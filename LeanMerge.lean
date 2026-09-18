import Lean

open Lean Lean.Elab Lean.Meta

namespace LeanMerge

structure Request where
  mode : String
  base : String
  donor : String := ""
  target : String := ""
  proof : String := ""
  result : String
  useDefEq : Bool := true
  setup : Option ModuleSetup := none
  deriving FromJson

structure CommandData where
  stx : Syntax
  before : Environment
  after : Environment
  levels : List Name := []
  included : List Name := []

instance [Inhabited Environment] : Inhabited CommandData :=
  ⟨{ stx := .missing, before := default, after := default }⟩

structure Document where
  source : String
  header : HeaderSyntax
  initial : Environment
  env : Environment
  commands : Array CommandData
  owners : NameMap Nat

def options : Options := ({} : Options).setBool `Elab.async false
  |>.set `maxRecDepth (8192 : Nat) |>.set `maxHeartbeats (2000000 : Nat)

def reportErrors (messages : MessageLog) : IO Unit := do
  if messages.hasErrors then
    for m in messages.toList do IO.eprintln (← m.toString)
    throw (IO.userError "Lean elaboration failed")

unsafe def analyze (source : String) (moduleName : Name)
    (setup? : Option ModuleSetup) : IO Document := do
  let ctx := Parser.mkInputContext source s!"{moduleName}.lean"
  let (header, parserState, messages) ← Parser.parseHeader ctx
  if HeaderSyntax.isModule header then
    throw (IO.userError "The new `module` syntax is not supported yet; use an ordinary Lean file")
  let setup := setup?.getD { name := moduleName }
  let opts := setup.options.toOptions.mergeBy (fun _ _ b => b) options
  for lib in setup.dynlibs do Lean.loadDynlib lib
  Lean.enableInitializersExecution
  let (initial, messages) ← processHeaderCore (HeaderSyntax.startPos header) (HeaderSyntax.imports header) false opts messages ctx
    (plugins := setup.plugins) (mainModule := moduleName) (arts := setup.importArts)
  reportErrors messages
  let _ : Inhabited Environment := ⟨initial⟩
  let first ← Language.Lean.processCommands ctx parserState (Command.mkState initial messages opts)
  let mut allMessages := messages
  for snap in (Language.toSnapshotTree first.get).getAll do
    allMessages := allMessages ++ snap.diagnostics.msgLog
  reportErrors allMessages
  let mut snap := first.get
  let mut previous := initial
  let mut previousScope := (Command.mkState initial messages opts).scopes.head!
  let mut commands : Array CommandData := #[]
  repeat
    let state := snap.elabSnap.resultSnap.get.cmdState
    let env := state.env
    unless Parser.isTerminalCommand snap.stx do
      commands := commands.push {
        stx := snap.stx, before := previous, after := env
        levels := previousScope.levelNames
        included := previousScope.includedVars.map Name.eraseMacroScopes }
    previous := env
    previousScope := state.scopes.head!
    if let some next := snap.nextCmdSnap? then snap := next.task.get else break
  let mut owners : NameMap Nat := {}
  for (name, _) in previous.constants.map₂.toList do
    if initial.contains name then continue
    let mut lo := 0
    let mut hi := commands.size
    while lo < hi do
      let mid := (lo + hi) / 2
      if commands[mid]!.after.contains name then hi := mid else lo := mid + 1
    owners := owners.insert name lo
  return { source, header, initial, env := previous, commands, owners }

def runMeta (env : Environment) (action : MetaM α) : IO α := do
  let (result, _, _) ← action.toIO
    { fileName := "lean-merge", fileMap := default, options }
    { env } {} {}
  return result

def isTheorem : ConstantInfo → Bool
  | .thmInfo _ => true
  | _ => false

partial def theoremSyntax? (stx : Syntax) : Option Syntax :=
  if ["theorem", "lemma"].contains stx[0].getAtomVal then some stx
  else stx.getArgs.findSome? theoremSyntax?

def theorems (doc : Document) : Array Name :=
  doc.owners.toArray.map (·.1) |>.filter (fun n =>
    (doc.env.find? n).any isTheorem && !(privateToUserName n).isInternalDetail)
    |>.qsort (fun a b => a.toString < b.toString)

def declaredTheorems (doc : Document) : Array Name :=
  (theorems doc).filter fun name => Id.run do
    let some owner := doc.owners.find? name | return false
    let some command := doc.commands[owner]? | return false
    let some stx := theoremSyntax? command.stx | return false
    let declared := stx[1][0].getId.replacePrefix `_root_ .anonymous
    return declared.isSuffixOf (privateToUserName name)

def resolve (doc : Document) (query : String) : IO Name := do
  let all := theorems doc
  let exact := all.filter fun n => n.toString == query || (privateToUserName n).toString == query
  let found := if exact.isEmpty then all.filter (fun n =>
    (privateToUserName n).toString.endsWith ("." ++ query)) else exact
  match found.toList with
  | [name] => return name
  | [] => throw (IO.userError s!"Theorem not found: {query}")
  | _ => throw (IO.userError s!"Ambiguous theorem {query}: {found.toList}")

def axioms (env : Environment) (name : Name) : IO (Array Name) :=
  runMeta env (collectAxioms name)

-- Follow compiler-generated helpers belonging to this command, not other theorems.
partial def hasOwnSorry (doc : Document) (owner : Nat) (name : Name)
    (seen : NameSet := {}) : Bool := Id.run do
  if seen.contains name || doc.owners.find? name != some owner then return false
  let some info := doc.env.find? name | return false
  let some value := info.value? (allowOpaque := true) | return false
  return value.hasSorry || value.getUsedConstants.any
    (fun dep => hasOwnSorry doc owner dep (seen.insert name))

def permittedAxiom (name : Name) : Bool :=
  [``propext, ``Classical.choice, ``Quot.sound].contains name

def checkProof (name : Name) : MetaM Unit := do
  let bad := (← collectAxioms name).filter (!permittedAxiom ·)
  unless bad.isEmpty do
    throwError "Proof {name} depends on unsupported axioms or unfinished proofs: {bad}"

def aligned (expr : Expr) (fromParams toParams : List Name) : Expr :=
  expr.instantiateLevelParams fromParams (toParams.map Level.param)

def equalTypes (a b : Expr) (useDefEq : Bool) : MetaM Bool :=
  if useDefEq then withTransparency .all (isDefEq a b) else pure (a == b)

def checkImportEffects (before after : Document) : IO Unit :=
  runMeta after.env do
    for (name, _) in before.owners.toArray do
      let some old := before.env.find? name | throwError "Missing original declaration: {name}"
      let some new := after.env.find? name | throwError "Imports removed a declaration: {name}"
      unless old.levelParams.length == new.levelParams.length &&
          (← equalTypes old.type (aligned new.type new.levelParams old.levelParams) true) do
        throwError "Additional imports changed the type of {name}"
      unless isTheorem old do
        if let some value := old.value? (allowOpaque := true) then
          let some newValue := new.value? (allowOpaque := true)
            | throwError "Additional imports changed the declaration kind of {name}"
          unless ← equalTypes value (aligned newValue new.levelParams old.levelParams) true do
            throwError "Additional imports changed the value of {name}"

structure TransferState where
  mapping : NameMap Name := {}
  visiting : NameSet := {}
  emitted : Array Name := #[]
  reused : Array Name := #[]
  reserved : NameSet := {}
  serial : Nat := 0

abbrev TransferM := StateT TransferState MetaM

partial def rewrite (expr : Expr) (mapping : NameMap Name) : Expr :=
  expr.replace fun e => match e with
    | .const n levels => (mapping.find? n).map (Expr.const · levels)
    | .proj n i value => some <| Expr.proj ((mapping.find? n).getD n) i (rewrite value mapping)
    | _ => none

def dependencies (expr : Expr) : MetaM (Array Name) := do
  let (_, names) ← (expr.forEach fun e => do
    match e with
    | .const n _ | .proj n _ _ => modify (fun names : NameSet => names.insert n)
    | _ => pure () : StateRefT NameSet MetaM Unit).run {}
  return names.toArray

def reservePrefixes (names : NameSet) : Name → NameSet
  | .anonymous => names
  | name@(.str parent _) | name@(.num parent _) => reservePrefixes (names.insert name) parent

def reservedPrefixes (env : Environment) : NameSet :=
  env.constants.fold (init := ({} : NameSet)) fun ns name _ => reservePrefixes ns name

def freshName : TransferM Name := do
  let mut serial := (← get).serial
  repeat
    let n := Name.mkSimple s!"LeanMergeAux{serial}"
    serial := serial + 1
    unless (← getEnv).contains n || (← get).reserved.contains n do
      modify fun s => { s with serial }
      return n
  throwError "Unable to allocate a declaration name"

def declaration (info : ConstantInfo) (name : Name) (type value : Expr) : MetaM Declaration := do
  match info with
  | .thmInfo v => return .thmDecl { v with name, type, value, all := [name] }
  | .defnInfo v =>
    unless v.safety == .safe do throwError "Unsafe/partial definition is unsupported: {info.name}"
    return .defnDecl { v with name, type, value, all := [name] }
  | .opaqueInfo v =>
    if v.isUnsafe then throwError "Unsafe opaque is unsupported: {info.name}"
    return .opaqueDecl { v with name, type, value, all := [name] }
  | _ => throwError "Cannot transfer {info.name}: only theorem, def, abbrev, instance and opaque dependencies are supported"

def inductiveGroup (donor : Document) (info : InductiveVal) : IO (Array ConstantInfo) := do
  let mut group := #[]
  for name in info.all do
    let some (.inductInfo val) := donor.env.find? name
      | throw (IO.userError s!"Missing inductive declaration: {name}")
    group := group.push (.inductInfo val)
    for ctor in val.ctors do
      let some ci := donor.env.find? ctor | throw (IO.userError s!"Missing constructor: {ctor}")
      group := group.push ci
  for (name, _) in donor.owners.toArray do
    if let some (.recInfo val) := donor.env.find? name then
      if val.all == info.all then group := group.push (.recInfo val)
  return group

-- Types alone are insufficient: constructor order and recursor reduction rules matter.
def checkInductiveMember (info : ConstantInfo) (mapping : NameMap Name)
    (useDefEq : Bool) : MetaM Unit := do
  let mapped := fun n => (mapping.find? n).getD n
  let old ← getConstInfo (mapped info.name)
  let mismatch : MetaM Unit := throwError "Conflicting inductive declaration: {info.name}"
  unless info.levelParams.length == old.levelParams.length do mismatch
  let eq := fun a b => equalTypes
    (aligned (rewrite a mapping) info.levelParams old.levelParams) b useDefEq
  unless ← eq info.type old.type do mismatch
  match info, old with
  | .inductInfo a, .inductInfo b =>
    unless a.numParams == b.numParams && a.numIndices == b.numIndices &&
        a.all.map mapped == b.all && a.ctors.map mapped == b.ctors &&
        a.numNested == b.numNested && a.isRec == b.isRec &&
        a.isUnsafe == b.isUnsafe && a.isReflexive == b.isReflexive do mismatch
  | .ctorInfo a, .ctorInfo b =>
    unless mapped a.induct == b.induct && a.cidx == b.cidx &&
        a.numParams == b.numParams && a.numFields == b.numFields && a.isUnsafe == b.isUnsafe do
      mismatch
  | .recInfo a, .recInfo b =>
    unless a.all.map mapped == b.all && a.numParams == b.numParams &&
        a.numIndices == b.numIndices && a.numMotives == b.numMotives &&
        a.numMinors == b.numMinors && a.k == b.k && a.isUnsafe == b.isUnsafe &&
        a.rules.length == b.rules.length do mismatch
    for (r, s) in a.rules.zip b.rules do
      unless mapped r.ctor == s.ctor && r.nfields == s.nfields && (← eq r.rhs s.rhs) do mismatch
  | _, _ => mismatch

def addInductive (decl : Declaration) : MetaM Unit := do
  addDecl decl
  let .inductDecl _ _ types _ := decl | return
  -- The kernel creates nested recursors, but addDecl only exposes the primary ones.
  for type in types do
    let mut i := 1
    repeat
      let name := (mkRecName type.name).appendIndexAfter i
      let env ← getEnv
      let some ci := env.toKernelEnv.find? name | break
      let result ← env.addConstAsync name .recursor
      result.commitConst result.asyncEnv (info? := ci)
      result.commitCheckEnv result.asyncEnv
      setEnv result.mainEnv
      i := i + 1

mutual
-- Resolve constants before printing. Textual substitution would confuse binders and namespaces.
partial def transfer (donor : Document) (useDefEq : Bool) (name : Name) : TransferM Name := do
  if let some mapped := (← get).mapping.find? name then return mapped
  unless donor.owners.contains name do
    unless (← getEnv).contains name do throwError "Missing imported dependency: {name}"
    return name
  if (← get).visiting.contains name then throwError "Cyclic dependency while transferring {name}"
  modify fun s => { s with visiting := s.visiting.insert name }
  let some info := donor.env.find? name | throwError "Missing donor declaration: {name}"
  match info with
  | .inductInfo val => return ← transferInductive donor useDefEq val name
  | .ctorInfo val =>
    discard <| transfer donor useDefEq val.induct
    return (← get).mapping.get! name
  | .recInfo val =>
    for induct in val.all do discard <| transfer donor useDefEq induct
    return (← get).mapping.get! name
  | _ => pure ()
  for dep in ← dependencies info.type do discard <| transfer donor useDefEq dep
  let type := rewrite info.type (← get).mapping
  let existing := (← getEnv).find? name
  -- A proven base theorem may replace a donor's placeholder of the same type.
  if let some old := existing then
    if isTheorem info && isTheorem old && info.levelParams.length == old.levelParams.length then
      if ← equalTypes (aligned type info.levelParams old.levelParams) old.type useDefEq then
        if (← collectAxioms name).all permittedAxiom then
          modify fun s => { s with
            mapping := s.mapping.insert name name
            reused := s.reused.push name, visiting := s.visiting.erase name }
          return name
  let some value := info.value? (allowOpaque := true)
    | throwError "Unsupported dependency {name}: local axioms cannot be transplanted"
  for dep in ← dependencies value do discard <| transfer donor useDefEq dep
  let value := rewrite value (← get).mapping
  if let some old := existing then
    if !isTheorem info && !isTheorem old && info.levelParams.length == old.levelParams.length then
      if let some oldValue := old.value? (allowOpaque := true) then
        if (← equalTypes (aligned type info.levelParams old.levelParams) old.type useDefEq) &&
            (← equalTypes (aligned value info.levelParams old.levelParams) oldValue useDefEq) then
          modify fun s => { s with
            mapping := s.mapping.insert name name
            reused := s.reused.push name, visiting := s.visiting.erase name }
          return name
  let fresh ← freshName
  addDecl (← declaration info fresh type value)
  modify fun s => { s with
    mapping := s.mapping.insert name fresh
    emitted := s.emitted.push fresh, visiting := s.visiting.erase name }
  return fresh

partial def transferInductive (donor : Document) (useDefEq : Bool)
    (info : InductiveVal) (requested : Name) : TransferM Name := do
  let group ← inductiveGroup donor info
  if group.any (·.isUnsafe) then throwError "Unsafe inductive is unsupported: {info.name}"
  let env ← getEnv
  let mut existing : NameMap Name := {}
  for n in info.all do
    if env.contains n then existing := existing.insert n n
    else if isPrivateName n then
      let candidates := env.constants.fold (init := #[]) fun names candidate _ =>
        if isPrivateName candidate && privateToUserName candidate == privateToUserName n then
          names.push candidate
        else names
      if candidates.size == 1 then existing := existing.insert n candidates[0]!
  let reuse := info.all.all existing.contains
  if !reuse && (!existing.isEmpty || group.any (fun ci => env.contains ci.name)) then
    throwError "Conflicting inductive declaration: {info.name} (incomplete matching group)"
  -- Reserve the entire mutually recursive group before following its dependencies.
  for n in info.all do
    let fresh ← if reuse then pure (existing.get! n) else freshName
    modify fun s => { s with mapping := s.mapping.insert n fresh }
  for ci in group do
    unless info.all.contains ci.name do
      let some parent := info.all.find? (·.isPrefixOf ci.name)
        | throwError "Unsupported generated inductive name: {ci.name}"
      let fresh := ci.name.replacePrefix parent ((← get).mapping.get! parent)
      modify fun s => { s with mapping := s.mapping.insert ci.name fresh }
  for ci in group do
    for dep in ← dependencies ci.type do discard <| transfer donor useDefEq dep
    if let .recInfo val := ci then
      for rule in val.rules do
        for dep in ← dependencies rule.rhs do discard <| transfer donor useDefEq dep
  let mapping := (← get).mapping
  unless reuse do
    let mut types := []
    for n in info.all do
      let val := (donor.env.find? n).get!.inductiveVal!
      let ctors := val.ctors.map fun ctor => {
        name := mapping.get! ctor
        type := rewrite (donor.env.find? ctor).get!.type mapping : Constructor }
      types := types ++ [{ name := mapping.get! n, type := rewrite val.type mapping, ctors }]
    addInductive (.inductDecl info.levelParams info.numParams types false)
  for ci in group do checkInductiveMember ci mapping useDefEq
  modify fun s => { s with
    visiting := group.foldl (fun ns ci => ns.erase ci.name) s.visiting
    reused := if reuse then s.reused ++ group.map (fun ci => mapping.get! ci.name) else s.reused
    emitted := if reuse then s.emitted else s.emitted.push (mapping.get! info.all.head!) }
  return mapping.get! requested
end

def printOptions : Options := options.setBool `pp.all true
  |>.setBool `pp.proofs true |>.setBool `pp.universes true
  |>.setBool `pp.privateNames false
  |>.setBool `pp.fullNames true |>.setBool `pp.notation false
  |>.setBool `pp.deepTerms true |>.set `pp.maxSteps (10000000 : Nat)
  |>.setBool `pp.fieldNotation false |>.setBool `pp.structureInstances false
  |>.set `pp.width (100 : Nat)

def renderInductive (info : InductiveVal) (existingLevels : List Name) : MetaM String := do
  -- Recursive names are local variables while Lean elaborates an inductive block.
  withOptions (fun _ => printOptions.setBool `pp.universes false) do
    let mut content := "set_option autoImplicit false in\nmutual\n"
    for n in info.all do
      let val := (← getConstInfo n).inductiveVal!
      let newLevels := val.levelParams.filter (!existingLevels.contains ·)
      let levels := if newLevels.isEmpty then "" else
        ".{" ++ String.intercalate ", " (newLevels.map Name.toString) ++ "}"
      content := content ++ (← forallBoundedTelescope val.type (some val.numParams) fun params result => do
        let mut binders := ""
        for param in params do
          let decl ← param.fvarId!.getDecl
          let name := (← ppExpr param).pretty 100
          let type := (← ppExpr decl.type).pretty 100
          let (left, right) := match decl.binderInfo with
            | .default => ("(", ")")
            | .implicit => ("{", "}")
            | .strictImplicit => ("⦃", "⦄")
            | .instImplicit => ("[", "]")
          binders := binders ++ s!" {left}{name} : {type}{right}"
        let mut text := s!"inductive _root_.{n}{levels}{binders} :\n  {(← ppExpr result).pretty 100} where\n"
        for ctor in val.ctors do
          let mut type := (← getConstInfo ctor).type
          for param in params do type := type.bindingBody!.instantiate1 param
          let typeText := ((← ppExpr type).pretty 100).replace "\n" "\n    "
          let ctorName := Name.mkSimple ctor.getString!
          text := text ++ s!"  | {ctorName} :\n    {typeText}\n"
        return text)
    return content ++ "end\n"

def render (info : ConstantInfo) (name : Name) (existingLevels : List Name := []) : MetaM String := do
  if let .inductInfo val := info then return ← renderInductive val existingLevels
  let some value := info.value? (allowOpaque := true) | throwError "No value for {info.name}"
  let kind := match info with
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "noncomputable opaque"
    | .defnInfo v => if v.hints.isAbbrev then "noncomputable abbrev" else "noncomputable def"
    | _ => "def"
  let newLevels := info.levelParams.filter (!existingLevels.contains ·)
  let levels := if newLevels.isEmpty then "" else
    ".{" ++ String.intercalate ", " (newLevels.map Name.toString) ++ "}"
  withOptions (fun _ => printOptions) do
    let type := (← ppExpr info.type).pretty 100
    let valueText := (← ppExpr value).pretty 100
    -- Projection values may use explicit lambda binders for an implicit function type.
    let valueText := if value.isLambda then "@" ++ valueText else valueText
    return s!"{kind} _root_.{name}{levels} :\n  {type}\n:=\n  {valueText}\n"

def bounds (stx : Syntax) : IO (String.Pos.Raw × String.Pos.Raw) := do
  let some start := stx.getPos? | throw (IO.userError "Missing syntax start position")
  let some stop := stx.getTailPos? | throw (IO.userError "Missing syntax end position")
  return (start, stop)

def slice (source : String) (start stop : String.Pos.Raw) : String :=
  String.Pos.Raw.extract source start stop

def headerText (doc : Document) : String :=
  let stop := doc.header.raw.getTailPos?.getD 0
  slice doc.source 0 stop

def extraImports (base donor : Document) : String := Id.run do
  let mut result := ""
  for imp in donor.header.imports do
    unless base.header.imports.any (fun other => other.module == imp.module) do
      result := result ++ s!"import {imp.module}\n"
  return result

structure Attempt where
  content : String
  candidate : Name
  inserted : Array Name
  reused : Array Name

def attempt (base donor : Document) (target candidate : Name) (useDefEq : Bool) : IO Attempt := do
  let _ : Inhabited Environment := ⟨base.env⟩
  let some owner := base.owners.find? target | throw (IO.userError "Missing target command")
  let command := base.commands[owner]!
  let some targetInfo := base.env.find? target | throw (IO.userError "Missing target")
  if isPrivateName target then throw (IO.userError "Private target theorems are not supported yet")
  let some stx := theoremSyntax? command.stx
    | throw (IO.userError "Target must be a theorem/lemma declaration")
  let (start, stop) ← bounds stx
  let (commandStart, _) ← bounds command.stx
  let reserved := reservedPrefixes base.env
  let (replacement, helpers, state) ← runMeta command.before do
    let (root, state) ← (transfer donor useDefEq candidate).run { reserved }
    let info ← getConstInfo root
    unless info.levelParams.length == targetInfo.levelParams.length do
      throwError "Universe parameter counts differ for {candidate} and {target}"
    let type := aligned info.type info.levelParams targetInfo.levelParams
    unless ← equalTypes type targetInfo.type useDefEq do
      throwError "Type mismatch: {candidate} does not prove {target}"
    checkProof root
    let some proofValue := info.value? (allowOpaque := true) | throwError "No proof value for {root}"
    let value := aligned proofValue info.levelParams targetInfo.levelParams
    let replacement ← render (.thmInfo {
      name := target, levelParams := targetInfo.levelParams, type := targetInfo.type, value }) target command.levels
    let mut helpers := ""
    for name in state.emitted do
      if name == root then continue
      helpers := helpers ++ (← render (← getConstInfo name) name command.levels) ++ "\n"
    return (replacement, helpers, state)
  let included := String.intercalate " " (command.included.map Name.toString)
  let omitCmd := if included.isEmpty then "" else s!"omit {included}\n"
  let restoreCmd := if included.isEmpty then "" else s!"\ninclude {included}\n"
  let content := slice base.source 0 commandStart ++ omitCmd ++ helpers ++
    slice base.source commandStart start ++ replacement ++ restoreCmd ++ slice base.source stop base.source.rawEndPos
  return {
    content, candidate
    inserted := state.emitted.filter (· != (state.mapping.find? candidate).getD candidate)
    reused := state.reused }

unsafe def merge (req : Request) : IO Json := do
  let original ← analyze req.base `LeanMergeBase req.setup
  let donor ← analyze req.donor `LeanMergeDonor req.setup
  let additions := extraImports original donor
  let headerEnd := original.header.raw.getTailPos?.getD 0
  let combined := if additions.isEmpty then req.base else
    slice req.base 0 headerEnd ++ "\n" ++ additions ++ slice req.base headerEnd req.base.rawEndPos
  let base ← if additions.isEmpty then pure original else analyze combined `LeanMergeBase req.setup
  unless additions.isEmpty do checkImportEffects original base
  let target ← if req.target.isEmpty then do
      let mut unfinished := #[]
      for name in declaredTheorems base do
        if let some owner := base.owners.find? name then
          if hasOwnSorry base owner name then unfinished := unfinished.push name
      match unfinished.toList with
      | [name] => pure name
      | _ => throw (IO.userError s!"Specify --target; found {unfinished.size} theorems with their own sorry: {unfinished.toList}")
    else resolve base req.target
  unless (← axioms base.env target).contains ``sorryAx do
    throw (IO.userError s!"Target {target} already has a complete proof")
  let candidates ← if req.proof.isEmpty then pure (theorems donor) else
    pure #[← resolve donor req.proof]
  let mut successes : Array Attempt := #[]
  let mut failures : Array String := #[]
  for candidate in candidates do
    try
      successes := successes.push (← attempt base donor target candidate req.useDefEq)
    catch e => failures := failures.push s!"{candidate}: {e}"
  let selected ← match successes.toList with
    | [one] => pure one
    | [] => throw (IO.userError ("No compatible complete proof found.\n" ++ String.intercalate "\n" failures.toList))
    | many =>
      let exact := many.filter (fun a => a.candidate == target)
      match exact with
      | [one] => pure one
      | _ => throw (IO.userError s!"Multiple matching proofs; specify --proof: {many.map (·.candidate)}")
  let verified ← analyze selected.content `LeanMergeBase req.setup
  runMeta verified.env do
    let some before := original.env.find? target | throwError "Original target is missing"
    let after ← getConstInfo target
    unless before.levelParams.length == after.levelParams.length &&
        (← equalTypes before.type (aligned after.type after.levelParams before.levelParams) req.useDefEq) do
      throwError "Verification changed the target type"
    checkProof target
  return json% { "okay": true, "content": $(selected.content), "target": $(target.toString),
    "proof": $(selected.candidate.toString), "inserted": $(selected.inserted.map Name.toString),
    "reused": $(selected.reused.map Name.toString), "verified": true,
    "axioms": $((← axioms verified.env target).map Name.toString) }

unsafe def normalize (req : Request) : IO Json := do
  let doc ← analyze req.base `LeanMergeNormalize req.setup
  let selected ← if req.target.isEmpty then pure ((declaredTheorems doc).filter (!isPrivateName ·))
    else pure #[← resolve doc req.target]
  if selected.isEmpty then throw (IO.userError "No theorems to normalize")
  let (content, count, nameMapping) ← runMeta doc.initial do
    let action : TransferM Unit := do
      for name in selected do discard <| transfer doc req.useDefEq name
    let reserved := reservedPrefixes doc.env
    let (_, state) ← action.run { reserved }
    let mut mapping : NameMap Name := {}
    let mut nameMapping : NameMap Name := {}
    let inductiveOwners := doc.owners.toArray.filterMap fun (name, owner) =>
      if (doc.env.find? name).any (fun ci => ci matches .inductInfo _) then some owner else none
    for (name, fresh) in state.mapping.toArray do
      -- Re-elaborating an inductive regenerates casesOn, noConfusion, sizeOf, etc.
      -- Keep transferred definitions under fresh names to avoid redeclaring them.
      let generated := (doc.owners.find? name).any inductiveOwners.contains &&
        (doc.env.find? name).any (fun ci => (ci.value? (allowOpaque := true)).isSome)
      let restored := if isPrivateName name || generated then fresh ++ `normalized else name
      mapping := mapping.insert fresh restored
    for (name, fresh) in state.mapping.toArray do
      if let some (.inductInfo info) := doc.env.find? name then
        for ci in ← inductiveGroup doc info do
          if name.isPrefixOf ci.name then
            let old := state.mapping.get! ci.name
            mapping := mapping.insert old (old.replacePrefix fresh (mapping.get! fresh))
    for (name, fresh) in state.mapping.toArray do
      nameMapping := nameMapping.insert name (mapping.get! fresh)
    for name in selected do
      if isPrivateName name then throwError "Private target theorems are not supported yet"
    let mut content := headerText doc ++ "\n\n"
    for fresh in state.emitted do
      let info ← getConstInfo fresh
      let name := (mapping.find? fresh).getD fresh
      if let .inductInfo val := info then
        if name != fresh then
          let mut types : List InductiveType := []
          for n in val.all do
            let induct := (← getConstInfo n).inductiveVal!
            let ctors ← induct.ctors.mapM fun ctor => do
              let type := rewrite (← getConstInfo ctor).type mapping
              return ({ name := (mapping.find? ctor).getD ctor, type } : Constructor)
            let type := rewrite induct.type mapping
            types := types ++ [{ name := (mapping.find? n).getD n, type, ctors }]
          addInductive (.inductDecl val.levelParams val.numParams types false)
        content := content ++ (← render (← getConstInfo name) name) ++ "\n"
        continue
      let some value := info.value? (allowOpaque := true) | throwError "No value for {fresh}"
      let decl ← declaration info name (rewrite info.type mapping) (rewrite value mapping)
      if name != fresh then addDecl decl
      let info := match decl with
        | .thmDecl v => ConstantInfo.thmInfo v
        | .defnDecl v => .defnInfo v
        | .opaqueDecl v => .opaqueInfo v
        | _ => info
      content := content ++ (← render info name) ++ "\n"
    return (content, state.emitted.size, nameMapping)
  let verified ← analyze content `LeanMergeNormalize req.setup
  for name in selected do
    let some old := doc.env.find? name | throw (IO.userError "Missing original theorem")
    let some new := verified.env.find? name | throw (IO.userError "Missing normalized theorem")
    unless old.levelParams.length == new.levelParams.length &&
        (← runMeta verified.env (equalTypes (rewrite old.type nameMapping)
          (aligned new.type new.levelParams old.levelParams) req.useDefEq)) do
      throw (IO.userError s!"Normalization changed theorem type: {name}")
  return json% { "okay": true, "verified": true, "content": $content,
    "normalize_stats": { "declarations": $count }, "targets": $(selected.map Name.toString) }

end LeanMerge

unsafe def main (args : List String) : IO UInt32 := do
  try
    let [requestPath] := args | throw (IO.userError "Expected a JSON request path")
    initSearchPath (← findSysroot)
    enableInitializersExecution
    let req : LeanMerge.Request ← IO.ofExcept <| fromJson? (← IO.ofExcept <| Json.parse (← IO.FS.readFile requestPath))
    let result ← match req.mode with
      | "merge" => LeanMerge.merge req
      | "normalize" => LeanMerge.normalize req
      | _ => throw (IO.userError s!"Unknown mode: {req.mode}")
    IO.FS.writeFile req.result result.pretty
    return (0 : UInt32)
  catch e =>
    IO.eprintln s!"lean-merge: {e}"
    return (1 : UInt32)
