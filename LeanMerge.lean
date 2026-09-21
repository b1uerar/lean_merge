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
  declarationsOnly : Bool := false
  setup : Option ModuleSetup := none
  deriving FromJson

structure CommandData where
  stx : Syntax
  before : Environment
  after : Environment
  refs : NameSet := {}
  context : Array Nat := #[]
  scopes : Array Nat := #[]
  attributeTargets : NameSet := {}
  names : Array Name := #[]

instance [Inhabited Environment] : Inhabited CommandData :=
  ⟨{ stx := .missing, before := default, after := default }⟩

structure Document where
  source : String
  header : HeaderSyntax
  initial : Environment
  env : Environment
  commands : Array CommandData
  owners : NameMap Nat
  scopeEnds : Std.HashMap Nat (Array Nat)

def options : Options := ({} : Options).setBool `Elab.async false
  |>.set `maxRecDepth (8192 : Nat) |>.set `maxHeartbeats (2000000 : Nat)

def reportErrors (messages : MessageLog) : IO Unit := do
  if messages.hasErrors then
    for m in messages.toList do IO.eprintln (← m.toString)
    throw (IO.userError "Lean elaboration failed")

partial def syntaxRefs (env : Environment) (stx : Syntax) (refs : NameSet) : NameSet := Id.run do
  match stx with
  | .ident _ _ _ resolved =>
    let mut refs := refs
    for r in resolved do
      if let .decl n _ := r then refs := refs.insert n
    return refs
  | .node _ kind args =>
    let mut refs := refs.insert kind
    -- Syntax and macro registrations are dependencies even when expansion erases them.
    for entry in macroAttribute.getEntries env kind do
      refs := refs.insert entry.declName
    for (_, category) in (Parser.parserExtension.getState env).categories do
      if category.kinds.contains kind then refs := refs.insert category.declName
    return args.foldl (fun acc s => syntaxRefs env s acc) refs
  | _ => return refs

partial def treeRefs (env : Environment) (mctx : MetavarContext)
    (tree : InfoTree) (refs : NameSet) : NameSet := Id.run do
  match tree with
  | .context (.commandCtx ctx) t => return treeRefs ctx.env ctx.mctx t refs
  | .context _ t => return treeRefs env mctx t refs
  | .hole _ => return refs
  | .node info children =>
    let mut refs := refs
    match info with
    | .ofTermInfo i =>
      refs := refs.insert i.elaborator ++ (instantiateExprMVarsImp mctx i.expr).2.getUsedConstantsAsSet
    | .ofCommandInfo i => refs := refs.insert i.elaborator
    | .ofTacticInfo i =>
      refs := refs.insert i.elaborator
      -- Intermediate tactic assignments include dependencies erased from the final proof.
      for goal in i.goalsBefore do
        refs := refs ++ (instantiateExprMVarsImp i.mctxAfter (.mvar goal)).2.getUsedConstantsAsSet
    | .ofFieldInfo i => refs := refs.insert i.projName ++ i.val.getUsedConstantsAsSet
    | .ofMacroExpansionInfo i =>
      refs := syntaxRefs env i.output (syntaxRefs env i.stx refs)
    | .ofOptionInfo i => refs := refs.insert i.declName
    | _ => pure ()
    for t in children do refs := treeRefs env mctx t refs
    return refs

def isScopeCommand (stx : Syntax) : Bool :=
  [``Parser.Command.namespace, ``Parser.Command.section, ``Parser.Command.end].contains stx.getKind

def isContextCommand (stx : Syntax) : Bool :=
  [``Parser.Command.variable, ``Parser.Command.universe, ``Parser.Command.open,
    ``Parser.Command.set_option, ``Parser.Command.include, ``Parser.Command.omit,
    ``Parser.Command.export].contains stx.getKind

def isDiagnostic (stx : Syntax) : Bool :=
  [``Parser.Command.check, ``Parser.Command.check_failure, ``Parser.Command.print,
    ``Parser.Command.printAxioms, ``Parser.Command.printEqns, ``Parser.Command.printSig,
    ``Parser.Command.synth, ``Parser.Command.version, ``Parser.Command.moduleDoc].contains stx.getKind

def isAttributeCommand (stx : Syntax) : Bool :=
  [``Parser.Command.attribute, ``Parser.Command.grindPattern, ``Parser.Command.export].contains stx.getKind

partial def hasKind (stx : Syntax) (kind : Name) : Bool :=
  stx.getKind == kind || stx.getArgs.any (hasKind · kind)

def hasUntrackedEffect (cmd : CommandData) : Bool :=
  cmd.stx.getKind == ``Parser.Command.initialize ||
  hasKind cmd.stx ``Parser.Command.eraseAttr ||
  (cmd.names.isEmpty && !isScopeCommand cmd.stx && !isContextCommand cmd.stx &&
    !isAttributeCommand cmd.stx && !isDiagnostic cmd.stx)

def attributeTargets (stx : Syntax) (state : Command.State) : NameSet := Id.run do
  let ids := if stx.getKind == ``Parser.Command.attribute then stx[4].getArgs
    else if stx.getKind == ``Parser.Command.export then stx[3].getArgs
    else if stx.getKind == ``Parser.Command.grindPattern then #[stx[2]] else #[]
  let scope := state.scopes.head!
  let mut refs := {}
  for id in ids do
    for (name, _) in ResolveName.resolveGlobalName state.env scope.opts scope.currNamespace scope.openDecls id.getId do
      refs := refs.insert name
  return refs

def referenceFormat (ctx : PPContext) (expr : Expr) : FormatWithInfos :=
  { fmt := .nil, infos := ({} : PrettyPrinter.InfoPerPos).insert 0 (.ofTermInfo {
      elaborator := .anonymous, stx := .missing, lctx := ctx.lctx,
      expectedType? := none, expr := (instantiateExprMVarsImp ctx.mctx expr).2 }) }

-- Decode structured trace payloads without parsing printed names or invoking delaborators.
def referenceContext (ctx : MessageDataContext) : PPContext :=
  { env := ppExt.setState ctx.env {
      ppExprWithInfos := fun ctx e => pure (referenceFormat ctx e)
      ppConstNameWithInfos := fun ctx n => pure (referenceFormat ctx (.const n []))
      ppTerm := fun _ _ => pure .nil
      ppLevel := fun _ _ => pure .nil
      ppGoal := fun _ _ => pure .nil }
    mctx := ctx.mctx, lctx := ctx.lctx, opts := ctx.opts.setBool `pp.raw false }

partial def messageRefs (msg : MessageData) (ctx : Option PPContext := none)
    (refs : NameSet := {}) : BaseIO NameSet := do
  match msg with
  | .withContext ctx msg => messageRefs msg (some (referenceContext ctx)) refs
  | .withNamingContext _ msg | .nest _ msg | .group msg | .tagged _ msg
  | .ofWidget _ msg => messageRefs msg ctx refs
  | .compose left right => messageRefs right ctx (← messageRefs left ctx refs)
  | .trace _ msg children =>
    let mut refs ← messageRefs msg ctx refs
    for child in children do refs ← messageRefs child ctx refs
    return refs
  | .ofLazy f _ =>
    let some msg := (← f ctx).get? MessageData | return refs
    messageRefs msg ctx refs
  | .ofFormatWithInfos fmt =>
    let mut refs := refs
    for (_, info) in fmt.infos do
      if let .ofTermInfo i := info then refs := refs ++ i.expr.getUsedConstantsAsSet
    return refs
  | _ => return refs


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
  let mut scopeOwners : Array Nat := #[]
  let mut contexts : Array (Array Nat) := #[#[]]
  let mut scopeEnds : Std.HashMap Nat (Array Nat) := {}
  let mut commands : Array CommandData := #[]
  repeat
    let state := snap.elabSnap.resultSnap.get.cmdState
    let env := state.env
    unless Parser.isTerminalCommand snap.stx do
      let refs := match snap.elabSnap.infoTreeSnap.get.infoTree? with
        | some tree => treeRefs env {} tree (syntaxRefs env snap.stx {})
        | none => syntaxRefs env snap.stx {}
      let i := commands.size
      let attrTargets := attributeTargets snap.stx state
      commands := commands.push {
        stx := snap.stx, before := previous, after := env, refs := refs ++ attrTargets
        context := contexts.flatten, scopes := scopeOwners, attributeTargets := attrTargets }
      while contexts.size < state.scopes.length do
        contexts := contexts.push #[]
        scopeOwners := scopeOwners.push i
      while contexts.size > state.scopes.length do
        let owner := scopeOwners.back!
        scopeEnds := scopeEnds.insert owner ((scopeEnds[owner]?).getD #[] |>.push i)
        scopeOwners := scopeOwners.pop
        contexts := contexts.pop
      if isContextCommand snap.stx then
        contexts := contexts.modify (contexts.size - 1) (·.push i)
    previous := env
    if let some next := snap.nextCmdSnap? then snap := next.task.get else break
  for msg in allMessages.toList do
    if !msg.data.hasTag (· == `trace) then continue
    let pos := ctx.fileMap.ofPosition msg.pos
    let mut lo := 0
    let mut hi := commands.size
    while lo < hi do
      let mid := (lo + hi) / 2
      if commands[mid]!.stx.getPos?.getD 0 <= pos then lo := mid + 1 else hi := mid
    if lo > 0 then
      let refs ← messageRefs msg.data
      commands := commands.modify (lo - 1) fun cmd => { cmd with refs := cmd.refs ++ refs }
  let mut owners : NameMap Nat := {}
  for (name, _) in previous.constants.map₂.toList do
    if initial.contains name then continue
    let mut lo := 0
    let mut hi := commands.size
    while lo < hi do
      let mid := (lo + hi) / 2
      if commands[mid]!.after.contains name then hi := mid else lo := mid + 1
    if lo == commands.size then
      throw (IO.userError s!"Cannot attribute local declaration {name} to source")
    owners := owners.insert name lo
    commands := commands.modify lo fun c => { c with names := c.names.push name }
  return { source, header, initial, env := previous, commands, owners, scopeEnds }

def runMeta (env : Environment) (action : MetaM α) : IO α := do
  let (result, _, _) ← action.toIO
    { fileName := "lean-merge", fileMap := default, options }
    { env } {} {}
  return result

def isTheorem : ConstantInfo → Bool
  | .thmInfo _ => true
  | _ => false

partial def theoremSyntaxAt? (stx : Syntax) (name : Name) (pos : String.Pos.Raw) : Option Syntax :=
  if ["theorem", "lemma"].contains stx[0].getAtomVal then
    let id := stx[1][0]
    let declared := id.getId.replacePrefix `_root_ .anonymous
    if id.getPos? == some pos && declared.isSuffixOf (privateToUserName name) then some stx else none
  else stx.getArgs.findSome? (fun child => theoremSyntaxAt? child name pos)

def theoremSyntax? (doc : Document) (name : Name) : Option Syntax := do
  let owner ← doc.owners.find? name
  let command ← doc.commands[owner]?
  let ranges ← declRangeExt.find? doc.env name
  let pos := doc.source.crlfToLf.toFileMap.ofPosition ranges.selectionRange.pos
  theoremSyntaxAt? command.stx name pos

def theorems (doc : Document) : Array Name :=
  doc.owners.toArray.map (·.1) |>.filter (fun n =>
    (doc.env.find? n).any isTheorem && !(privateToUserName n).isInternalDetail)
    |>.qsort (fun a b => a.toString < b.toString)

def declaredTheorems (doc : Document) : Array Name :=
  (theorems doc).filter fun name => (theoremSyntax? doc name).isSome

-- A mutual command owns several declarations; only the target and its helpers may be replaced.
def theoremDeclarations (doc : Document) (target : Name) : NameSet := Id.run do
  let mut names : NameSet := ({} : NameSet).insert target
  let some owner := doc.owners.find? target | return names
  let some command := doc.commands[owner]? | return names
  let some stx := theoremSyntax? doc target | return names
  let some start := stx.getPos? | return names
  let some stop := stx.getTailPos? | return names
  let fileMap := doc.source.crlfToLf.toFileMap
  for name in command.names do
    if name == target then continue
    if let some ranges := declRangeExt.find? doc.env name then
      let pos := fileMap.ofPosition ranges.selectionRange.pos
      if start ≤ pos && pos < stop then names := names.insert name
    else if target.isPrefixOf name then
      names := names.insert name
  return names

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

-- Follow only this theorem's helpers, not sibling declarations in the same mutual block.
partial def hasOwnSorry (doc : Document) (declarations : NameSet) (name : Name)
    (seen : NameSet := {}) : Bool := Id.run do
  if seen.contains name || !declarations.contains name then return false
  let some info := doc.env.find? name | return false
  let some value := info.value? (allowOpaque := true) | return false
  return value.hasSorry || value.getUsedConstants.any
    (fun dep => hasOwnSorry doc declarations dep (seen.insert name))

def permittedAxiom (name : Name) : Bool :=
  [``propext, ``Classical.choice, ``Quot.sound].contains name

def checkedAxioms (names : Array Name) : MetaM (Array Name) := do
  let env ← getEnv
  -- All roots are checked in the same environment; visit their shared dependencies once.
  let mut state : CollectAxioms.State := {}
  for name in names do
    let (_, next) := ((CollectAxioms.collect name).run env).run state
    let bad := next.axioms.filter (!permittedAxiom ·)
    unless bad.isEmpty do
      throwError "Proof {name} depends on unsupported axioms or unfinished proofs: {bad}"
    state := next
  return state.axioms

def checkProofs (names : Array Name) : MetaM Unit := discard (checkedAxioms names)

def checkProof (name : Name) : MetaM Unit := checkProofs #[name]

def aligned (expr : Expr) (fromParams toParams : List Name) : Expr :=
  expr.instantiateLevelParams fromParams (toParams.map Level.param)

def equalTypes (a b : Expr) (useDefEq : Bool) : MetaM Bool :=
  if useDefEq then withTransparency .all (isDefEq a b) else pure (a == b)

partial def rewrite (expr : Expr) (mapping : NameMap Name) : Expr :=
  expr.replace fun e => match e with
    | .const n levels => (mapping.find? n).map (Expr.const · levels)
    | .proj n i value => some <| Expr.proj ((mapping.find? n).getD n) i (rewrite value mapping)
    | _ => none

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

def existingName? (env : Environment) (name : Name) : Option Name := Id.run do
  if env.contains name then return some name
  let mut found := none
  for (candidate, _) in env.constants.map₂.toList do
    if privateToUserName candidate == privateToUserName name then
      if found.isSome then return none
      found := some candidate
  return found

structure SavedCommand where
  names : Array String
  source : String
  deriving FromJson, ToJson

def checkImportEffects (before after : Document) (target : Option Name := none) : IO Unit :=
  runMeta after.env do
    let stage := if target.isSome then "Merge" else "Additional imports"
    let replaced := target.map (theoremDeclarations before) |>.getD {}
    let mut mapping : NameMap Name := {}
    for (name, _) in before.owners.toArray do
      if let some current := existingName? after.env name then mapping := mapping.insert name current
    let mut beforeState : CollectAxioms.State := {}
    let mut afterState : CollectAxioms.State := {}
    for (name, _) in before.owners.toArray do
      if replaced.contains name then continue
      let some old := before.env.find? name | throwError "Missing original declaration: {name}"
      if (existingName? after.env name).isNone && (privateToUserName name).isInternalDetail then
        continue
      let some current := mapping.find? name | throwError "{stage} removed a declaration: {name}"
      let new ← getConstInfo current
      unless old.levelParams.length == new.levelParams.length &&
          (← equalTypes (rewrite old.type mapping) (aligned new.type new.levelParams old.levelParams) true) do
        throwError "{stage} changed the type of {name}"
      if isTheorem old then
        let (_, nextBefore) := ((CollectAxioms.collect name).run before.env).run beforeState
        -- Only retain visits from valid roots; unfinished proofs must not poison later checks.
        if nextBefore.axioms.all permittedAxiom then
          beforeState := nextBefore
          let (_, nextAfter) := ((CollectAxioms.collect current).run after.env).run afterState
          let bad := nextAfter.axioms.filter (!permittedAxiom ·)
          unless bad.isEmpty do
            throwError "{stage} introduced unsupported axioms in {name}: {bad}"
          afterState := nextAfter
      else
        if let some value := old.value? (allowOpaque := true) then
          let some newValue := new.value? (allowOpaque := true)
            | throwError "{stage} changed the declaration kind of {name}"
          unless ← equalTypes (rewrite value mapping) (aligned newValue new.levelParams old.levelParams) true do
            throwError "{stage} changed the value of {name}"

def bounds (doc : Document) (stx : Syntax) : IO (String.Pos.Raw × String.Pos.Raw) := do
  let some start := stx.getPos? | throw (IO.userError "Missing syntax start position")
  let some stop := stx.getTailPos? | throw (IO.userError "Missing syntax end position")
  let rawMap := doc.source.toFileMap
  let parserMap := doc.source.crlfToLf.toFileMap
  return (rawMap.ofPosition (parserMap.toPosition start),
    rawMap.ofPosition (parserMap.toPosition stop))

def sourceNewlines (doc : Document) (text : String) : String :=
  if doc.source.contains '\r' && !(doc.source.replace "\r\n" "").contains '\n' then
    text.replace "\n" "\r\n"
  else text

def slice (source : String) (start stop : String.Pos.Raw) : String :=
  String.Pos.Raw.extract source start stop

def headerText (doc : Document) : String :=
  let stop := doc.header.raw.getTailPos?.getD 0
  let stop := doc.source.toFileMap.ofPosition (doc.source.crlfToLf.toFileMap.toPosition stop)
  slice doc.source 0 stop

def extraImports (base donor : Document) : String := Id.run do
  let mut result := ""
  for imp in donor.header.imports do
    unless base.header.imports.any (fun other => other.module == imp.module) do
      result := result ++ s!"import {imp.module}\n"
  return result


-- A source command is reused as a whole, including declarations Lean generates for it.
def commandRefs (doc : Document) (cmd : CommandData) : NameSet := Id.run do
  let mut refs := cmd.refs
  for name in cmd.names do
    if let some info := doc.env.find? name then refs := refs ++ info.getUsedConstantsAsSet
  return refs

def nameMapping (base donor : Document) : NameMap Name := Id.run do
  let mut mapping := {}
  for (name, _) in donor.owners.toArray do
    if base.env.contains name then mapping := mapping.insert name name
    else if let some old := existingName? base.env name then mapping := mapping.insert name old
  return mapping

def reusableCommand (base donor : Document) (cmd : CommandData)
    (mapping : NameMap Name) (useDefEq : Bool) (allowUnfinished : Bool := false) : IO Bool := do
  if cmd.names.isEmpty then return false
  try
    runMeta base.env do
      for name in cmd.names do
        let some oldName := mapping.find? name | return false
        let some info := donor.env.find? name | return false
        let old ← getConstInfo oldName
        if info.levelParams.length != old.levelParams.length then return false
        let eq := fun a b => equalTypes
          (aligned (rewrite a mapping) info.levelParams old.levelParams) b useDefEq
        unless ← eq info.type old.type do return false
        match info, old with
        | .thmInfo _, .thmInfo _ => unless allowUnfinished do checkProof oldName
        | .inductInfo _, .inductInfo _ | .ctorInfo _, .ctorInfo _ | .recInfo _, .recInfo _ =>
          checkInductiveMember info mapping useDefEq
        | .defnInfo a, .defnInfo b =>
          unless a.safety == b.safety && (← eq a.value b.value) do return false
        | .opaqueInfo a, .opaqueInfo b =>
          unless a.isUnsafe == b.isUnsafe && (← eq a.value b.value) do return false
        | _, _ => return false
      return true
  catch _ => return false

-- Equality in the base environment is meaningful only when the constants in a
-- donor type/definition have also been matched. A reused theorem needs its type,
-- but may replace an entirely different proof, including a donor placeholder.
def reusableDependencies (doc : Document) (index : Nat) (reused : Std.HashSet Nat) : Bool := Id.run do
  let _ : Inhabited Environment := ⟨doc.env⟩
  for name in doc.commands[index]!.names do
    let some info := doc.env.find? name | return false
    let mut refs := info.type.headBeta.getUsedConstantsAsSet
    unless isTheorem info do
      if let some value := info.value? (allowOpaque := true) then
        refs := refs ++ value.headBeta.getUsedConstantsAsSet
    for dep in refs do
      if let some owner := doc.owners.find? dep then
        if owner != index && !reused.contains owner then return false
  return true

structure Selection where
  selected : Std.HashSet Nat := {}
  reused : NameSet := {}

-- Stop at reused declarations. In particular, a donor placeholder may use a completed
-- declaration from the current file, without copying its sorry or its dependencies.
def selectCommands (doc : Document) (seeds : Array Nat)
    (reuse : Std.HashSet Nat := {}) (mapping : NameMap Name := {}) : Selection := Id.run do
  let _ : Inhabited Environment := ⟨doc.env⟩
  let mut result : Selection := {}
  let mut seen : Std.HashSet Nat := {}
  let mut queue := seeds
  while !queue.isEmpty do
    let i := queue.back!
    queue := queue.pop
    if seen.contains i then continue
    seen := seen.insert i
    let cmd := doc.commands[i]!
    if reuse.contains i then
      for name in cmd.names do
        result := { result with reused := result.reused.insert ((mapping.find? name).getD name) }
      continue
    result := { result with selected := result.selected.insert i }
    queue := queue ++ cmd.scopes ++ (doc.scopeEnds[i]?).getD #[]
    if isScopeCommand cmd.stx then continue
    queue := queue ++ cmd.context
    let refs := commandRefs doc cmd
    for name in refs do
      if let some owner := doc.owners.find? name then queue := queue.push owner
    for j in [:i] do
      let previous := doc.commands[j]!
      if hasUntrackedEffect previous ||
          (isAttributeCommand previous.stx && previous.attributeTargets.toArray.any refs.contains) then
        queue := queue.push j
  return result

partial def declarationSyntaxAt? (stx : Syntax) (name : Name) (pos : String.Pos.Raw) : Option Syntax :=
  if stx.getKind == ``Parser.Command.declaration && (theoremSyntaxAt? stx name pos).isSome then
    some stx
  else stx.getArgs.findSome? (fun child => declarationSyntaxAt? child name pos)

def declarationSyntax (doc : Document) (name : Name) : IO Syntax := do
  let _ : Inhabited Environment := ⟨doc.env⟩
  let some owner := doc.owners.find? name | throw (IO.userError "Missing declaration owner")
  let some theoremStx := theoremSyntax? doc name | throw (IO.userError "Expected an explicit theorem/lemma")
  let some pos := theoremStx[1][0].getPos? | throw (IO.userError "Missing declaration position")
  return (declarationSyntaxAt? doc.commands[owner]!.stx name pos).getD theoremStx

-- Original text, with only the selected theorem's name/visibility adapted to the target.
def proofCommand (base donor : Document) (target candidate : Name) : IO String := do
  let _ : Inhabited Environment := ⟨donor.env⟩
  let some owner := donor.owners.find? candidate | throw (IO.userError "Missing proof command")
  let some stx := theoremSyntax? donor candidate | throw (IO.userError "Proof must be an explicit theorem/lemma")
  let (start, stop) ← bounds donor donor.commands[owner]!.stx
  let (idStart, idStop) ← bounds donor stx[1][0]
  let name := if privateToUserName candidate == privateToUserName target then
      slice donor.source idStart idStop
    else s!"_root_.{privateToUserName target}"
  let decl ← declarationSyntax donor candidate
  let (declStart, _) ← bounds donor decl
  let (theoremStart, _) ← bounds donor stx
  let oldDecl ← declarationSyntax base target
  let some oldTheorem := theoremSyntax? base target | throw (IO.userError "Missing target syntax")
  let (oldStart, _) ← bounds base oldDecl
  let (oldTheoremStart, _) ← bounds base oldTheorem
  -- Keep the target's documentation and attributes. The proof's binders and body stay intact.
  let modifiers := slice base.source oldStart oldTheoremStart
  return modifiers.crlfToLf ++ slice donor.source theoremStart idStart ++ name ++
    slice donor.source idStop stop

def selectedSource (doc : Document) (selected : Std.HashSet Nat)
    (replacement : Option (Nat × String) := none)
    (skip : NameSet := {}) (mapping : NameMap Name := {}) : IO String := do
  let _ : Inhabited Environment := ⟨doc.env⟩
  let mut output := ""
  let mut cursor := (headerText doc).rawEndPos
  for i in [:doc.commands.size] do
    let cmd := doc.commands[i]!
    let (start, stop) ← bounds doc cmd.stx
    if selected.contains i && !(cmd.names.size > 0 &&
        (cmd.names.all skip.contains || cmd.names.all (fun n => (mapping.find? n).isSome)) &&
        (replacement.map (fun r => r.1 == i) |>.getD false |>.not)) then
      let text := match replacement with
        | some (owner, text) => if owner == i then text else slice doc.source start stop
        | none => slice doc.source start stop
      -- Keep comments adjacent to retained commands, including comments before the first one.
      output := output ++ slice doc.source cursor start ++ text ++ "\n"
    cursor := stop
  return output ++ slice doc.source cursor doc.source.rawEndPos

def arrange (base donor : Document) (target candidate : Name) (selection : Selection) : IO String := do
  let _ : Inhabited Environment := ⟨base.env⟩
  let targetOwner := base.owners.get! target
  let replaced := theoremDeclarations base target
  let wholeTarget := base.commands[targetOwner]!.names.all replaced.contains
  let removed ← if wholeTarget then pure base.commands[targetOwner]!.stx else declarationSyntax base target
  let (removeStart, removeStop) ← bounds base removed
  let (ownerStart, ownerStop) ← bounds base base.commands[targetOwner]!.stx
  let remainingOwner := slice base.source ownerStart removeStart ++ slice base.source removeStop ownerStop
  -- Lift original dependencies together with their original context. Scope delimiters
  -- can be replayed; declarations are removed from their former positions, not copied.
  let seeds := selection.reused.toArray.filterMap base.owners.find?
  let lifted := selectCommands base seeds
  if lifted.selected.contains targetOwner then
    if wholeTarget then throw (IO.userError "Source order conflict: a dependency needs the unfinished target")
    for name in base.commands[targetOwner]!.names do
      if replaced.contains name then continue
      if let some info := base.env.find? name then
        if info.getUsedConstantsAsSet.toArray.any replaced.contains then
          throw (IO.userError "Source order conflict: a mutual dependency needs the unfinished target")
  let dependencies ← selectedSource base lifted.selected (some (targetOwner, remainingOwner))
  let replacement ← proofCommand base donor target candidate
  let mapping := nameMapping base donor
  let proofSource ← selectedSource donor selection.selected (some (donor.owners.get! candidate, replacement)) selection.reused mapping
  let mut rest := ""
  let mut cursor := (headerText base).rawEndPos
  for i in [:base.commands.size] do
    let cmd := base.commands[i]!
    let (start, stop) ← bounds base cmd.stx
    rest := rest ++ slice base.source cursor start
    if i == targetOwner then
      if !lifted.selected.contains i then rest := rest ++ remainingOwner
    else if lifted.selected.contains i && !isScopeCommand cmd.stx then pure ()
    else rest := rest ++ slice base.source start stop
    cursor := stop
  rest := rest ++ slice base.source cursor base.source.rawEndPos
  let dependencies := if lifted.selected.isEmpty then "" else "\nsection\n" ++ dependencies.crlfToLf ++ "\nend\n"
  -- Sections keep submitted variables, local notation and options out of the main file.
  return headerText base ++ sourceNewlines base
    (dependencies ++ "\nsection\n" ++ proofSource.crlfToLf ++ "\nend\n") ++ rest

structure Attempt where
  content : String
  candidate : Name
  reused : Array Name
  verified : Document

-- Equation lemmas may be generated lazily by a later tactic. Their source ranges
-- point to the original definition, not the command that first requested them.
def declaredInCommand (doc : Document) (cmd : CommandData) (name : Name) : Bool :=
  match declRangeExt.find? doc.env name, cmd.stx.getPos?, cmd.stx.getTailPos? with
  | some ranges, some start, some stop =>
    let pos := doc.source.crlfToLf.toFileMap.ofPosition ranges.selectionRange.pos
    start ≤ pos && pos < stop
  | _, _, _ => false

def mergeSelection (base donor : Document) (seeds : Array Nat) (req : Request)
    (replacement : Option (Name × Name) := none) : IO Selection := do
  let _ : Inhabited Environment := ⟨donor.env⟩
  let mapping := nameMapping base donor
  let owner := replacement.bind fun (_, candidate) => donor.owners.find? candidate
  let mut reuse : Std.HashSet Nat := {}
  for i in [:donor.commands.size] do
    if owner == some i then continue
    if replacement.any (fun (target, _) =>
        donor.commands[i]!.names.any (fun n => (mapping.find? n).any (· == target))) then continue
    if reusableDependencies donor i reuse &&
        (← reusableCommand base donor donor.commands[i]! mapping req.useDefEq req.declarationsOnly) then
      reuse := reuse.insert i
  let selection := selectCommands donor seeds reuse mapping
  for i in selection.selected.toArray do
    if owner == some i then continue
    for name in donor.commands[i]!.names do
      if let some old := mapping.find? name then
        let cmd := donor.commands[i]!
        if !declaredInCommand donor cmd name &&
            (← reusableCommand base donor { cmd with names := #[name] } mapping req.useDefEq) then continue
        throw (IO.userError s!"Source name conflict: {privateToUserName name} is not equivalent to existing {privateToUserName old}; rename it in the submitted source")
  return selection

unsafe def attempt (base donor : Document) (target candidate : Name) (req : Request) : IO Attempt := do
  let selection ← mergeSelection base donor #[donor.owners.get! candidate] req (some (target, candidate))
  let content ← arrange base donor target candidate selection
  let verified ← analyze content `LeanMergeBase req.setup
  let newTarget ← resolve verified (privateToUserName target).toString
  checkImportEffects base verified (some target)
  runMeta verified.env do
    let some before := base.env.find? target | throwError "Original target is missing"
    let after ← getConstInfo newTarget
    let mut currentNames : NameMap Name := {}
    for (name, _) in base.owners.toArray do
      if let some current := existingName? verified.env name then
        currentNames := currentNames.insert name current
    unless before.levelParams.length == after.levelParams.length &&
        (← equalTypes (rewrite before.type currentNames) (aligned after.type after.levelParams before.levelParams) req.useDefEq) do
      throwError "Type mismatch: {candidate} does not prove {target}"
    checkProofs (#[newTarget] ++ (verified.owners.toArray.map (·.1)).filter
      (fun n => (existingName? base.env n).isNone))
  return { content, candidate, reused := selection.reused.toArray, verified }

def addedCommands (before after : Document) (target : Option Name := none) : IO (Array SavedCommand) := do
  let mut added := #[]
  for cmd in after.commands do
    if target.any (fun t => cmd.names.any (fun n => privateToUserName n == privateToUserName t)) then continue
    let names := cmd.names.filter fun name =>
      (existingName? before.env name).isNone
    if names.isEmpty then continue
    let (start, stop) ← bounds after cmd.stx
    added := added.push {
      names := names.map (fun n => ((privateToUserName n).eraseMacroScopes).toString)
      source := slice after.source start stop }
  return added

unsafe def mergeDeclarations (base donor : Document) (req : Request) : IO Json := do
  let selection ← mergeSelection base donor (Array.range donor.commands.size) req
  let source ← selectedSource donor selection.selected (mapping := nameMapping base donor)
  let header := headerText base
  -- Each input starts with its own variables, local notation, options and open namespaces.
  let content := header ++ sourceNewlines base "\nsection\n" ++
    slice base.source header.rawEndPos base.source.rawEndPos ++
    sourceNewlines base ("\nend\n\nsection\n" ++ source.crlfToLf ++ "\nend\n")
  let verified ← analyze content `LeanMergeBase req.setup
  checkImportEffects base verified
  let inserted := (verified.owners.toArray.map (·.1)).filter (fun n => (existingName? base.env n).isNone)
  let usedAxioms ← runMeta verified.env (checkedAxioms inserted)
  let additions ← addedCommands base verified
  return json% { "okay": true, "content": $content, "source": $content,
    "strategy": "source", "declarations_only": true, "added_commands": $additions,
    "target": null, "proof": null, "inserted": $(additions.flatMap (·.names)),
    "reused": $(selection.reused.toArray.map Name.toString), "verified": true,
    "axioms": $(usedAxioms.map Name.toString) }

unsafe def merge (req : Request) : IO Json := do
  if req.declarationsOnly && (!req.target.isEmpty || !req.proof.isEmpty) then
    throw (IO.userError "--declarations-only cannot be combined with --target or --proof")
  let original ← analyze req.base `LeanMergeBase req.setup
  let donor ← analyze req.donor `LeanMergeDonor req.setup
  let additions := extraImports original donor
  let headerEnd := (headerText original).rawEndPos
  let combined := if additions.isEmpty then req.base else
    slice req.base 0 headerEnd ++ sourceNewlines original ("\n" ++ additions) ++ slice req.base headerEnd req.base.rawEndPos
  let base ← if additions.isEmpty then pure original else analyze combined `LeanMergeBase req.setup
  unless additions.isEmpty do checkImportEffects original base
  if req.declarationsOnly then return ← mergeDeclarations base donor req
  let target ← if req.target.isEmpty then do
      let unfinished := (declaredTheorems base).filter fun name =>
        hasOwnSorry base (theoremDeclarations base name) name
      match unfinished.toList with
      | [name] => pure name
      | _ => throw (IO.userError s!"Specify --target; found {unfinished.size} theorems with their own sorry: {unfinished.toList}")
    else resolve base req.target
  unless (← axioms base.env target).contains ``sorryAx do
    throw (IO.userError s!"Target {target} already has a complete proof")
  let candidates ← if req.proof.isEmpty then pure (declaredTheorems donor) else pure #[← resolve donor req.proof]
  let exact := candidates.filter (fun n => privateToUserName n == privateToUserName target)
  let mut successes : Array Attempt := #[]
  let mut failures : Array String := #[]
  for group in [exact, candidates.filter (!exact.contains ·)] do
    if !successes.isEmpty then break
    for candidate in group do
      try successes := successes.push (← attempt base donor target candidate req)
      catch e => failures := failures.push s!"{candidate}: {e}"
  let selected ← match successes.toList with
    | [one] => pure one
    | [] => throw (IO.userError ("No compatible complete proof found.\n" ++ String.intercalate "\n" failures.toList))
    | many => throw (IO.userError s!"Multiple matching proofs; specify --proof: {many.map (·.candidate)}")
  let additions ← addedCommands base selected.verified (some target)
  let newTarget ← resolve selected.verified (privateToUserName target).toString
  return json% { "okay": true, "content": $(selected.content), "source": $(selected.content),
    "strategy": "source", "added_commands": $additions, "target": $(newTarget.toString),
    "proof": $(selected.candidate.toString), "inserted": $(additions.flatMap (·.names)),
    "reused": $(selected.reused.map Name.toString), "verified": true,
    "axioms": $((← axioms selected.verified.env newTarget).map Name.toString) }

-- Compatibility entry point: normalization now extracts original commands and scopes.
unsafe def normalize (req : Request) : IO Json := do
  let doc ← analyze req.base `LeanMergeNormalize req.setup
  let targets ← if req.target.isEmpty then pure ((declaredTheorems doc).filter (!isPrivateName ·))
    else pure #[← resolve doc req.target]
  if targets.isEmpty then throw (IO.userError "No theorems to normalize")
  let selection := selectCommands doc (targets.map (fun n => doc.owners.get! n))
  let content := headerText doc ++ (← selectedSource doc selection.selected)
  let verified ← analyze content `LeanMergeNormalize req.setup
  let mapping := nameMapping verified doc
  for target in targets do
    let newTarget ← resolve verified (privateToUserName target).toString
    let some old := doc.env.find? target | throw (IO.userError "Missing original theorem")
    let some new := verified.env.find? newTarget | throw (IO.userError "Missing extracted theorem")
    unless old.levelParams.length == new.levelParams.length &&
        (← runMeta verified.env (equalTypes (rewrite old.type mapping)
          (aligned new.type new.levelParams old.levelParams) req.useDefEq)) do
      throw (IO.userError s!"Extraction changed theorem type: {target}")
  return json% { "okay": true, "verified": true, "content": $content,
    "normalize_stats": { "declarations": $selection.selected.size }, "targets": $(targets.map Name.toString) }

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
