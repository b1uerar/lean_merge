import Mathlib

structure Domino (n k : ℕ) where
  carrier : Finset (Fin n × Fin (2 * k))
  card : carrier.card = 2
  -- the two positions of the domino
  position : ∀ i ∈ carrier, ∀ j ∈ carrier, i ≠ j →
    -- i and j are on the same row and (i is left to j or j is left to i)
    (i.1.val = j.1.val ∧ (i.2.val + 1 = j.2.val ∨ j.2.val + 1 = i.2.val)) ∨ -- or
    -- i and j are on the same column and (i is above j or j is above i)
    (i.2.val = j.2.val ∧ (i.1.val + 1 = j.1.val ∨ j.1.val + 1 = i.1.val))

noncomputable instance {n k} : Fintype (Domino n k) :=
  Fintype.ofInjective Domino.carrier <| by
    rintro ⟨carrier, _⟩ ⟨carrier', _⟩ (rfl : carrier = carrier')
    rfl

structure PerfectCover (n k : ℕ) where
  -- the collections of tiles, each tile is a domino
  d_set : Finset (Domino n k)
  d_card : d_set.card = n * k
  -- every position on the board is covered by some dominos
  covers : ∀ i : Fin n × Fin (2 * k), ∃ d ∈ d_set, i ∈ d.carrier

noncomputable instance {n k} : Fintype (PerfectCover n k) :=
  Fintype.ofInjective PerfectCover.d_set <| by
    rintro ⟨d, _⟩ ⟨d', _⟩ (rfl : d = d')
    rfl


/-- The adjacency matrix of the `n × m` grid graph, over `ZMod 2`: two cells are
adjacent when they lie in the same row and are horizontally consecutive, or in the
same column and are vertically consecutive. -/
def gridAdj (n m : ℕ) : Matrix (Fin n × Fin m) (Fin n × Fin m) (ZMod 2) :=
  Matrix.of fun p q =>
    if (p.1.val = q.1.val ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) ∨
        (p.2.val = q.2.val ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val)) then 1 else 0


/-- The `ZMod 2`-valued checkerboard colour of a cell of an `n × m` board: `0` on one
colour class and `1` on the other. -/
def cellColour {n m : ℕ} (p : Fin n × Fin m) : ZMod 2 := (p.1.val + p.2.val : ZMod 2)

/-- The black cells of the `n × 2k` board, i.e. the cells of checkerboard colour `0`. -/
abbrev blackCell (n k : ℕ) : Type := {p : Fin n × Fin (2 * k) // cellColour p = 0}

/-- The white cells of the `n × 2k` board, i.e. the cells of checkerboard colour `1`. -/
abbrev whiteCell (n k : ℕ) : Type := {p : Fin n × Fin (2 * k) // cellColour p = 1}


/-- The number of perfect matchings of the `n × 2k` grid, i.e. of bijections from the
black cells to the white cells that only pair adjacent cells. -/
noncomputable def gridMatchingCount (n k : ℕ) : ℕ := by
  classical
  exact Fintype.card {f : blackCell n k → whiteCell n k //
    Function.Bijective f ∧ ∀ p, gridAdj n (2 * k) p.1 (f p).1 = 1}

namespace PerfectCoverBijection

open Classical

abbrev GridMatching (n k : ℕ) : Type :=
  {f : blackCell n k → whiteCell n k //
    Function.Bijective f ∧ ∀ p, gridAdj n (2 * k) p.1 (f p).1 = 1}

/-- The adjacency condition used in `gridAdj`, as a proposition. -/
def AdjCondition {n m : ℕ} (p q : Fin n × Fin m) : Prop :=
  (p.1.val = q.1.val ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) ∨
  (p.2.val = q.2.val ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val))

lemma gridAdj_eq_one_iff {n m : ℕ} (p q : Fin n × Fin m) :
    gridAdj n m p q = 1 ↔ AdjCondition p q := by
  unfold gridAdj
  rw [Matrix.of_apply]
  split <;> simp_all [AdjCondition]

lemma adjCondition_symm {n m : ℕ} {p q : Fin n × Fin m} (h : AdjCondition p q) :
    AdjCondition q p := by
  unfold AdjCondition at *
  rcases h with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩
  · exact Or.inl ⟨hr.symm, Or.inr hc⟩
  · exact Or.inl ⟨hr.symm, Or.inl hc⟩
  · exact Or.inr ⟨hc.symm, Or.inr hr⟩
  · exact Or.inr ⟨hc.symm, Or.inl hr⟩

lemma cellColour_ne_of_adjCondition {n m : ℕ} {p q : Fin n × Fin m}
    (h : AdjCondition p q) : cellColour p ≠ cellColour q := by
  intro heq
  change (p.1.val + p.2.val : ZMod 2) = (q.1.val + q.2.val : ZMod 2) at heq
  have heq' : ((p.1.val + p.2.val : ℕ) : ZMod 2) = ((q.1.val + q.2.val : ℕ) : ZMod 2) := by
    simpa only [Nat.cast_add] using heq
  have hmod : (p.1.val + p.2.val) % 2 = (q.1.val + q.2.val) % 2 :=
    (ZMod.natCast_eq_natCast_iff' (p.1.val + p.2.val) (q.1.val + q.2.val) 2).mp heq'
  unfold AdjCondition at h
  rcases h with ⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩ <;> omega

lemma cellColour_eq_zero_or_one {n m : ℕ} (p : Fin n × Fin m) :
    cellColour p = 0 ∨ cellColour p = 1 := by
  unfold cellColour
  have hval : (p.1.val + p.2.val) % 2 = 0 ∨ (p.1.val + p.2.val) % 2 = 1 := by omega
  rcases hval with h0 | h1
  · left
    simpa using (ZMod.natCast_eq_natCast_iff' (p.1.val + p.2.val) 0 2).mpr h0
  · right
    simpa using (ZMod.natCast_eq_natCast_iff' (p.1.val + p.2.val) 1 2).mpr h1

lemma domino_filter_black_card {n k : ℕ} (d : Domino n k) :
    (d.carrier.filter (fun p => cellColour p = 0)).card = 1 := by
  obtain ⟨a, b, hab, hc⟩ := Finset.card_eq_two.mp d.card
  have hne : cellColour a ≠ cellColour b :=
    cellColour_ne_of_adjCondition (d.position a (by rw [hc]; simp) b (by rw [hc]; simp) hab)
  rw [hc]
  rcases cellColour_eq_zero_or_one a with ha | ha <;>
    rcases cellColour_eq_zero_or_one b with hb | hb
  · exact (hne (ha.trans hb.symm)).elim
  · rw [Finset.filter_insert, Finset.filter_singleton]
    simp [ha, hb]
  · rw [Finset.filter_insert, Finset.filter_singleton]
    simp [ha, hb]
  · exact (hne (ha.trans hb.symm)).elim

lemma domino_filter_white_card {n k : ℕ} (d : Domino n k) :
    (d.carrier.filter (fun p => cellColour p = 1)).card = 1 := by
  obtain ⟨a, b, hab, hc⟩ := Finset.card_eq_two.mp d.card
  have hne : cellColour a ≠ cellColour b :=
    cellColour_ne_of_adjCondition (d.position a (by rw [hc]; simp) b (by rw [hc]; simp) hab)
  rw [hc]
  rcases cellColour_eq_zero_or_one a with ha | ha <;>
    rcases cellColour_eq_zero_or_one b with hb | hb
  · exact (hne (ha.trans hb.symm)).elim
  · rw [Finset.filter_insert, Finset.filter_singleton]
    simp [ha, hb]
  · rw [Finset.filter_insert, Finset.filter_singleton]
    simp [ha, hb]
  · exact (hne (ha.trans hb.symm)).elim

lemma existsUnique_black {n k : ℕ} (d : Domino n k) :
    ∃! p : Fin n × Fin (2 * k), p ∈ d.carrier ∧ cellColour p = 0 := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (domino_filter_black_card d)
  refine ⟨a, ?_, ?_⟩
  · have : a ∈ d.carrier.filter (fun p => cellColour p = 0) := by rw [ha]; simp
    simpa using this
  · intro b hb
    have : b ∈ d.carrier.filter (fun p => cellColour p = 0) := by simpa using hb
    rw [ha] at this
    simpa using this

lemma existsUnique_white {n k : ℕ} (d : Domino n k) :
    ∃! p : Fin n × Fin (2 * k), p ∈ d.carrier ∧ cellColour p = 1 := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (domino_filter_white_card d)
  refine ⟨a, ?_, ?_⟩
  · have : a ∈ d.carrier.filter (fun p => cellColour p = 1) := by rw [ha]; simp
    simpa using this
  · intro b hb
    have : b ∈ d.carrier.filter (fun p => cellColour p = 1) := by simpa using hb
    rw [ha] at this
    simpa using this

noncomputable def blackOfDomino {n k : ℕ} (d : Domino n k) : Fin n × Fin (2 * k) :=
  Classical.choose (existsUnique_black d)

lemma blackOfDomino_mem {n k : ℕ} (d : Domino n k) :
    blackOfDomino d ∈ d.carrier :=
  (Classical.choose_spec (existsUnique_black d)).1.1

lemma blackOfDomino_colour {n k : ℕ} (d : Domino n k) :
    cellColour (blackOfDomino d) = 0 :=
  (Classical.choose_spec (existsUnique_black d)).1.2

lemma eq_blackOfDomino {n k : ℕ} (d : Domino n k) {p : Fin n × Fin (2 * k)}
    (hp : p ∈ d.carrier) (hcol : cellColour p = 0) : p = blackOfDomino d :=
  (Classical.choose_spec (existsUnique_black d)).2 p ⟨hp, hcol⟩

noncomputable def whiteOfDomino {n k : ℕ} (d : Domino n k) : whiteCell n k :=
  ⟨Classical.choose (existsUnique_white d),
    (Classical.choose_spec (existsUnique_white d)).1.2⟩

lemma whiteOfDomino_mem {n k : ℕ} (d : Domino n k) :
    (whiteOfDomino d).1 ∈ d.carrier :=
  (Classical.choose_spec (existsUnique_white d)).1.1

lemma whiteOfDomino_colour {n k : ℕ} (d : Domino n k) :
    cellColour (whiteOfDomino d).1 = 1 :=
  (whiteOfDomino d).2

lemma eq_whiteOfDomino {n k : ℕ} (d : Domino n k) {p : Fin n × Fin (2 * k)}
    (hp : p ∈ d.carrier) (hcol : cellColour p = 1) : p = (whiteOfDomino d).1 :=
  (Classical.choose_spec (existsUnique_white d)).2 p ⟨hp, hcol⟩

abbrev Cell (n k : ℕ) := Fin n × Fin (2 * k)

def Incidence {n k : ℕ} (P : PerfectCover n k) : Type :=
  (d : {d : Domino n k // d ∈ P.d_set}) × {p : Cell n k // p ∈ d.1.carrier}

noncomputable instance {n k : ℕ} (P : PerfectCover n k) : Fintype (Incidence P) := by
  classical
  unfold Incidence
  infer_instance

lemma card_incidence {n k : ℕ} (P : PerfectCover n k) :
    Fintype.card (Incidence P) = n * (2 * k) := by
  classical
  unfold Incidence
  have hfiber : ∀ d : {d : Domino n k // d ∈ P.d_set},
      Fintype.card {p : Cell n k // p ∈ d.1.carrier} = 2 := by
    intro d
    simp [d.1.card]
  calc
    Fintype.card ((d : {d : Domino n k // d ∈ P.d_set}) × {p : Cell n k // p ∈ d.1.carrier})
        = ∑ d : {d : Domino n k // d ∈ P.d_set},
            Fintype.card {p : Cell n k // p ∈ d.1.carrier} := Fintype.card_sigma
    _ = ∑ _d : {d : Domino n k // d ∈ P.d_set}, 2 := by
      refine Finset.sum_congr rfl ?_
      intro d _
      exact hfiber d
    _ = Fintype.card {d : Domino n k // d ∈ P.d_set} * 2 := by simp
    _ = P.d_set.card * 2 := by
      congr 1
      simp
    _ = (n * k) * 2 := by rw [P.d_card]
    _ = n * (2 * k) := by ring

lemma unique_cover {n k : ℕ} (P : PerfectCover n k) (p : Cell n k) :
    ∃! d : Domino n k, d ∈ P.d_set ∧ p ∈ d.carrier := by
  classical
  let proj : Incidence P → Cell n k := fun x => x.2.1
  have hsurj : Function.Surjective proj := by
    intro p
    obtain ⟨d, hd, hp⟩ := P.covers p
    exact ⟨⟨⟨d, hd⟩, ⟨p, hp⟩⟩, rfl⟩
  have hinj : Function.Injective proj := by
    by_contra hnot
    have hlt := Fintype.card_lt_of_surjective_not_injective proj hsurj hnot
    rw [card_incidence P] at hlt
    simp at hlt
  obtain ⟨d0, hd0, hp0⟩ := P.covers p
  refine ⟨d0, ⟨hd0, hp0⟩, ?_⟩
  intro d ⟨hd, hp⟩
  let x : Incidence P := ⟨⟨d0, hd0⟩, ⟨p, hp0⟩⟩
  let y : Incidence P := ⟨⟨d, hd⟩, ⟨p, hp⟩⟩
  have hxy : x = y := hinj (by simp [proj, x, y])
  have : x.1.1 = y.1.1 := congrArg (fun z : Incidence P => z.1.1) hxy
  simpa [x, y] using this.symm

noncomputable def colEquiv (k : ℕ) : Fin (2 * k) ≃ Fin k × Fin 2 :=
  ((finProdFinEquiv (m := k) (n := 2)).trans (finCongr (Nat.mul_comm k 2))).symm

lemma colEquiv_symm_val (k : ℕ) (t : Fin k) (e : Fin 2) :
    ((colEquiv k).symm (t, e)).val = e.val + 2 * t.val := by
  rfl

def parityBit (n : ℕ) (i : Fin n) : Fin 2 := ⟨i.val % 2, by omega⟩

lemma color_eq_zero_iff (n : ℕ) (i : Fin n) (e : Fin 2) :
    (i.val + e.val : ZMod 2) = 0 ↔ e = parityBit n i := by
  constructor
  · intro h
    apply Fin.ext
    dsimp [parityBit]
    have hmod : (i.val + e.val) % 2 = 0 := by
      have := (ZMod.natCast_eq_natCast_iff (i.val + e.val) 0 2).mp (by simpa using h)
      simpa using this
    have he : e.val = 0 ∨ e.val = 1 := by omega
    rcases he with he | he <;> omega
  · rintro rfl
    dsimp [parityBit]
    rw [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_iff_mod_eq_zero.mpr (by omega)

noncomputable def cellEquiv (n k : ℕ) :
    Fin n × Fin (2 * k) ≃ Fin n × (Fin k × Fin 2) :=
  Equiv.prodCongr (Equiv.refl (Fin n)) (colEquiv k)

lemma cellColour_cellEquiv_symm (n k : ℕ) (i : Fin n) (t : Fin k) (e : Fin 2) :
    cellColour ((cellEquiv n k).symm (i, (t, e))) = (i.val + e.val : ZMod 2) := by
  unfold cellEquiv cellColour
  rw [Equiv.prodCongr_symm, Equiv.prodCongr_apply]
  simp only [Prod.map, Equiv.refl_symm, Equiv.refl_apply]
  rw [colEquiv_symm_val]
  push_cast
  have h2 : (2 * (t.val : ZMod 2)) = 0 := by
    change ((2 : ℕ) : ZMod 2) * (t.val : ZMod 2) = 0
    rw [ZMod.natCast_self, zero_mul]
  rw [← add_assoc, h2, add_zero]

def isBlackIndex (n k : ℕ) (i : Fin n) (x : Fin k × Fin 2) : Prop :=
  (i.val + x.2.val : ZMod 2) = 0

noncomputable def blackIndexEquiv (n k : ℕ) :
    {p : Fin n × Fin (2 * k) // cellColour p = 0} ≃
      {x : Fin n × (Fin k × Fin 2) // isBlackIndex n k x.1 x.2} :=
  Equiv.subtypeEquiv (cellEquiv n k) (by
    intro p
    constructor
    · intro hp
      rcases hpe : cellEquiv n k p with ⟨i, x⟩
      have hrepr : p = (cellEquiv n k).symm (i, x) := by
        rw [← hpe]
        exact (Equiv.symm_apply_apply (cellEquiv n k) p).symm
      rw [hrepr] at hp
      rw [cellColour_cellEquiv_symm] at hp
      simpa [isBlackIndex, hpe] using hp
    · intro hp
      rcases hpe : cellEquiv n k p with ⟨i, x⟩
      have hrepr : p = (cellEquiv n k).symm (i, x) := by
        rw [← hpe]
        exact (Equiv.symm_apply_apply (cellEquiv n k) p).symm
      rw [hrepr]
      rw [cellColour_cellEquiv_symm]
      simpa [isBlackIndex, hpe] using hp)

noncomputable def blackFiberEquiv (n k : ℕ) (i : Fin n) :
    {x : Fin k × Fin 2 // isBlackIndex n k i x} ≃ Fin k where
  toFun x := x.1.1
  invFun t := ⟨(t, parityBit n i), by
    dsimp [isBlackIndex]
    exact (color_eq_zero_iff n i (parityBit n i)).mpr rfl⟩
  left_inv x := by
    rcases x with ⟨⟨t, e⟩, hx⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact ((color_eq_zero_iff n i e).mp hx).symm
  right_inv x := rfl

noncomputable def blackEquiv (n k : ℕ) :
    {p : Fin n × Fin (2 * k) // cellColour p = 0} ≃ Fin n × Fin k :=
  (blackIndexEquiv n k).trans <|
    (Equiv.subtypeProdEquivSigmaSubtype (isBlackIndex n k)).trans <|
      (Equiv.sigmaCongrRight (fun i => blackFiberEquiv n k i)).trans
        (Equiv.sigmaEquivProd (Fin n) (Fin k))

lemma card_black (n k : ℕ) :
    Fintype.card {p : Fin n × Fin (2 * k) // cellColour p = 0} = n * k := by
  rw [Fintype.card_congr (blackEquiv n k)]
  simp


noncomputable def coverDomino {n k : ℕ} (P : PerfectCover n k) (b : blackCell n k) : Domino n k :=
  Classical.choose (P.covers b.1)

lemma coverDomino_mem {n k : ℕ} (P : PerfectCover n k) (b : blackCell n k) :
    coverDomino P b ∈ P.d_set :=
  (Classical.choose_spec (P.covers b.1)).1

lemma coverDomino_contains {n k : ℕ} (P : PerfectCover n k) (b : blackCell n k) :
    b.1 ∈ (coverDomino P b).carrier :=
  (Classical.choose_spec (P.covers b.1)).2

noncomputable def coverMap {n k : ℕ} (P : PerfectCover n k) : blackCell n k → whiteCell n k :=
  fun b => whiteOfDomino (coverDomino P b)

lemma gridAdj_coverMap {n k : ℕ} (P : PerfectCover n k) (b : blackCell n k) :
    gridAdj n (2 * k) b.1 (coverMap P b).1 = 1 := by
  rw [gridAdj_eq_one_iff]
  have hb : b.1 ∈ (coverDomino P b).carrier := coverDomino_contains P b
  have hw : (coverMap P b).1 ∈ (coverDomino P b).carrier := whiteOfDomino_mem _
  have hne : b.1 ≠ (coverMap P b).1 := by
    intro h
    have hblack : cellColour b.1 = 0 := b.2
    have hwhite : cellColour (coverMap P b).1 = 1 := whiteOfDomino_colour _
    rw [h] at hblack
    rw [hwhite] at hblack
    norm_num at hblack
  exact (coverDomino P b).position b.1 hb (coverMap P b).1 hw hne

lemma coverMap_injective {n k : ℕ} (P : PerfectCover n k) :
    Function.Injective (coverMap P) := by
  intro b1 b2 h
  have hw : (coverMap P b1).1 = (coverMap P b2).1 := congrArg Subtype.val h
  have hd1mem : (coverMap P b1).1 ∈ (coverDomino P b1).carrier := whiteOfDomino_mem _
  have hd2mem : (coverMap P b2).1 ∈ (coverDomino P b2).carrier := whiteOfDomino_mem _
  have hd_eq : coverDomino P b1 = coverDomino P b2 := by
    obtain ⟨d, hd, huniq⟩ := unique_cover P (coverMap P b1).1
    have h1 : coverDomino P b1 = d :=
      huniq _ ⟨coverDomino_mem P b1, hd1mem⟩
    have h2 : coverDomino P b2 = d := by
      apply huniq
      exact ⟨coverDomino_mem P b2, by rw [hw]; exact hd2mem⟩
    exact h1.trans h2.symm
  have hb1 : b1.1 ∈ (coverDomino P b1).carrier := coverDomino_contains P b1
  have hb2 : b2.1 ∈ (coverDomino P b1).carrier := by
    rw [hd_eq]
    exact coverDomino_contains P b2
  have hb_eq : b1.1 = b2.1 :=
    (eq_blackOfDomino (coverDomino P b1) hb1 b1.2).trans
      (eq_blackOfDomino (coverDomino P b1) hb2 b2.2).symm
  exact Subtype.ext hb_eq

lemma coverMap_surjective {n k : ℕ} (P : PerfectCover n k) :
    Function.Surjective (coverMap P) := by
  intro w
  obtain ⟨d, hd, hwmem⟩ := P.covers w.1
  let b : blackCell n k := ⟨blackOfDomino d, blackOfDomino_colour d⟩
  refine ⟨b, ?_⟩
  have hb_mem : b.1 ∈ d.carrier := blackOfDomino_mem d
  have hd_eq : coverDomino P b = d := by
    obtain ⟨d', hd', huniq⟩ := unique_cover P b.1
    have h1 : coverDomino P b = d' :=
      huniq _ ⟨coverDomino_mem P b, coverDomino_contains P b⟩
    have h2 : d = d' := huniq d ⟨hd, hb_mem⟩
    rw [h1, ← h2]
  apply Subtype.ext
  change (whiteOfDomino (coverDomino P b)).1 = w.1
  rw [hd_eq]
  exact (eq_whiteOfDomino d hwmem w.2).symm

lemma coverMap_bijective {n k : ℕ} (P : PerfectCover n k) :
    Function.Bijective (coverMap P) :=
  ⟨coverMap_injective P, coverMap_surjective P⟩

noncomputable def coverToMatching {n k : ℕ} (P : PerfectCover n k) : GridMatching n k :=
  ⟨coverMap P, coverMap_bijective P, fun b => gridAdj_coverMap P b⟩


noncomputable def edgeOfMatching {n k : ℕ} (M : GridMatching n k) (b : blackCell n k) : Domino n k where
  carrier := {b.1, (M.1 b).1}
  card := by
    have hne : b.1 ≠ (M.1 b).1 := by
      intro h
      have hb : cellColour b.1 = 0 := b.2
      have hw : cellColour (M.1 b).1 = 1 := (M.1 b).2
      rw [h] at hb
      rw [hw] at hb
      norm_num at hb
    exact Finset.card_pair hne
  position := by
    intro i hi j hj hij
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
    have hadj : gridAdj n (2 * k) b.1 (M.1 b).1 = 1 := M.2.2 b
    rw [gridAdj_eq_one_iff] at hadj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (hij rfl).elim
    · exact hadj
    · exact adjCondition_symm hadj
    · exact (hij rfl).elim

lemma edgeOfMatching_injective {n k : ℕ} (M : GridMatching n k) :
    Function.Injective (edgeOfMatching M) := by
  intro b1 b2 h
  have hcarrier : ({b1.1, (M.1 b1).1} : Finset (Fin n × Fin (2 * k))) =
      {b2.1, (M.1 b2).1} := by
    simpa [edgeOfMatching] using congrArg Domino.carrier h
  have hmem : b1.1 ∈ ({b2.1, (M.1 b2).1} : Finset (Fin n × Fin (2 * k))) := by
    rw [← hcarrier]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h
  · exact Subtype.ext h
  · exfalso
    have hb : cellColour b1.1 = 0 := b1.2
    have hw : cellColour (M.1 b2).1 = 1 := (M.1 b2).2
    rw [h] at hb
    rw [hw] at hb
    norm_num at hb

noncomputable def matchingToCover {n k : ℕ} (M : GridMatching n k) : PerfectCover n k where
  d_set := Finset.univ.image (edgeOfMatching M)
  d_card := by
    rw [Finset.card_image_of_injective]
    · rw [Finset.card_univ, card_black]
    · exact edgeOfMatching_injective M
  covers := by
    intro p
    rcases cellColour_eq_zero_or_one p with hp | hp
    · let b : blackCell n k := ⟨p, hp⟩
      refine ⟨edgeOfMatching M b, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
      · simp [edgeOfMatching, b]
    · let w : whiteCell n k := ⟨p, hp⟩
      rcases M.2.1.2 w with ⟨b, hb⟩
      refine ⟨edgeOfMatching M b, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
      · have hval : (M.1 b).1 = p := by rw [hb]
        simp [edgeOfMatching, hval]


lemma Domino.eq_of_carrier_eq {n k : ℕ} {d e : Domino n k} (h : d.carrier = e.carrier) : d = e := by
  cases d
  cases e
  simp only at h
  subst h
  rfl

lemma PerfectCover.eq_of_d_set_eq {n k : ℕ} {P Q : PerfectCover n k} (h : P.d_set = Q.d_set) : P = Q := by
  cases P
  cases Q
  simp only at h
  subst h
  rfl


lemma edgeOfMatching_coverToMatching_eq_coverDomino {n k : ℕ} (P : PerfectCover n k)
    (b : blackCell n k) :
    edgeOfMatching (coverToMatching P) b = coverDomino P b := by
  apply Domino.eq_of_carrier_eq
  change ({b.1, (coverMap P b).1} : Finset (Fin n × Fin (2 * k))) = (coverDomino P b).carrier
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact coverDomino_contains P b
    · exact whiteOfDomino_mem _
  · have hne : b.1 ≠ (coverMap P b).1 := by
      intro h
      have hb : cellColour b.1 = 0 := b.2
      have hw : cellColour (coverMap P b).1 = 1 := whiteOfDomino_colour _
      rw [h] at hb
      rw [hw] at hb
      norm_num at hb
    rw [Finset.card_pair hne]
    rw [(coverDomino P b).card]

lemma d_set_matchingToCover_coverToMatching {n k : ℕ} (P : PerfectCover n k) :
    (matchingToCover (coverToMatching P)).d_set = P.d_set := by
  ext d
  constructor
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨b, -, rfl⟩
    rw [edgeOfMatching_coverToMatching_eq_coverDomino]
    exact coverDomino_mem P b
  · intro hd
    apply Finset.mem_image.mpr
    let b : blackCell n k := ⟨blackOfDomino d, blackOfDomino_colour d⟩
    refine ⟨b, Finset.mem_univ _, ?_⟩
    rw [edgeOfMatching_coverToMatching_eq_coverDomino]
    obtain ⟨d', hd', huniq⟩ := unique_cover P b.1
    have h1 : coverDomino P b = d' :=
      huniq _ ⟨coverDomino_mem P b, coverDomino_contains P b⟩
    have h2 : d = d' := huniq d ⟨hd, blackOfDomino_mem d⟩
    rw [h1, ← h2]

lemma matchingToCover_coverToMatching {n k : ℕ} (P : PerfectCover n k) :
    matchingToCover (coverToMatching P) = P :=
  PerfectCover.eq_of_d_set_eq (d_set_matchingToCover_coverToMatching P)

lemma coverDomino_matchingToCover_eq_edge {n k : ℕ} (M : GridMatching n k)
    (b : blackCell n k) :
    coverDomino (matchingToCover M) b = edgeOfMatching M b := by
  obtain ⟨d, hd, huniq⟩ := unique_cover (matchingToCover M) b.1
  have h1 : coverDomino (matchingToCover M) b = d :=
    huniq _ ⟨coverDomino_mem _ b, coverDomino_contains _ b⟩
  have hedge_mem : edgeOfMatching M b ∈ (matchingToCover M).d_set :=
    Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
  have hedge_contains : b.1 ∈ (edgeOfMatching M b).carrier := by
    simp [edgeOfMatching]
  have h2 : edgeOfMatching M b = d := huniq _ ⟨hedge_mem, hedge_contains⟩
  exact h1.trans h2.symm

lemma coverToMatching_matchingToCover {n k : ℕ} (M : GridMatching n k) :
    coverToMatching (matchingToCover M) = M := by
  apply Subtype.ext
  funext b
  apply Subtype.ext
  change (whiteOfDomino (coverDomino (matchingToCover M) b)).1 = (M.1 b).1
  rw [coverDomino_matchingToCover_eq_edge]
  have hmem : (M.1 b).1 ∈ (edgeOfMatching M b).carrier := by
    simp [edgeOfMatching]
  exact (eq_whiteOfDomino (edgeOfMatching M b) hmem (M.1 b).2).symm

noncomputable def perfectCoverEquivGridMatching (n k : ℕ) :
    PerfectCover n k ≃ GridMatching n k where
  toFun := coverToMatching
  invFun := matchingToCover
  left_inv := matchingToCover_coverToMatching
  right_inv := coverToMatching_matchingToCover

lemma card_perfectCover_eq_gridMatchingCount (n k : ℕ) :
    Fintype.card (PerfectCover n k) = Fintype.card (GridMatching n k) :=
  Fintype.card_congr (perfectCoverEquivGridMatching n k)



end PerfectCoverBijection


/-- Every perfect cover of the `n × 2k` board determines, and is determined by, a perfect
matching of the grid graph: each domino pairs one black cell with an adjacent white
cell. -/
theorem card_perfectCover_eq_gridMatchingCount (n k : ℕ) :
    Fintype.card (PerfectCover n k) = gridMatchingCount n k :=
  PerfectCoverBijection.card_perfectCover_eq_gridMatchingCount n k


