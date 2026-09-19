import Mathlib
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

structure Domino (n k : ℕ) where
  carrier : Finset (Fin n × Fin (2 * k))
  card : carrier.card = 2
  position : ∀ i ∈ carrier, ∀ j ∈ carrier, i ≠ j →
    (i.1.val = j.1.val ∧ (i.2.val + 1 = j.2.val ∨ j.2.val + 1 = i.2.val)) ∨
    (i.2.val = j.2.val ∧ (i.1.val + 1 = j.1.val ∨ j.1.val + 1 = i.1.val))

noncomputable instance {n k} : Fintype (Domino n k) :=
  Fintype.ofInjective Domino.carrier <| by
    rintro ⟨carrier, _⟩ ⟨carrier', _⟩ (rfl : carrier = carrier')
    rfl

deriving instance DecidableEq for Domino

structure PerfectCover (n k : ℕ) where
  d_set : Finset (Domino n k)
  d_card : d_set.card = n * k
  covers : ∀ i : Fin n × Fin (2 * k), ∃ d ∈ d_set, i ∈ d.carrier

noncomputable instance {n k} : Fintype (PerfectCover n k) :=
  Fintype.ofInjective PerfectCover.d_set <| by
    rintro ⟨d, _⟩ ⟨d', _⟩ (rfl : d = d')
    rfl

deriving instance DecidableEq for PerfectCover

namespace BrualdiCh1_5

open Finset

abbrev C := Fin 3 × Fin 4
abbrev State := Finset (Fin 3)

def cell (r : Fin 3) (c : Fin 4) : C := (r, c)

@[simp] lemma cell_fst (r : Fin 3) (c : Fin 4) : (cell r c).1 = r := rfl
@[simp] lemma cell_snd (r : Fin 3) (c : Fin 4) : (cell r c).2 = c := rfl

abbrev Adj (i j : C) : Prop :=
  (i.1.val = j.1.val ∧ (i.2.val + 1 = j.2.val ∨ j.2.val + 1 = i.2.val)) ∨
  (i.2.val = j.2.val ∧ (i.1.val + 1 = j.1.val ∨ j.1.val + 1 = i.1.val))

noncomputable def domOf (c : PerfectCover 3 2) (x : C) : Domino 3 2 :=
  Classical.choose (c.covers x)

lemma domOf_mem (c : PerfectCover 3 2) (x : C) : domOf c x ∈ c.d_set :=
  (Classical.choose_spec (c.covers x)).1

lemma domOf_covers (c : PerfectCover 3 2) (x : C) : x ∈ (domOf c x).carrier :=
  (Classical.choose_spec (c.covers x)).2

lemma cover_unique (c : PerfectCover 3 2) (x : C) :
    (c.d_set.filter (fun d => x ∈ d.carrier)).card = 1 := by
  classical
  set A : Finset (Σ _ : Domino 3 2, C) := c.d_set.sigma (fun d => d.carrier) with hA
  have hAcard : A.card = 3 * (2*2) := by
    rw [hA, Finset.card_sigma]
    rw [Finset.sum_const_nat (f := fun d : Domino 3 2 => d.carrier.card) (m := 2) (fun d _ => d.card), c.d_card]
  have himg : A.image (fun p : (Σ _ : Domino 3 2, C) => p.2) = Finset.univ := by
    ext y
    constructor
    · intro _; exact Finset.mem_univ y
    · intro _
      obtain ⟨d, hd, hdy⟩ := c.covers y
      exact Finset.mem_image.mpr ⟨⟨d, y⟩, by rw [hA]; exact Finset.mem_sigma.mpr ⟨hd, hdy⟩, rfl⟩
  have hcarduniv : (Finset.univ : Finset C).card = 3 * (2*2) := by
    simp [Fintype.card_prod]
  have hinj : Set.InjOn (fun p : (Σ _ : Domino 3 2, C) => p.2) (A : Set _) := by
    apply Finset.injOn_of_card_image_eq
    rw [himg, hcarduniv, hAcard]
  have hle1 : (c.d_set.filter (fun d => x ∈ d.carrier)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro d hd e he
    rw [Finset.mem_filter] at hd he
    have hpd : (⟨d, x⟩ : Σ _ : Domino 3 2, C) ∈ A := by
      rw [hA]; exact Finset.mem_sigma.mpr ⟨hd.1, hd.2⟩
    have hpe : (⟨e, x⟩ : Σ _ : Domino 3 2, C) ∈ A := by
      rw [hA]; exact Finset.mem_sigma.mpr ⟨he.1, he.2⟩
    have h_eq := hinj hpd hpe rfl
    exact congrArg Sigma.fst h_eq
  have hge1 : 1 ≤ (c.d_set.filter (fun d => x ∈ d.carrier)).card :=
    Finset.card_pos.mpr ⟨domOf c x, Finset.mem_filter.mpr ⟨domOf_mem c x, domOf_covers c x⟩⟩
  omega

lemma domOf_unique (c : PerfectCover 3 2) {d : Domino 3 2} {x : C}
    (hd : d ∈ c.d_set) (hx : x ∈ d.carrier) : d = domOf c x :=
  Finset.card_le_one.mp (le_of_eq (cover_unique c x)) d
    (Finset.mem_filter.mpr ⟨hd, hx⟩) (domOf c x)
    (Finset.mem_filter.mpr ⟨domOf_mem c x, domOf_covers c x⟩)

def profMid (c : PerfectCover 3 2) (m : Fin 3) : State :=
  univ.filter (fun r => ∃ d ∈ c.d_set, cell r (Fin.castSucc m) ∈ d.carrier ∧ cell r m.succ ∈ d.carrier)

lemma mem_profMid (c : PerfectCover 3 2) (m r : Fin 3) :
    r ∈ profMid c m ↔ ∃ d ∈ c.d_set, cell r (Fin.castSucc m) ∈ d.carrier ∧ cell r m.succ ∈ d.carrier := by
  simp [profMid]

def horiz (c : PerfectCover 3 2) (x : C) : Prop :=
  ∃ d ∈ c.d_set, x ∈ d.carrier ∧ ∃ y ∈ d.carrier, y ≠ x ∧ y.1 = x.1

lemma horiz_zero (c : PerfectCover 3 2) (r : Fin 3) :
    horiz c (cell r 0) ↔ r ∈ profMid c 0 := by
  constructor
  · rintro ⟨d, hd, hx, y, hy, hyne, hyrow⟩
    have hAdj : Adj (cell r 0) y := d.position _ hx _ hy (Ne.symm hyne)
    obtain ⟨ry, cy⟩ := y
    have hry : ry = r := by simpa using hyrow
    rw [hry] at hy hyne hAdj
    fin_cases cy
    · exact absurd rfl hyne
    · exact (mem_profMid c 0 r).mpr ⟨d, hd, by simpa using hx, by simpa [cell] using hy⟩
    · exfalso; simp [Adj] at hAdj
    · exfalso; simp [Adj] at hAdj
  · intro hr
    obtain ⟨d, hd, h1, h2⟩ := (mem_profMid c 0 r).mp hr
    exact ⟨d, hd, by simpa using h1, cell r 1, by simpa using h2, by simp [cell], rfl⟩

lemma horiz_three (c : PerfectCover 3 2) (r : Fin 3) :
    horiz c (cell r 3) ↔ r ∈ profMid c 2 := by
  constructor
  · rintro ⟨d, hd, hx, y, hy, hyne, hyrow⟩
    have hAdj : Adj (cell r 3) y := d.position _ hx _ hy (Ne.symm hyne)
    obtain ⟨ry, cy⟩ := y
    have hry : ry = r := by simpa using hyrow
    rw [hry] at hy hyne hAdj
    fin_cases cy
    · exfalso; simp [Adj] at hAdj
    · exfalso; simp [Adj] at hAdj
    · exact (mem_profMid c 2 r).mpr ⟨d, hd, by simpa [cell] using hy, by simpa using hx⟩
    · exact absurd rfl hyne
  · intro hr
    obtain ⟨d, hd, h1, h2⟩ := (mem_profMid c 2 r).mp hr
    exact ⟨d, hd, by simpa using h2, cell r 2, by simpa using h1, by simp [cell], rfl⟩

lemma horiz_one (c : PerfectCover 3 2) (r : Fin 3) :
    horiz c (cell r 1) ↔ r ∈ profMid c 0 ∨ r ∈ profMid c 1 := by
  constructor
  · rintro ⟨d, hd, hx, y, hy, hyne, hyrow⟩
    have hAdj : Adj (cell r 1) y := d.position _ hx _ hy (Ne.symm hyne)
    obtain ⟨ry, cy⟩ := y
    have hry : ry = r := by simpa using hyrow
    rw [hry] at hy hyne hAdj
    fin_cases cy
    · exact Or.inl ((mem_profMid c 0 r).mpr ⟨d, hd, by simpa [cell] using hy, by simpa using hx⟩)
    · exact absurd rfl hyne
    · exact Or.inr ((mem_profMid c 1 r).mpr ⟨d, hd, by simpa using hx, by simpa [cell] using hy⟩)
    · exfalso; simp [Adj] at hAdj
  · rintro (hr | hr)
    · obtain ⟨d, hd, h1, h2⟩ := (mem_profMid c 0 r).mp hr
      exact ⟨d, hd, by simpa using h2, cell r 0, by simpa using h1, by simp [cell], rfl⟩
    · obtain ⟨d, hd, h1, h2⟩ := (mem_profMid c 1 r).mp hr
      exact ⟨d, hd, by simpa using h1, cell r 2, by simpa using h2, by simp [cell], rfl⟩

lemma horiz_two (c : PerfectCover 3 2) (r : Fin 3) :
    horiz c (cell r 2) ↔ r ∈ profMid c 1 ∨ r ∈ profMid c 2 := by
  constructor
  · rintro ⟨d, hd, hx, y, hy, hyne, hyrow⟩
    have hAdj : Adj (cell r 2) y := d.position _ hx _ hy (Ne.symm hyne)
    obtain ⟨ry, cy⟩ := y
    have hry : ry = r := by simpa using hyrow
    rw [hry] at hy hyne hAdj
    fin_cases cy
    · exfalso; simp [Adj] at hAdj
    · exact Or.inl ((mem_profMid c 1 r).mpr ⟨d, hd, by simpa [cell] using hy, by simpa using hx⟩)
    · exact absurd rfl hyne
    · exact Or.inr ((mem_profMid c 2 r).mpr ⟨d, hd, by simpa using hx, by simpa [cell] using hy⟩)
  · rintro (hr | hr)
    · obtain ⟨d, hd, h1, h2⟩ := (mem_profMid c 1 r).mp hr
      exact ⟨d, hd, by simpa using h2, cell r 1, by simpa using h1, by simp [cell], rfl⟩
    · obtain ⟨d, hd, h1, h2⟩ := (mem_profMid c 2 r).mp hr
      exact ⟨d, hd, by simpa using h1, cell r 3, by simpa using h2, by simp [cell], rfl⟩

def Lp (q : Fin 3 → State) : Fin 4 → State
  | ⟨0, _⟩ => ∅
  | ⟨1, _⟩ => q 0
  | ⟨2, _⟩ => q 1
  | ⟨3, _⟩ => q 2

def Rp (q : Fin 3 → State) : Fin 4 → State
  | ⟨0, _⟩ => q 0
  | ⟨1, _⟩ => q 1
  | ⟨2, _⟩ => q 2
  | ⟨3, _⟩ => ∅

lemma horiz_iff_profLR (c : PerfectCover 3 2) (r : Fin 3) (j : Fin 4) :
    horiz c (cell r j) ↔ r ∈ (Lp (profMid c) j ∪ Rp (profMid c) j) := by
  fin_cases j <;> simp [Lp, Rp, horiz_zero, horiz_one, horiz_two, horiz_three]

lemma three_contra {d : Domino 3 2} {a b cc : C}
    (ha : a ∈ d.carrier) (hb : b ∈ d.carrier) (hc : cc ∈ d.carrier)
    (hab : a ≠ b) (hac : a ≠ cc) (hbc : b ≠ cc) : False := by
  have hsub : (insert a (insert b ({cc} : Finset C))) ⊆ d.carrier := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hcard : (insert a (insert b ({cc} : Finset C))).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
        Finset.card_insert_of_notMem (by simp [hbc]),
        Finset.card_singleton]
  have := Finset.card_le_card hsub
  rw [d.card] at this
  omega

lemma profMid_disj01 (c : PerfectCover 3 2) : ∀ r, r ∈ profMid c 0 → r ∉ profMid c 1 := by
  intro r h0 h1
  obtain ⟨d, hd, ha, hb⟩ := (mem_profMid c 0 r).mp h0
  obtain ⟨e, he, hc, hd'⟩ := (mem_profMid c 1 r).mp h1
  have heq : d = e := by
    rw [domOf_unique c hd (by simpa using hb), domOf_unique c he (by simpa using hc)]
  subst heq
  exact three_contra (by simpa using ha) (by simpa using hb) (by simpa using hd')
    (by simp [cell]) (by simp [cell]) (by simp [cell])

lemma profMid_disj12 (c : PerfectCover 3 2) : ∀ r, r ∈ profMid c 1 → r ∉ profMid c 2 := by
  intro r h1 h2
  obtain ⟨d, hd, ha, hb⟩ := (mem_profMid c 1 r).mp h1
  obtain ⟨e, he, hc, hd'⟩ := (mem_profMid c 2 r).mp h2
  have heq : d = e := by
    rw [domOf_unique c hd (by simpa using hb), domOf_unique c he (by simpa using hc)]
  subst heq
  exact three_contra (by simpa using ha) (by simpa using hb) (by simpa using hd')
    (by simp [cell]) (by simp [cell]) (by simp [cell])

lemma q_lemma (Q : State)
    (h : ∃ f : Fin 3 → Fin 3, (∀ r, r ∈ Q → f r ∈ Q) ∧ (∀ r, r ∈ Q → f r ≠ r) ∧
        (∀ r, r ∈ Q → f (f r) = r) ∧
        (∀ r, r ∈ Q → (f r).val + 1 = r.val ∨ r.val + 1 = (f r).val)) :
    Q ∈ ({∅, ({0,1} : State), ({1,2} : State)} : Finset State) := by
  decide +revert


private lemma partner_exists (c : PerfectCover 3 2) (x : C) :
    ∃ y ∈ (domOf c x).carrier, y ≠ x :=
  Finset.exists_mem_ne (by rw [(domOf c x).card]; norm_num) x

noncomputable def partnerCell (c : PerfectCover 3 2) (x : C) : C :=
  Classical.choose (partner_exists c x)

lemma partnerCell_mem (c : PerfectCover 3 2) (x : C) : partnerCell c x ∈ (domOf c x).carrier :=
  (Classical.choose_spec (partner_exists c x)).1

lemma partnerCell_ne (c : PerfectCover 3 2) (x : C) : partnerCell c x ≠ x :=
  (Classical.choose_spec (partner_exists c x)).2

lemma partnerCell_eq (c : PerfectCover 3 2) {x y : C}
    (hy : y ∈ (domOf c x).carrier) (hne : y ≠ x) : y = partnerCell c x := by
  have hx : x ∈ (domOf c x).carrier := domOf_covers c x
  have hcarderase : ((domOf c x).carrier.erase x).card = 1 := by
    rw [Finset.card_erase_of_mem hx, (domOf c x).card]
  have hy' : y ∈ (domOf c x).carrier.erase x := Finset.mem_erase.mpr ⟨hne, hy⟩
  have hpc' : partnerCell c x ∈ (domOf c x).carrier.erase x :=
    Finset.mem_erase.mpr ⟨partnerCell_ne c x, partnerCell_mem c x⟩
  exact Finset.card_le_one.mp (le_of_eq hcarderase) y hy' (partnerCell c x) hpc'

noncomputable def rowPartner (c : PerfectCover 3 2) (j : Fin 4) (r : Fin 3) : Fin 3 :=
  (partnerCell c (cell r j)).1

lemma rowPartner_ne (c : PerfectCover 3 2) {r : Fin 3} {j : Fin 4}
    (hr : ¬ horiz c (cell r j)) : rowPartner c j r ≠ r := by
  intro h1
  refine hr ⟨domOf c (cell r j), domOf_mem c _, domOf_covers c _, partnerCell c (cell r j),
    partnerCell_mem c _, partnerCell_ne c _, ?_⟩
  simpa [rowPartner] using h1

lemma partnerCell_snd (c : PerfectCover 3 2) {r : Fin 3} {j : Fin 4}
    (hr : ¬ horiz c (cell r j)) : (partnerCell c (cell r j)).2 = j := by
  have hAdj : Adj (cell r j) (partnerCell c (cell r j)) :=
    (domOf c (cell r j)).position _ (domOf_covers c _) _ (partnerCell_mem c _)
      (Ne.symm (partnerCell_ne c _))
  have h1 : (partnerCell c (cell r j)).1 ≠ r := rowPartner_ne c hr
  rcases hAdj with ⟨ha, _⟩ | ⟨ha, _⟩
  · exact absurd (Fin.ext ha.symm) h1
  · simpa using Fin.ext ha.symm

lemma rowPartner_adj (c : PerfectCover 3 2) {r : Fin 3} {j : Fin 4}
    (hr : ¬ horiz c (cell r j)) :
    (rowPartner c j r).val + 1 = r.val ∨ r.val + 1 = (rowPartner c j r).val := by
  have hAdj : Adj (cell r j) (partnerCell c (cell r j)) :=
    (domOf c (cell r j)).position _ (domOf_covers c _) _ (partnerCell_mem c _)
      (Ne.symm (partnerCell_ne c _))
  have h1 : (partnerCell c (cell r j)).1 ≠ r := rowPartner_ne c hr
  rcases hAdj with ⟨ha, _⟩ | ⟨ha, hb⟩
  · exact absurd (Fin.ext ha.symm) h1
  · simpa [rowPartner, or_comm] using hb

lemma rowPartner_eq_partner (c : PerfectCover 3 2) {r : Fin 3} {j : Fin 4}
    (hr : ¬ horiz c (cell r j)) :
    cell (rowPartner c j r) j = partnerCell c (cell r j) := by
  have hy2 : (partnerCell c (cell r j)).2 = j := partnerCell_snd c hr
  have : partnerCell c (cell r j) = cell (rowPartner c j r) j := by
    rw [cell, rowPartner]
    exact Prod.ext rfl hy2
  exact this.symm

lemma rowPartner_not_horiz (c : PerfectCover 3 2) {r : Fin 3} {j : Fin 4}
    (hr : ¬ horiz c (cell r j)) : ¬ horiz c (cell (rowPartner c j r) j) := by
  intro hh
  have hyx : cell (rowPartner c j r) j = partnerCell c (cell r j) := rowPartner_eq_partner c hr
  rcases hh with ⟨e, he, hec, z, hz, hzne, hzrow⟩
  have heq1 : e = domOf c (cell (rowPartner c j r) j) := domOf_unique c he hec
  have heq2 : domOf c (cell r j) = domOf c (cell (rowPartner c j r) j) :=
    domOf_unique c (domOf_mem c _) (by rw [hyx]; exact partnerCell_mem c _)
  have hz' : z ∈ (domOf c (cell r j)).carrier := by
    rw [heq2, ← heq1]; exact hz
  have h1 : (partnerCell c (cell r j)).1 ≠ r := rowPartner_ne c hr
  have hzrow' : z.1 = rowPartner c j r := by simpa [cell] using hzrow
  have hxy : cell r j ≠ partnerCell c (cell r j) := Ne.symm (partnerCell_ne c _)
  have hyz : partnerCell c (cell r j) ≠ z := by
    intro h; exact hzne (hyx.trans h).symm
  have hxz : cell r j ≠ z := by
    intro h
    have hz1 : r = z.1 := by simpa using congrArg Prod.fst h
    exact h1 (hz1.trans hzrow').symm
  exact three_contra (domOf_covers c (cell r j)) (partnerCell_mem c _) hz' hxy hxz hyz

lemma rowPartner_invol (c : PerfectCover 3 2) {r : Fin 3} {j : Fin 4}
    (hr : ¬ horiz c (cell r j)) : rowPartner c j (rowPartner c j r) = r := by
  have hyx : cell (rowPartner c j r) j = partnerCell c (cell r j) := rowPartner_eq_partner c hr
  have hdom : domOf c (cell r j) = domOf c (cell (rowPartner c j r) j) :=
    domOf_unique c (domOf_mem c _) (by rw [hyx]; exact partnerCell_mem c _)
  have hpc : cell r j = partnerCell c (cell (rowPartner c j r) j) := by
    apply partnerCell_eq
    · rw [← hdom]; exact domOf_covers c (cell r j)
    · intro h
      exact rowPartner_ne c hr (by simpa [cell] using congrArg Prod.fst h.symm)
  simpa [rowPartner] using (congrArg Prod.fst hpc).symm


lemma not_horiz_of_mem_Q (c : PerfectCover 3 2) {r : Fin 3} {j : Fin 4}
    (hr : r ∈ univ \ (Lp (profMid c) j ∪ Rp (profMid c) j)) : ¬ horiz c (cell r j) := by
  intro hh
  exact (Finset.mem_sdiff.mp hr).2 ((horiz_iff_profLR c r j).mp hh)

lemma mem_Q_of_not_horiz (c : PerfectCover 3 2) {r : Fin 3} {j : Fin 4}
    (hr : ¬ horiz c (cell r j)) : r ∈ univ \ (Lp (profMid c) j ∪ Rp (profMid c) j) :=
  Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hmem => hr ((horiz_iff_profLR c r j).mpr hmem)⟩

lemma rowPartner_mem_Q (c : PerfectCover 3 2) {r : Fin 3} {j : Fin 4}
    (hr : ¬ horiz c (cell r j)) : rowPartner c j r ∈ univ \ (Lp (profMid c) j ∪ Rp (profMid c) j) :=
  mem_Q_of_not_horiz c (rowPartner_not_horiz c hr)

lemma columnQ (c : PerfectCover 3 2) (j : Fin 4) :
    (univ \ (Lp (profMid c) j ∪ Rp (profMid c) j)) ∈
      ({∅, ({0,1} : State), ({1,2} : State)} : Finset State) := by
  set Q : State := univ \ (Lp (profMid c) j ∪ Rp (profMid c) j) with hQ
  have hnot : ∀ r, r ∈ Q → ¬ horiz c (cell r j) := by
    intro r hr
    rw [hQ] at hr
    exact not_horiz_of_mem_Q c hr
  have hiff : ∀ r, ¬ horiz c (cell r j) → r ∈ Q := by
    intro r hr
    rw [hQ]
    exact mem_Q_of_not_horiz c hr
  apply q_lemma
  refine ⟨fun r => if hr : r ∈ Q then rowPartner c j r else r, ?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [dif_pos hr]
    exact hiff _ (rowPartner_not_horiz c (hnot r hr))
  · intro r hr
    simp only [dif_pos hr]
    exact rowPartner_ne c (hnot r hr)
  · intro r hr
    simp only [dif_pos hr]
    have hr' : rowPartner c j r ∈ Q := hiff _ (rowPartner_not_horiz c (hnot r hr))
    simp only [dif_pos hr']
    exact rowPartner_invol c (hnot r hr)
  · intro r hr
    simp only [dif_pos hr]
    exact rowPartner_adj c (hnot r hr)

lemma step_column (c : PerfectCover 3 2) (j : Fin 4) :
    (∀ r, r ∈ Lp (profMid c) j → r ∉ Rp (profMid c) j) ∧
      (univ \ (Lp (profMid c) j ∪ Rp (profMid c) j)) ∈
        ({∅, ({0,1} : State), ({1,2} : State)} : Finset State) := by
  refine ⟨?_, columnQ c j⟩
  fin_cases j
  · intro r hr; simp [Lp] at hr
  · exact profMid_disj01 c
  · exact profMid_disj12 c
  · intro r _ hr; simp [Rp] at hr

abbrev step (a b : State) : Prop :=
  (∀ r, r ∈ a → r ∉ b) ∧
    (univ \ (a ∪ b)) ∈ ({∅, ({0,1} : State), ({1,2} : State)} : Finset State)

abbrev validMid (q : Fin 3 → State) : Prop :=
  step ∅ (q 0) ∧ step (q 0) (q 1) ∧ step (q 1) (q 2) ∧ step (q 2) ∅

def validMids : Finset (Fin 3 → State) := univ.filter validMid

lemma validMids_card : validMids.card = 11 := by decide

lemma profMid_valid (c : PerfectCover 3 2) : validMid (profMid c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := step_column c 0
    simpa [step, Lp, Rp] using this
  · have := step_column c 1
    simpa [step, Lp, Rp] using this
  · have := step_column c 2
    simpa [step, Lp, Rp] using this
  · have := step_column c 3
    simpa [step, Lp, Rp] using this


lemma domino_eq_of_carrier_eq {a b : Domino 3 2} (h : a.carrier = b.carrier) : a = b := by
  cases a; cases b; simp_all

lemma carrier_eq_pair {d : Domino 3 2} {a b : C} (ha : a ∈ d.carrier) (hb : b ∈ d.carrier)
    (hab : a ≠ b) : d.carrier = {a, b} := by
  have hsub : ({a,b} : Finset C) ⊆ d.carrier := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard : ({a,b} : Finset C).card = 2 := by simp [hab]
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact le_of_eq d.card)).symm

lemma partner_unique (Q : State) (hQ : Q ∈ ({∅, ({0,1} : State), ({1,2} : State)} : Finset State))
    {r a b : Fin 3} (hr : r ∈ Q) (ha : a ∈ Q) (hb : b ∈ Q) (har : a ≠ r) (hbr : b ≠ r)
    (hadja : a.val + 1 = r.val ∨ r.val + 1 = a.val)
    (hadjb : b.val + 1 = r.val ∨ r.val + 1 = b.val) : a = b := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hQ
  rcases hQ with rfl | rfl | rfl
  · exact absurd hr (by simp)
  · decide +revert
  · decide +revert

lemma perfectCover_eq_of_d_set {c1 c2 : PerfectCover 3 2} (h : c1.d_set = c2.d_set) : c1 = c2 := by
  cases c1; cases c2; simp_all

lemma domOf_eq_of_hEdge (c1 c2 : PerfectCover 3 2)
    {r m : Fin 3} (h1 : r ∈ profMid c1 m) (h2 : r ∈ profMid c2 m) {x : C}
    (hx : x ∈ ({cell r (Fin.castSucc m), cell r m.succ} : Finset C)) :
    domOf c1 x = domOf c2 x := by
  obtain ⟨d1, hd1, ha1, hb1⟩ := (mem_profMid c1 m r).mp h1
  obtain ⟨d2, hd2, ha2, hb2⟩ := (mem_profMid c2 m r).mp h2
  have hne : cell r (Fin.castSucc m) ≠ cell r m.succ := by
    intro h
    have h2 := congrArg Prod.snd h
    simp only [cell_snd] at h2
    have h3 : (Fin.castSucc m).val = (m.succ).val := congrArg Fin.val h2
    simp only [Fin.val_castSucc, Fin.val_succ] at h3
    omega
  have hcar1 : d1.carrier = ({cell r (Fin.castSucc m), cell r m.succ} : Finset C) :=
    carrier_eq_pair ha1 hb1 hne
  have hcar2 : d2.carrier = ({cell r (Fin.castSucc m), cell r m.succ} : Finset C) :=
    carrier_eq_pair ha2 hb2 hne
  have hd : d1 = d2 := domino_eq_of_carrier_eq (hcar1.trans hcar2.symm)
  have e1 : domOf c1 x = d1 := (domOf_unique c1 hd1 (by rw [hcar1]; exact hx)).symm
  have e2 : domOf c2 x = d2 := (domOf_unique c2 hd2 (by rw [hcar2]; exact hx)).symm
  rw [e1, e2, hd]

lemma domOf_eq_of_not_horiz (c1 c2 : PerfectCover 3 2) (hp : profMid c1 = profMid c2)
    {r : Fin 3} {j : Fin 4} (h1 : ¬ horiz c1 (cell r j)) :
    domOf c1 (cell r j) = domOf c2 (cell r j) := by
  have hL : Lp (profMid c1) j = Lp (profMid c2) j := congrFun (congrArg Lp hp) j
  have hR : Rp (profMid c1) j = Rp (profMid c2) j := congrFun (congrArg Rp hp) j
  have hprofb : (Lp (profMid c1) j ∪ Rp (profMid c1) j) = (Lp (profMid c2) j ∪ Rp (profMid c2) j) := by
    rw [hL, hR]
  have h2 : ¬ horiz c2 (cell r j) := by
    intro hh
    apply h1
    exact (horiz_iff_profLR c1 r j).mpr (by
      have hh' := (horiz_iff_profLR c2 r j).mp hh
      rwa [← hL, ← hR] at hh')
  set Q : State := univ \ (Lp (profMid c1) j ∪ Rp (profMid c1) j) with hQ
  have hQmem : Q ∈ ({∅, ({0,1} : State), ({1,2} : State)} : Finset State) := by
    rw [hQ]; exact columnQ c1 j
  have hr1 : r ∈ Q := by rw [hQ]; exact mem_Q_of_not_horiz c1 h1
  have ha1 : rowPartner c1 j r ∈ Q := by rw [hQ]; exact rowPartner_mem_Q c1 h1
  have ha2 : rowPartner c2 j r ∈ Q := by
    rw [hQ, hprofb]
    exact rowPartner_mem_Q c2 h2
  have hrow : rowPartner c1 j r = rowPartner c2 j r :=
    partner_unique Q hQmem hr1 ha1 ha2 (rowPartner_ne c1 h1) (rowPartner_ne c2 h2)
      (rowPartner_adj c1 h1) (rowPartner_adj c2 h2)
  have hpcell : partnerCell c1 (cell r j) = partnerCell c2 (cell r j) := by
    rw [← rowPartner_eq_partner c1 h1, ← rowPartner_eq_partner c2 h2, hrow]
  have hcarr1 : (domOf c1 (cell r j)).carrier = {cell r j, partnerCell c1 (cell r j)} :=
    carrier_eq_pair (domOf_covers c1 _) (partnerCell_mem c1 _) (Ne.symm (partnerCell_ne c1 _))
  have hcarr2 : (domOf c2 (cell r j)).carrier = {cell r j, partnerCell c2 (cell r j)} :=
    carrier_eq_pair (domOf_covers c2 _) (partnerCell_mem c2 _) (Ne.symm (partnerCell_ne c2 _))
  exact domino_eq_of_carrier_eq (by rw [hcarr1, hcarr2, hpcell])

lemma profMid_injective : Function.Injective profMid := by
  intro c1 c2 hp
  have key : ∀ x : C, domOf c1 x = domOf c2 x := by
    intro x
    obtain ⟨r, j⟩ := x
    fin_cases j
    · by_cases h : horiz c1 (cell r 0)
      · have h1 : r ∈ profMid c1 0 := (horiz_zero c1 r).mp h
        have h2 : r ∈ profMid c2 0 := by rw [← hp]; exact h1
        exact domOf_eq_of_hEdge c1 c2 h1 h2 (x := cell r 0) (by simp [cell])
      · exact domOf_eq_of_not_horiz c1 c2 hp h
    · by_cases h : horiz c1 (cell r 1)
      · rcases (horiz_one c1 r).mp h with hm | hm
        · have hm2 : r ∈ profMid c2 0 := by rw [← hp]; exact hm
          exact domOf_eq_of_hEdge c1 c2 hm hm2 (x := cell r 1) (by simp [cell])
        · have hm2 : r ∈ profMid c2 1 := by rw [← hp]; exact hm
          exact domOf_eq_of_hEdge c1 c2 hm hm2 (x := cell r 1) (by simp [cell])
      · exact domOf_eq_of_not_horiz c1 c2 hp h
    · by_cases h : horiz c1 (cell r 2)
      · rcases (horiz_two c1 r).mp h with hm | hm
        · have hm2 : r ∈ profMid c2 1 := by rw [← hp]; exact hm
          exact domOf_eq_of_hEdge c1 c2 hm hm2 (x := cell r 2) (by simp [cell])
        · have hm2 : r ∈ profMid c2 2 := by rw [← hp]; exact hm
          exact domOf_eq_of_hEdge c1 c2 hm hm2 (x := cell r 2) (by simp [cell])
      · exact domOf_eq_of_not_horiz c1 c2 hp h
    · by_cases h : horiz c1 (cell r 3)
      · have h1 : r ∈ profMid c1 2 := (horiz_three c1 r).mp h
        have h2 : r ∈ profMid c2 2 := by rw [← hp]; exact h1
        exact domOf_eq_of_hEdge c1 c2 h1 h2 (x := cell r 3) (by simp [cell])
      · exact domOf_eq_of_not_horiz c1 c2 hp h
  have hdset : c1.d_set = c2.d_set := by
    apply Finset.Subset.antisymm
    · intro d hd
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [d.card]; norm_num)
      rw [domOf_unique c1 hd hx, key x]
      exact domOf_mem c2 x
    · intro d hd
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [d.card]; norm_num)
      rw [domOf_unique c2 hd hx, ← key x]
      exact domOf_mem c1 x
  exact perfectCover_eq_of_d_set hdset

lemma adj_symm {i j : C} (h : Adj i j) : Adj j i := by
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · exact Or.inl ⟨h1.symm, Or.inr h2⟩
  · exact Or.inl ⟨h1.symm, Or.inl h2⟩
  · exact Or.inr ⟨h1.symm, Or.inr h2⟩
  · exact Or.inr ⟨h1.symm, Or.inl h2⟩

lemma adj_ne {i j : C} (h : Adj i j) : i ≠ j := by
  rintro rfl
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;> omega

def dom (i j : C) (h : Adj i j) : Domino 3 2 where
  carrier := {i, j}
  card := by
    rw [Finset.card_insert_of_notMem (by simpa using (adj_ne h)), Finset.card_singleton]
  position := by
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact h
    · exact adj_symm h
    · exact absurd rfl hxy

def domH (r : Fin 3) (m : Fin 3) : Domino 3 2 :=
  dom (cell r (Fin.castSucc m)) (cell r m.succ) (by decide +revert)

def domV (r : Fin 2) (j : Fin 4) : Domino 3 2 :=
  dom (cell (Fin.castSucc r) j) (cell r.succ j) (by decide +revert)

def cover1 : PerfectCover 3 2 where
  d_set := {domH 2 0, domV 0 0, domV 0 1, domV 0 2, domV 0 3, domH 2 2}
  d_card := by decide
  covers := by decide

def cover2 : PerfectCover 3 2 where
  d_set := {domH 2 0, domV 0 0, domV 0 1, domH 0 2, domV 1 2, domV 1 3}
  d_card := by decide
  covers := by decide

def cover3 : PerfectCover 3 2 where
  d_set := {domH 2 0, domH 0 2, domH 1 2, domH 2 2, domV 0 0, domV 0 1}
  d_card := by decide
  covers := by decide

def cover4 : PerfectCover 3 2 where
  d_set := {domH 2 0, domH 0 1, domH 1 1, domH 2 2, domV 0 0, domV 0 3}
  d_card := by decide
  covers := by decide

def cover5 : PerfectCover 3 2 where
  d_set := {domH 0 0, domH 2 2, domV 1 0, domV 1 1, domV 0 2, domV 0 3}
  d_card := by decide
  covers := by decide

def cover6 : PerfectCover 3 2 where
  d_set := {domH 0 0, domH 0 2, domV 1 0, domV 1 1, domV 1 2, domV 1 3}
  d_card := by decide
  covers := by decide

def cover7 : PerfectCover 3 2 where
  d_set := {domH 0 0, domH 0 2, domH 1 2, domH 2 2, domV 1 0, domV 1 1}
  d_card := by decide
  covers := by decide

def cover8 : PerfectCover 3 2 where
  d_set := {domH 0 0, domH 1 1, domH 2 1, domH 0 2, domV 1 0, domV 1 3}
  d_card := by decide
  covers := by decide

def cover9 : PerfectCover 3 2 where
  d_set := {domH 0 0, domH 1 0, domH 2 0, domH 2 2, domV 0 2, domV 0 3}
  d_card := by decide
  covers := by decide

def cover10 : PerfectCover 3 2 where
  d_set := {domH 0 0, domH 1 0, domH 2 0, domH 0 2, domV 1 2, domV 1 3}
  d_card := by decide
  covers := by decide

def cover11 : PerfectCover 3 2 where
  d_set := {domH 0 0, domH 1 0, domH 2 0, domH 0 2, domH 1 2, domH 2 2}
  d_card := by decide
  covers := by decide

def g : Fin 11 → PerfectCover 3 2
  | ⟨0, _⟩ => cover1
  | ⟨1, _⟩ => cover2
  | ⟨2, _⟩ => cover3
  | ⟨3, _⟩ => cover4
  | ⟨4, _⟩ => cover5
  | ⟨5, _⟩ => cover6
  | ⟨6, _⟩ => cover7
  | ⟨7, _⟩ => cover8
  | ⟨8, _⟩ => cover9
  | ⟨9, _⟩ => cover10
  | ⟨10, _⟩ => cover11

lemma g_injective : Function.Injective g := by decide


lemma card_le_eleven : Fintype.card (PerfectCover 3 2) ≤ 11 := by
  have hcard : Fintype.card (PerfectCover 3 2) =
      ((Finset.univ : Finset (PerfectCover 3 2)).image profMid).card := by
    rw [Finset.card_image_of_injective _ profMid_injective]
    rfl
  calc Fintype.card (PerfectCover 3 2)
      = ((Finset.univ : Finset (PerfectCover 3 2)).image profMid).card := hcard
    _ ≤ validMids.card := Finset.card_le_card (by
        intro q hq
        obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hq
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, profMid_valid c⟩)
    _ = 11 := validMids_card

lemma eleven_le_card : 11 ≤ Fintype.card (PerfectCover 3 2) := by
  have h := Fintype.card_le_of_injective g g_injective
  simpa using h

end BrualdiCh1_5

/--
Find the number of different perfect covers of a 3-by-4 chessboard by dominoes.
-/
theorem brualdi_ch1_5 : Fintype.card (PerfectCover 3 2) = ((11) : ℕ ) := by
  have h1 := BrualdiCh1_5.card_le_eleven
  have h2 := BrualdiCh1_5.eleven_le_card
  omega
