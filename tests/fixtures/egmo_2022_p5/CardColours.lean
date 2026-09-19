import Mathlib


/-- The `ZMod 2`-valued checkerboard colour of a cell of an `n × m` board: `0` on one
colour class and `1` on the other. -/
def cellColour {n m : ℕ} (p : Fin n × Fin m) : ZMod 2 := (p.1.val + p.2.val : ZMod 2)

/-- The black cells of the `n × 2k` board, i.e. the cells of checkerboard colour `0`. -/
abbrev blackCell (n k : ℕ) : Type := {p : Fin n × Fin (2 * k) // cellColour p = 0}

/-- The white cells of the `n × 2k` board, i.e. the cells of checkerboard colour `1`. -/
abbrev whiteCell (n k : ℕ) : Type := {p : Fin n × Fin (2 * k) // cellColour p = 1}


/-- The checkerboard colouring splits the `n × 2k` board into two classes of equal size. -/
theorem card_blackCell_eq_card_whiteCell (n k : ℕ) :
    Fintype.card (blackCell n k) = Fintype.card (whiteCell n k) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hb : Fintype.card (blackCell n 0) = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun p => Fin.elim0 p.1.2⟩
    have hw : Fintype.card (whiteCell n 0) = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun p => Fin.elim0 p.1.2⟩
    rw [hb, hw]
  · haveI : NeZero (2 * k) := ⟨by omega⟩
    -- The bijection on column indices: add `1` in `ZMod (2 * k)`.
    let φ : Fin (2 * k) ≃ ZMod (2 * k) :=
      { toFun := fun j => (j : ZMod (2 * k))
        invFun := fun a => ⟨a.val, a.val_lt⟩
        left_inv := fun j => by ext; exact ZMod.val_cast_of_lt j.isLt
        right_inv := fun a => ZMod.natCast_zmod_val a }
    let e : Fin (2 * k) ≃ Fin (2 * k) :=
      φ.trans ((Equiv.addRight (1 : ZMod (2 * k))).trans φ.symm)
    have hcoe : ∀ j : Fin (2 * k), ((e j : ZMod (2 * k))) = (j : ZMod (2 * k)) + 1 := by
      intro j
      show φ (e j) = φ j + 1
      simp [e, Equiv.trans_apply]
    have hkey : ∀ j : Fin (2 * k), ((e j).val : ZMod 2) = (j.val : ZMod 2) + 1 := by
      intro j
      have hval : ZMod.val (e j : ZMod (2 * k)) = (e j).val :=
        ZMod.val_cast_of_lt (e j).isLt
      calc ((e j).val : ZMod 2)
          = (ZMod.val (e j : ZMod (2 * k)) : ZMod 2) := by rw [hval]
        _ = ZMod.cast (e j : ZMod (2 * k)) := ZMod.natCast_val _
        _ = ZMod.cast ((j : ZMod (2 * k)) + 1) := by rw [hcoe j]
        _ = ZMod.cast (j : ZMod (2 * k)) + ZMod.cast (1 : ZMod (2 * k)) :=
              ZMod.cast_add (by omega : 2 ∣ 2 * k) _ _
        _ = ZMod.cast (j : ZMod (2 * k)) + 1 := by
              rw [ZMod.cast_one (R := ZMod 2) (n := 2 * k) (by omega : 2 ∣ 2 * k)]
        _ = (j.val : ZMod 2) + 1 := by
              rw [ZMod.cast_natCast (R := ZMod 2) (h := ⟨k, by ring⟩)]
    refine Fintype.card_congr (Equiv.subtypeEquiv
      (Equiv.prodCongr (Equiv.refl (Fin n)) e) ?_)
    intro p
    have h1 : (Equiv.prodCongr (Equiv.refl (Fin n)) e p).1 = p.1 := rfl
    have h2 : (Equiv.prodCongr (Equiv.refl (Fin n)) e p).2 = e p.2 := rfl
    have hcell : cellColour (Equiv.prodCongr (Equiv.refl (Fin n)) e p)
        = cellColour p + 1 := by
      simp only [cellColour, h1, h2, hkey p.2]
      ring
    rw [hcell]
    constructor
    · intro h; rw [h, zero_add]
    · intro h
      exact add_right_cancel (by simpa using h : cellColour p + 1 = 0 + 1)


