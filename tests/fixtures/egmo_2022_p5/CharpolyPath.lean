import Mathlib


/-- The adjacency matrix of the path on `m` vertices, over `ZMod 2`. -/
def pathAdj (m : ℕ) : Matrix (Fin m) (Fin m) (ZMod 2) :=
  Matrix.of fun i j => if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0


/-- The Fibonacci polynomials over `ZMod 2`, defined by `fibP 0 = 0`, `fibP 1 = 1` and
`fibP (n + 2) = X * fibP (n + 1) + fibP n`.  Over `ZMod 2`, `fibP (m + 1)` is the
characteristic polynomial of `pathAdj m`. -/
noncomputable def fibP : ℕ → Polynomial (ZMod 2)
  | 0 => 0
  | 1 => 1
  | n + 2 => Polynomial.X * fibP (n + 1) + fibP n


namespace PathChar

open Matrix Polynomial

lemma pathAdj_self (m : ℕ) (i : Fin m) : pathAdj m i i = 0 := by
  simp only [pathAdj, Matrix.of_apply]
  rw [if_neg (by omega)]

lemma pathAdj_adj_one {m : ℕ} {i j : Fin m}
    (h : i.val + 1 = j.val ∨ j.val + 1 = i.val) : pathAdj m i j = 1 := by
  simp only [pathAdj, Matrix.of_apply]
  rw [if_pos h]

lemma charmatrix_pathAdj_apply (m : ℕ) (i j : Fin m) :
    (Matrix.charmatrix (pathAdj m)) i j =
      if i = j then Polynomial.X
      else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0 := by
  by_cases h : i = j
  · subst h
    rw [Matrix.charmatrix_apply_eq, pathAdj_self, map_zero, sub_zero]
    simp
  · rw [Matrix.charmatrix_apply_ne _ _ _ h, if_neg h]
    by_cases h2 : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · rw [if_pos h2, pathAdj, Matrix.of_apply, if_pos h2]
      rw [CharTwo.neg_eq, map_one]
    · rw [if_neg h2, pathAdj, Matrix.of_apply, if_neg h2, map_zero, neg_zero]

lemma charmatrix_pathAdj_diag (m : ℕ) (i : Fin m) :
    (Matrix.charmatrix (pathAdj m)) i i = Polynomial.X := by
  rw [Matrix.charmatrix_apply_eq, pathAdj_self, map_zero, sub_zero]

lemma charmatrix_pathAdj_adj {m : ℕ} {i j : Fin m} (hij : i ≠ j)
    (h : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    (Matrix.charmatrix (pathAdj m)) i j = 1 := by
  rw [Matrix.charmatrix_apply_ne _ _ _ hij, pathAdj_adj_one h, CharTwo.neg_eq, map_one]

lemma charmatrix_submatrix_self {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] {R : Type*} [CommRing R] (M : Matrix n n R) (f : m → n)
    (hf : Function.Injective f) :
    (Matrix.charmatrix M).submatrix f f = Matrix.charmatrix (M.submatrix f f) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.charmatrix, Matrix.scalar_apply, Matrix.sub_apply,
    RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply, hf.eq_iff]

lemma pathAdj_submatrix_succ (k : ℕ) :
    (pathAdj (k + 1)).submatrix (Fin.succ) (Fin.succ) = pathAdj k := by
  ext i j
  simp only [Matrix.submatrix_apply, pathAdj, Matrix.of_apply, Fin.val_succ]
  by_cases h : i.val + 1 = j.val ∨ j.val + 1 = i.val
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

lemma pathAdj_submatrix_succ_succ (k : ℕ) :
    (pathAdj (k + 2)).submatrix (Fin.succ ∘ Fin.succ) (Fin.succ ∘ Fin.succ) = pathAdj k := by
  rw [← Matrix.submatrix_submatrix]
  rw [pathAdj_submatrix_succ (k + 1), pathAdj_submatrix_succ k]

lemma det_row0_two {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) R)
    (h : ∀ j : Fin (n + 2), 2 ≤ j.val → A 0 j = 0) :
    A.det = A 0 0 * (A.submatrix (Fin.succ) (Fin.succ)).det
      - A 0 1 * (A.submatrix (Fin.succ) (Fin.succAbove (1 : Fin (n + 2)))).det := by
  rw [Matrix.det_succ_row_zero]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have htail : (∑ i : Fin n, (-1 : R) ^ ((i.succ.succ : Fin (n+2)) : ℕ) * A 0 (i.succ.succ)
        * (A.submatrix Fin.succ (i.succ.succ).succAbove).det) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [h (i.succ.succ) (by simp only [Fin.val_succ]; omega), mul_zero, zero_mul]
  rw [htail, add_zero]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero, Fin.succ_zero_eq_one,
    Fin.val_one, pow_one]
  ring

lemma det_col0_one {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : ∀ i : Fin (n + 1), i ≠ 0 → A i 0 = 0) :
    A.det = A 0 0 * (A.submatrix (Fin.succ) (Fin.succ)).det := by
  rw [Matrix.det_succ_column_zero]
  rw [Fin.sum_univ_succ]
  have htail : (∑ i : Fin n, (-1 : R) ^ ((i.succ : Fin (n+1)) : ℕ) * A i.succ 0 *
      (A.submatrix (i.succ).succAbove Fin.succ).det) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [h i.succ (by simp [Fin.ext_iff]), mul_zero, zero_mul]
  rw [htail, add_zero]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]

lemma succAbove_one_succ (k : ℕ) (j : Fin k) :
    Fin.succAbove (1 : Fin (k + 2)) (Fin.succ j) = (Fin.succ j).succ := by
  rw [Fin.succAbove_of_le_castSucc]
  simp [Fin.le_def]

lemma succAbove_one_comp_succ (k : ℕ) :
    (Fin.succAbove (1 : Fin (k + 2))) ∘ (Fin.succ : Fin k → Fin (k+1))
      = (Fin.succ : Fin (k+1) → Fin (k+2)) ∘ (Fin.succ : Fin k → Fin (k+1)) := by
  funext i
  exact succAbove_one_succ k i

lemma charpoly_pathAdj_add_two (k : ℕ) :
    (pathAdj (k + 2)).charpoly
      = Polynomial.X * (pathAdj (k + 1)).charpoly + (pathAdj k).charpoly := by
  rw [Matrix.charpoly, Matrix.charpoly, Matrix.charpoly]
  rw [det_row0_two (Matrix.charmatrix (pathAdj (k + 2))) (by
    intro j hj
    rw [charmatrix_pathAdj_apply,
      if_neg (by simp only [Fin.ext_iff, Fin.val_zero]; omega),
      if_neg (by simp only [Fin.val_zero]; omega)])]
  rw [charmatrix_pathAdj_diag]
  rw [charmatrix_pathAdj_adj (by
      simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_one]; omega)
    (Or.inl (by simp only [Fin.val_zero, Fin.val_one]))]
  rw [charmatrix_submatrix_self (pathAdj (k + 2)) Fin.succ (Fin.succ_injective _),
    pathAdj_submatrix_succ]
  have hN : ((Matrix.charmatrix (pathAdj (k + 2))).submatrix Fin.succ
        (Fin.succAbove (1 : Fin (k + 2)))).det = (Matrix.charmatrix (pathAdj k)).det := by
    rw [det_col0_one _ (by
      intro i hi
      rw [Matrix.submatrix_apply, Fin.succAbove_ne_zero_zero (by
        simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_one]; omega)]
      rw [charmatrix_pathAdj_apply,
        if_neg (by simp only [Fin.ext_iff, Fin.val_succ, Fin.val_zero]; omega),
        if_neg (by
          have hi' : i.val ≠ 0 := fun h0 => hi (Fin.ext h0)
          simp only [Fin.val_succ, Fin.val_zero]
          omega)])]
    rw [Matrix.submatrix_apply, Fin.succAbove_ne_zero_zero (by
      simp only [ne_eq, Fin.ext_iff, Fin.val_zero, Fin.val_one]; omega)]
    rw [charmatrix_pathAdj_adj (by
        simp only [ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_zero]; omega)
      (Or.inr (by simp))]
    rw [one_mul]
    congr 1
    rw [Matrix.submatrix_submatrix, succAbove_one_comp_succ]
    rw [charmatrix_submatrix_self (pathAdj (k + 2)) (Fin.succ ∘ Fin.succ)
      (fun a b h => Fin.succ_injective _ (Fin.succ_injective _ h))]
    rw [pathAdj_submatrix_succ_succ]
  rw [hN]
  rw [sub_eq_add_neg, CharTwo.neg_eq, one_mul]

end PathChar

/-- Over `ZMod 2`, `fibP (m + 1)` is the characteristic polynomial of the path
adjacency matrix `pathAdj m`. -/
theorem charpoly_pathAdj (m : ℕ) : (pathAdj m).charpoly = fibP (m + 1) := by
  induction m using Nat.twoStepInduction with
  | zero => simp [pathAdj, fibP]
  | one => simp [pathAdj, fibP, Matrix.charpoly, Matrix.charmatrix]
  | more k ih0 ih1 =>
      rw [PathChar.charpoly_pathAdj_add_two k, ih0, ih1]
      rfl
