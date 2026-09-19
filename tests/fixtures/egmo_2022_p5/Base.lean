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

/-- The adjacency matrix of the path on `m` vertices, over `ZMod 2`. -/
def pathAdj (m : ℕ) : Matrix (Fin m) (Fin m) (ZMod 2) :=
  Matrix.of fun i j => if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0

/-- The adjacency matrix of the `n × m` grid graph, over `ZMod 2`: two cells are
adjacent when they lie in the same row and are horizontally consecutive, or in the
same column and are vertically consecutive. -/
def gridAdj (n m : ℕ) : Matrix (Fin n × Fin m) (Fin n × Fin m) (ZMod 2) :=
  Matrix.of fun p q =>
    if (p.1.val = q.1.val ∧ (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val)) ∨
        (p.2.val = q.2.val ∧ (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val)) then 1 else 0

/-- The Fibonacci polynomials over `ZMod 2`, defined by `fibP 0 = 0`, `fibP 1 = 1` and
`fibP (n + 2) = X * fibP (n + 1) + fibP n`.  Over `ZMod 2`, `fibP (m + 1)` is the
characteristic polynomial of `pathAdj m`. -/
noncomputable def fibP : ℕ → Polynomial (ZMod 2)
  | 0 => 0
  | 1 => 1
  | n + 2 => Polynomial.X * fibP (n + 1) + fibP n

/-- The `ZMod 2`-valued checkerboard colour of a cell of an `n × m` board: `0` on one
colour class and `1` on the other. -/
def cellColour {n m : ℕ} (p : Fin n × Fin m) : ZMod 2 := (p.1.val + p.2.val : ZMod 2)

/-- The black cells of the `n × 2k` board, i.e. the cells of checkerboard colour `0`. -/
abbrev blackCell (n k : ℕ) : Type := {p : Fin n × Fin (2 * k) // cellColour p = 0}

/-- The white cells of the `n × 2k` board, i.e. the cells of checkerboard colour `1`. -/
abbrev whiteCell (n k : ℕ) : Type := {p : Fin n × Fin (2 * k) // cellColour p = 1}

/-- The biadjacency matrix of the `n × 2k` grid, computed with respect to a bijection `e`
between the two checkerboard classes: entry `(p, q)` is the adjacency of the black cell
`p` with the white cell `e q`. -/
def gridBiadj (n k : ℕ) (e : blackCell n k ≃ whiteCell n k) :
    Matrix (blackCell n k) (blackCell n k) (ZMod 2) :=
  fun p q => gridAdj n (2 * k) p.1 (e q).1

/-- The number of perfect matchings of the `n × 2k` grid, i.e. of bijections from the
black cells to the white cells that only pair adjacent cells. -/
noncomputable def gridMatchingCount (n k : ℕ) : ℕ := by
  classical
  exact Fintype.card {f : blackCell n k → whiteCell n k //
    Function.Bijective f ∧ ∀ p, gridAdj n (2 * k) p.1 (f p).1 = 1}

/-- Every perfect cover of the `n × 2k` board determines, and is determined by, a perfect
matching of the grid graph: each domino pairs one black cell with an adjacent white
cell. -/
theorem card_perfectCover_eq_gridMatchingCount (n k : ℕ) :
    Fintype.card (PerfectCover n k) = gridMatchingCount n k := by
  sorry

/-- The checkerboard colouring splits the `n × 2k` board into two classes of equal size. -/
theorem card_blackCell_eq_card_whiteCell (n k : ℕ) :
    Fintype.card (blackCell n k) = Fintype.card (whiteCell n k) := by
  sorry

/-- Over `ZMod 2` the determinant of the grid adjacency matrix equals the determinant of
the biadjacency matrix of the grid, computed with respect to any bijection between the
two checkerboard classes. -/
theorem det_gridAdj_eq_det_gridBiadj (n k : ℕ) (e : blackCell n k ≃ whiteCell n k) :
    (gridAdj n (2 * k)).det = (gridBiadj n k e).det := by
  sorry

/-- Over `ZMod 2` the determinant of the biadjacency matrix of the grid counts the
perfect matchings: the signs disappear from the determinant expansion and the surviving
terms are exactly the edge-supported bijections between the two colour classes. -/
theorem det_gridBiadj_eq_gridMatchingCount (n k : ℕ) (e : blackCell n k ≃ whiteCell n k) :
    (gridBiadj n k e).det = (gridMatchingCount n k : ZMod 2) := by
  sorry

/-- Parity of the number of perfect covers of an `n × 2k` board, expressed as the
non-vanishing of the determinant of the grid adjacency matrix over `ZMod 2`.

This is the combinatorial bridge: over `ZMod 2` the determinant expansion counts
cycle covers, and the cycle covers occurring an odd number of times are exactly the
perfect matchings, which are exactly the perfect covers of the board. -/
theorem odd_card_perfectCover_iff_gridAdj_det_ne_zero (n k : ℕ) :
    Odd (Fintype.card (PerfectCover n k)) ↔ (gridAdj n (2 * k)).det ≠ 0 := by
  let e : blackCell n k ≃ whiteCell n k :=
    Fintype.equivOfCardEq (card_blackCell_eq_card_whiteCell n k)
  rw [card_perfectCover_eq_gridMatchingCount n k, det_gridAdj_eq_det_gridBiadj n k e,
    det_gridBiadj_eq_gridMatchingCount n k e, ZMod.natCast_ne_zero_iff_odd]

/-- The `n × m` grid adjacency matrix is the Kronecker sum of the two path adjacency
matrices, `gridAdj n m = pathAdj n ⊗ 1 + 1 ⊗ pathAdj m`. -/
lemma gridAdj_eq_kroneckerSum (n m : ℕ) :
    gridAdj n m = Matrix.kronecker (pathAdj n) (1 : Matrix (Fin m) (Fin m) (ZMod 2))
      + Matrix.kronecker (1 : Matrix (Fin n) (Fin n) (ZMod 2)) (pathAdj m) := by
  ext p q
  simp only [gridAdj, pathAdj, Matrix.add_apply, Matrix.kronecker, Matrix.kroneckerMap_apply,
    Matrix.of_apply, Matrix.one_apply]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;>
    by_cases a1 : (p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val) <;>
    by_cases a2 : (p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val) <;>
    simp_all [Fin.ext_iff]

/-- Over `ZMod 2`, `fibP (m + 1)` is the characteristic polynomial of the path
adjacency matrix `pathAdj m`. -/
theorem charpoly_pathAdj (m : ℕ) : (pathAdj m).charpoly = fibP (m + 1) := by
  sorry

/-- Over `ZMod 2`, the determinant of the Kronecker sum `A ⊗ 1 + 1 ⊗ B` equals the
resultant of the characteristic polynomials of `A` and `B`. -/
theorem kroneckerSum_det_eq_resultant (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) (ZMod 2)) (B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    (Matrix.kronecker A (1 : Matrix (Fin m) (Fin m) (ZMod 2))
        + Matrix.kronecker (1 : Matrix (Fin n) (Fin n) (ZMod 2)) B).det
      = A.charpoly.resultant B.charpoly := by
  sorry

/-- The transfer-matrix / Kronecker bridge: over `ZMod 2` the grid adjacency matrix
`gridAdj n m = pathAdj n ⊗ 1 + 1 ⊗ pathAdj m` is invertible exactly when the
characteristic polynomials `fibP (n + 1)` and `fibP (m + 1)` are coprime. -/
theorem gridAdj_det_ne_zero_iff_isCoprime_fibP (n m : ℕ) :
    (gridAdj n m).det ≠ 0 ↔ IsCoprime (fibP (n + 1)) (fibP (m + 1)) := by
  rw [gridAdj_eq_kroneckerSum, kroneckerSum_det_eq_resultant]
  rw [← isUnit_iff_ne_zero,
    Polynomial.isUnit_resultant_iff_isCoprime (Matrix.charpoly_monic (pathAdj n)),
    charpoly_pathAdj n, charpoly_pathAdj m]

/-- The number-theoretic bridge: the Fibonacci polynomials `fibP a` and `fibP b` over
`ZMod 2`, with `a, b > 0`, are coprime exactly when `a` and `b` are coprime. -/
theorem isCoprime_fibP_iff_coprime (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    IsCoprime (fibP a) (fibP b) ↔ Nat.Coprime a b := by
  sorry


/-- Parity criterion for the number of domino tilings of an `n × 2k` board:
it is odd exactly when `n + 1` is coprime with `2 * k + 1`. -/
theorem odd_perfectCover_card_iff_coprime (n k : ℕ) (hk : 0 < k) :
    Odd (Fintype.card (PerfectCover n k)) ↔ Nat.Coprime (n + 1) (2 * k + 1) := by
  have h₁ := odd_card_perfectCover_iff_gridAdj_det_ne_zero n k
  have h₂ := gridAdj_det_ne_zero_iff_isCoprime_fibP n (2 * k)
  have h₃ := isCoprime_fibP_iff_coprime (n + 1) (2 * k + 1) (by omega) (by omega)
  exact h₁.trans (h₂.trans h₃)

/-- `n + 1` is coprime with every odd number `2 * k + 1` (`k ≥ 1`) exactly when `n + 1`
is a power of two. -/
theorem coprime_all_iff_eq_two_pow (n : ℕ) (hn : 0 < n) :
    (∀ k, 0 < k → Nat.Coprime (n + 1) (2 * k + 1)) ↔ ∃ m, 0 < m ∧ n + 1 = 2 ^ m := by
  constructor
  · intro h
    obtain ⟨a, m, hm_odd, hN⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.succ_ne_zero n)
    have hm_eq_one : m = 1 := by
      by_contra hm1
      obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hm_odd) (even_iff_two_dvd.mpr hpm)
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hpodd : Odd p := hp.odd_of_ne_two hp2
      obtain ⟨j, hj⟩ := hpodd
      have hjpos : 0 < j := by omega
      have hcop := h j hjpos
      have hpdvdN : p ∣ n + 1 := by
        rw [show n + 1 = 2 ^ a * m from hN]
        exact dvd_mul_of_dvd_right hpm _
      have hpdvd2j : p ∣ 2 * j + 1 := ⟨1, by rw [mul_one]; exact hj.symm⟩
      exact absurd hcop (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpdvdN hpdvd2j)
    have hN2 : n + 1 = 2 ^ a := by rw [hm_eq_one, mul_one] at hN; exact hN
    have ha : 0 < a := by
      by_contra hcon
      have : a = 0 := by omega
      rw [this, pow_zero] at hN2
      omega
    exact ⟨a, ha, hN2⟩
  · rintro ⟨m, hm, hN⟩ k hk
    rw [hN]
    exact (Nat.coprime_pow_left_iff hm 2 (2 * k + 1)).mpr (Nat.coprime_two_left.mpr ⟨k, rfl⟩)

/--
For all positive integers $n, k$, let $f(n, 2k)$ be the number of ways an $n \times 2k$ board can be fully covered by $nk$ dominoes of size $2 \times 1$. (For example, $f(2,2)=2$ and $f(3,2)=3$.)\nFind all positive integers $n$ such that for every positive integer $k$, the number $f(n, 2k)$ is odd.
-/
theorem egmo_2022_p5 : {n | n > 0 ∧ ∀ k > 0, Odd (Fintype.card (PerfectCover n k))} =
    (({x | ∃ m > 0, 2 ^ m - 1 = x}) : Set ℕ ) := by
  ext n
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hn, hodd⟩
    obtain ⟨m, hm, hmN⟩ := (coprime_all_iff_eq_two_pow n hn).mp
      (fun k hk => (odd_perfectCover_card_iff_coprime n k hk).mp (hodd k hk))
    exact ⟨m, hm, by omega⟩
  · rintro ⟨m, hm, hmN⟩
    have hpow : n + 1 = 2 ^ m := by
      have : 0 < 2 ^ m := pow_pos (by norm_num) m
      omega
    have hnpos : 0 < n := by
      have h2 : 2 ≤ 2 ^ m := by
        have := Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) hm
        simpa using this
      omega
    refine ⟨hnpos, fun k hk => (odd_perfectCover_card_iff_coprime n k hk).mpr ?_⟩
    exact (coprime_all_iff_eq_two_pow n hnpos).mpr ⟨m, hm, hpow⟩ k hk
