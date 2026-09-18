namespace Demo

def twice (n : Nat) := n + n

/-- This declaration keeps its name and attributes after merging. -/
@[simp] theorem target (n : Nat) : twice n = 2 * n := by
  sorry

theorem downstream (n : Nat) : twice n = 2 * n := target n

end Demo
