namespace Demo
def twice (n : Nat) := n + n
end Demo

private theorem auxiliary (k : Nat) : k + k = 2 * k := by
  exact (Nat.two_mul k).symm

theorem solution (k : Nat) : Demo.twice k = 2 * k := auxiliary k
