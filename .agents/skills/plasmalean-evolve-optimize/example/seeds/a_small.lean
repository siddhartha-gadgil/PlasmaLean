-- evolve: idea = small seed
def candidate : List ℕ := [1, 2, 3]
theorem bounded : ∀ x ∈ candidate, x ≤ 10 := by simp [candidate]
theorem short : candidate.length ≤ 5 := by simp [candidate]
theorem distinct : candidate.Nodup := by simp [candidate]
