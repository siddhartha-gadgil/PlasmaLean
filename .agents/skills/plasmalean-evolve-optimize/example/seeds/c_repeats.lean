def candidate : List ℕ := [10, 10, 10, 10, 10]
theorem bounded : ∀ x ∈ candidate, x ≤ 10 := by simp [candidate]
theorem short : candidate.length ≤ 5 := by simp [candidate]
theorem distinct : candidate.Nodup := by simp [candidate]
