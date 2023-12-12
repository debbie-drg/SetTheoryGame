intro x h2
rw [fam_inter_def] at h2
by_cases h3 : x ∈ A
· exact Or.inl h3
· apply Or.inr
  intro S h
  have h4 : x ∈ A ∪ S := h2 (A ∪ S) (h1 S h)
  cases' h4 with hA hS
  · by_contra
    apply h3
    exact hA
  · exact hS
