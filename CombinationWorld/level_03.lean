ext
apply Iff.intro
· intro h
  have hA : x ∈ A := h.left
  have hBC : x ∈ B ∪ C := h.right
  cases' hBC with hB hC
  · apply Or.inl (And.intro hA hB)
  · apply Or.inr (And.intro hA hC)
· intro h
  cases' h with hAB hAC
  · exact And.intro hAB.left (Or.inl hAB.right)
  · exact And.intro hAC.left (Or.inr hAC.right)
