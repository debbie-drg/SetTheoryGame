ext x
apply Iff.intro
· intro h
  rw [comp_def, union_def] at h
  rw [inter_def]
  apply And.intro
  · by_contra h'
    apply h
    apply Or.inl
    rw [comp_def] at h'
    by_contra h''
    exact h' h''
  · by_contra h'
    apply h
    apply Or.inr
    rw [comp_def] at h'
    by_contra h''
    exact h' h''
· intro h
  rw [comp_def, union_def]
  rw [inter_def] at h
  by_contra h'
  cases' h' with hA hB
  · apply h.left
    exact hA
  · apply h.right
    exact hB
