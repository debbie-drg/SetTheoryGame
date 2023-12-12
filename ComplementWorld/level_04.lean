apply sub_antisymm
· intro x h
  rw [comp_def] at h
  by_contra h1
  apply h
  exact h1
· intro x h
  rw [comp_def]
  by_contra h1
  exact h1 h
