apply Iff.intro
· intro h
  apply comp_sub_of_sub
  exact h
· intro h
  apply comp_sub_of_sub at h
  rw [comp_comp, comp_comp] at h
  exact h
