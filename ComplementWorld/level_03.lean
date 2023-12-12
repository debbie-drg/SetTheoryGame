intro x h2
rw [comp_def x A]
rw [comp_def x B] at h2
by_contra h3
exact h2 (h1 h3)
