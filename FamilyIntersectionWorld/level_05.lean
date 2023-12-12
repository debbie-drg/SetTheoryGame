apply Iff.intro
· intro h1
  intro B h2
  intro x h3
  exact (h1 h3) B h2
· intro h1
  intro x h2
  rw [fam_inter_def]
  intro S h3
  exact (h1 S h3) h2
