intro x h2
rw [fam_inter_def] at h2
rw [fam_inter_def]
intro S h3
have h4 : S ∈ G := h1 h3
exact h2 S h4
