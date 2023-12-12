intro x h2
rw [fam_union_def] at h2
rw [fam_union_def]
obtain ⟨S, h3⟩ := h2
apply Exists.intro S
exact And.intro (h1 h3.left) h3.right
