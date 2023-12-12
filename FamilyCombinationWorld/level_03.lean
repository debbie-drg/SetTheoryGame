intro x h2
have h3 := h2.left
rw [fam_union_def] at h3
obtain ⟨S, h4⟩ := h3
obtain ⟨S', h5⟩ := h1 S h4.left
rw [fam_union_def]
apply Exists.intro (S ∩ S')
apply And.intro h5.right
apply And.intro h4.right
have h3 := h2.right
rw [fam_inter_def] at h3
exact h3 S' h5.left
