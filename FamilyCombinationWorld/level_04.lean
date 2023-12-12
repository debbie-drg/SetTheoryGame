intro x h1
rw [fam_union_def]
have h2 := h1.left
rw [fam_union_def] at h2
obtain ⟨S, h2⟩ := h2
have h3 := h1.right
rw [comp_def, fam_union_def] at h3
have h4 : S ∈ Gᶜ := by
  rw [comp_def]
  by_contra h4
  apply h3
  apply Exists.intro S
  exact And.intro h4 h2.right
apply Exists.intro S
apply And.intro
· exact And.intro h2.left h4
· exact h2.right
