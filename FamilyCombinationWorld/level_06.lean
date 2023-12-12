intro x h1
rw [fam_union_def]
have h2 := h1.left
rw [fam_union_def] at h2
obtain ⟨A, h2⟩ := h2
have h3 := h1.right
rw [comp_def, fam_inter_def] at h3
have h4 : ∃ B ∈ G, x ∈ Bᶜ := by
  by_contra h4
  apply h3
  intro B h5
  by_contra h6
  apply h4
  apply Exists.intro B
  exact And.intro h5 h6
obtain ⟨B, h4⟩ := h4
apply Exists.intro (A ∩ Bᶜ)
apply And.intro
· rw [set_builder_def]
  apply Exists.intro A
  apply And.intro h2.left
  apply Exists.intro B
  apply And.intro h4.left
  rfl
· exact And.intro h2.right h4.right
