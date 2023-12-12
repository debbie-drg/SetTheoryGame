ext x
apply Iff.intro
· intro h1
  rw [comp_def, fam_inter_def] at h1
  rw [fam_union_def]
  by_contra h2
  apply h1
  intro S h3
  by_contra h4
  apply h2
  apply Exists.intro Sᶜ
  apply And.intro _ h4
  rw [set_builder_def, comp_comp]
  exact h3
· intro h1
  rw [fam_union_def] at h1
  obtain ⟨S, h2⟩ := h1
  rw [set_builder_def] at h2
  rw [comp_def, fam_inter_def]
  by_contra h3
  have h4 : x ∈ Sᶜ := h3 Sᶜ h2.left
  exact h4 h2.right
