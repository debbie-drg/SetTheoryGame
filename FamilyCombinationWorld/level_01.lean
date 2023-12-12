ext x
apply Iff.intro
· intro h1
  rw [comp_def, fam_union_def] at h1
  rw [fam_inter_def]
  intro S h2
  rw [set_builder_def] at h2
  by_contra h3
  apply h1
  apply Exists.intro Sᶜ
  exact And.intro h2 h3
· intro h1
  rw [comp_def]
  rw [fam_inter_def] at h1
  by_contra h2
  rw [fam_union_def] at h2
  obtain ⟨S, h3⟩ := h2
  have h4 : Sᶜ ∈ {A | Aᶜ ∈ F} := by
    rw [set_builder_def, comp_comp]
    exact h3.left
  have h5 : x ∈ Sᶜ := h1 Sᶜ h4
  apply h5
  exact h3.right
