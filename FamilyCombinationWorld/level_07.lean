have h2 := h1 {S | ∃ x ∈ A, S = {x}}
have h3 : ⋃₀ {S | ∃ x ∈ A, S = {x}} = A := by
  ext x
  apply Iff.intro
  · intro h
    rw [fam_union_def] at h
    obtain ⟨S, h3⟩ := h
    rw [set_builder_def] at h3
    obtain ⟨y, h4⟩ := h3.left
    have h5 : x = y := by
      rw [h4.right, single_def] at h3
      exact h3.right
    rw [h5]
    exact h4.left
  · intro h3
    rw [fam_union_def]
    apply Exists.intro {x}
    rw [set_builder_def]
    apply And.intro
    · apply Exists.intro x
      apply And.intro h3
      rfl
    · rw [single_def]
have h4 : A ∈ {S | ∃ x ∈ A, S = {x}} := h2 h3
rw [set_builder_def] at h4
obtain ⟨x, h4⟩ := h4
apply Exists.intro x
exact h4.right
