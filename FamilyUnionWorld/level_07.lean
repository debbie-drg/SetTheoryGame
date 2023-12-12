ext x
apply Iff.intro
· intro h1
  have h2 : x ∈ ⋃₀ F := h1.right
  rw [fam_union_def] at h2
  obtain ⟨S, h3⟩ := h2
  rw [fam_union_def]
  apply Exists.intro (A ∩ S)
  apply And.intro
  · rw [set_builder_def]
    apply Exists.intro S
    apply And.intro h3.left
    rfl
  · exact And.intro h1.left h3.right
· intro h1
  rw [fam_union_def] at h1
  obtain ⟨X, h2⟩ := h1
  rw [set_builder_def] at h2
  obtain ⟨S, h3⟩ := h2.left
  apply And.intro
  · rw [h3.right] at h2
    exact h2.right.left
  · rw [fam_union_def]
    apply Exists.intro S
    rw [h3.right] at h2
    exact And.intro h3.left h2.right.right
