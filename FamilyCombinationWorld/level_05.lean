intro x h2
rw [fam_union_def]
have h3 := h2.left
rw [fam_union_def] at h3
obtain ⟨S, h3⟩ := h3
have h4 : S ∈ G := by
  by_contra h4
  have h5 : S ∈ F ∩ Gᶜ := And.intro h3.left h4
  have h6 : x ∈ ⋃₀ (F ∩ Gᶜ) := by
    rw [fam_union_def]
    apply Exists.intro S
    exact And.intro h5 h3.right
  have h7 : x ∈ ⋃₀ F ∩ (⋃₀ G)ᶜ := h1 h6
  apply h7.right
  exact h2.right
apply Exists.intro S
apply And.intro
· exact And.intro h3.left h4
· exact h3.right
