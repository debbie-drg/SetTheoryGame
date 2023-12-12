apply Iff.intro
· intro h1
  intro B h2
  intro x h3
  have h4 : x ∈ ⋃₀ F := by
    rw [fam_union_def]
    apply Exists.intro B
    exact And.intro h2 h3
  exact h1 h4
· intro h1
  intro x h2
  rw [fam_union_def] at h2
  obtain ⟨S, h3⟩ := h2
  exact (h1 S h3.left) h3.right
