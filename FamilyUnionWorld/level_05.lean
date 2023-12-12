ext x
apply Iff.intro
· intro h1
  rw [fam_union_def] at h1
  obtain ⟨S, h2⟩ := h1
  cases' h2.left with hF hG
  · apply Or.inl
    rw [fam_union_def]
    apply Exists.intro S
    exact And.intro hF h2.right
  · apply Or.inr
    rw [fam_union_def]
    apply Exists.intro S
    exact And.intro hG h2.right
· intro h1
  rw [fam_union_def]
  cases' h1 with hF hG
  · rw [fam_union_def] at hF
    obtain ⟨S, h1⟩ := hF
    apply Exists.intro S
    exact And.intro (Or.inl h1.left) h1.right
  · rw [fam_union_def] at hG
    obtain ⟨S, h1⟩ := hG
    apply Exists.intro S
    exact And.intro (Or.inr h1.left) h1.right
