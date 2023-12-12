ext x
apply Iff.intro
· intro h1
  rw [fam_union_def]
  cases' h1 with hA hB
  · apply Exists.intro A
    apply And.intro _ hA
    rw [pair_def]
    apply Or.inl
    rfl
  · apply Exists.intro B
    apply And.intro _ hB
    rw [pair_def]
    apply Or.inr
    rfl
· intro h1
  rw [fam_union_def] at h1
  obtain ⟨S, h2⟩ := h1
  rw [pair_def] at h2
  cases' h2.left with hA hB
  · apply Or.inl
    rw [← hA]
    exact h2.right
  · apply Or.inr
    rw [← hB]
    exact h2.right
