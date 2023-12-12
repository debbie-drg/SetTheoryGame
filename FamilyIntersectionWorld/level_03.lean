ext x
apply Iff.intro
· intro h
  rw [fam_inter_def]
  intro S h'
  rw [pair_def S A B] at h'
  cases' h' with hA hB
  · rw [hA]
    exact h.left
  · rw [hB]
    exact h.right
· intro h
  rw [fam_inter_def] at h
  have h1 : A ∈ {A, B} := by
    rw [pair_def A A B]
    apply Or.inl
    rfl
  have hA : x ∈ A := h A h1
  have h2 : B ∈ {A, B} := by
    rw [pair_def B A B]
    apply Or.inr
    rfl
  have hB : x ∈ B := h B h2
  exact And.intro hA hB
