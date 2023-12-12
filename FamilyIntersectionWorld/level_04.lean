ext
apply Iff.intro
· intro h
  rw [fam_inter_def] at h
  apply And.intro
  · rw [fam_inter_def]
    intro S h'
    have hu : S ∈ F ∪ G := Or.inl h'
    exact h S hu
  · rw [fam_inter_def]
    intro S h'
    have hu : S ∈ F ∪ G := Or.inr h'
    exact h S hu
· intro h
  rw [fam_inter_def]
  intro S h'
  cases' h' with hF hG
  · exact h.left S hF
  · exact h.right S hG
