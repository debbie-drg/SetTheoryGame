ext x
apply Iff.intro
· intro h
  cases' h with hAB hC
  · cases' hAB with hA hB
    · exact Or.inl hA
    · exact Or.inr (Or.inl hB)
  · exact Or.inr (Or.inr hC)
· intro h
  cases' h with hA hBC
  · exact Or.inl (Or.inl hA)
  · cases' hBC with hB hC
    · exact Or.inl (Or.inr hB)
    · exact Or.inr hC
