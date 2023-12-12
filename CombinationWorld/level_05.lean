intro x h3
have h4 : x ∈ A ∪ C := Or.inl h3
have h5 : x ∈ B ∪ C := h1 h4
cases' h5 with hB hC
· exact hB
· have h6 : x ∈ A ∩ C := And.intro h3 hC
  have h7 : x ∈ B ∩ C := h2 h6
  exact h7.left
