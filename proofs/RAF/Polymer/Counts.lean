import proofs.RAF.Polymer.Reactions

namespace RAF.Polymer

theorem counts_binary_n5 :
    Fintype.card (Molecule 5) = 62 ∧ Fintype.card (Reaction 5) = 196 := by
  exact ⟨card_molecules_binary_five, card_reactions_binary_five⟩

end RAF.Polymer
