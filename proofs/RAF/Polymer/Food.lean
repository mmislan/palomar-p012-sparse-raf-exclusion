import proofs.RAF.Polymer.Words

namespace RAF.Polymer

/-- Food molecule identities for fixed food length `t`. -/
abbrev FoodMolecule (t : Nat) := Molecule t

theorem card_food_binary_t2 : Fintype.card (FoodMolecule 2) = 6 := by
  decide

end RAF.Polymer
