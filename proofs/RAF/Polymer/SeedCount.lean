import proofs.RAF.Polymer.Food
import proofs.RAF.Polymer.Reactions

namespace RAF.Polymer

theorem seed_count_binary_t2 : Fintype.card (FoodMolecule 2 × FoodMolecule 2) = 36 := by
  decide

end RAF.Polymer
