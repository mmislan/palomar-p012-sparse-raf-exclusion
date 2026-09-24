import Mathlib

namespace RAF.Polymer

/-- A binary word of fixed positive length, represented by its bit pattern. -/
abbrev Word (length : Nat) := Fin (2 ^ length)

/-- Nonempty binary words of length at most `n`. The `Fin n` index `k`
represents length `k+1`. -/
abbrev Molecule (n : Nat) := Σ k : Fin n, Word (k.val + 1)

def moleculeCount (n : Nat) : Nat := 2 ^ (n + 1) - 2

theorem card_molecule_sigma (n : Nat) :
    Fintype.card (Molecule n) = ∑ k : Fin n, 2 ^ (k.val + 1) := by
  simp [Molecule, Word]

theorem card_molecules_binary_five : Fintype.card (Molecule 5) = 62 := by
  decide

theorem moleculeCount_five : moleculeCount 5 = 62 := by norm_num [moleculeCount]

end RAF.Polymer
