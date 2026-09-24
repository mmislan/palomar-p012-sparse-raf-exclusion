import proofs.RAF.Polymer.Words

namespace RAF.Polymer

/-- A split-position bidirectional reaction. The index `k` represents a
product of length `k+1`; `split : Fin k` records one of its `k` splits. -/
abbrev Reaction (n : Nat) := Σ k : Fin n, Word (k.val + 1) × Fin k.val

def reactionCount (n : Nat) : Nat := ∑ length ∈ Finset.Icc 2 n, (length - 1) * 2 ^ length

theorem card_reaction_sigma (n : Nat) :
    Fintype.card (Reaction n) = ∑ k : Fin n, 2 ^ (k.val + 1) * k.val := by
  simp [Reaction, Word]

theorem card_reactions_binary_five : Fintype.card (Reaction 5) = 196 := by
  set_option maxRecDepth 100000 in decide

theorem reactionCount_five : reactionCount 5 = 196 := by
  norm_num [reactionCount, Finset.sum_Icc_succ_top]

/-- Stable seed identities are ordered pairs of food molecules. Concatenation
and the split after the first factor embed these into `Reaction n` for
`n >= 2*t`; retaining the pair as the identity prevents display deduplication. -/
abbrev SeedIndex (t : Nat) := Molecule t × Molecule t

theorem card_seed_binary_t2 : Fintype.card (SeedIndex 2) = 36 := by
  decide

end RAF.Polymer
