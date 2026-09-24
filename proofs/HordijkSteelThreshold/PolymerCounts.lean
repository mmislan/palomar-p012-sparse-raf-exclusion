import proofs.RAF.Polymer.Counts

namespace HordijkSteelThreshold

open RAF.Polymer

private theorem sum_binary_words (n : Nat) :
    (∑ k ∈ Finset.range n, 2 ^ (k + 1)) = 2 ^ (n + 1) - 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have hpow : 2 ≤ 2 ^ (n + 1) := by
      rw [pow_succ]
      have hp : 0 < 2 ^ n := by positivity
      omega
    omega

/-- Exact number of nonempty binary words of length at most `n`. -/
theorem card_molecules_exact (n : Nat) :
    Fintype.card (Molecule n) = 2 ^ (n + 1) - 2 := by
  rw [card_molecule_sigma]
  rw [Fin.sum_univ_eq_sum_range (fun k : Nat => 2 ^ (k + 1))]
  exact sum_binary_words n

private theorem sum_binary_reactions_shift (m : Nat) :
    (∑ k ∈ Finset.range (m + 2), 2 ^ (k + 1) * k) =
      m * 2 ^ (m + 3) + 4 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, Finset.sum_range_succ, ih]
    rw [show m + 2 + 1 = m + 3 by omega, show m + 1 + 3 = m + 4 by omega]
    rw [pow_succ]
    ring

/-- Exact split-position reversible reaction count. -/
theorem card_reactions_exact {n : Nat} (hn : 2 ≤ n) :
    Fintype.card (Reaction n) = (n - 2) * 2 ^ (n + 1) + 4 := by
  rw [card_reaction_sigma]
  rw [Fin.sum_univ_eq_sum_range (fun k : Nat => 2 ^ (k + 1) * k)]
  have h := sum_binary_reactions_shift (n - 2)
  have hn2 : n - 2 + 2 = n := by omega
  have hn3 : n - 2 + 3 = n + 1 := by omega
  simpa [hn2, hn3] using h

end HordijkSteelThreshold
