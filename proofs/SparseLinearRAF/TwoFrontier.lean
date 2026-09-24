import proofs.HordijkSteelThreshold.Gateway

namespace SparseLinearRAF

open RAF RAF.Polymer RAF.Concrete HordijkSteelThreshold

/-- A source closure cannot leave length `2*t` if its only selected channel
of length at most `4*t` is itself short. This includes both orientations. -/
theorem closure_length_le_of_unique_short {n t : Nat} (S : Finset (Reaction n))
    (r₀ : Reaction n) (h₀ : reactionProductLength r₀ ≤ 2 * t)
    (hunique : ∀ r ∈ S, reactionProductLength r ≤ 4 * t → r = r₀) :
    ∀ j, ∀ x ∈ revClosureAt (binaryPolymerCRS n t) S j, molLength x ≤ 2 * t := by
  intro j
  induction j with
  | zero =>
    intro x hx
    have h : molLength x ≤ t := by simpa [revClosureAt, binaryPolymerCRS, binaryFood] using hx
    omega
  | succ j ih =>
    intro x hx
    simp only [revClosureAt, revClosureStep, Finset.mem_union, Finset.mem_biUnion] at hx
    rcases hx with hx | ⟨r, hr, hx⟩
    · exact ih x hx
    have hlen := reaction_length_add r
    rcases hx with hx | hx
    · by_cases he : RevEnabledLhs (binaryPolymerCRS n t)
          (revClosureAt (binaryPolymerCRS n t) S j) r
      · have hl := ih (reactionLeft r) (he (by simp [binaryPolymerCRS]))
        have hh := ih (reactionRight r) (he (by simp [binaryPolymerCRS]))
        rw [molLength_reactionLeft] at hl
        rw [molLength_reactionRight] at hh
        have heq := hunique r hr (by omega)
        simp [he] at hx
        have hxp : x = reactionProduct r := by simpa [binaryPolymerCRS] using hx
        rw [hxp, molLength_reactionProduct, heq]
        exact h₀
      · simp [he] at hx
    · by_cases he : RevEnabledRhs (binaryPolymerCRS n t)
          (revClosureAt (binaryPolymerCRS n t) S j) r
      · have hp := ih (reactionProduct r) (he (by simp [binaryPolymerCRS]))
        rw [molLength_reactionProduct] at hp
        simp [he] at hx
        have hxside : x = reactionLeft r ∨ x = reactionRight r := by
          simpa [binaryPolymerCRS] using hx
        rcases hxside with rfl | rfl
        · rw [molLength_reactionLeft]; omega
        · rw [molLength_reactionRight]; omega
      · simp [he] at hx

/-- Every food-generated support reaching beyond the fixed one-step length
shell selects two distinct channels in a fixed finite length range. -/
theorem two_distinct_short_channels {n t : Nat} (S : Finset (Reaction n))
    (hne : S.Nonempty) (hfg : RevFoodGenerated (binaryPolymerCRS n t) S)
    (x : Molecule n) (j : Nat) (hx : x ∈ revClosureAt (binaryPolymerCRS n t) S j)
    (hlong : 2 * t < molLength x) :
    ∃ r₀ ∈ S, ∃ r₁ ∈ S, r₁ ≠ r₀ ∧
      reactionProductLength r₀ ≤ 2 * t ∧ reactionProductLength r₁ ≤ 4 * t := by
  obtain ⟨r₀, hr₀, hseed⟩ := exists_rev_seed_of_foodGenerated
    (binaryPolymerCRS n t) S hne hfg
  have hf := (revSeedReaction_iff_factor_lengths r₀).mp hseed
  have h₀ : reactionProductLength r₀ ≤ 2 * t := by
    have := reaction_length_add r₀
    omega
  by_contra hnone
  have hu : ∀ r ∈ S, reactionProductLength r ≤ 4 * t → r = r₀ := by
    intro r hr hshort
    by_contra hne'
    exact hnone ⟨r₀, hr₀, r, hr, hne', h₀, hshort⟩
  have := closure_length_le_of_unique_short S r₀ h₀ hu j x hx
  omega

end SparseLinearRAF
