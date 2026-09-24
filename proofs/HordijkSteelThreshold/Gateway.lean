import proofs.RAF.Concrete.SeedGateway
import proofs.RAF.Polymer.SeedCount

namespace HordijkSteelThreshold

open RAF RAF.Polymer RAF.Concrete

/-- In the concrete reversible polymer model, the apparent extra class of
reverse-food gateways adds nothing: a reaction is a gateway exactly when both
canonical split factors are food molecules. -/
theorem revSeedReaction_iff_food_factors {n t : Nat} (r : Reaction n) :
    RevSeedReaction (binaryPolymerCRS n t) r ↔
      reactionLeft r ∈ binaryFood n t ∧ reactionRight r ∈ binaryFood n t := by
  constructor
  · intro h
    rcases h with hl | hr
    · constructor
      · exact hl (by simp [binaryPolymerCRS])
      · exact hl (by simp [binaryPolymerCRS])
    · have hp : reactionProduct r ∈ binaryFood n t :=
        hr (by simp [binaryPolymerCRS])
      have hp_len : reactionProductLength r ≤ t := by
        simpa [binaryFood] using hp
      constructor <;> simp only [binaryFood, Finset.mem_filter, Finset.mem_univ, true_and]
      · rw [molLength_reactionLeft]
        linarith [reaction_length_add r]
      · rw [molLength_reactionRight]
        linarith [reaction_length_add r]
  · rintro ⟨hl, hr⟩
    refine Or.inl ?_
    intro x hx
    simp only [binaryPolymerCRS, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · simpa [binaryPolymerCRS, hx] using hl
    · simpa [binaryPolymerCRS, hx] using hr

theorem revSeedReaction_iff_factor_lengths {n t : Nat} (r : Reaction n) :
    RevSeedReaction (binaryPolymerCRS n t) r ↔
      reactionLeftLength r ≤ t ∧ reactionRightLength r ≤ t := by
  rw [revSeedReaction_iff_food_factors]
  simp [binaryFood]

theorem card_gateway_four_binary_t2 :
    Fintype.card (PolymerSeedReaction 4 2) = 36 := by
  decide

private def restrictReactionFour {n : Nat} (r : PolymerSeedReaction n 2) :
    Reaction 4 :=
  ⟨⟨r.1.1.val, by
      have h := (revSeedReaction_iff_factor_lengths r.1).mp r.2
      change r.1.2.2.val + 1 ≤ 2 ∧ r.1.1.val - r.1.2.2.val ≤ 2 at h
      omega⟩, r.1.2⟩

private theorem restrictReactionFour_lengths {n : Nat}
    (r : PolymerSeedReaction n 2) :
    reactionLeftLength (restrictReactionFour r) = reactionLeftLength r.1 ∧
      reactionRightLength (restrictReactionFour r) = reactionRightLength r.1 := by
  constructor <;> rfl

private def restrictGatewayFour {n : Nat} (r : PolymerSeedReaction n 2) :
    PolymerSeedReaction 4 2 :=
  ⟨restrictReactionFour r, by
    rw [revSeedReaction_iff_factor_lengths]
    rw [(restrictReactionFour_lengths r).1, (restrictReactionFour_lengths r).2]
    exact (revSeedReaction_iff_factor_lengths r.1).mp r.2⟩

private theorem restrictGatewayFour_injective {n : Nat} :
    Function.Injective (restrictGatewayFour (n := n)) := by
  intro a b hab
  apply Subtype.ext
  apply Sigma.ext
  · exact Fin.ext (congrArg (fun z : PolymerSeedReaction 4 2 => z.1.1.val) hab)
  · cases a with
    | mk a ha =>
      cases b with
      | mk b hb =>
        cases a with
        | mk ai ad =>
          cases b with
          | mk bi bd =>
            simp_all [restrictGatewayFour, restrictReactionFour]

private def liftReactionFour {n : Nat} (hn : 4 ≤ n) (r : Reaction 4) :
    Reaction n :=
  ⟨⟨r.1.val, lt_of_lt_of_le r.1.isLt hn⟩, r.2⟩

private theorem liftReactionFour_lengths {n : Nat} (hn : 4 ≤ n)
    (r : Reaction 4) :
    reactionLeftLength (liftReactionFour hn r) = reactionLeftLength r ∧
      reactionRightLength (liftReactionFour hn r) = reactionRightLength r := by
  constructor <;> rfl

private def liftGatewayFour {n : Nat} (hn : 4 ≤ n)
    (r : PolymerSeedReaction 4 2) : PolymerSeedReaction n 2 :=
  ⟨liftReactionFour hn r.1, by
    rw [revSeedReaction_iff_factor_lengths]
    rw [(liftReactionFour_lengths hn r.1).1, (liftReactionFour_lengths hn r.1).2]
    exact (revSeedReaction_iff_factor_lengths r.1).mp r.2⟩

private theorem liftGatewayFour_injective {n : Nat} (hn : 4 ≤ n) :
    Function.Injective (liftGatewayFour hn) := by
  intro a b hab
  apply Subtype.ext
  apply Sigma.ext
  · exact Fin.ext (congrArg (fun z : PolymerSeedReaction n 2 => z.1.1.val) hab)
  · cases a with
    | mk a ha =>
      cases b with
      | mk b hb =>
        cases a with
        | mk ai ad =>
          cases b with
          | mk bi bd =>
            simp_all [liftGatewayFour, liftReactionFour]

/-- The exact concrete gateway count.  It is stable once all products of two
food molecules (length at most four) are present. -/
theorem card_concrete_gateway_binary_t2 {n : Nat} (hn : 4 ≤ n) :
    Fintype.card (PolymerSeedReaction n 2) = 36 := by
  have hle : Fintype.card (PolymerSeedReaction n 2) ≤
      Fintype.card (PolymerSeedReaction 4 2) :=
    Fintype.card_le_of_injective restrictGatewayFour restrictGatewayFour_injective
  have hge : Fintype.card (PolymerSeedReaction 4 2) ≤
      Fintype.card (PolymerSeedReaction n 2) :=
    Fintype.card_le_of_injective (liftGatewayFour hn) (liftGatewayFour_injective hn)
  rw [card_gateway_four_binary_t2] at hle hge
  omega

end HordijkSteelThreshold
