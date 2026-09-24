import proofs.RAF.Concrete.PolymerCRS
import proofs.RAF.Core.CRS

namespace RAF.Concrete

open RAF RAF.Polymer

variable {M R : Type*} [DecidableEq M]

def RevSeedReaction (Q : ReversibleCRS M R) (r : R) : Prop :=
  Q.lhs r ⊆ Q.food ∨ Q.rhs r ⊆ Q.food

instance revSeedReactionDecidable (Q : ReversibleCRS M R) (r : R) :
    Decidable (RevSeedReaction Q r) := by
  unfold RevSeedReaction
  infer_instance

def RevFoodGenerated (Q : ReversibleCRS M R) (S : Finset R) : Prop :=
  ∀ r ∈ S, ∃ k, Q.lhs r ∪ Q.rhs r ⊆ revClosureAt Q S k

def RevReflexivelyAutocatalytic (Q : ReversibleCRS M R)
    (C : Catalysis M R) (S : Finset R) : Prop :=
  ∀ r ∈ S, ∃ x k, x ∈ revClosureAt Q S k ∧ C x r

def IsRevRAF (Q : ReversibleCRS M R) (C : Catalysis M R)
    (S : Finset R) : Prop :=
  S.Nonempty ∧ RevFoodGenerated Q S ∧ RevReflexivelyAutocatalytic Q C S

def RevSeedOpen (Q : ReversibleCRS M R) (C : Catalysis M R) : Prop :=
  ∃ r, RevSeedReaction Q r ∧ ∃ x, C x r

lemma revClosureStep_eq_food_of_no_seed (Q : ReversibleCRS M R) (S : Finset R)
    (h : ∀ r ∈ S, ¬ RevSeedReaction Q r) :
    revClosureStep Q S Q.food = Q.food := by
  have hempty : S.biUnion (fun r =>
      (if RevEnabledLhs Q Q.food r then Q.rhs r else ∅) ∪
      (if RevEnabledRhs Q Q.food r then Q.lhs r else ∅)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    simp only [Finset.mem_biUnion] at hx
    obtain ⟨r, hr, hx⟩ := hx
    have hn := h r hr
    have hnl : ¬ RevEnabledLhs Q Q.food r := fun hl => hn (Or.inl hl)
    have hnr : ¬ RevEnabledRhs Q Q.food r := fun hr' => hn (Or.inr hr')
    simp [hnl, hnr] at hx
  simp [revClosureStep, hempty]

lemma revClosureAt_eq_food_of_no_seed (Q : ReversibleCRS M R) (S : Finset R)
    (h : ∀ r ∈ S, ¬ RevSeedReaction Q r) :
    ∀ k, revClosureAt Q S k = Q.food := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [revClosureAt, ih, revClosureStep_eq_food_of_no_seed Q S h]

theorem exists_rev_seed_of_foodGenerated (Q : ReversibleCRS M R) (S : Finset R)
    (hne : S.Nonempty) (hfg : RevFoodGenerated Q S) :
    ∃ r ∈ S, RevSeedReaction Q r := by
  by_contra hexists
  have hnoseed : ∀ r ∈ S, ¬ RevSeedReaction Q r := by
    intro r hr hs
    exact hexists ⟨r, hr, hs⟩
  obtain ⟨r, hr⟩ := hne
  obtain ⟨k, hk⟩ := hfg r hr
  have hc := revClosureAt_eq_food_of_no_seed Q S hnoseed k
  have hl : Q.lhs r ⊆ Q.food := by
    intro x hx
    exact hc ▸ hk (Finset.mem_union_left _ hx)
  exact hnoseed r hr (Or.inl hl)

theorem rev_raf_implies_seedOpen (Q : ReversibleCRS M R) (C : Catalysis M R)
    (S : Finset R) (hraf : IsRevRAF Q C S) : RevSeedOpen Q C := by
  obtain ⟨hne, hfg, hra⟩ := hraf
  obtain ⟨r, hr, hseed⟩ := exists_rev_seed_of_foodGenerated Q S hne hfg
  obtain ⟨x, k, hx, hcat⟩ := hra r hr
  exact ⟨r, hseed, x, hcat⟩

abbrev PolymerSeedReaction (n t : Nat) :=
  {r : Reaction n // RevSeedReaction (binaryPolymerCRS n t) r}

private theorem seed_product_length_le_four {n : Nat} (r : Reaction n)
    (hseed : RevSeedReaction (binaryPolymerCRS n 2) r) :
    reactionProductLength r ≤ 4 := by
  rcases hseed with hl | hr
  · have hleft : reactionLeft r ∈ binaryFood n 2 := by
      apply hl
      simp [binaryPolymerCRS]
    have hright : reactionRight r ∈ binaryFood n 2 := by
      apply hl
      simp [binaryPolymerCRS]
    simp [binaryFood] at hleft hright
    rw [← reaction_length_add r]
    linarith
  · have hp : reactionProduct r ∈ binaryFood n 2 := by
      apply hr
      simp [binaryPolymerCRS]
    have hp2 : reactionProductLength r ≤ 2 := by
      simpa [binaryFood] using hp
    exact hp2.trans (by norm_num)

private def seedToReactionFour {n : Nat} (r : PolymerSeedReaction n 2) :
    Reaction 4 :=
  ⟨⟨r.1.1.val, by
      have := seed_product_length_le_four r.1 r.2
      dsimp [reactionProductLength] at this
      omega⟩, r.1.2⟩

private theorem seedToReactionFour_injective {n : Nat} :
    Function.Injective (seedToReactionFour (n := n)) := by
  intro a b hab
  apply Subtype.ext
  apply Sigma.ext
  · exact Fin.ext (congrArg (fun z : Reaction 4 => z.1.val) hab)
  · cases a with
    | mk a ha =>
      cases b with
      | mk b hb =>
        cases a with
        | mk ai ad =>
          cases b with
          | mk bi bd =>
            simp_all [seedToReactionFour]

theorem card_polymerSeedReaction_le_68 (n : Nat) :
    Fintype.card (PolymerSeedReaction n 2) ≤ 68 := by
  calc
    Fintype.card (PolymerSeedReaction n 2) ≤ Fintype.card (Reaction 4) :=
      Fintype.card_le_of_injective seedToReactionFour seedToReactionFour_injective
    _ = 68 := by decide

theorem polymer_raf_implies_seedOpen (n : Nat)
    (C : Catalysis (Molecule n) (Reaction n)) (S : Finset (Reaction n))
    (hraf : IsRevRAF (binaryPolymerCRS n 2) C S) :
    RevSeedOpen (binaryPolymerCRS n 2) C :=
  rev_raf_implies_seedOpen _ _ _ hraf

end RAF.Concrete
