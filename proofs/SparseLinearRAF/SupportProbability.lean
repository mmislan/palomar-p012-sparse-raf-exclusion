import proofs.SparseLinearRAF.SupportCounting
import proofs.SparseLinearRAF.SaturatedProgram
import proofs.SparseLinearRAF.CoverProbability
import proofs.SparseLinearRAF.SelfConstructionBound
import proofs.SparseLinearRAF.PrefixCounting

namespace SparseLinearRAF
open RAF RAF.Polymer RAF.Concrete MeasureTheory ProbabilityTheory unitInterval

theorem source_supportUniverse_card_le (n t : Nat) (S : Finset (Reaction n)) :
    (supportUniverse (binaryPolymerCRS n t) S).card ≤ Fintype.card (Molecule t)+3*S.card := by
  have hlocal (r : Reaction n) :
      ((binaryPolymerCRS n t).lhs r ∪ (binaryPolymerCRS n t).rhs r).card ≤ 3 := by
    have hh := Finset.card_union_le ((binaryPolymerCRS n t).lhs r) ((binaryPolymerCRS n t).rhs r)
    have hl : ((binaryPolymerCRS n t).lhs r).card ≤ 2 := by
      simpa [binaryPolymerCRS] using Finset.card_insert_le (reactionLeft r) {reactionRight r}
    have hr : ((binaryPolymerCRS n t).rhs r).card = 1 := by simp [binaryPolymerCRS]
    omega
  have hu : (S.biUnion (fun r => (binaryPolymerCRS n t).lhs r ∪ (binaryPolymerCRS n t).rhs r)).card ≤ 3*S.card := by
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ r ∈ S, (3:Nat) := Finset.sum_le_sum (fun r _ => hlocal r)
      _ = _ := by simp [Nat.mul_comm]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (source_food_card_le n t) hu)

def HasProductiveCover (n t m k : Nat) (ω : SparseSample (Molecule n) (Reaction n)) : Prop :=
  ∃ S : SupportFamily n t m, ∃ K : Finset (Molecule n),
    K ⊆ supportUniverse (binaryPolymerCRS n t) S.val ∧ K.card = k ∧
    (∀ x ∈ K, ω (x,none)) ∧ ∀ r ∈ S.val, ∃ x ∈ K, ω (x,some r)

theorem productive_cover_probability_le (n t m k : Nat) (p q : I) :
    sparseMeasure (Molecule n) (Reaction n) p q {ω | HasProductiveCover n t m k ω} ≤
      (Fintype.card (SupportFamily n t m) : ENNReal) *
      ((Fintype.card (Molecule t)+3*m : Nat) : ENNReal)^k *
      ((k:ENNReal)^m * ((toNNReal p : ENNReal)^k * (toNNReal q : ENNReal)^m)) := by
  classical
  let μ := sparseMeasure (Molecule n) (Reaction n) p q
  let E := fun S : SupportFamily n t m => {ω : SparseSample (Molecule n) (Reaction n) |
    ∃ K : Finset (Molecule n), K ⊆ supportUniverse (binaryPolymerCRS n t) S.val ∧ K.card=k ∧
      (∀ x ∈ K, ω (x,none)) ∧ ∀ r ∈ S.val, ∃ x ∈ K, ω (x,some r)}
  let c : ENNReal := (k:ENNReal)^m*((toNNReal p : ENNReal)^k*(toNNReal q : ENNReal)^m)
  have hE (S : SupportFamily n t m) : μ (E S) ≤
      (((Fintype.card (Molecule t)+3*m : Nat) : ENNReal)^k)*c := by
    let V := supportUniverse (binaryPolymerCRS n t) S.val
    let Ks := V.powersetCard k
    let A := fun K : Ks => {ω : SparseSample (Molecule n) (Reaction n) |
      (∀ x ∈ K.val, ω (x,none)) ∧ ∀ r ∈ S.val, ∃ x ∈ K.val, ω (x,some r)}
    have hs : E S ⊆ ⋃ K, A K := by
      rintro ω ⟨K,hKV,hk,ha,hcov⟩
      exact Set.mem_iUnion.mpr ⟨⟨K,Finset.mem_powersetCard.mpr ⟨hKV,hk⟩⟩,ha,hcov⟩
    have hh : ∀ K : Ks, μ (A K) ≤ c := by
      intro K
      have hk := (Finset.mem_powersetCard.mp K.property).2
      simpa only [μ,A,c,hk,S.property.1] using active_cover_probability_le p q K.val S.val
    have hcount : Ks.card ≤ (Fintype.card (Molecule t)+3*m)^k := by
      calc
        _ = V.card.choose k := Finset.card_powersetCard _ _
        _ ≤ V.card^k := Nat.choose_le_pow _ _
        _ ≤ _ := Nat.pow_le_pow_left (by simpa only [V,S.property.1] using source_supportUniverse_card_le n t S.val) k
    have h := (measure_mono hs).trans (measure_exists_le_card μ A c hh)
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ zero_le
    simpa only [Fintype.card_coe,Nat.cast_pow] using (show (Ks.card : ENNReal) ≤ ((Fintype.card (Molecule t)+3*m)^k : Nat) by exact_mod_cast hcount)
  have hs : {ω | HasProductiveCover n t m k ω} ⊆ ⋃ S, E S := by
    rintro ω ⟨S,hS⟩
    exact Set.mem_iUnion.mpr ⟨S,hS⟩
  have hh := (measure_mono hs).trans (measure_exists_le_card μ E _ hE)
  simpa only [μ,c,mul_assoc] using hh

end SparseLinearRAF
