import proofs.SparseLinearRAF.SparseLaw
import proofs.SparseLinearRAF.TwoFrontier
import proofs.SparseLinearRAF.Source

namespace SparseLinearRAF
open MeasureTheory ProbabilityTheory unitInterval RAF RAF.Polymer RAF.Concrete

def SelfConstructs {n : Nat} (t : Nat) (ω : SparseSample (Molecule n) (Reaction n))
    (x : Molecule n) : Prop :=
  ∃ T : Finset (Reaction n), T.Nonempty ∧ RevFoodGenerated (binaryPolymerCRS n t) T ∧
    (∃ j, x ∈ revClosureAt (binaryPolymerCRS n t) T j) ∧
    ∀ r ∈ T, sparseCatalysis ω x r

theorem selfConstructs_active {n t : Nat} {ω : SparseSample (Molecule n) (Reaction n)}
    {x : Molecule n} (h : SelfConstructs t ω x) : ω (x, none) := by
  obtain ⟨T, hne, _, _, hcat⟩ := h
  obtain ⟨r, hr⟩ := hne
  exact (hcat r hr).1

theorem selfConstructs_long_pair {n t : Nat} {ω : SparseSample (Molecule n) (Reaction n)}
    {x : Molecule n} (h : SelfConstructs t ω x) (hlong : 2*t < molLength x) :
    ∃ r : ShortReaction n (2*t), ∃ s : ShortReaction n (4*t),
      r.val ≠ s.val ∧ sparseCatalysis ω x r.val ∧ sparseCatalysis ω x s.val := by
  obtain ⟨T, hne, hfg, ⟨j,hj⟩, hcat⟩ := h
  obtain ⟨r,hr,s,hs,hne',hrl,hsl⟩ := two_distinct_short_channels T hne hfg x j hj hlong
  exact ⟨⟨r,hrl⟩,⟨s,hsl⟩,Ne.symm hne',hcat r hr,hcat s hs⟩

theorem long_selfConstructs_probability_le {n t : Nat} (p q : I) (x : Molecule n)
    (hlong : 2*t < molLength x) :
    sparseMeasure (Molecule n) (Reaction n) p q {ω | SelfConstructs t ω x} ≤
      (Fintype.card (ShortReaction n (2*t)) : ENNReal) *
      (Fintype.card (ShortReaction n (4*t)) : ENNReal) *
      ((toNNReal p : ENNReal) * (toNNReal q : ENNReal)^2) := by
  classical
  let μ := sparseMeasure (Molecule n) (Reaction n) p q
  let E := fun (z : ShortReaction n (2*t) × ShortReaction n (4*t)) =>
    {ω : SparseSample (Molecule n) (Reaction n) |
      z.1.val ≠ z.2.val ∧ sparseCatalysis ω x z.1.val ∧ sparseCatalysis ω x z.2.val}
  have hsub : {ω | SelfConstructs t ω x} ⊆ ⋃ z, E z := by
    intro ω hω
    obtain ⟨r,s,hrs,hr,hs⟩ := selfConstructs_long_pair hω hlong
    exact Set.mem_iUnion.mpr ⟨(r,s),hrs,hr,hs⟩
  have hE (z : ShortReaction n (2*t) × ShortReaction n (4*t)) :
      μ (E z) ≤ (toNNReal p : ENNReal) * (toNNReal q : ENNReal)^2 := by
    by_cases hz : z.1.val = z.2.val
    · simp [E, hz]
    · have he : E z = {ω | sparseCatalysis ω x z.1.val ∧ sparseCatalysis ω x z.2.val} := by
        ext ω
        simp [E, hz]
      rw [he]
      exact le_of_eq (sparse_two_edges p q x z.1.val z.2.val hz)
  calc
    μ {ω | SelfConstructs t ω x} ≤ μ (⋃ z, E z) := measure_mono hsub
    _ ≤ ∑ z, μ (E z) := measure_iUnion_fintype_le μ E
    _ ≤ ∑ _z : ShortReaction n (2*t) × ShortReaction n (4*t),
        (toNNReal p : ENNReal) * (toNNReal q : ENNReal)^2 := Finset.sum_le_sum (fun z _ => hE z)
    _ = _ := by simp [Fintype.card_prod, Nat.cast_mul, mul_assoc]

end SparseLinearRAF
