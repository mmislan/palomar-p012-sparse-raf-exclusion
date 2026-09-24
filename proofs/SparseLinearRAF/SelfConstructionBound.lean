import proofs.SparseLinearRAF.SelfConstruction

namespace SparseLinearRAF
open MeasureTheory ProbabilityTheory unitInterval RAF RAF.Polymer RAF.Concrete

theorem measure_exists_le_card {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (μ : Measure Ω) (E : J → Set Ω) (c : ENNReal) (h : ∀ j, μ (E j) ≤ c) :
    μ (⋃ j, E j) ≤ (Fintype.card J : ENNReal) * c := by
  calc
    _ ≤ ∑ j, μ (E j) := measure_iUnion_fintype_le μ E
    _ ≤ ∑ _j : J, c := Finset.sum_le_sum (fun j _ => h j)
    _ = _ := by simp

/-- Finite bound over the actual sparse law, including possible food catalysts. -/
theorem any_selfConstructs_probability_le (n t : Nat) (p q : I) :
    sparseMeasure (Molecule n) (Reaction n) p q {ω | ∃ x, SelfConstructs t ω x} ≤
      (Fintype.card (Molecule (2*t)) : ENNReal) * (toNNReal p : ENNReal) +
      (Fintype.card (Molecule n) : ENNReal) *
      ((Fintype.card (Reaction (2*t)) : ENNReal) *
       (Fintype.card (Reaction (4*t)) : ENNReal) *
       ((toNNReal p : ENNReal) * (toNNReal q : ENNReal)^2)) := by
  classical
  let μ := sparseMeasure (Molecule n) (Reaction n) p q
  let A := fun x : ShortMolecule n (2*t) => {ω : SparseSample (Molecule n) (Reaction n) | ω (x.val,none)}
  let B := fun x : Molecule n => {ω : SparseSample (Molecule n) (Reaction n) |
    2*t < molLength x ∧ SelfConstructs t ω x}
  let c : ENNReal := (Fintype.card (Reaction (2*t)) : ENNReal) *
    (Fintype.card (Reaction (4*t)) : ENNReal) *
    ((toNNReal p : ENNReal) * (toNNReal q : ENNReal)^2)
  have hsub : {ω | ∃ x, SelfConstructs t ω x} ⊆ (⋃ x, A x) ∪ (⋃ x, B x) := by
    rintro ω ⟨x,hx⟩
    by_cases hs : molLength x ≤ 2*t
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨x,hs⟩,selfConstructs_active hx⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨x,by omega,hx⟩)
  have hA : μ (⋃ x, A x) ≤ (Fintype.card (Molecule (2*t)) : ENNReal) * (toNNReal p : ENNReal) := by
    apply (measure_exists_le_card μ A (toNNReal p) ?_).trans
      (mul_le_mul_left (by exact_mod_cast short_molecule_card_le n (2*t)) _)
    intro x
    exact le_of_eq (sparse_coordinate_probability p q (x.val,none))
  have hB : μ (⋃ x, B x) ≤ (Fintype.card (Molecule n) : ENNReal) * c := by
    apply measure_exists_le_card
    intro x
    by_cases hs : 2*t < molLength x
    · have hb : B x ⊆ {ω | SelfConstructs t ω x} := fun _ h => h.2
      apply (measure_mono hb).trans
      apply (long_selfConstructs_probability_le p q x hs).trans
      exact mul_le_mul_left (mul_le_mul'
        (by exact_mod_cast short_reaction_card_le n (2*t))
        (by exact_mod_cast short_reaction_card_le n (4*t))) _
    · have he : B x = ∅ := by ext ω; simp [B, hs]
      rw [he, measure_empty]
      exact zero_le
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hA hB))

end SparseLinearRAF
