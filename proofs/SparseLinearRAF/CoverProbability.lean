import proofs.SparseLinearRAF.SparseLaw

namespace SparseLinearRAF
open MeasureTheory ProbabilityTheory unitInterval

theorem sparse_injective_cylinder {M R J : Type*} [Fintype J]
    (p q : I) (g : J → M × Option R) (hg : Function.Injective g) :
    sparseMeasure M R p q {ω | ∀ j, ω (g j)} =
      ∏ j, (toNNReal (coordinateParameter p q (g j)) : ENNReal) := by
  classical
  have h := sparse_cylinder_probability p q (Finset.univ.image g)
  rw [Finset.prod_image (fun a _ b _ hab => hg hab)] at h
  simpa using h

theorem active_assignment_probability {M R : Type*} [DecidableEq M] [DecidableEq R]
    (p q : I) (K : Finset M) (D : Finset R) (f : D → K) :
    sparseMeasure M R p q {ω | (∀ x ∈ K, ω (x,none)) ∧
      ∀ r : D, ω ((f r).val,some r.val)} =
      (toNNReal p : ENNReal)^K.card * (toNNReal q : ENNReal)^D.card := by
  classical
  let g : Sum K D → M × Option R := Sum.elim (fun x => (x.val,none))
    (fun r => ((f r).val,some r.val))
  have hg : Function.Injective g := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext (congrArg Prod.fst hab))
      | inr b => have hh := congrArg Prod.snd hab; cases hh
    | inr a =>
      cases b with
      | inl b => have hh := congrArg Prod.snd hab; cases hh
      | inr b => exact congrArg Sum.inr (Subtype.ext (Option.some.inj (congrArg Prod.snd hab)))
  have h := sparse_injective_cylinder p q g hg
  simpa [g,coordinateParameter,Fintype.prod_sum_type] using h

/-- A union over catalyst assignments preserves the activity penalty `p^k`.
This deliberately uses `k*q` rather than needing an exact conditional law. -/
theorem active_cover_probability_le {M R : Type*} [DecidableEq M] [DecidableEq R]
    (p q : I) (K : Finset M) (D : Finset R) :
    sparseMeasure M R p q {ω | (∀ x ∈ K, ω (x,none)) ∧
      ∀ r ∈ D, ∃ x ∈ K, ω (x,some r)} ≤
      (K.card : ENNReal)^D.card *
      ((toNNReal p : ENNReal)^K.card * (toNNReal q : ENNReal)^D.card) := by
  classical
  let μ := sparseMeasure M R p q
  let E := fun f : D → K => {ω : SparseSample M R | (∀ x ∈ K, ω (x,none)) ∧
      ∀ r : D, ω ((f r).val,some r.val)}
  have hsub : {ω | (∀ x ∈ K, ω (x,none)) ∧ ∀ r ∈ D, ∃ x ∈ K, ω (x,some r)} ⊆
      ⋃ f, E f := by
    rintro ω ⟨ha,hcov⟩
    have hc : ∀ r : D, ∃ x : K, ω (x.val,some r.val) := by
      intro r
      obtain ⟨x,hx,hbit⟩ := hcov r.val r.property
      exact ⟨⟨x,hx⟩,hbit⟩
    choose f hf using hc
    exact Set.mem_iUnion.mpr ⟨f,ha,hf⟩
  calc
    μ _ ≤ μ (⋃ f, E f) := measure_mono hsub
    _ ≤ ∑ f, μ (E f) := measure_iUnion_fintype_le μ E
    _ = _ := by
      simp only [μ,E,active_assignment_probability,Finset.sum_const,Finset.card_univ,
        Fintype.card_fun,Fintype.card_coe,nsmul_eq_mul,Nat.cast_pow]

end SparseLinearRAF
