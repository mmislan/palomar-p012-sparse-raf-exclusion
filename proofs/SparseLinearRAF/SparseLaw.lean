import Mathlib

namespace SparseLinearRAF
open MeasureTheory ProbabilityTheory unitInterval

/-- `none` is activity; `some r` is the conditional channel bit. -/
abbrev SparseSample (M R : Type*) := (M × Option R) → Prop

noncomputable def bitLaw (p : I) : Measure Prop :=
  toNNReal p • Measure.dirac True + toNNReal (σ p) • Measure.dirac False

noncomputable instance bitLaw_probability (p : I) : IsProbabilityMeasure (bitLaw p) := by
  constructor
  simp [bitLaw]

def coordinateParameter {M R : Type*} (p q : I) (z : M × Option R) : I :=
  match z.2 with
  | none => p
  | some _ => q

noncomputable def sparseMeasure (M R : Type*) (p q : I) : Measure (SparseSample M R) :=
  Measure.infinitePi (fun z => bitLaw (coordinateParameter p q z))

noncomputable instance sparseMeasure_probability (M R : Type*) (p q : I) :
    IsProbabilityMeasure (sparseMeasure M R p q) := by
  unfold sparseMeasure
  infer_instance

def sparseCatalysis {M R : Type*} (ω : SparseSample M R) (x : M) (r : R) : Prop :=
  ω (x, none) ∧ ω (x, some r)

theorem sparse_coordinate_independence (M R : Type*) (p q : I) :
    iIndepFun (fun z (ω : SparseSample M R) => ω z) (sparseMeasure M R p q) := by
  exact iIndepFun_infinitePi (fun _ => measurable_id)

theorem sparse_coordinate_probability {M R : Type*} (p q : I) (z : M × Option R) :
    sparseMeasure M R p q {ω | ω z} = (toNNReal (coordinateParameter p q z) : ENNReal) := by
  have h := Measure.infinitePi_map_eval (fun z : M × Option R =>
    bitLaw (coordinateParameter p q z)) z
  have hh := congrArg (fun μ : Measure Prop => μ {True}) h
  rw [Measure.map_apply (measurable_pi_apply z) (MeasurableSet.singleton True)] at hh
  simpa [sparseMeasure, bitLaw] using hh

theorem sparse_cylinder_probability {M R : Type*} (p q : I) (B : Finset (M × Option R)) :
    sparseMeasure M R p q {ω | ∀ z ∈ B, ω z} =
      ∏ z ∈ B, (toNNReal (coordinateParameter p q z) : ENNReal) := by
  have h := (sparse_coordinate_independence M R p q).measure_inter_preimage_eq_mul
    B (sets := fun _ => {True}) (fun _ _ => MeasurableSet.singleton True)
  simpa only [Set.preimage, Set.mem_singleton_iff, eq_iff_iff, iff_true,
    Set.iInter_ofPred, sparse_coordinate_probability] using h

theorem sparse_one_edge {M R : Type*} (p q : I) (x : M) (r : R) :
    sparseMeasure M R p q {ω | sparseCatalysis ω x r} =
      (toNNReal p : ENNReal) * (toNNReal q : ENNReal) := by
  classical
  have h := sparse_cylinder_probability p q ({(x, none), (x, some r)} : Finset (M × Option R))
  simpa [sparseCatalysis, coordinateParameter] using h

theorem sparse_two_edges {M R : Type*} (p q : I) (x : M) (r s : R) (hrs : r ≠ s) :
    sparseMeasure M R p q {ω | sparseCatalysis ω x r ∧ sparseCatalysis ω x s} =
      (toNNReal p : ENNReal) * (toNNReal q : ENNReal) ^ 2 := by
  classical
  have h := sparse_cylinder_probability p q
    ({(x, none), (x, some r), (x, some s)} : Finset (M × Option R))
  have he : {ω : SparseSample M R | sparseCatalysis ω x r ∧ sparseCatalysis ω x s} =
      {ω | ∀ z ∈ ({(x, none), (x, some r), (x, some s)} : Finset (M × Option R)), ω z} := by
    ext ω
    simp only [Set.mem_ofPred_eq, sparseCatalysis, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    tauto
  rw [he, h]
  simp [coordinateParameter, hrs, pow_two]

end SparseLinearRAF
