import proofs.SparseLinearRAF.LowRankLimit

namespace SparseLinearRAF
open MeasureTheory ProbabilityTheory unitInterval RAF RAF.Polymer RAF.Concrete Filter Topology

def HasBoundedCoverRank (n t K : Nat) (ω : SparseSample (Molecule n) (Reaction n)) : Prop :=
  ∃ k, 0 < k ∧ k ≤ K ∧ HasCoverRank n t k ω

noncomputable def boundedCoverRankProbability (n t K : Nat) (lambda : ℝ) : ℝ :=
  (sparseMeasure (Molecule n) (Reaction n) (activityParameter n lambda) (channelParameter n)
    {ω | HasBoundedCoverRank n t K ω}).toReal

theorem boundedCoverRankProbability_le (n t K : Nat) (lambda : ℝ) :
    boundedCoverRankProbability n t K lambda ≤
      ∑ k ∈ Finset.range K, coverRankProbability n t (k+1) lambda := by
  let μ := sparseMeasure (Molecule n) (Reaction n) (activityParameter n lambda) (channelParameter n)
  let E := fun k : Fin K => {ω : SparseSample (Molecule n) (Reaction n) | HasCoverRank n t (k.val+1) ω}
  have hs : {ω | HasBoundedCoverRank n t K ω} ⊆ ⋃ k, E k := by
    rintro ω ⟨k,hk,hK,h⟩
    refine Set.mem_iUnion.mpr ⟨⟨k-1,by omega⟩,?_⟩
    simpa [E, Nat.sub_add_cancel hk] using h
  have hh := (measure_mono hs).trans (measure_iUnion_fintype_le μ E)
  have hr := ENNReal.toReal_mono
    (ENNReal.sum_ne_top.mpr (fun _ _ => measure_ne_top μ _)) hh
  rw [ENNReal.toReal_sum (fun _ _ => by finiteness)] at hr
  rw [← Fin.sum_univ_eq_sum_range (fun k => coverRankProbability n t (k+1) lambda) K]
  exact hr

theorem bounded_cover_rank_probability_tendsto_zero (t K : Nat) {lambda : ℝ} (hl : 0 ≤ lambda) :
    Tendsto (fun n => boundedCoverRankProbability n t K lambda) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => ∑ k ∈ Finset.range K, coverRankProbability n t (k+1) lambda)
      atTop (𝓝 (∑ _k ∈ Finset.range K, (0:ℝ))) :=
    tendsto_finsetSum _ (fun k _ => fixed_cover_rank_probability_tendsto_zero t (k+1) (by omega) hl)
  simp only [Finset.sum_const_zero] at ht
  exact squeeze_zero (fun _ => ENNReal.toReal_nonneg)
    (fun n => boundedCoverRankProbability_le n t K lambda) ht

end SparseLinearRAF
