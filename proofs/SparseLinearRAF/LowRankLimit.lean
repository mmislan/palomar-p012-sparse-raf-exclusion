import proofs.SparseLinearRAF.LowRankBound
import proofs.SparseLinearRAF.Parameters

namespace SparseLinearRAF
open MeasureTheory ProbabilityTheory unitInterval RAF RAF.Polymer RAF.Concrete Filter Topology
open HordijkSteelThreshold

noncomputable def coverRankProbability (n t k : Nat) (lambda : ℝ) : ℝ :=
  (sparseMeasure (Molecule n) (Reaction n) (activityParameter n lambda) (channelParameter n)
    {ω | HasCoverRank n t k ω}).toReal

theorem coverRankProbability_bound (n t k d : Nat) (hk : 0 < k) (lambda : ℝ) :
    coverRankProbability n t k lambda ≤
      (shallowBound (Fintype.card (Molecule t)) t d : ℝ) * (activityParameter n lambda : ℝ) +
      (Fintype.card (Molecule n) : ℝ)^k *
      (prefixBound (Fintype.card (Molecule t)) t 0 d : ℝ) *
      ((k : ℝ)^d * ((activityParameter n lambda : ℝ)^k * (channelParameter n : ℝ)^d)) := by
  have h := cover_rank_probability_le n t k d hk (activityParameter n lambda) (channelParameter n)
  have hh := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hh
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_natCast,
    ENNReal.coe_toReal,unitInterval.coe_toNNReal] at hh
  apply hh.trans
  have hp0 := (activityParameter n lambda).2.1
  have hq0 := (channelParameter n).2.1
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ (activityParameter n lambda).2.1
    exact_mod_cast source_shallow_card_le n t d
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul
    · exact_mod_cast Nat.choose_le_pow (Fintype.card (Molecule n)) k
    · exact_mod_cast source_prefixes_card_le n t d
    · positivity
    · positivity

theorem rawActivity_rank_mass_tendsto_zero (k : Nat) (lambda : ℝ) :
    Tendsto (fun n => (Fintype.card (Molecule n) : ℝ)^k * (rawActivity n lambda)^k *
      (channelParameter n : ℝ)^(k+1)) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : Nat => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht := ((rawCatalysisP_mul_card_molecule_tendsto lambda).pow k).mul hi
  have ht' : Tendsto (fun n => (rawCatalysisP n lambda *
      (Fintype.card (Molecule n) : ℝ))^k * (n:ℝ)⁻¹) atTop (𝓝 0) := by simpa using ht
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [rawActivity_eq]
  dsimp [channelParameter]
  rw [mul_pow, mul_pow, pow_succ, inv_pow]
  field_simp

theorem fixed_cover_rank_probability_tendsto_zero (t k : Nat) (hk : 0 < k)
    {lambda : ℝ} (hl : 0 ≤ lambda) :
    Tendsto (fun n => coverRankProbability n t k lambda) atTop (𝓝 0) := by
  let a : ℝ := shallowBound (Fintype.card (Molecule t)) t (k+1)
  let b : ℝ := (prefixBound (Fintype.card (Molecule t)) t 0 (k+1) : ℝ) * (k:ℝ)^(k+1)
  have ht : Tendsto (fun n => a * (activityParameter n lambda : ℝ) +
      b * ((Fintype.card (Molecule n) : ℝ)^k * (rawActivity n lambda)^k *
      (channelParameter n : ℝ)^(k+1))) atTop (𝓝 0) := by
    simpa using ((activity_tendsto_zero hl).const_mul a).add
      ((rawActivity_rank_mass_tendsto_zero k lambda).const_mul b)
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) ?_ ht
  intro n
  apply (coverRankProbability_bound n t k (k+1) hk lambda).trans
  have hp := pow_le_pow_left₀ (activityParameter n lambda).2.1 (activity_le_raw hl n) k
  have hb : 0 ≤ (Fintype.card (Molecule n) : ℝ)^k * b * (channelParameter n : ℝ)^(k+1) := by
    have hq0 := (channelParameter n).2.1
    dsimp [b]
    positivity
  have hm := mul_le_mul_of_nonneg_left hp hb
  convert add_le_add_left hm (a * (activityParameter n lambda : ℝ)) using 1 <;>
    dsimp [a,b] <;> ring

end SparseLinearRAF
