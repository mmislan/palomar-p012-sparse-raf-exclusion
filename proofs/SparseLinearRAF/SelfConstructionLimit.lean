import proofs.SparseLinearRAF.SelfConstructionBound
import proofs.SparseLinearRAF.Parameters
import proofs.SparseLinearRAF.P012Foundation

namespace SparseLinearRAF
open MeasureTheory ProbabilityTheory unitInterval RAF RAF.Polymer RAF.Concrete Filter Topology

theorem selfConstructionProbability_bound (n t : Nat) (lambda : ℝ) :
    selfConstructionProbability n t lambda ≤
      (Fintype.card (Molecule (2*t)) : ℝ) * (activityParameter n lambda : ℝ) +
      (Fintype.card (Molecule n) : ℝ) *
      ((Fintype.card (Reaction (2*t)) : ℝ) *
       (Fintype.card (Reaction (4*t)) : ℝ) *
       ((activityParameter n lambda : ℝ) * (channelParameter n : ℝ)^2)) := by
  have h := any_selfConstructs_probability_le n t (activityParameter n lambda) (channelParameter n)
  have hh := ENNReal.toReal_mono (by finiteness) h
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hh
  simpa only [selfConstructionProbability, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, ENNReal.coe_toReal, unitInterval.coe_toNNReal] using hh

/-- Single-catalyst self-construction vanishes even with cleavage, at every
fixed nonnegative sparse intensity and every fixed food horizon. This is
the rank-one literature question; it does not resolve linear-size RAFs. -/
theorem single_catalyst_probability_tendsto_zero (t : Nat) {lambda : ℝ} (hl : 0 ≤ lambda) :
    Tendsto (fun n => selfConstructionProbability n t lambda) atTop (𝓝 0) := by
  let a : ℝ := Fintype.card (Molecule (2*t))
  let b : ℝ := (Fintype.card (Reaction (2*t)) : ℝ) * Fintype.card (Reaction (4*t))
  have ht : Tendsto (fun n => a * (activityParameter n lambda : ℝ) +
      b * ((Fintype.card (Molecule n) : ℝ) * rawActivity n lambda * (channelParameter n : ℝ)^2))
      atTop (𝓝 0) := by
    simpa using ((activity_tendsto_zero hl).const_mul a).add
      ((rawActivity_pair_mass_tendsto_zero lambda).const_mul b)
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) ?_ ht
  intro n
  apply (selfConstructionProbability_bound n t lambda).trans
  have hp := activity_le_raw hl n
  have hb : 0 ≤ (Fintype.card (Molecule n) : ℝ) * b * (channelParameter n : ℝ)^2 := by
    dsimp [b]
    positivity
  have hm := mul_le_mul_of_nonneg_left hp hb
  convert add_le_add_left hm (a * (activityParameter n lambda : ℝ)) using 1 <;>
    dsimp [a,b] <;> ring

end SparseLinearRAF
