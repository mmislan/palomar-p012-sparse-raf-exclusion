import proofs.SparseLinearRAF.Resolution
import proofs.SparseLinearRAF.P012Foundation

namespace SparseLinearRAF
open RAF RAF.Polymer RAF.Concrete MeasureTheory Filter Topology

/-- At every fixed sparse intensity and food horizon, the chance of any
nonempty RAF within any fixed linear reaction budget tends to zero.
Channels retain their literal split positions and both reversible orientations. -/
theorem sparse_linear_raf_literature_resolution (t : Nat) (C : ℝ) {lambda : ℝ} (hl : 0 ≤ lambda) :
    Tendsto (fun n => literatureRAFProbability n t lambda C) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) ?_
    (sparse_linear_raf_probability_tendsto_zero t (Nat.ceil C) hl)
  intro n
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  rintro ω ⟨T,hT,hsize⟩
  refine ⟨T,hT,?_⟩
  have hC : C ≤ (Nat.ceil C : ℝ) := Nat.le_ceil C
  have hh := hsize.trans (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg n))
  exact_mod_cast hh

/-- In particular the proposed high-probability linear-size assertion is false. -/
theorem no_high_probability_linear_raf (t : Nat) :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ lambda C : ℝ, 0 ≤ lambda ∧ 0 ≤ C ∧
      ∀ᶠ n : Nat in atTop, 1-ε ≤ literatureRAFProbability n t lambda C) := by
  intro h
  obtain ⟨lambda,C,hl,_,hlarge⟩ := h (1/2) (by norm_num)
  have hsmall := (sparse_linear_raf_literature_resolution t C hl).eventually_lt_const
    (by norm_num : (0:ℝ)<1/2)
  have hf : ∀ᶠ _n : Nat in atTop, False := by
    filter_upwards [hlarge,hsmall] with n hn hn'
    linarith
  exact Filter.Eventually.exists hf |>.elim (fun _ h => h)

end SparseLinearRAF
