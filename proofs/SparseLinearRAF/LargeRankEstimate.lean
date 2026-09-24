import proofs.SparseLinearRAF.GrowthBounds
import proofs.SparseLinearRAF.SupportProbability

namespace SparseLinearRAF
open RAF RAF.Polymer RAF.Concrete MeasureTheory ProbabilityTheory unitInterval Filter Topology

noncomputable def productiveCoverProbability (n t m k : Nat) (lambda : ℝ) : ℝ :=
  (sparseMeasure (Molecule n) (Reaction n) (activityParameter n lambda) (channelParameter n)
    {ω | HasProductiveCover n t m k ω}).toReal

theorem productiveCoverProbability_linear_bound (n t C m k : Nat)
    (hn : 0 < n) (hm : 0 < m) (hbudget : m ≤ C*n) (lambda : ℝ) :
    productiveCoverProbability n t m k lambda ≤
      (supportCountConstant t C*k)^m *
      (((Fintype.card (Molecule t) : ℝ)+3*C*n)*(activityParameter n lambda : ℝ))^k := by
  have h := productive_cover_probability_le n t m k (activityParameter n lambda) (channelParameter n)
  have hh := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_natCast,
    ENNReal.coe_toReal,unitInterval.coe_toNNReal,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hh
  have hp0 := (activityParameter n lambda).2.1
  have hq0 := (channelParameter n).2.1
  have hD := (supportCountConstant_one_le t C).trans' (by norm_num : (0:ℝ)≤1)
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  apply hh.trans
  calc
    _ ≤ (supportCountConstant t C*n)^m * ((Fintype.card (Molecule t) : ℝ)+3*m)^k *
        ((k:ℝ)^m*((activityParameter n lambda : ℝ)^k*(channelParameter n : ℝ)^m)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (linear_support_count_le n t C m hm hbudget) (by positivity)
    _ = (supportCountConstant t C*k)^m *
        ((((Fintype.card (Molecule t) : ℝ)+3*m))*(activityParameter n lambda : ℝ))^k := by
      dsimp [channelParameter]
      simp only [mul_pow,inv_pow]
      field_simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hp0
      have hb : (m:ℝ) ≤ (C:ℝ)*n := by exact_mod_cast hbudget
      linarith

theorem large_rank_uniform_estimate (t C : Nat) {lambda : ℝ} (hl : 0 ≤ lambda) :
    ∃ K : Nat, ∀ᶠ n : Nat in atTop, ∀ m k : Nat, 0 < m → m ≤ C*n → K < k →
      productiveCoverProbability n t m k lambda ≤ (3/4:ℝ)^n := by
  obtain ⟨K,hK⟩ := polynomial_rank_domination C (supportCountConstant t C)
  refine ⟨K,?_⟩
  filter_upwards [activity_universe_decay t C hl,eventually_ge_atTop 1] with n hact hn
  intro m k hm hbudget hk
  have hk1 : 0 < k := by omega
  have hb : 1 ≤ supportCountConstant t C*k :=
    one_le_mul_of_one_le_of_one_le (supportCountConstant_one_le t C) (by exact_mod_cast hk1)
  have hp0 := (activityParameter n lambda).2.1
  apply (productiveCoverProbability_linear_bound n t C m k hn hm hbudget lambda).trans
  calc
    _ ≤ (supportCountConstant t C*k)^(C*n) * ((9/16:ℝ)^n)^k := by
      apply mul_le_mul
      · exact pow_le_pow_right₀ hb hbudget
      · exact pow_le_pow_left₀ (by positivity) hact k
      · positivity
      · positivity
    _ ≤ ((4/3:ℝ)^k)^n * ((9/16:ℝ)^n)^k := by
      rw [pow_mul]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (hK k (by omega)) n) (by positivity)
    _ = (3/4:ℝ)^(n*k) := by
      rw [← pow_mul,← pow_mul,Nat.mul_comm k n,← mul_pow]
      norm_num
    _ ≤ (3/4:ℝ)^n := pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_mul_of_pos_right n hk1)

end SparseLinearRAF
