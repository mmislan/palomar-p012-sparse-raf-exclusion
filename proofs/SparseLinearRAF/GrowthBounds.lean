import proofs.SparseLinearRAF.Parameters
import proofs.SparseLinearRAF.LinearSupportCount

namespace SparseLinearRAF
open RAF RAF.Polymer RAF.Concrete HordijkSteelThreshold Filter Topology

theorem polynomial_rank_domination (C : Nat) (D : ℝ) :
    ∃ K : Nat, ∀ k ≥ K, (D*(k:ℝ))^C ≤ (4/3:ℝ)^k := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt C (by norm_num : (1:ℝ)<4/3)).const_mul (D^C)
  have hh : ∀ᶠ k : Nat in atTop, D^C*((k:ℝ)^C/(4/3:ℝ)^k) < 1 := by
    apply (show Tendsto (fun k : Nat => D^C*((k:ℝ)^C/(4/3:ℝ)^k)) atTop (𝓝 0) by simpa using ht).eventually_lt_const
    norm_num
  obtain ⟨K,hK⟩ := eventually_atTop.mp hh
  refine ⟨K,fun k hk => ?_⟩
  have h := hK k hk
  rw [← mul_div_assoc] at h
  have hh := (div_lt_one (by positivity : (0:ℝ)<(4/3:ℝ)^k)).mp h
  simpa only [mul_pow] using hh.le

theorem activity_le_polynomial_exp {lambda : ℝ} (hl : 0 ≤ lambda) {n : Nat} (hn : 2 ≤ n) :
    (activityParameter n lambda : ℝ) ≤ lambda*(n:ℝ)^2/(2:ℝ)^n := by
  apply (activity_le_raw hl n).trans
  have hR : (2:ℝ)^n ≤ Fintype.card (Reaction n) := by
    have hh := card_reaction_lower n (by omega)
    have hp := Nat.le_mul_of_pos_left (2^n) (show 0<n-1 by omega)
    exact_mod_cast hp.trans hh
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hR

theorem activity_universe_decay (t C : Nat) {lambda : ℝ} (hl : 0 ≤ lambda) :
    ∀ᶠ n : Nat in atTop,
      ((Fintype.card (Molecule t) : ℝ)+3*C*n)*(activityParameter n lambda : ℝ) ≤ (9/16:ℝ)^n := by
  let f : ℝ := Fintype.card (Molecule t)
  have ht2 := (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1:ℝ)<9/8)).const_mul (lambda*f)
  have ht3 := (tendsto_pow_const_div_const_pow_of_one_lt 3 (by norm_num : (1:ℝ)<9/8)).const_mul (lambda*3*C)
  have ht : Tendsto (fun n : Nat => lambda*(f*(n:ℝ)^2+3*C*(n:ℝ)^3)/(9/8:ℝ)^n)
      atTop (𝓝 0) := by
    convert ht2.add ht3 using 1 <;> try simp
    funext n
    ring
  filter_upwards [ht.eventually_lt_const (by norm_num : (0:ℝ)<1),eventually_ge_atTop 2] with n hsmall hn
  have hnum := (div_lt_one (by positivity : (0:ℝ)<(9/8:ℝ)^n)).mp hsmall
  have hact := mul_le_mul_of_nonneg_left (activity_le_polynomial_exp hl hn)
    (by positivity : 0 ≤ f+3*C*n)
  calc
    _ ≤ lambda*(f*(n:ℝ)^2+3*C*(n:ℝ)^3)/(2:ℝ)^n := by
      convert hact using 1
      dsimp [f]
      ring
    _ ≤ (9/8:ℝ)^n/(2:ℝ)^n := div_le_div_of_nonneg_right hnum.le (by positivity)
    _ = (9/16:ℝ)^n := by rw [← div_pow]; norm_num

theorem supportCountConstant_one_le (t C : Nat) : 1 ≤ supportCountConstant t C := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hf : (0:ℝ) ≤ Fintype.card (Molecule t) := by positivity
  have hC : (0:ℝ) ≤ C := by positivity
  unfold supportCountConstant
  have h1 : (1:ℝ) ≤ (Fintype.card (Molecule t) : ℝ)+3 := by linarith
  have h2 : (1:ℝ) ≤ ((Fintype.card (Molecule t) : ℝ)+3)*C+1 := by
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (Fintype.card (Molecule t) : ℝ)+3) hC]
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le he h1) h2

end SparseLinearRAF
