import proofs.SparseLinearRAF.SupportCounting
import proofs.SparseLinearRAF.PrefixCounting

namespace SparseLinearRAF
open RAF RAF.Polymer RAF.Concrete

noncomputable def supportCountConstant (t C : Nat) : ℝ :=
  Real.exp 1 * ((Fintype.card (Molecule t) : ℝ)+3) *
    (((Fintype.card (Molecule t) : ℝ)+3)*C+1)

theorem linear_support_count_le (n t C m : Nat) (hm : 0 < m) (hbudget : m ≤ C*n) :
    (Fintype.card (SupportFamily n t m) : ℝ) ≤ (supportCountConstant t C * n)^m := by
  let f : ℝ := Fintype.card (Molecule t)
  let a : ℝ := (binaryFood n t).card
  let E : ℝ := (f+3)*((f+3)*C+1)
  have hf : a ≤ f := by dsimp [a,f]; exact_mod_cast source_food_card_le n t
  have hf0 : 0 ≤ f := by positivity
  have ha0 : 0 ≤ a := by positivity
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hmn : (m:ℝ) ≤ (C:ℝ)*n := by exact_mod_cast hbudget
  have hx : a+3*m ≤ (f+3)*m := by nlinarith
  have hy : a+3*m+n ≤ ((f+3)*C+1)*n := by nlinarith
  have hB : a^2+6*a*m+9*(m:ℝ)^2+(a+3*m)*n ≤ (m:ℝ)*(E*n) := by
    have hh := mul_le_mul hx hy (by positivity : 0 ≤ a+3*m+n) (by positivity : 0 ≤ (f+3)*m)
    dsimp [E]
    nlinarith [hh]
  have hc : (Fintype.card (SupportFamily n t m) : ℝ) * (m.factorial : ℝ) ≤
      ((a+3*m)^2+(a+3*m)*n)^m := by
    dsimp [a]
    exact_mod_cast support_count_mul_factorial_le n t m hm
  have hp : (0:ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have he : Real.exp (m:ℝ) = (Real.exp 1)^m := by simp [← Real.exp_nat_mul]
  calc
    _ ≤ ((a+3*m)^2+(a+3*m)*n)^m / m.factorial := (le_div_iff₀ hp).mpr hc
    _ ≤ ((m:ℝ)*(E*n))^m / m.factorial := by
      apply div_le_div_of_nonneg_right _ hp.le
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [hB]
    _ = (E*n)^m * ((m:ℝ)^m / m.factorial) := by rw [mul_pow]; ring
    _ ≤ (E*n)^m * Real.exp (m:ℝ) := by
      apply mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp (m:ℝ) (Nat.cast_nonneg m) m)
      dsimp [E]
      positivity
    _ = (supportCountConstant t C*n)^m := by
      rw [he]
      rw [← mul_pow]
      congr 1
      dsimp [supportCountConstant,E,f]
      ring

end SparseLinearRAF
