import Mathlib

namespace RAF.Probability

/-- Product probability that `N` independent Bernoulli(`p`) coordinates are
all absent, defined recursively to expose the independence multiplication. -/
def allAbsentProbability (p : ℝ) : Nat → ℝ
  | 0 => 1
  | n + 1 => (1 - p) * allAbsentProbability p n

theorem allAbsentProbability_eq_pow (p : ℝ) (N : Nat) :
    allAbsentProbability p N = (1 - p) ^ N := by
  induction N with
  | zero => rfl
  | succ N ih => simp [allAbsentProbability, ih, pow_succ, mul_comm]

theorem allAbsentProbability_nonneg {p : ℝ} (hp1 : p ≤ 1) (N : Nat) :
    0 ≤ allAbsentProbability p N := by
  rw [allAbsentProbability_eq_pow]
  positivity

end RAF.Probability
