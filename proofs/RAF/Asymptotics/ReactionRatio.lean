import proofs.RAF.Polymer.Counts

namespace RAF.Asymptotics

def binaryCardX (n : Nat) : Nat := 2 ^ (n + 1) - 2
def binaryCardR (n : Nat) : Nat := (n - 2) * 2 ^ (n + 1) + 4
noncomputable def uniformP (lambda : ℝ) (n : Nat) : ℝ := lambda * n / binaryCardR n

theorem binary_counts_n5 : binaryCardX 5 = 62 ∧ binaryCardR 5 = 196 := by
  norm_num [binaryCardX, binaryCardR]

theorem uniformP_mul_cardX (lambda : ℝ) (n : Nat) :
    uniformP lambda n * binaryCardX n =
      lambda * n * binaryCardX n / binaryCardR n := by
  simp [uniformP]
  ring

theorem binaryCardX_tendsto : Filter.Tendsto binaryCardX Filter.atTop Filter.atTop := by
  have hsucc : Filter.Tendsto (fun n : Nat => n + 1) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id
  have hpow : Filter.Tendsto (fun n : Nat => 2 ^ (n + 1))
      Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : Nat) < 2)).comp hsucc
  apply Filter.tendsto_atTop.2
  intro b
  have hb : ∀ᶠ n in Filter.atTop, b + 2 ≤ 2 ^ (n + 1) :=
    hpow (Filter.eventually_ge_atTop (b + 2))
  filter_upwards [hb] with n hn
  simp only [binaryCardX]
  omega

theorem pairCount_tendsto {M : Nat} (hM : 0 < M) :
    Filter.Tendsto (fun n => M * binaryCardX n) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono (fun n => ?_) binaryCardX_tendsto
  exact Nat.le_mul_of_pos_left (binaryCardX n) hM

theorem card_ratio_bound (n : Nat) (hn : 4 ≤ n) :
    n * binaryCardX n ≤ 2 * binaryCardR n := by
  have hn2 : n ≤ 2 * (n - 2) := by omega
  have hx : binaryCardX n ≤ 2 ^ (n + 1) := by
    simp [binaryCardX]
  calc
    n * binaryCardX n ≤ n * 2 ^ (n + 1) := Nat.mul_le_mul_left n hx
    _ ≤ (2 * (n - 2)) * 2 ^ (n + 1) := Nat.mul_le_mul_right _ hn2
    _ = 2 * ((n - 2) * 2 ^ (n + 1)) := by ring
    _ ≤ 2 * binaryCardR n := by simp [binaryCardR]

theorem uniform_rate_pair_bound {M : Nat} (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (n : Nat) (hn : 4 ≤ n) :
    uniformP lambda n * (M * binaryCardX n : Nat) ≤ 2 * M * lambda := by
  have hRnat : 0 < binaryCardR n := by simp [binaryCardR]
  have hR : (0 : ℝ) < binaryCardR n := by exact_mod_cast hRnat
  have hratio : ((n * binaryCardX n : Nat) : ℝ) / binaryCardR n ≤ 2 := by
    rw [div_le_iff₀ hR]
    exact_mod_cast card_ratio_bound n hn
  calc
    uniformP lambda n * (M * binaryCardX n : Nat) =
        (lambda * M) * (((n * binaryCardX n : Nat) : ℝ) / binaryCardR n) := by
          simp [uniformP]
          ring
    _ ≤ (lambda * M) * 2 :=
      mul_le_mul_of_nonneg_left hratio (mul_nonneg hlambda (by positivity))
    _ = 2 * M * lambda := by ring

end RAF.Asymptotics
