import proofs.HordijkSteelThreshold.GatewayProbability

namespace SparseLinearRAF
open Filter Topology unitInterval RAF.Polymer RAF.Concrete HordijkSteelThreshold

noncomputable def rawActivity (n : Nat) (lambda : ℝ) : ℝ :=
  lambda * (n : ℝ)^2 / Fintype.card (Reaction n)

noncomputable def activityParameter (n : Nat) (lambda : ℝ) : I :=
  ⟨min 1 (max 0 (rawActivity n lambda)),
    le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

noncomputable def channelParameter (n : Nat) : I :=
  ⟨(n : ℝ)⁻¹, inv_nonneg.mpr (Nat.cast_nonneg n), by
    cases n with
    | zero => norm_num
    | succ n => apply inv_le_one_of_one_le₀; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)⟩

theorem activity_le_raw {lambda : ℝ} (hl : 0 ≤ lambda) (n : Nat) :
    (activityParameter n lambda : ℝ) ≤ rawActivity n lambda := by
  have h : 0 ≤ rawActivity n lambda := by unfold rawActivity; positivity
  exact (min_le_right _ _).trans_eq (max_eq_right h)

theorem rawActivity_eq (n : Nat) (lambda : ℝ) :
    rawActivity n lambda = (n : ℝ) * rawCatalysisP n lambda := by
  unfold rawActivity rawCatalysisP
  ring

theorem rawActivity_tendsto_zero {lambda : ℝ} (hl : 0 ≤ lambda) :
    Tendsto (fun n => rawActivity n lambda) atTop (𝓝 0) := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1:ℝ)<2)).const_mul lambda
  have ht' : Tendsto (fun n : Nat => lambda * ((n:ℝ)^2 / 2^n)) atTop (𝓝 0) := by
    simpa using ht
  apply squeeze_zero' (Eventually.of_forall (fun n => by unfold rawActivity; positivity)) ?_ ht'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hR : (2:ℝ)^n ≤ Fintype.card (Reaction n) := by
    have hh := card_reaction_lower n (by omega)
    have hp : 2^n ≤ (n-1)*2^n := Nat.le_mul_of_pos_left _ (by omega)
    exact_mod_cast hp.trans hh
  have hh := div_le_div_of_nonneg_left (show 0 ≤ lambda * (n:ℝ)^2 by positivity)
    (show (0:ℝ)<2^n by positivity) hR
  simpa [rawActivity, mul_div_assoc] using hh

theorem activity_tendsto_zero {lambda : ℝ} (hl : 0 ≤ lambda) :
    Tendsto (fun n => (activityParameter n lambda : ℝ)) atTop (𝓝 0) :=
  squeeze_zero (fun n => (activityParameter n lambda).2.1)
    (activity_le_raw hl) (rawActivity_tendsto_zero hl)

theorem activity_eq_raw_eventually {lambda : ℝ} (hl : 0 ≤ lambda) :
    ∀ᶠ n in atTop, (activityParameter n lambda : ℝ) = rawActivity n lambda := by
  filter_upwards [(rawActivity_tendsto_zero hl).eventually_lt_const (by norm_num : (0:ℝ)<1)] with n hn
  have h : 0 ≤ rawActivity n lambda := by unfold rawActivity; positivity
  simp [activityParameter, max_eq_right h, min_eq_right hn.le]

theorem rawActivity_pair_mass_tendsto_zero (lambda : ℝ) :
    Tendsto (fun n => (Fintype.card (Molecule n) : ℝ) * rawActivity n lambda *
      (channelParameter n : ℝ)^2) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : Nat => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht := (rawCatalysisP_mul_card_molecule_tendsto lambda).mul hi
  have ht' : Tendsto (fun n => rawCatalysisP n lambda *
      (Fintype.card (Molecule n) : ℝ) * (n:ℝ)⁻¹) atTop (𝓝 0) := by simpa using ht
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [rawActivity_eq]
  dsimp [channelParameter]
  field_simp

end SparseLinearRAF
