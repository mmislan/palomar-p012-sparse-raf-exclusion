import proofs.HordijkSteelThreshold.Gateway
import proofs.HordijkSteelThreshold.PolymerCounts
import proofs.RAF.Asymptotics.ReactionRatio
import proofs.RAF.Concrete.Asymptotics
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace HordijkSteelThreshold

open Filter Topology
open RAF.Polymer RAF.Concrete

noncomputable def normalizationRatio (n : Nat) : ℝ :=
  ((n : ℝ) * ((2 : ℝ) ^ (n + 1) - 2)) /
    (((n : ℝ) - 2) * (2 : ℝ) ^ (n + 1) + 4)

theorem normalizationRatio_tendsto_one :
    Tendsto normalizationRatio atTop (𝓝 1) := by
  have hn : Tendsto (fun n : Nat => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hnInv : Tendsto (fun n : Nat => ((n : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hn
  have hsucc : Tendsto (fun n : Nat => n + 1) atTop atTop := by
    apply Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id
  have hpowNat : Tendsto (fun n : Nat => 2 ^ (n + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : Nat) < 2)).comp hsucc
  have hpowCast : Tendsto (fun n : Nat => ((2 ^ (n + 1) : Nat) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hpowNat
  have hA : Tendsto (fun n : Nat => (2 : ℝ) ^ (n + 1)) atTop atTop := by
    simpa using hpowCast
  have hAInv : Tendsto (fun n : Nat => (((2 : ℝ) ^ (n + 1))⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hA
  have hnum : Tendsto
      (fun n : Nat => 1 - 2 * (((2 : ℝ) ^ (n + 1))⁻¹)) atTop (𝓝 1) := by
    convert tendsto_const_nhds.sub (tendsto_const_nhds.mul hAInv) using 1
    all_goals norm_num
  have hden : Tendsto
      (fun n : Nat =>
        1 - 2 * ((n : ℝ)⁻¹) +
          4 * ((n : ℝ)⁻¹) * (((2 : ℝ) ^ (n + 1))⁻¹))
      atTop (𝓝 1) := by
    convert (tendsto_const_nhds.sub (tendsto_const_nhds.mul hnInv)).add
      ((tendsto_const_nhds.mul hnInv).mul hAInv) using 1
    all_goals norm_num
  have hquot := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hquot' : Tendsto
      (fun n : Nat =>
        (1 - 2 * (((2 : ℝ) ^ (n + 1))⁻¹)) /
          (1 - 2 * ((n : ℝ)⁻¹) +
            4 * ((n : ℝ)⁻¹) * (((2 : ℝ) ^ (n + 1))⁻¹)))
      atTop (𝓝 1) := by
    convert hquot using 1; try norm_num
  apply hquot'.congr'
  filter_upwards [Filter.eventually_ge_atTop 3] with n hn3
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hA0 : (2 : ℝ) ^ (n + 1) ≠ 0 := by positivity
  dsimp [normalizationRatio]
  field_simp

theorem rawCatalysisP_mul_card_molecule_tendsto (lambda : ℝ) :
    Tendsto (fun n => rawCatalysisP n lambda * Fintype.card (Molecule n))
      atTop (𝓝 lambda) := by
  have h : Tendsto (fun n : Nat => lambda * normalizationRatio n)
      atTop (𝓝 lambda) := by
    simpa using (tendsto_const_nhds.mul normalizationRatio_tendsto_one)
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  have hpow : 2 ≤ 2 ^ (n + 1) := by
    have hp : 0 < 2 ^ n := by positivity
    rw [pow_succ]
    omega
  have hncast : ((n - 2 : Nat) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub hn]
    norm_num
  simp only [rawCatalysisP]
  rw [card_molecules_exact, card_reactions_exact hn]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_pow, Nat.cast_sub hpow, hncast]
  dsimp [normalizationRatio]
  ring

theorem catalysisP_mul_card_molecule_tendsto {lambda : ℝ} (hlambda : 0 < lambda) :
    Tendsto (fun n => (catalysisP n lambda : ℝ) * Fintype.card (Molecule n))
      atTop (𝓝 lambda) := by
  apply (rawCatalysisP_mul_card_molecule_tendsto lambda).congr'
  filter_upwards [catalysisP_eq_raw_eventually hlambda] with n hn
  rw [hn]

theorem card_molecule_tendsto_atTop :
    Tendsto (fun n : Nat => Fintype.card (Molecule n)) atTop atTop := by
  refine Tendsto.congr' ?_ RAF.Asymptotics.binaryCardX_tendsto
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [card_molecules_exact]
  rfl

theorem catalysisP_tendsto_zero {lambda : ℝ} (hlambda : 0 < lambda) :
    Tendsto (fun n => (catalysisP n lambda : ℝ)) atTop (nhds 0) := by
  have hcard : Tendsto (fun n : Nat => (Fintype.card (Molecule n) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp card_molecule_tendsto_atTop
  have hquot := (catalysisP_mul_card_molecule_tendsto hlambda).div_atTop hcard
  apply hquot.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hcard0 : (Fintype.card (Molecule n) : ℝ) ≠ 0 := by
    rw [card_molecules_exact]
    exact_mod_cast Nat.ne_of_gt (show 0 < 2 ^ (n + 1) - 2 by
      have hp : 2 < 2 ^ (n + 1) := by
        rw [pow_succ]
        have : 1 < 2 ^ n := by
          exact one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hn)
        omega
      omega)
  field_simp

private theorem log_one_sub_div_tendsto :
    Tendsto (fun x : ℝ => Real.log (1 - x) / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-1)) := by
  have hd : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1) 0 := by
    have hlog : HasDerivAt Real.log 1 1 := by
      simpa using Real.hasDerivAt_log one_ne_zero
    have hinner : HasDerivAt (fun x : ℝ => 1 - x) (-1) 0 := by
      convert (hasDerivAt_const (x := (0 : ℝ)) 1).sub
        (hasDerivAt_id (x := (0 : ℝ))) using 1
      · funext x
        rfl
      all_goals norm_num
    have hlog' : HasDerivAt Real.log 1 (1 - (0 : ℝ)) := by
      simpa using hlog
    simpa [Function.comp_def] using hlog'.comp 0 hinner
  simpa [div_eq_inv_mul, mul_comm] using hd.tendsto_slope_zero

theorem catalysisP_eventually_ne_zero {lambda : ℝ} (hlambda : 0 < lambda) :
    ∀ᶠ n in atTop, (catalysisP n lambda : ℝ) ≠ 0 := by
  have hprod := catalysisP_mul_card_molecule_tendsto hlambda
  filter_upwards [hprod.eventually_ne (ne_of_gt hlambda)] with n hn hp
  apply hn
  rw [hp, zero_mul]

theorem log_one_sub_catalysisP_div_tendsto {lambda : ℝ} (hlambda : 0 < lambda) :
    Tendsto (fun n => Real.log (1 - (catalysisP n lambda : ℝ)) /
      (catalysisP n lambda : ℝ)) atTop (nhds (-1)) := by
  have hp0 := catalysisP_tendsto_zero hlambda
  have hpne := catalysisP_eventually_ne_zero hlambda
  have hpwithin : Tendsto (fun n => (catalysisP n lambda : ℝ)) atTop
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hp0
      (hpne.mono fun n hn => by simpa using hn)
  exact log_one_sub_div_tendsto.comp hpwithin

theorem card_seedCoord_exact {n : Nat} (hn : 4 ≤ n) :
    Fintype.card (SeedCoord n) = Fintype.card (Molecule n) * 36 := by
  simp [SeedCoord, Fintype.card_prod, card_concrete_gateway_binary_t2 hn]

theorem seedLogExponent_tendsto {lambda : ℝ} (hlambda : 0 < lambda) :
    Tendsto (fun n => (Fintype.card (SeedCoord n) : ℝ) *
      Real.log (1 - (catalysisP n lambda : ℝ))) atTop (nhds (-36 * lambda)) := by
  have hmass := catalysisP_mul_card_molecule_tendsto hlambda
  have hscaled : Tendsto
      (fun n => 36 * ((catalysisP n lambda : ℝ) * Fintype.card (Molecule n)))
      atTop (nhds (36 * lambda)) := by
    simpa using tendsto_const_nhds.mul hmass
  have hratio := log_one_sub_catalysisP_div_tendsto hlambda
  have hmul := hscaled.mul hratio
  have hmul' : Tendsto
      (fun n => (36 * ((catalysisP n lambda : ℝ) * Fintype.card (Molecule n))) *
        (Real.log (1 - (catalysisP n lambda : ℝ)) /
          (catalysisP n lambda : ℝ)))
      atTop (nhds (-36 * lambda)) := by
    convert hmul using 1
    all_goals ring
  apply hmul'.congr'
  filter_upwards [Filter.eventually_ge_atTop 4,
    catalysisP_eventually_ne_zero hlambda] with n hn hp
  rw [card_seedCoord_exact hn]
  push_cast
  field_simp

theorem seedClosedProbability_tendsto_exp {lambda : ℝ} (hlambda : 0 < lambda) :
    Tendsto (fun n => seedClosedProbability n lambda) atTop
      (nhds (Real.exp (-36 * lambda))) := by
  have hexp := (Real.continuous_exp.tendsto (-36 * lambda)).comp
    (seedLogExponent_tendsto hlambda)
  apply hexp.congr'
  have hp_lt_one : ∀ᶠ n in atTop, (catalysisP n lambda : ℝ) < 1 :=
    (catalysisP_tendsto_zero hlambda).eventually_lt_const zero_lt_one
  filter_upwards [Filter.eventually_ge_atTop 4, hp_lt_one] with n hn hp
  rw [measure_seedClosed]
  have hbase : 0 < 1 - (catalysisP n lambda : ℝ) := sub_pos.mpr hp
  rw [← Real.exp_log hbase, ← Real.exp_nat_mul]
  rfl

theorem rafProbability_limsup_le_gateway_ceiling {lambda : ℝ} (hlambda : 0 < lambda) :
    limsup (fun n => rafProbability n lambda) atTop ≤
      1 - Real.exp (-36 * lambda) := by
  let closed : Nat → ℝ := fun n => seedClosedProbability n lambda
  let raf : Nat → ℝ := fun n => rafProbability n lambda
  have hpoint : ∀ᶠ n in atTop, raf n ≤ 1 - closed n := by
    filter_upwards [] with n
    dsimp [raf, closed]
    linarith [actual_raf_seed_bound n lambda]
  have hraf_nonneg : ∀ᶠ n in atTop, 0 ≤ raf n := by
    filter_upwards [] with n
    exact MeasureTheory.measureReal_nonneg
  have hraf_cobounded : atTop.IsCoboundedUnder (· ≤ ·) raf :=
    Filter.IsCoboundedUnder.of_frequently_ge hraf_nonneg.frequently
  have hright_bounded : atTop.IsBoundedUnder (· ≤ ·) (fun n => 1 - closed n) :=
    Filter.isBoundedUnder_of ⟨1, fun n => by
      have hn : 0 ≤ closed n := MeasureTheory.measureReal_nonneg
      linarith⟩
  have hmono := limsup_le_limsup hpoint hraf_cobounded hright_bounded
  have hright : Tendsto (fun n => 1 - closed n) atTop
      (nhds (1 - Real.exp (-36 * lambda))) := by
    exact tendsto_const_nhds.sub (seedClosedProbability_tendsto_exp hlambda)
  exact hmono.trans_eq hright.limsup_eq

end HordijkSteelThreshold
