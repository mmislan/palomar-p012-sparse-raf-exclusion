import proofs.RAF.Concrete.Events
import proofs.RAF.Asymptotics.FixedGap

namespace RAF.Concrete

open Filter Topology
open RAF.Polymer

def proxySeedCoordCount (n : Nat) : Nat := 68 * 2 ^ (n + 1)

private theorem sum_word_card_le (n : Nat) :
    (∑ k ∈ Finset.range n, 2 ^ (k + 1)) ≤ 2 ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ k ∈ Finset.range n, 2 ^ (k + 1)) + 2 ^ (n + 1) ≤
            2 ^ (n + 1) + 2 ^ (n + 1) := Nat.add_le_add_right ih _
        _ = 2 ^ (n + 1 + 1) := by rw [pow_succ]; ring

theorem card_molecule_le_pow (n : Nat) :
    Fintype.card (Molecule n) ≤ 2 ^ (n + 1) := by
  rw [RAF.Polymer.card_molecule_sigma]
  rw [Fin.sum_univ_eq_sum_range (fun k : Nat => 2 ^ (k + 1))]
  exact sum_word_card_le n

theorem card_reaction_lower (n : Nat) (hn : 1 ≤ n) :
    (n - 1) * 2 ^ n ≤ Fintype.card (Reaction n) := by
  rw [RAF.Polymer.card_reaction_sigma]
  let i : Fin n := ⟨n - 1, by omega⟩
  have hi := Finset.single_le_sum
    (s := Finset.univ) (f := fun k : Fin n => 2 ^ (k.val + 1) * k.val)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hnEq : n - 1 + 1 = n := Nat.sub_add_cancel hn
  simpa [i, hnEq, Nat.mul_comm] using hi

theorem card_seedCoord_le_proxy (n : Nat) :
    Fintype.card (SeedCoord n) ≤ proxySeedCoordCount n := by
  rw [Fintype.card_prod]
  calc
    Fintype.card (Molecule n) * Fintype.card (PolymerSeedReaction n 2) ≤
        2 ^ (n + 1) * Fintype.card (PolymerSeedReaction n 2) :=
      Nat.mul_le_mul_right _ (card_molecule_le_pow n)
    _ ≤ 2 ^ (n + 1) * 68 :=
      Nat.mul_le_mul_left _ (card_polymerSeedReaction_le_68 n)
    _ = proxySeedCoordCount n := by simp [proxySeedCoordCount, Nat.mul_comm]

theorem proxySeedCoordCount_tendsto :
    Tendsto proxySeedCoordCount atTop atTop := by
  have hsucc : Tendsto (fun n : Nat => n + 1) atTop atTop := by
    apply Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id
  have hpow : Tendsto (fun n : Nat => 2 ^ (n + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : Nat) < 2)).comp hsucc
  apply Filter.tendsto_atTop_mono (fun n => ?_) hpow
  exact Nat.le_mul_of_pos_left _ (by norm_num : 0 < 68)

theorem catalysisP_le_raw {n : Nat} {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    (catalysisP n lambda : ℝ) ≤ rawCatalysisP n lambda := by
  have hraw : 0 ≤ rawCatalysisP n lambda := by
    simp [rawCatalysisP]
    positivity
  change min 1 (max 0 (rawCatalysisP n lambda)) ≤ rawCatalysisP n lambda
  rw [max_eq_right hraw]
  exact min_le_right _ _

theorem rawCatalysisP_proxy_bound {lambda : ℝ} (hlambda : 0 ≤ lambda)
    (n : Nat) (hn : 4 ≤ n) :
    rawCatalysisP n lambda * proxySeedCoordCount n ≤ 272 * lambda := by
  have hRnat := card_reaction_lower n (by omega)
  have hR : (0 : ℝ) < Fintype.card (Reaction n) := by
    have : 0 < (n - 1) * 2 ^ n := Nat.mul_pos (by omega) (by positivity)
    exact_mod_cast this.trans_le hRnat
  have hcoef : 136 * n ≤ 272 * (n - 1) := by omega
  have hnat : n * proxySeedCoordCount n ≤
      272 * Fintype.card (Reaction n) := by
    calc
      n * proxySeedCoordCount n = (136 * n) * 2 ^ n := by
        simp [proxySeedCoordCount, pow_succ]
        ring
      _ ≤ (272 * (n - 1)) * 2 ^ n := Nat.mul_le_mul_right _ hcoef
      _ = 272 * ((n - 1) * 2 ^ n) := by ring
      _ ≤ 272 * Fintype.card (Reaction n) := Nat.mul_le_mul_left _ hRnat
  have hratio :
      ((n * proxySeedCoordCount n : Nat) : ℝ) /
          Fintype.card (Reaction n) ≤ 272 := by
    rw [div_le_iff₀ hR]
    exact_mod_cast hnat
  calc
    rawCatalysisP n lambda * proxySeedCoordCount n =
        lambda * (((n * proxySeedCoordCount n : Nat) : ℝ) /
          Fintype.card (Reaction n)) := by
      simp [rawCatalysisP]
      ring
    _ ≤ lambda * 272 := mul_le_mul_of_nonneg_left hratio hlambda
    _ = 272 * lambda := by ring

theorem catalysisP_eq_raw_eventually {lambda : ℝ} (hlambda : 0 < lambda) :
    ∀ᶠ n in atTop, (catalysisP n lambda : ℝ) = rawCatalysisP n lambda := by
  let C : ℝ := 272 * lambda
  have hcount := proxySeedCoordCount_tendsto
  have hcast : Tendsto (fun n => (proxySeedCoordCount n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcount
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hlarge : ∀ᶠ n : Nat in atTop, 4 ≤ n := Filter.eventually_ge_atTop 4
  have hC : ∀ᶠ n in atTop, C ≤ (proxySeedCoordCount n : ℝ) :=
    hcast (Filter.eventually_ge_atTop C)
  filter_upwards [hlarge, hC] with n hn hCn
  have hpair : (0 : ℝ) < proxySeedCoordCount n := lt_of_lt_of_le hCpos hCn
  have hpMul : rawCatalysisP n lambda * proxySeedCoordCount n ≤ C := by
    simpa [C] using rawCatalysisP_proxy_bound (le_of_lt hlambda) n hn
  have hraw_le : rawCatalysisP n lambda ≤ 1 := by
    nlinarith
  have hraw_nonneg : 0 ≤ rawCatalysisP n lambda := by
    simp [rawCatalysisP]
    positivity
  change min 1 (max 0 (rawCatalysisP n lambda)) = rawCatalysisP n lambda
  rw [max_eq_right hraw_nonneg, min_eq_right hraw_le]

theorem concrete_seedClosed_eventually_pos {lambda : ℝ} (hlambda : 0 < lambda) :
    ∃ delta > 0, ∀ᶠ n in atTop, delta ≤ seedClosedProbability n lambda := by
  let C : ℝ := 272 * lambda
  have hcount := proxySeedCoordCount_tendsto
  have hcast : Tendsto (fun n => (proxySeedCoordCount n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcount
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hlarge : ∀ᶠ n : Nat in atTop, 4 ≤ n := Filter.eventually_ge_atTop 4
  have hC : ∀ᶠ n in atTop, C ≤ (proxySeedCoordCount n : ℝ) :=
    hcast (Filter.eventually_ge_atTop C)
  have hrate : ∀ᶠ n in atTop,
      0 ≤ 1 - C / (proxySeedCoordCount n : ℝ) ∧
        (catalysisP n lambda : ℝ) ≤ C / (proxySeedCoordCount n : ℝ) := by
    filter_upwards [hlarge, hC] with n hn hCn
    have hpair : (0 : ℝ) < proxySeedCoordCount n :=
      lt_of_lt_of_le hCpos hCn
    have hpMul : (catalysisP n lambda : ℝ) * proxySeedCoordCount n ≤ C :=
      (mul_le_mul_of_nonneg_right (catalysisP_le_raw (le_of_lt hlambda))
        (by positivity)).trans (by simpa [C] using
          rawCatalysisP_proxy_bound (le_of_lt hlambda) n hn)
    constructor
    · rw [sub_nonneg, div_le_one hpair]
      exact hCn
    · exact (le_div_iff₀ hpair).2 hpMul
  obtain ⟨delta, hdelta, hproxy⟩ :=
    RAF.Asymptotics.bernoulli_absent_eventually_pos
      (fun n => (catalysisP n lambda : ℝ)) proxySeedCoordCount C hcount hrate
  refine ⟨delta, hdelta, ?_⟩
  filter_upwards [hproxy] with n hn
  rw [measure_seedClosed]
  have hp0 : 0 ≤ 1 - (catalysisP n lambda : ℝ) := by
    exact sub_nonneg.mpr (catalysisP n lambda).2.2
  have hp1 : 1 - (catalysisP n lambda : ℝ) ≤ 1 := by
    linarith [(catalysisP n lambda).2.1]
  exact hn.trans (pow_le_pow_of_le_one hp0 hp1 (card_seedCoord_le_proxy n))

end RAF.Concrete
