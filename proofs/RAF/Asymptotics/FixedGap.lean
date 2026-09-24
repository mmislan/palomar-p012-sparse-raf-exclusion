import proofs.RAF.Conjecture.SeedBound

namespace RAF.Asymptotics

open Filter Topology

/-- A positive limiting seed-closed mass is incompatible with RAF probability
converging to one. -/
theorem fixed_gap_prevents_tendsto_one
    (rafProbability seedClosedProbability : Nat → ℝ) (delta : ℝ)
    (hdelta : 0 < delta)
    (hbound : ∀ n, rafProbability n + seedClosedProbability n ≤ 1)
    (hclosed : Tendsto seedClosedProbability atTop (𝓝 delta)) :
    ¬ Tendsto rafProbability atTop (𝓝 1) := by
  intro hraf
  have hsum : Tendsto (fun n => rafProbability n + seedClosedProbability n)
      atTop (𝓝 (1 + delta)) := hraf.add hclosed
  have hle : 1 + delta ≤ 1 := le_of_tendsto hsum (Filter.Eventually.of_forall hbound)
  linarith

theorem eventual_fixed_gap_prevents_tendsto_one
    (rafProbability seedClosedProbability : Nat → ℝ) (delta : ℝ)
    (hdelta : 0 < delta)
    (hbound : ∀ n, rafProbability n + seedClosedProbability n ≤ 1)
    (hclosed : ∀ᶠ n in atTop, delta ≤ seedClosedProbability n) :
    ¬ Tendsto rafProbability atTop (𝓝 1) := by
  intro hraf
  have hrafLower : ∀ᶠ n in atTop, 1 - delta / 2 < rafProbability n :=
    (tendsto_order.1 hraf).1 (1 - delta / 2) (by linarith)
  have hfalse : ∀ᶠ _n : Nat in atTop, False := by
    filter_upwards [hrafLower, hclosed] with n hr hc
    linarith [hbound n]
  exact (Filter.Eventually.exists hfalse).elim (fun _ h => h)

/-- The minimum asymptotic lemma: if the number of seed coordinates tends to
infinity and their Bernoulli rate is eventually at most `C/N`, the all-absent
probability is eventually bounded below by a fixed positive constant. -/
theorem bernoulli_absent_eventually_pos
    (p : Nat → ℝ) (pairCount : Nat → Nat) (C : ℝ)
    (hcount : Tendsto pairCount atTop atTop)
    (hrate : ∀ᶠ n in atTop,
      0 ≤ 1 - C / (pairCount n : ℝ) ∧ p n ≤ C / (pairCount n : ℝ)) :
    ∃ delta > 0, ∀ᶠ n in atTop, delta ≤ (1 - p n) ^ pairCount n := by
  have hbenchmark : Tendsto
      (fun n => (1 - C / (pairCount n : ℝ)) ^ pairCount n)
      atTop (𝓝 (Real.exp (-C))) := by
    simpa [Function.comp_def, sub_eq_add_neg, neg_div] using
      (Real.tendsto_one_add_div_pow_exp (-C)).comp hcount
  let delta := Real.exp (-C) / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hlower : ∀ᶠ n in atTop,
      delta < (1 - C / (pairCount n : ℝ)) ^ pairCount n :=
    (tendsto_order.1 hbenchmark).1 delta (by
      dsimp [delta]
      nlinarith [Real.exp_pos (-C)])
  refine ⟨delta, hdelta, ?_⟩
  filter_upwards [hrate, hlower] with n hn hstrict
  exact le_trans (le_of_lt hstrict)
    (pow_le_pow_left₀ hn.1 (by linarith [hn.2]) (pairCount n))

end RAF.Asymptotics
