import proofs.SparseLinearRAF.RAFReduction
import proofs.SparseLinearRAF.LargeRankEstimate

namespace SparseLinearRAF
open RAF RAF.Polymer RAF.Concrete MeasureTheory ProbabilityTheory unitInterval Filter Topology

noncomputable def linearRAFProbability (n t C : Nat) (lambda : ℝ) : ℝ :=
  (sparseMeasure (Molecule n) (Reaction n) (activityParameter n lambda) (channelParameter n)
    {ω | HasLinearRAF n t C ω}).toReal

theorem linearRAFProbability_bound (n t C K : Nat) (lambda b : ℝ) (hb : 0 ≤ b)
    (hlarge : ∀ m k, 0 < m → m ≤ C*n → K < k → productiveCoverProbability n t m k lambda ≤ b) :
    linearRAFProbability n t C lambda ≤
      (Fintype.card (Molecule t) : ℝ)*(activityParameter n lambda : ℝ) +
      boundedCoverRankProbability n t K lambda +
      ((C*n : Nat) : ℝ)*((Fintype.card (Molecule t)+3*C*n : Nat) : ℝ)*b := by
  classical
  let μ := sparseMeasure (Molecule n) (Reaction n) (activityParameter n lambda) (channelParameter n)
  let A := {ω : SparseSample (Molecule n) (Reaction n) | ActiveFood n t ω}
  let B := {ω : SparseSample (Molecule n) (Reaction n) | HasBoundedCoverRank n t K ω}
  let J := Fin (C*n) × Fin (Fintype.card (Molecule t)+3*C*n)
  let E := fun z : J => {ω : SparseSample (Molecule n) (Reaction n) |
    K < z.2.val+1 ∧ HasProductiveCover n t (z.1.val+1) (z.2.val+1) ω}
  have hs : {ω | HasLinearRAF n t C ω} ⊆ (A ∪ B) ∪ ⋃ z, E z := by
    intro ω hω
    rcases linear_raf_decomposition n t C K ω hω with hA | hB | ⟨m,k,hm,hmb,hk,hkb,hp⟩
    · exact Or.inl (Or.inl hA)
    · exact Or.inl (Or.inr hB)
    · have hk1 : 0 < k := by omega
      refine Or.inr (Set.mem_iUnion.mpr ⟨(⟨m-1,by omega⟩,⟨k-1,by omega⟩),?_⟩)
      simp only [E]
      simpa [Nat.sub_add_cancel hm, Nat.sub_add_cancel hk1] using
        (And.intro hk hp)
  have hA : μ A ≤ (Fintype.card (Molecule t) : ENNReal)*(toNNReal (activityParameter n lambda) : ENNReal) := by
    let F := fun x : binaryFood n t => {ω : SparseSample (Molecule n) (Reaction n) | ω (x.val,none)}
    have hsub : A ⊆ ⋃ x, F x := by
      rintro ω ⟨x,hx,hactive⟩
      exact Set.mem_iUnion.mpr ⟨⟨x,hx⟩,hactive⟩
    have hh := (measure_mono hsub).trans (measure_exists_le_card μ F
      (toNNReal (activityParameter n lambda) : ENNReal) (fun x =>
      (sparse_coordinate_probability (R:=Reaction n) (activityParameter n lambda) (channelParameter n) (x.val,none)).le))
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ zero_le
    simpa only [Fintype.card_coe] using (show ((binaryFood n t).card : ENNReal) ≤ Fintype.card (Molecule t) by exact_mod_cast source_food_card_le n t)
  have hE : μ (⋃ z, E z) ≤ ((C*n : Nat) : ENNReal)*
      ((Fintype.card (Molecule t)+3*C*n : Nat) : ENNReal)*ENNReal.ofReal b := by
    have hh : ∀ z : J, μ (E z) ≤ ENNReal.ofReal b := by
      intro z
      by_cases hk : K < z.2.val+1
      · have hs' : E z ⊆ {ω | HasProductiveCover n t (z.1.val+1) (z.2.val+1) ω} := fun _ h => h.2
        apply (measure_mono hs').trans
        apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hb).mpr
        exact hlarge _ _ (by omega) (by have := z.1.isLt; omega) hk
      · have he : E z = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun _ h => hk h.1)
        rw [he,measure_empty]
        exact zero_le
    have hh' := measure_exists_le_card μ E (ENNReal.ofReal b) hh
    simpa only [J,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul] using hh'
  have hh := (measure_mono hs).trans ((measure_union_le _ _).trans
    (add_le_add ((measure_union_le _ _).trans (add_le_add hA le_rfl)) hE))
  have hreal := ENNReal.toReal_mono (by finiteness) hh
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (measure_ne_top μ B)] at hreal
  simpa only [linearRAFProbability,boundedCoverRankProbability,μ,B,ENNReal.toReal_mul,
    ENNReal.toReal_natCast,ENNReal.coe_toReal,unitInterval.coe_toNNReal,ENNReal.toReal_ofReal hb] using hreal

theorem sparse_linear_raf_probability_tendsto_zero (t C : Nat) {lambda : ℝ} (hl : 0 ≤ lambda) :
    Tendsto (fun n => linearRAFProbability n t C lambda) atTop (𝓝 0) := by
  obtain ⟨K,hK⟩ := large_rank_uniform_estimate t C hl
  let f : ℝ := Fintype.card (Molecule t)
  have ht1 := (tendsto_pow_const_mul_const_pow_of_lt_one 1 (by norm_num : (0:ℝ)≤3/4)
    (by norm_num : (3/4:ℝ)<1)).const_mul ((C:ℝ)*f)
  have ht2 := (tendsto_pow_const_mul_const_pow_of_lt_one 2 (by norm_num : (0:ℝ)≤3/4)
    (by norm_num : (3/4:ℝ)<1)).const_mul (3*(C:ℝ)^2)
  have htail : Tendsto (fun n : Nat => ((C*n : Nat):ℝ)*
      ((Fintype.card (Molecule t)+3*C*n : Nat):ℝ)*(3/4:ℝ)^n) atTop (𝓝 0) := by
    convert ht1.add ht2 using 1
    · funext n
      push_cast
      dsimp [f]
      ring
    · simp only [mul_zero,add_zero]
  have ht := (((activity_tendsto_zero hl).const_mul f).add
    (bounded_cover_rank_probability_tendsto_zero t K hl)).add htail
  apply squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg)) ?_
    (by simpa only [mul_zero,add_zero] using ht)
  filter_upwards [hK] with n hn
  exact linearRAFProbability_bound n t C K lambda ((3/4:ℝ)^n) (by positivity) hn

end SparseLinearRAF
