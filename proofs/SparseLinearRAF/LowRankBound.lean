import proofs.SparseLinearRAF.PrefixCounting
import proofs.SparseLinearRAF.CoverProbability
import proofs.SparseLinearRAF.CatalystRank
import proofs.SparseLinearRAF.SelfConstructionBound

namespace SparseLinearRAF
open RAF RAF.Polymer RAF.Concrete MeasureTheory ProbabilityTheory unitInterval

def HasCoverRank (n t k : Nat) (ω : SparseSample (Molecule n) (Reaction n)) : Prop :=
  ∃ K : Finset (Molecule n), K.card = k ∧ (∀ x ∈ K, ω (x,none)) ∧
    ∃ m, Build (binaryPolymerCRS n t) (sparseCatalysis ω) K m

theorem build_far_prefix {n t m d : Nat} (ω : SparseSample (Molecule n) (Reaction n))
    (K : Finset (Molecule n)) (hne : K.Nonempty)
    (hbuild : Build (binaryPolymerCRS n t) (sparseCatalysis ω) K m)
    (hfar : ∀ x ∈ K, x ∉ shallowUniverse (binaryPolymerCRS n t) Finset.univ (binaryFood n t) d) :
    ∃ rs ∈ prefixes (binaryPolymerCRS n t) Finset.univ (binaryFood n t) d,
      ∀ r ∈ rs.toFinset, ∃ x ∈ K, ω (x,some r) := by
  obtain ⟨T,_,_,_,hcov,hreach⟩ := hbuild
  obtain ⟨x,hxK⟩ := hne
  obtain ⟨j,hj⟩ := hreach x hxK
  obtain ⟨rs,B,hp,hlen⟩ := exists_program_length (binaryPolymerCRS n t) T x j hj d (by
    intro rs B hp hs hxB
    have hu := hp.mono (Finset.subset_univ T)
    exact hfar x hxK (hu.final_subset_shallow hs hxB))
  refine ⟨rs,?_,?_⟩
  · rw [← hlen]
    exact (hp.mono (Finset.subset_univ T)).mem_prefixes
  · intro r hr
    obtain ⟨y,hy,hcat⟩ := hcov r (hp.mem_allowed r (List.mem_toFinset.mp hr))
    exact ⟨y,hy,hcat.2⟩

/-- Finite low-rank bound over the literal source. `d` is freely chosen. -/
theorem cover_rank_probability_le (n t k d : Nat) (hk : 0 < k) (p q : I) :
    sparseMeasure (Molecule n) (Reaction n) p q {ω | HasCoverRank n t k ω} ≤
      ((shallowUniverse (binaryPolymerCRS n t) Finset.univ (binaryFood n t) d).card : ENNReal) *
        (toNNReal p : ENNReal) +
      ((Fintype.card (Molecule n)).choose k : ENNReal) *
      ((prefixes (binaryPolymerCRS n t) Finset.univ (binaryFood n t) d).card : ENNReal) *
      ((k : ENNReal)^d * ((toNNReal p : ENNReal)^k * (toNNReal q : ENNReal)^d)) := by
  classical
  let Q := binaryPolymerCRS n t
  let H := shallowUniverse Q Finset.univ (binaryFood n t) d
  let P := prefixes Q Finset.univ (binaryFood n t) d
  let Ks := (Finset.univ : Finset (Molecule n)).powersetCard k
  let μ := sparseMeasure (Molecule n) (Reaction n) p q
  let c : ENNReal := (k : ENNReal)^d*((toNNReal p : ENNReal)^k*(toNNReal q : ENNReal)^d)
  let A := fun x : H => {ω : SparseSample (Molecule n) (Reaction n) | ω (x.val,none)}
  let E := fun (z : Ks × P) => {ω : SparseSample (Molecule n) (Reaction n) |
    (∀ x ∈ z.1.val, ω (x,none)) ∧ ∀ r ∈ z.2.val.toFinset, ∃ x ∈ z.1.val, ω (x,some r)}
  have hsub : {ω | HasCoverRank n t k ω} ⊆ (⋃ x, A x) ∪ (⋃ z, E z) := by
    rintro ω ⟨K,hcard,ha,m,hb⟩
    by_cases hh : ∃ x ∈ K, x ∈ H
    · obtain ⟨x,hx,hH⟩ := hh
      exact Or.inl (Set.mem_iUnion.mpr ⟨⟨x,hH⟩,ha x hx⟩)
    · have hfar : ∀ x ∈ K, x ∉ H := by
        intro x hx hH
        exact hh ⟨x,hx,hH⟩
      have hne : K.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨rs,hrs,hcov⟩ := build_far_prefix ω K hne hb hfar
      have hK : K ∈ Ks := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hcard⟩
      exact Or.inr (Set.mem_iUnion.mpr ⟨(⟨K,hK⟩,⟨rs,hrs⟩),ha,hcov⟩)
  have hA : μ (⋃ x, A x) ≤ (H.card : ENNReal)*(toNNReal p : ENNReal) := by
    have hxprob : ∀ x : H, μ (A x) ≤ (toNNReal p : ENNReal) := by
      intro x
      exact le_of_eq (sparse_coordinate_probability p q (x.val,none))
    simpa only [Fintype.card_coe] using measure_exists_le_card μ A (toNNReal p) hxprob
  have hE : μ (⋃ z, E z) ≤ (Ks.card : ENNReal)*(P.card : ENNReal)*c := by
    have hu : ∀ z : Ks × P, μ (E z) ≤ c := by
      intro z
      have hk' : z.1.val.card = k := (Finset.mem_powersetCard.mp z.1.property).2
      have hp := mem_prefixes_program z.2.property
      have hd : z.2.val.toFinset.card = d := by rw [List.toFinset_card_of_nodup hp.1.nodup,hp.2]
      simpa only [μ,E,c,hk',hd] using active_cover_probability_le p q z.1.val z.2.val.toFinset
    have hh := measure_exists_le_card μ E c hu
    simpa only [Fintype.card_prod,Fintype.card_coe,Nat.cast_mul] using hh
  have hh := (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hA hE))
  simpa only [H,P,Ks,μ,c,Q,Finset.card_powersetCard,Finset.card_univ] using hh

end SparseLinearRAF
