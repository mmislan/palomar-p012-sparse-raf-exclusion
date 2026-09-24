import proofs.SparseLinearRAF.BoundedRank
import proofs.SparseLinearRAF.SupportProbability

namespace SparseLinearRAF
open RAF RAF.Polymer RAF.Concrete

def HasLinearRAF (n t C : Nat) (ω : SparseSample (Molecule n) (Reaction n)) : Prop :=
  ∃ T : Finset (Reaction n), IsRevRAF (binaryPolymerCRS n t) (sparseCatalysis ω) T ∧ T.card ≤ C*n

def ActiveFood (n t : Nat) (ω : SparseSample (Molecule n) (Reaction n)) : Prop :=
  ∃ x ∈ binaryFood n t, ω (x,none)

theorem active_build_from_raf {n t : Nat} (ω : SparseSample (Molecule n) (Reaction n))
    (T : Finset (Reaction n)) (hT : IsRevRAF (binaryPolymerCRS n t) (sparseCatalysis ω) T) :
    ∃ K : Finset (Molecule n), K.Nonempty ∧ (∀ x ∈ K, ω (x,none)) ∧
      Build (binaryPolymerCRS n t) (sparseCatalysis ω) K T.card := by
  classical
  obtain ⟨K,_,_,U,hU,hcard,hfg,hcov,hreach⟩ := raf_implies_build (binaryPolymerCRS n t) (sparseCatalysis ω) T hT
  let A := K.filter (fun x => ω (x,none))
  have hcovA : Covers (sparseCatalysis ω) A U := by
    intro r hr
    obtain ⟨x,hx,hcat⟩ := hcov r hr
    exact ⟨x,Finset.mem_filter.mpr ⟨hx,hcat.1⟩,hcat⟩
  have hne : A.Nonempty := by
    obtain ⟨r,hr⟩ := hU
    obtain ⟨x,hx,_⟩ := hcovA r hr
    exact ⟨x,hx⟩
  exact ⟨A,hne,fun _ hx => (Finset.mem_filter.mp hx).2,U,hU,hcard,hfg,hcovA,
    fun x hx => hreach x (Finset.mem_filter.mp hx).1⟩

theorem linear_raf_decomposition (n t C K0 : Nat) (ω : SparseSample (Molecule n) (Reaction n))
    (h : HasLinearRAF n t C ω) :
    ActiveFood n t ω ∨ HasBoundedCoverRank n t K0 ω ∨
      ∃ m k, 0 < m ∧ m ≤ C*n ∧ K0 < k ∧ k ≤ Fintype.card (Molecule t)+3*C*n ∧
        HasProductiveCover n t m k ω := by
  classical
  obtain ⟨T,hT,hsize⟩ := h
  obtain ⟨K,hK,ha,hb⟩ := active_build_from_raf ω T hT
  by_cases hsmall : K.card ≤ K0
  · exact Or.inr (Or.inl ⟨K.card,Finset.card_pos.mpr hK,hsmall,K,rfl,ha,T.card,hb⟩)
  obtain ⟨U,hU,hcard,_hfg,hcov,hreach⟩ := hb
  obtain ⟨rs,B,hp,hsub,hB,hclosed⟩ := saturated_support_extraction (binaryPolymerCRS n t) U
  have hKB : K ⊆ B := by
    intro x hx
    obtain ⟨j,hj⟩ := hreach x hx
    exact hclosed j hj
  by_cases hempty : rs.toFinset = ∅
  · obtain ⟨x,hx⟩ := hK
    have hxB := hKB hx
    rw [hB,hempty] at hxB
    have hfood : x ∈ binaryFood n t := by
      simpa [supportUniverse, binaryPolymerCRS] using hxB
    exact Or.inl ⟨x,hfood,ha x hx⟩
  · have hm : 0 < rs.toFinset.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
    have hmb : rs.toFinset.card ≤ C*n := (Finset.card_le_card hsub).trans (hcard.trans hsize)
    have hKcard : K.card ≤ Fintype.card (Molecule t)+3*rs.toFinset.card := by
      apply (Finset.card_le_card hKB).trans
      rw [hB]
      exact source_supportUniverse_card_le n t rs.toFinset
    refine Or.inr (Or.inr ⟨rs.toFinset.card,K.card,hm,hmb,by omega,by nlinarith,?_⟩)
    refine ⟨⟨rs.toFinset,rfl,rs,B,hp,rfl⟩,K,?_,rfl,ha,?_⟩
    · exact hB ▸ hKB
    · intro r hr
      obtain ⟨x,hx,hcat⟩ := hcov r (hsub hr)
      exact ⟨x,hx,hcat.2⟩

end SparseLinearRAF
