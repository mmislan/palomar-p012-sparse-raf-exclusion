import proofs.SparseLinearRAF.PrefixFamily
import proofs.SparseLinearRAF.ProgramEncoding

namespace SparseLinearRAF
open RAF RAF.Concrete

variable {M R : Type*} [DecidableEq M]

theorem exists_saturated_program [Fintype M] (Q : ReversibleCRS M R)
    (U : Finset R) (A : Finset M) :
    ∃ rs B, Program Q U A rs B ∧ ∀ r ∈ U, ¬ Productive Q B r := by
  classical
  generalize he : Fintype.card M - A.card = d
  induction d using Nat.strong_induction_on generalizing A with
  | h d ih =>
    by_cases hs : ∀ r ∈ U, ¬ Productive Q A r
    · exact ⟨[],A,Program.nil _,hs⟩
    · push Not at hs
      obtain ⟨r,hr,hp⟩ := hs
      have hlt : Fintype.card M - (fire Q A r).card < d := by
        have h1 := hp.card_fire_gt
        have h2 := Finset.card_le_univ (fire Q A r)
        omega
      obtain ⟨rs,B,ht,hstop⟩ := ih _ hlt (fire Q A r) rfl
      exact ⟨r::rs,B,Program.cons hr hp ht,hstop⟩

theorem Program.change_allowed {Q : ReversibleCRS M R} {U V : Finset R}
    {A B : Finset M} {rs : List R} (hp : Program Q U A rs B)
    (hV : ∀ r ∈ rs, r ∈ V) : Program Q V A rs B := by
  induction hp with
  | nil => exact Program.nil _
  | cons _ hp tail ih =>
    exact Program.cons (hV _ (by simp)) hp (ih (fun r hr => hV r (by simp [hr])))

def supportUniverse (Q : ReversibleCRS M R) (S : Finset R) : Finset M :=
  Q.food ∪ S.biUnion (fun r => Q.lhs r ∪ Q.rhs r)

theorem Program.final_eq_endpoints [DecidableEq R] {Q : ReversibleCRS M R} {U : Finset R}
    {A B : Finset M} {rs : List R} (hp : Program Q U A rs B) :
    B = A ∪ rs.toFinset.biUnion (fun r => Q.lhs r ∪ Q.rhs r) := by
  classical
  induction hp with
  | nil => simp
  | @cons A B rs r hr hp tail ih =>
    rw [ih]
    ext x
    simp only [fire,Finset.mem_union,List.toFinset_cons,Finset.mem_biUnion,Finset.mem_insert]
    constructor
    · rintro ((hx | hx) | ⟨s,hs,hxs⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨r,Or.inl rfl,hx⟩
      · exact Or.inr ⟨s,Or.inr hs,hxs⟩
    · rintro (hx | ⟨s,hs,hxs⟩)
      · exact Or.inl (Or.inl hx)
      · rcases hs with rfl | hs
        · exact Or.inl (Or.inr hxs)
        · exact Or.inr ⟨s,hs,hxs⟩

theorem saturated_support_extraction [DecidableEq R] [Fintype M] (Q : ReversibleCRS M R) (U : Finset R) :
    ∃ rs B, Program Q rs.toFinset Q.food rs B ∧ rs.toFinset ⊆ U ∧
      B = supportUniverse Q rs.toFinset ∧ ∀ j, revClosureAt Q U j ⊆ B := by
  classical
  obtain ⟨rs,B,hp,hs⟩ := exists_saturated_program Q U Q.food
  refine ⟨rs,B,hp.change_allowed (fun r hr => List.mem_toFinset.mpr hr),?_,hp.final_eq_endpoints,?_⟩
  · intro r hr
    exact hp.mem_allowed r (List.mem_toFinset.mp hr)
  · exact closure_subset_of_no_productive Q U B hp.initial_subset_final hs

end SparseLinearRAF
