import proofs.SparseLinearRAF.ProductiveProgram

namespace SparseLinearRAF
open RAF RAF.Polymer RAF.Concrete

theorem source_fire_card_le {n t : Nat} (A : Finset (Molecule n)) (r : Reaction n) :
    (fire (binaryPolymerCRS n t) A r).card ≤ A.card+3 := by
  have hl : ((binaryPolymerCRS n t).lhs r).card ≤ 2 := by
    simpa [binaryPolymerCRS] using Finset.card_insert_le (reactionLeft r) {reactionRight r}
  have hr : ((binaryPolymerCRS n t).rhs r).card = 1 := by simp [binaryPolymerCRS]
  have hs := Finset.card_union_le ((binaryPolymerCRS n t).lhs r) ((binaryPolymerCRS n t).rhs r)
  have ha := Finset.card_union_le A ((binaryPolymerCRS n t).lhs r ∪ (binaryPolymerCRS n t).rhs r)
  change (A ∪ ((binaryPolymerCRS n t).lhs r ∪ (binaryPolymerCRS n t).rhs r)).card ≤ A.card+3
  omega

theorem source_program_card_le {n t : Nat} {U : Finset (Reaction n)}
    {A B : Finset (Molecule n)} {rs : List (Reaction n)}
    (h : Program (binaryPolymerCRS n t) U A rs B) : B.card ≤ A.card+3*rs.length := by
  induction h with
  | nil => simp
  | @cons A B rs r hr hp tail ih =>
    have hh := source_fire_card_le (t:=t) A r
    simp only [List.length_cons]
    omega

theorem source_fire_length_le {n t L : Nat} (A : Finset (Molecule n)) (r : Reaction n)
    (hA : ∀ x ∈ A, molLength x ≤ L) (hp : Productive (binaryPolymerCRS n t) A r) :
    ∀ x ∈ fire (binaryPolymerCRS n t) A r, molLength x ≤ 2*L := by
  have hs : reactionProductLength r ≤ 2*L := by
    rcases hp.1 with hl | hr
    · have ha := hA (reactionLeft r) (hl (by simp [binaryPolymerCRS]))
      have hb := hA (reactionRight r) (hl (by simp [binaryPolymerCRS]))
      rw [molLength_reactionLeft] at ha
      rw [molLength_reactionRight] at hb
      have := reaction_length_add r
      omega
    · have ha := hA (reactionProduct r) (hr (by simp [binaryPolymerCRS]))
      rw [molLength_reactionProduct] at ha
      omega
  intro x hx
  simp only [fire,Finset.mem_union] at hx
  rcases hx with hx | hx | hx
  · have := hA x hx
    omega
  · have hh : x = reactionLeft r ∨ x = reactionRight r := by simpa [binaryPolymerCRS] using hx
    have := reaction_length_add r
    rcases hh with rfl | rfl
    · rw [molLength_reactionLeft]; omega
    · rw [molLength_reactionRight]; omega
  · have hh : x = reactionProduct r := by simpa [binaryPolymerCRS] using hx
    rw [hh,molLength_reactionProduct]
    exact hs

theorem source_program_length_le {n t L : Nat} {U : Finset (Reaction n)}
    {A B : Finset (Molecule n)} {rs : List (Reaction n)}
    (h : Program (binaryPolymerCRS n t) U A rs B)
    (hA : ∀ x ∈ A, molLength x ≤ L) :
    ∀ x ∈ B, molLength x ≤ L*2^rs.length := by
  induction h generalizing L with
  | nil => simpa using hA
  | @cons A B rs r hr hp tail ih =>
    have hh := ih (source_fire_length_le A r hA hp)
    intro x hx
    have he : (2*L)*2^rs.length = L*2^(r::rs).length := by
      simp only [List.length_cons,pow_succ]
      ring
    exact he ▸ hh x hx

end SparseLinearRAF
