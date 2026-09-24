import proofs.SparseLinearRAF.ProgramEncoding

namespace SparseLinearRAF
open RAF RAF.Polymer RAF.Concrete

abbrev SupportFamily (n t m : Nat) :=
  {S : Finset (Reaction n) // S.card = m ∧ ConstructibleSupport n t S}

noncomputable instance supportFamilyFintype (n t m : Nat) : Fintype (SupportFamily n t m) :=
  Fintype.ofFinite _

/-- Count arbitrary labelings, rather than assuming all orders are productive. -/
theorem support_count_mul_factorial_le (n t m : Nat) (hm : 0 < m) :
    Fintype.card (SupportFamily n t m) * m.factorial ≤
      (((binaryFood n t).card+3*m)^2+((binaryFood n t).card+3*m)*n)^m := by
  classical
  let base (S : SupportFamily n t m) : Fin m ≃ S.val :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin,Fintype.card_coe] using S.property.1.symm)
  let assign (z : SupportFamily n t m × Equiv.Perm (Fin m)) : Fin m → Reaction n :=
    fun i => (base z.1 (z.2 i)).val
  have ha (z : SupportFamily n t m × Equiv.Perm (Fin m)) : Function.Injective (assign z) := by
    intro i j h
    exact z.2.injective ((base z.1).injective (Subtype.ext h))
  have hrange (z : SupportFamily n t m × Equiv.Perm (Fin m)) :
      Finset.univ.image (assign z) = z.1.val := by
    ext r
    constructor
    · intro h
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
      exact (base z.1 (z.2 i)).property
    · intro h
      obtain ⟨j,hj⟩ := (base z.1).surjective ⟨r,h⟩
      obtain ⟨i,hi⟩ := z.2.surjective j
      refine Finset.mem_image.mpr ⟨i,Finset.mem_univ _,?_⟩
      dsimp only [assign]
      rw [hi,hj]
  let encode : SupportFamily n t m × Equiv.Perm (Fin m) → EncodableAssignment n t m := fun z =>
    ⟨assign z,constructible_assignment_encodable hm (assign z) (ha z)
      (by rw [hrange z]; exact z.1.property.2)⟩
  have hinj : Function.Injective encode := by
    rintro ⟨S,σ⟩ ⟨T,τ⟩ h
    have he : assign (S,σ) = assign (T,τ) := congrArg Subtype.val h
    have hs : S = T := by
      apply Subtype.ext
      rw [← hrange (S,σ),← hrange (T,τ),he]
    subst T
    have hp : σ = τ := by
      apply Equiv.ext
      intro i
      apply (base S).injective
      apply Subtype.ext
      exact congrFun he i
    cases hp
    rfl
  have hh := (Fintype.card_le_of_injective encode hinj).trans (encodable_assignments_card_le n t m)
  simpa only [Fintype.card_prod,Fintype.card_perm,Fintype.card_fin] using hh

end SparseLinearRAF
