import proofs.SparseLinearRAF.ProductiveProgram

namespace SparseLinearRAF
open RAF RAF.Polymer RAF.Concrete

theorem reaction_factors_injective {n : Nat} :
    Function.Injective (fun r : Reaction n => (reactionLeft r,reactionRight r)) := by
  intro r s h
  have hl := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  have hll : reactionLeftLength r = reactionLeftLength s := by
    simpa only [molLength_reactionLeft] using congrArg molLength hl
  have hrl : reactionRightLength r = reactionRightLength s := by
    simpa only [molLength_reactionRight] using congrArg molLength hr
  have hpl : reactionProductLength r = reactionProductLength s := by
    have := reaction_length_add r
    have := reaction_length_add s
    omega
  have hdiv := congrArg (fun x : Molecule n => x.2.val) hl
  have hmod := congrArg (fun x : Molecule n => x.2.val) hr
  change r.2.1.val / 2^reactionRightLength r = s.2.1.val / 2^reactionRightLength s at hdiv
  change r.2.1.val % 2^reactionRightLength r = s.2.1.val % 2^reactionRightLength s at hmod
  rw [hrl] at hdiv hmod
  have hcode : r.2.1.val = s.2.1.val := by
    have ha := Nat.mod_add_div r.2.1.val (2^reactionRightLength s)
    have hb := Nat.mod_add_div s.2.1.val (2^reactionRightLength s)
    rw [hdiv,hmod] at ha
    omega
  have hidx : r.1 = s.1 := Fin.ext (by unfold reactionProductLength at hpl; omega)
  cases r with
  | mk ri rd =>
    cases s with
    | mk si sd =>
      dsimp only at hidx
      subst si
      have hd : rd = sd := Prod.ext (Fin.ext hcode) (Fin.ext (by
        unfold reactionLeftLength at hll
        dsimp only at hll
        omega))
      cases hd
      rfl

theorem enabled_ligation_card_le {n t : Nat} (A : Finset (Molecule n)) :
    Fintype.card {r : Reaction n // RevEnabledLhs (binaryPolymerCRS n t) A r} ≤ A.card^2 := by
  classical
  let g : {r : Reaction n // RevEnabledLhs (binaryPolymerCRS n t) A r} → A × A := fun r =>
    (⟨reactionLeft r.val,r.property (by simp [binaryPolymerCRS])⟩,
     ⟨reactionRight r.val,r.property (by simp [binaryPolymerCRS])⟩)
  have hg : Function.Injective g := by
    intro r s h
    apply Subtype.ext
    apply reaction_factors_injective
    exact Prod.ext (congrArg (fun z : A × A => z.1.val) h)
      (congrArg (fun z : A × A => z.2.val) h)
  have h := Fintype.card_le_of_injective g hg
  simpa [Fintype.card_prod,pow_two] using h

theorem reaction_product_split_injective {n : Nat} :
    Function.Injective (fun r : Reaction n => (reactionProduct r,r.2.2.val)) := by
  intro r s h
  have hp := congrArg Prod.fst h
  have hs := congrArg Prod.snd h
  have hi : r.1 = s.1 := congrArg (fun x : Molecule n => x.1) hp
  have hw : r.2.1.val = s.2.1.val := congrArg (fun x : Molecule n => x.2.val) hp
  cases r with
  | mk ri rd =>
    cases s with
    | mk si sd =>
      dsimp only at hi
      subst si
      have hd : rd = sd := Prod.ext (Fin.ext hw) (Fin.ext hs)
      cases hd
      rfl

theorem enabled_cleavage_card_le {n t L : Nat} (A : Finset (Molecule n))
    (hL : ∀ x ∈ A, molLength x ≤ L) :
    Fintype.card {r : Reaction n // RevEnabledRhs (binaryPolymerCRS n t) A r} ≤ A.card*L := by
  classical
  let g : {r : Reaction n // RevEnabledRhs (binaryPolymerCRS n t) A r} → A × Fin L := fun r =>
    (⟨reactionProduct r.val,r.property (by simp [binaryPolymerCRS])⟩,
     ⟨r.val.2.2.val,by
       have hh := hL (reactionProduct r.val) (r.property (by simp [binaryPolymerCRS]))
       have hh' := r.val.2.2.isLt
       change r.val.1.val+1 ≤ L at hh
       omega⟩)
  have hg : Function.Injective g := by
    intro r s h
    apply Subtype.ext
    apply reaction_product_split_injective
    exact Prod.ext (congrArg (fun z : A × Fin L => z.1.val) h)
      (congrArg (fun z : A × Fin L => z.2.val) h)
  have h := Fintype.card_le_of_injective g hg
  simpa [Fintype.card_prod] using h

theorem productive_channels_card_le {n t L : Nat} (U : Finset (Reaction n))
    (A : Finset (Molecule n)) (hL : ∀ x ∈ A, molLength x ≤ L) :
    (U.filter (Productive (binaryPolymerCRS n t) A)).card ≤ A.card^2+A.card*L := by
  classical
  let B := Finset.univ.filter (RevEnabledLhs (binaryPolymerCRS n t) A)
  let C := Finset.univ.filter (RevEnabledRhs (binaryPolymerCRS n t) A)
  have hs : U.filter (Productive (binaryPolymerCRS n t) A) ⊆ B ∪ C := by
    intro r hr
    rcases (Finset.mem_filter.mp hr).2.1 with hl | hh
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)
  have hb : B.card ≤ A.card^2 := by
    simpa only [B,← Fintype.card_subtype] using enabled_ligation_card_le (t:=t) A
  have hc : C.card ≤ A.card*L := by
    simpa only [C,← Fintype.card_subtype] using enabled_cleavage_card_le (t:=t) A hL
  exact (Finset.card_le_card hs).trans ((Finset.card_union_le B C).trans (Nat.add_le_add hb hc))

end SparseLinearRAF
