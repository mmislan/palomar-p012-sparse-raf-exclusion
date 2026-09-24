import proofs.SparseLinearRAF.EnabledCounting

namespace SparseLinearRAF
open RAF RAF.Polymer RAF.Concrete

def endpoint {n : Nat} (r : Reaction n) (j : Fin 3) : Molecule n :=
  ![reactionLeft r,reactionRight r,reactionProduct r] j

abbrev AssemblyRef (n t m : Nat) := (binaryFood n t) ⊕ (Fin m × Fin 3)
abbrev AssemblyNode (n t m : Nat) :=
  (AssemblyRef n t m × AssemblyRef n t m) ⊕ (AssemblyRef n t m × Fin n)
abbrev AssemblyCode (n t m : Nat) := Fin m → AssemblyNode n t m

def refValue {n t m : Nat} (a : Fin m → Reaction n) : AssemblyRef n t m → Molecule n
  | .inl x => x.val
  | .inr z => endpoint (a z.1) z.2

def refBefore {n t m : Nat} (rank : Fin m → Nat) (i : Fin m) : AssemblyRef n t m → Prop
  | .inl _ => True
  | .inr z => rank z.1 < rank i

def nodeBefore {n t m : Nat} (rank : Fin m → Nat) (i : Fin m) : AssemblyNode n t m → Prop
  | .inl z => refBefore rank i z.1 ∧ refBefore rank i z.2
  | .inr z => refBefore rank i z.1

def nodeMatches {n t m : Nat} (a : Fin m → Reaction n) (i : Fin m) : AssemblyNode n t m → Prop
  | .inl z => refValue a z.1 = reactionLeft (a i) ∧ refValue a z.2 = reactionRight (a i)
  | .inr z => refValue a z.1 = reactionProduct (a i) ∧ z.2.val = (a i).2.2.val

def ValidAssembly {n t m : Nat} (a : Fin m → Reaction n) (c : AssemblyCode n t m) : Prop :=
  ∃ rank : Fin m → Nat, ∀ i, nodeBefore rank i (c i) ∧ nodeMatches a i (c i)

theorem refValue_eq_of_before {n t m : Nat} {a b : Fin m → Reaction n}
    {rank : Fin m → Nat} {i : Fin m} (h : ∀ j, rank j < rank i → a j = b j)
    (r : AssemblyRef n t m) (hr : refBefore rank i r) : refValue a r = refValue b r := by
  cases r with
  | inl x => rfl
  | inr z => simp only [refValue,h z.1 hr]

/-- The order is only a certificate: a code uniquely determines its assignment. -/
theorem validAssembly_unique {n t m : Nat} {a b : Fin m → Reaction n} {c : AssemblyCode n t m}
    (ha : ValidAssembly a c) (hb : ValidAssembly b c) : a = b := by
  obtain ⟨rank,ha⟩ := ha
  obtain ⟨_,hb⟩ := hb
  have hh : ∀ s, ∀ i, rank i = s → a i = b i := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro i hi
      have hprev : ∀ j, rank j < rank i → a j = b j := by
        intro j hj
        exact ih (rank j) (hi ▸ hj) j rfl
      have hA := ha i
      have hB := (hb i).2
      cases he : c i with
      | inl z =>
        rw [he] at hA hB
        apply reaction_factors_injective
        exact Prod.ext
          (hA.2.1.symm.trans ((refValue_eq_of_before hprev z.1 hA.1.1).trans hB.1))
          (hA.2.2.symm.trans ((refValue_eq_of_before hprev z.2 hA.1.2).trans hB.2))
      | inr z =>
        rw [he] at hA hB
        apply reaction_product_split_injective
        exact Prod.ext
          (hA.2.1.symm.trans ((refValue_eq_of_before hprev z.1 hA.1).trans hB.1))
          (hA.2.2.symm.trans hB.2)
  funext i
  exact hh (rank i) i rfl

theorem assemblyCode_card (n t m : Nat) :
    Fintype.card (AssemblyCode n t m) =
      (((binaryFood n t).card+3*m)^2+((binaryFood n t).card+3*m)*n)^m := by
  simp only [AssemblyCode,AssemblyNode,AssemblyRef,Fintype.card_fun,Fintype.card_sum,
    Fintype.card_prod,Fintype.card_fin,Fintype.card_coe]
  congr 1
  ring

abbrev EncodableAssignment (n t m : Nat) :=
  {a : Fin m → Reaction n // ∃ c : AssemblyCode n t m, ValidAssembly a c}

noncomputable instance encodableAssignmentFintype (n t m : Nat) : Fintype (EncodableAssignment n t m) :=
  Fintype.ofFinite _

theorem encodable_assignments_card_le (n t m : Nat) :
    Fintype.card (EncodableAssignment n t m) ≤
      (((binaryFood n t).card+3*m)^2+((binaryFood n t).card+3*m)*n)^m := by
  classical
  let encode : EncodableAssignment n t m → AssemblyCode n t m :=
    fun a => Classical.choose a.property
  have hinj : Function.Injective encode := by
    intro a b he
    apply Subtype.ext
    have ha : ValidAssembly a.val (encode a) := Classical.choose_spec a.property
    have hb : ValidAssembly b.val (encode b) := Classical.choose_spec b.property
    rw [← he] at hb
    exact validAssembly_unique ha hb
  exact (Fintype.card_le_of_injective encode hinj).trans_eq (assemblyCode_card n t m)

end SparseLinearRAF
