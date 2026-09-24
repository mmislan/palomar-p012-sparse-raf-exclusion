import proofs.HordijkSteelThreshold.PolymerCounts
import proofs.HordijkSteelThreshold.Gateway

namespace SparseLinearRAF

open RAF.Polymer RAF.Concrete

abbrev ShortReaction (n L : Nat) := {r : Reaction n // reactionProductLength r ≤ L}

def restrictShortReaction {n L : Nat} (r : ShortReaction n L) : Reaction L :=
  ⟨⟨r.1.1.val, by have := r.2; unfold reactionProductLength at this; omega⟩, r.1.2⟩

theorem restrictShortReaction_injective {n L : Nat} :
    Function.Injective (@restrictShortReaction n L) := by
  intro a b hab
  apply Subtype.ext
  apply Sigma.ext
  · exact Fin.ext (congrArg (fun z : Reaction L => z.1.val) hab)
  · cases a with
    | mk a ha =>
      cases b with
      | mk b hb =>
        cases a with
        | mk ai ad =>
          cases b with
          | mk bi bd => simp_all [restrictShortReaction]

theorem short_reaction_card_le (n L : Nat) :
    Fintype.card (ShortReaction n L) ≤ Fintype.card (Reaction L) :=
  Fintype.card_le_of_injective restrictShortReaction restrictShortReaction_injective

abbrev ShortMolecule (n L : Nat) := {x : Molecule n // molLength x ≤ L}

def restrictShortMolecule {n L : Nat} (x : ShortMolecule n L) : Molecule L :=
  ⟨⟨x.1.1.val, by have := x.2; unfold molLength at this; omega⟩, x.1.2⟩

theorem restrictShortMolecule_injective {n L : Nat} :
    Function.Injective (@restrictShortMolecule n L) := by
  intro a b hab
  apply Subtype.ext
  apply Sigma.ext
  · exact Fin.ext (congrArg (fun z : Molecule L => z.1.val) hab)
  · cases a with
    | mk a ha =>
      cases b with
      | mk b hb =>
        cases a with
        | mk ai ad =>
          cases b with
          | mk bi bd => simp_all [restrictShortMolecule]

theorem short_molecule_card_le (n L : Nat) :
    Fintype.card (ShortMolecule n L) ≤ Fintype.card (Molecule L) :=
  Fintype.card_le_of_injective restrictShortMolecule restrictShortMolecule_injective

theorem source_reaction_count_five : Fintype.card (RAF.Polymer.Reaction 5) = 196 := by
  rw [HordijkSteelThreshold.card_reactions_exact (by omega)]
  norm_num

theorem source_gateway_count {n : Nat} (hn : 4 ≤ n) :
    Fintype.card (RAF.Concrete.PolymerSeedReaction n 2) = 36 :=
  HordijkSteelThreshold.card_concrete_gateway_binary_t2 hn

end SparseLinearRAF
