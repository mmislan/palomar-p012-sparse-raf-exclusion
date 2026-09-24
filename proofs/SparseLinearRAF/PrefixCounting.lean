import proofs.SparseLinearRAF.EnabledCounting
import proofs.SparseLinearRAF.ProgramBounds
import proofs.SparseLinearRAF.PrefixFamily
import proofs.SparseLinearRAF.Source

namespace SparseLinearRAF
open RAF RAF.Polymer RAF.Concrete

def branchBound (f t j : Nat) : Nat := (f+3*j)^2+(f+3*j)*(t*2^j)

def prefixBound (f t j : Nat) : Nat → Nat
  | 0 => 1
  | d+1 => branchBound f t j * prefixBound f t (j+1) d

theorem prefixes_card_le {n t : Nat} (U : Finset (Reaction n))
    (f j d : Nat) (A : Finset (Molecule n)) (hc : A.card ≤ f+3*j)
    (hL : ∀ x ∈ A, molLength x ≤ t*2^j) :
    (prefixes (binaryPolymerCRS n t) U A d).card ≤ prefixBound f t j d := by
  classical
  induction d generalizing j A with
  | zero => simp [prefixes,prefixBound]
  | succ d ih =>
    let V := U.filter (Productive (binaryPolymerCRS n t) A)
    have hv : V.card ≤ branchBound f t j := by
      apply (productive_channels_card_le U A hL).trans
      unfold branchBound
      exact Nat.add_le_add (Nat.pow_le_pow_left hc 2) (Nat.mul_le_mul_right _ hc)
    have htail (r : Reaction n) (hr : r ∈ V) :
        (prefixes (binaryPolymerCRS n t) U (fire (binaryPolymerCRS n t) A r) d).card ≤
          prefixBound f t (j+1) d := by
      have hp := (Finset.mem_filter.mp hr).2
      apply ih
      · have hh := source_fire_card_le (t:=t) A r
        omega
      · have hh := source_fire_length_le A r hL hp
        intro x hx
        have he : 2*(t*2^j) = t*2^(j+1) := by rw [pow_succ]; ring
        exact he ▸ hh x hx
    calc
      (prefixes (binaryPolymerCRS n t) U A (d+1)).card ≤
          ∑ r ∈ V, ((prefixes (binaryPolymerCRS n t) U (fire (binaryPolymerCRS n t) A r) d).image
            (List.cons r)).card := by
              have he : prefixes (binaryPolymerCRS n t) U A (d+1) = V.biUnion
                  (fun r => (prefixes (binaryPolymerCRS n t) U
                    (fire (binaryPolymerCRS n t) A r) d).image (List.cons r)) := by
                ext rs
                simp only [prefixes,V,Finset.mem_biUnion,Finset.mem_image]
              rw [he]
              exact Finset.card_biUnion_le
      _ ≤ ∑ r ∈ V, prefixBound f t (j+1) d := by
        apply Finset.sum_le_sum
        intro r hr
        exact Finset.card_image_le.trans (htail r hr)
      _ = V.card * prefixBound f t (j+1) d := by simp
      _ ≤ branchBound f t j * prefixBound f t (j+1) d := Nat.mul_le_mul_right _ hv
      _ = prefixBound f t j (d+1) := rfl

def shallowBound (f t d : Nat) : Nat :=
  ∑ j ∈ Finset.range d, prefixBound f t 0 j * (f+3*j)

theorem shallow_card_le {n t : Nat} (U : Finset (Reaction n)) (f d : Nat)
    (A : Finset (Molecule n)) (hc : A.card ≤ f) (hL : ∀ x ∈ A, molLength x ≤ t) :
    (shallowUniverse (binaryPolymerCRS n t) U A d).card ≤ shallowBound f t d := by
  classical
  unfold shallowUniverse shallowBound
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro j hj
  have hpref : (prefixes (binaryPolymerCRS n t) U A j).card ≤ prefixBound f t 0 j := by
    apply prefixes_card_le U f 0 j A
    · simpa using hc
    · simpa using hL
  calc
    ((prefixes (binaryPolymerCRS n t) U A j).biUnion (runProgram (binaryPolymerCRS n t) A)).card ≤
        ∑ rs ∈ prefixes (binaryPolymerCRS n t) U A j, (runProgram (binaryPolymerCRS n t) A rs).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _rs ∈ prefixes (binaryPolymerCRS n t) U A j, (f+3*j) := by
      apply Finset.sum_le_sum
      intro rs hrs
      have hp := mem_prefixes_program hrs
      have hh := source_program_card_le hp.1
      rw [hp.2] at hh
      omega
    _ = (prefixes (binaryPolymerCRS n t) U A j).card * (f+3*j) := by simp
    _ ≤ prefixBound f t 0 j * (f+3*j) := Nat.mul_le_mul_right _ hpref

theorem source_food_card_le (n t : Nat) :
    (binaryFood n t).card ≤ Fintype.card (Molecule t) := by
  simpa only [ShortMolecule,Fintype.card_subtype,binaryFood] using short_molecule_card_le n t

theorem source_prefixes_card_le (n t d : Nat) :
    (prefixes (binaryPolymerCRS n t) Finset.univ (binaryFood n t) d).card ≤
      prefixBound (Fintype.card (Molecule t)) t 0 d := by
  apply prefixes_card_le Finset.univ (Fintype.card (Molecule t)) 0 d (binaryFood n t)
  · simpa using source_food_card_le n t
  · intro x hx
    simpa [binaryFood] using hx

theorem source_shallow_card_le (n t d : Nat) :
    (shallowUniverse (binaryPolymerCRS n t) Finset.univ (binaryFood n t) d).card ≤
      shallowBound (Fintype.card (Molecule t)) t d := by
  apply shallow_card_le Finset.univ (Fintype.card (Molecule t)) d (binaryFood n t)
    (source_food_card_le n t)
  intro x hx
  simpa [binaryFood] using hx

end SparseLinearRAF
