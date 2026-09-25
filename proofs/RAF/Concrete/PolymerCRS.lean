import proofs.RAF.Polymer.Reactions

namespace RAF.Concrete

open RAF.Polymer

/-- Length of an ambient binary polymer. -/
def molLength {n : Nat} (x : Molecule n) : Nat := x.1.val + 1

/-- A length-indexed word viewed as an ambient molecule. -/
def moleculeOfCode {n L : Nat} (hL : 1 ≤ L) (hLn : L ≤ n)
    (x : Word L) : Molecule n :=
  let hlt : L - 1 < n := by omega
  let hidx : L - 1 + 1 = L := Nat.sub_add_cancel hL
  ⟨⟨L - 1, hlt⟩, Fin.cast (congrArg (fun k => 2 ^ k) hidx.symm) x⟩

/-- Concatenate the bit patterns of two molecules.  `finProdFinEquiv` is the
standard mixed-radix bijection, here with radices `2^|u|` and `2^|v|`. -/
def concatCode {n : Nat} (u v : Molecule n) : Word (molLength u + molLength v) :=
  Fin.cast ((pow_add 2 (molLength u) (molLength v)).symm)
    (finProdFinEquiv (u.2, v.2))

def concatMolecule {n : Nat} (u v : Molecule n)
    (h : molLength u + molLength v ≤ n) : Molecule n :=
  moleculeOfCode (by simp [molLength]; omega) h (concatCode u v)

@[simp] theorem molLength_moleculeOfCode {n L : Nat} (hL : 1 ≤ L) (hLn : L ≤ n)
    (x : Word L) : molLength (moleculeOfCode hL hLn x) = L := by
  simp [molLength, moleculeOfCode]
  omega

def reactionProductLength {n : Nat} (r : Reaction n) : Nat := r.1.val + 1
def reactionLeftLength {n : Nat} (r : Reaction n) : Nat := r.2.2.val + 1
def reactionRightLength {n : Nat} (r : Reaction n) : Nat :=
  r.1.val - r.2.2.val

theorem reaction_length_add {n : Nat} (r : Reaction n) :
    reactionLeftLength r + reactionRightLength r = reactionProductLength r := by
  dsimp [reactionLeftLength, reactionRightLength, reactionProductLength]
  omega

theorem reaction_left_pos {n : Nat} (r : Reaction n) :
    1 ≤ reactionLeftLength r := by simp [reactionLeftLength]

theorem reaction_right_pos {n : Nat} (r : Reaction n) :
    1 ≤ reactionRightLength r := by
  dsimp [reactionRightLength]
  omega

theorem reaction_product_le {n : Nat} (r : Reaction n) :
    reactionProductLength r ≤ n := by
  dsimp [reactionProductLength]
  omega

theorem reaction_pow_split {n : Nat} (r : Reaction n) :
    2 ^ (r.1.val + 1) =
      2 ^ reactionLeftLength r * 2 ^ reactionRightLength r := by
  rw [← pow_add, reaction_length_add]
  rfl

/-- Split the encoded product at its recorded split position. -/
def splitCodes {n : Nat} (r : Reaction n) :
    Word (reactionLeftLength r) × Word (reactionRightLength r) :=
  (finProdFinEquiv).symm
    (Fin.cast (reaction_pow_split r) r.2.1)

def reactionLeft {n : Nat} (r : Reaction n) : Molecule n :=
  moleculeOfCode (reaction_left_pos r)
    (by linarith [reaction_product_le r, reaction_length_add r]) (splitCodes r).1

def reactionRight {n : Nat} (r : Reaction n) : Molecule n :=
  moleculeOfCode (reaction_right_pos r)
    (by linarith [reaction_product_le r, reaction_length_add r]) (splitCodes r).2

def reactionProduct {n : Nat} (r : Reaction n) : Molecule n :=
  ⟨r.1, r.2.1⟩

@[simp] theorem molLength_reactionLeft {n : Nat} (r : Reaction n) :
    molLength (reactionLeft r) = reactionLeftLength r := by
  simp [reactionLeft]

@[simp] theorem molLength_reactionRight {n : Nat} (r : Reaction n) :
    molLength (reactionRight r) = reactionRightLength r := by
  simp [reactionRight]

@[simp] theorem molLength_reactionProduct {n : Nat} (r : Reaction n) :
    molLength (reactionProduct r) = reactionProductLength r := rfl

/-- The splitting code is inverse to binary concatenation at the code level. -/
theorem split_concat_code {n : Nat} (r : Reaction n) :
    finProdFinEquiv (splitCodes r) =
      Fin.cast (reaction_pow_split r) r.2.1 := by
  exact Equiv.apply_symm_apply finProdFinEquiv _

/-- A reversible CRS records the two sides of each base reaction. Catalysis is
indexed by the base reaction, so one sampled coordinate catalyzes both
directions, exactly as in the paper's reaction convention. -/
structure ReversibleCRS (M R : Type*) [DecidableEq M] where
  lhs : R → Finset M
  rhs : R → Finset M
  food : Finset M

def RevEnabledLhs {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (available : Finset M) (r : R) : Prop :=
  Q.lhs r ⊆ available

def RevEnabledRhs {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (available : Finset M) (r : R) : Prop :=
  Q.rhs r ⊆ available

instance revEnabledLhsDecidable {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (available : Finset M) (r : R) :
    Decidable (RevEnabledLhs Q available r) := by
  unfold RevEnabledLhs
  infer_instance

instance revEnabledRhsDecidable {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (available : Finset M) (r : R) :
    Decidable (RevEnabledRhs Q available r) := by
  unfold RevEnabledRhs
  infer_instance

def revClosureStep {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) (available : Finset M) : Finset M :=
  available ∪ S.biUnion (fun r =>
    (if RevEnabledLhs Q available r then Q.rhs r else ∅) ∪
    (if RevEnabledRhs Q available r then Q.lhs r else ∅))

def revClosureAt {M R : Type*} [DecidableEq M]
    (Q : ReversibleCRS M R) (S : Finset R) : Nat → Finset M
  | 0 => Q.food
  | k + 1 => revClosureStep Q S (revClosureAt Q S k)

def binaryFood (n t : Nat) : Finset (Molecule n) :=
  Finset.univ.filter (fun x => molLength x ≤ t)

/-- The concrete split-position, bidirectional binary-polymer CRS. -/
def binaryPolymerCRS (n t : Nat) : ReversibleCRS (Molecule n) (Reaction n) where
  lhs := fun r => {reactionLeft r, reactionRight r}
  rhs := fun r => {reactionProduct r}
  food := binaryFood n t

theorem concrete_card_molecules_five : Fintype.card (Molecule 5) = 62 := by decide

theorem concrete_card_reactions_five : Fintype.card (Reaction 5) = 196 := by
  set_option maxRecDepth 100000 in decide

end RAF.Concrete
