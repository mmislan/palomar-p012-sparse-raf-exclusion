import proofs.RAF.Concrete.SeedGateway

namespace SparseLinearRAF
open RAF RAF.Concrete

variable {M R : Type*} [DecidableEq M]

def fire (Q : ReversibleCRS M R) (A : Finset M) (r : R) : Finset M :=
  A ∪ (Q.lhs r ∪ Q.rhs r)

def Productive (Q : ReversibleCRS M R) (A : Finset M) (r : R) : Prop :=
  (Q.lhs r ⊆ A ∨ Q.rhs r ⊆ A) ∧ ¬ Q.lhs r ∪ Q.rhs r ⊆ A

instance productiveDecidable (Q : ReversibleCRS M R) (A : Finset M) (r : R) :
    Decidable (Productive Q A r) := by
  unfold Productive
  infer_instance

/-- Every channel is enabled at its firing time and adds a new molecule. -/
inductive Program (Q : ReversibleCRS M R) (U : Finset R) :
    Finset M → List R → Finset M → Prop
  | nil (A) : Program Q U A [] A
  | cons {A B rs r} (hr : r ∈ U) (hp : Productive Q A r)
      (tail : Program Q U (fire Q A r) rs B) : Program Q U A (r::rs) B

theorem Program.initial_subset_final {Q : ReversibleCRS M R} {U : Finset R}
    {A B : Finset M} {rs : List R} (h : Program Q U A rs B) : A ⊆ B := by
  induction h with
  | nil => exact Finset.Subset.refl _
  | cons _ _ _ ih => exact Finset.subset_union_left.trans ih

theorem Program.completed_channel_not_mem {Q : ReversibleCRS M R} {U : Finset R}
    {A B : Finset M} {rs : List R} (h : Program Q U A rs B)
    (r : R) (hready : Q.lhs r ∪ Q.rhs r ⊆ A) : r ∉ rs := by
  induction h with
  | nil => simp
  | @cons A B rs s hs hp tail ih =>
    have hne : r ≠ s := by
      intro he
      subst s
      exact hp.2 hready
    have hnext : Q.lhs r ∪ Q.rhs r ⊆ fire Q A s :=
      hready.trans Finset.subset_union_left
    simp only [List.mem_cons,not_or]
    exact ⟨hne, ih hnext⟩

theorem Program.nodup {Q : ReversibleCRS M R} {U : Finset R}
    {A B : Finset M} {rs : List R} (h : Program Q U A rs B) : rs.Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | @cons A B rs r hr hp tail ih =>
    apply List.nodup_cons.mpr
    exact ⟨tail.completed_channel_not_mem r Finset.subset_union_right, ih⟩

/-- A state with no productive selected channel contains the entire closure. -/
theorem closure_subset_of_no_productive (Q : ReversibleCRS M R) (U : Finset R)
    (A : Finset M) (hf : Q.food ⊆ A) (hstop : ∀ r ∈ U, ¬ Productive Q A r) :
    ∀ j, revClosureAt Q U j ⊆ A := by
  intro j
  induction j with
  | zero => exact hf
  | succ j ih =>
    intro x hx
    simp only [revClosureAt,revClosureStep,Finset.mem_union,Finset.mem_biUnion] at hx
    rcases hx with hx | ⟨r,hr,hx⟩
    · exact ih hx
    rcases hx with hx | hx
    · by_cases he : RevEnabledLhs Q (revClosureAt Q U j) r
      · have hall : Q.lhs r ∪ Q.rhs r ⊆ A := by
          by_contra hn
          exact hstop r hr ⟨Or.inl (he.trans ih),hn⟩
        simp [he] at hx
        exact hall (Finset.mem_union_right _ hx)
      · simp [he] at hx
    · by_cases he : RevEnabledRhs Q (revClosureAt Q U j) r
      · have hall : Q.lhs r ∪ Q.rhs r ⊆ A := by
          by_contra hn
          exact hstop r hr ⟨Or.inr (he.trans ih),hn⟩
        simp [he] at hx
        exact hall (Finset.mem_union_left _ hx)
      · simp [he] at hx

theorem exists_productive_of_reachable (Q : ReversibleCRS M R) (U : Finset R)
    (A : Finset M) (hf : Q.food ⊆ A) (x : M) (j : Nat)
    (hx : x ∈ revClosureAt Q U j) (hmiss : x ∉ A) :
    ∃ r ∈ U, Productive Q A r := by
  by_contra hn
  have hstop : ∀ r ∈ U, ¬ Productive Q A r := by
    intro r hr hp
    exact hn ⟨r,hr,hp⟩
  exact hmiss (closure_subset_of_no_productive Q U A hf hstop j hx)

theorem Program.append {Q : ReversibleCRS M R} {U : Finset R}
    {A B C : Finset M} {rs ss : List R} (h : Program Q U A rs B)
    (h' : Program Q U B ss C) : Program Q U A (rs ++ ss) C := by
  induction h with
  | nil => exact h'
  | cons hr hp _ ih => exact Program.cons hr hp (ih h')

theorem Productive.card_fire_gt {Q : ReversibleCRS M R} {A : Finset M} {r : R}
    (h : Productive Q A r) : A.card < (fire Q A r).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨Finset.subset_union_left,?_⟩
  intro he
  have hs : Q.lhs r ∪ Q.rhs r ⊆ fire Q A r := Finset.subset_union_right
  rw [← he] at hs
  exact h.2 hs

theorem Program.card_lower {Q : ReversibleCRS M R} {U : Finset R}
    {A B : Finset M} {rs : List R} (h : Program Q U A rs B) :
    A.card + rs.length ≤ B.card := by
  induction h with
  | nil => simp
  | cons hr hp tail ih =>
    have := hp.card_fire_gt
    simp only [List.length_cons]
    omega

/-- A reachable target excluded by all shorter productive programs forces a
productive prefix of the requested depth. No arbitrary ordering is assumed. -/
theorem exists_program_length (Q : ReversibleCRS M R) (U : Finset R)
    (x : M) (j : Nat) (hx : x ∈ revClosureAt Q U j) (d : Nat)
    (hfar : ∀ (rs : List R) (B : Finset M), Program Q U Q.food rs B →
      rs.length < d → x ∉ B) :
    ∃ (rs : List R) (B : Finset M), Program Q U Q.food rs B ∧ rs.length = d := by
  induction d with
  | zero => exact ⟨[],Q.food,Program.nil _,rfl⟩
  | succ d ih =>
    obtain ⟨rs,B,hp,hlen⟩ := ih (fun rs B h hh => hfar rs B h (by omega))
    have hmiss := hfar rs B hp (by omega)
    obtain ⟨r,hr,hprod⟩ := exists_productive_of_reachable Q U B
      hp.initial_subset_final x j hx hmiss
    refine ⟨rs ++ [r],fire Q B r,hp.append (Program.cons hr hprod (Program.nil _)),?_⟩
    simp [hlen]

/-- Every closure membership has a productive construction certificate. -/
theorem reachable_has_productive_program [Fintype M] (Q : ReversibleCRS M R)
    (U : Finset R) (x : M) (j : Nat) (hx : x ∈ revClosureAt Q U j) :
    ∃ (rs : List R) (B : Finset M), Program Q U Q.food rs B ∧ x ∈ B := by
  by_contra hn
  have hfar : ∀ (rs : List R) (B : Finset M), Program Q U Q.food rs B →
      rs.length < Fintype.card M + 1 → x ∉ B := by
    intro rs B hp _ hm
    exact hn ⟨rs,B,hp,hm⟩
  obtain ⟨rs,B,hp,hlen⟩ := exists_program_length Q U x j hx (Fintype.card M+1) hfar
  have hlow := hp.card_lower
  have hu := Finset.card_le_univ B
  omega

end SparseLinearRAF
