import proofs.SparseLinearRAF.ProductiveProgram

namespace SparseLinearRAF
open RAF RAF.Concrete

variable {M R : Type*} [DecidableEq M]

noncomputable def prefixes (Q : ReversibleCRS M R) (U : Finset R) (A : Finset M) :
    Nat → Finset (List R)
  | 0 => {[]}
  | d+1 => by
    classical
    exact (U.filter (Productive Q A)).biUnion (fun r =>
      (prefixes Q U (fire Q A r) d).image (List.cons r))

def runProgram (Q : ReversibleCRS M R) (A : Finset M) : List R → Finset M
  | [] => A
  | r::rs => runProgram Q (fire Q A r) rs

theorem Program.final_eq_run {Q : ReversibleCRS M R} {U : Finset R}
    {A B : Finset M} {rs : List R} (h : Program Q U A rs B) : B = runProgram Q A rs := by
  induction h with
  | nil => rfl
  | cons _ _ _ ih => exact ih

theorem Program.mem_prefixes {Q : ReversibleCRS M R} {U : Finset R}
    {A B : Finset M} {rs : List R} (h : Program Q U A rs B) :
    rs ∈ prefixes Q U A rs.length := by
  classical
  induction h with
  | nil => simp [prefixes]
  | @cons A B rs r hr hp tail ih =>
    apply Finset.mem_biUnion.mpr
    exact ⟨r,Finset.mem_filter.mpr ⟨hr,hp⟩,Finset.mem_image.mpr ⟨rs,ih,rfl⟩⟩

theorem mem_prefixes_program {Q : ReversibleCRS M R} {U : Finset R}
    {A : Finset M} {d : Nat} {rs : List R} (h : rs ∈ prefixes Q U A d) :
    Program Q U A rs (runProgram Q A rs) ∧ rs.length = d := by
  classical
  induction d generalizing A rs with
  | zero =>
    have he : rs = [] := by simpa [prefixes] using h
    subst rs
    exact ⟨Program.nil _,rfl⟩
  | succ d ih =>
    obtain ⟨r,hr,hrest⟩ := Finset.mem_biUnion.mp h
    obtain ⟨ws,hw,he⟩ := Finset.mem_image.mp hrest
    subst rs
    obtain ⟨hp,hlen⟩ := ih hw
    exact ⟨Program.cons (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hr).2 hp,
      by simpa using congrArg Nat.succ hlen⟩

theorem Program.mono {Q : ReversibleCRS M R} {U V : Finset R} (hUV : U ⊆ V)
    {A B : Finset M} {rs : List R} (h : Program Q U A rs B) : Program Q V A rs B := by
  induction h with
  | nil => exact Program.nil _
  | cons hr hp _ ih => exact Program.cons (hUV hr) hp ih

theorem Program.mem_allowed {Q : ReversibleCRS M R} {U : Finset R}
    {A B : Finset M} {rs : List R} (h : Program Q U A rs B) :
    ∀ r ∈ rs, r ∈ U := by
  induction h with
  | nil => simp
  | @cons A B rs r hr hp tail ih =>
    intro s hs
    rcases List.mem_cons.mp hs with he | hs
    · exact he.symm ▸ hr
    · exact ih s hs

noncomputable def shallowUniverse (Q : ReversibleCRS M R) (U : Finset R)
    (A : Finset M) (d : Nat) : Finset M := by
  classical
  exact (Finset.range d).biUnion (fun j => (prefixes Q U A j).biUnion (runProgram Q A))

theorem Program.final_subset_shallow {Q : ReversibleCRS M R} {U : Finset R}
    {A B : Finset M} {rs : List R} (h : Program Q U A rs B) {d : Nat} (hlen : rs.length < d) :
    B ⊆ shallowUniverse Q U A d := by
  classical
  intro x hx
  apply Finset.mem_biUnion.mpr
  refine ⟨rs.length,Finset.mem_range.mpr hlen,Finset.mem_biUnion.mpr ?_⟩
  exact ⟨rs,h.mem_prefixes,h.final_eq_run ▸ hx⟩

theorem reachable_outside_shallow_prefix (Q : ReversibleCRS M R) (U : Finset R)
    (x : M) (j d : Nat) (hx : x ∈ revClosureAt Q U j)
    (hfar : x ∉ shallowUniverse Q U Q.food d) :
    ∃ rs ∈ prefixes Q U Q.food d, rs.length = d ∧ rs.Nodup := by
  obtain ⟨rs,B,hp,hlen⟩ := exists_program_length Q U x j hx d (by
    intro rs B h hs hxB
    exact hfar (h.final_subset_shallow hs hxB))
  refine ⟨rs,?_,hlen,hp.nodup⟩
  rw [← hlen]
  exact hp.mem_prefixes

end SparseLinearRAF
