import proofs.SparseLinearRAF.AssemblyCode

namespace SparseLinearRAF
open RAF RAF.Polymer RAF.Concrete

theorem endpoint_of_mem_sides {n t : Nat} {r : Reaction n} {x : Molecule n}
    (hx : x ∈ (binaryPolymerCRS n t).lhs r ∪ (binaryPolymerCRS n t).rhs r) :
    ∃ j : Fin 3, endpoint r j = x := by
  simp only [binaryPolymerCRS,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with (rfl | rfl) | rfl
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩

theorem program_nodes_encodable {n t m : Nat} {U : Finset (Reaction n)}
    {A B : Finset (Molecule n)} {rs : List (Reaction n)}
    (hp : Program (binaryPolymerCRS n t) U A rs B)
    (a : Fin m → Reaction n) (label : Reaction n → Fin m) (rank : Fin m → Nat)
    (hrecover : ∀ r ∈ rs, a (label r) = r)
    (horder : rs.Pairwise (fun r s => rank (label r) < rank (label s)))
    (hA : ∀ r ∈ rs, ∀ x ∈ A, ∃ z : AssemblyRef n t m,
      refValue a z = x ∧ refBefore rank (label r) z) :
    ∀ r ∈ rs, ∃ c : AssemblyNode n t m,
      nodeBefore rank (label r) c ∧ nodeMatches a (label r) c := by
  induction hp with
  | nil => simp
  | @cons A B rs r hr hprod tail ih =>
    have hord := List.pairwise_cons.mp horder
    have hrec := hrecover r (by simp)
    have hhead : ∃ c : AssemblyNode n t m,
        nodeBefore rank (label r) c ∧ nodeMatches a (label r) c := by
      rcases hprod.1 with hl | hh
      · obtain ⟨z,hz,hzb⟩ := hA r (by simp) (reactionLeft r) (hl (by simp [binaryPolymerCRS]))
        obtain ⟨w,hw,hwb⟩ := hA r (by simp) (reactionRight r) (hl (by simp [binaryPolymerCRS]))
        exact ⟨.inl (z,w),⟨hzb,hwb⟩,by simpa only [nodeMatches,hrec] using And.intro hz hw⟩
      · obtain ⟨z,hz,hzb⟩ := hA r (by simp) (reactionProduct r) (hh (by simp [binaryPolymerCRS]))
        have hs : r.2.2.val < n := by
          have h1 := r.2.2.isLt
          have h2 := r.1.isLt
          omega
        exact ⟨.inr (z,⟨r.2.2.val,hs⟩),hzb,
          hz.trans (congrArg reactionProduct hrec).symm,
          (congrArg (fun s : Reaction n => s.2.2.val) hrec).symm⟩
    have ht : ∀ s ∈ rs, ∃ c : AssemblyNode n t m,
        nodeBefore rank (label s) c ∧ nodeMatches a (label s) c := by
      apply ih
      · intro s hs
        exact hrecover s (by simp [hs])
      · exact hord.2
      · intro s hs x hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact hA s (by simp [hs]) x hx
        · obtain ⟨j,hj⟩ := endpoint_of_mem_sides hx
          exact ⟨.inr (label r,j),by simpa only [refValue,hrec] using hj,hord.1 s hs⟩
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hhead
    · exact ht s hs

def ConstructibleSupport (n t : Nat) (S : Finset (Reaction n)) : Prop :=
  ∃ rs B, Program (binaryPolymerCRS n t) S (binaryFood n t) rs B ∧ rs.toFinset = S

theorem constructible_assignment_encodable {n t m : Nat} (hm : 0 < m)
    (a : Fin m → Reaction n) (hinj : Function.Injective a)
    (hc : ConstructibleSupport n t (Finset.univ.image a)) :
    ∃ c : AssemblyCode n t m, ValidAssembly a c := by
  classical
  obtain ⟨rs,B,hp,hS⟩ := hc
  have hex : ∀ r ∈ rs, ∃ i, a i = r := by
    intro r hr
    have hh : r ∈ Finset.univ.image a := hS ▸ List.mem_toFinset.mpr hr
    simpa only [Finset.mem_image,Finset.mem_univ,true_and] using hh
  let label : Reaction n → Fin m := fun r =>
    if h : ∃ i, a i = r then Classical.choose h else ⟨0,hm⟩
  have hrec : ∀ r ∈ rs, a (label r) = r := by
    intro r hr
    dsimp only [label]
    simp [hex r hr]
    exact Classical.choose_spec (hex r hr)
  have hmem (i : Fin m) : a i ∈ rs := by
    apply List.mem_toFinset.mp
    rw [hS]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hlabel (i : Fin m) : label (a i) = i := hinj (hrec (a i) (hmem i))
  let rank : Fin m → Nat := fun i => rs.idxOf (a i)
  have hord : rs.Pairwise (fun r s => rank (label r) < rank (label s)) := by
    apply List.pairwise_iff_get.mpr
    intro i j hij
    dsimp only [rank]
    rw [hrec (rs.get i) (List.get_mem _ _),hrec (rs.get j) (List.get_mem _ _)]
    rw [List.get_idxOf hp.nodup, List.get_idxOf hp.nodup]
    exact_mod_cast hij
  have hn := program_nodes_encodable hp a label rank hrec hord (by
    intro r hr x hx
    exact ⟨.inl ⟨x,hx⟩,rfl,True.intro⟩)
  have hall : ∀ i, ∃ c : AssemblyNode n t m, nodeBefore rank i c ∧ nodeMatches a i c := by
    intro i
    simpa only [hlabel] using hn (a i) (hmem i)
  choose c hbefore hmatches using hall
  exact ⟨c,rank,fun i => ⟨hbefore i,hmatches i⟩⟩

end SparseLinearRAF
