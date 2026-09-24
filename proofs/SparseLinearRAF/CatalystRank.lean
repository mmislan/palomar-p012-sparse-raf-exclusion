import proofs.RAF.Concrete.SeedGateway

namespace SparseLinearRAF

open RAF RAF.Concrete

variable {M R : Type*} [DecidableEq M]

def Reachable (Q : ReversibleCRS M R) (T : Finset R) (x : M) : Prop :=
  ∃ j, x ∈ revClosureAt Q T j

def Covers (C : Catalysis M R) (K : Finset M) (T : Finset R) : Prop :=
  ∀ r ∈ T, ∃ x ∈ K, C x r

/-- Nonemptiness is essential when the targets can be food molecules. -/
def Build (Q : ReversibleCRS M R) (C : Catalysis M R)
    (K : Finset M) (m : Nat) : Prop :=
  ∃ T : Finset R, T.Nonempty ∧ T.card ≤ m ∧ RevFoodGenerated Q T ∧
    Covers C K T ∧ ∀ x ∈ K, Reachable Q T x

theorem build_implies_raf (Q : ReversibleCRS M R) (C : Catalysis M R)
    (K : Finset M) (m : Nat) (h : Build Q C K m) :
    ∃ T : Finset R, IsRevRAF Q C T ∧ T.card ≤ m := by
  obtain ⟨T, hne, hm, hfg, hcov, hreach⟩ := h
  refine ⟨T, ⟨hne, hfg, ?_⟩, hm⟩
  intro r hr
  obtain ⟨x, hx, hcat⟩ := hcov r hr
  obtain ⟨j, hj⟩ := hreach x hx
  exact ⟨x, j, hj, hcat⟩

theorem raf_implies_build (Q : ReversibleCRS M R) (C : Catalysis M R)
    (T : Finset R) (h : IsRevRAF Q C T) :
    ∃ K : Finset M, K.Nonempty ∧ K.card ≤ T.card ∧ Build Q C K T.card := by
  classical
  obtain ⟨hne, hfg, hra⟩ := h
  choose x j hj hcat using hra
  let K : Finset M := T.attach.image (fun r => x r.val r.property)
  have hK : ∀ y ∈ K, ∃ r, ∃ hr : r ∈ T, y = x r hr := by
    intro y hy
    obtain ⟨r, _, heq⟩ := Finset.mem_image.mp hy
    exact ⟨r.val, r.property, heq.symm⟩
  refine ⟨K, ?_, ?_, T, hne, le_rfl, hfg, ?_, ?_⟩
  · obtain ⟨r, hr⟩ := hne
    exact ⟨x r hr, Finset.mem_image.mpr ⟨⟨r, hr⟩, by simp, rfl⟩⟩
  · exact (Finset.card_image_le).trans (by simp)
  · intro r hr
    exact ⟨x r hr, Finset.mem_image.mpr ⟨⟨r, hr⟩, by simp, rfl⟩, hcat r hr⟩
  · intro y hy
    obtain ⟨r, hr, rfl⟩ := hK y hy
    exact ⟨j r hr, hj r hr⟩

theorem bounded_raf_iff_build (Q : ReversibleCRS M R) (C : Catalysis M R)
    (m : Nat) :
    (∃ T : Finset R, IsRevRAF Q C T ∧ T.card ≤ m) ↔
    ∃ K : Finset M, K.Nonempty ∧ K.card ≤ m ∧ Build Q C K m := by
  constructor
  · rintro ⟨T, hT, hm⟩
    obtain ⟨K, hK, hcard, S, hS, hSm, hfg, hcov, hreach⟩ :=
      raf_implies_build Q C T hT
    exact ⟨K, hK, hcard.trans hm, S, hS, hSm.trans hm, hfg, hcov, hreach⟩
  · rintro ⟨K, _, _, h⟩
    exact build_implies_raf Q C K m h

end SparseLinearRAF
