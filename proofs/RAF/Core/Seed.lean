import proofs.RAF.Core.RAF

namespace RAF

variable {M R : Type*} [DecidableEq M]

def SeedOpen (Q : CRS M R) (C : Catalysis M R) : Prop :=
  ∃ r, SeedReaction Q r ∧ ∃ x, C x r

theorem exists_seed_of_foodGenerated (Q : CRS M R) (S : Finset R)
    (hne : S.Nonempty) (hfg : FoodGenerated Q S) :
    ∃ r ∈ S, SeedReaction Q r := by
  by_contra hseedExists
  have hseed : ∀ r ∈ S, ¬ SeedReaction Q r := by
    intro r hr hs
    exact hseedExists ⟨r, hr, hs⟩
  obtain ⟨r, hr⟩ := hne
  obtain ⟨k, hk⟩ := hfg r hr
  have hc := closureAt_eq_food_of_no_seed Q S hseed k
  exact hseed r hr (by simpa [SeedReaction, Enabled, hc] using hk)

theorem raf_implies_seedOpen (Q : CRS M R) (C : Catalysis M R) (S : Finset R)
    (hraf : IsRAF Q C S) : SeedOpen Q C := by
  obtain ⟨hne, hfg, hra⟩ := hraf
  obtain ⟨r, hr, hseed⟩ := exists_seed_of_foodGenerated Q S hne hfg
  obtain ⟨x, k, hxmem, hx⟩ := hra r hr
  exact ⟨r, hseed, x, hx⟩

end RAF
