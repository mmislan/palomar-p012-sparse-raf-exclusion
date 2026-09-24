import proofs.RAF.Concrete.UniformModel

namespace RAF.Concrete

open MeasureTheory ProbabilityTheory
open RAF RAF.Polymer

def HasRAFEvent (n : Nat) : Set (CatalysisSample n) :=
  {ω | ∃ S : Finset (Reaction n),
    IsRevRAF (binaryPolymerCRS n 2) (catalysisOf ω) S}

/-- In the partitioned sample space, seed-closed is exactly the rectangle whose
seed-coordinate component is empty. -/
def SeedClosedEvent (n : Nat) : Set (CatalysisSample n) :=
  ({∅} : Set (Set (SeedCoord n))) ×ˢ Set.univ

def SeedOpenEvent (n : Nat) : Set (CatalysisSample n) :=
  (SeedClosedEvent n)ᶜ

theorem measurableSet_seedClosedEvent (n : Nat) : MeasurableSet (SeedClosedEvent n) := by
  exact (MeasurableSet.singleton (∅ : Set (SeedCoord n))).prod MeasurableSet.univ

theorem measurableSet_hasRAFEvent (n : Nat) : MeasurableSet (HasRAFEvent n) := by
  exact Set.toFinite (HasRAFEvent n) |>.measurableSet

theorem hasRAF_subset_seedOpen (n : Nat) : HasRAFEvent n ⊆ SeedOpenEvent n := by
  intro ω hraf
  obtain ⟨S, hS⟩ := hraf
  obtain ⟨r, hr, x, hcat⟩ := polymer_raf_implies_seedOpen n (catalysisOf ω) S hS
  intro hclosed
  have hempty : ω.1 = ∅ := by simpa [SeedClosedEvent] using hclosed
  have hmem : (x, ⟨r, hr⟩) ∈ ω.1 :=
    (catalysisOf_seed_iff ω x r hr).mp hcat
  rw [hempty] at hmem
  exact hmem

theorem hasRAF_disjoint_seedClosed (n : Nat) :
    Disjoint (HasRAFEvent n) (SeedClosedEvent n) := by
  exact Set.disjoint_left.2 fun ω hraf hclosed =>
    (hasRAF_subset_seedOpen n hraf) hclosed

noncomputable def rafProbability (n : Nat) (lambda : ℝ) : ℝ :=
  (uniformCatalysisMeasure n lambda).real (HasRAFEvent n)

noncomputable def seedClosedProbability (n : Nat) (lambda : ℝ) : ℝ :=
  (uniformCatalysisMeasure n lambda).real (SeedClosedEvent n)

theorem measure_seedClosed (n : Nat) (lambda : ℝ) :
    seedClosedProbability n lambda =
      (1 - (catalysisP n lambda : ℝ)) ^ Fintype.card (SeedCoord n) := by
  simp [seedClosedProbability, SeedClosedEvent, uniformCatalysisMeasure,
    setBernoulli_real_singleton]

theorem actual_raf_seed_bound (n : Nat) (lambda : ℝ) :
    rafProbability n lambda + seedClosedProbability n lambda ≤ 1 := by
  have hmono :
      (uniformCatalysisMeasure n lambda).real (HasRAFEvent n) ≤
        (uniformCatalysisMeasure n lambda).real (SeedClosedEvent n)ᶜ :=
    measureReal_mono (hasRAF_subset_seedOpen n)
  have hsum := measureReal_add_measureReal_compl
    (μ := uniformCatalysisMeasure n lambda) (measurableSet_seedClosedEvent n)
  have huniv : (uniformCatalysisMeasure n lambda).real Set.univ = 1 := probReal_univ
  dsimp [rafProbability, seedClosedProbability]
  linarith

end RAF.Concrete
