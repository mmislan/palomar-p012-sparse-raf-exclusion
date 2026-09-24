import proofs.RAF.Concrete.SeedGateway
import Mathlib.Probability.Distributions.SetBernoulli

namespace RAF.Concrete

open MeasureTheory ProbabilityTheory unitInterval
open RAF RAF.Polymer

abbrev SeedCoord (n : Nat) := Molecule n × PolymerSeedReaction n 2
abbrev NonseedReaction (n : Nat) :=
  {r : Reaction n // ¬ RevSeedReaction (binaryPolymerCRS n 2) r}
abbrev NonseedCoord (n : Nat) := Molecule n × NonseedReaction n

/-- Partitioned representation of every molecule--reaction coordinate. -/
abbrev CatalysisSample (n : Nat) := Set (SeedCoord n) × Set (NonseedCoord n)

noncomputable def rawCatalysisP (n : Nat) (lambda : ℝ) : ℝ :=
  lambda * n / Fintype.card (Reaction n)

/-- Clamp only to obtain a total unit-interval parameter.  The asymptotic proof
later shows the clamp is inactive in the positive fixed-lambda tail. -/
noncomputable def catalysisP (n : Nat) (lambda : ℝ) : I :=
  ⟨min 1 (max 0 (rawCatalysisP n lambda)), by
    constructor
    · exact le_min (by norm_num) (le_max_left _ _)
    · exact min_le_left _ _⟩

/-- Genuine product Bernoulli probability measure.  Seed and nonseed
coordinates are independently sampled with the same parameter. -/
noncomputable def uniformCatalysisMeasure (n : Nat) (lambda : ℝ) :
    Measure (CatalysisSample n) :=
  (setBernoulli (Set.univ : Set (SeedCoord n)) (catalysisP n lambda)).prod
    (setBernoulli (Set.univ : Set (NonseedCoord n)) (catalysisP n lambda))

noncomputable instance uniformCatalysisMeasure_isProbability (n : Nat) (lambda : ℝ) :
    IsProbabilityMeasure (uniformCatalysisMeasure n lambda) := by
  unfold uniformCatalysisMeasure
  infer_instance

theorem uniformCatalysisMeasure_univ (n : Nat) (lambda : ℝ) :
    uniformCatalysisMeasure n lambda Set.univ = 1 := by
  simp [uniformCatalysisMeasure]

/-- Convert a sampled partition back to the catalysis relation on the concrete
base reactions. -/
def catalysisOf {n : Nat} (ω : CatalysisSample n) :
    Catalysis (Molecule n) (Reaction n) := fun x r =>
  if h : RevSeedReaction (binaryPolymerCRS n 2) r then
    (x, ⟨r, h⟩) ∈ ω.1
  else
    (x, ⟨r, h⟩) ∈ ω.2

theorem catalysisOf_seed_iff {n : Nat} (ω : CatalysisSample n)
    (x : Molecule n) (r : Reaction n)
    (h : RevSeedReaction (binaryPolymerCRS n 2) r) :
    catalysisOf ω x r ↔ (x, ⟨r, h⟩) ∈ ω.1 := by
  simp [catalysisOf, h]

theorem catalysisOf_nonseed_iff {n : Nat} (ω : CatalysisSample n)
    (x : Molecule n) (r : Reaction n)
    (h : ¬ RevSeedReaction (binaryPolymerCRS n 2) r) :
    catalysisOf ω x r ↔ (x, ⟨r, h⟩) ∈ ω.2 := by
  simp [catalysisOf, h]

end RAF.Concrete
