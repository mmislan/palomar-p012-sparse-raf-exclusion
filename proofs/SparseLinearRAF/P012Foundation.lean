import proofs.SparseLinearRAF.SelfConstruction
import proofs.SparseLinearRAF.Parameters

namespace SparseLinearRAF

open RAF RAF.Polymer RAF.Concrete MeasureTheory ProbabilityTheory Filter Topology unitInterval

noncomputable def selfConstructionProbability (n t : Nat) (lambda : ℝ) : ℝ :=
  (sparseMeasure (Molecule n) (Reaction n) (activityParameter n lambda) (channelParameter n)
    {ω | ∃ x, SelfConstructs t ω x}).toReal

noncomputable def literatureRAFProbability (n t : Nat) (lambda C : ℝ) : ℝ :=
  (sparseMeasure (Molecule n) (Reaction n) (activityParameter n lambda) (channelParameter n)
    {ω | ∃ T : Finset (Reaction n), IsRevRAF (binaryPolymerCRS n t) (sparseCatalysis ω) T ∧
      (T.card : ℝ) ≤ C * n}).toReal

end SparseLinearRAF
