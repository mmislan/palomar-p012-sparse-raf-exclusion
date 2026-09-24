import proofs.RAF.Probability.UniformCatalysis

namespace RAF.Probability

def seedPairCount (M cardX : Nat) : Nat := M * cardX

/-- Exact independent-coordinate formula for the event that every
molecule--seed-reaction catalysis pair is absent. -/
theorem prob_seedClosed (p : ℝ) (M cardX : Nat) :
    allAbsentProbability p (seedPairCount M cardX) = (1 - p) ^ (M * cardX) := by
  exact allAbsentProbability_eq_pow p (M * cardX)

end RAF.Probability
