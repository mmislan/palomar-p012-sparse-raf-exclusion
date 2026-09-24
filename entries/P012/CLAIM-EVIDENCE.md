# P012: two questions, one formal model

Review method: source reading only. No Lean execution.

| Selected declaration in `SparseLinearRAF` | Mathematical statement | Source |
|---|---|---|
| `sparse_linear_raf_literature_resolution` | For fixed food bound t, real C and nonnegative lambda, the probability of a nonempty RAF with at most Cn reversible channels tends to zero. | `proofs/SparseLinearRAF/LiteratureResolution.lean` |
| `no_high_probability_linear_raf` | Negates the proposed eventual high-probability linear-size assertion, with constants chosen before the limit. | Same module; derived from the first limit. |
| `single_catalyst_probability_tendsto_zero` | At fixed t and nonnegative lambda, the probability that a molecule catalyses a nonempty food-generated set constructing it tends to zero. | `proofs/SparseLinearRAF/SelfConstructionLimit.lean` |

## Model and quantifiers

The [Challenge](../../Registry/P012/Challenge.lean) contains the binary molecule
and split-position reaction types. A channel supports ligation and reverse
cleavage with one catalysis coordinate. Molecule activity is sampled independently;
conditional channel coordinates are independent with probability 1/n. Their
conjunction gives catalysis, retaining dependence between events sharing a molecule.
The activity parameter is lambda*n^2 divided by the channel count, clamped to
[0,1] for small n. Food consists of molecules with length at most t.

`IsRevRAF` explicitly requires nonemptiness, reversible food generation and
available catalysts. `SelfConstructs` requires a nonempty food-generated set,
reachability of the molecule and its catalysis of every channel in the set.
All food/intensity/budget parameters in the limit statements are fixed before n
tends to infinity. These details are part of the result, not adjustable premises.

## Literature correspondence and evidence

[Hordijk–Steel, arXiv:1605.03919v1](https://arxiv.org/pdf/1605.03919v1),
closing discussion on page 20, poses the linear-size and single-catalyst questions.
Their model description groups forward and reverse reactions and introduces a
molecule-level sparse activity law. The selected source uses explicit channel
labels and gives the three theorem types listed above.

The source-reading comparison supports this description of the selected claims.
The preparation entry subsequently passed target Solution compilation, exact
Comparator comparison, and con-ron, nanoda and Lean kernel checks in
[P012-final-run](../../preparation/verification/P012-final-run/result.json).
That pass recorded no source changes during verification. Its evidence covers
the preparation-entry snapshot, not the older frozen public-release candidate,
whose separate Lake configuration remains unexecuted. Literature, metadata
and human mathematical review remain separate; see [readiness](readiness.json).

## This prepared candidate

The Challenge now contains explicit source definitions and imports only Mathlib.
The three theorem statements and all Solution proof sources are preserved.
The old passing receipt applies to the prior imported Challenge; the revised
Challenge has not been compiled or compared. An exact cloud check is pending.
