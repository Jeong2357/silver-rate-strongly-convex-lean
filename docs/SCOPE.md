# Formal scope

`StrongSilver.silver_rate_lower_bound_horizon` in
[Main.lean](../StrongSilver/Main.lean) is Theorem 1.1 of the accompanying
strongly convex manuscript. It has no theorem parameters outside its
quantified conclusion.

The constants `C` and `kappa_0` are chosen before the condition number,
horizon and schedule. The horizon may be zero. Steps are arbitrary real
numbers, fixed before the objective and trajectory are chosen.

`StrongSilver.Space d` is Euclidean space on `Fin (d+1)`, so varying
`d : Nat` covers every positive finite dimension. `Admissible kappa f g`
requires global `1/kappa` strong convexity, `HasGradientAt f (g x) x` at
every point, and a globally 1-Lipschitz gradient.

`Instance kappa` supplies such an objective, a minimizer, and a distinct
initial point. `iterate` folds every original gradient step over the full
schedule. `D` and `E` are the `ENNReal` suprema of the relative squared-distance
and relative function-value errors of the last iterate. The denominators
are respectively the initial squared distance and initial function gap.
See [Problem.lean](../StrongSilver/Problem.lean).

The proof constructs actual finite-dimensional objectives and trajectories.
`WeightedCountBound` is proved in [WeightedCountBound.lean](../StrongSilver/WeightedCountBound.lean)
and discharged in the final theorem. The distance-to-value repetition bridge
is in [RepetitionBridge.lean](../StrongSilver/RepetitionBridge.lean).
The [paper correspondence](../PAPER_CORRESPONDENCE.md) records the versions of
the supporting lemmas used in this proof.
