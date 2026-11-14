# 1.0.0

- `StrongSilver.silver_rate_lower_bound_horizon` proves the sharp silver-rate
  lower bound for both relative squared-distance and function-value errors.
  One absolute pair of constants applies to all sufficiently large condition
  numbers, all horizons and all predetermined real stepsize schedules.
- The objective class is globally differentiable, 1-smooth and
  `1/kappa`-strongly convex in positive finite Euclidean dimension. Both
  errors use the last iterate.
- The package includes the complete local proof sources, pinned Lean and
  library versions, declaration and axiom audits, and a GitHub Actions workflow.
- The original code is licensed under `GPL-3.0-only`. Dependency notices are
  preserved in `THIRD_PARTY_NOTICES.md`.

The allowed transitive axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Intermediate quantitative choices are recorded in `PAPER_CORRESPONDENCE.md`.

Authors: Yechan Jeong; Youngjoon Hong.
Affiliation: Department of Mathematical Sciences, Seoul National University.
Contact: Yechan Jeong <yechan@snu.ac.kr>; Youngjoon Hong <hongyj@snu.ac.kr>.

A paper presenting the mathematical proof will be submitted to arXiv.
A reference will be added when available.
