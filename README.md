# Silver-rate lower bound for gradient descent: strongly convex case

**Theorem.** There are absolute constants $`C,\kappa_0>0`$ such that, for every
$`\kappa\ge\kappa_0`$, every integer $`n\ge0`$, and every predetermined
real stepsize schedule $`h\in\mathbb R^n`$,

```math
\min\{D_{n,\kappa}(h),E_{n,\kappa}(h)\}
\ge \exp(-Cn\kappa^{-\nu}),\qquad
\nu=\frac1p,\quad p=\log_2(1+\sqrt2).
```

The final Lean declaration is
[`StrongSilver.silver_rate_lower_bound_horizon`](StrongSilver/Main.lean).
It uses one pair of constants before the condition number, horizon and schedule.
Negative and zero steps and the empty schedule are included.

The iteration is $`x_{i+1}=x_i-h_i\nabla f(x_i)`$. The two errors are the suprema of

```math
\frac{\lVert x_n-x_*\rVert^2}{\lVert x_0-x_*\rVert^2}
\quad\text{and}\quad
\frac{f(x_n)-f(x_*)}{f(x_0)-f(x_*)},
```

respectively, over all positive finite Euclidean dimensions, globally
differentiable 1-smooth $`1/\kappa`$-strongly convex objectives, their minimizers,
and distinct initial points. They are represented in `ENNReal`. Both errors
use the last iterate. See the [definitions](StrongSilver/Problem.lean) and
[formal scope](docs/SCOPE.md).

Version: 1.0.0.

Repository: [Jeong2357/silver-rate-strongly-convex-lean](https://github.com/Jeong2357/silver-rate-strongly-convex-lean).

Authors:

- Yechan Jeong — [yechan@snu.ac.kr](mailto:yechan@snu.ac.kr) · [ORCID](https://orcid.org/0009-0000-1476-0666)
- Youngjoon Hong — [hongyj@snu.ac.kr](mailto:hongyj@snu.ac.kr) · [ORCID](https://orcid.org/0000-0003-4956-8660)

Affiliation: Department of Mathematical Sciences, Seoul National University.

The original Lean code and verification scripts are licensed under
`GPL-3.0-only`; see [LICENSE](LICENSE) and [CITATION.cff](CITATION.cff).

A paper presenting the mathematical proof of the result will be submitted to
arXiv. A reference will be added when available.

The smooth convex result is in the separate
[silver-rate-lean repository](https://github.com/Jeong2357/silver-rate-lean).

## Formal statement

The explicit list-schedule declaration
[`StrongSilver.silver_rate_lower_bound_explicit`](StrongSilver/Main.lean)
has type:

```lean
∃ C κ₀ : ℝ, 0 < C ∧ 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ ≤ κ → ∀ h : List ℝ,
  ENNReal.ofReal (Real.exp (-C * (h.length : ℝ) * κ ^ (-StrongSilver.nu)))
    ≤ StrongSilver.D κ h ∧
  ENNReal.ofReal (Real.exp (-C * (h.length : ℝ) * κ ^ (-StrongSilver.nu)))
    ≤ StrongSilver.E κ h
```

The horizon declaration uses `h : Fin n → ℝ` and `List.ofFn h`. The final
declarations discharge the weighted-count, band-estimate, interpolation and
trajectory-construction premises in the proof. The [paper correspondence](PAPER_CORRESPONDENCE.md)
records the finite quantitative versions of the intermediate lemmas.
No numerical values of the absolute constants are extracted.

## Reproduce the verification

Prerequisites: Git, Python 3.10 or newer (standard library only), and
[elan](https://github.com/leanprover/elan) on `PATH`. From a fresh checkout:

```sh
git clone https://github.com/Jeong2357/silver-rate-strongly-convex-lean.git
cd silver-rate-strongly-convex-lean
lake exe cache get
bash scripts/verify.sh
```

The script explicitly builds `+StrongSilver.Main` and `+StrongSilver`, checks
every packaged input hash and dependency revision, and audits every project
declaration against the allowed transitive axioms. To run the steps separately:

```sh
lake build +StrongSilver.Main
lake build +StrongSilver
python3 scripts/audit_release.py
lake env lean MainAudit.lean
```

The first setup requires network access and several GB of disk space. Lean is
pinned to `v4.33.1` by [lean-toolchain](lean-toolchain). The
[lake manifest](lake-manifest.json) pins mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474` and records the transitive dependency
commits.

Results go to ignored `verification/` files. `status.json` records declaration
counts, all theorem axiom dependencies and the checked input-manifest hash.
`all-axioms.log` contains the full project audit;
`declarations-and-axioms.log` contains the final theorem types, definitions and
`#print axioms` output. A failed build, changed packaged input, missing declaration
or unexpected axiom makes verification exit nonzero. The same build and audit
run in [GitHub Actions](.github/workflows/lean.yml).

## Trust basis and package contents

The allowed axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.
The audit rejects proof-hole axioms, native-computation axioms and custom axioms.
Lean, its kernel and the pinned library dependencies form the trust basis.
See the [verification record](docs/VERIFICATION.md).

The snapshot contains Lean sources, verification scripts, documentation,
dependency pins and metadata. The manuscript and development logs are outside
this package. All project-specific proof sources are included; the package
requires neither the companion repository nor an external solver.

Dependency notices are preserved in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
Dependency source trees are obtained separately by Lake and retain their
upstream copyrights and licenses.
