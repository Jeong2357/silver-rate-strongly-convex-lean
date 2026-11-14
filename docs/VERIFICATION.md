# Verification

The complete source closure has 933 project modules. The reference audit
checks 8,112 project declarations, including 6,138 theorem declarations
(counting generated declarations).

The development version was recompiled in a fresh directory without reusing
its local Lean build artifacts. Its complete axiom output and final-declaration
output matched the original build byte for byte. The packaged mathematical
source bodies preserve that version; SPDX license comments were added where
needed, and trailing whitespace was normalized.

For this snapshot, `scripts/audit_release.py` checks `RELEASE_INPUTS.json`,
the complete local source closure, GPL identifiers and the pinned dependency
revisions. It runs `Audit.lean` and `MainAudit.lean`. `Audit.lean` checks every
project declaration, rejects project axiom declarations and rejects any
transitive axiom other than `propext`, `Classical.choice`, and `Quot.sound`.
The audit includes generated theorem declarations and definitions.

The final declarations are:

- `StrongSilver.silver_rate_lower_bound`
- `StrongSilver.silver_rate_lower_bound_explicit`
- `StrongSilver.silver_rate_lower_bound_horizon`

Their axiom dependencies are exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No proof-hole, native-computation or other unexpected axiom dependency is
accepted. `MainAudit.lean` prints the full final types and the objective,
iteration and error definitions. Verification outputs are generated under
ignored `verification/`, and GitHub Actions retains them as an artifact for
each checked commit.

The source hash manifest is an integrity check. The Lean build and transitive
axiom audit are the mathematical checks. The [trust basis](../README.md#trust-basis-and-package-contents)
is Lean, its kernel and the pinned dependencies.
