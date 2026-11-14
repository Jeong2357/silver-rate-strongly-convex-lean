-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if (`StrongSilver).isPrefixOf name then
      declarations := declarations + 1
      if let .axiomInfo _ := info then
        throwError "Local axiom declaration: {name}"
      let used ← collectAxioms name
      for a in used do
        unless a == ``propext || a == ``Classical.choice || a == ``Quot.sound do
          throwError "Unexpected transitive axiom {a} in {name}"
      if let .thmInfo _ := info then
        theorems := theorems + 1
        logInfo m!"STRONG_SILVER_AXIOMS {name}: {used}"
  logInfo m!"STRONG_SILVER_AUDIT_OK declarations={declarations} theorems={theorems}"

set_option pp.explicit true in
#print StrongSilver.MainLowerBound

#print axioms StrongSilver.D_append_le
#print axioms StrongSilver.E_append_le
#print axioms StrongSilver.D_le_kappa_E
#print axioms StrongSilver.moreau_admissible

#print axioms StrongSilver.silver_rate_lower_bound
#print axioms StrongSilver.silver_rate_lower_bound_explicit
#print axioms StrongSilver.silver_rate_lower_bound_horizon
#print axioms StrongSilver.weighted_count_bound
