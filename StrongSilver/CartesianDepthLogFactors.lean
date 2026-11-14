-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianDepthPhases

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 2600000

/-- Every actual chronological depth phase has a positive leading
factor when the intervening Cartesian excesses and exterior factor are
positive. This includes all following ancestor pivots. -/
theorem depthPhases_terminal_positive (φ : ℝ → ℝ) {d : ℕ} {t : ScheduleTree} {b : ℝ}
    (hpos : positiveExcessThrough φ d t) (hterm : 0 < terminalFactor φ t b) :
    ∀ q ∈ depthPhases d t b, 0 < terminalFactor φ q.1 q.2 := by
  induction d generalizing t b with
  | zero =>
    intro q hq
    simp only [depthPhases,List.mem_singleton] at hq
    subst q
    exact hterm
  | succ d ih =>
    cases t with
    | leaf h =>
      intro q hq
      simp only [depthPhases,List.mem_singleton] at hq
      subst q
      exact hterm
    | split l p r =>
      have hd := (positive_excess_mass_identity φ l r p hpos.1).2
      have hnum : 0 < φ b-1-gapDrawdown φ (.split l p r) := by
        have hm := prefixMass_positive φ (.split l p r)
        exact (div_pos_iff.mp hterm).elim (fun h => h.1) (fun h => False.elim ((not_lt_of_ge hm.le) h.2))
      have hl : 0 < terminalFactor φ l p := div_pos hpos.1 (prefixMass_positive φ l)
      have hr : 0 < terminalFactor φ r b := by
        unfold terminalFactor
        rw [hd] at hnum
        exact div_pos hnum (prefixMass_positive φ r)
      intro q hq
      simp only [depthPhases,List.mem_append] at hq
      exact hq.elim (fun hq => ih hpos.2.1 hl q hq) (fun hq => ih hpos.2.2 hr q hq)

/-- Logarithmic form of the exact product identity for the original
chronological groups, with every positivity obligation discharged. -/
theorem depthPhases_log_factor_sum (φ : ℝ → ℝ) {d : ℕ} {t : ScheduleTree} {b : ℝ}
    (hpos : positiveExcessThrough φ d t) (hterm : 0 < terminalFactor φ t b) :
    ((depthPhases d t b).map fun q => Real.log (terminalFactor φ q.1 q.2)).sum =
      Real.log (terminalFactor φ t b)+throughSum (rootGain φ) d t := by
  have hnonzero : ∀ x ∈ (depthPhases d t b).map (fun q => terminalFactor φ q.1 q.2), x ≠ 0 := by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact (depthPhases_terminal_positive φ hpos hterm q hq).ne'
  have hh := Real.log_list_prod hnonzero
  rw [depthPhases_factor_identity φ d t b hpos,Real.log_mul hterm.ne' (Real.exp_ne_zero _),Real.log_exp] at hh
  simpa only [List.map_map,Function.comp_def] using hh.symm

end
end StrongSilver.ScheduleTree
