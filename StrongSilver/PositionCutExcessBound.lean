-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PositionCutExcess

namespace StrongSilver
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2600000

/-- Total excess bound on an actual finite cut-insertion chain. The
centered log lower budget is uniform over every intermediate cut,
including partial ties. -/
theorem position_cut_excess_sum_bound (φ : ℝ → ℝ) (base : ℕ → ℝ → Bool) (h : List ℝ) (ps : List ℕ)
    {P reserve M e center : ℝ} (hP : 0 ≤ P) (hr : 0 ≤ reserve) (he : 0 ≤ e)
    (w : ℕ → ℝ) (hw : ∀ i ≤ ps.length, 0 < w i)
    (hmono : ∀ i < ps.length, w (i+1) ≤ w i)
    (hpivot : ∀ i < ps.length, w (i+1) = (φ (stepAt h (ps[i]?.getD 0))-P)^nu)
    (hlower : ∀ i ≤ ps.length,
      -e ≤ w i*(cutLogProduct φ P reserve (positionCut base h (ps.take i))-center))
    (hupper : w 0*(cutLogProduct φ P reserve (positionCut base h [])-center) ≤ M)
    (hfinal : cutPower φ P reserve (positionCut base h ps) ≤ M) :
    (∑ i ∈ Finset.range ps.length, positionCutExcess φ P reserve base h ps i) ≤
      splitCoefficient*(M+e+e*(Real.log (w 0)-Real.log (w ps.length)))+M := by
  have hpower0 : 0 ≤ cutPower φ P reserve (positionCut base h (ps.take 0)) := by
    unfold cutPower
    apply List.sum_nonneg
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    have ha0 : 0 ≤ a := by
      have hh := cutMasses_positive φ (P := P+1) (reserve := reserve) (by linarith only [hP]) hr (positionCut base h (ps.take 0))
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
        exact add_nonneg (gapPrefix_nonnegative φ q.gap) hP
      · have heq := List.mem_singleton.mp ha
        rw [heq]
        exact add_nonneg (add_nonneg (gapPrefix_nonnegative φ _) hP) hr
    exact Real.rpow_nonneg ha0 nu
  have hbound := weighted_excess_chain_bound
    (fun i => cutPower φ P reserve (positionCut base h (ps.take i)))
    (fun i => cutLogProduct φ P reserve (positionCut base h (ps.take i))-center) w
    (positionCutExcess φ P reserve base h ps) ps.length split_coefficient_positive.le he hw hmono hlower
    (by simpa only [List.take_zero] using hupper) hpower0
    (by simpa only [List.take_length] using hfinal) (by
      intro i hi
      rw [hpivot i hi]
      unfold positionCutExcess
      ring)
  exact hbound

end
end StrongSilver
