-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutMasses
import StrongSilver.LogProductReserve
import StrongSilver.ScheduleCutPartition

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

/-- One reference denominator for every gap, including the terminal reserve. -/
theorem cut_initial_power_reserve {φ : ℝ → ℝ} (hφ : Monotone φ) {B P reserve : ℝ}
    (hP : 0 < P) (hb : P < φ B) (hr : 0 < reserve) (hbr : φ B-P ≤ reserve)
    (C : ScheduleCut) (hpiv : ∀ q ∈ C.phases, B ≤ q.pivot) :
    ((C.phases.length : ℝ)+1)*powerLogMinimum*(φ B-P)^nu ≤
      cutPower φ P reserve C-splitCoefficient*(φ B-P)^nu*(cutLogProduct φ P reserve C-Real.log reserve) := by
  let ys := (C.phases.map fun q => φ q.pivot-P)++[reserve]
  have hy : ∀ y ∈ ys, φ B-P ≤ y := by
    intro y hy
    simp only [ys,List.mem_append,List.mem_map,List.mem_singleton] at hy
    rcases hy with ⟨q,hq,rfl⟩ | rfl
    · exact sub_le_sub_right (hφ (hpiv q hq)) P
    · exact hbr
  have hlen : (cutMasses φ P reserve C).length = ys.length := by
    simp only [cutMasses_length,ys,List.length_append,List.length_map,List.length_singleton]
  have hh := product_power_reserve (sub_pos.mpr hb) (cutMasses φ P reserve C) ys
    (cutMasses_positive φ hP hr.le C) hy hlen
  have he : (ys.map Real.log).sum =
      (C.phases.map fun q => Real.log (φ q.pivot-P)).sum+Real.log reserve := by
    simp only [ys,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,
      List.sum_nil,add_zero,List.map_map,Function.comp_def]
  rw [he,cutMasses_length,Nat.cast_add,Nat.cast_one] at hh
  simpa only [cutPower,cutLogProduct,sub_sub] using hh

theorem closed_cut_initial_power_reserve {φ : ℝ → ℝ} (hφ : Monotone φ) {B P reserve : ℝ}
    (hP : 0 < P) (hb : P < φ B) (hr : 0 < reserve) (hbr : φ B-P ≤ reserve) (h : List ℝ) :
    ((countAbove h B : ℝ)+1)*powerLogMinimum*(φ B-P)^nu ≤
      cutPower φ P reserve (closedCut B h)-splitCoefficient*(φ B-P)^nu*
        (cutLogProduct φ P reserve (closedCut B h)-Real.log reserve) := by
  simpa only [closedCut_count] using cut_initial_power_reserve hφ hP hb hr hbr (closedCut B h)
    (fun _ hq => closedCut_pivot hq)

/-- The tracked-only version has no terminal numerator or denominator. -/
theorem phase_initial_power_reserve {φ : ℝ → ℝ} (hφ : Monotone φ) {B P : ℝ}
    (hP : 0 < P) (hb : P < φ B) (qs : List CutPhase) (hpiv : ∀ q ∈ qs, B ≤ q.pivot) :
    (qs.length : ℝ)*powerLogMinimum*(φ B-P)^nu ≤
      (qs.map fun q => (gapPrefix φ q.gap+P)^nu).sum-splitCoefficient*(φ B-P)^nu*
        ((qs.map fun q => Real.log (gapPrefix φ q.gap+P)).sum-
          (qs.map fun q => Real.log (φ q.pivot-P)).sum) := by
  have hx : ∀ x ∈ qs.map (fun q => gapPrefix φ q.gap+P), 0 < x := by
    intro x hx
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx
    exact add_pos_of_nonneg_of_pos (gapPrefix_nonnegative φ q.gap) hP
  have hy : ∀ y ∈ qs.map (fun q => φ q.pivot-P), φ B-P ≤ y := by
    intro y hy
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hy
    exact sub_le_sub_right (hφ (hpiv q hq)) P
  have hh := product_power_reserve (sub_pos.mpr hb) _ _ hx hy (by simp only [List.length_map])
  simpa only [List.length_map,List.map_map,Function.comp_def] using hh

end
end StrongSilver
