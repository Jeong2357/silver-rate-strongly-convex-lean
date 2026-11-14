-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SmallStepInverseCharge
import StrongSilver.ScheduleCut

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1000000

theorem log_one_add_nonnegative {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.log (1+x) :=
  Real.log_nonneg (by linarith only [hx])

theorem log_one_add_subadditive {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.log (1+(x+y)) ≤ Real.log (1+x)+Real.log (1+y) := by
  have hx1 : 0 < 1+x := by linarith only [hx]
  have hy1 : 0 < 1+y := by linarith only [hy]
  rw [← Real.log_mul hx1.ne' hy1.ne']
  exact Real.log_le_log (by linarith only [hx,hy]) (by nlinarith only [mul_nonneg hx hy])

theorem log_one_add_sum (xs : List ℝ) (hxs : ∀ x ∈ xs, 0 ≤ x) :
    Real.log (1+xs.sum) ≤ (xs.map fun x => Real.log (1+x)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have ht : ∀ z ∈ xs, 0 ≤ z := fun z hz => hxs z (List.mem_cons_of_mem x hz)
    simp only [List.sum_cons,List.map_cons]
    exact (log_one_add_subadditive hx (List.sum_nonneg ht)).trans
      (add_le_add le_rfl (ih ht))

/-- A large gap is charged by one cutoff logarithm and its normalized mass. -/
theorem log_one_add_mass_budget {x L : ℝ} (hx : 0 ≤ x) (hL : 0 < L) :
    Real.log (1+x) ≤ Real.log (1+L)+x/L := by
  have hxL : 0 ≤ x/L := div_nonneg hx hL.le
  have hprod : 1+x ≤ (1+L)*(1+x/L) := by
    have he : L*(x/L) = x := by field_simp
    nlinarith only [he,hL,hxL]
  have hh := Real.log_le_log (by linarith only [hx] : 0 < 1+x) hprod
  rw [Real.log_mul (by positivity) (by positivity)] at hh
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1+x/L by linarith only [hxL])
  linarith only [hh,hlog]

def phaseGrowthCharge (q : CutPhase) : ℝ :=
  Real.log (1+Scalar.SignedIntervals.positiveMass q.gap)+Real.log (1+max q.pivot 0)

theorem phaseGrowthCharge_nonnegative (q : CutPhase) : 0 ≤ phaseGrowthCharge q :=
  add_nonneg (log_one_add_nonnegative (Scalar.SignedIntervals.positiveMass_nonneg q.gap))
    (log_one_add_nonnegative (le_max_right q.pivot 0))

theorem log_one_add_phase_mass (q : CutPhase) :
    Real.log (1+Scalar.SignedIntervals.positiveMass q.word) ≤ phaseGrowthCharge q := by
  have hh := log_one_add_subadditive (Scalar.SignedIntervals.positiveMass_nonneg q.gap) (le_max_right q.pivot 0)
  simpa [CutPhase.word,Scalar.SignedIntervals.positiveMass_append,Scalar.SignedIntervals.positiveMass,phaseGrowthCharge] using hh

theorem log_one_add_phases_mass (qs : List CutPhase) :
    Real.log (1+Scalar.SignedIntervals.positiveMass (qs.flatMap CutPhase.word)) ≤ (qs.map phaseGrowthCharge).sum := by
  induction qs with
  | nil => simp [Scalar.SignedIntervals.positiveMass]
  | cons q qs ih =>
    rw [List.flatMap_cons,Scalar.SignedIntervals.positiveMass_append]
    exact (log_one_add_subadditive (Scalar.SignedIntervals.positiveMass_nonneg q.word)
      (Scalar.SignedIntervals.positiveMass_nonneg _)).trans (add_le_add (log_one_add_phase_mass q) ih)

theorem log_one_add_block_mass (μ : ℝ) (qs : List CutPhase) (gap : List ℝ) :
    Real.log (1+smallPositiveSum μ (qs.flatMap CutPhase.word++gap)) ≤
      (qs.map phaseGrowthCharge).sum+Real.log (1+Scalar.SignedIntervals.positiveMass gap) := by
  have hm := Real.log_le_log (by linarith only [smallPositiveSum_nonneg μ (qs.flatMap CutPhase.word++gap)] :
    0 < 1+smallPositiveSum μ (qs.flatMap CutPhase.word++gap))
    (add_le_add le_rfl (smallPositiveSum_le_positiveMass μ _))
  rw [Scalar.SignedIntervals.positiveMass_append] at hm
  exact hm.trans ((log_one_add_subadditive (Scalar.SignedIntervals.positiveMass_nonneg _)
    (Scalar.SignedIntervals.positiveMass_nonneg _)).trans (add_le_add (log_one_add_phases_mass qs) le_rfl))

end
end StrongSilver
