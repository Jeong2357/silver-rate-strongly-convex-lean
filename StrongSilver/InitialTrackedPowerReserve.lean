-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ReservedCompressedCut
import StrongSilver.InitialCapSmallness
import StrongSilver.InitialCutPowerReserve
import StrongSilver.CappedCutPowerBound

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2400000

namespace InitialReservation

theorem tracked_phase_pivot_lower {κ B μ : ℝ} {C : ScheduleCut} (R : InitialReservation κ B μ C)
    (hpiv : ∀ q ∈ C.phases, B ≤ q.pivot) : ∀ q ∈ R.assembly.trackedPhases, B ≤ q.pivot := by
  intro q hq
  obtain ⟨z,hz,_,he⟩ := R.phase_data q (R.assembly.trackedPhases_sublist.subset hq)
  simpa only [← he] using hpiv z hz

/-- The scalar power/log floor gives one reserve per tracked phase,
without counting the artificial terminal factor of the compressed cut. -/
theorem compressed_initial_reserve {κ B μ P : ℝ} {C : ScheduleCut} (R : InitialReservation κ B μ C)
    (hμ : 0 < μ) (hcap : μ*B < 1) (hP : 0 < P) (hφB : P < cappedStep μ B B)
    (hpiv : ∀ q ∈ C.phases, B ≤ q.pivot) (hgap : ∀ q ∈ C.phases, ∀ b ∈ q.gap, b < B) :
    (R.assembly.trackedPhases.length : ℝ)*powerLogMinimum*(cappedStep μ B B-P)^nu ≤
      cutPower (cappedStep μ B) P 0 (closedCut B R.compressedSchedule)-P^nu-
      splitCoefficient*(cappedStep μ B B-P)^nu*
        (cutLogProduct (cappedStep μ B) P 0 (closedCut B R.compressedSchedule)-Real.log P) := by
  have he := R.compressed_closed_cut hpiv hgap
  have ht : (closedCut B R.compressedSchedule).terminal = [] := by rw [he]
  rw [cutPower_empty_terminal _ _ _ ht,cutLogProduct_empty_terminal _ ht,he]
  exact phase_initial_power_reserve (cappedStep_monotone hμ hcap) hP hφB R.assembly.trackedPhases
    (R.tracked_phase_pivot_lower hpiv)

/-- Small a preserves at least half the B^nu-weight of the original
selected pivots in the tracked part of the reservation. -/
theorem tracked_weight_lower {a κ B μ : ℝ} {C : ScheduleCut} (R : InitialReservation κ B μ C)
    (ha : 0 < a) (hamax : a ≤ 1/128) (hκ : 0 < κ) (hcap : 1 ≤ a*κ) (hB : 0 < B) (hBcap : B ≤ a*κ)
    (hgap : ∀ b ∈ C.unselected, 0 < b → b ≤ B) (hD : D κ C.word ≤ 1)
    (hsmall : 7*initialMarkedLogCoefficient a ≤ 1/2)
    (hmax : weightedCount C.word (a*κ) = (C.phases.length : ℝ)*B^nu) :
    weightedCount C.word (a*κ)/2 ≤ (R.assembly.trackedPhases.length : ℝ)*B^nu := by
  have hcount : (C.phases.length : ℝ) ≤ (R.assembly.trackedPhases.length : ℝ)+
      7*(badPhaseCount (initialPhaseTests κ) C.phases : ℝ) := by
    have hh := R.tracked_count
    have hl : R.assembly.trackedPhases.length = R.baseTracked.length := by rw [R.tracked_numbered,numberTrackedPhases_length]
    rw [← hl] at hh
    exact_mod_cast hh
  have hc := mul_le_mul_of_nonneg_right hcount (Real.rpow_pos_of_pos hB nu).le
  have hj := initial_marked_log_budget ha hamax hκ hcap hB hBcap C hgap hD
  have hBκ : B ≤ κ := by have hh := mul_le_mul_of_nonneg_right hamax hκ.le; nlinarith only [hBcap,hh,hκ]
  have hlog := Real.log_nonneg ((one_le_div hB).mpr hBκ)
  have hj0 : 0 ≤ B^nu*(badPhaseCount (initialPhaseTests κ) C.phases : ℝ) := by positivity
  have hl := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1+Real.log (κ/B) by linarith only [hlog]) hj0
  have hw := mul_le_mul_of_nonneg_left hsmall (weightedCount_nonneg C.word (a*κ))
  change B^nu*(badPhaseCount (initialPhaseTests κ) C.phases : ℝ)*(1+Real.log (κ/B)) ≤
    weightedCount C.word (a*κ)*initialMarkedLogCoefficient a at hj
  rw [← hmax] at hc
  linear_combination hc+7*hj+7*hl+hw

theorem initial_reserve_lower {a κ B μ P : ℝ} {C : ScheduleCut} (R : InitialReservation κ B μ C)
    (ha : 0 < a) (hamax : a ≤ 1/128) (hκ : 0 < κ) (hcap : 1 ≤ a*κ) (hB : 0 < B) (hBcap : B ≤ a*κ)
    (hμ : 0 < μ) (hμB : μ*B < 1) (hP : P ≤ B/2)
    (hgap : ∀ b ∈ C.unselected, 0 < b → b ≤ B) (hD : D κ C.word ≤ 1)
    (hsmall : 7*initialMarkedLogCoefficient a ≤ 1/2)
    (hmax : weightedCount C.word (a*κ) = (C.phases.length : ℝ)*B^nu) :
    (powerLogMinimum/4)*weightedCount C.word (a*κ) ≤
      (R.assembly.trackedPhases.length : ℝ)*powerLogMinimum*(cappedStep μ B B-P)^nu := by
  have ht := R.tracked_weight_lower ha hamax hκ hcap hB hBcap hgap hD hsmall hmax
  have hφ := cappedStep_ge hμ hμB B
  have hp := half_scale_power_lower hB (show B/2 ≤ cappedStep μ B B-P by linarith only [hφ,hP])
  have hscale := mul_le_mul_of_nonneg_left hp (show 0 ≤ (R.assembly.trackedPhases.length : ℝ)*powerLogMinimum by
    have hh := powerLogMinimum_positive
    positivity)
  have hweight := mul_le_mul_of_nonneg_left ht powerLogMinimum_positive.le
  nlinarith only [hscale,hweight]

end InitialReservation
end
end StrongSilver
