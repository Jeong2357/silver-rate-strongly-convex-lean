-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WeightedCountProperties
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace StrongSilver
open Set MeasureTheory
noncomputable section

def clippedMass (h : List ℝ) (s : ℝ) : ℝ := (h.map (fun b => max 0 (min b s))).sum
def thresholdIndicator (b t : ℝ) : ℝ := if t ≤ b then 1 else 0

theorem real_countAbove_cons (b : ℝ) (h : List ℝ) (t : ℝ) :
    (countAbove (b::h) t : ℝ) = thresholdIndicator b t+(countAbove h t : ℝ) := by
  rw [countAbove_cons,Nat.cast_add]
  by_cases ht : t ≤ b <;> simp [thresholdIndicator,ht]

theorem countAbove_integrable (h : List ℝ) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => (countAbove h t : ℝ)) volume a b := by
  have hm : Antitone (fun t : ℝ => (countAbove h t : ℝ)) := by
    intro s t hst
    change (countAbove h t : ℝ) ≤ (countAbove h s : ℝ)
    exact_mod_cast countAbove_antitone h hst
  exact hm.intervalIntegrable

theorem thresholdIndicator_integrable (b a c : ℝ) :
    IntervalIntegrable (thresholdIndicator b) volume a c := by
  have hm : Antitone (thresholdIndicator b) := by
    intro s t hst
    by_cases hs : s ≤ b <;> by_cases ht : t ≤ b <;> simp [thresholdIndicator,hs,ht]
    exact False.elim (hs (hst.trans ht))
  exact hm.intervalIntegrable

theorem integral_thresholdIndicator (b : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ t in (0 : ℝ)..s, thresholdIndicator b t) = max 0 (min b s) := by
  let c := max 0 (min b s)
  have hc0 : 0 ≤ c := le_max_left _ _
  have hcs : c ≤ s := max_le hs.le (min_le_right _ _)
  have he : (∫ t in (0 : ℝ)..s, thresholdIndicator b t) =
      ∫ t in (0 : ℝ)..s, (Iic c).indicator (fun _ : ℝ => (1 : ℝ)) t := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    rw [uIoo_of_le hs.le] at ht
    have hiff : t ≤ b ↔ t ≤ c := by
      constructor
      · intro hb
        exact (le_min hb ht.2.le).trans (le_max_right _ _)
      · intro htc
        rcases (le_max_iff.mp htc) with ht0 | htmin
        · exact False.elim (not_le_of_gt ht.1 ht0)
        · exact htmin.trans (min_le_left _ _)
    simp only [thresholdIndicator,Set.indicator,Iic,mem_setOf_eq,hiff]
  rw [he]
  change (∫ t in (0 : ℝ)..s, ({t : ℝ | t ≤ c}).indicator (fun _ : ℝ => (1 : ℝ)) t) = _
  rw [intervalIntegral.integral_indicator (f := fun _ : ℝ => (1 : ℝ)) ⟨hc0,hcs⟩,
    intervalIntegral.integral_const]
  simp only [sub_zero,smul_eq_mul,mul_one]
  rfl

theorem clippedMass_eq_integral (h : List ℝ) {s : ℝ} (hs : 0 < s) :
    clippedMass h s = ∫ t in (0 : ℝ)..s, (countAbove h t : ℝ) := by
  induction h with
  | nil => simp [clippedMass]
  | cons b h ih =>
    simp only [clippedMass,List.map_cons,List.sum_cons] at *
    simp_rw [real_countAbove_cons]
    rw [intervalIntegral.integral_add (thresholdIndicator_integrable b 0 s) (countAbove_integrable h 0 s),
      integral_thresholdIndicator b hs,← ih]

theorem countAbove_rank_bound (h : List ℝ) {s cap : ℝ} (hs : 0 < s) (hcap : s ≤ cap) :
    (countAbove h s : ℝ) ≤ weightedCount h cap*s^(-nu) := by
  have hb := threshold_le_weightedCount h hs hcap
  rw [Real.rpow_neg hs.le,← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hs nu)).mpr
  simpa only [mul_comm] using hb

/-- Layer-cake bound (2.3), with the exact factor 1/(1-ν). -/
theorem clippedMass_rank_bound (h : List ℝ) {s cap : ℝ} (hs : 0 < s) (hcap : s ≤ cap) :
    clippedMass h s ≤ weightedCount h cap*s^(1-nu)/(1-nu) := by
  have hν : -1 < -nu := by linarith [nu_lt_one]
  have hi : IntervalIntegrable (fun t : ℝ => weightedCount h cap*t^(-nu)) volume 0 s :=
    (intervalIntegral.intervalIntegrable_rpow' hν).const_mul _
  have hI := intervalIntegral.integral_mono_on_of_le_Ioo hs.le (countAbove_integrable h 0 s) hi
    (fun t ht => countAbove_rank_bound h ht.1 (ht.2.le.trans hcap))
  rw [← clippedMass_eq_integral h hs,intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl hν)] at hI
  have he : -nu+1 = 1-nu := by ring
  have hn : 1-nu ≠ 0 := by linarith [nu_lt_one]
  rw [he,Real.zero_rpow hn,sub_zero] at hI
  simpa only [mul_div_assoc] using hI

end
end StrongSilver
