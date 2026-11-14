-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.QuadraticLogs
import StrongSilver.ErrorBounds

namespace StrongSilver
open Set MeasureTheory Filter
noncomputable section

def scheduleLog (h : List ℝ) (s t : ℝ) : ℝ :=
  (h.map (fun b => Real.log (1-(t/s)*b))).sum

theorem step_log_integrable (b s : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log (1-(t/s)*b)) volume 2 4 := by
  convert! quadratic_log_integrable (b/s) 2 4 using 1
  ext t
  congr 1
  ring

theorem schedule_log_integrable (h : List ℝ) (s : ℝ) :
    IntervalIntegrable (scheduleLog h s) volume 2 4 := by
  induction h with
  | nil =>
    change IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 2 4
    exact intervalIntegrable_const
  | cons b h ih =>
    change IntervalIntegrable (fun t : ℝ => Real.log (1-(t/s)*b)+scheduleLog h s t) volume 2 4
    exact (step_log_integrable b s).add ih

theorem integral_schedule_log (h : List ℝ) (s : ℝ) :
    (∫ t in (2 : ℝ)..4, scheduleLog h s t) = (h.map (fun b => quadraticLogIntegral (b/s))).sum := by
  induction h with
  | nil => simp [scheduleLog]
  | cons b h ih =>
    change (∫ t in (2 : ℝ)..4, Real.log (1-(t/s)*b)+scheduleLog h s t) =
      quadraticLogIntegral (b/s)+(h.map (fun a => quadraticLogIntegral (a/s))).sum
    rw [intervalIntegral.integral_add (step_log_integrable b s) (schedule_log_integrable h s),ih]
    congr 1
    unfold quadraticLogIntegral
    apply intervalIntegral.integral_congr
    intro t ht
    congr 1
    ring

theorem step_factors_ae_nonzero (h : List ℝ) (s : ℝ) :
    ∀ᵐ t : ℝ ∂volume, ∀ b ∈ h, 1-(t/s)*b ≠ 0 := by
  induction h with
  | nil => simp
  | cons b h ih =>
    have hb : ∀ᵐ t : ℝ ∂volume, 1-(t/s)*b ≠ 0 := by
      by_cases hz : b/s = 0
      · apply Eventually.of_forall
        intro t
        have he : (t/s)*b = t*(b/s) := by ring
        simp [he,hz]
      · filter_upwards [volume.ae_ne (1/(b/s))] with t ht
        intro he
        apply ht
        apply (eq_div_iff hz).mpr
        have hid : (t/s)*b = t*(b/s) := by simp only [div_eq_mul_inv]; ring
        rw [hid] at he
        nlinarith only [he]
    filter_upwards [hb,ih] with t hb hh
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hb
    · exact hh a ha

theorem log_quadraticMultiplier (h : List ℝ) (s t : ℝ)
    (hh : ∀ b ∈ h, 1-(t/s)*b ≠ 0) :
    Real.log (quadraticMultiplier (t/s) h) = scheduleLog h s t := by
  have hn : ∀ z ∈ h.map (fun b => 1-(t/s)*b), z ≠ 0 := by
    intro z hz
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hz
    exact hh b hb
  simpa only [quadraticMultiplier,scheduleLog,List.map_map,Function.comp_def] using Real.log_list_prod hn

theorem schedule_log_le_distance {κ s t : ℝ} (hκ : 1 < κ) (hs : 4 ≤ s) (hsκ : s ≤ κ)
    (ht : t ∈ Icc (2 : ℝ) 4) (h : List ℝ) (hh : ∀ b ∈ h, 1-(t/s)*b ≠ 0) :
    scheduleLog h s t ≤ Real.log (D κ h).toReal/2 := by
  have hκpos : 0 < κ := lt_trans zero_lt_one hκ
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have ht1 : 1 ≤ t := by linarith [ht.1]
  have hlow : 1/κ ≤ t/s := by
    apply (div_le_div_iff₀ hκpos hspos).mpr
    nlinarith only [hsκ,mul_le_mul_of_nonneg_right ht1 hκpos.le]
  have hhigh : t/s ≤ 1 := (div_le_one hspos).mpr (ht.2.trans hs)
  have hq := quadratic_distance_lower κ (t/s) hκpos hlow hhigh h
  have hqr := ENNReal.toReal_mono (D_ne_top κ h) hq
  rw [ENNReal.toReal_ofReal (sq_nonneg _)] at hqr
  have hqn : quadraticMultiplier (t/s) h ≠ 0 := by
    apply List.prod_ne_zero
    intro hz
    obtain ⟨b,hb,he⟩ := List.mem_map.mp hz
    exact hh b hb he
  have hlog := Real.log_le_log ((sq_pos_iff).mpr hqn) hqr
  rw [Real.log_pow,log_quadraticMultiplier h s t hh] at hlog
  norm_num at hlog
  linarith

/-- The common-curvature averaging inequality behind (2.4), before the rank estimate. -/
theorem scalar_quadratic_log_average {κ s : ℝ} (hκ : 1 < κ) (hs : 4 ≤ s) (hsκ : s ≤ κ)
    (h : List ℝ) :
    (h.map (fun b => quadraticLogIntegral (b/s))).sum ≤ Real.log (D κ h).toReal := by
  have hae : ∀ᵐ t : ℝ ∂volume.restrict (Icc (2 : ℝ) 4),
      scheduleLog h s t ≤ Real.log (D κ h).toReal/2 := by
    have hn := (ae_mono (Measure.restrict_le_self (μ := volume) (s := Icc (2 : ℝ) 4)))
      (step_factors_ae_nonzero h s)
    filter_upwards [ae_restrict_mem measurableSet_Icc,hn] with t ht hh
    exact schedule_log_le_distance hκ hs hsκ ht h hh
  have hI := intervalIntegral.integral_mono_ae_restrict (by norm_num : (2 : ℝ) ≤ 4)
    (schedule_log_integrable h s)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Real.log (D κ h).toReal/2) volume 2 4) hae
  rw [integral_schedule_log,intervalIntegral.integral_const] at hI
  norm_num [smul_eq_mul] at hI
  linarith only [hI]

end
end StrongSilver
