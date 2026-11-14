-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseMassTimeError

namespace StrongSilver.FourPhase
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2400000

theorem last_time_error {μ T b d p α : ℝ} (hμ : 0 < μ) (hT : 0 < T)
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hsmall : μ*d ≤ 1)
    (hp : p/α = (1-μ*b)*Real.exp (μ*d)) :
    |T*((1-p/α)/(μ*T)-1/T)-(b-1-d)| ≤ μ*d^2+2*μ*b*d := by
  have hu : |μ*d| ≤ 1 := by rw [abs_of_nonneg (mul_nonneg hμ.le hd)]; exact hsmall
  have hfirst := exp_quotient_error hμ hu
  have hsecond := Real.abs_exp_sub_one_le hu
  rw [abs_of_nonneg (mul_nonneg hμ.le hd)] at hsecond
  have he : T*((1-p/α)/(μ*T)-1/T)-(b-1-d) =
      -((Real.exp (μ*d)-1)/μ-d)+b*(Real.exp (μ*d)-1) := by
    rw [hp]
    field_simp [hμ.ne',hT.ne']
    <;> ring
  have hprice := mul_le_mul_of_nonneg_left hsecond hb
  have htriangle := abs_add_le (-((Real.exp (μ*d)-1)/μ-d)) (b*(Real.exp (μ*d)-1))
  rw [abs_neg,abs_mul,abs_of_nonneg hb] at htriangle
  rw [he]
  nlinarith only [hfirst,hprice,htriangle]

/-- The product divided by its minimum prefix product is exactly the
exponential of the transformed drawdown, for arbitrary signed gaps. -/
theorem gap_product_ratio_exp_drawdown {μ : ℝ} (hμ : 0 < μ) (h : List ℝ)
    (hh : ∀ b ∈ h, μ*b < 1) :
    quadraticMultiplier μ h/minPrefixProduct μ h =
      Real.exp (μ*drawdown (h.map (logarithmicStep μ))) := by
  have hq := quadraticMultiplier_positive h hh
  have hα := minPrefixProduct_positive h hh
  have he : μ*drawdown (h.map (logarithmicStep μ)) =
      Real.log (quadraticMultiplier μ h)-Real.log (minPrefixProduct μ h) := by
    unfold drawdown
    rw [transformed_prefix_max hμ h hh,logarithmicSteps_sum h hh]
    field_simp [hμ.ne']
    <;> ring
  rw [he,Real.exp_sub,Real.exp_log hq,Real.exp_log hα]

theorem last_phase_product_ratio {μ : ℝ} (hμ : 0 < μ)
    (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ)
    (hsmall : μ*absoluteMass (boundedWord gap pivot) ≤ 1/4) :
    quadraticMultiplier μ (phaseWord gap pivot 3)/minPrefixProduct μ (gap 3) =
      (1-μ*pivot 3)*Real.exp (μ*drawdown ((gap 3).map (logarithmicStep μ))) := by
  have hg := gap_small_steps hμ.le gap pivot hsmall 3
  have he := gap_product_ratio_exp_drawdown hμ (gap 3) hg
  change (quadraticMultiplier μ ((gap 3)++[pivot 3]))/_ = _
  rw [quadraticMultiplier_append]
  have hlast : quadraticMultiplier μ [pivot 3] = 1-μ*pivot 3 := by simp [quadraticMultiplier]
  rw [hlast,← he]
  ring

theorem actual_last_excess_error {μ T : ℝ} (hμ : 0 < μ) (hT : 0 < T)
    (gap : Fin 4 → List ℝ) (pivot : Fin 4 → ℝ)
    (hsmall : μ*absoluteMass (boundedWord gap pivot) ≤ 1/4) (hb : 0 ≤ pivot 3)
    (hdsmall : μ*drawdown ((gap 3).map (logarithmicStep μ)) ≤ 1) :
    |T*lastExcess μ T gap pivot-
      (pivot 3-1-drawdown ((gap 3).map (logarithmicStep μ)))| ≤
      μ*(drawdown ((gap 3).map (logarithmicStep μ)))^2+
      2*μ*pivot 3*drawdown ((gap 3).map (logarithmicStep μ)) :=
  last_time_error hμ hT hb (drawdown_nonneg _) hdsmall (last_phase_product_ratio hμ gap pivot hsmall)

end
end StrongSilver.FourPhase
