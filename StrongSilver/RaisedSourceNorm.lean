-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingPaddingLinear
import StrongSilver.RaisedPhasePadding
import StrongSilver.AttachmentRatios

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1600000

theorem eventually_raised_source_norm : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T e P₀ s Z H : ℝ, ∀ h : List ℝ, OrdinaryPhaseParameters A μ b T P₀ h →
      ∀ L : LocalPhaseCertificate A μ b T e h, 0 < s → 0 ≤ Z → 0 ≤ H →
      e^2 = A^(-(3 : ℝ)/25)*T*(‖L.R‖+raisedPhasePadding A s Z H) →
      ‖L.path.x 0‖^2 ≤ A^(19 : ℝ)*(1+(Z+H)/s) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),eventually_working_padding_linear,
    eventually_const_mul_power_le (by norm_num : (18 : ℝ) < 19) 2] with A hA hnorm hpow
  intro μ b T e P₀ s Z H h W L hs hZ hH he
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hpad0 := raisedPhasePadding_positive hA0 hs hZ hH
  have hlocal := (hnorm μ b T e P₀ h W L (raisedPhasePadding A s Z H) hpad0.le he).2.2.2
  have hratio : 1 ≤ 1+(Z+H)/s := by have := div_nonneg (add_nonneg hZ hH) hs.le; linarith
  have hpad1 : 1 ≤ raisedPhasePadding A s Z H := by
    have hA10 : 1 ≤ A^(10 : ℝ) := Real.one_le_rpow hA (by norm_num)
    have hh := mul_le_mul hA10 hratio (by norm_num : (0 : ℝ) ≤ 1) (by linarith only [hA10] : 0 ≤ A^(10 : ℝ))
    dsimp only [raisedPhasePadding]
    nlinarith only [hh]
  have hlarge := mul_le_mul_of_nonneg_left (show 1+raisedPhasePadding A s Z H ≤ 2*raisedPhasePadding A s Z H by linarith only [hpad1])
    (Real.rpow_pos_of_pos hA0 (8 : ℝ)).le
  have hpower : A^(8 : ℝ)*A^(10 : ℝ) = A^(18 : ℝ) := by rw [← Real.rpow_add hA0]; norm_num
  have hscale := mul_le_mul_of_nonneg_right hpow (show 0 ≤ 1+(Z+H)/s by linarith only [hratio])
  have heq : A^(8 : ℝ)*(2*raisedPhasePadding A s Z H) =
      (2*A^(18 : ℝ))*(1+(Z+H)/s) := by
    unfold raisedPhasePadding
    rw [← hpower]
    ring
  rw [heq] at hlarge
  exact hlocal.trans (hlarge.trans hscale)

theorem scaled_raised_source_norm {A s U Z H N : ℝ} (hA : 0 < A) (hs : 0 < s)
    (hsU : s ≤ U) (hZ : 0 ≤ Z) (hH : 0 ≤ H)
    (hN : N ≤ A^(19 : ℝ)*(1+(Z+H)/s)) :
    s^2*N ≤ A^(19 : ℝ)*(U^2+U*Z+U*H) := by
  have hU : 0 < U := hs.trans_le hsU
  have hsq : s^2 ≤ U^2 := by nlinarith only [hsU,hs,hU]
  have hlin := mul_le_mul_of_nonneg_right hsU (add_nonneg hZ hH)
  have hbound : s^2+s*(Z+H) ≤ U^2+U*Z+U*H := by nlinarith only [hsq,hlin]
  have hscaled := mul_le_mul_of_nonneg_left hN (sq_nonneg s)
  have hpower := mul_le_mul_of_nonneg_left hbound (Real.rpow_pos_of_pos hA (19 : ℝ)).le
  have heq : s^2*(A^(19 : ℝ)*(1+(Z+H)/s)) = A^(19 : ℝ)*(s^2+s*(Z+H)) := by
    field_simp [hs.ne'] <;> ring
  rw [heq] at hscaled
  exact hscaled.trans hpower

end
end StrongSilver
