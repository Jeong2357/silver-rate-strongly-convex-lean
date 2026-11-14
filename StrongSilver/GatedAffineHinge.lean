-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SupportTransport

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1000000

theorem gated_affine_le_hinge {β y C θ H B Δ : ℝ} (hθ : 0 ≤ θ) (hH : 0 ≤ H)
    (hβ : |β| ≤ H) (hC : θ*|β| ≤ C) (hHB : H ≤ B) (hΔ : Δ ≤ B*θ) :
    β*y-C ≤ max (B*|y|-Δ) 0 := by
  have habs := le_abs_self (β*y)
  rw [abs_mul] at habs
  have hl : β*y-C ≤ |β| * (|y|-θ) := by nlinarith only [habs,hC]
  by_cases hsmall : |y| ≤ θ
  · have hp := mul_nonpos_of_nonneg_of_nonpos (abs_nonneg β) (sub_nonpos.mpr hsmall)
    exact (by linarith only [hl,hp] : β*y-C ≤ 0).trans (le_max_right _ _)
  · have hδ : 0 ≤ |y|-θ := sub_nonneg.mpr (le_of_not_ge hsmall)
    have h1 := mul_le_mul_of_nonneg_right hβ hδ
    have h2 := mul_le_mul_of_nonneg_right hHB hδ
    have hh : β*y-C ≤ B*|y|-Δ := by nlinarith only [hl,h1,h2,hΔ]
    exact hh.trans (le_max_left _ _)

theorem SupportFamily.symmetric_gate_intercept {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type*} (F : SupportFamily ι V) (f : V) (V₀ η : ℝ)
    (hplus : F.Gate (V₀ • f) η) (hminus : F.Gate (V₀ • f) (-η)) (i : ι) :
    (η*V₀)*|inner ℝ f (F.g i)| ≤ inner ℝ (F.g i) (F.z i)-F.d i := by
  have hp := hplus i
  have hm := hminus i
  rw [inner_sub_right,real_inner_smul_right,real_inner_smul_right,real_inner_comm f (F.g i)] at hp hm
  by_cases hβ : 0 ≤ inner ℝ f (F.g i)
  · rw [abs_of_nonneg hβ]
    nlinarith only [hp]
  · rw [abs_of_neg (lt_of_not_ge hβ)]
    nlinarith only [hm]

end
end StrongSilver
