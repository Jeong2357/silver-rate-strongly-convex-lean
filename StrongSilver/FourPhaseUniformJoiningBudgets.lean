-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseLastRelativeError

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 3000000

/-- Strong finite exterior-time bounds with ample fixed margins for
joining adjacent depth groups. They allow the capped exterior transform. -/
theorem last_excess_strong_scale {μ T b d φ k : ℝ} (hμ : 0 < μ) (hT : 0 < T)
    (hb : 100 ≤ b) (hd : 0 ≤ d) (hdb : d ≤ b/100) (hsmall : μ*b ≤ 1/10000)
    (hφ : b ≤ φ) (hφerror : φ-b ≤ 2*μ*b^2)
    (herror : |T*k-(b-1-d)| ≤ μ*d^2+2*μ*b*d) :
    (19/20:ℝ)*φ ≤ T*k ∧ T*k ≤ 2*b := by
  have hb0 : 0 < b := by linarith only [hb]
  obtain ⟨hK,hdev⟩ := last_excess_relative_error hμ hT (by linarith only [hb]) hd
    (by linarith only [hdb,hb]) hφ hφerror herror
  have hlo : (999/1000:ℝ) ≤ T*k/(φ-1-d) := by
    have hh := (abs_le.mp hdev).1
    linarith only [hh,hsmall]
  have hhi : T*k/(φ-1-d) ≤ (1001/1000:ℝ) := by
    have hh := (abs_le.mp hdev).2
    linarith only [hh,hsmall]
  have hp0 := (le_div_iff₀ hK).mp hlo
  have hp1 := (div_le_iff₀ hK).mp hhi
  have hKl : (49/50:ℝ)*b ≤ φ-1-d := by linarith only [hφ,hdb,hb]
  have hKu : φ-1-d ≤ φ := by linarith only [hd]
  have hsmallb := mul_le_mul_of_nonneg_right hsmall hb0.le
  have hφu : φ ≤ (5001/5000:ℝ)*b := by nlinarith only [hφerror,hsmallb]
  exact ⟨by nlinarith only [hp0,hKl,hφu,hb0],by nlinarith only [hp1,hKu,hφu,hb0]⟩

theorem joining_scale_condition {H T k φ : ℝ} (hφ : 0 ≤ φ)
    (hH : H ≤ (9/20:ℝ)*φ) (hk : (19/20:ℝ)*φ ≤ T*k) : H ≤ T*k/2 := by
  nlinarith only [hH,hk,hφ]

/-- A single uniform lower scale L and upper exterior scale U control
all first-three-gap negative budgets in the backwards construction. -/
theorem uniform_negative_join {N c L U H k : ℝ} (hN : 0 ≤ N) (hL : 0 < L)
    (hk : 0 < k) (hc : 0 ≤ c) (hH : L ≤ H) (hkU : L*k ≤ 2*U)
    (hbudget : 2*U*N ≤ c*L^2) : N ≤ c*H/k := by
  have hp := mul_le_mul_of_nonneg_left hkU hN
  have hNk : N*k ≤ c*L := (mul_le_mul_iff_right₀ hL).mp (by nlinarith only [hp,hbudget])
  have hHc := mul_le_mul_of_nonneg_left hH hc
  exact (le_div_iff₀ hk).mpr (hNk.trans hHc)

/-- Only the rightmost input offset is charged. This bound is uniform
in the group count and follows from the same two scale bounds. -/
theorem uniform_offset_join {Z Zmax c L U k : ℝ} (hZ : 0 ≤ Z) (hL : 0 < L)
    (hU : 0 ≤ U) (hkU : L*k ≤ 2*U) (hZmax : Z ≤ Zmax)
    (hbudget : 2*U*Zmax ≤ c*L) : k*Z ≤ c := by
  have hp := mul_le_mul_of_nonneg_right hkU hZ
  have hz := mul_le_mul_of_nonneg_left hZmax (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hU)
  exact (mul_le_mul_iff_right₀ hL).mp (by nlinarith only [hp,hz,hbudget])

end
end StrongSilver.FourPhase
