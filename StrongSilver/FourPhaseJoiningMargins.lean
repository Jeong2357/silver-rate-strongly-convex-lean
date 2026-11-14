-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Tactic

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 1500000

theorem retained_slope_margin {a H T k K : ℝ} (ha : a ≤ 9/40) (ha0 : 0 ≤ a)
    (hH : 0 ≤ H) (hT : 0 ≤ T) (hk : 0 ≤ k)
    (hβ : H ≤ T*k/2) (hK : (9/10:ℝ)*k ≤ K) : 8*H*a ≤ T*K := by
  have h1 := mul_le_mul_of_nonneg_right hβ ha0
  have h2 := mul_le_mul_of_nonneg_left ha (mul_nonneg hT hk)
  have h3 := mul_le_mul_of_nonneg_left hK hT
  nlinarith only [h1,h2,h3]

theorem retained_offset_margin {K k Z ζ : ℝ} (hK : K ≤ (11/10:ℝ)*k)
    (hk : 0 ≤ k) (hZ : 0 ≤ Z) (hζ : 2*k*Z ≤ ζ) : K*Z ≤ ζ := by
  have h1 := mul_le_mul_of_nonneg_right hK hZ
  have h2 : 0 ≤ k*Z := mul_nonneg hk hZ
  nlinarith only [h1,h2,hζ]

theorem gate_intercept_margin {a ζ η Q : ℝ} (ha : 1/8 ≤ a) (hζ : 0 ≤ ζ)
    (hη : 0 ≤ η) (hQ : Q ≤ 64) (hζeta : 512*η ≤ ζ) : η*Q ≤ a*ζ := by
  have h1 := mul_le_mul_of_nonneg_left hQ hη
  have h2 := mul_le_mul_of_nonneg_right ha hζ
  nlinarith only [h1,h2,hζeta]

/-- Numerical price of the old ray at a new query, paid by the actual
negative-step budget. -/
theorem retained_query_budget_margin {a H T k K N z d : ℝ}
    (hT : 0 < T) (hH : 0 < H) (hk : 0 < k) (hK : 0 ≤ K)
    (ha : 0 ≤ a) (ha2 : a ≤ 1/2) (hKupper : K ≤ (11/10:ℝ)*k)
    (hN : 0 ≤ N) (hNsmall : 1000*k*N ≤ H)
    (hz : max z 0 ≤ 2*a*N/T) (hd : 1/64 ≤ d) :
    (11*T*K/(10*H))*max z 0 ≤ d := by
  have hcoef : 0 ≤ 11*T*K/(10*H) := div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hT.le) hK) (mul_pos (by norm_num) hH).le
  have h1 := mul_le_mul_of_nonneg_left hz hcoef
  have h2 := mul_le_mul_of_nonneg_right hKupper hN
  have h3 := mul_le_mul_of_nonneg_left ha2 (mul_nonneg hK hN)
  have h4 : (11*T*K/(10*H))*(2*a*N/T) ≤ 1/64 := by
    have he : (11*T*K/(10*H))*(2*a*N/T) = (11/5:ℝ)*K*a*N/H := by
      field_simp
      <;> ring
    rw [he]
    apply (div_le_iff₀ hH).mpr
    nlinarith only [h2,h3,hNsmall,hH]
  exact (h1.trans h4).trans hd

end
end StrongSilver.FourPhase
