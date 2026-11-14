-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Tactic

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

/-- An affine ray with a sufficiently large intercept is dominated by
the positive-part retained height estimate. -/
theorem retained_affine_plane_bound {u N Z ζ b T K H d : ℝ}
    (hN : 0 ≤ N) (hb : 0 ≤ b) (hT : 0 < T) (hK : 0 < K) (hH : 0 < H)
    (hζ : K*Z ≤ ζ) (hslope : 8*H*b ≤ T*K)
    (hheight : max (u-Z*N) 0/(8*H) ≤ d) :
    b*u/(T*K)-N*b*ζ/(T*K^2) ≤ d := by
  have hTK : 0 < T*K := mul_pos hT hK
  have h8H : 0 < 8*H := mul_pos (by norm_num) hH
  have hprice : 0 ≤ b/(T*K) := div_nonneg hb hTK.le
  have hoff : Z ≤ ζ/K := (le_div_iff₀ hK).mpr (by nlinarith only [hζ])
  have hlinear : u-(ζ/K)*N ≤ max (u-Z*N) 0 :=
    (sub_le_sub_left (mul_le_mul_of_nonneg_right hoff hN) u).trans (le_max_left _ _)
  have hcoeff : b/(T*K) ≤ 1/(8*H) :=
    (div_le_div_iff₀ hTK h8H).mpr (by nlinarith only [hslope])
  have h1 := mul_le_mul_of_nonneg_left hlinear hprice
  have h2 := mul_le_mul_of_nonneg_right hcoeff (le_max_right (u-Z*N) 0)
  have he : b*u/(T*K)-N*b*ζ/(T*K^2) = b/(T*K)*(u-(ζ/K)*N) := by
    field_simp
    <;> ring
  rw [he]
  have he2 : (1/(8*H))*max (u-Z*N) 0 = max (u-Z*N) 0/(8*H) := by ring
  rw [he2] at h2
  exact (h1.trans h2).trans hheight

theorem retained_negative_axis_plane_bound {u N a ζ T K d : ℝ}
    (hu : 0 ≤ u) (hN : 0 ≤ N) (ha : 0 ≤ a) (hζ : 0 ≤ ζ)
    (hT : 0 < T) (hK : 0 < K) (hd : 0 ≤ d) :
    -u/(T*K)-N*a*ζ/(T*K^2) ≤ d := by
  have h1 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) (mul_pos hT hK).le
  have h2 := div_nonneg (mul_nonneg (mul_nonneg hN ha) hζ) (mul_pos hT (sq_pos_of_pos hK)).le
  linarith only [h1,h2,hd]

end
end StrongSilver
