-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PowerMargins

namespace StrongSilver
open Real
noncomputable section

theorem power_times_le_scaled_square {A Q p r : ℝ} (hA : 0 < A) (hQ : A^p ≤ Q) :
    A^r*Q ≤ A^(r-p)*Q^2 := by
  have hQ0 : 0 ≤ Q := (Real.rpow_pos_of_pos hA p).le.trans hQ
  have hh := mul_le_mul_of_nonneg_left hQ (Real.rpow_pos_of_pos hA (r-p)).le
  have he : A^(r-p)*A^p = A^r := by rw [← Real.rpow_add hA]; congr 1; ring
  rw [he] at hh
  have hm := mul_le_mul_of_nonneg_right hh hQ0
  nlinarith only [hm]

theorem power_le_scaled_square {A Q p r : ℝ} (hA : 0 < A) (hQ : A^p ≤ Q) :
    A^r ≤ A^(r-2*p)*Q^2 := by
  have hQ0 : 0 ≤ Q := (Real.rpow_pos_of_pos hA p).le.trans hQ
  have hs : (A^p)^2 ≤ Q^2 := by nlinarith only [hQ,Real.rpow_pos_of_pos hA p,hQ0]
  have hh := mul_le_mul_of_nonneg_left hs (Real.rpow_pos_of_pos hA (r-2*p)).le
  have he : A^(r-2*p)*(A^p)^2 = A^r := by
    rw [← Real.rpow_mul_natCast hA.le,← Real.rpow_add hA]
    congr 1
    ring
  rwa [he] at hh

theorem power_product_three {A r s t : ℝ} (hA : 0 < A) : A^r*A^s*A^t = A^(r+s+t) := by
  rw [← Real.rpow_add hA,← Real.rpow_add hA]

end
end StrongSilver
