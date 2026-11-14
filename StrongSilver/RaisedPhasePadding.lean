-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingScalarHeight

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1400000

def raisedPhasePadding (A s Z H : ℝ) : ℝ := A^(10 : ℝ)*(1+(Z+H)/s)

theorem raisedPhasePadding_positive {A s Z H : ℝ} (hA : 0 < A) (hs : 0 < s)
    (hZ : 0 ≤ Z) (hH : 0 ≤ H) : 0 < raisedPhasePadding A s Z H := by
  unfold raisedPhasePadding
  exact mul_pos (Real.rpow_pos_of_pos hA _) (by have := div_nonneg (add_nonneg hZ hH) hs.le; linarith)

theorem raisedPhasePadding_lower {A s Z H : ℝ} (hA : 1 ≤ A) (hs : 0 < s)
    (hZ : 0 ≤ Z) (hH : 0 ≤ H) : A^((49 : ℝ)/50) ≤ raisedPhasePadding A s Z H := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hh : A^(10 : ℝ) ≤ raisedPhasePadding A s Z H := by
    have hratio : 1 ≤ 1+(Z+H)/s := by have := div_nonneg (add_nonneg hZ hH) hs.le; linarith
    have hm := mul_le_mul_of_nonneg_left hratio (Real.rpow_pos_of_pos hA0 (10 : ℝ)).le
    simpa only [mul_one,raisedPhasePadding] using hm
  exact (Real.rpow_le_rpow_of_exponent_le hA (by norm_num)).trans hh

theorem eventually_raised_phase_height_cost : ∀ᶠ A : ℝ in atTop,
    ∀ s Z H r C R Ja : ℝ, 0 < s → 0 ≤ Z → 0 ≤ H → r ≤ 2 → C ≤ A^(5 : ℝ) →
      0 ≤ R → ((1 : ℝ)/1024)*A^(-(16 : ℝ)/125)*(R+raisedPhasePadding A s Z H) ≤ Ja →
      2*(r*Z/s+C*H/s) ≤ Ja := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_const_mul_power_le (by norm_num : (5 : ℝ) < 1234/125) 4096] with A hA hpow
  intro s Z H r C R Ja hs hZ hH hr hC hR hJa
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hratio : 0 ≤ (Z+H)/s := div_nonneg (add_nonneg hZ hH) hs.le
  have hpow5 : 1 ≤ A^(5 : ℝ) := Real.one_le_rpow hA (by norm_num)
  have hrA : r ≤ 2*A^(5 : ℝ) := by linarith only [hr,hpow5]
  have hCA : C ≤ 2*A^(5 : ℝ) := hC.trans (by have := (Real.rpow_pos_of_pos hA0 (5 : ℝ)).le; linarith)
  have h1 := mul_le_mul_of_nonneg_right hrA hZ
  have h2 := mul_le_mul_of_nonneg_right hCA hH
  have hcost : r*Z/s+C*H/s ≤ 2*A^(5 : ℝ)*((Z+H)/s) := by
    calc
      _ = (r*Z+C*H)/s := by ring
      _ ≤ (2*A^(5 : ℝ)*(Z+H))/s := div_le_div_of_nonneg_right (by nlinarith only [h1,h2]) hs.le
      _ = _ := by ring
  have hpowR := mul_le_mul_of_nonneg_right hpow hratio
  have hpower : A^(-(16 : ℝ)/125)*A^(10 : ℝ) = A^((1234 : ℝ)/125) := by
    rw [← Real.rpow_add hA0]; congr 1; norm_num
  have hRP := mul_le_mul_of_nonneg_left (show raisedPhasePadding A s Z H ≤ R+raisedPhasePadding A s Z H by linarith)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/1024) (Real.rpow_pos_of_pos hA0 (-(16 : ℝ)/125)).le)
  have hpad : ((1 : ℝ)/1024)*A^(-(16 : ℝ)/125)*raisedPhasePadding A s Z H =
      ((1 : ℝ)/1024)*A^((1234 : ℝ)/125)*(1+(Z+H)/s) := by
    unfold raisedPhasePadding
    rw [← hpower]
    ring
  rw [hpad] at hRP
  have hp0 : 0 ≤ A^((1234 : ℝ)/125) := (Real.rpow_pos_of_pos hA0 _).le
  nlinarith only [hcost,hpowR,hRP,hJa,hp0]

end
end StrongSilver
