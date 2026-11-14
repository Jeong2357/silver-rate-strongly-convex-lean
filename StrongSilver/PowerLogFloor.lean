-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SplitLemma

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1400000

def powerLogMinimum : ℝ := Scalar.Silver.minimum

theorem powerLogMinimum_positive : 0 < powerLogMinimum := Scalar.Silver.minimum_positive

theorem power_log_floor {x : ℝ} (hx : 0 < x) : powerLogMinimum ≤ x^nu-splitCoefficient*Real.log x := by
  simpa only [powerLogMinimum,Scalar.Silver.scalarPotential,scalar_nu_eq,scalar_coefficient_eq] using
    Scalar.Silver.scalarPotential_lower x hx

/-- A positive lower bound at any reference scale, without an
arithmetic-geometric-mean relaxation. -/
theorem scaled_power_log_floor {x b : ℝ} (hx : 0 < x) (hb : 0 < b) :
    powerLogMinimum*b^nu ≤ x^nu-splitCoefficient*b^nu*Real.log (x/b) := by
  have hpow := Real.rpow_pos_of_pos hb nu
  have hh := mul_le_mul_of_nonneg_left (power_log_floor (div_pos hx hb)) hpow.le
  have he : b^nu*(x/b)^nu = x^nu := by
    rw [Real.div_rpow hx.le hb.le]
    field_simp
  nlinarith only [hh,he]

theorem sum_power_log_floor {b : ℝ} (hb : 0 < b) (xs : List ℝ) (hxs : ∀ x ∈ xs, 0 < x) :
    (xs.length : ℝ)*powerLogMinimum*b^nu ≤
      (xs.map fun x => x^nu).sum-splitCoefficient*b^nu*(xs.map fun x => Real.log (x/b)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have ht := ih (fun z hz => hxs z (List.mem_cons_of_mem x hz))
    have hh := scaled_power_log_floor hx hb
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith only [hh,ht]

/-- The initial product comparison gives a positive power reserve, as in
(3.33), when its denominator factors are at least the reference scale. -/
theorem initial_power_log_reserve {b L : ℝ} (hb : 0 < b) (xs : List ℝ) (hxs : ∀ x ∈ xs, 0 < x)
    (hL : L ≤ (xs.map fun x => Real.log (x/b)).sum) :
    (xs.length : ℝ)*powerLogMinimum*b^nu ≤ (xs.map fun x => x^nu).sum-splitCoefficient*b^nu*L := by
  have hh := sum_power_log_floor hb xs hxs
  have hscale := mul_le_mul_of_nonneg_left hL (mul_pos split_coefficient_positive (Real.rpow_pos_of_pos hb nu)).le
  linarith only [hh,hscale]

end
end StrongSilver
