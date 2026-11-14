-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Scalar.SilverConstants
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope

namespace StrongSilver.Scalar.Silver
open Set
noncomputable section
set_option maxHeartbeats 800000

def scalarPotential (x : ℝ) : ℝ := x^nu-coefficient*Real.log x
def scalarFirst (x : ℝ) : ℝ := (nu*x^nu-coefficient)/x
def scalarSecond (x : ℝ) : ℝ := (coefficient-nu*(1-nu)*x^nu)/x^2

theorem scalarPotential_derivative (x : ℝ) (hx : 0 < x) :
    HasDerivAt scalarPotential (scalarFirst x) x := by
  have h := (Real.hasDerivAt_rpow_const (p := nu) (Or.inl hx.ne')).sub
    ((Real.hasDerivAt_log hx.ne').const_mul coefficient)
  convert! h using 1 <;> try rfl
  unfold scalarFirst
  rw [Real.rpow_sub_one hx.ne']
  try dsimp only [id_eq]
  field_simp [hx.ne'] <;> ring

theorem scalarFirst_derivative (x : ℝ) (hx : 0 < x) : HasDerivAt scalarFirst (scalarSecond x) x := by
  have h := (((Real.hasDerivAt_rpow_const (p := nu) (Or.inl hx.ne')).const_mul nu).sub_const coefficient).div
    (hasDerivAt_id x) hx.ne'
  convert! h using 1 <;> try rfl
  unfold scalarSecond
  rw [Real.rpow_sub_one hx.ne']
  try dsimp only [id_eq]
  field_simp [hx.ne'] <;> ring

/-- The strictly positive lower bound used to exclude boundary minima. -/
theorem scalarPotential_lower (x : ℝ) (hx : 0 < x) : minimum ≤ scalarPotential x := by
  let d := 2-Real.sqrt 2
  have hd : 0 < d := by dsimp [d]; linarith [sqrt_two_bounds.2]
  have hxpow := Real.rpow_pos_of_pos hx nu
  have hlog := Real.log_le_sub_one_of_pos (div_pos hxpow hd)
  rw [Real.log_div hxpow.ne' hd.ne',Real.log_rpow hx] at hlog
  have hid : d*(x^nu/d)=x^nu := by field_simp
  unfold minimum scalarPotential coefficient
  change d*(1-Real.log d) ≤ x^nu-nu*d*Real.log x
  nlinarith [mul_le_mul_of_nonneg_left hlog hd.le]

/-- The second derivative has at most one positive zero. -/
theorem scalarSecond_zero_unique (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hfa : scalarSecond a=0) (hfb : scalarSecond b=0) : a=b := by
  have hA : coefficient-nu*(1-nu)*a^nu=0 := by
    have h := (div_eq_zero_iff).mp hfa
    exact h.resolve_right (pow_ne_zero _ ha.ne')
  have hB : coefficient-nu*(1-nu)*b^nu=0 := by
    have h := (div_eq_zero_iff).mp hfb
    exact h.resolve_right (pow_ne_zero _ hb.ne')
  have hcoef : 0 < nu*(1-nu) := mul_pos nu_positive (by linarith [nu_lt_one])
  have heq : a^nu=b^nu := by nlinarith
  rcases lt_trichotomy a b with hab | hab | hab
  · have hlt := Real.rpow_lt_rpow ha.le hab nu_positive
    linarith
  · exact hab
  · have hlt := Real.rpow_lt_rpow hb.le hab nu_positive
    linarith

/-- Three distinct positive points cannot have the same first derivative.
This supplies the stationary-point reduction without an assumed shape oracle. -/
theorem scalarFirst_no_three (a b c : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (h1 : scalarFirst a=scalarFirst b) (h2 : scalarFirst b=scalarFirst c) : False := by
  have hcont (u v : ℝ) (hu : 0 < u) : ContinuousOn scalarFirst (Icc u v) := by
    intro x hx
    exact (scalarFirst_derivative x (hu.trans_le hx.1)).continuousAt.continuousWithinAt
  obtain ⟨x,hx,hzx⟩ := exists_hasDerivAt_eq_zero hab (hcont a b ha) h1
    (fun x hx => scalarFirst_derivative x (ha.trans hx.1))
  obtain ⟨y,hy,hzy⟩ := exists_hasDerivAt_eq_zero hbc (hcont b c (ha.trans hab)) h2
    (fun y hy => scalarFirst_derivative y ((ha.trans hab).trans hy.1))
  have heq := scalarSecond_zero_unique x y (ha.trans hx.1) ((ha.trans hab).trans hy.1) hzx hzy
  linarith [hx.2,hy.1]

theorem stationary_pair_diagonal (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : scalarFirst a=scalarFirst (a+b+1))
    (h2 : scalarFirst b=scalarFirst (a+b+1)) : a=b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact False.elim (scalarFirst_no_three a b (a+b+1) ha hab (by linarith) (h1.trans h2.symm) h2)
  · exact hab
  · exact False.elim (scalarFirst_no_three b a (a+b+1) hb hab (by linarith) (h2.trans h1.symm) h1)

end
end StrongSilver.Scalar.Silver
