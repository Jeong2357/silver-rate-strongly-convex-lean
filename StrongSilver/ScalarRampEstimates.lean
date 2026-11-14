-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScalarRampBudgets
import StrongSilver.ScalarRampParameters

namespace StrongSilver
open Set Real
noncomputable section
set_option maxHeartbeats 1000000

def scalarRampGrowth (T A b : ℝ) (h : List ℝ) : ℝ :=
  Real.exp (Scalar.SignedIntervals.positiveMass h/(T*(1-A/T)))*
    (1+Scalar.SignedIntervals.positiveMass h/b)

namespace ScalarRamp
variable (R : ScalarRamp)

theorem source_lower_exp {T : ℝ} (hT : 0 < T) (hbase : R.base = 1/T)
    (h : List ℝ) (x y : ℝ) (hyv : R.threshold ≤ y)
    (hend : iterate h R.physical x = y)
    (hstates : ∀ i : ℕ, i ≤ h.length → 0 < iterate (h.take i) R.physical x) :
    R.threshold*Real.exp (-negativeLogSum h T) ≤ x := by
  have hh := R.trajectory_lower h x y hend hstates
  rw [min_eq_right hyv,hbase,scalarNegativeProduct_eq_exp hT] at hh
  have hm := mul_le_mul_of_nonneg_left (min_le_left x R.threshold) (Real.exp_pos (negativeLogSum h T)).le
  have hbound : R.threshold ≤ Real.exp (negativeLogSum h T)*x := hh.trans hm
  have hd : R.threshold/Real.exp (negativeLogSum h T) ≤ x := (div_le_iff₀ (Real.exp_pos _)).mpr (by nlinarith only [hbound])
  simpa only [div_eq_mul_inv,Real.exp_neg] using hd

theorem source_upper_exp {T A b e : ℝ} (hT : 0 < T) (hb : 0 < b) (hAT : A < T)
    (hbase : R.base = 1/T) (ha : R.amplitude ≤ e/b) (h : List ℝ)
    (hh : ∀ c ∈ h, 0 < c → c ≤ A) (x : ℝ)
    (hend : iterate h R.physical x = e)
    (hstates : ∀ i : ℕ, i ≤ h.length → 0 < iterate (h.take i) R.physical x) :
    x ≤ scalarRampGrowth T A b h*e := by
  have hsmall : (1/T)*A < 1 := by
    have ht := (div_lt_one hT).mpr hAT
    simpa only [div_eq_mul_inv,one_mul,mul_one,mul_comm] using ht
  have hall : ∀ c ∈ h, R.base*c < 1 := by
    intro c hc
    rw [hbase]
    by_cases hcp : 0 < c
    · have hm := mul_le_mul_of_nonneg_left (hh c hc hcp) (one_div_pos.mpr hT).le
      exact hm.trans_lt hsmall
    · have hm := mul_nonpos_of_nonneg_of_nonpos (one_div_pos.mpr hT).le (le_of_not_gt hcp)
      linarith only [hm]
  have hu := R.trajectory_upper h hall x e hend hstates
  have hp := scalarBackwardProduct_exp_bound (one_div_pos.mpr hT).le hsmall h hh
  rw [← hbase] at hp
  have he : 0 < e := by
    have hs := hstates h.length (le_refl _)
    simpa only [List.take_length,hend] using hs
  have hmass := Scalar.SignedIntervals.positiveMass_nonneg h
  have hmul := mul_le_mul_of_nonneg_right ha hmass
  have hnum : 0 ≤ e+R.amplitude*Scalar.SignedIntervals.positiveMass h :=
    add_nonneg he.le (mul_nonneg R.amplitude_nonnegative hmass)
  have hprod := mul_le_mul_of_nonneg_right hp hnum
  have ha' := mul_le_mul_of_nonneg_left hmul (Real.exp_pos ((1/T)*Scalar.SignedIntervals.positiveMass h/(1-(1/T)*A))).le
  have heq : R.base*Scalar.SignedIntervals.positiveMass h/(1-R.base*A) =
      Scalar.SignedIntervals.positiveMass h/(T*(1-A/T)) := by
    rw [hbase]
    simp only [div_eq_mul_inv,mul_inv_rev,one_mul]
    ring
  rw [← hbase] at ha'
  rw [heq] at hprod ha'
  unfold scalarRampGrowth
  simp only [div_eq_mul_inv] at hu hprod ha' ⊢
  nlinarith only [hu,hprod,ha']

theorem contraction_slope_upper {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (hμb : μ ≤ R.base)
    (hμhalf : μ ≤ 1/2) {x : ℝ} (hx : 0 ≤ x) :
    (R.contraction hμ0 hμ1 hμb).g x ≤ 2*(R.base*x+R.amplitude) := by
  change (R.physical x-μ*x)/(1-μ) ≤ 2*(R.base*x+R.amplitude)
  apply (div_le_iff₀ (by linarith : 0 < 1-μ)).mpr
  have hp := (R.physical_positive_bounds hx).2
  have hμx := mul_nonneg hμ0 hx
  have hnonneg : 0 ≤ R.base*x+R.amplitude := add_nonneg (mul_nonneg R.base_nonnegative hx) R.amplitude_nonnegative
  have hm := mul_le_mul_of_nonneg_right hμhalf hnonneg
  nlinarith only [hp,hμx,hm]

end ScalarRamp
end
end StrongSilver
