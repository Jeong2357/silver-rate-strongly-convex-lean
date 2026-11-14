-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Scalar.MaxPlusUnitStability
import StrongSilver.Scalar.PowerLogControl
import Mathlib.Analysis.MeanInequalitiesPow

namespace StrongSilver.Scalar.Silver
open Set
noncomputable section
set_option maxHeartbeats 1500000

def unitGain (a b z : ℝ) : ℝ := Real.log (z/(a*b))
def powerDefect (a b z : ℝ) : ℝ := a^nu+b^nu-z^nu

theorem unitExcess_formula (a b z : ℝ) (ha : 0 < a) (hb : 0 < b) (hz : 0 < z) :
    unitExcess a b z=powerDefect a b z+coefficient*unitGain a b z := by
  unfold unitExcess powerDefect unitGain scalarPotential
  rw [Real.log_div hz.ne' (mul_pos ha hb).ne',Real.log_mul ha.ne' hb.ne']
  ring

theorem unitGain_negative (a b z : ℝ) : -unitGain a b z=Real.log (a*b/z) := by
  unfold unitGain
  rw [← Real.log_inv,inv_div]

theorem powerDefect_lower (a b z : ℝ) (ha : 0 < a) (hb : 0 < b) (hz : z ≤ a+b+1) (hz0 : 0 ≤ z) :
    (1-nu)*(min a b)^nu-nu*(min a b)^(nu-1) ≤ powerDefect a b z := by
  have hordered (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hz : z ≤ a+b+1) :
      (1-nu)*a^nu-nu*a^(nu-1) ≤ powerDefect a b z := by
    have hb := ha.trans_le hab
    have hinc := power_increment a b ha hb
    have hpow := Real.rpow_le_rpow_of_nonpos ha hab (by linarith [nu_lt_one] : nu-1 ≤ 0)
    have h1 := mul_le_mul_of_nonneg_left hpow (mul_nonneg nu_positive.le (show 0 ≤ a+1 by linarith))
    have hzp := Real.rpow_le_rpow hz0 hz nu_positive.le
    have hid : a*a^(nu-1)=a^nu := by rw [Real.rpow_sub_one ha.ne']; field_simp
    unfold powerDefect
    nlinarith [congrArg (fun t : ℝ => nu*t) hid]
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    exact hordered a b ha hab hz
  · rw [min_eq_right hba]
    have h := hordered b a hb hba (by simpa only [add_comm] using hz)
    simpa only [powerDefect,add_comm] using h

theorem powerDefect_ge_neg_one (a b z : ℝ) (ha : 0 < a) (hb : 0 < b) (hz : z ≤ a+b+1) (hz0 : 0 ≤ z) :
    -1 ≤ powerDefect a b z := by
  have h1 := Real.rpow_add_le_add_rpow ha.le hb.le nu_positive.le nu_lt_one.le
  have h2 := Real.rpow_add_le_add_rpow (show 0 ≤ a+b by linarith) (by norm_num : (0 : ℝ) ≤ 1) nu_positive.le nu_lt_one.le
  have h3 := Real.rpow_le_rpow hz0 hz nu_positive.le
  rw [Real.one_rpow] at h2
  unfold powerDefect
  linarith

/-- The uniform absolute logarithmic-gain bound in the normalized excess lemma. -/
theorem unitGain_control : ∃ C > 0, ∀ a b z : ℝ, 0 < a → 0 < b → a ≤ z → z ≤ a+b+1 →
    |unitGain a b z| ≤ C*(1+unitExcess a b z) := by
  let d₁ := 1-(1/2 : ℝ)^nu
  have hd₁ : 0 < d₁ := sub_pos.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) nu_positive)
  have hd₂ : 0 < 1-nu := by linarith [nu_lt_one]
  obtain ⟨C₁,hC₁,hcontrol₁⟩ := log_twice_control d₁ hd₁
  obtain ⟨C₂,hC₂,hcontrol₂⟩ := log_twice_control (1-nu) hd₂
  let C := max coefficient⁻¹ (max C₁ C₂)
  have hCpos : 0 < C := lt_of_lt_of_le (inv_pos.mpr coefficient_positive) (le_max_left _ _)
  have hC₁le : C₁ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC₂le : C₂ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C,hCpos,fun a b z ha hb haz hz => ?_⟩
  have hz0 : 0 < z := ha.trans_le haz
  have hE := unitExcess_nonnegative a b z ha hb haz hz
  have hE1 : 0 ≤ 1+unitExcess a b z := by linarith
  have hformula := unitExcess_formula a b z ha hb hz0
  by_cases hg : 0 ≤ unitGain a b z
  · rw [abs_of_nonneg hg]
    have hdef := powerDefect_ge_neg_one a b z ha hb hz hz0.le
    have hsmall : unitGain a b z ≤ coefficient⁻¹*(1+unitExcess a b z) := by
      apply (le_inv_mul_iff₀ coefficient_positive).mpr
      linarith
    exact hsmall.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hE1)
  · have hgneg : unitGain a b z < 0 := lt_of_not_ge hg
    have hneglog : 0 < Real.log (a*b/z) := by rw [← unitGain_negative]; linarith
    have hfrac : 1 < a*b/z := (Real.log_pos_iff (div_pos (mul_pos ha hb) hz0).le).mp hneglog
    have hfracB : a*b/z ≤ b := (div_le_iff₀ hz0).mpr (by nlinarith [mul_le_mul_of_nonneg_left haz hb.le])
    have hlogB : -unitGain a b z ≤ Real.log b := by
      rw [unitGain_negative]
      exact Real.log_le_log (div_pos (mul_pos ha hb) hz0) hfracB
    rw [abs_of_neg hgneg]
    by_cases hzhalf : z ≤ b/2
    · have hb1 : 1 < b := hfrac.trans_le hfracB
      have hlog2b : Real.log b ≤ Real.log (2*b) := Real.log_le_log hb (by linarith)
      have hpower := Real.rpow_le_rpow hz0.le hzhalf nu_positive.le
      rw [show b/2=(1/2 : ℝ)*b by ring,Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1/2) hb.le] at hpower
      have hdef : d₁*b^nu ≤ powerDefect a b z := by
        unfold d₁ powerDefect
        nlinarith [Real.rpow_nonneg ha.le nu]
      have hlo : d₁*b^nu-nu*b^(nu-1)-coefficient*Real.log (2*b) ≤ unitExcess a b z := by
        have hlog : -unitGain a b z ≤ Real.log (2*b) := hlogB.trans hlog2b
        have hweighted := mul_le_mul_of_nonneg_left hlog coefficient_positive.le
        have hpowpos := mul_nonneg nu_positive.le (Real.rpow_nonneg hb.le (nu-1))
        linarith
      have hcontrol := hcontrol₁ b (unitExcess a b z) (by linarith) hE hlo
      exact (hlogB.trans hlog2b).trans (hcontrol.trans (mul_le_mul_of_nonneg_right hC₁le hE1))
    · have hzlarge : b/2 < z := lt_of_not_ge hzhalf
      have hfrac2 : a*b/z ≤ 2*min a b := by
        rcases le_total a b with hab | hba
        · rw [min_eq_left hab]
          apply (div_le_iff₀ hz0).mpr
          nlinarith [mul_pos ha (sub_pos.mpr hzlarge)]
        · rw [min_eq_right hba]
          exact hfracB.trans (by linarith)
      have hmin : 1/2 ≤ min a b := by linarith
      have hlog : -unitGain a b z ≤ Real.log (2*min a b) := by
        rw [unitGain_negative]
        exact Real.log_le_log (div_pos (mul_pos ha hb) hz0) hfrac2
      have hdef := powerDefect_lower a b z ha hb hz hz0.le
      have hlo : (1-nu)*(min a b)^nu-nu*(min a b)^(nu-1)-coefficient*Real.log (2*min a b) ≤ unitExcess a b z := by
        linarith [mul_le_mul_of_nonneg_left hlog coefficient_positive.le]
      have hcontrol := hcontrol₂ (min a b) (unitExcess a b z) hmin hE hlo
      exact hlog.trans (hcontrol.trans (mul_le_mul_of_nonneg_right hC₂le hE1))

end
end StrongSilver.Scalar.Silver
