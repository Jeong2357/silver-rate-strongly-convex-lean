-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Scalar.MaxPlusAway
import StrongSilver.Scalar.LogRatioBound

namespace StrongSilver.Scalar.Silver
open Set
noncomputable section
set_option maxHeartbeats 1000000

def unitExcess (a b z : ℝ) : ℝ := scalarPotential a+scalarPotential b-scalarPotential z

theorem scalarPotential_interval_bound (a z b : ℝ) (ha : 0 < a) (haz : a ≤ z) (hzb : z ≤ b) :
    scalarPotential z ≤ max (scalarPotential a) (scalarPotential b) := by
  by_contra hn
  have hmax : max (scalarPotential a) (scalarPotential b) < scalarPotential z := lt_of_not_ge hn
  have hleft : scalarPotential a < scalarPotential z := lt_of_le_of_lt (le_max_left _ _) hmax
  have hright : scalarPotential b < scalarPotential z := lt_of_le_of_lt (le_max_right _ _) hmax
  have haz' : a < z := lt_of_le_of_ne haz (by intro he; rw [he] at hleft; exact lt_irrefl _ hleft)
  have hzb' : z < b := lt_of_le_of_ne hzb (by intro he; rw [he] at hright; exact lt_irrefl _ hright)
  have hcont (u v : ℝ) (hu : 0 < u) : ContinuousOn scalarPotential (Icc u v) := by
    intro x hx
    exact (scalarPotential_derivative x (hu.trans_le hx.1)).continuousAt.continuousWithinAt
  obtain ⟨u,hu,heU⟩ := exists_hasDerivAt_eq_slope scalarPotential scalarFirst haz' (hcont a z ha)
    (fun x hx => scalarPotential_derivative x (ha.trans hx.1))
  obtain ⟨v,hv,heV⟩ := exists_hasDerivAt_eq_slope scalarPotential scalarFirst hzb' (hcont z b (ha.trans_le haz))
    (fun x hx => scalarPotential_derivative x ((ha.trans_le haz).trans hx.1))
  have hU : 0 < scalarFirst u := by rw [heU]; exact div_pos (sub_pos.mpr hleft) (sub_pos.mpr haz')
  have hV : scalarFirst v < 0 := by rw [heV]; exact div_neg_of_neg_of_pos (sub_neg.mpr hright) (sub_pos.mpr hzb')
  have hu0 : 0 < u := ha.trans hu.1
  have hv0 : 0 < v := (ha.trans_le haz).trans hv.1
  have hnumU : 0 < nu*u^nu-coefficient := (div_pos_iff_of_pos_right hu0).mp hU
  have hnumV : nu*v^nu-coefficient < 0 := by
    have h := (div_lt_iff₀ hv0).mp hV
    simpa only [zero_mul] using h
  have hpower := Real.rpow_le_rpow hu0.le (by linarith [hu.2,hv.1] : u ≤ v) nu_positive.le
  nlinarith [mul_le_mul_of_nonneg_left hpower nu_positive.le]

theorem unitExcess_endpoint_lower (a b z : ℝ) (ha : 0 < a) (hb : 0 < b)
    (haz : a ≤ z) (hz : z ≤ a+b+1) : min minimum (splitPotential a b) ≤ unitExcess a b z := by
  have h := scalarPotential_interval_bound a z (a+b+1) ha haz hz
  by_cases hle : scalarPotential a ≤ scalarPotential (a+b+1)
  · rw [max_eq_right hle] at h
    unfold unitExcess
    exact (min_le_right _ _).trans (by unfold splitPotential; linarith)
  · rw [max_eq_left (le_of_not_ge hle)] at h
    have hlo := scalarPotential_lower b hb
    unfold unitExcess
    exact (min_le_left _ _).trans (by linarith)

theorem unitExcess_nonnegative (a b z : ℝ) (ha : 0 < a) (hb : 0 < b)
    (haz : a ≤ z) (hz : z ≤ a+b+1) : 0 ≤ unitExcess a b z :=
  (le_min minimum_positive.le (splitPotential_nonnegative a b ha hb)).trans (unitExcess_endpoint_lower a b z ha hb haz hz)

def intervalSlope : ℝ := (nu-coefficient)/(2*rho+3)

theorem intervalSlope_positive : 0 < intervalSlope := by
  apply div_pos _ (by linarith [rho_positive])
  unfold coefficient
  nlinarith [mul_pos nu_positive (sub_pos.mpr sqrt_two_bounds.1)]

theorem scalarFirst_interval_lower (s : ℝ) (hs : s ∈ Icc 1 (2*rho+3)) : intervalSlope ≤ scalarFirst s := by
  have hs0 : 0 < s := by linarith [hs.1]
  have hpow : 1 ≤ s^nu := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hs.1 nu_positive.le
    simpa only [Real.one_rpow] using h
  have hn : 0 ≤ nu-coefficient := by
    unfold coefficient
    nlinarith [mul_pos nu_positive (sub_pos.mpr sqrt_two_bounds.1)]
  unfold intervalSlope scalarFirst
  calc
    _ ≤ (nu-coefficient)/s := div_le_div_of_nonneg_left hn hs0 hs.2
    _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [mul_nonneg nu_positive.le (sub_nonneg.mpr hpow)]) hs0.le

theorem unitExcess_deficit_lower (a b z : ℝ) (ha : 1 ≤ a) (hb : 0 < b)
    (hz : a ≤ z) (hzmax : z ≤ a+b+1) (hcap : a+b+1 ≤ 2*rho+3) :
    splitPotential a b+intervalSlope*(a+b+1-z) ≤ unitExcess a b z := by
  by_cases he : z=a+b+1
  · rw [he,sub_self,mul_zero,add_zero]
    rfl
  · have hlt : z < a+b+1 := lt_of_le_of_ne hzmax he
    have hz0 : 0 < z := by linarith
    have hc : ContinuousOn scalarPotential (Icc z (a+b+1)) := by
      intro x hx
      exact (scalarPotential_derivative x (hz0.trans_le hx.1)).continuousAt.continuousWithinAt
    obtain ⟨x,hx,heq⟩ := exists_hasDerivAt_eq_slope scalarPotential scalarFirst hlt hc
      (fun x hx => scalarPotential_derivative x (hz0.trans hx.1))
    have hs := scalarFirst_interval_lower x ⟨by linarith [hx.1],by linarith [hx.2]⟩
    rw [heq] at hs
    have hdiff := (le_div_iff₀ (sub_pos.mpr hlt)).mp hs
    unfold splitPotential unitExcess
    linarith

end
end StrongSilver.Scalar.Silver
