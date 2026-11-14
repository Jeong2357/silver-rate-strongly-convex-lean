-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Scalar.MaxPlusLocal
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace StrongSilver.Scalar.Silver
open Set Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000

def largeBarrier (a : ℝ) : ℝ := (1-nu)*a^nu-nu*a^(nu-1)-coefficient*Real.log a

theorem power_increment (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a+b+1)^nu-b^nu ≤ nu*(a+1)*b^(nu-1) := by
  have hab : b < a+b+1 := by linarith
  have hc : ContinuousOn (fun x : ℝ => x^nu) (Icc b (a+b+1)) := by
    intro x hx
    exact (Real.hasDerivAt_rpow_const (p := nu) (Or.inl (hb.trans_le hx.1).ne')).continuousAt.continuousWithinAt
  obtain ⟨x,hx,he⟩ := exists_hasDerivAt_eq_slope (fun x : ℝ => x^nu) (fun x => nu*x^(nu-1)) hab hc
    (fun x hx => Real.hasDerivAt_rpow_const (Or.inl (hb.trans hx.1).ne'))
  have hpow := Real.rpow_le_rpow_of_nonpos hb hx.1.le (by linarith [nu_lt_one] : nu-1 ≤ 0)
  have he' : nu*x^(nu-1)*(a+1)=(a+b+1)^nu-b^nu := by
    have hh := (eq_div_iff (sub_pos.mpr hab).ne').mp he
    convert hh using 1 <;> ring
  rw [← he']
  have hcoef : 0 ≤ nu*(a+1) := mul_nonneg nu_positive.le (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hpow hcoef]

theorem splitPotential_large_lower (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    largeBarrier a ≤ splitPotential a b := by
  have hb := ha.trans_le hab
  have hinc := power_increment a b ha hb
  have hpow := Real.rpow_le_rpow_of_nonpos ha hab (by linarith [nu_lt_one] : nu-1 ≤ 0)
  have hlog := Real.log_le_log hb (show b ≤ a+b+1 by linarith)
  have h1 := mul_le_mul_of_nonneg_left hpow (mul_nonneg nu_positive.le (show 0 ≤ a+1 by linarith))
  have hid : a*a^(nu-1)=a^nu := by rw [Real.rpow_sub_one ha.ne']; field_simp
  unfold largeBarrier splitPotential scalarPotential
  nlinarith [mul_le_mul_of_nonneg_left hlog coefficient_positive.le,congrArg (fun t : ℝ => nu*t) hid]

theorem largeBarrier_tendsto : Tendsto largeBarrier atTop atTop := by
  have hlog : Tendsto (fun x : ℝ => Real.log x/x^nu) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop nu_positive).tendsto_div_nhds_zero
  have hinv : Tendsto (fun x : ℝ => 1/x) atTop (𝓝 0) := by simpa only [one_div] using tendsto_inv_atTop_zero
  have hnorm : Tendsto (fun x : ℝ => (1-nu)-nu*(1/x)-coefficient*(Real.log x/x^nu)) atTop (𝓝 (1-nu)) := by
    simpa only [mul_zero,sub_zero] using
      ((tendsto_const_nhds (x := 1-nu)).sub ((tendsto_const_nhds (x := nu)).mul hinv)).sub
        ((tendsto_const_nhds (x := coefficient)).mul hlog)
  have hprod := Filter.Tendsto.atTop_mul_pos (show 0 < 1-nu by linarith [nu_lt_one])
    (tendsto_rpow_atTop nu_positive) hnorm
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold largeBarrier
  rw [Real.rpow_sub_one hx.ne']
  have hp : x^nu ≠ 0 := (Real.rpow_pos_of_pos hx nu).ne'
  field_simp [hx.ne',hp] <;> ring

theorem scalarPotential_tendsto_zero : Tendsto scalarPotential (𝓝[>] (0 : ℝ)) atTop := by
  have h := Real.tendsto_log_nhdsGT_zero.atBot_mul_const_of_neg (neg_neg_of_pos coefficient_positive)
  apply tendsto_atTop_mono' (𝓝[>] (0 : ℝ)) _ h
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  unfold scalarPotential
  nlinarith [Real.rpow_nonneg hx.le nu]

def tailSlopeBound (b : ℝ) : ℝ := nu*b^(nu-1)+coefficient/b

theorem tailSlopeBound_nonnegative (b : ℝ) (hb : 0 < b) : 0 ≤ tailSlopeBound b :=
  add_nonneg (mul_nonneg nu_positive.le (Real.rpow_nonneg hb.le _)) (div_nonneg coefficient_positive.le hb.le)

theorem scalarFirst_abs_bound (b x : ℝ) (hb : 0 < b) (hbx : b ≤ x) :
    |scalarFirst x| ≤ tailSlopeBound b := by
  have hx := hb.trans_le hbx
  have he : scalarFirst x=nu*x^(nu-1)-coefficient/x := by
    unfold scalarFirst
    rw [Real.rpow_sub_one hx.ne']
    ring
  rw [he]
  have hpow := Real.rpow_le_rpow_of_nonpos hb hbx (by linarith [nu_lt_one] : nu-1 ≤ 0)
  have hdiv := div_le_div_of_nonneg_left coefficient_positive.le hb hbx
  have habs : |nu*x^(nu-1)-coefficient/x| ≤ |nu*x^(nu-1)|+|coefficient/x| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (nu*x^(nu-1)) (-(coefficient/x))
  rw [abs_of_nonneg (mul_nonneg nu_positive.le (Real.rpow_nonneg hx.le _)),
    abs_of_nonneg (div_nonneg coefficient_positive.le hx.le)] at habs
  unfold tailSlopeBound
  nlinarith [mul_le_mul_of_nonneg_left hpow nu_positive.le]

theorem tailSlopeBound_tendsto : Tendsto tailSlopeBound atTop (𝓝 0) := by
  have hp : Tendsto (fun b : ℝ => b^(nu-1)) atTop (𝓝 0) := by
    convert tendsto_rpow_neg_atTop (show 0 < 1-nu by linarith [nu_lt_one]) using 1 <;> congr 1 <;> ring
  have hinv : Tendsto (fun b : ℝ => b⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  change Tendsto (fun b : ℝ => nu*b^(nu-1)+coefficient/b) atTop (𝓝 0)
  simpa only [div_eq_mul_inv,mul_zero,add_zero] using
    ((tendsto_const_nhds (x := nu)).mul hp).add ((tendsto_const_nhds (x := coefficient)).mul hinv)

/-- Uniform control when one coordinate is bounded and the other tends to infinity. -/
theorem bounded_small_large (A a b : ℝ) (ha : 0 < a) (haA : a ≤ A) (hb : 0 < b) :
    minimum-(A+1)*tailSlopeBound b ≤ splitPotential a b := by
  have hab : b < a+b+1 := by linarith
  have hc : ContinuousOn scalarPotential (Icc b (a+b+1)) := by
    intro x hx
    exact (scalarPotential_derivative x (hb.trans_le hx.1)).continuousAt.continuousWithinAt
  obtain ⟨x,hx,he⟩ := exists_hasDerivAt_eq_slope scalarPotential scalarFirst hab hc
    (fun x hx => scalarPotential_derivative x (hb.trans hx.1))
  have he' : scalarPotential (a+b+1)-scalarPotential b=scalarFirst x*(a+1) := by
    have hh := ((eq_div_iff (sub_pos.mpr hab).ne').mp he).symm
    convert hh using 1 <;> ring
  have habs : |scalarPotential (a+b+1)-scalarPotential b| ≤ (A+1)*tailSlopeBound b := by
    rw [he',abs_mul,abs_of_pos (show 0 < a+1 by linarith)]
    have h1 := scalarFirst_abs_bound b x hb hx.1.le
    have h2 := tailSlopeBound_nonnegative b hb
    nlinarith [mul_le_mul_of_nonneg_right h1 (show 0 ≤ a+1 by linarith),
      mul_nonneg h2 (sub_nonneg.mpr haA)]
  have hl := scalarPotential_lower a ha
  have hdiff := le_abs_self (scalarPotential (a+b+1)-scalarPotential b)
  unfold splitPotential
  linarith

end
end StrongSilver.Scalar.Silver
