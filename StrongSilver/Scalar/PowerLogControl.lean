-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Scalar.MaxPlusBoundary

namespace StrongSilver.Scalar.Silver
open Set Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000

def powerLogBarrier (d k c x : ℝ) : ℝ := d*x^nu-k*x^(nu-1)-c*Real.log x

theorem powerLogBarrier_tendsto (d k c : ℝ) (hd : 0 < d) :
    Tendsto (powerLogBarrier d k c) atTop atTop := by
  have hlog : Tendsto (fun x : ℝ => Real.log x/x^nu) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop nu_positive).tendsto_div_nhds_zero
  have hinv : Tendsto (fun x : ℝ => 1/x) atTop (𝓝 0) := by simpa only [one_div] using tendsto_inv_atTop_zero
  have hn : Tendsto (fun x : ℝ => d-k*(1/x)-c*(Real.log x/x^nu)) atTop (𝓝 d) := by
    simpa only [mul_zero,sub_zero] using
      ((tendsto_const_nhds (x := d)).sub ((tendsto_const_nhds (x := k)).mul hinv)).sub
        ((tendsto_const_nhds (x := c)).mul hlog)
  have hp := Filter.Tendsto.atTop_mul_pos hd (tendsto_rpow_atTop nu_positive) hn
  apply hp.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold powerLogBarrier
  rw [Real.rpow_sub_one hx.ne']
  have hxpow : x^nu ≠ 0 := (Real.rpow_pos_of_pos hx nu).ne'
  field_simp [hx.ne',hxpow] <;> ring

/-- A uniform logarithmic bound from a positive power lower bound. This is
applied separately to the two negative-gain cases in the excess lemma. -/
theorem log_twice_control (d : ℝ) (hd : 0 < d) : ∃ C > 0,
    ∀ x E : ℝ, 1/2 ≤ x → 0 ≤ E →
      d*x^nu-nu*x^(nu-1)-coefficient*Real.log (2*x) ≤ E →
      Real.log (2*x) ≤ C*(1+E) := by
  obtain ⟨B₀,hB₀⟩ := eventually_atTop.mp
    ((powerLogBarrier_tendsto d nu (coefficient+1) hd).eventually_ge_atTop ((coefficient+1)*Real.log 2))
  let B := max 1 B₀
  have hB : 1 ≤ B := le_max_left _ _
  let C := max 1 (Real.log (2*B))
  have hC : 1 ≤ C := le_max_left _ _
  have hClog : Real.log (2*B) ≤ C := le_max_right _ _
  refine ⟨C,by linarith,fun x E hx hE hlo => ?_⟩
  have hx0 : 0 < x := by linarith
  by_cases hxB : B ≤ x
  · have hp := hB₀ x ((le_max_right _ _).trans hxB)
    unfold powerLogBarrier at hp
    have hlog : Real.log (2*x)=Real.log 2+Real.log x := Real.log_mul (by norm_num) hx0.ne'
    rw [hlog] at hlo
    have hg : Real.log (2*x) ≤ E := by rw [hlog]; linarith
    have hnonneg := mul_nonneg (sub_nonneg.mpr hC) hE
    nlinarith
  · have hlog : Real.log (2*x) ≤ Real.log (2*B) :=
      Real.log_le_log (by linarith) (by linarith [lt_of_not_ge hxB])
    have hnonneg := mul_nonneg (show 0 ≤ C by linarith) hE
    nlinarith

end
end StrongSilver.Scalar.Silver
