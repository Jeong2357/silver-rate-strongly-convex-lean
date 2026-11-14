-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2200000

/-- The selected product in the last phase may be negative or large.
Its contribution to the joining scale is controlled relative to k. -/
theorem last_product_relative_bound {μ T C α p k : ℝ}
    (hμ : 0 ≤ μ) (hμmax : μ ≤ 1/4) (hT : 0 < T)
    (hμT : μ*T ≤ 1/4) (hα : α ≠ 0)
    (hCA : 0 ≤ C*α) (hCA2 : C*α ≤ 2) (hk : 1/2 ≤ k)
    (hp : p/α = 1-μ*T*(k+1/T)) : |C*p| ≤ 6*k := by
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hμT0 : 0 ≤ μ*T := mul_nonneg hμ hT.le
  have hprod := mul_le_mul_of_nonneg_right hμT hk0
  have he : p = α*(1-μ*T*k-μ) := by
    calc
      p = (1-μ*T*(k+1/T))*α := (div_eq_iff hα).mp hp
      _ = _ := by field_simp <;> ring
  have hbase : |1-μ*T*k-μ| ≤ 1+μ*T*k+μ := by
    apply abs_le.mpr
    constructor <;> nlinarith only [mul_nonneg hμT0 hk0,hμ]
  rw [he,← mul_assoc,abs_mul,abs_of_nonneg hCA]
  have h1 := mul_le_mul_of_nonneg_left hbase hCA
  have h2 := mul_le_mul_of_nonneg_right hCA2
    (show 0 ≤ 1+μ*T*k+μ by nlinarith only [mul_nonneg hμT0 hk0,hμ])
  nlinarith only [h1,h2,hprod,hμmax,hk]

theorem last_scale_bounds {k d ζ : ℝ} (hk : 0 < k) (hd : |d| ≤ 6*k)
    (hζ : 0 ≤ ζ) (hζsmall : ζ ≤ 1/60) :
    (9/10:ℝ)*k ≤ k-d*ζ ∧ k-d*ζ ≤ (11/10:ℝ)*k := by
  have habs := mul_le_mul_of_nonneg_right hd hζ
  have habs2 : |d*ζ| ≤ 6*k*ζ := by
    simpa only [abs_mul,abs_of_nonneg hζ] using habs
  have hl := (abs_le.mp habs2).1
  have hu := (abs_le.mp habs2).2
  have hsmall := mul_le_mul_of_nonneg_left hζsmall hk.le
  constructor <;> nlinarith only [hl,hu,hsmall]

/-- The loss from replacing k by the actual joining scale is linear in ζ. -/
theorem last_scale_log_lower {k d ζ : ℝ} (hk : 0 < k) (hd : |d| ≤ 6*k)
    (hζ : 0 ≤ ζ) (hζsmall : ζ ≤ 1/60) : -12*ζ ≤ Real.log ((k-d*ζ)/k) := by
  obtain ⟨hlo,hhi⟩ := last_scale_bounds hk hd hζ hζsmall
  let w := (k-d*ζ)/k
  have hw : 0 < w := div_pos (by nlinarith only [hlo,hk]) hk
  have hw2 : 1/2 ≤ w := (le_div_iff₀ hk).mpr (by nlinarith only [hlo,hk])
  have hdiv : d/k ≤ 6 := (div_le_iff₀ hk).mpr ((le_abs_self d).trans hd)
  have hwm : w-1 ≥ -6*ζ := by
    have hmul := mul_le_mul_of_nonneg_right hdiv hζ
    have he : w-1 = -(d/k)*ζ := by dsimp [w]; field_simp <;> ring
    rw [he]
    nlinarith only [hmul]
  have hp := mul_nonneg hζ (sub_nonneg.mpr hw2)
  have hfrac : -12*ζ ≤ 1-w⁻¹ := by
    have hmul : (-12*ζ)*w ≤ w-1 := by nlinarith only [hp,hwm]
    have hdiv' : -12*ζ ≤ (w-1)/w := (le_div_iff₀ hw).mpr hmul
    have he : (w-1)/w = 1-w⁻¹ := by field_simp <;> ring
    rwa [he] at hdiv'
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hw)
  rw [Real.log_inv] at hlog
  linarith only [hlog,hfrac]

end
end StrongSilver.FourPhase
