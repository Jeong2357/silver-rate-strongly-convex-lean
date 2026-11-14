-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarFrame
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace StrongSilver
open Real Set
noncomputable section

theorem normalAngle_hasDerivAt {k : ℝ → ℝ} {θ k' : ℝ} (hk : HasDerivAt k k' θ) :
    HasDerivAt (fun t => normalAngle (k t) t) (1+k'/(1+(k θ)^2)) θ := by
  convert! (hasDerivAt_id θ).add hk.arctan using 1 <;> ring

theorem normalAngle_derivative_pos {k k' : ℝ} (hk' : -1 < k') :
    0 < 1+k'/(1+k^2) := by
  have hd : 0 < 1+k^2 := by positivity
  have he : 1+k'/(1+k^2) = (1+k^2+k')/(1+k^2) := by field_simp <;> ring
  rw [he]
  exact div_pos (by nlinarith only [sq_nonneg k,hk']) hd

theorem normalAngle_first_quadrant {k θ : ℝ} (hk : 0 ≤ k) (hθ0 : 0 ≤ θ) (hθ : θ < Real.pi/2)
    (htransverse : k*Real.sin θ < Real.cos θ) :
    0 ≤ normalAngle k θ ∧ normalAngle k θ < Real.pi/2 := by
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hθ⟩
  have hprod : Real.tan θ*k < 1 := by
    rw [Real.tan_eq_sin_div_cos,div_mul_eq_mul_div]
    apply (div_lt_one hc).mpr
    nlinarith only [htransverse]
  have hangle : Real.arctan (Real.tan θ) = θ := Real.arctan_tan (by linarith [Real.pi_pos]) hθ
  constructor
  · exact add_nonneg hθ0 (Real.arctan_nonneg.mpr hk)
  · have hh := Real.arctan_add_arctan_lt_pi_div_two hprod
    rwa [hangle] at hh

theorem smoothNormalAngle_strictMonoOn {k₀ Θ : ℝ} (hk : 0 < k₀) (hk1 : k₀ ≤ 1/2)
    (hΘ : Θ < Real.pi/2) : StrictMonoOn (fun θ => normalAngle (smoothPlanarSlope k₀ θ) θ) (Icc 0 Θ) := by
  have hder (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) Θ) :
      HasDerivAt (fun t => normalAngle (smoothPlanarSlope k₀ t) t)
        (1+smoothPlanarSlopeDeriv k₀ θ/(1+(smoothPlanarSlope k₀ θ)^2)) θ := by
    have hd := smoothPlanar_denominator_lower hk hk1 ⟨hθ.1,hθ.2.trans hΘ.le⟩
    have hdpos : 0 < Real.cos θ+2*k₀*Real.sin θ := lt_of_lt_of_le (by linarith) hd
    exact normalAngle_hasDerivAt (smoothPlanarSlope_hasDerivAt hdpos.ne')
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun θ hθ => (hder θ hθ).continuousAt.continuousWithinAt)
  intro θ hθ
  have hθ' := interior_subset hθ
  rw [(hder θ hθ').deriv]
  have hk' := (smoothPlanarSlopeDeriv_bounds hk hk1 ⟨hθ'.1,hθ'.2.trans hΘ.le⟩).1
  exact normalAngle_derivative_pos (by linarith)

theorem smoothNormalAngle_first_quadrant {k₀ θ : ℝ} (hk : 0 < k₀) (hθ0 : 0 ≤ θ)
    (hθ : θ < Real.pi/2) :
    0 ≤ normalAngle (smoothPlanarSlope k₀ θ) θ ∧ normalAngle (smoothPlanarSlope k₀ θ) θ < Real.pi/2 := by
  obtain ⟨hpos,hbound,htrans⟩ := smoothPlanarSlope_bounds hk hθ0 hθ
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hθ⟩
  apply normalAngle_first_quadrant hpos.le hθ0 hθ
  linarith

end
end StrongSilver
