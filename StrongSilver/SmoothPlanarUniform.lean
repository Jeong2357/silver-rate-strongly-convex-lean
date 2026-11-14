-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarEndpoint

namespace StrongSilver
open Real Set
noncomputable section

theorem smoothPlanarSlope_antitoneOn {k₀ Θ : ℝ} (hk : 0 < k₀) (hk1 : k₀ ≤ 1/2)
    (hΘ : Θ < Real.pi/2) : AntitoneOn (smoothPlanarSlope k₀) (Icc (0 : ℝ) Θ) := by
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Θ) :
      HasDerivAt (smoothPlanarSlope k₀) (smoothPlanarSlopeDeriv k₀ t) t := by
    have hh := smoothPlanar_denominator_lower hk hk1 ⟨ht.1,ht.2.trans hΘ.le⟩
    exact smoothPlanarSlope_hasDerivAt (ne_of_gt (lt_of_lt_of_le (by linarith : 0 < 2*k₀) hh))
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
  intro t ht
  have ht0 := interior_subset ht
  rw [(hd t ht0).deriv]
  exact (smoothPlanarSlopeDeriv_bounds hk hk1 ⟨ht0.1,ht0.2.trans hΘ.le⟩).2.le

theorem smoothPlanarSlope_uniform_lower {k₀ ε θ : ℝ} (hk : 0 < k₀) (hk1 : k₀ ≤ 1/2)
    (hε : 0 < ε) (hεk : ε ≤ k₀) (hθ : θ ∈ Icc (0 : ℝ) (Real.arctan ε⁻¹)) :
    ε/3 ≤ smoothPlanarSlope k₀ θ := by
  have hanti := smoothPlanarSlope_antitoneOn hk hk1 (Real.arctan_lt_pi_div_two ε⁻¹)
  exact (smoothPlanarSlope_terminal_bounds hk hε hεk).1.trans
    (hanti hθ ⟨hθ.1.trans hθ.2,le_rfl⟩ hθ.2)

def planarLinearPerturbation (μ k : ℝ) : ℝ := μ*(1+k^2)/k
def planarQuadraticPerturbation (μ r k k' : ℝ) : ℝ := μ*(1+k^2+k')/(r*k^2)

theorem planar_perturbation_bounds {μ r k k₀ k' ε : ℝ} (hμ : 0 ≤ μ) (hε : 0 < ε)
    (hmin : ε/3 ≤ k) (hk : k ≤ k₀) (hk₀ : 0 ≤ k₀) (hk' : -(1 : ℝ)/2 ≤ k') (hk'u : k' ≤ 0)
    (hr : 1 ≤ r) :
    (0 ≤ planarLinearPerturbation μ k ∧ planarLinearPerturbation μ k ≤ 3*μ*(1+k₀^2)/ε) ∧
    (0 ≤ planarQuadraticPerturbation μ r k k' ∧
      planarQuadraticPerturbation μ r k k' ≤ 9*μ*(1+k₀^2)/ε^2) := by
  have hkpos : 0 < k := lt_of_lt_of_le (by positivity : 0 < ε/3) hmin
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hsquares : k^2 ≤ k₀^2 := by gcongr
  have hnum : 0 ≤ 1+k^2+k' := by nlinarith only [sq_nonneg k,hk']
  have hnumu : 1+k^2+k' ≤ 1+k₀^2 := by linarith
  have hμnum : 0 ≤ μ*(1+k₀^2) := by positivity
  constructor
  · unfold planarLinearPerturbation
    refine ⟨by positivity,?_⟩
    calc
      _ ≤ μ*(1+k₀^2)/k := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : 1+k^2 ≤ 1+k₀^2) hμ) hkpos.le
      _ ≤ μ*(1+k₀^2)/(ε/3) := div_le_div_of_nonneg_left hμnum (by positivity) hmin
      _ = _ := by field_simp <;> ring
  · unfold planarQuadraticPerturbation
    refine ⟨div_nonneg (mul_nonneg hμ hnum) (by positivity),?_⟩
    have hsqmin : (ε/3)^2 ≤ k^2 := by gcongr
    have hden : ε^2/9 ≤ r*k^2 := by
      have hh := mul_le_mul_of_nonneg_right hr (sq_nonneg k)
      nlinarith only [hsqmin,hh]
    calc
      _ ≤ μ*(1+k₀^2)/(r*k^2) := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnumu hμ) (by positivity)
      _ ≤ μ*(1+k₀^2)/(ε^2/9) := div_le_div_of_nonneg_left hμnum (by positivity) hden
      _ = _ := by field_simp <;> ring

end
end StrongSilver
