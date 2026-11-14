-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ConePlaneRows
import StrongSilver.OppositeDomain

namespace StrongSilver
open Set Real Complex
noncomputable section
set_option maxHeartbeats 1000000

theorem coneRay_quadrant (c s : ℝ) (z : ℂ) :
    ∃ n ∈ coneRays c s, inner ℝ n z = c*|z.re|+s*|z.im| := by
  by_cases hx : 0 ≤ z.re <;> by_cases hy : 0 ≤ z.im
  · refine ⟨wedgeUpper c s,by simp [coneRays],?_⟩
    simp only [wedgeUpper,complex_inner_coordinates,abs_of_nonneg hx,abs_of_nonneg hy]
  · refine ⟨wedgeLower c s,by simp [coneRays],?_⟩
    simp only [wedgeLower,complex_inner_coordinates,abs_of_nonneg hx,abs_of_neg (lt_of_not_ge hy)]
    ring
  · refine ⟨-wedgeLower c s,by simp [coneRays],?_⟩
    simp only [wedgeLower,complex_inner_coordinates,Complex.neg_re,Complex.neg_im,
      abs_of_neg (lt_of_not_ge hx),abs_of_nonneg hy]
    ring
  · refine ⟨-wedgeUpper c s,by simp [coneRays],?_⟩
    simp only [wedgeUpper,complex_inner_coordinates,Complex.neg_re,Complex.neg_im,
      abs_of_neg (lt_of_not_ge hx),abs_of_neg (lt_of_not_ge hy)]
    ring

theorem conePlane_quadrant_lower (a d r c s Δ : ℝ) (z : ℂ) :
    r*(c*|z.re|+s*|z.im|)-Δ ≤ Moreau.planeMaximum (conePlaneRows a d r c s Δ) z := by
  obtain ⟨n,hn,he⟩ := coneRay_quadrant c s z
  have hrow : (r • n,Δ) ∈ conePlaneRows a d r c s Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨n,hn,rfl⟩)
  have hh := Moreau.plane_le_maximum _ (r • n,Δ) hrow z
  rwa [real_inner_smul_left,he] at hh

theorem wedge_absolute_bound {c s : ℝ} (hs : 0 < s) {z : ℂ}
    (hz : z ∈ wedgeCone c s ∪ oppositeSet (wedgeCone c s)) : c*|z.im| ≤ s*|z.re| := by
  have hpos (x : ℂ) (hx : x ∈ wedgeCone c s) : c*|x.im| ≤ s*|x.re| := by
    have hh := (wedge_mem_iff c s x).mp hx
    rw [abs_of_nonneg (wedge_re_nonnegative hs hx)]
    by_cases hy : 0 ≤ x.im
    · rw [abs_of_nonneg hy]; linarith only [hh.1]
    · rw [abs_of_neg (lt_of_not_ge hy)]; nlinarith only [hh.2]
  rcases hz with hz | hz
  · exact hpos z hz
  · have hh := hpos (-z) hz
    simpa only [Complex.neg_re,Complex.neg_im,abs_neg] using hh

theorem conePlane_hinge_lower {a d r c s Δ : ℝ} (hr : 0 ≤ r) (hc : 0 ≤ c) (hs : 0 < s)
    (hu : c^2+s^2 = 1) {z : ℂ} (hz : z ∈ wedgeCone c s ∪ oppositeSet (wedgeCone c s)) :
    max ((r/s)*|z.im|-Δ) 0 ≤ Moreau.planeMaximum (conePlaneRows a d r c s Δ) z := by
  have hbound := wedge_absolute_bound hs hz
  have hm := mul_le_mul_of_nonneg_left hbound hc
  have huY := congrArg (fun t : ℝ => t*|z.im|) hu
  have hquot : |z.im|/s ≤ c*|z.re|+s*|z.im| := by
    apply (div_le_iff₀ hs).mpr
    nlinarith only [hm,huY]
  have hscale := mul_le_mul_of_nonneg_left hquot hr
  have hQ := conePlane_quadrant_lower a d r c s Δ z
  apply max_le _ (Moreau.planeMaximum_nonnegative _ _)
  simp only [div_eq_mul_inv] at hscale ⊢
  nlinarith only [hQ,hscale]

end
end StrongSilver
