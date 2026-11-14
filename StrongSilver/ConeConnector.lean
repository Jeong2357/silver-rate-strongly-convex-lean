-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ConeEpigraph
import StrongSilver.ConePotentialLower
import StrongSilver.ExactProximalValues

namespace StrongSilver
open Real Complex
noncomputable section
set_option maxHeartbeats 1600000

theorem cone_connector_plane_dominates {a d r c s Δ X Y : ℝ}
    (ha : 0 < a) (hd : 0 ≤ d) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1) (hu : c^2+s^2 = 1)
    (hr : 0 ≤ r) (hra : r ≤ 2*a) (hradius : r = a*c+d*s)
    (hX : 0 < X) (hY : 0 ≤ Y) (hdsmall : d ≤ a*s/256)
    (hYsmall : Y ≤ s*X/256) (hΔ : Δ ≤ a*X/128) :
    0 ≤ a*X-d*Y-Δ ∧
      ∀ p ∈ conePlaneRows a d r c s Δ,
        inner ℝ p.1 (⟨X,Y⟩ : ℂ)-p.2 ≤ a*X-d*Y-Δ := by
  have hdAs : d ≤ a*s := by nlinarith only [hdsmall,mul_pos ha hs]
  have hYsX : Y ≤ s*X := by nlinarith only [hYsmall,mul_pos hs hX]
  have hds : d*s ≤ a*s^2/256 := by
    have hh := mul_le_mul_of_nonneg_right hdsmall hs.le
    nlinarith only [hh]
  have hdsc : d*s*c ≤ a*s^2/256 := by
    have hh := mul_le_mul_of_nonneg_left hc1 (mul_nonneg hd hs.le)
    nlinarith only [hh,hds]
  have hrS : d+r*s ≤ 3*a*s := by
    have hh := mul_le_mul_of_nonneg_right hra hs.le
    nlinarith only [hh,hdAs]
  have hcross : (d+r*s)*Y ≤ 3*a*s^2*X/256 := by
    have h1 := mul_le_mul_of_nonneg_right hrS hY
    have h2 := mul_le_mul_of_nonneg_left hYsmall (by positivity : 0 ≤ 3*a*s)
    nlinarith only [h1,h2]
  have hmain : r*(c*X+s*Y) ≤ a*X-d*Y := by
    have h1 := mul_le_mul_of_nonneg_right hdsc hX.le
    have hsq := congrArg (fun t : ℝ => a*X*t) hu
    rw [hradius] at hcross ⊢
    have hpos : 0 ≤ a*s^2*X := by positivity
    nlinarith only [h1,hcross,hsq,hpos]
  have hdY : d*Y ≤ a*X/256 := by
    have h1 := mul_le_mul_of_nonneg_right hdAs hY
    have h2 := mul_le_mul_of_nonneg_left hYsmall (mul_nonneg ha.le hs.le)
    have h3 : s^2 ≤ 1 := by nlinarith only [hs,hs1]
    have h4 := mul_le_mul_of_nonneg_left h3 (mul_nonneg ha.le hX.le)
    nlinarith only [h1,h2,h4]
  refine ⟨by nlinarith only [hdY,hΔ,mul_pos ha hX],?_⟩
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · simp only [complex_inner_coordinates]
    nlinarith
  · obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hp
    have hncoord : inner ℝ n (⟨X,Y⟩ : ℂ) ≤ c*X+s*Y := by
      simp only [coneRays,List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl <;>
        simp only [wedgeUpper,wedgeLower,complex_inner_coordinates,Complex.neg_re,Complex.neg_im] <;>
        nlinarith only [mul_nonneg hc hX.le,mul_nonneg hs.le hY]
    have hh := mul_le_mul_of_nonneg_left hncoord hr
    simp only [real_inner_smul_left]
    linarith only [hh,hmain]

theorem cone_connector_support {a d r c s Δ X Y : ℝ} (hΔ0 : 0 ≤ Δ)
    (hpositive : 0 ≤ a*X-d*Y-Δ)
    (hactive : ∀ p ∈ conePlaneRows a d r c s Δ,
      inner ℝ p.1 (⟨X,Y⟩ : ℂ)-p.2 ≤ a*X-d*Y-Δ) :
    Moreau.Supports (coneEpigraph a d r c s Δ hΔ0) (⟨X,Y⟩ : ℂ)
      (a*X-d*Y-Δ) (⟨a,-d⟩ : ℂ) := by
  apply Moreau.active_plane_supports
  · exact hpositive
  · have hh : ((⟨a,-d⟩ : ℂ),Δ) ∈ conePlaneRows a d r c s Δ := List.mem_cons_self
    convert hh using 1 <;> simp only [complex_inner_coordinates] <;> ring
  · exact hactive

theorem cone_connector_exact_step {a d r c s Δ μ b U V X Y : ℝ} (hΔ0 : 0 ≤ Δ)
    (hpositive : 0 ≤ a*X-d*Y-Δ)
    (hactive : ∀ p ∈ conePlaneRows a d r c s Δ,
      inner ℝ p.1 (⟨X,Y⟩ : ℂ)-p.2 ≤ a*X-d*Y-Δ)
    (hX : X+a = U) (hY : Y=d) (ha : (1-μ)*b*a = (1-μ*b)*U)
    (hd : (1-μ)*b*d = V) :
    let P := coneEpigraph a d r c s Δ hΔ0
    Moreau.proximal P (⟨U,0⟩ : ℂ) = (⟨X,Y⟩ : ℂ) ∧
    Moreau.gradient P (⟨U,0⟩ : ℂ) = (⟨a,-d⟩ : ℂ) ∧
    (⟨U,0⟩ : ℂ)-b • stronglyConvexGradient μ (Moreau.gradient P) (⟨U,0⟩ : ℂ) = (⟨0,V⟩ : ℂ) := by
  dsimp only
  have hsupp := cone_connector_support hΔ0 hpositive hactive
  have hsum : (⟨X,Y⟩ : ℂ)+(⟨a,-d⟩ : ℂ) = (⟨U,0⟩ : ℂ) := by
    apply Complex.ext <;> simp only [Complex.add_re,Complex.add_im] <;> linarith only [hX,hY]
  have hgrad := (Moreau.envelope_interpolates _ _ _ _ hsupp).1
  have hprox := Moreau.minimizingPair_eq_from_supports _ _ _ _ hsupp
  rw [hsum] at hgrad hprox
  refine ⟨by unfold Moreau.proximal; rw [hprox],hgrad,?_⟩
  rw [stronglyConvexGradient,hgrad]
  apply Complex.ext <;>
    simp only [Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,
      smul_eq_mul] <;> nlinarith only [ha,hd]

end
end StrongSilver
