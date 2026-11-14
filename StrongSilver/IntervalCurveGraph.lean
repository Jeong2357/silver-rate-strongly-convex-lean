-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IntervalInverseWithin
import StrongSilver.PlanarFieldSlope

namespace StrongSilver
open Set Complex
noncomputable section

def intervalCurveGraph {a b : ℝ} {γ : ℝ → ℂ} (hab : a ≤ b)
    (hcX : ContinuousOn (fun θ => (γ θ).re) (Icc a b))
    (hsX : StrictAntiOn (fun θ => (γ θ).re) (Icc a b)) (y : ℝ) : ℝ :=
  (γ (intervalGraphInverse hab hcX hsX y)).im

theorem intervalCurveGraph_continuous {a b : ℝ} {γ : ℝ → ℂ} (hab : a ≤ b)
    (hcX : ContinuousOn (fun θ => (γ θ).re) (Icc a b))
    (hsX : StrictAntiOn (fun θ => (γ θ).re) (Icc a b))
    (hcY : ContinuousOn (fun θ => (γ θ).im) (Icc a b)) :
    Continuous (intervalCurveGraph hab hcX hsX) :=
  hcY.comp_continuous (intervalGraphInverse_continuous hab hcX hsX)
    (fun y => intervalGraphInverse_mem hab hcX hsX y)

theorem intervalCurveGraph_on_curve {a b θ : ℝ} {γ : ℝ → ℂ} (hab : a ≤ b)
    (hcX : ContinuousOn (fun θ => (γ θ).re) (Icc a b))
    (hsX : StrictAntiOn (fun θ => (γ θ).re) (Icc a b)) (ht : θ ∈ Icc a b) :
    intervalCurveGraph hab hcX hsX (γ θ).re = (γ θ).im := by
  unfold intervalCurveGraph
  rw [intervalGraphInverse_left_inverse hab hcX hsX ht]

theorem intervalCurveGraph_hasDerivWithinAt {a b y t : ℝ} {γ F : ℝ → ℂ} (hab : a ≤ b)
    (hcX : ContinuousOn (fun θ => (γ θ).re) (Icc a b))
    (hsX : StrictAntiOn (fun θ => (γ θ).re) (Icc a b))
    (hy : y ∈ Icc (γ b).re (γ a).re) (ht : t ≠ 0)
    (hF : (F (intervalGraphInverse hab hcX hsX y)).re ≠ 0)
    (hγ : HasDerivWithinAt γ (t • F (intervalGraphInverse hab hcX hsX y))
      (Icc a b) (intervalGraphInverse hab hcX hsX y)) :
    HasDerivWithinAt (intervalCurveGraph hab hcX hsX)
      (planarFieldSlope F (intervalGraphInverse hab hcX hsX y)) (Icc (γ b).re (γ a).re) y := by
  have hx := complex_curve_re_hasDerivWithinAt hγ
  have him := complex_curve_im_hasDerivWithinAt hγ
  simp only [Complex.smul_re,Complex.smul_im,smul_eq_mul] at hx him
  have hi := intervalGraphInverse_hasDerivWithinAt hab hcX hsX hy hx (mul_ne_zero ht hF)
  have hh := him.comp y hi (fun z hz => intervalGraphInverse_mem hab hcX hsX z)
  convert! hh using 1
  unfold planarFieldSlope
  field_simp [ht,hF]

theorem intervalCurveGraph_concave {a b : ℝ} {γ F : ℝ → ℂ} (hab : a ≤ b)
    (hcX : ContinuousOn (fun θ => (γ θ).re) (Icc a b))
    (hsX : StrictAntiOn (fun θ => (γ θ).re) (Icc a b))
    (hcY : ContinuousOn (fun θ => (γ θ).im) (Icc a b))
    (hFpos : ∀ θ ∈ Icc a b, 0 < (F θ).re)
    (hγ : ∀ θ ∈ Icc a b, ∃ t : ℝ, t < 0 ∧ HasDerivWithinAt γ (t • F θ) (Icc a b) θ)
    (hslope : MonotoneOn (planarFieldSlope F) (Icc a b)) :
    ConcaveOn ℝ (Icc (γ b).re (γ a).re) (intervalCurveGraph hab hcX hsX) := by
  let S := Icc (γ b).re (γ a).re
  have hd (y : ℝ) (hy : y ∈ S) :
      HasDerivWithinAt (intervalCurveGraph hab hcX hsX)
        (planarFieldSlope F (intervalGraphInverse hab hcX hsX y)) S y := by
    have ht := intervalGraphInverse_mem hab hcX hsX y
    obtain ⟨t,htn,htd⟩ := hγ _ ht
    exact intervalCurveGraph_hasDerivWithinAt hab hcX hsX hy htn.ne (hFpos _ ht).ne' htd
  have hiOrder := intervalGraphInverse_antitoneOn hab hcX hsX
  have hanti : AntitoneOn (fun y => planarFieldSlope F (intervalGraphInverse hab hcX hsX y)) S := by
    intro x hx y hy hxy
    exact hslope (intervalGraphInverse_mem hab hcX hsX y) (intervalGraphInverse_mem hab hcX hsX x) (hiOrder hx hy hxy)
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc _ _)
    (intervalCurveGraph_continuous hab hcX hsX hcY).continuousOn
    (fun y hy => ((hd y (interior_subset hy)).hasDerivAt (mem_interior_iff_mem_nhds.mp hy)).differentiableAt.differentiableWithinAt)
  intro x hx y hy hxy
  have hdx := ((hd x (interior_subset hx)).hasDerivAt (mem_interior_iff_mem_nhds.mp hx)).deriv
  have hdy := ((hd y (interior_subset hy)).hasDerivAt (mem_interior_iff_mem_nhds.mp hy)).deriv
  rw [hdx,hdy]
  exact hanti (interior_subset hx) (interior_subset hy) hxy

end
end StrongSilver
