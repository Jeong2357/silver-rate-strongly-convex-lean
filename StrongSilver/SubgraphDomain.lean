-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Predecessor
import Mathlib.Analysis.Complex.Basic

namespace StrongSilver
open Set Real Complex Filter
open scoped Topology
noncomputable section

def subgraphDomain (u : ℝ → ℝ) : Set ℂ := {z | 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.im ≤ u z.re}

theorem complex_inner_coordinates (x y : ℂ) : inner ℝ x y = x.re*y.re+x.im*y.im := by
  rw [Complex.inner]
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring

theorem subgraphDomain_closed {u : ℝ → ℝ} (hu : Continuous u) : IsClosed (subgraphDomain u) :=
  (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le Complex.continuous_im (hu.comp Complex.continuous_re)))

theorem subgraphDomain_convex {u : ℝ → ℝ} (hu : ConcaveOn ℝ (Ici (0 : ℝ)) u) :
    Convex ℝ (subgraphDomain u) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx0,hxy,hxu⟩ := hx
  obtain ⟨hy0,hyy,hyu⟩ := hy
  have hc := hu.2 hx0 hy0 ha hb hab
  simp only [smul_eq_mul] at hc
  change 0 ≤ (a • x+b • y).re ∧ 0 ≤ (a • x+b • y).im ∧ (a • x+b • y).im ≤ u ((a • x+b • y).re)
  simp only [Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  refine ⟨add_nonneg (mul_nonneg ha hx0) (mul_nonneg hb hy0),
    add_nonneg (mul_nonneg ha hxy) (mul_nonneg hb hyy),?_⟩
  have hax := mul_le_mul_of_nonneg_left hxu ha
  have hby := mul_le_mul_of_nonneg_left hyu hb
  linarith

theorem subgraph_axis_mem {u : ℝ → ℝ} (hu : ∀ x, 0 ≤ x → 0 ≤ u x) {x : ℝ} (hx : 0 ≤ x) :
    (⟨x,0⟩ : ℂ) ∈ subgraphDomain u := ⟨hx,le_rfl,hu x hx⟩

theorem subgraph_normal_re_zero {u : ℝ → ℝ} (hu : ∀ x, 0 ≤ x → 0 ≤ u x) {z q : ℂ}
    (hz : 0 < z.re) (hq : OutwardNormal (subgraphDomain u) z q) (hvertical : q.im*z.im = 0) : q.re = 0 := by
  have hplus := hq (⟨2*z.re,0⟩ : ℂ) (subgraph_axis_mem hu (by positivity))
  have hminus := hq (⟨z.re/2,0⟩ : ℂ) (subgraph_axis_mem hu (by positivity))
  simp only [complex_inner_coordinates,Complex.sub_re,Complex.sub_im] at hplus hminus
  nlinarith only [hplus,hminus,hvertical,hz]

theorem subgraph_upper_normal_tangent {u : ℝ → ℝ} {z q : ℂ} {d : ℝ}
    (hu : ∀ x, 0 ≤ x → 0 ≤ u x) (hz : 0 < z.re) (hzu : z.im = u z.re)
    (hq : OutwardNormal (subgraphDomain u) z q) (hd : HasDerivAt u d z.re) : q.re+q.im*d = 0 := by
  let f := fun t : ℝ => q.re*(t-z.re)+q.im*(u t-z.im)
  have hm : IsLocalMax f z.re := by
    have ht : ∀ᶠ t in 𝓝 z.re, 0 < t := Ioi_mem_nhds hz
    filter_upwards [ht] with t ht
    have hh := hq (⟨t,u t⟩ : ℂ) ⟨ht.le,hu t ht.le,le_rfl⟩
    simp only [complex_inner_coordinates,Complex.sub_re,Complex.sub_im] at hh
    simpa only [f,sub_self,hzu,mul_zero,zero_add] using hh
  have hf := (((hasDerivAt_id z.re).sub_const z.re).const_mul q.re).add ((hd.sub_const z.im).const_mul q.im)
  have he := hm.hasDerivAt_eq_zero hf
  simpa only [mul_one] using he

/-- Normal orthogonality for a nonnegative differentiable concave graph.
This is the exact condition needed by the predecessor existence theorem. -/
theorem subgraph_normal_orthogonal {u du : ℝ → ℝ} (hu : ∀ x, 0 ≤ x → 0 ≤ u x) (hu0 : u 0 = 0)
    (hdu : ∀ x, 0 < x → HasDerivAt u (du x) x) (G : ℂ → ℂ) (hG0 : G 0 = 0)
    (haxis : ∀ x, 0 ≤ x → (G (⟨x,0⟩ : ℂ)).im = 0)
    (hgraph : ∀ x, 0 < x → (G (⟨x,u x⟩ : ℂ)).im = du x*(G (⟨x,u x⟩ : ℂ)).re)
    {z q : ℂ} (hz : z ∈ subgraphDomain u) (hq : OutwardNormal (subgraphDomain u) z q) :
    inner ℝ q (G z) = 0 := by
  obtain ⟨hz0,hzi,hzu⟩ := hz
  by_cases hzre : z.re = 0
  · have hzime : z.im = 0 := by rw [hzre,hu0] at hzu; linarith
    have hz0' : z = 0 := Complex.ext hzre hzime
    rw [hz0',hG0,inner_zero_right]
  have hzpos : 0 < z.re := lt_of_le_of_ne hz0 (Ne.symm hzre)
  by_cases hzim : z.im = 0
  · have hqr := subgraph_normal_re_zero hu hzpos hq (by rw [hzim,mul_zero])
    have hzaxis : z = (⟨z.re,0⟩ : ℂ) := Complex.ext rfl hzim
    have hGi : (G z).im = 0 := by rw [hzaxis]; exact haxis z.re hz0
    rw [complex_inner_coordinates,hqr,hGi,zero_mul,mul_zero,zero_add]
  by_cases hboundary : z.im = u z.re
  · have hnormal := subgraph_upper_normal_tangent hu hzpos hboundary hq (hdu z.re hzpos)
    have hzgraph : z = (⟨z.re,u z.re⟩ : ℂ) := Complex.ext rfl hboundary
    have hGi : (G z).im = du z.re*(G z).re := by rw [hzgraph]; exact hgraph z.re hzpos
    rw [complex_inner_coordinates,hGi]
    nlinarith only [congrArg (fun x : ℝ => x*(G z).re) hnormal]
  · have hzbetween : 0 < z.im ∧ z.im < u z.re :=
      ⟨lt_of_le_of_ne hzi (Ne.symm hzim),lt_of_le_of_ne hzu hboundary⟩
    have htop := hq (⟨z.re,u z.re⟩ : ℂ) ⟨hz0,hu z.re hz0,le_rfl⟩
    have hbottom := hq (⟨z.re,0⟩ : ℂ) (subgraph_axis_mem hu hz0)
    simp only [complex_inner_coordinates,Complex.sub_re,Complex.sub_im] at htop hbottom
    have hqi : q.im = 0 := by nlinarith only [htop,hbottom,hzbetween.1,hzbetween.2]
    have hqr := subgraph_normal_re_zero hu hzpos hq (by rw [hqi,zero_mul])
    simp only [complex_inner_coordinates,hqr,hqi,zero_mul,zero_add]

end
end StrongSilver
