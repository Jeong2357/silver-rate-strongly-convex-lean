-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarDomainGeometry
import StrongSilver.Transform

namespace StrongSilver.PlanarBoundaryCertificate
open Set Real Complex
noncomputable section
variable {A μ : ℝ} (C : PlanarBoundaryCertificate A μ)
include C
set_option maxHeartbeats 1000000

def headShift (_C : PlanarBoundaryCertificate A μ) : ℝ := (1-μ)*planarRadius A 0/μ

theorem headShift_nonnegative (hμ : 0 < μ) : 0 ≤ C.headShift :=
  div_nonneg (mul_nonneg (sub_nonneg.mpr C.mu_lt_one.le) (C.radius_pos 0).le) hμ.le

theorem domain_head_projection {z : ℂ} (hz : z ∈ C.domain) (hx : C.right ≤ z.re) :
    C.body.projection z = (⟨planarRadius A 0,0⟩ : ℂ) := by
  have hu : z.im ≤ planarSlopeScale A*(z.re-planarRadius A 0) :=
    hz.2.2.trans (C.right_graph_in_head_region hx)
  have he : z = (⟨z.re,z.im⟩ : ℂ) := (Complex.eta z).symm
  rw [he]
  exact C.projection_head_region (C.right_ge_radius.trans hx) hz.2.1 hu

theorem head_step_coordinates (hμ : 0 < μ) {z : ℂ} (hz : z ∈ C.domain)
    (hx : C.right ≤ z.re) (b : ℝ) :
    (z-b • C.physical z).re+C.headShift = (1-μ*b)*(z.re+C.headShift) ∧
    (z-b • C.physical z).im = (1-μ*b)*z.im := by
  have hp : C.physical z = μ • z+(1-μ) • (⟨planarRadius A 0,0⟩ : ℂ) := by
    unfold physical stronglyConvexGradient
    rw [C.body.support_envelope_gradient,C.domain_head_projection hz hx]
  have hshift : μ*C.headShift = (1-μ)*planarRadius A 0 := by
    unfold headShift
    field_simp [hμ.ne']
  rw [hp]
  simp only [Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    Complex.smul_re,Complex.smul_im,smul_eq_mul,mul_zero,add_zero]
  constructor
  · have hbshift := congrArg (fun t : ℝ => b*t) hshift
    nlinarith only [hbshift]
  · ring

theorem minPrefixProduct_le_one (h : List ℝ) : minPrefixProduct μ h ≤ 1 := by
  cases h with
  | nil => exact le_rfl
  | cons b h => exact min_le_left _ _

/-- The size bounds (3.13), in a division-free form. They apply to every
domain-valued exact trajectory ending at the terminal point. -/
theorem trajectory_prefix_bounds (hμ : 0 < μ) (h : List ℝ)
    (hh : ∀ b ∈ h, μ*b < 1) (x : ℂ)
    (hend : iterate h C.physical x = (⟨planarEpsilon A,1⟩ : ℂ))
    (hstates : ∀ i : ℕ, i ≤ h.length → iterate (h.take i) C.physical x ∈ C.domain) :
    minPrefixProduct μ h*(x.re+C.headShift) ≤ C.right+C.headShift ∧
    minPrefixProduct μ h*x.im ≤ C.J 0 := by
  induction h generalizing x with
  | nil =>
    have he : x = (⟨planarEpsilon A,1⟩ : ℂ) := hend
    subst x
    simp only [minPrefixProduct,one_mul]
    exact ⟨by rw [← C.left_eq_epsilon]; linarith [C.left_lt_right],C.head_y_ge_one⟩
  | cons b h ih =>
    have hx : x ∈ C.domain := by simpa only [List.take_zero,iterate_nil] using hstates 0 (by omega)
    have hc := C.minPrefixProduct_le_one (b::h)
    have hshift := C.headShift_nonnegative hμ
    by_cases hhead : x.re ≤ C.right
    · have hy := C.domain_height_before_head hx hhead
      have hX := mul_le_mul_of_nonneg_right hc (add_nonneg hx.1 hshift)
      have hY := mul_le_mul_of_nonneg_right hc hx.2.1
      simp only [one_mul] at hX hY
      exact ⟨by linarith only [hX,hhead],hY.trans hy⟩
    · let z := x-b • C.physical x
      have hzstates : ∀ i : ℕ, i ≤ h.length → iterate (h.take i) C.physical z ∈ C.domain := by
        intro i hi
        have hs := hstates (i+1) (by simp only [List.length_cons]; omega)
        simpa only [List.take_succ_cons,iterate_cons] using hs
      have hzEnd : iterate h C.physical z = (⟨planarEpsilon A,1⟩ : ℂ) := by
        simpa only [iterate_cons] using hend
      have hi := ih (fun a ha => hh a (List.mem_cons_of_mem b ha)) z hzEnd hzstates
      have hstep := C.head_step_coordinates hμ hx (le_of_not_ge hhead) b
      change z.re+C.headShift = (1-μ*b)*(x.re+C.headShift) ∧ z.im = (1-μ*b)*x.im at hstep
      rw [hstep.1,hstep.2] at hi
      have hmin : minPrefixProduct μ (b::h) ≤ (1-μ*b)*minPrefixProduct μ h := min_le_right _ _
      have hX := mul_le_mul_of_nonneg_right hmin (add_nonneg hx.1 hshift)
      have hY := mul_le_mul_of_nonneg_right hmin hx.2.1
      constructor <;> nlinarith only [hi.1,hi.2,hX,hY]

theorem terminal_trajectory_size_bounds (hμ : 0 < μ) (h : List ℝ)
    (hh : ∀ b ∈ h, μ*b < 1) :
    ∃ x ∈ C.domain, iterate h C.physical x = (⟨planarEpsilon A,1⟩ : ℂ) ∧
      x.re ≤ C.right/minPrefixProduct μ h+
        C.headShift*((minPrefixProduct μ h)⁻¹-1) ∧
      x.im ≤ C.J 0/minPrefixProduct μ h := by
  obtain ⟨x,hx,hend,hstates⟩ := C.terminal_trajectory_exists h (fun b hb => by linarith [hh b hb])
  have hbounds := C.trajectory_prefix_bounds hμ h hh x hend hstates
  have hc := minPrefixProduct_positive h hh
  refine ⟨x,hx,hend,?_,(le_div_iff₀ hc).mpr (by nlinarith only [hbounds.2])⟩
  have hd : x.re+C.headShift ≤ (C.right+C.headShift)/minPrefixProduct μ h :=
    (le_div_iff₀ hc).mpr (by nlinarith only [hbounds.1])
  calc
    x.re ≤ (C.right+C.headShift)/minPrefixProduct μ h-C.headShift := by linarith only [hd]
    _ = C.right/minPrefixProduct μ h+C.headShift*((minPrefixProduct μ h)⁻¹-1) := by ring

end
end StrongSilver.PlanarBoundaryCertificate
