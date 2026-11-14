-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarTurning

namespace StrongSilver
open Set Complex
open scoped Topology
noncomputable section

theorem complex_curve_re_hasDerivWithinAt {γ : ℝ → ℂ} {v : ℂ} {S : Set ℝ} {θ : ℝ}
    (hγ : HasDerivWithinAt γ v S θ) : HasDerivWithinAt (fun t => (γ t).re) v.re S θ := by
  convert! Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt θ hγ using 1

theorem complex_curve_im_hasDerivWithinAt {γ : ℝ → ℂ} {v : ℂ} {S : Set ℝ} {θ : ℝ}
    (hγ : HasDerivWithinAt γ v S θ) : HasDerivWithinAt (fun t => (γ t).im) v.im S θ := by
  convert! Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt θ hγ using 1

theorem planar_curve_coordinates_antitone {a b : ℝ} {γ F : ℝ → ℂ}
    (hγ : ∀ θ ∈ Icc a b, ∃ t : ℝ, t < 0 ∧ HasDerivWithinAt γ (t • F θ) (Icc a b) θ)
    (hF : ∀ θ ∈ Icc a b, 0 < (F θ).re ∧ 0 ≤ (F θ).im) :
    StrictAntiOn (fun θ => (γ θ).re) (Icc a b) ∧ AntitoneOn (fun θ => (γ θ).im) (Icc a b) := by
  have hxc : ContinuousOn (fun θ => (γ θ).re) (Icc a b) := by
    intro θ hθ
    obtain ⟨t,ht,hd⟩ := hγ θ hθ
    exact (complex_curve_re_hasDerivWithinAt hd).continuousWithinAt
  have hyc : ContinuousOn (fun θ => (γ θ).im) (Icc a b) := by
    intro θ hθ
    obtain ⟨t,ht,hd⟩ := hγ θ hθ
    exact (complex_curve_im_hasDerivWithinAt hd).continuousWithinAt
  constructor
  · apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hxc
    intro θ hθ
    have ht0 := interior_subset hθ
    obtain ⟨t,ht,hd⟩ := hγ θ ht0
    have hx := (complex_curve_re_hasDerivWithinAt hd).hasDerivAt (mem_interior_iff_mem_nhds.mp hθ)
    rw [hx.deriv,Complex.smul_re,smul_eq_mul]
    exact mul_neg_of_neg_of_pos ht (hF θ ht0).1
  · apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hyc
    · intro θ hθ
      obtain ⟨t,ht,hd⟩ := hγ θ (interior_subset hθ)
      exact ((complex_curve_im_hasDerivWithinAt hd).hasDerivAt (mem_interior_iff_mem_nhds.mp hθ)).differentiableAt.differentiableWithinAt
    · intro θ hθ
      have ht0 := interior_subset hθ
      obtain ⟨t,ht,hd⟩ := hγ θ ht0
      have hy := (complex_curve_im_hasDerivWithinAt hd).hasDerivAt (mem_interior_iff_mem_nhds.mp hθ)
      rw [hy.deriv,Complex.smul_im,smul_eq_mul]
      exact mul_nonpos_of_nonpos_of_nonneg ht.le (hF θ ht0).2

end
end StrongSilver
