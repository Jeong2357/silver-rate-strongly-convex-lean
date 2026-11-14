-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarCurveMonotonicity

namespace StrongSilver
open Set Complex
noncomputable section

def planarFieldSlope (F : ℝ → ℂ) (θ : ℝ) : ℝ := (F θ).im/(F θ).re

theorem planarFieldSlope_hasDerivWithinAt {F : ℝ → ℂ} {v : ℂ} {S : Set ℝ} {θ : ℝ}
    (hF : HasDerivWithinAt F v S θ) (hre : (F θ).re ≠ 0) :
    HasDerivWithinAt (planarFieldSlope F) (planarDet (F θ) v/(F θ).re^2) S θ := by
  have hh := (complex_curve_im_hasDerivWithinAt hF).div (complex_curve_re_hasDerivWithinAt hF) hre
  convert! hh using 1
  unfold planarDet
  ring

theorem planarFieldSlope_strictMonoOn {a b : ℝ} {F : ℝ → ℂ}
    (hpos : ∀ θ ∈ Icc a b, 0 < (F θ).re)
    (hF : ∀ θ ∈ Icc a b, ∃ v : ℂ, HasDerivWithinAt F v (Icc a b) θ ∧ 0 < planarDet (F θ) v) :
    StrictMonoOn (planarFieldSlope F) (Icc a b) := by
  have hc : ContinuousOn (planarFieldSlope F) (Icc a b) := by
    intro θ ht
    obtain ⟨v,hv,hvp⟩ := hF θ ht
    exact (planarFieldSlope_hasDerivWithinAt hv (hpos θ ht).ne').continuousWithinAt
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hc
  intro θ ht
  have ht0 := interior_subset ht
  obtain ⟨v,hv,hvp⟩ := hF θ ht0
  have hd := (planarFieldSlope_hasDerivWithinAt hv (hpos θ ht0).ne').hasDerivAt (mem_interior_iff_mem_nhds.mp ht)
  rw [hd.deriv]
  exact div_pos hvp (sq_pos_of_pos (hpos θ ht0))

end
end StrongSilver
