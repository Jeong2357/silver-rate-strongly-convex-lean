-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ClosedHullBody
import StrongSilver.ArcRadius

namespace StrongSilver
open Set Real Complex
noncomputable section

theorem polarArc_continuousOn {Θ : ℝ} {r : ℝ → ℝ} (hr : ContinuousOn r (Icc (0 : ℝ) Θ)) :
    ContinuousOn (polarArc r) (Icc (0 : ℝ) Θ) :=
  hr.smul (fun θ hθ => (polarUnit_hasDerivAt θ).continuousAt.continuousWithinAt)

def radialArcBody (Θ : ℝ) (r : ℝ → ℝ) (hr : ContinuousOn r (Icc (0 : ℝ) Θ)) : CompactConvexBody ℂ :=
  bodyOfCompact (insert 0 (polarArc r '' Icc (0 : ℝ) Θ))
    ((isCompact_Icc.image_of_continuousOn (polarArc_continuousOn hr)).insert 0) (mem_insert _ _)

theorem polarArc_mem_body {Θ θ : ℝ} {r : ℝ → ℝ} (hr : ContinuousOn r (Icc (0 : ℝ) Θ))
    (hθ : θ ∈ Icc (0 : ℝ) Θ) : polarArc r θ ∈ (radialArcBody Θ r hr).carrier := by
  apply mem_bodyOfCompact
  exact mem_insert_of_mem _ (mem_image_of_mem (polarArc r) hθ)

theorem polarNormal_arc_value (k θ R : ℝ) : inner ℝ (polarNormal k θ) (R • polarUnit θ) = R := by
  have horth : inner ℝ (polarTangent θ) (polarUnit θ) = 0 := by
    have hh := real_inner_comm (polarUnit θ) (polarTangent θ)
    simpa only [polarUnit_inner_tangent,sub_self,Real.sin_zero] using hh
  rw [polarNormal,inner_add_left,real_inner_smul_left,real_inner_smul_right,real_inner_smul_right,
    polarUnit_inner,horth,sub_self,Real.cos_zero,mul_one,mul_zero,mul_zero,add_zero]

theorem radialArcBody_normal {Θ θ : ℝ} {r k : ℝ → ℝ} (hr : ContinuousOn r (Icc (0 : ℝ) Θ))
    (hθ : θ ∈ Icc (0 : ℝ) Θ) (hrθ : 0 ≤ r θ)
    (hsupport : ∀ s ∈ Icc (0 : ℝ) Θ,
      inner ℝ (polarNormal (k θ) θ) (polarArc r s) ≤ inner ℝ (polarNormal (k θ) θ) (polarArc r θ)) :
    ∀ w ∈ (radialArcBody Θ r hr).carrier, inner ℝ (polarNormal (k θ) θ) (w-polarArc r θ) ≤ 0 := by
  have hsource : ∀ w ∈ insert 0 (polarArc r '' Icc (0 : ℝ) Θ),
      inner ℝ (polarNormal (k θ) θ) w ≤ inner ℝ (polarNormal (k θ) θ) (polarArc r θ) := by
    intro w hw
    rcases mem_insert_iff.mp hw with rfl | hw
    · rw [inner_zero_right]
      change 0 ≤ inner ℝ (polarNormal (k θ) θ) (r θ • polarUnit θ)
      rw [polarNormal_arc_value]
      exact hrθ
    · obtain ⟨s,hs,rfl⟩ := hw
      exact hsupport s hs
  have hbody := bodyOfCompact_inner_le
    ((isCompact_Icc.image_of_continuousOn (polarArc_continuousOn hr)).insert 0)
    (mem_insert (0 : ℂ) _) (polarNormal (k θ) θ) (inner ℝ (polarNormal (k θ) θ) (polarArc r θ)) hsource
  intro w hw
  rw [inner_sub_right]
  exact sub_nonpos.mpr (hbody w hw)

/-- Every nonnegative normal displacement projects back to the specified arc point. -/
theorem radialArcBody_projection {Θ θ t : ℝ} {r k : ℝ → ℝ} (hr : ContinuousOn r (Icc (0 : ℝ) Θ))
    (hθ : θ ∈ Icc (0 : ℝ) Θ) (hrθ : 0 ≤ r θ) (ht : 0 ≤ t)
    (hsupport : ∀ s ∈ Icc (0 : ℝ) Θ,
      inner ℝ (polarNormal (k θ) θ) (polarArc r s) ≤ inner ℝ (polarNormal (k θ) θ) (polarArc r θ)) :
    (radialArcBody Θ r hr).projection (polarArc r θ+t • polarNormal (k θ) θ) = polarArc r θ := by
  apply CompactConvexBody.projection_eq_of_normal _ _ _ (polarArc_mem_body hr hθ)
  intro w hw
  rw [add_sub_cancel_left,real_inner_smul_left]
  exact mul_nonpos_of_nonneg_of_nonpos ht (radialArcBody_normal hr hθ hrθ hsupport w hw)

theorem smoothRadialArcBody_projection {k₀ Θ R θ t : ℝ} (hk : 0 < k₀) (hk1 : k₀ ≤ 1/2)
    (hΘ : Θ < Real.pi/2) (hR : 0 ≤ R) (hθ : θ ∈ Icc (0 : ℝ) Θ) (ht : 0 ≤ t) :
    let r := arcRadius Θ R (smoothPlanarSlope k₀)
    let hc : ContinuousOn r (Icc (0 : ℝ) Θ) := fun s hs =>
      (smoothArcRadius_hasDerivAt hk hk1 hΘ hs).continuousAt.continuousWithinAt
    (radialArcBody Θ r hc).projection
      (polarArc r θ+t • polarNormal (smoothPlanarSlope k₀ θ) θ) = polarArc r θ := by
  dsimp only
  have hpos : 0 ≤ arcRadius Θ R (smoothPlanarSlope k₀) θ := mul_nonneg hR (Real.exp_pos _).le
  apply radialArcBody_projection _ hθ hpos ht
  intro s hs
  exact smoothPolarArc_support hk hk1 hΘ hR hθ hs

end
end StrongSilver
