-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarBoundaryExistence
import StrongSilver.PlanarEndpoint

namespace StrongSilver
open Real Set Complex
noncomputable section

def planarBoundaryCurve (r k J : ℝ → ℝ) (θ : ℝ) : ℂ :=
  (r θ+J θ/k θ) • polarUnit θ+J θ • polarTangent θ

def planarBoundaryField (μ : ℝ) (r k J : ℝ → ℝ) (θ : ℝ) : ℂ :=
  (r θ+μ*J θ/k θ) • polarUnit θ+(μ*J θ) • polarTangent θ

theorem planarBoundaryCurve_eq_normal {r k J : ℝ → ℝ} {θ : ℝ} (hk : k θ ≠ 0) :
    planarBoundaryCurve r k J θ = polarArc r θ+(J θ/k θ) • polarNormal (k θ) θ := by
  have he : (J θ/k θ)*k θ = J θ := div_mul_cancel₀ _ hk
  unfold planarBoundaryCurve polarArc polarNormal
  simp only [smul_add,smul_smul,he]
  module

theorem planarBoundaryCurve_hasDerivWithinAt {r k J : ℝ → ℝ} {θ k' J' : ℝ} {S : Set ℝ}
    (hr : HasDerivWithinAt r (-k θ*r θ) S θ) (hk : HasDerivWithinAt k k' S θ)
    (hJ : HasDerivWithinAt J J' S θ) (hk0 : k θ ≠ 0) :
    HasDerivWithinAt (planarBoundaryCurve r k J)
      (planarDerivativeRadial (r θ) (k θ) k' (J θ) J' • polarUnit θ+
        planarDerivativeTransverse (r θ) (k θ) (J θ) J' • polarTangent θ) S θ := by
  have he := (polarUnit_hasDerivAt θ).hasDerivWithinAt (s := S)
  have hep := (polarTangent_hasDerivAt θ).hasDerivWithinAt (s := S)
  have hh := ((hr.add (hJ.div hk hk0)).smul he).add (hJ.smul hep)
  simp only [Pi.add_apply,Pi.div_apply] at hh
  convert! hh using 1
  unfold planarDerivativeRadial planarDerivativeTransverse
  module

theorem planarBoundaryCurve_hasDerivWithinAt_field {μ : ℝ} {r k J : ℝ → ℝ} {θ k' : ℝ} {S : Set ℝ}
    (hr : HasDerivWithinAt r (-k θ*r θ) S θ) (hk : HasDerivWithinAt k k' S θ)
    (hJ : HasDerivWithinAt J (planarRiccati μ (r θ) (k θ) k' (J θ)) S θ)
    (hμ : 0 ≤ μ) (hr0 : 0 < r θ) (hk0 : 0 < k θ) (hk' : -1 < k') (hJ0 : 0 ≤ J θ) :
    ∃ t : ℝ, t < 0 ∧ HasDerivWithinAt (planarBoundaryCurve r k J) (t • planarBoundaryField μ r k J θ) S θ := by
  obtain ⟨t,ht,hx,hy⟩ := planar_boundary_negative_multiple hμ hr0 hk0 hk' hJ0
  have hh := planarBoundaryCurve_hasDerivWithinAt hr hk hJ hk0.ne'
  rw [hx,hy] at hh
  refine ⟨t,ht,?_⟩
  convert! hh using 1
  unfold planarBoundaryField
  module

theorem planarBoundaryField_is_gradient {Θ μ : ℝ} {r k J : ℝ → ℝ}
    (hc : ContinuousOn r (Icc (0 : ℝ) Θ)) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Θ)
    (hr : 0 ≤ r θ) (hk : 0 < k θ) (hJ : 0 ≤ J θ)
    (hsupport : ∀ s ∈ Icc (0 : ℝ) Θ,
      inner ℝ (polarNormal (k θ) θ) (polarArc r s) ≤ inner ℝ (polarNormal (k θ) θ) (polarArc r θ)) :
    stronglyConvexGradient μ (Moreau.gradient (radialArcBody Θ r hc).supportEpigraph)
      (planarBoundaryCurve r k J θ) = planarBoundaryField μ r k J θ := by
  have hp := radialArcBody_projection hc hθ hr (div_nonneg hJ hk.le) hsupport
  have he := planarBoundaryCurve_eq_normal (r := r) (J := J) hk.ne'
  unfold stronglyConvexGradient
  rw [(radialArcBody Θ r hc).support_envelope_gradient,he,hp]
  unfold polarArc polarNormal planarBoundaryField
  have hcanc : (J θ/k θ)*k θ = J θ := div_mul_cancel₀ _ hk.ne'
  simp only [smul_add,smul_smul,hcanc]
  module

theorem planarBoundaryCurve_head {r k J : ℝ → ℝ} :
    planarBoundaryCurve r k J 0 = (⟨r 0+J 0/k 0,J 0⟩ : ℂ) := by
  apply Complex.ext <;>
    simp only [planarBoundaryCurve,polarUnit,polarTangent,Real.cos_zero,Real.sin_zero,
      Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul,
      neg_zero,mul_zero,mul_one,zero_add,add_zero]

theorem planarBoundaryCurve_terminal {r k J : ℝ → ℝ} {Θ : ℝ} (hJ : J Θ = 0) :
    planarBoundaryCurve r k J Θ = polarArc r Θ := by
  simp only [planarBoundaryCurve,hJ,zero_div,add_zero,zero_smul,polarArc]

end
end StrongSilver
