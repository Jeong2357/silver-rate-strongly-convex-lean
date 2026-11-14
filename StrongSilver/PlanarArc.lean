-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarNormalAngle

namespace StrongSilver
open Set Real Complex
noncomputable section

def rotatedPolarNormal (k θ : ℝ) : ℂ := (-k) • polarUnit θ+polarTangent θ
def polarArc (r : ℝ → ℝ) (θ : ℝ) : ℂ := r θ • polarUnit θ

theorem rotatedPolarNormal_angle (k θ : ℝ) :
    rotatedPolarNormal k θ = Real.sqrt (1+k^2) • polarTangent (normalAngle k θ) := by
  have hs : Real.sqrt (1+k^2) ≠ 0 := (Real.sqrt_pos.2 (by positivity : 0 < 1+k^2)).ne'
  apply Complex.ext
  · simp only [rotatedPolarNormal,polarUnit,polarTangent,normalAngle,Complex.add_re,Complex.smul_re,smul_eq_mul,
      Real.sin_add,Real.cos_arctan,Real.sin_arctan]
    field_simp
    <;> ring
  · simp only [rotatedPolarNormal,polarUnit,polarTangent,normalAngle,Complex.add_im,Complex.smul_im,smul_eq_mul,
      Real.cos_add,Real.cos_arctan,Real.sin_arctan]
    field_simp
    <;> ring

theorem polarArc_hasDerivAt {r k : ℝ → ℝ} {θ : ℝ} (hr : HasDerivAt r (-k θ*r θ) θ) :
    HasDerivAt (polarArc r) (r θ • rotatedPolarNormal (k θ) θ) θ := by
  have hh := hr.smul (polarUnit_hasDerivAt θ)
  convert! hh using 1
  unfold rotatedPolarNormal
  module

def arcSupportDerivative (r k : ℝ → ℝ) (θ s : ℝ) : ℝ :=
  r s*Real.sqrt (1+(k θ)^2)*Real.sqrt (1+(k s)^2)*
    Real.sin (normalAngle (k θ) θ-normalAngle (k s) s)

theorem arcSupport_hasDerivAt {r k : ℝ → ℝ} {s : ℝ} (hr : HasDerivAt r (-k s*r s) s) (θ : ℝ) :
    HasDerivAt (fun t => inner ℝ (polarNormal (k θ) θ) (polarArc r t))
      (arcSupportDerivative r k θ s) s := by
  have hh := (hasDerivAt_const s (polarNormal (k θ) θ)).inner ℝ (polarArc_hasDerivAt hr)
  simp only [inner_zero_left,add_zero] at hh
  convert! hh using 1
  rw [polarNormal_angle,rotatedPolarNormal_angle,real_inner_smul_left,real_inner_smul_right,
    real_inner_smul_right,polarUnit_inner_tangent]
  unfold arcSupportDerivative
  ring

/-- Increasing first-quadrant normal angles give supporting normals for the
entire radial arc. This supplies the convex-hull support calculation in §3.3. -/
theorem polarArc_support {Θ : ℝ} {r k : ℝ → ℝ}
    (hr : ∀ s ∈ Icc (0 : ℝ) Θ, HasDerivAt r (-k s*r s) s)
    (hrpos : ∀ s ∈ Icc (0 : ℝ) Θ, 0 ≤ r s)
    (hmono : MonotoneOn (fun s => normalAngle (k s) s) (Icc 0 Θ))
    (hangle : ∀ s ∈ Icc (0 : ℝ) Θ, 0 ≤ normalAngle (k s) s ∧ normalAngle (k s) s ≤ Real.pi/2)
    {θ s : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Θ) (hs : s ∈ Icc (0 : ℝ) Θ) :
    inner ℝ (polarNormal (k θ) θ) (polarArc r s) ≤ inner ℝ (polarNormal (k θ) θ) (polarArc r θ) := by
  let f : ℝ → ℝ := fun t => inner ℝ (polarNormal (k θ) θ) (polarArc r t)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Θ) : HasDerivAt f (arcSupportDerivative r k θ t) t :=
    arcSupport_hasDerivAt (hr t ht) θ
  have hcoef (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Θ) :
      0 ≤ r t*Real.sqrt (1+(k θ)^2)*Real.sqrt (1+(k t)^2) := by
    exact mul_nonneg (mul_nonneg (hrpos t ht) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  by_cases hst : s ≤ θ
  · have hsub : Icc (0 : ℝ) θ ⊆ Icc (0 : ℝ) Θ := Icc_subset_Icc le_rfl hθ.2
    have hm : MonotoneOn f (Icc 0 θ) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (fun t ht => (hd t (hsub ht)).continuousAt.continuousWithinAt)
        (fun t ht => (hd t (hsub (interior_subset ht))).differentiableAt.differentiableWithinAt)
      intro t ht
      have ht0 := hsub (interior_subset ht)
      have htθ : t ≤ θ := (interior_subset ht).2
      rw [(hd t ht0).deriv]
      unfold arcSupportDerivative
      apply mul_nonneg (hcoef t ht0)
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · exact sub_nonneg.mpr (hmono ht0 hθ htθ)
      · linarith [(hangle θ hθ).2,(hangle t ht0).1,Real.pi_pos]
    exact hm ⟨hs.1,hst⟩ ⟨hθ.1,le_rfl⟩ hst
  · have hθs : θ ≤ s := le_of_not_ge hst
    have hsub : Icc θ Θ ⊆ Icc (0 : ℝ) Θ := Icc_subset_Icc hθ.1 le_rfl
    have hm : AntitoneOn f (Icc θ Θ) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
        (fun t ht => (hd t (hsub ht)).continuousAt.continuousWithinAt)
        (fun t ht => (hd t (hsub (interior_subset ht))).differentiableAt.differentiableWithinAt)
      intro t ht
      have ht0 := hsub (interior_subset ht)
      have hθt : θ ≤ t := (interior_subset ht).1
      rw [(hd t ht0).deriv]
      unfold arcSupportDerivative
      apply mul_nonpos_of_nonneg_of_nonpos (hcoef t ht0)
      apply Real.sin_nonpos_of_nonpos_of_neg_pi_le
      · exact sub_nonpos.mpr (hmono hθ ht0 hθt)
      · linarith [(hangle θ hθ).1,(hangle t ht0).2,Real.pi_pos]
    exact hm ⟨le_rfl,hθ.2⟩ ⟨hθs,hs.2⟩ hθs

end
end StrongSilver
