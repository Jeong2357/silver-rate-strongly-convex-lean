-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Calculus
import StrongSilver.FiniteInterpolation

namespace StrongSilver
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

def stronglyConvexObjective (μ : ℝ) (f : V → ℝ) (x : V) : ℝ :=
  (μ/2)*‖x‖^2 + (1-μ)*f x

def stronglyConvexGradient (μ : ℝ) (g : V → V) (x : V) : V :=
  μ • x + (1-μ) • g x

theorem strongify_convex {μ : ℝ} {f : V → ℝ} (hμ : μ ≤ 1)
    (hf : ConvexOn ℝ Set.univ f) :
    StrongConvexOn Set.univ μ (stronglyConvexObjective μ f) := by
  apply strongConvexOn_iff_convex.mpr
  convert! hf.smul (sub_nonneg.mpr hμ) using 1
  funext x
  simp only [stronglyConvexObjective, Pi.smul_apply, smul_eq_mul]
  ring

theorem strongify_gradient {μ : ℝ} {f : V → ℝ} {g : V → V}
    (hg : ∀ x, HasGradientAt f (g x) x) (x : V) :
    HasGradientAt (stronglyConvexObjective μ f) (stronglyConvexGradient μ g x) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert! (quadratic_hasGradientAt μ x).hasFDerivAt.add
    ((hg x).hasFDerivAt.const_mul (1-μ)) using 1
  ext y
  simp only [stronglyConvexGradient, map_add, map_smul]

theorem strongify_smooth {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) {g : V → V}
    (hg : ∀ x y, ‖g x-g y‖ ≤ ‖x-y‖) (x y : V) :
    ‖stronglyConvexGradient μ g x-stronglyConvexGradient μ g y‖ ≤ ‖x-y‖ := by
  have he : stronglyConvexGradient μ g x-stronglyConvexGradient μ g y =
      μ • (x-y)+(1-μ) • (g x-g y) := by unfold stronglyConvexGradient; module
  rw [he]
  calc
    _ ≤ ‖μ • (x-y)‖+‖(1-μ) • (g x-g y)‖ := norm_add_le _ _
    _ = μ*‖x-y‖+(1-μ)*‖g x-g y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hμ, abs_of_nonneg (sub_nonneg.mpr hμ1)]
    _ ≤ μ*‖x-y‖+(1-μ)*‖x-y‖ := by gcongr; exact hg x y
    _ = ‖x-y‖ := by ring

theorem strongify_admissible {κ : ℝ} (hκ : 1 ≤ κ) {f : V → ℝ} {g : V → V}
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hl : ∀ x y, ‖g x-g y‖ ≤ ‖x-y‖) :
    Admissible κ (stronglyConvexObjective (1/κ) f) (stronglyConvexGradient (1/κ) g) := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hμ : 0 ≤ 1/κ := by positivity
  have hμ1 : 1/κ ≤ 1 := (div_le_one hκpos).mpr hκ
  exact ⟨strongify_convex hμ1 hf, strongify_gradient hg, strongify_smooth hμ hμ1 hl⟩

/-- The selected construction curvature may exceed the class modulus 1/κ. -/
theorem strongify_admissible_curvature {κ μ : ℝ} (hκ : 1 ≤ κ) (hμ : 1/κ ≤ μ) (hμ1 : μ ≤ 1)
    {f : V → ℝ} {g : V → V} (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ x, HasGradientAt f (g x) x) (hl : ∀ x y, ‖g x-g y‖ ≤ ‖x-y‖) :
    Admissible κ (stronglyConvexObjective μ f) (stronglyConvexGradient μ g) := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hμ0 : 0 ≤ μ := le_trans (by positivity) hμ
  exact ⟨StrongConvexOn.mono hμ (strongify_convex hμ1 hf),
    strongify_gradient hg,strongify_smooth hμ0 hμ1 hl⟩

variable [ProperSpace V]

theorem moreau_admissible {κ : ℝ} (hκ : 1 ≤ κ) (P : Moreau.Epigraph V) :
    Admissible κ (stronglyConvexObjective (1/κ) (Moreau.envelope P))
      (stronglyConvexGradient (1/κ) (Moreau.gradient P)) :=
  strongify_admissible hκ (Moreau.envelope_convex P) (Moreau.envelope_hasGradientAt P)
    (Moreau.gradient_lipschitz P)

theorem moreau_admissible_curvature {κ μ : ℝ} (hκ : 1 ≤ κ) (hμ : 1/κ ≤ μ) (hμ1 : μ ≤ 1)
    (P : Moreau.Epigraph V) :
    Admissible κ (stronglyConvexObjective μ (Moreau.envelope P))
      (stronglyConvexGradient μ (Moreau.gradient P)) :=
  strongify_admissible_curvature hκ hμ hμ1 (Moreau.envelope_convex P)
    (Moreau.envelope_hasGradientAt P) (Moreau.gradient_lipschitz P)

theorem moreau_strong_interpolates (μ : ℝ) (P : Moreau.Epigraph V) (z g : V) (t : ℝ)
    (hs : Moreau.Supports P z t g) :
    stronglyConvexGradient μ (Moreau.gradient P) (z+g) = μ • (z+g)+(1-μ) • g ∧
    stronglyConvexObjective μ (Moreau.envelope P) (z+g) =
      (μ/2)*‖z+g‖^2+(1-μ)*(t+‖g‖^2/2) := by
  obtain ⟨hg, hf⟩ := Moreau.envelope_interpolates P z g t hs
  simp only [stronglyConvexGradient, stronglyConvexObjective, hg, hf, and_self]

theorem moreau_strong_minimizer {κ : ℝ} (hκ : 1 ≤ κ) (P : Moreau.Epigraph V) (x : V) :
    stronglyConvexObjective (1/κ) (Moreau.envelope P) 0 ≤
      stronglyConvexObjective (1/κ) (Moreau.envelope P) x := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hμ1 : 1/κ ≤ 1 := (div_le_one hκpos).mpr hκ
  simp only [stronglyConvexObjective, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, Moreau.envelope_zero, add_zero]
  exact add_nonneg (by positivity) (mul_nonneg (sub_nonneg.mpr hμ1) (Moreau.envelope_nonnegative P x))

end
end StrongSilver
