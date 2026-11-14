-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LogarithmicCutoff
import Mathlib.Analysis.Calculus.MeanValue

namespace StrongSilver
open Real Set
noncomputable section
set_option maxHeartbeats 6200000

theorem logarithmicCutoff_hasDerivAt {μ P : ℝ} (hμ : 0 < μ) (y : ℝ) :
    HasDerivAt (logarithmicCutoff μ P) (Real.exp (-μ*(P+Real.exp y))*Real.exp y) y := by
  have h := ((hasDerivAt_const y (1:ℝ)).sub
    ((((hasDerivAt_const y P).add (hasDerivAt_id y).exp).const_mul (-μ)).exp)).div_const μ
  change HasDerivAt (logarithmicCutoff μ P)
    ((0-Real.exp (-μ*(P+Real.exp y))*(-μ*(0+Real.exp y*1)))/μ) y at h
  have he : (0-Real.exp (-μ*(P+Real.exp y))*(-μ*(0+Real.exp y*1)))/μ =
      Real.exp (-μ*(P+Real.exp y))*Real.exp y := by field_simp [hμ.ne'] <;> ring
  rwa [he] at h

/-- The logarithm of the inverse cutoff has derivative between zero
and one for every height; this uses only positive curvature and pad. -/
theorem logCutoff_derivative_bounds {μ P : ℝ} (hμ : 0 < μ) (hP : 0 ≤ P) (y : ℝ) :
    0 ≤ (Real.exp (-μ*(P+Real.exp y))*Real.exp y)/logarithmicCutoff μ P y ∧
    (Real.exp (-μ*(P+Real.exp y))*Real.exp y)/logarithmicCutoff μ P y ≤ 1 := by
  have hA := logarithmicCutoff_positive (y:=y) hμ hP
  refine ⟨div_nonneg (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le hA.le,?_⟩
  apply (div_le_iff₀ hA).mpr
  rw [one_mul]
  unfold logarithmicCutoff
  apply (le_div_iff₀ hμ).mpr
  have hExp := Real.add_one_le_exp (μ*(P+Real.exp y))
  have hPμ := mul_nonneg hμ.le hP
  have hScale := mul_le_mul_of_nonneg_right hExp (Real.exp_pos (-μ*(P+Real.exp y))).le
  have hCancel : Real.exp (μ*(P+Real.exp y))*Real.exp (-μ*(P+Real.exp y)) = 1 := by
    rw [← Real.exp_add,show μ*(P+Real.exp y)+ -μ*(P+Real.exp y) = 0 by ring,Real.exp_zero]
  rw [hCancel] at hScale
  have hPadScale := mul_nonneg hPμ (Real.exp_pos (-μ*(P+Real.exp y))).le
  nlinarith only [hScale,hPadScale]

/-- The inverse logarithmic cutoff is 1-Lipschitz in logarithmic
scale, so the smoothed band weights can be transported to height. -/
theorem logCutoff_lipschitz {μ P : ℝ} (hμ : 0 < μ) (hP : 0 ≤ P) (x y : ℝ) :
    |Real.log (logarithmicCutoff μ P y)-Real.log (logarithmicCutoff μ P x)| ≤ |y-x| := by
  have hD (z : ℝ) : HasDerivAt (fun z => Real.log (logarithmicCutoff μ P z))
      ((Real.exp (-μ*(P+Real.exp z))*Real.exp z)/logarithmicCutoff μ P z) z :=
    (logarithmicCutoff_hasDerivAt hμ z).log (logarithmicCutoff_positive hμ hP).ne'
  have hBounds (z : ℝ) : ‖deriv (fun z => Real.log (logarithmicCutoff μ P z)) z‖ ≤ (1:ℝ) := by
    rw [(hD z).deriv,Real.norm_eq_abs,abs_of_nonneg (logCutoff_derivative_bounds hμ hP z).1]
    exact (logCutoff_derivative_bounds hμ hP z).2
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (s:=Set.univ)
    (fun z _ => (hD z).differentiableAt) (fun z _ => hBounds z) convex_univ (mem_univ x) (mem_univ y)
  simpa only [Real.norm_eq_abs,one_mul] using hh

end
end StrongSilver
