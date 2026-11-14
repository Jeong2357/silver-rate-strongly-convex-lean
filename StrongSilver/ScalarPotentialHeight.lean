-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScalarRamp

namespace StrongSilver
open Set Real
noncomputable section
set_option maxHeartbeats 1000000

namespace ScalarContraction
variable (S : ScalarContraction)

theorem inverse_zero : S.proximalIso.symm 0 = 0 := by
  have hh := S.proximalIso.symm_apply_apply 0
  change S.proximalIso.symm (S.proximalMap 0) = 0 at hh
  rwa [S.proximal_zero] at hh

theorem inverseSlope_lower {m : ℝ} (hm : 0 ≤ m)
    (hg : ∀ x : ℝ, 0 ≤ x → m*x ≤ S.g x) {z : ℝ} (hz : 0 ≤ z) : m*z ≤ S.inverseSlope z := by
  have hx : 0 ≤ S.proximalIso.symm z := by
    have hh := S.proximalIso.symm.monotone hz
    rwa [S.inverse_zero] at hh
  have hpx := S.proximal_positive_bounds hx
  have he : S.proximalMap (S.proximalIso.symm z) = z := S.proximalIso.apply_symm_apply z
  rw [he] at hpx
  exact (mul_le_mul_of_nonneg_left hpx.2 hm).trans (hg _ hx)

theorem potential_quadratic_lower {m : ℝ} (hm : 0 ≤ m)
    (hg : ∀ x : ℝ, 0 ≤ x → m*x ≤ S.g x) {z : ℝ} (hz : 0 ≤ z) :
    (m/2)*z^2 ≤ S.potential z := by
  let F : ℝ → ℝ := fun t => S.potential t-(m/2)*t^2
  have hd (t : ℝ) : HasDerivAt F (S.inverseSlope t-m*t) t := by
    have hh := (S.potential_hasDerivAt t).sub (((hasDerivAt_id t).pow 2).const_mul (m/2))
    simp only [id_eq,Pi.sub_apply,Pi.pow_apply] at hh
    convert! hh using 1 <;> ring
  have hmono : MonotoneOn F (Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
      (fun t ht => (hd t).continuousAt.continuousWithinAt)
      (fun t ht => (hd t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hd t).deriv]
    exact sub_nonneg.mpr (S.inverseSlope_lower hm hg (interior_subset ht))
  have hh := hmono (show (0 : ℝ) ∈ Ici (0 : ℝ) from (le_refl (0 : ℝ))) hz hz
  dsimp [F] at hh
  rw [S.potential_zero] at hh
  nlinarith only [hh]

end ScalarContraction

namespace ScalarRamp
variable (R : ScalarRamp)

theorem contraction_linear_lower {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (hμb : μ ≤ R.base)
    {x : ℝ} (hx : 0 ≤ x) : (R.base-μ)*x ≤ (R.contraction hμ0 hμ1 hμb).g x := by
  change (R.base-μ)*x ≤ (R.physical x-μ*x)/(1-μ)
  apply (le_div_iff₀ (by linarith : 0 < 1-μ)).mpr
  have hh := (R.physical_positive_bounds hx).1
  have hm := mul_nonneg hμ0 (mul_nonneg (sub_nonneg.mpr hμb) hx)
  nlinarith only [hh,hm]

theorem proximal_potential_height {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (hμb : μ ≤ R.base)
    {x : ℝ} (hx : 0 ≤ x) :
    ((R.base-μ)/8)*x^2 ≤ (R.contraction hμ0 hμ1 hμb).potential
      ((R.contraction hμ0 hμ1 hμb).proximalMap x) := by
  let S := R.contraction hμ0 hμ1 hμb
  have hz := S.proximal_positive_bounds hx
  have hp := S.potential_quadratic_lower (sub_nonneg.mpr hμb)
    (fun t ht => R.contraction_linear_lower hμ0 hμ1 hμb ht) (by linarith : 0 ≤ S.proximalMap x)
  have hs : x^2/4 ≤ (S.proximalMap x)^2 := by nlinarith only [hz.1,hx]
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ (R.base-μ)/2 by linarith)
  nlinarith only [hp,hm]

end ScalarRamp
end
end StrongSilver
