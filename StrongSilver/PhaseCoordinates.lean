-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarConstruction
import StrongSilver.ScalarConstruction
import Mathlib.Analysis.InnerProductSpace.ProdL2

namespace StrongSilver
open Real Complex
noncomputable section
set_option maxHeartbeats 1000000

abbrev PhaseSpace := WithLp 2 (ℂ × WithLp 2 (ℝ × ℝ))
def phasePoint (R : ℂ) (D a : ℝ) : PhaseSpace := WithLp.toLp 2 (R,WithLp.toLp 2 (D,a))
def phaseSlope (v : ℂ) (g : ℝ) : PhaseSpace := phasePoint v 0 g

theorem phase_inner (R S : ℂ) (D a E b : ℝ) :
    inner ℝ (phasePoint R D a) (phasePoint S E b) = inner ℝ R S+D*E+a*b := by
  change inner ℝ R S+(inner ℝ D E+inner ℝ a b) = _
  rw [Real.inner_apply,Real.inner_apply]
  ring

theorem phase_norm_sq (R : ℂ) (D a : ℝ) : ‖phasePoint R D a‖^2 = ‖R‖^2+D^2+a^2 := by
  rw [← real_inner_self_eq_norm_sq,phase_inner,real_inner_self_eq_norm_sq]
  ring

theorem phase_start_endpoint_inner (R V : ℂ) (D a q b : ℝ) :
    inner ℝ (phasePoint R D a) (phasePoint (-(b-1) • V) (q*D) 0) =
      -(b-1)*inner ℝ R V+q*D^2 := by
  rw [phase_inner,real_inner_smul_right]
  ring

theorem exists_orthogonal_phase_pad {J q b : ℝ} (hJ : 0 ≤ J) (hq : 0 < q) (hb : 1 ≤ b) :
    ∃ D : ℝ, 0 ≤ D ∧ q*D^2 = (b-1)*J := by
  refine ⟨Real.sqrt ((b-1)*J/q),Real.sqrt_nonneg _,?_⟩
  rw [Real.sq_sqrt (div_nonneg (mul_nonneg (sub_nonneg.mpr hb) hJ) hq.le)]
  exact mul_div_cancel₀ _ hq.ne'

theorem phase_endpoint_norm_lower {ε q D b : ℝ} (hb : 1 ≤ b) :
    b-1 ≤ ‖phasePoint (-(b-1) • (⟨ε,1⟩ : ℂ)) (q*D) 0‖ := by
  have hn := phase_norm_sq (-(b-1) • (⟨ε,1⟩ : ℂ)) (q*D) 0
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonpos (by linarith : -(b-1) ≤ 0)] at hn
  have hV : 1 ≤ ‖(⟨ε,1⟩ : ℂ)‖ := Complex.im_le_norm (⟨ε,1⟩ : ℂ)
  have hmul := mul_le_mul_of_nonneg_left hV (sub_nonneg.mpr hb)
  have hm0 : 0 ≤ (b-1)*‖(⟨ε,1⟩ : ℂ)‖ := mul_nonneg (sub_nonneg.mpr hb) (norm_nonneg _)
  nlinarith only [hn,hmul,hm0,sq_nonneg (q*D),norm_nonneg (phasePoint (-(b-1) • (⟨ε,1⟩ : ℂ)) (q*D) 0),hb]

theorem phase_endpoint_slope_inner (V v : ℂ) (q D b g : ℝ) :
    inner ℝ (phasePoint (-(b-1) • V) (q*D) 0) (phaseSlope v g) =
      -(b-1)*inner ℝ V v := by
  rw [phaseSlope,phase_inner,real_inner_smul_left]
  ring

theorem phase_source_slope_upper {R v : ℂ} {D a g M K G : ℝ}
    (hR : ‖R‖ ≤ M) (hv : ‖v‖ ≤ K) (hM : 0 ≤ M) (ha : 0 ≤ a) (hg : g ≤ G) :
    inner ℝ (phasePoint R D a) (phaseSlope v g) ≤ K*M+a*G := by
  rw [phaseSlope,phase_inner,mul_zero,add_zero]
  have hi := (real_inner_le_norm R v).trans (mul_le_mul hR hv (norm_nonneg v) hM)
  have hm := mul_le_mul_of_nonneg_left hg ha
  nlinarith only [hi,hm]

theorem phase_source_proximal_upper {R w : ℂ} {D a c z M Λ H : ℝ}
    (hR : ‖R‖ ≤ M) (hM : 0 ≤ M) (hc : c ≤ Λ) (ha : 0 ≤ a) (hz : z ≤ H) :
    inner ℝ (phasePoint R D a) (phasePoint w (c*D) z) ≤ M*‖w‖+Λ*D^2+a*H := by
  rw [phase_inner]
  have hi := (real_inner_le_norm R w).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg w))
  have hpad := mul_le_mul_of_nonneg_right hc (sq_nonneg D)
  have hm := mul_le_mul_of_nonneg_left hz ha
  nlinarith only [hi,hpad,hm]

end
end StrongSilver
