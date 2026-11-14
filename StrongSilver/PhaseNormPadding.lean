-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PhaseCoordinates

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 1000000

theorem phase_norm_le_of_relative_padding {R : ℂ} {D a P δ : ℝ} (hP : 0 ≤ P) (hδ : 0 ≤ δ)
    (hpad : D^2+a^2 ≤ δ*(‖R‖+P)^2) :
    ‖phasePoint R D a‖ ≤ (1+δ)*(‖R‖+P) := by
  have hQ0 : 0 ≤ ‖R‖+P := add_nonneg (norm_nonneg R) hP
  have hR : ‖R‖^2 ≤ (‖R‖+P)^2 := by nlinarith only [hP,norm_nonneg R,sq_nonneg P]
  have hn := phase_norm_sq R D a
  have hδQ := mul_nonneg hδ (sq_nonneg (‖R‖+P))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith : 0 ≤ 1+δ) hQ0)).mp
  nlinarith only [hn,hR,hpad,hδQ,sq_nonneg (δ*(‖R‖+P))]

theorem phase_norm_exponential_bound {R : ℂ} {D a P m z α δ K H : ℝ}
    (hP : 0 ≤ P) (hm : 0 ≤ m) (hz : 0 ≤ z) (hα : 0 ≤ α) (hδ : 0 ≤ δ) (hδα : δ ≤ α)
    (hK : K ≤ 1+α) (hH : H ≤ α*P)
    (hR : ‖R‖ ≤ Real.exp z*(H+K*m))
    (hpad : D^2+a^2 ≤ δ*(‖R‖+P)^2) :
    ‖phasePoint R D a‖ ≤ Real.exp (2*α+z)*(m+P) := by
  have hnorm := phase_norm_le_of_relative_padding hP hδ hpad
  have hexp : 1 ≤ Real.exp z := Real.one_le_exp_iff.mpr hz
  have hKm := mul_le_mul_of_nonneg_right hK hm
  have hPe := mul_le_mul_of_nonneg_right hexp hP
  have hpoly : H+K*m+P ≤ (1+α)*(m+P) := by nlinarith only [hH,hKm]
  have hmul := mul_le_mul_of_nonneg_left hpoly (Real.exp_pos z).le
  have hQ : ‖R‖+P ≤ (1+α)*Real.exp z*(m+P) := by nlinarith only [hR,hPe,hmul]
  have hnormQ := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 1+δ by linarith)
  have hαexp : 1+α ≤ Real.exp α := by linarith only [Real.add_one_le_exp α]
  have hδexp : 1+δ ≤ Real.exp α := by linarith only [hδα,hαexp]
  have hfactor := mul_le_mul hδexp hαexp (by linarith : 0 ≤ 1+α) (Real.exp_pos α).le
  have hM := mul_le_mul_of_nonneg_right hfactor (mul_nonneg (Real.exp_pos z).le (add_nonneg hm hP))
  have he : Real.exp α*Real.exp α*(Real.exp z*(m+P)) = Real.exp (2*α+z)*(m+P) := by
    rw [show 2*α+z = α+(α+z) by ring,Real.exp_add,Real.exp_add]
    ring
  rw [he] at hM
  nlinarith only [hnorm,hnormQ,hM]

end
end StrongSilver
