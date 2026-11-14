-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LocalPhaseConstruction
import StrongSilver.PrefixMultiplierBounds
import StrongSilver.PlanarGapNorm

namespace StrongSilver.LocalPhaseCertificate
open Real Set Complex
noncomputable section
variable {A μ b T e : ℝ} {h : List ℝ} (L : LocalPhaseCertificate A μ b T e h)
include L
set_option maxHeartbeats 1000000

theorem b_positive : 0 < b := by linarith [L.b_large]
theorem T_positive : 0 < T := L.b_positive.trans L.b_lt_T
theorem mu_le_inverse_T : μ ≤ 1/T := ((lt_div_iff₀ L.T_positive).mpr (by nlinarith [L.mu_T_lt_one])).le

theorem e_positive : 0 < e := by
  have hh := L.scalar.positive h.length (le_refl _)
  simpa only [List.take_length,L.scalar.terminal] using hh

theorem scalar_start_positive : 0 < L.scalar.x := by
  simpa only [List.take_zero,iterate_nil] using L.scalar.positive 0 (by omega)

theorem R_mem_domain : L.R ∈ L.planar.domain := by
  simpa only [List.take_zero,iterate_nil] using L.planar_states 0 (by omega)

theorem R_ne_zero : L.R ≠ 0 := by
  intro he
  have hzero : L.planar.physical 0 = 0 := L.planar.physical_gradient_zero
  have hr := L.planar_run
  rw [he,iterate_fixed h L.planar.physical 0 hzero] at hr
  have hh := congrArg Complex.im hr
  norm_num at hh

def scalarSlopeCap (_L : LocalPhaseCertificate A μ b T e h) : ℝ := 2*(scalarRampGrowth T A b h/T+1/b)*e
def sourceSlopeCap : ℝ := planarRadius A 0*‖L.R‖+L.scalar.x*L.scalarSlopeCap
def sourceHeightOffset : ℝ := Real.exp (negativeLogSum h T)*L.D^2+L.scalar.x*(scalarRampGrowth T A b h*e)
def terminalInner : ℝ := inner ℝ L.R (⟨planarEpsilon A,1⟩ : ℂ)
def terminalGate : ℝ := (b-1)*L.terminalInner*Real.exp (negativeLogSum h T)/‖L.path.x (Fin.last _)‖^2

theorem growth_positive : 0 < scalarRampGrowth T A b h := by
  have hmass := Scalar.SignedIntervals.positiveMass_nonneg h
  unfold scalarRampGrowth
  exact mul_pos (Real.exp_pos _) (by have hp := div_nonneg hmass L.b_positive.le; linarith)

theorem scalarSlopeCap_positive : 0 < L.scalarSlopeCap := by
  unfold scalarSlopeCap
  exact mul_pos (mul_pos (by norm_num) (add_pos (div_pos L.growth_positive L.T_positive)
    (one_div_pos.mpr L.b_positive))) L.e_positive

theorem sourceSlopeCap_positive : 0 < L.sourceSlopeCap := by
  unfold sourceSlopeCap
  exact add_pos_of_pos_of_nonneg (mul_pos (L.planar.radius_pos 0) (norm_pos_iff.mpr L.R_ne_zero))
    (mul_nonneg L.scalar_start_positive.le L.scalarSlopeCap_positive.le)

theorem source_slope_bound (i : Fin (h++[b]).length) :
    inner ℝ (L.path.x 0) (L.path.family.g i) ≤ L.sourceSlopeCap := by
  apply localPhase_source_slope_cap L.planar L.scalar.S h b L.R L.D L.scalar.x L.scalarSlopeCap L.scalar_start_positive.le
  intro j hj
  exact (L.scalar.estimates j hj).2.2.2.1

theorem source_height_offset_nonnegative : 0 ≤ L.sourceHeightOffset := by
  unfold sourceHeightOffset
  exact add_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg L.D))
    (mul_nonneg L.scalar_start_positive.le (mul_nonneg L.growth_positive.le L.e_positive.le))

theorem source_height_bound (i : Fin (h++[b]).length) :
    inner ℝ (L.path.x 0) (L.path.family.z i) ≤ ‖L.R‖*L.path.family.d i+L.sourceHeightOffset := by
  unfold sourceHeightOffset
  rw [← add_assoc]
  apply localPhase_source_height L.planar L.scalar.S h b L.R L.D L.scalar.x
    (Real.exp (negativeLogSum h T)) (scalarRampGrowth T A b h*e) L.scalar_start_positive.le L.planar_states
  · intro j hj
    exact ⟨(L.scalar.positive j hj).le,(L.scalar.estimates j hj).2.1⟩
  · intro j hj
    exact prefixMultiplier_le_negative_exp L.mu_positive.le L.T_positive L.mu_le_inverse_T h L.small_steps j

theorem terminalInner_nonnegative : 0 ≤ L.terminalInner :=
  complex_inner_nonnegative L.R_mem_domain.1 L.R_mem_domain.2.1 L.planar.epsilon_pos.le zero_le_one

theorem terminal_gate_bound (i : Fin (h++[b]).length) :
    inner ℝ (L.path.x (Fin.last _)) (L.path.family.z i) ≤ L.terminalGate*‖L.path.x (Fin.last _)‖^2 := by
  have hh := localPhase_endpoint_proximal_upper L.planar L.scalar.S h b L.R L.D L.scalar.x
    (quadraticMultiplier μ h*(1-μ*b)) (Real.exp (negativeLogSum h T)) L.terminalInner
    (by linarith [L.b_large]) L.q_positive.le L.pad L.planar_states
    (fun j hj => prefixMultiplier_le_negative_exp L.mu_positive.le L.T_positive L.mu_le_inverse_T h L.small_steps j) i
  rw [← L.endpoint] at hh
  unfold terminalGate
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr L.endpoint_ne_zero))]
  exact hh

theorem planar_start_norm_bound : ‖L.R‖ ≤ Real.exp (μ*transformedGapMaximum μ h)*
    (L.planar.right+L.planar.J 0+planarRadius A 0*transformedGapMaximum μ h) :=
  L.planar.trajectory_norm_bound L.mu_positive h L.small_steps L.R L.planar_run L.planar_states

end
end StrongSilver.LocalPhaseCertificate
