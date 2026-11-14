-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialPhaseBudget
import StrongSilver.WorkingEndpointCap

namespace StrongSilver
open Real
noncomputable section

def initialPlaneConstant : ℝ := 4*Real.exp 4
def initialQuadraticConstant : ℝ := 1+2*(32*Real.exp 4)*initialPlaneConstant
def initialProximalConstant : ℝ := 2*initialPlaneConstant*(1+Real.exp 2)

theorem initialPlaneConstant_positive : 0 < initialPlaneConstant := by unfold initialPlaneConstant; positivity
theorem initialQuadraticConstant_positive : 0 < initialQuadraticConstant := by
  unfold initialQuadraticConstant initialPlaneConstant
  positivity
theorem initialProximalConstant_positive : 0 < initialProximalConstant := by
  unfold initialProximalConstant initialPlaneConstant
  positivity

namespace InitialPhaseBudget
variable {A μ b T κ B e : ℝ} {h : List ℝ} (W : InitialPhaseBudget A μ b T κ B h)
    (L : LocalPhaseCertificate A μ b T e h)
include W L
set_option maxHeartbeats 1600000

theorem plane_start : ‖L.R‖ ≤ initialPlaneConstant*κ := by
  simpa only [List.take_zero,iterate_nil,initialPlaneConstant] using W.planar_all_norm L 0

theorem terminal_inner : L.terminalInner ≤ 2*initialPlaneConstant*κ := by
  have hh := (real_inner_le_norm L.R (⟨planarEpsilon A,1⟩ : ℂ)).trans
    (mul_le_mul (W.plane_start L) L.terminal_planar_norm_le_two (norm_nonneg _)
      (mul_nonneg initialPlaneConstant_positive.le W.kappa_positive.le))
  change L.terminalInner ≤ (initialPlaneConstant*κ)*2 at hh
  nlinarith only [hh]

theorem quadratic_pad : L.D ≤ initialQuadraticConstant*κ := by
  let K := 32*Real.exp 4
  have hK : 0 < K := by dsimp only [K]; positivity
  have hq : 1 ≤ (quadraticMultiplier μ h*(1-μ*b))*K := (div_le_iff₀ hK).mp (W.q_lower L)
  have hDq := mul_le_mul_of_nonneg_right hq (sq_nonneg L.D)
  have hpadK := congrArg (fun t : ℝ => K*t) L.pad
  change K*((quadraticMultiplier μ h*(1-μ*b))*L.D^2) = K*((b-1)*L.terminalInner) at hpadK
  have hDb : L.D^2 ≤ K*b*L.terminalInner := by
    nlinarith only [hDq,hpadK,mul_nonneg hK.le L.terminalInner_nonnegative]
  have hbκ : b ≤ κ := by linarith [W.pivot_upper,W.kappa_positive]
  have hJ := W.terminal_inner L
  have hbJ := mul_le_mul hbκ hJ L.terminalInner_nonnegative W.kappa_positive.le
  have hmul := mul_le_mul_of_nonneg_left hbJ hK.le
  have hDsq : L.D^2 ≤ (2*K*initialPlaneConstant)*κ^2 := by nlinarith only [hDb,hmul]
  have hC : 2*K*initialPlaneConstant ≤ initialQuadraticConstant^2 := by
    have hx : 0 ≤ 2*K*initialPlaneConstant := by have := initialPlaneConstant_positive; positivity
    change 2*K*initialPlaneConstant ≤ (1+2*K*initialPlaneConstant)^2
    nlinarith only [hx]
  have hCκ := mul_le_mul_of_nonneg_right hC (sq_nonneg κ)
  have hfinal : L.D^2 ≤ (initialQuadraticConstant*κ)^2 := by nlinarith only [hDsq,hCκ]
  exact (sq_le_sq₀ L.D_nonnegative (mul_nonneg initialQuadraticConstant_positive.le W.kappa_positive.le)).mp hfinal

theorem proximal_cap : L.endpointProximalCap (initialPlaneConstant*κ) ≤ initialProximalConstant*κ := by
  have hB : 0 ≤ initialPlaneConstant*κ := mul_nonneg initialPlaneConstant_positive.le W.kappa_positive.le
  have hcap := L.endpointProximalCap_le hB
  have hV := mul_le_mul_of_nonneg_right L.terminal_planar_norm_le_two hB
  have hJ := W.terminal_inner L
  have hExp := Real.exp_le_exp.mpr W.negative_charge
  have hprod := mul_le_mul hJ hExp (Real.exp_pos _).le
    (mul_nonneg (by have := initialPlaneConstant_positive; positivity : (0 : ℝ) ≤ 2*initialPlaneConstant) W.kappa_positive.le)
  unfold initialProximalConstant
  nlinarith only [hcap,hV,hprod]

end InitialPhaseBudget
end
end StrongSilver
