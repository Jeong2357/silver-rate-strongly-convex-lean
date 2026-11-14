-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LocalPhaseEstimates
import StrongSilver.MoreauAtZero
import StrongSilver.UnitProjectionBound

namespace StrongSilver.LocalPhaseCertificate
open Real Complex
noncomputable section
variable {A μ b T e : ℝ} {h : List ℝ} (L : LocalPhaseCertificate A μ b T e h)
include L
set_option maxHeartbeats 1600000

theorem endpoint_planar_norm_lower :
    (b-1)*‖(⟨planarEpsilon A,1⟩ : ℂ)‖ ≤ ‖L.path.x (Fin.last _)‖ := by
  have hh := phase_norm_sq (-(b-1) • (⟨planarEpsilon A,1⟩ : ℂ))
    ((quadraticMultiplier μ h*(1-μ*b))*L.D) 0
  rw [← L.endpoint,norm_smul,Real.norm_eq_abs,abs_of_nonpos (by linarith [L.b_large] : -(b-1) ≤ 0)] at hh
  have hpos : 0 ≤ (b-1)*‖(⟨planarEpsilon A,1⟩ : ℂ)‖ :=
    mul_nonneg (by linarith [L.b_large]) (norm_nonneg _)
  nlinarith only [hh,hpos,norm_nonneg (L.path.x (Fin.last _)),sq_nonneg ((quadraticMultiplier μ h*(1-μ*b))*L.D)]

theorem endpoint_slope_absolute (i : Fin (h++[b]).length) :
    |inner ℝ (unitDirection (L.path.x (Fin.last _))) (L.path.family.g i)| ≤ planarRadius A 0 := by
  apply unit_projection_of_inner_bound L.endpoint_ne_zero
  have hi := abs_real_inner_le_norm (⟨planarEpsilon A,1⟩ : ℂ)
    (L.planar.body.projection (iterate ((h++[b]).take i.val) L.planar.physical L.R))
  have hbody := L.planar.body_norm_bound (L.planar.body.projection_mem
    (iterate ((h++[b]).take i.val) L.planar.physical L.R))
  have hc := mul_le_mul_of_nonneg_left hbody (norm_nonneg (⟨planarEpsilon A,1⟩ : ℂ))
  have h1 := mul_le_mul_of_nonneg_left (hi.trans hc) (by linarith [L.b_large] : 0 ≤ b-1)
  have h2 := mul_le_mul_of_nonneg_right L.endpoint_planar_norm_lower (L.planar.radius_pos 0).le
  rw [L.endpoint]
  rw [L.endpoint] at h2
  change |inner ℝ (phasePoint _ _ _) ((localPhasePath L.planar L.scalar.S h b L.R L.D L.scalar.x).family.g i)| ≤ _
  rw [localPhasePath_slope,phase_endpoint_slope_inner,abs_mul,abs_of_nonpos (by linarith [L.b_large] : -(b-1) ≤ 0)]
  nlinarith only [h1,h2]

def endpointProximalCap (B : ℝ) : ℝ :=
  ((b-1)*(‖(⟨planarEpsilon A,1⟩ : ℂ)‖*B+L.terminalInner*Real.exp (negativeLogSum h T)))/‖L.path.x (Fin.last _)‖

theorem endpoint_proximal_absolute {B : ℝ}
    (hR : ∀ j : ℕ, j ≤ h.length → ‖iterate (h.take j) L.planar.physical L.R‖ ≤ B)
    (i : Fin (h++[b]).length) :
    |inner ℝ (unitDirection (L.path.x (Fin.last _))) (L.path.family.z i)| ≤ L.endpointProximalCap B := by
  have hi : i.val ≤ h.length := by have := i.isLt; simp only [List.length_append,List.length_singleton] at this; omega
  let Ri := iterate (h.take i.val) L.planar.physical L.R
  let c := quadraticMultiplier μ (h.take i.val)
  let q := quadraticMultiplier μ h*(1-μ*b)
  have hc : 0 < c := quadraticMultiplier_positive _ (fun t ht => L.small_steps t (List.mem_of_mem_take ht))
  have hcU : c ≤ Real.exp (negativeLogSum h T) :=
    prefixMultiplier_le_negative_exp L.mu_positive.le L.T_positive L.mu_le_inverse_T h L.small_steps i.val
  have hprox : ‖Ri-L.planar.body.projection Ri‖ ≤ B := by
    have hh := Moreau.proximal_norm_le L.planar.body.supportEpigraph Ri
    unfold Moreau.proximal at hh
    rw [L.planar.body.exact_proximal_values] at hh
    exact hh.trans (hR i.val hi)
  have hinner := (abs_real_inner_le_norm (⟨planarEpsilon A,1⟩ : ℂ) (Ri-L.planar.body.projection Ri)).trans
    (mul_le_mul_of_nonneg_left hprox (norm_nonneg _))
  have h1 := mul_le_mul_of_nonneg_left hinner (by linarith [L.b_large] : 0 ≤ b-1)
  have h2 := mul_le_mul_of_nonneg_left hcU (mul_nonneg L.q_positive.le (sq_nonneg L.D))
  have habs := abs_add_le (-(b-1)*inner ℝ (⟨planarEpsilon A,1⟩ : ℂ) (Ri-L.planar.body.projection Ri)) (q*L.D^2*c)
  have hqc : 0 ≤ q*L.D^2*c := mul_nonneg (mul_nonneg L.q_positive.le (sq_nonneg _)) hc.le
  rw [abs_mul,abs_of_nonpos (by linarith [L.b_large] : -(b-1) ≤ 0),abs_of_nonneg hqc] at habs
  have hpad : q*L.D^2 = (b-1)*L.terminalInner := L.pad
  change q*L.D^2*c ≤ q*L.D^2*Real.exp (negativeLogSum h T) at h2
  rw [hpad] at h2
  have hbound : |inner ℝ (L.path.x (Fin.last _)) (L.path.family.z i)| ≤
      (b-1)*(‖(⟨planarEpsilon A,1⟩ : ℂ)‖*B+L.terminalInner*Real.exp (negativeLogSum h T)) := by
    rw [L.endpoint]
    change |inner ℝ (phasePoint _ _ _) ((localPhasePath L.planar L.scalar.S h b L.R L.D L.scalar.x).family.z i)| ≤ _
    rw [localPhasePath_proximal,before_selected_take,phase_inner,real_inner_smul_left]
    simp only [zero_mul,add_zero]
    change |-(b-1)*inner ℝ (⟨planarEpsilon A,1⟩ : ℂ) (Ri-L.planar.body.projection Ri)+(q*L.D)*(c*L.D)| ≤ _
    rw [show (q*L.D)*(c*L.D) = q*L.D^2*c by ring]
    rw [hpad] at habs ⊢
    nlinarith only [habs,h1,h2]
  apply unit_projection_of_inner_bound L.endpoint_ne_zero
  unfold endpointProximalCap
  convert hbound using 1
  field_simp [norm_ne_zero_iff.mpr L.endpoint_ne_zero]

end
end StrongSilver.LocalPhaseCertificate
