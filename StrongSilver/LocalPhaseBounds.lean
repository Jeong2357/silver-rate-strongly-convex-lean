-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LocalPhaseGeometry

namespace StrongSilver
open Set Real Complex
noncomputable section
set_option maxHeartbeats 1000000
variable {A μ : ℝ}

theorem localPhase_endpoint_proximal_upper (C : PlanarBoundaryCertificate A μ) (S : ScalarContraction)
    (h : List ℝ) (b : ℝ) (R : ℂ) (D a q Λ J : ℝ) (hb : 1 ≤ b) (hq : 0 ≤ q)
    (hpad : q*D^2 = (b-1)*J)
    (hR : ∀ j : ℕ, j ≤ h.length → iterate (h.take j) C.physical R ∈ C.domain)
    (hΛ : ∀ j : ℕ, j ≤ h.length → quadraticMultiplier μ (h.take j) ≤ Λ)
    (i : Fin (h++[b]).length) :
    inner ℝ (phasePoint (-(b-1) • (⟨planarEpsilon A,1⟩ : ℂ)) (q*D) 0)
      ((localPhasePath C S h b R D a).family.z i) ≤ (b-1)*J*Λ := by
  have hi : i.val ≤ h.length := by have := i.isLt; simp only [List.length_append,List.length_singleton] at this; omega
  have hr := hR i.val hi
  have hres := C.projection_residual_nonnegative hr
  have hv := complex_inner_nonnegative (z := (⟨planarEpsilon A,1⟩ : ℂ)) C.epsilon_pos.le zero_le_one hres.1 hres.2
  have hneg := mul_nonpos_of_nonpos_of_nonneg (show -(b-1) ≤ 0 by linarith) hv
  have hc := mul_le_mul_of_nonneg_left (hΛ i.val hi) (mul_nonneg hq (sq_nonneg D))
  rw [localPhasePath_proximal,before_selected_take,phase_inner,real_inner_smul_left]
  rw [← hpad]
  nlinarith only [hneg,hc]

theorem localPhase_source_slope_cap (C : PlanarBoundaryCertificate A μ) (S : ScalarContraction)
    (h : List ℝ) (b : ℝ) (R : ℂ) (D a G : ℝ) (ha : 0 ≤ a)
    (hG : ∀ j : ℕ, j ≤ h.length → S.g (iterate (h.take j) (S.physical μ) a) ≤ G)
    (i : Fin (h++[b]).length) :
    inner ℝ (phasePoint R D a) ((localPhasePath C S h b R D a).family.g i) ≤
      planarRadius A 0*‖R‖+a*G := by
  have hi : i.val ≤ h.length := by have := i.isLt; simp only [List.length_append,List.length_singleton] at this; omega
  rw [localPhasePath_slope,before_selected_take]
  exact phase_source_slope_upper (le_refl ‖R‖) (C.body_norm_bound (C.body.projection_mem _))
    (norm_nonneg R) ha (hG i.val hi)

/-- The linear source-height estimate behind (3.17). -/
theorem localPhase_source_height (C : PlanarBoundaryCertificate A μ) (S : ScalarContraction)
    (h : List ℝ) (b : ℝ) (R : ℂ) (D a Λ H : ℝ) (ha : 0 ≤ a)
    (hR : ∀ j : ℕ, j ≤ h.length → iterate (h.take j) C.physical R ∈ C.domain)
    (hscalar : ∀ j : ℕ, j ≤ h.length → 0 ≤ iterate (h.take j) (S.physical μ) a ∧
      iterate (h.take j) (S.physical μ) a ≤ H)
    (hΛ : ∀ j : ℕ, j ≤ h.length → quadraticMultiplier μ (h.take j) ≤ Λ)
    (i : Fin (h++[b]).length) :
    inner ℝ (phasePoint R D a) ((localPhasePath C S h b R D a).family.z i) ≤
      ‖R‖*(localPhasePath C S h b R D a).family.d i+Λ*D^2+a*H := by
  have hi : i.val ≤ h.length := by have := i.isLt; simp only [List.length_append,List.length_singleton] at this; omega
  let Ri := iterate (h.take i.val) C.physical R
  let ai := iterate (h.take i.val) (S.physical μ) a
  have hcoords := C.projection_residual_nonnegative (hR i.val hi)
  have hQ := C.supportValue_ge_norm hcoords.1 hcoords.2
  have hscalar0 := hscalar i.val hi
  have hz := (S.proximal_positive_bounds hscalar0.1).2.trans hscalar0.2
  have hd : ‖Ri-C.body.projection Ri‖ ≤ (localPhasePath C S h b R D a).family.d i := by
    rw [localPhasePath_height,before_selected_take]
    exact hQ.trans (le_add_of_nonneg_right (S.potential_nonnegative _))
  have hm := mul_le_mul_of_nonneg_left hd (norm_nonneg R)
  rw [localPhasePath_proximal,before_selected_take]
  have hp := phase_source_proximal_upper (R := R) (w := Ri-C.body.projection Ri) (D := D) (a := a)
    (le_refl ‖R‖) (norm_nonneg R) (hΛ i.val hi) ha hz
  nlinarith only [hm,hp]

end
end StrongSilver
