-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LocalPhasePath

namespace StrongSilver
open Set Real Complex
noncomputable section
set_option maxHeartbeats 1000000
variable {A μ : ℝ}

theorem before_selected_take (h : List ℝ) (b : ℝ) (i : Fin (h++[b]).length) :
    (h++[b]).take i.val = h.take i.val :=
  List.take_append_of_le_length (by have := i.isLt; simp only [List.length_append,List.length_singleton] at this; omega)

theorem complex_inner_nonnegative {z w : ℂ} (hzx : 0 ≤ z.re) (hzy : 0 ≤ z.im)
    (hwx : 0 ≤ w.re) (hwy : 0 ≤ w.im) : 0 ≤ inner ℝ z w := by
  rw [complex_inner_coordinates]
  exact add_nonneg (mul_nonneg hzx hwx) (mul_nonneg hzy hwy)

theorem phase_inner_nonnegative {R S : ℂ} {D a E b : ℝ}
    (hR : 0 ≤ R.re ∧ 0 ≤ R.im) (hS : 0 ≤ S.re ∧ 0 ≤ S.im)
    (hD : 0 ≤ D) (ha : 0 ≤ a) (hE : 0 ≤ E) (hb : 0 ≤ b) :
    0 ≤ inner ℝ (phasePoint R D a) (phasePoint S E b) := by
  rw [phase_inner]
  exact add_nonneg (add_nonneg (complex_inner_nonnegative hR.1 hR.2 hS.1 hS.2)
    (mul_nonneg hD hE)) (mul_nonneg ha hb)

theorem localPhase_source_positive (C : PlanarBoundaryCertificate A μ) (S : ScalarContraction)
    (h : List ℝ) (b : ℝ) (R : ℂ) (D a : ℝ) (hD : 0 ≤ D)
    (hh : ∀ c ∈ h, μ*c < 1)
    (hR : ∀ j : ℕ, j ≤ h.length → iterate (h.take j) C.physical R ∈ C.domain)
    (ha : ∀ j : ℕ, j ≤ h.length → 0 < iterate (h.take j) (S.physical μ) a) :
    (localPhasePath C S h b R D a).family.PositiveAt (phasePoint R D a) := by
  have hR0 : R ∈ C.domain := by simpa only [List.take_zero,iterate_nil] using hR 0 (by omega)
  have ha0 : 0 < a := by simpa only [List.take_zero,iterate_nil] using ha 0 (by omega)
  have hRsign : 0 ≤ R.re ∧ 0 ≤ R.im := ⟨hR0.1,hR0.2.1⟩
  constructor
  · intro i
    have hi : i.val ≤ h.length := by have := i.isLt; simp only [List.length_append,List.length_singleton] at this; omega
    have hRi := hR i.val hi
    have hai := ha i.val hi
    have hres := C.projection_residual_nonnegative hRi
    have hc := quadraticMultiplier_positive (h.take i.val) (fun c hc => hh c (List.mem_of_mem_take hc))
    have hp := S.proximal_positive_bounds hai.le
    rw [localPhasePath_proximal,before_selected_take]
    exact phase_inner_nonnegative hRsign hres hD ha0.le (mul_nonneg hc.le hD) (by linarith only [hp.1,hai])
  · intro i
    have hi : i.val ≤ h.length := by have := i.isLt; simp only [List.length_append,List.length_singleton] at this; omega
    have hv := C.body.projection_mem (iterate (h.take i.val) C.physical R)
    have hai := ha i.val hi
    have hg : 0 ≤ S.g (iterate (h.take i.val) (S.physical μ) a) := by
      have hm := S.monotone hai.le
      rwa [S.zero] at hm
    rw [localPhasePath_slope,before_selected_take]
    exact phase_inner_nonnegative hRsign ⟨C.body_re_nonnegative hv,C.body_im_nonnegative hv⟩
      hD ha0.le (le_refl 0) hg

theorem localPhase_endpoint_slope_nonpositive (C : PlanarBoundaryCertificate A μ) (S : ScalarContraction)
    (h : List ℝ) (b : ℝ) (R : ℂ) (D a q : ℝ) (hb : 1 ≤ b) (i : Fin (h++[b]).length) :
    inner ℝ (phasePoint (-(b-1) • (⟨planarEpsilon A,1⟩ : ℂ)) (q*D) 0)
      ((localPhasePath C S h b R D a).family.g i) ≤ 0 := by
  rw [localPhasePath_slope,phase_endpoint_slope_inner]
  have hv := C.body.projection_mem (iterate ((h++[b]).take i.val) C.physical R)
  have hi := complex_inner_nonnegative (z := (⟨planarEpsilon A,1⟩ : ℂ)) C.epsilon_pos.le zero_le_one
    (C.body_re_nonnegative hv) (C.body_im_nonnegative hv)
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hi

theorem localPhase_height_floor (C : PlanarBoundaryCertificate A μ) (S : ScalarContraction)
    (h : List ℝ) (b : ℝ) (R : ℂ) (D a J : ℝ)
    (hJ : ∀ j : ℕ, j ≤ h.length → J ≤ S.potential
      (S.proximalMap (iterate (h.take j) (S.physical μ) a))) (i : Fin (h++[b]).length) :
    J ≤ (localPhasePath C S h b R D a).family.d i := by
  have hi : i.val ≤ h.length := by have := i.isLt; simp only [List.length_append,List.length_singleton] at this; omega
  rw [localPhasePath_height,before_selected_take]
  exact (hJ i.val hi).trans (le_add_of_nonneg_left (C.body.supportValue_nonnegative _))

end
end StrongSilver
