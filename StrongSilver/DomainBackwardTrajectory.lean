-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BackwardStep
import StrongSilver.Schedules

namespace StrongSilver
open Set
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]

theorem backwardPotential_quadratic_lower {μ h K : ℝ} (F : V → ℝ)
    (hlower : ∀ x, (μ/2)*‖x‖^2 ≤ F x)
    (hupper : ∀ x, F x ≤ (μ/2)*‖x‖^2+K*‖x‖) (x : V) :
    ((1-μ*h)/2)*‖x‖^2-(|h| * K)*‖x‖ ≤ backwardPotential h F x := by
  have hdef : |F x-(μ/2)*‖x‖^2| ≤ K*‖x‖ := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hlower x))]
    linarith only [hupper x]
  have hp := mul_le_mul_of_nonneg_left hdef (abs_nonneg h)
  have hh := le_abs_self (h*(F x-(μ/2)*‖x‖^2))
  rw [abs_mul] at hh
  unfold backwardPotential
  nlinarith only [hp,hh]

theorem exists_backward_step_in_domain {μ h K : ℝ} {S : Set V} (hclosed : IsClosed S) (hconvex : Convex ℝ S)
    (F : V → ℝ) (G : V → V) (hG : ∀ x, HasGradientAt F (G x) x)
    (hlower : ∀ x, (μ/2)*‖x‖^2 ≤ F x) (hupper : ∀ x, F x ≤ (μ/2)*‖x‖^2+K*‖x‖)
    (hpositive : 0 < 1-μ*h)
    (horth : ∀ x ∈ S, ∀ q, OutwardNormal S x q → inner ℝ q (G x) = 0)
    (y : V) (hy : y ∈ S) : ∃ x ∈ S, x-h • G x = y := by
  have hc : CoerciveOn S (fun x => backwardPotential h F x-inner ℝ y x) := by
    apply coercive_of_quadratic_lower (A := (1-μ*h)/2) (B := |h| * K+‖y‖) (C := 0)
      (div_pos hpositive (by norm_num))
    intro x hx
    have hb := backwardPotential_quadratic_lower (h := h) F hlower hupper x
    have hi := real_inner_le_norm y x
    nlinarith only [hb,hi]
  apply exists_predecessor hclosed hconvex (backwardPotential h F) (fun x => x-h • G x)
    (backwardPotential_hasGradientAt h F G hG) y hy hc
  intro x hx q hq
  have he : (x-h • G x)-x = (-h) • G x := by module
  rw [he,real_inner_smul_right,horth x hx q hq,mul_zero]

/-- All intermediate iterates remain in the specified convex domain. -/
theorem exists_backward_trajectory_in_domain {μ K : ℝ} {S : Set V}
    (hclosed : IsClosed S) (hconvex : Convex ℝ S) (F : V → ℝ) (G : V → V)
    (hG : ∀ x, HasGradientAt F (G x) x) (hlower : ∀ x, (μ/2)*‖x‖^2 ≤ F x)
    (hupper : ∀ x, F x ≤ (μ/2)*‖x‖^2+K*‖x‖)
    (horth : ∀ x ∈ S, ∀ q, OutwardNormal S x q → inner ℝ q (G x) = 0)
    (h : List ℝ) (hpositive : ∀ b ∈ h, 0 < 1-μ*b) (y : V) (hy : y ∈ S) :
    ∃ x ∈ S, iterate h G x = y ∧ ∀ i : ℕ, i ≤ h.length → iterate (h.take i) G x ∈ S := by
  induction h generalizing y with
  | nil => exact ⟨y,hy,rfl,fun i hi => by simpa [iterate] using hy⟩
  | cons b h ih =>
    obtain ⟨z,hz,hzy,hstates⟩ := ih (fun c hc => hpositive c (List.mem_cons_of_mem b hc)) y hy
    obtain ⟨x,hx,hxz⟩ := exists_backward_step_in_domain hclosed hconvex F G hG hlower hupper
      (hpositive b List.mem_cons_self) horth z hz
    refine ⟨x,hx,by rw [iterate_cons,hxz,hzy],fun i hi => ?_⟩
    cases i with
    | zero => simpa only [List.take_zero,iterate_nil] using hx
    | succ i =>
      rw [List.take_succ_cons,iterate_cons,hxz]
      exact hstates i (by simp only [List.length_cons] at hi; omega)

end
end StrongSilver
