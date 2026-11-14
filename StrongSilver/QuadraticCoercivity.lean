-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Predecessor

namespace StrongSilver
open Set
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]

theorem coercive_of_quadratic_lower {S : Set V} {f : V → ℝ} {A B C : ℝ} (hA : 0 < A)
    (hlower : ∀ x ∈ S, A*‖x‖^2-B*‖x‖-C ≤ f x) : CoerciveOn S f := by
  intro M
  refine ⟨max 1 ((|B|+|C|+|M|+1)/A),fun x hx hnorm => ?_⟩
  have hr1 : 1 ≤ ‖x‖ := (le_max_left _ _).trans hnorm
  have hrA : |B|+|C|+|M|+1 ≤ ‖x‖*A :=
    (div_le_iff₀ hA).mp ((le_max_right _ _).trans hnorm)
  have hp := mul_le_mul_of_nonneg_right hrA (norm_nonneg x)
  have hb := mul_le_mul_of_nonneg_right (le_abs_self B) (norm_nonneg x)
  have hc := mul_le_mul_of_nonneg_left hr1 (abs_nonneg C)
  have hm := mul_le_mul_of_nonneg_left hr1 (abs_nonneg M)
  have hC := le_abs_self C
  have hM := le_abs_self M
  nlinarith only [hlower x hx,hp,hb,hc,hm,hC,hM,hr1]

theorem outward_normal_univ_zero (x q : V) (hq : OutwardNormal univ x q) : q = 0 := by
  have h := hq (x+q) (mem_univ _)
  rw [add_sub_cancel_left,real_inner_self_eq_norm_sq] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg q])

theorem exists_gradient_preimage_of_quadratic_lower (Φ : V → ℝ) (G : V → V)
    (hG : ∀ x, HasGradientAt Φ (G x) x) {A B : ℝ} (hA : 0 < A)
    (hlower : ∀ x, A*‖x‖^2-B*‖x‖ ≤ Φ x) (y : V) : ∃ x, G x = y := by
  have hcoercive : CoerciveOn univ (fun x => Φ x-inner ℝ y x) := by
    apply coercive_of_quadratic_lower (A := A) (B := B+‖y‖) (C := 0) hA
    intro x hx
    have hh := real_inner_le_norm y x
    nlinarith only [hlower x,hh]
  obtain ⟨x,hx,hxy⟩ := exists_predecessor isClosed_univ convex_univ Φ G hG y (mem_univ _) hcoercive
    (fun x hx q hq => by rw [outward_normal_univ_zero x q hq,inner_zero_left])
  exact ⟨x,hxy⟩

end
end StrongSilver
