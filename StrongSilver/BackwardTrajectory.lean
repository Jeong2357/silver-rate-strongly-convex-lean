-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BackwardStep
import StrongSilver.BackwardNorm
import StrongSilver.PlaneBounds
import StrongSilver.Schedules

namespace StrongSilver
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]

def inverseCharge (μ : ℝ) (h : List ℝ) : ℝ :=
  (h.map (fun b => inverseLogKernel (1-μ*b))).sum

def smallPositiveSum (μ : ℝ) (h : List ℝ) : ℝ :=
  (h.map (smallPositiveStep μ)).sum

theorem inverseCharge_nonneg (μ : ℝ) (h : List ℝ) : 0 ≤ inverseCharge μ h :=
  List.sum_nonneg (fun _ hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; exact inverseLogKernel_nonneg _)

theorem smallPositiveSum_nonneg (μ : ℝ) (h : List ℝ) : 0 ≤ smallPositiveSum μ h :=
  List.sum_nonneg (fun _ hx => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx; exact smallPositiveStep_nonneg _ _)

theorem backward_step_divided_bound {μ h M : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (g : V → V) (x : V) (hg : 0 ≤ inner ℝ (g x) x) (hM : ‖g x‖ ≤ M)
    (hcritical : 1-μ*h ≠ 0) :
    ‖x‖ ≤ Real.exp (inverseLogKernel (1-μ*h)) *
      (‖x-h • stronglyConvexGradient μ g x‖+(1-μ)*M*smallPositiveStep μ h) := by
  have hb := backward_step_norm_bound (h := h) hμ hμ1 g x hg hM
  have hfactor := inverse_factor_le_exp_kernel hcritical
  have hpos : 0 < |1-μ*h| := abs_pos.mpr hcritical
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hrhs : 0 ≤ ‖x-h • stronglyConvexGradient μ g x‖+(1-μ)*M*smallPositiveStep μ h :=
    add_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg (sub_nonneg.mpr hμ1) hM0)
      (smallPositiveStep_nonneg μ h))
  calc
    ‖x‖ ≤ |1-μ*h|⁻¹ * (‖x-h • stronglyConvexGradient μ g x‖+(1-μ)*M*smallPositiveStep μ h) := by
      have hd : ‖x‖ ≤ (‖x-h • stronglyConvexGradient μ g x‖+(1-μ)*M*smallPositiveStep μ h)/|1-μ*h| :=
        (le_div_iff₀ hpos).mpr (by nlinarith only [hb])
      convert hd using 1 <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor hrhs

/-- Exact backward realization through a finite schedule, with the logarithmic
inverse-factor bound of (3.19). This does not assert the cone attachment lemma. -/
theorem exists_backward_trajectory {μ M : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hM : 0 ≤ M)
    (f : V → ℝ) (g : V → V) (hg : ∀ x, HasGradientAt f (g x) x)
    (hf0 : ∀ x, 0 ≤ f x) (hfupper : ∀ x, f x ≤ M*‖x‖)
    (hginner : ∀ x, 0 ≤ inner ℝ (g x) x) (hgbound : ∀ x, ‖g x‖ ≤ M)
    (h : List ℝ) (hcritical : ∀ b ∈ h, 1-μ*b ≠ 0) (y : V) :
    ∃ x : V, iterate h (stronglyConvexGradient μ g) x = y ∧
      ‖x‖ ≤ Real.exp (inverseCharge μ h)*(‖y‖+(1-μ)*M*smallPositiveSum μ h) := by
  have hF := strongify_gradient (μ := μ) hg
  have hlower (x : V) : (μ/2)*‖x‖^2 ≤ stronglyConvexObjective μ f x := by
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr hμ1) (hf0 x))
  have hupper (x : V) : stronglyConvexObjective μ f x ≤ (μ/2)*‖x‖^2+((1-μ)*M)*‖x‖ := by
    have hh := mul_le_mul_of_nonneg_left (hfupper x) (sub_nonneg.mpr hμ1)
    unfold stronglyConvexObjective
    nlinarith only [hh]
  induction h generalizing y with
  | nil => exact ⟨y,rfl,by simp [inverseCharge,smallPositiveSum]⟩
  | cons b h ih =>
    obtain ⟨z,hz,hzb⟩ := ih (fun c hc => hcritical c (List.mem_cons_of_mem b hc)) y
    obtain ⟨x,hx⟩ := exists_backward_step (stronglyConvexObjective μ f) (stronglyConvexGradient μ g)
      hF hlower hupper (hcritical b List.mem_cons_self) z
    have hxb := backward_step_divided_bound hμ hμ1 g x (hginner x) (hgbound x)
      (hcritical b List.mem_cons_self)
    rw [hx] at hxb
    have hetail : 1 ≤ Real.exp (inverseCharge μ h) := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (inverseCharge_nonneg μ h)
    have hc : 0 ≤ (1-μ)*M*smallPositiveStep μ b :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hμ1) hM) (smallPositiveStep_nonneg μ b)
    have hcb := mul_le_mul_of_nonneg_right hetail hc
    refine ⟨x,by rw [iterate_cons,hx,hz],?_⟩
    simp only [inverseCharge,smallPositiveSum,List.map_cons,List.sum_cons,Real.exp_add]
    have he : 0 ≤ Real.exp (inverseLogKernel (1-μ*b)) := (Real.exp_pos _).le
    have hscale := mul_le_mul_of_nonneg_left hzb he
    have hscale2 := mul_le_mul_of_nonneg_left hcb he
    change ‖x‖ ≤ Real.exp (inverseLogKernel (1-μ*b))*Real.exp (inverseCharge μ h)*
      (‖y‖+(1-μ)*M*(smallPositiveStep μ b+smallPositiveSum μ h))
    nlinarith only [hxb,hscale,hscale2]

end
end StrongSilver
