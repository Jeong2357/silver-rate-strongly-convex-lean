-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.MaxPrefixProduct
import StrongSilver.RunSupportedPath
import StrongSilver.PlaneProjectionBounds

namespace StrongSilver.SupportedPath
open Real
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]
set_option maxHeartbeats 1200000

theorem quadraticRun_slope (μ : ℝ) (h : List ℝ) (Y : V) (i : Fin h.length) :
    (quadraticRun μ h Y).family.g i = 0 := rfl

theorem quadraticRun_height (μ : ℝ) (h : List ℝ) (Y : V) (i : Fin h.length) :
    (quadraticRun μ h Y).family.d i = 0 := rfl

theorem quadraticRun_proximal (μ : ℝ) (h : List ℝ) (Y : V) (i : Fin h.length) :
    (quadraticRun μ h Y).family.z i = quadraticMultiplier μ (h.take i.val) • Y := by
  change iterate (h.take i.val) (fun x => μ • x) Y = _
  exact quadratic_iterate μ (h.take i.val) Y

theorem quadraticRun_gate (μ : ℝ) (h : List ℝ) (Y : V) (η : ℝ) :
    (quadraticRun μ h Y).family.Gate Y η := by
  intro i
  rw [quadraticRun_slope,quadraticRun_height,inner_zero_left,add_zero]

theorem quadraticRun_positive {μ : ℝ} (h : List ℝ) (hh : ∀ a ∈ h, μ*a < 1) (Y : V) :
    (quadraticRun μ h Y).family.PositiveAt Y := by
  constructor
  · intro i
    rw [quadraticRun_proximal,real_inner_smul_right,real_inner_self_eq_norm_sq]
    exact mul_nonneg (quadraticMultiplier_positive _ (fun a ha => hh a (List.mem_of_mem_take ha))).le (sq_nonneg _)
  · intro i
    rw [quadraticRun_slope,inner_zero_right]

theorem quadraticRun_proximal_norm {μ : ℝ} (h : List ℝ) (hh : ∀ a ∈ h, μ*a < 1) (Y : V) (i : Fin h.length) :
    ‖(quadraticRun μ h Y).family.z i‖ ≤ maxPrefixProduct μ h*‖Y‖ := by
  rw [quadraticRun_proximal,norm_smul,Real.norm_eq_abs,
    abs_of_pos (quadraticMultiplier_positive _ (fun a ha => hh a (List.mem_of_mem_take ha)))]
  exact mul_le_mul_of_nonneg_right (quadraticPrefix_le_maxPrefixProduct h hh i.val) (norm_nonneg _)

theorem quadraticRun_directional_bound {μ : ℝ} (h : List ℝ) (hh : ∀ a ∈ h, μ*a < 1)
    {Y : V} (hY : Y ≠ 0) (i : Fin h.length) :
    |inner ℝ (unitDirection Y) ((quadraticRun μ h Y).family.z i)| ≤ maxPrefixProduct μ h*‖Y‖ :=
  (unitDirection_projection_le hY _).trans (quadraticRun_proximal_norm h hh Y i)

theorem quadraticRun_terminal_gain {μ A : ℝ} (hμ : 0 ≤ μ) (hcap : μ*A ≤ 1/2) (h : List ℝ)
    (hh : ∀ b ∈ h, 0 < b → b ≤ A) (Y : V) :
    maxPrefixProduct μ h*Real.exp (-2*μ*Scalar.SignedIntervals.positiveMass h)*‖Y‖ ≤
      ‖(quadraticRun μ h Y).x (Fin.last _)‖ := by
  rw [quadraticRun_end,norm_smul,Real.norm_eq_abs]
  have hg := terminal_product_lower hμ hcap h hh
  have hl := mul_le_mul_of_nonneg_right hg (norm_nonneg Y)
  exact hl.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))

end
end StrongSilver.SupportedPath
