-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.TerminalQuadratic
import StrongSilver.SupportedPathError

namespace StrongSilver
open Real
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]
set_option maxHeartbeats 1600000

theorem quadraticMultiplier_ne_zero {μ : ℝ} (h : List ℝ) (hh : ∀ b ∈ h, 1-μ*b ≠ 0) :
    quadraticMultiplier μ h ≠ 0 := by
  induction h with
  | nil => exact one_ne_zero
  | cons b h ih =>
    change (1-μ*b)*quadraticMultiplier μ h ≠ 0
    exact mul_ne_zero (hh b List.mem_cons_self) (ih (fun a ha => hh a (List.mem_cons_of_mem b ha)))

def normalizedQuadraticPath (μ : ℝ) (h : List ℝ) (Y : V) : SupportedPath V μ h.length :=
  SupportedPath.quadraticRun μ h ((quadraticMultiplier μ h)⁻¹ • Y)

theorem normalizedQuadraticPath_end {μ : ℝ} (h : List ℝ) (hh : ∀ b ∈ h, 1-μ*b ≠ 0) (Y : V) :
    (normalizedQuadraticPath μ h Y).x (Fin.last _) = Y := by
  rw [normalizedQuadraticPath,SupportedPath.quadraticRun_end,smul_smul,
    mul_inv_cancel₀ (quadraticMultiplier_ne_zero h hh),one_smul]

theorem normalizedQuadraticPath_steps (μ : ℝ) (h : List ℝ) (Y : V) :
    List.ofFn (normalizedQuadraticPath μ h Y).steps = h := List.ofFn_get _

theorem normalizedQuadraticPath_ne_zero {μ : ℝ} (h : List ℝ) (hh : ∀ b ∈ h, 1-μ*b ≠ 0) {Y : V} (hY : Y ≠ 0) :
    (normalizedQuadraticPath μ h Y).x 0 ≠ 0 :=
  (normalizedQuadraticPath μ h Y).source_ne_zero (by rw [normalizedQuadraticPath_end h hh]; exact hY)

theorem normalizedQuadraticPath_prefix_norm {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (h : List ℝ) (hh : ∀ b ∈ h, 1-μ*b ≠ 0) (Y : V) (i : ℕ) :
    ‖iterate (h.take i) (fun x : V => μ • x) ((quadraticMultiplier μ h)⁻¹ • Y)‖ ≤
      Real.exp (inverseCharge μ h)*‖Y‖ := by
  let X := (quadraticMultiplier μ h)⁻¹ • Y
  have hrun : iterate h (fun x : V => μ • x) X = Y := by
    rw [quadratic_iterate,smul_smul,mul_inv_cancel₀ (quadraticMultiplier_ne_zero h hh),one_smul]
  have hG : stronglyConvexGradient μ (fun _ : V => 0) = (fun x : V => μ • x) := by
    funext x
    simp only [stronglyConvexGradient,smul_zero,add_zero]
  have hrun' : iterate h (stronglyConvexGradient μ (fun _ : V => 0)) X = Y := by rwa [hG]
  have hn := backward_norm_all_prefixes hμ hμ1 (M := 0) le_rfl (fun _ : V => 0)
    (fun x => by simp) (fun x => by simp) h hh X Y hrun' i
  simpa only [hG,mul_zero,zero_mul,add_zero] using hn

theorem normalizedQuadraticPath_source_norm {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (h : List ℝ) (hh : ∀ b ∈ h, 1-μ*b ≠ 0) (Y : V) :
    ‖(normalizedQuadraticPath μ h Y).x 0‖ ≤ Real.exp (inverseCharge μ h)*‖Y‖ := by
  rw [normalizedQuadraticPath,SupportedPath.quadraticRun_start]
  simpa only [List.take_zero,iterate_nil] using normalizedQuadraticPath_prefix_norm hμ hμ1 h hh Y 0

theorem normalizedQuadraticPath_directional {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (h : List ℝ) (hh : ∀ b ∈ h, 1-μ*b ≠ 0) {Y : V} (hY : Y ≠ 0) (i : Fin h.length) :
    |inner ℝ (unitDirection ((normalizedQuadraticPath μ h Y).x 0)) ((normalizedQuadraticPath μ h Y).family.z i)| ≤
      Real.exp (inverseCharge μ h)*‖Y‖ := by
  have hbound := unitDirection_projection_le (normalizedQuadraticPath_ne_zero h hh hY)
    ((normalizedQuadraticPath μ h Y).family.z i)
  apply hbound.trans
  change ‖(SupportedPath.quadraticRun μ h ((quadraticMultiplier μ h)⁻¹ • Y)).family.z i‖ ≤ _
  rw [SupportedPath.quadraticRun_proximal,← quadratic_iterate]
  exact normalizedQuadraticPath_prefix_norm hμ hμ1 h hh Y i.val

theorem normalizedQuadraticPath_slope (μ : ℝ) (h : List ℝ) (Y : V) (i : Fin h.length) :
    (normalizedQuadraticPath μ h Y).family.g i = 0 := rfl

theorem normalizedQuadraticPath_gate (μ : ℝ) (h : List ℝ) (Y : V) (η : ℝ) :
    (normalizedQuadraticPath μ h Y).family.Gate ((normalizedQuadraticPath μ h Y).x 0) η :=
  SupportedPath.quadraticRun_gate μ h ((quadraticMultiplier μ h)⁻¹ • Y) η

end
end StrongSilver
