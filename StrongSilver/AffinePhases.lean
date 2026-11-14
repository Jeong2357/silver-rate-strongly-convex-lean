-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Quadratics

namespace StrongSilver
noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem affine_step_shift (μ h : ℝ) (g q x : V) (hq : μ • q = (1-μ) • g) :
    x-h • (μ • x+(1-μ) • g)+q = (1-μ*h) • (x+q) := by
  rw [← hq]
  module

theorem affine_phase_shift (μ : ℝ) (g q : V) (hq : μ • q = (1-μ) • g)
    (h : List ℝ) (x : V) :
    iterate h (fun y => μ • y+(1-μ) • g) x+q = quadraticMultiplier μ h • (x+q) := by
  induction h generalizing x with
  | nil => simp [quadraticMultiplier]
  | cons a h ih =>
    rw [iterate_cons,ih,affine_step_shift μ a g q x hq]
    simp only [quadraticMultiplier,List.map_cons,List.prod_cons]
    module

theorem affine_phase_formula {μ : ℝ} (hμ : μ ≠ 0) (g : V) (h : List ℝ) (x : V) :
    iterate h (fun y => μ • y+(1-μ) • g) x =
      quadraticMultiplier μ h • x-
        (((1-μ)/μ)*(1-quadraticMultiplier μ h)) • g := by
  let q : V := ((1-μ)/μ) • g
  have hq : μ • q = (1-μ) • g := by
    rw [show q = ((1-μ)/μ) • g from rfl,smul_smul]
    congr 1
    field_simp
  have hh := affine_phase_shift μ g q hq h x
  have he : quadraticMultiplier μ h • (x+q)-q =
      quadraticMultiplier μ h • x-(((1-μ)/μ)*(1-quadraticMultiplier μ h)) • g := by
    dsimp [q]
    module
  rw [← he]
  exact eq_sub_of_add_eq hh

end
end StrongSilver
