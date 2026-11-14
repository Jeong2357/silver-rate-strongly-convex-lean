-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.AffinePhases
import Mathlib.Tactic

namespace StrongSilver.FourPhase
noncomputable section
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
set_option maxHeartbeats 2200000

/-- Affine orbit in the original product time, with normalized slope g/T. -/
def phaseState (μ T C : ℝ) (ξ g : V) (c : ℝ) : V :=
  (C*c) • ξ-((1-μ)*(1-c)/(μ*T)) • g

def queryTime (μ T C c : ℝ) : ℝ := (c⁻¹-(1-μ))/(μ*T*C)

theorem phaseState_start (μ T C : ℝ) (ξ g : V) : phaseState μ T C ξ g 1 = C • ξ := by
  simp [phaseState]

theorem phaseState_from_iterate {μ T : ℝ} (hμ : μ ≠ 0) (hT : T ≠ 0)
    (C : ℝ) (ξ g : V) (h : List ℝ) :
    iterate h (fun y => μ • y+(1-μ) • ((1/T) • g)) (C • ξ) =
      phaseState μ T C ξ g (quadraticMultiplier μ h) := by
  rw [affine_phase_formula hμ]
  unfold phaseState
  simp only [smul_smul]
  have he : ((1-μ)/μ*(1-quadraticMultiplier μ h))*(1/T) =
      (1-μ)*(1-quadraticMultiplier μ h)/(μ*T) := by field_simp <;> ring
  rw [he,mul_comm (quadraticMultiplier μ h) C]

theorem phaseState_query {μ T C c : ℝ} (hμ : μ ≠ 0) (hT : T ≠ 0)
    (hC : C ≠ 0) (hc : c ≠ 0) (ξ g : V) :
    phaseState μ T C ξ g c-(1/T) • g = (C*c) • (ξ-queryTime μ T C c • g) := by
  have he : (1-μ)*(1-c)/(μ*T)+1/T = C*c*queryTime μ T C c := by
    unfold queryTime
    field_simp
    <;> ring
  unfold phaseState
  rw [smul_sub,smul_smul,← he]
  module

theorem queryTime_le {μ T C c α : ℝ} (hμ : 0 < μ) (hT : 0 < T)
    (hC : 0 < C) (hα : 0 < α) (hc : α ≤ c) :
    queryTime μ T C c ≤ queryTime μ T C α := by
  unfold queryTime
  apply div_le_div_of_nonneg_right _ (mul_nonneg (mul_nonneg hμ.le hT.le) hC.le)
  exact sub_le_sub_right (inv_anti₀ hα hc) _

theorem phaseState_next {μ T C p m k : ℝ} (hμ : μ ≠ 0) (hT : T ≠ 0)
    (hC : C ≠ 0) (hp : p ≠ 0) (ξ g : V)
    (hk : k = (1-μ)*(1-p)/(μ*T*(C*p))-m) :
    phaseState μ T C ξ g p = (C*p) • (ξ-(m+k) • g) := by
  have he : C*p*(m+k) = (1-μ)*(1-p)/(μ*T) := by
    rw [hk]
    field_simp
    <;> ring
  unfold phaseState
  rw [smul_sub,smul_smul,he]

/-- Unlike the first three phase transitions, the last product can have
any sign. The endpoint formula never divides by it. -/
theorem phaseState_last {μ T C α m k ζ p : ℝ} (hμ : μ ≠ 0) (hT : T ≠ 0)
    (hC : C ≠ 0) (hα : α ≠ 0) (Y : V)
    (hm : m = queryTime μ T C α)
    (hk : k = (1-p/α)/(μ*T)-1/T) :
    phaseState μ T C (-(m+ζ) • Y) (-Y) p = (k-C*p*ζ) • Y := by
  have he : -C*p*(m+ζ)+(1-μ)*(1-p)/(μ*T) = k-C*p*ζ := by
    rw [hm,hk]
    unfold queryTime
    field_simp
    <;> ring
  unfold phaseState
  simp only [smul_smul,smul_neg,sub_neg_eq_add]
  rw [← add_smul]
  congr 1
  linear_combination he

end
end StrongSilver.FourPhase
