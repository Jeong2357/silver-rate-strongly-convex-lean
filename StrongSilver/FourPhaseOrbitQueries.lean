-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseTimeChange
import StrongSilver.FourPhaseComparisons
import StrongSilver.Transform

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2200000

theorem minPrefixProduct_le_take {μ : ℝ} (h : List ℝ)
    (hh : ∀ b ∈ h, μ*b < 1) (k : ℕ) : minPrefixProduct μ h ≤ quadraticMultiplier μ (h.take k) := by
  induction h generalizing k with
  | nil => simp [minPrefixProduct,quadraticMultiplier]
  | cons b h ih =>
    cases k with
    | zero => exact min_le_left _ _
    | succ k =>
      have hb : 0 ≤ 1-μ*b := by linarith only [hh b List.mem_cons_self]
      have ht := ih (fun c hc => hh c (List.mem_cons_of_mem b hc)) k
      exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_left ht hb)

namespace FourPhase

def phaseStart (x : Shape) : Fin 4 → Coordinates := ![source x,start1 x,start2 x,start3 x]
def phaseMass (x : Shape) (i : Fin 4) : ℝ := x (i.castLE (by decide : 4 ≤ 8))
def phaseTime (x : Shape) : Fin 3 → ℝ := ![t0 x,t1 x,t2 x]
def phaseExcess (x : Shape) (i : Fin 3) : ℝ := x ⟨i.val+4,by omega⟩

theorem foot_eq_start_sub (x : Shape) (i : Fin 4) : foot x i = phaseStart x i-phaseMass x i • slope x i := by
  fin_cases i <;> rfl

theorem phaseStart_recurrence (x : Shape) (i : Fin 3) :
    phaseStart x i.castSucc = phaseStart x i.succ+phaseTime x i • slope x i.castSucc := by
  fin_cases i <;> rfl

theorem phaseTime_eq (x : Shape) (i : Fin 3) :
    phaseTime x i = phaseMass x i.castSucc+phaseExcess x i := by
  fin_cases i <;> rfl

/-- Every pre-step query of an actual affine phase lies on the backward
ray whose inter-plane comparisons were proved geometrically. -/
theorem orbit_query_ray {x : Shape} {μ T C : ℝ} (hμ : 0 < μ) (hT : 0 < T) (hC : 0 < C)
    (i : Fin 4) (h : List ℝ) (hh : ∀ b ∈ h, μ*b < 1)
    (hmi : phaseMass x i = queryTime μ T C (minPrefixProduct μ h)) (k : ℕ) :
    let c := quadraticMultiplier μ (h.take k)
    let s := phaseMass x i-queryTime μ T C c
    0 ≤ s ∧ phaseState μ T C (phaseStart x i) (slope x i) c-(1/T) • slope x i =
      (C*c) • (foot x i+s • slope x i) := by
  dsimp only
  have hα := minPrefixProduct_positive h hh
  have hc := quadraticMultiplier_positive (h.take k) (fun b hb => hh b (List.mem_of_mem_take hb))
  have ht := queryTime_le hμ hT hC hα (minPrefixProduct_le_take h hh k)
  refine ⟨by rw [hmi]; exact sub_nonneg.mpr ht,?_⟩
  rw [phaseState_query hμ.ne' hT.ne' hC.ne' hc.ne',foot_eq_start_sub]
  module

theorem orbit_phase_next {x : Shape} {μ T C p : ℝ} (hμ : μ ≠ 0) (hT : T ≠ 0)
    (hC : C ≠ 0) (hp : p ≠ 0) (i : Fin 3)
    (hk : phaseExcess x i = (1-μ)*(1-p)/(μ*T*(C*p))-phaseMass x i.castSucc) :
    phaseState μ T C (phaseStart x i.castSucc) (slope x i.castSucc) p =
      (C*p) • phaseStart x i.succ := by
  rw [phaseState_next hμ hT hC hp _ _ hk,← phaseTime_eq,phaseStart_recurrence]
  module

end FourPhase
end
end StrongSilver
