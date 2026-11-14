-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutAssemblyWeights
import StrongSilver.ScheduleCutPartition
import StrongSilver.CommonCurvatureBounds

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1600000

theorem ScheduleCut.selected_weight_le (C : ScheduleCut) (w : ℝ → ℝ) (hw : ∀ a, 0 ≤ w a) :
    (C.phases.map fun q => w q.pivot).sum ≤ (C.word.map w).sum := by
  have hh := C.word_sum w
  have hp := list_weight_nonnegative w hw C.unselected
  linarith only [hh,hp]

theorem CutAssembly.reserved_weight_le (s : CutAssembly) (w : CutPhase → ℝ) (hw : ∀ q, 0 ≤ w q) :
    (s.reserved.map w).sum ≤ (s.phases.map w).sum := by
  have hh := s.weight_partition w
  have hp : 0 ≤ (s.tracked.map w).sum := by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hz
    exact hw q
  linarith only [hh,hp]

theorem inverse_pivot_budget {κ μ b : ℝ} (hκ : 0 < κ) (hμ : 0 ≤ μ) (hμu : μ ≤ 2/κ) :
    inverseLogKernel (1-μ*b) ≤ 1+(if κ/4 ≤ b then inverseLogKernel (1-μ*b) else 0) := by
  by_cases hb : κ/4 ≤ b
  · simp only [hb,if_true]
    linarith
  · have hb' : b ≤ κ/4 := (lt_of_not_ge hb).le
    have hmκ := (le_div_iff₀ hκ).mp hμu
    have hmb := mul_le_mul_of_nonneg_left hb' hμ
    have hhalf : μ*b ≤ 1/2 := by nlinarith only [hmκ,hmb]
    have hh := inverseLogKernel_one_sub_small hhalf
    have hmax : max (μ*b) 0 ≤ 1/2 := max_le hhalf (by norm_num)
    simp only [hb,if_false,add_zero]
    linarith only [hh,hmax]

theorem phase_inverse_sum {μ : ℝ} (qs : List CutPhase) :
    inverseCharge μ (qs.flatMap CutPhase.word) =
      (qs.map fun q => inverseCharge μ q.gap).sum+(qs.map fun q => inverseLogKernel (1-μ*q.pivot)).sum := by
  induction qs with
  | nil => simp [inverseCharge]
  | cons q qs ih =>
    simp only [List.flatMap_cons,CutPhase.word,inverseCharge_append,List.map_cons,List.sum_cons]
    rw [ih]
    simp only [inverseCharge,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    ring

theorem phase_inverse_budget {κ μ A : ℝ} (hκ : 0 < κ) (hμ : 0 ≤ μ) (hμu : μ ≤ 2/κ) (hcap : μ*A ≤ 1/2)
    (qs : List CutPhase) (hgap : ∀ q ∈ qs, ∀ a ∈ q.gap, 0 < a → a ≤ A) :
    inverseCharge μ (qs.flatMap CutPhase.word) ≤
      2*μ*(qs.map fun q => Scalar.SignedIntervals.positiveMass q.gap).sum+(qs.length : ℝ)+
      (qs.map fun q => if κ/4 ≤ q.pivot then inverseLogKernel (1-μ*q.pivot) else 0).sum := by
  induction qs with
  | nil => simp [inverseCharge]
  | cons q qs ih =>
    have hq := inverseCharge_small_steps hμ hcap q.gap (hgap q (by simp))
    have hp := inverse_pivot_budget (b := q.pivot) hκ hμ hμu
    have ht := ih (fun z hz => hgap z (List.mem_cons_of_mem q hz))
    simp only [List.flatMap_cons,CutPhase.word,inverseCharge_append,List.map_cons,List.sum_cons,
      List.length_cons,Nat.cast_add,Nat.cast_one]
    have he : inverseCharge μ [q.pivot] = inverseLogKernel (1-μ*q.pivot) := by simp [inverseCharge]
    rw [he]
    nlinarith only [hq,hp,ht]

theorem CutAssembly.reserved_inverse_budget {κ μ A : ℝ}
    (hκ : 0 < κ) (hμ : 0 ≤ μ) (hμu : μ ≤ 2/κ) (hcap : μ*A ≤ 1/2)
    (s : CutAssembly) (t : List ℝ) (hgap : ∀ q ∈ s.reserved, ∀ a ∈ q.gap, 0 < a → a ≤ A) :
    inverseCharge μ (s.reserved.flatMap CutPhase.word) ≤
      2*μ*(s.reserved.map fun q => Scalar.SignedIntervals.positiveMass q.gap).sum+(s.reserved.length : ℝ)+
      inverseChargeAbove (κ/4) (s.phases.flatMap CutPhase.word++t) μ := by
  have hh := phase_inverse_budget hκ hμ hμu hcap s.reserved hgap
  let w : ℝ → ℝ := fun b => if κ/4 ≤ b then inverseLogKernel (1-μ*b) else 0
  have hw : ∀ b, 0 ≤ w b := by intro b; dsimp only [w]; split_ifs <;> first | exact inverseLogKernel_nonneg _ | exact le_rfl
  have hreserve := s.reserved_weight_le (fun q => w q.pivot) (fun q => hw q.pivot)
  have hwhole := (ScheduleCut.mk s.phases t).selected_weight_le w hw
  change (s.phases.map fun q => w q.pivot).sum ≤ inverseChargeAbove (κ/4) (s.phases.flatMap CutPhase.word++t) μ at hwhole
  exact hh.trans (add_le_add le_rfl (hreserve.trans hwhole))

end
end StrongSilver
