-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialMassCharge
import StrongSilver.StrictCommonCurvature

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

theorem inverse_pivot_initial_budget {κ μ b : ℝ} (hκ : 0 < κ) (hμ : 0 ≤ μ) (hμu : μ ≤ 9/(8*κ)) :
    inverseLogKernel (1-μ*b) ≤ 2+(if κ/2 < b then inverseLogKernel (1-μ*b) else 0) := by
  by_cases hb : κ/2 < b
  · simp only [hb,if_true]
    linarith
  · simp only [hb,if_false,add_zero]
    have hμκ : μ*κ ≤ 9/8 := by
      have hh := (le_div_iff₀ (by positivity : 0 < 8*κ)).mp hμu
      nlinarith only [hh]
    have hmb := mul_le_mul_of_nonneg_left (le_of_not_gt hb) hμ
    exact inverseLogKernel_le_two (by nlinarith only [hμκ,hmb])

theorem phases_initial_inverse_budget {κ μ B : ℝ} (hκ : 0 < κ) (hμ : 0 ≤ μ) (hμu : μ ≤ 9/(8*κ)) (hcap : μ*B ≤ 1/2)
    (qs : List CutPhase) (hgap : ∀ q ∈ qs, ∀ b ∈ q.gap, 0 < b → b ≤ B) :
    inverseCharge μ (qs.flatMap CutPhase.word) ≤ 2*μ*phaseGapMass qs+2*(qs.length : ℝ)+
      (qs.map fun q => if κ/2 < q.pivot then inverseLogKernel (1-μ*q.pivot) else 0).sum := by
  induction qs with
  | nil => simp [inverseCharge,phaseGapMass]
  | cons q qs ih =>
    have hq := inverseCharge_small_steps hμ hcap q.gap (hgap q (by simp))
    have hp := inverse_pivot_initial_budget (b := q.pivot) hκ hμ hμu
    have ht := ih (fun z hz => hgap z (List.mem_cons_of_mem q hz))
    simp only [List.flatMap_cons,CutPhase.word,inverseCharge_append,phaseGapMass,List.map_cons,List.sum_cons,
      List.length_cons,Nat.cast_add,Nat.cast_one]
    have he : inverseCharge μ [q.pivot] = inverseLogKernel (1-μ*q.pivot) := by simp [inverseCharge]
    rw [he]
    change inverseCharge μ (qs.flatMap CutPhase.word) ≤
      2*μ*(qs.map fun z => Scalar.SignedIntervals.positiveMass z.gap).sum+2*(qs.length : ℝ)+
      (qs.map fun z => if κ/2 < z.pivot then inverseLogKernel (1-μ*z.pivot) else 0).sum at ht
    nlinarith only [hq,hp,ht]

theorem InitialCutAssembly.reserved_weight_le (s : InitialCutAssembly) (w : CutPhase → ℝ) (hw : ∀ q, 0 ≤ w q) :
    (s.reserved.map w).sum ≤ (s.phases.map w).sum := by
  have hh := s.weight_partition w
  have hp : 0 ≤ (s.trackedPhases.map w).sum := by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hz
    exact hw q
  linarith only [hh,hp]

theorem InitialCutAssembly.reserved_inverse_budget {κ μ B : ℝ}
    (hκ : 0 < κ) (hμ : 0 ≤ μ) (hμu : μ ≤ 9/(8*κ)) (hcap : μ*B ≤ 1/2)
    (s : InitialCutAssembly) (t : List ℝ) (hgap : ∀ q ∈ s.reserved, ∀ b ∈ q.gap, 0 < b → b ≤ B) :
    inverseCharge μ (s.reserved.flatMap CutPhase.word) ≤
      2*μ*phaseGapMass s.reserved+2*(s.reserved.length : ℝ)+
      largeInverseCharge κ (s.phases.flatMap CutPhase.word++t) μ := by
  have hh := phases_initial_inverse_budget hκ hμ hμu hcap s.reserved hgap
  let w : ℝ → ℝ := fun b => if κ/2 < b then inverseLogKernel (1-μ*b) else 0
  have hw : ∀ b, 0 ≤ w b := by intro b; dsimp only [w]; split_ifs <;> first | exact inverseLogKernel_nonneg _ | exact le_rfl
  have hreserve := s.reserved_weight_le (fun q => w q.pivot) (fun q => hw q.pivot)
  have hwhole := (ScheduleCut.mk s.phases t).selected_weight_le w hw
  change (s.phases.map fun q => w q.pivot).sum ≤ largeInverseCharge κ (s.phases.flatMap CutPhase.word++t) μ at hwhole
  exact hh.trans (add_le_add le_rfl (hreserve.trans hwhole))

end
end StrongSilver
