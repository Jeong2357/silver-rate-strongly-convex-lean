-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.LinkedFollowingIntegral

namespace StrongSilver
open ScheduleTree BinaryForest Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 5600000

/-- Each selected internal parent creates at most two frontier child
gaps. This estimate includes leaf gaps and keeps all occurrences. -/
theorem linkedFrontier_parent_charge (φ : ℝ → ℝ) (s : ℝ) (F : ScheduleNode → ℝ) (hF : ∀ q, 0 ≤ F q)
    (start : ℕ) (κ : ℝ) (parent following : Option ScheduleNode) (t : ScheduleTree) :
    ((linkedFrontier φ s start κ parent following t).map fun q => optionalNodeCharge F q.parent).sum ≤
      2*((labels (t.indexedTree start κ)).map fun q => if s < φ q.pivot then F q else 0).sum+optionalNodeCharge F parent := by
  induction t generalizing start κ parent following with
  | leaf word => simp [linkedFrontier,indexedTree,labels]
  | split l b r il ir =>
    by_cases hb : s < φ b
    · have hl := il start 0 (some (⟨start,.split l b r,κ⟩ : ScheduleNode)) (some (⟨start,.split l b r,κ⟩ : ScheduleNode))
      have hr := ir (start+l.word.length+1) κ (some (⟨start,.split l b r,κ⟩ : ScheduleNode)) following
      rw [linkedFrontier,if_pos hb,List.map_append,List.sum_append]
      simp only [indexedTree,labels,List.map_cons,List.map_append,List.sum_cons,List.sum_append]
      have hroot : s < φ (⟨start,.split l b r,κ⟩ : ScheduleNode).pivot := hb
      rw [if_pos hroot]
      have hparent := optionalNodeCharge_nonnegative F hF parent
      dsimp only [optionalNodeCharge] at hl hr hparent ⊢
      linear_combination hl+hr+hparent
    · have hNonneg : 0 ≤ ((labels ((ScheduleTree.split l b r).indexedTree start κ)).map fun q => if s < φ q.pivot then F q else 0).sum := by
        apply List.sum_nonneg
        intro x hx
        obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx
        split_ifs
        · exact hF q
        · exact le_rfl
      rw [linkedFrontier,if_neg hb]
      simp only [List.map_singleton,List.sum_singleton]
      linarith only [hNonneg]

def linkedParentObservable (φ : ℝ → ℝ) (P κ v : ℝ) (F : ScheduleNode → ℝ) (h : List ℝ) (y : ℝ) : ℝ :=
  ((linkedFrontier φ (P+Real.exp y) 0 κ none none (cartesian h)).map fun q =>
    Real.exp (v*y)*optionalNodeCharge F q.parent).sum

theorem linkedParentObservable_upper (φ : ℝ → ℝ) (P κ v : ℝ) (F : ScheduleNode → ℝ)
    (hF : ∀ q, 0 ≤ F q) (h : List ℝ) (y : ℝ) :
    linkedParentObservable φ P κ v F h y ≤
      2*selectedNodeObservable φ P v F (labels ((cartesian h).indexedTree 0 κ)) y := by
  unfold linkedParentObservable
  rw [List.sum_map_mul_left]
  have hh := mul_le_mul_of_nonneg_left (linkedFrontier_parent_charge φ (P+Real.exp y) F hF 0 κ none none (cartesian h)) (Real.exp_pos (v*y)).le
  simp only [optionalNodeCharge,add_zero] at hh
  have he : selectedNodeObservable φ P v F (labels ((cartesian h).indexedTree 0 κ)) y =
      Real.exp (v*y)*((labels ((cartesian h).indexedTree 0 κ)).map fun q => if P+Real.exp y < φ q.pivot then F q else 0).sum := by
    unfold selectedNodeObservable
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro q _
    split_ifs <;> simp
  rw [he]
  dsimp only [optionalNodeCharge]
  linear_combination hh

end
end StrongSilver
