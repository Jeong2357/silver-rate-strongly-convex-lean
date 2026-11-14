-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CanonicalPositionCuts
import StrongSilver.RefinementWeights
import StrongSilver.Constants

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2000000

theorem eligible_positions_range (h : List ℝ) (R : Finset (Fin h.length)) (A B : ℝ) :
    ∀ p ∈ orderedPositions h (eligibleIndices h R A B), A < stepAt h p ∧ stepAt h p < B := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  have he := (Finset.mem_filter.mp (mem_sortedScheduleIndices.mp hq)).2
  simpa only [stepAt_eq q.isLt,Fin.getElem_fin] using he

def eligiblePivotWeights (φ : ℝ → ℝ) (P : ℝ) (h : List ℝ) (R : Finset (Fin h.length)) (A B : ℝ) : List ℝ :=
  (orderedPositions h (eligibleIndices h R A B)).map fun p => (φ (stepAt h p)-P)^nu

def eligibleRefinementWeights (φ : ℝ → ℝ) (P : ℝ) (h : List ℝ) (R : Finset (Fin h.length)) (A B : ℝ) : ℕ → ℝ :=
  refinementWeights ((φ B-P)^nu) (eligiblePivotWeights φ P h R A B)

theorem eligiblePivotWeights_positive {φ : ℝ → ℝ} (hφ : Monotone φ) {P A B : ℝ} (hP : P < φ A)
    (h : List ℝ) (R : Finset (Fin h.length)) : ∀ w ∈ eligiblePivotWeights φ P h R A B, 0 < w := by
  intro w hw
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hw
  have hh := hφ (eligible_positions_range h R A B p hp).1.le
  exact Real.rpow_pos_of_pos (by linarith only [hP,hh]) nu

theorem eligiblePivotWeights_upper {φ : ℝ → ℝ} (hφ : Monotone φ) {P A B : ℝ} (hP : P < φ A)
    (h : List ℝ) (R : Finset (Fin h.length)) : ∀ w ∈ eligiblePivotWeights φ P h R A B, w ≤ (φ B-P)^nu := by
  intro w hw
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hw
  obtain ⟨hA,hB⟩ := eligible_positions_range h R A B p hp
  have hp0 : 0 ≤ φ (stepAt h p)-P := by have hh := hφ hA.le; linarith only [hh,hP]
  exact Real.rpow_le_rpow hp0 (sub_le_sub_right (hφ hB.le) P) nu_positive.le

theorem eligiblePivotWeights_decreasing {φ : ℝ → ℝ} (hφ : Monotone φ) {P A B : ℝ} (hP : P < φ A)
    (h : List ℝ) (R : Finset (Fin h.length)) : (eligiblePivotWeights φ P h R A B).Pairwise (· ≥ ·) := by
  rw [eligiblePivotWeights,List.pairwise_map]
  apply List.Pairwise.imp_of_mem ?_ (orderedPositions_priority h (eligibleIndices h R A B))
  intro p q hp hq hpq
  have hq0 : 0 ≤ φ (stepAt h q)-P := by
    have hh := hφ (eligible_positions_range h R A B q hq).1.le
    linarith only [hh,hP]
  exact Real.rpow_le_rpow hq0 (sub_le_sub_right (hφ hpq.1) P) nu_positive.le

theorem eligibleRefinementWeights_step (φ : ℝ → ℝ) (P : ℝ) (h : List ℝ) (R : Finset (Fin h.length)) (A B : ℝ)
    {i : ℕ} (hi : i < (orderedPositions h (eligibleIndices h R A B)).length) :
    eligibleRefinementWeights φ P h R A B (i+1) =
      (φ (stepAt h (orderedPositions h (eligibleIndices h R A B))[i])-P)^nu := by
  have hvec : i < (eligiblePivotWeights φ P h R A B).length := by simpa [eligiblePivotWeights] using hi
  rw [eligibleRefinementWeights,refinementWeights_step _ _ hvec]
  simp only [eligiblePivotWeights,List.getElem_map]

theorem eligibleRefinementWeights_end (φ : ℝ → ℝ) (P : ℝ) (h : List ℝ) (R : Finset (Fin h.length)) (A B : ℝ) :
    eligibleRefinementWeights φ P h R A B ((orderedPositions h (eligibleIndices h R A B)).length+1) = 0 := by
  have hh := refinementWeights_end ((φ B-P)^nu) (eligiblePivotWeights φ P h R A B)
  simpa only [eligibleRefinementWeights,eligiblePivotWeights,List.length_map] using hh

theorem eligibleRefinementWeights_decreasing {φ : ℝ → ℝ} (hφ : Monotone φ) {P A B : ℝ} (hP : P < φ A) (hAB : A ≤ B)
    (h : List ℝ) (R : Finset (Fin h.length)) (i : ℕ) :
    eligibleRefinementWeights φ P h R A B (i+1) ≤ eligibleRefinementWeights φ P h R A B i := by
  have hb0 : 0 < φ B-P := by have hh := hφ hAB; linarith only [hh,hP]
  exact refinementWeights_decreasing (Real.rpow_pos_of_pos hb0 nu).le _
    (fun w hw => (eligiblePivotWeights_positive hφ hP h R w hw).le)
    (eligiblePivotWeights_upper hφ hP h R) (eligiblePivotWeights_decreasing hφ hP h R) i

end
end StrongSilver
