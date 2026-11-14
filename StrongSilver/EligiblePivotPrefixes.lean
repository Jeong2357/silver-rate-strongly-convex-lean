-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SortedPivotPrefixes
import StrongSilver.PositionCuts

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

def eligibleIndices (h : List ℝ) (R : Finset (Fin h.length)) (A B : ℝ) : Finset (Fin h.length) :=
  R.filter fun p => A < h[p] ∧ h[p] < B

theorem fin_val_mem_map {n : ℕ} (xs : List (Fin n)) (p : Fin n) : p.val ∈ xs.map Fin.val ↔ p ∈ xs := by
  constructor
  · intro hp
    obtain ⟨q,hq,he⟩ := List.mem_map.mp hp
    have hqp : q = p := Fin.ext he
    rwa [hqp] at hq
  · intro hp
    exact List.mem_map.mpr ⟨p,hp,rfl⟩

/-- Among eligible positions, a sorted initial segment is exactly a full
value cut followed by a chronological initial segment of its boundary tie. -/
theorem eligible_prefix_selected (h : List ℝ) (R : Finset (Fin h.length)) (A B : ℝ)
    {i : ℕ} (hi : i < (sortedScheduleIndices h (eligibleIndices h R A B)).length)
    (p : Fin h.length) (hp : p ∈ R) :
    p ∈ (sortedScheduleIndices h (eligibleIndices h R A B)).take (i+1) ∨ B ≤ h[p] ↔
      h[(sortedScheduleIndices h (eligibleIndices h R A B))[i]] < h[p] ∨
        h[p] = h[(sortedScheduleIndices h (eligibleIndices h R A B))[i]] ∧
          p.val ≤ ((sortedScheduleIndices h (eligibleIndices h R A B))[i]).val := by
  let E := eligibleIndices h R A B
  let xs := sortedScheduleIndices h E
  let q : Fin h.length := xs[i]
  have hq : q ∈ E := mem_sortedScheduleIndices.mp (List.getElem_mem hi)
  obtain ⟨hqR,hqA,hqB⟩ := Finset.mem_filter.mp hq
  rw [sortedScheduleIndices_prefix E hi p]
  change (p ∈ E ∧ (h[q] < h[p] ∨ h[p] = h[q] ∧ p.val ≤ q.val)) ∨ B ≤ h[p] ↔
    h[q] < h[p] ∨ h[p] = h[q] ∧ p.val ≤ q.val
  constructor
  · intro hh
    rcases hh with ⟨_,hh⟩ | hb
    · exact hh
    · exact Or.inl (hqB.trans_le hb)
  · intro hh
    rcases hh with hl | ⟨he,hi⟩
    · by_cases hb : B ≤ h[p]
      · exact Or.inr hb
      · exact Or.inl ⟨Finset.mem_filter.mpr ⟨hp,hqA.trans hl,lt_of_not_ge hb⟩,Or.inl hl⟩
    · refine Or.inl ⟨Finset.mem_filter.mpr ⟨hp,?_,?_⟩,Or.inr ⟨he,hi⟩⟩
      · simpa only [he] using hqA
      · simpa only [he] using hqB

theorem selectedWith_eligible_prefix (h : List ℝ) (R : Finset (Fin h.length)) (A B : ℝ)
    {i : ℕ} (hi : i < (sortedScheduleIndices h (eligibleIndices h R A B)).length)
    (p : Fin h.length) (hp : p ∈ R) :
    selectedWith (fun _ b => decide (B ≤ b)) ((orderedPositions h (eligibleIndices h R A B)).take (i+1)) p.val h[p] = true ↔
      h[(sortedScheduleIndices h (eligibleIndices h R A B))[i]] < h[p] ∨
        h[p] = h[(sortedScheduleIndices h (eligibleIndices h R A B))[i]] ∧
          p.val ≤ ((sortedScheduleIndices h (eligibleIndices h R A B))[i]).val := by
  simpa only [selectedWith,orderedPositions,← List.map_take,Bool.or_eq_true,decide_eq_true_eq,fin_val_mem_map]
    using eligible_prefix_selected h R A B hi p hp

end
end StrongSilver
