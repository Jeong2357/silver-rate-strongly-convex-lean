-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.OrderedPositions
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Nodup

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1600000

theorem sorted_prefix_membership {α β : Type*} [LinearOrder β] (f : α → β) (hf : Function.Injective f)
    (xs : List α) (hnd : xs.Nodup) (hs : xs.Pairwise (fun a b => f a ≤ f b))
    {i : ℕ} (hi : i < xs.length) (a : α) :
    a ∈ xs.take (i+1) ↔ a ∈ xs ∧ f a ≤ f xs[i] := by
  constructor
  · intro ha
    obtain ⟨j,hj,he⟩ := List.mem_take_iff_getElem.mp ha
    have hjlen : j < xs.length := hj.trans_le (min_le_right _ _)
    have hji : j ≤ i := by have hh := hj.trans_le (min_le_left _ _); omega
    refine ⟨List.mem_of_mem_take ha,?_⟩
    by_cases heq : j = i
    · subst j
      rw [← he]
    · have hjlt : j < i := by omega
      have hh := hs.rel_get_of_lt (a := ⟨j,hjlen⟩) (b := ⟨i,hi⟩) hjlt
      simpa only [List.get_eq_getElem,he] using hh
  · intro ⟨ha,hkey⟩
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp ha
    have hji : j ≤ i := by
      by_contra hn
      have hij : i < j := by omega
      have hh := hs.rel_get_of_lt (a := ⟨i,hi⟩) (b := ⟨j,hj⟩) hij
      change f xs[i] ≤ f xs[j] at hh
      have heq : xs[j] = xs[i] := hf (le_antisymm (by simpa only [he] using hkey) hh)
      have hind : j = i := hnd.getElem_inj_iff.mp heq
      omega
    apply List.mem_take_iff_getElem.mpr
    exact ⟨j,by omega,he⟩

theorem pivotKey_le_iff (h : List ℝ) (p q : Fin h.length) :
    pivotKey h p ≤ pivotKey h q ↔ h[q] < h[p] ∨ h[p] = h[q] ∧ p.val ≤ q.val := by
  simp only [pivotKey,Prod.Lex.toLex_le_toLex,neg_lt_neg_iff,neg_inj]

theorem sortedScheduleIndices_prefix {h : List ℝ} (E : Finset (Fin h.length)) {i : ℕ}
    (hi : i < (sortedScheduleIndices h E).length) (p : Fin h.length) :
    p ∈ (sortedScheduleIndices h E).take (i+1) ↔
      p ∈ E ∧ (h[(sortedScheduleIndices h E)[i]] < h[p] ∨
        h[p] = h[(sortedScheduleIndices h E)[i]] ∧ p.val ≤ ((sortedScheduleIndices h E)[i]).val) := by
  have hs : (sortedScheduleIndices h E).Pairwise (fun p q => pivotKey h p ≤ pivotKey h q) := E.pairwise_sort _
  rw [sorted_prefix_membership (pivotKey h) (pivotKey_injective h) _ (sortedScheduleIndices_nodup h E) hs hi,
    mem_sortedScheduleIndices,pivotKey_le_iff]

end
end StrongSilver
