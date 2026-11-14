-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1600000

def pivotKey (h : List ℝ) (p : Fin h.length) : ℝ ×ₗ ℕ := toLex (-h[p],p.val)

theorem pivotKey_injective (h : List ℝ) : Function.Injective (pivotKey h) := by
  intro p q he
  apply Fin.ext
  exact congrArg (fun x : ℝ ×ₗ ℕ => (ofLex x).2) he

instance pivotPriority_trans (h : List ℝ) : IsTrans (Fin h.length) (fun p q => pivotKey h p ≤ pivotKey h q) :=
  ⟨fun _ _ _ hpq hqr => le_trans hpq hqr⟩

instance pivotPriority_antisymm (h : List ℝ) : Std.Antisymm (fun p q : Fin h.length => pivotKey h p ≤ pivotKey h q) :=
  ⟨fun _ _ hpq hqp => pivotKey_injective h (le_antisymm hpq hqp)⟩

instance pivotPriority_total (h : List ℝ) : Std.Total (fun p q : Fin h.length => pivotKey h p ≤ pivotKey h q) :=
  ⟨fun _ _ => le_total _ _⟩

/-- Decreasing step value; chronological index breaks ties. -/
def sortedScheduleIndices (h : List ℝ) (E : Finset (Fin h.length)) : List (Fin h.length) :=
  E.sort (fun p q => pivotKey h p ≤ pivotKey h q)

theorem sortedScheduleIndices_nodup (h : List ℝ) (E : Finset (Fin h.length)) : (sortedScheduleIndices h E).Nodup := by
  exact E.sort_nodup _

@[simp] theorem mem_sortedScheduleIndices {h : List ℝ} {E : Finset (Fin h.length)} {p : Fin h.length} :
    p ∈ sortedScheduleIndices h E ↔ p ∈ E := by
  exact Finset.mem_sort (r := fun p q => pivotKey h p ≤ pivotKey h q)

theorem pivotKey_priority {h : List ℝ} {p q : Fin h.length} (hh : pivotKey h p ≤ pivotKey h q) :
    h[q] ≤ h[p] ∧ (h[q] = h[p] → p.val ≤ q.val) := by
  rcases Prod.Lex.toLex_le_toLex.mp hh with hlt | ⟨he,hindex⟩
  · constructor
    · change -h[p] < -h[q] at hlt
      linarith only [hlt]
    · intro he
      change -h[p] < -h[q] at hlt
      linarith only [hlt,he]
  · constructor
    · change -h[p] = -h[q] at he
      linarith only [he]
    · exact fun _ => hindex

theorem sortedScheduleIndices_priority (h : List ℝ) (E : Finset (Fin h.length)) :
    (sortedScheduleIndices h E).Pairwise (fun p q => h[q] ≤ h[p] ∧ (h[q] = h[p] → p.val ≤ q.val)) := by
  have hh : (sortedScheduleIndices h E).Pairwise (fun p q => pivotKey h p ≤ pivotKey h q) := by
    exact E.pairwise_sort _
  exact hh.imp (fun hpq => pivotKey_priority hpq)

def orderedPositions (h : List ℝ) (E : Finset (Fin h.length)) : List ℕ := (sortedScheduleIndices h E).map Fin.val

def stepAt (h : List ℝ) (p : ℕ) : ℝ := h[p]?.getD 0

theorem stepAt_eq {h : List ℝ} {p : ℕ} (hp : p < h.length) : stepAt h p = h[p] := by
  simp only [stepAt,List.getElem?_eq_getElem hp,Option.getD_some]

theorem orderedPositions_nodup (h : List ℝ) (E : Finset (Fin h.length)) : (orderedPositions h E).Nodup :=
  (sortedScheduleIndices_nodup h E).map Fin.val_injective

theorem orderedPositions_valid (h : List ℝ) (E : Finset (Fin h.length)) :
    ∀ p ∈ orderedPositions h E, p < h.length := by
  intro p hp
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hp
  exact q.isLt

theorem orderedPositions_priority (h : List ℝ) (E : Finset (Fin h.length)) :
    (orderedPositions h E).Pairwise (fun p q => stepAt h q ≤ stepAt h p ∧ (stepAt h q = stepAt h p → p ≤ q)) := by
  rw [orderedPositions,List.pairwise_map]
  apply (sortedScheduleIndices_priority h E).imp
  intro p q hpq
  simpa only [stepAt_eq p.isLt,stepAt_eq q.isLt,Fin.getElem_fin] using hpq

end
end StrongSilver
