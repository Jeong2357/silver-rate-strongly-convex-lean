-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutSelectorInsertion
import Mathlib.Data.List.Nodup

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

def selectedWith (base : ℕ → ℝ → Bool) (ps : List ℕ) (j : ℕ) (a : ℝ) : Bool :=
  decide (j ∈ ps) || base j a

def positionCut (base : ℕ → ℝ → Bool) (h : List ℝ) (ps : List ℕ) : ScheduleCut :=
  cutSchedule (selectedWith base ps) h

@[simp] theorem positionCut_word (base : ℕ → ℝ → Bool) (h : List ℝ) (ps : List ℕ) :
    (positionCut base h ps).word = h := cutSchedule_word _ _

theorem selectedWith_nil (base : ℕ → ℝ → Bool) : selectedWith base [] = base := by
  funext j a
  simp [selectedWith]

theorem selectedWith_append_one (base : ℕ → ℝ → Bool) (ps : List ℕ) (p : ℕ) :
    selectedWith base (ps++[p]) = selectIndex (selectedWith base ps) p := by
  funext j a
  by_cases hj : j = p
  · subst j
    simp [selectedWith,selectIndex]
  · simp [selectedWith,selectIndex,hj]

theorem exists_position_insertion (base : ℕ → ℝ → Bool) (h : List ℝ) (ps : List ℕ) {p : ℕ}
    (hp : p < h.length) (hnot : p ∉ ps) (hfalse : base p h[p] = false) :
    ∃ I : CutInsertion, I.oldCut = positionCut base h ps ∧ I.newCut = positionCut base h (ps++[p]) ∧ I.pivot = h[p] := by
  have hf : selectedWith base ps (0+p) h[p] = false := by simp [selectedWith,hnot,hfalse]
  obtain ⟨I,ho,hn,hpivot⟩ := exists_selector_insertion (selectedWith base ps) 0 h p hp hf
  refine ⟨I,ho,?_,hpivot⟩
  simpa only [Nat.zero_add,positionCut,cutSchedule,selectedWith_append_one] using hn

theorem nodup_next_not_mem_take {α : Type*} {xs : List α} (hx : xs.Nodup) {i : ℕ} (hi : i < xs.length) :
    xs[i] ∉ xs.take i := by
  intro hmem
  obtain ⟨j,hj,he⟩ := List.mem_take_iff_getElem.mp hmem
  have hjlen : j < xs.length := hj.trans_le (min_le_right _ _)
  have hji : j = i := hx.getElem_inj_iff.mp he
  have hjiLt : j < i := hj.trans_le (min_le_left _ _)
  omega

theorem exists_position_chain_insertion (base : ℕ → ℝ → Bool) (h : List ℝ) (ps : List ℕ)
    (hnd : ps.Nodup) (hvalid : ∀ p ∈ ps, p < h.length) (hfalse : ∀ p (hp : p ∈ ps), base p (h[p]'(hvalid p hp)) = false)
    (i : ℕ) (hi : i < ps.length) :
    ∃ I : CutInsertion, I.oldCut = positionCut base h (ps.take i) ∧ I.newCut = positionCut base h (ps.take (i+1)) ∧
      I.pivot = h[ps[i]]'(hvalid ps[i] (List.getElem_mem hi)) := by
  have hp := hvalid ps[i] (List.getElem_mem hi)
  have hf := hfalse ps[i] (List.getElem_mem hi)
  have hn := nodup_next_not_mem_take hnd hi
  simpa only [List.take_succ_eq_append_getElem hi] using exists_position_insertion base h (ps.take i) hp hn hf

end
end StrongSilver
