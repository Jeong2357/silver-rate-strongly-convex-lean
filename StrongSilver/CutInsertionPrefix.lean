-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutInsertion

namespace StrongSilver.CutInsertion
noncomputable section
set_option maxHeartbeats 1400000

def prependSelected (j : ℕ) (a : ℝ) : CutInsertion → CutInsertion
  | .interior pre post t c k L R b i => .interior (⟨[],a,j⟩::pre) post t c k L R b i
  | .terminal pre L R b i => .terminal (⟨[],a,j⟩::pre) L R b i

def prependUnselected (a : ℝ) : CutInsertion → CutInsertion
  | .interior [] post t c k L R b i => .interior [] post t c k (a::L) R b i
  | .interior (q::pre) post t c k L R b i => .interior ({q with gap := a::q.gap}::pre) post t c k L R b i
  | .terminal [] L R b i => .terminal [] (a::L) R b i
  | .terminal (q::pre) L R b i => .terminal ({q with gap := a::q.gap}::pre) L R b i

@[simp] theorem oldCut_prependSelected (I : CutInsertion) (j : ℕ) (a : ℝ) :
    (I.prependSelected j a).oldCut = I.oldCut.prependSelected j a := by
  cases I <;> rfl

@[simp] theorem newCut_prependSelected (I : CutInsertion) (j : ℕ) (a : ℝ) :
    (I.prependSelected j a).newCut = I.newCut.prependSelected j a := by
  cases I <;> rfl

@[simp] theorem oldCut_prependUnselected (I : CutInsertion) (a : ℝ) :
    (I.prependUnselected a).oldCut = I.oldCut.prependUnselected a := by
  cases I with
  | interior pre post t c k L R b i => cases pre <;> rfl
  | terminal pre L R b i => cases pre <;> rfl

@[simp] theorem newCut_prependUnselected (I : CutInsertion) (a : ℝ) :
    (I.prependUnselected a).newCut = I.newCut.prependUnselected a := by
  cases I with
  | interior pre post t c k L R b i => cases pre <;> rfl
  | terminal pre L R b i => cases pre <;> rfl

@[simp] theorem pivot_prependSelected (I : CutInsertion) (j : ℕ) (a : ℝ) :
    (I.prependSelected j a).pivot = I.pivot := by cases I <;> rfl

@[simp] theorem pivot_prependUnselected (I : CutInsertion) (a : ℝ) :
    (I.prependUnselected a).pivot = I.pivot := by
  cases I with
  | interior pre post t c k L R b i => cases pre <;> rfl
  | terminal pre L R b i => cases pre <;> rfl

theorem selected_count_increment (I : CutInsertion) : I.newCut.phases.length = I.oldCut.phases.length+1 := by
  cases I <;> simp [oldCut,newCut] <;> omega

theorem pivot_mem_old_word (I : CutInsertion) : I.pivot ∈ I.oldCut.word := by
  cases I <;> simp [oldCut,pivot,ScheduleCut.word,CutPhase.word]

/-- Insert an unselected first step before any already partitioned suffix. -/
theorem exists_first_insertion (C : ScheduleCut) (a : ℝ) (i : ℕ) :
    ∃ I : CutInsertion, I.oldCut = C.prependUnselected a ∧ I.newCut = C.prependSelected i a ∧ I.pivot = a := by
  rcases C with ⟨qs,t⟩
  cases qs with
  | nil => exact ⟨.terminal [] [] t a i,rfl,rfl,rfl⟩
  | cons q qs => exact ⟨.interior [] qs t q.pivot q.index [] q.gap a i,rfl,rfl,rfl⟩

end
end StrongSilver.CutInsertion
