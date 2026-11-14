-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutMasses
import StrongSilver.PaddedGapSplit

namespace StrongSilver
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2200000

/-- Insert one actual pivot in an interior gap or in the terminal gap. -/
inductive CutInsertion where
  | interior (before after : List CutPhase) (terminal : List ℝ) (following : ℝ) (followingIndex : ℕ)
      (left right : List ℝ) (pivot : ℝ) (index : ℕ)
  | terminal (before : List CutPhase) (left right : List ℝ) (pivot : ℝ) (index : ℕ)

namespace CutInsertion

def oldCut : CutInsertion → ScheduleCut
  | .interior pre post t c j L R b i => ⟨pre++(⟨L++b::R,c,j⟩::post),t⟩
  | .terminal pre L R b i => ⟨pre,L++b::R⟩

def newCut : CutInsertion → ScheduleCut
  | .interior pre post t c j L R b i => ⟨pre++(⟨L,b,i⟩::⟨R,c,j⟩::post),t⟩
  | .terminal pre L R b i => ⟨pre++[⟨L,b,i⟩],R⟩

def left : CutInsertion → List ℝ
  | .interior _ _ _ _ _ L _ _ _ => L
  | .terminal _ L _ _ _ => L

def right : CutInsertion → List ℝ
  | .interior _ _ _ _ _ _ R _ _ => R
  | .terminal _ _ R _ _ => R

def pivot : CutInsertion → ℝ
  | .interior _ _ _ _ _ _ _ b _ => b
  | .terminal _ _ _ b _ => b

def splitReserve (reserve : ℝ) : CutInsertion → ℝ
  | .interior _ _ _ _ _ _ _ _ _ => 0
  | .terminal _ _ _ _ _ => reserve

def a (φ : ℝ → ℝ) (P : ℝ) (I : CutInsertion) : ℝ := gapPrefix φ I.left+P
def b (φ : ℝ → ℝ) (P reserve : ℝ) (I : CutInsertion) : ℝ := gapPrefix φ I.right+P+I.splitReserve reserve
def z (φ : ℝ → ℝ) (P reserve : ℝ) (I : CutInsertion) : ℝ := gapPrefix φ (I.left++I.pivot::I.right)+P+I.splitReserve reserve

theorem word_preserved (I : CutInsertion) : I.oldCut.word = I.newCut.word := by
  cases I <;> simp [oldCut,newCut,ScheduleCut.word,CutPhase.word,List.append_assoc]

theorem power_difference (φ : ℝ → ℝ) (P reserve : ℝ) (I : CutInsertion) :
    cutPower φ P reserve I.oldCut-cutPower φ P reserve I.newCut = powerDecrease (I.a φ P) (I.b φ P reserve) (I.z φ P reserve) := by
  cases I <;> simp only [oldCut,newCut,cutPower,cutMasses,a,b,z,left,right,pivot,splitReserve,
    List.map_append,List.sum_append,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,add_zero,zero_add,powerDecrease] <;> ring

theorem log_difference_raw (φ : ℝ → ℝ) (P reserve : ℝ) (I : CutInsertion) :
    cutLogProduct φ P reserve I.oldCut-cutLogProduct φ P reserve I.newCut =
      Real.log (I.z φ P reserve)-Real.log (I.a φ P)-Real.log (I.b φ P reserve)+Real.log (φ I.pivot-P) := by
  cases I <;> simp only [oldCut,newCut,cutLogProduct,cutMasses,a,b,z,left,right,pivot,splitReserve,
    List.map_append,List.sum_append,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,add_zero,zero_add] <;> ring

theorem mass_bounds (φ : ℝ → ℝ) {P reserve : ℝ} (hP : 0 < P) (hr : 0 ≤ reserve) (I : CutInsertion)
    (hi : P < φ I.pivot) :
    0 < I.a φ P ∧ 0 < I.b φ P reserve ∧ 0 < φ I.pivot-P ∧
      I.a φ P ≤ I.z φ P reserve ∧ I.z φ P reserve ≤ I.a φ P+I.b φ P reserve+(φ I.pivot-P) := by
  have hres : 0 ≤ I.splitReserve reserve := by cases I <;> first | exact le_rfl | exact hr
  obtain ⟨ha,hb,ht,haz,hz,hdef⟩ := padded_gap_split_masses (I.left.map φ) (I.right.map φ) hP hres hi
  simpa only [a,b,z,gapPrefix,List.map_append,List.map_cons] using And.intro ha (And.intro hb (And.intro ht (And.intro haz hz)))

theorem log_difference (φ : ℝ → ℝ) {P reserve : ℝ} (hP : 0 < P) (hr : 0 ≤ reserve) (I : CutInsertion)
    (hi : P < φ I.pivot) :
    cutLogProduct φ P reserve I.oldCut-cutLogProduct φ P reserve I.newCut =
      splitGain (I.a φ P) (I.b φ P reserve) (φ I.pivot-P) (I.z φ P reserve) := by
  obtain ⟨ha,hb,ht,haz,hz⟩ := I.mass_bounds φ hP hr hi
  have hz0 := ha.trans_le haz
  rw [log_difference_raw,splitGain,Real.log_div (mul_pos ht hz0).ne' (mul_pos ha hb).ne',
    Real.log_mul ht.ne' hz0.ne',Real.log_mul ha.ne' hb.ne']
  ring

/-- The scalar split inequality now acts on concrete cuts of the actual
schedule, including the terminal reserve convention. -/
theorem power_log_control (φ : ℝ → ℝ) {P reserve : ℝ} (hP : 0 < P) (hr : 0 ≤ reserve) (I : CutInsertion)
    (hi : P < φ I.pivot) :
    cutPower φ P reserve I.oldCut-cutPower φ P reserve I.newCut ≤
      splitCoefficient*(φ I.pivot-P)^nu*(cutLogProduct φ P reserve I.oldCut-cutLogProduct φ P reserve I.newCut) := by
  obtain ⟨ha,hb,ht,haz,hz⟩ := I.mass_bounds φ hP hr hi
  rw [I.power_difference,I.log_difference φ hP hr hi]
  exact split_power_decrease_le _ _ _ _ ha hb ht haz hz

end CutInsertion
end
end StrongSilver
