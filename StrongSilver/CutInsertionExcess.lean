-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutInsertion
import StrongSilver.PaddedSplitCharges

namespace StrongSilver.CutInsertion
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2200000

/-- The concrete scalar split input for an insertion of an original
signed step; only a terminal insertion receives the terminal reserve. -/
def splitInput (φ : ℝ → ℝ) {P reserve : ℝ} (hP : 0 < P) (hr : 0 ≤ reserve)
    (I : CutInsertion) (hi : P < φ I.pivot) : PaddedSplitInput where
  left := I.left.map φ
  right := I.right.map φ
  pivot := φ I.pivot
  pad := P
  reserve := I.splitReserve reserve
  pad_positive := hP
  reserve_nonnegative := by cases I <;> first | exact le_rfl | exact hr
  pivot_large := hi

@[simp] theorem splitInput_gain (φ : ℝ → ℝ) {P reserve : ℝ} (hP : 0 < P) (hr : 0 ≤ reserve)
    (I : CutInsertion) (hi : P < φ I.pivot) :
    (I.splitInput φ hP hr hi).gain = cutLogProduct φ P reserve I.oldCut-cutLogProduct φ P reserve I.newCut := by
  rw [I.log_difference φ hP hr hi]
  simp only [PaddedSplitInput.gain,PaddedSplitInput.a,PaddedSplitInput.b,PaddedSplitInput.t,
    PaddedSplitInput.z,splitInput,a,b,z,gapPrefix,List.map_append,List.map_cons]

@[simp] theorem splitInput_decrease (φ : ℝ → ℝ) {P reserve : ℝ} (hP : 0 < P) (hr : 0 ≤ reserve)
    (I : CutInsertion) (hi : P < φ I.pivot) :
    (I.splitInput φ hP hr hi).decrease = cutPower φ P reserve I.oldCut-cutPower φ P reserve I.newCut := by
  rw [I.power_difference]
  simp only [PaddedSplitInput.decrease,PaddedSplitInput.a,PaddedSplitInput.b,PaddedSplitInput.z,
    splitInput,a,b,z,gapPrefix,List.map_append,List.map_cons]

/-- The excess used in Section 4 is attached to an actual before/after
cut, rather than introduced as an independent nonnegative variable. -/
theorem split_excess_identity (φ : ℝ → ℝ) {P reserve : ℝ} (hP : 0 < P) (hr : 0 ≤ reserve)
    (I : CutInsertion) (hi : P < φ I.pivot) :
    (I.splitInput φ hP hr hi).excess = splitCoefficient*(φ I.pivot-P)^nu*
      (cutLogProduct φ P reserve I.oldCut-cutLogProduct φ P reserve I.newCut)-
      (cutPower φ P reserve I.oldCut-cutPower φ P reserve I.newCut) := by
  have hh := (I.splitInput φ hP hr hi).decrease_identity
  rw [splitInput_decrease,splitInput_gain] at hh
  change cutPower φ P reserve I.oldCut-cutPower φ P reserve I.newCut =
    splitCoefficient*(φ I.pivot-P)^nu*(cutLogProduct φ P reserve I.oldCut-cutLogProduct φ P reserve I.newCut)-
      (I.splitInput φ hP hr hi).excess at hh
  linarith only [hh]

end
end StrongSilver.CutInsertion
