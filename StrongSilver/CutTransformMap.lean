-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutMasses

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2200000

namespace CutPhase

def mapSteps (φ : ℝ → ℝ) (q : CutPhase) : CutPhase := ⟨q.gap.map φ,φ q.pivot,q.index⟩

end CutPhase
namespace ScheduleCut

def mapSteps (φ : ℝ → ℝ) (C : ScheduleCut) : ScheduleCut := ⟨C.phases.map (CutPhase.mapSteps φ),C.terminal.map φ⟩

@[simp] theorem mapSteps_prependSelected (φ : ℝ → ℝ) (C : ScheduleCut) (i : ℕ) (b : ℝ) :
    (C.prependSelected i b).mapSteps φ = (C.mapSteps φ).prependSelected i (φ b) := rfl

@[simp] theorem mapSteps_prependUnselected (φ : ℝ → ℝ) (C : ScheduleCut) (b : ℝ) :
    (C.prependUnselected b).mapSteps φ = (C.mapSteps φ).prependUnselected (φ b) := by
  cases C with
  | mk qs t => cases qs <;> rfl

end ScheduleCut

theorem cutScheduleFrom_mapSteps (choose : ℕ → ℝ → Bool) (φ : ℝ → ℝ) (i : ℕ) (h : List ℝ) :
    cutScheduleFrom choose i (h.map φ) =
      (cutScheduleFrom (fun j b => choose j (φ b)) i h).mapSteps φ := by
  induction h generalizing i with
  | nil => rfl
  | cons b h ih =>
    simp only [List.map_cons,cutScheduleFrom,ih]
    split <;> simp only [ScheduleCut.mapSteps_prependSelected,ScheduleCut.mapSteps_prependUnselected]

theorem cutPower_mapSteps (φ : ℝ → ℝ) (P κ : ℝ) (C : ScheduleCut) :
    cutPower id P κ (C.mapSteps φ) = cutPower φ P κ C := by
  simp only [cutPower,cutMasses,ScheduleCut.mapSteps,CutPhase.mapSteps,List.map_map,Function.comp_def,gapPrefix,List.map_id]
  rfl

theorem cutLogProduct_mapSteps (φ : ℝ → ℝ) (P κ : ℝ) (C : ScheduleCut) :
    cutLogProduct id P κ (C.mapSteps φ) = cutLogProduct φ P κ C := by
  simp only [cutLogProduct,cutMasses,ScheduleCut.mapSteps,CutPhase.mapSteps,List.map_map,Function.comp_def,gapPrefix,List.map_id]
  rfl

end
end StrongSilver
