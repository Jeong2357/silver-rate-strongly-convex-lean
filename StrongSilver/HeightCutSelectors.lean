-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutTransformMap
import StrongSilver.CartesianTransformMap

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2400000

/-- A full cut in transformed height, retaining original actual steps
and their chronological indices. -/
def heightCut (φ : ℝ → ℝ) (P y : ℝ) (h : List ℝ) : ScheduleCut :=
  cutSchedule (fun _ b => decide (P+Real.exp y < φ b)) h

theorem fullCut_transformed_word (φ : ℝ → ℝ) (P y : ℝ) (h : List ℝ) :
    fullCut (P+Real.exp y) (h.map φ) = (heightCut φ P y h).mapSteps φ :=
  cutScheduleFrom_mapSteps (fun _ b => decide (P+Real.exp y < b)) φ 0 h

theorem heightCut_eq_fullCut {φ : ℝ → ℝ} (hφ : StrictMono φ) {P y A : ℝ}
    (hA : φ A = P+Real.exp y) (h : List ℝ) : heightCut φ P y h = fullCut A h := by
  have he : (fun (_ : ℕ) b => decide (P+Real.exp y < φ b)) =
      (fun (_ : ℕ) b => decide (A < b)) := by
    funext i b
    rw [← hA]
    simp only [hφ.lt_iff_lt]
  unfold heightCut fullCut
  rw [he]

theorem transformed_height_cut_log (φ : ℝ → ℝ) (P κ y : ℝ) (t : ScheduleTree) :
    cutLogProduct id P κ (fullCut (P+Real.exp y) (t.mapSteps φ).word) =
      cutLogProduct φ P κ (heightCut φ P y t.word) := by
  rw [ScheduleTree.mapSteps_word,fullCut_transformed_word,cutLogProduct_mapSteps]

theorem transformed_height_cut_power (φ : ℝ → ℝ) (P κ y : ℝ) (t : ScheduleTree) :
    cutPower id P κ (fullCut (P+Real.exp y) (t.mapSteps φ).word) =
      cutPower φ P κ (heightCut φ P y t.word) := by
  rw [ScheduleTree.mapSteps_word,fullCut_transformed_word,cutPower_mapSteps]

end
end StrongSilver
