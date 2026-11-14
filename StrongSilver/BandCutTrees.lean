-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandCutObservables
import StrongSilver.CartesianPositiveMap
import StrongSilver.CartesianExcessBudgets

namespace StrongSilver
open ScheduleTree
noncomputable section
set_option maxHeartbeats 2800000

def bandSignedTree (μ B : ℝ) (h : List ℝ) : ScheduleTree := (cartesian h).mapSteps (cappedStep μ B)
def bandPositiveTree (μ B : ℝ) (h : List ℝ) : ScheduleTree :=
  (cartesian h).mapSteps (positivePartStep (cappedStep μ B))

theorem bandSignedTree_cartesian {μ B : ℝ} (hμ : 0 < μ) (hB : 0 ≤ B) (hcap : μ*B < 1) (h : List ℝ) :
    (bandSignedTree μ B h).Cartesian := capped_map_cartesian hμ hB hcap (cartesian_valid h)

theorem bandPositiveTree_cartesian {μ B : ℝ} (hμ : 0 < μ) (hB : 0 ≤ B) (hcap : μ*B < 1) (h : List ℝ) :
    (bandPositiveTree μ B h).Cartesian :=
  positivePart_map_cartesian (cappedStep_strictMono hμ hcap)
    (by simp only [cappedStep,if_pos hB,logarithmicStep_zero]) (cartesian_valid h)

theorem band_heightCut_eq {μ B u y : ℝ} (hμ : 0 < μ) (hcap : μ*B < 1)
    (hbranch : cappedStep μ B (bandCutoff μ u y) = bandPad u+Real.exp y) (h : List ℝ) :
    heightCut (cappedStep μ B) (bandPad u) y h = bandFullCut μ u y h :=
  heightCut_eq_fullCut (cappedStep_strictMono hμ hcap) hbranch h

theorem bandSignedTree_log {κ μ B u y : ℝ} {h : List ℝ}
    (hcut : heightCut (cappedStep μ B) (bandPad u) y h = bandFullCut μ u y h) :
    cutLogProduct id (bandPad u) κ (fullCut (bandPad u+Real.exp y) (bandSignedTree μ B h).word)-Real.log κ =
      bandSignedLog κ B μ u y h := by
  have hh := transformed_height_cut_log (cappedStep μ B) (bandPad u) κ y (cartesian h)
  rw [cartesian_word,hcut] at hh
  change cutLogProduct id (bandPad u) κ (fullCut (bandPad u+Real.exp y) ((cartesian h).mapSteps (cappedStep μ B)).word)-Real.log κ = _
  exact congrArg (fun x => x-Real.log κ) hh

theorem bandPositiveTree_log {κ μ B u y : ℝ} {h : List ℝ}
    (hcut : heightCut (cappedStep μ B) (bandPad u) y h = bandFullCut μ u y h) :
    cutLogProduct id (bandPad u) κ (fullCut (bandPad u+Real.exp y) (bandPositiveTree μ B h).word)-Real.log κ =
      bandPositiveLog κ B μ u y h := by
  have hh := transformed_height_cut_log (positivePartStep (cappedStep μ B)) (bandPad u) κ y (cartesian h)
  rw [cartesian_word,heightCut_positivePart (P := bandPad u) (show 0 ≤ bandPad u by exact (Real.exp_pos _).le),hcut] at hh
  exact congrArg (fun x => x-Real.log κ) hh

theorem bandSignedTree_power {κ μ B u y : ℝ} {h : List ℝ}
    (hcut : heightCut (cappedStep μ B) (bandPad u) y h = bandFullCut μ u y h) :
    cutPower id (bandPad u) κ (fullCut (bandPad u+Real.exp y) (bandSignedTree μ B h).word) =
      bandSignedPower κ B μ u y h := by
  have hh := transformed_height_cut_power (cappedStep μ B) (bandPad u) κ y (cartesian h)
  rw [cartesian_word,hcut] at hh
  exact hh

theorem bandPositiveTree_power {κ μ B u y : ℝ} {h : List ℝ}
    (hcut : heightCut (cappedStep μ B) (bandPad u) y h = bandFullCut μ u y h) :
    cutPower id (bandPad u) κ (fullCut (bandPad u+Real.exp y) (bandPositiveTree μ B h).word) =
      bandPositivePower κ B μ u y h := by
  have hh := transformed_height_cut_power (positivePartStep (cappedStep μ B)) (bandPad u) κ y (cartesian h)
  rw [cartesian_word,heightCut_positivePart (P := bandPad u) (show 0 ≤ bandPad u by exact (Real.exp_pos _).le),hcut] at hh
  exact hh

end
end StrongSilver
