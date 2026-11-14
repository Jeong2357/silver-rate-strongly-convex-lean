-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianTransformMap
import StrongSilver.ReservedTreeNodes
import StrongSilver.CartesianExcessIntegral

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3200000

def mapReservedNode (φ : ℝ → ℝ) (q : ScheduleTree × ℝ) : ScheduleTree × ℝ := (q.1.mapSteps φ,q.2)

theorem reservedNodes_mapSteps (φ : ℝ → ℝ) (κ : ℝ) (t : ScheduleTree) :
    (t.mapSteps φ).reservedNodes κ = (t.reservedNodes κ).map (mapReservedNode φ) := by
  induction t generalizing κ with
  | leaf hw => rfl
  | split l b r il ir => simp only [mapSteps,reservedNodes,List.map_cons,List.map_append,il,ir,mapReservedNode]

theorem rootStep_mapSteps {φ : ℝ → ℝ} (hzero : φ 0 = 0) (t : ScheduleTree) :
    (t.mapSteps φ).rootStep = φ t.rootStep := by
  cases t with
  | leaf hw => exact hzero.symm
  | split l b r => rfl

theorem paddedRootGain_mapSteps (φ : ℝ → ℝ) (P κ : ℝ) (t : ScheduleTree) :
    paddedRootGain id P κ (t.mapSteps φ) = paddedRootGain φ P κ t := by
  cases t with
  | leaf hw => rfl
  | split l b r =>
    simp only [mapSteps,paddedRootGain,mapSteps_word,gapPrefix,List.map_id,List.map_append,List.map_cons,id_eq]

theorem paddedRootDecrease_mapSteps (φ : ℝ → ℝ) (P κ : ℝ) (t : ScheduleTree) :
    paddedRootDecrease id P κ (t.mapSteps φ) = paddedRootDecrease φ P κ t := by
  cases t with
  | leaf hw => rfl
  | split l b r =>
    simp only [mapSteps,paddedRootDecrease,mapSteps_word,gapPrefix,List.map_id,List.map_append,List.map_cons,id_eq]

def nodeHeight (φ : ℝ → ℝ) (P : ℝ) (q : ScheduleTree × ℝ) : ℝ := Real.log (φ q.1.rootStep-P)

def nodeExcess (φ : ℝ → ℝ) (P : ℝ) (q : ScheduleTree × ℝ) : ℝ :=
  splitCoefficient*Real.exp (nu*nodeHeight φ P q)*paddedRootGain φ P q.2 q.1-paddedRootDecrease φ P q.2 q.1

def positivePaddedNodes (φ : ℝ → ℝ) (P κ : ℝ) (t : ScheduleTree) : List (ScheduleTree × ℝ) :=
  (t.reservedNodes κ).filter (fun q => decide (P < φ q.1.rootStep))

theorem paddedEvents_mapSteps {φ : ℝ → ℝ} (hzero : φ 0 = 0) (P κ : ℝ) (t : ScheduleTree) :
    (t.mapSteps φ).paddedEvents P κ = (positivePaddedNodes φ P κ t).map (mapReservedNode φ) := by
  rw [paddedEvents,reservedNodes_mapSteps,List.filter_map]
  simp only [positivePaddedNodes,Function.comp_def,mapReservedNode,rootStep_mapSteps hzero]

theorem paddedHeight_mapReservedNode {φ : ℝ → ℝ} (hzero : φ 0 = 0) (P : ℝ) (q : ScheduleTree × ℝ) :
    paddedHeight P (mapReservedNode φ q) = nodeHeight φ P q := by
  simp only [paddedHeight,mapReservedNode,nodeHeight,rootStep_mapSteps hzero]

theorem paddedExcess_mapReservedNode {φ : ℝ → ℝ} (hzero : φ 0 = 0) (P : ℝ) (q : ScheduleTree × ℝ) :
    paddedEventExcess P (mapReservedNode φ q) = nodeExcess φ P q := by
  unfold paddedEventExcess
  rw [paddedHeight_mapReservedNode hzero]
  simp only [mapReservedNode,nodeExcess,paddedRootGain_mapSteps,paddedRootDecrease_mapSteps]

end
end StrongSilver.ScheduleTree
