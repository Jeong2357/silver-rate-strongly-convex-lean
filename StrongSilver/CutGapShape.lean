-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScheduleCut
import StrongSilver.PhaseRefinement
import StrongSilver.TrackedPhaseNumbering

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1800000

def prependFirstGap (a : ℝ) : List (List ℝ) → List (List ℝ)
  | [] => []
  | g::gs => (a::g)::gs

theorem ScheduleCut.gaps_prependSelected (C : ScheduleCut) (i : ℕ) (a : ℝ) :
    (C.prependSelected i a).gaps = []::C.gaps := rfl

theorem ScheduleCut.gaps_prependUnselected (C : ScheduleCut) (a : ℝ) :
    (C.prependUnselected a).gaps = prependFirstGap a C.gaps := by
  rcases C with ⟨qs,t⟩
  cases qs <;> rfl

/-- Value-only cuts have exactly the same actual gap lists at every
choice of starting index. -/
theorem cutScheduleFrom_value_gaps (choose : ℝ → Bool) (i j : ℕ) (h : List ℝ) :
    (cutScheduleFrom (fun _ b => choose b) i h).gaps =
      (cutScheduleFrom (fun _ b => choose b) j h).gaps := by
  induction h generalizing i j with
  | nil => rfl
  | cons a h ih =>
    by_cases hc : choose a = true
    · simp only [cutScheduleFrom,hc,↓reduceIte,ScheduleCut.gaps_prependSelected]
      exact congrArg (List.cons []) (ih (i+1) (j+1))
    · have hf := Bool.eq_false_iff.mpr hc
      simp only [cutScheduleFrom,hf,Bool.false_eq_true,↓reduceIte,ScheduleCut.gaps_prependUnselected]
      exact congrArg (prependFirstGap a) (ih (i+1) (j+1))

theorem refinePhase_gap_list (choose : ℕ → ℝ → Bool) (q : CutPhase) :
    (refinePhase choose q).map CutPhase.gap = (cutScheduleFrom choose (q.index-q.gap.length) q.gap).gaps := by
  simp only [refinePhase,List.map_append,List.map_cons,List.map_nil,ScheduleCut.gaps]

theorem refinePhase_value_map_gap {α : Type*} (f : List ℝ → α) (choose : ℝ → Bool) (q : CutPhase) (j : ℕ) :
    (refinePhase (fun _ b => choose b) (q.withIndex j)).map (fun z => f z.gap) =
      (refinePhase (fun _ b => choose b) q).map (fun z => f z.gap) := by
  have he : (refinePhase (fun _ b => choose b) (q.withIndex j)).map CutPhase.gap =
      (refinePhase (fun _ b => choose b) q).map CutPhase.gap := by
    rw [refinePhase_gap_list,refinePhase_gap_list]
    exact cutScheduleFrom_value_gaps choose _ _ _
  have hh := congrArg (List.map f) he
  simpa only [List.map_map,Function.comp_def] using hh

theorem numberTrackedPhases_refined_map_gap {α : Type*} (f : List ℝ → α) (choose : ℝ → Bool)
    (i : ℕ) (qs : List CutPhase) :
    ((numberTrackedPhases i qs).flatMap (refinePhase (fun _ b => choose b))).map (fun z => f z.gap) =
      (qs.flatMap (refinePhase (fun _ b => choose b))).map (fun z => f z.gap) := by
  induction qs generalizing i with
  | nil => rfl
  | cons q qs ih => simp only [numberTrackedPhases,List.flatMap_cons,List.map_append,refinePhase_value_map_gap,ih]

end
end StrongSilver
