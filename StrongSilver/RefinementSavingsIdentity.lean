-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutGapRefinements

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 3000000

/-- Logarithmic saving from refining one original signed gap, after a
fixed charge for each inserted pivot. -/
def gapRefinementScore (φ : ℝ → ℝ) (P κ price : ℝ) (start : ℕ) (gap : List ℝ)
    (choose : ℕ → ℝ → Bool) : ℝ :=
  Real.log (gapPrefix φ gap+P+κ)-cutLogProduct φ P κ (cutScheduleFrom choose start gap)-
    price*((cutScheduleFrom choose start gap).phases.length:ℝ)

theorem cutLogProduct_phase_cons (φ : ℝ → ℝ) (P κ : ℝ) (q : CutPhase) (qs : List CutPhase) (t : List ℝ) :
    cutLogProduct φ P κ ⟨q::qs,t⟩ = cutLogProduct φ P κ ⟨qs,t⟩+
      Real.log (gapPrefix φ q.gap+P)-Real.log (φ q.pivot-P) := by
  simp only [cutLogProduct,cutMasses,List.map_cons,List.sum_cons,List.map_append,List.sum_append,
    List.map_nil,List.sum_nil,List.map_map,Function.comp_def,add_zero]
  ring

/-- Every gap's maximizer may be chosen independently and realized
simultaneously. This exact identity is the finite core of (4.7). -/
theorem refinement_savings_identity (φ : ℝ → ℝ) (P κ price : ℝ)
    (choose : CutPhase → ℕ → ℝ → Bool) (D : ScheduleCut) (qs : List CutPhase) (terminal : List ℝ) :
    (qs.map fun q => gapRefinementScore φ P 0 price (q.index-q.gap.length) q.gap (choose q)).sum+
      (Real.log (gapPrefix φ terminal+P+κ)-cutLogProduct φ P κ D-price*(D.phases.length:ℝ)) =
    cutLogProduct φ P κ ⟨qs,terminal⟩-cutLogProduct φ P κ (refineCutGaps choose D qs)-
      price*(((refineCutGaps choose D qs).phases.length:ℝ)-(qs.length:ℝ)) := by
  induction qs with
  | nil => simp [refineCutGaps,cutLogProduct,cutMasses]
  | cons q qs ih =>
    have hcount : (refineCutGaps choose D (q::qs)).phases.length =
        (cutScheduleFrom (choose q) (q.index-q.gap.length) q.gap).phases.length+1+
          (refineCutGaps choose D qs).phases.length := by
      simp only [refineCutGaps,ScheduleCut.concat_before_selected,List.length_append,List.length_cons]
      omega
    rw [hcount]
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    rw [cutLogProduct_phase_cons,refineCutGaps,cut_log_concat_selected]
    unfold gapRefinementScore at ih ⊢
    simp only [add_zero] at ih ⊢
    linear_combination ih

end
end StrongSilver
