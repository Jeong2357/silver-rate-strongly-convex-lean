-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SingleGapRefinement

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 3600000

/-- Every actual cut selecting only eligible indexed pivots is one of
the finite masked candidates defining the gap's savings maximum. -/
theorem gap_refinement_score_le_maximum (φ : ℝ → ℝ) (P κ price : ℝ) (start : ℕ) (word : List ℝ)
    (eligible choose : ℕ → ℝ → Bool)
    (hchoose : ∀ p : Fin word.length, choose (start+p.val) word[p] = true → eligible (start+p.val) word[p] = true) :
    gapRefinementScore φ P κ price start word choose ≤ gapSavingsMaximum φ P κ price start word eligible := by
  classical
  let E := (Finset.range word.length).filter fun j => choose (start+j) (stepAt word j) = true
  have hE : E ∈ gapMasks word := Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  have hcut : cutScheduleFrom (gapMaskSelector start E eligible) start word = cutScheduleFrom choose start word := by
    apply cutScheduleFrom_congr_values
    intro p
    have he : (start+p.val)-start = p.val := by omega
    have hs : stepAt word p.val = word[p] := stepAt_eq p.isLt
    have hmem : p.val ∈ E ↔ choose (start+p.val) word[p] = true := by
      simp only [E,Finset.mem_filter,Finset.mem_range,p.isLt,true_and,hs,Fin.getElem_fin]
    by_cases hc : choose (start+p.val) word[p] = true
    · have helig := hchoose p hc
      simp only [gapMaskSelector,he,hmem.mpr hc,decide_true,Bool.true_and,helig,hc]
    · have hm : p.val ∉ E := fun hm => hc (hmem.mp hm)
      simp only [gapMaskSelector,he,hm,decide_false,Bool.false_and,Bool.eq_false_iff.mpr hc]
  have hh := gap_score_le_maximum φ P κ price start word eligible hE
  unfold gapRefinementScore at hh ⊢
  rw [hcut] at hh
  exact hh

end
end StrongSilver
