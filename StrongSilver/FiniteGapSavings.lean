-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.RefinementSavingsIdentity
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 3000000

/-- A finite mask selects original local positions, subject to the
prescribed eligible-height predicate. -/
def gapMaskSelector (start : ℕ) (E : Finset ℕ) (eligible : ℕ → ℝ → Bool) (j : ℕ) (b : ℝ) : Bool :=
  decide (j-start ∈ E) && eligible j b

def gapMasks (gap : List ℝ) : Finset (Finset ℕ) := (Finset.range gap.length).powerset

theorem empty_mem_gapMasks (gap : List ℝ) : ∅ ∈ gapMasks gap := by simp [gapMasks]

theorem exists_max_gap_score (φ : ℝ → ℝ) (P κ price : ℝ) (start : ℕ) (gap : List ℝ)
    (eligible : ℕ → ℝ → Bool) :
    ∃ E ∈ gapMasks gap, ∀ D ∈ gapMasks gap,
      gapRefinementScore φ P κ price start gap (gapMaskSelector start D eligible) ≤
        gapRefinementScore φ P κ price start gap (gapMaskSelector start E eligible) :=
  Finset.exists_max_image (gapMasks gap)
    (fun E => gapRefinementScore φ P κ price start gap (gapMaskSelector start E eligible))
    ⟨∅,empty_mem_gapMasks gap⟩

def maximizingGapMask (φ : ℝ → ℝ) (P κ price : ℝ) (start : ℕ) (gap : List ℝ)
    (eligible : ℕ → ℝ → Bool) : Finset ℕ :=
  (exists_max_gap_score φ P κ price start gap eligible).choose

def gapSavingsMaximum (φ : ℝ → ℝ) (P κ price : ℝ) (start : ℕ) (gap : List ℝ)
    (eligible : ℕ → ℝ → Bool) : ℝ :=
  gapRefinementScore φ P κ price start gap
    (gapMaskSelector start (maximizingGapMask φ P κ price start gap eligible) eligible)

theorem maximizingGapMask_mem (φ : ℝ → ℝ) (P κ price : ℝ) (start : ℕ) (gap : List ℝ)
    (eligible : ℕ → ℝ → Bool) : maximizingGapMask φ P κ price start gap eligible ∈ gapMasks gap :=
  (exists_max_gap_score φ P κ price start gap eligible).choose_spec.1

theorem gap_score_le_maximum (φ : ℝ → ℝ) (P κ price : ℝ) (start : ℕ) (gap : List ℝ)
    (eligible : ℕ → ℝ → Bool) {E : Finset ℕ} (hE : E ∈ gapMasks gap) :
    gapRefinementScore φ P κ price start gap (gapMaskSelector start E eligible) ≤
      gapSavingsMaximum φ P κ price start gap eligible :=
  (exists_max_gap_score φ P κ price start gap eligible).choose_spec.2 E hE

theorem gap_score_empty (φ : ℝ → ℝ) (P κ price : ℝ) (start : ℕ) (gap : List ℝ)
    (eligible : ℕ → ℝ → Bool) :
    gapRefinementScore φ P κ price start gap (gapMaskSelector start ∅ eligible) = 0 := by
  have hnone : cutScheduleFrom (gapMaskSelector start ∅ eligible) start gap = ⟨[],gap⟩ := by
    apply cutScheduleFrom_none
    intro b hb j
    simp only [gapMaskSelector,Finset.notMem_empty,decide_false,Bool.false_and]
  simp only [gapRefinementScore,hnone,cutLogProduct,cutMasses,List.map_nil,List.nil_append,
    List.map_cons,List.sum_cons,List.sum_nil,List.length_nil,Nat.cast_zero,mul_zero,add_zero,sub_zero,sub_self]

theorem gapSavingsMaximum_nonnegative (φ : ℝ → ℝ) (P κ price : ℝ) (start : ℕ) (gap : List ℝ)
    (eligible : ℕ → ℝ → Bool) : 0 ≤ gapSavingsMaximum φ P κ price start gap eligible := by
  have hh := gap_score_le_maximum φ P κ price start gap eligible (empty_mem_gapMasks gap)
  rwa [gap_score_empty] at hh

theorem gapMaskSelector_eligible {start j : ℕ} {E : Finset ℕ} {eligible : ℕ → ℝ → Bool} {b : ℝ}
    (h : gapMaskSelector start E eligible j b = true) : eligible j b = true := by
  have hh : decide (j-start ∈ E) = true ∧ eligible j b = true := by simpa only [gapMaskSelector,Bool.and_eq_true] using h
  exact hh.2

end
end StrongSilver
