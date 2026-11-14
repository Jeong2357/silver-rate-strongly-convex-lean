-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FiniteGapSavings
import StrongSilver.CanonicalPositionCuts

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 3200000

def pointEligibleSelector (target : ℕ) (eligible : ℕ → ℝ → Bool) (j : ℕ) (b : ℝ) : Bool :=
  if j = target then eligible j b else false

theorem pointEligible_cut_after {target start : ℕ} (ht : target < start)
    (eligible : ℕ → ℝ → Bool) (h : List ℝ) :
    cutScheduleFrom (pointEligibleSelector target eligible) start h = ⟨[],h⟩ := by
  have he : cutScheduleFrom (pointEligibleSelector target eligible) start h =
      cutScheduleFrom (fun _ _ => false) start h := by
    apply cutScheduleFrom_congr
    intro j b hj _
    simp only [pointEligibleSelector,if_neg (by omega : j ≠ target)]
  rw [he]
  exact cutScheduleFrom_none _ start h (by intros; rfl)

theorem pointEligible_cut_split (eligible : ℕ → ℝ → Bool) (start : ℕ) (L R : List ℝ) (b : ℝ)
    (he : eligible (start+L.length) b = true) :
    cutScheduleFrom (pointEligibleSelector (start+L.length) eligible) start (L++b::R) =
      ⟨[⟨L,b,start+L.length⟩],R⟩ := by
  induction L generalizing start with
  | nil =>
    have ht := pointEligible_cut_after (target := start) (start := start+1) (by omega) eligible R
    simp only [List.nil_append,List.length_nil,Nat.add_zero] at he ⊢
    rw [cutScheduleFrom]
    have hh : pointEligibleSelector start eligible start b = true := by simpa only [pointEligibleSelector,↓reduceIte] using he
    rw [hh,if_pos rfl,ht]
    rfl
  | cons a L ih =>
    have htarget : start+(a::L).length = (start+1)+L.length := by simp only [List.length_cons]; omega
    have hhead : pointEligibleSelector (start+(a::L).length) eligible start a = false := by
      simp only [pointEligibleSelector,if_neg (by simp only [List.length_cons]; omega : start ≠ start+(a::L).length)]
    change cutScheduleFrom _ start (a::(L++b::R)) = _
    rw [cutScheduleFrom,hhead,if_neg Bool.false_ne_true,htarget,ih (start+1) (by simpa only [htarget] using he)]
    rfl

theorem gapMask_singleton_cut (eligible : ℕ → ℝ → Bool) (start : ℕ) (L R : List ℝ) (b : ℝ)
    (he : eligible (start+L.length) b = true) :
    cutScheduleFrom (gapMaskSelector start {L.length} eligible) start (L++b::R) =
      ⟨[⟨L,b,start+L.length⟩],R⟩ := by
  have hcong : cutScheduleFrom (gapMaskSelector start {L.length} eligible) start (L++b::R) =
      cutScheduleFrom (pointEligibleSelector (start+L.length) eligible) start (L++b::R) := by
    apply cutScheduleFrom_congr
    intro j x hj _
    by_cases heq : j = start+L.length
    · have hd : j-start = L.length := by omega
      simp only [gapMaskSelector,Finset.mem_singleton,hd,decide_true,Bool.true_and,pointEligibleSelector,if_pos heq]
    · have hd : j-start ≠ L.length := by omega
      simp only [gapMaskSelector,Finset.mem_singleton,if_neg heq,pointEligibleSelector,hd,decide_false,Bool.false_and]
  rw [hcong]
  exact pointEligible_cut_split eligible start L R b he

/-- Inserting just the visible root is one of the finite competitors
for R_I. Its logarithmic saving is its exact scalar gain less one charge. -/
theorem single_pivot_saving_le_maximum (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ)
    (price : ℝ) (start : ℕ) (L R : List ℝ) (b : ℝ) (hb : P < φ b)
    (eligible : ℕ → ℝ → Bool) (he : eligible (start+L.length) b = true) :
    splitGain (gapPrefix φ L+P) (gapPrefix φ R+P+κ) (φ b-P) (gapPrefix φ (L++b::R)+P+κ)-price ≤
      gapSavingsMaximum φ P κ price start (L++b::R) eligible := by
  have hmask : {L.length} ∈ gapMasks (L++b::R) := by
    simp only [gapMasks,Finset.mem_powerset,Finset.singleton_subset_iff,Finset.mem_range,List.length_append,List.length_cons]
    omega
  have hmax := gap_score_le_maximum φ P κ price start (L++b::R) eligible hmask
  have hcut := gapMask_singleton_cut eligible start L R b he
  let I : CutInsertion := .terminal [] L R b (start+L.length)
  have hg := I.log_difference φ hP hκ hb
  have hold : cutLogProduct φ P κ I.oldCut = Real.log (gapPrefix φ (L++b::R)+P+κ) := by
    simp only [I,CutInsertion.oldCut,cutLogProduct,cutMasses,List.map_nil,List.nil_append,List.map_cons,
      List.sum_cons,List.sum_nil,add_zero,sub_zero]
  rw [hold] at hg
  have hs : gapRefinementScore φ P κ price start (L++b::R) (gapMaskSelector start {L.length} eligible) =
      splitGain (gapPrefix φ L+P) (gapPrefix φ R+P+κ) (φ b-P) (gapPrefix φ (L++b::R)+P+κ)-price := by
    rw [gapRefinementScore,hcut]
    simp only [List.length_singleton,Nat.cast_one]
    change Real.log (gapPrefix φ (L++b::R)+P+κ)-cutLogProduct φ P κ I.newCut-price*(1:ℝ) = _
    change Real.log (gapPrefix φ (L++b::R)+P+κ)-cutLogProduct φ P κ I.newCut =
      splitGain (gapPrefix φ L+P) (gapPrefix φ R+P+κ) (φ b-P) (gapPrefix φ (L++b::R)+P+κ) at hg
    linear_combination hg
  rwa [hs] at hmax

end
end StrongSilver
