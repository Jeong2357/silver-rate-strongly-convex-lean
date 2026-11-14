-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ParentChargeMultiplicity
import StrongSilver.BandNodeCharges

namespace StrongSilver
open ScheduleTree
noncomputable section
set_option maxHeartbeats 3800000

def windowNodeExcess (φ : ℝ → ℝ) (P a b : ℝ) (q : ScheduleNode) : ℝ :=
  if P < φ q.pivot ∧ 0 ≤ q.reserve ∧ a < nodeHeight φ P (q.source,q.reserve) ∧ nodeHeight φ P (q.source,q.reserve) ≤ b
  then nodeExcess φ P (q.source,q.reserve) else 0

theorem windowNodeExcess_nonnegative (φ : ℝ → ℝ) {P : ℝ} (hP : 0 < P) (hzero : φ 0 ≤ 0)
    (a b : ℝ) (q : ScheduleNode) : 0 ≤ windowNodeExcess φ P a b q := by
  unfold windowNodeExcess
  split_ifs with hq
  · exact nodeExcess_nonnegative φ hP hq.2.1 hzero q.source hq.1
  · exact le_rfl

theorem parentedNodes_sum_reserves (F : ScheduleTree × ℝ → ℝ) (start : ℕ) (κ : ℝ)
    (parent : Option ScheduleNode) (t : ScheduleTree) :
    ((parentedNodes start κ parent t).map fun q => F (q.node.source,q.node.reserve)).sum =
      ((t.reservedNodes κ).map F).sum := by
  have h1 := congrArg (fun qs : List ScheduleNode => (qs.map fun q => F (q.source,q.reserve)).sum)
    (parentedNodes_erase start κ parent t)
  have h2 := congrArg (fun qs : List (ScheduleTree × ℝ) => (qs.map F).sum)
    (indexedTree_labels_reserves start κ t)
  simp only [List.map_map,Function.comp_def] at h1 h2
  exact h1.trans h2

/-- The positioned tree charges sum to precisely the excess in the
original height window. Outside that window the charge is zero. -/
theorem windowNodeExcess_sum {φ : ℝ → ℝ} {P κ a b : ℝ} (hκ : 0 ≤ κ) (t : ScheduleTree) :
    ((parentedNodes 0 κ none t).map fun q => windowNodeExcess φ P a b q.node).sum =
      ((nodesInHeightWindow φ P κ a b t).map (nodeExcess φ P)).sum := by
  let F := fun q : ScheduleTree × ℝ =>
    if P < φ q.1.rootStep ∧ 0 ≤ q.2 ∧ a < nodeHeight φ P q ∧ nodeHeight φ P q ≤ b then nodeExcess φ P q else 0
  have he : ((parentedNodes 0 κ none t).map fun q => windowNodeExcess φ P a b q.node).sum =
      ((t.reservedNodes κ).map F).sum := parentedNodes_sum_reserves F 0 κ none t
  rw [he]
  clear he
  unfold nodesInHeightWindow positivePaddedNodes
  have hvalid : ∀ q ∈ t.reservedNodes κ, 0 ≤ q.2 := fun _ hq => reservedNodes_reserve_nonnegative hκ hq
  generalize t.reservedNodes κ = qs at *
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    have hr := hvalid q (by simp)
    have hi := ih (fun x hx => hvalid x (List.mem_cons_of_mem q hx))
    dsimp only [F] at hi
    by_cases hp : P < φ q.1.rootStep <;>
      by_cases hw : a < nodeHeight φ P q ∧ nodeHeight φ P q ≤ b
    · simp only [List.map_cons,List.sum_cons,F,hp,hr,hw.1,hw.2,and_self,↓reduceIte,
        List.filter_cons,decide_true,hi]
    · have hcond : ¬ (P < φ q.1.rootStep ∧ 0 ≤ q.2 ∧ a < nodeHeight φ P q ∧ nodeHeight φ P q ≤ b) := fun hh => hw ⟨hh.2.2.1,hh.2.2.2⟩
      simp only [List.map_cons,List.sum_cons,F,if_neg hcond,List.filter_cons,decide_eq_true hp,↓reduceIte,
        decide_eq_false hw,Bool.false_eq_true,zero_add,hi]
    · have hcond : ¬ (P < φ q.1.rootStep ∧ 0 ≤ q.2 ∧ a < nodeHeight φ P q ∧ nodeHeight φ P q ≤ b) := fun hh => hp hh.1
      simp only [List.map_cons,List.sum_cons,F,if_neg hcond,List.filter_cons,decide_eq_false hp,Bool.false_eq_true,↓reduceIte,zero_add,hi]
    · have hcond : ¬ (P < φ q.1.rootStep ∧ 0 ≤ q.2 ∧ a < nodeHeight φ P q ∧ nodeHeight φ P q ≤ b) := fun hh => hp hh.1
      simp only [List.map_cons,List.sum_cons,F,if_neg hcond,List.filter_cons,decide_eq_false hp,Bool.false_eq_true,↓reduceIte,zero_add,hi]

theorem band_windowNodeExcess_sum {κ B cap μ u : ℝ} (hκ : 0 ≤ κ) (hB : 0 ≤ B) (h : List ℝ) :
    ((parentedNodes 0 κ none (cartesian h)).map fun q =>
      windowNodeExcess (cappedStep μ B) (bandPad u) (outerBandLow u) (outerBandHigh u) q.node).sum =
        bandExcessSum κ B cap μ u h := by
  rw [windowNodeExcess_sum hκ,bandExcessSum_eq_original hB]
  rfl

end
end StrongSilver
