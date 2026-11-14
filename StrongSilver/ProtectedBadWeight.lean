-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ProtectedWindowNodes
import StrongSilver.NodeNegativeFailure
import StrongSilver.FiniteFilteredSums

namespace StrongSilver
open ScheduleTree
noncomputable section
set_option maxHeartbeats 6200000

local instance (φ : ℝ → ℝ) (P κ δ : ℝ) (t : ScheduleTree) : Decidable (PaddedGood φ P κ δ t) := Classical.propDecidable _

/-- Finite good/bad weight estimate on a protected actual Cartesian
window. Every term on the right is an actual excess, visible-gap
logarithm, or short-edge charge proved earlier. -/
theorem protected_bad_weight_charge : ∃ K > 0,
    ∀ φ : ℝ → ℝ, ∀ P κ a b δ : ℝ, ∀ eligible : ℕ → ℝ → Bool, ∀ t : ScheduleTree,
    Monotone φ → 0 < P → 0 ≤ κ → φ 0 ≤ 0 → 0 ≤ δ → δ ≤ 1/4 → t.Cartesian →
    δ^2*((protectedWindowNodes φ P κ a b eligible t).map fun q =>
      if PaddedGood φ P q.node.reserve δ q.node.source then 0 else Real.exp (nu*parentedHeight φ P q)).sum ≤
    K*((parentedNodes 0 κ none t).map fun q => windowNodeExcess φ P a b q.node).sum+
      23*((longVisibleNodes φ P κ a b visibilitySpacing eligible t).map fun q =>
        Real.exp (nu*parentedHeight φ P q)*(max (paddedRootGain φ P q.node.reserve q.node.source) 0+
          gapLogDeficit φ P q.node.reserve q.node.source.word)).sum+
      ((parentedNodes 0 κ none t).map (shortWindowWeight φ P a b)).sum := by
  classical
  obtain ⟨c₁,hc₁,hbad⟩ := node_unbalanced_charge
  obtain ⟨c₂,hc₂,hdraw⟩ := node_drawdown_charge
  let K := 1/c₁+2/c₂
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K,hK,?_⟩
  intro φ P κ a b δ eligible t hφ hP hκ hzero hδ hδmax hc
  let xs := parentedNodes 0 κ none t
  let qs := protectedWindowNodes φ P κ a b eligible t
  let vs := longVisibleNodes φ P κ a b visibilitySpacing eligible t
  let w := fun q : ParentedScheduleNode => Real.exp (nu*parentedHeight φ P q)
  let G := fun q : ParentedScheduleNode => max (paddedRootGain φ P q.node.reserve q.node.source) 0+
    gapLogDeficit φ P q.node.reserve q.node.source.word
  let V := fun q : ParentedScheduleNode => if q ∈ vs then w q*G q else 0
  let E := fun q : ParentedScheduleNode => windowNodeExcess φ P a b q.node
  let T := shortWindowWeight φ P a b
  have hE (q : ParentedScheduleNode) : 0 ≤ E q := windowNodeExcess_nonnegative φ hP hzero a b q.node
  have hT (q : ParentedScheduleNode) : 0 ≤ T q := by
    dsimp only [T,shortWindowWeight]
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have hG : ∀ q ∈ xs, 0 ≤ G q := by
    intro q hq
    exact add_nonneg (le_max_right _ _) (gapLogDeficit_nonnegative φ hP (parentedNodes_reserve_nonnegative hκ hq) _)
  have hV : ∀ q ∈ xs, 0 ≤ V q := by
    intro q hq
    dsimp only [V]
    split_ifs
    · exact mul_nonneg (Real.exp_pos _).le (hG q hq)
    · exact le_rfl
  have hδ1 : δ ≤ 1 := hδmax.trans (by norm_num)
  have hδsq : δ^2 ≤ 1 := by nlinarith only [hδ,hδ1]
  have hδsqδ : δ^2 ≤ δ := by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hδ1)]
  have hpoint : ∀ q ∈ qs,
      δ^2*(if PaddedGood φ P q.node.reserve δ q.node.source then 0 else w q) ≤ K*E q+23*V q+T q := by
    intro q hq
    have hmem := (List.mem_filter.mp hq).1
    have hh := of_decide_eq_true (List.mem_filter.mp hq).2
    obtain ⟨hroot,helig,hlo,hhi⟩ := hh
    have hres := parentedNodes_reserve_nonnegative hκ hmem
    have hW : 0 ≤ w q := (Real.exp_pos _).le
    have hEK := mul_nonneg hK.le (hE q)
    have hVq := hV q hmem
    have hTq := hT q
    by_cases hg : PaddedGood φ P q.node.reserve δ q.node.source
    · rw [if_pos hg,mul_zero]
      positivity
    · rw [if_neg hg]
      by_cases hs : ShortWindowEdge φ P a b q
      · have ht : T q = w q := if_pos hs
        have hi := mul_le_mul_of_nonneg_right hδsq hW
        rw [one_mul] at hi
        rw [ht]
        linarith only [hi,hEK,hVq]
      · have hlong : q ∈ vs := (protected_node_short_or_long hφ hκ hc hq).resolve_left hs
        have hVeq : V q = w q*G q := if_pos hlong
        have hmass : E q = nodeExcess φ P (q.node.source,q.node.reserve) := by
          apply if_pos
          exact ⟨hroot,hres,hlo,by change parentedHeight φ P q ≤ b; linarith only [hhi,visibilitySpacing_positive]⟩
        have hEn := hE q
        have hKE : K*E q = E q/c₁+2*(E q/c₂) := by dsimp only [K]; ring
        have hcE₁ : 0 ≤ E q/c₁ := div_nonneg hEn hc₁.le
        have hcE₂ : 0 ≤ E q/c₂ := div_nonneg hEn hc₂.le
        rw [hKE]
        by_cases hb : PaddedBalanced φ P q.node.reserve δ q.node.source
        · have hN := balanced_node_negative_failure hP hres hzero hδ hδmax hb hg
          have hD := hdraw φ P q.node.reserve δ q.node.source hP hres hzero hroot hδ1 hb
          rw [← hmass] at hD
          have hD' : w q*(nodeLeftDrawdown φ q.node.source/(φ q.node.pivot-P)) ≤ E q/c₂ := by
            apply (le_div_iff₀ hc₂).mpr
            dsimp only [w,parentedHeight,ScheduleNode.pivot]
            linear_combination hD
          have hN' := mul_le_mul_of_nonneg_left hN hW
          have hsmall := mul_le_mul_of_nonneg_right hδsqδ hW
          have hDef : w q*gapLogDeficit φ P q.node.reserve q.node.source.word ≤ V q := by
            rw [hVeq]
            have hp := mul_nonneg hW (le_max_right (paddedRootGain φ P q.node.reserve q.node.source) (0:ℝ))
            dsimp only [G]
            nlinarith only [hp]
          dsimp only [w,parentedHeight,ScheduleNode.pivot] at hN' hD' hsmall hDef ⊢
          linear_combination hsmall+hN'+2*hD'+23*hDef+hcE₁+hTq
        · have hB := hbad φ P q.node.reserve δ q.node.source hP hres hzero hroot hδ hδ1 hb
          rw [← hmass] at hB
          have hB' : δ^2*w q ≤ E q/c₁ := by
            apply (le_div_iff₀ hc₁).mpr
            dsimp only [w,parentedHeight]
            linear_combination hB
          linarith only [hB',hcE₂,hVq,hTq]
  have hsum := List.sum_le_sum hpoint
  simp only [List.sum_map_mul_left,List.sum_map_add] at hsum
  have hsub : qs.Sublist xs := List.filter_sublist
  have heSum : (qs.map E).sum ≤ (xs.map E).sum := (hsub.map E).sum_le_sum (by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact hE q)
  have htSum : (qs.map T).sum ≤ (xs.map T).sum := (hsub.map T).sum_le_sum (by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact hT q)
  have hvSum : (qs.map V).sum ≤ (xs.map V).sum := (hsub.map V).sum_le_sum (by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact hV q hq)
  have hvEq : (xs.map V).sum = (vs.map fun q => w q*G q).sum := by
    dsimp only [vs,longVisibleNodes]
    rw [list_filter_sum_eq]
    congr 1
    apply List.map_congr_left
    intro q hq
    dsimp only [V]
    by_cases hh : q ∈ vs
    · have he := (List.mem_filter.mp hh).2
      rw [if_pos hh,if_pos he]
    · have he : ¬ decide (P < φ q.node.pivot ∧ eligible q.node.pivotIndex q.node.pivot = true ∧
          a ≤ parentedHeight φ P q+visibilitySpacing ∧ parentedHeight φ P q+2*visibilitySpacing ≤ b ∧
          parentWindowClear φ P visibilitySpacing q) = true := fun he => hh (List.mem_filter.mpr ⟨hq,he⟩)
      rw [if_neg (by exact hh),if_neg he]
  rw [hvEq] at hvSum
  have heK := mul_le_mul_of_nonneg_left heSum hK.le
  dsimp only [qs,xs,E,T,V,w,G] at hsum heK htSum hvSum ⊢
  linear_combination hsum+heK+23*hvSum+htSum

end
end StrongSilver
