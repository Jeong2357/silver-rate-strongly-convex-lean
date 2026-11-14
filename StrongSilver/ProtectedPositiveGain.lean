-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ProtectedWindowNodes
import StrongSilver.FiniteFilteredSums

namespace StrongSilver
open ScheduleTree
noncomputable section
set_option maxHeartbeats 5200000

/-- Positive logarithmic gains on a protected actual window are paid
by short-edge charges and the long visible-gap budget. -/
theorem protected_positive_gain_charge : ∃ C > 0,
    ∀ φ : ℝ → ℝ, ∀ P κ a b : ℝ, ∀ eligible : ℕ → ℝ → Bool, ∀ t : ScheduleTree,
    Monotone φ → 0 < P → 0 ≤ κ → φ 0 ≤ 0 → t.Cartesian →
    ((protectedWindowNodes φ P κ a b eligible t).map fun q =>
      Real.exp (nu*parentedHeight φ P q)*max (paddedRootGain φ P q.node.reserve q.node.source) 0).sum ≤
    C*((parentedNodes 0 κ none t).map fun q => windowNodeExcess φ P a b q.node).sum+
      C*((parentedNodes 0 κ none t).map (shortWindowWeight φ P a b)).sum+
      ((longVisibleNodes φ P κ a b visibilitySpacing eligible t).map fun q =>
        Real.exp (nu*parentedHeight φ P q)*(max (paddedRootGain φ P q.node.reserve q.node.source) 0+
          gapLogDeficit φ P q.node.reserve q.node.source.word)).sum := by
  classical
  obtain ⟨C,hC,hgain⟩ := node_absolute_gain_charge
  refine ⟨C,hC,?_⟩
  intro φ P κ a b eligible t hφ hP hκ hzero hc
  let xs := parentedNodes 0 κ none t
  let qs := protectedWindowNodes φ P κ a b eligible t
  let vs := longVisibleNodes φ P κ a b visibilitySpacing eligible t
  let w := fun q : ParentedScheduleNode => Real.exp (nu*parentedHeight φ P q)
  let G := fun q : ParentedScheduleNode => max (paddedRootGain φ P q.node.reserve q.node.source) 0+
    gapLogDeficit φ P q.node.reserve q.node.source.word
  let V := fun q : ParentedScheduleNode => @ite ℝ (q ∈ vs) (Classical.propDecidable _) (w q*G q) 0
  let E := fun q : ParentedScheduleNode => windowNodeExcess φ P a b q.node
  let T := shortWindowWeight φ P a b
  have hE (q : ParentedScheduleNode) : 0 ≤ E q := windowNodeExcess_nonnegative φ hP hzero a b q.node
  have hT (q : ParentedScheduleNode) : 0 ≤ T q := by
    dsimp only [T,shortWindowWeight]
    split_ifs
    · exact (Real.exp_pos _).le
    · exact le_rfl
  have hV : ∀ q ∈ xs, 0 ≤ V q := by
    intro q hq
    dsimp only [V]
    split_ifs
    · exact mul_nonneg (Real.exp_pos _).le (add_nonneg (le_max_right _ _)
        (gapLogDeficit_nonnegative φ hP (parentedNodes_reserve_nonnegative hκ hq) _))
    · exact le_rfl
  have hpoint : ∀ q ∈ qs, w q*max (paddedRootGain φ P q.node.reserve q.node.source) 0 ≤ C*E q+C*T q+V q := by
    intro q hq
    obtain ⟨hmem,he⟩ := List.mem_filter.mp hq
    obtain ⟨hroot,helig,hlo,hhi⟩ := of_decide_eq_true he
    have hres := parentedNodes_reserve_nonnegative hκ hmem
    have hmass : E q = nodeExcess φ P (q.node.source,q.node.reserve) := by
      apply if_pos
      exact ⟨hroot,hres,hlo,by change parentedHeight φ P q ≤ b; linarith only [hhi,visibilitySpacing_positive]⟩
    have hw : 0 ≤ w q := (Real.exp_pos _).le
    rcases protected_node_short_or_long hφ hκ hc hq with hs | hl
    · have ht : T q = w q := if_pos hs
      have hg := hgain φ P q.node.reserve q.node.source hP hres hzero hroot
      have hmax : max (paddedRootGain φ P q.node.reserve q.node.source) 0 ≤ |paddedRootGain φ P q.node.reserve q.node.source| :=
        max_le (le_abs_self _) (abs_nonneg _)
      have hh := mul_le_mul_of_nonneg_left hmax hw
      rw [ht,hmass]
      dsimp only [w,parentedHeight] at hh ⊢
      linear_combination hg+hh+hV q hmem
    · have hv : V q = w q*G q := if_pos hl
      have hg := mul_nonneg hw (gapLogDeficit_nonnegative φ hP hres q.node.source.word)
      rw [hv]
      dsimp only [G]
      have he := mul_nonneg hC.le (hE q)
      have ht := mul_nonneg hC.le (hT q)
      nlinarith only [hg,he,ht]
  have hsum := List.sum_le_sum hpoint
  simp only [List.sum_map_add,List.sum_map_mul_left] at hsum
  have hsub : qs.Sublist xs := List.filter_sublist
  have hES : (qs.map E).sum ≤ (xs.map E).sum := (hsub.map E).sum_le_sum (by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact hE q)
  have hTS : (qs.map T).sum ≤ (xs.map T).sum := (hsub.map T).sum_le_sum (by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact hT q)
  have hVS : (qs.map V).sum ≤ (xs.map V).sum := (hsub.map V).sum_le_sum (by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
    exact hV q hq)
  have hvEq : (xs.map V).sum = (vs.map fun q => w q*G q).sum := by
    have hh := list_sum_if_mem_filter (fun q : ParentedScheduleNode => decide
      (P < φ q.node.pivot ∧ eligible q.node.pivotIndex q.node.pivot = true ∧
        a ≤ parentedHeight φ P q+visibilitySpacing ∧ parentedHeight φ P q+2*visibilitySpacing ≤ b ∧
        parentWindowClear φ P visibilitySpacing q)) (fun q => w q*G q) xs
    exact hh
  rw [hvEq] at hVS
  have heC := mul_le_mul_of_nonneg_left hES hC.le
  have htC := mul_le_mul_of_nonneg_left hTS hC.le
  dsimp only [qs,xs,E,T,w] at hsum heC htC hVS ⊢
  linear_combination hsum+heC+htC+hVS

end
end StrongSilver
