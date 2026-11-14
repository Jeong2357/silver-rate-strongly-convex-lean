-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutRankBudgets
import StrongSilver.ArcsineBudget

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 2200000

theorem negativeLogCharge_eq_negativeLogSum {κ : ℝ} (h : List ℝ) :
    negativeLogCharge κ h = negativeLogSum h κ := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro b _
  by_cases hb : b < 0
  · simp only [if_pos hb,abs_of_neg hb]
    congr 1
    ring
  · simp only [if_neg hb]

def initialMarkedRankConstant : ℝ := (9/(1-nu))*(1+1/Real.log 3)

theorem initialMarkedRankConstant_positive : 0 < initialMarkedRankConstant := by
  have hν : 0 < 1-nu := by linarith [nu_lt_one]
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  unfold initialMarkedRankConstant
  positivity

/-- Both the large-pivot count and the negative logarithmic mass are paid
by the same arcsine budget, retaining its square-root dependence on a. -/
theorem initial_large_negative_rank_bound {a κ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1/128)
    (hκ : 0 < κ) (hcap : 1 ≤ a*κ) (h : List ℝ) (hD : D κ h ≤ 1) :
    (countAbove h (κ/2) : ℝ)+negativeLogSum h κ ≤
      initialMarkedRankConstant*Real.sqrt a*weightedCount h (a*κ)*(a*κ)^(-nu) := by
  have hh := large_negative_charge_bound ha ha1 hκ hcap h hD
  rw [negativeLogCharge_eq_negativeLogSum] at hh
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hn := negativeLogSum_nonnegative hκ h
  have hc : (0 : ℝ) ≤ (countAbove h (κ/2) : ℝ) := Nat.cast_nonneg _
  let R := (9/(1-nu))*Real.sqrt a*weightedCount h (a*κ)*(a*κ)^(-nu)
  have hb : (countAbove h (κ/2) : ℝ) ≤ R/Real.log 3 := by
    apply (le_div_iff₀ hlog).mpr
    nlinarith only [hh,hn]
  have he : negativeLogSum h κ ≤ R := by
    have hp := mul_nonneg hlog.le hc
    linarith only [hh,hp]
  calc
    _ ≤ R/Real.log 3+R := add_le_add hb he
    _ = _ := by unfold R initialMarkedRankConstant; ring

/-- Quantitative marked-count estimate for the initial cut, before its
logarithmic block price is applied. -/
theorem initial_marked_rank_bound {a κ B : ℝ} (ha : 0 < a) (ha1 : a ≤ 1/128)
    (hκ : 0 < κ) (hcap : 1 ≤ a*κ) (hB : 0 < B) (hBcap : B ≤ a*κ)
    (C : ScheduleCut) (hgap : ∀ b ∈ C.unselected, 0 < b → b ≤ B) (hD : D κ C.word ≤ 1) :
    (badPhaseCount (initialPhaseTests κ) C.phases : ℝ) ≤
      initialMarkedRankConstant*Real.sqrt a*weightedCount C.word (a*κ)*(a*κ)^(-nu)+
        (weightedCount C.word (a*κ)*B^(1-nu)/(1-nu))/κ := by
  have hh := cut_three_test_marked_count (L := κ/2) hκ hκ (by norm_num : (0 : ℝ) < 1) C
  have hs := initial_large_negative_rank_bound ha ha1 hκ hcap C.word hD
  have hm := div_le_div_of_nonneg_right (C.unselected_positiveMass_rank_bound hB hBcap hgap) hκ.le
  simp only [div_one] at hh
  change (badPhaseCount (initialPhaseTests κ) C.phases : ℝ) ≤ _ at hh
  linarith only [hh,hs,hm]

end
end StrongSilver
