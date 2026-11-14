-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BalancedSplitMasses
import StrongSilver.PaddedNodeDrawdown
import StrongSilver.IndexedGapObservables

namespace StrongSilver
open ScheduleTree Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3600000

theorem gapLogDeficit_eq_log_ratio (φ : ℝ → ℝ) {P κ : ℝ} (hP : 0 < P) (hκ : 0 ≤ κ) (word : List ℝ) :
    gapLogDeficit φ P κ word =
      Real.log (1+(positiveMass (word.map φ)-prefixMax (word.map φ))/(gapPrefix φ word+P+κ)) := by
  have hm : 0 < gapPrefix φ word+P+κ := by
    have hh := gapPrefix_nonnegative φ word
    linarith only [hh,hP,hκ]
  have hp : 0 < positiveMass (word.map φ)+P+κ := by
    have hh := positiveMass_nonneg (word.map φ)
    linarith only [hh,hP,hκ]
  rw [gapLogDeficit,gapPrefix_positivePart,← Real.log_div hp.ne' hm.ne']
  congr 1
  unfold gapPrefix
  change 0 < prefixMax (word.map φ)+P+κ at hm
  field_simp [hm.ne'] <;> ring

/-- On a balanced vertex, failure of the actual transformed negative
mass test is paid by drawdown or the visible gap logarithmic deficit. -/
theorem balanced_node_negative_failure {φ : ℝ → ℝ} {P κ δ : ℝ} {t : ScheduleTree}
    (hP : 0 < P) (hκ : 0 ≤ κ) (hzero : φ 0 ≤ 0) (hδ : 0 ≤ δ) (hδmax : δ ≤ 1/4)
    (hb : PaddedBalanced φ P κ δ t) (hbad : ¬ PaddedGood φ P κ δ t) :
    δ ≤ 2*(nodeLeftDrawdown φ t/(φ t.rootStep-P))+23*gapLogDeficit φ P κ t.word := by
  have hroot := hb.root_positive
  let S := paddedInput φ hP hκ hzero t hroot
  have hbal : S.Balanced δ := (paddedInput_balance_iff φ hP hκ hzero t hroot δ).mpr hb
  have hneg : δ*S.t < negativeMass S.left := by
    cases t with
    | leaf hw => exact False.elim hb
    | split l b r =>
      have hh : ¬ negativeMass (l.word.map φ) ≤ δ*(φ b-P) := fun hh => hbad ⟨hb,hh⟩
      exact lt_of_not_ge hh
  have hg := gapLogDeficit_nonnegative φ hP hκ t.word
  have hdraw : 0 ≤ nodeLeftDrawdown φ t/(φ t.rootStep-P) := by
    rw [← paddedInput_left_drawdown φ hP hκ hzero t hroot]
    exact div_nonneg (drawdown_nonneg _) (sub_pos.mpr hroot).le
  rcases PaddedSplitInput.balanced_negative_failure_visible hδ hδmax hbal hneg with hd | hd
  · rw [paddedInput_left_drawdown,paddedInput_time] at hd
    have hh := (lt_div_iff₀ (sub_pos.mpr hroot)).mpr (by linarith only [hd] : δ*(φ t.rootStep-P) < 2*nodeLeftDrawdown φ t)
    have he : 2*nodeLeftDrawdown φ t/(φ t.rootStep-P) = 2*(nodeLeftDrawdown φ t/(φ t.rootStep-P)) := by ring
    rw [he] at hh
    linarith only [hh,hg]
  · have he : Real.log (1+(positiveMass (S.left++S.pivot::S.right)-prefixMax (S.left++S.pivot::S.right))/S.z) =
        gapLogDeficit φ P κ t.word := by
      rw [gapLogDeficit_eq_log_ratio φ hP hκ,paddedInput_mass]
      cases t with
      | leaf hw => exact False.elim hb
      | split l b r =>
        simp only [S,paddedInput,word,List.map_append,List.map_cons]
    rw [he] at hd
    linarith only [hd,hdraw]

end
end StrongSilver
