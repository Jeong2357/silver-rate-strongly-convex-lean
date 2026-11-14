-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WeightedCount

namespace StrongSilver
noncomputable section

theorem countAbove_pos_iff (h : List ℝ) (s : ℝ) :
    0 < countAbove h s ↔ ∃ b ∈ h, s ≤ b := by
  simp [countAbove, List.length_pos_iff, List.mem_filter]

theorem weightedCount_le (h : List ℝ) (cap M : ℝ) (hM : 0 ≤ M)
    (hm : ∀ s : ℝ, 0 < s → s ≤ cap → s^nu*(countAbove h s : ℝ) ≤ M) :
    weightedCount h cap ≤ M := by
  apply maxWeight_le hM
  intro w hw
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hw
  unfold candidateWeight
  split_ifs with hpos
  · exact hm _ hpos (min_le_right _ _)
  · exact hM

theorem weightedCount_le_length (h : List ℝ) {cap : ℝ} (hcap : 0 < cap) :
    weightedCount h cap ≤ cap^nu*(h.length : ℝ) := by
  apply weightedCount_le h cap _ (by positivity)
  intro s hs hscap
  apply mul_le_mul (Real.rpow_le_rpow hs.le hscap nu_positive.le)
  · exact_mod_cast countAbove_le_length h s
  · positivity
  · positivity

theorem weightedCount_positive (h : List ℝ) {cap b : ℝ} (hcap : 0 < cap)
    (hb : b ∈ h) (hbpos : 0 < b) : 0 < weightedCount h cap := by
  have hs : 0 < min b cap := lt_min hbpos hcap
  have hN : 0 < countAbove h (min b cap) :=
    (countAbove_pos_iff _ _).mpr ⟨b,hb,min_le_left _ _⟩
  have hw : 0 < candidateWeight h cap b := by
    rw [candidateWeight, if_pos hs]
    exact mul_pos (Real.rpow_pos_of_pos hs nu) (by exact_mod_cast hN)
  exact hw.trans_le (candidate_le_weightedCount h cap hb)

theorem maxWeight_eq_zero_or_mem (l : List ℝ) : maxWeight l = 0 ∨ maxWeight l ∈ l := by
  induction l with
  | nil => exact Or.inl rfl
  | cons a l ih =>
    change max a (maxWeight l) = 0 ∨ max a (maxWeight l) ∈ a :: l
    rcases le_total a (maxWeight l) with ha | ha
    · rw [max_eq_right ha]
      rcases ih with hz | hm
      · exact Or.inl hz
      · exact Or.inr (by simp [hm])
    · rw [max_eq_left ha]
      exact Or.inr (by simp)

theorem exists_weightedCount_maximizer (h : List ℝ) (cap : ℝ) (hW : 0 < weightedCount h cap) :
    ∃ B : ℝ, 0 < B ∧ B ≤ cap ∧ B^nu*(countAbove h B : ℝ) = weightedCount h cap := by
  have hm := maxWeight_eq_zero_or_mem (h.map (candidateWeight h cap))
  change weightedCount h cap = 0 ∨ weightedCount h cap ∈ h.map (candidateWeight h cap) at hm
  rcases hm with hz | hm
  · exact False.elim (hW.ne' hz)
  · obtain ⟨b,hb,he⟩ := List.mem_map.mp hm
    have hpos : 0 < min b cap := by
      by_contra hn
      rw [candidateWeight, if_neg hn] at he
      exact hW.ne' he.symm
    refine ⟨min b cap,hpos,min_le_right _ _,?_⟩
    simpa only [candidateWeight, if_pos hpos] using he

theorem weightedCount_repeat (h : List ℝ) {cap : ℝ} (hcap : 0 < cap) (r : ℕ) :
    weightedCount (repeatSchedule h r) cap = (r : ℝ)*weightedCount h cap := by
  have hr : (0 : ℝ) ≤ r := by positivity
  apply le_antisymm
  · apply weightedCount_le _ _ _ (mul_nonneg hr (weightedCount_nonneg h cap))
    intro s hs hscap
    rw [countAbove_repeat, Nat.cast_mul]
    have hh := mul_le_mul_of_nonneg_left (threshold_le_weightedCount h hs hscap) hr
    nlinarith only [hh]
  · rcases eq_or_lt_of_le (weightedCount_nonneg h cap) with hzero | hpos
    · rw [← hzero, mul_zero]
      exact weightedCount_nonneg _ _
    · obtain ⟨B,hB,hBcap,hmax⟩ := exists_weightedCount_maximizer h cap hpos
      have hb := threshold_le_weightedCount (repeatSchedule h r) hB hBcap
      rw [countAbove_repeat, Nat.cast_mul] at hb
      rw [← hmax]
      nlinarith only [hb]

theorem weightedCount_append_le (h k : List ℝ) (cap : ℝ) :
    weightedCount (h ++ k) cap ≤ weightedCount h cap+weightedCount k cap := by
  apply weightedCount_le _ _ _ (add_nonneg (weightedCount_nonneg _ _) (weightedCount_nonneg _ _))
  intro s hs hscap
  have hh := threshold_le_weightedCount h hs hscap
  have hk := threshold_le_weightedCount k hs hscap
  rw [countAbove_append, Nat.cast_add]
  nlinarith only [hh,hk]

end
end StrongSilver
