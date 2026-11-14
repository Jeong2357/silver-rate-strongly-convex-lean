-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InverseNegativeMass
import StrongSilver.BandNonterminal
import StrongSilver.BandBadWeightBudget

namespace StrongSilver
open ScheduleTree Scalar.SignedIntervals Filter Real
noncomputable section
set_option maxHeartbeats 3800000

theorem capped_actual_negative_mass {μ B : ℝ} (hμ : 0 < μ) (hcap : μ*B ≤ 1/2) (word : List ℝ)
    (hword : ∀ b ∈ word, b ≤ B) (hsmall : μ*negativeMass (word.map (cappedStep μ B)) ≤ 1) :
    negativeMass word ≤ 2*negativeMass (word.map (cappedStep μ B)) := by
  have he : word.map (cappedStep μ B) = word.map (logarithmicStep μ) := by
    apply List.map_congr_left
    intro b hb
    exact if_pos (hword b hb)
  rw [he] at hsmall ⊢
  apply actual_negative_mass_le_transformed hμ word _ hsmall
  intro b hb
  have hh := (mul_le_mul_of_nonneg_left (hword b hb) hμ.le).trans hcap
  linarith only [hh]

/-- A good actual band vertex supplies the original signed negative-mass
budget needed for trajectory construction, not just a transformed budget. -/
theorem eventually_good_node_negative_mass : ∀ᶠ u : ℝ in atTop,
    ∀ κ B μ δ : ℝ, ∀ h : List ℝ, ∀ q : ParentedScheduleNode, ∀ l r : ScheduleTree, ∀ b : ℝ,
    0 ≤ κ → 1 < B → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    0 ≤ δ → δ ≤ 1/4 → q ∈ bandProtectedNodes κ B μ u h → q.node.source = .split l b r →
    PaddedGood (cappedStep μ B) (bandPad u) q.node.reserve δ q.node.source →
    negativeMass l.word ≤ 2*δ*cappedStep μ B b := by
  filter_upwards [eventually_eligible_band_step_upper] with u hupper
  intro κ B μ δ h q l r b hκ hB hU hμ hμB hδ hδmax hq hs hg
  have hp := (List.mem_filter.mp hq).1
  have hh := of_decide_eq_true (List.mem_filter.mp hq).2
  have hn : q.node ∈ (parentedNodes 0 κ none (cartesian h)).map ParentedScheduleNode.node := List.mem_map.mpr ⟨q,hp,rfl⟩
  rw [parentedNodes_erase] at hn
  have hc := indexedTree_source_cartesian (cartesian_valid h) hn
  rw [hs] at hc hg
  have hbB := hupper B μ q.node.pivot q.node.pivotIndex hB hU hμ hμB hh.2.1
  have he : q.node.pivot = b := by rw [ScheduleNode.pivot,hs,rootStep_split]
  rw [he] at hbB
  have hw : ∀ a ∈ l.word, a ≤ B := fun a ha => ((hc.2.2.2.1 a ha).le).trans hbB
  have hφ := cappedStep_positive_upper hμ (zero_lt_one.trans hB) hμB hbB
  rw [max_eq_left hc.2.2.1.le] at hφ
  have hφB : cappedStep μ B b ≤ 2*B := (le_max_left _ _).trans (hφ.trans (mul_le_mul_of_nonneg_left hbB (by norm_num : (0:ℝ) ≤ 2)))
  have hneg : negativeMass (l.word.map (cappedStep μ B)) ≤ δ*cappedStep μ B b := by
    have hpad := Real.exp_pos ((987:ℝ)/1000*u)
    change 0 < bandPad u at hpad
    have hn := hg.2
    nlinarith only [hn,mul_nonneg hδ hpad.le]
  have hsmall : μ*negativeMass (l.word.map (cappedStep μ B)) ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left hneg hμ.le
    have h2 := mul_le_mul_of_nonneg_left hφB (mul_nonneg hμ.le hδ)
    have h3 := mul_le_mul_of_nonneg_right hμB (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hδ)
    nlinarith only [h1,h2,h3,hδmax]
  have hi := capped_actual_negative_mass hμ hμB l.word hw hsmall
  nlinarith only [hi,hneg]

end
end StrongSilver
