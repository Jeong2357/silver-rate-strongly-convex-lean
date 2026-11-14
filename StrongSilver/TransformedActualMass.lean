-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarGapNorm
import StrongSilver.SmallAbsoluteMassProduct

namespace StrongSilver
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 1800000

theorem absoluteMass_identity (h : List ℝ) : absoluteMass h = positiveMass h+negativeMass h := by
  induction h with
  | nil => simp [absoluteMass,positiveMass,negativeMass]
  | cons b h ih =>
    have hb : |b| = max b 0+max (-b) 0 := by
      by_cases h0 : 0 ≤ b
      · rw [abs_of_nonneg h0,max_eq_left h0,max_eq_right (by linarith only [h0])]; ring
      · rw [abs_of_neg (lt_of_not_ge h0),max_eq_right (le_of_not_ge h0),max_eq_left (by linarith only [h0])]; ring
    simp only [absoluteMass,positiveMass,negativeMass,List.map_cons,List.sum_cons] at ih ⊢
    linarith only [ih,hb]

theorem logarithmicSteps_sum_ge {μ : ℝ} (hμ : 0 < μ) (h : List ℝ)
    (hh : ∀ b ∈ h, μ*b < 1) : h.sum ≤ (h.map (logarithmicStep μ)).sum := by
  simpa only [List.map_id] using (List.sum_le_sum (f := id) (g := logarithmicStep μ) (l := h)
    (fun b hb => logarithmicStep_ge hμ (hh b hb)))

theorem logarithmicSteps_negative_mass_le {μ : ℝ} (hμ : 0 < μ) (h : List ℝ)
    (hh : ∀ b ∈ h, μ*b < 1) : negativeMass (h.map (logarithmicStep μ)) ≤ negativeMass h := by
  unfold negativeMass
  rw [List.map_map]
  apply List.sum_le_sum
  intro b hb
  exact max_le_max (neg_le_neg (logarithmicStep_ge hμ (hh b hb))) le_rfl

/-- Signed schedules with small positive factors need no nonnegativity
assumption: their positive actual mass is controlled by transformed
prefix mass plus the actual negative mass. -/
theorem positive_mass_le_transformed_prefix {μ : ℝ} (hμ : 0 < μ) (h : List ℝ)
    (hh : ∀ b ∈ h, μ*b < 1) :
    positiveMass h ≤ transformedGapMaximum μ h+negativeMass h := by
  have hid := negativeMass_identity h
  have hs := (logarithmicSteps_sum_ge hμ h hh).trans (sum_le_prefixMax _)
  rw [transformed_prefix_max hμ h hh] at hs
  change h.sum ≤ transformedGapMaximum μ h at hs
  dsimp only [drawdown] at hid
  linarith only [hid,hs]

theorem absolute_mass_le_transformed_prefix {μ : ℝ} (hμ : 0 < μ) (h : List ℝ)
    (hh : ∀ b ∈ h, μ*b < 1) :
    absoluteMass h ≤ transformedGapMaximum μ h+2*negativeMass h := by
  rw [absoluteMass_identity]
  linarith only [positive_mass_le_transformed_prefix hμ h hh]

theorem transformed_drawdown_le_negative_mass {μ : ℝ} (hμ : 0 < μ) (h : List ℝ)
    (hh : ∀ b ∈ h, μ*b < 1) : drawdown (h.map (logarithmicStep μ)) ≤ negativeMass h := by
  have hid := negativeMass_identity (h.map (logarithmicStep μ))
  have hp := prefixMax_le_positiveMass (h.map (logarithmicStep μ))
  linarith only [hid,hp,logarithmicSteps_negative_mass_le hμ h hh]

end
end StrongSilver
