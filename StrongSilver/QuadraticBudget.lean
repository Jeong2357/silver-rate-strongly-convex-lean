-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScalarQuadraticAverage
import StrongSilver.LayerCake

namespace StrongSilver
noncomputable section

def logGain (x : ℝ) : ℝ := if x < 0 then Real.log (1-x) else if 1 ≤ x then Real.log x else 0
def shortFraction (x : ℝ) : ℝ := if 0 < x ∧ x < 1 then x else 0
def logGains (h : List ℝ) (s : ℝ) : ℝ := (h.map (fun b => logGain (b/s))).sum
def shortFractions (h : List ℝ) (s : ℝ) : ℝ := (h.map (fun b => shortFraction (b/s))).sum

theorem logGain_nonneg (x : ℝ) : 0 ≤ logGain x := by
  by_cases hx : x < 0
  · rw [logGain,if_pos hx]
    exact Real.log_nonneg (by linarith)
  · rw [logGain,if_neg hx]
    split_ifs with h1
    · exact Real.log_nonneg h1
    · exact le_rfl

theorem logGains_nonneg (h : List ℝ) (s : ℝ) : 0 ≤ logGains h s := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
  exact logGain_nonneg _

theorem step_log_gain_loss : ∃ C > 0, ∀ x : ℝ,
    2*logGain x-C*shortFraction x ≤ quadraticLogIntegral x := by
  obtain ⟨C,hC,hbound⟩ := quadraticLogIntegral_lower
  refine ⟨C,hC,fun x => ?_⟩
  by_cases hx : x < 0
  · have hh := quadraticLogIntegral_negative hx.le
    simpa [logGain,shortFraction,hx,not_lt_of_ge hx.le] using hh
  · by_cases h1 : 1 ≤ x
    · have hh := quadraticLogIntegral_large h1
      simpa [logGain,shortFraction,hx,h1,not_lt_of_ge h1] using hh
    · have hx0 : 0 ≤ x := le_of_not_gt hx
      have hx1 : x < 1 := lt_of_not_ge h1
      by_cases hxpos : 0 < x
      · simpa [logGain,shortFraction,hx,h1,hxpos,hx1] using hbound x hx0 hx1.le
      · have hz : x = 0 := le_antisymm (le_of_not_gt hxpos) hx0
        subst x
        simp [logGain,shortFraction,quadraticLogIntegral]

theorem schedule_log_gain_loss {C : ℝ}
    (hbound : ∀ x : ℝ, 2*logGain x-C*shortFraction x ≤ quadraticLogIntegral x)
    (h : List ℝ) (s : ℝ) :
    2*logGains h s-C*shortFractions h s ≤ (h.map (fun b => quadraticLogIntegral (b/s))).sum := by
  induction h with
  | nil => simp [logGains,shortFractions]
  | cons b h ih =>
    simp only [logGains,shortFractions,List.map_cons,List.sum_cons] at *
    linarith only [ih,hbound (b/s)]

theorem shortFraction_le_clipped {s : ℝ} (hs : 0 < s) (b : ℝ) :
    shortFraction (b/s) ≤ max 0 (min b s)/s := by
  by_cases hh : 0 < b/s ∧ b/s < 1
  · have hb0 : 0 < b := by
      have hc := (lt_div_iff₀ hs).mp hh.1
      simpa only [zero_mul] using hc
    have hbs : b ≤ s := ((div_lt_one hs).mp hh.2).le
    rw [shortFraction,if_pos hh,min_eq_left hbs,max_eq_right hb0.le]
  · rw [shortFraction,if_neg hh]
    exact div_nonneg (le_max_left _ _) hs.le

theorem shortFractions_le_clipped {s : ℝ} (hs : 0 < s) (h : List ℝ) :
    shortFractions h s ≤ clippedMass h s/s := by
  induction h with
  | nil => simp [shortFractions,clippedMass]
  | cons b h ih =>
    simp only [shortFractions,clippedMass,List.map_cons,List.sum_cons] at *
    have hh := add_le_add (shortFraction_le_clipped hs b) ih
    simpa only [← add_div] using hh

/-- Equation (2.4), combining actual scalar tests, integrability, and the rank bound. -/
theorem scalar_log_budget : ∃ C > 0, ∀ κ s cap : ℝ, 1 < κ → 4 ≤ s → s ≤ κ → s ≤ cap →
    ∀ h : List ℝ, -Real.log (D κ h).toReal/2+logGains h s ≤ C*weightedCount h cap*s^(-nu) := by
  obtain ⟨C0,hC0,hstep⟩ := step_log_gain_loss
  have hν : 0 < 1-nu := sub_pos.mpr nu_lt_one
  refine ⟨C0/(2*(1-nu)),div_pos hC0 (mul_pos (by norm_num) hν),fun κ s cap hκ hs hsκ hcap h => ?_⟩
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hsum := schedule_log_gain_loss hstep h s
  have havg := scalar_quadratic_log_average hκ hs hsκ h
  have hb : -Real.log (D κ h).toReal/2+logGains h s ≤ (C0/2)*shortFractions h s := by
    linarith only [hsum,havg]
  have hshort := shortFractions_le_clipped hspos h
  have hmass := div_le_div_of_nonneg_right (clippedMass_rank_bound h hspos hcap) hspos.le
  have hscale : (C0/2)*(weightedCount h cap*s^(1-nu)/(1-nu)/s) =
      (C0/(2*(1-nu)))*weightedCount h cap*s^(-nu) := by
    have he : s^(1-nu) = s^(-nu)*s := by
      rw [show 1-nu = -nu+1 by ring,Real.rpow_add hspos,Real.rpow_one]
    rw [he]
    field_simp [hspos.ne',hν.ne']
  rw [← hscale]
  exact hb.trans (mul_le_mul_of_nonneg_left (hshort.trans hmass) (by positivity))

/-- Equation (2.5), at the cap aκ; constants depend only on the fixed a. -/
theorem distance_log_rank_bound : ∃ C > 0, ∀ κ a : ℝ, 1 < κ → 0 < a → a ≤ 1 → 4 ≤ a*κ →
    ∀ h : List ℝ, -Real.log (D κ h).toReal ≤
      (2*C*a^(-nu))*weightedCount h (a*κ)*κ^(-nu) := by
  obtain ⟨C,hC,hbudget⟩ := scalar_log_budget
  refine ⟨C,hC,fun κ a hκ ha ha1 hacap h => ?_⟩
  have hkpos : 0 < κ := lt_trans zero_lt_one hκ
  have hcap : a*κ ≤ κ := by nlinarith only [mul_le_mul_of_nonneg_right ha1 hkpos.le]
  have hb := hbudget κ (a*κ) (a*κ) hκ hacap hcap le_rfl h
  have hg := logGains_nonneg h (a*κ)
  rw [Real.mul_rpow ha.le hkpos.le] at hb
  nlinarith only [hb,hg]

end
end StrongSilver
