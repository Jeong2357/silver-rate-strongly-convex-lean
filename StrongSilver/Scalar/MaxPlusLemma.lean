-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Scalar.MaxPlusScaling

namespace StrongSilver.Scalar.Silver
noncomputable section
set_option maxHeartbeats 1000000

/-- The full max-plus excess lemma, with universal positive constants and the
actual silver exponent. All global, local, gain, and scaling estimates are proved. -/
theorem max_plus_excess : ∃ c > 0, ∃ C > 0,
    ∀ a b t z : ℝ, 0 < a → 0 < b → 0 < t → a ≤ z → z ≤ a+b+t →
      c*t^nu*min 1 ((Real.log (a/(rho*t)))^2+(Real.log (b/(rho*t)))^2+(a+b+t-z)/t) ≤ excess a b t z ∧
      |gain a b t z| ≤ C*(1+excess a b t z/t^nu) := by
  obtain ⟨c,hc,hstable⟩ := unitExcess_stability
  obtain ⟨C,hC,hgain⟩ := unitGain_control
  refine ⟨c,hc,C,hC,fun a b t z ha hb ht haz hz => ?_⟩
  have hz0 : 0 < z := ha.trans_le haz
  have haz' : a/t ≤ z/t := div_le_div_of_nonneg_right haz ht.le
  have hz' : z/t ≤ a/t+b/t+1 := by
    apply (div_le_iff₀ ht).mpr
    have he : (a/t+b/t+1)*t=a+b+t := by field_simp [ht.ne'] <;> ring
    rw [he]
    exact hz
  have h1 := hstable (a/t) (b/t) (z/t) (div_pos ha ht) (div_pos hb ht) haz' hz'
  have h2 := hgain (a/t) (b/t) (z/t) (div_pos ha ht) (div_pos hb ht) haz' hz'
  rw [excess_normalize a b t z ha hb ht hz0,normalized_cost a b t z ht] at h1
  rw [excess_normalize a b t z ha hb ht hz0,gain_normalize a b t z ht] at h2
  have h1' := (le_div_iff₀ (Real.rpow_pos_of_pos ht nu)).mp h1
  refine ⟨?_,h2⟩
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h1'

end
end StrongSilver.Scalar.Silver
