-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialOpenBlock

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1800000

def initialOpenTerminalRate (κ B μ : ℝ) (I t : List ℝ) : ℝ :=
  Real.exp (-4*(μ*Scalar.SignedIntervals.positiveMass t))/
    ((4*(1200000*(κ/B))^2)*(Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I/κ))^2)

theorem initial_open_terminal_distance_lower {κ B μ c : ℝ}
    (hκ : 1 ≤ κ) (hB : 0 < B) (hBκ : B ≤ κ) (hμ : 1/κ ≤ μ) (hμ1 : μ ≤ 1)
    (hc : 2 ≤ c) (hcB : B ≤ c) (hqc : 1/32 ≤ 1-μ*c) (hcap : μ*B ≤ 1/2)
    (I t : List ℝ) (hcritical : ∀ a ∈ I, 1-μ*a ≠ 0) (ht : ∀ a ∈ t, 0 < a → a ≤ B) :
    ENNReal.ofReal (initialOpenTerminalRate κ B μ I t) ≤ D κ ((I++[c])++t) := by
  have hκ0 := zero_lt_one.trans_le hκ
  have hμ0 : 0 < μ := (one_div_pos.mpr hκ0).trans_le hμ
  have hK : 1 ≤ κ/B := (one_le_div hB).mpr hBκ
  have hκKc : κ ≤ (κ/B)*c := by
    have hh := mul_le_mul_of_nonneg_left hcB (div_pos hκ0 hB).le
    have he : (κ/B)*B = κ := by field_simp
    rwa [he] at hh
  obtain ⟨n,Q,hQ,hsteps,hend,hratio⟩ := terminal_connector_ratio hμ0 hc hqc hκ0 hK hκKc hcap I t hcritical ht (Y := (1 : ℝ)) one_ne_zero
  have hh := (ENNReal.ofReal_le_ofReal hratio).trans (Q.finite_distance_lower hκ hμ hμ1 hQ)
  simpa only [hsteps,initialOpenTerminalRate] using hh

theorem eventually_initial_open_reserved_lower : ∀ᶠ A : ℝ in atTop,
    ∀ κ B μ c d T : ℝ, ∀ I g : List ℝ,
      A ≤ B → κ ≤ A^((1003 : ℝ)/1000) → InitialPhaseBudget B μ d T κ B g →
      1/κ ≤ μ → μ ≤ 1 → 2 ≤ c → B ≤ c → c ≤ κ → 1/32 ≤ 1-μ*c →
      (∀ a ∈ I, 1-μ*a ≠ 0) →
      ∀ s : List ℝ, ∀ M G r : ℝ, PositiveTrace μ s (workingGateFraction A) M G r →
      ENNReal.ofReal (initialReservedRate κ B μ I r) ≤ D κ ((I++[c])++((g++[d])++s)) := by
  filter_upwards [eventually_initial_gate_from_working] with A hgate
  intro κ B μ c d T I g hAB hκA W hμ hμ1 hc hcB hcκ hqc hcritical s M G r S
  obtain ⟨Sg⟩ := hgate κ B μ d T g hAB hκA W s M G r S
  exact initial_open_block_distance_lower W.kappa_large W.B_positive W.B_le_kappa hμ hμ1 hc hcB hcκ hqc I _ hcritical Sg

end
end StrongSilver
