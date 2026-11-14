-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

namespace StrongSilver
open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1800000

def geometricScale (U r : ℝ) (i : ℕ) : ℝ := U*(r⁻¹)^i

theorem geometricScale_step (U r : ℝ) (i : ℕ) :
    geometricScale U r (i+1) = geometricScale U r i/r := by
  simp only [geometricScale,pow_succ,div_eq_mul_inv,mul_assoc]

theorem geometricScale_positive {U r : ℝ} (hU : 0 < U) (hr : 0 < r) (i : ℕ) :
    0 < geometricScale U r i := mul_pos hU (pow_pos (inv_pos.mpr hr) i)

theorem geometricScale_antitone {U r : ℝ} (hU : 0 ≤ U) (hr : 1 < r) : Antitone (geometricScale U r) := by
  have hr0 := zero_lt_one.trans hr
  have hi : r⁻¹ ≤ 1 := by simpa only [one_div] using (div_le_one hr0).mpr hr.le
  apply antitone_nat_of_succ_le
  intro i
  have hs : 0 ≤ geometricScale U r i := mul_nonneg hU (pow_nonneg (inv_nonneg.mpr hr0.le) i)
  have hh := mul_le_mul_of_nonneg_left hi hs
  simpa only [geometricScale,pow_succ,mul_one,mul_assoc] using hh

/-- The stopping index is chosen by its first crossing of r*Y, so the
last scale lies in [Y,r*Y) and every earlier scale remains at least Y. -/
theorem exists_geometric_ladder {U Y r : ℝ} (hY : 0 < Y) (hr : 1 < r) (hU : r*Y ≤ U) :
    ∃ m : ℕ, 1 ≤ m ∧ Y ≤ geometricScale U r m ∧ geometricScale U r m < r*Y ∧
      ∀ i ≤ m, Y ≤ geometricScale U r i ∧ geometricScale U r i ≤ U := by
  have hr0 := zero_lt_one.trans hr
  have hU0 : 0 < U := (mul_pos hr0 hY).trans_le hU
  have hi0 : 0 ≤ r⁻¹ := inv_nonneg.mpr hr0.le
  have hi1 : r⁻¹ < 1 := by simpa only [one_div] using (div_lt_one hr0).mpr hr
  have ht : Tendsto (geometricScale U r) atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => U*(r⁻¹)^n) atTop (𝓝 0)
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hi0 hi1).const_mul U
  have he : ∃ m : ℕ, geometricScale U r m < r*Y :=
    ((tendsto_order.1 ht).2 (r*Y) (mul_pos hr0 hY)).exists
  let m := Nat.find he
  have hm : geometricScale U r m < r*Y := Nat.find_spec he
  have hmpos : 0 < m := by
    by_contra hn
    have hz : m = 0 := by omega
    rw [hz] at hm
    simp only [geometricScale,pow_zero,mul_one] at hm
    linarith only [hm,hU]
  obtain ⟨n,hn⟩ : ∃ n : ℕ, m = n+1 := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
  have hbefore : r*Y ≤ geometricScale U r n := le_of_not_gt (Nat.find_min he (by omega : n < m))
  have hlast : Y ≤ geometricScale U r m := by
    rw [hn,geometricScale_step]
    apply (le_div_iff₀ hr0).mpr
    nlinarith only [hbefore]
  have hanti := geometricScale_antitone hU0.le hr
  refine ⟨m,hmpos,hlast,hm,?_⟩
  intro i hi
  refine ⟨hlast.trans (hanti hi),?_⟩
  simpa only [geometricScale,pow_zero,mul_one] using hanti (Nat.zero_le i)

end
end StrongSilver
