-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.GeometricLadder
import StrongSilver.InverseCubeLadder

namespace StrongSilver
open Real Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 8000000

theorem sum_reverse_successive_differences (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (f (i+1)-f i)) = f n-f 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; ring

/-- A finite geometric band ladder has a summable inverse-cubic log
term and a summable fixed negative-power term, uniformly in its length. -/
theorem geometric_band_rate_sum {U Y r δ : ℝ} (hY : 1 < Y) (hr : 1 < r) (hδ : 0 < δ)
    (m : ℕ) (hLast : Y ≤ geometricScale U r m) :
    (∑ i ∈ Finset.range m, (1/(Real.log (geometricScale U r i))^3+(geometricScale U r i)^(-δ))) ≤
      1/(2*Real.log r*(Real.log Y)^2)+Y^(-δ)/(r^δ-1) := by
  have hY0 := zero_lt_one.trans hY
  have hr0 := zero_lt_one.trans hr
  have hUm : 0 < geometricScale U r m := hY0.trans_le hLast
  have hU : 0 < U := by
    exact (mul_pos_iff_of_pos_right (pow_pos (inv_pos.mpr hr0) m)).mp hUm
  have hAll (i : ℕ) (hi : i ≤ m) : Y ≤ geometricScale U r i :=
    hLast.trans (geometricScale_antitone hU.le hr hi)
  have hPos (i : ℕ) : 0 < geometricScale U r i := geometricScale_positive hU hr0 i
  have hLogR : 0 < Real.log r := Real.log_pos hr
  have hLogY : 0 < Real.log Y := Real.log_pos hY
  have hLogStep (i : ℕ) : Real.log (geometricScale U r i) =
      Real.log (geometricScale U r (i+1))+Real.log r := by
    rw [geometricScale_step,Real.log_div (hPos i).ne' hr0.ne']
    ring
  have hLogBound (i : ℕ) (hi : i ≤ m) : Real.log Y ≤ Real.log (geometricScale U r i) :=
    Real.log_le_log hY0 (hAll i hi)
  have hCubeStep (i : ℕ) (hi : i < m) :
      1/(Real.log (geometricScale U r i))^3 ≤
        (1/(Real.log (geometricScale U r (i+1)))^2-1/(Real.log (geometricScale U r i))^2)/(2*Real.log r) := by
    have hh := inverse_cube_step (hLogY.trans_le (hLogBound (i+1) (by omega))) hLogR
    rwa [← hLogStep i] at hh
  have hCubeSum := Finset.sum_le_sum (s:=Finset.range m) (fun i hi => hCubeStep i (Finset.mem_range.mp hi))
  rw [← Finset.sum_div,sum_reverse_successive_differences (fun i => 1/(Real.log (geometricScale U r i))^2) m] at hCubeSum
  have hSq : (Real.log Y)^2 ≤ (Real.log (geometricScale U r m))^2 :=
    pow_le_pow_left₀ hLogY.le (hLogBound m le_rfl) 2
  have hInv := one_div_le_one_div_of_le (sq_pos_of_pos hLogY) hSq
  have hCubeUpper := div_le_div_of_nonneg_right
    (show 1/(Real.log (geometricScale U r m))^2-1/(Real.log (geometricScale U r 0))^2 ≤ 1/(Real.log Y)^2 by
      have hh : 0 ≤ 1/(Real.log (geometricScale U r 0))^2 := by positivity
      linarith only [hInv,hh]) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hLogR.le)
  have hCube : (∑ i ∈ Finset.range m, 1/(Real.log (geometricScale U r i))^3) ≤
      1/(2*Real.log r*(Real.log Y)^2) := by
    calc
      _ ≤ (1/(Real.log (geometricScale U r m))^2-1/(Real.log (geometricScale U r 0))^2)/(2*Real.log r) := hCubeSum
      _ ≤ (1/(Real.log Y)^2)/(2*Real.log r) := hCubeUpper
      _ = _ := by ring
  have hrδ : 1 < r^δ := by
    have hh := Real.rpow_lt_rpow (by norm_num : (0:ℝ) ≤ 1) hr hδ
    simpa only [Real.one_rpow] using hh
  have hPowerStep (i : ℕ) : (geometricScale U r i)^(-δ) =
      ((geometricScale U r (i+1))^(-δ)-(geometricScale U r i)^(-δ))/(r^δ-1) := by
    have hNext : (geometricScale U r (i+1))^(-δ) = (geometricScale U r i)^(-δ)*r^δ := by
      rw [geometricScale_step,Real.div_rpow (hPos i).le hr0.le,Real.rpow_neg hr0.le]
      field_simp
    rw [hNext]
    field_simp [sub_ne_zero.mpr (ne_of_gt hrδ)] <;> ring
  have hPowerSum : (∑ i ∈ Finset.range m, (geometricScale U r i)^(-δ)) =
      ((geometricScale U r m)^(-δ)-(geometricScale U r 0)^(-δ))/(r^δ-1) := by
    calc
      _ = ∑ i ∈ Finset.range m, ((geometricScale U r (i+1))^(-δ)-(geometricScale U r i)^(-δ))/(r^δ-1) :=
        Finset.sum_congr rfl (fun i _ => hPowerStep i)
      _ = _ := by rw [← Finset.sum_div,sum_reverse_successive_differences (fun i => (geometricScale U r i)^(-δ)) m]
  have hPowerBound := Real.rpow_le_rpow_of_nonpos hY0 hLast (neg_nonpos.mpr hδ.le)
  have hPower : (∑ i ∈ Finset.range m, (geometricScale U r i)^(-δ)) ≤ Y^(-δ)/(r^δ-1) := by
    rw [hPowerSum]
    apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hrδ.le)
    have hh := Real.rpow_pos_of_pos (hPos 0) (-δ)
    linarith only [hPowerBound,hh]
  rw [Finset.sum_add_distrib]
  exact add_le_add hCube hPower

/-- The uniform tail bound tends to zero at the stopping scale. -/
theorem geometric_band_rate_tail_tendsto_zero {r δ : ℝ} (hr : 1 < r) (hδ : 0 < δ) :
    Tendsto (fun Y : ℝ => 1/(2*Real.log r*(Real.log Y)^2)+Y^(-δ)/(r^δ-1)) atTop (𝓝 0) := by
  have hInv : Tendsto (fun Y : ℝ => (Real.log Y)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hSquare := (hInv.pow 2).div_const (2*Real.log r)
  have hPower := (tendsto_rpow_neg_atTop hδ).div_const (r^δ-1)
  have hSum := hSquare.add hPower
  have hSum0 : Tendsto (fun Y : ℝ => (Real.log Y)⁻¹^2/(2*Real.log r)+Y^(-δ)/(r^δ-1)) atTop (𝓝 0) := by
    simpa using hSum
  convert hSum0 using 1
  funext Y
  simp only [div_eq_mul_inv,mul_inv,inv_pow]
  ring

end
end StrongSilver
