-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScalarPotentialHeight
import StrongSilver.Schedules

namespace StrongSilver.ScalarRamp
open Set Real
noncomputable section
variable (R : ScalarRamp)
set_option maxHeartbeats 1000000

theorem backward_map_lower (h : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (1-R.base*h)*x-|h| * R.amplitude ≤ x-h*R.physical x := by
  have hH := R.physical_positive_bounds hx
  have he : |R.physical x-R.base*x| ≤ R.amplitude := by
    rw [abs_of_nonneg (sub_nonneg.mpr hH.1)]
    linarith only [hH.2]
  have hp : h*(R.physical x-R.base*x) ≤ |h| * R.amplitude := (le_abs_self (h*(R.physical x-R.base*x))).trans
    (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left he (abs_nonneg h))
  nlinarith only [hp]

theorem positive_predecessor {h y : ℝ} (hh : 0 < 1-R.base*h) (hy : 0 < y) :
    ∃ x : ℝ, 0 < x ∧ x-h*R.physical x = y := by
  let M : ℝ := (y+|h| * R.amplitude)/(1-R.base*h)
  have hnum : 0 < y+|h| * R.amplitude := add_pos_of_pos_of_nonneg hy (mul_nonneg (abs_nonneg h) R.amplitude_nonnegative)
  have hM : 0 < M := div_pos hnum hh
  have hbound := R.backward_map_lower h hM.le
  have hcancel : (1-R.base*h)*M = y+|h| * R.amplitude := mul_div_cancel₀ _ hh.ne'
  have hzero : (0 : ℝ)-h*R.physical 0 = 0 := by rw [R.physical_zero,mul_zero,sub_zero]
  have hyI : y ∈ Icc ((0 : ℝ)-h*R.physical 0) (M-h*R.physical M) := by
    rw [hzero]
    exact ⟨hy.le,by linarith only [hbound,hcancel]⟩
  have hc : Continuous (fun x : ℝ => x-h*R.physical x) := continuous_id.sub (continuous_const.mul R.physical_continuous)
  obtain ⟨x,hx,hxy⟩ := intermediate_value_Icc hM.le hc.continuousOn hyI
  refine ⟨x,lt_of_le_of_ne hx.1 ?_,hxy⟩
  intro he
  have hx0 : x = 0 := he.symm
  change x-h*R.physical x = y at hxy
  rw [hx0,hzero] at hxy
  linarith

theorem predecessor_upper {h x y : ℝ} (hx : 0 ≤ x) (he : x-h*R.physical x = y) :
    (h ≤ 0 → x ≤ y) ∧ (0 ≤ h → (1-R.base*h)*x ≤ y+h*R.amplitude) := by
  have hp := R.physical_positive_bounds hx
  have hH0 : 0 ≤ R.physical x := (mul_nonneg R.base_nonnegative hx).trans hp.1
  constructor
  · intro hh
    have hm := mul_nonpos_of_nonpos_of_nonneg hh hH0
    linarith only [he,hm]
  · intro hh
    have hm := mul_le_mul_of_nonneg_left hp.2 hh
    nlinarith only [he,hm]

theorem positive_trajectory (h : List ℝ) (hh : ∀ b ∈ h, R.base*b < 1) {y : ℝ} (hy : 0 < y) :
    ∃ x : ℝ, iterate h R.physical x = y ∧
      ∀ i : ℕ, i ≤ h.length → 0 < iterate (h.take i) R.physical x := by
  induction h generalizing y with
  | nil => exact ⟨y,rfl,fun i hi => by simpa only [iterate,List.take_nil,List.foldl_nil] using hy⟩
  | cons b h ih =>
    obtain ⟨z,hz,hstates⟩ := ih (fun c hc => hh c (List.mem_cons_of_mem b hc)) hy
    have hz0 : 0 < z := by simpa only [List.take_zero,iterate_nil] using hstates 0 (by omega)
    obtain ⟨x,hx,hxz⟩ := R.positive_predecessor (h := b) (by linarith [hh b List.mem_cons_self]) hz0
    refine ⟨x,?_,fun i hi => ?_⟩
    · rw [iterate_cons]
      change iterate h R.physical (x-b*R.physical x) = y
      rw [hxz,hz]
    · cases i with
      | zero => simpa only [List.take_zero,iterate_nil] using hx
      | succ i =>
        rw [List.take_succ_cons,iterate_cons]
        change 0 < iterate (h.take i) R.physical (x-b*R.physical x)
        rw [hxz]
        exact hstates i (by simp only [List.length_cons] at hi; omega)

end
end StrongSilver.ScalarRamp
