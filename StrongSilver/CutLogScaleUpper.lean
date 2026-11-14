-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutMasses

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 3000000

theorem log_ratio_scale_upper {x a A : ℝ} (hx : 0 < x) (hA : 0 < A) (ha : A/2 ≤ a) :
    Real.log x-Real.log a ≤ (2/A)*x := by
  have ha0 : 0 < a := (half_pos hA).trans_le ha
  have hl := Real.log_le_sub_one_of_pos (div_pos hx ha0)
  calc
    _ = Real.log (x/a) := (Real.log_div hx.ne' ha0.ne').symm
    _ ≤ x/a := hl.trans (sub_le_self _ zero_le_one)
    _ ≤ x/(A/2) := div_le_div_of_nonneg_left hx.le (half_pos hA) ha
    _ = _ := by field_simp <;> ring

theorem terminal_log_scale_upper {x κ A : ℝ} (hx : 0 ≤ x) (hA : 0 < A) (hAκ : A ≤ κ) :
    Real.log (x+κ)-Real.log κ ≤ (2/A)*x := by
  have hκ := hA.trans_le hAκ
  have hxκ : 0 < x+κ := add_pos_of_nonneg_of_pos hx hκ
  have hl := Real.log_le_sub_one_of_pos (div_pos hxκ hκ)
  have he : (x+κ)/κ-1 = x/κ := by field_simp <;> ring
  have hb : x/κ ≤ x/A := div_le_div_of_nonneg_left hx hA hAκ
  have hxA : 0 ≤ x/A := div_nonneg hx hA.le
  rw [← Real.log_div hxκ.ne' hκ.ne']
  rw [he] at hl
  have he' : (2/A)*x = 2*(x/A) := by ring
  rw [he']
  linarith only [hl,hb,hxA]

/-- Uniform logarithmic upper bound at a cut whose selected factors
are at least A/2. The terminal reserve is included exactly. -/
theorem cut_log_scaled_mass_upper (φ : ℝ → ℝ) {A P κ : ℝ} (hA : 0 < A)
    (hP : 0 < P) (hAκ : A ≤ κ) (C : ScheduleCut)
    (hselected : ∀ q ∈ C.phases, A/2 ≤ φ q.pivot-P) :
    cutLogProduct φ P κ C-Real.log κ ≤
      (2/A)*((C.phases.map fun q => gapPrefix φ q.gap).sum+gapPrefix φ C.terminal+
        ((C.phases.length:ℝ)+1)*P) := by
  have hsum (qs : List CutPhase) :
      (qs.map fun q => Real.log (gapPrefix φ q.gap+P)-Real.log (φ q.pivot-P)).sum =
      (qs.map fun q => Real.log (gapPrefix φ q.gap+P)).sum-(qs.map fun q => Real.log (φ q.pivot-P)).sum := by
    induction qs with
    | nil => simp
    | cons q qs ih => simp only [List.map_cons,List.sum_cons]; linarith only [ih]
  have hp := List.sum_le_sum (l := C.phases)
    (f := fun q => Real.log (gapPrefix φ q.gap+P)-Real.log (φ q.pivot-P))
    (g := fun q => (2/A)*(gapPrefix φ q.gap+P))
    (fun q hq => log_ratio_scale_upper (add_pos_of_nonneg_of_pos (gapPrefix_nonnegative φ q.gap) hP) hA (hselected q hq))
  have ht := terminal_log_scale_upper (show 0 ≤ gapPrefix φ C.terminal+P from
    (add_pos_of_nonneg_of_pos (gapPrefix_nonnegative φ C.terminal) hP).le) hA hAκ
  rw [hsum] at hp
  simp only [List.sum_map_mul_left,List.sum_map_add,List.map_const',List.sum_replicate,nsmul_eq_mul] at hp
  simp only [cutLogProduct,cutMasses,List.map_append,List.sum_append,List.map_cons,List.sum_cons,
    List.map_nil,List.sum_nil,List.map_map,Function.comp_def,add_zero]
  nlinarith only [hp,ht]

end
end StrongSilver
