-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Quadratics

namespace StrongSilver
noncomputable section

def Instance.restart {κ : ℝ} (w : Instance κ) (x : Space w.dimension) (hx : x ≠ w.minimizer) :
    Instance κ := { w with start := x, distinct := hx }

theorem iterate_fixed {V : Type*} [AddCommGroup V] [Module ℝ V]
    (h : List ℝ) (g : V → V) (x : V) (hg : g x = 0) : iterate h g x = x := by
  induction h with
  | nil => rfl
  | cons a h ih => simpa only [iterate_cons, hg, smul_zero, sub_zero] using ih

theorem iterate_minimizer {κ : ℝ} (h : List ℝ) (w : Instance κ) :
    iterate h w.g w.minimizer = w.minimizer :=
  iterate_fixed h w.g w.minimizer
    (gradient_zero_at_min w.f w.g w.minimizer (w.admissible.gradient _) w.minimal)

theorem distance_error_append {κ : ℝ} (h k : List ℝ) (w : Instance κ)
    (hy : iterate h w.g w.start ≠ w.minimizer) :
    distanceError (h ++ k) w =
      distanceError h w * distanceError k (w.restart (iterate h w.g w.start) hy) := by
  have hn : ‖iterate h w.g w.start - w.minimizer‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy))
  simp only [distanceError, iterate_append, Instance.restart]
  exact (div_mul_div_cancel₀' hn _ _).symm

theorem value_error_append {κ : ℝ} (hκ : 0 < κ) (h k : List ℝ) (w : Instance κ)
    (hy : iterate h w.g w.start ≠ w.minimizer) :
    valueError (h ++ k) w =
      valueError h w * valueError k (w.restart (iterate h w.g w.start) hy) := by
  have hn : w.f (iterate h w.g w.start) - w.f w.minimizer ≠ 0 :=
    (value_gap_pos hκ (w.restart (iterate h w.g w.start) hy)).ne'
  simp only [valueError, iterate_append, Instance.restart]
  exact (div_mul_div_cancel₀' hn _ _).symm

theorem D_append_le (κ : ℝ) (h k : List ℝ) : D κ (h ++ k) ≤ D κ h * D κ k := by
  apply iSup_le
  intro w
  by_cases hy : iterate h w.g w.start = w.minimizer
  · simp [distanceError, iterate_append, hy, iterate_minimizer]
  · rw [distance_error_append h k w hy, ENNReal.ofReal_mul (distance_error_nonneg h w)]
    exact mul_le_mul' (distance_error_le_D h w)
      (distance_error_le_D k (w.restart (iterate h w.g w.start) hy))

theorem E_append_le {κ : ℝ} (hκ : 0 < κ) (h k : List ℝ) : E κ (h ++ k) ≤ E κ h * E κ k := by
  apply iSup_le
  intro w
  by_cases hy : iterate h w.g w.start = w.minimizer
  · simp [valueError, iterate_append, hy, iterate_minimizer]
  · rw [value_error_append hκ h k w hy, ENNReal.ofReal_mul (value_error_nonneg h w)]
    exact mul_le_mul' (value_error_le_E h w)
      (value_error_le_E k (w.restart (iterate h w.g w.start) hy))

def repeatSchedule (h : List ℝ) : ℕ → List ℝ
  | 0 => []
  | r+1 => repeatSchedule h r ++ h

@[simp] theorem repeatSchedule_length (h : List ℝ) (r : ℕ) :
    (repeatSchedule h r).length = r * h.length := by
  induction r with
  | zero => simp [repeatSchedule]
  | succ r ih => simp [repeatSchedule, ih, Nat.succ_mul]

theorem D_repeat_le {κ : ℝ} (hκ : 1 ≤ κ) (h : List ℝ) (r : ℕ) :
    D κ (repeatSchedule h r) ≤ D κ h ^ r := by
  induction r with
  | zero => simp [repeatSchedule, D_nil hκ]
  | succ r ih =>
    exact (D_append_le κ (repeatSchedule h r) h).trans
      (by simpa only [pow_succ] using mul_le_mul' ih (le_refl (D κ h)))

theorem E_repeat_le {κ : ℝ} (hκ : 1 ≤ κ) (h : List ℝ) (r : ℕ) :
    E κ (repeatSchedule h r) ≤ E κ h ^ r := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  induction r with
  | zero => simp [repeatSchedule, E_nil hκ]
  | succ r ih =>
    exact (E_append_le hκpos (repeatSchedule h r) h).trans
      (by simpa only [pow_succ] using mul_le_mul' ih (le_refl (E κ h)))

theorem distance_error_le_kappa_value_error {κ : ℝ} (hκ : 0 < κ) (h : List ℝ) (w : Instance κ) :
    distanceError h w ≤ κ * valueError h w := by
  have hl := strong_lower_at_min w.admissible.strong_convex w.minimal (iterate h w.g w.start)
  have hu := smooth_upper_at_min w.f w.g w.start w.minimizer
    w.admissible.gradient w.admissible.smooth w.minimal
  have hs : 0 < ‖w.start-w.minimizer‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr w.distinct))
  have hv := value_gap_pos hκ w
  have he : 0 ≤ w.f (iterate h w.g w.start)-w.f w.minimizer := sub_nonneg.mpr (w.minimal _)
  have hratio : ‖iterate h w.g w.start-w.minimizer‖^2 ≤
      2*κ*(w.f (iterate h w.g w.start)-w.f w.minimizer) := by
    have hdiv : ‖iterate h w.g w.start-w.minimizer‖^2/(2*κ) ≤
        w.f (iterate h w.g w.start)-w.f w.minimizer := by
      convert hl using 1 <;> ring
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < 2*κ)).mp hdiv
  have hprod : ‖iterate h w.g w.start-w.minimizer‖^2*(w.f w.start-w.f w.minimizer) ≤
      (κ*(w.f (iterate h w.g w.start)-w.f w.minimizer))*‖w.start-w.minimizer‖^2 := by
    calc
      _ ≤ (2*κ*(w.f (iterate h w.g w.start)-w.f w.minimizer)) *
          (w.f w.start-w.f w.minimizer) := mul_le_mul_of_nonneg_right hratio hv.le
      _ ≤ _ := by
        nlinarith only [mul_le_mul_of_nonneg_left hu (mul_nonneg hκ.le he)]
  change ‖iterate h w.g w.start-w.minimizer‖^2/‖w.start-w.minimizer‖^2 ≤
    κ*((w.f (iterate h w.g w.start)-w.f w.minimizer)/(w.f w.start-w.f w.minimizer))
  calc
    _ ≤ (κ*(w.f (iterate h w.g w.start)-w.f w.minimizer))/(w.f w.start-w.f w.minimizer) :=
      (div_le_div_iff₀ hs hv).mpr hprod
    _ = _ := by ring

theorem D_le_kappa_E {κ : ℝ} (hκ : 0 < κ) (h : List ℝ) : D κ h ≤ ENNReal.ofReal κ * E κ h := by
  apply iSup_le
  intro w
  have he := ENNReal.ofReal_le_ofReal (distance_error_le_kappa_value_error hκ h w)
  rw [ENNReal.ofReal_mul hκ.le] at he
  exact he.trans (mul_le_mul' le_rfl (value_error_le_E h w))

end
end StrongSilver
