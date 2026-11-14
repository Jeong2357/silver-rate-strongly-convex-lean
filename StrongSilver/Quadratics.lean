-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Calculus

namespace StrongSilver
noncomputable section

def quadraticMultiplier (s : ℝ) (h : List ℝ) : ℝ :=
  (h.map (fun a => 1 - s*a)).prod

theorem quadratic_iterate {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (s : ℝ) (h : List ℝ) (x : V) :
    iterate h (fun y => s • y) x = quadraticMultiplier s h • x := by
  induction h generalizing x with
  | nil => simp [quadraticMultiplier]
  | cons a h ih =>
    rw [iterate_cons, ih]
    simp only [quadraticMultiplier, List.map_cons, List.prod_cons]
    module

def quadraticInstance (κ s : ℝ) (hs : 1/κ ≤ s) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : Instance κ where
  dimension := 0
  f := fun x => (s/2)*‖x‖^2
  g := fun x => s • x
  admissible := {
    strong_convex := by
      apply strongConvexOn_iff_convex.mpr
      convert quadratic_convex (V := Space 0) (s-1/κ) (sub_nonneg.mpr hs) using 1
      funext x
      ring
    gradient := quadratic_hasGradientAt s
    smooth := quadratic_lipschitz s hs0 hs1
  }
  start := EuclideanSpace.single 0 1
  minimizer := 0
  minimal := by intro x; simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]; positivity
  distinct := by
    intro he
    have hn := congrArg norm he
    simp at hn

theorem quadratic_distance_error (κ s : ℝ) (hs : 1/κ ≤ s) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (h : List ℝ) :
    distanceError h (quadraticInstance κ s hs hs0 hs1) = quadraticMultiplier s h ^ 2 := by
  change ‖iterate h (fun y : Space 0 => s • y) (EuclideanSpace.single 0 1) - 0‖ ^ 2 /
    ‖(EuclideanSpace.single 0 1 : Space 0) - 0‖ ^ 2 = _
  rw [quadratic_iterate]
  simp [norm_smul, Real.norm_eq_abs, sq_abs]

theorem quadratic_value_error (κ s : ℝ) (hs : 1/κ ≤ s) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hspos : 0 < s) (h : List ℝ) :
    valueError h (quadraticInstance κ s hs hs0 hs1) = quadraticMultiplier s h ^ 2 := by
  change ((s/2)*‖iterate h (fun y : Space 0 => s • y) (EuclideanSpace.single 0 1)‖^2 -
    (s/2)*‖(0 : Space 0)‖^2) /
    ((s/2)*‖(EuclideanSpace.single 0 1 : Space 0)‖^2 - (s/2)*‖(0 : Space 0)‖^2) = _
  rw [quadratic_iterate]
  simp only [norm_smul, Real.norm_eq_abs,
    EuclideanSpace.norm_single, Real.norm_eq_abs, abs_one, mul_one, norm_zero,
    zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, one_pow, sq_abs]
  field_simp [hspos.ne']

theorem quadratic_distance_lower (κ s : ℝ) (hκ : 0 < κ) (hs : 1/κ ≤ s) (hs1 : s ≤ 1)
    (h : List ℝ) : ENNReal.ofReal (quadraticMultiplier s h ^ 2) ≤ D κ h := by
  have hs0 : 0 ≤ s := le_trans (by positivity) hs
  simpa only [quadratic_distance_error] using distance_error_le_D h (quadraticInstance κ s hs hs0 hs1)

theorem quadratic_value_lower (κ s : ℝ) (hκ : 0 < κ) (hs : 1/κ ≤ s) (hs1 : s ≤ 1)
    (h : List ℝ) : ENNReal.ofReal (quadraticMultiplier s h ^ 2) ≤ E κ h := by
  have hspos : 0 < s := lt_of_lt_of_le (by positivity) hs
  simpa only [quadratic_value_error κ s hs hspos.le hs1 hspos] using
    value_error_le_E h (quadraticInstance κ s hs hspos.le hs1)

theorem D_nil {κ : ℝ} (hκ : 1 ≤ κ) : D κ [] = 1 := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hs : 1/κ ≤ 1 := (div_le_one hκpos).mpr hκ
  apply le_antisymm
  · apply iSup_le
    intro w
    simp
  · simpa [quadraticMultiplier] using quadratic_distance_lower κ 1 hκpos hs le_rfl []

theorem E_nil {κ : ℝ} (hκ : 1 ≤ κ) : E κ [] = 1 := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hs : 1/κ ≤ 1 := (div_le_one hκpos).mpr hκ
  apply le_antisymm
  · apply iSup_le
    intro w
    rw [value_error_nil hκpos]
    simp
  · simpa [quadraticMultiplier] using quadratic_value_lower κ 1 hκpos hs le_rfl []

theorem multiplier_of_nonpos {s : ℝ} (hs : 0 ≤ s) (h : List ℝ)
    (hh : ∀ a ∈ h, a ≤ 0) : 1 ≤ quadraticMultiplier s h := by
  induction h with
  | nil => simp [quadraticMultiplier]
  | cons a h ih =>
    have ha : a ≤ 0 := hh a (by simp)
    have hp : 1 ≤ quadraticMultiplier s h := ih (fun b hb => hh b (by simp [hb]))
    have hf : 1 ≤ 1-s*a := by nlinarith
    simpa [quadraticMultiplier] using one_le_mul_of_one_le_of_one_le hf hp

theorem nonpositive_schedule_lower {κ : ℝ} (hκ : 1 ≤ κ) (h : List ℝ)
    (hh : ∀ a ∈ h, a ≤ 0) : 1 ≤ D κ h ∧ 1 ≤ E κ h := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hs : 1/κ ≤ 1 := (div_le_one hκpos).mpr hκ
  have hp := multiplier_of_nonpos (show 0 ≤ 1/κ by positivity) h hh
  have hbound : (1 : ℝ) ≤ quadraticMultiplier (1/κ) h ^ 2 := by nlinarith
  have he : (1 : ENNReal) ≤ ENNReal.ofReal (quadraticMultiplier (1/κ) h ^ 2) := by
    simpa using ENNReal.ofReal_le_ofReal hbound
  exact ⟨he.trans (quadratic_distance_lower κ (1/κ) hκpos le_rfl hs h),
    he.trans (quadratic_value_lower κ (1/κ) hκpos le_rfl hs h)⟩

end
end StrongSilver
