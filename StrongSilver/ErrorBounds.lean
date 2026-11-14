-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Schedules
import Mathlib.Order.Interval.Set.Infinite

namespace StrongSilver
noncomputable section

def growthFactor (h : List ℝ) : ℝ := (h.map (fun a => 1+|a|)).prod

theorem growthFactor_nonneg (h : List ℝ) : 0 ≤ growthFactor h := by
  apply List.prod_nonneg
  intro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  positivity

theorem norm_update_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (g : V → V) (xstar : V) (hzero : g xstar = 0)
    (hl : ∀ x y, ‖g x-g y‖ ≤ ‖x-y‖) (x : V) (a : ℝ) :
    ‖x-a • g x-xstar‖ ≤ (1+|a|)*‖x-xstar‖ := by
  have hx : ‖g x‖ ≤ ‖x-xstar‖ := by simpa only [hzero,sub_zero] using hl x xstar
  have he : x-a • g x-xstar = (x-xstar)-a • g x := by abel
  rw [he]
  calc
    _ ≤ ‖x-xstar‖+‖a • g x‖ := norm_sub_le _ _
    _ = ‖x-xstar‖ + |a| * ‖g x‖ := by rw [norm_smul,Real.norm_eq_abs]
    _ ≤ (1+|a|)*‖x-xstar‖ := by
      nlinarith only [mul_le_mul_of_nonneg_left hx (abs_nonneg a)]

theorem iterate_norm_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (h : List ℝ) (g : V → V) (xstar : V) (hzero : g xstar = 0)
    (hl : ∀ x y, ‖g x-g y‖ ≤ ‖x-y‖) (x : V) :
    ‖iterate h g x-xstar‖ ≤ growthFactor h*‖x-xstar‖ := by
  induction h generalizing x with
  | nil => simp [growthFactor]
  | cons a h ih =>
    rw [iterate_cons]
    have hu := norm_update_le g xstar hzero hl x a
    calc
      _ ≤ growthFactor h*‖x-a • g x-xstar‖ := ih _
      _ ≤ growthFactor h*((1+|a|)*‖x-xstar‖) :=
        mul_le_mul_of_nonneg_left hu (growthFactor_nonneg h)
      _ = growthFactor (a::h)*‖x-xstar‖ := by simp [growthFactor]; ring

theorem distance_error_upper {κ : ℝ} (h : List ℝ) (w : Instance κ) :
    distanceError h w ≤ growthFactor h ^ 2 := by
  have hzero := gradient_zero_at_min w.f w.g w.minimizer (w.admissible.gradient _) w.minimal
  have hb := iterate_norm_le h w.g w.minimizer hzero w.admissible.smooth w.start
  have hs : 0 < ‖w.start-w.minimizer‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr w.distinct))
  have hp := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (growthFactor_nonneg h) (norm_nonneg _))).mpr hb
  apply (div_le_iff₀ hs).mpr
  simpa only [mul_pow] using hp

theorem D_upper (κ : ℝ) (h : List ℝ) : D κ h ≤ ENNReal.ofReal (growthFactor h ^ 2) := by
  apply iSup_le
  intro w
  exact ENNReal.ofReal_le_ofReal (distance_error_upper h w)

theorem D_ne_top (κ : ℝ) (h : List ℝ) : D κ h ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (D_upper κ h)

theorem value_error_le_kappa_distance_error {κ : ℝ} (hκ : 0 < κ) (h : List ℝ) (w : Instance κ) :
    valueError h w ≤ κ*distanceError h w := by
  have hl := strong_lower_at_min w.admissible.strong_convex w.minimal w.start
  have hu := smooth_upper_at_min w.f w.g (iterate h w.g w.start) w.minimizer
    w.admissible.gradient w.admissible.smooth w.minimal
  have hv := value_gap_pos hκ w
  have hs : 0 < ‖w.start-w.minimizer‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr w.distinct))
  have he : 0 ≤ w.f (iterate h w.g w.start)-w.f w.minimizer := sub_nonneg.mpr (w.minimal _)
  have hb : ‖w.start-w.minimizer‖^2 ≤ 2*κ*(w.f w.start-w.f w.minimizer) := by
    have hd : ‖w.start-w.minimizer‖^2/(2*κ) ≤ w.f w.start-w.f w.minimizer := by
      convert hl using 1 <;> ring
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < 2*κ)).mp hd
  have hp : (w.f (iterate h w.g w.start)-w.f w.minimizer)*‖w.start-w.minimizer‖^2 ≤
      (κ*‖iterate h w.g w.start-w.minimizer‖^2)*(w.f w.start-w.f w.minimizer) := by
    have h1 := mul_le_mul_of_nonneg_left hb he
    have h2 := mul_le_mul_of_nonneg_left hu (mul_nonneg hκ.le hv.le)
    nlinarith only [h1,h2]
  change (w.f (iterate h w.g w.start)-w.f w.minimizer)/(w.f w.start-w.f w.minimizer) ≤
    κ*(‖iterate h w.g w.start-w.minimizer‖^2/‖w.start-w.minimizer‖^2)
  calc
    _ ≤ (κ*‖iterate h w.g w.start-w.minimizer‖^2)/‖w.start-w.minimizer‖^2 :=
      (div_le_div_iff₀ hv hs).mpr hp
    _ = _ := by ring

theorem E_le_kappa_D {κ : ℝ} (hκ : 0 < κ) (h : List ℝ) : E κ h ≤ ENNReal.ofReal κ*D κ h := by
  apply iSup_le
  intro w
  have he := ENNReal.ofReal_le_ofReal (value_error_le_kappa_distance_error hκ h w)
  rw [ENNReal.ofReal_mul hκ.le] at he
  exact he.trans (mul_le_mul' le_rfl (distance_error_le_D h w))

theorem E_ne_top {κ : ℝ} (hκ : 0 < κ) (h : List ℝ) : E κ h ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (D_ne_top κ h)) (E_le_kappa_D hκ h)

theorem exists_nonzero_quadratic {κ : ℝ} (hκ : 1 < κ) (h : List ℝ) :
    ∃ s : ℝ, 1/κ < s ∧ s < 1 ∧ quadraticMultiplier s h ≠ 0 := by
  classical
  have hκpos : 0 < κ := lt_trans zero_lt_one hκ
  have hinterval : 1/κ < 1 := (div_lt_one hκpos).mpr hκ
  let bad := (h.map (fun a => a⁻¹)).toFinset
  obtain ⟨s,hs,hnot⟩ := (Set.Ioo_infinite hinterval).exists_notMem_finset bad
  refine ⟨s,hs.1,hs.2,?_⟩
  unfold quadraticMultiplier
  apply List.prod_ne_zero
  intro hz
  obtain ⟨a,ha,he⟩ := List.mem_map.mp hz
  have ha0 : a ≠ 0 := by intro hz; simp [hz] at he
  have hsi : s = 1/a := (eq_div_iff ha0).mpr (by linarith)
  apply hnot
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨a,ha,by simpa only [one_div] using hsi.symm⟩

theorem errors_positive {κ : ℝ} (hκ : 1 < κ) (h : List ℝ) : 0 < D κ h ∧ 0 < E κ h := by
  obtain ⟨s,hs,hs1,hprod⟩ := exists_nonzero_quadratic hκ h
  have hκpos : 0 < κ := lt_trans zero_lt_one hκ
  have hsq : 0 < quadraticMultiplier s h ^ 2 := (sq_pos_iff).mpr hprod
  have he : 0 < ENNReal.ofReal (quadraticMultiplier s h ^ 2) := ENNReal.ofReal_pos.mpr hsq
  exact ⟨he.trans_le (quadratic_distance_lower κ s hκpos hs.le hs1.le h),
    he.trans_le (quadratic_value_lower κ s hκpos hs.le hs1.le h)⟩

end
end StrongSilver
