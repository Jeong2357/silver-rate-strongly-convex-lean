-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SupportTransport
import StrongSilver.UnitProjectionBound

namespace StrongSilver
noncomputable section
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] {ι : Type*}
set_option maxHeartbeats 1800000

/-- The retained finite supporting data inequalities (4.18). -/
structure FourPhaseSuffixBounds (F : SupportFamily ι V) (Y : V) (H Z : ℝ) : Prop where
  source_nonzero : Y ≠ 0
  scale_positive : 0 < H
  offset_nonnegative : 0 ≤ Z
  point_positive : ∀ i, 0 ≤ inner ℝ Y (F.z i)
  slope_positive : ∀ i, 0 ≤ inner ℝ Y (F.g i)
  slope_upper : ∀ i, inner ℝ Y (F.g i) ≤ (11/(10*H))*‖Y‖^2
  height_lower : ∀ i, max (inner ℝ Y (F.z i)-Z*‖Y‖^2) 0/(8*H) ≤ F.d i

namespace FourPhaseSuffixBounds

theorem positive_at {F : SupportFamily ι V} {Y : V} {H Z : ℝ} (B : FourPhaseSuffixBounds F Y H Z) :
    F.PositiveAt Y := ⟨B.point_positive,B.slope_positive⟩

/-- Every recorded supporting plane satisfies the ray upper estimate
used to compare it with the four new affine planes. -/
theorem ray_plane_upper {F : SupportFamily ι V} {Y : V} {H Z : ℝ} (B : FourPhaseSuffixBounds F Y H Z)
    (s : ℝ) (i : ι) :
    F.d i+inner ℝ (F.g i) (s • Y-F.z i) ≤ (11/(10*H))*‖Y‖^2*max s 0 := by
  have ho := F.origin i
  rw [inner_sub_right,real_inner_smul_right,real_inner_comm Y (F.g i)]
  by_cases hs : 0 ≤ s
  · rw [max_eq_left hs]
    have hh := mul_le_mul_of_nonneg_left (B.slope_upper i) hs
    nlinarith only [hh,ho]
  · rw [max_eq_right (le_of_not_ge hs),mul_zero]
    have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs) (B.slope_positive i)
    nlinarith only [hh,ho]

theorem transport {F : SupportFamily ι V} {Y : V} {H Z c : ℝ} (B : FourPhaseSuffixBounds F Y H Z)
    (T : V →ₗ[ℝ] W) (hc : 0 < c) (hT : ∀ x y, inner ℝ (T x) (T y) = c*inner ℝ x y) :
    FourPhaseSuffixBounds (F.transport T c hc.le hT) (T Y) H Z := by
  have hnorm : ‖T Y‖^2 = c*‖Y‖^2 := by
    simpa only [real_inner_self_eq_norm_sq] using hT Y Y
  have hY : 0 < ‖Y‖^2 := sq_pos_of_pos (norm_pos_iff.mpr B.source_nonzero)
  have hTY : T Y ≠ 0 := by
    intro hz
    have hh := mul_pos hc hY
    rw [hz,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hnorm
    nlinarith only [hnorm,hh]
  refine ⟨hTY,B.scale_positive,B.offset_nonnegative,?_,?_,?_,?_⟩
  · intro i
    change 0 ≤ inner ℝ (T Y) (T (F.z i))
    rw [hT]
    exact mul_nonneg hc.le (B.point_positive i)
  · intro i
    change 0 ≤ inner ℝ (T Y) (T (F.g i))
    rw [hT]
    exact mul_nonneg hc.le (B.slope_positive i)
  · intro i
    change inner ℝ (T Y) (T (F.g i)) ≤ _
    rw [hT,hnorm]
    have hh := mul_le_mul_of_nonneg_left (B.slope_upper i) hc.le
    nlinarith only [hh]
  · intro i
    change max (inner ℝ (T Y) (T (F.z i))-Z*‖T Y‖^2) 0/(8*H) ≤ c*F.d i
    rw [hT,hnorm]
    have he : c*inner ℝ Y (F.z i)-Z*(c*‖Y‖^2) = c*(inner ℝ Y (F.z i)-Z*‖Y‖^2) := by ring
    rw [he,← mul_zero c,← mul_max_of_nonneg _ _ hc.le]
    have hh := mul_le_mul_of_nonneg_left (B.height_lower i) hc.le
    linear_combination hh

end FourPhaseSuffixBounds
end
end StrongSilver
