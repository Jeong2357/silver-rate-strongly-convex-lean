-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseAxisAttachment
import StrongSilver.FourPhaseQueryHeights
import StrongSilver.FourPhaseRetainedPlaneBound
import StrongSilver.FourPhaseSuffixBounds

namespace StrongSilver.FourPhase
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type*}
set_option maxHeartbeats 3000000

variable {x : Shape} (R : Regular x) {F : SupportFamily ι V} {Y : V} {H Z T K : ℝ}
    (B : FourPhaseSuffixBounds F Y H Z) (hT : 0 < T) (hK : 0 < K)
include R B hT hK

theorem first_new_plane_at_retained (hζ : K*Z ≤ x 7) (hslope : 8*H*a x ≤ T*K)
    (i : Fin 3) (z : Coordinates) (j : ι) :
    (‖Y‖/K)^2*(planeValue x i.castSucc z/T)+
      inner ℝ (axisAttachment Y K ((1/T) • slope x i.castSucc))
        (retainedMap (W := Coordinates) (F.z j)-axisAttachment Y K z) ≤ F.d j := by
  have hb : inner ℝ axis ((1/T) • slope x i.castSucc) = a x/T := by
    rw [real_inner_smul_right]
    have hi : inner ℝ axis (slope x i.castSucc) = a x := by
      exact (real_inner_comm _ _).trans (slope_axis i)
    rw [hi]; ring
  have hd : planeValue x i.castSucc z/T =
      inner ℝ ((1/T) • slope x i.castSucc) z-a x*x 7/T := by
    rw [real_inner_smul_left]; unfold planeValue; ring
  rw [hd,axisAttachment_plane_value B.source_nonzero hK.ne' _ _ _ hb]
  have hh := retained_affine_plane_bound (u := inner ℝ Y (F.z j)) (N := ‖Y‖^2)
    (sq_nonneg _) R.a_positive.le hT hK B.scale_positive hζ hslope (B.height_lower j)
  convert hh using 1 <;> ring

theorem last_new_plane_at_retained (hζ : 0 ≤ x 7) (z : Coordinates) (j : ι) :
    (‖Y‖/K)^2*(planeValue x 3 z/T)+
      inner ℝ (axisAttachment Y K ((1/T) • slope x 3))
        (retainedMap (W := Coordinates) (F.z j)-axisAttachment Y K z) ≤ F.d j := by
  have hb : inner ℝ axis ((1/T) • slope x 3) = (-1:ℝ)/T := by
    change inner ℝ axis ((1/T) • slope3 x) = _
    rw [slope3_axis,real_inner_smul_right,real_inner_smul_right,axis_unit]
    ring
  have hd : planeValue x 3 z/T = inner ℝ ((1/T) • slope x 3) z-a x*x 7/T := by
    rw [real_inner_smul_left]; unfold planeValue; ring
  rw [hd,axisAttachment_plane_value B.source_nonzero hK.ne' _ _ _ hb]
  have hh := retained_negative_axis_plane_bound (B.point_positive j) (sq_nonneg ‖Y‖)
    R.a_positive.le hζ hT hK (F.nonnegative j)
  convert hh using 1 <;> ring

/-- Every new plane lies below the retained contact value, so every old
value and subgradient can be kept in the common finite support family. -/
theorem new_plane_at_retained (hζ0 : 0 ≤ x 7) (hζ : K*Z ≤ x 7)
    (hslope : 8*H*a x ≤ T*K) (i : Fin 4) (z : Coordinates) (j : ι) :
    (‖Y‖/K)^2*(planeValue x i z/T)+
      inner ℝ (axisAttachment Y K ((1/T) • slope x i))
        (retainedMap (W := Coordinates) (F.z j)-axisAttachment Y K z) ≤ F.d j := by
  fin_cases i
  · exact first_new_plane_at_retained R B hT hK hζ hslope 0 z j
  · exact first_new_plane_at_retained R B hT hK hζ hslope 1 z j
  · exact first_new_plane_at_retained R B hT hK hζ hslope 2 z j
  · exact last_new_plane_at_retained R B hT hK hζ0 z j

end
end StrongSilver.FourPhase
