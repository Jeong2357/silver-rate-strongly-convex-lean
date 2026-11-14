-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseAxisAttachment
import StrongSilver.FourPhaseSuffixBounds

namespace StrongSilver.FourPhase
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type*}
set_option maxHeartbeats 2400000

/-- In the retained coordinates, a new point is exactly the source ray
with scalar coordinate given by its old-axis projection. -/
theorem retained_axisAttachment_plane {Y : V} (hY : Y ≠ 0) {K : ℝ} (hK : K ≠ 0)
    (z : Coordinates) (g w : V) (d : ℝ) :
    d+inner ℝ (retainedMap (W := Coordinates) g) (axisAttachment Y K z-retainedMap (W := Coordinates) w) =
    d+inner ℝ g ((inner ℝ axis z/K) • Y-w) := by
  rw [inner_sub_right,retained_inner,inner_sub_right,real_inner_smul_right]
  have hc : inner ℝ (retainedMap (W := Coordinates) g) (axisAttachment Y K z) =
      (inner ℝ axis z/K)*inner ℝ g Y := by
    calc
      _ = inner ℝ (axisAttachment Y K z) (retainedMap (W := Coordinates) g) := real_inner_comm _ _
      _ = (‖Y‖/K)*inner ℝ axis z*inner ℝ (unitDirection Y) g := attachment_retained_inner _ _ _ _ _
      _ = _ := by
        rw [unitDirection,real_inner_smul_left,real_inner_comm g Y]
        have hn := norm_ne_zero_iff.mpr hY
        field_simp
        <;> ring
  rw [hc]

/-- A numerical old-axis projection budget is sufficient for all retained
planes to lie below one new contact value. The budget is discharged from
the signed prefix-product estimates when a schedule is instantiated. -/
theorem retained_plane_at_new {F : SupportFamily ι V} {Y : V} {H Z T K d : ℝ}
    (B : FourPhaseSuffixBounds F Y H Z) (hT : 0 < T) (hK : 0 < K)
    (z : Coordinates) (j : ι)
    (hvalue : (11*T*K/(10*H))*max (inner ℝ axis z) 0 ≤ d) :
    F.d j+inner ℝ (retainedMap (W := Coordinates) (F.g j))
      (axisAttachment Y K z-retainedMap (W := Coordinates) (F.z j)) ≤ (‖Y‖/K)^2*(d/T) := by
  rw [retained_axisAttachment_plane B.source_nonzero hK.ne']
  have hh := B.ray_plane_upper (inner ℝ axis z/K) j
  have hm : max (inner ℝ axis z/K) 0 = max (inner ℝ axis z) 0/K := by
    simpa only [zero_div] using max_div_div_right hK.le (inner ℝ axis z) 0
  rw [hm] at hh
  have hp : 0 ≤ ‖Y‖^2/(K^2*T) := div_nonneg (sq_nonneg _) (mul_pos (sq_pos_of_pos hK) hT).le
  have hnum := mul_le_mul_of_nonneg_left hvalue hp
  have hH : H ≠ 0 := B.scale_positive.ne'
  have hleft : (‖Y‖^2/(K^2*T))*((11*T*K/(10*H))*max (inner ℝ axis z) 0) =
      (11/(10*H))*‖Y‖^2*(max (inner ℝ axis z) 0/K) := by
    field_simp
    <;> ring
  have hright : (‖Y‖^2/(K^2*T))*d = (‖Y‖/K)^2*(d/T) := by ring
  rw [hleft,hright] at hnum
  exact hh.trans hnum

end
end StrongSilver.FourPhase
