-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarSupportLower
import StrongSilver.PlanarTrajectoryBounds

namespace StrongSilver
open Set Real Filter Complex
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem eventually_log_le_small_power : ∀ᶠ A : ℝ in atTop, Real.log A ≤ A^((1 : ℝ)/20) := by
  have ht : Tendsto (fun A : ℝ => Real.log A/A^((1 : ℝ)/20)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/20)).tendsto_div_nhds_zero
  filter_upwards [eventually_gt_atTop (1 : ℝ),(tendsto_order.1 ht).2 1 zero_lt_one] with A hA hh
  exact ((div_lt_one (Real.rpow_pos_of_pos (zero_lt_one.trans hA) _)).mp hh).le

namespace PlanarBoundaryCertificate
variable {A μ : ℝ} (C : PlanarBoundaryCertificate A μ)
include C

theorem head_radius_bound : planarRadius A 0 ≤ 1+6*planarSlopeScale A :=
  planar_head_radius_upper C.epsilon_pos C.scale_pos C.epsilon_slope C.scale_le

theorem head_size_bound (hlog : Real.log A ≤ A^((1 : ℝ)/20)) :
    C.right+C.J 0 ≤ 35*A^((1 : ℝ)/2) := by
  have hApos : 0 < A := zero_lt_one.trans C.large
  have hJ := C.bound 0 ⟨le_rfl,C.angle_pos.le⟩
  have hJ0 : 0 ≤ C.J 0 := C.nonnegative 0 ⟨le_rfl,C.angle_pos.le⟩
  have hr := C.head_radius_bound
  have hk := C.scale_le
  have hhalf : 1 ≤ A^((1 : ℝ)/2) := Real.one_le_rpow C.large.le (by norm_num)
  have hpow : A^((9 : ℝ)/20) ≤ A^((1 : ℝ)/2) :=
    Real.rpow_le_rpow_of_exponent_le C.large.le (by norm_num)
  have hprod : A^((9 : ℝ)/20)*A^((1 : ℝ)/20) = A^((1 : ℝ)/2) := by
    rw [← Real.rpow_add hApos]
    congr 1
    norm_num
  have hquot : C.J 0/planarSlopeScale A = C.J 0*Real.log A/100 := by
    unfold planarSlopeScale
    field_simp
  have hm := mul_le_mul hJ hlog (Real.log_pos C.large).le (by positivity : 0 ≤ 32*A^((9 : ℝ)/20))
  have hfactor : 32*A^((9 : ℝ)/20)*A^((1 : ℝ)/20) = 32*A^((1 : ℝ)/2) := by rw [← hprod]; ring
  rw [hfactor] at hm
  rw [C.right_eq_head,hquot]
  nlinarith only [hm,hr,hk,hJ,hpow,hhalf]

theorem body_norm_maximum : (∀ v ∈ C.body.carrier, ‖v‖ ≤ planarRadius A 0) ∧
    ∃ v ∈ C.body.carrier, ‖v‖ = planarRadius A 0 := by
  refine ⟨fun v hv => C.body_norm_bound hv,⟨(⟨planarRadius A 0,0⟩ : ℂ),C.body_head_mem,?_⟩⟩
  rw [← C.head_arc_eq,polarArc_norm (C.radius_pos 0).le]

end PlanarBoundaryCertificate

/-- The planar geometric construction has no unproved existence assumption. -/
theorem eventually_planar_construction : ∀ᶠ A : ℝ in atTop,
    ∀ μ : ℝ, 0 ≤ μ → μ*A ≤ 1 → ∃ C : PlanarBoundaryCertificate A μ,
      planarRadius A 0 ≤ 1+600/Real.log A ∧ C.right+C.J 0 ≤ 35*A^((1 : ℝ)/2) := by
  filter_upwards [eventually_exists_planar_boundary_certificate,eventually_planar_head_radius,
    eventually_log_le_small_power] with A hex hr hl
  intro μ hμ hμA
  obtain ⟨C⟩ := hex μ hμ hμA
  exact ⟨C,hr,C.head_size_bound hl⟩

end
end StrongSilver
