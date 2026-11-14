-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WedgeGeometry
import StrongSilver.FirmHalfspace
import StrongSilver.StrongMoreau

namespace StrongSilver
open Set Real Complex
noncomputable section
set_option maxHeartbeats 1000000

theorem wedge_upper_orthogonal (c s : ℝ) : inner ℝ (wedgeInward c s 0) (wedgeUpper c s) = 0 := by
  simp only [wedgeInward,ite_true,wedgeUpper,complex_inner_coordinates]
  ring

theorem wedge_lower_orthogonal (c s : ℝ) : inner ℝ (wedgeInward c s 1) (wedgeLower c s) = 0 := by
  norm_num [wedgeInward,wedgeLower,complex_inner_coordinates] <;> ring

theorem wedge_firm_invariant {c s : ℝ} (hc : 0 < c) (hs : 0 < s) (hsc : s ≤ c) (hu : c^2+s^2 = 1)
    (F : ℂ → ℂ) (hfirm : ∀ x y, ‖F x-F y‖^2 ≤ inner ℝ (F x-F y) (x-y))
    (hupper : ∀ t : ℝ, 0 ≤ t → ∃ a : ℝ, F (t • wedgeUpper c s) = a • wedgeUpper c s)
    (hlower : ∀ t : ℝ, 0 ≤ t → ∃ a : ℝ, F (t • wedgeLower c s) = a • wedgeLower c s)
    {x : ℂ} (hx : x ∈ wedgeCone c s) : F x ∈ wedgeCone c s := by
  intro i
  fin_cases i
  · have ht := wedge_upper_projection_nonnegative hc hs hsc hx
    obtain ⟨a,ha⟩ := hupper (inner ℝ (wedgeUpper c s) x) ht
    have hp : inner ℝ (wedgeInward c s 0) (F ((inner ℝ (wedgeUpper c s) x) • wedgeUpper c s)) = 0 := by
      rw [ha,real_inner_smul_right,wedge_upper_orthogonal,mul_zero]
    exact firm_map_inward_halfspace F hfirm (hx 0) (wedge_frame_upper hu x) hp
  · have ht := wedge_lower_projection_nonnegative hc hs hsc hx
    obtain ⟨a,ha⟩ := hlower (inner ℝ (wedgeLower c s) x) ht
    have hp : inner ℝ (wedgeInward c s 1) (F ((inner ℝ (wedgeLower c s) x) • wedgeLower c s)) = 0 := by
      rw [ha,real_inner_smul_right,wedge_lower_orthogonal,mul_zero]
    exact firm_map_inward_halfspace F hfirm (hx 1) (wedge_frame_lower hu x) hp

theorem wedge_active_face_tangent {c s : ℝ} (hc : 0 < c) (hs : 0 < s) (hsc : s ≤ c) (hu : c^2+s^2 = 1)
    (F : ℂ → ℂ)
    (hupper : ∀ t : ℝ, 0 ≤ t → ∃ a : ℝ, F (t • wedgeUpper c s) = a • wedgeUpper c s)
    (hlower : ∀ t : ℝ, 0 ≤ t → ∃ a : ℝ, F (t • wedgeLower c s) = a • wedgeLower c s)
    {x : ℂ} (hx : x ∈ wedgeCone c s) (i : Fin 2) (hface : wedgeForm c s i x = 0) :
    wedgeForm c s i (F x) = 0 := by
  fin_cases i
  · have ht := wedge_upper_projection_nonnegative hc hs hsc hx
    obtain ⟨a,ha⟩ := hupper (inner ℝ (wedgeUpper c s) x) ht
    have he : x = (inner ℝ (wedgeUpper c s) x) • wedgeUpper c s := by
      apply sub_eq_zero.mp
      rw [wedge_frame_upper hu x]
      change inner ℝ (wedgeInward c s 0) x = 0 at hface
      rw [hface,zero_smul]
    change inner ℝ (wedgeInward c s 0) (F x) = 0
    calc
      _ = inner ℝ (wedgeInward c s 0) (F ((inner ℝ (wedgeUpper c s) x) • wedgeUpper c s)) := congrArg (fun z : ℂ => inner ℝ (wedgeInward c s 0) (F z)) he
      _ = 0 := by rw [ha,real_inner_smul_right,wedge_upper_orthogonal,mul_zero]
  · have ht := wedge_lower_projection_nonnegative hc hs hsc hx
    obtain ⟨a,ha⟩ := hlower (inner ℝ (wedgeLower c s) x) ht
    have he : x = (inner ℝ (wedgeLower c s) x) • wedgeLower c s := by
      apply sub_eq_zero.mp
      rw [wedge_frame_lower hu x]
      change inner ℝ (wedgeInward c s 1) x = 0 at hface
      rw [hface,zero_smul]
    change inner ℝ (wedgeInward c s 1) (F x) = 0
    calc
      _ = inner ℝ (wedgeInward c s 1) (F ((inner ℝ (wedgeLower c s) x) • wedgeLower c s)) := congrArg (fun z : ℂ => inner ℝ (wedgeInward c s 1) (F z)) he
      _ = 0 := by rw [ha,real_inner_smul_right,wedge_lower_orthogonal,mul_zero]

end
end StrongSilver
