-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace StrongSilver
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem firm_map_inward_halfspace (F : V → V)
    (hfirm : ∀ x y, ‖F x-F y‖^2 ≤ inner ℝ (F x-F y) (x-y))
    {x p N : V} {t : ℝ} (ht : 0 ≤ t) (hxp : x-p = t • N) (hp : inner ℝ N (F p) = 0) :
    0 ≤ inner ℝ N (F x) := by
  by_cases ht0 : t = 0
  · have he : x = p := sub_eq_zero.mp (by simpa only [ht0,zero_smul] using hxp)
    rw [he,hp]
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hh := hfirm x p
  rw [hxp,real_inner_smul_right,inner_sub_left,
    real_inner_comm N (F x),real_inner_comm N (F p),hp,sub_zero] at hh
  have hnorm := sq_nonneg ‖F x-F p‖
  nlinarith only [hh,hnorm,htpos]

end
end StrongSilver
