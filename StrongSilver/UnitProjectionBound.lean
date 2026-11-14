-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.AttachmentNormalization

namespace StrongSilver
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem unit_projection_of_inner_bound {E z : V} {K : ℝ} (hE : E ≠ 0)
    (hb : |inner ℝ E z| ≤ ‖E‖*K) : |inner ℝ (unitDirection E) z| ≤ K := by
  rw [unitDirection,real_inner_smul_left,abs_mul,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg E))]
  have hh := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (norm_nonneg E))
  rwa [← mul_assoc,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hE),one_mul] at hh

end
end StrongSilver
