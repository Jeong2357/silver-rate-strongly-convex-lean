-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PlanarRootEntry
import StrongSilver.WorkingOrdinarySourceCap

namespace StrongSilver.LocalPhaseCertificate
open Real Filter Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2000000

theorem planar_start_lower_large_root {A μ b T e : ℝ} {h : List ℝ}
    (L : LocalPhaseCertificate A μ b T e h) (i : Fin h.length)
    (hroot : 2 ≤ h.get i) (hnegative : negativeMass h ≤ h.get i/16) : h.get i/8 ≤ ‖L.R‖ := by
  have hsmall := L.small_steps (h.get i) (List.get_mem h i)
  have hμroot := mul_le_mul_of_nonneg_left hroot L.mu_positive.le
  have hμ : μ ≤ 1/2 := by nlinarith only [hsmall,hμroot]
  have hμN := mul_le_mul_of_nonneg_left hnegative L.mu_positive.le
  have hcharge : μ*negativeMass h ≤ 1/4 := by nlinarith only [hμN,hsmall]
  exact L.planar_start_lower_at_root i (by linarith only [hroot]) hμ hcharge hnegative

end
end StrongSilver.LocalPhaseCertificate

namespace StrongSilver
open Real Filter Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 2000000

/-- The ordinary pad is eventually below the planar source norm when
an actual gap root is at least the working pivot scale and its original
negative-step mass is small. -/
theorem eventually_root_pad_le_planar_norm : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T e P : ℝ, ∀ h : List ℝ, ∀ L : LocalPhaseCertificate A μ b T e h,
    ∀ i : Fin h.length, A^((499 : ℝ)/500) ≤ h.get i → P ≤ A^((199 : ℝ)/200) →
    negativeMass h ≤ h.get i/16 → P ≤ ‖L.R‖ := by
  filter_upwards [eventually_gt_atTop (0:ℝ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 499/500)).eventually (eventually_ge_atTop (2:ℝ)),
    eventually_const_mul_power_le (by norm_num : (199:ℝ)/200 < 499/500) (8:ℝ)]
    with A hA htwo hpad
  intro μ b T e P h L i hroot hP hN
  have hR := L.planar_start_lower_large_root i (htwo.trans hroot) hN
  nlinarith only [hR,hroot,hP,hpad]

end
end StrongSilver
