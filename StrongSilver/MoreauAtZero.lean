-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.HingeRaySupport
import StrongSilver.MoreauFirm

namespace StrongSilver.Moreau
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]

theorem gradient_at_zero (P : Epigraph V) : gradient P 0 = 0 := by
  have hs := zero_support_of_zero_height P P.zero_mem
  have hh := (envelope_interpolates P 0 0 0 hs).1
  simpa only [add_zero] using hh

theorem proximal_at_zero (P : Epigraph V) : proximal P 0 = 0 := by
  have hh := gradient_at_zero P
  simpa only [gradient,zero_sub,neg_eq_zero] using hh

theorem gradient_inner_nonnegative (P : Epigraph V) (x : V) : 0 ≤ inner ℝ (gradient P x) x := by
  have hh := gradient_firm P x 0
  rw [gradient_at_zero P,sub_zero,sub_zero] at hh
  exact (sq_nonneg _).trans hh

theorem proximal_norm_le (P : Epigraph V) (x : V) : ‖proximal P x‖ ≤ ‖x‖ := by
  have hh := proximal_lipschitz P x 0
  rwa [proximal_at_zero P,sub_zero,sub_zero] at hh

end
end StrongSilver.Moreau
