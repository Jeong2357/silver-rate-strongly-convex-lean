-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SupportProjection

namespace StrongSilver.CompactConvexBody
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]

theorem supportValue_norm_upper (K : CompactConvexBody V) {M : ℝ}
    (hM : ∀ v ∈ K.carrier, ‖v‖ ≤ M) (x : V) : K.supportValue x ≤ M*‖x‖ := by
  apply (K.supportValue_le _ _).mpr
  intro v hv
  exact (real_inner_le_norm x v).trans (by nlinarith only [hM v hv,norm_nonneg x])

theorem support_envelope_upper (K : CompactConvexBody V) (x : V) :
    Moreau.envelope K.supportEpigraph x ≤ K.supportValue x := by
  have hh := Moreau.minimizingPair_min K.supportEpigraph x (x,K.supportValue x)
    (show K.supportValue x ≤ K.supportValue x from le_rfl)
  simpa only [Moreau.objective,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_div,add_zero] using hh

theorem support_strong_growth (K : CompactConvexBody V) {μ M : ℝ} (hμ : μ ≤ 1)
    (hM : ∀ v ∈ K.carrier, ‖v‖ ≤ M) (x : V) :
    (μ/2)*‖x‖^2 ≤ stronglyConvexObjective μ (Moreau.envelope K.supportEpigraph) x ∧
    stronglyConvexObjective μ (Moreau.envelope K.supportEpigraph) x ≤
      (μ/2)*‖x‖^2+((1-μ)*M)*‖x‖ := by
  have he0 := Moreau.envelope_nonnegative K.supportEpigraph x
  have he := (K.support_envelope_upper x).trans (K.supportValue_norm_upper hM x)
  have hm := mul_nonneg (sub_nonneg.mpr hμ) he0
  have hu := mul_le_mul_of_nonneg_left he (sub_nonneg.mpr hμ)
  unfold stronglyConvexObjective
  constructor <;> nlinarith only [hm,hu]

end
end StrongSilver.CompactConvexBody
