-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SupportTransport

namespace StrongSilver.SupportFamily
noncomputable section
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] {ι κ : Type*}
set_option maxHeartbeats 1000000

theorem shifted_gate (F : SupportFamily ι V) {X : V} {a G : ℝ} (ha : 0 ≤ a) (hG : 0 < G)
    (hfloor : ∀ i, a ≤ F.d i) (hcap : ∀ i, inner ℝ X (F.g i) ≤ G) :
    (F.shifted a ha hfloor).Gate X (a/G) := by
  intro i
  change F.d i-a+inner ℝ (F.g i) ((a/G) • X-F.z i) ≤ 0
  rw [inner_sub_right,real_inner_smul_right,real_inner_comm X (F.g i)]
  have hm := mul_le_mul_of_nonneg_left (hcap i) (div_nonneg ha hG.le)
  rw [div_mul_cancel₀ a hG.ne'] at hm
  linarith only [F.origin i,hm]

theorem transport_gate (F : SupportFamily ι V) (T : V →ₗ[ℝ] W) (c : ℝ) (hc : 0 ≤ c)
    (hT : ∀ x y, inner ℝ (T x) (T y) = c*inner ℝ x y) {X : V} {η : ℝ}
    (hg : F.Gate X η) : (F.transport T c hc hT).Gate (T X) η := by
  intro i
  change c*F.d i+inner ℝ (T (F.g i)) (η • T X-T (F.z i)) ≤ 0
  rw [← map_smul,← map_sub,hT]
  have hm := mul_nonpos_of_nonneg_of_nonpos hc (hg i)
  simpa only [mul_add,mul_zero] using hm

theorem retained_gate_at_orthogonal (F : SupportFamily ι V) (u : W) (v : V) (s η : ℝ) {X : W}
    (hX : inner ℝ u X = 0) : (F.retained (W := W)).Gate (attachmentMap u v s X) η := by
  intro i
  change 1*F.d i+inner ℝ (retainedMap (W := W) (F.g i))
    (η • attachmentMap u v s X-retainedMap (W := W) (F.z i)) ≤ 0
  rw [one_mul,inner_sub_right,real_inner_smul_right,retained_inner]
  have hz : inner ℝ (retainedMap (W := W) (F.g i)) (attachmentMap u v s X) = 0 := by
    rw [real_inner_comm,attachment_source_orthogonal v s hX]
  rw [hz,mul_zero]
  linarith only [F.origin i]

theorem sum_gate (F : SupportFamily ι V) (G : SupportFamily κ V)
    (hFG : ∀ i j, F.d i+inner ℝ (F.g i) (G.z j-F.z i) ≤ G.d j)
    (hGF : ∀ j i, G.d j+inner ℝ (G.g j) (F.z i-G.z j) ≤ F.d i)
    {X : V} {η : ℝ} (hF : F.Gate X η) (hG : G.Gate X η) : (F.sum G hFG hGF).Gate X η := by
  intro i
  cases i with | inl i => exact hF i | inr j => exact hG j

/-- A nonnegative supporting height converts a linear source estimate into the
positive-part height bound used in (3.17). -/
theorem positive_part_height (F : SupportFamily ι V) {X : V} {M Z : ℝ} (hM : 0 < M)
    (hlinear : ∀ i, inner ℝ X (F.z i)-Z*‖X‖^2 ≤ M*F.d i) (i : ι) :
    max (inner ℝ X (F.z i)-Z*‖X‖^2) 0/M ≤ F.d i := by
  apply (div_le_iff₀ hM).mpr
  exact max_le (by nlinarith only [hlinear i]) (mul_nonneg (F.nonnegative i) hM.le)

end
end StrongSilver.SupportFamily
