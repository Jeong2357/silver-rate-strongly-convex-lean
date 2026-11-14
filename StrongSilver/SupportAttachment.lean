-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SupportTransport

namespace StrongSilver.SupportFamily
noncomputable section
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] {ι κ : Type*}
set_option maxHeartbeats 1000000

theorem attached_support_at_retained (F : SupportFamily ι W) (G : SupportFamily κ V)
    {u : W} {v : V} (hu : inner ℝ u u = 1) (hv : inner ℝ v v = 1)
    {s a : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hnew : ∀ i, inner ℝ u (F.g i) ≤ 0) (hold : ∀ j, 0 ≤ inner ℝ v (G.z j)) (i : ι) (j : κ) :
    s^2*F.d i-s^2*a+inner ℝ (attachmentMap u v s (F.g i))
      (retainedMap (W := W) (G.z j)-attachmentMap u v s (F.z i)) ≤ 0 := by
  rw [inner_sub_right,attachment_retained_inner,attachment_inner hu hv]
  have hplane := mul_le_mul_of_nonneg_left (F.origin i) (sq_nonneg s)
  have hcross := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos hs (hnew i)) (hold j)
  have ha' := mul_nonneg (sq_nonneg s) ha
  linarith only [hplane,hcross,ha']

theorem retained_support_at_attached (F : SupportFamily ι W) (G : SupportFamily κ V)
    (u : W) (v : V) (s Q η : ℝ)
    (hpositive : ∀ j, 0 ≤ inner ℝ v (G.g j)) (hgate : G.Gate (Q • v) η)
    (hproject : ∀ i, s*inner ℝ u (F.z i) ≤ η*Q) (i : ι) (j : κ) :
    G.d j+inner ℝ (retainedMap (W := W) (G.g j))
      (attachmentMap u v s (F.z i)-retainedMap (W := W) (G.z j)) ≤ 0 := by
  rw [inner_sub_right,retained_inner]
  have he : inner ℝ (retainedMap (W := W) (G.g j)) (attachmentMap u v s (F.z i)) =
      s*inner ℝ u (F.z i)*inner ℝ v (G.g j) := by
    rw [real_inner_comm,attachment_retained_inner]
  rw [he]
  have hh := hgate j
  rw [inner_sub_right,real_inner_smul_right,real_inner_smul_right,real_inner_comm v (G.g j)] at hh
  have hm := mul_le_mul_of_nonneg_right (hproject i) (hpositive j)
  nlinarith only [hh,hm]

/-- An explicit support-preserving attachment in a finite dimensional extension.
All geometric and gate conditions used by the construction are displayed. -/
def attach (F : SupportFamily ι W) (G : SupportFamily κ V)
    {u : W} {v : V} (hu : inner ℝ u u = 1) (hv : inner ℝ v v = 1)
    {s a Q η : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) (hfloor : ∀ i, a ≤ F.d i)
    (hnew : ∀ i, inner ℝ u (F.g i) ≤ 0)
    (holdz : ∀ j, 0 ≤ inner ℝ v (G.z j)) (holdg : ∀ j, 0 ≤ inner ℝ v (G.g j))
    (hgate : G.Gate (Q • v) η) (hproject : ∀ i, s*inner ℝ u (F.z i) ≤ η*Q) :
    SupportFamily (ι ⊕ κ) (AttachmentSpace V W) :=
  (F.attached hu hv s).glue G.retained (s^2*a) (mul_nonneg (sq_nonneg s) ha)
    (fun i => mul_le_mul_of_nonneg_left (hfloor i) (sq_nonneg s))
    (fun i j => attached_support_at_retained F G hu hv hs ha hnew holdz i j)
    (fun j i => by
      simpa only [attached,retained,transport,one_mul] using
        retained_support_at_attached F G u v s Q η holdg hgate hproject i j)

end
end StrongSilver.SupportFamily
