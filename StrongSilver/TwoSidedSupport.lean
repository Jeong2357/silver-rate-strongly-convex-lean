-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SupportAttachment

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 1000000

theorem product_le_of_abs_le {x y K Z : ℝ} (hx : |x| ≤ K) (hy : |y| ≤ Z) : x*y ≤ K*Z := by
  have hK : 0 ≤ K := (abs_nonneg _).trans hx
  have hh := mul_le_mul hx hy (abs_nonneg _) hK
  rw [← abs_mul] at hh
  exact (le_abs_self _).trans hh

namespace SupportFamily
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] {ι κ : Type*}

theorem two_sided_attached_support (F : SupportFamily ι W) (G : SupportFamily κ V)
    {u : W} {v : V} (hu : inner ℝ u u = 1) (hv : inner ℝ v v = 1)
    {s d K Z : ℝ} (hs : 0 ≤ s) (hcost : s*K*Z ≤ s^2*d)
    (hnew : ∀ i, |inner ℝ u (F.g i)| ≤ K) (hold : ∀ j, |inner ℝ v (G.z j)| ≤ Z)
    (i : ι) (j : κ) :
    s^2*(F.d i-d)+inner ℝ (attachmentMap u v s (F.g i))
      (retainedMap (W := W) (G.z j)-attachmentMap u v s (F.z i)) ≤ G.d j := by
  rw [inner_sub_right,attachment_retained_inner,attachment_inner hu hv]
  have hc := mul_le_mul_of_nonneg_left (product_le_of_abs_le (hnew i) (hold j)) hs
  have hor := mul_le_mul_of_nonneg_left (F.origin i) (sq_nonneg s)
  nlinarith only [hc,hor,hcost,G.nonnegative j]

theorem two_sided_retained_support (F : SupportFamily ι W) (G : SupportFamily κ V)
    {u : W} {v : V} {s d Ja C H : ℝ} (hs : 0 ≤ s)
    (hcost : s*C*H ≤ s^2*(Ja-d)) (hfloor : ∀ i, Ja ≤ F.d i)
    (hnew : ∀ i, |inner ℝ u (F.z i)| ≤ C) (hold : ∀ j, |inner ℝ v (G.g j)| ≤ H)
    (j : κ) (i : ι) :
    G.d j+inner ℝ (retainedMap (W := W) (G.g j))
      (attachmentMap u v s (F.z i)-retainedMap (W := W) (G.z j)) ≤ s^2*(F.d i-d) := by
  rw [inner_sub_right,retained_inner,real_inner_comm (attachmentMap u v s (F.z i)),attachment_retained_inner]
  have hc := mul_le_mul_of_nonneg_left (product_le_of_abs_le (hnew i) (hold j)) hs
  have hf := mul_le_mul_of_nonneg_left (hfloor i) (sq_nonneg s)
  nlinarith only [hc,hf,hcost,G.origin j]

end SupportFamily
end
end StrongSilver
