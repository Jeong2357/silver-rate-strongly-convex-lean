-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SupportTransport
import StrongSilver.EpigraphSupportFamily
import StrongSilver.SubgraphDomain

namespace StrongSilver
open Complex
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι κ : Type*}
set_option maxHeartbeats 1000000

theorem complex_I_inner_self : inner ℝ Complex.I Complex.I = 1 := by
  simp only [complex_inner_coordinates,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_add]

theorem plane_attachment_cross (f : V) (z : ℂ) (y : V) :
    inner ℝ (attachmentMap Complex.I f 1 z) (retainedMap (W := ℂ) y) =
      inner ℝ z (⟨0,inner ℝ f y⟩ : ℂ) := by
  rw [attachment_retained_inner]
  simp only [complex_inner_coordinates,Complex.I_re,Complex.I_im,zero_mul,one_mul,mul_zero,zero_add]

theorem plane_attachment_compatibility (P : Moreau.Epigraph ℂ) (F : SupportFamily ι ℂ) (G : SupportFamily κ V)
    (f : V) (hf : inner ℝ f f = 1) (hsupport : ∀ i, Moreau.Supports P (F.z i) (F.d i) (F.g i))
    (hzero : ∀ j, ((⟨0,inner ℝ f (G.z j)⟩ : ℂ),0) ∈ P.carrier)
    (hold : ∀ i j, G.d j+(F.z i).im*inner ℝ f (G.g j)-inner ℝ (G.g j) (G.z j) ≤ F.d i) :
    let T := attachmentMap Complex.I f 1
    let Fi := F.transport T 1 zero_le_one (fun x y => by
      simpa only [one_pow,one_mul] using attachment_inner complex_I_inner_self hf 1 x y)
    let Gi := G.retained (W := ℂ)
    (∀ i j, Fi.d i+inner ℝ (Fi.g i) (Gi.z j-Fi.z i) ≤ Gi.d j) ∧
    (∀ j i, Gi.d j+inner ℝ (Gi.g j) (Fi.z i-Gi.z j) ≤ Fi.d i) := by
  dsimp only
  constructor
  · intro i j
    have hh := (hsupport i).2 _ (hzero j)
    change 1*F.d i+inner ℝ (attachmentMap Complex.I f 1 (F.g i))
      (retainedMap (W := ℂ) (G.z j)-attachmentMap Complex.I f 1 (F.z i)) ≤ 1*G.d j
    rw [one_mul,one_mul,inner_sub_right,plane_attachment_cross,attachment_inner complex_I_inner_self hf]
    simp only [one_pow,one_mul]
    rw [inner_sub_right] at hh
    exact hh.trans (G.nonnegative j)
  · intro j i
    change 1*G.d j+inner ℝ (retainedMap (W := ℂ) (G.g j))
      (attachmentMap Complex.I f 1 (F.z i)-retainedMap (W := ℂ) (G.z j)) ≤ 1*F.d i
    rw [one_mul,one_mul,inner_sub_right,retained_inner,real_inner_comm,plane_attachment_cross]
    simp only [complex_inner_coordinates,mul_zero,zero_add]
    nlinarith only [hold i j]

end
end StrongSilver
