-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SupportFamilies
import StrongSilver.OrthogonalAttachment

namespace StrongSilver.SupportFamily
noncomputable section
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] {ι κ : Type*}

def transport (F : SupportFamily ι V) (T : V →ₗ[ℝ] W) (c : ℝ) (hc : 0 ≤ c)
    (hT : ∀ x y, inner ℝ (T x) (T y) = c*inner ℝ x y) : SupportFamily ι W where
  z := fun i => T (F.z i)
  g := fun i => T (F.g i)
  d := fun i => c*F.d i
  nonnegative := fun i => mul_nonneg hc (F.nonnegative i)
  origin := by intro i; rw [hT]; exact mul_le_mul_of_nonneg_left (F.origin i) hc
  supports := by
    intro i j
    rw [← map_sub,hT]
    have hh := mul_le_mul_of_nonneg_left (F.supports i j) hc
    simpa only [mul_add] using hh

def retained (F : SupportFamily ι V) : SupportFamily ι (AttachmentSpace V W) :=
  F.transport retainedMap 1 zero_le_one (fun x y => by rw [retained_inner,one_mul])

def attached (F : SupportFamily ι W) {u : W} {v : V} (hu : inner ℝ u u = 1)
    (hv : inner ℝ v v = 1) (s : ℝ) : SupportFamily ι (AttachmentSpace V W) :=
  F.transport (attachmentMap u v s) (s^2) (sq_nonneg s) (attachment_inner hu hv s)

def PositiveAt (F : SupportFamily ι V) (Y : V) : Prop :=
  (∀ i, 0 ≤ inner ℝ Y (F.z i)) ∧ (∀ i, 0 ≤ inner ℝ Y (F.g i))

def Gate (F : SupportFamily ι V) (Y : V) (η : ℝ) : Prop :=
  ∀ i, F.d i+inner ℝ (F.g i) (η • Y-F.z i) ≤ 0

theorem gate_below (F : SupportFamily ι V) {Y : V} {η t : ℝ}
    (hpos : ∀ i, 0 ≤ inner ℝ Y (F.g i)) (hgate : F.Gate Y η) (ht : t ≤ η) (i : ι) :
    F.d i+inner ℝ (F.g i) (t • Y-F.z i) ≤ 0 := by
  have hh := hgate i
  have hm := mul_le_mul_of_nonneg_right ht (hpos i)
  rw [inner_sub_right,real_inner_smul_right,real_inner_comm Y (F.g i)] at hh ⊢
  linarith only [hh,hm]

end
end StrongSilver.SupportFamily
