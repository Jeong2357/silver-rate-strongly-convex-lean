-- SPDX-License-Identifier: GPL-3.0-only
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

namespace StrongSilver
noncomputable section
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
set_option maxHeartbeats 1000000

abbrev AttachmentSpace (V W : Type*) := WithLp 2 (V × W)

def retainedMap : V →ₗ[ℝ] AttachmentSpace V W where
  toFun x := WithLp.toLp 2 (x,0)
  map_add' x y := by apply WithLp.ofLp_injective 2; simp only [WithLp.ofLp_add,WithLp.ofLp_toLp,Prod.mk_add_mk,add_zero]
  map_smul' a x := by apply WithLp.ofLp_injective 2; simp only [WithLp.ofLp_smul,WithLp.ofLp_toLp,Prod.smul_mk,smul_zero,RingHom.id_apply]

/-- Align a local endpoint direction with the retained source direction, while
placing its orthogonal complement in fresh coordinates. -/
def attachmentMap (u : W) (v : V) (s : ℝ) : W →ₗ[ℝ] AttachmentSpace V W where
  toFun x := WithLp.toLp 2 ((s*inner ℝ u x) • v,s • (x-(inner ℝ u x) • u))
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    simp only [WithLp.ofLp_add,WithLp.ofLp_toLp,inner_add_right]
    apply Prod.ext <;> dsimp only [Prod.fst_add,Prod.snd_add] <;> module
  map_smul' a x := by
    apply WithLp.ofLp_injective 2
    simp only [WithLp.ofLp_smul,WithLp.ofLp_toLp,real_inner_smul_right,RingHom.id_apply]
    apply Prod.ext <;> dsimp only [Prod.smul_fst,Prod.smul_snd] <;> module

theorem retained_inner (x y : V) :
    inner ℝ (retainedMap (W := W) x) (retainedMap (W := W) y) = inner ℝ x y := by
  change inner ℝ x y+inner ℝ (0 : W) 0 = inner ℝ x y
  rw [inner_zero_left,add_zero]

theorem attachment_inner {u : W} {v : V} (hu : inner ℝ u u = 1) (hv : inner ℝ v v = 1)
    (s : ℝ) (x y : W) :
    inner ℝ (attachmentMap u v s x) (attachmentMap u v s y) = s^2*inner ℝ x y := by
  change inner ℝ ((s*inner ℝ u x) • v) ((s*inner ℝ u y) • v)+
    inner ℝ (s • (x-(inner ℝ u x) • u)) (s • (y-(inner ℝ u y) • u)) = _
  simp only [real_inner_smul_left,real_inner_smul_right,inner_sub_left,inner_sub_right,hu,hv]
  rw [real_inner_comm x u]
  ring

theorem attachment_retained_inner (u : W) (v : V) (s : ℝ) (x : W) (y : V) :
    inner ℝ (attachmentMap u v s x) (retainedMap (W := W) y) =
      s*inner ℝ u x*inner ℝ v y := by
  change inner ℝ ((s*inner ℝ u x) • v) y+inner ℝ (s • (x-(inner ℝ u x) • u)) 0 = _
  rw [real_inner_smul_left,inner_zero_right,add_zero]

theorem attachment_source_orthogonal {u : W} (v : V) (s : ℝ) {x : W}
    (hx : inner ℝ u x = 0) (y : V) :
    inner ℝ (attachmentMap u v s x) (retainedMap (W := W) y) = 0 := by
  rw [attachment_retained_inner,hx,mul_zero,zero_mul]

theorem attachment_endpoint {u : W} (hu : inner ℝ u u = 1) (v : V) (s B : ℝ) :
    attachmentMap u v s (B • u) = retainedMap (W := W) ((s*B) • v) := by
  apply WithLp.ofLp_injective 2
  change ((s*inner ℝ u (B • u)) • v,s • (B • u-(inner ℝ u (B • u)) • u)) = ((s*B) • v,0)
  rw [real_inner_smul_right,hu,mul_one,sub_self,smul_zero]

theorem attachment_norm_sq {u : W} {v : V} (hu : inner ℝ u u = 1) (hv : inner ℝ v v = 1)
    (s : ℝ) (x : W) : ‖attachmentMap u v s x‖^2 = s^2*‖x‖^2 := by
  rw [← real_inner_self_eq_norm_sq,attachment_inner hu hv,real_inner_self_eq_norm_sq]

def retainedIsometry : V →ₗᵢ[ℝ] AttachmentSpace V W where
  toLinearMap := retainedMap
  norm_map' x := by
    have hh := retained_inner (W := W) x x
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hh
    nlinarith only [hh,norm_nonneg x,norm_nonneg (retainedMap (W := W) x)]

end
end StrongSilver
