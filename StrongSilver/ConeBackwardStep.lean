-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.DomainBackwardTrajectory

namespace StrongSilver
open Set
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]
set_option maxHeartbeats 1000000

theorem cone_normal_radial_orthogonal {S : Set V}
    (hcone : ∀ x ∈ S, ∀ t : ℝ, 0 ≤ t → t • x ∈ S) {x q : V}
    (hx : x ∈ S) (hq : OutwardNormal S x q) : inner ℝ q x = 0 := by
  have h0 := hq (0 • x) (hcone x hx 0 (le_refl 0))
  have h2 := hq (2 • x) (hcone x hx 2 (by norm_num))
  have he : (2 : ℝ) • x-x = x := by module
  rw [he] at h2
  rw [zero_smul,zero_sub,inner_neg_right] at h0
  linarith only [h0,h2]

/-- Above the reciprocal-curvature threshold, the reversed potential is
coercive. This is the sign change used in the two-cone predecessor argument. -/
theorem exists_backward_step_negative_coefficient {μ b : ℝ} {S : Set V}
    (hclosed : IsClosed S) (hconvex : Convex ℝ S)
    (hcone : ∀ x ∈ S, ∀ t : ℝ, 0 ≤ t → t • x ∈ S)
    (F : V → ℝ) (G : V → V) (hG : ∀ x, HasGradientAt F (G x) x)
    (hlower : ∀ x, (μ/2)*‖x‖^2 ≤ F x) (hb : 0 ≤ b) (hlarge : 1 < μ*b)
    (horth : ∀ x ∈ S, ∀ q, OutwardNormal S x q → inner ℝ q (G x) = 0)
    (y : V) (hy : -y ∈ S) : ∃ x ∈ S, x-b • G x = y := by
  let Φ : V → ℝ := fun x => -backwardPotential b F x
  let H : V → V := fun x => -(x-b • G x)
  have hH (x : V) : HasGradientAt Φ (H x) x := by
    apply hasGradientAt_iff_hasFDerivAt.mpr
    convert! (backwardPotential_hasGradientAt b F G hG x).hasFDerivAt.neg using 1 <;>
      simp only [Φ,H,map_neg]
  have hc : CoerciveOn S (fun x => Φ x-inner ℝ (-y) x) := by
    apply coercive_of_quadratic_lower (A := (μ*b-1)/2) (B := ‖-y‖) (C := 0)
      (by linarith : 0 < (μ*b-1)/2)
    intro x hx
    have hf := mul_le_mul_of_nonneg_left (hlower x) hb
    have hi := real_inner_le_norm (-y) x
    dsimp [Φ,backwardPotential]
    nlinarith only [hf,hi]
  obtain ⟨x,hx,hxy⟩ := exists_predecessor hclosed hconvex Φ H hH (-y) hy hc (by
    intro x hx q hq
    have hrad := cone_normal_radial_orthogonal hcone hx hq
    have hg := horth x hx q hq
    have he : H x-x = b • G x-(2 : ℝ) • x := by dsimp [H]; module
    rw [he,inner_sub_right,real_inner_smul_right,real_inner_smul_right,hg,hrad,mul_zero,mul_zero,sub_self])
  refine ⟨x,hx,?_⟩
  have he := congrArg Neg.neg hxy
  simpa only [H,neg_neg] using he

end
end StrongSilver
