-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SupportedPathError
import StrongSilver.SupportSourceBounds
import StrongSilver.AttachmentNormalization

namespace StrongSilver
noncomputable section
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
set_option maxHeartbeats 1400000

namespace SupportedPath
variable {μ : ℝ} {n : ℕ}

def isometric (P : SupportedPath V μ n) (T : V ≃ₗᵢ[ℝ] W) : SupportedPath W μ n :=
  P.transport T.toLinearMap 1 zero_le_one (fun x y => by
    change inner ℝ (T x) (T y) = 1*inner ℝ x y
    rw [T.inner_map_map,one_mul])

theorem isometric_norm (P : SupportedPath V μ n) (T : V ≃ₗᵢ[ℝ] W) (i : Fin (n+1)) :
    ‖(P.isometric T).x i‖ = ‖P.x i‖ := by
  change ‖T (P.x i)‖ = ‖P.x i‖
  exact T.norm_map _

theorem isometric_ne_zero (P : SupportedPath V μ n) (T : V ≃ₗᵢ[ℝ] W) (hX : P.x 0 ≠ 0) :
    (P.isometric T).x 0 ≠ 0 := by
  change T (P.x 0) ≠ 0
  intro he
  exact hX (T.injective (by simpa only [map_zero] using he))

theorem isometric_positive (P : SupportedPath V μ n) (T : V ≃ₗᵢ[ℝ] W)
    (hp : P.family.PositiveAt (P.x 0)) : (P.isometric T).family.PositiveAt ((P.isometric T).x 0) := by
  constructor
  · intro i
    change 0 ≤ inner ℝ (T (P.x 0)) (T (P.family.z i))
    rw [T.inner_map_map]
    exact hp.1 i
  · intro i
    change 0 ≤ inner ℝ (T (P.x 0)) (T (P.family.g i))
    rw [T.inner_map_map]
    exact hp.2 i

theorem isometric_gate (P : SupportedPath V μ n) (T : V ≃ₗᵢ[ℝ] W) {η : ℝ}
    (hg : P.family.Gate (P.x 0) η) : (P.isometric T).family.Gate ((P.isometric T).x 0) η :=
  P.family.transport_gate T.toLinearMap 1 zero_le_one (fun x y => by
    change inner ℝ (T x) (T y) = 1*inner ℝ x y
    rw [T.inner_map_map,one_mul]) hg

theorem isometric_projections (P : SupportedPath V μ n) (T : V ≃ₗᵢ[ℝ] W) {M G : ℝ}
    (hp : ∀ i, |inner ℝ (unitDirection (P.x 0)) (P.family.z i)| ≤ M*‖P.x 0‖ ∧
      |inner ℝ (unitDirection (P.x 0)) (P.family.g i)| ≤ G*‖P.x 0‖) (i : Fin n) :
    |inner ℝ (unitDirection ((P.isometric T).x 0)) ((P.isometric T).family.z i)| ≤ M*‖(P.isometric T).x 0‖ ∧
      |inner ℝ (unitDirection ((P.isometric T).x 0)) ((P.isometric T).family.g i)| ≤ G*‖(P.isometric T).x 0‖ := by
  change |inner ℝ (unitDirection (T (P.x 0))) (T (P.family.z i))| ≤ M*‖T (P.x 0)‖ ∧
    |inner ℝ (unitDirection (T (P.x 0))) (T (P.family.g i))| ≤ G*‖T (P.x 0)‖
  simpa only [unitDirection,real_inner_smul_left,T.norm_map,T.inner_map_map] using hp i

end SupportedPath

theorem exists_euclidean_isometry [FiniteDimensional ℝ V] {x : V} (hx : x ≠ 0) :
    ∃ d : ℕ, Nonempty (V ≃ₗᵢ[ℝ] Space d) := by
  have hd : 0 < Module.finrank ℝ V := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨x,hx⟩
  obtain ⟨d,hdim⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  have hdim' : Module.finrank ℝ V = d+1 := hdim
  let T : V ≃ₗᵢ[ℝ] Space d := by
    unfold Space
    rw [← hdim']
    exact (stdOrthonormalBasis ℝ V).repr
  exact ⟨d,⟨T⟩⟩

end
end StrongSilver
