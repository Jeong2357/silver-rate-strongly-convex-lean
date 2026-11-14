-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SupportedPath
import StrongSilver.TraceTransport

namespace StrongSilver
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem SupportFamily.gradient_zero_of_query_zero {ι : Type*} (F : SupportFamily ι V) (i : ι)
    (hx : F.z i+F.g i = 0) : F.g i = 0 := by
  have hz : F.z i = -F.g i := eq_neg_of_add_eq_zero_left hx
  have hh := F.origin i
  rw [hz,inner_neg_right,real_inner_self_eq_norm_sq] at hh
  exact norm_eq_zero.mp (by nlinarith only [hh,F.nonnegative i,norm_nonneg (F.g i)])

namespace SupportedPath
variable {μ : ℝ} {n : ℕ}

theorem endpoint_zero_of_source_zero (P : SupportedPath V μ n) (hx : P.x 0 = 0) : P.x (Fin.last n) = 0 := by
  have hall (i : Fin (n+1)) : P.x i = 0 := by
    induction i using Fin.induction with
    | zero => exact hx
    | succ i ih =>
      have hg := P.family.gradient_zero_of_query_zero i (by rw [← P.split,ih])
      rw [P.update,ih,hg,smul_zero,smul_zero,add_zero,smul_zero,sub_self]
  exact hall _

theorem source_ne_zero (P : SupportedPath V μ n) (he : P.x (Fin.last n) ≠ 0) : P.x 0 ≠ 0 :=
  fun hx => he (P.endpoint_zero_of_source_zero hx)

theorem distance_lower {κ : ℝ} {dimension : ℕ} (hκ : 1 ≤ κ) (hμ : 1/κ ≤ μ) (hμ1 : μ ≤ 1)
    (P : SupportedPath (Space dimension) μ n) (hx : P.x 0 ≠ 0) :
    ENNReal.ofReal (‖P.x (Fin.last n)‖^2/‖P.x 0‖^2) ≤ D κ (List.ofFn P.steps) := by
  obtain ⟨f,G,hf,h0,hn,hgrad,hrun⟩ := P.realize hκ hμ hμ1
  let w : Instance κ := {
    dimension := dimension
    f := f
    g := G
    admissible := hf
    start := P.x 0
    minimizer := 0
    minimal := by intro y; rw [h0]; exact hn y
    distinct := hx
  }
  have hh := distance_error_le_D (List.ofFn P.steps) w
  simpa only [distanceError,w,hrun,sub_zero] using hh

theorem finite_distance_lower [FiniteDimensional ℝ V] {κ : ℝ} (hκ : 1 ≤ κ)
    (hμ : 1/κ ≤ μ) (hμ1 : μ ≤ 1) (P : SupportedPath V μ n) (hx : P.x 0 ≠ 0) :
    ENNReal.ofReal (‖P.x (Fin.last n)‖^2/‖P.x 0‖^2) ≤ D κ (List.ofFn P.steps) := by
  have hd : 0 < Module.finrank ℝ V := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨P.x 0,hx⟩
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  have hm' : Module.finrank ℝ V = m+1 := hm
  let U : V ≃ₗᵢ[ℝ] Space m := by
    unfold Space
    rw [← hm']
    exact (stdOrthonormalBasis ℝ V).repr
  let Q := P.transport U.toLinearMap 1 zero_le_one (fun x y => by
    change inner ℝ (U x) (U y) = 1*inner ℝ x y
    rw [U.inner_map_map,one_mul])
  have hQ : Q.x 0 ≠ 0 := by
    change U (P.x 0) ≠ 0
    intro he
    exact hx (U.injective (by simpa only [map_zero] using he))
  have hh := Q.distance_lower hκ hμ hμ1 hQ
  change ENNReal.ofReal (‖U (P.x (Fin.last n))‖^2/‖U (P.x 0)‖^2) ≤ D κ (List.ofFn P.steps) at hh
  simpa only [U.norm_map] using hh

end SupportedPath
end
end StrongSilver
