-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseAxisAttachment
import StrongSilver.FourPhaseVectors
import StrongSilver.SupportedPath

namespace StrongSilver.FourPhase
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
set_option maxHeartbeats 1800000

theorem axisAttachment_norm_sq {Y : V} (hY : Y ≠ 0) (K : ℝ) (X : Coordinates) :
    ‖axisAttachment Y K X‖^2 = (‖Y‖/K)^2*‖X‖^2 := by
  simpa only [real_inner_self_eq_norm_sq] using axisAttachment_inner hY K X X

theorem attached_source_ratio {Y : V} (hY : Y ≠ 0) {K : ℝ} (hK : K ≠ 0)
    {X : Coordinates} (hX : X ≠ 0) :
    ‖Y‖^2/‖axisAttachment Y K X‖^2 = K^2/‖X‖^2 := by
  rw [axisAttachment_norm_sq hY]
  have hnY := norm_ne_zero_iff.mpr hY
  have hnX := norm_ne_zero_iff.mpr hX
  field_simp
  <;> ring

theorem attached_path_ratio {μ : ℝ} {m n : ℕ} (Q : SupportedPath V μ m)
    (P : SupportedPath (AttachmentSpace V Coordinates) μ n)
    (hY : Q.x 0 ≠ 0) {K : ℝ} (hK : K ≠ 0) {X : Coordinates} (hX : X ≠ 0)
    (hs : P.x 0 = axisAttachment (Q.x 0) K X)
    (he : P.x (Fin.last n) = retainedMap (W := Coordinates) (Q.x (Fin.last m))) :
    ‖P.x (Fin.last n)‖^2/‖P.x 0‖^2 =
      (‖Q.x (Fin.last m)‖^2/‖Q.x 0‖^2)*(K^2/‖X‖^2) := by
  rw [hs,he,axisAttachment_norm_sq hY]
  have heN : ‖retainedMap (W := Coordinates) (Q.x (Fin.last m))‖^2 = ‖Q.x (Fin.last m)‖^2 := by
    simpa only [real_inner_self_eq_norm_sq] using retained_inner (W := Coordinates) (Q.x (Fin.last m)) (Q.x (Fin.last m))
  rw [heN]
  have hnY := norm_ne_zero_iff.mpr hY
  have hnX := norm_ne_zero_iff.mpr hX
  field_simp
  <;> ring

end
end StrongSilver.FourPhase
