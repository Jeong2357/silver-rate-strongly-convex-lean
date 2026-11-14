-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseScheduleParameters
import StrongSilver.FourPhaseSupportedAttachment
import StrongSilver.FourPhaseJoinedGain

namespace StrongSilver.FourPhase
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3600000

abbrev PhaseSchedule.LocalQueryIndex (S : PhaseSchedule) := Σ i : Fin 4, Fin (phaseWord S.gap S.pivot i).length

def PhaseSchedule.totalWord (S : PhaseSchedule) : List ℝ :=
  phaseWord S.gap S.pivot 0++phaseWord S.gap S.pivot 1++phaseWord S.gap S.pivot 2++phaseWord S.gap S.pivot 3

def PhaseSchedule.joiningScale (S : PhaseSchedule) (ζ : ℝ) : ℝ :=
  S.k-carry S.μ S.gap S.pivot 3*quadraticMultiplier S.μ (phaseWord S.gap S.pivot 3)*ζ

/-- Finite quantitative form of Lemma 4.1. The absolute constants are
chosen before all original signed schedules, retained spaces and suffixes.
The local geometry and every interpolation comparison are constructed. -/
theorem finite_four_phase_attachment : ∃ C > 0, ∃ ε₀ > 0, ∃ c₀ > 0,
    ∀ S : PhaseSchedule, ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
    (∀ i : Fin 8, i ≠ 7 → |S.shape 0 i-reference i| ≤ ε) →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      [ProperSpace (AttachmentSpace V Coordinates)],
    ∀ m : ℕ, ∀ Q : SupportedPath V S.μ m, ∀ H Z η : ℝ,
    FourPhaseSuffixBounds Q.family (Q.x 0) H Z →
    H ≤ S.T*S.k/2 → S.k*Z ≤ c₀ →
    (∀ i : Fin 3, negativeMass (S.gap i.castSucc) ≤ c₀*H/S.k) →
    0 ≤ η → η ≤ c₀ →
    let ζ := 1024*(η+S.k*Z)
    ∃ F : SupportFamily (S.LocalQueryIndex ⊕ Fin m) (AttachmentSpace V Coordinates),
    ∃ n : ℕ, ∃ P : SupportedPath (AttachmentSpace V Coordinates) S.μ n,
      List.ofFn P.steps = S.totalWord++List.ofFn Q.steps ∧
      P.x 0 = axisAttachment (Q.x 0) (S.joiningScale ζ) (source (S.shape ζ)) ∧
      P.x (Fin.last n) = retainedMap (W := Coordinates) (Q.x (Fin.last m)) ∧
      FourPhaseSuffixBounds P.family (P.x 0) S.T 0 ∧ P.family.Gate (P.x 0) η ∧
      P.WithinFamily F ∧
      (∀ j, F.z (Sum.inr j) = retainedMap (W := Coordinates) (Q.family.z j) ∧
        F.g (Sum.inr j) = retainedMap (W := Coordinates) (Q.family.g j) ∧ F.d (Sum.inr j) = Q.family.d j) ∧
      (∀ i, |inner ℝ (unitDirection (P.x 0)) (P.family.z i)| ≤ 26*‖P.x 0‖ ∧
        |inner ℝ (unitDirection (P.x 0)) (P.family.g i)| ≤ (1/S.T)*‖P.x 0‖) ∧
      gain (S.shape ζ)+(gain (S.shape ζ)+gainLeft (S.shape ζ)+gainRight (S.shape ζ))/Real.sqrt 2-
        C*ε*(|gain (S.shape ζ)|+|gainLeft (S.shape ζ)|+|gainRight (S.shape ζ)|)-C*(η+S.k*Z) ≤
      Real.log ((‖Q.x 0‖^2/‖P.x 0‖^2)*(totalMass (S.shape ζ)/S.k)^2) := by
  obtain ⟨b,hb,hb60,hparams⟩ := exists_schedule_parameter_radius
  obtain ⟨Cg,hCg,d,hd,hgain⟩ := exists_joined_gain_constants
  let ε₀ := min b d
  let c₀ := min (ε₀/2048) (1/1000)
  let C := 1024*Cg
  have he0 : 0 < ε₀ := lt_min hb hd
  have hc0 : 0 < c₀ := lt_min (div_pos he0 (by norm_num)) (by norm_num)
  have hC : 0 < C := mul_pos (by norm_num) hCg
  refine ⟨C,hC,ε₀,he0,c₀,hc0,?_⟩
  intro S ε hε hε0 hx V _ _ _ m Q H Z η B hH hZ hN hη hηsmall
  dsimp only
  let ζ := 1024*(η+S.k*Z)
  have hk := S.k_positive
  have hkZ : 0 ≤ S.k*Z := mul_nonneg hk.le B.offset_nonnegative
  have hz0 : 0 ≤ ζ := mul_nonneg (by norm_num) (add_nonneg hη hkZ)
  have hcb : c₀ ≤ ε₀/2048 := min_le_left _ _
  have hcn : c₀ ≤ 1/1000 := min_le_right _ _
  have hzε : ζ ≤ ε₀ := by dsimp [ζ]; nlinarith only [hηsmall,hZ,hcb]
  have hz60 : ζ ≤ 1/60 := hzε.trans ((min_le_left _ _).trans hb60)
  have hz16 : ζ ≤ 1/16 := by linarith only [hz60]
  have hG := hparams S ε hε (hε0.trans (min_le_left _ _)) hx ζ hz0 (hzε.trans (min_le_left _ _))
  let D := S.localParameters ζ hG hz0 hz16
  have J : D.JoiningScaleConditions := S.localParameters_joining hG hz0 hz16 hz60
  have hζZ : 2*lastExcess D.μ D.T D.gap D.pivot*Z ≤ D.ζ := by
    change 2*S.k*Z ≤ ζ
    dsimp [ζ]
    nlinarith only [hη,hkZ]
  have hζη : 512*η ≤ D.ζ := by
    change 512*η ≤ ζ
    dsimp [ζ]
    nlinarith only [hη,hkZ]
  have hN' (i : Fin 3) : 1000*lastExcess D.μ D.T D.gap D.pivot*negativeMass (D.gap i.castSucc) ≤ H := by
    change 1000*S.k*negativeMass (S.gap i.castSucc) ≤ H
    have hh := (le_div_iff₀ hk).mp (hN i)
    have hc := mul_le_mul_of_nonneg_right hcn B.scale_positive.le
    nlinarith only [hh,hc]
  obtain ⟨F,n,P,hword,hs,he,hB,hgate,hrows,hold,hrel⟩ :=
    D.exists_supported_attachment J Q B hH hζZ hN' hη hζη
  have hxD : ∀ i : Fin 8, i ≠ 7 → |D.shape i-reference i| ≤ ε := by
    intro i hi
    change |S.shape ζ i-reference i| ≤ ε
    rw [S.shape_coordinate_independent ζ 0 i hi]
    exact hx i hi
  have hg := hgain D J ε hε (hε0.trans (min_le_right _ _)) hxD (hzε.trans (min_le_right _ _))
  have hlog : Real.log ((‖Q.x 0‖^2/‖P.x 0‖^2)*(totalMass (S.shape ζ)/S.k)^2) =
      Real.log ((D.joiningScale/lastExcess D.μ D.T D.gap D.pivot)^2*
        (totalMass D.shape^2/‖source D.shape‖^2)) := by
    rw [hs]
    exact attached_log_gain_identity D J B.source_nonzero
  rw [← hlog] at hg
  refine ⟨F,n,P,hword,hs,he,hB,hgate,hrows,hold,hrel,?_⟩
  change gain (S.shape ζ)+(gain (S.shape ζ)+gainLeft (S.shape ζ)+gainRight (S.shape ζ))/Real.sqrt 2-
    Cg*ε*(|gain (S.shape ζ)|+|gainLeft (S.shape ζ)|+|gainRight (S.shape ζ)|)-Cg*ζ ≤ _ at hg
  have hsum : 0 ≤ |gain (S.shape ζ)|+|gainLeft (S.shape ζ)|+|gainRight (S.shape ζ)| := by positivity
  have hprice := mul_nonneg hε hsum
  have hmore := mul_nonneg hCg.le hprice
  dsimp only [C,ζ] at hg ⊢
  nlinarith only [hg,hmore]

end
end StrongSilver.FourPhase
