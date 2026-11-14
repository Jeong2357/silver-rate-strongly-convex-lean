-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PositiveTrace
import StrongSilver.OrdinaryPhaseAttachment
import StrongSilver.OrdinaryReferenceFactor
import StrongSilver.TerminalBasePath

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2000000

theorem terminal_positive_trace {μ A : ℝ} (hμ : 0 ≤ μ) (hcap : μ*A ≤ 1/2)
    (t : List ℝ) (ht : ∀ a ∈ t, 0 < a → a ≤ A) (η : ℝ) :
    Nonempty (PositiveTrace μ t η (maxPrefixProduct μ t) 0
      (Real.exp (-4*(μ*Scalar.SignedIntervals.positiveMass t)))) := by
  obtain ⟨Q,hsteps,hsource,hNZ,hpositive,hgate,hprojections,hratio⟩ :=
    terminal_base_path hμ hcap t ht (Y := (1 : ℝ)) one_ne_zero
  exact ⟨PositiveTrace.ofPath Q hsteps hNZ hpositive (hgate η) hprojections hratio⟩

theorem eventually_ordinary_positive_trace : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T P : ℝ, ∀ h : List ℝ, OrdinaryPhaseParameters A μ b T P h →
      ∀ s : List ℝ, ∀ M G r : ℝ,
      PositiveTrace μ s (workingGateFraction A) M G r →
      Nonempty (PositiveTrace μ ((h++[b])++s) (workingGateFraction A) (A^(10 : ℝ)) (A^(10 : ℝ))
        (r*(ordinaryReferenceFactor A μ b P h)^2)) := by
  filter_upwards [eventually_ordinary_phase_attachment] with A hattach
  intro μ b T P h W s M G r S
  obtain ⟨n,J,hsteps,hNZ,hpositive,hgate,hprojections,hgain⟩ :=
    hattach μ b T P h W (Space S.dimension) S.length S.path S.nonzero S.positive S.gate
  have hstepseq : List.ofFn J.steps = (h++[b])++s :=
    hsteps.trans (congrArg (fun l : List ℝ => (h++[b])++l) S.steps_eq)
  have hmul := mul_le_mul_of_nonneg_right S.ratio (sq_nonneg (ordinaryReferenceFactor A μ b P h))
  have hratio : r*(ordinaryReferenceFactor A μ b P h)^2 ≤ ‖J.x (Fin.last n)‖^2/‖J.x 0‖^2 := hmul.trans hgain
  exact ⟨PositiveTrace.ofPath J hstepseq hNZ hpositive hgate hprojections hratio⟩

end
end StrongSilver
