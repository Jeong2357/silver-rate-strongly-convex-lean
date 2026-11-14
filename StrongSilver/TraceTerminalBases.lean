-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.InitialPositiveTrace
import StrongSilver.WorkingTerminalAttachment
import StrongSilver.InitialTerminalAttachment
import StrongSilver.NoConnectingTerminal

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2000000

def workingTerminalRate (A μ : ℝ) (I t : List ℝ) : ℝ :=
  Real.exp (-4*(μ*Scalar.SignedIntervals.positiveMass t))/
    ((4*A^(19 : ℝ)*(1200000 : ℝ)^2)*(Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I))^2)
def initialTerminalRate (κ B μ : ℝ) (I t : List ℝ) : ℝ :=
  Real.exp (-4*(μ*Scalar.SignedIntervals.positiveMass t))/
    ((4*initialEntryConstant*(1200000 : ℝ)^2*(κ/B)^6)*(Real.exp (inverseCharge μ I)*(1+smallPositiveSum μ I/κ))^2)
def workingNoConnectorRate (A μ : ℝ) (I t : List ℝ) : ℝ :=
  Real.exp (-2*(inverseCharge μ I+2*μ*Scalar.SignedIntervals.positiveMass t))/(2*A^(19 : ℝ))
def initialNoConnectorRate (κ B μ : ℝ) (I t : List ℝ) : ℝ :=
  Real.exp (-2*(inverseCharge μ I+2*μ*Scalar.SignedIntervals.positiveMass t))/(2*initialEntryConstant*(κ/B)^4)

theorem eventually_working_terminal_trace : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T P c : ℝ, ∀ h I t : List ℝ, OrdinaryPhaseParameters A μ b T P h →
      2 ≤ c → 1/32 ≤ 1-μ*c → (∀ a ∈ I, 1-μ*a ≠ 0) → (∀ a ∈ t, 0 < a → a ≤ A) →
      Nonempty (PositiveTrace μ ((h++[b])++((I++[c])++t)) (workingGateFraction A) (A^(10 : ℝ)) (A^(10 : ℝ))
        (workingTerminalRate A μ I t)) := by
  filter_upwards [eventually_working_terminal_attachment (V := ℝ)] with A hattach
  intro μ b T P c h I t W hc hqc hcritical ht
  obtain ⟨n,J,hsteps,hend,hNZ,hpositive,hgate,hprojections,hratio⟩ :=
    hattach μ b T P c h I t W hc hqc hcritical ht 1 one_ne_zero
  exact ⟨PositiveTrace.ofPath J hsteps hNZ hpositive hgate hprojections hratio⟩

theorem eventually_initial_terminal_trace : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T κ B c : ℝ, ∀ h I t : List ℝ, InitialPhaseBudget A μ b T κ B h →
      2 ≤ c → B ≤ c → 1/32 ≤ 1-μ*c → μ*B ≤ 1/2 → (∀ a ∈ I, 1-μ*a ≠ 0) → (∀ a ∈ t, 0 < a → a ≤ B) →
      Nonempty (PositiveTrace μ ((h++[b])++((I++[c])++t)) (initialGateConstant/(κ/B)^2)
        (initialPointRelativeConstant*(κ/B)) (initialSlopeRelativeConstant*(κ/B)/κ) (initialTerminalRate κ B μ I t)) := by
  filter_upwards [eventually_initial_terminal_attachment (V := ℝ)] with A hattach
  intro μ b T κ B c h I t W hc hcB hqc hcap hcritical ht
  obtain ⟨n,J,hsteps,hend,hNZ,hpositive,hgate,hprojections,hratio⟩ :=
    hattach μ b T κ B c h I t W hc hcB hqc hcap hcritical ht 1 one_ne_zero
  exact ⟨PositiveTrace.ofInitialPath J hsteps hNZ hpositive hgate hprojections hratio⟩

theorem eventually_working_no_connector_trace : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T P : ℝ, ∀ h I t : List ℝ, OrdinaryPhaseParameters A μ b T P h →
      (∀ a ∈ I, 1-μ*a ≠ 0) → (∀ a ∈ t, 0 < a → a ≤ A) →
      Nonempty (PositiveTrace μ ((h++[b])++(I++t)) (workingGateFraction A) (A^(10 : ℝ)) (A^(10 : ℝ))
        (workingNoConnectorRate A μ I t)) := by
  filter_upwards [eventually_working_no_connector_terminal (V := ℝ)] with A hattach
  intro μ b T P h I t W hcritical ht
  obtain ⟨n,J,hsteps,hend,hNZ,hpositive,hgate,hprojections,hratio⟩ :=
    hattach μ b T P h I t W hcritical ht 1 one_ne_zero
  exact ⟨PositiveTrace.ofPath J hsteps hNZ hpositive hgate hprojections hratio⟩

theorem eventually_initial_no_connector_trace : ∀ᶠ A : ℝ in atTop,
    ∀ μ b T κ B : ℝ, ∀ h I t : List ℝ, InitialPhaseBudget A μ b T κ B h → μ*B ≤ 1/2 →
      (∀ a ∈ I, 1-μ*a ≠ 0) → (∀ a ∈ t, 0 < a → a ≤ B) →
      Nonempty (PositiveTrace μ ((h++[b])++(I++t)) (initialGateConstant/(κ/B)^2)
        (initialPointRelativeConstant*(κ/B)) (initialSlopeRelativeConstant*(κ/B)/κ) (initialNoConnectorRate κ B μ I t)) := by
  filter_upwards [eventually_initial_no_connector_terminal (V := ℝ)] with A hattach
  intro μ b T κ B h I t W hcap hcritical ht
  obtain ⟨n,J,hsteps,hend,hNZ,hpositive,hgate,hprojections,hratio⟩ :=
    hattach μ b T κ B h I t W hcap hcritical ht 1 one_ne_zero
  exact ⟨PositiveTrace.ofInitialPath J hsteps hNZ hpositive hgate hprojections hratio⟩

end
end StrongSilver
