-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandEligibleSteps
import StrongSilver.FullCutRefinementSavings
import StrongSilver.FullWorkingLogLower
import StrongSilver.CutPositiveSumPower
import StrongSilver.CutLogRankUpper
import StrongSilver.HeightPowerNormalization

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 4000000

def bandFullCut (μ u y : ℝ) (h : List ℝ) : ScheduleCut := fullCut (bandCutoff μ u y) h

def bandSignedLog (κ B μ u y : ℝ) (h : List ℝ) : ℝ :=
  cutLogProduct (cappedStep μ B) (bandPad u) κ (bandFullCut μ u y h)-Real.log κ

def bandPositiveLog (κ B μ u y : ℝ) (h : List ℝ) : ℝ :=
  cutLogProduct (positivePartStep (cappedStep μ B)) (bandPad u) κ (bandFullCut μ u y h)-Real.log κ

def bandSignedPower (κ B μ u y : ℝ) (h : List ℝ) : ℝ :=
  cutPower (cappedStep μ B) (bandPad u) κ (bandFullCut μ u y h)

def bandPositivePower (κ B μ u y : ℝ) (h : List ℝ) : ℝ :=
  cutPower (positivePartStep (cappedStep μ B)) (bandPad u) κ (bandFullCut μ u y h)

def bandRefinementSavings (κ B μ u y : ℝ) (h : List ℝ) : ℝ :=
  totalGapSavingsMaximum (cappedStep μ B) (bandPad u) κ (2400/u) (bandEligible μ B u) (bandFullCut μ u y h)

def bandLogUpperConstant : ℝ := 2*(4/(1-nu)+4)
def bandPowerUpperConstant : ℝ := 5+2/(1-nu)

/-- The actual cut observables needed for (4.9)--(4.10). Every field is
a conclusion of the full-cut trajectory, rank and refinement estimates. -/
structure BandCutBounds (κ B cap μ u y : ℝ) (h : List ℝ) : Prop where
  signed_log_lower : -4804*weightedCount h cap/u ≤ Real.exp (nu*y)*bandSignedLog κ B μ u y h
  positive_log_upper : Real.exp (nu*y)*bandPositiveLog κ B μ u y h ≤ bandLogUpperConstant*weightedCount h cap
  log_order : bandSignedLog κ B μ u y h ≤ bandPositiveLog κ B μ u y h
  power_order : bandSignedPower κ B μ u y h ≤ bandPositivePower κ B μ u y h
  positive_power_upper : bandPositivePower κ B μ u y h ≤ bandPowerUpperConstant*weightedCount h cap
  savings_nonnegative : 0 ≤ bandRefinementSavings κ B μ u y h
  savings_upper : Real.exp (nu*y)*bandRefinementSavings κ B μ u y h ≤
    Real.exp (nu*y)*bandSignedLog κ B μ u y h+4804*weightedCount h cap/u

end
end StrongSilver
