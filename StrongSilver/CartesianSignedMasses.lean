-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianScheduleTree
import StrongSilver.Scalar.SignedIntervals
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace StrongSilver.ScheduleTree
open Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 1800000

def transformedWord (φ : ℝ → ℝ) (t : ScheduleTree) : List ℝ := t.word.map φ

def prefixMass (φ : ℝ → ℝ) (t : ScheduleTree) : ℝ := prefixMax (t.transformedWord φ)+1

def gapDrawdown (φ : ℝ → ℝ) (t : ScheduleTree) : ℝ := drawdown (t.transformedWord φ)

def adjustedExcess (φ : ℝ → ℝ) (l : ScheduleTree) (b : ℝ) : ℝ := φ b-1-l.gapDrawdown φ

def rootGain (φ : ℝ → ℝ) : ScheduleTree → ℝ
  | .leaf _ => 0
  | .split l b r => Real.log (adjustedExcess φ l b*(prefixMass φ (.split l b r))/(l.prefixMass φ*r.prefixMass φ))

theorem prefixMass_positive (φ : ℝ → ℝ) (t : ScheduleTree) : 0 < t.prefixMass φ := by
  have hh := prefixMax_nonneg (t.transformedWord φ)
  unfold prefixMass
  linarith only [hh]

theorem gapDrawdown_nonnegative (φ : ℝ → ℝ) (t : ScheduleTree) : 0 ≤ t.gapDrawdown φ := drawdown_nonneg _

/-- Exact signed mass and drawdown identities (4.14) on the original
Cartesian intervals whenever the adjusted excess is positive. -/
theorem positive_excess_mass_identity (φ : ℝ → ℝ) (l r : ScheduleTree) (b : ℝ)
    (hK : 0 < adjustedExcess φ l b) :
    prefixMass φ (.split l b r) = l.prefixMass φ+r.prefixMass φ+adjustedExcess φ l b ∧
      gapDrawdown φ (.split l b r) = r.gapDrawdown φ := by
  have hd : drawdown (l.transformedWord φ) < φ b := by
    unfold adjustedExcess gapDrawdown at hK
    linarith only [hK]
  have hreset := record_reset (l.transformedWord φ) (r.transformedWord φ) (φ b) hd
  constructor
  · simp only [prefixMass,transformedWord,word,List.map_append,List.map_cons]
    dsimp only [prefixMass,transformedWord,adjustedExcess,gapDrawdown] at hreset ⊢
    nlinarith only [hreset.1]
  · simpa only [gapDrawdown,transformedWord,word,List.map_append,List.map_cons] using hreset.2

theorem rootGain_log_identity (φ : ℝ → ℝ) (l r : ScheduleTree) (b : ℝ)
    (hK : 0 < adjustedExcess φ l b) :
    rootGain φ (.split l b r) = Real.log (adjustedExcess φ l b)+Real.log (prefixMass φ (.split l b r))-
      Real.log (l.prefixMass φ)-Real.log (r.prefixMass φ) := by
  rw [rootGain,Real.log_div (mul_pos hK (prefixMass_positive φ _)).ne'
    (mul_pos (prefixMass_positive φ l) (prefixMass_positive φ r)).ne',
    Real.log_mul hK.ne' (prefixMass_positive φ _).ne',
    Real.log_mul (prefixMass_positive φ l).ne' (prefixMass_positive φ r).ne']
  ring

end
end StrongSilver.ScheduleTree
