-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianGainAggregation

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 2400000

/-- Every depth group includes the original positive step immediately
following its interval; the rightmost group keeps the exterior boundary. -/
def depthPhases : ℕ → ScheduleTree → ℝ → List (ScheduleTree × ℝ)
  | 0,t,b => [(t,b)]
  | _+1,t@(.leaf _),b => [(t,b)]
  | d+1,.split l p r,b => depthPhases d l p++depthPhases d r b

def terminalFactor (φ : ℝ → ℝ) (t : ScheduleTree) (b : ℝ) : ℝ :=
  (φ b-1-t.gapDrawdown φ)/t.prefixMass φ

theorem depthPhases_word (d : ℕ) (t : ScheduleTree) (b : ℝ) :
    ((depthPhases d t b).flatMap fun q => q.1.word++[q.2]) = t.word++[b] := by
  induction d generalizing t b with
  | zero => simp [depthPhases]
  | succ d ih =>
    cases t with
    | leaf h => simp [depthPhases]
    | split l p r => simp only [depthPhases,List.flatMap_append,ih,word]; simp [List.append_assoc]

theorem depthPhases_length (d : ℕ) (t : ScheduleTree) (b : ℝ) :
    (depthPhases d t b).length = (depthFrontier d t).length := by
  induction d generalizing t b with
  | zero => rfl
  | succ d ih => cases t <;> simp [depthPhases,depthFrontier,ih]

theorem rootGain_exp_identity (φ : ℝ → ℝ) (l r : ScheduleTree) (b : ℝ)
    (hK : 0 < adjustedExcess φ l b) :
    Real.exp (rootGain φ (.split l b r)) =
      adjustedExcess φ l b*prefixMass φ (.split l b r)/(l.prefixMass φ*r.prefixMass φ) := by
  rw [rootGain,Real.exp_log (div_pos (mul_pos hK (prefixMass_positive φ _))
    (mul_pos (prefixMass_positive φ l) (prefixMass_positive φ r)))]

/-- Exact product identity for the real consecutive depth groups, with
their actual following pivots and drawdowns. -/
theorem depthPhases_factor_identity (φ : ℝ → ℝ) (d : ℕ) (t : ScheduleTree) (b : ℝ)
    (hpos : positiveExcessThrough φ d t) :
    ((depthPhases d t b).map fun q => terminalFactor φ q.1 q.2).prod =
      terminalFactor φ t b*Real.exp (throughSum (rootGain φ) d t) := by
  induction d generalizing t b with
  | zero => simp [depthPhases,throughSum]
  | succ d ih =>
    cases t with
    | leaf h => simp [depthPhases,throughSum]
    | split l p r =>
      have hd := (positive_excess_mass_identity φ l r p hpos.1).2
      have hl := ih l p hpos.2.1
      have hr := ih r b hpos.2.2
      simp only [depthPhases,List.map_append,List.prod_append,hl,hr,throughSum,Real.exp_add]
      rw [rootGain_exp_identity φ l r p hpos.1]
      unfold terminalFactor adjustedExcess
      rw [hd]
      have hM := (prefixMass_positive φ (.split l p r)).ne'
      have hlM := (prefixMass_positive φ l).ne'
      have hrM := (prefixMass_positive φ r).ne'
      field_simp
      <;> ring

end
end StrongSilver.ScheduleTree
