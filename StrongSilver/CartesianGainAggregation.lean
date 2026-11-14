-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianSignedMasses

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 2200000

def levelSum (f : ScheduleTree → ℝ) : ℕ → ScheduleTree → ℝ
  | 0,.leaf _ => 0
  | 0,t@(.split _ _ _) => f t
  | _+1,.leaf _ => 0
  | d+1,.split l _ r => levelSum f d l+levelSum f d r

def throughSum (f : ScheduleTree → ℝ) : ℕ → ScheduleTree → ℝ
  | 0,_ => 0
  | _+1,.leaf _ => 0
  | d+1,t@(.split l _ r) => f t+throughSum f d l+throughSum f d r

def depthFrontier : ℕ → ScheduleTree → List ScheduleTree
  | 0,t => [t]
  | _+1,t@(.leaf _) => [t]
  | d+1,.split l _ r => depthFrontier d l++depthFrontier d r

def positiveExcessThrough (φ : ℝ → ℝ) : ℕ → ScheduleTree → Prop
  | 0,_ => True
  | _+1,.leaf _ => True
  | d+1,.split l b r => 0 < adjustedExcess φ l b ∧ positiveExcessThrough φ d l ∧ positiveExcessThrough φ d r

def logExcess (φ : ℝ → ℝ) : ScheduleTree → ℝ
  | .leaf _ => 0
  | .split l b _ => Real.log (adjustedExcess φ l b)

def frontierLogMass (φ : ℝ → ℝ) (d : ℕ) (t : ScheduleTree) : ℝ :=
  ((depthFrontier d t).map fun s => Real.log (s.prefixMass φ)).sum

theorem throughSum_succ (f : ScheduleTree → ℝ) (d : ℕ) (t : ScheduleTree) :
    throughSum f (d+1) t = throughSum f d t+levelSum f d t := by
  induction d generalizing t with
  | zero => cases t <;> simp [throughSum,levelSum]
  | succ d ih =>
    cases t with
    | leaf h => simp [throughSum,levelSum]
    | split l b r => simp only [throughSum,levelSum,ih]; ring

/-- Exact logarithmic telescoping of all actual split factors above a
fixed depth. This is the leading-product identity used in Lemma 4.2. -/
theorem depth_gain_telescoping (φ : ℝ → ℝ) (d : ℕ) (t : ScheduleTree)
    (hpos : positiveExcessThrough φ d t) :
    throughSum (rootGain φ) d t = Real.log (t.prefixMass φ)+throughSum (logExcess φ) d t-frontierLogMass φ d t := by
  induction d generalizing t with
  | zero => simp [throughSum,frontierLogMass,depthFrontier]
  | succ d ih =>
    cases t with
    | leaf h => simp [throughSum,frontierLogMass,depthFrontier]
    | split l b r =>
      have hl := ih l hpos.2.1
      have hr := ih r hpos.2.2
      have hg := rootGain_log_identity φ l r b hpos.1
      simp only [throughSum,logExcess,frontierLogMass,depthFrontier,List.map_append,List.sum_append]
      unfold frontierLogMass at hl hr
      linear_combination hg+hl+hr

def fourGain (φ : ℝ → ℝ) (t : ScheduleTree) : ℝ :=
  rootGain φ t+(rootGain φ t+levelSum (rootGain φ) 1 t)/Real.sqrt 2

/-- Grouping four leaf gaps yields precisely the two final depth
coefficients 1+1/sqrt(2) and 1/sqrt(2), with no dropped tie or leaf terms. -/
theorem fourGain_level_identity (φ : ℝ → ℝ) (d : ℕ) (t : ScheduleTree) :
    levelSum (fourGain φ) d t = (1+1/Real.sqrt 2)*levelSum (rootGain φ) d t+
      (1/Real.sqrt 2)*levelSum (rootGain φ) (d+1) t := by
  induction d generalizing t with
  | zero => cases t <;> simp only [levelSum,fourGain,rootGain] <;> ring
  | succ d ih =>
    cases t with
    | leaf h => simp [levelSum]
    | split l b r => simp only [levelSum,ih]; ring

def silverDepthGain (φ : ℝ → ℝ) (d : ℕ) (t : ScheduleTree) : ℝ :=
  2*throughSum (rootGain φ) d t+levelSum (fourGain φ) d t

theorem silverDepthGain_coefficients (φ : ℝ → ℝ) (d : ℕ) (t : ScheduleTree) :
    silverDepthGain φ d t = 2*throughSum (rootGain φ) d t+
      (1+1/Real.sqrt 2)*levelSum (rootGain φ) d t+
      (1/Real.sqrt 2)*levelSum (rootGain φ) (d+1) t := by
  rw [silverDepthGain,fourGain_level_identity]
  ring

theorem depthFrontier_length_le (d : ℕ) (t : ScheduleTree) : (depthFrontier d t).length ≤ 2^d := by
  induction d generalizing t with
  | zero => simp [depthFrontier]
  | succ d ih =>
    cases t with
    | leaf h =>
      simp only [depthFrontier,List.length_singleton]
      have hh : 0 < (2:ℕ)^(d+1) := pow_pos (by decide) _
      omega
    | split l b r =>
      simp only [depthFrontier,List.length_append,pow_succ]
      have hl := ih l
      have hr := ih r
      omega

end
end StrongSilver.ScheduleTree
