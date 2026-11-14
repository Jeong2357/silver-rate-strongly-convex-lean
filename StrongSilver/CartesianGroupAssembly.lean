-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianGroupTrace

namespace StrongSilver.ScheduleTree.FourGapGroup
open FourPhase Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 3600000

abbrev Group := FourGapGroup × ℝ

def groupScale (μ : ℝ) (q : Group) : ℝ := q.1.first.prefixMass (logarithmicStep μ)
def groupWord (q : Group) : List ℝ := q.1.tree.word++[q.2]

def firstScale (μ : ℝ) : List Group → ℝ → ℝ
  | [],H => H
  | q::_,_ => groupScale μ q

def firstOffset : List Group → ℝ → ℝ
  | [],Z => Z
  | _::_,_ => 0

def firstGate : List Group → ℝ → ℝ → ℝ
  | [],ηo,_ => ηo
  | _::_,_,η => η

def firstPointCap : List Group → ℝ → ℝ
  | [],Mo => Mo
  | _::_,_ => 26

def firstSlopeCap (μ : ℝ) : List Group → ℝ → ℝ
  | [],Go => Go
  | q::_,_ => 1/groupScale μ q

/-- Every field is an inequality about the actual original schedule;
no objective, interpolation family or trajectory is assumed. -/
structure GroupReady (δ c μ ε : ℝ) (q : Group) (H Z : ℝ) : Prop where
  data : BalancedGroupData q.1 μ (groupScale μ q) q.2 ε
  near : ε+μ*groupScale μ q ≤ δ
  scale_join : H ≤ groupScale μ q*lastExcess μ (groupScale μ q) q.1.gaps (q.1.pivots q.2)/2
  offset_join : lastExcess μ (groupScale μ q) q.1.gaps (q.1.pivots q.2)*Z ≤ c
  negative_join : ∀ i : Fin 3, negativeMass (q.1.gaps i.castSucc) ≤
    c*H/lastExcess μ (groupScale μ q) q.1.gaps (q.1.pivots q.2)

def sequenceReady (δ c μ ε : ℝ) : List Group → ℝ → ℝ → Prop
  | [],_,_ => True
  | q::qs,H,Z => GroupReady δ c μ ε q (firstScale μ qs H) (firstOffset qs Z) ∧ sequenceReady δ c μ ε qs H Z

def sequenceRate (C μ B ε η : ℝ) : List Group → ℝ → ℝ
  | [],_ => 1
  | q::qs,Z => sequenceRate C μ B ε η qs Z *
      (Real.exp (gainLower C q.1 μ (groupScale μ q) q.2 ε η (firstOffset qs Z))*
        (q.1.leadingFactor μ B q.2)^2)

/-- Actual finite backward assembly across any chronological list of
balanced four-gap groups. Only the rightmost group receives the input
height offset. Every preceding group receives the renewed zero offset. -/
theorem exists_group_sequence_trace : ∃ C > 0, ∃ δ > 0, ∃ c > 0,
    ∀ μ B ε η : ℝ, 0 ≤ B → μ*B ≤ 1/2 → 0 ≤ η → η ≤ c →
    ∀ qs : List Group, ∀ H Z ηo Mo Go r : ℝ, ∀ h : List ℝ,
    FourPhaseTrace μ h H Z ηo Mo Go r → sequenceReady δ c μ ε qs H Z →
    Nonempty (FourPhaseTrace μ ((qs.flatMap groupWord)++h)
      (firstScale μ qs H) (firstOffset qs Z) (firstGate qs ηo η)
      (firstPointCap qs Mo) (firstSlopeCap μ qs Go) (r*sequenceRate C μ B ε η qs Z)) := by
  obtain ⟨C,hC,δ,hδ,c,hc,hextend⟩ := exists_balanced_group_trace
  refine ⟨C,hC,δ,hδ,c,hc,?_⟩
  intro μ B ε η hB hμB hη hηc qs
  induction qs with
  | nil =>
    intro H Z ηo Mo Go r h W _
    simpa only [List.flatMap_nil,List.nil_append,firstScale,firstOffset,firstGate,firstPointCap,
      firstSlopeCap,sequenceRate,mul_one] using Nonempty.intro W
  | cons q qs ih =>
    intro H Z ηo Mo Go r h W hready
    obtain ⟨Q⟩ := ih H Z ηo Mo Go r h W hready.2
    have D := hready.1
    obtain ⟨P⟩ := hextend q.1 μ (groupScale μ q) q.2 ε B D.data D.near hB hμB
      (firstScale μ qs H) (firstOffset qs Z) η (firstGate qs ηo η) (firstPointCap qs Mo)
      (firstSlopeCap μ qs Go) (r*sequenceRate C μ B ε η qs Z) ((qs.flatMap groupWord)++h) Q
      D.scale_join D.offset_join D.negative_join hη hηc
    simpa only [List.flatMap_cons,List.append_assoc,groupWord,firstScale,firstOffset,firstGate,
      firstPointCap,firstSlopeCap,sequenceRate,mul_assoc] using Nonempty.intro P

end
end StrongSilver.ScheduleTree.FourGapGroup
