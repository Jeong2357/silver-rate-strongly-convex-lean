-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.PhaseTraceExtensions
import StrongSilver.WorkingAssemblyLog

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 4000000

/-- A matching on the ordinary runs of the original reserved assembly.
A pair consumes two consecutive ordinary phases, so distinct pair
operations have disjoint original words. Exceptional blocks are retained. -/
inductive DisjointReplacementPlan (A μ P : ℝ) : WorkingAssembly → ℝ → Prop where
  | ordinaryEnd (q : CutPhase) (t : List ℝ) (g : ℝ)
      (extension : WordTraceExtension A μ q.word
        ((ordinaryReferenceFactor A μ q.pivot P q.gap)^2*Real.exp g)) :
      DisjointReplacementPlan A μ P (.ordinaryEnd q t) g
  | ordinary (q : CutPhase) (s : WorkingAssembly) (v g : ℝ)
      (tail : DisjointReplacementPlan A μ P s v)
      (extension : WordTraceExtension A μ q.word
        ((ordinaryReferenceFactor A μ q.pivot P q.gap)^2*Real.exp g)) :
      DisjointReplacementPlan A μ P (.ordinary q s) (v+g)
  | pairEnd (q r : CutPhase) (t : List ℝ) (g : ℝ)
      (extension : WordTraceExtension A μ (q.word++r.word)
        (((ordinaryReferenceFactor A μ q.pivot P q.gap)^2*
          (ordinaryReferenceFactor A μ r.pivot P r.gap)^2)*Real.exp g)) :
      DisjointReplacementPlan A μ P (.ordinary q (.ordinaryEnd r t)) g
  | pair (q r : CutPhase) (s : WorkingAssembly) (v g : ℝ)
      (tail : DisjointReplacementPlan A μ P s v)
      (extension : WordTraceExtension A μ (q.word++r.word)
        (((ordinaryReferenceFactor A μ q.pivot P q.gap)^2*
          (ordinaryReferenceFactor A μ r.pivot P r.gap)^2)*Real.exp g)) :
      DisjointReplacementPlan A μ P (.ordinary q (.ordinary r s)) (v+g)
  | block (q : CutPhase) (I : List ℝ) (c : ℝ) (s : WorkingAssembly) (v : ℝ)
      (tail : DisjointReplacementPlan A μ P s v) :
      DisjointReplacementPlan A μ P (.block q I c s) v
  | blockEnd (q : CutPhase) (I : List ℝ) (c : ℝ) (t : List ℝ) :
      DisjointReplacementPlan A μ P (.blockEnd q I c t) 0
  | noConnector (q : CutPhase) (I t : List ℝ) :
      DisjointReplacementPlan A μ P (.noConnector q I t) 0

namespace DisjointReplacementPlan

/-- The matching is realized by one actual objective and trajectory,
including all retained interpolation contacts and exceptional words. -/
theorem eventually_realize : ∀ᶠ A : ℝ in atTop,
    ∀ μ T P : ℝ, ∀ s : WorkingAssembly, s.Valid A μ T P → ∀ g : ℝ,
    DisjointReplacementPlan A μ P s g →
    Nonempty (PositiveTrace μ s.word (workingGateFraction A) (A^(10:ℝ)) (A^(10:ℝ))
      (s.rate A μ P*Real.exp g)) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_working_exceptional_trace,
    eventually_working_terminal_trace,eventually_working_no_connector_trace]
    with A hA hblock hterminal hno
  intro μ T P s hs g plan
  induction plan with
  | ordinaryEnd q t g hext =>
    obtain ⟨S⟩ := terminal_positive_trace hs.1.mu_positive.le (hs.1.mu_cap (zero_lt_one.trans hA)) t hs.2 (workingGateFraction A)
    obtain ⟨Q⟩ := hext t _ _ _ (Real.exp_pos _).le S
    have he : Real.exp (-4*(μ*Scalar.SignedIntervals.positiveMass t))*
        ((ordinaryReferenceFactor A μ q.pivot P q.gap)^2*Real.exp g) =
        (WorkingAssembly.ordinaryEnd q t).rate A μ P*Real.exp g := by
      simp only [WorkingAssembly.rate]
      ring
    rw [he] at Q
    exact ⟨Q⟩
  | ordinary q s v g tail hext ih =>
    obtain ⟨S⟩ := ih hs.2
    obtain ⟨Q⟩ := hext s.word _ _ _
      (mul_pos (WorkingAssembly.rate_positive hA hs.2) (Real.exp_pos _)).le S
    have he : (s.rate A μ P*Real.exp v)*
        ((ordinaryReferenceFactor A μ q.pivot P q.gap)^2*Real.exp g) =
        (WorkingAssembly.ordinary q s).rate A μ P*Real.exp (v+g) := by
      rw [Real.exp_add]
      simp only [WorkingAssembly.rate]
      ring
    rw [he] at Q
    exact ⟨Q⟩
  | pairEnd q r t g hext =>
    obtain ⟨S⟩ := terminal_positive_trace hs.1.mu_positive.le (hs.1.mu_cap (zero_lt_one.trans hA)) t hs.2.2 (workingGateFraction A)
    obtain ⟨Q⟩ := hext t _ _ _ (Real.exp_pos _).le S
    have he : Real.exp (-4*(μ*Scalar.SignedIntervals.positiveMass t))*
        (((ordinaryReferenceFactor A μ q.pivot P q.gap)^2*
          (ordinaryReferenceFactor A μ r.pivot P r.gap)^2)*Real.exp g) =
        (WorkingAssembly.ordinary q (.ordinaryEnd r t)).rate A μ P*Real.exp g := by
      simp only [WorkingAssembly.rate]
      ring
    rw [he] at Q
    simpa only [WorkingAssembly.word,List.append_assoc] using Nonempty.intro Q
  | pair q r s v g tail hext ih =>
    obtain ⟨S⟩ := ih hs.2.2
    obtain ⟨Q⟩ := hext s.word _ _ _
      (mul_pos (WorkingAssembly.rate_positive hA hs.2.2) (Real.exp_pos _)).le S
    have he : (s.rate A μ P*Real.exp v)*
        (((ordinaryReferenceFactor A μ q.pivot P q.gap)^2*
          (ordinaryReferenceFactor A μ r.pivot P r.gap)^2)*Real.exp g) =
        (WorkingAssembly.ordinary q (.ordinary r s)).rate A μ P*Real.exp (v+g) := by
      rw [Real.exp_add]
      simp only [WorkingAssembly.rate]
      ring
    rw [he] at Q
    simpa only [WorkingAssembly.word,List.append_assoc] using Nonempty.intro Q
  | block q I c s v tail ih =>
    obtain ⟨S⟩ := ih hs.2.2.2.2.2
    obtain ⟨Q⟩ := hblock μ q.pivot T P c q.gap I hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 s.word _ S
    have he : (s.rate A μ P*Real.exp v)/(workingBlockFactor A μ I)^2 =
        (WorkingAssembly.block q I c s).rate A μ P*Real.exp v := by
      simp only [WorkingAssembly.rate]
      ring
    rw [he] at Q
    exact ⟨Q⟩
  | blockEnd q I c t =>
    simpa only [WorkingAssembly.word,CutPhase.word,WorkingAssembly.rate,Real.exp_zero,mul_one] using
      hterminal μ q.pivot T P c q.gap I t hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  | noConnector q I t =>
    simpa only [WorkingAssembly.word,CutPhase.word,WorkingAssembly.rate,Real.exp_zero,mul_one] using
      hno μ q.pivot T P q.gap I t hs.1 hs.2.1 hs.2.2

end DisjointReplacementPlan
end
end StrongSilver
