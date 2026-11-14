-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingReplacement
import StrongSilver.WorkingAssemblyLog

namespace StrongSilver.WorkingAssembly
open Real Filter
noncomputable section
set_option maxHeartbeats 3600000

/-- Reservation costs cancel exactly when comparing two sets of actual
ordinary replacement factors on the same original assembly. -/
theorem log_replacement_ratio {A μ T P : ℝ} {s : WorkingAssembly} (hA : 0 < A)
    (hs : s.Valid A μ T P) {f g : CutPhase → ℝ}
    (hf : ∀ q ∈ s.tracked, 0 < f q) (hg : ∀ q ∈ s.tracked, 0 < g q) :
    Real.log (s.replacementRate A μ P f)-Real.log (s.replacementRate A μ P g) =
      (s.tracked.map fun q => Real.log (f q)-Real.log (g q)).sum := by
  induction s with
  | ordinaryEnd q t =>
    rw [replacementRate,replacementRate,Real.log_mul (Real.exp_ne_zero _) (hf q (by simp [tracked])).ne',
      Real.log_mul (Real.exp_ne_zero _) (hg q (by simp [tracked])).ne']
    simp only [tracked,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    ring
  | ordinary q s ih =>
    have hft : ∀ p ∈ s.tracked, 0 < f p := fun p hp => hf p (List.mem_cons_of_mem q hp)
    have hgt : ∀ p ∈ s.tracked, 0 < g p := fun p hp => hg p (List.mem_cons_of_mem q hp)
    rw [replacementRate,replacementRate,
      Real.log_mul (replacementRate_positive hA hs.2 hft).ne' (hf q (by simp [tracked])).ne',
      Real.log_mul (replacementRate_positive hA hs.2 hgt).ne' (hg q (by simp [tracked])).ne']
    have hh := ih hs.2 hft hgt
    simp only [tracked,List.map_cons,List.sum_cons]
    linarith only [hh]
  | block q I c s ih =>
    have hf0 := replacementRate_positive hA hs.2.2.2.2.2 hf
    have hg0 := replacementRate_positive hA hs.2.2.2.2.2 hg
    have hc0 := (sq_pos_of_pos (workingBlockFactor_positive hA μ I)).ne'
    rw [replacementRate,replacementRate,Real.log_div hf0.ne' hc0,Real.log_div hg0.ne' hc0]
    have hh := ih hs.2.2.2.2.2 hf hg
    simp only [tracked]
    linarith only [hh]
  | blockEnd q I c t => simp [replacementRate,tracked]
  | noConnector q I t => simp [replacementRate,tracked]

theorem replacementRate_baseline (A μ P : ℝ) (s : WorkingAssembly) :
    s.replacementRate A μ P (fun q => (ordinaryReferenceFactor A μ q.pivot P q.gap)^2) = s.rate A μ P := by
  induction s with
  | ordinaryEnd q t => rfl
  | ordinary q s ih => simp only [replacementRate,rate,ih]
  | block q I c s ih => simp only [replacementRate,rate,ih]
  | blockEnd q I c t => rfl
  | noConnector q I t => rfl

theorem log_replacement_gain {A μ T P : ℝ} {s : WorkingAssembly} (hA : 1 < A)
    (hs : s.Valid A μ T P) {f : CutPhase → ℝ} (hf : ∀ q ∈ s.tracked, 0 < f q) :
    Real.log (s.replacementRate A μ P f) = Real.log (s.rate A μ P)+
      (s.tracked.map fun q => Real.log (f q)-2*Real.log (ordinaryReferenceFactor A μ q.pivot P q.gap)).sum := by
  have hg : ∀ q ∈ s.tracked, 0 < (ordinaryReferenceFactor A μ q.pivot P q.gap)^2 :=
    fun q hq => sq_pos_of_pos ((tracked_parameters hs q hq).reference_factor_positive hA)
  have hh := log_replacement_ratio (zero_lt_one.trans hA) hs hf hg
  rw [replacementRate_baseline] at hh
  simp only [Real.log_pow,Nat.cast_ofNat] at hh
  linarith only [hh]

/-- Actual last-iterate realizations yield the local-replacement test
for a stable original schedule; the original reservation cost is kept. -/
theorem eventually_stable_replacement_gain : ∀ᶠ A : ℝ in atTop,
    ∀ κ μ T P : ℝ, ∀ s : WorkingAssembly, s.Valid A μ T P →
    ∀ f : CutPhase → ℝ, (∀ q ∈ s.tracked, 0 < f q) →
    (∀ q ∈ s.tracked, PhaseTraceExtension A μ q (f q)) →
    1 ≤ κ → 1/κ ≤ μ → μ ≤ 1 → D κ s.word ≤ 1 →
    (s.tracked.map fun q => Real.log (f q)-2*Real.log (ordinaryReferenceFactor A μ q.pivot P q.gap)).sum ≤
      s.logCost A μ P-2*s.referenceLog μ P := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_realize_replacements] with A hA hrealize
  intro κ μ T P s hs f hf hext hκ hμ hμ1 hD
  obtain ⟨W⟩ := hrealize μ T P s hs f hf hext
  have hrate := W.stable_ratio_le_one hκ hμ hμ1 hD
  have hpos := replacementRate_positive (zero_lt_one.trans hA) hs hf
  have hlog := Real.log_le_log hpos hrate
  rw [Real.log_one,log_replacement_gain hA hs hf,log_rate hA hs] at hlog
  linarith only [hlog]

end
end StrongSilver.WorkingAssembly
