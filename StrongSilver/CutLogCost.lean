-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CutBlockGrowth

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2000000

theorem eventually_terminal_log_prices : ∀ᶠ A : ℝ in atTop,
    Real.log (4*A^(19 : ℝ)*(1200000 : ℝ)^2) ≤ 50*Real.log A ∧
      Real.log (2*A^(19 : ℝ)) ≤ 50*Real.log A := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log (4*(1200000 : ℝ)^2))),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log (2 : ℝ)))]
    with A hA hbig htwo
  have hA0 := zero_lt_one.trans hA
  have hlog := (Real.log_pos hA).le
  constructor
  · calc
      _ = Real.log ((4*(1200000 : ℝ)^2)*A^(19 : ℝ)) := by congr 1; ring
      _ = Real.log (4*(1200000 : ℝ)^2)+19*Real.log A := by
        rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hA0 _).ne',Real.log_rpow hA0]
      _ ≤ _ := by linarith only [hbig,hlog]
  · rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hA0 _).ne',Real.log_rpow hA0]
    linarith only [htwo,hlog]

namespace CutAssembly

theorem eventually_logCost_raw : ∀ᶠ A : ℝ in atTop,
    ∀ μ P : ℝ, ∀ s : CutAssembly, ∀ t : List ℝ,
      (s.erase t).logCost A μ P ≤
        2*(s.tracked.map fun q => 1200/Real.log A+μ*transformedGapMaximum μ q.gap).sum+
        4*μ*Scalar.SignedIntervals.positiveMass t+50*(s.blockCount : ℝ)*Real.log A+
        2*((s.erase t).blockWords.map fun I => inverseCharge μ I).sum+
        2*((s.erase t).blockWords.map fun I => Real.log (1+smallPositiveSum μ I)).sum := by
  filter_upwards [eventually_terminal_log_prices] with A hpoly
  intro μ P s t
  induction s with
  | ordinaryEnd q =>
    simp only [erase,WorkingAssembly.logCost,tracked,blockCount,WorkingAssembly.blockWords,List.map_cons,
      List.sum_cons,List.map_nil,List.sum_nil,Nat.cast_zero,mul_zero,zero_mul,add_zero]
    ring_nf
    exact le_rfl
  | ordinary q s ih =>
    simp only [erase,WorkingAssembly.logCost,tracked,blockCount,WorkingAssembly.blockWords,List.map_cons,List.sum_cons]
    nlinarith only [ih]
  | block q I c s ih =>
    simp only [erase,WorkingAssembly.logCost,tracked,blockCount,WorkingAssembly.blockWords,List.map_cons,List.sum_cons,
      Nat.cast_add,Nat.cast_one]
    nlinarith only [ih]
  | blockEnd q I c =>
    simp only [erase,WorkingAssembly.logCost,tracked,blockCount,WorkingAssembly.blockWords,List.map_cons,List.sum_cons,
      List.map_nil,List.sum_nil,Nat.cast_one,mul_zero,zero_mul,add_zero]
    nlinarith only [hpoly.1]
  | noConnector q I =>
    have hlog := log_one_add_nonnegative (smallPositiveSum_nonneg μ (I.flatMap CutPhase.word))
    simp only [erase,WorkingAssembly.logCost,tracked,blockCount,WorkingAssembly.blockWords,List.map_cons,List.sum_cons,
      List.map_nil,List.sum_nil,Nat.cast_one,mul_zero,zero_mul,add_zero]
    nlinarith only [hpoly.2,hlog]

/-- Aggregate block charges are bounded by disjoint reserved-phase charges. -/
theorem eventually_logCost_reserved : ∀ᶠ A : ℝ in atTop,
    ∀ μ P : ℝ, ∀ s : CutAssembly, ∀ t : List ℝ,
      (s.erase t).logCost A μ P ≤
        2*(s.tracked.map fun q => 1200/Real.log A+μ*transformedGapMaximum μ q.gap).sum+
        4*μ*Scalar.SignedIntervals.positiveMass t+50*(s.blockCount : ℝ)*Real.log A+
        2*inverseCharge μ (s.reserved.flatMap CutPhase.word)+2*(s.reserved.map phaseGrowthCharge).sum := by
  filter_upwards [eventually_logCost_raw] with A hraw
  intro μ P s t
  have hh := hraw μ P s t
  have hi := s.block_inverse_bound t μ
  have hg := s.block_growth_bound t μ
  linarith only [hh,hi,hg]

end CutAssembly
end
end StrongSilver
