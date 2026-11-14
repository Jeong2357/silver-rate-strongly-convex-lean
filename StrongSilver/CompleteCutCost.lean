-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CompleteCutLog
import StrongSilver.PhaseInverseBudget
import StrongSilver.OrdinaryCostBudget

namespace StrongSilver.CompleteCutAssembly
open Real Filter
noncomputable section
set_option maxHeartbeats 2400000

def blockWords (t : List ℝ) : CompleteCutAssembly → List (List ℝ)
  | .scalar I => [I.flatMap CutPhase.word]
  | .positive s => (s.erase t).blockWords
  | .leadingBlock I c s => (I.flatMap CutPhase.word++c.gap)::(s.erase t).blockWords
  | .leadingEnd I c => [I.flatMap CutPhase.word++c.gap]

def blockCount : CompleteCutAssembly → ℕ
  | .scalar _ => 0
  | .positive s => s.blockCount
  | .leadingBlock _ _ s => 1+s.blockCount
  | .leadingEnd _ _ => 1

theorem blockCount_le_reserved (s : CompleteCutAssembly) : s.blockCount ≤ s.reserved.length := by
  cases s with
  | scalar I => exact Nat.zero_le _
  | positive s => exact s.blockCount_le_reserved
  | leadingBlock I c s =>
    have hh := s.blockCount_le_reserved
    simp only [blockCount,reserved,List.length_append,List.length_cons]
    omega
  | leadingEnd I c => simp [blockCount,reserved]

theorem block_weight_bound (s : CompleteCutAssembly) (t : List ℝ) (w : ℝ → ℝ) (hw : ∀ a, 0 ≤ w a) :
    ((s.blockWords t).map fun I => (I.map w).sum).sum ≤ (s.reserved.flatMap CutPhase.word |>.map w).sum := by
  cases s with
  | scalar I => simp [blockWords,reserved]
  | positive s => exact s.block_weight_bound t w hw
  | leadingBlock I c s =>
    have hh := s.block_weight_bound t w hw
    have hc := hw c.pivot
    simp only [blockWords,reserved,List.map_cons,List.sum_cons,List.map_append,List.sum_append,
      List.flatMap_append,List.flatMap_cons,CutPhase.word,List.map_nil,List.sum_nil]
    linarith only [hh,hc]
  | leadingEnd I c =>
    have hc := hw c.pivot
    simp only [blockWords,reserved,List.map_cons,List.sum_cons,List.map_append,List.sum_append,
      List.flatMap_append,List.flatMap_cons,List.flatMap_nil,CutPhase.word,List.map_nil,List.sum_nil]
    linarith only [hc]

theorem block_inverse_bound (s : CompleteCutAssembly) (t : List ℝ) (μ : ℝ) :
    ((s.blockWords t).map fun I => inverseCharge μ I).sum ≤ inverseCharge μ (s.reserved.flatMap CutPhase.word) := by
  simpa only [inverseCharge] using s.block_weight_bound t (fun a => inverseLogKernel (1-μ*a))
    (fun _ => inverseLogKernel_nonneg _)

theorem block_growth_bound (s : CompleteCutAssembly) (t : List ℝ) (μ : ℝ) :
    ((s.blockWords t).map fun I => Real.log (1+smallPositiveSum μ I)).sum ≤ (s.reserved.map phaseGrowthCharge).sum := by
  cases s with
  | scalar I =>
    have hh := log_one_add_block_mass μ I []
    simpa [blockWords,reserved,Scalar.SignedIntervals.positiveMass] using hh
  | positive s => exact s.block_growth_bound t μ
  | leadingBlock I c s =>
    have hh := s.block_growth_bound t μ
    have hI := log_one_add_block_mass μ I c.gap
    have hc : Real.log (1+Scalar.SignedIntervals.positiveMass c.gap) ≤ phaseGrowthCharge c :=
      le_add_of_nonneg_right (log_one_add_nonnegative (le_max_right c.pivot 0))
    simp only [blockWords,reserved,List.map_cons,List.sum_cons,List.map_append,List.sum_append]
    linarith only [hh,hI,hc]
  | leadingEnd I c =>
    have hI := log_one_add_block_mass μ I c.gap
    have hc : Real.log (1+Scalar.SignedIntervals.positiveMass c.gap) ≤ phaseGrowthCharge c :=
      le_add_of_nonneg_right (log_one_add_nonnegative (le_max_right c.pivot 0))
    simp only [blockWords,reserved,List.map_cons,List.sum_cons,List.map_append,List.sum_append,List.map_nil,List.sum_nil]
    linarith only [hI,hc]

theorem reserved_weight_le (s : CompleteCutAssembly) (w : CutPhase → ℝ) (hw : ∀ q, 0 ≤ w q) :
    (s.reserved.map w).sum ≤ (s.phases.map w).sum := by
  have hh := s.weight_partition w
  have hp : 0 ≤ (s.tracked.map w).sum := by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hz
    exact hw q
  linarith only [hh,hp]

theorem reserved_inverse_budget {κ μ A : ℝ}
    (hκ : 0 < κ) (hμ : 0 ≤ μ) (hμu : μ ≤ 2/κ) (hcap : μ*A ≤ 1/2)
    (s : CompleteCutAssembly) (t : List ℝ) (hgap : ∀ q ∈ s.reserved, ∀ a ∈ q.gap, 0 < a → a ≤ A) :
    inverseCharge μ (s.reserved.flatMap CutPhase.word) ≤
      2*μ*(s.reserved.map fun q => Scalar.SignedIntervals.positiveMass q.gap).sum+(s.reserved.length : ℝ)+
      inverseChargeAbove (κ/4) (s.word t) μ := by
  have hh := phase_inverse_budget hκ hμ hμu hcap s.reserved hgap
  let w : ℝ → ℝ := fun b => if κ/4 ≤ b then inverseLogKernel (1-μ*b) else 0
  have hw : ∀ b, 0 ≤ w b := by intro b; dsimp only [w]; split_ifs <;> first | exact inverseLogKernel_nonneg _ | exact le_rfl
  have hreserve := s.reserved_weight_le (fun q => w q.pivot) (fun q => hw q.pivot)
  have hwhole := (ScheduleCut.mk s.phases t).selected_weight_le w hw
  change (s.phases.map fun q => w q.pivot).sum ≤ inverseChargeAbove (κ/4) (s.word t) μ at hwhole
  exact hh.trans (add_le_add le_rfl (hreserve.trans hwhole))

theorem eventually_logCost_raw : ∀ᶠ A : ℝ in atTop,
    ∀ μ P : ℝ, ∀ s : CompleteCutAssembly, ∀ t : List ℝ,
      s.logCost A μ P t ≤
        2*(s.tracked.map fun q => 1200/Real.log A+μ*transformedGapMaximum μ q.gap).sum+
        4*μ*Scalar.SignedIntervals.positiveMass t+50*(s.blockCount : ℝ)*Real.log A+
        2*((s.blockWords t).map fun I => inverseCharge μ I).sum+
        2*((s.blockWords t).map fun I => Real.log (1+smallPositiveSum μ I)).sum := by
  filter_upwards [CutAssembly.eventually_logCost_raw,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log (4*(1200000 : ℝ)^2))),
    eventually_gt_atTop (1 : ℝ)] with A hraw hconstant hA
  have hlogA := (Real.log_pos hA).le
  intro μ P s t
  cases s with
  | scalar I =>
    have hg := log_one_add_nonnegative (smallPositiveSum_nonneg μ (I.flatMap CutPhase.word))
    simp only [logCost,tracked,blockWords,blockCount,List.map_nil,List.sum_nil,List.map_cons,List.sum_cons,
      Nat.cast_zero,mul_zero,zero_mul,add_zero,zero_add]
    linarith only [hg]
  | positive s => exact hraw μ P s t
  | leadingBlock I c s =>
    have hh := hraw μ P s t
    simp only [logCost,tracked,blockWords,blockCount,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_one]
    linarith only [hh]
  | leadingEnd I c =>
    simp only [logCost,tracked,blockWords,blockCount,List.map_nil,List.sum_nil,List.map_cons,List.sum_cons,
      Nat.cast_one,mul_zero,zero_mul,add_zero,zero_add]
    linarith only [hconstant,hlogA]

theorem eventually_logCost_reserved : ∀ᶠ A : ℝ in atTop,
    ∀ μ P : ℝ, ∀ s : CompleteCutAssembly, ∀ t : List ℝ,
      s.logCost A μ P t ≤
        2*(s.tracked.map fun q => 1200/Real.log A+μ*transformedGapMaximum μ q.gap).sum+
        4*μ*Scalar.SignedIntervals.positiveMass t+50*(s.blockCount : ℝ)*Real.log A+
        2*inverseCharge μ (s.reserved.flatMap CutPhase.word)+2*(s.reserved.map phaseGrowthCharge).sum := by
  filter_upwards [eventually_logCost_raw] with A hraw
  intro μ P s t
  have hh := hraw μ P s t
  have hi := s.block_inverse_bound t μ
  have hg := s.block_growth_bound t μ
  linarith only [hh,hi,hg]

end
end StrongSilver.CompleteCutAssembly
