-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingCutBound
import StrongSilver.WorkingBandParameters

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1800000

theorem badPhaseCount_mono {α : Type*} (good weak : α → Bool) (qs : List α)
    (himp : ∀ q ∈ qs, weak q = true → good q = true) : badPhaseCount good qs ≤ badPhaseCount weak qs := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    have ht := ih (fun z hz => himp z (List.mem_cons_of_mem q hz))
    have hq := himp q (by simp)
    cases hg : good q <;> cases hw : weak q <;> simp_all [badPhaseCount_cons] <;> omega

def workingPhaseTests (A σ τ υ : ℝ) (q : CutPhase) : Bool :=
  decide (q.pivot ≤ A^(1+σ) ∧ Scalar.SignedIntervals.positiveMass q.gap ≤ A^(1+τ) ∧
    negativeLogSum q.gap (A^(1+υ)) ≤ (1/250)*Real.log A)

theorem eventually_working_marked_count {σ τ υ : ℝ} (hσ : 0 < σ) (hσmax : σ ≤ 1/200)
    (hτ : 0 < τ) (hτmax : τ ≤ 1/1000) (hσυ : σ < υ) (hτυ : τ < υ) (hυmax : υ ≤ 1/50) :
    ∀ᶠ A : ℝ in atTop, ∀ μ P : ℝ, ∀ qs : List CutPhase,
      0 < μ → μ*A^(1+υ) ≤ 31/32 → A^((49 : ℝ)/50) ≤ P → P ≤ A^((199 : ℝ)/200) →
      (∀ q ∈ qs, A^((499 : ℝ)/500) ≤ q.pivot) → (∀ q ∈ qs, ∀ b ∈ q.gap, 0 < b → b ≤ A) →
      badPhaseCount (ordinaryPhaseGood A μ (A^(1+υ)) P) qs ≤ badPhaseCount (workingPhaseTests A σ τ υ) qs := by
  classical
  filter_upwards [eventually_working_band_parameters hσ hσmax hτ hτmax hσυ hτυ hυmax] with A hparams
  intro μ P qs hμ hμT hPL hPU hpiv hgap
  apply badPhaseCount_mono
  intro q hq htest
  obtain ⟨hb,hm,hE⟩ : q.pivot ≤ A^(1+σ) ∧ Scalar.SignedIntervals.positiveMass q.gap ≤ A^(1+τ) ∧
      negativeLogSum q.gap (A^(1+υ)) ≤ (1/250)*Real.log A := of_decide_eq_true htest
  have hW := hparams μ q.pivot P q.gap hμ hμT (hpiv q hq) hb hPL hPU hm hE (hgap q hq)
  simp only [ordinaryPhaseGood,decide_eq_true_eq]
  exact hW

theorem eventually_working_band_curvature {υ : ℝ} (hυ : 0 < υ) : ∀ᶠ A : ℝ in atTop,
    ∀ μ : ℝ, 0 ≤ μ → μ*A^(1+υ) ≤ 31/32 → μ*A ≤ 1/2 ∧ μ ≤ 1 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop hυ).eventually (eventually_ge_atTop (2 : ℝ))] with A hA hpower
  intro μ hμ hμT
  have hA0 := zero_lt_one.trans hA
  have hT : 2*A ≤ A^(1+υ) := by
    rw [Real.rpow_add hA0,Real.rpow_one]
    nlinarith only [mul_le_mul_of_nonneg_left hpower hA0.le]
  have hμA := mul_le_mul_of_nonneg_left hT hμ
  have hT1 : 1 ≤ A^(1+υ) := Real.one_le_rpow hA.le (by linarith only [hυ])
  have hμ1 := mul_le_mul_of_nonneg_left hT1 hμ
  constructor <;> nlinarith only [hμA,hμ1,hμT]

def workingNumericalCutLoss (A κ μ σ τ υ : ℝ) (C : ScheduleCut) : ℝ :=
  2400*(C.phases.length : ℝ)/Real.log A+4*μ*Scalar.SignedIntervals.positiveMass C.unselected+
  304*(badPhaseCount (workingPhaseTests A σ τ υ) C.phases : ℝ)*Real.log A+
  2*inverseChargeAbove (κ/4) C.word μ+4*largeLogESum C.word (A^(1+σ))+
  4*(Scalar.SignedIntervals.positiveMass C.unselected/A^(1+τ))

/-- The working-cut lower bound with the three marked-phase tests of
Lemma 3.7 and no assumption of a pre-existing trajectory. -/
theorem eventually_working_cut_numerical_bound {σ τ υ : ℝ} (hσ : 0 < σ) (hσmax : σ ≤ 1/200)
    (hτ : 0 < τ) (hτmax : τ ≤ 1/1000) (hσυ : σ < υ) (hτυ : τ < υ) (hυmax : υ ≤ 1/50) :
    ∀ᶠ A : ℝ in atTop, ∀ κ μ P : ℝ, ∀ C : ScheduleCut,
      1 ≤ κ → 1/κ ≤ μ → μ ≤ 2/κ → μ*A^(1+υ) ≤ 31/32 →
      A^((49 : ℝ)/50) ≤ P → P ≤ A^((199 : ℝ)/200) →
      (∀ q ∈ C.phases, A^((499 : ℝ)/500) ≤ q.pivot) →
      (∀ q ∈ C.phases, ∀ b ∈ q.gap, 0 < b → b ≤ A) →
      (∀ b ∈ C.terminal, 0 < b → b ≤ A) → (∀ b ∈ C.word, 1-μ*b ≠ 0) →
      ENNReal.ofReal (Real.exp (-workingNumericalCutLoss A κ μ σ τ υ C)*(cutReferenceProduct μ P C.phases)^2) ≤ D κ C.word := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),eventually_working_cut_distance_bound,
    eventually_working_marked_count hσ hσmax hτ hτmax hσυ hτυ hυmax,
    eventually_working_band_curvature (hσ.trans hσυ)] with A hA hlower hmarked hcurv
  intro κ μ P C hκ hμ hμu hμT hPL hPU hpiv hgap ht hcritical
  have hμ0 : 0 < μ := (one_div_pos.mpr (zero_lt_one.trans_le hκ)).trans_le hμ
  obtain ⟨hcap,hμ1⟩ := hcurv μ hμ0.le hμT
  have hP : 1 ≤ P := (Real.one_le_rpow hA.le (by norm_num : (0 : ℝ) ≤ 49/50)).trans hPL
  have hmargin : ∀ q ∈ C.phases, P < q.pivot := by
    intro q hq
    exact hPU.trans_lt ((Real.rpow_lt_rpow_of_exponent_lt hA (by norm_num : (199 : ℝ)/200 < 499/500)).trans_le (hpiv q hq))
  have hactual := hlower κ μ (A^(1+υ)) P σ τ C hκ hμ hμ1 hμu hcap hP hσ.le (by linarith only [hσmax])
    hτ.le (by linarith only [hτmax]) hmargin hgap ht hcritical
  have hJ := hmarked μ P C.phases hμ0 hμT hPL hPU hpiv hgap
  have hJreal : (badPhaseCount (ordinaryPhaseGood A μ (A^(1+υ)) P) C.phases : ℝ) ≤
      (badPhaseCount (workingPhaseTests A σ τ υ) C.phases : ℝ) := by exact_mod_cast hJ
  have hcost : workingCutLoss A κ μ (A^(1+υ)) P σ τ C ≤ workingNumericalCutLoss A κ μ σ τ υ C := by
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJreal (by norm_num : (0 : ℝ) ≤ 304)) (Real.log_pos hA).le
    unfold workingCutLoss workingNumericalCutLoss
    linarith only [hm]
  have he := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost)) (sq_nonneg (cutReferenceProduct μ P C.phases))
  exact (ENNReal.ofReal_le_ofReal he).trans hactual

end
end StrongSilver
