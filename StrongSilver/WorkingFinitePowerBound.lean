-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.UniformWorkingCutLog
import StrongSilver.CappedCutPowerBound
import StrongSilver.CommonCurvatureBounds

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2800000

theorem workingLogEnvelope_nonnegative {Cneg Ctail A B μ σ τ υ W critical : ℝ}
    (hCneg : 0 ≤ Cneg) (hCtail : 0 ≤ Ctail) (hA : 0 < A) (hB : 1 ≤ B)
    (hμ : 0 ≤ μ) (hW : 0 ≤ W) (hc : 0 ≤ critical) :
    0 ≤ workingLogEnvelope Cneg Ctail A B μ σ τ υ W critical := by
  have hd : 0 < 1-nu := by linarith [nu_lt_one]
  have hl := Real.log_nonneg hB
  unfold workingLogEnvelope
  positivity

theorem workingLogEnvelope_mono_mu {Cneg Ctail A B μ μ' σ τ υ W critical : ℝ}
    (hB : 0 < B) (hW : 0 ≤ W) (hμ : μ ≤ μ') :
    workingLogEnvelope Cneg Ctail A B μ σ τ υ W critical ≤
      workingLogEnvelope Cneg Ctail A B μ' σ τ υ W critical := by
  have hd : 0 < 1-nu := by linarith [nu_lt_one]
  have hh := mul_le_mul_of_nonneg_right hμ (show 0 ≤ 6*(W*B^(1-nu)/(1-nu)) by positivity)
  unfold workingLogEnvelope
  linear_combination hh

/-- A finite first-cut power lower bound derived from actual GD stability.
The curvature, root avoidance, trajectories, marked-count charges, sorted
refinements and weighted moment budget are all supplied by proved lemmas. -/
theorem eventually_working_finite_power_bound {σ τ υ : ℝ} (hσ : 0 < σ) (hσmax : σ ≤ 1/200)
    (hτ : 0 < τ) (hτmax : τ ≤ 1/1000) (hσυ : σ < υ) (hτυ : τ < υ) (hυmax : υ ≤ 1/50) :
    ∃ Cneg > 0, ∃ Ctail > 0, ∀ᶠ A : ℝ in atTop, ∀ κ B cap P : ℝ, ∀ h : List ℝ,
      1 < κ → A < B → B ≤ cap → cap ≤ κ/4 → B^(1+υ) ≤ cap →
      (∀ t : ℝ, A ≤ t → t ≤ B → t^((49 : ℝ)/50) ≤ P ∧ P ≤ t^((199 : ℝ)/200)) → 2*P ≤ A →
      weightedCount h cap = (countAbove h B : ℝ)*B^nu → D κ h ≤ 1 →
      ∃ μ : ℝ, 1/κ ≤ μ ∧ μ ≤ 9/(8*κ) ∧ (∀ b ∈ h, 1-μ*b ≠ 0) ∧
        (powerLogMinimum/2)*weightedCount h cap-
          splitCoefficient*(2*workingLogEnvelope Cneg Ctail A B (9/(8*κ)) σ τ υ (weightedCount h cap)
            (34*weightedCount h cap*cap^(-nu))*B^nu+
            4*(1200/Real.log A)*weightedCount h cap*(1+Real.log (B/A))) ≤
        cutPower (cappedStep μ B) P κ (fullCut A h) := by
  obtain ⟨Cneg,hCneg,Ctail,hCtail,hlower⟩ := eventually_uniform_working_cut_log hσ hσmax hτ hτmax hσυ hτυ hυmax
  refine ⟨Cneg,hCneg,Ctail,hCtail,?_⟩
  filter_upwards [hlower,eventually_ge_atTop (4 : ℝ)] with A hlog hA
  intro κ B cap P h hκ hAB hBcap hcapκ hTcap hpad hmargin hmax hD
  have hκ0 := zero_lt_one.trans hκ
  have hA1 : 1 < A := lt_of_lt_of_le (by norm_num) hA
  have hA0 := zero_lt_one.trans hA1
  have hB := hA0.trans hAB
  have hcap0 := hB.trans_le hBcap
  have hcapκ' : cap ≤ κ := hcapκ.trans (by linarith only [hκ0])
  obtain ⟨μ,hμ,hμu,hcrit,_,hq⟩ := exists_common_curvature_with_quarter_bound hκ0 h
  have hμ0 : 0 < μ := (one_div_pos.mpr hκ0).trans_le hμ
  have hμu2 : μ ≤ 2/κ := hμu.trans (by
    apply (div_le_div_iff₀ (by positivity : 0 < 8*κ) hκ0).mpr
    nlinarith only [hκ0])
  have hκμ := (le_div_iff₀ (by positivity : 0 < 8*κ)).mp hμu
  have hmT := mul_le_mul_of_nonneg_left (hTcap.trans hcapκ) hμ0.le
  have hμT : μ*B^(1+υ) ≤ 31/32 := by nlinarith only [hmT,hκμ]
  have hmB := mul_le_mul_of_nonneg_left (hBcap.trans hcapκ) hμ0.le
  have hμB : μ*B ≤ 1/2 := by nlinarith only [hmB,hκμ]
  have hcount : (countAbove h (κ/4) : ℝ) ≤ weightedCount h cap*cap^(-nu) := by
    have hh : (countAbove h (κ/4) : ℝ) ≤ (countAbove h cap : ℝ) := by exact_mod_cast countAbove_antitone h hcapκ
    exact hh.trans (countAbove_rank_bound h hcap0 le_rfl)
  have hcritical : inverseChargeAbove (κ/4) h μ ≤ 34*weightedCount h cap*cap^(-nu) :=
    hq.trans (by linear_combination 34*hcount)
  have hL := hlog κ B cap μ P (34*weightedCount h cap*cap^(-nu)) h hκ hAB.le hBcap hcapκ' hTcap
    hμ hμu2 hμT hμB hpad hmargin hcrit hcritical hD
  have henv := workingLogEnvelope_mono_mu (Cneg := Cneg) (Ctail := Ctail) (A := A)
    (σ := σ) (τ := τ) (υ := υ) (critical := 34*weightedCount h cap*cap^(-nu)) hB (weightedCount_nonneg h cap) hμu
  have hW := weightedCount_nonneg h cap
  have hE := workingLogEnvelope_nonnegative (A := A) (σ := σ) (τ := τ) (υ := υ)
    hCneg.le hCtail.le hA0 (hA1.le.trans hAB.le) (by positivity : 0 ≤ 9/(8*κ)) (weightedCount_nonneg h cap)
    (show 0 ≤ 34*weightedCount h cap*cap^(-nu) by positivity)
  have hL' : let ps := orderedPositions h (eligibleIndices h Finset.univ A B)
      ∀ i ≤ ps.length, -workingLogEnvelope Cneg Ctail A B (9/(8*κ)) σ τ υ (weightedCount h cap)
        (34*weightedCount h cap*cap^(-nu))-(1200/Real.log A)*((countAbove h B : ℝ)+(i : ℝ)) ≤
        cutLogProduct (cappedStep μ B) P κ (positionCut (fun _ b => decide (B ≤ b)) h (ps.take i))-Real.log κ := by
    dsimp only
    intro i hi
    exact (sub_le_sub_right (neg_le_neg henv) _).trans (hL i hi)
  have hP : 0 < P := (Real.rpow_pos_of_pos hA0 _).trans_le (hpad A le_rfl hAB.le).1
  have hφA : P < cappedStep μ B A := by
    have hh := cappedStep_ge hμ0 (by linarith only [hμB] : μ*B < 1) A
    linarith only [hh,hmargin,hP]
  refine ⟨μ,hμ,hμu,hcrit,?_⟩
  exact capped_full_cut_power_lower hμ0 hA0 hAB hBcap hμB hP (by linarith only [hmargin,hAB]) hφA hκ0
    (by linarith only [hBcap,hcapκ,hκ0]) hE (div_nonneg (by norm_num) (Real.log_pos hA1).le) h hmax hL'

end
end StrongSilver
