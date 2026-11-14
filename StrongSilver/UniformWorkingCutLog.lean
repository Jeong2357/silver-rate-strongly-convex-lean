-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.WorkingLogEnvelope
import StrongSilver.OrderedCutProperties
import StrongSilver.EventualUniformTail

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 2600000

/-- One uniform logarithmic budget applies after every actual insertion
between the closed B-cut and the full A-cut. -/
theorem eventually_uniform_working_cut_log {σ τ υ : ℝ} (hσ : 0 < σ) (hσmax : σ ≤ 1/200)
    (hτ : 0 < τ) (hτmax : τ ≤ 1/1000) (hσυ : σ < υ) (hτυ : τ < υ) (hυmax : υ ≤ 1/50) :
    ∃ Cneg > 0, ∃ Ctail > 0, ∀ᶠ A : ℝ in atTop, ∀ κ B cap μ P critical : ℝ, ∀ h : List ℝ,
      1 < κ → A ≤ B → B ≤ cap → cap ≤ κ → B^(1+υ) ≤ cap →
      1/κ ≤ μ → μ ≤ 2/κ → μ*B^(1+υ) ≤ 31/32 → μ*B ≤ 1/2 →
      (∀ t : ℝ, A ≤ t → t ≤ B → t^((49 : ℝ)/50) ≤ P ∧ P ≤ t^((199 : ℝ)/200)) → 2*P ≤ A →
      (∀ b ∈ h, 1-μ*b ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical → D κ h ≤ 1 →
      let ps := orderedPositions h (eligibleIndices h Finset.univ A B)
      ∀ i ≤ ps.length, -workingLogEnvelope Cneg Ctail A B μ σ τ υ (weightedCount h cap) critical-
        (1200/Real.log A)*((countAbove h B : ℝ)+(i : ℝ)) ≤
        cutLogProduct (cappedStep μ B) P κ (positionCut (fun _ b => decide (B ≤ b)) h (ps.take i))-Real.log κ := by
  obtain ⟨Cneg,hCneg,Ctail,hCtail,hlower⟩ := eventually_working_stable_rank_log hσ hσmax hτ hτmax hσυ hτυ hυmax
  refine ⟨Cneg,hCneg,Ctail,hCtail,?_⟩
  filter_upwards [eventually_all_larger hlower,eventually_ge_atTop (4 : ℝ),
    eventually_ge_atTop (Real.exp 1),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
    with A hall hA he hlog
  intro κ B cap μ P critical h hκ hAB hBcap hcapκ hTcap hμ hμu hμT hcap hpad hPmargin hcrit hcritical hD
  dsimp only
  let ps := orderedPositions h (eligibleIndices h Finset.univ A B)
  intro i hi
  let C := positionCut (fun _ b => decide (B ≤ b)) h (ps.take i)
  obtain ⟨t,hAt,htB,hpiv,hgap⟩ := ordered_positionCut_band h hAB hi
  have ht4 : 4 ≤ t := hA.trans hAt
  have ht1 : 1 < t := lt_of_lt_of_le (by norm_num) ht4
  have ht0 := zero_lt_one.trans ht1
  have hA1 : 1 < A := lt_of_lt_of_le (by norm_num) hA
  have hA0 := zero_lt_one.trans hA1
  have hB0 := hA0.trans_le hAB
  have hLcap : t^(1+σ) ≤ cap := by
    calc
      _ ≤ B^(1+σ) := Real.rpow_le_rpow ht0.le htB (by linarith only [hσ])
      _ ≤ B^(1+υ) := Real.rpow_le_rpow_of_exponent_le (hA1.le.trans hAB) (by linarith only [hσυ])
      _ ≤ cap := hTcap
  have htT : t^(1+υ) ≤ B^(1+υ) := Real.rpow_le_rpow ht0.le htB (by linarith only [hσ,hσυ])
  have hμ0 : 0 < μ := (one_div_pos.mpr (zero_lt_one.trans hκ)).trans_le hμ
  have hμt := (mul_le_mul_of_nonneg_left htT hμ0.le).trans hμT
  have hpivlow : ∀ q ∈ C.phases, t^((499 : ℝ)/500) ≤ q.pivot := by
    intro q hq
    have hh : t^((499 : ℝ)/500) ≤ t := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le ht1.le (by norm_num : (499 : ℝ)/500 ≤ 1)
    exact hh.trans (hpiv q hq)
  have hpivmargin : ∀ q ∈ C.phases, 2*P ≤ q.pivot := fun q hq => hPmargin.trans (hAt.trans (hpiv q hq))
  have hword : C.word = h := positionCut_word _ _ _
  have hlocal := hall t hAt κ B cap μ P critical C hκ htB hBcap hcapκ hLcap (htT.trans hTcap)
    hμ hμu hμt hcap (hpad t hAt htB).1 (hpad t hAt htB).2 hpivlow hpivmargin
    (fun b hb _ => hgap b hb) (by simpa only [hword] using hcrit)
    (by simpa only [hword] using hcritical) (by simpa only [hword] using hD)
  rw [hword] at hlocal
  have hlogs := Real.log_le_log hA0 hAt
  have hterr := workingRankLogError_le_envelope (Cneg := Cneg) (μ := μ) (τ := τ) (υ := υ) (critical := critical) (by linarith only [ht4] : 2 ≤ t) (he.trans hAt) (hlog.trans hlogs) htB hCtail.le
    (weightedCount_nonneg h cap) hσ.le (hσmax.trans (by norm_num))
  have henv := workingLogEnvelope_mono_cutoff (μ := μ) (critical := critical) hA0 hAt (hA1.le.trans hAB) hCneg.le hCtail.le
    (weightedCount_nonneg h cap) hσ.le hτ.le (hσ.trans hσυ).le
  have hcount : (C.phases.length : ℝ) = (countAbove h B : ℝ)+(i : ℝ) := by
    exact_mod_cast ordered_positionCut_count h A B hi
  have hratio : 1200*(C.phases.length : ℝ)/Real.log t ≤ 1200*(C.phases.length : ℝ)/Real.log A :=
    div_le_div_of_nonneg_left (by positivity) (Real.log_pos hA1) hlogs
  rw [hcount] at hratio hlocal
  linear_combination hlocal+hterr+henv+hratio

end
end StrongSilver
