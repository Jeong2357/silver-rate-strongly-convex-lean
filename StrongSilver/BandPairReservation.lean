-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandMarkedPhaseBudget
import StrongSilver.CompletePairTests

namespace StrongSilver
open Real Filter Set
noncomputable section
set_option maxHeartbeats 6800000

/-- The actual full-cut reservation and its pair test, with all band
geometry and the weighted reservation count discharged. -/
structure BandPairReservation (κ B cap μ u y : ℝ) (h : List ℝ) where
  assembly : CompleteCutAssembly
  phases_eq : assembly.phases = (bandFullCut μ u y h).phases
  wellFormed : assembly.WellFormed (ordinaryPhaseGood (bandCutoff μ u y) μ
    ((bandCutoff μ u y)^(1+bandUpsilon firstAverageEta)) (bandPad u))
  counted : assembly.Counted (ordinaryPhaseGood (bandCutoff μ u y) μ
    ((bandCutoff μ u y)^(1+bandUpsilon firstAverageEta)) (bandPad u))
  reserved_weight : Real.exp (nu*y)*(assembly.reserved.length:ℝ) ≤ 16*weightedCount h cap/u
  pair_test : ∀ f : CutPhase × CutPhase → ℝ,
    (∀ p ∈ assembly.ordinaryPairs (bandFullCut μ u y h).terminal,
      PairTraceExtension (bandCutoff μ u y) μ (bandPad u) p (f p)) →
    2*((bandFullCut μ u y h).phases.map fun q => Real.log ((q.pivot-bandPad u)/(transformedGapMaximum μ q.gap+bandPad u))).sum+
      (((assembly.ordinaryPairs (bandFullCut μ u y h).terminal).map f).sum)/2 ≤
      workingCutLoss (bandCutoff μ u y) κ μ ((bandCutoff μ u y)^(1+bandUpsilon firstAverageEta)) (bandPad u)
        (bandSigma firstAverageEta) (bandTau firstAverageEta) (bandFullCut μ u y h)

theorem eventually_band_pair_reservation : ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/2 → (∀ z ∈ h, 1-μ*z ≠ 0) → D κ h ≤ 1 →
    ∀ y ∈ Icc (outerBandLow u) (outerBandHigh u), Nonempty (BandPairReservation κ B cap μ u y h) := by
  obtain ⟨A₀,hSource⟩ := eventually_atTop.mp eventually_working_cut_pair_test
  have hη := firstAverageEta_bounds.1
  obtain ⟨hσ,hσmax,hτ,hτmax,_,_,_,_⟩ := band_exponent_bounds hη firstAverageEta_small
  filter_upwards [eventually_outer_band_log_window,eventually_band_cutoff_ge A₀,eventually_band_marked_phase_budget,
    eventually_ge_atTop (0:ℝ)] with u hWindow hMinimum hMarked hu
  intro κ B cap μ h hκ hB hBcap hcapκ hU hμ hμu hμB hcrit hD y hy
  let A := bandCutoff μ u y
  let P := bandPad u
  let C := bandFullCut μ u y h
  let T := A^(1+bandUpsilon firstAverageEta)
  have hμ0 := (one_div_pos.mpr (zero_lt_one.trans hκ)).trans_le hμ
  have W := hWindow B μ y hB hU hμ0 hμB hy
  have hA : 0 < A := W.2.2.1
  have hη1 := firstAverageEta_bounds.2
  have hBpower : B^(1-firstAverageEta) ≤ B := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB.le
      (show 1-firstAverageEta ≤ (1:ℝ) by linarith only [hη])
  have hAB : A ≤ B := W.2.2.2.2.2.2.2.2.1.trans hBpower
  have hμA : μ*A ≤ 1/2 := (mul_le_mul_of_nonneg_left hAB hμ0.le).trans hμB
  have hμ1 : μ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hB.le hμ0.le
    nlinarith only [hh,hμB,hμ0]
  have hP : 1 ≤ P := Real.one_le_exp_iff.mpr (by positivity)
  have hPpos : 0 < P := Real.exp_pos _
  have hPA : 2*P ≤ A := W.2.2.2.2.2.2.2.1
  have hPiv : ∀ p ∈ C.phases, P < p.pivot := by
    intro p hp
    have ha := fullCut_pivot hp
    linarith only [ha,hPA,hPpos]
  have hGap : ∀ p ∈ C.phases, ∀ b ∈ p.gap, 0 < b → b ≤ A := fun p hp b hb _ => fullCut_unselected (C.mem_gap_unselected hp hb)
  have hTerminal : ∀ b ∈ C.terminal, 0 < b → b ≤ A := fun b hb _ => fullCut_unselected (C.mem_terminal_unselected hb)
  have hWord : C.word = h := cutSchedule_word _ _
  obtain ⟨s,hph,hs,hCount,hReserved,hTest⟩ := hSource A (hMinimum B μ y hB hU hμ0 hμB hy) κ μ T P
    (bandSigma firstAverageEta) (bandTau firstAverageEta) C hκ.le hμ hμ1 hμu hμA hP
    hσ.le (hσmax.trans (by norm_num)) hτ.le (hτmax.trans (by norm_num)) hPiv hGap hTerminal
    (by simpa only [hWord] using hcrit) (by simpa only [hWord] using hD)
  have hMarkedCount := hMarked κ B cap μ h hκ hB hBcap hcapκ hU hμ0 hμB hD y hy
  have hReservedReal : (s.reserved.length:ℝ) ≤ 4*(badPhaseCount (ordinaryPhaseGood A μ T P) C.phases:ℝ) := by exact_mod_cast hReserved
  have hScale := mul_le_mul_of_nonneg_left hReservedReal (Real.exp_pos (nu*y)).le
  refine ⟨⟨s,hph,hs,hCount,?_,hTest⟩⟩
  dsimp only [T,P,A,C] at hScale
  linear_combination hScale+4*hMarkedCount

end
end StrongSilver
