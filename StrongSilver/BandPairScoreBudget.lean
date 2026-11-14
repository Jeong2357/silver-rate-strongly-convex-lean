-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandPairExtension
import StrongSilver.BandWorkingCutLoss
import StrongSilver.PairPositiveExtension
import StrongSilver.AdjacentOptionPairs
import StrongSilver.FiniteInjectiveProvider

namespace StrongSilver
open ScheduleTree BinaryForest Real Filter Set
noncomputable section
set_option maxHeartbeats 8500000

def linkedPairPhase (p : LinkedGap × LinkedGap) : CutPhase × CutPhase :=
  (p.1.phase?.getD ⟨[],0,0⟩,p.2.phase?.getD ⟨[],0,0⟩)

theorem linkedPairPhase_of_some {q r : LinkedGap} {a b : CutPhase}
    (hqa : q.phase? = some a) (hrb : r.phase? = some b) : linkedPairPhase (q,r) = (a,b) := by
  simp only [linkedPairPhase,hqa,hrb,Option.getD_some]

/-- All positive actual pair scores are paid by a choice-independent
source-cut envelope. The reservation is arbitrary and need not be
selected measurably as the cutoff varies. -/
theorem eventually_band_pair_score_budget : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ critical : ℝ, ∀ h : List ℝ,
    1 < κ → 1 < B → B ≤ cap → cap ≤ κ → B ≤ κ/128 → u ≤ firstAverageLogScale B →
    1/κ ≤ μ → μ ≤ 2/κ → μ*B ≤ 1/10000 →
    (∀ z ∈ h, 1-μ*z ≠ 0) → inverseChargeAbove (κ/4) h μ ≤ critical →
    critical ≤ 34*weightedCount h cap*cap^(-nu) → D κ h ≤ 1 →
    ∀ y ∈ Icc (outerBandLow u) (outerBandHigh u), ∀ s : BandPairReservation κ B cap μ u y h,
    Real.exp (nu*y)*((bandPostReservedPairs κ B μ u (Real.log u/200) (fourPhaseDepth u+1) h s.assembly.reserved y).map
      fun p => max (bandPairScore C B μ u y p.1) 0).sum ≤
      4*max (Real.exp (nu*y)*bandPositiveLog κ B μ u y h) 0+19216*weightedCount h cap/u := by
  classical
  obtain ⟨C,hC,H⟩ := eventually_band_pair_extension
  obtain ⟨A₀,hZero⟩ := eventually_atTop.mp eventually_ordinary_pair_extension
  refine ⟨C,hC,?_⟩
  filter_upwards [H,eventually_band_working_cut_loss,eventually_band_linked_cut_phases,
    eventually_band_cutoff_ge A₀,eventually_outer_band_log_window] with u hExt hLoss hPhases hMinimum hWindow
  intro κ B cap μ critical h hκ hB hBcap hcapκ hBκ hU hμ hμu hμB hcrit hcritical hcriticalRank hD y hy s
  let A := bandCutoff μ u y
  let P := bandPad u
  let T := A^(1+bandUpsilon firstAverageEta)
  let xs := bandPostReservedPairs κ B μ u (Real.log u/200) (fourPhaseDepth u+1) h s.assembly.reserved y
  let ys := s.assembly.ordinaryPairs (bandFullCut μ u y h).terminal
  let g := fun p : LinkedGap × LinkedGap => max (bandPairScore C B μ u y p.1) 0
  have hκ0 := zero_lt_one.trans hκ
  have hμ0 := (one_div_pos.mpr hκ0).trans_le hμ
  have hCap : μ*B ≤ 1/2 := by linarith only [hμB]
  have W := hWindow B μ y hB hU hμ0 hCap hy
  have hA : 0 < A := W.2.2.1
  have hActual (p : LinkedGap × LinkedGap) (hp : p ∈ xs) :
      ∃ a b : CutPhase, p.1.phase? = some a ∧ p.2.phase? = some b ∧ (a,b) ∈ ys ∧
        PairTraceExtension A μ P (a,b) (bandPairScore C B μ u y p.1) :=
    hExt κ B cap μ y h hκ0 hB hBκ hU hμ0 hμB hy s p.1 p.2 hp
  have hMem (p : LinkedGap × LinkedGap) (hp : p ∈ xs) : linkedPairPhase p ∈ ys := by
    obtain ⟨a,b,ha,hb,hm,_⟩ := hActual p hp
    simpa only [linkedPairPhase,ha,hb,Option.getD_some] using hm
  have hBase (p : CutPhase × CutPhase) (hp : p ∈ ys) : PairTraceExtension A μ P p 0 := by
    have hGood := s.assembly.ordinaryPairs_good s.wellFormed _ hp
    have Wa : OrdinaryPhaseParameters A μ p.1.pivot T P p.1.gap := @of_decide_eq_true _ (Classical.propDecidable _) hGood.1
    have Wb : OrdinaryPhaseParameters A μ p.2.pivot T P p.2.gap := @of_decide_eq_true _ (Classical.propDecidable _) hGood.2
    exact hZero A (hMinimum B μ y hB hU hμ0 hCap hy) μ T P p.1 p.2 Wa Wb
  have hValid (p : LinkedGap × LinkedGap) (hp : p ∈ xs) : PairTraceExtension A μ P (linkedPairPhase p) (g p) := by
    obtain ⟨a,b,ha,hb,hm,he⟩ := hActual p hp
    have hmap : linkedPairPhase p = (a,b) := by simp only [linkedPairPhase,ha,hb,Option.getD_some]
    rw [hmap]
    exact pairTraceExtension_positive_part (hBase (a,b) hm) he
  have hSub : xs.Sublist (adjacentOccurrences (bandLinkedFrontier κ B μ u y h)) :=
    (List.filter_sublist.trans List.filter_sublist)
  have hImageSub := (hSub.filterMap (optionPairMap LinkedGap.phase?)).trans
    (adjacentOccurrences_filterMap_sublist LinkedGap.phase? (bandLinkedFrontier κ B μ u y h))
  have hPh := hPhases κ B μ y h hB hU hμ0 hCap hy
  change (bandLinkedFrontier κ B μ u y h).filterMap LinkedGap.phase? = _ at hPh
  rw [hPh] at hImageSub
  have hImageEq : xs.filterMap (optionPairMap LinkedGap.phase?) = xs.map linkedPairPhase := by
    apply List.filterMap_eq_map_iff_forall_eq_some.mpr
    intro p hp
    obtain ⟨a,b,ha,hb,_,_⟩ := hActual p hp
    simp only [optionPairMap,ha,hb,Option.bind_some,Option.map_some,linkedPairPhase,Option.getD_some]
  have hNodup : (xs.map linkedPairPhase).Nodup := by
    rw [← hImageEq]
    exact (adjacentOccurrences_nodup (cutScheduleFrom_phases_nodup _ _ _)).sublist hImageSub
  obtain ⟨F,hF,hFV,hFE,hSum⟩ := finite_injective_provider linkedPairPhase g (PairTraceExtension A μ P) xs ys hNodup
    hMem (fun p _ => le_max_right _ _) hBase hValid
  have hTest := s.pair_test F hFV
  have hSumBound : (xs.map g).sum ≤
      2*workingCutLoss A κ μ T P (bandSigma firstAverageEta) (bandTau firstAverageEta) (bandFullCut μ u y h)-
      4*rawReferenceLog μ P (bandFullCut μ u y h).phases := by
    change 2*rawReferenceLog μ P (bandFullCut μ u y h).phases+(ys.map F).sum/2 ≤ _ at hTest
    linarith only [hSum,hTest]
  have hB0 := zero_lt_one.trans hB
  have hPpos : 0 < P := Real.exp_pos _
  have hη := firstAverageEta_bounds.1
  have hAB : A ≤ B := W.2.2.2.2.2.2.2.2.1.trans (by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB.le
      (show 1-firstAverageEta ≤ (1:ℝ) by linarith only [hη]))
  have hWord : (bandFullCut μ u y h).word = h := cutSchedule_word _ _
  have hConversion := full_cut_capped_log_lower hκ0 hμ0 hB0 hCap hPpos (bandFullCut μ u y h)
    (fun p hp => W.2.2.2.2.2.2.2.1.trans (fullCut_pivot hp).le) (by
      intro p hp a ha
      by_cases ha0 : 0 < a
      · exact (fullCut_unselected ((bandFullCut μ u y h).mem_gap_unselected hp ha)).trans hAB
      · exact (le_of_not_gt ha0).trans hB0.le)
  rw [hWord] at hConversion
  have hSigned : -rawReferenceLog μ P (bandFullCut μ u y h).phases-4*μ*clippedMass h B ≤
      bandSignedLog κ B μ u y h := hConversion
  have hSourceLoss := hLoss κ B cap μ critical h hκ hB hBcap hcapκ hU hμ hμu hCap hcrit hcritical hcriticalRank hD y hy
  have hLogOrder : bandSignedLog κ B μ u y h ≤ bandPositiveLog κ B μ u y h := by
    apply sub_le_sub_right _ (Real.log κ)
    apply cutLogProduct_le_positivePart (cappedStep μ B) hPpos hκ0.le (bandFullCut μ u y h)
    intro p hp
    have hp0 := hA.trans (fullCut_pivot hp)
    exact (hp0.trans_le (cappedStep_ge hμ0 (by linarith only [hCap]) p.pivot)).le
  have hPoint := mul_le_mul_of_nonneg_left hSumBound (Real.exp_pos (nu*y)).le
  have hConvert := mul_le_mul_of_nonneg_left hSigned (Real.exp_pos (nu*y)).le
  have hOrder := mul_le_mul_of_nonneg_left hLogOrder (Real.exp_pos (nu*y)).le
  have hMax := le_max_left (Real.exp (nu*y)*bandPositiveLog κ B μ u y h) (0:ℝ)
  dsimp only [A,P,T,xs,g] at hPoint hConvert hOrder ⊢
  linear_combination hPoint+4*hConvert+4*hSourceLoss+4*hOrder+4*hMax

end
end StrongSilver
