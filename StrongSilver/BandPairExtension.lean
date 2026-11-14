-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandTwoGapCommonBudgets
import StrongSilver.BandRightRoot
import StrongSilver.BandCandidateDrawdown
import StrongSilver.BandReservedPairOrdinary
import StrongSilver.OrdinaryPairParameters
import StrongSilver.BandGoodThroughBalance
import StrongSilver.TwoGapExtension

namespace StrongSilver
open ScheduleTree BinaryForest Scalar.SignedIntervals Real Filter Set
noncomputable section
set_option maxHeartbeats 8500000

/-- The gap preceding an original selected pivot consists of steps
bounded by that pivot, with the original signed word unchanged. -/
theorem linkedFrontier_word_le_following {φ : ℝ → ℝ} {s κ : ℝ}
    {t : ScheduleTree} (ht : t.Cartesian) {q : LinkedGap} {p : ScheduleNode}
    (hq : q ∈ linkedFrontier φ s 0 κ none none t) (hp : q.following = some p) :
    ∀ a ∈ q.node.source.word, a ≤ p.pivot := by
  have hMem := linkedFrontier_following_mem hq hp
  have hc := indexedTree_source_cartesian ht hMem
  obtain ⟨l,r,b,hs,hSuffix⟩ := linkedFrontier_following_suffix hq hp
  rw [hs] at hc
  have he : p.pivot = b := by rw [ScheduleNode.pivot,hs,rootStep_split]
  intro a ha
  rw [he]
  exact (hc.2.2.2.1 a (hSuffix.sublist.subset ha)).le

/-- Gain supplied by the actual pair's source subtree, with the common
band scales rather than additional free numerical parameters. -/
def bandPairScore (C B μ u y : ℝ) (q : LinkedGap) : ℝ :=
  twoGapScore C μ B (4*bandTolerance u)
    (bandLocalLowerScale u (bandCutoff μ u y))
    (bandLocalUpperScale u (bandCutoff μ u y))
    (bandCutoff μ u y) (fourPhaseDepth u) q.node.source (q.followingStep 0)

/-- Every actual available pair after the full-cut reservation has the
claimed retained-suffix extension. All local two-gap hypotheses follow
from the original schedule and its good-subtree condition. -/
theorem eventually_band_pair_extension : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ y : ℝ, ∀ h : List ℝ,
    0 < κ → 1 < B → B ≤ κ/128 → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/10000 →
    y ∈ Icc (outerBandLow u) (outerBandHigh u) → ∀ s : BandPairReservation κ B cap μ u y h,
    ∀ q r : LinkedGap,
    (q,r) ∈ bandPostReservedPairs κ B μ u (Real.log u/200) (fourPhaseDepth u+1) h s.assembly.reserved y →
    ∃ a b : CutPhase, q.phase? = some a ∧ r.phase? = some b ∧
      (a,b) ∈ s.assembly.ordinaryPairs (bandFullCut μ u y h).terminal ∧
      PairTraceExtension (bandCutoff μ u y) μ (bandPad u) (a,b) (bandPairScore C B μ u y q) := by
  classical
  obtain ⟨C,hC,τ,hτ,c,hc,HE⟩ := eventually_two_gap_extension
  obtain ⟨A₀,hExtension⟩ := eventually_atTop.mp HE
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_band_candidate_scale,eventually_band_candidate_upper_scales,
    eventually_band_two_gap_common_budgets hc,eventually_band_two_gap_near hτ,
    eventually_band_right_root,eventually_band_right_gap_mass,eventually_band_candidate_drawdown,
    eventually_band_goodThrough_balance,eventually_band_reserved_pair_ordinary,
    eventually_outer_band_log_window,eventually_band_cutoff_ge A₀,eventually_eligible_band_step,
    eventually_ge_atTop (1:ℝ)]
    with u hScale hUpper hBudget hNear hRight hMass hDraw hBalance hOrdinary hWindow hMinimum hEligible hu
  intro κ B cap μ y h hκ hB hBκ hU hμ hμB hy s q r hPair
  let A := bandCutoff μ u y
  let L := bandLocalLowerScale u A
  let U := bandLocalUpperScale u A
  let P := bandPad u
  let T := A^(1+bandUpsilon firstAverageEta)
  let d := fourPhaseDepth u
  have hCap : μ*B ≤ 1/2 := by linarith only [hμB]
  have hPreMem := List.mem_filter.mp (List.mem_filter.mp hPair).1
  have hPre : PreAvailablePair B μ u (Real.log u/200) (fourPhaseDepth u+1) (q,r) y := of_decide_eq_true hPreMem.2
  have hAdjacent := hPreMem.1
  have hMembers := adjacentOccurrences_members hAdjacent
  have hq := hMembers.1
  have hr := hMembers.2
  have hqCand := hPre.1
  have hrCand := hPre.2.1
  have W := hWindow B μ y hB hU hμ hCap hy
  have hA : 0 < A := W.2.2.1
  have hSc := hScale κ B μ y h q hκ hB hBκ hU hμ hCap hy hq hqCand.1
  obtain ⟨p,hp,hp0,hpB,hPhi,hpU,hNeg⟩ := hUpper κ B μ y h q hκ.le hB hU hμ hCap hy hq hqCand
  obtain ⟨pR,hpR,hpR0,hpRB,hPhiR,hpRU,hNegR⟩ := hUpper κ B μ y h r hκ.le hB hU hμ hCap hy hr hrCand
  obtain ⟨a,b,hqa,hrb,hOrd⟩ := hOrdinary κ B cap μ y (Real.log u/200) (d+1) h hκ hB hBκ hU hμ hCap hy s q r hPair
  have hPhaseQ : a = ⟨q.node.source.word,p.pivot,p.pivotIndex⟩ := by
    have he : q.phase? = some (⟨q.node.source.word,p.pivot,p.pivotIndex⟩ : CutPhase) := by
      simp only [LinkedGap.phase?,hp,Option.map_some]
    exact Option.some.inj (hqa.symm.trans he)
  have hPhaseR : b = ⟨r.node.source.word,pR.pivot,pR.pivotIndex⟩ := by
    have he : r.phase? = some (⟨r.node.source.word,pR.pivot,pR.pivotIndex⟩ : CutPhase) := by
      simp only [LinkedGap.phase?,hpR,Option.map_some]
    exact Option.some.inj (hrb.symm.trans he)
  have hGoodOrd := s.assembly.ordinaryPairs_good s.wellFormed _ hOrd
  have Wq : OrdinaryPhaseParameters A μ p.pivot T P q.node.source.word := by
    have hh := @of_decide_eq_true _ (Classical.propDecidable _) hGoodOrd.1
    simpa only [hPhaseQ] using hh
  have Wr : OrdinaryPhaseParameters A μ pR.pivot T P r.node.source.word := by
    have hh := @of_decide_eq_true _ (Classical.propDecidable _) hGoodOrd.2
    simpa only [hPhaseR] using hh
  have hqMem := linkedFrontier_internal_mem hq (bandGoodBool_internal hqCand.1.1)
  have hCart := indexedTree_source_cartesian (cartesian_valid h) hqMem
  have hDom := linkedFrontier_word_le_following (cartesian_valid h) hq hp
  have hBalanced := (hBalance κ B μ h q.node (d+3) hκ hB hBκ hU hμ hCap hqMem hPre.2.2).2
  have hBalanced' : balancedThrough (logarithmicStep μ) (4*bandTolerance u) (d+2) q.node.source :=
    (balancedThrough_capped hSc.2.2.2.2).mp (balancedThrough_prefix (k:=1) hBalanced)
  have hNearActual := hNear B μ y (q.node.source.prefixMass (logarithmicStep μ)) hB hU hμ hCap hy hSc.2.2.2.1
  have hBudgets := hBudget B μ y hB hU hμ hCap hy
  have hLower := band_local_lower_scale_bounds u A (q.node.source.prefixMass (logarithmicStep μ))
    q.node.pivot hA hSc.2.2.1 hSc.1
  have hUNonneg : 0 ≤ U := hp0.le.trans hpU
  have hNegBudget := mul_le_mul_of_nonneg_left hNeg (show 0 ≤ 2*U by positivity)
  obtain ⟨i,hi,hRoot,hNr,hLroot,hMuMass⟩ := hRight κ B μ y h r hκ hB hBκ hU hμ hCap hy hr hrCand
  obtain ⟨pM,hpM,hMr⟩ := hMass κ B μ y (Real.log u/200) h q r hκ hB hBκ hU hμ hCap hAdjacent hqCand
  have heM : pM = p := Option.some.inj (hpM.symm.trans hp)
  subst pM
  obtain ⟨pD,hpD,hDrawdown⟩ := hDraw κ B μ y (Real.log u/200) h q hq hqCand
  have heD : pD = p := Option.some.inj (hpD.symm.trans hp)
  subst pD
  obtain ⟨pG,hpG,hGoodP,_⟩ := hqCand.2
  have heG : pG = p := Option.some.inj (hpG.symm.trans hp)
  subst pG
  have hEligibleP := hEligible B μ p.pivot p.pivotIndex hB hU hμ hCap
    (bandProtectedPredicate_eligible ((bandGoodBool_iff B μ u p).mp hGoodP).2)
  have hP : 1 ≤ P := Real.one_le_exp_iff.mpr (by positivity)
  have hMuPivot := (mul_le_mul_of_nonneg_left hpB hμ.le).trans hμB
  have hTolerance : 0 ≤ 4*bandTolerance u := by
    unfold bandTolerance
    positivity
  have H := hExtension A (hMinimum B μ y hB hU hμ hCap hy) μ B (4*bandTolerance u) L U
    p.pivot pR.pivot T P d q.node.source r.node.source.word hμ (zero_lt_one.trans hB).le hμB hMuPivot
    hTolerance hNearActual hCart hSc.2.2.2.2 hp0 hDom hBalanced' hBudgets.1 hLower.2.1 hpU
    (hNeg.trans hBudgets.2.1) (hNegBudget.trans hBudgets.2.2.1) hBudgets.2.2.2 Wr i hRoot hNr hLroot
    hMuMass hMr Wq hP hEligibleP.2.2.2 hDrawdown
  refine ⟨a,b,hqa,hrb,hOrd,?_⟩
  have hFollowing : q.followingStep 0 = p.pivot := by simp only [LinkedGap.followingStep,hp,Option.map_some,Option.getD_some]
  simpa only [PairTraceExtension,hPhaseQ,hPhaseR,CutPhase.word,bandPairScore,hFollowing,A,L,U,P,T,d] using H

end
end StrongSilver
