-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianDepthTrace
import StrongSilver.TransformedRootMass

namespace StrongSilver
open Real Filter Scalar.SignedIntervals
open ScheduleTree ScheduleTree.FourGapGroup
open scoped Topology
noncomputable section
set_option maxHeartbeats 4800000

/-- Actual finite two-gap construction. One ordinary right gap supplies
its retained scale and vanishing offset; the original balanced left gap
is then extended by the complete depth construction. The output has the
original signed word, renewed working gate and uniform working caps. -/
theorem eventually_two_gap_trace : ∃ C > 0, ∃ τ > 0, ∃ c > 0, ∀ᶠ A : ℝ in atTop,
    ∀ μ B ε L U bv br T P : ℝ, ∀ d : ℕ, ∀ t : ScheduleTree, ∀ hr : List ℝ,
    0 < μ → 0 ≤ B → μ*B ≤ 1/10000 → μ*bv ≤ 1/10000 → 0 ≤ ε →
    ε+μ*t.prefixMass (logarithmicStep μ) ≤ τ →
    t.Cartesian → (∀ s ∈ t.word, s ≤ B) → 0 < bv → (∀ s ∈ t.word, s ≤ bv) →
    balancedThrough (logarithmicStep μ) ε (d+2) t →
    1000 ≤ L → L ≤ (1/4:ℝ)^(d+2)*t.prefixMass (logarithmicStep μ) → bv ≤ U →
    negativeMass t.word ≤ L/1000 → 2*U*negativeMass t.word ≤ c*L^2 →
    2*U*A^(-(1:ℝ)/20) ≤ c*L →
    OrdinaryPhaseParameters A μ br T P hr →
    ∀ i : Fin hr.length, A^((499:ℝ)/500) ≤ hr.get i → negativeMass hr ≤ hr.get i/16 →
    64*L ≤ hr.get i → μ*transformedGapMaximum μ hr ≤ 1/1000 →
    transformedGapMaximum μ hr+1 ≤ (14/5:ℝ)*cappedStep μ B bv →
    ∀ s : List ℝ, ∀ Mo Go r : ℝ, PositiveTrace μ s (workingGateFraction A) Mo Go r →
    ∃ qs : List Group, ∃ Z : ℝ, 0 ≤ Z ∧ Z ≤ A^(-(1:ℝ)/20) ∧
      qs.map (fun q => (q.1.tree,q.2)) = depthPhases d t bv ∧
      Nonempty (PositiveTrace μ ((t.word++[bv])++((hr++[br])++s)) (workingGateFraction A)
        (A^(10:ℝ)) (A^(10:ℝ))
        ((r*(ordinaryReferenceFactor A μ br P hr)^2)*sequenceRate C μ B ε (workingGateFraction A) qs Z)) := by
  obtain ⟨C,hC,τ,hτ,c,hc,hdepth⟩ := balanced_depth_trace
  have hgateLimit : Tendsto workingGateFraction atTop (𝓝 0) := by
    change Tendsto (fun A : ℝ => A^(-(67:ℝ)/500)) atTop (𝓝 0)
    simpa only [neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 67/500))
  have hgate := ((tendsto_order.1 hgateLimit).2 c hc).mono (fun _ h => h.le)
  refine ⟨C,hC,min τ (1/100),lt_min hτ (by norm_num),c,hc,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_ordinary_root_trace,
    eventually_ordinary_root_planar_scale,hgate,
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 10)).eventually (eventually_ge_atTop (26:ℝ))]
    with A hA hright hscale hgate hA10
  intro μ B ε L U bv br T P d t hr hμ hB hμB hμbv hε hnear hcart hword hbv hdom hbal hL hLdepth hbU hN hNbudget
    hZbudget W i hroot hNr hLroot hμmr hMr s Mo Go r Q
  obtain ⟨e,he,K,M,G,heq,hZ,⟨R⟩⟩ := hright μ br T P hr W i hroot hNr s Mo Go r Q
  have hnorm := hscale μ br T e hr K i hroot hNr hμmr
  have hHlow : L ≤ ‖K.R‖/8 := by linarith only [hnorm.1,hLroot]
  have hHup : ‖K.R‖/8 ≤ (9/20:ℝ)*cappedStep μ B bv := by
    have hφ := cappedStep_ge hμ (show μ*B < 1 by linarith only [hμB]) bv
    have hφpos : 0 < cappedStep μ B bv := hbv.trans_le hφ
    nlinarith only [hnorm.2,hMr,hφpos]
  have hη : 0 ≤ workingGateFraction A := (Real.rpow_pos_of_pos hA _).le
  obtain ⟨qs,hqs,⟨J⟩⟩ := hdepth μ B ε L U (A^(-(1:ℝ)/20)) (workingGateFraction A) d t bv
    hμ hB hμB hμbv hε (hnear.trans (min_le_left _ _)) hcart hword hbv hdom hbal hL hLdepth hbU hN hNbudget hη hgate hZbudget
    (‖K.R‖/8) _ (workingGateFraction A) M G (r*(ordinaryReferenceFactor A μ br P hr)^2) ((hr++[br])++s)
    R hHlow hHup hZ
  have hε100 : ε ≤ 1/100 := by
    have hh := hnear.trans (min_le_right _ _)
    have hm := mul_nonneg hμ.le (prefixMass_positive (logarithmicStep μ) t).le
    linarith only [hh,hm]
  have hfirst : L ≤ firstScale μ qs (‖K.R‖/8) := by
    cases qs with
    | nil => exact hHlow
    | cons q tail =>
      have hq : q ∈ q::tail := by simp
      exact hLdepth.trans (depth_groups_scale_bounds hε100 hbal hqs hq).1
  have hGcap : 1/firstScale μ qs (‖K.R‖/8) ≤ A^(10:ℝ) := by
    have hscale1 : 1 ≤ firstScale μ qs (‖K.R‖/8) := by linarith only [hL,hfirst]
    have hinv : 1/firstScale μ qs (‖K.R‖/8) ≤ 1 := (div_le_one (by linarith only [hscale1])).mpr hscale1
    exact hinv.trans (by linarith only [hA10])
  exact ⟨qs,_,R.suffix_bounds.offset_nonnegative,hZ,hqs,
    ⟨J.toPositiveTrace.weaken le_rfl hA10 hGcap le_rfl⟩⟩

end
end StrongSilver
