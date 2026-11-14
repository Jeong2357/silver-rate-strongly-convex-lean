-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.BandFarChildRate
import StrongSilver.BandBinGeometry
import StrongSilver.FiniteHeightBins

namespace StrongSilver
open ScheduleTree Real Filter Set
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 6800000

def parentHeightBin (φ : ℝ → ℝ) (P : ℝ) (q : ParentedScheduleNode) : ℕ :=
  match q.parent with
  | none => 0
  | some p => Nat.floor (nodePaddedHeight φ P p)

def FarProtectedChild (φ : ℝ → ℝ) (P a b δ width : ℝ) (q : ParentedScheduleNode) : Prop :=
  ∃ p : ScheduleNode, q.parent = some p ∧ PaddedBalanced φ P p.reserve δ p.source ∧ p.reserve = 0 ∧
    P ≤ (φ p.pivot-P)/4 ∧ a+width < nodePaddedHeight φ P p ∧ nodePaddedHeight φ P p ≤ b ∧
    φ q.node.pivot ≤ P+Real.exp (nodePaddedHeight φ P p-width)

theorem parentWeight_nonnegative (φ : ℝ → ℝ) (P : ℝ) (q : ParentedScheduleNode) : 0 ≤ parentWeight φ P q := by
  cases hp : q.parent with
  | none => simp only [parentWeight,hp,le_refl]
  | some p => simpa only [parentWeight,hp] using (Real.exp_pos (nu*nodePaddedHeight φ P p)).le

/-- Summation of the far-child charge over the actual unit height bins.
The number of bins is O(u), and nu<4/5 gives the u^(9/10) bound in (4.23). -/
theorem eventually_band_far_children_sum : ∃ C > 0, ∀ᶠ u : ℝ in atTop,
    ∀ κ B cap μ : ℝ, ∀ h : List ℝ,
    1 < B → B ≤ cap → u ≤ firstAverageLogScale B → 0 < μ → μ*B ≤ 1/2 →
    (((parentedNodes 0 κ none (cartesian h)).filter fun q =>
      @decide (FarProtectedChild (cappedStep μ B) (bandPad u) (outerBandLow u) (protectedBandHigh u)
        (bandTolerance u) (bandBinWidth u) q) (Classical.propDecidable _)).map
        (parentWeight (cappedStep μ B) (bandPad u))).sum ≤ C*weightedCount h cap*u^((9:ℝ)/10) := by
  classical
  obtain ⟨C,hC,H⟩ := eventually_band_far_child_rate
  refine ⟨3*C,mul_pos (by norm_num) hC,?_⟩
  filter_upwards [H,eventually_band_bin_geometry,eventually_ge_atTop (1:ℝ)] with u hFar hGeometry hu
  intro κ B cap μ h hB hBcap hU hμ hμB
  obtain ⟨ha,hb,hw,hN,hGeometry⟩ := hGeometry
  let φ := cappedStep μ B
  let P := bandPad u
  let xs := parentedNodes 0 κ none (cartesian h)
  let sel := fun q : ParentedScheduleNode => decide (FarProtectedChild φ P (outerBandLow u) (protectedBandHigh u)
    (bandTolerance u) (bandBinWidth u) q)
  let ys := xs.filter sel
  let key := parentHeightBin φ P
  let cost := parentWeight φ P
  let N := bandBinCount u
  let E := C*weightedCount h cap*u^(-(1-nu)/2)
  have hu0 := zero_lt_one.trans_le hu
  have hE : 0 ≤ E := by have hW := weightedCount_nonneg h cap; dsimp only [E]; positivity
  have hKeys : ∀ q ∈ ys, key q < N := by
    intro q hq
    have Hq := of_decide_eq_true (List.mem_filter.mp hq).2
    obtain ⟨p,hp,_,_,_,hlo,hhi,_⟩ := Hq
    have hg := hGeometry (nodePaddedHeight φ P p) hlo hhi
    simpa only [key,parentHeightBin,hp,N] using hg.1
  have hBin (j : ℕ) : (((ys.filter fun q => decide (key q = j)).map cost).sum) ≤ E := by
    by_cases hex : ∃ q, q ∈ ys.filter (fun q => decide (key q = j))
    · obtain ⟨q₀,hq₀⟩ := hex
      obtain ⟨hys₀,hkey₀⟩ := List.mem_filter.mp hq₀
      have hsel₀ := of_decide_eq_true (List.mem_filter.mp hys₀).2
      obtain ⟨p₀,hp₀,_,_,_,hlo₀,hhi₀,_⟩ := hsel₀
      have hg₀ := hGeometry (nodePaddedHeight φ P p₀) hlo₀ hhi₀
      have hj₀ : Nat.floor (nodePaddedHeight φ P p₀) = j := by
        simpa only [key,parentHeightBin,hp₀] using (of_decide_eq_true hkey₀)
      have hy : (j:ℝ)+1-bandBinWidth u ∈ Icc (outerBandLow u) (outerBandHigh u) := by simpa only [hj₀] using hg₀.2.2.2
      have hFarBin := hFar κ B cap μ (j:ℝ) h hB hBcap hU hμ hμB hy
      have hDom := list_filtered_sum_domination (fun q => sel q && decide (key q = j))
        (fun q => decide (FarChildAt φ P (bandTolerance u) (j:ℝ) (bandBinWidth u) q)) cost cost xs
        (fun q _ => parentWeight_nonnegative φ P q) (by
          intro q hq hqsel
          have hs : sel q = true ∧ decide (key q = j) = true := by simpa only [Bool.and_eq_true] using hqsel
          obtain ⟨p,hp,hbal,hres,hsmall,hlo,hhi,hchild⟩ := of_decide_eq_true hs.1
          have hg := hGeometry (nodePaddedHeight φ P p) hlo hhi
          have hj : Nat.floor (nodePaddedHeight φ P p) = j := by
            simpa only [key,parentHeightBin,hp] using (of_decide_eq_true hs.2)
          have hjlo : (j:ℝ) ≤ nodePaddedHeight φ P p := by simpa only [hj] using hg.2.1
          have hjhi : nodePaddedHeight φ P p < (j:ℝ)+1 := by simpa only [hj] using hg.2.2.1
          have hChildUpper := add_le_add (le_refl P) (Real.exp_le_exp.mpr (sub_le_sub_right hjhi.le (bandBinWidth u)))
          refine ⟨decide_eq_true ⟨p,hp,hbal,hres,hsmall,hjlo,hjhi,hchild.trans hChildUpper⟩,le_rfl⟩)
      have hDom' : (((ys.filter fun q => decide (key q = j)).map cost).sum) ≤
          (((parentedNodes 0 κ none (cartesian h)).filter fun q => decide
            (FarChildAt φ P (bandTolerance u) (j:ℝ) (bandBinWidth u) q)).map cost).sum := by
        simpa only [ys,xs,List.filter_filter,Bool.and_comm] using hDom
      exact hDom'.trans hFarBin
    · have hz : (((ys.filter fun q => decide (key q = j)).map cost).sum) = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hx
        exact False.elim (hex ⟨q,hq⟩)
      rw [hz]
      exact hE
  have hSum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range N) => hBin j)
  rw [list_sum_by_nat_bins ys key cost N hKeys] at hSum
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hSum
  have hNMul := mul_le_mul_of_nonneg_right hN hE
  have hPower : u*u^(-(1-nu)/2) ≤ u^((9:ℝ)/10) := by
    have hp := Real.rpow_le_rpow_of_exponent_le hu (show 1+(-(1-nu)/2) ≤ (9:ℝ)/10 by linarith only [nu_lt_four_fifths])
    rwa [Real.rpow_add hu0,Real.rpow_one] at hp
  have hRate := mul_le_mul_of_nonneg_left hPower (mul_nonneg (mul_pos (by norm_num : (0:ℝ) < 3) hC).le (weightedCount_nonneg h cap))
  change (ys.map cost).sum ≤ _
  dsimp only [N,E] at hSum hNMul
  linear_combination hSum+hNMul+hRate

end
end StrongSilver
