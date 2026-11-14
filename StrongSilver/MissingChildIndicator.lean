-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.GoodThroughFailure
import StrongSilver.BandGoodNode

namespace StrongSilver
open ScheduleTree BinaryForest Real
noncomputable section
set_option maxHeartbeats 5200000

def missingGoodChildIndicator (G : ScheduleNode → Bool) (q : ScheduleNode) : ℝ :=
  missingGoodChildWeight G (fun _ => 1) q

theorem missingGoodChildIndicator_nonnegative (G : ScheduleNode → Bool) (q : ScheduleNode) :
    0 ≤ missingGoodChildIndicator G q := by
  unfold missingGoodChildIndicator missingGoodChildWeight
  cases hs : q.source with
  | leaf word => simp only [hs,le_refl]
  | split l b r => simp only [hs]; split_ifs <;> norm_num

theorem missingGoodChildIndicator_weight (G : ScheduleNode → Bool) (w : ScheduleNode → ℝ) (q : ScheduleNode) :
    w q*missingGoodChildIndicator G q = missingGoodChildWeight G w q := by
  unfold missingGoodChildIndicator missingGoodChildWeight
  cases hs : q.source with
  | leaf word => simp only [hs,mul_zero]
  | split l b r => simp only [hs]; split_ifs <;> simp

theorem indexedTree_rootGood (G : ScheduleNode → Bool)
    (hLeaf : ∀ start κ word, G ⟨start,.leaf word,κ⟩ = false) (start : ℕ) (κ : ℝ) (t : ScheduleTree) :
    rootGood G (t.indexedTree start κ) = G ⟨start,t,κ⟩ := by
  cases t with
  | leaf word => exact (hLeaf start κ word).symm
  | split l b r => rfl

theorem bandGoodBool_leaf_false (B μ u : ℝ) (start : ℕ) (κ : ℝ) (word : List ℝ) :
    bandGoodBool B μ u ⟨start,.leaf word,κ⟩ = false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  exact ((bandGoodBool_iff B μ u _).mp hh).1

/-- The abstract shortest-failure-path charge uses the same actual
missing-child indicator already controlled by (4.23). -/
theorem indexedTree_missing_good_charge (G : ScheduleNode → Bool)
    (hLeaf : ∀ start κ word, G ⟨start,.leaf word,κ⟩ = false)
    (start : ℕ) (κ : ℝ) (t : ScheduleTree) :
    GoodMissingCharge G (missingGoodChildIndicator G) (t.indexedTree start κ) := by
  induction t generalizing start κ with
  | leaf word => trivial
  | split l b r il ir =>
    refine ⟨?_,il start 0,ir (start+l.word.length+1) κ⟩
    intro hg hbad
    have hb : ¬ (G ⟨start,l,0⟩ = true ∧ G ⟨start+l.word.length+1,r,κ⟩ = true) := by
      simpa only [indexedTree_rootGood G hLeaf] using hbad
    have hh : G (⟨start,.split l b r,κ⟩ : ScheduleNode) = true ∧
        ¬ (G ⟨start,l,0⟩ = true ∧ G ⟨start+l.word.length+1,r,κ⟩ = true) := ⟨hg,hb⟩
    change 1 ≤ if G (⟨start,.split l b r,κ⟩ : ScheduleNode) = true ∧
        ¬ (G ⟨start,l,0⟩ = true ∧ G ⟨start+l.word.length+1,r,κ⟩ = true) then (1:ℝ) else 0
    rw [if_pos hh]

end
end StrongSilver
