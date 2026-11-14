-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Schedules
import StrongSilver.Constants

namespace StrongSilver
noncomputable section
open scoped BigOperators

def countAbove (h : List ℝ) (s : ℝ) : ℕ :=
  (h.filter (fun b => decide (s ≤ b))).length

@[simp] theorem countAbove_nil (s : ℝ) : countAbove [] s = 0 := rfl

theorem countAbove_cons (a : ℝ) (h : List ℝ) (s : ℝ) :
    countAbove (a :: h) s = (if s ≤ a then 1 else 0) + countAbove h s := by
  by_cases hs : s ≤ a <;> simp [countAbove, hs, Nat.add_comm]

theorem countAbove_le_length (h : List ℝ) (s : ℝ) : countAbove h s ≤ h.length :=
  List.length_filter_le _ _

theorem countAbove_mono_on (h : List ℝ) (s t : ℝ)
    (hm : ∀ b ∈ h, t ≤ b → s ≤ b) : countAbove h t ≤ countAbove h s := by
  induction h with
  | nil => simp
  | cons a h ih =>
    have ht := ih (fun b hb => hm b (by simp [hb]))
    rw [countAbove_cons, countAbove_cons]
    by_cases hs : s ≤ a <;> by_cases ha : t ≤ a
    · simp only [hs, ha, if_true]; omega
    · simp only [hs, ha, if_true, if_false]; omega
    · exact False.elim (hs (hm a (by simp) ha))
    · simpa only [hs, ha, if_false, zero_add] using ht

theorem countAbove_antitone (h : List ℝ) : Antitone (countAbove h) := by
  intro s t hst
  exact countAbove_mono_on h s t (fun _ _ hb => hst.trans hb)

theorem countAbove_append (h k : List ℝ) (s : ℝ) :
    countAbove (h ++ k) s = countAbove h s + countAbove k s := by
  simp [countAbove, List.filter_append]

theorem countAbove_repeat (h : List ℝ) (r : ℕ) (s : ℝ) :
    countAbove (repeatSchedule h r) s = r * countAbove h s := by
  induction r with
  | zero => simp [repeatSchedule]
  | succ r ih => simp only [repeatSchedule, countAbove_append, ih, Nat.succ_mul]

def maxWeight (l : List ℝ) : ℝ := l.foldr max 0

theorem maxWeight_nonneg (l : List ℝ) : 0 ≤ maxWeight l := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih => exact ih.trans (le_max_right a (maxWeight l))

theorem le_maxWeight {l : List ℝ} {a : ℝ} (ha : a ∈ l) : a ≤ maxWeight l := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_max_left _ _
    · exact (ih ha).trans (le_max_right _ _)

theorem maxWeight_le {l : List ℝ} {a : ℝ} (ha : 0 ≤ a) (hl : ∀ b ∈ l, b ≤ a) :
    maxWeight l ≤ a := by
  induction l with
  | nil => exact ha
  | cons b l ih =>
    exact max_le (hl b (by simp)) (ih (fun c hc => hl c (by simp [hc])))

def candidateWeight (h : List ℝ) (cap b : ℝ) : ℝ :=
  if 0 < min b cap then (min b cap)^nu * (countAbove h (min b cap) : ℝ) else 0

/-- A finite maximum, equal to max_{0<s≤cap} s^ν N(s) for cap>0. -/
def weightedCount (h : List ℝ) (cap : ℝ) : ℝ :=
  maxWeight (h.map (candidateWeight h cap))

theorem weightedCount_nonneg (h : List ℝ) (cap : ℝ) : 0 ≤ weightedCount h cap :=
  maxWeight_nonneg _

theorem candidate_le_weightedCount (h : List ℝ) (cap : ℝ) {b : ℝ} (hb : b ∈ h) :
    candidateWeight h cap b ≤ weightedCount h cap :=
  le_maxWeight (List.mem_map.mpr ⟨b, hb, rfl⟩)

theorem threshold_le_weightedCount (h : List ℝ) {s cap : ℝ} (hs : 0 < s) (hcap : s ≤ cap) :
    s^nu * (countAbove h s : ℝ) ≤ weightedCount h cap := by
  classical
  by_cases hn : countAbove h s = 0
  · simpa only [hn, Nat.cast_zero, mul_zero] using weightedCount_nonneg h cap
  let selected := h.toFinset.filter (fun b => s ≤ b)
  have hselected : selected.Nonempty := by
    by_contra hempty
    have hnone : ∀ b ∈ h, ¬s ≤ b := by
      intro b hb hsb
      apply hempty
      exact ⟨b, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hb, hsb⟩⟩
    have hz : countAbove h s = 0 := by
      simp only [countAbove, List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro b hb
      simp [hnone b hb]
    exact hn hz
  let b := selected.min' hselected
  have hb : b ∈ selected := Finset.min'_mem _ _
  have hbdata := Finset.mem_filter.mp hb
  have hbh : b ∈ h := List.mem_toFinset.mp hbdata.1
  have hsb : s ≤ b := hbdata.2
  have hB : s ≤ min b cap := le_min hsb hcap
  have hBpos : 0 < min b cap := hs.trans_le hB
  have hN : countAbove h s ≤ countAbove h (min b cap) := by
    apply countAbove_mono_on
    intro c hc hsc
    have hcmem : c ∈ selected := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hc, hsc⟩
    exact (min_le_left b cap).trans (Finset.min'_le _ _ hcmem)
  calc
    s^nu * (countAbove h s : ℝ) ≤ (min b cap)^nu * (countAbove h (min b cap) : ℝ) := by
      apply mul_le_mul (Real.rpow_le_rpow hs.le hB nu_positive.le)
      · exact_mod_cast hN
      · positivity
      · positivity
    _ = candidateWeight h cap b := by simp [candidateWeight, hBpos]
    _ ≤ weightedCount h cap := candidate_le_weightedCount h cap hbh

end
end StrongSilver
