-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.IntervalGraphInverse

namespace StrongSilver
open Set
noncomputable section

theorem intervalGraphInverse_antitoneOn {a b : ℝ} {X : ℝ → ℝ} (hab : a ≤ b)
    (hc : ContinuousOn X (Icc a b)) (hs : StrictAntiOn X (Icc a b)) :
    AntitoneOn (intervalGraphInverse hab hc hs) (Icc (X b) (X a)) := by
  intro y hy z hz hyz
  by_contra hn
  have hlt : intervalGraphInverse hab hc hs y < intervalGraphInverse hab hc hs z := lt_of_not_ge hn
  have hh := hs (intervalGraphInverse_mem hab hc hs y) (intervalGraphInverse_mem hab hc hs z) hlt
  rw [intervalGraphInverse_right_inverse hab hc hs hy,intervalGraphInverse_right_inverse hab hc hs hz] at hh
  exact not_lt_of_ge hyz hh

theorem intervalGraphInverse_mem_interior {a b y : ℝ} {X : ℝ → ℝ} (hab : a ≤ b)
    (hc : ContinuousOn X (Icc a b)) (hs : StrictAntiOn X (Icc a b))
    (hy : y ∈ Ioo (X b) (X a)) : intervalGraphInverse hab hc hs y ∈ Ioo a b := by
  have ht := intervalGraphInverse_mem hab hc hs y
  have hi := intervalGraphInverse_right_inverse hab hc hs (Ioo_subset_Icc_self hy)
  have ha : a ≠ intervalGraphInverse hab hc hs y := by
    intro he
    rw [← he] at hi
    linarith [hy.2]
  have hb : intervalGraphInverse hab hc hs y ≠ b := by
    intro he
    rw [he] at hi
    linarith [hy.1]
  exact ⟨lt_of_le_of_ne ht.1 ha,lt_of_le_of_ne ht.2 hb⟩

end
end StrongSilver
