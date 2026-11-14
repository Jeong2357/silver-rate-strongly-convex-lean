-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ConcaveExtrapolation

namespace StrongSilver
open Set Filter
open scoped Topology
noncomputable section

def extensionSlope (a b : ℝ) (d : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x < a then d a else if b < x then d b else d x

theorem tangentLine_hasDerivAt (f d : ℝ → ℝ) (s x : ℝ) :
    HasDerivAt (tangentLine f d s) (d s) x := by
  have hh := (((hasDerivAt_id x).sub_const s).const_mul (d s)).const_add (f s)
  convert! hh using 1 <;> ring

theorem linearConcaveExtension_hasDerivAt {a b : ℝ} (hab : a < b) {f d : ℝ → ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (d x) (Icc a b) x) (x : ℝ) :
    HasDerivAt (linearConcaveExtension a b f d) (extensionSlope a b d x) x := by
  let E := linearConcaveExtension a b f d
  have hmid (y : ℝ) (hy : y ∈ Icc a b) : HasDerivWithinAt E (d y) (Icc a b) y :=
    (hd y hy).congr_of_mem (fun z hz => linearConcaveExtension_on_interval hz) hy
  by_cases hx : x < a
  · rw [extensionSlope,if_pos hx]
    apply (tangentLine_hasDerivAt f d a x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with z hz
    exact linearConcaveExtension_left hab.le f d hz.le
  · by_cases hx' : b < x
    · rw [extensionSlope,if_neg hx,if_pos hx']
      apply (tangentLine_hasDerivAt f d b x).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hx'] with z hz
      exact linearConcaveExtension_right hab.le f d hz.le
    · rw [extensionSlope,if_neg hx,if_neg hx']
      have hxIcc : x ∈ Icc a b := ⟨le_of_not_gt hx,le_of_not_gt hx'⟩
      by_cases hxa : x = a
      · subst x
        have hl : HasDerivWithinAt E (d a) (Iic a) a :=
          (tangentLine_hasDerivAt f d a a).hasDerivWithinAt.congr_of_mem
            (fun z hz => linearConcaveExtension_left hab.le f d hz) (show a ∈ Iic a from le_refl a)
        have hr : HasDerivWithinAt E (d a) (Ici a) a :=
          (hmid a ⟨le_rfl,hab.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hab)
        have hh := hl.union hr
        simpa only [Iic_union_Ici,hasDerivWithinAt_univ] using hh
      · by_cases hxb : x = b
        · subst x
          have hl : HasDerivWithinAt E (d b) (Iic b) b :=
            (hmid b ⟨hab.le,le_rfl⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hab)
          have hr : HasDerivWithinAt E (d b) (Ici b) b :=
            (tangentLine_hasDerivAt f d b b).hasDerivWithinAt.congr_of_mem
              (fun z hz => linearConcaveExtension_right hab.le f d hz) (show b ∈ Ici b from le_refl b)
          have hh := hl.union hr
          simpa only [Iic_union_Ici,hasDerivWithinAt_univ] using hh
        · have ha : a < x := lt_of_le_of_ne hxIcc.1 (Ne.symm hxa)
          have hb : x < b := lt_of_le_of_ne hxIcc.2 hxb
          exact (hmid x hxIcc).hasDerivAt (Icc_mem_nhds ha hb)

theorem linearConcaveExtension_continuous {a b : ℝ} (hab : a < b) {f d : ℝ → ℝ}
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt f (d x) (Icc a b) x) :
    Continuous (linearConcaveExtension a b f d) :=
  continuous_iff_continuousAt.mpr (fun x => (linearConcaveExtension_hasDerivAt hab hd x).continuousAt)

end
end StrongSilver
