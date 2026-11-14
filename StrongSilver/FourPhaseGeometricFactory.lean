-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseGainBox
import StrongSilver.FourPhaseLogNorm
import StrongSilver.FourPhaseNeighborhood

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 3000000

/-- Closed geometric part of Lemma 4.1: the four slopes and starting point
are constructed from the masses and excesses. Regularity, every inter-plane
query comparison and the quantitative logarithmic gain are conclusions. -/
theorem exists_four_phase_geometry : ∃ C > 0, ∃ δ > 0,
    ∀ ε : ℝ, 0 ≤ ε → ε ≤ δ → ∀ x : Shape,
    (∀ i : Fin 8, i ≠ 7 → |x i-reference i| ≤ ε) →
    0 ≤ x 7 → x 7 ≤ δ →
    Regular x ∧ source x ≠ 0 ∧
    (∀ i j : Fin 4, ∀ s c : ℝ, 0 ≤ s → 0 ≤ c →
      inner ℝ (slope x j) (c • (foot x i+s • slope x i)) ≤
      inner ℝ (slope x i) (c • (foot x i+s • slope x i))) ∧
    gain x+(gain x+gainLeft x+gainRight x)/Real.sqrt 2-
      C*ε*(|gain x|+|gainLeft x|+|gainRight x|)-C*x 7 ≤
        Real.log (totalMass x^2/‖source x‖^2) := by
  obtain ⟨K,hK,d,hd,hgains⟩ := exists_gain_box
  obtain ⟨b,hb,hregular⟩ := exists_regular_box
  let δ := min b (min d (min (1/K) (1/4)))
  let C := 4*K+3
  have hδ : 0 < δ := lt_min hb (lt_min hd (lt_min (one_div_pos.mpr hK) (by norm_num)))
  have hC : 0 < C := by dsimp [C]; linarith only [hK]
  refine ⟨C,hC,δ,hδ,fun ε hε hεδ x hx hz hzd => ?_⟩
  have hδb : δ ≤ b := min_le_left _ _
  have hδd : δ ≤ d := (min_le_right _ _).trans (min_le_left _ _)
  have hδK : δ ≤ 1/K := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ4 : δ ≤ 1/4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have R : Regular x := hregular x (by
    intro i
    by_cases hi : i = 7
    · subst i; rw [reference_zeta,sub_zero,abs_of_nonneg hz]; exact hzd.trans hδb
    · exact (hx i hi).trans (hεδ.trans hδb))
  have hKε : K*ε ≤ 1 := by
    have hh := (le_div_iff₀ hK).mp (hεδ.trans hδK)
    nlinarith only [hh]
  obtain ⟨hg,hv,hclose⟩ := hgains ε hε (hεδ.trans hδd) x hx
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt1 : 1 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hc01 : 1/Real.sqrt 2 ≤ 1 := (div_le_one hsqrt).mpr hsqrt1
  have hc2 : gainCoefficient x ≤ 2 := by
    have hc := (le_abs_self (gainCoefficient x-1/Real.sqrt 2)).trans hclose
    linarith only [hc,hc01,hKε]
  have he4 : ε ≤ 1/4 := hεδ.trans hδ4
  have hx0 : |x 0-1| ≤ ε := by simpa only [reference_m0] using hx 0 (by decide)
  have hx3 : |x 3-1| ≤ ε := by simpa only [reference_m3] using hx 3 (by decide)
  have hm3 : 1/2 ≤ x 3 := by have hh := (abs_le.mp hx3).1; linarith only [hh,he4]
  have hsum : x 0+x 3 ≤ totalMass x := by
    dsimp only [totalMass,leftMass,rightMass]
    linarith only [R.k0_positive,R.m1_positive,R.k1_positive,R.m2_positive,R.k2_positive]
  have hM : 1 ≤ totalMass x := by
    have hh0 := (abs_le.mp hx0).1
    have hh3 := (abs_le.mp hx3).1
    linarith only [hsum,hh0,hh3,he4]
  have hmain := log_norm_gain_lower R hK.le hε hKε hc2 hg hv hclose hz hm3 hM
  refine ⟨R,source_nonzero R,fun i j s c hs hc => query_dominates R hz i j hs hc,?_⟩
  have hS : 0 ≤ |gain x|+|gainLeft x|+|gainRight x| := by positivity
  have hprice := mul_nonneg (mul_nonneg hε hS) (show 0 ≤ C-4*K by dsimp [C]; linarith)
  have hzprice := mul_nonneg hz (show 0 ≤ C-3 by dsimp [C]; linarith only [hK])
  nlinarith only [hmain,hprice,hzprice]

end
end StrongSilver.FourPhase
