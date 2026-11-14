-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SmoothPlanarUniform
import StrongSilver.LinearBoundaryBounds
import StrongSilver.RiccatiPerturbation

namespace StrongSilver
open Set Real
noncomputable section

def planarComparisonBound (Θ R k₀ : ℝ) : ℝ :=
  R*Real.exp (k₀*Θ)*Θ*Real.exp (inverseSlopePrimitive k₀ Θ)

def planarPerturbationSize (μ ε Θ R k₀ : ℝ) : ℝ :=
  3*μ*(1+k₀^2)/ε+18*μ*(1+k₀^2)*planarComparisonBound Θ R k₀/ε^2

/-- The concrete planar Riccati equation has a nonnegative bounded solution
whenever the displayed scalar smallness condition holds. That condition is
still to be discharged for the paper's A-dependent parameters. -/
theorem exists_smooth_planar_Riccati {μ ε Θ R k₀ : ℝ}
    (hμ : 0 ≤ μ) (hε : 0 < ε) (hk : 0 < k₀) (hk1 : k₀ ≤ 1/2) (hεk : ε ≤ k₀)
    (hΘeq : Θ = Real.arctan ε⁻¹) (hR : 1 ≤ R)
    (hsmall : (5 : ℝ)/4*Real.exp (planarPerturbationSize μ ε Θ R k₀*Θ) ≤ 2) :
    ∃ J : ℝ → ℝ, J Θ = 0 ∧ ∀ θ ∈ Icc (0 : ℝ) Θ,
      0 ≤ J θ ∧ J θ ≤ 2*planarComparisonBound Θ R k₀ ∧
      HasDerivWithinAt J
        (planarRiccati μ (explicitArcRadius Θ R k₀ θ) (smoothPlanarSlope k₀ θ)
          (smoothPlanarSlopeDeriv k₀ θ) (J θ)) (Icc (0 : ℝ) Θ) θ := by
  have hΘ0 : 0 ≤ Θ := by rw [hΘeq]; exact (Real.arctan_pos.mpr (inv_pos.mpr hε)).le
  have hΘ : Θ < Real.pi/2 := by rw [hΘeq]; exact Real.arctan_lt_pi_div_two _
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  let r := explicitArcRadius Θ R k₀
  let k := smoothPlanarSlope k₀
  let kp := smoothPlanarSlopeDeriv k₀
  let α₀ := fun θ => (k θ)⁻¹
  let α := fun θ => α₀ θ+planarLinearPerturbation μ (k θ)
  let β := fun θ => planarQuadraticPerturbation μ (r θ) (k θ) (kp θ)
  let M := planarComparisonBound Θ R k₀
  let δ := planarPerturbationSize μ ε Θ R k₀
  have hM : 0 ≤ M := by dsimp [M,planarComparisonBound]; positivity
  have hδ : 0 ≤ δ := by dsimp [δ,planarPerturbationSize]; positivity
  have hD (θ : ℝ) (ht : θ ∈ Icc (0 : ℝ) Θ) : 0 < Real.cos θ+2*k₀*Real.sin θ :=
    lt_of_lt_of_le (by linarith : 0 < 2*k₀) (smoothPlanar_denominator_lower hk hk1 ⟨ht.1,ht.2.trans hΘ.le⟩)
  have hkpos (θ : ℝ) (ht : θ ∈ Icc (0 : ℝ) Θ) : 0 < k θ :=
    (smoothPlanarSlope_bounds hk ht.1 (ht.2.trans_lt hΘ)).1
  have hrbound (θ : ℝ) (ht : θ ∈ Icc (0 : ℝ) Θ) : 1 ≤ r θ := by
    change 1 ≤ explicitArcRadius Θ R k₀ θ
    rw [explicitArcRadius_eq hk hk1 hΘ ht]
    apply hR.trans
    apply le_mul_of_one_le_right hR0
    apply Real.one_le_exp_iff.mpr
    apply intervalIntegral.integral_nonneg ht.2
    intro t htime
    exact (smoothPlanarSlope_bounds hk (ht.1.trans htime.1) (htime.2.trans_lt hΘ)).1.le
  have hcK (θ : ℝ) (ht : θ ∈ Icc (0 : ℝ) Θ) : ContinuousAt k θ :=
    (smoothPlanarSlope_hasDerivAt (hD θ ht).ne').continuousAt
  have hcR (θ : ℝ) (ht : θ ∈ Icc (0 : ℝ) Θ) : ContinuousAt r θ :=
    (explicitArcRadius_hasDerivAt (Θ := Θ) (R := R) (hD θ ht).ne').continuousAt
  have hcKP (θ : ℝ) (ht : θ ∈ Icc (0 : ℝ) Θ) : ContinuousAt kp θ := by
    have hp := hD θ ht
    exact continuousAt_const.div
      ((Real.continuous_cos.continuousAt.add (continuousAt_const.mul Real.continuous_sin.continuousAt)).pow 2)
      (pow_ne_zero 2 hp.ne')
  have hcα (θ : ℝ) (ht : θ ∈ Icc (0 : ℝ) Θ) : ContinuousAt α θ := by
    have hc := hcK θ ht
    have hp := hkpos θ ht
    dsimp [α,α₀,planarLinearPerturbation]
    fun_prop (disch := positivity)
  have hcβ (θ : ℝ) (ht : θ ∈ Icc (0 : ℝ) Θ) : ContinuousAt β θ := by
    have hck := hcK θ ht
    have hcr := hcR θ ht
    have hckp := hcKP θ ht
    have hkp := hkpos θ ht
    have hrp : 0 < r θ := zero_lt_one.trans_le (hrbound θ ht)
    dsimp [β,planarQuadraticPerturbation]
    fun_prop (disch := positivity)
  have hcoeff (θ : ℝ) (ht : θ ∈ Icc (0 : ℝ) Θ) :
      0 ≤ β θ ∧ α θ-α₀ θ+2*β θ*M ≤ δ := by
    have ht' : θ ∈ Icc (0 : ℝ) (Real.arctan ε⁻¹) := by simpa only [hΘeq] using ht
    have hmin := smoothPlanarSlope_uniform_lower hk hk1 hε hεk ht'
    obtain ⟨hks,hku,hkt⟩ := smoothPlanarSlope_bounds hk ht.1 (ht.2.trans_lt hΘ)
    obtain ⟨hkpmin,hkpmax⟩ := smoothPlanarSlopeDeriv_bounds hk hk1 ⟨ht.1,ht.2.trans hΘ.le⟩
    obtain ⟨hal,hbe⟩ := planar_perturbation_bounds hμ hε hmin hku hk.le hkpmin hkpmax.le (hrbound θ ht)
    have hmul := mul_le_mul_of_nonneg_right hbe.2 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)
    refine ⟨hbe.1,?_⟩
    dsimp only [α,β,k,kp,M,δ,planarPerturbationSize] at hmul ⊢
    simp only [div_eq_mul_inv] at hal hmul ⊢
    nlinarith only [hal.2,hmul]
  let flip := fun t : ℝ => Θ-t
  have hflip : MapsTo flip (Icc (0 : ℝ) Θ) (Icc (0 : ℝ) Θ) := by
    intro t ht
    change 0 ≤ Θ-t ∧ Θ-t ≤ Θ
    constructor <;> linarith [ht.1,ht.2]
  have hfc : Continuous flip := continuous_const.sub continuous_id
  let J₀ := fun t => linearBoundarySolution Θ R k₀ (flip t)
  have hJderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Θ) :
      HasDerivWithinAt J₀ (r (flip t)+α₀ (flip t)*J₀ t) (Icc (0 : ℝ) Θ) t := by
    have hh := (smoothLinearBoundarySolution_hasDerivAt (R := R) hk hk1 hΘ (hflip ht)).comp t
      ((hasDerivAt_const t Θ).sub (hasDerivAt_id t))
    apply HasDerivAt.hasDerivWithinAt
    convert! hh using 1 <;> dsimp [r,α₀,k,J₀,flip] <;> ring
  have hJbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) Θ) : 0 ≤ J₀ t ∧ J₀ t ≤ M :=
    ⟨linearBoundarySolution_nonnegative hR0 (hflip ht).2,
      linearBoundarySolution_upper hk hk1 hΘ hR0 (hflip ht)⟩
  have hRc : ContinuousOn r (Icc (0 : ℝ) Θ) := fun θ ht => (hcR θ ht).continuousWithinAt
  have hαc : ContinuousOn α (Icc (0 : ℝ) Θ) := fun θ ht => (hcα θ ht).continuousWithinAt
  have hβc : ContinuousOn β (Icc (0 : ℝ) Θ) := fun θ ht => (hcβ θ ht).continuousWithinAt
  obtain ⟨Jf,hJf0,hJf⟩ := exists_Riccati_small_perturbation hΘ0 hδ hM
    (r ∘ flip) (α₀ ∘ flip) (α ∘ flip) (β ∘ flip) J₀
    (hRc.comp hfc.continuousOn hflip)
    (hαc.comp hfc.continuousOn hflip)
    (hβc.comp hfc.continuousOn hflip)
    hJderiv hJbound (fun t ht => zero_lt_one.trans_le (hrbound _ (hflip (Ico_subset_Icc_self ht))))
    (fun t ht => (hcoeff _ (hflip ht)).1)
    (fun t ht => (hcoeff _ (hflip (Ico_subset_Icc_self ht))).2)
    (by simpa only [sub_zero] using hsmall)
  refine ⟨Jf ∘ flip,by simpa only [Function.comp_apply,flip,sub_self] using hJf0,fun θ ht => ?_⟩
  have hmap := hflip ht
  refine ⟨(hJf (flip θ) hmap).1,(hJf (flip θ) hmap).2.1,?_⟩
  have hh := (hJf (flip θ) hmap).2.2.comp θ
    (((hasDerivWithinAt_const θ (Icc (0 : ℝ) Θ) Θ).sub (hasDerivWithinAt_id θ (Icc (0 : ℝ) Θ)))) hflip
  convert! hh using 1 <;>
    simp only [Function.comp_apply,flip,sub_sub_cancel,r,α,α₀,β,k,kp,planarLinearPerturbation,
      planarQuadraticPerturbation,planarRiccati] <;> ring

end
end StrongSilver
