-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.ScalarReconstruction

namespace StrongSilver
open Set Real
noncomputable section
set_option maxHeartbeats 1000000

def softThreshold (v x : ℝ) : ℝ := max (x-v) 0+min (x+v) 0
def symmetricClip (a t : ℝ) : ℝ := max (-a) (min a t)

theorem softThreshold_increments {v x y : ℝ} (hv : 0 ≤ v) (hxy : x ≤ y) :
    0 ≤ softThreshold v y-softThreshold v x ∧ softThreshold v y-softThreshold v x ≤ y-x := by
  unfold softThreshold
  simp only [max_def,min_def]
  split_ifs <;> constructor <;> linarith

theorem symmetricClip_increments {a x y : ℝ} (ha : 0 ≤ a) (hxy : x ≤ y) :
    0 ≤ symmetricClip a y-symmetricClip a x ∧ symmetricClip a y-symmetricClip a x ≤ y-x := by
  unfold symmetricClip
  simp only [max_def,min_def]
  split_ifs <;> constructor <;> linarith

theorem softThreshold_zero {v : ℝ} (hv : 0 ≤ v) : softThreshold v 0 = 0 := by
  simp only [softThreshold,zero_sub,zero_add,max_eq_right (neg_nonpos.mpr hv),min_eq_right hv,add_zero]

theorem symmetricClip_zero {a : ℝ} (ha : 0 ≤ a) : symmetricClip a 0 = 0 := by
  simp only [symmetricClip,min_eq_right ha,max_eq_right (neg_nonpos.mpr ha)]

theorem softThreshold_of_nonnegative {v x : ℝ} (hv : 0 ≤ v) (hx : 0 ≤ x) :
    softThreshold v x = max (x-v) 0 := by
  rw [softThreshold,min_eq_right (add_nonneg hx hv),add_zero]

theorem symmetricClip_of_nonnegative {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    symmetricClip a t = min a t := by
  exact max_eq_right ((neg_nonpos.mpr ha).trans (le_min ha ht))

structure ScalarRamp where
  base : ℝ
  threshold : ℝ
  amplitude : ℝ
  base_nonnegative : 0 ≤ base
  base_le_half : base ≤ 1/2
  threshold_nonnegative : 0 ≤ threshold
  amplitude_nonnegative : 0 ≤ amplitude

namespace ScalarRamp
variable (R : ScalarRamp)

def physical (x : ℝ) : ℝ := R.base*x+symmetricClip R.amplitude ((1/2-R.base)*softThreshold R.threshold x)

theorem physical_continuous : Continuous R.physical := by unfold physical symmetricClip softThreshold; fun_prop

theorem physical_zero : R.physical 0 = 0 := by
  simp only [physical,softThreshold_zero R.threshold_nonnegative,mul_zero,
    symmetricClip_zero R.amplitude_nonnegative,add_zero]

theorem physical_increments {x y : ℝ} (hxy : x ≤ y) :
    R.base*(y-x) ≤ R.physical y-R.physical x ∧ R.physical y-R.physical x ≤ (y-x)/2 := by
  have hs := softThreshold_increments R.threshold_nonnegative hxy
  have hδ : 0 ≤ 1/2-R.base := sub_nonneg.mpr R.base_le_half
  have hm0 := mul_nonneg hδ hs.1
  have hm := mul_le_mul_of_nonneg_left hs.2 hδ
  have hc := symmetricClip_increments R.amplitude_nonnegative (by nlinarith only [hm0] :
    (1/2-R.base)*softThreshold R.threshold x ≤ (1/2-R.base)*softThreshold R.threshold y)
  dsimp [physical]
  constructor <;> nlinarith only [hc.1,hc.2,hm]

theorem physical_positive_bounds {x : ℝ} (hx : 0 ≤ x) :
    R.base*x ≤ R.physical x ∧ R.physical x ≤ R.base*x+R.amplitude := by
  have ht : 0 ≤ (1/2-R.base)*softThreshold R.threshold x := by
    rw [softThreshold_of_nonnegative R.threshold_nonnegative hx]
    exact mul_nonneg (sub_nonneg.mpr R.base_le_half) (le_max_right _ _)
  rw [physical,symmetricClip_of_nonnegative R.amplitude_nonnegative ht]
  exact ⟨le_add_of_nonneg_right (le_min R.amplitude_nonnegative ht),add_le_add le_rfl (min_le_left _ _)⟩

theorem physical_below_threshold {x : ℝ} (hx : 0 ≤ x) (hxv : x ≤ R.threshold) : R.physical x = R.base*x := by
  rw [physical,softThreshold_of_nonnegative R.threshold_nonnegative hx,
    max_eq_right (sub_nonpos.mpr hxv),mul_zero,symmetricClip_zero R.amplitude_nonnegative,add_zero]

def contraction {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (hμb : μ ≤ R.base) : ScalarContraction where
  g := fun x => (R.physical x-μ*x)/(1-μ)
  zero := by rw [R.physical_zero,mul_zero,sub_self,zero_div]
  increments := by
    intro x y hxy
    have hH := R.physical_increments hxy
    have hμΔ := mul_nonneg hμ0 (sub_nonneg.mpr hxy)
    have hbΔ := mul_le_mul_of_nonneg_right hμb (sub_nonneg.mpr hxy)
    have he : (R.physical y-μ*y)/(1-μ)-(R.physical x-μ*x)/(1-μ) =
        (R.physical y-R.physical x-μ*(y-x))/(1-μ) := by ring
    rw [he]
    constructor
    · apply div_nonneg _ (by linarith)
      nlinarith only [hH.1,hbΔ]
    · apply (div_le_iff₀ (by linarith : 0 < 1-μ)).mpr
      nlinarith only [hH.2,hμΔ]

theorem actual_physical_gradient {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ < 1) (hμb : μ ≤ R.base) (x : ℝ) :
    stronglyConvexGradient μ (Moreau.gradient (R.contraction hμ0 hμ1 hμb).epigraph) x = R.physical x := by
  rw [stronglyConvexGradient,(R.contraction hμ0 hμ1 hμb).envelope_gradient]
  change μ*x+(1-μ)*((R.physical x-μ*x)/(1-μ)) = R.physical x
  field_simp [show 1-μ ≠ 0 by linarith]
  <;> ring

end ScalarRamp
end
end StrongSilver
