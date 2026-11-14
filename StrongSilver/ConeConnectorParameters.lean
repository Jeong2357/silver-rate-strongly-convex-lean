-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.NormalizedWedge
import StrongSilver.ConeConnector

namespace StrongSilver
open Real
noncomputable section
set_option maxHeartbeats 2000000

structure ConeConnectorParameters (μ b V M H η : ℝ) where
  γ : ℝ
  U : ℝ
  a : ℝ
  d : ℝ
  r : ℝ
  c : ℝ
  s : ℝ
  Δ : ℝ
  X : ℝ
  gamma_pos : 0 < γ
  gamma_small : γ ≤ 1/16
  radius_pos : 0 < r
  a_pos : 0 < a
  d_pos : 0 < d
  cos_pos : 0 < c
  sin_pos : 0 < s
  sin_cos : s ≤ c
  cos_le_one : c ≤ 1
  sin_le_one : s ≤ 1
  unit : c^2+s^2 = 1
  radius : r = a*c+d*s
  radius_bound : r ≤ 2*a
  d_small : d ≤ a*s/256
  X_pos : 0 < X
  Y_small : d ≤ s*X/256
  delta_nonnegative : 0 ≤ Δ
  delta_small : Δ ≤ a*X/128
  delta_eq : Δ = 2*a*γ*M*V
  imag_bound : r*s ≤ 2*a*γ
  d_imag_bound : d ≤ 2*a*γ
  old_slope : H ≤ r/s
  old_gate : Δ ≤ (r/s)*(η*V)
  connector_source : X+a = U
  connector_a : (1-μ)*b*a = (1-μ*b)*U
  connector_d : (1-μ)*b*d = V
  U_pos : 0 < U
  gamma_eq : γ = min (1/16) (Real.sqrt (η/(16*M)))
  H_le_a : H ≤ a
  U_eq : U = 512*(V+V/((1-μ*b)*γ)+γ*M*V+((1-μ)*b)*H/(1-μ*b))

theorem exists_cone_connector_parameters {μ b V M H η : ℝ}
    (hμ : 0 < μ) (hb : 2 ≤ b) (hq : μ*b < 1) (hV : 0 < V)
    (hM : 1 ≤ M) (hH : 0 ≤ H) (hη : 0 < η) (hη1 : η ≤ 1) :
    Nonempty (ConeConnectorParameters μ b V M H η) := by
  let q := 1-μ*b
  let D := (1-μ)*b
  let γ := min (1/16) (Real.sqrt (η/(16*M)))
  let c := normalizedWedgeCos γ
  let s := normalizedWedgeSin γ
  let U := 512*(V+V/(q*γ)+γ*M*V+D*H/q)
  let a := q*U/D
  let d := V/D
  let r := a*c+d*s
  let Δ := 2*a*γ*M*V
  let X := U-a
  have hb0 : 0 < b := by linarith
  have hμb : 0 < μ*b := mul_pos hμ hb0
  have hq0 : 0 < q := sub_pos.mpr hq
  have hq1 : q ≤ 1 := by dsimp [q]; linarith only [hμb]
  have hμ1 : μ < 1 := by nlinarith only [hμb,hq,hb,hμ]
  have hD : 0 < D := mul_pos (sub_pos.mpr hμ1) hb0
  have hDq : 2*q ≤ D := by dsimp [D,q]; nlinarith only [hμb,hb]
  have hM0 : 0 < M := by linarith
  have hroot : 0 < Real.sqrt (η/(16*M)) := Real.sqrt_pos.mpr (div_pos hη (by positivity))
  have hγ : 0 < γ := lt_min (by norm_num) hroot
  have hγ16 : γ ≤ 1/16 := min_le_left _ _
  have hγ1 : γ ≤ 1 := by linarith only [hγ16]
  have hγsq : 2*γ^2*M ≤ η := by
    have hh : γ ≤ Real.sqrt (η/(16*M)) := min_le_right _ _
    have hsquare := Real.sq_sqrt (show 0 ≤ η/(16*M) by positivity)
    have hh' : γ^2 ≤ η/(16*M) := by nlinarith only [hh,hsquare,hγ,hroot]
    have hm := (le_div_iff₀ (by positivity : 0 < 16*M)).mp hh'
    nlinarith only [hm,hη]
  obtain ⟨hc,hs,hsc,hu,hcL,hcU,hsL,hsU⟩ := normalizedWedge_properties hγ hγ1
  change 0 < c at hc
  change 0 < s at hs
  have hratio : c/s = 1/γ := normalizedWedge_ratio hγ
  have hDH : 0 ≤ D*H/q := div_nonneg (mul_nonneg hD.le hH) hq0.le
  have hγMV : 0 ≤ γ*M*V := by positivity
  have hdiv : 0 < V/(q*γ) := div_pos hV (mul_pos hq0 hγ)
  have hU : 0 < U := by dsimp only [U]; positivity
  have hUdiv : 512*(V/(q*γ)) ≤ U := by dsimp only [U]; linarith only [hV,hDH,hγMV]
  have hUpad : 512*(γ*M*V) ≤ U := by dsimp only [U]; linarith only [hV,hDH,hdiv]
  have hUH : 512*(D*H/q) ≤ U := by dsimp only [U]; linarith only [hV,hγMV,hdiv]
  have ha : 0 < a := div_pos (mul_pos hq0 hU) hD
  have hd : 0 < d := div_pos hV hD
  have haD : a*D = q*U := by dsimp only [a]; field_simp
  have hdD : d*D = V := by dsimp only [d]; field_simp
  have haU : 2*a ≤ U := by
    have hh := mul_le_mul_of_nonneg_left hDq ha.le
    nlinarith only [haD,hh,hq0]
  have hX : 0 < X := by dsimp only [X]; linarith only [haU,hU]
  have haX : a ≤ X := by dsimp only [X]; linarith only [haU]
  have hUV : 512*V ≤ U*q*γ := by
    have hh := (div_le_iff₀ (mul_pos hq0 hγ)).mp (show (512*V)/(q*γ) ≤ U by simpa only [mul_div_assoc] using hUdiv)
    nlinarith only [hh]
  have hdγ : d ≤ a*γ/512 := by
    have he := congrArg (fun t : ℝ => t*γ) haD
    have hh : 512*d*D ≤ a*γ*D := by nlinarith only [hdD,he,hUV]
    nlinarith only [hh,hD]
  have hds : d ≤ a*s/256 := by
    have hh := mul_le_mul_of_nonneg_left hsL ha.le
    change γ/2 ≤ s at hsL
    nlinarith only [hdγ,hh]
  have hdX : d ≤ s*X/256 := by
    have hh := mul_le_mul_of_nonneg_left haX hs.le
    nlinarith only [hds,hh]
  have hdA : d ≤ a := by
    have hh := mul_le_mul_of_nonneg_left hγ1 ha.le
    nlinarith only [hdγ,hh,ha]
  have hs1 : s ≤ 1 := hsU.trans hγ1
  have hr : 0 < r := add_pos_of_pos_of_nonneg (mul_pos ha hc) (mul_nonneg hd.le hs.le)
  have hr2a : r ≤ 2*a := by
    have h1 := mul_le_mul_of_nonneg_left hcU ha.le
    have h2 := mul_le_mul_of_nonneg_left hs1 hd.le
    dsimp only [r]
    linarith only [h1,h2,hdA]
  have hΔ : Δ ≤ a*X/128 := by
    have hx : 256*(γ*M*V) ≤ X := by dsimp only [X]; linarith only [hUpad,haU]
    have hh := mul_le_mul_of_nonneg_left hx ha.le
    dsimp only [Δ]
    nlinarith only [hh]
  have hrS : r*s ≤ 2*a*γ := by
    exact (mul_le_mul_of_nonneg_right hr2a hs.le).trans (mul_le_mul_of_nonneg_left hsU (by positivity))
  have hd2 : d ≤ 2*a*γ := by nlinarith only [hdγ,mul_pos ha hγ]
  have hHa : H ≤ a := by
    have hh := (div_le_iff₀ hq0).mp (show (512*(D*H))/q ≤ U by simpa only [mul_div_assoc] using hUH)
    have hh' : 512*H*D ≤ a*D := by nlinarith only [hh,haD]
    nlinarith only [hh',hD,hH]
  have hra : a/γ ≤ r/s := by
    have hh : a*c ≤ r := le_add_of_nonneg_right (mul_nonneg hd.le hs.le)
    have hh' := div_le_div_of_nonneg_right hh hs.le
    have he : a*c/s = a/γ := by rw [mul_div_assoc,hratio]; ring
    rwa [he] at hh'
  have haγ : a ≤ a/γ := by apply (le_div_iff₀ hγ).mpr; nlinarith only [mul_le_mul_of_nonneg_left hγ1 ha.le]
  have hgate : Δ ≤ (r/s)*(η*V) := by
    have hh := mul_le_mul_of_nonneg_left hγsq (mul_nonneg ha.le hV.le)
    have hfirst : Δ ≤ (a/γ)*(η*V) := by
      rw [show (a/γ)*(η*V) = (a*(η*V))/γ by ring]
      apply (le_div_iff₀ hγ).mpr
      dsimp only [Δ]
      nlinarith only [hh]
    exact hfirst.trans (mul_le_mul_of_nonneg_right hra (mul_nonneg hη.le hV.le))
  refine ⟨⟨γ,U,a,d,r,c,s,Δ,X,hγ,hγ16,hr,ha,hd,hc,hs,hsc,hcU,hs1,hu,rfl,hr2a,hds,hX,hdX,
    by positivity,hΔ,rfl,hrS,hd2,hHa.trans (haγ.trans hra),hgate,?_,?_,?_,hU,rfl,hHa,rfl⟩⟩
  · dsimp only [X]; ring
  · change D*a = q*U; nlinarith only [haD]
  · change D*d = V; nlinarith only [hdD]

end
end StrongSilver
