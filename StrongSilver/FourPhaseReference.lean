-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseParameters

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2000000

@[simp] theorem reference_m0 : reference 0 = 1 := rfl
@[simp] theorem reference_m1 : reference 1 = 1 := rfl
@[simp] theorem reference_m2 : reference 2 = 1 := rfl
@[simp] theorem reference_m3 : reference 3 = 1 := rfl
@[simp] theorem reference_k0 : reference 4 = rho⁻¹ := rfl
@[simp] theorem reference_k1 : reference 5 = 1 := rfl
@[simp] theorem reference_k2 : reference 6 = rho⁻¹ := rfl
@[simp] theorem reference_zeta : reference 7 = 0 := rfl

theorem rho_inv_identity : rho⁻¹ = rho-2 := by
  rw [← one_div]
  apply (div_eq_iff rho_positive.ne').mpr
  nlinarith only [rho_square]

theorem t0_reference : t0 reference = rho-1 := by
  simp [t0,rho_inv_identity]
  <;> ring

theorem t1_reference : t1 reference = 2 := by norm_num [t1]

theorem t2_reference : t2 reference = rho-1 := by
  simp [t2,rho_inv_identity]
  <;> ring

theorem totalTime_reference : totalTime reference = 2*rho := by
  rw [totalTime,t0_reference,t1_reference,t2_reference]
  ring

theorem leftMass_reference : leftMass reference = rho := by
  simp [leftMass,rho_inv_identity]
  <;> ring

theorem rightMass_reference : rightMass reference = rho := by
  simp [rightMass,rho_inv_identity]
  <;> ring

theorem totalMass_reference : totalMass reference = rho^2 := by
  rw [totalMass,leftMass_reference,rightMass_reference]
  norm_num
  nlinarith only [rho_square]

theorem q_reference : q reference = 1 := by norm_num [q]

theorem a_reference : a reference = 1/(2*rho) := by rw [a,q_reference,totalTime_reference]

theorem bodyScale_reference : bodyScale reference = rho/2 := by
  rw [bodyScale,a_reference,q_reference,mul_one]
  have hr := rho_positive.ne'
  field_simp
  nlinarith only [rho_square]

theorem upperTime_reference : upperTime reference = rho := by
  rw [upperTime,t2_reference]
  norm_num

theorem b1sq_reference : b1sq reference = 1/4 := by
  rw [b1sq,bodyScale_reference,upperTime_reference,totalTime_reference]
  have hr := rho_positive.ne'
  field_simp
  <;> ring

theorem b2sq_reference : b2sq reference = rho := by
  rw [b2sq,bodyScale_reference,upperTime_reference]
  change (rho/2)*(1/rho⁻¹-1/rho) = rho
  simp only [one_div,inv_inv]
  rw [rho_inv_identity]
  ring

theorem theta_reference : theta reference = rho-1 := by
  rw [theta,t2_reference]
  norm_num

theorem r2_reference : r2 reference = 1-1/(2*(rho-1)) := by
  rw [r2,theta_reference,totalTime_reference,b1sq_reference,b2sq_reference,t0_reference]
  have hr := rho_positive.ne'
  have hr1 : rho-1 ≠ 0 := by have hh := rho_bounds.1; linarith only [hh]
  norm_num
  field_simp
  <;> ring

theorem gainCoefficient_reference : gainCoefficient reference = (rho-1)/2 := by
  rw [gainCoefficient,leftMass_reference,t2_reference,totalTime_reference]
  have hr := rho_positive.ne'
  norm_num
  field_simp
  <;> ring

theorem gains_reference : gain reference = 0 ∧ gainLeft reference = 0 ∧ gainRight reference = 0 := by
  have hr := rho_positive.ne'
  constructor
  · rw [gain,totalMass_reference,leftMass_reference,rightMass_reference]
    norm_num [pow_two,hr]
  constructor
  · rw [gainLeft,leftMass_reference]
    norm_num [hr]
  · rw [gainRight,rightMass_reference]
    norm_num [hr]

end
end StrongSilver.FourPhase
