-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseNorm
import StrongSilver.FourPhaseGainIdentities

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 7000000

def normPrefactor (x : Shape) : ℝ := (1+x 7/x 3)*(1+x 7/totalMass x)
def normalizedNorm (x : Shape) : ℝ := ‖source x‖^2/(totalMass x^2*normPrefactor x)

variable {x : Shape} (R : Regular x)
include R

theorem normPrefactor_positive : 0 < normPrefactor x := by
  have hq : 0 < x 3+x 7 := R.q_positive
  have hM : 0 < totalMass x+x 7 := by
    rw [totalMass_eq]; linarith only [R.totalTime_positive,hq]
  have h1 : 0 < 1+x 7/x 3 := by
    rw [one_add_div R.m3_positive.ne']
    exact div_pos hq R.m3_positive
  have h2 : 0 < 1+x 7/totalMass x := by
    rw [one_add_div R.totalMass_positive.ne']
    exact div_pos hM R.totalMass_positive
  exact mul_pos h1 h2

theorem normalizedNorm_positive : 0 < normalizedNorm x :=
  div_pos (sq_pos_of_pos (norm_pos_iff.mpr (source_nonzero R)))
    (mul_pos (sq_pos_of_pos R.totalMass_positive) (normPrefactor_positive R))

/-- Exact identity underlying the first-order gain calculation in (4.19). -/
theorem normalizedNorm_gain_identity : normalizedNorm x = Real.exp (-gain x)+
    gainCoefficient x*(Real.exp (-gain x-gainLeft x-gainRight x)-1) := by
  rw [normalizedNorm,source_norm_formula R,bodyScale_eq x R.totalTime_positive.ne',
    exp_neg_gain R,exp_neg_three_gains R]
  unfold normPrefactor gainCoefficient
  have hk0 := R.k0_positive.ne'
  have hk1 := R.k1_positive.ne'
  have hk2 := R.k2_positive.ne'
  have hm3 := R.m3_positive.ne'
  have hM := R.totalMass_positive.ne'
  have hT := R.totalTime_positive.ne'
  have hq : q x ≠ 0 := R.q_positive.ne'
  have hMq : totalMass x+x 7 ≠ 0 := by
    have hp : 0 < totalMass x+x 7 := by
      rw [totalMass_eq]; have hh := R.q_positive; unfold q at hh
      linarith only [R.totalTime_positive,hh]
    exact hp.ne'
  rw [one_add_div hm3,one_add_div hM]
  change _/(_*(q x/x 3*((totalMass x+x 7)/totalMass x))) = _
  field_simp [hq,hMq]
  dsimp only [q,totalMass,totalTime,leftMass,rightMass,t0,t1,t2]
  ring

end
end StrongSilver.FourPhase
