-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CompleteCutCost

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1800000

def largePivotCharge (L b : ℝ) : ℝ := if L ≤ b then Real.log (Real.exp 1+b) else 0

theorem largePivotCharge_nonnegative {L : ℝ} (hL : 0 ≤ L) (b : ℝ) : 0 ≤ largePivotCharge L b := by
  unfold largePivotCharge
  split_ifs with hb
  · apply Real.log_nonneg
    have he := Real.one_le_exp_iff.mpr (show (0 : ℝ) ≤ 1 by norm_num)
    linarith only [he,hL,hb]
  · exact le_rfl

theorem log_one_add_power_cutoff {A s : ℝ} (hA : 2 ≤ A) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.log (1+A^(1+s)) ≤ 3*Real.log A := by
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hA1 : 1 ≤ A := le_trans (by norm_num) hA
  have hp : 1 ≤ A^(1+s) := Real.one_le_rpow hA1 (by linarith only [hs])
  have hh := Real.log_le_log (by positivity : 0 < 1+A^(1+s)) (show 1+A^(1+s) ≤ 2*A^(1+s) by linarith only [hp])
  rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hA0 _).ne',Real.log_rpow hA0] at hh
  have htwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hA
  have hlog := Real.log_nonneg hA1
  nlinarith only [hh,htwo,mul_nonneg (show 0 ≤ 1-s by linarith only [hs1]) hlog]

theorem log_one_add_pivot_budget {A s : ℝ} (hA : 2 ≤ A) (hs : 0 ≤ s) (hs1 : s ≤ 1) (b : ℝ) :
    Real.log (1+max b 0) ≤ 3*Real.log A+largePivotCharge (A^(1+s)) b := by
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hA1 : 1 ≤ A := le_trans (by norm_num) hA
  have hL := Real.rpow_pos_of_pos hA0 (1+s)
  by_cases hb : A^(1+s) ≤ b
  · have hb0 : 0 ≤ b := hL.le.trans hb
    rw [largePivotCharge,if_pos hb,max_eq_left hb0]
    have he := Real.one_le_exp_iff.mpr (show (0 : ℝ) ≤ 1 by norm_num)
    have hh := Real.log_le_log (by positivity : 0 < 1+b) (add_le_add he le_rfl)
    have hlog := Real.log_nonneg hA1
    linarith only [hh,hlog]
  · rw [largePivotCharge,if_neg hb,add_zero]
    exact (Real.log_le_log (by positivity : 0 < 1+max b 0)
      (add_le_add le_rfl (max_le (le_of_not_ge hb) hL.le))).trans (log_one_add_power_cutoff hA hs hs1)

theorem phase_growth_budget {A σ τ : ℝ} (hA : 2 ≤ A)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (q : CutPhase) :
    phaseGrowthCharge q ≤ 6*Real.log A+Scalar.SignedIntervals.positiveMass q.gap/A^(1+τ)+largePivotCharge (A^(1+σ)) q.pivot := by
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hg := log_one_add_mass_budget (Scalar.SignedIntervals.positiveMass_nonneg q.gap) (Real.rpow_pos_of_pos hA0 (1+τ))
  have hp := log_one_add_pivot_budget hA hσ hσ1 q.pivot
  have hL := log_one_add_power_cutoff hA hτ hτ1
  unfold phaseGrowthCharge
  linarith only [hg,hp,hL]

theorem phases_growth_budget {A σ τ : ℝ} (hA : 2 ≤ A)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (qs : List CutPhase) :
    (qs.map phaseGrowthCharge).sum ≤ 6*(qs.length : ℝ)*Real.log A+
      (qs.map fun q => Scalar.SignedIntervals.positiveMass q.gap).sum/A^(1+τ)+
      (qs.map fun q => largePivotCharge (A^(1+σ)) q.pivot).sum := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    have hh := phase_growth_budget hA hσ hσ1 hτ hτ1 q
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    rw [add_div]
    nlinarith only [hh,ih]

theorem CompleteCutAssembly.reserved_growth_budget {A σ τ : ℝ} (hA : 2 ≤ A)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (s : CompleteCutAssembly) (t : List ℝ) :
    (s.reserved.map phaseGrowthCharge).sum ≤ 6*(s.reserved.length : ℝ)*Real.log A+
      (s.reserved.map fun q => Scalar.SignedIntervals.positiveMass q.gap).sum/A^(1+τ)+
      largeLogESum (s.word t) (A^(1+σ)) := by
  have hh := phases_growth_budget hA hσ hσ1 hτ hτ1 s.reserved
  let w := largePivotCharge (A^(1+σ))
  have hw : ∀ b, 0 ≤ w b := largePivotCharge_nonnegative (Real.rpow_nonneg (by linarith only [hA] : 0 ≤ A) (1+σ))
  have hreserve := s.reserved_weight_le (fun q => w q.pivot) (fun q => hw q.pivot)
  have hwhole := (ScheduleCut.mk s.phases t).selected_weight_le w hw
  change (s.phases.map fun q => w q.pivot).sum ≤ largeLogESum (s.word t) (A^(1+σ)) at hwhole
  exact hh.trans (add_le_add le_rfl (hreserve.trans hwhole))

end
end StrongSilver
