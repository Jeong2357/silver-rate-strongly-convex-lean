-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseProductShape
import StrongSilver.FourPhaseQueryFamily
import StrongSilver.FourPhaseJoiningBox

namespace StrongSilver.FourPhase
noncomputable section
set_option maxHeartbeats 2200000

/-- Finite scalar input to the four-phase schedule construction.
All coordinates are defined from the original steps. -/
structure LocalParameters where
  μ : ℝ
  T : ℝ
  gap : Fin 4 → List ℝ
  pivot : Fin 4 → ℝ
  ζ : ℝ
  mu_positive : 0 < μ
  time_positive : 0 < T
  small_total : μ*absoluteMass (boundedWord gap pivot) ≤ 1/4
  geometry : JoiningGeometry (productShape μ T gap pivot ζ)
  offset_nonnegative : 0 ≤ ζ
  offset_upper : ζ ≤ 1/16

namespace LocalParameters

def shape (D : LocalParameters) : Shape := productShape D.μ D.T D.gap D.pivot D.ζ
abbrev QueryIndex (D : LocalParameters) := Σ i : Fin 4, Fin (phaseWord D.gap D.pivot i).length

def queryScale (D : LocalParameters) (j : D.QueryIndex) : ℝ :=
  carry D.μ D.gap D.pivot j.1*quadraticMultiplier D.μ ((D.gap j.1).take j.2.val)

def querySlack (D : LocalParameters) (j : D.QueryIndex) : ℝ := phaseMass D.shape j.1-
  queryTime D.μ D.T (carry D.μ D.gap D.pivot j.1) (quadraticMultiplier D.μ ((D.gap j.1).take j.2.val))

theorem queryScale_lower (D : LocalParameters) (j : D.QueryIndex) : 1/2 ≤ D.queryScale j :=
  (carry_prefix_bounds D.mu_positive.le D.gap D.pivot D.small_total j.1 j.2.val).1

theorem querySlack_nonnegative (D : LocalParameters) (j : D.QueryIndex) : 0 ≤ D.querySlack j :=
  (productShape_orbit_ray D.mu_positive D.time_positive D.gap D.pivot D.small_total D.ζ j.1 j.2.val).1

/-- All local pre-step contacts in all four phases share one finite
support family. -/
def localFamily (D : LocalParameters) : SupportFamily D.QueryIndex Coordinates :=
  queryFamily D.geometry.regular D.offset_nonnegative
    (D.geometry.a_upper.trans (by norm_num)) D.geometry.masses_lower D.offset_upper
    D.time_positive (fun j => j.1) D.queryScale D.querySlack D.queryScale_lower D.querySlack_nonnegative

theorem localFamily_split (D : LocalParameters) (j : D.QueryIndex) :
    D.localFamily.z j+D.localFamily.g j =
    iterate ((phaseWord D.gap D.pivot j.1).take j.2.val)
      (fun y => D.μ • y+(1-D.μ) • ((1/D.T) • slope D.shape j.1))
      (carry D.μ D.gap D.pivot j.1 • phaseStart D.shape j.1) := by
  have hk : j.2.val ≤ (D.gap j.1).length := by
    have hh := j.2.isLt
    simp only [phaseWord,List.length_append,List.length_singleton] at hh
    omega
  have htake : (phaseWord D.gap D.pivot j.1).take j.2.val = (D.gap j.1).take j.2.val :=
    List.take_append_of_le_length hk
  rw [htake,phaseState_from_iterate D.mu_positive.ne' D.time_positive.ne']
  have hray := (productShape_orbit_ray D.mu_positive D.time_positive D.gap D.pivot D.small_total D.ζ j.1 j.2.val).2
  change D.queryScale j • (foot D.shape j.1+D.querySlack j • slope D.shape j.1)+
    (1/D.T) • slope D.shape j.1 = _
  change _-(1/D.T) • slope D.shape j.1 =
    D.queryScale j • (foot D.shape j.1+D.querySlack j • slope D.shape j.1) at hray
  rw [← hray,sub_add_cancel]
  rfl

end LocalParameters
end
end StrongSilver.FourPhase
