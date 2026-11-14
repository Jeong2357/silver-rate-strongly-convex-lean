-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseLocalParameters
import StrongSilver.AffineSupportPath
import StrongSilver.PathFamilyRows

namespace StrongSilver.FourPhase.LocalParameters
noncomputable section
set_option maxHeartbeats 2600000

def localPath (D : LocalParameters) (i : Fin 4) : SupportedPath Coordinates D.μ (phaseWord D.gap D.pivot i).length :=
  affineSupportPath D.localFamily D.μ ((1/D.T) • slope D.shape i)
    (carry D.μ D.gap D.pivot i • phaseStart D.shape i) (phaseWord D.gap D.pivot i)
    (fun k => ⟨i,k⟩) (fun _ => rfl) (fun k => D.localFamily_split ⟨i,k⟩)

theorem localPath_start (D : LocalParameters) (i : Fin 4) :
    (D.localPath i).x 0 = carry D.μ D.gap D.pivot i • phaseStart D.shape i := rfl

theorem localPath_end (D : LocalParameters) (i : Fin 4) :
    (D.localPath i).x (Fin.last _) = phaseState D.μ D.T (carry D.μ D.gap D.pivot i)
      (phaseStart D.shape i) (slope D.shape i) (quadraticMultiplier D.μ (phaseWord D.gap D.pivot i)) := by
  change iterate ((phaseWord D.gap D.pivot i).take (phaseWord D.gap D.pivot i).length)
    (fun y => D.μ • y+(1-D.μ) • ((1/D.T) • slope D.shape i)) _ = _
  rw [List.take_length,phaseState_from_iterate D.mu_positive.ne' D.time_positive.ne']

theorem localPath_steps (D : LocalParameters) (i : Fin 4) : List.ofFn (D.localPath i).steps = phaseWord D.gap D.pivot i := List.ofFn_get _

theorem localPath_within (D : LocalParameters) (i : Fin 4) : (D.localPath i).WithinFamily D.localFamily := by
  intro k
  exact ⟨⟨i,k⟩,rfl,rfl,rfl⟩

theorem localPath_next (D : LocalParameters) (i : Fin 3) :
    (D.localPath i.castSucc).x (Fin.last _) = (D.localPath i.succ).x 0 := by
  rw [localPath_end,localPath_start]
  exact productShape_orbit_next D.mu_positive D.time_positive D.gap D.pivot D.small_total D.ζ i

theorem localPath_zero_source (D : LocalParameters) : (D.localPath 0).x 0 = source D.shape := by
  rw [localPath_start]
  change (1:ℝ) • source D.shape = source D.shape
  exact one_smul _ _

def joiningScale (D : LocalParameters) : ℝ := lastExcess D.μ D.T D.gap D.pivot-
  carry D.μ D.gap D.pivot 3*quadraticMultiplier D.μ (phaseWord D.gap D.pivot 3)*D.ζ

theorem localPath_last_endpoint (D : LocalParameters) :
    (D.localPath 3).x (Fin.last _) = D.joiningScale • axis := by
  rw [localPath_end]
  have hξ : phaseStart D.shape 3 = -(normalizedMass D.μ D.T D.gap D.pivot 3+D.ζ) • axis := by
    change point (-q D.shape) 0 0 0 = _
    rw [axis,point_smul]
    have hm := productShape_mass D.μ D.T D.gap D.pivot D.ζ 3
    change D.shape 3 = normalizedMass D.μ D.T D.gap D.pivot 3 at hm
    have hz : D.shape 7 = D.ζ := rfl
    unfold q
    rw [hm,hz]
    congr 1 <;> ring
  have hg : slope D.shape 3 = -axis := by
    change slope3 D.shape = -axis
    rw [slope3_axis,neg_one_smul]
  rw [hξ,hg]
  exact phaseState_last D.mu_positive.ne' D.time_positive.ne'
    (carry_positive D.mu_positive.le D.gap D.pivot D.small_total 3).ne'
    (minPrefixProduct_positive (D.gap 3) (gap_small_steps D.mu_positive.le D.gap D.pivot D.small_total 3)).ne'
    axis rfl rfl

end
end StrongSilver.FourPhase.LocalParameters
