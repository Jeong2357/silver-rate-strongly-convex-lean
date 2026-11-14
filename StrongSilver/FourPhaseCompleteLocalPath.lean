-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.FourPhaseLocalPaths

namespace StrongSilver.FourPhase.LocalParameters
noncomputable section
set_option maxHeartbeats 2400000

def totalWord (D : LocalParameters) : List ℝ := phaseWord D.gap D.pivot 0++phaseWord D.gap D.pivot 1++
  phaseWord D.gap D.pivot 2++phaseWord D.gap D.pivot 3

/-- A single supported path follows every original step of all four
phases and reaches the exact joining scale, while all its rows remain
in the common explicitly constructed local family. -/
theorem exists_complete_local_path (D : LocalParameters) : ∃ n : ℕ, ∃ P : SupportedPath Coordinates D.μ n,
    List.ofFn P.steps = D.totalWord ∧ P.x 0 = source D.shape ∧
    P.x (Fin.last n) = D.joiningScale • axis ∧ P.WithinFamily D.localFamily := by
  obtain ⟨P01,h01s,h01e,h01w,h01r⟩ := (D.localPath 0).concat_within_family (D.localPath 1) D.localFamily
    (D.localPath_within 0) (D.localPath_within 1) (D.localPath_next 0)
  have hj12 : P01.x (Fin.last _) = (D.localPath 2).x 0 := h01e.trans (D.localPath_next 1)
  obtain ⟨P012,h012s,h012e,h012w,h012r⟩ := P01.concat_within_family (D.localPath 2) D.localFamily
    h01r (D.localPath_within 2) hj12
  have hj23 : P012.x (Fin.last _) = (D.localPath 3).x 0 := h012e.trans (D.localPath_next 2)
  obtain ⟨P,hPs,hPe,hPw,hPr⟩ := P012.concat_within_family (D.localPath 3) D.localFamily
    h012r (D.localPath_within 3) hj23
  refine ⟨_,P,?_,hPs.trans (h012s.trans (h01s.trans D.localPath_zero_source)),
    hPe.trans D.localPath_last_endpoint,hPr⟩
  rw [hPw,h012w,h01w,localPath_steps,localPath_steps,localPath_steps,localPath_steps]
  rfl

end
end StrongSilver.FourPhase.LocalParameters
