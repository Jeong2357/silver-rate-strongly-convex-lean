-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.OrdinaryCutTrace

namespace StrongSilver
open Real Filter
noncomputable section
set_option maxHeartbeats 1800000

theorem eventually_ordinary_prepend_chain : ∀ᶠ A : ℝ in atTop,
    ∀ μ T P : ℝ, ∀ qs : List CutPhase,
      (∀ q ∈ qs, OrdinaryPhaseParameters A μ q.pivot T P q.gap) →
      ∀ s : List ℝ, ∀ M G r : ℝ, PositiveTrace μ s (workingGateFraction A) M G r →
      ∃ M' G' : ℝ, Nonempty (PositiveTrace μ (qs.flatMap CutPhase.word++s) (workingGateFraction A) M' G'
        (r*(ordinaryPhaseProduct A μ P qs)^2)) := by
  filter_upwards [eventually_ordinary_positive_trace] with A hattach
  intro μ T P qs
  induction qs with
  | nil =>
    intro _ s M G r S
    exact ⟨M,G,by simpa [ordinaryPhaseProduct] using (Nonempty.intro S)⟩
  | cons q qs ih =>
    intro hgood s M G r S
    obtain ⟨M',G',⟨S'⟩⟩ := ih (fun z hz => hgood z (List.mem_cons_of_mem q hz)) s M G r S
    have hh := hattach μ q.pivot T P q.gap (hgood q (by simp)) _ M' G' _ S'
    refine ⟨A^(10 : ℝ),A^(10 : ℝ),?_⟩
    simpa [CutPhase.word,ordinaryPhaseProduct,List.append_assoc,mul_pow,mul_assoc,mul_comm,mul_left_comm] using hh

end
end StrongSilver
