-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.Scalar.MaxPlusGlobal

namespace StrongSilver.Scalar.Silver
open Set
noncomputable section
set_option maxHeartbeats 1000000

def farSet (δ : ℝ) : Set (ℝ × ℝ) :=
  {x | δ ≤ |x.1-rho| ∨ δ ≤ |x.2-rho|}

theorem farSet_closed (δ : ℝ) : IsClosed (farSet δ) := by
  change IsClosed ({x : ℝ × ℝ | δ ≤ |x.1-rho|} ∪ {x : ℝ × ℝ | δ ≤ |x.2-rho|})
  apply IsClosed.union
  · apply isClosed_le continuous_const
    fun_prop
  · apply isClosed_le continuous_const
    fun_prop

/-- Positivity is uniform away from the unique minimum, including all
unbounded and boundary portions of the positive quadrant. -/
theorem splitPotential_away (δ : ℝ) (hδ : 0 < δ) : ∃ c > 0,
    ∀ a b : ℝ, 0 < a → 0 < b → (δ ≤ |a-rho| ∨ δ ≤ |b-rho|) → c ≤ splitPotential a b := by
  obtain ⟨l,U,hl,hlU,hbarrier⟩ := splitPotential_compact_barrier
  let K := (Icc l U) ×ˢ (Icc l U)
  let S := K ∩ farSet δ
  have hcompact : IsCompact S := (isCompact_Icc.prod isCompact_Icc).inter_right (farSet_closed δ)
  have hcont : ContinuousOn (fun x : ℝ × ℝ => splitPotential x.1 x.2) S := by
    intro x hx
    exact (splitPotential_continuousAt x.1 x.2 (hl.trans_le hx.1.1.1) (hl.trans_le hx.1.2.1)).continuousWithinAt
  have hpos (x : ℝ × ℝ) (hx : x ∈ S) : 0 < splitPotential x.1 x.2 := by
    have ha : 0 < x.1 := hl.trans_le hx.1.1.1
    have hb : 0 < x.2 := hl.trans_le hx.1.2.1
    have hn := splitPotential_nonnegative x.1 x.2 ha hb
    have hne : splitPotential x.1 x.2 ≠ 0 := by
      intro he
      obtain ⟨h1,h2⟩ := (splitPotential_zero_iff x.1 x.2 ha hb).mp he
      have hf : δ ≤ |x.1-rho| ∨ δ ≤ |x.2-rho| := hx.2
      rw [h1,h2,sub_self,abs_zero] at hf
      cases hf <;> linarith
    exact lt_of_le_of_ne hn (Ne.symm hne)
  have hc : ∃ c > 0, ∀ x ∈ S, c ≤ splitPotential x.1 x.2 := by
    by_cases hS : S.Nonempty
    · obtain ⟨p,hp,hmin⟩ := hcompact.exists_isMinOn hS hcont
      exact ⟨splitPotential p.1 p.2,hpos p hp,fun x hx => hmin hx⟩
    · exact ⟨1,zero_lt_one,fun x hx => False.elim (hS ⟨x,hx⟩)⟩
  obtain ⟨c,hc,hcBound⟩ := hc
  refine ⟨min c (minimum/2),lt_min hc (by linarith [minimum_positive]),fun a b ha hb hfar => ?_⟩
  by_cases hK : (a,b) ∈ K
  · exact (min_le_left _ _).trans (hcBound (a,b) ⟨hK,hfar⟩)
  · have hout : a ∉ Icc l U ∨ b ∉ Icc l U := by
      change ¬(a ∈ Icc l U ∧ b ∈ Icc l U) at hK
      exact not_and_or.mp hK
    exact (min_le_right _ _).trans (hbarrier a b ha hb hout)

end
end StrongSilver.Scalar.Silver
