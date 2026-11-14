-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianFrontierPhases
import StrongSilver.CartesianGroupScaleSeparation

namespace StrongSilver.ScheduleTree
noncomputable section
set_option maxHeartbeats 3000000

/-- The selected pivot between adjacent original gaps belongs to an
actual split: the left gap is its left-child suffix, and the next gap is
its right-child prefix. These are word relations, including signed steps. -/
def FollowsAtSplit (t : ScheduleTree) (qv qr : ScheduleTree × ℝ) : Prop :=
  ∃ l r : ScheduleTree, (.split l qv.2 r) ∈ t.splitNodes ∧
    qv.1.word.IsSuffix l.word ∧ qr.1.word.IsPrefix r.word

theorem FollowsAtSplit.mono {t s : ScheduleTree} {qv qr : ScheduleTree × ℝ}
    (hn : t.splitNodes.Sublist s.splitNodes) (h : FollowsAtSplit t qv qr) : FollowsAtSplit s qv qr := by
  obtain ⟨l,r,hnode,hs,hp⟩ := h
  exact ⟨l,r,hn.subset hnode,hs,hp⟩

theorem frontierPhases_adjacent (A : ℝ) (t : ScheduleTree) (b : ℝ) :
    (frontierPhases A t b).IsChain (FollowsAtSplit t) := by
  induction t generalizing b with
  | leaf h => simp [frontierPhases]
  | split l p r il ir =>
    simp only [frontierPhases]
    split_ifs with hp
    · have hleft : l.splitNodes.Sublist (ScheduleTree.split l p r).splitNodes :=
        (List.sublist_append_left _ _).trans (List.sublist_cons_self _ _)
      have hright : r.splitNodes.Sublist (ScheduleTree.split l p r).splitNodes :=
        (List.sublist_append_right _ _).trans (List.sublist_cons_self _ _)
      have hl := (il p).imp (fun _ _ h => FollowsAtSplit.mono hleft h)
      have hr := (ir b).imp (fun _ _ h => FollowsAtSplit.mono hright h)
      apply hl.append hr
      intro q hq s hs
      obtain ⟨hboundary,hsuffix⟩ := frontierPhases_last_suffix A l p q hq
      have hprefix := frontierPhases_first_prefix A r b s hs
      refine ⟨l,r,?_,hsuffix,hprefix⟩
      rw [hboundary]
      simp [splitNodes]
    · simp

theorem frontierPhases_following_split {A b : ℝ} {t : ScheduleTree} {qv qr : ScheduleTree × ℝ}
    {before after : List (ScheduleTree × ℝ)}
    (h : frontierPhases A t b = before++qv::qr::after) : FollowsAtSplit t qv qr :=
  (List.isChain_iff_forall_rel_of_append_cons_cons.mp (frontierPhases_adjacent A t b)) h

theorem prefixMass_le_of_word_prefix {φ : ℝ → ℝ} {s t : ScheduleTree} (hp : s.word.IsPrefix t.word) :
    s.prefixMass φ ≤ t.prefixMass φ := by
  obtain ⟨tail,htail⟩ := List.prefix_iff_exists_eq_append.mp hp
  unfold prefixMass transformedWord
  rw [htail,List.map_append,Scalar.SignedIntervals.prefixMax_append]
  exact add_le_add (le_max_left _ _) le_rfl

/-- This is the sharp input scale estimate used by the ordinary right
suffix in the two-gap construction. -/
theorem right_gap_mass_bound {φ : ℝ → ℝ} {ε p : ℝ} {l r next : ScheduleTree}
    (hp : next.word.IsPrefix r.word) (hε : ε ≤ 1/100)
    (hbal : SilverBalanced φ ε (.split l p r)) : next.prefixMass φ ≤ (14/5:ℝ)*φ p := by
  have hm := prefixMass_le_of_word_prefix (φ := φ) hp
  have hr := FourGapGroup.balanced_right_mass_upper hε hbal
  nlinarith only [hm,hr,hbal.1]

end
end StrongSilver.ScheduleTree
