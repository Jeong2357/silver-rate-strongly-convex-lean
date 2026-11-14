-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianUniformGroups

namespace StrongSilver.ScheduleTree.FourGapGroup
noncomputable section
set_option maxHeartbeats 4800000

/-- All actual joining conditions for a complete balanced depth
partition follow from the common scale and signed-mass budgets. Internal
boundaries are discharged recursively using the parent's right mass;
only the exterior input scale and offset need to be supplied. -/
theorem uniform_depth_sequence_ready {δ c μ B ε L U Zmax : ℝ}
    (hμB : μ*B ≤ 1/2) (hε : ε ≤ 1/100) (hL : 0 < L) (hU : 0 ≤ U) (hc : 0 ≤ c)
    (hZbudget : 2*U*Zmax ≤ c*L)
    (d : ℕ) (t : ScheduleTree) (b : ℝ) (qs : List Group) (H Z : ℝ)
    (hqs : qs.map (fun q => (q.1.tree,q.2)) = depthPhases d t b)
    (hbal : balancedThrough (logarithmicStep μ) ε (d+2) t)
    (hword : ∀ s ∈ t.word, s ≤ B)
    (W : UniformGroups δ c μ B ε L U qs)
    (hHlow : L ≤ H) (hHup : H ≤ (9/20:ℝ)*cappedStep μ B b)
    (hZ : 0 ≤ Z) (hZmax : Z ≤ Zmax) : sequenceReady δ c μ ε qs H Z := by
  induction d generalizing t b qs H Z with
  | zero =>
    cases qs with
    | nil => exact False.elim (depthPhases_ne_nil 0 t b hqs.symm)
    | cons q tail =>
      change (q.1.tree,q.2)::tail.map (fun q => (q.1.tree,q.2)) = [(t,b)] at hqs
      have hp := List.cons.inj hqs
      have ht : tail = [] := List.map_eq_nil_iff.mp hp.2
      subst tail
      have hb := congrArg Prod.snd hp.1
      change q.2 = b at hb
      have hq : q ∈ [q] := by simp
      change GroupReady δ c μ ε q H Z ∧ True
      refine ⟨groupReady_of_uniform_budgets (W.data q hq) (W.near q hq) hμB hL hU hc
        (W.scale_lower q hq) (W.boundary_upper q hq) hHlow ?_ (W.time_lower q hq) (W.time_upper q hq)
        (W.negative_budget q hq) hZ hZmax hZbudget,True.intro⟩
      simpa only [hb] using hHup
  | succ d ih =>
    rw [Nat.succ_add] at hbal
    cases t with
    | leaf h => exact False.elim hbal
    | split l p r =>
      change qs.map (fun q => (q.1.tree,q.2)) = depthPhases d l p++depthPhases d r b at hqs
      obtain ⟨ps,rs,hpart,hps,hrs⟩ := List.map_eq_append_iff.mp hqs
      subst qs
      have Wp := W.restrict (List.sublist_append_left ps rs)
      have Wr := W.restrict (List.sublist_append_right ps rs)
      have hwl : ∀ s ∈ l.word, s ≤ B := fun s hs => hword s ((left_word_sublist l r p).subset hs)
      have hwr : ∀ s ∈ r.word, s ≤ B := fun s hs => hword s ((right_word_sublist l r p).subset hs)
      have hrready := ih r b rs H Z hrs hbal.2.2 hwr Wr hHlow hHup hZ hZmax
      have hrsne : rs ≠ [] := by
        intro hn
        have hh : depthPhases d r b = [] := by simpa only [hn,List.map_nil] using hrs.symm
        exact depthPhases_ne_nil d r b hh
      have hcrosslow := Wr.first_scale_lower hrsne H
      have hcrossmass := Wr.first_scale_upper hrs hε (balancedThrough_prefix (k := 2) hbal.2.2) H
      have hcross := internal_retained_scale_upper hε hbal.1 hcrossmass
      have hpB : p ≤ B := hword p (by simp [word])
      have hcrosscap : firstScale μ rs H ≤ (9/20:ℝ)*cappedStep μ B p := by
        simpa only [cappedStep,if_pos hpB] using hcross
      have hoffset : firstOffset rs Z = 0 := by
        cases rs with
        | nil => exact False.elim (hrsne rfl)
        | cons q qs => rfl
      have hcrossZ : 0 ≤ firstOffset rs Z := by rw [hoffset]
      have hcrossZmax : firstOffset rs Z ≤ Zmax := by rw [hoffset]; exact hZ.trans hZmax
      have hlready := ih l p ps (firstScale μ rs H) (firstOffset rs Z) hps hbal.2.1 hwl Wp
        hcrosslow hcrosscap hcrossZ hcrossZmax
      exact (sequenceReady_append δ c μ ε ps rs H Z).mpr ⟨hlready,hrready⟩

end
end StrongSilver.ScheduleTree.FourGapGroup
