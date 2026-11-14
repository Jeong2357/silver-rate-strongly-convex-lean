-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CartesianGroupDataFromBalance
import StrongSilver.CartesianUniformGroups

namespace StrongSilver.ScheduleTree.FourGapGroup
open FourPhase Scalar.SignedIntervals
noncomputable section
set_option maxHeartbeats 4800000

/-- Uniform bounds for every actual depth group are derived from one
balanced original Cartesian tree, one common negative-mass budget, and
one curvature bound. No per-group construction assumptions are retained. -/
theorem exists_uniform_groups_radius {δ : ℝ} (hδ : 0 < δ) : ∃ τ > 0,
    ∀ c μ B ε L U : ℝ, ∀ d : ℕ, ∀ t : ScheduleTree, ∀ b : ℝ, ∀ qs : List Group,
    0 < μ → 0 ≤ B → μ*B ≤ 1/10000 → μ*b ≤ 1/10000 → 0 ≤ ε →
    ε+μ*t.prefixMass (logarithmicStep μ) ≤ τ →
    t.Cartesian → (∀ s ∈ t.word, s ≤ B) → 0 < b → (∀ s ∈ t.word, s ≤ b) →
    balancedThrough (logarithmicStep μ) ε (d+2) t →
    qs.map (fun q => (q.1.tree,q.2)) = depthPhases d t b →
    1000 ≤ L → L ≤ (1/4:ℝ)^(d+2)*t.prefixMass (logarithmicStep μ) → b ≤ U →
    negativeMass t.word ≤ L/1000 → 2*U*negativeMass t.word ≤ c*L^2 →
    UniformGroups δ c μ B ε L U qs := by
  obtain ⟨Cb,hCb,db,hdb,hshape⟩ := exists_balanced_shape_constants
  obtain ⟨dt,hdt,htime⟩ := exists_uniform_exterior_time_radius
  let τ := min δ (min dt (min db (min (1/100) (1/(100*Cb)))))
  have hτ : 0 < τ := lt_min hδ (lt_min hdt (lt_min hdb (lt_min (by norm_num) (by positivity))))
  refine ⟨τ,hτ,?_⟩
  intro c μ B ε L U d t b qs hμ hB hμB hμb hε hnear hc hword hb hdom hbal hqs hL hLdepth hbU hN hNbudget
  have hτδ : τ ≤ δ := min_le_left _ _
  have hτdt : τ ≤ dt := (min_le_right _ _).trans (min_le_left _ _)
  have hτdb : τ ≤ db := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hτ100 : τ ≤ 1/100 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hτCb : τ ≤ 1/(100*Cb) := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hMroot := prefixMass_positive (logarithmicStep μ) t
  have hετ : ε ≤ τ := by linarith only [hnear,mul_nonneg hμ.le hMroot.le]
  have hε100 : ε ≤ 1/100 := hετ.trans hτ100
  have hε1 : ε < 1 := hε100.trans_lt (by norm_num)
  have hCbε : Cb*ε ≤ 1/100 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num) hCb)).mp (hετ.trans hτCb)
    nlinarith only [hh]
  have hU0 : 0 ≤ U := hb.le.trans hbU
  have hinfo (q : Group) (hq : q ∈ qs) :
      q.1.tree.Cartesian ∧ q.1.tree.word.Sublist t.word ∧
      (∀ s ∈ q.1.tree.word, s ≤ q.2) ∧ 0 < q.2 ∧ q.2 ≤ b := by
    have hphase : (q.1.tree,q.2) ∈ depthPhases d t b := hqs ▸ List.mem_map.mpr ⟨q,hq,rfl⟩
    exact depthPhases_original_bounds hc hb hdom d _ hphase
  have hscales (q : Group) (hq : q ∈ qs) : L ≤ groupScale μ q ∧ groupScale μ q ≤ t.prefixMass (logarithmicStep μ) := by
    have hh := depth_groups_scale_bounds hε100 hbal hqs hq
    exact ⟨hLdepth.trans hh.1,hh.2⟩
  have hlocalnear (q : Group) (hq : q ∈ qs) : ε+μ*groupScale μ q ≤ τ := by
    have hh := mul_le_mul_of_nonneg_left (hscales q hq).2 hμ.le
    linarith only [hh,hnear]
  have hbalances (q : Group) (hq : q ∈ qs) := depth_group_balances hbal hqs hq
  have hmassShape (q : Group) (hq : q ∈ qs) :
      ∀ i, |q.1.massShape (logarithmicStep μ) (groupScale μ q) i-reference i| ≤ 1/100 := by
    have hh := hshape q.1 (logarithmicStep μ) ε hε (hετ.trans hτdb)
      (hbalances q hq).1 (hbalances q hq).2.1 (hbalances q hq).2.2
    exact fun i => (hh i).trans hCbε
  have hdata (q : Group) (hq : q ∈ qs) :
      BalancedGroupData q.1 μ (groupScale μ q) q.2 ε ∧ 100 ≤ q.2 ∧
      drawdown ((q.1.gaps 3).map (logarithmicStep μ)) ≤ q.2/100 := by
    have hi := hinfo q hq
    have hqB : ∀ s ∈ q.1.tree.word, s ≤ B := fun s hs => hword s (hi.2.1.subset hs)
    have hqN := (negative_mass_sublist_le hi.2.1).trans hN
    exact group_data_from_original_balance rfl (hL.trans (hscales q hq).1) hμ hμB
      ((mul_le_mul_of_nonneg_left hi.2.2.2.2 hμ.le).trans hμb) hε hi.1 hqB hi.2.2.1
      (hbalances q hq).1 (hbalances q hq).2.1 (hbalances q hq).2.2 (hmassShape q hq)
      (hqN.trans (by linarith only [(hscales q hq).1]))
  have htimes (q : Group) (hq : q ∈ qs) := htime q.1 μ (groupScale μ q) q.2 ε B (hdata q hq).1
    ((hlocalnear q hq).trans hτdt) hB (by linarith only [hμB]) (hdata q hq).2.1 (hdata q hq).2.2
    ((mul_le_mul_of_nonneg_left (hinfo q hq).2.2.2.2 hμ.le).trans hμb)
  refine {
    data := fun q hq => (hdata q hq).1
    near := fun q hq => (hlocalnear q hq).trans hτδ
    scale_lower := fun q hq => (hscales q hq).1
    scale_upper := ?_
    boundary_upper := fun q hq => (hinfo q hq).2.2.2.2.trans hbU
    time_lower := fun q hq => (htimes q hq).1
    time_upper := fun q hq => (htimes q hq).2
    negative_budget := ?_
  }
  · intro q hq
    have hbs := hbalances q hq
    exact group_scale_upper (zero_lt_one.trans_le (hdata q hq).1.scale_lower)
      (positive_excess_of_balance hbs.1 hε1) (positive_excess_of_balance hbs.2.1 hε1)
      (positive_excess_of_balance hbs.2.2 hε1) (hmassShape q hq)
  · intro q hq i
    have hsub := (q.1.gap_word_sublist i.castSucc).trans (hinfo q hq).2.1
    have hn := negative_mass_sublist_le hsub
    exact (mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 2*U)).trans hNbudget

end
end StrongSilver.ScheduleTree.FourGapGroup
