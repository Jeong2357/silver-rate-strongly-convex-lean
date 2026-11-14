-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.AdjacentOccurrenceMembership
import Mathlib.Data.List.Nodup

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 4800000
variable {α β : Type*}

def optionPairMap (f : α → Option β) (p : α × α) : Option (β × β) :=
  (f p.1).bind fun a => (f p.2).map fun b => (a,b)

theorem adjacentOccurrences_tail_sublist (a : α) (xs : List α) :
    (adjacentOccurrences xs).Sublist (adjacentOccurrences (a::xs)) := by
  cases xs with
  | nil => simp [adjacentOccurrences]
  | cons b bs => exact List.sublist_cons_self _ _

/-- Filtering absent labels preserves the order and multiplicity of
the adjacent pairs whose two labels are present. -/
theorem adjacentOccurrences_filterMap_sublist (f : α → Option β) (xs : List α) :
    ((adjacentOccurrences xs).filterMap (optionPairMap f)).Sublist
      (adjacentOccurrences (xs.filterMap f)) := by
  induction xs with
  | nil => simp [adjacentOccurrences]
  | cons a xs ih =>
    cases xs with
    | nil => simp [adjacentOccurrences]
    | cons b bs =>
      cases ha : f a with
      | none =>
        simpa only [adjacentOccurrences,List.filterMap_cons,optionPairMap,ha,Option.bind_none] using ih
      | some u =>
        cases hb : f b with
        | none =>
          simp only [adjacentOccurrences,List.filterMap_cons,optionPairMap,ha,hb,Option.bind_some,Option.map_none]
          have ht : ((adjacentOccurrences (b::bs)).filterMap (optionPairMap f)).Sublist
              (adjacentOccurrences (bs.filterMap f)) := by simpa only [List.filterMap_cons,hb] using ih
          exact ht.trans (adjacentOccurrences_tail_sublist u _)
        | some v =>
          have ht : ((adjacentOccurrences (b::bs)).filterMap (optionPairMap f)).Sublist
              (adjacentOccurrences (v::bs.filterMap f)) := by simpa only [List.filterMap_cons,hb] using ih
          simpa only [adjacentOccurrences,List.filterMap_cons,optionPairMap,ha,hb,Option.bind_some,Option.map_some]
            using List.Sublist.cons_cons (u,v) ht

theorem adjacentOccurrences_nodup {xs : List α} (hx : xs.Nodup) : (adjacentOccurrences xs).Nodup := by
  induction xs with
  | nil => simp [adjacentOccurrences]
  | cons a xs ih =>
    cases xs with
    | nil => simp [adjacentOccurrences]
    | cons b bs =>
      have htail := List.nodup_cons.mp hx
      apply List.nodup_cons.mpr
      constructor
      · intro hp
        exact htail.1 (adjacentOccurrences_members hp).1
      · exact ih htail.2

end
end StrongSilver
