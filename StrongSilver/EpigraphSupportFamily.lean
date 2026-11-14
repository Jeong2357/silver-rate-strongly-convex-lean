-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.SupportFamilies

namespace StrongSilver
open Set
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [ProperSpace V]
variable {ι : Type*}

/-- Extract the exact proximal values and supporting gradients of an actual
Moreau objective at any collection of query points. -/
def SupportFamily.ofEpigraph (P : Moreau.Epigraph V) (x : ι → V) : SupportFamily ι V where
  z := fun i => Moreau.proximal P (x i)
  g := fun i => Moreau.gradient P (x i)
  d := fun i => (Moreau.minimizingPair P (x i)).2
  nonnegative := fun i => P.nonnegative _ (Moreau.minimizingPair_mem P (x i))
  origin := by
    intro i
    have hh := (Moreau.minimizingPair_supports P (x i)).2 (0,0) P.zero_mem
    simp only [sub_zero,zero_sub,inner_neg_right] at hh
    linarith only [hh]
  supports := by
    intro i j
    exact (Moreau.minimizingPair_supports P (x i)).2 _ (Moreau.minimizingPair_mem P (x j))

theorem SupportFamily.ofEpigraph_split (P : Moreau.Epigraph V) (x : ι → V) (i : ι) :
    x i = (SupportFamily.ofEpigraph P x).z i+(SupportFamily.ofEpigraph P x).g i := by
  change x i = Moreau.proximal P (x i)+(x i-Moreau.proximal P (x i))
  abel

end
end StrongSilver
