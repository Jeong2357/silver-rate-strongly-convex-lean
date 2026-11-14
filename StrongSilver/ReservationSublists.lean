-- SPDX-License-Identifier: GPL-3.0-only
import StrongSilver.CompleteCutAssembly

namespace StrongSilver
noncomputable section
set_option maxHeartbeats 3600000

namespace CutAssembly

theorem reserved_sublist (s : CutAssembly) : s.reserved.Sublist s.phases := by
  induction s with
  | ordinaryEnd q => simp [reserved,phases]
  | ordinary q s ih => exact ih.cons q
  | block q I c s ih =>
    exact ((ih.cons₂ c).append_left I).cons₂ q
  | blockEnd q I c => exact List.Sublist.refl _
  | noConnector q I => exact List.Sublist.refl _

end CutAssembly
namespace CompleteCutAssembly

theorem reserved_sublist (s : CompleteCutAssembly) : s.reserved.Sublist s.phases := by
  cases s with
  | scalar I => exact List.Sublist.refl _
  | positive s => exact s.reserved_sublist
  | leadingBlock I c s => exact (s.reserved_sublist.cons₂ c).append_left I
  | leadingEnd I c => exact List.Sublist.refl _

end CompleteCutAssembly
end
end StrongSilver
