-- SPDX-License-Identifier: GPL-3.0-only
-- Exponent alias used by the scalar lemmas copied from the v1.0.0 library.
import Mathlib.Analysis.SpecialFunctions.Pow.Real
namespace StrongSilver.Scalar.Problem
noncomputable def silverExponent : ℝ := Real.log (1 + Real.sqrt 2) / Real.log 2
end StrongSilver.Scalar.Problem
