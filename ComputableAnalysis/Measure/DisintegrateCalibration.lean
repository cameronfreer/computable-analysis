/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.DisintegrateUpper
import ComputableAnalysis.Measure.DisintegrateLower

/-!
# The strong Weihrauch classification of continuous disintegration on Cantor space

Combining the general upper bound `disintegrate_le_lim` with the calibration lower bound
`lim_le_disintegrate`: continuous disintegration of joint laws on `Cantor × Cantor` is strongly
Weihrauch equivalent to `Lim`. This module exists so that users of the general upper bound need
not import the calibration construction.
-/

namespace ComputableAnalysis

open scoped PiNatInstances in
/-- **The exact classification on Cantor space**: continuous disintegration of joint laws on
`Cantor × Cantor` is strongly Weihrauch equivalent to `Lim`. -/
theorem disintegrate_cantor_equiv_lim :
    Disintegrate cantorPresentation cantorPresentation ≡sW Lim :=
  ⟨disintegrate_le_lim _ _, lim_le_disintegrate⟩

end ComputableAnalysis
