/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.ForMathlib.PrimrecContainers

/-!
# Compatibility shim: `TypeTwo/PrimrecContainers` moved to `ForMathlib/PrimrecContainers`

The declarations are unchanged, in the same namespace; only the module path moved, when the
`ForMathlib/` staging folder was introduced (see issue #21).

This shim exists because relocating a module breaks any downstream file importing the old path
directly, even though no declaration changed. Prefer
`ComputableAnalysis.ForMathlib.PrimrecContainers` in new code; this file will be removed once
known consumers have migrated.
-/
