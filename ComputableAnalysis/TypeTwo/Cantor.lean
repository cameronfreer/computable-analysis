/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.TypeTwo.Baire

/-!
# Cantor space: binary words and translations

`Cantor := ℕ → Bool` carries the product topology (factors discrete); prefixes,
extensions, and cylinders come from the generic stream layer in
`ComputableAnalysis.TypeTwo.Baire`. This file adds the word-level translations
between binary words and natural-number words that the oracle-code layer uses to
feed Cantor data to a machine whose native alphabet is `ℕ`.

Convention (pinned): the Baire coordinate `0` decodes to `false` and every
positive coordinate decodes to `true`; the encoding direction sends `false ↦ 0`,
`true ↦ 1`. This matches the name-level `truncate` retraction introduced with the
stream layer and the Cantor representation `cantorRep` introduced with
represented spaces (whose valid names take values in `{0, 1}` only).
-/

namespace ComputableAnalysis

/-- Cantor space: streams of Booleans, with the product topology. -/
abbrev Cantor : Type := ℕ → Bool

namespace Cantor

/-- The cylinder of Cantor points beginning with the binary word `s`.
An abbreviation for the generic word cylinder, fixing the alphabet. -/
abbrev cylinder (s : List Bool) : Set Cantor :=
  ComputableAnalysis.cylinder s

theorem isClopen_cylinder (s : List Bool) : IsClopen (cylinder s) :=
  ComputableAnalysis.isClopen_cylinder s

end Cantor

/-! ### Word translations -/

/-- Encode a binary word as a natural-number word (`false ↦ 0`, `true ↦ 1`). -/
def boolWordToNat (s : List Bool) : List ℕ :=
  s.map fun b => cond b 1 0

/-- Decode a natural-number word as a binary word (`0 ↦ false`, positive ↦ `true`). -/
def natWordToBool (s : List ℕ) : List Bool :=
  s.map fun n => decide (0 < n)

@[simp]
theorem length_boolWordToNat (s : List Bool) : (boolWordToNat s).length = s.length := by
  simp [boolWordToNat]

@[simp]
theorem length_natWordToBool (s : List ℕ) : (natWordToBool s).length = s.length := by
  simp [natWordToBool]

@[simp]
theorem natWordToBool_boolWordToNat (s : List Bool) :
    natWordToBool (boolWordToNat s) = s := by
  have h : ∀ b : Bool, decide (0 < cond b 1 0) = b := by decide
  simp only [natWordToBool, boolWordToNat, List.map_map, Function.comp_def, h,
    List.map_id']

@[simp]
theorem getElem_boolWordToNat (s : List Bool) (i : ℕ) (h : i < (boolWordToNat s).length) :
    (boolWordToNat s)[i] = cond (s[i]'(by simpa using h)) 1 0 := by
  simp [boolWordToNat]

theorem primrec_boolWordToNat : Primrec boolWordToNat :=
  Primrec.list_map Primrec.id <|
    (Primrec.cond Primrec.id (Primrec.const 1) (Primrec.const 0)).comp₂ Primrec₂.right

theorem primrec_natWordToBool : Primrec natWordToBool :=
  Primrec.list_map Primrec.id <|
    (Primrec.nat_lt.decide.comp (Primrec.const 0) Primrec.id).comp₂ Primrec₂.right

/-! ### Stream-level decoder and encoder -/

/-- Decode a nat-stream to a Cantor point with the pinned decoder (`0 ↦ false`, positive
`↦ true`). A neutral decoding operation — **not** a representation; invalid Cantor names
must remain invalid in the later representation layer (`cantorRep`). -/
def natStreamToBool (p : Baire) : Cantor := fun n => decide (0 < p n)

@[simp] theorem natStreamToBool_apply (p : Baire) (n : ℕ) :
    natStreamToBool p n = decide (0 < p n) := rfl

/-- Encode a Cantor point as a Baire name (`false ↦ 0`, `true ↦ 1`). -/
def encodeCantor (x : Cantor) : Baire := fun n => if x n then 1 else 0

@[simp] theorem encodeCantor_apply (x : Cantor) (n : ℕ) :
    encodeCantor x n = if x n then 1 else 0 := rfl

/-! ### Name-level truncation -/

/-- Truncate a Baire name to a valid Cantor name coordinatewise: `truncate p n = min (p n) 1`.
It fixes names already valued in `{0,1}` and sends every stream to a valid Cantor name,
without totalizing the Cantor representation (`cantorRep` still rejects invalid names). -/
def truncate (p : Baire) : Baire := fun n => min (p n) 1

/-- Every coordinate of `truncate p` is at most one. -/
theorem truncate_le_one (p : Baire) (n : ℕ) : truncate p n ≤ 1 := min_le_right _ _

/-- `truncate` fixes streams already valued in `{0, 1}`. -/
theorem truncate_of_forall_le_one {p : Baire} (h : ∀ n, p n ≤ 1) : truncate p = p := by
  funext n; exact min_eq_left (h n)

end ComputableAnalysis
