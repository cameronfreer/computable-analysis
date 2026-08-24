/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.TypeTwo.Tracks
import ComputableAnalysis.Weihrauch.ParallelProduct
import ComputableAnalysis.Weihrauch.Principles.Limit

/-!
# `Lim` is a cylinder

`id ×ₚ Lim ≤sW Lim`, by one fixed total preprocessor and the trivial postprocessor
`query`. From a name `w` of a pair `(p, x)` — even track `p`, odd track the `Lim` table
`x` — the preprocessor builds the table whose even columns are constant at the
corresponding coordinates of `p` and whose odd columns are the columns of `x`:

* column `2 i` at every stage is `w (2 i)` (i.e. `p i`), so it stabilizes immediately;
* column `2 i + 1` at stage `t` is `x (Nat.pair i t)`, so it stabilizes to column `i`'s
  limit.

The limit stream of the built table is therefore exactly `Baire.interleave p (lim x)` —
which *is* the product name of the answer `(p, lim x)` — so the strong postprocessor is
`query`. The index rewiring is the explicit code `limCylIndexCode`, built from the
arithmetic kit of `Tracks.lean`; the preprocessor `limCylPreCode` is the corresponding
total query rewiring, and the whole construction is choice-free at the code level.

This closes the code layer of the cylinder story for `Lim`: with
`IsCylinder.weihrauch_iff_strong`, every ordinary reduction to `Lim` upgrades to a strong
one.
-/

namespace ComputableAnalysis

namespace OracleCode

/-- The index map of `limCylPreCode`: on `Nat.pair j t`, keep `j` when `j` is even
(even columns read the input's even track directly, ignoring the stage), and point into
the odd track's table entry `Nat.pair (j / 2) t` when `j` is odd. -/
def limCylIndexCode : OracleCode :=
  comp
    (caseszCode left
      (comp succ (comp doubleCode (pair (comp left (comp div2mod2Code left)) right))))
    (pair .id (comp right (comp div2mod2Code left)))

theorem eval_limCylIndexCode (p : Baire) (m : ℕ) :
    limCylIndexCode.eval p m = Part.some (if m.unpair.1 % 2 = 0 then m.unpair.1
      else 2 * Nat.pair (m.unpair.1 / 2) m.unpair.2 + 1) := by
  simp only [limCylIndexCode]
  have hd : (comp div2mod2Code left).eval p m =
      Part.some (Nat.pair (m.unpair.1 / 2) (m.unpair.1 % 2)) := by
    rw [eval_comp_some (eval_left p m), eval_div2mod2Code]
  rw [eval_comp_some (show (pair OracleCode.id (comp right (comp div2mod2Code left))).eval
      p m = Part.some (Nat.pair m (m.unpair.1 % 2)) from
    eval_pair_some (eval_id p m) (by rw [eval_comp_some hd, eval_right, Nat.unpair_pair]))]
  rcases Nat.mod_two_eq_zero_or_one m.unpair.1 with h | h
  · rw [h, eval_caseszCode_zero, ite_eq_left rfl, eval_left]
  · rw [h, eval_caseszCode_one _ (eval_left p m), ite_eq_right one_ne_zero]
    rw [eval_comp_some (show (comp doubleCode (pair (comp left (comp div2mod2Code left))
        right)).eval p m = Part.some (2 * Nat.pair (m.unpair.1 / 2) m.unpair.2) by
      rw [eval_comp_some (eval_pair_some
        (by rw [eval_comp_some hd, eval_left, Nat.unpair_pair]) (eval_right p m)),
        eval_doubleCode]), eval_succ]

/-- The preprocessor of `Lim.isCylinder`: the total query rewiring along
`limCylIndexCode`. -/
def limCylPreCode : OracleCode := comp query limCylIndexCode

theorem evalStream_limCylPreCode (w : Baire) :
    limCylPreCode.evalStream w = Part.some (fun m => w (if m.unpair.1 % 2 = 0
      then m.unpair.1 else 2 * Nat.pair (m.unpair.1 / 2) m.unpair.2 + 1)) :=
  evalStream_query_comp eval_limCylIndexCode w

end OracleCode

/-- The table built by `limCylPreCode`, as a function of the input name. -/
private def cylTable (w : Baire) : Baire := fun m =>
  w (if m.unpair.1 % 2 = 0 then m.unpair.1
    else 2 * Nat.pair (m.unpair.1 / 2) m.unpair.2 + 1)

/-- An even column of the built table is constant at the input's corresponding
coordinate. -/
private theorem cylTable_even {w : Baire} {j t : ℕ} (h : j % 2 = 0) :
    cylTable w (Nat.pair j t) = w j := by
  simp [cylTable, Nat.unpair_pair, h]

/-- An odd column of the built table is the corresponding column of the odd track. -/
private theorem cylTable_odd {w : Baire} {j t : ℕ} (h : j % 2 = 1) :
    cylTable w (Nat.pair j t) = w.oddPart (Nat.pair (j / 2) t) := by
  simp [cylTable, Nat.unpair_pair, h, Baire.oddPart_apply]

/-- **`Lim` is a cylinder**: `id ×ₚ Lim ≤sW Lim` via `limCylPreCode` and the trivial
postprocessor `query`. The built table's limit stream is itself the product name of the
answer, so nothing remains for the postprocessor to do. -/
theorem Lim.isCylinder : IsCylinder Lim := by
  refine strongReduction_iff_exists_reductionPair.mpr
    ⟨.limCylPreCode, .query, fun w x hwx hdom => ?_⟩
  obtain ⟨hx₁, hx₂⟩ := Representation.prod_names_iff.mp hwx
  have hx1 : x.1 = w.evenPart := baireRep_names_iff.mp hx₁
  have hx2 : x.2 = w.oddPart := baireRep_names_iff.mp hx₂
  rw [Problem.prod_dom_iff] at hdom
  obtain ⟨-, ℓ, hℓ⟩ := hdom
  rw [hx2] at hℓ
  replace hℓ := Lim.accepts_iff.mp hℓ
  have hzmem : cylTable w ∈ OracleCode.limCylPreCode.evalStream w := by
    rw [OracleCode.evalStream_limCylPreCode]; exact Part.mem_some _
  have hzdom : Lim.Dom (cylTable w) := by
    refine ⟨Baire.interleave w.evenPart ℓ, Lim.accepts_iff.mpr fun j => ?_⟩
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · refine ⟨0, fun t _ => ?_⟩
      rw [cylTable_even h]
      change w j = if j % 2 = 0 then w.evenPart (j / 2) else ℓ (j / 2)
      rw [ite_eq_left h, Baire.evenPart_apply]
      exact congrArg w (by omega)
    · obtain ⟨s, hs⟩ := hℓ (j / 2)
      refine ⟨s, fun t ht => ?_⟩
      rw [cylTable_odd h, hs t ht]
      change ℓ (j / 2) = if j % 2 = 0 then w.evenPart (j / 2) else ℓ (j / 2)
      rw [ite_eq_right (by omega)]
  refine ⟨cylTable w, hzmem, cylTable w, baireRep_names_iff.mpr rfl, hzdom,
    fun a y' hay' hacc => ?_⟩
  obtain rfl : y' = a := baireRep_names_iff.mp hay'
  replace hacc := Lim.accepts_iff.mp hacc
  have hid : y'.evenPart = x.1 := by
    rw [hx1]
    funext i
    obtain ⟨s, hs⟩ := hacc (2 * i)
    have h := hs s le_rfl
    rw [cylTable_even (by omega)] at h
    rw [Baire.evenPart_apply, Baire.evenPart_apply y' i, ← h]
  have hlim : Lim.accepts x.2 y'.oddPart := by
    rw [hx2, Lim.accepts_iff]
    intro i
    obtain ⟨s, hs⟩ := hacc (2 * i + 1)
    refine ⟨s, fun t ht => ?_⟩
    have h := hs t ht
    rw [cylTable_odd (by omega)] at h
    have h2 : (2 * i + 1) / 2 = i := by omega
    rw [h2] at h
    rw [h, Baire.oddPart_apply y' i]
  exact ⟨y', OracleCode.mem_evalStream.mpr fun n => by
      rw [OracleCode.eval_query y' n]; exact Part.mem_some _,
    (y'.evenPart, y'.oddPart),
    Representation.prod_names_iff.mpr
      ⟨baireRep_names_iff.mpr rfl, baireRep_names_iff.mpr rfl⟩,
    Problem.prod_accepts_iff.mpr ⟨hid, hlim⟩⟩

end ComputableAnalysis
