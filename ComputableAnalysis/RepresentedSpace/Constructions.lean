/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.RepresentedSpace.ComputableMap

/-!
# Products, sums, and subtypes of representations

The **product** representation names `(a, b)` by interleaving a name of `a` (even
coordinates) with a name of `b` (odd coordinates). The **sum** representation reads a tag
at coordinate `0`: an even track that is `0` at its first coordinate selects the left
summand, anything else the right; the payload lives on the odd track, so the injections are
realized by output pairing (`OracleCode.pairCode`) against a constant tag track.
The **subtype** representation restricts a representation to names of points satisfying
`P`, without totalization.

Structural maps: pairing (`ComputableMap.pair`, via `OracleCode.pairCode`), projections
(via the deinterleaving codes of `Continuity`), injections, `Subtype.val` (via
`query`), and the Cantor–Baire inclusion `encodeCantor` (a valid Cantor name already *is*
the Baire name of its point's encoding, so `query` realizes it).
-/

namespace ComputableAnalysis

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace Representation

/-- Product representation: even coordinates name the first component, odd coordinates the
second. -/
def prod (X : Representation α) (Y : Representation β) : Representation (α × β) where
  rep p := (X.rep p.evenPart).bind fun a => (Y.rep p.oddPart).map fun b => (a, b)
  onto ab := by
    obtain ⟨p, hp⟩ := X.onto ab.1
    obtain ⟨q, hq⟩ := Y.onto ab.2
    refine ⟨Baire.interleave p q, Part.mem_bind_iff.mpr ⟨ab.1, ?_, ?_⟩⟩
    · rwa [Baire.evenPart_interleave]
    · rw [Baire.oddPart_interleave]
      exact Part.mem_map (fun b => (ab.1, b)) hq

/-- Names of the product are exactly interleavings of names of the components. -/
@[simp]
theorem prod_names_iff {X : Representation α} {Y : Representation β} {p : Baire}
    {ab : α × β} :
    (X.prod Y).Names p ab ↔ X.Names p.evenPart ab.1 ∧ Y.Names p.oddPart ab.2 := by
  obtain ⟨a, b⟩ := ab
  simp only [Names, prod, Part.mem_bind_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨a', ha', b', hb', h⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
    exact ⟨ha', hb'⟩
  · exact fun ⟨ha, hb⟩ => ⟨a, ha, b, hb, rfl⟩

/-- Sum representation: the tag at coordinate `0` (the first even-track entry) selects the
summand — `0` for left, anything else for right — and the odd track names the payload. -/
def sum (X : Representation α) (Y : Representation β) : Representation (α ⊕ β) where
  rep p :=
    if p 0 = 0 then (X.rep p.oddPart).map Sum.inl else (Y.rep p.oddPart).map Sum.inr
  onto s := by
    cases s with
    | inl a =>
      obtain ⟨q, hq⟩ := X.onto a
      refine ⟨Baire.interleave (fun _ => 0) q, ?_⟩
      have h0 : Baire.interleave (fun _ => 0) q 0 = 0 := by
        simpa using Baire.interleave_even (fun _ => 0) q 0
      rw [if_pos h0, Baire.oddPart_interleave]
      exact Part.mem_map Sum.inl hq
    | inr b =>
      obtain ⟨q, hq⟩ := Y.onto b
      refine ⟨Baire.interleave (fun _ => 1) q, ?_⟩
      have h0 : Baire.interleave (fun _ => 1) q 0 = 1 := by
        simpa using Baire.interleave_even (fun _ => 1) q 0
      rw [if_neg (by omega), Baire.oddPart_interleave]
      exact Part.mem_map Sum.inr hq

/-- A name denotes `Sum.inl a` exactly when its tag is `0` and its odd track names `a`. -/
@[simp]
theorem sum_names_inl_iff {X : Representation α} {Y : Representation β} {p : Baire}
    {a : α} : (X.sum Y).Names p (Sum.inl a) ↔ p 0 = 0 ∧ X.Names p.oddPart a := by
  by_cases h : p 0 = 0 <;>
    simp [Names, sum, h, Part.mem_map_iff]

/-- A name denotes `Sum.inr b` exactly when its tag is nonzero and its odd track names
`b`. -/
@[simp]
theorem sum_names_inr_iff {X : Representation α} {Y : Representation β} {p : Baire}
    {b : β} : (X.sum Y).Names p (Sum.inr b) ↔ p 0 ≠ 0 ∧ Y.Names p.oddPart b := by
  by_cases h : p 0 = 0 <;>
    simp [Names, sum, h, Part.mem_map_iff]

/-- Subtype representation: the names of `⟨a, h⟩` are exactly the `X`-names of `a`. A name
of a point outside `P` denotes nothing — no totalization. -/
def subtype (X : Representation α) (P : α → Prop) : Representation {a // P a} where
  rep p := (X.rep p).bind fun a => Part.assert (P a) fun h => Part.some ⟨a, h⟩
  onto s := by
    obtain ⟨p, hp⟩ := X.onto s.val
    exact ⟨p, Part.mem_bind_iff.mpr
      ⟨s.val, hp, Part.mem_assert_iff.mpr ⟨s.property, Part.mem_some_iff.mpr rfl⟩⟩⟩

/-- Names of the subtype are exactly names of the underlying point. -/
@[simp]
theorem subtype_names_iff {X : Representation α} {P : α → Prop} {p : Baire}
    {s : {a // P a}} : (X.subtype P).Names p s ↔ X.Names p s.val := by
  simp only [Names, subtype, Part.mem_bind_iff, Part.mem_assert_iff, Part.mem_some_iff]
  constructor
  · rintro ⟨a, ha, h, rfl⟩
    exact ha
  · exact fun h => ⟨s.val, h, s.property, rfl⟩

end Representation

/-! ### Products and sums of represented spaces

Bundled forms of the constructions above, for use where the endpoints of problems and
reductions vary (`RepSpace` enters with units 10–11). -/

/-- The product of two represented spaces: the product carrier under the interleaving
product representation. -/
def RepSpace.prod (X : RepSpace.{u}) (Y : RepSpace.{v}) : RepSpace.{max u v} :=
  ⟨X.carrier × Y.carrier, X.rep.prod Y.rep⟩

/-- The sum of two represented spaces: the sum carrier under the tagged sum
representation. -/
def RepSpace.sum (X : RepSpace.{u}) (Y : RepSpace.{v}) : RepSpace.{max u v} :=
  ⟨X.carrier ⊕ Y.carrier, X.rep.sum Y.rep⟩

/-- The representation of the product space is the product representation. -/
@[simp]
theorem RepSpace.prod_rep (X : RepSpace.{u}) (Y : RepSpace.{v}) :
    (X.prod Y).rep = X.rep.prod Y.rep := rfl

/-- The representation of the sum space is the sum representation. -/
@[simp]
theorem RepSpace.sum_rep (X : RepSpace.{u}) (Y : RepSpace.{v}) :
    (X.sum Y).rep = X.rep.sum Y.rep := rfl

variable {X : Representation α} {Y : Representation β} {Z : Representation γ}

/-- **Pairing.** Two computable maps out of a common source pair into the product,
realized by the output-pairing combinator (`OracleCode.pairCode`). -/
protected theorem ComputableMap.pair {f : α → β} {g : α → γ} (hf : ComputableMap X Y f)
    (hg : ComputableMap X Z g) : ComputableMap X (Y.prod Z) fun a => (f a, g a) := by
  obtain ⟨cf, hcf⟩ := hf
  obtain ⟨cg, hcg⟩ := hg
  refine ⟨OracleCode.pairCode cf cg, fun p a hpa => ?_⟩
  obtain ⟨q, hq, hqf⟩ := hcf p a hpa
  obtain ⟨r, hr, hrg⟩ := hcg p a hpa
  exact ⟨Baire.interleave q r, OracleCode.pairCode_spec hq hr,
    Representation.prod_names_iff.mpr ⟨by simpa using hqf, by simpa using hrg⟩⟩

/-- The first projection is computable, realized by the even-track deinterleaver. -/
theorem computableMap_fst : ComputableMap (X.prod Y) X Prod.fst := by
  obtain ⟨c, hc⟩ := type2Computable_evenPart
  exact ⟨c, .of_computes hc fun p ab hab => (Representation.prod_names_iff.mp hab).1⟩

/-- The second projection is computable, realized by the odd-track deinterleaver. -/
theorem computableMap_snd : ComputableMap (X.prod Y) Y Prod.snd := by
  obtain ⟨c, hc⟩ := type2Computable_oddPart
  exact ⟨c, .of_computes hc fun p ab hab => (Representation.prod_names_iff.mp hab).2⟩

/-- The left injection is computable: pair a constant-`0` tag track with the input. -/
theorem computableMap_inl : ComputableMap X (X.sum Y) Sum.inl := by
  refine ⟨OracleCode.pairCode (.const 0) .query, fun p a hpa => ?_⟩
  refine ⟨Baire.interleave (fun _ => 0) p,
    OracleCode.pairCode_spec (by simp) (by simp),
    Representation.sum_names_inl_iff.mpr ⟨?_, ?_⟩⟩
  · simpa using Baire.interleave_even (fun _ => 0) p 0
  · rwa [Baire.oddPart_interleave]

/-- The right injection is computable: pair a constant-`1` tag track with the input. -/
theorem computableMap_inr : ComputableMap Y (X.sum Y) Sum.inr := by
  refine ⟨OracleCode.pairCode (.const 1) .query, fun p b hpb => ?_⟩
  refine ⟨Baire.interleave (fun _ => 1) p,
    OracleCode.pairCode_spec (by simp) (by simp),
    Representation.sum_names_inr_iff.mpr ⟨?_, ?_⟩⟩
  · have : Baire.interleave (fun _ => 1) p 0 = 1 := by
      simpa using Baire.interleave_even (fun _ => 1) p 0
    omega
  · rwa [Baire.oddPart_interleave]

/-- `Subtype.val` is computable, realized by `query`: a name of the subtype point already
names the underlying point. -/
theorem computableMap_subtypeVal {P : α → Prop} :
    ComputableMap (X.subtype P) X Subtype.val :=
  ⟨.query, fun p s hps => ⟨p, by simp, Representation.subtype_names_iff.mp hps⟩⟩

/-- The Cantor–Baire inclusion `encodeCantor` is computable, realized by `query`: a valid
Cantor name takes values in `{0, 1}`, so it already *is* the Baire name of its point's
encoding. -/
theorem computableMap_encodeCantor : ComputableMap cantorRep baireRep encodeCantor := by
  refine ⟨.query, fun p x hpx => ?_⟩
  obtain ⟨hle, hx⟩ := cantorRep_names_iff.mp hpx
  refine ⟨p, by simp, baireRep_names_iff.mpr ?_⟩
  funext n
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hle n) with h | h <;>
    simp [hx, encodeCantor_apply, h]

end ComputableAnalysis
