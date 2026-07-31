/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.TypeTwo.Tracks
import ComputableAnalysis.RepresentedSpace.Constructions

/-!
# The countable-product representation

`Representation.sequence` represents `ℕ → α` by packing one name per coordinate along the
track convention of `Tracks.lean`: `F` names `x` exactly when for every `n`, track `n` of
`F` names `x n` (`sequence_names_iff`). The representation itself uses classical choice
(countable name selection in surjectivity); the *code kit* it runs on is the fully explicit,
axiom-free one of `Tracks.lean`.

The structural computable maps are the consumers the parallelization layer needs:

* `computableMap_const_sequence` / `computableMap_apply_sequence` — the constant family and
  coordinate evaluation (extensivity of parallelization);
* `computableMap_sequence_prod` / `computableMap_prod_sequence` — the canonical bijection
  between a product of sequences and a sequence of products, computable in both directions
  (ordinary monotonicity);
* `computableMap_sequence_flatten` / `computableMap_sequence_unflatten` — the canonical
  bijection between a sequence of sequences and a sequence along `Nat.pair`, computable in
  both directions (idempotence).
-/

namespace ComputableAnalysis

universe u v

variable {α : Type u} {β : Type v}

namespace Representation

/-- The countable-product representation of `ℕ → α`: a name packs one `X`-name per
coordinate along `Baire.track`. Defined exactly when every track denotes. -/
def sequence (X : Representation α) : Representation (ℕ → α) where
  rep F := ⟨∀ n, (X.rep (Baire.track n F)).Dom, fun h n => (X.rep (Baire.track n F)).get (h n)⟩
  onto x := by
    choose p hp using fun n => X.onto (x n)
    refine ⟨Baire.packTracks p, fun n => ?_, funext fun n => ?_⟩
    · rw [Baire.track_packTracks]
      exact Part.dom_iff_mem.mpr ⟨x n, hp n⟩
    · exact Part.get_eq_of_mem
        (Baire.track_packTracks p n ▸ hp n : x n ∈ X.rep (Baire.track n _)) _

/-- Names of the countable product are exactly trackwise names. -/
@[simp]
theorem sequence_names_iff {X : Representation α} {F : Baire} {x : ℕ → α} :
    X.sequence.Names F x ↔ ∀ n, X.Names (Baire.track n F) (x n) := by
  constructor
  · rintro ⟨h, hval⟩ n
    exact congrFun hval n ▸ Part.get_mem (h n)
  · intro h
    exact ⟨fun n => Part.dom_iff_mem.mpr ⟨x n, h n⟩,
      funext fun n => Part.get_eq_of_mem (h n) _⟩

/-- Names of a **packed** family: a packed name denotes the family its members denote.
The normal form for producing sequence names, since a producer naturally has one name per
coordinate rather than a single packed stream. -/
theorem sequence_names_packTracks_iff {X : Representation α} {g : ℕ → Baire}
    {x : ℕ → α} :
    X.sequence.Names (Baire.packTracks g) x ↔ ∀ n, X.Names (g n) (x n) := by
  rw [sequence_names_iff]
  exact forall_congr' fun n => by rw [Baire.track_packTracks]

end Representation

/-! ### Concrete normal forms

The two sequence representations that occur throughout the Weihrauch layer, with their
names unfolded to a direct statement about the packed stream. -/

/-- A name of a sequence of **streams** is the packing: coordinate `n` is track `n`. -/
theorem baireSequence_names_iff {p : Baire} {xs : ℕ → Baire} :
    baireRep.sequence.Names p xs ↔ ∀ n, xs n = Baire.track n p := by
  rw [Representation.sequence_names_iff]
  exact forall_congr' fun n => baireRep_names_iff

/-- A name of a sequence of **naturals** carries coordinate `n` at the head of track `n`:
the bit-decoding normal form for parallelized `natSpace`-valued principles. -/
theorem natSequence_names_iff {p : Baire} {xs : ℕ → ℕ} :
    natRep.sequence.Names p xs ↔ ∀ n, xs n = p (Nat.pair n 0) := by
  rw [Representation.sequence_names_iff]
  exact forall_congr' fun n => natRep_names_iff

/-- The countable product of a represented space, on the ordinary carrier `ℕ → X`. -/
def RepSpace.sequence (X : RepSpace.{u}) : RepSpace.{u} :=
  ⟨ℕ → X.carrier, X.rep.sequence⟩

namespace Representation

/-- The constant family is computable, realized by `repeatTracksCode`. -/
theorem computableMap_const_sequence (X : Representation α) :
    ComputableMap X X.sequence fun a _ => a := by
  refine ⟨.repeatTracksCode, fun p a hpa => ?_⟩
  refine ⟨fun m => p m.unpair.2, ?_, ?_⟩
  · rw [OracleCode.evalStream_repeatTracksCode]
    exact Part.mem_some _
  · rw [sequence_names_iff]
    intro n
    rw [OracleCode.track_repeatTracks]
    exact hpa

/-- Evaluation at a fixed coordinate is computable, realized by `extractTrackCode`. -/
theorem computableMap_apply_sequence (X : Representation α) (n : ℕ) :
    ComputableMap X.sequence X fun x => x n := by
  refine ⟨.extractTrackCode n, fun F x hFx => ?_⟩
  refine ⟨Baire.track n F, ?_, sequence_names_iff.mp hFx n⟩
  rw [OracleCode.evalStream_extractTrackCode]
  exact Part.mem_some _

/-- A product of sequences maps computably to the sequence of products, realized by
`zipTracksCode`. -/
theorem computableMap_sequence_prod (X : Representation α) (Y : Representation β) :
    ComputableMap (X.sequence.prod Y.sequence) ((X.prod Y).sequence)
      fun fg n => (fg.1 n, fg.2 n) := by
  refine ⟨.zipTracksCode, fun r fg hr => ?_⟩
  rw [prod_names_iff] at hr
  refine ⟨fun m => r (2 * Nat.pair m.unpair.1 (m.unpair.2 / 2) + m.unpair.2 % 2), ?_, ?_⟩
  · rw [OracleCode.evalStream_zipTracksCode]
    exact Part.mem_some _
  · rw [sequence_names_iff]
    intro n
    rw [prod_names_iff, OracleCode.track_zipTracks, Baire.evenPart_interleave,
      Baire.oddPart_interleave]
    exact ⟨sequence_names_iff.mp hr.1 n, sequence_names_iff.mp hr.2 n⟩

/-- A sequence of products maps computably to the product of sequences, realized by
`unzipTracksCode`. -/
theorem computableMap_prod_sequence (X : Representation α) (Y : Representation β) :
    ComputableMap ((X.prod Y).sequence) (X.sequence.prod Y.sequence)
      fun h => (fun n => (h n).1, fun n => (h n).2) := by
  refine ⟨.unzipTracksCode, fun G h hG => ?_⟩
  refine ⟨fun j => G (Nat.pair (j / 2).unpair.1 (2 * (j / 2).unpair.2 + j % 2)), ?_, ?_⟩
  · rw [OracleCode.evalStream_unzipTracksCode]
    exact Part.mem_some _
  · rw [prod_names_iff]
    constructor
    · rw [sequence_names_iff]
      intro n
      rw [OracleCode.track_evenPart_unzipTracks]
      exact (prod_names_iff.mp (sequence_names_iff.mp hG n)).1
    · rw [sequence_names_iff]
      intro n
      rw [OracleCode.track_oddPart_unzipTracks]
      exact (prod_names_iff.mp (sequence_names_iff.mp hG n)).2

/-- A sequence of sequences flattens computably along `Nat.pair`, realized by
`flattenTracksCode`. -/
theorem computableMap_sequence_flatten (X : Representation α) :
    ComputableMap X.sequence.sequence X.sequence
      fun f m => f m.unpair.1 m.unpair.2 := by
  refine ⟨.flattenTracksCode, fun F f hF => ?_⟩
  refine ⟨fun m => F (Nat.pair m.unpair.1.unpair.1 (Nat.pair m.unpair.1.unpair.2 m.unpair.2)),
    ?_, ?_⟩
  · rw [OracleCode.evalStream_flattenTracksCode]
    exact Part.mem_some _
  · rw [sequence_names_iff]
    intro m
    rw [OracleCode.track_flattenTracks]
    exact sequence_names_iff.mp (sequence_names_iff.mp hF m.unpair.1) m.unpair.2

/-- A sequence unflattens computably to a sequence of sequences, realized by
`unflattenTracksCode`. -/
theorem computableMap_sequence_unflatten (X : Representation α) :
    ComputableMap X.sequence X.sequence.sequence
      fun g s t => g (Nat.pair s t) := by
  refine ⟨.unflattenTracksCode, fun G g hG => ?_⟩
  refine ⟨fun m => G (Nat.pair (Nat.pair m.unpair.1 m.unpair.2.unpair.1) m.unpair.2.unpair.2),
    ?_, ?_⟩
  · rw [OracleCode.evalStream_unflattenTracksCode]
    exact Part.mem_some _
  · rw [sequence_names_iff]
    intro s
    rw [sequence_names_iff]
    intro t
    rw [OracleCode.track_unflattenTracks]
    exact sequence_names_iff.mp hG (Nat.pair s t)

end Representation

end ComputableAnalysis
