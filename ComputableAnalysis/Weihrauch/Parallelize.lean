/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Weihrauch.Witness
import ComputableAnalysis.RepresentedSpace.Sequence

/-!
# Countable parallelization and its closure laws

`Problem.parallelize f` runs countably many independent instances of `f`: inputs and
outputs live in the countable-product spaces of `Sequence.lean`, and acceptance is
coordinatewise. The closure laws are proved by explicit reduction pairs over the track
kit, and the code layer is **fully computable** — `mapTracks` and the reshuffling codes
are axiom-free, so the bundled lifting combinators are plain `def`s:

* **Lifting** (monotonicity): a strong pair `(K, H)` lifts to
  `(mapTracks K, mapTracks H)` — the same codes run trackwise, uniformity being exactly
  the fixed-code quantifier order of the reduction. An ordinary pair lifts to
  `(mapTracks K, (mapTracks H).subst zipTracksCode)`: an ordinary postprocessor for the
  parallelization sees the interleaving of the *packed* input with the *packed* answer,
  and `zipTracksCode` re-pairs them trackwise into the packed family of interleavings
  each instance's postprocessor expects.
* **Extensivity** `f ≤sW f.parallelize`: name the constant family
  (`repeatTracksCode`), answer with track `0` (`extractTrackCode 0`).
* **Idempotence** `f.parallelize.parallelize ≡sW f.parallelize`: the two directions are
  the flatten/unflatten rewirings along `Nat.pair`.
* **Congruence**: `≡W`-equivalent problems have `≡W`-equivalent parallelizations.

These are closure laws for the (future) parallelization closure operator on degrees;
packaging as a mathlib `ClosureOperator` waits for a set-sized quotient of degrees
(deferred). Parallelization as a closure operator is from Brattka–Gherardi
(arXiv:0905.4679).
-/

namespace ComputableAnalysis

universe u v u' v'

variable {X : RepSpace.{u}} {Y : RepSpace.{v}} {X' : RepSpace.{u'}} {Y' : RepSpace.{v'}}

/-- **Countable parallelization**: countably many independent instances of `f`, with
coordinatewise acceptance on the countable-product spaces. -/
def Problem.parallelize (f : Problem X Y) : Problem X.sequence Y.sequence :=
  ⟨fun xs ys => ∀ n, f.accepts (xs n) (ys n)⟩

/-- Definitional unfolding of `Problem.parallelize.accepts`. -/
theorem Problem.parallelize_accepts_iff {f : Problem X Y} {xs : ℕ → X} {ys : ℕ → Y} :
    f.parallelize.accepts xs ys ↔ ∀ n, f.accepts (xs n) (ys n) :=
  Iff.rfl

/-- The domain of the parallelization is the coordinatewise domain. -/
@[simp]
theorem Problem.parallelize_dom_iff {f : Problem X Y} {xs : ℕ → X} :
    f.parallelize.Dom xs ↔ ∀ n, f.Dom (xs n) := by
  constructor
  · rintro ⟨ys, h⟩ n
    exact ⟨ys n, h n⟩
  · intro h
    choose ys hys using h
    exact ⟨ys, hys⟩

/-- Parallelization respects extensional equivalence of problems. -/
protected theorem Problem.Equivalent.parallelize {f f' : Problem X Y}
    (h : f.Equivalent f') : f.parallelize.Equivalent f'.parallelize :=
  fun xs ys => forall_congr' fun n => h (xs n) (ys n)

/-- Track `t` of a `Nat.pair`-packed family of streams. -/
private theorem track_pack (g : ℕ → Baire) (t : ℕ) :
    Baire.track t (fun m => g m.unpair.1 m.unpair.2) = g t :=
  funext fun k => by simp [Nat.unpair_pair]

/-! ### Lifting reductions trackwise -/

/-- **Strong lifting**: a strong reduction pair lifts to the parallelizations by running
both codes trackwise. Uniformity — one code serving every coordinate — is exactly the
fixed-code quantifier order of the reduction. -/
protected theorem IsStrongReductionPair.parallelize {f : Problem X Y} {g : Problem X' Y'}
    {K H : OracleCode} (hp : IsStrongReductionPair f g K H) :
    IsStrongReductionPair f.parallelize g.parallelize K.mapTracks H.mapTracks := by
  intro F xs hF hdom
  have hFn := Representation.sequence_names_iff.mp hF
  rw [Problem.parallelize_dom_iff] at hdom
  choose k hk x' hx' hdom' hH using fun n => hp (Baire.track n F) (xs n) (hFn n) (hdom n)
  refine ⟨fun m => k m.unpair.1 m.unpair.2, ?_, fun n => x' n, ?_, ?_, ?_⟩
  · rw [OracleCode.evalStream_mapTracks_iff]
    intro t
    rw [track_pack]
    exact hk t
  · exact Representation.sequence_names_iff.mpr fun n => by rw [track_pack]; exact hx' n
  · exact Problem.parallelize_dom_iff.mpr hdom'
  · intro a ys' ha hacc
    have han := Representation.sequence_names_iff.mp ha
    choose q hq y hy hfacc using fun n =>
      hH n (Baire.track n a) (ys' n) (han n) (hacc n)
    refine ⟨fun m => q m.unpair.1 m.unpair.2, ?_, fun n => y n, ?_, fun n => hfacc n⟩
    · rw [OracleCode.evalStream_mapTracks_iff]
      intro t
      rw [track_pack]
      exact hq t
    · exact Representation.sequence_names_iff.mpr fun n => by rw [track_pack]; exact hy n

/-- **Ordinary lifting**: as the strong case for the preprocessor; the postprocessor
first re-pairs the interleaving of the packed input with the packed answer into the
packed family of trackwise interleavings (`zipTracksCode`), then runs `H` trackwise. -/
protected theorem IsReductionPair.parallelize {f : Problem X Y} {g : Problem X' Y'}
    {K H : OracleCode} (hp : IsReductionPair f g K H) :
    IsReductionPair f.parallelize g.parallelize K.mapTracks
      (H.mapTracks.subst .zipTracksCode) := by
  intro F xs hF hdom
  have hFn := Representation.sequence_names_iff.mp hF
  rw [Problem.parallelize_dom_iff] at hdom
  choose k hk x' hx' hdom' hH using fun n => hp (Baire.track n F) (xs n) (hFn n) (hdom n)
  refine ⟨fun m => k m.unpair.1 m.unpair.2, ?_, fun n => x' n, ?_, ?_, ?_⟩
  · rw [OracleCode.evalStream_mapTracks_iff]
    intro t
    rw [track_pack]
    exact hk t
  · exact Representation.sequence_names_iff.mpr fun n => by rw [track_pack]; exact hx' n
  · exact Problem.parallelize_dom_iff.mpr hdom'
  · intro a ys' ha hacc
    have han := Representation.sequence_names_iff.mp ha
    choose q hq y hy hfacc using fun n =>
      hH n (Baire.track n a) (ys' n) (han n) (hacc n)
    have hzip : (fun m => Baire.interleave F a
        (2 * Nat.pair m.unpair.1 (m.unpair.2 / 2) + m.unpair.2 % 2)) ∈
        OracleCode.zipTracksCode.evalStream (Baire.interleave F a) := by
      rw [OracleCode.evalStream_zipTracksCode]
      exact Part.mem_some _
    refine ⟨fun m => q m.unpair.1 m.unpair.2, ?_, fun n => y n, ?_, fun n => hfacc n⟩
    · rw [OracleCode.evalStream_subst hzip, OracleCode.evalStream_mapTracks_iff]
      intro t
      rw [track_pack, OracleCode.track_zipTracks, Baire.evenPart_interleave,
        Baire.oddPart_interleave]
      exact hq t
    · exact Representation.sequence_names_iff.mpr fun n => by rw [track_pack]; exact hy n

/-- The bundled strong lifting, fields explicit and fully computable: `mapTracks` on both
codes. -/
def StrongWeihrauchReduction.parallelize {f : Problem X Y} {g : Problem X' Y'}
    (r : StrongWeihrauchReduction f g) :
    StrongWeihrauchReduction f.parallelize g.parallelize :=
  ⟨r.pre.mapTracks, r.post.mapTracks, r.spec.parallelize⟩

@[simp] theorem StrongWeihrauchReduction.parallelize_pre {f : Problem X Y}
    {g : Problem X' Y'} (r : StrongWeihrauchReduction f g) :
    r.parallelize.pre = r.pre.mapTracks := rfl

@[simp] theorem StrongWeihrauchReduction.parallelize_post {f : Problem X Y}
    {g : Problem X' Y'} (r : StrongWeihrauchReduction f g) :
    r.parallelize.post = r.post.mapTracks := rfl

/-- The bundled ordinary lifting, fields explicit and fully computable: the postprocessor
re-pairs trackwise before running `H` trackwise. -/
def WeihrauchReduction.parallelize {f : Problem X Y} {g : Problem X' Y'}
    (r : WeihrauchReduction f g) : WeihrauchReduction f.parallelize g.parallelize :=
  ⟨r.pre.mapTracks, r.post.mapTracks.subst .zipTracksCode, r.spec.parallelize⟩

@[simp] theorem WeihrauchReduction.parallelize_pre {f : Problem X Y} {g : Problem X' Y'}
    (r : WeihrauchReduction f g) : r.parallelize.pre = r.pre.mapTracks := rfl

@[simp] theorem WeihrauchReduction.parallelize_post {f : Problem X Y} {g : Problem X' Y'}
    (r : WeihrauchReduction f g) :
    r.parallelize.post = r.post.mapTracks.subst .zipTracksCode := rfl

/-- Strong reducibility is monotone under parallelization. -/
theorem StrongWeihrauchReducible.parallelize {f : Problem X Y} {g : Problem X' Y'}
    (h : f ≤sW g) : f.parallelize ≤sW g.parallelize := by
  obtain ⟨K, H, hp⟩ := strongReduction_iff_exists_reductionPair.mp h
  exact strongReduction_iff_exists_reductionPair.mpr ⟨_, _, hp.parallelize⟩

/-- Ordinary reducibility is monotone under parallelization. -/
theorem WeihrauchReducible.parallelize {f : Problem X Y} {g : Problem X' Y'}
    (h : f ≤W g) : f.parallelize ≤W g.parallelize := by
  obtain ⟨K, H, hp⟩ := reduction_iff_exists_reductionPair.mp h
  exact reduction_iff_exists_reductionPair.mpr ⟨_, _, hp.parallelize⟩

/-- Parallelization respects ordinary Weihrauch equivalence. -/
theorem parallelize_congr {f : Problem X Y} {g : Problem X' Y'} (h : f ≡W g) :
    f.parallelize ≡W g.parallelize :=
  ⟨h.1.parallelize, h.2.parallelize⟩

/-! ### Extensivity and idempotence -/

/-- **Extensivity, as an explicit pair**: name the constant family, answer with track
`0`. -/
theorem isStrongReductionPair_parallelize_extensive (f : Problem X Y) :
    IsStrongReductionPair f f.parallelize .repeatTracksCode (.extractTrackCode 0) := by
  intro p x hpx hdom
  obtain ⟨y₀, hy₀⟩ := hdom
  refine ⟨fun m => p m.unpair.2, ?_, fun _ => x, ?_, ⟨fun _ => y₀, fun _ => hy₀⟩, ?_⟩
  · rw [OracleCode.evalStream_repeatTracksCode]
    exact Part.mem_some _
  · exact Representation.sequence_names_iff.mpr fun n => by
      rw [OracleCode.track_repeatTracks]; exact hpx
  · intro a ys hays hacc
    refine ⟨Baire.track 0 a, ?_, ys 0, Representation.sequence_names_iff.mp hays 0, hacc 0⟩
    rw [OracleCode.evalStream_extractTrackCode]
    exact Part.mem_some _

/-- **Extensivity**: a single instance reduces strongly to the parallelization. -/
theorem parallelize_extensive (f : Problem X Y) : f ≤sW f.parallelize :=
  strongReduction_iff_exists_reductionPair.mpr
    ⟨_, _, isStrongReductionPair_parallelize_extensive f⟩

/-- **Idempotence, forward pair**: a doubly parallelized instance reduces strongly to a
single parallelization by flattening the input along `Nat.pair` and unflattening the
answer. -/
theorem isStrongReductionPair_parallelize_flatten (f : Problem X Y) :
    IsStrongReductionPair f.parallelize.parallelize f.parallelize
      .flattenTracksCode .unflattenTracksCode := by
  intro F xss hF hdom
  have hFn := Representation.sequence_names_iff.mp hF
  rw [Problem.parallelize_dom_iff] at hdom
  refine ⟨fun m => F (Nat.pair m.unpair.1.unpair.1 (Nat.pair m.unpair.1.unpair.2
      m.unpair.2)), ?_, fun m => xss m.unpair.1 m.unpair.2, ?_, ?_, ?_⟩
  · rw [OracleCode.evalStream_flattenTracksCode]
    exact Part.mem_some _
  · refine Representation.sequence_names_iff.mpr fun m => ?_
    rw [OracleCode.track_flattenTracks]
    exact Representation.sequence_names_iff.mp (hFn m.unpair.1) m.unpair.2
  · rw [Problem.parallelize_dom_iff]
    intro m
    exact Problem.parallelize_dom_iff.mp (hdom m.unpair.1) m.unpair.2
  · intro a ys hays hacc
    have han := Representation.sequence_names_iff.mp hays
    refine ⟨fun m => a (Nat.pair (Nat.pair m.unpair.1 m.unpair.2.unpair.1)
        m.unpair.2.unpair.2), ?_, fun s t => ys (Nat.pair s t), ?_, ?_⟩
    · rw [OracleCode.evalStream_unflattenTracksCode]
      exact Part.mem_some _
    · refine Representation.sequence_names_iff.mpr fun s => ?_
      refine Representation.sequence_names_iff.mpr fun t => ?_
      rw [OracleCode.track_unflattenTracks]
      exact han (Nat.pair s t)
    · intro s t
      simpa [Nat.unpair_pair] using hacc (Nat.pair s t)

/-- **Idempotence, reverse pair**: a single parallelization reduces strongly to the
doubly parallelized one by unflattening the input and flattening the answer. -/
theorem isStrongReductionPair_parallelize_unflatten (f : Problem X Y) :
    IsStrongReductionPair f.parallelize f.parallelize.parallelize
      .unflattenTracksCode .flattenTracksCode := by
  intro F xs hF hdom
  have hFn := Representation.sequence_names_iff.mp hF
  rw [Problem.parallelize_dom_iff] at hdom
  refine ⟨fun m => F (Nat.pair (Nat.pair m.unpair.1 m.unpair.2.unpair.1)
      m.unpair.2.unpair.2), ?_, fun s t => xs (Nat.pair s t), ?_, ?_, ?_⟩
  · rw [OracleCode.evalStream_unflattenTracksCode]
    exact Part.mem_some _
  · refine Representation.sequence_names_iff.mpr fun s => ?_
    refine Representation.sequence_names_iff.mpr fun t => ?_
    rw [OracleCode.track_unflattenTracks]
    exact hFn (Nat.pair s t)
  · rw [Problem.parallelize_dom_iff]
    intro s
    rw [Problem.parallelize_dom_iff]
    intro t
    exact hdom (Nat.pair s t)
  · intro a yss hays hacc
    have han := Representation.sequence_names_iff.mp hays
    refine ⟨fun m => a (Nat.pair m.unpair.1.unpair.1 (Nat.pair m.unpair.1.unpair.2
        m.unpair.2)), ?_, fun m => yss m.unpair.1 m.unpair.2, ?_, ?_⟩
    · rw [OracleCode.evalStream_flattenTracksCode]
      exact Part.mem_some _
    · refine Representation.sequence_names_iff.mpr fun m => ?_
      rw [OracleCode.track_flattenTracks]
      exact Representation.sequence_names_iff.mp (han m.unpair.1) m.unpair.2
    · intro m
      simpa [Nat.pair_unpair] using hacc m.unpair.1 m.unpair.2

/-- **Idempotence**: parallelizing twice is strongly equivalent to parallelizing once. -/
theorem parallelize_idempotent (f : Problem X Y) :
    f.parallelize.parallelize ≡sW f.parallelize :=
  ⟨strongReduction_iff_exists_reductionPair.mpr
      ⟨_, _, isStrongReductionPair_parallelize_flatten f⟩,
   strongReduction_iff_exists_reductionPair.mpr
      ⟨_, _, isStrongReductionPair_parallelize_unflatten f⟩⟩

end ComputableAnalysis
