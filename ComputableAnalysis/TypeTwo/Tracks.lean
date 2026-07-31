/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.TypeTwo.OracleCodeArith

/-!
# Track packing and the generic trackwise map

The countable-product layer's frozen packing convention: a single Baire stream encodes a
countable family of streams, with `Baire.track t p = fun k => p (Nat.pair t k)` the `t`-th
member. This file provides the code-level kit for that convention, **fully explicit and
axiom-free**: every code here is a closed first-order term built from the `OracleCode`
constructors, and every specification is proved by structural induction — no
`Classical.choose`, no `Nat.Partrec.Code.exists_code`.

* `OracleCode.mapTracks`: the generic trackwise map. `mapTracks c` runs `c` independently
  on every track of the packed input. The transformation is a structural recursion: under
  the pairing convention the `query` constructor maps to *itself* (the transformed code's
  arguments carry the track tag paired on the left, so a query at a tagged coordinate is
  already a query into the right track); only `prec` and `rfind'` need the reassociation
  codes `assocArg`/`assocIn`. `eval_mapTracks_pair` is the coordinate-level contract and
  `evalStream_mapTracks_iff` the stream-level one — an *iff*, since `Nat.pair` is
  surjective.
* Reshuffling codes for the parallelization layer's consumers: `repeatTracksCode`
  (constant family), `extractTrackCode` (one track), `zipTracksCode`/`unzipTracksCode`
  (between a pair of packed families and a packed family of pairs, mediating between the
  `Nat.pair` packing and the even/odd product interleaving), and `flattenTracksCode`/
  `unflattenTracksCode` (between doubly and singly packed families).

The explicit arithmetic these codes ride on (`addCode`, `subCode`, `div2mod2Code`, …)
lives in `TypeTwo/OracleCodeArith.lean`.
-/

namespace ComputableAnalysis

/-- Track `t` of a packed stream: the section along `Nat.pair t ·`. The frozen packing
convention for countable families of names. -/
def Baire.track (t : ℕ) (p : Baire) : Baire := fun k => p (Nat.pair t k)

@[simp]
theorem Baire.track_apply (t : ℕ) (p : Baire) (k : ℕ) :
    Baire.track t p k = p (Nat.pair t k) := rfl

/-- Pack a family of streams into one stream along the track convention: the `t`-th
member is laid out on track `t`. Inverse to `Baire.track` (`Baire.track_packTracks`). -/
def Baire.packTracks (g : ℕ → Baire) : Baire := fun m => g m.unpair.1 m.unpair.2

/-- Packing is a section of tracking: track `t` of a packed family is its `t`-th
member. -/
@[simp]
theorem Baire.track_packTracks (g : ℕ → Baire) (t : ℕ) :
    Baire.track t (Baire.packTracks g) = g t :=
  funext fun k => by simp [Baire.packTracks, Nat.unpair_pair]

namespace OracleCode

/-! ### Reassociation codes -/

/-- Reassociation `Nat.pair t (Nat.pair a n) ↦ Nat.pair (Nat.pair t a) n`: move the track
tag inward onto the recursion parameter. -/
def assocArg : OracleCode :=
  pair (pair left (comp left right)) (comp right right)

/-- Reassociation `Nat.pair (Nat.pair t a) v ↦ Nat.pair t (Nat.pair a v)`: move the track
tag back outward. -/
def assocIn : OracleCode :=
  pair (comp left left) (pair (comp right left) right)

theorem eval_assocArg (p : Baire) (m : ℕ) :
    assocArg.eval p m =
      Part.some (Nat.pair (Nat.pair m.unpair.1 m.unpair.2.unpair.1) m.unpair.2.unpair.2) := by
  simp [assocArg, Seq.seq]

theorem eval_assocIn (p : Baire) (m : ℕ) :
    assocIn.eval p m =
      Part.some (Nat.pair m.unpair.1.unpair.1 (Nat.pair m.unpair.1.unpair.2 m.unpair.2)) := by
  simp [assocIn, Seq.seq]

/-! ### The generic trackwise map -/

/-- **The generic trackwise map.** `mapTracks c` runs `c` independently on every track of
the packed input stream: output coordinate `Nat.pair t k` is coordinate `k` of the run of
`c` against input track `t`. A structural recursion: the transformed code's arguments carry
the track tag `t` paired on the left, so `query` maps to itself — a query at tagged
coordinate `Nat.pair t k` is exactly a query into track `t` — and only `prec`/`rfind'`
need the reassociation codes. -/
def mapTracks : OracleCode → OracleCode
  | zero => zero
  | succ => comp succ right
  | left => comp left right
  | right => comp right right
  | query => query
  | pair cf cg => pair (mapTracks cf) (mapTracks cg)
  | comp cf cg => comp (mapTracks cf) (pair left (mapTracks cg))
  | prec cf cg => comp (prec (mapTracks cf) (comp (mapTracks cg) assocIn)) assocArg
  | rfind' cf => comp (rfind' (comp (mapTracks cf) assocIn)) assocArg

/-- Pairing a total `left` tag onto an arbitrary evaluation, in `<$>` form. -/
private theorem eval_pair_left (c : OracleCode) (p : Baire) (t k : ℕ) :
    (pair left c).eval p (Nat.pair t k) = Nat.pair t <$> c.eval p (Nat.pair t k) := by
  simp [Seq.seq, Nat.unpair_pair]

/-- **The coordinate-level contract.** On a tagged input `Nat.pair t k`, the transformed
code computes exactly what `c` computes at `k` against track `t`. -/
theorem eval_mapTracks_pair (c : OracleCode) (p : Baire) (t : ℕ) :
    ∀ k, (mapTracks c).eval p (Nat.pair t k) = c.eval (Baire.track t p) k := by
  induction c with
  | zero => intro k; rfl
  | succ => intro k; simp [mapTracks]
  | left => intro k; simp [mapTracks]
  | right => intro k; simp [mapTracks]
  | query => intro k; simp [mapTracks, Baire.track]
  | pair cf cg ihf ihg => intro k; simp [mapTracks, ihf, ihg]
  | comp cf cg ihf ihg =>
      intro k
      simp only [mapTracks, eval_comp, eval_pair_left, ihg, Part.bind_eq_bind,
        Part.map_eq_map, Part.bind_map]
      exact congrArg (Part.bind _) (funext fun v => ihf v)
  | prec cf cg ihf ihg =>
      intro k
      obtain ⟨a, n, rfl⟩ : ∃ a n, k = Nat.pair a n :=
        ⟨k.unpair.1, k.unpair.2, (Nat.pair_unpair k).symm⟩
      simp only [mapTracks]
      rw [eval_comp_some (show assocArg.eval p (Nat.pair t (Nat.pair a n)) =
        Part.some (Nat.pair (Nat.pair t a) n) by simp [eval_assocArg, Nat.unpair_pair])]
      induction n with
      | zero => rw [eval_prec_zero, eval_prec_zero, ihf]
      | succ n ihn =>
          rw [eval_prec_succ, eval_prec_succ, ihn]
          refine congrArg (Part.bind _) (funext fun i => ?_)
          rw [eval_comp_some (show assocIn.eval p (Nat.pair (Nat.pair t a) (Nat.pair n i)) =
            Part.some (Nat.pair t (Nat.pair a (Nat.pair n i))) by
              simp [eval_assocIn, Nat.unpair_pair]), ihg]
  | rfind' cf ihf =>
      intro k
      obtain ⟨a, m, rfl⟩ : ∃ a m, k = Nat.pair a m :=
        ⟨k.unpair.1, k.unpair.2, (Nat.pair_unpair k).symm⟩
      simp only [mapTracks]
      rw [eval_comp_some (show assocArg.eval p (Nat.pair t (Nat.pair a m)) =
        Part.some (Nat.pair (Nat.pair t a) m) by simp [eval_assocArg, Nat.unpair_pair])]
      rw [eval_rfind', eval_rfind']
      refine congrArg (Part.map (· + m)) (congrArg Nat.rfind (funext fun n => ?_))
      rw [eval_comp_some (show assocIn.eval p (Nat.pair (Nat.pair t a) (n + m)) =
        Part.some (Nat.pair t (Nat.pair a (n + m))) by
          simp [eval_assocIn, Nat.unpair_pair]), ihf]

/-- **The stream-level contract**, as an iff: `q` is a stream value of `mapTracks c` on `p`
exactly when, for every `t`, track `t` of `q` is a stream value of `c` on track `t` of `p`.
The reverse direction is what makes sequence-name validity and parallelization congruence
painless; do not weaken it to an implication. -/
theorem evalStream_mapTracks_iff {c : OracleCode} {p q : Baire} :
    q ∈ (mapTracks c).evalStream p ↔
      ∀ t, Baire.track t q ∈ c.evalStream (Baire.track t p) := by
  simp only [mem_evalStream, Baire.track]
  constructor
  · intro h t k
    simpa [eval_mapTracks_pair] using h (Nat.pair t k)
  · intro h m
    rw [← Nat.pair_unpair m, eval_mapTracks_pair]
    exact h m.unpair.1 m.unpair.2

/-! ### Reshuffling codes

Total query rewirings: each is `comp query ix` for an explicit index code `ix`, so each has
a total `evalStream` law. Names follow the packed-family reading of the *output*. -/

/-- A total index rewiring: `comp query c` with `c` computing the (oracle-independent) index
map `g` produces, on any stream `p`, the total stream `fun m => p (g m)`. -/
theorem evalStream_query_comp {c : OracleCode} {g : ℕ → ℕ}
    (h : ∀ p m, c.eval p m = Part.some (g m)) (p : Baire) :
    (comp query c).evalStream p = Part.some (fun m => p (g m)) :=
  computes_iff_evalStream.mp
    (fun q n => by rw [eval_comp_some (h q n), eval_query]) p

/-- The constant family: every track of the output is the input stream. -/
def repeatTracksCode : OracleCode := comp query right

theorem evalStream_repeatTracksCode (p : Baire) :
    repeatTracksCode.evalStream p = Part.some (fun m => p m.unpair.2) :=
  evalStream_query_comp (fun q m => eval_right q m) p

@[simp]
theorem track_repeatTracks (t : ℕ) (p : Baire) :
    Baire.track t (fun m => p m.unpair.2) = p :=
  funext fun k => by simp [Nat.unpair_pair]

/-- One track of a packed family. -/
def extractTrackCode (n : ℕ) : OracleCode := comp query (pair (.const n) .id)

theorem evalStream_extractTrackCode (n : ℕ) (p : Baire) :
    (extractTrackCode n).evalStream p = Part.some (Baire.track n p) :=
  evalStream_query_comp (fun q m => by simp [Seq.seq]) p

/-- The index map of `zipTracksCode`: mediate from the product interleaving (outer) to the
per-track interleaving (inner). -/
def zipIndexCode : OracleCode :=
  comp addCode (pair (comp doubleCode (pair left (comp left (comp div2mod2Code right))))
    (comp right (comp div2mod2Code right)))

theorem eval_zipIndexCode (p : Baire) (m : ℕ) :
    zipIndexCode.eval p m =
      Part.some (2 * Nat.pair m.unpair.1 (m.unpair.2 / 2) + m.unpair.2 % 2) := by
  simp only [zipIndexCode]
  have hd : (comp div2mod2Code right).eval p m =
      Part.some (Nat.pair (m.unpair.2 / 2) (m.unpair.2 % 2)) := by
    rw [eval_comp_some (eval_right p m), eval_div2mod2Code]
  rw [eval_comp_some (show (pair (comp doubleCode (pair left (comp left
      (comp div2mod2Code right)))) (comp right (comp div2mod2Code right))).eval p m =
      Part.some (Nat.pair (2 * Nat.pair m.unpair.1 (m.unpair.2 / 2)) (m.unpair.2 % 2)) from
    eval_pair_some
      (by rw [eval_comp_some (eval_pair_some (eval_left p m)
          (by rw [eval_comp_some hd, eval_left, Nat.unpair_pair])), eval_doubleCode])
      (by rw [eval_comp_some hd, eval_right, Nat.unpair_pair])), eval_addCode]

/-- From a product of packed families (even/odd interleaving of two `Nat.pair`-packed
streams) to the packed family of products: track `n` of the output is the interleaving of
track `n` of the even part with track `n` of the odd part. -/
def zipTracksCode : OracleCode := comp query zipIndexCode

theorem evalStream_zipTracksCode (r : Baire) :
    zipTracksCode.evalStream r =
      Part.some (fun m => r (2 * Nat.pair m.unpair.1 (m.unpair.2 / 2) + m.unpair.2 % 2)) :=
  evalStream_query_comp eval_zipIndexCode r

/-- Track `n` of the `zipTracksCode` output interleaves the tracks of the two halves. -/
theorem track_zipTracks (n : ℕ) (r : Baire) :
    Baire.track n (fun m => r (2 * Nat.pair m.unpair.1 (m.unpair.2 / 2) + m.unpair.2 % 2)) =
      Baire.interleave (Baire.track n r.evenPart) (Baire.track n r.oddPart) := by
  funext k
  simp only [Baire.track_apply, Nat.unpair_pair, Baire.interleave, Baire.evenPart_apply,
    Baire.oddPart_apply]
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h]

/-- The index map of `unzipTracksCode`, inverse rewiring to `zipIndexCode`. -/
def unzipIndexCode : OracleCode :=
  pair (comp left (comp left div2mod2Code))
    (comp addCode (pair (comp doubleCode (comp right (comp left div2mod2Code)))
      (comp right div2mod2Code)))

theorem eval_unzipIndexCode (p : Baire) (j : ℕ) :
    unzipIndexCode.eval p j =
      Part.some (Nat.pair (j / 2).unpair.1 (2 * (j / 2).unpair.2 + j % 2)) := by
  simp only [unzipIndexCode]
  have hd : div2mod2Code.eval p j = Part.some (Nat.pair (j / 2) (j % 2)) :=
    eval_div2mod2Code p j
  have hleft : (comp left div2mod2Code).eval p j = Part.some (j / 2) := by
    rw [eval_comp_some hd, eval_left, Nat.unpair_pair]
  exact eval_pair_some
    (by rw [eval_comp_some hleft, eval_left])
    (by rw [eval_comp_some (eval_pair_some
        (by rw [eval_comp_some (by rw [eval_comp_some hleft, eval_right]), eval_doubleCode])
        (by rw [eval_comp_some hd, eval_right, Nat.unpair_pair])), eval_addCode])

/-- From a packed family of products to the product of packed families: the inverse
rewiring of `zipTracksCode`. -/
def unzipTracksCode : OracleCode := comp query unzipIndexCode

theorem evalStream_unzipTracksCode (r : Baire) :
    unzipTracksCode.evalStream r =
      Part.some (fun j => r (Nat.pair (j / 2).unpair.1 (2 * (j / 2).unpair.2 + j % 2))) :=
  evalStream_query_comp eval_unzipIndexCode r

/-- The even part of the `unzipTracksCode` output packs the even parts of the tracks. -/
theorem track_evenPart_unzipTracks (n : ℕ) (r : Baire) :
    Baire.track n
        (Baire.evenPart fun j => r (Nat.pair (j / 2).unpair.1 (2 * (j / 2).unpair.2 + j % 2)))
      = Baire.evenPart (Baire.track n r) := by
  funext k
  have h1 : 2 * Nat.pair n k / 2 = Nat.pair n k := by omega
  have h2 : 2 * Nat.pair n k % 2 = 0 := by omega
  simp [h1, h2, Nat.unpair_pair]

/-- The odd part of the `unzipTracksCode` output packs the odd parts of the tracks. -/
theorem track_oddPart_unzipTracks (n : ℕ) (r : Baire) :
    Baire.track n
        (Baire.oddPart fun j => r (Nat.pair (j / 2).unpair.1 (2 * (j / 2).unpair.2 + j % 2)))
      = Baire.oddPart (Baire.track n r) := by
  funext k
  have h1 : (2 * Nat.pair n k + 1) / 2 = Nat.pair n k := by omega
  have h2 : (2 * Nat.pair n k + 1) % 2 = 1 := by omega
  simp [h1, h2, Nat.unpair_pair]

/-- From a doubly packed family to the singly packed one along `Nat.pair`: track
`Nat.pair s t` of the output is track `t` of track `s` of the input. -/
def flattenTracksCode : OracleCode := comp query assocIn

theorem evalStream_flattenTracksCode (p : Baire) :
    flattenTracksCode.evalStream p =
      Part.some (fun m => p (Nat.pair m.unpair.1.unpair.1
        (Nat.pair m.unpair.1.unpair.2 m.unpair.2))) :=
  evalStream_query_comp (fun q m => by
    rw [eval_assocIn]) p

/-- Track `m` of the `flattenTracksCode` output is the nested track of the input. -/
theorem track_flattenTracks (m : ℕ) (p : Baire) :
    Baire.track m (fun w => p (Nat.pair w.unpair.1.unpair.1
        (Nat.pair w.unpair.1.unpair.2 w.unpair.2))) =
      Baire.track m.unpair.2 (Baire.track m.unpair.1 p) :=
  funext fun k => by simp [Nat.unpair_pair]

/-- From a singly packed family to the doubly packed one: the inverse rewiring of
`flattenTracksCode`. -/
def unflattenTracksCode : OracleCode := comp query assocArg

theorem evalStream_unflattenTracksCode (p : Baire) :
    unflattenTracksCode.evalStream p =
      Part.some (fun m => p (Nat.pair (Nat.pair m.unpair.1 m.unpair.2.unpair.1)
        m.unpair.2.unpair.2)) :=
  evalStream_query_comp (fun q m => by rw [eval_assocArg]) p

/-- The nested track of the `unflattenTracksCode` output is track `Nat.pair s t` of the
input. -/
theorem track_unflattenTracks (s t : ℕ) (p : Baire) :
    Baire.track t (Baire.track s (fun m => p (Nat.pair (Nat.pair m.unpair.1
        m.unpair.2.unpair.1) m.unpair.2.unpair.2))) =
      Baire.track (Nat.pair s t) p :=
  funext fun k => by simp [Nat.unpair_pair]

end OracleCode

end ComputableAnalysis
