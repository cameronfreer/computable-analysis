/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.ForMathlib.PrimrecContainers
import ComputableAnalysis.TypeTwo.Evaln
import ComputableAnalysis.TypeTwo.Cantor

/-!
# Effective compactness: the uniform prefix table

For a code total on Cantor space, the realized map `streamFn c hc : Cantor → Cantor`
decodes outputs with the pinned Cantor decoder (`0 ↦ false`, positive `↦ true`). The
predicate `TotalOnCantor` asserts **coordinatewise convergence only** — it does not force
binary-valued output; the decoder absorbs arbitrary natural outputs, and this is the same
decoder the prefix-table search uses.

`uniformPrefixTableSearch c s` is one canonical partial search: by dovetailing the bounded
simulation `evalnPrefix` over the finitely many length-`k` binary prefixes, it finds a
uniform prefix length `m` and the list `T` of length-`m` prefixes whose cylinders map into
the target cylinder `s`. Under `TotalOnCantor` it terminates (compactness of Cantor space),
and the returned `(m, T)` satisfies the four table properties: `Nodup`, uniform length,
pairwise-disjoint cylinders, and the preimage-union law.

Continuity of `streamFn` as a `Cantor → Cantor` map — the bridge later measurability
arguments need — is deferred to the represented-space realizer layer (Unit 8), where the
decoded map is presented through `evalStream` on valid names.
-/

namespace ComputableAnalysis

namespace OracleCode

/-- A code is **total on Cantor** when it converges at every coordinate on every Cantor
name (coordinatewise convergence only — *not* binary-valued output; the decoder handles
arbitrary natural outputs). -/
def TotalOnCantor (c : OracleCode) : Prop :=
  ∀ (x : Cantor) (n : ℕ), (c.eval (encodeCantor x) n).Dom

/-- The Cantor point a total code decodes on input `x`, applying the neutral stream-level
decoder `natStreamToBool` (`0 ↦ false`, positive `↦ true`) to the evaluation output.

Three semantic points: (i) `TotalOnCantor` asserts coordinatewise *convergence only*;
(ii) arbitrary natural outputs are decoded by the zero/positive test, so no binary-valued
output is assumed; (iii) this is therefore **not** automatically a realizer for `cantorRep`,
whose valid output names must already take values in `{0, 1}`. That realizer bridge belongs
to the represented-space layer, not here. -/
def streamFn (c : OracleCode) (hc : TotalOnCantor c) (x : Cantor) : Cantor :=
  natStreamToBool fun n => (c.eval (encodeCantor x) n).get (hc x n)

/-- Evaluator equation: the realized coordinate is the decoded evaluation output. -/
theorem streamFn_apply {c : OracleCode} (hc : TotalOnCantor c) (x : Cantor) {n y : ℕ}
    (hy : y ∈ c.eval (encodeCantor x) n) : streamFn c hc x n = decide (0 < y) := by
  have hget : (c.eval (encodeCantor x) n).get (hc x n) = y := Part.get_eq_of_mem hy _
  simp only [streamFn, natStreamToBool_apply, hget]

/-! ### Enumeration of binary words -/

/-- All binary words of a given length, enumerated without repeats. -/
def binaryWords : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 => (binaryWords k).flatMap fun w => [false :: w, true :: w]

theorem length_of_mem_binaryWords {k : ℕ} {w : List Bool} (h : w ∈ binaryWords k) :
    w.length = k := by
  induction k generalizing w with
  | zero => simp only [binaryWords, List.mem_singleton] at h; subst h; rfl
  | succ k ih =>
    simp only [binaryWords, List.mem_flatMap] at h
    obtain ⟨v, hv, hw⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> simp [ih hv]

theorem binaryWords_nodup : ∀ k : ℕ, (binaryWords k).Nodup
  | 0 => by simp [binaryWords]
  | k + 1 => by
    rw [binaryWords, List.nodup_flatMap]
    refine ⟨fun w _ => by simp, (binaryWords_nodup k).imp fun {w1 w2} hne => ?_⟩
    simp only [Function.onFun, List.disjoint_left, List.mem_cons, List.not_mem_nil, or_false]
    rintro a (rfl | rfl) <;> rintro (h | h) <;> exact hne (by injection h)

/-- Every length-`k` binary word is enumerated (completeness). -/
theorem mem_binaryWords {k : ℕ} {w : List Bool} : w ∈ binaryWords k ↔ w.length = k := by
  refine ⟨length_of_mem_binaryWords, fun h => ?_⟩
  induction k generalizing w with
  | zero => rw [List.length_eq_zero_iff] at h; subst h; simp [binaryWords]
  | succ k ih =>
    obtain ⟨b, w, rfl⟩ : ∃ b w', w = b :: w' := by
      cases w with
      | nil => simp at h
      | cons b w' => exact ⟨b, w', rfl⟩
    simp only [binaryWords, List.mem_flatMap]
    exact ⟨w, ih (by simpa using h), by cases b <;> simp⟩

/-! ### Computability plumbing -/

/-- `Option.any` of a primitive-recursive predicate is primitive recursive. -/
private theorem primrec_option_any {α σ : Type} [Primcodable α] [Primcodable σ]
    {f : α → Option σ} {p : α → σ → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).any (p a) := by
  have h : ∀ a, (f a).any (p a) = ((f a).map (p a)).getD false := fun a => by cases f a <;> rfl
  refine (Primrec.option_getD.comp (Primrec.option_map hf hp) (Primrec.const false)).of_eq
    (fun a => (h a).symm)

/-- The inner coordinate check (decode-and-compare against a target bit), at a shallow
argument packing so its instance resolution stays cheap when composed. -/
private theorem primrec_matchAt : Primrec (fun a : (List Bool × ℕ) × Option ℕ =>
    a.2.any (fun v => decide (0 < v) == a.1.1.getD a.1.2 false)) := by
  refine primrec_option_any Primrec.snd ?_
  have hlhs : Primrec (fun u : ((List Bool × ℕ) × Option ℕ) × ℕ => decide (0 < u.2)) :=
    Primrec.nat_lt.decide.comp (Primrec.const 0) Primrec.snd
  have hrhs : Primrec (fun u : ((List Bool × ℕ) × Option ℕ) × ℕ => u.1.1.1.getD u.1.1.2 false) :=
    (Primrec.list_getD false).comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  exact (Primrec.dom_bool₂ (fun a b => a == b)).comp hlhs hrhs

/-- The binary-word enumeration is primitive recursive. -/
theorem primrec_binaryWords : Primrec binaryWords := by
  have key : ∀ k, binaryWords k
      = Nat.rec [[]] (fun _ prev => prev.flatMap (fun w => [false :: w, true :: w])) k := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => rw [binaryWords, ih]
  refine (Primrec.nat_rec₁ [[]] ?_).of_eq (fun k => (key k).symm)
  refine Primrec.list_flatMap Primrec.snd ?_
  exact Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const false) Primrec.snd)
    (Primrec.list_cons.comp (Primrec.list_cons.comp (Primrec.const true) Primrec.snd)
      (Primrec.const []))

/-! ### Finite success/match predicates -/

section Search

variable (c : OracleCode) (s : List Bool)

/-- At fuel `k`, the length-`k` word `t` **determines** all `s.length` output
coordinates: the bounded simulation converges at each `i < s.length`. -/
def determined (k : ℕ) (t : List Bool) : Bool :=
  (List.range s.length).all fun i => (evalnPrefix k c (boolWordToNat t) i).isSome

/-- At fuel `k`, the output of `t` **matches** `s`: every coordinate `i < s.length`
converges and decodes (via `decide (0 < ·)`) to `s`'s `i`-th bit. -/
def outMatches (k : ℕ) (t : List Bool) : Bool :=
  (List.range s.length).all fun i =>
    (evalnPrefix k c (boolWordToNat t) i).any fun v => decide (0 < v) == s.getD i false

/-- A match determines the output. -/
theorem determined_of_outMatches {k : ℕ} {t : List Bool} (h : outMatches c s k t) :
    determined c s k t := by
  simp only [outMatches, List.all_eq_true, List.mem_range] at h
  simp only [determined, List.all_eq_true, List.mem_range]
  intro i hi
  rcases hv : evalnPrefix k c (boolWordToNat t) i with _ | v
  · simpa [hv] using h i hi
  · simp

/-- At fuel `k`, *every* length-`k` word determines all `s.length` output coordinates. -/
def allDetermined (k : ℕ) : Bool := (binaryWords k).all (determined c s k)

/-- The canonical uniform-prefix-table search: find the least fuel `m` at which every
length-`m` word determines the first `s.length` output coordinates, then return that `m`
together with the length-`m` words whose output matches `s`. -/
def uniformPrefixTableSearch : Part (ℕ × List (List Bool)) :=
  (Nat.rfind fun k => ↑(allDetermined c s k)).map fun k =>
    (k, (binaryWords k).filter (outMatches c s k))

/-- Result equation for the search. -/
theorem mem_uniformPrefixTableSearch {p : ℕ × List (List Bool)} :
    p ∈ uniformPrefixTableSearch c s ↔
      allDetermined c s p.1 = true ∧ (∀ k, k < p.1 → allDetermined c s k = false) ∧
        p.2 = (binaryWords p.1).filter (outMatches c s p.1) := by
  simp only [uniformPrefixTableSearch, Part.mem_map_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rw [Nat.mem_rfind] at hk
    exact ⟨by simpa using hk.1, fun j hj => by simpa using hk.2 hj, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨p.1, ?_, Prod.ext rfl h3.symm⟩
    rw [Nat.mem_rfind]
    exact ⟨by simpa using h1, fun hj => by simpa using h2 _ hj⟩

/-! ### Compactness: the search terminates on total codes -/

/-- The nat-word oracle prefix from `x`'s length-`k` binary prefix equals the length-`k`
prefix of the encoded stream. -/
private theorem boolWordToNat_streamTake (x : Cantor) (k : ℕ) :
    boolWordToNat (streamTake x k) = streamTake (encodeCantor x) k := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [getElem_boolWordToNat, getElem_streamTake, encodeCantor_apply]
  cases x i <;> rfl

/-- Fuel `k` determines the first `s.length` outputs of `x` from its length-`k` prefix.
Private termination machinery for `uniformPrefixTableSearch_dom`. -/
private def Good (k : ℕ) (x : Cantor) : Prop := determined c s k (streamTake x k) = true

private theorem good_mono {k k' : ℕ} (hk : k ≤ k') {x : Cantor} (h : Good c s k x) :
    Good c s k' x := by
  simp only [Good, determined, List.all_eq_true, List.mem_range, boolWordToNat_streamTake] at h ⊢
  intro i hi
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (h i hi)
  exact Option.isSome_iff_exists.mpr
    ⟨v, evalnPrefix_mono hk (streamTake_prefix (encodeCantor x) hk) hv⟩

private theorem isOpen_good (k : ℕ) : IsOpen {x : Cantor | Good c s k x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  refine Filter.mem_of_superset ((isClopen_cylinder (streamTake x k)).isOpen.mem_nhds
    (mem_cylinder_streamTake x k)) fun y hy => ?_
  have hst : streamTake y k = streamTake x k := by
    have := mem_cylinder_iff.mp hy; rwa [length_streamTake] at this
  simp only [Set.mem_setOf_eq, Good, hst]; exact hx

/-- Every Cantor point is eventually good (finite use of its `s.length` output coords). -/
private theorem good_cover (hc : TotalOnCantor c) (x : Cantor) : ∃ k, Good c s k x := by
  have hi : ∀ i, ∃ k, (evalnPrefix k c (streamTake (encodeCantor x) k) i).isSome := fun i => by
    obtain ⟨k, hk⟩ := evalnPrefix_complete.mp (Part.get_mem (hc x i))
    exact ⟨k, Option.isSome_iff_exists.mpr ⟨_, hk⟩⟩
  choose K hK using hi
  refine ⟨(Finset.range s.length).sup K, ?_⟩
  simp only [Good, determined, List.all_eq_true, List.mem_range, boolWordToNat_streamTake]
  intro i hi'
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hK i)
  have hle : K i ≤ (Finset.range s.length).sup K := Finset.le_sup (Finset.mem_range.mpr hi')
  exact Option.isSome_iff_exists.mpr
    ⟨v, evalnPrefix_mono hle (streamTake_prefix (encodeCantor x) hle) hv⟩

/-- Compactness: a single fuel `K` is good for every Cantor point. -/
private theorem exists_uniform_good (hc : TotalOnCantor c) : ∃ K, ∀ x : Cantor, Good c s K x := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun k => {x : Cantor | Good c s k x})
    (fun k => isOpen_good c s k)
    (fun x _ => by simp only [Set.mem_iUnion, Set.mem_setOf_eq]; exact good_cover c s hc x)
  refine ⟨t.sup id, fun x => ?_⟩
  obtain ⟨k, hkt, hgk⟩ := by
    simpa only [Set.mem_iUnion, Set.mem_setOf_eq] using ht (Set.mem_univ x)
  exact good_mono c s (Finset.le_sup (f := id) hkt) hgk

/-- **Termination.** On a code total on Cantor, the prefix-table search converges. -/
theorem uniformPrefixTableSearch_dom (hc : TotalOnCantor c) :
    (uniformPrefixTableSearch c s).Dom := by
  obtain ⟨K, hK⟩ := exists_uniform_good c s hc
  have hall : allDetermined c s K = true := by
    simp only [allDetermined, List.all_eq_true]
    intro t ht
    have hlen : t.length = K := length_of_mem_binaryWords ht
    have hgood := hK (streamExtend t (fun _ => false))
    simp only [Good] at hgood
    rwa [show streamTake (streamExtend t (fun _ => false)) K = t from
      hlen ▸ streamTake_streamExtend t _] at hgood
  have hrfind : (Nat.rfind fun k => (↑(allDetermined c s k) : Part Bool)).Dom := by
    rw [Nat.rfind_dom]
    exact ⟨K, by simpa using hall, fun {m} _ => trivial⟩
  exact hrfind

/-! ### Table properties of the search result `(m, T)` -/

variable {m : ℕ} {T : List (List Bool)}

/-- The table is exactly the matching length-`m` words. -/
theorem uniformPrefixTableSearch_table_eq (h : (m, T) ∈ uniformPrefixTableSearch c s) :
    T = (binaryWords m).filter (outMatches c s m) := ((mem_uniformPrefixTableSearch c s).mp h).2.2

/-- (i) The table has no repeats. -/
theorem uniformPrefixTableSearch_nodup (h : (m, T) ∈ uniformPrefixTableSearch c s) : T.Nodup := by
  rw [uniformPrefixTableSearch_table_eq c s h]
  exact (binaryWords_nodup m).filter _

/-- (ii) Every table entry has length `m`. -/
theorem uniformPrefixTableSearch_length (h : (m, T) ∈ uniformPrefixTableSearch c s)
    {t : List Bool} (ht : t ∈ T) : t.length = m := by
  rw [uniformPrefixTableSearch_table_eq c s h] at ht
  exact length_of_mem_binaryWords (List.mem_of_mem_filter ht)

/-- (iii) Distinct table entries have disjoint cylinders. -/
theorem uniformPrefixTableSearch_disjoint (h : (m, T) ∈ uniformPrefixTableSearch c s)
    {t t' : List Bool} (ht : t ∈ T) (ht' : t' ∈ T) (hne : t ≠ t') :
    Disjoint (Cantor.cylinder t) (Cantor.cylinder t') := by
  have hl := uniformPrefixTableSearch_length c s h ht
  have hl' := uniformPrefixTableSearch_length c s h ht'
  rw [Set.disjoint_left]
  intro x hx hx'
  exact hne (by rw [← mem_cylinder_iff.mp hx, ← mem_cylinder_iff.mp hx', hl, hl'])

/-- (iv) The table cylinders are exactly the preimage of the target cylinder under the
realized map: `streamFn c hc ⁻¹' cylinder s = ⋃ t ∈ T, cylinder t`. -/
theorem uniformPrefixTableSearch_preimage (hc : TotalOnCantor c)
    (h : (m, T) ∈ uniformPrefixTableSearch c s) :
    streamFn c hc ⁻¹' Cantor.cylinder s = ⋃ t ∈ T, Cantor.cylinder t := by
  have hdet : allDetermined c s m = true := ((mem_uniformPrefixTableSearch c s).mp h).1
  have hT := uniformPrefixTableSearch_table_eq c s h
  ext x
  have hmemx : streamTake x m ∈ binaryWords m := mem_binaryWords.mpr (length_streamTake x m)
  have hdetx : ∀ i, i < s.length → (evalnPrefix m c (streamTake (encodeCantor x) m) i).isSome := by
    have hd := List.all_eq_true.mp hdet _ hmemx
    simpa only [determined, List.all_eq_true, List.mem_range, boolWordToNat_streamTake] using hd
  have hcoord : ∀ i, i < s.length →
      ((evalnPrefix m c (streamTake (encodeCantor x) m) i).any
          (fun v => decide (0 < v) == s.getD i false) = true
        ↔ streamFn c hc x i = s.getD i false) := by
    intro i hi
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hdetx i hi)
    have hsf : streamFn c hc x i = decide (0 < v) :=
      streamFn_apply hc x (evalnPrefix_sound (mem_cylinder_streamTake (encodeCantor x) m) hv)
    rw [hv, Option.any_some, beq_iff_eq, ← hsf]
  have hgetD : ∀ (i : ℕ) (hi : i < s.length), s.getD i false = s[i] := fun i hi => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  have hpivot : (streamFn c hc x ∈ Cantor.cylinder s)
      ↔ outMatches c s m (streamTake x m) = true := by
    rw [outMatches, boolWordToNat_streamTake, List.all_eq_true]
    simp only [List.mem_range, Cantor.cylinder, cylinder, Set.mem_setOf_eq]
    refine ⟨fun hcyl i hi => (hcoord i hi).mpr (by rw [hgetD i hi]; exact hcyl i hi),
      fun hall i hi => ?_⟩
    rw [← hgetD i hi]
    exact (hcoord i hi).mp (hall i hi)
  have hunion : (x ∈ ⋃ t ∈ T, Cantor.cylinder t) ↔ streamTake x m ∈ T := by
    simp only [Set.mem_iUnion, exists_prop]
    refine ⟨fun ⟨t, htT, hxt⟩ => ?_, fun ht => ⟨streamTake x m, ht, mem_cylinder_streamTake x m⟩⟩
    have hlt := uniformPrefixTableSearch_length c s h htT
    rw [Cantor.cylinder, mem_cylinder_iff, hlt] at hxt
    rwa [hxt]
  rw [Set.mem_preimage, hpivot, hunion, hT, List.mem_filter]
  simp [hmemx]

end Search

/-! ### Partial recursiveness of the search -/

set_option maxHeartbeats 1000000 in
-- the deeply nested packed products make Primrec instance resolution exceed the default
private theorem primrec_determined :
    Primrec₂ (fun (x : (OracleCode × List Bool) × ℕ) (t : List Bool) =>
      determined x.1.1 x.1.2 x.2 t) := by
  unfold determined
  refine primrec_list_all (Primrec.list_range.comp (Primrec.list_length.comp
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))) ?_
  have hk : Primrec (fun w : (((OracleCode × List Bool) × ℕ) × List Bool) × ℕ => w.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hc : Primrec (fun w : (((OracleCode × List Bool) × ℕ) × List Bool) × ℕ => w.1.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have ht : Primrec (fun w : (((OracleCode × List Bool) × ℕ) × List Bool) × ℕ =>
      boolWordToNat w.1.2) := primrec_boolWordToNat.comp (Primrec.snd.comp Primrec.fst)
  exact Primrec.option_isSome.comp
    (primrec_evalnPrefix.comp ((hk.pair hc).pair (ht.pair Primrec.snd)))

set_option maxHeartbeats 1000000 in
-- the deeply nested packed products make Primrec instance resolution exceed the default
private theorem primrec_outMatches :
    Primrec₂ (fun (x : (OracleCode × List Bool) × ℕ) (t : List Bool) =>
      outMatches x.1.1 x.1.2 x.2 t) := by
  unfold outMatches
  refine primrec_list_all (Primrec.list_range.comp (Primrec.list_length.comp
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))) ?_
  have hs : Primrec (fun w : (((OracleCode × List Bool) × ℕ) × List Bool) × ℕ => w.1.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hk : Primrec (fun w : (((OracleCode × List Bool) × ℕ) × List Bool) × ℕ => w.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hc : Primrec (fun w : (((OracleCode × List Bool) × ℕ) × List Bool) × ℕ => w.1.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have ht : Primrec (fun w : (((OracleCode × List Bool) × ℕ) × List Bool) × ℕ =>
      boolWordToNat w.1.2) := primrec_boolWordToNat.comp (Primrec.snd.comp Primrec.fst)
  have hEval : Primrec (fun w : (((OracleCode × List Bool) × ℕ) × List Bool) × ℕ =>
      evalnPrefix w.1.1.2 w.1.1.1.1 (boolWordToNat w.1.2) w.2) :=
    primrec_evalnPrefix.comp ((hk.pair hc).pair (ht.pair Primrec.snd))
  exact primrec_matchAt.comp ((hs.pair Primrec.snd).pair hEval)

private theorem primrec_allDetermined :
    Primrec (fun x : (OracleCode × List Bool) × ℕ => allDetermined x.1.1 x.1.2 x.2) := by
  unfold allDetermined
  exact primrec_list_all (primrec_binaryWords.comp Primrec.snd) primrec_determined

/-- **The prefix-table search is partial recursive.** -/
theorem uniformPrefixTableSearch_partrec : Partrec₂ uniformPrefixTableSearch := by
  have hp : Partrec₂ (fun (cs : OracleCode × List Bool) (k : ℕ) =>
      (allDetermined cs.1 cs.2 k : Part Bool)) := primrec_allDetermined.to_comp
  have hFilter : Computable (fun x : (OracleCode × List Bool) × ℕ =>
      (x.2, (binaryWords x.2).filter (outMatches x.1.1 x.1.2 x.2))) :=
    (Primrec.pair Primrec.snd
      (primrec_list_filter (primrec_binaryWords.comp Primrec.snd) primrec_outMatches)).to_comp
  exact (Partrec.rfind hp).map hFilter

end OracleCode

end ComputableAnalysis
