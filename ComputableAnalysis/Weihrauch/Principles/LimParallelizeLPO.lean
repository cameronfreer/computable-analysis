/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Weihrauch.Compilers
import ComputableAnalysis.Weihrauch.Principles.LimCylinder

/-!
# The calibration `parallelize LPO ≡sW Lim`

Parallelized `LPO` is strongly equivalent to `Lim`, making `Lim` the standard target for
countably many Σ₁ questions.

**`Lim ≤sW LPO.parallelize`** is by stability questions: one `LPO`
instance per triple `⟨n, s, v⟩` (packed `Nat.pair n (Nat.pair s v)`) asking whether
column `n` of the table ever differs from `v` at or after stage `s` (`stabFamily`,
produced by the explicit code `limStabCode`). An answer bit `0` certifies that the
column sits at `v` from `s` on; the limit *value* rides inside the question index, so
the strong postprocessor `limFromBitsCode` needs neither the original table nor a
canonical witness: it `rfind`-searches *any* `u` whose bit at `⟨n, u⟩` is `0` and emits
`u.unpair.2`. Correctness holds for **every** accepted `LPO` answer — no chosen answer,
no search minimality: any zero bit certifies stability outright, and convergence is
forced because a stabilizing column's true stability pair has an all-zero instance,
which pins its accepted bit to `0`. Both codes are explicit first-order terms with
empty `#print axioms`.

**Strong parallelizability of `Lim`** (`Lim.parallelize ≡sW Lim`): the collapse
direction flattens a packed family of tables into one table along `Nat.pair` — the
preprocessor is literally `flattenTracksCode` and the postprocessor is `query`, since
the limit stream of the flattened table *is* the packed family of limit streams.

**`LPO.parallelize ≤sW Lim`** is compositional, exactly the pattern the operations were
built for: `lpo_le_lim`, upgraded to strong through `Lim.isCylinder`, lifted by
the parallelization functor, and collapsed by strong parallelizability.

The explicit pair is derived through the `LPO.parallelize` compiler of
`Weihrauch/Compilers.lean`, whose hypotheses are exactly this module's semantic content
(question family, bit-consistent decoding); the module also hosts the composite entry
point `sigma1Family_le_lim` sending Σ₁ question families through the calibration to
`Lim`. The calibration is part of `Lim ≡sW LPÔ ≡sW lim_ℕ-hat ≡sW EC`
(Brattka–Gherardi–Pauly, Theorem 11.6.7).
-/

namespace ComputableAnalysis

open OracleCode

/-! ### The stability-question family and its explicit code -/

/-- The stability-question family of a table: coordinate `Nat.pair j k` with
`j = Nat.pair n (Nat.pair s v)` flags whether `p (Nat.pair n (s + k)) ≠ v`. Instance
`⟨n, s, v⟩` is therefore all-zero exactly when column `n` sits at `v` from `s` on
(`stabFamily_track_allZero_iff`). -/
def stabFamily (p : Baire) : Baire := fun m =>
  if p (Nat.pair m.unpair.1.unpair.1 (m.unpair.1.unpair.2.unpair.1 + m.unpair.2))
      = m.unpair.1.unpair.2.unpair.2 then 0 else 1

theorem stabFamily_track_apply (p : Baire) (n s v k : ℕ) :
    Baire.track (Nat.pair n (Nat.pair s v)) (stabFamily p) k
      = if p (Nat.pair n (s + k)) = v then 0 else 1 := by
  simp [stabFamily, Nat.unpair_pair]

/-- Instance `⟨n, s, v⟩` is all-zero exactly when column `n` sits at `v` from `s` on. -/
theorem stabFamily_track_allZero_iff {p : Baire} {n s v : ℕ} :
    (∀ k, Baire.track (Nat.pair n (Nat.pair s v)) (stabFamily p) k = 0)
      ↔ ∀ t, s ≤ t → p (Nat.pair n t) = v := by
  constructor
  · intro h t hst
    have hk := h (t - s)
    rw [stabFamily_track_apply] at hk
    have hts : s + (t - s) = t := by omega
    rw [hts] at hk
    by_contra hne
    rw [if_neg hne] at hk
    exact absurd hk one_ne_zero
  · intro h k
    rw [stabFamily_track_apply]
    exact if_pos (h (s + k) (by omega))

/-- The index of the queried table entry: `Nat.pair j k ↦ Nat.pair n (s + k)` for
`j = Nat.pair n (Nat.pair s v)`. Explicit first-order term. -/
def limStabIndexCode : OracleCode :=
  pair (comp left left) (comp addCode (pair (comp left (comp right left)) right))

theorem eval_limStabIndexCode (p : Baire) (m : ℕ) :
    limStabIndexCode.eval p m = Part.some (Nat.pair m.unpair.1.unpair.1
      (m.unpair.1.unpair.2.unpair.1 + m.unpair.2)) := by
  refine eval_pair_some ?_ ?_
  · rw [eval_comp_some (eval_left p m), eval_left]
  · rw [eval_comp_some (eval_pair_some
      (show (comp left (comp right left)).eval p m =
          Part.some m.unpair.1.unpair.2.unpair.1 by
        rw [eval_comp_some (show (comp right left).eval p m =
            Part.some m.unpair.1.unpair.2 by
          rw [eval_comp_some (eval_left p m), eval_right]), eval_left])
      (eval_right p m)), eval_addCode]

/-- The target value carried by the question index: `Nat.pair j k ↦ v`. -/
def limStabValueCode : OracleCode := comp right (comp right left)

theorem eval_limStabValueCode (p : Baire) (m : ℕ) :
    limStabValueCode.eval p m = Part.some m.unpair.1.unpair.2.unpair.2 := by
  simp only [limStabValueCode]
  rw [eval_comp_some (show (comp right left).eval p m =
    Part.some m.unpair.1.unpair.2 by rw [eval_comp_some (eval_left p m), eval_right]),
    eval_right]

/-- **The preprocessor of `lim_le_parallelize_lpo`**: produce the stability-question family
from the table. The comparison `[a ≠ v]` is the arithmetic
`1 ∸ (1 ∸ ((a ∸ v) + (v ∸ a)))`, so the whole code is an explicit first-order term
over the arithmetic kit. -/
def limStabCode : OracleCode :=
  comp subCode (pair (.const 1) (comp subCode (pair (.const 1)
    (comp addCode (pair
      (comp subCode (pair (comp query limStabIndexCode) limStabValueCode))
      (comp subCode (pair limStabValueCode (comp query limStabIndexCode))))))))

theorem eval_limStabCode (p : Baire) (m : ℕ) :
    limStabCode.eval p m = Part.some (stabFamily p m) := by
  simp only [limStabCode]
  have hq : (OracleCode.comp .query limStabIndexCode).eval p m
      = Part.some (p (Nat.pair m.unpair.1.unpair.1
        (m.unpair.1.unpair.2.unpair.1 + m.unpair.2))) := by
    rw [eval_comp_some (eval_limStabIndexCode p m), eval_query]
  set a := p (Nat.pair m.unpair.1.unpair.1 (m.unpair.1.unpair.2.unpair.1 + m.unpair.2))
  set v := m.unpair.1.unpair.2.unpair.2
  have hd : (OracleCode.comp addCode (pair
      (comp subCode (pair (comp query limStabIndexCode) limStabValueCode))
      (comp subCode (pair limStabValueCode (comp query limStabIndexCode))))).eval p m
      = Part.some ((a - v) + (v - a)) := by
    rw [eval_comp_some (eval_pair_some
      (by rw [eval_comp_some (eval_pair_some hq (eval_limStabValueCode p m)),
        eval_subCode])
      (by rw [eval_comp_some (eval_pair_some (eval_limStabValueCode p m) hq),
        eval_subCode])), eval_addCode]
  rw [eval_comp_some (eval_pair_some (eval_const p 1 m)
    (by rw [eval_comp_some (eval_pair_some (eval_const p 1 m) hd), eval_subCode])),
    eval_subCode]
  rcases eq_or_ne a v with h | h
  · have hs : stabFamily p m = 0 := if_pos h
    rw [hs]
    exact congrArg Part.some (by omega)
  · have hs : stabFamily p m = 1 := if_neg h
    rw [hs]
    exact congrArg Part.some (by omega)

/-- The preprocessor is total: its stream value on any table is the family. -/
theorem evalStream_limStabCode (p : Baire) :
    limStabCode.evalStream p = Part.some (stabFamily p) :=
  computes_iff_evalStream.mp (fun q m => eval_limStabCode q m) p

/-- **The postprocessor of `lim_le_parallelize_lpo`**: per output coordinate `n`,
`rfind`-search the least `u` whose answer bit at index `Nat.pair n u` is `0`, and emit
`u.unpair.2` — the certified limit value carried by the question index. Partial off
valid answer names, as a strong postprocessor may be. -/
def limFromBitsCode : OracleCode :=
  .comp .right (.rfind (.comp .query (.pair .id (.const 0))))

/-! ### Reducing `Lim` to parallelized `LPO` -/

/-- **The reduction of `Lim` to parallelized `LPO`, as an explicit pair**:
`limStabCode` asks the stability
questions and `limFromBitsCode` reads a limit value off *any* accepted answer. -/
theorem isStrongReductionPair_lim_le_parallelize_lpo :
    IsStrongReductionPair Lim LPO.parallelize limStabCode limFromBitsCode := by
  refine isStrongReductionPair_parallelize_lpo_of_questions fun w x hpx hdom => ?_
  obtain rfl : x = w := baireRep_names_iff.mp hpx
  obtain ⟨ℓ, hℓ⟩ := hdom
  refine ⟨stabFamily x, by rw [evalStream_limStabCode]; exact Part.mem_some _, ?_⟩
  intro a hbits
  -- every column forces a zero bit at its true stability pair
  have hex : ∀ n, ∃ u, a (Nat.pair (Nat.pair n u) 0) = 0 := by
    intro n
    obtain ⟨s, hs⟩ := Lim.accepts_iff.mp hℓ n
    refine ⟨Nat.pair s (ℓ n), ?_⟩
    have hall : ∀ k, Baire.track (Nat.pair n (Nat.pair s (ℓ n))) (stabFamily x) k = 0 :=
      stabFamily_track_allZero_iff.mpr fun t hst => hs t hst
    rcases hbits (Nat.pair n (Nat.pair s (ℓ n))) with ⟨hb, -⟩ | ⟨-, k, hk⟩
    · exact hb
    · exact absurd (hall k) hk
  -- per-coordinate evaluation of the postprocessor
  have key : ∀ n, ∃ v, limFromBitsCode.eval a n = Part.some v ∧
      ∃ s, ∀ t, s ≤ t → x (Nat.pair n t) = v := by
    intro n
    set pred : ℕ → Bool := fun u => decide (a (Nat.pair (Nat.pair n u) 0) = 0) with hpred
    have hrfeq : (OracleCode.rfind (.comp .query (.pair OracleCode.id
        (.const 0)))).eval a n = Nat.rfind (pred : ℕ →. Bool) := by
      rw [eval_rfind]
      congr 1
      funext u
      rw [eval_comp_some (eval_pair_some (eval_id a (Nat.pair n u))
        (eval_const a 0 (Nat.pair n u))), eval_query, PFun.coe_val]
      simp [hpred]
    obtain ⟨u₁, hu₁⟩ := hex n
    have hpu : pred u₁ = true := by simp [hpred, hu₁]
    obtain ⟨u₀, hu₀, -⟩ := Nat.rfind_min' hpu
    have hspec := Nat.rfind_spec hu₀
    rw [PFun.coe_val, Part.mem_some_iff] at hspec
    have hbit0 : a (Nat.pair (Nat.pair n u₀) 0) = 0 := by
      have h' := hspec.symm
      simpa [hpred] using h'
    have hrf : (OracleCode.rfind (.comp .query (.pair OracleCode.id
        (.const 0)))).eval a n = Part.some u₀ :=
      Part.eq_some_iff.mpr (by rw [hrfeq]; exact hu₀)
    refine ⟨u₀.unpair.2, ?_, ?_⟩
    · simp only [limFromBitsCode]
      rw [eval_comp_some hrf, eval_right]
    · -- the zero bit certifies stability at the carried value, for every
      -- bit-consistent answer
      rcases hbits (Nat.pair n u₀) with ⟨-, hall⟩ | ⟨hb1, -⟩
      · have hall' : ∀ k, Baire.track (Nat.pair n (Nat.pair u₀.unpair.1 u₀.unpair.2))
            (stabFamily x) k = 0 := by
          rw [Nat.pair_unpair]
          exact hall
        exact ⟨u₀.unpair.1, stabFamily_track_allZero_iff.mp hall'⟩
      · rw [hbit0] at hb1
        exact absurd hb1 (by omega)
  choose v hv hstab using key
  refine ⟨v, mem_evalStream.mpr fun n => ?_, v, baireRep_names_iff.mpr rfl, ?_⟩
  · rw [hv n]
    exact Part.mem_some _
  · exact Lim.accepts_iff.mpr fun n => hstab n

/-- `Lim` reduces strongly to parallelized `LPO`. -/
theorem lim_le_parallelize_lpo : Lim ≤sW LPO.parallelize :=
  strongReduction_iff_exists_reductionPair.mpr
    ⟨_, _, isStrongReductionPair_lim_le_parallelize_lpo⟩

/-! ### Strong parallelizability of `Lim` -/

/-- **The collapse, as an explicit pair**: flatten a packed family of tables into one
table along `Nat.pair` (`flattenTracksCode`); the limit stream of the flattened table
*is* the packed family of limit streams, so the postprocessor is `query`. -/
theorem isStrongReductionPair_parallelize_lim :
    IsStrongReductionPair Lim.parallelize Lim .flattenTracksCode .query := by
  intro F xs hF hdom
  have hxs : ∀ n, xs n = Baire.track n F := fun n =>
    baireRep_names_iff.mp (Representation.sequence_names_iff.mp hF n)
  rw [Problem.parallelize_dom_iff] at hdom
  choose ℓ hℓ using hdom
  set big : Baire := fun m => F (Nat.pair m.unpair.1.unpair.1
    (Nat.pair m.unpair.1.unpair.2 m.unpair.2)) with hbig
  have hbigval : ∀ c t : ℕ, big (Nat.pair c t)
      = F (Nat.pair c.unpair.1 (Nat.pair c.unpair.2 t)) := fun c t => by
    simp [hbig, Nat.unpair_pair]
  have hmem : big ∈ OracleCode.flattenTracksCode.evalStream F := by
    rw [OracleCode.evalStream_flattenTracksCode]
    exact Part.mem_some _
  refine ⟨big, hmem, big, baireRep_names_iff.mpr rfl, ?_, ?_⟩
  · -- the flattened table is a Lim input: every column stabilizes
    refine ⟨fun c => ℓ c.unpair.1 c.unpair.2, Lim.accepts_iff.mpr fun c => ?_⟩
    obtain ⟨s, hs⟩ := Lim.accepts_iff.mp (hℓ c.unpair.1) c.unpair.2
    refine ⟨s, fun t ht => ?_⟩
    rw [hbigval]
    have h := hs t ht
    rw [hxs] at h
    simpa using h
  · intro a y' hay' hacc
    obtain rfl : y' = a := baireRep_names_iff.mp hay'
    refine ⟨y', by simp, fun n => Baire.track n y',
      Representation.sequence_names_iff.mpr fun n => baireRep_names_iff.mpr rfl, ?_⟩
    intro n
    rw [hxs n, Lim.accepts_iff]
    intro i
    obtain ⟨s, hs⟩ := Lim.accepts_iff.mp hacc (Nat.pair n i)
    refine ⟨s, fun t ht => ?_⟩
    have h := hs t ht
    rw [hbigval, Nat.unpair_pair] at h
    simpa using h

/-- **`Lim` is strongly parallelizable**: `Lim.parallelize ≡sW Lim`, the collapse by
flattening and the expansion by extensivity. -/
theorem Lim.isStronglyParallelizable : IsStronglyParallelizable Lim :=
  ⟨strongReduction_iff_exists_reductionPair.mpr
      ⟨_, _, isStrongReductionPair_parallelize_lim⟩,
   parallelize_extensive Lim⟩

/-! ### The calibration -/

/-- **The converse reduction, compositionally**: `lpo_le_lim`, upgraded to strong through
the cylinder, lifted by parallelization, and collapsed by strong parallelizability. -/
theorem parallelize_lpo_le_lim : LPO.parallelize ≤sW Lim :=
  ((Lim.isCylinder.weihrauch_iff_strong.mp lpo_le_lim).parallelize).trans
    Lim.isStronglyParallelizable.collapse

/-- **The calibration**: parallelized `LPO` is strongly equivalent to `Lim` — the
standard target for countably many Σ₁ questions. -/
theorem parallelize_lpo_equiv_lim : LPO.parallelize ≡sW Lim :=
  ⟨parallelize_lpo_le_lim, lim_le_parallelize_lpo⟩

universe u v

/-- **The composite entry point**: a problem whose instances can uniformly pose
countably many Σ₁ questions and decode any consistent answer bits reduces strongly to
`Lim`, through parallelized `LPO` and the calibration. -/
theorem sigma1Family_le_lim {X : RepSpace.{u}} {Y : RepSpace.{v}} {f : Problem X Y}
    {K H : OracleCode}
    (h : ∀ p x, X.rep.Names p x → f.Dom x →
      ∃ G ∈ K.evalStream p,
        ∀ a : Baire, BitConsistent G a →
          ∃ q ∈ H.evalStream a, ∃ y, Y.rep.Names q y ∧ f.accepts x y) :
    f ≤sW Lim :=
  (sigma1Family_le_parallelize_lpo h).trans parallelize_lpo_le_lim

end ComputableAnalysis
