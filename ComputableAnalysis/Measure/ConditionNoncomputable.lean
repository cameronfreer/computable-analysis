/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.TypeTwo.PrimrecArith
import ComputableAnalysis.Measure.Conditioning
import ComputableAnalysis.Measure.CantorJoint
import ComputableAnalysis.Measure.CylinderValues
import ComputableAnalysis.Measure.WeakEquivalence
import ComputableAnalysis.Metric.AdmissibilityConverse

/-!
# Noncomputability of conditioning (Ackerman–Freer–Roy, part A)

The central negative theorem: `condition_noncomputable` exhibits a *computable* joint law
`μ` on the presented product `Cantor × Cantor` that *has* a disintegration in the general
output carrier (`(Condition …).Dom μ`), yet **no computable point** of the output space is
accepted at `μ` — conditioning is not computable, even restricted to a single computable
input.

**The construction** (AFR's base construction, carried on Cantor × Cantor; machine `k` is
`Denumerable.ofNat Nat.Partrec.Code k`, pinned at input `0`, with fuelled halting test
`Nat.Partrec.Code.evaln`). The second coordinate carries a discrete atom
`atomPoint k b = 0ᵏ1b0^ω` with geometric weight `2^{-(k+2)}`; given the atom `(k, b)`, the
first coordinate has independent fair bits EXCEPT that when machine `k` halts, the bit at
its least halting stage is forced equal to the coin `b`. Averaging the coin kills the
bias, so the first marginal is exactly the fair coin `bernoulliProduct ½` — the halting
information is invisible in the joint law but present in every disintegration.

**Computability of μ.** The joint law is the deinterleave pushforward (`jointOfCantor`) of
a single Cantor measure `ρ` whose cylinder masses are the *exactly dyadic* rationals of
`mQ`: on an interleaved word with even part `u` and odd part `t`, at most one atom family
is compatible with `t` and the mass is `0` or a single power `2^{-M}`, decided by finitely
many `evaln` runs at fuel `|u|` plus the closed-form geometric tail (all-`false` odd
words absorb the whole tail `∑_{k ≥ |t|} 2^{-(k+1)} = 2^{-|t|}`). A first-order procedure
emits these exact masses, so `ρ` is a computable point of `cantorMeasureRep` (unit 21),
and unit 35's realizer pushes it to a computable weak name of `μ` on the product.

**The disintegration.** The explicit kernel
`κ x = ∑_{k ∉ H} 2^{-(k+2)}(δ_{(k,0)} + δ_{(k,1)}) + ∑_{k ∈ H} 2^{-(k+1)} δ_{(k, x s_k)}`
is built as a `Measure.sum` of weighted Dirac branches: Markov by the geometric series,
Giry measurable branchwise, weakly continuous (a Lévy–Prokhorov estimate: two inputs
agreeing beyond every recorded halting stage below `K` give kernels within tail mass
`2^{-K}`), and a version of `μ` by π-system uniqueness on cylinder rectangles. Bundled as
a `ContinuousMarkovKernel`, unit 30's `advisedRealizable` provides the `Dom` witness —
continuous but not computable, which is the paper's point.

**The extraction.** A computable accepted `f` would be a computable map
(`funRep_computablePoint_iff`), hence continuous into the weak topology (unit 34's
converse admissibility through the Prokhorov presentation); a.e. uniqueness of
disintegrations (`isCondKernel_ae_unique`, standard Borel) plus full support of the fair
coin and continuity of both sides force `f = κ` *everywhere*. Evaluating at the
computable point `0^ω` yields a computable measure `ν = κ(0^ω)` whose atom masses
`ν(cyl 0ᵏ11)` are `0` on halting `k` and `2^{-(k+2)}` on non-halting `k`; positivity of a
cylinder mass of a computable measure point is Σ₁ (a coded-rational comparison against
its exact-name components), so the complement of the halting set would be r.e. —
contradicting `ComputablePred.halting_problem_not_re`.
-/

set_option linter.style.longFile 2100

namespace ComputableAnalysis

open MeasureTheory ProbabilityTheory Encodable Denumerable OracleCode Metric

open scoped PiNatInstances ENNReal

/-! ### The halting substrate

Machine `k` is `Denumerable.ofNat Nat.Partrec.Code k` at input `0`; `haltsByB k s` is the
decidable fuelled test, `KHalts k` the Σ₁ halting predicate, `hStage k` the least halting
fuel, and `stageK k n` its computable `n`-bounded version (`n` when no fuel `< n`
succeeds). -/

/-- The fuelled halting test: does machine `k` halt on input `0` within fuel `s`? -/
private def haltsByB (k s : ℕ) : Bool :=
  (Nat.Partrec.Code.evaln s (ofNat Nat.Partrec.Code k) 0).isSome

private theorem haltsByB_mono {k s s' : ℕ} (h : s ≤ s') (hs : haltsByB k s = true) :
    haltsByB k s' = true := by
  unfold haltsByB at hs ⊢
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
  exact Option.isSome_iff_exists.mpr ⟨x, Nat.Partrec.Code.evaln_mono h hx⟩

/-- Machine `k` halts on input `0`: the Σ₁ form through the fuelled test. -/
private def KHalts (k : ℕ) : Prop := ∃ s, haltsByB k s = true

private theorem kHalts_iff {k : ℕ} :
    KHalts k ↔ ((ofNat Nat.Partrec.Code k).eval 0).Dom := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨x, Nat.Partrec.Code.evaln_sound hx⟩
  · rintro ⟨x, hx⟩
    obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp hx
    exact ⟨s, Option.isSome_iff_exists.mpr ⟨x, hs⟩⟩

open Classical in
/-- The least halting fuel of machine `k` (`0` on non-halting machines). -/
private noncomputable def hStage (k : ℕ) : ℕ :=
  if h : KHalts k then Nat.find h else 0

private theorem haltsByB_hStage {k : ℕ} (h : KHalts k) : haltsByB k (hStage k) = true := by
  rw [hStage, dif_pos h]
  exact Nat.find_spec h

private theorem not_haltsByB_of_lt_hStage {k : ℕ} (h : KHalts k) {j : ℕ}
    (hj : j < hStage k) : haltsByB k j = false := by
  rw [hStage, dif_pos h] at hj
  simpa using Nat.find_min h hj

/-- The `n`-bounded halting stage: least fuel `< n` that halts, and `n` if none. -/
private def stageK (k n : ℕ) : ℕ := (List.range n).findIdx (haltsByB k)

private theorem stageK_lt_iff {k n : ℕ} :
    stageK k n < n ↔ ∃ s, s < n ∧ haltsByB k s = true := by
  have h := @List.findIdx_lt_length (p := haltsByB k) (xs := List.range n)
  simpa [stageK, List.mem_range] using h

private theorem stageK_halts {k n : ℕ} (h : stageK k n < n) :
    haltsByB k (stageK k n) = true := by
  have h' : stageK k n < (List.range n).length := by simpa using h
  have := List.findIdx_getElem (p := haltsByB k) (xs := List.range n) (w := h')
  simpa [stageK] using this

private theorem stageK_min {k n j : ℕ} (hj : j < stageK k n) : haltsByB k j = false := by
  have h' : j < (List.range n).findIdx (haltsByB k) := by simpa [stageK] using hj
  have := List.not_of_lt_findIdx h'
  simpa using this

/-- Uniqueness of the "first halting fuel" specification. -/
private theorem stage_unique {k : ℕ} {a b : ℕ} (ha : haltsByB k a = true)
    (ha' : ∀ j < a, haltsByB k j = false) (hb : haltsByB k b = true)
    (hb' : ∀ j < b, haltsByB k j = false) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact absurd ha (by rw [hb' a h]; simp)
  · exact h
  · exact absurd hb (by rw [ha' b h]; simp)

private theorem stageK_eq_hStage {k n : ℕ} (h : stageK k n < n) :
    KHalts k ∧ stageK k n = hStage k := by
  have hk : KHalts k := ⟨stageK k n, stageK_halts h⟩
  exact ⟨hk, stage_unique (stageK_halts h) (fun j hj => stageK_min hj)
    (haltsByB_hStage hk) (fun j hj => not_haltsByB_of_lt_hStage hk hj)⟩

private theorem stageK_lt_of_hStage_lt {k n : ℕ} (hk : KHalts k) (hn : hStage k < n) :
    stageK k n < n :=
  stageK_lt_iff.mpr ⟨hStage k, hn, haltsByB_hStage hk⟩

private theorem not_stageK_lt_of_not {k n : ℕ} (hk : ¬ KHalts k) : ¬ stageK k n < n := by
  intro h
  exact hk (stageK_eq_hStage h).1

/-! ### First-`true` positions of binary words -/

/-- The first `true` position of a binary word (`t.length` when all bits are `false`). -/
private def firstTrue (t : List Bool) : ℕ := t.findIdx id

private theorem firstTrue_le (t : List Bool) : firstTrue t ≤ t.length :=
  List.findIdx_le_length

private theorem firstTrue_eq_length_iff {t : List Bool} :
    firstTrue t = t.length ↔ ∀ i, (h : i < t.length) → t[i] = false := by
  rw [firstTrue, List.findIdx_eq_length]
  constructor
  · intro h i hi
    simpa using h t[i] (List.getElem_mem hi)
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    simpa using h i hi

private theorem firstTrue_true {t : List Bool} (h : firstTrue t < t.length) :
    t[firstTrue t] = true := by
  have := List.findIdx_getElem (p := id) (xs := t) (w := h)
  exact this

private theorem firstTrue_false {t : List Bool} {i : ℕ} (hi : i < firstTrue t) :
    t[i]'(lt_of_lt_of_le hi (firstTrue_le t)) = false := by
  have := List.not_of_lt_findIdx (p := id) (xs := t) hi
  simp only [id] at this
  exact this

/-- Characterization of `firstTrue` from a witness specification. -/
private theorem firstTrue_eq_of {t : List Bool} {j : ℕ} (hj : j < t.length)
    (ht : t[j] = true) (hb : ∀ i, i < j → (h : i < t.length) → t[i] = false) :
    firstTrue t = j := by
  rcases lt_trichotomy (firstTrue t) j with h | h | h
  · exact absurd (firstTrue_true (h.trans hj)) (by rw [hb _ h (h.trans hj)]; simp)
  · exact h
  · exact absurd ht (by rw [firstTrue_false h]; simp)

private theorem firstTrue_append_of_lt {t : List Bool} {c : Bool}
    (h : firstTrue t < t.length) : firstTrue (t ++ [c]) = firstTrue t := by
  refine firstTrue_eq_of (by simp; omega) ?_ ?_
  · rw [List.getElem_append_left h]
    exact firstTrue_true h
  · intro i hi hlen
    rw [List.getElem_append_left (hi.trans h)]
    exact firstTrue_false hi

private theorem firstTrue_append_false {t : List Bool} (h : firstTrue t = t.length) :
    firstTrue (t ++ [false]) = t.length + 1 := by
  have hall := firstTrue_eq_length_iff.mp h
  have hnew : ∀ i, (hi : i < (t ++ [false]).length) → (t ++ [false])[i] = false := by
    intro i hi
    rcases lt_or_ge i t.length with h' | h'
    · rw [List.getElem_append_left h']
      exact hall i h'
    · have hieq : i = t.length := by simp at hi; omega
      subst hieq
      rw [List.getElem_append_right le_rfl]
      simp
  simpa using firstTrue_eq_length_iff.mpr hnew

private theorem firstTrue_append_true {t : List Bool} (h : firstTrue t = t.length) :
    firstTrue (t ++ [true]) = t.length := by
  refine firstTrue_eq_of (by simp) ?_ ?_
  · rw [List.getElem_append_right le_rfl]
    simp
  · intro i hi hlen
    rw [List.getElem_append_left hi]
    exact firstTrue_eq_length_iff.mp h i hi

/-- The dropped-tail all-`false` test, transported to absolute positions. -/
private theorem firstTrue_drop_eq_length_iff {t : List Bool} {m : ℕ} :
    firstTrue (t.drop m) = (t.drop m).length ↔
      ∀ i, m ≤ i → (h : i < t.length) → t[i] = false := by
  rw [firstTrue_eq_length_iff]
  constructor
  · intro h i him hi
    have hlt : i - m < (t.drop m).length := by simp [List.length_drop]; omega
    have := h (i - m) hlt
    simp only [List.getElem_drop] at this
    convert this using 2
    omega
  · intro h i hi
    simp only [List.getElem_drop]
    exact h (m + i) (by omega) (by simp [List.length_drop] at hi; omega)

/-! ### The interleaved mass function

`condMassQ k b u` is the conditioned data-law mass of the cylinder `u` given the atom
`(k, b)` — fair bits except the bit at the least halting fuel of machine `k` forced equal
to `b` — an exactly dyadic rational decided by `stageK k |u|`. `mQ u t` is the joint
interleaved mass: at most one atom family is compatible with the odd word `t`, and the
undetermined-coin boundary shapes absorb their geometric tails in closed form. -/

/-- The conditioned data-law mass of the cylinder `u` given the atom `(k, b)`. -/
private def condMassQ (k : ℕ) (b : Bool) (u : List Bool) : ℚ :=
  if stageK k u.length < u.length then
    (if u.getD (stageK k u.length) false = b then 2 else 0) * (2⁻¹ : ℚ) ^ u.length
  else (2⁻¹ : ℚ) ^ u.length

/-- The interleaved joint mass of the even word `u` and the odd word `t`. -/
private def mQ (u t : List Bool) : ℚ :=
  if firstTrue t = t.length then (2⁻¹ : ℚ) ^ (t.length + u.length)
  else if firstTrue t + 1 = t.length then (2⁻¹ : ℚ) ^ (t.length + u.length)
  else if firstTrue (t.drop (firstTrue t + 2)) = (t.drop (firstTrue t + 2)).length then
    (2⁻¹ : ℚ) ^ (firstTrue t + 2) * condMassQ (firstTrue t) (t.getD (firstTrue t + 1) false) u
  else 0

private theorem qhalf_pow_pos (n : ℕ) : (0 : ℚ) < (2⁻¹ : ℚ) ^ n := by positivity

private theorem qhalf_succ (n : ℕ) :
    (2⁻¹ : ℚ) ^ (n + 1) + (2⁻¹ : ℚ) ^ (n + 1) = (2⁻¹ : ℚ) ^ n := by
  rw [pow_succ]
  ring

private theorem condMassQ_nonneg (k : ℕ) (b : Bool) (u : List Bool) :
    0 ≤ condMassQ k b u := by
  unfold condMassQ
  split_ifs <;> positivity

/-- Coin averaging: the two conditioned masses always sum to `2 · 2^{-|u|}`. -/
private theorem condMassQ_sum (k : ℕ) (u : List Bool) :
    condMassQ k false u + condMassQ k true u = 2 * (2⁻¹ : ℚ) ^ u.length := by
  unfold condMassQ
  split_ifs with h0 h1 h2 h3
  · rw [h1] at h2
    simp at h2
  · ring
  · ring
  · rcases Bool.eq_false_or_eq_true (u.getD (stageK k u.length) false) with h | h
    · exact absurd h h3
    · exact absurd h h1
  · ring

private theorem getD_append_lt {u : List Bool} {c : Bool} {i : ℕ} (h : i < u.length) :
    (u ++ [c]).getD i false = u.getD i false := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ h,
    List.getElem_append_left h]

private theorem getD_append_self {u : List Bool} {c : Bool} :
    (u ++ [c]).getD u.length false = c := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right le_rfl]
  simp

private theorem stageK_succ_of_lt {k n : ℕ} (h : stageK k n < n) :
    stageK k (n + 1) = stageK k n := by
  have h2 : stageK k (n + 1) < n + 1 :=
    stageK_lt_iff.mpr ⟨stageK k n, by omega, stageK_halts h⟩
  exact stage_unique (stageK_halts h2) (fun j hj => stageK_min hj)
    (stageK_halts h) (fun j hj => stageK_min hj)

private theorem stageK_succ_of_halt {k n : ℕ} (h : ¬ stageK k n < n)
    (hn : haltsByB k n = true) : stageK k (n + 1) = n := by
  have hbelow : ∀ s, s < n → haltsByB k s = false := by
    intro s hs
    by_contra hc
    exact h (stageK_lt_iff.mpr ⟨s, hs, by simpa using hc⟩)
  have h2 : stageK k (n + 1) < n + 1 := stageK_lt_iff.mpr ⟨n, by omega, hn⟩
  exact stage_unique (stageK_halts h2) (fun j hj => stageK_min hj) hn hbelow

private theorem stageK_succ_of_none {k n : ℕ} (h : ¬ stageK k n < n)
    (hn : haltsByB k n = false) : ¬ stageK k (n + 1) < n + 1 := by
  intro hc
  obtain ⟨s, hs, hhalt⟩ := stageK_lt_iff.mp hc
  rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hs) with h' | h'
  · exact h (stageK_lt_iff.mpr ⟨s, h', hhalt⟩)
  · subst h'
    rw [hn] at hhalt
    exact Bool.noConfusion hhalt

private theorem condMassQ_of_lt {k : ℕ} {b : Bool} {u : List Bool}
    (h : stageK k u.length < u.length) :
    condMassQ k b u =
      (if u.getD (stageK k u.length) false = b then 2 else 0) * (2⁻¹ : ℚ) ^ u.length := by
  rw [condMassQ, if_pos h]

private theorem condMassQ_of_ge {k : ℕ} {b : Bool} {u : List Bool}
    (h : ¬ stageK k u.length < u.length) : condMassQ k b u = (2⁻¹ : ℚ) ^ u.length := by
  rw [condMassQ, if_neg h]

/-- Binary splitting of the conditioned mass in the data word. -/
private theorem condMassQ_split (k : ℕ) (b : Bool) (u : List Bool) :
    condMassQ k b u = condMassQ k b (u ++ [false]) + condMassQ k b (u ++ [true]) := by
  have hlen : ∀ c : Bool, (u ++ [c]).length = u.length + 1 := fun c => by simp
  by_cases h1 : stageK k u.length < u.length
  · have hstab : stageK k (u.length + 1) = stageK k u.length := stageK_succ_of_lt h1
    have hval : ∀ c : Bool, condMassQ k b (u ++ [c]) =
        (if u.getD (stageK k u.length) false = b then 2 else 0)
          * (2⁻¹ : ℚ) ^ (u.length + 1) := by
      intro c
      have hlt : stageK k (u ++ [c]).length < (u ++ [c]).length := by
        rw [hlen, hstab]
        omega
      rw [condMassQ_of_lt hlt, hlen, hstab, getD_append_lt h1]
    rw [condMassQ_of_lt h1, hval false, hval true, ← qhalf_succ u.length]
    ring
  · by_cases h2 : haltsByB k u.length = true
    · have hst : stageK k (u.length + 1) = u.length := stageK_succ_of_halt h1 h2
      have hval : ∀ c : Bool, condMassQ k b (u ++ [c]) =
          (if c = b then 2 else 0) * (2⁻¹ : ℚ) ^ (u.length + 1) := by
        intro c
        have hlt : stageK k (u ++ [c]).length < (u ++ [c]).length := by
          rw [hlen, hst]
          omega
        rw [condMassQ_of_lt hlt, hlen, hst, getD_append_self]
      rw [condMassQ_of_ge h1, hval false, hval true]
      rcases b with _ | _
      · rw [if_pos rfl, if_neg (by decide), pow_succ]
        ring
      · rw [if_neg (by decide), if_pos rfl, pow_succ]
        ring
    · have hval : ∀ c : Bool, condMassQ k b (u ++ [c]) = (2⁻¹ : ℚ) ^ (u.length + 1) := by
        intro c
        have hge : ¬ stageK k (u ++ [c]).length < (u ++ [c]).length := by
          rw [hlen]
          exact stageK_succ_of_none h1 (by simpa using h2)
        rw [condMassQ_of_ge hge, hlen]
      rw [condMassQ_of_ge h1, hval false, hval true, qhalf_succ]

/-! ### Branch evaluations of the interleaved mass -/

private theorem mQ_allFalse {u t : List Bool} (h : firstTrue t = t.length) :
    mQ u t = (2⁻¹ : ℚ) ^ (t.length + u.length) := by
  rw [mQ, if_pos h]

private theorem mQ_oneLast {u t : List Bool} (h1 : ¬ firstTrue t = t.length)
    (h2 : firstTrue t + 1 = t.length) :
    mQ u t = (2⁻¹ : ℚ) ^ (t.length + u.length) := by
  rw [mQ, if_neg h1, if_pos h2]

private theorem mQ_atom {u t : List Bool} (h1 : ¬ firstTrue t = t.length)
    (h2 : ¬ firstTrue t + 1 = t.length)
    (h3 : firstTrue (t.drop (firstTrue t + 2)) = (t.drop (firstTrue t + 2)).length) :
    mQ u t = (2⁻¹ : ℚ) ^ (firstTrue t + 2)
      * condMassQ (firstTrue t) (t.getD (firstTrue t + 1) false) u := by
  rw [mQ, if_neg h1, if_neg h2, if_pos h3]

private theorem mQ_garbage {u t : List Bool} (h1 : ¬ firstTrue t = t.length)
    (h2 : ¬ firstTrue t + 1 = t.length)
    (h3 : ¬ firstTrue (t.drop (firstTrue t + 2)) = (t.drop (firstTrue t + 2)).length) :
    mQ u t = 0 := by
  rw [mQ, if_neg h1, if_neg h2, if_neg h3]

private theorem mQ_nonneg (u t : List Bool) : 0 ≤ mQ u t := by
  unfold mQ
  split_ifs with h1 h2 h3
  · positivity
  · positivity
  · exact mul_nonneg (by positivity) (condMassQ_nonneg _ _ _)
  · exact le_rfl

/-! ### The two splitting laws of the interleaved mass -/

/-- Even-track splitting: appending a data bit halves every branch. -/
private theorem mQ_evenSplit (u t : List Bool) :
    mQ u t = mQ (u ++ [false]) t + mQ (u ++ [true]) t := by
  have hlen : ∀ c : Bool, (u ++ [c]).length = u.length + 1 := fun c => by simp
  by_cases h1 : firstTrue t = t.length
  · rw [mQ_allFalse h1, mQ_allFalse h1, mQ_allFalse h1, hlen, hlen,
      show t.length + (u.length + 1) = (t.length + u.length) + 1 from by omega, qhalf_succ]
  · by_cases h2 : firstTrue t + 1 = t.length
    · rw [mQ_oneLast h1 h2, mQ_oneLast h1 h2, mQ_oneLast h1 h2, hlen, hlen,
        show t.length + (u.length + 1) = (t.length + u.length) + 1 from by omega, qhalf_succ]
    · by_cases h3 : firstTrue (t.drop (firstTrue t + 2)) = (t.drop (firstTrue t + 2)).length
      · rw [mQ_atom h1 h2 h3, mQ_atom h1 h2 h3, mQ_atom h1 h2 h3,
          condMassQ_split (firstTrue t) (t.getD (firstTrue t + 1) false) u]
        ring
      · rw [mQ_garbage h1 h2 h3, mQ_garbage h1 h2 h3, mQ_garbage h1 h2 h3]
        norm_num

/-- Odd-track splitting: the boundary shapes shed one tail weight, atom shapes pin the
coin, and the coin average closes the one-last case. -/
private theorem mQ_oddSplit (u t : List Bool) :
    mQ u t = mQ u (t ++ [false]) + mQ u (t ++ [true]) := by
  by_cases h1 : firstTrue t = t.length
  · have hf : firstTrue (t ++ [false]) = (t ++ [false]).length := by
      rw [firstTrue_append_false h1]
      simp
    have ht : firstTrue (t ++ [true]) = t.length := firstTrue_append_true h1
    have hne : ¬ firstTrue (t ++ [true]) = (t ++ [true]).length := by
      rw [ht]
      simp
    have hol : firstTrue (t ++ [true]) + 1 = (t ++ [true]).length := by
      rw [ht]
      simp
    rw [mQ_allFalse h1, mQ_allFalse hf, mQ_oneLast hne hol]
    simp only [List.length_append, List.length_cons, List.length_nil]
    rw [show t.length + (0 + 1) + u.length = (t.length + u.length) + 1 from by omega,
      qhalf_succ]
  · have hjlt : firstTrue t < t.length := lt_of_le_of_ne (firstTrue_le t) h1
    have hft : ∀ c : Bool, firstTrue (t ++ [c]) = firstTrue t := fun c =>
      firstTrue_append_of_lt hjlt
    have hne1 : ∀ c : Bool, ¬ firstTrue (t ++ [c]) = (t ++ [c]).length := by
      intro c
      rw [hft]
      simp
      omega
    by_cases h2 : firstTrue t + 1 = t.length
    · have hne2 : ∀ c : Bool, ¬ firstTrue (t ++ [c]) + 1 = (t ++ [c]).length := by
        intro c
        rw [hft]
        simp
        omega
      have hdrop : ∀ c : Bool, (t ++ [c]).drop (firstTrue (t ++ [c]) + 2) = [] := by
        intro c
        rw [hft]
        refine List.drop_eq_nil_of_le ?_
        simp
        omega
      have h3 : ∀ c : Bool, firstTrue ((t ++ [c]).drop (firstTrue (t ++ [c]) + 2))
          = ((t ++ [c]).drop (firstTrue (t ++ [c]) + 2)).length := by
        intro c
        rw [hdrop]
        rfl
      have hgetD : ∀ c : Bool, (t ++ [c]).getD (firstTrue t + 1) false = c := by
        intro c
        rw [show firstTrue t + 1 = t.length from h2]
        exact getD_append_self
      rw [mQ_oneLast h1 h2, mQ_atom (hne1 false) (hne2 false) (h3 false),
        mQ_atom (hne1 true) (hne2 true) (h3 true), hft, hft, hgetD false, hgetD true,
        ← mul_add, condMassQ_sum, ← h2]
      ring
    · have hj2 : firstTrue t + 2 ≤ t.length := by omega
      have hne2 : ∀ c : Bool, ¬ firstTrue (t ++ [c]) + 1 = (t ++ [c]).length := by
        intro c
        rw [hft]
        simp
        omega
      have hdropc : ∀ c : Bool,
          (t ++ [c]).drop (firstTrue (t ++ [c]) + 2) = t.drop (firstTrue t + 2) ++ [c] := by
        intro c
        rw [hft]
        exact List.drop_append_of_le_length hj2
      have hgetDc : ∀ c : Bool,
          (t ++ [c]).getD (firstTrue t + 1) false = t.getD (firstTrue t + 1) false := by
        intro c
        exact getD_append_lt (by omega)
      by_cases h3 : firstTrue (t.drop (firstTrue t + 2)) = (t.drop (firstTrue t + 2)).length
      · have h3f : firstTrue ((t ++ [false]).drop (firstTrue (t ++ [false]) + 2))
            = ((t ++ [false]).drop (firstTrue (t ++ [false]) + 2)).length := by
          rw [hdropc, firstTrue_append_false h3]
          simp
        have h3t : ¬ firstTrue ((t ++ [true]).drop (firstTrue (t ++ [true]) + 2))
            = ((t ++ [true]).drop (firstTrue (t ++ [true]) + 2)).length := by
          rw [hdropc, firstTrue_append_true h3]
          simp only [List.length_append, List.length_cons, List.length_nil]
          intro hc
          have hle := firstTrue_le (t.drop (firstTrue t + 2))
          omega
        rw [mQ_atom h1 h2 h3, mQ_atom (hne1 false) (hne2 false) h3f,
          mQ_garbage (hne1 true) (hne2 true) h3t, hft, hgetDc false, add_zero]
      · have hlt3 : firstTrue (t.drop (firstTrue t + 2)) < (t.drop (firstTrue t + 2)).length :=
          lt_of_le_of_ne (firstTrue_le _) h3
        have h3c : ∀ c : Bool, ¬ firstTrue ((t ++ [c]).drop (firstTrue (t ++ [c]) + 2))
            = ((t ++ [c]).drop (firstTrue (t ++ [c]) + 2)).length := by
          intro c
          rw [hdropc, firstTrue_append_of_lt hlt3]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [mQ_garbage h1 h2 h3, mQ_garbage (hne1 false) (hne2 false) (h3c false),
          mQ_garbage (hne1 true) (hne2 true) (h3c true), add_zero]

/-! ### Parity of `wordEven`/`wordOdd` under a one-bit append -/

private theorem wordEven_append_of_even {w : List Bool} {c : Bool} (h : w.length % 2 = 0) :
    wordEven (w ++ [c]) = wordEven w ++ [c] := by
  refine List.ext_getElem ?_ fun i hi1 hi2 => ?_
  · simp only [length_wordEven, List.length_append, List.length_cons, List.length_nil]
    omega
  · rw [getElem_wordEven hi1]
    rcases lt_or_ge i (wordEven w).length with hlt | hge
    · rw [List.getElem_append_left hlt, getElem_wordEven hlt]
      have h2i : 2 * i < w.length := by
        rw [length_wordEven] at hlt
        omega
      rw [List.getElem_append_left h2i]
    · have hieq : i = (wordEven w).length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hi2
        omega
      have h2i : w.length ≤ 2 * i := by
        rw [hieq, length_wordEven]
        omega
      have h2i' : 2 * i = w.length := by
        rw [length_wordEven] at hi1
        simp only [List.length_append, List.length_cons, List.length_nil] at hi1
        omega
      rw [List.getElem_append_right h2i, List.getElem_append_right (hieq ▸ le_rfl)]
      simp [hieq]

private theorem wordOdd_append_of_even {w : List Bool} {c : Bool} (h : w.length % 2 = 0) :
    wordOdd (w ++ [c]) = wordOdd w := by
  refine List.ext_getElem ?_ fun i hi1 hi2 => ?_
  · simp only [length_wordOdd, List.length_append, List.length_cons, List.length_nil]
    omega
  · rw [getElem_wordOdd hi1, getElem_wordOdd hi2]
    have h2i : 2 * i + 1 < w.length := by
      rw [length_wordOdd] at hi2
      omega
    rw [List.getElem_append_left h2i]

private theorem wordEven_append_of_odd {w : List Bool} {c : Bool} (h : w.length % 2 = 1) :
    wordEven (w ++ [c]) = wordEven w := by
  refine List.ext_getElem ?_ fun i hi1 hi2 => ?_
  · simp only [length_wordEven, List.length_append, List.length_cons, List.length_nil]
    omega
  · rw [getElem_wordEven hi1, getElem_wordEven hi2]
    have h2i : 2 * i < w.length := by
      rw [length_wordEven] at hi2
      omega
    rw [List.getElem_append_left h2i]

private theorem wordOdd_append_of_odd {w : List Bool} {c : Bool} (h : w.length % 2 = 1) :
    wordOdd (w ++ [c]) = wordOdd w ++ [c] := by
  refine List.ext_getElem ?_ fun i hi1 hi2 => ?_
  · simp only [length_wordOdd, List.length_append, List.length_cons, List.length_nil]
    omega
  · rw [getElem_wordOdd hi1]
    rcases lt_or_ge i (wordOdd w).length with hlt | hge
    · rw [List.getElem_append_left hlt, getElem_wordOdd hlt]
      have h2i : 2 * i + 1 < w.length := by
        rw [length_wordOdd] at hlt
        omega
      rw [List.getElem_append_left h2i]
    · have hieq : i = (wordOdd w).length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hi2
        omega
      have h2i : w.length ≤ 2 * i + 1 := by
        rw [hieq, length_wordOdd]
        omega
      have h2i' : 2 * i + 1 = w.length := by
        rw [length_wordOdd] at hi1
        simp only [List.length_append, List.length_cons, List.length_nil] at hi1
        omega
      rw [List.getElem_append_right h2i, List.getElem_append_right (hieq ▸ le_rfl)]
      simp [hieq]

/-! ### The joint mass function and its measure -/

/-- The interleaved joint cylinder-mass function of the AFR construction. -/
private noncomputable def condM (w : List Bool) : ℝ :=
  ((mQ (wordEven w) (wordOdd w) : ℚ) : ℝ)

private theorem wordEven_nil : wordEven ([] : List Bool) = [] := by
  simp [wordEven]

private theorem wordOdd_nil : wordOdd ([] : List Bool) = [] := by
  simp [wordOdd]

private theorem condM_isConsistent : IsConsistentCylinderMass condM := by
  refine ⟨?_, fun w => ?_, fun w => ?_⟩
  · rw [condM, wordEven_nil, wordOdd_nil]
    norm_num [mQ, firstTrue]
  · rw [condM]
    exact_mod_cast mQ_nonneg _ _
  · rcases Nat.mod_two_eq_zero_or_one w.length with h | h
    · rw [condM, condM, condM, wordEven_append_of_even h, wordOdd_append_of_even h,
        wordEven_append_of_even h, wordOdd_append_of_even h, ← Rat.cast_add]
      exact congrArg (fun q : ℚ => (q : ℝ)) (mQ_evenSplit (wordEven w) (wordOdd w))
    · rw [condM, condM, condM, wordEven_append_of_odd h, wordOdd_append_of_odd h,
        wordEven_append_of_odd h, wordOdd_append_of_odd h, ← Rat.cast_add]
      exact congrArg (fun q : ℚ => (q : ℝ)) (mQ_oddSplit (wordEven w) (wordOdd w))

/-- The AFR single-Cantor measure: cylinder masses are the interleaved joint masses. -/
private noncomputable def condRho : ProbabilityMeasure Cantor :=
  (existsUnique_probabilityMeasure_of_isConsistent condM_isConsistent).exists.choose

private theorem cylMass_condRho (w : List Bool) : cylMass condRho w = condM w :=
  (existsUnique_probabilityMeasure_of_isConsistent condM_isConsistent).exists.choose_spec w

/-- The AFR joint law on `Cantor × Cantor`: the deinterleave pushforward of `condRho`. -/
private noncomputable def condJoint : ProbabilityMeasure (Cantor × Cantor) :=
  jointOfCantor condRho

/-! ### Exact dyadic mass codes and the computable point of `condRho` -/

private def pow2 (d : ℕ) : ℕ := (fun x => 2 * x)^[d] 1

private theorem pow2_eq (d : ℕ) : pow2 d = 2 ^ d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [pow2, Function.iterate_succ_apply', ← pow2, ih, pow_succ]
    ring

private theorem primrec_pow2 : Primrec pow2 :=
  (primrec_pow 2).of_eq fun d => (pow2_eq d).symm

/-- The rational code of the exact dyadic `2^{-M}`. -/
private def dyadicCode (M : ℕ) : ℕ := Nat.pair (Nat.pair 1 0) (pow2 M - 1)

private theorem primrec_dyadicCode : Primrec dyadicCode :=
  Primrec₂.natPair.comp (Primrec.const (Nat.pair 1 0))
    (Primrec.nat_sub.comp primrec_pow2 (Primrec.const 1))

private theorem ratOfCode_dyadicCode (M : ℕ) :
    ratOfCode (dyadicCode M) = (2⁻¹ : ℚ) ^ M := by
  have hpos : 0 < pow2 M := by rw [pow2_eq]; positivity
  rw [ratOfCode, dyadicCode]
  simp only [Nat.unpair_pair]
  have hden : ((pow2 M - 1 : ℕ) : ℚ) + 1 = (2 : ℚ) ^ M := by
    have hsub : (pow2 M - 1) + 1 = pow2 M := Nat.succ_pred_eq_of_pos hpos
    have hc : (((pow2 M - 1) + 1 : ℕ) : ℚ) = ((pow2 M : ℕ) : ℚ) := by exact_mod_cast hsub
    push_cast at hc
    rw [hc, pow2_eq]
    push_cast
    ring
  rw [hden, inv_pow]
  norm_num

/-- The exact mass code of `mQ u t`: the same branch structure, emitting dyadic codes. -/
private def massCodeW (u t : List Bool) : ℕ :=
  if firstTrue t = t.length then dyadicCode (t.length + u.length)
  else if firstTrue t + 1 = t.length then dyadicCode (t.length + u.length)
  else if firstTrue (t.drop (firstTrue t + 2)) = (t.drop (firstTrue t + 2)).length then
    (if stageK (firstTrue t) u.length < u.length then
      (if u.getD (stageK (firstTrue t) u.length) false = t.getD (firstTrue t + 1) false
       then dyadicCode (firstTrue t + 1 + u.length) else zeroCode)
     else dyadicCode (firstTrue t + 2 + u.length))
  else zeroCode

private theorem ratOfCode_massCodeW (u t : List Bool) :
    ratOfCode (massCodeW u t) = mQ u t := by
  unfold massCodeW mQ condMassQ
  split_ifs with h1 h2 h3 h4 h5
  · exact ratOfCode_dyadicCode _
  · exact ratOfCode_dyadicCode _
  · rw [ratOfCode_dyadicCode]
    ring
  · rw [ratOfCode_zeroCode]
    ring
  · rw [ratOfCode_dyadicCode]
    ring
  · exact ratOfCode_zeroCode

private theorem primrec_haltsByB : Primrec₂ haltsByB := by
  have h1 : Primrec fun p : ℕ × ℕ =>
      ((p.2, ofNat Nat.Partrec.Code p.1), (0 : ℕ)) :=
    (Primrec.snd.pair ((Primrec.ofNat Nat.Partrec.Code).comp Primrec.fst)).pair
      (Primrec.const 0)
  have h2 : Primrec fun p : ℕ × ℕ =>
      Nat.Partrec.Code.evaln p.2 (ofNat Nat.Partrec.Code p.1) 0 :=
    Nat.Partrec.Code.primrec_evaln.comp h1
  exact (Primrec.option_isSome.comp h2).to₂

private theorem primrec_stageK : Primrec₂ stageK := by
  have h := Primrec.list_findIdx (f := fun p : ℕ × ℕ => List.range p.2)
    (p := fun (p : ℕ × ℕ) (s : ℕ) => haltsByB p.1 s)
    (Primrec.list_range.comp Primrec.snd)
    ((primrec_haltsByB.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)
  exact (h.of_eq fun p => rfl).to₂

private theorem primrec_firstTrue : Primrec firstTrue := by
  have h := Primrec.list_findIdx (f := @id (List Bool))
    (p := fun (_ : List Bool) (b : Bool) => b) Primrec.id (Primrec.snd.to₂)
  exact h.of_eq fun l => rfl

/-- Decode an index to a binary word (the `Primcodable (List Bool)` numbering). -/
private def wordOf (e : ℕ) : List Bool := (decode (α := List Bool) e).getD []

private theorem primrec_wordOf : Primrec wordOf :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

private theorem wordOf_encode (s : List Bool) : wordOf (encode s) = s := by
  simp [wordOf, Encodable.encodek]

/-- List-level even subword (a `Primrec`-friendly form of `wordEven`). -/
private def wordEvenL (s : List Bool) : List Bool :=
  (List.range ((s.length + 1) / 2)).map fun i => s.getD (2 * i) false

/-- List-level odd subword (a `Primrec`-friendly form of `wordOdd`). -/
private def wordOddL (s : List Bool) : List Bool :=
  (List.range (s.length / 2)).map fun i => s.getD (2 * i + 1) false

private theorem wordEvenL_eq (s : List Bool) : wordEvenL s = wordEven s := by
  refine List.ext_getElem (by simp [wordEvenL]) fun i h1 h2 => ?_
  have hi : 2 * i < s.length := by
    have h2' := h2
    simp at h2'
    omega
  simp only [wordEvenL, List.getElem_map, List.getElem_range]
  rw [getElem_wordEven h2, List.getD_eq_getElem _ _ hi]

private theorem wordOddL_eq (s : List Bool) : wordOddL s = wordOdd s := by
  refine List.ext_getElem (by simp [wordOddL]) fun i h1 h2 => ?_
  have hi : 2 * i + 1 < s.length := by
    have h2' := h2
    simp at h2'
    omega
  simp only [wordOddL, List.getElem_map, List.getElem_range]
  rw [getElem_wordOdd h2, List.getD_eq_getElem _ _ hi]

private theorem primrec_wordEvenL : Primrec wordEvenL := by
  unfold wordEvenL
  exact Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_div.comp
      (Primrec.succ.comp Primrec.list_length) (Primrec.const 2)))
    ((Primrec.list_getD false).comp Primrec.fst
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)).to₂

private theorem primrec_wordOddL : Primrec wordOddL := by
  unfold wordOddL
  exact Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_div.comp Primrec.list_length (Primrec.const 2)))
    ((Primrec.list_getD false).comp Primrec.fst
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd))).to₂

private theorem primrec₂_massCodeW : Primrec₂ massCodeW := by
  have hU : Primrec fun p : List Bool × List Bool => p.1 := Primrec.fst
  have hT : Primrec fun p : List Bool × List Bool => p.2 := Primrec.snd
  have hA : Primrec fun p : List Bool × List Bool => firstTrue p.2 :=
    primrec_firstTrue.comp hT
  have hB : Primrec fun p : List Bool × List Bool => p.2.length :=
    Primrec.list_length.comp hT
  have hC : Primrec fun p : List Bool × List Bool => p.1.length :=
    Primrec.list_length.comp hU
  have hD : Primrec fun p : List Bool × List Bool => p.2.drop (firstTrue p.2 + 2) :=
    Primrec.list_drop.comp (Primrec.nat_add.comp hA (Primrec.const 2)) hT
  have hE : Primrec fun p : List Bool × List Bool => stageK (firstTrue p.2) p.1.length :=
    primrec_stageK.comp hA hC
  have hG : Primrec fun p : List Bool × List Bool =>
      p.1.getD (stageK (firstTrue p.2) p.1.length) false :=
    (Primrec.list_getD false).comp hU hE
  have hH : Primrec fun p : List Bool × List Bool => p.2.getD (firstTrue p.2 + 1) false :=
    (Primrec.list_getD false).comp hT (Primrec.succ.comp hA)
  have hd1 : Primrec fun p : List Bool × List Bool =>
      dyadicCode (p.2.length + p.1.length) :=
    primrec_dyadicCode.comp (Primrec.nat_add.comp hB hC)
  have hd2 : Primrec fun p : List Bool × List Bool =>
      dyadicCode (firstTrue p.2 + 1 + p.1.length) :=
    primrec_dyadicCode.comp (Primrec.nat_add.comp (Primrec.succ.comp hA) hC)
  have hd3 : Primrec fun p : List Bool × List Bool =>
      dyadicCode (firstTrue p.2 + 2 + p.1.length) :=
    primrec_dyadicCode.comp
      (Primrec.nat_add.comp (Primrec.nat_add.comp hA (Primrec.const 2)) hC)
  have hinner2 : Primrec fun p : List Bool × List Bool =>
      if p.1.getD (stageK (firstTrue p.2) p.1.length) false
          = p.2.getD (firstTrue p.2 + 1) false
       then dyadicCode (firstTrue p.2 + 1 + p.1.length) else zeroCode :=
    Primrec.ite (Primrec.eq.comp hG hH) hd2 (Primrec.const zeroCode)
  have hinner1 : Primrec fun p : List Bool × List Bool =>
      if stageK (firstTrue p.2) p.1.length < p.1.length then
        (if p.1.getD (stageK (firstTrue p.2) p.1.length) false
            = p.2.getD (firstTrue p.2 + 1) false
         then dyadicCode (firstTrue p.2 + 1 + p.1.length) else zeroCode)
      else dyadicCode (firstTrue p.2 + 2 + p.1.length) :=
    Primrec.ite (Primrec.nat_lt.comp hE hC) hinner2 hd3
  have hcond3 : PrimrecPred fun p : List Bool × List Bool =>
      firstTrue (p.2.drop (firstTrue p.2 + 2)) = (p.2.drop (firstTrue p.2 + 2)).length :=
    Primrec.eq.comp (primrec_firstTrue.comp hD) (Primrec.list_length.comp hD)
  have hbr3 : Primrec fun p : List Bool × List Bool =>
      if firstTrue (p.2.drop (firstTrue p.2 + 2)) = (p.2.drop (firstTrue p.2 + 2)).length
      then
        (if stageK (firstTrue p.2) p.1.length < p.1.length then
          (if p.1.getD (stageK (firstTrue p.2) p.1.length) false
              = p.2.getD (firstTrue p.2 + 1) false
           then dyadicCode (firstTrue p.2 + 1 + p.1.length) else zeroCode)
         else dyadicCode (firstTrue p.2 + 2 + p.1.length))
      else zeroCode :=
    Primrec.ite hcond3 hinner1 (Primrec.const zeroCode)
  have hbr2 : Primrec fun p : List Bool × List Bool =>
      if firstTrue p.2 + 1 = p.2.length then dyadicCode (p.2.length + p.1.length)
      else
        (if firstTrue (p.2.drop (firstTrue p.2 + 2))
            = (p.2.drop (firstTrue p.2 + 2)).length
        then
          (if stageK (firstTrue p.2) p.1.length < p.1.length then
            (if p.1.getD (stageK (firstTrue p.2) p.1.length) false
                = p.2.getD (firstTrue p.2 + 1) false
             then dyadicCode (firstTrue p.2 + 1 + p.1.length) else zeroCode)
           else dyadicCode (firstTrue p.2 + 2 + p.1.length))
        else zeroCode) :=
    Primrec.ite (Primrec.eq.comp (Primrec.succ.comp hA) hB) hd1 hbr3
  exact (Primrec.ite (Primrec.eq.comp hA hB) hd1 hbr2).to₂

/-- The component procedure of `condRho`'s measure name: the exact dyadic mass code of
the decoded word. -/
private def massCodeIdx (e : ℕ) : ℕ :=
  massCodeW (wordEvenL (wordOf e)) (wordOddL (wordOf e))

private theorem primrec_massCodeIdx : Primrec massCodeIdx :=
  primrec₂_massCodeW.comp (primrec_wordEvenL.comp primrec_wordOf)
    (primrec_wordOddL.comp primrec_wordOf)

/-- `condRho` is a computable point of the Cantor measure representation: one first-order
procedure emits exact rational names of every cylinder mass. -/
private theorem computablePoint_condRho : cantorMeasureRep.ComputablePoint condRho := by
  refine computablePoint_cantorMeasureRep_iff.mpr ⟨fun e _ => massCodeIdx e, ?_, ?_⟩
  · exact ((primrec_massCodeIdx.comp Primrec.fst).to_comp).to₂
  · intro s
    refine Representation.subtype_names_iff.mpr ?_
    refine (realPresentation.cauchyRep_names_iff).mpr fun n => ?_
    have hval : ((ratOfCode (massCodeIdx (encode s)) : ℚ) : ℝ) = (cylMass01 condRho s).val := by
      rw [massCodeIdx, wordOf_encode, wordEvenL_eq, wordOddL_eq, ratOfCode_massCodeW]
      change ((mQ (wordEven s) (wordOdd s) : ℚ) : ℝ) = cylMass condRho s
      rw [cylMass_condRho, condM]
    change dist (realPresentation.dense (massCodeIdx (encode s)))
        ((cylMass01 condRho s).val) ≤ ((2 : ℝ)⁻¹) ^ n
    rw [show realPresentation.dense (massCodeIdx (encode s))
        = ((ratOfCode (massCodeIdx (encode s)) : ℚ) : ℝ) from rfl, hval, dist_self]
    positivity

/-- `condJoint` is a computable point of the weak measure representation on the presented
product — unit 35's realizer applied to `condRho`'s computable name. -/
private theorem computablePoint_condJoint :
    (weakMeasureRep (cantorPresentation.prod cantorPresentation)).ComputablePoint
      condJoint :=
  computableMap_jointOfCantor.computablePoint computablePoint_condRho

/-! ### Atoms of the second coordinate -/

/-- The atom word `0ᵏ1b` of the second coordinate. -/
private def atomWord (k : ℕ) (b : Bool) : List Bool := List.replicate k false ++ [true, b]

private theorem atomWord_length (k : ℕ) (b : Bool) : (atomWord k b).length = k + 2 := by
  simp [atomWord]

/-- The atom point `0ᵏ1b0^ω` of the second coordinate. -/
private def atomPoint (k : ℕ) (b : Bool) : Cantor := wordPoint (atomWord k b)

private theorem atomPoint_apply (k : ℕ) (b : Bool) (i : ℕ) :
    atomPoint k b i = if i = k then true else if i = k + 1 then b else false := by
  rw [atomPoint, wordPoint_apply, atomWord]
  rcases lt_trichotomy i k with h | rfl | h
  · rw [if_neg (by omega), if_neg (by omega),
      List.getD_eq_getElem _ _ (by simp; omega),
      List.getElem_append_left (by simpa using h)]
    simp
  · rw [if_pos rfl, List.getD_eq_getElem _ _ (by simp),
      List.getElem_append_right (by simp)]
    simp
  · rw [if_neg (by omega)]
    by_cases h1 : i = k + 1
    · subst h1
      rw [if_pos rfl, List.getD_eq_getElem _ _ (by simp),
        List.getElem_append_right (by simp)]
      simp
    · rw [if_neg h1, List.getD_eq_default _ _ (by simp; omega)]

private theorem atomPoint_mem_cyl {k : ℕ} {b : Bool} {t : List Bool} :
    atomPoint k b ∈ (cylinder t : Set Cantor) ↔
      ∀ i, (h : i < t.length) → t[i] = atomPoint k b i := by
  constructor
  · intro hmem i hi
    exact (hmem i hi).symm
  · intro h i hi
    exact (h i hi).symm

private theorem atom_mem_allFalse {k : ℕ} {b : Bool} {t : List Bool}
    (hAF : firstTrue t = t.length) :
    atomPoint k b ∈ (cylinder t : Set Cantor) ↔ t.length ≤ k := by
  rw [atomPoint_mem_cyl]
  constructor
  · intro h
    by_contra hk
    push Not at hk
    have hkk := h k hk
    rw [atomPoint_apply, if_pos rfl, firstTrue_eq_length_iff.mp hAF k hk] at hkk
    exact Bool.noConfusion hkk
  · intro hk i hi
    rw [atomPoint_apply, if_neg (by omega), if_neg (by omega)]
    exact firstTrue_eq_length_iff.mp hAF i hi

private theorem atom_mem_oneLast {k : ℕ} {b : Bool} {t : List Bool}
    (hlt : firstTrue t < t.length) (hOL : firstTrue t + 1 = t.length) :
    atomPoint k b ∈ (cylinder t : Set Cantor) ↔ k = firstTrue t := by
  rw [atomPoint_mem_cyl]
  constructor
  · intro h
    by_contra hk
    rcases lt_trichotomy k (firstTrue t) with hc | hc | hc
    · have hkk := h k (by omega)
      rw [atomPoint_apply, if_pos rfl, firstTrue_false hc] at hkk
      exact Bool.noConfusion hkk
    · exact hk hc
    · have hjj := h (firstTrue t) hlt
      rw [atomPoint_apply, if_neg (by omega), if_neg (by omega), firstTrue_true hlt] at hjj
      exact Bool.noConfusion hjj
  · intro hk i hi
    rw [atomPoint_apply, hk]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp (by omega : i < firstTrue t + 1)) with
      hik | hik
    · rw [if_neg (by omega), if_neg (by omega)]
      exact firstTrue_false hik
    · subst hik
      rw [if_pos rfl]
      exact firstTrue_true hlt

private theorem atom_mem_atomShape {k : ℕ} {b : Bool} {t : List Bool}
    (h2 : firstTrue t + 2 ≤ t.length)
    (hT : firstTrue (t.drop (firstTrue t + 2)) = (t.drop (firstTrue t + 2)).length) :
    atomPoint k b ∈ (cylinder t : Set Cantor) ↔
      k = firstTrue t ∧ b = t.getD (firstTrue t + 1) false := by
  have hjlt : firstTrue t < t.length := by omega
  have htail := firstTrue_drop_eq_length_iff.mp hT
  rw [atomPoint_mem_cyl]
  constructor
  · intro h
    have hk : k = firstTrue t := by
      by_contra hk
      rcases lt_trichotomy k (firstTrue t) with hc | hc | hc
      · have hkk := h k (by omega)
        rw [atomPoint_apply, if_pos rfl, firstTrue_false hc] at hkk
        exact Bool.noConfusion hkk
      · exact hk hc
      · have hjj := h (firstTrue t) hjlt
        rw [atomPoint_apply, if_neg (by omega), if_neg (by omega),
          firstTrue_true hjlt] at hjj
        exact Bool.noConfusion hjj
    refine ⟨hk, ?_⟩
    have hb := h (firstTrue t + 1) (by omega)
    rw [atomPoint_apply, if_neg (by omega), if_pos (by omega)] at hb
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hb.symm
  · rintro ⟨rfl, rfl⟩
    intro i hi
    rw [atomPoint_apply]
    by_cases hik : i = firstTrue t
    · subst hik
      rw [if_pos rfl]
      exact firstTrue_true hjlt
    · by_cases hik1 : i = firstTrue t + 1
      · subst hik1
        rw [if_neg (by omega), if_pos rfl, List.getD_eq_getElem _ _ (by omega)]
      · rw [if_neg hik, if_neg hik1]
        rcases lt_or_ge i (firstTrue t) with hc | hc
        · exact firstTrue_false hc
        · exact htail i (by omega) hi

private theorem atom_not_mem_garbage {k : ℕ} {b : Bool} {t : List Bool}
    (h2 : firstTrue t + 2 ≤ t.length)
    (hT : ¬ firstTrue (t.drop (firstTrue t + 2)) = (t.drop (firstTrue t + 2)).length) :
    atomPoint k b ∉ (cylinder t : Set Cantor) := by
  have hjlt : firstTrue t < t.length := by omega
  have hlt3 : firstTrue (t.drop (firstTrue t + 2)) < (t.drop (firstTrue t + 2)).length :=
    lt_of_le_of_ne (firstTrue_le _) hT
  have hi0lt : firstTrue t + 2 + firstTrue (t.drop (firstTrue t + 2)) < t.length := by
    simp only [List.length_drop] at hlt3
    omega
  have hi0true : t[firstTrue t + 2 + firstTrue (t.drop (firstTrue t + 2))]'hi0lt = true := by
    have h := firstTrue_true hlt3
    simp only [List.getElem_drop] at h
    exact h
  intro hmem
  rw [atomPoint_mem_cyl] at hmem
  have h1 := hmem (firstTrue t) hjlt
  rw [atomPoint_apply, firstTrue_true hjlt] at h1
  have h2' := hmem (firstTrue t + 2 + firstTrue (t.drop (firstTrue t + 2))) hi0lt
  rw [atomPoint_apply, hi0true] at h2'
  by_cases hjk : firstTrue t = k
  · rw [if_neg (by omega), if_neg (by omega)] at h2'
    exact Bool.noConfusion h2'
  · rw [if_neg hjk] at h1
    by_cases hjk1 : firstTrue t = k + 1
    · rw [if_neg (by omega), if_neg (by omega)] at h2'
      exact Bool.noConfusion h2'
    · rw [if_neg hjk1] at h1
      exact Bool.noConfusion h1

/-! ### The explicit disintegration kernel -/

open Classical in
/-- The `k`-th branch of the kernel: on halting machines a single coin-following Dirac of
weight `2^{-(k+1)}`, otherwise the two-atom pair with weight `2^{-(k+2)}` each. -/
private noncomputable def condBranch (k : ℕ) (x : Cantor) : Measure Cantor :=
  if KHalts k then ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) • Measure.dirac (atomPoint k (x (hStage k)))
  else ((2 : ℝ≥0∞)⁻¹) ^ (k + 2) • Measure.dirac (atomPoint k false)
    + ((2 : ℝ≥0∞)⁻¹) ^ (k + 2) • Measure.dirac (atomPoint k true)

private theorem ehalf_pow_ne_top (n : ℕ) : ((2 : ℝ≥0∞)⁻¹) ^ n ≠ ⊤ :=
  ENNReal.pow_ne_top (by simp)

private theorem ehalf_succ (n : ℕ) :
    ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) + ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) = ((2 : ℝ≥0∞)⁻¹) ^ n := by
  rw [pow_succ, ← mul_add, ENNReal.inv_two_add_inv_two, mul_one]

private theorem condBranch_univ (k : ℕ) (x : Cantor) :
    condBranch k x Set.univ = ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) := by
  unfold condBranch
  split_ifs with h
  · simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  · simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact ehalf_succ (k + 1)

private theorem measurable_condBranch_apply (k : ℕ) (S : Set Cantor) :
    Measurable fun x => condBranch k x S := by
  by_cases h : KHalts k
  · have heq : (fun x => condBranch k x S)
        = fun x => ((2 : ℝ≥0∞)⁻¹) ^ (k + 1)
            * Measure.dirac (atomPoint k (x (hStage k))) S := by
      funext x
      rw [condBranch, if_pos h, Measure.smul_apply, smul_eq_mul]
    rw [heq]
    exact Measurable.const_mul
      ((measurable_of_countable fun b : Bool =>
        Measure.dirac (atomPoint k b) S).comp (measurable_pi_apply (hStage k))) _
  · have heq : (fun x => condBranch k x S)
        = fun _ => ((2 : ℝ≥0∞)⁻¹) ^ (k + 2) • Measure.dirac (atomPoint k false) S
            + ((2 : ℝ≥0∞)⁻¹) ^ (k + 2) • Measure.dirac (atomPoint k true) S := by
      funext x
      rw [condBranch, if_neg h, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    rw [heq]
    exact measurable_const

/-- The explicit AFR disintegration kernel, as a countable sum of Dirac branches. -/
private noncomputable def condKerM (x : Cantor) : Measure Cantor :=
  Measure.sum fun k => condBranch k x

private theorem tsum_ehalf_succ : ∑' k : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) = 1 := by
  rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

private theorem isProbability_condKerM (x : Cantor) :
    IsProbabilityMeasure (condKerM x) := by
  constructor
  rw [condKerM, Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [condBranch_univ]
  exact tsum_ehalf_succ

/-- The kernel as a map into probability measures. -/
private noncomputable def condKer (x : Cantor) : ProbabilityMeasure Cantor :=
  ⟨condKerM x, isProbability_condKerM x⟩

private theorem condKerM_apply (x : Cantor) {S : Set Cantor} (hS : MeasurableSet S) :
    condKerM x S = ∑' k, condBranch k x S :=
  Measure.sum_apply _ hS

private theorem measurable_condKerM : Measurable condKerM := by
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  have heq : (fun x => condKerM x S) = fun x => ∑' k, condBranch k x S := by
    funext x
    exact condKerM_apply x hS
  rw [heq]
  exact Measurable.tsum fun k => measurable_condBranch_apply k S

/-! ### Weak continuity of the kernel -/

private theorem tail_tsum (L : ℕ) :
    ∑' k : ℕ, (if k < L then 0 else ((2 : ℝ≥0∞)⁻¹) ^ (k + 1)) = ((2 : ℝ≥0∞)⁻¹) ^ L := by
  induction L with
  | zero => simpa using tsum_ehalf_succ
  | succ L ih =>
    have hsplit : ∀ k : ℕ, (if k < L then 0 else ((2 : ℝ≥0∞)⁻¹) ^ (k + 1))
        = (if k = L then ((2 : ℝ≥0∞)⁻¹) ^ (L + 1) else 0)
          + (if k < L + 1 then 0 else ((2 : ℝ≥0∞)⁻¹) ^ (k + 1)) := by
      intro k
      by_cases h1 : k < L
      · rw [if_pos h1, if_neg (by omega), if_pos (by omega), add_zero]
      · by_cases h2 : k = L
        · subst h2
          rw [if_neg (by omega), if_pos rfl, if_pos (by omega), add_zero]
        · rw [if_neg h1, if_neg h2, if_neg (by omega), zero_add]
    have h1 : ((2 : ℝ≥0∞)⁻¹) ^ (L + 1)
        + (∑' k : ℕ, (if k < L + 1 then 0 else ((2 : ℝ≥0∞)⁻¹) ^ (k + 1)))
        = ((2 : ℝ≥0∞)⁻¹) ^ L := by
      calc ((2 : ℝ≥0∞)⁻¹) ^ (L + 1)
            + (∑' k : ℕ, (if k < L + 1 then 0 else ((2 : ℝ≥0∞)⁻¹) ^ (k + 1)))
          = (∑' k : ℕ, (if k = L then ((2 : ℝ≥0∞)⁻¹) ^ (L + 1) else 0))
            + (∑' k : ℕ, (if k < L + 1 then 0 else ((2 : ℝ≥0∞)⁻¹) ^ (k + 1))) := by
            rw [tsum_ite_eq]
        _ = ∑' k : ℕ, ((if k = L then ((2 : ℝ≥0∞)⁻¹) ^ (L + 1) else 0)
            + (if k < L + 1 then 0 else ((2 : ℝ≥0∞)⁻¹) ^ (k + 1))) :=
            (ENNReal.tsum_add).symm
        _ = ∑' k : ℕ, (if k < L then 0 else ((2 : ℝ≥0∞)⁻¹) ^ (k + 1)) :=
            (tsum_congr hsplit).symm
        _ = ((2 : ℝ≥0∞)⁻¹) ^ L := ih
    exact (ENNReal.add_right_inj (ehalf_pow_ne_top (L + 1))).mp
      (h1.trans (ehalf_succ L).symm)

private theorem condKerM_le_tail {x x' : Cantor} {K : ℕ}
    (hagree : ∀ k, k < K → KHalts k → x' (hStage k) = x (hStage k))
    {B : Set Cantor} (hB : MeasurableSet B) :
    condKerM x' B ≤ condKerM x B + ((2 : ℝ≥0∞)⁻¹) ^ K := by
  rw [condKerM_apply x' hB, condKerM_apply x hB]
  have hle : ∀ k, condBranch k x' B
      ≤ condBranch k x B + (if k < K then 0 else ((2 : ℝ≥0∞)⁻¹) ^ (k + 1)) := by
    intro k
    by_cases hk : k < K
    · rw [if_pos hk, add_zero]
      have heq : condBranch k x' = condBranch k x := by
        unfold condBranch
        split_ifs with h
        · rw [hagree k hk h]
        · rfl
      rw [heq]
    · rw [if_neg hk]
      calc condBranch k x' B ≤ condBranch k x' Set.univ :=
            measure_mono (Set.subset_univ B)
        _ = ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) := condBranch_univ k x'
        _ ≤ condBranch k x B + ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) := le_add_self
  calc ∑' k, condBranch k x' B
      ≤ ∑' k, (condBranch k x B + (if k < K then 0 else ((2 : ℝ≥0∞)⁻¹) ^ (k + 1))) :=
        ENNReal.tsum_le_tsum hle
    _ = (∑' k, condBranch k x B) + ((2 : ℝ≥0∞)⁻¹) ^ K := by
        rw [ENNReal.tsum_add, tail_tsum]

private theorem ofReal_half_pow (n : ℕ) :
    ENNReal.ofReal ((2⁻¹ : ℝ) ^ n) = ((2 : ℝ≥0∞)⁻¹) ^ n := by
  rw [ENNReal.ofReal_pow (by norm_num)]
  congr 1
  rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

/-- Weak continuity of the kernel: agreement beyond the recorded halting stages below `K`
bounds the Lévy–Prokhorov distance by the tail mass `2^{-K}`. -/
private theorem continuous_condKer : Continuous condKer := by
  have hLP : Continuous fun x =>
      (LevyProkhorov.ofMeasure (condKer x) : LevyProkhorov (ProbabilityMeasure Cantor)) := by
    rw [Metric.continuous_iff]
    intro x ε hε
    obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2⁻¹ : ℝ) < 1)
    refine ⟨(1 / 2 : ℝ) ^ ((Finset.range K).sup hStage + 1), by positivity,
      fun x' hx' => ?_⟩
    have hagree : ∀ k, k < K → KHalts k → x' (hStage k) = x (hStage k) := by
      intro k hk _
      refine PiNat.apply_eq_of_dist_lt hx' ?_
      exact le_trans (Finset.le_sup (Finset.mem_range.mpr hk)) (Nat.le_succ _)
    rw [LevyProkhorov.dist_probabilityMeasure_def]
    refine lt_of_le_of_lt ?_ hK
    refine levyProkhorovDist_le_of_forall_le _ _ (by positivity) fun δ B hδ hB => ?_
    have hδ0 : 0 < δ := lt_trans (by positivity) hδ
    calc (condKer x').toMeasure B
        ≤ (condKer x).toMeasure B + ((2 : ℝ≥0∞)⁻¹) ^ K := condKerM_le_tail hagree hB
      _ ≤ (condKer x).toMeasure (thickening δ B) + ENNReal.ofReal δ := by
          refine add_le_add (measure_mono (self_subset_thickening hδ0 B)) ?_
          rw [← ofReal_half_pow]
          exact ENNReal.ofReal_le_ofReal hδ.le
  exact LevyProkhorov.continuous_toMeasure_probabilityMeasure.comp hLP

/-- The bundled continuous Markov kernel of the AFR disintegration. -/
private noncomputable def condCMK : ContinuousMarkovKernel Cantor Cantor where
  law := condKer
  continuous_law := continuous_condKer
  measurable_toMeasure := measurable_condKerM

/-! ### The fair coin and its cylinder masses -/

/-- The fair coin `bernoulliProduct ½` — the first marginal of the AFR joint law. -/
private noncomputable def fairCoin : ProbabilityMeasure Cantor :=
  bernoulliProduct ⟨1 / 2, by norm_num⟩

private theorem fairCoin_cyl (s : List Bool) :
    fairCoin.toMeasure (cylinder s) = ((2 : ℝ≥0∞)⁻¹) ^ s.length := by
  have h := cylMass_bernoulliProduct ⟨1 / 2, by norm_num⟩ s
  have hprod : (∏ i : Fin s.length, cond s[i] ((1 : ℝ) / 2) (1 - (1 : ℝ) / 2))
      = (2⁻¹ : ℝ) ^ s.length := by
    calc ∏ i : Fin s.length, cond s[i] ((1 : ℝ) / 2) (1 - (1 : ℝ) / 2)
        = ∏ _i : Fin s.length, (2⁻¹ : ℝ) :=
          Finset.prod_congr rfl fun i _ => by cases s[i] <;> norm_num
      _ = (2⁻¹ : ℝ) ^ s.length := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hR : (fairCoin.toMeasure (cylinder s)).toReal = (2⁻¹ : ℝ) ^ s.length := by
    rw [show (fairCoin.toMeasure (cylinder s)).toReal = cylMass fairCoin s from rfl,
      fairCoin, h, hprod]
  rw [← ENNReal.ofReal_toReal (measure_ne_top fairCoin.toMeasure (cylinder s)), hR,
    ofReal_half_pow]

private theorem measurableSet_coordEq (j : ℕ) (c : Bool) :
    MeasurableSet {x : Cantor | x j = c} := by
  have h : Measurable fun x : Cantor => x j := measurable_pi_apply j
  exact h (measurableSet_singleton c)

private theorem cyl_inter_eq_of_lt {s : List Bool} {j : ℕ} {c : Bool} (h : j < s.length) :
    (cylinder s : Set Cantor) ∩ {x : Cantor | x j = c}
      = if s[j] = c then (cylinder s : Set Cantor) else ∅ := by
  ext x
  by_cases hc : s[j] = c
  · rw [if_pos hc]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨fun hx => hx.1, fun h1 => ⟨h1, by rw [h1 j h, hc]⟩⟩
  · rw [if_neg hc]
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩
    exact hc (by rw [← h2, h1 j h])

private theorem fairCoin_cyl_inter_aux :
    ∀ (d : ℕ) (s : List Bool) (j : ℕ) (c : Bool), j = s.length + d →
      fairCoin.toMeasure ((cylinder s : Set Cantor) ∩ {x : Cantor | x j = c})
        = ((2 : ℝ≥0∞)⁻¹) ^ (s.length + 1) := by
  intro d
  induction d with
  | zero =>
    intro s j c hj
    have hset : (cylinder s : Set Cantor) ∩ {x : Cantor | x j = c}
        = (cylinder (s ++ [c]) : Set Cantor) := by
      ext x
      rw [Set.mem_inter_iff, Set.mem_setOf_eq, mem_cylinder_append_iff, hj, Nat.add_zero]
    rw [hset, fairCoin_cyl]
    simp
  | succ d ih =>
    intro s j c hj
    have hsplit : (cylinder s : Set Cantor) ∩ {x : Cantor | x j = c}
        = ((cylinder (s ++ [false]) : Set Cantor) ∩ {x : Cantor | x j = c})
          ∪ ((cylinder (s ++ [true]) : Set Cantor) ∩ {x : Cantor | x j = c}) := by
      rw [cylinder_eq_union_append s, Set.union_inter_distrib_right]
    have hdisj : Disjoint
        ((cylinder (s ++ [false]) : Set Cantor) ∩ {x : Cantor | x j = c})
        ((cylinder (s ++ [true]) : Set Cantor) ∩ {x : Cantor | x j = c}) :=
      (disjoint_cylinder_append s).mono Set.inter_subset_left Set.inter_subset_left
    have hmeas : MeasurableSet
        ((cylinder (s ++ [true]) : Set Cantor) ∩ {x : Cantor | x j = c}) :=
      (measurableSet_cylinder _).inter (measurableSet_coordEq j c)
    rw [hsplit, measure_union hdisj hmeas, ih (s ++ [false]) j c (by simp; omega),
      ih (s ++ [true]) j c (by simp; omega)]
    simp only [List.length_append, List.length_cons, List.length_nil]
    rw [show s.length + (0 + 1) + 1 = (s.length + 1) + 1 from by omega]
    exact ehalf_succ (s.length + 1)

private theorem fairCoin_cyl_inter {s : List Bool} {j : ℕ} {c : Bool}
    (h : s.length ≤ j) :
    fairCoin.toMeasure ((cylinder s : Set Cantor) ∩ {x : Cantor | x j = c})
      = ((2 : ℝ≥0∞)⁻¹) ^ (s.length + 1) := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
  exact fairCoin_cyl_inter_aux d s j c hd

/-! ### Set integrals of the kernel branches -/

private theorem condBranch_apply_halt {k : ℕ} (h : KHalts k) (x : Cantor)
    {S : Set Cantor} (hS : MeasurableSet S) :
    condBranch k x S
      = ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) * S.indicator 1 (atomPoint k (x (hStage k))) := by
  rw [condBranch, if_pos h, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hS]

private theorem condBranch_apply_not {k : ℕ} (h : ¬ KHalts k) (x : Cantor)
    {S : Set Cantor} (hS : MeasurableSet S) :
    condBranch k x S
      = ((2 : ℝ≥0∞)⁻¹) ^ (k + 2) * S.indicator 1 (atomPoint k false)
        + ((2 : ℝ≥0∞)⁻¹) ^ (k + 2) * S.indicator 1 (atomPoint k true) := by
  rw [condBranch, if_neg h, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul, Measure.dirac_apply' _ hS, Measure.dirac_apply' _ hS]

private theorem setLIntegral_condBranch_both {k : ℕ} {s t : List Bool}
    (hmem : ∀ b : Bool, atomPoint k b ∈ (cylinder t : Set Cantor)) :
    ∫⁻ x in cylinder s, condBranch k x (cylinder t) ∂fairCoin.toMeasure
      = ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) * fairCoin.toMeasure (cylinder s) := by
  have hval : ∀ x : Cantor, condBranch k x (cylinder t) = ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) := by
    intro x
    by_cases h : KHalts k
    · rw [condBranch_apply_halt h x (measurableSet_cylinder t),
        Set.indicator_of_mem (hmem _), Pi.one_apply, mul_one]
    · rw [condBranch_apply_not h x (measurableSet_cylinder t),
        Set.indicator_of_mem (hmem false), Set.indicator_of_mem (hmem true)]
      simp only [Pi.one_apply, mul_one]
      exact ehalf_succ (k + 1)
  calc ∫⁻ x in cylinder s, condBranch k x (cylinder t) ∂fairCoin.toMeasure
      = ∫⁻ _x in cylinder s, ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) ∂fairCoin.toMeasure :=
        lintegral_congr fun x => hval x
    _ = ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) * fairCoin.toMeasure (cylinder s) :=
        setLIntegral_const _ _

private theorem setLIntegral_condBranch_none {k : ℕ} {s t : List Bool}
    (hmem : ∀ b : Bool, atomPoint k b ∉ (cylinder t : Set Cantor)) :
    ∫⁻ x in cylinder s, condBranch k x (cylinder t) ∂fairCoin.toMeasure = 0 := by
  have hval : ∀ x : Cantor, condBranch k x (cylinder t) = 0 := by
    intro x
    by_cases h : KHalts k
    · rw [condBranch_apply_halt h x (measurableSet_cylinder t),
        Set.indicator_of_notMem (hmem _), mul_zero]
    · rw [condBranch_apply_not h x (measurableSet_cylinder t),
        Set.indicator_of_notMem (hmem false), Set.indicator_of_notMem (hmem true),
        mul_zero, add_zero]
  calc ∫⁻ x in cylinder s, condBranch k x (cylinder t) ∂fairCoin.toMeasure
      = ∫⁻ _x in cylinder s, (0 : ℝ≥0∞) ∂fairCoin.toMeasure :=
        lintegral_congr fun x => hval x
    _ = 0 := lintegral_zero

open Classical in
private theorem setLIntegral_condBranch_single {k : ℕ} {s t : List Bool} {b₀ : Bool}
    (hmem : ∀ b : Bool, atomPoint k b ∈ (cylinder t : Set Cantor) ↔ b = b₀) :
    ∫⁻ x in cylinder s, condBranch k x (cylinder t) ∂fairCoin.toMeasure
      = if KHalts k then
          ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) * fairCoin.toMeasure
            ((cylinder s : Set Cantor) ∩ {x : Cantor | x (hStage k) = b₀})
        else ((2 : ℝ≥0∞)⁻¹) ^ (k + 2) * fairCoin.toMeasure (cylinder s) := by
  by_cases h : KHalts k
  · rw [if_pos h]
    have hval : ∀ x : Cantor, condBranch k x (cylinder t)
        = ((2 : ℝ≥0∞)⁻¹) ^ (k + 1)
          * ({x : Cantor | x (hStage k) = b₀} : Set Cantor).indicator 1 x := by
      intro x
      rw [condBranch_apply_halt h x (measurableSet_cylinder t)]
      congr 1
      by_cases hx : x (hStage k) = b₀
      · rw [Set.indicator_of_mem ((hmem _).mpr hx),
          Set.indicator_of_mem (by exact hx : x ∈ {x : Cantor | x (hStage k) = b₀})]
        simp only [Pi.one_apply]
      · rw [Set.indicator_of_notMem (fun hc => hx ((hmem _).mp hc)),
          Set.indicator_of_notMem (by exact hx : x ∉ {x : Cantor | x (hStage k) = b₀})]
    have hV : MeasurableSet ({x : Cantor | x (hStage k) = b₀} : Set Cantor) :=
      measurableSet_coordEq (hStage k) b₀
    calc ∫⁻ x in cylinder s, condBranch k x (cylinder t) ∂fairCoin.toMeasure
        = ∫⁻ x in cylinder s, ((2 : ℝ≥0∞)⁻¹) ^ (k + 1)
            * ({x : Cantor | x (hStage k) = b₀} : Set Cantor).indicator 1 x
            ∂fairCoin.toMeasure := lintegral_congr fun x => hval x
      _ = ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) * ∫⁻ x in cylinder s,
            ({x : Cantor | x (hStage k) = b₀} : Set Cantor).indicator 1 x
            ∂fairCoin.toMeasure := by
          rw [lintegral_const_mul _ (measurable_one.indicator hV)]
      _ = ((2 : ℝ≥0∞)⁻¹) ^ (k + 1) * fairCoin.toMeasure
            ((cylinder s : Set Cantor) ∩ {x : Cantor | x (hStage k) = b₀}) := by
          rw [lintegral_indicator hV]
          simp only [Pi.one_apply]
          rw [setLIntegral_one, Measure.restrict_apply hV, Set.inter_comm]
  · rw [if_neg h]
    have hval : ∀ x : Cantor, condBranch k x (cylinder t)
        = ((2 : ℝ≥0∞)⁻¹) ^ (k + 2) := by
      intro x
      rw [condBranch_apply_not h x (measurableSet_cylinder t)]
      cases b₀
      · rw [Set.indicator_of_mem ((hmem false).mpr rfl),
          Set.indicator_of_notMem (fun hc => Bool.noConfusion ((hmem true).mp hc))]
        simp only [Pi.one_apply, mul_one, mul_zero, add_zero]
      · rw [Set.indicator_of_notMem (fun hc => Bool.noConfusion ((hmem false).mp hc)),
          Set.indicator_of_mem ((hmem true).mpr rfl)]
        simp only [Pi.one_apply, mul_one, mul_zero, zero_add]
    calc ∫⁻ x in cylinder s, condBranch k x (cylinder t) ∂fairCoin.toMeasure
        = ∫⁻ _x in cylinder s, ((2 : ℝ≥0∞)⁻¹) ^ (k + 2) ∂fairCoin.toMeasure :=
          lintegral_congr fun x => hval x
      _ = ((2 : ℝ≥0∞)⁻¹) ^ (k + 2) * fairCoin.toMeasure (cylinder s) :=
          setLIntegral_const _ _

private theorem ofReal_qhalf_pow (M : ℕ) :
    ENNReal.ofReal (((2⁻¹ : ℚ) ^ M : ℚ) : ℝ) = ((2 : ℝ≥0∞)⁻¹) ^ M := by
  have hcast : (((2⁻¹ : ℚ) ^ M : ℚ) : ℝ) = (2⁻¹ : ℝ) ^ M := by
    push_cast
    ring
  rw [hcast, ofReal_half_pow]

open Classical in
/-- **The kernel-side rectangle integral**: the set integral of the kernel against the
fair coin over a cylinder rectangle is the interleaved mass — checked branch by branch
against the shape trichotomy of the odd word. -/
private theorem lintegral_condKerM_cyl (s t : List Bool) :
    ∫⁻ x in cylinder s, condKerM x (cylinder t) ∂fairCoin.toMeasure
      = ENNReal.ofReal ((mQ s t : ℚ) : ℝ) := by
  have hint : ∫⁻ x in cylinder s, condKerM x (cylinder t) ∂fairCoin.toMeasure
      = ∑' k, ∫⁻ x in cylinder s, condBranch k x (cylinder t) ∂fairCoin.toMeasure := by
    rw [← lintegral_tsum fun k => (measurable_condBranch_apply k (cylinder t)).aemeasurable]
    exact lintegral_congr fun x => condKerM_apply x (measurableSet_cylinder t)
  rw [hint]
  by_cases h1 : firstTrue t = t.length
  · have hterm : ∀ k, ∫⁻ x in cylinder s, condBranch k x (cylinder t) ∂fairCoin.toMeasure
        = (if k < t.length then 0 else ((2 : ℝ≥0∞)⁻¹) ^ (k + 1))
            * fairCoin.toMeasure (cylinder s) := by
      intro k
      by_cases hk : k < t.length
      · rw [if_pos hk, zero_mul]
        refine setLIntegral_condBranch_none fun b => ?_
        rw [atom_mem_allFalse h1]
        omega
      · rw [if_neg hk]
        exact setLIntegral_condBranch_both fun b => (atom_mem_allFalse h1).mpr (by omega)
    rw [tsum_congr hterm, ENNReal.tsum_mul_right, tail_tsum, fairCoin_cyl,
      mQ_allFalse h1, ofReal_qhalf_pow, ← pow_add]
  · by_cases h2 : firstTrue t + 1 = t.length
    · have hlt : firstTrue t < t.length := lt_of_le_of_ne (firstTrue_le t) h1
      have hterm : ∀ k, ∫⁻ x in cylinder s, condBranch k x (cylinder t)
          ∂fairCoin.toMeasure
          = if k = firstTrue t then
              ((2 : ℝ≥0∞)⁻¹) ^ (firstTrue t + 1) * fairCoin.toMeasure (cylinder s)
            else 0 := by
        intro k
        by_cases hk : k = firstTrue t
        · subst hk
          rw [if_pos rfl]
          exact setLIntegral_condBranch_both fun b => (atom_mem_oneLast hlt h2).mpr rfl
        · rw [if_neg hk]
          exact setLIntegral_condBranch_none fun b hc =>
            hk ((atom_mem_oneLast hlt h2).mp hc)
      rw [tsum_congr hterm, tsum_ite_eq, fairCoin_cyl, mQ_oneLast h1 h2, ← h2,
        ofReal_qhalf_pow, ← pow_add]
    · by_cases h3 : firstTrue (t.drop (firstTrue t + 2))
          = (t.drop (firstTrue t + 2)).length
      · have hj2 : firstTrue t + 2 ≤ t.length := by
          have := firstTrue_le t
          omega
        have hmemA : ∀ (k : ℕ) (b : Bool),
            atomPoint k b ∈ (cylinder t : Set Cantor) ↔
              k = firstTrue t ∧ b = t.getD (firstTrue t + 1) false :=
          fun k b => atom_mem_atomShape hj2 h3
        have hterm : ∀ k, ∫⁻ x in cylinder s, condBranch k x (cylinder t)
            ∂fairCoin.toMeasure
            = if k = firstTrue t then
                (if KHalts (firstTrue t) then
                  ((2 : ℝ≥0∞)⁻¹) ^ (firstTrue t + 1) * fairCoin.toMeasure
                    ((cylinder s : Set Cantor)
                      ∩ {x : Cantor | x (hStage (firstTrue t))
                          = t.getD (firstTrue t + 1) false})
                 else ((2 : ℝ≥0∞)⁻¹) ^ (firstTrue t + 2)
                   * fairCoin.toMeasure (cylinder s))
              else 0 := by
          intro k
          by_cases hk : k = firstTrue t
          · subst hk
            rw [if_pos rfl]
            refine setLIntegral_condBranch_single fun b => ?_
            rw [hmemA (firstTrue t) b]
            simp
          · rw [if_neg hk]
            exact setLIntegral_condBranch_none fun b hc => hk ((hmemA k b).mp hc).1
        rw [tsum_congr hterm, tsum_ite_eq, mQ_atom h1 h2 h3]
        by_cases hh : KHalts (firstTrue t)
        · rw [if_pos hh]
          by_cases hst : hStage (firstTrue t) < s.length
          · have hsk : stageK (firstTrue t) s.length < s.length :=
              stageK_lt_of_hStage_lt hh hst
            have hske : stageK (firstTrue t) s.length = hStage (firstTrue t) :=
              (stageK_eq_hStage hsk).2
            rw [cyl_inter_eq_of_lt hst, condMassQ_of_lt hsk, hske,
              List.getD_eq_getElem _ _ hst]
            by_cases hsb : s[hStage (firstTrue t)]'hst
                = t.getD (firstTrue t + 1) false
            · rw [if_pos hsb, if_pos hsb, fairCoin_cyl,
                show ((2⁻¹ : ℚ) ^ (firstTrue t + 2) * (2 * (2⁻¹ : ℚ) ^ s.length) : ℚ)
                    = (2⁻¹ : ℚ) ^ (firstTrue t + 1 + s.length) from by ring,
                ofReal_qhalf_pow, ← pow_add]
            · rw [if_neg hsb, if_neg hsb]
              simp
          · have hns : ¬ stageK (firstTrue t) s.length < s.length := by
              intro hc
              have h2' := (stageK_eq_hStage hc).2
              omega
            rw [condMassQ_of_ge hns, fairCoin_cyl_inter (Nat.le_of_not_lt hst),
              show ((2⁻¹ : ℚ) ^ (firstTrue t + 2) * (2⁻¹ : ℚ) ^ s.length : ℚ)
                  = (2⁻¹ : ℚ) ^ (firstTrue t + 2 + s.length) from by ring,
              ofReal_qhalf_pow, ← pow_add]
            congr 1
            omega
        · rw [if_neg hh]
          have hns : ¬ stageK (firstTrue t) s.length < s.length :=
            not_stageK_lt_of_not hh
          rw [condMassQ_of_ge hns, fairCoin_cyl,
            show ((2⁻¹ : ℚ) ^ (firstTrue t + 2) * (2⁻¹ : ℚ) ^ s.length : ℚ)
                = (2⁻¹ : ℚ) ^ (firstTrue t + 2 + s.length) from by ring,
            ofReal_qhalf_pow, ← pow_add]
      · have hj2 : firstTrue t + 2 ≤ t.length := by
          have := firstTrue_le t
          omega
        have hterm : ∀ k, ∫⁻ x in cylinder s, condBranch k x (cylinder t)
            ∂fairCoin.toMeasure = 0 := fun k =>
          setLIntegral_condBranch_none fun b => atom_not_mem_garbage hj2 h3
        rw [tsum_congr hterm, tsum_zero, mQ_garbage h1 h2 h3]
        simp

/-! ### Rectangle masses of the joint law -/

private theorem condJoint_rect_eq (s t : List Bool) (h : s.length = t.length) :
    condJoint.toMeasure ((cylinder s : Set Cantor) ×ˢ (cylinder t : Set Cantor))
      = ENNReal.ofReal ((mQ s t : ℚ) : ℝ) := by
  rw [condJoint, jointOfCantor_rectangle condRho h]
  have hm : cylMass condRho (wordInterleave s t) = ((mQ s t : ℚ) : ℝ) := by
    rw [cylMass_condRho, condM, wordEven_wordInterleave h, wordOdd_wordInterleave h]
  rw [← hm, cylMass, ENNReal.ofReal_toReal (measure_ne_top _ _)]

private theorem condJoint_rect_grow_t :
    ∀ (d : ℕ) (s t : List Bool), t.length + d = s.length →
      condJoint.toMeasure ((cylinder s : Set Cantor) ×ˢ (cylinder t : Set Cantor))
        = ENNReal.ofReal ((mQ s t : ℚ) : ℝ) := by
  intro d
  induction d with
  | zero =>
    intro s t h
    exact condJoint_rect_eq s t (by omega)
  | succ d ih =>
    intro s t h
    have hsplit : (cylinder s : Set Cantor) ×ˢ (cylinder t : Set Cantor)
        = ((cylinder s : Set Cantor) ×ˢ (cylinder (t ++ [false]) : Set Cantor))
          ∪ ((cylinder s : Set Cantor) ×ˢ (cylinder (t ++ [true]) : Set Cantor)) := by
      rw [cylinder_eq_union_append t, Set.prod_union]
    have hdisj : Disjoint
        ((cylinder s : Set Cantor) ×ˢ (cylinder (t ++ [false]) : Set Cantor))
        ((cylinder s : Set Cantor) ×ˢ (cylinder (t ++ [true]) : Set Cantor)) := by
      rw [Set.disjoint_left]
      rintro ⟨a, b⟩ ⟨-, hb1⟩ ⟨-, hb2⟩
      exact Set.disjoint_left.mp (disjoint_cylinder_append t) hb1 hb2
    have hmeas : MeasurableSet
        ((cylinder s : Set Cantor) ×ˢ (cylinder (t ++ [true]) : Set Cantor)) :=
      (measurableSet_cylinder s).prod (measurableSet_cylinder _)
    rw [hsplit, measure_union hdisj hmeas, ih s (t ++ [false]) (by simp; omega),
      ih s (t ++ [true]) (by simp; omega),
      ← ENNReal.ofReal_add (by exact_mod_cast mQ_nonneg s (t ++ [false]))
        (by exact_mod_cast mQ_nonneg s (t ++ [true])), ← Rat.cast_add]
    exact congrArg (fun q : ℚ => ENNReal.ofReal (q : ℝ)) (mQ_oddSplit s t).symm

private theorem condJoint_rect_grow_s :
    ∀ (d : ℕ) (s t : List Bool), s.length + d = t.length →
      condJoint.toMeasure ((cylinder s : Set Cantor) ×ˢ (cylinder t : Set Cantor))
        = ENNReal.ofReal ((mQ s t : ℚ) : ℝ) := by
  intro d
  induction d with
  | zero =>
    intro s t h
    exact condJoint_rect_eq s t (by omega)
  | succ d ih =>
    intro s t h
    have hsplit : (cylinder s : Set Cantor) ×ˢ (cylinder t : Set Cantor)
        = ((cylinder (s ++ [false]) : Set Cantor) ×ˢ (cylinder t : Set Cantor))
          ∪ ((cylinder (s ++ [true]) : Set Cantor) ×ˢ (cylinder t : Set Cantor)) := by
      rw [cylinder_eq_union_append s, Set.union_prod]
    have hdisj : Disjoint
        ((cylinder (s ++ [false]) : Set Cantor) ×ˢ (cylinder t : Set Cantor))
        ((cylinder (s ++ [true]) : Set Cantor) ×ˢ (cylinder t : Set Cantor)) := by
      rw [Set.disjoint_left]
      rintro ⟨a, b⟩ ⟨ha1, -⟩ ⟨ha2, -⟩
      exact Set.disjoint_left.mp (disjoint_cylinder_append s) ha1 ha2
    have hmeas : MeasurableSet
        ((cylinder (s ++ [true]) : Set Cantor) ×ˢ (cylinder t : Set Cantor)) :=
      (measurableSet_cylinder _).prod (measurableSet_cylinder t)
    rw [hsplit, measure_union hdisj hmeas, ih (s ++ [false]) t (by simp; omega),
      ih (s ++ [true]) t (by simp; omega),
      ← ENNReal.ofReal_add (by exact_mod_cast mQ_nonneg (s ++ [false]) t)
        (by exact_mod_cast mQ_nonneg (s ++ [true]) t), ← Rat.cast_add]
    exact congrArg (fun q : ℚ => ENNReal.ofReal (q : ℝ)) (mQ_evenSplit s t).symm

/-- **Rectangle masses of the AFR joint law**, at all pairs of word lengths. -/
private theorem condJoint_rect (s t : List Bool) :
    condJoint.toMeasure ((cylinder s : Set Cantor) ×ˢ (cylinder t : Set Cantor))
      = ENNReal.ofReal ((mQ s t : ℚ) : ℝ) := by
  rcases le_total t.length s.length with h | h
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
    exact condJoint_rect_grow_t d s t (by omega)
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
    exact condJoint_rect_grow_s d s t (by omega)

/-! ### The first marginal is the fair coin -/

private theorem condJoint_fst : condJoint.toMeasure.fst = fairCoin.toMeasure := by
  have hcyl : ∀ s : List Bool,
      condJoint.toMeasure.fst (cylinder s) = fairCoin.toMeasure (cylinder s) := by
    intro s
    rw [Measure.fst_apply (measurableSet_cylinder s)]
    have hpre : (Prod.fst ⁻¹' (cylinder s : Set Cantor) : Set (Cantor × Cantor))
        = (cylinder s : Set Cantor) ×ˢ (cylinder ([] : List Bool) : Set Cantor) := by
      rw [cylinder_nil, Set.prod_univ]
    rw [hpre, condJoint_rect s [], fairCoin_cyl,
      mQ_allFalse (by rfl : firstTrue ([] : List Bool) = ([] : List Bool).length),
      show ([] : List Bool).length + s.length = s.length from by simp, ofReal_qhalf_pow]
  refine Measure.ext_of_generateFrom_of_iUnion cantorCylinders (fun _ => Set.univ)
    generateFrom_cantorCylinders.symm isPiSystem_cantorCylinders
    (Set.iUnion_const Set.univ) (fun _ => ⟨[], cylinder_nil⟩)
    (fun _ => measure_ne_top _ _) ?_
  rintro _ ⟨s, rfl⟩
  exact hcyl s

/-! ### The compProd identity on cylinder rectangles, and the `Dom` witness -/

/-- The cylinder rectangles of the product — the generating π-system. -/
private def cylRects : Set (Set (Cantor × Cantor)) :=
  {S | ∃ s t : List Bool,
    S = (cylinder s : Set Cantor) ×ˢ (cylinder t : Set Cantor)}

private theorem univ_mem_cylRects : Set.univ ∈ cylRects :=
  ⟨[], [], by rw [cylinder_nil, Set.univ_prod_univ]⟩

private theorem isPiSystem_cylRects : IsPiSystem cylRects := by
  rintro _ ⟨s, t, rfl⟩ _ ⟨s', t', rfl⟩ hne
  rw [Set.prod_inter_prod] at hne ⊢
  rw [Set.prod_nonempty_iff] at hne
  obtain ⟨w1, hw1⟩ := isPiSystem_cantorCylinders _ ⟨s, rfl⟩ _ ⟨s', rfl⟩ hne.1
  obtain ⟨w2, hw2⟩ := isPiSystem_cantorCylinders _ ⟨t, rfl⟩ _ ⟨t', rfl⟩ hne.2
  exact ⟨w1, w2, by rw [hw1, hw2]⟩

private theorem generateFrom_cylRects :
    (inferInstance : MeasurableSpace (Cantor × Cantor))
      = MeasurableSpace.generateFrom cylRects := by
  refine le_antisymm ?_ (MeasurableSpace.generateFrom_le ?_)
  · change MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Cantor)
        ⊔ MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace Cantor)
      ≤ MeasurableSpace.generateFrom cylRects
    refine sup_le ?_ ?_
    · rw [← generateFrom_cantorCylinders, MeasurableSpace.comap_generateFrom]
      refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
      refine MeasurableSpace.measurableSet_generateFrom ⟨u, [], ?_⟩
      rw [cylinder_nil, Set.prod_univ]
    · rw [← generateFrom_cantorCylinders, MeasurableSpace.comap_generateFrom]
      refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
      refine MeasurableSpace.measurableSet_generateFrom ⟨[], u, ?_⟩
      rw [cylinder_nil, Set.univ_prod]
  · rintro _ ⟨s, t, rfl⟩
    exact (measurableSet_cylinder s).prod (measurableSet_cylinder t)

/-- **The disintegration identity**: the fair coin composed with the explicit kernel is
the AFR joint law — π-system uniqueness on cylinder rectangles. -/
private theorem compProd_condCMK :
    fairCoin.toMeasure ⊗ₘ condCMK.toKernel = condJoint.toMeasure := by
  refine Measure.ext_of_generateFrom_of_iUnion cylRects (fun _ => Set.univ)
    generateFrom_cylRects isPiSystem_cylRects (Set.iUnion_const Set.univ)
    (fun _ => univ_mem_cylRects) (fun _ => measure_ne_top _ _) ?_
  rintro _ ⟨s, t, rfl⟩
  rw [Measure.compProd_apply_prod (measurableSet_cylinder s) (measurableSet_cylinder t),
    condJoint_rect s t]
  exact lintegral_condKerM_cyl s t

private theorem isCondKernel_condCMK : IsCondKernel condJoint condCMK.toKernel := by
  refine ⟨inferInstance, ⟨?_⟩⟩
  rw [condJoint_fst]
  exact compProd_condCMK

/-- The `Dom` witness: the kernel's law as a point of the general output carrier. -/
private noncomputable def condDomFun :
    RealizableFun cantorPresentation.cauchyRep (weakMeasureRep cantorPresentation) :=
  condCMK.toRealizableFun cantorPresentation cantorPresentation

private theorem condDom :
    (Condition cantorPresentation cantorPresentation).Dom condJoint :=
  ⟨condDomFun, condCMK.toKernel, isCondKernel_condCMK,
    Filter.Eventually.of_forall fun _ => rfl⟩

/-! ### The extraction: no computable point is accepted

From a computable accepted output: interpret (`funRep_computablePoint_iff`), force
continuity (converse admissibility through the Prokhorov presentation), collapse onto the
explicit kernel a.e. (`isCondKernel_ae_unique`) and then everywhere (full support of the
fair coin), evaluate at `0^ω`, and semidecide the positivity of the atom masses — the
complement of the halting set would be r.e. -/

private theorem weakNames_iff_namesPoint {p : Baire} {ν : ProbabilityMeasure Cantor} :
    WeakMeasureNames cantorPresentation p ν ↔
      (prokhorovPresentation cantorPresentation).NamesPoint p
        (LevyProkhorov.ofMeasure ν) := by
  unfold WeakMeasureNames ComputableMetricPresentation.NamesPoint
  refine forall_congr' fun n => ?_
  rw [show (prokhorovPresentation cantorPresentation).dense (p n)
      = LevyProkhorov.ofMeasure (atomic cantorPresentation (p n)) from rfl,
    LevyProkhorov.dist_probabilityMeasure_def, levyProkhorovDist_comm]

/-- The converse-admissibility step for weak-measure targets: any advice-realized map
into the weak measure representation is weakly continuous. -/
private theorem continuous_of_weakRealizable {f : Cantor → ProbabilityMeasure Cantor}
    {c : OracleCode} {q : Baire}
    (h : AdvisedRealizes cantorPresentation.cauchyRep
      (weakMeasureRep cantorPresentation) c q f) : Continuous f := by
  have h' : AdvisedRealizes cantorPresentation.cauchyRep
      (prokhorovPresentation cantorPresentation).cauchyRep c q
      fun x => LevyProkhorov.ofMeasure (f x) := by
    intro p x hp
    obtain ⟨r, hr, hn⟩ := h p x hp
    refine ⟨r, hr, ?_⟩
    rw [(prokhorovPresentation cantorPresentation).cauchyRep_names_iff]
    exact weakNames_iff_namesPoint.mp
      ((weakMeasureRep_names_iff cantorPresentation).mp hn)
  have hcont := continuous_of_advisedRealizes cantorPresentation
    (prokhorovPresentation cantorPresentation) h'
  exact LevyProkhorov.continuous_toMeasure_probabilityMeasure.comp hcont

/-- The all-`false` stream, the computable evaluation point of the extraction. -/
private def zeroC : Cantor := fun _ => false

private theorem computablePoint_zeroC :
    cantorPresentation.cauchyRep.ComputablePoint zeroC := by
  refine cantorPresentation_cauchyRep_equiv.2.computablePoint ?_
  refine ⟨fun _ => 0, Computable.const 0, ?_⟩
  exact cantorRep_names_iff.mpr ⟨fun n => Nat.zero_le 1, rfl⟩

private theorem firstTrue_atomWord (k : ℕ) (b : Bool) : firstTrue (atomWord k b) = k := by
  refine firstTrue_eq_of (by rw [atomWord_length]; omega) ?_ ?_
  · simp only [atomWord]
    rw [List.getElem_append_right (by simp)]
    simp
  · intro i hi hlen
    simp only [atomWord]
    rw [List.getElem_append_left (by simpa using hi)]
    simp

private theorem atomWord_getD (k : ℕ) (b : Bool) :
    (atomWord k b).getD (k + 1) false = b := by
  rw [atomWord, List.getD_eq_getElem _ _ (by simp),
    List.getElem_append_right (by simp)]
  simp

private theorem atomWord_drop (k : ℕ) (b : Bool) : (atomWord k b).drop (k + 2) = [] :=
  List.drop_eq_nil_of_le (by rw [atomWord_length])

/-- Membership in the `(k, true)` atom cylinder pins the atom exactly. -/
private theorem mem_atomWordTrue_iff (k k' : ℕ) (b : Bool) :
    atomPoint k' b ∈ (cylinder (atomWord k true) : Set Cantor) ↔ k' = k ∧ b = true := by
  have h2 : firstTrue (atomWord k true) + 2 ≤ (atomWord k true).length := by
    rw [firstTrue_atomWord, atomWord_length]
  have h3 : firstTrue ((atomWord k true).drop (firstTrue (atomWord k true) + 2))
      = ((atomWord k true).drop (firstTrue (atomWord k true) + 2)).length := by
    rw [firstTrue_atomWord, atomWord_drop]
    rfl
  rw [atom_mem_atomShape h2 h3, firstTrue_atomWord, atomWord_getD]

open Classical in
/-- The atom masses of the kernel at `0^ω`: `0` on halting machines, the full geometric
weight `2^{-(k+2)}` on non-halting ones. -/
private theorem condKerM_zeroC_atom (k : ℕ) :
    condKerM zeroC (cylinder (atomWord k true))
      = if KHalts k then 0 else ((2 : ℝ≥0∞)⁻¹) ^ (k + 2) := by
  rw [condKerM_apply zeroC (measurableSet_cylinder _)]
  have hterm : ∀ k', condBranch k' zeroC (cylinder (atomWord k true))
      = if k' = k then (if KHalts k then 0 else ((2 : ℝ≥0∞)⁻¹) ^ (k + 2)) else 0 := by
    intro k'
    by_cases hk : k' = k
    · subst hk
      by_cases hh : KHalts k'
      · rw [if_pos rfl, if_pos hh,
          condBranch_apply_halt hh zeroC (measurableSet_cylinder _),
          Set.indicator_of_notMem
            (fun hc => by simpa [zeroC] using ((mem_atomWordTrue_iff k' k' _).mp hc).2),
          mul_zero]
      · rw [if_pos rfl, if_neg hh,
          condBranch_apply_not hh zeroC (measurableSet_cylinder _),
          Set.indicator_of_notMem
            (fun hc => Bool.noConfusion ((mem_atomWordTrue_iff k' k' false).mp hc).2),
          Set.indicator_of_mem ((mem_atomWordTrue_iff k' k' true).mpr ⟨rfl, rfl⟩)]
        simp only [Pi.one_apply, mul_one, mul_zero, zero_add]
    · rw [if_neg hk]
      by_cases hh : KHalts k'
      · rw [condBranch_apply_halt hh zeroC (measurableSet_cylinder _),
          Set.indicator_of_notMem
            (fun hc => hk ((mem_atomWordTrue_iff k k' _).mp hc).1), mul_zero]
      · rw [condBranch_apply_not hh zeroC (measurableSet_cylinder _),
          Set.indicator_of_notMem
            (fun hc => hk ((mem_atomWordTrue_iff k k' false).mp hc).1),
          Set.indicator_of_notMem
            (fun hc => hk ((mem_atomWordTrue_iff k k' true).mp hc).1), mul_zero,
          add_zero]
  rw [tsum_congr hterm, tsum_ite_eq]

open Classical in
private theorem cylMass_condKer_zeroC_atom (k : ℕ) :
    cylMass (condKer zeroC) (atomWord k true)
      = if KHalts k then 0 else (2⁻¹ : ℝ) ^ (k + 2) := by
  have h1 : cylMass (condKer zeroC) (atomWord k true)
      = (condKerM zeroC (cylinder (atomWord k true))).toReal := rfl
  rw [h1, condKerM_zeroC_atom]
  split_ifs with h
  · simp
  · rw [← ofReal_half_pow, ENNReal.toReal_ofReal (by positivity)]

/-! ### The Σ₁ positivity test -/

private theorem ratOfCode_lt_iff' (m₁ m₂ : ℕ) :
    ratOfCode m₁ < ratOfCode m₂ ↔
      m₁.unpair.1.unpair.1 * (m₂.unpair.2 + 1) + m₂.unpair.1.unpair.2 * (m₁.unpair.2 + 1)
        < m₂.unpair.1.unpair.1 * (m₁.unpair.2 + 1)
            + m₁.unpair.1.unpair.2 * (m₂.unpair.2 + 1) := by
  have h₁ : (0 : ℚ) < (m₁.unpair.2 : ℚ) + 1 := by positivity
  have h₂ : (0 : ℚ) < (m₂.unpair.2 : ℚ) + 1 := by positivity
  rw [ratOfCode, ratOfCode, div_lt_div_iff₀ h₁ h₂, sub_mul, sub_mul, sub_lt_sub_iff]
  exact_mod_cast Iff.rfl

/-- Left numerator slot of a rational code. -/
private def ratNumA (m : ℕ) : ℕ := m.unpair.1.unpair.1

/-- Right numerator slot of a rational code. -/
private def ratNumB (m : ℕ) : ℕ := m.unpair.1.unpair.2

/-- Denominator slot of a rational code. -/
private def ratDen (m : ℕ) : ℕ := m.unpair.2 + 1

private theorem primrec_ratNumA : Primrec ratNumA :=
  primrec_unpairFst.comp primrec_unpairFst

private theorem primrec_ratNumB : Primrec ratNumB :=
  primrec_unpairSnd.comp primrec_unpairFst

private theorem primrec_ratDen : Primrec ratDen :=
  Primrec.succ.comp primrec_unpairSnd

/-- The decidable coded-rational comparison, as a `Bool` test. -/
private def ratLtB (m₁ m₂ : ℕ) : Bool :=
  decide (ratNumA m₁ * ratDen m₂ + ratNumB m₂ * ratDen m₁
    < ratNumA m₂ * ratDen m₁ + ratNumB m₁ * ratDen m₂)

private theorem ratLtB_iff {m₁ m₂ : ℕ} :
    ratLtB m₁ m₂ = true ↔ ratOfCode m₁ < ratOfCode m₂ := by
  rw [ratLtB, decide_eq_true_iff]
  simp only [ratNumA, ratNumB, ratDen]
  exact (ratOfCode_lt_iff' m₁ m₂).symm

private theorem primrec₂_ratLtB : Primrec₂ ratLtB := by
  have hnat : PrimrecPred fun p : ℕ × ℕ =>
      ratNumA p.1 * ratDen p.2 + ratNumB p.2 * ratDen p.1
        < ratNumA p.2 * ratDen p.1 + ratNumB p.1 * ratDen p.2 :=
    Primrec.nat_lt.comp
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (primrec_ratNumA.comp Primrec.fst)
          (primrec_ratDen.comp Primrec.snd))
        (Primrec.nat_mul.comp (primrec_ratNumB.comp Primrec.snd)
          (primrec_ratDen.comp Primrec.fst)))
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (primrec_ratNumA.comp Primrec.snd)
          (primrec_ratDen.comp Primrec.fst))
        (Primrec.nat_mul.comp (primrec_ratNumB.comp Primrec.fst)
          (primrec_ratDen.comp Primrec.snd)))
  obtain ⟨_, hraw⟩ := hnat
  have h2 : Primrec fun p : ℕ × ℕ => ratLtB p.1 p.2 :=
    hraw.of_eq fun p => decide_eq_decide.mpr Iff.rfl
  exact h2.to₂

private def repFalse (k : ℕ) : List Bool := (fun l => false :: l)^[k] []

private theorem repFalse_eq (k : ℕ) : repFalse k = List.replicate k false := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [repFalse, Function.iterate_succ_apply', ← repFalse, ih, List.replicate_succ]

private theorem primrec_repFalse : Primrec repFalse :=
  Primrec.nat_iterate Primrec.id (Primrec.const [])
    ((Primrec.list_cons.comp (Primrec.const false) Primrec.snd).to₂)

/-- The encoded `(k, true)` atom word. -/
private def atomIdx (k : ℕ) : ℕ := encode (repFalse k ++ [true, true])

private theorem primrec_atomIdx : Primrec atomIdx :=
  Primrec.encode.comp
    (Primrec.list_append.comp primrec_repFalse (Primrec.const [true, true]))

private theorem atomIdx_eq (k : ℕ) : atomIdx k = encode (atomWord k true) := by
  rw [atomIdx, repFalse_eq, atomWord]

/-! ### The negative clause -/

private theorem no_computable_accepted
    (f : RealizableFun cantorPresentation.cauchyRep (weakMeasureRep cantorPresentation))
    (hf : (funRep cantorPresentation.cauchyRep
      (weakMeasureRep cantorPresentation)).ComputablePoint f)
    (hacc : (Condition cantorPresentation cantorPresentation).accepts condJoint f) :
    False := by
  have hcm : ComputableMap cantorPresentation.cauchyRep
      (weakMeasureRep cantorPresentation) f.toFun := funRep_computablePoint_iff.mp hf
  obtain ⟨c, q, hcq⟩ := f.exists_advised
  have hcont : Continuous f.toFun := continuous_of_weakRealizable hcq
  obtain ⟨κ', hκ', hae⟩ := hacc
  have haeK : CondKernelAEEq condJoint κ' condCMK.toKernel :=
    isCondKernel_ae_unique hκ' isCondKernel_condCMK
  have haefun : f.toFun =ᵐ[condJoint.toMeasure.fst] condKer := by
    filter_upwards [hae, haeK] with x hx1 hx2
    exact ProbabilityMeasure.toMeasure_injective (hx1.trans hx2)
  rw [condJoint_fst] at haefun
  haveI hOP : fairCoin.toMeasure.IsOpenPosMeasure :=
    isOpenPosMeasure_bernoulliProduct (by norm_num) (by norm_num)
  have heq : f.toFun = condKer := Measure.eq_of_ae_eq haefun hcont continuous_condKer
  have hν : cantorMeasureRep.ComputablePoint (condKer zeroC) := by
    rw [← congrFun heq zeroC]
    exact cantorMeasureRep_equiv_weak.2.computablePoint
      (hcm.computablePoint computablePoint_zeroC)
  obtain ⟨F, hFc, hFn⟩ := computablePoint_cantorMeasureRep_iff.mp hν
  have hest : ∀ (s : List Bool) (n : ℕ),
      |((ratOfCode (F (encode s) n) : ℚ) : ℝ) - cylMass (condKer zeroC) s|
        ≤ ((2 : ℝ)⁻¹) ^ n := by
    intro s n
    have h1 := Representation.subtype_names_iff.mp (hFn s)
    have h2 := (realPresentation.cauchyRep_names_iff).mp h1 n
    rwa [show realPresentation.dense (F (encode s) n)
        = ((ratOfCode (F (encode s) n) : ℚ) : ℝ) from rfl, Real.dist_eq] at h2
  have hsemi : REPred fun cd : Nat.Partrec.Code =>
      0 < cylMass (condKer zeroC) (atomWord (encode cd) true) := by
    have htest : Computable fun a : Nat.Partrec.Code × ℕ =>
        ratLtB (dyadicCode a.2) (F (atomIdx (encode a.1)) a.2) :=
      primrec₂_ratLtB.to_comp.comp (primrec_dyadicCode.comp Primrec.snd).to_comp
        (hFc.comp (primrec_atomIdx.comp (Primrec.encode.comp Primrec.fst)).to_comp
          Primrec.snd.to_comp)
    have hP : REPred fun a : Nat.Partrec.Code × ℕ =>
        ratLtB (dyadicCode a.2) (F (atomIdx (encode a.1)) a.2) = true :=
      ComputablePred.to_re (ComputablePred.computable_iff.mpr ⟨_, htest, rfl⟩)
    have hEx : REPred fun cd : Nat.Partrec.Code => ∃ n : ℕ,
        ratLtB (dyadicCode n) (F (atomIdx (encode cd)) n) = true :=
      repred_exists_nat hP
    refine hEx.of_eq fun cd => ?_
    constructor
    · rintro ⟨n, hn⟩
      rw [atomIdx_eq] at hn
      have hlt := ratLtB_iff.mp hn
      rw [ratOfCode_dyadicCode] at hlt
      have hlt' : ((2 : ℝ)⁻¹) ^ n
          < ((ratOfCode (F (encode (atomWord (encode cd) true)) n) : ℚ) : ℝ) := by
        have hc := (Rat.cast_lt (K := ℝ)).mpr hlt
        push_cast at hc
        exact hc
      have habs := abs_le.mp (hest (atomWord (encode cd) true) n)
      linarith [habs.2]
    · intro hpos
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (half_pos hpos)
        (by norm_num : (2⁻¹ : ℝ) < 1)
      refine ⟨n, ratLtB_iff.mpr ?_⟩
      rw [ratOfCode_dyadicCode]
      have habs := abs_le.mp (hest (atomWord (encode cd) true) n)
      have hR : ((2 : ℝ)⁻¹) ^ n
          < ((ratOfCode (F (atomIdx (encode cd)) n) : ℚ) : ℝ) := by
        rw [atomIdx_eq]
        linarith [habs.1]
      refine (Rat.cast_lt (K := ℝ)).mp ?_
      push_cast
      exact hR
  refine ComputablePred.halting_problem_not_re 0 ?_
  have hpred : (fun cd : Nat.Partrec.Code => ¬ (cd.eval 0).Dom)
      = fun cd => 0 < cylMass (condKer zeroC) (atomWord (encode cd) true) := by
    funext cd
    refine propext ?_
    have hmass := cylMass_condKer_zeroC_atom (encode cd)
    by_cases hh : (cd.eval 0).Dom
    · have hK : KHalts (encode cd) := kHalts_iff.mpr (by rwa [Denumerable.ofNat_encode])
      rw [if_pos hK] at hmass
      exact iff_of_false (not_not_intro hh) (by rw [hmass]; exact lt_irrefl 0)
    · have hK : ¬ KHalts (encode cd) := fun hc =>
        hh (by have := kHalts_iff.mp hc; rwa [Denumerable.ofNat_encode] at this)
      rw [if_neg hK] at hmass
      refine iff_of_true hh ?_
      rw [hmass]
      positivity
  rw [hpred]
  exact hsemi

/-! ### The frozen headline -/

/-- **Noncomputability of conditioning** (Ackerman–Freer–Roy, part A, pinned on the
presented product `Cantor × Cantor`): a computable joint law that has a disintegration in
the general output carrier, yet accepts NO computable point of the output space. The
witness is the AFR joint law `condJoint`; its `Dom` witness is the explicit continuous
kernel (continuous but not computable), and any computable accepted output would
semidecide the complement of the halting set. -/
theorem condition_noncomputable :
    ∃ μ : ProbabilityMeasure (Cantor × Cantor),
      (jointMeasureSpace cantorPresentation cantorPresentation).rep.ComputablePoint μ ∧
        (Condition cantorPresentation cantorPresentation).Dom μ ∧
        ∀ f, (condFunSpace cantorPresentation cantorPresentation).rep.ComputablePoint f →
          ¬ (Condition cantorPresentation cantorPresentation).accepts μ f :=
  ⟨condJoint, computablePoint_condJoint, condDom,
    fun f hf hacc => no_computable_accepted f hf hacc⟩

/-- **Conditioning is not a computable problem.** No oracle machine takes names of joint
laws to names of accepted conditional versions.

This is the operational form of `condition_noncomputable`, and for a multivalued problem it
is the stronger reading: the claim is not that some chosen canonical conditioning map fails
to be computable, but that no machine can uniformly return *even one* accepted version. A
realizer would converge on the witness's computable name, and its stream value there would be
computable, so it would exhibit a computable accepted version — which the witness has none of.

The scope is the repository's output representation: advice-realizable conditional maps taken
modulo the acceptance relation. A differently represented quotient of measurable kernels would
need its own transfer theorem. -/
theorem not_computableProblem_condition :
    ¬ ComputableProblem (Condition cantorPresentation cantorPresentation) := by
  intro hc
  obtain ⟨μ, hμ, hdom, hnone⟩ := condition_noncomputable
  obtain ⟨f, hf, hacc⟩ := hc.exists_computablePoint_accepts hμ hdom
  exact hnone f hf hacc

end ComputableAnalysis
