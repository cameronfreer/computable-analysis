/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.ForMathlib.PrimrecContainers
import ComputableAnalysis.TypeTwo.Tracks
import ComputableAnalysis.TypeTwo.Universal
import ComputableAnalysis.Weihrauch.StrongReduction
import ComputableAnalysis.Weihrauch.Principles.LLPO

/-!
# Closed choice on two points and the calibration `C₂ ≡sW LLPO`

`C₂` is choice on the two-point space from negative information: a name enumerates
removals — value `i + 1` at any position removes the point `i ∈ {0, 1}`, value `0`
carries no information — and an accepted answer is a point never removed. The domain is
the nonemptiness promise: some point survives.

`C₂ ≡sW LLPO`, both directions by a fixed preprocessor and the trivial postprocessor
`query` (the answer, a `natRep` name of the chosen point, transfers unchanged):

* `llpo_le_c2` translates events: a nonzero entry of the `LLPO` input at position `k`
  removes the point `k % 2` — a nonzero on the even track refutes answer `0`, on the odd
  track answer `1`. The preprocessor `llpoRemovalCode` is an explicit first-order term
  over the arithmetic kit. The at-most-one promise makes at most one point removed, and
  the vanishing track's point survives.
* `c2_le_llpo` must conversely produce an input with **at most one** nonzero entry from
  a removal stream that may repeat removals, so it flags only *first* removals:
  `c2FlagStream p` is nonzero at `2 n` exactly when position `n` is the first removal of
  point `0`, and at `2 n + 1` for point `1`. First occurrences are unique per parity,
  and under the nonemptiness promise only one parity occurs at all. The flags are a
  prefix computation, so the preprocessor comes from the head-adaptive prefix bridge
  `OracleCode.exists_prefixPostCode`.

The calibration keeps the closed-set and omniscience presentations independently
meaningful; it is the two-point instance of the closed-choice bridges of
Brattka–Gherardi (arXiv:0905.4679).
-/

namespace ComputableAnalysis

open OracleCode Encodable Denumerable

/-- **Closed choice on two points**: the input enumerates removals (`i + 1` removes
`i ∈ {0, 1}`; `0` is no information), and an accepted answer is a surviving point. The
domain is the promise that some point survives. -/
def C₂ : Problem baireSpace natSpace :=
  ⟨fun p (i : ℕ) => i ≤ 1 ∧ ∀ n, p n ≠ i + 1⟩

/-- **Definitional unfolding of `C₂.accepts`.** An explicit rewrite lemma, deliberately
not a global `simp` rule: the semantic API the compact-choice branch consumes. -/
theorem C₂.accepts_iff {p : Baire} {i : ℕ} :
    C₂.accepts p i ↔ i ≤ 1 ∧ ∀ n, p n ≠ i + 1 :=
  Iff.rfl

/-! ### `LLPO ≤sW C₂` -/

/-- The removal stream of an `LLPO` input: a nonzero entry at position `k` removes the
point `k % 2`. -/
def llpoRemovalStream (p : Baire) : Baire := fun k =>
  if p k = 0 then 0 else k % 2 + 1

/-- **The preprocessor of `llpo_le_c2`**: an explicit first-order term computing the
removal stream, branching on the normalized flag `1 ∸ (1 ∸ p k)`. -/
def llpoRemovalCode : OracleCode :=
  comp (caseszCode zero (comp succ (comp right div2mod2Code)))
    (pair .id (comp subCode (pair (.const 1) (comp subCode (pair (.const 1) query)))))

theorem eval_llpoRemovalCode (p : Baire) (k : ℕ) :
    llpoRemovalCode.eval p k = Part.some (llpoRemovalStream p k) := by
  simp only [llpoRemovalCode]
  have hflag : (comp subCode (pair (OracleCode.const 1)
      (comp subCode (pair (OracleCode.const 1) query)))).eval p k
      = Part.some (1 - (1 - p k)) := by
    rw [eval_comp_some (eval_pair_some (eval_const p 1 k)
      (by rw [eval_comp_some (eval_pair_some (eval_const p 1 k) (eval_query p k)),
        eval_subCode])), eval_subCode]
  rcases eq_or_ne (p k) 0 with h | h
  · have h0 : (1 : ℕ) - (1 - p k) = 0 := by omega
    rw [eval_comp_some (eval_pair_some (eval_id p k) (h0 ▸ hflag)),
      eval_caseszCode_zero]
    simp only [llpoRemovalStream, if_pos h]
    rfl
  · have h1 : (1 : ℕ) - (1 - p k) = 1 := by omega
    rw [eval_comp_some (eval_pair_some (eval_id p k) (h1 ▸ hflag)),
      eval_caseszCode_one _ (show OracleCode.zero.eval p k = Part.some 0 from rfl)]
    rw [eval_comp_some (show (comp right div2mod2Code).eval p k = Part.some (k % 2) by
      rw [eval_comp_some (eval_div2mod2Code p k), eval_right, Nat.unpair_pair]), eval_succ]
    simp [llpoRemovalStream, h]

/-- **`LLPO ≤sW C₂`, as an explicit pair**: translate refutation events into removals and
pass the chosen point through unchanged. -/
theorem isStrongReductionPair_llpo_le_c2 :
    IsStrongReductionPair LLPO C₂ llpoRemovalCode .query := by
  intro w x hpx hdom
  obtain rfl : x = w := baireRep_names_iff.mp hpx
  obtain ⟨i₀, hi₀⟩ := hdom
  obtain ⟨hone, hdisj⟩ := LLPO.accepts_iff.mp hi₀
  have hmem : llpoRemovalStream x ∈ llpoRemovalCode.evalStream x :=
    mem_evalStream.mpr fun k => by rw [eval_llpoRemovalCode]; exact Part.mem_some _
  have hdom' : C₂.Dom (llpoRemovalStream x) := by
    rcases hdisj with ⟨-, hall⟩ | ⟨-, hall⟩
    · refine ⟨(0 : ℕ), C₂.accepts_iff.mpr ⟨by omega, fun n hn => ?_⟩⟩
      rcases eq_or_ne (x n) 0 with h | h
      · simp [llpoRemovalStream, h] at hn
      · have hpar : n % 2 = 0 := by
          simp only [llpoRemovalStream, if_neg h] at hn
          omega
        have hev : n = 2 * (n / 2) := by omega
        exact h (hev ▸ hall (n / 2))
    · refine ⟨(1 : ℕ), C₂.accepts_iff.mpr ⟨le_rfl, fun n hn => ?_⟩⟩
      rcases eq_or_ne (x n) 0 with h | h
      · simp [llpoRemovalStream, h] at hn
      · have hpar : n % 2 = 1 := by
          simp only [llpoRemovalStream, if_neg h] at hn
          omega
        have hodd : n = 2 * (n / 2) + 1 := by omega
        exact h (hodd ▸ hall (n / 2))
  refine ⟨llpoRemovalStream x, hmem, llpoRemovalStream x, baireRep_names_iff.mpr rfl,
    hdom', fun a y' hay' hacc => ?_⟩
  obtain ⟨hy'le, hnorem⟩ := C₂.accepts_iff.mp hacc
  refine ⟨a, by simp, y', hay', LLPO.accepts_iff.mpr ⟨hone, ?_⟩⟩
  obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.mp hy'le
  · refine Or.inl ⟨rfl, fun n => ?_⟩
    by_contra h
    exact hnorem (2 * n) (by simp [llpoRemovalStream, if_neg h])
  · refine Or.inr ⟨rfl, fun n => ?_⟩
    by_contra h
    exact hnorem (2 * n + 1) (by simp [llpoRemovalStream, if_neg h])

/-! ### `C₂ ≤sW LLPO` -/

/-- The first-removal flags of a removal stream: coordinate `2 n + j` (for `j ∈ {0, 1}`)
is `1` exactly when position `n` is the *first* removal of point `j`. Flagging only first
removals is what gives the at-most-one promise `LLPO` requires. -/
def c2FlagStream (p : Baire) : Baire := fun k =>
  if p (k / 2) = k % 2 + 1 ∧ ∀ m < k / 2, p m ≠ k % 2 + 1 then 1 else 0

private theorem c2FlagStream_even (p : Baire) (n : ℕ) :
    c2FlagStream p (2 * n) = if p n = 1 ∧ ∀ m < n, p m ≠ 1 then 1 else 0 := by
  have h1 : 2 * n / 2 = n := by omega
  have h2 : 2 * n % 2 = 0 := by omega
  simp [c2FlagStream, h1, h2]

private theorem c2FlagStream_odd (p : Baire) (n : ℕ) :
    c2FlagStream p (2 * n + 1) = if p n = 2 ∧ ∀ m < n, p m ≠ 2 then 1 else 0 := by
  have h1 : (2 * n + 1) / 2 = n := by omega
  have h2 : (2 * n + 1) % 2 = 1 := by omega
  simp [c2FlagStream, h1, h2]

/-- The even track of the flags vanishes exactly when point `0` is never removed. -/
theorem c2FlagStream_even_zero_iff {p : Baire} :
    (∀ n, c2FlagStream p (2 * n) = 0) ↔ ∀ n, p n ≠ 1 := by
  constructor
  · intro h n hn
    by_cases hex : ∃ m, p m = 1
    · have hfind := Nat.find_spec hex
      have hmin : ∀ m < Nat.find hex, p m ≠ 1 := fun m hm => Nat.find_min hex hm
      have := h (Nat.find hex)
      rw [c2FlagStream_even, if_pos ⟨hfind, hmin⟩] at this
      exact one_ne_zero this
    · exact hex ⟨n, hn⟩
  · intro h n
    rw [c2FlagStream_even, if_neg fun hc => h n hc.1]

/-- The odd track of the flags vanishes exactly when point `1` is never removed. -/
theorem c2FlagStream_odd_zero_iff {p : Baire} :
    (∀ n, c2FlagStream p (2 * n + 1) = 0) ↔ ∀ n, p n ≠ 2 := by
  constructor
  · intro h n hn
    by_cases hex : ∃ m, p m = 2
    · have hfind := Nat.find_spec hex
      have hmin : ∀ m < Nat.find hex, p m ≠ 2 := fun m hm => Nat.find_min hex hm
      have := h (Nat.find hex)
      rw [c2FlagStream_odd, if_pos ⟨hfind, hmin⟩] at this
      exact one_ne_zero this
    · exact hex ⟨n, hn⟩
  · intro h n
    rw [c2FlagStream_odd, if_neg fun hc => h n hc.1]

/-- A nonzero flag unpacks to a first-removal certificate. -/
private theorem c2FlagStream_ne_zero {p : Baire} {k : ℕ} (h : c2FlagStream p k ≠ 0) :
    p (k / 2) = k % 2 + 1 ∧ ∀ m < k / 2, p m ≠ k % 2 + 1 := by
  by_contra hc
  exact h (if_neg hc)

/-- **The preprocessor of `c2_le_llpo`**, from the head-adaptive prefix bridge: the flag
at `k` is a computable function of the length-`(k / 2 + 1)` prefix of the input. -/
theorem exists_c2FlagCode : ∃ K : OracleCode, ∀ p : Baire,
    c2FlagStream p ∈ K.evalStream p := by
  have hu1 : Primrec (fun v : ℕ => v.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hu2 : Primrec (fun v : ℕ => v.unpair.2) := Primrec.snd.comp Primrec.unpair
  have hb : Primrec₂ fun (k : ℕ) (_ : ℕ) => k / 2 + 1 :=
    (Primrec.succ.comp ((Primrec.nat_div.comp Primrec.id (Primrec.const 2)).comp
      Primrec.fst)).to₂
  have hl : Primrec fun v : ℕ => ofNat (List ℕ) v.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp hu2
  have hc : Primrec fun v : ℕ => v.unpair.1 % 2 + 1 :=
    Primrec.succ.comp (Primrec.nat_mod.comp hu1 (Primrec.const 2))
  have hhalf : Primrec fun v : ℕ => v.unpair.1 / 2 :=
    Primrec.nat_div.comp hu1 (Primrec.const 2)
  have hgetD : Primrec fun v : ℕ => (ofNat (List ℕ) v.unpair.2).getD (v.unpair.1 / 2) 0 :=
    (Primrec.list_getD 0).comp hl hhalf
  have h1 : PrimrecPred fun v : ℕ =>
      (ofNat (List ℕ) v.unpair.2).getD (v.unpair.1 / 2) 0 = v.unpair.1 % 2 + 1 :=
    PrimrecRel.comp Primrec.eq hgetD hc
  have hpredaux : PrimrecPred fun q : ℕ × ℕ =>
      0 < (q.2 - (q.1.unpair.1 % 2 + 1)) + ((q.1.unpair.1 % 2 + 1) - q.2) :=
    PrimrecRel.comp Primrec.nat_lt (Primrec.const 0)
      (Primrec.nat_add.comp
        (Primrec.nat_sub.comp Primrec.snd (hc.comp Primrec.fst))
        (Primrec.nat_sub.comp (hc.comp Primrec.fst) Primrec.snd))
  have hpred : Primrec₂ fun (v x : ℕ) => decide (0 <
      (x - (v.unpair.1 % 2 + 1)) + ((v.unpair.1 % 2 + 1) - x)) := by
    obtain ⟨_, hp⟩ := hpredaux
    exact Primrec₂.of_eq hp.to₂ fun v x => decide_eq_decide.mpr Iff.rfl
  have htake : Primrec fun v : ℕ => (ofNat (List ℕ) v.unpair.2).take (v.unpair.1 / 2) :=
    Primrec.list_take.comp hhalf hl
  have hall : Primrec fun v : ℕ =>
      ((ofNat (List ℕ) v.unpair.2).take (v.unpair.1 / 2)).all fun x =>
        decide (0 < (x - (v.unpair.1 % 2 + 1)) + ((v.unpair.1 % 2 + 1) - x)) :=
    primrec_list_all htake hpred
  have h2 : PrimrecPred fun v : ℕ =>
      (((ofNat (List ℕ) v.unpair.2).take (v.unpair.1 / 2)).all fun x =>
        decide (0 < (x - (v.unpair.1 % 2 + 1)) + ((v.unpair.1 % 2 + 1) - x))) = true :=
    PrimrecRel.comp Primrec.eq hall (Primrec.const true)
  obtain ⟨K, hK⟩ := exists_prefixPostCode hb
    (Primrec.ite (h1.and h2) (Primrec.const 1) (Primrec.const 0))
  refine ⟨K, fun p => mem_evalStream.mpr fun k => ?_⟩
  rw [hK p k]
  simp only [Nat.unpair_pair, Denumerable.ofNat_encode, Part.mem_some_iff]
  have hlen : k / 2 < k / 2 + 1 := Nat.lt_succ_self _
  rw [streamTake_getD p hlen, take_streamTake p (Nat.le_succ _)]
  -- align the list-scan condition with the pointwise one
  have hcond : ((streamTake p (k / 2)).all fun x =>
      decide (0 < (x - (k % 2 + 1)) + ((k % 2 + 1) - x))) = true ↔
      ∀ m < k / 2, p m ≠ k % 2 + 1 := by
    rw [List.all_eq_true]
    constructor
    · intro h m hm
      have hx : p m ∈ streamTake p (k / 2) :=
        List.mem_ofFn.mpr ⟨⟨m, hm⟩, rfl⟩
      have := h _ hx
      rw [decide_eq_true_eq] at this
      omega
    · intro h x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      rw [decide_eq_true_eq]
      have := h i i.isLt
      omega
  by_cases hcase : p (k / 2) = k % 2 + 1 ∧ ∀ m < k / 2, p m ≠ k % 2 + 1
  · rw [if_pos ⟨hcase.1, hcond.mpr hcase.2⟩, c2FlagStream, if_pos hcase]
  · rw [c2FlagStream, if_neg hcase]
    rcases Decidable.not_and_iff_not_or_not.mp hcase with h | h
    · rw [if_neg fun hc => h hc.1]
    · rw [if_neg fun hc => h (hcond.mp hc.2)]

/-- The first-removal flag code, extracted once from `exists_c2FlagCode` so that consumers
share a single combinator. Specified, not constructed — the documented atom pattern of
`OracleCode.pairCode`: the helper codes inside `exists_c2FlagCode` come from
`OracleCode.exists_prefixPostCode` (Prop-level), so only properties following from
`mem_evalStream_c2FlagCode` can be proved about it. -/
noncomputable def c2FlagCode : OracleCode := Classical.choose exists_c2FlagCode

/-- Specification of `c2FlagCode`: on any removal stream it produces the first-removal
flags. -/
theorem mem_evalStream_c2FlagCode (p : Baire) :
    c2FlagStream p ∈ c2FlagCode.evalStream p :=
  Classical.choose_spec exists_c2FlagCode p

/-- **`C₂ ≤sW LLPO`, as an explicit pair**: flag first removals — unique per parity, and
under the nonemptiness promise only one parity occurs — and pass the chosen point through
unchanged. -/
theorem isStrongReductionPair_c2_le_llpo :
    IsStrongReductionPair C₂ LLPO c2FlagCode .query := by
  intro w x hpx hdom
  obtain rfl : x = w := baireRep_names_iff.mp hpx
  obtain ⟨i₀, hi₀⟩ := hdom
  obtain ⟨hi₀le, hi₀norem⟩ := C₂.accepts_iff.mp hi₀
  -- the at-most-one promise: all nonzero flags share the surviving parity's complement,
  -- and first occurrences are unique
  have hone : ∀ a b, c2FlagStream x a ≠ 0 → c2FlagStream x b ≠ 0 → a = b := by
    intro a b ha hb
    obtain ⟨hpa, hmina⟩ := c2FlagStream_ne_zero ha
    obtain ⟨hpb, hminb⟩ := c2FlagStream_ne_zero hb
    have hpar : a % 2 = b % 2 := by
      by_contra hne
      -- both points removed, contradicting the surviving point
      obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.mp hi₀le
      · rcases Nat.mod_two_eq_zero_or_one a with h | h
        · exact hi₀norem (a / 2) (by rw [hpa, h])
        · have hb2 : b % 2 = 0 := by omega
          exact hi₀norem (b / 2) (by rw [hpb, hb2])
      · rcases Nat.mod_two_eq_zero_or_one a with h | h
        · have hb2 : b % 2 = 1 := by omega
          exact hi₀norem (b / 2) (by rw [hpb, hb2])
        · exact hi₀norem (a / 2) (by rw [hpa, h])
    have hdiv : a / 2 = b / 2 := by
      rcases Nat.lt_trichotomy (a / 2) (b / 2) with h | h | h
      · exact absurd (hpar ▸ hpa) (hminb _ h)
      · exact h
      · exact absurd (hpar ▸ hpb) (hmina _ h)
    omega
  have hmem := mem_evalStream_c2FlagCode x
  have hdom' : LLPO.Dom (c2FlagStream x) := by
    obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.mp hi₀le
    · exact ⟨(0 : ℕ), LLPO.accepts_iff.mpr ⟨hone, Or.inl ⟨rfl,
        c2FlagStream_even_zero_iff.mpr hi₀norem⟩⟩⟩
    · exact ⟨(1 : ℕ), LLPO.accepts_iff.mpr ⟨hone, Or.inr ⟨rfl,
        c2FlagStream_odd_zero_iff.mpr hi₀norem⟩⟩⟩
  refine ⟨c2FlagStream x, hmem, c2FlagStream x, baireRep_names_iff.mpr rfl, hdom',
    fun a y' hay' hacc => ?_⟩
  obtain ⟨-, hdisj⟩ := LLPO.accepts_iff.mp hacc
  refine ⟨a, by simp, y', hay', C₂.accepts_iff.mpr ?_⟩
  rcases hdisj with ⟨h0, hall⟩ | ⟨h1, hall⟩
  · exact ⟨by omega, by simpa [h0] using c2FlagStream_even_zero_iff.mp hall⟩
  · exact ⟨by omega, by simpa [h1] using c2FlagStream_odd_zero_iff.mp hall⟩

/-- `LLPO` reduces strongly to `C₂`. -/
theorem llpo_le_c2 : LLPO ≤sW C₂ :=
  strongReduction_iff_exists_reductionPair.mpr ⟨_, _, isStrongReductionPair_llpo_le_c2⟩

/-- `C₂` reduces strongly to `LLPO`. -/
theorem c2_le_llpo : C₂ ≤sW LLPO :=
  strongReduction_iff_exists_reductionPair.mpr ⟨_, _, isStrongReductionPair_c2_le_llpo⟩

/-- **The calibration**: closed choice on two points is strongly equivalent to `LLPO` —
the closed-set and omniscience presentations of finite binary choice agree. -/
theorem c2_equiv_llpo : C₂ ≡sW LLPO :=
  ⟨c2_le_llpo, llpo_le_c2⟩

end ComputableAnalysis
