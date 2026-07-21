/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.RepresentedSpace.FunctionSpace
import ComputableAnalysis.Metric.CauchyRepresentation

/-!
# The Cauchy-admissibility bridge

Every continuous map between Cauchy-presented metric spaces is **advice-realizable**: the
advice stream encodes a classical "modulus associate" (a table of ball-image containment
certificates), and a single fixed oracle code searches it by `OracleCode.rfind`. Consequently
the carrier of `funRep P.cauchyRep Q.cauchyRep` contains every continuous map.

The advice is produced by `Classical.choice`, so this is **not** a computable-point claim:
nothing here asserts that the resulting name of `f` is computable, only that continuity
suffices for membership in the function-space carrier. The realizer is the library's first
legitimately **partial** one — the `rfind` search converges on every valid name, and its
divergence off valid names is harmless because realization only quantifies over names.

## Main result

* `continuous_advisedRealizable` — every continuous `f : X → Y` between Cauchy-presented
  metric spaces has an advice-realizer for the fast Cauchy representations.
-/

namespace ComputableAnalysis

open OracleCode Metric ComputableMetricPresentation

section Helpers

variable {X Y : Type} [MetricSpace X] [MetricSpace Y]

/-! ### The mathematical layer: certificates -/

/-- A **containment certificate**: `Q.dense j` is a `(2⁻¹)^(n+1)`-approximation of `f`
uniformly on the doubled closed ball around `P.dense i` at input precision `k`. The
factor-2 margin makes the certificate transfer along any fast Cauchy name whose `k`-th
index is `i`. -/
private def Cert (P : ComputableMetricPresentation X) (Q : ComputableMetricPresentation Y)
    (f : X → Y) (n i k j : ℕ) : Prop :=
  ∀ z ∈ closedBall (P.dense i) (2 * ((2 : ℝ)⁻¹) ^ k),
    dist (Q.dense j) (f z) ≤ ((2 : ℝ)⁻¹) ^ (n + 1)

/-- **Certificate existence** along any name: continuity of `f` at the named point plus
density of `Q.dense` produce, for every output precision `n`, some input precision `k`
and target index `j` certified at the name's `k`-th index. -/
private theorem cert_exists (P : ComputableMetricPresentation X)
    (Q : ComputableMetricPresentation Y) {f : X → Y} (hf : Continuous f) {p : Baire}
    {x : X} (hp : P.NamesPoint p x) (n : ℕ) : ∃ k j : ℕ, Cert P Q f n (p k) k j := by
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.continuous_iff.mp hf x (((2 : ℝ)⁻¹) ^ (n + 2)) (by positivity)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < δ / 3)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  obtain ⟨j, hj⟩ := Q.denseRange.exists_dist_lt (f x)
    (by positivity : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ (n + 2))
  refine ⟨k, j, fun z hz => ?_⟩
  rw [mem_closedBall] at hz
  have hzx : dist z x < δ := by
    have ht := dist_triangle z (P.dense (p k)) x
    have hpk := hp k
    linarith
  have hfz : dist (f z) (f x) < ((2 : ℝ)⁻¹) ^ (n + 2) := hδ z hzx
  have ht2 := dist_triangle (Q.dense j) (f x) (f z)
  rw [dist_comm] at hj
  have hsym : dist (f x) (f z) = dist (f z) (f x) := dist_comm _ _
  have hpow : ((2 : ℝ)⁻¹) ^ (n + 2) + ((2 : ℝ)⁻¹) ^ (n + 2) = ((2 : ℝ)⁻¹) ^ (n + 1) := by
    rw [pow_succ]
    ring
  linarith

/-- **Certificate soundness** along any name: the named point lies in the doubled ball
around its own `k`-th index, so any certified `j` is a `(2⁻¹)^(n+1)`-approximation of
`f x`. -/
private theorem cert_sound {P : ComputableMetricPresentation X}
    {Q : ComputableMetricPresentation Y} {f : X → Y} {p : Baire} {x : X}
    (hp : P.NamesPoint p x) {n k j : ℕ} (hc : Cert P Q f n (p k) k j) :
    dist (Q.dense j) (f x) ≤ ((2 : ℝ)⁻¹) ^ (n + 1) := by
  refine hc x ?_
  rw [mem_closedBall, dist_comm]
  have hpk := hp k
  have hnn : (0 : ℝ) ≤ ((2 : ℝ)⁻¹) ^ k := by positivity
  linarith

/-! ### The advice stream: a classical modulus associate -/

open Classical in
/-- The advice value at output precision `n`, dense index `i`, input precision `k`:
`1 + j` for some certified `j` when a certificate exists, else `0`. Built by
`Classical.choice`; advice streams may be arbitrary. -/
private noncomputable def adviceAt (P : ComputableMetricPresentation X)
    (Q : ComputableMetricPresentation Y) (f : X → Y) (n i k : ℕ) : ℕ :=
  if h : ∃ j, Cert P Q f n i k j then h.choose + 1 else 0

/-- The advice stream: `adviceAt` read through the packed index
`Nat.pair n (Nat.pair i k)`. -/
private noncomputable def advice (P : ComputableMetricPresentation X)
    (Q : ComputableMetricPresentation Y) (f : X → Y) : Baire := fun m =>
  adviceAt P Q f m.unpair.1 m.unpair.2.unpair.1 m.unpair.2.unpair.2

/-- Reading the advice stream at a packed index recovers `adviceAt`. -/
private theorem advice_pack_eq {P : ComputableMetricPresentation X}
    {Q : ComputableMetricPresentation Y} {f : X → Y} (n i k : ℕ) :
    advice P Q f (Nat.pair n (Nat.pair i k)) = adviceAt P Q f n i k := by
  simp only [advice, Nat.unpair_pair]

/-- The advice is positive wherever a certificate exists. -/
private theorem advice_pack_pos {P : ComputableMetricPresentation X}
    {Q : ComputableMetricPresentation Y} {f : X → Y} {n i k : ℕ}
    (h : ∃ j, Cert P Q f n i k j) : 0 < advice P Q f (Nat.pair n (Nat.pair i k)) := by
  rw [advice_pack_eq, adviceAt, dif_pos h]
  exact Nat.succ_pos _

/-- A positive advice value decodes (via `· - 1`) to a certified index. -/
private theorem advice_pack_cert {P : ComputableMetricPresentation X}
    {Q : ComputableMetricPresentation Y} {f : X → Y} {n i k : ℕ}
    (h : 0 < advice P Q f (Nat.pair n (Nat.pair i k))) :
    Cert P Q f n i k (advice P Q f (Nat.pair n (Nat.pair i k)) - 1) := by
  rw [advice_pack_eq] at h ⊢
  by_cases hex : ∃ j, Cert P Q f n i k j
  · rw [adviceAt, dif_pos hex, Nat.add_sub_cancel]
    exact hex.choose_spec
  · rw [adviceAt, dif_neg hex] at h
    exact absurd h (lt_irrefl 0)

/-! ### The code layer -/

/-- The **α-query code**: on input `Nat.pair n k`, read the argument's `k`-th index off
the odd track, pack `(n, p k, k)`, and query the advice (even) track at the packed
index. Totally uniform in the oracle. -/
private theorem exists_alphaQueryCode :
    ∃ aq : OracleCode, ∀ (r : Baire) (n k : ℕ),
      aq.eval r (Nat.pair n k) =
        Part.some (r (2 * Nat.pair n (Nat.pair (r (2 * k + 1)) k))) := by
  obtain ⟨oddC, hodd⟩ := exists_ofNatFnCode (g := fun w => 2 * w.unpair.2 + 1)
    ((Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.unpair))
      (Primrec.const 1)).to_comp)
  obtain ⟨packC, hpack⟩ := exists_ofNatFnCode
    (g := fun v => 2 * Nat.pair v.unpair.1.unpair.1 (Nat.pair v.unpair.2 v.unpair.1.unpair.2))
    (by
      have h1 : Primrec fun v : ℕ => v.unpair.1 := Primrec.fst.comp Primrec.unpair
      have h2 : Primrec fun v : ℕ => v.unpair.2 := Primrec.snd.comp Primrec.unpair
      have hn : Primrec fun v : ℕ => v.unpair.1.unpair.1 :=
        Primrec.fst.comp (Primrec.unpair.comp h1)
      have hk : Primrec fun v : ℕ => v.unpair.1.unpair.2 :=
        Primrec.snd.comp (Primrec.unpair.comp h1)
      exact (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec₂.natPair.comp hn (Primrec₂.natPair.comp h2 hk))).to_comp)
  refine ⟨.comp .query (.comp packC (.pair OracleCode.id (.comp .query oddC))),
    fun r n k => ?_⟩
  have h1 : (OracleCode.comp .query oddC).eval r (Nat.pair n k)
      = Part.some (r (2 * k + 1)) := by
    rw [eval_comp_some (hodd r (Nat.pair n k)), eval_query]
    simp only [Nat.unpair_pair]
  have h2 := eval_pair_some (eval_id r (Nat.pair n k)) h1
  have h3 : (OracleCode.comp packC (.pair OracleCode.id (.comp .query oddC))).eval r
      (Nat.pair n k) = Part.some (2 * Nat.pair n (Nat.pair (r (2 * k + 1)) k)) := by
    rw [eval_comp_some h2, hpack]
    simp only [Nat.unpair_pair]
  rw [eval_comp_some h3, eval_query]

/-- **The realizer**, given any advice stream `α` that is positive exactly where packed
certificates exist and whose positive values decode (−1) to certified indices. The code:
per output coordinate `n`, `rfind`-search the least `k` with `α(pack n (p k) k) > 0`
(via the flipped query `1 − α(...)`, matching `rfind`'s search-for-zero convention),
then re-query and subtract 1. Convergence holds on valid names only — this is the
library's first legitimately partial realizer. -/
private theorem realizes_of_certOracle (P : ComputableMetricPresentation X)
    (Q : ComputableMetricPresentation Y) {f : X → Y} (hf : Continuous f) (α : Baire)
    (hpos : ∀ n i k : ℕ, (∃ j, Cert P Q f n i k j) → 0 < α (Nat.pair n (Nat.pair i k)))
    (hcert : ∀ n i k : ℕ, 0 < α (Nat.pair n (Nat.pair i k)) →
      Cert P Q f n i k (α (Nat.pair n (Nat.pair i k)) - 1)) :
    ∃ c : OracleCode, AdvisedRealizes P.cauchyRep Q.cauchyRep c α f := by
  obtain ⟨aq, haq⟩ := exists_alphaQueryCode
  obtain ⟨flipC, hflip⟩ := exists_ofNatFnCode (g := fun v => 1 - v)
    ((Primrec.nat_sub.comp (Primrec.const 1) Primrec.id).to_comp)
  obtain ⟨subC, hsub1⟩ := exists_ofNatFnCode (g := fun v => v - 1)
    ((Primrec.nat_sub.comp Primrec.id (Primrec.const 1)).to_comp)
  refine ⟨.comp subC (.comp aq (.pair OracleCode.id (OracleCode.rfind (.comp flipC aq)))),
    ?_⟩
  intro p x hp
  rw [P.cauchyRep_names_iff] at hp
  have hodd : ∀ k, Baire.interleave α p (2 * k + 1) = p k := Baire.interleave_odd α p
  have heven : ∀ m, Baire.interleave α p (2 * m) = α m := Baire.interleave_even α p
  -- the α-query value along the name
  have hA : ∀ n k : ℕ, aq.eval (Baire.interleave α p) (Nat.pair n k)
      = Part.some (α (Nat.pair n (Nat.pair (p k) k))) := by
    intro n k
    rw [haq, hodd, heven]
  -- the (total) search predicate value
  have hSC : ∀ n k : ℕ,
      (OracleCode.comp flipC aq).eval (Baire.interleave α p) (Nat.pair n k)
        = Part.some (1 - α (Nat.pair n (Nat.pair (p k) k))) := fun n k => by
    rw [eval_comp_some (hA n k), hflip]
  -- per-coordinate convergence to a certified index
  have key : ∀ n : ℕ, ∃ v : ℕ,
      (OracleCode.comp subC (.comp aq (.pair OracleCode.id
        (OracleCode.rfind (.comp flipC aq))))).eval (Baire.interleave α p) n
          = Part.some v ∧
      dist (Q.dense v) (f x) ≤ ((2 : ℝ)⁻¹) ^ n := by
    intro n
    let pred : ℕ → Bool := fun m => decide (1 - α (Nat.pair n (Nat.pair (p m) m)) = 0)
    have hpreddef : pred = fun m => decide (1 - α (Nat.pair n (Nat.pair (p m) m)) = 0) :=
      rfl
    have hrfeq : (OracleCode.rfind (.comp flipC aq)).eval (Baire.interleave α p) n
        = Nat.rfind (pred : ℕ →. Bool) := by
      rw [eval_rfind]
      congr 1
      funext m
      rw [hSC n m, PFun.coe_val]
      simp [hpreddef]
    obtain ⟨k, j, hkj⟩ := cert_exists P Q hf hp n
    have hposk : 0 < α (Nat.pair n (Nat.pair (p k) k)) := hpos n (p k) k ⟨j, hkj⟩
    have hpk : pred k = true := by
      simp only [hpreddef, decide_eq_true_eq]
      omega
    obtain ⟨k₀, hk₀, -⟩ := Nat.rfind_min' hpk
    have hrf : (OracleCode.rfind (.comp flipC aq)).eval (Baire.interleave α p) n
        = Part.some k₀ := Part.eq_some_iff.mpr (by rw [hrfeq]; exact hk₀)
    have hspec0 := Nat.rfind_spec hk₀
    rw [PFun.coe_val, Part.mem_some_iff] at hspec0
    have hpos₀ : 0 < α (Nat.pair n (Nat.pair (p k₀) k₀)) := by
      have h' := hspec0.symm
      simp only [hpreddef, decide_eq_true_eq] at h'
      omega
    have h1 := eval_pair_some (eval_id (Baire.interleave α p) n) hrf
    have h2 : (OracleCode.comp aq (.pair OracleCode.id
        (OracleCode.rfind (.comp flipC aq)))).eval (Baire.interleave α p) n
        = Part.some (α (Nat.pair n (Nat.pair (p k₀) k₀))) := by
      rw [eval_comp_some h1, hA]
    refine ⟨α (Nat.pair n (Nat.pair (p k₀) k₀)) - 1, ?_, ?_⟩
    · rw [eval_comp_some h2, hsub1]
    · have hd := cert_sound hp (hcert n (p k₀) k₀ hpos₀)
      have hstep : ((2 : ℝ)⁻¹) ^ (n + 1) ≤ ((2 : ℝ)⁻¹) ^ n := by
        have hnn : (0 : ℝ) ≤ ((2 : ℝ)⁻¹) ^ n := by positivity
        rw [pow_succ]
        linarith
      exact hd.trans hstep
  choose v hv hd using key
  refine ⟨v, mem_evalStream.mpr fun n => ?_, Q.cauchyRep_names_iff.mpr hd⟩
  rw [hv n]
  exact Part.mem_some _

end Helpers

/-! ### The Cauchy-admissibility bridge -/

/-- **Every continuous map between Cauchy-presented metric spaces has an
advice-realizer.** The advice is a classical modulus associate (certificate table), so
this carries no computable-point claim; the code is a single `rfind`-search realizer,
partial off valid names. Consequently the carrier of `funRep P.cauchyRep Q.cauchyRep`
contains all continuous maps. -/
theorem continuous_advisedRealizable {X Y : Type} [MetricSpace X] [MetricSpace Y]
    (P : ComputableMetricPresentation X) (Q : ComputableMetricPresentation Y)
    {f : X → Y} (hf : Continuous f) :
    ∃ (c : OracleCode) (q : Baire), AdvisedRealizes P.cauchyRep Q.cauchyRep c q f := by
  obtain ⟨c, hc⟩ := realizes_of_certOracle P Q hf (advice P Q f)
    (fun _ _ _ h => advice_pack_pos h) (fun _ _ _ h => advice_pack_cert h)
  exact ⟨c, advice P Q f, hc⟩

end ComputableAnalysis
