/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.CylinderValues
import ComputableAnalysis.TypeTwo.PrefixTable
import ComputableAnalysis.RepresentedSpace.ComputableMap
import ComputableAnalysis.Metric.RatCodeArith

/-!
# Pushforward of Cantor probability measures along computable maps

For a total map `f : Cantor → Cantor` with `ComputableMap cantorRep cantorRep f` (a
realizer converging on every *valid* Cantor name — not necessarily on every Baire
stream), the measurability bridge runs computable ⇒ continuous (per-coordinate finite
use of the realizer on encoded names) ⇒ measurable, and `pushforwardMeasure f hf μ` is
the classical image measure `μ.map f` as a probability measure.

The effective content is the unit 6 prefix table: the realizer of `f` is total on
Cantor (`TotalOnCantor`), its decoded map `streamFn` *is* `f`, and
`uniformPrefixTableSearch` returns, for each word `s`, a finite disjoint list of
same-length cylinders whose union is `f ⁻¹' cylinder s`
(`exists_pushforward_cylinder_table`), so the pushforward mass of `s` is a finite sum
of source masses. Since the search is partial recursive and total here, the table is
*computable* in `s`, which yields uniform computability of the pushforward in the
measure (`computableMap_pushforwardMeasure`): the realizer reads the table for `s`,
sums the input mass approximants of the table words at a bumped precision, and the
`k · 2⁻⁽ⁿ⁺ᵏ⁾ ≤ 2⁻ⁿ` estimate gives the rate.

**API note**: `OracleCode.exists_prefixPostCode` (unit 16) takes `Primrec` bound and
postprocessor hypotheses, but the table map runs an unbounded search and is only
`Computable`; the private `exists_prefixPostCode'` below is the same assembly with
`Computable` hypotheses (its proof only ever needed `exists_ofNatFnCode`, which takes
`Computable`). The code-level rational arithmetic (`addCode`, `sumCode`, …) comes from
`ComputableAnalysis/Metric/RatCodeArith.lean`; the estimate toolkit is still re-derived
privately here (it is `private` in `ComputableAnalysis/Metric/Real.lean` and
`ComputableAnalysis/Measure/Constructors.lean`) and will be consolidated in a later API
pass.
-/

open MeasureTheory

namespace ComputableAnalysis

open OracleCode Encodable Denumerable Function

/-! ### The canonical name of a Cantor point -/

/-- `encodeCantor x` is a valid `cantorRep` name of `x`. -/
private theorem names_encodeCantor (x : Cantor) : cantorRep.Names (encodeCantor x) x := by
  refine cantorRep_names_iff.mpr ⟨fun n => ?_, funext fun n => ?_⟩
  · simp only [encodeCantor_apply]
    split <;> omega
  · cases hxn : x n <;> simp [hxn]

/-! ### Computable ⇒ continuous ⇒ measurable -/

open Topology in
/-- **Continuity.** A map of Cantor space with a `cantorRep`-realizer is continuous:
each output coordinate is read from a converging evaluation on the encoded name, which
by finite use depends on only finitely many input coordinates, so each coordinate map
is locally constant. -/
theorem continuous_of_computableMap_cantor {f : Cantor → Cantor}
    (hf : ComputableMap cantorRep cantorRep f) : Continuous f := by
  obtain ⟨c, hc⟩ := hf
  refine continuous_pi fun i => continuous_iff_continuousAt.mpr fun x => ?_
  obtain ⟨q, hq, hqf⟩ := hc (encodeCantor x) x (names_encodeCantor x)
  obtain ⟨hqle, hxq⟩ := cantorRep_names_iff.mp hqf
  obtain ⟨u, hu⟩ := OracleCode.eval_eq_of_agree_on_use (OracleCode.mem_evalStream.mp hq i)
  have hnhds : {y : Cantor | ∀ j ∈ u, y j = x j} ∈ 𝓝 x := by
    refine IsOpen.mem_nhds ?_ fun _ _ => rfl
    have hset : {y : Cantor | ∀ j ∈ u, y j = x j}
        = ⋂ j ∈ u, (fun y : Cantor => y j) ⁻¹' {x j} := by
      ext y; simp
    rw [hset]
    exact isOpen_biInter_finset fun j _ =>
      (continuous_apply j).isOpen_preimage _ (isOpen_discrete _)
  have heq : (fun _ : Cantor => f x i) =ᶠ[𝓝 x] fun y => f y i := by
    refine Filter.eventually_of_mem hnhds fun y hy => ?_
    obtain ⟨q', hq', hq'f⟩ := hc (encodeCantor y) y (names_encodeCantor y)
    obtain ⟨hq'le, hyq'⟩ := cantorRep_names_iff.mp hq'f
    have hagree : ∀ j ∈ u, encodeCantor y j = encodeCantor x j := fun j hj => by
      rw [encodeCantor_apply, encodeCantor_apply, hy j hj]
    have hqq' : q' i = q i :=
      Part.mem_unique (OracleCode.mem_evalStream.mp hq' i) (hu (encodeCantor y) hagree)
    have h1 : f x i = (q i == 1) := by rw [hxq]
    have h2 : f y i = (q' i == 1) := by rw [hyq']
    change f x i = f y i
    rw [h1, h2, hqq']
  exact continuousAt_const.congr heq

/-- **Measurability.** A map of Cantor space with a `cantorRep`-realizer is measurable
(Borel of the product topology; continuity plus the opens-measurable Pi structure). -/
theorem measurable_of_computableMap_cantor {f : Cantor → Cantor}
    (hf : ComputableMap cantorRep cantorRep f) : Measurable f :=
  (continuous_of_computableMap_cantor hf).measurable

/-! ### The pushforward measure -/

/-- The pushforward of a Cantor probability measure along a computable map: the image
measure `μ.map f`, a probability measure since `f` is measurable
(`measurable_of_computableMap_cantor`). -/
noncomputable def pushforwardMeasure (f : Cantor → Cantor)
    (hf : ComputableMap cantorRep cantorRep f) (μ : ProbabilityMeasure Cantor) :
    ProbabilityMeasure Cantor :=
  ⟨μ.toMeasure.map f,
    Measure.isProbabilityMeasure_map (measurable_of_computableMap_cantor hf).aemeasurable⟩

/-! ### The prefix table of a realizer

The realizer of `f` converges on every valid Cantor name, so it is total on Cantor and
its decoded map `streamFn` is `f` itself; the unit 6 search then decomposes every
cylinder preimage as a finite disjoint union of cylinders. -/

/-- A `cantorRep`-realizer of a total map is total on Cantor: it converges
coordinatewise on every encoded name. -/
private theorem totalOnCantor_of_realizes {f : Cantor → Cantor} {c : OracleCode}
    (hc : Realizes cantorRep cantorRep c f) : c.TotalOnCantor := by
  intro x n
  obtain ⟨q, hq, -⟩ := hc (encodeCantor x) x (names_encodeCantor x)
  exact Part.dom_iff_mem.mpr ⟨q n, OracleCode.mem_evalStream.mp hq n⟩

/-- The decoded map of a `cantorRep`-realizer is the realized map: the output name has
values `≤ 1`, so the zero/positive decoder agrees with the `== 1` reading. -/
private theorem streamFn_eq_of_realizes {f : Cantor → Cantor} {c : OracleCode}
    (hc : Realizes cantorRep cantorRep c f) (htot : c.TotalOnCantor) :
    OracleCode.streamFn c htot = f := by
  funext x n
  obtain ⟨q, hq, hqf⟩ := hc (encodeCantor x) x (names_encodeCantor x)
  obtain ⟨hqle, hxq⟩ := cantorRep_names_iff.mp hqf
  have h1 : OracleCode.streamFn c htot x n = decide (0 < q n) :=
    OracleCode.streamFn_apply htot x (OracleCode.mem_evalStream.mp hq n)
  have h2 : f x n = (q n == 1) := by rw [hxq]
  rw [h1, h2]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hqle n) with h | h <;> simp [h]

/-- The cylinder-preimage law of the search table, transported from `streamFn` to the
realized map `f`. -/
private theorem preimage_cylinder_eq {f : Cantor → Cantor} {c : OracleCode}
    {htot : c.TotalOnCantor} (hstream : OracleCode.streamFn c htot = f) {s : List Bool}
    {m : ℕ} {T : List (List Bool)}
    (h : (m, T) ∈ OracleCode.uniformPrefixTableSearch c s) :
    f ⁻¹' (cylinder s : Set Cantor) = ⋃ t ∈ T, (cylinder t : Set Cantor) := by
  rw [← hstream]
  exact OracleCode.uniformPrefixTableSearch_preimage c s htot h

/-- A list-indexed cylinder union equals the union over the list's finset. -/
private theorem biUnion_toFinset (T : List (List Bool)) :
    ⋃ t ∈ T.toFinset, (cylinder t : Set Cantor) = ⋃ t ∈ T, (cylinder t : Set Cantor) := by
  ext x
  simp

/-- The pairwise-disjointness of table cylinders, packaged on the list's finset. -/
private theorem pairwise_disjoint_toFinset {c : OracleCode} {s : List Bool} {m : ℕ}
    {T : List (List Bool)} (h : (m, T) ∈ OracleCode.uniformPrefixTableSearch c s) :
    (↑T.toFinset : Set (List Bool)).Pairwise
      (Disjoint on fun t => (cylinder t : Set Cantor)) := by
  intro t ht t' ht' hne
  exact OracleCode.uniformPrefixTableSearch_disjoint c s h
    (List.mem_toFinset.mp (Finset.mem_coe.mp ht))
    (List.mem_toFinset.mp (Finset.mem_coe.mp ht')) hne

/-- The pushforward mass of a cylinder decomposed by a finite disjoint cylinder cover
of its preimage: `Measure.map_apply` plus finite additivity. -/
private theorem cylMass_pushforwardMeasure_eq_sum {f : Cantor → Cantor}
    (hf : ComputableMap cantorRep cantorRep f) {s : List Bool} {T : Finset (List Bool)}
    (hpre : f ⁻¹' (cylinder s : Set Cantor) = ⋃ t ∈ T, (cylinder t : Set Cantor))
    (hdisj : (T : Set (List Bool)).Pairwise
      (Disjoint on fun t => (cylinder t : Set Cantor)))
    (μ : ProbabilityMeasure Cantor) :
    cylMass (pushforwardMeasure f hf μ) s = ∑ t ∈ T, cylMass μ t := by
  have hmap : (pushforwardMeasure f hf μ).toMeasure (cylinder s)
      = μ.toMeasure (f ⁻¹' (cylinder s : Set Cantor)) := by
    change (μ.toMeasure.map f) (cylinder s) = _
    exact Measure.map_apply (measurable_of_computableMap_cantor hf)
      (measurableSet_cylinder s)
  simp only [cylMass]
  rw [hmap, hpre, measure_biUnion_finset hdisj fun t _ => measurableSet_cylinder t,
    ENNReal.toReal_sum fun t _ => measure_ne_top _ _]

/-- The pushforward mass as a *list* sum over a search table (the form the realizer
computes with). -/
private theorem cylMass_pushforwardMeasure_eq_listSum {f : Cantor → Cantor}
    (hf : ComputableMap cantorRep cantorRep f) {c : OracleCode} {htot : c.TotalOnCantor}
    (hstream : OracleCode.streamFn c htot = f) {s : List Bool} {m : ℕ}
    {T : List (List Bool)} (h : (m, T) ∈ OracleCode.uniformPrefixTableSearch c s)
    (μ : ProbabilityMeasure Cantor) :
    cylMass (pushforwardMeasure f hf μ) s = (T.map (cylMass μ)).sum := by
  rw [cylMass_pushforwardMeasure_eq_sum hf
      (by rw [biUnion_toFinset]; exact preimage_cylinder_eq hstream h)
      (pairwise_disjoint_toFinset h) μ,
    List.sum_toFinset _ (OracleCode.uniformPrefixTableSearch_nodup c s h)]

/-- **Prefix-table mass formula.** The preimage of a cylinder under a computable map is
a finite disjoint union of cylinders (read off `uniformPrefixTableSearch` on a realizer
of `f`), so the pushforward mass of the cylinder is the finite sum of the source masses
of the table words, uniformly in the measure. -/
theorem exists_pushforward_cylinder_table {f : Cantor → Cantor}
    (hf : ComputableMap cantorRep cantorRep f) (s : List Bool) :
    ∃ T : Finset (List Bool),
      (f ⁻¹' (cylinder s : Set Cantor) = ⋃ t ∈ T, (cylinder t : Set Cantor)) ∧
      (T : Set (List Bool)).Pairwise (Disjoint on fun t => (cylinder t : Set Cantor)) ∧
      ∀ μ, cylMass (pushforwardMeasure f hf μ) s = ∑ t ∈ T, cylMass μ t := by
  obtain ⟨c, hcr⟩ := id hf
  have htot := totalOnCantor_of_realizes hcr
  have hstream := streamFn_eq_of_realizes hcr htot
  obtain ⟨⟨m, T⟩, hmem⟩ := Part.dom_iff_mem.mp
    (OracleCode.uniformPrefixTableSearch_dom c s htot)
  refine ⟨T.toFinset, ?_, pairwise_disjoint_toFinset hmem, fun μ => ?_⟩
  · rw [biUnion_toFinset]
    exact preimage_cylinder_eq hstream hmem
  · rw [cylMass_pushforwardMeasure_eq_listSum hf hstream hmem μ,
      List.sum_toFinset _ (OracleCode.uniformPrefixTableSearch_nodup c s hmem)]

/-! ### Word decoding (private duplicate)

Re-derived from the private sections of `Metric/Real.lean` and
`Measure/Constructors.lean`; consolidation is deferred to a later API pass. -/

section WordDecoding

/-- Decode a coordinate as the (default-`[]`) binary word it encodes. -/
private def wordOf (e : ℕ) : List Bool := (decode (α := List Bool) e).getD []

private theorem primrec_wordOf : Primrec wordOf :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

private theorem wordOf_encode (s : List Bool) : wordOf (encode s) = s := by
  simp [wordOf]

end WordDecoding

section EstimateToolkit

private theorem realNames_iff {p : Baire} {x : ℝ} :
    realRep.Names p x ↔
      ∀ n : ℕ, |((ratOfCode (p n) : ℚ) : ℝ) - x| ≤ (2 : ℝ)⁻¹ ^ n := by
  refine Iff.trans realPresentation.cauchyRep_names_iff ?_
  constructor
  · intro h n
    have hn := h n
    rw [Real.dist_eq] at hn
    exact hn
  · intro h n
    rw [Real.dist_eq]
    exact h n

/-- Extracting a coordinate from a decoded stream prefix. -/
private theorem streamTake_getD (p : Baire) {j m : ℕ} (h : j < m) :
    (streamTake p m).getD j 0 = p j := by
  rw [List.getD_eq_getElem _ _ (by rw [length_streamTake]; exact h), getElem_streamTake]

/-- The precision bump: `k · 2⁻⁽ⁿ⁺ᵏ⁾ ≤ 2⁻ⁿ`, from `k < 2 ^ k`. -/
private theorem bump (k n : ℕ) : (k : ℝ) * (2 : ℝ)⁻¹ ^ (n + k) ≤ (2 : ℝ)⁻¹ ^ n := by
  have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  have h1 : (k : ℝ) * (2 : ℝ)⁻¹ ^ k ≤ 1 := by
    rw [inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact hk
  calc (k : ℝ) * (2 : ℝ)⁻¹ ^ (n + k)
      = ((k : ℝ) * (2 : ℝ)⁻¹ ^ k) * (2 : ℝ)⁻¹ ^ n := by rw [pow_add]; ring
    _ ≤ 1 * (2 : ℝ)⁻¹ ^ n := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (2 : ℝ)⁻¹ ^ n := one_mul _

/-- Casting a rational list sum to the reals, termwise. -/
private theorem ratCast_listSum (l : List ℚ) :
    ((l.sum : ℚ) : ℝ) = (l.map fun q : ℚ => (q : ℝ)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Termwise triangle inequality for list sums. -/
private theorem abs_listSum_sub_listSum_le {α : Type*} (g h : α → ℝ) :
    ∀ L : List α, |(L.map g).sum - (L.map h).sum| ≤ (L.map fun t => |g t - h t|).sum
  | [] => by simp
  | a :: L => by
    simp only [List.map_cons, List.sum_cons]
    calc |g a + (L.map g).sum - (h a + (L.map h).sum)|
        = |(g a - h a) + ((L.map g).sum - (L.map h).sum)| := by
          congr 1
          ring
      _ ≤ |g a - h a| + |(L.map g).sum - (L.map h).sum| := abs_add_le _ _
      _ ≤ |g a - h a| + (L.map fun t => |g t - h t|).sum := by
          have := abs_listSum_sub_listSum_le g h L
          linarith

/-- A list sum of uniformly bounded terms is bounded by length times the bound. -/
private theorem listSum_le_length_mul {α : Type*} {u : α → ℝ} {c : ℝ} :
    ∀ L : List α, (∀ t ∈ L, u t ≤ c) → (L.map u).sum ≤ (L.length : ℝ) * c
  | [] => fun _ => by simp
  | a :: L => fun hall => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 : u a ≤ c := hall a (by simp)
    have h2 := listSum_le_length_mul L fun t ht => hall t (by simp [ht])
    push_cast
    linarith

/-- The maximum of a list of naturals (`foldr max 0`). -/
private def listMax (l : List ℕ) : ℕ := l.foldr max 0

private theorem le_listMax {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ listMax l := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · exact le_max_left _ _
    · exact (ih h').trans (le_max_right _ _)

private theorem primrec_listMax : Primrec listMax :=
  (Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun _ => rfl

end EstimateToolkit

/-! ### The pushforward realizer -/

section PushforwardRealizer

/-- Prefix length the pushforward realizer needs for the table `L` at precision `n`:
one past the largest input read index `Nat.pair (encode t) (n + L.length)`. -/
private def pushBoundKernel (L : List (List Bool)) (n : ℕ) : ℕ :=
  listMax (L.map fun t => Nat.pair (encode t) (n + L.length)) + 1

private theorem primrec₂_pushBoundKernel : Primrec₂ pushBoundKernel := by
  unfold pushBoundKernel
  exact (Primrec.succ.comp (primrec_listMax.comp (Primrec.list_map Primrec.fst
    (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.snd)
      (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst)
        (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)))).to₂))).to₂

/-- Oracle-free postprocessor of the pushforward realizer: sum, over the table words,
the input mass approximants read from the prefix `P` at the bumped precision. -/
private def pushPostKernel (L : List (List Bool)) (n : ℕ) (P : List ℕ) : ℕ :=
  sumCode (L.map fun t => P.getD (Nat.pair (encode t) (n + L.length)) 0)

private theorem primrec_pushPostKernel :
    Primrec fun v : (List (List Bool) × ℕ) × List ℕ => pushPostKernel v.1.1 v.1.2 v.2 := by
  unfold pushPostKernel
  exact primrec_sumCode.comp (Primrec.list_map (Primrec.fst.comp Primrec.fst)
    ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst)
      (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.snd)
        (Primrec.nat_add.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.list_length.comp
            (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))).to₂)

/-- Every read index of the postprocessor lies below the bound. -/
private theorem read_lt_pushBoundKernel {L : List (List Bool)} {t : List Bool}
    (ht : t ∈ L) (n : ℕ) :
    Nat.pair (encode t) (n + L.length) < pushBoundKernel L n :=
  Nat.lt_succ_of_le (le_listMax (List.mem_map.mpr ⟨t, ht, rfl⟩))

/-- The uniform prefix table as a *computable total function* of the word: the search
is partial recursive and, on a code total on Cantor, everywhere convergent. -/
private theorem exists_computable_table {c : OracleCode} (htot : c.TotalOnCantor) :
    ∃ tbl : List Bool → ℕ × List (List Bool), Computable tbl ∧
      ∀ s : List Bool, tbl s ∈ OracleCode.uniformPrefixTableSearch c s := by
  have hpart : Partrec fun s : List Bool => OracleCode.uniformPrefixTableSearch c s :=
    OracleCode.uniformPrefixTableSearch_partrec.comp (Computable.const c) Computable.id
  exact ⟨fun s => (OracleCode.uniformPrefixTableSearch c s).get
      (OracleCode.uniformPrefixTableSearch_dom c s htot),
    hpart.of_eq_tot fun s => Part.get_mem _, fun s => Part.get_mem _⟩

/-- The head-adaptive finite-use bridge of unit 16 with **`Computable`** (rather than
`Primrec`) bound and postprocessor. The proof is the assembly of
`OracleCode.exists_prefixPostCode`, which only ever needed `exists_ofNatFnCode` — and
that takes `Computable`. Needed because the table map runs an unbounded search and is
computable but not primitive recursive. -/
private theorem exists_prefixPostCode' {b : ℕ → ℕ → ℕ} {g : ℕ → ℕ}
    (hb : Computable₂ b) (hg : Computable g) :
    ∃ c : OracleCode, ∀ (F : Baire) (n : ℕ),
      c.eval F n = Part.some (g (Nat.pair n (encode (streamTake F (b n (F 0)))))) := by
  obtain ⟨t, ht⟩ := OracleCode.exists_takeCode
  obtain ⟨B, hB⟩ := OracleCode.exists_ofNatFnCode (g := fun v => b v.unpair.1 v.unpair.2)
    (hb.comp (Computable.fst.comp Computable.unpair) (Computable.snd.comp Computable.unpair))
  obtain ⟨G, hG⟩ := OracleCode.exists_ofNatFnCode hg
  refine ⟨.comp G (.pair OracleCode.id (.comp t (.comp B
    (.pair OracleCode.id (.comp .query .zero))))), fun F n => ?_⟩
  have h0 : (OracleCode.comp .query .zero).eval F n = Part.some (F 0) :=
    (OracleCode.eval_comp_some rfl).trans (OracleCode.eval_query F 0)
  have hbc : (OracleCode.comp B (.pair OracleCode.id (.comp .query .zero))).eval F n
      = Part.some (b n (F 0)) := by
    rw [OracleCode.eval_comp_some (OracleCode.eval_pair_some (OracleCode.eval_id F n) h0), hB]
    simp
  rw [OracleCode.eval_comp_some (OracleCode.eval_pair_some (OracleCode.eval_id F n)
    (OracleCode.eval_comp_some hbc ▸ ht F (b n (F 0)))), hG]

/-- **Uniform computability of the pushforward in the measure.** For a fixed computable
`f`, one oracle code sends every `cantorMeasureRep` name of `μ` to a name of the
pushforward: the output component for the word `s` at precision `n` reads the (computable)
prefix table `T_s`, sums the input approximants of the table words at the bumped
precision `n + |T_s|`, and `|T_s| · 2⁻⁽ⁿ⁺|T_s|⁾ ≤ 2⁻ⁿ` gives the rate. -/
theorem computableMap_pushforwardMeasure {f : Cantor → Cantor}
    (hf : ComputableMap cantorRep cantorRep f) :
    ComputableMap cantorMeasureRep cantorMeasureRep (pushforwardMeasure f hf) := by
  obtain ⟨c, hcr⟩ := id hf
  have htot := totalOnCantor_of_realizes hcr
  have hstream := streamFn_eq_of_realizes hcr htot
  obtain ⟨tbl, htblc, htblmem⟩ := exists_computable_table htot
  have hb : Computable₂ fun v _h : ℕ =>
      pushBoundKernel (tbl (wordOf v.unpair.1)).2 v.unpair.2 :=
    (primrec₂_pushBoundKernel.to_comp.comp
      (Computable.snd.comp (htblc.comp (primrec_wordOf.comp primrec_unpairFst).to_comp))
      primrec_unpairSnd.to_comp).comp Computable.fst
  have hg : Computable fun w : ℕ =>
      pushPostKernel (tbl (wordOf w.unpair.1.unpair.1)).2 w.unpair.1.unpair.2
        (ofNat (List ℕ) w.unpair.2) :=
    primrec_pushPostKernel.to_comp.comp
      ((Computable.pair
        (Computable.snd.comp (htblc.comp
          (primrec_wordOf.comp (primrec_unpairFst.comp primrec_unpairFst)).to_comp))
        (primrec_unpairSnd.comp primrec_unpairFst).to_comp).pair
        (((Primrec.ofNat (List ℕ)).comp primrec_unpairSnd).to_comp))
  obtain ⟨e, he⟩ := exists_prefixPostCode' hb hg
  refine ⟨e, Realizes.of_computes he fun F μ hFμ => ?_⟩
  have hM : MeasureNames F μ := cantorMeasureRep_names_iff.mp hFμ
  refine cantorMeasureRep_names_iff.mpr fun s => ?_
  refine Representation.subtype_names_iff.mpr (realNames_iff.mpr fun n => ?_)
  simp only [Nat.unpair_pair, ofNat_encode, wordOf_encode]
  have hread : ((tbl s).2.map fun t =>
      (streamTake F (pushBoundKernel (tbl s).2 n)).getD
        (Nat.pair (encode t) (n + (tbl s).2.length)) 0)
      = (tbl s).2.map fun t => F (Nat.pair (encode t) (n + (tbl s).2.length)) :=
    List.map_congr_left fun t ht => streamTake_getD F (read_lt_pushBoundKernel ht n)
  have hcast : ((ratOfCode (pushPostKernel (tbl s).2 n
      (streamTake F (pushBoundKernel (tbl s).2 n))) : ℚ) : ℝ)
      = ((tbl s).2.map fun t =>
          ((ratOfCode (F (Nat.pair (encode t) (n + (tbl s).2.length))) : ℚ) : ℝ)).sum := by
    simp only [pushPostKernel]
    rw [hread, ratOfCode_sumCode, ratCast_listSum, List.map_map, List.map_map]
    rfl
  have hval : ((cylMass01 (pushforwardMeasure f hf μ) s : ℝ))
      = ((tbl s).2.map (cylMass μ)).sum :=
    cylMass_pushforwardMeasure_eq_listSum hf hstream (htblmem s) μ
  have hest : ∀ t ∈ (tbl s).2,
      |((ratOfCode (F (Nat.pair (encode t) (n + (tbl s).2.length))) : ℚ) : ℝ)
        - cylMass μ t| ≤ (2 : ℝ)⁻¹ ^ (n + (tbl s).2.length) := fun t _ =>
    realNames_iff.mp (Representation.subtype_names_iff.mp (hM t)) (n + (tbl s).2.length)
  calc |((ratOfCode (pushPostKernel (tbl s).2 n
        (streamTake F (pushBoundKernel (tbl s).2 n))) : ℚ) : ℝ)
        - ((cylMass01 (pushforwardMeasure f hf μ) s : ℝ))|
      = |((tbl s).2.map fun t =>
            ((ratOfCode (F (Nat.pair (encode t) (n + (tbl s).2.length))) : ℚ) : ℝ)).sum
          - ((tbl s).2.map (cylMass μ)).sum| := by rw [hcast, hval]
    _ ≤ ((tbl s).2.map fun t =>
          |((ratOfCode (F (Nat.pair (encode t) (n + (tbl s).2.length))) : ℚ) : ℝ)
            - cylMass μ t|).sum := abs_listSum_sub_listSum_le _ _ _
    _ ≤ ((tbl s).2.length : ℝ) * (2 : ℝ)⁻¹ ^ (n + (tbl s).2.length) :=
        listSum_le_length_mul _ hest
    _ ≤ (2 : ℝ)⁻¹ ^ n := bump (tbl s).2.length n

end PushforwardRealizer

/-! ### Composition -/

/-- **Composition law.** Pushing forward along `f` then `g` is pushing forward along
`g ∘ f` (with the composite realizer `hg.comp hf`): `Measure.map_map` under the
probability-measure subtype. -/
theorem pushforwardMeasure_comp {f g : Cantor → Cantor} {μ : ProbabilityMeasure Cantor}
    (hf : ComputableMap cantorRep cantorRep f)
    (hg : ComputableMap cantorRep cantorRep g) :
    pushforwardMeasure g hg (pushforwardMeasure f hf μ) =
      pushforwardMeasure (g ∘ f) (hg.comp hf) μ := by
  refine ProbabilityMeasure.toMeasure_injective ?_
  change (μ.toMeasure.map f).map g = μ.toMeasure.map (g ∘ f)
  exact Measure.map_map (measurable_of_computableMap_cantor hg)
    (measurable_of_computableMap_cantor hf)

end ComputableAnalysis
