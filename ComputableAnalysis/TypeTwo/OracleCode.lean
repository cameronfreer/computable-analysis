/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Computability.PartrecCode
import ComputableAnalysis.TypeTwo.Baire

/-!
# Oracle codes: syntax and coding

A finite syntax for Type-2 machines, modeled on `Nat.Partrec.Code` with one added
constructor `query` that reads a coordinate of the oracle stream. This file
provides the syntax only: the numeric encoding (`encodeCode`/`ofNatCode`), the
`Denumerable` and (hence) `Primcodable` instances, primitive recursiveness of the
constructors, and the strict monotonicity of the encoding used later for
well-founded recursion over codes.

Minimization uses mathlib's starting-point `rfind'` convention (a derived plain
`rfind` is provided with the evaluator), so that the recursion structure of
`Nat.Partrec.Code` transfers verbatim.

Code equality is syntactic (`DecidableEq`); extensional equality is only ever
stated through evaluation lemmas, never as a quotient.
-/

namespace ComputableAnalysis

/-- Code for oracle-relative partial recursive functions from ℕ to ℕ. The
`query` constructor reads one coordinate of the oracle stream. See
`OracleCode.eval` for the interpretation of the constructors. -/
inductive OracleCode : Type
  | zero : OracleCode
  | succ : OracleCode
  | left : OracleCode
  | right : OracleCode
  | query : OracleCode
  | pair : OracleCode → OracleCode → OracleCode
  | comp : OracleCode → OracleCode → OracleCode
  | prec : OracleCode → OracleCode → OracleCode
  | rfind' : OracleCode → OracleCode
  deriving DecidableEq

compile_inductive% OracleCode

namespace OracleCode

instance instInhabited : Inhabited OracleCode :=
  ⟨zero⟩

/-- An encoding of an `OracleCode` as a natural number: the five atoms take
`0`–`4`, and the four composite constructors are tagged by two bits above `5`. -/
def encodeCode : OracleCode → ℕ
  | zero => 0
  | succ => 1
  | left => 2
  | right => 3
  | query => 4
  | pair cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 5
  | comp cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg) + 1) + 5
  | prec cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 1 + 5
  | rfind' cf => 2 * (2 * encodeCode cf + 1) + 1 + 5

/-- Decode a natural number as an `OracleCode`, inverting `encodeCode`. -/
def ofNatCode : ℕ → OracleCode
  | 0 => zero
  | 1 => succ
  | 2 => left
  | 3 => right
  | 4 => query
  | n + 5 =>
    have hm : n.div2.div2 < n + 5 := by
      simp only [Nat.div2_val]
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : (Nat.unpair n.div2.div2).1 < n + 5 :=
      lt_of_le_of_lt (Nat.unpair_left_le _) hm
    have _m2 : (Nat.unpair n.div2.div2).2 < n + 5 :=
      lt_of_le_of_lt (Nat.unpair_right_le _) hm
    match n.bodd, n.div2.bodd with
    | false, false =>
      pair (ofNatCode (Nat.unpair n.div2.div2).1) (ofNatCode (Nat.unpair n.div2.div2).2)
    | false, true =>
      comp (ofNatCode (Nat.unpair n.div2.div2).1) (ofNatCode (Nat.unpair n.div2.div2).2)
    | true, false =>
      prec (ofNatCode (Nat.unpair n.div2.div2).1) (ofNatCode (Nat.unpair n.div2.div2).2)
    | true, true => rfind' (ofNatCode n.div2.div2)

private theorem encode_ofNatCode : ∀ n, encodeCode (ofNatCode n) = n
  | 0 => by simp [ofNatCode, encodeCode]
  | 1 => by simp [ofNatCode, encodeCode]
  | 2 => by simp [ofNatCode, encodeCode]
  | 3 => by simp [ofNatCode, encodeCode]
  | 4 => by simp [ofNatCode, encodeCode]
  | n + 5 => by
    have hm : n.div2.div2 < n + 5 := by
      simp only [Nat.div2_val]
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : (Nat.unpair n.div2.div2).1 < n + 5 :=
      lt_of_le_of_lt (Nat.unpair_left_le _) hm
    have _m2 : (Nat.unpair n.div2.div2).2 < n + 5 :=
      lt_of_le_of_lt (Nat.unpair_right_le _) hm
    have IH := encode_ofNatCode n.div2.div2
    have IH1 := encode_ofNatCode (Nat.unpair n.div2.div2).1
    have IH2 := encode_ofNatCode (Nat.unpair n.div2.div2).2
    conv_rhs => rw [← Nat.bit_bodd_div2 n, ← Nat.bit_bodd_div2 n.div2]
    simp only [ofNatCode.eq_6]
    cases n.bodd <;> cases n.div2.bodd <;>
      simp [encodeCode, IH, IH1, IH2, Nat.bit_val]

instance instDenumerable : Denumerable OracleCode :=
  Denumerable.mk'
    ⟨encodeCode, ofNatCode, fun c => by
        induction c <;> simp [encodeCode, ofNatCode, Nat.div2_val, *],
      encode_ofNatCode⟩

theorem encodeCode_eq : Encodable.encode = encodeCode :=
  rfl

theorem ofNatCode_eq : Denumerable.ofNat OracleCode = ofNatCode :=
  rfl

/-! ### Encoding bounds (for well-founded recursion over codes) -/

theorem encode_lt_pair (cf cg : OracleCode) :
    Encodable.encode cf < Encodable.encode (pair cf cg) ∧
      Encodable.encode cg < Encodable.encode (pair cf cg) := by
  simp only [encodeCode_eq, encodeCode]
  have h := Nat.mul_le_mul_right (Nat.pair cf.encodeCode cg.encodeCode)
    (by decide : 1 ≤ 2 * 2)
  rw [one_mul, mul_assoc] at h
  have h := lt_of_le_of_lt h (lt_add_of_pos_right _ (by decide : 0 < 5))
  exact ⟨lt_of_le_of_lt (Nat.left_le_pair _ _) h, lt_of_le_of_lt (Nat.right_le_pair _ _) h⟩

theorem encode_lt_comp (cf cg : OracleCode) :
    Encodable.encode cf < Encodable.encode (comp cf cg) ∧
      Encodable.encode cg < Encodable.encode (comp cf cg) := by
  have : Encodable.encode (pair cf cg) < Encodable.encode (comp cf cg) := by
    simp [encodeCode_eq, encodeCode]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

theorem encode_lt_prec (cf cg : OracleCode) :
    Encodable.encode cf < Encodable.encode (prec cf cg) ∧
      Encodable.encode cg < Encodable.encode (prec cf cg) := by
  have : Encodable.encode (pair cf cg) < Encodable.encode (prec cf cg) := by
    simp [encodeCode_eq, encodeCode]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

theorem encode_lt_rfind' (cf : OracleCode) :
    Encodable.encode cf < Encodable.encode (rfind' cf) := by
  simp only [encodeCode_eq, encodeCode]
  omega

/-! ### Primitive recursiveness of the constructors -/

section

open Primrec Encodable Denumerable

theorem primrec₂_pair : Primrec₂ pair :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double.comp <|
          nat_double.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat OracleCode).comp fst)
              (encode_iff.2 <| (Primrec.ofNat OracleCode).comp snd))
        (Primrec₂.const 5)

theorem primrec₂_comp : Primrec₂ comp :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double.comp <|
          nat_double_succ.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat OracleCode).comp fst)
              (encode_iff.2 <| (Primrec.ofNat OracleCode).comp snd))
        (Primrec₂.const 5)

theorem primrec₂_prec : Primrec₂ prec :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double_succ.comp <|
          nat_double.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat OracleCode).comp fst)
              (encode_iff.2 <| (Primrec.ofNat OracleCode).comp snd))
        (Primrec₂.const 5)

theorem primrec_rfind' : Primrec rfind' :=
  ofNat_iff.2 <|
    encode_iff.1 <|
      nat_add.comp
        (nat_double_succ.comp <| nat_double_succ.comp <|
          encode_iff.2 <| Primrec.ofNat OracleCode)
        (const 5)

-- The flexible linter is disabled as in mathlib's original proof of
-- `Nat.Partrec.Code.primrec_recOn'`, which this adapts.
set_option linter.flexible false in
/-- Recursion on `OracleCode` is primitive recursive (unbundled hypotheses).
Adapted from `Nat.Partrec.Code.primrec_recOn'` with the extra `query` atom. -/
theorem primrec_recOn' {α σ}
    [Primcodable α] [Primcodable σ] {c : α → OracleCode} (hc : Primrec c) {z : α → σ}
    (hz : Primrec z) {s : α → σ} (hs : Primrec s) {l : α → σ} (hl : Primrec l) {r : α → σ}
    (hr : Primrec r) {q : α → σ} (hq : Primrec q) {pr : α → OracleCode × OracleCode × σ × σ → σ}
    (hpr : Primrec₂ pr) {co : α → OracleCode × OracleCode × σ × σ → σ} (hco : Primrec₂ co)
    {pc : α → OracleCode × OracleCode × σ × σ → σ} (hpc : Primrec₂ pc)
    {rf : α → OracleCode × σ → σ} (hrf : Primrec₂ rf) :
    let PR (a) cf cg hf hg := pr a (cf, cg, hf, hg)
    let CO (a) cf cg hf hg := co a (cf, cg, hf, hg)
    let PC (a) cf cg hf hg := pc a (cf, cg, hf, hg)
    let RF (a) cf hf := rf a (cf, hf)
    let F (a : α) (c : OracleCode) : σ :=
      OracleCode.recOn c (z a) (s a) (l a) (r a) (q a) (PR a) (CO a) (PC a) (RF a)
    Primrec (fun a => F a (c a) : α → σ) := by
  intro _ _ _ _ F
  let G₁ : (α × List σ) × ℕ × ℕ → Option σ := fun p =>
    letI a := p.1.1; letI IH := p.1.2; letI n := p.2.1; letI m := p.2.2
    IH[m]?.bind fun s =>
    IH[m.unpair.1]?.bind fun s₁ =>
    IH[m.unpair.2]?.map fun s₂ =>
    cond n.bodd
      (cond n.div2.bodd (rf a (ofNat OracleCode m, s))
        (pc a (ofNat OracleCode m.unpair.1, ofNat OracleCode m.unpair.2, s₁, s₂)))
      (cond n.div2.bodd (co a (ofNat OracleCode m.unpair.1, ofNat OracleCode m.unpair.2, s₁, s₂))
        (pr a (ofNat OracleCode m.unpair.1, ofNat OracleCode m.unpair.2, s₁, s₂)))
  have : Primrec G₁ :=
    option_bind (list_getElem?.comp (snd.comp fst) (snd.comp snd)) <| .mk <|
    option_bind ((list_getElem?.comp (snd.comp fst)
      (fst.comp <| Primrec.unpair.comp (snd.comp snd))).comp fst) <| .mk <|
    option_map ((list_getElem?.comp (snd.comp fst)
      (snd.comp <| Primrec.unpair.comp (snd.comp snd))).comp <| fst.comp fst) <| .mk <|
    have a := fst.comp (fst.comp <| fst.comp <| fst.comp fst)
    have n := fst.comp (snd.comp <| fst.comp <| fst.comp fst)
    have m := snd.comp (snd.comp <| fst.comp <| fst.comp fst)
    have m₁ := fst.comp (Primrec.unpair.comp m)
    have m₂ := snd.comp (Primrec.unpair.comp m)
    have s := snd.comp (fst.comp fst)
    have s₁ := snd.comp fst
    have s₂ := snd
    (nat_bodd.comp n).cond
      ((nat_bodd.comp <| nat_div2.comp n).cond
        (hrf.comp a (((Primrec.ofNat OracleCode).comp m).pair s))
        (hpc.comp a (((Primrec.ofNat OracleCode).comp m₁).pair <|
          ((Primrec.ofNat OracleCode).comp m₂).pair <| s₁.pair s₂)))
      (Primrec.cond (nat_bodd.comp <| nat_div2.comp n)
        (hco.comp a (((Primrec.ofNat OracleCode).comp m₁).pair <|
          ((Primrec.ofNat OracleCode).comp m₂).pair <| s₁.pair s₂))
        (hpr.comp a (((Primrec.ofNat OracleCode).comp m₁).pair <|
          ((Primrec.ofNat OracleCode).comp m₂).pair <| s₁.pair s₂)))
  let G : α → List σ → Option σ := fun a IH =>
    IH.length.casesOn (some (z a)) fun n =>
    n.casesOn (some (s a)) fun n =>
    n.casesOn (some (l a)) fun n =>
    n.casesOn (some (r a)) fun n =>
    n.casesOn (some (q a)) fun n =>
    G₁ ((a, IH), n, n.div2.div2)
  have : Primrec₂ G := .mk <|
    nat_casesOn (list_length.comp snd) (option_some_iff.2 (hz.comp fst)) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (hs.comp (fst.comp fst))) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (hl.comp (fst.comp <| fst.comp fst))) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (hr.comp (fst.comp <| fst.comp <| fst.comp fst))) <| .mk <|
    nat_casesOn snd
      (option_some_iff.2 (hq.comp (fst.comp <| fst.comp <| fst.comp <| fst.comp fst))) <| .mk <|
    this.comp <|
      ((fst.pair snd).comp <| fst.comp <| fst.comp <| fst.comp <| fst.comp <| fst).pair <|
      snd.pair <| nat_div2.comp <| nat_div2.comp snd
  refine (nat_strong_rec (fun a n => F a (ofNat OracleCode n)) this.to₂ fun a n => ?_)
    |>.comp .id (encode_iff.2 hc) |>.of_eq fun a => by simp
  iterate 5 rcases n with - | n; · simp [ofNatCode_eq, ofNatCode]; rfl
  simp only [G]; rw [List.length_map, List.length_range]
  let m := n.div2.div2
  change G₁ ((a, (List.range (n + 5)).map fun n => F a (ofNat OracleCode n)), n, m)
    = some (F a (ofNat OracleCode (n + 5)))
  have hm : m < n + 5 := by
    simp only [m, Nat.div2_val]
    exact lt_of_le_of_lt
      (le_trans (Nat.div_le_self ..) (Nat.div_le_self ..))
      (Nat.succ_le_succ (Nat.le_add_right ..))
  have m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
  have m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
  simp [G₁, m, hm, m1, m2]
  rw [show ofNat OracleCode (n + 5) = ofNatCode (n + 5) from rfl]
  simp [ofNatCode]
  cases n.bodd <;> cases n.div2.bodd <;> rfl

/-- Recursion on `OracleCode` is primitive recursive.
Adapted from `Nat.Partrec.Code.primrec_recOn`. -/
theorem primrec_recOn {α σ}
    [Primcodable α] [Primcodable σ] {c : α → OracleCode} (hc : Primrec c) {z : α → σ}
    (hz : Primrec z) {s : α → σ} (hs : Primrec s) {l : α → σ} (hl : Primrec l) {r : α → σ}
    (hr : Primrec r) {q : α → σ} (hq : Primrec q)
    {pr : α → OracleCode → OracleCode → σ → σ → σ}
    (hpr : Primrec fun a : α × OracleCode × OracleCode × σ × σ =>
      pr a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {co : α → OracleCode → OracleCode → σ → σ → σ}
    (hco : Primrec fun a : α × OracleCode × OracleCode × σ × σ =>
      co a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {pc : α → OracleCode → OracleCode → σ → σ → σ}
    (hpc : Primrec fun a : α × OracleCode × OracleCode × σ × σ =>
      pc a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {rf : α → OracleCode → σ → σ}
    (hrf : Primrec fun a : α × OracleCode × σ => rf a.1 a.2.1 a.2.2) :
    let F (a : α) (c : OracleCode) : σ :=
      OracleCode.recOn c (z a) (s a) (l a) (r a) (q a) (pr a) (co a) (pc a) (rf a)
    Primrec fun a => F a (c a) :=
  primrec_recOn' hc hz hs hl hr hq
    (pr := fun a b => pr a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hpr)
    (co := fun a b => co a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hco)
    (pc := fun a b => pc a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hpc)
    (rf := fun a b => rf a b.1 b.2) (.mk hrf)

end

end OracleCode

end ComputableAnalysis
