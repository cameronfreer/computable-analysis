/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.TypeTwo.OracleCode

/-!
# Oracle codes: evaluation

The coordinatewise Type-2 primitive: `OracleCode.eval c p : ℕ →. ℕ` evaluates the
code `c` against the oracle stream `p : Baire`. The `query` constructor reads one
oracle coordinate (`eval_query` is query soundness); the remaining constructors
evaluate exactly as in `Nat.Partrec.Code.eval`, with minimization in mathlib's
starting-point `rfind'` convention (plain `rfind` is derived).

`ofPartrecCode` embeds oracle-free codes, with evaluation preserved
(`eval_ofPartrecCode`); `const`, `id`, and `curry` transfer verbatim.

Everything here is uniform in the oracle: one code is evaluated against every
stream. No totalized stream operator appears in this file; the stream layer is
introduced after bounded simulation and continuity.
-/

namespace ComputableAnalysis

namespace OracleCode

/-- Evaluation of an oracle code against an oracle stream, coordinatewise on ℕ.
`query` returns the queried oracle coordinate; the other constructors follow
`Nat.Partrec.Code.eval`. -/
def eval (c : OracleCode) (p : Baire) : ℕ →. ℕ :=
  match c with
  | zero => pure 0
  | succ => fun n => Part.some (n + 1)
  | left => fun n => Part.some n.unpair.1
  | right => fun n => Part.some n.unpair.2
  | query => fun n => Part.some (p n)
  | pair cf cg => fun n => Nat.pair <$> cf.eval p n <*> cg.eval p n
  | comp cf cg => fun n => cg.eval p n >>= cf.eval p
  | prec cf cg =>
    Nat.unpaired fun a n =>
      n.rec (cf.eval p a) fun y IH => do
        let i ← IH
        cg.eval p (Nat.pair a (Nat.pair y i))
  | rfind' cf =>
    Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun x => x = 0) <$> cf.eval p (Nat.pair a (n + m))).map (· + m)

@[simp]
theorem eval_zero (p : Baire) : zero.eval p = pure 0 :=
  rfl

@[simp]
theorem eval_succ (p : Baire) (n : ℕ) : succ.eval p n = Part.some (n + 1) :=
  rfl

@[simp]
theorem eval_left (p : Baire) (n : ℕ) : left.eval p n = Part.some n.unpair.1 :=
  rfl

@[simp]
theorem eval_right (p : Baire) (n : ℕ) : right.eval p n = Part.some n.unpair.2 :=
  rfl

/-- Query soundness: the `query` instruction returns the queried oracle value. -/
@[simp]
theorem eval_query (p : Baire) (n : ℕ) : query.eval p n = Part.some (p n) :=
  rfl

@[simp]
theorem eval_pair (cf cg : OracleCode) (p : Baire) (n : ℕ) :
    (pair cf cg).eval p n = Nat.pair <$> cf.eval p n <*> cg.eval p n :=
  rfl

/-- `Part.bind_some` stated at the `PFun` type. Since Lean 4.34 the elaborator no longer
unfolds `α →. β` to `α → Part β` at `implicit` transparency, so `Part.bind_some` itself no
longer matches goals whose continuation is a partial function — every code-assembly step below
goes through this instead. -/
theorem some_bind_pfun (a : ℕ) (f : ℕ →. ℕ) :
    (Part.some a >>= f) = f a := Part.bind_some a f

/-- The same bridge with the continuation at the plain function type. Both forms are needed:
`rw` matches syntactically, and since Lean 4.34 `ℕ →. ℕ` and `ℕ → Part ℕ` are no longer
interchangeable at that level, so a site's shape decides which one applies. -/
theorem some_bind_fun (a : ℕ) (f : ℕ → Part ℕ) :
    (Part.some a >>= f) = f a := Part.bind_some a f

/-- The `.bind`-spelled form of the same bridge, for goals `simp` has already normalized away
from `>>=`. -/
theorem bind_some_pfun (a : ℕ) (f : ℕ →. ℕ) :
    (Part.some a).bind f = f a := Part.bind_some a f

@[simp]
theorem eval_comp (cf cg : OracleCode) (p : Baire) (n : ℕ) :
    (comp cf cg).eval p n = cg.eval p n >>= cf.eval p :=
  rfl

/-- Code-assembly step: composing past a converged inner evaluation. -/
theorem eval_comp_some {cf cg : OracleCode} {p : Baire} {n a : ℕ}
    (h : cg.eval p n = Part.some a) : (comp cf cg).eval p n = cf.eval p a := by
  rw [eval_comp, h, some_bind_pfun]

/-- Code-assembly step: pairing two converged evaluations. -/
theorem eval_pair_some {cf cg : OracleCode} {p : Baire} {n a b : ℕ}
    (hf : cf.eval p n = Part.some a) (hg : cg.eval p n = Part.some b) :
    (pair cf cg).eval p n = Part.some (Nat.pair a b) := by
  rw [eval_pair, hf, hg]
  simp [Seq.seq]

/-- Evaluation of `prec` in the base case. -/
@[simp]
theorem eval_prec_zero (cf cg : OracleCode) (p : Baire) (a : ℕ) :
    (prec cf cg).eval p (Nat.pair a 0) = cf.eval p a := by
  rw [eval, Nat.unpaired, Nat.unpair_pair]
  rw [Nat.rec_zero]

/-- Evaluation of `prec` in the successor case. -/
theorem eval_prec_succ (cf cg : OracleCode) (p : Baire) (a k : ℕ) :
    (prec cf cg).eval p (Nat.pair a (k + 1)) =
      do {let ih ← (prec cf cg).eval p (Nat.pair a k); cg.eval p (Nat.pair a (Nat.pair k ih))} := by
  rw [eval, Nat.unpaired, Part.bind_eq_bind, Nat.unpair_pair]
  simp

theorem eval_rfind' (cf : OracleCode) (p : Baire) (a m : ℕ) :
    (rfind' cf).eval p (Nat.pair a m) =
      (Nat.rfind fun n => (fun x => x = 0) <$> cf.eval p (Nat.pair a (n + m))).map (· + m) := by
  rw [eval, Nat.unpaired, Nat.unpair_pair]

/-! ### Derived codes: constants, identity, currying, plain minimization -/

/-- A code for the constant function with value `n`. -/
protected def const : ℕ → OracleCode
  | 0 => zero
  | n + 1 => comp succ (OracleCode.const n)

theorem const_inj : ∀ {n₁ n₂ : ℕ}, OracleCode.const n₁ = OracleCode.const n₂ → n₁ = n₂
  | 0, 0, _ => rfl
  | n₁ + 1, n₂ + 1, h => by
    dsimp [OracleCode.const] at h
    injection h with h₁ h₂
    simp only [const_inj h₂]

/-- A code for the identity function. -/
protected def id : OracleCode :=
  pair left right

/-- Given a code `c` taking a pair as input, a code using `n` as the first
component of that pair. -/
def curry (c : OracleCode) (n : ℕ) : OracleCode :=
  comp c (pair (OracleCode.const n) OracleCode.id)

/-- A code for plain minimization, derived from the `rfind'` constructor. -/
def rfind (cf : OracleCode) : OracleCode :=
  comp (rfind' cf) (pair OracleCode.id zero)

@[simp]
theorem eval_const (p : Baire) : ∀ n m, (OracleCode.const n).eval p m = Part.some n
  | 0, _ => rfl
  | n + 1, m => by simp! [eval_const p n m]

@[simp]
theorem eval_id (p : Baire) (n : ℕ) : OracleCode.id.eval p n = Part.some n := by
  simp! [Seq.seq, OracleCode.id]

@[simp]
theorem eval_curry (c : OracleCode) (n x : ℕ) (p : Baire) :
    (curry c n).eval p x = c.eval p (Nat.pair n x) := by
  simp! [Seq.seq, curry]
  rw [some_bind_pfun]

theorem eval_rfind (cf : OracleCode) (p : Baire) (a : ℕ) :
    (rfind cf).eval p a =
      Nat.rfind fun n => (fun x => x = 0) <$> cf.eval p (Nat.pair a n) := by
  have h : (pair OracleCode.id zero).eval p a = Part.some (Nat.pair a 0) := by
    simp [Seq.seq, pure, PFun.pure]
  simp only [rfind, eval_comp, h, some_bind_pfun]
  rw [eval_rfind' cf p a 0]
  simp only [Nat.add_zero]
  exact Part.map_id' (fun _ => rfl) _

theorem primrec_const : Primrec OracleCode.const :=
  (Primrec.id.nat_iterate (Primrec.const zero)
        (primrec₂_comp.comp (Primrec.const succ) Primrec.snd).to₂).of_eq
    fun n => by
      simp only [id_eq]
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih]
        rfl

theorem primrec₂_curry : Primrec₂ curry :=
  primrec₂_comp.comp Primrec.fst <|
    primrec₂_pair.comp (primrec_const.comp Primrec.snd) (Primrec.const OracleCode.id)

theorem curry_inj {c₁ c₂ : OracleCode} {n₁ n₂ : ℕ} (h : curry c₁ n₁ = curry c₂ n₂) :
    c₁ = c₂ ∧ n₁ = n₂ :=
  ⟨by injection h, by
    injection h with h₁ h₂
    injection h₂ with h₃ h₄
    exact const_inj h₃⟩

/-! ### Embedding oracle-free codes -/

/-- Embed a `Nat.Partrec.Code` as an `OracleCode` that never queries the oracle. -/
def ofPartrecCode : Nat.Partrec.Code → OracleCode
  | .zero => zero
  | .succ => succ
  | .left => left
  | .right => right
  | .pair cf cg => pair (ofPartrecCode cf) (ofPartrecCode cg)
  | .comp cf cg => comp (ofPartrecCode cf) (ofPartrecCode cg)
  | .prec cf cg => prec (ofPartrecCode cf) (ofPartrecCode cg)
  | .rfind' cf => rfind' (ofPartrecCode cf)

/-- Evaluation of an embedded oracle-free code ignores the oracle. -/
@[simp]
theorem eval_ofPartrecCode (c : Nat.Partrec.Code) (p : Baire) :
    (ofPartrecCode c).eval p = c.eval := by
  induction c with
  | zero => rfl
  | succ => rfl
  | left => rfl
  | right => rfl
  | pair cf cg ihf ihg => simp only [ofPartrecCode, eval, Nat.Partrec.Code.eval, ihf, ihg]; rfl
  | comp cf cg ihf ihg => simp only [ofPartrecCode, eval, Nat.Partrec.Code.eval, ihf, ihg]; rfl
  | prec cf cg ihf ihg => simp only [ofPartrecCode, eval, Nat.Partrec.Code.eval, ihf, ihg]; rfl
  | rfind' cf ihf => simp only [ofPartrecCode, eval, Nat.Partrec.Code.eval, ihf]; rfl

end OracleCode

end ComputableAnalysis
