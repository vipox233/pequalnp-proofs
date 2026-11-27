import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bitwise
import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_073

open PEqualNP.CircuitLowerBounds

def ValidGates (I : ℕ) (gs : List Gate) : Prop :=
  PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack I ⟨gs, 0⟩

def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires x

def wireVal (gs : List Gate) (x : List Bool) (w : ℕ) : Bool :=
  (wiresOf gs x).getD w false

lemma wiresOf_nil (x : List Bool) : wiresOf [] x = x := rfl

lemma wiresOf_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    wiresOf (g :: gs) x =
      wiresOf gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl

lemma wiresOf_append (gs1 gs2 : List Gate) (x : List Bool) :
    wiresOf (gs1 ++ gs2) x = wiresOf gs2 (wiresOf gs1 x) := by
  simp [wiresOf, Circuit.wires, List.foldl_append]

lemma wiresOf_length (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [wiresOf, Circuit.wires]
  | cons g gs ih =>
    rw [wiresOf_cons, ih]
    simp; omega

lemma wiresOf_getD_lt (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (wiresOf gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresOf_cons, ih]
    · exact List.getD_append _ _ _ _ hw
    · simp; omega

lemma wireVal_append_left (gs1 gs2 : List Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + gs1.length) :
    wireVal (gs1 ++ gs2) x w = wireVal gs1 x w := by
  unfold wireVal
  rw [wiresOf_append, wiresOf_getD_lt]
  rw [wiresOf_length]
  exact hw

lemma wireVal_input (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    wireVal gs x w = x.getD w false := by
  exact wiresOf_getD_lt gs x w hw

lemma wireVal_push (gs : List Gate) (g : Gate) (x : List Bool) :
    wireVal (gs ++ [g]) x (x.length + gs.length) =
      g.op.eval (g.inputs.map fun i => wireVal gs x i) := by
  unfold wireVal
  rw [wiresOf_append, wiresOf_cons, wiresOf_nil]
  have hlen : (wiresOf gs x).length = x.length + gs.length := wiresOf_length gs x
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hlen]

lemma validGates_nil (I : ℕ) : ValidGates I [] := by
  refine ⟨?_, ?_⟩
  · intro g hg; cases hg
  · intro j hj; cases hj

lemma validGates_push (I : ℕ) (gs : List Gate) (g : Gate)
    (hgs : ValidGates I gs)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2)
    (hins : ∀ i ∈ g.inputs, i < I + gs.length) :
    ValidGates I (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with h | rfl
    · exact hgs.1 g' h
    · exact ⟨hop, hlen⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
    dsimp only at hi
    by_cases hlt : j < gs.length
    · rw [List.getD_append _ _ _ _ hlt] at hi
      exact hgs.2 j hlt i hi
    · have hj_eq : j = gs.length := by omega
      subst hj_eq
      rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
      simp only [Nat.sub_self, List.getD_cons_zero] at hi
      exact hins i hi

def Extends (I : ℕ) (gs1 gs2 : List Gate) : Prop :=
  ∃ extra, gs2 = gs1 ++ extra ∧ (ValidGates I gs1 → ValidGates I gs2)

lemma extends_refl (I : ℕ) (gs : List Gate) : Extends I gs gs :=
  ⟨[], by simp, id⟩

lemma extends_trans {I : ℕ} {gs1 gs2 gs3 : List Gate}
    (h1 : Extends I gs1 gs2) (h2 : Extends I gs2 gs3) : Extends I gs1 gs3 := by
  rcases h1 with ⟨e1, rfl, hv1⟩
  rcases h2 with ⟨e2, rfl, hv2⟩
  exact ⟨e1 ++ e2, by simp [List.append_assoc], fun h => hv2 (hv1 h)⟩

lemma extends_length_le {I : ℕ} {gs1 gs2 : List Gate} (h : Extends I gs1 gs2) :
    gs1.length ≤ gs2.length := by
  rcases h with ⟨e, rfl, _⟩
  simp

lemma extends_valid {I : ℕ} {gs1 gs2 : List Gate} (h : Extends I gs1 gs2)
    (hv : ValidGates I gs1) : ValidGates I gs2 := by
  rcases h with ⟨_, _, hf⟩
  exact hf hv

lemma extends_wireVal {I : ℕ} {gs1 gs2 : List Gate} (h : Extends I gs1 gs2)
    (x : List Bool) (hx : x.length = I) (w : ℕ) (hw : w < I + gs1.length) :
    wireVal gs2 x w = wireVal gs1 x w := by
  rcases h with ⟨e, rfl, _⟩
  apply wireVal_append_left
  omega

def mkFalse (I : ℕ) (gs : List Gate) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.or, []⟩], I + gs.length)

def mkTrue (I : ℕ) (gs : List Gate) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.and, []⟩], I + gs.length)

def mkNot (I : ℕ) (gs : List Gate) (a : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.not, [a]⟩], I + gs.length)

def mkAnd (I : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.and, [a, b]⟩], I + gs.length)

def mkOr (I : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.or, [a, b]⟩], I + gs.length)

lemma mkFalse_spec (I : ℕ) (gs : List Gate) :
    Extends I gs (mkFalse I gs).1 ∧ (mkFalse I gs).1.length = gs.length + 1 ∧
    (mkFalse I gs).2 < I + (mkFalse I gs).1.length ∧
    ∀ x, x.length = I → wireVal (mkFalse I gs).1 x (mkFalse I gs).2 = false := by
  refine ⟨⟨[⟨GateOp.or, []⟩], rfl, fun h => validGates_push I gs _ h (by simp) (by simp) (by simp)⟩,
    by simp [mkFalse], by simp [mkFalse], ?_⟩
  intro x hx
  dsimp [mkFalse]
  rw [← hx, wireVal_push]
  rfl

lemma mkTrue_spec (I : ℕ) (gs : List Gate) :
    Extends I gs (mkTrue I gs).1 ∧ (mkTrue I gs).1.length = gs.length + 1 ∧
    (mkTrue I gs).2 < I + (mkTrue I gs).1.length ∧
    ∀ x, x.length = I → wireVal (mkTrue I gs).1 x (mkTrue I gs).2 = true := by
  refine ⟨⟨[⟨GateOp.and, []⟩], rfl, fun h => validGates_push I gs _ h (by simp) (by simp) (by simp)⟩,
    by simp [mkTrue], by simp [mkTrue], ?_⟩
  intro x hx
  dsimp [mkTrue]
  rw [← hx, wireVal_push]
  rfl

lemma mkNot_spec (I : ℕ) (gs : List Gate) (a : ℕ) (ha : a < I + gs.length) :
    Extends I gs (mkNot I gs a).1 ∧ (mkNot I gs a).1.length = gs.length + 1 ∧
    (mkNot I gs a).2 < I + (mkNot I gs a).1.length ∧
    ∀ x, x.length = I → wireVal (mkNot I gs a).1 x (mkNot I gs a).2 = !(wireVal gs x a) := by
  refine ⟨⟨[⟨GateOp.not, [a]⟩], rfl, fun h => validGates_push I gs _ h (by simp) (by simp) (by simpa)⟩,
    by simp [mkNot], by simp [mkNot], ?_⟩
  intro x hx
  dsimp [mkNot]
  rw [← hx, wireVal_push]
  simp [GateOp.eval]

lemma mkAnd_spec (I : ℕ) (gs : List Gate) (a b : ℕ)
    (ha : a < I + gs.length) (hb : b < I + gs.length) :
    Extends I gs (mkAnd I gs a b).1 ∧ (mkAnd I gs a b).1.length = gs.length + 1 ∧
    (mkAnd I gs a b).2 < I + (mkAnd I gs a b).1.length ∧
    ∀ x, x.length = I → wireVal (mkAnd I gs a b).1 x (mkAnd I gs a b).2 =
      (wireVal gs x a && wireVal gs x b) := by
  refine ⟨⟨[⟨GateOp.and, [a, b]⟩], rfl, fun h => validGates_push I gs _ h (by simp) (by simp)
    (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
    by simp [mkAnd], by simp [mkAnd], ?_⟩
  intro x hx
  dsimp [mkAnd]
  rw [← hx, wireVal_push]
  simp [GateOp.eval]

lemma mkOr_spec (I : ℕ) (gs : List Gate) (a b : ℕ)
    (ha : a < I + gs.length) (hb : b < I + gs.length) :
    Extends I gs (mkOr I gs a b).1 ∧ (mkOr I gs a b).1.length = gs.length + 1 ∧
    (mkOr I gs a b).2 < I + (mkOr I gs a b).1.length ∧
    ∀ x, x.length = I → wireVal (mkOr I gs a b).1 x (mkOr I gs a b).2 =
      (wireVal gs x a || wireVal gs x b) := by
  refine ⟨⟨[⟨GateOp.or, [a, b]⟩], rfl, fun h => validGates_push I gs _ h (by simp) (by simp)
    (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
    by simp [mkOr], by simp [mkOr], ?_⟩
  intro x hx
  dsimp [mkOr]
  rw [← hx, wireVal_push]
  simp [GateOp.eval]

def mkMux (I : ℕ) (gs : List Gate) (c nc a b : ℕ) : List Gate × ℕ :=
  let (gs1, t1) := mkAnd I gs c a
  let (gs2, t2) := mkAnd I gs1 nc b
  mkOr I gs2 t1 t2

lemma mkMux_spec (I : ℕ) (gs : List Gate) (c nc a b : ℕ)
    (hc : c < I + gs.length) (hnc : nc < I + gs.length)
    (ha : a < I + gs.length) (hb : b < I + gs.length) :
    Extends I gs (mkMux I gs c nc a b).1 ∧ (mkMux I gs c nc a b).1.length = gs.length + 3 ∧
    (mkMux I gs c nc a b).2 < I + (mkMux I gs c nc a b).1.length ∧
    ∀ x, x.length = I → wireVal gs x nc = !(wireVal gs x c) →
      wireVal (mkMux I gs c nc a b).1 x (mkMux I gs c nc a b).2 =
        if wireVal gs x c then wireVal gs x a else wireVal gs x b := by
  dsimp only [mkMux]
  obtain ⟨he1, hl1, hw1, hv1⟩ := mkAnd_spec I gs c a hc ha
  set r1 := mkAnd I gs c a
  obtain ⟨he2, hl2, hw2, hv2⟩ := mkAnd_spec I r1.1 nc b (by omega) (by omega)
  set r2 := mkAnd I r1.1 nc b
  obtain ⟨he3, hl3, hw3, hv3⟩ := mkOr_spec I r2.1 r1.2 r2.2 (by omega) (by omega)
  set r3 := mkOr I r2.1 r1.2 r2.2
  refine ⟨extends_trans he1 (extends_trans he2 he3), by omega, hw3, ?_⟩
  intro x hx hnot
  rw [hv3 x hx, extends_wireVal he2 x hx r1.2 hw1, hv1 x hx, hv2 x hx]
  rw [extends_wireVal he1 x hx nc hnc, extends_wireVal he1 x hx b hb, hnot]
  cases wireVal gs x c <;> simp

def mkXnor (I : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  let (gs1, na) := mkNot I gs a
  let (gs2, nb) := mkNot I gs1 b
  let (gs3, t1) := mkAnd I gs2 a b
  let (gs4, t2) := mkAnd I gs3 na nb
  mkOr I gs4 t1 t2

lemma mkXnor_spec (I : ℕ) (gs : List Gate) (a b : ℕ)
    (ha : a < I + gs.length) (hb : b < I + gs.length) :
    Extends I gs (mkXnor I gs a b).1 ∧ (mkXnor I gs a b).1.length = gs.length + 5 ∧
    (mkXnor I gs a b).2 < I + (mkXnor I gs a b).1.length ∧
    ∀ x, x.length = I → wireVal (mkXnor I gs a b).1 x (mkXnor I gs a b).2 =
      (wireVal gs x a == wireVal gs x b) := by
  dsimp only [mkXnor]
  obtain ⟨he1, hl1, hw1, hv1⟩ := mkNot_spec I gs a ha
  set r1 := mkNot I gs a
  obtain ⟨he2, hl2, hw2, hv2⟩ := mkNot_spec I r1.1 b (by omega)
  set r2 := mkNot I r1.1 b
  obtain ⟨he3, hl3, hw3, hv3⟩ := mkAnd_spec I r2.1 a b (by omega) (by omega)
  set r3 := mkAnd I r2.1 a b
  obtain ⟨he4, hl4, hw4, hv4⟩ := mkAnd_spec I r3.1 r1.2 r2.2 (by omega) (by omega)
  set r4 := mkAnd I r3.1 r1.2 r2.2
  obtain ⟨he5, hl5, hw5, hv5⟩ := mkOr_spec I r4.1 r3.2 r4.2 (by omega) (by omega)
  set r5 := mkOr I r4.1 r3.2 r4.2
  have he12 : Extends I gs r2.1 := extends_trans he1 he2
  have he13 : Extends I gs r3.1 := extends_trans he12 he3
  have he23 : Extends I r1.1 r3.1 := extends_trans he2 he3
  refine ⟨extends_trans he13 (extends_trans he4 he5), by omega, hw5, ?_⟩
  intro x hx
  rw [hv5 x hx, extends_wireVal he4 x hx r3.2 hw3, hv3 x hx, hv4 x hx]
  rw [extends_wireVal he12 x hx a ha, extends_wireVal he12 x hx b hb]
  rw [extends_wireVal he23 x hx r1.2 hw1, extends_wireVal he3 x hx r2.2 hw2]
  rw [hv1 x hx, hv2 x hx, extends_wireVal he1 x hx b hb]
  cases wireVal gs x a <;> cases wireVal gs x b <;> rfl

def bitsListToNat : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 2 ^ bs.length else 0) + bitsListToNat bs

lemma bitsListToNat_lt (l : List Bool) : bitsListToNat l < 2 ^ l.length := by
  induction l with
  | nil => simp [bitsListToNat]
  | cons b bs ih =>
    simp only [bitsListToNat, List.length_cons, pow_succ]
    cases b <;> (simp; omega)

lemma bitsListToNat_append_singleton (l : List Bool) (b : Bool) :
    bitsListToNat (l ++ [b]) = 2 * bitsListToNat l + (if b then 1 else 0) := by
  induction l with
  | nil => simp [bitsListToNat]
  | cons a as ih =>
    simp only [List.cons_append, bitsListToNat, List.length_append, List.length_singleton,
      pow_succ, ih]
    cases a
    · simp
    · simp; omega

lemma bitsListToNat_gt_cons (a b : Bool) (as bs : List Bool) (h : as.length = bs.length) :
    decide (bitsListToNat (b :: bs) < bitsListToNat (a :: as)) =
      ((a && !b) || ((a || !b) && decide (bitsListToNat bs < bitsListToNat as))) := by
  have ha := bitsListToNat_lt as
  have hb := bitsListToNat_lt bs
  rw [h] at ha
  simp only [bitsListToNat, h]
  cases a <;> cases b <;> simp
  · omega
  · omega

def mkGt (I wFalse : ℕ) (gs : List Gate) : List ℕ → List ℕ → List Gate × ℕ
  | [], _ => (gs, wFalse)
  | _, [] => (gs, wFalse)
  | a :: as, b :: bs =>
    let (gs1, gtTail) := mkGt I wFalse gs as bs
    let (gs2, nb) := mkNot I gs1 b
    let (gs3, strict) := mkAnd I gs2 a nb
    let (gs4, ge) := mkOr I gs3 a nb
    let (gs5, tie) := mkAnd I gs4 ge gtTail
    mkOr I gs5 strict tie

lemma mkGt_spec (I wFalse : ℕ) (gs : List Gate) (as bs : List ℕ)
    (hlen : as.length = bs.length)
    (hwf : wFalse < I + gs.length)
    (has : ∀ w ∈ as, w < I + gs.length)
    (hbs : ∀ w ∈ bs, w < I + gs.length) :
    Extends I gs (mkGt I wFalse gs as bs).1 ∧
    (mkGt I wFalse gs as bs).1.length = gs.length + 5 * as.length ∧
    (mkGt I wFalse gs as bs).2 < I + (mkGt I wFalse gs as bs).1.length ∧
    ∀ x, x.length = I → wireVal gs x wFalse = false →
      wireVal (mkGt I wFalse gs as bs).1 x (mkGt I wFalse gs as bs).2 =
        decide (bitsListToNat (bs.map (wireVal gs x)) < bitsListToNat (as.map (wireVal gs x))) := by
  induction as generalizing bs gs with
  | nil =>
    cases bs with
    | nil =>
      refine ⟨extends_refl I gs, by simp [mkGt], hwf, ?_⟩
      intro x hx hwf0
      simpa [mkGt, bitsListToNat] using hwf0
    | cons _ _ => simp at hlen
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have ha : a < I + gs.length := has a (by simp)
      have hb : b < I + gs.length := hbs b (by simp)
      dsimp only [mkGt]
      obtain ⟨he1, hl1, hw1, hv1⟩ := ih gs bs hlen hwf
        (fun w hw => has w (by simp [hw])) (fun w hw => hbs w (by simp [hw]))
      set r1 := mkGt I wFalse gs as bs
      obtain ⟨he2, hl2, hw2, hv2⟩ := mkNot_spec I r1.1 b (by omega)
      set r2 := mkNot I r1.1 b
      obtain ⟨he3, hl3, hw3, hv3⟩ := mkAnd_spec I r2.1 a r2.2 (by omega) (by omega)
      set r3 := mkAnd I r2.1 a r2.2
      obtain ⟨he4, hl4, hw4, hv4⟩ := mkOr_spec I r3.1 a r2.2 (by omega) (by omega)
      set r4 := mkOr I r3.1 a r2.2
      obtain ⟨he5, hl5, hw5, hv5⟩ := mkAnd_spec I r4.1 r4.2 r1.2 (by omega) (by omega)
      set r5 := mkAnd I r4.1 r4.2 r1.2
      obtain ⟨he6, hl6, hw6, hv6⟩ := mkOr_spec I r5.1 r3.2 r5.2 (by omega) (by omega)
      set r6 := mkOr I r5.1 r3.2 r5.2
      have he02 : Extends I gs r2.1 := extends_trans he1 he2
      have he03 : Extends I gs r3.1 := extends_trans he02 he3
      have he04 : Extends I gs r4.1 := extends_trans he03 he4
      have he05 : Extends I gs r5.1 := extends_trans he04 he5
      have he06 : Extends I gs r6.1 := extends_trans he05 he6
      have he14 : Extends I r1.1 r4.1 := extends_trans he2 (extends_trans he3 he4)
      have he35 : Extends I r3.1 r5.1 := extends_trans he4 he5
      refine ⟨he06, by simp only [List.length_cons]; omega, hw6, ?_⟩
      intro x hx hwf0
      rw [hv6 x hx, extends_wireVal he35 x hx r3.2 hw3]
      rw [hv3 x hx, hv5 x hx, hv4 x hx]
      rw [extends_wireVal he02 x hx a ha, extends_wireVal he03 x hx a ha]
      rw [extends_wireVal he3 x hx r2.2 hw2, extends_wireVal he14 x hx r1.2 hw1]
      rw [hv2 x hx, extends_wireVal he1 x hx b hb, hv1 x hx hwf0]
      simp only [List.map_cons]
      rw [bitsListToNat_gt_cons]
      simp [hlen]

def mkEq (I wTrue : ℕ) (gs : List Gate) : List ℕ → List ℕ → List Gate × ℕ
  | [], _ => (gs, wTrue)
  | _, [] => (gs, wTrue)
  | a :: as, b :: bs =>
    let (gs1, eqTail) := mkEq I wTrue gs as bs
    let (gs2, bitEq) := mkXnor I gs1 a b
    mkAnd I gs2 bitEq eqTail

lemma mkEq_spec (I wTrue : ℕ) (gs : List Gate) (as bs : List ℕ)
    (hlen : as.length = bs.length)
    (hwt : wTrue < I + gs.length)
    (has : ∀ w ∈ as, w < I + gs.length)
    (hbs : ∀ w ∈ bs, w < I + gs.length) :
    Extends I gs (mkEq I wTrue gs as bs).1 ∧
    (mkEq I wTrue gs as bs).1.length = gs.length + 6 * as.length ∧
    (mkEq I wTrue gs as bs).2 < I + (mkEq I wTrue gs as bs).1.length ∧
    ∀ x, x.length = I → wireVal gs x wTrue = true →
      wireVal (mkEq I wTrue gs as bs).1 x (mkEq I wTrue gs as bs).2 =
        decide (as.map (wireVal gs x) = bs.map (wireVal gs x)) := by
  induction as generalizing bs gs with
  | nil =>
    cases bs with
    | nil =>
      refine ⟨extends_refl I gs, by simp [mkEq], hwt, ?_⟩
      intro x hx hwt1
      simpa [mkEq] using hwt1
    | cons _ _ => simp at hlen
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have ha : a < I + gs.length := has a (by simp)
      have hb : b < I + gs.length := hbs b (by simp)
      dsimp only [mkEq]
      obtain ⟨he1, hl1, hw1, hv1⟩ := ih gs bs hlen hwt
        (fun w hw => has w (by simp [hw])) (fun w hw => hbs w (by simp [hw]))
      set r1 := mkEq I wTrue gs as bs
      obtain ⟨he2, hl2, hw2, hv2⟩ := mkXnor_spec I r1.1 a b (by omega) (by omega)
      set r2 := mkXnor I r1.1 a b
      obtain ⟨he3, hl3, hw3, hv3⟩ := mkAnd_spec I r2.1 r2.2 r1.2 (by omega) (by omega)
      set r3 := mkAnd I r2.1 r2.2 r1.2
      refine ⟨extends_trans he1 (extends_trans he2 he3), by simp only [List.length_cons]; omega, hw3, ?_⟩
      intro x hx hwt1
      rw [hv3 x hx, hv2 x hx, extends_wireVal he2 x hx r1.2 hw1, hv1 x hx hwt1]
      rw [extends_wireVal he1 x hx a ha, extends_wireVal he1 x hx b hb]
      simp only [List.map_cons, List.cons.injEq]
      cases wireVal gs x a <;> cases wireVal gs x b <;> simp

def mkSwapVec (I : ℕ) (gs : List Gate) (ctrl notCtrl : ℕ) :
    List ℕ → List ℕ → List Gate × List ℕ × List ℕ
  | [], _ => (gs, [], [])
  | _, [] => (gs, [], [])
  | a :: as, b :: bs =>
    let (gs1, a') := mkMux I gs ctrl notCtrl b a
    let (gs2, b') := mkMux I gs1 ctrl notCtrl a b
    let (gs3, as', bs') := mkSwapVec I gs2 ctrl notCtrl as bs
    (gs3, a' :: as', b' :: bs')

lemma mkSwapVec_spec (I : ℕ) (gs : List Gate) (ctrl notCtrl : ℕ) (as bs : List ℕ)
    (hlen : as.length = bs.length)
    (hc : ctrl < I + gs.length) (hnc : notCtrl < I + gs.length)
    (has : ∀ w ∈ as, w < I + gs.length)
    (hbs : ∀ w ∈ bs, w < I + gs.length) :
    Extends I gs (mkSwapVec I gs ctrl notCtrl as bs).1 ∧
    (mkSwapVec I gs ctrl notCtrl as bs).1.length = gs.length + 6 * as.length ∧
    (mkSwapVec I gs ctrl notCtrl as bs).2.1.length = as.length ∧
    (mkSwapVec I gs ctrl notCtrl as bs).2.2.length = bs.length ∧
    (∀ w ∈ (mkSwapVec I gs ctrl notCtrl as bs).2.1, w < I + (mkSwapVec I gs ctrl notCtrl as bs).1.length) ∧
    (∀ w ∈ (mkSwapVec I gs ctrl notCtrl as bs).2.2, w < I + (mkSwapVec I gs ctrl notCtrl as bs).1.length) ∧
    ∀ x, x.length = I → wireVal gs x notCtrl = !(wireVal gs x ctrl) →
      (mkSwapVec I gs ctrl notCtrl as bs).2.1.map (wireVal (mkSwapVec I gs ctrl notCtrl as bs).1 x) =
        (if wireVal gs x ctrl then bs.map (wireVal gs x) else as.map (wireVal gs x)) ∧
      (mkSwapVec I gs ctrl notCtrl as bs).2.2.map (wireVal (mkSwapVec I gs ctrl notCtrl as bs).1 x) =
        (if wireVal gs x ctrl then as.map (wireVal gs x) else bs.map (wireVal gs x)) := by
  induction as generalizing bs gs with
  | nil =>
    cases bs with
    | nil =>
      refine ⟨extends_refl I gs, by simp [mkSwapVec], rfl, rfl, by simp [mkSwapVec],
        by simp [mkSwapVec], ?_⟩
      intro x hx hnot
      cases wireVal gs x ctrl <;> simp [mkSwapVec]
    | cons _ _ => simp at hlen
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      have ha : a < I + gs.length := has a (by simp)
      have hb : b < I + gs.length := hbs b (by simp)
      dsimp only [mkSwapVec]
      obtain ⟨he1, hl1, hw1, hv1⟩ := mkMux_spec I gs ctrl notCtrl b a hc hnc hb ha
      set r1 := mkMux I gs ctrl notCtrl b a
      obtain ⟨he2, hl2, hw2, hv2⟩ := mkMux_spec I r1.1 ctrl notCtrl a b (by omega) (by omega) (by omega) (by omega)
      set r2 := mkMux I r1.1 ctrl notCtrl a b
      have he02 : Extends I gs r2.1 := extends_trans he1 he2
      obtain ⟨he3, hl3, hla3, hlb3, hwa3, hwb3, hv3⟩ := ih r2.1 bs hlen (by omega) (by omega)
        (fun w hw => by have := has w (by simp [hw]); omega)
        (fun w hw => by have := hbs w (by simp [hw]); omega)
      set r3 := mkSwapVec I r2.1 ctrl notCtrl as bs
      have he03 : Extends I gs r3.1 := extends_trans he02 he3
      have he13 : Extends I r1.1 r3.1 := extends_trans he2 he3
      refine ⟨he03, by simp only [List.length_cons]; omega, by simp [hla3], by simp [hlb3], ?_, ?_, ?_⟩
      · intro w hw
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · omega
        · exact hwa3 w hw
      · intro w hw
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · omega
        · exact hwb3 w hw
      · intro x hx hnot
        have hnot1 : wireVal r1.1 x notCtrl = !(wireVal r1.1 x ctrl) := by
          rw [extends_wireVal he1 x hx notCtrl hnc, extends_wireVal he1 x hx ctrl hc, hnot]
        have hnot2 : wireVal r2.1 x notCtrl = !(wireVal r2.1 x ctrl) := by
          rw [extends_wireVal he02 x hx notCtrl hnc, extends_wireVal he02 x hx ctrl hc, hnot]
        have hspec3 := hv3 x hx hnot2
        have hmap_as : as.map (wireVal r2.1 x) = as.map (wireVal gs x) :=
          List.map_congr_left fun w hw => extends_wireVal he02 x hx w (has w (by simp [hw]))
        have hmap_bs : bs.map (wireVal r2.1 x) = bs.map (wireVal gs x) :=
          List.map_congr_left fun w hw => extends_wireVal he02 x hx w (hbs w (by simp [hw]))
        have hctrl2 : wireVal r2.1 x ctrl = wireVal gs x ctrl :=
          extends_wireVal he02 x hx ctrl hc
        simp only [List.map_cons]
        rw [extends_wireVal he13 x hx r1.2 hw1, hv1 x hx hnot]
        rw [extends_wireVal he3 x hx r2.2 hw2, hv2 x hx hnot1]
        rw [extends_wireVal he1 x hx ctrl hc, extends_wireVal he1 x hx a ha,
          extends_wireVal he1 x hx b hb]
        rw [hspec3.1, hspec3.2, hctrl2, hmap_as, hmap_bs]
        cases wireVal gs x ctrl <;> simp

def mkCmp (I wFalse : ℕ) (gs : List Gate) (asc : Bool) (as bs : List ℕ) :
    List Gate × ℕ × ℕ × List ℕ × List ℕ :=
  let (gs1, ctrl) := if asc then mkGt I wFalse gs as bs else mkGt I wFalse gs bs as
  let (gs2, notCtrl) := mkNot I gs1 ctrl
  let (gs3, as', bs') := mkSwapVec I gs2 ctrl notCtrl as bs
  (gs3, ctrl, notCtrl, as', bs')

lemma mkCmp_spec (I wFalse : ℕ) (gs : List Gate) (asc : Bool) (as bs : List ℕ)
    (hlen : as.length = bs.length)
    (hwf : wFalse < I + gs.length)
    (has : ∀ w ∈ as, w < I + gs.length)
    (hbs : ∀ w ∈ bs, w < I + gs.length) :
    Extends I gs (mkCmp I wFalse gs asc as bs).1 ∧
    (mkCmp I wFalse gs asc as bs).1.length = gs.length + (11 * as.length + 1) ∧
    (mkCmp I wFalse gs asc as bs).2.1 < I + (mkCmp I wFalse gs asc as bs).1.length ∧
    (mkCmp I wFalse gs asc as bs).2.2.1 < I + (mkCmp I wFalse gs asc as bs).1.length ∧
    (mkCmp I wFalse gs asc as bs).2.2.2.1.length = as.length ∧
    (mkCmp I wFalse gs asc as bs).2.2.2.2.length = bs.length ∧
    (∀ w ∈ (mkCmp I wFalse gs asc as bs).2.2.2.1, w < I + (mkCmp I wFalse gs asc as bs).1.length) ∧
    (∀ w ∈ (mkCmp I wFalse gs asc as bs).2.2.2.2, w < I + (mkCmp I wFalse gs asc as bs).1.length) ∧
    ∀ x, x.length = I → wireVal gs x wFalse = false →
      let va := bitsListToNat (as.map (wireVal gs x))
      let vb := bitsListToNat (bs.map (wireVal gs x))
      let swap := if asc then decide (vb < va) else decide (va < vb)
      wireVal (mkCmp I wFalse gs asc as bs).1 x (mkCmp I wFalse gs asc as bs).2.1 = swap ∧
      wireVal (mkCmp I wFalse gs asc as bs).1 x (mkCmp I wFalse gs asc as bs).2.2.1 = !swap ∧
      bitsListToNat ((mkCmp I wFalse gs asc as bs).2.2.2.1.map (wireVal (mkCmp I wFalse gs asc as bs).1 x)) =
        (if swap then vb else va) ∧
      bitsListToNat ((mkCmp I wFalse gs asc as bs).2.2.2.2.map (wireVal (mkCmp I wFalse gs asc as bs).1 x)) =
        (if swap then va else vb) := by
  dsimp only [mkCmp]
  have h1 :
      Extends I gs (if asc then mkGt I wFalse gs as bs else mkGt I wFalse gs bs as).1 ∧
      (if asc then mkGt I wFalse gs as bs else mkGt I wFalse gs bs as).1.length = gs.length + 5 * as.length ∧
      (if asc then mkGt I wFalse gs as bs else mkGt I wFalse gs bs as).2 <
        I + (if asc then mkGt I wFalse gs as bs else mkGt I wFalse gs bs as).1.length ∧
      ∀ x, x.length = I → wireVal gs x wFalse = false →
        wireVal (if asc then mkGt I wFalse gs as bs else mkGt I wFalse gs bs as).1 x
          (if asc then mkGt I wFalse gs as bs else mkGt I wFalse gs bs as).2 =
          if asc then decide (bitsListToNat (bs.map (wireVal gs x)) < bitsListToNat (as.map (wireVal gs x)))
          else decide (bitsListToNat (as.map (wireVal gs x)) < bitsListToNat (bs.map (wireVal gs x))) := by
    cases asc
    · simpa [hlen] using mkGt_spec I wFalse gs bs as hlen.symm hwf hbs has
    · simpa using mkGt_spec I wFalse gs as bs hlen hwf has hbs
  set r1 := if asc then mkGt I wFalse gs as bs else mkGt I wFalse gs bs as
  rcases h1 with ⟨he1, hl1, hw1, hv1⟩
  obtain ⟨he2, hl2, hw2, hv2⟩ := mkNot_spec I r1.1 r1.2 hw1
  set r2 := mkNot I r1.1 r1.2
  have he02 : Extends I gs r2.1 := extends_trans he1 he2
  obtain ⟨he3, hl3, hla3, hlb3, hwa3, hwb3, hv3⟩ := mkSwapVec_spec I r2.1 r1.2 r2.2 as bs hlen
    (by omega) (by omega)
    (fun w hw => by have := has w hw; omega) (fun w hw => by have := hbs w hw; omega)
  set r3 := mkSwapVec I r2.1 r1.2 r2.2 as bs
  have he03 : Extends I gs r3.1 := extends_trans he02 he3
  have he13 : Extends I r1.1 r3.1 := extends_trans he2 he3
  refine ⟨he03, by omega, by omega, by omega, hla3, hlb3, hwa3, hwb3, ?_⟩
  intro x hx hwf0
  have hnot2 : wireVal r2.1 x r2.2 = !(wireVal r2.1 x r1.2) := by
    rw [hv2 x hx, extends_wireVal he2 x hx r1.2 hw1]
  have hspec3 := hv3 x hx hnot2
  have hctrl_val : wireVal r2.1 x r1.2 =
      if asc then decide (bitsListToNat (bs.map (wireVal gs x)) < bitsListToNat (as.map (wireVal gs x)))
      else decide (bitsListToNat (as.map (wireVal gs x)) < bitsListToNat (bs.map (wireVal gs x))) := by
    rw [extends_wireVal he2 x hx r1.2 hw1, hv1 x hx hwf0]
  have hmap_as : as.map (wireVal r2.1 x) = as.map (wireVal gs x) :=
    List.map_congr_left fun w hw => extends_wireVal he02 x hx w (has w hw)
  have hmap_bs : bs.map (wireVal r2.1 x) = bs.map (wireVal gs x) :=
    List.map_congr_left fun w hw => extends_wireVal he02 x hx w (hbs w hw)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [extends_wireVal he13 x hx r1.2 hw1, hv1 x hx hwf0]
  · rw [extends_wireVal he3 x hx r2.2 hw2, hnot2, hctrl_val]
  · rw [hspec3.1, hctrl_val, hmap_as, hmap_bs]
    cases asc <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split <;> rfl
  · rw [hspec3.2, hctrl_val, hmap_as, hmap_bs]
    cases asc <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split <;> rfl

def natToBits (n : ℕ) (m : ℕ) : Fin n → Bool :=
  fun j => m.testBit (n - 1 - j.val)

def bitsToNat {n : ℕ} (v : Fin n → Bool) : ℕ :=
  bitsListToNat (List.ofFn v)

lemma bitsToNat_lt {n : ℕ} (v : Fin n → Bool) : bitsToNat v < 2 ^ n := by
  simpa [bitsToNat] using bitsListToNat_lt (List.ofFn v)

lemma testBit_bitsListToNat (l : List Bool) (j : ℕ) (hj : j < l.length) :
    (bitsListToNat l).testBit (l.length - 1 - j) = l.getD j false := by
  induction l generalizing j with
  | nil => simp at hj
  | cons b bs ih =>
    simp only [bitsListToNat, List.length_cons]
    cases j with
    | zero =>
      simp only [Nat.sub_zero, Nat.add_sub_cancel, List.getD_cons_zero]
      have hlt := bitsListToNat_lt bs
      rw [Nat.testBit_eq_decide_div_mod_eq]
      cases b
      · simp [Nat.div_eq_of_lt hlt]
      · have h1 : (2 ^ bs.length + bitsListToNat bs) / 2 ^ bs.length = 1 := by
          rw [Nat.add_div_left _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt]
        simp [h1]
    | succ j' =>
      simp only [List.length_cons] at hj
      have hj' : j' < bs.length := by omega
      have hsub : bs.length + 1 - 1 - (j' + 1) = bs.length - 1 - j' := by omega
      rw [hsub, List.getD_cons_succ, ← ih j' hj']
      have hle : bs.length - 1 - j' < bs.length := by omega
      cases b
      · simp
      · simp only [↓reduceIte]
        rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
        have hpow : 2 ^ bs.length = 2 ^ (bs.length - 1 - j') * (2 * 2 ^ (bs.length - 1 - (bs.length - 1 - j'))) := by
          rw [← pow_succ', ← pow_add]
          congr 1; omega
        have hdiv : (2 ^ bs.length + bitsListToNat bs) / 2 ^ (bs.length - 1 - j') =
            2 * 2 ^ (bs.length - 1 - (bs.length - 1 - j')) + bitsListToNat bs / 2 ^ (bs.length - 1 - j') := by
          rw [hpow, Nat.mul_add_div (Nat.two_pow_pos _)]
        rw [hdiv]
        simp

lemma natToBits_bitsToNat {n : ℕ} (v : Fin n → Bool) :
    natToBits n (bitsToNat v) = v := by
  funext j
  unfold natToBits bitsToNat
  have hj : j.val < (List.ofFn v).length := by simp
  have h := testBit_bitsListToNat (List.ofFn v) j.val hj
  simp only [List.length_ofFn] at h
  rw [h, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

lemma bitsToNat_natToBits (n m : ℕ) (hm : m < 2 ^ n) :
    bitsToNat (natToBits n m) = m := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < n
  · have h := testBit_bitsListToNat (List.ofFn (natToBits n m)) (n - 1 - k) (by simp; omega)
    simp only [List.length_ofFn] at h
    have hsub : n - 1 - (n - 1 - k) = k := by omega
    rw [hsub] at h
    unfold bitsToNat
    rw [h, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    have hlt : n - 1 - k < n := by omega
    simp [natToBits, hsub, hlt]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (bitsToNat_lt _) (Nat.pow_le_pow_right (by omega) (by omega)))]
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by omega) (by omega)))]

lemma bitsToNat_cons {n : ℕ} (b : Bool) (v : Fin n → Bool) :
    bitsToNat (Fin.cons (α := fun _ : Fin (n + 1) => Bool) b v) =
      (if b then 2 ^ n else 0) + bitsToNat v := by
  unfold bitsToNat
  rw [List.ofFn_succ, Fin.cons_zero]
  simp only [Fin.cons_succ, bitsListToNat, List.length_ofFn]

lemma natToBits_succ_zero (n m : ℕ) :
    natToBits (n + 1) m 0 = m.testBit n := by
  simp [natToBits]

lemma natToBits_succ_succ (n m : ℕ) (j : Fin n) :
    natToBits (n + 1) m j.succ = natToBits n m j := by
  simp only [natToBits, Fin.val_succ]
  congr 1; omega

lemma natToBits_eq_cons_false {d : ℕ} (v : Fin d → Bool) :
    natToBits (d + 1) (bitsToNat v) = Fin.cons (α := fun _ : Fin (d + 1) => Bool) false v := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rw [natToBits_succ_zero, Fin.cons_zero]
    exact Nat.testBit_eq_false_of_lt (bitsToNat_lt v)
  · intro j
    rw [natToBits_succ_succ, Fin.cons_succ]
    exact congrFun (natToBits_bitsToNat v) j

lemma natToBits_eq_cons_true {d : ℕ} (v : Fin d → Bool) :
    natToBits (d + 1) (2 ^ d + bitsToNat v) = Fin.cons (α := fun _ : Fin (d + 1) => Bool) true v := by
  have hlt : bitsToNat v < 2 ^ d := bitsToNat_lt v
  funext i
  refine Fin.cases ?_ ?_ i
  · rw [natToBits_succ_zero, Fin.cons_zero, Nat.testBit_eq_decide_div_mod_eq]
    have hdiv : (2 ^ d + bitsToNat v) / 2 ^ d = 1 := by
      rw [Nat.add_div_left _ (Nat.two_pow_pos d), Nat.div_eq_of_lt hlt]
    simp [hdiv]
  · intro j
    rw [natToBits_succ_succ, Fin.cons_succ]
    have hj : d - 1 - j.val < d := by omega
    unfold natToBits
    have hpow : 2 ^ d = 2 ^ (d - 1 - j.val) * (2 * 2 ^ (d - 1 - (d - 1 - j.val))) := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have hdiv : (2 ^ d + bitsToNat v) / 2 ^ (d - 1 - j.val) =
        2 * 2 ^ (d - 1 - (d - 1 - j.val)) + bitsToNat v / 2 ^ (d - 1 - j.val) := by
      rw [hpow, Nat.mul_add_div (Nat.two_pow_pos _)]
    rw [hdiv, Nat.mul_add_mod, ← Nat.testBit_eq_decide_div_mod_eq]
    exact congrFun (natToBits_bitsToNat v) j

def flipBit (j u : ℕ) : ℕ :=
  if u.testBit j then u - 2 ^ j else u + 2 ^ j

def loBit (j u : ℕ) : ℕ :=
  if u.testBit j then u - 2 ^ j else u

lemma testBit_true_ge {j u : ℕ} (h : u.testBit j = true) : 2 ^ j ≤ u := by
  by_contra hlt
  push Not at hlt
  rw [Nat.testBit_eq_false_of_lt hlt] at h
  cases h

lemma testBit_add_two_pow_same {j u : ℕ} (h : u.testBit j = false) :
    (u + 2 ^ j).testBit j = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq] at h ⊢
  rw [Nat.add_div_right _ (Nat.two_pow_pos j)]
  have hmod : u / 2 ^ j % 2 = 0 := by
    have : ¬ (u / 2 ^ j % 2 = 1) := by simpa using h
    omega
  simp [Nat.add_mod, hmod]

lemma testBit_sub_two_pow_same {j u : ℕ} (h : u.testBit j = true) :
    (u - 2 ^ j).testBit j = false := by
  have hge := testBit_true_ge h
  rw [Nat.testBit_eq_decide_div_mod_eq] at h ⊢
  have h1 : u / 2 ^ j % 2 = 1 := by simpa using h
  have hdiv1 : (u - 2 ^ j) / 2 ^ j + 1 = u / 2 ^ j := by
    have := Nat.add_div_right (u - 2 ^ j) (Nat.two_pow_pos j)
    rw [Nat.sub_add_cancel hge] at this
    exact this.symm
  have hdiv : (u - 2 ^ j) / 2 ^ j = u / 2 ^ j - 1 := Nat.eq_sub_of_add_eq hdiv1
  rw [hdiv]
  simp; omega

lemma two_pow_add_lt {p j u : ℕ} (hu : u < 2 ^ p) (hj : j < p) (hb : u.testBit j = false) :
    u + 2 ^ j < 2 ^ p := by
  rw [Nat.testBit_eq_decide_div_mod_eq] at hb
  have hmod : u / 2 ^ j % 2 = 0 := by
    have : ¬ (u / 2 ^ j % 2 = 1) := by simpa using hb
    omega
  have hq : u / 2 ^ j + 1 < 2 ^ (p - j) := by
    have hpow : 2 ^ p = 2 ^ (p - j) * 2 ^ j := by rw [← pow_add, Nat.sub_add_cancel (le_of_lt hj)]
    have hdiv_lt : u / 2 ^ j < 2 ^ (p - j) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos j), ← hpow]; exact hu
    have heven : 2 ∣ 2 ^ (p - j) := by
      have : p - j = (p - j - 1) + 1 := by omega
      rw [this, pow_succ]; exact dvd_mul_left 2 _
    omega
  have hpow : 2 ^ p = 2 ^ (p - j) * 2 ^ j := by rw [← pow_add, Nat.sub_add_cancel (le_of_lt hj)]
  have h1 : u < (u / 2 ^ j + 1) * 2 ^ j := by
    have := Nat.div_add_mod u (2 ^ j)
    have := Nat.mod_lt u (Nat.two_pow_pos j)
    nlinarith
  have h2 : (u / 2 ^ j + 2) * 2 ^ j ≤ 2 ^ (p - j) * 2 ^ j := by
    apply Nat.mul_le_mul_right; omega
  nlinarith

lemma flipBit_lt {p j u : ℕ} (hu : u < 2 ^ p) (hj : j < p) : flipBit j u < 2 ^ p := by
  unfold flipBit
  cases hb : u.testBit j
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact two_pow_add_lt hu hj hb
  · simp only [↓reduceIte]
    exact lt_of_le_of_lt (Nat.sub_le _ _) hu

lemma loBit_le (j u : ℕ) : loBit j u ≤ u := by
  unfold loBit
  cases u.testBit j <;> simp

lemma loBit_lt {p j u : ℕ} (hu : u < 2 ^ p) : loBit j u < 2 ^ p :=
  lt_of_le_of_lt (loBit_le j u) hu

lemma loBit_testBit_false (j u : ℕ) : (loBit j u).testBit j = false := by
  unfold loBit
  cases hb : u.testBit j
  · simpa using hb
  · simpa using testBit_sub_two_pow_same hb

lemma loBit_two_pow_add_lt {p j u : ℕ} (hu : u < 2 ^ p) (hj : j < p) :
    loBit j u + 2 ^ j < 2 ^ p :=
  two_pow_add_lt (loBit_lt hu) hj (loBit_testBit_false j u)

lemma flipBit_invol (j u : ℕ) : flipBit j (flipBit j u) = u := by
  unfold flipBit
  cases hb : u.testBit j
  · simp [testBit_add_two_pow_same hb]
  · have hge := testBit_true_ge hb
    simp [testBit_sub_two_pow_same hb, Nat.sub_add_cancel hge]

lemma loBit_flipBit (j u : ℕ) : loBit j (flipBit j u) = loBit j u := by
  unfold loBit flipBit
  cases hb : u.testBit j
  · simp [testBit_add_two_pow_same hb]
  · simp [testBit_sub_two_pow_same hb]

lemma testBit_add_two_pow_ne {j u i : ℕ} (hb : u.testBit j = false) (hij : i ≠ j) :
    (u + 2 ^ j).testBit i = u.testBit i := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
    have hpow : 2 ^ j = 2 * 2 ^ (j - 1 - i) * 2 ^ i := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    rw [hpow, Nat.add_mul_div_right _ _ (Nat.two_pow_pos i)]
    simp [Nat.add_mul_mod_self_left]
  · rw [Nat.testBit_eq_decide_div_mod_eq] at hb
    have hmod : u / 2 ^ j % 2 = 0 := by
      have : ¬ (u / 2 ^ j % 2 = 1) := by simpa using hb
      omega
    have hpow : 2 ^ i = 2 ^ j * 2 ^ (i - j) := by rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hgt)]
    have h2 : 2 ∣ 2 ^ (i - j) := by
      have : i - j = (i - j - 1) + 1 := by omega
      rw [this, pow_succ]; exact dvd_mul_left 2 _
    have hdiv : (u + 2 ^ j) / 2 ^ i = u / 2 ^ i := by
      rw [hpow, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
        Nat.add_div_right _ (Nat.two_pow_pos j)]
      have hrem : (u / 2 ^ j) % 2 ^ (i - j) + 1 < 2 ^ (i - j) := by
        have hlt2 := Nat.mod_lt (u / 2 ^ j) (Nat.two_pow_pos (i - j))
        have hm2 : (u / 2 ^ j) % 2 ^ (i - j) % 2 = 0 := by
          rw [Nat.mod_mod_of_dvd _ h2]; exact hmod
        omega
      have hdm := Nat.div_add_mod (u / 2 ^ j) (2 ^ (i - j))
      have : u / 2 ^ j + 1 = 2 ^ (i - j) * (u / 2 ^ j / 2 ^ (i - j)) + (u / 2 ^ j % 2 ^ (i - j) + 1) := by
        omega
      rw [this, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hrem, Nat.add_zero]
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, hdiv]

lemma testBit_flipBit (j u i : ℕ) :
    (flipBit j u).testBit i = if i = j then !(u.testBit j) else u.testBit i := by
  unfold flipBit
  cases hb : u.testBit j
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    by_cases hij : i = j
    · subst hij; simp [testBit_add_two_pow_same hb]
    · simp only [hij, ↓reduceIte]
      exact testBit_add_two_pow_ne hb hij
  · simp only [↓reduceIte, Bool.not_true]
    have hge := testBit_true_ge hb
    have hsub := testBit_sub_two_pow_same hb
    by_cases hij : i = j
    · subst hij; simpa using hsub
    · simp only [hij, ↓reduceIte]
      have hne := testBit_add_two_pow_ne hsub hij
      rw [Nat.sub_add_cancel hge] at hne
      exact hne.symm

lemma testBit_sub_two_pow (u k i : ℕ) (hge : 2 ^ k ≤ u) :
    (u - 2 ^ k).testBit i =
      if i < k then u.testBit i
      else xor (u.testBit i) (decide (∀ r, k ≤ r → r < i → u.testBit r = false)) := by
  by_cases hik : i < k
  · simp only [hik, ↓reduceIte]
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
    have hpow : 2 ^ k = 2 * 2 ^ (k - 1 - i) * 2 ^ i := by
      rw [← pow_succ', ← pow_add]; congr 1; omega
    have hu_eq : u = (u - 2 ^ k) + 2 * 2 ^ (k - 1 - i) * 2 ^ i := by
      rw [← hpow, Nat.sub_add_cancel hge]
    have hdiv : u / 2 ^ i = (u - 2 ^ k) / 2 ^ i + 2 * 2 ^ (k - 1 - i) := by
      conv_lhs => rw [hu_eq]
      rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos i)]
    rw [hdiv]
    simp [Nat.add_mul_mod_self_left]
  · simp only [hik, ↓reduceIte]
    set j := i - k
    have hi_eq : i = k + j := by omega
    set q := u / 2 ^ k
    have hq_pos : 1 ≤ q := by
      have := Nat.div_le_div_right (c := 2 ^ k) hge
      rw [Nat.div_self (Nat.two_pow_pos k)] at this
      exact this
    have hsub_div1 : (u - 2 ^ k) / 2 ^ k + 1 = q := by
      have := Nat.add_div_right (u - 2 ^ k) (Nat.two_pow_pos k)
      rw [Nat.sub_add_cancel hge] at this
      exact this.symm
    have hsub_div : (u - 2 ^ k) / 2 ^ k = q - 1 := Nat.eq_sub_of_add_eq hsub_div1
    have htb_q : ∀ r, u.testBit (k + r) = q.testBit r := by
      intro r
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
        pow_add, ← Nat.div_div_eq_div_mul]
    have htb_qm : (u - 2 ^ k).testBit (k + j) = (q - 1).testBit j := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
        pow_add, ← Nat.div_div_eq_div_mul, hsub_div]
    have hall : (∀ r, k ≤ r → r < k + j → u.testBit r = false) ↔ q % 2 ^ j = 0 := by
      constructor
      · intro h
        apply Nat.eq_of_testBit_eq
        intro r
        rw [Nat.zero_testBit, Nat.testBit_mod_two_pow]
        by_cases hr : r < j
        · simp only [hr, decide_true, Bool.true_and, ← htb_q r]
          exact h (k + r) (by omega) (by omega)
        · simp [hr]
      · intro h r hkr hrlt
        have hr' : r = k + (r - k) := by omega
        rw [hr', htb_q]
        have hlt : r - k < j := by omega
        have := congrArg (fun n => n.testBit (r - k)) h
        simp [Nat.testBit_mod_two_pow, hlt] at this
        exact this
    rw [hi_eq, htb_qm, htb_q j]
    have hdec : decide (∀ r, k ≤ r → r < k + j → u.testBit r = false) = decide (q % 2 ^ j = 0) :=
      decide_eq_decide.mpr hall
    rw [hdec]
    set a := q / 2 ^ j
    set b := q % 2 ^ j
    have hdm : 2 ^ j * a + b = q := Nat.div_add_mod q (2 ^ j)
    have hblt : b < 2 ^ j := Nat.mod_lt q (Nat.two_pow_pos j)
    by_cases hb0 : b = 0
    · simp only [hb0, decide_true, Bool.xor_true]
      have ha_pos : 1 ≤ a := by
        cases ha : a with
        | zero =>
          rw [ha, hb0] at hdm
          simp at hdm
          omega
        | succ _ => exact Nat.succ_le_succ (Nat.zero_le _)
      have hqm : q - 1 = 2 ^ j * (a - 1) + (2 ^ j - 1) := by
        have h1 : 1 ≤ 2 ^ j := Nat.two_pow_pos j
        have h2 : 2 ^ j * a = 2 ^ j * (a - 1) + 2 ^ j := by
          conv_lhs => rw [show a = (a - 1) + 1 by omega, Nat.mul_add, Nat.mul_one]
        omega
      have hdiv_qm : (q - 1) / 2 ^ j = a - 1 := by
        rw [hqm, Nat.mul_add_div (Nat.two_pow_pos j),
          Nat.div_eq_of_lt (by have := Nat.two_pow_pos j; omega), Nat.add_zero]
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, hdiv_qm]
      change decide ((a - 1) % 2 = 1) = !(decide (a % 2 = 1))
      cases hpar : decide (a % 2 = 1)
      · simp at hpar ⊢; omega
      · simp at hpar ⊢; omega
    · simp only [hb0, decide_false, Bool.xor_false]
      have hqm : q - 1 = 2 ^ j * a + (b - 1) := by omega
      have hdiv_qm : (q - 1) / 2 ^ j = a := by
        rw [hqm, Nat.mul_add_div (Nat.two_pow_pos j),
          Nat.div_eq_of_lt (by omega), Nat.add_zero]
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, hdiv_qm]

def bitonicSchedule (p : ℕ) : List (ℕ × ℕ) :=
  (List.range p).flatMap fun k =>
    (List.range (k + 1)).reverse.map fun j => (k, j)

lemma bitonicSchedule_mem_lt (p : ℕ) :
    ∀ e ∈ bitonicSchedule p, e.2 ≤ e.1 ∧ e.1 < p := by
  intro e he
  simp only [bitonicSchedule, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_reverse] at he
  rcases he with ⟨k, hk, j, hj, rfl⟩
  exact ⟨by omega, hk⟩

lemma bitonicSchedule_lt (p : ℕ) : ∀ e ∈ bitonicSchedule p, e.2 < p :=
  fun e he => lt_of_le_of_lt (bitonicSchedule_mem_lt p e he).1 (bitonicSchedule_mem_lt p e he).2

lemma bitonicSchedule_length_mul_two (p : ℕ) :
    2 * (bitonicSchedule p).length = p * (p + 1) := by
  induction p with
  | zero => simp [bitonicSchedule]
  | succ p ih =>
    unfold bitonicSchedule
    rw [List.range_succ, List.flatMap_append, List.length_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_map,
      List.length_reverse, List.length_range]
    unfold bitonicSchedule at ih
    linarith

def applyLayer {α : Type*} [LinearOrder α] (p k j : ℕ) (hj : j < p) (arr : Fin (2 ^ p) → α) :
    Fin (2 ^ p) → α :=
  fun u =>
    let a := loBit j u.val
    let b := a + 2 ^ j
    let va := arr ⟨a, loBit_lt u.isLt⟩
    let vb := arr ⟨b, loBit_two_pow_add_lt u.isLt hj⟩
    let asc := !(a.testBit (k + 1))
    if u.val.testBit j then
      if asc then max va vb else min va vb
    else
      if asc then min va vb else max va vb

def applySchedule {α : Type*} [LinearOrder α] (p : ℕ) :
    (sched : List (ℕ × ℕ)) → (∀ e ∈ sched, e.2 < p) →
    (Fin (2 ^ p) → α) → (Fin (2 ^ p) → α)
  | [], _, arr => arr
  | e :: es, h, arr =>
    applySchedule p es (fun x hx => h x (by simp [hx]))
      (applyLayer p e.1 e.2 (h e (by simp)) arr)

lemma applySchedule_congr {α : Type*} [LinearOrder α] (p : ℕ)
    {s1 s2 : List (ℕ × ℕ)} (heq : s1 = s2)
    (h1 : ∀ e ∈ s1, e.2 < p) (h2 : ∀ e ∈ s2, e.2 < p) (arr : Fin (2 ^ p) → α) :
    applySchedule p s1 h1 arr = applySchedule p s2 h2 arr := by
  subst heq
  rfl

lemma applySchedule_append {α : Type*} [LinearOrder α] (p : ℕ)
    (s1 s2 : List (ℕ × ℕ)) (h1 : ∀ e ∈ s1, e.2 < p) (h2 : ∀ e ∈ s2, e.2 < p)
    (arr : Fin (2 ^ p) → α) :
    applySchedule p (s1 ++ s2)
      (fun e he => by simp at he; rcases he with h | h; exact h1 e h; exact h2 e h) arr =
    applySchedule p s2 h2 (applySchedule p s1 h1 arr) := by
  induction s1 generalizing arr with
  | nil => rfl
  | cons e es ih =>
    simp only [List.cons_append, applySchedule]
    exact ih (fun x hx => h1 x (by simp [hx])) _

lemma applyLayer_map_mono {α β : Type*} [LinearOrder α] [LinearOrder β]
    (φ : α → β) (hφ : Monotone φ) (p k j : ℕ) (hj : j < p) (arr : Fin (2 ^ p) → α) :
    applyLayer p k j hj (fun u => φ (arr u)) = fun u => φ (applyLayer p k j hj arr u) := by
  funext u
  unfold applyLayer
  dsimp only
  split <;> split <;> simp [hφ.map_max, hφ.map_min]

lemma applySchedule_map_mono {α β : Type*} [LinearOrder α] [LinearOrder β]
    (φ : α → β) (hφ : Monotone φ) (p : ℕ)
    (sched : List (ℕ × ℕ)) (hs : ∀ e ∈ sched, e.2 < p) (arr : Fin (2 ^ p) → α) :
    applySchedule p sched hs (fun u => φ (arr u)) =
      fun u => φ (applySchedule p sched hs arr u) := by
  induction sched generalizing arr with
  | nil => rfl
  | cons e es ih =>
    simp only [applySchedule]
    rw [applyLayer_map_mono φ hφ, ih]

def IsBitonicSlice (v : ℕ → Bool) (base len : ℕ) : Prop :=
  (∃ l r, l ≤ r ∧ r ≤ len ∧ ∀ i < len, v (base + i) = true ↔ l ≤ i ∧ i < r) ∨
  (∃ l r, l ≤ r ∧ r ≤ len ∧ ∀ i < len, v (base + i) = false ↔ l ≤ i ∧ i < r)

def IsSortedSlice (v : ℕ → Bool) (base len : ℕ) (asc : Bool) : Prop :=
  ∀ i j, i ≤ j → j < len →
    if asc then v (base + i) ≤ v (base + j) else v (base + j) ≤ v (base + i)

lemma bitonic_of_asc_desc (v : ℕ → Bool) (base h : ℕ)
    (hasc : IsSortedSlice v base h true)
    (hdesc : IsSortedSlice v (base + h) h false) :
    IsBitonicSlice v base (2 * h) := by
  left
  have hexL : ∃ l, l ≤ h ∧ ∀ i < h, v (base + i) = true ↔ l ≤ i := by
    by_cases hall : ∀ i < h, v (base + i) = false
    · refine ⟨h, le_refl h, ?_⟩
      intro i hi
      simp [hall i hi]; omega
    · push Not at hall
      have hne : ∃ i, i < h ∧ v (base + i) = true := by
        rcases hall with ⟨i, hi, hne⟩
        exact ⟨i, hi, by cases hv : v (base + i) <;> simp_all⟩
      classical
      let l := Nat.find hne
      have hl : l < h ∧ v (base + l) = true := Nat.find_spec hne
      refine ⟨l, le_of_lt hl.1, ?_⟩
      intro i hi
      constructor
      · intro hv
        by_contra hlt
        exact Nat.find_min hne (by omega) ⟨hi, hv⟩
      · intro hle
        have hmono := hasc l i hle hi
        simp only [↓reduceIte, hl.2] at hmono
        cases hv : v (base + i)
        · rw [hv] at hmono; exact Bool.noConfusion (hmono rfl)
        · rfl
  have hexR : ∃ r, r ≤ h ∧ ∀ i < h, v (base + h + i) = true ↔ i < r := by
    by_cases hall : ∀ i < h, v (base + h + i) = true
    · refine ⟨h, le_refl h, ?_⟩
      intro i hi; simp [hall i hi, hi]
    · push Not at hall
      have hne : ∃ i, i < h ∧ v (base + h + i) = false := by
        rcases hall with ⟨i, hi, hne⟩
        exact ⟨i, hi, by cases hv : v (base + h + i) <;> simp_all⟩
      classical
      let r := Nat.find hne
      have hr : r < h ∧ v (base + h + r) = false := Nat.find_spec hne
      refine ⟨r, le_of_lt hr.1, ?_⟩
      intro i hi
      constructor
      · intro hv
        by_contra hge
        have hmono := hdesc r i (by omega) hi
        simp only [Bool.false_eq_true, ↓reduceIte, hr.2, hv] at hmono
        exact Bool.noConfusion (hmono rfl)
      · intro hlt
        have hnot := Nat.find_min hne hlt
        cases hv : v (base + h + i)
        · exact absurd ⟨hi, hv⟩ hnot
        · rfl
  rcases hexL with ⟨l, hlh, hL⟩
  rcases hexR with ⟨r, hrh, hR⟩
  refine ⟨l, h + r, by omega, by omega, ?_⟩
  intro i hi
  by_cases hil : i < h
  · rw [hL i hil]; omega
  · have hi' : i - h < h := by omega
    have hadd : base + i = base + h + (i - h) := by omega
    rw [hadd, hR (i - h) hi']
    omega

lemma bitonic_split_bool (v : ℕ → Bool) (base h : ℕ) (asc : Bool)
    (hbit : IsBitonicSlice v base (2 * h)) :
    let v' : ℕ → Bool := fun x =>
      if x < base + h then
        if asc then min (v x) (v (x + h)) else max (v x) (v (x + h))
      else
        if asc then max (v (x - h)) (v x) else min (v (x - h)) (v x)
    IsBitonicSlice v' base h ∧ IsBitonicSlice v' (base + h) h ∧
    ((∀ i < h, v' (base + i) = !asc) ∨ (∀ i < h, v' (base + h + i) = asc)) := by
  have core : ∀ (w : ℕ → Bool),
      (∃ l r, l ≤ r ∧ r ≤ 2 * h ∧ ∀ i < 2 * h, w (base + i) = true ↔ l ≤ i ∧ i < r) →
      let wL : ℕ → Bool := fun x => min (w x) (w (x + h))
      let wR : ℕ → Bool := fun x => max (w (x - h)) (w x)
      IsBitonicSlice wL base h ∧ IsBitonicSlice wR (base + h) h ∧
      ((∀ i < h, wL (base + i) = false) ∨ (∀ i < h, wR (base + h + i) = true)) := by
    intro w ⟨l, r, hlr, hr2, hw⟩
    dsimp only
    by_cases hlen : r - l ≤ h
    · refine ⟨?_, ?_, Or.inl ?_⟩
      · left; refine ⟨0, 0, le_refl 0, Nat.zero_le h, ?_⟩
        intro i hi
        dsimp only
        have h1 := hw i (by omega)
        have h2 := hw (i + h) (by omega)
        have hadd : base + i + h = base + (i + h) := by omega
        rw [hadd]
        cases ha : w (base + i) <;> cases hb : w (base + (i + h)) <;> simp_all; omega
      · by_cases hr_le : r ≤ h
        · left; refine ⟨l, r, hlr, hr_le, ?_⟩
          intro i hi
          dsimp only
          have h1 := hw i (by omega)
          have h2 := hw (i + h) (by omega)
          have hsub : base + h + i - h = base + i := by omega
          have hadd : base + h + i = base + (i + h) := by omega
          rw [hsub, hadd]
          cases ha : w (base + i) <;> cases hb : w (base + (i + h)) <;> simp_all; omega
        · by_cases hl_ge : h ≤ l
          · left; refine ⟨l - h, r - h, by omega, by omega, ?_⟩
            intro i hi
            dsimp only
            have h1 := hw i (by omega)
            have h2 := hw (i + h) (by omega)
            have hsub : base + h + i - h = base + i := by omega
            have hadd : base + h + i = base + (i + h) := by omega
            rw [hsub, hadd]
            cases ha : w (base + i) <;> cases hb : w (base + (i + h)) <;> simp_all <;> omega
          · right; refine ⟨r - h, l, by omega, by omega, ?_⟩
            intro i hi
            dsimp only
            have h1 := hw i (by omega)
            have h2 := hw (i + h) (by omega)
            have hsub : base + h + i - h = base + i := by omega
            have hadd : base + h + i = base + (i + h) := by omega
            rw [hsub, hadd]
            cases ha : w (base + i) <;> cases hb : w (base + (i + h)) <;> simp_all; omega
      · intro i hi
        have h1 := hw i (by omega)
        have h2 := hw (i + h) (by omega)
        have hadd : base + i + h = base + (i + h) := by omega
        rw [hadd]
        cases ha : w (base + i) <;> cases hb : w (base + (i + h)) <;> simp_all; omega
    · refine ⟨?_, ?_, Or.inr ?_⟩
      · left; refine ⟨l, r - h, by omega, by omega, ?_⟩
        intro i hi
        dsimp only
        have h1 := hw i (by omega)
        have h2 := hw (i + h) (by omega)
        have hadd : base + i + h = base + (i + h) := by omega
        rw [hadd]
        cases ha : w (base + i) <;> cases hb : w (base + (i + h)) <;> simp_all <;> omega
      · left; refine ⟨0, h, Nat.zero_le h, le_refl h, ?_⟩
        intro i hi
        dsimp only
        have h1 := hw i (by omega)
        have h2 := hw (i + h) (by omega)
        have hsub : base + h + i - h = base + i := by omega
        have hadd : base + h + i = base + (i + h) := by omega
        rw [hsub, hadd]
        cases ha : w (base + i) <;> cases hb : w (base + (i + h)) <;> simp_all; omega
      · intro i hi
        have h1 := hw i (by omega)
        have h2 := hw (i + h) (by omega)
        have hsub : base + h + i - h = base + i := by omega
        have hadd : base + h + i = base + (i + h) := by omega
        rw [hsub, hadd]
        cases ha : w (base + i) <;> cases hb : w (base + (i + h)) <;> simp_all; omega
  have bitonic_congr : ∀ {f g : ℕ → Bool} {b n : ℕ},
      (∀ i < n, f (b + i) = g (b + i)) → IsBitonicSlice f b n → IsBitonicSlice g b n := by
    intro f g b n heq hf
    rcases hf with ⟨l, r, h1, h2, h3⟩ | ⟨l, r, h1, h2, h3⟩
    · left; refine ⟨l, r, h1, h2, fun i hi => by rw [← heq i hi]; exact h3 i hi⟩
    · right; refine ⟨l, r, h1, h2, fun i hi => by rw [← heq i hi]; exact h3 i hi⟩
  have bitonic_not : ∀ {f : ℕ → Bool} {b n : ℕ},
      IsBitonicSlice f b n → IsBitonicSlice (fun x => !(f x)) b n := by
    intro f b n hf
    rcases hf with ⟨l, r, h1, h2, h3⟩ | ⟨l, r, h1, h2, h3⟩
    · right; refine ⟨l, r, h1, h2, fun i hi => by simp [h3 i hi]⟩
    · left; refine ⟨l, r, h1, h2, fun i hi => by simp [h3 i hi]⟩
  have bitonic_shift : ∀ {f g : ℕ → Bool} {b1 b2 n : ℕ},
      (∀ i < n, f (b1 + i) = g (b2 + i)) → IsBitonicSlice f b1 n → IsBitonicSlice g b2 n := by
    intro f g b1 b2 n heq hf
    rcases hf with ⟨l, r, h1, h2, h3⟩ | ⟨l, r, h1, h2, h3⟩
    · left; refine ⟨l, r, h1, h2, fun i hi => by rw [← heq i hi]; exact h3 i hi⟩
    · right; refine ⟨l, r, h1, h2, fun i hi => by rw [← heq i hi]; exact h3 i hi⟩
  have not_min : ∀ a b : Bool, (!(min (!a) (!b))) = max a b := by decide
  have not_max : ∀ a b : Bool, (!(max (!a) (!b))) = min a b := by decide
  cases asc
  · rcases hbit with hpos | hneg
    · have hc2 := core v hpos
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · exact bitonic_shift (fun i hi => by
          simp only [show base + i < base + h by omega, Bool.false_eq_true, ↓reduceIte]
          have hsub : base + h + i - h = base + i := by omega
          have hadd : base + h + i = base + i + h := by omega
          rw [hsub, hadd]) hc2.2.1
      · exact bitonic_shift (fun i hi => by
          simp only [show ¬ (base + h + i < base + h) by omega, Bool.false_eq_true, ↓reduceIte]
          have hsub : base + h + i - h = base + i := by omega
          have hadd : base + h + i = base + i + h := by omega
          rw [hsub, hadd]) hc2.1
      · rcases hc2.2.2 with hL | hR
        · right; intro i hi
          simp only [show ¬ (base + h + i < base + h) by omega, Bool.false_eq_true, ↓reduceIte]
          have hsub : base + h + i - h = base + i := by omega
          have hadd : base + h + i = base + i + h := by omega
          rw [hsub, hadd]; exact hL i hi
        · left; intro i hi
          simp only [show base + i < base + h by omega, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
          have hsub : base + h + i - h = base + i := by omega
          have hadd : base + h + i = base + i + h := by omega
          have := hR i hi; dsimp only at this; rw [hsub, hadd] at this; exact this
    · have hnot : ∃ l r, l ≤ r ∧ r ≤ 2 * h ∧ ∀ i < 2 * h, (!(v (base + i))) = true ↔ l ≤ i ∧ i < r := by
        rcases hneg with ⟨l, r, h1, h2, h3⟩
        exact ⟨l, r, h1, h2, fun i hi => by simp [h3 i hi]⟩
      have hc := core (fun x => !(v x)) hnot
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · exact bitonic_congr (fun i hi => by
          simp only [show base + i < base + h by omega, Bool.false_eq_true, ↓reduceIte]
          exact not_min (v (base + i)) (v (base + i + h))) (bitonic_not hc.1)
      · exact bitonic_congr (fun i hi => by
          simp only [show ¬ (base + h + i < base + h) by omega, Bool.false_eq_true, ↓reduceIte]
          exact not_max (v (base + h + i - h)) (v (base + h + i))) (bitonic_not hc.2.1)
      · rcases hc.2.2 with hL | hR
        · left; intro i hi
          simp only [show base + i < base + h by omega, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
          have := hL i hi; dsimp only at this
          rw [← not_min, this]; rfl
        · right; intro i hi
          simp only [show ¬ (base + h + i < base + h) by omega, Bool.false_eq_true, ↓reduceIte]
          have := hR i hi; dsimp only at this
          rw [← not_max, this]; rfl
  · rcases hbit with hpos | hneg
    · have hc := core v hpos
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · exact bitonic_congr (fun i hi => by simp [show base + i < base + h by omega]) hc.1
      · exact bitonic_congr (fun i hi => by simp [show ¬ (base + h + i < base + h) by omega]) hc.2.1
      · rcases hc.2.2 with hL | hR
        · left; intro i hi; simp [show base + i < base + h by omega, hL i hi]
        · right; intro i hi; simp [show ¬ (base + h + i < base + h) by omega, hR i hi]
    · have hnot : ∃ l r, l ≤ r ∧ r ≤ 2 * h ∧ ∀ i < 2 * h, (!(v (base + i))) = true ↔ l ≤ i ∧ i < r := by
        rcases hneg with ⟨l, r, h1, h2, h3⟩
        exact ⟨l, r, h1, h2, fun i hi => by simp [h3 i hi]⟩
      have hc := core (fun x => !(v x)) hnot
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · exact bitonic_shift (fun i hi => by
          simp only [show base + i < base + h by omega, ↓reduceIte]
          have hsub : base + h + i - h = base + i := by omega
          have hadd : base + h + i = base + i + h := by omega
          rw [hsub, hadd]
          exact not_max (v (base + i)) (v (base + i + h))) (bitonic_not hc.2.1)
      · exact bitonic_shift (fun i hi => by
          simp only [show ¬ (base + h + i < base + h) by omega, ↓reduceIte]
          have hsub : base + h + i - h = base + i := by omega
          have hadd : base + h + i = base + i + h := by omega
          rw [hsub, hadd]
          exact not_min (v (base + i)) (v (base + i + h))) (bitonic_not hc.1)
      · rcases hc.2.2 with hL | hR
        · right; intro i hi
          simp only [show ¬ (base + h + i < base + h) by omega, ↓reduceIte]
          have hsub : base + h + i - h = base + i := by omega
          have hadd : base + h + i = base + i + h := by omega
          have := hL i hi; dsimp only at this
          rw [hsub, hadd, ← not_min, this]; rfl
        · left; intro i hi
          simp only [show base + i < base + h by omega, ↓reduceIte, Bool.not_true]
          have hsub : base + h + i - h = base + i := by omega
          have hadd : base + h + i = base + i + h := by omega
          have := hR i hi; dsimp only at this; rw [hsub, hadd] at this
          rw [← not_max, this]; rfl

def arrFun {p : ℕ} (arr : Fin (2 ^ p) → Bool) (x : ℕ) : Bool :=
  if h : x < 2 ^ p then arr ⟨x, h⟩ else false

lemma applyLayer_const_block (p k j m : ℕ) (hj : j < p) (hjm : j < m)
    (arr : Fin (2 ^ p) → Bool) (q : ℕ) (hq : (q + 1) * 2 ^ m ≤ 2 ^ p) (c : Bool)
    (hc : ∀ i < 2 ^ m, arrFun arr (q * 2 ^ m + i) = c) :
    ∀ i < 2 ^ m, arrFun (applyLayer p k j hj arr) (q * 2 ^ m + i) = c := by
  intro i hi
  have hx : q * 2 ^ m + i < 2 ^ p := by
    have : (q + 1) * 2 ^ m = q * 2 ^ m + 2 ^ m := by ring
    omega
  simp only [arrFun, hx, ↓reduceDIte, applyLayer]
  have hlo : loBit j (q * 2 ^ m + i) = q * 2 ^ m + loBit j i := by
    unfold loBit
    have htb : (q * 2 ^ m + i).testBit j = i.testBit j := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
      have hpow : 2 ^ m = 2 ^ j * (2 * 2 ^ (m - 1 - j)) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      have hmul : q * 2 ^ m = 2 ^ j * (2 * (q * 2 ^ (m - 1 - j))) := by rw [hpow]; ring
      rw [hmul, Nat.mul_add_div (Nat.two_pow_pos j)]
      simp
    rw [htb]
    cases hb : i.testBit j
    · rfl
    · have hge := testBit_true_ge hb
      simp; omega
  have ha_lt : loBit j i < 2 ^ m := lt_of_le_of_lt (loBit_le j i) hi
  have hb_lt : loBit j i + 2 ^ j < 2 ^ m :=
    two_pow_add_lt ha_lt hjm (loBit_testBit_false j i)
  have hva : arr ⟨loBit j (q * 2 ^ m + i), loBit_lt hx⟩ = c := by
    have h1 := hc (loBit j i) ha_lt
    have hx1 : q * 2 ^ m + loBit j i < 2 ^ p := by
      have : (q + 1) * 2 ^ m = q * 2 ^ m + 2 ^ m := by ring
      omega
    simp only [arrFun, hx1, ↓reduceDIte] at h1
    simpa [hlo] using h1
  have hvb : arr ⟨loBit j (q * 2 ^ m + i) + 2 ^ j, loBit_two_pow_add_lt hx hj⟩ = c := by
    have h1 := hc (loBit j i + 2 ^ j) hb_lt
    have hx1 : q * 2 ^ m + (loBit j i + 2 ^ j) < 2 ^ p := by
      have : (q + 1) * 2 ^ m = q * 2 ^ m + 2 ^ m := by ring
      omega
    simp only [arrFun, hx1, ↓reduceDIte] at h1
    have hadd : loBit j (q * 2 ^ m + i) + 2 ^ j = q * 2 ^ m + (loBit j i + 2 ^ j) := by omega
    simpa [hadd] using h1
  rw [hva, hvb]
  split <;> split <;> simp

lemma applyLayer_split_block (p k m : ℕ) (hmk : m ≤ k) (hkp : k < p)
    (arr : Fin (2 ^ p) → Bool) (q : ℕ) (hq : (q + 1) * 2 ^ (m + 1) ≤ 2 ^ p) :
    let asc := !((q * 2 ^ (m + 1)).testBit (k + 1))
    let arr' := applyLayer p k m (by omega) arr
    ∀ i < 2 ^ (m + 1),
      arrFun arr' (q * 2 ^ (m + 1) + i) =
        if q * 2 ^ (m + 1) + i < q * 2 ^ (m + 1) + 2 ^ m then
          if asc then min (arrFun arr (q * 2 ^ (m + 1) + i)) (arrFun arr (q * 2 ^ (m + 1) + i + 2 ^ m))
          else max (arrFun arr (q * 2 ^ (m + 1) + i)) (arrFun arr (q * 2 ^ (m + 1) + i + 2 ^ m))
        else
          if asc then max (arrFun arr (q * 2 ^ (m + 1) + i - 2 ^ m)) (arrFun arr (q * 2 ^ (m + 1) + i))
          else min (arrFun arr (q * 2 ^ (m + 1) + i - 2 ^ m)) (arrFun arr (q * 2 ^ (m + 1) + i)) := by
  intro asc arr' i hi
  have hx : q * 2 ^ (m + 1) + i < 2 ^ p := by
    have : (q + 1) * 2 ^ (m + 1) = q * 2 ^ (m + 1) + 2 ^ (m + 1) := by ring
    omega
  have htb_m : (q * 2 ^ (m + 1) + i).testBit m = decide (2 ^ m ≤ i) := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ']
    have hmul : q * 2 ^ (m + 1) = 2 ^ m * (2 * q) := by rw [hpow]; ring
    rw [hmul, Nat.mul_add_div (Nat.two_pow_pos m)]
    have hdiv_i : i / 2 ^ m = if 2 ^ m ≤ i then 1 else 0 := by
      split
      · have h1 : 1 ≤ i / 2 ^ m := by
          have := Nat.div_le_div_right (c := 2 ^ m) ‹2 ^ m ≤ i›
          rwa [Nat.div_self (Nat.two_pow_pos m)] at this
        have h2 : i / 2 ^ m < 2 := by
          rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos m), ← hpow]; exact hi
        omega
      · exact Nat.div_eq_of_lt (by omega)
    rw [hdiv_i]
    split
    · simp; omega
    · simp; omega
  have hlo : loBit m (q * 2 ^ (m + 1) + i) =
      if i < 2 ^ m then q * 2 ^ (m + 1) + i else q * 2 ^ (m + 1) + i - 2 ^ m := by
    unfold loBit
    rw [htb_m]
    by_cases hlt : i < 2 ^ m
    · simp [hlt, show ¬ (2 ^ m ≤ i) by omega]
    · simp [hlt, show 2 ^ m ≤ i by omega]
  have hasc : (loBit m (q * 2 ^ (m + 1) + i)).testBit (k + 1) =
      (q * 2 ^ (m + 1)).testBit (k + 1) := by
    have hlo_eq : loBit m (q * 2 ^ (m + 1) + i) = q * 2 ^ (m + 1) + (if i < 2 ^ m then i else i - 2 ^ m) := by
      rw [hlo]; split <;> omega
    rw [hlo_eq]
    set r := if i < 2 ^ m then i else i - 2 ^ m
    have hr : r < 2 ^ (m + 1) := by dsimp [r]; split <;> omega
    have hdvd : 2 ^ (m + 1) ∣ 2 ^ (k + 1) := Nat.pow_dvd_pow 2 (by omega)
    rcases hdvd with ⟨t, ht⟩
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
    have hdiv : (q * 2 ^ (m + 1) + r) / 2 ^ (k + 1) = (q * 2 ^ (m + 1)) / 2 ^ (k + 1) := by
      rw [ht, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
      rw [Nat.mul_comm q (2 ^ (m + 1)), Nat.mul_add_div (Nat.two_pow_pos (m + 1)),
        Nat.div_eq_of_lt hr, Nat.add_zero, Nat.mul_div_right q (Nat.two_pow_pos (m + 1))]
    rw [hdiv]
  simp only [arr', arrFun, hx, ↓reduceDIte, applyLayer, hasc]
  dsimp only [asc]
  by_cases hlt : i < 2 ^ m
  · have hlt' : q * 2 ^ (m + 1) + i < q * 2 ^ (m + 1) + 2 ^ m := by omega
    have hxb : q * 2 ^ (m + 1) + i + 2 ^ m < 2 ^ p := by
      have : (q + 1) * 2 ^ (m + 1) = q * 2 ^ (m + 1) + 2 ^ (m + 1) := by ring
      have : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; omega
      omega
    simp only [htb_m, show ¬ (2 ^ m ≤ i) by omega, decide_false, Bool.false_eq_true, ↓reduceIte,
      hlt', hxb, ↓reduceDIte]
    have hlo1 : loBit m (q * 2 ^ (m + 1) + i) = q * 2 ^ (m + 1) + i := by rw [hlo]; simp [hlt]
    simp [hlo1]
  · have hlt' : ¬ (q * 2 ^ (m + 1) + i < q * 2 ^ (m + 1) + 2 ^ m) := by omega
    have hxa : q * 2 ^ (m + 1) + i - 2 ^ m < 2 ^ p := by omega
    simp only [htb_m, show 2 ^ m ≤ i by omega, decide_true, ↓reduceIte, hlt', hxa, ↓reduceDIte]
    have hlo1 : loBit m (q * 2 ^ (m + 1) + i) = q * 2 ^ (m + 1) + i - 2 ^ m := by rw [hlo]; simp [hlt]
    have hlo2 : loBit m (q * 2 ^ (m + 1) + i) + 2 ^ m = q * 2 ^ (m + 1) + i := by omega
    have hfa : (⟨loBit m (q * 2 ^ (m + 1) + i), loBit_lt hx⟩ : Fin (2 ^ p)) =
        ⟨q * 2 ^ (m + 1) + i - 2 ^ m, hxa⟩ := by ext; exact hlo1
    have hfb : (⟨loBit m (q * 2 ^ (m + 1) + i) + 2 ^ m, loBit_two_pow_add_lt hx (by omega)⟩ : Fin (2 ^ p)) =
        ⟨q * 2 ^ (m + 1) + i, hx⟩ := by ext; exact hlo2
    rw [hfa, hfb]

def mergeSched (k m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).reverse.map fun j => (k, j)

lemma mergeSched_lt (p k m : ℕ) (hmp : m ≤ p) :
    ∀ e ∈ mergeSched k m, e.2 < p := by
  intro e he
  simp only [mergeSched, List.mem_map, List.mem_reverse, List.mem_range] at he
  rcases he with ⟨j, hj, rfl⟩
  omega

lemma mergeSched_succ (k m : ℕ) : mergeSched k (m + 1) = (k, m) :: mergeSched k m := by
  simp [mergeSched, List.range_succ]

lemma mergeSched_const_block (p k m r : ℕ) (hmp : m ≤ p) (hmr : m ≤ r)
    (arr : Fin (2 ^ p) → Bool) (q : ℕ) (hq : (q + 1) * 2 ^ r ≤ 2 ^ p) (c : Bool)
    (hc : ∀ i < 2 ^ r, arrFun arr (q * 2 ^ r + i) = c) :
    ∀ i < 2 ^ r, arrFun (applySchedule p (mergeSched k m) (mergeSched_lt p k m hmp) arr) (q * 2 ^ r + i) = c := by
  induction m generalizing arr with
  | zero => exact hc
  | succ m ih =>
    have heq : applySchedule p (mergeSched k (m + 1)) (mergeSched_lt p k (m + 1) hmp) arr =
        applySchedule p (mergeSched k m) (mergeSched_lt p k m (by omega))
          (applyLayer p k m (by omega) arr) := by
      have h1 := applySchedule_congr p (mergeSched_succ k m)
        (mergeSched_lt p k (m + 1) hmp)
        (fun e he => by simp at he; rcases he with rfl | h; omega; exact mergeSched_lt p k m (by omega) e h) arr
      exact h1
    rw [heq]
    exact ih (by omega) (by omega) _ (applyLayer_const_block p k m r (by omega) (by omega) arr q hq c hc)

lemma mergeSched_bitonic_bool (p k m : ℕ) (hmk : m ≤ k + 1) (hkp : k < p)
    (arr : Fin (2 ^ p) → Bool)
    (hbit : ∀ q, (q + 1) * 2 ^ m ≤ 2 ^ p → IsBitonicSlice (arrFun arr) (q * 2 ^ m) (2 ^ m)) :
    ∀ q, (q + 1) * 2 ^ m ≤ 2 ^ p →
      IsSortedSlice (arrFun (applySchedule p (mergeSched k m) (mergeSched_lt p k m (by omega)) arr))
        (q * 2 ^ m) (2 ^ m) (!((q * 2 ^ m).testBit (k + 1))) := by
  induction m generalizing arr with
  | zero =>
    intro q hq i j hij hjlt
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0
    split <;> exact le_refl _
  | succ m ih =>
    have heq : applySchedule p (mergeSched k (m + 1)) (mergeSched_lt p k (m + 1) (by omega)) arr =
        applySchedule p (mergeSched k m) (mergeSched_lt p k m (by omega))
          (applyLayer p k m (by omega) arr) := by
      have h1 := applySchedule_congr p (mergeSched_succ k m)
        (mergeSched_lt p k (m + 1) (by omega))
        (fun e he => by simp at he; rcases he with rfl | h; omega; exact mergeSched_lt p k m (by omega) e h) arr
      exact h1
    rw [heq]
    set arr1 := applyLayer p k m (by omega) arr
    have hsplit : ∀ q, (q + 1) * 2 ^ (m + 1) ≤ 2 ^ p →
        let asc := !((q * 2 ^ (m + 1)).testBit (k + 1))
        IsBitonicSlice (arrFun arr1) (q * 2 ^ (m + 1)) (2 ^ m) ∧
        IsBitonicSlice (arrFun arr1) (q * 2 ^ (m + 1) + 2 ^ m) (2 ^ m) ∧
        ((∀ i < 2 ^ m, arrFun arr1 (q * 2 ^ (m + 1) + i) = !asc) ∨
         (∀ i < 2 ^ m, arrFun arr1 (q * 2 ^ (m + 1) + 2 ^ m + i) = asc)) := by
      intro q hq
      have h2m : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ']
      have hb0 : IsBitonicSlice (arrFun arr) (q * 2 ^ (m + 1)) (2 * 2 ^ m) := by
        rw [← h2m]; exact hbit q hq
      have hbs := bitonic_split_bool (arrFun arr) (q * 2 ^ (m + 1)) (2 ^ m)
        (!((q * 2 ^ (m + 1)).testBit (k + 1))) hb0
      have heq1 := applyLayer_split_block p k m (by omega) hkp arr q hq
      have bitonic_congr : ∀ {f g : ℕ → Bool} {b n : ℕ},
          (∀ i < n, f (b + i) = g (b + i)) → IsBitonicSlice f b n → IsBitonicSlice g b n := by
        intro f g b n heq hf
        rcases hf with ⟨l, r, h1, h2, h3⟩ | ⟨l, r, h1, h2, h3⟩
        · left; refine ⟨l, r, h1, h2, fun i hi => by rw [← heq i hi]; exact h3 i hi⟩
        · right; refine ⟨l, r, h1, h2, fun i hi => by rw [← heq i hi]; exact h3 i hi⟩
      refine ⟨?_, ?_, ?_⟩
      · exact bitonic_congr (fun i hi => (heq1 i (by omega)).symm) hbs.1
      · exact bitonic_congr (fun i hi => by
          have h1 := heq1 (2 ^ m + i) (by omega)
          have hadd : q * 2 ^ (m + 1) + 2 ^ m + i = q * 2 ^ (m + 1) + (2 ^ m + i) := by omega
          rw [hadd]; exact h1.symm) hbs.2.1
      · rcases hbs.2.2 with hL | hR
        · left; intro i hi; rw [heq1 i (by omega)]; exact hL i hi
        · right; intro i hi
          have hadd : q * 2 ^ (m + 1) + 2 ^ m + i = q * 2 ^ (m + 1) + (2 ^ m + i) := by omega
          rw [hadd, heq1 (2 ^ m + i) (by omega), ← hadd]; exact hR i hi
    have hbit1 : ∀ q', (q' + 1) * 2 ^ m ≤ 2 ^ p →
        IsBitonicSlice (arrFun arr1) (q' * 2 ^ m) (2 ^ m) := by
      intro q' hq'
      set q := q' / 2
      have hq : (q + 1) * 2 ^ (m + 1) ≤ 2 ^ p := by
        have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ']
        have h2 : 2 ^ (m + 1) ∣ 2 ^ p := Nat.pow_dvd_pow 2 (by omega)
        rcases h2 with ⟨t, ht⟩
        have hq'le : q' + 1 ≤ 2 * t := by
          have hmul : (q' + 1) * 2 ^ m ≤ (2 * t) * 2 ^ m := by
            have : (2 * t) * 2 ^ m = 2 ^ p := by rw [ht, hpow]; ring
            rw [this]; exact hq'
          exact Nat.le_of_mul_le_mul_right hmul (Nat.two_pow_pos m)
        have : q + 1 ≤ t := by omega
        calc (q + 1) * 2 ^ (m + 1) ≤ t * 2 ^ (m + 1) := Nat.mul_le_mul_right _ this
          _ = 2 ^ p := by rw [ht, mul_comm]
      have hs := hsplit q hq
      by_cases hpar : q' % 2 = 0
      · have heq' : q' * 2 ^ m = q * 2 ^ (m + 1) := by
          rw [pow_succ']; have : q' = 2 * q := by omega
          rw [this]; ring
        rw [heq']; exact hs.1
      · have heq' : q' * 2 ^ m = q * 2 ^ (m + 1) + 2 ^ m := by
          rw [pow_succ']; have : q' = 2 * q + 1 := by omega
          rw [this]; ring
        rw [heq']; exact hs.2.1
    have hsorted1 := ih (by omega) arr1 hbit1
    set arr2 := applySchedule p (mergeSched k m) (mergeSched_lt p k m (by omega)) arr1
    intro q hq
    have h2m_mul : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ']
    have hqR : (2 * q + 1 + 1) * 2 ^ m ≤ 2 ^ p := by
      have : (2 * q + 1 + 1) * 2 ^ m = (q + 1) * 2 ^ (m + 1) := by rw [h2m_mul]; ring
      rw [this]; exact hq
    have hqL : (2 * q + 1) * 2 ^ m ≤ 2 ^ p := by
      calc (2 * q + 1) * 2 ^ m ≤ (2 * q + 1 + 1) * 2 ^ m := Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 ^ p := hqR
    have hbaseL : (2 * q) * 2 ^ m = q * 2 ^ (m + 1) := by rw [pow_succ']; ring
    have hbaseR : (2 * q + 1) * 2 ^ m = q * 2 ^ (m + 1) + 2 ^ m := by rw [pow_succ']; ring
    have hdirR : ((2 * q + 1) * 2 ^ m).testBit (k + 1) = (q * 2 ^ (m + 1)).testBit (k + 1) := by
      rw [hbaseR]
      have hdvd : 2 ^ (m + 1) ∣ 2 ^ (k + 1) := Nat.pow_dvd_pow 2 (by omega)
      rcases hdvd with ⟨t, ht⟩
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
      have hdiv : (q * 2 ^ (m + 1) + 2 ^ m) / 2 ^ (k + 1) = (q * 2 ^ (m + 1)) / 2 ^ (k + 1) := by
        rw [ht, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
        have hlt : 2 ^ m < 2 ^ (m + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
        rw [Nat.mul_comm q (2 ^ (m + 1)), Nat.mul_add_div (Nat.two_pow_pos (m + 1)),
          Nat.div_eq_of_lt hlt, Nat.add_zero, Nat.mul_div_right q (Nat.two_pow_pos (m + 1))]
      rw [hdiv]
    have hSL := hsorted1 (2 * q) hqL
    have hSR := hsorted1 (2 * q + 1) hqR
    rw [hbaseL] at hSL
    rw [hdirR, hbaseR] at hSR
    have hs := hsplit q hq
    have hconst : (∀ i < 2 ^ m, arrFun arr2 (q * 2 ^ (m + 1) + i) = !(!((q * 2 ^ (m + 1)).testBit (k + 1)))) ∨
        (∀ i < 2 ^ m, arrFun arr2 (q * 2 ^ (m + 1) + 2 ^ m + i) = !((q * 2 ^ (m + 1)).testBit (k + 1))) := by
      rcases hs.2.2 with hL | hR
      · left
        have := mergeSched_const_block p k m m (by omega) (le_refl m) arr1 (2 * q) hqL _ (by
          rw [hbaseL]; exact hL)
        rwa [hbaseL] at this
      · right
        have := mergeSched_const_block p k m m (by omega) (le_refl m) arr1 (2 * q + 1) hqR _ (by
          rw [hbaseR]; exact hR)
        rwa [hbaseR] at this
    intro i j hij hjlt
    have h2m : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; omega
    by_cases hjL : j < 2 ^ m
    · exact hSL i j hij hjL
    · by_cases hiL : i < 2 ^ m
      · have hadd : q * 2 ^ (m + 1) + j = q * 2 ^ (m + 1) + 2 ^ m + (j - 2 ^ m) := by omega
        rw [hadd]
        rcases hconst with hL | hR
        · rw [hL i hiL]
          cases (!((q * 2 ^ (m + 1)).testBit (k + 1))) <;> simp
        · rw [hR (j - 2 ^ m) (by omega)]
          cases (!((q * 2 ^ (m + 1)).testBit (k + 1))) <;> simp
      · have hadd1 : q * 2 ^ (m + 1) + i = q * 2 ^ (m + 1) + 2 ^ m + (i - 2 ^ m) := by omega
        have hadd2 : q * 2 ^ (m + 1) + j = q * 2 ^ (m + 1) + 2 ^ m + (j - 2 ^ m) := by omega
        rw [hadd1, hadd2]
        exact hSR (i - 2 ^ m) (j - 2 ^ m) (by omega) (by omega)

def stageSched (s : ℕ) : List (ℕ × ℕ) :=
  (List.range s).flatMap fun k => mergeSched k (k + 1)

lemma stageSched_eq_bitonicSchedule (p : ℕ) : stageSched p = bitonicSchedule p := rfl

lemma stageSched_lt (p s : ℕ) (hsp : s ≤ p) : ∀ e ∈ stageSched s, e.2 < p := by
  intro e he
  simp only [stageSched, mergeSched, List.mem_flatMap, List.mem_range, List.mem_map,
    List.mem_reverse] at he
  rcases he with ⟨k, hk, j, hj, rfl⟩
  omega

lemma bitonic_sort_bool (p s : ℕ) (hsp : s ≤ p) (arr : Fin (2 ^ p) → Bool) :
    ∀ q, (q + 1) * 2 ^ s ≤ 2 ^ p →
      IsSortedSlice (arrFun (applySchedule p (stageSched s) (stageSched_lt p s hsp) arr))
        (q * 2 ^ s) (2 ^ s) (q % 2 == 0) := by
  induction s with
  | zero =>
    intro q hq i j hij hjlt
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0
    split <;> exact le_refl _
  | succ s ih =>
    have happ : stageSched (s + 1) = stageSched s ++ mergeSched s (s + 1) := by
      simp [stageSched, List.range_succ, List.flatMap_append]
    have heq : applySchedule p (stageSched (s + 1)) (stageSched_lt p (s + 1) hsp) arr =
        applySchedule p (mergeSched s (s + 1)) (mergeSched_lt p s (s + 1) hsp)
          (applySchedule p (stageSched s) (stageSched_lt p s (by omega)) arr) := by
      rw [← applySchedule_append p (stageSched s) (mergeSched s (s + 1))
        (stageSched_lt p s (by omega)) (mergeSched_lt p s (s + 1) hsp) arr]
      exact applySchedule_congr p happ _ _ arr
    rw [heq]
    set arr1 := applySchedule p (stageSched s) (stageSched_lt p s (by omega)) arr
    have hbit : ∀ q, (q + 1) * 2 ^ (s + 1) ≤ 2 ^ p →
        IsBitonicSlice (arrFun arr1) (q * 2 ^ (s + 1)) (2 ^ (s + 1)) := by
      intro q hq
      have h2s : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ']
      have hqR : (2 * q + 1 + 1) * 2 ^ s ≤ 2 ^ p := by
        have : (2 * q + 1 + 1) * 2 ^ s = (q + 1) * 2 ^ (s + 1) := by rw [h2s]; ring
        rw [this]; exact hq
      have hqL : (2 * q + 1) * 2 ^ s ≤ 2 ^ p := by
        calc (2 * q + 1) * 2 ^ s ≤ (2 * q + 1 + 1) * 2 ^ s := Nat.mul_le_mul_right _ (by omega)
          _ ≤ 2 ^ p := hqR
      have hL := ih (by omega) (2 * q) hqL
      have hR := ih (by omega) (2 * q + 1) hqR
      have hbaseL : (2 * q) * 2 ^ s = q * 2 ^ (s + 1) := by rw [pow_succ']; ring
      have hbaseR : (2 * q + 1) * 2 ^ s = q * 2 ^ (s + 1) + 2 ^ s := by rw [pow_succ']; ring
      have hparL : (2 * q) % 2 = 0 := by omega
      have hparR : (2 * q + 1) % 2 = 1 := by omega
      simp only [hbaseL, hparL, beq_self_eq_true] at hL
      simp only [hbaseR, hparR] at hR
      have hb := bitonic_of_asc_desc (arrFun arr1) (q * 2 ^ (s + 1)) (2 ^ s) hL hR
      rwa [← h2s] at hb
    have hres := mergeSched_bitonic_bool p s (s + 1) (le_refl _) (by omega) arr1 hbit
    intro q hq
    have htb : (!((q * 2 ^ (s + 1)).testBit (s + 1))) = (q % 2 == 0) := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.mul_div_cancel _ (Nat.two_pow_pos (s + 1))]
      cases h : q % 2
      · simp
      · simp; omega
    have hq_res := hres q hq
    rwa [htb] at hq_res

lemma bitonic_sort_monotone (p : ℕ) (arr : Fin (2 ^ p) → ℕ) :
    Monotone (applySchedule p (bitonicSchedule p) (bitonicSchedule_lt p) arr) := by
  intro i j hij
  set res := applySchedule p (bitonicSchedule p) (bitonicSchedule_lt p) arr
  let φ : ℕ → Bool := fun z => decide (res i ≤ z)
  have hφ : Monotone φ := by
    intro a b hab
    dsimp [φ]
    by_cases h : res i ≤ a
    · simp [h, le_trans h hab]
    · simp [h]
  have hcomm := applySchedule_map_mono φ hφ p (bitonicSchedule p) (bitonicSchedule_lt p) arr
  have hbool := bitonic_sort_bool p p (le_refl p) (fun u => φ (arr u)) 0 (by simp)
  have hstep := hbool i.val j.val hij j.isLt
  simp only [Nat.zero_mul, Nat.zero_add, Nat.zero_mod, beq_self_eq_true, ↓reduceIte] at hstep
  have h1 : arrFun (applySchedule p (stageSched p) (stageSched_lt p p (le_refl p))
      (fun u => φ (arr u))) i.val = φ (res i) := by
    simp only [arrFun, i.isLt, ↓reduceDIte]
    exact congrFun hcomm i
  have h2 : arrFun (applySchedule p (stageSched p) (stageSched_lt p p (le_refl p))
      (fun u => φ (arr u))) j.val = φ (res j) := by
    simp only [arrFun, j.isLt, ↓reduceDIte]
    exact congrFun hcomm j
  rw [h1, h2] at hstep
  have hi_true : φ (res i) = true := by simp [φ]
  rw [hi_true] at hstep
  have hj_true : φ (res j) = true := by
    cases h : φ (res j)
    · rw [h] at hstep; exact Bool.noConfusion (hstep rfl)
    · rfl
  simpa [φ] using hj_true

def layerPerm (p k j : ℕ) (hj : j < p) (arr : Fin (2 ^ p) → ℕ) (u : Fin (2 ^ p)) : Fin (2 ^ p) :=
  let a := loBit j u.val
  let b := a + 2 ^ j
  let asc := !(a.testBit (k + 1))
  let ctrl := if asc then decide (arr ⟨b, loBit_two_pow_add_lt u.isLt hj⟩ < arr ⟨a, loBit_lt u.isLt⟩)
              else decide (arr ⟨a, loBit_lt u.isLt⟩ < arr ⟨b, loBit_two_pow_add_lt u.isLt hj⟩)
  if ctrl then ⟨flipBit j u.val, flipBit_lt u.isLt hj⟩ else u

lemma layerPerm_invol (p k j : ℕ) (hj : j < p) (arr : Fin (2 ^ p) → ℕ) (u : Fin (2 ^ p)) :
    layerPerm p k j hj arr (layerPerm p k j hj arr u) = u := by
  let c : Fin (2 ^ p) → Bool := fun x =>
    if !(loBit j x.val).testBit (k + 1) then
      decide (arr ⟨loBit j x.val + 2 ^ j, loBit_two_pow_add_lt x.isLt hj⟩ < arr ⟨loBit j x.val, loBit_lt x.isLt⟩)
    else
      decide (arr ⟨loBit j x.val, loBit_lt x.isLt⟩ < arr ⟨loBit j x.val + 2 ^ j, loBit_two_pow_add_lt x.isLt hj⟩)
  have hlp : ∀ x, layerPerm p k j hj arr x = if c x then ⟨flipBit j x.val, flipBit_lt x.isLt hj⟩ else x :=
    fun _ => rfl
  have hc_flip : c ⟨flipBit j u.val, flipBit_lt u.isLt hj⟩ = c u := by
    dsimp only [c]
    have hlo : loBit j (flipBit j u.val) = loBit j u.val := loBit_flipBit j u.val
    simp only [hlo]
  rw [hlp u]
  cases hcu : c u
  · simp only [Bool.false_eq_true, ↓reduceIte, hlp u, hcu]
  · simp only [↓reduceIte, hlp, hc_flip, hcu]
    ext
    exact flipBit_invol j u.val

lemma applyLayer_eq_comp_layerPerm (p k j : ℕ) (hj : j < p) (arr : Fin (2 ^ p) → ℕ)
    (u : Fin (2 ^ p)) :
    applyLayer p k j hj arr u = arr (layerPerm p k j hj arr u) := by
  unfold applyLayer layerPerm
  dsimp only
  set a := loBit j u.val
  set b := a + 2 ^ j
  set fa : Fin (2 ^ p) := ⟨a, loBit_lt u.isLt⟩
  set fb : Fin (2 ^ p) := ⟨b, loBit_two_pow_add_lt u.isLt hj⟩
  have hfa_u : u.val.testBit j = false → u = fa := by
    intro h; ext; simp [fa, a, loBit, h]
  have hfb_u : u.val.testBit j = true → u = fb := by
    intro h; ext; have hge := testBit_true_ge h; simp [fb, b, a, loBit, h, Nat.sub_add_cancel hge]
  have hflip_a : u.val.testBit j = false →
      (⟨flipBit j u.val, flipBit_lt u.isLt hj⟩ : Fin (2 ^ p)) = fb := by
    intro h; ext; simp [fb, b, a, loBit, flipBit, h]
  have hflip_b : u.val.testBit j = true →
      (⟨flipBit j u.val, flipBit_lt u.isLt hj⟩ : Fin (2 ^ p)) = fa := by
    intro h; ext; simp [fa, a, loBit, flipBit, h]
  have hite : ∀ (c : Bool) (x y : Fin (2 ^ p)), arr (if c then x else y) = if c then arr x else arr y := by
    intro c x y; cases c <;> rfl
  rw [hite]
  cases hu : u.val.testBit j
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hflip_a hu, congrArg arr (hfa_u hu)]
    cases !(a.testBit (k + 1))
    · simp only [Bool.false_eq_true, ↓reduceIte, max_def]
      by_cases h : arr fa < arr fb
      · simp [h, le_of_lt h]
      · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
        by_cases hle : arr fa ≤ arr fb
        · have heq : arr fa = arr fb := by omega
          simp [heq]
        · simp [hle]
    · simp only [↓reduceIte, min_def]
      by_cases h : arr fb < arr fa
      · simp [h, show ¬ (arr fa ≤ arr fb) by omega]
      · simp [h, show arr fa ≤ arr fb by omega]
  · simp only [↓reduceIte]
    rw [hflip_b hu, congrArg arr (hfb_u hu)]
    cases !(a.testBit (k + 1))
    · simp only [Bool.false_eq_true, ↓reduceIte, min_def]
      by_cases h : arr fa < arr fb
      · simp [h, le_of_lt h]
      · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
        by_cases hle : arr fa ≤ arr fb
        · have heq : arr fa = arr fb := by omega
          simp [heq]
        · simp [hle]
    · simp only [↓reduceIte, max_def]
      by_cases h : arr fb < arr fa
      · simp [h, show ¬ (arr fa ≤ arr fb) by omega]
      · simp [h, show arr fa ≤ arr fb by omega]

def buildLayerAux (I wFalse p k j : ℕ) (hj : j < p) :
    (m : ℕ) → List Gate → (Fin (2 ^ p) → List ℕ) → (Fin (2 ^ p) → ℕ × ℕ) →
    List Gate × (Fin (2 ^ p) → List ℕ) × (Fin (2 ^ p) → ℕ × ℕ)
  | 0, gs, keys, ctrls => (gs, keys, ctrls)
  | m + 1, gs, keys, ctrls =>
    let (gs1, keys1, ctrls1) := buildLayerAux I wFalse p k j hj m gs keys ctrls
    if hm : m < 2 ^ p ∧ m.testBit j = false then
      let b := m + 2 ^ j
      have hb : b < 2 ^ p := two_pow_add_lt hm.1 hj hm.2
      let asc := !(m.testBit (k + 1))
      let (gs2, ctrl, notCtrl, A', B') :=
        mkCmp I wFalse gs1 asc (keys1 ⟨m, hm.1⟩) (keys1 ⟨b, hb⟩)
      let keys2 : Fin (2 ^ p) → List ℕ := fun u =>
        if u.val = m then A' else if u.val = b then B' else keys1 u
      let ctrls2 : Fin (2 ^ p) → ℕ × ℕ := fun u =>
        if u.val = m then (ctrl, notCtrl) else ctrls1 u
      (gs2, keys2, ctrls2)
    else
      (gs1, keys1, ctrls1)

lemma buildLayerAux_spec (I wFalse p k j : ℕ) (hj : j < p) (m : ℕ)
    (gs : List Gate) (keys : Fin (2 ^ p) → List ℕ) (ctrls : Fin (2 ^ p) → ℕ × ℕ)
    (hwf : wFalse < I + gs.length)
    (hkeys_len : ∀ u, (keys u).length = p)
    (hkeys_lt : ∀ u w, w ∈ keys u → w < I + gs.length)
    (hctrls_lt : ∀ u, (ctrls u).1 < I + gs.length ∧ (ctrls u).2 < I + gs.length) :
    Extends I gs (buildLayerAux I wFalse p k j hj m gs keys ctrls).1 ∧
    (buildLayerAux I wFalse p k j hj m gs keys ctrls).1.length ≤ gs.length + m * (11 * p + 1) ∧
    (∀ u, ((buildLayerAux I wFalse p k j hj m gs keys ctrls).2.1 u).length = p) ∧
    (∀ u w, w ∈ (buildLayerAux I wFalse p k j hj m gs keys ctrls).2.1 u →
      w < I + (buildLayerAux I wFalse p k j hj m gs keys ctrls).1.length) ∧
    (∀ u, ((buildLayerAux I wFalse p k j hj m gs keys ctrls).2.2 u).1 <
      I + (buildLayerAux I wFalse p k j hj m gs keys ctrls).1.length ∧
      ((buildLayerAux I wFalse p k j hj m gs keys ctrls).2.2 u).2 <
      I + (buildLayerAux I wFalse p k j hj m gs keys ctrls).1.length) ∧
    (∀ u, m ≤ loBit j u.val → (buildLayerAux I wFalse p k j hj m gs keys ctrls).2.1 u = keys u) ∧
    ∀ x, x.length = I → wireVal gs x wFalse = false →
      let arr : Fin (2 ^ p) → ℕ := fun u => bitsListToNat ((keys u).map (wireVal gs x))
      ∀ u, loBit j u.val < m →
        bitsListToNat (((buildLayerAux I wFalse p k j hj m gs keys ctrls).2.1 u).map
          (wireVal (buildLayerAux I wFalse p k j hj m gs keys ctrls).1 x)) = applyLayer p k j hj arr u ∧
        (let a := loBit j u.val
         let asc := !(a.testBit (k + 1))
         let swap := if asc then decide (arr ⟨a + 2 ^ j, loBit_two_pow_add_lt u.isLt hj⟩ < arr ⟨a, loBit_lt u.isLt⟩)
                     else decide (arr ⟨a, loBit_lt u.isLt⟩ < arr ⟨a + 2 ^ j, loBit_two_pow_add_lt u.isLt hj⟩)
         wireVal (buildLayerAux I wFalse p k j hj m gs keys ctrls).1 x
           ((buildLayerAux I wFalse p k j hj m gs keys ctrls).2.2 ⟨a, loBit_lt u.isLt⟩).1 = swap ∧
         wireVal (buildLayerAux I wFalse p k j hj m gs keys ctrls).1 x
           ((buildLayerAux I wFalse p k j hj m gs keys ctrls).2.2 ⟨a, loBit_lt u.isLt⟩).2 = !swap) := by
  induction m with
  | zero =>
    refine ⟨extends_refl I gs, by simp [buildLayerAux], hkeys_len, hkeys_lt, hctrls_lt,
      fun _ _ => rfl, ?_⟩
    intro x hx hwf0 u hlt; omega
  | succ m ih =>
    dsimp only [buildLayerAux]
    rcases ih with ⟨he1, hlen1, hklen1, hklt1, hclt1, hunk1, hval1⟩
    set r1 := buildLayerAux I wFalse p k j hj m gs keys ctrls
    have hlen_le1 : gs.length ≤ r1.1.length := extends_length_le he1
    by_cases hm : m < 2 ^ p ∧ m.testBit j = false
    · rw [dite_eq_left_of_eq_true (eq_true hm)]
      dsimp only
      have hb : m + 2 ^ j < 2 ^ p := two_pow_add_lt hm.1 hj hm.2
      obtain ⟨hec, hlc, hwc1, hwc2, hlca, hlcb, hwca, hwcb, hvc⟩ :=
        mkCmp_spec I wFalse r1.1 (!(m.testBit (k + 1))) (r1.2.1 ⟨m, hm.1⟩) (r1.2.1 ⟨m + 2 ^ j, hb⟩)
          (by rw [hklen1, hklen1]) (by omega) (hklt1 _) (hklt1 _)
      set rc := mkCmp I wFalse r1.1 (!(m.testBit (k + 1))) (r1.2.1 ⟨m, hm.1⟩) (r1.2.1 ⟨m + 2 ^ j, hb⟩)
      have he02 : Extends I gs rc.1 := extends_trans he1 hec
      have hlen_le2 : r1.1.length ≤ rc.1.length := extends_length_le hec
      have hkeys_m : r1.2.1 ⟨m, hm.1⟩ = keys ⟨m, hm.1⟩ := by
        apply hunk1; simp [loBit, hm.2]
      have hkeys_b : r1.2.1 ⟨m + 2 ^ j, hb⟩ = keys ⟨m + 2 ^ j, hb⟩ := by
        apply hunk1
        have htb : (m + 2 ^ j).testBit j = true := testBit_add_two_pow_same hm.2
        simp [loBit, htb]
      refine ⟨he02, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hklen1] at hlc
        have : (m + 1) * (11 * p + 1) = m * (11 * p + 1) + (11 * p + 1) := by ring
        omega
      · intro u
        split
        · rw [hlca, hklen1]
        · split
          · rw [hlcb, hklen1]
          · exact hklen1 u
      · intro u w hw
        split at hw
        · exact hwca w hw
        · split at hw
          · exact hwcb w hw
          · have := hklt1 u w hw; omega
      · intro u
        split
        · exact ⟨hwc1, hwc2⟩
        · exact ⟨lt_of_lt_of_le (hclt1 u).1 (Nat.add_le_add_left hlen_le2 I),
            lt_of_lt_of_le (hclt1 u).2 (Nat.add_le_add_left hlen_le2 I)⟩
      · intro u hle
        have hne1 : u.val ≠ m := by
          intro heq; have : loBit j u.val = m := by simp [loBit, heq, hm.2]
          omega
        have hne2 : u.val ≠ m + 2 ^ j := by
          intro heq
          have htb : (m + 2 ^ j).testBit j = true := testBit_add_two_pow_same hm.2
          have : loBit j u.val = m := by simp [loBit, heq, htb]
          omega
        simp only [hne1, hne2, ↓reduceIte]
        exact hunk1 u (by omega)
      · intro x hx hwf0 u hlt
        have hwf1 : wireVal r1.1 x wFalse = false := by
          rw [extends_wireVal he1 x hx wFalse hwf, hwf0]
        have hcs := hvc x hx hwf1
        have hmap_m : (r1.2.1 ⟨m, hm.1⟩).map (wireVal r1.1 x) = (keys ⟨m, hm.1⟩).map (wireVal gs x) := by
          rw [hkeys_m]
          exact List.map_congr_left fun w hw => extends_wireVal he1 x hx w (hkeys_lt _ w hw)
        have hmap_b : (r1.2.1 ⟨m + 2 ^ j, hb⟩).map (wireVal r1.1 x) = (keys ⟨m + 2 ^ j, hb⟩).map (wireVal gs x) := by
          rw [hkeys_b]
          exact List.map_congr_left fun w hw => extends_wireVal he1 x hx w (hkeys_lt _ w hw)
        by_cases hlt1 : loBit j u.val < m
        · have hne1 : u.val ≠ m := by
            intro heq; have : loBit j u.val = m := by simp [loBit, heq, hm.2]
            omega
          have hne2 : u.val ≠ m + 2 ^ j := by
            intro heq
            have htb : (m + 2 ^ j).testBit j = true := testBit_add_two_pow_same hm.2
            have : loBit j u.val = m := by simp [loBit, heq, htb]
            omega
          have hlo_ne : loBit j u.val ≠ m := by omega
          have hv1 := hval1 x hx hwf0 u hlt1
          simp only [hne1, hne2, hlo_ne, ↓reduceIte]
          have hmap_u : (r1.2.1 u).map (wireVal rc.1 x) = (r1.2.1 u).map (wireVal r1.1 x) :=
            List.map_congr_left fun w hw => extends_wireVal hec x hx w (hklt1 u w hw)
          rw [hmap_u, hv1.1]
          refine ⟨rfl, ?_, ?_⟩
          · rw [extends_wireVal hec x hx _ (hclt1 _).1]; exact hv1.2.1
          · rw [extends_wireVal hec x hx _ (hclt1 _).2]; exact hv1.2.2
        · have hlo_eq : loBit j u.val = m := by omega
          rw [hmap_m, hmap_b] at hcs
          have hu_cases : u.val = m ∨ u.val = m + 2 ^ j := by
            unfold loBit at hlo_eq
            cases hub : u.val.testBit j
            · left; simpa [hub] using hlo_eq
            · right; have hge := testBit_true_ge hub; simp [hub] at hlo_eq; omega
          have hctrl_pair :
              wireVal rc.1 x (if loBit j u.val = m then (rc.2.1, rc.2.2.1) else r1.2.2 ⟨loBit j u.val, loBit_lt u.isLt⟩).1 =
                (if !(loBit j u.val).testBit (k + 1) then
                  decide (bitsListToNat ((keys ⟨loBit j u.val + 2 ^ j, loBit_two_pow_add_lt u.isLt hj⟩).map (wireVal gs x)) <
                          bitsListToNat ((keys ⟨loBit j u.val, loBit_lt u.isLt⟩).map (wireVal gs x)))
                else
                  decide (bitsListToNat ((keys ⟨loBit j u.val, loBit_lt u.isLt⟩).map (wireVal gs x)) <
                          bitsListToNat ((keys ⟨loBit j u.val + 2 ^ j, loBit_two_pow_add_lt u.isLt hj⟩).map (wireVal gs x)))) ∧
              wireVal rc.1 x (if loBit j u.val = m then (rc.2.1, rc.2.2.1) else r1.2.2 ⟨loBit j u.val, loBit_lt u.isLt⟩).2 =
                !(if !(loBit j u.val).testBit (k + 1) then
                  decide (bitsListToNat ((keys ⟨loBit j u.val + 2 ^ j, loBit_two_pow_add_lt u.isLt hj⟩).map (wireVal gs x)) <
                          bitsListToNat ((keys ⟨loBit j u.val, loBit_lt u.isLt⟩).map (wireVal gs x)))
                else
                  decide (bitsListToNat ((keys ⟨loBit j u.val, loBit_lt u.isLt⟩).map (wireVal gs x)) <
                          bitsListToNat ((keys ⟨loBit j u.val + 2 ^ j, loBit_two_pow_add_lt u.isLt hj⟩).map (wireVal gs x)))) := by
            simp only [hlo_eq, ↓reduceIte]
            exact ⟨hcs.1, hcs.2.1⟩
          refine ⟨?_, hctrl_pair.1, hctrl_pair.2⟩
          rcases hu_cases with hum | hub
          · simp only [hum, ↓reduceIte]
            rw [hcs.2.2.1]
            unfold applyLayer
            simp only [hum, hm.2, Bool.false_eq_true, ↓reduceIte,
              show loBit j m = m by simp [loBit, hm.2]]
            set va := bitsListToNat ((keys ⟨m, hm.1⟩).map (wireVal gs x))
            set vb := bitsListToNat ((keys ⟨m + 2 ^ j, hb⟩).map (wireVal gs x))
            cases hbit : m.testBit (k + 1)
            · simp only [Bool.not_false, ↓reduceIte, min_def]
              by_cases h : vb < va
              · simp [h, show ¬ (va ≤ vb) by omega]
              · simp [h, show va ≤ vb by omega]
            · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, max_def]
              by_cases h : va < vb
              · simp [h, le_of_lt h]
              · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
                by_cases hle : va ≤ vb
                · have : va = vb := by omega
                  simp [this]
                · simp [hle]
          · have hne : m + 2 ^ j ≠ m := by have := Nat.two_pow_pos j; omega
            have htb : (m + 2 ^ j).testBit j = true := testBit_add_two_pow_same hm.2
            simp only [hub, hne, ↓reduceIte]
            rw [hcs.2.2.2]
            unfold applyLayer
            simp only [hub, htb, ↓reduceIte, show loBit j (m + 2 ^ j) = m by simp [loBit, htb]]
            set va := bitsListToNat ((keys ⟨m, hm.1⟩).map (wireVal gs x))
            set vb := bitsListToNat ((keys ⟨m + 2 ^ j, hb⟩).map (wireVal gs x))
            cases hbit : m.testBit (k + 1)
            · simp only [Bool.not_false, ↓reduceIte, max_def]
              by_cases h : vb < va
              · simp [h, show ¬ (va ≤ vb) by omega]
              · simp [h, show va ≤ vb by omega]
            · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, min_def]
              by_cases h : va < vb
              · simp [h, le_of_lt h]
              · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
                by_cases hle : va ≤ vb
                · have : va = vb := by omega
                  simp [this]
                · simp [hle]
    · simp only [hm, ↓reduceDIte]
      refine ⟨he1, ?_, hklen1, hklt1, hclt1, ?_, ?_⟩
      · have : (m + 1) * (11 * p + 1) = m * (11 * p + 1) + (11 * p + 1) := by ring
        omega
      · intro u hle; exact hunk1 u (by omega)
      · intro x hx hwf0 u hlt
        have hne : loBit j u.val ≠ m := by
          intro heq
          apply hm
          refine ⟨?_, ?_⟩
          · rw [← heq]; exact loBit_lt u.isLt
          · rw [← heq]; exact loBit_testBit_false j u.val
        exact hval1 x hx hwf0 u (by omega)

def buildNetwork (I wFalse p : ℕ) :
    (sched : List (ℕ × ℕ)) → (∀ e ∈ sched, e.2 < p) →
    List Gate → (Fin (2 ^ p) → List ℕ) →
    List Gate × (Fin (2 ^ p) → List ℕ) × List (ℕ × (Fin (2 ^ p) → ℕ × ℕ))
  | [], _, gs, keys => (gs, keys, [])
  | e :: es, h, gs, keys =>
    let r1 := buildLayerAux I wFalse p e.1 e.2 (h e (by simp)) (2 ^ p) gs keys (fun _ => (wFalse, wFalse))
    let r2 := buildNetwork I wFalse p es (fun x hx => h x (by simp [hx])) r1.1 r1.2.1
    (r2.1, r2.2.1, (e.2, r1.2.2) :: r2.2.2)

def runLayerPerms (p : ℕ) (arr0 : Fin (2 ^ p) → ℕ) :
    (sched : List (ℕ × ℕ)) → (∀ e ∈ sched, e.2 < p) →
    List (Fin (2 ^ p) → Fin (2 ^ p))
  | [], _ => []
  | e :: es, h =>
    let hj := h e (by simp)
    layerPerm p e.1 e.2 hj arr0 ::
      runLayerPerms p (applyLayer p e.1 e.2 hj arr0) es (fun x hx => h x (by simp [hx]))

lemma runLayerPerms_length (p : ℕ) (arr0 : Fin (2 ^ p) → ℕ)
    (sched : List (ℕ × ℕ)) (hs : ∀ e ∈ sched, e.2 < p) :
    (runLayerPerms p arr0 sched hs).length = sched.length := by
  induction sched generalizing arr0 with
  | nil => rfl
  | cons e es ih => simp [runLayerPerms, ih]

lemma buildNetwork_len (I wFalse p : ℕ) (sched : List (ℕ × ℕ)) (hs : ∀ e ∈ sched, e.2 < p)
    (gs : List Gate) (keys : Fin (2 ^ p) → List ℕ) :
    (buildNetwork I wFalse p sched hs gs keys).2.2.length = sched.length := by
  induction sched generalizing gs keys with
  | nil => rfl
  | cons e es ih => simp [buildNetwork, ih]

lemma buildNetwork_j_lt (I wFalse p : ℕ) (sched : List (ℕ × ℕ)) (hs : ∀ e ∈ sched, e.2 < p)
    (gs : List Gate) (keys : Fin (2 ^ p) → List ℕ) :
    ∀ lc ∈ (buildNetwork I wFalse p sched hs gs keys).2.2, lc.1 < p := by
  induction sched generalizing gs keys with
  | nil => intro lc h; cases h
  | cons e es ih =>
    intro lc h
    dsimp only [buildNetwork] at h
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact hs e (by simp)
    · exact ih (fun x hx => hs x (by simp [hx])) _ _ lc h

lemma buildNetwork_spec (I wFalse p : ℕ)
    (sched : List (ℕ × ℕ)) (hs : ∀ e ∈ sched, e.2 < p)
    (gs : List Gate) (keys : Fin (2 ^ p) → List ℕ)
    (hwf : wFalse < I + gs.length)
    (hkeys_len : ∀ u, (keys u).length = p)
    (hkeys_lt : ∀ u w, w ∈ keys u → w < I + gs.length) :
    Extends I gs (buildNetwork I wFalse p sched hs gs keys).1 ∧
    (buildNetwork I wFalse p sched hs gs keys).1.length ≤ gs.length + sched.length * (2 ^ p * (11 * p + 1)) ∧
    (∀ u, ((buildNetwork I wFalse p sched hs gs keys).2.1 u).length = p) ∧
    (∀ u w, w ∈ (buildNetwork I wFalse p sched hs gs keys).2.1 u →
      w < I + (buildNetwork I wFalse p sched hs gs keys).1.length) ∧
    (∀ lc ∈ (buildNetwork I wFalse p sched hs gs keys).2.2,
      lc.1 < p ∧ ∀ u, (lc.2 u).1 < I + (buildNetwork I wFalse p sched hs gs keys).1.length ∧
        (lc.2 u).2 < I + (buildNetwork I wFalse p sched hs gs keys).1.length) ∧
    ∀ x, x.length = I → wireVal gs x wFalse = false →
      let arr0 : Fin (2 ^ p) → ℕ := fun u => bitsListToNat ((keys u).map (wireVal gs x))
      (∀ u, bitsListToNat (((buildNetwork I wFalse p sched hs gs keys).2.1 u).map
        (wireVal (buildNetwork I wFalse p sched hs gs keys).1 x)) = applySchedule p sched hs arr0 u) ∧
      ∀ idx (hidx : idx < sched.length),
        let lc := (buildNetwork I wFalse p sched hs gs keys).2.2[idx]'(by rw [buildNetwork_len]; exact hidx)
        let perm := (runLayerPerms p arr0 sched hs)[idx]'(by rw [runLayerPerms_length]; exact hidx)
        ∀ u : Fin (2 ^ p),
          let a := loBit lc.1 u.val
          let ctrl := wireVal (buildNetwork I wFalse p sched hs gs keys).1 x (lc.2 ⟨a, loBit_lt u.isLt⟩).1
          let notCtrl := wireVal (buildNetwork I wFalse p sched hs gs keys).1 x (lc.2 ⟨a, loBit_lt u.isLt⟩).2
          notCtrl = !ctrl ∧
          perm u = if ctrl then ⟨flipBit lc.1 u.val,
            flipBit_lt u.isLt (buildNetwork_j_lt I wFalse p sched hs gs keys lc (List.getElem_mem _))⟩ else u := by
  induction sched generalizing gs keys with
  | nil =>
    refine ⟨extends_refl I gs, by simp [buildNetwork], hkeys_len, hkeys_lt,
      by simp [buildNetwork], ?_⟩
    intro x hx hwf0
    refine ⟨fun _ => rfl, ?_⟩
    intro idx hidx; cases hidx
  | cons e es ih =>
    have hej : e.2 < p := hs e (by simp)
    obtain ⟨he1, hlen1, hklen1, hklt1, hclt1, _, hval1⟩ :=
      buildLayerAux_spec I wFalse p e.1 e.2 (hs e (by simp)) (2 ^ p) gs keys
        (fun _ => (wFalse, wFalse)) hwf hkeys_len hkeys_lt (fun _ => ⟨hwf, hwf⟩)
    set r1 := buildLayerAux I wFalse p e.1 e.2 (hs e (by simp)) (2 ^ p) gs keys (fun _ => (wFalse, wFalse))
    have hlen_le1 : gs.length ≤ r1.1.length := extends_length_le he1
    obtain ⟨he2, hlen2, hklen2, hklt2, hclt2, hval2⟩ :=
      ih (fun x hx => hs x (by simp [hx])) r1.1 r1.2.1 (by omega) hklen1 hklt1
    set r2 := buildNetwork I wFalse p es (fun x hx => hs x (by simp [hx])) r1.1 r1.2.1
    have hlen_le2 : r1.1.length ≤ r2.1.length := extends_length_le he2
    have he02 : Extends I gs r2.1 := extends_trans he1 he2
    have h1eq : (buildNetwork I wFalse p (e :: es) hs gs keys).1 = r2.1 := rfl
    have h21eq : (buildNetwork I wFalse p (e :: es) hs gs keys).2.1 = r2.2.1 := rfl
    have h22eq : (buildNetwork I wFalse p (e :: es) hs gs keys).2.2 = (e.2, r1.2.2) :: r2.2.2 := rfl
    refine ⟨he02, ?_, hklen2, hklt2, ?_, ?_⟩
    · rw [h1eq]
      simp only [List.length_cons]
      have : (es.length + 1) * (2 ^ p * (11 * p + 1)) =
          es.length * (2 ^ p * (11 * p + 1)) + 2 ^ p * (11 * p + 1) := by ring
      omega
    · intro lc hlc
      rw [h1eq]
      rw [h22eq, List.mem_cons] at hlc
      rcases hlc with rfl | hlc
      · exact ⟨hej, fun u => ⟨lt_of_lt_of_le (hclt1 u).1 (Nat.add_le_add_left hlen_le2 I),
          lt_of_lt_of_le (hclt1 u).2 (Nat.add_le_add_left hlen_le2 I)⟩⟩
      · exact hclt2 lc hlc
    · intro x hx hwf0
      have hwf1 : wireVal r1.1 x wFalse = false := by
        rw [extends_wireVal he1 x hx wFalse hwf, hwf0]
      have hs2 := hval2 x hx hwf1
      have harr1 : (fun u => bitsListToNat ((r1.2.1 u).map (wireVal r1.1 x))) =
          applyLayer p e.1 e.2 hej (fun u => bitsListToNat ((keys u).map (wireVal gs x))) := by
        funext u
        exact (hval1 x hx hwf0 u (loBit_lt u.isLt)).1
      refine ⟨?_, ?_⟩
      · intro u
        rw [h1eq, h21eq]
        have := hs2.1 u
        rw [harr1] at this
        exact this
      · intro idx hidx _lc _perm u
        cases idx with
        | zero =>
          have hv1 := (hval1 x hx hwf0 u (loBit_lt u.isLt)).2
          have hw1 : wireVal r2.1 x (r1.2.2 ⟨loBit e.2 u.val, loBit_lt u.isLt⟩).1 =
              wireVal r1.1 x (r1.2.2 ⟨loBit e.2 u.val, loBit_lt u.isLt⟩).1 :=
            extends_wireVal he2 x hx _ (hclt1 _).1
          have hw2 : wireVal r2.1 x (r1.2.2 ⟨loBit e.2 u.val, loBit_lt u.isLt⟩).2 =
              wireVal r1.1 x (r1.2.2 ⟨loBit e.2 u.val, loBit_lt u.isLt⟩).2 :=
            extends_wireVal he2 x hx _ (hclt1 _).2
          change wireVal r2.1 x (r1.2.2 ⟨loBit e.2 u.val, loBit_lt u.isLt⟩).2 =
            !(wireVal r2.1 x (r1.2.2 ⟨loBit e.2 u.val, loBit_lt u.isLt⟩).1) ∧
            layerPerm p e.1 e.2 hej (fun u => bitsListToNat ((keys u).map (wireVal gs x))) u =
            if wireVal r2.1 x (r1.2.2 ⟨loBit e.2 u.val, loBit_lt u.isLt⟩).1 then
              ⟨flipBit e.2 u.val, flipBit_lt u.isLt hej⟩
            else u
          rw [hw1, hw2, hv1.1, hv1.2]
          exact ⟨rfl, rfl⟩
        | succ idx' =>
          simp only [List.length_cons, Nat.add_lt_add_iff_right] at hidx
          have hsub := hs2.2 idx' hidx u
          change wireVal r2.1 x ((r2.2.2[idx']'(by rw [buildNetwork_len]; exact hidx)).2
              ⟨loBit (r2.2.2[idx']'(by rw [buildNetwork_len]; exact hidx)).1 u.val, loBit_lt u.isLt⟩).2 =
            !(wireVal r2.1 x ((r2.2.2[idx']'(by rw [buildNetwork_len]; exact hidx)).2
              ⟨loBit (r2.2.2[idx']'(by rw [buildNetwork_len]; exact hidx)).1 u.val, loBit_lt u.isLt⟩).1) ∧
            ((runLayerPerms p (applyLayer p e.1 e.2 hej (fun u => bitsListToNat ((keys u).map (wireVal gs x)))) es
              (fun x hx => hs x (by simp [hx])))[idx']'(by rw [runLayerPerms_length]; exact hidx)) u =
            if wireVal r2.1 x ((r2.2.2[idx']'(by rw [buildNetwork_len]; exact hidx)).2
              ⟨loBit (r2.2.2[idx']'(by rw [buildNetwork_len]; exact hidx)).1 u.val, loBit_lt u.isLt⟩).1 then
              ⟨flipBit (r2.2.2[idx']'(by rw [buildNetwork_len]; exact hidx)).1 u.val,
                flipBit_lt u.isLt (buildNetwork_j_lt I wFalse p es (fun x hx => hs x (by simp [hx]))
                  r1.1 r1.2.1 _ (List.getElem_mem _))⟩
            else u
          rw [← harr1]
          exact hsub

def buildStrideForKAux (I wFalse wTrue p d k : ℕ) (sortedKeys : Fin (2 ^ p) → List ℕ) :
    (m : ℕ) → List Gate → (Fin (2 ^ p) → ℕ) → List Gate × (Fin (2 ^ p) → ℕ)
  | 0, gs, eqW => (gs, eqW)
  | m + 1, gs, eqW =>
    let (gs1, eqW1) := buildStrideForKAux I wFalse wTrue p d k sortedKeys m gs eqW
    if hm : 2 ^ k ≤ m ∧ m < 2 ^ p then
      let (gs2, w) := mkEq I wTrue gs1
        ((sortedKeys ⟨m - 2 ^ k, lt_of_le_of_lt (Nat.sub_le _ _) hm.2⟩).take d)
        ((sortedKeys ⟨m, hm.2⟩).take d)
      (gs2, fun u => if u.val = m then w else eqW1 u)
    else
      (gs1, eqW1)

lemma buildStrideForKAux_spec (I wFalse wTrue p d k : ℕ) (hdp : d ≤ p)
    (sortedKeys : Fin (2 ^ p) → List ℕ) (m : ℕ)
    (gs : List Gate) (eqW : Fin (2 ^ p) → ℕ)
    (hwf : wFalse < I + gs.length) (hwt : wTrue < I + gs.length)
    (hsk_len : ∀ u, (sortedKeys u).length = p)
    (hsk_lt : ∀ u w, w ∈ sortedKeys u → w < I + gs.length)
    (heq_lt : ∀ u, eqW u < I + gs.length)
    (heq_init : ∀ u, u.val < 2 ^ k → eqW u = wFalse) :
    Extends I gs (buildStrideForKAux I wFalse wTrue p d k sortedKeys m gs eqW).1 ∧
    (buildStrideForKAux I wFalse wTrue p d k sortedKeys m gs eqW).1.length ≤ gs.length + m * (6 * d) ∧
    (∀ u, (buildStrideForKAux I wFalse wTrue p d k sortedKeys m gs eqW).2 u <
      I + (buildStrideForKAux I wFalse wTrue p d k sortedKeys m gs eqW).1.length) ∧
    (∀ u, u.val < 2 ^ k → (buildStrideForKAux I wFalse wTrue p d k sortedKeys m gs eqW).2 u = wFalse) ∧
    ∀ x, x.length = I → wireVal gs x wFalse = false → wireVal gs x wTrue = true →
      ∀ u, u.val < m →
        wireVal (buildStrideForKAux I wFalse wTrue p d k sortedKeys m gs eqW).1 x
          ((buildStrideForKAux I wFalse wTrue p d k sortedKeys m gs eqW).2 u) =
          if _h : 2 ^ k ≤ u.val then
            decide (((sortedKeys ⟨u.val - 2 ^ k, lt_of_le_of_lt (Nat.sub_le _ _) u.isLt⟩).take d).map (wireVal gs x) =
                    ((sortedKeys u).take d).map (wireVal gs x))
          else false := by
  induction m with
  | zero =>
    refine ⟨extends_refl I gs, by simp [buildStrideForKAux], heq_lt, heq_init, ?_⟩
    intro x _ _ _ u hu; omega
  | succ m ih =>
    dsimp only [buildStrideForKAux]
    rcases ih with ⟨he1, hlen1, hlt1, hinit1, hval1⟩
    set r1 := buildStrideForKAux I wFalse wTrue p d k sortedKeys m gs eqW
    have hlen_le1 : gs.length ≤ r1.1.length := extends_length_le he1
    by_cases hm : 2 ^ k ≤ m ∧ m < 2 ^ p
    · rw [dite_eq_left_of_eq_true (eq_true hm)]
      dsimp only
      have hlen_a : ((sortedKeys ⟨m - 2 ^ k, lt_of_le_of_lt (Nat.sub_le _ _) hm.2⟩).take d).length = d := by
        simp [hsk_len, Nat.min_eq_left hdp]
      have hlen_b : ((sortedKeys ⟨m, hm.2⟩).take d).length = d := by
        simp [hsk_len, Nat.min_eq_left hdp]
      obtain ⟨he2, hl2, hw2, hv2⟩ := mkEq_spec I wTrue r1.1
        ((sortedKeys ⟨m - 2 ^ k, lt_of_le_of_lt (Nat.sub_le _ _) hm.2⟩).take d)
        ((sortedKeys ⟨m, hm.2⟩).take d)
        (by rw [hlen_a, hlen_b]) (by omega)
        (fun w hw => by have := hsk_lt _ w (List.mem_of_mem_take hw); omega)
        (fun w hw => by have := hsk_lt _ w (List.mem_of_mem_take hw); omega)
      set r2 := mkEq I wTrue r1.1
        ((sortedKeys ⟨m - 2 ^ k, lt_of_le_of_lt (Nat.sub_le _ _) hm.2⟩).take d)
        ((sortedKeys ⟨m, hm.2⟩).take d)
      have he02 : Extends I gs r2.1 := extends_trans he1 he2
      have hlen_le2 : r1.1.length ≤ r2.1.length := extends_length_le he2
      refine ⟨he02, ?_, ?_, ?_, ?_⟩
      · rw [hlen_a] at hl2
        have : (m + 1) * (6 * d) = m * (6 * d) + 6 * d := by ring
        omega
      · intro u
        split
        · exact hw2
        · have := hlt1 u; omega
      · intro u hu
        have hne : u.val ≠ m := by omega
        simp [hne, hinit1 u hu]
      · intro x hx hwf0 hwt1 u hlt
        by_cases heqm : u.val = m
        · simp only [heqm, ↓reduceIte, hm.1, ↓reduceDIte]
          have hwt_r1 : wireVal r1.1 x wTrue = true := by
            rw [extends_wireVal he1 x hx wTrue hwt, hwt1]
          rw [hv2 x hx hwt_r1]
          have hu_eq : u = ⟨m, hm.2⟩ := by ext; exact heqm
          have hma : ((sortedKeys ⟨m - 2 ^ k, lt_of_le_of_lt (Nat.sub_le _ _) hm.2⟩).take d).map (wireVal r1.1 x) =
              ((sortedKeys ⟨m - 2 ^ k, lt_of_le_of_lt (Nat.sub_le _ _) hm.2⟩).take d).map (wireVal gs x) :=
            List.map_congr_left fun w hw => extends_wireVal he1 x hx w (hsk_lt _ w (List.mem_of_mem_take hw))
          have hmb : ((sortedKeys ⟨m, hm.2⟩).take d).map (wireVal r1.1 x) =
              ((sortedKeys u).take d).map (wireVal gs x) := by
            rw [hu_eq]
            exact List.map_congr_left fun w hw => extends_wireVal he1 x hx w (hsk_lt _ w (List.mem_of_mem_take hw))
          rw [hma, hmb]
        · simp only [heqm, ↓reduceIte]
          rw [extends_wireVal he2 x hx (r1.2 u) (hlt1 u)]
          exact hval1 x hx hwf0 hwt1 u (by omega)
    · simp only [hm, ↓reduceDIte]
      refine ⟨he1, ?_, hlt1, hinit1, ?_⟩
      · have : (m + 1) * (6 * d) = m * (6 * d) + 6 * d := by ring
        omega
      · intro x hx hwf0 hwt1 u hlt
        by_cases heqm : u.val = m
        · have hnot : ¬ (2 ^ k ≤ u.val) := by
            intro hge; apply hm; exact ⟨by omega, by rw [← heqm]; exact u.isLt⟩
          simp only [hnot, ↓reduceDIte]
          rw [hinit1 u (by omega), extends_wireVal he1 x hx wFalse hwf, hwf0]
        · exact hval1 x hx hwf0 hwt1 u (by omega)

def buildAllStridesAux (I wFalse wTrue p d : ℕ) (sortedKeys : Fin (2 ^ p) → List ℕ) :
    (k : ℕ) → List Gate → (Fin p → Fin (2 ^ p) → ℕ) →
    List Gate × (Fin p → Fin (2 ^ p) → ℕ)
  | 0, gs, sw => (gs, sw)
  | k + 1, gs, sw =>
    let (gs1, sw1) := buildAllStridesAux I wFalse wTrue p d sortedKeys k gs sw
    let (gs2, eqK) := buildStrideForKAux I wFalse wTrue p d k sortedKeys (2 ^ p) gs1 (fun _ => wFalse)
    (gs2, fun idx => if idx.val = k then eqK else sw1 idx)

lemma buildAllStridesAux_spec (I wFalse wTrue p d : ℕ) (hdp : d ≤ p)
    (sortedKeys : Fin (2 ^ p) → List ℕ) (k : ℕ)
    (gs : List Gate) (sw : Fin p → Fin (2 ^ p) → ℕ)
    (hwf : wFalse < I + gs.length) (hwt : wTrue < I + gs.length)
    (hsk_len : ∀ u, (sortedKeys u).length = p)
    (hsk_lt : ∀ u w, w ∈ sortedKeys u → w < I + gs.length)
    (hsw_lt : ∀ idx u, sw idx u < I + gs.length) :
    Extends I gs (buildAllStridesAux I wFalse wTrue p d sortedKeys k gs sw).1 ∧
    (buildAllStridesAux I wFalse wTrue p d sortedKeys k gs sw).1.length ≤ gs.length + k * (2 ^ p * (6 * d)) ∧
    (∀ idx u, (buildAllStridesAux I wFalse wTrue p d sortedKeys k gs sw).2 idx u <
      I + (buildAllStridesAux I wFalse wTrue p d sortedKeys k gs sw).1.length) ∧
    ∀ x, x.length = I → wireVal gs x wFalse = false → wireVal gs x wTrue = true →
      ∀ (idx : Fin p), idx.val < k → ∀ u : Fin (2 ^ p),
        wireVal (buildAllStridesAux I wFalse wTrue p d sortedKeys k gs sw).1 x
          ((buildAllStridesAux I wFalse wTrue p d sortedKeys k gs sw).2 idx u) =
          if _h : 2 ^ idx.val ≤ u.val then
            decide (((sortedKeys ⟨u.val - 2 ^ idx.val, lt_of_le_of_lt (Nat.sub_le _ _) u.isLt⟩).take d).map (wireVal gs x) =
                    ((sortedKeys u).take d).map (wireVal gs x))
          else false := by
  induction k with
  | zero =>
    refine ⟨extends_refl I gs, by simp [buildAllStridesAux], hsw_lt, ?_⟩
    intro _ _ _ _ idx h; omega
  | succ k ih =>
    dsimp only [buildAllStridesAux]
    rcases ih with ⟨he1, hlen1, hlt1, hval1⟩
    set r1 := buildAllStridesAux I wFalse wTrue p d sortedKeys k gs sw
    have hlen_le1 : gs.length ≤ r1.1.length := extends_length_le he1
    obtain ⟨he2, hlen2, hlt2, _, hval2⟩ :=
      buildStrideForKAux_spec I wFalse wTrue p d k hdp sortedKeys (2 ^ p) r1.1
        (fun _ => wFalse) (by omega) (by omega) hsk_len
        (fun u w hw => by have := hsk_lt u w hw; omega) (fun _ => by omega) (fun _ _ => rfl)
    set r2 := buildStrideForKAux I wFalse wTrue p d k sortedKeys (2 ^ p) r1.1 (fun _ => wFalse)
    have he02 : Extends I gs r2.1 := extends_trans he1 he2
    have hlen_le2 : r1.1.length ≤ r2.1.length := extends_length_le he2
    refine ⟨he02, ?_, ?_, ?_⟩
    · have : (k + 1) * (2 ^ p * (6 * d)) = k * (2 ^ p * (6 * d)) + 2 ^ p * (6 * d) := by ring
      omega
    · intro idx u
      split
      · exact hlt2 u
      · have := hlt1 idx u; omega
    · intro x hx hwf0 hwt1 idx hlt u
      by_cases heqk : idx.val = k
      · simp only [heqk, ↓reduceIte]
        have hwf1 : wireVal r1.1 x wFalse = false := by
          rw [extends_wireVal he1 x hx wFalse hwf, hwf0]
        have hwt1' : wireVal r1.1 x wTrue = true := by
          rw [extends_wireVal he1 x hx wTrue hwt, hwt1]
        have hv2 := hval2 x hx hwf1 hwt1' u u.isLt
        rw [hv2]
        by_cases hge : 2 ^ k ≤ u.val
        · simp only [hge, ↓reduceDIte]
          have hma : ((sortedKeys ⟨u.val - 2 ^ k, lt_of_le_of_lt (Nat.sub_le _ _) u.isLt⟩).take d).map (wireVal r1.1 x) =
              ((sortedKeys ⟨u.val - 2 ^ k, lt_of_le_of_lt (Nat.sub_le _ _) u.isLt⟩).take d).map (wireVal gs x) :=
            List.map_congr_left fun w hw => extends_wireVal he1 x hx w (hsk_lt _ w (List.mem_of_mem_take hw))
          have hmb : ((sortedKeys u).take d).map (wireVal r1.1 x) =
              ((sortedKeys u).take d).map (wireVal gs x) :=
            List.map_congr_left fun w hw => extends_wireVal he1 x hx w (hsk_lt _ w (List.mem_of_mem_take hw))
          rw [hma, hmb]
        · simp [hge]
      · simp only [heqk, ↓reduceIte]
        rw [extends_wireVal he2 x hx (r1.2 idx u) (hlt1 idx u)]
        exact hval1 x hx hwf0 hwt1 idx (by omega) u

def shiftStep (p : ℕ) (s : Fin (p + 1) → Bool) (b : Bool) : Fin (p + 1) → Bool :=
  Fin.snoc (α := fun _ : Fin (p + 1) => Bool) (fun j : Fin p => s j.succ) b

def rotState (p : ℕ) (s0 s1 : Fin (p + 1) → Bool) (k : ℕ) : Fin (p + 1) → Bool :=
  fun i =>
    if h : i.val < (p + 1) - k then s0 ⟨i.val + k, by omega⟩
    else s1 ⟨i.val - ((p + 1) - k), by omega⟩

lemma shiftStep_rotState (p : ℕ) (s0 s1 : Fin (p + 1) → Bool) (t : Fin (p + 1)) :
    shiftStep p (rotState p s0 s1 t.val) (s1 t) = rotState p s0 s1 (t.val + 1) := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · unfold shiftStep rotState
    rw [Fin.snoc_last]
    have hnot : ¬ ((Fin.last p).val < (p + 1) - (t.val + 1)) := by simp
    simp only [hnot, ↓reduceDIte]
    congr 1; ext; simp; omega
  · intro j
    unfold shiftStep rotState
    rw [Fin.snoc_castSucc]
    simp only [Fin.val_castSucc, Fin.val_succ]
    by_cases h1 : j.val < (p + 1) - (t.val + 1)
    · have h2 : j.val + 1 < (p + 1) - t.val := by omega
      simp only [h1, h2, ↓reduceDIte]
      congr 1; ext; simp; omega
    · have h2 : ¬ (j.val + 1 < (p + 1) - t.val) := by omega
      simp only [h1, h2, ↓reduceDIte]
      congr 1; ext; simp; omega

lemma runSweep_eq {p : ℕ} (stepBit : Fin (p + 1) → (Fin (p + 1) → Bool) → Bool)
    (s0 s1 : Fin (p + 1) → Bool)
    (hstep : ∀ (t : Fin (p + 1)), stepBit t (rotState p s0 s1 t.val) = s1 t) :
    (List.finRange (p + 1)).foldl (fun s t => shiftStep p s (stepBit t s)) s0 = s1 := by
  have hgen : ∀ (k : ℕ) (hk : k ≤ p + 1),
      ((List.finRange (p + 1)).take k).foldl (fun s t => shiftStep p s (stepBit t s)) s0 =
        rotState p s0 s1 k := by
    intro k hk
    induction k with
    | zero =>
      simp only [List.take_zero, List.foldl_nil]
      funext i
      unfold rotState
      simp [i.isLt]
    | succ k ih =>
      have hlt : k < (List.finRange (p + 1)).length := by simp; omega
      rw [List.take_succ_eq_append_getElem hlt, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih (by omega)]
      have hget : (List.finRange (p + 1))[k]'hlt = ⟨k, by omega⟩ := by simp
      rw [hget, hstep ⟨k, by omega⟩]
      exact shiftStep_rotState p s0 s1 ⟨k, by omega⟩
  have hfull := hgen (p + 1) (le_refl _)
  rw [List.take_of_length_le (by simp)] at hfull
  rw [hfull]
  funext i
  unfold rotState
  simp

lemma flatten_length_uniform {α : Type*} (L : List (List α)) (d : ℕ)
    (hlen : ∀ x ∈ L, x.length = d) : L.flatten.length = L.length * d := by
  induction L with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [hlen a (by simp), ih (fun x hx => hlen x (by simp [hx]))]
    ring

lemma flatten_getElem_uniform {α : Type*} (L : List (List α)) (d : ℕ)
    (hlen : ∀ x ∈ L, x.length = d) (q r : ℕ) (hq : q < L.length) (hr : r < d) :
    L.flatten[q * d + r]'(by
      rw [flatten_length_uniform L d hlen]
      have h1 : q + 1 ≤ L.length := hq
      calc q * d + r < q * d + d := Nat.add_lt_add_left hr _
        _ = (q + 1) * d := by ring
        _ ≤ L.length * d := Nat.mul_le_mul_right d h1) =
    (L[q]'hq)[r]'(by rw [hlen _ (List.getElem_mem hq)]; exact hr) := by
  induction L generalizing q with
  | nil => cases hq
  | cons a as ih =>
    have ha : a.length = d := hlen a (by simp)
    have has : ∀ x ∈ as, x.length = d := fun x hx => hlen x (by simp [hx])
    cases q with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.flatten_cons, List.getElem_cons_zero]
      exact List.getElem_append_left (by omega)
    | succ q' =>
      simp only [List.flatten_cons, List.getElem_cons_succ]
      have hge : a.length ≤ (q' + 1) * d + r := by rw [ha]; nlinarith
      rw [List.getElem_append_right hge]
      have hsub : (q' + 1) * d + r - a.length = q' * d + r := by rw [ha]; ring_nf; omega
      simp only [hsub]
      exact ih has q' (by simp at hq; omega)

lemma foldl_finRange_mul {α : Type*} (w n : ℕ) (f : α → Fin (w * n) → α) (a0 : α) :
    (List.finRange (w * n)).foldl f a0 =
      (List.finRange n).foldl (fun a sw =>
        (List.finRange w).foldl (fun a' t =>
          f a' ⟨sw.val * w + t.val, by
            have h1 : sw.val + 1 ≤ n := sw.isLt
            calc sw.val * w + t.val < sw.val * w + w := Nat.add_lt_add_left t.isLt _
              _ = (sw.val + 1) * w := by ring
              _ ≤ n * w := Nat.mul_le_mul_right w h1
              _ = w * n := Nat.mul_comm n w⟩) a) a0 := by
  have hlist : List.finRange (w * n) =
      ((List.finRange n).map fun sw =>
        (List.finRange w).map fun t =>
          (⟨sw.val * w + t.val, by
            have h1 : sw.val + 1 ≤ n := sw.isLt
            calc sw.val * w + t.val < sw.val * w + w := Nat.add_lt_add_left t.isLt _
              _ = (sw.val + 1) * w := by ring
              _ ≤ n * w := Nat.mul_le_mul_right w h1
              _ = w * n := Nat.mul_comm n w⟩ : Fin (w * n))).flatten := by
    set L := (List.finRange n).map fun sw =>
      (List.finRange w).map fun t =>
        (⟨sw.val * w + t.val, by
          have h1 : sw.val + 1 ≤ n := sw.isLt
          calc sw.val * w + t.val < sw.val * w + w := Nat.add_lt_add_left t.isLt _
            _ = (sw.val + 1) * w := by ring
            _ ≤ n * w := Nat.mul_le_mul_right w h1
            _ = w * n := Nat.mul_comm n w⟩ : Fin (w * n))
    have hL_len : ∀ x ∈ L, x.length = w := by
      intro x hx
      simp only [L, List.mem_map] at hx
      rcases hx with ⟨_, _, rfl⟩
      simp
    apply List.ext_getElem
    · rw [List.length_finRange, flatten_length_uniform L w hL_len]
      simp [L, Nat.mul_comm]
    · intro i hi1 hi2
      have hi : i < w * n := by simpa using hi1
      have hwpos : 0 < w := by
        by_contra h0; have : w = 0 := by omega
        rw [this, Nat.zero_mul] at hi; omega
      have hq : i / w < n := by
        rw [Nat.div_lt_iff_lt_mul hwpos, Nat.mul_comm]; exact hi
      have hr : i % w < w := Nat.mod_lt i hwpos
      have hi_eq : (i / w) * w + i % w = i := by
        have := Nat.div_add_mod i w; nlinarith
      have hget := flatten_getElem_uniform L w hL_len (i / w) (i % w) (by simp [L, hq]) hr
      have hget' : L.flatten[i]'hi2 = (L[i / w]'(by simp [L, hq]))[i % w]'(by simp [L, hr]) := by
        convert hget using 1
        congr 1; exact hi_eq.symm
      rw [hget']
      simp only [List.getElem_finRange, L, List.getElem_map]
      ext
      simp [hi_eq]
  rw [hlist, List.foldl_flatten, List.foldl_map]
  congr 1
  funext a sw
  rw [List.foldl_map]

def stateOf (p : ℕ) (g : Bool) (u : Fin (2 ^ p)) : Fin (p + 1) → Bool :=
  Fin.cons (α := fun _ : Fin (p + 1) => Bool) g (natToBits p u.val)

def sweepId (p wFalse wTrue : ℕ) (_t : Fin (p + 1)) (st : Fin (p + 1) → Bool) : ℕ :=
  if st 0 then wTrue else wFalse

def sweepSwap (p wFalse wTrue j : ℕ) (ctrls : Fin (2 ^ p) → ℕ × ℕ)
    (t : Fin (p + 1)) (st : Fin (p + 1) → Bool) : ℕ :=
  if t.val = p - j then
    let uBits : Fin p → Bool := fun r =>
      st ⟨(r.val + 1 + (p + 1) - (p - j)) % (p + 1), Nat.mod_lt _ (Nat.succ_pos p)⟩
    let uVal := bitsToNat uBits
    let a := loBit j uVal
    let pair := ctrls ⟨a, loBit_lt (bitsToNat_lt uBits)⟩
    if st 0 then pair.2 else pair.1
  else
    if st 0 then wTrue else wFalse

def sweepLoadGuard (p : ℕ) (eqW : Fin (2 ^ p) → ℕ) (wFalse wTrue : ℕ)
    (t : Fin (p + 1)) (st : Fin (p + 1) → Bool) : ℕ :=
  if t.val = 0 then
    let uBits : Fin p → Bool := fun r => st r.succ
    eqW ⟨bitsToNat uBits, bitsToNat_lt uBits⟩
  else
    if st 0 then wTrue else wFalse

def sweepSub (p k wFalse wTrue : ℕ) (t : Fin (p + 1)) (st : Fin (p + 1) → Bool) : ℕ :=
  let bit : Bool :=
    if ht0 : t.val = 0 then
      st 0
    else if p - t.val < k then
      st 0
    else
      let gVal := st ⟨p + 1 - t.val, by omega⟩
      let allZero := (List.range (p - t.val - k)).all fun r =>
        if hr : r + 1 < p + 1 then !(st ⟨r + 1, hr⟩) else true
      xor (st 0) (gVal && allZero)
  if bit then wTrue else wFalse

def sweepClearGuard (p wFalse wTrue : ℕ) (t : Fin (p + 1)) (st : Fin (p + 1) → Bool) : ℕ :=
  if t.val = 0 then wFalse else if st 0 then wTrue else wFalse

def sweepClearTag (p wFalse wTrue : ℕ) (t : Fin (p + 1)) (st : Fin (p + 1) → Bool) : ℕ :=
  if t.val = 1 then wFalse else if st 0 then wTrue else wFalse

lemma runSweep_id (p wFalse wTrue : ℕ) (eval : ℕ → Bool)
    (hf : eval wFalse = false) (ht : eval wTrue = true) (s : Fin (p + 1) → Bool) :
    (List.finRange (p + 1)).foldl (fun st t => shiftStep p st (eval (sweepId p wFalse wTrue t st))) s = s := by
  apply runSweep_eq
  intro t
  have h0 : rotState p s s t.val 0 = s t := by
    unfold rotState; simp [show 0 < p + 1 - t.val by omega]
  unfold sweepId
  simp only [h0]
  cases s t <;> simp [hf, ht]

lemma runSweep_swap (p wFalse wTrue j : ℕ) (hj : j < p) (ctrls : Fin (2 ^ p) → ℕ × ℕ)
    (eval : ℕ → Bool) (hf : eval wFalse = false) (ht : eval wTrue = true)
    (u : Fin (2 ^ p)) (ctrl : Bool)
    (hc1 : eval (ctrls ⟨loBit j u.val, loBit_lt u.isLt⟩).1 = ctrl)
    (hc2 : eval (ctrls ⟨loBit j u.val, loBit_lt u.isLt⟩).2 = !ctrl) :
    (List.finRange (p + 1)).foldl
      (fun st t => shiftStep p st (eval (sweepSwap p wFalse wTrue j ctrls t st)))
      (stateOf p false u) =
    stateOf p false (if ctrl then ⟨flipBit j u.val, flipBit_lt u.isLt hj⟩ else u) := by
  set u' : Fin (2 ^ p) := if ctrl then ⟨flipBit j u.val, flipBit_lt u.isLt hj⟩ else u
  set s0 := stateOf p false u
  set s1 := stateOf p false u'
  have hs_ne : ∀ i : Fin (p + 1), i.val ≠ p - j → s1 i = s0 i := by
    intro i hne
    revert hne
    refine Fin.cases ?_ ?_ i
    · intro _; simp [s0, s1, stateOf]
    · intro r hne
      simp only [s0, s1, stateOf, Fin.cons_succ, natToBits]
      cases ctrl
      · rfl
      · simp only [u', ↓reduceIte]
        rw [testBit_flipBit]
        have hne2 : p - 1 - r.val ≠ j := by
          have : r.val + 1 ≠ p - j := hne
          omega
        simp only [hne2, ↓reduceIte]
  have hs_at : s1 ⟨p - j, by omega⟩ = xor (s0 ⟨p - j, by omega⟩) ctrl := by
    have hidx : (⟨p - j, by omega⟩ : Fin (p + 1)) = Fin.succ ⟨p - 1 - j, by omega⟩ := by
      ext; simp; omega
    rw [hidx]
    simp only [s0, s1, stateOf, Fin.cons_succ, natToBits]
    have hsub : p - 1 - (p - 1 - j) = j := by omega
    rw [hsub]
    cases ctrl
    · simp [u']
    · simp only [u', ↓reduceIte, testBit_flipBit, Bool.xor_true]
  apply runSweep_eq
  intro t
  have h0 : rotState p s0 s1 t.val 0 = s0 t := by
    unfold rotState; simp [show 0 < p + 1 - t.val by omega]
  unfold sweepSwap
  by_cases hteq : t.val = p - j
  · simp only [hteq, ↓reduceIte]
    have ht_fin : t = ⟨p - j, by omega⟩ := by ext; exact hteq
    have hrot_eq : ∀ r : Fin p,
        rotState p s0 s1 (p - j)
          ⟨(r.val + 1 + (p + 1) - (p - j)) % (p + 1), Nat.mod_lt _ (Nat.succ_pos p)⟩ =
        natToBits p u.val r := by
      intro r
      unfold rotState
      by_cases hlt : r.val + 1 < p - j
      · have hmod : (r.val + 1 + (p + 1) - (p - j)) % (p + 1) = r.val + 1 + (j + 1) := by
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        have hnot : ¬ ((r.val + 1 + (p + 1) - (p - j)) % (p + 1) < (p + 1) - (p - j)) := by
          rw [hmod]; omega
        simp only [hnot, ↓reduceDIte]
        have hidx_val : (r.val + 1 + (p + 1) - (p - j)) % (p + 1) - ((p + 1) - (p - j)) = r.val + 1 := by
          rw [hmod]; omega
        have hlt_sub : (r.val + 1 + (p + 1) - (p - j)) % (p + 1) - ((p + 1) - (p - j)) < p + 1 := by
          rw [hidx_val]; omega
        have hne : (⟨(r.val + 1 + (p + 1) - (p - j)) % (p + 1) - ((p + 1) - (p - j)),
            hlt_sub⟩ : Fin (p + 1)).val ≠ p - j := by
          change (r.val + 1 + (p + 1) - (p - j)) % (p + 1) - ((p + 1) - (p - j)) ≠ p - j
          rw [hidx_val]; omega
        rw [hs_ne _ hne]
        have hfin : (⟨(r.val + 1 + (p + 1) - (p - j)) % (p + 1) - ((p + 1) - (p - j)),
            hlt_sub⟩ : Fin (p + 1)) = r.succ := by ext; simp [hidx_val]
        rw [hfin]; simp [s0, stateOf]
      · have hmod : (r.val + 1 + (p + 1) - (p - j)) % (p + 1) = r.val + 1 - (p - j) := by
          have : r.val + 1 + (p + 1) - (p - j) = (p + 1) + (r.val + 1 - (p - j)) := by omega
          rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        have hlt2 : (r.val + 1 + (p + 1) - (p - j)) % (p + 1) < (p + 1) - (p - j) := by
          rw [hmod]; omega
        simp only [hlt2, ↓reduceDIte]
        have hfin : (⟨(r.val + 1 + (p + 1) - (p - j)) % (p + 1) + (p - j),
            by omega⟩ : Fin (p + 1)) = r.succ := by ext; simp [hmod]; omega
        rw [hfin]; simp [s0, stateOf]
    have hubits : (fun r : Fin p =>
        rotState p s0 s1 (p - j)
          ⟨(r.val + 1 + (p + 1) - (p - j)) % (p + 1), Nat.mod_lt _ (Nat.succ_pos p)⟩) =
        natToBits p u.val := funext hrot_eq
    have hnat : bitsToNat (fun r : Fin p =>
        rotState p s0 s1 (p - j)
          ⟨(r.val + 1 + (p + 1) - (p - j)) % (p + 1), Nat.mod_lt _ (Nat.succ_pos p)⟩) = u.val := by
      rw [hubits]; exact bitsToNat_natToBits p u.val u.isLt
    have hpair : (⟨loBit j (bitsToNat (fun r : Fin p =>
        rotState p s0 s1 (p - j)
          ⟨(r.val + 1 + (p + 1) - (p - j)) % (p + 1), Nat.mod_lt _ (Nat.succ_pos p)⟩)),
        loBit_lt (bitsToNat_lt _)⟩ : Fin (2 ^ p)) = ⟨loBit j u.val, loBit_lt u.isLt⟩ := by
      ext; simp [hnat]
    have h0' : rotState p s0 s1 (p - j) 0 = s0 ⟨p - j, by omega⟩ := by
      unfold rotState; simp [show 0 < p + 1 - (p - j) by omega]
    rw [hpair]
    simp only [h0', ht_fin, hs_at]
    cases s0 ⟨p - j, by omega⟩
    · simp [hc1]
    · simp [hc2]
  · simp only [hteq, ↓reduceIte]
    simp only [h0, hs_ne t hteq]
    cases s0 t <;> simp [hf, ht]

lemma runSweep_loadGuard (p wFalse wTrue : ℕ) (eqW : Fin (2 ^ p) → ℕ)
    (eval : ℕ → Bool) (hf : eval wFalse = false) (ht : eval wTrue = true)
    (u : Fin (2 ^ p)) :
    (List.finRange (p + 1)).foldl
      (fun st t => shiftStep p st (eval (sweepLoadGuard p eqW wFalse wTrue t st)))
      (stateOf p false u) =
    stateOf p (eval (eqW u)) u := by
  apply runSweep_eq
  intro t
  unfold sweepLoadGuard
  refine Fin.cases ?_ ?_ t
  · simp only [Fin.val_zero, ↓reduceIte]
    have hbits : (fun r : Fin p => rotState p (stateOf p false u) (stateOf p (eval (eqW u)) u) 0 r.succ) =
        natToBits p u.val := by
      funext r; unfold rotState
      simp only [Nat.sub_zero, Fin.isLt, ↓reduceDIte]
      have hfin : (⟨r.succ.val + 0, by omega⟩ : Fin (p + 1)) = r.succ := by ext; simp
      rw [hfin]; simp [stateOf]
    have hu : (⟨bitsToNat (fun r : Fin p =>
        rotState p (stateOf p false u) (stateOf p (eval (eqW u)) u) 0 r.succ),
        bitsToNat_lt _⟩ : Fin (2 ^ p)) = u := by
      ext; rw [hbits]; exact bitsToNat_natToBits p u.val u.isLt
    rw [hu]; simp [stateOf]
  · intro r
    simp only [Fin.val_succ, Nat.succ_ne_zero, ↓reduceIte]
    have h0 : rotState p (stateOf p false u) (stateOf p (eval (eqW u)) u) (r.val + 1) 0 =
        stateOf p (eval (eqW u)) u r.succ := by
      unfold rotState
      simp only [Fin.val_zero, show 0 < p + 1 - (r.val + 1) by omega, ↓reduceDIte, Nat.zero_add]
      have hfin : (⟨r.val + 1, by omega⟩ : Fin (p + 1)) = r.succ := by ext; simp
      rw [hfin]; simp [stateOf]
    simp only [h0]
    cases stateOf p (eval (eqW u)) u r.succ <;> simp [hf, ht]

lemma runSweep_sub (p k wFalse wTrue : ℕ) (hk : k < p)
    (eval : ℕ → Bool) (hf : eval wFalse = false) (ht : eval wTrue = true)
    (g : Bool) (u : Fin (2 ^ p)) (hge : g = true → 2 ^ k ≤ u.val) :
    (List.finRange (p + 1)).foldl
      (fun st t => shiftStep p st (eval (sweepSub p k wFalse wTrue t st)))
      (stateOf p g u) =
    stateOf p g (if g then ⟨u.val - 2 ^ k, lt_of_le_of_lt (Nat.sub_le _ _) u.isLt⟩ else u) := by
  set u' : Fin (2 ^ p) := if g then ⟨u.val - 2 ^ k, lt_of_le_of_lt (Nat.sub_le _ _) u.isLt⟩ else u
  set s0 := stateOf p g u
  set s1 := stateOf p g u'
  have h0all : ∀ t : Fin (p + 1), rotState p s0 s1 t.val 0 = s0 t := by
    intro t; unfold rotState; simp [show 0 < p + 1 - t.val by omega]
  apply runSweep_eq
  intro t
  unfold sweepSub
  dsimp only
  have hbit :
      (if ht0 : t.val = 0 then rotState p s0 s1 t.val 0
       else if p - t.val < k then rotState p s0 s1 t.val 0
       else
         let gVal := rotState p s0 s1 t.val ⟨p + 1 - t.val, by omega⟩
         let allZero := (List.range (p - t.val - k)).all fun r =>
           if hr : r + 1 < p + 1 then !(rotState p s0 s1 t.val ⟨r + 1, hr⟩) else true
         xor (rotState p s0 s1 t.val 0) (gVal && allZero)) = s1 t := by
    refine Fin.cases ?_ ?_ t
    · simp only [Fin.val_zero, ↓reduceDIte]
      have h00 := h0all 0
      simp only [Fin.val_zero] at h00
      rw [h00]; simp [s0, s1, stateOf]
    · intro j
      simp only [Fin.val_succ, Nat.succ_ne_zero, ↓reduceDIte]
      have h0j : rotState p s0 s1 (j.val + 1) 0 = u.val.testBit (p - 1 - j.val) := by
        have := h0all j.succ; simp only [Fin.val_succ] at this
        rw [this]; simp [s0, stateOf, natToBits]
      have h1j : s1 j.succ = u'.val.testBit (p - 1 - j.val) := by
        simp [s1, stateOf, natToBits]
      have hsub_eq : p - (j.val + 1) = p - 1 - j.val := by omega
      rw [h0j, h1j, hsub_eq]
      by_cases hlt : p - 1 - j.val < k
      · simp only [hlt, ↓reduceIte]
        cases g
        · rfl
        · simp only [u', ↓reduceIte]
          rw [testBit_sub_two_pow u.val k (p - 1 - j.val) (hge rfl)]
          simp [hlt]
      · simp only [hlt, ↓reduceIte]
        have hgVal : rotState p s0 s1 (j.val + 1) ⟨p + 1 - (j.val + 1), by omega⟩ = g := by
          unfold rotState
          have hnot : ¬ (p + 1 - (j.val + 1) < p + 1 - (j.val + 1)) := lt_irrefl _
          simp only [hnot, ↓reduceDIte, Nat.sub_self]
          simp [s1, stateOf]
        rw [hgVal]
        cases g
        · simp [u']
        · simp only [u', ↓reduceIte, Bool.true_and]
          rw [testBit_sub_two_pow u.val k (p - 1 - j.val) (hge rfl)]
          simp only [hlt, ↓reduceIte]
          congr 1
          have hall : ((List.range (p - 1 - j.val - k)).all fun r =>
              if hr : r + 1 < p + 1 then !(rotState p s0 s1 (j.val + 1) ⟨r + 1, hr⟩) else true) =
              decide (∀ r, k ≤ r → r < p - 1 - j.val → u.val.testBit r = false) := by
            rw [Bool.eq_iff_iff]
            simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]
            constructor
            · intro h r hkr hrlt
              have hidx : p - 1 - j.val - 1 - r < p - 1 - j.val - k := by omega
              have h1 := h (p - 1 - j.val - 1 - r) hidx
              have hr1 : p - 1 - j.val - 1 - r + 1 < p + 1 := by omega
              simp only [hr1, ↓reduceDIte, Bool.not_eq_true'] at h1
              have hlt_rot : p - 1 - j.val - 1 - r + 1 < p + 1 - (j.val + 1) := by omega
              unfold rotState at h1
              simp only [hlt_rot, ↓reduceDIte] at h1
              have hfin : (⟨p - 1 - j.val - 1 - r + 1 + (j.val + 1), by omega⟩ : Fin (p + 1)) =
                  Fin.succ ⟨p - 1 - r, by omega⟩ := by ext; simp; omega
              rw [hfin] at h1
              simp only [s0, stateOf, Fin.cons_succ, natToBits] at h1
              have hsub2 : p - 1 - (p - 1 - r) = r := by omega
              rwa [hsub2] at h1
            · intro h r hrlt
              have hr1 : r + 1 < p + 1 := by omega
              simp only [hr1, ↓reduceDIte, Bool.not_eq_true']
              have hlt_rot : r + 1 < p + 1 - (j.val + 1) := by omega
              unfold rotState
              simp only [hlt_rot, ↓reduceDIte]
              have hfin : (⟨r + 1 + (j.val + 1), by omega⟩ : Fin (p + 1)) =
                  Fin.succ ⟨r + 1 + j.val, by omega⟩ := by ext; simp; omega
              rw [hfin]
              simp only [s0, stateOf, Fin.cons_succ, natToBits]
              exact h (p - 1 - (r + 1 + j.val)) (by omega) (by omega)
          exact hall
  simp only [hbit]
  cases s1 t <;> simp [hf, ht]

lemma runSweep_clearGuard (p wFalse wTrue : ℕ) (eval : ℕ → Bool)
    (hf : eval wFalse = false) (ht : eval wTrue = true)
    (g : Bool) (u : Fin (2 ^ p)) :
    (List.finRange (p + 1)).foldl
      (fun st t => shiftStep p st (eval (sweepClearGuard p wFalse wTrue t st)))
      (stateOf p g u) =
    stateOf p false u := by
  apply runSweep_eq
  intro t
  unfold sweepClearGuard
  refine Fin.cases ?_ ?_ t
  · simp [stateOf, hf]
  · intro r
    simp only [Fin.val_succ, Nat.succ_ne_zero, ↓reduceIte]
    have h0 : rotState p (stateOf p g u) (stateOf p false u) (r.val + 1) 0 =
        stateOf p false u r.succ := by
      unfold rotState
      simp only [Fin.val_zero, show 0 < p + 1 - (r.val + 1) by omega, ↓reduceDIte, Nat.zero_add]
      have hfin : (⟨r.val + 1, by omega⟩ : Fin (p + 1)) = r.succ := by ext; simp
      rw [hfin]; simp [stateOf]
    simp only [h0]
    cases stateOf p false u r.succ <;> simp [hf, ht]

lemma runSweep_clearTag (d wFalse wTrue : ℕ) (eval : ℕ → Bool)
    (hf : eval wFalse = false) (ht : eval wTrue = true)
    (y : Fin d → Bool) :
    (List.finRange (d + 2)).foldl
      (fun st t => shiftStep (d + 1) st (eval (sweepClearTag (d + 1) wFalse wTrue t st)))
      (stateOf (d + 1) false ⟨2 ^ d + bitsToNat y, by
        have := bitsToNat_lt y; rw [pow_succ]; omega⟩) =
    stateOf (d + 1) false ⟨bitsToNat y, by
      have := bitsToNat_lt y; rw [pow_succ]; omega⟩ := by
  set s0 := stateOf (d + 1) false ⟨2 ^ d + bitsToNat y, by
    have := bitsToNat_lt y; rw [pow_succ]; omega⟩
  set s1 := stateOf (d + 1) false ⟨bitsToNat y, by
    have := bitsToNat_lt y; rw [pow_succ]; omega⟩
  apply runSweep_eq
  intro t
  unfold sweepClearTag
  by_cases ht1 : t.val = 1
  · simp only [ht1, ↓reduceIte, hf]
    have ht_fin : t = Fin.succ 0 := by ext; simp [ht1]
    rw [ht_fin]
    simp only [s1, stateOf, Fin.cons_succ, natToBits_eq_cons_false, Fin.cons_zero]
  · simp only [ht1, ↓reduceIte]
    have h0 : rotState (d + 1) s0 s1 t.val 0 = s0 t := by
      unfold rotState; simp [show 0 < d + 2 - t.val by omega]
    have hst : s0 t = s1 t := by
      revert ht1
      refine Fin.cases ?_ ?_ t
      · intro _; simp [s0, s1, stateOf]
      · intro r
        refine Fin.cases ?_ ?_ r
        · intro ht1; exfalso; exact ht1 rfl
        · intro r' _
          simp [s0, s1, stateOf, natToBits_eq_cons_false, natToBits_eq_cons_true]
    simp only [h0, hst]
    cases s1 t <;> simp [hf, ht]

lemma inp_length (d : ℕ) (f : (Fin d → Bool) → (Fin d → Bool)) :
    (List.ofFn (fun i : Fin (2 ^ d) => List.ofFn
      (f (fun j => i.val.testBit (d - 1 - j.val))))).flatten.length = 2 ^ d * d := by
  rw [List.length_flatten, List.map_ofFn]
  simp [Function.comp_def]

lemma inp_getD (d : ℕ) (f : (Fin d → Bool) → (Fin d → Bool))
    (i : Fin (2 ^ d)) (j : Fin d) :
    ((List.ofFn (fun i : Fin (2 ^ d) => List.ofFn
      (f (fun j => i.val.testBit (d - 1 - j.val))))).flatten).getD (i.val * d + j.val) false =
      f (natToBits d i.val) j := by
  set L := List.ofFn (fun i : Fin (2 ^ d) => List.ofFn
    (f (fun j => i.val.testBit (d - 1 - j.val))))
  have hL_len : ∀ x ∈ L, x.length = d := by
    intro x hx
    simp only [L, List.mem_ofFn] at hx
    rcases hx with ⟨_, rfl⟩
    simp
  have hlt : i.val * d + j.val < L.flatten.length := by
    rw [inp_length]
    have h1 : i.val + 1 ≤ 2 ^ d := i.isLt
    calc i.val * d + j.val < i.val * d + d := Nat.add_lt_add_left j.isLt _
      _ = (i.val + 1) * d := by ring
      _ ≤ 2 ^ d * d := Nat.mul_le_mul_right d h1
  rw [List.getD_eq_getElem _ _ hlt]
  have hget := flatten_getElem_uniform L d hL_len i.val j.val (by simp [L]) j.isLt
  rw [hget]
  simp only [L, List.getElem_ofFn]
  rfl

lemma list_eq_of_bitsListToNat_eq (l1 l2 : List Bool) (hlen : l1.length = l2.length)
    (hnat : bitsListToNat l1 = bitsListToNat l2) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all
  | cons a as ih =>
    cases l2 with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [bitsListToNat, hlen] at hnat
      have ha := bitsListToNat_lt as
      have hb := bitsListToNat_lt bs
      rw [hlen] at ha
      cases a <;> cases b
      · simp at hnat; exact congrArg (List.cons false) (ih bs hlen hnat)
      · simp at hnat; omega
      · simp at hnat; omega
      · simp at hnat; exact congrArg (List.cons true) (ih bs hlen hnat)

lemma bitsListToNat_take_eq_div_two (l : List Bool) (d : ℕ) (hlen : l.length = d + 1) :
    bitsListToNat (l.take d) = bitsListToNat l / 2 := by
  have hsplit : l = l.take d ++ [l[d]'(by omega)] := by
    have h1 := List.take_append_drop d l
    have hdrop : l.drop d = [l[d]'(by omega)] := by
      apply List.ext_getElem
      · simp [hlen]
      · intro i hi1 hi2
        have hi0 : i = 0 := by simp at hi2; omega
        subst hi0; simp
    rw [hdrop] at h1
    exact h1.symm
  conv_rhs => rw [hsplit, bitsListToNat_append_singleton]
  cases l[d]'(by omega)
  · simp
  · simp; omega

lemma runLayerPerms_spec (p : ℕ) (arr0 : Fin (2 ^ p) → ℕ)
    (sched : List (ℕ × ℕ)) (hs : ∀ e ∈ sched, e.2 < p) :
    let perms := runLayerPerms p arr0 sched hs
    (∀ u, perms.reverse.foldl (fun x π => π x) (perms.foldl (fun x π => π x) u) = u) ∧
    (∀ u, perms.foldl (fun x π => π x) (perms.reverse.foldl (fun x π => π x) u) = u) ∧
    (∀ u, applySchedule p sched hs arr0 (perms.foldl (fun x π => π x) u) = arr0 u) ∧
    (∀ u, applySchedule p sched hs arr0 u = arr0 (perms.reverse.foldl (fun x π => π x) u)) := by
  induction sched generalizing arr0 with
  | nil =>
    refine ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  | cons e es ih =>
    dsimp only [runLayerPerms]
    set hj := hs e (by simp)
    set π := layerPerm p e.1 e.2 hj arr0
    set arr1 := applyLayer p e.1 e.2 hj arr0
    have hinv : ∀ u, π (π u) = u := layerPerm_invol p e.1 e.2 hj arr0
    have hcomp : ∀ u, arr1 u = arr0 (π u) := applyLayer_eq_comp_layerPerm p e.1 e.2 hj arr0
    have hrec := ih arr1 (fun x hx => hs x (by simp [hx]))
    rcases hrec with ⟨hr1, hr2, hr3, hr4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u
      simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hr1 (π u), hinv u]
    · intro u
      simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hinv, hr2 u]
    · intro u
      simp only [List.foldl_cons, applySchedule]
      rw [hr3 (π u), hcomp (π u), hinv u]
    · intro u
      simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, applySchedule]
      rw [hr4 u, hcomp]

lemma main_proof (d : ℕ) :
    let p := d + 1
    let w := p + 1
    let rows := w * (p + 2) ^ 2
    let I := 2 ^ d * d
    let D := Fin d → Bool
    let State := Fin w → Bool
    let active := fun (v : D) => Fin.cons (α := fun _ : Fin w => Bool) false
      (Fin.cons (α := fun _ : Fin p => Bool) false v)
    ∃ (C : Circuit)
      (out : Fin rows → State → Fin (I + C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧ C.output < I + C.size ∧
      C.size ≤ 128 * 2 ^ p * (p + 2) ^ 3 ∧
      ∀ f : D → D,
        let inp := (List.ofFn (fun i : Fin (2 ^ d) => List.ofFn
          (f (fun j => i.val.testBit (d - 1 - j.val))))).flatten
        ∀ v : D, (List.finRange rows).foldl (fun (s : State) row =>
          Fin.snoc (α := fun _ : Fin w => Bool) (fun j : Fin p => s j.succ)
            ((C.wires inp).getD (out row s).val false)) (active v) = active (f v) := by
  intro p w rows I D State active
  obtain ⟨hFe, hFl, hFw, hFv⟩ := mkFalse_spec I []
  set rF := mkFalse I []
  set wFalse := rF.2
  obtain ⟨hTe, hTl, hTw, hTv⟩ := mkTrue_spec I rF.1
  set rT := mkTrue I rF.1
  set wTrue := rT.2
  have heFT : Extends I [] rT.1 := extends_trans hFe hTe
  have hlenT : rT.1.length = 2 := by simp at hFl; omega
  have hwfT : wFalse < I + rT.1.length := by omega
  have hwtT : wTrue < I + rT.1.length := by omega
  let initKeys : Fin (2 ^ p) → List ℕ := fun u =>
    if u.val < 2 ^ d then
      List.ofFn (fun j : Fin d => u.val * d + j.val) ++ [wTrue]
    else
      List.ofFn (fun j : Fin d => if (u.val - 2 ^ d).testBit (d - 1 - j.val) then wTrue else wFalse) ++ [wFalse]
  have hinit_len : ∀ u, (initKeys u).length = p := by
    intro u; dsimp [initKeys]; split <;> simp [p]
  have hinit_lt : ∀ u w0, w0 ∈ initKeys u → w0 < I + rT.1.length := by
    intro u w0 hw0
    dsimp [initKeys] at hw0
    split at hw0
    · rename_i hlt
      simp only [List.mem_append, List.mem_ofFn, List.mem_singleton] at hw0
      rcases hw0 with ⟨j, rfl⟩ | rfl
      · have h1 : u.val + 1 ≤ 2 ^ d := hlt
        have h2 : u.val * d + j.val < 2 ^ d * d := by
          calc u.val * d + j.val < u.val * d + d := Nat.add_lt_add_left j.isLt _
            _ = (u.val + 1) * d := by ring
            _ ≤ 2 ^ d * d := Nat.mul_le_mul_right d h1
        change u.val * d + j.val < I + rT.1.length
        omega
      · exact hwtT
    · simp only [List.mem_append, List.mem_ofFn, List.mem_singleton] at hw0
      rcases hw0 with ⟨j, rfl⟩ | rfl
      · split <;> assumption
      · exact hwfT
  set sched := bitonicSchedule p
  have hsched_lt : ∀ e ∈ sched, e.2 < p := bitonicSchedule_lt p
  obtain ⟨hNet_e, hNet_sz, hNet_klen, hNet_klt, hNet_clt, hNet_v⟩ :=
    buildNetwork_spec I wFalse p sched hsched_lt rT.1 initKeys hwfT hinit_len hinit_lt
  set rNet := buildNetwork I wFalse p sched hsched_lt rT.1 initKeys
  have hNet_len : rNet.2.2.length = sched.length := buildNetwork_len I wFalse p sched hsched_lt rT.1 initKeys
  have hlen_T_Net : rT.1.length ≤ rNet.1.length := extends_length_le hNet_e
  obtain ⟨hStr_e, hStr_sz, hStr_lt, hStr_v⟩ :=
    buildAllStridesAux_spec I wFalse wTrue p d (by omega) rNet.2.1 p rNet.1
      (fun _ _ => wFalse) (by omega) (by omega) hNet_klen hNet_klt (fun _ _ => by omega)
  set rStr := buildAllStridesAux I wFalse wTrue p d rNet.2.1 p rNet.1 (fun _ _ => wFalse)
  have hlen_Net_Str : rNet.1.length ≤ rStr.1.length := extends_length_le hStr_e
  have heAll : Extends I [] rStr.1 := extends_trans heFT (extends_trans hNet_e hStr_e)
  have hValid : ValidGates I rStr.1 := extends_valid heAll (validGates_nil I)
  set C : Circuit := ⟨rStr.1, 0⟩
  have hFanIn : PEqualNP.MetaComplexity.FanInTwo C := hValid.1
  have hReads : PEqualNP.MetaComplexity.NestedCover.ReadsBack I C := hValid.2
  have hOutLt : C.output < I + C.size := by
    change 0 < I + rStr.1.length; omega
  have hSizeBound : C.size ≤ 128 * 2 ^ p * (p + 2) ^ 3 := by
    have hlenS : 2 * sched.length = p * (p + 1) := bitonicSchedule_length_mul_two p
    have hS_le : sched.length ≤ p * (p + 1) := by omega
    have hpow_ge : 2 ≤ 2 ^ p := by
      have : 1 ≤ p := by omega
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) this
    have hp1 : 1 ≤ (p + 2) ^ 3 := by
      have : (p + 2) ^ 3 = p ^ 3 + 6 * p ^ 2 + 12 * p + 8 := by ring
      omega
    have hterm1 : 2 ≤ 2 ^ p * (p + 2) ^ 3 := by nlinarith
    have hterm2 : sched.length * (2 ^ p * (11 * p + 1)) ≤ 11 * 2 ^ p * (p + 2) ^ 3 := by
      have ha : sched.length * (11 * p + 1) ≤ 11 * (p + 2) ^ 3 := by
        have hb : sched.length * (11 * p + 1) ≤ (p * (p + 1)) * (11 * p + 1) :=
          Nat.mul_le_mul_right _ hS_le
        have hc : 11 * (p + 2) ^ 3 = (p * (p + 1)) * (11 * p + 1) + (54 * p ^ 2 + 131 * p + 88) := by ring
        omega
      calc sched.length * (2 ^ p * (11 * p + 1)) = 2 ^ p * (sched.length * (11 * p + 1)) := by ring
        _ ≤ 2 ^ p * (11 * (p + 2) ^ 3) := Nat.mul_le_mul_left _ ha
        _ = 11 * 2 ^ p * (p + 2) ^ 3 := by ring
    have hterm3 : p * (2 ^ p * (6 * d)) ≤ 6 * 2 ^ p * (p + 2) ^ 3 := by
      have ha : p * (6 * d) ≤ 6 * (p + 2) ^ 3 := by
        have hdp : d ≤ p := by omega
        have h1 : p * (6 * d) ≤ p * (6 * p) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hdp)
        have h2 : 6 * (p + 2) ^ 3 = 6 * p ^ 3 + 36 * p ^ 2 + 72 * p + 48 := by ring
        have h3 : p * (6 * p) = 6 * p ^ 2 := by ring
        omega
      calc p * (2 ^ p * (6 * d)) = 2 ^ p * (p * (6 * d)) := by ring
        _ ≤ 2 ^ p * (6 * (p + 2) ^ 3) := Nat.mul_le_mul_left _ ha
        _ = 6 * 2 ^ p * (p + 2) ^ 3 := by ring
    have hsum : 128 * 2 ^ p * (p + 2) ^ 3 =
        2 ^ p * (p + 2) ^ 3 + 11 * 2 ^ p * (p + 2) ^ 3 + 6 * 2 ^ p * (p + 2) ^ 3 +
          110 * 2 ^ p * (p + 2) ^ 3 := by ring
    change rStr.1.length ≤ 128 * 2 ^ p * (p + 2) ^ 3
    omega
  let fwdSweeps : List (Fin w → State → ℕ) :=
    rNet.2.2.map fun lc => sweepSwap p wFalse wTrue lc.1 lc.2
  let strideSweeps : List (Fin w → State → ℕ) :=
    ((List.finRange p).reverse).flatMap fun k =>
      [sweepLoadGuard p (rStr.2 k) wFalse wTrue,
       sweepSub p k.val wFalse wTrue,
       sweepClearGuard p wFalse wTrue]
  let revSweeps : List (Fin w → State → ℕ) :=
    rNet.2.2.reverse.map fun lc => sweepSwap p wFalse wTrue lc.1 lc.2
  let tailSweeps : List (Fin w → State → ℕ) :=
    [sweepClearTag p wFalse wTrue,
     sweepId p wFalse wTrue,
     sweepId p wFalse wTrue,
     sweepId p wFalse wTrue]
  let allSweeps : List (Fin w → State → ℕ) :=
    fwdSweeps ++ strideSweeps ++ revSweeps ++ tailSweeps
  have hallLen : allSweeps.length = (p + 2) ^ 2 := by
    have h2S : 2 * sched.length = p * (p + 1) := bitonicSchedule_length_mul_two p
    have hstrL : strideSweeps.length = 3 * p := by
      dsimp [strideSweeps]
      rw [List.length_flatMap]
      have hmap : (((List.finRange p).reverse).map fun _ => 3) = List.replicate p 3 := by
        apply List.ext_getElem <;> simp
      change ((((List.finRange p).reverse).map fun _ => 3)).sum = 3 * p
      rw [hmap, List.sum_replicate, smul_eq_mul]; ring
    simp only [allSweeps, fwdSweeps, revSweeps, tailSweeps, List.length_append, List.length_map,
      List.length_reverse, List.length_cons, List.length_nil, hNet_len, hstrL]
    nlinarith
  have hwf_all : wFalse < I + C.size := by change wFalse < I + rStr.1.length; omega
  have hwt_all : wTrue < I + C.size := by change wTrue < I + rStr.1.length; omega
  have hall_lt : ∀ sw ∈ allSweeps, ∀ t st, sw t st < I + C.size := by
    intro sw hsw t st
    simp only [allSweeps, List.mem_append] at hsw
    rcases hsw with ((h | h) | h) | h
    · simp only [fwdSweeps, List.mem_map] at h
      rcases h with ⟨lc, hlc, rfl⟩
      unfold sweepSwap
      split
      · dsimp only
        have hlc_lt := (hNet_clt lc hlc).2
        split
        · exact lt_of_lt_of_le (hlc_lt _).2 (by change I + rNet.1.length ≤ I + rStr.1.length; omega)
        · exact lt_of_lt_of_le (hlc_lt _).1 (by change I + rNet.1.length ≤ I + rStr.1.length; omega)
      · split
        · exact hwt_all
        · exact hwf_all
    · simp only [strideSweeps, List.mem_flatMap, List.mem_reverse, List.mem_finRange,
        List.mem_cons, List.not_mem_nil, or_false, true_and] at h
      rcases h with ⟨k, rfl | rfl | rfl⟩
      · unfold sweepLoadGuard
        split
        · exact hStr_lt k _
        · split
          · exact hwt_all
          · exact hwf_all
      · unfold sweepSub
        have hite : ∀ b : Bool, (if b then wTrue else wFalse) < I + C.size := by
          intro b; cases b <;> [exact hwf_all; exact hwt_all]
        exact hite _
      · unfold sweepClearGuard; split
        · exact hwf_all
        · split
          · exact hwt_all
          · exact hwf_all
    · simp only [revSweeps, List.mem_map, List.mem_reverse] at h
      rcases h with ⟨lc, hlc, rfl⟩
      unfold sweepSwap
      split
      · dsimp only
        have hlc_lt := (hNet_clt lc hlc).2
        split
        · exact lt_of_lt_of_le (hlc_lt _).2 (by change I + rNet.1.length ≤ I + rStr.1.length; omega)
        · exact lt_of_lt_of_le (hlc_lt _).1 (by change I + rNet.1.length ≤ I + rStr.1.length; omega)
      · split
        · exact hwt_all
        · exact hwf_all
    · simp only [tailSweeps, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl
      · unfold sweepClearTag; split
        · exact hwf_all
        · split
          · exact hwt_all
          · exact hwf_all
      · unfold sweepId; split
        · exact hwt_all
        · exact hwf_all
      · unfold sweepId; split
        · exact hwt_all
        · exact hwf_all
      · unfold sweepId; split
        · exact hwt_all
        · exact hwf_all
  let out : Fin rows → State → Fin (I + C.size) := fun row st =>
    let swIdx := row.val / w
    let tIdx := row.val % w
    have hsw : swIdx < allSweeps.length := by
      rw [hallLen]
      have hwpos : 0 < w := by omega
      rw [Nat.div_lt_iff_lt_mul hwpos, Nat.mul_comm]
      exact row.isLt
    have ht : tIdx < w := Nat.mod_lt _ (by omega)
    ⟨(allSweeps[swIdx]'hsw) ⟨tIdx, ht⟩ st, hall_lt _ (List.getElem_mem hsw) _ _⟩
  refine ⟨C, out, hFanIn, hReads, hOutLt, hSizeBound, ?_⟩
  intro f inp v
  have hinp_len : inp.length = I := inp_length d f
  set eval : ℕ → Bool := wireVal rStr.1 inp
  have hevalF : eval wFalse = false := by
    have h1 := hFv inp hinp_len
    have h2 : Extends I rF.1 rStr.1 := extends_trans hTe (extends_trans hNet_e hStr_e)
    dsimp [eval]
    rw [extends_wireVal h2 inp hinp_len wFalse hFw, h1]
  have hevalT : eval wTrue = true := by
    have h1 := hTv inp hinp_len
    have h2 : Extends I rT.1 rStr.1 := extends_trans hNet_e hStr_e
    dsimp [eval]
    rw [extends_wireVal h2 inp hinp_len wTrue hTw, h1]
  have hwf_rT : wireVal rT.1 inp wFalse = false := by
    rw [extends_wireVal hTe inp hinp_len wFalse hFw, hFv inp hinp_len]
  have hwt_rT : wireVal rT.1 inp wTrue = true := hTv inp hinp_len
  have hwf_rNet : wireVal rNet.1 inp wFalse = false := by
    rw [extends_wireVal hNet_e inp hinp_len wFalse hwfT, hwf_rT]
  have hwt_rNet : wireVal rNet.1 inp wTrue = true := by
    rw [extends_wireVal hNet_e inp hinp_len wTrue hwtT, hwt_rT]
  let initArr : Fin (2 ^ p) → ℕ := fun u =>
    if u.val < 2 ^ d then
      2 * bitsToNat (f (natToBits d u.val)) + 1
    else
      2 * (u.val - 2 ^ d)
  have hinit_eval : ∀ u, bitsListToNat ((initKeys u).map (wireVal rT.1 inp)) = initArr u := by
    intro u
    dsimp [initKeys, initArr]
    split
    · rename_i hlt
      rw [List.map_append, List.map_singleton, bitsListToNat_append_singleton, hwt_rT]
      simp only [↓reduceIte]
      congr 2
      unfold bitsToNat
      congr 1
      rw [List.map_ofFn]
      congr 1
      funext j
      dsimp [Function.comp_def]
      have hidx_lt : u.val * d + j.val < inp.length := by
        rw [hinp_len]
        have h1 : u.val + 1 ≤ 2 ^ d := hlt
        calc u.val * d + j.val < u.val * d + d := Nat.add_lt_add_left j.isLt _
          _ = (u.val + 1) * d := by ring
          _ ≤ 2 ^ d * d := Nat.mul_le_mul_right d h1
      rw [wireVal_input rT.1 inp _ hidx_lt]
      exact inp_getD d f ⟨u.val, hlt⟩ j
    · rename_i hge
      rw [List.map_append, List.map_singleton, bitsListToNat_append_singleton, hwf_rT]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      congr 1
      have hmap : (List.ofFn (fun j : Fin d =>
          if (u.val - 2 ^ d).testBit (d - 1 - j.val) then wTrue else wFalse)).map (wireVal rT.1 inp) =
          List.ofFn (natToBits d (u.val - 2 ^ d)) := by
        rw [List.map_ofFn]
        congr 1
        funext j
        dsimp [Function.comp_def, natToBits]
        cases (u.val - 2 ^ d).testBit (d - 1 - j.val)
        · simp [hwf_rT]
        · simp [hwt_rT]
      rw [hmap]
      have hlt_sub : u.val - 2 ^ d < 2 ^ d := by
        have := u.isLt; have : 2 ^ p = 2 ^ d + 2 ^ d := by rw [pow_succ]; omega
        omega
      exact bitsToNat_natToBits d (u.val - 2 ^ d) hlt_sub
  have hNet_val := hNet_v inp hinp_len hwf_rT
  set sortedArr : Fin (2 ^ p) → ℕ := applySchedule p sched hsched_lt initArr
  have hNet_sorted : ∀ u, bitsListToNat ((rNet.2.1 u).map (wireVal rNet.1 inp)) = sortedArr u := by
    intro u
    have h1 := hNet_val.1 u
    have hfn : (fun u => bitsListToNat ((initKeys u).map (wireVal rT.1 inp))) = initArr :=
      funext hinit_eval
    rwa [hfn] at h1
  have hsorted_mono : Monotone sortedArr := bitonic_sort_monotone p initArr
  set perms := runLayerPerms p initArr sched hsched_lt
  have hperms_len : perms.length = sched.length := runLayerPerms_length p initArr sched hsched_lt
  have hperms_spec := runLayerPerms_spec p initArr sched hsched_lt
  have hStr_val := hStr_v inp hinp_len hwf_rNet hwt_rNet
  have hfold_sweeps :
      (List.finRange rows).foldl (fun (s : State) row =>
        Fin.snoc (α := fun _ : Fin w => Bool) (fun j : Fin p => s j.succ)
          ((C.wires inp).getD (out row s).val false)) (active v) =
      allSweeps.foldl (fun s sw =>
        (List.finRange w).foldl (fun st t => shiftStep p st (eval (sw t st))) s) (active v) := by
    rw [foldl_finRange_mul w ((p + 2) ^ 2)]
    have hlist : allSweeps = (List.finRange ((p + 2) ^ 2)).map (fun i => allSweeps[i.val]'(by omega)) := by
      apply List.ext_getElem
      · simp [hallLen]
      · intro i hi1 hi2; simp
    conv_rhs => rw [hlist, List.foldl_map]
    congr 1
    funext s sw
    congr 1
    funext st t
    have hdiv : (sw.val * w + t.val) / w = sw.val := by
      rw [Nat.mul_comm sw.val w, Nat.mul_add_div (by omega), Nat.div_eq_of_lt t.isLt, Nat.add_zero]
    have hmod : (sw.val * w + t.val) % w = t.val := by
      rw [Nat.mul_comm sw.val w, Nat.mul_add_mod, Nat.mod_eq_of_lt t.isLt]
    have hout_eq : (out ⟨sw.val * w + t.val, by
        have h1 : sw.val + 1 ≤ (p + 2) ^ 2 := sw.isLt
        calc sw.val * w + t.val < sw.val * w + w := Nat.add_lt_add_left t.isLt _
          _ = (sw.val + 1) * w := by ring
          _ ≤ (p + 2) ^ 2 * w := Nat.mul_le_mul_right w h1
          _ = w * (p + 2) ^ 2 := Nat.mul_comm _ _⟩ st).val =
        (allSweeps[sw.val]'(by omega)) t st := by
      dsimp only [out]
      have hsw_eq : allSweeps[(sw.val * w + t.val) / w]'(by omega) = allSweeps[sw.val]'(by omega) := by
        congr 1
      have ht_eq : (⟨(sw.val * w + t.val) % w, by omega⟩ : Fin w) = t := by ext; exact hmod
      rw [hsw_eq, ht_eq]
    change shiftStep p st (eval (out _ st).val) = shiftStep p st (eval ((allSweeps[sw.val]'(by omega)) t st))
    rw [hout_eq]
  rw [hfold_sweeps]
  have hactive_eq : ∀ y : D,
      active y = stateOf p false ⟨bitsToNat y, by
        have := bitsToNat_lt y; rw [pow_succ]; omega⟩ := by
    intro y
    unfold active stateOf
    rw [natToBits_eq_cons_false]
  rw [hactive_eq v, hactive_eq (f v)]
  simp only [allSweeps, List.foldl_append]
  set u0 : Fin (2 ^ p) := ⟨bitsToNat v, by have := bitsToNat_lt v; rw [pow_succ]; omega⟩
  have hlayer_step : ∀ (idx : ℕ) (hidx : idx < sched.length) (u : Fin (2 ^ p)),
      let lc := rNet.2.2[idx]'(by rw [hNet_len]; exact hidx)
      let perm := perms[idx]'(by rw [hperms_len]; exact hidx)
      (List.finRange w).foldl
        (fun st t => shiftStep p st (eval (sweepSwap p wFalse wTrue lc.1 lc.2 t st)))
        (stateOf p false u) =
      stateOf p false (perm u) := by
    intro idx hidx u
    dsimp only
    set lc := rNet.2.2[idx]'(by rw [hNet_len]; exact hidx)
    have hlc_mem : lc ∈ rNet.2.2 := List.getElem_mem _
    have hlc_j : lc.1 < p := (hNet_clt lc hlc_mem).1
    have hlc_lt := (hNet_clt lc hlc_mem).2 ⟨loBit lc.1 u.val, loBit_lt u.isLt⟩
    have hfn : (fun u => bitsListToNat ((initKeys u).map (wireVal rT.1 inp))) = initArr :=
      funext hinit_eval
    have hspec := hNet_val.2 idx hidx u
    dsimp only at hspec
    rw [hfn] at hspec
    have hc1 : eval (lc.2 ⟨loBit lc.1 u.val, loBit_lt u.isLt⟩).1 =
        wireVal rNet.1 inp (lc.2 ⟨loBit lc.1 u.val, loBit_lt u.isLt⟩).1 :=
      extends_wireVal hStr_e inp hinp_len _ hlc_lt.1
    have hc2 : eval (lc.2 ⟨loBit lc.1 u.val, loBit_lt u.isLt⟩).2 =
        !(wireVal rNet.1 inp (lc.2 ⟨loBit lc.1 u.val, loBit_lt u.isLt⟩).1) := by
      change wireVal rStr.1 inp (lc.2 ⟨loBit lc.1 u.val, loBit_lt u.isLt⟩).2 = _
      rw [extends_wireVal hStr_e inp hinp_len _ hlc_lt.2]
      exact hspec.1
    rw [runSweep_swap p wFalse wTrue lc.1 hlc_j lc.2 eval hevalF hevalT u _ hc1 hc2]
    congr 1
    exact hspec.2.symm
  have hphase1 :
      fwdSweeps.foldl (fun s sw =>
        (List.finRange w).foldl (fun st t => shiftStep p st (eval (sw t st))) s)
        (stateOf p false u0) =
      stateOf p false (perms.foldl (fun x π => π x) u0) := by
    have hgen : ∀ (k : ℕ) (hk : k ≤ sched.length),
        (fwdSweeps.take k).foldl (fun s sw =>
          (List.finRange w).foldl (fun st t => shiftStep p st (eval (sw t st))) s)
          (stateOf p false u0) =
        stateOf p false ((perms.take k).foldl (fun x π => π x) u0) := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih =>
        have hlt_f : k < fwdSweeps.length := by simp [fwdSweeps, hNet_len]; omega
        have hlt_p : k < perms.length := by rw [hperms_len]; omega
        rw [List.take_succ_eq_append_getElem hlt_f, List.foldl_append, List.foldl_cons, List.foldl_nil,
          ih (by omega)]
        rw [List.take_succ_eq_append_getElem hlt_p, List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [fwdSweeps, List.getElem_map]
        exact hlayer_step k (by omega) _
    have hfull := hgen sched.length (le_refl _)
    rw [List.take_of_length_le (by simp [fwdSweeps, hNet_len]),
      List.take_of_length_le (by rw [hperms_len])] at hfull
    exact hfull
  rw [hphase1]
  set u1 := perms.foldl (fun x π => π x) u0
  set yNat := bitsToNat (f v)
  have hyLt : yNat < 2 ^ d := bitsToNat_lt (f v)
  set m0 : Fin (2 ^ p) := ⟨2 ^ d + yNat, by rw [pow_succ]; omega⟩
  set m := perms.foldl (fun x π => π x) m0
  have hsorted_u1 : sortedArr u1 = 2 * yNat + 1 := by
    dsimp only [sortedArr, u1, perms]
    rw [hperms_spec.2.2.1 u0]
    have hlt0 : u0.val < 2 ^ d := bitsToNat_lt v
    simp only [initArr, hlt0, ↓reduceIte, u0, natToBits_bitsToNat, yNat]
  have hsorted_m : sortedArr m = 2 * yNat := by
    dsimp only [sortedArr, m, perms]
    rw [hperms_spec.2.2.1 m0]
    have hge0 : ¬ (m0.val < 2 ^ d) := by simp [m0]
    simp only [initArr, hge0, ↓reduceIte, m0, Nat.add_sub_cancel_left]
  have hm_le_u1 : m.val ≤ u1.val := by
    by_contra hlt
    push Not at hlt
    have hmono := hsorted_mono (le_of_lt hlt)
    omega
  have hdiv_ge : ∀ pos : Fin (2 ^ p), m.val ≤ pos.val → pos.val ≤ u1.val →
      sortedArr pos / 2 = yNat := by
    intro pos h1 h2
    have hle1 : sortedArr m ≤ sortedArr pos := hsorted_mono h1
    have hle2 : sortedArr pos ≤ sortedArr u1 := hsorted_mono h2
    omega
  have hdiv_lt : ∀ pos : Fin (2 ^ p), pos.val < m.val → sortedArr pos / 2 ≠ yNat := by
    intro pos hlt heq
    have hle : sortedArr pos ≤ sortedArr m := hsorted_mono (le_of_lt hlt)
    have hval : sortedArr pos = 2 * yNat := by omega
    dsimp only [sortedArr] at hval
    rw [hperms_spec.2.2.2 pos] at hval
    set pre := perms.reverse.foldl (fun x π => π x) pos
    have hpre_eq : pre = m0 := by
      dsimp only [initArr] at hval
      split at hval
      · omega
      · ext; dsimp [m0]; omega
    have hpos_eq : pos = m := by
      calc pos = perms.foldl (fun x π => π x) pre := (hperms_spec.2.1 pos).symm
        _ = perms.foldl (fun x π => π x) m0 := by rw [hpre_eq]
        _ = m := rfl
    rw [hpos_eq] at hlt
    exact lt_irrefl _ hlt
  have hstride_eval : ∀ (k : Fin p) (pos : Fin (2 ^ p)),
      m.val ≤ pos.val → pos.val ≤ u1.val →
      eval (rStr.2 k pos) = decide (2 ^ k.val ≤ pos.val - m.val) := by
    intro k pos h1 h2
    dsimp [eval]
    rw [hStr_val k k.isLt pos]
    by_cases hge : 2 ^ k.val ≤ pos.val
    · simp only [hge, ↓reduceDIte]
      set prev : Fin (2 ^ p) := ⟨pos.val - 2 ^ k.val, lt_of_le_of_lt (Nat.sub_le _ _) pos.isLt⟩
      have hlen1 : ((rNet.2.1 prev).map (wireVal rNet.1 inp)).take d =
          ((rNet.2.1 prev).take d).map (wireVal rNet.1 inp) := List.map_take.symm
      have hlen2 : ((rNet.2.1 pos).map (wireVal rNet.1 inp)).take d =
          ((rNet.2.1 pos).take d).map (wireVal rNet.1 inp) := List.map_take.symm
      have hiff : (((rNet.2.1 prev).take d).map (wireVal rNet.1 inp) =
                   ((rNet.2.1 pos).take d).map (wireVal rNet.1 inp)) ↔
                  sortedArr prev / 2 = sortedArr pos / 2 := by
        rw [← hlen1, ← hlen2]
        constructor
        · intro heq
          have hb := congrArg bitsListToNat heq
          rw [bitsListToNat_take_eq_div_two _ d (by simp [hNet_klen, p]),
            bitsListToNat_take_eq_div_two _ d (by simp [hNet_klen, p]),
            hNet_sorted prev, hNet_sorted pos] at hb
          exact hb
        · intro heq
          apply list_eq_of_bitsListToNat_eq
          · simp [hNet_klen, p]
          · rw [bitsListToNat_take_eq_div_two _ d (by simp [hNet_klen, p]),
              bitsListToNat_take_eq_div_two _ d (by simp [hNet_klen, p]),
              hNet_sorted prev, hNet_sorted pos]
            exact heq
      rw [decide_eq_decide]
      rw [hiff, hdiv_ge pos h1 h2]
      constructor
      · intro hprev
        by_contra hlt
        push Not at hlt
        have : prev.val < m.val := by dsimp [prev]; omega
        exact hdiv_lt prev this hprev
      · intro hge_m
        have hprev_le : prev.val ≤ pos.val := Nat.sub_le _ _
        exact hdiv_ge prev (by dsimp [prev]; omega) (le_trans hprev_le h2)
    · simp only [hge, ↓reduceDIte]
      have hnot : ¬ (2 ^ k.val ≤ pos.val - m.val) := by omega
      simp [hnot]
  have hphase2 :
      strideSweeps.foldl (fun s sw =>
        (List.finRange w).foldl (fun st t => shiftStep p st (eval (sw t st))) s)
        (stateOf p false u1) =
      stateOf p false m := by
    have hstep_k : ∀ (k : Fin p) (pos : Fin (2 ^ p)),
        m.val ≤ pos.val → pos.val ≤ u1.val → pos.val - m.val < 2 ^ (k.val + 1) →
        ∃ pos' : Fin (2 ^ p),
          ([sweepLoadGuard p (rStr.2 k) wFalse wTrue,
            sweepSub p k.val wFalse wTrue,
            sweepClearGuard p wFalse wTrue].foldl (fun s sw =>
              (List.finRange w).foldl (fun st t => shiftStep p st (eval (sw t st))) s)
              (stateOf p false pos) = stateOf p false pos') ∧
          m.val ≤ pos'.val ∧ pos'.val ≤ u1.val ∧ pos'.val - m.val < 2 ^ k.val := by
      intro k pos h1 h2 h3
      simp only [List.foldl_cons, List.foldl_nil]
      rw [runSweep_loadGuard p wFalse wTrue (rStr.2 k) eval hevalF hevalT pos]
      rw [hstride_eval k pos h1 h2]
      have hge_imp : decide (2 ^ k.val ≤ pos.val - m.val) = true → 2 ^ k.val ≤ pos.val := by
        intro hd; simp at hd; omega
      rw [runSweep_sub p k.val wFalse wTrue k.isLt eval hevalF hevalT _ pos hge_imp]
      rw [runSweep_clearGuard p wFalse wTrue eval hevalF hevalT]
      refine ⟨if decide (2 ^ k.val ≤ pos.val - m.val) then
          ⟨pos.val - 2 ^ k.val, lt_of_le_of_lt (Nat.sub_le _ _) pos.isLt⟩ else pos,
        rfl, ?_, ?_, ?_⟩
      · by_cases h : 2 ^ k.val ≤ pos.val - m.val <;> (simp [h]; omega)
      · by_cases h : 2 ^ k.val ≤ pos.val - m.val
        · simp only [h, decide_true, ↓reduceIte]
          exact le_trans (Nat.sub_le _ _) h2
        · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]; exact h2
      · by_cases h : 2 ^ k.val ≤ pos.val - m.val
        · simp only [h, decide_true, ↓reduceIte]
          have hpow : 2 ^ (k.val + 1) = 2 ^ k.val + 2 ^ k.val := by rw [pow_succ]; omega
          omega
        · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]; omega
    have hgen : ∀ (n : ℕ) (hn : n ≤ p),
        ∃ pos : Fin (2 ^ p),
          ((((List.finRange p).reverse).take n).flatMap fun k =>
            [sweepLoadGuard p (rStr.2 k) wFalse wTrue,
             sweepSub p k.val wFalse wTrue,
             sweepClearGuard p wFalse wTrue]).foldl (fun s sw =>
              (List.finRange w).foldl (fun st t => shiftStep p st (eval (sw t st))) s)
              (stateOf p false u1) = stateOf p false pos ∧
          m.val ≤ pos.val ∧ pos.val ≤ u1.val ∧ pos.val - m.val < 2 ^ (p - n) := by
      intro n hn
      induction n with
      | zero =>
        refine ⟨u1, rfl, hm_le_u1, le_refl _, ?_⟩
        simp only [Nat.sub_zero]
        exact lt_of_le_of_lt (Nat.sub_le _ _) u1.isLt
      | succ n ih =>
        rcases ih (by omega) with ⟨pos, hpos, h1, h2, h3⟩
        have hlt_n : n < ((List.finRange p).reverse).length := by simp; omega
        rw [List.take_succ_eq_append_getElem hlt_n, List.flatMap_append, List.foldl_append,
          hpos, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        set k : Fin p := ((List.finRange p).reverse)[n]'hlt_n
        have hk_val : k.val = p - 1 - n := by
          simp [k, List.getElem_reverse]
        have hpow_eq : p - n = k.val + 1 := by omega
        rw [hpow_eq] at h3
        rcases hstep_k k pos h1 h2 h3 with ⟨pos', hpos', h1', h2', h3'⟩
        have hsub_eq : k.val = p - (n + 1) := by omega
        rw [hsub_eq] at h3'
        exact ⟨pos', hpos', h1', h2', h3'⟩
    rcases hgen p (le_refl p) with ⟨pos, hpos, h1, _, h3⟩
    rw [List.take_of_length_le (by simp)] at hpos
    have heq_m : pos = m := by
      ext; simp only [Nat.sub_self, pow_zero] at h3; omega
    rw [heq_m] at hpos
    exact hpos
  rw [hphase2]
  have hphase3 :
      revSweeps.foldl (fun s sw =>
        (List.finRange w).foldl (fun st t => shiftStep p st (eval (sw t st))) s)
        (stateOf p false m) =
      stateOf p false m0 := by
    have hgen : ∀ (k : ℕ) (hk : k ≤ sched.length),
        (revSweeps.take k).foldl (fun s sw =>
          (List.finRange w).foldl (fun st t => shiftStep p st (eval (sw t st))) s)
          (stateOf p false m) =
        stateOf p false ((perms.reverse.take k).foldl (fun x π => π x) m) := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih =>
        have hlt_r : k < revSweeps.length := by simp [revSweeps, hNet_len]; omega
        have hlt_p : k < perms.reverse.length := by simp [hperms_len]; omega
        rw [List.take_succ_eq_append_getElem hlt_r, List.foldl_append, List.foldl_cons, List.foldl_nil,
          ih (by omega)]
        rw [List.take_succ_eq_append_getElem hlt_p, List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [revSweeps, List.getElem_map, List.getElem_reverse]
        have hidx_eq : rNet.2.2.length - 1 - k = sched.length - 1 - k := by rw [hNet_len]
        have hidx_eq2 : perms.length - 1 - k = sched.length - 1 - k := by rw [hperms_len]
        have hlc_eq : rNet.2.2[rNet.2.2.length - 1 - k]'(by omega) =
            rNet.2.2[sched.length - 1 - k]'(by rw [hNet_len]; omega) := by congr 1
        have hperm_eq : perms[perms.length - 1 - k]'(by omega) =
            perms[sched.length - 1 - k]'(by rw [hperms_len]; omega) := by congr 1
        rw [hlc_eq, hperm_eq]
        exact hlayer_step (sched.length - 1 - k) (by omega)
          ((perms.reverse.take k).foldl (fun x π => π x) m)
    have hfull := hgen sched.length (le_refl _)
    rw [List.take_of_length_le (by simp [revSweeps, hNet_len]),
      List.take_of_length_le (by simp [hperms_len]), hperms_spec.1 m0] at hfull
    exact hfull
  rw [hphase3]
  simp only [tailSweeps, List.foldl_cons, List.foldl_nil]
  rw [runSweep_clearTag d wFalse wTrue eval hevalF hevalT (f v)]
  rw [runSweep_id p wFalse wTrue eval hevalF hevalT]
  rw [runSweep_id p wFalse wTrue eval hevalF hevalT]
  rw [runSweep_id p wFalse wTrue eval hevalF hevalT]

end PEqualNP.Outside.L_clb_073

theorem PEqualNP.Outside.L_clb_073 : (∀ d : ℕ,
  let p := d + 1
  let w := p + 1
  let rows := w * (p + 2)^2
  let I := 2^d * d
  let D := Fin d → Bool
  let State := Fin w → Bool
  let active := fun (v : D) => Fin.cons (α := fun _ : Fin w => Bool) false
    (Fin.cons (α := fun _ : Fin p => Bool) false v)
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
    (out : Fin rows → State → Fin (I + C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack I C ∧ C.output < I + C.size ∧
    C.size ≤ 128 * 2^p * (p+2)^3 ∧
    ∀ f : D → D,
      let inp := (List.ofFn (fun i : Fin (2^d) => List.ofFn
        (f (fun j => i.val.testBit (d - 1 - j.val))))).flatten
      ∀ v : D, (List.finRange rows).foldl (fun (s : State) row =>
        Fin.snoc (α := fun _ : Fin w => Bool) (fun j : Fin p => s j.succ)
          ((C.wires inp).getD (out row s).val false)) (active v) = active (f v)) := by
  exact PEqualNP.Outside.L_clb_073.main_proof
