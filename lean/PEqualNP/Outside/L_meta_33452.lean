import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33452_aux

open Finset Matrix PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

abbrev F2 := ZMod 2

def toF2 (b : Bool) : F2 := if b then 1 else 0

lemma toF2_false : toF2 false = 0 := rfl
lemma toF2_true : toF2 true = 1 := rfl

lemma toF2_xor (a b : Bool) : toF2 (xor a b) = toF2 a + toF2 b := by
  cases a <;> cases b <;> decide

lemma toF2_not (a : Bool) : toF2 (!a) = 1 + toF2 a := by
  cases a <;> decide

lemma toF2_and (a b : Bool) : toF2 (a && b) = toF2 a * toF2 b := by
  cases a <;> cases b <;> decide

lemma toF2_decide (x : F2) : toF2 (decide (x ≠ 0)) = x := by
  fin_cases x <;> rfl

lemma toF2_injective : Function.Injective toF2 := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

lemma f2_add_self (x : F2) : x + x = 0 := by fin_cases x <;> rfl
lemma f2_sub_eq_add (x y : F2) : x - y = x + y := by fin_cases x <;> fin_cases y <;> rfl
lemma f2_neg_eq (x : F2) : -x = x := by fin_cases x <;> rfl

def nonlinear (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depths (width : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)

def outerPair {d : ℕ} (u1 v1 u2 v2 : Fin d → F2) : Matrix (Fin d) (Fin d) F2 :=
  Matrix.of (fun i j => u1 i * v1 j + u2 i * v2 j)

def IsRankLe2 {d : ℕ} (M : Matrix (Fin d) (Fin d) F2) : Prop :=
  ∃ u1 v1 u2 v2 : Fin d → F2, M = outerPair u1 v1 u2 v2

def delta {d : ℕ} (f : Fin (d + 1) → Fin (d + 1) → F2) : Matrix (Fin d) (Fin d) F2 :=
  Matrix.of (fun i j => f i.succ j.succ + f i.succ 0 + f 0 j.succ + f 0 0)

def tableMat {d : ℕ} (H : Matrix (Fin d) (Fin d) F2) (x y : Fin (d + 1)) : Bool :=
  Fin.cases false (fun i => Fin.cases false (fun j => decide (H i j ≠ 0)) y) x

lemma delta_tableMat {d : ℕ} (H : Matrix (Fin d) (Fin d) F2) :
    delta (fun x y => toF2 (tableMat H x y)) = H := by
  ext i j
  simp only [delta, Matrix.of_apply, tableMat, Fin.cases_succ, Fin.cases_zero, toF2_false, add_zero, toF2_decide]

lemma delta_const {d : ℕ} (c : F2) : delta (fun _ _ : Fin (d + 1) => c) = 0 := by
  ext i j
  simp only [delta, Matrix.of_apply, Matrix.zero_apply]
  have h := f2_add_self c
  calc c + c + c + c = (c + c) + (c + c) := by ring
    _ = 0 := by rw [h, add_zero]

lemma delta_add {d : ℕ} (f g : Fin (d + 1) → Fin (d + 1) → F2) :
    delta (fun x y => f x y + g x y) = delta f + delta g := by
  ext i j
  simp only [delta, Matrix.of_apply, Matrix.add_apply]
  ring

lemma delta_smul {d : ℕ} (c : F2) (f : Fin (d + 1) → Fin (d + 1) → F2) :
    delta (fun x y => c * f x y) = c • delta f := by
  ext i j
  simp only [delta, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  ring

lemma delta_sep {d : ℕ} (a b : Fin (d + 1) → F2) :
    delta (fun x y => a x + b y) = 0 := by
  ext i j
  simp only [delta, Matrix.of_apply, Matrix.zero_apply]
  have ha1 := f2_add_self (a i.succ)
  have ha0 := f2_add_self (a 0)
  have hb1 := f2_add_self (b j.succ)
  have hb0 := f2_add_self (b 0)
  calc a i.succ + b j.succ + (a i.succ + b 0) + (a 0 + b j.succ) + (a 0 + b 0)
      = (a i.succ + a i.succ) + (a 0 + a 0) + (b j.succ + b j.succ) + (b 0 + b 0) := by ring
    _ = 0 := by rw [ha1, ha0, hb1, hb0]; simp

lemma delta_mul_sep {d : ℕ} (a1 b1 a2 b2 : Fin (d + 1) → F2) :
    IsRankLe2 (delta (fun x y => (a1 x + b1 y) * (a2 x + b2 y))) := by
  refine ⟨fun i => a1 i.succ + a1 0, fun j => b2 j.succ + b2 0,
    fun i => a2 i.succ + a2 0, fun j => b1 j.succ + b1 0, ?_⟩
  ext i j
  simp only [delta, outerPair, Matrix.of_apply]
  have h1 := f2_add_self (a1 i.succ * a2 i.succ)
  have h2 := f2_add_self (a1 0 * a2 0)
  have h3 := f2_add_self (b1 j.succ * b2 j.succ)
  have h4 := f2_add_self (b1 0 * b2 0)
  calc (a1 i.succ + b1 j.succ) * (a2 i.succ + b2 j.succ) +
        (a1 i.succ + b1 0) * (a2 i.succ + b2 0) +
        (a1 0 + b1 j.succ) * (a2 0 + b2 j.succ) +
        (a1 0 + b1 0) * (a2 0 + b2 0)
      = (a1 i.succ * a2 i.succ + a1 i.succ * a2 i.succ) +
        (a1 0 * a2 0 + a1 0 * a2 0) +
        (b1 j.succ * b2 j.succ + b1 j.succ * b2 j.succ) +
        (b1 0 * b2 0 + b1 0 * b2 0) +
        ((a1 i.succ + a1 0) * (b2 j.succ + b2 0) + (a2 i.succ + a2 0) * (b1 j.succ + b1 0)) := by ring
    _ = (a1 i.succ + a1 0) * (b2 j.succ + b2 0) + (a2 i.succ + a2 0) * (b1 j.succ + b1 0) := by
        rw [h1, h2, h3, h4]; ring

section CircuitToRank2

lemma eval_poly_len1 (op : GateOp) :
    ∃ c0 c1 : F2, ∀ a : Bool, toF2 (op.eval [a]) = c0 + c1 * toF2 a := by
  refine ⟨toF2 (op.eval [false]), toF2 (op.eval [false]) + toF2 (op.eval [true]), fun a => ?_⟩
  cases a
  · simp [toF2_false]
  · simp [toF2_true]
    rw [← add_assoc, f2_add_self, zero_add]

lemma eval_poly_len2 (op : GateOp) :
    let e00 := toF2 (op.eval [false, false])
    let e01 := toF2 (op.eval [false, true])
    let e10 := toF2 (op.eval [true, false])
    let e11 := toF2 (op.eval [true, true])
    ∀ a b : Bool,
      toF2 (op.eval [a, b]) = e00 + (e00 + e10) * toF2 a + (e00 + e01) * toF2 b +
        (e00 + e01 + e10 + e11) * toF2 a * toF2 b := by
  intro e00 e01 e10 e11 a b
  cases a <;> cases b <;> dsimp only [e00, e01, e10, e11] <;> simp only [toF2_false, toF2_true]
  · ring
  · have h := f2_add_self (toF2 (op.eval [false, false]))
    calc toF2 (op.eval [false, true])
        = (toF2 (op.eval [false, false]) + toF2 (op.eval [false, false])) +
          toF2 (op.eval [false, true]) := by rw [h, zero_add]
      _ = _ := by ring
  · have h := f2_add_self (toF2 (op.eval [false, false]))
    calc toF2 (op.eval [true, false])
        = (toF2 (op.eval [false, false]) + toF2 (op.eval [false, false])) +
          toF2 (op.eval [true, false]) := by rw [h, zero_add]
      _ = _ := by ring
  · have h0 := f2_add_self (toF2 (op.eval [false, false]))
    have h1 := f2_add_self (toF2 (op.eval [false, true]))
    have h2 := f2_add_self (toF2 (op.eval [true, false]))
    calc toF2 (op.eval [true, true])
        = (toF2 (op.eval [false, false]) + toF2 (op.eval [false, false])) +
          (toF2 (op.eval [false, false]) + toF2 (op.eval [false, false])) +
          (toF2 (op.eval [false, true]) + toF2 (op.eval [false, true])) +
          (toF2 (op.eval [true, false]) + toF2 (op.eval [true, false])) +
          toF2 (op.eval [true, true]) := by rw [h0, h1, h2]; simp
      _ = _ := by ring

lemma depths_length (width : ℕ) (gs : List Gate) :
    (depths width gs).length = width + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [depths]
  | append_singleton gs g ih =>
    simp only [depths, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton]
    change (depths width gs).length + 1 = width + (gs.length + 1)
    rw [ih]; omega

lemma depths_append_singleton (width : ℕ) (gs : List Gate) (g : Gate) :
    depths width (gs ++ [g]) =
      depths width gs ++ [(g.inputs.map (fun a => (depths width gs).getD a 0)).foldr max 0 +
        (nonlinear g).toNat] := by
  simp [depths, List.foldl_append]

lemma wires_length (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton]
    change (Circuit.wires ⟨gs, 0⟩ x).length + 1 = x.length + (gs.length + 1)
    rw [ih]; omega

lemma wires_append_singleton (gs : List Gate) (g : Gate) (x : List Bool) :
    Circuit.wires ⟨gs ++ [g], 0⟩ x =
      Circuit.wires ⟨gs, 0⟩ x ++
        [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

lemma oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

lemma oneEach_getD {d : ℕ} (w : ℕ) :
    ∃ a b : Fin (d + 1) → F2, ∀ x y : Fin (d + 1),
      toF2 ((oneEach x y).getD w false) = a x + b y := by
  by_cases h1 : w < d + 1
  · refine ⟨fun x => toF2 (decide (w = x.val)), fun _ => 0, fun x y => ?_⟩
    dsimp only [oneEach]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
      List.getElem?_ofFn, dif_pos h1, Option.getD_some, add_zero]
    congr 1
  · by_cases h2 : w < (d + 1) + (d + 1)
    · refine ⟨fun _ => 0, fun y => toF2 (decide (w - (d + 1) = y.val)), fun x y => ?_⟩
      dsimp only [oneEach]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp; omega),
        List.length_ofFn, List.getElem?_ofFn, dif_pos (by omega : w - (d + 1) < d + 1),
        Option.getD_some, zero_add]
      congr 1
    · refine ⟨fun _ => 0, fun _ => 0, fun x y => ?_⟩
      have hge : (oneEach x y).length ≤ w := by rw [oneEach_length]; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, toF2_false]

lemma circuit_to_rank2_span {d : ℕ} (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ Ms : List (Matrix (Fin d) (Fin d) F2),
      Ms.length ≤ gs.countP nonlinear ∧
      (∀ M ∈ Ms, IsRankLe2 M) ∧
      ∀ w : ℕ,
        ((depths ((d + 1) + (d + 1)) gs).getD w 0 = 0 →
          ∃ a b : Fin (d + 1) → F2, ∀ x y : Fin (d + 1),
            toF2 ((Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD w false) = a x + b y) ∧
        ((depths ((d + 1) + (d + 1)) gs).getD w 0 ≤ 1 →
          delta (fun x y => toF2 ((Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD w false)) ∈
            Submodule.span F2 {M | M ∈ Ms}) := by
  let width := (d + 1) + (d + 1)
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], le_rfl, fun _ h => absurd h List.not_mem_nil, fun w => ?_⟩
    have hsep := oneEach_getD (d := d) w
    refine ⟨fun _ => hsep, fun _ => ?_⟩
    obtain ⟨a, b, hab⟩ := hsep
    have h0 : delta (fun (x y : Fin (d + 1)) => toF2 ((Circuit.wires ⟨[], 0⟩ (oneEach x y)).getD w false)) = 0 := by
      have : (fun x y : Fin (d + 1) => toF2 ((Circuit.wires ⟨[], 0⟩ (oneEach x y)).getD w false)) =
          fun x y => a x + b y := by funext x y; exact hab x y
      rw [this, delta_sep]
    rw [h0]
    exact Submodule.zero_mem _
  | append_singleton gs g ih =>
    have hfan_gs : ∀ g' ∈ gs, g'.inputs.length ≤ 2 := fun g' hg' => hfan g' (by simp [hg'])
    have hfan_g : g.inputs.length ≤ 2 := hfan g (by simp)
    obtain ⟨Ms, hMs_len, hMs_rk, hIH⟩ := ih hfan_gs
    let dNew : ℕ := (g.inputs.map (fun a => (depths width gs).getD a 0)).foldr max 0 +
      (nonlinear g).toNat
    have hlen_d : (depths width gs).length = width + gs.length := depths_length width gs
    have hlen_w : ∀ x y : Fin (d + 1), (Circuit.wires ⟨gs, 0⟩ (oneEach x y)).length = width + gs.length :=
      fun x y => by rw [wires_length, oneEach_length]
    have hold_d : ∀ w < width + gs.length,
        (depths width (gs ++ [g])).getD w 0 = (depths width gs).getD w 0 := by
      intro w hw
      rw [depths_append_singleton, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega)]
    have hold_w : ∀ w < width + gs.length, ∀ x y : Fin (d + 1),
        (Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).getD w false =
          (Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD w false := by
      intro w hw x y
      rw [wires_append_singleton, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [hlen_w x y]; omega)]
    have hnew_d : (depths width (gs ++ [g])).getD (width + gs.length) 0 = dNew := by
      rw [depths_append_singleton, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega), hlen_d, Nat.sub_self]
      rfl
    have hnew_w : ∀ x y : Fin (d + 1),
        (Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).getD (width + gs.length) false =
          g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD i false) := by
      intro x y
      rw [wires_append_singleton, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by rw [hlen_w x y]), hlen_w x y, Nat.sub_self]
      rfl
    have hgt_w : ∀ w > width + gs.length, ∀ x y : Fin (d + 1),
        (Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).getD w false = false := by
      intro w hw x y
      have hge : (Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).length ≤ w := by
        rw [wires_length, oneEach_length, List.length_append, List.length_singleton]; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
    have hcnt_app : (gs ++ [g]).countP nonlinear = gs.countP nonlinear + (nonlinear g).toNat := by
      rw [List.countP_append, List.countP_cons, List.countP_nil]
      cases nonlinear g <;> simp
    by_cases hnl : nonlinear g = true
    · by_cases hd1 : dNew ≤ 1
      · have hlen2 : g.inputs.length = 2 := by
          simp only [nonlinear, Bool.and_eq_true, beq_iff_eq] at hnl
          exact hnl.1
        obtain ⟨i1, i2, hgin⟩ : ∃ i1 i2, g.inputs = [i1, i2] := by
          cases h1 : g.inputs with
          | nil => simp [h1] at hlen2
          | cons a rest =>
            cases rest with
            | nil => simp [h1] at hlen2
            | cons b rest2 =>
              cases rest2 with
              | nil => exact ⟨a, b, rfl⟩
              | cons _ _ => simp [h1] at hlen2
        have hi1_d : (depths width gs).getD i1 0 = 0 := by
          dsimp only [dNew] at hd1
          rw [hgin, hnl] at hd1
          simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_true] at hd1
          omega
        have hi2_d : (depths width gs).getD i2 0 = 0 := by
          dsimp only [dNew] at hd1
          rw [hgin, hnl] at hd1
          simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_true] at hd1
          omega
        obtain ⟨a1, b1, h1⟩ := (hIH i1).1 hi1_d
        obtain ⟨a2, b2, h2⟩ := (hIH i2).1 hi2_d
        let Mnew : Matrix (Fin d) (Fin d) F2 :=
          delta (fun x y => toF2 ((Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).getD (width + gs.length) false))
        have hMnew_rk : IsRankLe2 Mnew := by
          have hpoly := eval_poly_len2 g.op
          dsimp only at hpoly
          have hquad1 : toF2 (g.op.eval [false, false]) + toF2 (g.op.eval [false, true]) +
              toF2 (g.op.eval [true, false]) + toF2 (g.op.eval [true, true]) = 1 := by
            simp only [nonlinear, hgin, List.length_cons, List.length_nil, beq_self_eq_true,
              Bool.true_and] at hnl
            have := congrArg toF2 hnl
            simp only [toF2_xor, toF2_true] at this
            simpa [add_assoc] using this
          have hfun : (fun x y : Fin (d + 1) =>
              toF2 ((Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).getD (width + gs.length) false)) =
              fun x y => toF2 (g.op.eval [false, false]) +
                (toF2 (g.op.eval [false, false]) + toF2 (g.op.eval [true, false])) * (a1 x + b1 y) +
                (toF2 (g.op.eval [false, false]) + toF2 (g.op.eval [false, true])) * (a2 x + b2 y) +
                (a1 x + b1 y) * (a2 x + b2 y) := by
            funext x y
            rw [hnew_w x y, hgin]
            simp only [List.map_cons, List.map_nil]
            rw [hpoly, hquad1, one_mul, h1 x y, h2 x y]
          have hdel : Mnew = delta (fun x y => (a1 x + b1 y) * (a2 x + b2 y)) := by
            dsimp only [Mnew]
            rw [hfun, delta_add, delta_add, delta_add, delta_const, delta_smul, delta_smul,
              delta_sep, delta_sep]
            simp
          rw [hdel]
          exact delta_mul_sep a1 b1 a2 b2
        refine ⟨Mnew :: Ms, by rw [List.length_cons, hcnt_app, hnl]; simp; omega,
          fun M hM => by rcases List.mem_cons.1 hM with rfl | hM'; exact hMnew_rk; exact hMs_rk M hM',
          fun w => ?_⟩
        by_cases hlt : w < width + gs.length
        · have hsub : Submodule.span F2 {M | M ∈ Ms} ≤ Submodule.span F2 {M | M ∈ Mnew :: Ms} :=
            Submodule.span_mono fun M hM => List.mem_cons_of_mem Mnew hM
          refine ⟨fun hd0 => ?_, fun hdle => ?_⟩
          · rw [hold_d w hlt] at hd0
            obtain ⟨a, b, hab⟩ := (hIH w).1 hd0
            exact ⟨a, b, fun x y => by rw [hold_w w hlt]; exact hab x y⟩
          · rw [hold_d w hlt] at hdle
            have hmem := hsub ((hIH w).2 hdle)
            convert hmem using 2
            funext x y
            rw [hold_w w hlt]
        · by_cases heq : w = width + gs.length
          · subst heq
            refine ⟨fun hd0 => by rw [hnew_d] at hd0; dsimp only [dNew] at hd0; rw [hnl] at hd0; simp at hd0,
              fun _ => Submodule.subset_span List.mem_cons_self⟩
          · have hgt : w > width + gs.length := by omega
            refine ⟨fun _ => ⟨fun _ => 0, fun _ => 0, fun x y => by rw [hgt_w w hgt, toF2_false, add_zero]⟩,
              fun _ => ?_⟩
            have h0 : delta (fun (x y : Fin (d + 1)) => toF2 ((Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).getD w false)) = 0 := by
              have : (fun x y : Fin (d + 1) =>
                  toF2 ((Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).getD w false)) = fun _ _ => 0 := by
                funext x y; rw [hgt_w w hgt, toF2_false]
              rw [this, delta_const]
            rw [h0]
            exact Submodule.zero_mem _
      · refine ⟨Ms, by rw [hcnt_app, hnl]; simp; omega, hMs_rk, fun w => ?_⟩
        by_cases hlt : w < width + gs.length
        · refine ⟨fun hd0 => ?_, fun hdle => ?_⟩
          · rw [hold_d w hlt] at hd0
            obtain ⟨a, b, hab⟩ := (hIH w).1 hd0
            exact ⟨a, b, fun x y => by rw [hold_w w hlt]; exact hab x y⟩
          · rw [hold_d w hlt] at hdle
            have hmem := (hIH w).2 hdle
            convert hmem using 2
            funext x y
            rw [hold_w w hlt]
        · by_cases heq : w = width + gs.length
          · subst heq
            refine ⟨fun hd0 => by rw [hnew_d] at hd0; omega,
              fun hdle => by rw [hnew_d] at hdle; omega⟩
          · have hgt : w > width + gs.length := by omega
            refine ⟨fun _ => ⟨fun _ => 0, fun _ => 0, fun x y => by rw [hgt_w w hgt, toF2_false, add_zero]⟩,
              fun _ => ?_⟩
            have h0 : delta (fun (x y : Fin (d + 1)) => toF2 ((Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).getD w false)) = 0 := by
              have : (fun x y : Fin (d + 1) =>
                  toF2 ((Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).getD w false)) = fun _ _ => 0 := by
                funext x y; rw [hgt_w w hgt, toF2_false]
              rw [this, delta_const]
            rw [h0]
            exact Submodule.zero_mem _
    · have hnlF : nonlinear g = false := Bool.eq_false_iff.2 hnl
      refine ⟨Ms, by rw [hcnt_app, hnlF]; simp; exact hMs_len, hMs_rk, fun w => ?_⟩
      by_cases hlt : w < width + gs.length
      · refine ⟨fun hd0 => ?_, fun hdle => ?_⟩
        · rw [hold_d w hlt] at hd0
          obtain ⟨a, b, hab⟩ := (hIH w).1 hd0
          exact ⟨a, b, fun x y => by rw [hold_w w hlt]; exact hab x y⟩
        · rw [hold_d w hlt] at hdle
          have hmem := (hIH w).2 hdle
          convert hmem using 2
          funext x y
          rw [hold_w w hlt]
      · by_cases heq : w = width + gs.length
        · subst heq
          have hlin_form : ∀ (hd : dNew ≤ 1),
              (dNew = 0 → ∃ a b : Fin (d + 1) → F2, ∀ x y : Fin (d + 1),
                toF2 ((Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).getD (width + gs.length) false) = a x + b y) ∧
              delta (fun x y => toF2 ((Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).getD (width + gs.length) false)) ∈
                Submodule.span F2 {M | M ∈ Ms} := by
            intro hd1
            cases hgin : g.inputs with
            | nil =>
              have hconst : ∀ x y : Fin (d + 1),
                  toF2 ((Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).getD (width + gs.length) false) =
                    toF2 (g.op.eval []) := fun x y => by rw [hnew_w x y, hgin]; rfl
              refine ⟨fun _ => ⟨fun _ => toF2 (g.op.eval []), fun _ => 0, fun x y => by rw [hconst x y, add_zero]⟩, ?_⟩
              have h0 : delta (fun (x y : Fin (d + 1)) => toF2 ((Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).getD (width + gs.length) false)) = 0 := by
                have : (fun x y : Fin (d + 1) =>
                    toF2 ((Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).getD (width + gs.length) false)) =
                    fun _ _ => toF2 (g.op.eval []) := by funext x y; exact hconst x y
                rw [this, delta_const]
              rw [h0]
              exact Submodule.zero_mem _
            | cons i1 rest =>
              cases rest with
              | nil =>
                obtain ⟨c0, c1, hc⟩ := eval_poly_len1 g.op
                have hi1_le : (depths width gs).getD i1 0 ≤ 1 := by
                  dsimp only [dNew] at hd1; rw [hgin, hnlF] at hd1
                  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_false, add_zero] at hd1
                  omega
                have hfun : ∀ x y : Fin (d + 1),
                    toF2 ((Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).getD (width + gs.length) false) =
                      c0 + c1 * toF2 ((Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD i1 false) := fun x y => by
                  rw [hnew_w x y, hgin]; simp only [List.map_cons, List.map_nil]; exact hc _
                refine ⟨fun hd0 => ?_, ?_⟩
                · have hi1_0 : (depths width gs).getD i1 0 = 0 := by
                    dsimp only [dNew] at hd0; rw [hgin, hnlF] at hd0
                    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_false, add_zero] at hd0
                    omega
                  obtain ⟨a1, b1, h1⟩ := (hIH i1).1 hi1_0
                  refine ⟨fun x => c0 + c1 * a1 x, fun y => c1 * b1 y, fun x y => ?_⟩
                  rw [hfun x y, h1 x y]; ring
                · have : (fun x y : Fin (d + 1) =>
                      toF2 ((Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).getD (width + gs.length) false)) =
                      fun x y => c0 + c1 * toF2 ((Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD i1 false) := by
                    funext x y; exact hfun x y
                  rw [this, delta_add, delta_const, zero_add, delta_smul]
                  exact Submodule.smul_mem _ c1 ((hIH i1).2 hi1_le)
              | cons i2 rest2 =>
                cases rest2 with
                | cons _ _ => rw [hgin] at hfan_g; simp at hfan_g
                | nil =>
                  have hpoly := eval_poly_len2 g.op
                  dsimp only at hpoly
                  have hquad0 : toF2 (g.op.eval [false, false]) + toF2 (g.op.eval [false, true]) +
                      toF2 (g.op.eval [true, false]) + toF2 (g.op.eval [true, true]) = 0 := by
                    simp only [nonlinear, hgin, List.length_cons, List.length_nil, beq_self_eq_true,
                      Bool.true_and] at hnlF
                    have := congrArg toF2 hnlF
                    simp only [toF2_xor, toF2_false] at this
                    simpa [add_assoc] using this
                  have hi1_le : (depths width gs).getD i1 0 ≤ 1 := by
                    dsimp only [dNew] at hd1; rw [hgin, hnlF] at hd1
                    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_false, add_zero] at hd1
                    omega
                  have hi2_le : (depths width gs).getD i2 0 ≤ 1 := by
                    dsimp only [dNew] at hd1; rw [hgin, hnlF] at hd1
                    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_false, add_zero] at hd1
                    omega
                  let c0 := toF2 (g.op.eval [false, false])
                  let c1 := toF2 (g.op.eval [false, false]) + toF2 (g.op.eval [true, false])
                  let c2 := toF2 (g.op.eval [false, false]) + toF2 (g.op.eval [false, true])
                  have hfun : ∀ x y : Fin (d + 1),
                      toF2 ((Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).getD (width + gs.length) false) =
                        c0 + c1 * toF2 ((Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD i1 false) +
                          c2 * toF2 ((Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD i2 false) := fun x y => by
                    rw [hnew_w x y, hgin]; simp only [List.map_cons, List.map_nil]
                    rw [hpoly, hquad0, zero_mul, zero_mul, add_zero]
                  refine ⟨fun hd0 => ?_, ?_⟩
                  · have hi1_0 : (depths width gs).getD i1 0 = 0 := by
                      dsimp only [dNew] at hd0; rw [hgin, hnlF] at hd0
                      simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_false, add_zero] at hd0
                      omega
                    have hi2_0 : (depths width gs).getD i2 0 = 0 := by
                      dsimp only [dNew] at hd0; rw [hgin, hnlF] at hd0
                      simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_false, add_zero] at hd0
                      omega
                    obtain ⟨a1, b1, h1⟩ := (hIH i1).1 hi1_0
                    obtain ⟨a2, b2, h2⟩ := (hIH i2).1 hi2_0
                    refine ⟨fun x => c0 + c1 * a1 x + c2 * a2 x, fun y => c1 * b1 y + c2 * b2 y, fun x y => ?_⟩
                    rw [hfun x y, h1 x y, h2 x y]; ring
                  · have : (fun x y : Fin (d + 1) =>
                        toF2 ((Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).getD (width + gs.length) false)) =
                        fun x y => c0 + c1 * toF2 ((Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD i1 false) +
                          c2 * toF2 ((Circuit.wires ⟨gs, 0⟩ (oneEach x y)).getD i2 false) := by
                      funext x y; exact hfun x y
                    rw [this, delta_add, delta_add, delta_const, zero_add, delta_smul, delta_smul]
                    exact Submodule.add_mem _ (Submodule.smul_mem _ c1 ((hIH i1).2 hi1_le))
                      (Submodule.smul_mem _ c2 ((hIH i2).2 hi2_le))
          refine ⟨fun hd0 => ?_, fun hd1 => ?_⟩
          · rw [hnew_d] at hd0
            exact (hlin_form (by omega)).1 hd0
          · rw [hnew_d] at hd1
            exact (hlin_form hd1).2
        · have hgt : w > width + gs.length := by omega
          refine ⟨fun _ => ⟨fun _ => 0, fun _ => 0, fun x y => by rw [hgt_w w hgt, toF2_false, add_zero]⟩,
            fun _ => ?_⟩
          have h0 : delta (fun (x y : Fin (d + 1)) => toF2 ((Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).getD w false)) = 0 := by
            have : (fun x y : Fin (d + 1) =>
                toF2 ((Circuit.wires ⟨gs ++ [g], 0⟩ (oneEach x y)).getD w false)) = fun _ _ => 0 := by
              funext x y; rw [hgt_w w hgt, toF2_false]
            rw [this, delta_const]
          rw [h0]
          exact Submodule.zero_mem _

end CircuitToRank2

section Rank2ToCircuit

structure CircBuild (d : ℕ) where
  gates : List Gate
  rb : ReadsBack ((d + 1) + (d + 1)) ⟨gates, 0⟩
  fan : ∀ g ∈ gates, g.inputs.length ≤ 2

def CircBuild.addGate {d : ℕ} (st : CircBuild d) (g : Gate)
    (hfan : g.inputs.length ≤ 2)
    (hrb : ∀ i ∈ g.inputs, i < ((d + 1) + (d + 1)) + st.gates.length) :
    CircBuild d × ℕ :=
  let w := ((d + 1) + (d + 1)) + st.gates.length
  let st' : CircBuild d :=
    { gates := st.gates ++ [g]
      rb := by
        intro j hj i hi
        rw [List.length_append, List.length_singleton] at hj
        by_cases hlt : j < st.gates.length
        · have hg : gateAt ⟨st.gates ++ [g], 0⟩ j = gateAt ⟨st.gates, 0⟩ j := by
            simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
          rw [hg] at hi
          exact st.rb j hlt i hi
        · have heq : j = st.gates.length := by omega
          subst heq
          have hg : gateAt ⟨st.gates ++ [g], 0⟩ st.gates.length = g := by
            simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
          rw [hg] at hi
          exact hrb i hi
      fan := fun g' hg' => by
        rcases List.mem_append.1 hg' with h | h
        · exact st.fan g' h
        · rw [List.mem_singleton.1 h]; exact hfan }
  (st', w)

lemma addGate_old_wire {d : ℕ} (st : CircBuild d) (g : Gate) (hfan hrb)
    {w : ℕ} (hw : w < ((d + 1) + (d + 1)) + st.gates.length) (x y : Fin (d + 1)) :
    (Circuit.wires ⟨(st.addGate g hfan hrb).1.gates, 0⟩ (oneEach x y)).getD w false =
      (Circuit.wires ⟨st.gates, 0⟩ (oneEach x y)).getD w false := by
  dsimp only [CircBuild.addGate]
  rw [wires_append_singleton, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [wires_length, oneEach_length]; omega)]

lemma addGate_old_depth {d : ℕ} (st : CircBuild d) (g : Gate) (hfan hrb)
    {w : ℕ} (hw : w < ((d + 1) + (d + 1)) + st.gates.length) :
    (depths ((d + 1) + (d + 1)) (st.addGate g hfan hrb).1.gates).getD w 0 =
      (depths ((d + 1) + (d + 1)) st.gates).getD w 0 := by
  dsimp only [CircBuild.addGate]
  rw [depths_append_singleton, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [depths_length]; omega)]

lemma addGate_new_wire {d : ℕ} (st : CircBuild d) (g : Gate) (hfan hrb) (x y : Fin (d + 1)) :
    (Circuit.wires ⟨(st.addGate g hfan hrb).1.gates, 0⟩ (oneEach x y)).getD
        (st.addGate g hfan hrb).2 false =
      g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨st.gates, 0⟩ (oneEach x y)).getD i false) := by
  dsimp only [CircBuild.addGate]
  rw [wires_append_singleton, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [wires_length, oneEach_length]),
    wires_length, oneEach_length, Nat.sub_self]
  rfl

lemma addGate_new_depth {d : ℕ} (st : CircBuild d) (g : Gate) (hfan hrb) :
    (depths ((d + 1) + (d + 1)) (st.addGate g hfan hrb).1.gates).getD
        (st.addGate g hfan hrb).2 0 =
      (g.inputs.map (fun a => (depths ((d + 1) + (d + 1)) st.gates).getD a 0)).foldr max 0 +
        (nonlinear g).toNat := by
  dsimp only [CircBuild.addGate]
  rw [depths_append_singleton, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [depths_length]),
    depths_length, Nat.sub_self]
  rfl

lemma addGate_countP {d : ℕ} (st : CircBuild d) (g : Gate) (hfan hrb) :
    (st.addGate g hfan hrb).1.gates.countP nonlinear =
      st.gates.countP nonlinear + (nonlinear g).toNat := by
  dsimp only [CircBuild.addGate]
  rw [List.countP_append, List.countP_cons, List.countP_nil]
  cases nonlinear g <;> simp

def CircBuild.addZero {d : ℕ} (st : CircBuild d) : CircBuild d × ℕ :=
  st.addGate ⟨GateOp.or, []⟩ (by simp) (by simp)

def CircBuild.addXor {d : ℕ} (st : CircBuild d) (a b : ℕ)
    (ha : a < ((d + 1) + (d + 1)) + st.gates.length)
    (hb : b < ((d + 1) + (d + 1)) + st.gates.length) : CircBuild d × ℕ :=
  let r1 := st.addGate ⟨GateOp.mod 2, [a, b]⟩ (by simp) (by simp [ha, hb])
  let hw1 : r1.2 < ((d + 1) + (d + 1)) + r1.1.gates.length := by
    simp [r1, CircBuild.addGate]
  r1.1.addGate ⟨GateOp.not, [r1.2]⟩ (by simp) (by simp [hw1])

def CircBuild.addAnd {d : ℕ} (st : CircBuild d) (a b : ℕ)
    (ha : a < ((d + 1) + (d + 1)) + st.gates.length)
    (hb : b < ((d + 1) + (d + 1)) + st.gates.length) : CircBuild d × ℕ :=
  st.addGate ⟨GateOp.and, [a, b]⟩ (by simp) (by simp [ha, hb])

lemma nonlinear_or_nil : nonlinear ⟨GateOp.or, []⟩ = false := by decide
lemma nonlinear_mod2 (a b : ℕ) : nonlinear ⟨GateOp.mod 2, [a, b]⟩ = false := by
  simp [nonlinear, GateOp.eval]
lemma nonlinear_not1 (a : ℕ) : nonlinear ⟨GateOp.not, [a]⟩ = false := by
  simp [nonlinear]
lemma nonlinear_and2 (a b : ℕ) : nonlinear ⟨GateOp.and, [a, b]⟩ = true := by
  simp [nonlinear, GateOp.eval]

lemma circBuild_prefix_preserve {d : ℕ} (gs1 gs2 : List Gate)
    {w : ℕ} (hw : w < ((d + 1) + (d + 1)) + gs1.length) :
    (∀ x y : Fin (d + 1),
      (Circuit.wires ⟨gs1 ++ gs2, 0⟩ (oneEach x y)).getD w false =
        (Circuit.wires ⟨gs1, 0⟩ (oneEach x y)).getD w false) ∧
    (depths ((d + 1) + (d + 1)) (gs1 ++ gs2)).getD w 0 =
      (depths ((d + 1) + (d + 1)) gs1).getD w 0 := by
  induction gs2 using List.reverseRecOn with
  | nil => simp
  | append_singleton gs2 g ih =>
    have hw2 : w < ((d + 1) + (d + 1)) + (gs1 ++ gs2).length := by
      rw [List.length_append]; omega
    constructor
    · intro x y
      rw [← List.append_assoc, wires_append_singleton, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [wires_length, oneEach_length]; omega),
        ← List.getD_eq_getElem?_getD]
      exact ih.1 x y
    · rw [← List.append_assoc, depths_append_singleton, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [depths_length]; omega),
        ← List.getD_eq_getElem?_getD]
      exact ih.2

lemma build_xor_list {d : ℕ} (st : CircBuild d) (ws : List ℕ)
    (hws : ∀ w ∈ ws, w < ((d + 1) + (d + 1)) + st.gates.length) (k : ℕ)
    (hd : ∀ w ∈ ws, (depths ((d + 1) + (d + 1)) st.gates).getD w 0 ≤ k) :
    ∃ (st' : CircBuild d) (wOut : ℕ),
      (∃ ext, st'.gates = st.gates ++ ext) ∧
      wOut < ((d + 1) + (d + 1)) + st'.gates.length ∧
      st'.gates.countP nonlinear = st.gates.countP nonlinear ∧
      (depths ((d + 1) + (d + 1)) st'.gates).getD wOut 0 ≤ k ∧
      ∀ x y : Fin (d + 1),
        toF2 ((Circuit.wires ⟨st'.gates, 0⟩ (oneEach x y)).getD wOut false) =
          (ws.map fun w => toF2 ((Circuit.wires ⟨st.gates, 0⟩ (oneEach x y)).getD w false)).sum := by
  induction ws with
  | nil =>
    refine ⟨st.addZero.1, st.addZero.2, ⟨[⟨GateOp.or, []⟩], rfl⟩, ?_, ?_, ?_, fun x y => ?_⟩
    · dsimp only [CircBuild.addZero, CircBuild.addGate]; rw [List.length_append, List.length_singleton]; omega
    · dsimp only [CircBuild.addZero]; rw [addGate_countP, nonlinear_or_nil]; simp
    · dsimp only [CircBuild.addZero]; rw [addGate_new_depth, nonlinear_or_nil]; simp
    · dsimp only [CircBuild.addZero]; rw [addGate_new_wire]; simp [GateOp.eval, toF2_false]
  | cons w ws ih =>
    have hws' : ∀ u ∈ ws, u < ((d + 1) + (d + 1)) + st.gates.length :=
      fun u hu => hws u (List.mem_cons_of_mem w hu)
    have hd' : ∀ u ∈ ws, (depths ((d + 1) + (d + 1)) st.gates).getD u 0 ≤ k :=
      fun u hu => hd u (List.mem_cons_of_mem w hu)
    obtain ⟨st1, w1, ⟨ext1, hext1⟩, hw1_lt, hcnt1, hd1, hval1⟩ := ih hws' hd'
    have hw_lt0 : w < ((d + 1) + (d + 1)) + st.gates.length := hws w List.mem_cons_self
    have hw_lt1 : w < ((d + 1) + (d + 1)) + st1.gates.length := by
      rw [hext1, List.length_append]; omega
    have hpre1 := circBuild_prefix_preserve st.gates ext1 hw_lt0
    rw [← hext1] at hpre1
    set r2 := st1.addXor w w1 hw_lt1 hw1_lt
    refine ⟨r2.1, r2.2,
      ⟨ext1 ++ [⟨GateOp.mod 2, [w, w1]⟩, ⟨GateOp.not, [((d + 1) + (d + 1)) + st1.gates.length]⟩], by
        dsimp only [r2, CircBuild.addXor, CircBuild.addGate]
        rw [hext1]; simp [List.append_assoc]⟩,
      ?_, ?_, ?_, fun x y => ?_⟩
    · dsimp only [r2, CircBuild.addXor, CircBuild.addGate]
      simp only [List.length_append, List.length_singleton]; omega
    · dsimp only [r2, CircBuild.addXor]
      rw [addGate_countP, addGate_countP, nonlinear_not1, nonlinear_mod2]
      simpa using hcnt1
    · dsimp only [r2, CircBuild.addXor]
      rw [addGate_new_depth, nonlinear_not1]
      simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_false, add_zero]
      rw [addGate_new_depth, nonlinear_mod2]
      simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_false, add_zero]
      have hdw : (depths ((d + 1) + (d + 1)) st1.gates).getD w 0 ≤ k := by
        rw [hpre1.2]; exact hd w List.mem_cons_self
      omega
    · dsimp only [r2, CircBuild.addXor]
      rw [addGate_new_wire]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
      rw [addGate_new_wire]
      simp only [List.map_cons, List.map_nil, GateOp.eval]
      have hmod2 : ∀ a b : Bool,
          toF2 (!decide ([a, b].count true % 2 = 0)) = toF2 a + toF2 b := by
        intro a b; cases a <;> cases b <;> decide
      rw [hmod2, hpre1.1 x y, hval1 x y, List.sum_cons]

lemma build_one_rank2 {d : ℕ} (st : CircBuild d) (u1 v1 u2 v2 : Fin d → F2) :
    ∃ (st' : CircBuild d) (wOut : ℕ),
      (∃ ext, st'.gates = st.gates ++ ext) ∧
      wOut < ((d + 1) + (d + 1)) + st'.gates.length ∧
      st'.gates.countP nonlinear = st.gates.countP nonlinear + 1 ∧
      (depths ((d + 1) + (d + 1)) st'.gates).getD wOut 0 ≤ 1 ∧
      ∀ x y : Fin (d + 1),
        toF2 ((Circuit.wires ⟨st'.gates, 0⟩ (oneEach x y)).getD wOut false) =
          toF2 (tableMat (outerPair u1 v1 u2 v2) x y) := by
  let width := (d + 1) + (d + 1)
  let mkLinear : (Fin d → F2) → (Fin d → F2) → List ℕ := fun u v =>
    ((List.finRange d).filter (fun i => decide (u i ≠ 0))).map (fun i => i.succ.val) ++
    ((List.finRange d).filter (fun j => decide (v j ≠ 0))).map (fun j => (d + 1) + j.succ.val)
  have hmk_in : ∀ u v w, w ∈ mkLinear u v → w < width := by
    intro u v w hw
    simp only [mkLinear, List.mem_append, List.mem_map, List.mem_filter, List.mem_finRange,
      true_and] at hw
    rcases hw with ⟨i, _, rfl⟩ | ⟨j, _, rfl⟩ <;> dsimp only [width] <;> omega
  have hmk_d0 : ∀ (st0 : CircBuild d) u v, ∀ w ∈ mkLinear u v,
      (depths width st0.gates).getD w 0 = 0 := by
    intro st0 u v w hw
    have hw_lt := hmk_in u v w hw
    have hpre := circBuild_prefix_preserve ([] : List Gate) st0.gates (by simpa using hw_lt)
    rw [List.nil_append] at hpre
    rw [hpre.2]
    simp [depths, List.getD_eq_getElem?_getD, hw_lt]
  have hmk_val : ∀ (st0 : CircBuild d) (u v : Fin d → F2) (x y : Fin (d + 1)),
      ((mkLinear u v).map fun w =>
        toF2 ((Circuit.wires ⟨st0.gates, 0⟩ (oneEach x y)).getD w false)).sum =
      Fin.cases (0 : F2) u x + Fin.cases (0 : F2) v y := by
    intro st0 u v x y
    have hwire_in : ∀ w < width,
        (Circuit.wires ⟨st0.gates, 0⟩ (oneEach x y)).getD w false = (oneEach x y).getD w false := by
      intro w hw
      have hpre := circBuild_prefix_preserve ([] : List Gate) st0.gates (by simpa using hw)
      rw [List.nil_append] at hpre
      exact hpre.1 x y
    have hpart1 : ∀ (u : Fin d → F2),
        ((((List.finRange d).filter (fun i => decide (u i ≠ 0))).map (fun i => i.succ.val)).map
          fun w => toF2 ((Circuit.wires ⟨st0.gates, 0⟩ (oneEach x y)).getD w false)).sum =
        Fin.cases (0 : F2) u x := by
      intro u
      rw [List.map_map]
      have hterm : ∀ i : Fin d,
          toF2 ((Circuit.wires ⟨st0.gates, 0⟩ (oneEach x y)).getD i.succ.val false) =
            if x = i.succ then 1 else 0 := by
        intro i
        rw [hwire_in i.succ.val (by dsimp only [width]; omega)]
        dsimp only [oneEach]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp),
          List.getElem?_ofFn, dif_pos i.succ.isLt, Option.getD_some]
        have heq_fin : (⟨i.succ.val, i.succ.isLt⟩ : Fin (d + 1)) = i.succ := Fin.eta _ _
        rw [heq_fin]
        by_cases hx : x = i.succ
        · subst hx; simp [toF2_true]
        · simp [hx, Ne.symm hx, toF2_false]
      have hsum_all : ((((List.finRange d).filter (fun i => decide (u i ≠ 0))).map
          fun i => toF2 ((Circuit.wires ⟨st0.gates, 0⟩ (oneEach x y)).getD i.succ.val false))).sum =
          ∑ i : Fin d, (if u i ≠ 0 then (if x = i.succ then (1 : F2) else 0) else 0) := by
        have hnd : (List.finRange d).Nodup := List.nodup_finRange d
        have hflt_nd := hnd.filter (fun i => decide (u i ≠ 0))
        rw [← List.sum_toFinset _ hflt_nd]
        have htofin : ((List.finRange d).filter (fun i => decide (u i ≠ 0))).toFinset =
            Finset.univ.filter (fun i : Fin d => u i ≠ 0) := by
          ext i; simp [List.mem_filter]
        rw [htofin, sum_filter]
        refine sum_congr rfl fun i _ => ?_
        by_cases hu : u i ≠ 0
        · rw [if_pos hu, if_pos hu, hterm i]
        · rw [if_neg hu, if_neg hu]
      rw [show ((fun w => toF2 ((Circuit.wires ⟨st0.gates, 0⟩ (oneEach x y)).getD w false)) ∘
          (fun i : Fin d => i.succ.val)) =
          (fun i : Fin d => toF2 ((Circuit.wires ⟨st0.gates, 0⟩ (oneEach x y)).getD i.succ.val false)) from rfl]
      rw [hsum_all]
      cases x using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero]
        exact sum_eq_zero fun i _ => by simp [(Fin.succ_ne_zero i).symm]
      | succ i0 =>
        simp only [Fin.cases_succ]
        rw [sum_eq_single i0]
        · by_cases hu : u i0 ≠ 0
          · rw [if_pos hu, if_pos rfl]
            have := toF2_decide (u i0); simp [hu, toF2_true] at this; exact this
          · push_neg at hu; simp [hu]
        · intro i _ hne
          have : i0.succ ≠ i.succ := fun h => hne (Fin.succ_injective _ h).symm
          simp [this]
        · intro h; exact absurd (mem_univ i0) h
    have hpart2 : ∀ (v : Fin d → F2),
        ((((List.finRange d).filter (fun j => decide (v j ≠ 0))).map (fun j => (d + 1) + j.succ.val)).map
          fun w => toF2 ((Circuit.wires ⟨st0.gates, 0⟩ (oneEach x y)).getD w false)).sum =
        Fin.cases (0 : F2) v y := by
      intro v
      rw [List.map_map]
      have hterm : ∀ j : Fin d,
          toF2 ((Circuit.wires ⟨st0.gates, 0⟩ (oneEach x y)).getD ((d + 1) + j.succ.val) false) =
            if y = j.succ then 1 else 0 := by
        intro j
        rw [hwire_in ((d + 1) + j.succ.val) (by dsimp only [width]; omega)]
        dsimp only [oneEach]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp),
          List.length_ofFn, Nat.add_sub_cancel_left, List.getElem?_ofFn, dif_pos j.succ.isLt,
          Option.getD_some]
        have heq_fin : (⟨j.succ.val, j.succ.isLt⟩ : Fin (d + 1)) = j.succ := Fin.eta _ _
        rw [heq_fin]
        by_cases hy : y = j.succ
        · subst hy; simp [toF2_true]
        · simp [hy, Ne.symm hy, toF2_false]
      have hsum_all : ((((List.finRange d).filter (fun j => decide (v j ≠ 0))).map
          fun j => toF2 ((Circuit.wires ⟨st0.gates, 0⟩ (oneEach x y)).getD ((d + 1) + j.succ.val) false))).sum =
          ∑ j : Fin d, (if v j ≠ 0 then (if y = j.succ then (1 : F2) else 0) else 0) := by
        have hnd : (List.finRange d).Nodup := List.nodup_finRange d
        have hflt_nd := hnd.filter (fun j => decide (v j ≠ 0))
        rw [← List.sum_toFinset _ hflt_nd]
        have htofin : ((List.finRange d).filter (fun j => decide (v j ≠ 0))).toFinset =
            Finset.univ.filter (fun j : Fin d => v j ≠ 0) := by
          ext j; simp [List.mem_filter]
        rw [htofin, sum_filter]
        refine sum_congr rfl fun j _ => ?_
        by_cases hv : v j ≠ 0
        · rw [if_pos hv, if_pos hv, hterm j]
        · rw [if_neg hv, if_neg hv]
      rw [show ((fun w => toF2 ((Circuit.wires ⟨st0.gates, 0⟩ (oneEach x y)).getD w false)) ∘
          (fun j : Fin d => (d + 1) + j.succ.val)) =
          (fun j : Fin d => toF2 ((Circuit.wires ⟨st0.gates, 0⟩ (oneEach x y)).getD ((d + 1) + j.succ.val) false)) from rfl]
      rw [hsum_all]
      cases y using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero]
        exact sum_eq_zero fun j _ => by simp [(Fin.succ_ne_zero j).symm]
      | succ j0 =>
        simp only [Fin.cases_succ]
        rw [sum_eq_single j0]
        · by_cases hv : v j0 ≠ 0
          · rw [if_pos hv, if_pos rfl]
            have := toF2_decide (v j0); simp [hv, toF2_true] at this; exact this
          · push_neg at hv; simp [hv]
        · intro j _ hne
          have : j0.succ ≠ j.succ := fun h => hne (Fin.succ_injective _ h).symm
          simp [this]
        · intro h; exact absurd (mem_univ j0) h
    dsimp only [mkLinear]
    rw [List.map_append, List.sum_append, hpart1 u, hpart2 v]
  have h1_in : ∀ w ∈ mkLinear u1 v2, w < ((d + 1) + (d + 1)) + st.gates.length := fun w hw => by
    have := hmk_in u1 v2 w hw; dsimp only [width] at this; omega
  have h1_d : ∀ w ∈ mkLinear u1 v2, (depths ((d + 1) + (d + 1)) st.gates).getD w 0 ≤ 0 := fun w hw => by
    rw [hmk_d0 st u1 v2 w hw]
  obtain ⟨st1, w1, ⟨ext1, hext1⟩, hw1_lt, hcnt1, hd1, hval1⟩ := build_xor_list st (mkLinear u1 v2) h1_in 0 h1_d
  have h2_in : ∀ w ∈ mkLinear u2 v1, w < ((d + 1) + (d + 1)) + st1.gates.length := fun w hw => by
    have := hmk_in u2 v1 w hw; dsimp only [width] at this; omega
  have h2_d : ∀ w ∈ mkLinear u2 v1, (depths ((d + 1) + (d + 1)) st1.gates).getD w 0 ≤ 0 := fun w hw => by
    rw [hmk_d0 st1 u2 v1 w hw]
  obtain ⟨st2, w2, ⟨ext2, hext2⟩, hw2_lt, hcnt2, hd2, hval2⟩ := build_xor_list st1 (mkLinear u2 v1) h2_in 0 h2_d
  have hw1_in2 : w1 < ((d + 1) + (d + 1)) + st2.gates.length := by rw [hext2, List.length_append]; omega
  set r3 := st2.addAnd w1 w2 hw1_in2 hw2_lt
  have h4_in : ∀ w ∈ mkLinear (fun i => u1 i * u2 i) (fun j => v1 j * v2 j),
      w < ((d + 1) + (d + 1)) + r3.1.gates.length := fun w hw => by
    have := hmk_in _ _ w hw; dsimp only [width] at this; omega
  have h4_d : ∀ w ∈ mkLinear (fun i => u1 i * u2 i) (fun j => v1 j * v2 j),
      (depths ((d + 1) + (d + 1)) r3.1.gates).getD w 0 ≤ 0 := fun w hw => by
    rw [hmk_d0 r3.1 _ _ w hw]
  obtain ⟨st4, w4, ⟨ext4, hext4⟩, hw4_lt, hcnt4, hd4, hval4⟩ :=
    build_xor_list r3.1 (mkLinear (fun i => u1 i * u2 i) (fun j => v1 j * v2 j)) h4_in 0 h4_d
  have hw3_lt3 : r3.2 < ((d + 1) + (d + 1)) + r3.1.gates.length := by
    dsimp only [r3, CircBuild.addAnd, CircBuild.addGate]; rw [List.length_append, List.length_singleton]; omega
  have hw3_in4 : r3.2 < ((d + 1) + (d + 1)) + st4.gates.length := by rw [hext4, List.length_append]; omega
  set r5 := st4.addXor r3.2 w4 hw3_in4 hw4_lt
  have hpre12 := circBuild_prefix_preserve st1.gates ext2 hw1_lt
  rw [← hext2] at hpre12
  have hpre34 := circBuild_prefix_preserve r3.1.gates ext4 hw3_lt3
  rw [← hext4] at hpre34
  have hd3 : (depths ((d + 1) + (d + 1)) r3.1.gates).getD r3.2 0 ≤ 1 := by
    dsimp only [r3, CircBuild.addAnd]
    rw [addGate_new_depth, nonlinear_and2]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_true]
    rw [hpre12.2]
    omega
  refine ⟨r5.1, r5.2, ?_, ?_, ?_, ?_, fun x y => ?_⟩
  · refine ⟨ext1 ++ ext2 ++ [⟨GateOp.and, [w1, w2]⟩] ++ ext4 ++
      [⟨GateOp.mod 2, [r3.2, w4]⟩, ⟨GateOp.not, [((d + 1) + (d + 1)) + st4.gates.length]⟩], ?_⟩
    have h3 : r3.1.gates = st2.gates ++ [⟨GateOp.and, [w1, w2]⟩] := rfl
    have h5 : r5.1.gates = st4.gates ++
        [⟨GateOp.mod 2, [r3.2, w4]⟩, ⟨GateOp.not, [((d + 1) + (d + 1)) + st4.gates.length]⟩] := by
      dsimp only [r5, CircBuild.addXor, CircBuild.addGate]
      simp [List.append_assoc]
    rw [h5, hext4, h3, hext2, hext1]
    simp [List.append_assoc]
  · dsimp only [r5, CircBuild.addXor, CircBuild.addGate]
    simp only [List.length_append, List.length_singleton]; omega
  · have hcnt3 : r3.1.gates.countP nonlinear = st2.gates.countP nonlinear + 1 := by
      dsimp only [r3, CircBuild.addAnd]; rw [addGate_countP, nonlinear_and2]; rfl
    have hcnt5 : r5.1.gates.countP nonlinear = st4.gates.countP nonlinear := by
      dsimp only [r5, CircBuild.addXor]; rw [addGate_countP, addGate_countP, nonlinear_not1, nonlinear_mod2]; simp
    omega
  · dsimp only [r5, CircBuild.addXor]
    rw [addGate_new_depth, nonlinear_not1]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_false, add_zero]
    rw [addGate_new_depth, nonlinear_mod2]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_false, add_zero]
    rw [hpre34.2]
    omega
  · dsimp only [r5, CircBuild.addXor]
    rw [addGate_new_wire]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
    rw [addGate_new_wire]
    simp only [List.map_cons, List.map_nil, GateOp.eval]
    have hmod2 : ∀ a b : Bool, toF2 (!decide ([a, b].count true % 2 = 0)) = toF2 a + toF2 b := by
      intro a b; cases a <;> cases b <;> decide
    rw [hmod2, hpre34.1 x y, hval4 x y, hmk_val r3.1]
    have hval3 : toF2 ((Circuit.wires ⟨r3.1.gates, 0⟩ (oneEach x y)).getD r3.2 false) =
        (Fin.cases (0 : F2) u1 x + Fin.cases (0 : F2) v2 y) *
        (Fin.cases (0 : F2) u2 x + Fin.cases (0 : F2) v1 y) := by
      dsimp only [r3, CircBuild.addAnd]
      rw [addGate_new_wire]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq,
        Bool.and_true, toF2_and]
      rw [hpre12.1 x y, hval1 x y, hmk_val st, hval2 x y, hmk_val st1]
    rw [hval3]
    cases x using Fin.cases with
    | zero =>
      cases y using Fin.cases with
      | zero => simp [tableMat, toF2_false]
      | succ j =>
        simp only [tableMat, Fin.cases_zero, Fin.cases_succ, zero_add, toF2_false]
        have := f2_add_self (v2 j * v1 j)
        calc v2 j * v1 j + v1 j * v2 j = v2 j * v1 j + v2 j * v1 j := by ring
          _ = 0 := this
    | succ i =>
      cases y using Fin.cases with
      | zero =>
        simp only [tableMat, Fin.cases_zero, Fin.cases_succ, add_zero, toF2_false]
        exact f2_add_self (u1 i * u2 i)
      | succ j =>
        simp only [tableMat, Fin.cases_succ, toF2_decide]
        change (u1 i + v2 j) * (u2 i + v1 j) + (u1 i * u2 i + v1 j * v2 j) = u1 i * v1 j + u2 i * v2 j
        have hu := f2_add_self (u1 i * u2 i)
        have hv := f2_add_self (v1 j * v2 j)
        calc (u1 i + v2 j) * (u2 i + v1 j) + (u1 i * u2 i + v1 j * v2 j)
            = (u1 i * u2 i + u1 i * u2 i) + (v1 j * v2 j + v1 j * v2 j) +
              (u1 i * v1 j + u2 i * v2 j) := by ring
          _ = u1 i * v1 j + u2 i * v2 j := by rw [hu, hv]; ring

lemma rank2_list_to_circuit {d : ℕ}
    (ps : List ((Fin d → F2) × (Fin d → F2) × (Fin d → F2) × (Fin d → F2)))
    (S : Finset (Matrix (Fin d) (Fin d) F2))
    (hspan : ∀ M ∈ S, M ∈ Submodule.span F2
      {A | ∃ p ∈ ps, A = outerPair p.1 p.2.1 p.2.2.1 p.2.2.2}) :
    ∃ (C : Circuit) (tap : Matrix (Fin d) (Fin d) F2 → ℕ),
      ReadsBack ((d + 1) + (d + 1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      C.gates.countP nonlinear ≤ ps.length ∧
      ∀ M ∈ S,
        (depths ((d + 1) + (d + 1)) C.gates).getD (tap M) 0 ≤ 1 ∧
        Represents (tableMat M) ⟨C.gates, tap M⟩ := by
  classical
  have hphase1 : ∀ (qs : List ((Fin d → F2) × (Fin d → F2) × (Fin d → F2) × (Fin d → F2))),
      ∃ (st : CircBuild d) (ws : Fin qs.length → ℕ),
        st.gates.countP nonlinear = qs.length ∧
        ∀ (idx : Fin qs.length),
          let p := qs.get idx
          ws idx < ((d + 1) + (d + 1)) + st.gates.length ∧
          (depths ((d + 1) + (d + 1)) st.gates).getD (ws idx) 0 ≤ 1 ∧
          ∀ x y : Fin (d + 1),
            toF2 ((Circuit.wires ⟨st.gates, 0⟩ (oneEach x y)).getD (ws idx) false) =
              toF2 (tableMat (outerPair p.1 p.2.1 p.2.2.1 p.2.2.2) x y) := by
    intro qs
    induction qs with
    | nil =>
      refine ⟨⟨[], fun j hj => absurd hj (by simp), fun _ h => absurd h List.not_mem_nil⟩,
        fun idx => idx.elim0, rfl, fun idx => idx.elim0⟩
    | cons p qs ih =>
      obtain ⟨st, ws, hcnt, hspec⟩ := ih
      obtain ⟨st', w0, ⟨ext, hext⟩, hw0_lt, hcnt', hd0, hval0⟩ :=
        build_one_rank2 st p.1 p.2.1 p.2.2.1 p.2.2.2
      refine ⟨st', Fin.cons w0 ws, by rw [hcnt', hcnt]; rfl, fun idx => ?_⟩
      cases idx using Fin.cases with
      | zero =>
        exact ⟨hw0_lt, hd0, hval0⟩
      | succ j =>
        have hs := hspec j
        have hpre := circBuild_prefix_preserve st.gates ext hs.1
        rw [← hext] at hpre
        refine ⟨by simp only [Fin.cons_succ]; rw [hext, List.length_append]; omega, ?_, fun x y => ?_⟩
        · change (depths ((d + 1) + (d + 1)) st'.gates).getD (ws j) 0 ≤ 1
          rw [hpre.2]; exact hs.2.1
        · change toF2 ((Circuit.wires ⟨st'.gates, 0⟩ (oneEach x y)).getD (ws j) false) = _
          rw [hpre.1 x y]; exact hs.2.2 x y
  obtain ⟨st1, ws, hcnt1, hws_spec⟩ := hphase1 ps
  have hsub_sum : ∀ M ∈ S, ∃ idxs : List (Fin ps.length),
      M = (idxs.map fun idx =>
        let p := ps.get idx
        outerPair p.1 p.2.1 p.2.2.1 p.2.2.2).sum := by
    intro M hM
    have hmem := hspan M hM
    refine Submodule.span_induction (p := fun M _ => ∃ idxs : List (Fin ps.length),
        M = (idxs.map fun idx =>
          let p := ps.get idx
          outerPair p.1 p.2.1 p.2.2.1 p.2.2.2).sum) ?_ ?_ ?_ ?_ hmem
    · rintro A ⟨p, hp, rfl⟩
      obtain ⟨idx, rfl⟩ := List.mem_iff_get.1 hp
      exact ⟨[idx], by simp⟩
    · exact ⟨[], by simp⟩
    · rintro A B _ _ ⟨l1, rfl⟩ ⟨l2, rfl⟩
      exact ⟨l1 ++ l2, by simp⟩
    · rintro c A _ ⟨l, rfl⟩
      fin_cases c
      · exact ⟨[], by change (0 : F2) • _ = _; simp⟩
      · exact ⟨l, by change (1 : F2) • _ = _; simp⟩
  have hphase2 : ∀ (Ms : List (Matrix (Fin d) (Fin d) F2)),
      (∀ M ∈ Ms, M ∈ S) →
      ∃ (st : CircBuild d) (tap : Matrix (Fin d) (Fin d) F2 → ℕ),
        (∃ ext, st.gates = st1.gates ++ ext) ∧
        st.gates.countP nonlinear = st1.gates.countP nonlinear ∧
        ∀ M ∈ Ms,
          tap M < ((d + 1) + (d + 1)) + st.gates.length ∧
          (depths ((d + 1) + (d + 1)) st.gates).getD (tap M) 0 ≤ 1 ∧
          ∀ x y : Fin (d + 1),
            toF2 ((Circuit.wires ⟨st.gates, 0⟩ (oneEach x y)).getD (tap M) false) =
              toF2 (tableMat M x y) := by
    intro Ms
    induction Ms with
    | nil =>
      intro _
      exact ⟨st1, fun _ => 0, ⟨[], by simp⟩, rfl, fun _ h => absurd h List.not_mem_nil⟩
    | cons M Ms ih =>
      intro hMs
      obtain ⟨st, tap, ⟨ext0, hext0⟩, hcnt0, hspec0⟩ := ih (fun A hA => hMs A (List.mem_cons_of_mem M hA))
      obtain ⟨idxs, hM_sum⟩ := hsub_sum M (hMs M List.mem_cons_self)
      let wList : List ℕ := idxs.map ws
      have hwList_in : ∀ w ∈ wList, w < ((d + 1) + (d + 1)) + st.gates.length := by
        intro w hw
        obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hw
        have := (hws_spec idx).1
        rw [hext0, List.length_append]; omega
      have hwList_d : ∀ w ∈ wList, (depths ((d + 1) + (d + 1)) st.gates).getD w 0 ≤ 1 := by
        intro w hw
        obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hw
        have hpre := circBuild_prefix_preserve st1.gates ext0 (hws_spec idx).1
        rw [← hext0] at hpre
        rw [hpre.2]
        exact (hws_spec idx).2.1
      obtain ⟨st', wM, ⟨ext1, hext1⟩, hres_lt, hres_cnt, hres_d, hres_val⟩ :=
        build_xor_list st wList hwList_in 1 hwList_d
      refine ⟨st', fun A => if A = M then wM else tap A,
        ⟨ext0 ++ ext1, by rw [hext1, hext0, List.append_assoc]⟩,
        by rw [hres_cnt, hcnt0], fun A hA => ?_⟩
      dsimp only
      by_cases hAM : A = M
      · subst hAM
        rw [if_pos rfl]
        refine ⟨hres_lt, hres_d, fun x y => ?_⟩
        rw [hres_val x y]
        have hsum_eq : (wList.map fun w => toF2 ((Circuit.wires ⟨st.gates, 0⟩ (oneEach x y)).getD w false)).sum =
            (idxs.map fun idx => toF2 (tableMat (outerPair (ps.get idx).1 (ps.get idx).2.1
              (ps.get idx).2.2.1 (ps.get idx).2.2.2) x y)).sum := by
          dsimp only [wList]
          rw [List.map_map]
          congr 1
          refine List.map_congr_left fun idx _ => ?_
          have hpre := circBuild_prefix_preserve st1.gates ext0 (hws_spec idx).1
          rw [← hext0] at hpre
          change toF2 ((Circuit.wires ⟨st.gates, 0⟩ (oneEach x y)).getD (ws idx) false) = _
          rw [hpre.1 x y]
          exact (hws_spec idx).2.2 x y
        rw [hsum_eq, hM_sum]
        clear hsum_eq hM_sum hres_val wList hwList_in hwList_d ext1 hext1 hres_lt hres_cnt hres_d
        induction idxs with
        | nil =>
          cases x using Fin.cases <;> cases y using Fin.cases <;> simp [tableMat, toF2_false]
        | cons idx rest ihr =>
          rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ihr]
          have hadd : ∀ (A B : Matrix (Fin d) (Fin d) F2),
              toF2 (tableMat A x y) + toF2 (tableMat B x y) = toF2 (tableMat (A + B) x y) := by
            intro A B
            cases x using Fin.cases with
            | zero => simp [tableMat, toF2_false]
            | succ i =>
              cases y using Fin.cases with
              | zero => simp [tableMat, toF2_false]
              | succ j =>
                simp only [tableMat, Fin.cases_succ]
                rw [toF2_decide, toF2_decide, toF2_decide, Matrix.add_apply]
          exact hadd _ _
      · rw [if_neg hAM]
        have hA' : A ∈ Ms := (List.mem_cons.1 hA).resolve_left hAM
        have hs := hspec0 A hA'
        have hpre := circBuild_prefix_preserve st.gates ext1 hs.1
        rw [← hext1] at hpre
        refine ⟨by rw [hext1, List.length_append]; omega,
          by rw [hpre.2]; exact hs.2.1, fun x y => by rw [hpre.1 x y]; exact hs.2.2 x y⟩
  obtain ⟨stF, tap, _, hcntF, hspecF⟩ := hphase2 S.toList (fun M hM => Finset.mem_toList.1 hM)
  refine ⟨⟨stF.gates, 0⟩, tap, stF.rb, stF.fan, by rw [hcntF, hcnt1], fun M hM => ?_⟩
  have hs := hspecF M (Finset.mem_toList.2 hM)
  refine ⟨hs.2.1, fun x y => ?_⟩
  exact toF2_injective (hs.2.2 x y)

end Rank2ToCircuit

section MatrixBridge

def outerPairG {ι : Type*} (u1 v1 u2 v2 : ι → F2) : Matrix ι ι F2 :=
  Matrix.of fun i j => u1 i * v1 j + u2 i * v2 j

def IsRankLe2G {ι : Type*} (M : Matrix ι ι F2) : Prop :=
  ∃ u1 v1 u2 v2 : ι → F2, M = outerPairG u1 v1 u2 v2

def reindexLM {ι κ : Type*} (e : ι ≃ κ) : Matrix ι ι F2 ≃ₗ[F2] Matrix κ κ F2 :=
  { toFun := fun M => M.submatrix e.symm e.symm
    invFun := fun M => M.submatrix e e
    left_inv := fun M => by ext i j; simp
    right_inv := fun M => by ext i j; simp
    map_add' := fun A B => by ext i j; rfl
    map_smul' := fun c A => by ext i j; rfl }

lemma isRankLe2G_reindex {ι κ : Type*} (e : ι ≃ κ) {M : Matrix ι ι F2}
    (h : IsRankLe2G M) : IsRankLe2G (reindexLM e M) := by
  obtain ⟨u1, v1, u2, v2, rfl⟩ := h
  refine ⟨u1 ∘ e.symm, v1 ∘ e.symm, u2 ∘ e.symm, v2 ∘ e.symm, ?_⟩
  ext i j; rfl

lemma isRankLe2G_iff_fin {d : ℕ} (M : Matrix (Fin d) (Fin d) F2) :
    IsRankLe2G M ↔ IsRankLe2 M := Iff.rfl

abbrev J (n : ℕ) := Fin n ⊕ Fin n

def altM {n : ℕ} (A : Matrix (Fin n) (Fin n) F2) : Prop :=
  Aᵀ = A ∧ ∀ i, A i i = 0

def allowedM {n : ℕ} (edges : Finset (Fin n × Fin n)) (K : Matrix (Fin n) (Fin n) F2) : Prop :=
  altM K ∧ ∀ i j, (i, j) ∉ edges → (j, i) ∉ edges → K i j = 0

def blockX {n : ℕ} (A K : Matrix (Fin n) (Fin n) F2) : Matrix (J n) (J n) F2 :=
  Matrix.fromBlocks A K K (0 : Matrix (Fin n) (Fin n) F2)

def blockY {n f : ℕ} (B : Matrix (Fin n) (Fin f) F2) : Matrix (J n) (Fin f) F2 :=
  fun i j => Sum.elim (fun a => B a j) (fun _ => 0) i

def blockZ {n f : ℕ} (A K : Matrix (Fin n) (Fin n) F2) (B : Matrix (Fin n) (Fin f) F2) :
    Matrix (J n ⊕ Fin f) (J n ⊕ Fin f) F2 :=
  Matrix.fromBlocks (blockX A K) (blockY B) (blockY B)ᵀ (0 : Matrix (Fin f) (Fin f) F2)

lemma blockX_zero {n : ℕ} : blockX (0 : Matrix (Fin n) (Fin n) F2) 0 = 0 := by
  ext i j; cases i <;> cases j <;> rfl

lemma blockX_add {n : ℕ} (A1 K1 A2 K2 : Matrix (Fin n) (Fin n) F2) :
    blockX (A1 + A2) (K1 + K2) = blockX A1 K1 + blockX A2 K2 := by
  ext i j; cases i <;> cases j <;> simp [blockX]

lemma blockX_smul {n : ℕ} (c : F2) (A K : Matrix (Fin n) (Fin n) F2) :
    blockX (c • A) (c • K) = c • blockX A K := by
  ext i j; cases i <;> cases j <;> simp [blockX]

lemma blockY_zero {n f : ℕ} : blockY (0 : Matrix (Fin n) (Fin f) F2) = 0 := by
  ext i j; cases i <;> rfl

lemma blockY_add {n f : ℕ} (B1 B2 : Matrix (Fin n) (Fin f) F2) :
    blockY (B1 + B2) = blockY B1 + blockY B2 := by
  ext i j; cases i <;> simp [blockY]

lemma blockY_smul {n f : ℕ} (c : F2) (B : Matrix (Fin n) (Fin f) F2) :
    blockY (c • B) = c • blockY B := by
  ext i j; cases i <;> simp [blockY]

lemma blockZ_zero {n f : ℕ} :
    blockZ (0 : Matrix (Fin n) (Fin n) F2) 0 (0 : Matrix (Fin n) (Fin f) F2) = 0 := by
  ext i j
  cases i with
  | inl a => cases j with
    | inl b => cases a <;> cases b <;> rfl
    | inr b => cases a <;> rfl
  | inr a => cases j with
    | inl b => cases b <;> rfl
    | inr b => rfl

lemma blockZ_add {n f : ℕ} (A1 K1 A2 K2 : Matrix (Fin n) (Fin n) F2)
    (B1 B2 : Matrix (Fin n) (Fin f) F2) :
    blockZ (A1 + A2) (K1 + K2) (B1 + B2) = blockZ A1 K1 B1 + blockZ A2 K2 B2 := by
  ext i j
  cases i with
  | inl a => cases j with
    | inl b => cases a <;> cases b <;> simp [blockZ, blockX]
    | inr b => cases a <;> simp [blockZ, blockY]
  | inr a => cases j with
    | inl b => cases b <;> simp [blockZ, blockY]
    | inr b => simp [blockZ]

lemma blockZ_smul {n f : ℕ} (c : F2) (A K : Matrix (Fin n) (Fin n) F2)
    (B : Matrix (Fin n) (Fin f) F2) :
    blockZ (c • A) (c • K) (c • B) = c • blockZ A K B := by
  ext i j
  cases i with
  | inl a => cases j with
    | inl b => cases a <;> cases b <;> simp [blockZ, blockX]
    | inr b => cases a <;> simp [blockZ, blockY]
  | inr a => cases j with
    | inl b => cases b <;> simp [blockZ, blockY]
    | inr b => simp [blockZ]

lemma altM_zero {n : ℕ} : altM (0 : Matrix (Fin n) (Fin n) F2) := ⟨Matrix.transpose_zero, fun _ => rfl⟩

lemma altM_add {n : ℕ} {A B : Matrix (Fin n) (Fin n) F2} (hA : altM A) (hB : altM B) :
    altM (A + B) :=
  ⟨by rw [Matrix.transpose_add, hA.1, hB.1], fun i => by simp [hA.2 i, hB.2 i]⟩

lemma altM_smul {n : ℕ} (c : F2) {A : Matrix (Fin n) (Fin n) F2} (hA : altM A) :
    altM (c • A) :=
  ⟨by rw [Matrix.transpose_smul, hA.1], fun i => by simp [hA.2 i]⟩

lemma allowedM_zero {n : ℕ} (edges : Finset (Fin n × Fin n)) :
    allowedM edges (0 : Matrix (Fin n) (Fin n) F2) :=
  ⟨altM_zero, fun _ _ _ _ => rfl⟩

lemma allowedM_add {n : ℕ} {edges : Finset (Fin n × Fin n)} {K1 K2 : Matrix (Fin n) (Fin n) F2}
    (h1 : allowedM edges K1) (h2 : allowedM edges K2) : allowedM edges (K1 + K2) :=
  ⟨altM_add h1.1 h2.1, fun i j hne1 hne2 => by simp [h1.2 i j hne1 hne2, h2.2 i j hne1 hne2]⟩

lemma allowedM_smul {n : ℕ} {edges : Finset (Fin n × Fin n)} (c : F2) {K : Matrix (Fin n) (Fin n) F2}
    (h : allowedM edges K) : allowedM edges (c • K) :=
  ⟨altM_smul c h.1, fun i j hne1 hne2 => by simp [h.2 i j hne1 hne2]⟩

def W0 {n : ℕ} (edges : Finset (Fin n × Fin n)) : Submodule F2 (Matrix (J n) (J n) F2) :=
  { carrier := {M | ∃ A K, altM A ∧ allowedM edges K ∧ M = blockX A K}
    zero_mem' := ⟨0, 0, altM_zero, allowedM_zero edges, blockX_zero.symm⟩, add_mem' := by
      rintro _ _ ⟨A1, K1, hA1, hK1, rfl⟩ ⟨A2, K2, hA2, hK2, rfl⟩
      exact ⟨A1 + A2, K1 + K2, altM_add hA1 hA2, allowedM_add hK1 hK2, (blockX_add A1 K1 A2 K2).symm⟩
    smul_mem' := by
      rintro c _ ⟨A, K, hA, hK, rfl⟩
      exact ⟨c • A, c • K, altM_smul c hA, allowedM_smul c hK, (blockX_smul c A K).symm⟩ }

def Wf {n : ℕ} (edges : Finset (Fin n × Fin n)) (f : ℕ) :
    Submodule F2 (Matrix (J n ⊕ Fin f) (J n ⊕ Fin f) F2) :=
  { carrier := {M | ∃ A K B, altM A ∧ allowedM edges K ∧ M = blockZ A K B}
    zero_mem' := ⟨0, 0, 0, altM_zero, allowedM_zero edges, blockZ_zero.symm⟩, add_mem' := by
      rintro _ _ ⟨A1, K1, B1, hA1, hK1, rfl⟩ ⟨A2, K2, B2, hA2, hK2, rfl⟩
      exact ⟨A1 + A2, K1 + K2, B1 + B2, altM_add hA1 hA2, allowedM_add hK1 hK2,
        (blockZ_add A1 K1 A2 K2 B1 B2).symm⟩
    smul_mem' := by
      rintro c _ ⟨A, K, B, hA, hK, rfl⟩
      exact ⟨c • A, c • K, c • B, altM_smul c hA, allowedM_smul c hK, (blockZ_smul c A K B).symm⟩ }

def coordEquiv (n f : ℕ) : J n ⊕ Fin f ≃ Fin (n + n + f) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin f))).trans finSumFinEquiv

def dropFin0 (n : ℕ) : J n ⊕ Fin 0 ≃ J n :=
  { toFun := Sum.elim id Fin.elim0
    invFun := Sum.inl
    left_inv := fun x => by cases x with | inl a => rfl | inr b => exact Fin.elim0 b
    right_inv := fun _ => rfl }

def bankProp {n : ℕ} (edges : Finset (Fin n × Fin n)) (f t : ℕ) : Prop :=
  let d := n + n + f
  let coord := coordEquiv n f
  ∃ (C : Circuit) (tap : Matrix (Fin n) (Fin n) F2 → Matrix (Fin n) (Fin n) F2 → Matrix (Fin n) (Fin f) F2 → ℕ),
    ReadsBack ((d + 1) + (d + 1)) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    C.gates.countP nonlinear ≤ t ∧
    ∀ A K B, altM A → allowedM edges K →
      (depths ((d + 1) + (d + 1)) C.gates).getD (tap A K B) 0 ≤ 1 ∧
      Represents (tableMat (reindexLM coord (blockZ A K B))) ⟨C.gates, tap A K B⟩

lemma bankProp_iff_span {n : ℕ} (edges : Finset (Fin n × Fin n)) (f t : ℕ) :
    bankProp edges f t ↔
      ∃ Ms : List (Matrix (J n ⊕ Fin f) (J n ⊕ Fin f) F2),
        Ms.length ≤ t ∧
        (∀ M ∈ Ms, IsRankLe2G M) ∧
        Wf edges f ≤ Submodule.span F2 {M | M ∈ Ms} := by
  classical
  let d := n + n + f
  let coord := coordEquiv n f
  let eM := reindexLM coord
  constructor
  · rintro ⟨C, tap, _, hfan, hcnt, hspec⟩
    obtain ⟨MsFin, hMs_len, hMs_rk, hMs_wire⟩ := circuit_to_rank2_span (d := d) C.gates hfan
    let Ms := MsFin.map fun M => eM.symm M
    refine ⟨Ms, by rw [List.length_map]; exact le_trans hMs_len hcnt, ?_, ?_⟩
    · intro M hM
      obtain ⟨M0, hM0, rfl⟩ := List.mem_map.1 hM
      exact isRankLe2G_reindex coord.symm ((isRankLe2G_iff_fin M0).2 (hMs_rk M0 hM0))
    · rintro _ ⟨A, K, B, hA, hK, rfl⟩
      obtain ⟨hdep, hrep⟩ := hspec A K B hA hK
      have hmem0 := (hMs_wire (tap A K B)).2 hdep
      have hfun_eq : (fun x y : Fin (d + 1) =>
          toF2 ((Circuit.wires ⟨C.gates, 0⟩ (oneEach x y)).getD (tap A K B) false)) =
          fun x y => toF2 (tableMat (eM (blockZ A K B)) x y) := by
        funext x y; exact congrArg toF2 (hrep x y)
      rw [hfun_eq, delta_tableMat] at hmem0
      have hmap : eM.symm (eM (blockZ A K B)) ∈
          (Submodule.span F2 {M | M ∈ MsFin}).map eM.symm.toLinearMap :=
        Submodule.mem_map_of_mem hmem0
      rw [Submodule.map_span, eM.symm_apply_apply] at hmap
      have hle : Submodule.span F2 (eM.symm.toLinearMap '' {M | M ∈ MsFin}) ≤
          Submodule.span F2 {M | M ∈ Ms} := by
        refine Submodule.span_mono ?_
        rintro _ ⟨M0, hM0, rfl⟩
        exact List.mem_map.2 ⟨M0, hM0, rfl⟩
      exact hle hmap
  · rintro ⟨Ms, hMs_len, hMs_rk, hW_le⟩
    let pick : Matrix (J n ⊕ Fin f) (J n ⊕ Fin f) F2 →
        (Fin d → F2) × (Fin d → F2) × (Fin d → F2) × (Fin d → F2) := fun M =>
      if h : IsRankLe2G M then
        let u1 := Classical.choose h
        let v1 := Classical.choose (Classical.choose_spec h)
        let u2 := Classical.choose (Classical.choose_spec (Classical.choose_spec h))
        let v2 := Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h)))
        (u1 ∘ coord.symm, v1 ∘ coord.symm, u2 ∘ coord.symm, v2 ∘ coord.symm)
      else (0, 0, 0, 0)
    have hpick : ∀ M, IsRankLe2G M →
        let p := pick M
        outerPair p.1 p.2.1 p.2.2.1 p.2.2.2 = eM M := by
      intro M h
      dsimp only [pick]
      rw [dif_pos h]
      have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h)))
      ext i j
      have hij := congrFun (congrFun hspec (coord.symm i)) (coord.symm j)
      simpa [eM, reindexLM, outerPair, outerPairG] using hij.symm
    let ps := Ms.map pick
    let S : Finset (Matrix (Fin d) (Fin d) F2) :=
      Finset.univ.filter fun M => eM.symm M ∈ Wf edges f
    have hS_span : ∀ M ∈ S, M ∈ Submodule.span F2
        {A | ∃ p ∈ ps, A = outerPair p.1 p.2.1 p.2.2.1 p.2.2.2} := by
      intro M hM
      have hmem : eM.symm M ∈ Wf edges f := (mem_filter.1 hM).2
      have hsp := hW_le hmem
      have hmap : eM (eM.symm M) ∈ (Submodule.span F2 {A | A ∈ Ms}).map eM.toLinearMap :=
        Submodule.mem_map_of_mem hsp
      rw [Submodule.map_span, eM.apply_symm_apply] at hmap
      have hle : Submodule.span F2 (eM.toLinearMap '' {A | A ∈ Ms}) ≤
          Submodule.span F2 {A | ∃ p ∈ ps, A = outerPair p.1 p.2.1 p.2.2.1 p.2.2.2} := by
        refine Submodule.span_mono ?_
        rintro _ ⟨A, hA, rfl⟩
        exact ⟨pick A, List.mem_map.2 ⟨A, hA, rfl⟩, (hpick A (hMs_rk A hA)).symm⟩
      exact hle hmap
    obtain ⟨C, tapM, hrb, hfan, hcnt, hrep⟩ := rank2_list_to_circuit ps S hS_span
    refine ⟨C, fun A K B => tapM (eM (blockZ A K B)), hrb, hfan,
      le_trans hcnt (by simpa [ps] using hMs_len), fun A K B hA hK => ?_⟩
    have hmemS : eM (blockZ A K B) ∈ S := by
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      rw [eM.symm_apply_apply]
      exact ⟨A, K, B, hA, hK, rfl⟩
    exact hrep _ hmemS

lemma bankProp0_iff_span {n : ℕ} (edges : Finset (Fin n × Fin n)) (t : ℕ) :
    bankProp edges 0 t ↔
      ∃ Ms : List (Matrix (J n) (J n) F2),
        Ms.length ≤ t ∧
        (∀ M ∈ Ms, IsRankLe2G M) ∧
        W0 edges ≤ Submodule.span F2 {M | M ∈ Ms} := by
  rw [bankProp_iff_span]
  let e0 := reindexLM (dropFin0 n)
  have hW_img : ∀ M : Matrix (J n ⊕ Fin 0) (J n ⊕ Fin 0) F2,
      M ∈ Wf edges 0 ↔ e0 M ∈ W0 edges := by
    intro M
    constructor
    · rintro ⟨A, K, B, hA, hK, rfl⟩
      refine ⟨A, K, hA, hK, ?_⟩
      ext i j; rfl
    · rintro ⟨A, K, hA, hK, hEq⟩
      refine ⟨A, K, 0, hA, hK, ?_⟩
      ext i j
      cases i with
      | inl a => cases j with
        | inl b => exact congrFun (congrFun hEq a) b
        | inr b => exact Fin.elim0 b
      | inr a => exact Fin.elim0 a
  constructor
  · rintro ⟨Ms, hlen, hrk, hle⟩
    refine ⟨Ms.map e0, by simpa using hlen, ?_, ?_⟩
    · intro M hM
      obtain ⟨M0, hM0, rfl⟩ := List.mem_map.1 hM
      exact isRankLe2G_reindex (dropFin0 n) (hrk M0 hM0)
    · intro M hM
      have h0 : e0.symm M ∈ Wf edges 0 := (hW_img (e0.symm M)).2 (by simpa using hM)
      have hsp := hle h0
      have hmap : e0 (e0.symm M) ∈ (Submodule.span F2 {A | A ∈ Ms}).map e0.toLinearMap :=
        Submodule.mem_map_of_mem hsp
      rw [Submodule.map_span, e0.apply_symm_apply] at hmap
      have hsub : Submodule.span F2 (e0.toLinearMap '' {A | A ∈ Ms}) ≤
          Submodule.span F2 {A | A ∈ Ms.map e0} := by
        refine Submodule.span_mono ?_
        rintro _ ⟨A, hA, rfl⟩
        exact List.mem_map.2 ⟨A, hA, rfl⟩
      exact hsub hmap
  · rintro ⟨Ms, hlen, hrk, hle⟩
    refine ⟨Ms.map e0.symm, by simpa using hlen, ?_, ?_⟩
    · intro M hM
      obtain ⟨M0, hM0, rfl⟩ := List.mem_map.1 hM
      exact isRankLe2G_reindex (dropFin0 n).symm (hrk M0 hM0)
    · intro M hM
      have h0 : e0 M ∈ W0 edges := (hW_img M).1 hM
      have hsp := hle h0
      have hmap : e0.symm (e0 M) ∈ (Submodule.span F2 {A | A ∈ Ms}).map e0.symm.toLinearMap :=
        Submodule.mem_map_of_mem hsp
      rw [Submodule.map_span, e0.symm_apply_apply] at hmap
      have hsub : Submodule.span F2 (e0.symm.toLinearMap '' {A | A ∈ Ms}) ≤
          Submodule.span F2 {A | A ∈ Ms.map e0.symm} := by
        refine Submodule.span_mono ?_
        rintro _ ⟨A, hA, rfl⟩
        exact List.mem_map.2 ⟨A, hA, rfl⟩
      exact hsub hmap

end MatrixBridge

section LinearAlgHelpers

lemma f2_eq_one_of_ne_zero {x : F2} (h : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl h
  · rfl

lemma single_mul_singleG {ι : Type*} [DecidableEq ι] (a b i j : ι) :
    (Pi.single a (1 : F2) : ι → F2) i * (Pi.single b (1 : F2) : ι → F2) j =
      if i = a ∧ j = b then 1 else 0 := by
  by_cases hi : i = a <;> by_cases hj : j = b <;> simp [Pi.single_apply, hi, hj]

lemma exists_sublist_span_li {V : Type*} [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]
    (L : List V) :
    ∃ L' : List V, (∀ x ∈ L', x ∈ L) ∧
      Submodule.span F2 {x | x ∈ L'} = Submodule.span F2 {x | x ∈ L} ∧
      LinearIndependent F2 (fun i : Fin L'.length => L'.get i) ∧
      L'.length ≤ Module.finrank F2 (Submodule.span F2 {x | x ∈ L}) := by
  classical
  let P : ℕ → Prop := fun k =>
    ∃ L' : List V, L'.length = k ∧ (∀ x ∈ L', x ∈ L) ∧
      Submodule.span F2 {x | x ∈ L'} = Submodule.span F2 {x | x ∈ L}
  have hex : ∃ k, P k := ⟨L.length, L, rfl, fun _ h => h, rfl⟩
  let k0 := Nat.find hex
  obtain ⟨L', hlen, hsub, hspan⟩ := Nat.find_spec hex
  have hli : LinearIndependent F2 (fun i : Fin L'.length => L'.get i) := by
    rw [Fintype.linearIndependent_iff]
    intro c hsum i0
    by_contra hne
    have hc1 : c i0 = 1 := f2_eq_one_of_ne_zero hne
    have hsplit : L'.get i0 = ∑ i ∈ (Finset.univ : Finset (Fin L'.length)).erase i0, c i • L'.get i := by
      have h1 := add_sum_erase (s := (Finset.univ : Finset (Fin L'.length)))
        (f := fun i => c i • L'.get i) (mem_univ i0)
      rw [hsum, hc1, one_smul] at h1
      have h2 := congrArg (fun z => L'.get i0 + z) h1
      rw [← add_assoc, show L'.get i0 + L'.get i0 = 0 from by
        have : (1 : F2) + 1 = 0 := rfl
        calc L'.get i0 + L'.get i0 = ((1 : F2) + 1) • L'.get i0 := by rw [add_smul, one_smul]
          _ = 0 := by rw [this, zero_smul],
        zero_add, add_zero] at h2
      exact h2.symm
    let L'' := L'.eraseIdx i0.val
    have hL''_sub : ∀ x ∈ L'', x ∈ L := fun x hx => hsub x (List.mem_of_mem_eraseIdx hx)
    have hL''_mem : ∀ i : Fin L'.length, i ≠ i0 → L'.get i ∈ L'' := by
      intro i hne'
      have hne_val : i.val ≠ i0.val := fun h => hne' (Fin.ext h)
      have hlt : i0.val < L'.length := i0.isLt
      rcases lt_or_gt_of_ne hne_val with h1 | h2
      · have : L''[i.val]'(by simp [L'', List.length_eraseIdx, hlt]; omega) = L'.get i := by
          simp [L'', List.getElem_eraseIdx, h1]
        rw [← this]; exact List.getElem_mem _
      · have : L''[i.val - 1]'(by simp [L'', List.length_eraseIdx, hlt]; omega) = L'.get i := by
          simp [L'', List.getElem_eraseIdx, show ¬ i.val - 1 < i0.val by omega,
            show i.val - 1 + 1 = i.val by omega]
        rw [← this]; exact List.getElem_mem _
    have hget_mem : L'.get i0 ∈ Submodule.span F2 {x | x ∈ L''} := by
      rw [hsplit]
      refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
      exact Submodule.subset_span (hL''_mem i (mem_erase.1 hi).1)
    have hspan'' : Submodule.span F2 {x | x ∈ L''} = Submodule.span F2 {x | x ∈ L} := by
      rw [← hspan]
      refine le_antisymm (Submodule.span_mono fun x hx => List.mem_of_mem_eraseIdx hx) ?_
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hx
      by_cases hi : i = i0
      · subst hi; exact hget_mem
      · exact Submodule.subset_span (hL''_mem i hi)
    have hlen'' : L''.length = k0 - 1 := by
      dsimp only [L'', k0]
      rw [List.length_eraseIdx, if_pos i0.isLt, hlen]
    have hk0_pos : 0 < k0 := by have := i0.isLt; omega
    exact Nat.find_min hex (show k0 - 1 < k0 by omega) ⟨L'', hlen'', hL''_sub, hspan''⟩
  have hle_rank : L'.length ≤ Module.finrank F2 (Submodule.span F2 {x | x ∈ L}) := by
    rw [← hspan]
    let f : Fin L'.length → ↥(Submodule.span F2 {x | x ∈ L'}) :=
      fun i => ⟨L'.get i, Submodule.subset_span (List.get_mem L' i)⟩
    have hf_li : LinearIndependent F2 f := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have h0 : ∑ i : Fin L'.length, c i • L'.get i = 0 := by
        have := congrArg Subtype.val hc
        simpa [f, Submodule.coe_sum, Submodule.coe_smul_of_tower] using this
      exact Fintype.linearIndependent_iff.1 hli c h0
    simpa using hf_li.fintype_card_le_finrank
  exact ⟨L', hsub, hspan, hli, hle_rank⟩

abbrev PairLt (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

lemma card_pairLt (n : ℕ) : Fintype.card (PairLt n) = Nat.choose n 2 := by
  have hbij : Fintype.card (PairLt n) = ((Finset.univ : Finset (Fin n)).powersetCard 2).card := by
    rw [Fintype.card_subtype]
    refine card_bij (fun p _ => {p.1, p.2}) ?_ ?_ ?_
    · rintro ⟨a, b⟩ hp
      have hlt : a < b := (mem_filter.1 hp).2
      have hne : a ≠ b := ne_of_lt hlt
      exact mem_powersetCard.2 ⟨subset_univ _, card_pair hne⟩
    · rintro ⟨a1, b1⟩ hp1 ⟨a2, b2⟩ hp2 heq
      have hlt1 : a1 < b1 := (mem_filter.1 hp1).2
      have hlt2 : a2 < b2 := (mem_filter.1 hp2).2
      have h1 : a1 ∈ ({a2, b2} : Finset (Fin n)) := by rw [← heq]; simp
      have h2 : b1 ∈ ({a2, b2} : Finset (Fin n)) := by rw [← heq]; simp
      simp only [mem_insert, mem_singleton] at h1 h2
      rcases h1 with rfl | rfl <;> rcases h2 with h | h
      · exact absurd h (ne_of_gt hlt1)
      · exact Prod.ext rfl h
      · subst h; exact absurd (lt_trans hlt1 hlt2) (lt_irrefl _)
      · exact absurd hlt1 (by rw [h]; exact lt_irrefl _)
    · intro s hs
      obtain ⟨_, hcard⟩ := mem_powersetCard.1 hs
      obtain ⟨a, b, hne, rfl⟩ := card_eq_two.1 hcard
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨(a, b), mem_filter.2 ⟨mem_univ _, hlt⟩, rfl⟩
      · exact ⟨(b, a), mem_filter.2 ⟨mem_univ _, hgt⟩, by ext x; simp [or_comm]⟩
  rw [hbij, card_powersetCard, card_univ, Fintype.card_fin]

lemma finrank_W0 {n : ℕ} (edges : Finset (Fin n × Fin n)) (hedges : ∀ p ∈ edges, p.1 < p.2) :
    Module.finrank F2 (W0 edges) = Nat.choose n 2 + edges.card := by
  classical
  let Coord := PairLt n ⊕ {p : Fin n × Fin n // p ∈ edges}
  let toCoord : W0 edges →ₗ[F2] (Coord → F2) :=
    { toFun := fun M c => match c with
        | Sum.inl p => M.1 (Sum.inl p.1.1) (Sum.inl p.1.2)
        | Sum.inr p => M.1 (Sum.inl p.1.1) (Sum.inr p.1.2)
      map_add' := fun M1 M2 => by funext c; cases c <;> rfl
      map_smul' := fun c M => by funext k; cases k <;> rfl }
  have hinj : Function.Injective toCoord := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨M, A, K, hA, hK, rfl⟩ h0
    apply Subtype.ext
    have hA0 : A = 0 := by
      ext i j
      rcases lt_trichotomy i j with hlt | rfl | hgt
      · have := congrFun h0 (Sum.inl ⟨(i, j), hlt⟩)
        simpa [toCoord, blockX] using this
      · exact hA.2 i
      · have hsym : A i j = A j i := congrFun (congrFun hA.1 j) i
        rw [hsym]
        have := congrFun h0 (Sum.inl ⟨(j, i), hgt⟩)
        simpa [toCoord, blockX] using this
    have hK0 : K = 0 := by
      ext i j
      by_cases h1 : (i, j) ∈ edges
      · have := congrFun h0 (Sum.inr ⟨(i, j), h1⟩)
        simpa [toCoord, blockX] using this
      · by_cases h2 : (j, i) ∈ edges
        · have hsym : K i j = K j i := congrFun (congrFun hK.1.1 j) i
          rw [hsym]
          have := congrFun h0 (Sum.inr ⟨(j, i), h2⟩)
          simpa [toCoord, blockX] using this
        · exact hK.2 i j h1 h2
    change blockX A K = 0
    rw [hA0, hK0, blockX_zero]
  have hsurj : Function.Surjective toCoord := by
    intro g
    let A : Matrix (Fin n) (Fin n) F2 := Matrix.of fun i j =>
      if h1 : i < j then g (Sum.inl ⟨(i, j), h1⟩)
      else if h2 : j < i then g (Sum.inl ⟨(j, i), h2⟩)
      else 0
    let K : Matrix (Fin n) (Fin n) F2 := Matrix.of fun i j =>
      if h1 : (i, j) ∈ edges then g (Sum.inr ⟨(i, j), h1⟩)
      else if h2 : (j, i) ∈ edges then g (Sum.inr ⟨(j, i), h2⟩)
      else 0
    have hA : altM A := by
      refine ⟨?_, fun i => by simp [A]⟩
      ext i j
      simp only [Matrix.transpose_apply, A, Matrix.of_apply]
      rcases lt_trichotomy j i with hlt | rfl | hgt
      · rw [dif_pos hlt, dif_neg (not_lt_of_gt hlt), dif_pos hlt]
      · simp
      · rw [dif_neg (not_lt_of_gt hgt), dif_pos hgt, dif_pos hgt]
    have hK : allowedM edges K := by
      refine ⟨⟨?_, fun i => ?_⟩, fun i j h1 h2 => by simp [K, h1, h2]⟩
      · ext i j
        simp only [Matrix.transpose_apply, K, Matrix.of_apply]
        by_cases h1 : (j, i) ∈ edges
        · have h1' : (i, j) ∉ edges := fun h => by
            have := hedges _ h; have := hedges _ h1; exact absurd (lt_trans this ‹_›) (lt_irrefl _)
          rw [dif_pos h1, dif_neg h1', dif_pos h1]
        · by_cases h2 : (i, j) ∈ edges
          · rw [dif_neg h1, dif_pos h2, dif_pos h2]
          · rw [dif_neg h1, dif_neg h2, dif_neg h2, dif_neg h1]
      · have hni : (i, i) ∉ edges := fun h => absurd (hedges _ h) (lt_irrefl _)
        simp [K, hni]
    refine ⟨⟨blockX A K, A, K, hA, hK, rfl⟩, ?_⟩
    funext c
    rcases c with ⟨⟨i, j⟩, hlt⟩ | ⟨⟨i, j⟩, hmem⟩
    · simp only [toCoord, LinearMap.coe_mk, AddHom.coe_mk, blockX, Matrix.fromBlocks_apply₁₁,
        A, Matrix.of_apply]
      rw [dif_pos hlt]
    · simp only [toCoord, LinearMap.coe_mk, AddHom.coe_mk, blockX, Matrix.fromBlocks_apply₁₂,
        K, Matrix.of_apply]
      rw [dif_pos hmem]
  let e : W0 edges ≃ₗ[F2] (Coord → F2) := LinearEquiv.ofBijective toCoord ⟨hinj, hsurj⟩
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card]
  simp only [Coord, Fintype.card_sum, card_pairLt, Fintype.card_coe]

def projJ {n f : ℕ} : Matrix (J n ⊕ Fin f) (J n ⊕ Fin f) F2 →ₗ[F2] Matrix (J n) (J n) F2 :=
  { toFun := fun M => M.submatrix Sum.inl Sum.inl
    map_add' := fun A B => by ext i j; rfl
    map_smul' := fun c A => by ext i j; rfl }

lemma projJ_rank2 {n f : ℕ} {M : Matrix (J n ⊕ Fin f) (J n ⊕ Fin f) F2}
    (h : IsRankLe2G M) : IsRankLe2G (projJ M) := by
  obtain ⟨u1, v1, u2, v2, rfl⟩ := h
  exact ⟨u1 ∘ Sum.inl, v1 ∘ Sum.inl, u2 ∘ Sum.inl, v2 ∘ Sum.inl, by ext i j; rfl⟩

lemma finrank_ker_projJ_Wf {n f : ℕ} (edges : Finset (Fin n × Fin n)) :
    Module.finrank F2 (LinearMap.ker (projJ.domRestrict (Wf edges f))) = n * f := by
  let toKer : Matrix (Fin n) (Fin f) F2 →ₗ[F2] LinearMap.ker (projJ.domRestrict (Wf edges f)) :=
    { toFun := fun B => ⟨⟨blockZ 0 0 B, 0, 0, B, altM_zero, allowedM_zero edges, rfl⟩, by
        ext i j; cases i <;> cases j <;> rfl⟩
      map_add' := fun B1 B2 => by
        apply Subtype.ext; apply Subtype.ext
        simpa using blockZ_add (0 : Matrix (Fin n) (Fin n) F2) 0 0 0 B1 B2
      map_smul' := fun c B => by
        apply Subtype.ext; apply Subtype.ext
        simpa using blockZ_smul c (0 : Matrix (Fin n) (Fin n) F2) 0 B }
  have hinj : Function.Injective toKer := by
    intro B1 B2 h
    have hM := congrArg (fun x => x.1.1) h
    ext a b
    have := congrFun (congrFun hM (Sum.inl (Sum.inl a))) (Sum.inr b)
    simpa [toKer, blockZ, blockY] using this
  have hsurj : Function.Surjective toKer := by
    rintro ⟨⟨_, A, K, B, hA, hK, rfl⟩, hker⟩
    have hX0 : blockX A K = 0 := by
      ext i j
      exact congrFun (congrFun hker i) j
    have hA0 : A = 0 := by
      ext i j
      have := congrFun (congrFun hX0 (Sum.inl i)) (Sum.inl j)
      simpa [blockX] using this
    have hK0 : K = 0 := by
      ext i j
      have := congrFun (congrFun hX0 (Sum.inl i)) (Sum.inr j)
      simpa [blockX] using this
    refine ⟨B, ?_⟩
    apply Subtype.ext; apply Subtype.ext
    simp [toKer, hA0, hK0]
  let e : Matrix (Fin n) (Fin f) F2 ≃ₗ[F2] LinearMap.ker (projJ.domRestrict (Wf edges f)) :=
    LinearEquiv.ofBijective toKer ⟨hinj, hsurj⟩
  rw [← e.finrank_eq]
  rw [Module.finrank_matrix, Fintype.card_fin, Fintype.card_fin, Module.finrank_self, mul_one]

end LinearAlgHelpers

section Part1Padding

lemma part1_padding {n : ℕ} (edges : Finset (Fin n × Fin n)) (f t : ℕ) :
    bankProp edges f t ↔ n * f ≤ t ∧ bankProp edges 0 (t - n * f) := by
  classical
  rw [bankProp_iff_span, bankProp0_iff_span]
  constructor
  · rintro ⟨Ms, hMs_len, hMs_rk, hW_le⟩
    let U := Submodule.span F2 {M | M ∈ Ms}
    have hU_rank : Module.finrank F2 U ≤ t := by
      have hrange : LinearMap.range (Fintype.linearCombination F2 (fun i : Fin Ms.length => Ms.get i)) = U := by
        rw [Fintype.range_linearCombination]
        congr 1; ext M; simp [List.mem_iff_get]
      have h1 : Module.finrank F2 U ≤ Ms.length := by
        rw [← hrange]
        calc Module.finrank F2 _ ≤ Module.finrank F2 (Fin Ms.length → F2) := LinearMap.finrank_range_le _
          _ = Ms.length := Module.finrank_fin_fun F2
      exact le_trans h1 hMs_len
    let kerWf := LinearMap.ker (projJ.domRestrict (Wf edges f))
    let kerU := LinearMap.ker (projJ.domRestrict U)
    have hker_le : Module.finrank F2 kerWf ≤ Module.finrank F2 kerU := by
      let emb : kerWf →ₗ[F2] kerU :=
        { toFun := fun x => ⟨⟨x.1.1, hW_le x.1.2⟩, x.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hemb_inj : Function.Injective emb := fun a b h =>
        Subtype.ext (Subtype.ext (congrArg (fun z => z.1.1) h))
      exact LinearMap.finrank_le_finrank_of_injective hemb_inj
    have hkerWf_eq : Module.finrank F2 kerWf = n * f := finrank_ker_projJ_Wf edges
    have hrn := LinearMap.finrank_range_add_finrank_ker (projJ.domRestrict U)
    dsimp only [kerU] at hker_le
    have hnf_le_t : n * f ≤ t := by omega
    have hrange_eq : LinearMap.range (projJ.domRestrict U) = Submodule.span F2 {M | M ∈ Ms.map projJ} := by
      have h1 : LinearMap.range (projJ.domRestrict U) = U.map projJ := by
        ext y; simp [LinearMap.mem_range, Submodule.mem_map]
      rw [h1, Submodule.map_span]
      congr 1; ext y; simp
    obtain ⟨L', hL'_sub, hL'_span, _, hL'_len⟩ := exists_sublist_span_li (Ms.map projJ)
    refine ⟨hnf_le_t, L', ?_, ?_, ?_⟩
    · rw [← hrange_eq] at hL'_len; omega
    · intro M hM
      obtain ⟨M0, hM0, rfl⟩ := List.mem_map.1 (hL'_sub M hM)
      exact projJ_rank2 (hMs_rk M0 hM0)
    · rintro _ ⟨A, K, hA, hK, rfl⟩
      rw [hL'_span, ← hrange_eq]
      exact ⟨⟨blockZ A K 0, hW_le ⟨A, K, 0, hA, hK, rfl⟩⟩, by ext i j; rfl⟩
  · rintro ⟨hnf, Ms0, hMs0_len, hMs0_rk, hW0_le⟩
    let pad : Matrix (J n) (J n) F2 →ₗ[F2] Matrix (J n ⊕ Fin f) (J n ⊕ Fin f) F2 :=
      { toFun := fun X => Matrix.fromBlocks X 0 0 0
        map_add' := fun X1 X2 => by ext i j; cases i <;> cases j <;> simp
        map_smul' := fun c X => by ext i j; cases i <;> cases j <;> simp }
    have hpad_rk : ∀ X, IsRankLe2G X → IsRankLe2G (pad X) := by
      rintro X ⟨u1, v1, u2, v2, rfl⟩
      refine ⟨Sum.elim u1 0, Sum.elim v1 0, Sum.elim u2 0, Sum.elim v2 0, ?_⟩
      ext i j; cases i <;> cases j <;> simp [pad, outerPairG]
    let eL : Fin n → (J n ⊕ Fin f → F2) := fun a => Pi.single (Sum.inl (Sum.inl a)) 1
    let eF : Fin f → (J n ⊕ Fin f → F2) := fun b => Pi.single (Sum.inr b) 1
    let EB : Fin n × Fin f → Matrix (J n ⊕ Fin f) (J n ⊕ Fin f) F2 :=
      fun ab => outerPairG (eL ab.1) (eF ab.2) (eF ab.2) (eL ab.1)
    let MsB : List (Matrix (J n ⊕ Fin f) (J n ⊕ Fin f) F2) :=
      (Finset.univ : Finset (Fin n × Fin f)).toList.map EB
    let Ms := Ms0.map pad ++ MsB
    refine ⟨Ms, ?_, ?_, ?_⟩
    · simp only [Ms, MsB, List.length_append, List.length_map, Finset.length_toList,
        card_univ, Fintype.card_prod, Fintype.card_fin]
      omega
    · intro M hM
      simp only [Ms, MsB, List.mem_append, List.mem_map, Finset.mem_toList, mem_univ, true_and] at hM
      rcases hM with ⟨X, hX, rfl⟩ | ⟨ab, rfl⟩
      · exact hpad_rk X (hMs0_rk X hX)
      · exact ⟨eL ab.1, eF ab.2, eF ab.2, eL ab.1, rfl⟩
    · rintro _ ⟨A, K, B, hA, hK, rfl⟩
      have hdecomp : blockZ A K B =
          pad (blockX A K) + ∑ ab : Fin n × Fin f, B ab.1 ab.2 • EB ab := by
        ext i j
        simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
          EB, outerPairG, Matrix.of_apply, eL, eF]
        cases i with
        | inl a =>
          cases j with
          | inl b =>
            have h0 : ∑ ab : Fin n × Fin f, B ab.1 ab.2 *
                ((Pi.single (Sum.inl (Sum.inl ab.1)) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inl a) *
                  (Pi.single (Sum.inr ab.2) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inl b) +
                (Pi.single (Sum.inr ab.2) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inl a) *
                  (Pi.single (Sum.inl (Sum.inl ab.1)) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inl b)) = 0 :=
              sum_eq_zero fun ab _ => by simp [Pi.single_apply]
            rw [h0, add_zero]; rfl
          | inr b =>
            cases a with
            | inl a0 =>
              have h1 : ∑ ab : Fin n × Fin f, B ab.1 ab.2 *
                  ((Pi.single (Sum.inl (Sum.inl ab.1)) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inl (Sum.inl a0)) *
                    (Pi.single (Sum.inr ab.2) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inr b) +
                  (Pi.single (Sum.inr ab.2) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inl (Sum.inl a0)) *
                    (Pi.single (Sum.inl (Sum.inl ab.1)) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inr b)) = B a0 b := by
                rw [sum_eq_single (a0, b)]
                · simp [Pi.single_apply]
                · intro ab _ hne
                  by_cases h1 : ab.1 = a0
                  · have h2 : ab.2 ≠ b := fun h => hne (Prod.ext h1 h)
                    simp [Pi.single_apply, h1, Ne.symm h2]
                  · simp [Pi.single_apply, Ne.symm h1]
                · intro h; exact absurd (mem_univ _) h
              rw [h1]; simp [blockZ, blockY, pad]
            | inr a0 =>
              have h0 : ∑ ab : Fin n × Fin f, B ab.1 ab.2 *
                  ((Pi.single (Sum.inl (Sum.inl ab.1)) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inl (Sum.inr a0)) *
                    (Pi.single (Sum.inr ab.2) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inr b) +
                  (Pi.single (Sum.inr ab.2) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inl (Sum.inr a0)) *
                    (Pi.single (Sum.inl (Sum.inl ab.1)) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inr b)) = 0 :=
                sum_eq_zero fun ab _ => by simp [Pi.single_apply]
              rw [h0]; simp [blockZ, blockY, pad]
        | inr a =>
          cases j with
          | inl b =>
            cases b with
            | inl b0 =>
              have h1 : ∑ ab : Fin n × Fin f, B ab.1 ab.2 *
                  ((Pi.single (Sum.inl (Sum.inl ab.1)) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inr a) *
                    (Pi.single (Sum.inr ab.2) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inl (Sum.inl b0)) +
                  (Pi.single (Sum.inr ab.2) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inr a) *
                    (Pi.single (Sum.inl (Sum.inl ab.1)) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inl (Sum.inl b0))) = B b0 a := by
                rw [sum_eq_single (b0, a)]
                · simp [Pi.single_apply]
                · intro ab _ hne
                  by_cases h1 : ab.1 = b0
                  · have h2 : ab.2 ≠ a := fun h => hne (Prod.ext h1 h)
                    simp [Pi.single_apply, h1, Ne.symm h2]
                  · simp [Pi.single_apply, Ne.symm h1]
                · intro h; exact absurd (mem_univ _) h
              rw [h1]; simp [blockZ, blockY, pad]
            | inr b0 =>
              have h0 : ∑ ab : Fin n × Fin f, B ab.1 ab.2 *
                  ((Pi.single (Sum.inl (Sum.inl ab.1)) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inr a) *
                    (Pi.single (Sum.inr ab.2) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inl (Sum.inr b0)) +
                  (Pi.single (Sum.inr ab.2) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inr a) *
                    (Pi.single (Sum.inl (Sum.inl ab.1)) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inl (Sum.inr b0))) = 0 :=
                sum_eq_zero fun ab _ => by simp [Pi.single_apply]
              rw [h0]; simp [blockZ, blockY, pad]
          | inr b =>
            have h0 : ∑ ab : Fin n × Fin f, B ab.1 ab.2 *
                ((Pi.single (Sum.inl (Sum.inl ab.1)) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inr a) *
                  (Pi.single (Sum.inr ab.2) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inr b) +
                (Pi.single (Sum.inr ab.2) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inr a) *
                  (Pi.single (Sum.inl (Sum.inl ab.1)) (1 : F2) : J n ⊕ Fin f → F2) (Sum.inr b)) = 0 :=
              sum_eq_zero fun ab _ => by simp [Pi.single_apply]
            rw [h0]; simp [blockZ, pad]
      rw [hdecomp]
      refine Submodule.add_mem _ ?_ ?_
      · have hX := hW0_le ⟨A, K, hA, hK, rfl⟩
        have hmap : pad (blockX A K) ∈ (Submodule.span F2 {X | X ∈ Ms0}).map pad :=
          Submodule.mem_map_of_mem hX
        rw [Submodule.map_span] at hmap
        have hle : Submodule.span F2 (pad '' {X | X ∈ Ms0}) ≤ Submodule.span F2 {M | M ∈ Ms} := by
          refine Submodule.span_mono ?_
          rintro _ ⟨X, hX', rfl⟩
          exact List.mem_append_left _ (List.mem_map.2 ⟨X, hX', rfl⟩)
        exact hle hmap
      · refine Submodule.sum_mem _ fun ab _ => Submodule.smul_mem _ _ ?_
        refine Submodule.subset_span (List.mem_append_right _ ?_)
        exact List.mem_map.2 ⟨ab, Finset.mem_toList.2 (mem_univ ab), rfl⟩

end Part1Padding

section Part2Cover

def orthSub {ι : Type*} [Fintype ι] (S : Submodule F2 (ι → F2)) : Submodule F2 (ι → F2) :=
  { carrier := {x | ∀ v ∈ S, dotProduct x v = 0}
    zero_mem' := fun v _ => by simp [dotProduct], add_mem' := fun hx hy v hv => by rw [add_dotProduct, hx v hv, hy v hv, add_zero]
    smul_mem' := fun c x hx v hv => by rw [smul_dotProduct, hx v hv, smul_zero] }

lemma finrank_orthSub {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Submodule F2 (ι → F2)) :
    Module.finrank F2 (orthSub S) + Module.finrank F2 S = Fintype.card ι := by
  let ev : (ι → F2) →ₗ[F2] (S →ₗ[F2] F2) :=
    { toFun := fun x =>
        { toFun := fun v => dotProduct x v.1
          map_add' := fun u v => dotProduct_add x u.1 v.1
          map_smul' := fun c v => by simp [dotProduct_smul] }
      map_add' := fun x y => by ext v; exact add_dotProduct x y v.1
      map_smul' := fun c x => by ext v; simp [smul_dotProduct] }
  have hker : LinearMap.ker ev = orthSub S := by
    ext x
    simp only [LinearMap.mem_ker, orthSub, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_setOf_eq, LinearMap.ext_iff, LinearMap.zero_apply]
    exact ⟨fun h v hv => h ⟨v, hv⟩, fun h ⟨v, hv⟩ => h v hv⟩
  have hsurj : Function.Surjective ev := by
    intro φ
    obtain ⟨T, hT⟩ := Submodule.exists_isCompl S
    let φ' : (ι → F2) →ₗ[F2] F2 :=
      φ.comp (Submodule.linearProjOfIsCompl S T hT)
    refine ⟨fun i => φ' (Pi.single i 1), ?_⟩
    ext ⟨v, hv⟩
    change dotProduct (fun i => φ' (Pi.single i 1)) v = φ ⟨v, hv⟩
    have hv_eq : v = ∑ i : ι, v i • Pi.single i (1 : F2) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    have h1 : φ' v = φ ⟨v, hv⟩ := by
      dsimp only [φ', LinearMap.comp_apply]
      exact congrArg φ (Submodule.linearProjOfIsCompl_apply_left hT ⟨v, hv⟩)
    rw [← h1]
    conv_rhs => rw [hv_eq]
    rw [map_sum]
    simp only [dotProduct, map_smul, smul_eq_mul]
    exact sum_congr rfl fun i _ => mul_comm _ _
  have hrange : LinearMap.range ev = ⊤ := LinearMap.range_eq_top.2 hsurj
  have hrn := LinearMap.finrank_range_add_finrank_ker ev
  rw [hrange, hker, finrank_top, Module.finrank_fintype_fun_eq_card,
    Subspace.dual_finrank_eq] at hrn
  omega

lemma orthSub_orthSub {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Submodule F2 (ι → F2)) :
    orthSub (orthSub S) = S := by
  have hle : S ≤ orthSub (orthSub S) := by
    intro v hv x hx
    rw [dotProduct_comm]
    exact hx v hv
  have h1 := finrank_orthSub S
  have h2 := finrank_orthSub (orthSub S)
  exact (Submodule.eq_of_le_of_finrank_le hle (by omega)).symm

lemma alt_quad_zero {n : ℕ} {K : Matrix (Fin n) (Fin n) F2} (hK : altM K) (x : Fin n → F2) :
    dotProduct (x ᵥ* K) x = 0 := by
  let f : Fin n × Fin n → F2 := fun p => x p.2 * K p.2 p.1 * x p.1
  have hsum_eq : dotProduct (x ᵥ* K) x = ∑ p : Fin n × Fin n, f p := by
    simp only [dotProduct, Matrix.vecMul, Finset.sum_mul, f]
    exact (Fintype.sum_prod_type (fun p : Fin n × Fin n => x p.2 * K p.2 p.1 * x p.1)).symm
  have hsymm : ∀ p : Fin n × Fin n, f (p.2, p.1) = f p := fun p => by
    dsimp only [f]
    have hKsym : K p.1 p.2 = K p.2 p.1 := congrFun (congrFun hK.1 p.2) p.1
    rw [hKsym]; ring
  let Slt := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1.val < p.2.val)
  let Sgt := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.2.val < p.1.val)
  let Seq := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1.val = p.2.val)
  have hpart : (Finset.univ : Finset (Fin n × Fin n)) = Seq ∪ (Slt ∪ Sgt) := by
    ext p; simp only [Seq, Slt, Sgt, mem_union, mem_filter, mem_univ, true_and, true_iff]; omega
  have hd1 : Disjoint Seq (Slt ∪ Sgt) := by
    rw [disjoint_left]; intro p h1 h2
    simp only [Seq, Slt, Sgt, mem_union, mem_filter, mem_univ, true_and] at h1 h2; omega
  have hd2 : Disjoint Slt Sgt := by
    rw [disjoint_left]; intro p h1 h2
    simp only [Slt, Sgt, mem_filter, mem_univ, true_and] at h1 h2; omega
  rw [hsum_eq, hpart, sum_union hd1, sum_union hd2]
  have hSeq : ∑ p ∈ Seq, f p = 0 := sum_eq_zero fun p hp => by
    have heq : p.1 = p.2 := Fin.ext (mem_filter.1 hp).2
    simp [f, heq, hK.2 p.2]
  have hSgt : ∑ p ∈ Sgt, f p = ∑ p ∈ Slt, f p := by
    refine sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp; exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hp).2⟩
    · intro p1 _ p2 _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro p hp; exact ⟨(p.2, p.1), mem_filter.2 ⟨mem_univ _, (mem_filter.1 hp).2⟩, rfl⟩
    · intro p _; exact (hsymm p).symm
  rw [hSeq, zero_add, hSgt, f2_add_self]

lemma alt_rank_one_in_sub {n : ℕ} {K : Matrix (Fin n) (Fin n) F2} (hK : altM K)
    (A : Submodule F2 (Fin n → F2))
    (hrk : Module.finrank F2 (LinearMap.range ((Matrix.vecMulLinear K).domRestrict (orthSub A))) = 1) :
    ∃ v ∈ A, ∀ t ∈ orthSub A, t ᵥ* K = 0 ∨ t ᵥ* K = v := by
  classical
  let R := LinearMap.range ((Matrix.vecMulLinear K).domRestrict (orthSub A))
  have hrkR : Module.finrank F2 R = 1 := hrk
  have hne_bot : R ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at hrkR; omega
  obtain ⟨v, hvR, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
  have hspan : Submodule.span F2 {v} = R := by
    have hle : Submodule.span F2 {v} ≤ R := Submodule.span_le.2 (by simpa using hvR)
    have h1 : Module.finrank F2 (Submodule.span F2 {v}) = 1 := finrank_span_singleton hv_ne
    exact Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hmem_or : ∀ w ∈ R, w = 0 ∨ w = v := by
    intro w hw
    rw [← hspan, Submodule.mem_span_singleton] at hw
    obtain ⟨c, rfl⟩ := hw
    fin_cases c
    · left; change (0 : F2) • v = 0; simp
    · right; change (1 : F2) • v = v; simp
  have hv_all : ∀ t ∈ orthSub A, t ᵥ* K = 0 ∨ t ᵥ* K = v := fun t ht =>
    hmem_or (t ᵥ* K) ⟨⟨t, ht⟩, rfl⟩
  have hv_in_A : v ∈ A := by
    rw [← orthSub_orthSub A]
    intro t ht
    obtain ⟨⟨t0, ht0⟩, ht0v⟩ := hvR
    have ht0v' : t0 ᵥ* K = v := ht0v
    rw [← ht0v']
    rcases hv_all t ht with h0 | hv'
    · have hsym : dotProduct (t0 ᵥ* K) t = dotProduct (t ᵥ* K) t0 := by
        simp only [dotProduct, Matrix.vecMul, Finset.sum_mul, Finset.mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        have hKsym : K j i = K i j := congrFun (congrFun hK.1 i) j
        rw [hKsym]; ring
      rw [hsym, h0, zero_dotProduct]
    · have hsum : (t0 + t) ᵥ* K = 0 := by
        rw [Matrix.add_vecMul, ht0v', hv']
        funext j; exact f2_add_self (v j)
      have h0 : dotProduct ((t0 + t) ᵥ* K) t = 0 := by rw [hsum, zero_dotProduct]
      rw [Matrix.add_vecMul, add_dotProduct, alt_quad_zero hK t, add_zero] at h0
      exact h0
  exact ⟨v, hv_in_A, hv_all⟩

def topSlice {n : ℕ} (V : Submodule F2 (J n → F2)) : Submodule F2 (Fin n → F2) :=
  { carrier := {t | Sum.elim t (0 : Fin n → F2) ∈ V}
    zero_mem' := by
      change Sum.elim (0 : Fin n → F2) (0 : Fin n → F2) ∈ V
      have h : Sum.elim (0 : Fin n → F2) (0 : Fin n → F2) = 0 := by funext i; cases i <;> rfl
      rw [h]; exact V.zero_mem, add_mem' := fun {a b} hx hy => by
      change Sum.elim (a + b) (0 : Fin n → F2) ∈ V
      have h : Sum.elim (a + b) (0 : Fin n → F2) = Sum.elim a 0 + Sum.elim b 0 := by
        funext i; cases i <;> simp
      rw [h]; exact V.add_mem hx hy
    smul_mem' := fun c {a} hx => by
      change Sum.elim (c • a) (0 : Fin n → F2) ∈ V
      have h : Sum.elim (c • a) (0 : Fin n → F2) = c • Sum.elim a 0 := by
        funext i; cases i <;> simp
      rw [h]; exact V.smul_mem c hx }

def botProjLM {n : ℕ} (V : Submodule F2 (J n → F2)) : V →ₗ[F2] (Fin n → F2) :=
  { toFun := fun v => fun i => v.1 (Sum.inr i)
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

def botProj {n : ℕ} (V : Submodule F2 (J n → F2)) : Submodule F2 (Fin n → F2) :=
  LinearMap.range (botProjLM V)

lemma flag_criterion_one {n : ℕ} (V : Submodule F2 (J n → F2))
    {A K : Matrix (Fin n) (Fin n) F2} (hK : altM K)
    (hrank2 : Module.finrank F2 (LinearMap.range ((Matrix.vecMulLinear (blockX A K)).domRestrict (orthSub V))) ≤ 2) :
    ∀ x ∈ orthSub (topSlice V ⊔ botProj V), ∀ y ∈ orthSub (topSlice V ⊓ botProj V),
      dotProduct (x ᵥ* K) y = 0 := by
  classical
  let A0 := topSlice V
  let A1 := botProj V
  let R := LinearMap.range ((Matrix.vecMulLinear (blockX A K)).domRestrict (orthSub V))
  let ρ : R →ₗ[F2] (Fin n → F2) :=
    { toFun := fun r => fun j => r.1 (Sum.inr j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let R1 := LinearMap.range ((Matrix.vecMulLinear K).domRestrict (orthSub A1))
  let R0 := LinearMap.range ((Matrix.vecMulLinear K).domRestrict (orthSub A0))
  have h1_le : Module.finrank F2 R1 ≤ Module.finrank F2 (LinearMap.ker ρ) := by
    let emb : R1 →ₗ[F2] LinearMap.ker ρ :=
      { toFun := fun w => ⟨⟨Sum.elim w.1 0, by
          obtain ⟨⟨u, hu⟩, hw⟩ := w.2
          have huV : Sum.elim (0 : Fin n → F2) u ∈ orthSub V := by
            intro v hv
            have hv1 : (fun i => v (Sum.inr i)) ∈ A1 := ⟨⟨v, hv⟩, rfl⟩
            have h0 := hu _ hv1
            simpa [dotProduct, Fintype.sum_sum_type] using h0
          refine ⟨⟨Sum.elim 0 u, huV⟩, ?_⟩
          ext j
          cases j with
          | inl j0 =>
            have hwj := congrFun hw j0
            simpa [Matrix.vecMul, dotProduct, blockX, Fintype.sum_sum_type] using hwj
          | inr j0 =>
            simp [Matrix.vecMul, dotProduct, blockX, Fintype.sum_sum_type]⟩, rfl⟩
        map_add' := fun a b => by
          apply Subtype.ext; apply Subtype.ext; funext i; cases i <;> simp
        map_smul' := fun c a => by
          apply Subtype.ext; apply Subtype.ext; funext i; cases i <;> simp }
    have hinj : Function.Injective emb := by
      intro a b h
      apply Subtype.ext; funext i
      have := congrFun (congrArg (fun z => z.1.1) h) (Sum.inl i)
      simpa [emb] using this
    exact LinearMap.finrank_le_finrank_of_injective hinj
  have h0_le : Module.finrank F2 R0 ≤ Module.finrank F2 (LinearMap.range ρ) := by
    have hsub : R0 ≤ LinearMap.range ρ := by
      rintro w ⟨⟨t, ht⟩, rfl⟩
      let πB := botProjLM V
      let φ : V →ₗ[F2] F2 :=
        { toFun := fun v => dotProduct t (fun i => v.1 (Sum.inl i))
          map_add' := fun u v => dotProduct_add t _ _
          map_smul' := fun c v => by
            change dotProduct t (c • fun i => v.1 (Sum.inl i)) = c * dotProduct t (fun i => v.1 (Sum.inl i))
            simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
            exact sum_congr rfl fun i _ => by ring }
      have hker_le : LinearMap.ker πB ≤ LinearMap.ker φ := by
        intro v hv
        have hv0 : (fun i => v.1 (Sum.inl i)) ∈ A0 := by
          change Sum.elim (fun i => v.1 (Sum.inl i)) (0 : Fin n → F2) ∈ V
          have heq : Sum.elim (fun i => v.1 (Sum.inl i)) (0 : Fin n → F2) = v.1 := by
            funext i
            cases i with
            | inl a => rfl
            | inr b => exact (congrFun hv b).symm
          rw [heq]; exact v.2
        exact ht _ hv0
      obtain ⟨T, hT⟩ := Submodule.exists_isCompl A1
      let ψA1 : A1 →ₗ[F2] F2 :=
        { toFun := fun a => φ (Classical.choose a.2)
          map_add' := fun a b => by
            have ha : πB (Classical.choose a.2) = a.1 := Classical.choose_spec a.2
            have hb : πB (Classical.choose b.2) = b.1 := Classical.choose_spec b.2
            have hab : πB (Classical.choose (a + b).2) = a.1 + b.1 := Classical.choose_spec (a + b).2
            have hdiff : Classical.choose (a + b).2 - (Classical.choose a.2 + Classical.choose b.2) ∈ LinearMap.ker πB := by
              change πB _ = 0
              rw [map_sub, map_add, hab, ha, hb, sub_self]
            have h0 := hker_le hdiff
            change φ _ = 0 at h0
            rw [map_sub, map_add, sub_eq_zero] at h0
            exact h0
          map_smul' := fun c a => by
            have ha : πB (Classical.choose a.2) = a.1 := Classical.choose_spec a.2
            have hca : πB (Classical.choose (c • a).2) = c • a.1 := Classical.choose_spec (c • a).2
            have hdiff : Classical.choose (c • a).2 - c • Classical.choose a.2 ∈ LinearMap.ker πB := by
              change πB _ = 0
              rw [map_sub, map_smul, hca, ha, sub_self]
            have h0 := hker_le hdiff
            change φ _ = 0 at h0
            rw [map_sub, map_smul, sub_eq_zero] at h0
            exact h0 }
      let ψ : (Fin n → F2) →ₗ[F2] F2 := ψA1.comp (Submodule.linearProjOfIsCompl A1 T hT)
      let b : Fin n → F2 := fun i => ψ (Pi.single i 1)
      have htbV : Sum.elim t b ∈ orthSub V := by
        intro v hv
        have hb_val : dotProduct b (fun i => v (Sum.inr i)) = dotProduct t (fun i => v (Sum.inl i)) := by
          have hv_eq : (fun i => v (Sum.inr i)) = ∑ i : Fin n, v (Sum.inr i) • Pi.single i (1 : F2) := by
            funext j; simp [Finset.sum_apply, Pi.single_apply]
          have h1 : dotProduct b (fun i => v (Sum.inr i)) = ψ (fun i => v (Sum.inr i)) := by
            conv_rhs => rw [hv_eq]
            rw [map_sum]
            simp only [dotProduct, b, map_smul, smul_eq_mul]
            exact sum_congr rfl fun i _ => mul_comm _ _
          rw [h1]
          have hmem : (fun i => v (Sum.inr i)) ∈ A1 := ⟨⟨v, hv⟩, rfl⟩
          have hproj : ψ (fun i => v (Sum.inr i)) = ψA1 ⟨_, hmem⟩ :=
            congrArg ψA1 (Submodule.linearProjOfIsCompl_apply_left hT ⟨_, hmem⟩)
          rw [hproj]
          dsimp only [ψA1, LinearMap.coe_mk, AddHom.coe_mk]
          have hspec := Classical.choose_spec hmem
          have hdiff : Classical.choose hmem - ⟨v, hv⟩ ∈ LinearMap.ker πB := by
            change πB _ = 0
            rw [map_sub, hspec]; exact sub_self _
          have h0 := hker_le hdiff
          change φ _ = 0 at h0
          rw [map_sub, sub_eq_zero] at h0
          exact h0
        change dotProduct (Sum.elim t b) v = 0
        rw [dotProduct, Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
        change dotProduct t (fun i => v (Sum.inl i)) + dotProduct b (fun i => v (Sum.inr i)) = 0
        rw [hb_val, f2_add_self]
      refine ⟨⟨Sum.elim t b ᵥ* blockX A K, ⟨⟨Sum.elim t b, htbV⟩, rfl⟩⟩, ?_⟩
      funext j
      simp only [ρ, LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMul, dotProduct, blockX,
        Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero, sum_const_zero, add_zero]
      rfl
    exact Submodule.finrank_mono hsub
  have hrn := LinearMap.finrank_range_add_finrank_ker ρ
  have hrkR : Module.finrank F2 R ≤ 2 := hrank2
  have hsum_le : Module.finrank F2 R0 + Module.finrank F2 R1 ≤ 2 := by omega
  intro x hx y hy
  have hx0 : x ∈ orthSub A0 := fun v hv => hx v (Submodule.mem_sup_left hv)
  have hx1 : x ∈ orthSub A1 := fun v hv => hx v (Submodule.mem_sup_right hv)
  by_cases hr0 : Module.finrank F2 R0 = 0
  · have hbot : R0 = ⊥ := Submodule.finrank_eq_zero.1 hr0
    have h0 : x ᵥ* K = 0 := (Submodule.mem_bot F2).1 (hbot ▸ ⟨⟨x, hx0⟩, rfl⟩)
    rw [h0, zero_dotProduct]
  · by_cases hr1 : Module.finrank F2 R1 = 0
    · have hbot : R1 = ⊥ := Submodule.finrank_eq_zero.1 hr1
      have h0 : x ᵥ* K = 0 := (Submodule.mem_bot F2).1 (hbot ▸ ⟨⟨x, hx1⟩, rfl⟩)
      rw [h0, zero_dotProduct]
    · have h0_eq : Module.finrank F2 R0 = 1 := by omega
      have h1_eq : Module.finrank F2 R1 = 1 := by omega
      obtain ⟨v0, hv0A, hv0_all⟩ := alt_rank_one_in_sub hK A0 h0_eq
      obtain ⟨v1, hv1A, hv1_all⟩ := alt_rank_one_in_sub hK A1 h1_eq
      rcases hv0_all x hx0 with h0 | heq0
      · rw [h0, zero_dotProduct]
      · rcases hv1_all x hx1 with h1 | heq1
        · rw [h1, zero_dotProduct]
        · have hv_eq : v0 = v1 := heq0.symm.trans heq1
          have hv_in : v0 ∈ A0 ⊓ A1 := ⟨hv0A, hv_eq ▸ hv1A⟩
          rw [heq0, dotProduct_comm]
          exact hy v0 hv_in

lemma extend_pivot_set {n : ℕ} (F : Submodule F2 (Fin n → F2)) (P0 : Finset (Fin n))
    (hli0 : LinearIndependent F2 (fun i : P0 =>
      ({ toFun := fun v : F => v.1 i.1
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl } : F →ₗ[F2] F2))) :
    ∃ P : Finset (Fin n), P0 ⊆ P ∧ P.card = Module.finrank F2 F ∧
      ∀ i ∉ P, ∃ x ∈ orthSub F, x i = 1 ∧ ∀ j, x j ≠ 0 → j = i ∨ j ∈ P := by
  classical
  let ev : Fin n → (F →ₗ[F2] F2) := fun i =>
    { toFun := fun v => v.1 i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hstep : ∀ (S : Finset (Fin n)) (Q : Finset (Fin n)),
      LinearIndependent F2 (fun i : Q => ev i.1) →
      ∃ P : Finset (Fin n), Q ⊆ P ∧ LinearIndependent F2 (fun i : P => ev i.1) ∧
        ∀ i ∈ S, ev i ∈ Submodule.span F2 (ev '' (P : Set (Fin n))) := by
    intro S
    induction S using Finset.induction with
    | empty =>
      intro Q hQ
      exact ⟨Q, Subset.rfl, hQ, fun _ h => absurd h (notMem_empty _)⟩
    | @insert a S ha ih =>
      intro Q hQ
      obtain ⟨P1, hQP1, hli1, hsp1⟩ := ih Q hQ
      by_cases hmem : ev a ∈ Submodule.span F2 (ev '' (P1 : Set (Fin n)))
      · refine ⟨P1, hQP1, hli1, fun i hi => ?_⟩
        rcases mem_insert.1 hi with rfl | hiS
        · exact hmem
        · exact hsp1 i hiS
      · have ha_not : a ∉ P1 := fun h => hmem (Submodule.subset_span ⟨a, h, rfl⟩)
        let P2 := insert a P1
        have hli2 : LinearIndependent F2 (fun i : P2 => ev i.1) := by
          rw [Fintype.linearIndependent_iff]
          intro c hc
          have hsplit := add_sum_erase (s := (Finset.univ : Finset P2))
            (f := fun i : P2 => c i • ev i.1) (mem_univ ⟨a, mem_insert_self a P1⟩)
          rw [hc] at hsplit
          have hca0 : c ⟨a, mem_insert_self a P1⟩ = 0 := by
            by_contra hne
            have hc1 : c ⟨a, mem_insert_self a P1⟩ = 1 := f2_eq_one_of_ne_zero hne
            rw [hc1, one_smul] at hsplit
            have heva : ev a = ∑ x ∈ (Finset.univ : Finset P2).erase ⟨a, mem_insert_self a P1⟩, c x • ev x.1 := by
              have h2 := congrArg (fun z => ev a + z) hsplit
              dsimp only at h2
              rw [← add_assoc, show ev a + ev a = 0 from by
                ext v; exact f2_add_self (v.1 a), zero_add, add_zero] at h2
              exact h2.symm
            apply hmem
            rw [heva]
            refine Submodule.sum_mem _ fun x hx => Submodule.smul_mem _ _ ?_
            have hx_ne : x.1 ≠ a := fun h => (mem_erase.1 hx).1 (Subtype.ext h)
            have hx_P1 : x.1 ∈ P1 := (mem_insert.1 x.2).resolve_left hx_ne
            exact Submodule.subset_span ⟨x.1, hx_P1, rfl⟩
          rw [hca0, zero_smul, zero_add] at hsplit
          let c1 : P1 → F2 := fun y => c ⟨y.1, mem_insert_of_mem y.2⟩
          have hc1_sum : ∑ y : P1, c1 y • ev y.1 = 0 := by
            rw [← hsplit]
            refine sum_bij (fun y _ => (⟨y.1, mem_insert_of_mem y.2⟩ : P2)) ?_ ?_ ?_ ?_
            · intro y _
              refine mem_erase.2 ⟨fun h => ha_not (by
                have h' : y.1 = a := congrArg (Subtype.val : P2 → Fin n) h
                exact h' ▸ y.2), mem_univ _⟩
            · intro y1 _ y2 _ h
              exact Subtype.ext (congrArg (Subtype.val : P2 → Fin n) h)
            · intro x hx
              have hx_ne : x.1 ≠ a := fun h => (mem_erase.1 hx).1 (Subtype.ext h)
              have hx_P1 : x.1 ∈ P1 := (mem_insert.1 x.2).resolve_left hx_ne
              exact ⟨⟨x.1, hx_P1⟩, mem_univ _, Subtype.ext rfl⟩
            · intro y _; rfl
          have hc1_0 := Fintype.linearIndependent_iff.1 hli1 c1 hc1_sum
          intro x
          by_cases hxa : x.1 = a
          · convert hca0 using 1; congr 1; exact Subtype.ext hxa
          · exact hc1_0 ⟨x.1, (mem_insert.1 x.2).resolve_left hxa⟩
        refine ⟨P2, Subset.trans hQP1 (subset_insert a P1), hli2, fun i hi => ?_⟩
        rcases mem_insert.1 hi with hia | hiS
        · rw [hia]; exact Submodule.subset_span ⟨a, mem_insert_self a P1, rfl⟩
        · exact Submodule.span_mono (Set.image_mono (subset_insert a P1)) (hsp1 i hiS)
  obtain ⟨P, hP0, hliP, hspAll⟩ := hstep Finset.univ P0 hli0
  have hsp_top : Submodule.span F2 (Set.range fun i : P => ev i.1) = ⊤ := by
    rw [eq_top_iff]
    intro φ _
    obtain ⟨T, hT⟩ := Submodule.exists_isCompl F
    let φ' : (Fin n → F2) →ₗ[F2] F2 := φ.comp (Submodule.linearProjOfIsCompl F T hT)
    have hφ_eq : φ = ∑ i : Fin n, φ' (Pi.single i 1) • ev i := by
      ext ⟨v, hv⟩
      have hv_eq : v = ∑ i : Fin n, v i • Pi.single i (1 : F2) := by
        funext j; simp [Finset.sum_apply, Pi.single_apply]
      have h1 : φ' v = φ ⟨v, hv⟩ :=
        congrArg φ (Submodule.linearProjOfIsCompl_apply_left hT ⟨v, hv⟩)
      rw [← h1]
      conv_lhs => rw [hv_eq]
      rw [map_sum]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, ev,
        LinearMap.coe_mk, AddHom.coe_mk, map_smul, smul_eq_mul]
      exact sum_congr rfl fun i _ => mul_comm _ _
    rw [hφ_eq]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have hmem := hspAll i (mem_univ i)
    rwa [show ev '' (P : Set (Fin n)) = Set.range (fun j : P => ev j.1) from by
      ext f; simp] at hmem
  have hcard : P.card = Module.finrank F2 F := by
    have hle1 : P.card ≤ Module.finrank F2 (F →ₗ[F2] F2) := by
      simpa using hliP.fintype_card_le_finrank
    have hge1 : Module.finrank F2 (F →ₗ[F2] F2) ≤ P.card := by
      have hrange : LinearMap.range (Fintype.linearCombination F2 (fun j : P => ev j.1)) = ⊤ := by
        rw [Fintype.range_linearCombination, hsp_top]
      calc Module.finrank F2 (F →ₗ[F2] F2)
          = Module.finrank F2 (LinearMap.range (Fintype.linearCombination F2 (fun j : P => ev j.1))) := by
              rw [hrange, finrank_top]
        _ ≤ Module.finrank F2 (P → F2) := LinearMap.finrank_range_le _
        _ = P.card := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
    rw [Subspace.dual_finrank_eq] at hle1 hge1
    omega
  refine ⟨P, hP0, hcard, fun i hi => ?_⟩
  have hmem := hspAll i (mem_univ i)
  rw [show ev '' (P : Set (Fin n)) = Set.range (fun j : P => ev j.1) from by ext f; simp,
    ← Fintype.range_linearCombination] at hmem
  obtain ⟨c, hc⟩ := hmem
  let x : Fin n → F2 := fun j =>
    if j = i then 1 else if hj : j ∈ P then c ⟨j, hj⟩ else 0
  refine ⟨x, ?_, by simp [x], ?_⟩
  · intro v hv
    have hev_i : v i = ∑ j : P, c j * v j.1 := by
      have := congrArg (fun f : F →ₗ[F2] F2 => f ⟨v, hv⟩) hc
      simp only [Fintype.linearCombination_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, ev, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul] at this
      exact this.symm
    change dotProduct x v = 0
    rw [dotProduct]
    have hsum_P : ∑ j ∈ P, x j * v j = ∑ j : P, c j * v j.1 := by
      rw [← Finset.sum_attach P]
      refine sum_congr rfl fun j _ => ?_
      have hne : j.1 ≠ i := fun h => hi (h ▸ j.2)
      simp [x, hne, j.2]
    have hsub_u : insert i P ⊆ Finset.univ := subset_univ _
    rw [← sum_subset hsub_u]
    · rw [sum_insert hi, hsum_P]
      have hxi : x i = 1 := by simp [x]
      rw [hxi, one_mul, hev_i, f2_add_self]
    · intro j _ hj_not
      simp only [mem_insert, not_or] at hj_not
      simp [x, hj_not.1, hj_not.2]
  · intro j hxj
    by_cases h1 : j = i
    · left; exact h1
    · by_cases h2 : j ∈ P
      · right; exact h2
      · exfalso; apply hxj; simp [x, h1, h2]

lemma part2_cover_zero {n : ℕ} (edges : Finset (Fin n × Fin n)) (hedges : ∀ p ∈ edges, p.1 < p.2)
    (t0 : ℕ) (hbank : bankProp edges 0 t0) :
    Nat.choose n 2 + edges.card ≤ t0 ∧
    ∃ w : Fin n → Fin 3,
      (∀ p ∈ edges, 2 ≤ (w p.1).val + (w p.2).val) ∧
      (∑ i : Fin n, (w i).val) ≤ 2 * (t0 - (Nat.choose n 2 + edges.card)) := by
  classical
  obtain ⟨Ms, hMs_len, hMs_rk, hW0_le⟩ := (bankProp0_iff_span edges t0).1 hbank
  let U := Submodule.span F2 {M | M ∈ Ms}
  have hU_rank : Module.finrank F2 U ≤ t0 := by
    have hrange : LinearMap.range (Fintype.linearCombination F2 (fun i : Fin Ms.length => Ms.get i)) = U := by
      rw [Fintype.range_linearCombination]
      congr 1; ext M; simp [List.mem_iff_get]
    have h1 : Module.finrank F2 U ≤ Ms.length := by
      rw [← hrange]
      calc Module.finrank F2 _ ≤ Module.finrank F2 (Fin Ms.length → F2) := LinearMap.finrank_range_le _
        _ = Ms.length := Module.finrank_fin_fun F2
    exact le_trans h1 hMs_len
  have hD0_eq : Module.finrank F2 (W0 edges) = Nat.choose n 2 + edges.card := finrank_W0 edges hedges
  have hD0_le_U : Module.finrank F2 (W0 edges) ≤ Module.finrank F2 U := Submodule.finrank_mono hW0_le
  have hD0_le : Nat.choose n 2 + edges.card ≤ t0 := by omega
  let q := (W0 edges).mkQ
  obtain ⟨Lq, hLq_sub, hLq_span, hLq_li, hLq_len⟩ := exists_sublist_span_li (Ms.map q)
  have hqU_span : Submodule.span F2 {x | x ∈ Ms.map q} = U.map q := by
    rw [Submodule.map_span]
    congr 1; ext y; simp
  have hqU_rank : Module.finrank F2 (U.map q) + Module.finrank F2 (W0 edges) = Module.finrank F2 U := by
    let qU := q.domRestrict U
    have hrg : LinearMap.range qU = U.map q := by
      ext y; simp [qU, LinearMap.mem_range, Submodule.mem_map]
    have hker_eq : Module.finrank F2 (LinearMap.ker qU) = Module.finrank F2 (W0 edges) := by
      let emb : W0 edges →ₗ[F2] LinearMap.ker qU :=
        { toFun := fun x => ⟨⟨x.1, hW0_le x.2⟩, by
            change q x.1 = 0; exact (Submodule.Quotient.mk_eq_zero _).2 x.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hinj : Function.Injective emb := fun a b h =>
        Subtype.ext (congrArg (fun z => z.1.1) h)
      have hsurj : Function.Surjective emb := by
        rintro ⟨⟨x, hxU⟩, hxker⟩
        have hxW : x ∈ W0 edges := (Submodule.Quotient.mk_eq_zero _).1 hxker
        exact ⟨⟨x, hxW⟩, rfl⟩
      exact (LinearEquiv.ofBijective emb ⟨hinj, hsurj⟩).finrank_eq.symm
    have hrn := LinearMap.finrank_range_add_finrank_ker qU
    rw [hrg, hker_eq] at hrn
    exact hrn
  have hLq_le_k : Lq.length ≤ t0 - (Nat.choose n 2 + edges.card) := by
    rw [hqU_span] at hLq_len; omega
  have hlift : ∀ i : Fin Lq.length, ∃ G ∈ Ms, q G = Lq.get i := fun i =>
    List.mem_map.1 (hLq_sub (Lq.get i) (List.get_mem Lq i))
  choose gFun hgMem hgQ using hlift
  let Gs : List (Matrix (J n) (J n) F2) := List.ofFn gFun
  have hGs_len : Gs.length = Lq.length := List.length_ofFn
  let SGs := Submodule.span F2 {G | G ∈ Gs}
  have hdisj : W0 edges ⊓ SGs = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hxW, hxG⟩
    have hrange : LinearMap.range (Fintype.linearCombination F2 gFun) = SGs := by
      rw [Fintype.range_linearCombination]
      congr 1; ext G; simp [Gs, List.mem_ofFn]
    rw [← hrange] at hxG
    obtain ⟨c, rfl⟩ := hxG
    have hq0 : ∑ i : Fin Lq.length, c i • Lq.get i = 0 := by
      have h1 : q (Fintype.linearCombination F2 gFun c) = 0 := (Submodule.Quotient.mk_eq_zero _).2 hxW
      rw [Fintype.linearCombination_apply, map_sum] at h1
      simpa [map_smul, hgQ] using h1
    have hc0 := Fintype.linearIndependent_iff.1 hLq_li c hq0
    rw [Fintype.linearCombination_apply]
    exact sum_eq_zero fun i _ => by rw [hc0 i, zero_smul]
  have hU_le_sup : U ≤ W0 edges ⊔ SGs := by
    rw [Submodule.span_le]
    intro M hM
    have hqM : q M ∈ Submodule.span F2 {x | x ∈ Lq} := by
      rw [hLq_span]; exact Submodule.subset_span (List.mem_map.2 ⟨M, hM, rfl⟩)
    have hrange : LinearMap.range (Fintype.linearCombination F2 (fun i : Fin Lq.length => Lq.get i)) =
        Submodule.span F2 {x | x ∈ Lq} := by
      rw [Fintype.range_linearCombination]
      congr 1; ext x; simp [List.mem_iff_get]
    rw [← hrange] at hqM
    obtain ⟨c, hc⟩ := hqM
    let MG := Fintype.linearCombination F2 gFun c
    have hMG_mem : MG ∈ SGs := by
      dsimp only [MG]
      rw [Fintype.linearCombination_apply]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span (by simp [Gs, List.mem_ofFn]))
    have hdiff_W : M - MG ∈ W0 edges := by
      rw [← Submodule.Quotient.mk_eq_zero]
      change q (M - MG) = 0
      rw [map_sub]
      dsimp only [MG]
      rw [Fintype.linearCombination_apply, map_sum]
      simp only [map_smul, hgQ]
      rw [← Fintype.linearCombination_apply, hc, sub_self]
    have heq : M = (M - MG) + MG := by abel
    rw [heq]
    exact Submodule.add_mem_sup hdiff_W hMG_mem
  have hpickG : ∀ i : Fin Lq.length, ∃ u1 v1 u2 v2 : J n → F2, gFun i = outerPairG u1 v1 u2 v2 :=
    fun i => hMs_rk (gFun i) (hgMem i)
  choose u1G v1G u2G v2G hG_eq using hpickG
  let colList : List (J n → F2) := List.ofFn u1G ++ List.ofFn u2G
  let V : Submodule F2 (J n → F2) := Submodule.span F2 {v | v ∈ colList}
  have hV_rank : Module.finrank F2 V ≤ 2 * (t0 - (Nat.choose n 2 + edges.card)) := by
    have hrange : LinearMap.range (Fintype.linearCombination F2 (fun i : Fin colList.length => colList.get i)) = V := by
      rw [Fintype.range_linearCombination]
      congr 1; ext v; simp [List.mem_iff_get]
    have h1 : Module.finrank F2 V ≤ colList.length := by
      rw [← hrange]
      calc Module.finrank F2 _ ≤ Module.finrank F2 (Fin colList.length → F2) := LinearMap.finrank_range_le _
        _ = colList.length := Module.finrank_fin_fun F2
    have h2 : colList.length = 2 * Lq.length := by
      simp [colList, List.length_append, List.length_ofFn]; ring
    omega
  have hMG_kill : ∀ MG ∈ SGs, ∀ x ∈ orthSub V, x ᵥ* MG = 0 := by
    intro MG hMG
    refine Submodule.span_induction
      (p := fun A _ => ∀ x ∈ orthSub V, x ᵥ* A = 0) ?_ ?_ ?_ ?_ hMG
    · rintro A hA x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hA
      rw [hG_eq i]
      have h1 : dotProduct x (u1G i) = 0 := hx (u1G i) (Submodule.subset_span
        (List.mem_append_left _ (List.mem_ofFn.2 ⟨i, rfl⟩)))
      have h2 : dotProduct x (u2G i) = 0 := hx (u2G i) (Submodule.subset_span
        (List.mem_append_right _ (List.mem_ofFn.2 ⟨i, rfl⟩)))
      funext j
      simp only [Matrix.vecMul, dotProduct, outerPairG, Matrix.of_apply, mul_add, sum_add_distrib,
        Pi.zero_apply]
      have s1 : ∑ k : J n, x k * (u1G i k * v1G i j) = (∑ k : J n, x k * u1G i k) * v1G i j := by
        rw [Finset.sum_mul]; refine sum_congr rfl fun k _ => by ring
      have s2 : ∑ k : J n, x k * (u2G i k * v2G i j) = (∑ k : J n, x k * u2G i k) * v2G i j := by
        rw [Finset.sum_mul]; refine sum_congr rfl fun k _ => by ring
      rw [s1, s2]
      change dotProduct x (u1G i) * v1G i j + dotProduct x (u2G i) * v2G i j = 0
      rw [h1, h2]; simp
    · intro x _; simp
    · intro A B _ _ hA hB x hx; rw [Matrix.vecMul_add, hA x hx, hB x hx, add_zero]
    · intro c A _ hA x hx; rw [Matrix.vecMul_smul, hA x hx, smul_zero]
  let A0 := topSlice V
  let πB := botProjLM V
  let A1 := botProj V
  have hA0_A1_rank : Module.finrank F2 A0 + Module.finrank F2 A1 = Module.finrank F2 V := by
    have hker : Module.finrank F2 (LinearMap.ker πB) = Module.finrank F2 A0 := by
      let emb : A0 →ₗ[F2] LinearMap.ker πB :=
        { toFun := fun t => ⟨⟨Sum.elim t.1 0, t.2⟩, rfl⟩
          map_add' := fun a b => by apply Subtype.ext; apply Subtype.ext; funext i; cases i <;> simp
          map_smul' := fun c a => by apply Subtype.ext; apply Subtype.ext; funext i; cases i <;> simp }
      have hinj : Function.Injective emb := fun a b h => by
        apply Subtype.ext; funext i
        exact congrFun (congrArg (fun z => z.1.1) h) (Sum.inl i)
      have hsurj : Function.Surjective emb := by
        rintro ⟨⟨v, hvV⟩, hvker⟩
        have hveq : Sum.elim (fun i => v (Sum.inl i)) (0 : Fin n → F2) = v := by
          funext i; cases i with
          | inl a => rfl
          | inr b => exact (congrFun hvker b).symm
        refine ⟨⟨fun i => v (Sum.inl i), hveq.symm ▸ hvV⟩, ?_⟩
        apply Subtype.ext; apply Subtype.ext; exact hveq
      exact (LinearEquiv.ofBijective emb ⟨hinj, hsurj⟩).finrank_eq.symm
    have hrn := LinearMap.finrank_range_add_finrank_ker πB
    rw [hker] at hrn
    exact (add_comm _ _).trans hrn
  have hMs_decomp : ∀ M ∈ Ms, ∃ MW ∈ W0 edges, ∃ MG ∈ SGs, M = MW + MG := fun M hM => by
    obtain ⟨MW, hMW, MG, hMG, hEq⟩ := Submodule.mem_sup.1 (hU_le_sup (Submodule.subset_span hM))
    exact ⟨MW, hMW, MG, hMG, hEq.symm⟩
  have hflag_gen : ∀ M ∈ Ms, ∀ MW ∈ W0 edges, ∀ MG ∈ SGs, M = MW + MG →
      ∀ x ∈ orthSub (A0 ⊔ A1), ∀ y ∈ orthSub (A0 ⊓ A1),
        dotProduct (x ᵥ* MW.submatrix Sum.inl Sum.inr) y = 0 := by
    intro M hM MW hMW MG hMG hEq x hx y hy
    obtain ⟨A, K, hA, hK, rfl⟩ := hMW
    obtain ⟨u1, v1, u2, v2, hMrk⟩ := hMs_rk M hM
    have hR_le : LinearMap.range ((Matrix.vecMulLinear (blockX A K)).domRestrict (orthSub V)) ≤
        Submodule.span F2 ({v1, v2} : Set (J n → F2)) := by
      rintro w ⟨⟨z, hz⟩, rfl⟩
      have hkill := hMG_kill MG hMG z hz
      have hzw : z ᵥ* blockX A K = z ᵥ* M := by
        rw [hEq, Matrix.vecMul_add, hkill, add_zero]
      change z ᵥ* blockX A K ∈ _
      rw [hzw, hMrk]
      have hform : z ᵥ* outerPairG u1 v1 u2 v2 =
          dotProduct z u1 • v1 + dotProduct z u2 • v2 := by
        funext j
        simp only [Matrix.vecMul, dotProduct, outerPairG, Matrix.of_apply, mul_add, sum_add_distrib,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        congr 1
        · rw [Finset.sum_mul]; refine sum_congr rfl fun k _ => by ring
        · rw [Finset.sum_mul]; refine sum_congr rfl fun k _ => by ring
      rw [hform]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert v1 {v2})))
        (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem v1 rfl)))
    have hrk2 : Module.finrank F2 (LinearMap.range ((Matrix.vecMulLinear (blockX A K)).domRestrict (orthSub V))) ≤ 2 := by
      calc Module.finrank F2 _
          ≤ Module.finrank F2 (Submodule.span F2 ({v1, v2} : Set (J n → F2))) := Submodule.finrank_mono hR_le
        _ ≤ 2 := by
            have h1 : Module.finrank F2 (Submodule.span F2 ({v1, v2} : Set (J n → F2))) ≤
                Fintype.card (Fin 2) := by
              have hrg : LinearMap.range (Fintype.linearCombination F2 ![v1, v2]) =
                  Submodule.span F2 ({v1, v2} : Set (J n → F2)) := by
                rw [Fintype.range_linearCombination]
                congr 1; ext z
                simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero,
                  Matrix.cons_val_one, Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm]
              rw [← hrg]
              calc Module.finrank F2 _ ≤ Module.finrank F2 (Fin 2 → F2) := LinearMap.finrank_range_le _
                _ = 2 := Module.finrank_fin_fun F2
            simpa using h1
    have hfc := flag_criterion_one V hK.1 hrk2 x hx y hy
    have hsub : (blockX A K).submatrix Sum.inl Sum.inr = K := rfl
    rw [hsub]; exact hfc
  have hflag_all : ∀ MW ∈ W0 edges, ∀ x ∈ orthSub (A0 ⊔ A1), ∀ y ∈ orthSub (A0 ⊓ A1),
      dotProduct (x ᵥ* MW.submatrix Sum.inl Sum.inr) y = 0 := by
    intro MW hMW x hx y hy
    have hMW_U : MW ∈ U := hW0_le hMW
    have hsplit : ∃ MW' ∈ W0 edges, ∃ MG' ∈ SGs,
        MW = MW' + MG' ∧ dotProduct (x ᵥ* MW'.submatrix Sum.inl Sum.inr) y = 0 := by
      refine Submodule.span_induction
        (p := fun A _ => ∃ MW' ∈ W0 edges, ∃ MG' ∈ SGs,
          A = MW' + MG' ∧ dotProduct (x ᵥ* MW'.submatrix Sum.inl Sum.inr) y = 0) ?_ ?_ ?_ ?_ hMW_U
      · intro M hM
        obtain ⟨MW', hMW', MG', hMG', hEq⟩ := hMs_decomp M hM
        exact ⟨MW', hMW', MG', hMG', hEq, hflag_gen M hM MW' hMW' MG' hMG' hEq x hx y hy⟩
      · exact ⟨0, (W0 edges).zero_mem, 0, SGs.zero_mem, (add_zero 0).symm, by simp⟩
      · rintro A B _ _ ⟨MW1, hMW1, MG1, hMG1, rfl, h1⟩ ⟨MW2, hMW2, MG2, hMG2, rfl, h2⟩
        refine ⟨MW1 + MW2, (W0 edges).add_mem hMW1 hMW2, MG1 + MG2, SGs.add_mem hMG1 hMG2, by abel, ?_⟩
        have hsub_add : (MW1 + MW2).submatrix Sum.inl Sum.inr =
            MW1.submatrix Sum.inl Sum.inr + MW2.submatrix Sum.inl Sum.inr := rfl
        rw [hsub_add, Matrix.vecMul_add, add_dotProduct, h1, h2, add_zero]
      · rintro c A _ ⟨MW1, hMW1, MG1, hMG1, rfl, h1⟩
        refine ⟨c • MW1, (W0 edges).smul_mem c hMW1, c • MG1, SGs.smul_mem c hMG1, by rw [smul_add], ?_⟩
        have hsub_smul : (c • MW1).submatrix Sum.inl Sum.inr =
            c • MW1.submatrix Sum.inl Sum.inr := rfl
        rw [hsub_smul, Matrix.vecMul_smul, smul_dotProduct, h1, smul_zero]
    obtain ⟨MW', hMW', MG', hMG', hEq, h0⟩ := hsplit
    have hdiff : MW - MW' = MG' := eq_of_sub_eq_zero (by rw [hEq]; abel)
    have hMG0 : MG' = 0 := (Submodule.mem_bot F2).1 (hdisj ▸ ⟨hdiff ▸ (W0 edges).sub_mem hMW hMW', hMG'⟩)
    rw [hMG0, add_zero] at hEq
    rw [hEq]; exact h0
  let F2_sub := A0 ⊓ A1
  let F1_sub := A0 ⊔ A1
  have hF_le : F2_sub ≤ F1_sub := inf_le_sup
  obtain ⟨P2, _, hP2_card, hP2_orth⟩ := extend_pivot_set F2_sub ∅ (by
    rw [Fintype.linearIndependent_iff]; intro c _ i; exact absurd i.2 (notMem_empty _))
  have hP2_li_F1 : LinearIndependent F2 (fun i : P2 =>
      ({ toFun := fun v : F1_sub => v.1 i.1
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl } : F1_sub →ₗ[F2] F2)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hzero : ∀ v ∈ F2_sub, ∑ i : P2, c i * v i.1 = 0 := by
      intro v hv
      have := congrArg (fun f : F1_sub →ₗ[F2] F2 => f ⟨v, hF_le hv⟩) hc
      simpa [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using this
    by_contra hne
    push_neg at hne
    obtain ⟨i0, hi0⟩ := hne
    have hc1 : c i0 = 1 := f2_eq_one_of_ne_zero hi0
    let F2_ev : P2 → (F2_sub →ₗ[F2] F2) := fun i =>
      { toFun := fun v => v.1 i.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hP2_orth_card : Module.finrank F2 F2_sub ≤ P2.card - 1 := by
      let ev_sub : F2_sub →ₗ[F2] ({j : P2 // j ≠ i0} → F2) :=
        { toFun := fun v j => v.1 j.1.1
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hinj_ev : Function.Injective ev_sub := by
        rw [injective_iff_map_eq_zero]
        rintro ⟨v, hv⟩ hv0
        apply Subtype.ext; funext j
        by_cases hj : j ∈ P2
        · by_cases hji0 : (⟨j, hj⟩ : P2) = i0
          · have hsum0 := hzero v hv
            have hsp := add_sum_erase (s := (Finset.univ : Finset P2))
              (f := fun k : P2 => c k * v k.1) (mem_univ i0)
            rw [hsum0, hc1, one_mul] at hsp
            have hrest : ∑ k ∈ (Finset.univ : Finset P2).erase i0, c k * v k.1 = 0 :=
              sum_eq_zero fun k hk => by
                have hk0 := congrFun hv0 ⟨k, (mem_erase.1 hk).1⟩
                simp [ev_sub] at hk0; rw [hk0, mul_zero]
            rw [hrest, add_zero] at hsp
            have : j = i0.1 := congrArg Subtype.val hji0
            rw [this]; exact hsp
          · exact congrFun hv0 ⟨⟨j, hj⟩, hji0⟩
        · obtain ⟨y, hy, hyj, hysupp⟩ := hP2_orth j hj
          have hy_dot := hy v hv
          have hy_zero_P2 : ∀ k ∈ P2, y k * v k = 0 := fun k hk => by
            by_cases hki0 : (⟨k, hk⟩ : P2) = i0
            · have hsum0 := hzero v hv
              have hsp := add_sum_erase (s := (Finset.univ : Finset P2))
                (f := fun m : P2 => c m * v m.1) (mem_univ i0)
              rw [hsum0, hc1, one_mul] at hsp
              have hrest : ∑ m ∈ (Finset.univ : Finset P2).erase i0, c m * v m.1 = 0 :=
                sum_eq_zero fun m hm => by
                  have hm0 := congrFun hv0 ⟨m, (mem_erase.1 hm).1⟩
                  simp [ev_sub] at hm0; rw [hm0, mul_zero]
              rw [hrest, add_zero] at hsp
              have : k = i0.1 := congrArg Subtype.val hki0
              rw [this, hsp, mul_zero]
            · have hk0 := congrFun hv0 ⟨⟨k, hk⟩, hki0⟩
              simp [ev_sub] at hk0; rw [hk0, mul_zero]
          have hsum_eq : dotProduct y v = y j * v j := by
            rw [dotProduct, sum_eq_single j]
            · intro k _ hkj
              by_cases hyk : y k = 0
              · rw [hyk, zero_mul]
              · exact hy_zero_P2 k ((hysupp k hyk).resolve_left hkj)
            · intro h; exact absurd (mem_univ j) h
          rw [hsum_eq, hyj, one_mul] at hy_dot
          exact hy_dot
      have h1 := LinearMap.finrank_le_finrank_of_injective hinj_ev
      rw [Module.finrank_fintype_fun_eq_card] at h1
      have hcard_sub : Fintype.card {j : P2 // j ≠ i0} = P2.card - 1 := by
        have hu : Fintype.card {j : P2 // j = i0} = 1 := Fintype.card_unique
        rw [Fintype.card_subtype_compl, hu, Fintype.card_coe]
      omega
    have hP2_pos : 0 < P2.card := Finset.card_pos.2 ⟨i0.1, i0.2⟩
    omega
  obtain ⟨P1, hP2_sub_P1, hP1_card, hP1_orth⟩ := extend_pivot_set F1_sub P2 hP2_li_F1
  let w : Fin n → Fin 3 := fun i =>
    if i ∈ P2 then ⟨2, by omega⟩
    else if i ∈ P1 then ⟨1, by omega⟩
    else ⟨0, by omega⟩
  refine ⟨hD0_le, w, ?_, ?_⟩
  · intro p hp
    rcases p with ⟨a, b⟩
    have hab : a < b := hedges (a, b) hp
    have hne : a ≠ b := ne_of_lt hab
    by_contra hlt
    have hcases : (a ∉ P1 ∧ b ∉ P2) ∨ (b ∉ P1 ∧ a ∉ P2) := by
      dsimp only [w] at hlt
      by_cases ha2 : a ∈ P2 <;> by_cases ha1 : a ∈ P1 <;>
        by_cases hb2 : b ∈ P2 <;> by_cases hb1 : b ∈ P1 <;>
        simp [ha2, ha1, hb2, hb1] at hlt
      all_goals try exact absurd (hP2_sub_P1 ha2) ha1
      all_goals try exact absurd (hP2_sub_P1 hb2) hb1
      all_goals tauto
    let K_ab : Matrix (Fin n) (Fin n) F2 := Matrix.of fun i j =>
      if (i = a ∧ j = b) ∨ (i = b ∧ j = a) then 1 else 0
    have hK_ab : allowedM edges K_ab := by
      refine ⟨⟨?_, fun i => ?_⟩, fun i j h1 h2 => ?_⟩
      · ext i j; simp only [Matrix.transpose_apply, K_ab, Matrix.of_apply]
        have hiff : ((j = a ∧ i = b) ∨ (j = b ∧ i = a)) ↔ ((i = a ∧ j = b) ∨ (i = b ∧ j = a)) := by tauto
        simp only [hiff]
      · simp only [K_ab, Matrix.of_apply]
        split_ifs with h
        · rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩
          · exact absurd h hne
          · exact absurd h.symm hne
        · rfl
      · simp only [K_ab, Matrix.of_apply]
        rw [if_neg]; rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact h1 hp
        · exact h2 hp
    have hM_ab : blockX 0 K_ab ∈ W0 edges := ⟨0, K_ab, altM_zero, hK_ab, rfl⟩
    have hquad_eval : ∀ (u v : Fin n → F2), dotProduct (u ᵥ* K_ab) v = u a * v b + u b * v a := by
      intro u v
      simp only [dotProduct, Matrix.vecMul, K_ab, Matrix.of_apply]
      have hterm : ∀ j : Fin n, (∑ i : Fin n, u i * (if i = a ∧ j = b ∨ i = b ∧ j = a then 1 else 0)) * v j =
          if j = b then u a * v b else if j = a then u b * v a else 0 := by
        intro j
        by_cases hjb : j = b
        · subst hjb
          rw [if_pos rfl, sum_eq_single a]
          · simp [hne.symm]
          · intro i _ hia; simp [hia, hne.symm]
          · intro h; exact absurd (mem_univ a) h
        · by_cases hja : j = a
          · subst hja
            rw [if_neg hne, if_pos rfl, sum_eq_single b]
            · simp [hne]
            · intro i _ hib; simp [hib, hne]
            · intro h; exact absurd (mem_univ b) h
          · rw [if_neg hjb, if_neg hja]
            have h0 : ∑ i : Fin n, u i * (if i = a ∧ j = b ∨ i = b ∧ j = a then 1 else 0) = 0 :=
              sum_eq_zero fun i _ => by simp [hja, hjb]
            rw [h0, zero_mul]
      simp_rw [hterm]
      rw [← sum_subset (subset_univ ({a, b} : Finset (Fin n)))]
      · rw [sum_pair hne]
        simp [hne, add_comm]
      · intro j _ hj
        simp only [mem_insert, mem_singleton, not_or] at hj
        simp [hj.1, hj.2]
    rcases hcases with ⟨ha1, hb2⟩ | ⟨hb1, ha2⟩
    · obtain ⟨x, hx, hxa, _⟩ := hP1_orth a ha1
      obtain ⟨y, hy, hyb, hysupp⟩ := hP2_orth b hb2
      have h0 := hflag_all (blockX 0 K_ab) hM_ab x hx y hy
      have hsub_eq : (blockX 0 K_ab).submatrix Sum.inl Sum.inr = K_ab := rfl
      rw [hsub_eq, hquad_eval] at h0
      have hya : y a = 0 := by
        by_contra hne0
        rcases hysupp a hne0 with rfl | haP2
        · exact hne rfl
        · exact ha1 (hP2_sub_P1 haP2)
      rw [hxa, hyb, hya, one_mul, mul_zero, add_zero] at h0
      exact one_ne_zero h0
    · obtain ⟨x, hx, hxb, _⟩ := hP1_orth b hb1
      obtain ⟨y, hy, hya, hysupp⟩ := hP2_orth a ha2
      have h0 := hflag_all (blockX 0 K_ab) hM_ab x hx y hy
      have hsub_eq : (blockX 0 K_ab).submatrix Sum.inl Sum.inr = K_ab := rfl
      rw [hsub_eq, hquad_eval] at h0
      have hyb : y b = 0 := by
        by_contra hne0
        rcases hysupp b hne0 with rfl | hbP2
        · exact hne rfl
        · exact hb1 (hP2_sub_P1 hbP2)
      rw [hxb, hya, hyb, one_mul, mul_zero, zero_add] at h0
      exact one_ne_zero h0
  · have hsum_w : ∑ i : Fin n, (w i).val = P1.card + P2.card := by
      have hval : ∀ i : Fin n, (w i).val = (if i ∈ P1 then 1 else 0) + (if i ∈ P2 then 1 else 0) := by
        intro i
        by_cases h2 : i ∈ P2
        · have h1 : i ∈ P1 := hP2_sub_P1 h2
          simp [w, h1, h2]
        · by_cases h1 : i ∈ P1 <;> simp [w, h1, h2]
      simp_rw [hval, sum_add_distrib]
      simp [Finset.sum_boole]
    have hgrass := Submodule.finrank_sup_add_finrank_inf_eq A0 A1
    rw [hsum_w, hP1_card, hP2_card]
    dsimp only [F1_sub, F2_sub]
    omega

lemma part2_cover {n : ℕ} (edges : Finset (Fin n × Fin n)) (hedges : ∀ p ∈ edges, p.1 < p.2)
    (f t : ℕ) (hbank : bankProp edges f t) :
    Nat.choose n 2 + edges.card + n * f ≤ t ∧
    ∃ w : Fin n → Fin 3,
      (∀ p ∈ edges, 2 ≤ (w p.1).val + (w p.2).val) ∧
      (∑ i : Fin n, (w i).val) ≤ 2 * (t - (Nat.choose n 2 + edges.card + n * f)) := by
  obtain ⟨hnf, hbank0⟩ := (part1_padding edges f t).1 hbank
  obtain ⟨hD0, w, hcov, hsum⟩ := part2_cover_zero edges hedges (t - n * f) hbank0
  refine ⟨by omega, w, hcov, ?_⟩
  have heq : t - n * f - (Nat.choose n 2 + edges.card) = t - (Nat.choose n 2 + edges.card + n * f) := by omega
  rwa [heq] at hsum

end Part2Cover

section Part3Upper

lemma part3_upper_zero {n : ℕ} (edges : Finset (Fin n × Fin n)) (hedges : ∀ p ∈ edges, p.1 < p.2)
    (s : Finset (Fin n)) :
    bankProp edges 0 (Nat.choose n 2 + edges.card + s.card +
      (edges.filter fun p => p.1 ∉ s ∨ p.2 ∉ s).card) := by
  classical
  rw [bankProp0_iff_span]
  let eT : Fin n → (J n → F2) := fun i => Pi.single (Sum.inl i) 1
  let eB : Fin n → (J n → F2) := fun i => Pi.single (Sum.inr i) 1
  let EA : PairLt n → Matrix (J n) (J n) F2 := fun p =>
    outerPairG (eT p.1.1) (eT p.1.2) (eT p.1.2) (eT p.1.1)
  let ED : Fin n → Matrix (J n) (J n) F2 := fun i =>
    outerPairG (eT i) (eT i) (eB i) (eB i)
  let SQ : Fin n × Fin n → Matrix (J n) (J n) F2 := fun p =>
    outerPairG (eT p.1 + eB p.2) (eT p.1 + eB p.2) (eT p.2 + eB p.1) (eT p.2 + eB p.1)
  let K1 : Fin n × Fin n → Matrix (J n) (J n) F2 := fun p =>
    outerPairG (eT p.1) (eB p.2) (eT p.2) (eB p.1)
  let K2 : Fin n × Fin n → Matrix (J n) (J n) F2 := fun p =>
    outerPairG (eB p.2) (eT p.1) (eB p.1) (eT p.2)
  let edgesIn := edges.filter fun p => p.1 ∈ s ∧ p.2 ∈ s
  let edgesOut := edges.filter fun p => p.1 ∉ s ∨ p.2 ∉ s
  let MsA := (Finset.univ : Finset (PairLt n)).toList.map EA
  let MsD := s.toList.map ED
  let MsIn := edgesIn.toList.map SQ
  let MsOut1 := edgesOut.toList.map K1
  let MsOut2 := edgesOut.toList.map K2
  let Ms := MsA ++ MsD ++ MsIn ++ MsOut1 ++ MsOut2
  have hpart_edges : edgesIn.card + edgesOut.card = edges.card := by
    have hdisj : Disjoint edgesIn edgesOut := by
      rw [disjoint_left]; intro p h1 h2
      simp only [edgesIn, edgesOut, mem_filter] at h1 h2
      tauto
    have hunion : edgesIn ∪ edgesOut = edges := by
      ext p; simp only [edgesIn, edgesOut, mem_union, mem_filter]
      by_cases h1 : p.1 ∈ s <;> by_cases h2 : p.2 ∈ s <;> tauto
    rw [← card_union_of_disjoint hdisj, hunion]
  refine ⟨Ms, ?_, ?_, ?_⟩
  · simp only [Ms, MsA, MsD, MsIn, MsOut1, MsOut2, List.length_append, List.length_map,
      Finset.length_toList, card_univ, card_pairLt]
    have hOut : edgesOut.card = (edges.filter fun p => p.1 ∉ s ∨ p.2 ∉ s).card := rfl
    omega
  · intro M hM
    simp only [Ms, MsA, MsD, MsIn, MsOut1, MsOut2, List.mem_append, List.mem_map,
      Finset.mem_toList] at hM
    rcases hM with ((((⟨p, _, rfl⟩ | ⟨i, _, rfl⟩) | ⟨p, _, rfl⟩) | ⟨p, _, rfl⟩) | ⟨p, _, rfl⟩)
    · exact ⟨eT p.1.1, eT p.1.2, eT p.1.2, eT p.1.1, rfl⟩
    · exact ⟨eT i, eT i, eB i, eB i, rfl⟩
    · exact ⟨eT p.1 + eB p.2, eT p.1 + eB p.2, eT p.2 + eB p.1, eT p.2 + eB p.1, rfl⟩
    · exact ⟨eT p.1, eB p.2, eT p.2, eB p.1, rfl⟩
    · exact ⟨eB p.2, eT p.1, eB p.1, eT p.2, rfl⟩
  · let Sp := Submodule.span F2 {M | M ∈ Ms}
    have hEA_mem : ∀ p : PairLt n, EA p ∈ Sp := fun p =>
      Submodule.subset_span (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _
          (List.mem_map.2 ⟨p, Finset.mem_toList.2 (mem_univ p), rfl⟩)))))
    have hEK_mem : ∀ p ∈ edges, K1 p + K2 p ∈ Sp := by
      intro p hp
      by_cases hin : p.1 ∈ s ∧ p.2 ∈ s
      · have hSQ_mem : SQ p ∈ Sp := Submodule.subset_span (by
          simp only [Ms, MsIn, edgesIn, List.mem_append, List.mem_map, Finset.mem_toList, mem_filter]
          left; left; right; exact ⟨p, ⟨hp, hin⟩, rfl⟩)
        have hD1_mem : ED p.1 ∈ Sp := Submodule.subset_span (by
          simp only [Ms, MsD, List.mem_append, List.mem_map, Finset.mem_toList]
          left; left; left; right; exact ⟨p.1, hin.1, rfl⟩)
        have hD2_mem : ED p.2 ∈ Sp := Submodule.subset_span (by
          simp only [Ms, MsD, List.mem_append, List.mem_map, Finset.mem_toList]
          left; left; left; right; exact ⟨p.2, hin.2, rfl⟩)
        have heq : K1 p + K2 p = SQ p + ED p.1 + ED p.2 := by
          ext i j
          simp only [Matrix.add_apply, K1, K2, SQ, ED, outerPairG, Matrix.of_apply, Pi.add_apply]
          have h1 := f2_add_self (eT p.1 i * eT p.1 j)
          have h2 := f2_add_self (eB p.2 i * eB p.2 j)
          have h3 := f2_add_self (eT p.2 i * eT p.2 j)
          have h4 := f2_add_self (eB p.1 i * eB p.1 j)
          calc (eT p.1 i * eB p.2 j + eT p.2 i * eB p.1 j) +
                (eB p.2 i * eT p.1 j + eB p.1 i * eT p.2 j)
              = (eT p.1 i * eB p.2 j + eT p.2 i * eB p.1 j) +
                (eB p.2 i * eT p.1 j + eB p.1 i * eT p.2 j) +
                ((eT p.1 i * eT p.1 j + eT p.1 i * eT p.1 j) +
                 (eB p.2 i * eB p.2 j + eB p.2 i * eB p.2 j) +
                 (eT p.2 i * eT p.2 j + eT p.2 i * eT p.2 j) +
                 (eB p.1 i * eB p.1 j + eB p.1 i * eB p.1 j)) := by
                  rw [h1, h2, h3, h4]; ring
            _ = _ := by ring
        rw [heq]
        exact Submodule.add_mem _ (Submodule.add_mem _ hSQ_mem hD1_mem) hD2_mem
      · have hout : p.1 ∉ s ∨ p.2 ∉ s := by tauto
        have h1 : K1 p ∈ Sp := Submodule.subset_span (by
          simp only [Ms, MsOut1, edgesOut, List.mem_append, List.mem_map, Finset.mem_toList, mem_filter]
          left; right; exact ⟨p, ⟨hp, hout⟩, rfl⟩)
        have h2 : K2 p ∈ Sp := Submodule.subset_span (by
          simp only [Ms, MsOut2, edgesOut, List.mem_append, List.mem_map, Finset.mem_toList, mem_filter]
          right; exact ⟨p, ⟨hp, hout⟩, rfl⟩)
        exact Submodule.add_mem _ h1 h2
    have hEA_entry : ∀ (p : PairLt n) (i j : J n),
        EA p i j = (if i = Sum.inl p.1.1 ∧ j = Sum.inl p.1.2 then 1 else 0) +
                   (if i = Sum.inl p.1.2 ∧ j = Sum.inl p.1.1 then 1 else 0) := fun p i j => by
      simp only [EA, outerPairG, Matrix.of_apply, eT, single_mul_singleG]
    have hEK_entry : ∀ (p : Fin n × Fin n) (i j : J n),
        (K1 p + K2 p) i j =
          ((if i = Sum.inl p.1 ∧ j = Sum.inr p.2 then 1 else 0) +
           (if i = Sum.inl p.2 ∧ j = Sum.inr p.1 then 1 else 0)) +
          ((if i = Sum.inr p.2 ∧ j = Sum.inl p.1 then 1 else 0) +
           (if i = Sum.inr p.1 ∧ j = Sum.inl p.2 then 1 else 0)) := fun p i j => by
      simp only [Matrix.add_apply, K1, K2, outerPairG, Matrix.of_apply, eT, eB, single_mul_singleG]
    rintro _ ⟨A, K, hA, hK, rfl⟩
    have hdecomp : blockX A K =
        (∑ p : PairLt n, A p.1.1 p.1.2 • EA p) +
        (∑ p ∈ edges, K p.1 p.2 • (K1 p + K2 p)) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        hEA_entry, hEK_entry]
      cases i with
      | inl i0 =>
        cases j with
        | inl j0 =>
          have hK0 : ∑ p ∈ edges, K p.1 p.2 *
              (((if (Sum.inl i0 : J n) = Sum.inl p.1 ∧ (Sum.inl j0 : J n) = Sum.inr p.2 then 1 else 0) +
                (if (Sum.inl i0 : J n) = Sum.inl p.2 ∧ (Sum.inl j0 : J n) = Sum.inr p.1 then 1 else 0)) +
               ((if (Sum.inl i0 : J n) = Sum.inr p.2 ∧ (Sum.inl j0 : J n) = Sum.inl p.1 then 1 else 0) +
                (if (Sum.inl i0 : J n) = Sum.inr p.1 ∧ (Sum.inl j0 : J n) = Sum.inl p.2 then 1 else 0))) = 0 :=
            sum_eq_zero fun p _ => by simp
          rw [hK0, add_zero]
          change A i0 j0 = _
          simp only [Sum.inl.injEq, mul_add, sum_add_distrib]
          rcases lt_trichotomy i0 j0 with hlt | rfl | hgt
          · have h1 : ∑ p : PairLt n, A p.1.1 p.1.2 * (if i0 = p.1.1 ∧ j0 = p.1.2 then 1 else 0) = A i0 j0 := by
              rw [sum_eq_single ⟨(i0, j0), hlt⟩]
              · simp
              · intro p _ hne
                rw [if_neg]; · simp
                · rintro ⟨h1, h2⟩; exact hne (Subtype.ext (Prod.ext h1.symm h2.symm))
              · intro h; exact absurd (mem_univ _) h
            have h2 : ∑ p : PairLt n, A p.1.1 p.1.2 * (if i0 = p.1.2 ∧ j0 = p.1.1 then 1 else 0) = 0 :=
              sum_eq_zero fun p _ => by
                rw [if_neg]; · simp
                · rintro ⟨h1, h2⟩; have := p.2; rw [← h1, ← h2] at this; exact absurd (lt_trans hlt this) (lt_irrefl _)
            rw [h1, h2, add_zero]
          · have h1 : ∑ p : PairLt n, A p.1.1 p.1.2 * (if i0 = p.1.1 ∧ i0 = p.1.2 then 1 else 0) = 0 :=
              sum_eq_zero fun p _ => by
                rw [if_neg]; · simp
                · rintro ⟨h1, h2⟩; exact absurd (h1.symm.trans h2) (ne_of_lt p.2)
            have h2 : ∑ p : PairLt n, A p.1.1 p.1.2 * (if i0 = p.1.2 ∧ i0 = p.1.1 then 1 else 0) = 0 :=
              sum_eq_zero fun p _ => by
                rw [if_neg]; · simp
                · rintro ⟨h1, h2⟩; exact absurd (h2.symm.trans h1) (ne_of_lt p.2)
            rw [h1, h2, add_zero, hA.2 i0]
          · have h1 : ∑ p : PairLt n, A p.1.1 p.1.2 * (if i0 = p.1.1 ∧ j0 = p.1.2 then 1 else 0) = 0 :=
              sum_eq_zero fun p _ => by
                rw [if_neg]; · simp
                · rintro ⟨h1, h2⟩; have := p.2; rw [← h1, ← h2] at this; exact absurd (lt_trans hgt this) (lt_irrefl _)
            have h2 : ∑ p : PairLt n, A p.1.1 p.1.2 * (if i0 = p.1.2 ∧ j0 = p.1.1 then 1 else 0) = A j0 i0 := by
              rw [sum_eq_single ⟨(j0, i0), hgt⟩]
              · simp
              · intro p _ hne
                rw [if_neg]; · simp
                · rintro ⟨h1, h2⟩; exact hne (Subtype.ext (Prod.ext h2.symm h1.symm))
              · intro h; exact absurd (mem_univ _) h
            have hsym : A i0 j0 = A j0 i0 := congrFun (congrFun hA.1 j0) i0
            rw [h1, h2, zero_add, hsym]
        | inr j0 =>
          have hA0 : ∑ p : PairLt n, A p.1.1 p.1.2 *
              ((if (Sum.inl i0 : J n) = Sum.inl p.1.1 ∧ (Sum.inr j0 : J n) = Sum.inl p.1.2 then 1 else 0) +
               (if (Sum.inl i0 : J n) = Sum.inl p.1.2 ∧ (Sum.inr j0 : J n) = Sum.inl p.1.1 then 1 else 0)) = 0 :=
            sum_eq_zero fun p _ => by simp
          rw [hA0, zero_add]
          change K i0 j0 = _
          simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and, and_false,
            ↓reduceIte, add_zero, mul_add, sum_add_distrib]
          by_cases h1 : (i0, j0) ∈ edges
          · have hlt := hedges _ h1
            have s1 : ∑ p ∈ edges, K p.1 p.2 * (if i0 = p.1 ∧ j0 = p.2 then 1 else 0) = K i0 j0 := by
              rw [sum_eq_single (i0, j0)]
              · simp
              · intro p _ hne
                rw [if_neg]; · simp
                · rintro ⟨ha, hb⟩; exact hne (Prod.ext ha.symm hb.symm)
              · intro h; exact absurd h1 h
            have s2 : ∑ p ∈ edges, K p.1 p.2 * (if i0 = p.2 ∧ j0 = p.1 then 1 else 0) = 0 :=
              sum_eq_zero fun p hp => by
                rw [if_neg]; · simp
                · rintro ⟨ha, hb⟩; have := hedges p hp; rw [← ha, ← hb] at this; exact absurd (lt_trans hlt this) (lt_irrefl _)
            rw [s1, s2, add_zero]
          · by_cases h2 : (j0, i0) ∈ edges
            · have hlt := hedges _ h2
              have s1 : ∑ p ∈ edges, K p.1 p.2 * (if i0 = p.1 ∧ j0 = p.2 then 1 else 0) = 0 :=
                sum_eq_zero fun p hp => by
                  rw [if_neg]; · simp
                  · rintro ⟨ha, hb⟩; have := hedges p hp; rw [← ha, ← hb] at this; exact absurd (lt_trans hlt this) (lt_irrefl _)
              have s2 : ∑ p ∈ edges, K p.1 p.2 * (if i0 = p.2 ∧ j0 = p.1 then 1 else 0) = K j0 i0 := by
                rw [sum_eq_single (j0, i0)]
                · simp
                · intro p _ hne
                  rw [if_neg]; · simp
                  · rintro ⟨ha, hb⟩; exact hne (Prod.ext hb.symm ha.symm)
                · intro h; exact absurd h2 h
              have hsym : K i0 j0 = K j0 i0 := congrFun (congrFun hK.1.1 j0) i0
              rw [s1, s2, zero_add, hsym]
            · have s1 : ∑ p ∈ edges, K p.1 p.2 * (if i0 = p.1 ∧ j0 = p.2 then 1 else 0) = 0 :=
                sum_eq_zero fun p hp => by
                  rw [if_neg]; · simp
                  · rintro ⟨ha, hb⟩; exact h1 (by simpa [ha, hb] using hp)
              have s2 : ∑ p ∈ edges, K p.1 p.2 * (if i0 = p.2 ∧ j0 = p.1 then 1 else 0) = 0 :=
                sum_eq_zero fun p hp => by
                  rw [if_neg]; · simp
                  · rintro ⟨ha, hb⟩; exact h2 (by simpa [ha, hb] using hp)
              rw [s1, s2, add_zero, hK.2 i0 j0 h1 h2]
      | inr i0 =>
        cases j with
        | inl j0 =>
          have hA0 : ∑ p : PairLt n, A p.1.1 p.1.2 *
              ((if (Sum.inr i0 : J n) = Sum.inl p.1.1 ∧ (Sum.inl j0 : J n) = Sum.inl p.1.2 then 1 else 0) +
               (if (Sum.inr i0 : J n) = Sum.inl p.1.2 ∧ (Sum.inl j0 : J n) = Sum.inl p.1.1 then 1 else 0)) = 0 :=
            sum_eq_zero fun p _ => by simp
          rw [hA0, zero_add]
          change K i0 j0 = _
          simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, false_and, and_false,
            ↓reduceIte, zero_add, mul_add, sum_add_distrib]
          by_cases h1 : (i0, j0) ∈ edges
          · have hlt := hedges _ h1
            have s1 : ∑ p ∈ edges, K p.1 p.2 * (if i0 = p.2 ∧ j0 = p.1 then 1 else 0) = 0 :=
              sum_eq_zero fun p hp => by
                rw [if_neg]; · simp
                · rintro ⟨ha, hb⟩; have := hedges p hp; rw [← ha, ← hb] at this; exact absurd (lt_trans hlt this) (lt_irrefl _)
            have s2 : ∑ p ∈ edges, K p.1 p.2 * (if i0 = p.1 ∧ j0 = p.2 then 1 else 0) = K i0 j0 := by
              rw [sum_eq_single (i0, j0)]
              · simp
              · intro p _ hne
                rw [if_neg]; · simp
                · rintro ⟨ha, hb⟩; exact hne (Prod.ext ha.symm hb.symm)
              · intro h; exact absurd h1 h
            rw [s1, s2, zero_add]
          · by_cases h2 : (j0, i0) ∈ edges
            · have hlt := hedges _ h2
              have s1 : ∑ p ∈ edges, K p.1 p.2 * (if i0 = p.2 ∧ j0 = p.1 then 1 else 0) = K j0 i0 := by
                rw [sum_eq_single (j0, i0)]
                · simp
                · intro p _ hne
                  rw [if_neg]; · simp
                  · rintro ⟨ha, hb⟩; exact hne (Prod.ext hb.symm ha.symm)
                · intro h; exact absurd h2 h
              have s2 : ∑ p ∈ edges, K p.1 p.2 * (if i0 = p.1 ∧ j0 = p.2 then 1 else 0) = 0 :=
                sum_eq_zero fun p hp => by
                  rw [if_neg]; · simp
                  · rintro ⟨ha, hb⟩; have := hedges p hp; rw [← ha, ← hb] at this; exact absurd (lt_trans hlt this) (lt_irrefl _)
              have hsym : K i0 j0 = K j0 i0 := congrFun (congrFun hK.1.1 j0) i0
              rw [s1, s2, add_zero, hsym]
            · have s1 : ∑ p ∈ edges, K p.1 p.2 * (if i0 = p.2 ∧ j0 = p.1 then 1 else 0) = 0 :=
                sum_eq_zero fun p hp => by
                  rw [if_neg]; · simp
                  · rintro ⟨ha, hb⟩; exact h2 (by simpa [ha, hb] using hp)
              have s2 : ∑ p ∈ edges, K p.1 p.2 * (if i0 = p.1 ∧ j0 = p.2 then 1 else 0) = 0 :=
                sum_eq_zero fun p hp => by
                  rw [if_neg]; · simp
                  · rintro ⟨ha, hb⟩; exact h1 (by simpa [ha, hb] using hp)
              rw [s1, s2, add_zero, hK.2 i0 j0 h1 h2]
        | inr j0 =>
          have hA0 : ∑ p : PairLt n, A p.1.1 p.1.2 *
              ((if (Sum.inr i0 : J n) = Sum.inl p.1.1 ∧ (Sum.inr j0 : J n) = Sum.inl p.1.2 then 1 else 0) +
               (if (Sum.inr i0 : J n) = Sum.inl p.1.2 ∧ (Sum.inr j0 : J n) = Sum.inl p.1.1 then 1 else 0)) = 0 :=
            sum_eq_zero fun p _ => by simp
          have hK0 : ∑ p ∈ edges, K p.1 p.2 *
              (((if (Sum.inr i0 : J n) = Sum.inl p.1 ∧ (Sum.inr j0 : J n) = Sum.inr p.2 then 1 else 0) +
                (if (Sum.inr i0 : J n) = Sum.inl p.2 ∧ (Sum.inr j0 : J n) = Sum.inr p.1 then 1 else 0)) +
               ((if (Sum.inr i0 : J n) = Sum.inr p.2 ∧ (Sum.inr j0 : J n) = Sum.inl p.1 then 1 else 0) +
                (if (Sum.inr i0 : J n) = Sum.inr p.1 ∧ (Sum.inr j0 : J n) = Sum.inl p.2 then 1 else 0))) = 0 :=
            sum_eq_zero fun p _ => by simp
          rw [hA0, hK0, add_zero]; rfl
    rw [hdecomp]
    exact Submodule.add_mem _
      (Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (hEA_mem p))
      (Submodule.sum_mem _ fun p hp => Submodule.smul_mem _ _ (hEK_mem p hp))

lemma part3_upper {n : ℕ} (edges : Finset (Fin n × Fin n)) (hedges : ∀ p ∈ edges, p.1 < p.2)
    (f : ℕ) (s : Finset (Fin n)) :
    bankProp edges f (Nat.choose n 2 + edges.card + n * f + s.card +
      (edges.filter fun p => p.1 ∉ s ∨ p.2 ∉ s).card) := by
  rw [part1_padding]
  refine ⟨by omega, ?_⟩
  have heq : Nat.choose n 2 + edges.card + n * f + s.card +
      (edges.filter fun p => p.1 ∉ s ∨ p.2 ∉ s).card - n * f =
      Nat.choose n 2 + edges.card + s.card +
      (edges.filter fun p => p.1 ∉ s ∨ p.2 ∉ s).card := by omega
  rw [heq]
  exact part3_upper_zero edges hedges s

end Part3Upper

lemma main_33452 :
(
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let F := ZMod 2
∀ (n : ℕ) (edges : Finset (Fin n × Fin n)), (∀ p ∈ edges, p.1 < p.2) →
  let cover := fun (w : Fin n → Fin 3) =>
    ∀ p ∈ edges, 2 ≤ (w p.1).val + (w p.2).val
  let M := Matrix (Fin n) (Fin n) F
  let alt := fun (A : M) => A.transpose = A ∧ ∀ i, A i i = 0
  let allowed := fun (K : M) => alt K ∧
    ∀ i j, (i,j) ∉ edges → (j,i) ∉ edges → K i j = 0
  let D := fun f : ℕ => Nat.choose n 2 + edges.card + n*f
  let bank := fun (f t : ℕ) =>
    let J := Fin n ⊕ Fin n
    let d := n+n+f
    let BMat := Matrix (Fin n) (Fin f) F
    let coord : J ⊕ Fin f ≃ Fin d :=
      (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin f))).trans finSumFinEquiv
    let table := fun (A K : M) (B : BMat) (x y : Fin (d+1)) =>
      let X := Matrix.fromBlocks A K K (0 : M)
      let Y : Matrix J (Fin f) F := fun i j => Sum.elim (fun a => B a j) (fun _ => 0) i
      let Z := Matrix.fromBlocks X Y Y.transpose (0 : Matrix (Fin f) (Fin f) F)
      Fin.cases false (fun i => Fin.cases false (fun j =>
        decide (Z (coord.symm i) (coord.symm j) ≠ 0)) y) x
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : M → M → BMat → ℕ),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack ((d+1)+(d+1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
      ∀ A K B, alt A → allowed K →
        (depths ((d+1)+(d+1)) C).getD (tap A K B) 0 ≤ 1 ∧
        PEqualNP.Represents.Represents (table A K B) ⟨C.gates, tap A K B⟩
  (∀ f t : ℕ, bank f t ↔ n*f ≤ t ∧ bank 0 (t-n*f)) ∧
    (∀ f t : ℕ, bank f t → D f ≤ t ∧
      ∃ w : Fin n → Fin 3, cover w ∧ (∑ i, (w i).val) ≤ 2*(t-D f)) ∧
    ∀ (f : ℕ) (s : Finset (Fin n)),
      bank f (D f + s.card + (edges.filter (fun p => p.1 ∉ s ∨ p.2 ∉ s)).card)
) := by
  dsimp only
  intro n edges hedges
  exact ⟨fun f t => part1_padding edges f t,
    fun f t h => part2_cover edges hedges f t h,
    fun f s => part3_upper edges hedges f s⟩

end PEqualNP.Outside.L_meta_33452_aux

theorem PEqualNP.Outside.L_meta_33452 :
(
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let F := ZMod 2
∀ (n : ℕ) (edges : Finset (Fin n × Fin n)), (∀ p ∈ edges, p.1 < p.2) →
  let cover := fun (w : Fin n → Fin 3) =>
    ∀ p ∈ edges, 2 ≤ (w p.1).val + (w p.2).val
  let M := Matrix (Fin n) (Fin n) F
  let alt := fun (A : M) => A.transpose = A ∧ ∀ i, A i i = 0
  let allowed := fun (K : M) => alt K ∧
    ∀ i j, (i,j) ∉ edges → (j,i) ∉ edges → K i j = 0
  let D := fun f : ℕ => Nat.choose n 2 + edges.card + n*f
  let bank := fun (f t : ℕ) =>
    let J := Fin n ⊕ Fin n
    let d := n+n+f
    let BMat := Matrix (Fin n) (Fin f) F
    let coord : J ⊕ Fin f ≃ Fin d :=
      (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin f))).trans finSumFinEquiv
    let table := fun (A K : M) (B : BMat) (x y : Fin (d+1)) =>
      let X := Matrix.fromBlocks A K K (0 : M)
      let Y : Matrix J (Fin f) F := fun i j => Sum.elim (fun a => B a j) (fun _ => 0) i
      let Z := Matrix.fromBlocks X Y Y.transpose (0 : Matrix (Fin f) (Fin f) F)
      Fin.cases false (fun i => Fin.cases false (fun j =>
        decide (Z (coord.symm i) (coord.symm j) ≠ 0)) y) x
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : M → M → BMat → ℕ),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack ((d+1)+(d+1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
      ∀ A K B, alt A → allowed K →
        (depths ((d+1)+(d+1)) C).getD (tap A K B) 0 ≤ 1 ∧
        PEqualNP.Represents.Represents (table A K B) ⟨C.gates, tap A K B⟩
  (∀ f t : ℕ, bank f t ↔ n*f ≤ t ∧ bank 0 (t-n*f)) ∧
    (∀ f t : ℕ, bank f t → D f ≤ t ∧
      ∃ w : Fin n → Fin 3, cover w ∧ (∑ i, (w i).val) ≤ 2*(t-D f)) ∧
    ∀ (f : ℕ) (s : Finset (Fin n)),
      bank f (D f + s.card + (edges.filter (fun p => p.1 ∉ s ∨ p.2 ∉ s)).card)
) :=
  PEqualNP.Outside.L_meta_33452_aux.main_33452
