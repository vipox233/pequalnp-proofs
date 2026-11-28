import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32062_aux

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

section InvolutionNormalForm

def Nstd (d r : ℕ) : Matrix (Fin d) (Fin d) F2 :=
  Matrix.of fun i j => if r ≤ i.val ∧ i.val < 2 * r ∧ j.val + r = i.val then 1 else 0

set_option maxHeartbeats 600000 in
lemma involution_normal_form {d : ℕ} (U : Matrix (Fin d) (Fin d) F2) (hU : U * U = 1) :
    let r := (U - 1).rank
    2 * r ≤ d ∧
    ∃ P Q : Matrix (Fin d) (Fin d) F2,
      P * Q = 1 ∧ Q * P = 1 ∧ Q * (U - 1) * P = Nstd d r := by
  classical
  intro r
  set N : Matrix (Fin d) (Fin d) F2 := U - 1
  have hN2 : N * N = 0 := by
    have h1 : N = U + 1 := by ext i j; exact f2_sub_eq_add _ _
    rw [h1]
    calc (U + 1) * (U + 1) = U * U + (U + U) + 1 := by noncomm_ring
      _ = 1 + 0 + 1 := by
          rw [hU]
          congr 2
          ext i j; exact f2_add_self (U i j)
      _ = 0 := by ext i j; simp [f2_add_self]
  let L : (Fin d → F2) →ₗ[F2] (Fin d → F2) := Matrix.toLin' N
  have hL2 : ∀ v, L (L v) = 0 := fun v => by
    change N *ᵥ (N *ᵥ v) = 0
    rw [Matrix.mulVec_mulVec, hN2, Matrix.zero_mulVec]
  have him_le_ker : LinearMap.range L ≤ LinearMap.ker L := by
    rintro _ ⟨v, rfl⟩
    exact hL2 v
  have hr_eq : Module.finrank F2 (LinearMap.range L) = r := rfl
  have hker_rank : Module.finrank F2 (LinearMap.ker L) + r = d := by
    have h := LinearMap.finrank_range_add_finrank_ker L
    rw [hr_eq, Module.finrank_fin_fun] at h
    omega
  have h2r : 2 * r ≤ d := by
    have hle := Submodule.finrank_mono him_le_ker
    rw [hr_eq] at hle
    omega
  let Rsub : Submodule F2 (LinearMap.ker L) := (LinearMap.range L).comap (LinearMap.ker L).subtype
  have hRsub_rank : Module.finrank F2 Rsub = r := by
    have hrg : LinearMap.range ((LinearMap.ker L).subtype.domRestrict Rsub) = LinearMap.range L := by
      ext v
      simp only [LinearMap.mem_range, LinearMap.domRestrict_apply, Submodule.coe_subtype,
        Subtype.exists, Submodule.mem_comap, Rsub]
      exact ⟨fun ⟨w, _, hwR, hwv⟩ => hwv ▸ hwR, fun hv => ⟨v, him_le_ker hv, hv, rfl⟩⟩
    have hinj : Function.Injective ((LinearMap.ker L).subtype.domRestrict Rsub) :=
      fun a b h => Subtype.ext (Subtype.ext h)
    rw [← hr_eq, ← hrg]
    exact (LinearEquiv.ofInjective _ hinj).finrank_eq
  obtain ⟨Ksub, hKcomp⟩ := Submodule.exists_isCompl Rsub
  have hKsub_rank : Module.finrank F2 Ksub = d - 2 * r := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hKcomp
    rw [hRsub_rank] at h1
    omega
  obtain ⟨bIm, _⟩ : ∃ _ : Module.Basis (Fin r) F2 (LinearMap.range L), True :=
    ⟨Module.finBasisOfFinrankEq F2 (LinearMap.range L) hr_eq, trivial⟩
  haveI : Module.Free F2 Ksub := Module.Free.of_divisionRing F2 Ksub
  obtain ⟨bK, _⟩ : ∃ _ : Module.Basis (Fin (d - 2 * r)) F2 Ksub, True :=
    ⟨Module.finBasisOfFinrankEq F2 Ksub hKsub_rank, trivial⟩
  have hlift : ∀ a : Fin r, ∃ u : Fin d → F2, L u = (bIm a).1 := fun a => (bIm a).2
  choose uVec huVec using hlift
  let col : Fin d → (Fin d → F2) := fun j =>
    if h1 : j.val < r then uVec ⟨j.val, h1⟩
    else if h2 : j.val < 2 * r then (bIm ⟨j.val - r, by omega⟩).1
    else (bK ⟨j.val - 2 * r, by omega⟩).1.1
  have hcol_li : LinearIndependent F2 col := by
    rw [Fintype.linearIndependent_iff]
    intro c hsum
    have hLsum : ∑ j : Fin d, c j • L (col j) = 0 := by
      have := congrArg L hsum
      rwa [map_sum, map_zero, sum_congr rfl (fun j _ => map_smul L (c j) (col j))] at this
    have hLcol : ∀ j : Fin d, L (col j) = if h1 : j.val < r then (bIm ⟨j.val, h1⟩).1 else 0 := by
      intro j
      dsimp only [col]
      split_ifs with h1 h2
      · exact huVec ⟨j.val, h1⟩
      · exact him_le_ker (bIm ⟨j.val - r, by omega⟩).2
      · exact (bK ⟨j.val - 2 * r, by omega⟩).1.2
    have hc_first : ∀ a : Fin r, c ⟨a.val, by omega⟩ = 0 := by
      have hIm_sum : ∑ a : Fin r, c ⟨a.val, by omega⟩ • bIm a = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum, Submodule.coe_zero]
        have hflt : ∑ j : Fin d, c j • L (col j) =
            ∑ a : Fin r, c ⟨a.val, by omega⟩ • (bIm a).1 := by
          simp_rw [hLcol]
          rw [← sum_subset (subset_univ (Finset.univ.filter fun j : Fin d => j.val < r))]
          · refine sum_bij (fun j hj => ⟨j.val, (mem_filter.1 hj).2⟩) ?_ ?_ ?_ ?_
            · intro _ _; exact mem_univ _
            · intro j1 _ j2 _ h; exact Fin.ext (congrArg (Fin.val : Fin r → ℕ) h)
            · intro a _
              exact ⟨⟨a.val, by omega⟩, mem_filter.2 ⟨mem_univ _, a.isLt⟩, Fin.ext rfl⟩
            · intro j hj
              have hlt := (mem_filter.1 hj).2
              simp [hlt]
          · intro j _ hnot
            have hge : ¬ j.val < r := by simpa using hnot
            simp [hge]
        simp only [Submodule.coe_smul_of_tower]
        rw [← hflt]
        exact hLsum
      exact Fintype.linearIndependent_iff.1 bIm.linearIndependent _ hIm_sum
    let s1 : LinearMap.ker L :=
      ⟨∑ a : Fin r, c ⟨r + a.val, by omega⟩ • (bIm a).1,
        Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (him_le_ker (bIm a).2)⟩
    let s2 : LinearMap.ker L :=
      ⟨∑ b : Fin (d - 2 * r), c ⟨2 * r + b.val, by omega⟩ • (bK b).1.1,
        Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (bK b).1.2⟩
    have hs1_mem : s1 ∈ Rsub := by
      change (s1 : Fin d → F2) ∈ LinearMap.range L
      dsimp only [s1]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (bIm a).2
    have hs2_mem : s2 ∈ Ksub := by
      have : s2 = ∑ b : Fin (d - 2 * r), c ⟨2 * r + b.val, by omega⟩ • (bK b).1 := by
        apply Subtype.ext; simp [s2]
      rw [this]
      exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (bK b).2
    have hs12 : s1 + s2 = 0 := by
      apply Subtype.ext
      change (s1 : Fin d → F2) + (s2 : Fin d → F2) = 0
      rw [← hsum]
      let A1 := (Finset.univ : Finset (Fin d)).filter (fun j => j.val < r)
      let A2 := (Finset.univ : Finset (Fin d)).filter (fun j => r ≤ j.val ∧ j.val < 2 * r)
      let A3 := (Finset.univ : Finset (Fin d)).filter (fun j => 2 * r ≤ j.val)
      have hpart : (Finset.univ : Finset (Fin d)) = A1 ∪ (A2 ∪ A3) := by
        ext j; simp only [A1, A2, A3, mem_union, mem_filter, mem_univ, true_and, true_iff]; omega
      have hd12 : Disjoint A1 (A2 ∪ A3) := by
        rw [disjoint_left]; intro j h1 h2
        simp only [A1, A2, A3, mem_union, mem_filter, mem_univ, true_and] at h1 h2; omega
      have hd23 : Disjoint A2 A3 := by
        rw [disjoint_left]; intro j h2 h3
        simp only [A2, A3, mem_filter, mem_univ, true_and] at h2 h3; omega
      rw [hpart, sum_union hd12, sum_union hd23]
      have hA1 : ∑ j ∈ A1, c j • col j = 0 := sum_eq_zero fun j hj => by
        have hlt := (mem_filter.1 hj).2
        have : c j = 0 := hc_first ⟨j.val, hlt⟩
        simp [this]
      have hA2 : ∑ j ∈ A2, c j • col j = (s1 : Fin d → F2) := by
        symm
        change ∑ a : Fin r, c ⟨r + a.val, by omega⟩ • (bIm a).1 = ∑ j ∈ A2, c j • col j
        refine sum_bij (fun (a : Fin r) _ => (⟨r + a.val, by omega⟩ : Fin d)) ?_ ?_ ?_ ?_
        · intro a _; exact mem_filter.2 ⟨mem_univ _, by simp, by simp; omega⟩
        · intro a1 _ a2 _ h; exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)
        · intro j hj
          have ⟨hge, hlt⟩ := (mem_filter.1 hj).2
          exact ⟨⟨j.val - r, by omega⟩, mem_univ _, Fin.ext (by simp; omega)⟩
        · intro a _
          dsimp only [col]
          have h1 : ¬ r + a.val < r := by omega
          have h2 : r + a.val < 2 * r := by omega
          simp [h1, h2]
      have hA3 : ∑ j ∈ A3, c j • col j = (s2 : Fin d → F2) := by
        symm
        change ∑ b : Fin (d - 2 * r), c ⟨2 * r + b.val, by omega⟩ • (bK b).1.1 = ∑ j ∈ A3, c j • col j
        refine sum_bij (fun (b : Fin (d - 2 * r)) _ => (⟨2 * r + b.val, by omega⟩ : Fin d)) ?_ ?_ ?_ ?_
        · intro b _; exact mem_filter.2 ⟨mem_univ _, by simp⟩
        · intro b1 _ b2 _ h; exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)
        · intro j hj
          have hge := (mem_filter.1 hj).2
          exact ⟨⟨j.val - 2 * r, by omega⟩, mem_univ _, Fin.ext (by simp; omega)⟩
        · intro b _
          dsimp only [col]
          have h1 : ¬ 2 * r + b.val < r := by omega
          have h2 : ¬ 2 * r + b.val < 2 * r := by omega
          simp [h1, h2]
      rw [hA1, zero_add, hA2, hA3]
    have hs1_0 : s1 = 0 := by
      have hs1_K : s1 ∈ Ksub := by
        have : s1 = -s2 := eq_neg_of_add_eq_zero_left hs12
        rw [this]; exact Ksub.neg_mem hs2_mem
      exact (Submodule.mem_bot F2).1 (hKcomp.inf_eq_bot ▸ ⟨hs1_mem, hs1_K⟩)
    have hs2_0 : s2 = 0 := by rw [hs1_0, zero_add] at hs12; exact hs12
    have hc_mid : ∀ a : Fin r, c ⟨r + a.val, by omega⟩ = 0 := by
      have h0 : ∑ a : Fin r, c ⟨r + a.val, by omega⟩ • bIm a = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum, Submodule.coe_zero]
        exact congrArg Subtype.val hs1_0
      exact Fintype.linearIndependent_iff.1 bIm.linearIndependent _ h0
    have hc_last : ∀ b : Fin (d - 2 * r), c ⟨2 * r + b.val, by omega⟩ = 0 := by
      have h0 : ∑ b : Fin (d - 2 * r), c ⟨2 * r + b.val, by omega⟩ • bK b = 0 := by
        apply Subtype.ext
        apply Subtype.ext
        simp only [Submodule.coe_sum, Submodule.coe_zero, Submodule.coe_smul_of_tower]
        exact congrArg Subtype.val hs2_0
      intro b
      let evalB : Ksub →ₗ[F2] F2 := (Finsupp.lapply b).comp bK.repr.toLinearMap
      have h1 := congrArg evalB h0
      simp only [map_sum, map_smul, map_zero, evalB, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap, Module.Basis.repr_self, Finsupp.lapply_apply,
        Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h1
      exact h1
    intro j
    by_cases h1 : j.val < r
    · exact hc_first ⟨j.val, h1⟩
    · by_cases h2 : j.val < 2 * r
      · convert hc_mid ⟨j.val - r, by omega⟩ using 1
        congr 1; exact Fin.ext (by simp; omega)
      · convert hc_last ⟨j.val - 2 * r, by omega⟩ using 1
        congr 1; exact Fin.ext (by simp; omega)
  let P : Matrix (Fin d) (Fin d) F2 := Matrix.of fun i j => col j i
  have hP_inj : Function.Injective (Matrix.toLin' P) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hsum : ∑ j : Fin d, v j • col j = 0 := by
      funext i
      have hi := congrFun hv i
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, P, Matrix.of_apply,
        Pi.zero_apply] at hi
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hi
    have h0 := Fintype.linearIndependent_iff.1 hcol_li v hsum
    funext j; exact h0 j
  have hP_bij : Function.Bijective (Matrix.toLin' P) :=
    ⟨hP_inj, LinearMap.injective_iff_surjective.1 hP_inj⟩
  let eP : (Fin d → F2) ≃ₗ[F2] (Fin d → F2) := LinearEquiv.ofBijective (Matrix.toLin' P) hP_bij
  let Q : Matrix (Fin d) (Fin d) F2 := LinearMap.toMatrix' eP.symm.toLinearMap
  have hQ_lin : Matrix.toLin' Q = eP.symm.toLinearMap :=
    Matrix.toLin'_toMatrix' eP.symm.toLinearMap
  have hPQ : P * Q = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext; intro v
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_one, LinearMap.id_apply, hQ_lin]
    exact eP.apply_symm_apply v
  have hQP : Q * P = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext; intro v
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_one, LinearMap.id_apply, hQ_lin]
    exact eP.symm_apply_apply v
  have hNP : N * P = P * Nstd d r := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply]
    have hbasis : ∀ j : Fin d, N *ᵥ (P *ᵥ Pi.single j 1) = P *ᵥ (Nstd d r *ᵥ Pi.single j 1) := by
      intro j
      have hPj : P *ᵥ Pi.single j 1 = col j := by
        funext i; simp [Matrix.mulVec, dotProduct, P, Pi.single_apply]
      rw [hPj]
      by_cases h1 : j.val < r
      · have hNcol : N *ᵥ col j = col ⟨j.val + r, by omega⟩ := by
          have hL1 : L (col j) = (bIm ⟨j.val, h1⟩).1 := by
            dsimp only [col]; rw [dif_pos h1]; exact huVec ⟨j.val, h1⟩
          have hcol2 : col ⟨j.val + r, by omega⟩ = (bIm ⟨j.val, h1⟩).1 := by
            dsimp only [col]
            rw [dif_neg (by omega), dif_pos (by omega)]
            congr 1; congr 1; exact Fin.ext (by simp)
          rw [hcol2]; exact hL1
        have hNsj : Nstd d r *ᵥ Pi.single j 1 = Pi.single ⟨j.val + r, by omega⟩ 1 := by
          funext i
          simp only [Matrix.mulVec, dotProduct, Nstd, Matrix.of_apply, Pi.single_apply,
            mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]
          by_cases hi : i = ⟨j.val + r, by omega⟩
          · subst hi; simp [show r ≤ j.val + r by omega, show j.val + r < 2 * r by omega]
          · have hne : ¬ (r ≤ i.val ∧ i.val < 2 * r ∧ j.val + r = i.val) := by
              intro h; apply hi; exact Fin.ext h.2.2.symm
            simp [hi, hne]
        rw [hNcol, hNsj]
        funext i; simp [Matrix.mulVec, dotProduct, P, Pi.single_apply]
      · have hNcol : N *ᵥ col j = 0 := by
          dsimp only [col]
          rw [dif_neg h1]
          split_ifs with h2
          · exact him_le_ker (bIm ⟨j.val - r, by omega⟩).2
          · exact (bK ⟨j.val - 2 * r, by omega⟩).1.2
        have hNsj : Nstd d r *ᵥ Pi.single j 1 = 0 := by
          funext i
          simp only [Matrix.mulVec, dotProduct, Nstd, Matrix.of_apply, Pi.single_apply,
            mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true, Pi.zero_apply]
          have hne : ¬ (r ≤ i.val ∧ i.val < 2 * r ∧ j.val + r = i.val) := by omega
          simp [hne]
        rw [hNcol, hNsj, Matrix.mulVec_zero]
    have hv_eq : v = ∑ j : Fin d, v j • Pi.single j 1 := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv_eq]
    conv_rhs => rw [hv_eq]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, hbasis]
  refine ⟨h2r, P, Q, hPQ, hQP, ?_⟩
  rw [Matrix.mul_assoc, hNP, ← Matrix.mul_assoc, hQP, one_mul]

end InvolutionNormalForm

section StandardSpace

def alt {d : ℕ} (H : Matrix (Fin d) (Fin d) F2) : Prop :=
  Hᵀ = H ∧ ∀ i, H i i = 0

lemma alt_cong {d : ℕ} (P H : Matrix (Fin d) (Fin d) F2) (hH : alt H) :
    alt (P * H * Pᵀ) := by
  constructor
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hH.1, Matrix.mul_assoc]
  · intro i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, sum_mul]
    rw [show ∑ x : Fin d, ∑ y : Fin d, P i y * H y x * P i x =
        ∑ p : Fin d × Fin d, P i p.2 * H p.2 p.1 * P i p.1 from
        (Fintype.sum_prod_type (fun p : Fin d × Fin d => P i p.2 * H p.2 p.1 * P i p.1)).symm]
    let f : Fin d × Fin d → F2 := fun p => P i p.2 * H p.2 p.1 * P i p.1
    have hsymm : ∀ p : Fin d × Fin d, f (p.2, p.1) = f p := fun p => by
      dsimp only [f]
      have hHsym : H p.1 p.2 = H p.2 p.1 := congrFun (congrFun hH.1 p.2) p.1
      rw [hHsym]; ring
    have hdiag : ∀ a : Fin d, f (a, a) = 0 := fun a => by simp [f, hH.2 a]
    let Slt := (Finset.univ : Finset (Fin d × Fin d)).filter (fun p => p.1.val < p.2.val)
    let Sgt := (Finset.univ : Finset (Fin d × Fin d)).filter (fun p => p.2.val < p.1.val)
    let Seq := (Finset.univ : Finset (Fin d × Fin d)).filter (fun p => p.1.val = p.2.val)
    have hpart : (Finset.univ : Finset (Fin d × Fin d)) = Seq ∪ (Slt ∪ Sgt) := by
      ext p; simp only [Seq, Slt, Sgt, mem_union, mem_filter, mem_univ, true_and, true_iff]; omega
    have hd1 : Disjoint Seq (Slt ∪ Sgt) := by
      rw [disjoint_left]; intro p h1 h2
      simp only [Seq, Slt, Sgt, mem_union, mem_filter, mem_univ, true_and] at h1 h2; omega
    have hd2 : Disjoint Slt Sgt := by
      rw [disjoint_left]; intro p h1 h2
      simp only [Slt, Sgt, mem_filter, mem_univ, true_and] at h1 h2; omega
    rw [hpart, sum_union hd1, sum_union hd2]
    have hSeq : ∑ p ∈ Seq, f p = 0 := sum_eq_zero fun p hp => by
      have heq : p.1 = p.2 := Fin.ext (mem_filter.1 hp).2
      rw [show p = (p.1, p.1) from Prod.ext rfl heq.symm]
      exact hdiag p.1
    have hSgt : ∑ p ∈ Sgt, f p = ∑ p ∈ Slt, f p := by
      refine sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
      · intro p hp; exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hp).2⟩
      · intro p1 _ p2 _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
      · intro p hp; exact ⟨(p.2, p.1), mem_filter.2 ⟨mem_univ _, (mem_filter.1 hp).2⟩, rfl⟩
      · intro p _; exact (hsymm p).symm
    rw [hSeq, zero_add, hSgt, f2_add_self]

def Wstd (d r : ℕ) (h2r : 2 * r ≤ d) : Submodule F2 (Matrix (Fin d) (Fin d) F2) :=
  { carrier := {M |
      alt M ∧
      (∀ i j : Fin d, ¬ (r ≤ i.val ∧ i.val < 2 * r) → ¬ (r ≤ j.val ∧ j.val < 2 * r) → M i j = 0) ∧
      (∀ i j : Fin d, i.val < r → 2 * r ≤ j.val → M i j = 0) ∧
      (∀ i j : Fin d, 2 * r ≤ i.val → j.val < r → M i j = 0) ∧
      (∀ a b : Fin r, M ⟨a.val, by omega⟩ ⟨r + b.val, by omega⟩ =
        M ⟨b.val, by omega⟩ ⟨r + a.val, by omega⟩) ∧
      (∀ a : Fin r, M ⟨a.val, by omega⟩ ⟨r + a.val, by omega⟩ = 0)}
    zero_mem' := by simp [alt], add_mem' := by
      rintro M1 M2 ⟨⟨hs1, hd1⟩, hz1, ha1, hb1, hk1, hkd1⟩ ⟨⟨hs2, hd2⟩, hz2, ha2, hb2, hk2, hkd2⟩
      refine ⟨⟨by rw [Matrix.transpose_add, hs1, hs2], fun i => by simp [hd1 i, hd2 i]⟩,
        fun i j hi hj => by simp [hz1 i j hi hj, hz2 i j hi hj],
        fun i j hi hj => by simp [ha1 i j hi hj, ha2 i j hi hj],
        fun i j hi hj => by simp [hb1 i j hi hj, hb2 i j hi hj],
        fun a b => by simp [hk1 a b, hk2 a b],
        fun a => by simp [hkd1 a, hkd2 a]⟩
    smul_mem' := by
      rintro c M ⟨⟨hs, hd⟩, hz, ha, hb, hk, hkd⟩
      refine ⟨⟨by rw [Matrix.transpose_smul, hs], fun i => by simp [hd i]⟩,
        fun i j hi hj => by simp [hz i j hi hj],
        fun i j hi hj => by simp [ha i j hi hj],
        fun i j hi hj => by simp [hb i j hi hj],
        fun a b => by simp [hk a b],
        fun a => by simp [hkd a]⟩ }

lemma std_diff_formula {d r : ℕ} (h2r : 2 * r ≤ d) (H : Matrix (Fin d) (Fin d) F2) (i j : Fin d) :
    (((1 : Matrix (Fin d) (Fin d) F2) + Nstd d r) * H * ((1 : Matrix (Fin d) (Fin d) F2) + Nstd d r)ᵀ + H) i j =
      (if h1 : r ≤ i.val ∧ i.val < 2 * r then H ⟨i.val - r, by omega⟩ j else 0) +
      (if h2 : r ≤ j.val ∧ j.val < 2 * r then H i ⟨j.val - r, by omega⟩ else 0) +
      (if h12 : (r ≤ i.val ∧ i.val < 2 * r) ∧ (r ≤ j.val ∧ j.val < 2 * r) then
        H ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩ else 0) := by
  have hexp : (1 + Nstd d r) * H * (1 + Nstd d r)ᵀ + H =
      Nstd d r * H + H * (Nstd d r)ᵀ + Nstd d r * H * (Nstd d r)ᵀ := by
    rw [Matrix.transpose_add, Matrix.transpose_one]
    have hHH : H + H = 0 := by ext a b; exact f2_add_self (H a b)
    calc (1 + Nstd d r) * H * (1 + (Nstd d r)ᵀ) + H
        = (H + H) + (Nstd d r * H + H * (Nstd d r)ᵀ + Nstd d r * H * (Nstd d r)ᵀ) := by noncomm_ring
      _ = Nstd d r * H + H * (Nstd d r)ᵀ + Nstd d r * H * (Nstd d r)ᵀ := by rw [hHH, zero_add]
  rw [hexp]
  have hNH : ∀ a b : Fin d, (Nstd d r * H) a b =
      if h : r ≤ a.val ∧ a.val < 2 * r then H ⟨a.val - r, by omega⟩ b else 0 := by
    intro a b
    rw [Matrix.mul_apply]
    by_cases ha : r ≤ a.val ∧ a.val < 2 * r
    · rw [dif_pos ha]
      rw [sum_eq_single ⟨a.val - r, by omega⟩]
      · simp [Nstd, ha, show a.val - r + r = a.val by omega]
      · intro k _ hne
        have : ¬ (r ≤ a.val ∧ a.val < 2 * r ∧ k.val + r = a.val) := by
          intro h; apply hne; exact Fin.ext (by simp; omega)
        simp [Nstd, this]
      · intro h; exact absurd (mem_univ _) h
    · rw [dif_neg ha]
      exact sum_eq_zero fun k _ => by
        have hnot : ¬ (r ≤ a.val ∧ a.val < 2 * r ∧ k.val + r = a.val) := fun h => ha ⟨h.1, h.2.1⟩
        simp [Nstd, hnot]
  have hHNT : ∀ (M : Matrix (Fin d) (Fin d) F2) (a b : Fin d), (M * (Nstd d r)ᵀ) a b =
      if h : r ≤ b.val ∧ b.val < 2 * r then M a ⟨b.val - r, by omega⟩ else 0 := by
    intro M a b
    rw [Matrix.mul_apply]
    by_cases hb : r ≤ b.val ∧ b.val < 2 * r
    · rw [dif_pos hb]
      rw [sum_eq_single ⟨b.val - r, by omega⟩]
      · simp [Nstd, hb, show b.val - r + r = b.val by omega]
      · intro k _ hne
        have : ¬ (r ≤ b.val ∧ b.val < 2 * r ∧ k.val + r = b.val) := by
          intro h; apply hne; exact Fin.ext (by simp; omega)
        simp [Nstd, this]
      · intro h; exact absurd (mem_univ _) h
    · rw [dif_neg hb]
      exact sum_eq_zero fun k _ => by
        have hnot : ¬ (r ≤ b.val ∧ b.val < 2 * r ∧ k.val + r = b.val) := fun h => hb ⟨h.1, h.2.1⟩
        simp [Nstd, hnot]
  simp only [Matrix.add_apply, hNH, hHNT]
  by_cases hi : r ≤ i.val ∧ i.val < 2 * r <;> by_cases hj : r ≤ j.val ∧ j.val < 2 * r <;>
    simp [hi, hj]

lemma image_eq_Wstd {d r : ℕ} (h2r : 2 * r ≤ d) (M : Matrix (Fin d) (Fin d) F2) :
    (∃ H : Matrix (Fin d) (Fin d) F2, alt H ∧ M = (1 + Nstd d r) * H * (1 + Nstd d r)ᵀ + H) ↔
      M ∈ Wstd d r h2r := by
  constructor
  · rintro ⟨H, hH, rfl⟩
    have halt : alt ((1 + Nstd d r) * H * (1 + Nstd d r)ᵀ + H) := by
      have h1 := alt_cong (1 + Nstd d r) H hH
      exact ⟨by rw [Matrix.transpose_add, h1.1, hH.1], fun i => by rw [Matrix.add_apply, h1.2 i, hH.2 i, add_zero]⟩
    refine ⟨halt, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hi hj
      rw [std_diff_formula h2r H i j]
      simp [hi, hj]
    · intro i j hi hj
      rw [std_diff_formula h2r H i j]
      have h1 : ¬ (r ≤ i.val ∧ i.val < 2 * r) := by omega
      have h2 : ¬ (r ≤ j.val ∧ j.val < 2 * r) := by omega
      simp [h1, h2]
    · intro i j hi hj
      rw [std_diff_formula h2r H i j]
      have h1 : ¬ (r ≤ i.val ∧ i.val < 2 * r) := by omega
      have h2 : ¬ (r ≤ j.val ∧ j.val < 2 * r) := by omega
      simp [h1, h2]
    · intro a b
      rw [std_diff_formula h2r H, std_diff_formula h2r H]
      have h1a : ¬ (r ≤ a.val ∧ a.val < 2 * r) := by omega
      have h1b : ¬ (r ≤ b.val ∧ b.val < 2 * r) := by omega
      have h2a : r ≤ r + a.val ∧ r + a.val < 2 * r := by omega
      have h2b : r ≤ r + b.val ∧ r + b.val < 2 * r := by omega
      rw [dif_neg h1a, dif_pos h2b, dif_neg (fun h => h1a h.1),
        dif_neg h1b, dif_pos h2a, dif_neg (fun h => h1b h.1), zero_add, add_zero, zero_add, add_zero]
      have hsym : H ⟨a.val, by omega⟩ ⟨b.val, by omega⟩ = H ⟨b.val, by omega⟩ ⟨a.val, by omega⟩ :=
        congrFun (congrFun hH.1 ⟨b.val, by omega⟩) ⟨a.val, by omega⟩
      convert hsym using 2 <;> exact Fin.ext (by simp)
    · intro a
      rw [std_diff_formula h2r H]
      have h1a : ¬ (r ≤ a.val ∧ a.val < 2 * r) := by omega
      have h2a : r ≤ r + a.val ∧ r + a.val < 2 * r := by omega
      simp only [h1a, h2a, ↓reduceDIte, false_and, zero_add, add_zero, Nat.add_sub_cancel_left]
      exact hH.2 ⟨a.val, by omega⟩
  · rintro ⟨⟨hMsym, hMdiag⟩, hMz, hMa, hMb, hMk, hMkd⟩
    let H : Matrix (Fin d) (Fin d) F2 := Matrix.of fun i j =>
      if h1 : i.val < r ∧ j.val < r then M i ⟨r + j.val, by omega⟩
      else if h2 : i.val < r ∧ r ≤ j.val ∧ j.val < 2 * r then
        if i.val < j.val - r then M ⟨r + i.val, by omega⟩ j + M i j else 0
      else if h3 : r ≤ i.val ∧ i.val < 2 * r ∧ j.val < r then
        if j.val < i.val - r then M ⟨r + j.val, by omega⟩ i + M j i else 0
      else if h4 : i.val < r ∧ 2 * r ≤ j.val then M ⟨r + i.val, by omega⟩ j
      else if h5 : 2 * r ≤ i.val ∧ j.val < r then M ⟨r + j.val, by omega⟩ i
      else 0
    have hHalt : alt H := by
      constructor
      · ext i j
        simp only [Matrix.transpose_apply, H, Matrix.of_apply]
        by_cases h1 : j.val < r ∧ i.val < r
        · have h1' : i.val < r ∧ j.val < r := ⟨h1.2, h1.1⟩
          rw [dif_pos h1, dif_pos h1']
          exact hMk ⟨j.val, h1.1⟩ ⟨i.val, h1.2⟩
        · have h1' : ¬ (i.val < r ∧ j.val < r) := fun h => h1 ⟨h.2, h.1⟩
          rw [dif_neg h1, dif_neg h1']
          by_cases h2 : j.val < r ∧ r ≤ i.val ∧ i.val < 2 * r
          · have h2' : ¬ (i.val < r ∧ r ≤ j.val ∧ j.val < 2 * r) := by omega
            have h3' : r ≤ i.val ∧ i.val < 2 * r ∧ j.val < r := ⟨h2.2.1, h2.2.2, h2.1⟩
            rw [dif_pos h2, dif_neg h2', dif_pos h3']
          · by_cases h3 : r ≤ j.val ∧ j.val < 2 * r ∧ i.val < r
            · have h2' : i.val < r ∧ r ≤ j.val ∧ j.val < 2 * r := ⟨h3.2.2, h3.1, h3.2.1⟩
              rw [dif_neg h2, dif_pos h3, dif_pos h2']
            · have h2' : ¬ (i.val < r ∧ r ≤ j.val ∧ j.val < 2 * r) := fun h => h3 ⟨h.2.1, h.2.2, h.1⟩
              have h3' : ¬ (r ≤ i.val ∧ i.val < 2 * r ∧ j.val < r) := fun h => h2 ⟨h.2.2, h.1, h.2.1⟩
              rw [dif_neg h2, dif_neg h3, dif_neg h2', dif_neg h3']
              by_cases h4 : j.val < r ∧ 2 * r ≤ i.val
              · have h4' : ¬ (i.val < r ∧ 2 * r ≤ j.val) := by omega
                have h5' : 2 * r ≤ i.val ∧ j.val < r := ⟨h4.2, h4.1⟩
                rw [dif_pos h4, dif_neg h4', dif_pos h5']
              · by_cases h5 : 2 * r ≤ j.val ∧ i.val < r
                · have h4' : i.val < r ∧ 2 * r ≤ j.val := ⟨h5.2, h5.1⟩
                  rw [dif_neg h4, dif_pos h5, dif_pos h4']
                · have h4' : ¬ (i.val < r ∧ 2 * r ≤ j.val) := fun h => h5 ⟨h.2, h.1⟩
                  have h5' : ¬ (2 * r ≤ i.val ∧ j.val < r) := fun h => h4 ⟨h.2, h.1⟩
                  rw [dif_neg h4, dif_neg h5, dif_neg h4', dif_neg h5']
      · intro i
        simp only [H, Matrix.of_apply]
        by_cases h1 : i.val < r
        · rw [dif_pos ⟨h1, h1⟩]
          exact hMkd ⟨i.val, h1⟩
        · have h1' : ¬ (i.val < r ∧ i.val < r) := by omega
          have h2' : ¬ (i.val < r ∧ r ≤ i.val ∧ i.val < 2 * r) := by omega
          have h3' : ¬ (r ≤ i.val ∧ i.val < 2 * r ∧ i.val < r) := by omega
          have h4' : ¬ (i.val < r ∧ 2 * r ≤ i.val) := by omega
          have h5' : ¬ (2 * r ≤ i.val ∧ i.val < r) := by omega
          rw [dif_neg h1', dif_neg h2', dif_neg h3', dif_neg h4', dif_neg h5']
    refine ⟨H, hHalt, ?_⟩
    ext i j
    rw [std_diff_formula h2r H i j]
    by_cases hi1 : i.val < r
    · by_cases hj1 : j.val < r
      · have hni : ¬ (r ≤ i.val ∧ i.val < 2 * r) := by omega
        have hnj : ¬ (r ≤ j.val ∧ j.val < 2 * r) := by omega
        simp [hni, hnj, hMz i j hni hnj]
      · by_cases hj2 : j.val < 2 * r
        · have hni : ¬ (r ≤ i.val ∧ i.val < 2 * r) := by omega
          have hj : r ≤ j.val ∧ j.val < 2 * r := ⟨by omega, hj2⟩
          rw [dif_neg hni, dif_pos hj, dif_neg (fun h => hni h.1), zero_add, add_zero]
          simp only [H, Matrix.of_apply]
          rw [dif_pos ⟨hi1, show j.val - r < r by omega⟩]
          congr 1; exact Fin.ext (by simp; omega)
        · have hni : ¬ (r ≤ i.val ∧ i.val < 2 * r) := by omega
          have hnj : ¬ (r ≤ j.val ∧ j.val < 2 * r) := by omega
          simp [hni, hnj, hMa i j hi1 (by omega)]
    · by_cases hi2 : i.val < 2 * r
      · have hi : r ≤ i.val ∧ i.val < 2 * r := ⟨by omega, hi2⟩
        by_cases hj1 : j.val < r
        · have hnj : ¬ (r ≤ j.val ∧ j.val < 2 * r) := by omega
          rw [dif_pos hi, dif_neg hnj, dif_neg (fun h => hnj h.2), add_zero, add_zero]
          simp only [H, Matrix.of_apply]
          rw [dif_pos ⟨show i.val - r < r by omega, hj1⟩]
          have hsym : M i j = M j i := congrFun (congrFun hMsym j) i
          rw [hsym]
          have h0 := hMk ⟨i.val - r, by omega⟩ ⟨j.val, hj1⟩
          symm; convert h0 using 2 <;> exact Fin.ext (by simp; omega)
        · by_cases hj2 : j.val < 2 * r
          · have hj : r ≤ j.val ∧ j.val < 2 * r := ⟨by omega, hj2⟩
            rw [dif_pos hi, dif_pos hj, dif_pos ⟨hi, hj⟩]
            simp only [H, Matrix.of_apply]
            have ha1 : ¬ (i.val - r < r ∧ j.val < r) := by omega
            have ha2 : i.val - r < r ∧ r ≤ j.val ∧ j.val < 2 * r := ⟨by omega, hj.1, hj.2⟩
            have hb1 : ¬ (i.val < r ∧ j.val - r < r) := by omega
            have hb2 : ¬ (i.val < r ∧ r ≤ j.val - r ∧ j.val - r < 2 * r) := by omega
            have hb3 : r ≤ i.val ∧ i.val < 2 * r ∧ j.val - r < r := ⟨hi.1, hi.2, by omega⟩
            have hc1 : i.val - r < r ∧ j.val - r < r := ⟨by omega, by omega⟩
            rw [dif_neg ha1, dif_pos ha2, dif_neg hb1, dif_neg hb2, dif_pos hb3, dif_pos hc1]
            have hi_eq : (⟨r + (i.val - r), by omega⟩ : Fin d) = i := Fin.ext (by simp; omega)
            have hj_eq : (⟨r + (j.val - r), by omega⟩ : Fin d) = j := Fin.ext (by simp; omega)
            rcases lt_trichotomy (i.val - r) (j.val - r) with hlt | heq | hgt
            · have hnot : ¬ j.val - r < i.val - r := by omega
              rw [if_pos hlt, if_neg hnot, add_zero, hi_eq, hj_eq]
              have hcancel := f2_add_self (M ⟨i.val - r, by omega⟩ j)
              calc M i j = M i j + (M ⟨i.val - r, by omega⟩ j + M ⟨i.val - r, by omega⟩ j) := by rw [hcancel, add_zero]
                _ = (M i j + M ⟨i.val - r, by omega⟩ j) + M ⟨i.val - r, by omega⟩ j := by ring
            · have heqij : i = j := Fin.ext (by omega)
              subst heqij
              have hnot : ¬ i.val - r < i.val - r := lt_irrefl _
              rw [if_neg hnot, zero_add, zero_add, hMdiag i]
              have h0 := hMkd ⟨i.val - r, by omega⟩
              symm; convert h0 using 2 <;> exact Fin.ext (by simp; omega)
            · have hnot : ¬ i.val - r < j.val - r := by omega
              rw [if_neg hnot, if_pos hgt, zero_add, hj_eq]
              have hsymM : M j i = M i j := congrFun (congrFun hMsym i) j
              have hsymK : M ⟨j.val - r, by omega⟩ i = M ⟨i.val - r, by omega⟩ j := by
                have h0 := hMk ⟨j.val - r, by omega⟩ ⟨i.val - r, by omega⟩
                convert h0 using 2 <;> exact Fin.ext (by simp; omega)
              rw [hsymM, hsymK]
              have hcancel := f2_add_self (M ⟨i.val - r, by omega⟩ j)
              calc M i j = M i j + (M ⟨i.val - r, by omega⟩ j + M ⟨i.val - r, by omega⟩ j) := by rw [hcancel, add_zero]
                _ = (M i j + M ⟨i.val - r, by omega⟩ j) + M ⟨i.val - r, by omega⟩ j := by ring
          · have hnj : ¬ (r ≤ j.val ∧ j.val < 2 * r) := by omega
            rw [dif_pos hi, dif_neg hnj, dif_neg (fun h => hnj h.2), add_zero, add_zero]
            simp only [H, Matrix.of_apply]
            have h1 : ¬ (i.val - r < r ∧ j.val < r) := by omega
            have h2 : ¬ (i.val - r < r ∧ r ≤ j.val ∧ j.val < 2 * r) := by omega
            have h3 : ¬ (r ≤ i.val - r ∧ i.val - r < 2 * r ∧ j.val < r) := by omega
            have h4 : i.val - r < r ∧ 2 * r ≤ j.val := ⟨by omega, by omega⟩
            rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4]
            congr 1; exact Fin.ext (by simp; omega)
      · have hni : ¬ (r ≤ i.val ∧ i.val < 2 * r) := by omega
        by_cases hj1 : j.val < r
        · have hnj : ¬ (r ≤ j.val ∧ j.val < 2 * r) := by omega
          simp [hni, hnj, hMb i j (by omega) hj1]
        · by_cases hj2 : j.val < 2 * r
          · have hj : r ≤ j.val ∧ j.val < 2 * r := ⟨by omega, hj2⟩
            rw [dif_neg hni, dif_pos hj, dif_neg (fun h => hni h.1), zero_add, add_zero]
            simp only [H, Matrix.of_apply]
            have h1 : ¬ (i.val < r ∧ j.val - r < r) := by omega
            have h2 : ¬ (i.val < r ∧ r ≤ j.val - r ∧ j.val - r < 2 * r) := by omega
            have h3 : ¬ (r ≤ i.val ∧ i.val < 2 * r ∧ j.val - r < r) := by omega
            have h4 : ¬ (i.val < r ∧ 2 * r ≤ j.val - r) := by omega
            have h5 : 2 * r ≤ i.val ∧ j.val - r < r := ⟨by omega, by omega⟩
            rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4, dif_pos h5]
            have hsym : M i j = M j i := congrFun (congrFun hMsym j) i
            rw [hsym]
            congr 1; exact Fin.ext (by simp; omega)
          · have hnj : ¬ (r ≤ j.val ∧ j.val < 2 * r) := by omega
            simp [hni, hnj, hMz i j hni hnj]

abbrev PairLt (r : ℕ) := {p : Fin r × Fin r // p.1.val < p.2.val}

lemma card_pairLt (r : ℕ) : Fintype.card (PairLt r) = Nat.choose r 2 := by
  have hbij : Fintype.card (PairLt r) = ((Finset.univ : Finset (Fin r)).powersetCard 2).card := by
    rw [Fintype.card_subtype]
    refine card_bij (fun p _ => {p.1, p.2}) ?_ ?_ ?_
    · rintro ⟨a, b⟩ hp
      have hlt : a.val < b.val := (mem_filter.1 hp).2
      have hne : a ≠ b := fun h => by subst h; omega
      exact mem_powersetCard.2 ⟨subset_univ _, card_pair hne⟩
    · rintro ⟨a1, b1⟩ hp1 ⟨a2, b2⟩ hp2 heq
      have hlt1 : a1.val < b1.val := (mem_filter.1 hp1).2
      have hlt2 : a2.val < b2.val := (mem_filter.1 hp2).2
      have h1 : a1 ∈ ({a2, b2} : Finset (Fin r)) := by rw [← heq]; simp
      have h2 : b1 ∈ ({a2, b2} : Finset (Fin r)) := by rw [← heq]; simp
      simp only [mem_insert, mem_singleton] at h1 h2
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> first | exact Prod.ext rfl rfl | omega
    · intro s hs
      obtain ⟨a, b, hne, rfl⟩ := card_eq_two.1 (mem_powersetCard.1 hs).2
      by_cases hab : a.val < b.val
      · exact ⟨(a, b), mem_filter.2 ⟨mem_univ _, hab⟩, rfl⟩
      · have hba : b.val < a.val := by
          have : a.val ≠ b.val := fun h => hne (Fin.ext h)
          omega
        exact ⟨(b, a), mem_filter.2 ⟨mem_univ _, hba⟩, pair_comm b a⟩
  rw [hbij, card_powersetCard, card_univ, Fintype.card_fin]

lemma two_mul_choose_two_add (d r : ℕ) (h2r : 2 * r ≤ d) :
    Nat.choose r 2 + Nat.choose r 2 + r * (d - 2 * r) = r * (d - r - 1) := by
  have h2c : 2 * Nat.choose r 2 = r * (r - 1) := by
    rw [Nat.choose_two_right]
    have heven : Even (r * (r - 1)) := Nat.even_mul_pred_self r
    obtain ⟨k, hk⟩ := heven
    omega
  cases r with
  | zero => simp
  | succ r' =>
    have h1 : d - (r' + 1) - 1 = (d - 2 * (r' + 1)) + r' := by omega
    rw [h1, Nat.mul_add]
    have : Nat.choose (r' + 1) 2 + Nat.choose (r' + 1) 2 = (r' + 1) * r' := by
      have := h2c
      simp only [Nat.add_sub_cancel] at this
      omega
    rw [this]; ring

lemma finrank_Wstd {d r : ℕ} (h2r : 2 * r ≤ d) :
    Module.finrank F2 (Wstd d r h2r) = r * (d - r - 1) := by
  classical
  let Coord := PairLt r ⊕ PairLt r ⊕ (Fin r × Fin (d - 2 * r))
  let toCoord : Wstd d r h2r →ₗ[F2] (Coord → F2) :=
    { toFun := fun M c =>
        match c with
        | Sum.inl p => M.1 ⟨p.1.1.val, by omega⟩ ⟨r + p.1.2.val, by omega⟩
        | Sum.inr (Sum.inl p) => M.1 ⟨r + p.1.1.val, by omega⟩ ⟨r + p.1.2.val, by omega⟩
        | Sum.inr (Sum.inr ac) => M.1 ⟨r + ac.1.val, by omega⟩ ⟨2 * r + ac.2.val, by omega⟩
      map_add' := fun M1 M2 => by
        funext c; rcases c with p | (p | ac) <;> rfl
      map_smul' := fun s M => by
        funext c; rcases c with p | (p | ac) <;> rfl }
  have hinj : Function.Injective toCoord := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨M, ⟨hMsym, hMdiag⟩, hMz, hMa, hMb, hMk, hMkd⟩ h0
    apply Subtype.ext
    ext i j
    change M i j = 0
    have hMsym' : ∀ x y : Fin d, M x y = M y x := fun x y => congrFun (congrFun hMsym y) x
    have hK : ∀ a b : Fin r, M ⟨a.val, by omega⟩ ⟨r + b.val, by omega⟩ = 0 := by
      intro a b
      rcases lt_trichotomy a.val b.val with hlt | heq | hgt
      · exact congrFun h0 (Sum.inl ⟨(a, b), hlt⟩)
      · have hab : a = b := Fin.ext heq; subst hab; exact hMkd a
      · rw [hMk a b]; exact congrFun h0 (Sum.inl ⟨(b, a), hgt⟩)
    have hL : ∀ a b : Fin r, M ⟨r + a.val, by omega⟩ ⟨r + b.val, by omega⟩ = 0 := by
      intro a b
      rcases lt_trichotomy a.val b.val with hlt | heq | hgt
      · exact congrFun h0 (Sum.inr (Sum.inl ⟨(a, b), hlt⟩))
      · have hab : a = b := Fin.ext heq; subst hab; exact hMdiag ⟨r + a.val, by omega⟩
      · rw [hMsym']; exact congrFun h0 (Sum.inr (Sum.inl ⟨(b, a), hgt⟩))
    have hC : ∀ (a : Fin r) (c : Fin (d - 2 * r)),
        M ⟨r + a.val, by omega⟩ ⟨2 * r + c.val, by omega⟩ = 0 := fun a c =>
      congrFun h0 (Sum.inr (Sum.inr (a, c)))
    by_cases hi1 : i.val < r
    · by_cases hj1 : j.val < r
      · exact hMz i j (by omega) (by omega)
      · by_cases hj2 : j.val < 2 * r
        · have hj_eq : (⟨r + (j.val - r), by omega⟩ : Fin d) = j := Fin.ext (by simp; omega)
          rw [← hj_eq]; exact hK ⟨i.val, hi1⟩ ⟨j.val - r, by omega⟩
        · exact hMa i j hi1 (by omega)
    · by_cases hi2 : i.val < 2 * r
      · by_cases hj1 : j.val < r
        · rw [hMsym']
          have hi_eq : (⟨r + (i.val - r), by omega⟩ : Fin d) = i := Fin.ext (by simp; omega)
          rw [← hi_eq]; exact hK ⟨j.val, hj1⟩ ⟨i.val - r, by omega⟩
        · by_cases hj2 : j.val < 2 * r
          · have hi_eq : (⟨r + (i.val - r), by omega⟩ : Fin d) = i := Fin.ext (by simp; omega)
            have hj_eq : (⟨r + (j.val - r), by omega⟩ : Fin d) = j := Fin.ext (by simp; omega)
            rw [← hi_eq, ← hj_eq]; exact hL ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩
          · have h := hC ⟨i.val - r, by omega⟩ ⟨j.val - 2 * r, by omega⟩
            convert h using 2 <;> exact Fin.ext (by simp; omega)
      · by_cases hj1 : j.val < r
        · exact hMb i j (by omega) hj1
        · by_cases hj2 : j.val < 2 * r
          · rw [hMsym']
            have hi_eq : (⟨2 * r + (i.val - 2 * r), by omega⟩ : Fin d) = i := Fin.ext (by simp; omega)
            have hj_eq : (⟨r + (j.val - r), by omega⟩ : Fin d) = j := Fin.ext (by simp; omega)
            rw [← hi_eq, ← hj_eq]; exact hC ⟨j.val - r, by omega⟩ ⟨i.val - 2 * r, by omega⟩
          · exact hMz i j (by omega) (by omega)
  have hsurj : Function.Surjective toCoord := by
    intro f
    let M : Matrix (Fin d) (Fin d) F2 := Matrix.of fun i j =>
      if h1 : i.val < r ∧ r ≤ j.val ∧ j.val < 2 * r then
        if hlt : i.val < j.val - r then f (Sum.inl ⟨(⟨i.val, h1.1⟩, ⟨j.val - r, by omega⟩), hlt⟩)
        else if hgt : j.val - r < i.val then f (Sum.inl ⟨(⟨j.val - r, by omega⟩, ⟨i.val, h1.1⟩), hgt⟩)
        else 0
      else if h2 : r ≤ i.val ∧ i.val < 2 * r ∧ j.val < r then
        if hlt : j.val < i.val - r then f (Sum.inl ⟨(⟨j.val, h2.2.2⟩, ⟨i.val - r, by omega⟩), hlt⟩)
        else if hgt : i.val - r < j.val then f (Sum.inl ⟨(⟨i.val - r, by omega⟩, ⟨j.val, h2.2.2⟩), hgt⟩)
        else 0
      else if h3 : r ≤ i.val ∧ i.val < 2 * r ∧ r ≤ j.val ∧ j.val < 2 * r then
        if hlt : i.val - r < j.val - r then
          f (Sum.inr (Sum.inl ⟨(⟨i.val - r, by omega⟩, ⟨j.val - r, by omega⟩), hlt⟩))
        else if hgt : j.val - r < i.val - r then
          f (Sum.inr (Sum.inl ⟨(⟨j.val - r, by omega⟩, ⟨i.val - r, by omega⟩), hgt⟩))
        else 0
      else if h4 : r ≤ i.val ∧ i.val < 2 * r ∧ 2 * r ≤ j.val then
        f (Sum.inr (Sum.inr (⟨i.val - r, by omega⟩, ⟨j.val - 2 * r, by omega⟩)))
      else if h5 : 2 * r ≤ i.val ∧ r ≤ j.val ∧ j.val < 2 * r then
        f (Sum.inr (Sum.inr (⟨j.val - r, by omega⟩, ⟨i.val - 2 * r, by omega⟩)))
      else 0
    have hMmem : M ∈ Wstd d r h2r := by
      refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
      · ext i j
        simp only [Matrix.transpose_apply, M, Matrix.of_apply]
        by_cases h1 : j.val < r ∧ r ≤ i.val ∧ i.val < 2 * r
        · have h1' : ¬ (i.val < r ∧ r ≤ j.val ∧ j.val < 2 * r) := by omega
          have h2' : r ≤ i.val ∧ i.val < 2 * r ∧ j.val < r := ⟨h1.2.1, h1.2.2, h1.1⟩
          rw [dif_pos h1, dif_neg h1', dif_pos h2']
        · by_cases h2 : r ≤ j.val ∧ j.val < 2 * r ∧ i.val < r
          · have h1' : i.val < r ∧ r ≤ j.val ∧ j.val < 2 * r := ⟨h2.2.2, h2.1, h2.2.1⟩
            rw [dif_neg h1, dif_pos h2, dif_pos h1']
          · have h1' : ¬ (i.val < r ∧ r ≤ j.val ∧ j.val < 2 * r) := fun h => h2 ⟨h.2.1, h.2.2, h.1⟩
            have h2' : ¬ (r ≤ i.val ∧ i.val < 2 * r ∧ j.val < r) := fun h => h1 ⟨h.2.2, h.1, h.2.1⟩
            rw [dif_neg h1, dif_neg h2, dif_neg h1', dif_neg h2']
            by_cases h3 : r ≤ j.val ∧ j.val < 2 * r ∧ r ≤ i.val ∧ i.val < 2 * r
            · have h3' : r ≤ i.val ∧ i.val < 2 * r ∧ r ≤ j.val ∧ j.val < 2 * r :=
                ⟨h3.2.2.1, h3.2.2.2, h3.1, h3.2.1⟩
              rw [dif_pos h3, dif_pos h3']
              rcases lt_trichotomy (j.val - r) (i.val - r) with hlt | heq | hgt
              · have hnot : ¬ i.val - r < j.val - r := by omega
                rw [dif_pos hlt, dif_neg hnot, dif_pos hlt]
              · have hnot1 : ¬ j.val - r < i.val - r := by omega
                have hnot2 : ¬ i.val - r < j.val - r := by omega
                rw [dif_neg hnot1, dif_neg hnot2, dif_neg hnot2, dif_neg hnot1]
              · have hnot : ¬ j.val - r < i.val - r := by omega
                rw [dif_neg hnot, dif_pos hgt, dif_pos hgt]
            · have h3' : ¬ (r ≤ i.val ∧ i.val < 2 * r ∧ r ≤ j.val ∧ j.val < 2 * r) :=
                fun h => h3 ⟨h.2.2.1, h.2.2.2, h.1, h.2.1⟩
              rw [dif_neg h3, dif_neg h3']
              by_cases h4 : r ≤ j.val ∧ j.val < 2 * r ∧ 2 * r ≤ i.val
              · have h4' : ¬ (r ≤ i.val ∧ i.val < 2 * r ∧ 2 * r ≤ j.val) := by omega
                have h5' : 2 * r ≤ i.val ∧ r ≤ j.val ∧ j.val < 2 * r := ⟨h4.2.2, h4.1, h4.2.1⟩
                rw [dif_pos h4, dif_neg h4', dif_pos h5']
              · by_cases h5 : 2 * r ≤ j.val ∧ r ≤ i.val ∧ i.val < 2 * r
                · have h4' : r ≤ i.val ∧ i.val < 2 * r ∧ 2 * r ≤ j.val := ⟨h5.2.1, h5.2.2, h5.1⟩
                  rw [dif_neg h4, dif_pos h5, dif_pos h4']
                · have h4' : ¬ (r ≤ i.val ∧ i.val < 2 * r ∧ 2 * r ≤ j.val) :=
                    fun h => h5 ⟨h.2.2, h.1, h.2.1⟩
                  have h5' : ¬ (2 * r ≤ i.val ∧ r ≤ j.val ∧ j.val < 2 * r) :=
                    fun h => h4 ⟨h.2.1, h.2.2, h.1⟩
                  rw [dif_neg h4, dif_neg h5, dif_neg h4', dif_neg h5']
      · intro i
        simp only [M, Matrix.of_apply]
        have h1 : ¬ (i.val < r ∧ r ≤ i.val ∧ i.val < 2 * r) := by omega
        have h2 : ¬ (r ≤ i.val ∧ i.val < 2 * r ∧ i.val < r) := by omega
        have h4 : ¬ (r ≤ i.val ∧ i.val < 2 * r ∧ 2 * r ≤ i.val) := by omega
        have h5 : ¬ (2 * r ≤ i.val ∧ r ≤ i.val ∧ i.val < 2 * r) := by omega
        simp only [h1, h2, h4, h5, ↓reduceDIte]
        split_ifs <;> first | rfl | omega
      · intro i j hi hj
        simp only [M, Matrix.of_apply]
        have h1 : ¬ (i.val < r ∧ r ≤ j.val ∧ j.val < 2 * r) := fun h => hj ⟨h.2.1, h.2.2⟩
        have h2 : ¬ (r ≤ i.val ∧ i.val < 2 * r ∧ j.val < r) := fun h => hi ⟨h.1, h.2.1⟩
        have h3 : ¬ (r ≤ i.val ∧ i.val < 2 * r ∧ r ≤ j.val ∧ j.val < 2 * r) := fun h => hi ⟨h.1, h.2.1⟩
        have h4 : ¬ (r ≤ i.val ∧ i.val < 2 * r ∧ 2 * r ≤ j.val) := fun h => hi ⟨h.1, h.2.1⟩
        have h5 : ¬ (2 * r ≤ i.val ∧ r ≤ j.val ∧ j.val < 2 * r) := fun h => hj ⟨h.2.1, h.2.2⟩
        simp [h1, h2, h3, h4, h5]
      · intro i j hi hj
        simp only [M, Matrix.of_apply]
        have h1 : ¬ (i.val < r ∧ r ≤ j.val ∧ j.val < 2 * r) := by omega
        have h2 : ¬ (r ≤ i.val ∧ i.val < 2 * r ∧ j.val < r) := by omega
        have h3 : ¬ (r ≤ i.val ∧ i.val < 2 * r ∧ r ≤ j.val ∧ j.val < 2 * r) := by omega
        have h4 : ¬ (r ≤ i.val ∧ i.val < 2 * r ∧ 2 * r ≤ j.val) := by omega
        have h5 : ¬ (2 * r ≤ i.val ∧ r ≤ j.val ∧ j.val < 2 * r) := by omega
        simp [h1, h2, h3, h4, h5]
      · intro i j hi hj
        simp only [M, Matrix.of_apply]
        have h1 : ¬ (i.val < r ∧ r ≤ j.val ∧ j.val < 2 * r) := by omega
        have h2 : ¬ (r ≤ i.val ∧ i.val < 2 * r ∧ j.val < r) := by omega
        have h3 : ¬ (r ≤ i.val ∧ i.val < 2 * r ∧ r ≤ j.val ∧ j.val < 2 * r) := by omega
        have h4 : ¬ (r ≤ i.val ∧ i.val < 2 * r ∧ 2 * r ≤ j.val) := by omega
        have h5 : ¬ (2 * r ≤ i.val ∧ r ≤ j.val ∧ j.val < 2 * r) := by omega
        simp [h1, h2, h3, h4, h5]
      · intro a b
        simp only [M, Matrix.of_apply]
        have h1a : a.val < r ∧ r ≤ r + b.val ∧ r + b.val < 2 * r := ⟨a.isLt, by omega, by omega⟩
        have h1b : b.val < r ∧ r ≤ r + a.val ∧ r + a.val < 2 * r := ⟨b.isLt, by omega, by omega⟩
        simp only [h1a, h1b, ↓reduceDIte, Nat.add_sub_cancel_left]
        rcases lt_trichotomy a.val b.val with hlt | heq | hgt
        · have hnot : ¬ b.val < a.val := by omega
          simp [hlt, hnot]
        · have hnot1 : ¬ a.val < b.val := by omega
          have hnot2 : ¬ b.val < a.val := by omega
          simp [hnot1, hnot2]
        · have hnot : ¬ a.val < b.val := by omega
          simp [hgt, hnot]
      · intro a
        simp only [M, Matrix.of_apply]
        have h1a : a.val < r ∧ r ≤ r + a.val ∧ r + a.val < 2 * r := ⟨a.isLt, by omega, by omega⟩
        simp [h1a]
    refine ⟨⟨M, hMmem⟩, ?_⟩
    funext c
    rcases c with ⟨⟨a, b⟩, hlt⟩ | (⟨⟨a, b⟩, hlt⟩ | ⟨a, c⟩)
    · simp only [toCoord, LinearMap.coe_mk, AddHom.coe_mk, M, Matrix.of_apply]
      have h1 : a.val < r ∧ r ≤ r + b.val ∧ r + b.val < 2 * r := ⟨a.isLt, by omega, by omega⟩
      simp [h1, hlt]
    · simp only [toCoord, LinearMap.coe_mk, AddHom.coe_mk, M, Matrix.of_apply]
      have h1 : ¬ (r + a.val < r ∧ r ≤ r + b.val ∧ r + b.val < 2 * r) := by omega
      have h2 : ¬ (r ≤ r + a.val ∧ r + a.val < 2 * r ∧ r + b.val < r) := by omega
      have h3 : r ≤ r + a.val ∧ r + a.val < 2 * r ∧ r ≤ r + b.val ∧ r + b.val < 2 * r :=
        ⟨by omega, by omega, by omega, by omega⟩
      simp [h1, h2, h3, hlt]
    · simp only [toCoord, LinearMap.coe_mk, AddHom.coe_mk, M, Matrix.of_apply]
      have h1 : ¬ (r + a.val < r ∧ r ≤ 2 * r + c.val ∧ 2 * r + c.val < 2 * r) := by omega
      have h2 : ¬ (r ≤ r + a.val ∧ r + a.val < 2 * r ∧ 2 * r + c.val < r) := by omega
      have h3 : ¬ (r ≤ r + a.val ∧ r + a.val < 2 * r ∧ r ≤ 2 * r + c.val ∧ 2 * r + c.val < 2 * r) := by omega
      have h4 : r ≤ r + a.val ∧ r + a.val < 2 * r ∧ 2 * r ≤ 2 * r + c.val := ⟨by omega, by omega, by omega⟩
      rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_pos h4]
      congr 1; congr 1; congr 1
      exact Prod.ext (Fin.ext (by simp)) (Fin.ext (by simp))
  let e : Wstd d r h2r ≃ₗ[F2] (Coord → F2) := LinearEquiv.ofBijective toCoord ⟨hinj, hsurj⟩
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card]
  simp only [Coord, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_pairLt]
  rw [← add_assoc]
  exact two_mul_choose_two_add d r h2r

lemma single_mul_single {d : ℕ} (a b i j : Fin d) :
    (Pi.single a (1 : F2) : Fin d → F2) i * (Pi.single b (1 : F2) : Fin d → F2) j =
      if i = a ∧ j = b then 1 else 0 := by
  by_cases hi : i = a <;> by_cases hj : j = b <;> simp [Pi.single_apply, hi, hj]

lemma sum_indicator_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → F2) (P : ι → Prop) [DecidablePred P] (x0 : ι)
    (hx : P x0) (huniq : ∀ x, P x → x = x0) :
    ∑ x : ι, f x * (if P x then (1 : F2) else 0) = f x0 := by
  rw [sum_eq_single x0]
  · simp [hx]
  · intro x _ hne
    have : ¬ P x := fun h => hne (huniq x h)
    simp [this]
  · intro h; exact absurd (mem_univ x0) h

lemma sum_indicator_zero {ι : Type*} [Fintype ι]
    (f : ι → F2) (P : ι → Prop) [DecidablePred P]
    (hnone : ∀ x, ¬ P x) :
    ∑ x : ι, f x * (if P x then (1 : F2) else 0) = 0 :=
  sum_eq_zero fun x _ => by simp [hnone x]

set_option maxHeartbeats 600000 in
lemma Wstd_rank2_upper {d r : ℕ} (h2r : 2 * r ≤ d) :
    ∃ ps : List ((Fin d → F2) × (Fin d → F2) × (Fin d → F2) × (Fin d → F2)),
      ps.length = r * (d - r - 1) + Nat.choose r 2 ∧
      ∀ M ∈ Wstd d r h2r, M ∈ Submodule.span F2
        {A | ∃ p ∈ ps, A = outerPair p.1 p.2.1 p.2.2.1 p.2.2.2} := by
  classical
  let eVec : Fin d → (Fin d → F2) := fun i => Pi.single i 1
  let psC : List ((Fin d → F2) × (Fin d → F2) × (Fin d → F2) × (Fin d → F2)) :=
    (Finset.univ : Finset (Fin r × Fin (d - 2 * r))).toList.map fun ac =>
      (eVec ⟨r + ac.1.val, by omega⟩, eVec ⟨2 * r + ac.2.val, by omega⟩,
       eVec ⟨2 * r + ac.2.val, by omega⟩, eVec ⟨r + ac.1.val, by omega⟩)
  let psL : List ((Fin d → F2) × (Fin d → F2) × (Fin d → F2) × (Fin d → F2)) :=
    (Finset.univ : Finset (PairLt r)).toList.map fun p =>
      (eVec ⟨r + p.1.1.val, by omega⟩, eVec ⟨r + p.1.2.val, by omega⟩,
       eVec ⟨r + p.1.2.val, by omega⟩, eVec ⟨r + p.1.1.val, by omega⟩)
  let psK1 : List ((Fin d → F2) × (Fin d → F2) × (Fin d → F2) × (Fin d → F2)) :=
    (Finset.univ : Finset (PairLt r)).toList.map fun p =>
      (eVec ⟨p.1.1.val, by omega⟩, eVec ⟨r + p.1.2.val, by omega⟩,
       eVec ⟨p.1.2.val, by omega⟩, eVec ⟨r + p.1.1.val, by omega⟩)
  let psK2 : List ((Fin d → F2) × (Fin d → F2) × (Fin d → F2) × (Fin d → F2)) :=
    (Finset.univ : Finset (PairLt r)).toList.map fun p =>
      (eVec ⟨r + p.1.2.val, by omega⟩, eVec ⟨p.1.1.val, by omega⟩,
       eVec ⟨r + p.1.1.val, by omega⟩, eVec ⟨p.1.2.val, by omega⟩)
  let ps := psC ++ psL ++ psK1 ++ psK2
  have hlen : ps.length = r * (d - r - 1) + Nat.choose r 2 := by
    simp only [ps, psC, psL, psK1, psK2, List.length_append, List.length_map,
      Finset.length_toList, card_univ, Fintype.card_prod, Fintype.card_fin, card_pairLt]
    have := two_mul_choose_two_add d r h2r
    omega
  refine ⟨ps, hlen, fun M hM => ?_⟩
  rcases hM with ⟨⟨hMsym, hMdiag⟩, hMz, hMa, hMb, hMk, hMkd⟩
  have hMsym' : ∀ x y : Fin d, M x y = M y x := fun x y => congrFun (congrFun hMsym y) x
  let Sp := Submodule.span F2 {A | ∃ p ∈ ps, A = outerPair p.1 p.2.1 p.2.2.1 p.2.2.2}
  let EC : Fin r × Fin (d - 2 * r) → Matrix (Fin d) (Fin d) F2 := fun ac =>
    outerPair (eVec ⟨r + ac.1.val, by omega⟩) (eVec ⟨2 * r + ac.2.val, by omega⟩)
      (eVec ⟨2 * r + ac.2.val, by omega⟩) (eVec ⟨r + ac.1.val, by omega⟩)
  let EL : PairLt r → Matrix (Fin d) (Fin d) F2 := fun p =>
    outerPair (eVec ⟨r + p.1.1.val, by omega⟩) (eVec ⟨r + p.1.2.val, by omega⟩)
      (eVec ⟨r + p.1.2.val, by omega⟩) (eVec ⟨r + p.1.1.val, by omega⟩)
  let EK : PairLt r → Matrix (Fin d) (Fin d) F2 := fun p =>
    outerPair (eVec ⟨p.1.1.val, by omega⟩) (eVec ⟨r + p.1.2.val, by omega⟩)
      (eVec ⟨p.1.2.val, by omega⟩) (eVec ⟨r + p.1.1.val, by omega⟩) +
    outerPair (eVec ⟨r + p.1.2.val, by omega⟩) (eVec ⟨p.1.1.val, by omega⟩)
      (eVec ⟨r + p.1.1.val, by omega⟩) (eVec ⟨p.1.2.val, by omega⟩)
  have hEC_mem : ∀ ac, EC ac ∈ Sp := fun ac =>
    Submodule.subset_span ⟨_, by
      simp only [ps, psC, List.mem_append, List.mem_map, Finset.mem_toList, mem_univ, true_and]
      left; left; left; exact ⟨ac, rfl⟩, rfl⟩
  have hEL_mem : ∀ p, EL p ∈ Sp := fun p =>
    Submodule.subset_span ⟨_, by
      simp only [ps, psL, List.mem_append, List.mem_map, Finset.mem_toList, mem_univ, true_and]
      left; left; right; exact ⟨p, rfl⟩, rfl⟩
  have hEK_mem : ∀ p, EK p ∈ Sp := fun p =>
    Submodule.add_mem _
      (Submodule.subset_span ⟨_, by
        simp only [ps, psK1, List.mem_append, List.mem_map, Finset.mem_toList, mem_univ, true_and]
        left; right; exact ⟨p, rfl⟩, rfl⟩)
      (Submodule.subset_span ⟨_, by
        simp only [ps, psK2, List.mem_append, List.mem_map, Finset.mem_toList, mem_univ, true_and]
        right; exact ⟨p, rfl⟩, rfl⟩)
  have hEC_sum : ∀ i j : Fin d,
      (∑ ac : Fin r × Fin (d - 2 * r), M ⟨r + ac.1.val, by omega⟩ ⟨2 * r + ac.2.val, by omega⟩ * EC ac i j) =
      (if r ≤ i.val ∧ i.val < 2 * r ∧ 2 * r ≤ j.val then M i j else 0) +
      (if 2 * r ≤ i.val ∧ r ≤ j.val ∧ j.val < 2 * r then M i j else 0) := by
    intro i j
    simp only [EC, outerPair, Matrix.of_apply, eVec, single_mul_single, mul_add, sum_add_distrib]
    congr 1
    · by_cases h : r ≤ i.val ∧ i.val < 2 * r ∧ 2 * r ≤ j.val
      · rw [if_pos h]
        have h1 := sum_indicator_eq
          (fun ac : Fin r × Fin (d - 2 * r) => M ⟨r + ac.1.val, by omega⟩ ⟨2 * r + ac.2.val, by omega⟩)
          (fun ac => i = ⟨r + ac.1.val, by omega⟩ ∧ j = ⟨2 * r + ac.2.val, by omega⟩)
          (⟨i.val - r, by omega⟩, ⟨j.val - 2 * r, by omega⟩)
          ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩
          (fun ac hac => Prod.ext (Fin.ext (by dsimp only; have := congrArg Fin.val hac.1; simp at this; omega))
            (Fin.ext (by dsimp only; have := congrArg Fin.val hac.2; simp at this; omega)))
        rw [h1]; congr 1 <;> exact Fin.ext (by simp; omega)
      · rw [if_neg h]
        exact sum_indicator_zero _ _ fun ac hac => h ⟨by have := congrArg Fin.val hac.1; simp at this; omega,
          by have := congrArg Fin.val hac.1; simp at this; omega,
          by have := congrArg Fin.val hac.2; simp at this; omega⟩
    · by_cases h : 2 * r ≤ i.val ∧ r ≤ j.val ∧ j.val < 2 * r
      · rw [if_pos h]
        have h1 := sum_indicator_eq
          (fun ac : Fin r × Fin (d - 2 * r) => M ⟨r + ac.1.val, by omega⟩ ⟨2 * r + ac.2.val, by omega⟩)
          (fun ac => i = ⟨2 * r + ac.2.val, by omega⟩ ∧ j = ⟨r + ac.1.val, by omega⟩)
          (⟨j.val - r, by omega⟩, ⟨i.val - 2 * r, by omega⟩)
          ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩
          (fun ac hac => Prod.ext (Fin.ext (by dsimp only; have := congrArg Fin.val hac.2; simp at this; omega))
            (Fin.ext (by dsimp only; have := congrArg Fin.val hac.1; simp at this; omega)))
        rw [h1, hMsym' i j]; congr 1 <;> exact Fin.ext (by simp; omega)
      · rw [if_neg h]
        exact sum_indicator_zero _ _ fun ac hac => h ⟨by have := congrArg Fin.val hac.1; simp at this; omega,
          by have := congrArg Fin.val hac.2; simp at this; omega,
          by have := congrArg Fin.val hac.2; simp at this; omega⟩
  have hEL_sum : ∀ i j : Fin d,
      (∑ p : PairLt r, M ⟨r + p.1.1.val, by omega⟩ ⟨r + p.1.2.val, by omega⟩ * EL p i j) =
      (if r ≤ i.val ∧ i.val < 2 * r ∧ r ≤ j.val ∧ j.val < 2 * r ∧ i.val < j.val then M i j else 0) +
      (if r ≤ i.val ∧ i.val < 2 * r ∧ r ≤ j.val ∧ j.val < 2 * r ∧ j.val < i.val then M i j else 0) := by
    intro i j
    simp only [EL, outerPair, Matrix.of_apply, eVec, single_mul_single, mul_add, sum_add_distrib]
    congr 1
    · by_cases h : r ≤ i.val ∧ i.val < 2 * r ∧ r ≤ j.val ∧ j.val < 2 * r ∧ i.val < j.val
      · rw [if_pos h]
        have h1 := sum_indicator_eq
          (fun p : PairLt r => M ⟨r + p.1.1.val, by omega⟩ ⟨r + p.1.2.val, by omega⟩)
          (fun p => i = ⟨r + p.1.1.val, by omega⟩ ∧ j = ⟨r + p.1.2.val, by omega⟩)
          ⟨(⟨i.val - r, by omega⟩, ⟨j.val - r, by omega⟩), by simp; omega⟩
          ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩
          (fun p hp => Subtype.ext (Prod.ext (Fin.ext (by dsimp only; have := congrArg Fin.val hp.1; simp at this; omega))
            (Fin.ext (by dsimp only; have := congrArg Fin.val hp.2; simp at this; omega))))
        rw [h1]; congr 1 <;> exact Fin.ext (by simp; omega)
      · rw [if_neg h]
        exact sum_indicator_zero _ _ fun p hp => h ⟨by have := congrArg Fin.val hp.1; simp at this; omega,
          by have := congrArg Fin.val hp.1; simp at this; omega,
          by have := congrArg Fin.val hp.2; simp at this; omega,
          by have := congrArg Fin.val hp.2; simp at this; omega,
          by have h1 := congrArg Fin.val hp.1; have h2 := congrArg Fin.val hp.2; have hlt := p.2; simp at h1 h2; omega⟩
    · by_cases h : r ≤ i.val ∧ i.val < 2 * r ∧ r ≤ j.val ∧ j.val < 2 * r ∧ j.val < i.val
      · rw [if_pos h]
        have h1 := sum_indicator_eq
          (fun p : PairLt r => M ⟨r + p.1.1.val, by omega⟩ ⟨r + p.1.2.val, by omega⟩)
          (fun p => i = ⟨r + p.1.2.val, by omega⟩ ∧ j = ⟨r + p.1.1.val, by omega⟩)
          ⟨(⟨j.val - r, by omega⟩, ⟨i.val - r, by omega⟩), by simp; omega⟩
          ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩
          (fun p hp => Subtype.ext (Prod.ext (Fin.ext (by dsimp only; have := congrArg Fin.val hp.2; simp at this; omega))
            (Fin.ext (by dsimp only; have := congrArg Fin.val hp.1; simp at this; omega))))
        rw [h1, hMsym' i j]; congr 1 <;> exact Fin.ext (by simp; omega)
      · rw [if_neg h]
        exact sum_indicator_zero _ _ fun p hp => h ⟨by have := congrArg Fin.val hp.1; simp at this; omega,
          by have := congrArg Fin.val hp.1; simp at this; omega,
          by have := congrArg Fin.val hp.2; simp at this; omega,
          by have := congrArg Fin.val hp.2; simp at this; omega,
          by have h1 := congrArg Fin.val hp.1; have h2 := congrArg Fin.val hp.2; have hlt := p.2; simp at h1 h2; omega⟩
  have hEK_sum : ∀ i j : Fin d,
      (∑ p : PairLt r, M ⟨p.1.1.val, by omega⟩ ⟨r + p.1.2.val, by omega⟩ * EK p i j) =
      ((if i.val < r ∧ r ≤ j.val ∧ j.val < 2 * r ∧ i.val < j.val - r then M i j else 0) +
       (if i.val < r ∧ r ≤ j.val ∧ j.val < 2 * r ∧ j.val - r < i.val then M i j else 0)) +
      ((if r ≤ i.val ∧ i.val < 2 * r ∧ j.val < r ∧ j.val < i.val - r then M i j else 0) +
       (if r ≤ i.val ∧ i.val < 2 * r ∧ j.val < r ∧ i.val - r < j.val then M i j else 0)) := by
    intro i j
    simp only [EK, Matrix.add_apply, outerPair, Matrix.of_apply, eVec, single_mul_single, mul_add, sum_add_distrib]
    congr 1
    · congr 1
      · by_cases h : i.val < r ∧ r ≤ j.val ∧ j.val < 2 * r ∧ i.val < j.val - r
        · rw [if_pos h]
          have h1 := sum_indicator_eq
            (fun p : PairLt r => M ⟨p.1.1.val, by omega⟩ ⟨r + p.1.2.val, by omega⟩)
            (fun p => i = ⟨p.1.1.val, by omega⟩ ∧ j = ⟨r + p.1.2.val, by omega⟩)
            ⟨(⟨i.val, h.1⟩, ⟨j.val - r, by omega⟩), by simp; omega⟩
            ⟨Fin.ext (by simp), Fin.ext (by simp; omega)⟩
            (fun p hp => Subtype.ext (Prod.ext (Fin.ext (by dsimp only; have := congrArg Fin.val hp.1; simp at this; omega))
              (Fin.ext (by dsimp only; have := congrArg Fin.val hp.2; simp at this; omega))))
          rw [h1]; congr 1 <;> exact Fin.ext (by simp; omega)
        · rw [if_neg h]
          exact sum_indicator_zero _ _ fun p hp => h ⟨by have := congrArg Fin.val hp.1; simp at this; omega,
            by have := congrArg Fin.val hp.2; simp at this; omega,
            by have := congrArg Fin.val hp.2; simp at this; omega,
            by have h1 := congrArg Fin.val hp.1; have h2 := congrArg Fin.val hp.2; have hlt := p.2; simp at h1 h2; omega⟩
      · by_cases h : i.val < r ∧ r ≤ j.val ∧ j.val < 2 * r ∧ j.val - r < i.val
        · rw [if_pos h]
          have h1 := sum_indicator_eq
            (fun p : PairLt r => M ⟨p.1.1.val, by omega⟩ ⟨r + p.1.2.val, by omega⟩)
            (fun p => i = ⟨p.1.2.val, by omega⟩ ∧ j = ⟨r + p.1.1.val, by omega⟩)
            ⟨(⟨j.val - r, by omega⟩, ⟨i.val, h.1⟩), by simp; omega⟩
            ⟨Fin.ext (by simp), Fin.ext (by simp; omega)⟩
            (fun p hp => Subtype.ext (Prod.ext (Fin.ext (by dsimp only; have := congrArg Fin.val hp.2; simp at this; omega))
              (Fin.ext (by dsimp only; have := congrArg Fin.val hp.1; simp at this; omega))))
          rw [h1]
          have hsym := hMk ⟨j.val - r, by omega⟩ ⟨i.val, h.1⟩
          rw [hsym]; congr 1 <;> exact Fin.ext (by simp; omega)
        · rw [if_neg h]
          exact sum_indicator_zero _ _ fun p hp => h ⟨by have := congrArg Fin.val hp.1; simp at this; omega,
            by have := congrArg Fin.val hp.2; simp at this; omega,
            by have := congrArg Fin.val hp.2; simp at this; omega,
            by have h1 := congrArg Fin.val hp.1; have h2 := congrArg Fin.val hp.2; have hlt := p.2; simp at h1 h2; omega⟩
    · congr 1
      · by_cases h : r ≤ i.val ∧ i.val < 2 * r ∧ j.val < r ∧ j.val < i.val - r
        · rw [if_pos h]
          have h1 := sum_indicator_eq
            (fun p : PairLt r => M ⟨p.1.1.val, by omega⟩ ⟨r + p.1.2.val, by omega⟩)
            (fun p => i = ⟨r + p.1.2.val, by omega⟩ ∧ j = ⟨p.1.1.val, by omega⟩)
            ⟨(⟨j.val, h.2.2.1⟩, ⟨i.val - r, by omega⟩), by simp; omega⟩
            ⟨Fin.ext (by simp; omega), Fin.ext (by simp)⟩
            (fun p hp => Subtype.ext (Prod.ext (Fin.ext (by dsimp only; have := congrArg Fin.val hp.2; simp at this; omega))
              (Fin.ext (by dsimp only; have := congrArg Fin.val hp.1; simp at this; omega))))
          rw [h1, hMsym' i j]; congr 1 <;> exact Fin.ext (by simp; omega)
        · rw [if_neg h]
          exact sum_indicator_zero _ _ fun p hp => h ⟨by have := congrArg Fin.val hp.1; simp at this; omega,
            by have := congrArg Fin.val hp.1; simp at this; omega,
            by have := congrArg Fin.val hp.2; simp at this; omega,
            by have h1 := congrArg Fin.val hp.1; have h2 := congrArg Fin.val hp.2; have hlt := p.2; simp at h1 h2; omega⟩
      · by_cases h : r ≤ i.val ∧ i.val < 2 * r ∧ j.val < r ∧ i.val - r < j.val
        · rw [if_pos h]
          have h1 := sum_indicator_eq
            (fun p : PairLt r => M ⟨p.1.1.val, by omega⟩ ⟨r + p.1.2.val, by omega⟩)
            (fun p => i = ⟨r + p.1.1.val, by omega⟩ ∧ j = ⟨p.1.2.val, by omega⟩)
            ⟨(⟨i.val - r, by omega⟩, ⟨j.val, h.2.2.1⟩), by simp; omega⟩
            ⟨Fin.ext (by simp; omega), Fin.ext (by simp)⟩
            (fun p hp => Subtype.ext (Prod.ext (Fin.ext (by dsimp only; have := congrArg Fin.val hp.1; simp at this; omega))
              (Fin.ext (by dsimp only; have := congrArg Fin.val hp.2; simp at this; omega))))
          rw [h1, hMsym' i j]
          have hsym := hMk ⟨i.val - r, by omega⟩ ⟨j.val, h.2.2.1⟩
          rw [hsym]; congr 1 <;> exact Fin.ext (by simp; omega)
        · rw [if_neg h]
          exact sum_indicator_zero _ _ fun p hp => h ⟨by have := congrArg Fin.val hp.1; simp at this; omega,
            by have := congrArg Fin.val hp.1; simp at this; omega,
            by have := congrArg Fin.val hp.2; simp at this; omega,
            by have h1 := congrArg Fin.val hp.1; have h2 := congrArg Fin.val hp.2; have hlt := p.2; simp at h1 h2; omega⟩
  have hM_eq : M =
      (∑ ac : Fin r × Fin (d - 2 * r), M ⟨r + ac.1.val, by omega⟩ ⟨2 * r + ac.2.val, by omega⟩ • EC ac) +
      (∑ p : PairLt r, M ⟨r + p.1.1.val, by omega⟩ ⟨r + p.1.2.val, by omega⟩ • EL p) +
      (∑ p : PairLt r, M ⟨p.1.1.val, by omega⟩ ⟨r + p.1.2.val, by omega⟩ • EK p) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hEC_sum i j, hEL_sum i j, hEK_sum i j]
    by_cases hi1 : i.val < r
    · by_cases hj1 : j.val < r
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp only [add_zero, zero_add]
        exact hMz i j (by omega) (by omega)
      · by_cases hj2 : j.val < 2 * r
        · rcases lt_trichotomy i.val (j.val - r) with hlt | heq | hgt
          · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
          · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp only [add_zero, zero_add]
            have h0 := hMkd ⟨i.val, hi1⟩
            convert h0 using 2 <;> exact Fin.ext (by simp; omega)
          · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega)]; simp
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp only [add_zero, zero_add]
          exact hMa i j hi1 (by omega)
    · by_cases hi2 : i.val < 2 * r
      · by_cases hj1 : j.val < r
        · rcases lt_trichotomy j.val (i.val - r) with hlt | heq | hgt
          · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega)]; simp
          · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp only [add_zero, zero_add]
            rw [hMsym' i j]
            have h0 := hMkd ⟨j.val, hj1⟩
            convert h0 using 2 <;> exact Fin.ext (by simp; omega)
          · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]; simp
        · by_cases hj2 : j.val < 2 * r
          · rcases lt_trichotomy i.val j.val with hlt | heq | hgt
            · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
            · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp only [add_zero, zero_add]
              have hij : i = j := Fin.ext heq
              subst hij; exact hMdiag i
            · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
          · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
      · by_cases hj1 : j.val < r
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp only [add_zero, zero_add]
          exact hMb i j (by omega) hj1
        · by_cases hj2 : j.val < 2 * r
          · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp
          · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; simp only [add_zero, zero_add]
            exact hMz i j (by omega) (by omega)
  rw [hM_eq]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact Submodule.sum_mem _ fun ac _ => Submodule.smul_mem _ _ (hEC_mem ac)
  · exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (hEL_mem p)
  · exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (hEK_mem p)

lemma Wstd_rank_le_two_K_zero {d r : ℕ} (h2r : 2 * r ≤ d) {M : Matrix (Fin d) (Fin d) F2}
    (hM : M ∈ Wstd d r h2r) (hrk : IsRankLe2 M) :
    ∀ a b : Fin r, M ⟨a.val, by omega⟩ ⟨r + b.val, by omega⟩ = 0 := by
  rcases hM with ⟨⟨hMsym, hMdiag⟩, hMz, _, _, hMk, hMkd⟩
  obtain ⟨u1, v1, u2, v2, rfl⟩ := hrk
  intro a b
  by_contra hne0
  have hMsym' : ∀ x y : Fin d, outerPair u1 v1 u2 v2 x y = outerPair u1 v1 u2 v2 y x :=
    fun x y => congrFun (congrFun hMsym y) x
  have h1 : outerPair u1 v1 u2 v2 ⟨a.val, by omega⟩ ⟨r + b.val, by omega⟩ = 1 := by
    generalize outerPair u1 v1 u2 v2 ⟨a.val, by omega⟩ ⟨r + b.val, by omega⟩ = x at hne0 ⊢
    fin_cases x
    · exact absurd rfl hne0
    · rfl
  have hab : a ≠ b := by
    intro h; subst h; exact hne0 (hMkd a)
  let idx : Fin 4 → Fin d
    | 0 => ⟨a.val, by omega⟩
    | 1 => ⟨b.val, by omega⟩
    | 2 => ⟨r + a.val, by omega⟩
    | 3 => ⟨r + b.val, by omega⟩
  have hrow_ne_zero : ∀ k : Fin 4, ∃ l : Fin 4, outerPair u1 v1 u2 v2 (idx k) (idx l) = 1 := by
    intro k
    fin_cases k
    · exact ⟨3, h1⟩
    · refine ⟨2, ?_⟩
      change outerPair u1 v1 u2 v2 ⟨b.val, by omega⟩ ⟨r + a.val, by omega⟩ = 1
      rw [← hMk a b]; exact h1
    · refine ⟨1, ?_⟩
      change outerPair u1 v1 u2 v2 ⟨r + a.val, by omega⟩ ⟨b.val, by omega⟩ = 1
      rw [hMsym', ← hMk a b]; exact h1
    · refine ⟨0, ?_⟩
      change outerPair u1 v1 u2 v2 ⟨r + b.val, by omega⟩ ⟨a.val, by omega⟩ = 1
      rw [hMsym']; exact h1
  have hrow_diff : ∀ k1 k2 : Fin 4, k1 ≠ k2 →
      ∃ l : Fin 4, outerPair u1 v1 u2 v2 (idx k1) (idx l) ≠ outerPair u1 v1 u2 v2 (idx k2) (idx l) := by
    have h00 : outerPair u1 v1 u2 v2 (idx 0) (idx 0) = 0 := hMz _ _ (by dsimp [idx]; omega) (by dsimp [idx]; omega)
    have h01 : outerPair u1 v1 u2 v2 (idx 0) (idx 1) = 0 := hMz _ _ (by dsimp [idx]; omega) (by dsimp [idx]; omega)
    have h02 : outerPair u1 v1 u2 v2 (idx 0) (idx 2) = 0 := hMkd a
    have h03 : outerPair u1 v1 u2 v2 (idx 0) (idx 3) = 1 := h1
    have h10 : outerPair u1 v1 u2 v2 (idx 1) (idx 0) = 0 := hMz _ _ (by dsimp [idx]; omega) (by dsimp [idx]; omega)
    have h11 : outerPair u1 v1 u2 v2 (idx 1) (idx 1) = 0 := hMz _ _ (by dsimp [idx]; omega) (by dsimp [idx]; omega)
    have h12 : outerPair u1 v1 u2 v2 (idx 1) (idx 2) = 1 := by
      change outerPair u1 v1 u2 v2 ⟨b.val, by omega⟩ ⟨r + a.val, by omega⟩ = 1
      rw [← hMk a b]; exact h1
    have h13 : outerPair u1 v1 u2 v2 (idx 1) (idx 3) = 0 := hMkd b
    have h20 : outerPair u1 v1 u2 v2 (idx 2) (idx 0) = 0 := by rw [hMsym']; exact h02
    have h21 : outerPair u1 v1 u2 v2 (idx 2) (idx 1) = 1 := by rw [hMsym']; exact h12
    have h30 : outerPair u1 v1 u2 v2 (idx 3) (idx 0) = 1 := by rw [hMsym']; exact h03
    have h31 : outerPair u1 v1 u2 v2 (idx 3) (idx 1) = 0 := by rw [hMsym']; exact h13
    intro k1 k2 hne
    fin_cases k1 <;> fin_cases k2 <;> try exact absurd rfl hne
    · exact ⟨2, by rw [h02, h12]; decide⟩
    · exact ⟨1, by rw [h01, h21]; decide⟩
    · exact ⟨0, by rw [h00, h30]; decide⟩
    · exact ⟨2, by rw [h12, h02]; decide⟩
    · exact ⟨1, by rw [h11, h21]; decide⟩
    · exact ⟨0, by rw [h10, h30]; decide⟩
    · exact ⟨1, by rw [h21, h01]; decide⟩
    · exact ⟨1, by rw [h21, h11]; decide⟩
    · exact ⟨0, by rw [h20, h30]; decide⟩
    · exact ⟨0, by rw [h30, h00]; decide⟩
    · exact ⟨0, by rw [h30, h10]; decide⟩
    · exact ⟨0, by rw [h30, h20]; decide⟩
  let tag : Fin 4 → F2 × F2 := fun k => (u1 (idx k), u2 (idx k))
  have htag_ne0 : ∀ k : Fin 4, tag k ≠ (0, 0) := by
    intro k hk
    have hu1 : u1 (idx k) = 0 := congrArg Prod.fst hk
    have hu2 : u2 (idx k) = 0 := congrArg Prod.snd hk
    obtain ⟨l, hl⟩ := hrow_ne_zero k
    simp [outerPair, hu1, hu2] at hl
  have htag_inj : Function.Injective tag := by
    intro k1 k2 heq
    by_contra hne
    obtain ⟨l, hl⟩ := hrow_diff k1 k2 hne
    apply hl
    have hu1 : u1 (idx k1) = u1 (idx k2) := congrArg Prod.fst heq
    have hu2 : u2 (idx k1) = u2 (idx k2) := congrArg Prod.snd heq
    simp only [outerPair, Matrix.of_apply, hu1, hu2]
  have hcard_le : (Finset.univ : Finset (Fin 4)).card ≤
      ((Finset.univ : Finset (F2 × F2)).erase (0, 0)).card := by
    have him : (Finset.univ.image tag) ⊆ (Finset.univ : Finset (F2 × F2)).erase (0, 0) := by
      intro x hx
      obtain ⟨k, _, rfl⟩ := mem_image.1 hx
      exact mem_erase.2 ⟨htag_ne0 k, mem_univ _⟩
    have h1 := card_le_card him
    rwa [card_image_of_injective _ htag_inj] at h1
  have h4 : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
  have h3 : ((Finset.univ : Finset (F2 × F2)).erase (0, 0)).card = 3 := by decide
  omega

end StandardSpace

lemma outerPair_cong {d : ℕ} (P : Matrix (Fin d) (Fin d) F2) (u1 v1 u2 v2 : Fin d → F2) :
    P * outerPair u1 v1 u2 v2 * Pᵀ = outerPair (P *ᵥ u1) (P *ᵥ v1) (P *ᵥ u2) (P *ᵥ v2) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, outerPair, Matrix.of_apply,
    Matrix.mulVec, dotProduct, mul_add, add_mul, sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  · refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

lemma main_32062 :
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
∀ (d : ℕ) (U : Matrix (Fin d) (Fin d) F), U*U = 1 →
  let Mat := Matrix (Fin d) (Fin d) F
  let alt := fun (H : Mat) => H.transpose = H ∧ ∀ i, H i i = 0
  let r := (U-1).rank
  let table := fun (H : Mat) (x y : Fin (d+1)) =>
    Fin.cases false (fun i => Fin.cases false (fun j => decide (H i j ≠ 0)) y) x
  let D := r*(d-r-1)
  let bank := fun (t : ℕ) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Mat → ℕ),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack ((d+1)+(d+1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
      ∀ H : Mat, alt H →
        (depths ((d+1)+(d+1)) C).getD (tap H) 0 ≤ 1 ∧
        PEqualNP.Represents.Represents (table (U*H*U.transpose + H)) ⟨C.gates, tap H⟩
  bank (D + Nat.choose r 2) ∧ (∀ t : ℕ, bank t → D + (if 2 ≤ r then 1 else 0) ≤ t)
) := by
  classical
  dsimp only
  intro d U hU
  let r := (U - 1).rank
  let D := r * (d - r - 1)
  obtain ⟨h2r, P, Q, hPQ, hQP, hQNP⟩ := involution_normal_form U hU
  have hQUP : Q * U * P = 1 + Nstd d r := by
    have hUeq : U = 1 + (U - 1) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.sub_apply, f2_sub_eq_add]
      rw [add_left_comm, f2_add_self, add_zero]
    calc Q * U * P = Q * (1 + (U - 1)) * P := by rw [← hUeq]
      _ = Q * P + Q * (U - 1) * P := by noncomm_ring
      _ = 1 + Nstd d r := by rw [hQP, hQNP]
  have hU_eq : U = P * (1 + Nstd d r) * Q := by
    calc U = (P * Q) * U * (P * Q) := by rw [hPQ, one_mul, mul_one]
      _ = P * (Q * U * P) * Q := by simp only [Matrix.mul_assoc]
      _ = P * (1 + Nstd d r) * Q := by rw [hQUP]
  have hcong_diff : ∀ H : Matrix (Fin d) (Fin d) F2,
      Q * (U * H * Uᵀ + H) * Qᵀ =
        (1 + Nstd d r) * (Q * H * Qᵀ) * (1 + Nstd d r)ᵀ + (Q * H * Qᵀ) := by
    intro H
    have hQT : Qᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hPQ, Matrix.transpose_one]
    have hPT : Pᵀ * Qᵀ = 1 := by rw [← Matrix.transpose_mul, hQP, Matrix.transpose_one]
    have hUT : Uᵀ = Qᵀ * (1 + Nstd d r)ᵀ * Pᵀ := by
      rw [hU_eq, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [Matrix.mul_add, Matrix.add_mul, hUT, hU_eq]
    congr 1
    calc Q * (P * (1 + Nstd d r) * Q * H * (Qᵀ * (1 + Nstd d r)ᵀ * Pᵀ)) * Qᵀ
        = (Q * P) * (1 + Nstd d r) * (Q * H * Qᵀ) * (1 + Nstd d r)ᵀ * (Pᵀ * Qᵀ) := by
            simp only [Matrix.mul_assoc]
      _ = (1 + Nstd d r) * (Q * H * Qᵀ) * (1 + Nstd d r)ᵀ := by rw [hQP, hPT, one_mul, mul_one]
  have hcong_inv : ∀ M : Matrix (Fin d) (Fin d) F2, P * (Q * M * Qᵀ) * Pᵀ = M := fun M => by
    have hQT : Qᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hPQ, Matrix.transpose_one]
    calc P * (Q * M * Qᵀ) * Pᵀ = (P * Q) * M * (Qᵀ * Pᵀ) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hPQ, hQT, one_mul, mul_one]
  constructor
  ·
    obtain ⟨psStd, hps_len, hps_span⟩ := Wstd_rank2_upper h2r
    let ps := psStd.map fun p => (P *ᵥ p.1, P *ᵥ p.2.1, P *ᵥ p.2.2.1, P *ᵥ p.2.2.2)
    let S : Finset (Matrix (Fin d) (Fin d) F2) :=
      (Finset.univ.filter fun H : Matrix (Fin d) (Fin d) F2 => alt H).image (fun H => U * H * Uᵀ + H)
    have hS_span : ∀ M ∈ S, M ∈ Submodule.span F2
        {A | ∃ p ∈ ps, A = outerPair p.1 p.2.1 p.2.2.1 p.2.2.2} := by
      intro M hM
      obtain ⟨H, hHflt, rfl⟩ := mem_image.1 hM
      have hHalt : alt H := (mem_filter.1 hHflt).2
      have hQH : alt (Q * H * Qᵀ) := alt_cong Q H hHalt
      have hmemW : Q * (U * H * Uᵀ + H) * Qᵀ ∈ Wstd d r h2r :=
        (image_eq_Wstd h2r _).1 ⟨Q * H * Qᵀ, hQH, hcong_diff H⟩
      have hsp := hps_span _ hmemW
      let φ : Matrix (Fin d) (Fin d) F2 →ₗ[F2] Matrix (Fin d) (Fin d) F2 :=
        { toFun := fun A => P * A * Pᵀ
          map_add' := fun A B => by rw [Matrix.mul_add, Matrix.add_mul]
          map_smul' := fun c A => by simp [Matrix.mul_smul, Matrix.smul_mul] }
      have hmap : φ (Q * (U * H * Uᵀ + H) * Qᵀ) ∈
          (Submodule.span F2 {A | ∃ p ∈ psStd, A = outerPair p.1 p.2.1 p.2.2.1 p.2.2.2}).map φ :=
        Submodule.mem_map_of_mem hsp
      rw [Submodule.map_span] at hmap
      have hle : Submodule.span F2 (φ '' {A | ∃ p ∈ psStd, A = outerPair p.1 p.2.1 p.2.2.1 p.2.2.2}) ≤
          Submodule.span F2 {A | ∃ p ∈ ps, A = outerPair p.1 p.2.1 p.2.2.1 p.2.2.2} := by
        refine Submodule.span_mono ?_
        rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨(P *ᵥ p.1, P *ᵥ p.2.1, P *ᵥ p.2.2.1, P *ᵥ p.2.2.2),
          List.mem_map.2 ⟨p, hp, rfl⟩, outerPair_cong P p.1 p.2.1 p.2.2.1 p.2.2.2⟩
      have hval := hle hmap
      rwa [show φ (Q * (U * H * Uᵀ + H) * Qᵀ) = U * H * Uᵀ + H from hcong_inv _] at hval
    obtain ⟨C, tapM, hrb, hfan, hcnt, hrep⟩ := rank2_list_to_circuit ps S hS_span
    have hps_len' : ps.length = D + Nat.choose r 2 := by
      simp only [ps, List.length_map, hps_len, D, r]
    refine ⟨C, fun H => tapM (U * H * Uᵀ + H), hrb, hfan, hps_len' ▸ hcnt, fun H hH => ?_⟩
    have hmemS : U * H * Uᵀ + H ∈ S := mem_image.2 ⟨H, mem_filter.2 ⟨mem_univ _, hH⟩, rfl⟩
    exact hrep _ hmemS
  ·
    rintro t ⟨C, tap, _, hfan, hcnt, hbank⟩
    obtain ⟨Ms, hMs_len, hMs_rk, hMs_wire⟩ := circuit_to_rank2_span (d := d) C.gates hfan
    let MsQ := Ms.map fun M => Q * M * Qᵀ
    have hMsQ_rk : ∀ M ∈ MsQ, IsRankLe2 M := by
      intro M hM
      obtain ⟨M0, hM0, rfl⟩ := List.mem_map.1 hM
      obtain ⟨u1, v1, u2, v2, rfl⟩ := hMs_rk M0 hM0
      exact ⟨Q *ᵥ u1, Q *ᵥ v1, Q *ᵥ u2, Q *ᵥ v2, outerPair_cong Q u1 v1 u2 v2⟩
    have hW_le : Wstd d r h2r ≤ Submodule.span F2 {M | M ∈ MsQ} := by
      intro M hM
      obtain ⟨H', hH'alt, rfl⟩ := (image_eq_Wstd h2r M).2 hM
      let H := P * H' * Pᵀ
      have hHalt : alt H := alt_cong P H' hH'alt
      have ⟨hdep, hrep⟩ := hbank H hHalt
      have hmem0 := (hMs_wire (tap H)).2 hdep
      have hfun_eq : (fun x y : Fin (d + 1) =>
          toF2 ((Circuit.wires ⟨C.gates, 0⟩ (oneEach x y)).getD (tap H) false)) =
          fun x y => toF2 (tableMat (U * H * Uᵀ + H) x y) := by
        funext x y
        exact congrArg toF2 (hrep x y)
      rw [hfun_eq, delta_tableMat] at hmem0
      let ψ : Matrix (Fin d) (Fin d) F2 →ₗ[F2] Matrix (Fin d) (Fin d) F2 :=
        { toFun := fun A => Q * A * Qᵀ
          map_add' := fun A B => by rw [Matrix.mul_add, Matrix.add_mul]
          map_smul' := fun c A => by simp [Matrix.mul_smul, Matrix.smul_mul] }
      have hmap : ψ (U * H * Uᵀ + H) ∈ (Submodule.span F2 {M | M ∈ Ms}).map ψ :=
        Submodule.mem_map_of_mem hmem0
      rw [Submodule.map_span] at hmap
      have hle : Submodule.span F2 (ψ '' {M | M ∈ Ms}) ≤ Submodule.span F2 {M | M ∈ MsQ} := by
        refine Submodule.span_mono ?_
        rintro _ ⟨M0, hM0, rfl⟩
        exact List.mem_map.2 ⟨M0, hM0, rfl⟩
      have hval := hle hmap
      have hQH' : Q * H * Qᵀ = H' := by
        have hPT : Pᵀ * Qᵀ = 1 := by rw [← Matrix.transpose_mul, hQP, Matrix.transpose_one]
        calc Q * (P * H' * Pᵀ) * Qᵀ = (Q * P) * H' * (Pᵀ * Qᵀ) := by simp only [Matrix.mul_assoc]
          _ = H' := by rw [hQP, hPT, one_mul, mul_one]
      have hψeq : ψ (U * H * Uᵀ + H) = (1 + Nstd d r) * H' * (1 + Nstd d r)ᵀ + H' := by
        change Q * (U * H * Uᵀ + H) * Qᵀ = _
        rw [hcong_diff H, hQH']
      rwa [hψeq] at hval
    have hspan_rank : Module.finrank F2 (Submodule.span F2 {M | M ∈ MsQ}) ≤ MsQ.length := by
      have hrange : LinearMap.range (Fintype.linearCombination F2 (fun i : Fin MsQ.length => MsQ.get i)) =
          Submodule.span F2 {M | M ∈ MsQ} := by
        rw [Fintype.range_linearCombination]
        congr 1
        ext M
        simp [List.mem_iff_get]
      rw [← hrange]
      calc Module.finrank F2 (LinearMap.range (Fintype.linearCombination F2 fun i : Fin MsQ.length => MsQ.get i))
          ≤ Module.finrank F2 (Fin MsQ.length → F2) := LinearMap.finrank_range_le _
        _ = MsQ.length := Module.finrank_fin_fun F2
    have hD_le : D ≤ MsQ.length := by
      calc D = Module.finrank F2 (Wstd d r h2r) := (finrank_Wstd h2r).symm
        _ ≤ Module.finrank F2 (Submodule.span F2 {M | M ∈ MsQ}) := Submodule.finrank_mono hW_le
        _ ≤ MsQ.length := hspan_rank
    have hMsQ_le_t : MsQ.length ≤ t := by
      rw [List.length_map]; exact le_trans hMs_len hcnt
    have hD_def : D = (U - 1).rank * (d - (U - 1).rank - 1) := rfl
    by_cases hr2 : 2 ≤ r
    · rw [if_pos hr2]
      by_contra hlt
      have ht_eq : MsQ.length = D := by omega
      have hrank_eq : Module.finrank F2 (Submodule.span F2 {M | M ∈ MsQ}) ≤
          Module.finrank F2 (Wstd d r h2r) := by
        rw [finrank_Wstd h2r, ← hD_def, ← ht_eq]; exact hspan_rank
      have hW_eq : Wstd d r h2r = Submodule.span F2 {M | M ∈ MsQ} :=
        Submodule.eq_of_le_of_finrank_le hW_le hrank_eq
      let i0 : Fin r := ⟨0, by omega⟩
      let i1 : Fin r := ⟨1, by omega⟩
      have hK_zero_all : ∀ M ∈ Wstd d r h2r,
          M ⟨i0.val, by omega⟩ ⟨r + i1.val, by omega⟩ = 0 := by
        intro M hM
        rw [hW_eq] at hM
        refine Submodule.span_induction
          (p := fun A _ => A ⟨i0.val, by omega⟩ ⟨r + i1.val, by omega⟩ = 0) ?_ ?_ ?_ ?_ hM
        · intro A hA
          have hAW : A ∈ Wstd d r h2r := by rw [hW_eq]; exact Submodule.subset_span hA
          exact Wstd_rank_le_two_K_zero h2r hAW (hMsQ_rk A hA) i0 i1
        · rfl
        · intro A B _ _ ha hb; simp [ha, hb]
        · intro c A _ ha; simp [ha]

      let H0 : Matrix (Fin d) (Fin d) F2 := Matrix.of fun i j =>
        if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) then 1 else 0
      have hH0_alt : alt H0 := by
        constructor
        · ext i j; simp only [Matrix.transpose_apply, H0, Matrix.of_apply]; by_cases h : (j.val = 0 ∧ i.val = 1) ∨ (j.val = 1 ∧ i.val = 0) <;> simp_all [or_comm, and_comm]
        · intro i; simp only [H0, Matrix.of_apply]; split_ifs with h <;> first | omega | rfl
      let M0 := (1 + Nstd d r) * H0 * (1 + Nstd d r)ᵀ + H0
      have hM0_mem : M0 ∈ Wstd d r h2r := (image_eq_Wstd h2r M0).1 ⟨H0, hH0_alt, rfl⟩
      have hM0_zero := hK_zero_all M0 hM0_mem
      have hM0_one : M0 ⟨i0.val, by omega⟩ ⟨r + i1.val, by omega⟩ = 1 := by
        dsimp only [M0]
        rw [std_diff_formula h2r H0]
        have h1 : ¬ (r ≤ i0.val ∧ i0.val < 2 * r) := by dsimp [i0]; omega
        have h2 : r ≤ r + i1.val ∧ r + i1.val < 2 * r := by dsimp [i1]; omega
        rw [dif_neg h1, dif_pos h2, dif_neg (fun h => h1 h.1), zero_add, add_zero]
        simp only [H0, Matrix.of_apply, i0, i1]
        rw [if_pos (Or.inl ⟨trivial, by omega⟩)]
      rw [hM0_one] at hM0_zero
      exact one_ne_zero hM0_zero
    · rw [if_neg hr2, add_zero]
      exact le_trans hD_le hMsQ_le_t

end PEqualNP.Outside.L_meta_32062_aux

theorem PEqualNP.Outside.L_meta_32062 :
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
∀ (d : ℕ) (U : Matrix (Fin d) (Fin d) F), U*U = 1 →
  let Mat := Matrix (Fin d) (Fin d) F
  let alt := fun (H : Mat) => H.transpose = H ∧ ∀ i, H i i = 0
  let r := (U-1).rank
  let table := fun (H : Mat) (x y : Fin (d+1)) =>
    Fin.cases false (fun i => Fin.cases false (fun j => decide (H i j ≠ 0)) y) x
  let D := r*(d-r-1)
  let bank := fun (t : ℕ) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Mat → ℕ),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack ((d+1)+(d+1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
      ∀ H : Mat, alt H →
        (depths ((d+1)+(d+1)) C).getD (tap H) 0 ≤ 1 ∧
        PEqualNP.Represents.Represents (table (U*H*U.transpose + H)) ⟨C.gates, tap H⟩
  bank (D + Nat.choose r 2) ∧ (∀ t : ℕ, bank t → D + (if 2 ≤ r then 1 else 0) ≤ t)
) :=
  PEqualNP.Outside.L_meta_32062_aux.main_32062
