import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_30578

open PEqualNP.CircuitLowerBounds PEqualNP.Represents

def nl (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depthList (width : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nl g).toNat])
    (List.replicate width 0)

def wireList (gs : List Gate) (inp : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) inp

def b2f (b : Bool) : ZMod 2 := if b then 1 else 0

def anchor {n m : ℕ} (a : Fin n) (b : Fin m) (f : Fin n → Fin m → ZMod 2)
    (x : Fin n) (y : Fin m) : ZMod 2 :=
  f x y + f x b + f a y + f a b

lemma z2_self_sum (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma z2_two : (2 : ZMod 2) = 0 := by decide

lemma b2f_xor (a b : Bool) : b2f (xor a b) = b2f a + b2f b := by
  cases a <;> cases b <;> decide

lemma b2f_nat_mod2 (k : ℕ) : b2f (k % 2 == 1) = (k : ZMod 2) := by
  have hk : (k : ZMod 2) = ((k % 2 : ℕ) : ZMod 2) := by
    conv_lhs => rw [← Nat.div_add_mod k 2]
    push_cast
    simp [z2_two]
  rw [hk]
  rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
  · rw [h0]; decide
  · rw [h1]; decide

lemma sum_b2f_eq {α : Type*} (S : Finset α) (f : α → Bool) :
    (∑ i ∈ S, b2f (f i)) = b2f (((S.filter (fun i => f i)).card % 2) == 1) := by
  rw [b2f_nat_mod2, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro i _
  cases f i <;> simp [b2f]

lemma b2f_unary (op : GateOp) (x : Bool) :
    b2f (op.eval [x]) =
      b2f (op.eval [false]) + (b2f (op.eval [false]) + b2f (op.eval [true])) * b2f x := by
  cases x
  · simp [b2f]
  · rw [show b2f true = 1 from rfl, mul_one, ← add_assoc, z2_self_sum, zero_add]

lemma b2f_binary (op : GateOp) (x y : Bool) :
    b2f (op.eval [x, y]) =
      b2f (op.eval [false, false]) +
      (b2f (op.eval [false, false]) + b2f (op.eval [true, false])) * b2f x +
      (b2f (op.eval [false, false]) + b2f (op.eval [false, true])) * b2f y +
      b2f (xor (xor (op.eval [false, false]) (op.eval [false, true]))
               (xor (op.eval [true, false]) (op.eval [true, true]))) * (b2f x * b2f y) := by
  rw [b2f_xor, b2f_xor, b2f_xor]
  have h4 : (4 : ZMod 2) = 0 := by decide
  cases x <;> cases y <;>
    simp only [show b2f false = 0 from rfl, show b2f true = 1 from rfl] <;>
    ring_nf <;> simp [z2_two, h4]

lemma getD_append_lt {α : Type*} (xs : List α) (a d : α) {i : ℕ} (hi : i < xs.length) :
    (xs ++ [a]).getD i d = xs.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_eq {α : Type*} (xs : List α) (a d : α) :
    (xs ++ [a]).getD xs.length d = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_append_gt {α : Type*} (xs : List α) (a d : α) {i : ℕ} (hi : xs.length < i) :
    (xs ++ [a]).getD i d = d := by
  have hle : xs.length ≤ i := le_of_lt hi
  have hlen : ([a] : List α).length ≤ i - xs.length := by simp; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hle, List.getElem?_eq_none hlen]
  rfl

lemma wireList_length (gs : List Gate) (inp : List Bool) :
    (wireList gs inp).length = inp.length + gs.length := by
  induction gs generalizing inp with
  | nil => simp [wireList]
  | cons g gs ih =>
    simp only [wireList, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

lemma depthList_length (width : ℕ) (gs : List Gate) :
    (depthList width gs).length = width + gs.length := by
  unfold depthList
  suffices ∀ (init : List ℕ),
      (gs.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nl g).toNat]) init).length =
      init.length + gs.length by
    simpa using this (List.replicate width 0)
  induction gs with
  | nil => intro init; simp
  | cons g gs ih =>
    intro init
    simp only [List.foldl_cons]
    rw [ih]
    simp
    omega

lemma wireList_append_singleton (gs : List Gate) (g : Gate) (inp : List Bool) :
    wireList (gs ++ [g]) inp =
      wireList gs inp ++ [g.op.eval (g.inputs.map fun i => (wireList gs inp).getD i false)] := by
  simp [wireList, List.foldl_append]

lemma depthList_append_singleton (width : ℕ) (gs : List Gate) (g : Gate) :
    depthList width (gs ++ [g]) =
      depthList width gs ++
        [(g.inputs.map (fun a => (depthList width gs).getD a 0)).foldr max 0 + (nl g).toNat] := by
  simp [depthList, List.foldl_append]

lemma oneEach_length {n m : ℕ} (x : Fin n) (y : Fin m) :
    (oneEach x y).length = n + m := by
  simp [oneEach]

lemma oneEach_getD {n m : ℕ} (x : Fin n) (y : Fin m) (i : ℕ) :
    b2f ((oneEach x y).getD i false) =
      (if x.val = i then (1 : ZMod 2) else 0) +
      (if n ≤ i ∧ y.val = i - n then (1 : ZMod 2) else 0) := by
  unfold oneEach
  by_cases h1 : i < n
  · have hnot : ¬ (n ≤ i ∧ y.val = i - n) := by omega
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by simp [h1]), List.getElem?_ofFn]
    simp only [h1, dite_true, Option.getD_some, hnot, ite_false, add_zero, b2f]
    by_cases hx : x.val = i
    · have : (⟨i, h1⟩ : Fin n) = x := Fin.ext hx.symm
      simp [this, hx]
    · have : (⟨i, h1⟩ : Fin n) ≠ x := fun h => hx (congrArg Fin.val h).symm
      simp [this, hx]
  · have hx : x.val ≠ i := by omega
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, hx, ite_false, zero_add]
    by_cases h2 : i - n < m
    · rw [List.getElem?_ofFn]
      simp only [h2, dite_true, Option.getD_some, b2f]
      have hle : n ≤ i := by omega
      by_cases hy : y.val = i - n
      · have : (⟨i - n, h2⟩ : Fin m) = y := Fin.ext hy.symm
        simp [this, hle, hy]
      · have : (⟨i - n, h2⟩ : Fin m) ≠ y := fun h => hy (congrArg Fin.val h).symm
        simp [this, hle, hy]
    · have hy : ¬ (n ≤ i ∧ y.val = i - n) := by omega
      rw [List.getElem?_ofFn]
      simp [h2, hy, b2f]

lemma circuit_decomp_aux (n m : ℕ) (gs : List Gate) (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∀ (r : ℕ), gs.countP nl ≤ r →
    ∃ (u1 u2 : Fin r → Fin n → ZMod 2) (v1 v2 : Fin r → Fin m → ZMod 2),
      (∀ i : ℕ, (depthList (n + m) gs).getD i 0 = 0 →
        ∃ (p : Fin n → ZMod 2) (q : Fin m → ZMod 2),
          ∀ (x : Fin n) (y : Fin m),
            b2f ((wireList gs (oneEach x y)).getD i false) = p x + q y) ∧
      (∀ i : ℕ, (depthList (n + m) gs).getD i 0 ≤ 1 →
        ∃ (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) (c : Fin r → ZMod 2),
          ∀ (x : Fin n) (y : Fin m),
            b2f ((wireList gs (oneEach x y)).getD i false) =
              p x + q y + ∑ k : Fin r, c k * (u1 k x * v1 k y + u2 k x * v2 k y)) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro r _
    refine ⟨0, 0, 0, 0, ?_, ?_⟩
    · intro i _
      refine ⟨fun x => if x.val = i then 1 else 0,
              fun y => if n ≤ i ∧ y.val = i - n then 1 else 0, ?_⟩
      intro x y
      simpa [wireList] using oneEach_getD x y i
    · intro i _
      refine ⟨fun x => if x.val = i then 1 else 0,
              fun y => if n ≤ i ∧ y.val = i - n then 1 else 0, 0, ?_⟩
      intro x y
      simpa [wireList] using oneEach_getD x y i
  | append_singleton gs g ih =>
    intro r hr
    have hfan_gs : ∀ g' ∈ gs, g'.inputs.length ≤ 2 := fun g' hg' =>
      hfan g' (List.mem_append_left _ hg')
    have hfan_g : g.inputs.length ≤ 2 := hfan g (List.mem_append_right _ (List.mem_singleton_self g))
    have hcnt : (gs ++ [g]).countP nl = gs.countP nl + if nl g then 1 else 0 := by
      simp [List.countP_append]
    rw [hcnt] at hr
    by_cases hnl : nl g = true
    · simp only [hnl, ite_true] at hr
      cases r with
      | zero => omega
      | succ r' =>
        obtain ⟨u1, u2, v1, v2, h0, h1⟩ := ih hfan_gs r' (by omega)
        have hlen2 : g.inputs.length = 2 := by
          simp only [nl, Bool.and_eq_true, beq_iff_eq] at hnl
          exact hnl.1
        rcases hinp : g.inputs with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, rest⟩⟩⟩
        · simp [hinp] at hlen2
        · simp [hinp] at hlen2
        · let d0 := (depthList (n + m) gs).getD a0 0
          let d1 := (depthList (n + m) gs).getD a1 0
          let dnew := max d0 d1 + 1
          have hdnew : (g.inputs.map (fun a => (depthList (n + m) gs).getD a 0)).foldr max 0 +
              (nl g).toNat = dnew := by
            simp [hinp, hnl, dnew, d0, d1]
          have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
              (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = true := by
            simp only [nl, Bool.and_eq_true] at hnl
            exact hnl.2
          by_cases hdle : dnew ≤ 1
          · have hd0 : d0 = 0 := by omega
            have hd1 : d1 = 0 := by omega
            obtain ⟨p0, q0, hw0⟩ := h0 a0 hd0
            obtain ⟨p1, q1, hw1⟩ := h0 a1 hd1
            let u1' : Fin (r' + 1) → Fin n → ZMod 2 := Fin.snoc u1 p0
            let v1' : Fin (r' + 1) → Fin m → ZMod 2 := Fin.snoc v1 q1
            let u2' : Fin (r' + 1) → Fin n → ZMod 2 := Fin.snoc u2 p1
            let v2' : Fin (r' + 1) → Fin m → ZMod 2 := Fin.snoc v2 q0
            refine ⟨u1', u2', v1', v2', ?_, ?_⟩
            · intro i hi
              rw [depthList_append_singleton, hdnew] at hi
              rcases lt_trichotomy i (n + m + gs.length) with hlt | heq | hgt
              · have hltD : i < (depthList (n + m) gs).length := by rw [depthList_length]; exact hlt
                rw [getD_append_lt _ _ _ hltD] at hi
                obtain ⟨p, q, hpq⟩ := h0 i hi
                refine ⟨p, q, fun x y => ?_⟩
                rw [wireList_append_singleton, getD_append_lt]
                · exact hpq x y
                · rw [wireList_length, oneEach_length]; exact hlt
              · subst heq
                have heqD : n + m + gs.length = (depthList (n + m) gs).length :=
                  (depthList_length (n + m) gs).symm
                rw [heqD, getD_append_eq] at hi
                omega
              · refine ⟨0, 0, fun x y => ?_⟩
                rw [wireList_append_singleton, getD_append_gt]
                · simp [b2f]
                · rw [wireList_length, oneEach_length]; exact hgt
            · intro i hi
              rw [depthList_append_singleton, hdnew] at hi
              rcases lt_trichotomy i (n + m + gs.length) with hlt | heq | hgt
              · have hltD : i < (depthList (n + m) gs).length := by rw [depthList_length]; exact hlt
                rw [getD_append_lt _ _ _ hltD] at hi
                obtain ⟨p, q, c, hpqc⟩ := h1 i hi
                refine ⟨p, q, Fin.snoc c 0, fun x y => ?_⟩
                rw [wireList_append_singleton, getD_append_lt]
                · rw [hpqc x y, Fin.sum_univ_castSucc]
                  simp [u1', u2', v1', v2']
                · rw [wireList_length, oneEach_length]; exact hlt
              · subst heq
                let c0 := b2f (g.op.eval [false, false])
                let c1 := b2f (g.op.eval [false, false]) + b2f (g.op.eval [true, false])
                let c2 := b2f (g.op.eval [false, false]) + b2f (g.op.eval [false, true])
                refine ⟨fun x => c0 + c1 * p0 x + c2 * p1 x + p0 x * p1 x,
                        fun y => c1 * q0 y + c2 * q1 y + q0 y * q1 y,
                        Fin.snoc 0 1, fun x y => ?_⟩
                have heqW : n + m + gs.length = (wireList gs (oneEach x y)).length := by
                  rw [wireList_length, oneEach_length]
                rw [wireList_append_singleton, heqW, getD_append_eq]
                simp only [hinp, List.map_cons, List.map_nil]
                rw [b2f_binary, hxor, hw0 x y, hw1 x y, Fin.sum_univ_castSucc]
                simp only [b2f, ite_true, Fin.snoc_castSucc, Fin.snoc_last, Pi.zero_apply,
                  zero_mul, Finset.sum_const_zero, zero_add, one_mul, u1', u2', v1', v2',
                  c0, c1, c2]
                ring
              · refine ⟨0, 0, 0, fun x y => ?_⟩
                rw [wireList_append_singleton, getD_append_gt]
                · simp [b2f]
                · rw [wireList_length, oneEach_length]; exact hgt
          · let u1' : Fin (r' + 1) → Fin n → ZMod 2 := Fin.snoc u1 0
            let v1' : Fin (r' + 1) → Fin m → ZMod 2 := Fin.snoc v1 0
            let u2' : Fin (r' + 1) → Fin n → ZMod 2 := Fin.snoc u2 0
            let v2' : Fin (r' + 1) → Fin m → ZMod 2 := Fin.snoc v2 0
            refine ⟨u1', u2', v1', v2', ?_, ?_⟩
            · intro i hi
              rw [depthList_append_singleton, hdnew] at hi
              rcases lt_trichotomy i (n + m + gs.length) with hlt | heq | hgt
              · have hltD : i < (depthList (n + m) gs).length := by rw [depthList_length]; exact hlt
                rw [getD_append_lt _ _ _ hltD] at hi
                obtain ⟨p, q, hpq⟩ := h0 i hi
                refine ⟨p, q, fun x y => ?_⟩
                rw [wireList_append_singleton, getD_append_lt]
                · exact hpq x y
                · rw [wireList_length, oneEach_length]; exact hlt
              · subst heq
                have heqD : n + m + gs.length = (depthList (n + m) gs).length :=
                  (depthList_length (n + m) gs).symm
                rw [heqD, getD_append_eq] at hi
                omega
              · refine ⟨0, 0, fun x y => ?_⟩
                rw [wireList_append_singleton, getD_append_gt]
                · simp [b2f]
                · rw [wireList_length, oneEach_length]; exact hgt
            · intro i hi
              rw [depthList_append_singleton, hdnew] at hi
              rcases lt_trichotomy i (n + m + gs.length) with hlt | heq | hgt
              · have hltD : i < (depthList (n + m) gs).length := by rw [depthList_length]; exact hlt
                rw [getD_append_lt _ _ _ hltD] at hi
                obtain ⟨p, q, c, hpqc⟩ := h1 i hi
                refine ⟨p, q, Fin.snoc c 0, fun x y => ?_⟩
                rw [wireList_append_singleton, getD_append_lt]
                · rw [hpqc x y, Fin.sum_univ_castSucc]
                  simp [u1', u2', v1', v2']
                · rw [wireList_length, oneEach_length]; exact hlt
              · subst heq
                have heqD : n + m + gs.length = (depthList (n + m) gs).length :=
                  (depthList_length (n + m) gs).symm
                rw [heqD, getD_append_eq] at hi
                omega
              · refine ⟨0, 0, 0, fun x y => ?_⟩
                rw [wireList_append_singleton, getD_append_gt]
                · simp [b2f]
                · rw [wireList_length, oneEach_length]; exact hgt
        · simp [hinp] at hlen2
    · have hnlf : nl g = false := Bool.eq_false_iff.mpr hnl
      simp only [hnlf, Bool.false_eq_true, ite_false, add_zero] at hr
      obtain ⟨u1, u2, v1, v2, h0, h1⟩ := ih hfan_gs r hr
      refine ⟨u1, u2, v1, v2, ?_, ?_⟩
      · intro i hi
        rw [depthList_append_singleton] at hi
        rcases lt_trichotomy i (n + m + gs.length) with hlt | heq | hgt
        · have hltD : i < (depthList (n + m) gs).length := by rw [depthList_length]; exact hlt
          rw [getD_append_lt _ _ _ hltD] at hi
          obtain ⟨p, q, hpq⟩ := h0 i hi
          refine ⟨p, q, fun x y => ?_⟩
          rw [wireList_append_singleton, getD_append_lt]
          · exact hpq x y
          · rw [wireList_length, oneEach_length]; exact hlt
        · subst heq
          have heqD : n + m + gs.length = (depthList (n + m) gs).length :=
            (depthList_length (n + m) gs).symm
          rw [heqD, getD_append_eq, hnlf] at hi
          rcases hinp : g.inputs with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, rest⟩⟩⟩
          · refine ⟨fun _ => b2f (g.op.eval []), 0, fun x y => ?_⟩
            have heqW : n + m + gs.length = (wireList gs (oneEach x y)).length := by
              rw [wireList_length, oneEach_length]
            rw [wireList_append_singleton, heqW, getD_append_eq]
            simp [hinp]
          · have hd0 : (depthList (n + m) gs).getD a0 0 = 0 := by
              simp [hinp] at hi; exact hi
            obtain ⟨p0, q0, hw0⟩ := h0 a0 hd0
            let c0 := b2f (g.op.eval [false])
            let c1 := b2f (g.op.eval [false]) + b2f (g.op.eval [true])
            refine ⟨fun x => c0 + c1 * p0 x, fun y => c1 * q0 y, fun x y => ?_⟩
            have heqW : n + m + gs.length = (wireList gs (oneEach x y)).length := by
              rw [wireList_length, oneEach_length]
            rw [wireList_append_singleton, heqW, getD_append_eq]
            simp only [hinp, List.map_cons, List.map_nil]
            rw [b2f_unary, hw0 x y]
            simp only [c0, c1]
            ring
          · simp only [hinp, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
              Bool.toNat_false, add_zero] at hi
            have hd0 : (depthList (n + m) gs).getD a0 0 = 0 := by omega
            have hd1 : (depthList (n + m) gs).getD a1 0 = 0 := by omega
            have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
              simp only [nl, hinp, List.length_cons, List.length_nil, beq_self_eq_true,
                Bool.true_and] at hnlf
              exact hnlf
            obtain ⟨p0, q0, hw0⟩ := h0 a0 hd0
            obtain ⟨p1, q1, hw1⟩ := h0 a1 hd1
            let c0 := b2f (g.op.eval [false, false])
            let c1 := b2f (g.op.eval [false, false]) + b2f (g.op.eval [true, false])
            let c2 := b2f (g.op.eval [false, false]) + b2f (g.op.eval [false, true])
            refine ⟨fun x => c0 + c1 * p0 x + c2 * p1 x,
                    fun y => c1 * q0 y + c2 * q1 y, fun x y => ?_⟩
            have heqW : n + m + gs.length = (wireList gs (oneEach x y)).length := by
              rw [wireList_length, oneEach_length]
            rw [wireList_append_singleton, heqW, getD_append_eq]
            simp only [hinp, List.map_cons, List.map_nil]
            rw [b2f_binary, hxor, hw0 x y, hw1 x y]
            simp only [b2f, Bool.false_eq_true, ite_false, zero_mul, add_zero, c0, c1, c2]
            ring
          · simp [hinp] at hfan_g
        · refine ⟨0, 0, fun x y => ?_⟩
          rw [wireList_append_singleton, getD_append_gt]
          · simp [b2f]
          · rw [wireList_length, oneEach_length]; exact hgt
      · intro i hi
        rw [depthList_append_singleton] at hi
        rcases lt_trichotomy i (n + m + gs.length) with hlt | heq | hgt
        · have hltD : i < (depthList (n + m) gs).length := by rw [depthList_length]; exact hlt
          rw [getD_append_lt _ _ _ hltD] at hi
          obtain ⟨p, q, c, hpqc⟩ := h1 i hi
          refine ⟨p, q, c, fun x y => ?_⟩
          rw [wireList_append_singleton, getD_append_lt]
          · exact hpqc x y
          · rw [wireList_length, oneEach_length]; exact hlt
        · subst heq
          have heqD : n + m + gs.length = (depthList (n + m) gs).length :=
            (depthList_length (n + m) gs).symm
          rw [heqD, getD_append_eq, hnlf] at hi
          rcases hinp : g.inputs with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, rest⟩⟩⟩
          · refine ⟨fun _ => b2f (g.op.eval []), 0, 0, fun x y => ?_⟩
            have heqW : n + m + gs.length = (wireList gs (oneEach x y)).length := by
              rw [wireList_length, oneEach_length]
            rw [wireList_append_singleton, heqW, getD_append_eq]
            simp [hinp]
          · have hd0 : (depthList (n + m) gs).getD a0 0 ≤ 1 := by
              simp [hinp] at hi; exact hi
            obtain ⟨p0, q0, cc0, hw0⟩ := h1 a0 hd0
            let c0 := b2f (g.op.eval [false])
            let c1 := b2f (g.op.eval [false]) + b2f (g.op.eval [true])
            refine ⟨fun x => c0 + c1 * p0 x, fun y => c1 * q0 y, fun k => c1 * cc0 k, fun x y => ?_⟩
            have heqW : n + m + gs.length = (wireList gs (oneEach x y)).length := by
              rw [wireList_length, oneEach_length]
            rw [wireList_append_singleton, heqW, getD_append_eq]
            simp only [hinp, List.map_cons, List.map_nil]
            rw [b2f_unary, hw0 x y]
            simp only [c0, c1, mul_add, Finset.mul_sum, mul_assoc]
            ring
          · simp only [hinp, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
              Bool.toNat_false, add_zero] at hi
            have hd0 : (depthList (n + m) gs).getD a0 0 ≤ 1 := by omega
            have hd1 : (depthList (n + m) gs).getD a1 0 ≤ 1 := by omega
            have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
              simp only [nl, hinp, List.length_cons, List.length_nil, beq_self_eq_true,
                Bool.true_and] at hnlf
              exact hnlf
            obtain ⟨p0, q0, cc0, hw0⟩ := h1 a0 hd0
            obtain ⟨p1, q1, cc1, hw1⟩ := h1 a1 hd1
            let c0 := b2f (g.op.eval [false, false])
            let c1 := b2f (g.op.eval [false, false]) + b2f (g.op.eval [true, false])
            let c2 := b2f (g.op.eval [false, false]) + b2f (g.op.eval [false, true])
            refine ⟨fun x => c0 + c1 * p0 x + c2 * p1 x,
                    fun y => c1 * q0 y + c2 * q1 y,
                    fun k => c1 * cc0 k + c2 * cc1 k, fun x y => ?_⟩
            have heqW : n + m + gs.length = (wireList gs (oneEach x y)).length := by
              rw [wireList_length, oneEach_length]
            rw [wireList_append_singleton, heqW, getD_append_eq]
            simp only [hinp, List.map_cons, List.map_nil]
            rw [b2f_binary, hxor, hw0 x y, hw1 x y]
            simp only [show b2f false = 0 from rfl, zero_mul, add_zero]
            simp only [c0, c1, c2, mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
              mul_assoc]
            ring
          · simp [hinp] at hfan_g
        · refine ⟨0, 0, 0, fun x y => ?_⟩
          rw [wireList_append_singleton, getD_append_gt]
          · simp [b2f]
          · rw [wireList_length, oneEach_length]; exact hgt

lemma anchor_of_decomp {n m r : ℕ} (a : Fin n) (b : Fin m)
    (f : Fin n → Fin m → ZMod 2) (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (c : Fin r → ZMod 2) (u1 u2 : Fin r → Fin n → ZMod 2) (v1 v2 : Fin r → Fin m → ZMod 2)
    (hf : ∀ x y, f x y = p x + q y + ∑ k : Fin r, c k * (u1 k x * v1 k y + u2 k x * v2 k y))
    (x : Fin n) (y : Fin m) :
    anchor a b f x y =
      ∑ k : Fin r, c k * ((u1 k x + u1 k a) * (v1 k y + v1 k b) +
        (u2 k x + u2 k a) * (v2 k y + v2 k b)) := by
  unfold anchor
  rw [hf x y, hf x b, hf a y, hf a b]
  have hlin : (p x + q y) + (p x + q b) + (p a + q y) + (p a + q b) = 0 := by
    ring_nf
    simp [z2_two]
  have hsum :
      (∑ k : Fin r, c k * (u1 k x * v1 k y + u2 k x * v2 k y)) +
      (∑ k : Fin r, c k * (u1 k x * v1 k b + u2 k x * v2 k b)) +
      (∑ k : Fin r, c k * (u1 k a * v1 k y + u2 k a * v2 k y)) +
      (∑ k : Fin r, c k * (u1 k a * v1 k b + u2 k a * v2 k b)) =
      ∑ k : Fin r, c k * ((u1 k x + u1 k a) * (v1 k y + v1 k b) +
        (u2 k x + u2 k a) * (v2 k y + v2 k b)) := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  calc
    (p x + q y + ∑ k : Fin r, c k * (u1 k x * v1 k y + u2 k x * v2 k y)) +
      (p x + q b + ∑ k : Fin r, c k * (u1 k x * v1 k b + u2 k x * v2 k b)) +
      (p a + q y + ∑ k : Fin r, c k * (u1 k a * v1 k y + u2 k a * v2 k y)) +
      (p a + q b + ∑ k : Fin r, c k * (u1 k a * v1 k b + u2 k a * v2 k b))
        = ((p x + q y) + (p x + q b) + (p a + q y) + (p a + q b)) +
          ((∑ k : Fin r, c k * (u1 k x * v1 k y + u2 k x * v2 k y)) +
           (∑ k : Fin r, c k * (u1 k x * v1 k b + u2 k x * v2 k b)) +
           (∑ k : Fin r, c k * (u1 k a * v1 k y + u2 k a * v2 k y)) +
           (∑ k : Fin r, c k * (u1 k a * v1 k b + u2 k a * v2 k b))) := by ring
    _ = ∑ k : Fin r, c k * ((u1 k x + u1 k a) * (v1 k y + v1 k b) +
          (u2 k x + u2 k a) * (v2 k y + v2 k b)) := by rw [hlin, zero_add, hsum]

lemma fits_decomp {n m g s : ℕ} (T : Fin g → Fin n → Fin m → Bool) (a : Fin n) (b : Fin m)
    (C : Circuit) (tap : Fin g → ℕ)
    (hfan : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2)
    (hcnt : C.gates.countP nl ≤ s)
    (htap : ∀ j : Fin g, (depthList (n + m) C.gates).getD (tap j) 0 ≤ 1 ∧
      Represents (T j) ⟨C.gates, tap j⟩) :
    ∃ (W : Fin g → Fin s → ZMod 2)
      (u1 u2 : Fin s → Fin n → ZMod 2)
      (v1 v2 : Fin s → Fin m → ZMod 2),
      ∀ (j : Fin g) (x : Fin n) (y : Fin m),
        anchor a b (fun x y => b2f (T j x y)) x y =
          ∑ k : Fin s, W j k * (u1 k x * v1 k y + u2 k x * v2 k y) := by
  obtain ⟨u1, u2, v1, v2, _, h1⟩ := circuit_decomp_aux n m C.gates hfan s hcnt
  have hex : ∀ j : Fin g, ∃ (p : Fin n → ZMod 2) (q : Fin m → ZMod 2) (c : Fin s → ZMod 2),
      ∀ x y, b2f (T j x y) =
        p x + q y + ∑ k : Fin s, c k * (u1 k x * v1 k y + u2 k x * v2 k y) := by
    intro j
    obtain ⟨p, q, c, hpc⟩ := h1 (tap j) (htap j).1
    refine ⟨p, q, c, fun x y => ?_⟩
    have hrep : (wireList C.gates (oneEach x y)).getD (tap j) false = T j x y := (htap j).2 x y
    rw [← hrep]
    exact hpc x y
  choose p q W hW using hex
  refine ⟨W,
    fun k x => u1 k x + u1 k a,
    fun k x => u2 k x + u2 k a,
    fun k y => v1 k y + v1 k b,
    fun k y => v2 k y + v2 k b, ?_⟩
  intro j x y
  exact anchor_of_decomp a b (fun x y => b2f (T j x y)) (p j) (q j) (W j) u1 u2 v1 v2 (hW j) x y

lemma anchor_add {n m : ℕ} (a : Fin n) (b : Fin m)
    (f g : Fin n → Fin m → ZMod 2) (x : Fin n) (y : Fin m) :
    anchor a b (fun x y => f x y + g x y) x y = anchor a b f x y + anchor a b g x y := by
  unfold anchor
  ring

lemma anchor_sum {α : Type*} {n m : ℕ} (a : Fin n) (b : Fin m)
    (S : Finset α) (f : α → Fin n → Fin m → ZMod 2) (x : Fin n) (y : Fin m) :
    anchor a b (fun x y => ∑ i ∈ S, f i x y) x y = ∑ i ∈ S, anchor a b (f i) x y := by
  unfold anchor
  simp only [Finset.sum_add_distrib]

end PEqualNP.Outside.L_meta_30578

theorem PEqualNP.Outside.L_meta_30578 :
(
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let fits := fun (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) =>
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
    ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
      PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩

let F := ZMod 2
∀ (n m g s : ℕ) (T : Fin g → Fin n → Fin m → Bool) (a : Fin n) (b : Fin m),
  fits n m g T s →
  ∃ W : Fin g → Fin s → F,
    ∀ (q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (S : Fin q → Finset (Fin g))
        (t : Fin q → ℕ),
      (∀ j, fits n m 1 (fun _ x y => xor (G j x y)
        ((((S j).filter (fun i => T i x y)).card % 2) == 1)) (t j)) →
      let v := fun j x y => if G j x y then (1 : F) else 0
      let A := fun j x y => v j x y + v j x b + v j a y + v j a b
      ∀ (h : ℕ) (P : Fin h → Finset (Fin q)),
        let coeff := fun (l : Fin h) (i : Fin s) => ∑ j ∈ P l, ∑ u ∈ S j, W u i
        let active := (Finset.univ : Finset (Fin s)).filter (fun i =>
          ∃ l : Fin h, coeff l i ≠ 0)
        let used := (Finset.univ : Finset (Fin h)).biUnion P
        let H : Matrix (Fin n) (Fin h × Fin m) F := fun x ly => ∑ j ∈ P ly.1, A j x ly.2
        let V : Matrix (Fin h × Fin n) (Fin m) F := fun lx y => ∑ j ∈ P lx.1, A j lx.2 y
        max H.rank V.rank ≤ 2 * (active.card + ∑ j ∈ used, t j)) := by
  dsimp only
  intro n m g s T a b hfitsT
  rcases hfitsT with ⟨CT, tapT, _, hfanT, hcntT, htapT⟩
  obtain ⟨W, u1, u2, v1, v2, hT⟩ :=
    PEqualNP.Outside.L_meta_30578.fits_decomp T a b CT tapT hfanT hcntT htapT
  refine ⟨W, ?_⟩
  intro q G S t hfitsD h P
  have hexE : ∀ j : Fin q,
      ∃ (p1 p2 : Fin (t j) → Fin n → ZMod 2) (q1 q2 : Fin (t j) → Fin m → ZMod 2),
        ∀ (x : Fin n) (y : Fin m),
          PEqualNP.Outside.L_meta_30578.anchor a b
            (fun x y => PEqualNP.Outside.L_meta_30578.b2f
              (xor (G j x y) ((((S j).filter (fun i => T i x y)).card % 2) == 1))) x y =
            ∑ r : Fin (t j), (p1 r x * q1 r y + p2 r x * q2 r y) := by
    intro j
    rcases hfitsD j with ⟨CD, tapD, _, hfanD, hcntD, htapD⟩
    obtain ⟨WD, p1, p2, q1, q2, hD⟩ :=
      PEqualNP.Outside.L_meta_30578.fits_decomp
        (fun (_ : Fin 1) x y => xor (G j x y) ((((S j).filter (fun i => T i x y)).card % 2) == 1))
        a b CD tapD hfanD hcntD htapD
    refine ⟨fun r x => WD 0 r * p1 r x, fun r x => WD 0 r * p2 r x, q1, q2, fun x y => ?_⟩
    rw [hD 0 x y]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  choose p1 p2 q1 q2 hE using hexE
  let v : Fin q → Fin n → Fin m → ZMod 2 := fun j x y => if G j x y then (1 : ZMod 2) else 0
  let A : Fin q → Fin n → Fin m → ZMod 2 := fun j x y => v j x y + v j x b + v j a y + v j a b
  have hA : ∀ (j : Fin q) (x : Fin n) (y : Fin m),
      A j x y =
        (∑ u ∈ S j, ∑ k : Fin s, W u k * (u1 k x * v1 k y + u2 k x * v2 k y)) +
        ∑ r : Fin (t j), (p1 j r x * q1 j r y + p2 j r x * q2 j r y) := by
    intro j x y
    have hxor_eq : ∀ x' y',
        v j x' y' =
          (∑ u ∈ S j, PEqualNP.Outside.L_meta_30578.b2f (T u x' y')) +
          PEqualNP.Outside.L_meta_30578.b2f
            (xor (G j x' y') ((((S j).filter (fun i => T i x' y')).card % 2) == 1)) := by
      intro x' y'
      rw [PEqualNP.Outside.L_meta_30578.b2f_xor, ← PEqualNP.Outside.L_meta_30578.sum_b2f_eq]
      have hself := PEqualNP.Outside.L_meta_30578.z2_self_sum
        (∑ u ∈ S j, PEqualNP.Outside.L_meta_30578.b2f (T u x' y'))
      change PEqualNP.Outside.L_meta_30578.b2f (G j x' y') = _
      calc
        PEqualNP.Outside.L_meta_30578.b2f (G j x' y')
            = PEqualNP.Outside.L_meta_30578.b2f (G j x' y') + 0 := (add_zero _).symm
        _ = PEqualNP.Outside.L_meta_30578.b2f (G j x' y') +
            ((∑ u ∈ S j, PEqualNP.Outside.L_meta_30578.b2f (T u x' y')) +
             (∑ u ∈ S j, PEqualNP.Outside.L_meta_30578.b2f (T u x' y'))) := by rw [hself]
        _ = _ := by ring
    have hA_eq : A j x y = PEqualNP.Outside.L_meta_30578.anchor a b (v j) x y := rfl
    rw [hA_eq]
    have hfun : v j = fun x' y' =>
        (∑ u ∈ S j, PEqualNP.Outside.L_meta_30578.b2f (T u x' y')) +
        PEqualNP.Outside.L_meta_30578.b2f
          (xor (G j x' y') ((((S j).filter (fun i => T i x' y')).card % 2) == 1)) := by
      funext x' y'
      exact hxor_eq x' y'
    rw [hfun, PEqualNP.Outside.L_meta_30578.anchor_add, PEqualNP.Outside.L_meta_30578.anchor_sum, hE j x y]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    exact hT u x y
  let coeff : Fin h → Fin s → ZMod 2 := fun l i => ∑ j ∈ P l, ∑ u ∈ S j, W u i
  let active : Finset (Fin s) :=
    (Finset.univ : Finset (Fin s)).filter (fun i => ∃ l : Fin h, coeff l i ≠ 0)
  let used : Finset (Fin q) := (Finset.univ : Finset (Fin h)).biUnion P
  let H : Matrix (Fin n) (Fin h × Fin m) (ZMod 2) := fun x ly => ∑ j ∈ P ly.1, A j x ly.2
  let V : Matrix (Fin h × Fin n) (Fin m) (ZMod 2) := fun lx y => ∑ j ∈ P lx.1, A j lx.2 y
  have hsumA : ∀ (l : Fin h) (x : Fin n) (y : Fin m),
      ∑ j ∈ P l, A j x y =
        (∑ i ∈ active, coeff l i * (u1 i x * v1 i y + u2 i x * v2 i y)) +
        ∑ j ∈ used, (if j ∈ P l then (1 : ZMod 2) else 0) *
          ∑ r : Fin (t j), (p1 j r x * q1 j r y + p2 j r x * q2 j r y) := by
    intro l x y
    simp_rw [hA, Finset.sum_add_distrib]
    congr 1
    · trans (∑ i : Fin s, coeff l i * (u1 i x * v1 i y + u2 i x * v2 i y))
      · simp only [coeff, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
      · symm
        refine Finset.sum_subset (Finset.subset_univ active) ?_
        intro i _ hi
        have hzero : coeff l i = 0 := by
          by_contra hne
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, l, hne⟩)
        simp [hzero]
    · have hsub : P l ⊆ used := Finset.subset_biUnion_of_mem P (Finset.mem_univ l)
      symm
      have hfilt : used.filter (fun j => j ∈ P l) = P l := by
        ext j
        simp only [Finset.mem_filter]
        exact ⟨fun hj => hj.2, fun hj => ⟨hsub hj, hj⟩⟩
      simp only [ite_mul, one_mul, zero_mul]
      rw [← Finset.sum_filter, hfilt, Finset.sum_add_distrib]
  let K := ({i : Fin s // i ∈ active} × Bool) ⊕
    (Σ j : {j : Fin q // j ∈ used}, Fin (t j.1) × Bool)
  have hcardK : Fintype.card K = 2 * (active.card + ∑ j ∈ used, t j) := by
    simp only [K, Fintype.card_sum, Fintype.card_prod, Fintype.card_sigma,
      Fintype.card_coe, Fintype.card_bool, Fintype.card_fin]
    rw [← Finset.attach_eq_univ, Finset.sum_attach used (fun j => t j * 2)]
    rw [← Finset.sum_mul]
    ring
  let LH : Matrix (Fin n) K (ZMod 2) := fun x k =>
    match k with
    | Sum.inl (i, false) => u1 i.1 x
    | Sum.inl (i, true) => u2 i.1 x
    | Sum.inr ⟨j, r, false⟩ => p1 j.1 r x
    | Sum.inr ⟨j, r, true⟩ => p2 j.1 r x
  let RH : Matrix K (Fin h × Fin m) (ZMod 2) := fun k ly =>
    match k with
    | Sum.inl (i, false) => coeff ly.1 i.1 * v1 i.1 ly.2
    | Sum.inl (i, true) => coeff ly.1 i.1 * v2 i.1 ly.2
    | Sum.inr ⟨j, r, false⟩ => (if j.1 ∈ P ly.1 then (1 : ZMod 2) else 0) * q1 j.1 r ly.2
    | Sum.inr ⟨j, r, true⟩ => (if j.1 ∈ P ly.1 then (1 : ZMod 2) else 0) * q2 j.1 r ly.2
  have hH : H = LH * RH := by
    ext x ⟨l, y⟩
    show ∑ j ∈ P l, A j x y = (LH * RH) x (l, y)
    rw [hsumA l x y, Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fintype.sum_sigma]
    simp only [LH, RH, Fintype.sum_prod_type, Fintype.sum_bool]
    congr 1
    · rw [← Finset.attach_eq_univ]
      rw [Finset.sum_attach active (fun i =>
        u2 i x * (coeff l i * v2 i y) + u1 i x * (coeff l i * v1 i y))]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    · rw [← Finset.attach_eq_univ]
      rw [Finset.sum_attach used (fun j =>
        ∑ r : Fin (t j), (p2 j r x * ((if j ∈ P l then (1 : ZMod 2) else 0) * q2 j r y) +
          p1 j r x * ((if j ∈ P l then (1 : ZMod 2) else 0) * q1 j r y)))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
  let LV : Matrix (Fin h × Fin n) K (ZMod 2) := fun lx k =>
    match k with
    | Sum.inl (i, false) => coeff lx.1 i.1 * u1 i.1 lx.2
    | Sum.inl (i, true) => coeff lx.1 i.1 * u2 i.1 lx.2
    | Sum.inr ⟨j, r, false⟩ => (if j.1 ∈ P lx.1 then (1 : ZMod 2) else 0) * p1 j.1 r lx.2
    | Sum.inr ⟨j, r, true⟩ => (if j.1 ∈ P lx.1 then (1 : ZMod 2) else 0) * p2 j.1 r lx.2
  let RV : Matrix K (Fin m) (ZMod 2) := fun k y =>
    match k with
    | Sum.inl (i, false) => v1 i.1 y
    | Sum.inl (i, true) => v2 i.1 y
    | Sum.inr ⟨j, r, false⟩ => q1 j.1 r y
    | Sum.inr ⟨j, r, true⟩ => q2 j.1 r y
  have hV : V = LV * RV := by
    ext ⟨l, x⟩ y
    show ∑ j ∈ P l, A j x y = (LV * RV) (l, x) y
    rw [hsumA l x y, Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fintype.sum_sigma]
    simp only [LV, RV, Fintype.sum_prod_type, Fintype.sum_bool]
    congr 1
    · rw [← Finset.attach_eq_univ]
      rw [Finset.sum_attach active (fun i =>
        coeff l i * u2 i x * v2 i y + coeff l i * u1 i x * v1 i y)]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    · rw [← Finset.attach_eq_univ]
      rw [Finset.sum_attach used (fun j =>
        ∑ r : Fin (t j), ((if j ∈ P l then (1 : ZMod 2) else 0) * p2 j r x * q2 j r y +
          (if j ∈ P l then (1 : ZMod 2) else 0) * p1 j r x * q1 j r y))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
  have hrankH : H.rank ≤ 2 * (active.card + ∑ j ∈ used, t j) := by
    calc
      H.rank = (LH * RH).rank := by rw [hH]
      _ ≤ LH.rank := Matrix.rank_mul_le_left LH RH
      _ ≤ Fintype.card K := Matrix.rank_le_card_width LH
      _ = 2 * (active.card + ∑ j ∈ used, t j) := hcardK
  have hrankV : V.rank ≤ 2 * (active.card + ∑ j ∈ used, t j) := by
    calc
      V.rank = (LV * RV).rank := by rw [hV]
      _ ≤ LV.rank := Matrix.rank_mul_le_left LV RV
      _ ≤ Fintype.card K := Matrix.rank_le_card_width LV
      _ = 2 * (active.card + ∑ j ∈ used, t j) := hcardK
  exact max_le hrankH hrankV
