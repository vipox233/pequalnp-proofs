import PEqualNP.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_meta_33595_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def nonlinearG (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depthsList (w : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinearG g).toNat])
    (List.replicate w 0)

def wiresList (x : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

lemma b2z_false : b2z false = 0 := rfl
lemma b2z_true : b2z true = 1 := rfl

lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_not (a : Bool) : b2z (!a) = 1 + b2z a := by
  cases a <;> decide

lemma b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> simp_all [b2z]

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

lemma zmod2_eq_iff_add_eq_zero (a b : ZMod 2) : a = b ↔ a + b = 0 := by
  revert a b; decide

lemma zmod2_ne_iff_add_eq_one (a b : ZMod 2) : a ≠ b ↔ a + b = 1 := by
  revert a b; decide

lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert a h; decide

lemma zmod2_eq_zero_of_ne_one {a : ZMod 2} (h : a ≠ 1) : a = 0 := by
  revert a h; decide

lemma b2z_decide_eq_one (z : ZMod 2) : b2z (decide (z = 1)) = z := by
  revert z; decide

def chi (u : ZMod 2) : ℤ := if u = 0 then 1 else -1

lemma chi_zero : chi 0 = 1 := rfl
lemma chi_one : chi 1 = -1 := by decide

lemma chi_add (a b : ZMod 2) : chi (a + b) = chi a * chi b := by
  revert a b; decide

lemma chi_b2z_ne (a b : Bool) :
    chi (b2z a + b2z b) = if a ≠ b then (-1 : ℤ) else 1 := by
  cases a <;> cases b <;> decide

lemma sum_chi_dot {d : ℕ} (v : Fin d → ZMod 2) :
    ∑ z : Fin d → ZMod 2, chi (dotProduct v z) = if v = 0 then (2 ^ d : ℤ) else 0 := by
  by_cases hv : v = 0
  · subst hv
    simp [chi]
  · simp only [hv, ↓reduceIte]
    have hex : ∃ k : Fin d, v k ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    obtain ⟨k, hk⟩ := hex
    have hk1 : v k = 1 := zmod2_eq_one_of_ne_zero hk
    let flip : (Fin d → ZMod 2) ≃ (Fin d → ZMod 2) :=
      { toFun := fun z => Function.update z k (z k + 1)
        invFun := fun z => Function.update z k (z k + 1)
        left_inv := fun z => by
          funext j
          by_cases hj : j = k
          · subst hj; simp [add_assoc, zmod2_add_self]
          · simp [hj]
        right_inv := fun z => by
          funext j
          by_cases hj : j = k
          · subst hj; simp [add_assoc, zmod2_add_self]
          · simp [hj] }
    have hdot : ∀ z : Fin d → ZMod 2, dotProduct v (flip z) = dotProduct v z + 1 := by
      intro z
      unfold dotProduct
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
      have hrest : ∑ x ∈ Finset.univ.erase k, v x * flip z x =
          ∑ x ∈ Finset.univ.erase k, v x * z x := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [flip, Finset.ne_of_mem_erase hx]
      rw [hrest]
      have hf : flip z k = z k + 1 := by simp [flip]
      rw [hk1, one_mul, hf]
      ring
    have hneg : ∑ z : Fin d → ZMod 2, chi (dotProduct v z) =
        -(∑ z : Fin d → ZMod 2, chi (dotProduct v z)) := by
      calc ∑ z, chi (dotProduct v z)
          = ∑ z, chi (dotProduct v (flip z)) := (Equiv.sum_comp flip _).symm
        _ = ∑ z, chi (dotProduct v z + 1) := by simp_rw [hdot]
        _ = ∑ z, (chi (dotProduct v z) * (-1)) := by simp_rw [chi_add, chi_one]
        _ = -(∑ z, chi (dotProduct v z)) := by simp [Finset.sum_neg_distrib]
    omega

lemma gate_affine_of_not_nonlinear (g : Gate) (hlen : g.inputs.length ≤ 2)
    (hnl : nonlinearG g = false) :
    ∃ (c0 : ZMod 2) (c1 c2 : ZMod 2), ∀ (vals : List Bool), vals.length = g.inputs.length →
      b2z (g.op.eval vals) = c0 + c1 * b2z (vals.getD 0 false) + c2 * b2z (vals.getD 1 false) := by
  cases hlen_eq : g.inputs.length with
  | zero =>
    refine ⟨b2z (g.op.eval []), 0, 0, ?_⟩
    intro vals hv
    cases vals with
    | nil => simp
    | cons _ _ => simp at hv
  | succ k =>
    cases k with
    | zero =>
      refine ⟨b2z (g.op.eval [false]), b2z (g.op.eval [true]) + b2z (g.op.eval [false]), 0, ?_⟩
      intro vals hv
      rcases vals with _ | ⟨a, _ | ⟨_, _⟩⟩
      · simp at hv
      · cases a
        · simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
            List.getElem?_nil, Option.getD_some, Option.getD_none, b2z_false, mul_zero, add_zero]
        · simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
            List.getElem?_nil, Option.getD_some, Option.getD_none, b2z_true, b2z_false, mul_one, mul_zero, add_zero]
          have := zmod2_add_self (b2z (g.op.eval [false]))
          linear_combination -this
      · simp at hv
    | succ k' =>
      cases k' with
      | zero =>
        have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
            (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
          simpa [nonlinearG, hlen_eq] using hnl
        have hsum0 : b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true]) +
            b2z (g.op.eval [true, false]) + b2z (g.op.eval [true, true]) = 0 := by
          have := congrArg b2z hxor
          rw [b2z_xor, b2z_xor, b2z_xor, b2z_false] at this
          simpa [add_assoc] using this
        refine ⟨b2z (g.op.eval [false, false]),
                b2z (g.op.eval [true, false]) + b2z (g.op.eval [false, false]),
                b2z (g.op.eval [false, true]) + b2z (g.op.eval [false, false]), ?_⟩
        intro vals hv
        rcases vals with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩
        · simp at hv
        · simp at hv
        · cases a <;> cases b
          · simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
              Option.getD_some, b2z_false, mul_zero, add_zero]
          · simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
              Option.getD_some, b2z_false, b2z_true, mul_zero, mul_one, add_zero]
            have := zmod2_add_self (b2z (g.op.eval [false, false]))
            linear_combination -this
          · simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
              Option.getD_some, b2z_false, b2z_true, mul_zero, mul_one, add_zero]
            have := zmod2_add_self (b2z (g.op.eval [false, false]))
            linear_combination -this
          · simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
              Option.getD_some, b2z_true, mul_one]
            have h1 := zmod2_add_self (b2z (g.op.eval [false, false]))
            have h2 := zmod2_add_self (b2z (g.op.eval [false, true]))
            have h3 := zmod2_add_self (b2z (g.op.eval [true, false]))
            linear_combination hsum0 - 2 * h1 - h2 - h3
        · simp at hv
      | succ _ => omega

lemma gate_quad_of_nonlinear (g : Gate) (hnl : nonlinearG g = true) :
    g.inputs.length = 2 ∧
    ∃ (c0 c1 c2 : ZMod 2), ∀ (a b : Bool),
      b2z (g.op.eval [a, b]) = c0 + c1 * b2z a + c2 * b2z b + b2z a * b2z b := by
  have hlen : g.inputs.length = 2 := by
    have := (Bool.and_eq_true _ _).mp hnl
    exact beq_iff_eq.mp this.1
  have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = true := by
    exact ((Bool.and_eq_true _ _).mp hnl).2
  have hsum1 : b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true]) +
      b2z (g.op.eval [true, false]) + b2z (g.op.eval [true, true]) = 1 := by
    have := congrArg b2z hxor
    rw [b2z_xor, b2z_xor, b2z_xor, b2z_true] at this
    simpa [add_assoc] using this
  refine ⟨hlen, b2z (g.op.eval [false, false]),
    b2z (g.op.eval [true, false]) + b2z (g.op.eval [false, false]),
    b2z (g.op.eval [false, true]) + b2z (g.op.eval [false, false]), ?_⟩
  intro a b
  cases a <;> cases b
  · simp only [b2z_false, mul_zero, add_zero]
  · simp only [b2z_false, b2z_true, mul_zero, mul_one, add_zero]
    have := zmod2_add_self (b2z (g.op.eval [false, false]))
    linear_combination -this
  · simp only [b2z_false, b2z_true, mul_zero, mul_one, add_zero]
    have := zmod2_add_self (b2z (g.op.eval [false, false]))
    linear_combination -this
  · simp only [b2z_true, mul_one]
    have h1 := zmod2_add_self (b2z (g.op.eval [false, false]))
    have h2 := zmod2_add_self (b2z (g.op.eval [false, true]))
    have h3 := zmod2_add_self (b2z (g.op.eval [true, false]))
    linear_combination hsum1 - 2 * h1 - h2 - h3

lemma foldl_append_step {α β : Type*} (f : List α → β → α) (init : List α) (gs : List β) :
    (gs.foldl (fun l g => l ++ [f l g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp; omega

lemma foldl_append_prefix {α β : Type*} (f : List α → β → α) (init : List α) (gs : List β)
    (i : ℕ) (hi : i < init.length) (d : α) :
    (gs.foldl (fun l g => l ++ [f l g]) init).getD i d = init.getD i d := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (init ++ [f init g]).length := by simp; omega
    rw [ih _ hi']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_append_at {α β : Type*} (f : List α → β → α) (init : List α) (gs : List β)
    (j : ℕ) (hj : j < gs.length) (d : α) :
    (gs.foldl (fun l g => l ++ [f l g]) init).getD (init.length + j) d =
      f ((gs.take j).foldl (fun l g => l ++ [f l g]) init) gs[j] := by
  induction gs generalizing init j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.foldl_cons, Nat.add_zero, List.take_zero, List.foldl_nil, List.getElem_cons_zero]
      have hlt : init.length < (init ++ [f init g]).length := by simp
      rw [foldl_append_prefix f (init ++ [f init g]) gs init.length hlt d]
      simp [List.getD_eq_getElem?_getD]
    | succ j' =>
      simp only [List.foldl_cons, List.take_succ_cons, List.getElem_cons_succ]
      have hj' : j' < gs.length := Nat.lt_of_succ_lt_succ hj
      have hlen : (init ++ [f init g]).length + j' = init.length + (j' + 1) := by
        simp; omega
      rw [← hlen]
      exact ih (init ++ [f init g]) j' hj'

lemma foldr_max_le {l : List ℕ} {k : ℕ} :
    l.foldr max 0 ≤ k ↔ ∀ a ∈ l, a ≤ k := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons, Nat.max_le, ih, List.mem_cons, forall_eq_or_imp]

lemma depthsList_len (w : ℕ) (gs : List Gate) :
    (depthsList w gs).length = w + gs.length := by
  unfold depthsList
  simpa using foldl_append_step (fun ds g => (g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinearG g).toNat)
    (List.replicate w 0) gs

lemma wiresList_len (x : List Bool) (gs : List Gate) :
    (wiresList x gs).length = x.length + gs.length := by
  unfold wiresList
  exact foldl_append_step _ x gs

lemma depthsList_prefix (w : ℕ) (gs : List Gate) (j : ℕ) (k : ℕ) (hk : k < w + j) :
    ((gs.take j).foldl (fun (ds : List ℕ) g =>
      ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinearG g).toNat])
      (List.replicate w 0)).getD k 0 = (depthsList w gs).getD k 0 := by
  have hsp : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
  unfold depthsList
  conv_rhs => rw [hsp, List.foldl_append]
  have hlen : ((gs.take j).foldl (fun (ds : List ℕ) g =>
      ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinearG g).toNat])
      (List.replicate w 0)).length = w + (gs.take j).length := by
    simpa using foldl_append_step (fun (ds : List ℕ) g => (g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinearG g).toNat)
      (List.replicate w 0) (gs.take j)
  by_cases hj : j ≤ gs.length
  · have hlt : k < ((gs.take j).foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinearG g).toNat])
        (List.replicate w 0)).length := by
      rw [hlen, List.length_take, Nat.min_eq_left hj]; exact hk
    exact (foldl_append_prefix _ _ (gs.drop j) k hlt 0).symm
  · have hdrop : gs.drop j = [] := List.drop_eq_nil_of_le (Nat.le_of_not_ge hj)
    rw [hdrop, List.foldl_nil]

lemma wiresList_prefix (x : List Bool) (gs : List Gate) (j : ℕ) (k : ℕ) (hk : k < x.length + j) :
    ((gs.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD k false =
      (wiresList x gs).getD k false := by
  have hsp : gs = gs.take j ++ gs.drop j := (List.take_append_drop j gs).symm
  unfold wiresList
  conv_rhs => rw [hsp, List.foldl_append]
  have hlen : ((gs.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length =
      x.length + (gs.take j).length := foldl_append_step _ x (gs.take j)
  by_cases hj : j ≤ gs.length
  · have hlt : k < ((gs.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length := by
      rw [hlen, List.length_take, Nat.min_eq_left hj]; exact hk
    exact (foldl_append_prefix _ _ (gs.drop j) k hlt false).symm
  · have hdrop : gs.drop j = [] := List.drop_eq_nil_of_le (Nat.le_of_not_ge hj)
    rw [hdrop, List.foldl_nil]

lemma depthsList_at_gate (w : ℕ) (C : Circuit) (hrb : ReadsBack w C) (j : ℕ) (hj : j < C.gates.length) :
    (depthsList w C.gates).getD (w + j) 0 =
      ((C.gates[j]).inputs.map (fun a => (depthsList w C.gates).getD a 0)).foldr max 0 +
        (nonlinearG C.gates[j]).toNat := by
  unfold depthsList
  have h1 := foldl_append_at (fun (ds : List ℕ) g => (g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinearG g).toNat)
    (List.replicate w 0) C.gates j hj 0
  rw [List.length_replicate] at h1
  rw [h1]
  congr 1
  congr 1
  apply List.map_congr_left
  intro a ha
  have halt : a < w + j := by
    have := hrb j hj a
    simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this
    exact this ha
  exact depthsList_prefix w C.gates j a halt

lemma wiresList_at_gate (x : List Bool) (C : Circuit) (hrb : ReadsBack x.length C)
    (j : ℕ) (hj : j < C.gates.length) :
    (wiresList x C.gates).getD (x.length + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun a => (wiresList x C.gates).getD a false) := by
  unfold wiresList
  have h1 := foldl_append_at (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)) x C.gates j hj false
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro a ha
  have halt : a < x.length + j := by
    have := hrb j hj a
    simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this
    exact this ha
  exact wiresList_prefix x C.gates j a halt

lemma oneEach_length {n m : ℕ} (i : Fin n) (c : Fin m) : (oneEach i c).length = n + m := by
  simp [oneEach]

lemma oneEach_getD_left {n m : ℕ} (i : Fin n) (c : Fin m) (k : ℕ) (hk : k < n) :
    (oneEach i c).getD k false = decide (k = i.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [hk])]
  simp [hk, Fin.ext_iff]

lemma oneEach_getD_right {n m : ℕ} (i : Fin n) (c : Fin m) (k : ℕ) (hk : k < m) :
    (oneEach i c).getD (n + k) false = decide (k = c.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]
  simp [hk, Fin.ext_iff]

lemma forward_factorization {n m t : ℕ} (T : Fin n → Fin m → Bool) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : ReadsBack (n + m) C)
    (hrep : Represents T C)
    (hdep : (depthsList (n + m) C.gates).getD C.output 0 ≤ 1)
    (hcnt : C.gates.countP nonlinearG ≤ t) :
    ∃ (A : Fin n → ZMod 2) (B : Fin m → ZMod 2)
      (x : Fin n → Fin (2 * t) → ZMod 2) (y : Fin m → Fin (2 * t) → ZMod 2),
      ∀ i c, b2z (T i c) = A i + B c + dotProduct (x i) (y c) := by
  let ds := depthsList (n + m) C.gates
  let wval : ℕ → Fin n → Fin m → ZMod 2 := fun w i c =>
    b2z ((wiresList (oneEach i c) C.gates).getD w false)
  have hsep0 : ∀ w, ds.getD w 0 = 0 →
      ∃ (a : Fin n → ZMod 2) (b : Fin m → ZMod 2), ∀ i c, wval w i c = a i + b c := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw0
      by_cases hwin : w < n + m
      · by_cases hw1 : w < n
        · refine ⟨fun i => b2z (decide (w = i.val)), fun _ => 0, ?_⟩
          intro i c
          simp only [wval, wiresList, add_zero]
          rw [foldl_append_prefix _ (oneEach i c) C.gates w (by rw [oneEach_length]; exact hwin) false]
          rw [oneEach_getD_left i c w hw1]
        · refine ⟨fun _ => 0, fun c => b2z (decide (w - n = c.val)), ?_⟩
          intro i c
          simp only [wval, wiresList, zero_add]
          rw [foldl_append_prefix _ (oneEach i c) C.gates w (by rw [oneEach_length]; exact hwin) false]
          have hsub : w = n + (w - n) := by omega
          have hlt : w - n < m := by omega
          conv_lhs => rw [hsub]
          rw [oneEach_getD_right i c (w - n) hlt]
      · by_cases hwgt : w < n + m + C.gates.length
        · let j := w - (n + m)
          have hj : j < C.gates.length := by omega
          have hw_eq : w = (n + m) + j := by omega
          have hdj := depthsList_at_gate (n + m) C hrb j hj
          rw [← hw_eq] at hdj
          have hnl : nonlinearG C.gates[j] = false := by
            by_contra h
            have h1 : nonlinearG C.gates[j] = true := by cases hn : nonlinearG C.gates[j] <;> simp_all
            rw [h1] at hdj
            change ds.getD w 0 = _ at hdj
            rw [hw0] at hdj
            simp at hdj
          have hinputs0 : ∀ a ∈ (C.gates[j]).inputs, ds.getD a 0 = 0 := by
            intro a ha
            have hle : ((C.gates[j]).inputs.map (fun u => ds.getD u 0)).foldr max 0 ≤ 0 := by
              change ds.getD w 0 = ((C.gates[j]).inputs.map (fun u => ds.getD u 0)).foldr max 0 + (nonlinearG C.gates[j]).toNat at hdj
              rw [hw0, hnl] at hdj
              simp only [Bool.toNat_false, add_zero] at hdj
              omega
            exact Nat.eq_zero_of_le_zero ((foldr_max_le.mp hle) (ds.getD a 0) (List.mem_map.mpr ⟨a, ha, rfl⟩))
          have hrbj : ∀ a ∈ (C.gates[j]).inputs, a < w := by
            intro a ha
            have hlt := hrb j hj a
            simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at hlt
            have := hlt ha
            omega
          obtain ⟨c0, c1, c2, haff⟩ := gate_affine_of_not_nonlinear C.gates[j] (hfan _ (List.getElem_mem hj)) hnl
          have hget : ∀ k, ∃ (a : Fin n → ZMod 2) (b : Fin m → ZMod 2), ∀ i c,
              b2z (((C.gates[j]).inputs.map fun u => (wiresList (oneEach i c) C.gates).getD u false).getD k false) =
                a i + b c := by
            intro k
            by_cases hk : k < (C.gates[j]).inputs.length
            · let u := (C.gates[j]).inputs[k]
              have hu_mem : u ∈ (C.gates[j]).inputs := List.getElem_mem hk
              obtain ⟨au, bu, hab⟩ := ih u (hrbj u hu_mem) (hinputs0 u hu_mem)
              refine ⟨au, bu, ?_⟩
              intro i c
              have hmap : (((C.gates[j]).inputs.map fun a => (wiresList (oneEach i c) C.gates).getD a false).getD k false) =
                  (wiresList (oneEach i c) C.gates).getD u false := by
                simp [List.getD_eq_getElem?_getD, hk, u]
              rw [hmap]
              exact hab i c
            · refine ⟨fun _ => 0, fun _ => 0, ?_⟩
              intro i c
              have hge : ((C.gates[j]).inputs.map fun a => (wiresList (oneEach i c) C.gates).getD a false).length ≤ k := by
                simp; omega
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
              simp [b2z]
          obtain ⟨a0, b0, h0⟩ := hget 0
          obtain ⟨a1, b1, h1⟩ := hget 1
          refine ⟨fun i => c0 + c1 * a0 i + c2 * a1 i, fun c => c1 * b0 c + c2 * b1 c, ?_⟩
          intro i c
          have hwg : wval w i c = b2z ((C.gates[j]).op.eval ((C.gates[j]).inputs.map fun a => (wiresList (oneEach i c) C.gates).getD a false)) := by
            unfold wval
            have hlen := oneEach_length i c
            have hrb' : ReadsBack (oneEach i c).length C := by rwa [hlen]
            have hstep := wiresList_at_gate (oneEach i c) C hrb' j hj
            rw [hlen, ← hw_eq] at hstep
            rw [hstep]
          rw [hwg, haff _ (by simp), h0 i c, h1 i c]
          ring
        · refine ⟨fun _ => 0, fun _ => 0, ?_⟩
          intro i c
          unfold wval
          have hnone : (wiresList (oneEach i c) C.gates)[w]? = none := by
            apply List.getElem?_eq_none
            rw [wiresList_len, oneEach_length]
            omega
          simp [List.getD_eq_getElem?_getD, hnone, b2z]
  let nlIdx : List ℕ := (List.range C.gates.length).filter (fun j =>
    nonlinearG (C.gates.getD j ⟨.or, []⟩) && decide (ds.getD ((n + m) + j) 0 ≤ 1))
  have hnl_len : nlIdx.length ≤ t := by
    have h1 : nlIdx.length ≤ C.gates.countP nonlinearG := by
      have hmap : C.gates.countP nonlinearG = ((List.range C.gates.length).filter (fun j => nonlinearG (C.gates.getD j ⟨.or, []⟩))).length := by
        rw [List.countP_eq_length_filter]
        have hrg : C.gates = (List.range C.gates.length).map (fun j => C.gates.getD j ⟨.or, []⟩) := by
          apply List.ext_getElem
          · simp
          · intro k hk1 hk2
            simp [List.getD_eq_getElem?_getD, hk1]
        conv_lhs => rw [hrg, List.filter_map, List.length_map]
        rfl
      rw [hmap]
      have hsub : nlIdx.Sublist ((List.range C.gates.length).filter (fun j => nonlinearG (C.gates.getD j ⟨.or, []⟩))) := by
        have hfl : nlIdx = ((List.range C.gates.length).filter (fun j => nonlinearG (C.gates.getD j ⟨.or, []⟩))).filter
            (fun j => decide (ds.getD ((n + m) + j) 0 ≤ 1)) := by
          unfold nlIdx
          rw [List.filter_filter]
          apply List.filter_congr
          intro x _
          simp [Bool.and_comm]
        rw [hfl]
        exact List.filter_sublist
      exact hsub.length_le
    exact le_trans h1 hcnt
  have hnl_quad : ∀ r : Fin nlIdx.length,
      ∃ (a0 : Fin n → ZMod 2) (b0 : Fin m → ZMod 2)
        (α1 α2 : Fin n → ZMod 2) (β1 β2 : Fin m → ZMod 2),
        ∀ i c, wval ((n + m) + nlIdx[r]) i c =
          a0 i + b0 c + α1 i * β2 c + α2 i * β1 c := by
    intro r
    let j := nlIdx[r]
    have hmem : j ∈ nlIdx := List.getElem_mem r.isLt
    simp only [nlIdx, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hmem
    obtain ⟨hj, hnl_d, hdle⟩ := hmem
    have hnl : nonlinearG C.gates[j] = true := by
      simpa [List.getD_eq_getElem?_getD, hj] using hnl_d
    obtain ⟨hlen2, c0, c1, c2, hquad⟩ := gate_quad_of_nonlinear C.gates[j] hnl
    have hdj := depthsList_at_gate (n + m) C hrb j hj
    have hinputs0 : ∀ a ∈ (C.gates[j]).inputs, ds.getD a 0 = 0 := by
      intro a ha
      have hle : ((C.gates[j]).inputs.map (fun u => ds.getD u 0)).foldr max 0 ≤ 0 := by
        change ds.getD ((n + m) + j) 0 =
          ((C.gates[j]).inputs.map (fun u => ds.getD u 0)).foldr max 0 + (nonlinearG C.gates[j]).toNat at hdj
        rw [hnl] at hdj
        simp only [Bool.toNat_true] at hdj
        omega
      exact Nat.eq_zero_of_le_zero ((foldr_max_le.mp hle) (ds.getD a 0) (List.mem_map.mpr ⟨a, ha, rfl⟩))
    have hu0_mem : (C.gates[j]).inputs[0]'(by omega) ∈ (C.gates[j]).inputs := List.getElem_mem (by omega)
    have hu1_mem : (C.gates[j]).inputs[1]'(by omega) ∈ (C.gates[j]).inputs := List.getElem_mem (by omega)
    obtain ⟨α1, β1, h1⟩ := hsep0 _ (hinputs0 _ hu0_mem)
    obtain ⟨α2, β2, h2⟩ := hsep0 _ (hinputs0 _ hu1_mem)
    refine ⟨fun i => c0 + c1 * α1 i + c2 * α2 i + α1 i * α2 i,
            fun c => c1 * β1 c + c2 * β2 c + β1 c * β2 c,
            α1, α2, β1, β2, ?_⟩
    intro i c
    have hlen := oneEach_length i c
    have hrb' : ReadsBack (oneEach i c).length C := by rwa [hlen]
    have hstep := wiresList_at_gate (oneEach i c) C hrb' j hj
    rw [hlen] at hstep
    have hlist_aux : ∀ l : List ℕ, (hl : l.length = 2) → l = [l[0]'(by omega), l[1]'(by omega)] := by
      intro l hl
      rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩
      · simp at hl
      · simp at hl
      · rfl
      · simp at hl
    have hlist : (C.gates[j]).inputs = [(C.gates[j]).inputs[0]'(by omega), (C.gates[j]).inputs[1]'(by omega)] :=
      hlist_aux _ hlen2
    have hval : wval ((n + m) + j) i c =
        b2z ((C.gates[j]).op.eval [(wiresList (oneEach i c) C.gates).getD ((C.gates[j]).inputs[0]'(by omega)) false,
                                   (wiresList (oneEach i c) C.gates).getD ((C.gates[j]).inputs[1]'(by omega)) false]) := by
      unfold wval
      rw [hstep]
      conv_lhs => rw [hlist]
      rfl
    rw [hval, hquad]
    have e1 := h1 i c
    have e2 := h2 i c
    unfold wval at e1 e2
    rw [e1, e2]
    ring
  choose a0 b0 α1 α2 β1 β2 hnl_eq using hnl_quad
  have hrep1 : ∀ w, ds.getD w 0 ≤ 1 →
      ∃ (A : Fin n → ZMod 2) (B : Fin m → ZMod 2) (lam : Fin nlIdx.length → ZMod 2),
        ∀ i c, wval w i c = A i + B c + ∑ r : Fin nlIdx.length, lam r * (α1 r i * β2 r c + α2 r i * β1 r c) := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hwle
      by_cases hw0 : ds.getD w 0 = 0
      · obtain ⟨a, b, hab⟩ := hsep0 w hw0
        refine ⟨a, b, fun _ => 0, ?_⟩
        intro i c; simp [hab i c]
      · have hwin : ¬ w < n + m := by
          intro hlt
          have h0 : ds.getD w 0 = 0 := by
            unfold ds depthsList
            rw [foldl_append_prefix _ (List.replicate (n + m) 0) C.gates w (by simp [hlt]) 0]
            simp [List.getD_eq_getElem?_getD, hlt]
          exact hw0 h0
        have hwgt : w < n + m + C.gates.length := by
          by_contra hge
          have hnone : ds[w]? = none := by
            apply List.getElem?_eq_none
            rw [depthsList_len]
            omega
          have h0 : ds.getD w 0 = 0 := by simp [List.getD_eq_getElem?_getD, hnone]
          exact hw0 h0
        let j := w - (n + m)
        have hj : j < C.gates.length := by omega
        have hw_eq : w = (n + m) + j := by omega
        by_cases hnl : nonlinearG C.gates[j] = true
        · have hj_mem : j ∈ nlIdx := by
            simp only [nlIdx, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
            refine ⟨hj, ?_, ?_⟩
            · simpa [List.getD_eq_getElem?_getD, hj] using hnl
            · rwa [← hw_eq]
          obtain ⟨r, hr⟩ := List.mem_iff_getElem.mp hj_mem
          let rFin : Fin nlIdx.length := ⟨r, hr.1⟩
          refine ⟨a0 rFin, b0 rFin, fun s => if s = rFin then 1 else 0, ?_⟩
          intro i c
          rw [hw_eq, ← hr.2]
          have hsum1 : (∑ s : Fin nlIdx.length, (if s = rFin then (1 : ZMod 2) else 0) * (α1 s i * β2 s c + α2 s i * β1 s c)) =
              α1 rFin i * β2 rFin c + α2 rFin i * β1 rFin c := by
            simp
          have hnl' : wval (n + m + nlIdx[r]'hr.1) i c = a0 rFin i + b0 rFin c + α1 rFin i * β2 rFin c + α2 rFin i * β1 rFin c :=
            hnl_eq rFin i c
          rw [hsum1, hnl']
          ring
        · have hnlf : nonlinearG C.gates[j] = false := by cases hn : nonlinearG C.gates[j] <;> simp_all
          have hdj := depthsList_at_gate (n + m) C hrb j hj
          have hinputs1 : ∀ a ∈ (C.gates[j]).inputs, ds.getD a 0 ≤ 1 := by
            intro a ha
            have hle : ((C.gates[j]).inputs.map (fun u => ds.getD u 0)).foldr max 0 ≤ 1 := by
              change ds.getD ((n + m) + j) 0 = ((C.gates[j]).inputs.map (fun u => ds.getD u 0)).foldr max 0 + (nonlinearG C.gates[j]).toNat at hdj
              rw [← hw_eq, hnlf] at hdj
              simp only [Bool.toNat_false, add_zero] at hdj
              omega
            exact (foldr_max_le.mp hle) (ds.getD a 0) (List.mem_map.mpr ⟨a, ha, rfl⟩)
          have hrbj : ∀ a ∈ (C.gates[j]).inputs, a < w := by
            intro a ha
            have hlt := hrb j hj a
            simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at hlt
            have := hlt ha
            omega
          obtain ⟨c0, c1, c2, haff⟩ := gate_affine_of_not_nonlinear C.gates[j] (hfan _ (List.getElem_mem hj)) hnlf
          have hget : ∀ k, ∃ (A : Fin n → ZMod 2) (B : Fin m → ZMod 2) (lam : Fin nlIdx.length → ZMod 2),
              ∀ i c, b2z (((C.gates[j]).inputs.map fun u => (wiresList (oneEach i c) C.gates).getD u false).getD k false) =
                A i + B c + ∑ r : Fin nlIdx.length, lam r * (α1 r i * β2 r c + α2 r i * β1 r c) := by
            intro k
            by_cases hk : k < (C.gates[j]).inputs.length
            · let u := (C.gates[j]).inputs[k]
              have hu_mem : u ∈ (C.gates[j]).inputs := List.getElem_mem hk
              obtain ⟨Au, Bu, lu, hlu⟩ := ih u (hrbj u hu_mem) (hinputs1 u hu_mem)
              refine ⟨Au, Bu, lu, ?_⟩
              intro i c
              have hmap : (((C.gates[j]).inputs.map fun a => (wiresList (oneEach i c) C.gates).getD a false).getD k false) =
                  (wiresList (oneEach i c) C.gates).getD u false := by
                simp [List.getD_eq_getElem?_getD, hk, u]
              rw [hmap]
              exact hlu i c
            · refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
              intro i c
              have hge : ((C.gates[j]).inputs.map fun a => (wiresList (oneEach i c) C.gates).getD a false).length ≤ k := by
                simp; omega
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
              simp [b2z]
          obtain ⟨A0, B0, l0, hl0⟩ := hget 0
          obtain ⟨A1, B1, l1, hl1⟩ := hget 1
          refine ⟨fun i => c0 + c1 * A0 i + c2 * A1 i,
                  fun c => c1 * B0 c + c2 * B1 c,
                  fun r => c1 * l0 r + c2 * l1 r, ?_⟩
          intro i c
          have hwg : wval w i c = b2z ((C.gates[j]).op.eval ((C.gates[j]).inputs.map fun a => (wiresList (oneEach i c) C.gates).getD a false)) := by
            unfold wval
            have hlen := oneEach_length i c
            have hrb' : ReadsBack (oneEach i c).length C := by rwa [hlen]
            have hstep := wiresList_at_gate (oneEach i c) C hrb' j hj
            rw [hlen, ← hw_eq] at hstep
            rw [hstep]
          rw [hwg, haff _ (by simp), hl0 i c, hl1 i c]
          simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_add_distrib, mul_assoc]
          ring
  obtain ⟨A, B, lam, hout⟩ := hrep1 C.output hdep
  let x : Fin n → Fin (2 * t) → ZMod 2 := fun i p =>
    if h : p.val / 2 < nlIdx.length then
      if p.val % 2 = 0 then lam ⟨p.val / 2, h⟩ * α1 ⟨p.val / 2, h⟩ i
      else lam ⟨p.val / 2, h⟩ * α2 ⟨p.val / 2, h⟩ i
    else 0
  let y : Fin m → Fin (2 * t) → ZMod 2 := fun c p =>
    if h : p.val / 2 < nlIdx.length then
      if p.val % 2 = 0 then β2 ⟨p.val / 2, h⟩ c
      else β1 ⟨p.val / 2, h⟩ c
    else 0
  refine ⟨A, B, x, y, ?_⟩
  intro i c
  have hT : b2z (T i c) = wval C.output i c := by
    unfold wval
    have := hrep i c
    unfold Circuit.eval Circuit.wires at this
    rw [← this]
    rfl
  rw [hT, hout i c]
  congr 1
  unfold dotProduct
  have hsplit : ∑ p : Fin (2 * t), x i p * y c p =
      ∑ r : Fin t, (x i ⟨2 * r.val, by omega⟩ * y c ⟨2 * r.val, by omega⟩ +
                    x i ⟨2 * r.val + 1, by omega⟩ * y c ⟨2 * r.val + 1, by omega⟩) := by
    let e : Fin t × Fin 2 ≃ Fin (2 * t) :=
      { toFun := fun ⟨r, b⟩ => ⟨2 * r.val + b.val, by omega⟩
        invFun := fun p => (⟨p.val / 2, by omega⟩, ⟨p.val % 2, by omega⟩)
        left_inv := fun ⟨r, b⟩ => by
          ext <;> simp <;> omega
        right_inv := fun p => by
          ext; simp; omega }
    rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro r _
    rw [Fin.sum_univ_two]
    rfl
  rw [hsplit]
  have htr : ∑ r : Fin t, (x i ⟨2 * r.val, by omega⟩ * y c ⟨2 * r.val, by omega⟩ +
                    x i ⟨2 * r.val + 1, by omega⟩ * y c ⟨2 * r.val + 1, by omega⟩) =
      ∑ r : Fin nlIdx.length, lam r * (α1 r i * β2 r c + α2 r i * β1 r c) := by
    have hL : ∑ r : Fin t, (x i ⟨2 * r.val, by omega⟩ * y c ⟨2 * r.val, by omega⟩ +
                    x i ⟨2 * r.val + 1, by omega⟩ * y c ⟨2 * r.val + 1, by omega⟩) =
        ∑ k ∈ Finset.range t, (if h : k < nlIdx.length then
          lam ⟨k, h⟩ * (α1 ⟨k, h⟩ i * β2 ⟨k, h⟩ c + α2 ⟨k, h⟩ i * β1 ⟨k, h⟩ c) else 0) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro r _
      simp only [x, y]
      have hdiv0 : (2 * r.val) / 2 = r.val := by omega
      have hmod0 : (2 * r.val) % 2 = 0 := by omega
      have hdiv1 : (2 * r.val + 1) / 2 = r.val := by omega
      have hmod1 : (2 * r.val + 1) % 2 = 1 := by omega
      by_cases hlt : r.val < nlIdx.length
      · simp only [hdiv0, hmod0, hdiv1, hmod1, hlt, ↓reduceDIte, ↓reduceIte, one_ne_zero]
        ring
      · simp only [hdiv0, hdiv1, hlt, ↓reduceDIte, mul_zero, add_zero]
    have hR : ∑ r : Fin nlIdx.length, lam r * (α1 r i * β2 r c + α2 r i * β1 r c) =
        ∑ k ∈ Finset.range nlIdx.length, (if h : k < nlIdx.length then
          lam ⟨k, h⟩ * (α1 ⟨k, h⟩ i * β2 ⟨k, h⟩ c + α2 ⟨k, h⟩ i * β1 ⟨k, h⟩ c) else 0) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro r _
      simp [r.isLt]
    rw [hL, hR]
    symm
    apply Finset.sum_subset (Finset.range_mono hnl_len)
    intro k _ hk
    simp only [Finset.mem_range] at hk
    simp [hk]
  exact htr.symm

def buildXor (gs : List Gate) (w1 w2 : ℕ) : List Gate × ℕ :=
  let base := gs.length
  (gs ++ [⟨GateOp.mod 2, [w1, w2]⟩, ⟨GateOp.not, [base]⟩], base + 1)

def buildXorOffset (offset : ℕ) (gs : List Gate) (w1 w2 : ℕ) : List Gate × ℕ :=
  let base := offset + gs.length
  (gs ++ [⟨GateOp.mod 2, [w1, w2]⟩, ⟨GateOp.not, [base]⟩], base + 1)

def buildXorList (offset : ℕ) (gs : List Gate) (ws : List ℕ) : List Gate × ℕ :=
  match ws with
  | [] => (gs ++ [⟨GateOp.or, []⟩], offset + gs.length)
  | [w] => (gs, w)
  | w :: rest =>
    let (gs1, acc) := buildXorList offset gs rest
    buildXorOffset offset gs1 w acc

def listBoolXor (l : List Bool) : Bool :=
  l.foldr xor false

lemma b2z_listBoolXor (l : List Bool) :
    b2z (listBoolXor l) = (l.map b2z).sum := by
  induction l with
  | nil => simp [listBoolXor, b2z]
  | cons a rest ih =>
    simp only [listBoolXor, List.foldr_cons, List.map_cons, List.sum_cons]
    rw [b2z_xor, ← ih]
    rfl

def validGates (w : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.inputs.length ≤ 2) ∧
  (∀ j (hj : j < gs.length), ∀ a ∈ gs[j].inputs, a < w + j)

lemma validGates_readsBack (w : ℕ) (C : Circuit) (h : validGates w C.gates) :
    ReadsBack w C := by
  intro j hj a ha
  have h1 := h.2 j hj a
  simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at ha
  exact h1 ha

lemma validGates_append_one {w : ℕ} {gs : List Gate} {g : Gate}
    (hv : validGates w gs) (hf : g.inputs.length ≤ 2)
    (hb : ∀ a ∈ g.inputs, a < w + gs.length) :
    validGates w (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hv.1 x hx
    · simp only [List.mem_singleton] at hx; subst hx; exact hf
  · intro j hj a ha
    by_cases hlt : j < gs.length
    · have heq : (gs ++ [g])[j] = gs[j] := List.getElem_append_left hlt
      rw [heq] at ha
      exact hv.2 j hlt a ha
    · have hjeq : j = gs.length := by simp at hj; omega
      subst hjeq
      have heq : (gs ++ [g])[gs.length] = g := by simp
      rw [heq] at ha
      exact hb a ha

lemma wiresList_append_one (x : List Bool) (gs : List Gate) (g : Gate) :
    wiresList x (gs ++ [g]) =
      wiresList x gs ++ [g.op.eval (g.inputs.map fun i => (wiresList x gs).getD i false)] := by
  simp [wiresList, List.foldl_append]

lemma depthsList_append_one (w : ℕ) (gs : List Gate) (g : Gate) :
    depthsList w (gs ++ [g]) =
      depthsList w gs ++ [(g.inputs.map fun i => (depthsList w gs).getD i 0).foldr max 0 + (nonlinearG g).toNat] := by
  simp [depthsList, List.foldl_append]

lemma getD_append_right_single {α : Type*} (l : List α) (v d : α) :
    (l ++ [v]).getD l.length d = v := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_append_left_lt {α : Type*} (l r : List α) (i : ℕ) (hi : i < l.length) (d : α) :
    (l ++ r).getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma buildXorOffset_spec (w : ℕ) (gs : List Gate) (w1 w2 : ℕ)
    (hv : validGates w gs) (h1 : w1 < w + gs.length) (h2 : w2 < w + gs.length)
    (dmax : ℕ)
    (hd1 : (depthsList w gs).getD w1 0 ≤ dmax)
    (hd2 : (depthsList w gs).getD w2 0 ≤ dmax) :
    let res := buildXorOffset w gs w1 w2
    validGates w res.1 ∧
    res.1.countP nonlinearG = gs.countP nonlinearG ∧
    res.2 < w + res.1.length ∧
    (∀ k < w + gs.length, (depthsList w res.1).getD k 0 = (depthsList w gs).getD k 0) ∧
    (depthsList w res.1).getD res.2 0 ≤ dmax ∧
    (∀ x : List Bool, x.length = w →
      (∀ k < w + gs.length, (wiresList x res.1).getD k false = (wiresList x gs).getD k false) ∧
      (wiresList x res.1).getD res.2 false = xor ((wiresList x gs).getD w1 false) ((wiresList x gs).getD w2 false)) := by
  dsimp only [buildXorOffset]
  let g1 : Gate := ⟨GateOp.mod 2, [w1, w2]⟩
  let g2 : Gate := ⟨GateOp.not, [w + gs.length]⟩
  have hv1 : validGates w (gs ++ [g1]) :=
    validGates_append_one hv (by simp [g1]) (by intro a ha; simp [g1] at ha; rcases ha with rfl | rfl <;> omega)
  have hv2 : validGates w ((gs ++ [g1]) ++ [g2]) :=
    validGates_append_one hv1 (by simp [g2]) (by intro a ha; simp [g2] at ha; subst ha; simp)
  have happ : gs ++ [g1, g2] = (gs ++ [g1]) ++ [g2] := by simp [List.append_assoc]
  rw [happ]
  have hnl1 : nonlinearG g1 = false := rfl
  have hnl2 : nonlinearG g2 = false := rfl
  refine ⟨hv2, ?_, ?_, ?_, ?_, ?_⟩
  · simp [List.countP_append, hnl1, hnl2]
  · simp; omega
  · intro k hk
    have hlen0 : (depthsList w gs).length = w + gs.length := depthsList_len w gs
    have hlen1 : (depthsList w (gs ++ [g1])).length = w + gs.length + 1 := by
      rw [depthsList_len]; simp; omega
    rw [depthsList_append_one, getD_append_left_lt _ _ k (by omega)]
    rw [depthsList_append_one, getD_append_left_lt _ _ k (by omega)]
  · have hlen0 : (depthsList w gs).length = w + gs.length := depthsList_len w gs
    have hlen1 : (depthsList w (gs ++ [g1])).length = w + gs.length + 1 := by
      rw [depthsList_len]; simp; omega
    rw [depthsList_append_one]
    have hidx : w + gs.length + 1 = (depthsList w (gs ++ [g1])).length := by omega
    rw [hidx, getD_append_right_single]
    simp only [g2, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, hnl2, Bool.toNat_false, add_zero]
    rw [depthsList_append_one]
    have hidx0 : w + gs.length = (depthsList w gs).length := by omega
    rw [hidx0, getD_append_right_single]
    simp only [g1, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, hnl1, Bool.toNat_false, add_zero]
    omega
  · intro x hx
    have hlen0 : (wiresList x gs).length = w + gs.length := by rw [wiresList_len, hx]
    have hlen1 : (wiresList x (gs ++ [g1])).length = w + gs.length + 1 := by
      rw [wiresList_len, hx]; simp; omega
    refine ⟨?_, ?_⟩
    · intro k hk
      rw [wiresList_append_one, getD_append_left_lt _ _ k (by omega)]
      rw [wiresList_append_one, getD_append_left_lt _ _ k (by omega)]
    · rw [wiresList_append_one]
      have hidx : w + gs.length + 1 = (wiresList x (gs ++ [g1])).length := by omega
      rw [hidx, getD_append_right_single]
      simp only [g2, List.map_cons, List.map_nil]
      rw [wiresList_append_one]
      have hidx0 : w + gs.length = (wiresList x gs).length := by omega
      rw [hidx0, getD_append_right_single]
      simp only [g1, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
      cases ((wiresList x gs).getD w1 false) <;> cases ((wiresList x gs).getD w2 false) <;> decide

lemma buildXorList_spec (w : ℕ) (ws : List ℕ) (gs : List Gate) (dmax : ℕ)
    (hv : validGates w gs)
    (hws : ∀ a ∈ ws, a < w + gs.length)
    (hds : ∀ a ∈ ws, (depthsList w gs).getD a 0 ≤ dmax) :
    let res := buildXorList w gs ws
    validGates w res.1 ∧
    res.1.countP nonlinearG = gs.countP nonlinearG ∧
    w + gs.length ≤ w + res.1.length ∧
    res.2 < w + res.1.length ∧
    (∀ k < w + gs.length, (depthsList w res.1).getD k 0 = (depthsList w gs).getD k 0) ∧
    (depthsList w res.1).getD res.2 0 ≤ dmax ∧
    (∀ x : List Bool, x.length = w →
      (∀ k < w + gs.length, (wiresList x res.1).getD k false = (wiresList x gs).getD k false) ∧
      (wiresList x res.1).getD res.2 false = listBoolXor (ws.map fun a => (wiresList x gs).getD a false)) := by
  induction ws generalizing gs with
  | nil =>
    dsimp only [buildXorList]
    let g0 : Gate := ⟨GateOp.or, []⟩
    have hv1 : validGates w (gs ++ [g0]) := validGates_append_one hv (by simp [g0]) (by simp [g0])
    have hnl0 : nonlinearG g0 = false := rfl
    refine ⟨hv1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.countP_append, List.countP_cons, List.countP_nil, hnl0]; simp
    · simp
    · simp
    · intro k hk
      rw [depthsList_append_one, getD_append_left_lt _ _ k (by rw [depthsList_len]; exact hk)]
    · rw [depthsList_append_one]
      have hidx : w + gs.length = (depthsList w gs).length := (depthsList_len w gs).symm
      rw [hidx, getD_append_right_single]
      simp [g0, hnl0]
    · intro x hx
      refine ⟨?_, ?_⟩
      · intro k hk
        rw [wiresList_append_one, getD_append_left_lt _ _ k (by rw [wiresList_len, hx]; exact hk)]
      · rw [wiresList_append_one]
        have hidx : w + gs.length = (wiresList x gs).length := by rw [wiresList_len, hx]
        rw [hidx, getD_append_right_single]
        simp [GateOp.eval, listBoolXor]
  | cons a rest ih =>
    cases rest with
    | nil =>
      dsimp only [buildXorList]
      refine ⟨hv, rfl, le_rfl, hws a (by simp), fun _ _ => rfl, hds a (by simp), ?_⟩
      intro x _
      refine ⟨fun _ _ => rfl, ?_⟩
      simp [listBoolXor]
    | cons b rest' =>
      dsimp only [buildXorList]
      have hsub := ih gs hv (fun u hu => hws u (List.mem_cons_of_mem a hu))
        (fun u hu => hds u (List.mem_cons_of_mem a hu))
      obtain ⟨hv1, hcnt1, hlen1, hacc_lt, hdep1, hdep_acc, hwire1⟩ := hsub
      let gs1 := (buildXorList w gs (b :: rest')).1
      let acc := (buildXorList w gs (b :: rest')).2
      have ha_lt0 : a < w + gs.length := hws a (by simp)
      have ha_lt1 : a < w + gs1.length := lt_of_lt_of_le ha_lt0 hlen1
      have ha_d1 : (depthsList w gs1).getD a 0 ≤ dmax := by
        rw [hdep1 a ha_lt0]; exact hds a (by simp)
      have hstep := buildXorOffset_spec w gs1 a acc hv1 ha_lt1 hacc_lt dmax ha_d1 hdep_acc
      obtain ⟨hv2, hcnt2, hout_lt, hdep2, hdep_out, hwire2⟩ := hstep
      have hlen2 : w + gs1.length ≤ w + (buildXorOffset w gs1 a acc).1.length := by
        simp [buildXorOffset]
      refine ⟨hv2, hcnt2.trans hcnt1, le_trans hlen1 hlen2, hout_lt, ?_, hdep_out, ?_⟩
      · intro k hk
        rw [hdep2 k (lt_of_lt_of_le hk hlen1), hdep1 k hk]
      · intro x hx
        obtain ⟨hw1_pre, hw1_val⟩ := hwire1 x hx
        obtain ⟨hw2_pre, hw2_val⟩ := hwire2 x hx
        refine ⟨?_, ?_⟩
        · intro k hk
          rw [hw2_pre k (lt_of_lt_of_le hk hlen1), hw1_pre k hk]
        · rw [hw2_val, hw1_pre a ha_lt0, hw1_val]
          simp [listBoolXor]

lemma xor_indicators_left {n m : ℕ} (f : Fin n → ZMod 2) (i : Fin n) (c : Fin m) :
    b2z (listBoolXor (((List.finRange n).filter (fun k => decide (f k = 1))).map
      (fun k => (oneEach i c).getD k.val false))) = f i := by
  rw [b2z_listBoolXor, List.map_map]
  have h1 : (((List.finRange n).filter (fun k => decide (f k = 1))).map
      (b2z ∘ fun k : Fin n => (oneEach i c).getD k.val false)).sum =
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => f k = 1), b2z ((oneEach i c).getD k.val false) := by
    have hnd : ((List.finRange n).filter (fun k => decide (f k = 1))).Nodup :=
      (List.nodup_finRange n).filter _
    rw [← List.sum_toFinset _ hnd]
    have hset : ((List.finRange n).filter (fun k => decide (f k = 1))).toFinset =
        Finset.univ.filter (fun k : Fin n => f k = 1) := by
      ext k; simp
    rw [hset]
    rfl
  rw [h1]
  have hterm : ∀ k : Fin n, b2z ((oneEach i c).getD k.val false) = if k = i then (1 : ZMod 2) else 0 := by
    intro k
    rw [oneEach_getD_left i c k.val k.isLt]
    by_cases hki : k = i
    · subst hki; simp [b2z]
    · have : k.val ≠ i.val := fun h => hki (Fin.ext h)
      simp [this, hki, b2z]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq']
  by_cases hfi : f i = 1
  · simp [hfi]
  · have h0 : f i = 0 := zmod2_eq_zero_of_ne_one hfi
    simp [h0]

lemma xor_indicators_right {n m : ℕ} (g : Fin m → ZMod 2) (i : Fin n) (c : Fin m) :
    b2z (listBoolXor (((List.finRange m).filter (fun k => decide (g k = 1))).map
      (fun k => (oneEach i c).getD (n + k.val) false))) = g c := by
  rw [b2z_listBoolXor, List.map_map]
  have h1 : (((List.finRange m).filter (fun k => decide (g k = 1))).map
      (b2z ∘ fun k : Fin m => (oneEach i c).getD (n + k.val) false)).sum =
      ∑ k ∈ Finset.univ.filter (fun k : Fin m => g k = 1), b2z ((oneEach i c).getD (n + k.val) false) := by
    have hnd : ((List.finRange m).filter (fun k => decide (g k = 1))).Nodup :=
      (List.nodup_finRange m).filter _
    rw [← List.sum_toFinset _ hnd]
    have hset : ((List.finRange m).filter (fun k => decide (g k = 1))).toFinset =
        Finset.univ.filter (fun k : Fin m => g k = 1) := by
      ext k; simp
    rw [hset]
    rfl
  rw [h1]
  have hterm : ∀ k : Fin m, b2z ((oneEach i c).getD (n + k.val) false) = if k = c then (1 : ZMod 2) else 0 := by
    intro k
    rw [oneEach_getD_right i c k.val k.isLt]
    by_cases hkc : k = c
    · subst hkc; simp [b2z]
    · have : k.val ≠ c.val := fun h => hkc (Fin.ext h)
      simp [this, hkc, b2z]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq']
  by_cases hgc : g c = 1
  · simp [hgc]
  · have h0 : g c = 0 := zmod2_eq_zero_of_ne_one hgc
    simp [h0]

def sepWires {n m : ℕ} (f : Fin n → ZMod 2) (g : Fin m → ZMod 2) : List ℕ :=
  (((List.finRange n).filter (fun k => decide (f k = 1))).map (fun k => k.val)) ++
  (((List.finRange m).filter (fun k => decide (g k = 1))).map (fun k => n + k.val))

lemma sepWires_lt {n m : ℕ} (f : Fin n → ZMod 2) (g : Fin m → ZMod 2) :
    ∀ a ∈ sepWires f g, a < n + m := by
  intro a ha
  unfold sepWires at ha
  rcases List.mem_append.mp ha with h1 | h2
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp h1; omega
  · obtain ⟨k, _, rfl⟩ := List.mem_map.mp h2; omega

lemma sepWires_eval {n m : ℕ} (f : Fin n → ZMod 2) (g : Fin m → ZMod 2) (i : Fin n) (c : Fin m) :
    b2z (listBoolXor ((sepWires f g).map (fun a => (oneEach i c).getD a false))) = f i + g c := by
  unfold sepWires
  rw [List.map_append]
  have hxor_app : ∀ l1 l2 : List Bool, listBoolXor (l1 ++ l2) = xor (listBoolXor l1) (listBoolXor l2) := by
    intro l1 l2
    induction l1 with
    | nil => simp [listBoolXor]
    | cons a r ih =>
      simp only [List.cons_append, listBoolXor, List.foldr_cons] at ih ⊢
      rw [ih, Bool.xor_assoc]
  rw [hxor_app, b2z_xor, List.map_map, List.map_map]
  have hL := xor_indicators_left f i c
  have hR := xor_indicators_right g i c
  exact congrArg₂ (· + ·) hL hR

lemma build_circuit_from_factor {n m t : ℕ}
    (s : Fin n → Bool) (x : Fin n → Fin (2 * t) → ZMod 2) (y : Fin m → Fin (2 * t) → ZMod 2) :
    ∃ C : Circuit,
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      ReadsBack (n + m) C ∧
      Represents (fun i c => decide (b2z (s i) + dotProduct (x i) (y c) = 1)) C ∧
      (depthsList (n + m) C.gates).getD C.output 0 ≤ 1 ∧
      C.gates.countP nonlinearG ≤ t := by
  let w := n + m
  have hin_depth : ∀ (gs : List Gate) (a : ℕ), a < w → (depthsList w gs).getD a 0 = 0 := by
    intro gs a ha
    unfold depthsList
    rw [foldl_append_prefix _ (List.replicate w 0) gs a (by simp [ha]) 0]
    simp [List.getD_eq_getElem?_getD, ha]
  have hin_wire : ∀ (gs : List Gate) (i : Fin n) (c : Fin m) (a : ℕ), a < w →
      (wiresList (oneEach i c) gs).getD a false = (oneEach i c).getD a false := by
    intro gs i c a ha
    unfold wiresList
    rw [foldl_append_prefix _ (oneEach i c) gs a (by rw [oneEach_length]; exact ha) false]
  have hstep_pairs : ∀ k : ℕ, (hk : k ≤ t) →
      ∃ (gs : List Gate) (gws : List ℕ),
        validGates w gs ∧
        gs.countP nonlinearG = k ∧
        gws.length = k ∧
        (∀ a ∈ gws, a < w + gs.length ∧ (depthsList w gs).getD a 0 ≤ 1) ∧
        (∀ i c, b2z (listBoolXor (gws.map fun a => (wiresList (oneEach i c) gs).getD a false)) =
          ∑ r : Fin k,
            (x i ⟨2 * r.val, by omega⟩ + y c ⟨2 * r.val + 1, by omega⟩) *
            (x i ⟨2 * r.val + 1, by omega⟩ + y c ⟨2 * r.val, by omega⟩)) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨[], [], ⟨by simp, by simp⟩, rfl, rfl, by simp, ?_⟩
      intro i c; simp [listBoolXor, b2z]
    | succ k ih =>
      obtain ⟨gs0, gws0, hv0, hcnt0, hlen0, hmem0, heval0⟩ := ih (Nat.le_of_succ_le hk)
      let f1 : Fin n → ZMod 2 := fun i => x i ⟨2 * k, by omega⟩
      let g2 : Fin m → ZMod 2 := fun c => y c ⟨2 * k + 1, by omega⟩
      let f2 : Fin n → ZMod 2 := fun i => x i ⟨2 * k + 1, by omega⟩
      let g1 : Fin m → ZMod 2 := fun c => y c ⟨2 * k, by omega⟩
      let uRes := buildXorList w gs0 (sepWires f1 g2)
      have hu := buildXorList_spec w (sepWires f1 g2) gs0 0 hv0
        (fun a ha => lt_of_lt_of_le (sepWires_lt f1 g2 a ha) (Nat.le_add_right _ _))
        (fun a ha => by rw [hin_depth gs0 a (sepWires_lt f1 g2 a ha)])
      obtain ⟨hvu, hcntu, hlenu, hu_lt, hdepu, hdep_u, hwireu⟩ := hu
      let gs1 := uRes.1
      let wu := uRes.2
      let vRes := buildXorList w gs1 (sepWires f2 g1)
      have hv_spec := buildXorList_spec w (sepWires f2 g1) gs1 0 hvu
        (fun a ha => lt_of_lt_of_le (sepWires_lt f2 g1 a ha) (Nat.le_add_right _ _))
        (fun a ha => by rw [hin_depth gs1 a (sepWires_lt f2 g1 a ha)])
      obtain ⟨hvv, hcntv, hlenv, hv_lt, hdepv, hdep_v, hwirev⟩ := hv_spec
      let gs2 := vRes.1
      let wv := vRes.2
      let gand : Gate := ⟨GateOp.and, [wu, wv]⟩
      let gs3 := gs2 ++ [gand]
      let wg := w + gs2.length
      have hwu_lt2 : wu < w + gs2.length := lt_of_lt_of_le hu_lt hlenv
      have hv3 : validGates w gs3 :=
        validGates_append_one hvv (by simp [gand]) (by intro a ha; simp [gand] at ha; rcases ha with rfl | rfl; exact hwu_lt2; exact hv_lt)
      have hnl_and : nonlinearG gand = true := rfl
      have hcnt3 : gs3.countP nonlinearG = k + 1 := by
        rw [show gs3 = gs2 ++ [gand] from rfl, List.countP_append, List.countP_cons, List.countP_nil, hnl_and]
        have h2 : gs2.countP nonlinearG = gs1.countP nonlinearG := hcntv
        have h1 : gs1.countP nonlinearG = gs0.countP nonlinearG := hcntu
        rw [h2, h1, hcnt0]
        simp
      have hdep_u2 : (depthsList w gs2).getD wu 0 = 0 := by
        rw [hdepv wu hu_lt]; exact Nat.eq_zero_of_le_zero hdep_u
      have hdep_v2 : (depthsList w gs2).getD wv 0 = 0 := Nat.eq_zero_of_le_zero hdep_v
      have hdep_g : (depthsList w gs3).getD wg 0 ≤ 1 := by
        simp only [gs3, wg, depthsList_append_one]
        rw [show w + gs2.length = (depthsList w gs2).length from (depthsList_len w gs2).symm]
        rw [getD_append_right_single]
        simp only [gand, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, hnl_and, Bool.toNat_true]
        rw [hdep_u2, hdep_v2]
        decide
      refine ⟨gs3, gws0 ++ [wg], hv3, hcnt3, by simp [hlen0], ?_, ?_⟩
      · intro a ha
        rcases List.mem_append.mp ha with ha0 | hag
        · obtain ⟨ha_lt0, ha_d0⟩ := hmem0 a ha0
          have ha_lt1 : a < w + gs1.length := lt_of_lt_of_le ha_lt0 hlenu
          have ha_lt2 : a < w + gs2.length := lt_of_lt_of_le ha_lt1 hlenv
          refine ⟨by simp [gs3]; omega, ?_⟩
          rw [depthsList_append_one, getD_append_left_lt _ _ a (by rw [depthsList_len]; exact ha_lt2)]
          rw [hdepv a ha_lt1, hdepu a ha_lt0]
          exact ha_d0
        · simp only [List.mem_singleton] at hag; subst hag
          exact ⟨by simp [gs3, wg], hdep_g⟩
      · intro i c
        have hxlen : (oneEach i c).length = w := oneEach_length i c
        obtain ⟨hwu_pre, hwu_val⟩ := hwireu (oneEach i c) hxlen
        obtain ⟨hwv_pre, hwv_val⟩ := hwirev (oneEach i c) hxlen
        have hxor_app : ∀ l1 l2 : List Bool, listBoolXor (l1 ++ l2) = xor (listBoolXor l1) (listBoolXor l2) := by
          intro l1 l2
          induction l1 with
          | nil => simp [listBoolXor]
          | cons a r ih =>
            simp only [List.cons_append, listBoolXor, List.foldr_cons] at ih ⊢
            rw [ih, Bool.xor_assoc]
        rw [List.map_append, hxor_app, b2z_xor]
        have hprev_map : gws0.map (fun a => (wiresList (oneEach i c) gs3).getD a false) =
            gws0.map (fun a => (wiresList (oneEach i c) gs0).getD a false) := by
          apply List.map_congr_left
          intro a ha
          have ha_lt0 := (hmem0 a ha).1
          have ha_lt1 := lt_of_lt_of_le ha_lt0 hlenu
          have ha_lt2 := lt_of_lt_of_le ha_lt1 hlenv
          rw [wiresList_append_one, getD_append_left_lt _ _ a (by rw [wiresList_len, hxlen]; exact ha_lt2)]
          rw [hwv_pre a ha_lt1, hwu_pre a ha_lt0]
        rw [hprev_map, heval0 i c]
        have hsingle : b2z (listBoolXor ([wg].map fun a => (wiresList (oneEach i c) gs3).getD a false)) =
            (f1 i + g2 c) * (f2 i + g1 c) := by
          simp only [List.map_cons, List.map_nil, listBoolXor, List.foldr_cons, List.foldr_nil, Bool.xor_false]
          simp only [gs3, wg, wiresList_append_one]
          rw [show w + gs2.length = (wiresList (oneEach i c) gs2).length by rw [wiresList_len, hxlen]]
          rw [getD_append_right_single]
          simp only [gand, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          rw [b2z_and]
          have hbu : b2z ((wiresList (oneEach i c) gs2).getD wu false) = f1 i + g2 c := by
            rw [hwv_pre wu hu_lt, hwu_val]
            have hmapu : (sepWires f1 g2).map (fun a => (wiresList (oneEach i c) gs0).getD a false) =
                (sepWires f1 g2).map (fun a => (oneEach i c).getD a false) := by
              apply List.map_congr_left
              intro a ha; exact hin_wire gs0 i c a (sepWires_lt f1 g2 a ha)
            rw [hmapu]
            exact sepWires_eval f1 g2 i c
          have hbv : b2z ((wiresList (oneEach i c) gs2).getD wv false) = f2 i + g1 c := by
            rw [hwv_val]
            have hmapv : (sepWires f2 g1).map (fun a => (wiresList (oneEach i c) gs1).getD a false) =
                (sepWires f2 g1).map (fun a => (oneEach i c).getD a false) := by
              apply List.map_congr_left
              intro a ha; exact hin_wire gs1 i c a (sepWires_lt f2 g1 a ha)
            rw [hmapv]
            exact sepWires_eval f2 g1 i c
          rw [hbu, hbv]
        rw [hsingle, Fin.sum_univ_castSucc]
        rfl
  obtain ⟨gsA, gwsA, hvA, hcntA, _, hmemA, hevalA⟩ := hstep_pairs t le_rfl
  let rowCorr : Fin n → ZMod 2 := fun i =>
    b2z (s i) + ∑ r : Fin t, x i ⟨2 * r.val, by omega⟩ * x i ⟨2 * r.val + 1, by omega⟩
  let colCorr : Fin m → ZMod 2 := fun c =>
    ∑ r : Fin t, y c ⟨2 * r.val, by omega⟩ * y c ⟨2 * r.val + 1, by omega⟩
  let corrWires := sepWires rowCorr colCorr
  let allWires := corrWires ++ gwsA
  have hall_lt : ∀ a ∈ allWires, a < w + gsA.length := by
    intro a ha
    rcases List.mem_append.mp ha with h1 | h2
    · exact lt_of_lt_of_le (sepWires_lt rowCorr colCorr a h1) (Nat.le_add_right _ _)
    · exact (hmemA a h2).1
  have hall_dep : ∀ a ∈ allWires, (depthsList w gsA).getD a 0 ≤ 1 := by
    intro a ha
    rcases List.mem_append.mp ha with h1 | h2
    · rw [hin_depth gsA a (sepWires_lt rowCorr colCorr a h1)]; omega
    · exact (hmemA a h2).2
  let finalRes := buildXorList w gsA allWires
  have hfin := buildXorList_spec w allWires gsA 1 hvA hall_lt hall_dep
  obtain ⟨hvF, hcntF, _, _, _, hdepF, hwireF⟩ := hfin
  let C : Circuit := ⟨finalRes.1, finalRes.2⟩
  refine ⟨C, hvF.1, validGates_readsBack w C hvF, ?_, hdepF, ?_⟩
  · intro i c
    have hxlen : (oneEach i c).length = w := oneEach_length i c
    have hval := (hwireF (oneEach i c) hxlen).2
    apply b2z_inj
    have hev : b2z (C.eval (oneEach i c)) =
        b2z (listBoolXor (allWires.map fun a => (wiresList (oneEach i c) gsA).getD a false)) := by
      change b2z ((wiresList (oneEach i c) finalRes.1).getD finalRes.2 false) = _
      rw [hval]
    rw [hev]
    have hxor_app : ∀ l1 l2 : List Bool, listBoolXor (l1 ++ l2) = xor (listBoolXor l1) (listBoolXor l2) := by
      intro l1 l2
      induction l1 with
      | nil => simp [listBoolXor]
      | cons a r ih =>
        simp only [List.cons_append, listBoolXor, List.foldr_cons] at ih ⊢
        rw [ih, Bool.xor_assoc]
    rw [List.map_append, hxor_app, b2z_xor]
    have hcorr_map : corrWires.map (fun a => (wiresList (oneEach i c) gsA).getD a false) =
        corrWires.map (fun a => (oneEach i c).getD a false) := by
      apply List.map_congr_left
      intro a ha; exact hin_wire gsA i c a (sepWires_lt rowCorr colCorr a ha)
    rw [hcorr_map, sepWires_eval rowCorr colCorr i c, hevalA i c]
    have hrhs : b2z (decide (b2z (s i) + dotProduct (x i) (y c) = 1)) = b2z (s i) + dotProduct (x i) (y c) :=
      b2z_decide_eq_one _
    rw [hrhs]
    have hdot_split : dotProduct (x i) (y c) =
        ∑ r : Fin t, (x i ⟨2 * r.val, by omega⟩ * y c ⟨2 * r.val, by omega⟩ +
                      x i ⟨2 * r.val + 1, by omega⟩ * y c ⟨2 * r.val + 1, by omega⟩) := by
      unfold dotProduct
      let e : Fin t × Fin 2 ≃ Fin (2 * t) :=
        { toFun := fun ⟨r, b⟩ => ⟨2 * r.val + b.val, by omega⟩
          invFun := fun p => (⟨p.val / 2, by omega⟩, ⟨p.val % 2, by omega⟩)
          left_inv := fun ⟨r, b⟩ => by ext <;> simp <;> omega
          right_inv := fun p => by ext; simp; omega }
      rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro r _
      rw [Fin.sum_univ_two]
      rfl
    rw [hdot_split]
    dsimp only [rowCorr, colCorr]
    have hsum_cancel :
        (∑ r : Fin t, x i ⟨2 * r.val, by omega⟩ * x i ⟨2 * r.val + 1, by omega⟩) +
        (∑ r : Fin t, y c ⟨2 * r.val, by omega⟩ * y c ⟨2 * r.val + 1, by omega⟩) +
        (∑ r : Fin t, (x i ⟨2 * r.val, by omega⟩ + y c ⟨2 * r.val + 1, by omega⟩) *
                      (x i ⟨2 * r.val + 1, by omega⟩ + y c ⟨2 * r.val, by omega⟩)) =
        ∑ r : Fin t, (x i ⟨2 * r.val, by omega⟩ * y c ⟨2 * r.val, by omega⟩ +
                      x i ⟨2 * r.val + 1, by omega⟩ * y c ⟨2 * r.val + 1, by omega⟩) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      have h1 := zmod2_add_self (x i ⟨2 * r.val, by omega⟩ * x i ⟨2 * r.val + 1, by omega⟩)
      have h2 := zmod2_add_self (y c ⟨2 * r.val, by omega⟩ * y c ⟨2 * r.val + 1, by omega⟩)
      linear_combination h1 + h2
    linear_combination hsum_cancel
  · rw [show C.gates.countP nonlinearG = gsA.countP nonlinearG from hcntF, hcntA]

lemma card_filter_corr {m : ℕ} (P : Fin m → Prop) [DecidablePred P] :
    (m : ℤ) - 2 * ((Finset.univ.filter P).card : ℤ) =
      ∑ c : Fin m, (if P c then (-1 : ℤ) else 1) := by
  have h1 : ∑ c : Fin m, (if P c then (-1 : ℤ) else 1) =
      ∑ c : Fin m, ((1 : ℤ) - (if P c then (2 : ℤ) else 0)) := by
    apply Finset.sum_congr rfl
    intro c _; split_ifs <;> ring
  rw [h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  ring

lemma nat_modEq_iff_int_two_modEq (q m d D : ℕ) :
    Nat.ModEq q d D ↔ Int.ModEq (2 * (q : ℤ)) ((m : ℤ) - 2 * (D : ℤ)) ((m : ℤ) - 2 * (d : ℤ)) := by
  rw [← Int.natCast_modEq_iff, Int.modEq_iff_dvd, Int.modEq_iff_dvd]
  have hdiff : ((m : ℤ) - 2 * (d : ℤ)) - ((m : ℤ) - 2 * (D : ℤ)) = 2 * ((D : ℤ) - (d : ℤ)) := by ring
  rw [hdiff]
  exact (mul_dvd_mul_iff_left (by decide : (2 : ℤ) ≠ 0)).symm

end PEqualNP.Outside.L_meta_33595_aux

open PEqualNP.Outside.L_meta_33595_aux
theorem PEqualNP.Outside.L_meta_33595 :
(let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depth := fun (w : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  (C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)).getD C.output 0
∀ (n m t : ℕ) (_ : 0 < n) (_ : 0 < m) (D q : Fin n → Fin n → ℕ),
  let V := Fin (2*t) → ZMod 2
  let W := fun (K : V → ℤ) (y : V) =>
    ∑ z : V, K z * (if dotProduct y z = 0 then (1 : ℤ) else -1)
  (∃ (T : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
    PEqualNP.Represents.Represents T C ∧ depth (n+m) C ≤ 1 ∧
    C.gates.countP nonlinear ≤ t ∧
    ∀ i j, Nat.ModEq (q i j) ((Finset.univ.filter (fun c : Fin m => T i c ≠ T j c)).card) (D i j)) ↔
  ∃ (x : Fin n → V) (s : Fin n → Bool) (K : V → ℤ),
    K 0 = (m : ℤ) ∧
    (∀ y, 0 ≤ W K y ∧ (2^(2*t) : ℤ) ∣ W K y) ∧
    ∀ i j, Int.ModEq (2*(q i j : ℤ)) ((m : ℤ)-2*(D i j : ℤ))
      (if s i = s j then K (x i+x j) else -(K (x i+x j)))) := by
  intro nonlinear depth n m t _ _ D q
  dsimp only [nonlinear, depth]
  constructor
  · rintro ⟨T, C, hfan, hrb, hrep, hdep, hcnt, hmod⟩
    obtain ⟨A, B, x, y, hfac⟩ := forward_factorization T C hfan hrb hrep hdep hcnt
    let s : Fin n → Bool := fun i => decide (A i = 1)
    let K : (Fin (2 * t) → ZMod 2) → ℤ := fun z => ∑ c : Fin m, chi (dotProduct z (y c))
    refine ⟨x, s, K, ?_, ?_, ?_⟩
    · simp [K, chi]
    · intro u
      have hW : (∑ z : Fin (2 * t) → ZMod 2, K z * (if dotProduct u z = 0 then (1 : ℤ) else -1)) =
          (2 ^ (2 * t) : ℤ) * ((Finset.univ.filter (fun c : Fin m => y c = u)).card : ℤ) := by
        calc ∑ z : Fin (2 * t) → ZMod 2, K z * (if dotProduct u z = 0 then (1 : ℤ) else -1)
            = ∑ z : Fin (2 * t) → ZMod 2, ∑ c : Fin m, chi (dotProduct z (y c)) * chi (dotProduct u z) := by
              apply Finset.sum_congr rfl; intro z _; simp [K, chi]
          _ = ∑ c : Fin m, ∑ z : Fin (2 * t) → ZMod 2, chi (dotProduct (u + y c) z) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl; intro c _
              apply Finset.sum_congr rfl; intro z _
              rw [← chi_add, add_dotProduct, dotProduct_comm z (y c), add_comm]
          _ = ∑ c : Fin m, (if u + y c = 0 then (2 ^ (2 * t) : ℤ) else 0) := by
              apply Finset.sum_congr rfl; intro c _; exact sum_chi_dot (u + y c)
          _ = ∑ c : Fin m, (if y c = u then (2 ^ (2 * t) : ℤ) else 0) := by
              apply Finset.sum_congr rfl; intro c _
              have heq : u + y c = 0 ↔ y c = u := by
                constructor
                · intro h; funext k
                  have hk := congrFun h k
                  exact ((zmod2_eq_iff_add_eq_zero (y c k) (u k)).mpr (by simpa [add_comm] using hk))
                · intro h; subst h; funext k; exact zmod2_add_self (y c k)
              simp [heq]
          _ = (2 ^ (2 * t) : ℤ) * ((Finset.univ.filter (fun c : Fin m => y c = u)).card : ℤ) := by
              rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
      rw [hW]
      exact ⟨by positivity, dvd_mul_right _ _⟩
    · intro i j
      have hcorr : (m : ℤ) - 2 * ((Finset.univ.filter (fun c : Fin m => T i c ≠ T j c)).card : ℤ) =
          if s i = s j then K (x i + x j) else -(K (x i + x j)) := by
        rw [card_filter_corr]
        have hs : ∀ r : Fin n, b2z (s r) = A r := fun r => b2z_decide_eq_one (A r)
        have hterm : ∀ c : Fin m, (if T i c ≠ T j c then (-1 : ℤ) else 1) =
            chi (A i + A j) * chi (dotProduct (x i + x j) (y c)) := by
          intro c
          rw [← chi_b2z_ne, hfac i c, hfac j c, ← chi_add]
          congr 1
          rw [add_dotProduct]
          have hB := zmod2_add_self (B c)
          linear_combination hB
        simp_rw [hterm, ← Finset.mul_sum]
        have hsign : chi (A i + A j) = if s i = s j then (1 : ℤ) else -1 := by
          rw [← hs i, ← hs j]
          cases s i <;> cases s j <;> decide
        rw [hsign]
        split_ifs <;> simp [K]
      rw [← hcorr]
      exact (nat_modEq_iff_int_two_modEq (q i j) m _ (D i j)).mp (hmod i j)
  · rintro ⟨x, s, K, hK0, hW, hmod⟩
    let V := Fin (2 * t) → ZMod 2
    let Wf : V → ℤ := fun u => ∑ z : V, K z * chi (dotProduct u z)
    have hW_pos : ∀ u : V, 0 ≤ Wf u ∧ (2 ^ (2 * t) : ℤ) ∣ Wf u := hW
    let cnt : V → ℕ := fun u => (Wf u / (2 ^ (2 * t) : ℤ)).toNat
    have hcnt_mul : ∀ u : V, (cnt u : ℤ) * (2 ^ (2 * t) : ℤ) = Wf u := by
      intro u
      obtain ⟨hnn, hdvd⟩ := hW_pos u
      have h2pos : (0 : ℤ) < 2 ^ (2 * t) := by positivity
      have hdiv_nn : 0 ≤ Wf u / (2 ^ (2 * t) : ℤ) := Int.ediv_nonneg hnn (le_of_lt h2pos)
      dsimp only [cnt]
      rw [Int.toNat_of_nonneg hdiv_nn, Int.ediv_mul_cancel hdvd]
    have hK_inv : ∀ z : V, K z = ∑ u : V, (cnt u : ℤ) * chi (dotProduct z u) := by
      intro z
      have h2ne : (2 ^ (2 * t) : ℤ) ≠ 0 := by positivity
      apply mul_left_cancel₀ h2ne
      calc (2 ^ (2 * t) : ℤ) * K z
          = ∑ w : V, K w * (if w + z = 0 then (2 ^ (2 * t) : ℤ) else 0) := by
            have h1 : ∀ w : V, (w + z = 0) ↔ (w = z) := by
              intro w; constructor
              · intro h; funext k; exact (zmod2_eq_iff_add_eq_zero (w k) (z k)).mpr (congrFun h k)
              · intro h; subst h; funext k; exact zmod2_add_self (w k)
            simp_rw [h1]
            simp [mul_ite, mul_comm]
        _ = ∑ w : V, K w * ∑ u : V, chi (dotProduct (w + z) u) := by
            apply Finset.sum_congr rfl; intro w _; rw [sum_chi_dot]
        _ = ∑ u : V, Wf u * chi (dotProduct z u) := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro u _
            simp only [Wf, Finset.sum_mul]
            apply Finset.sum_congr rfl; intro w _
            rw [add_dotProduct, chi_add, dotProduct_comm u w]
            ring
        _ = ∑ u : V, ((cnt u : ℤ) * (2 ^ (2 * t) : ℤ)) * chi (dotProduct z u) := by
            apply Finset.sum_congr rfl; intro u _; rw [hcnt_mul u]
        _ = (2 ^ (2 * t) : ℤ) * ∑ u : V, (cnt u : ℤ) * chi (dotProduct z u) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro u _; ring
    have hsum_cnt : ∑ u : V, cnt u = m := by
      have hZ : (∑ u : V, (cnt u : ℤ)) = (m : ℤ) := by
        have h0 := hK_inv 0
        simp only [zero_dotProduct, chi_zero, mul_one] at h0
        linarith [hK0]
      exact_mod_cast hZ
    let L : List V := (Finset.univ : Finset V).toList.flatMap (fun u => List.replicate (cnt u) u)
    have hL_len : L.length = m := by
      rw [List.length_flatMap]
      have h1 : ((Finset.univ : Finset V).toList.map (fun u => (List.replicate (cnt u) u).length)).sum =
          ∑ u : V, cnt u := by
        simp only [List.length_replicate]
        rw [← List.sum_toFinset _ (Finset.nodup_toList _)]
        simp
      rw [h1, hsum_cnt]
    let y : Fin m → V := fun c => L[c.val]'(by omega)
    have hK_eq_y : ∀ z : V, K z = ∑ c : Fin m, chi (dotProduct z (y c)) := by
      intro z
      rw [hK_inv z]
      have hsumL : (L.map (fun u => chi (dotProduct z u))).sum =
          ∑ c : Fin m, chi (dotProduct z (y c)) := by
        have hL_eq : L.map (fun u => chi (dotProduct z u)) =
            (List.finRange m).map (fun c => chi (dotProduct z (y c))) := by
          apply List.ext_getElem
          · simp [hL_len]
          · intro k hk1 hk2
            simp [y]
        rw [hL_eq, ← List.sum_toFinset _ (List.nodup_finRange m)]
        have : (List.finRange m).toFinset = Finset.univ := by ext a; simp
        rw [this]
      rw [← hsumL]
      dsimp only [L]
      rw [List.map_flatMap]
      have hsf : ∀ (xs : List V) (f : V → List ℤ), (xs.flatMap f).sum = (xs.map fun a => (f a).sum).sum := by
        intro xs f
        induction xs with
        | nil => rfl
        | cons a r ih => simp [List.flatMap_cons, List.sum_append, ih]
      rw [hsf]
      have h3 : ((Finset.univ : Finset V).toList.map (fun u => ((List.replicate (cnt u) u).map (fun v => chi (dotProduct z v))).sum)).sum =
          ((Finset.univ : Finset V).toList.map (fun u => (cnt u : ℤ) * chi (dotProduct z u))).sum := by
        congr 1
        apply List.map_congr_left
        intro u _
        simp [List.map_replicate, List.sum_replicate, nsmul_eq_mul]
      rw [h3]
      rw [← List.sum_toFinset _ (Finset.nodup_toList _)]
      simp
    obtain ⟨C, hfan, hrb, hrep, hdep, hcnt⟩ := build_circuit_from_factor s x y
    let T : Fin n → Fin m → Bool := fun i c => decide (b2z (s i) + dotProduct (x i) (y c) = 1)
    refine ⟨T, C, hfan, hrb, hrep, hdep, hcnt, ?_⟩
    intro i j
    have hcorr : (m : ℤ) - 2 * ((Finset.univ.filter (fun c : Fin m => T i c ≠ T j c)).card : ℤ) =
        if s i = s j then K (x i + x j) else -(K (x i + x j)) := by
      rw [card_filter_corr]
      have hTb : ∀ r c, b2z (T r c) = b2z (s r) + dotProduct (x r) (y c) := fun r c =>
        b2z_decide_eq_one _
      have hterm : ∀ c : Fin m, (if T i c ≠ T j c then (-1 : ℤ) else 1) =
          chi (b2z (s i) + b2z (s j)) * chi (dotProduct (x i + x j) (y c)) := by
        intro c
        rw [← chi_b2z_ne, hTb i c, hTb j c, ← chi_add]
        congr 1
        rw [add_dotProduct]
        ring
      simp_rw [hterm, ← Finset.mul_sum]
      rw [← hK_eq_y (x i + x j)]
      have hsign : chi (b2z (s i) + b2z (s j)) = if s i = s j then (1 : ℤ) else -1 := by
        cases s i <;> cases s j <;> decide
      rw [hsign]
      split_ifs <;> simp
    rw [nat_modEq_iff_int_two_modEq, hcorr]
    exact hmod i j
