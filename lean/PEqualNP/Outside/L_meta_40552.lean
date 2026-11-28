import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40552_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

def nlGate (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depthsOf (w : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat])
    (List.replicate w 0)

def wiresOf (x : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem wiresOf_length (x : List Bool) (gs : List Gate) :
    (wiresOf x gs).length = x.length + gs.length := by
  unfold wiresOf
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem depthsOf_length (w : ℕ) (gs : List Gate) :
    (depthsOf w gs).length = w + gs.length := by
  unfold depthsOf
  have aux : ∀ (ds : List ℕ) (gs : List Gate),
      (gs.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat]) ds).length =
      ds.length + gs.length := by
    intro ds gs
    induction gs generalizing ds with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  rw [aux, List.length_replicate]

theorem wiresOf_append (x : List Bool) (gs1 gs2 : List Gate) :
    wiresOf x (gs1 ++ gs2) =
      gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (wiresOf x gs1) := by
  unfold wiresOf
  rw [List.foldl_append]

theorem depthsOf_append (w : ℕ) (gs1 gs2 : List Gate) :
    depthsOf w (gs1 ++ gs2) =
      gs2.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat])
        (depthsOf w gs1) := by
  unfold depthsOf
  rw [List.foldl_append]

theorem foldl_append_ext {α β : Type*} (f : List α → β → α) (l : List β) (init : List α) :
    ∃ ext : List α, l.foldl (fun acc b => acc ++ [f acc b]) init = init ++ ext := by
  induction l generalizing init with
  | nil => exact ⟨[], by simp⟩
  | cons b l ih =>
    rw [List.foldl_cons]
    obtain ⟨ext, hext⟩ := ih (init ++ [f init b])
    exact ⟨f init b :: ext, by rw [hext]; simp⟩

theorem wiresOf_append_getD_lt (x : List Bool) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < x.length + gs1.length) :
    (wiresOf x (gs1 ++ gs2)).getD k false = (wiresOf x gs1).getD k false := by
  rw [wiresOf_append]
  obtain ⟨ext, hext⟩ := foldl_append_ext
    (fun (w : List Bool) (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false))
    gs2 (wiresOf x gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [wiresOf_length]; exact hk)]

theorem depthsOf_append_getD_lt (w : ℕ) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < w + gs1.length) :
    (depthsOf w (gs1 ++ gs2)).getD k 0 = (depthsOf w gs1).getD k 0 := by
  rw [depthsOf_append]
  obtain ⟨ext, hext⟩ := foldl_append_ext
    (fun (ds : List ℕ) (g : Gate) =>
      (g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat)
    gs2 (depthsOf w gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [depthsOf_length]; exact hk)]

theorem wiresOf_getD_input (x : List Bool) (gs : List Gate) {k : ℕ} (hk : k < x.length) :
    (wiresOf x gs).getD k false = x.getD k false := by
  have h := wiresOf_append_getD_lt x [] gs (by simpa using hk)
  simpa [wiresOf] using h

theorem depthsOf_getD_input (w : ℕ) (gs : List Gate) {k : ℕ} (hk : k < w) :
    (depthsOf w gs).getD k 0 = 0 := by
  have h := depthsOf_append_getD_lt w [] gs (by simpa using hk)
  simp only [List.nil_append] at h
  rw [h]
  unfold depthsOf
  simp only [List.foldl_nil]
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_replicate]

theorem wiresOf_getD_gate (x : List Bool) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
    (hrb : ∀ a ∈ (gs[idx]).inputs, a < x.length + idx) :
    (wiresOf x gs).getD (x.length + idx) false =
      (gs[idx]).op.eval ((gs[idx]).inputs.map fun a => (wiresOf x gs).getD a false) := by
  have hsplit : gs = (gs.take idx ++ [gs[idx]]) ++ gs.drop (idx + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  have hlen1 : (gs.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
  have hlen2 : (gs.take idx ++ [gs[idx]]).length = idx + 1 := by
    rw [List.length_append, hlen1]
    rfl
  conv_lhs => rw [hsplit]
  rw [wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
  have hlw : (wiresOf x (gs.take idx)).length = x.length + idx := by
    rw [wiresOf_length, hlen1]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hlw, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro a ha
  have halt : a < x.length + (gs.take idx).length := by rw [hlen1]; exact hrb a ha
  conv_rhs => rw [hsplit]
  rw [wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [wiresOf_append_getD_lt x (gs.take idx) [gs[idx]] halt]

theorem depthsOf_getD_gate (w : ℕ) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
    (hrb : ∀ a ∈ (gs[idx]).inputs, a < w + idx) :
    (depthsOf w gs).getD (w + idx) 0 =
      ((gs[idx]).inputs.map (fun a => (depthsOf w gs).getD a 0)).foldr max 0 +
        (nlGate (gs[idx])).toNat := by
  have hsplit : gs = (gs.take idx ++ [gs[idx]]) ++ gs.drop (idx + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  have hlen1 : (gs.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
  have hlen2 : (gs.take idx ++ [gs[idx]]).length = idx + 1 := by
    rw [List.length_append, hlen1]
    rfl
  conv_lhs => rw [hsplit]
  rw [depthsOf_append_getD_lt w (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
  have hld : (depthsOf w (gs.take idx)).length = w + idx := by
    rw [depthsOf_length, hlen1]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hld, Nat.sub_self, List.getD_cons_zero]
  congr 2
  apply List.map_congr_left
  intro a ha
  have halt : a < w + (gs.take idx).length := by rw [hlen1]; exact hrb a ha
  conv_rhs => rw [hsplit]
  rw [depthsOf_append_getD_lt w (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [depthsOf_append_getD_lt w (gs.take idx) [gs[idx]] halt]

theorem anf_one (f : Bool → Bool) (x : Bool) :
    b2z (f x) = b2z (f false) + (b2z (f false) + b2z (f true)) * b2z x := by
  cases x <;> cases h0 : f false <;> cases h1 : f true <;> decide

theorem anf_two (f : Bool → Bool → Bool) (x y : Bool) :
    b2z (f x y) =
      b2z (f false false) +
      (b2z (f false false) + b2z (f true false)) * b2z x +
      (b2z (f false false) + b2z (f false true)) * b2z y +
      b2z (xor (xor (f false false) (f false true)) (xor (f true false) (f true true))) *
        (b2z x * b2z y) := by
  cases x <;> cases y <;>
    cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;> decide

/-! ## Representation by low degree polynomials over GF(2) -/

open MvPolynomial in
def Rep {m : ℕ} (f : (Fin m → Bool) → Bool) (D : ℕ) : Prop :=
  ∃ Q : MvPolynomial (Fin m) (ZMod 2), Q.totalDegree ≤ D ∧
    ∀ y, b2z (f y) = MvPolynomial.eval (fun i => b2z (y i)) Q

theorem rep_mono {m : ℕ} {f : (Fin m → Bool) → Bool} {D D' : ℕ} (h : D ≤ D') (hf : Rep f D) :
    Rep f D' := by
  obtain ⟨Q, hQ, hQe⟩ := hf
  exact ⟨Q, hQ.trans h, hQe⟩

theorem rep_congr {m : ℕ} {f g : (Fin m → Bool) → Bool} {D : ℕ} (h : ∀ y, f y = g y)
    (hf : Rep f D) : Rep g D := by
  obtain ⟨Q, hQ, hQe⟩ := hf
  exact ⟨Q, hQ, fun y => by rw [← h y]; exact hQe y⟩

theorem rep_const {m : ℕ} (c : Bool) : Rep (fun (_ : Fin m → Bool) => c) 0 :=
  ⟨MvPolynomial.C (b2z c), by simp [MvPolynomial.totalDegree_C], fun y => by simp⟩

theorem rep_var {m : ℕ} (i : Fin m) : Rep (fun (y : Fin m → Bool) => y i) 1 :=
  ⟨MvPolynomial.X i, by simp [MvPolynomial.totalDegree_X], fun y => by simp⟩

theorem deg_Cmul {m : ℕ} (c : ZMod 2) (Q : MvPolynomial (Fin m) (ZMod 2)) :
    (MvPolynomial.C c * Q).totalDegree ≤ Q.totalDegree := by
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp [MvPolynomial.totalDegree_C]

theorem rep_un {m : ℕ} {f : (Fin m → Bool) → Bool} {D : ℕ} (g : Bool → Bool) (hf : Rep f D) :
    Rep (fun y => g (f y)) D := by
  obtain ⟨Q, hQ, hQe⟩ := hf
  refine ⟨MvPolynomial.C (b2z (g false)) +
    MvPolynomial.C (b2z (g false) + b2z (g true)) * Q, ?_, fun y => ?_⟩
  · refine (MvPolynomial.totalDegree_add _ _).trans ?_
    simp only [MvPolynomial.totalDegree_C, zero_le, max_le_iff, true_and]
    exact (deg_Cmul _ _).trans hQ
  · rw [anf_one g (f y), hQe y]
    simp

theorem rep_bin {m : ℕ} {f g : (Fin m → Bool) → Bool} {D1 D2 : ℕ} (F : Bool → Bool → Bool)
    (hf : Rep f D1) (hg : Rep g D2) :
    Rep (fun y => F (f y) (g y)) (D1 + D2) := by
  obtain ⟨P, hP, hPe⟩ := hf
  obtain ⟨Q, hQ, hQe⟩ := hg
  refine ⟨MvPolynomial.C (b2z (F false false)) +
    MvPolynomial.C (b2z (F false false) + b2z (F true false)) * P +
    MvPolynomial.C (b2z (F false false) + b2z (F false true)) * Q +
    MvPolynomial.C (b2z (xor (xor (F false false) (F false true))
      (xor (F true false) (F true true)))) * (P * Q), ?_, fun y => ?_⟩
  · have h1 := deg_Cmul (b2z (F false false) + b2z (F true false)) P
    have h2 := deg_Cmul (b2z (F false false) + b2z (F false true)) Q
    have h3 := deg_Cmul (b2z (xor (xor (F false false) (F false true))
      (xor (F true false) (F true true)))) (P * Q)
    have h4 := MvPolynomial.totalDegree_mul P Q
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
        · simp [MvPolynomial.totalDegree_C]
        · omega
      · omega
    · omega
  · rw [anf_two F (f y) (g y), hPe y, hQe y]
    simp

theorem rep_bin_lin {m : ℕ} {f g : (Fin m → Bool) → Bool} {D1 D2 : ℕ} (F : Bool → Bool → Bool)
    (hlin : xor (xor (F false false) (F false true)) (xor (F true false) (F true true)) = false)
    (hf : Rep f D1) (hg : Rep g D2) :
    Rep (fun y => F (f y) (g y)) (max D1 D2) := by
  obtain ⟨P, hP, hPe⟩ := hf
  obtain ⟨Q, hQ, hQe⟩ := hg
  refine ⟨MvPolynomial.C (b2z (F false false)) +
    MvPolynomial.C (b2z (F false false) + b2z (F true false)) * P +
    MvPolynomial.C (b2z (F false false) + b2z (F false true)) * Q, ?_, fun y => ?_⟩
  · have h1 := deg_Cmul (b2z (F false false) + b2z (F true false)) P
    have h2 := deg_Cmul (b2z (F false false) + b2z (F false true)) Q
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
      · simp [MvPolynomial.totalDegree_C]
      · omega
    · omega
  · rw [anf_two F (f y) (g y), hPe y, hQe y, hlin]
    simp [b2z]

theorem rep_xor {m : ℕ} {f g : (Fin m → Bool) → Bool} {D1 D2 : ℕ}
    (hf : Rep f D1) (hg : Rep g D2) : Rep (fun y => xor (f y) (g y)) (max D1 D2) :=
  rep_bin_lin (fun a b => xor a b) (by decide) hf hg

/-- Every wire of a fan-in two circuit fed with affine data is a polynomial of degree at most
`2 ^ depth`. -/
theorem wires_rep {m w : ℕ} (X : (Fin m → Bool) → List Bool) (gs : List Gate)
    (hlen : ∀ y, (X y).length = w)
    (hin : ∀ v, Rep (fun y => (X y).getD v false) 1)
    (har : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hrb : ∀ j (hj : j < gs.length), ∀ a ∈ (gs[j]).inputs, a < w + j) :
    ∀ idx, Rep (fun y => (wiresOf (X y) gs).getD idx false)
      (2 ^ ((depthsOf w gs).getD idx 0)) := by
  intro idx
  induction idx using Nat.strong_induction_on with
  | _ idx ih =>
  by_cases hw : idx < w
  · rw [depthsOf_getD_input w gs hw]
    refine rep_congr (fun y => ?_) (hin idx)
    rw [wiresOf_getD_input (X y) gs (by rw [hlen]; exact hw)]
  by_cases hg : idx - w < gs.length
  · obtain ⟨j, rfl⟩ : ∃ j, idx = w + j := ⟨idx - w, by omega⟩
    have hj : j < gs.length := by omega
    have hval : ∀ y, (wiresOf (X y) gs).getD (w + j) false =
        (gs[j]).op.eval ((gs[j]).inputs.map fun a => (wiresOf (X y) gs).getD a false) := by
      intro y
      have := wiresOf_getD_gate (X y) gs hj (by rw [hlen]; exact hrb j hj)
      rwa [hlen] at this
    rw [depthsOf_getD_gate w gs hj (hrb j hj)]
    have hlt : ∀ a ∈ (gs[j]).inputs, a < w + j := hrb j hj
    have hl2 : (gs[j]).inputs.length ≤ 2 := har _ (List.getElem_mem hj)
    unfold nlGate
    generalize hgj : gs[j] = g at hval hlt hl2
    obtain ⟨op, ins⟩ := g
    simp only at hval hlt hl2 ⊢
    match ins, hval, hlt, hl2 with
    | [], hval, _, _ =>
      refine rep_mono ?_ (rep_congr (fun y => (hval y).symm) (rep_const (op.eval [])))
      simp
    | [a], hval, hlt, _ =>
      have ha := ih a (hlt a (by simp))
      refine rep_mono (by simp) (rep_congr (fun y => (hval y).symm)
        (rep_un (fun p => op.eval [p]) ha))
    | [a, b], hval, hlt, _ =>
      have ha := ih a (hlt a (by simp))
      have hb := ih b (hlt b (by simp))
      simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
        List.length_cons, List.length_nil] at hval ⊢
      cases hnl : xor (xor (op.eval [false, false]) (op.eval [false, true]))
          (xor (op.eval [true, false]) (op.eval [true, true]))
      · refine rep_mono ?_ (rep_congr (fun y => (hval y).symm)
          (rep_bin_lin (fun p q => op.eval [p, q]) hnl ha hb))
        simp only [Nat.max_zero, beq_self_eq_true, Bool.and_false, Bool.toNat_false, add_zero]
        rcases le_total ((depthsOf w gs).getD a 0) ((depthsOf w gs).getD b 0) with hab | hab
        · rw [max_eq_right hab, max_eq_right (Nat.pow_le_pow_right (by norm_num) hab)]
        · rw [max_eq_left hab, max_eq_left (Nat.pow_le_pow_right (by norm_num) hab)]
      · refine rep_mono ?_ (rep_congr (fun y => (hval y).symm)
          (rep_bin (fun p q => op.eval [p, q]) ha hb))
        simp only [Nat.max_zero, beq_self_eq_true, Bool.and_true, Bool.toNat_true]
        rw [pow_succ]
        have h1 : 2 ^ (depthsOf w gs).getD a 0 ≤ 2 ^ max ((depthsOf w gs).getD a 0)
            ((depthsOf w gs).getD b 0) := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
        have h2 : 2 ^ (depthsOf w gs).getD b 0 ≤ 2 ^ max ((depthsOf w gs).getD a 0)
            ((depthsOf w gs).getD b 0) := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
        omega
    | _ :: _ :: _ :: _, _, _, hl2 => simp at hl2
  · refine rep_mono (by simp) (rep_congr (fun y => ?_) (rep_const false))
    rw [List.getD_eq_default]
    rw [wiresOf_length, hlen]
    omega

/-- A polynomial of degree below the number of variables sums to zero over the cube. -/
theorem cube_sum_zero {m : ℕ} (Q : MvPolynomial (Fin m) (ZMod 2)) (hQ : Q.totalDegree < m) :
    ∑ y : Fin m → Bool, MvPolynomial.eval (fun i => b2z (y i)) Q = 0 := by
  simp_rw [MvPolynomial.eval_eq']
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro μ hμ
  rw [← Finset.mul_sum]
  have hex : ∃ i0, μ i0 = 0 := by
    by_contra hne
    push Not at hne
    have h1 := MvPolynomial.le_totalDegree hμ
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1
    have h2 : ∑ _i : Fin m, 1 ≤ ∑ i : Fin m, μ i :=
      Finset.sum_le_sum (fun i _ => Nat.one_le_iff_ne_zero.mpr (hne i))
    simp at h2
    omega
  obtain ⟨i0, hi0⟩ := hex
  rw [Finset.sum_ninvolution (fun y => Function.update y i0 (!y i0))]
  · simp
  · intro y
    have : (∏ i, b2z (Function.update y i0 (!y i0) i) ^ μ i) = ∏ i, b2z (y i) ^ μ i := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i = i0
      · subst hi; simp [hi0]
      · simp [Function.update_of_ne hi]
    rw [this]
    exact zmod2_add_self _
  · intro y _ heq
    have := congrFun heq i0
    simp at this
  · intro y; simp
  · intro y; simp


/-! ## Data layout -/

def chiF (u : ℕ → Bool) (i : ℕ) : Bool := xor (u i) (!(u (i+1)) && u (i+2))

def dataOf (h n : ℕ) (mask : Fin n → Finset ℕ) (u : Fin n → Fin (2^(h+2))) : List Bool :=
  (List.ofFn (fun j : Fin n =>
    let bits := fun l : Nat => (u j).val.testBit l
    List.ofFn (fun i : Fin h => chiF bits i) ++ [bits h, bits (h+1)] ++
    List.ofFn (fun i : Fin h => if i.val ∈ mask j then bits i else false))).flatten

theorem flatten_ofFn_length {α : Type*} {n B : ℕ} (f : Fin n → List α)
    (hf : ∀ j, (f j).length = B) : (List.ofFn f).flatten.length = n * B := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, hf 0,
      ih (fun i => f i.succ) (fun i => hf _)]
    ring

theorem flatten_ofFn_getD {α : Type*} {n B : ℕ} (f : Fin n → List α)
    (hf : ∀ j, (f j).length = B) (j : Fin n) (q : ℕ) (hq : q < B) (d : α) :
    (List.ofFn f).flatten.getD (j.val * B + q) d = (f j).getD q d := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · simp only [Fin.val_zero, zero_mul, zero_add]
      rw [List.getD_append _ _ _ _ (by rw [hf 0]; exact hq)]
    · have e : j'.succ.val * B + q = B + (j'.val * B + q) := by
        rw [Fin.val_succ, add_mul, one_mul]; omega
      rw [e, List.getD_append_right _ _ _ _ (by rw [hf 0]; omega), hf 0, Nat.add_sub_cancel_left]
      exact ih (fun i => f i.succ) (fun i => hf _) j'

def blockVal (bits : ℕ → Bool) (M : Finset ℕ) (h q : ℕ) : Bool :=
  if q < h then chiF bits q else if q < h + 2 then bits q else
    (if q - (h+2) ∈ M then bits (q - (h+2)) else false)

theorem dataOf_length (h n : ℕ) (mask : Fin n → Finset ℕ) (u : Fin n → Fin (2^(h+2))) :
    (dataOf h n mask u).length = n * (2*h+2) := by
  unfold dataOf
  exact flatten_ofFn_length _ (fun j => by simp; omega)

theorem dataOf_getD (h n : ℕ) (mask : Fin n → Finset ℕ) (u : Fin n → Fin (2^(h+2)))
    (j : Fin n) (q : ℕ) (hq : q < 2*h+2) :
    (dataOf h n mask u).getD (j.val * (2*h+2) + q) false =
      blockVal (fun l => (u j).val.testBit l) (mask j) h q := by
  unfold dataOf
  rw [flatten_ofFn_getD _ (fun j => by simp; omega) j q hq]
  unfold blockVal
  simp only
  by_cases h1 : q < h
  · rw [if_pos h1, List.getD_append _ _ _ _ (by simp; omega),
      List.getD_append _ _ _ _ (by simp; omega)]
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  · rw [if_neg h1]
    by_cases h2 : q < h + 2
    · rw [if_pos h2, List.getD_append _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_ofFn]
      obtain ⟨r, rfl⟩ : ∃ r, q = h + r := ⟨q - h, by omega⟩
      have hr : r < 2 := by omega
      interval_cases r <;> simp
    · rw [if_neg h2, List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]

/-! ## The restricted family for the lower bound -/

section family

variable (s len : ℕ)

def tY (y : Fin (len+1) → Bool) (a : ℕ) : Bool := if ha : a < len then y ⟨a, by omega⟩ else false

def zY (y : Fin (len+1) → Bool) : Bool := y (Fin.last len)

def rY (y : Fin (len+1) → Bool) (a : ℕ) : Bool :=
  zY len y && decide (∀ b < len, a ≤ b → tY len y b = false)

def bitsY (y : Fin (len+1) → Bool) (p : ℕ) : Bool :=
  if p + 1 = s then true
  else if s ≤ p ∧ p < s + 2*len then
    (if (p - s) % 2 = 0 then rY len y ((p - s)/2) else tY len y ((p - s)/2))
  else if p = s + 2*len then zY len y else false

variable {s len}

theorem rY_step (y : Fin (len+1) → Bool) {a : ℕ} (ha : a < len) :
    rY len y a = (!tY len y a && rY len y (a+1)) := by
  unfold rY
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  constructor
  · rintro ⟨hz, H⟩
    exact ⟨H a ha le_rfl, hz, fun b hb hab => H b hb (by omega)⟩
  · rintro ⟨ht, hz, H⟩
    refine ⟨hz, fun b hb hab => ?_⟩
    rcases Nat.eq_or_lt_of_le hab with rfl | hlt
    · exact ht
    · exact H b hb hlt

theorem rY_len (y : Fin (len+1) → Bool) : rY len y len = zY len y := by
  unfold rY
  cases zY len y
  · simp
  · simp only [Bool.true_and, decide_eq_true_eq]
    intro b hb hab; omega

theorem rY_t (y : Fin (len+1) → Bool) {a : ℕ} (ha : a < len) (hr : rY len y a = true) :
    tY len y a = false := by
  unfold rY at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  exact hr.2 a ha le_rfl

theorem bits_pre (y : Fin (len+1) → Bool) {p : ℕ} (hp : p + 1 = s) : bitsY s len y p = true := by
  unfold bitsY; rw [if_pos hp]

theorem bits_low (y : Fin (len+1) → Bool) {p : ℕ} (hp : p + 1 < s) :
    bitsY s len y p = false := by
  unfold bitsY
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem bits_high (y : Fin (len+1) → Bool) {p : ℕ} (hp : s + 2*len < p) :
    bitsY s len y p = false := by
  unfold bitsY
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem bits_run (y : Fin (len+1) → Bool) {a : ℕ} (ha : a ≤ len) :
    bitsY s len y (s + 2*a) = rY len y a := by
  unfold bitsY
  rw [if_neg (by omega)]
  rcases Nat.eq_or_lt_of_le ha with rfl | hlt
  · rw [if_neg (by omega), if_pos rfl, rY_len]
  · rw [if_pos ⟨by omega, by omega⟩, if_pos (by omega)]
    congr 1; omega

theorem bits_guard (y : Fin (len+1) → Bool) {a : ℕ} (ha : a < len) :
    bitsY s len y (s + 2*a + 1) = tY len y a := by
  unfold bitsY
  rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, if_neg (by omega)]
  congr 1; omega

theorem bits_run_eq (y : Fin (len+1) → Bool) {p a : ℕ} (hp : p = s + 2*a) (ha : a ≤ len) :
    bitsY s len y p = rY len y a := by
  subst hp; exact bits_run y ha

theorem bits_guard_eq (y : Fin (len+1) → Bool) {p a : ℕ} (hp : p = s + 2*a + 1) (ha : a < len) :
    bitsY s len y p = tY len y a := by
  subst hp; exact bits_guard y ha

theorem rep_t (a : ℕ) : Rep (fun y => tY len y a) 1 := by
  by_cases ha : a < len
  · refine rep_congr (fun y => ?_) (rep_var (⟨a, by omega⟩ : Fin (len+1)))
    simp [tY, ha]
  · refine rep_mono (by norm_num) (rep_congr (fun y => ?_) (rep_const false))
    simp [tY, ha]

theorem rep_z : Rep (fun y => zY len y) 1 := rep_var _

theorem rep_bits_nonrun (p : ℕ) (hp : ∀ a < len, p ≠ s + 2*a) :
    Rep (fun y => bitsY s len y p) 1 := by
  by_cases h1 : p + 1 = s
  · exact rep_mono (by norm_num) (rep_congr (fun y => (bits_pre y h1).symm) (rep_const true))
  by_cases h2 : p + 1 < s
  · exact rep_mono (by norm_num) (rep_congr (fun y => (bits_low y h2).symm) (rep_const false))
  by_cases h3 : p < s + 2*len
  · obtain ⟨a, rfl | rfl⟩ : ∃ a, p = s + 2*a ∨ p = s + 2*a + 1 := ⟨(p - s)/2, by omega⟩
    · exact absurd rfl (hp a (by omega))
    · exact rep_congr (fun y => (bits_guard y (by omega)).symm) (rep_t a)
  by_cases h4 : p = s + 2*len
  · subst h4
    exact rep_congr (fun y => by rw [bits_run y le_rfl, rY_len]) rep_z
  · exact rep_mono (by norm_num)
      (rep_congr (fun y => (bits_high y (by omega)).symm) (rep_const false))

theorem rep_chi (hlen : 1 ≤ len) (q : ℕ) : Rep (fun y => chiF (bitsY s len y) q) 1 := by
  unfold chiF
  by_cases hA : q + 3 < s
  · refine rep_mono (by norm_num) (rep_congr (fun y => ?_) (rep_const false))
    rw [bits_low y (by omega), bits_low y (by omega), bits_low y (by omega)]; rfl
  by_cases hB : q + 3 = s
  · refine rep_mono (by norm_num) (rep_congr (fun y => ?_) (rep_const true))
    rw [bits_low y (by omega), bits_low y (by omega), bits_pre y (by omega)]; rfl
  by_cases hC : q + 2 = s
  · refine rep_mono (by norm_num) (rep_congr (fun y => ?_) (rep_const false))
    rw [bits_low y (by omega), bits_pre y (by omega)]; rfl
  by_cases hD : q + 1 = s
  · refine rep_congr (fun y => ?_) (rep_un (fun b => !b) (rep_t (len := len) 0))
    rw [bits_pre y hD, bits_run_eq y (p := q+1) (a := 0) (by omega) (by omega),
      bits_guard_eq y (p := q+2) (a := 0) (by omega) (by omega)]
    cases hr : rY len y 0
    · simp
    · simp [rY_t y (by omega) hr]
  by_cases hE : q < s + 2*len
  · obtain ⟨a, rfl | rfl⟩ : ∃ a, q = s + 2*a ∨ q = s + 2*a + 1 := ⟨(q - s)/2, by omega⟩
    · refine rep_mono (by norm_num) (rep_congr (fun y => ?_) (rep_const false))
      rw [bits_run_eq y (p := s + 2*a) (a := a) rfl (by omega),
        bits_guard_eq y (p := s + 2*a + 1) (a := a) rfl (by omega),
        bits_run_eq y (p := s + 2*a + 2) (a := a+1) (by ring) (by omega),
        rY_step y (by omega : a < len)]
      cases tY len y a <;> cases rY len y (a+1) <;> rfl
    · by_cases hF : a + 1 < len
      · refine rep_congr (fun y => ?_) (rep_xor (rep_t (len := len) a) (rep_t (len := len) (a+1)))
        rw [bits_guard_eq y (p := s + 2*a + 1) (a := a) rfl (by omega),
          bits_run_eq y (p := s + 2*a + 1 + 1) (a := a+1) (by ring) (by omega),
          bits_guard_eq y (p := s + 2*a + 1 + 2) (a := a+1) (by ring) hF]
        cases hr : rY len y (a+1)
        · simp
        · simp [rY_t y hF hr]
      · refine rep_congr (fun y => ?_) (rep_t (len := len) a)
        rw [bits_guard_eq y (p := s + 2*a + 1) (a := a) rfl (by omega),
          bits_run_eq y (p := s + 2*a + 1 + 1) (a := a+1) (by ring) (by omega),
          bits_high y (p := s + 2*a + 1 + 2) (by omega)]
        simp
  by_cases hH : q = s + 2*len
  · subst hH
    refine rep_congr (fun y => ?_) rep_z
    rw [bits_run y le_rfl, rY_len, bits_high y (p := s + 2*len + 1) (by omega),
      bits_high y (p := s + 2*len + 2) (by omega)]
    simp
  · refine rep_mono (by norm_num) (rep_congr (fun y => ?_) (rep_const false))
    rw [bits_high y (by omega), bits_high y (by omega), bits_high y (by omega)]; rfl

theorem target_sum (hlen : 1 ≤ len) :
    ∑ y : Fin (len+1) → Bool, b2z (bitsY s len y s) = 1 := by
  have key : ∀ y : Fin (len+1) → Bool,
      bitsY s len y s = decide (y = fun i => decide (i = Fin.last len)) := by
    intro y
    rw [bits_run_eq y (p := s) (a := 0) (by ring) (by omega)]
    unfold rY zY tY
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hz, ht⟩
      funext i
      by_cases hi : i = Fin.last len
      · subst hi; simp [hz]
      · have hil : i.val < len := by
          have := Fin.val_lt_last hi; simpa using this
        have := ht i.val hil (Nat.zero_le _)
        simp only [hil, dite_true] at this
        simp only [hi, decide_false]
        exact this
    · rintro rfl
      refine ⟨by simp, fun b hb _ => ?_⟩
      simp only [hb, dite_true, decide_eq_false_iff_not]
      intro heq
      have := congrArg Fin.val heq
      simp at this; omega
  simp_rw [key]
  have : ∀ y : Fin (len+1) → Bool,
      b2z (decide (y = fun i => decide (i = Fin.last len))) =
        if y = (fun i => decide (i = Fin.last len)) then 1 else 0 := by
    intro y; by_cases hy : y = (fun i => decide (i = Fin.last len)) <;> simp [hy, b2z]
  simp_rw [this]
  simp

end family

/-! ## Encoding bit vectors -/

def enc : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | K+1, b => Nat.bit (b 0) (enc K (fun p => b (p+1)))

theorem enc_lt (K : ℕ) (b : ℕ → Bool) : enc K b < 2^K := by
  induction K generalizing b with
  | zero => simp [enc]
  | succ K ih => simp only [enc, Nat.bit_lt_two_pow_succ_iff]; exact ih _

theorem enc_testBit (K : ℕ) (b : ℕ → Bool) (p : ℕ) (hp : p < K) : (enc K b).testBit p = b p := by
  induction K generalizing b p with
  | zero => omega
  | succ K ih =>
    simp only [enc]
    cases p with
    | zero => exact Nat.testBit_bit_zero _ _
    | succ p =>
      rw [Nat.testBit_bit_succ]
      exact ih _ p (by omega)

theorem getD_le_foldr_max (l : List ℕ) (i : ℕ) : l.getD i 0 ≤ l.foldr max 0 := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i => simp only [List.getD_cons_succ, List.foldr_cons]; exact (ih i).trans (le_max_right _ _)

theorem lower_bound (h n d : ℕ) (mask : Fin n → Finset ℕ) (C : Circuit)
    (tap : Fin n → Fin (h+2) → ℕ)
    (hrb : ReadsBack (n*(2*h+2)) C) (har : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hdepth : (depthsOf (n*(2*h+2)) C.gates).foldr max 0 ≤ d)
    (hcorr : ∀ u : Fin n → Fin (2^(h+2)), ∀ j i,
      (wiresOf (dataOf h n mask u) C.gates).getD (tap j i) false = (u j).val.testBit i)
    (j0 : Fin n) (s len : ℕ) (hrun : ∀ a < len, s + 2*a < h ∧ s + 2*a ∉ mask j0) :
    len + 1 ≤ 2^d := by
  rcases Nat.eq_zero_or_pos len with h0 | hlen
  · subst h0; exact Nat.one_le_two_pow
  have hs : s < h := by have := (hrun 0 hlen).1; omega
  let uY : (Fin (len+1) → Bool) → Fin n → Fin (2^(h+2)) := fun y j =>
    if j = j0 then ⟨enc (h+2) (bitsY s len y), enc_lt _ _⟩ else ⟨0, by positivity⟩
  have hu0 : ∀ y p, p < h + 2 → (uY y j0).val.testBit p = bitsY s len y p := by
    intro y p hp
    simp only [uY, if_pos rfl]
    exact enc_testBit _ _ p hp
  have hu1 : ∀ y j p, j ≠ j0 → (uY y j).val.testBit p = false := by
    intro y j p hj
    simp only [uY, if_neg hj, Nat.zero_testBit]
  let X := fun y => dataOf h n mask (uY y)
  have hin : ∀ v, Rep (fun y => (X y).getD v false) 1 := by
    intro v
    by_cases hv : v < n * (2*h+2)
    · have hB : 0 < 2*h+2 := by omega
      obtain ⟨j, q, hq, rfl⟩ : ∃ (j : Fin n) (q : ℕ), q < 2*h+2 ∧ v = j.val * (2*h+2) + q := by
        refine ⟨⟨v / (2*h+2), ?_⟩, v % (2*h+2), Nat.mod_lt _ hB, ?_⟩
        · exact (Nat.div_lt_iff_lt_mul hB).mpr hv
        · simp only; rw [Nat.mul_comm]; exact (Nat.div_add_mod v (2*h+2)).symm
      have hX : ∀ y, (X y).getD (j.val * (2*h+2) + q) false =
          blockVal (fun l => (uY y j).val.testBit l) (mask j) h q :=
        fun y => dataOf_getD h n mask (uY y) j q hq
      by_cases hj : j = j0
      · subst hj
        refine rep_congr (fun y => (hX y).symm) ?_
        unfold blockVal
        by_cases h1 : q < h
        · simp only [if_pos h1]
          refine rep_congr (fun y => ?_) (rep_chi (s := s) hlen q)
          unfold chiF
          simp only [hu0 y q (by omega), hu0 y (q+1) (by omega), hu0 y (q+2) (by omega)]
        · simp only [if_neg h1]
          by_cases h2 : q < h + 2
          · simp only [if_pos h2]
            refine rep_congr (fun y => (hu0 y q h2).symm) (rep_bits_nonrun q ?_)
            intro a ha heq; have := (hrun a ha).1; omega
          · simp only [if_neg h2]
            by_cases h3 : q - (h+2) ∈ mask j
            · simp only [if_pos h3]
              refine rep_congr (fun y => (hu0 y _ (by omega)).symm) (rep_bits_nonrun _ ?_)
              intro a ha heq; rw [heq] at h3; exact (hrun a ha).2 h3
            · simp only [if_neg h3]
              exact rep_mono (by norm_num) (rep_const false)
      · refine rep_mono (by norm_num) (rep_congr (fun y => ?_) (rep_const false))
        rw [hX y]
        unfold blockVal chiF
        simp only [hu1 y j _ hj]
        split_ifs <;> rfl
    · refine rep_mono (by norm_num) (rep_congr (fun y => ?_) (rep_const false))
      rw [List.getD_eq_default]
      simp only [X, dataOf_length]; omega
  have hrb' : ∀ j (hj : j < C.gates.length), ∀ a ∈ (C.gates[j]).inputs,
      a < n*(2*h+2) + j := by
    intro j hj a ha
    have := hrb j hj a
    simp only [gateAt, List.getD_eq_getElem _ _ hj] at this
    exact this ha
  have hrep := wires_rep X C.gates (fun y => dataOf_length h n mask (uY y)) hin har hrb'
    (tap j0 ⟨s, by omega⟩)
  have hdep : 2 ^ ((depthsOf (n*(2*h+2)) C.gates).getD (tap j0 ⟨s, by omega⟩) 0) ≤ 2^d :=
    Nat.pow_le_pow_right (by norm_num) ((getD_le_foldr_max _ _).trans hdepth)
  obtain ⟨Q, hQ, hQe⟩ := rep_mono hdep hrep
  by_contra hlt
  push Not at hlt
  have hz := cube_sum_zero Q (by omega)
  have hsum : ∑ y : Fin (len+1) → Bool, MvPolynomial.eval (fun i => b2z (y i)) Q = 1 := by
    rw [← target_sum (s := s) hlen]
    apply Finset.sum_congr rfl
    intro y _
    rw [← hQe y]
    simp only [X]
    rw [hcorr (uY y) j0 ⟨s, by omega⟩]
    simp only
    rw [hu0 y s (by omega)]
  rw [hz] at hsum
  exact absurd hsum (by decide)

/-! ## The construction: pointer doubling along each parity -/

def maskN {n : ℕ} (mask : Fin n → Finset ℕ) (j : ℕ) : Finset ℕ :=
  if hj : j < n then mask ⟨j, hj⟩ else ∅

def gateL (h n : ℕ) (mask : Fin n → Finset ℕ) (ℓ σ : ℕ) : Gate :=
  if ℓ = 0 then
    ⟨GateOp.and, [if σ % (h+2) < h ∧ σ % (h+2) ∈ maskN mask (σ / (h+2))
      then σ / (h+2) * (2*h+2) + (h + 2 + σ % (h+2)) else σ / (h+2) * (2*h+2) + σ % (h+2)]⟩
  else if ℓ = 1 then
    (if σ % (h+2) < h ∧ σ % (h+2) ∉ maskN mask (σ / (h+2))
      then ⟨GateOp.not, [σ / (h+2) * (2*h+2) + (σ % (h+2) + 1)]⟩ else ⟨GateOp.or, []⟩)
  else
    if (ℓ - 2) % 4 = 0 then
      ⟨GateOp.and, [n*(2*h+2) + (4*((ℓ-2)/4)+1)*(n*(h+2)) + σ,
        n*(2*h+2) + (4*((ℓ-2)/4))*(n*(h+2)) +
          (if σ % (h+2) + 2^((ℓ-2)/4+1) < h+2 then σ + 2^((ℓ-2)/4+1) else σ)]⟩
    else if (ℓ - 2) % 4 = 1 then
      ⟨GateOp.mod 2, [n*(2*h+2) + (4*((ℓ-2)/4))*(n*(h+2)) + σ,
        n*(2*h+2) + (4*((ℓ-2)/4)+2)*(n*(h+2)) + σ]⟩
    else if (ℓ - 2) % 4 = 2 then
      ⟨GateOp.not, [n*(2*h+2) + (4*((ℓ-2)/4)+3)*(n*(h+2)) + σ]⟩
    else
      ⟨GateOp.and, [n*(2*h+2) + (4*((ℓ-2)/4)+1)*(n*(h+2)) + σ,
        n*(2*h+2) + (4*((ℓ-2)/4)+1)*(n*(h+2)) +
          (if σ % (h+2) + 2^((ℓ-2)/4+1) < h+2 then σ + 2^((ℓ-2)/4+1) else σ)]⟩

def gatesU (h n d : ℕ) (mask : Fin n → Finset ℕ) : List Gate :=
  List.ofFn (fun m : Fin ((4*d+2)*(n*(h+2))) =>
    gateL h n mask (m.val / (n*(h+2))) (m.val % (n*(h+2))))

theorem gatesU_length (h n d : ℕ) (mask : Fin n → Finset ℕ) :
    (gatesU h n d mask).length = (4*d+2)*(n*(h+2)) := by
  simp [gatesU]

theorem layer_lt {a b N σ τ : ℕ} (hab : a < b) (hσ : σ < N) : a*N + σ < b*N + τ := by
  have : (a+1)*N ≤ b*N := Nat.mul_le_mul_right _ hab
  rw [Nat.succ_mul] at this; omega

theorem gatesU_getElem (h n d : ℕ) (mask : Fin n → Finset ℕ) {ℓ σ : ℕ} (hℓ : ℓ < 4*d+2)
    (hσ : σ < n*(h+2)) (hlt : ℓ * (n*(h+2)) + σ < (gatesU h n d mask).length) :
    (gatesU h n d mask)[ℓ * (n*(h+2)) + σ] = gateL h n mask ℓ σ := by
  have hN : 0 < n*(h+2) := by omega
  have e1 : (ℓ * (n*(h+2)) + σ) / (n*(h+2)) = ℓ := by
    rw [Nat.add_comm (ℓ * (n*(h+2))) σ, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hσ,
      zero_add]
  have e2 : (ℓ * (n*(h+2)) + σ) % (n*(h+2)) = σ := by
    rw [Nat.add_comm (ℓ * (n*(h+2))) σ, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hσ]
  simp only [gatesU, List.getElem_ofFn, e1, e2]

theorem slot_lt {n h j i : ℕ} (hj : j < n) (hi : i < h + 2) : j * (h+2) + i < n * (h+2) := by
  have : (j+1)*(h+2) ≤ n*(h+2) := Nat.mul_le_mul_right _ hj
  rw [Nat.succ_mul] at this; omega

theorem data_lt {n h j q : ℕ} (hj : j < n) (hq : q < 2*h+2) : j * (2*h+2) + q < n * (2*h+2) := by
  have : (j+1)*(2*h+2) ≤ n*(2*h+2) := Nat.mul_le_mul_right _ hj
  rw [Nat.succ_mul] at this; omega

theorem shift_lt {h n σ k : ℕ} (hσ : σ < n*(h+2)) :
    (if σ % (h+2) + 2^(k+1) < h+2 then σ + 2^(k+1) else σ) < n*(h+2) := by
  split_ifs with hc
  · have hj : σ / (h+2) < n := (Nat.div_lt_iff_lt_mul (by omega)).mpr hσ
    have := slot_lt (h := h) hj hc
    have e := Nat.div_add_mod σ (h+2)
    rw [Nat.mul_comm] at e
    omega
  · exact hσ

theorem gateL_inputs_lt (h n d : ℕ) (mask : Fin n → Finset ℕ) {ℓ σ : ℕ} (hℓ : ℓ < 4*d+2)
    (hσ : σ < n*(h+2)) :
    ∀ a ∈ (gateL h n mask ℓ σ).inputs, a < n*(2*h+2) + (ℓ * (n*(h+2)) + σ) := by
  intro a ha
  have hj : σ / (h+2) < n := (Nat.div_lt_iff_lt_mul (by omega)).mpr hσ
  have hi : σ % (h+2) < h+2 := Nat.mod_lt _ (by omega)
  unfold gateL at ha
  by_cases h0 : ℓ = 0
  · rw [if_pos h0] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    split_ifs with hc
    · have := data_lt (h := h) hj (q := h + 2 + σ % (h+2)) (by omega); omega
    · have := data_lt (h := h) hj (q := σ % (h+2)) (by omega); omega
  rw [if_neg h0] at ha
  by_cases h1 : ℓ = 1
  · rw [if_pos h1] at ha
    split_ifs at ha with hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha
      have := data_lt (h := h) hj (q := σ % (h+2) + 1) (by omega); omega
    · simp at ha
  rw [if_neg h1] at ha
  have hsh := shift_lt (h := h) (k := (ℓ-2)/4) hσ
  generalize (if σ % (h+2) + 2^((ℓ-2)/4+1) < h+2 then σ + 2^((ℓ-2)/4+1) else σ) = σ' at ha hsh
  have L1 := layer_lt (N := n*(h+2)) (τ := σ) (show 4*((ℓ-2)/4)+1 < ℓ by omega) hσ
  have L0 := layer_lt (N := n*(h+2)) (τ := σ) (show 4*((ℓ-2)/4) < ℓ by omega) hsh
  have L1' := layer_lt (N := n*(h+2)) (τ := σ) (show 4*((ℓ-2)/4)+1 < ℓ by omega) hsh
  by_cases c0 : (ℓ - 2) % 4 = 0
  · rw [if_pos c0] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> omega
  rw [if_neg c0] at ha
  by_cases c1 : (ℓ - 2) % 4 = 1
  · rw [if_pos c1] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    have L0' := layer_lt (N := n*(h+2)) (τ := σ) (show 4*((ℓ-2)/4) < ℓ by omega) hσ
    have L2 := layer_lt (N := n*(h+2)) (τ := σ) (show 4*((ℓ-2)/4)+2 < ℓ by omega) hσ
    rcases ha with rfl | rfl <;> omega
  rw [if_neg c1] at ha
  by_cases c2 : (ℓ - 2) % 4 = 2
  · rw [if_pos c2] at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    have L3 := layer_lt (N := n*(h+2)) (τ := σ) (show 4*((ℓ-2)/4)+3 < ℓ by omega) hσ
    subst ha; omega
  rw [if_neg c2] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl <;> omega

theorem decomp {N m : ℕ} (hN : 0 < N) : m = (m / N) * N + m % N := by
  have := Nat.div_add_mod m N; rw [Nat.mul_comm] at this; omega

theorem gatesU_rb (h n d : ℕ) (mask : Fin n → Finset ℕ) :
    ∀ m (hm : m < (gatesU h n d mask).length), ∀ a ∈ ((gatesU h n d mask)[m]).inputs,
      a < n*(2*h+2) + m := by
  intro m hm a ha
  rw [gatesU_length] at hm
  have hN : 0 < n*(h+2) := by
    rcases Nat.eq_zero_or_pos (n*(h+2)) with h0 | h0
    · rw [h0, Nat.mul_zero] at hm; omega
    · exact h0
  have hℓ : m / (n*(h+2)) < 4*d+2 := (Nat.div_lt_iff_lt_mul hN).mpr hm
  have hσ : m % (n*(h+2)) < n*(h+2) := Nat.mod_lt _ hN
  have e := decomp (m := m) hN
  have hlt : m / (n*(h+2)) * (n*(h+2)) + m % (n*(h+2)) < (gatesU h n d mask).length := by
    rw [← e, gatesU_length]; exact hm
  have hg : (gatesU h n d mask)[m] = gateL h n mask (m / (n*(h+2))) (m % (n*(h+2))) := by
    rw [← gatesU_getElem h n d mask hℓ hσ hlt]
    congr 1
  rw [hg] at ha
  have := gateL_inputs_lt h n d mask hℓ hσ a ha
  rw [← e] at this
  exact this

theorem gateL_arity (h n : ℕ) (mask : Fin n → Finset ℕ) (ℓ σ : ℕ) :
    (gateL h n mask ℓ σ).inputs.length ≤ 2 := by
  unfold gateL
  split_ifs <;> simp

/-! ### depth -/

def dl (ℓ : ℕ) : ℕ := if ℓ ≤ 1 then 0 else (ℓ - 2)/4 + 1

theorem foldr_max_le (l : List ℕ) (d : ℕ) (H : ∀ i < l.length, l.getD i 0 ≤ d) :
    l.foldr max 0 ≤ d := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    refine max_le (by simpa using H 0 (by simp)) (ih (fun i hi => ?_))
    simpa using H (i+1) (by simp; omega)

theorem gatesU_depth (h n d : ℕ) (mask : Fin n → Finset ℕ) :
    ∀ ℓ, ℓ < 4*d+2 → ∀ σ, σ < n*(h+2) →
      (depthsOf (n*(2*h+2)) (gatesU h n d mask)).getD (n*(2*h+2) + (ℓ * (n*(h+2)) + σ)) 0
        ≤ dl ℓ := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
  intro hℓ σ hσ
  have hN : 0 < n*(h+2) := by omega
  have hlt : ℓ * (n*(h+2)) + σ < (gatesU h n d mask).length := by
    rw [gatesU_length]
    have := layer_lt (N := n*(h+2)) (τ := 0) hℓ hσ; omega
  rw [depthsOf_getD_gate _ _ hlt (gatesU_rb h n d mask _ hlt)]
  rw [gatesU_getElem h n d mask hℓ hσ hlt]
  -- depth of a wire read by the gate
  have hD : ∀ a, a < n*(2*h+2) →
      (depthsOf (n*(2*h+2)) (gatesU h n d mask)).getD a 0 = 0 :=
    fun a ha => depthsOf_getD_input _ _ ha
  have hL : ∀ ℓ' σ', ℓ' < ℓ → σ' < n*(h+2) →
      (depthsOf (n*(2*h+2)) (gatesU h n d mask)).getD
        (n*(2*h+2) + ℓ' * (n*(h+2)) + σ') 0 ≤ dl ℓ' := by
    intro ℓ' σ' hl hs
    have := ih ℓ' hl (by omega) σ' hs
    rwa [Nat.add_assoc]
  have hj : σ / (h+2) < n := (Nat.div_lt_iff_lt_mul (by omega)).mpr hσ
  have hi : σ % (h+2) < h+2 := Nat.mod_lt _ (by omega)
  unfold gateL
  by_cases h0 : ℓ = 0
  · subst h0
    rw [if_pos rfl]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    rw [hD _ (by split_ifs <;> exact data_lt hj (by omega))]
    have : ∀ a, nlGate ⟨GateOp.and, [a]⟩ = false := fun _ => rfl
    rw [this]
    simp [dl]
  rw [if_neg h0]
  by_cases h1 : ℓ = 1
  · subst h1
    rw [if_pos rfl]
    by_cases hc : σ % (h + 2) < h ∧ σ % (h + 2) ∉ maskN mask (σ / (h + 2))
    · rw [if_pos hc]
      simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
      rw [hD _ (data_lt hj (by omega))]
      have : ∀ a, nlGate ⟨GateOp.not, [a]⟩ = false := fun _ => rfl
      rw [this]
      simp [dl]
    · rw [if_neg hc]
      have : nlGate ⟨GateOp.or, []⟩ = false := rfl
      rw [this]
      simp [dl]
  rw [if_neg h1]
  have hsh := shift_lt (h := h) (k := (ℓ-2)/4) hσ
  have hdl : dl ℓ = (ℓ-2)/4 + 1 := by simp only [dl]; rw [if_neg (by omega)]
  have hk0 : dl (4*((ℓ-2)/4)) ≤ (ℓ-2)/4 := by simp only [dl]; split_ifs <;> omega
  have hk1 : dl (4*((ℓ-2)/4)+1) ≤ (ℓ-2)/4 := by simp only [dl]; split_ifs <;> omega
  have hk2 : dl (4*((ℓ-2)/4)+2) ≤ (ℓ-2)/4 + 1 := by simp only [dl]; split_ifs <;> omega
  have hk3 : dl (4*((ℓ-2)/4)+3) ≤ (ℓ-2)/4 + 1 := by simp only [dl]; split_ifs <;> omega
  rw [hdl]
  generalize (if σ % (h+2) + 2^((ℓ-2)/4+1) < h+2 then σ + 2^((ℓ-2)/4+1) else σ) = σ' at hsh ⊢
  have hand : ∀ a b, nlGate ⟨GateOp.and, [a, b]⟩ = true := fun _ _ => rfl
  have hmod : ∀ a b, nlGate ⟨GateOp.mod 2, [a, b]⟩ = false := fun _ _ => rfl
  have hnot : ∀ a, nlGate ⟨GateOp.not, [a]⟩ = false := fun _ => rfl
  by_cases c0 : (ℓ - 2) % 4 = 0
  · rw [if_pos c0]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    have e1 := hL _ σ (show 4*((ℓ-2)/4)+1 < ℓ by omega) hσ
    have e2 := hL _ _ (show 4*((ℓ-2)/4) < ℓ by omega) hsh
    rw [hand]
    simp only [Bool.toNat_true]
    omega
  rw [if_neg c0]
  by_cases c1 : (ℓ - 2) % 4 = 1
  · rw [if_pos c1]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    have e1 := hL _ σ (show 4*((ℓ-2)/4) < ℓ by omega) hσ
    have e2 := hL _ σ (show 4*((ℓ-2)/4)+2 < ℓ by omega) hσ
    rw [hmod]
    simp only [Bool.toNat_false, add_zero]
    omega
  rw [if_neg c1]
  by_cases c2 : (ℓ - 2) % 4 = 2
  · rw [if_pos c2]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
    have e1 := hL _ σ (show 4*((ℓ-2)/4)+3 < ℓ by omega) hσ
    rw [hnot]
    simp only [Bool.toNat_false, add_zero]
    omega
  rw [if_neg c2]
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
  have e1 := hL _ σ (show 4*((ℓ-2)/4)+1 < ℓ by omega) hσ
  have e2 := hL _ _ (show 4*((ℓ-2)/4)+1 < ℓ by omega) hsh
  rw [hand]
  simp only [Bool.toNat_true]
  omega

/-! ### semantics of the layers -/

section sem

variable (h n d : ℕ) (mask : Fin n → Finset ℕ)

def V (x : List Bool) (ℓ σ : ℕ) : Bool :=
  (wiresOf x (gatesU h n d mask)).getD (n*(2*h+2) + ℓ*(n*(h+2)) + σ) false

theorem V_gate (x : List Bool) (hx : x.length = n*(2*h+2)) {ℓ σ : ℕ} (hℓ : ℓ < 4*d+2)
    (hσ : σ < n*(h+2)) :
    V h n d mask x ℓ σ = (gateL h n mask ℓ σ).op.eval ((gateL h n mask ℓ σ).inputs.map
      (fun a => (wiresOf x (gatesU h n d mask)).getD a false)) := by
  have hlt : ℓ * (n*(h+2)) + σ < (gatesU h n d mask).length := by
    rw [gatesU_length]
    have := layer_lt (N := n*(h+2)) (τ := 0) hℓ hσ; omega
  unfold V
  have := wiresOf_getD_gate x (gatesU h n d mask) hlt
    (by rw [hx]; exact gatesU_rb h n d mask _ hlt)
  rw [hx, gatesU_getElem h n d mask hℓ hσ hlt] at this
  rw [Nat.add_assoc, this]

theorem shiftS_lt {σ k : ℕ} (hσ : σ < n*(h+2)) :
    (if σ % (h+2) + 2^(k+1) < h+2 then σ + 2^(k+1) else σ) < n*(h+2) := shift_lt hσ

theorem V_P (x : List Bool) (hx : x.length = n*(2*h+2)) {k σ : ℕ} (hk : 4*k+2 < 4*d+2)
    (hσ : σ < n*(h+2)) :
    V h n d mask x (4*k+2) σ = (V h n d mask x (4*k+1) σ &&
      V h n d mask x (4*k) (if σ % (h+2) + 2^(k+1) < h+2 then σ + 2^(k+1) else σ)) := by
  rw [V_gate h n d mask x hx hk hσ]
  unfold gateL
  have e1 : (4*k+2-2)/4 = k := by omega
  have e2 : (4*k+2-2)%4 = 0 := by omega
  rw [if_neg (by omega), if_neg (by omega), e1, if_pos e2]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id,
    Bool.and_true]
  rfl

theorem V_Q (x : List Bool) (hx : x.length = n*(2*h+2)) {k σ : ℕ} (hk : 4*k+3 < 4*d+2)
    (hσ : σ < n*(h+2)) :
    V h n d mask x (4*k+3) σ = !(xor (V h n d mask x (4*k) σ) (V h n d mask x (4*k+2) σ)) := by
  rw [V_gate h n d mask x hx hk hσ]
  unfold gateL
  have e1 : (4*k+3-2)/4 = k := by omega
  have e2 : (4*k+3-2)%4 = 1 := by omega
  rw [if_neg (by omega), if_neg (by omega), e1, if_neg (by omega), if_pos e2]
  simp only [List.map_cons, List.map_nil, GateOp.eval]
  unfold V
  generalize (wiresOf x (gatesU h n d mask)).getD (n * (2 * h + 2) + 4 * k * (n * (h + 2)) + σ)
    false = a
  generalize (wiresOf x (gatesU h n d mask)).getD
    (n * (2 * h + 2) + (4 * k + 2) * (n * (h + 2)) + σ) false = b
  cases a <;> cases b <;> decide

theorem V_A (x : List Bool) (hx : x.length = n*(2*h+2)) {k σ : ℕ} (hk : 4*k+4 < 4*d+2)
    (hσ : σ < n*(h+2)) :
    V h n d mask x (4*k+4) σ = !(V h n d mask x (4*k+3) σ) := by
  rw [V_gate h n d mask x hx hk hσ]
  unfold gateL
  have e1 : (4*k+4-2)/4 = k := by omega
  have e2 : (4*k+4-2)%4 = 2 := by omega
  rw [if_neg (by omega), if_neg (by omega), e1, if_neg (by omega), if_neg (by omega), if_pos e2]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
  rfl

theorem V_B (x : List Bool) (hx : x.length = n*(2*h+2)) {k σ : ℕ} (hk : 4*k+5 < 4*d+2)
    (hσ : σ < n*(h+2)) :
    V h n d mask x (4*k+5) σ = (V h n d mask x (4*k+1) σ &&
      V h n d mask x (4*k+1) (if σ % (h+2) + 2^(k+1) < h+2 then σ + 2^(k+1) else σ)) := by
  rw [V_gate h n d mask x hx hk hσ]
  unfold gateL
  have e1 : (4*k+5-2)/4 = k := by omega
  have e2 : (4*k+5-2)%4 = 3 := by omega
  rw [if_neg (by omega), if_neg (by omega), e1, if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id,
    Bool.and_true]
  rfl

theorem slot_div {h j i : ℕ} (hi : i < h + 2) : (j * (h+2) + i) / (h+2) = j := by
  rw [Nat.add_comm (j * (h+2)) i, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hi,
    zero_add]

theorem slot_mod {h j i : ℕ} (hi : i < h + 2) : (j * (h+2) + i) % (h+2) = i := by
  rw [Nat.add_comm (j * (h+2)) i, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

theorem maskN_val (j : Fin n) : maskN mask j.val = mask j := by
  simp [maskN, j.isLt]

theorem V_0 (u : Fin n → Fin (2^(h+2))) (j : Fin n) {i : ℕ} (hi : i < h + 2) (hd : 0 < d + 1) :
    V h n d mask (dataOf h n mask u) 0 (j.val * (h+2) + i) =
      (if i < h ∧ i ∈ mask j then (u j).val.testBit i
        else blockVal (fun l => (u j).val.testBit l) (mask j) h i) := by
  have hσ := slot_lt (h := h) j.isLt hi
  rw [V_gate h n d mask _ (dataOf_length h n mask u) (by omega) hσ]
  unfold gateL
  rw [if_pos rfl, slot_div hi, slot_mod hi, maskN_val]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id,
    Bool.and_true]
  split_ifs with hc
  · rw [wiresOf_getD_input _ _ (by rw [dataOf_length]; exact data_lt j.isLt (by omega))]
    rw [dataOf_getD h n mask u j _ (by omega)]
    unfold blockVal
    rw [if_neg (by omega), if_neg (by omega), if_pos (by simpa using hc.2)]
    congr 1; omega
  · rw [wiresOf_getD_input _ _ (by rw [dataOf_length]; exact data_lt j.isLt (by omega))]
    rw [dataOf_getD h n mask u j _ (by omega)]

theorem V_1 (u : Fin n → Fin (2^(h+2))) (j : Fin n) {i : ℕ} (hi : i < h + 2) (hd : 1 < 4*d+2) :
    V h n d mask (dataOf h n mask u) 1 (j.val * (h+2) + i) =
      (if i < h ∧ i ∉ mask j then
        !(blockVal (fun l => (u j).val.testBit l) (mask j) h (i+1)) else false) := by
  have hσ := slot_lt (h := h) j.isLt hi
  rw [V_gate h n d mask _ (dataOf_length h n mask u) hd hσ]
  unfold gateL
  rw [if_neg (by omega), if_pos rfl, slot_div hi, slot_mod hi, maskN_val]
  split_ifs with hc
  · simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
    rw [wiresOf_getD_input _ _ (by rw [dataOf_length]; exact data_lt j.isLt (by omega))]
    rw [dataOf_getD h n mask u j _ (by omega)]
  · simp [GateOp.eval]

theorem invariant (u : Fin n → Fin (2^(h+2))) :
    ∀ k, k ≤ d → ∀ (j : Fin n) (i : ℕ), i < h + 2 →
      (V h n d mask (dataOf h n mask u) (4*k+1) (j.val*(h+2)+i) = true →
        ∀ m < 2^k, i + 2*m < h ∧ i + 2*m ∉ mask j) ∧
      (u j).val.testBit i = xor (V h n d mask (dataOf h n mask u) (4*k) (j.val*(h+2)+i))
        (V h n d mask (dataOf h n mask u) (4*k+1) (j.val*(h+2)+i) &&
          (u j).val.testBit (i + 2^(k+1))) := by
  intro k
  induction k with
  | zero =>
    intro _ j i hi
    simp only [Nat.mul_zero, Nat.zero_add, pow_zero, zero_add, pow_one]
    rw [V_1 h n d mask u j hi (by omega), V_0 h n d mask u j hi (by omega)]
    constructor
    · intro hb m hm
      have hm0 : m = 0 := by omega
      subst hm0
      by_cases hc : i < h ∧ i ∉ mask j
      · simpa using hc
      · rw [if_neg hc] at hb; exact absurd hb (by simp)
    · unfold blockVal
      by_cases hc : i < h ∧ i ∈ mask j
      · rw [if_pos hc, if_neg (fun h' => h'.2 hc.2)]; simp
      · rw [if_neg hc]
        by_cases hih : i < h
        · have hnm : i ∉ mask j := fun hm => hc ⟨hih, hm⟩
          rw [if_pos hih, if_pos ⟨hih, hnm⟩]
          unfold chiF
          beta_reduce
          by_cases hi1 : i + 1 < h
          · rw [if_pos hi1]
            have e : i + 1 + 1 = i + 2 := rfl
            have e' : i + 1 + 2 = i + 3 := rfl
            simp only [e, e']
            generalize (u j).val.testBit i = b0
            generalize (u j).val.testBit (i+1) = b1
            generalize (u j).val.testBit (i+2) = b2
            generalize (u j).val.testBit (i+3) = b3
            cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> rfl
          · rw [if_neg hi1, if_pos (by omega)]
            generalize (u j).val.testBit i = b0
            generalize (u j).val.testBit (i+1) = b1
            generalize (u j).val.testBit (i+2) = b2
            cases b0 <;> cases b1 <;> cases b2 <;> rfl
        · rw [if_neg hih, if_pos hi, if_neg (fun h' => hih h'.1)]
          simp
  | succ k ih =>
    intro hk j i hi
    have hσ := slot_lt (h := h) j.isLt hi
    have ih' := ih (by omega)
    have hx := dataOf_length h n mask u
    have e4 : 4*(k+1) = 4*k+4 := by ring
    have e5 : 4*(k+1)+1 = 4*k+5 := by ring
    rw [e5, e4, V_A h n d mask _ hx (by omega) hσ, V_Q h n d mask _ hx (by omega) hσ,
      V_P h n d mask _ hx (by omega) hσ, V_B h n d mask _ hx (by omega) hσ]
    rw [slot_mod hi]
    obtain ⟨hI1, hI2⟩ := ih' j i hi
    by_cases hc : i + 2^(k+1) < h + 2
    · rw [if_pos hc]
      have e : j.val * (h+2) + i + 2^(k+1) = j.val * (h+2) + (i + 2^(k+1)) := by ring
      rw [e]
      obtain ⟨hJ1, hJ2⟩ := ih' j (i + 2^(k+1)) hc
      constructor
      · intro hb m hm
        rw [Bool.and_eq_true] at hb
        by_cases hmk : m < 2^k
        · exact hI1 hb.1 m hmk
        · have h2 : 2^(k+1) = 2 * 2^k := by ring
          have := hJ1 hb.2 (m - 2^k) (by rw [h2] at hm; omega)
          have e2 : i + 2^(k+1) + 2*(m - 2^k) = i + 2*m := by rw [h2]; omega
          rwa [e2] at this
      · rw [hI2, hJ2]
        have e3 : i + 2^(k+1) + 2^(k+1) = i + 2^(k+1+1) := by ring
        rw [e3]
        generalize V h n d mask (dataOf h n mask u) (4*k) (j.val*(h+2)+i) = a1
        generalize V h n d mask (dataOf h n mask u) (4*k+1) (j.val*(h+2)+i) = b1
        generalize V h n d mask (dataOf h n mask u) (4*k) (j.val*(h+2)+(i + 2^(k+1))) = a2
        generalize V h n d mask (dataOf h n mask u) (4*k+1) (j.val*(h+2)+(i + 2^(k+1))) = b2
        cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> simp
    · rw [if_neg hc]
      have hb : V h n d mask (dataOf h n mask u) (4*k+1) (j.val*(h+2)+i) = false := by
        by_contra hne
        rw [Bool.not_eq_false] at hne
        have := (hI1 hne (2^k - 1) (by have := Nat.one_le_two_pow (n := k); omega)).1
        have h2 : 2^(k+1) = 2 * 2^k := by ring
        have := Nat.one_le_two_pow (n := k)
        omega
      rw [hb]
      constructor
      · intro hf; simp at hf
      · rw [hI2, hb]; simp

end sem

theorem upper_bound (h n d : ℕ) (mask : Fin n → Finset ℕ)
    (hrhs : ∀ (j : Fin n) (s len : ℕ), (∀ a < len, s+2*a < h ∧ s+2*a ∉ mask j) → len+1 ≤ 2^d) :
    ∃ (C : Circuit) (tap : Fin n → Fin (h+2) → ℕ),
      ReadsBack (n*(2*h+2)) C ∧ (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      (depthsOf (n*(2*h+2)) C.gates).foldr max 0 ≤ d ∧
      (∀ j i, tap j i < n*(2*h+2) + C.gates.length) ∧
      ∀ (u : Fin n → Fin (2^(h+2))) j i,
        (wiresOf (dataOf h n mask u) C.gates).getD (tap j i) false = (u j).val.testBit i := by
  refine ⟨⟨gatesU h n d mask, 0⟩, fun j i => n*(2*h+2) + (4*d)*(n*(h+2)) + (j.val*(h+2)+i.val),
    ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm a ha
    change m < (gatesU h n d mask).length at hm
    change a ∈ ((gatesU h n d mask).getD m ⟨GateOp.or, []⟩).inputs at ha
    rw [List.getD_eq_getElem _ _ hm] at ha
    exact gatesU_rb h n d mask m hm a ha
  · intro g hg
    change g ∈ gatesU h n d mask at hg
    unfold gatesU at hg
    rw [List.mem_ofFn] at hg
    obtain ⟨m, rfl⟩ := hg
    exact gateL_arity _ _ _ _ _
  · show (depthsOf (n*(2*h+2)) (gatesU h n d mask)).foldr max 0 ≤ d
    apply foldr_max_le
    intro idx hidx
    rw [depthsOf_length, gatesU_length] at hidx
    by_cases hw : idx < n*(2*h+2)
    · rw [depthsOf_getD_input _ _ hw]; omega
    · have hN : 0 < n*(h+2) := by
        rcases Nat.eq_zero_or_pos (n*(h+2)) with h0 | h0
        · rw [h0, Nat.mul_zero] at hidx; omega
        · exact h0
      obtain ⟨m, rfl⟩ : ∃ m, idx = n*(2*h+2) + m := ⟨idx - n*(2*h+2), by omega⟩
      have hm : m < (4*d+2)*(n*(h+2)) := by omega
      have hℓ : m / (n*(h+2)) < 4*d+2 := (Nat.div_lt_iff_lt_mul hN).mpr hm
      have hσ : m % (n*(h+2)) < n*(h+2) := Nat.mod_lt _ hN
      have e := decomp (m := m) hN
      have := gatesU_depth h n d mask _ hℓ _ hσ
      rw [← e] at this
      refine this.trans ?_
      simp only [dl]; split_ifs <;> omega
  · show ∀ j i, _ < n*(2*h+2) + (gatesU h n d mask).length
    intro j i
    simp only [gatesU_length]
    have := slot_lt (h := h) j.isLt i.isLt
    have := layer_lt (N := n*(h+2)) (τ := 0) (show 4*d < 4*d+2 by omega) this
    omega
  · show ∀ (u : Fin n → Fin (2^(h+2))) j i,
      (wiresOf (dataOf h n mask u) (gatesU h n d mask)).getD _ false = _
    intro u j i
    obtain ⟨hI1, hI2⟩ := invariant h n d mask u d le_rfl j i.val i.isLt
    have hb : V h n d mask (dataOf h n mask u) (4*d+1) (j.val*(h+2)+i.val) = false := by
      by_contra hne
      rw [Bool.not_eq_false] at hne
      have := hrhs j i.val (2^d) (hI1 hne)
      omega
    rw [hI2, hb]
    simp only [Bool.false_and, Bool.xor_false]
    rfl

end PEqualNP.Outside.L_meta_40552_aux

theorem PEqualNP.Outside.L_meta_40552 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
        (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
let valid := fun (w : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.NestedCover.ReadsBack w C ∧
  ∀ g ∈ C.gates, g.inputs.length ≤ 2
let chi := fun (u : Nat → Bool) (i : Nat) => xor (u i) (!(u (i+1)) && u (i+2))
let depth := fun (w : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  (C.gates.foldl (fun (ds : List Nat) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate w 0)).foldr max 0
∀ (h n d : Nat) (mask : Fin n → Finset Nat),
  let U := Fin n → Fin (2^(h+2))
  let w := n*(2*h+2)
  (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin n → Fin (h+2) → Nat),
    valid w C ∧ depth w C ≤ d ∧ (∀ j i, tap j i < w+C.gates.length) ∧
    ∀ (u : U),
      let data := (List.ofFn (fun j : Fin n =>
        let bits := fun l : Nat => (u j).val.testBit l
        List.ofFn (fun i : Fin h => chi bits i) ++ [bits h, bits (h+1)] ++
        List.ofFn (fun i : Fin h => if i.val ∈ mask j then bits i else false))).flatten
      ∀ j i, (C.wires data).getD (tap j i) false = (u j).val.testBit i) ↔
    ∀ (j : Fin n) (s len : Nat),
      (∀ a < len, s+2*a < h ∧ s+2*a ∉ mask j) → len+1 ≤ 2^d) := by
  intro nonlinear valid chi depth h n d mask U w
  constructor
  · rintro ⟨C, tap, ⟨hrb, har⟩, hdep, _htap, hcorr⟩ j s len hrun
    exact PEqualNP.Outside.L_meta_40552_aux.lower_bound h n d mask C tap hrb har hdep
      (fun u j i => hcorr u j i) j s len hrun
  · intro hrhs
    obtain ⟨C, tap, hrb, har, hdep, htap, hcorr⟩ :=
      PEqualNP.Outside.L_meta_40552_aux.upper_bound h n d mask hrhs
    exact ⟨C, tap, ⟨hrb, har⟩, hdep, htap, fun u j i => hcorr u j i⟩
