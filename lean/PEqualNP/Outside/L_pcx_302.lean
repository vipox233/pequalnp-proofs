import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_302_aux

theorem z2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

-- gate evaluation, generic in the wire value type (Bool for run, ℕ for depths)
def gop (b l r : Bool) : Bool := if b then l && r else l || r

def dop (_b : Bool) (l r : ℕ) : ℕ := max l r + 1

def wstep {α : Type} (F : Bool → α → α → α) (d : α) (w : List α) (g : Bool × ℕ × ℕ) :
    List α :=
  w ++ [F g.1 (w.getD g.2.1 d) (w.getD g.2.2 d)]

def wl {α : Type} (F : Bool → α → α → α) (d : α) (D : List (Bool × ℕ × ℕ)) (w : List α) :
    List α :=
  D.foldl (wstep F d) w

-- the statement's run and depths are these folds
theorem run_eq (G : List (Bool × ℕ × ℕ)) (w : List Bool) :
    G.foldl (fun (w : List Bool) g =>
      let l := w.getD g.2.1 false
      let r := w.getD g.2.2 false
      w ++ [if g.1 then l && r else l || r]) w = wl gop false G w := rfl

theorem depths_eq (G : List (Bool × ℕ × ℕ)) (w : List ℕ) :
    G.foldl (fun (w : List ℕ) g =>
      w ++ [max (w.getD g.2.1 0) (w.getD g.2.2 0) + 1]) w = wl dop 0 G w := rfl

section Eval

variable {α : Type} (F : Bool → α → α → α) (d : α)

theorem wl_cons (g : Bool × ℕ × ℕ) (D : List (Bool × ℕ × ℕ)) (w : List α) :
    wl F d (g :: D) w = wl F d D (wstep F d w g) := rfl

theorem wl_append (D E : List (Bool × ℕ × ℕ)) (w : List α) :
    wl F d (D ++ E) w = wl F d E (wl F d D w) := by
  simp [wl, List.foldl_append]

theorem wstep_length (w : List α) (g : Bool × ℕ × ℕ) :
    (wstep F d w g).length = w.length + 1 := by
  simp [wstep]

theorem wl_length (D : List (Bool × ℕ × ℕ)) :
    ∀ w : List α, (wl F d D w).length = w.length + D.length := by
  induction D with
  | nil => intro w; simp [wl]
  | cons g D ih => intro w; rw [wl_cons, ih, wstep_length]; simp; omega

theorem wstep_getD_lt (w : List α) (g : Bool × ℕ × ℕ) (i : ℕ) (h : i < w.length) :
    (wstep F d w g).getD i d = w.getD i d := by
  simp [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem wl_getD_lt (D : List (Bool × ℕ × ℕ)) : ∀ (w : List α) (i : ℕ), i < w.length →
    (wl F d D w).getD i d = w.getD i d := by
  induction D with
  | nil => intro w i _; rfl
  | cons g D ih =>
    intro w i h
    rw [wl_cons, ih _ _ (by rw [wstep_length]; omega), wstep_getD_lt F d _ _ _ h]

theorem wstep_getD_last (w : List α) (g : Bool × ℕ × ℕ) :
    (wstep F d w g).getD w.length d = F g.1 (w.getD g.2.1 d) (w.getD g.2.2 d) := by
  simp [wstep, List.getD_eq_getElem?_getD]

theorem wl_take_getD (D : List (Bool × ℕ × ℕ)) (w : List α) (j i : ℕ)
    (hi : i < w.length + j) (hj : j ≤ D.length) :
    (wl F d (D.take j) w).getD i d = (wl F d D w).getD i d := by
  have hsplit : D = D.take j ++ D.drop j := by simp
  have hlen : (wl F d (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  conv_rhs => rw [hsplit, wl_append]
  rw [wl_getD_lt F d (D.drop j) (wl F d (D.take j) w) i (by rw [hlen]; exact hi)]

-- a gate that reads only earlier wires: its wire is the operation on the final values
theorem wl_gate (D : List (Bool × ℕ × ℕ)) (w : List α) (j : ℕ) (hj : j < D.length)
    (ha : (D[j]'hj).2.1 < w.length + j) (hb : (D[j]'hj).2.2 < w.length + j) :
    (wl F d D w).getD (w.length + j) d =
      F (D[j]'hj).1 ((wl F d D w).getD (D[j]'hj).2.1 d)
        ((wl F d D w).getD (D[j]'hj).2.2 d) := by
  have hsplit : D = D.take j ++ (D[j]'hj) :: D.drop (j + 1) := by simp
  have hlen : (wl F d (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  rw [← wl_take_getD F d D w j _ ha hj.le, ← wl_take_getD F d D w j _ hb hj.le]
  conv_lhs => rw [hsplit, wl_append, wl_cons]
  rw [wl_getD_lt F d _ _ _ (by rw [wstep_length, hlen]; omega), ← hlen, wstep_getD_last]

end Eval

-- the gate list as a map over positions, each gate guarded to read only earlier wires
def gd (W0 : ℕ) (raw : ℕ → Bool × ℕ × ℕ) (j : ℕ) : Bool × ℕ × ℕ :=
  if (raw j).2.1 < W0 + j ∧ (raw j).2.2 < W0 + j then raw j else (true, 0, 0)

def glist (W0 N : ℕ) (raw : ℕ → Bool × ℕ × ℕ) : List (Bool × ℕ × ℕ) :=
  (List.range N).map (gd W0 raw)

theorem glist_length (W0 N : ℕ) (raw : ℕ → Bool × ℕ × ℕ) : (glist W0 N raw).length = N := by
  simp [glist]

theorem glist_get (W0 N : ℕ) (raw : ℕ → Bool × ℕ × ℕ) (j : ℕ) (hj : j < (glist W0 N raw).length) :
    (glist W0 N raw)[j]'hj = gd W0 raw j := by
  simp [glist]

theorem gd_lt (W0 : ℕ) (hW : 0 < W0) (raw : ℕ → Bool × ℕ × ℕ) (j : ℕ) :
    (gd W0 raw j).2.1 < W0 + j ∧ (gd W0 raw j).2.2 < W0 + j := by
  unfold gd
  split_ifs with hg
  · exact hg
  · exact ⟨by show 0 < W0 + j; omega, by show 0 < W0 + j; omega⟩

theorem gd_eq (W0 : ℕ) (raw : ℕ → Bool × ℕ × ℕ) (j : ℕ)
    (h1 : (raw j).2.1 < W0 + j) (h2 : (raw j).2.2 < W0 + j) : gd W0 raw j = raw j := by
  unfold gd
  rw [if_pos ⟨h1, h2⟩]

-- the value and the depth of a guarded gate wire
theorem gate_val (W0 N : ℕ) (hW : 0 < W0) (raw : ℕ → Bool × ℕ × ℕ) (w : List Bool)
    (hw : w.length = W0) (j : ℕ) (hj : j < N) :
    (wl gop false (glist W0 N raw) w).getD (W0 + j) false =
      gop (gd W0 raw j).1 ((wl gop false (glist W0 N raw) w).getD (gd W0 raw j).2.1 false)
        ((wl gop false (glist W0 N raw) w).getD (gd W0 raw j).2.2 false) := by
  have hj' : j < (glist W0 N raw).length := by rw [glist_length]; exact hj
  have hg := glist_get W0 N raw j hj'
  have hlt := gd_lt W0 hW raw j
  have := wl_gate gop false (glist W0 N raw) w j hj' (by rw [hg, hw]; exact hlt.1)
    (by rw [hg, hw]; exact hlt.2)
  rw [hw, hg] at this
  exact this

theorem gate_dep (W0 N : ℕ) (hW : 0 < W0) (raw : ℕ → Bool × ℕ × ℕ) (w : List ℕ)
    (hw : w.length = W0) (j : ℕ) (hj : j < N) :
    (wl dop 0 (glist W0 N raw) w).getD (W0 + j) 0 =
      max ((wl dop 0 (glist W0 N raw) w).getD (gd W0 raw j).2.1 0)
        ((wl dop 0 (glist W0 N raw) w).getD (gd W0 raw j).2.2 0) + 1 := by
  have hj' : j < (glist W0 N raw).length := by rw [glist_length]; exact hj
  have hg := glist_get W0 N raw j hj'
  have hlt := gd_lt W0 hW raw j
  have := wl_gate dop 0 (glist W0 N raw) w j hj' (by rw [hg, hw]; exact hlt.1)
    (by rw [hg, hw]; exact hlt.2)
  rw [hw, hg] at this
  exact this

-- the pin wires
theorem pins_length (n : ℕ) (ρ : Fin n → Option Bool) :
    ([false, true] ++ List.ofFn (fun i : Fin n => decide (ρ i = some false)) ++
      List.ofFn (fun i : Fin n => decide (ρ i = some true))).length = 2 + 2 * n := by
  simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil] <;> omega

theorem pins_zero (n : ℕ) (ρ : Fin n → Option Bool) :
    ([false, true] ++ List.ofFn (fun i : Fin n => decide (ρ i = some false)) ++
      List.ofFn (fun i : Fin n => decide (ρ i = some true))).getD 0 false = false := by
  simp

theorem pins_one (n : ℕ) (ρ : Fin n → Option Bool) :
    ([false, true] ++ List.ofFn (fun i : Fin n => decide (ρ i = some false)) ++
      List.ofFn (fun i : Fin n => decide (ρ i = some true))).getD 1 false = true := by
  simp

theorem pins_lo (n : ℕ) (ρ : Fin n → Option Bool) (i : Fin n) :
    ([false, true] ++ List.ofFn (fun i : Fin n => decide (ρ i = some false)) ++
      List.ofFn (fun i : Fin n => decide (ρ i = some true))).getD (2 + i.val) false =
      decide (ρ i = some false) := by
  have hl : ([false, true] ++ List.ofFn (fun i : Fin n => decide (ρ i = some false))).length =
      2 + n := by
    simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil] <;> omega
  have h1 : 2 + i.val <
      ([false, true] ++ List.ofFn (fun i : Fin n => decide (ρ i = some false))).length := by
    rw [hl]; omega
  have h2 : [false, true].length ≤ 2 + i.val := by
    simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1, List.getElem?_append_right h2]
  simp

theorem pins_hi (n : ℕ) (ρ : Fin n → Option Bool) (i : Fin n) :
    ([false, true] ++ List.ofFn (fun i : Fin n => decide (ρ i = some false)) ++
      List.ofFn (fun i : Fin n => decide (ρ i = some true))).getD (2 + n + i.val) false =
      decide (ρ i = some true) := by
  have hl : ([false, true] ++ List.ofFn (fun i : Fin n => decide (ρ i = some false))).length =
      2 + n := by
    simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil] <;> omega
  have h2 : ([false, true] ++ List.ofFn (fun i : Fin n => decide (ρ i = some false))).length ≤
      2 + n + i.val := by
    rw [hl]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h2, hl, Nat.add_sub_cancel_left]
  simp

-- row combinations and syndromes as numbers below 2 ^ h
def toF {h : ℕ} (v : Fin h → ZMod 2) : Fin h → Fin 2 := fun j => ⟨(v j).val, ZMod.val_lt (v j)⟩

def enc {h : ℕ} (v : Fin h → ZMod 2) : ℕ := (finFunctionFinEquiv (toF v)).val

def yvec (h z : ℕ) : Fin h → ZMod 2 := fun j => ((z / 2 ^ j.val % 2 : ℕ) : ZMod 2)

theorem enc_lt {h : ℕ} (v : Fin h → ZMod 2) : enc v < 2 ^ h :=
  (finFunctionFinEquiv (toF v)).isLt

theorem yvec_enc {h : ℕ} (v : Fin h → ZMod 2) : yvec h (enc v) = v := by
  funext j
  have h1 : ((finFunctionFinEquiv.symm (finFunctionFinEquiv (toF v)) j : Fin 2) : ℕ) =
      enc v / 2 ^ j.val % 2 := rfl
  rw [Equiv.symm_apply_apply] at h1
  simp only [yvec]
  rw [← h1]
  exact ZMod.natCast_zmod_val (v j)

-- the tree size: 2 ^ clog 2 (n + 1) is at most 2 n + 1
theorem M_le (n : ℕ) : 2 ^ Nat.clog 2 (n + 1) ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.clog_one_right]
  · have h1 := Nat.pow_pred_clog_lt_self 2 (show 1 < n + 1 by omega)
    have h2 : 0 < Nat.clog 2 (n + 1) := Nat.clog_pos (by norm_num) (by omega)
    have h3 : 2 ^ Nat.clog 2 (n + 1) = 2 * 2 ^ (Nat.clog 2 (n + 1)).pred := by
      rw [← pow_succ']
      congr 1
      exact (Nat.succ_pred_eq_of_pos h2).symm
    omega

theorem M_ge (n : ℕ) : n + 1 ≤ 2 ^ Nat.clog 2 (n + 1) := Nat.le_pow_clog (by norm_num) _

-- combining two known-parity flags
theorem comb (A B : Prop) (x y p : ZMod 2) :
    ((A ∧ B) ∧ x + y = p) ↔
      ((A ∧ x = 0) ∧ (B ∧ y = p)) ∨ ((A ∧ x = 1) ∧ (B ∧ y = p + 1)) := by
  have key : ∀ x y p : ZMod 2, x + y = p ↔ ((x = 0 ∧ y = p) ∨ (x = 1 ∧ y = p + 1)) := by
    decide
  rw [key]
  tauto

-- known-parity flag of the sites in [lo, hi)
def Flag (ok : ℕ → Prop) (par : ℕ → ZMod 2) (lo hi : ℕ) (p : ZMod 2) : Prop :=
  (∀ k, lo ≤ k → k < hi → ok k) ∧ (∑ k ∈ Finset.Ico lo hi, par k) = p

theorem Flag_split (ok : ℕ → Prop) (par : ℕ → ZMod 2) (lo mid hi : ℕ) (p : ZMod 2)
    (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    Flag ok par lo hi p ↔ (Flag ok par lo mid 0 ∧ Flag ok par mid hi p) ∨
      (Flag ok par lo mid 1 ∧ Flag ok par mid hi (p + 1)) := by
  have hs : (∑ k ∈ Finset.Ico lo hi, par k) =
      (∑ k ∈ Finset.Ico lo mid, par k) + ∑ k ∈ Finset.Ico mid hi, par k :=
    (Finset.sum_Ico_consecutive par h1 h2).symm
  have hall : (∀ k, lo ≤ k → k < hi → ok k) ↔
      (∀ k, lo ≤ k → k < mid → ok k) ∧ (∀ k, mid ≤ k → k < hi → ok k) := by
    constructor
    · intro H
      exact ⟨fun k a b => H k a (by omega), fun k a b => H k (by omega) b⟩
    · rintro ⟨H1, H2⟩ k a b
      by_cases hk : k < mid
      · exact H1 k a hk
      · exact H2 k (by omega) b
  unfold Flag
  rw [hs, hall, comb]

-- the butterfly over the bits of a row combination
def bset {h : ℕ} (z : Fin h → ZMod 2) (t : ℕ) (a : ZMod 2) : Fin h → ZMod 2 :=
  fun j => if j.val = t then a else z j

def bsum {h : ℕ} (y z : Fin h → ZMod 2) (t : ℕ) : ZMod 2 :=
  ∑ j : Fin h, if j.val < t then y j * z j else 0

def BF {h : ℕ} (P : (Fin h → ZMod 2) → ZMod 2 → Prop) (t : ℕ) (z : Fin h → ZMod 2)
    (e : ZMod 2) : Prop :=
  ∃ y : Fin h → ZMod 2, (∀ j : Fin h, t ≤ j.val → y j = z j) ∧ P y (e + bsum y z t)

theorem bsum_bset {h : ℕ} (y z : Fin h → ZMod 2) (t : ℕ) (a : ZMod 2) :
    bsum y (bset z t a) t = bsum y z t := by
  unfold bsum bset
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < t
  · have hjt : ¬ (j.val = t) := by omega
    rw [if_pos hj, if_pos hj, if_neg hjt]
  · rw [if_neg hj, if_neg hj]

theorem bsum_succ {h : ℕ} (y z : Fin h → ZMod 2) (t : ℕ) (ht : t < h) :
    bsum y z (t + 1) = bsum y z t + y ⟨t, ht⟩ * z ⟨t, ht⟩ := by
  unfold bsum
  have key : ∀ j : Fin h, (if j.val < t + 1 then y j * z j else 0) =
      (if j.val < t then y j * z j else 0) + (if j = ⟨t, ht⟩ then y j * z j else 0) := by
    intro j
    by_cases h1 : j.val < t
    · have h2 : j ≠ ⟨t, ht⟩ := fun e => by rw [e] at h1; exact lt_irrefl _ h1
      have h4 : j.val < t + 1 := by omega
      rw [if_pos h4, if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : j = ⟨t, ht⟩
      · subst h2
        simp
      · have h3 : j.val ≠ t := fun e => h2 (Fin.ext e)
        have h4 : ¬ (j.val < t + 1) := by omega
        rw [if_neg h4, if_neg h1, if_neg h2, add_zero]
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem BF_zero {h : ℕ} (P : (Fin h → ZMod 2) → ZMod 2 → Prop) (z : Fin h → ZMod 2)
    (e : ZMod 2) : BF P 0 z e ↔ P z e := by
  have h0 : ∀ y : Fin h → ZMod 2, bsum y z 0 = 0 := by
    intro y
    simp [bsum]
  constructor
  · rintro ⟨y, hy, hP⟩
    have : y = z := funext fun j => hy j (Nat.zero_le _)
    subst this
    rwa [h0, add_zero] at hP
  · intro hP
    exact ⟨z, fun _ _ => rfl, by rwa [h0, add_zero]⟩

theorem BF_top {h : ℕ} (P : (Fin h → ZMod 2) → ZMod 2 → Prop) (z : Fin h → ZMod 2)
    (e : ZMod 2) : BF P h z e ↔ ∃ y : Fin h → ZMod 2, P y (e + ∑ j, y j * z j) := by
  have hb : ∀ y : Fin h → ZMod 2, bsum y z h = ∑ j, y j * z j := by
    intro y
    unfold bsum
    apply Finset.sum_congr rfl
    intro j _
    rw [if_pos j.isLt]
  constructor
  · rintro ⟨y, -, hP⟩
    exact ⟨y, by rwa [hb] at hP⟩
  · rintro ⟨y, hP⟩
    exact ⟨y, fun j hj => absurd j.isLt (by omega), by rwa [hb]⟩

theorem BF_succ {h : ℕ} (P : (Fin h → ZMod 2) → ZMod 2 → Prop) (t : ℕ) (ht : t < h)
    (z : Fin h → ZMod 2) (e : ZMod 2) :
    BF P (t + 1) z e ↔ BF P t (bset z t 0) e ∨ BF P t (bset z t 1) (e + z ⟨t, ht⟩) := by
  constructor
  · rintro ⟨y, hy, hP⟩
    rw [bsum_succ y z t ht] at hP
    rcases z2 (y ⟨t, ht⟩) with h0 | h1
    · left
      refine ⟨y, fun j hj => ?_, ?_⟩
      · unfold bset
        by_cases hjt : j.val = t
        · rw [if_pos hjt, ← h0]
          congr 1
          exact Fin.ext hjt
        · rw [if_neg hjt]
          exact hy j (by omega)
      · rw [bsum_bset]
        rw [h0, zero_mul, add_zero] at hP
        exact hP
    · right
      refine ⟨y, fun j hj => ?_, ?_⟩
      · unfold bset
        by_cases hjt : j.val = t
        · rw [if_pos hjt, ← h1]
          congr 1
          exact Fin.ext hjt
        · rw [if_neg hjt]
          exact hy j (by omega)
      · rw [bsum_bset]
        rw [h1, one_mul] at hP
        have : e + (bsum y z t + z ⟨t, ht⟩) = e + z ⟨t, ht⟩ + bsum y z t := by ring
        rw [← this]
        exact hP
  · rintro (⟨y, hy, hP⟩ | ⟨y, hy, hP⟩)
    · have h0 : y ⟨t, ht⟩ = 0 := by
        have := hy ⟨t, ht⟩ le_rfl
        rw [this]
        simp [bset]
      refine ⟨y, fun j hj => ?_, ?_⟩
      · rw [hy j (by omega)]
        have hjt : ¬ (j.val = t) := by omega
        unfold bset
        rw [if_neg hjt]
      · rw [bsum_succ y z t ht, h0, zero_mul, add_zero]
        rw [bsum_bset] at hP
        exact hP
    · have h1 : y ⟨t, ht⟩ = 1 := by
        have := hy ⟨t, ht⟩ le_rfl
        rw [this]
        simp [bset]
      refine ⟨y, fun j hj => ?_, ?_⟩
      · rw [hy j (by omega)]
        have hjt : ¬ (j.val = t) := by omega
        unfold bset
        rw [if_neg hjt]
      · rw [bsum_succ y z t ht, h1, one_mul]
        rw [bsum_bset] at hP
        have : e + (bsum y z t + z ⟨t, ht⟩) = e + z ⟨t, ht⟩ + bsum y z t := by ring
        rw [this]
        exact hP

-- the pin list, and its wires by site number
def pinsL (n : ℕ) (ρ : Fin n → Option Bool) : List Bool :=
  [false, true] ++ List.ofFn (fun i : Fin n => decide (ρ i = some false)) ++
    List.ofFn (fun i : Fin n => decide (ρ i = some true))

theorem pinsL_length (n : ℕ) (ρ : Fin n → Option Bool) : (pinsL n ρ).length = 2 + 2 * n := by
  unfold pinsL
  simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil] <;> omega

theorem pinsL_lo (n : ℕ) (ρ : Fin n → Option Bool) (k : ℕ) (hk : k < n) :
    (pinsL n ρ).getD (2 + k) false = decide (ρ ⟨k, hk⟩ = some false) := by
  have hl : ([false, true] ++ List.ofFn (fun i : Fin n => decide (ρ i = some false))).length =
      2 + n := by
    simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil] <;> omega
  have h1 : 2 + k <
      ([false, true] ++ List.ofFn (fun i : Fin n => decide (ρ i = some false))).length := by
    rw [hl]; omega
  have h2 : [false, true].length ≤ 2 + k := by
    simp
  unfold pinsL
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1, List.getElem?_append_right h2]
  simp [hk]

theorem pinsL_hi (n : ℕ) (ρ : Fin n → Option Bool) (k : ℕ) (hk : k < n) :
    (pinsL n ρ).getD (2 + n + k) false = decide (ρ ⟨k, hk⟩ = some true) := by
  have hl : ([false, true] ++ List.ofFn (fun i : Fin n => decide (ρ i = some false))).length =
      2 + n := by
    simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil] <;> omega
  have h2 : ([false, true] ++ List.ofFn (fun i : Fin n => decide (ρ i = some false))).length ≤
      2 + n + k := by
    rw [hl]; omega
  unfold pinsL
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h2, hl, Nat.add_sub_cancel_left]
  simp [hk]

theorem pinsL_zero (n : ℕ) (ρ : Fin n → Option Bool) : (pinsL n ρ).getD 0 false = false := by
  simp [pinsL]

theorem pinsL_one (n : ℕ) (ρ : Fin n → Option Bool) : (pinsL n ρ).getD 1 false = true := by
  simp [pinsL]

-- layout of the trees: H levels, M leaves, sites padded to ℕ
def HH (n : ℕ) : ℕ := Nat.clog 2 (n + 1)

def MM (n : ℕ) : ℕ := 2 ^ HH n

def cf (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (yv : Fin h → ZMod 2) (k : ℕ) : ZMod 2 :=
  if hk : k < n then ∑ j, yv j * A j ⟨k, hk⟩ else 0

def rho (n : ℕ) (ρ : Fin n → Option Bool) (k : ℕ) : Option Bool :=
  if hk : k < n then ρ ⟨k, hk⟩ else none

def okS (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (yv : Fin h → ZMod 2) (k : ℕ) : Prop :=
  cf n h A yv k = 0 ∨ rho n ρ k ≠ none

def parS (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (yv : Fin h → ZMod 2) (k : ℕ) : ZMod 2 :=
  if rho n ρ k = some true then cf n h A yv k else 0

-- the flag of tree node (l, a), which covers the sites [a 2^(H-l), (a+1) 2^(H-l))
def KF (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (yv : Fin h → ZMod 2) (l a : ℕ) (p : ZMod 2) : Prop :=
  Flag (okS n h A ρ yv) (parS n h A ρ yv) (a * 2 ^ (HH n - l)) ((a + 1) * 2 ^ (HH n - l)) p

def leafW (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (y k : ℕ) (p : ZMod 2) : ℕ :=
  if k < n ∧ cf n h A (yvec h y) k = 1 then (if p = 0 then 2 + k else 2 + n + k)
  else (if p = 0 then 1 else 0)

-- slot of heap node v of tree y in the up pass (children come first)
def uq (n y v : ℕ) : ℕ := y * MM n + (MM n - 1 - v)

-- the wire of the flag of heap node v of tree y
def wK (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (y v : ℕ) (p : ZMod 2) : ℕ :=
  if MM n ≤ v then leafW n h A y (v - MM n) p
  else 2 + 2 * n + (6 * uq n y v + (if p = 0 then 2 else 5))

-- the six gates of an up node: AND(L0,R0), AND(L1,R1), OR = K0, AND(L0,R1), AND(L1,R0), OR = K1
def upOp (c : ℕ) : Bool := if c = 2 ∨ c = 5 then false else true

def upA (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (y v c : ℕ) : ℕ :=
  if c = 2 then 2 + 2 * n + (6 * uq n y v + 0)
  else if c = 5 then 2 + 2 * n + (6 * uq n y v + 3)
  else wK n h A y (2 * v) (if c = 0 ∨ c = 3 then 0 else 1)

def upB (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (y v c : ℕ) : ℕ :=
  if c = 2 then 2 + 2 * n + (6 * uq n y v + 1)
  else if c = 5 then 2 + 2 * n + (6 * uq n y v + 4)
  else wK n h A y (2 * v + 1) (if c = 0 ∨ c = 4 then 0 else 1)

def upGate (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (j : ℕ) : Bool × ℕ × ℕ :=
  (upOp (j % 6), upA n h A (j / 6 / MM n) (MM n - 1 - j / 6 % MM n) (j % 6),
    upB n h A (j / 6 / MM n) (MM n - 1 - j / 6 % MM n) (j % 6))

def SU (n h : ℕ) : ℕ := 6 * (2 ^ h * MM n)

-- slot of heap node v of tree y in the down pass (parents come first)
def dq (n y v : ℕ) : ℕ := y * (2 * MM n) + v

def SD (n h : ℕ) : ℕ := 6 * (2 ^ h * (2 * MM n))

def TT (n : ℕ) : ℕ := 2 * n + 1

def SB (n h : ℕ) : ℕ := 2 * (h * TT n * 2 ^ h)

def NN (n h : ℕ) : ℕ := SU n h + SD n h + SB n h

def sib (v : ℕ) : ℕ := if v % 2 = 0 then v + 1 else v - 1

-- the wire of the outside flag of heap node v of tree y (the root has the constant flag)
def wO (n h : ℕ) (y v : ℕ) (p : ZMod 2) : ℕ :=
  if v ≤ 1 then (if p = 0 then 1 else 0)
  else 2 + 2 * n + (SU n h + (6 * dq n y v + (if p = 0 then 2 else 5)))

-- the six gates of a down node read the parent outside flag and the sibling flag
def dnA (n h : ℕ) (y v c : ℕ) : ℕ :=
  if c = 2 then 2 + 2 * n + (SU n h + (6 * dq n y v + 0))
  else if c = 5 then 2 + 2 * n + (SU n h + (6 * dq n y v + 3))
  else wO n h y (v / 2) (if c = 0 ∨ c = 3 then 0 else 1)

def dnB (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (y v c : ℕ) : ℕ :=
  if c = 2 then 2 + 2 * n + (SU n h + (6 * dq n y v + 1))
  else if c = 5 then 2 + 2 * n + (SU n h + (6 * dq n y v + 4))
  else wK n h A y (sib v) (if c = 0 ∨ c = 4 then 0 else 1)

def dnGate (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (j : ℕ) : Bool × ℕ × ℕ :=
  (upOp (j % 6), dnA n h (j / 6 / (2 * MM n)) (j / 6 % (2 * MM n)) (j % 6),
    dnB n h A (j / 6 / (2 * MM n)) (j / 6 % (2 * MM n)) (j % 6))

-- butterfly layout: level t (reading level t - 1), target τ, position z, sign e
def bq (n h t τ z : ℕ) : ℕ := (t * TT n + τ) * 2 ^ h + z

def dig (z t : ℕ) : ZMod 2 := ((z / 2 ^ t % 2 : ℕ) : ZMod 2)

-- the inputs of the butterflies: root flags for dead, leaf outside flags for excludeBit
def wG (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (τ z : ℕ) (e : ZMod 2) : ℕ :=
  if τ = 2 * n then wK n h A z 1 (e + 1)
  else wO n h z (MM n + τ / 2) (e + 1 + ((τ % 2 : ℕ) : ZMod 2) * cf n h A (yvec h z) (τ / 2))

def wF (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (t τ z : ℕ) (e : ZMod 2) : ℕ :=
  if t = 0 then wG n h A τ z e
  else 2 + 2 * n + (SU n h + SD n h + (2 * bq n h (t - 1) τ z + e.val))

def bfGate (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (j : ℕ) : Bool × ℕ × ℕ :=
  (false,
    wF n h A (j / 2 / 2 ^ h / TT n) (j / 2 / 2 ^ h % TT n)
      (enc (bset (yvec h (j / 2 % 2 ^ h)) (j / 2 / 2 ^ h / TT n) 0)) ((j % 2 : ℕ) : ZMod 2),
    wF n h A (j / 2 / 2 ^ h / TT n) (j / 2 / 2 ^ h % TT n)
      (enc (bset (yvec h (j / 2 % 2 ^ h)) (j / 2 / 2 ^ h / TT n) 1))
      (((j % 2 : ℕ) : ZMod 2) + dig (j / 2 % 2 ^ h) (j / 2 / 2 ^ h / TT n)))

-- the up pass, the down pass and the butterflies
def rawU (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (j : ℕ) : Bool × ℕ × ℕ :=
  if j < SU n h then upGate n h A j
  else if j < SU n h + SD n h then dnGate n h A (j - SU n h)
  else if j < SU n h + SD n h + SB n h then bfGate n h A (j - (SU n h + SD n h))
  else (true, 0, 0)

def GU (n h : ℕ) (A : Fin h → Fin n → ZMod 2) : List (Bool × ℕ × ℕ) :=
  glist (2 + 2 * n) (NN n h) (rawU n h A)

def vl (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool) (k : ℕ) : Bool :=
  (wl gop false (GU n h A) (pinsL n ρ)).getD k false

theorem dm (q r m : ℕ) (hr : r < m) : (q * m + r) / m = q ∧ (q * m + r) % m = r := by
  have hm : 0 < m := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right r q hm, Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

theorem idx_lt (y r Y m : ℕ) (hy : y < Y) (hr : r < m) : y * m + r < Y * m := by
  have h1 : (y + 1) * m ≤ Y * m := Nat.mul_le_mul_right m hy
  have h2 : (y + 1) * m = y * m + m := by ring
  omega

theorem up_raw (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (y v c : ℕ) (hy : y < 2 ^ h)
    (hv : v < MM n) (hc : c < 6) :
    rawU n h A (6 * uq n y v + c) = (upOp c, upA n h A y v c, upB n h A y v c) := by
  have hr : MM n - 1 - v < MM n := by omega
  obtain ⟨d1, d2⟩ := dm y (MM n - 1 - v) (MM n) hr
  have h6 : (6 * uq n y v + c) / 6 = y * MM n + (MM n - 1 - v) := by unfold uq; omega
  have h6' : (6 * uq n y v + c) % 6 = c := by omega
  have hvv : MM n - 1 - (MM n - 1 - v) = v := by omega
  have hlt : 6 * uq n y v + c < SU n h := by
    have := idx_lt y (MM n - 1 - v) (2 ^ h) (MM n) hy hr
    unfold SU uq
    omega
  unfold rawU upGate
  rw [if_pos hlt, h6', h6, d1, d2, hvv]

theorem leafW_lt (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (y k : ℕ) (p : ZMod 2) :
    leafW n h A y k p < 2 + 2 * n := by
  unfold leafW
  by_cases h1 : k < n ∧ cf n h A (yvec h y) k = 1
  · have hk := h1.1
    rw [if_pos h1]
    split_ifs <;> omega
  · rw [if_neg h1]
    split_ifs <;> omega

theorem wK_child_lt (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (y v b : ℕ) (p : ZMod 2)
    (hb : b < 2) (hv1 : 1 ≤ v) :
    wK n h A y (2 * v + b) p < 2 + 2 * n + (6 * uq n y v + 0) := by
  unfold wK
  split_ifs with h1 h2
  · have := leafW_lt n h A y (2 * v + b - MM n) p
    omega
  · unfold uq
    omega
  · unfold uq
    omega

theorem upA_lt (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (y v c : ℕ) (hv1 : 1 ≤ v) (hc : c < 6) :
    upA n h A y v c < 2 + 2 * n + (6 * uq n y v + c) := by
  unfold upA
  by_cases h2 : c = 2
  · rw [if_pos h2]
    omega
  · rw [if_neg h2]
    by_cases h5 : c = 5
    · rw [if_pos h5]
      omega
    · rw [if_neg h5]
      have := wK_child_lt n h A y v 0 (if c = 0 ∨ c = 3 then 0 else 1) (by omega) hv1
      simp only [Nat.add_zero] at this
      omega

theorem upB_lt (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (y v c : ℕ) (hv1 : 1 ≤ v) (hc : c < 6) :
    upB n h A y v c < 2 + 2 * n + (6 * uq n y v + c) := by
  unfold upB
  by_cases h2 : c = 2
  · rw [if_pos h2]
    omega
  · rw [if_neg h2]
    by_cases h5 : c = 5
    · rw [if_pos h5]
      omega
    · rw [if_neg h5]
      have := wK_child_lt n h A y v 1 (if c = 0 ∨ c = 4 then 0 else 1) (by omega) hv1
      omega

theorem gop_true (a b : Bool) : gop true a b = (a && b) := rfl

theorem gop_false (a b : Bool) : gop false a b = (a || b) := rfl

-- the value of a gate of the up pass
theorem up_val (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (y v c : ℕ) (hy : y < 2 ^ h) (hv1 : 1 ≤ v) (hv : v < MM n) (hc : c < 6) :
    vl n h A ρ (2 + 2 * n + (6 * uq n y v + c)) =
      gop (upOp c) (vl n h A ρ (upA n h A y v c)) (vl n h A ρ (upB n h A y v c)) := by
  have hr : MM n - 1 - v < MM n := by omega
  have hlt : 6 * uq n y v + c < SU n h := by
    have := idx_lt y (MM n - 1 - v) (2 ^ h) (MM n) hy hr
    unfold SU uq
    omega
  have hraw := up_raw n h A y v c hy hv hc
  have hg := gd_eq (2 + 2 * n) (rawU n h A) (6 * uq n y v + c)
    (by rw [hraw]; exact upA_lt n h A y v c hv1 hc) (by rw [hraw]; exact upB_lt n h A y v c hv1 hc)
  have := gate_val (2 + 2 * n) (NN n h) (by omega) (rawU n h A) (pinsL n ρ) (pinsL_length n ρ)
    (6 * uq n y v + c) (by unfold NN; omega)
  rw [hg, hraw] at this
  exact this

-- leaves are input wires
theorem L_leaf (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (yv : Fin h → ZMod 2) (k : ℕ) (p : ZMod 2) :
    vl n h A ρ (leafW n h A (enc yv) k p) = true ↔
      okS n h A ρ yv k ∧ parS n h A ρ yv k = p := by
  unfold vl
  rw [wl_getD_lt gop false _ _ _ (by rw [pinsL_length]; exact leafW_lt n h A _ k p)]
  unfold leafW
  rw [yvec_enc]
  have h00 : (0 : ZMod 2) = 0 := rfl
  have h10 : ¬ ((1 : ZMod 2) = 0) := by decide
  by_cases hk : k < n
  · by_cases hc : cf n h A yv k = 1
    · have hkc : k < n ∧ cf n h A yv k = 1 := ⟨hk, hc⟩
      rw [if_pos hkc]
      have hok : okS n h A ρ yv k ↔ ρ ⟨k, hk⟩ ≠ none := by
        unfold okS rho
        rw [dif_pos hk, hc]
        simp
      have hpar : parS n h A ρ yv k = if ρ ⟨k, hk⟩ = some true then 1 else 0 := by
        unfold parS rho
        rw [dif_pos hk, hc]
      rw [hok, hpar]
      rcases z2 p with rfl | rfl
      · rw [if_pos h00, pinsL_lo n ρ k hk]
        cases ρ ⟨k, hk⟩ with
        | none => simp
        | some b => cases b <;> simp
      · rw [if_neg h10, pinsL_hi n ρ k hk]
        cases ρ ⟨k, hk⟩ with
        | none => simp
        | some b => cases b <;> simp
    · have hc0 : cf n h A yv k = 0 := by
        rcases z2 (cf n h A yv k) with h0 | h1
        · exact h0
        · exact absurd h1 hc
      have hn : ¬ (k < n ∧ cf n h A yv k = 1) := fun hh => hc hh.2
      rw [if_neg hn]
      have hok : okS n h A ρ yv k := Or.inl hc0
      have hpar : parS n h A ρ yv k = 0 := by
        unfold parS
        rw [hc0]
        simp
      rw [hpar]
      rcases z2 p with rfl | rfl
      · rw [if_pos h00, pinsL_one]
        simp [hok]
      · rw [if_neg h10, pinsL_zero]
        simp
  · have hc0 : cf n h A yv k = 0 := by
      unfold cf
      rw [dif_neg hk]
    have hn : ¬ (k < n ∧ cf n h A yv k = 1) := fun hh => hk hh.1
    rw [if_neg hn]
    have hok : okS n h A ρ yv k := Or.inl hc0
    have hpar : parS n h A ρ yv k = 0 := by
      unfold parS
      rw [hc0]
      simp
    rw [hpar]
    rcases z2 p with rfl | rfl
    · rw [if_pos h00, pinsL_one]
      simp [hok]
    · rw [if_neg h10, pinsL_zero]
      simp

-- the up pass computes the flag of every node
theorem L_up (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (yv : Fin h → ZMod 2) :
    ∀ m l a, l + m = HH n → a < 2 ^ l → ∀ p : ZMod 2,
      (vl n h A ρ (wK n h A (enc yv) (2 ^ l + a) p) = true ↔ KF n h A ρ yv l a p) := by
  intro m
  induction m with
  | zero =>
    intro l a hl ha p
    have hl' : l = HH n := by omega
    subst hl'
    have hv : MM n ≤ 2 ^ HH n + a := by unfold MM; omega
    have hva : 2 ^ HH n + a - MM n = a := by unfold MM; omega
    unfold wK
    rw [if_pos hv, hva, L_leaf]
    unfold KF Flag
    rw [Nat.sub_self, pow_zero, mul_one, mul_one, Nat.Ico_succ_singleton, Finset.sum_singleton]
    constructor
    · rintro ⟨hok, hp⟩
      refine ⟨fun k h1 h2 => ?_, hp⟩
      have hka : k = a := by omega
      rw [hka]
      exact hok
    · rintro ⟨hok, hp⟩
      exact ⟨hok a le_rfl (by omega), hp⟩
  | succ m ih =>
    intro l a hl ha p
    have hlt : l < HH n := by omega
    have hpow : 2 ^ (l + 1) ≤ MM n := by
      unfold MM
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2l : 2 ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
    have hpos : 0 < 2 ^ l := pow_pos (by norm_num) l
    have hv : 2 ^ l + a < MM n := by omega
    have hv1 : 1 ≤ 2 ^ l + a := by omega
    have hy : enc yv < 2 ^ h := enc_lt yv
    have hc0 : 2 * (2 ^ l + a) = 2 ^ (l + 1) + 2 * a := by rw [h2l]; ring
    have hc1 : 2 * (2 ^ l + a) + 1 = 2 ^ (l + 1) + (2 * a + 1) := by rw [h2l]; ring
    have ihL := ih (l + 1) (2 * a) (by omega) (by omega)
    have ihR := ih (l + 1) (2 * a + 1) (by omega) (by omega)
    rw [← hc0] at ihL
    rw [← hc1] at ihR
    have hP : 2 ^ (HH n - l) = 2 * 2 ^ (HH n - (l + 1)) := by
      rw [show HH n - l = HH n - (l + 1) + 1 by omega, pow_succ]
      ring
    have hsplit : ∀ q : ZMod 2, KF n h A ρ yv l a q ↔
        (KF n h A ρ yv (l + 1) (2 * a) 0 ∧ KF n h A ρ yv (l + 1) (2 * a + 1) q) ∨
        (KF n h A ρ yv (l + 1) (2 * a) 1 ∧ KF n h A ρ yv (l + 1) (2 * a + 1) (q + 1)) := by
      intro q
      unfold KF
      rw [hP, show a * (2 * 2 ^ (HH n - (l + 1))) = 2 * a * 2 ^ (HH n - (l + 1)) by ring,
        show (a + 1) * (2 * 2 ^ (HH n - (l + 1))) = (2 * a + 1 + 1) * 2 ^ (HH n - (l + 1)) by ring]
      exact Flag_split _ _ _ _ _ q (Nat.mul_le_mul_right _ (by omega))
        (Nat.mul_le_mul_right _ (by omega))
    have hnot : ¬ (MM n ≤ 2 ^ l + a) := by omega
    have hw : ∀ q : ZMod 2, wK n h A (enc yv) (2 ^ l + a) q =
        2 + 2 * n + (6 * uq n (enc yv) (2 ^ l + a) + (if q = 0 then 2 else 5)) := by
      intro q
      unfold wK
      rw [if_neg hnot]
    have h00 : (0 : ZMod 2) = 0 := rfl
    have h10 : ¬ ((1 : ZMod 2) = 0) := by decide
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have e0 : vl n h A ρ (2 + 2 * n + (6 * uq n (enc yv) (2 ^ l + a) + 0)) =
        (vl n h A ρ (wK n h A (enc yv) (2 * (2 ^ l + a)) 0) &&
          vl n h A ρ (wK n h A (enc yv) (2 * (2 ^ l + a) + 1) 0)) :=
      (up_val n h A ρ (enc yv) (2 ^ l + a) 0 hy hv1 hv (by norm_num)).trans rfl
    have e1 : vl n h A ρ (2 + 2 * n + (6 * uq n (enc yv) (2 ^ l + a) + 1)) =
        (vl n h A ρ (wK n h A (enc yv) (2 * (2 ^ l + a)) 1) &&
          vl n h A ρ (wK n h A (enc yv) (2 * (2 ^ l + a) + 1) 1)) :=
      (up_val n h A ρ (enc yv) (2 ^ l + a) 1 hy hv1 hv (by norm_num)).trans rfl
    have e2 : vl n h A ρ (2 + 2 * n + (6 * uq n (enc yv) (2 ^ l + a) + 2)) =
        (vl n h A ρ (2 + 2 * n + (6 * uq n (enc yv) (2 ^ l + a) + 0)) ||
          vl n h A ρ (2 + 2 * n + (6 * uq n (enc yv) (2 ^ l + a) + 1))) :=
      (up_val n h A ρ (enc yv) (2 ^ l + a) 2 hy hv1 hv (by norm_num)).trans rfl
    have e3 : vl n h A ρ (2 + 2 * n + (6 * uq n (enc yv) (2 ^ l + a) + 3)) =
        (vl n h A ρ (wK n h A (enc yv) (2 * (2 ^ l + a)) 0) &&
          vl n h A ρ (wK n h A (enc yv) (2 * (2 ^ l + a) + 1) 1)) :=
      (up_val n h A ρ (enc yv) (2 ^ l + a) 3 hy hv1 hv (by norm_num)).trans rfl
    have e4 : vl n h A ρ (2 + 2 * n + (6 * uq n (enc yv) (2 ^ l + a) + 4)) =
        (vl n h A ρ (wK n h A (enc yv) (2 * (2 ^ l + a)) 1) &&
          vl n h A ρ (wK n h A (enc yv) (2 * (2 ^ l + a) + 1) 0)) :=
      (up_val n h A ρ (enc yv) (2 ^ l + a) 4 hy hv1 hv (by norm_num)).trans rfl
    have e5 : vl n h A ρ (2 + 2 * n + (6 * uq n (enc yv) (2 ^ l + a) + 5)) =
        (vl n h A ρ (2 + 2 * n + (6 * uq n (enc yv) (2 ^ l + a) + 3)) ||
          vl n h A ρ (2 + 2 * n + (6 * uq n (enc yv) (2 ^ l + a) + 4))) :=
      (up_val n h A ρ (enc yv) (2 ^ l + a) 5 hy hv1 hv (by norm_num)).trans rfl
    rcases z2 p with rfl | rfl
    · rw [hw, if_pos h00, e2, e0, e1]
      simp only [Bool.or_eq_true, Bool.and_eq_true, ihL, ihR, hsplit 0, zero_add]
    · rw [hw, if_neg h10, e5, e3, e4]
      simp only [Bool.or_eq_true, Bool.and_eq_true, ihL, ihR, hsplit 1, h11]

-- the outside flag of tree node (l, a): all sites of [0, M) outside its interval
def OFs (ok : ℕ → Prop) (par : ℕ → ZMod 2) (M lo hi : ℕ) (p : ZMod 2) : Prop :=
  (∀ k, (k < lo ∨ hi ≤ k) → k < M → ok k) ∧
    (∑ k ∈ Finset.Ico 0 lo, par k) + (∑ k ∈ Finset.Ico hi M, par k) = p

def OF (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (yv : Fin h → ZMod 2) (l a : ℕ) (p : ZMod 2) : Prop :=
  OFs (okS n h A ρ yv) (parS n h A ρ yv) (MM n) (a * 2 ^ (HH n - l)) ((a + 1) * 2 ^ (HH n - l)) p

theorem OFs_left (ok : ℕ → Prop) (par : ℕ → ZMod 2) (M lo mid hi : ℕ) (p : ZMod 2)
    (h1 : lo ≤ mid) (h2 : mid ≤ hi) (h3 : hi ≤ M) :
    OFs ok par M lo mid p ↔ (OFs ok par M lo hi 0 ∧ Flag ok par mid hi p) ∨
      (OFs ok par M lo hi 1 ∧ Flag ok par mid hi (p + 1)) := by
  have hs : (∑ k ∈ Finset.Ico 0 lo, par k) + (∑ k ∈ Finset.Ico mid M, par k) =
      ((∑ k ∈ Finset.Ico 0 lo, par k) + (∑ k ∈ Finset.Ico hi M, par k)) +
        ∑ k ∈ Finset.Ico mid hi, par k := by
    rw [← Finset.sum_Ico_consecutive par h2 h3]
    ring
  have hall : (∀ k, (k < lo ∨ mid ≤ k) → k < M → ok k) ↔
      (∀ k, (k < lo ∨ hi ≤ k) → k < M → ok k) ∧ (∀ k, mid ≤ k → k < hi → ok k) := by
    constructor
    · intro H
      exact ⟨fun k hk hkM => H k (by omega) hkM, fun k a b => H k (Or.inr a) (by omega)⟩
    · rintro ⟨H1, H2⟩ k hk hkM
      by_cases hkh : k < hi
      · rcases hk with hk | hk
        · exact H1 k (Or.inl hk) hkM
        · exact H2 k hk hkh
      · exact H1 k (Or.inr (by omega)) hkM
  unfold OFs Flag
  rw [hs, hall, comb]

theorem OFs_right (ok : ℕ → Prop) (par : ℕ → ZMod 2) (M lo mid hi : ℕ) (p : ZMod 2)
    (h1 : lo ≤ mid) (h2 : mid ≤ hi) (h3 : hi ≤ M) :
    OFs ok par M mid hi p ↔ (OFs ok par M lo hi 0 ∧ Flag ok par lo mid p) ∨
      (OFs ok par M lo hi 1 ∧ Flag ok par lo mid (p + 1)) := by
  have hs : (∑ k ∈ Finset.Ico 0 mid, par k) + (∑ k ∈ Finset.Ico hi M, par k) =
      ((∑ k ∈ Finset.Ico 0 lo, par k) + (∑ k ∈ Finset.Ico hi M, par k)) +
        ∑ k ∈ Finset.Ico lo mid, par k := by
    rw [← Finset.sum_Ico_consecutive par (Nat.zero_le lo) h1]
    ring
  have hall : (∀ k, (k < mid ∨ hi ≤ k) → k < M → ok k) ↔
      (∀ k, (k < lo ∨ hi ≤ k) → k < M → ok k) ∧ (∀ k, lo ≤ k → k < mid → ok k) := by
    constructor
    · intro H
      exact ⟨fun k hk hkM => H k (by omega) hkM, fun k a b => H k (Or.inl b) (by omega)⟩
    · rintro ⟨H1, H2⟩ k hk hkM
      by_cases hkl : k < lo
      · exact H1 k (Or.inl hkl) hkM
      · rcases hk with hk | hk
        · exact H2 k (by omega) hk
        · exact H1 k (Or.inr hk) hkM
  unfold OFs Flag
  rw [hs, hall, comb]

-- one step down the tree: child = parent outside flag combined with the sibling flag
theorem OF_step (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (yv : Fin h → ZMod 2) (l a : ℕ) (hl : l + 1 ≤ HH n) (ha : a < 2 ^ (l + 1)) (p : ZMod 2) :
    OF n h A ρ yv (l + 1) a p ↔
      (OF n h A ρ yv l (a / 2) 0 ∧ KF n h A ρ yv (l + 1) (sib a) p) ∨
      (OF n h A ρ yv l (a / 2) 1 ∧ KF n h A ρ yv (l + 1) (sib a) (p + 1)) := by
  have hP : 2 ^ (HH n - l) = 2 * 2 ^ (HH n - (l + 1)) := by
    rw [show HH n - l = HH n - (l + 1) + 1 by omega, pow_succ]
    ring
  have h2l : 2 ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
  have hMM : 2 ^ l * 2 ^ (HH n - l) = MM n := by
    unfold MM
    rw [← pow_add]
    congr 1
    omega
  rcases Nat.even_or_odd' a with ⟨c, rfl | rfl⟩
  · have hc : 2 * c / 2 = c := by omega
    have hs : sib (2 * c) = 2 * c + 1 := by
      unfold sib
      split_ifs with hh <;> omega
    have hcl : c + 1 ≤ 2 ^ l := by omega
    have hM : (2 * c + 1 + 1) * 2 ^ (HH n - (l + 1)) ≤ MM n := by
      rw [show (2 * c + 1 + 1) * 2 ^ (HH n - (l + 1)) = (c + 1) * 2 ^ (HH n - l) by rw [hP]; ring,
        ← hMM]
      exact Nat.mul_le_mul_right _ hcl
    unfold OF KF
    rw [hc, hs, hP, show c * (2 * 2 ^ (HH n - (l + 1))) = 2 * c * 2 ^ (HH n - (l + 1)) by ring,
      show (c + 1) * (2 * 2 ^ (HH n - (l + 1))) = (2 * c + 1 + 1) * 2 ^ (HH n - (l + 1)) by ring]
    exact OFs_left _ _ _ _ _ _ p (Nat.mul_le_mul_right _ (by omega))
      (Nat.mul_le_mul_right _ (by omega)) hM
  · have hc : (2 * c + 1) / 2 = c := by omega
    have hs : sib (2 * c + 1) = 2 * c := by
      unfold sib
      split_ifs with hh <;> omega
    have hcl : c + 1 ≤ 2 ^ l := by omega
    have hM : (2 * c + 1 + 1) * 2 ^ (HH n - (l + 1)) ≤ MM n := by
      rw [show (2 * c + 1 + 1) * 2 ^ (HH n - (l + 1)) = (c + 1) * 2 ^ (HH n - l) by rw [hP]; ring,
        ← hMM]
      exact Nat.mul_le_mul_right _ hcl
    unfold OF KF
    rw [hc, hs, hP, show c * (2 * 2 ^ (HH n - (l + 1))) = 2 * c * 2 ^ (HH n - (l + 1)) by ring,
      show (c + 1) * (2 * 2 ^ (HH n - (l + 1))) = (2 * c + 1 + 1) * 2 ^ (HH n - (l + 1)) by ring]
    exact OFs_right _ _ _ _ _ _ p (Nat.mul_le_mul_right _ (by omega))
      (Nat.mul_le_mul_right _ (by omega)) hM

theorem dn_raw (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (y v c : ℕ) (hy : y < 2 ^ h)
    (hv : v < 2 * MM n) (hc : c < 6) :
    rawU n h A (SU n h + (6 * dq n y v + c)) = (upOp c, dnA n h y v c, dnB n h A y v c) := by
  obtain ⟨d1, d2⟩ := dm y v (2 * MM n) hv
  have h6 : (6 * dq n y v + c) / 6 = y * (2 * MM n) + v := by unfold dq; omega
  have h6' : (6 * dq n y v + c) % 6 = c := by omega
  have hlt : 6 * dq n y v + c < SD n h := by
    have := idx_lt y v (2 ^ h) (2 * MM n) hy hv
    unfold SD dq
    omega
  have hnot : ¬ (SU n h + (6 * dq n y v + c) < SU n h) := by omega
  have hlt2 : SU n h + (6 * dq n y v + c) < SU n h + SD n h := by omega
  unfold rawU dnGate
  rw [if_neg hnot, if_pos hlt2, Nat.add_sub_cancel_left, h6', h6, d1, d2]

theorem wK_lt_SU (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (y v : ℕ) (p : ZMod 2) (hy : y < 2 ^ h) :
    wK n h A y v p < 2 + 2 * n + SU n h := by
  unfold wK
  split_ifs with h1 h2
  · have := leafW_lt n h A y (v - MM n) p
    omega
  · have := idx_lt y (MM n - 1 - v) (2 ^ h) (MM n) hy (by omega)
    unfold uq SU
    omega
  · have := idx_lt y (MM n - 1 - v) (2 ^ h) (MM n) hy (by omega)
    unfold uq SU
    omega

theorem dnA_lt (n h : ℕ) (y v c : ℕ) (hv2 : 2 ≤ v) (hc : c < 6) :
    dnA n h y v c < 2 + 2 * n + (SU n h + (6 * dq n y v + c)) := by
  unfold dnA wO dq
  split_ifs <;> omega

theorem dnB_lt (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (y v c : ℕ) (hy : y < 2 ^ h) (hc : c < 6) :
    dnB n h A y v c < 2 + 2 * n + (SU n h + (6 * dq n y v + c)) := by
  unfold dnB
  by_cases h2 : c = 2
  · rw [if_pos h2]
    omega
  · rw [if_neg h2]
    by_cases h5 : c = 5
    · rw [if_pos h5]
      omega
    · rw [if_neg h5]
      have := wK_lt_SU n h A y (sib v) (if c = 0 ∨ c = 4 then 0 else 1) hy
      omega

-- the value of a gate of the down pass
theorem dn_val (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (y v c : ℕ) (hy : y < 2 ^ h) (hv2 : 2 ≤ v) (hv : v < 2 * MM n) (hc : c < 6) :
    vl n h A ρ (2 + 2 * n + (SU n h + (6 * dq n y v + c))) =
      gop (upOp c) (vl n h A ρ (dnA n h y v c)) (vl n h A ρ (dnB n h A y v c)) := by
  have hlt : SU n h + (6 * dq n y v + c) < NN n h := by
    have := idx_lt y v (2 ^ h) (2 * MM n) hy hv
    unfold NN SD dq
    omega
  have hraw := dn_raw n h A y v c hy hv hc
  have hg := gd_eq (2 + 2 * n) (rawU n h A) (SU n h + (6 * dq n y v + c))
    (by rw [hraw]; exact dnA_lt n h y v c hv2 hc) (by rw [hraw]; exact dnB_lt n h A y v c hy hc)
  have := gate_val (2 + 2 * n) (NN n h) (by omega) (rawU n h A) (pinsL n ρ) (pinsL_length n ρ) _ hlt
  rw [hg, hraw] at this
  exact this

theorem sib_lt (l a : ℕ) (ha : a < 2 ^ (l + 1)) : sib a < 2 ^ (l + 1) := by
  have h2l : 2 ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
  unfold sib
  split_ifs <;> omega

-- the down pass computes the outside flag of every node
theorem L_down (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (yv : Fin h → ZMod 2) :
    ∀ l, l ≤ HH n → ∀ a, a < 2 ^ l → ∀ p : ZMod 2,
      (vl n h A ρ (wO n h (enc yv) (2 ^ l + a) p) = true ↔ OF n h A ρ yv l a p) := by
  have h00 : (0 : ZMod 2) = 0 := rfl
  have h10 : ¬ ((1 : ZMod 2) = 0) := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  intro l
  induction l with
  | zero =>
    intro _ a ha p
    rw [pow_zero] at ha
    have ha0 : a = 0 := by omega
    subst ha0
    have hw : wO n h (enc yv) (2 ^ 0 + 0) p = if p = 0 then 1 else 0 := by
      unfold wO
      rw [if_pos (by norm_num)]
    have hOF : OF n h A ρ yv 0 0 p ↔ p = 0 := by
      unfold OF OFs
      have hM : MM n = 2 ^ HH n := rfl
      rw [Nat.sub_zero, zero_mul, zero_add, one_mul, ← hM]
      simp only [Finset.Ico_self, Finset.sum_empty, add_zero]
      constructor
      · rintro ⟨-, hp⟩
        exact hp.symm
      · intro hp
        exact ⟨fun k hk hkM => absurd hkM (by omega), hp.symm⟩
    rw [hw, hOF]
    unfold vl
    rcases z2 p with rfl | rfl
    · rw [if_pos h00, wl_getD_lt gop false _ _ _ (by rw [pinsL_length]; omega), pinsL_one]
      simp
    · rw [if_neg h10, wl_getD_lt gop false _ _ _ (by rw [pinsL_length]; omega), pinsL_zero]
      simp
  | succ l ih =>
    intro hl a ha p
    have hl' : l ≤ HH n := by omega
    have h2l : 2 ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
    have hpos : 0 < 2 ^ l := pow_pos (by norm_num) l
    have hMM : 2 ^ (l + 1) ≤ MM n := by
      unfold MM
      exact Nat.pow_le_pow_right (by norm_num) hl
    have hv2 : 2 ≤ 2 ^ (l + 1) + a := by omega
    have hv : 2 ^ (l + 1) + a < 2 * MM n := by omega
    have hy : enc yv < 2 ^ h := enc_lt yv
    have hpar : (2 ^ (l + 1) + a) / 2 = 2 ^ l + a / 2 := by omega
    have hsib : sib (2 ^ (l + 1) + a) = 2 ^ (l + 1) + sib a := by
      unfold sib
      split_ifs with h1 h2 h2 <;> omega
    have ihP := ih hl' (a / 2) (by omega)
    rw [← hpar] at ihP
    have hK := L_up n h A ρ yv (HH n - (l + 1)) (l + 1) (sib a) (by omega) (sib_lt l a ha)
    rw [← hsib] at hK
    have hnot : ¬ (2 ^ (l + 1) + a ≤ 1) := by omega
    have hw : ∀ q : ZMod 2, wO n h (enc yv) (2 ^ (l + 1) + a) q =
        2 + 2 * n + (SU n h + (6 * dq n (enc yv) (2 ^ (l + 1) + a) + (if q = 0 then 2 else 5))) := by
      intro q
      unfold wO
      rw [if_neg hnot]
    have e0 : vl n h A ρ (2 + 2 * n + (SU n h + (6 * dq n (enc yv) (2 ^ (l + 1) + a) + 0))) =
        (vl n h A ρ (wO n h (enc yv) ((2 ^ (l + 1) + a) / 2) 0) &&
          vl n h A ρ (wK n h A (enc yv) (sib (2 ^ (l + 1) + a)) 0)) :=
      (dn_val n h A ρ (enc yv) (2 ^ (l + 1) + a) 0 hy hv2 hv (by norm_num)).trans rfl
    have e1 : vl n h A ρ (2 + 2 * n + (SU n h + (6 * dq n (enc yv) (2 ^ (l + 1) + a) + 1))) =
        (vl n h A ρ (wO n h (enc yv) ((2 ^ (l + 1) + a) / 2) 1) &&
          vl n h A ρ (wK n h A (enc yv) (sib (2 ^ (l + 1) + a)) 1)) :=
      (dn_val n h A ρ (enc yv) (2 ^ (l + 1) + a) 1 hy hv2 hv (by norm_num)).trans rfl
    have e2 : vl n h A ρ (2 + 2 * n + (SU n h + (6 * dq n (enc yv) (2 ^ (l + 1) + a) + 2))) =
        (vl n h A ρ (2 + 2 * n + (SU n h + (6 * dq n (enc yv) (2 ^ (l + 1) + a) + 0))) ||
          vl n h A ρ (2 + 2 * n + (SU n h + (6 * dq n (enc yv) (2 ^ (l + 1) + a) + 1)))) :=
      (dn_val n h A ρ (enc yv) (2 ^ (l + 1) + a) 2 hy hv2 hv (by norm_num)).trans rfl
    have e3 : vl n h A ρ (2 + 2 * n + (SU n h + (6 * dq n (enc yv) (2 ^ (l + 1) + a) + 3))) =
        (vl n h A ρ (wO n h (enc yv) ((2 ^ (l + 1) + a) / 2) 0) &&
          vl n h A ρ (wK n h A (enc yv) (sib (2 ^ (l + 1) + a)) 1)) :=
      (dn_val n h A ρ (enc yv) (2 ^ (l + 1) + a) 3 hy hv2 hv (by norm_num)).trans rfl
    have e4 : vl n h A ρ (2 + 2 * n + (SU n h + (6 * dq n (enc yv) (2 ^ (l + 1) + a) + 4))) =
        (vl n h A ρ (wO n h (enc yv) ((2 ^ (l + 1) + a) / 2) 1) &&
          vl n h A ρ (wK n h A (enc yv) (sib (2 ^ (l + 1) + a)) 0)) :=
      (dn_val n h A ρ (enc yv) (2 ^ (l + 1) + a) 4 hy hv2 hv (by norm_num)).trans rfl
    have e5 : vl n h A ρ (2 + 2 * n + (SU n h + (6 * dq n (enc yv) (2 ^ (l + 1) + a) + 5))) =
        (vl n h A ρ (2 + 2 * n + (SU n h + (6 * dq n (enc yv) (2 ^ (l + 1) + a) + 3))) ||
          vl n h A ρ (2 + 2 * n + (SU n h + (6 * dq n (enc yv) (2 ^ (l + 1) + a) + 4)))) :=
      (dn_val n h A ρ (enc yv) (2 ^ (l + 1) + a) 5 hy hv2 hv (by norm_num)).trans rfl
    rcases z2 p with rfl | rfl
    · rw [hw, if_pos h00, e2, e0, e1]
      simp only [Bool.or_eq_true, Bool.and_eq_true, ihP, hK,
        OF_step n h A ρ yv l a hl ha 0, zero_add]
    · rw [hw, if_neg h10, e5, e3, e4]
      simp only [Bool.or_eq_true, Bool.and_eq_true, ihP, hK,
        OF_step n h A ρ yv l a hl ha 1, h11]

theorem wO_lt (n h : ℕ) (z v : ℕ) (p : ZMod 2) (hz : z < 2 ^ h) (hv : v < 2 * MM n) :
    wO n h z v p < 2 + 2 * n + (SU n h + SD n h) := by
  have := idx_lt z v (2 ^ h) (2 * MM n) hz hv
  unfold wO dq SD
  split_ifs <;> omega

theorem bf_raw (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (t τ z : ℕ) (e : ZMod 2) (ht : t < h)
    (hτ : τ < TT n) (hz : z < 2 ^ h) :
    rawU n h A (SU n h + SD n h + (2 * bq n h t τ z + e.val)) =
      (false, wF n h A t τ (enc (bset (yvec h z) t 0)) e,
        wF n h A t τ (enc (bset (yvec h z) t 1)) (e + dig z t)) := by
  have he : e.val < 2 := ZMod.val_lt e
  obtain ⟨d1, d2⟩ := dm (t * TT n + τ) z (2 ^ h) hz
  obtain ⟨d3, d4⟩ := dm t τ (TT n) hτ
  have h2 : (2 * bq n h t τ z + e.val) / 2 = (t * TT n + τ) * 2 ^ h + z := by unfold bq; omega
  have h2' : (2 * bq n h t τ z + e.val) % 2 = e.val := by omega
  have hev : ((e.val : ℕ) : ZMod 2) = e := ZMod.natCast_zmod_val e
  have hb1 : t * TT n + τ < h * TT n := idx_lt t τ h (TT n) ht hτ
  have hb2 : (t * TT n + τ) * 2 ^ h + z < h * TT n * 2 ^ h := idx_lt _ z _ _ hb1 hz
  have hnot1 : ¬ (SU n h + SD n h + (2 * bq n h t τ z + e.val) < SU n h) := by omega
  have hnot2 : ¬ (SU n h + SD n h + (2 * bq n h t τ z + e.val) < SU n h + SD n h) := by omega
  have hlt3 : SU n h + SD n h + (2 * bq n h t τ z + e.val) < SU n h + SD n h + SB n h := by
    unfold SB bq
    omega
  unfold rawU bfGate
  rw [if_neg hnot1, if_neg hnot2, if_pos hlt3, Nat.add_sub_cancel_left, h2', h2, d1, d2, d3, d4, hev]

theorem wF_lt (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (t τ z z' : ℕ) (e e' : ZMod 2)
    (hτ : τ < TT n) (hz' : z' < 2 ^ h) :
    wF n h A t τ z' e' < 2 + 2 * n + (SU n h + SD n h + (2 * bq n h t τ z + e.val)) := by
  unfold wF
  by_cases ht0 : t = 0
  · rw [if_pos ht0]
    unfold wG
    by_cases hτ2 : τ = 2 * n
    · rw [if_pos hτ2]
      have := wK_lt_SU n h A z' 1 (e' + 1) hz'
      omega
    · rw [if_neg hτ2]
      have hM := M_ge n
      have hMM : MM n = 2 ^ Nat.clog 2 (n + 1) := rfl
      have hT : TT n = 2 * n + 1 := rfl
      have := wO_lt n h z' (MM n + τ / 2)
        (e' + 1 + ((τ % 2 : ℕ) : ZMod 2) * cf n h A (yvec h z') (τ / 2)) hz' (by omega)
      omega
  · rw [if_neg ht0]
    have hT : 1 ≤ TT n := by unfold TT; omega
    have he' : e'.val < 2 := ZMod.val_lt e'
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have h1 := idx_lt (t' * TT n + τ) z' (t' * TT n + τ + 1) (2 ^ h) (Nat.lt_succ_self _) hz'
    have h2 : (t' * TT n + τ + 1) * 2 ^ h ≤ ((t' + 1) * TT n + τ) * 2 ^ h := by
      apply Nat.mul_le_mul_right
      have : (t' + 1) * TT n = t' * TT n + TT n := by ring
      omega
    unfold bq
    rw [Nat.add_sub_cancel]
    omega

-- the value of a butterfly gate
theorem bf_val (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool) (t τ z : ℕ)
    (e : ZMod 2) (ht : t < h) (hτ : τ < TT n) (hz : z < 2 ^ h) :
    vl n h A ρ (2 + 2 * n + (SU n h + SD n h + (2 * bq n h t τ z + e.val))) =
      (vl n h A ρ (wF n h A t τ (enc (bset (yvec h z) t 0)) e) ||
        vl n h A ρ (wF n h A t τ (enc (bset (yvec h z) t 1)) (e + dig z t))) := by
  have he : e.val < 2 := ZMod.val_lt e
  have hb1 : t * TT n + τ < h * TT n := idx_lt t τ h (TT n) ht hτ
  have hb2 : (t * TT n + τ) * 2 ^ h + z < h * TT n * 2 ^ h := idx_lt _ z _ _ hb1 hz
  have hlt : SU n h + SD n h + (2 * bq n h t τ z + e.val) < NN n h := by
    unfold NN SB bq
    omega
  have hraw := bf_raw n h A t τ z e ht hτ hz
  have hg := gd_eq (2 + 2 * n) (rawU n h A) (SU n h + SD n h + (2 * bq n h t τ z + e.val))
    (by rw [hraw]; exact wF_lt n h A t τ z _ e _ hτ (enc_lt _))
    (by rw [hraw]; exact wF_lt n h A t τ z _ e _ hτ (enc_lt _))
  have := gate_val (2 + 2 * n) (NN n h) (by omega) (rawU n h A) (pinsL n ρ) (pinsL_length n ρ)
    (SU n h + SD n h + (2 * bq n h t τ z + e.val)) hlt
  rw [hg, hraw] at this
  exact this

-- what the butterfly input of target τ says about row combination yv with sign e
def GP (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool) (τ : ℕ)
    (yv : Fin h → ZMod 2) (e : ZMod 2) : Prop :=
  if τ = 2 * n then KF n h A ρ yv 0 0 (e + 1)
  else OF n h A ρ yv (HH n) (τ / 2) (e + 1 + ((τ % 2 : ℕ) : ZMod 2) * cf n h A yv (τ / 2))

-- the butterflies send every certificate to every syndrome
theorem L_bfly (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool) :
    ∀ t, t ≤ h → ∀ τ, τ < TT n → ∀ (zv : Fin h → ZMod 2) (e : ZMod 2),
      (vl n h A ρ (wF n h A t τ (enc zv) e) = true ↔ BF (GP n h A ρ τ) t zv e) := by
  intro t
  induction t with
  | zero =>
    intro _ τ hτ zv e
    rw [BF_zero]
    unfold wF GP
    rw [if_pos (rfl : (0 : ℕ) = 0)]
    unfold wG
    by_cases hτ2 : τ = 2 * n
    · rw [if_pos hτ2, if_pos hτ2]
      exact L_up n h A ρ zv (HH n) 0 0 (by omega) (by norm_num) (e + 1)
    · rw [if_neg hτ2, if_neg hτ2, yvec_enc]
      have hM := M_ge n
      have hMM : MM n = 2 ^ Nat.clog 2 (n + 1) := rfl
      have hT : TT n = 2 * n + 1 := rfl
      have hlt : τ / 2 < 2 ^ HH n := by
        unfold HH
        omega
      exact L_down n h A ρ zv (HH n) le_rfl (τ / 2) hlt _
  | succ t ih =>
    intro ht τ hτ zv e
    have htl : t < h := by omega
    rw [BF_succ _ t htl zv e]
    have hw : wF n h A (t + 1) τ (enc zv) e =
        2 + 2 * n + (SU n h + SD n h + (2 * bq n h t τ (enc zv) + e.val)) := by
      unfold wF
      rw [if_neg (Nat.succ_ne_zero t), Nat.add_sub_cancel]
    have hd : dig (enc zv) t = zv ⟨t, htl⟩ := congrFun (yvec_enc zv) ⟨t, htl⟩
    rw [hw, bf_val n h A ρ t τ (enc zv) e htl hτ (enc_lt zv), yvec_enc, hd, Bool.or_eq_true,
      ih (by omega) τ hτ _ e, ih (by omega) τ hτ _ _]

-- section dep

-- the depth of wire k in the gate list GU (the depths fold of the statement)
def dep (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (k : ℕ) : ℕ :=
  (wl dop 0 (GU n h A) (List.replicate (2 + 2 * n) 0)).getD k 0

-- input wires have depth 0
theorem dep_in (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (k : ℕ) (hk : k < 2 + 2 * n) :
    dep n h A k = 0 := by
  have h1 := wl_getD_lt dop 0 (GU n h A) (List.replicate (2 + 2 * n) 0) k
    (by rw [List.length_replicate]; exact hk)
  have h2 : (List.replicate (2 + 2 * n) (0 : ℕ)).getD k 0 = 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate_of_lt hk]
    rfl
  exact h1.trans h2

-- one gate on top of two wires of depth at most c
theorem dep_max (a b c : ℕ) (ha : a ≤ c) (hb : b ≤ c) : max a b + 1 ≤ c + 1 := by
  have hm : max a b ≤ c := Nat.max_le_of_le_of_le ha hb
  exact Nat.add_le_add_right hm 1

-- the depth of a gate of the up pass
theorem up_dep (n h : ℕ) (A : Fin h → Fin n → ZMod 2)
    (y v c : ℕ) (hy : y < 2 ^ h) (hv1 : 1 ≤ v) (hv : v < MM n) (hc : c < 6) :
    dep n h A (2 + 2 * n + (6 * uq n y v + c)) =
      max (dep n h A (upA n h A y v c)) (dep n h A (upB n h A y v c)) + 1 := by
  have hr : MM n - 1 - v < MM n := by omega
  have hlt : 6 * uq n y v + c < SU n h := by
    have := idx_lt y (MM n - 1 - v) (2 ^ h) (MM n) hy hr
    unfold SU uq
    omega
  have hraw := up_raw n h A y v c hy hv hc
  have hg := gd_eq (2 + 2 * n) (rawU n h A) (6 * uq n y v + c)
    (by rw [hraw]; exact upA_lt n h A y v c hv1 hc) (by rw [hraw]; exact upB_lt n h A y v c hv1 hc)
  have := gate_dep (2 + 2 * n) (NN n h) (by omega) (rawU n h A) (List.replicate (2 + 2 * n) 0)
    List.length_replicate (6 * uq n y v + c) (by unfold NN; omega)
  rw [hg, hraw] at this
  exact this

-- the up pass: the flag wires of a node of level l have depth at most 2 (H - l)
theorem L_up_dep (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (y : ℕ) (hy : y < 2 ^ h) :
    ∀ m l a, l + m = HH n → a < 2 ^ l → ∀ p : ZMod 2,
      dep n h A (wK n h A y (2 ^ l + a) p) ≤ 2 * m := by
  have h00 : (0 : ZMod 2) = 0 := rfl
  have h10 : ¬ ((1 : ZMod 2) = 0) := by decide
  intro m
  induction m with
  | zero =>
    intro l a hl ha p
    have hl' : l = HH n := by omega
    subst hl'
    have hv : MM n ≤ 2 ^ HH n + a := by unfold MM; omega
    unfold wK
    rw [if_pos hv]
    exact Nat.le_trans (Nat.le_of_eq (dep_in n h A (leafW n h A y (2 ^ HH n + a - MM n) p)
      (leafW_lt n h A y (2 ^ HH n + a - MM n) p))) (Nat.zero_le _)
  | succ m ih =>
    intro l a hl ha p
    have hlt : l < HH n := by omega
    have hpow : 2 ^ (l + 1) ≤ MM n := by
      unfold MM
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2l : 2 ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
    have hpos : 0 < 2 ^ l := pow_pos (by norm_num) l
    have hv : 2 ^ l + a < MM n := by omega
    have hv1 : 1 ≤ 2 ^ l + a := by omega
    have hc0 : 2 * (2 ^ l + a) = 2 ^ (l + 1) + 2 * a := by rw [h2l]; ring
    have hc1 : 2 * (2 ^ l + a) + 1 = 2 ^ (l + 1) + (2 * a + 1) := by rw [h2l]; ring
    have ihL : ∀ q : ZMod 2, dep n h A (wK n h A y (2 * (2 ^ l + a)) q) ≤ 2 * m := by
      intro q
      rw [hc0]
      exact ih (l + 1) (2 * a) (by omega) (by omega) q
    have ihR : ∀ q : ZMod 2, dep n h A (wK n h A y (2 * (2 ^ l + a) + 1) q) ≤ 2 * m := by
      intro q
      rw [hc1]
      exact ih (l + 1) (2 * a + 1) (by omega) (by omega) q
    have hnot : ¬ (MM n ≤ 2 ^ l + a) := by omega
    have hw : ∀ q : ZMod 2, wK n h A y (2 ^ l + a) q =
        2 + 2 * n + (6 * uq n y (2 ^ l + a) + (if q = 0 then 2 else 5)) := by
      intro q
      unfold wK
      rw [if_neg hnot]
    have e0 : dep n h A (2 + 2 * n + (6 * uq n y (2 ^ l + a) + 0)) =
        max (dep n h A (wK n h A y (2 * (2 ^ l + a)) 0))
          (dep n h A (wK n h A y (2 * (2 ^ l + a) + 1) 0)) + 1 :=
      (up_dep n h A y (2 ^ l + a) 0 hy hv1 hv (by norm_num)).trans rfl
    have e1 : dep n h A (2 + 2 * n + (6 * uq n y (2 ^ l + a) + 1)) =
        max (dep n h A (wK n h A y (2 * (2 ^ l + a)) 1))
          (dep n h A (wK n h A y (2 * (2 ^ l + a) + 1) 1)) + 1 :=
      (up_dep n h A y (2 ^ l + a) 1 hy hv1 hv (by norm_num)).trans rfl
    have e2 : dep n h A (2 + 2 * n + (6 * uq n y (2 ^ l + a) + 2)) =
        max (dep n h A (2 + 2 * n + (6 * uq n y (2 ^ l + a) + 0)))
          (dep n h A (2 + 2 * n + (6 * uq n y (2 ^ l + a) + 1))) + 1 :=
      (up_dep n h A y (2 ^ l + a) 2 hy hv1 hv (by norm_num)).trans rfl
    have e3 : dep n h A (2 + 2 * n + (6 * uq n y (2 ^ l + a) + 3)) =
        max (dep n h A (wK n h A y (2 * (2 ^ l + a)) 0))
          (dep n h A (wK n h A y (2 * (2 ^ l + a) + 1) 1)) + 1 :=
      (up_dep n h A y (2 ^ l + a) 3 hy hv1 hv (by norm_num)).trans rfl
    have e4 : dep n h A (2 + 2 * n + (6 * uq n y (2 ^ l + a) + 4)) =
        max (dep n h A (wK n h A y (2 * (2 ^ l + a)) 1))
          (dep n h A (wK n h A y (2 * (2 ^ l + a) + 1) 0)) + 1 :=
      (up_dep n h A y (2 ^ l + a) 4 hy hv1 hv (by norm_num)).trans rfl
    have e5 : dep n h A (2 + 2 * n + (6 * uq n y (2 ^ l + a) + 5)) =
        max (dep n h A (2 + 2 * n + (6 * uq n y (2 ^ l + a) + 3)))
          (dep n h A (2 + 2 * n + (6 * uq n y (2 ^ l + a) + 4))) + 1 :=
      (up_dep n h A y (2 ^ l + a) 5 hy hv1 hv (by norm_num)).trans rfl
    rcases z2 p with rfl | rfl
    · rw [hw, if_pos h00, e2, e0, e1]
      exact Nat.le_trans (dep_max _ _ _ (dep_max _ _ _ (ihL 0) (ihR 0))
        (dep_max _ _ _ (ihL 1) (ihR 1))) (by omega)
    · rw [hw, if_neg h10, e5, e3, e4]
      exact Nat.le_trans (dep_max _ _ _ (dep_max _ _ _ (ihL 0) (ihR 1))
        (dep_max _ _ _ (ihL 1) (ihR 0))) (by omega)

-- the same bound in the form 2 (H - l)
theorem dep_wK (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (y l a : ℕ) (hy : y < 2 ^ h)
    (hl : l ≤ HH n) (ha : a < 2 ^ l) (p : ZMod 2) :
    dep n h A (wK n h A y (2 ^ l + a) p) ≤ 2 * (HH n - l) :=
  L_up_dep n h A y hy (HH n - l) l a (by omega) ha p

-- the depth of a gate of the down pass
theorem dn_dep (n h : ℕ) (A : Fin h → Fin n → ZMod 2)
    (y v c : ℕ) (hy : y < 2 ^ h) (hv2 : 2 ≤ v) (hv : v < 2 * MM n) (hc : c < 6) :
    dep n h A (2 + 2 * n + (SU n h + (6 * dq n y v + c))) =
      max (dep n h A (dnA n h y v c)) (dep n h A (dnB n h A y v c)) + 1 := by
  have hlt : SU n h + (6 * dq n y v + c) < NN n h := by
    have := idx_lt y v (2 ^ h) (2 * MM n) hy hv
    unfold NN SD dq
    omega
  have hraw := dn_raw n h A y v c hy hv hc
  have hg := gd_eq (2 + 2 * n) (rawU n h A) (SU n h + (6 * dq n y v + c))
    (by rw [hraw]; exact dnA_lt n h y v c hv2 hc) (by rw [hraw]; exact dnB_lt n h A y v c hy hc)
  have := gate_dep (2 + 2 * n) (NN n h) (by omega) (rawU n h A) (List.replicate (2 + 2 * n) 0)
    List.length_replicate (SU n h + (6 * dq n y v + c)) hlt
  rw [hg, hraw] at this
  exact this

-- the down pass: the outside flag wires of a node of level l have depth at most 2 H + 2 l
theorem L_down_dep (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (y : ℕ) (hy : y < 2 ^ h) :
    ∀ l, l ≤ HH n → ∀ a, a < 2 ^ l → ∀ p : ZMod 2,
      dep n h A (wO n h y (2 ^ l + a) p) ≤ 2 * HH n + 2 * l := by
  have h00 : (0 : ZMod 2) = 0 := rfl
  have h10 : ¬ ((1 : ZMod 2) = 0) := by decide
  intro l
  induction l with
  | zero =>
    intro _ a ha p
    rw [pow_zero] at ha
    have ha0 : a = 0 := by omega
    subst ha0
    have hw : wO n h y (2 ^ 0 + 0) p = if p = 0 then 1 else 0 := by
      unfold wO
      rw [if_pos (by norm_num)]
    rw [hw]
    rcases z2 p with rfl | rfl
    · rw [if_pos h00]
      exact Nat.le_trans (Nat.le_of_eq (dep_in n h A 1 (by omega))) (Nat.zero_le _)
    · rw [if_neg h10]
      exact Nat.le_trans (Nat.le_of_eq (dep_in n h A 0 (by omega))) (Nat.zero_le _)
  | succ l ih =>
    intro hl a ha p
    have hl' : l ≤ HH n := by omega
    have h2l : 2 ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
    have hpos : 0 < 2 ^ l := pow_pos (by norm_num) l
    have hMM : 2 ^ (l + 1) ≤ MM n := by
      unfold MM
      exact Nat.pow_le_pow_right (by norm_num) hl
    have hv2 : 2 ≤ 2 ^ (l + 1) + a := by omega
    have hv : 2 ^ (l + 1) + a < 2 * MM n := by omega
    have hpar : (2 ^ (l + 1) + a) / 2 = 2 ^ l + a / 2 := by omega
    have hsib : sib (2 ^ (l + 1) + a) = 2 ^ (l + 1) + sib a := by
      unfold sib
      split_ifs with h1 h2 h2 <;> omega
    have ihP : ∀ q : ZMod 2, dep n h A (wO n h y ((2 ^ (l + 1) + a) / 2) q) ≤
        2 * HH n + 2 * l := by
      intro q
      rw [hpar]
      exact ih hl' (a / 2) (by omega) q
    have hK : ∀ q : ZMod 2, dep n h A (wK n h A y (sib (2 ^ (l + 1) + a)) q) ≤
        2 * HH n + 2 * l := by
      intro q
      rw [hsib]
      exact Nat.le_trans (L_up_dep n h A y hy (HH n - (l + 1)) (l + 1) (sib a) (by omega)
        (sib_lt l a ha) q) (by omega)
    have hnot : ¬ (2 ^ (l + 1) + a ≤ 1) := by omega
    have hw : ∀ q : ZMod 2, wO n h y (2 ^ (l + 1) + a) q =
        2 + 2 * n + (SU n h + (6 * dq n y (2 ^ (l + 1) + a) + (if q = 0 then 2 else 5))) := by
      intro q
      unfold wO
      rw [if_neg hnot]
    have e0 : dep n h A (2 + 2 * n + (SU n h + (6 * dq n y (2 ^ (l + 1) + a) + 0))) =
        max (dep n h A (wO n h y ((2 ^ (l + 1) + a) / 2) 0))
          (dep n h A (wK n h A y (sib (2 ^ (l + 1) + a)) 0)) + 1 :=
      (dn_dep n h A y (2 ^ (l + 1) + a) 0 hy hv2 hv (by norm_num)).trans rfl
    have e1 : dep n h A (2 + 2 * n + (SU n h + (6 * dq n y (2 ^ (l + 1) + a) + 1))) =
        max (dep n h A (wO n h y ((2 ^ (l + 1) + a) / 2) 1))
          (dep n h A (wK n h A y (sib (2 ^ (l + 1) + a)) 1)) + 1 :=
      (dn_dep n h A y (2 ^ (l + 1) + a) 1 hy hv2 hv (by norm_num)).trans rfl
    have e2 : dep n h A (2 + 2 * n + (SU n h + (6 * dq n y (2 ^ (l + 1) + a) + 2))) =
        max (dep n h A (2 + 2 * n + (SU n h + (6 * dq n y (2 ^ (l + 1) + a) + 0))))
          (dep n h A (2 + 2 * n + (SU n h + (6 * dq n y (2 ^ (l + 1) + a) + 1)))) + 1 :=
      (dn_dep n h A y (2 ^ (l + 1) + a) 2 hy hv2 hv (by norm_num)).trans rfl
    have e3 : dep n h A (2 + 2 * n + (SU n h + (6 * dq n y (2 ^ (l + 1) + a) + 3))) =
        max (dep n h A (wO n h y ((2 ^ (l + 1) + a) / 2) 0))
          (dep n h A (wK n h A y (sib (2 ^ (l + 1) + a)) 1)) + 1 :=
      (dn_dep n h A y (2 ^ (l + 1) + a) 3 hy hv2 hv (by norm_num)).trans rfl
    have e4 : dep n h A (2 + 2 * n + (SU n h + (6 * dq n y (2 ^ (l + 1) + a) + 4))) =
        max (dep n h A (wO n h y ((2 ^ (l + 1) + a) / 2) 1))
          (dep n h A (wK n h A y (sib (2 ^ (l + 1) + a)) 0)) + 1 :=
      (dn_dep n h A y (2 ^ (l + 1) + a) 4 hy hv2 hv (by norm_num)).trans rfl
    have e5 : dep n h A (2 + 2 * n + (SU n h + (6 * dq n y (2 ^ (l + 1) + a) + 5))) =
        max (dep n h A (2 + 2 * n + (SU n h + (6 * dq n y (2 ^ (l + 1) + a) + 3))))
          (dep n h A (2 + 2 * n + (SU n h + (6 * dq n y (2 ^ (l + 1) + a) + 4)))) + 1 :=
      (dn_dep n h A y (2 ^ (l + 1) + a) 5 hy hv2 hv (by norm_num)).trans rfl
    rcases z2 p with rfl | rfl
    · rw [hw, if_pos h00, e2, e0, e1]
      exact Nat.le_trans (dep_max _ _ _ (dep_max _ _ _ (ihP 0) (hK 0))
        (dep_max _ _ _ (ihP 1) (hK 1))) (by omega)
    · rw [hw, if_neg h10, e5, e3, e4]
      exact Nat.le_trans (dep_max _ _ _ (dep_max _ _ _ (ihP 0) (hK 1))
        (dep_max _ _ _ (ihP 1) (hK 0))) (by omega)

-- the depth of a butterfly gate
theorem bf_dep (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (t τ z : ℕ)
    (e : ZMod 2) (ht : t < h) (hτ : τ < TT n) (hz : z < 2 ^ h) :
    dep n h A (2 + 2 * n + (SU n h + SD n h + (2 * bq n h t τ z + e.val))) =
      max (dep n h A (wF n h A t τ (enc (bset (yvec h z) t 0)) e))
        (dep n h A (wF n h A t τ (enc (bset (yvec h z) t 1)) (e + dig z t))) + 1 := by
  have he : e.val < 2 := ZMod.val_lt e
  have hb1 : t * TT n + τ < h * TT n := idx_lt t τ h (TT n) ht hτ
  have hb2 : (t * TT n + τ) * 2 ^ h + z < h * TT n * 2 ^ h := idx_lt _ z _ _ hb1 hz
  have hlt : SU n h + SD n h + (2 * bq n h t τ z + e.val) < NN n h := by
    unfold NN SB bq
    omega
  have hraw := bf_raw n h A t τ z e ht hτ hz
  have hg := gd_eq (2 + 2 * n) (rawU n h A) (SU n h + SD n h + (2 * bq n h t τ z + e.val))
    (by rw [hraw]; exact wF_lt n h A t τ z _ e _ hτ (enc_lt _))
    (by rw [hraw]; exact wF_lt n h A t τ z _ e _ hτ (enc_lt _))
  have := gate_dep (2 + 2 * n) (NN n h) (by omega) (rawU n h A) (List.replicate (2 + 2 * n) 0)
    List.length_replicate (SU n h + SD n h + (2 * bq n h t τ z + e.val)) hlt
  rw [hg, hraw] at this
  exact this

-- the butterflies: a wire of level t has depth at most 4 H + t
theorem L_bfly_dep (n h : ℕ) (A : Fin h → Fin n → ZMod 2) :
    ∀ t, t ≤ h → ∀ τ, τ < TT n → ∀ z, z < 2 ^ h → ∀ e : ZMod 2,
      dep n h A (wF n h A t τ z e) ≤ 4 * HH n + t := by
  intro t
  induction t with
  | zero =>
    intro _ τ hτ z hz e
    unfold wF
    rw [if_pos (rfl : (0 : ℕ) = 0)]
    unfold wG
    by_cases hτ2 : τ = 2 * n
    · rw [if_pos hτ2]
      have h1 : dep n h A (wK n h A z 1 (e + 1)) ≤ 2 * HH n :=
        L_up_dep n h A z hz (HH n) 0 0 (by omega) (by norm_num) (e + 1)
      exact Nat.le_trans h1 (by omega)
    · rw [if_neg hτ2]
      have hM := M_ge n
      have hT : TT n = 2 * n + 1 := rfl
      have hlt : τ / 2 < 2 ^ HH n := by
        unfold HH
        omega
      have h1 : ∀ q : ZMod 2, dep n h A (wO n h z (MM n + τ / 2) q) ≤ 2 * HH n + 2 * HH n :=
        fun q => L_down_dep n h A z hz (HH n) le_rfl (τ / 2) hlt q
      exact Nat.le_trans (h1 _) (by omega)
  | succ t ih =>
    intro ht τ hτ z hz e
    have htl : t < h := by omega
    have hw : wF n h A (t + 1) τ z e =
        2 + 2 * n + (SU n h + SD n h + (2 * bq n h t τ z + e.val)) := by
      unfold wF
      rw [if_neg (Nat.succ_ne_zero t), Nat.add_sub_cancel]
    rw [hw, bf_dep n h A t τ z e htl hτ hz]
    have h0 := ih (by omega) τ hτ (enc (bset (yvec h z) t 0)) (enc_lt _) e
    have h1 := ih (by omega) τ hτ (enc (bset (yvec h z) t 1)) (enc_lt _) (e + dig z t)
    exact Nat.le_trans (dep_max _ _ _ h0 h1) (by omega)

-- the dead wire of syndrome s meets the depth bound of the statement
theorem dep_dead (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (s : Fin h → ZMod 2) :
    dep n h A (wF n h A h (2 * n) (enc s) 0) ≤ 16 * (h + Nat.clog 2 (n + 1) + 1) := by
  have h1 := L_bfly_dep n h A h le_rfl (2 * n) (by unfold TT; omega) (enc s) (enc_lt s) 0
  have h2 : HH n = Nat.clog 2 (n + 1) := rfl
  exact Nat.le_trans h1 (by omega)

-- section C
-- the final OR gates: gate tau * Y + z of this section is OR(pin wire, wF h tau z 0), where for
-- tau = 2 i + b the pin wire is the input wire of rho i = some (!b)
def SC (n h : ℕ) : ℕ := 2 * n * 2 ^ h

-- the pin wire of rho i = some (!b) for tau = 2 i + b: b = 0 reads some true, b = 1 reads some false
def pinC (n τ : ℕ) : ℕ := if τ % 2 = 0 then 2 + n + τ / 2 else 2 + τ / 2

def cfGate (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (j : ℕ) : Bool × ℕ × ℕ :=
  (false, pinC n (j / 2 ^ h), wF n h A h (j / 2 ^ h) (j % 2 ^ h) 0)

-- all four sections: up pass, down pass, butterflies, final ORs
def rawC (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (j : ℕ) : Bool × ℕ × ℕ :=
  if j < NN n h then rawU n h A j
  else if j < NN n h + SC n h then cfGate n h A (j - NN n h)
  else (true, 0, 0)

-- the number of gates of the whole circuit
def NC (n h : ℕ) : ℕ := NN n h + SC n h

-- the whole circuit, its wire values and its wire depths
def GC (n h : ℕ) (A : Fin h → Fin n → ZMod 2) : List (Bool × ℕ × ℕ) :=
  glist (2 + 2 * n) (NC n h) (rawC n h A)

def vC (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool) (k : ℕ) : Bool :=
  (wl gop false (GC n h A) (pinsL n ρ)).getD k false

def dC (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (k : ℕ) : ℕ :=
  (wl dop 0 (GC n h A) (List.replicate (2 + 2 * n) 0)).getD k 0

-- the wire of final OR gate (tau, z), that is W0 + (SU + SD + SB + (tau * Y + z));
-- excludeBit s (i, b) is wC (2 i + b.toNat) (enc s)
def wC (n h τ z : ℕ) : ℕ := 2 + 2 * n + (NN n h + (τ * 2 ^ h + z))

theorem cpos_lt (n h τ z : ℕ) (hτ : τ < 2 * n) (hz : z < 2 ^ h) : τ * 2 ^ h + z < SC n h :=
  idx_lt τ z (2 * n) (2 ^ h) hτ hz

theorem pinC_lt (n τ : ℕ) (hτ : τ < 2 * n) : pinC n τ < 2 + 2 * n := by
  unfold pinC
  split_ifs <;> omega

-- the pin wire of target 2 i + b carries rho i = some (!b)
theorem pinC_val (n : ℕ) (ρ : Fin n → Option Bool) (i : Fin n) (b : Bool) :
    (pinsL n ρ).getD (pinC n (2 * i.val + b.toNat)) false = decide (ρ i = some (!b)) := by
  have hi : i.val < n := i.isLt
  cases b
  · have h0 : Bool.toNat false = 0 := rfl
    have hp : pinC n (2 * i.val + Bool.toNat false) = 2 + n + i.val := by
      unfold pinC
      rw [h0]
      split_ifs <;> omega
    rw [hp, pinsL_hi n ρ i.val hi]
    rfl
  · have h1 : Bool.toNat true = 1 := rfl
    have hp : pinC n (2 * i.val + Bool.toNat true) = 2 + i.val := by
      unfold pinC
      rw [h1]
      split_ifs <;> omega
    rw [hp, pinsL_lo n ρ i.val hi]
    rfl

-- decode by Y: the gate at an encoded position of the final section
theorem cf_raw (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (τ z : ℕ) (hτ : τ < 2 * n)
    (hz : z < 2 ^ h) :
    rawC n h A (NN n h + (τ * 2 ^ h + z)) = (false, pinC n τ, wF n h A h τ z 0) := by
  obtain ⟨d1, d2⟩ := dm τ z (2 ^ h) hz
  have hlt := cpos_lt n h τ z hτ hz
  have hnot : ¬ (NN n h + (τ * 2 ^ h + z) < NN n h) := by omega
  have hlt2 : NN n h + (τ * 2 ^ h + z) < NN n h + SC n h := by omega
  unfold rawC cfGate
  rw [if_neg hnot, if_pos hlt2, Nat.add_sub_cancel_left, d1, d2]

-- every butterfly wire (levels 0 to h) lies before the final section
theorem wF_lt_NN (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (t τ z : ℕ) (e : ZMod 2) (ht : t ≤ h)
    (hτ : τ < TT n) (hz : z < 2 ^ h) :
    wF n h A t τ z e < 2 + 2 * n + NN n h := by
  have hNN : NN n h = SU n h + SD n h + SB n h := rfl
  unfold wF
  by_cases ht0 : t = 0
  · rw [if_pos ht0]
    unfold wG
    by_cases hτ2 : τ = 2 * n
    · rw [if_pos hτ2]
      have := wK_lt_SU n h A z 1 (e + 1) hz
      omega
    · rw [if_neg hτ2]
      have hM := M_ge n
      have hMM : MM n = 2 ^ Nat.clog 2 (n + 1) := rfl
      have hT : TT n = 2 * n + 1 := rfl
      have := wO_lt n h z (MM n + τ / 2)
        (e + 1 + ((τ % 2 : ℕ) : ZMod 2) * cf n h A (yvec h z) (τ / 2)) hz (by omega)
      omega
  · rw [if_neg ht0]
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have he : e.val < 2 := ZMod.val_lt e
    have hb1 : t' * TT n + τ < h * TT n := idx_lt t' τ h (TT n) (by omega) hτ
    have hb2 : (t' * TT n + τ) * 2 ^ h + z < h * TT n * 2 ^ h := idx_lt _ z _ _ hb1 hz
    unfold NN SB bq
    omega

theorem rawC_lt (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (j : ℕ) (hj : j < NN n h) :
    rawC n h A j = rawU n h A j := by
  unfold rawC
  rw [if_pos hj]

theorem GC_length (n h : ℕ) (A : Fin h → Fin n → ZMod 2) : (GC n h A).length = NC n h :=
  glist_length (2 + 2 * n) (NC n h) (rawC n h A)

-- the first NN gates of the whole circuit are the gates of GU
theorem GC_take (n h : ℕ) (A : Fin h → Fin n → ZMod 2) :
    (GC n h A).take (NN n h) = GU n h A := by
  have hmin : min (NN n h) (NC n h) = NN n h := by
    unfold NC
    omega
  have hl : (GU n h A).length = NN n h := glist_length (2 + 2 * n) (NN n h) (rawU n h A)
  have hg : ∀ j, j < NN n h → gd (2 + 2 * n) (rawC n h A) j = gd (2 + 2 * n) (rawU n h A) j := by
    intro j hj
    unfold gd
    rw [rawC_lt n h A j hj]
  apply List.ext_getElem
  · rw [List.length_take, GC_length, hl, hmin]
  · intro j h1 h2
    have hj : j < NN n h := by
      rw [hl] at h2
      exact h2
    have hj2 : j < (GC n h A).length := by
      rw [GC_length]
      unfold NC
      omega
    have e1 : (GC n h A)[j]'hj2 = gd (2 + 2 * n) (rawC n h A) j :=
      glist_get (2 + 2 * n) (NC n h) (rawC n h A) j hj2
    have e2 : (GU n h A)[j]'h2 = gd (2 + 2 * n) (rawU n h A) j :=
      glist_get (2 + 2 * n) (NN n h) (rawU n h A) j h2
    rw [List.getElem_take, e1, e2, hg j hj]

-- below the final section, the whole circuit has the wires of GU (values and depths alike)
theorem GC_agree {α : Type} (F : Bool → α → α → α) (d : α) (n h : ℕ)
    (A : Fin h → Fin n → ZMod 2) (w : List α) (k : ℕ) (hk : k < w.length + NN n h) :
    (wl F d (GC n h A) w).getD k d = (wl F d (GU n h A) w).getD k d := by
  have hj : NN n h ≤ (GC n h A).length := by
    rw [GC_length]
    unfold NC
    omega
  rw [← wl_take_getD F d (GC n h A) w (NN n h) k hk hj, GC_take]

theorem vC_eq (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool) (k : ℕ)
    (hk : k < 2 + 2 * n + NN n h) : vC n h A ρ k = vl n h A ρ k := by
  unfold vC vl
  exact GC_agree gop false n h A (pinsL n ρ) k (by rw [pinsL_length]; exact hk)

theorem dC_eq (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (k : ℕ) (hk : k < 2 + 2 * n + NN n h) :
    dC n h A k = (wl dop 0 (GU n h A) (List.replicate (2 + 2 * n) 0)).getD k 0 := by
  unfold dC
  exact GC_agree dop 0 n h A (List.replicate (2 + 2 * n) 0) k
    (by rw [List.length_replicate]; exact hk)

-- the value of a final OR gate
theorem cf_val (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool) (τ z : ℕ)
    (hτ : τ < 2 * n) (hz : z < 2 ^ h) :
    vC n h A ρ (wC n h τ z) =
      gop false (vC n h A ρ (pinC n τ)) (vC n h A ρ (wF n h A h τ z 0)) := by
  have hlt := cpos_lt n h τ z hτ hz
  have hraw := cf_raw n h A τ z hτ hz
  have hp := pinC_lt n τ hτ
  have hf := wF_lt_NN n h A h τ z 0 le_rfl (by unfold TT; omega) hz
  have hp' : pinC n τ < 2 + 2 * n + (NN n h + (τ * 2 ^ h + z)) := by omega
  have hf' : wF n h A h τ z 0 < 2 + 2 * n + (NN n h + (τ * 2 ^ h + z)) := by omega
  have hg := gd_eq (2 + 2 * n) (rawC n h A) (NN n h + (τ * 2 ^ h + z))
    (by rw [hraw]; exact hp') (by rw [hraw]; exact hf')
  have := gate_val (2 + 2 * n) (NC n h) (by omega) (rawC n h A) (pinsL n ρ) (pinsL_length n ρ)
    (NN n h + (τ * 2 ^ h + z)) (by unfold NC; omega)
  rw [hg, hraw] at this
  exact this

-- the depth of a final OR gate: one more than its butterfly input
theorem cf_dep (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (τ z : ℕ) (hτ : τ < 2 * n)
    (hz : z < 2 ^ h) :
    dC n h A (wC n h τ z) =
      (wl dop 0 (GU n h A) (List.replicate (2 + 2 * n) 0)).getD (wF n h A h τ z 0) 0 + 1 := by
  have hlt := cpos_lt n h τ z hτ hz
  have hraw := cf_raw n h A τ z hτ hz
  have hp := pinC_lt n τ hτ
  have hf := wF_lt_NN n h A h τ z 0 le_rfl (by unfold TT; omega) hz
  have hp' : pinC n τ < 2 + 2 * n + (NN n h + (τ * 2 ^ h + z)) := by omega
  have hf' : wF n h A h τ z 0 < 2 + 2 * n + (NN n h + (τ * 2 ^ h + z)) := by omega
  have hg := gd_eq (2 + 2 * n) (rawC n h A) (NN n h + (τ * 2 ^ h + z))
    (by rw [hraw]; exact hp') (by rw [hraw]; exact hf')
  have hrep : (List.replicate (2 + 2 * n) (0 : ℕ)).length = 2 + 2 * n := by
    rw [List.length_replicate]
  have := gate_dep (2 + 2 * n) (NC n h) (by omega) (rawC n h A) (List.replicate (2 + 2 * n) 0)
    hrep (NN n h + (τ * 2 ^ h + z)) (by unfold NC; omega)
  rw [hg, hraw] at this
  have e : dC n h A (wC n h τ z) =
      max (dC n h A (pinC n τ)) (dC n h A (wF n h A h τ z 0)) + 1 := this
  have h0 : dC n h A (pinC n τ) = 0 := by
    unfold dC
    rw [wl_getD_lt dop 0 _ _ _ (by rw [hrep]; exact hp)]
    simp [List.getD_eq_getElem?_getD, hp]
  have e3 := dC_eq n h A _ hf
  omega

-- index bounds of the outputs
theorem wC_lt (n h τ z : ℕ) (hτ : τ < 2 * n) (hz : z < 2 ^ h) :
    wC n h τ z < 2 + 2 * n + NC n h := by
  have := cpos_lt n h τ z hτ hz
  unfold wC NC
  omega

theorem excl_lt (n h : ℕ) (s : Fin h → ZMod 2) (i : Fin n) (b : Bool) :
    wC n h (2 * i.val + b.toNat) (enc s) < 2 + 2 * n + NC n h := by
  have hi : i.val < n := i.isLt
  have hb : b.toNat < 2 := Bool.toNat_lt b
  exact wC_lt n h _ _ (by omega) (enc_lt s)

theorem dead_lt (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (s : Fin h → ZMod 2) :
    wF n h A h (2 * n) (enc s) 0 < 2 + 2 * n + NC n h := by
  have := wF_lt_NN n h A h (2 * n) (enc s) 0 le_rfl (by unfold TT; omega) (enc_lt s)
  unfold NC
  omega

-- the excludeBit wire: true iff the pin wire of rho i = some (!b) or the butterfly output is true
theorem L_cf (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (s : Fin h → ZMod 2) (i : Fin n) (b : Bool) :
    vC n h A ρ (wC n h (2 * i.val + b.toNat) (enc s)) = true ↔
      ρ i = some (!b) ∨ vl n h A ρ (wF n h A h (2 * i.val + b.toNat) (enc s) 0) = true := by
  have hi : i.val < n := i.isLt
  have hb : b.toNat < 2 := Bool.toNat_lt b
  have hτ : 2 * i.val + b.toNat < 2 * n := by omega
  have hz : enc s < 2 ^ h := enc_lt s
  have hf : wF n h A h (2 * i.val + b.toNat) (enc s) 0 < 2 + 2 * n + NN n h :=
    wF_lt_NN n h A h _ _ 0 le_rfl (by unfold TT; omega) hz
  have e1 : vC n h A ρ (wC n h (2 * i.val + b.toNat) (enc s)) =
      (vC n h A ρ (pinC n (2 * i.val + b.toNat)) ||
        vC n h A ρ (wF n h A h (2 * i.val + b.toNat) (enc s) 0)) :=
    (cf_val n h A ρ _ _ hτ hz).trans rfl
  have e2 : vC n h A ρ (pinC n (2 * i.val + b.toNat)) = decide (ρ i = some (!b)) := by
    unfold vC
    rw [wl_getD_lt gop false _ _ _ (by rw [pinsL_length]; exact pinC_lt n _ hτ)]
    exact pinC_val n ρ i b
  rw [e1, e2, vC_eq n h A ρ _ hf, Bool.or_eq_true, decide_eq_true_eq]

-- the same with the butterfly lemma applied
theorem L_excl (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (s : Fin h → ZMod 2) (i : Fin n) (b : Bool) :
    vC n h A ρ (wC n h (2 * i.val + b.toNat) (enc s)) = true ↔
      ρ i = some (!b) ∨ BF (GP n h A ρ (2 * i.val + b.toNat)) h s 0 := by
  have hi : i.val < n := i.isLt
  have hb : b.toNat < 2 := Bool.toNat_lt b
  rw [L_cf n h A ρ s i b,
    L_bfly n h A ρ h le_rfl (2 * i.val + b.toNat) (by unfold TT; omega) s 0]

-- the dead wire in the whole circuit
theorem L_dead (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (s : Fin h → ZMod 2) :
    vC n h A ρ (wF n h A h (2 * n) (enc s) 0) = true ↔ BF (GP n h A ρ (2 * n)) h s 0 := by
  have hT : 2 * n < TT n := by
    unfold TT
    omega
  rw [vC_eq n h A ρ _ (wF_lt_NN n h A h (2 * n) (enc s) 0 le_rfl hT (enc_lt s))]
  exact L_bfly n h A ρ h le_rfl (2 * n) hT s 0

-- depths of the outputs in the whole circuit, in terms of depths in GU
theorem dead_dep (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (s : Fin h → ZMod 2) :
    dC n h A (wF n h A h (2 * n) (enc s) 0) =
      (wl dop 0 (GU n h A) (List.replicate (2 + 2 * n) 0)).getD (wF n h A h (2 * n) (enc s) 0) 0 := by
  have hT : 2 * n < TT n := by
    unfold TT
    omega
  exact dC_eq n h A _ (wF_lt_NN n h A h (2 * n) (enc s) 0 le_rfl hT (enc_lt s))

theorem excl_dep (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (s : Fin h → ZMod 2) (i : Fin n)
    (b : Bool) :
    dC n h A (wC n h (2 * i.val + b.toNat) (enc s)) =
      (wl dop 0 (GU n h A) (List.replicate (2 + 2 * n) 0)).getD
        (wF n h A h (2 * i.val + b.toNat) (enc s) 0) 0 + 1 := by
  have hi : i.val < n := i.isLt
  have hb : b.toNat < 2 := Bool.toNat_lt b
  exact cf_dep n h A _ _ (by omega) (enc_lt s)

-- every gate of the whole circuit reads earlier wires only
theorem GC_strict (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (i : Fin (GC n h A).length) :
    ((GC n h A).get i).2.1 < 2 + 2 * n + i.val ∧ ((GC n h A).get i).2.2 < 2 + 2 * n + i.val := by
  have hg : (GC n h A).get i = gd (2 + 2 * n) (rawC n h A) i.val :=
    glist_get (2 + 2 * n) (NC n h) (rawC n h A) i.val i.isLt
  rw [hg]
  exact gd_lt (2 + 2 * n) (by omega) (rawC n h A) i.val

-- the size: 18 Y M + 2 h (2n+1) Y + 2n Y gates, with M at most 2n + 1
theorem size_aux (n h Y M : ℕ) (hM : M ≤ 2 * n + 1) :
    6 * (Y * M) + 6 * (Y * (2 * M)) + 2 * (h * (2 * n + 1) * Y) + 2 * n * Y ≤
      256 * (n + 1) * (h + 1) * Y := by
  nlinarith [Nat.mul_le_mul_right Y hM, Nat.zero_le (Y * n * h), Nat.zero_le (Y * h),
    Nat.zero_le (Y * n), Nat.zero_le Y]

theorem NC_le (n h : ℕ) : NC n h ≤ 256 * (n + 1) * (h + 1) * 2 ^ h := by
  have hM : MM n ≤ 2 * n + 1 := M_le n
  have := size_aux n h (2 ^ h) (MM n) hM
  unfold NC NN SU SD SB SC TT
  exact this

-- section bridge

-- the duality core, copied verbatim from scratch_core.lean (scratch_bfly.lean does not hold it)
theorem z2_sub : ∀ a b : ZMod 2, a - b ≠ 0 → b = a + 1 := by decide

-- The duality core in pinned affine form. A pinned system has no solution exactly when some
-- row combination y vanishes on every free column while its parity on the pinned sites
-- disagrees with y . s (over ZMod 2: equals y . s + 1).
theorem core (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (s : Fin h → ZMod 2) :
    (¬ ∃ x : Fin n → Bool, (∀ i b, ρ i = some b → x i = b) ∧
        ∀ j, (∑ i : Fin n, if x i then A j i else 0) = s j) ↔
    ∃ y : Fin h → ZMod 2, (∀ i, ρ i = none → ∑ j, y j * A j i = 0) ∧
        (∑ i : Fin n, if ρ i = some true then ∑ j, y j * A j i else 0) =
          (∑ j, y j * s j) + 1 := by
  constructor
  · intro hno
    have hv : (fun j => s j - ∑ i : Fin n, if ρ i = some true then A j i else 0) ∉
        Submodule.span (ZMod 2)
          (Set.range (fun (i : Fin n) (j : Fin h) => if ρ i = none then A j i else 0)) := by
      intro hmem
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hmem
      apply hno
      refine ⟨fun i => (ρ i).getD (decide (c i = 1)), ?_, ?_⟩
      · intro i b hb
        simp [hb]
      · intro j
        have hcj : (∑ i, c i * (if ρ i = none then A j i else 0)) =
            s j - ∑ i : Fin n, (if ρ i = some true then A j i else 0) := by
          have := congrFun hc j
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
          exact this
        have key : ∀ i, (if (ρ i).getD (decide (c i = 1)) = true then A j i else 0) =
            (if ρ i = some true then A j i else 0) +
              c i * (if ρ i = none then A j i else 0) := by
          intro i
          rcases hρ : ρ i with _ | b
          · rcases z2 (c i) with h0 | h1
            · simp [h0]
            · simp [h1]
          · cases b <;> simp
        refine (Finset.sum_congr rfl (fun i _ => key i)).trans ?_
        rw [Finset.sum_add_distrib, hcj]
        ring
    obtain ⟨f, hfv, hpf⟩ := Submodule.exists_le_ker_of_notMem hv
    obtain ⟨y, hy⟩ : ∃ y : Fin h → ZMod 2, ∀ w, f w = ∑ i, w i * y i :=
      ⟨fun i => f (fun j => if i = j then 1 else 0), fun w => by
        rw [LinearMap.pi_apply_eq_sum_univ f w]
        simp only [smul_eq_mul]⟩
    refine ⟨y, ?_, ?_⟩
    · intro i hi
      have hmem : f (fun j => if ρ i = none then A j i else 0) = 0 :=
        LinearMap.mem_ker.mp (hpf (Submodule.subset_span ⟨i, rfl⟩))
      have hcol : (fun (j : Fin h) => if ρ i = none then A j i else 0) = fun j => A j i := by
        funext j
        simp [hi]
      rw [hcol, hy] at hmem
      rw [← hmem]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · apply z2_sub
      intro h0
      apply hfv
      simp only [hy]
      have E : (∑ i, (s i - ∑ k : Fin n, if ρ k = some true then A i k else 0) * y i) =
          (∑ j, y j * s j) - ∑ k : Fin n, if ρ k = some true then ∑ j, y j * A j k else 0 := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
        rw [Finset.sum_comm]
        congr 1
        · apply Finset.sum_congr rfl
          intro j _
          ring
        · apply Finset.sum_congr rfl
          intro k _
          split_ifs <;> simp [mul_comm]
      rw [E]
      exact h0
  · rintro ⟨y, hy0, hy1⟩ ⟨x, hx, hs⟩
    have e1 : (∑ j, y j * s j) =
        ∑ i : Fin n, if ρ i = some true then ∑ j, y j * A j i else 0 := by
      calc (∑ j, y j * s j) = ∑ j, y j * ∑ i : Fin n, (if x i then A j i else 0) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hs j]
        _ = ∑ i : Fin n, ∑ j, y j * (if x i then A j i else 0) := by
            simp only [Finset.mul_sum]
            rw [Finset.sum_comm]
        _ = ∑ i : Fin n, if ρ i = some true then ∑ j, y j * A j i else 0 := by
            apply Finset.sum_congr rfl
            intro i _
            rcases hρ : ρ i with _ | b
            · by_cases hxi : x i = true
              · simp [hxi, hy0 i hρ]
              · simp [hxi]
            · have hxb := hx i b hρ
              cases b <;> simp [hxb]
    rw [← e1] at hy1
    simp at hy1

-- The excludeBit form: forcing site i0 to b either contradicts its pin, or some row
-- combination vanishes on every free site other than i0 and its parity, with the forced
-- bit added back, disagrees with y . s.
theorem core_excl (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (s : Fin h → ZMod 2) (i0 : Fin n) (b : Bool) :
    (¬ ∃ x : Fin n → Bool, ((∀ i c, ρ i = some c → x i = c) ∧
        ∀ j, (∑ i : Fin n, if x i then A j i else 0) = s j) ∧ x i0 = b) ↔
    (ρ i0 = some (!b) ∨ ∃ y : Fin h → ZMod 2,
        (∀ i, i ≠ i0 → ρ i = none → ∑ j, y j * A j i = 0) ∧
        (∑ i : Fin n, if i = i0 then (if b then ∑ j, y j * A j i else 0)
          else (if ρ i = some true then ∑ j, y j * A j i else 0)) = (∑ j, y j * s j) + 1) := by
  by_cases hρ : ρ i0 = some (!b)
  · refine iff_of_true ?_ (Or.inl hρ)
    rintro ⟨x, ⟨hx, -⟩, hxb⟩
    have hb := hx i0 (!b) hρ
    rw [hxb] at hb
    cases b <;> simp at hb
  · rw [or_iff_right hρ]
    have hiff : (∃ x : Fin n → Bool, ((∀ i c, ρ i = some c → x i = c) ∧
        ∀ j, (∑ i : Fin n, if x i then A j i else 0) = s j) ∧ x i0 = b) ↔
        ∃ x : Fin n → Bool, (∀ i c, Function.update ρ i0 (some b) i = some c → x i = c) ∧
          ∀ j, (∑ i : Fin n, if x i then A j i else 0) = s j := by
      constructor
      · rintro ⟨x, ⟨hx, hs⟩, hxb⟩
        refine ⟨x, ?_, hs⟩
        intro i c hc
        by_cases hi : i = i0
        · subst hi
          rw [Function.update_self] at hc
          rw [hxb]
          exact Option.some.inj hc
        · rw [Function.update_of_ne hi] at hc
          exact hx i c hc
      · rintro ⟨x, hx, hs⟩
        have hxb : x i0 = b := hx i0 b (Function.update_self _ _ _)
        refine ⟨x, ⟨?_, hs⟩, hxb⟩
        intro i c hc
        by_cases hi : i = i0
        · subst hi
          rw [hxb]
          cases b <;> cases c <;> simp_all
        · exact hx i c (by rw [Function.update_of_ne hi]; exact hc)
    rw [hiff, core n h A (Function.update ρ i0 (some b)) s]
    apply exists_congr
    intro y
    apply and_congr
    · constructor
      · intro H i hi hn
        exact H i (by rw [Function.update_of_ne hi]; exact hn)
      · intro H i hn
        by_cases hi : i = i0
        · subst hi
          rw [Function.update_self] at hn
          exact absurd hn (by simp)
        · rw [Function.update_of_ne hi] at hn
          exact H i hi hn
    · have hsum : (∑ i : Fin n, if Function.update ρ i0 (some b) i = some true
            then ∑ j, y j * A j i else 0) =
          ∑ i : Fin n, if i = i0 then (if b then ∑ j, y j * A j i else 0)
            else (if ρ i = some true then ∑ j, y j * A j i else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = i0
        · subst hi
          rw [Function.update_self]
          cases b <;> simp
        · rw [Function.update_of_ne hi]
          simp [hi]
      rw [hsum]

-- padding: a site function that vanishes from n on sums over [0, M) as over Fin n
theorem pad_sum (f : ℕ → ZMod 2) (n M : ℕ) (hM : n ≤ M) (hf : ∀ k, n ≤ k → f k = 0) :
    (∑ k ∈ Finset.Ico 0 M, f k) = ∑ i : Fin n, f i.val := by
  have h2 : (∑ k ∈ Finset.Ico n M, f k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact hf k (Finset.mem_Ico.mp hk).1
  rw [← Finset.sum_Ico_consecutive f (Nat.zero_le n) hM, h2, add_zero, Nat.Ico_zero_eq_range,
    Finset.sum_range]

-- the sites of [0, M) other than i
theorem out_sum (par : ℕ → ZMod 2) (i M : ℕ) (hi : i < M) :
    (∑ k ∈ Finset.Ico 0 i, par k) + (∑ k ∈ Finset.Ico (i + 1) M, par k) =
      ∑ k ∈ Finset.Ico 0 M, (if k = i then 0 else par k) := by
  rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le i) (show i ≤ M by omega),
    ← Finset.sum_Ico_consecutive _ (show i ≤ i + 1 by omega) (show i + 1 ≤ M by omega),
    Nat.Ico_succ_singleton, Finset.sum_singleton, ite_eq_left (rfl : i = i), zero_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≠ i := by
      have := (Finset.mem_Ico.mp hk).2
      omega
    rw [ite_eq_right hki]
  · apply Finset.sum_congr rfl
    intro k hk
    have hki : k ≠ i := by
      have := (Finset.mem_Ico.mp hk).1
      omega
    rw [ite_eq_right hki]

-- the sum with one term split off
theorem excl_sum (n : ℕ) (u g : Fin n → ZMod 2) (i0 : Fin n) :
    (∑ i : Fin n, if i = i0 then u i else g i) =
      u i0 + ∑ i : Fin n, if i = i0 then 0 else g i := by
  have key : ∀ i : Fin n, (if i = i0 then u i else g i) =
      (if i = i0 then u i else 0) + (if i = i0 then 0 else g i) := by
    intro i
    by_cases hi : i = i0
    · rw [ite_eq_left hi, ite_eq_left hi, ite_eq_left hi, add_zero]
    · rw [ite_eq_right hi, ite_eq_right hi, ite_eq_right hi, zero_add]
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib, Finset.sum_ite_eq',
    ite_eq_left (Finset.mem_univ i0)]

-- in ZMod 2, x = a + c exactly when c + x = a
theorem z2_shift : ∀ s e c : ZMod 2, s = e + 1 + c ↔ c + s = e + 1 := by decide

-- the padded site data at a real site and at a padding site
theorem cf_fin (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (yv : Fin h → ZMod 2) (i : Fin n) :
    cf n h A yv i.val = ∑ j, yv j * A j i := by
  unfold cf
  exact dite_eq_left i.isLt

theorem rho_fin (n : ℕ) (ρ : Fin n → Option Bool) (i : Fin n) : rho n ρ i.val = ρ i := by
  unfold rho
  exact dite_eq_left i.isLt

theorem cf_ge (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (yv : Fin h → ZMod 2) (k : ℕ)
    (hk : n ≤ k) : cf n h A yv k = 0 := by
  have hk' : ¬ (k < n) := by omega
  unfold cf
  rw [dite_eq_right hk']

theorem okS_fin (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (yv : Fin h → ZMod 2) (i : Fin n) :
    okS n h A ρ yv i.val ↔ (ρ i = none → ∑ j, yv j * A j i = 0) := by
  unfold okS
  rw [cf_fin, rho_fin]
  constructor
  · rintro (h0 | h1) hn
    · exact h0
    · exact absurd hn h1
  · intro H
    by_cases hn : ρ i = none
    · exact Or.inl (H hn)
    · exact Or.inr hn

theorem okS_ge (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (yv : Fin h → ZMod 2) (k : ℕ) (hk : n ≤ k) : okS n h A ρ yv k :=
  Or.inl (cf_ge n h A yv k hk)

theorem parS_fin (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (yv : Fin h → ZMod 2) (i : Fin n) :
    parS n h A ρ yv i.val = if ρ i = some true then ∑ j, yv j * A j i else 0 := by
  unfold parS
  rw [cf_fin, rho_fin]

theorem parS_ge (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (yv : Fin h → ZMod 2) (k : ℕ) (hk : n ≤ k) : parS n h A ρ yv k = 0 := by
  unfold parS
  rw [cf_ge n h A yv k hk, ite_self]

-- the root flag is the right side of core for the row combination yv
theorem KF_root (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (yv : Fin h → ZMod 2) (p : ZMod 2) :
    KF n h A ρ yv 0 0 p ↔ (∀ i : Fin n, ρ i = none → ∑ j, yv j * A j i = 0) ∧
      (∑ i : Fin n, if ρ i = some true then ∑ j, yv j * A j i else 0) = p := by
  have hM : n ≤ MM n := by
    have h1 := M_ge n
    have h2 : MM n = 2 ^ Nat.clog 2 (n + 1) := rfl
    omega
  have hs : (∑ k ∈ Finset.Ico 0 (MM n), parS n h A ρ yv k) =
      ∑ i : Fin n, if ρ i = some true then ∑ j, yv j * A j i else 0 := by
    rw [pad_sum (parS n h A ρ yv) n (MM n) hM (parS_ge n h A ρ yv)]
    exact Finset.sum_congr rfl (fun i _ => parS_fin n h A ρ yv i)
  have hall : (∀ k, 0 ≤ k → k < MM n → okS n h A ρ yv k) ↔
      ∀ i : Fin n, ρ i = none → ∑ j, yv j * A j i = 0 := by
    constructor
    · intro H i
      have hin := i.isLt
      exact (okS_fin n h A ρ yv i).mp (H i.val (Nat.zero_le _) (by omega))
    · intro H k _ hkM
      by_cases hkn : k < n
      · exact (okS_fin n h A ρ yv ⟨k, hkn⟩).mpr (H ⟨k, hkn⟩)
      · exact okS_ge n h A ρ yv k (by omega)
  have hMd : MM n = 2 ^ HH n := rfl
  unfold KF Flag
  rw [Nat.sub_zero, zero_mul, zero_add, one_mul, ← hMd, hs]
  exact and_congr hall Iff.rfl

-- the outside flag of leaf i0 is the right side of core_excl without the forced bit
theorem OF_leaf (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (yv : Fin h → ZMod 2) (i0 : Fin n) (p : ZMod 2) :
    OF n h A ρ yv (HH n) i0.val p ↔
      (∀ i : Fin n, i ≠ i0 → ρ i = none → ∑ j, yv j * A j i = 0) ∧
      (∑ i : Fin n, if i = i0 then 0
        else (if ρ i = some true then ∑ j, yv j * A j i else 0)) = p := by
  have hM : n ≤ MM n := by
    have h1 := M_ge n
    have h2 : MM n = 2 ^ Nat.clog 2 (n + 1) := rfl
    omega
  have hi0 : i0.val < MM n := by
    have := i0.isLt
    omega
  have hp : (∑ k ∈ Finset.Ico 0 (MM n), (if k = i0.val then 0 else parS n h A ρ yv k)) =
      ∑ i : Fin n, (if i.val = i0.val then 0 else parS n h A ρ yv i.val) :=
    pad_sum (fun k => if k = i0.val then 0 else parS n h A ρ yv k) n (MM n) hM (fun k hk => by
      show (if k = i0.val then 0 else parS n h A ρ yv k) = 0
      rw [ite_eq_right (show k ≠ i0.val by have := i0.isLt; omega)]
      exact parS_ge n h A ρ yv k hk)
  have hs : (∑ k ∈ Finset.Ico 0 i0.val, parS n h A ρ yv k) +
      (∑ k ∈ Finset.Ico (i0.val + 1) (MM n), parS n h A ρ yv k) =
      ∑ i : Fin n, if i = i0 then 0
        else (if ρ i = some true then ∑ j, yv j * A j i else 0) := by
    rw [out_sum (parS n h A ρ yv) i0.val (MM n) hi0, hp]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = i0
    · rw [ite_eq_left hi, ite_eq_left (congrArg Fin.val hi)]
    · rw [ite_eq_right hi, ite_eq_right (show ¬ (i.val = i0.val) from fun e => hi (Fin.ext e)),
        parS_fin]
  have hall : (∀ k, (k < i0.val ∨ i0.val + 1 ≤ k) → k < MM n → okS n h A ρ yv k) ↔
      ∀ i : Fin n, i ≠ i0 → ρ i = none → ∑ j, yv j * A j i = 0 := by
    constructor
    · intro H i hi
      have hv : i.val ≠ i0.val := fun e => hi (Fin.ext e)
      have hin := i.isLt
      exact (okS_fin n h A ρ yv i).mp (H i.val (by omega) (by omega))
    · intro H k hk hkM
      by_cases hkn : k < n
      · have hne : (⟨k, hkn⟩ : Fin n) ≠ i0 := by
          intro e
          have he : k = i0.val := congrArg Fin.val e
          omega
        exact (okS_fin n h A ρ yv ⟨k, hkn⟩).mpr (H ⟨k, hkn⟩ hne)
      · exact okS_ge n h A ρ yv k (by omega)
  unfold OF OFs
  rw [Nat.sub_self, pow_zero, mul_one, mul_one, hs]
  exact and_congr hall Iff.rfl

-- the butterfly input of dead (target 2 n) is the right side of core
theorem GP_dead (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (yv : Fin h → ZMod 2) (e : ZMod 2) :
    GP n h A ρ (2 * n) yv e ↔
      (∀ i : Fin n, ρ i = none → ∑ j, yv j * A j i = 0) ∧
      (∑ i : Fin n, if ρ i = some true then ∑ j, yv j * A j i else 0) = e + 1 := by
  unfold GP
  rw [ite_eq_left (rfl : 2 * n = 2 * n)]
  exact KF_root n h A ρ yv (e + 1)

-- the butterfly input of excludeBit (i0, b) (target 2 i0 + b) is the right side of core_excl
theorem GP_excl (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (i0 : Fin n) (b : Bool) (yv : Fin h → ZMod 2) (e : ZMod 2) :
    GP n h A ρ (2 * i0.val + b.toNat) yv e ↔
      (∀ i : Fin n, i ≠ i0 → ρ i = none → ∑ j, yv j * A j i = 0) ∧
      (∑ i : Fin n, if i = i0 then (if b then ∑ j, yv j * A j i else 0)
        else (if ρ i = some true then ∑ j, yv j * A j i else 0)) = e + 1 := by
  have hb : b.toNat < 2 := Bool.toNat_lt b
  have hi := i0.isLt
  have hτ : ¬ (2 * i0.val + b.toNat = 2 * n) := by omega
  have hd : (2 * i0.val + b.toNat) / 2 = i0.val := by omega
  have hm : (2 * i0.val + b.toNat) % 2 = b.toNat := by omega
  have hsum : (∑ i : Fin n, if i = i0 then (if b then ∑ j, yv j * A j i else 0)
        else (if ρ i = some true then ∑ j, yv j * A j i else 0)) =
      (if b then ∑ j, yv j * A j i0 else 0) +
        ∑ i : Fin n, if i = i0 then 0 else (if ρ i = some true then ∑ j, yv j * A j i else 0) :=
    excl_sum n (fun i => if b then ∑ j, yv j * A j i else 0)
      (fun i => if ρ i = some true then ∑ j, yv j * A j i else 0) i0
  have hu : ((b.toNat : ℕ) : ZMod 2) * cf n h A yv i0.val =
      if b then ∑ j, yv j * A j i0 else 0 := by
    rw [cf_fin]
    cases b <;> simp
  unfold GP
  rw [ite_eq_right hτ, hd, hm, OF_leaf, hsum, hu]
  exact and_congr Iff.rfl (z2_shift _ _ _)

-- BF_top at sign 0
theorem BF_top0 {h : ℕ} (P : (Fin h → ZMod 2) → ZMod 2 → Prop) (z : Fin h → ZMod 2) :
    BF P h z 0 ↔ ∃ y : Fin h → ZMod 2, P y (∑ j, y j * z j) := by
  rw [BF_top]
  simp only [zero_add]

-- the full butterfly of dead at syndrome s says: the pinned system has no solution
theorem bridge_dead (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (s : Fin h → ZMod 2) :
    BF (GP n h A ρ (2 * n)) h s 0 ↔
      ¬ ∃ x : Fin n → Bool, (∀ i b, ρ i = some b → x i = b) ∧
        ∀ j, (∑ i : Fin n, if x i then A j i else 0) = s j := by
  have h1 := BF_top0 (GP n h A ρ (2 * n)) s
  have h2 := exists_congr (fun y => GP_dead n h A ρ y (∑ j, y j * s j))
  exact h1.trans (h2.trans (core n h A ρ s).symm)

-- the pin of i0 or the full butterfly of target 2 i0 + b: no solution with x i0 = b
theorem bridge_excl (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (s : Fin h → ZMod 2) (i0 : Fin n) (b : Bool) :
    (ρ i0 = some (!b) ∨ BF (GP n h A ρ (2 * i0.val + b.toNat)) h s 0) ↔
      ¬ ∃ x : Fin n → Bool, ((∀ i c, ρ i = some c → x i = c) ∧
        ∀ j, (∑ i : Fin n, if x i then A j i else 0) = s j) ∧ x i0 = b := by
  have h1 := BF_top0 (GP n h A ρ (2 * i0.val + b.toNat)) s
  have h2 := exists_congr (fun y => GP_excl n h A ρ i0 b y (∑ j, y j * s j))
  exact (or_congr Iff.rfl (h1.trans h2)).trans (core_excl n h A ρ s i0 b).symm

-- the same on wires: the top butterfly wire of dead, and of excludeBit next to its pin
theorem vl_dead (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (s : Fin h → ZMod 2) :
    vl n h A ρ (wF n h A h (2 * n) (enc s) 0) = true ↔
      ¬ ∃ x : Fin n → Bool, (∀ i b, ρ i = some b → x i = b) ∧
        ∀ j, (∑ i : Fin n, if x i then A j i else 0) = s j := by
  have hτ : 2 * n < TT n := by
    unfold TT
    omega
  exact (L_bfly n h A ρ h le_rfl (2 * n) hτ s 0).trans (bridge_dead n h A ρ s)

theorem vl_excl (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (ρ : Fin n → Option Bool)
    (s : Fin h → ZMod 2) (i0 : Fin n) (b : Bool) :
    (ρ i0 = some (!b) ∨ vl n h A ρ (wF n h A h (2 * i0.val + b.toNat) (enc s) 0) = true) ↔
      ¬ ∃ x : Fin n → Bool, ((∀ i c, ρ i = some c → x i = c) ∧
        ∀ j, (∑ i : Fin n, if x i then A j i else 0) = s j) ∧ x i0 = b := by
  have hb : b.toNat < 2 := Bool.toNat_lt b
  have hi := i0.isLt
  have hτ : 2 * i0.val + b.toNat < TT n := by
    unfold TT
    omega
  exact (or_congr Iff.rfl (L_bfly n h A ρ h le_rfl _ hτ s 0)).trans (bridge_excl n h A ρ s i0 b)

-- section spec

-- the clean specification the construction meets, with run and depths as the fold wl
def Spec (n h : ℕ) (A : Fin h → Fin n → ZMod 2) : Prop :=
  ∃ (G : List (Bool × ℕ × ℕ)) (dead : (Fin h → ZMod 2) → ℕ)
    (excl : (Fin h → ZMod 2) → Fin n × Bool → ℕ),
    G.length ≤ 256 * (n + 1) * (h + 1) * 2 ^ h ∧
    (∀ (i : Fin G.length), (G.get i).2.1 < 2 + 2 * n + i.val ∧ (G.get i).2.2 < 2 + 2 * n + i.val) ∧
    ∀ s : Fin h → ZMod 2,
      dead s < 2 + 2 * n + G.length ∧
      (wl dop 0 G (List.replicate (2 + 2 * n) 0)).getD (dead s) 0 ≤
        16 * (h + Nat.clog 2 (n + 1) + 1) ∧
      (∀ v : Fin n × Bool, excl s v < 2 + 2 * n + G.length ∧
        (wl dop 0 G (List.replicate (2 + 2 * n) 0)).getD (excl s v) 0 ≤
          16 * (h + Nat.clog 2 (n + 1) + 1)) ∧
      ∀ ρ : Fin n → Option Bool,
        ((wl gop false G (pinsL n ρ)).getD (dead s) false = true ↔
          ¬ ∃ x : Fin n → Bool, (∀ i b, ρ i = some b → x i = b) ∧
            ∀ j, (∑ i : Fin n, if x i then A j i else 0) = s j) ∧
        ∀ v : Fin n × Bool, (wl gop false G (pinsL n ρ)).getD (excl s v) false = true ↔
          ¬ ∃ x : Fin n → Bool, ((∀ i b, ρ i = some b → x i = b) ∧
            ∀ j, (∑ i : Fin n, if x i then A j i else 0) = s j) ∧ x v.1 = v.2

-- the depth of the dead wire in the whole circuit: at most 4 H + h
theorem dead_dep_le (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (s : Fin h → ZMod 2) :
    dC n h A (wF n h A h (2 * n) (enc s) 0) ≤ 16 * (h + Nat.clog 2 (n + 1) + 1) := by
  have h1 : dC n h A (wF n h A h (2 * n) (enc s) 0) = dep n h A (wF n h A h (2 * n) (enc s) 0) :=
    dead_dep n h A s
  rw [h1]
  exact dep_dead n h A s

-- the depth of an excludeBit wire in the whole circuit: at most 4 H + h + 1
theorem excl_dep_le (n h : ℕ) (A : Fin h → Fin n → ZMod 2) (s : Fin h → ZMod 2) (i : Fin n)
    (b : Bool) :
    dC n h A (wC n h (2 * i.val + b.toNat) (enc s)) ≤ 16 * (h + Nat.clog 2 (n + 1) + 1) := by
  have hi : i.val < n := i.isLt
  have hb : b.toNat < 2 := Bool.toNat_lt b
  have hτ : 2 * i.val + b.toNat < TT n := by
    unfold TT
    omega
  have h1 : dep n h A (wF n h A h (2 * i.val + b.toNat) (enc s) 0) ≤ 4 * HH n + h :=
    L_bfly_dep n h A h le_rfl (2 * i.val + b.toNat) hτ (enc s) (enc_lt s) 0
  have h2 : HH n = Nat.clog 2 (n + 1) := rfl
  have h3 : dC n h A (wC n h (2 * i.val + b.toNat) (enc s)) =
      dep n h A (wF n h A h (2 * i.val + b.toNat) (enc s) 0) + 1 :=
    excl_dep n h A s i b
  omega

-- the construction meets the clean specification
theorem spec_holds (n h : ℕ) (A : Fin h → Fin n → ZMod 2) : Spec n h A := by
  unfold Spec
  refine ⟨GC n h A, fun s => wF n h A h (2 * n) (enc s) 0,
    fun s v => wC n h (2 * v.1.val + v.2.toNat) (enc s), ?_, ?_, ?_⟩
  · rw [GC_length]
    exact NC_le n h
  · intro i
    exact GC_strict n h A i
  · intro s
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [GC_length]
      exact dead_lt n h A s
    · exact dead_dep_le n h A s
    · intro v
      refine ⟨?_, ?_⟩
      · rw [GC_length]
        exact excl_lt n h s v.1 v.2
      · exact excl_dep_le n h A s v.1 v.2
    · intro ρ
      refine ⟨?_, ?_⟩
      · exact (L_dead n h A ρ s).trans (bridge_dead n h A ρ s)
      · intro v
        exact (L_excl n h A ρ s v.1 v.2).trans (bridge_excl n h A ρ s v.1 v.2)

end PEqualNP.Outside.L_pcx_302_aux

-- the posted statement follows from the clean specification by unfolding its lets
theorem PEqualNP.Outside.L_pcx_302 : ∀ (n h : ℕ) (A : Fin h → Fin n → ZMod 2),
  let V := Fin n × Bool
  let S := Fin h → ZMod 2
  let compatible := fun (ρ : Fin n → Option Bool) (s : S) (x : Fin n → Bool) =>
    (∀ i b, ρ i = some b → x i = b) ∧
    ∀ j, (∑ i : Fin n, if x i then A j i else 0) = s j
  let pins := fun (ρ : Fin n → Option Bool) =>
    [false, true] ++ List.ofFn (fun i : Fin n => decide (ρ i = some false)) ++
      List.ofFn (fun i : Fin n => decide (ρ i = some true))
  let Gate := Bool × ℕ × ℕ
  let run := fun (G : List Gate) (ρ : Fin n → Option Bool) =>
    G.foldl (fun (w : List Bool) g =>
      let l := w.getD g.2.1 false
      let r := w.getD g.2.2 false
      w ++ [if g.1 then l && r else l || r]) (pins ρ)
  let depths := fun (G : List Gate) =>
    G.foldl (fun (w : List ℕ) g =>
      w ++ [max (w.getD g.2.1 0) (w.getD g.2.2 0) + 1]) (List.replicate (2+2*n) 0)
  ∃ (G : List Gate) (dead : S → ℕ) (excludeBit : S → V → ℕ),
    G.length ≤ 256*(n+1)*(h+1)*2^h ∧
    (∀ (i : Fin G.length), (G.get i).2.1 < 2+2*n+i.val ∧ (G.get i).2.2 < 2+2*n+i.val) ∧
    ∀ s : S,
      dead s < 2+2*n+G.length ∧ (depths G).getD (dead s) 0 ≤ 16*(h+Nat.clog 2 (n+1)+1) ∧
      (∀ v : V, excludeBit s v < 2+2*n+G.length ∧
        (depths G).getD (excludeBit s v) 0 ≤ 16*(h+Nat.clog 2 (n+1)+1)) ∧
      ∀ ρ : Fin n → Option Bool,
        ((run G ρ).getD (dead s) false = true ↔ ¬ ∃ x, compatible ρ s x) ∧
        ∀ v : V, (run G ρ).getD (excludeBit s v) false = true ↔
          ¬ ∃ x, compatible ρ s x ∧ x v.1 = v.2 := by
  intro n h A
  obtain ⟨G, dead, excl, h1, h2, h3⟩ := PEqualNP.Outside.L_pcx_302_aux.spec_holds n h A
  exact ⟨G, dead, excl, h1, h2, h3⟩
