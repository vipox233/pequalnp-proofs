import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_722

open PEqualNP.CircuitLowerBounds

/-! ## Evaluation of circuits, one gate at a time -/

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem len_fold (G : List Gate) (L : List Bool) :
    (G.foldl step L).length = L.length + G.length := by
  induction G generalizing L with
  | nil => simp
  | cons g G ih => rw [List.foldl_cons, ih]; simp [step]; omega

theorem getD_left (L M : List Bool) (k : ℕ) (h : k < L.length) :
    (L ++ M).getD k false = L.getD k false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_ge (L : List Bool) (k : ℕ) (h : L.length ≤ k) : L.getD k false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_concat (L : List Bool) (v : Bool) : (L ++ [v]).getD L.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem lt_of_getD (L : List Bool) (k : ℕ) (h : L.getD k false = true) : k < L.length := by
  by_contra hc
  rw [getD_ge _ _ (by omega)] at h
  exact Bool.false_ne_true h

theorem prefix_fold (G : List Gate) (L : List Bool) (k : ℕ) (hk : k < L.length) :
    (G.foldl step L).getD k false = L.getD k false := by
  induction G generalizing L with
  | nil => rfl
  | cons g G ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    exact getD_left _ _ _ hk

theorem at_fold (G : List Gate) (L : List Bool) (j : ℕ) (hj : j < G.length) :
    (G.foldl step L).getD (L.length + j) false =
      (G[j]'hj).op.eval ((G[j]'hj).inputs.map fun i =>
        if i < L.length + j then (G.foldl step L).getD i false else false) := by
  induction G generalizing L j with
  | nil => simp at hj
  | cons g G ih =>
    cases j with
    | zero =>
      simp only [List.foldl_cons, List.getElem_cons_zero, Nat.add_zero]
      rw [prefix_fold G (step L g) L.length (by simp [step])]
      simp only [step]
      rw [getD_concat]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with h
      · rw [prefix_fold _ _ _ (by simp; omega), getD_left _ _ _ h]
      · exact getD_ge _ _ (by omega)
    | succ j =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      have := ih (step L g) j (by simpa using hj)
      have hl : (step L g).length = L.length + 1 := by simp [step]
      rw [hl] at this
      rw [show L.length + (j + 1) = L.length + 1 + j by omega]
      exact this

def mapG (ψ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ψ⟩

theorem sim (ψ : ℕ → ℕ) (G : List Gate) : ∀ (L L' : List Bool),
    (∀ k < L.length, ψ k < L'.length ∧ L'.getD (ψ k) false = L.getD k false) →
    (∀ j, ψ (L.length + j) = L'.length + j) →
    ∀ k < L.length + G.length, ((G.map (mapG ψ)).foldl step L').getD (ψ k) false =
      (G.foldl step L).getD k false := by
  induction G with
  | nil => intro L L' h1 _ k hk; simpa using (h1 k (by simpa using hk)).2
  | cons g G ih =>
    intro L L' h1 h2 k hk
    have hread : ∀ i, L'.getD (ψ i) false = L.getD i false := by
      intro i
      by_cases hi : i < L.length
      · exact (h1 i hi).2
      · have := h2 (i - L.length)
        rw [show L.length + (i - L.length) = i by omega] at this
        rw [this, getD_ge _ _ (by omega), getD_ge _ _ (by omega)]
    have hv : (mapG ψ g).op.eval ((mapG ψ g).inputs.map fun i => L'.getD i false) =
        g.op.eval (g.inputs.map fun i => L.getD i false) := by
      simp only [mapG, List.map_map, Function.comp_def, hread]
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · intro k hk
      simp only [step, List.length_append, List.length_singleton] at hk ⊢
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · refine ⟨by have := (h1 k hk).1; omega, ?_⟩
        rw [getD_left _ _ _ (h1 k hk).1, getD_left _ _ _ hk]
        exact (h1 k hk).2
      · subst hk
        have := h2 0
        simp only [Nat.add_zero] at this
        rw [this]
        refine ⟨by omega, ?_⟩
        rw [getD_concat, getD_concat]
        exact hv
    · intro j
      simp only [step, List.length_append, List.length_singleton]
      rw [show L.length + 1 + j = L.length + (j + 1) by omega, h2]
      omega
    · simp only [step, List.length_append, List.length_singleton]
      simp only [List.length_cons] at hk
      omega

theorem allfalse (G : List Gate) (hG : ∀ g ∈ G, g.op = GateOp.or) : ∀ L : List Bool,
    (∀ k, L.getD k false = false) → ∀ k, (G.foldl step L).getD k false = false := by
  induction G with
  | nil => intro L h k; exact h k
  | cons g G ih =>
    intro L h k
    simp only [List.foldl_cons]
    apply ih (fun g hg => hG g (List.mem_cons_of_mem _ hg))
    intro k
    have hv : g.op.eval (g.inputs.map fun i => L.getD i false) = false := by
      rw [hG g (by simp)]
      simp only [GateOp.eval, h]
      simp
    by_cases hk : k < L.length
    · simp only [step]
      rw [getD_left _ _ _ hk]
      exact h k
    · by_cases hk2 : k = L.length
      · subst hk2
        simp only [step]
        rw [getD_concat]
        exact hv
      · simp only [step]
        exact getD_ge _ _ (by simp; omega)

/-! ## Supports of wires of an OR circuit on unit inputs -/

def e (n : ℕ) (i : Fin n) : List Bool := List.ofFn fun h : Fin n => decide (h = i)

def val (C : Circuit) (n : ℕ) (i : Fin n) (w : ℕ) : Bool := (C.wires (e n i)).getD w false

def supp (C : Circuit) (n : ℕ) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => val C n i w = true

theorem e_len (n : ℕ) (i : Fin n) : (e n i).length = n := by simp [e]

theorem e_get (n : ℕ) (i : Fin n) (k : ℕ) (hk : k < n) :
    (e n i).getD k false = decide (k = i.val) := by
  simp [e, List.getD_eq_getElem?_getD, hk, Fin.ext_iff]

theorem mem_supp (C : Circuit) (n w : ℕ) (i : Fin n) :
    i ∈ supp C n w ↔ (C.gates.foldl step (e n i)).getD w false = true := by
  unfold supp
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rfl

theorem supp_input (C : Circuit) (n w : ℕ) (hw : w < n) (i : Fin n) (h : i ∈ supp C n w) :
    i.val = w := by
  rw [mem_supp] at h
  rw [prefix_fold _ _ _ (by rw [e_len]; exact hw), e_get _ _ _ hw] at h
  simp at h
  omega

theorem supp_big (C : Circuit) (n w : ℕ) (hw : n + C.gates.length ≤ w) : supp C n w = ∅ := by
  ext i
  simp only [Finset.notMem_empty, iff_false]
  rw [mem_supp, getD_ge _ _ (by rw [len_fold, e_len]; omega)]
  simp

theorem supp_gate (C : Circuit) (n : ℕ) (hor : ∀ g ∈ C.gates, g.op = GateOp.or)
    (j : ℕ) (hj : j < C.gates.length) (i : Fin n) :
    i ∈ supp C n (n + j) ↔ ∃ k ∈ (C.gates[j]'hj).inputs, k < n + j ∧ i ∈ supp C n k := by
  simp only [mem_supp]
  have := at_fold C.gates (e n i) j hj
  rw [e_len] at this
  rw [this, hor _ (List.getElem_mem hj)]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  constructor
  · rintro ⟨k, hk, h⟩
    by_cases hk2 : k < n + j
    · rw [if_pos hk2] at h
      exact ⟨k, hk, hk2, h⟩
    · rw [if_neg hk2] at h
      exact absurd h Bool.false_ne_true
  · rintro ⟨k, hk, hk2, h⟩
    exact ⟨k, hk, by rw [if_pos hk2]; exact h⟩

/-! ## The cost function and the charge -/

def c : ℕ → ℕ
  | n => if h : n < 2 then 0 else
      2 ^ n + (Finset.univ : Finset (Fin (n - 1))).inf' ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
        (fun a => c (a.val + 1) + c (n - (a.val + 1)))
decreasing_by all_goals (have := a.isLt; omega)

theorem c_small (n : ℕ) (h : n < 2) : c n = 0 := by
  rw [c]; simp [h]

theorem c_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : c (a + b) ≤ 2 ^ (a + b) + c a + c b := by
  rw [c, dif_neg (by omega)]
  have := Finset.inf'_le (fun x : Fin (a + b - 1) => c (x.val + 1) + c (a + b - (x.val + 1)))
    (Finset.mem_univ ⟨a - 1, by omega⟩)
  simp only at this
  rw [show a - 1 + 1 = a by omega, show a + b - a = b by omega] at this
  omega

theorem c_eq (n : ℕ) (h : 2 ≤ n) :
    ∃ a b, 0 < a ∧ 0 < b ∧ a + b = n ∧ c n = 2 ^ n + c a + c b := by
  rw [c, dif_neg (by omega)]
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_inf' (⟨⟨0, by omega⟩, Finset.mem_univ _⟩ :
    (Finset.univ : Finset (Fin (n - 1))).Nonempty)
    (fun a => c (a.val + 1) + c (n - (a.val + 1)))
  refine ⟨x.val + 1, n - (x.val + 1), by omega, by have := x.isLt; omega, by
    have := x.isLt; omega, ?_⟩
  rw [hx]
  ring

def f (k : ℕ) : ℕ := if 2 ≤ k then 2 ^ k else 0

theorem f_mono (a b : ℕ) (h : a ≤ b) : f a ≤ f b := by
  unfold f
  split_ifs
  all_goals first
    | exact Nat.pow_le_pow_right (by norm_num) h
    | exact Nat.zero_le _
    | omega

theorem f_super (a b : ℕ) : f a + f b ≤ f (a + b) := by
  by_cases ha : 2 ≤ a
  · by_cases hb : 2 ≤ b
    · unfold f
      rw [if_pos ha, if_pos hb, if_pos (by omega), pow_add]
      have h1 : 2 ≤ 2 ^ a := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ≤ 2 ^ b := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
    · have : f b = 0 := by unfold f; rw [if_neg hb]
      rw [this, Nat.add_zero]
      exact f_mono _ _ (by omega)
  · have : f a = 0 := by unfold f; rw [if_neg ha]
    rw [this, Nat.zero_add]
    exact f_mono _ _ (by omega)

theorem c_split (a b : ℕ) : c (a + b) ≤ f (a + b) + c a + c b := by
  by_cases ha : a = 0
  · subst ha; rw [c_small 0 (by norm_num)]; simp
  by_cases hb : b = 0
  · subst hb; rw [c_small 0 (by norm_num)]; simp
  have := c_le a b (by omega) (by omega)
  unfold f
  rw [if_pos (by omega)]
  exact this

def Wt (C : Circuit) (n w : ℕ) (B : Finset (Fin n)) : ℕ :=
  ∑ z ∈ (Finset.range (w + 1)).filter (fun z => n ≤ z ∧ supp C n z ⊆ supp C n w),
    f (supp C n z ∩ B).card

theorem helper (C : Circuit) (n w p q : ℕ) (hn : n ≤ w) (hp : p < w) (hq : q < w)
    (hpq : supp C n w = supp C n p ∪ supp C n q)
    (ihp : ∀ B ⊆ supp C n p, c B.card ≤ Wt C n p B)
    (ihq : ∀ B ⊆ supp C n q, c B.card ≤ Wt C n q B)
    (B : Finset (Fin n)) (hB : B ⊆ supp C n w) : c B.card ≤ Wt C n w B := by
  have hcard : ∀ X : Finset (Fin n), (X ∩ B.filter (· ∈ supp C n p)).card +
      (X ∩ B.filter (fun i => ¬ i ∈ supp C n p)).card = (X ∩ B).card := by
    intro X
    rw [Finset.inter_filter, Finset.inter_filter]
    exact Finset.card_filter_add_card_filter_not _
  have hsp : supp C n p ⊆ supp C n w := hpq ▸ Finset.subset_union_left
  have hsq : supp C n q ⊆ supp C n w := hpq ▸ Finset.subset_union_right
  have hB1 : B.filter (· ∈ supp C n p) ⊆ supp C n p := fun i hi => (Finset.mem_filter.1 hi).2
  have hB2 : B.filter (fun i => ¬ i ∈ supp C n p) ⊆ supp C n q := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have := hB hi.1
    rw [hpq, Finset.mem_union] at this
    tauto
  have hW : Wt C n w B = f B.card + ∑ z ∈ (Finset.range w).filter
      (fun z => n ≤ z ∧ supp C n z ⊆ supp C n w), f (supp C n z ∩ B).card := by
    unfold Wt
    rw [Finset.range_add_one, Finset.filter_insert, if_pos ⟨hn, subset_rfl⟩,
      Finset.sum_insert (by simp), Finset.inter_eq_right.2 hB]
  have hsub : ∀ m, m < w → supp C n m ⊆ supp C n w →
      (Finset.range (m + 1)).filter (fun z => n ≤ z ∧ supp C n z ⊆ supp C n m) ⊆
        (Finset.range w).filter (fun z => n ≤ z ∧ supp C n z ⊆ supp C n w) := by
    intro m hm hs z hz
    simp only [Finset.mem_filter, Finset.mem_range] at hz ⊢
    exact ⟨by omega, hz.2.1, hz.2.2.trans hs⟩
  have h1 := Finset.sum_le_sum_of_subset (f := fun z => f (supp C n z ∩
    B.filter (· ∈ supp C n p)).card) (hsub p hp hsp)
  have h2 := Finset.sum_le_sum_of_subset (f := fun z => f (supp C n z ∩
    B.filter (fun i => ¬ i ∈ supp C n p)).card) (hsub q hq hsq)
  have h3 : ∑ z ∈ (Finset.range w).filter (fun z => n ≤ z ∧ supp C n z ⊆ supp C n w),
      f (supp C n z ∩ B.filter (· ∈ supp C n p)).card +
      ∑ z ∈ (Finset.range w).filter (fun z => n ≤ z ∧ supp C n z ⊆ supp C n w),
      f (supp C n z ∩ B.filter (fun i => ¬ i ∈ supp C n p)).card ≤
      ∑ z ∈ (Finset.range w).filter (fun z => n ≤ z ∧ supp C n z ⊆ supp C n w),
      f (supp C n z ∩ B).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro z _
    rw [← hcard]
    exact f_super _ _
  have h4 := c_split (B.filter (· ∈ supp C n p)).card
    (B.filter (fun i => ¬ i ∈ supp C n p)).card
  rw [Finset.card_filter_add_card_filter_not] at h4
  have h5 := ihp _ hB1
  have h6 := ihq _ hB2
  unfold Wt at h5 h6
  rw [hW]
  omega

theorem claim (C : Circuit) (n : ℕ) (hor : ∀ g ∈ C.gates, g.op = GateOp.or)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∀ w, ∀ B ⊆ supp C n w, c B.card ≤ Wt C n w B := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro B hB
  by_cases hw : w < n
  · have : B.card ≤ 1 := by
      apply Finset.card_le_one.2
      intro x hx y hy
      exact Fin.ext ((supp_input C n w hw x (hB hx)).trans
        (supp_input C n w hw y (hB hy)).symm)
    rw [c_small _ (by omega)]
    exact Nat.zero_le _
  by_cases hw2 : n + C.gates.length ≤ w
  · rw [supp_big C n w hw2, Finset.subset_empty] at hB
    subst hB
    rw [Finset.card_empty, c_small 0 (by norm_num)]
    exact Nat.zero_le _
  obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
  have hj : j < C.gates.length := by omega
  have key := supp_gate C n hor j hj
  have hlen := hfan _ (List.getElem_mem hj)
  have hcase : supp C n (n + j) = ∅ ∨ ∃ p q, p < n + j ∧ q < n + j ∧
      supp C n (n + j) = supp C n p ∪ supp C n q := by
    generalize (C.gates[j]'hj).inputs = l at key hlen
    rcases l with _ | ⟨p, _ | ⟨q, _ | ⟨t, l⟩⟩⟩
    · left; ext i; simp [key]
    · by_cases hp : p < n + j
      · right; exact ⟨p, p, hp, hp, by ext i; simp [key, hp]⟩
      · left; ext i; simp [key, hp]
    · by_cases hp : p < n + j <;> by_cases hq : q < n + j
      · right; exact ⟨p, q, hp, hq, by ext i; simp [key, hp, hq]⟩
      · right; exact ⟨p, p, hp, hp, by ext i; simp [key, hp, hq]⟩
      · right; exact ⟨q, q, hq, hq, by ext i; simp [key, hp, hq]⟩
      · left; ext i; simp [key, hp, hq]
    · simp at hlen
  rcases hcase with h0 | ⟨p, q, hp, hq, hpq⟩
  · rw [h0, Finset.subset_empty] at hB
    subst hB
    rw [Finset.card_empty, c_small 0 (by norm_num)]
    exact Nat.zero_le _
  · exact helper C n (n + j) p q (by omega) hp hq hpq (ih p hp) (ih q hq) B hB

/-! ## Counting targets -/

def S (r : ℕ) (x : Fin (2 ^ r)) : Finset (Fin (2 * r)) :=
  Finset.univ.filter fun i => (Nat.testBit x.val (i.val / 2) == decide (i.val % 2 = 1)) = true

theorem mem_S (r : ℕ) (x : Fin (2 ^ r)) (i : Fin (2 * r)) :
    i ∈ S r x ↔ Nat.testBit x.val (i.val / 2) = decide (i.val % 2 = 1) := by
  simp [S]

theorem S_card (r : ℕ) (x : Fin (2 ^ r)) : (S r x).card = r := by
  have : (S r x).card = (Finset.univ : Finset (Fin r)).card := by
    apply Finset.card_nbij' (fun i => (⟨i.val / 2, by have := i.isLt; omega⟩ : Fin r))
      (fun j => (⟨2 * j.val + (if Nat.testBit x.val j.val then 1 else 0),
        by have := j.isLt; split_ifs <;> omega⟩ : Fin (2 * r)))
    · intro i _
      simp
    · intro j _
      simp only [Finset.coe_univ, Set.mem_univ, Finset.mem_coe] at *
      rw [mem_S]
      by_cases hb : Nat.testBit x.val j.val = true
      · simp only [hb, if_true]
        rw [show (2 * j.val + 1) / 2 = j.val by omega, show (2 * j.val + 1) % 2 = 1 by omega]
        simp [hb]
      · simp only [hb]
        simp only [Bool.false_eq_true, if_false, Nat.add_zero]
        rw [show (2 * j.val) / 2 = j.val by omega, show (2 * j.val) % 2 = 0 by omega]
        simpa using hb
    · intro i hi
      simp only [Finset.mem_coe] at hi
      rw [mem_S] at hi
      apply Fin.ext
      simp only
      rw [hi]
      by_cases h : i.val % 2 = 1
      · simp [h]; omega
      · simp [h]; omega
    · intro j _
      apply Fin.ext
      simp only
      split_ifs <;> omega
  simpa using this

def flp (r k : ℕ) (hk : k < r) (x : Fin (2 ^ r)) : Fin (2 ^ r) :=
  ⟨x.val ^^^ 2 ^ k, Nat.xor_lt_two_pow x.isLt (Nat.pow_lt_pow_right (by norm_num) hk)⟩

theorem flp_flp (r k : ℕ) (hk : k < r) (x : Fin (2 ^ r)) : flp r k hk (flp r k hk x) = x := by
  apply Fin.ext
  simp [flp, Nat.xor_assoc]

theorem mem_S_flp (r : ℕ) (i : Fin (2 * r)) (hk : i.val / 2 < r) (x : Fin (2 ^ r))
    (i' : Fin (2 * r)) :
    i' ∈ S r (flp r _ hk x) ↔ (if i'.val / 2 = i.val / 2 then ¬ i' ∈ S r x else i' ∈ S r x) := by
  rw [mem_S, mem_S]
  simp only [flp]
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  split_ifs with h
  · rw [h]
    simp only [decide_true]
    generalize Nat.testBit x.val (i.val / 2) = b
    generalize decide (i'.val % 2 = 1) = d
    cases b <;> cases d <;> simp
  · have : decide (i.val / 2 = i'.val / 2) = false := by
      simp only [decide_eq_false_iff_not]; omega
    rw [this, Bool.xor_false]

theorem count_eq (r : ℕ) (x0 : Fin (2 ^ r)) (A : Finset (Fin (2 * r))) (hA : A ⊆ S r x0) :
    (Finset.univ.filter fun x => A ⊆ S r x).card * 2 ^ A.card = 2 ^ r := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert i A hi ih =>
    have hA' : A ⊆ S r x0 := (Finset.subset_insert _ _).trans hA
    have hiS : i ∈ S r x0 := hA (Finset.mem_insert_self _ _)
    specialize ih hA'
    have hk : i.val / 2 < r := by have := i.isLt; omega
    have hdiff : ∀ i' ∈ A, i'.val / 2 ≠ i.val / 2 := by
      intro i' hi' heq
      have h1 := (mem_S _ _ _).1 (hA' hi')
      have h2 := (mem_S _ _ _).1 hiS
      rw [heq, h2] at h1
      have h3 : i'.val % 2 = i.val % 2 := by
        by_cases a1 : i'.val % 2 = 1 <;> by_cases a2 : i.val % 2 = 1 <;> simp [a1, a2] at h1 <;>
          omega
      have : i' = i := Fin.ext (by omega)
      exact hi (this ▸ hi')
    have hT' : (Finset.univ.filter fun x => insert i A ⊆ S r x) =
        (Finset.univ.filter fun x => A ⊆ S r x).filter (fun x => i ∈ S r x) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.insert_subset_iff]
      tauto
    have hAflp : ∀ x, A ⊆ S r (flp r _ hk x) ↔ A ⊆ S r x := by
      intro x
      constructor
      · intro h i' hi'
        have := h hi'
        rw [mem_S_flp, if_neg (hdiff i' hi')] at this
        exact this
      · intro h i' hi'
        rw [mem_S_flp, if_neg (hdiff i' hi')]
        exact h hi'
    have hiflp : ∀ x, i ∈ S r (flp r _ hk x) ↔ ¬ i ∈ S r x := by
      intro x
      rw [mem_S_flp, if_pos rfl]
    have hbij : ((Finset.univ.filter fun x => A ⊆ S r x).filter
        (fun x => ¬ i ∈ S r x)).card =
        ((Finset.univ.filter fun x => A ⊆ S r x).filter (fun x => i ∈ S r x)).card := by
      apply Finset.card_nbij' (flp r _ hk) (flp r _ hk)
      · intro x hx
        simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq] at hx ⊢
        exact ⟨(hAflp x).2 hx.1, (hiflp x).2 hx.2⟩
      · intro x hx
        simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq] at hx ⊢
        exact ⟨(hAflp x).2 hx.1, fun h => ((hiflp x).1 h) hx.2⟩
      · intro x _
        exact flp_flp r _ hk x
      · intro x _
        exact flp_flp r _ hk x
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter fun x => A ⊆ S r x) (fun x => i ∈ S r x)
    rw [hT', Finset.card_insert_of_notMem hi, pow_succ]
    rw [← hsplit, hbij] at ih
    linarith

theorem count_le (r : ℕ) (A : Finset (Fin (2 * r))) :
    (Finset.univ.filter fun x => A ⊆ S r x).card * 2 ^ A.card ≤ 2 ^ r := by
  by_cases h : ∃ x0, A ⊆ S r x0
  · obtain ⟨x0, hx0⟩ := h
    exact (count_eq r x0 A hx0).le
  · push_neg at h
    have : (Finset.univ.filter fun x => A ⊆ S r x) = ∅ := by
      ext x
      simp [h x]
    rw [this]
    simp

/-! ## The lower bound -/

theorem lower (r : ℕ) (hr : 1 ≤ r) (C : Circuit) (hor : ∀ g ∈ C.gates, g.op = GateOp.or)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (o : Fin (2 ^ r) → ℕ)
    (ho : ∀ x, supp C (2 * r) (o x) = S r x) : c r ≤ C.gates.length := by
  have hlt : ∀ x, o x < 2 * r + C.gates.length := by
    intro x
    by_contra hc
    have h1 := supp_big C (2 * r) (o x) (by omega)
    rw [ho x] at h1
    have h2 := S_card r x
    rw [h1, Finset.card_empty] at h2
    omega
  have hx : ∀ x, c r ≤ ∑ z ∈ (Finset.Ico (2 * r) (2 * r + C.gates.length)).filter
      (fun z => supp C (2 * r) z ⊆ S r x), 2 ^ (supp C (2 * r) z).card := by
    intro x
    have := claim C (2 * r) hor hfan (o x) (S r x) (by rw [ho x])
    rw [S_card] at this
    refine this.trans ?_
    unfold Wt
    rw [ho x]
    calc ∑ z ∈ (Finset.range (o x + 1)).filter
          (fun z => 2 * r ≤ z ∧ supp C (2 * r) z ⊆ S r x), f (supp C (2 * r) z ∩ S r x).card
        ≤ ∑ z ∈ (Finset.range (o x + 1)).filter
          (fun z => 2 * r ≤ z ∧ supp C (2 * r) z ⊆ S r x), 2 ^ (supp C (2 * r) z).card := by
          apply Finset.sum_le_sum
          intro z hz
          rw [Finset.mem_filter] at hz
          rw [Finset.inter_eq_left.2 hz.2.2]
          unfold f
          split_ifs
          · exact le_rfl
          · exact Nat.zero_le _
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset
          intro z hz
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hz ⊢
          have := hlt x
          exact ⟨⟨hz.2.1, by omega⟩, hz.2.2⟩
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (2 ^ r)))) (fun x _ => hx x)
  simp only [Finset.sum_filter] at hsum
  rw [Finset.sum_comm] at hsum
  have h2 : ∀ z ∈ Finset.Ico (2 * r) (2 * r + C.gates.length),
      ∑ x : Fin (2 ^ r), (if supp C (2 * r) z ⊆ S r x then 2 ^ (supp C (2 * r) z).card else 0)
        ≤ 2 ^ r := by
    intro z _
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    exact count_le r _
  have h3 := Finset.sum_le_sum h2
  rw [Finset.sum_const, smul_eq_mul, Nat.card_Ico] at h3
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_fin] at hsum
  have h4 : 2 ^ r * c r ≤ 2 ^ r * C.gates.length := by
    have := hsum.trans h3
    rw [show 2 * r + C.gates.length - 2 * r = C.gates.length by omega] at this
    linarith
  exact Nat.le_of_mul_le_mul_left h4 (by positivity)

/-! ## The construction -/

def Dec (r budget : ℕ) : Prop :=
  ∃ C : Circuit, C.size ≤ budget ∧
    (∀ g ∈ C.gates, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧
    ∀ x : Fin (2 ^ r), ∃ w : ℕ, ∀ i : Fin (2 * r),
      (C.wires (List.ofFn (fun h : Fin (2 * r) => decide (h = i)))).getD w false =
        (Nat.testBit x.val (i.val / 2) == decide (i.val % 2 = 1))

theorem base : Dec 1 0 := by
  refine ⟨⟨[], 0⟩, le_rfl, by simp, fun x => ⟨x.val, ?_⟩⟩
  revert x
  decide

theorem out_lt (r : ℕ) (hr : 1 ≤ r) (C : Circuit) (y : Fin (2 ^ r)) (w : ℕ)
    (hw : ∀ i : Fin (2 * r),
      (C.wires (List.ofFn (fun h : Fin (2 * r) => decide (h = i)))).getD w false =
        (Nat.testBit y.val (i.val / 2) == decide (i.val % 2 = 1))) :
    w < 2 * r + C.gates.length := by
  by_contra hc
  have hgd : ∀ i : Fin (2 * r),
      (C.wires (List.ofFn (fun h : Fin (2 * r) => decide (h = i)))).getD w false = false := by
    intro i
    rw [wires_eq]
    exact getD_ge _ _ (by rw [len_fold, List.length_ofFn]; omega)
  cases hbit : Nat.testBit y.val 0
  · have := hw ⟨0, by omega⟩
    rw [hgd] at this
    simp [hbit] at this
  · have := hw ⟨1, by omega⟩
    rw [hgd] at this
    simp [hbit] at this

theorem ofFn_getD (m : ℕ) (g : Fin m → Bool) (k : ℕ) :
    (List.ofFn g).getD k false = if h : k < m then g ⟨k, h⟩ else false := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · exact getD_ge _ _ (by simp; omega)

theorem combine (a b u v : ℕ) (ha : 0 < a) (hb : 0 < b) (h1 : Dec a u) (h2 : Dec b v) :
    Dec (a + b) (2 ^ (a + b) + u + v) := by
  obtain ⟨C1, hs1, hg1, ho1⟩ := h1
  obtain ⟨C2, hs2, hg2, ho2⟩ := h2
  choose o1 ho1 using ho1
  choose o2 ho2 using ho2
  have hb1 : ∀ y, o1 y < 2 * a + C1.gates.length := fun y => out_lt a ha C1 y _ (ho1 y)
  have hb2 : ∀ y, o2 y < 2 * b + C2.gates.length := fun y => out_lt b hb C2 y _ (ho2 y)
  have hor1 : ∀ g ∈ C1.gates, g.op = GateOp.or := fun g hg => (hg1 g hg).1
  have hor2 : ∀ g ∈ C2.gates, g.op = GateOp.or := fun g hg => (hg2 g hg).1
  let ψ1 : ℕ → ℕ := fun k => if k < 2 * a then k else k + 2 * b
  let ψ2 : ℕ → ℕ := fun k => if k < 2 * b then k + 2 * a else k + 2 * a + C1.gates.length
  let o1' : ℕ → ℕ := fun x => o1 ⟨x % 2 ^ a, Nat.mod_lt _ (by positivity)⟩
  let o2' : ℕ → ℕ := fun y => if h : y < 2 ^ b then o2 ⟨y, h⟩ else 0
  let outs : List Gate := (List.range (2 ^ (a + b))).map fun x =>
    ⟨GateOp.or, [ψ1 (o1' x), ψ2 (o2' (x / 2 ^ a))]⟩
  refine ⟨⟨C1.gates.map (mapG ψ1) ++ C2.gates.map (mapG ψ2) ++ outs, 0⟩, ?_, ?_, ?_⟩
  · simp only [Circuit.size, List.length_append, List.length_map, List.length_range, outs]
      at hs1 hs2 ⊢
    omega
  · intro g hg
    simp only [List.mem_append, List.mem_map, outs] at hg
    rcases hg with (⟨g1, hg1', rfl⟩ | ⟨g2, hg2', rfl⟩) | ⟨x, _, rfl⟩
    · exact ⟨(hg1 g1 hg1').1, by simpa [mapG] using (hg1 g1 hg1').2⟩
    · exact ⟨(hg2 g2 hg2').1, by simpa [mapG] using (hg2 g2 hg2').2⟩
    · exact ⟨rfl, by simp⟩
  · intro x
    refine ⟨2 * (a + b) + C1.gates.length + C2.gates.length + x.val, fun i => ?_⟩
    rw [wires_eq]
    simp only [List.foldl_append]
    have hE : (List.ofFn (fun h : Fin (2 * (a + b)) => decide (h = i))).length =
        2 * (a + b) := by simp
    have hEget : ∀ k < 2 * (a + b),
        (List.ofFn (fun h : Fin (2 * (a + b)) => decide (h = i))).getD k false =
          decide (k = i.val) := by
      intro k hk
      rw [ofFn_getD, dif_pos hk]
      simp [Fin.ext_iff]
    have hL1 : (List.foldl step (List.ofFn (fun h : Fin (2 * (a + b)) => decide (h = i)))
        (C1.gates.map (mapG ψ1))).length = 2 * (a + b) + C1.gates.length := by
      rw [len_fold, hE, List.length_map]
    have hL2 : (List.foldl step (List.foldl step
        (List.ofFn (fun h : Fin (2 * (a + b)) => decide (h = i)))
        (C1.gates.map (mapG ψ1))) (C2.gates.map (mapG ψ2))).length =
          2 * (a + b) + C1.gates.length + C2.gates.length := by
      rw [len_fold, hL1, List.length_map]
    have hs1' := sim ψ1 C1.gates (List.ofFn (fun h : Fin (2 * a) => decide (h.val = i.val)))
      (List.ofFn (fun h : Fin (2 * (a + b)) => decide (h = i))) (by
        intro k hk
        rw [List.length_ofFn] at hk
        simp only [ψ1, if_pos hk]
        refine ⟨by omega, ?_⟩
        rw [hEget k (by omega), ofFn_getD, dif_pos hk])
      (by
        intro j
        rw [List.length_ofFn, hE]
        simp only [ψ1]
        rw [if_neg (by omega)]
        omega)
    have hs2' := sim ψ2 C2.gates
      (List.ofFn (fun h : Fin (2 * b) => decide (h.val + 2 * a = i.val)))
      (List.foldl step (List.ofFn (fun h : Fin (2 * (a + b)) => decide (h = i)))
        (C1.gates.map (mapG ψ1))) (by
        intro k hk
        rw [List.length_ofFn] at hk
        simp only [ψ2, if_pos hk]
        refine ⟨by omega, ?_⟩
        rw [prefix_fold _ _ _ (by omega), hEget _ (by omega), ofFn_getD, dif_pos hk])
      (by
        intro j
        rw [List.length_ofFn, hL1]
        simp only [ψ2]
        rw [if_neg (by omega)]
        omega)
    have hxlt : x.val < outs.length := by simp [outs]
    have hgx : outs[x.val]'hxlt = ⟨GateOp.or, [ψ1 (o1' x.val), ψ2 (o2' (x.val / 2 ^ a))]⟩ := by
      simp [outs]
    have hy : x.val / 2 ^ a < 2 ^ b := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_comm b a]
      exact x.isLt
    have hk1 : o1' x.val < 2 * a + C1.gates.length := hb1 _
    have hk2 : o2' (x.val / 2 ^ a) < 2 * b + C2.gates.length := by
      simp only [o2', dif_pos hy]
      exact hb2 _
    have hq1 : ψ1 (o1' x.val) < 2 * (a + b) + C1.gates.length := by
      simp only [ψ1]
      split_ifs <;> omega
    have hq2 : ψ2 (o2' (x.val / 2 ^ a)) < 2 * (a + b) + C1.gates.length + C2.gates.length := by
      simp only [ψ2]
      split_ifs <;> omega
    generalize List.foldl step (List.ofFn (fun h : Fin (2 * (a + b)) => decide (h = i)))
      (C1.gates.map (mapG ψ1)) = L1 at hL1 hL2 hs1' hs2' ⊢
    have v1 : (List.foldl step L1 (C2.gates.map (mapG ψ2))).getD (ψ1 (o1' x.val)) false =
        L1.getD (ψ1 (o1' x.val)) false := prefix_fold _ _ _ (by rw [hL1]; exact hq1)
    generalize List.foldl step L1 (C2.gates.map (mapG ψ2)) = L2 at hL2 hs2' v1 ⊢
    rw [show 2 * (a + b) + C1.gates.length + C2.gates.length + x.val = L2.length + x.val by
      omega, at_fold outs L2 x.val hxlt, hgx]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      Bool.or_false, id_eq]
    rw [if_pos (show ψ1 (o1' x.val) < L2.length + x.val by omega),
      if_pos (show ψ2 (o2' (x.val / 2 ^ a)) < L2.length + x.val by omega),
      prefix_fold outs L2 (ψ1 (o1' x.val)) (by omega),
      prefix_fold outs L2 (ψ2 (o2' (x.val / 2 ^ a))) (by omega), v1,
      hs1' (o1' x.val) (by rw [List.length_ofFn]; exact hk1),
      hs2' (o2' (x.val / 2 ^ a)) (by rw [List.length_ofFn]; exact hk2)]
    by_cases hi : i.val < 2 * a
    · have hE2f : ∀ k, (List.ofFn (fun h : Fin (2 * b) =>
          decide (h.val + 2 * a = i.val))).getD k false = false := by
        intro k
        rw [ofFn_getD]
        split_ifs
        · simp only [decide_eq_false_iff_not]
          omega
        · rfl
      rw [allfalse C2.gates hor2 _ hE2f, Bool.or_false]
      have hE1 : (List.ofFn (fun h : Fin (2 * a) => decide (h.val = i.val))) =
          List.ofFn (fun h : Fin (2 * a) => decide (h = (⟨i.val, hi⟩ : Fin (2 * a)))) := by
        congr 1
      have := ho1 ⟨x.val % 2 ^ a, Nat.mod_lt _ (by positivity)⟩ ⟨i.val, hi⟩
      rw [wires_eq] at this
      rw [hE1]
      simp only [o1']
      rw [this]
      simp only [Nat.testBit_mod_two_pow]
      have : i.val / 2 < a := by omega
      simp [this]
    · have hE1f : ∀ k, (List.ofFn (fun h : Fin (2 * a) =>
          decide (h.val = i.val))).getD k false = false := by
        intro k
        rw [ofFn_getD]
        split_ifs
        · simp only [decide_eq_false_iff_not]
          omega
        · rfl
      rw [allfalse C1.gates hor1 _ hE1f, Bool.false_or]
      have hi2 : i.val - 2 * a < 2 * b := by have := i.isLt; omega
      have hE2 : List.ofFn (fun h : Fin (2 * b) => decide (h.val + 2 * a = i.val)) =
          List.ofFn (fun h : Fin (2 * b) =>
            decide (h = (⟨i.val - 2 * a, hi2⟩ : Fin (2 * b)))) := by
        congr 1
        funext h
        apply Bool.eq_iff_iff.2
        simp only [decide_eq_true_eq, Fin.ext_iff]
        constructor <;> intro <;> omega
      have := ho2 ⟨x.val / 2 ^ a, hy⟩ ⟨i.val - 2 * a, hi2⟩
      rw [wires_eq] at this
      rw [hE2]
      simp only [o2', dif_pos hy]
      rw [this]
      simp only [Nat.testBit_div_two_pow]
      rw [show (i.val - 2 * a) / 2 + a = i.val / 2 by omega,
        show (i.val - 2 * a) % 2 = i.val % 2 by omega]

theorem mono (r s t : ℕ) (h : Dec r s) (hst : s ≤ t) : Dec r t := by
  obtain ⟨C, h1, h2, h3⟩ := h
  exact ⟨C, h1.trans hst, h2, h3⟩

theorem upper : ∀ n, 1 ≤ n → Dec n (c n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  by_cases h1 : n = 1
  · subst h1
    rw [c_small 1 (by norm_num)]
    exact base
  · obtain ⟨a, b, ha, hb, hab, hc⟩ := c_eq n (by omega)
    rw [hc, ← hab]
    exact combine a b _ _ ha hb (ih a (by omega) ha) (ih b (by omega) hb)

theorem lower_dec (r s : ℕ) (hr : 1 ≤ r) (h : Dec r s) : c r ≤ s := by
  obtain ⟨C, hs, hg, ho⟩ := h
  choose o ho using ho
  have hsupp : ∀ x, supp C (2 * r) (o x) = S r x := by
    intro x
    ext i
    rw [mem_supp, mem_S]
    have := ho x i
    rw [wires_eq] at this
    show (List.foldl step (List.ofFn fun h : Fin (2 * r) => decide (h = i)) C.gates).getD
      (o x) false = true ↔ _
    rw [this]
    simp
  exact (lower r hr C (fun g hg' => (hg g hg').1) (fun g hg' => (hg g hg').2) o hsupp).trans hs

end PEqualNP.Outside.L_lib_722

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_lib_722 in
theorem PEqualNP.Outside.L_lib_722 :
    let dec := fun (r budget : ℕ) =>
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ budget ∧
        (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2) ∧
        ∀ x : Fin (2 ^ r), ∃ w : ℕ, ∀ i : Fin (2 * r),
          (C.wires (List.ofFn (fun h : Fin (2 * r) => decide (h = i)))).getD w false =
            (Nat.testBit x.val (i.val / 2) == decide (i.val % 2 = 1))
    dec 1 0 ∧ ∀ r s : ℕ, 2 ≤ r →
      (dec r s ↔ ∃ a b u v : ℕ,
        0 < a ∧ 0 < b ∧ a + b = r ∧ dec a u ∧ dec b v ∧ 2 ^ r + u + v ≤ s) := by
  intro dec
  refine ⟨base, fun r s hr => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hc := lower_dec r s (by omega) h
    obtain ⟨a, b, ha, hb, hab, hceq⟩ := c_eq r hr
    exact ⟨a, b, c a, c b, ha, hb, hab, upper a ha, upper b hb, by omega⟩
  · obtain ⟨a, b, u, v, ha, hb, hab, hu, hv, hs⟩ := h
    subst hab
    exact mono _ _ _ (combine a b u v ha hb hu hv) hs
