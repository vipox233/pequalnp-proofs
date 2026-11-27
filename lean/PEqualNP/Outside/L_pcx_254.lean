import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_254_aux
open Finset

variable {n : ℕ}

def Agree (x : Fin n → Bool) (C : Finset (Fin n × Bool)) : Prop := ∀ p ∈ C, x p.1 = p.2

instance (x : Fin n → Bool) (C : Finset (Fin n × Bool)) : Decidable (Agree x C) := by
  unfold Agree; infer_instance

def Cons (C : Finset (Fin n × Bool)) : Prop := ∀ i : Fin n, ¬ ((i, false) ∈ C ∧ (i, true) ∈ C)

theorem agree_insert {x : Fin n → Bool} {q : Fin n × Bool} {C : Finset (Fin n × Bool)} :
    Agree x (insert q C) ↔ x q.1 = q.2 ∧ Agree x C := by
  simp [Agree]

theorem count_agree (C : Finset (Fin n × Bool)) : Cons C →
    (univ.filter (fun x : Fin n → Bool => Agree x C)).card * 2 ^ C.card = 2 ^ n := by
  induction C using Finset.induction_on with
  | empty =>
    intro _
    simp [Agree]
  | @insert q C hq ih =>
    intro hc
    obtain ⟨i, a⟩ := q
    have hC : Cons C := fun j hj => hc j ⟨mem_insert_of_mem hj.1, mem_insert_of_mem hj.2⟩
    have hna : (i, !a) ∉ C := by
      intro h
      cases a
      · exact hc i ⟨mem_insert_self _ _, mem_insert_of_mem h⟩
      · exact hc i ⟨mem_insert_of_mem h, mem_insert_self _ _⟩
    have hvar : ∀ p ∈ C, p.1 ≠ i := by
      rintro ⟨j, v⟩ hp hj
      simp only at hj
      subst hj
      by_cases hv : v = a
      · subst hv; exact hq hp
      · have : v = !a := by cases v <;> cases a <;> simp_all
        subst this; exact hna hp
    set S := univ.filter (fun x : Fin n → Bool => Agree x C)
    set T := univ.filter (fun x : Fin n → Bool => Agree x (insert (i, a) C))
    have hT : T = S.filter (fun x => x i = a) := by
      ext x; simp [T, S, agree_insert, and_comm]
    have hS := Finset.card_filter_add_card_filter_not (s := S) (fun x : Fin n → Bool => x i = a)
    have hflip : (S.filter (fun x => ¬ x i = a)).card = (S.filter (fun x => x i = a)).card := by
      apply Finset.card_bij (fun x _ => Function.update x i (!x i))
      · intro x hx
        simp only [S, mem_filter, mem_univ, true_and] at hx ⊢
        refine ⟨?_, ?_⟩
        · intro p hp
          rw [Function.update_of_ne (hvar p hp)]
          exact hx.1 p hp
        · simp only [Function.update_self]
          cases h : x i <;> cases a <;> simp_all
      · intro x hx y hy hxy
        have h1 := congrFun hxy i
        simp only [Function.update_self, Bool.not_inj_iff] at h1
        funext j
        by_cases hj : j = i
        · subst hj; exact h1
        · have := congrFun hxy j
          rwa [Function.update_of_ne hj, Function.update_of_ne hj] at this
      · intro y hy
        simp only [S, mem_filter, mem_univ, true_and] at hy
        refine ⟨Function.update y i (!y i), ?_, ?_⟩
        · simp only [S, mem_filter, mem_univ, true_and]
          refine ⟨?_, ?_⟩
          · intro p hp
            rw [Function.update_of_ne (hvar p hp)]
            exact hy.1 p hp
          · simp [hy.2]
        · funext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_of_ne hj]
    rw [card_insert_of_notMem hq, pow_succ, ← ih hC, hT]
    rw [← hS, hflip]
    ring

theorem agree_card (C : Finset (Fin n × Bool)) (hc : Cons C) :
    C.card ≤ n ∧ (univ.filter (fun x : Fin n → Bool => Agree x C)).card = 2 ^ (n - C.card) := by
  have h := count_agree C hc
  set k := (univ.filter (fun x : Fin n → Bool => Agree x C)).card
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, zero_mul] at h; exact absurd h.symm (by positivity)
    · exact h0
  have hle : C.card ≤ n := by
    have : 2 ^ C.card ≤ 2 ^ n := by rw [← h]; exact Nat.le_mul_of_pos_left _ hk
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  refine ⟨hle, ?_⟩
  have h2 : 2 ^ n = 2 ^ (n - C.card) * 2 ^ C.card := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

theorem kraft (L : Finset (Finset (Fin n × Bool))) (hc : ∀ C ∈ L, Cons C)
    (hp : ∀ x : Fin n → Bool, (L.filter (fun C => Agree x C)).card = 1) :
    ∑ C ∈ L, 2 ^ (n - C.card) = 2 ^ n := by
  calc ∑ C ∈ L, 2 ^ (n - C.card)
      = ∑ C ∈ L, (univ.filter (fun x : Fin n → Bool => Agree x C)).card :=
        sum_congr rfl (fun C h => ((agree_card C (hc C h)).2).symm)
    _ = ∑ C ∈ L, ∑ x : Fin n → Bool, if Agree x C then 1 else 0 := by
        simp only [card_filter]
    _ = ∑ x : Fin n → Bool, ∑ C ∈ L, if Agree x C then 1 else 0 := sum_comm
    _ = ∑ x : Fin n → Bool, 1 := sum_congr rfl (fun x _ => by rw [← card_filter]; exact hp x)
    _ = 2 ^ n := by simp

theorem key_ineq (w h : ℕ) : (h + 1) * 2 ^ w ≤ w * 2 ^ w + 2 ^ h := by
  rcases Nat.lt_or_ge h w with hw | hw
  · have : (h + 1) * 2 ^ w ≤ w * 2 ^ w := Nat.mul_le_mul_right _ hw
    exact Nat.le_add_right_of_le this
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hw
    have hk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
    rw [pow_add]
    nlinarith [Nat.mul_le_mul_left (2 ^ w) hk]

theorem two_mul_le_two_pow (n : ℕ) : 2 * n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · rw [pow_succ]; have : 1 ≤ 2 ^ m := Nat.one_le_two_pow; omega

section Words
variable (hn : 0 < n) (f : Fin n → Bool)

def nxt (k : Fin n) : Fin n := ⟨(k.val + 1) % n, Nat.mod_lt _ hn⟩

theorem nxt_val (k : Fin n) : (nxt hn k).val = if k.val + 1 < n then k.val + 1 else 0 := by
  unfold nxt
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have : k.val + 1 = n := by omega
    simp [this]

def idx (i : Fin n) (m : ℕ) : ℕ := if i.val + 1 + m < n then i.val + 1 + m else i.val + 1 + m - n

def off (i j : Fin n) : ℕ := if i.val < j.val then j.val - i.val - 1 else j.val + n - i.val - 1

def g (i : Fin n) (m : ℕ) : Bool := if h : idx i m < n then f ⟨idx i m, h⟩ else false

def pre (i : Fin n) : ℕ → Bool
  | 0 => false
  | m + 1 => pre i m ^^ g f i m

theorem pre_iff (i : Fin n) (m : ℕ) :
    pre f i m = true ↔ Odd ((Finset.range m).filter (fun t => g f i t = true)).card := by
  induction m with
  | zero => simp [pre]
  | succ m ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    simp only [pre]
    by_cases hg : g f i m = true
    · rw [if_pos hg, Finset.card_insert_of_notMem (by simp), Nat.odd_add_one, ← ih, hg]
      cases pre f i m <;> simp
    · rw [if_neg hg]
      have : g f i m = false := by simpa using hg
      rw [this, ← ih]; cases pre f i m <;> simp

theorem idx_lt (i : Fin n) {m : ℕ} (hm : m < n) : idx i m < n := by
  unfold idx; have := i.isLt; split_ifs <;> omega

theorem off_lt (i j : Fin n) : off i j < n := by
  unfold off; have := i.isLt; have := j.isLt; split_ifs <;> omega

theorem idx_off (i j : Fin n) : idx i (off i j) = j.val := by
  unfold idx off; have := i.isLt; have := j.isLt; split_ifs <;> omega

theorem off_idx (i : Fin n) {m : ℕ} (hm : m < n) (h : idx i m < n) : off i ⟨idx i m, h⟩ = m := by
  unfold idx off at *; have := i.isLt; simp only at *; split_ifs at * <;> omega

theorem card_g (i : Fin n) :
    ((Finset.range n).filter (fun t => g f i t = true)).card =
      (Finset.univ.filter (fun j => f j = true)).card := by
  apply Finset.card_bij (fun t ht => (⟨idx i t, idx_lt i (Finset.mem_range.1 (Finset.mem_filter.1 ht).1)⟩ : Fin n))
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and] at ht ⊢
    have := ht.2; unfold g at this; rwa [dif_pos (idx_lt i ht.1)] at this
  · intro a ha b hb hab
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    have h1 := off_idx i ha.1 (idx_lt i ha.1)
    have h2 := off_idx i hb.1 (idx_lt i hb.1)
    rw [← h1, ← h2]; congr 1
  · intro j hj
    refine ⟨off i j, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      refine ⟨off_lt i j, ?_⟩
      unfold g; rw [dif_pos (by rw [idx_off]; exact j.isLt)]
      have : (⟨idx i (off i j), by rw [idx_off]; exact j.isLt⟩ : Fin n) = j := Fin.ext (idx_off i j)
      rw [this]; exact hj.2
    · exact Fin.ext (idx_off i j)

def word (i : Fin n) (b : Bool) (j : Fin n) : Bool := b ^^ pre f i (off i j)

theorem word_spec (hn2 : 2 ≤ n) (hodd : Odd (Finset.univ.filter (fun j => f j = true)).card)
    (i : Fin n) (b : Bool) :
    word f i b (nxt hn i) = b ∧
      ∀ k, (word f i b (nxt hn k) = !(word f i b k ^^ f k)) ↔ k = i := by
  have hpre : pre f i n = true := by rw [pre_iff, card_g]; exact hodd
  have hoff0 : off i (nxt hn i) = 0 := by
    unfold off; rw [nxt_val]; have := i.isLt; split_ifs <;> omega
  refine ⟨by simp [word, hoff0, pre], ?_⟩
  intro k
  constructor
  · intro hv
    by_contra hki

    have hok : off i k + 1 < n := by
      have h1 := idx_off i k
      have := off_lt i k
      unfold idx at h1; have := i.isLt; have := k.isLt
      have hne : k.val ≠ i.val := fun h => hki (Fin.ext h)
      split_ifs at h1 <;> omega
    have hnx : off i (nxt hn k) = off i k + 1 := by
      have h1 := idx_off i k
      have h2 := nxt_val hn k
      unfold idx at h1; unfold off at *; have := i.isLt; have := k.isLt
      split_ifs at * <;> omega
    have hgk : g f i (off i k) = f k := by
      unfold g; rw [dif_pos (by rw [idx_off]; exact k.isLt)]
      congr 1; exact Fin.ext (idx_off i k)
    simp only [word, hnx, pre, hgk] at hv
    cases b <;> cases pre f i (off i k) <;> cases f k <;> simp at hv
  · intro hk; rw [hk]
    have hoi : off i i = n - 1 := by unfold off; simp only [lt_irrefl, if_false]; omega
    have hgi : g f i (n - 1) = f i := by
      unfold g
      have : idx i (n - 1) = i.val := by unfold idx; have := i.isLt; split_ifs <;> omega
      rw [dif_pos (by rw [this]; exact i.isLt)]
      congr 1; exact Fin.ext this
    have hpn : pre f i n = (pre f i (n - 1) ^^ g f i (n - 1)) := by
      obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      subst hm; simp [pre]
    show (b ^^ pre f i (off i (nxt hn i))) = !((b ^^ pre f i (off i i)) ^^ f i)
    rw [hoff0, hoi, Bool.xor_assoc, ← hgi, ← hpn, hpre]
    cases b <;> rfl

end Words

section Lower
variable (hn : 0 < n) (f : Fin n → Bool)

def Valid (C : Finset (Fin n × Bool)) : Prop :=
  Cons C ∧ ∃ (k : Fin n) (a : Bool), (k, a) ∈ C ∧ (nxt hn k, !(a ^^ f k)) ∈ C

theorem lower (hn2 : 2 ≤ n) (hodd : Odd (univ.filter (fun j => f j = true)).card)
    (L : Finset (Finset (Fin n × Bool))) (hv : ∀ C ∈ L, Valid hn f C)
    (hp : ∀ x : Fin n → Bool, (L.filter (fun C => Agree x C)).card = 1) (h : ℕ) :
    2 * n ≤ L.card ∧ (∀ d, (∀ C ∈ L, C.card ≤ d) → 2 * n ≤ 2 ^ d) ∧
    2 * n * (h + 1) ≤ L.sum Finset.card + 2 ^ h := by
  have hone : ∀ x : Fin n → Bool, ∃ C, L.filter (fun C => Agree x C) = {C} :=
    fun x => Finset.card_eq_one.1 (hp x)
  choose φ hφ using hone
  have hφL : ∀ x, φ x ∈ L ∧ Agree x (φ x) := by
    intro x
    have hm : φ x ∈ L.filter (fun C => Agree x C) := by rw [hφ x]; exact mem_singleton_self _
    exact mem_filter.1 hm
  let ψ : Fin n × Bool → Finset (Fin n × Bool) := fun ib => φ (word f ib.1 ib.2)
  have hinj : Function.Injective ψ := by
    rintro ⟨i, b⟩ ⟨j, c⟩ heq
    simp only [ψ] at heq
    have ha1 := (hφL (word f i b)).2
    have ha2 := (hφL (word f j c)).2
    rw [heq] at ha1
    obtain ⟨_, k, a, hk1, hk2⟩ := hv _ (hφL (word f j c)).1
    have e1 := ha1 _ hk1
    have e2 := ha1 _ hk2
    have e3 := ha2 _ hk1
    have e4 := ha2 _ hk2
    simp only at e1 e2 e3 e4
    have s1 := word_spec hn f hn2 hodd i b
    have s2 := word_spec hn f hn2 hodd j c
    have hki : k = i := (s1.2 k).1 (by rw [e2, e1])
    have hkj : k = j := (s2.2 k).1 (by rw [e4, e3])
    subst hki
    subst hkj
    have hbc : b = c := by
      have t1 := s1.1
      have t2 := s2.1
      rw [← t1, ← t2, e2, e4]
    rw [hbc]
  set P := (univ : Finset (Fin n × Bool)).image ψ with hPdef
  have hPc : P.card = 2 * n := by
    rw [card_image_of_injective _ hinj, card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool]; ring
  have hPL : P ⊆ L := by
    intro C hC
    obtain ⟨ib, _, rfl⟩ := mem_image.1 hC
    exact (hφL _).1
  have hcons : ∀ C ∈ L, Cons C := fun C hC => (hv C hC).1
  have hK := kraft L hcons hp
  have hcn : ∀ C ∈ L, C.card ≤ n := fun C hC => (agree_card C (hcons C hC)).1
  have hKP : ∑ C ∈ P, 2 ^ (n - C.card) ≤ 2 ^ n := by
    rw [← hK]; exact sum_le_sum_of_subset hPL
  refine ⟨hPc ▸ card_le_card hPL, ?_, ?_⟩
  · intro d hd
    set e := min d n
    have hce : ∀ C ∈ P, C.card ≤ e := fun C hC => le_min (hd C (hPL hC)) (hcn C (hPL hC))
    have h1 : P.card * 2 ^ (n - e) ≤ ∑ C ∈ P, 2 ^ (n - C.card) := by
      rw [← smul_eq_mul, ← sum_const]
      apply sum_le_sum
      intro C hC
      exact Nat.pow_le_pow_right (by norm_num) (by have := hce C hC; omega)
    have h2 : 2 ^ n = 2 ^ (n - e) * 2 ^ e := by
      rw [← pow_add]; congr 1; have : e ≤ n := min_le_right _ _; omega
    have h3 : P.card * 2 ^ (n - e) ≤ 2 ^ e * 2 ^ (n - e) := by
      calc _ ≤ _ := h1
        _ ≤ 2 ^ n := hKP
        _ = _ := by rw [h2, mul_comm]
    have h4 : P.card ≤ 2 ^ e := Nat.le_of_mul_le_mul_right h3 (by positivity)
    calc 2 * n = P.card := hPc.symm
      _ ≤ 2 ^ e := h4
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (min_le_left _ _)
  · have hper : ∀ C ∈ P, (h + 1) * 2 ^ n ≤ C.card * 2 ^ n + 2 ^ h * 2 ^ (n - C.card) := by
      intro C hC
      have hc := hcn C (hPL hC)
      have k := Nat.mul_le_mul_right (2 ^ (n - C.card)) (key_ineq C.card h)
      have e1 : 2 ^ C.card * 2 ^ (n - C.card) = 2 ^ n := by
        rw [← pow_add]; congr 1; omega
      calc (h + 1) * 2 ^ n = (h + 1) * 2 ^ C.card * 2 ^ (n - C.card) := by rw [mul_assoc, e1]
        _ ≤ (C.card * 2 ^ C.card + 2 ^ h) * 2 ^ (n - C.card) := k
        _ = C.card * 2 ^ n + 2 ^ h * 2 ^ (n - C.card) := by
          rw [add_mul, mul_assoc, e1, mul_comm (2 ^ h)]
    have hsum := sum_le_sum hper
    rw [sum_const, smul_eq_mul, sum_add_distrib, ← sum_mul, ← mul_sum] at hsum
    have hsub : ∑ C ∈ P, C.card ≤ L.sum Finset.card := sum_le_sum_of_subset hPL
    have : 2 * n * (h + 1) * 2 ^ n ≤ (L.sum Finset.card + 2 ^ h) * 2 ^ n := by
      rw [hPc] at hsum
      calc 2 * n * (h + 1) * 2 ^ n = 2 * n * ((h + 1) * 2 ^ n) := by ring
        _ ≤ (∑ C ∈ P, C.card) * 2 ^ n + 2 ^ h * ∑ C ∈ P, 2 ^ (n - C.card) := hsum
        _ ≤ (L.sum Finset.card) * 2 ^ n + 2 ^ h * 2 ^ n := by
          gcongr
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_right this (by positivity)

end Lower

section Build
variable (hn : 0 < n) (f : Fin n → Bool)

def F (m : ℕ) : Bool := if h : m < n then f ⟨m, h⟩ else false

def pp (b : Bool) : ℕ → Bool
  | 0 => b
  | m + 1 => pp b m ^^ F f m

def pos (m : ℕ) : Fin n := ⟨m % n, Nat.mod_lt _ hn⟩

theorem pos_val {m : ℕ} (hm : m < n) : (pos hn m).val = m := Nat.mod_eq_of_lt hm

theorem pos_inj {m m' : ℕ} (hm : m < n) (hm' : m' < n) (h : pos hn m = pos hn m') : m = m' := by
  have := congrArg Fin.val h; rwa [pos_val hn hm, pos_val hn hm'] at this

theorem pos_n : pos hn n = pos hn 0 := by apply Fin.ext; simp [pos]

def cells (b : Bool) (l r : ℕ) : List (Finset (Fin n × Bool)) :=
  if l + 1 < r then
    (cells b l ((l + r) / 2)).map (insert (pos hn ((l + r) / 2), !pp f b ((l + r) / 2))) ++
    (cells b ((l + r) / 2) r).map (insert (pos hn ((l + r) / 2), pp f b ((l + r) / 2)))
  else [∅]
termination_by r - l
decreasing_by all_goals omega

theorem cells_eq (b : Bool) (l r : ℕ) : cells hn f b l r =
    if l + 1 < r then
    (cells hn f b l ((l + r) / 2)).map (insert (pos hn ((l + r) / 2), !pp f b ((l + r) / 2))) ++
    (cells hn f b ((l + r) / 2) r).map (insert (pos hn ((l + r) / 2), pp f b ((l + r) / 2)))
  else [∅] := by
  rw [cells]

set_option maxHeartbeats 1000000 in

theorem cells_inv (b : Bool) : ∀ k l r, r - l = k → l < r → r ≤ n →
    (∀ x : Fin n → Bool, (cells hn f b l r).countP (fun C => decide (Agree x C)) = 1) ∧
    (cells hn f b l r).length = r - l ∧
    ∀ C ∈ cells hn f b l r,
      (∀ q ∈ C, ∃ m, l < m ∧ m < r ∧ q.1 = pos hn m) ∧
      (∀ q ∈ C, ∀ q' ∈ C, q.1 = q'.1 → q = q') ∧
      Nat.log 2 (r - l) ≤ C.card ∧ C.card ≤ Nat.clog 2 (r - l) ∧
      ∃ m, l ≤ m ∧ m + 1 ≤ r ∧ ((pos hn m, pp f b m) ∈ C ∨ m = l) ∧
        ((pos hn (m + 1), !pp f b (m + 1)) ∈ C ∨ m + 1 = r) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro l r hk hlr hrn
  by_cases hs : l + 1 < r
  · rw [cells_eq, if_pos hs]
    set mid := (l + r) / 2 with hmid
    have h1 : l < mid := by omega
    have h2 : mid < r := by omega
    obtain ⟨cL, lenL, iL⟩ := ih (mid - l) (by omega) l mid rfl h1 (by omega)
    obtain ⟨cR, lenR, iR⟩ := ih (r - mid) (by omega) mid r rfl h2 hrn
    have hmn : mid < n := by omega

    have freshL : ∀ C ∈ cells hn f b l mid, ∀ v, (pos hn mid, v) ∉ C := by
      intro C hC v hq
      obtain ⟨m, hm1, hm2, hm3⟩ := (iL C hC).1 _ hq
      have := pos_inj hn hmn (by omega) hm3; omega
    have freshR : ∀ C ∈ cells hn f b mid r, ∀ v, (pos hn mid, v) ∉ C := by
      intro C hC v hq
      obtain ⟨m, hm1, hm2, hm3⟩ := (iR C hC).1 _ hq
      have := pos_inj hn hmn (by omega) hm3; omega
    have hlog : Nat.log 2 (r - l) = Nat.log 2 (mid - l) + 1 := by
      rw [Nat.log_of_one_lt_of_le (by norm_num) (by omega)]
      congr 2; omega
    have hlog2 : Nat.log 2 (mid - l) ≤ Nat.log 2 (r - mid) := Nat.log_mono_right (by omega)
    have hclog : Nat.clog 2 (r - l) = Nat.clog 2 (r - mid) + 1 := by
      rw [Nat.clog_of_two_le (by norm_num) (by omega)]
      congr 2; omega
    have hclog2 : Nat.clog 2 (mid - l) ≤ Nat.clog 2 (r - mid) := Nat.clog_mono_right _ (by omega)
    refine ⟨?_, ?_, ?_⟩
    · intro x
      rw [List.countP_append, List.countP_map, List.countP_map]
      by_cases hx : x (pos hn mid) = pp f b mid
      · have e1 : (cells hn f b l mid).countP
            ((fun C => decide (Agree x C)) ∘ insert (pos hn mid, !pp f b mid)) = 0 := by
          rw [List.countP_eq_zero]
          intro C _
          simp [Function.comp, agree_insert, hx]
        have e2 : (cells hn f b mid r).countP
            ((fun C => decide (Agree x C)) ∘ insert (pos hn mid, pp f b mid)) =
            (cells hn f b mid r).countP (fun C => decide (Agree x C)) := by
          congr 1; funext C; simp [Function.comp, agree_insert, hx]
        rw [e1, e2, cR x]
      · have e1 : (cells hn f b l mid).countP
            ((fun C => decide (Agree x C)) ∘ insert (pos hn mid, !pp f b mid)) =
            (cells hn f b l mid).countP (fun C => decide (Agree x C)) := by
          congr 1; funext C
          have : x (pos hn mid) = !pp f b mid := by
            revert hx; generalize x (pos hn mid) = u; generalize pp f b mid = w
            cases u <;> cases w <;> decide
          simp [Function.comp, agree_insert, this]
        have e2 : (cells hn f b mid r).countP
            ((fun C => decide (Agree x C)) ∘ insert (pos hn mid, pp f b mid)) = 0 := by
          rw [List.countP_eq_zero]
          intro C _
          simp [Function.comp, agree_insert, hx]
        rw [e1, e2, cL x]
    · rw [List.length_append, List.length_map, List.length_map, lenL, lenR]; omega
    · intro C hC
      rw [List.mem_append, List.mem_map, List.mem_map] at hC
      rcases hC with ⟨C', hC', rfl⟩ | ⟨C', hC', rfl⟩
      · obtain ⟨p1, p2, p3, p4, m, hm1, hm2, hm3, hm4⟩ := iL C' hC'
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro q hq
          rcases Finset.mem_insert.1 hq with rfl | hq
          · exact ⟨mid, h1, h2, rfl⟩
          · obtain ⟨m', a1, a2, a3⟩ := p1 q hq; exact ⟨m', a1, by omega, a3⟩
        · intro q hq q' hq' he
          rcases Finset.mem_insert.1 hq with rfl | hq <;> rcases Finset.mem_insert.1 hq' with rfl | hq'
          · rfl
          · exfalso; apply freshL C' hC' q'.2
            have : q' = (pos hn mid, q'.2) := Prod.ext (by simpa using he.symm) rfl
            rw [← this]; exact hq'
          · exfalso; apply freshL C' hC' q.2
            have : q = (pos hn mid, q.2) := Prod.ext (by simpa using he) rfl
            rw [← this]; exact hq
          · exact p2 q hq q' hq' he
        · rw [Finset.card_insert_of_notMem (freshL C' hC' _)]; omega
        · rw [Finset.card_insert_of_notMem (freshL C' hC' _)]; omega
        · refine ⟨m, hm1, by omega, ?_, ?_⟩
          · rcases hm3 with h | h
            · exact Or.inl (Finset.mem_insert_of_mem h)
            · exact Or.inr h
          · rcases hm4 with h | h
            · exact Or.inl (Finset.mem_insert_of_mem h)
            · left; rw [h]; exact Finset.mem_insert_self _ _
      · obtain ⟨p1, p2, p3, p4, m, hm1, hm2, hm3, hm4⟩ := iR C' hC'
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro q hq
          rcases Finset.mem_insert.1 hq with rfl | hq
          · exact ⟨mid, h1, h2, rfl⟩
          · obtain ⟨m', a1, a2, a3⟩ := p1 q hq; exact ⟨m', by omega, a2, a3⟩
        · intro q hq q' hq' he
          rcases Finset.mem_insert.1 hq with rfl | hq <;> rcases Finset.mem_insert.1 hq' with rfl | hq'
          · rfl
          · exfalso; apply freshR C' hC' q'.2
            have : q' = (pos hn mid, q'.2) := Prod.ext (by simpa using he.symm) rfl
            rw [← this]; exact hq'
          · exfalso; apply freshR C' hC' q.2
            have : q = (pos hn mid, q.2) := Prod.ext (by simpa using he) rfl
            rw [← this]; exact hq
          · exact p2 q hq q' hq' he
        · rw [Finset.card_insert_of_notMem (freshR C' hC' _)]; omega
        · rw [Finset.card_insert_of_notMem (freshR C' hC' _)]; omega
        · refine ⟨m, by omega, hm2, ?_, ?_⟩
          · rcases hm3 with h | h
            · exact Or.inl (Finset.mem_insert_of_mem h)
            · left; rw [h]; exact Finset.mem_insert_self _ _
          · rcases hm4 with h | h
            · exact Or.inl (Finset.mem_insert_of_mem h)
            · exact Or.inr h
  · rw [cells_eq, if_neg hs]
    have hr : r = l + 1 := by omega
    subst hr
    refine ⟨?_, ?_, ?_⟩
    · intro x; simp [Agree]
    · simp
    · intro C hC
      simp only [List.mem_singleton] at hC
      subst hC
      refine ⟨by simp, by simp, by simp, by simp, l, le_refl _, le_refl _, Or.inr rfl, Or.inr rfl⟩

end Build

section Root
variable (hn : 0 < n) (f : Fin n → Bool)

theorem pp_iff (b : Bool) (m : ℕ) :
    pp f b m = (b ^^ decide (Odd ((Finset.range m).filter (fun t => F f t = true)).card)) := by
  induction m with
  | zero => simp [pp]
  | succ m ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    simp only [pp, ih]
    by_cases hg : F f m = true
    · rw [if_pos hg, Finset.card_insert_of_notMem (by simp), hg]
      cases b <;> by_cases ho : Odd ((Finset.range m).filter (fun t => F f t = true)).card <;>
        simp [ho, Nat.odd_add_one]
    · rw [if_neg hg]
      have : F f m = false := by simpa using hg
      rw [this]; cases b <;> simp

theorem card_F : ((Finset.range n).filter (fun t => F f t = true)).card =
    (Finset.univ.filter (fun j => f j = true)).card := by
  symm
  apply Finset.card_bij (fun j _ => j.val)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hj ⊢
    refine ⟨j.isLt, ?_⟩
    unfold F; rw [dif_pos j.isLt]; exact hj
  · intro a _ b _ h; exact Fin.ext h
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    refine ⟨⟨t, ht.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := ht.2; unfold F at this; rwa [dif_pos ht.1] at this

def rootList (b : Bool) : List (Finset (Fin n × Bool)) :=
  (cells hn f b 0 n).map (insert (pos hn 0, b))

def allList : List (Finset (Fin n × Bool)) := rootList hn f true ++ rootList hn f false

theorem root_fresh (b : Bool) : ∀ C ∈ cells hn f b 0 n, ∀ v, (pos hn 0, v) ∉ C := by
  intro C hC v hq
  obtain ⟨_, _, I⟩ := cells_inv hn f b (n - 0) 0 n rfl hn le_rfl
  obtain ⟨m, hm1, hm2, hm3⟩ := (I C hC).1 _ hq
  have := pos_inj hn hn (by omega) hm3; omega

theorem all_count (x : Fin n → Bool) : (allList hn f).countP (fun C => decide (Agree x C)) = 1 := by
  unfold allList rootList
  rw [List.countP_append, List.countP_map, List.countP_map]
  have c1 := (cells_inv hn f true (n - 0) 0 n rfl hn le_rfl).1 x
  have c2 := (cells_inv hn f false (n - 0) 0 n rfl hn le_rfl).1 x
  have z : ∀ b, x (pos hn 0) ≠ b → (cells hn f b 0 n).countP
      ((fun C => decide (Agree x C)) ∘ insert (pos hn 0, b)) = 0 := by
    intro b hb
    rw [List.countP_eq_zero]; intro C _; simp [Function.comp, agree_insert, hb]
  have o : ∀ b, x (pos hn 0) = b → (cells hn f b 0 n).countP
      ((fun C => decide (Agree x C)) ∘ insert (pos hn 0, b)) =
      (cells hn f b 0 n).countP (fun C => decide (Agree x C)) := by
    intro b hb
    congr 1; funext C; simp [Function.comp, agree_insert, hb]
  by_cases hx : x (pos hn 0) = true
  · rw [o true hx, z false (by rw [hx]; simp), c1]
  · have hx' : x (pos hn 0) = false := by simpa using hx
    rw [z true hx, o false hx', c2]

theorem all_props (hodd : Odd (Finset.univ.filter (fun j => f j = true)).card) :
    ∀ C ∈ allList hn f, Valid hn f C ∧ Nat.log 2 n + 1 ≤ C.card ∧ C.card ≤ Nat.clog 2 n + 1 := by
  intro C hC
  unfold allList rootList at hC
  have key : ∀ b, ∀ C ∈ (cells hn f b 0 n).map (insert (pos hn 0, b)),
      Valid hn f C ∧ Nat.log 2 n + 1 ≤ C.card ∧ C.card ≤ Nat.clog 2 n + 1 := by
    intro b C hC
    obtain ⟨C', hC', rfl⟩ := List.mem_map.1 hC
    obtain ⟨_, _, I⟩ := cells_inv hn f b (n - 0) 0 n rfl hn le_rfl
    obtain ⟨p1, p2, p3, p4, m, hm1, hm2, hm3, hm4⟩ := I C' hC'
    have fr := root_fresh hn f b C' hC'
    simp only [Nat.sub_zero] at p3 p4
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro i ⟨h1, h2⟩
      rcases Finset.mem_insert.1 h1 with e1 | h1 <;> rcases Finset.mem_insert.1 h2 with e2 | h2
      · have := e1.trans e2.symm; simp at this
      · rw [Prod.ext_iff] at e1; simp only at e1; rw [e1.1] at h2; exact fr _ h2
      · rw [Prod.ext_iff] at e2; simp only at e2; rw [e2.1] at h1; exact fr _ h1
      · have := p2 _ h1 _ h2 rfl; simp at this
    · have hmn : m < n := by omega
      refine ⟨pos hn m, pp f b m, ?_, ?_⟩
      · rcases hm3 with h | h
        · exact Finset.mem_insert_of_mem h
        · subst h; simp [pp]
      · have hnx : nxt hn (pos hn m) = pos hn (m + 1) := by
          apply Fin.ext; rw [nxt_val, pos_val hn hmn]; unfold pos; simp only
          split_ifs with h
          · exact (Nat.mod_eq_of_lt h).symm
          · have : m + 1 = n := by omega
            rw [this, Nat.mod_self]
        have hfm : f (pos hn m) = F f m := by
          unfold F; rw [dif_pos hmn]; congr 1; exact Fin.ext (pos_val hn hmn)
        rw [hnx, hfm]
        have hpp : (!(pp f b m ^^ F f m)) = !pp f b (m + 1) := by simp [pp]
        rw [hpp]
        rcases hm4 with h | h
        · exact Finset.mem_insert_of_mem h
        · rw [h, pos_n]
          have : pp f b n = !b := by
            rw [pp_iff, card_F]; simp [hodd]
          rw [this]; simp
    · rw [Finset.card_insert_of_notMem (fr _)]; omega
    · rw [Finset.card_insert_of_notMem (fr _)]; omega
  rcases List.mem_append.1 hC with h | h
  · exact key true C h
  · exact key false C h

theorem all_length : (allList hn f).length = 2 * n := by
  unfold allList rootList
  rw [List.length_append, List.length_map, List.length_map,
    (cells_inv hn f true (n - 0) 0 n rfl hn le_rfl).2.1,
    (cells_inv hn f false (n - 0) 0 n rfl hn le_rfl).2.1]
  omega

end Root

section Upper
variable (hn : 0 < n) (f : Fin n → Bool)

theorem all_nodup (hodd : Odd (Finset.univ.filter (fun j => f j = true)).card) :
    (allList hn f).Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro C
  by_cases hC : C ∈ allList hn f
  · have hc := (all_props hn f hodd C hC).1.1
    have hk := (agree_card C hc).2
    have hpos : 0 < (univ.filter (fun x : Fin n → Bool => Agree x C)).card := by
      rw [hk]; positivity
    obtain ⟨x, hx⟩ := Finset.card_pos.1 hpos
    have hx' : Agree x C := (Finset.mem_filter.1 hx).2
    rw [List.count_eq_countP]
    calc _ ≤ (allList hn f).countP (fun C => decide (Agree x C)) := by
          apply List.countP_mono_left
          intro D _ hD
          have : D = C := by simpa using hD
          subst this; simpa using hx'
      _ = 1 := all_count hn f x
  · rw [List.count_eq_zero.2 hC]; omega

theorem upper (hodd : Odd (Finset.univ.filter (fun j => f j = true)).card) :
    ∃ L : Finset (Finset (Fin n × Bool)),
      (∀ C ∈ L, Valid hn f C ∧ C.card ≤ Nat.clog 2 (2 * n)) ∧
      (∀ x : Fin n → Bool, (L.filter (fun C => Agree x C)).card = 1) ∧
      L.card = 2 * n ∧ L.sum Finset.card + 2 ^ Nat.clog 2 (2 * n) = 2 * n * (Nat.clog 2 (2 * n) + 1) := by
  have hcl : Nat.clog 2 (2 * n) = Nat.clog 2 n + 1 := by
    rw [Nat.clog_of_two_le (by norm_num) (by omega)]
    have : (2 * n + 2 - 1) / 2 = n := by omega
    rw [this]
  have hlog : Nat.clog 2 n ≤ Nat.log 2 n + 1 :=
    Nat.clog_le_of_le_pow (le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) n))
  have hnd := all_nodup hn f hodd
  have hcard : (allList hn f).toFinset.card = 2 * n := by
    rw [List.toFinset_card_of_nodup hnd, all_length]
  have hp : ∀ x : Fin n → Bool,
      ((allList hn f).toFinset.filter (fun C => Agree x C)).card = 1 := by
    intro x
    rw [← all_count hn f x, List.countP_eq_length_filter,
      ← List.toFinset_card_of_nodup (hnd.filter _)]
    congr 1; ext C; simp
  have hh : ∀ C ∈ (allList hn f).toFinset, Valid hn f C ∧
      Nat.clog 2 (2 * n) ≤ C.card + 1 ∧ C.card ≤ Nat.clog 2 (2 * n) := by
    intro C hC
    obtain ⟨a, b, c⟩ := all_props hn f hodd C (List.mem_toFinset.1 hC)
    exact ⟨a, by omega, by omega⟩
  refine ⟨(allList hn f).toFinset, fun C hC => ⟨(hh C hC).1, (hh C hC).2.2⟩, hp, hcard, ?_⟩
  have hhn : Nat.clog 2 (2 * n) ≤ n := Nat.clog_le_of_le_pow (two_mul_le_two_pow n)
  have kr := kraft (allList hn f).toFinset (fun C hC => (hh C hC).1.1) hp
  have ks : ∑ C ∈ (allList hn f).toFinset, 2 ^ (Nat.clog 2 (2 * n) - C.card) =
      2 ^ Nat.clog 2 (2 * n) := by
    have e : ∀ C ∈ (allList hn f).toFinset, 2 ^ (n - C.card) =
        2 ^ (Nat.clog 2 (2 * n) - C.card) * 2 ^ (n - Nat.clog 2 (2 * n)) := by
      intro C hC
      rw [← pow_add]; congr 1; have := (hh C hC).2.2; omega
    rw [Finset.sum_congr rfl e, ← Finset.sum_mul] at kr
    have e2 : 2 ^ n = 2 ^ Nat.clog 2 (2 * n) * 2 ^ (n - Nat.clog 2 (2 * n)) := by
      rw [← pow_add]; congr 1; omega
    rw [e2] at kr
    exact Nat.eq_of_mul_eq_mul_right (by positivity) kr
  have h1 : ∀ C ∈ (allList hn f).toFinset,
      C.card + 2 ^ (Nat.clog 2 (2 * n) - C.card) = Nat.clog 2 (2 * n) + 1 := by
    intro C hC
    obtain ⟨_, a, b⟩ := hh C hC
    rcases (show C.card = Nat.clog 2 (2 * n) ∨ C.card + 1 = Nat.clog 2 (2 * n) by omega) with e | e
    · rw [e, Nat.sub_self]; simp
    · rw [show Nat.clog 2 (2 * n) - C.card = 1 by omega]; omega
  calc (allList hn f).toFinset.sum Finset.card + 2 ^ Nat.clog 2 (2 * n)
      = ∑ C ∈ (allList hn f).toFinset, (C.card + 2 ^ (Nat.clog 2 (2 * n) - C.card)) := by
        rw [Finset.sum_add_distrib, ks]
    _ = ∑ C ∈ (allList hn f).toFinset, (Nat.clog 2 (2 * n) + 1) := Finset.sum_congr rfl h1
    _ = 2 * n * (Nat.clog 2 (2 * n) + 1) := by rw [Finset.sum_const, hcard, smul_eq_mul]

end Upper

end PEqualNP.Outside.L_pcx_254_aux

theorem PEqualNP.Outside.L_pcx_254 : (∀ (n : ℕ) (hn : 0 < n), 2 ≤ n → ∀ f : Fin n → Bool,
  Odd ((Finset.univ.filter (fun i => f i = true)).card) →
  let Cell := Finset (Fin n × Bool)
  let next := fun i : Fin n => (⟨(i.val+1) % n, Nat.mod_lt _ hn⟩ : Fin n)
  let valid := fun C : Cell =>
    (∀ i : Fin n, ¬ ((i, false) ∈ C ∧ (i, true) ∈ C)) ∧
    ∃ (i : Fin n) (a : Bool), (i, a) ∈ C ∧ (next i, !(a ^^ f i)) ∈ C
  let load := fun (L : Finset Cell) (x : Fin n → Bool) =>
    (L.filter (fun C => (C.filter (fun p => x p.1 ≠ p.2)) = ∅)).card
  let h := Nat.clog 2 (2*n)
  ∀ d s t : ℕ,
    (∃ L : Finset Cell, (∀ C ∈ L, valid C ∧ C.card ≤ d) ∧
      (∀ x, load L x = 1) ∧ L.card ≤ s ∧ L.sum Finset.card ≤ t) ↔
    2*n ≤ 2^d ∧ 2*n ≤ s ∧ 2*n*(h+1)-2^h ≤ t) := by
  intro n hn hn2 f hodd Cell next valid load h d s t
  have hload : ∀ (L : Finset Cell) (x : Fin n → Bool),
      load L x = (L.filter (fun C => L_pcx_254_aux.Agree x C)).card := by
    intro L x
    show (L.filter _).card = _
    congr 1
    apply Finset.filter_congr
    intro C _
    rw [Finset.filter_eq_empty_iff]
    simp [L_pcx_254_aux.Agree]
  constructor
  · rintro ⟨L, hL, hpL, hs, ht⟩
    have hv : ∀ C ∈ L, L_pcx_254_aux.Valid hn f C := fun C hC => (hL C hC).1
    have hp : ∀ x : Fin n → Bool, (L.filter (fun C => L_pcx_254_aux.Agree x C)).card = 1 := by
      intro x; rw [← hload]; exact hpL x
    obtain ⟨a1, a2, a3⟩ := L_pcx_254_aux.lower hn f hn2 hodd L hv hp h
    exact ⟨a2 d (fun C hC => (hL C hC).2), le_trans a1 hs,
      Nat.sub_le_iff_le_add.2 (le_trans a3 (Nat.add_le_add_right ht _))⟩
  · rintro ⟨hd, hs, ht⟩
    obtain ⟨L, hL, hp, hc, hsum⟩ := L_pcx_254_aux.upper hn f hodd
    refine ⟨L, fun C hC => ⟨(hL C hC).1, le_trans (hL C hC).2 (Nat.clog_le_of_le_pow hd)⟩,
      fun x => by rw [hload]; exact hp x, by rw [hc]; exact hs, ?_⟩
    exact le_trans (le_of_eq (Nat.eq_sub_of_add_eq hsum)) ht

