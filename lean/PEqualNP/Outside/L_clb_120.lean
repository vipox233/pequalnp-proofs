import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_586
import PEqualNP.Outside.L_meta_25689
import PEqualNP.Outside.L_lib_540
import PEqualNP.Outside.L_lib_377
import PEqualNP.Outside.L_lib_845
import PEqualNP.Outside.L_lib_743

namespace PEqualNP.Outside.L_clb_120

def loc (n : Nat) (hn : 0 < n) (k : Nat) : Fin n := ⟨k % n, Nat.mod_lt _ hn⟩

def cnt (n w : Nat) (hn : 0 < n) (tab : Fin n × (Fin (w+1) → Bool) → Bool) : Nat :=
  ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
    ∀ i : Fin n, tab (i, fun j => x (loc n hn (i.val+j.val))) = true)).card

def fval (n w : Nat) (hn : 0 < n) (raw : Fin (n*2^(w+1)) → Bool) : Bool :=
  (((Finset.univ : Finset (Fin n → Bool)).filter (fun x => ∀ i : Fin n,
    (List.ofFn raw).getD (i.val*2^(w+1) +
      ∑ j : Fin (w+1), if x (loc n hn (i.val+j.val)) then 2^j.val else 0) false = true)).card).testBit 0

def pval (w : Nat) (p : Fin (w+1) → Bool) : Nat := ∑ j : Fin (w+1), if p j then 2^j.val else 0

lemma ha_bsum_lt (k : Nat) (p : Fin k → Bool) :
    (∑ j : Fin k, if p j then 2^j.val else 0) < 2^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    have h1 := ih (fun j => p j.castSucc)
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [pow_succ]
    split_ifs <;> omega

lemma ha_bsum_bit (k : Nat) (p : Fin k → Bool) (i : Nat) :
    (∑ j : Fin k, if p j then 2^j.val else 0).testBit i =
      if h : i < k then p ⟨i, h⟩ else false := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    have h1 := ha_bsum_lt k (fun j => p j.castSucc)
    have h2 := ih (fun j => p j.castSucc)
    simp only [Fin.val_castSucc, Fin.val_last] at h1 h2 ⊢
    have e : (∑ j : Fin k, if p j.castSucc then 2^j.val else 0) +
        (if p (Fin.last k) then 2^k else 0) =
        2^k * (if p (Fin.last k) then 1 else 0) +
          (∑ j : Fin k, if p j.castSucc then 2^j.val else 0) := by
      split_ifs <;> omega
    rw [e, Nat.testBit_two_pow_mul_add _ h1, h2 i]
    by_cases hik : i < k
    · have hik' : i < k+1 := by omega
      rw [if_pos hik, dif_pos hik, dif_pos hik']
      rfl
    · rw [if_neg hik]
      by_cases hik' : i < k+1
      · have hi : i = k := by omega
        subst hi
        rw [dif_pos hik', Nat.sub_self]
        have hl : (⟨i, hik'⟩ : Fin (i+1)) = Fin.last i := rfl
        rw [hl]
        cases p (Fin.last i) <;> simp
      · rw [dif_neg hik']
        have hz : (if p (Fin.last k) then 1 else 0 : Nat).testBit (i - k) = false := by
          apply Nat.testBit_eq_false_of_lt
          have h3 : 2 ≤ 2^(i-k) := by
            calc 2 = 2^1 := by norm_num
              _ ≤ 2^(i-k) := Nat.pow_le_pow_right (by norm_num) (by omega)
          split_ifs <;> omega
        exact hz

lemma ha_bsum_of (k m : Nat) (hm : m < 2^k) :
    (∑ j : Fin k, if m.testBit j.val then 2^j.val else 0) = m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [ha_bsum_bit k (fun j => m.testBit j.val) i]
  by_cases hik : i < k
  · rw [dif_pos hik]
  · rw [dif_neg hik]
    symm
    apply Nat.testBit_eq_false_of_lt
    calc m < 2^k := hm
      _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma pval_lt (w : Nat) (p : Fin (w+1) → Bool) : pval w p < 2^(w+1) := by
  exact ha_bsum_lt (w+1) p

lemma enc_bound (n w : Nat) (s : Fin n × (Fin (w+1) → Bool)) :
    s.1.val*2^(w+1) + pval w s.2 < n*2^(w+1) := by
  have h1 := pval_lt w s.2
  have h2 : (s.1.val+1)*2^(w+1) ≤ n*2^(w+1) := Nat.mul_le_mul_right _ s.1.isLt
  rw [Nat.add_mul, Nat.one_mul] at h2
  omega

lemma dec_bound (n w : Nat) (idx : Fin (n*2^(w+1))) : idx.val / 2^(w+1) < n := by
  rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by norm_num))]
  exact idx.isLt

def enc (n w : Nat) (s : Fin n × (Fin (w+1) → Bool)) : Fin (n*2^(w+1)) :=
  ⟨s.1.val*2^(w+1) + pval w s.2, enc_bound n w s⟩

def dec (n w : Nat) (idx : Fin (n*2^(w+1))) : Fin n × (Fin (w+1) → Bool) :=
  (⟨idx.val / 2^(w+1), dec_bound n w idx⟩, fun j => (idx.val % 2^(w+1)).testBit j.val)

lemma dec_enc (n w : Nat) (s : Fin n × (Fin (w+1) → Bool)) : dec n w (enc n w s) = s := by
  have hp := pval_lt w s.2
  have hpos : 0 < 2^(w+1) := Nat.pow_pos (by norm_num)
  apply Prod.ext
  · apply Fin.ext
    show (s.1.val*2^(w+1) + pval w s.2) / 2^(w+1) = s.1.val
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hp, Nat.zero_add]
  · funext j
    show ((s.1.val*2^(w+1) + pval w s.2) % 2^(w+1)).testBit j.val = s.2 j
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp]
    have h := ha_bsum_bit (w+1) s.2 j.val
    rw [dif_pos j.isLt] at h
    exact h

lemma enc_dec (n w : Nat) (idx : Fin (n*2^(w+1))) : enc n w (dec n w idx) = idx := by
  have hpos : 0 < 2^(w+1) := Nat.pow_pos (by norm_num)
  apply Fin.ext
  show idx.val / 2^(w+1) * 2^(w+1) + pval w (fun j => (idx.val % 2^(w+1)).testBit j.val) = idx.val
  have h : pval w (fun j => (idx.val % 2^(w+1)).testBit j.val) = idx.val % 2^(w+1) :=
    ha_bsum_of (w+1) _ (Nat.mod_lt _ hpos)
  rw [h]
  exact Nat.div_add_mod' _ _

lemma ha_getD (N : Nat) (raw : Fin N → Bool) (k : Nat) (h : k < N) :
    (List.ofFn raw).getD k false = raw ⟨k, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

lemma fval_tab (n w : Nat) (hn : 0 < n) (tab : Fin n × (Fin (w+1) → Bool) → Bool) :
    fval n w hn (fun idx => tab (dec n w idx)) = (cnt n w hn tab).testBit 0 := by
  unfold fval cnt
  congr 2
  apply Finset.filter_congr
  intro x _
  apply forall_congr'
  intro i
  have hb := enc_bound n w (i, fun j => x (loc n hn (i.val+j.val)))
  have hg := ha_getD _ (fun idx => tab (dec n w idx)) _ hb
  have hd := dec_enc n w (i, fun j => x (loc n hn (i.val+j.val)))
  have he : (⟨i.val*2^(w+1) + pval w (fun j => x (loc n hn (i.val+j.val))), hb⟩ :
      Fin (n*2^(w+1))) = enc n w (i, fun j => x (loc n hn (i.val+j.val))) := rfl
  rw [he] at hg
  simp only [hd] at hg
  have hs : (∑ j : Fin (w+1), if x (loc n hn (i.val+j.val)) then 2^j.val else 0) =
      pval w (fun j => x (loc n hn (i.val+j.val))) := rfl
  rw [hs, hg]

lemma ha_upd (n w : Nat) (tab : Fin n × (Fin (w+1) → Bool) → Bool)
    (s : Fin n × (Fin (w+1) → Bool)) (b : Bool) :
    Function.update (fun idx => tab (dec n w idx)) (enc n w s) b =
      fun idx => (Function.update tab s b) (dec n w idx) := by
  funext idx
  by_cases h : idx = enc n w s
  · subst h
    rw [Function.update_self, dec_enc, Function.update_self]
  · have h2 : dec n w idx ≠ s := by
      intro e
      apply h
      rw [← e, enc_dec]
    rw [Function.update_of_ne h, Function.update_of_ne h2]

lemma dep_mem (n w : Nat) (hn : 0 < n) (tab : Fin n × (Fin (w+1) → Bool) → Bool)
    (s : Fin n × (Fin (w+1) → Bool))
    (h : (cnt n w hn (Function.update tab s false)).testBit 0 ≠
      (cnt n w hn (Function.update tab s true)).testBit 0) :
    ∃ x : Fin (n*2^(w+1)) → Bool,
      fval n w hn (Function.update x (enc n w s) false) ≠
        fval n w hn (Function.update x (enc n w s) true) := by
  refine ⟨fun idx => tab (dec n w idx), ?_⟩
  rw [ha_upd, ha_upd, fval_tab, fval_tab]
  exact h

lemma hc_loc_zero (n w : Nat) (hn : 0 < n) (i : Fin n) :
    loc n hn (i.val + (0 : Fin (w+1)).val) = i := by
  apply Fin.ext
  show (i.val + (0 : Fin (w+1)).val) % n = i.val
  rw [Fin.val_zero, Nat.add_zero, Nat.mod_eq_of_lt i.isLt]

lemma hc_upd (n w : Nat) (hn : 0 < n) (x0 x : Fin n → Bool) (i : Fin n) (b : Bool) :
    (∀ r : Fin n, Function.update
      (fun s : Fin n × (Fin (w+1) → Bool) =>
        decide (s.1 ≠ i ∧ s.2 = fun j : Fin (w+1) => x0 (loc n hn (s.1.val + j.val))))
      (i, fun j : Fin (w+1) => x0 (loc n hn (i.val + j.val))) b
      (r, fun j : Fin (w+1) => x (loc n hn (r.val + j.val))) = true) ↔ (x = x0 ∧ b = true) := by
  constructor
  · intro h
    have hpat : ∀ r : Fin n, (fun j : Fin (w+1) => x (loc n hn (r.val + j.val))) =
        fun j : Fin (w+1) => x0 (loc n hn (r.val + j.val)) := by
      intro r
      by_contra hne
      have hr := h r
      have hs : (r, fun j : Fin (w+1) => x (loc n hn (r.val + j.val))) ≠
          (i, fun j : Fin (w+1) => x0 (loc n hn (i.val + j.val))) := by
        intro he
        have h1 : r = i := congrArg Prod.fst he
        subst h1
        exact hne (congrArg Prod.snd he)
      rw [Function.update_of_ne hs] at hr
      simp only [decide_eq_true_eq] at hr
      exact hne hr.2
    have hx : x = x0 := by
      funext p
      have h0 := congrFun (hpat p) 0
      simp only [hc_loc_zero] at h0
      exact h0
    refine ⟨hx, ?_⟩
    subst hx
    have hi := h i
    rw [Function.update_self] at hi
    exact hi
  · rintro ⟨rfl, rfl⟩ r
    by_cases hr : r = i
    · subst hr
      rw [Function.update_self]
    · have hs : (r, fun j : Fin (w+1) => x (loc n hn (r.val + j.val))) ≠
          (i, fun j : Fin (w+1) => x (loc n hn (i.val + j.val))) := by
        intro he
        exact hr (congrArg Prod.fst he)
      rw [Function.update_of_ne hs]
      simp only [decide_eq_true_eq]
      exact ⟨hr, trivial⟩

lemma hc_dep_real (n w : Nat) (hn : 0 < n) (x0 : Fin n → Bool) (i : Fin n) :
    ∃ x : Fin (n*2^(w+1)) → Bool,
      fval n w hn (Function.update x
        (enc n w (i, fun j : Fin (w+1) => x0 (loc n hn (i.val + j.val)))) false) ≠
      fval n w hn (Function.update x
        (enc n w (i, fun j : Fin (w+1) => x0 (loc n hn (i.val + j.val)))) true) := by
  apply dep_mem n w hn (fun s : Fin n × (Fin (w+1) → Bool) =>
        decide (s.1 ≠ i ∧ s.2 = fun j : Fin (w+1) => x0 (loc n hn (s.1.val + j.val))))
  have h0 : cnt n w hn (Function.update (fun s : Fin n × (Fin (w+1) → Bool) =>
        decide (s.1 ≠ i ∧ s.2 = fun j : Fin (w+1) => x0 (loc n hn (s.1.val + j.val))))
      (i, fun j : Fin (w+1) => x0 (loc n hn (i.val + j.val))) false) = 0 := by
    unfold cnt
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    have := (hc_upd n w hn x0 x i false).1 hx
    exact Bool.false_ne_true this.2
  have h1 : cnt n w hn (Function.update (fun s : Fin n × (Fin (w+1) → Bool) =>
        decide (s.1 ≠ i ∧ s.2 = fun j : Fin (w+1) => x0 (loc n hn (s.1.val + j.val))))
      (i, fun j : Fin (w+1) => x0 (loc n hn (i.val + j.val))) true) = 1 := by
    unfold cnt
    rw [Finset.card_eq_one]
    refine ⟨x0, ?_⟩
    ext x
    rw [Finset.mem_filter, Finset.mem_singleton, hc_upd n w hn x0 x i true]
    simp
  rw [h0, h1]
  decide

def hc_xz (n m : Nat) (i : Fin n) (z : Fin m → Bool) : Fin n → Bool :=
  fun p => if h : (p.val + n - i.val) % n < m then z ⟨(p.val + n - i.val) % n, h⟩ else false

lemma hc_xz_at (n w : Nat) (hn : 0 < n) (m : Nat) (hmn : m ≤ n) (i : Fin n) (z : Fin m → Bool)
    (j : Nat) (hj : j < m) : hc_xz n m i z (loc n hn (i.val + j)) = z ⟨j, hj⟩ := by
  have hi := i.isLt
  have key : ((loc n hn (i.val + j)).val + n - i.val) % n = j := by
    show ((i.val + j) % n + n - i.val) % n = j
    by_cases hlt : i.val + j < n
    · rw [Nat.mod_eq_of_lt hlt]
      have : i.val + j + n - i.val = j + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · have h2 : (i.val + j) % n = i.val + j - n := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [h2]
      have : i.val + j - n + n - i.val = j := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
  unfold hc_xz
  have hlt : ((loc n hn (i.val + j)).val + n - i.val) % n < m := by rw [key]; exact hj
  rw [dif_pos hlt]
  congr 1
  exact Fin.ext key

lemma dep_count (n w : Nat) (hn : 0 < n) :
    n * 2^(min n (w+1)) ≤ ((Finset.univ : Finset (Fin (n*2^(w+1)))).filter (fun i =>
      ∃ x : Fin (n*2^(w+1)) → Bool,
        fval n w hn (Function.update x i false) ≠ fval n w hn (Function.update x i true))).card := by
  have hmn : min n (w+1) ≤ n := Nat.min_le_left _ _
  have hmw : min n (w+1) ≤ w+1 := Nat.min_le_right _ _
  have hcard : (Finset.univ : Finset (Fin n × (Fin (min n (w+1)) → Bool))).card =
      n * 2^(min n (w+1)) := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
  rw [← hcard]
  apply Finset.card_le_card_of_injOn (fun s : Fin n × (Fin (min n (w+1)) → Bool) =>
    enc n w (s.1, fun j : Fin (w+1) =>
      hc_xz n (min n (w+1)) s.1 s.2 (loc n hn (s.1.val + j.val))))
  · intro s _
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact hc_dep_real n w hn (hc_xz n (min n (w+1)) s.1 s.2) s.1
  · rintro ⟨i, z⟩ _ ⟨i', z'⟩ _ he
    have he2 := congrArg (dec n w) he
    simp only [dec_enc] at he2
    have h1 : i = i' := congrArg Prod.fst he2
    subst h1
    have h2 := congrArg Prod.snd he2
    simp only at h2
    have hz : z = z' := by
      funext j
      have h3 := congrFun h2 ⟨j.val, by omega⟩
      simp only at h3
      rw [hc_xz_at n w hn _ hmn i z j.val j.isLt, hc_xz_at n w hn _ hmn i z' j.val j.isLt] at h3
      exact h3
    rw [hz]

def Good (n w : Nat) (hn : 0 < n) (M : Nat) : Prop :=
  ∃ (slot : Fin M → Fin n × (Fin (w+1) → Bool)) (base : Fin n × (Fin (w+1) → Bool) → Bool),
    Function.Injective slot ∧ (∀ j, base (slot j) = false) ∧
    ∀ A : Finset (Fin M),
      cnt n w hn (fun s => base s || decide (s ∈ A.image slot)) % 2 = A.card % 2

lemma good_mono (n w : Nat) (hn : 0 < n) (M H : Nat) (h : Good n w hn M) (hle : H ≤ M) :
    Good n w hn H := by
  obtain ⟨slot, base, hinj, hbase, hpar⟩ := h
  refine ⟨fun j => slot (Fin.castLE hle j), base, ?_, fun j => hbase _, ?_⟩
  · intro a b hab
    exact Fin.castLE_injective hle (hinj hab)
  · intro A
    have h1 := hpar (A.image (Fin.castLE hle))
    rw [Finset.image_image, Finset.card_image_of_injective _ (Fin.castLE_injective hle)] at h1
    exact h1

def hc_xk (n m : Nat) (f : Fin m → Bool) : Fin n → Bool :=
  fun p => if h : p.val < m then f ⟨p.val, h⟩ else false

def hc_sl (n w : Nat) (hn : 0 < n) (m : Nat) (hm : 0 < m) (f : Fin m → Bool) :
    Fin n × (Fin (w+1) → Bool) :=
  (⟨0, hn⟩, fun j => f ⟨j.val % m, Nat.mod_lt _ hm⟩)

def hc_base (n w m : Nat) (s : Fin n × (Fin (w+1) → Bool)) : Bool :=
  decide (s.1.val ≠ 0 ∧ (m ≤ s.1.val → s.2 0 = false))

lemma hc_sl_inj (n w : Nat) (hn : 0 < n) (m : Nat) (hm : 0 < m) (hmw : m ≤ w+1)
    (f g : Fin m → Bool) (h : hc_sl n w hn m hm f = hc_sl n w hn m hm g) : f = g := by
  funext j
  have h2 := congrFun (congrArg Prod.snd h) ⟨j.val, by omega⟩
  simp only [hc_sl, Nat.mod_eq_of_lt j.isLt] at h2
  exact h2

lemma hc_xk_inj (n m : Nat) (hmn : m ≤ n) (f g : Fin m → Bool)
    (h : hc_xk n m f = hc_xk n m g) : f = g := by
  funext j
  have h2 := congrFun h ⟨j.val, by omega⟩
  simp only [hc_xk, dif_pos j.isLt] at h2
  exact h2

lemma hc_row0 (n w : Nat) (hn : 0 < n) (m : Nat) (hm : 0 < m)
    (hmod : ∀ j : Nat, j < w+1 → j % n = j % m) (f : Fin m → Bool) :
    ((⟨0, hn⟩ : Fin n), fun j : Fin (w+1) =>
      hc_xk n m f (loc n hn ((⟨0, hn⟩ : Fin n).val + j.val))) = hc_sl n w hn m hm f := by
  unfold hc_sl
  congr 1
  funext j
  have key : (loc n hn ((⟨0, hn⟩ : Fin n).val + j.val)).val = j.val % m := by
    show (0 + j.val) % n = j.val % m
    rw [Nat.zero_add]
    exact hmod j.val j.isLt
  unfold hc_xk
  have hlt : (loc n hn ((⟨0, hn⟩ : Fin n).val + j.val)).val < m := by
    rw [key]
    exact Nat.mod_lt _ hm
  rw [dif_pos hlt]
  congr 1
  exact Fin.ext key

lemma hc_pass (n w : Nat) (hn : 0 < n) (m : Nat) (hm : 0 < m) (hmn : m ≤ n) (hmw : m ≤ w+1)
    (hmod : ∀ j : Nat, j < w+1 → j % n = j % m) (ev : Fin (2^m) → (Fin m → Bool))
    (A : Finset (Fin (2^m))) (x : Fin n → Bool) :
    (∀ i : Fin n, (hc_base n w m (i, fun j : Fin (w+1) => x (loc n hn (i.val + j.val))) ||
      decide ((i, fun j : Fin (w+1) => x (loc n hn (i.val + j.val))) ∈
        A.image (fun k => hc_sl n w hn m hm (ev k)))) = true) ↔
    x ∈ A.image (fun k => hc_xk n m (ev k)) := by
  rw [Finset.mem_image]
  constructor
  · intro h
    have h0 := h ⟨0, hn⟩
    rw [Bool.or_eq_true, decide_eq_true_eq] at h0
    rcases h0 with h0 | h0
    · simp [hc_base] at h0
    · rw [Finset.mem_image] at h0
      obtain ⟨k, hk, hke⟩ := h0
      refine ⟨k, hk, ?_⟩
      funext p
      by_cases hp : p.val < m
      · have h2 := congrFun (congrArg Prod.snd hke) ⟨p.val, by omega⟩
        simp only [hc_sl, Nat.mod_eq_of_lt hp] at h2
        have hl : loc n hn (0 + p.val) = p := by
          apply Fin.ext
          show (0 + p.val) % n = p.val
          rw [Nat.zero_add, Nat.mod_eq_of_lt p.isLt]
        rw [hl] at h2
        unfold hc_xk
        rw [dif_pos hp]
        exact h2
      · have hpp := h p
        rw [Bool.or_eq_true, decide_eq_true_eq] at hpp
        have hx : x p = false := by
          rcases hpp with hpp | hpp
          · simp only [hc_base, decide_eq_true_eq] at hpp
            have h3 := hpp.2 (by omega)
            rw [hc_loc_zero] at h3
            exact h3
          · rw [Finset.mem_image] at hpp
            obtain ⟨k', _, hk'⟩ := hpp
            have h4 : (0 : Nat) = p.val := congrArg (fun s => s.1.val) hk'
            omega
        unfold hc_xk
        rw [dif_neg hp]
        exact hx.symm
  · rintro ⟨k, hk, rfl⟩ i
    rw [Bool.or_eq_true, decide_eq_true_eq]
    by_cases hi : i.val = 0
    · right
      have hi' : i = ⟨0, hn⟩ := Fin.ext hi
      rw [hi', hc_row0 n w hn m hm hmod (ev k)]
      exact Finset.mem_image_of_mem _ hk
    · left
      simp only [hc_base, decide_eq_true_eq]
      refine ⟨hi, ?_⟩
      intro hmi
      rw [hc_loc_zero]
      unfold hc_xk
      rw [dif_neg (by omega)]

lemma hc_good (n w : Nat) (hn : 0 < n) (m : Nat) (hm : 0 < m) (hmn : m ≤ n) (hmw : m ≤ w+1)
    (hmod : ∀ j : Nat, j < w+1 → j % n = j % m) : Good n w hn (2^m) := by
  have hc : Fintype.card (Fin m → Bool) = 2^m := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  obtain ⟨ev⟩ : Nonempty (Fin (2^m) ≃ (Fin m → Bool)) := ⟨(Fintype.equivFinOfCardEq hc).symm⟩
  refine ⟨fun k => hc_sl n w hn m hm (ev k), hc_base n w m, ?_, ?_, ?_⟩
  · intro a b hab
    exact ev.injective (hc_sl_inj n w hn m hm hmw _ _ hab)
  · intro j
    simp [hc_base, hc_sl]
  · intro A
    have hcnt : cnt n w hn (fun s => hc_base n w m s ||
        decide (s ∈ A.image (fun k => hc_sl n w hn m hm (ev k)))) = A.card := by
      unfold cnt
      have hf : ((Finset.univ : Finset (Fin n → Bool)).filter (fun x => ∀ i : Fin n,
          (hc_base n w m (i, fun j : Fin (w+1) => x (loc n hn (i.val + j.val))) ||
          decide ((i, fun j : Fin (w+1) => x (loc n hn (i.val + j.val))) ∈
            A.image (fun k => hc_sl n w hn m hm (ev k)))) = true)) =
          A.image (fun k => hc_xk n m (ev k)) := by
        ext x
        rw [Finset.mem_filter, hc_pass n w hn m hm hmn hmw hmod ev A x]
        simp only [Finset.mem_univ, true_and]
      rw [hf]
      apply Finset.card_image_of_injective
      intro a b hab
      exact ev.injective (hc_xk_inj n m hmn _ _ hab)
    rw [hcnt]

lemma good_direct (n w : Nat) (hn : 0 < n) : Good n w hn (2^(min n (w+1))) := by
  apply hc_good n w hn (min n (w+1)) (by omega) (Nat.min_le_left _ _) (Nat.min_le_right _ _)
  intro j hj
  rcases Nat.le_total n (w+1) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hj]

lemma he_loc_lt (n : Nat) (hn : 0 < n) (k : Nat) (h : k < n) : loc n hn k = ⟨k, h⟩ :=
  Fin.ext (Nat.mod_eq_of_lt h)

lemma he_loc_ge (n : Nat) (hn : 0 < n) (k : Nat) (h1 : n ≤ k) (h2 : k < n+n) :
    (loc n hn k).val = k - n := by
  show k % n = k - n
  rw [Nat.mod_eq_sub_mod h1]
  exact Nat.mod_eq_of_lt (by omega)

lemma he_ofNat (m k : Nat) (h : k < m+1) : Fin.ofNat (m+1) k = ⟨k, h⟩ :=
  Fin.ext (Nat.mod_eq_of_lt h)

def he_W (d L : Nat) (T : Fin L × (Fin (d+1+1) → Bool) → Bool) (u v : Fin (d+1) → Bool) :
    Finset (Fin (L+d+1) → Bool) :=
  (Finset.univ : Finset (Fin (L+d+1) → Bool)).filter (fun word =>
    (∀ pos : Fin (d+1), word ⟨pos.val, by omega⟩ = u pos ∧ word ⟨L+pos.val, by omega⟩ = v pos) ∧
    ∀ i : Fin L, T (i, fun off : Fin (d+1+1) => word ⟨i.val+off.val, by omega⟩) = true)

lemma he_W_eq (d L : Nat) (T : Fin L × (Fin (d+1+1) → Bool) → Bool) (u v : Fin (d+1) → Bool) :
    ((Finset.univ : Finset (Fin (L+d+1) → Bool)).filter (fun word =>
        (∀ pos : Fin (d+1), word (Fin.ofNat (L+d+1) pos.val) = u pos ∧
          word (Fin.ofNat (L+d+1) (L+pos.val)) = v pos) ∧
        ∀ i : Fin L, T (i, fun off => word (Fin.ofNat (L+d+1) (i.val+off.val))) = true)) =
    he_W d L T u v := by
  unfold he_W
  apply Finset.filter_congr
  intro word _
  have e1 : ∀ pos : Fin (d+1), Fin.ofNat (L+d+1) pos.val = ⟨pos.val, by omega⟩ :=
    fun pos => he_ofNat (L+d) pos.val (by omega)
  have e2 : ∀ pos : Fin (d+1), Fin.ofNat (L+d+1) (L+pos.val) = ⟨L+pos.val, by omega⟩ :=
    fun pos => he_ofNat (L+d) (L+pos.val) (by omega)
  have e3 : ∀ (i : Fin L) (off : Fin (d+1+1)),
      Fin.ofNat (L+d+1) (i.val+off.val) = ⟨i.val+off.val, by omega⟩ :=
    fun i off => he_ofNat (L+d) (i.val+off.val) (by omega)
  simp only [e1, e2, e3]

def he_tab (d L : Nat) (T1 T2 : Fin L × (Fin (d+1+1) → Bool) → Bool) :
    Fin (L+L) × (Fin (d+1+1) → Bool) → Bool :=
  fun s => if h : s.1.val < L then T1 (⟨s.1.val, h⟩, s.2)
        else T2 (⟨s.1.val - L, by omega⟩, s.2)

def he_w1 (d L : Nat) (hw : d+1 ≤ L) (x : Fin (L+L) → Bool) : Fin (L+d+1) → Bool :=
  fun k => x ⟨k.val, by omega⟩

def he_w2 (d L : Nat) (hn : 0 < L+L) (x : Fin (L+L) → Bool) : Fin (L+d+1) → Bool :=
  fun k => x (loc (L+L) hn (L+k.val))

def he_back (d L : Nat) (a c : Fin (L+d+1) → Bool) : Fin (L+L) → Bool :=
  fun p => if h : p.val < L then a ⟨p.val, by omega⟩ else c ⟨p.val - L, by omega⟩

def he_U (d L : Nat) (hw : d+1 ≤ L) (x : Fin (L+L) → Bool) : Fin (d+1) → Bool :=
  fun pos => x ⟨pos.val, by omega⟩

def he_V (d L : Nat) (hw : d+1 ≤ L) (x : Fin (L+L) → Bool) : Fin (d+1) → Bool :=
  fun pos => x ⟨L+pos.val, by omega⟩

lemma he_back_lt (d L : Nat) (a c : Fin (L+d+1) → Bool) (p : Fin (L+L)) (h : p.val < L) :
    he_back d L a c p = a ⟨p.val, by omega⟩ := dif_pos h

lemma he_back_ge (d L : Nat) (a c : Fin (L+d+1) → Bool) (p : Fin (L+L)) (h : ¬ p.val < L) :
    he_back d L a c p = c ⟨p.val - L, by omega⟩ := dif_neg h

lemma he_key (L m : Nat) (T : Fin L × (Fin m → Bool) → Bool) (a b : Fin L) (p q : Fin m → Bool)
    (h1 : a = b) (h2 : p = q) (h3 : T (a, p) = true) : T (b, q) = true := by
  rw [← h1, ← h2]
  exact h3

lemma he_pass (d L : Nat) (hn : 0 < L+L) (hw : d+1 ≤ L)
    (T1 T2 : Fin L × (Fin (d+1+1) → Bool) → Bool) (x : Fin (L+L) → Bool) :
    (∀ i : Fin (L+L), he_tab d L T1 T2 (i, fun j => x (loc (L+L) hn (i.val+j.val))) = true) ↔
    ((∀ i : Fin L, T1 (i, fun off : Fin (d+1+1) =>
        he_w1 d L hw x ⟨i.val+off.val, by omega⟩) = true) ∧
      (∀ i : Fin L, T2 (i, fun off : Fin (d+1+1) =>
        he_w2 d L hn x ⟨i.val+off.val, by omega⟩) = true)) := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have h0 := h ⟨i.val, by omega⟩
      unfold he_tab at h0
      rw [dif_pos i.isLt] at h0
      refine he_key L _ T1 _ _ _ _ rfl ?_ h0
      funext off
      show x (loc (L+L) hn (i.val+off.val)) = x ⟨i.val+off.val, _⟩
      rw [he_loc_lt (L+L) hn (i.val+off.val) (by omega)]
    · have h0 := h ⟨L+i.val, by omega⟩
      unfold he_tab at h0
      rw [dif_neg (by show ¬ L+i.val < L; omega)] at h0
      refine he_key L _ T2 _ _ _ _ (Fin.ext (by show L+i.val-L = i.val; omega)) ?_ h0
      funext off
      show x (loc (L+L) hn (L+i.val+off.val)) = x (loc (L+L) hn (L+(i.val+off.val)))
      rw [Nat.add_assoc]
  · rintro ⟨h1, h2⟩ i
    unfold he_tab
    by_cases hi : i.val < L
    · rw [dif_pos hi]
      refine he_key L _ T1 _ _ _ _ rfl ?_ (h1 ⟨i.val, hi⟩)
      funext off
      show x ⟨i.val+off.val, _⟩ = x (loc (L+L) hn (i.val+off.val))
      rw [he_loc_lt (L+L) hn (i.val+off.val) (by omega)]
    · rw [dif_neg hi]
      refine he_key L _ T2 _ _ _ _ rfl ?_ (h2 ⟨i.val-L, by omega⟩)
      funext off
      show x (loc (L+L) hn (L+(i.val-L+off.val))) = x (loc (L+L) hn (i.val+off.val))
      have e : L+(i.val-L+off.val) = i.val+off.val := by omega
      rw [e]

lemma he_left (d L : Nat) (hn : 0 < L+L) (hw : d+1 ≤ L) (x : Fin (L+L) → Bool) :
    he_back d L (he_w1 d L hw x) (he_w2 d L hn x) = x := by
  funext p
  by_cases h : p.val < L
  · rw [he_back_lt d L _ _ p h]
    rfl
  · rw [he_back_ge d L _ _ p h]
    show x (loc (L+L) hn (L+(p.val-L))) = x p
    rw [he_loc_lt (L+L) hn (L+(p.val-L)) (by omega)]
    exact congrArg x (Fin.ext (by show L+(p.val-L) = p.val; omega))

lemma he_right1 (d L : Nat) (hw : d+1 ≤ L) (T1 T2 : Fin L × (Fin (d+1+1) → Bool) → Bool)
    (u v : Fin (d+1) → Bool) (a c : Fin (L+d+1) → Bool)
    (ha : a ∈ he_W d L T1 u v) (hc : c ∈ he_W d L T2 v u) :
    he_w1 d L hw (he_back d L a c) = a := by
  unfold he_W at ha hc
  rw [Finset.mem_filter] at ha hc
  funext k
  show he_back d L a c ⟨k.val, _⟩ = a k
  by_cases h : k.val < L
  · rw [he_back_lt d L a c _ h]
  · rw [he_back_ge d L a c _ h]
    have hk := k.isLt
    exact ((hc.2.1 ⟨k.val-L, by omega⟩).1).trans (((ha.2.1 ⟨k.val-L, by omega⟩).2).symm.trans
      (congrArg a (Fin.ext (by show L+(k.val-L) = k.val; omega))))

lemma he_right2 (d L : Nat) (hn : 0 < L+L) (hw : d+1 ≤ L)
    (T1 T2 : Fin L × (Fin (d+1+1) → Bool) → Bool)
    (u v : Fin (d+1) → Bool) (a c : Fin (L+d+1) → Bool)
    (ha : a ∈ he_W d L T1 u v) (hc : c ∈ he_W d L T2 v u) :
    he_w2 d L hn (he_back d L a c) = c := by
  unfold he_W at ha hc
  rw [Finset.mem_filter] at ha hc
  funext k
  have hk := k.isLt
  show he_back d L a c (loc (L+L) hn (L+k.val)) = c k
  by_cases h : k.val < L
  · rw [he_loc_lt (L+L) hn (L+k.val) (by omega)]
    rw [he_back_ge d L a c _ (by show ¬ L+k.val < L; omega)]
    exact congrArg c (Fin.ext (by show L+k.val-L = k.val; omega))
  · have hv := he_loc_ge (L+L) hn (L+k.val) (by omega) (by omega)
    rw [he_back_lt d L a c _ (by rw [hv]; omega)]
    have e1 : a ⟨(loc (L+L) hn (L+k.val)).val, by rw [hv]; omega⟩ = a ⟨k.val-L, by omega⟩ :=
      congrArg a (Fin.ext (by show (loc (L+L) hn (L+k.val)).val = k.val-L; rw [hv]; omega))
    exact e1.trans (((ha.2.1 ⟨k.val-L, by omega⟩).1).trans
      (((hc.2.1 ⟨k.val-L, by omega⟩).2).symm.trans
        (congrArg c (Fin.ext (by show L+(k.val-L) = k.val; omega)))))

lemma he_fiber (d L : Nat) (hn : 0 < L+L) (hw : d+1 ≤ L)
    (T1 T2 : Fin L × (Fin (d+1+1) → Bool) → Bool) (u v : Fin (d+1) → Bool) :
    (((Finset.univ : Finset (Fin (L+L) → Bool)).filter (fun x =>
      ∀ i : Fin (L+L), he_tab d L T1 T2 (i, fun j => x (loc (L+L) hn (i.val+j.val))) = true)).filter
      (fun x => (he_U d L hw x, he_V d L hw x) = (u, v))).card =
    (he_W d L T1 u v ×ˢ he_W d L T2 v u).card := by
  apply Finset.card_nbij' (fun x => (he_w1 d L hw x, he_w2 d L hn x))
    (fun p => he_back d L p.1 p.2)
  · intro x hx
    have hx' := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
    have hp := (he_pass d L hn hw T1 T2 x).mp (Finset.mem_filter.mp hx'.1).2
    have hu : he_U d L hw x = u := congrArg Prod.fst hx'.2
    have hv : he_V d L hw x = v := congrArg Prod.snd hx'.2
    rw [Finset.mem_coe, Finset.mem_product]
    unfold he_W
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hp.1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hp.2⟩⟩
    · intro pos
      rw [← hu, ← hv]
      exact ⟨rfl, rfl⟩
    · intro pos
      rw [← hu, ← hv]
      refine ⟨?_, ?_⟩
      · show x (loc (L+L) hn (L+pos.val)) = x ⟨L+pos.val, _⟩
        rw [he_loc_lt (L+L) hn (L+pos.val) (by omega)]
      · show x (loc (L+L) hn (L+(L+pos.val))) = x ⟨pos.val, _⟩
        refine congrArg x (Fin.ext ?_)
        show (loc (L+L) hn (L+(L+pos.val))).val = pos.val
        rw [he_loc_ge (L+L) hn (L+(L+pos.val)) (by omega) (by omega)]
        omega
  · intro p hp
    have hp' := Finset.mem_product.mp (Finset.mem_coe.mp hp)
    have r1 := he_right1 d L hw T1 T2 u v p.1 p.2 hp'.1 hp'.2
    have r2 := he_right2 d L hn hw T1 T2 u v p.1 p.2 hp'.1 hp'.2
    have ha := hp'.1
    have hc := hp'.2
    unfold he_W at ha hc
    rw [Finset.mem_filter] at ha hc
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter]
    refine ⟨⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [he_pass d L hn hw T1 T2, r1, r2]
      exact ⟨ha.2.2, hc.2.2⟩
    · have hu : he_U d L hw (he_back d L p.1 p.2) = u := by
        funext pos
        show he_back d L p.1 p.2 ⟨pos.val, _⟩ = u pos
        rw [he_back_lt d L _ _ _ (by show pos.val < L; omega)]
        exact (ha.2.1 pos).1
      have hv : he_V d L hw (he_back d L p.1 p.2) = v := by
        funext pos
        show he_back d L p.1 p.2 ⟨L+pos.val, _⟩ = v pos
        rw [he_back_ge d L _ _ _ (by show ¬ L+pos.val < L; omega)]
        exact (congrArg p.2 (Fin.ext (by show L+pos.val-L = pos.val; omega))).trans (hc.2.1 pos).1
      rw [hu, hv]
  · intro x _
    exact he_left d L hn hw x
  · intro p hp
    have hp' := Finset.mem_product.mp (Finset.mem_coe.mp hp)
    exact Prod.ext (he_right1 d L hw T1 T2 u v p.1 p.2 hp'.1 hp'.2)
      (he_right2 d L hn hw T1 T2 u v p.1 p.2 hp'.1 hp'.2)

lemma arcs_split (d L : Nat) (hn : 0 < L+L) (hw : d+1 ≤ L)
    (T1 T2 : Fin L × (Fin (d+1+1) → Bool) → Bool) :
    cnt (L+L) (d+1) hn (fun s => if h : s.1.val < L then T1 (⟨s.1.val, h⟩, s.2)
        else T2 (⟨s.1.val - L, by omega⟩, s.2)) =
    ∑ u : Fin (d+1) → Bool, ∑ v : Fin (d+1) → Bool,
      ((Finset.univ : Finset (Fin (L+d+1) → Bool)).filter (fun word =>
        (∀ pos : Fin (d+1), word (Fin.ofNat (L+d+1) pos.val) = u pos ∧
          word (Fin.ofNat (L+d+1) (L+pos.val)) = v pos) ∧
        ∀ i : Fin L, T1 (i, fun off => word (Fin.ofNat (L+d+1) (i.val+off.val))) = true)).card *
      ((Finset.univ : Finset (Fin (L+d+1) → Bool)).filter (fun word =>
        (∀ pos : Fin (d+1), word (Fin.ofNat (L+d+1) pos.val) = v pos ∧
          word (Fin.ofNat (L+d+1) (L+pos.val)) = u pos) ∧
        ∀ i : Fin L, T2 (i, fun off => word (Fin.ofNat (L+d+1) (i.val+off.val))) = true)).card := by
  refine Eq.trans ?_ (Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ =>
    congrArg₂ (fun a b => a * b) (congrArg Finset.card (he_W_eq d L T1 u v).symm)
      (congrArg Finset.card (he_W_eq d L T2 v u).symm))))
  have h1 : (∑ u : Fin (d+1) → Bool, ∑ v : Fin (d+1) → Bool,
      (he_W d L T1 u v).card * (he_W d L T2 v u).card) =
      ∑ p : (Fin (d+1) → Bool) × (Fin (d+1) → Bool),
        (he_W d L T1 p.1 p.2 ×ˢ he_W d L T2 p.2 p.1).card := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.card_product]
  rw [h1]
  show cnt (L+L) (d+1) hn (he_tab d L T1 T2) = _
  unfold cnt
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => (he_U d L hw x, he_V d L hw x))
    (t := Finset.univ) (fun x _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro p _
  exact he_fiber d L hn hw T1 T2 p.1 p.2

def hf_slot (L d m : Nat) (port : Fin m → Fin L × (Fin (d+1+1) → Bool)) (j : Fin m) :
    Fin (L+L) × (Fin (d+1+1) → Bool) :=
  (⟨(port j).1.val, by omega⟩, (port j).2)

lemma hf_tab (L d m : Nat) (base : Fin L × (Fin (d+1+1) → Bool) → Bool)
    (pf pt : Fin m → Fin L × (Fin (d+1+1) → Bool)) (A : Finset (Fin m)) :
    (fun s : Fin (L+L) × (Fin (d+1+1) → Bool) =>
      (if h : s.1.val < L then base (⟨s.1.val, h⟩, s.2)
        else (base (⟨s.1.val - L, by omega⟩, s.2) ||
          decide ((⟨s.1.val - L, by omega⟩, s.2) ∈ Finset.univ.image pt))) ||
        decide (s ∈ A.image (hf_slot L d m pf))) =
    (fun s : Fin (L+L) × (Fin (d+1+1) → Bool) =>
      if h : s.1.val < L then
        (fun t => base t || decide (t ∈ A.image pf)) (⟨s.1.val, h⟩, s.2)
      else (fun t => base t || decide (t ∈ Finset.univ.image pt)) (⟨s.1.val - L, by omega⟩, s.2)) := by
  funext s
  by_cases h : s.1.val < L
  · rw [dif_pos h, dif_pos h]
    have hmem : s ∈ A.image (hf_slot L d m pf) ↔
        ((⟨s.1.val, h⟩, s.2) : Fin L × (Fin (d+1+1) → Bool)) ∈ A.image pf := by
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨j, hj, rfl⟩
      · rintro ⟨j, hj, he⟩
        refine ⟨j, hj, ?_⟩
        apply Prod.ext
        · apply Fin.ext
          show (pf j).1.val = s.1.val
          rw [he]
        · show (pf j).2 = s.2
          rw [he]
    simp only [hmem]
  · rw [dif_neg h, dif_neg h]
    have hmem : s ∉ A.image (hf_slot L d m pf) := by
      simp only [Finset.mem_image]
      rintro ⟨j, hj, rfl⟩
      exact h (pf j).1.isLt
    simp only [hmem, decide_false, Bool.or_false]

lemma hf_term (X : Type) [DecidableEq X] (m : Nat) (edge : Fin m → X × X)
    (hne : ∀ u v : Fin m, (edge u).1 ≠ (edge v).2) (A : Finset (Fin m)) (u v : X) :
    ((if u = v then 1 else 0) + (if ∃ j ∈ A, edge j = (u, v) then 1 else 0)) *
      ((if v = u then 1 else 0) + (if ∃ j ∈ (Finset.univ : Finset (Fin m)), edge j = (u, v)
        then 1 else 0)) =
    (if u = v then 1 else 0) + (if (u, v) ∈ A.image edge then 1 else 0) := by
  have hno : ∀ j, edge j ≠ (u, u) := by
    intro j hj
    apply hne j j
    rw [hj]
  by_cases huv : u = v
  · subst huv
    have h1 : ¬ ∃ j ∈ A, edge j = (u, u) := by
      rintro ⟨j, _, hj⟩
      exact hno j hj
    have h2 : ¬ ∃ j ∈ (Finset.univ : Finset (Fin m)), edge j = (u, u) := by
      rintro ⟨j, _, hj⟩
      exact hno j hj
    have h3 : (u, u) ∉ A.image edge := by
      rw [Finset.mem_image]
      exact h1
    rw [if_neg h1, if_neg h2, if_neg h3, if_pos rfl]
  · have hvu : ¬ v = u := fun h => huv h.symm
    rw [if_neg huv, if_neg hvu]
    by_cases hA : ∃ j ∈ A, edge j = (u, v)
    · have h2 : ∃ j ∈ (Finset.univ : Finset (Fin m)), edge j = (u, v) := by
        obtain ⟨j, _, hj⟩ := hA
        exact ⟨j, Finset.mem_univ j, hj⟩
      have h3 : (u, v) ∈ A.image edge := by
        rw [Finset.mem_image]
        exact hA
      rw [if_pos hA, if_pos h2, if_pos h3]
    · have h3 : (u, v) ∉ A.image edge := by
        rw [Finset.mem_image]
        exact hA
      rw [if_neg hA, if_neg h3, Nat.zero_add, Nat.zero_mul]

lemma hf_sum (X : Type) [Fintype X] [DecidableEq X] (m : Nat) (edge : Fin m → X × X)
    (hinj : Function.Injective edge) (A : Finset (Fin m)) :
    (∑ u : X, ∑ v : X, ((if u = v then 1 else 0) + (if (u, v) ∈ A.image edge then 1 else 0))) =
      Fintype.card X + A.card := by
  have h1 : (∑ u : X, ∑ v : X, (if u = v then 1 else 0)) = Fintype.card X := by
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, mul_one]
  have h2 : (∑ u : X, ∑ v : X, (if (u, v) ∈ A.image edge then 1 else 0)) = A.card := by
    rw [← Fintype.sum_prod_type (f := fun p : X × X => if p ∈ A.image edge then 1 else 0)]
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.card_image_of_injective A hinj]
    rfl
  simp only [Finset.sum_add_distrib]
  rw [h1, h2]

lemma hf_core (d L : Nat) (hn : 0 < L+L) (hw : d+1 ≤ L) (m : Nat)
    (edge : Fin m → (Fin (d+1) → Bool) × (Fin (d+1) → Bool))
    (base : Fin L × (Fin (d+1+1) → Bool) → Bool)
    (port : Bool → Fin m → Fin L × (Fin (d+1+1) → Bool))
    (hinj : Function.Injective edge) (hne : ∀ u v : Fin m, (edge u).1 ≠ (edge v).2)
    (hport : ∀ rev : Bool, Function.Injective (port rev) ∧ (∀ j, base (port rev j) = false) ∧
        ∀ enabled : Finset (Fin m), ∀ x y : Fin (d+1) → Bool,
          (Finset.univ.filter (fun word : Fin (L+d+1) → Bool =>
            (∀ pos : Fin (d+1),
              word (Fin.ofNat (L+d+1) pos.val) = x pos ∧
              word (Fin.ofNat (L+d+1) (L+pos.val)) = y pos) ∧
            ∀ i : Fin L,
              let s : Fin L × (Fin (d+1+1) → Bool) :=
                (i,fun off => word (Fin.ofNat (L+d+1) (i.val+off.val)))
              base s = true ∨ s ∈ enabled.image (port rev))).card =
                (if x = y then 1 else 0) +
                (if ∃ j ∈ enabled, edge j = (if rev then (y,x) else (x,y)) then 1 else 0)) :
    Good (L+L) (d+1) hn m := by
  refine ⟨hf_slot L d m (port false),
    fun s => if h : s.1.val < L then base (⟨s.1.val, h⟩, s.2)
        else (base (⟨s.1.val - L, by omega⟩, s.2) ||
          decide ((⟨s.1.val - L, by omega⟩, s.2) ∈ Finset.univ.image (port true))), ?_, ?_, ?_⟩
  · intro a b hab
    unfold hf_slot at hab
    simp only [Prod.mk.injEq, Fin.mk.injEq] at hab
    exact (hport false).1 (Prod.ext (Fin.ext hab.1) hab.2)
  · intro j
    have hlt : (hf_slot L d m (port false) j).1.val < L := (port false j).1.isLt
    dsimp only
    rw [dif_pos hlt]
    exact (hport false).2.1 j
  · intro A
    rw [hf_tab L d m base (port false) (port true) A]
    rw [arcs_split d L hn hw (fun t => base t || decide (t ∈ A.image (port false)))
      (fun t => base t || decide (t ∈ Finset.univ.image (port true)))]
    have h1 : ∀ u v : Fin (d+1) → Bool,
        ((Finset.univ : Finset (Fin (L+d+1) → Bool)).filter (fun word =>
          (∀ pos : Fin (d+1), word (Fin.ofNat (L+d+1) pos.val) = u pos ∧
            word (Fin.ofNat (L+d+1) (L+pos.val)) = v pos) ∧
          ∀ i : Fin L, (fun t => base t || decide (t ∈ A.image (port false)))
            (i, fun off => word (Fin.ofNat (L+d+1) (i.val+off.val))) = true)).card =
        (if u = v then 1 else 0) + (if ∃ j ∈ A, edge j = (u, v) then 1 else 0) := by
      intro u v
      have h := (hport false).2.2 A u v
      simp only [Bool.false_eq_true, if_false] at h
      rw [← h]
      congr 1
      apply Finset.filter_congr
      intro word _
      simp only [Bool.or_eq_true, decide_eq_true_eq]
    have h2 : ∀ u v : Fin (d+1) → Bool,
        ((Finset.univ : Finset (Fin (L+d+1) → Bool)).filter (fun word =>
          (∀ pos : Fin (d+1), word (Fin.ofNat (L+d+1) pos.val) = v pos ∧
            word (Fin.ofNat (L+d+1) (L+pos.val)) = u pos) ∧
          ∀ i : Fin L, (fun t => base t || decide (t ∈ Finset.univ.image (port true)))
            (i, fun off => word (Fin.ofNat (L+d+1) (i.val+off.val))) = true)).card =
        (if v = u then 1 else 0) +
          (if ∃ j ∈ (Finset.univ : Finset (Fin m)), edge j = (u, v) then 1 else 0) := by
      intro u v
      have h := (hport true).2.2 Finset.univ v u
      simp only [if_true] at h
      rw [← h]
      congr 1
      apply Finset.filter_congr
      intro word _
      simp only [Bool.or_eq_true, decide_eq_true_eq]
    simp only [h1, h2, hf_term (Fin (d+1) → Bool) m edge hne A]
    rw [hf_sum (Fin (d+1) → Bool) m edge hinj A]
    have hc : Fintype.card (Fin (d+1) → Bool) = 2 * 2^d := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, pow_succ, Nat.mul_comm]
    rw [hc]
    omega

lemma good_arcs (n w : Nat) (hn : 0 < n) (hw : 0 < w) (h2 : 2*w ≤ n) (he : n % 2 = 0) :
    Good n w hn ((2^w * min (n/2) (2^w) + 19)/20) := by
  obtain ⟨d, rfl⟩ : ∃ d, w = d+1 := ⟨w-1, by omega⟩
  obtain ⟨L, rfl⟩ : ∃ L, n = L+L := ⟨n/2, by omega⟩
  have hL : (L+L)/2 = L := by omega
  rw [hL]
  obtain ⟨m, edge, base, port, hb, hinj, hne, hport⟩ := PEqualNP.Outside.L_lib_540 d L (by omega)
  have hb' : 2^(d+1) * min L (2^(d+1)) ≤ 20*m := hb
  refine good_mono _ _ hn m _ (hf_core d L hn (by omega) m edge base port hinj hne hport) ?_
  generalize 2^(d+1) * min L (2^(d+1)) = z at hb'
  omega

lemma ha_good_two (n w : Nat) (hn : 0 < n) (a M k : Nat) (hk : k = w+1)
    (h : ∃ (code : Fin M → Fin n → Bool) (base : Fin n × (Fin k → Bool) → Bool)
      (left right : Fin M → Fin n × (Fin k → Bool)),
      Function.Injective code ∧ Function.Injective left ∧ Function.Injective right ∧
      (∀ i, (left i).1.val < a ∧ a ≤ (right i).1.val ∧
        base (left i) = false ∧ base (right i) = false) ∧
      ∀ A B : Finset (Fin M), (Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
        ∀ i : Fin n, (fun slot =>
          base slot || decide (slot ∈ A.image left) || decide (slot ∈ B.image right))
          (i, fun j => x (loc n hn (i.val+j.val))) = true) = (A ∩ B).image code) :
    Good n w hn M := by
  subst hk
  obtain ⟨code, base, left, right, hcode, hleft, hright, hlr, hsol⟩ := h
  refine ⟨left, fun s => base s || decide (s ∈ Finset.univ.image right), hleft, ?_, ?_⟩
  · intro j
    have hnot : left j ∉ Finset.univ.image right := by
      intro hm
      obtain ⟨k, _, hk⟩ := Finset.mem_image.1 hm
      have h1 := (hlr k).2.1
      have h2 := (hlr j).1
      rw [hk] at h1
      omega
    simp only [(hlr j).2.2.1, hnot, decide_false, Bool.or_false]
  · intro A
    have hT : (fun s => (base s || decide (s ∈ Finset.univ.image right)) ||
        decide (s ∈ A.image left)) = (fun slot =>
          base slot || decide (slot ∈ A.image left) ||
            decide (slot ∈ Finset.univ.image right)) := by
      funext s
      exact Bool.or_right_comm _ _ _
    rw [hT]
    have e := congrArg Finset.card (hsol A Finset.univ)
    rw [Finset.inter_univ, Finset.card_image_of_injective _ hcode] at e
    have e2 : cnt (w := w) n hn (fun slot =>
          base slot || decide (slot ∈ A.image left) ||
            decide (slot ∈ Finset.univ.image right)) = A.card := e
    rw [e2]

lemma ha_pow_big (m : Nat) (hm : 6 ≤ m) : 4 * m + 10 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    omega

lemma ha_params (a b : Nat) (hab : a ≤ b) (hba : b ≤ a + 1) (h32 : 32 ≤ a + b) :
    2 * b ≤ 2 ^ Nat.clog 2 (2 * b) ∧ 5 ≤ Nat.clog 2 (2 * b) ∧ 2 * Nat.clog 2 (2 * b) + 3 ≤ a ∧
      2 ^ (Nat.clog 2 (2 * b) - 3) ≤ a - Nat.clog 2 (2 * b) - 1 := by
  set c := Nat.clog 2 (2 * b) with hc
  have h1 : 2 * b ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) _
  have ha : 16 ≤ a := by omega
  have h2 : 2 * c + 3 ≤ a := by
    have hm : c ≤ (a - 3) / 2 := by
      rw [hc, Nat.clog_le_iff_le_pow (by norm_num)]
      have := ha_pow_big ((a - 3) / 2) (by omega)
      omega
    omega
  have h5 : 5 ≤ c := by
    by_contra hlt
    have : 2 ^ c ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h3 : 2 ^ (c - 1) < 2 * b := by
    have := Nat.pow_pred_clog_lt_self (b := 2) (x := 2 * b) (by omega)
    rwa [← hc, Nat.pred_eq_sub_one] at this
  have h4 : 2 ^ (c - 1) = 2 ^ (c - 3) * 4 := by
    rw [show c - 1 = (c - 3) + 2 by omega, pow_add]
    norm_num
  refine ⟨h1, h5, h2, ?_⟩
  omega

lemma ha_M_bound (a b h c M : Nat) (hab : a ≤ b) (hh : h ≤ c) (h5 : 5 ≤ c) (h2 : 2 * c + 3 ≤ a)
    (h3 : 2 ^ (c - 3) ≤ a - c - 1)
    (hM : (a - h - 1) * 2 ^ (a - c - 3) * ((b - h - 1) * 2 ^ (b - c - 3)) ≤ M) :
    2 ^ (a + b - 13) ≤ M := by
  have ea : 2 ^ (c - 3) ≤ a - h - 1 := le_trans h3 (by omega)
  have eb : 2 ^ (c - 3) ≤ b - h - 1 := le_trans h3 (by omega)
  calc 2 ^ (a + b - 13) ≤ 2 ^ ((c - 3) + (a - c - 3) + ((c - 3) + (b - c - 3))) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 ^ (c - 3) * 2 ^ (a - c - 3) * (2 ^ (c - 3) * 2 ^ (b - c - 3)) := by
        rw [pow_add, pow_add, pow_add]
    _ ≤ (a - h - 1) * 2 ^ (a - c - 3) * ((b - h - 1) * 2 ^ (b - c - 3)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_right _ ea) (Nat.mul_le_mul_right _ eb)
    _ ≤ M := hM

lemma good_near (n w : Nat) (hn : 0 < n) (h32 : 32 ≤ n)
    (hc : n-(w+1) ≤ Nat.clog 2 (2*(n-n/2))) : Good n w hn (2^(n-13)) := by
  obtain ⟨a, b, rfl, hab, hba⟩ : ∃ a b, n = a + b ∧ a ≤ b ∧ b ≤ a + 1 :=
    ⟨n / 2, n - n / 2, by omega, by omega, by omega⟩
  have hb2 : a + b - (a + b) / 2 = b := by omega
  rw [hb2] at hc
  obtain ⟨hc1, hc5, hc2, hc3⟩ := ha_params a b hab hba h32
  obtain ⟨M, code, base, left, right, hM, hcode, hleft, hright, hlr, hsol⟩ :=
    PEqualNP.Outside.L_lib_845 a b w (Nat.clog 2 (2 * b)) hn hc
      (by rw [min_eq_left hab]; omega) (by rw [max_eq_right hab]; exact hc1)
  have hHM : 2^(a+b-13) ≤ M := ha_M_bound a b _ _ M hab hc hc5 hc2 hc3 hM
  have hg : Good (a+b) w hn M :=
    ha_good_two (a+b) w hn a M (w+1) rfl ⟨code, base, left, right, hcode, hleft, hright, hlr, hsol⟩
  exact good_mono (a+b) w hn M _ hg hHM

lemma good_far (n w : Nat) (hn : 0 < n) (a b q s : Nat) (hab : n = a+b) (hq : 0 < q) (hs : 0 < s)
    (hsh : s ≤ n-(w+1)) (h1 : q*(n-(w+1)) < a) (h2 : (q+1)*(n-(w+1)) ≤ b) :
    Good n w hn (q^2*(2^s-1)^(2*(q-1))*2^(n-(2*q*s+((n-(w+1))-s)))) := by
  subst hab
  have h := PEqualNP.Outside.L_lib_743 a b (a+b-(w+1)) s q hn hq hs hsh h1 h2
  exact ha_good_two (a+b) w hn a _ (a+b-(a+b-(w+1))) (by omega) h

lemma hb_plug (n w H : Nat) (slot : Fin H → Fin n × (Fin (w+1) → Bool))
    (base : Fin n × (Fin (w+1) → Bool) → Bool) (hbase : ∀ j, base (slot j) = false)
    (y : Fin H → Bool) (idx : Fin (n*2^(w+1))) :
    (if idx ∈ Finset.univ.image (fun j => enc n w (slot j)) then
      decide (∃ j, (fun j => enc n w (slot j)) j = idx ∧ y j = true)
      else (fun idx => base (dec n w idx)) idx) =
    (base (dec n w idx) ||
      decide (dec n w idx ∈ (Finset.univ.filter (fun j => y j = true)).image slot)) := by
  by_cases hm : ∃ j, enc n w (slot j) = idx
  · obtain ⟨j0, rfl⟩ := hm
    rw [if_pos (Finset.mem_image.mpr ⟨j0, Finset.mem_univ _, rfl⟩), dec_enc, hbase, Bool.false_or]
    apply decide_eq_decide.mpr
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, hy⟩
      have h2 := congrArg (dec n w) hj
      rw [dec_enc, dec_enc] at h2
      exact ⟨j, hy, h2⟩
    · rintro ⟨j, hy, hj⟩
      exact ⟨j, by rw [hj], hy⟩
  · have h1 : idx ∉ Finset.univ.image (fun j => enc n w (slot j)) := by
      intro hc
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hc
      exact hm ⟨j, hj⟩
    have h2 : dec n w idx ∉ (Finset.univ.filter (fun j => y j = true)).image slot := by
      intro hc
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hc
      exact hm ⟨j, by rw [hj, enc_dec]⟩
    rw [if_neg h1, decide_eq_false h2, Bool.or_false]

lemma hb_evalplug (n w : Nat) (hn : 0 < n) (H : Nat)
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hev : ∀ raw : Fin (n*2^(w+1)) → Bool, C.eval (List.ofFn raw) = fval n w hn raw)
    (slot : Fin H → Fin n × (Fin (w+1) → Bool))
    (base : Fin n × (Fin (w+1) → Bool) → Bool) (hbase : ∀ j, base (slot j) = false)
    (hpar : ∀ A : Finset (Fin H),
      cnt n w hn (fun s => base s || decide (s ∈ A.image slot)) % 2 = A.card % 2)
    (y : Fin H → Bool) :
    C.eval (List.ofFn (fun idx : Fin (n*2^(w+1)) =>
      if idx ∈ Finset.univ.image (fun j => enc n w (slot j)) then
      decide (∃ j, (fun j => enc n w (slot j)) j = idx ∧ y j = true)
      else (fun idx => base (dec n w idx)) idx)) =
    ((Finset.univ.filter (fun j => y j = true)).card).testBit 0 := by
  have h1 : (fun idx : Fin (n*2^(w+1)) =>
      if idx ∈ Finset.univ.image (fun j => enc n w (slot j)) then
      decide (∃ j, (fun j => enc n w (slot j)) j = idx ∧ y j = true)
      else (fun idx => base (dec n w idx)) idx) =
      fun idx => (fun s => base s ||
        decide (s ∈ (Finset.univ.filter (fun j => y j = true)).image slot)) (dec n w idx) :=
    funext (hb_plug n w H slot base hbase y)
  rw [h1, hev]
  refine (fval_tab n w hn (fun s => base s ||
        decide (s ∈ (Finset.univ.filter (fun j => y j = true)).image slot))).trans ?_
  rw [Nat.testBit_zero, Nat.testBit_zero, hpar]

lemma hb_slotdep (n w : Nat) (hn : 0 < n) (H : Nat)
    (slot : Fin H → Fin n × (Fin (w+1) → Bool))
    (base : Fin n × (Fin (w+1) → Bool) → Bool) (hbase : ∀ j, base (slot j) = false)
    (hpar : ∀ A : Finset (Fin H),
      cnt n w hn (fun s => base s || decide (s ∈ A.image slot)) % 2 = A.card % 2)
    (j : Fin H) :
    (cnt n w hn (Function.update base (slot j) false)).testBit 0 ≠
      (cnt n w hn (Function.update base (slot j) true)).testBit 0 := by
  have e0 : Function.update base (slot j) false =
      fun s => base s || decide (s ∈ (∅ : Finset (Fin H)).image slot) := by
    funext s
    by_cases hs : s = slot j
    · subst hs
      simp [hbase]
    · simp [Function.update_of_ne hs]
  have e1 : Function.update base (slot j) true =
      fun s => base s || decide (s ∈ ({j} : Finset (Fin H)).image slot) := by
    funext s
    by_cases hs : s = slot j
    · subst hs
      simp
    · simp [hs]
  have p0 := hpar ∅
  have p1 := hpar {j}
  rw [← e0] at p0
  rw [← e1] at p1
  rw [Nat.testBit_zero, Nat.testBit_zero, p0, p1]
  simp

lemma hb_parity (H : Nat) (hH : 0 < H) (D : PEqualNP.CircuitLowerBounds.Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo D)
    (hev : ∀ y : Fin H → Bool, D.eval (List.ofFn y) =
      ((Finset.univ.filter (fun j => y j = true)).card).testBit 0) :
    3*(H-1) ≤ D.gates.length - (D.gates.filter (fun g =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length ∧
    4*(H-1) ≤ D.gates.length := by
  have hm := PEqualNP.Outside.L_meta_25689 H H hH
  dsimp only at hm
  have hm2 := (hm (fun i => i) (fun j x => x j) (fun j => ⟨j, rfl⟩)
    (fun j x y hxy => hxy j rfl)
    (fun i => ⟨fun _ => false, by simp, by simp⟩)
    (fun j => ⟨⟨[], j.val⟩, by intro g hg; simp at hg, by
      simp [PEqualNP.CircuitLowerBounds.Circuit.size, Finset.filter_eq'], by
      intro x
      simp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]⟩)).2
    D ⟨hfan, hev⟩
  simp only [PEqualNP.CircuitLowerBounds.Circuit.size] at hm2
  omega

lemma lower_core (n w : Nat) (hn : 0 < n) (H : Nat) (hH : 0 < H) (hg : Good n w hn H)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hev : ∀ raw : Fin (n*2^(w+1)) → Bool, C.eval (List.ofFn raw) = fval n w hn raw) :
    (n*2^(min n (w+1)) - H) + 3*(H-1) ≤ C.size - (C.gates.filter (fun g =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length ∧
    (n*2^(min n (w+1)) - H) + 4*(H-1) ≤ C.size := by
  obtain ⟨slot, base, hinj, hbase, hpar⟩ := hg
  have winj : Function.Injective (fun j => enc n w (slot j)) := by
    intro a b hab
    have h2 := congrArg (dec n w) hab
    rw [dec_enc, dec_enc] at h2
    exact hinj h2
  have hpl := hb_evalplug n w hn H C hev slot base hbase hpar
  have h586 := PEqualNP.Outside.L_lib_586 (n*2^(w+1)) H C hfan
    (fun j => enc n w (slot j)) (fun idx => base (dec n w idx)) winj
  have hnc : ((Finset.univ.filter (fun j : Fin H => (fun _ => false : Fin H → Bool) j = true)).card).testBit 0
      ≠ ((Finset.univ.filter (fun j : Fin H =>
        (fun j => decide (j = (⟨0, hH⟩ : Fin H))) j = true)).card).testBit 0 := by
    simp [Finset.filter_eq']
  obtain ⟨D, hDfan, hDbin, hDinv, hDev⟩ := h586 ⟨fun _ => false,
    fun j => decide (j = (⟨0, hH⟩ : Fin H)), fun heq =>
      hnc ((hpl _).symm.trans (heq.trans (hpl _)))⟩
  have hDev2 : ∀ y : Fin H → Bool, D.eval (List.ofFn y) =
      ((Finset.univ.filter (fun j => y j = true)).card).testBit 0 :=
    fun y => (hDev y).trans (hpl y)
  have hD := hb_parity H hH D hDfan hDev2
  have hE : n*2^(min n (w+1)) ≤ ((Finset.univ : Finset (Fin (n*2^(w+1)))).filter (fun i =>
      ∃ x : Fin (n*2^(w+1)) → Bool, C.eval (List.ofFn (Function.update x i false)) ≠
        C.eval (List.ofFn (Function.update x i true)))).card := by
    simp only [hev]
    exact dep_count n w hn
  have hHe : H ≤ ((Finset.univ : Finset (Fin (n*2^(w+1)))).filter (fun i =>
      ∃ x : Fin (n*2^(w+1)) → Bool, C.eval (List.ofFn (Function.update x i false)) ≠
        C.eval (List.ofFn (Function.update x i true)))).card := by
    have h3 := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin H)))
      (t := ((Finset.univ : Finset (Fin (n*2^(w+1)))).filter (fun i =>
      ∃ x : Fin (n*2^(w+1)) → Bool, C.eval (List.ofFn (Function.update x i false)) ≠
        C.eval (List.ofFn (Function.update x i true))))) (fun j => enc n w (slot j))
      (by
        intro j _
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simp only [hev]
        exact dep_mem n w hn base (slot j) (hb_slotdep n w hn H slot base hbase hpar j))
      (fun a _ b _ hab => winj hab)
    rwa [Finset.card_univ, Fintype.card_fin] at h3
  have hDbin2 : (D.gates.length - (D.gates.filter (fun g =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length) +
      ((Finset.univ : Finset (Fin (n*2^(w+1)))).filter (fun i =>
      ∃ x : Fin (n*2^(w+1)) → Bool, C.eval (List.ofFn (Function.update x i false)) ≠
        C.eval (List.ofFn (Function.update x i true)))).card ≤
      (C.gates.length - (C.gates.filter (fun g =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length) + H :=
    hDbin
  have hDinv2 : (D.gates.filter (fun g =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length ≤
      (C.gates.filter (fun g =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length :=
    hDinv
  have hiC := List.length_filter_le (fun g : PEqualNP.CircuitLowerBounds.Gate =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _)) C.gates
  have hiD := List.length_filter_le (fun g : PEqualNP.CircuitLowerBounds.Gate =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _)) D.gates
  simp only [PEqualNP.CircuitLowerBounds.Circuit.size]
  generalize ((Finset.univ : Finset (Fin (n*2^(w+1)))).filter (fun i =>
      ∃ x : Fin (n*2^(w+1)) → Bool, C.eval (List.ofFn (Function.update x i false)) ≠
        C.eval (List.ofFn (Function.update x i true)))).card = e at hE hHe hDbin2
  generalize n*2^(min n (w+1)) = E at hE ⊢
  generalize (C.gates.filter (fun g =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length = iC
    at hDbin2 hDinv2 hiC ⊢
  generalize (D.gates.filter (fun g =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length = iD
    at hDbin2 hDinv2 hiD hD
  omega

open PEqualNP.CircuitLowerBounds in
lemma hg_pre (gs : List Gate) (x : List Bool) :
    ∃ G : List Bool,
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x = x ++ G ∧
      G.length = gs.length := by
  induction gs generalizing x with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨G, h1, h2⟩ := ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
    refine ⟨[g.op.eval (g.inputs.map fun i => x.getD i false)] ++ G, ?_, ?_⟩
    · rw [List.foldl_cons, h1, List.append_assoc]
    · simp only [List.length_append, List.length_cons, List.length_nil, h2]
      omega

def hg_rho (a b : Nat) (φ : Fin a → Fin b) (k : Nat) : Nat :=
  if h : k < a then (φ ⟨k, h⟩).val else k - a + b

lemma hg_ofFn_getD (N : Nat) (x : Fin N → Bool) (G : List Bool) (k : Fin N) :
    (List.ofFn x ++ G).getD k.val false = x k := by
  have h : k.val < (List.ofFn x).length := by simp
  rw [List.getD_append _ _ _ _ h, List.getD_eq_getElem _ _ h, List.getElem_ofFn]

lemma hg_getD (a b : Nat) (φ : Fin a → Fin b) (x : Fin b → Bool) (G : List Bool) (k : Nat) :
    (List.ofFn x ++ G).getD (hg_rho a b φ k) false =
      (List.ofFn (fun k => x (φ k)) ++ G).getD k false := by
  unfold hg_rho
  split_ifs with h
  · rw [hg_ofFn_getD]
    exact (hg_ofFn_getD a (fun k => x (φ k)) G ⟨k, h⟩).symm
  · rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp; omega)]
    congr 1
    simp only [List.length_ofFn]
    omega

open PEqualNP.CircuitLowerBounds in
def hg_rel (C : Circuit) (a b : Nat) (φ : Fin a → Fin b) : Circuit :=
  ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map (hg_rho a b φ)⟩), hg_rho a b φ C.output⟩

open PEqualNP.CircuitLowerBounds in
lemma hg_fold (a b : Nat) (φ : Fin a → Fin b) (x : Fin b → Bool) (gs : List Gate) (G : List Bool) :
    ∃ G' : List Bool,
      (gs.map (fun g => (⟨g.op, g.inputs.map (hg_rho a b φ)⟩ : Gate))).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x ++ G) =
        List.ofFn x ++ G' ∧
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn (fun k => x (φ k)) ++ G) = List.ofFn (fun k => x (φ k)) ++ G' := by
  induction gs generalizing G with
  | nil => exact ⟨G, rfl, rfl⟩
  | cons g gs ih =>
    obtain ⟨G', h1, h2⟩ := ih (G ++ [g.op.eval (g.inputs.map fun i =>
      (List.ofFn (fun k => x (φ k)) ++ G).getD i false)])
    have hv : g.op.eval ((g.inputs.map (hg_rho a b φ)).map fun i =>
        (List.ofFn x ++ G).getD i false) =
        g.op.eval (g.inputs.map fun i => (List.ofFn (fun k => x (φ k)) ++ G).getD i false) := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro k _
      exact hg_getD a b φ x G k
    refine ⟨G', ?_, ?_⟩
    · rw [List.map_cons, List.foldl_cons]
      dsimp only
      rw [hv, List.append_assoc]
      exact h1
    · rw [List.foldl_cons, List.append_assoc]
      exact h2

open PEqualNP.CircuitLowerBounds in
lemma hg_rel_eval (C : Circuit) (a b : Nat) (φ : Fin a → Fin b) (x : Fin b → Bool) :
    (hg_rel C a b φ).eval (List.ofFn x) = C.eval (List.ofFn (fun k => x (φ k))) := by
  obtain ⟨G', h1, h2⟩ := hg_fold a b φ x C.gates []
  simp only [List.append_nil] at h1 h2
  unfold Circuit.eval Circuit.wires
  dsimp only [hg_rel]
  rw [h1, h2]
  exact hg_getD a b φ x G' C.output

open PEqualNP.CircuitLowerBounds in
lemma hg_rel_fan (C : Circuit) (a b : Nat) (φ : Fin a → Fin b)
    (h : PEqualNP.MetaComplexity.FanInTwo C) : PEqualNP.MetaComplexity.FanInTwo (hg_rel C a b φ) := by
  intro g hg
  dsimp only [hg_rel] at hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  have := h g0 hg0
  refine ⟨this.1, ?_⟩
  simp only [List.length_map]
  exact this.2

open PEqualNP.CircuitLowerBounds in
lemma hg_rel_size (C : Circuit) (a b : Nat) (φ : Fin a → Fin b) :
    (hg_rel C a b φ).size = C.size := by
  simp only [hg_rel, Circuit.size, List.length_map]

open PEqualNP.CircuitLowerBounds in
lemma hg_rel_inv (C : Circuit) (a b : Nat) (φ : Fin a → Fin b) :
    ((hg_rel C a b φ).gates.filter (fun g =>
      @decide (g.op = GateOp.not) (Classical.propDecidable _))).length =
    (C.gates.filter (fun g => @decide (g.op = GateOp.not) (Classical.propDecidable _))).length := by
  dsimp only [hg_rel]
  rw [List.filter_map, List.length_map]
  rfl

open PEqualNP.CircuitLowerBounds in
lemma hg_and (N : Nat) (l : List (Fin N)) (hl : l ≠ []) :
    ∃ P : Circuit, PEqualNP.MetaComplexity.Monotone2 P ∧ P.size + 1 = l.length ∧
      ∀ x : Fin N → Bool, P.eval (List.ofFn x) = l.all (fun t => x t) := by
  induction l with
  | nil => exact absurd rfl hl
  | cons t l ih =>
    by_cases hl' : l = []
    · subst hl'
      refine ⟨⟨[], t.val⟩, ?_, rfl, ?_⟩
      · intro g hg
        simp at hg
      · intro x
        have := hg_ofFn_getD N x [] t
        simp only [List.append_nil] at this
        simp only [Circuit.eval, Circuit.wires, List.foldl_nil, this, List.all_cons, List.all_nil,
          Bool.and_true]
    · obtain ⟨P0, hm, hs, hev⟩ := ih hl'
      refine ⟨⟨P0.gates ++ [⟨GateOp.and, [t.val, P0.output]⟩], N + P0.size⟩, ?_, ?_, ?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hm g hg
        · rw [List.mem_singleton] at hg
          subst hg
          exact ⟨Or.inl rfl, le_refl _⟩
      · simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil] at hs ⊢
        omega
      · intro x
        obtain ⟨G, h1, h2⟩ := hg_pre P0.gates (List.ofFn x)
        have he := hev x
        unfold Circuit.eval Circuit.wires at he
        rw [h1] at he
        unfold Circuit.eval Circuit.wires
        dsimp only
        rw [List.foldl_append, h1, List.foldl_cons, List.foldl_nil]
        have hlen : N + P0.size = (List.ofFn x ++ G).length := by
          simp only [List.length_append, List.length_ofFn, h2, Circuit.size]
        rw [hlen, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
        simp only [List.getD_cons_zero, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
          List.all_nil, Bool.and_true, id, he, hg_ofFn_getD]

lemma hg_idx_lt (n J : Nat) (i : Fin n) (v : Fin J) : i.val * J + v.val < n * J := by
  have h1 : (i.val + 1) * J ≤ n * J := Nat.mul_le_mul_right J i.isLt
  have h2 := v.isLt
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

def hg_idx (n J : Nat) (i : Fin n) (v : Fin J) : Fin (n * J) := ⟨i.val * J + v.val, hg_idx_lt n J i v⟩

lemma hg_mod_lt (n J : Nat) (hn : 0 < n) (t : Fin (n * J)) : t.val % J < J := by
  apply Nat.mod_lt
  rcases Nat.eq_zero_or_pos J with h | h
  · have h1 := t.isLt
    have h2 : n * J = 0 := by
      rw [h]
      exact Nat.mul_zero n
    omega
  · exact h

lemma hg_div_lt (n J : Nat) (t : Fin (n * J)) : t.val / J < n := by
  apply Nat.div_lt_of_lt_mul
  have h1 := t.isLt
  have h2 : J * n = n * J := Nat.mul_comm J n
  omega

def hg_own (n J : Nat) (hn : 0 < n) (t : Fin (n * J)) : Fin J := ⟨t.val % J, hg_mod_lt n J hn t⟩

def hg_row (n J : Nat) (t : Fin (n * J)) : Fin n := ⟨t.val / J, hg_div_lt n J t⟩

lemma hg_own_idx (n J : Nat) (hn : 0 < n) (i : Fin n) (v : Fin J) :
    hg_own n J hn (hg_idx n J i v) = v := by
  apply Fin.ext
  show (i.val * J + v.val) % J = v.val
  rw [Nat.add_comm, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt v.isLt

lemma hg_row_idx (n J : Nat) (i : Fin n) (v : Fin J) :
    hg_row n J (hg_idx n J i v) = i := by
  apply Fin.ext
  show (i.val * J + v.val) / J = i.val
  have hJ : 0 < J := Nat.pos_of_ne_zero (fun h => by have := v.isLt; omega)
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hJ, Nat.div_eq_of_lt v.isLt, Nat.zero_add]

lemma hg_idx_row_own (n J : Nat) (hn : 0 < n) (t : Fin (n * J)) :
    hg_idx n J (hg_row n J t) (hg_own n J hn t) = t := by
  apply Fin.ext
  show t.val / J * J + t.val % J = t.val
  exact Nat.div_add_mod' _ _

def hg_block (n J : Nat) (v : Fin J) (z : Fin (n * J) → Bool) : Bool :=
  (List.ofFn (fun i : Fin n => hg_idx n J i v)).all (fun t => z t)

lemma hg_block_iff (n J : Nat) (v : Fin J) (z : Fin (n * J) → Bool) :
    hg_block n J v z = true ↔ ∀ i : Fin n, z (hg_idx n J i v) = true := by
  unfold hg_block
  rw [List.all_eq_true]
  constructor
  · intro h i
    exact h _ ((List.mem_ofFn' _ _).mpr ⟨i, rfl⟩)
  · intro h t ht
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp ht
    exact h i

def hg_phi (n w : Nat) (hn : 0 < n) (ev : Fin (2^n) ≃ (Fin n → Bool)) (t : Fin (n * 2^n)) :
    Fin (n * 2^(w+1)) :=
  enc n w (hg_row n (2^n) t,
    fun j => ev (hg_own n (2^n) hn t) (loc n hn ((hg_row n (2^n) t).val + j.val)))

lemma hg_read (n w : Nat) (hn : 0 < n) (raw : Fin (n*2^(w+1)) → Bool) (x : Fin n → Bool)
    (i : Fin n) :
    (List.ofFn raw).getD (i.val*2^(w+1) +
      ∑ j : Fin (w+1), if x (loc n hn (i.val+j.val)) then 2^j.val else 0) false =
    raw (enc n w (i, fun j => x (loc n hn (i.val + j.val)))) := by
  have := hg_ofFn_getD _ raw [] (enc n w (i, fun j => x (loc n hn (i.val + j.val))))
  rw [List.append_nil] at this
  exact this

lemma hg_core (n : Nat) (hn : 0 < n) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      (∀ z : Fin (n * 2^n) → Bool, C.eval (List.ofFn z) =
        (((Finset.univ : Finset (Fin (2^n))).filter
          (fun v => hg_block n (2^n) v z = true)).card).testBit 0) ∧
      C.size - (C.gates.filter (fun g =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length =
        (n*2^n - 2^n) + 3*(2^n-1) ∧
      C.size = (n*2^n - 2^n) + 4*(2^n-1) := by
  have hJ : 0 < 2^n := Nat.pos_of_ne_zero (by positivity)
  have key := PEqualNP.Outside.L_meta_25689 (n * 2^n) (2^n) hJ (hg_own n (2^n) hn)
    (hg_block n (2^n)) ?_ ?_ ?_ ?_
  · obtain ⟨⟨C, ⟨hfan, hev⟩, hb, hs⟩, -⟩ := key
    exact ⟨C, hfan, hev, hb, hs⟩
  · intro v
    exact ⟨hg_idx n (2^n) ⟨0, hn⟩ v, hg_own_idx n (2^n) hn _ v⟩
  · intro j x y h
    rw [Bool.eq_iff_iff, hg_block_iff, hg_block_iff]
    have h' : ∀ i : Fin n, x (hg_idx n (2^n) i j) = y (hg_idx n (2^n) i j) :=
      fun i => h _ (hg_own_idx n (2^n) hn i j)
    constructor
    · intro hx i
      rw [← h' i]
      exact hx i
    · intro hy i
      rw [h' i]
      exact hy i
  · intro t
    refine ⟨fun _ => true, ?_, ?_⟩
    · rw [← Bool.not_eq_true, hg_block_iff]
      intro h
      have := h (hg_row n (2^n) t)
      rw [hg_idx_row_own, Function.update_self] at this
      exact Bool.false_ne_true this
    · rw [hg_block_iff]
      intro i
      rw [Function.update_eq_self]
  · intro v
    obtain ⟨P, hm, hs, hev⟩ := hg_and (n * 2^n) (List.ofFn (fun i : Fin n => hg_idx n (2^n) i v))
      (by
        intro h
        have := congrArg List.length h
        simp only [List.length_ofFn, List.length_nil] at this
        omega)
    refine ⟨P, hm, ?_, fun x => hev x⟩
    rw [hs, List.length_ofFn]
    have hc : (Finset.univ : Finset (Fin n)).card ≤
        ((Finset.univ : Finset (Fin (n * 2^n))).filter
          (fun t => hg_own n (2^n) hn t = v)).card := by
      apply Finset.card_le_card_of_injOn (fun i => hg_idx n (2^n) i v)
      · intro i _
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
        exact hg_own_idx n (2^n) hn i v
      · intro i _ i' _ h
        have := congrArg (hg_row n (2^n)) h
        rwa [hg_row_idx, hg_row_idx] at this
    rw [Finset.card_univ, Fintype.card_fin] at hc
    exact hc

lemma upper (n w : Nat) (hn : 0 < n) (hle : n ≤ w+1) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      (∀ raw : Fin (n*2^(w+1)) → Bool, C.eval (List.ofFn raw) = fval n w hn raw) ∧
      C.size - (C.gates.filter (fun g =>
        @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length =
        (n*2^n - 2^n) + 3*(2^n-1) ∧
      C.size = (n*2^n - 2^n) + 4*(2^n-1) := by
  obtain ⟨C0, hfan, hev, hb, hs⟩ := hg_core n hn
  have ev : Fin (2^n) ≃ (Fin n → Bool) :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin])).symm
  refine ⟨hg_rel C0 (n * 2^n) (n * 2^(w+1)) (hg_phi n w hn ev), hg_rel_fan _ _ _ _ hfan, ?_, ?_, ?_⟩
  · intro raw
    rw [hg_rel_eval, hev]
    unfold fval
    congr 1
    apply Finset.card_equiv ev
    intro v
    rw [Finset.mem_filter, Finset.mem_filter, hg_block_iff]
    simp only [Finset.mem_univ, true_and]
    apply forall_congr'
    intro i
    rw [hg_read]
    unfold hg_phi
    rw [hg_own_idx, hg_row_idx]
  · rw [hg_rel_size, hg_rel_inv]
    exact hb
  · rw [hg_rel_size]
    exact hs

end PEqualNP.Outside.L_clb_120

theorem PEqualNP.Outside.L_clb_120 : (∀ (n w : Nat) (hn : 0 < n),
  let P := 2^(w+1)
  let J := 2^(min n (w+1))
  let E := n*J
  let h := n-(w+1)
  let D := 2^w
  let admissible := fun H : Nat => H ≤ J ∨
    (0 < w ∧ 2*w ≤ n ∧ n % 2 = 0 ∧ H ≤ (D*min (n/2) D+19)/20) ∨
    (32 ≤ n ∧ h ≤ Nat.clog 2 (2*(n-n/2)) ∧ H ≤ 2^(n-13)) ∨
    (∃ a b q s : Nat, n = a+b ∧ 0 < q ∧ 0 < s ∧ s ≤ h ∧ q*h < a ∧
      (q+1)*h ≤ b ∧ H ≤ q^2*(2^s-1)^(2*(q-1))*2^(n-(2*q*s+(h-s))))
  let inv := fun (G : PEqualNP.CircuitLowerBounds.Circuit) =>
    (G.gates.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length
  let binary := fun (G : PEqualNP.CircuitLowerBounds.Circuit) => G.size - inv G
  let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
  let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ ∀ raw : Fin (n*P) → Bool,
      let entries := List.ofFn raw
      let pass := fun (x : Fin n → Bool) => ∀ i : Fin n,
        let word := ∑ j : Fin (w+1), if x (loc (i.val+j.val)) then 2^j.val else 0
        entries.getD (i.val*P+word) false = true
      C.eval entries = (((Finset.univ : Finset (Fin n → Bool)).filter pass).card).testBit 0
  (∀ (H : Nat), 0 < H → admissible H → ∀ C, fits C →
     (E-H)+3*(H-1) ≤ binary C ∧ (E-H)+4*(H-1) ≤ C.size) ∧
    (n ≤ w+1 → ∃ C, fits C ∧ binary C = (E-J)+3*(J-1) ∧ C.size = (E-J)+4*(J-1))) := by
  intro n w hn P J E h D admissible inv binary loc fits
  refine ⟨?_, ?_⟩
  · intro H hH hadm C hfit
    have hg : PEqualNP.Outside.L_clb_120.Good n w hn H := by
      rcases hadm with h1 | ⟨hw, h2, he, hb⟩ | ⟨h32, hc, hb⟩ | ⟨a, b, q, s, hab, hq, hs, hsh, h1, h2, hb⟩
      · exact PEqualNP.Outside.L_clb_120.good_mono n w hn _ H
          (PEqualNP.Outside.L_clb_120.good_direct n w hn) h1
      · exact PEqualNP.Outside.L_clb_120.good_mono n w hn _ H
          (PEqualNP.Outside.L_clb_120.good_arcs n w hn hw h2 he) hb
      · exact PEqualNP.Outside.L_clb_120.good_mono n w hn _ H
          (PEqualNP.Outside.L_clb_120.good_near n w hn h32 hc) hb
      · exact PEqualNP.Outside.L_clb_120.good_mono n w hn _ H
          (PEqualNP.Outside.L_clb_120.good_far n w hn a b q s hab hq hs hsh h1 h2) hb
    exact PEqualNP.Outside.L_clb_120.lower_core n w hn H hH hg C hfit.1 hfit.2
  · intro hle
    obtain ⟨C, hfan, hev, hb, hs⟩ := PEqualNP.Outside.L_clb_120.upper n w hn hle
    have hJ : J = 2^n := by
      show 2^(min n (w+1)) = 2^n
      rw [min_eq_left hle]
    refine ⟨C, ⟨hfan, hev⟩, ?_, ?_⟩
    · show C.size - _ = (n*J - J) + 3*(J-1)
      rw [hJ]
      exact hb
    · show C.size = (n*J - J) + 4*(J-1)
      rw [hJ]
      exact hs
