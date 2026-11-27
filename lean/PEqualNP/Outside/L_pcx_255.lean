import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_255_aux

def step (a : Bool) (e i : ℕ) : Bool := if i ≤ e then a else !a

def P (l r e : ℕ) : Finset ℕ :=
  if h : r ≤ l + 1 then {l, r} else
    if e < (l + r) / 2 then insert r (P l ((l + r) / 2) e) else insert l (P ((l + r) / 2) r e)
termination_by r - l
decreasing_by all_goals omega

theorem P_base {l r : ℕ} (e : ℕ) (h : r ≤ l + 1) : P l r e = {l, r} := by
  rw [P]; simp [h]

theorem P_left {l r e : ℕ} (h : l + 2 ≤ r) (he : e < (l + r) / 2) :
    P l r e = insert r (P l ((l + r) / 2) e) := by
  rw [P]; simp [show ¬ r ≤ l + 1 by omega, he]

theorem P_right {l r e : ℕ} (h : l + 2 ≤ r) (he : ¬ e < (l + r) / 2) :
    P l r e = insert l (P ((l + r) / 2) r e) := by
  rw [P]; simp [show ¬ r ≤ l + 1 by omega, he]

theorem P_sub : ∀ d l r e, r - l = d → l ≤ r → ∀ i ∈ P l r e, l ≤ i ∧ i ≤ r := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro l r e hd hlr i hi
    by_cases h : r ≤ l + 1
    · rw [P_base e h] at hi; simp at hi; omega
    · by_cases he : e < (l + r) / 2
      · rw [P_left (by omega) he] at hi
        simp at hi
        rcases hi with rfl | hi
        · omega
        · have := ih ((l + r) / 2 - l) (by omega) l ((l + r) / 2) e rfl (by omega) i hi
          omega
      · rw [P_right (by omega) he] at hi
        simp at hi
        rcases hi with rfl | hi
        · omega
        · have := ih (r - (l + r) / 2) (by omega) ((l + r) / 2) r e rfl (by omega) i hi
          omega

theorem l_mem : ∀ d l r e, r - l = d → l < r → l ∈ P l r e := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro l r e hd hlr
    by_cases h : r ≤ l + 1
    · rw [P_base e h]; simp
    · by_cases he : e < (l + r) / 2
      · rw [P_left (by omega) he]
        exact Finset.mem_insert_of_mem (ih ((l + r) / 2 - l) (by omega) l _ e rfl (by omega))
      · rw [P_right (by omega) he]; simp

theorem r_mem : ∀ d l r e, r - l = d → l < r → r ∈ P l r e := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro l r e hd hlr
    by_cases h : r ≤ l + 1
    · rw [P_base e h]; simp
    · by_cases he : e < (l + r) / 2
      · rw [P_left (by omega) he]; simp
      · rw [P_right (by omega) he]
        exact Finset.mem_insert_of_mem (ih (r - (l + r) / 2) (by omega) _ r e rfl (by omega))

theorem mid_mem {l r : ℕ} (e : ℕ) (h : l + 2 ≤ r) : (l + r) / 2 ∈ P l r e := by
  by_cases he : e < (l + r) / 2
  · rw [P_left h he]
    exact Finset.mem_insert_of_mem (r_mem _ l _ e rfl (by omega))
  · rw [P_right h he]
    exact Finset.mem_insert_of_mem (l_mem _ _ r e rfl (by omega))

theorem P_card_le : ∀ d l r e, r - l = d → l < r → (P l r e).card ≤ 2 + Nat.clog 2 (r - l) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro l r e hd hlr
    by_cases h : r ≤ l + 1
    · rw [P_base e h]
      have : r = l + 1 := by omega
      subst this
      simp
    · have hc : 1 ≤ Nat.clog 2 (r - l) := by
        apply Nat.succ_le_of_lt
        apply Nat.clog_pos (by norm_num)
        omega
      have hle : r - l ≤ 2 ^ Nat.clog 2 (r - l) := Nat.le_pow_clog (by norm_num) _
      by_cases he : e < (l + r) / 2
      · rw [P_left (by omega) he]
        have hn : r ∉ P l ((l + r) / 2) e := by
          intro hm
          have := P_sub ((l + r) / 2 - l) l ((l + r) / 2) e rfl (by omega) r hm
          omega
        rw [Finset.card_insert_of_notMem hn]
        have ih' := ih ((l + r) / 2 - l) (by omega) l ((l + r) / 2) e rfl (by omega)
        have : Nat.clog 2 ((l + r) / 2 - l) ≤ Nat.clog 2 (r - l) - 1 := by
          rw [Nat.clog_le_iff_le_pow (by norm_num)]
          obtain ⟨c, hc'⟩ : ∃ c, Nat.clog 2 (r - l) = c + 1 := ⟨Nat.clog 2 (r - l) - 1, by omega⟩
          rw [hc'] at hle ⊢
          rw [pow_succ] at hle
          simp only [Nat.add_sub_cancel]
          omega
        omega
      · rw [P_right (by omega) he]
        have hn : l ∉ P ((l + r) / 2) r e := by
          intro hm
          have := P_sub (r - (l + r) / 2) ((l + r) / 2) r e rfl (by omega) l hm
          omega
        rw [Finset.card_insert_of_notMem hn]
        have ih' := ih (r - (l + r) / 2) (by omega) ((l + r) / 2) r e rfl (by omega)
        have : Nat.clog 2 (r - (l + r) / 2) ≤ Nat.clog 2 (r - l) - 1 := by
          rw [Nat.clog_le_iff_le_pow (by norm_num)]
          obtain ⟨c, hc'⟩ : ∃ c, Nat.clog 2 (r - l) = c + 1 := ⟨Nat.clog 2 (r - l) - 1, by omega⟩
          rw [hc'] at hle ⊢
          rw [pow_succ] at hle
          simp only [Nat.add_sub_cancel]
          omega
        omega

theorem P_card_pow : ∀ h l e, l ≤ e → e < l + 2 ^ h → (P l (l + 2 ^ h) e).card = 2 + h := by
  intro h
  induction h with
  | zero =>
    intro l e h1 h2
    rw [P_base e (by simp)]
    simp
  | succ h ih =>
    intro l e h1 h2
    have hp : 2 ^ (h + 1) = 2 * 2 ^ h := by ring
    have hpos : 0 < 2 ^ h := by positivity
    have hmid : (l + (l + 2 ^ (h + 1))) / 2 = l + 2 ^ h := by omega
    by_cases he : e < l + 2 ^ h
    · rw [P_left (by omega) (by omega)]
      rw [hmid]
      have hn : l + 2 ^ (h + 1) ∉ P l (l + 2 ^ h) e := by
        intro hm
        have := P_sub _ l (l + 2 ^ h) e rfl (by omega) _ hm
        omega
      rw [Finset.card_insert_of_notMem hn, ih l e h1 he]
      ring
    · rw [P_right (by omega) (by omega)]
      rw [hmid]
      have hn : l ∉ P (l + 2 ^ h) (l + 2 ^ (h + 1)) e := by
        intro hm
        have := P_sub _ _ _ e rfl (by omega) _ hm
        omega
      rw [Finset.card_insert_of_notMem hn]
      have := ih (l + 2 ^ h) e (by omega) (by omega)
      have e2 : l + 2 ^ (h + 1) = l + 2 ^ h + 2 ^ h := by omega
      rw [e2, this]
      ring

theorem P_uniq (p : ℕ → Bool) (a : Bool) : ∀ d l r e e', r - l = d → l < r → l ≤ e → e < r →
    l ≤ e' → e' < r → (∀ i ∈ P l r e, p i = step a e i) → (∀ i ∈ P l r e', p i = step a e' i) →
    e = e' := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro l r e e' hd hlr h1 h2 h3 h4 hp hp'
    by_cases h : r ≤ l + 1
    · omega
    · have hm1 := hp _ (mid_mem e (by omega))
      have hm2 := hp' _ (mid_mem e' (by omega))
      have hcc : ((l + r) / 2 ≤ e ↔ (l + r) / 2 ≤ e') := by
        unfold step at hm1 hm2
        rcases em ((l + r) / 2 ≤ e) with c1 | c1 <;> rcases em ((l + r) / 2 ≤ e') with c2 | c2
        · exact ⟨fun _ => c2, fun _ => c1⟩
        · exfalso
          simp only [c1, c2, if_true, if_false] at hm1 hm2
          rw [hm1] at hm2
          cases a <;> simp at hm2
        · exfalso
          simp only [c1, c2, if_true, if_false] at hm1 hm2
          rw [hm1] at hm2
          cases a <;> simp at hm2
        · exact ⟨fun h => absurd h c1, fun h => absurd h c2⟩
      by_cases he : e < (l + r) / 2
      · have he' : e' < (l + r) / 2 := by omega
        rw [P_left (by omega) he] at hp
        rw [P_left (by omega) he'] at hp'
        exact ih ((l + r) / 2 - l) (by omega) l _ e e' rfl (by omega) h1 he h3 he'
          (fun i hi => hp i (Finset.mem_insert_of_mem hi))
          (fun i hi => hp' i (Finset.mem_insert_of_mem hi))
      · have he' : ¬ e' < (l + r) / 2 := by omega
        rw [P_right (by omega) he] at hp
        rw [P_right (by omega) he'] at hp'
        exact ih (r - (l + r) / 2) (by omega) _ r e e' rfl (by omega) (by omega) h2 (by omega) h4
          (fun i hi => hp i (Finset.mem_insert_of_mem hi))
          (fun i hi => hp' i (Finset.mem_insert_of_mem hi))

theorem P_exists (p : ℕ → Bool) (a : Bool) : ∀ d l r, r - l = d → l < r → p l = a → p r = !a →
    ∃ e, l ≤ e ∧ e < r ∧ ∀ i ∈ P l r e, p i = step a e i := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro l r hd hlr hl hr
    by_cases h : r ≤ l + 1
    · refine ⟨l, le_refl _, by omega, ?_⟩
      rw [P_base l h]
      intro i hi
      simp at hi
      rcases hi with h' | h'
      · rw [h']; simp [step, hl]
      · rw [h', hr]
        simp [step, show ¬ r ≤ l by omega]
    · by_cases hc : p ((l + r) / 2) = a
      · obtain ⟨e, h1, h2, h3⟩ := ih (r - (l + r) / 2) (by omega) _ r rfl (by omega) hc hr
        have he : ¬ e < (l + r) / 2 := by omega
        refine ⟨e, by omega, h2, ?_⟩
        rw [P_right (by omega) he]
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simp [step, hl, show i ≤ e by omega]
        · exact h3 i hi
      · have hc' : p ((l + r) / 2) = !a := by
          cases a <;> cases hh : p ((l + r) / 2) <;> simp_all
        obtain ⟨e, h1, h2, h3⟩ := ih ((l + r) / 2 - l) (by omega) l _ rfl (by omega) hl hc'
        have he : e < (l + r) / 2 := h2
        refine ⟨e, h1, by omega, ?_⟩
        rw [P_left (by omega) he]
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simp [step, hr, show ¬ i ≤ e by omega]
        · exact h3 i hi

theorem P_ends (p : ℕ → Bool) (a : Bool) {l r e : ℕ} (hlr : l < r) (h1 : l ≤ e) (h2 : e < r)
    (hp : ∀ i ∈ P l r e, p i = step a e i) : p l = a ∧ p r = !a := by
  have a1 := hp l (l_mem _ l r e rfl hlr)
  have a2 := hp r (r_mem _ l r e rfl hlr)
  simp [step, h1, show ¬ r ≤ e by omega] at a1 a2
  exact ⟨a1, a2⟩

theorem leaf_mem : ∀ d l r e, r - l = d → l ≤ e → e < r → e ∈ P l r e ∧ e + 1 ∈ P l r e := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro l r e hd h1 h2
    by_cases h : r ≤ l + 1
    · rw [P_base e h]
      have : e = l := by omega
      have : r = l + 1 := by omega
      simp_all
    · by_cases he : e < (l + r) / 2
      · rw [P_left (by omega) he]
        obtain ⟨a1, a2⟩ := ih ((l + r) / 2 - l) (by omega) l _ e rfl h1 he
        exact ⟨Finset.mem_insert_of_mem a1, Finset.mem_insert_of_mem a2⟩
      · rw [P_right (by omega) he]
        obtain ⟨a1, a2⟩ := ih (r - (l + r) / 2) (by omega) _ r e rfl (by omega) h2
        exact ⟨Finset.mem_insert_of_mem a1, Finset.mem_insert_of_mem a2⟩

def bnd (n k t : ℕ) : ℕ := t * (n / k) + min t (n % k)

theorem bnd_zero (n k : ℕ) : bnd n k 0 = 0 := by simp [bnd]

theorem bnd_k {n k : ℕ} (hk : 0 < k) : bnd n k k = n := by
  have h1 : n % k < k := Nat.mod_lt _ hk
  have h2 : min k (n % k) = n % k := min_eq_right h1.le
  have h3 := Nat.div_add_mod n k
  unfold bnd; rw [h2]; exact h3

theorem bnd_succ (n k t : ℕ) :
    bnd n k (t + 1) = bnd n k t + n / k + (if t < n % k then 1 else 0) := by
  unfold bnd
  rw [Nat.succ_mul]
  split_ifs with h <;> omega

theorem bnd_mono (n k : ℕ) : Monotone (bnd n k) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [bnd_succ]
  exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)

theorem ceil_div (n k : ℕ) (hk : 0 < k) :
    (n + k - 1) / k = n / k + (if n % k = 0 then 0 else 1) := by
  have h := Nat.div_add_mod n k
  have hr : n % k < k := Nat.mod_lt _ hk
  generalize n / k = q at *
  generalize n % k = m at *
  have e : n + k - 1 = (m + k - 1) + k * q := by omega
  rw [e, Nat.add_mul_div_left _ _ hk]
  by_cases hm : m = 0
  · subst hm
    have h0 : (0 + k - 1) / k = 0 := Nat.div_eq_of_lt (by omega)
    rw [h0]; simp
  · simp only [hm, ite_false]
    have : (m + k - 1) / k = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    omega

theorem len_le {n k : ℕ} (hk : 0 < k) (t : ℕ) :
    bnd n k (t + 1) - bnd n k t ≤ (n + k - 1) / k := by
  rw [bnd_succ, ceil_div n k hk]
  generalize n / k = q
  by_cases h : t < n % k
  · have hne : n % k ≠ 0 := by omega
    rw [if_pos h, if_neg hne]; omega
  · rw [if_neg h]; split_ifs <;> omega

theorem len_pos {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) (t : ℕ) :
    1 ≤ bnd n k (t + 1) - bnd n k t := by
  rw [bnd_succ]
  have : 1 ≤ n / k := Nat.div_pos hkn hk
  omega

theorem len_lt {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (t : ℕ) :
    bnd n k (t + 1) - bnd n k t < n := by
  rw [bnd_succ]
  have hk0 : 0 < k := by omega
  have h1 : 1 ≤ n / k := Nat.div_pos hkn hk0
  have h2 := Nat.div_add_mod n k
  have h3 : 2 * (n / k) ≤ k * (n / k) := Nat.mul_le_mul_right _ hk
  have h4 : n % k < k := Nat.mod_lt _ hk0
  generalize n / k = q at *
  generalize n % k = m at *
  split_ifs with h <;> omega

theorem exact_bnd {k h : ℕ} (hk : 0 < k) :
    (k * 2 ^ h) / k = 2 ^ h ∧ (k * 2 ^ h) % k = 0 :=
  ⟨Nat.mul_div_cancel_left _ hk, Nat.mul_mod_right _ _⟩

variable {n : ℕ}

def fe (f : Fin n → Bool) (i : ℕ) : Bool := if h : i < n then f ⟨i, h⟩ else false

def G (f : Fin n → Bool) : ℕ → Bool
  | 0 => false
  | i + 1 => G f i ^^ fe f i

theorem G_eq (f : Fin n → Bool) :
    ∀ i, G f i = decide (Odd ((Finset.range i).filter (fun j => fe f j = true)).card) := by
  intro i
  induction i with
  | zero => simp [G]
  | succ i ih =>
    have hnot : i ∉ (Finset.range i).filter (fun j => fe f j = true) := by simp
    rw [G, ih, Finset.range_add_one, Finset.filter_insert]
    cases hf : fe f i
    · simp [hf]
    · simp only [hf, ite_true, Finset.card_insert_of_notMem hnot, Bool.xor_true]
      generalize ((Finset.range i).filter (fun j => fe f j = true)).card = c
      by_cases h : Odd c <;> simp [h, Nat.odd_add_one]

theorem G_n (f : Fin n → Bool) (hodd : Odd ((Finset.univ.filter (fun i => f i = true)).card)) :
    G f n = true := by
  rw [G_eq]
  have : (Finset.range n).filter (fun j => fe f j = true) =
      (Finset.univ.filter (fun i => f i = true)).map Fin.valEmbedding := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply]
    constructor
    · rintro ⟨hi, hf⟩
      exact ⟨⟨i, hi⟩, by simpa [fe, hi] using hf, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j.2, by simpa [fe, j.2] using hj⟩
  rw [this, Finset.card_map]
  simp [hodd]

variable (hn : 0 < n)

def vtx (i : ℕ) : Fin n := ⟨i % n, Nat.mod_lt _ hn⟩

theorem vtx_of_lt {i : ℕ} (h : i < n) : vtx hn i = ⟨i, h⟩ := by
  simp [vtx, Nat.mod_eq_of_lt h]

theorem vtx_n : vtx hn n = ⟨0, hn⟩ := by simp [vtx]

theorem vtx_inj {l r j j' : ℕ} (hlen : r - l < n) (h1 : l ≤ j) (h2 : j ≤ r) (h3 : l ≤ j')
    (h4 : j' ≤ r) (h : vtx hn j = vtx hn j') : j = j' := by
  have h' : j % n = j' % n := congrArg Fin.val h
  rcases le_total j j' with hle | hle
  · have := Nat.sub_mod_eq_zero_of_mod_eq h'.symm
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega
  · have := Nat.sub_mod_eq_zero_of_mod_eq h'
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega

def cell (f : Fin n → Bool) (l r e : ℕ) (a : Bool) : Finset (Fin n × Bool) :=
  (P l r e).image (fun i => (vtx hn i, step a e i ^^ G f i))

def wd (f : Fin n → Bool) (x : Fin n → Bool) (i : ℕ) : Bool := x (vtx hn i) ^^ G f i

theorem xor_aux : ∀ u s g : Bool, (¬ (u ≠ (s ^^ g))) ↔ ((u ^^ g) = s) := by decide

theorem match_cell (f : Fin n → Bool) (x : Fin n → Bool) (l r e : ℕ) (a : Bool) :
    (cell hn f l r e a).filter (fun p => x p.1 ≠ p.2) = ∅ ↔
      ∀ i ∈ P l r e, wd hn f x i = step a e i := by
  rw [Finset.filter_eq_empty_iff]
  constructor
  · intro h i hi
    have := h (Finset.mem_image_of_mem _ hi)
    exact (xor_aux _ _ _).mp this
  · intro h q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact (xor_aux _ _ _).mpr (h i hi)

theorem cell_card_le (f : Fin n → Bool) {l r : ℕ} (e : ℕ) (a : Bool) (hlr : l < r) :
    (cell hn f l r e a).card ≤ 2 + Nat.clog 2 (r - l) :=
  (Finset.card_image_le).trans (P_card_le _ l r e rfl hlr)

theorem cell_card_pow (f : Fin n → Bool) (h l e : ℕ) (a : Bool) (hl : l ≤ e) (he : e < l + 2 ^ h)
    (hlen : 2 ^ h < n) : (cell hn f l (l + 2 ^ h) e a).card = 2 + h := by
  unfold cell
  rw [Finset.card_image_of_injOn, P_card_pow h l e hl he]
  intro i hi j hj hij
  have hi' := P_sub _ l (l + 2 ^ h) e rfl (by omega) i hi
  have hj' := P_sub _ l (l + 2 ^ h) e rfl (by omega) j hj
  have := congrArg Prod.fst hij
  exact vtx_inj hn (by omega) hi'.1 hi'.2 hj'.1 hj'.2 this

theorem cell_valid (f : Fin n → Bool) {l r : ℕ} (e : ℕ) (a : Bool) (hlr : l < r) (h1 : l ≤ e)
    (h2 : e < r) (hlen : r - l < n) (hr : r ≤ n) :
    (∀ i : Fin n, ¬ ((i, false) ∈ cell hn f l r e a ∧ (i, true) ∈ cell hn f l r e a)) ∧
    ∃ (i : Fin n) (b : Bool), (i, b) ∈ cell hn f l r e a ∧
      ((⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n), !(b ^^ f i)) ∈ cell hn f l r e a := by
  constructor
  · rintro i ⟨h1', h2'⟩
    obtain ⟨j, hj, hj1⟩ := Finset.mem_image.mp h1'
    obtain ⟨j', hj', hj2⟩ := Finset.mem_image.mp h2'
    have hj0 := P_sub _ l r e rfl hlr.le j hj
    have hj0' := P_sub _ l r e rfl hlr.le j' hj'
    have hv : vtx hn j = vtx hn j' := by
      have := congrArg Prod.fst hj1
      have := congrArg Prod.fst hj2
      simp_all
    have := vtx_inj hn hlen hj0.1 hj0.2 hj0'.1 hj0'.2 hv
    subst this
    have a1 := congrArg Prod.snd hj1
    have a2 := congrArg Prod.snd hj2
    dsimp only at a1 a2
    rw [a1] at a2
    exact Bool.false_ne_true a2
  · have he : e < n := by omega
    refine ⟨⟨e, he⟩, a ^^ G f e, ?_, ?_⟩
    · obtain ⟨m1, _⟩ := leaf_mem _ l r e rfl h1 h2
      refine Finset.mem_image.mpr ⟨e, m1, ?_⟩
      simp [vtx_of_lt hn he, step]
    · obtain ⟨_, m2⟩ := leaf_mem _ l r e rfl h1 h2
      refine Finset.mem_image.mpr ⟨e + 1, m2, ?_⟩
      have hfe : fe f e = f ⟨e, he⟩ := by simp [fe, he]
      have hG : G f (e + 1) = (G f e ^^ f ⟨e, he⟩) := by rw [G, hfe]
      have hv : vtx hn (e + 1) = ⟨(e + 1) % n, Nat.mod_lt _ hn⟩ := rfl
      rw [Prod.ext_iff]
      refine ⟨hv, ?_⟩
      simp only [step, hG]
      cases a <;> cases G f e <;> cases f ⟨e, he⟩ <;> simp

section Load
variable {n : ℕ} (hn : 0 < n) (f : Fin n → Bool) (k : ℕ)

def Ix (n k : ℕ) : Finset (Σ _ : ℕ, ℕ × Bool) :=
  (Finset.range k).sigma (fun t => (Finset.Ico (bnd n k t) (bnd n k (t + 1))) ×ˢ
    (Finset.univ : Finset Bool))

def Fc (s : Σ _ : ℕ, ℕ × Bool) : Finset (Fin n × Bool) :=
  cell hn f (bnd n k s.1) (bnd n k (s.1 + 1)) s.2.1 s.2.2

theorem mem_Ix {t e : ℕ} {a : Bool} :
    (⟨t, (e, a)⟩ : Σ _ : ℕ, ℕ × Bool) ∈ Ix n k ↔
      t < k ∧ bnd n k t ≤ e ∧ e < bnd n k (t + 1) := by
  simp [Ix]

def stw (e : ℕ) (a : Bool) : Fin n → Bool := fun v => step a e v.val ^^ G f v.val

theorem wd_stw (hG : G f n = true) {e : ℕ} (he : e < n) (a : Bool) {i : ℕ} (hi : i ≤ n) :
    wd hn f (stw f e a) i = step a e i := by
  by_cases h : i < n
  · simp only [wd, stw, vtx_of_lt hn h]
    cases step a e i <;> cases G f i <;> rfl
  · have : i = n := by omega
    subst this
    simp only [wd, stw, vtx_n, hG]
    have h0 : G f 0 = false := rfl
    simp only [h0, step]
    simp [show 0 ≤ e by omega, show ¬ i ≤ e by omega]

theorem step_cases {a a' : Bool} {e l r : ℕ} (hlr : l < r) (e1 : step a e l = a')
    (e2 : step a e r = !a') : a = a' ∧ l ≤ e ∧ e < r := by
  unfold step at e1 e2
  by_cases hl : l ≤ e <;> by_cases hr : r ≤ e
  · exfalso
    simp only [hl, hr, ite_true] at e1 e2
    subst e1
    cases a <;> simp at e2
  · simp only [hl, hr, ite_true, ite_false] at e1 e2
    exact ⟨e1, hl, by omega⟩
  · exfalso; omega
  · exfalso
    simp only [hl, hr, ite_false] at e1 e2
    subst e1
    cases a <;> simp at e2

theorem Fc_injOn (hk : 0 < k) (hkn : k ≤ n) (hG : G f n = true) :
    Set.InjOn (Fc hn f k) (Ix n k : Set (Σ _ : ℕ, ℕ × Bool)) := by
  rintro ⟨t, e, a⟩ hs ⟨t', e', a'⟩ hs' hF
  simp only [Finset.mem_coe, mem_Ix] at hs hs'
  obtain ⟨ht, h1, h2⟩ := hs
  obtain ⟨ht', h1', h2'⟩ := hs'
  have hbn : ∀ s, s ≤ k → bnd n k s ≤ n := fun s hs => (bnd_mono n k hs).trans (bnd_k hk).le
  have en : e < n := lt_of_lt_of_le h2 (hbn _ ht)
  have hF' : Fc hn f k ⟨t', (e', a')⟩ = Fc hn f k ⟨t, (e, a)⟩ := hF.symm
  have hmatch : ∀ i ∈ P (bnd n k t) (bnd n k (t + 1)) e, wd hn f (stw f e a) i = step a e i := by
    intro i hi
    have := P_sub _ _ _ e rfl (bnd_mono n k (Nat.le_succ t)) i hi
    exact wd_stw hn f hG en a (this.2.trans (hbn _ ht))
  have hm1 : (Fc hn f k ⟨t, (e, a)⟩).filter (fun p => stw f e a p.1 ≠ p.2) = ∅ :=
    (match_cell hn f (stw f e a) _ _ e a).mpr hmatch
  rw [← hF'] at hm1
  have hm2 : ∀ i ∈ P (bnd n k t') (bnd n k (t' + 1)) e', wd hn f (stw f e a) i = step a' e' i :=
    (match_cell hn f (stw f e a) _ _ e' a').mp hm1
  have hlr' : bnd n k t' < bnd n k (t' + 1) := by
    have := len_pos (n := n) hk hkn t'
    omega
  obtain ⟨hla, hra⟩ := P_ends (wd hn f (stw f e a)) a' hlr' h1' h2' hm2
  have hl' : bnd n k t' ≤ n := hbn _ (by omega)
  have hr' : bnd n k (t' + 1) ≤ n := hbn _ (by omega)
  rw [wd_stw hn f hG en a hl'] at hla
  rw [wd_stw hn f hG en a hr'] at hra
  obtain ⟨haa, hle, hlt⟩ := step_cases hlr' hla hra
  subst haa
  have htt : t = t' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt' | hgt
    · have := bnd_mono n k (show t + 1 ≤ t' by omega)
      omega
    · have := bnd_mono n k (show t' + 1 ≤ t by omega)
      omega
  subst t'
  have hlr : bnd n k t < bnd n k (t + 1) := hlr'
  have hee := P_uniq (wd hn f (stw f e a)) a _ _ _ e e' rfl hlr h1 h2 h1' h2' hmatch hm2
  subst hee
  rfl

theorem arc_count (hkn : k ≤ n) (hk : 0 < k) (x : Fin n → Bool) {t : ℕ} (ht : t < k) :
    (((Finset.Ico (bnd n k t) (bnd n k (t + 1))) ×ˢ (Finset.univ : Finset Bool)).filter
      (fun q => (cell hn f (bnd n k t) (bnd n k (t + 1)) q.1 q.2).filter
        (fun p => x p.1 ≠ p.2) = ∅)).card =
      if wd hn f x (bnd n k t) ≠ wd hn f x (bnd n k (t + 1)) then 1 else 0 := by
  have hlr : bnd n k t < bnd n k (t + 1) := by
    have := len_pos (n := n) hk hkn t
    omega
  set p := wd hn f x with hp
  by_cases hne : p (bnd n k t) ≠ p (bnd n k (t + 1))
  · rw [if_pos hne]
    have hr : p (bnd n k (t + 1)) = !p (bnd n k t) := by
      cases h1 : p (bnd n k t) <;> cases h2 : p (bnd n k (t + 1)) <;> simp_all
    obtain ⟨e0, h1, h2, h3⟩ := P_exists p (p (bnd n k t)) _ (bnd n k t) (bnd n k (t + 1)) rfl hlr rfl hr
    rw [Finset.card_eq_one]
    refine ⟨(e0, p (bnd n k t)), ?_⟩
    ext ⟨e, a⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico, Finset.mem_univ, and_true,
      Finset.mem_singleton, Prod.mk.injEq]
    rw [match_cell]
    constructor
    · rintro ⟨⟨he1, he2⟩, hm⟩
      obtain ⟨ha, _⟩ := P_ends p a hlr he1 he2 hm
      subst ha
      exact ⟨P_uniq p _ _ (bnd n k t) (bnd n k (t + 1)) e e0 rfl hlr he1 he2 h1 h2 hm h3, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  · rw [if_neg hne, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨e, a⟩ hq hm
    simp only [Finset.mem_product, Finset.mem_Ico, Finset.mem_univ, and_true] at hq
    rw [match_cell] at hm
    obtain ⟨ha, hb⟩ := P_ends p a hlr hq.1 hq.2 hm
    apply hne
    rw [ha, hb]
    cases a <;> simp

theorem card_Ix (hk : 0 < k) (hkn : k ≤ n) : (Ix n k).card = 2 * n := by
  unfold Ix
  rw [Finset.card_sigma]
  have : ∀ t ∈ Finset.range k,
      ((Finset.Ico (bnd n k t) (bnd n k (t + 1))) ×ˢ (Finset.univ : Finset Bool)).card =
        2 * (bnd n k (t + 1) - bnd n k t) := by
    intro t _
    rw [Finset.card_product, Nat.card_Ico, Finset.card_univ, Fintype.card_bool]
    ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, Finset.sum_range_tsub (bnd_mono n k), bnd_k hk,
    bnd_zero]
  simp

theorem load_eq (hk : 0 < k) (hkn : k ≤ n) (hG : G f n = true) (x : Fin n → Bool) :
    (((Ix n k).image (Fc hn f k)).filter
      (fun C => C.filter (fun p => x p.1 ≠ p.2) = ∅)).card =
      ∑ t ∈ Finset.range k,
        if wd hn f x (bnd n k t) ≠ wd hn f x (bnd n k (t + 1)) then 1 else 0 := by
  rw [Finset.filter_image, Finset.card_image_of_injOn]
  · rw [Finset.card_filter]
    unfold Ix
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro t ht
    rw [← Finset.card_filter]
    exact arc_count hn f k hkn hk x (Finset.mem_range.mp ht)
  · exact (Fc_injOn hn f k hk hkn hG).mono (by
      intro s hs
      exact (Finset.mem_filter.mp (Finset.mem_coe.mp hs)).1)

end Load

section Count

def chg {m : ℕ} (z : Fin (m + 1) → Bool) : ℕ :=
  ∑ t : Fin m, if z t.castSucc ≠ z t.succ then 1 else 0

theorem chg_cons {m : ℕ} (u : Bool) (z : Fin (m + 1) → Bool) :
    chg (Fin.cons u z : Fin (m + 2) → Bool) = (if u ≠ z 0 then 1 else 0) + chg z := by
  unfold chg
  rw [Fin.sum_univ_succ]
  simp

theorem bool_aux1 : ∀ u v o : Bool, (v = (!u ^^ o)) ↔ (v = (u ^^ !o)) := by decide

theorem path_count : ∀ (m : ℕ) (u : Bool) (i : ℕ) (v : Bool),
    (Finset.univ.filter (fun z : Fin (m + 1) → Bool =>
      z 0 = u ∧ chg z = i ∧ z (Fin.last m) = v)).card =
      if v = (u ^^ decide (Odd i)) then m.choose i else 0 := by
  intro m
  induction m with
  | zero =>
    intro u i v
    cases i with
    | zero => cases u <;> cases v <;> decide
    | succ i =>
      have hR : (if v = (u ^^ decide (Odd (i + 1))) then Nat.choose 0 (i + 1) else 0) = 0 := by
        simp
      rw [hR, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro z - ⟨_, h2, _⟩
      simp [chg] at h2
  | succ m ih =>
    intro u i v
    have hset : (Finset.univ.filter (fun z : Fin (m + 2) → Bool =>
        z 0 = u ∧ chg z = i ∧ z (Fin.last (m + 1)) = v)) =
        (Finset.univ.filter (fun z' : Fin (m + 1) → Bool =>
          (if u ≠ z' 0 then 1 else 0) + chg z' = i ∧ z' (Fin.last m) = v)).image (Fin.cons u) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨h0, h1, h2⟩
        refine ⟨Fin.tail z, ?_, ?_⟩
        · have hz : z = Fin.cons u (Fin.tail z) := by
            rw [← h0]; exact (Fin.cons_self_tail z).symm
          rw [hz, chg_cons] at h1
          refine ⟨by simpa [Fin.tail] using h1, ?_⟩
          have := h2
          rw [hz] at this
          simpa [Fin.tail, ← Fin.succ_last] using this
        · rw [← h0]; exact Fin.cons_self_tail z
      · rintro ⟨z', ⟨h1, h2⟩, rfl⟩
        refine ⟨by simp, ?_, ?_⟩
        · rw [chg_cons]; exact h1
        · simpa [← Fin.succ_last] using h2
    rw [hset, Finset.card_image_of_injective _ (fun z1 z2 h => by simpa using congrArg Fin.tail h)]
    have hsplit : (Finset.univ.filter (fun z' : Fin (m + 1) → Bool =>
          (if u ≠ z' 0 then 1 else 0) + chg z' = i ∧ z' (Fin.last m) = v)) =
        (Finset.univ.filter (fun z' : Fin (m + 1) → Bool =>
          z' 0 = u ∧ chg z' = i ∧ z' (Fin.last m) = v)) ∪
        (Finset.univ.filter (fun z' : Fin (m + 1) → Bool =>
          z' 0 = !u ∧ chg z' + 1 = i ∧ z' (Fin.last m) = v)) := by
      ext z'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      by_cases h0 : z' 0 = u
      · have : z' 0 ≠ !u := by rw [h0]; cases u <;> simp
        simp [h0, this]
      · have h0' : z' 0 = !u := by cases u <;> cases hz : z' 0 <;> simp_all
        simp [h0, h0']
        omega
    have hdis : Disjoint (Finset.univ.filter (fun z' : Fin (m + 1) → Bool =>
          z' 0 = u ∧ chg z' = i ∧ z' (Fin.last m) = v))
        (Finset.univ.filter (fun z' : Fin (m + 1) → Bool =>
          z' 0 = !u ∧ chg z' + 1 = i ∧ z' (Fin.last m) = v)) := by
      rw [Finset.disjoint_filter]
      rintro z' - ⟨h0, _⟩ ⟨h0', _⟩
      rw [h0] at h0'
      cases u <;> simp at h0'
    rw [hsplit, Finset.card_union_of_disjoint hdis, ih]
    cases i with
    | zero =>
      have : (Finset.univ.filter (fun z' : Fin (m + 1) → Bool =>
          z' 0 = !u ∧ chg z' + 1 = 0 ∧ z' (Fin.last m) = v)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        rintro z' - ⟨_, h, _⟩
        omega
      rw [this]
      simp
    | succ i =>
      have hB : (Finset.univ.filter (fun z' : Fin (m + 1) → Bool =>
          z' 0 = !u ∧ chg z' + 1 = i + 1 ∧ z' (Fin.last m) = v)) =
          (Finset.univ.filter (fun z' : Fin (m + 1) → Bool =>
          z' 0 = !u ∧ chg z' = i ∧ z' (Fin.last m) = v)) := by
        apply Finset.filter_congr
        intro z' _
        simp
      rw [hB, ih]
      have h1 : decide (Odd (i + 1)) = !decide (Odd i) := by
        simp only [Nat.odd_add_one, decide_not]
      rw [h1]
      by_cases hc : v = (u ^^ !decide (Odd i))
      · have hc' : v = (!u ^^ decide (Odd i)) := (bool_aux1 u v _).mpr hc
        rw [if_pos hc, if_pos hc', if_pos hc, Nat.choose_succ_succ]
        have e : m.choose i.succ = m.choose (i + 1) := rfl
        omega
      · have hc' : ¬ v = (!u ^^ decide (Odd i)) := fun h => hc ((bool_aux1 u v _).mp h)
        rw [if_neg hc, if_neg hc', if_neg hc]

end Count

end PEqualNP.Outside.L_pcx_255_aux

namespace PEqualNP.Outside.L_pcx_255_aux

section Lam
variable {k : ℕ} (hk : 0 < k)

def ext' (y : Fin k → Bool) (s : ℕ) : Bool := if h : s < k then y ⟨s, h⟩ else !y ⟨0, hk⟩

def Lam (y : Fin k → Bool) : ℕ :=
  ∑ t ∈ Finset.range k, if ext' hk y t ≠ ext' hk y (t + 1) then 1 else 0

def zOf (y : Fin k → Bool) : Fin (k + 1) → Bool := fun s => ext' hk y s.val

theorem chg_zOf (y : Fin k → Bool) : chg (zOf hk y) = Lam hk y := by
  unfold chg Lam zOf
  simp only [Fin.coe_castSucc, Fin.val_succ]
  exact Fin.sum_univ_eq_sum_range (fun t => if ext' hk y t ≠ ext' hk y (t + 1) then 1 else 0) k

theorem card_Lam (j : ℕ) :
    (Finset.univ.filter (fun y : Fin k → Bool => Lam hk y = j)).card =
      if Odd j then 2 * k.choose j else 0 := by
  have h1 : (Finset.univ.filter (fun y : Fin k → Bool => Lam hk y = j)).card =
      (Finset.univ.filter (fun z : Fin (k + 1) → Bool =>
        z (Fin.last k) = !z 0 ∧ chg z = j)).card := by
    apply Finset.card_bij (fun y _ => zOf hk y)
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      refine ⟨?_, by rw [chg_zOf, hy]⟩
      simp [zOf, ext', hk]
    · intro y1 _ y2 _ h
      funext t
      have := congrFun h t.castSucc
      simpa [zOf, ext'] using this
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      have hzy : zOf hk (fun t => z t.castSucc) = z := by
        funext s
        by_cases hs : s.val < k
        · simp only [zOf, ext', hs, dif_pos]
          congr 1
        · have hs' : s = Fin.last k := by
            apply Fin.ext; simp; omega
          subst hs'
          simp only [zOf, ext', Fin.val_last, lt_irrefl, dif_neg, not_false_eq_true]
          rw [hz.1]
          congr 2
      refine ⟨fun t => z t.castSucc, ?_, hzy⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← chg_zOf, hzy]
      exact hz.2
  have h2 : (Finset.univ.filter (fun z : Fin (k + 1) → Bool =>
        z (Fin.last k) = !z 0 ∧ chg z = j)).card =
      ∑ u : Bool, (Finset.univ.filter (fun z : Fin (k + 1) → Bool =>
        z 0 = u ∧ chg z = j ∧ z (Fin.last k) = !u)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun z : Fin (k + 1) → Bool => z 0)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.filter_filter]
    apply congrArg
    apply Finset.filter_congr
    intro z _
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      subst h3
      exact ⟨rfl, h2, h1⟩
    · rintro ⟨h3, h2, h1⟩
      subst h3
      exact ⟨⟨h1, h2⟩, rfl⟩
  rw [h1, h2]
  simp only [path_count]
  rw [Fintype.sum_bool]
  by_cases hj : Odd j <;> simp [hj, two_mul]

end Lam

theorem card_restrict {n k : ℕ} (b : Fin k → Fin n) (hb : Function.Injective b)
    (R : (Fin k → Bool) → Prop) [DecidablePred R] :
    (Finset.univ.filter (fun w : Fin n → Bool => R (fun t => w (b t)))).card
      = 2 ^ (n - k) * (Finset.univ.filter R).card := by
  classical
  let p : Fin n → Prop := fun v => v ∈ Set.range b
  let E := Equiv.piEquivPiSubtypeProd p (fun _ : Fin n => Bool)
  let e : Fin k ≃ {v // p v} := Equiv.ofInjective b hb
  rw [Finset.card_filter, Finset.card_filter, ← Equiv.sum_comp E.symm, Fintype.sum_prod_type]
  have hE : ∀ (u : {v // p v} → Bool) (u' : {v // ¬ p v} → Bool) (t : Fin k),
      (E.symm (u, u')) (b t) = u (e t) := by
    intro u u' t
    have hp : p (b t) := ⟨t, rfl⟩
    simp only [E, Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos hp]
    rfl
  simp_rw [hE]
  have hcard : Fintype.card {v // ¬ p v} = n - k := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
    have : Fintype.card {v // p v} = k := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
    rw [this]
  have h1 : ∀ u : {v // p v} → Bool, (∑ _u' : {v // ¬ p v} → Bool,
      if R (fun t => u (e t)) then 1 else 0) = 2 ^ (n - k) * (if R (fun t => u (e t)) then 1 else 0) := by
    intro u
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, hcard, Fintype.card_bool]
    simp
  simp_rw [h1]
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl Bool))
    (fun u => if R (fun t => u (e t)) then 1 else 0) (fun y => if R y then 1 else 0)
    (fun u => by
      have : (Equiv.arrowCongr e.symm (Equiv.refl Bool)) u = fun t => u (e t) := by
        funext t; simp [Equiv.arrowCongr]
      rw [this])

end PEqualNP.Outside.L_pcx_255_aux

namespace PEqualNP.Outside.L_pcx_255_aux

section Words
variable {n : ℕ} (hn : 0 < n) (f : Fin n → Bool)

def psi (x : Fin n → Bool) : Fin n → Bool := fun v => x v ^^ G f v.val

theorem psi_psi (x : Fin n → Bool) : psi f (psi f x) = x := by
  funext v
  simp only [psi]
  cases x v <;> cases G f v.val <;> rfl

def wext (w : Fin n → Bool) (i : ℕ) : Bool := if h : i < n then w ⟨i, h⟩ else !w ⟨0, hn⟩

theorem wd_psi (hG : G f n = true) (x : Fin n → Bool) {i : ℕ} (hi : i ≤ n) :
    wd hn f x i = wext hn (psi f x) i := by
  by_cases h : i < n
  · simp only [wd, wext, psi, vtx_of_lt hn h, dif_pos h]
  · have : i = n := by omega
    subst this
    have h0 : G f 0 = false := rfl
    simp only [wd, wext, psi, vtx_n, hG, dif_neg h, h0]
    cases x ⟨0, hn⟩ <;> rfl

variable (k : ℕ)

theorem bnd_lt (hk : 0 < k) (hkn : k ≤ n) {t : ℕ} (ht : t < k) : bnd n k t < n := by
  have h1 := len_pos (n := n) hk hkn t
  have h2 : bnd n k (t + 1) ≤ n := (bnd_mono n k ht).trans (bnd_k hk).le
  omega

def bfun (hk : 0 < k) (hkn : k ≤ n) (t : Fin k) : Fin n := ⟨bnd n k t.val, bnd_lt k hk hkn t.2⟩

theorem bfun_inj (hk : 0 < k) (hkn : k ≤ n) : Function.Injective (bfun k hk hkn) := by
  intro s t h
  have h' : bnd n k s.val = bnd n k t.val := congrArg Fin.val h
  by_contra hne
  have hne' : s.val ≠ t.val := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne' with hlt | hgt
  · have := bnd_mono n k (show s.val + 1 ≤ t.val by omega)
    have := len_pos (n := n) hk hkn s.val
    omega
  · have := bnd_mono n k (show t.val + 1 ≤ s.val by omega)
    have := len_pos (n := n) hk hkn t.val
    omega

theorem wext_bnd (hk : 0 < k) (hkn : k ≤ n) (w : Fin n → Bool) {t : ℕ} (ht : t ≤ k) :
    wext hn w (bnd n k t) = ext' hk (fun s => w (bfun k hk hkn s)) t := by
  by_cases h : t < k
  · simp only [wext, ext', dif_pos (bnd_lt k hk hkn h), dif_pos h, bfun]
  · have : t = k := by omega
    subst this
    simp [wext, ext', bnd_k hk, bfun, bnd_zero]

theorem load_Lam (hk : 0 < k) (hkn : k ≤ n) (hG : G f n = true) (x : Fin n → Bool) :
    (∑ t ∈ Finset.range k, if wd hn f x (bnd n k t) ≠ wd hn f x (bnd n k (t + 1)) then 1 else 0)
      = Lam hk (fun s => psi f x (bfun k hk hkn s)) := by
  unfold Lam
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_range.mp ht
  have hb1 : bnd n k t ≤ n := (bnd_mono n k ht'.le).trans (bnd_k hk).le
  have hb2 : bnd n k (t + 1) ≤ n := (bnd_mono n k ht').trans (bnd_k hk).le
  rw [wd_psi hn f hG x hb1, wd_psi hn f hG x hb2, wext_bnd hn k hk hkn _ ht'.le,
    wext_bnd hn k hk hkn _ ht']

theorem part1 (hk2 : 2 ≤ k) (hkn : k ≤ n) (hodd : Odd ((Finset.univ.filter (fun i => f i = true)).card)) :
    (((Ix n k).image (Fc hn f k)).card = 2 * n) := by
  have hk : 0 < k := by omega
  rw [Finset.card_image_of_injOn (Fc_injOn hn f k hk hkn (G_n f hodd)), card_Ix k hk hkn]

theorem part2 (hk2 : 2 ≤ k) (hkn : k ≤ n) (C : Finset (Fin n × Bool))
    (hC : C ∈ (Ix n k).image (Fc hn f k)) :
    ((∀ i : Fin n, ¬ ((i, false) ∈ C ∧ (i, true) ∈ C)) ∧
      ∃ (i : Fin n) (a : Bool), (i, a) ∈ C ∧
        ((⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n), !(a ^^ f i)) ∈ C) ∧
      C.card ≤ 2 + Nat.clog 2 ((n + k - 1) / k) := by
  have hk : 0 < k := by omega
  obtain ⟨⟨t, e, a⟩, hs, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨ht, h1, h2⟩ := (mem_Ix k).mp hs
  have hlr : bnd n k t < bnd n k (t + 1) := by
    have := len_pos (n := n) hk hkn t
    omega
  have hr : bnd n k (t + 1) ≤ n := (bnd_mono n k ht).trans (bnd_k hk).le
  refine ⟨cell_valid hn f e a hlr h1 h2 (len_lt hk2 hkn t) hr, ?_⟩
  have := cell_card_le hn f e a hlr
  have h3 := Nat.clog_mono_right 2 (len_le (n := n) hk t)
  change (cell hn f (bnd n k t) (bnd n k (t + 1)) e a).card ≤ _
  omega

theorem part3 (hk2 : 2 ≤ k) (hkn : k ≤ n)
    (hnk : n = k * 2 ^ Nat.clog 2 ((n + k - 1) / k)) (C : Finset (Fin n × Bool))
    (hC : C ∈ (Ix n k).image (Fc hn f k)) : C.card = 2 + Nat.clog 2 ((n + k - 1) / k) := by
  have hk : 0 < k := by omega
  generalize Nat.clog 2 ((n + k - 1) / k) = H at hnk ⊢
  obtain ⟨⟨t, e, a⟩, hs, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨ht, h1, h2⟩ := (mem_Ix k).mp hs
  have e1 : n / k = 2 ^ H := by
    rw [hnk]; exact Nat.mul_div_cancel_left _ hk
  have e2 : n % k = 0 := by
    rw [hnk]; exact Nat.mul_mod_right _ _
  have hr : bnd n k (t + 1) = bnd n k t + 2 ^ H := by
    rw [bnd_succ, e1, e2]; simp
  have hP : 0 < 2 ^ H := by positivity
  have h3 : 2 * 2 ^ H ≤ k * 2 ^ H := Nat.mul_le_mul_right _ hk2
  have hlt : 2 ^ H < n := by omega
  change (cell hn f (bnd n k t) (bnd n k (t + 1)) e a).card = 2 + H
  rw [hr] at h2 ⊢
  exact cell_card_pow hn f H _ e a h1 h2 hlt

theorem part4 (hk2 : 2 ≤ k) (hkn : k ≤ n)
    (hodd : Odd ((Finset.univ.filter (fun i => f i = true)).card)) (j : ℕ) :
    (Finset.univ.filter (fun x : Fin n → Bool =>
      (((Ix n k).image (Fc hn f k)).filter
        (fun C => C.filter (fun p => x p.1 ≠ p.2) = ∅)).card = j)).card =
      if Odd j then k.choose j * 2 ^ (n - k + 1) else 0 := by
  have hk : 0 < k := by omega
  have hG := G_n f hodd
  have step1 : ∀ x : Fin n → Bool, (((Ix n k).image (Fc hn f k)).filter
        (fun C => C.filter (fun p => x p.1 ≠ p.2) = ∅)).card =
      Lam hk (fun s => psi f x (bfun k hk hkn s)) := by
    intro x
    rw [load_eq hn f k hk hkn hG x, load_Lam hn f k hk hkn hG x]
  simp_rw [step1]
  have step2 : (Finset.univ.filter (fun x : Fin n → Bool =>
      Lam hk (fun s => psi f x (bfun k hk hkn s)) = j)).card =
      (Finset.univ.filter (fun w : Fin n → Bool => Lam hk (fun s => w (bfun k hk hkn s)) = j)).card := by
    apply Finset.card_bij (fun x _ => psi f x)
    · intro x hx
      simpa using hx
    · intro x _ y _ h
      simpa [psi_psi] using congrArg (psi f) h
    · intro w hw
      refine ⟨psi f w, ?_, psi_psi f w⟩
      simpa [psi_psi] using hw
  rw [step2]
  have step3 := card_restrict (bfun k hk hkn) (bfun_inj k hk hkn) (fun y => Lam hk y = j)
  rw [step3, card_Lam hk j]
  split_ifs
  · rw [pow_succ]; ring
  · simp

end Words

end PEqualNP.Outside.L_pcx_255_aux

theorem PEqualNP.Outside.L_pcx_255 : (∀ (n : ℕ) (hn : 0 < n), 2 ≤ n → ∀ f : Fin n → Bool,
  Odd ((Finset.univ.filter (fun i => f i = true)).card) →
  let Cell := Finset (Fin n × Bool)
  let next := fun i : Fin n => (⟨(i.val+1) % n, Nat.mod_lt _ hn⟩ : Fin n)
  let valid := fun C : Cell =>
    (∀ i : Fin n, ¬ ((i, false) ∈ C ∧ (i, true) ∈ C)) ∧
    ∃ (i : Fin n) (a : Bool), (i, a) ∈ C ∧ (next i, !(a ^^ f i)) ∈ C
  let load := fun (L : Finset Cell) (x : Fin n → Bool) =>
    (L.filter (fun C => (C.filter (fun p => x p.1 ≠ p.2)) = ∅)).card
  ∀ k : ℕ, 2 ≤ k → k ≤ n →
    let h := Nat.clog 2 ((n+k-1)/k)
    ∃ L : Finset Cell, L.card = 2*n ∧
      (∀ C ∈ L, valid C ∧ C.card ≤ 2+h) ∧
      (n = k*2^h → ∀ C ∈ L, C.card = 2+h) ∧
      ∀ j : ℕ, (Finset.univ.filter (fun x : Fin n → Bool => load L x = j)).card =
        if Odd j then k.choose j * 2^(n-k+1) else 0) := by
  intro n hn h2 f hodd Cell next valid load k hk2 hkn h
  refine ⟨(PEqualNP.Outside.L_pcx_255_aux.Ix n k).image (PEqualNP.Outside.L_pcx_255_aux.Fc hn f k),
    PEqualNP.Outside.L_pcx_255_aux.part1 hn f k hk2 hkn hodd, ?_, ?_, ?_⟩
  · intro C hC
    exact PEqualNP.Outside.L_pcx_255_aux.part2 hn f k hk2 hkn C hC
  · intro hnk C hC
    exact PEqualNP.Outside.L_pcx_255_aux.part3 hn f k hk2 hkn hnk C hC
  · intro j
    exact PEqualNP.Outside.L_pcx_255_aux.part4 hn f k hk2 hkn hodd j
