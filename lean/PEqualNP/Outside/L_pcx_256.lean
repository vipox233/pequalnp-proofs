import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_256

def a_g {n : ℕ} (f : Fin n → Bool) (k : ℕ) : ℕ := if h : k < n then (if f ⟨k, h⟩ = true then 1 else 0) else 0

def a_u {n : ℕ} (f : Fin n → Bool) : ℕ → Bool
  | 0 => false
  | k+1 => a_u f k ^^ (if h : k < n then f ⟨k, h⟩ else false)

theorem a_u_zero {n : ℕ} (f : Fin n → Bool) : a_u f 0 = false := by
  simp [a_u]

theorem a_u_succ {n : ℕ} (f : Fin n → Bool) (k : ℕ) (h : k < n) : a_u f (k+1) = (a_u f k ^^ f ⟨k, h⟩) := by
  simp [a_u, h]

theorem a_u_odd {n : ℕ} (f : Fin n → Bool) (k : ℕ) : (a_u f k = true ↔ Odd (∑ m ∈ Finset.range k, a_g f m)) := by
  induction k with
  | zero => simp [a_u]
  | succ k ih =>
    rw [Finset.sum_range_succ]
    by_cases h : k < n
    · have e2 : a_g f k = if f ⟨k, h⟩ = true then 1 else 0 := by simp [a_g, h]
      rw [a_u_succ f k h, e2]
      cases hf : f ⟨k, h⟩
      · rw [show (if false = true then 1 else 0 : ℕ) = 0 from rfl, Nat.add_zero, Bool.xor_false]
        exact ih
      · rw [show (if true = true then 1 else 0 : ℕ) = 1 from rfl, Nat.odd_add_one, ← ih, Bool.xor_true]
        cases a_u f k <;> simp
    · have e1 : a_u f (k+1) = a_u f k := by simp [a_u, h]
      have e2 : a_g f k = 0 := by simp [a_g, h]
      rw [e1, e2, Nat.add_zero, ih]

theorem a_u_n {n : ℕ} (f : Fin n → Bool) (hodd : Odd ((Finset.univ.filter (fun i => f i = true)).card)) : a_u f n = true := by
  rw [a_u_odd]
  have e : (Finset.univ.filter (fun i => f i = true)).card = ∑ m ∈ Finset.range n, a_g f m := by
    rw [Finset.card_filter]
    rw [← Fin.sum_univ_eq_sum_range (fun m => a_g f m) n]
    apply Finset.sum_congr rfl
    intro m _
    simp [a_g, m.isLt]
  rw [← e]
  exact hodd

def a_w {n : ℕ} (f : Fin n → Bool) (i : Fin n) (a : Bool) (j : Fin n) : Bool :=
  ((a_u f j.val ^^ a_u f i.val) ^^ a) ^^ decide (i.val < j.val)

theorem a_w_self {n : ℕ} (f : Fin n → Bool) (i : Fin n) (a : Bool) : a_w f i a i = a := by
  simp [a_w]

theorem a_w_val {n : ℕ} (f : Fin n → Bool) (i : Fin n) (a : Bool) (j : Fin n) (k : ℕ) (hk : j.val = k) :
    a_w f i a j = (((a_u f k ^^ a_u f i.val) ^^ a) ^^ decide (i.val < k)) := by
  subst hk; rfl

theorem a_w_edge {n : ℕ} (hn : 0 < n) (f : Fin n → Bool)
    (hodd : Odd ((Finset.univ.filter (fun i => f i = true)).card)) (i : Fin n) (a : Bool) (j : Fin n) :
    a_w f i a ⟨(j.val+1) % n, Nat.mod_lt _ hn⟩ = ((a_w f i a j ^^ f j) ^^ decide (j = i)) := by
  by_cases hj : j.val + 1 < n
  · rw [a_w_val f i a _ (j.val+1) (Nat.mod_eq_of_lt hj), a_u_succ f j.val (by omega)]
    unfold a_w
    simp only [Fin.eta]
    by_cases hij : j = i
    · subst hij
      have h1 : decide (j.val < j.val + 1) = true := by simp
      have h2 : decide (j.val < j.val) = false := by simp
      rw [h1, h2, decide_eq_true (rfl : j = j)]
      generalize a_u f j.val = p
      generalize f j = r
      cases p <;> cases r <;> cases a <;> rfl
    · have hne : j.val ≠ i.val := fun h => hij (Fin.ext h)
      have h1 : decide (i.val < j.val + 1) = decide (i.val < j.val) := by
        simp only [decide_eq_decide]; omega
      rw [h1, decide_eq_false hij]
      generalize a_u f j.val = p
      generalize a_u f i.val = q
      generalize f j = r
      generalize decide (i.val < j.val) = s
      cases p <;> cases q <;> cases r <;> cases a <;> cases s <;> rfl
  · have hj' : j.val + 1 = n := by omega
    have hz : (⟨(j.val+1) % n, Nat.mod_lt _ hn⟩ : Fin n).val = 0 := by
      show (j.val + 1) % n = 0
      rw [hj', Nat.mod_self]
    rw [a_w_val f i a _ 0 hz, a_u_zero]
    have hu : (a_u f j.val ^^ f j) = true := by
      have := a_u_succ f j.val j.isLt
      rw [hj', a_u_n f hodd] at this
      simpa using this.symm
    have h0 : decide (i.val < 0) = false := by simp
    rw [h0]
    unfold a_w
    by_cases hij : j = i
    · subst hij
      have h2 : decide (j.val < j.val) = false := by simp
      rw [h2, decide_eq_true (rfl : j = j)]
      revert hu
      generalize a_u f j.val = p
      generalize f j = r
      cases p <;> cases r <;> cases a <;> decide
    · have hne : j.val ≠ i.val := fun h => hij (Fin.ext h)
      have h2 : decide (i.val < j.val) = true := by
        simp only [decide_eq_true_eq]; have := i.isLt; omega
      rw [h2, decide_eq_false hij]
      revert hu
      generalize a_u f j.val = p
      generalize a_u f i.val = q
      generalize f j = r
      cases p <;> cases q <;> cases r <;> cases a <;> decide

theorem a_key {n : ℕ} (hn : 0 < n) (f : Fin n → Bool)
    (hodd : Odd ((Finset.univ.filter (fun i => f i = true)).card))
    (C : Finset (Fin n × Bool)) (i : Fin n) (a : Bool)
    (hc : ∀ p ∈ C, a_w f i a p.1 = p.2) (j : Fin n) (b : Bool)
    (h1 : (j, b) ∈ C) (h2 : ((⟨(j.val+1) % n, Nat.mod_lt _ hn⟩ : Fin n), !(b ^^ f j)) ∈ C) :
    j = i ∧ b = a := by
  have e1 : a_w f i a j = b := hc _ h1
  have e2 : a_w f i a ⟨(j.val+1) % n, Nat.mod_lt _ hn⟩ = !(b ^^ f j) := hc _ h2
  rw [a_w_edge hn f hodd i a j, e1] at e2
  have hji : j = i := by
    by_contra hne
    rw [decide_eq_false hne] at e2
    revert e2
    generalize (b ^^ f j) = t
    cases t <;> decide
  subst hji
  exact ⟨rfl, by rw [← e1, a_w_self]⟩

theorem a_card {n : ℕ} (hn : 0 < n) (f : Fin n → Bool)
    (hodd : Odd ((Finset.univ.filter (fun i => f i = true)).card))
    (L : Finset (Finset (Fin n × Bool)))
    (hval : ∀ C ∈ L, ∃ (i : Fin n) (a : Bool), (i, a) ∈ C ∧
      ((⟨(i.val+1) % n, Nat.mod_lt _ hn⟩ : Fin n), !(a ^^ f i)) ∈ C)
    (hload : ∀ x : Fin n → Bool, Odd ((L.filter (fun C => (C.filter (fun p => x p.1 ≠ p.2)) = ∅)).card)) :
    2 * n ≤ L.card := by
  have hex : ∀ p : Fin n × Bool, ∃ C ∈ L, ∀ q ∈ C, a_w f p.1 p.2 q.1 = q.2 := by
    intro p
    have ho := hload (a_w f p.1 p.2)
    have hpos : 0 < (L.filter (fun C => (C.filter (fun q => a_w f p.1 p.2 q.1 ≠ q.2)) = ∅)).card := ho.pos
    obtain ⟨C, hC⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter, Finset.filter_eq_empty_iff] at hC
    refine ⟨C, hC.1, fun q hq => ?_⟩
    have := hC.2 hq
    exact not_not.mp this
  choose φ hφL hφc using hex
  have hinj : Set.InjOn φ (Finset.univ : Finset (Fin n × Bool)) := by
    intro p _ q _ hpq
    obtain ⟨j, b, hj1, hj2⟩ := hval (φ q) (hφL q)
    have h1 := a_key hn f hodd (φ q) q.1 q.2 (hφc q) j b hj1 hj2
    have h2 := a_key hn f hodd (φ q) p.1 p.2 (by rw [← hpq]; exact hφc p) j b hj1 hj2
    exact Prod.ext (h2.1.symm.trans h1.1) (h2.2.symm.trans h1.2)
  have := Finset.card_le_card_of_injOn φ (fun p _ => hφL p) hinj
  have hu : (Finset.univ : Finset (Fin n × Bool)).card = 2 * n := by
    simp [Finset.card_univ, mul_comm]
  rw [hu] at this
  exact this

theorem a_count {n : ℕ} (C : Finset (Fin n × Bool)) (hC : ∀ i : Fin n, ¬ ((i, false) ∈ C ∧ (i, true) ∈ C)) :
    (Finset.univ.filter (fun x : Fin n → Bool => C.filter (fun p => x p.1 ≠ p.2) = ∅)).card = 2 ^ (n - C.card) := by
  have e1 : (Finset.univ.filter (fun x : Fin n → Bool => C.filter (fun p => x p.1 ≠ p.2) = ∅)) =
      Fintype.piFinset (fun i : Fin n => Finset.univ.filter (fun b : Bool => (i, !b) ∉ C)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, Finset.filter_eq_empty_iff]
    constructor
    · intro h i hi
      apply h hi
      show x i ≠ !x i
      generalize x i = y
      cases y <;> decide
    · intro h p hp hne
      obtain ⟨i, c⟩ := p
      have hne' : x i ≠ c := hne
      have hc : c = !x i := by
        revert hne'; generalize x i = y; cases c <;> cases y <;> decide
      rw [hc] at hp
      exact h i hp
  rw [e1, Fintype.card_piFinset]
  have hS : (C.image Prod.fst).card = C.card := by
    apply Finset.card_image_of_injOn
    intro p hp q hq hpq
    obtain ⟨i, c⟩ := p
    obtain ⟨i', c'⟩ := q
    have hii : i = i' := hpq
    subst hii
    have hp' : (i, c) ∈ C := hp
    have hq' : (i, c') ∈ C := hq
    cases c <;> cases c'
    · rfl
    · exact absurd ⟨hp', hq'⟩ (hC i)
    · exact absurd ⟨hq', hp'⟩ (hC i)
    · rfl
  have e2 : ∀ i : Fin n, (Finset.univ.filter (fun b : Bool => (i, !b) ∉ C)).card =
      if i ∈ C.image Prod.fst then 1 else 2 := by
    intro i
    by_cases hi : i ∈ C.image Prod.fst
    · rw [ite_eq_left hi]
      obtain ⟨⟨j, c⟩, hjc, hji⟩ := Finset.mem_image.mp hi
      have hji' : j = i := hji
      subst hji'
      have e3 : Finset.univ.filter (fun b : Bool => (j, !b) ∉ C) = {c} := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hb
          by_contra hbc
          have hbc' : (!b) = c := by revert hbc; cases b <;> cases c <;> decide
          rw [hbc'] at hb
          exact hb hjc
        · rintro rfl
          intro hn
          cases b
          · exact hC j ⟨hjc, hn⟩
          · exact hC j ⟨hn, hjc⟩
      rw [e3, Finset.card_singleton]
    · rw [ite_eq_right hi]
      have e3 : Finset.univ.filter (fun b : Bool => (i, !b) ∉ C) = Finset.univ := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        intro hb
        exact hi (Finset.mem_image.mpr ⟨(i, !b), hb, rfl⟩)
      rw [e3, Finset.card_univ, Fintype.card_bool]
  rw [Finset.prod_congr rfl (fun i _ => e2 i), Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  rw [← hS]
  have e4 : (Finset.univ.filter (fun i : Fin n => ¬ (i ∈ C.image Prod.fst))) = (C.image Prod.fst)ᶜ := by
    ext i; simp
  rw [e4, Finset.card_compl, Fintype.card_fin]

theorem a_dc {n : ℕ} (L : Finset (Finset (Fin n × Bool))) :
    ∑ x : Fin n → Bool, (L.filter (fun C => (C.filter (fun p => x p.1 ≠ p.2)) = ∅)).card =
    ∑ C ∈ L, (Finset.univ.filter (fun x : Fin n → Bool => C.filter (fun p => x p.1 ≠ p.2) = ∅)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

theorem a_main (n : ℕ) (hn : 0 < n) (f : Fin n → Bool)
    (hodd : Odd ((Finset.univ.filter (fun i => f i = true)).card))
    (d : ℕ) (hdn : d ≤ n) (L : Finset (Finset (Fin n × Bool)))
    (hval : ∀ C ∈ L, ((∀ i : Fin n, ¬ ((i, false) ∈ C ∧ (i, true) ∈ C)) ∧
      ∃ (i : Fin n) (a : Bool), (i, a) ∈ C ∧ ((⟨(i.val+1) % n, Nat.mod_lt _ hn⟩ : Fin n), !(a ^^ f i)) ∈ C) ∧
        C.card ≤ d)
    (hload : ∀ x : Fin n → Bool, Odd ((L.filter (fun C => (C.filter (fun p => x p.1 ≠ p.2)) = ∅)).card)) :
    2*n ≤ L.card ∧ 2*n * 2^(n-d) ≤ ∑ x : Fin n → Bool, (L.filter (fun C => (C.filter (fun p => x p.1 ≠ p.2)) = ∅)).card ∧
      (∑ x : Fin n → Bool, (L.filter (fun C => (C.filter (fun p => x p.1 ≠ p.2)) = ∅)).card = 2*n * 2^(n-d) ↔
        L.card = 2*n ∧ ∀ C ∈ L, C.card = d) := by
  have hcard : 2 * n ≤ L.card := a_card hn f hodd L (fun C hC => (hval C hC).1.2) hload
  rw [a_dc L]
  have hsum : ∑ C ∈ L, (Finset.univ.filter (fun x : Fin n → Bool => C.filter (fun p => x p.1 ≠ p.2) = ∅)).card =
      ∑ C ∈ L, 2 ^ (n - C.card) :=
    Finset.sum_congr rfl (fun C hC => a_count C (hval C hC).1.1)
  rw [hsum]
  have hle : ∀ C ∈ L, 2 ^ (n - d) ≤ 2 ^ (n - C.card) := fun C hC =>
    Nat.pow_le_pow_right (by norm_num) (by have := (hval C hC).2; omega)
  have h1 : ∑ C ∈ L, 2 ^ (n - d) ≤ ∑ C ∈ L, 2 ^ (n - C.card) := Finset.sum_le_sum hle
  have h2 : ∑ C ∈ L, 2 ^ (n - d) = L.card * 2 ^ (n - d) := by rw [Finset.sum_const, smul_eq_mul]
  have hpos : 0 < 2 ^ (n - d) := by positivity
  have h3 : 2 * n * 2 ^ (n - d) ≤ L.card * 2 ^ (n - d) := Nat.mul_le_mul_right _ hcard
  refine ⟨hcard, le_trans h3 (by rw [← h2]; exact h1), ?_⟩
  constructor
  · intro heq
    have h4 : L.card * 2 ^ (n - d) = 2 * n * 2 ^ (n - d) := le_antisymm (by rw [← h2, ← heq]; exact h1) h3
    have h5 : L.card = 2 * n := Nat.eq_of_mul_eq_mul_right hpos h4
    refine ⟨h5, ?_⟩
    have h6 : ∑ C ∈ L, 2 ^ (n - d) = ∑ C ∈ L, 2 ^ (n - C.card) := by rw [h2, h4, heq]
    rw [Finset.sum_eq_sum_iff_of_le hle] at h6
    intro C hC
    have h7 := h6 C hC
    have h8 : n - d = n - C.card := Nat.pow_right_injective (le_refl 2) h7
    have := (hval C hC).2
    omega
  · rintro ⟨h5, h6⟩
    rw [Finset.sum_congr rfl (fun C hC => by rw [h6 C hC]), Finset.sum_const, smul_eq_mul, h5]

theorem partA : ∀ (n : ℕ) (hn : 0 < n), 2 ≤ n → ∀ f : Fin n → Bool,
  Odd ((Finset.univ.filter (fun i => f i = true)).card) →
  let Cell := Finset (Fin n × Bool)
  let next := fun i : Fin n => (⟨(i.val+1) % n, Nat.mod_lt _ hn⟩ : Fin n)
  let valid := fun C : Cell =>
    (∀ i : Fin n, ¬ ((i, false) ∈ C ∧ (i, true) ∈ C)) ∧
    ∃ (i : Fin n) (a : Bool), (i, a) ∈ C ∧ (next i, !(a ^^ f i)) ∈ C
  let load := fun (L : Finset Cell) (x : Fin n → Bool) =>
    (L.filter (fun C => (C.filter (fun p => x p.1 ≠ p.2)) = ∅)).card
  ∀ d : ℕ, 2 ≤ d → d ≤ n →
    let cover := fun L : Finset Cell =>
      (∀ C ∈ L, valid C ∧ C.card ≤ d) ∧ (∀ x, Odd (load L x))
    let incid := fun L : Finset Cell => ∑ x : Fin n → Bool, load L x
    let bound := 2*n * 2^(n-d)
    (∀ L, cover L → 2*n ≤ L.card ∧ bound ≤ incid L ∧
      (incid L = bound ↔ L.card = 2*n ∧ ∀ C ∈ L, C.card = d)) := by
  intro n hn h2 f hodd Cell next valid load d hd hdn cover incid bound L hcov
  exact a_main n hn f hodd d hdn L hcov.1 hcov.2

def c_pos (n : ℕ) (hn : 0 < n) (m : ℕ) : Fin n := ⟨m % n, Nat.mod_lt _ hn⟩

def c_F (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (s : ℕ) : ℕ → Bool
  | 0 => false
  | l + 1 => c_F n hn f s l ^^ f (c_pos n hn (s + l))

def c_inc (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (s l : ℕ) (x : Fin n → Bool) : Bool :=
  x (c_pos n hn (s + l)) ^^ x (c_pos n hn s) ^^ c_F n hn f s l

def c_Q (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) : ℕ → ℕ → ℕ → (Fin n → Bool) → Finset (Fin n)
  | 0, s, l, _ => {c_pos n hn s, c_pos n hn (s + l)}
  | t + 1, s, l, x =>
    if l ≤ 2 ^ t then c_Q n hn f t s l x
    else if c_inc n hn f s (2 ^ t) x = true then
      insert (c_pos n hn (s + l)) (c_Q n hn f t s (2 ^ t) x)
    else insert (c_pos n hn s) (c_Q n hn f t (s + 2 ^ t) (l - 2 ^ t) x)

def c_cell (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (t s l : ℕ) (x : Fin n → Bool) :
    Finset (Fin n × Bool) :=
  (c_Q n hn f t s l x).image (fun i => (i, x i))

def c_Lf (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (t s l : ℕ) : Finset (Finset (Fin n × Bool)) :=
  (Finset.univ.filter (fun x => c_inc n hn f s l x = true)).image (fun x => c_cell n hn f t s l x)

def c_Lk (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (t k m : ℕ) : Finset (Finset (Fin n × Bool)) :=
  (Finset.range k).biUnion (fun j => c_Lf n hn f t (j * m) m)

def c_load (n : ℕ) (L : Finset (Finset (Fin n × Bool))) (x : Fin n → Bool) : ℕ :=
  (L.filter (fun C => (C.filter (fun p => x p.1 ≠ p.2)) = ∅)).card

def c_valid (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (C : Finset (Fin n × Bool)) : Prop :=
  (∀ i : Fin n, ¬ ((i, false) ∈ C ∧ (i, true) ∈ C)) ∧
    ∃ (i : Fin n) (a : Bool), (i, a) ∈ C ∧ ((⟨(i.val+1) % n, Nat.mod_lt _ hn⟩ : Fin n), !(a ^^ f i)) ∈ C

theorem c_F_zero (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (s : ℕ) : c_F n hn f s 0 = false := rfl

theorem c_F_succ (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (s l : ℕ) :
    c_F n hn f s (l + 1) = (c_F n hn f s l ^^ f (c_pos n hn (s + l))) := rfl

theorem c_F_one (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (s : ℕ) :
    c_F n hn f s 1 = f (c_pos n hn s) := by
  show (c_F n hn f s 0 ^^ f (c_pos n hn (s + 0))) = _
  simp [c_F_zero]

theorem c_F_add (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (s a b : ℕ) :
    c_F n hn f s (a + b) = (c_F n hn f s a ^^ c_F n hn f (s + a) b) := by
  induction b with
  | zero => simp [c_F_zero]
  | succ b ih =>
    rw [← Nat.add_assoc, c_F_succ, c_F_succ, ih, Nat.add_assoc s a b, Bool.xor_assoc]

theorem c_b5 (e m s u v : Bool) : (e ^^ s ^^ (u ^^ v)) = ((m ^^ s ^^ u) ^^ (e ^^ m ^^ v)) := by
  revert e m s u v; decide

theorem c_b3 (a b c : Bool) (h : (a ^^ b ^^ c) = true) : a = !(b ^^ c) := by
  revert h; revert a b c; decide

theorem c_b3n (a b c : Bool) : ((!a) ^^ b ^^ c) = !(a ^^ b ^^ c) := by
  revert a b c; decide

theorem c_inc_add (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (s a b : ℕ) (x : Fin n → Bool) :
    c_inc n hn f s (a + b) x = (c_inc n hn f s a x ^^ c_inc n hn f (s + a) b x) := by
  unfold c_inc
  rw [c_F_add, ← Nat.add_assoc]
  exact c_b5 _ _ _ _ _

theorem c_pos_eq (n : ℕ) (hn : 0 < n) (i : Fin n) : c_pos n hn i.val = i := by
  apply Fin.ext; simp [c_pos, Nat.mod_eq_of_lt i.isLt]

theorem c_pos_n (n : ℕ) (hn : 0 < n) : c_pos n hn (0 + n) = c_pos n hn 0 := by
  apply Fin.ext; simp [c_pos]

theorem c_next (n : ℕ) (hn : 0 < n) (m : ℕ) :
    ((⟨((c_pos n hn m).val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n)) = c_pos n hn (m + 1) := by
  apply Fin.ext; simp [c_pos, Nat.mod_add_mod]

theorem c_odd_succ (c : ℕ) : decide (Odd (c + 1)) = !decide (Odd c) := by
  rcases Nat.even_or_odd c with h | h
  · rw [decide_eq_true h.add_one, decide_eq_false (Nat.not_odd_iff_even.mpr h)]; rfl
  · rw [decide_eq_false (Nat.not_odd_iff_even.mpr h.add_one), decide_eq_true h]; rfl

theorem c_F_count (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (l : ℕ) :
    c_F n hn f 0 l =
      decide (Odd ((Finset.range l).filter (fun j => f (c_pos n hn j) = true)).card) := by
  induction l with
  | zero => simp [c_F_zero]
  | succ l ih =>
    rw [c_F_succ, ih, Finset.range_add_one, Finset.filter_insert, zero_add]
    by_cases h : f (c_pos n hn l) = true
    · rw [ite_eq_left h, Finset.card_insert_of_notMem (by simp), h, c_odd_succ]
      simp
    · rw [ite_eq_right h]
      simp only [Bool.not_eq_true] at h
      rw [h, Bool.xor_false]

theorem c_F_full (n : ℕ) (hn : 0 < n) (f : Fin n → Bool)
    (hodd : Odd ((Finset.univ.filter (fun i => f i = true)).card)) : c_F n hn f 0 n = true := by
  rw [c_F_count]
  have e : ((Finset.range n).filter (fun j => f (c_pos n hn j) = true)).card =
      (Finset.univ.filter (fun i => f i = true)).card := by
    apply Finset.card_nbij' (fun j => c_pos n hn j) (fun i => i.val)
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Finset.mem_univ,
        true_and] at hj ⊢
      exact hj.2
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Finset.mem_univ,
        true_and] at hi ⊢
      exact ⟨i.isLt, by rw [c_pos_eq]; exact hi⟩
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
      simp [c_pos, Nat.mod_eq_of_lt hj.1]
    · intro i _
      exact c_pos_eq n hn i
  rw [e]
  exact decide_eq_true hodd

theorem c_inc_full (n : ℕ) (hn : 0 < n) (f : Fin n → Bool)
    (hodd : Odd ((Finset.univ.filter (fun i => f i = true)).card)) (x : Fin n → Bool) :
    c_inc n hn f 0 n x = true := by
  unfold c_inc
  rw [c_pos_n, c_F_full n hn f hodd]
  simp

theorem c_Q_zero (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (s l : ℕ) (x : Fin n → Bool) :
    c_Q n hn f 0 s l x = {c_pos n hn s, c_pos n hn (s + l)} := rfl

theorem c_Q_succ (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (t s l : ℕ) (x : Fin n → Bool) :
    c_Q n hn f (t + 1) s l x = (if l ≤ 2 ^ t then c_Q n hn f t s l x
      else if c_inc n hn f s (2 ^ t) x = true then
        insert (c_pos n hn (s + l)) (c_Q n hn f t s (2 ^ t) x)
      else insert (c_pos n hn s) (c_Q n hn f t (s + 2 ^ t) (l - 2 ^ t) x)) := rfl

theorem c_Q_ends (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (x : Fin n → Bool) (t : ℕ) :
    ∀ s l, c_pos n hn s ∈ c_Q n hn f t s l x ∧ c_pos n hn (s + l) ∈ c_Q n hn f t s l x := by
  induction t with
  | zero => intro s l; simp [c_Q_zero]
  | succ t ih =>
    intro s l
    rw [c_Q_succ]
    split_ifs with h1 h2
    · exact ih s l
    · exact ⟨Finset.mem_insert_of_mem (ih s _).1, Finset.mem_insert_self _ _⟩
    · refine ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ?_⟩
      have := (ih (s + 2 ^ t) (l - 2 ^ t)).2
      rwa [show s + 2 ^ t + (l - 2 ^ t) = s + l by omega] at this

theorem c_Q_card (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (x : Fin n → Bool) (t : ℕ) :
    ∀ s l, (c_Q n hn f t s l x).card ≤ t + 2 := by
  induction t with
  | zero => intro s l; rw [c_Q_zero]; exact Finset.card_le_two
  | succ t ih =>
    intro s l
    rw [c_Q_succ]
    split_ifs with h1 h2
    · exact (ih s l).trans (by omega)
    · exact (Finset.card_insert_le _ _).trans (by have := ih s (2 ^ t); omega)
    · exact (Finset.card_insert_le _ _).trans (by have := ih (s + 2 ^ t) (l - 2 ^ t); omega)

theorem c_Q_card_loop (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (x : Fin n → Bool) (t : ℕ) :
    ∀ s l, c_pos n hn (s + l) = c_pos n hn s → (c_Q n hn f t s l x).card ≤ t + 1 := by
  induction t with
  | zero =>
    intro s l h
    rw [c_Q_zero, h, Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.card_singleton]
  | succ t ih =>
    intro s l h
    rw [c_Q_succ]
    split_ifs with h1 h2
    · exact (ih s l h).trans (by omega)
    · have hm : c_pos n hn (s + l) ∈ c_Q n hn f t s (2 ^ t) x := by
        rw [h]; exact (c_Q_ends n hn f x t s (2 ^ t)).1
      rw [Finset.insert_eq_of_mem hm]
      exact c_Q_card n hn f x t s _
    · have hm := (c_Q_ends n hn f x t (s + 2 ^ t) (l - 2 ^ t)).2
      rw [show s + 2 ^ t + (l - 2 ^ t) = s + l by omega, h] at hm
      rw [Finset.insert_eq_of_mem hm]
      exact c_Q_card n hn f x t _ _

theorem c_inc_congr (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (s l : ℕ) (x y : Fin n → Bool)
    (h1 : y (c_pos n hn s) = x (c_pos n hn s))
    (h2 : y (c_pos n hn (s + l)) = x (c_pos n hn (s + l))) :
    c_inc n hn f s l y = c_inc n hn f s l x := by
  unfold c_inc; rw [h1, h2]

theorem c_Q_adapt (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (x y : Fin n → Bool) (t : ℕ) :
    ∀ s l, (∀ i ∈ c_Q n hn f t s l x, y i = x i) →
      c_Q n hn f t s l y = c_Q n hn f t s l x := by
  induction t with
  | zero => intro s l _; rfl
  | succ t ih =>
    intro s l h
    rw [c_Q_succ] at h
    rw [c_Q_succ, c_Q_succ]
    by_cases h1 : l ≤ 2 ^ t
    · simp only [ite_eq_left h1] at h ⊢
      exact ih s l h
    · simp only [ite_eq_right h1] at h ⊢
      by_cases h2 : c_inc n hn f s (2 ^ t) x = true
      · simp only [ite_eq_left h2] at h
        have hsub : ∀ i ∈ c_Q n hn f t s (2 ^ t) x, y i = x i :=
          fun i hi => h i (Finset.mem_insert_of_mem hi)
        have he := c_Q_ends n hn f x t s (2 ^ t)
        have h3 : c_inc n hn f s (2 ^ t) y = true := by
          rw [c_inc_congr n hn f s (2 ^ t) x y (hsub _ he.1) (hsub _ he.2)]; exact h2
        rw [ite_eq_left h2, ite_eq_left h3, ih s (2 ^ t) hsub]
      · simp only [ite_eq_right h2] at h
        have hsub : ∀ i ∈ c_Q n hn f t (s + 2 ^ t) (l - 2 ^ t) x, y i = x i :=
          fun i hi => h i (Finset.mem_insert_of_mem hi)
        have he := c_Q_ends n hn f x t (s + 2 ^ t) (l - 2 ^ t)
        have h3 : ¬ c_inc n hn f s (2 ^ t) y = true := by
          rw [c_inc_congr n hn f s (2 ^ t) x y (h _ (Finset.mem_insert_self _ _)) (hsub _ he.1)]
          exact h2
        rw [ite_eq_right h2, ite_eq_right h3, ih _ _ hsub]

theorem c_Q_viol (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (x : Fin n → Bool) (t : ℕ) :
    ∀ s l, c_inc n hn f s l x = true → 1 ≤ l → l ≤ 2 ^ t →
      ∃ j, c_pos n hn (s + j) ∈ c_Q n hn f t s l x ∧
        c_pos n hn (s + j + 1) ∈ c_Q n hn f t s l x ∧
        x (c_pos n hn (s + j + 1)) = !(x (c_pos n hn (s + j)) ^^ f (c_pos n hn (s + j))) := by
  induction t with
  | zero =>
    intro s l h hl1 hl2
    have hl : l = 1 := by simp at hl2; omega
    subst hl
    refine ⟨0, ?_, ?_, ?_⟩
    · simp [c_Q_zero]
    · simp [c_Q_zero]
    · unfold c_inc at h
      rw [c_F_one] at h
      simp only [Nat.add_zero]
      exact c_b3 _ _ _ h
  | succ t ih =>
    intro s l h hl1 hl2
    rw [c_Q_succ]
    split_ifs with h1 h2
    · exact ih s l h hl1 h1
    · obtain ⟨j, hj1, hj2, hj3⟩ := ih s (2 ^ t) h2 Nat.one_le_two_pow le_rfl
      exact ⟨j, Finset.mem_insert_of_mem hj1, Finset.mem_insert_of_mem hj2, hj3⟩
    · have e : l = 2 ^ t + (l - 2 ^ t) := by omega
      have h3 : c_inc n hn f (s + 2 ^ t) (l - 2 ^ t) x = true := by
        have h' := h
        rw [e, c_inc_add] at h'
        simp only [Bool.not_eq_true] at h2
        rw [h2, Bool.false_xor] at h'
        exact h'
      have hl3 : l ≤ 2 ^ t * 2 := by rw [pow_succ] at hl2; exact hl2
      obtain ⟨j, hj1, hj2, hj3⟩ := ih (s + 2 ^ t) (l - 2 ^ t) h3 (by omega) (by omega)
      refine ⟨2 ^ t + j, ?_, ?_, ?_⟩
      · rw [← Nat.add_assoc s (2 ^ t) j]; exact Finset.mem_insert_of_mem hj1
      · rw [← Nat.add_assoc s (2 ^ t) j]; exact Finset.mem_insert_of_mem hj2
      · rw [← Nat.add_assoc s (2 ^ t) j]; exact hj3

theorem c_Q_sub (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (x : Fin n → Bool) (t : ℕ) :
    ∀ s l, ∀ p ∈ c_Q n hn f t s l x, ∃ j, j ≤ l ∧ p = c_pos n hn (s + j) := by
  induction t with
  | zero =>
    intro s l p hp
    rw [c_Q_zero] at hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | hp
    · exact ⟨0, Nat.zero_le _, by rw [hp, Nat.add_zero]⟩
    · exact ⟨l, le_rfl, hp⟩
  | succ t ih =>
    intro s l p hp
    rw [c_Q_succ] at hp
    split_ifs at hp with h1 h2
    · exact ih s l p hp
    · rcases Finset.mem_insert.mp hp with hp | hp
      · exact ⟨l, le_rfl, hp⟩
      · obtain ⟨j, hj, hpj⟩ := ih s (2 ^ t) p hp
        exact ⟨j, by omega, hpj⟩
    · rcases Finset.mem_insert.mp hp with hp | hp
      · exact ⟨0, Nat.zero_le _, by rw [hp, Nat.add_zero]⟩
      · obtain ⟨j, hj, hpj⟩ := ih (s + 2 ^ t) (l - 2 ^ t) p hp
        exact ⟨2 ^ t + j, by omega, by rw [hpj, Nat.add_assoc]⟩

theorem c_cell_cons (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (t s l : ℕ) (x y : Fin n → Bool) :
    ((c_cell n hn f t s l x).filter (fun p => y p.1 ≠ p.2) = ∅) ↔
      ∀ i ∈ c_Q n hn f t s l x, y i = x i := by
  rw [Finset.filter_eq_empty_iff]
  unfold c_cell
  simp only [Finset.mem_image, ne_eq, not_not]
  constructor
  · intro h i hi
    exact h ⟨i, hi, rfl⟩
  · rintro h p ⟨i, hi, rfl⟩
    exact h i hi

theorem c_cell_mem (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (t s l : ℕ) (x : Fin n → Bool)
    (i : Fin n) (b : Bool) (h : (i, b) ∈ c_cell n hn f t s l x) : b = x i := by
  simp only [c_cell, Finset.mem_image, Prod.mk.injEq] at h
  obtain ⟨a, _, rfl, rfl⟩ := h
  rfl

theorem c_cell_card (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (t s l : ℕ) (x : Fin n → Bool) :
    (c_cell n hn f t s l x).card = (c_Q n hn f t s l x).card := by
  unfold c_cell
  apply Finset.card_image_of_injective
  intro a b hab
  simp only [Prod.mk.injEq] at hab
  exact hab.1

theorem c_cell_adapt (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (t s l : ℕ) (x y : Fin n → Bool)
    (h : ∀ i ∈ c_Q n hn f t s l x, y i = x i) :
    c_cell n hn f t s l y = c_cell n hn f t s l x ∧ c_inc n hn f s l y = c_inc n hn f s l x := by
  have he := c_Q_ends n hn f x t s l
  refine ⟨?_, c_inc_congr n hn f s l x y (h _ he.1) (h _ he.2)⟩
  unfold c_cell
  rw [c_Q_adapt n hn f x y t s l h]
  apply Finset.image_congr
  intro i hi
  show (i, y i) = (i, x i)
  rw [h i hi]

theorem c_Lf_filter (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (t s l : ℕ) (y : Fin n → Bool) :
    (c_Lf n hn f t s l).filter (fun C => (C.filter (fun p => y p.1 ≠ p.2)) = ∅) =
      if c_inc n hn f s l y = true then {c_cell n hn f t s l y} else ∅ := by
  ext C
  simp only [c_Lf, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hc⟩
    rw [c_cell_cons] at hc
    obtain ⟨h1, h2⟩ := c_cell_adapt n hn f t s l x y hc
    rw [ite_eq_left (h2.trans hx), h1, Finset.mem_singleton]
  · intro hC
    split_ifs at hC with h
    · rw [Finset.mem_singleton] at hC
      subst hC
      refine ⟨⟨y, h, rfl⟩, ?_⟩
      rw [c_cell_cons]
      intro i _
      rfl
    · simp at hC

theorem c_cell_valid (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (t s l : ℕ) (x : Fin n → Bool)
    (h : c_inc n hn f s l x = true) (hl1 : 1 ≤ l) (hl2 : l ≤ 2 ^ t) :
    c_valid n hn f (c_cell n hn f t s l x) := by
  unfold c_valid
  constructor
  · intro i hi
    have e1 := c_cell_mem n hn f t s l x i false hi.1
    have e2 := c_cell_mem n hn f t s l x i true hi.2
    exact absurd (e1.trans e2.symm) (by decide)
  · obtain ⟨j, hj1, hj2, hj3⟩ := c_Q_viol n hn f x t s l h hl1 hl2
    refine ⟨c_pos n hn (s + j), x (c_pos n hn (s + j)), ?_, ?_⟩
    · exact Finset.mem_image_of_mem (fun i => (i, x i)) hj1
    · rw [c_next, ← hj3]
      exact Finset.mem_image_of_mem (fun i => (i, x i)) hj2

theorem c_first (n : ℕ) (hn : 0 < n) (f : Fin n → Bool)
    (hodd : Odd ((Finset.univ.filter (fun i => f i = true)).card)) (d : ℕ) (hd : 2 ≤ d)
    (h : 2 * n ≤ 2 ^ d) :
    ∃ L : Finset (Finset (Fin n × Bool)),
      ((∀ C ∈ L, c_valid n hn f C ∧ C.card ≤ d) ∧ (∀ x, Odd (c_load n L x))) ∧
        ∑ x : Fin n → Bool, c_load n L x = 2 ^ n := by
  have hnd : n ≤ 2 ^ (d - 1) := by
    have : 2 ^ d = 2 ^ (d - 1) * 2 := by rw [← pow_succ]; congr 1; omega
    omega
  have hload : ∀ y, c_load n (c_Lf n hn f (d - 1) 0 n) y = 1 := by
    intro y
    unfold c_load
    rw [c_Lf_filter, ite_eq_left (c_inc_full n hn f hodd y), Finset.card_singleton]
  refine ⟨c_Lf n hn f (d - 1) 0 n, ⟨fun C hC => ?_, fun x => ?_⟩, ?_⟩
  · simp only [c_Lf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hC
    obtain ⟨x, hx, rfl⟩ := hC
    refine ⟨c_cell_valid n hn f (d - 1) 0 n x hx hn hnd, ?_⟩
    rw [c_cell_card]
    have := c_Q_card_loop n hn f x (d - 1) 0 n (c_pos_n n hn)
    omega
  · rw [hload]; exact odd_one
  · simp only [hload]
    simp

theorem c_arith (n k m j j' i : ℕ) (hm : 0 < m) (hnk : n = k * m) (hj : j < k) (hj' : j' < k)
    (hi : i ≤ m) (h : (j * m) % n = (j' * m + i) % n) :
    j = j' ∨ j = j' + 1 ∨ (j = 0 ∧ j' + 1 = k) := by
  subst hnk
  have h1 : j * m < k * m := Nat.mul_lt_mul_of_pos_right hj hm
  have h2 : (j' + 1) * m ≤ k * m := Nat.mul_le_mul_right m hj'
  rw [Nat.add_mul, Nat.one_mul] at h2
  rw [Nat.mod_eq_of_lt h1] at h
  rcases Nat.lt_or_ge (j' * m + i) (k * m) with h3 | h3
  · rw [Nat.mod_eq_of_lt h3] at h
    have h4 : j' * m ≤ j * m := by omega
    have h5 : j * m ≤ (j' + 1) * m := by rw [Nat.add_mul, Nat.one_mul]; omega
    have h6 := Nat.le_of_mul_le_mul_right h4 hm
    have h7 := Nat.le_of_mul_le_mul_right h5 hm
    omega
  · have h8 : j' * m + i = k * m := by omega
    rw [h8, Nat.mod_self] at h
    have h9 : j = 0 := by
      rcases Nat.mul_eq_zero.mp h with h9 | h9
      · exact h9
      · omega
    have h10 : k * m ≤ (j' + 1) * m := by rw [Nat.add_mul, Nat.one_mul]; omega
    have h11 := Nat.le_of_mul_le_mul_right h10 hm
    omega

theorem c_cell_ne (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (t k m : ℕ) (hm : 0 < m) (hk : 3 ≤ k)
    (hnk : n = k * m) (y : Fin n → Bool) (j j' : ℕ) (hj : j < k) (hj' : j' < k) (hne : j ≠ j') :
    c_cell n hn f t (j * m) m y ≠ c_cell n hn f t (j' * m) m y := by
  intro heq
  have key : ∀ a b, a < k → b < k →
      c_cell n hn f t (a * m) m y = c_cell n hn f t (b * m) m y →
      a = b ∨ a = b + 1 ∨ (a = 0 ∧ b + 1 = k) := by
    intro a b ha hb hab
    have h1 : (c_pos n hn (a * m), y (c_pos n hn (a * m))) ∈ c_cell n hn f t (b * m) m y := by
      rw [← hab]
      exact Finset.mem_image_of_mem (fun i => (i, y i)) (c_Q_ends n hn f y t (a * m) m).1
    have h2 : c_pos n hn (a * m) ∈ c_Q n hn f t (b * m) m y := by
      unfold c_cell at h1
      rw [Finset.mem_image] at h1
      obtain ⟨i, hi, hi'⟩ := h1
      rw [Prod.mk.injEq] at hi'
      rw [← hi'.1]; exact hi
    obtain ⟨i, hi, hpi⟩ := c_Q_sub n hn f y t (b * m) m _ h2
    have hv : (a * m) % n = (b * m + i) % n := congrArg Fin.val hpi
    exact c_arith n k m a b i hm hnk ha hb hi hv
  have A := key j j' hj hj' heq
  have B := key j' j hj' hj heq.symm
  omega

theorem c_arc_ne (n : ℕ) (hn : 0 < n) (k m j : ℕ) (hm : 0 < m) (hk : 2 ≤ k) (hnk : n = k * m)
    (hj : j < k) : c_pos n hn (j * m) ≠ c_pos n hn (j * m + m) := by
  intro h
  have hv : (j * m) % n = (j * m + m) % n := congrArg Fin.val h
  subst hnk
  have h1 : j * m < k * m := Nat.mul_lt_mul_of_pos_right hj hm
  have h2 : (j + 1) * m ≤ k * m := Nat.mul_le_mul_right m hj
  rw [Nat.add_mul, Nat.one_mul] at h2
  have h3 : 2 * m ≤ k * m := Nat.mul_le_mul_right m hk
  rw [Nat.mod_eq_of_lt h1] at hv
  rcases Nat.lt_or_ge (j * m + m) (k * m) with h4 | h4
  · rw [Nat.mod_eq_of_lt h4] at hv; omega
  · have h5 : j * m + m = k * m := by omega
    rw [h5, Nat.mod_self] at hv
    omega

theorem c_half (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (s l : ℕ)
    (hne : c_pos n hn s ≠ c_pos n hn (s + l)) :
    (Finset.univ.filter (fun y : Fin n → Bool => c_inc n hn f s l y = true)).card = 2 ^ (n - 1) := by
  have hg : ∀ y : Fin n → Bool,
      c_inc n hn f s l (Function.update y (c_pos n hn (s + l)) (!(y (c_pos n hn (s + l))))) =
        !(c_inc n hn f s l y) := by
    intro y
    unfold c_inc
    rw [Function.update_self, Function.update_of_ne hne]
    exact c_b3n _ _ _
  have hgg : ∀ y : Fin n → Bool,
      Function.update (Function.update y (c_pos n hn (s + l)) (!(y (c_pos n hn (s + l)))))
        (c_pos n hn (s + l))
        (!(Function.update y (c_pos n hn (s + l)) (!(y (c_pos n hn (s + l)))) (c_pos n hn (s + l))))
        = y := by
    intro y
    rw [Function.update_self, Function.update_idem, Bool.not_not, Function.update_eq_self]
  have h1 : (Finset.univ.filter (fun y : Fin n → Bool => c_inc n hn f s l y = true)).card =
      (Finset.univ.filter (fun y : Fin n → Bool => ¬ c_inc n hn f s l y = true)).card := by
    apply Finset.card_nbij'
      (fun y => Function.update y (c_pos n hn (s + l)) (!(y (c_pos n hn (s + l)))))
      (fun y => Function.update y (c_pos n hn (s + l)) (!(y (c_pos n hn (s + l)))))
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [hg, hy]; decide
    · intro y hy
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [hg]; simpa using hy
    · intro y _; exact hgg y
    · intro y _; exact hgg y
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n → Bool)))
    (fun y => c_inc n hn f s l y = true)
  have hu : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by simp
  rw [hu] at h2
  have h3 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  omega

theorem c_par (n : ℕ) (hn : 0 < n) (f : Fin n → Bool) (m : ℕ) (y : Fin n → Bool) (J : ℕ) :
    decide (Odd ((Finset.range J).filter (fun j => c_inc n hn f (j * m) m y = true)).card) =
      c_inc n hn f 0 (J * m) y := by
  induction J with
  | zero => simp [c_inc, c_F_zero]
  | succ J ih =>
    rw [Finset.range_add_one, Finset.filter_insert, Nat.add_mul, Nat.one_mul, c_inc_add, ← ih,
      zero_add]
    by_cases h : c_inc n hn f (J * m) m y = true
    · rw [ite_eq_left h, Finset.card_insert_of_notMem (by simp), h, c_odd_succ]
      simp
    · rw [ite_eq_right h]
      simp only [Bool.not_eq_true] at h
      rw [h, Bool.xor_false]

theorem c_second (n : ℕ) (hn : 0 < n) (f : Fin n → Bool)
    (hodd : Odd ((Finset.univ.filter (fun i => f i = true)).card)) (d : ℕ) (hd : 2 ≤ d)
    (hdn : d ≤ n) (k : ℕ) (hk : 3 ≤ k) (hnk : n = k * 2 ^ (d - 2)) :
    ∃ L : Finset (Finset (Fin n × Bool)),
      ((∀ C ∈ L, c_valid n hn f C ∧ C.card ≤ d) ∧ (∀ x, Odd (c_load n L x))) ∧
        ∑ x : Fin n → Bool, c_load n L x = 2 * n * 2 ^ (n - d) := by
  obtain ⟨m, hm_def⟩ : ∃ m, m = 2 ^ (d - 2) := ⟨_, rfl⟩
  rw [← hm_def] at hnk
  have hm : 0 < m := by rw [hm_def]; positivity
  have hload : ∀ y, c_load n (c_Lk n hn f (d - 2) k m) y =
      ((Finset.range k).filter (fun j => c_inc n hn f (j * m) m y = true)).card := by
    intro y
    unfold c_load c_Lk
    rw [Finset.filter_biUnion]
    rw [Finset.biUnion_congr rfl (fun j _ => c_Lf_filter n hn f (d - 2) (j * m) m y)]
    rw [Finset.card_biUnion, Finset.card_filter]
    · apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    · intro a ha b hb hab
      simp only [Function.onFun]
      split_ifs with h1 h2
      · rw [Finset.disjoint_singleton]
        exact c_cell_ne n hn f (d - 2) k m hm hk hnk y a b (Finset.mem_range.mp ha)
          (Finset.mem_range.mp hb) hab
      · exact Finset.disjoint_empty_right _
      · exact Finset.disjoint_empty_left _
      · exact Finset.disjoint_empty_left _
  refine ⟨c_Lk n hn f (d - 2) k m, ⟨fun C hC => ?_, fun y => ?_⟩, ?_⟩
  · simp only [c_Lk, Finset.mem_biUnion, c_Lf, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and] at hC
    obtain ⟨j, _, x, hx, rfl⟩ := hC
    refine ⟨c_cell_valid n hn f (d - 2) (j * m) m x hx hm hm_def.le, ?_⟩
    rw [c_cell_card]
    have := c_Q_card n hn f x (d - 2) (j * m) m
    omega
  · rw [hload]
    have := c_par n hn f m y k
    rw [← hnk, c_inc_full n hn f hodd] at this
    exact of_decide_eq_true this
  · simp only [hload, Finset.card_filter]
    rw [Finset.sum_comm]
    have hj : ∀ j ∈ Finset.range k,
        (∑ y : Fin n → Bool, if c_inc n hn f (j * m) m y = true then 1 else 0) = 2 ^ (n - 1) := by
      intro j hj
      have := c_half n hn f (j * m) m
        (c_arc_ne n hn k m j hm (by omega) hnk (Finset.mem_range.mp hj))
      rw [Finset.card_filter] at this
      exact this
    rw [Finset.sum_congr rfl hj, Finset.sum_const, Finset.card_range, smul_eq_mul]
    have e1 : 2 ^ (n - 1) = 2 * m * 2 ^ (n - d) := by
      rw [hm_def, ← pow_succ', ← pow_add]; congr 1; omega
    rw [e1, hnk]
    ring

theorem constr : ∀ (n : ℕ) (hn : 0 < n), 2 ≤ n → ∀ f : Fin n → Bool,
  Odd ((Finset.univ.filter (fun i => f i = true)).card) →
  let Cell := Finset (Fin n × Bool)
  let next := fun i : Fin n => (⟨(i.val+1) % n, Nat.mod_lt _ hn⟩ : Fin n)
  let valid := fun C : Cell =>
    (∀ i : Fin n, ¬ ((i, false) ∈ C ∧ (i, true) ∈ C)) ∧
    ∃ (i : Fin n) (a : Bool), (i, a) ∈ C ∧ (next i, !(a ^^ f i)) ∈ C
  let load := fun (L : Finset Cell) (x : Fin n → Bool) =>
    (L.filter (fun C => (C.filter (fun p => x p.1 ≠ p.2)) = ∅)).card
  ∀ d : ℕ, 2 ≤ d → d ≤ n →
    let cover := fun L : Finset Cell =>
      (∀ C ∈ L, valid C ∧ C.card ≤ d) ∧ (∀ x, Odd (load L x))
    let incid := fun L : Finset Cell => ∑ x : Fin n → Bool, load L x
    let bound := 2*n * 2^(n-d)
    (2*n ≤ 2^d → ∃ L, cover L ∧ incid L = 2^n) ∧
    ((∃ k : ℕ, 2 ≤ k ∧ n = k * 2^(d-2)) →
      ∃ L, cover L ∧ incid L = bound) := by
  intro n hn h2 f hodd Cell next valid load d hd hdn cover incid bound
  refine ⟨fun h => c_first n hn f hodd d hd h, ?_⟩
  rintro ⟨k, hk, hnk⟩
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · have hk2 : k = 2 := by omega
    subst hk2
    have hp : 2 ^ d = 2 ^ (d - 2) * 2 ^ 2 := by rw [← pow_add]; congr 1; omega
    have h2d : 2 * n = 2 ^ d := by rw [hp, hnk]; ring
    obtain ⟨L, hL1, hL2⟩ := c_first n hn f hodd d hd h2d.le
    refine ⟨L, hL1, ?_⟩
    show ∑ x : Fin n → Bool, c_load n L x = 2 * n * 2 ^ (n - d)
    rw [hL2, h2d, ← pow_add]
    congr 1
    omega
  · exact c_second n hn f hodd d hd hdn k hk3 hnk

end PEqualNP.Outside.L_pcx_256

theorem PEqualNP.Outside.L_pcx_256 : ∀ (n : ℕ) (hn : 0 < n), 2 ≤ n → ∀ f : Fin n → Bool,
  Odd ((Finset.univ.filter (fun i => f i = true)).card) →
  let Cell := Finset (Fin n × Bool)
  let next := fun i : Fin n => (⟨(i.val+1) % n, Nat.mod_lt _ hn⟩ : Fin n)
  let valid := fun C : Cell =>
    (∀ i : Fin n, ¬ ((i, false) ∈ C ∧ (i, true) ∈ C)) ∧
    ∃ (i : Fin n) (a : Bool), (i, a) ∈ C ∧ (next i, !(a ^^ f i)) ∈ C
  let load := fun (L : Finset Cell) (x : Fin n → Bool) =>
    (L.filter (fun C => (C.filter (fun p => x p.1 ≠ p.2)) = ∅)).card
  ∀ d : ℕ, 2 ≤ d → d ≤ n →
    let cover := fun L : Finset Cell =>
      (∀ C ∈ L, valid C ∧ C.card ≤ d) ∧ (∀ x, Odd (load L x))
    let incid := fun L : Finset Cell => ∑ x : Fin n → Bool, load L x
    let bound := 2*n * 2^(n-d)
    (∀ L, cover L → 2*n ≤ L.card ∧ bound ≤ incid L ∧
      (incid L = bound ↔ L.card = 2*n ∧ ∀ C ∈ L, C.card = d)) ∧
    ((∃ L, cover L ∧ incid L = 2^n) ↔ 2*n ≤ 2^d) ∧
    ((∃ k : ℕ, 2 ≤ k ∧ n = k * 2^(d-2)) →
      ∃ L, cover L ∧ incid L = bound) := by
  intro n hn h2 f hodd Cell next valid load d hd hdn cover incid bound
  have hA := PEqualNP.Outside.L_pcx_256.partA n hn h2 f hodd d hd hdn
  have hC := PEqualNP.Outside.L_pcx_256.constr n hn h2 f hodd d hd hdn
  refine ⟨hA, ⟨?_, hC.1⟩, hC.2⟩
  rintro ⟨L, hcov, hinc⟩
  have hb : bound ≤ incid L := (hA L hcov).2.1
  rw [hinc] at hb
  have e : 2^n = 2^d * 2^(n-d) := by rw [← pow_add]; congr 1; omega
  have hb' : 2*n * 2^(n-d) ≤ 2^d * 2^(n-d) := by rw [← e]; exact hb
  exact Nat.le_of_mul_le_mul_right hb' (by positivity)
