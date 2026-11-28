import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_335_aux

open Finset

lemma automaton {X β : Type} [DecidableEq β] [Nonempty X] {N b : ℕ}
    (rd : Fin N → X → Bool) (F : ℕ → X → β) (S : ℕ → Finset β)
    (hS : ∀ k ≤ N, ∀ x, F k x ∈ S k) (hcard : ∀ k ≤ N, (S k).card ≤ 2 ^ b)
    (h0 : ∀ x y, F 0 x = F 0 y)
    (hstep : ∀ (k : Fin N) x y, F k x = F k y → rd k x = rd k y → F (k + 1) x = F (k + 1) y)
    (fin : β → Bool) :
    ∃ (init : Fin (2 ^ b)) (step : Fin N → Fin (2 ^ b) → Bool → Fin (2 ^ b))
      (out : Fin (2 ^ b) → Bool),
      ∀ x, out ((List.finRange N).foldl (fun st k => step k st (rd k x)) init) = fin (F N x) := by
  classical
  have hpos : 0 < 2 ^ b := Nat.pow_pos two_pos
  let enc : ℕ → β → Fin (2 ^ b) := fun k v =>
    if h : v ∈ S k ∧ k ≤ N then
      ⟨((S k).equivFin ⟨v, h.1⟩).val, lt_of_lt_of_le (Fin.isLt _) (hcard k h.2)⟩
    else ⟨0, hpos⟩
  have henc : ∀ k ≤ N, ∀ x y, enc k (F k x) = enc k (F k y) → F k x = F k y := by
    intro k hk x y h
    simp only [enc, dite_eq_left (And.intro (hS k hk x) hk),
      dite_eq_left (And.intro (hS k hk y) hk), Fin.mk.injEq] at h
    exact congrArg Subtype.val ((S k).equivFin.injective (Fin.ext h))
  obtain ⟨x0⟩ := ‹Nonempty X›
  let step : Fin N → Fin (2 ^ b) → Bool → Fin (2 ^ b) := fun k st bit =>
    if h : ∃ x, enc k (F k x) = st ∧ rd k x = bit then enc (k + 1) (F (k + 1) h.choose)
    else ⟨0, hpos⟩
  let out : Fin (2 ^ b) → Bool := fun st =>
    if h : ∃ x, enc N (F N x) = st then fin (F N h.choose) else false
  refine ⟨enc 0 (F 0 x0), step, out, fun x => ?_⟩
  have key : ∀ k (hk : k ≤ N), ((List.finRange N).take k).foldl
      (fun st k => step k st (rd k x)) (enc 0 (F 0 x0)) = enc k (F k x) := by
    intro k hk
    induction k with
    | zero => simp [h0 x0 x]
    | succ k ih =>
      have hk' : k < N := hk
      rw [List.take_add_one, List.foldl_append, ih hk'.le,
        List.getElem?_eq_getElem (by simpa using hk'), List.getElem_finRange]
      simp only [Option.toList_some, List.foldl_cons, List.foldl_nil, Fin.cast_mk]
      have hex : ∃ y, enc k (F k y) = enc k (F k x) ∧ rd ⟨k, hk'⟩ y = rd ⟨k, hk'⟩ x :=
        ⟨x, rfl, rfl⟩
      simp only [step, dite_eq_left hex]
      have hy := hex.choose_spec
      have := hstep ⟨k, hk'⟩ _ _ (henc k hk'.le _ _ hy.1) hy.2
      rw [this]
  have hfull := key N le_rfl
  rw [List.take_of_length_le (by simp)] at hfull
  rw [hfull]
  have hex : ∃ y, enc N (F N y) = enc N (F N x) := ⟨x, rfl⟩
  simp only [out, dite_eq_left hex, henc N le_rfl _ _ hex.choose_spec]

lemma sum_sq_sample (n : ℕ) (Z : Fin n → ℤ) (hZ : ∑ i, Z i = 0) : ∀ m : ℕ,
    (n : ℤ) * ∑ s : Fin m → Fin n, (∑ l, Z (s l)) ^ 2 = m * n ^ m * ∑ i, Z i ^ 2
  | 0 => by simp
  | m + 1 => by
    rw [← (Fin.consEquiv fun _ => Fin n).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_sq,
      sum_add_distrib, ← mul_sum, ← sum_mul, sum_const,
      card_univ, Fintype.card_fun, Fintype.card_fin, hZ, nsmul_eq_mul]
    have ih := sum_sq_sample n Z hZ m
    push_cast
    linear_combination (n : ℤ) * ih

lemma cheb (n m g : ℕ) (P : Fin n → Prop) [DecidablePred P] (hn : 0 < n) (hm : 0 < m)
    (hmg : 5 * n ^ 2 ≤ m * g ^ 2) :
    20 * (univ.filter (fun s : Fin m → Fin n => ((m : ℤ) * g) ^ 2 ≤
      ((n : ℤ) * (univ.filter (fun l => P (s l))).card - m * (univ.filter P).card) ^ 2)).card
      ≤ n ^ m := by
  set D := (univ.filter P).card
  set Z : Fin n → ℤ := fun i => n * (if P i then 1 else 0) - D
  have hsum : ∀ {k : ℕ} (f : Fin k → Fin n), ∑ l, Z (f l) =
      n * (univ.filter (fun l => P (f l))).card - k * D := by
    intro k f
    simp only [Z, sum_sub_distrib, ← mul_sum, sum_boole, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hZ : ∑ i, Z i = 0 := by
    have := hsum (id : Fin n → Fin n)
    simp only [id] at this
    rw [this]; ring
  have hZ2 : ∑ i, Z i ^ 2 = n * D * (n - D) := by
    have : ∀ i, Z i ^ 2 = ((n : ℤ) ^ 2 - 2 * n * D) * (if P i then 1 else 0) + (D : ℤ) ^ 2 := by
      intro i; simp only [Z]; split_ifs <;> ring
    simp only [this, sum_add_distrib, ← mul_sum, sum_boole,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hid := sum_sq_sample n Z hZ m
  simp only [hsum] at hid
  rw [hZ2] at hid
  set bad := univ.filter (fun s : Fin m → Fin n => ((m : ℤ) * g) ^ 2 ≤
      ((n : ℤ) * (univ.filter (fun l => P (s l))).card - m * D) ^ 2)
  have hmk : (bad.card : ℤ) * ((m : ℤ) * g) ^ 2 ≤
      ∑ s : Fin m → Fin n, ((n : ℤ) * (univ.filter (fun l => P (s l))).card - m * D) ^ 2 := by
    calc (bad.card : ℤ) * ((m : ℤ) * g) ^ 2 = bad.card • (((m : ℤ) * g) ^ 2) := by
          rw [nsmul_eq_mul]
      _ ≤ ∑ s ∈ bad, ((n : ℤ) * (univ.filter (fun l => P (s l))).card - m * D) ^ 2 :=
          card_nsmul_le_sum _ _ _ (fun s hs => (mem_filter.1 hs).2)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _)
          (fun _ _ _ => sq_nonneg _)
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  have hmg' : (5 : ℤ) * n ^ 2 ≤ m * g ^ 2 := by exact_mod_cast hmg
  have h4 : 4 * (D : ℤ) * (n - D) ≤ (n : ℤ) ^ 2 := by nlinarith [sq_nonneg ((n : ℤ) - 2 * D)]
  have e1 : (n : ℤ) * (bad.card * ((m : ℤ) * g) ^ 2) ≤ m * n ^ m * (n * D * (n - D)) := by
    rw [← hid]; exact mul_le_mul_of_nonneg_left hmk hnz.le
  have e2 : (n : ℤ) * bad.card * m * (5 * n ^ 2) ≤ (n : ℤ) * bad.card * m * (m * g ^ 2) :=
    mul_le_mul_of_nonneg_left hmg' (by positivity)
  have e3 : (m : ℤ) * n ^ m * n * (4 * D * (n - D)) ≤ (m : ℤ) * n ^ m * n * n ^ 2 :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have key : (20 : ℤ) * bad.card * (m * n ^ 2 * n) ≤ (n : ℤ) ^ m * (m * n ^ 2 * n) := by
    nlinarith
  have : (20 : ℤ) * bad.card ≤ (n : ℤ) ^ m :=
    le_of_mul_le_mul_right key (by positivity)
  exact_mod_cast this

lemma pow_le_two_pow (n t N Q : ℕ) (hn : 0 < n) (h : N * t ≤ 20 * n * Q) :
    (n + t) ^ N ≤ 2 ^ (40 * Q) * n ^ N := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : (N : ℝ) * (t / n) ≤ 20 * Q := by
    rw [mul_div_assoc', div_le_iff₀ hnR]
    have : ((N * t : ℕ) : ℝ) ≤ ((20 * n * Q : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith
  have h1 : ((n : ℝ) + t) ^ N ≤ n ^ N * Real.exp (N * (t / n)) := by
    rw [Real.exp_nat_mul, ← mul_pow]
    gcongr
    have := Real.add_one_le_exp (t / n)
    rw [mul_comm, ← div_le_iff₀ hnR, add_div, div_self hnR.ne']
    linarith
  have h2 : Real.exp (N * (t / n)) ≤ 2 ^ (40 * Q) := by
    calc Real.exp (N * (t / n)) ≤ Real.exp (((20 * Q : ℕ) : ℝ) * 1) := by
          apply Real.exp_le_exp.2; push_cast; linarith
      _ = Real.exp 1 ^ (20 * Q) := Real.exp_nat_mul 1 _
      _ ≤ (2 ^ 2) ^ (20 * Q) := by
          gcongr; linarith [Real.exp_one_lt_d9]
      _ = 2 ^ (40 * Q) := by rw [← pow_mul]; ring_nf
  have : ((n : ℝ) + t) ^ N ≤ 2 ^ (40 * Q) * n ^ N := by
    calc ((n : ℝ) + t) ^ N ≤ n ^ N * Real.exp (N * (t / n)) := h1
      _ ≤ n ^ N * 2 ^ (40 * Q) := by gcongr
      _ = 2 ^ (40 * Q) * n ^ N := mul_comm _ _
  exact_mod_cast this

lemma pinned_count (n t m K0 : ℕ) (l : Fin m) (a : Fin n) (L : Finset (Fin n))
    (hL : L.card ≤ t) :
    (univ.filter fun s : Fin m → Fin n =>
      s l = a ∧ K0 < (univ.filter fun l' => s l' ∈ L).card).card * 2 ^ K0 ≤ (n + t) ^ (m - 1) := by
  classical
  set w : Fin n → ℕ := fun b => if b ∈ L then 2 else 1
  set A := univ.filter fun s : Fin m → Fin n =>
    s l = a ∧ K0 < (univ.filter fun l' => s l' ∈ L).card
  set T : Fin m → Finset (Fin n) := fun l' => if l' = l then {a} else univ
  have hpow : ∀ s : Fin m → Fin n,
      2 ^ (univ.filter fun l' => s l' ∈ L).card = ∏ l', w (s l') := fun s => by
    rw [← prod_const, prod_filter]
  have hpin : (univ.filter fun s : Fin m → Fin n => s l = a) = Fintype.piFinset T := by
    ext s
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, T]
    refine ⟨fun h l' => ?_, fun h => by simpa using h l⟩
    split_ifs with hl
    · simp [hl, h]
    · exact mem_univ _
  have hw : ∑ b, w b ≤ n + t := by
    have : ∀ b, w b = 1 + if b ∈ L then 1 else 0 := fun b => by simp only [w]; split_ifs <;> rfl
    simp only [this, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one, sum_boole, Nat.cast_id, filter_mem_eq_inter, univ_inter]
    omega
  have hwa : w a ≤ 2 := by simp only [w]; split_ifs <;> norm_num
  have hprod : ∏ l', ∑ b ∈ T l', w b ≤ 2 * (n + t) ^ (m - 1) := by
    rw [← mul_prod_erase univ _ (mem_univ l)]
    have : ∏ l' ∈ univ.erase l, ∑ b ∈ T l', w b = (∑ b, w b) ^ (m - 1) := by
      rw [prod_congr rfl fun l' hl' => by
          rw [show T l' = univ from ite_eq_right (ne_of_mem_erase hl')],
        prod_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    rw [this, show T l = {a} from ite_eq_left rfl, sum_singleton]
    exact Nat.mul_le_mul hwa (Nat.pow_le_pow_left hw _)
  have h1 : A.card * 2 ^ (K0 + 1) ≤ ∑ s ∈ A, ∏ l', w (s l') := by
    rw [← smul_eq_mul]
    refine card_nsmul_le_sum A _ _ fun s hs => ?_
    rw [← hpow]
    exact Nat.pow_le_pow_right two_pos (mem_filter.1 hs).2.2
  have h2 : ∑ s ∈ A, ∏ l', w (s l') ≤ ∏ l', ∑ b ∈ T l', w b := by
    rw [prod_univ_sum, ← hpin]
    exact sum_le_sum_of_subset_of_nonneg (fun s hs => by simp [(mem_filter.1 hs).2.1])
      (fun _ _ _ => Nat.zero_le _)
  have := h1.trans (h2.trans hprod)
  rw [pow_succ] at this
  linarith

lemma decide_right {n m g D c : ℕ} (hn : 0 < n)
    (hacc : ¬ ((m : ℤ) * g) ^ 2 ≤ ((n : ℤ) * c - m * D) ^ 2) :
    (15 * n + 32 * g ≤ 32 * D ∧ 32 * D + 32 * g ≤ 17 * n → 15 * m ≤ 32 * c ∧ 32 * c ≤ 17 * m) ∧
    (32 * D + 32 * g ≤ 15 * n ∨ 17 * n + 32 * g ≤ 32 * D →
      ¬ (15 * m ≤ 32 * c ∧ 32 * c ≤ 17 * m)) := by
  obtain ⟨h1, h2⟩ := abs_lt.1 (abs_lt_of_sq_lt_sq (not_le.1 hacc) (by positivity))
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hm' : (0 : ℤ) ≤ m := by positivity
  zify
  refine ⟨fun ⟨y1, y2⟩ => ⟨?_, ?_⟩, fun y ⟨d1, d2⟩ => y.elim (fun y => ?_) (fun y => ?_)⟩
  · nlinarith [mul_le_mul_of_nonneg_left y1 hm']
  · nlinarith [mul_le_mul_of_nonneg_left y2 hm']
  · nlinarith [mul_le_mul_of_nonneg_left y hm', mul_le_mul_of_nonneg_left d1 hn'.le]
  · nlinarith [mul_le_mul_of_nonneg_left y hm', mul_le_mul_of_nonneg_left d2 hn'.le]

section Reader

variable {n : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (order : Fin (2 * n) ≃ Bool × Fin n)

abbrev live (j : Fin 3) (k : ℕ) (i : Fin n) : Prop :=
  ¬ ((order.symm (false, i)).val < k ↔ (order.symm (true, M j i)).val < k)

abbrev done (j : Fin 3) (k : ℕ) (i : Fin n) : Prop :=
  (order.symm (false, i)).val < k ∧ (order.symm (true, M j i)).val < k

def readEnd (j : Fin 3) (k : ℕ) (i : Fin n) : Bool × Fin n :=
  if (order.symm (false, i)).val < k then (false, i) else (true, M j i)

def needed (S : Finset (Fin n)) (k : ℕ) : Finset (Bool × Fin n) :=
  univ.biUnion fun j => (S.filter (live M order j k)).image (readEnd M order j k)

def tally {m : ℕ} (s : Fin m → Fin n) (k : ℕ) (x : Bool × Fin n → Bool) (j : Fin 3) : ℕ :=
  (univ.filter fun l => done M order j k (s l) ∧ x (false, s l) ≠ x (true, M j (s l))).card

def summary {m : ℕ} (s : Fin m → Fin n) (k : ℕ) (x : Bool × Fin n → Bool) :
    Finset (Bool × Fin n) × (Fin 3 → ℕ) :=
  ((needed M order (univ.image s) k).filter (fun v => x v = true), tally M order s k x)

lemma val_symm_ne (j : Fin 3) (i : Fin n) :
    (order.symm (false, i)).val ≠ (order.symm (true, M j i)).val := by
  intro h
  have := order.symm.injective (Fin.ext h)
  simp at this

lemma eq_of_val_symm {k : ℕ} (hk : k < 2 * n) {v : Bool × Fin n}
    (h : (order.symm v).val = k) : v = order ⟨k, hk⟩ :=
  (Equiv.symm_apply_eq order).1 (Fin.ext h)

lemma needed_succ (S : Finset (Fin n)) {k : ℕ} (hk : k < 2 * n) {v : Bool × Fin n}
    (hv : v ∈ needed M order S (k + 1)) (hne : v ≠ order ⟨k, hk⟩) : v ∈ needed M order S k := by
  simp only [needed, mem_biUnion, mem_image, mem_filter, mem_univ, true_and] at hv ⊢
  obtain ⟨j, i, ⟨hiS, hl⟩, rfl⟩ := hv
  have hvk : (order.symm (readEnd M order j (k + 1) i)).val ≠ k :=
    fun h => hne (eq_of_val_symm order hk h)
  have := val_symm_ne M order j i
  refine ⟨j, i, ⟨hiS, ?_⟩, ?_⟩ <;> unfold live readEnd at * <;> split_ifs at hvk ⊢ <;>
    first | omega | rfl

lemma agree_of_done (S : Finset (Fin n)) (j : Fin 3) {i : Fin n} (hi : i ∈ S) {k : ℕ}
    (hk : k < 2 * n) (h1 : done M order j (k + 1) i) (h2 : ¬ done M order j k i)
    {x y : Bool × Fin n → Bool} (hE : ∀ v ∈ needed M order S k, x v = y v)
    (hxy : x (order ⟨k, hk⟩) = y (order ⟨k, hk⟩)) :
    x (false, i) = y (false, i) ∧ x (true, M j i) = y (true, M j i) := by
  have hne := val_symm_ne M order j i
  have hl : live M order j k i := by unfold live; unfold done at h1 h2; omega
  have hmem : readEnd M order j k i ∈ needed M order S k := by
    simp only [needed, mem_biUnion, mem_image, mem_filter, mem_univ, true_and]
    exact ⟨j, i, ⟨hi, hl⟩, rfl⟩
  unfold readEnd at hmem
  unfold done at h1 h2
  by_cases ha : (order.symm (false, i)).val < k
  · rw [ite_eq_left ha] at hmem
    rw [eq_of_val_symm order hk (show (order.symm (true, M j i)).val = k by omega)]
    exact ⟨hE _ hmem, hxy⟩
  · rw [ite_eq_right ha] at hmem
    rw [eq_of_val_symm order hk (show (order.symm (false, i)).val = k by omega)]
    exact ⟨hxy, hE _ hmem⟩

lemma tally_succ {m : ℕ} (s : Fin m → Fin n) (k : ℕ) (x : Bool × Fin n → Bool) (j : Fin 3) :
    tally M order s (k + 1) x j = tally M order s k x j +
      (univ.filter fun l => (done M order j (k + 1) (s l) ∧ ¬ done M order j k (s l)) ∧
        x (false, s l) ≠ x (true, M j (s l))).card := by
  unfold tally
  rw [← card_union_of_disjoint]
  · congr 1
    ext l
    have : done M order j k (s l) → done M order j (k + 1) (s l) := by
      unfold done; omega
    simp only [mem_union, mem_filter, mem_univ, true_and]
    tauto
  · exact disjoint_filter.2 fun l _ h1 h2 => h2.1.2 h1.1

lemma summary_step {m : ℕ} (s : Fin m → Fin n) {k : ℕ} (hk : k < 2 * n)
    {x y : Bool × Fin n → Bool} (h : summary M order s k x = summary M order s k y)
    (hxy : x (order ⟨k, hk⟩) = y (order ⟨k, hk⟩)) :
    summary M order s (k + 1) x = summary M order s (k + 1) y := by
  simp only [summary, Prod.mk.injEq] at h ⊢
  obtain ⟨hf, ht⟩ := h
  have hE : ∀ v ∈ needed M order (univ.image s) k, x v = y v := by
    intro v hv
    have := congrArg (v ∈ ·) hf
    simp only [mem_filter, hv, true_and, eq_iff_iff] at this
    exact Bool.eq_iff_iff.2 this
  refine ⟨filter_congr fun v hv => ?_, funext fun j => ?_⟩
  · by_cases hv' : v = order ⟨k, hk⟩
    · rw [hv', hxy]
    · rw [hE v (needed_succ M order _ hk hv hv')]
  · rw [tally_succ, tally_succ, congrFun ht j]
    congr 1
    refine congrArg card (filter_congr fun l _ => and_congr_right fun hd => ?_)
    obtain ⟨e1, e2⟩ := agree_of_done M order _ j (mem_image_of_mem s (mem_univ l)) hk hd.1 hd.2
      hE hxy
    rw [e1, e2]

lemma summary_zero {m : ℕ} (s : Fin m → Fin n) (x y : Bool × Fin n → Bool) :
    summary M order s 0 x = summary M order s 0 y := by
  have hE : needed M order (univ.image s) 0 = ∅ := by
    ext v; simp [needed]
  exact Prod.ext (by simp [summary, hE]) (funext fun j => by simp [summary, tally, done])

lemma tally_le {m : ℕ} (s : Fin m → Fin n) (k : ℕ) (x : Bool × Fin n → Bool) (j : Fin 3) :
    tally M order s k x j ≤ m :=
  (card_filter_le _ _).trans (by simp)

lemma tally_final {m : ℕ} (s : Fin m → Fin n) (x : Bool × Fin n → Bool) (j : Fin 3) :
    tally M order s (2 * n) x j =
      (univ.filter fun l => x (false, s l) ≠ x (true, M j (s l))).card := by
  unfold tally done
  congr 1
  exact filter_congr fun l _ => by simp

lemma needed_card (S : Finset (Fin n)) (k K : ℕ)
    (hK : ∀ j, (S.filter (live M order j k)).card ≤ K) : (needed M order S k).card ≤ 3 * K :=
  calc (needed M order S k).card
      ≤ ∑ j : Fin 3, ((S.filter (live M order j k)).image (readEnd M order j k)).card :=
        card_biUnion_le
    _ ≤ ∑ _j : Fin 3, K := sum_le_sum fun j _ => card_image_le.trans (hK j)
    _ = 3 * K := by simp

lemma seed_reader {m : ℕ} (s : Fin m → Fin n) (K : ℕ) :
    ∃ (init : Fin (2 ^ (3 * K + 3 * Nat.clog 2 (m + 1))))
      (step : Fin (2 * n) → Fin (2 ^ (3 * K + 3 * Nat.clog 2 (m + 1))) → Bool →
        Fin (2 ^ (3 * K + 3 * Nat.clog 2 (m + 1))))
      (out : Fin (2 ^ (3 * K + 3 * Nat.clog 2 (m + 1))) → Bool),
      (∀ j, ∀ k ≤ 2 * n, ((univ.image s).filter (live M order j k)).card ≤ K) →
      ∀ x : Bool × Fin n → Bool,
        out ((List.finRange (2 * n)).foldl (fun st k => step k st (x (order k))) init) =
          decide (∀ j,
            15 * m ≤ 32 * (univ.filter fun l => x (false, s l) ≠ x (true, M j (s l))).card ∧
            32 * (univ.filter fun l => x (false, s l) ≠ x (true, M j (s l))).card ≤ 17 * m) := by
  by_cases hK : ∀ j, ∀ k ≤ 2 * n, ((univ.image s).filter (live M order j k)).card ≤ K
  swap
  · exact ⟨⟨0, Nat.pow_pos two_pos⟩, fun _ st _ => st, fun _ => false, fun h => absurd h hK⟩
  obtain ⟨init, step, out, h⟩ := automaton (fun k (x : Bool × Fin n → Bool) => x (order k))
    (summary M order s)
    (fun k => (needed M order (univ.image s) k).powerset ×ˢ
      Fintype.piFinset fun _ : Fin 3 => range (m + 1))
    (fun k _ x => mem_product.2 ⟨mem_powerset.2 (filter_subset _ _),
      Fintype.mem_piFinset.2 fun j => mem_range.2 (Nat.lt_succ_of_le (tally_le M order s k x j))⟩)
    (fun k hk => by
      rw [card_product, card_powerset, Fintype.card_piFinset, prod_const, card_range, card_univ,
        Fintype.card_fin, pow_add]
      exact Nat.mul_le_mul
        (Nat.pow_le_pow_right two_pos (needed_card M order _ k K fun j => hK j k hk))
        ((Nat.pow_le_pow_left (Nat.le_pow_clog one_lt_two _) 3).trans_eq
          (by rw [← pow_mul, mul_comm])))
    (summary_zero M order s)
    (fun k x y h hxy => summary_step M order s k.isLt h hxy)
    (fun β => decide (∀ j, 15 * m ≤ 32 * β.2 j ∧ 32 * β.2 j ≤ 17 * m))
  exact ⟨init, step, out, fun _ x => by rw [h x]; simp only [summary, tally_final]⟩

lemma overload {m : ℕ} (t K0 : ℕ)
    (hw : ∀ (k : ℕ) (j : Fin 3), k ≤ 2 * n → (univ.filter (live M order j k)).card ≤ t) :
    (univ.filter fun s : Fin m → Fin n => ∃ j, ∃ k ≤ 2 * n,
      K0 < (univ.filter fun l => live M order j k (s l)).card).card * 2 ^ K0 ≤
      3 * m * n * (n + t) ^ (m - 1) := by
  set start : Fin 3 → Fin n → ℕ := fun j i =>
    min (order.symm (false, i)).val (order.symm (true, M j i)).val + 1
  have hsub : (univ.filter fun s : Fin m → Fin n => ∃ j, ∃ k ≤ 2 * n,
      K0 < (univ.filter fun l => live M order j k (s l)).card) ⊆
      univ.biUnion fun j => univ.biUnion fun l => univ.biUnion fun a =>
        univ.filter fun s : Fin m → Fin n => s l = a ∧
          K0 < (univ.filter fun l' => s l' ∈ univ.filter (live M order j (start j a))).card := by
    intro s hs
    obtain ⟨j, k, -, hK⟩ := (mem_filter.1 hs).2
    obtain ⟨l, hl, hmax⟩ := exists_max_image (univ.filter fun l => live M order j k (s l))
      (fun l => start j (s l)) (card_pos.1 (by omega))
    simp only [mem_biUnion, mem_univ, true_and, mem_filter]
    refine ⟨j, l, s l, rfl, hK.trans_le (card_le_card fun l' hl' => ?_)⟩
    have h1 := hmax l' hl'
    simp only [mem_filter, mem_univ, true_and, start, live] at hl hl' h1 ⊢
    omega
  calc _ ≤ (∑ j : Fin 3, ∑ l : Fin m, ∑ a : Fin n, (univ.filter fun s : Fin m → Fin n =>
          s l = a ∧ K0 < (univ.filter fun l' =>
            s l' ∈ univ.filter (live M order j (start j a))).card).card) * 2 ^ K0 := by
        gcongr
        exact (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum fun j _ =>
          card_biUnion_le.trans (sum_le_sum fun l _ => card_biUnion_le)))
    _ ≤ ∑ _j : Fin 3, ∑ _l : Fin m, ∑ _a : Fin n, (n + t) ^ (m - 1) := by
        simp only [sum_mul]
        refine sum_le_sum fun j _ => sum_le_sum fun l _ => sum_le_sum fun a _ =>
          pinned_count n t m K0 l a _ (hw _ j ?_)
        have := (order.symm (false, a)).isLt
        simp only [start]
        omega
    _ = 3 * m * n * (n + t) ^ (m - 1) := by simp; ring

end Reader

lemma main : ∃ C : ℕ, 0 < C ∧ ∀ (n g : ℕ), 0 < g →
  let V := Bool × Fin n
  ∀ (M : Fin 3 → Equiv.Perm (Fin n)) (order : Fin (2*n) ≃ V) (t : ℕ),
    (∀ (k : ℕ) (j : Fin 3), k ≤ 2*n →
      (Finset.univ.filter (fun i : Fin n =>
        ¬ ((order.symm (false,i)).val < k ↔ (order.symm (true,M j i)).val < k))).card ≤ t) →
    ∃ b R : ℕ, b ≤ C*(1 + Nat.clog 2 (1+n/g) + min t (n*t/(g*g))) ∧ 0 < R ∧
      ∃ (init : Fin R → Fin (2^b)) (step : Fin R → Fin (2*n) → Fin (2^b) → Bool → Fin (2^b))
        (out : Fin R → Fin (2^b) → Bool),
        ∀ x : V → Bool,
          let D := fun j : Fin 3 => (Finset.univ.filter (fun i : Fin n =>
            x (false,i) ≠ x (true,M j i))).card
          let yes := ∀ j : Fin 3, 15*n + 32*g ≤ 32*D j ∧ 32*D j + 32*g ≤ 17*n
          let no := ∃ j : Fin 3, 32*D j + 32*g ≤ 15*n ∨ 17*n + 32*g ≤ 32*D j
          let answer := fun seed : Fin R => out seed ((List.finRange (2*n)).foldl
            (fun st k => step seed k st (x (order k))) (init seed))
          2*R ≤ 3*(Finset.univ.filter (fun seed : Fin R =>
            (yes → answer seed = true) ∧ (no → answer seed = false))).card := by
  refine ⟨200, by norm_num, ?_⟩
  intro n g hg V M order t hw
  by_cases htriv : 15 * n < 32 * g
  ·
    refine ⟨0, 1, Nat.zero_le _, one_pos, fun _ => 0, fun _ _ st _ => st, fun _ _ => true,
      fun x => ?_⟩
    have hD : ∀ j, (univ.filter fun i : Fin n => x (false, i) ≠ x (true, M j i)).card ≤ n :=
      fun j => (card_filter_le _ _).trans (by simp)
    dsimp only
    rw [filter_true_of_mem fun seed _ => ⟨fun hy => by have := hy 0; have := hD 0; omega,
      fun ⟨j, hj⟩ => by have := hD j; omega⟩]
    simp
  have hn : 0 < n := by omega

  obtain ⟨a, ha⟩ : ∃ a, a = n / g + 1 := ⟨_, rfl⟩
  have ha1 : n < a * g := by rw [ha, add_mul, one_mul]; exact Nat.lt_div_mul_add hg
  have ha2 : a * g ≤ 2 * n := by
    have := (Nat.one_le_div_iff hg).2 (show g ≤ n by omega)
    have := Nat.div_mul_le_self n g
    rw [ha]; nlinarith
  generalize hL : Nat.clog 2 (1 + n / g) = L
  generalize hq : n * t / (g * g) = q
  have haL : a ^ 2 ≤ 2 ^ (2 * L) := by
    rw [pow_mul', ← hL, ha, add_comm]; exact Nat.pow_le_pow_left (Nat.le_pow_clog one_lt_two _) 2
  have ha0 : 1 ≤ a ^ 2 := Nat.one_le_pow _ _ (by rw [ha]; exact Nat.succ_pos _)
  have hq1 : n * t < (q + 1) * (g * g) := by
    rw [← hq, add_mul, one_mul]; exact Nat.lt_div_mul_add (by positivity)
  obtain ⟨m, hm⟩ : ∃ m, m = 5 * a ^ 2 := ⟨_, rfl⟩
  have hm1 : m + 1 ≤ 2 ^ (2 * L + 3) := by
    rw [show 2 ^ (2 * L + 3) = 8 * 2 ^ (2 * L) by ring]; omega
  have hcL : Nat.clog 2 (m + 1) ≤ 2 * L + 3 := Nat.clog_le_of_le_pow hm1
  obtain ⟨K0, hK0⟩ : ∃ K0, K0 = 40 * (q + 1) + 2 * L + 7 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = min t K0 := ⟨_, rfl⟩
  refine ⟨3 * K + 3 * Nat.clog 2 (m + 1), n ^ m, by omega, Nat.pow_pos hn, ?_⟩
  set e : Fin (n ^ m) ≃ (Fin m → Fin n) := (Fintype.equivFinOfCardEq (by simp)).symm

  choose init step out hspec using fun s : Fin m → Fin n => seed_reader M order s K
  refine ⟨fun r => init (e r), fun r => step (e r), fun r => out (e r), fun x => ?_⟩
  dsimp only
  have hw' : ∀ (k : ℕ) (j : Fin 3), k ≤ 2 * n → (univ.filter (live M order j k)).card ≤ t := hw

  obtain ⟨B, hBd⟩ : ∃ B : Finset (Fin m → Fin n), B = univ.filter fun s =>
      ¬ ∀ j, ∀ k ≤ 2 * n, ((univ.image s).filter (live M order j k)).card ≤ K := ⟨_, rfl⟩
  obtain ⟨I, hId⟩ : ∃ I : Fin 3 → Finset (Fin m → Fin n), I = fun j => univ.filter fun s =>
      ((m : ℤ) * g) ^ 2 ≤
        ((n : ℤ) * (univ.filter fun l => x (false, s l) ≠ x (true, M j (s l))).card -
          m * (univ.filter fun i : Fin n => x (false, i) ≠ x (true, M j i)).card) ^ 2 := ⟨_, rfl⟩
  have hB : 6 * B.card ≤ n ^ m := by
    have hsub : B ⊆ univ.filter fun s : Fin m → Fin n => ∃ j, ∃ k ≤ 2 * n,
        K0 < (univ.filter fun l => live M order j k (s l)).card := by
      intro s hs
      simp only [hBd, mem_filter, mem_univ, true_and, not_forall, not_le] at hs ⊢
      obtain ⟨j, k, hk, hlt⟩ := hs
      have h1 : ((univ.image s).filter (live M order j k)).card ≤ t :=
        (card_le_card (filter_subset_filter _ (subset_univ _))).trans (hw' k j hk)
      have h2 : ((univ.image s).filter (live M order j k)).card ≤
          (univ.filter fun l => live M order j k (s l)).card := by
        rw [filter_image]; exact card_image_le
      exact ⟨j, k, hk, by omega⟩
    have hmt : (m - 1) * t ≤ 20 * n * (q + 1) := by
      have : m * t * (g * g) ≤ 20 * n * (q + 1) * (g * g) :=
        calc m * t * (g * g) = 5 * (a * g) ^ 2 * t := by rw [hm]; ring
          _ ≤ 5 * (2 * n) ^ 2 * t := by gcongr
          _ = 20 * n * (n * t) := by ring
          _ ≤ 20 * n * ((q + 1) * (g * g)) := by gcongr
          _ = 20 * n * (q + 1) * (g * g) := by ring
      exact (Nat.mul_le_mul_right t (Nat.sub_le m 1)).trans
        (Nat.le_of_mul_le_mul_right this (by positivity))
    have h18 : 18 * m ≤ 2 ^ (2 * L + 7) := by
      rw [hm, show 2 ^ (2 * L + 7) = 128 * 2 ^ (2 * L) by ring]; omega
    obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have key : 6 * B.card * 2 ^ K0 ≤ n ^ m * 2 ^ K0 :=
      calc 6 * B.card * 2 ^ K0 ≤ 6 * ((univ.filter fun s : Fin m → Fin n => ∃ j, ∃ k ≤ 2 * n,
            K0 < (univ.filter fun l => live M order j k (s l)).card).card * 2 ^ K0) := by
            rw [← mul_assoc]; gcongr
        _ ≤ 6 * (3 * m * n * (n + t) ^ (m - 1)) :=
            Nat.mul_le_mul_left 6 (overload M order t K0 hw')
        _ = 18 * m * (n * (n + t) ^ (m - 1)) := by ring
        _ ≤ 2 ^ (2 * L + 7) * (n * (2 ^ (40 * (q + 1)) * n ^ (m - 1))) := by
            gcongr; exact pow_le_two_pow n t (m - 1) (q + 1) hn hmt
        _ = n ^ m * 2 ^ K0 := by rw [hK0, hm', Nat.add_sub_cancel, pow_succ]; ring
    exact Nat.le_of_mul_le_mul_right key (Nat.pow_pos two_pos)
  have hI : ∀ j, 20 * (I j).card ≤ n ^ m := fun j => by
    rw [hId]
    exact cheb n m g (fun i => x (false, i) ≠ x (true, M j i)) hn (by omega) (by
      rw [hm, show 5 * a ^ 2 * g ^ 2 = 5 * (a * g) ^ 2 by ring]
      exact Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left ha1.le 2))
  obtain ⟨G, hGd⟩ : ∃ G : Finset (Fin m → Fin n),
      G = univ.filter fun s => s ∉ B ∧ ∀ j, s ∉ I j := ⟨_, rfl⟩
  have hcover : n ^ m ≤ G.card + (B.card + ∑ j, (I j).card) := by
    have hsub : (univ : Finset (Fin m → Fin n)) ⊆ G ∪ (B ∪ univ.biUnion I) := by
      intro s _
      by_cases h1 : s ∈ B
      · exact mem_union_right _ (mem_union_left _ h1)
      by_cases h2 : ∃ j, s ∈ I j
      · obtain ⟨j, hj⟩ := h2
        exact mem_union_right _ (mem_union_right _ (mem_biUnion.2 ⟨j, mem_univ _, hj⟩))
      simp only [not_exists] at h2
      exact mem_union_left _ (hGd ▸ mem_filter.2 ⟨mem_univ _, h1, h2⟩)
    have := card_le_card hsub
    rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at this
    exact this.trans ((card_union_le _ _).trans (Nat.add_le_add_left
      ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _)) _))
  rw [Fin.sum_univ_three] at hcover
  have := hI 0
  have := hI 1
  have := hI 2

  refine (show 2 * n ^ m ≤ 3 * G.card by omega).trans (Nat.mul_le_mul_left 3
    (card_le_card_of_injOn e.symm (fun s hs => ?_) e.symm.injective.injOn))
  rw [mem_coe, hGd, mem_filter] at hs
  obtain ⟨-, hgood, hacc⟩ := hs
  rw [hBd, mem_filter, not_and, not_not] at hgood
  have hr := fun j => decide_right (m := m) (g := g) hn (by
    have := hacc j
    rw [hId, mem_filter, not_and] at this
    exact this (mem_univ _))
  rw [mem_coe, mem_filter, Equiv.apply_symm_apply, hspec s (hgood (mem_univ _)) x]
  exact ⟨mem_univ _, fun hy => decide_eq_true fun j => (hr j).1 (hy j),
    fun ⟨j, hj⟩ => decide_eq_false fun h => (hr j).2 hj (h j)⟩

end PEqualNP.Outside.L_pcx_335_aux

theorem PEqualNP.Outside.L_pcx_335 : ∃ C : ℕ, 0 < C ∧ ∀ (n g : ℕ), 0 < g →
  let V := Bool × Fin n
  ∀ (M : Fin 3 → Equiv.Perm (Fin n)) (order : Fin (2*n) ≃ V) (t : ℕ),
    (∀ (k : ℕ) (j : Fin 3), k ≤ 2*n →
      (Finset.univ.filter (fun i : Fin n =>
        ¬ ((order.symm (false,i)).val < k ↔ (order.symm (true,M j i)).val < k))).card ≤ t) →
    ∃ b R : ℕ, b ≤ C*(1 + Nat.clog 2 (1+n/g) + min t (n*t/(g*g))) ∧ 0 < R ∧
      ∃ (init : Fin R → Fin (2^b)) (step : Fin R → Fin (2*n) → Fin (2^b) → Bool → Fin (2^b))
        (out : Fin R → Fin (2^b) → Bool),
        ∀ x : V → Bool,
          let D := fun j : Fin 3 => (Finset.univ.filter (fun i : Fin n =>
            x (false,i) ≠ x (true,M j i))).card
          let yes := ∀ j : Fin 3, 15*n + 32*g ≤ 32*D j ∧ 32*D j + 32*g ≤ 17*n
          let no := ∃ j : Fin 3, 32*D j + 32*g ≤ 15*n ∨ 17*n + 32*g ≤ 32*D j
          let answer := fun seed : Fin R => out seed ((List.finRange (2*n)).foldl
            (fun st k => step seed k st (x (order k))) (init seed))
          2*R ≤ 3*(Finset.univ.filter (fun seed : Fin R =>
            (yes → answer seed = true) ∧ (no → answer seed = false))).card :=
  PEqualNP.Outside.L_pcx_335_aux.main
