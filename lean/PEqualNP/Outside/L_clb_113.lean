import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_836

namespace PEqualNP.Outside.L_clb_113_aux

open Classical

private lemma foldl_pat_testBit : ∀ (k : ℕ) (f : ℕ → Bool) (b : ℕ),
    ((List.range k).foldl (fun (acc bit : ℕ) => acc ||| ((f bit).toNat <<< bit)) 0).testBit b =
      if b < k then f b else false
  | 0, f, b => by simp
  | k + 1, f, b => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [Nat.testBit_or, foldl_pat_testBit k f b, Nat.testBit_shiftLeft]
    by_cases hbk : b < k
    · have h1 : b < k + 1 := by omega
      have h2 : ¬ (k ≤ b) := by omega
      simp [hbk, h1, h2]
    · by_cases hbeq : b = k
      · subst hbeq
        simp only [lt_irrefl, ↓reduceIte, Nat.lt_succ_self, le_refl, decide_true, Nat.sub_self,
          Bool.false_or, Bool.true_and]
        cases f b <;> decide
      · have h1 : ¬ (b < k + 1) := by omega
        have hgt : 1 ≤ b - k := by omega
        have htb : (f k).toNat.testBit (b - k) = false := by
          cases f k
          · simp
          · have h2 : (1 : ℕ) < 2 ^ (b - k) := by
              calc (1 : ℕ) < 2 ^ 1 := by decide
                _ ≤ 2 ^ (b - k) := Nat.pow_le_pow_right (by decide) hgt
            exact Nat.testBit_eq_false_of_lt h2
        simp [hbk, h1, htb]

private def wordOf : ∀ {n : ℕ}, (Fin n → Bool) → ℕ
  | 0, _ => 0
  | _ + 1, x => 2 * wordOf (fun i => x i.succ) + (x 0).toNat

private lemma wordOf_lt : ∀ {n : ℕ} (x : Fin n → Bool), wordOf x < 2 ^ n
  | 0, _ => by simp [wordOf]
  | n + 1, x => by
    have ih := wordOf_lt (fun i : Fin n => x i.succ)
    have h0 : (x 0).toNat ≤ 1 := by cases x 0 <;> decide
    dsimp only [wordOf]
    rw [pow_succ']
    omega

private lemma testBit_wordOf : ∀ {n : ℕ} (x : Fin n → Bool) (j : ℕ),
    (wordOf x).testBit j = if h : j < n then x ⟨j, h⟩ else false
  | 0, _, j => by simp [wordOf]
  | n + 1, x, 0 => by
    dsimp only [wordOf]
    rw [dif_pos (Nat.succ_pos n), Nat.testBit_zero]
    cases h0 : x 0 <;> simp [h0, Nat.add_mod, Nat.mul_mod_right]
  | n + 1, x, j + 1 => by
    dsimp only [wordOf]
    rw [Nat.testBit_succ]
    have hdiv : (2 * wordOf (fun i : Fin n => x i.succ) + (x 0).toNat) / 2 =
        wordOf (fun i : Fin n => x i.succ) := by
      have h0 : (x 0).toNat < 2 := by cases x 0 <;> decide
      omega
    rw [hdiv, testBit_wordOf (fun i : Fin n => x i.succ) j]
    by_cases hj : j < n
    · have hj1 : j + 1 < n + 1 := by omega
      simp [hj, hj1]
    · have hj1 : ¬ (j + 1 < n + 1) := by omega
      simp [hj, hj1]

private lemma wordOf_bits : ∀ {n : ℕ} (w : ℕ), w < 2 ^ n →
    wordOf (fun i : Fin n => w.testBit i.val) = w
  | 0, w, hw => by simp [wordOf]; omega
  | n + 1, w, hw => by
    dsimp only [wordOf]
    have hdiv_lt : w / 2 < 2 ^ n := by rw [pow_succ'] at hw; omega
    have hsucc : (fun i : Fin n => w.testBit (i.succ).val) = fun i : Fin n => (w / 2).testBit i.val := by
      funext i
      exact Nat.testBit_succ w i.val
    rw [hsucc, wordOf_bits (w / 2) hdiv_lt]
    have h0 : (w.testBit 0).toNat = w % 2 := by
      rw [Nat.testBit_zero]
      have hmod : w % 2 = 0 ∨ w % 2 = 1 := by omega
      rcases hmod with h | h <;> simp [h]
    rw [Fin.val_zero, h0]
    omega

private lemma wordOf_inj {n : ℕ} : Function.Injective (@wordOf n) := by
  intro x y hxy
  funext i
  have h := congrArg (fun w => w.testBit i.val) hxy
  rw [testBit_wordOf, testBit_wordOf, dif_pos i.isLt, dif_pos i.isLt] at h
  exact h

private lemma list_filter_nodup_eq_card {α : Type*} (L : List α) (hnd : L.Nodup) (p : α → Bool) :
    (L.filter p).length = (L.toFinset.filter (fun x => p x = true)).card := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rcases List.nodup_cons.mp hnd with ⟨hnot, hndL⟩
    rw [List.filter_cons, List.toFinset_cons, Finset.filter_insert]
    have hnotF : a ∉ L.toFinset.filter (fun x => p x = true) := by
      intro hm; exact hnot (List.mem_toFinset.mp (Finset.mem_filter.mp hm).1)
    cases hpa : p a
    · simp [ih hndL]
    · simp [Finset.card_insert_of_notMem hnotF, ih hndL]

private lemma sum_testBit_two_pow : ∀ (q m : ℕ), m < 2 ^ q →
    (∑ bit : Fin q, if m.testBit bit.val then 2 ^ bit.val else 0) = m
  | 0, m, hm => by simp; omega
  | q + 1, m, hm => by
    rw [Fin.sum_univ_succ]
    have hdiv_lt : m / 2 < 2 ^ q := by rw [pow_succ'] at hm; omega
    have ih := sum_testBit_two_pow q (m / 2) hdiv_lt
    have hrest : (∑ i : Fin q, if m.testBit (i.succ).val then 2 ^ (i.succ).val else 0) =
        2 * (∑ i : Fin q, if (m / 2).testBit i.val then 2 ^ i.val else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have htb : m.testBit (i.succ).val = (m / 2).testBit i.val := Nat.testBit_succ m i.val
      rw [htb]
      split_ifs
      · change 2 ^ (i.val + 1) = 2 * 2 ^ i.val; rw [pow_succ']
      · simp
    rw [hrest, ih]
    have h0 : (if m.testBit 0 then 2 ^ 0 else 0) = m % 2 := by
      rw [Nat.testBit_zero]
      have hmod : m % 2 = 0 ∨ m % 2 = 1 := by omega
      rcases hmod with h | h <;> simp [h]
    change (if m.testBit 0 then 2 ^ 0 else 0) + 2 * (m / 2) = m
    rw [h0]
    omega

private lemma hamming_sum_eq : ∀ (N : ℕ) (y : Fin N → Bool),
    (∑ x : Fin N → Bool, (1 / 2 : ℝ) ^ (Finset.univ.filter (fun i : Fin N => x i ≠ y i)).card) =
      (3 / 2 : ℝ) ^ N
  | 0, y => by
    have huniv : (Finset.univ : Finset (Fin 0 → Bool)) = {Fin.elim0} := by
      ext x; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      funext i; exact Fin.elim0 i
    rw [huniv, Finset.sum_singleton]
    simp
  | N + 1, y => by
    let e : (Bool × (Fin N → Bool)) ≃ (Fin (N + 1) → Bool) :=
      { toFun := fun p => Fin.cases p.1 p.2,
        invFun := fun x => (x 0, fun i => x i.succ),
        left_inv := fun p => by
          cases p with
          | mk b g =>
            apply Prod.ext
            · rfl
            · funext i; rfl
        right_inv := fun x => by
          funext i
          refine Fin.cases rfl (fun _ => rfl) i }
    rw [← Equiv.sum_comp e]
    rw [Fintype.sum_prod_type]
    have hcard_split : ∀ (b : Bool) (g : Fin N → Bool),
        (Finset.univ.filter (fun i : Fin (N + 1) => e (b, g) i ≠ y i)).card =
          (if b ≠ y 0 then 1 else 0) +
            (Finset.univ.filter (fun i : Fin N => g i ≠ y i.succ)).card := by
      intro b g
      let Sfull := Finset.univ.filter (fun i : Fin (N + 1) => e (b, g) i ≠ y i)
      let Stail := Finset.univ.filter (fun i : Fin (N + 1) => i ≠ 0 ∧ e (b, g) i ≠ y i)
      have htail_eq : Stail.card = (Finset.univ.filter (fun i : Fin N => g i ≠ y i.succ)).card := by
        refine (Finset.card_bij (fun (i : Fin N) _ => i.succ) ?_ ?_ ?_).symm
        · intro i hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.succ_ne_zero i, (Finset.mem_filter.mp hi).2⟩
        · intro i1 _ i2 _ heq; exact Fin.succ_inj.mp heq
        · intro i hi
          rcases (Finset.mem_filter.mp hi).2 with ⟨hne, hneval⟩
          refine ⟨i.pred hne, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Fin.succ_pred i hne⟩
          have h1 : e (b, g) (i.pred hne).succ = g (i.pred hne) := rfl
          rw [← h1, Fin.succ_pred i hne]
          exact hneval
      by_cases hb : b ≠ y 0
      · rw [if_pos hb]
        have hset : Sfull = insert 0 Stail := by
          ext i
          simp only [Sfull, Stail, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · intro hne
            by_cases hi0 : i = 0
            · exact Or.inl hi0
            · exact Or.inr ⟨hi0, hne⟩
          · rintro (rfl | ⟨_, hne⟩)
            · exact hb
            · exact hne
        have hnot : (0 : Fin (N + 1)) ∉ Stail := by simp [Stail]
        change Sfull.card = 1 + (Finset.univ.filter (fun i : Fin N => g i ≠ y i.succ)).card
        rw [hset, Finset.card_insert_of_notMem hnot, htail_eq, add_comm]
      · rw [if_neg hb, zero_add]
        have hset : Sfull = Stail := by
          ext i
          simp only [Sfull, Stail, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hne
            refine ⟨?_, hne⟩
            rintro rfl; exact hb hne
          · exact fun h => h.2
        change Sfull.card = (Finset.univ.filter (fun i : Fin N => g i ≠ y i.succ)).card
        rw [hset, htail_eq]
    have hsplit : ∀ b : Bool,
        (∑ g : Fin N → Bool, (1 / 2 : ℝ) ^ (Finset.univ.filter (fun i : Fin (N + 1) => e (b, g) i ≠ y i)).card) =
          (if b ≠ y 0 then (1 / 2 : ℝ) else 1) * (3 / 2 : ℝ) ^ N := by
      intro b
      have hrew : ∀ g : Fin N → Bool,
          (1 / 2 : ℝ) ^ (Finset.univ.filter (fun i : Fin (N + 1) => e (b, g) i ≠ y i)).card =
            (if b ≠ y 0 then (1 / 2 : ℝ) else 1) *
              (1 / 2 : ℝ) ^ (Finset.univ.filter (fun i : Fin N => g i ≠ y i.succ)).card := by
        intro g
        rw [hcard_split b g, pow_add]
        split_ifs <;> simp
      simp only [hrew, ← Finset.mul_sum, hamming_sum_eq N (fun i => y i.succ)]
    simp only [hsplit, Fintype.sum_bool]
    cases y 0 <;> norm_num <;> ring

private lemma main_proof :
∀ (d a b L : Nat),
  let w := d+2
  let K := 2^b
  let h := b-3
  let q := h+3*2^a
  let N := (a+h)*4^d
  q*(2*w+(2^w-1)) ≤ L →
    let n := L+w
    let Rows := Nat → Nat → Bool
    let total := fun (left right : Rows) =>
      ((List.range (2^n)).filter (fun word => (List.range n).all (fun site =>
        let pat := (List.range (w+1)).foldl (fun (acc bit : Nat) =>
          acc ||| ((word.testBit ((site+bit) % n)).toNat <<< bit)) 0
        if site < L then left site pat else right (site-L) pat))).length
    let good := fun (c y : Nat) => K*c ≤ (K+1)*y ∧ K*y ≤ (K+1)*c
    (∀ (S : Nat) (send : Rows → Fin S) (answer : Fin S → Rows → Nat),
      (∀ left right : Rows, good (total left right) (answer (send left) right)) → 2^N ≤ S) ∧
    ∀ (S R : Nat), 0 < R →
      ∀ (pack : Fin R → Rows → Fin S) (guess : Fin R → Fin S → Rows → Nat),
        (∀ firstPart lastPart : Rows, 2*R ≤ 3*((List.finRange R).filter (fun coin =>
          good (total firstPart lastPart) (guess coin (pack coin firstPart) lastPart))).length) →
        2^N ≤ S^15 := by
  intro d a b L w K h q N hLbound n Rows total good
  let plane : ℕ := 2 * w + (2 ^ w - 1)
  let L0 : ℕ := q * plane
  let n0 : ℕ := L0 + w
  have hL0_le : L0 ≤ L := hLbound
  have hw_pos : 0 < w := by dsimp only [w]; omega
  have hn0_pos : 0 < n0 := by dsimp only [n0]; omega
  have hn_pos : 0 < n := by dsimp only [n]; omega
  let D := Fin d → Bool
  let E := Fin q × D × D
  let S0 := Fin L0 × (Fin (w + 1) → Bool)
  let loc0 : ℕ → Fin n0 := fun k => ⟨k % n0, Nat.mod_lt _ hn0_pos⟩
  let packW : Bool → D → (Fin w → Bool) := fun tag payload =>
    (Fin.cases tag (Fin.cases false payload) : Fin w → Bool)
  rcases PEqualNP.Outside.L_lib_836 d q with ⟨base, port, hport_inj, hbase_port, hport_plane, hcount836⟩
  -- Define separated weight encoding for Val = Fin (2^a) × Fin (2^h)
  let Val := Fin (2 ^ a) × Fin (2 ^ h)
  let valNat : Val → ℕ := fun v => (2 ^ h + v.2.val) * 8 ^ v.1.val
  have hval_lt : ∀ v : Val, valNat v < 2 ^ q := by
    intro v
    have h2a_pos : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by decide)
    have h1 : 2 ^ h + v.2.val < 2 ^ (h + 1) := by
      have := v.2.isLt
      rw [pow_succ']
      omega
    have h8 : 8 ^ v.1.val = 2 ^ (3 * v.1.val) := by
      have : (8 : ℕ) = 2 ^ 3 := by decide
      rw [this, ← pow_mul]
    have hexp : (h + 1) + 3 * v.1.val ≤ q := by
      have := v.1.isLt
      dsimp only [q]
      omega
    dsimp only [valNat]
    calc (2 ^ h + v.2.val) * 8 ^ v.1.val
        < 2 ^ (h + 1) * 8 ^ v.1.val := Nat.mul_lt_mul_of_pos_right h1 (by positivity)
      _ = 2 ^ ((h + 1) + 3 * v.1.val) := by rw [h8, ← pow_add]
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by decide) hexp
  have hval_sep : ∀ (v1 v2 : Val) (y : ℕ), good (valNat v1) y → good (valNat v2) y → v1 = v2 := by
    have hsep_lt : ∀ v1 v2 : Val, (v1.1.val < v2.1.val ∨ (v1.1.val = v2.1.val ∧ v1.2.val < v2.2.val)) →
        (K + 1) ^ 2 * valNat v1 < K ^ 2 * valNat v2 := by
      intro v1 v2 hord
      rcases hord with he | ⟨heq, hj⟩
      · have h8le : 8 ^ v1.1.val * 8 ≤ 8 ^ v2.1.val := by
          calc 8 ^ v1.1.val * 8 = 8 ^ (v1.1.val + 1) := (pow_succ 8 v1.1.val).symm
            _ ≤ 8 ^ v2.1.val := Nat.pow_le_pow_right (by decide) (by omega)
        by_cases hb0 : b = 0
        · have hh0 : h = 0 := by dsimp only [h]; omega
          have h2h : 2 ^ h = 1 := by rw [hh0]; rfl
          have hK1 : K = 1 := by dsimp only [K]; rw [hb0]; rfl
          have hj1 : v1.2.val = 0 := by have := v1.2.isLt; omega
          have hj2 : v2.2.val = 0 := by have := v2.2.isLt; omega
          have h8pos : 0 < 8 ^ v1.1.val := by positivity
          dsimp only [valNat]
          rw [hj1, hj2, hK1]
          nlinarith
        · have hK2 : 2 ≤ K := by
            dsimp only [K]
            calc 2 = 2 ^ 1 := rfl
              _ ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
          have hKsq : (K + 1) ^ 2 < 4 * K ^ 2 := by nlinarith
          have hmant : 2 ^ h + v1.2.val < 2 * (2 ^ h + v2.2.val) := by
            have := v1.2.isLt; omega
          have h8pos : 0 < 8 ^ v1.1.val := by positivity
          dsimp only [valNat]
          calc (K + 1) ^ 2 * ((2 ^ h + v1.2.val) * 8 ^ v1.1.val)
              < (4 * K ^ 2) * ((2 ^ h + v1.2.val) * 8 ^ v1.1.val) :=
                Nat.mul_lt_mul_of_pos_right hKsq (Nat.mul_pos (by positivity) h8pos)
            _ ≤ (4 * K ^ 2) * (2 * (2 ^ h + v2.2.val) * 8 ^ v1.1.val) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (le_of_lt hmant))
            _ = K ^ 2 * ((2 ^ h + v2.2.val) * (8 ^ v1.1.val * 8)) := by ring
            _ ≤ K ^ 2 * ((2 ^ h + v2.2.val) * 8 ^ v2.1.val) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h8le)
      · have hh_pos : 1 ≤ h := by
          by_contra h0
          have hh0 : h = 0 := by omega
          have h2h : 2 ^ h = 1 := by rw [hh0]; rfl
          have h1 := v1.2.isLt
          have h2 := v2.2.isLt
          omega
        have hb4 : 4 ≤ b := by dsimp only [h] at hh_pos; omega
        have hK8 : K = 8 * 2 ^ h := by
          dsimp only [K, h]
          have : b = (b - 3) + 3 := by omega
          conv_lhs => rw [this, pow_add]
          ring
        have h1 : 4 * (2 ^ h + v1.2.val) < K := by
          have := v1.2.isLt
          omega
        have hKpos : 1 ≤ K := by omega
        have h2 : (2 * K + 1) * (2 ^ h + v1.2.val) < K ^ 2 := by nlinarith
        have h8pos : 0 < 8 ^ v1.1.val := by positivity
        dsimp only [valNat]
        rw [← heq]
        have hstep : (K + 1) ^ 2 * (2 ^ h + v1.2.val) < K ^ 2 * (2 ^ h + v2.2.val) := by nlinarith
        calc (K + 1) ^ 2 * ((2 ^ h + v1.2.val) * 8 ^ v1.1.val)
            = ((K + 1) ^ 2 * (2 ^ h + v1.2.val)) * 8 ^ v1.1.val := by ring
          _ < (K ^ 2 * (2 ^ h + v2.2.val)) * 8 ^ v1.1.val := Nat.mul_lt_mul_of_pos_right hstep h8pos
          _ = K ^ 2 * ((2 ^ h + v2.2.val) * 8 ^ v1.1.val) := by ring
    have hcontra : ∀ v1 v2 y, (v1.1.val < v2.1.val ∨ (v1.1.val = v2.1.val ∧ v1.2.val < v2.2.val)) →
        good (valNat v1) y → good (valNat v2) y → False := by
      intro v1 v2 y hord hg1 hg2
      have hstrict := hsep_lt v1 v2 hord
      have hle : K ^ 2 * valNat v2 ≤ (K + 1) ^ 2 * valNat v1 := by
        calc K ^ 2 * valNat v2 = K * (K * valNat v2) := by ring
          _ ≤ K * ((K + 1) * y) := Nat.mul_le_mul_left K hg2.1
          _ = (K + 1) * (K * y) := by ring
          _ ≤ (K + 1) * ((K + 1) * valNat v1) := Nat.mul_le_mul_left (K + 1) hg1.2
          _ = (K + 1) ^ 2 * valNat v1 := by ring
      omega
    intro v1 v2 y hg1 hg2
    rcases lt_trichotomy v1.1.val v2.1.val with h1 | h1 | h1
    · exact False.elim (hcontra v1 v2 y (Or.inl h1) hg1 hg2)
    · rcases lt_trichotomy v1.2.val v2.2.val with h2 | h2 | h2
      · exact False.elim (hcontra v1 v2 y (Or.inr ⟨h1, h2⟩) hg1 hg2)
      · exact Prod.ext (Fin.ext h1) (Fin.ext h2)
      · exact False.elim (hcontra v2 v1 y (Or.inr ⟨h1.symm, h2⟩) hg2 hg1)
    · exact False.elim (hcontra v2 v1 y (Or.inl h1) hg2 hg1)
  -- Database & Rows construction
  let P := D × D
  let DB := P → Val
  let digitsOf : DB → Finset E := fun X =>
    Finset.univ.filter (fun e => (valNat (X e.2)).testBit e.1.val = true)
  let leftOf : DB → Rows := fun X site pat =>
    if hs : site < L0 then
      let s : S0 := (⟨site, hs⟩, fun off => pat.testBit off.val)
      decide (base s = true ∨ s ∈ (digitsOf X).image port)
    else
      decide (pat.testBit w = pat.testBit 0)
  let rightOf : P → Rows := fun p idx pat =>
    if hj : idx < w then
      decide (pat.testBit 0 = packW true p.2 ⟨(L - L0 + idx) % w, Nat.mod_lt _ hw_pos⟩ ∧
              pat.testBit w = packW false p.1 ⟨idx, hj⟩)
    else true
  have htotal_eq : ∀ (X : DB) (p : P), total (leftOf X) (rightOf p) = valNat (X p) := by
    intro X p
    have h836 := hcount836 (digitsOf X) false true p.1 p.2
    simp only [Bool.false_eq_true, ↓reduceIte] at h836
    have hweight : (∑ bit : Fin q, if (bit, p.1, p.2) ∈ digitsOf X then 2 ^ bit.val else 0) = valNat (X p) := by
      have hcongr : (∑ bit : Fin q, if (bit, p.1, p.2) ∈ digitsOf X then 2 ^ bit.val else 0) =
          (∑ bit : Fin q, if (valNat (X p)).testBit bit.val = true then 2 ^ bit.val else 0) := by
        refine Finset.sum_congr rfl fun bit _ => ?_
        simp [digitsOf]
      rw [hcongr]
      exact sum_testBit_two_pow q (valNat (X p)) (hval_lt (X p))
    rw [hweight] at h836
    rw [← h836]
    dsimp only [total]
    rw [list_filter_nodup_eq_card _ List.nodup_range]
    let Sleft := (List.range (2 ^ n)).toFinset.filter (fun word =>
      ((List.range n).all (fun site =>
        let pat := (List.range (w + 1)).foldl (fun (acc bit : ℕ) =>
          acc ||| ((word.testBit ((site + bit) % n)).toNat <<< bit)) 0
        if site < L then leftOf X site pat else rightOf p (site - L) pat)) = true)
    let Sright := (Finset.univ : Finset (Fin n0 → Bool)).filter (fun x0 =>
      (∀ j : Fin w, x0 (loc0 j.val) = packW false p.1 j ∧ x0 (loc0 (L0 + j.val)) = packW true p.2 j) ∧
      ∀ i : Fin L0,
        let s : S0 := (i, fun off => x0 (loc0 (i.val + off.val)))
        base s = true ∨ s ∈ (digitsOf X).image port)
    suffices hcard_eq : Sleft.card = Sright.card by
      trans Sleft.card
      · congr 1; ext word; simp [Sleft]
      · trans Sright.card
        · exact hcard_eq
        · congr 1
    let extBits : (Fin n0 → Bool) → (Fin n → Bool) := fun x0 i =>
      if hi : i.val < n0 then x0 ⟨i.val, hi⟩
      else x0 ⟨L0 + (i.val - L0) % w, by have := Nat.mod_lt (i.val - L0) hw_pos; dsimp only [n0]; omega⟩
    have hext_periodic : ∀ (x0 : Fin n0 → Bool) (k : ℕ) (hk : L0 ≤ k) (hkn : k < n),
        extBits x0 ⟨k, hkn⟩ = x0 ⟨L0 + (k - L0) % w, by have := Nat.mod_lt (k - L0) hw_pos; dsimp only [n0]; omega⟩ := by
      intro x0 k hk hkn
      dsimp only [extBits]
      by_cases h1 : k < n0
      · rw [dif_pos h1]
        congr 1; apply Fin.ext
        have hmod : (k - L0) % w = k - L0 := Nat.mod_eq_of_lt (by dsimp only [n0] at h1; omega)
        change k = L0 + (k - L0) % w; omega
      · rw [dif_neg h1]
    have hpat_eval : ∀ (word : ℕ) (site b : ℕ),
        ((List.range (w + 1)).foldl (fun (acc bit : ℕ) =>
          acc ||| ((word.testBit ((site + bit) % n)).toNat <<< bit)) 0).testBit b =
          if b < w + 1 then word.testBit ((site + b) % n) else false := by
      intro word site b
      exact foldl_pat_testBit (w + 1) (fun bit => word.testBit ((site + bit) % n)) b
    refine (Finset.card_bij (fun (x0 : Fin n0 → Bool) _ => wordOf (extBits x0)) ?_ ?_ ?_).symm
    · intro x0 hx0
      rcases (Finset.mem_filter.mp hx0).2 with ⟨hbd, hseg⟩
      refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.mem_range.mpr (wordOf_lt _)), ?_⟩
      rw [List.all_eq_true]
      intro site hsite
      have hs_lt : site < n := List.mem_range.mp hsite
      by_cases hsL : site < L
      · rw [if_pos hsL]
        by_cases hsL0 : site < L0
        · dsimp only [leftOf]; rw [dif_pos hsL0, decide_eq_true_eq]
          have harg : (fun off : Fin (w + 1) =>
              ((List.range (w + 1)).foldl (fun (acc bit : ℕ) =>
                acc ||| (((wordOf (extBits x0)).testBit ((site + bit) % n)).toNat <<< bit)) 0).testBit off.val) =
              (fun off : Fin (w + 1) => x0 (loc0 (site + off.val))) := by
            funext off
            rw [hpat_eval, if_pos off.isLt, testBit_wordOf]
            have hlt1 : site + off.val < n0 := by have := off.isLt; dsimp only [n0]; omega
            have hlt2 : site + off.val < n := by omega
            rw [Nat.mod_eq_of_lt hlt2, dif_pos hlt2]
            dsimp only [extBits, loc0]
            rw [dif_pos hlt1]
            congr 1; apply Fin.ext; exact (Nat.mod_eq_of_lt hlt1).symm
          rw [harg]
          exact hseg ⟨site, hsL0⟩
        · dsimp only [leftOf]; rw [dif_neg hsL0, decide_eq_true_eq]
          rw [hpat_eval, hpat_eval, if_pos (Nat.lt_succ_self w), if_pos (by omega),
            testBit_wordOf, testBit_wordOf]
          have h1 : site + w < n := by dsimp only [n]; omega
          have h2 : site + 0 < n := by omega
          rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, dif_pos h1, dif_pos h2]
          rw [hext_periodic x0 (site + w) (by omega) h1, hext_periodic x0 (site + 0) (by omega) h2]
          congr 1; apply Fin.ext
          have hmod : (site + w - L0) % w = (site + 0 - L0) % w := by
            have : site + w - L0 = (site + 0 - L0) + w := by omega
            rw [this, Nat.add_mod_right]
          change L0 + (site + w - L0) % w = L0 + (site + 0 - L0) % w
          rw [hmod]
      · rw [if_neg hsL]
        have hj : site - L < w := by dsimp only [n] at hs_lt; omega
        dsimp only [rightOf]; rw [dif_pos hj, decide_eq_true_eq]
        rw [hpat_eval, hpat_eval, if_pos (by omega), if_pos (Nat.lt_succ_self w),
          testBit_wordOf, testBit_wordOf]
        have hm1 : (site + 0) % n = site := Nat.mod_eq_of_lt hs_lt
        have hm2 : (site + w) % n = site - L := by
          have : site + w = (site - L) + n := by dsimp only [n]; omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hm1, hm2, dif_pos hs_lt, dif_pos (by omega)]
        constructor
        · rw [hext_periodic x0 site (by omega) hs_lt]
          have hidx_eq : (site - L0) % w = (L - L0 + (site - L)) % w := by
            have : site - L0 = L - L0 + (site - L) := by omega
            rw [this]
          let j' : Fin w := ⟨(L - L0 + (site - L)) % w, Nat.mod_lt _ hw_pos⟩
          have hbd_j := (hbd j').2
          have hloc_eq : loc0 (L0 + j'.val) = ⟨L0 + (site - L0) % w, by have := Nat.mod_lt (site - L0) hw_pos; dsimp only [n0]; omega⟩ := by
            apply Fin.ext
            have hlt : L0 + j'.val < n0 := by have := j'.isLt; dsimp only [n0]; omega
            change (L0 + j'.val) % n0 = L0 + (site - L0) % w
            rw [Nat.mod_eq_of_lt hlt]
            change L0 + (L - L0 + (site - L)) % w = L0 + (site - L0) % w
            rw [hidx_eq]
          rw [← hloc_eq]
          exact hbd_j
        · dsimp only [extBits]
          have hlt0 : site - L < n0 := by dsimp only [n0]; omega
          rw [dif_pos hlt0]
          have hbd_j := (hbd ⟨site - L, hj⟩).1
          have hloc_eq : loc0 (site - L) = ⟨site - L, hlt0⟩ := by
            apply Fin.ext; exact Nat.mod_eq_of_lt hlt0
          rw [← hloc_eq]
          exact hbd_j
    · intro x1 _ x2 _ heq
      have hbit := wordOf_inj heq
      funext i
      have h1 := congrFun hbit ⟨i.val, by have := i.isLt; dsimp only [n0, n] at *; omega⟩
      dsimp only [extBits] at h1
      rw [dif_pos i.isLt, dif_pos i.isLt] at h1
      exact h1
    · intro word hword
      rcases Finset.mem_filter.mp hword with ⟨hw_mem, hall⟩
      have hw_lt : word < 2 ^ n := List.mem_range.mp (List.mem_toFinset.mp hw_mem)
      rw [List.all_eq_true] at hall
      let x : Fin n → Bool := fun i => word.testBit i.val
      let x0 : Fin n0 → Bool := fun i => word.testBit i.val
      have hstep_per : ∀ k : ℕ, L0 ≤ k → k < L → word.testBit (k + w) = word.testBit k := by
        intro k hk1 hk2
        have hsite := hall k (List.mem_range.mpr (by dsimp only [n]; omega))
        rw [if_pos hk2] at hsite
        dsimp only [leftOf] at hsite
        rw [dif_neg (by omega), decide_eq_true_eq, hpat_eval, hpat_eval,
          if_pos (Nat.lt_succ_self w), if_pos (by omega)] at hsite
        rw [Nat.mod_eq_of_lt (by dsimp only [n]; omega), Nat.mod_eq_of_lt (by dsimp only [n]; omega)] at hsite
        simpa using hsite
      have hper : ∀ t : ℕ, L0 + t < n → word.testBit (L0 + t) = word.testBit (L0 + t % w) := by
        intro t
        induction t using Nat.strong_induction_on with
        | ind t ih =>
          intro htn
          by_cases htw : t < w
          · rw [Nat.mod_eq_of_lt htw]
          · have h1 := hstep_per (L0 + (t - w)) (by omega) (by dsimp only [n] at htn; omega)
            have h2 : L0 + (t - w) + w = L0 + t := by omega
            rw [h2] at h1
            rw [h1, ih (t - w) (by omega) (by omega)]
            have hmod : (t - w) % w = t % w := by
              have : t = (t - w) + w := by omega
              conv_rhs => rw [this, Nat.add_mod_right]
            rw [hmod]
      have hx0_mem : x0 ∈ Sright := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
        · intro j
          constructor
          · have hsite := hall (L + j.val) (List.mem_range.mpr (by have := j.isLt; dsimp only [n]; omega))
            rw [if_neg (by omega)] at hsite
            dsimp only [rightOf] at hsite
            have hsub : L + j.val - L = j.val := by omega
            rw [hsub, dif_pos j.isLt, decide_eq_true_eq, hpat_eval, hpat_eval,
              if_pos (Nat.lt_succ_self w), if_pos (by omega)] at hsite
            have hm2 : (L + j.val + w) % n = j.val := by
              have : L + j.val + w = j.val + n := by dsimp only [n]; omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := j.isLt; dsimp only [n]; omega)]
            rw [hm2] at hsite
            dsimp only [x0, loc0]
            rw [Nat.mod_eq_of_lt (by have := j.isLt; dsimp only [n0]; omega)]
            exact hsite.2
          · let r0 : ℕ := (w - (L - L0) % w + j.val) % w
            have hr0_lt : r0 < w := Nat.mod_lt _ hw_pos
            have hrot : (L - L0 + r0) % w = j.val := by
              have h1 : (L - L0 + r0) % w = (L - L0 + (w - (L - L0) % w + j.val)) % w := by
                dsimp only [r0]
                simp only [Nat.add_mod, Nat.mod_mod]
              rw [h1]
              have hrem_lt : (L - L0) % w < w := Nat.mod_lt _ hw_pos
              have h2 : ((L - L0) % w + (w - (L - L0) % w + j.val)) % w = j.val := by
                have : (L - L0) % w + (w - (L - L0) % w + j.val) = j.val + w := by omega
                rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
              conv_rhs => rw [← h2]
              simp only [Nat.add_mod, Nat.mod_mod]
            have hsite := hall (L + r0) (List.mem_range.mpr (by dsimp only [n]; omega))
            rw [if_neg (by omega)] at hsite
            dsimp only [rightOf] at hsite
            have hsub : L + r0 - L = r0 := by omega
            rw [hsub, dif_pos hr0_lt, decide_eq_true_eq, hpat_eval, hpat_eval,
              if_pos (by omega), if_pos (Nat.lt_succ_self w)] at hsite
            have hm1 : (L + r0 + 0) % n = L + r0 := Nat.mod_eq_of_lt (by dsimp only [n]; omega)
            rw [hm1] at hsite
            have hp_eq := hper (L - L0 + r0) (by dsimp only [n]; omega)
            have hsum_eq : L0 + (L - L0 + r0) = L + r0 := by omega
            rw [hsum_eq, hrot] at hp_eq
            dsimp only [x0, loc0]
            rw [Nat.mod_eq_of_lt (by have := j.isLt; dsimp only [n0]; omega), ← hp_eq]
            have hj_eq : (⟨(L - L0 + r0) % w, Nat.mod_lt _ hw_pos⟩ : Fin w) = j := Fin.ext hrot
            rw [hj_eq] at hsite
            exact hsite.1
        · intro i
          have hsite := hall i.val (List.mem_range.mpr (by have := i.isLt; dsimp only [n]; omega))
          rw [if_pos (by have := i.isLt; omega)] at hsite
          dsimp only [leftOf] at hsite
          rw [dif_pos i.isLt, decide_eq_true_eq] at hsite
          have harg : (fun off : Fin (w + 1) =>
              ((List.range (w + 1)).foldl (fun (acc bit : ℕ) =>
                acc ||| ((word.testBit ((i.val + bit) % n)).toNat <<< bit)) 0).testBit off.val) =
              (fun off : Fin (w + 1) => x0 (loc0 (i.val + off.val))) := by
            funext off
            rw [hpat_eval, if_pos off.isLt]
            have hlt1 : i.val + off.val < n0 := by have := i.isLt; have := off.isLt; dsimp only [n0]; omega
            have hlt2 : i.val + off.val < n := by omega
            rw [Nat.mod_eq_of_lt hlt2]
            dsimp only [x0, loc0]
            rw [Nat.mod_eq_of_lt hlt1]
          rw [harg] at hsite
          exact hsite
      refine ⟨x0, hx0_mem, ?_⟩
      have hext_eq : extBits x0 = fun i : Fin n => word.testBit i.val := by
        funext i
        dsimp only [extBits, x0]
        by_cases hi : i.val < n0
        · rw [dif_pos hi]
        · rw [dif_neg hi]
          have h1 := hper (i.val - L0) (by have := i.isLt; omega)
          have h2 : L0 + (i.val - L0) = i.val := by dsimp only [n0] at hi; omega
          rw [h2] at h1
          exact h1.symm
      rw [hext_eq, wordOf_bits word hw_lt]
  -- Equivalence DB ≃ (Fin N → Bool)
  have hcard_DB : Fintype.card DB = 2 ^ N := by
    dsimp only [DB, P, D, Val, N]
    rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin]
    have h1 : 2 ^ a * 2 ^ h = 2 ^ (a + h) := (pow_add 2 a h).symm
    have h2 : 2 ^ d * 2 ^ d = 4 ^ d := by
      rw [← mul_pow]; norm_num
    rw [h1, h2, ← pow_mul]
  let dec : ℕ → Val := fun y =>
    if hex : ∃ v : Val, good (valNat v) y then Classical.choose hex else (⟨0, by positivity⟩, ⟨0, by positivity⟩)
  have hdec_spec : ∀ (v : Val) (y : ℕ), good (valNat v) y → dec y = v := by
    intro v y hgy
    have hex : ∃ v' : Val, good (valNat v') y := ⟨v, hgy⟩
    dsimp only [dec]; rw [dif_pos hex]
    exact hval_sep _ v y (Classical.choose_spec hex) hgy
  constructor
  · -- Part 1: Deterministic lower bound
    intro S send answer hgood
    have hinj : Function.Injective (fun X : DB => send (leftOf X)) := by
      intro X1 X2 heq
      funext p
      have hg1 : good (valNat (X1 p)) (answer (send (leftOf X1)) (rightOf p)) := by
        rw [← htotal_eq X1 p]; exact hgood (leftOf X1) (rightOf p)
      have hg2 : good (valNat (X2 p)) (answer (send (leftOf X1)) (rightOf p)) := by
        dsimp only at heq
        rw [heq, ← htotal_eq X2 p]; exact hgood (leftOf X2) (rightOf p)
      exact hval_sep _ _ _ hg1 hg2
    have hle := Fintype.card_le_of_injective _ hinj
    rw [hcard_DB, Fintype.card_fin] at hle
    exact hle
  · -- Part 2: Randomized lower bound
    intro S R hR pack guess hgood
    have hVal_card : Fintype.card Val = Fintype.card (Fin (a + h) → Bool) := by
      dsimp only [Val]
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, ← pow_add]
    let eVal : Val ≃ (Fin (a + h) → Bool) := Fintype.equivOfCardEq hVal_card
    have hIdx_card : Fintype.card (P × Fin (a + h)) = Fintype.card (Fin N) := by
      dsimp only [P, D, N]
      rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
        Fintype.card_fin, Fintype.card_fin]
      have h4 : 2 ^ d * 2 ^ d = 4 ^ d := by rw [← mul_pow]; norm_num
      rw [h4, mul_comm]
    let eIdx : (P × Fin (a + h)) ≃ Fin N := Fintype.equivOfCardEq hIdx_card
    let eDB : DB ≃ (Fin N → Bool) :=
      { toFun := fun X t => eVal (X (eIdx.symm t).1) (eIdx.symm t).2,
        invFun := fun f p => eVal.symm (fun k => f (eIdx (p, k))),
        left_inv := fun X => by
          funext p
          dsimp only
          have h1 : (fun k : Fin (a + h) => eVal (X (eIdx.symm (eIdx (p, k))).1) (eIdx.symm (eIdx (p, k))).2) =
              eVal (X p) := by
            funext k; simp
          rw [h1, eVal.symm_apply_apply],
        right_inv := fun f => by
          funext t
          simp }
    let pred : Fin R → Fin S → DB := fun coin msg p => dec (guess coin msg (rightOf p))
    let dist : DB → DB → ℕ := fun X Y =>
      (Finset.univ.filter (fun t : Fin N => eDB X t ≠ eDB Y t)).card
    have hbit_err : ∀ (X : DB) (t : Fin N),
        3 * (Finset.univ.filter (fun coin : Fin R => eDB (pred coin (pack coin (leftOf X))) t ≠ eDB X t)).card ≤ R := by
      intro X t
      let p : P := (eIdx.symm t).1
      have hg_list := hgood (leftOf X) (rightOf p)
      rw [list_filter_nodup_eq_card _ (List.nodup_finRange R)] at hg_list
      let Gset := (Finset.univ : Finset (Fin R)).filter (fun coin =>
        good (total (leftOf X) (rightOf p)) (guess coin (pack coin (leftOf X)) (rightOf p)))
      let Eset := (Finset.univ : Finset (Fin R)).filter (fun coin =>
        eDB (pred coin (pack coin (leftOf X))) t ≠ eDB X t)
      have hdisj : Disjoint Gset Eset := by
        rw [Finset.disjoint_left]
        intro coin hG hE
        have hg := (Finset.mem_filter.mp hG).2
        rw [htotal_eq X p] at hg
        have heq_p : pred coin (pack coin (leftOf X)) p = X p := hdec_spec (X p) _ hg
        have heq_t : eDB (pred coin (pack coin (leftOf X))) t = eDB X t := by
          change eVal (pred coin (pack coin (leftOf X)) (eIdx.symm t).1) (eIdx.symm t).2 =
            eVal (X (eIdx.symm t).1) (eIdx.symm t).2
          rw [show (eIdx.symm t).1 = p from rfl, heq_p]
        exact (Finset.mem_filter.mp hE).2 heq_t
      have hleR : Gset.card + Eset.card ≤ R := by
        rw [← Finset.card_union_of_disjoint hdisj]
        calc (Gset ∪ Eset).card ≤ (Finset.univ : Finset (Fin R)).card := Finset.card_le_card (Finset.subset_univ _)
          _ = R := by simp
      have hg_card : 2 * R ≤ 3 * Gset.card := by
        convert hg_list using 2
        congr 1
        ext coin
        simp [Gset]
      change 3 * Eset.card ≤ R
      omega
    have htotal_err : 3 * ∑ coin : Fin R, ∑ X : DB, dist X (pred coin (pack coin (leftOf X))) ≤
        R * (N * 2 ^ N) := by
      have hswap : ∑ coin : Fin R, ∑ X : DB, dist X (pred coin (pack coin (leftOf X))) =
          ∑ X : DB, ∑ t : Fin N,
            (Finset.univ.filter (fun coin : Fin R => eDB (pred coin (pack coin (leftOf X))) t ≠ eDB X t)).card := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun X _ => ?_
        have h1 : ∀ coin : Fin R, dist X (pred coin (pack coin (leftOf X))) =
            ∑ t : Fin N, if eDB (pred coin (pack coin (leftOf X))) t ≠ eDB X t then 1 else 0 := by
          intro coin
          dsimp only [dist]
          rw [Finset.card_filter]
          refine Finset.sum_congr rfl fun t _ => ?_
          by_cases h : eDB X t = eDB (pred coin (pack coin (leftOf X))) t
          · simp [h]
          · simp [h, Ne.symm h]
        simp only [h1]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.card_filter]
      rw [hswap, Finset.mul_sum]
      calc ∑ X : DB, 3 * ∑ t : Fin N,
              (Finset.univ.filter (fun coin : Fin R => eDB (pred coin (pack coin (leftOf X))) t ≠ eDB X t)).card
          = ∑ X : DB, ∑ t : Fin N,
              3 * (Finset.univ.filter (fun coin : Fin R => eDB (pred coin (pack coin (leftOf X))) t ≠ eDB X t)).card := by
                refine Finset.sum_congr rfl fun X _ => Finset.mul_sum _ _ _
        _ ≤ ∑ _X : DB, ∑ _t : Fin N, R :=
            Finset.sum_le_sum fun X _ => Finset.sum_le_sum fun t _ => hbit_err X t
        _ = R * (N * 2 ^ N) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hcard_DB, smul_eq_mul]
            ring
    have hex_coin : ∃ coin0 : Fin R,
        3 * ∑ X : DB, dist X (pred coin0 (pack coin0 (leftOf X))) ≤ N * 2 ^ N := by
      by_contra hall
      push Not at hall
      have hgt : R * (N * 2 ^ N) < 3 * ∑ coin : Fin R, ∑ X : DB, dist X (pred coin (pack coin (leftOf X))) := by
        rw [Finset.mul_sum]
        have hsum_gt : ∑ _coin : Fin R, (N * 2 ^ N) <
            ∑ coin : Fin R, 3 * ∑ X : DB, dist X (pred coin (pack coin (leftOf X))) :=
          Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hR⟩⟩) fun coin _ => hall coin
        simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using hsum_gt
      omega
    rcases hex_coin with ⟨coin0, hcoin0⟩
    let msg0 : DB → Fin S := fun X => pack coin0 (leftOf X)
    let pred0 : Fin S → DB := fun m => pred coin0 m
    -- Lower bound sum of (1/2)^(dist X (pred0 (msg0 X))) via tangent line to exp
    let c : ℝ := Real.log 2
    have hc_pos : 0 < c := Real.log_pos (by norm_num)
    have hpow_exp : ∀ k : ℕ, (1 / 2 : ℝ) ^ k = Real.exp (-c * (k : ℝ)) := by
      intro k
      have h1 : Real.exp (-c * (k : ℝ)) = (Real.exp (-c)) ^ k := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      rw [h1, Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    have hsum_lb : (2 ^ N : ℝ) * Real.exp (-c * (N : ℝ) / 3) ≤
        ∑ X : DB, (1 / 2 : ℝ) ^ (dist X (pred0 (msg0 X))) := by
      have hpt : ∀ X : DB,
          Real.exp (-c * (N : ℝ) / 3) * (1 - c * ((dist X (pred0 (msg0 X)) : ℝ) - (N : ℝ) / 3)) ≤
            (1 / 2 : ℝ) ^ (dist X (pred0 (msg0 X))) := by
        intro X
        rw [hpow_exp]
        have hlin : 1 + (-c * ((dist X (pred0 (msg0 X)) : ℝ) - (N : ℝ) / 3)) ≤
            Real.exp (-c * ((dist X (pred0 (msg0 X)) : ℝ) - (N : ℝ) / 3)) := by
          linarith [Real.add_one_le_exp (-c * ((dist X (pred0 (msg0 X)) : ℝ) - (N : ℝ) / 3))]
        have hmul := mul_le_mul_of_nonneg_left hlin (le_of_lt (Real.exp_pos (-c * (N : ℝ) / 3)))
        rw [← Real.exp_add] at hmul
        have hexp_eq : -c * (N : ℝ) / 3 + -c * ((dist X (pred0 (msg0 X)) : ℝ) - (N : ℝ) / 3) =
            -c * (dist X (pred0 (msg0 X)) : ℝ) := by ring
        rw [hexp_eq] at hmul
        linarith
      calc (2 ^ N : ℝ) * Real.exp (-c * (N : ℝ) / 3)
          ≤ Real.exp (-c * (N : ℝ) / 3) *
              ∑ X : DB, (1 - c * ((dist X (pred0 (msg0 X)) : ℝ) - (N : ℝ) / 3)) := by
            have hsum_avg : (2 ^ N : ℝ) ≤
                ∑ X : DB, (1 - c * ((dist X (pred0 (msg0 X)) : ℝ) - (N : ℝ) / 3)) := by
              rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hcard_DB, nsmul_eq_mul,
                mul_one, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
                hcard_DB, nsmul_eq_mul]
              push_cast
              have hleR : 3 * (∑ X : DB, (dist X (pred0 (msg0 X)) : ℝ)) ≤ (N : ℝ) * (2 ^ N : ℝ) := by
                exact_mod_cast hcoin0
              have hdiff : ∑ X : DB, (dist X (pred0 (msg0 X)) : ℝ) - (2 ^ N : ℝ) * ((N : ℝ) / 3) ≤ 0 := by
                linarith
              nlinarith
            have := mul_le_mul_of_nonneg_left hsum_avg (le_of_lt (Real.exp_pos (-c * (N : ℝ) / 3)))
            linarith
        _ = ∑ X : DB, Real.exp (-c * (N : ℝ) / 3) *
              (1 - c * ((dist X (pred0 (msg0 X)) : ℝ) - (N : ℝ) / 3)) := Finset.mul_sum _ _ _
        _ ≤ ∑ X : DB, (1 / 2 : ℝ) ^ (dist X (pred0 (msg0 X))) := Finset.sum_le_sum fun X _ => hpt X
    -- Upper bound sum by S * (3/2)^N
    have hsum_ub : ∑ X : DB, (1 / 2 : ℝ) ^ (dist X (pred0 (msg0 X))) ≤ (S : ℝ) * (3 / 2 : ℝ) ^ N := by
      have h1 : ∑ X : DB, (1 / 2 : ℝ) ^ (dist X (pred0 (msg0 X))) ≤
          ∑ m : Fin S, ∑ X : DB, (1 / 2 : ℝ) ^ (dist X (pred0 m)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_le_sum fun X _ => ?_
        exact Finset.single_le_sum (f := fun m : Fin S => (1 / 2 : ℝ) ^ (dist X (pred0 m)))
          (fun m _ => by positivity) (Finset.mem_univ (msg0 X))
      have h2 : ∀ m : Fin S, ∑ X : DB, (1 / 2 : ℝ) ^ (dist X (pred0 m)) = (3 / 2 : ℝ) ^ N := by
        intro m
        have hcomp := Equiv.sum_comp eDB.symm (fun X : DB => (1 / 2 : ℝ) ^ (dist X (pred0 m)))
        rw [← hcomp]
        have heq_f : ∀ x : Fin N → Bool, dist (eDB.symm x) (pred0 m) =
            (Finset.univ.filter (fun i : Fin N => x i ≠ eDB (pred0 m) i)).card := by
          intro x; dsimp only [dist]; simp
        simp only [heq_f]
        exact hamming_sum_eq N (eDB (pred0 m))
      calc ∑ X : DB, (1 / 2 : ℝ) ^ (dist X (pred0 (msg0 X)))
          ≤ ∑ m : Fin S, ∑ X : DB, (1 / 2 : ℝ) ^ (dist X (pred0 m)) := h1
        _ = ∑ _m : Fin S, (3 / 2 : ℝ) ^ N := Finset.sum_congr rfl fun m _ => h2 m
        _ = (S : ℝ) * (3 / 2 : ℝ) ^ N := by simp
    have hmain_real : (2 ^ N : ℝ) * Real.exp (-c * (N : ℝ) / 3) ≤ (S : ℝ) * (3 / 2 : ℝ) ^ N :=
      le_trans hsum_lb hsum_ub
    -- Cube to eliminate exp
    have hcube : ((2 ^ N : ℝ) * Real.exp (-c * (N : ℝ) / 3)) ^ 3 ≤ ((S : ℝ) * (3 / 2 : ℝ) ^ N) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hmain_real 3
    have hlhs_cube : ((2 ^ N : ℝ) * Real.exp (-c * (N : ℝ) / 3)) ^ 3 = (4 : ℝ) ^ N := by
      rw [mul_pow, ← Real.exp_nat_mul]
      have hexp : (3 : ℕ) * (-c * (N : ℝ) / 3) = -c * (N : ℝ) := by push_cast; ring
      rw [hexp, ← hpow_exp N]
      have h1 : ((2 : ℝ) ^ N) ^ 3 * (1 / 2 : ℝ) ^ N = ((2 : ℝ) ^ 3 * (1 / 2 : ℝ)) ^ N := by
        rw [← pow_mul, mul_comm N 3, pow_mul, ← mul_pow]
      rw [h1]
      norm_num
    have hrhs_cube : ((S : ℝ) * (3 / 2 : ℝ) ^ N) ^ 3 = (S : ℝ) ^ 3 * ((27 : ℝ) / 8) ^ N := by
      rw [mul_pow, ← pow_mul, mul_comm N 3, pow_mul]
      norm_num
    rw [hlhs_cube, hrhs_cube] at hcube
    have h32_real : (32 : ℝ) ^ N ≤ (S : ℝ) ^ 3 * (27 : ℝ) ^ N := by
      have h8pos : (0 : ℝ) < (8 : ℝ) ^ N := by positivity
      have hmul := mul_le_mul_of_nonneg_right hcube (le_of_lt h8pos)
      have hL : (4 : ℝ) ^ N * (8 : ℝ) ^ N = (32 : ℝ) ^ N := by rw [← mul_pow]; norm_num
      have hR : (S : ℝ) ^ 3 * ((27 : ℝ) / 8) ^ N * (8 : ℝ) ^ N = (S : ℝ) ^ 3 * (27 : ℝ) ^ N := by
        rw [mul_assoc, ← mul_pow]; norm_num
      rw [hL, hR] at hmul
      exact hmul
    have h32_nat : 32 ^ N ≤ S ^ 3 * 27 ^ N := by exact_mod_cast h32_real
    have hpow5 : (32 ^ N) ^ 5 ≤ (S ^ 3 * 27 ^ N) ^ 5 := Nat.pow_le_pow_left h32_nat 5
    have hconst : 2 * 27 ^ 5 ≤ 32 ^ 5 := by decide
    have h27pos : 0 < 27 ^ (5 * N) := by positivity
    have hfinal : 2 ^ N * 27 ^ (5 * N) ≤ S ^ 15 * 27 ^ (5 * N) := by
      calc 2 ^ N * 27 ^ (5 * N)
          = (2 * 27 ^ 5) ^ N := by rw [mul_pow, ← pow_mul, mul_comm 5 N]
        _ ≤ (32 ^ 5) ^ N := Nat.pow_le_pow_left hconst N
        _ = (32 ^ N) ^ 5 := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ (S ^ 3 * 27 ^ N) ^ 5 := hpow5
        _ = S ^ 15 * 27 ^ (5 * N) := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm N 5]
    exact Nat.le_of_mul_le_mul_right hfinal h27pos

end PEqualNP.Outside.L_clb_113_aux

open PEqualNP.Outside.L_clb_113_aux in
theorem PEqualNP.Outside.L_clb_113 :
∀ (d a b L : Nat),
  let w := d+2
  let K := 2^b
  let h := b-3
  let q := h+3*2^a
  let N := (a+h)*4^d
  q*(2*w+(2^w-1)) ≤ L →
    let n := L+w
    let Rows := Nat → Nat → Bool
    let total := fun (left right : Rows) =>
      ((List.range (2^n)).filter (fun word => (List.range n).all (fun site =>
        let pat := (List.range (w+1)).foldl (fun (acc bit : Nat) =>
          acc ||| ((word.testBit ((site+bit) % n)).toNat <<< bit)) 0
        if site < L then left site pat else right (site-L) pat))).length
    let good := fun (c y : Nat) => K*c ≤ (K+1)*y ∧ K*y ≤ (K+1)*c
    (∀ (S : Nat) (send : Rows → Fin S) (answer : Fin S → Rows → Nat),
      (∀ left right : Rows, good (total left right) (answer (send left) right)) → 2^N ≤ S) ∧
    ∀ (S R : Nat), 0 < R →
      ∀ (pack : Fin R → Rows → Fin S) (guess : Fin R → Fin S → Rows → Nat),
        (∀ firstPart lastPart : Rows, 2*R ≤ 3*((List.finRange R).filter (fun coin =>
          good (total firstPart lastPart) (guess coin (pack coin firstPart) lastPart))).length) →
        2^N ≤ S^15 :=
  main_proof
