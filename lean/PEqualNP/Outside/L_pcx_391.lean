import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_pcx_391

def sgn (b : Bool) : ℤ := if b then -1 else 1

lemma one_add_sgn_eq (U : ℤ) (a b : Bool) :
    1 + U * sgn a * sgn b = if a ≠ b then 1 - U else 1 + U := by
  cases a <;> cases b <;> simp [sgn] <;> ring

lemma fin_val_add_one (n : ℕ) (j : Fin (n + 1)) :
    (j + 1).val = (j.val + 1) % (n + 1) := by
  cases n with
  | zero =>
    have hj : j.val = 0 := by omega
    have h0 : (j + 1).val = 0 := by omega
    rw [hj, h0]
  | succ k =>
    have h1 : (1 : Fin (k + 2)).val = 1 := by
      change 1 % (k + 2) = 1
      exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, h1]

lemma fin_val_add_one_neZero (n : ℕ) [NeZero n] (i : Fin n) :
    (i + 1).val = (i.val + 1) % n := by
  rcases Nat.exists_eq_succ_of_ne_zero (NeZero.ne n) with ⟨k, rfl⟩
  exact fin_val_add_one k i

def finAddOneEquiv (n : ℕ) [NeZero n] : Fin n ≃ Fin n where
  toFun i := i + 1
  invFun i := ⟨if i.val = 0 then n - 1 else i.val - 1, by
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    split_ifs <;> omega⟩
  left_inv i := by
    ext
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hval : (i + 1).val = (i.val + 1) % n := fin_val_add_one_neZero n i
    dsimp only
    rw [hval]
    by_cases hlast : i.val = n - 1
    · have hm : (i.val + 1) % n = 0 := by
        have : i.val + 1 = n := by omega
        rw [this, Nat.mod_self]
      rw [hm]
      simp only [↓reduceIte]
      omega
    · have hm : (i.val + 1) % n = i.val + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hm]
      have hne : i.val + 1 ≠ 0 := by omega
      simp only [hne, ↓reduceIte]
      omega
  right_inv i := by
    ext
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    have hlt : (if i.val = 0 then n - 1 else i.val - 1) < n := by split_ifs <;> omega
    have hval : ((⟨if i.val = 0 then n - 1 else i.val - 1, hlt⟩ : Fin n) + 1).val =
        ((if i.val = 0 then n - 1 else i.val - 1) + 1) % n :=
      fin_val_add_one_neZero n ⟨if i.val = 0 then n - 1 else i.val - 1, hlt⟩
    dsimp only
    rw [hval]
    by_cases h0 : i.val = 0
    · simp only [h0, ↓reduceIte]
      have : n - 1 + 1 = n := by omega
      rw [this, Nat.mod_self]
    · simp only [h0, ↓reduceIte]
      have : i.val - 1 + 1 = i.val := by omega
      rw [this]
      exact Nat.mod_eq_of_lt i.isLt

lemma sigma_snd_eq_zero {α : Type*} {n : α → ℕ} (q : (i : α) × Fin (n i + 1)) (h : q.2.val = 0) :
    q = ⟨q.1, 0⟩ := by
  rcases q with ⟨i, j⟩
  congr 1
  exact Fin.ext h

lemma sigma_fin_pred_succ {α : Type*} {n : α → ℕ} (q : (r : α) × Fin (n r + 1)) (h0 : q.2.val ≠ 0) :
    (⟨q.1, ⟨q.2.val - 1 + 1, by have := q.2.isLt; omega⟩⟩ : (r : α) × Fin (n r + 1)) = q := by
  rcases q with ⟨r, j⟩
  dsimp only at h0 ⊢
  exact Sigma.ext rfl (heq_of_eq (Fin.ext (by dsimp only; omega)))

def edgeWeight (U V : ℤ) (e : ℕ) : ℤ := if e % 2 = 0 then V else U

def oddCnt (a L : ℕ) : ℕ :=
  ((Finset.range L).filter (fun j => (a + j) % 2 = 1)).card

def evenCnt (a L : ℕ) : ℕ :=
  ((Finset.range L).filter (fun j => (a + j) % 2 = 0)).card

lemma oddCnt_add_evenCnt (a L : ℕ) : oddCnt a L + evenCnt a L = L := by
  unfold oddCnt evenCnt
  have hfeq : (Finset.range L).filter (fun j => (a + j) % 2 = 0) =
      (Finset.range L).filter (fun j => ¬ ((a + j) % 2 = 1)) := by
    refine Finset.filter_congr (fun j _ => ?_)
    omega
  rw [hfeq, Finset.card_filter_add_card_filter_not, Finset.card_range]

lemma prod_edgeWeight_range (U V : ℤ) (a : ℕ) : ∀ L : ℕ,
    ∏ j ∈ Finset.range L, edgeWeight U V (a + j) = U ^ oddCnt a L * V ^ evenCnt a L
  | 0 => by simp [oddCnt, evenCnt]
  | L + 1 => by
    rw [Finset.prod_range_succ, prod_edgeWeight_range U V a L]
    unfold oddCnt evenCnt edgeWeight
    rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
    have hmem : L ∉ Finset.range L := by simp
    have hnot1 : L ∉ (Finset.range L).filter (fun j => (a + j) % 2 = 1) :=
      fun hm => hmem (Finset.mem_filter.mp hm).1
    have hnot0 : L ∉ (Finset.range L).filter (fun j => (a + j) % 2 = 0) :=
      fun hm => hmem (Finset.mem_filter.mp hm).1
    by_cases h : (a + L) % 2 = 0
    · simp only [h, ↓reduceIte, Nat.zero_ne_one, Finset.card_insert_of_notMem hnot0]
      rw [pow_succ]
      ring
    · have h1 : (a + L) % 2 = 1 := by omega
      simp only [h1, ↓reduceIte, Nat.one_ne_zero, Finset.card_insert_of_notMem hnot1]
      rw [pow_succ]
      ring

lemma oddCnt_zero_two_mul : ∀ d : ℕ, oddCnt 0 (2 * d) = d
  | 0 => by simp [oddCnt]
  | d + 1 => by
    have h : 2 * (d + 1) = (2 * d + 1) + 1 := by omega
    unfold oddCnt
    rw [h, Finset.range_add_one, Finset.filter_insert, Finset.range_add_one, Finset.filter_insert]
    have h1 : (0 + (2 * d + 1)) % 2 = 1 := by omega
    have h2 : ¬ ((0 + 2 * d) % 2 = 1) := by omega
    have hnot : 2 * d + 1 ∉ (Finset.range (2 * d)).filter (fun j => (0 + j) % 2 = 1) := by
      intro hm
      have := (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)
      omega
    simp only [h1, h2, ↓reduceIte, Finset.card_insert_of_notMem hnot]
    have ih := oddCnt_zero_two_mul d
    unfold oddCnt at ih
    omega

lemma evenCnt_zero_two_mul (d : ℕ) : evenCnt 0 (2 * d) = d := by
  have h1 := oddCnt_add_evenCnt 0 (2 * d)
  have h2 := oddCnt_zero_two_mul d
  omega

def arcVert (L : ℕ) (b0 bL : Bool) (y : Fin L → Bool) (j : ℕ) : Bool :=
  if j = 0 then b0
  else if h : j - 1 < L then y ⟨j - 1, h⟩
  else bL

lemma arc_sum (w : ℕ → ℤ) (a : ℕ) : ∀ (L : ℕ) (b0 bL : Bool),
    ∑ y : Fin L → Bool,
      ∏ j : Fin (L + 1),
        (1 + w (a + j.val) * sgn (arcVert L b0 bL y j.val) * sgn (arcVert L b0 bL y (j.val + 1))) =
    (2 : ℤ) ^ L * (1 + sgn b0 * sgn bL * ∏ j ∈ Finset.range (L + 1), w (a + j))
  | 0, b0, bL => by
    have huniq : (Finset.univ : Finset (Fin 0 → Bool)) = {Fin.elim0} := by
      ext y
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      funext i
      exact Fin.elim0 i
    rw [huniq, Finset.sum_singleton, Fin.prod_univ_one]
    simp [arcVert]
    ring
  | L + 1, b0, bL => by
    let e : (Fin (L + 1) → Bool) ≃ (Fin L → Bool) × Bool :=
      { toFun := fun y => (fun i => y i.castSucc, y (Fin.last L))
        invFun := fun p => Fin.snoc p.1 p.2
        left_inv := fun y => by
          funext i
          refine Fin.lastCases ?_ ?_ i
          · simp
          · intro j
            simp
        right_inv := fun p => by
          ext i
          · simp
          · simp }
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type_right]
    have hstep : ∀ (b : Bool) (y' : Fin L → Bool),
        ∏ j : Fin (L + 2),
          (1 + w (a + j.val) * sgn (arcVert (L + 1) b0 bL (e.symm (y', b)) j.val) *
            sgn (arcVert (L + 1) b0 bL (e.symm (y', b)) (j.val + 1))) =
        (∏ j : Fin (L + 1),
          (1 + w (a + j.val) * sgn (arcVert L b0 b y' j.val) *
            sgn (arcVert L b0 b y' (j.val + 1)))) *
          (1 + w (a + (L + 1)) * sgn b * sgn bL) := by
      intro b y'
      rw [Fin.prod_univ_castSucc]
      congr 1
      · refine Finset.prod_congr rfl (fun j _ => ?_)
        have h1 : arcVert (L + 1) b0 bL (Fin.snoc y' b) j.val = arcVert L b0 b y' j.val := by
          unfold arcVert
          by_cases hj0 : j.val = 0
          · simp [hj0]
          · have hlt : j.val - 1 < L := by omega
            have hlt1 : j.val - 1 < L + 1 := by omega
            simp only [hj0, hlt, hlt1, ↓reduceIte, ↓reduceDIte]
            have hcs : (⟨j.val - 1, hlt1⟩ : Fin (L + 1)) = (⟨j.val - 1, hlt⟩ : Fin L).castSucc := rfl
            rw [hcs, Fin.snoc_castSucc]
        have h2 : arcVert (L + 1) b0 bL (Fin.snoc y' b) (j.val + 1) = arcVert L b0 b y' (j.val + 1) := by
          unfold arcVert
          have hj1 : j.val + 1 ≠ 0 := by omega
          have hlt1 : j.val + 1 - 1 < L + 1 := by omega
          simp only [hj1, hlt1, ↓reduceIte, ↓reduceDIte]
          by_cases hlt : j.val + 1 - 1 < L
          · simp only [hlt, ↓reduceDIte]
            have hcs : (⟨j.val + 1 - 1, hlt1⟩ : Fin (L + 1)) = (⟨j.val + 1 - 1, hlt⟩ : Fin L).castSucc := rfl
            rw [hcs, Fin.snoc_castSucc]
          · simp only [hlt, ↓reduceDIte]
            have hlast : (⟨j.val + 1 - 1, hlt1⟩ : Fin (L + 1)) = Fin.last L := by
              ext
              simp only [Fin.val_last]
              omega
            rw [hlast, Fin.snoc_last]
        simp only [e, Equiv.coe_fn_symm_mk, Fin.val_castSucc, h1, h2]
      · have h1 : arcVert (L + 1) b0 bL (Fin.snoc y' b) (L + 1) = b := by
          unfold arcVert
          have hne : L + 1 ≠ 0 := by omega
          have hlt : L + 1 - 1 < L + 1 := by omega
          simp only [hne, hlt, ↓reduceIte, ↓reduceDIte]
          have hlast : (⟨L + 1 - 1, hlt⟩ : Fin (L + 1)) = Fin.last L := by
            ext
            simp
          rw [hlast, Fin.snoc_last]
        have h2 : arcVert (L + 1) b0 bL (Fin.snoc y' b) (L + 1 + 1) = bL := by
          unfold arcVert
          have hne : L + 1 + 1 ≠ 0 := by omega
          have hlt : ¬ (L + 1 + 1 - 1 < L + 1) := by omega
          simp only [hne, hlt, ↓reduceIte, ↓reduceDIte]
        simp only [e, Equiv.coe_fn_symm_mk, Fin.val_last, h1, h2]
    simp_rw [hstep, ← Finset.sum_mul, arc_sum w a L b0]
    rw [Fintype.sum_bool, Finset.prod_range_succ (n := L + 1), pow_succ]
    simp only [sgn, ↓reduceIte, Bool.false_eq_true]
    ring

lemma diag_le_of_le {a b : ℕ} (hab : a ≤ b) :
    (1 + 2 ^ (a + b)) ^ 2 ≤ (1 + 2 ^ (2 * a)) * (1 + 2 ^ (2 * b)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  have h1 : 2 ^ (a + (a + k)) = 2 ^ (2 * a) * 2 ^ k := by
    rw [← pow_add]
    congr 1
    omega
  have h2 : 2 ^ (2 * (a + k)) = 2 ^ (2 * a) * (2 ^ k * 2 ^ k) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hx : 2 * 2 ^ k ≤ 1 + 2 ^ k * 2 ^ k := by
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
    obtain ⟨y, hy⟩ := Nat.exists_eq_add_of_le hpos
    rw [hy]
    have : 2 * (1 + y) + y * y = 1 + (1 + y) * (1 + y) := by ring
    omega
  have hmul : 2 ^ (2 * a) * (2 * 2 ^ k) ≤ 2 ^ (2 * a) * (1 + 2 ^ k * 2 ^ k) :=
    Nat.mul_le_mul_left _ hx
  have hlhs : (1 + 2 ^ (a + (a + k))) ^ 2 =
      1 + 2 ^ (2 * a) * (2 * 2 ^ k) + (2 ^ (2 * a) * 2 ^ k) ^ 2 := by
    rw [h1]; ring
  have hrhs : (1 + 2 ^ (2 * a)) * (1 + 2 ^ (2 * (a + k))) =
      1 + 2 ^ (2 * a) * (1 + 2 ^ k * 2 ^ k) + (2 ^ (2 * a) * 2 ^ k) ^ 2 := by
    rw [h2]; ring
  omega

lemma diag_lt_of_lt {a b : ℕ} (hab : a < b) :
    (1 + 2 ^ (a + b)) ^ 2 < (1 + 2 ^ (2 * a)) * (1 + 2 ^ (2 * b)) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hab
  have hb : b = a + (k + 1) := by omega
  rw [hb]
  have h1 : 2 ^ (a + (a + (k + 1))) = 2 ^ (2 * a) * 2 ^ (k + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have h2 : 2 ^ (2 * (a + (k + 1))) = 2 ^ (2 * a) * (2 ^ (k + 1) * 2 ^ (k + 1)) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hx : 2 * 2 ^ (k + 1) < 1 + 2 ^ (k + 1) * 2 ^ (k + 1) := by
    have hge : 2 ≤ 2 ^ (k + 1) := by
      rw [pow_succ]
      have := Nat.one_le_pow k 2 (by omega)
      omega
    obtain ⟨y, hy⟩ := Nat.exists_eq_add_of_le hge
    rw [hy]
    have : 2 * (2 + y) + (1 + y) * (1 + y) = 1 + (2 + y) * (2 + y) := by ring
    have hpos : 0 < (1 + y) * (1 + y) := Nat.mul_pos (by omega) (by omega)
    omega
  have hmul : 2 ^ (2 * a) * (2 * 2 ^ (k + 1)) < 2 ^ (2 * a) * (1 + 2 ^ (k + 1) * 2 ^ (k + 1)) :=
    Nat.mul_lt_mul_of_pos_left hx (Nat.pow_pos (by omega))
  have hlhs : (1 + 2 ^ (a + (a + (k + 1)))) ^ 2 =
      1 + 2 ^ (2 * a) * (2 * 2 ^ (k + 1)) + (2 ^ (2 * a) * 2 ^ (k + 1)) ^ 2 := by
    rw [h1]; ring
  have hrhs : (1 + 2 ^ (2 * a)) * (1 + 2 ^ (2 * (a + (k + 1)))) =
      1 + 2 ^ (2 * a) * (1 + 2 ^ (k + 1) * 2 ^ (k + 1)) + (2 ^ (2 * a) * 2 ^ (k + 1)) ^ 2 := by
    rw [h2]; ring
  omega

lemma diag_le_nat (a b : ℕ) :
    (1 + 2 ^ (a + b)) ^ 2 ≤ (1 + 2 ^ (2 * a)) * (1 + 2 ^ (2 * b)) := by
  rcases le_total a b with h | h
  · exact diag_le_of_le h
  · rw [add_comm a b, mul_comm (1 + 2 ^ (2 * a))]
    exact diag_le_of_le h

lemma diag_lt_nat {a b : ℕ} (hne : a ≠ b) :
    (1 + 2 ^ (a + b)) ^ 2 < (1 + 2 ^ (2 * a)) * (1 + 2 ^ (2 * b)) := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact diag_lt_of_lt h
  · rw [add_comm a b, mul_comm (1 + 2 ^ (2 * a))]
    exact diag_lt_of_lt h

lemma prod_le_prod_nat {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℕ)
    (hle : ∀ x ∈ s, f x ≤ g x) : ∏ x ∈ s, f x ≤ ∏ x ∈ s, g x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Nat.mul_le_mul (hle a (Finset.mem_insert_self a s))
      (ih (fun x hx => hle x (Finset.mem_insert_of_mem hx)))

lemma prod_pos_nat {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ)
    (hpos : ∀ x ∈ s, 0 < f x) : 0 < ∏ x ∈ s, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact Nat.mul_pos (hpos a (Finset.mem_insert_self a s))
      (ih (fun x hx => hpos x (Finset.mem_insert_of_mem hx)))

lemma eq_of_prod_two_pow_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (α β : ι → ℕ)
    (heq : ∏ r : ι, ((1 + 2 ^ (2 * α r)) * (1 + 2 ^ (2 * β r))) =
           ∏ r : ι, (1 + 2 ^ (α r + β r)) ^ 2) :
    ∀ r : ι, α r = β r := by
  intro r
  by_contra hne
  have hlt := diag_lt_nat hne
  have hle_rest :
      ∏ x ∈ Finset.univ.erase r, (1 + 2 ^ (α x + β x)) ^ 2 ≤
      ∏ x ∈ Finset.univ.erase r, ((1 + 2 ^ (2 * α x)) * (1 + 2 ^ (2 * β x))) :=
    prod_le_prod_nat _ _ _ (fun x _ => diag_le_nat (α x) (β x))
  have hpos_rest : 0 < ∏ x ∈ Finset.univ.erase r, (1 + 2 ^ (α x + β x)) ^ 2 :=
    prod_pos_nat _ _ (fun x _ => Nat.pow_pos (Nat.add_pos_left Nat.one_pos _))
  have hprod_lt :
      ∏ x : ι, (1 + 2 ^ (α x + β x)) ^ 2 <
      ∏ x : ι, ((1 + 2 ^ (2 * α x)) * (1 + 2 ^ (2 * β x))) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r),
        ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r)]
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt hpos_rest)
      (Nat.mul_le_mul_left _ hle_rest)
  omega

lemma prod_one_add_pow_mod (d W : ℕ) (hd : 0 < d) : ∀ (L : List ℕ),
    (∀ x ∈ L, d ≤ x) →
    (L.map (fun x => 1 + W ^ x)).prod % W ^ (d + 1) = (1 + L.count d * W ^ d) % W ^ (d + 1)
  | [], _ => by simp
  | x :: xs, hmin => by
    have hmin_xs : ∀ y ∈ xs, d ≤ y := fun y hy => hmin y (List.mem_cons_of_mem x hy)
    have ih := prod_one_add_pow_mod d W hd xs hmin_xs
    simp only [List.map_cons, List.prod_cons]
    rw [Nat.mul_mod, ih, ← Nat.mul_mod]
    by_cases hx : x = d
    · subst hx
      have hcnt : (x :: xs).count x = xs.count x + 1 := by simp
      rw [hcnt]
      have hexp : (1 + W ^ x) * (1 + xs.count x * W ^ x) =
          1 + (xs.count x + 1) * W ^ x + (xs.count x * W ^ (x - 1)) * W ^ (x + 1) := by
        have hpow : W ^ x * W ^ x = W ^ (x - 1) * W ^ (x + 1) := by
          rw [← pow_add, ← pow_add]
          congr 1
          omega
        calc (1 + W ^ x) * (1 + xs.count x * W ^ x)
            = 1 + (xs.count x + 1) * W ^ x + xs.count x * (W ^ x * W ^ x) := by ring
          _ = 1 + (xs.count x + 1) * W ^ x + (xs.count x * W ^ (x - 1)) * W ^ (x + 1) := by
              rw [hpow]; ring
      rw [hexp, Nat.add_mul_mod_self_right]
    · have hdx : d + 1 ≤ x := by
        have := hmin x (List.mem_cons_self)
        omega
      have hcnt : (x :: xs).count d = xs.count d :=
        List.count_cons_of_ne hx
      rw [hcnt]
      have hpow : W ^ x = W ^ (x - (d + 1)) * W ^ (d + 1) := by
        rw [← pow_add]
        congr 1
        omega
      have hexp : (1 + W ^ x) * (1 + xs.count d * W ^ d) =
          1 + xs.count d * W ^ d + (W ^ (x - (d + 1)) * (1 + xs.count d * W ^ d)) * W ^ (d + 1) := by
        rw [hpow]
        ring
      rw [hexp, Nat.add_mul_mod_self_right]

lemma list_prod_erase_eq {L : List ℕ} {d : ℕ} (hd : d ∈ L) (f : ℕ → ℕ) :
    f d * ((L.erase d).map f).prod = (L.map f).prod := by
  induction L with
  | nil => simp at hd
  | cons x xs ih =>
    by_cases hxd : x = d
    · subst hxd
      simp [List.erase_cons_head]
    · have hmem : d ∈ xs := by
        rcases List.mem_cons.mp hd with rfl | h
        · exact absurd rfl hxd
        · exact h
      have hbeq : (x == d) = false := beq_false_of_ne hxd
      simp only [List.erase_cons, hbeq, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.prod_cons]
      rw [← mul_assoc, mul_comm (f d) (f x), mul_assoc, ih hmem]

lemma list_count_eq_of_prod_one_add_pow : ∀ (n : ℕ) (L1 L2 : List ℕ),
    L1.length = n →
    (∀ x ∈ L1, 0 < x) → (∀ x ∈ L2, 0 < x) →
    (∀ W : ℕ, (L1.map (fun x => 1 + W ^ x)).prod = (L2.map (fun x => 1 + W ^ x)).prod) →
    ∀ d : ℕ, L1.count d = L2.count d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro L1 L2 hlen h1 h2 hprod
    have hlen2 : L1.length = L2.length := by
      have hW1 := hprod 1
      have hpow : ∀ L : List ℕ, (L.map (fun x => 1 + 1 ^ x)).prod = 2 ^ L.length := by
        intro L
        induction L with
        | nil => simp
        | cons x xs ihL =>
          rw [List.map_cons, List.prod_cons, ihL, List.length_cons, pow_succ, one_pow]
          ring
      rw [hpow L1, hpow L2] at hW1
      exact Nat.pow_right_injective (by omega) hW1
    cases L1 with
    | nil =>
      cases L2 with
      | nil => intro d; rfl
      | cons _ _ => simp at hlen2
    | cons a as =>
      let S : Finset ℕ := ((a :: as) ++ L2).toFinset
      have hne : S.Nonempty := ⟨a, List.mem_toFinset.mpr (by simp)⟩
      let d := S.min' hne
      have hd_mem : d ∈ S := Finset.min'_mem S hne
      have hd_or : d ∈ a :: as ∨ d ∈ L2 :=
        List.mem_append.mp (List.mem_toFinset.mp hd_mem)
      have hd_pos : 0 < d := by
        rcases hd_or with hm | hm
        · exact h1 d hm
        · exact h2 d hm
      have hmin1 : ∀ x ∈ a :: as, d ≤ x := fun x hx =>
        Finset.min'_le S x (List.mem_toFinset.mpr (List.mem_append_left L2 hx))
      have hmin2 : ∀ x ∈ L2, d ≤ x := fun x hx =>
        Finset.min'_le S x (List.mem_toFinset.mpr (List.mem_append_right (a :: as) hx))
      let c1 := (a :: as).count d
      let c2 := L2.count d
      let W := c1 + c2 + 2
      have hW_ge : 2 ≤ W := by omega
      have hW_pow_gt : 1 < W ^ d := by
        calc 1 < 2 := by omega
          _ ≤ W := hW_ge
          _ = W ^ 1 := (pow_one W).symm
          _ ≤ W ^ d := Nat.pow_le_pow_right (by omega) hd_pos
      have hlt1 : 1 + c1 * W ^ d < W ^ (d + 1) := by
        have h1' : (c1 + 1) * W ^ d ≤ W * W ^ d := Nat.mul_le_mul_right _ (by omega)
        have h2' : W ^ (d + 1) = W * W ^ d := by rw [pow_succ, mul_comm]
        have h3' : 1 + c1 * W ^ d < W ^ d + c1 * W ^ d := Nat.add_lt_add_right hW_pow_gt _
        have h4' : W ^ d + c1 * W ^ d = (c1 + 1) * W ^ d := by ring
        omega
      have hlt2 : 1 + c2 * W ^ d < W ^ (d + 1) := by
        have h1' : (c2 + 1) * W ^ d ≤ W * W ^ d := Nat.mul_le_mul_right _ (by omega)
        have h2' : W ^ (d + 1) = W * W ^ d := by rw [pow_succ, mul_comm]
        have h3' : 1 + c2 * W ^ d < W ^ d + c2 * W ^ d := Nat.add_lt_add_right hW_pow_gt _
        have h4' : W ^ d + c2 * W ^ d = (c2 + 1) * W ^ d := by ring
        omega
      have hmod1 := prod_one_add_pow_mod d W hd_pos (a :: as) hmin1
      have hmod2 := prod_one_add_pow_mod d W hd_pos L2 hmin2
      have hmod_eq : (1 + c1 * W ^ d) % W ^ (d + 1) = (1 + c2 * W ^ d) % W ^ (d + 1) := by
        rw [← hmod1, ← hmod2, hprod W]
      rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hmod_eq
      have hc_eq : c1 = c2 := by
        have hm : c1 * W ^ d = c2 * W ^ d := by omega
        exact Nat.eq_of_mul_eq_mul_right (by omega) hm
      have hd1 : d ∈ a :: as := by
        rcases hd_or with hm | hm
        · exact hm
        · have hc2 : 0 < c2 := List.count_pos_iff.mpr hm
          exact List.count_pos_iff.mp (by omega)
      have hd2 : d ∈ L2 := by
        rcases hd_or with hm | hm
        · have hc1 : 0 < c1 := List.count_pos_iff.mpr hm
          exact List.count_pos_iff.mp (by omega)
        · exact hm
      let L1' := (a :: as).erase d
      let L2' := L2.erase d
      have hlen1' : L1'.length < n := by
        have : L1'.length = (a :: as).length - 1 := List.length_erase_of_mem hd1
        simp only [List.length_cons] at this hlen
        omega
      have h1' : ∀ x ∈ L1', 0 < x := fun x hx => h1 x (List.mem_of_mem_erase hx)
      have h2' : ∀ x ∈ L2', 0 < x := fun x hx => h2 x (List.mem_of_mem_erase hx)
      have hprod' : ∀ W : ℕ, (L1'.map (fun x => 1 + W ^ x)).prod = (L2'.map (fun x => 1 + W ^ x)).prod := by
        intro W'
        have hL1 := list_prod_erase_eq hd1 (fun x => 1 + W' ^ x)
        have hL2 := list_prod_erase_eq hd2 (fun x => 1 + W' ^ x)
        have hmul : (1 + W' ^ d) * (L1'.map (fun x => 1 + W' ^ x)).prod =
            (1 + W' ^ d) * (L2'.map (fun x => 1 + W' ^ x)).prod := by
          rw [hL1, hL2, hprod W']
        exact Nat.eq_of_mul_eq_mul_left (by omega) hmul
      have hcnt' := ih L1'.length hlen1' L1' L2' rfl h1' h2' hprod'
      intro x
      have he1 := List.count_erase (a := x) (b := d) (l := a :: as)
      have he2 := List.count_erase (a := x) (b := d) (l := L2)
      have hx_eq := hcnt' x
      by_cases hxd : d = x
      · subst hxd
        exact hc_eq
      · have hbeq : (d == x) = false := beq_false_of_ne hxd
        simp only [L1', L2', hbeq, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] at he1 he2 hx_eq
        omega

lemma count_toList_map {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) (d : ℕ) :
    (s.toList.map f).count d = (s.filter (fun a => f a = d)).card := by
  have hnd : s.toList.Nodup := Finset.nodup_toList s
  have h1 : (s.toList.map f).count d = (s.toList.filter (fun a => decide (f a = d))).length := by
    induction s.toList with
    | nil => simp
    | cons x xs ih =>
      by_cases hfx : f x = d
      · simp [hfx, ih]
      · simp [hfx, ih]
  rw [h1]
  have hsub : (s.toList.filter (fun a => decide (f a = d))).toFinset = s.filter (fun a => f a = d) := by
    ext x
    simp
  rw [← hsub, List.toFinset_card_of_nodup (hnd.filter _)]

lemma card_filter_eq_of_prod_one_add_pow {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (f : α → ℕ) (g : β → ℕ)
    (hf : ∀ a, 0 < f a) (hg : ∀ b, 0 < g b)
    (hprod : ∀ W : ℕ, ∏ a : α, (1 + W ^ f a) = ∏ b : β, (1 + W ^ g b)) :
    ∀ d : ℕ, (Finset.univ.filter (fun a : α => f a = d)).card =
             (Finset.univ.filter (fun b : β => g b = d)).card := by
  let L1 := (Finset.univ : Finset α).toList.map f
  let L2 := (Finset.univ : Finset β).toList.map g
  have h1 : ∀ x ∈ L1, 0 < x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨a, _, rfl⟩
    exact hf a
  have h2 : ∀ x ∈ L2, 0 < x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨b, _, rfl⟩
    exact hg b
  have hp : ∀ W : ℕ, (L1.map (fun x => 1 + W ^ x)).prod = (L2.map (fun x => 1 + W ^ x)).prod := by
    intro W
    simp only [L1, L2, List.map_map]
    rw [Finset.prod_map_toList, Finset.prod_map_toList]
    exact hprod W
  have hcnt := list_count_eq_of_prod_one_add_pow L1.length L1 L2 rfl h1 h2 hp
  intro d
  rw [← count_toList_map, ← count_toList_map]
  exact hcnt d

lemma prod_edge_eq_pow {A : Type*} [Fintype A] {N : ℕ} (hN : Fintype.card A = N)
    (σ : A → A) (x : Bool × A → Bool) (U : ℤ) :
    ∏ i : A, (1 + U * sgn (x (false, i)) * sgn (x (true, σ i))) =
      (1 - U) ^ (Finset.univ.filter (fun i : A => x (false, i) ≠ x (true, σ i))).card *
      (1 + U) ^ (N - (Finset.univ.filter (fun i : A => x (false, i) ≠ x (true, σ i))).card) := by
  simp_rw [one_add_sgn_eq]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 2
  have hadd := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset A))
    (p := fun i : A => x (false, i) ≠ x (true, σ i))
  rw [Finset.card_univ, hN] at hadd
  omega

lemma sum_histGen_eq_card_valid {A : Type*} [Fintype A] [DecidableEq A] {N : ℕ}
    (hN : Fintype.card A = N)
    (σ : A → A) (valid : (Bool × A → Bool) → Prop) [DecidablePred valid] :
    ∑ d : Fin (N + 1) × Fin (N + 1),
      ((Finset.univ : Finset ((Bool × A) → Bool)).filter (fun x =>
        valid x ∧
        (Finset.univ.filter (fun i : A => x (false, i) ≠ x (true, i))).card = d.1.val ∧
        (Finset.univ.filter (fun i : A => x (false, i) ≠ x (true, σ i))).card = d.2.val)).card =
      (Finset.univ.filter valid).card := by
  let g : ((Bool × A) → Bool) → Fin (N + 1) × Fin (N + 1) := fun x =>
    (⟨(Finset.univ.filter (fun i : A => x (false, i) ≠ x (true, i))).card,
        Nat.lt_succ_of_le (by rw [← hN]; exact Finset.card_filter_le _ _)⟩,
     ⟨(Finset.univ.filter (fun i : A => x (false, i) ≠ x (true, σ i))).card,
        Nat.lt_succ_of_le (by rw [← hN]; exact Finset.card_filter_le _ _)⟩)
  symm
  rw [Finset.card_eq_sum_card_fiberwise (f := g) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, g, Prod.ext_iff, Fin.ext_iff]

lemma sum_histGen_poly_eq {A : Type*} [Fintype A] [DecidableEq A] {N : ℕ}
    (hN : Fintype.card A = N)
    (σ : A → A) (valid : (Bool × A → Bool) → Prop) [DecidablePred valid] (U V : ℤ) :
    ∑ d : Fin (N + 1) × Fin (N + 1),
      (((Finset.univ : Finset ((Bool × A) → Bool)).filter (fun x =>
        valid x ∧
        (Finset.univ.filter (fun i : A => x (false, i) ≠ x (true, i))).card = d.1.val ∧
        (Finset.univ.filter (fun i : A => x (false, i) ≠ x (true, σ i))).card = d.2.val)).card : ℤ) *
        ((1 - U) ^ d.1.val * (1 + U) ^ (N - d.1.val) *
         (1 - V) ^ d.2.val * (1 + V) ^ (N - d.2.val)) =
    ∑ x ∈ Finset.univ.filter valid,
      (∏ i : A, (1 + U * sgn (x (false, i)) * sgn (x (true, i)))) *
      (∏ i : A, (1 + V * sgn (x (false, i)) * sgn (x (true, σ i)))) := by
  let g : ((Bool × A) → Bool) → Fin (N + 1) × Fin (N + 1) := fun x =>
    (⟨(Finset.univ.filter (fun i : A => x (false, i) ≠ x (true, i))).card,
        Nat.lt_succ_of_le (by rw [← hN]; exact Finset.card_filter_le _ _)⟩,
     ⟨(Finset.univ.filter (fun i : A => x (false, i) ≠ x (true, σ i))).card,
        Nat.lt_succ_of_le (by rw [← hN]; exact Finset.card_filter_le _ _)⟩)
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter valid) (t := Finset.univ)
        (g := g) (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hfib : (Finset.univ.filter valid).filter (fun x => g x = d) =
      Finset.univ.filter (fun x =>
        valid x ∧
        (Finset.univ.filter (fun i : A => x (false, i) ≠ x (true, i))).card = d.1.val ∧
        (Finset.univ.filter (fun i : A => x (false, i) ≠ x (true, σ i))).card = d.2.val) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, g, Prod.ext_iff, Fin.ext_iff]
  rw [hfib]
  have hconst : ∀ x ∈ Finset.univ.filter (fun x =>
      valid x ∧
      (Finset.univ.filter (fun i : A => x (false, i) ≠ x (true, i))).card = d.1.val ∧
      (Finset.univ.filter (fun i : A => x (false, i) ≠ x (true, σ i))).card = d.2.val),
      (∏ i : A, (1 + U * sgn (x (false, i)) * sgn (x (true, i)))) *
      (∏ i : A, (1 + V * sgn (x (false, i)) * sgn (x (true, σ i)))) =
      (1 - U) ^ d.1.val * (1 + U) ^ (N - d.1.val) *
      (1 - V) ^ d.2.val * (1 + V) ^ (N - d.2.val) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [prod_edge_eq_pow hN (fun i => i) x U, prod_edge_eq_pow hN σ x V]
    simp only [hx.2.1, hx.2.2]
    ring
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]

lemma card_valid_pin {V : Type*} [Fintype V] [DecidableEq V] (p : V → Option Bool) :
    (Finset.univ.filter (fun x : V → Bool => ∀ v, p v = none ∨ p v = some (x v))).card =
      2 ^ (Finset.univ.filter (fun v : V => p v = none)).card := by
  let e : {x : V → Bool // ∀ v, p v = none ∨ p v = some (x v)} ≃
      ({v : V // p v = none} → Bool) :=
    { toFun := fun x v => x.1 v.1
      invFun := fun y =>
        ⟨fun v => match h : p v with
          | none => y ⟨v, h⟩
          | some b => b,
         fun v => by
           dsimp only
           split
           · left; assumption
           · right; assumption⟩
      left_inv := fun x => by
        ext v
        dsimp only
        split
        · rfl
        · rename_i b hb
          rcases x.2 v with h | h
          · rw [hb] at h; cases h
          · rw [hb] at h; cases h; rfl
      right_inv := fun y => by
        funext v
        dsimp only
        split
        · rfl
        · rename_i b hb
          rw [v.2] at hb; cases hb }
  have h1 : (Finset.univ.filter (fun x : V → Bool => ∀ v, p v = none ∨ p v = some (x v))).card =
      Fintype.card {x : V → Bool // ∀ v, p v = none ∨ p v = some (x v)} :=
    (Fintype.card_subtype _).symm
  rw [h1, Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype]

lemma single_cycle_sum (d : ℕ) (U V : ℤ) :
    ∑ y ∈ (Finset.univ : Finset (Bool × Fin (d + 1) → Bool)).filter (fun y => y (false, 0) = false),
      (∏ j : Fin (d + 1), (1 + U * sgn (y (false, j)) * sgn (y (true, j)))) *
      (∏ j : Fin (d + 1), (1 + V * sgn (y (false, j)) * sgn (y (true, j + 1)))) =
    (2 : ℤ) ^ (2 * d + 1) * (1 + (U * V) ^ (d + 1)) := by
  let rIdx : Fin (2 * d + 2) ≃ Bool × Fin (d + 1) :=
    { toFun := fun e =>
        if e.val % 2 = 0 then (false, ⟨e.val / 2, by omega⟩)
        else (true, (⟨e.val / 2, by omega⟩ : Fin (d + 1)) + 1)
      invFun := fun v =>
        match v with
        | (false, j) => ⟨2 * j.val, by omega⟩
        | (true, j) => ⟨2 * (if j.val = 0 then d else j.val - 1) + 1, by
            split_ifs <;> omega⟩
      left_inv := fun e => by
        ext
        by_cases h : e.val % 2 = 0
        · simp only [h, ↓reduceIte]; omega
        · simp only [h, ↓reduceIte]
          have hv : ((⟨e.val / 2, by omega⟩ : Fin (d + 1)) + 1).val = (e.val / 2 + 1) % (d + 1) :=
            fin_val_add_one d _
          rw [hv]
          by_cases hlast : e.val / 2 = d
          · have hm : (e.val / 2 + 1) % (d + 1) = 0 := by rw [hlast]; exact Nat.mod_self (d + 1)
            simp only [hm, ↓reduceIte]
            omega
          · have hm : (e.val / 2 + 1) % (d + 1) = e.val / 2 + 1 := Nat.mod_eq_of_lt (by omega)
            rw [hm]
            have hne0 : e.val / 2 + 1 ≠ 0 := by omega
            simp only [hne0, ↓reduceIte]
            omega
      right_inv := fun v => by
        rcases v with ⟨b, j⟩
        cases b
        · simp
        · dsimp only
          have hne : ¬ ((2 * (if j.val = 0 then d else j.val - 1) + 1) % 2 = 0) := by omega
          simp only [hne, ↓reduceIte]
          refine Prod.ext rfl (Fin.ext ?_)
          rw [fin_val_add_one]
          have hdiv : (2 * (if j.val = 0 then d else j.val - 1) + 1) / 2 =
              if j.val = 0 then d else j.val - 1 := by omega
          dsimp only
          rw [hdiv]
          by_cases hj0 : j.val = 0
          · simp only [hj0, ↓reduceIte]
            exact Nat.mod_self (d + 1)
          · simp only [hj0, ↓reduceIte]
            have : j.val - 1 + 1 = j.val := by omega
            rw [this]
            exact Nat.mod_eq_of_lt j.isLt }
  let eY : {y : Bool × Fin (d + 1) → Bool // y (false, 0) = false} ≃ (Fin (2 * d + 1) → Bool) :=
    { toFun := fun y i => y.1 (rIdx ⟨i.val + 1, by omega⟩)
      invFun := fun z =>
        ⟨fun v => arcVert (2 * d + 1) false false z (rIdx.symm v).val, by
           change arcVert (2 * d + 1) false false z (rIdx.symm (false, 0)).val = false
           have h0 : (rIdx.symm (false, 0)).val = 0 := rfl
           rw [h0]; rfl⟩
      left_inv := fun y => by
        ext v
        dsimp only
        have hv : rIdx (rIdx.symm v) = v := rIdx.apply_symm_apply v
        by_cases h0 : (rIdx.symm v).val = 0
        · have hfv : rIdx.symm v = 0 := Fin.ext h0
          rw [hfv] at hv
          have hv0 : v = (false, 0) := by simpa [rIdx] using hv.symm
          subst hv0
          simp only [arcVert, h0, ↓reduceIte, y.2]
        · have hlt : (rIdx.symm v).val - 1 < 2 * d + 1 := by omega
          simp only [arcVert, h0, hlt, ↓reduceIte, ↓reduceDIte]
          have hmk : (⟨(rIdx.symm v).val - 1 + 1, by omega⟩ : Fin (2 * d + 2)) = rIdx.symm v := by
            ext; dsimp; omega
          rw [hmk, hv]
      right_inv := fun z => by
        funext i
        dsimp only
        rw [rIdx.symm_apply_apply]
        unfold arcVert
        have h1 : i.val + 1 ≠ 0 := by omega
        have h2 : i.val + 1 - 1 < 2 * d + 1 := by omega
        simp only [h1, h2, ↓reduceIte, ↓reduceDIte]
        congr 1 }
  have hsum :
      ∑ y ∈ (Finset.univ : Finset (Bool × Fin (d + 1) → Bool)).filter (fun y => y (false, 0) = false),
        ((∏ j : Fin (d + 1), (1 + U * sgn (y (false, j)) * sgn (y (true, j)))) *
         (∏ j : Fin (d + 1), (1 + V * sgn (y (false, j)) * sgn (y (true, j + 1))))) =
      ∑ z : Fin (2 * d + 1) → Bool,
        ∏ e : Fin (2 * d + 2),
          (1 + edgeWeight U V (0 + e.val) *
            sgn (arcVert (2 * d + 1) false false z e.val) *
            sgn (arcVert (2 * d + 1) false false z (e.val + 1))) := by
    rw [Finset.sum_subtype (s := (Finset.univ : Finset (Bool × Fin (d + 1) → Bool)).filter (fun y => y (false, 0) = false))
          (p := fun y => y (false, 0) = false) (fun _ => by simp)]
    rw [← Equiv.sum_comp eY.symm]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    have hsplit :
        ∏ e : Fin (2 * d + 2),
          (1 + edgeWeight U V (0 + e.val) *
            sgn (arcVert (2 * d + 1) false false z e.val) *
            sgn (arcVert (2 * d + 1) false false z (e.val + 1))) =
        (∏ j : Fin (d + 1),
          (1 + edgeWeight U V (2 * j.val + 1) *
            sgn (arcVert (2 * d + 1) false false z (2 * j.val + 1)) *
            sgn (arcVert (2 * d + 1) false false z (2 * j.val + 2)))) *
        (∏ j : Fin (d + 1),
          (1 + edgeWeight U V (2 * j.val) *
            sgn (arcVert (2 * d + 1) false false z (2 * j.val)) *
            sgn (arcVert (2 * d + 1) false false z (2 * j.val + 1)))) := by
      let evOdd : Bool × Fin (d + 1) ≃ Fin (2 * d + 2) :=
        { toFun := fun p => if p.1 then ⟨2 * p.2.val + 1, by omega⟩ else ⟨2 * p.2.val, by omega⟩
          invFun := fun e => (decide (e.val % 2 = 1), ⟨e.val / 2, by omega⟩)
          left_inv := fun p => by
            rcases p with ⟨b, j⟩
            cases b <;> ext <;> simp <;> omega
          right_inv := fun e => by
            ext
            by_cases h : e.val % 2 = 1
            · simp [h]; omega
            · simp [h]; omega }
      rw [← Equiv.prod_comp evOdd, Fintype.prod_prod_type, Fintype.prod_bool]
      simp only [evOdd, Equiv.coe_fn_mk, ↓reduceIte, Bool.false_eq_true, zero_add]
    rw [hsplit]
    have hr_true : ∀ j : Fin (d + 1), (rIdx.symm (true, j + 1)).val = 2 * j.val + 1 := by
      intro j
      have hval : (j + 1).val = (j.val + 1) % (d + 1) := fin_val_add_one d j
      change 2 * (if (j + 1).val = 0 then d else (j + 1).val - 1) + 1 = 2 * j.val + 1
      rw [hval]
      by_cases hlast : j.val = d
      · have hm : (j.val + 1) % (d + 1) = 0 := by rw [hlast]; exact Nat.mod_self (d + 1)
        rw [hm, hlast]
        simp only [↓reduceIte]
      · have hm : (j.val + 1) % (d + 1) = j.val + 1 := Nat.mod_eq_of_lt (by omega)
        rw [hm]
        have hne0 : j.val + 1 ≠ 0 := by omega
        simp only [hne0, ↓reduceIte]
        omega
    congr 1
    · let shift : Fin (d + 1) ≃ Fin (d + 1) := finAddOneEquiv (d + 1)
      rw [← Equiv.prod_comp shift]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      have hw : edgeWeight U V (2 * j.val + 1) = U := by
        unfold edgeWeight
        have hne : ¬ ((2 * j.val + 1) % 2 = 0) := by omega
        simp only [hne, ↓reduceIte]
      have ha1 : (eY.symm z).1 (true, j + 1) = arcVert (2 * d + 1) false false z (2 * j.val + 1) := by
        change arcVert (2 * d + 1) false false z (rIdx.symm (true, j + 1)).val = _
        rw [hr_true j]
      have ha2 : (eY.symm z).1 (false, j + 1) = arcVert (2 * d + 1) false false z (2 * j.val + 2) := by
        change arcVert (2 * d + 1) false false z (rIdx.symm (false, j + 1)).val = _
        have hval : (j + 1).val = (j.val + 1) % (d + 1) := fin_val_add_one d j
        have hr : (rIdx.symm (false, j + 1)).val = 2 * (j + 1).val := rfl
        rw [hr, hval]
        by_cases hj : j.val < d
        · have hm : (j.val + 1) % (d + 1) = j.val + 1 := Nat.mod_eq_of_lt (by omega)
          rw [hm, show 2 * (j.val + 1) = 2 * j.val + 2 by omega]
        · have hjd : j.val = d := by omega
          have hm : (j.val + 1) % (d + 1) = 0 := by rw [hjd]; exact Nat.mod_self (d + 1)
          rw [hm, hjd]
          simp [arcVert]
      have hsh : shift j = j + 1 := rfl
      rw [hsh, hw, ha1, ha2]
      ring
    · refine Finset.prod_congr rfl (fun j _ => ?_)
      have hw : edgeWeight U V (2 * j.val) = V := by
        unfold edgeWeight
        have : (2 * j.val) % 2 = 0 := by omega
        simp [this]
      have ha1 : (eY.symm z).1 (false, j) = arcVert (2 * d + 1) false false z (2 * j.val) := rfl
      have ha2 : (eY.symm z).1 (true, j + 1) = arcVert (2 * d + 1) false false z (2 * j.val + 1) := by
        change arcVert (2 * d + 1) false false z (rIdx.symm (true, j + 1)).val = _
        rw [hr_true j]
      simp only [hw, ha1, ha2]
  rw [hsum, arc_sum (edgeWeight U V) 0 (2 * d + 1) false false]
  have h2d : 2 * d + 1 + 1 = 2 * (d + 1) := by omega
  rw [h2d, prod_edgeWeight_range, oddCnt_zero_two_mul, evenCnt_zero_two_mul]
  simp only [sgn, Bool.false_eq_true, ↓reduceIte, one_mul, mul_pow]

def nextFn (t b : ℕ) (i : Fin (t + 1) × Fin (b + 1)) : Fin (t + 1) × Fin (b + 1) :=
  if i.2.val + 1 = b + 1 then (i.1 + 1, 0) else (i.1, i.2 + 1)

def phiEquiv (t b : ℕ) : Fin ((t + 1) * (b + 1)) ≃ Fin (t + 1) × Fin (b + 1) where
  toFun q := (⟨q.val / (b + 1), Nat.div_lt_of_lt_mul (by rw [mul_comm (b + 1) (t + 1)]; exact q.isLt)⟩,
              ⟨q.val % (b + 1), Nat.mod_lt _ (by omega)⟩)
  invFun p := ⟨p.1.val * (b + 1) + p.2.val, by
    have h1 : (p.1.val + 1) * (b + 1) ≤ (t + 1) * (b + 1) :=
      Nat.mul_le_mul_right (b + 1) p.1.isLt
    have h2 : p.1.val * (b + 1) + (b + 1) = (p.1.val + 1) * (b + 1) := by ring
    omega⟩
  left_inv q := by
    ext
    dsimp only
    rw [mul_comm, Nat.div_add_mod]
  right_inv p := by
    ext
    · dsimp only
      rw [mul_comm p.1.val (b + 1), Nat.mul_add_div (by omega), Nat.div_eq_of_lt p.2.isLt, add_zero]
    · dsimp only
      rw [Nat.mul_add_mod_of_lt p.2.isLt]

lemma phiEquiv_add_one (t b : ℕ) (q : Fin ((t + 1) * (b + 1))) :
    phiEquiv t b (q + 1) = nextFn t b (phiEquiv t b q) := by
  have hN : 0 < (t + 1) * (b + 1) := Nat.mul_pos (by omega) (by omega)
  have hq1 : (q + 1).val = (q.val + 1) % ((t + 1) * (b + 1)) := by
    have h := fin_val_add_one ((t + 1) * (b + 1) - 1) (q.cast (by omega))
    simpa only [Fin.val_cast, Nat.sub_add_cancel hN, Fin.val_add] using h
  simp only [nextFn, phiEquiv, Equiv.coe_fn_mk]
  by_cases hr : q.val % (b + 1) + 1 = b + 1
  · simp only [hr, ↓reduceIte]
    have hdiv_step : q.val + 1 = (q.val / (b + 1) + 1) * (b + 1) := by
      have hdm := Nat.div_add_mod q.val (b + 1)
      have hmul : (q.val / (b + 1) + 1) * (b + 1) = (b + 1) * (q.val / (b + 1)) + (b + 1) := by ring
      omega
    ext
    · dsimp only
      rw [hq1, fin_val_add_one]
      by_cases hc : q.val / (b + 1) + 1 = t + 1
      · have htot : q.val + 1 = (t + 1) * (b + 1) := by rw [hdiv_step, hc]
        rw [htot, Nat.mod_self, Nat.zero_div, hc, Nat.mod_self]
      · have hlt : q.val + 1 < (t + 1) * (b + 1) := by
          have hc_lt : q.val / (b + 1) + 1 < t + 1 := by
            have := Nat.div_lt_of_lt_mul (by rw [mul_comm (b + 1) (t + 1)]; exact q.isLt)
            omega
          have hmul : (q.val / (b + 1) + 1) * (b + 1) < (t + 1) * (b + 1) :=
            Nat.mul_lt_mul_of_pos_right hc_lt (by omega)
          omega
        rw [Nat.mod_eq_of_lt hlt, hdiv_step, Nat.mul_div_cancel _ (by omega)]
        exact (Nat.mod_eq_of_lt (by
          have := Nat.div_lt_of_lt_mul (by rw [mul_comm (b + 1) (t + 1)]; exact q.isLt)
          omega)).symm
    · dsimp only
      rw [hq1]
      by_cases hc : q.val / (b + 1) + 1 = t + 1
      · have htot : q.val + 1 = (t + 1) * (b + 1) := by rw [hdiv_step, hc]
        rw [htot, Nat.mod_self, Nat.zero_mod]; rfl
      · have hlt : q.val + 1 < (t + 1) * (b + 1) := by
          have hc_lt : q.val / (b + 1) + 1 < t + 1 := by
            have := Nat.div_lt_of_lt_mul (by rw [mul_comm (b + 1) (t + 1)]; exact q.isLt)
            omega
          have hmul : (q.val / (b + 1) + 1) * (b + 1) < (t + 1) * (b + 1) :=
            Nat.mul_lt_mul_of_pos_right hc_lt (by omega)
          omega
        rw [Nat.mod_eq_of_lt hlt, hdiv_step, Nat.mul_mod_left]; rfl
  · simp only [hr, ↓reduceIte]
    have hlt_rem : q.val % (b + 1) + 1 < b + 1 := by
      have := Nat.mod_lt q.val (show 0 < b + 1 by omega)
      omega
    have hlt_q : q.val + 1 < (t + 1) * (b + 1) := by
      have hdm := Nat.div_add_mod q.val (b + 1)
      have hc : q.val / (b + 1) < t + 1 := Nat.div_lt_of_lt_mul (by rw [mul_comm (b + 1) (t + 1)]; exact q.isLt)
      have hmul : (q.val / (b + 1) + 1) * (b + 1) ≤ (t + 1) * (b + 1) :=
        Nat.mul_le_mul_right (b + 1) hc
      have hexp : (q.val / (b + 1) + 1) * (b + 1) = (b + 1) * (q.val / (b + 1)) + (b + 1) := by ring
      omega
    have hdm : q.val + 1 = (b + 1) * (q.val / (b + 1)) + (q.val % (b + 1) + 1) := by
      have := Nat.div_add_mod q.val (b + 1)
      omega
    ext
    · dsimp only
      rw [hq1, Nat.mod_eq_of_lt hlt_q, hdm, Nat.mul_add_div (by omega),
          Nat.div_eq_of_lt hlt_rem, add_zero]
    · dsimp only
      rw [hq1, Nat.mod_eq_of_lt hlt_q, hdm, mul_comm (b + 1), Nat.mul_add_mod_of_lt hlt_rem, fin_val_add_one]
      exact (Nat.mod_eq_of_lt hlt_rem).symm

def ringEquiv (t b : ℕ) :
    Fin (2 * ((t + 1) * (b + 1))) ≃ Bool × (Fin (t + 1) × Fin (b + 1)) :=
  let N := (t + 1) * (b + 1)
  have hN : 0 < N := Nat.mul_pos (by omega) (by omega)
  { toFun := fun e =>
      if e.val % 2 = 0 then (false, phiEquiv t b ⟨e.val / 2, by omega⟩)
      else (true, phiEquiv t b ((⟨e.val / 2, by omega⟩ : Fin N) + 1))
    invFun := fun v =>
      match v with
      | (false, i) => ⟨2 * ((phiEquiv t b).symm i).val, by omega⟩
      | (true, i) =>
          ⟨2 * (if ((phiEquiv t b).symm i).val = 0 then N - 1 else ((phiEquiv t b).symm i).val - 1) + 1,
            by split_ifs <;> omega⟩
    left_inv := fun e => by
      ext
      by_cases h : e.val % 2 = 0
      · simp only [h, ↓reduceIte, Equiv.symm_apply_apply]
        omega
      · simp only [h, ↓reduceIte, Equiv.symm_apply_apply]
        have hq : ((⟨e.val / 2, by omega⟩ : Fin N) + 1).val = (e.val / 2 + 1) % N := by
          have := fin_val_add_one (N - 1) ((⟨e.val / 2, by omega⟩ : Fin N).cast (by omega))
          simpa only [Fin.val_cast, Nat.sub_add_cancel hN, Fin.val_add] using this
        rw [hq]
        by_cases hlast : e.val / 2 = N - 1
        · have hm : (e.val / 2 + 1) % N = 0 := by
            have : e.val / 2 + 1 = N := by omega
            rw [this, Nat.mod_self]
          simp only [hm, ↓reduceIte]
          omega
        · have hm : (e.val / 2 + 1) % N = e.val / 2 + 1 := Nat.mod_eq_of_lt (by omega)
          rw [hm]
          have hne0 : e.val / 2 + 1 ≠ 0 := by omega
          simp only [hne0, ↓reduceIte]
          omega
    right_inv := fun v => by
      rcases v with ⟨side, i⟩
      cases side
      · dsimp only
        have hev : (2 * ((phiEquiv t b).symm i).val) % 2 = 0 := by omega
        simp only [hev, ↓reduceIte]
        refine Prod.ext rfl ?_
        have hdiv : (⟨2 * ((phiEquiv t b).symm i).val / 2, by omega⟩ : Fin N) = (phiEquiv t b).symm i := by
          ext; dsimp only; omega
        rw [hdiv, Equiv.apply_symm_apply]
      · dsimp only
        rw [ite_eq_right_iff.mpr (fun h => by omega)]
        refine Prod.ext rfl ?_
        set q := (phiEquiv t b).symm i
        have hq_lt : (if q.val = 0 then N - 1 else q.val - 1) < N := by split_ifs <;> omega
        have hstep : (⟨(2 * (if q.val = 0 then N - 1 else q.val - 1) + 1) / 2, by omega⟩ : Fin N) + 1 = q := by
          ext
          have hval := fin_val_add_one (N - 1)
            ((⟨(2 * (if q.val = 0 then N - 1 else q.val - 1) + 1) / 2, by omega⟩ : Fin N).cast (by omega))
          have hval' : ((⟨(2 * (if q.val = 0 then N - 1 else q.val - 1) + 1) / 2, by omega⟩ : Fin N) + 1).val =
              ((2 * (if q.val = 0 then N - 1 else q.val - 1) + 1) / 2 + 1) % N := by
            simpa only [Fin.val_cast, Nat.sub_add_cancel hN, Fin.val_add] using hval
          rw [hval']
          have hdiv : (2 * (if q.val = 0 then N - 1 else q.val - 1) + 1) / 2 =
              if q.val = 0 then N - 1 else q.val - 1 := by omega
          rw [hdiv]
          by_cases hq0 : q.val = 0
          · simp only [hq0, ↓reduceIte]
            have : N - 1 + 1 = N := by omega
            rw [this, Nat.mod_self]
          · simp only [hq0, ↓reduceIte]
            have : q.val - 1 + 1 = q.val := by omega
            rw [this]
            exact Nat.mod_eq_of_lt q.isLt
        rw [hstep, Equiv.apply_symm_apply] }

lemma ringEquiv_edge_prod (t b : ℕ) (x : Bool × (Fin (t + 1) × Fin (b + 1)) → Bool) (U V : ℤ) :
    (∏ i : Fin (t + 1) × Fin (b + 1), (1 + U * sgn (x (false, i)) * sgn (x (true, i)))) *
    (∏ i : Fin (t + 1) × Fin (b + 1), (1 + V * sgn (x (false, i)) * sgn (x (true, nextFn t b i)))) =
    ∏ e : Fin (2 * ((t + 1) * (b + 1))),
      (1 + edgeWeight U V e.val *
        sgn (x (ringEquiv t b e)) * sgn (x (ringEquiv t b (e + 1)))) := by
  let N := (t + 1) * (b + 1)
  have hN : 0 < N := Nat.mul_pos (by omega) (by omega)
  let evOdd : Bool × Fin N ≃ Fin (2 * N) :=
    { toFun := fun p => if p.1 then ⟨2 * p.2.val + 1, by omega⟩ else ⟨2 * p.2.val, by omega⟩
      invFun := fun e => (decide (e.val % 2 = 1), ⟨e.val / 2, by omega⟩)
      left_inv := fun p => by rcases p with ⟨side, q⟩; cases side <;> ext <;> simp <;> omega
      right_inv := fun e => by
        ext
        by_cases h : e.val % 2 = 1
        · simp [h]; omega
        · simp [h]; omega }
  rw [← Equiv.prod_comp evOdd]
  conv_rhs => rw [Fintype.prod_prod_type, Fintype.prod_bool]
  congr 1
  · have : NeZero N := ⟨Nat.ne_of_gt hN⟩
    let shiftPhi : Fin N ≃ Fin (t + 1) × Fin (b + 1) := (finAddOneEquiv N).trans (phiEquiv t b)
    rw [← Equiv.prod_comp shiftPhi]
    refine Finset.prod_congr rfl (fun q _ => ?_)
    have hw : edgeWeight U V (2 * q.val + 1) = U := by
      unfold edgeWeight
      have hne : ¬ ((2 * q.val + 1) % 2 = 0) := by omega
      simp only [hne, ↓reduceIte]
    have h1 : ringEquiv t b ⟨2 * q.val + 1, by omega⟩ = (true, phiEquiv t b (q + 1)) := by
      unfold ringEquiv
      have hne : ¬ ((2 * q.val + 1) % 2 = 0) := by omega
      simp only [Equiv.coe_fn_mk, hne, ↓reduceIte]
      have hdiv : (⟨(2 * q.val + 1) / 2, by omega⟩ : Fin N) = q := by ext; dsimp only; omega
      rw [hdiv]
    have h2 : ringEquiv t b ((⟨2 * q.val + 1, by omega⟩ : Fin (2 * N)) + 1) = (false, phiEquiv t b (q + 1)) := by
      have hval2 : ((⟨2 * q.val + 1, by omega⟩ : Fin (2 * N)) + 1).val = (2 * q.val + 2) % (2 * N) := by
        have := fin_val_add_one (2 * N - 1) ((⟨2 * q.val + 1, by omega⟩ : Fin (2 * N)).cast (by omega))
        simpa only [Fin.val_cast, Nat.sub_add_cancel (show 0 < 2 * N by omega), Fin.val_add] using this
      have hvalq : (q + 1).val = (q.val + 1) % N := by
        have := fin_val_add_one (N - 1) (q.cast (by omega))
        simpa only [Fin.val_cast, Nat.sub_add_cancel hN, Fin.val_add] using this
      unfold ringEquiv
      have hev : (((⟨2 * q.val + 1, by omega⟩ : Fin (2 * N)) + 1).val) % 2 = 0 := by
        rw [hval2]
        have : 2 * q.val + 2 = 2 * (q.val + 1) := by omega
        rw [this, Nat.mul_mod_mul_left]
        omega
      simp only [Equiv.coe_fn_mk, hev, ↓reduceIte]
      refine Prod.ext rfl (congrArg (phiEquiv t b) (Fin.ext ?_))
      dsimp only
      rw [hval2, hvalq]
      have : 2 * q.val + 2 = 2 * (q.val + 1) := by omega
      rw [this, Nat.mul_mod_mul_left, Nat.mul_div_right _ (by omega)]
    have hsh : shiftPhi q = phiEquiv t b (q + 1) := rfl
    simp only [evOdd, Equiv.coe_fn_mk, ↓reduceIte, hsh, hw, h1, h2]
    ring
  · rw [← Equiv.prod_comp (phiEquiv t b)]
    refine Finset.prod_congr rfl (fun q _ => ?_)
    have hw : edgeWeight U V (2 * q.val) = V := by
      unfold edgeWeight
      have : (2 * q.val) % 2 = 0 := by omega
      simp [this]
    have h1 : ringEquiv t b ⟨2 * q.val, by omega⟩ = (false, phiEquiv t b q) := by
      unfold ringEquiv
      have hev : (2 * q.val) % 2 = 0 := by omega
      simp only [Equiv.coe_fn_mk, hev, ↓reduceIte]
      have hdiv : (⟨2 * q.val / 2, by omega⟩ : Fin N) = q := by ext; dsimp only; omega
      rw [hdiv]
    have h2 : ringEquiv t b ((⟨2 * q.val, by omega⟩ : Fin (2 * N)) + 1) = (true, nextFn t b (phiEquiv t b q)) := by
      have hval2 : ((⟨2 * q.val, by omega⟩ : Fin (2 * N)) + 1).val = 2 * q.val + 1 := by
        have := fin_val_add_one (2 * N - 1) ((⟨2 * q.val, by omega⟩ : Fin (2 * N)).cast (by omega))
        have h' : ((⟨2 * q.val, by omega⟩ : Fin (2 * N)) + 1).val = (2 * q.val + 1) % (2 * N) := by
          simpa only [Fin.val_cast, Nat.sub_add_cancel (show 0 < 2 * N by omega), Fin.val_add] using this
        rw [h', Nat.mod_eq_of_lt (by omega)]
      unfold ringEquiv
      have hne : ¬ (((⟨2 * q.val, by omega⟩ : Fin (2 * N)) + 1).val % 2 = 0) := by
        rw [hval2]; omega
      simp only [Equiv.coe_fn_mk, hne, ↓reduceIte]
      refine Prod.ext rfl ?_
      have hdiv : (⟨((⟨2 * q.val, by omega⟩ : Fin (2 * N)) + 1).val / 2, by omega⟩ : Fin N) = q := by
        ext; dsimp only; rw [hval2]; omega
      rw [hdiv, phiEquiv_add_one]
    simp only [evOdd, Equiv.coe_fn_mk, Bool.false_eq_true, ↓reduceIte, hw, h1, h2]

lemma ring_poly_of_all_false (t b : ℕ)
    (p : Bool × (Fin (t + 1) × Fin (b + 1)) → Option Bool)
    (h0 : p (ringEquiv t b 0) ≠ none)
    (hall : ∀ v, p v ≠ none → p v = some false)
    (U V : ℤ) :
    let N := (t + 1) * (b + 1)
    let S := (Finset.univ : Finset (Fin (2 * N))).filter (fun e => p (ringEquiv t b e) ≠ none)
    let k := S.card
    let emb := S.orderEmbOfFin rfl
    let pos : ℕ → ℕ := fun r => if hr : r < k then (emb ⟨r, hr⟩).val else 2 * N
    ∑ x ∈ Finset.univ.filter (fun x : Bool × (Fin (t + 1) × Fin (b + 1)) → Bool =>
        ∀ v, p v = none ∨ p v = some (x v)),
      (∏ i : Fin (t + 1) × Fin (b + 1), (1 + U * sgn (x (false, i)) * sgn (x (true, i)))) *
      (∏ i : Fin (t + 1) × Fin (b + 1), (1 + V * sgn (x (false, i)) * sgn (x (true, nextFn t b i)))) =
    (2 : ℤ) ^ (2 * N - k) *
      ∏ r : Fin k,
        (1 + U ^ oddCnt (pos r.val) (pos (r.val + 1) - pos r.val) *
             V ^ evenCnt (pos r.val) (pos (r.val + 1) - pos r.val)) := by
  intro N S k emb pos
  have hN : 0 < N := Nat.mul_pos (by omega) (by omega)
  have h0S : (0 : Fin (2 * N)) ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h0
  have hk_pos : 0 < k := Finset.card_pos.mpr ⟨0, h0S⟩
  have hpos_mono : ∀ r1 r2 : ℕ, r1 < r2 → r2 ≤ k → pos r1 < pos r2 := by
    intro r1 r2 hlt hle
    have hr1 : r1 < k := by omega
    by_cases hr2 : r2 < k
    · simp only [pos, hr1, hr2, ↓reduceDIte]
      exact emb.strictMono (show (⟨r1, hr1⟩ : Fin k) < ⟨r2, hr2⟩ from hlt)
    · simp only [pos, hr1, hr2, ↓reduceDIte]
      exact (emb ⟨r1, hr1⟩).isLt
  have hpos_le : ∀ r1 r2 : ℕ, r1 ≤ r2 → r2 ≤ k → pos r1 ≤ pos r2 := by
    intro r1 r2 hle1 hle2
    rcases eq_or_lt_of_le hle1 with rfl | hlt
    · exact le_rfl
    · exact le_of_lt (hpos_mono r1 r2 hlt hle2)
  have hpos0 : pos 0 = 0 := by
    have h0mem : (0 : Fin (2 * N)) ∈ Set.range emb := by
      rw [Finset.range_orderEmbOfFin]
      exact h0S
    rcases h0mem with ⟨r0, hr0⟩
    have hle : emb ⟨0, hk_pos⟩ ≤ emb r0 := emb.monotone (Nat.zero_le r0.val)
    rw [hr0] at hle
    have h0val : (emb ⟨0, hk_pos⟩).val = 0 := Nat.eq_zero_of_le_zero hle
    simp only [pos, hk_pos, ↓reduceDIte, h0val]
  have hposk : pos k = 2 * N := by
    simp only [pos, lt_irrefl, ↓reduceDIte]
  let lenR : Fin k → ℕ := fun r => pos (r.val + 1) - pos r.val - 1
  have hlenR_add : ∀ r : Fin k, lenR r + 1 = pos (r.val + 1) - pos r.val := by
    intro r
    have hlt := hpos_mono r.val (r.val + 1) (by omega) r.isLt
    dsimp only [lenR]
    omega
  have hsum_len : ∑ r : Fin k, (lenR r + 1) = 2 * N := by
    have h1 : ∀ n : ℕ, n ≤ k → ∑ r ∈ Finset.range n, (pos (r + 1) - pos r) = pos n - pos 0 := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ihn =>
        intro hn
        rw [Finset.sum_range_succ, ihn (by omega)]
        have hle1 := hpos_le 0 n (Nat.zero_le n) (by omega)
        have hle2 := hpos_le n (n + 1) (by omega) hn
        omega
    have hfin : ∑ r : Fin k, (lenR r + 1) = ∑ r ∈ Finset.range k, (pos (r + 1) - pos r) := by
      rw [← Fin.sum_univ_eq_sum_range (fun r => pos (r + 1) - pos r)]
      exact Finset.sum_congr rfl (fun r _ => hlenR_add r)
    rw [hfin, h1 k le_rfl, hposk, hpos0, Nat.sub_zero]
  have hsum_lenR : ∑ r : Fin k, lenR r = 2 * N - k := by
    have hadd : (∑ r : Fin k, lenR r) + k = 2 * N := by
      have : (∑ r : Fin k, lenR r) + ∑ _r : Fin k, 1 = ∑ r : Fin k, (lenR r + 1) := by
        rw [← Finset.sum_add_distrib]
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using this.trans hsum_len
    omega
  let segFun : ((r : Fin k) × Fin (lenR r + 1)) → Fin (2 * N) := fun q =>
    ⟨pos q.1.val + q.2.val, by
      have h1 := hlenR_add q.1
      have h2 := hpos_le (q.1.val + 1) k q.1.isLt le_rfl
      rw [hposk] at h2
      omega⟩
  have hseg_inj : Function.Injective segFun := by
    intro a b hab
    have hval : pos a.1.val + a.2.val = pos b.1.val + b.2.val := congrArg Fin.val hab
    have hr_eq : a.1 = b.1 := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
      · have h1 := hlenR_add a.1
        have h2 := hpos_le (a.1.val + 1) b.1.val hlt (le_of_lt b.1.isLt)
        omega
      · have h1 := hlenR_add b.1
        have h2 := hpos_le (b.1.val + 1) a.1.val hlt (le_of_lt a.1.isLt)
        omega
    rcases a with ⟨r1, j1⟩
    rcases b with ⟨r2, j2⟩
    dsimp only at hval hr_eq
    subst hr_eq
    congr 1
    ext
    omega
  have hseg_card : Fintype.card ((r : Fin k) × Fin (lenR r + 1)) = Fintype.card (Fin (2 * N)) := by
    rw [Fintype.card_sigma, Fintype.card_fin]
    simp only [Fintype.card_fin]
    exact hsum_len
  let segEquiv : ((r : Fin k) × Fin (lenR r + 1)) ≃ Fin (2 * N) :=
    Equiv.ofBijective segFun ((Fintype.bijective_iff_injective_and_card segFun).mpr ⟨hseg_inj, hseg_card⟩)
  have hpos_fin : ∀ r : Fin k, pos r.val = (emb r).val := by
    intro r
    simp only [pos, r.isLt, ↓reduceDIte]
    rfl
  have hseg_mem_S : ∀ (r : Fin k) (j : Fin (lenR r + 1)),
      segEquiv ⟨r, j⟩ ∈ S ↔ j.val = 0 := by
    intro r j
    constructor
    · intro hmem
      have hrng : segEquiv ⟨r, j⟩ ∈ Set.range emb := by
        rw [Finset.range_orderEmbOfFin]
        exact hmem
      rcases hrng with ⟨r', hr'⟩
      by_contra hj0
      have h1 := hlenR_add r
      have hval : (emb r').val = pos r.val + j.val := by
        simpa [segEquiv, segFun] using congrArg Fin.val hr'
      have hlt_r : pos r.val < pos r'.val := by
        rw [hpos_fin r', hval]
        omega
      have hr_lt : r.val < r'.val := by
        by_contra hge
        have hle := hpos_le r'.val r.val (by omega) (le_of_lt r.isLt)
        omega
      have hle_next : pos (r.val + 1) ≤ pos r'.val := hpos_le (r.val + 1) r'.val hr_lt (le_of_lt r'.isLt)
      rw [hpos_fin r', hval] at hle_next
      omega
    · intro hj0
      have heq : segEquiv ⟨r, j⟩ = emb r := by
        ext
        simp only [segEquiv, Equiv.ofBijective_apply, segFun, hj0, add_zero, hpos_fin r]
      rw [heq]
      exact Finset.orderEmbOfFin_mem S rfl r
  have hvalid_iff : ∀ x : Bool × (Fin (t + 1) × Fin (b + 1)) → Bool,
      (∀ v, p v = none ∨ p v = some (x v)) ↔ ∀ e ∈ S, x (ringEquiv t b e) = false := by
    intro x
    constructor
    · intro hx e he
      have hne : p (ringEquiv t b e) ≠ none := (Finset.mem_filter.mp he).2
      have hsf := hall (ringEquiv t b e) hne
      rcases hx (ringEquiv t b e) with h | h
      · exact absurd h hne
      · rw [hsf] at h
        exact (Option.some.inj h).symm
    · intro hx v
      by_cases hv : p v = none
      · left; exact hv
      · right
        have hsf := hall v hv
        rw [hsf]
        have he : (ringEquiv t b).symm v ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
          exact hv
        have hxv := hx _ he
        rw [Equiv.apply_symm_apply] at hxv
        rw [hxv]
  let eAssign : {x : Bool × (Fin (t + 1) × Fin (b + 1)) → Bool // ∀ v, p v = none ∨ p v = some (x v)} ≃
      ((r : Fin k) → (Fin (lenR r) → Bool)) :=
    { toFun := fun x r i =>
        x.1 (ringEquiv t b (segEquiv ⟨r, ⟨i.val + 1, by omega⟩⟩))
      invFun := fun z =>
        ⟨fun v =>
           let q := segEquiv.symm ((ringEquiv t b).symm v)
           arcVert (lenR q.1) false false (z q.1) q.2.val,
         (hvalid_iff _).mpr (fun e he => by
           rw [Equiv.symm_apply_apply]
           have h0 : (segEquiv.symm e).2.val = 0 := by
             have hmem : segEquiv (segEquiv.symm e) ∈ S := by simpa using he
             exact (hseg_mem_S _ _).mp hmem
           simp only [arcVert, h0, ↓reduceIte])⟩
      left_inv := fun x => by
        ext v
        dsimp only
        set q := segEquiv.symm ((ringEquiv t b).symm v)
        have hq : segEquiv q = (ringEquiv t b).symm v := segEquiv.apply_symm_apply _
        by_cases hj0 : q.2.val = 0
        · simp only [arcVert, hj0, ↓reduceIte]
          have hmem : (ringEquiv t b).symm v ∈ S := by
            rw [← hq]
            exact (hseg_mem_S q.1 q.2).mpr hj0
          have hx := (hvalid_iff x.1).mp x.2 _ hmem
          rw [Equiv.apply_symm_apply] at hx
          exact hx.symm
        · have hlt : q.2.val - 1 < lenR q.1 := by omega
          simp only [arcVert, hj0, hlt, ↓reduceIte, ↓reduceDIte]
          rw [sigma_fin_pred_succ q hj0, hq, Equiv.apply_symm_apply]
      right_inv := fun z => by
        funext r i
        dsimp only
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        unfold arcVert
        have h1 : i.val + 1 ≠ 0 := by omega
        have h2 : i.val + 1 - 1 < lenR r := by omega
        simp only [h1, h2, ↓reduceIte, ↓reduceDIte]
        congr 1 }
  rw [Finset.sum_subtype (s := Finset.univ.filter _) (p := fun x => ∀ v, p v = none ∨ p v = some (x v))
        (fun _ => by simp)]
  rw [← Equiv.sum_comp eAssign.symm]
  have hterm : ∀ z : (r : Fin k) → (Fin (lenR r) → Bool),
      (∏ i : Fin (t + 1) × Fin (b + 1), (1 + U * sgn ((eAssign.symm z).1 (false, i)) * sgn ((eAssign.symm z).1 (true, i)))) *
      (∏ i : Fin (t + 1) × Fin (b + 1), (1 + V * sgn ((eAssign.symm z).1 (false, i)) * sgn ((eAssign.symm z).1 (true, nextFn t b i)))) =
      ∏ r : Fin k, ∏ j : Fin (lenR r + 1),
        (1 + edgeWeight U V (pos r.val + j.val) *
          sgn (arcVert (lenR r) false false (z r) j.val) *
          sgn (arcVert (lenR r) false false (z r) (j.val + 1))) := by
    intro z
    rw [ringEquiv_edge_prod t b (eAssign.symm z).1 U V]
    rw [← Equiv.prod_comp segEquiv, Fintype.prod_sigma]
    refine Finset.prod_congr rfl (fun r _ => Finset.prod_congr rfl (fun j _ => ?_))
    have hv1 : (eAssign.symm z).1 (ringEquiv t b (segEquiv ⟨r, j⟩)) =
        arcVert (lenR r) false false (z r) j.val := by
      dsimp only [eAssign, Equiv.coe_fn_symm_mk]
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    have hv2 : (eAssign.symm z).1 (ringEquiv t b (segEquiv ⟨r, j⟩ + 1)) =
        arcVert (lenR r) false false (z r) (j.val + 1) := by
      by_cases hj : j.val < lenR r
      · have hnext : segEquiv ⟨r, j⟩ + 1 = segEquiv ⟨r, ⟨j.val + 1, by omega⟩⟩ := by
          ext
          have hval := fin_val_add_one (2 * N - 1) ((segEquiv ⟨r, j⟩).cast (by omega))
          have hval' : (segEquiv ⟨r, j⟩ + 1).val = ((segEquiv ⟨r, j⟩).val + 1) % (2 * N) := by
            simpa only [Fin.val_cast, Nat.sub_add_cancel (show 0 < 2 * N by omega), Fin.val_add] using hval
          rw [hval']
          have hlt : (segEquiv ⟨r, j⟩).val + 1 < 2 * N := by
            have h1 := hlenR_add r
            have h2 := hpos_le (r.val + 1) k r.isLt le_rfl
            rw [hposk] at h2
            simp only [segEquiv, Equiv.ofBijective_apply, segFun]
            omega
          rw [Nat.mod_eq_of_lt hlt]
          simp only [segEquiv, Equiv.ofBijective_apply, segFun]
          omega
        rw [hnext]
        dsimp only [eAssign, Equiv.coe_fn_symm_mk]
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      · have hjlast : j.val = lenR r := by omega
        have hmemS : segEquiv ⟨r, j⟩ + 1 ∈ S := by
          have hval := fin_val_add_one (2 * N - 1) ((segEquiv ⟨r, j⟩).cast (by omega))
          have hval' : (segEquiv ⟨r, j⟩ + 1).val = ((segEquiv ⟨r, j⟩).val + 1) % (2 * N) := by
            simpa only [Fin.val_cast, Nat.sub_add_cancel (show 0 < 2 * N by omega), Fin.val_add] using hval
          have hsum_eq : (segEquiv ⟨r, j⟩).val + 1 = pos (r.val + 1) := by
            have h1 := hlenR_add r
            simp only [segEquiv, Equiv.ofBijective_apply, segFun, hjlast]
            omega
          by_cases hr1 : r.val + 1 < k
          · have heq : segEquiv ⟨r, j⟩ + 1 = emb ⟨r.val + 1, hr1⟩ := by
              ext
              rw [hval', hsum_eq]
              simp only [pos, hr1, ↓reduceDIte]
              exact Nat.mod_eq_of_lt (emb ⟨r.val + 1, hr1⟩).isLt
            rw [heq]
            exact Finset.orderEmbOfFin_mem S rfl _
          · have hrk : r.val + 1 = k := by omega
            have heq : segEquiv ⟨r, j⟩ + 1 = 0 := by
              ext
              rw [hval', hsum_eq, hrk, hposk, Nat.mod_self]
              rfl
            rw [heq]
            exact h0S
        have hfalse := (hvalid_iff (eAssign.symm z).1).mp (eAssign.symm z).2 _ hmemS
        rw [hfalse]
        unfold arcVert
        have hne : j.val + 1 ≠ 0 := by omega
        simp only [hne, Nat.add_sub_cancel, hj, ↓reduceIte, ↓reduceDIte]
    have hval_seg : (segEquiv ⟨r, j⟩).val = pos r.val + j.val := rfl
    rw [hval_seg, hv1, hv2]
  simp_rw [hterm]
  rw [← Fintype.prod_sum (f := fun (r : Fin k) (y : Fin (lenR r) → Bool) =>
        ∏ j : Fin (lenR r + 1),
          (1 + edgeWeight U V (pos r.val + j.val) *
            sgn (arcVert (lenR r) false false y j.val) *
            sgn (arcVert (lenR r) false false y (j.val + 1))))]
  simp_rw [arc_sum (edgeWeight U V)]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum_lenR]
  congr 1
  refine Finset.prod_congr rfl (fun r _ => ?_)
  rw [hlenR_add r, prod_edgeWeight_range]
  simp only [sgn, Bool.false_eq_true, ↓reduceIte, one_mul]

def pinOf (t b : ℕ) (f : (Fin (t + 1) × Fin 3) → ℕ) :
    Bool × (Fin (t + 1) × Fin (b + 1)) → Option Bool :=
  fun v =>
    if v.1 = false ∧
      (v.2.2.val = 0 ∨ v.2.2.val = f (v.2.1, 0) ∨ v.2.2.val = f (v.2.1, 0) + f (v.2.1, 1))
    then some false else none

lemma pinOf_inj (t b : ℕ) (f1 f2 : (Fin (t + 1) × Fin 3) → ℕ)
    (hpos1 : ∀ k, 0 < f1 k) (hpos2 : ∀ k, 0 < f2 k)
    (hsum1 : ∀ c, ∑ u : Fin 3, f1 (c, u) = b + 1)
    (hsum2 : ∀ c, ∑ u : Fin 3, f2 (c, u) = b + 1)
    (heq : pinOf t b f1 = pinOf t b f2) : f1 = f2 := by
  funext ⟨c, u⟩
  have hsum1c : f1 (c, 0) + f1 (c, 1) + f1 (c, 2) = b + 1 := by
    have := hsum1 c
    rw [Fin.sum_univ_three] at this
    exact this
  have hsum2c : f2 (c, 0) + f2 (c, 1) + f2 (c, 2) = b + 1 := by
    have := hsum2 c
    rw [Fin.sum_univ_three] at this
    exact this
  have hp10 := hpos1 (c, 0); have hp11 := hpos1 (c, 1); have hp12 := hpos1 (c, 2)
  have hp20 := hpos2 (c, 0); have hp21 := hpos2 (c, 1); have hp22 := hpos2 (c, 2)
  have hiff : ∀ r : Fin (b + 1),
      (r.val = 0 ∨ r.val = f1 (c, 0) ∨ r.val = f1 (c, 0) + f1 (c, 1)) ↔
      (r.val = 0 ∨ r.val = f2 (c, 0) ∨ r.val = f2 (c, 0) + f2 (c, 1)) := by
    intro r
    have hval := congrFun heq (false, (c, r))
    unfold pinOf at hval
    dsimp only at hval
    by_cases h1 : r.val = 0 ∨ r.val = f1 (c, 0) ∨ r.val = f1 (c, 0) + f1 (c, 1) <;>
    by_cases h2 : r.val = 0 ∨ r.val = f2 (c, 0) ∨ r.val = f2 (c, 0) + f2 (c, 1)
    · exact ⟨fun _ => h2, fun _ => h1⟩
    · rw [ite_eq_left_iff.mpr (fun hn => absurd ⟨rfl, h1⟩ hn),
          ite_eq_right_iff.mpr (fun hy => absurd hy.2 h2)] at hval
      cases hval
    · rw [ite_eq_right_iff.mpr (fun hy => absurd hy.2 h1),
          ite_eq_left_iff.mpr (fun hn => absurd ⟨rfl, h2⟩ hn)] at hval
      cases hval
    · exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  have ha1 := (hiff ⟨f1 (c, 0), by omega⟩).mp (Or.inr (Or.inl rfl))
  have ha2 := (hiff ⟨f2 (c, 0), by omega⟩).mpr (Or.inr (Or.inl rfl))
  have hb1 := (hiff ⟨f1 (c, 0) + f1 (c, 1), by omega⟩).mp (Or.inr (Or.inr rfl))
  have hb2 := (hiff ⟨f2 (c, 0) + f2 (c, 1), by omega⟩).mpr (Or.inr (Or.inr rfl))
  dsimp only at ha1 ha2 hb1 hb2
  have h0 : f1 (c, 0) = f2 (c, 0) := by omega
  have h1 : f1 (c, 1) = f2 (c, 1) := by omega
  have h2 : f1 (c, 2) = f2 (c, 2) := by omega
  rcases u with ⟨_ | _ | _ | u, hu⟩
  · exact h0
  · exact h1
  · exact h2
  · omega

lemma hist_pinOf_eq_source (t b : ℕ) (s : (Fin (t + 1) × Fin 3) → ℕ)
    (hsum : (∑ i : Fin (t + 1) × Fin 3, (s i + 1)) = (t + 1) * (b + 1))
    (π : Equiv.Perm (Fin (t + 1) × Fin 3))
    (hπ : ∀ c : Fin (t + 1), (∑ u : Fin 3, (s (π (c, u)) + 1)) = b + 1)
    (d : Fin ((t + 1) * (b + 1) + 1) × Fin ((t + 1) * (b + 1) + 1)) :
    let K := Fin (t + 1) × Fin 3
    let I := (i : K) × Fin (s i + 1)
    let T := Fin (t + 1) × Fin (b + 1)
    let p := pinOf t b (fun k => s (π k) + 1)
    ((Finset.univ : Finset ((Bool × T) → Bool)).filter (fun x =>
      (∀ v, p v = none ∨ p v = some (x v)) ∧
      (Finset.univ.filter (fun i : T => x (false, i) ≠ x (true, i))).card = d.1.val ∧
      (Finset.univ.filter (fun i : T => x (false, i) ≠ x (true, nextFn t b i))).card = d.2.val)).card =
    ((Finset.univ : Finset ((Bool × I) → Bool)).filter (fun x =>
      (∀ i : K, x (false, (⟨i, 0⟩ : I)) = false) ∧
      (Finset.univ.filter (fun i : I => x (false, i) ≠ x (true, i))).card = d.1.val ∧
      (Finset.univ.filter (fun i : I => x (false, i) ≠ x (true, (⟨i.1, i.2 + 1⟩ : I)))).card = d.2.val)).card := by
  intro K I T p
  let off : Fin (t + 1) → Fin 3 → ℕ := fun c u =>
    match u.val with
    | 0 => 0
    | 1 => s (π (c, 0)) + 1
    | _ => (s (π (c, 0)) + 1) + (s (π (c, 1)) + 1)
  have hsumc : ∀ c : Fin (t + 1),
      (s (π (c, 0)) + 1) + (s (π (c, 1)) + 1) + (s (π (c, 2)) + 1) = b + 1 := by
    intro c
    have := hπ c
    rw [Fin.sum_univ_three] at this
    exact this
  have hoff_lt : ∀ (c : Fin (t + 1)) (u : Fin 3), off c u + (s (π (c, u)) + 1) ≤ b + 1 := by
    intro c u
    have hc := hsumc c
    rcases u with ⟨_ | _ | _ | u, hu⟩
    · simp only [off]; exact Nat.le_of_lt_succ (by change 0 + (s (π (c, 0)) + 1) < b + 1 + 1; omega)
    · simp only [off]; exact Nat.le_of_lt_succ (by change (s (π (c, 0)) + 1) + (s (π (c, 1)) + 1) < b + 1 + 1; omega)
    · simp only [off]; exact Nat.le_of_lt_succ (by change (s (π (c, 0)) + 1) + (s (π (c, 1)) + 1) + (s (π (c, 2)) + 1) < b + 1 + 1; omega)
    · omega
  let psiFun : I → T := fun q =>
    let cu := π.symm q.1
    (cu.1, ⟨off cu.1 cu.2 + q.2.val, by
      have h1 := hoff_lt cu.1 cu.2
      have hcu_eq : (cu.1, cu.2) = cu := rfl
      have h2 : q.2.val < s (π (cu.1, cu.2)) + 1 := by
        rw [hcu_eq]
        dsimp only [cu]
        rw [Equiv.apply_symm_apply]
        exact q.2.isLt
      omega⟩)
  have hpsi_inj : Function.Injective psiFun := by
    intro a b hab
    have hc : (π.symm a.1).1 = (π.symm b.1).1 := by
      have h := congrArg Prod.fst hab
      exact h
    have hr : off (π.symm a.1).1 (π.symm a.1).2 + a.2.val =
              off (π.symm b.1).1 (π.symm b.1).2 + b.2.val := by
      have h := congrArg (fun z : T => z.2.val) hab
      exact h
    have ha_lt : a.2.val < s (π (π.symm a.1)) + 1 := by rw [Equiv.apply_symm_apply]; exact a.2.isLt
    have hb_lt : b.2.val < s (π (π.symm b.1)) + 1 := by rw [Equiv.apply_symm_apply]; exact b.2.isLt
    have hu : (π.symm a.1).2 = (π.symm b.1).2 := by
      set c := (π.symm a.1).1
      set u1 := (π.symm a.1).2
      set u2 := (π.symm b.1).2
      have hpi1 : π (π.symm a.1) = π (c, u1) := rfl
      have hpi2 : π (π.symm b.1) = π (c, u2) := by
        congr 1
        exact Prod.ext hc.symm rfl
      rw [hpi1] at ha_lt
      rw [hpi2] at hb_lt
      rw [← hc] at hr
      rcases u1 with ⟨_ | _ | _ | u1, hu1⟩ <;> rcases u2 with ⟨_ | _ | _ | u2, hu2⟩
      · rfl
      · simp only [off] at hr; change a.2.val < s (π (c, 0)) + 1 at ha_lt; omega
      · simp only [off] at hr; change a.2.val < s (π (c, 0)) + 1 at ha_lt; omega
      · omega
      · simp only [off] at hr; change b.2.val < s (π (c, 0)) + 1 at hb_lt; omega
      · rfl
      · simp only [off] at hr; change a.2.val < s (π (c, 1)) + 1 at ha_lt; omega
      · omega
      · simp only [off] at hr; change b.2.val < s (π (c, 0)) + 1 at hb_lt; omega
      · simp only [off] at hr; change b.2.val < s (π (c, 1)) + 1 at hb_lt; omega
      · rfl
      · omega
      · omega
      · omega
      · omega
      · omega
    have hcu : π.symm a.1 = π.symm b.1 := Prod.ext hc hu
    have hi : a.1 = b.1 := π.symm.injective hcu
    rcases a with ⟨i1, j1⟩
    rcases b with ⟨i2, j2⟩
    dsimp only at hi hr hcu
    subst hi
    congr 1
    ext
    omega
  have hpsi_card : Fintype.card I = Fintype.card T := by
    rw [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    simp only [Fintype.card_fin]
    exact hsum
  let psi : I ≃ T :=
    Equiv.ofBijective psiFun ((Fintype.bijective_iff_injective_and_card psiFun).mpr ⟨hpsi_inj, hpsi_card⟩)
  have hNpos : 0 < (t + 1) * (b + 1) := Nat.mul_pos (by omega) (by omega)
  have : NeZero ((t + 1) * (b + 1)) := ⟨Nat.ne_of_gt hNpos⟩
  let nextEquiv : T ≃ T := (phiEquiv t b).symm.trans ((finAddOneEquiv ((t + 1) * (b + 1))).trans (phiEquiv t b))
  have hnextEquiv : ∀ i : T, nextEquiv i = nextFn t b i := by
    intro i
    change phiEquiv t b ((phiEquiv t b).symm i + 1) = nextFn t b i
    rw [phiEquiv_add_one, Equiv.apply_symm_apply]
  let sigI : I ≃ I :=
    { toFun := fun q => ⟨q.1, q.2 + 1⟩
      invFun := fun q => ⟨q.1, (finAddOneEquiv (s q.1 + 1)).symm q.2⟩
      left_inv := fun q => by
        rcases q with ⟨i, j⟩
        exact Sigma.ext rfl (heq_of_eq ((finAddOneEquiv (s i + 1)).symm_apply_apply j))
      right_inv := fun q => by
        rcases q with ⟨i, j⟩
        exact Sigma.ext rfl (heq_of_eq ((finAddOneEquiv (s i + 1)).apply_symm_apply j)) }
  let theta : Bool × T ≃ Bool × I :=
    { toFun := fun v =>
        match v with
        | (false, i) => (false, psi.symm i)
        | (true, i) => (true, sigI (psi.symm (nextEquiv.symm i)))
      invFun := fun v =>
        match v with
        | (false, q) => (false, psi q)
        | (true, q) => (true, nextEquiv (psi (sigI.symm q)))
      left_inv := fun v => by
        rcases v with ⟨side, i⟩
        cases side <;> simp
      right_inv := fun v => by
        rcases v with ⟨side, q⟩
        cases side <;> simp }
  have hpin_zero_q : ∀ q : I, p (false, psi q) ≠ none ↔ q.2.val = 0 := by
    intro q
    rcases hcu : π.symm q.1 with ⟨c, u⟩
    have hpi : π (c, u) = q.1 := by rw [← hcu, Equiv.apply_symm_apply]
    have hltq : q.2.val < s (π (c, u)) + 1 := by rw [hpi]; exact q.2.isLt
    have hsum_cu := hsumc c
    simp only [p, pinOf, true_and, ne_eq, ite_eq_right_iff, reduceCtorEq, imp_false, not_not,
      psi, Equiv.ofBijective_apply, psiFun, hcu]
    rcases u with ⟨_ | _ | _ | u, hu⟩
    · simp only [off]; change q.2.val < s (π (c, 0)) + 1 at hltq; omega
    · simp only [off]; change q.2.val < s (π (c, 1)) + 1 at hltq; omega
    · simp only [off]; change q.2.val < s (π (c, 2)) + 1 at hltq; omega
    · omega
  have hpin_zero : ∀ i : T, p (false, i) ≠ none ↔ (psi.symm i).2.val = 0 := by
    intro i
    simpa only [Equiv.apply_symm_apply] using hpin_zero_q (psi.symm i)
  have hnext_step : ∀ q : I,
      psi.symm (nextFn t b (psi q)) = sigI q ∨
      ((psi.symm (nextFn t b (psi q))).2.val = 0 ∧ (sigI q).2.val = 0) := by
    intro q
    rcases hcu : π.symm q.1 with ⟨c, u⟩
    have hpi : π (c, u) = q.1 := by rw [← hcu, Equiv.apply_symm_apply]
    have hltq : q.2.val < s (π (c, u)) + 1 := by rw [hpi]; exact q.2.isLt
    have hsum_cu := hsumc c
    have hsig_val : (sigI q).2.val = (q.2.val + 1) % (s q.1 + 1) := fin_val_add_one (s q.1) q.2
    by_cases hlast : q.2.val + 1 < s q.1 + 1
    · left
      apply psi.injective
      rw [Equiv.apply_symm_apply]
      have hm : (q.2.val + 1) % (s q.1 + 1) = q.2.val + 1 := Nat.mod_eq_of_lt hlast
      have hne_B : off c u + q.2.val + 1 ≠ b + 1 := by
        have := hoff_lt c u
        rw [hpi] at this
        omega
      have hsig1 : (sigI q).1 = q.1 := rfl
      simp only [psi, Equiv.ofBijective_apply, psiFun, nextFn, hsig1, hcu]
      rw [ite_eq_right_iff.mpr (fun h => absurd h hne_B)]
      refine Prod.ext rfl (Fin.ext ?_)
      rw [fin_val_add_one]
      have hsig_eq : (sigI q).2.val = q.2.val + 1 := by rw [hsig_val, hm]
      change (off c u + q.2.val + 1) % (b + 1) = off c u + (sigI q).2.val
      rw [hsig_eq]
      have hltB : off c u + q.2.val + 1 < b + 1 := by
        have := hoff_lt c u
        rw [hpi] at this
        omega
      rw [Nat.mod_eq_of_lt hltB]
      omega
    · right
      have hqlast : q.2.val + 1 = s q.1 + 1 := by have := q.2.isLt; omega
      have hsig0 : (sigI q).2.val = 0 := by rw [hsig_val, hqlast, Nat.mod_self]
      refine ⟨?_, hsig0⟩
      rw [← hpin_zero]
      simp only [p, pinOf, true_and, ne_eq, ite_eq_right_iff, reduceCtorEq, imp_false, not_not,
        psi, Equiv.ofBijective_apply, psiFun, nextFn, hcu]
      have hqlast' : q.2.val + 1 = s (π (c, u)) + 1 := by rw [hpi]; exact hqlast
      rcases u with ⟨_ | _ | _ | u, hu⟩
      · simp only [off]
        change q.2.val + 1 = s (π (c, 0)) + 1 at hqlast'
        have hne_B : 0 + q.2.val + 1 ≠ b + 1 := by omega
        simp only [hne_B, ↓reduceIte]
        rw [fin_val_add_one]
        dsimp only
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · simp only [off]
        change q.2.val + 1 = s (π (c, 1)) + 1 at hqlast'
        have hne_B : s (π (c, 0)) + 1 + q.2.val + 1 ≠ b + 1 := by omega
        simp only [hne_B, ↓reduceIte]
        rw [fin_val_add_one]
        dsimp only
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
      · simp only [off]
        change q.2.val + 1 = s (π (c, 2)) + 1 at hqlast'
        have heq_B : (s (π (c, 0)) + 1) + (s (π (c, 1)) + 1) + q.2.val + 1 = b + 1 := by omega
        simp only [heq_B, ↓reduceIte]
        left; rfl
      · omega
  let phiAssign : ((Bool × I) → Bool) ≃ ((Bool × T) → Bool) := Equiv.arrowCongr theta.symm (Equiv.refl Bool)
  symm
  refine Finset.card_bij (fun x _ => phiAssign x) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with ⟨h0x, hd1x, hd2x⟩
    have hpin : ∀ v, p v = none ∨ p v = some (phiAssign x v) := by
      intro ⟨side, i⟩
      cases side
      · by_cases hne : p (false, i) = none
        · left; exact hne
        · right
          have hsf : p (false, i) = some false := by
            unfold p pinOf at hne ⊢
            split_ifs at hne ⊢
            · rfl
            · exact absurd rfl hne
          rw [hsf]
          have hq0 : (psi.symm i).2.val = 0 := (hpin_zero i).mp hne
          have hqeq : psi.symm i = ⟨(psi.symm i).1, 0⟩ := sigma_snd_eq_zero (psi.symm i) hq0
          change some false = some (x (false, psi.symm i))
          rw [hqeq, h0x]
      · left; rfl
    refine ⟨hpin, ?_, ?_⟩
    · have hcard1 :
          (Finset.univ.filter (fun i : T => phiAssign x (false, i) ≠ phiAssign x (true, i))).card =
          (Finset.univ.filter (fun q : I => x (false, sigI q) ≠ x (true, sigI q))).card := by
        refine Finset.card_bij (fun i _ => psi.symm (nextEquiv.symm i)) ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          set q := psi.symm (nextEquiv.symm i)
          have hi_eq : i = nextFn t b (psi q) := by
            rw [← hnextEquiv, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
          have ht : phiAssign x (true, i) = x (true, sigI q) := rfl
          have hf : phiAssign x (false, i) = x (false, sigI q) := by
            change x (false, psi.symm i) = x (false, sigI q)
            rw [hi_eq]
            rcases hnext_step q with heq | ⟨h1, h2⟩
            · rw [heq]
            · have ha := sigma_snd_eq_zero (psi.symm (nextFn t b (psi q))) h1
              have hb := sigma_snd_eq_zero (sigI q) h2
              rw [ha, hb, h0x, h0x]
          rw [← hf, ← ht]
          exact hi
        · intro i1 _ i2 _ heq
          exact nextEquiv.symm.injective (psi.symm.injective heq)
        · intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
          refine ⟨nextEquiv (psi q), ?_, by simp⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have ht : phiAssign x (true, nextEquiv (psi q)) = x (true, sigI q) := by
            change x (true, sigI (psi.symm (nextEquiv.symm (nextEquiv (psi q))))) = _
            simp
          have hf : phiAssign x (false, nextEquiv (psi q)) = x (false, sigI q) := by
            change x (false, psi.symm (nextEquiv (psi q))) = _
            rw [hnextEquiv]
            rcases hnext_step q with heq | ⟨h1, h2⟩
            · rw [heq]
            · have ha := sigma_snd_eq_zero (psi.symm (nextFn t b (psi q))) h1
              have hb := sigma_snd_eq_zero (sigI q) h2
              rw [ha, hb, h0x, h0x]
          rw [hf, ht]
          exact hq
      have hcard1' :
          (Finset.univ.filter (fun q : I => x (false, sigI q) ≠ x (true, sigI q))).card =
          (Finset.univ.filter (fun q : I => x (false, q) ≠ x (true, q))).card := by
        refine Finset.card_bij (fun q _ => sigI q) ?_ ?_ ?_
        · intro q hq; simpa using hq
        · intro q1 _ q2 _ h; exact sigI.injective h
        · intro q hq; exact ⟨sigI.symm q, by simpa using hq, sigI.apply_symm_apply q⟩
      rw [hcard1, hcard1', hd1x]
    · have hcard2 :
          (Finset.univ.filter (fun i : T => phiAssign x (false, i) ≠ phiAssign x (true, nextFn t b i))).card =
          (Finset.univ.filter (fun q : I => x (false, q) ≠ x (true, sigI q))).card := by
        refine Finset.card_bij (fun i _ => psi.symm i) ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          have ht : phiAssign x (true, nextFn t b i) = x (true, sigI (psi.symm i)) := by
            rw [← hnextEquiv]
            change x (true, sigI (psi.symm (nextEquiv.symm (nextEquiv i)))) = _
            simp
          rw [← ht]
          exact hi
        · intro i1 _ i2 _ heq; exact psi.symm.injective heq
        · intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
          refine ⟨psi q, ?_, psi.symm_apply_apply q⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hf : phiAssign x (false, psi q) = x (false, q) := by
            change x (false, psi.symm (psi q)) = _; simp
          have ht : phiAssign x (true, nextFn t b (psi q)) = x (true, sigI q) := by
            rw [← hnextEquiv]
            change x (true, sigI (psi.symm (nextEquiv.symm (nextEquiv (psi q))))) = _
            simp
          rw [hf, ht]
          exact hq
      rw [hcard2]
      exact hd2x
  · intro x1 _ x2 _ heq
    exact phiAssign.injective heq
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rcases hy with ⟨hpy, hd1y, hd2y⟩
    let x := phiAssign.symm y
    have hxy : phiAssign x = y := phiAssign.apply_symm_apply y
    refine ⟨x, ?_, hxy⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have h0x : ∀ i : K, x (false, ⟨i, 0⟩) = false := by
      intro i
      have hne : p (false, psi ⟨i, 0⟩) ≠ none :=
        (hpin_zero _).mpr (by rw [Equiv.symm_apply_apply]; rfl)
      have hsf : p (false, psi ⟨i, 0⟩) = some false := by
        unfold p pinOf at hne ⊢
        split_ifs at hne ⊢
        · rfl
        · exact absurd rfl hne
      rcases hpy (false, psi ⟨i, 0⟩) with h | h
      · exact absurd h hne
      · rw [hsf] at h
        have hy0 : y (false, psi ⟨i, 0⟩) = false := (Option.some.inj h).symm
        change y (false, psi ⟨i, 0⟩) = false
        exact hy0
    refine ⟨h0x, ?_, ?_⟩
    · have hcard1 :
          (Finset.univ.filter (fun i : T => y (false, i) ≠ y (true, i))).card =
          (Finset.univ.filter (fun q : I => x (false, q) ≠ x (true, q))).card := by
        rw [← hxy]
        have h1 :
            (Finset.univ.filter (fun i : T => phiAssign x (false, i) ≠ phiAssign x (true, i))).card =
            (Finset.univ.filter (fun q : I => x (false, sigI q) ≠ x (true, sigI q))).card := by
          refine Finset.card_bij (fun i _ => psi.symm (nextEquiv.symm i)) ?_ ?_ ?_
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            set q := psi.symm (nextEquiv.symm i)
            have hi_eq : i = nextFn t b (psi q) := by
              rw [← hnextEquiv, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
            have ht : phiAssign x (true, i) = x (true, sigI q) := rfl
            have hf : phiAssign x (false, i) = x (false, sigI q) := by
              change x (false, psi.symm i) = x (false, sigI q)
              rw [hi_eq]
              rcases hnext_step q with heq | ⟨h1, h2⟩
              · rw [heq]
              · have ha := sigma_snd_eq_zero (psi.symm (nextFn t b (psi q))) h1
                have hb := sigma_snd_eq_zero (sigI q) h2
                rw [ha, hb, h0x, h0x]
            rw [← hf, ← ht]
            exact hi
          · intro i1 _ i2 _ heq; exact nextEquiv.symm.injective (psi.symm.injective heq)
          · intro q hq
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
            refine ⟨nextEquiv (psi q), ?_, by simp⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            have ht : phiAssign x (true, nextEquiv (psi q)) = x (true, sigI q) := by
              change x (true, sigI (psi.symm (nextEquiv.symm (nextEquiv (psi q))))) = _; simp
            have hf : phiAssign x (false, nextEquiv (psi q)) = x (false, sigI q) := by
              change x (false, psi.symm (nextEquiv (psi q))) = _
              rw [hnextEquiv]
              rcases hnext_step q with heq | ⟨h1, h2⟩
              · rw [heq]
              · have ha := sigma_snd_eq_zero (psi.symm (nextFn t b (psi q))) h1
                have hb := sigma_snd_eq_zero (sigI q) h2
                rw [ha, hb, h0x, h0x]
            rw [hf, ht]
            exact hq
        have h2 :
            (Finset.univ.filter (fun q : I => x (false, sigI q) ≠ x (true, sigI q))).card =
            (Finset.univ.filter (fun q : I => x (false, q) ≠ x (true, q))).card := by
          refine Finset.card_bij (fun q _ => sigI q) ?_ ?_ ?_
          · intro q hq; simpa using hq
          · intro q1 _ q2 _ h; exact sigI.injective h
          · intro q hq; exact ⟨sigI.symm q, by simpa using hq, sigI.apply_symm_apply q⟩
        exact h1.trans h2
      rw [← hcard1, hd1y]
    · have hcard2 :
          (Finset.univ.filter (fun i : T => y (false, i) ≠ y (true, nextFn t b i))).card =
          (Finset.univ.filter (fun q : I => x (false, q) ≠ x (true, sigI q))).card := by
        rw [← hxy]
        refine Finset.card_bij (fun i _ => psi.symm i) ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          have ht : phiAssign x (true, nextFn t b i) = x (true, sigI (psi.symm i)) := by
            rw [← hnextEquiv]
            change x (true, sigI (psi.symm (nextEquiv.symm (nextEquiv i)))) = _; simp
          rw [← ht]
          exact hi
        · intro i1 _ i2 _ heq; exact psi.symm.injective heq
        · intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
          refine ⟨psi q, ?_, psi.symm_apply_apply q⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hf : phiAssign x (false, psi q) = x (false, q) := by
            change x (false, psi.symm (psi q)) = _; simp
          have ht : phiAssign x (true, nextFn t b (psi q)) = x (true, sigI q) := by
            rw [← hnextEquiv]
            change x (true, sigI (psi.symm (nextEquiv.symm (nextEquiv (psi q))))) = _; simp
          rw [hf, ht]
          exact hq
      exact hcard2.symm.trans hd2y

lemma subtype_equiv_cast_symm {α β : Type*} {f g : α → β}
    (e : (b : β) → {x : α // f x = b} ≃ {x : α // g x = b})
    {b : β} {y : α} (h : g y = b) :
    ((e (g y)).symm ⟨y, rfl⟩).1 = ((e b).symm ⟨y, h⟩).1 := by
  cases h; rfl

lemma subtype_equiv_cast_apply {α β : Type*} {f g : α → β}
    (e : (b : β) → {x : α // f x = b} ≃ {x : α // g x = b})
    {b : β} {y : α} (h : f y = b) :
    (e (f y) ⟨y, rfl⟩).1 = (e b ⟨y, h⟩).1 := by
  cases h; rfl

lemma subtype_equiv_symm_apply {α β : Type*} (f g : α → β)
    (e : (b : β) → {x : α // f x = b} ≃ {x : α // g x = b}) (k : α) :
    ((e (g (e (f k) ⟨k, rfl⟩).1)).symm ⟨(e (f k) ⟨k, rfl⟩).1, rfl⟩).1 = k := by
  generalize hy : e (f k) ⟨k, rfl⟩ = y
  rcases y with ⟨y, hgy⟩
  dsimp only
  rw [subtype_equiv_cast_symm e hgy, ← hy, Equiv.symm_apply_apply]

lemma subtype_equiv_apply_symm {α β : Type*} (f g : α → β)
    (e : (b : β) → {x : α // f x = b} ≃ {x : α // g x = b}) (k : α) :
    (e (f ((e (g k)).symm ⟨k, rfl⟩).1) ⟨((e (g k)).symm ⟨k, rfl⟩).1, rfl⟩).1 = k := by
  generalize hy : (e (g k)).symm ⟨k, rfl⟩ = y
  rcases y with ⟨y, hfy⟩
  dsimp only
  rw [subtype_equiv_cast_apply e hfy, ← hy, Equiv.apply_symm_apply]

lemma perm_preserving_card {K : Type*} [Fintype K] [DecidableEq K] (B : ℕ) (len : K → ℕ)
    (hlen : ∀ k, len k < B + 1) :
    (Finset.univ.filter (fun τ : Equiv.Perm K => ∀ k, len (τ k) = len k)).card =
    ∏ j : Fin (B + 1), (Finset.univ.filter (fun k : K => len k = j.val)).card.factorial := by
  let lf : K → Fin (B + 1) := fun k => ⟨len k, hlen k⟩
  have hsub_eq : ∀ j : Fin (B + 1), {k : K // len k = j.val} ≃ {k : K // lf k = j} := fun j =>
    { toFun := fun x => ⟨x.1, Fin.ext x.2⟩
      invFun := fun x => ⟨x.1, congrArg Fin.val x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e : {τ : Equiv.Perm K // ∀ k, len (τ k) = len k} ≃
      ((j : Fin (B + 1)) → Equiv.Perm {k : K // lf k = j}) :=
    { toFun := fun τ j =>
        { toFun := fun x => ⟨τ.1 x.1, Fin.ext (by dsimp only [lf]; rw [τ.2]; exact congrArg Fin.val x.2)⟩
          invFun := fun x => ⟨τ.1.symm x.1, Fin.ext (by
            have := τ.2 (τ.1.symm x.1)
            rw [Equiv.apply_symm_apply] at this
            dsimp only [lf]
            rw [← this]
            exact congrArg Fin.val x.2)⟩
          left_inv := fun x => by ext; simp
          right_inv := fun x => by ext; simp }
      invFun := fun g =>
        ⟨{ toFun := fun k => (g (lf k) ⟨k, rfl⟩).1
           invFun := fun k => ((g (lf k)).symm ⟨k, rfl⟩).1
           left_inv := fun k => subtype_equiv_symm_apply lf lf g k
           right_inv := fun k => subtype_equiv_apply_symm lf lf g k },
         fun k => congrArg Fin.val (g (lf k) ⟨k, rfl⟩).2⟩
      left_inv := fun τ => by
        ext k
        rfl
      right_inv := fun g => by
        funext j
        ext x
        rcases x with ⟨k, hk⟩
        dsimp only
        cases hk
        rfl }
  have h1 : (Finset.univ.filter (fun τ : Equiv.Perm K => ∀ k, len (τ k) = len k)).card =
      Fintype.card {τ : Equiv.Perm K // ∀ k, len (τ k) = len k} := (Fintype.card_subtype _).symm
  rw [h1, Fintype.card_congr e, Fintype.card_pi]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Fintype.card_perm, Fintype.card_congr (hsub_eq j).symm, Fintype.card_subtype]

lemma exists_perm_of_card_filter_eq {K : Type*} [Fintype K] [DecidableEq K] (B : ℕ)
    (f len : K → ℕ) (hf : ∀ k, f k < B + 1) (hlen : ∀ k, len k < B + 1)
    (hcard : ∀ j : ℕ, (Finset.univ.filter (fun k : K => f k = j)).card =
                      (Finset.univ.filter (fun k : K => len k = j)).card) :
    ∃ π : Equiv.Perm K, ∀ k, len (π k) = f k := by
  let ff : K → Fin (B + 1) := fun k => ⟨f k, hf k⟩
  let lf : K → Fin (B + 1) := fun k => ⟨len k, hlen k⟩
  have heq : ∀ j : Fin (B + 1),
      Fintype.card {k : K // ff k = j} = Fintype.card {k : K // lf k = j} := by
    intro j
    rw [Fintype.card_subtype, Fintype.card_subtype]
    have h1 : Finset.univ.filter (fun k : K => ff k = j) = Finset.univ.filter (fun k : K => f k = j.val) :=
      Finset.filter_congr (fun k _ => Fin.ext_iff)
    have h2 : Finset.univ.filter (fun k : K => lf k = j) = Finset.univ.filter (fun k : K => len k = j.val) :=
      Finset.filter_congr (fun k _ => Fin.ext_iff)
    rw [h1, h2]
    exact hcard j.val
  let e : (j : Fin (B + 1)) → ({k : K // ff k = j} ≃ {k : K // lf k = j}) :=
    fun j => Fintype.equivOfCardEq (heq j)
  refine ⟨
    { toFun := fun k => (e (ff k) ⟨k, rfl⟩).1
      invFun := fun k => ((e (lf k)).symm ⟨k, rfl⟩).1
      left_inv := fun k => subtype_equiv_symm_apply ff lf e k
      right_inv := fun k => subtype_equiv_apply_symm ff lf e k },
    fun k => congrArg Fin.val (e (ff k) ⟨k, rfl⟩).2⟩

end PEqualNP.Outside.L_pcx_391

theorem PEqualNP.Outside.L_pcx_391 : ∀ (t b : ℕ) (s : (Fin (t+1) × Fin 3) → ℕ),
  let m := t+1
  let B := b+1
  let K := Fin m × Fin 3
  let len := fun i : K => s i + 1
  (∑ i : K, len i) = m*B → (∀ i, B < 4*len i ∧ 2*len i < B) →
  let I := (i : K) × Fin (s i+1)
  let T := Fin m × Fin B
  let J := Fin (m*B+1)
  let source := fun (d : J × J) =>
    ((Finset.univ : Finset ((Bool × I) → Bool)).filter (fun x =>
      (∀ i : K, x (false,(⟨i,0⟩ : I)) = false) ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,i))).card = d.1.val ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,(⟨i.1,i.2+1⟩ : I)))).card = d.2.val)).card
  let next := fun (i : T) => if i.2.val+1 = B then (i.1+1,0) else (i.1,i.2+1)
  let anchor := fun (p : Bool × T → Option Bool) => ∀ c : Fin m, p (false,(c,0)) = some false
  let hist := fun (p : Bool × T → Option Bool) (d : J × J) =>
    ((Finset.univ : Finset ((Bool × T) → Bool)).filter (fun x =>
      (∀ v, p v = none ∨ p v = some (x v)) ∧
      (Finset.univ.filter (fun i : T => x (false,i) ≠ x (true,i))).card = d.1.val ∧
      (Finset.univ.filter (fun i : T => x (false,i) ≠ x (true,next i))).card = d.2.val)).card
  let good := Finset.univ.filter (fun p => anchor p ∧ hist p = source)
  let slots := (Finset.univ : Finset (Equiv.Perm K)).filter (fun π =>
    ∀ c : Fin m, (∑ u : Fin 3, len (π (c,u))) = B)
  let copies := ∏ j : Fin (B+1), ((Finset.univ : Finset K).filter (fun i => len i = j.val)).card.factorial
  (∀ p, anchor p → ((∀ d, hist p d * 2^(2*m*B-3*m) =
    source d * 2^((Finset.univ.filter (fun v => p v = none)).card)) ↔ hist p = source)) ∧
    (∀ p ∈ good, ∀ v, p v ≠ none → v.1 = false ∧ p v = some false) ∧
    (good.Nonempty ↔ slots.Nonempty) ∧ copies * good.card = slots.card := by
  intro t b s m B K len hsum hbounds I T J source next anchor hist good slots copies
  have hB3 : 3 ≤ B := by
    have h0 := (hbounds (0, 0)).2
    have : 1 ≤ len (0, 0) := Nat.succ_le_succ (Nat.zero_le _)
    omega
  have hcardI : Fintype.card I = m * B := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    exact hsum
  have hcardT : Fintype.card T = m * B := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hcardK : Fintype.card K = 3 * m := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mul_comm]
  have h2mB : 2 * (m * B) = 2 * m * B := by ring
  have hsource00 : source (0, 0) = 1 := by
    have hfilt : (Finset.univ : Finset ((Bool × I) → Bool)).filter (fun x =>
        (∀ i : K, x (false, (⟨i, 0⟩ : I)) = false) ∧
        (Finset.univ.filter (fun i : I => x (false, i) ≠ x (true, i))).card = (0 : J).val ∧
        (Finset.univ.filter (fun i : I => x (false, i) ≠ x (true, (⟨i.1, i.2 + 1⟩ : I)))).card = (0 : J).val) =
        {fun _ => false} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      simp only [Fin.val_zero]
      constructor
      · rintro ⟨h0, h1, h2⟩
        have he1 : ∀ a : I, x (false, a) = x (true, a) := by
          intro a
          by_contra hne
          have hmem : a ∈ Finset.univ.filter (fun i : I => x (false, i) ≠ x (true, i)) := by
            simp [hne]
          have hpos := Finset.card_pos.mpr ⟨a, hmem⟩
          omega
        have he2 : ∀ a : I, x (false, a) = x (true, ⟨a.1, a.2 + 1⟩) := by
          intro a
          by_contra hne
          have hmem : a ∈ Finset.univ.filter (fun i : I => x (false, i) ≠ x (true, ⟨i.1, i.2 + 1⟩)) := by
            simp [hne]
          have hpos := Finset.card_pos.mpr ⟨a, hmem⟩
          omega
        have hfalse : ∀ (i : K) (r : ℕ) (hr : r < s i + 1), x (false, ⟨i, ⟨r, hr⟩⟩) = false := by
          intro i r
          induction r with
          | zero => intro hr; exact h0 i
          | succ r ihr =>
            intro hr
            have hprev := ihr (by omega)
            have hstep := he2 ⟨i, ⟨r, by omega⟩⟩
            have hadd : (⟨r, by omega⟩ : Fin (s i + 1)) + 1 = ⟨r + 1, hr⟩ := by
              ext
              rw [PEqualNP.Outside.L_pcx_391.fin_val_add_one]
              exact Nat.mod_eq_of_lt hr
            rw [hadd] at hstep
            rw [he1 ⟨i, ⟨r + 1, hr⟩⟩, ← hstep, hprev]
        funext ⟨side, ⟨i, j⟩⟩
        cases side
        · exact hfalse i j.val j.isLt
        · rw [← he1 ⟨i, j⟩]
          exact hfalse i j.val j.isLt
      · intro hx
        subst hx
        simp
    exact congrArg Finset.card hfilt
  have hsum_source : ∑ d : J × J, source d = 2 ^ (2 * m * B - 3 * m) := by
    have h1 := PEqualNP.Outside.L_pcx_391.sum_histGen_eq_card_valid hcardI
      (fun a : I => (⟨a.1, a.2 + 1⟩ : I)) (fun x : Bool × I → Bool => ∀ i : K, x (false, ⟨i, 0⟩) = false)
    change ∑ d : J × J, source d =
      (Finset.univ.filter (fun x : Bool × I → Bool => ∀ i : K, x (false, ⟨i, 0⟩) = false)).card at h1
    rw [h1]
    let pS : Bool × I → Option Bool := fun v => if v.1 = false ∧ v.2.2.val = 0 then some false else none
    have hfeq : Finset.univ.filter (fun x : Bool × I → Bool => ∀ i : K, x (false, ⟨i, 0⟩) = false) =
        Finset.univ.filter (fun x : Bool × I → Bool => ∀ v, pS v = none ∨ pS v = some (x v)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hx ⟨side, ⟨i, j⟩⟩
        by_cases hc : side = false ∧ j.val = 0
        · right
          rcases hc with ⟨rfl, hj0⟩
          have hj : j = 0 := Fin.ext hj0
          subst hj
          simp [pS, hx i]
        · left
          simp only [pS, hc, ↓reduceIte]
      · intro hx i
        rcases hx (false, ⟨i, 0⟩) with h | h
        · simp [pS] at h
        · simp only [pS, Fin.val_zero, and_self, ↓reduceIte, Option.some.injEq] at h
          exact h.symm
    rw [hfeq, PEqualNP.Outside.L_pcx_391.card_valid_pin]
    congr 1
    have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Bool × I)))
      (p := fun v => pS v = none)
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_bool, hcardI, h2mB] at htot
    have hpinned : (Finset.univ.filter (fun v : Bool × I => ¬ pS v = none)).card = 3 * m := by
      rw [← hcardK]
      symm
      refine Finset.card_bij (fun i _ => (false, (⟨i, 0⟩ : I))) ?_ ?_ ?_
      · intro i _
        simp [pS]
      · intro i1 _ i2 _ heq
        have := congrArg (fun z : Bool × I => z.2.1) heq
        exact this
      · intro ⟨side, ⟨i, j⟩⟩ hmem
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, pS, ite_eq_right_iff,
          reduceCtorEq, imp_false, not_not] at hmem
        rcases hmem with ⟨rfl, hj0⟩
        exact ⟨i, Finset.mem_univ i, by congr 1; congr 1; exact (Fin.ext hj0).symm⟩
    omega
  have hsum_hist : ∀ p : Bool × T → Option Bool,
      ∑ d : J × J, hist p d = 2 ^ (Finset.univ.filter (fun v : Bool × T => p v = none)).card := by
    intro p
    have h1 := PEqualNP.Outside.L_pcx_391.sum_histGen_eq_card_valid hcardT next
      (fun x : Bool × T → Bool => ∀ v, p v = none ∨ p v = some (x v))
    change ∑ d : J × J, hist p d = _ at h1
    rw [h1, PEqualNP.Outside.L_pcx_391.card_valid_pin]
  have hhist00_sub : ∀ p : Bool × T → Option Bool, anchor p →
      (Finset.univ : Finset ((Bool × T) → Bool)).filter (fun x =>
        (∀ v, p v = none ∨ p v = some (x v)) ∧
        (Finset.univ.filter (fun i : T => x (false, i) ≠ x (true, i))).card = (0 : J).val ∧
        (Finset.univ.filter (fun i : T => x (false, i) ≠ x (true, next i))).card = (0 : J).val) ⊆
      {fun _ => false} := by
    intro p hanc x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hx ⊢
    simp only [Fin.val_zero] at hx
    rcases hx with ⟨hpx, h1, h2⟩
    have he1 : ∀ i : T, x (false, i) = x (true, i) := by
      intro i
      by_contra hne
      have hmem : i ∈ Finset.univ.filter (fun j : T => x (false, j) ≠ x (true, j)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
      have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
      omega
    have he2 : ∀ i : T, x (false, i) = x (true, next i) := by
      intro i
      by_contra hne
      have hmem : i ∈ Finset.univ.filter (fun j : T => x (false, j) ≠ x (true, next j)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
      have hpos := Finset.card_pos.mpr ⟨i, hmem⟩
      omega
    have hfalse : ∀ (c : Fin m) (r : ℕ) (hr : r < B), x (false, (c, ⟨r, hr⟩)) = false := by
      intro c r
      induction r with
      | zero =>
        intro hr
        rcases hpx (false, (c, 0)) with h | h
        · rw [hanc c] at h; cases h
        · rw [hanc c] at h; exact (Option.some.inj h).symm
      | succ r ihr =>
        intro hr
        have hprev := ihr (by omega)
        have hstep := he2 (c, ⟨r, by omega⟩)
        have hnxt : next (c, ⟨r, by omega⟩) = (c, ⟨r + 1, hr⟩) := by
          simp only [next]
          have hne : r + 1 ≠ B := by omega
          simp only [hne, ↓reduceIte]
          refine Prod.ext rfl (Fin.ext ?_)
          rw [PEqualNP.Outside.L_pcx_391.fin_val_add_one]
          exact Nat.mod_eq_of_lt hr
        rw [hnxt] at hstep
        rw [he1 (c, ⟨r + 1, hr⟩), ← hstep, hprev]
    funext ⟨side, ⟨c, r⟩⟩
    cases side
    · exact hfalse c r.val r.isLt
    · rw [← he1 (c, r)]
      exact hfalse c r.val r.isLt
  have hhist00_le : ∀ p, anchor p → hist p (0, 0) ≤ 1 := by
    intro p hanc
    calc hist p (0, 0) ≤ ({fun _ => false} : Finset ((Bool × T) → Bool)).card :=
          Finset.card_le_card (hhist00_sub p hanc)
      _ = 1 := Finset.card_singleton _
  have hhist00_eq_one_imp : ∀ p, anchor p → hist p (0, 0) = 1 →
      ∀ v, p v ≠ none → p v = some false := by
    intro p hanc h1 v hv
    have hpos : 0 < hist p (0, 0) := by omega
    rcases Finset.card_pos.mp hpos with ⟨x, hx⟩
    have hx0 : x = fun _ => false := Finset.mem_singleton.mp (hhist00_sub p hanc hx)
    have hpx := (Finset.mem_filter.mp hx).2.1 v
    rcases hpx with h | h
    · exact absurd h hv
    · rw [hx0] at h
      exact h
  have hpart1 : ∀ p, anchor p → ((∀ d, hist p d * 2 ^ (2 * m * B - 3 * m) =
      source d * 2 ^ ((Finset.univ.filter (fun v => p v = none)).card)) ↔ hist p = source) := by
    intro p hanc
    constructor
    · intro hscaled
      have h00 := hscaled (0, 0)
      rw [hsource00, one_mul] at h00
      have hne0 : hist p (0, 0) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at h00
        have : 0 < 2 ^ (Finset.univ.filter (fun v : Bool × T => p v = none)).card := Nat.pow_pos (by omega)
        omega
      have hle1 := hhist00_le p hanc
      have heq1 : hist p (0, 0) = 1 := by omega
      rw [heq1, one_mul] at h00
      funext d
      have hd := hscaled d
      rw [← h00] at hd
      exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by omega)) hd
    · intro heq d
      have htot : 2 ^ (Finset.univ.filter (fun v : Bool × T => p v = none)).card = 2 ^ (2 * m * B - 3 * m) := by
        rw [← hsum_hist p, ← hsum_source, heq]
      rw [heq, htot]
  have hsource_poly : ∀ U V : ℤ,
      ∑ d : J × J, (source d : ℤ) *
        ((1 - U) ^ d.1.val * (1 + U) ^ (m * B - d.1.val) *
         (1 - V) ^ d.2.val * (1 + V) ^ (m * B - d.2.val)) =
      (2 : ℤ) ^ (2 * m * B - 3 * m) * ∏ i : K, (1 + (U * V) ^ len i) := by
    intro U V
    have h1 := PEqualNP.Outside.L_pcx_391.sum_histGen_poly_eq hcardI
      (fun a : I => (⟨a.1, a.2 + 1⟩ : I)) (fun x : Bool × I → Bool => ∀ i : K, x (false, ⟨i, 0⟩) = false) U V
    change ∑ d : J × J, (source d : ℤ) * _ = _ at h1
    rw [h1]
    let eS : {x : Bool × I → Bool // ∀ i : K, x (false, ⟨i, 0⟩) = false} ≃
        ((i : K) → {y : Bool × Fin (s i + 1) → Bool // y (false, 0) = false}) :=
      { toFun := fun x i => ⟨fun v => x.1 (v.1, ⟨i, v.2⟩), x.2 i⟩
        invFun := fun y => ⟨fun v => (y v.2.1).1 (v.1, v.2.2), fun i => (y i).2⟩
        left_inv := fun x => by ext ⟨side, ⟨i, j⟩⟩; rfl
        right_inv := fun y => by funext i; ext ⟨side, j⟩; rfl }
    rw [Finset.sum_subtype (s := Finset.univ.filter _)
          (p := fun x : Bool × I → Bool => ∀ i : K, x (false, ⟨i, 0⟩) = false) (fun _ => by simp)]
    rw [← Equiv.sum_comp eS.symm]
    have hsplit : ∀ y : (i : K) → {y : Bool × Fin (s i + 1) → Bool // y (false, 0) = false},
        (∏ a : I, (1 + U * PEqualNP.Outside.L_pcx_391.sgn ((eS.symm y).1 (false, a)) *
          PEqualNP.Outside.L_pcx_391.sgn ((eS.symm y).1 (true, a)))) *
        (∏ a : I, (1 + V * PEqualNP.Outside.L_pcx_391.sgn ((eS.symm y).1 (false, a)) *
          PEqualNP.Outside.L_pcx_391.sgn ((eS.symm y).1 (true, ⟨a.1, a.2 + 1⟩)))) =
        ∏ i : K,
          ((∏ j : Fin (s i + 1), (1 + U * PEqualNP.Outside.L_pcx_391.sgn ((y i).1 (false, j)) *
              PEqualNP.Outside.L_pcx_391.sgn ((y i).1 (true, j)))) *
           (∏ j : Fin (s i + 1), (1 + V * PEqualNP.Outside.L_pcx_391.sgn ((y i).1 (false, j)) *
              PEqualNP.Outside.L_pcx_391.sgn ((y i).1 (true, j + 1))))) := by
      intro y
      rw [Fintype.prod_sigma, Fintype.prod_sigma, ← Finset.prod_mul_distrib]
      rfl
    simp_rw [hsplit]
    rw [← Fintype.prod_sum (f := fun (i : K) (yi : {y : Bool × Fin (s i + 1) → Bool // y (false, 0) = false}) =>
          (∏ j : Fin (s i + 1), (1 + U * PEqualNP.Outside.L_pcx_391.sgn (yi.1 (false, j)) *
              PEqualNP.Outside.L_pcx_391.sgn (yi.1 (true, j)))) *
          (∏ j : Fin (s i + 1), (1 + V * PEqualNP.Outside.L_pcx_391.sgn (yi.1 (false, j)) *
              PEqualNP.Outside.L_pcx_391.sgn (yi.1 (true, j + 1)))))]
    have hcyc : ∀ i : K,
        (∑ yi : {y : Bool × Fin (s i + 1) → Bool // y (false, 0) = false},
          (∏ j : Fin (s i + 1), (1 + U * PEqualNP.Outside.L_pcx_391.sgn (yi.1 (false, j)) *
              PEqualNP.Outside.L_pcx_391.sgn (yi.1 (true, j)))) *
          (∏ j : Fin (s i + 1), (1 + V * PEqualNP.Outside.L_pcx_391.sgn (yi.1 (false, j)) *
              PEqualNP.Outside.L_pcx_391.sgn (yi.1 (true, j + 1))))) =
        (2 : ℤ) ^ (2 * s i + 1) * (1 + (U * V) ^ len i) := by
      intro i
      rw [← Finset.sum_subtype
            (s := Finset.univ.filter (fun y : Bool × Fin (s i + 1) → Bool => y (false, 0) = false))
            (p := fun y : Bool × Fin (s i + 1) → Bool => y (false, 0) = false)
            (f := fun y =>
              (∏ j : Fin (s i + 1), (1 + U * PEqualNP.Outside.L_pcx_391.sgn (y (false, j)) *
                  PEqualNP.Outside.L_pcx_391.sgn (y (true, j)))) *
              (∏ j : Fin (s i + 1), (1 + V * PEqualNP.Outside.L_pcx_391.sgn (y (false, j)) *
                  PEqualNP.Outside.L_pcx_391.sgn (y (true, j + 1)))))
            (fun _ => by simp)]
      exact PEqualNP.Outside.L_pcx_391.single_cycle_sum (s i) U V
    simp_rw [hcyc]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    congr 2
    have h2 : (∑ i : K, (2 * s i + 1)) + 3 * m = 2 * m * B := by
      have : (∑ i : K, (2 * s i + 1)) + ∑ _i : K, 1 = ∑ i : K, (2 * len i) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => by dsimp only [len]; omega)
      rw [← Finset.mul_sum, hsum] at this
      simp only [Finset.sum_const, Finset.card_univ, hcardK, smul_eq_mul, mul_one] at this
      omega
    omega
  have hgood_extract : ∀ p ∈ good,
      (∀ v, p v ≠ none → v.1 = false ∧ p v = some false) ∧
      ∃ f : K → ℕ,
        (∀ k, 0 < f k) ∧
        (∀ c, ∑ u : Fin 3, f (c, u) = B) ∧
        (∀ d, (Finset.univ.filter (fun k : K => f k = d)).card =
              (Finset.univ.filter (fun k : K => len k = d)).card) ∧
        p = PEqualNP.Outside.L_pcx_391.pinOf t b f := by
    intro p hp
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases hp with ⟨hanc, hhist⟩
    have h00 : hist p (0, 0) = 1 := by rw [hhist, hsource00]
    have hall : ∀ v, p v ≠ none → p v = some false := hhist00_eq_one_imp p hanc h00
    have hfree : (Finset.univ.filter (fun v : Bool × T => p v = none)).card = 2 * m * B - 3 * m := by
      have hpow : 2 ^ (Finset.univ.filter (fun v : Bool × T => p v = none)).card = 2 ^ (2 * m * B - 3 * m) := by
        rw [← hsum_hist p, hhist, hsum_source]
      exact Nat.pow_right_injective (by omega) hpow
    let S := (Finset.univ : Finset (Fin (2 * (m * B)))).filter (fun e => p (PEqualNP.Outside.L_pcx_391.ringEquiv t b e) ≠ none)
    let k := S.card
    have hk_eq : k = 3 * m := by
      have hbij : k = (Finset.univ.filter (fun v : Bool × T => ¬ p v = none)).card := by
        refine Finset.card_bij (fun e _ => PEqualNP.Outside.L_pcx_391.ringEquiv t b e) ?_ ?_ ?_
        · intro e he; simpa [S] using he
        · intro e1 _ e2 _ h; exact (PEqualNP.Outside.L_pcx_391.ringEquiv t b).injective h
        · intro v hv
          refine ⟨(PEqualNP.Outside.L_pcx_391.ringEquiv t b).symm v, ?_, Equiv.apply_symm_apply _ _⟩
          simpa [S] using hv
      have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Bool × T)))
        (p := fun v => p v = none)
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_bool, hcardT, h2mB, hfree] at htot
      have hge3m : 3 * m ≤ 2 * m * B := by
        have h1 : 3 * m ≤ m * B := by
          rw [mul_comm 3 m]
          exact Nat.mul_le_mul_left m hB3
        omega
      omega
    have h0_pin : p (PEqualNP.Outside.L_pcx_391.ringEquiv t b 0) ≠ none := by
      have hr0 : PEqualNP.Outside.L_pcx_391.ringEquiv t b 0 = (false, (0, 0)) := by
        unfold PEqualNP.Outside.L_pcx_391.ringEquiv PEqualNP.Outside.L_pcx_391.phiEquiv
        simp
      rw [hr0, hanc 0]
      simp
    let emb := S.orderEmbOfFin rfl
    let pos : ℕ → ℕ := fun r => if hr : r < k then (emb ⟨r, hr⟩).val else 2 * (m * B)
    have hpos_fin : ∀ r : Fin k, pos r.val = (emb r).val := by
      intro r
      simp only [pos, r.isLt, ↓reduceDIte]
      rfl
    let α : Fin k → ℕ := fun r => PEqualNP.Outside.L_pcx_391.oddCnt (pos r.val) (pos (r.val + 1) - pos r.val)
    let β : Fin k → ℕ := fun r => PEqualNP.Outside.L_pcx_391.evenCnt (pos r.val) (pos (r.val + 1) - pos r.val)
    have hpoly_eq : ∀ U V : ℤ,
        ∏ r : Fin k, (1 + U ^ α r * V ^ β r) = ∏ i : K, (1 + (U * V) ^ len i) := by
      intro U V
      have hLHS := PEqualNP.Outside.L_pcx_391.sum_histGen_poly_eq hcardT next
        (fun x : Bool × T → Bool => ∀ v, p v = none ∨ p v = some (x v)) U V
      change ∑ d : J × J, (hist p d : ℤ) * _ = _ at hLHS
      have hnext_eq : next = PEqualNP.Outside.L_pcx_391.nextFn t b := rfl
      rw [hnext_eq] at hLHS
      have hR := PEqualNP.Outside.L_pcx_391.ring_poly_of_all_false t b p h0_pin hall U V
      have hS := hsource_poly U V
      have hmul : (2 : ℤ) ^ (2 * (m * B) - k) * ∏ r : Fin k, (1 + U ^ α r * V ^ β r) =
          (2 : ℤ) ^ (2 * m * B - 3 * m) * ∏ i : K, (1 + (U * V) ^ len i) := by
        rw [← hR, ← hLHS, hhist, hS]
      have hexp : 2 * (m * B) - k = 2 * m * B - 3 * m := by rw [h2mB, hk_eq]
      rw [hexp] at hmul
      have h2pos : (2 : ℤ) ^ (2 * m * B - 3 * m) ≠ 0 := by
        exact pow_ne_zero _ (by decide)
      exact mul_left_cancel₀ h2pos hmul
    have hdiag : ∀ r : Fin k, α r = β r := by
      have h41 := hpoly_eq 4 1
      have h14 := hpoly_eq 1 4
      have h22 := hpoly_eq 2 2
      have hprod_int :
          ∏ r : Fin k, (((1 : ℤ) + 2 ^ (2 * α r)) * (1 + 2 ^ (2 * β r))) =
          ∏ r : Fin k, ((1 : ℤ) + 2 ^ (α r + β r)) ^ 2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow]
        have h1 : (∏ r : Fin k, ((1 : ℤ) + 2 ^ (2 * α r))) = ∏ i : K, ((1 : ℤ) + (4 : ℤ) ^ len i) := by
          simpa [pow_mul] using h41
        have h2 : (∏ r : Fin k, ((1 : ℤ) + 2 ^ (2 * β r))) = ∏ i : K, ((1 : ℤ) + (4 : ℤ) ^ len i) := by
          simpa [pow_mul] using h14
        have h3 : (∏ r : Fin k, ((1 : ℤ) + 2 ^ (α r + β r))) = ∏ i : K, ((1 : ℤ) + (4 : ℤ) ^ len i) := by
          have h22' : (∏ r : Fin k, ((1 : ℤ) + 2 ^ α r * 2 ^ β r)) = ∏ i : K, ((1 : ℤ) + (2 * 2 : ℤ) ^ len i) := h22
          simpa [← pow_add, show (2 * 2 : ℤ) = 4 by rfl] using h22'
        rw [h1, h2, h3, sq]
      have hprod_nat :
          ∏ r : Fin k, ((1 + 2 ^ (2 * α r)) * (1 + 2 ^ (2 * β r))) =
          ∏ r : Fin k, (1 + 2 ^ (α r + β r)) ^ 2 := by
        exact_mod_cast hprod_int
      exact PEqualNP.Outside.L_pcx_391.eq_of_prod_two_pow_eq α β hprod_nat
    have hpos_mono : ∀ r1 r2 : ℕ, r1 < r2 → r2 ≤ k → pos r1 < pos r2 := by
      intro r1 r2 hlt hle
      have hr1 : r1 < k := by omega
      by_cases hr2 : r2 < k
      · simp only [pos, hr1, hr2, ↓reduceDIte]
        exact emb.strictMono (show (⟨r1, hr1⟩ : Fin k) < ⟨r2, hr2⟩ from hlt)
      · simp only [pos, hr1, hr2, ↓reduceDIte]
        exact (emb ⟨r1, hr1⟩).isLt
    have hpos_le : ∀ r1 r2 : ℕ, r1 ≤ r2 → r2 ≤ k → pos r1 ≤ pos r2 := by
      intro r1 r2 hle1 hle2
      rcases eq_or_lt_of_le hle1 with rfl | hlt
      · exact le_rfl
      · exact le_of_lt (hpos_mono r1 r2 hlt hle2)
    have h0S : (0 : Fin (2 * (m * B))) ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact h0_pin
    have hk_pos : 0 < k := Finset.card_pos.mpr ⟨0, h0S⟩
    have hpos0 : pos 0 = 0 := by
      have h0mem : (0 : Fin (2 * (m * B))) ∈ Set.range emb := by
        rw [Finset.range_orderEmbOfFin]; exact h0S
      rcases h0mem with ⟨r0, hr0⟩
      have hle : emb ⟨0, hk_pos⟩ ≤ emb r0 := emb.monotone (Nat.zero_le r0.val)
      rw [hr0] at hle
      have h0val : (emb ⟨0, hk_pos⟩).val = 0 := Nat.eq_zero_of_le_zero hle
      simp only [pos, hk_pos, ↓reduceDIte, h0val]
    have hposk : pos k = 2 * (m * B) := by simp only [pos, lt_irrefl, ↓reduceDIte]
    have hstep_pos : ∀ r : Fin k, pos (r.val + 1) = pos r.val + 2 * α r := by
      intro r
      have hsum_ab := PEqualNP.Outside.L_pcx_391.oddCnt_add_evenCnt (pos r.val) (pos (r.val + 1) - pos r.val)
      have hab : α r = β r := hdiag r
      have hlt := hpos_mono r.val (r.val + 1) (by omega) r.isLt
      dsimp only [α, β] at hab ⊢
      omega
    have hpos_even : ∀ r : ℕ, r ≤ k → pos r % 2 = 0 := by
      intro r
      induction r with
      | zero => intro _; rw [hpos0]
      | succ r ihr =>
        intro hr
        have hstep := hstep_pos ⟨r, by omega⟩
        have hev := ihr (by omega)
        dsimp only at hstep
        omega
    have hside_false : ∀ v, p v ≠ none → v.1 = false ∧ p v = some false := by
      intro v hv
      refine ⟨?_, hall v hv⟩
      generalize he : (PEqualNP.Outside.L_pcx_391.ringEquiv t b).symm v = e
      have heS : e ∈ S := by
        rw [← he]
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
        exact hv
      have hrng : e ∈ Set.range emb := by
        rw [Finset.range_orderEmbOfFin]; exact heS
      rcases hrng with ⟨r, hr⟩
      have hev : e.val % 2 = 0 := by
        rw [← hr, ← hpos_fin r]
        exact hpos_even r.val (le_of_lt r.isLt)
      have hv_eq : v = PEqualNP.Outside.L_pcx_391.ringEquiv t b e := by
        rw [← he, Equiv.apply_symm_apply]
      rw [hv_eq]
      unfold PEqualNP.Outside.L_pcx_391.ringEquiv
      simp only [Equiv.coe_fn_mk, hev, ↓reduceIte]
    have hα_pos : ∀ r : Fin k, 0 < α r := by
      intro r
      have h1 := hstep_pos r
      have h2 := hpos_mono r.val (r.val + 1) (by omega) r.isLt
      omega
    have hmult : ∀ d : ℕ,
        (Finset.univ.filter (fun r : Fin k => α r = d)).card =
        (Finset.univ.filter (fun i : K => len i = d)).card := by
      refine PEqualNP.Outside.L_pcx_391.card_filter_eq_of_prod_one_add_pow α len hα_pos
        (fun i => Nat.succ_pos _) ?_
      intro W
      have hW := hpoly_eq (W : ℤ) 1
      have hW' : ∏ r : Fin k, ((1 : ℤ) + (W : ℤ) ^ α r) = ∏ i : K, ((1 : ℤ) + (W : ℤ) ^ len i) := by
        simpa using hW
      exact_mod_cast hW'
    have hα_bounds : ∀ r : Fin k, B < 4 * α r ∧ 2 * α r < B := by
      intro r
      have hpos_card : 0 < (Finset.univ.filter (fun i : K => len i = α r)).card := by
        rw [← hmult (α r)]
        exact Finset.card_pos.mpr ⟨r, by simp⟩
      rcases Finset.card_pos.mp hpos_card with ⟨i, hi⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [← hi]
      exact hbounds i
    let q : ℕ → ℕ := fun r => pos r / 2
    have hq_step : ∀ r : Fin k, q (r.val + 1) = q r.val + α r := by
      intro r
      have h1 := hstep_pos r
      have h2 := hpos_even r.val (le_of_lt r.isLt)
      dsimp only [q]
      omega
    have hq_mono : ∀ r1 r2 : ℕ, r1 < r2 → r2 ≤ k → q r1 < q r2 := by
      intro r1 r2 hlt hle
      have h1 := hpos_mono r1 r2 hlt hle
      have he1 := hpos_even r1 (by omega)
      have he2 := hpos_even r2 hle
      dsimp only [q]
      omega
    have hq_anchor : ∀ c : ℕ, c ≤ m → 3 * c ≤ k ∧ q (3 * c) = c * B := by
      intro c
      induction c with
      | zero =>
        intro _
        exact ⟨Nat.zero_le k, by simp [q, hpos0]⟩
      | succ c ihc =>
        intro hc
        rcases ihc (by omega) with ⟨h3c, hq3c⟩
        have hex : ∃ r1 : ℕ, r1 ≤ k ∧ q r1 = (c + 1) * B := by
          by_cases hcm : c + 1 = m
          · exact ⟨k, le_rfl, by simp only [q, hposk, hcm]; omega⟩
          · have hc1 : c + 1 < m := by omega
            let v : Bool × T := (false, (⟨c + 1, hc1⟩, 0))
            have hv : p v ≠ none := by
              rw [hanc ⟨c + 1, hc1⟩]; simp
            have heS : (PEqualNP.Outside.L_pcx_391.ringEquiv t b).symm v ∈ S := by
              simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
              exact hv
            have hrng : (PEqualNP.Outside.L_pcx_391.ringEquiv t b).symm v ∈ Set.range emb := by
              rw [Finset.range_orderEmbOfFin]; exact heS
            rcases hrng with ⟨r1, hr1⟩
            refine ⟨r1.val, le_of_lt r1.isLt, ?_⟩
            have hval : (emb r1).val = 2 * ((c + 1) * B) := by
              rw [hr1]
              change 2 * ((c + 1) * B + 0) = 2 * ((c + 1) * B)
              omega
            dsimp only [q]
            rw [hpos_fin r1, hval]
            omega
        rcases hex with ⟨r1, hr1_le, hqr1⟩
        have hlt_r : 3 * c < r1 := by
          by_contra hge
          rcases eq_or_lt_of_le (show r1 ≤ 3 * c by omega) with rfl | hlt
          · have : (c + 1) * B = c * B := by rw [← hqr1, hq3c]
            have : (c + 1) * B = c * B + B := by ring
            omega
          · have := hq_mono r1 (3 * c) hlt h3c
            have : (c + 1) * B = c * B + B := by ring
            omega
        let u := r1 - 3 * c
        have hu_pos : 0 < u := by omega
        have hsum_α : ∀ n : ℕ, 3 * c + n ≤ k →
            ∑ j ∈ Finset.range n, (if h : 3 * c + j < k then α ⟨3 * c + j, h⟩ else 0) =
              q (3 * c + n) - q (3 * c) := by
          intro n
          induction n with
          | zero => intro _; simp
          | succ n ihn =>
            intro hn
            rw [Finset.sum_range_succ, ihn (by omega)]
            have hlt : 3 * c + n < k := by omega
            simp only [hlt, ↓reduceDIte]
            have hst := hq_step ⟨3 * c + n, hlt⟩
            dsimp only at hst
            have hge : q (3 * c) ≤ q (3 * c + n) := by
              rcases Nat.eq_zero_or_pos n with rfl | hnp
              · exact le_rfl
              · exact le_of_lt (hq_mono (3 * c) (3 * c + n) (by omega) (by omega))
            have hadd_eq : 3 * c + (n + 1) = 3 * c + n + 1 := by omega
            rw [hadd_eq, hst]
            omega
        have hsum_u : ∑ j ∈ Finset.range u, (if h : 3 * c + j < k then α ⟨3 * c + j, h⟩ else 0) = B := by
          have h := hsum_α u (by omega)
          have hr1_eq : 3 * c + u = r1 := by omega
          rw [hr1_eq, hqr1, hq3c] at h
          have : (c + 1) * B = c * B + B := by ring
          omega
        have hlow : ∀ n : ℕ, 3 * c + n ≤ k → n * B < 4 * ∑ j ∈ Finset.range n,
            (if h : 3 * c + j < k then α ⟨3 * c + j, h⟩ else 0) ∨ n = 0 := by
          intro n
          induction n with
          | zero => intro _; right; rfl
          | succ n ihn =>
            intro hn
            left
            rw [Finset.sum_range_succ]
            have hlt : 3 * c + n < k := by omega
            simp only [hlt, ↓reduceDIte]
            have hb := (hα_bounds ⟨3 * c + n, hlt⟩).1
            rcases ihn (by omega) with hprev | rfl
            · have : (n + 1) * B = n * B + B := by ring
              omega
            · simp only [Finset.range_zero, Finset.sum_empty, zero_add, one_mul]
              exact hb
        have hhigh : ∀ n : ℕ, 3 * c + n ≤ k → 2 * ∑ j ∈ Finset.range n,
            (if h : 3 * c + j < k then α ⟨3 * c + j, h⟩ else 0) < n * B ∨ n = 0 := by
          intro n
          induction n with
          | zero => intro _; right; rfl
          | succ n ihn =>
            intro hn
            left
            rw [Finset.sum_range_succ]
            have hlt : 3 * c + n < k := by omega
            simp only [hlt, ↓reduceDIte]
            have hb := (hα_bounds ⟨3 * c + n, hlt⟩).2
            rcases ihn (by omega) with hprev | rfl
            · have : (n + 1) * B = n * B + B := by ring
              omega
            · simp only [Finset.range_zero, Finset.sum_empty, zero_add, one_mul]
              exact hb
        have hu_lt4 : u < 4 := by
          rcases hlow u (by omega) with h | h
          · rw [hsum_u] at h
            by_contra hge
            have : 4 * B ≤ u * B := Nat.mul_le_mul_right B (by omega)
            omega
          · omega
        have hu_gt2 : 2 < u := by
          rcases hhigh u (by omega) with h | h
          · rw [hsum_u] at h
            by_contra hle
            have : u * B ≤ 2 * B := Nat.mul_le_mul_right B (by omega)
            omega
          · omega
        have hu3 : u = 3 := by omega
        have hr1_eq : r1 = 3 * (c + 1) := by omega
        rw [← hr1_eq]
        exact ⟨hr1_le, hqr1⟩
    let idxEquiv : K ≃ Fin k :=
      { toFun := fun cu => ⟨3 * cu.1.val + cu.2.val, by omega⟩
        invFun := fun r => (⟨r.val / 3, by omega⟩, ⟨r.val % 3, Nat.mod_lt _ (by omega)⟩)
        left_inv := fun ⟨c, u⟩ => by
          ext
          · dsimp only; omega
          · dsimp only; omega
        right_inv := fun r => by
          ext; dsimp only; exact Nat.div_add_mod r.val 3 }
    let f : K → ℕ := fun cu => α (idxEquiv cu)
    refine ⟨hside_false, f, fun cu => hα_pos (idxEquiv cu), ?_, ?_, ?_⟩
    · intro c
      rw [Fin.sum_univ_three]
      have h0 := (hq_anchor c.val (le_of_lt c.isLt)).2
      have h1 := (hq_anchor (c.val + 1) c.isLt).2
      have hs0 := hq_step (idxEquiv (c, 0))
      have hs1 := hq_step (idxEquiv (c, 1))
      have hs2 := hq_step (idxEquiv (c, 2))
      have hidx0 : (idxEquiv (c, 0)).val = 3 * c.val := by simp [idxEquiv]
      have hidx1 : (idxEquiv (c, 1)).val = 3 * c.val + 1 := by simp [idxEquiv]
      have hidx2 : (idxEquiv (c, 2)).val = 3 * c.val + 2 := by simp [idxEquiv]
      rw [hidx0] at hs0
      rw [hidx1] at hs1
      rw [hidx2] at hs2
      have h32 : 3 * c.val + 1 + 1 = 3 * c.val + 2 := by omega
      rw [h32] at hs1
      have h3c1 : 3 * (c.val + 1) = 3 * c.val + 2 + 1 := by omega
      rw [h3c1] at h1
      have : (c.val + 1) * B = c.val * B + B := by ring
      dsimp only [f]
      omega
    · intro d
      rw [← hmult d]
      refine Finset.card_bij (fun cu _ => idxEquiv cu) ?_ ?_ ?_
      · intro cu hcu; simpa [f] using hcu
      · intro a _ b _ h; exact idxEquiv.injective h
      · intro r hr; exact ⟨idxEquiv.symm r, by simpa [f] using hr, idxEquiv.apply_symm_apply r⟩
    · funext ⟨side, ⟨c, r⟩⟩
      cases side
      · have hiff_pin : p (false, (c, r)) ≠ none ↔
            (r.val = 0 ∨ r.val = f (c, 0) ∨ r.val = f (c, 0) + f (c, 1)) := by
          have hq0 := (hq_anchor c.val (le_of_lt c.isLt)).2
          have hs0 := hq_step (idxEquiv (c, 0))
          have hs1 := hq_step (idxEquiv (c, 1))
          have hidx0 : (idxEquiv (c, 0)).val = 3 * c.val := by simp [idxEquiv]
          have hidx1 : (idxEquiv (c, 1)).val = 3 * c.val + 1 := by simp [idxEquiv]
          rw [hidx0] at hs0
          rw [hidx1] at hs1
          have h3c_lt : 3 * c.val + 2 < k := by omega
          constructor
          · intro hne
            have heS : (PEqualNP.Outside.L_pcx_391.ringEquiv t b).symm (false, (c, r)) ∈ S := by
              simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
              exact hne
            have hrng : (PEqualNP.Outside.L_pcx_391.ringEquiv t b).symm (false, (c, r)) ∈ Set.range emb := by
              rw [Finset.range_orderEmbOfFin]; exact heS
            rcases hrng with ⟨idx, hidx⟩
            have hqr : q idx.val = c.val * B + r.val := by
              have hval : (emb idx).val = 2 * (c.val * B + r.val) := by
                rw [hidx]; rfl
              dsimp only [q]
              rw [hpos_fin idx, hval]
              omega
            have hge3c : 3 * c.val ≤ idx.val := by
              by_contra hlt
              have := hq_mono idx.val (3 * c.val) (by omega) (by omega)
              omega
            have hlt3c3 : idx.val < 3 * (c.val + 1) := by
              by_contra hge
              have hqnext := (hq_anchor (c.val + 1) c.isLt).2
              have hle : q (3 * (c.val + 1)) ≤ q idx.val := by
                rcases eq_or_lt_of_le (show 3 * (c.val + 1) ≤ idx.val by omega) with heq | hlt
                · rw [heq]
                · exact le_of_lt (hq_mono _ _ hlt (le_of_lt idx.isLt))
              have : (c.val + 1) * B = c.val * B + B := by ring
              have hrlt : r.val < B := r.isLt
              omega
            have hcases : idx.val = 3 * c.val ∨ idx.val = 3 * c.val + 1 ∨ idx.val = 3 * c.val + 2 := by omega
            dsimp only [f]
            rcases hcases with h | h | h
            · rw [h, hq0] at hqr; left; omega
            · rw [h, hs0, hq0] at hqr; right; left; omega
            · rw [h, show 3 * c.val + 2 = 3 * c.val + 1 + 1 by omega, hs1, hs0, hq0] at hqr
              right; right; omega
          · intro hor
            have hex : ∃ idx : Fin k, q idx.val = c.val * B + r.val := by
              dsimp only [f] at hor
              rcases hor with hr0 | hr1 | hr2
              · exact ⟨idxEquiv (c, 0), by rw [hidx0, hq0, hr0, add_zero]⟩
              · exact ⟨idxEquiv (c, 1), by rw [hidx1, hs0, hq0, hr1]⟩
              · exact ⟨idxEquiv (c, 2), by
                  have hidx2 : (idxEquiv (c, 2)).val = 3 * c.val + 1 + 1 := by simp [idxEquiv]
                  rw [hidx2, hs1, hs0, hq0, hr2]; omega⟩
            rcases hex with ⟨idx, hidx⟩
            have hpos_eq : (emb idx).val = 2 * (c.val * B + r.val) := by
              have hev := hpos_even idx.val (le_of_lt idx.isLt)
              dsimp only [q] at hidx
              rw [hpos_fin idx] at hidx hev
              omega
            have heq_ring : PEqualNP.Outside.L_pcx_391.ringEquiv t b (emb idx) = (false, (c, r)) := by
              apply (PEqualNP.Outside.L_pcx_391.ringEquiv t b).symm.injective
              rw [Equiv.symm_apply_apply]
              ext
              exact hpos_eq
            have hmemS : p (PEqualNP.Outside.L_pcx_391.ringEquiv t b (emb idx)) ≠ none := by
              have hm := Finset.orderEmbOfFin_mem S rfl idx
              exact (Finset.mem_filter.mp hm).2
            rw [heq_ring] at hmemS
            exact hmemS
        unfold PEqualNP.Outside.L_pcx_391.pinOf
        dsimp only
        by_cases hcond : r.val = 0 ∨ r.val = f (c, 0) ∨ r.val = f (c, 0) + f (c, 1)
        · rw [ite_eq_left_iff.mpr (fun hn => absurd ⟨rfl, hcond⟩ hn)]
          exact hall (false, (c, r)) (hiff_pin.mpr hcond)
        · rw [ite_eq_right_iff.mpr (fun hy => absurd hy.2 hcond)]
          by_contra hne
          exact hcond (hiff_pin.mp hne)
      · unfold PEqualNP.Outside.L_pcx_391.pinOf
        simp only [Bool.true_eq_false, false_and, ↓reduceIte]
        by_contra hne
        have := (hside_false (true, (c, r)) hne).1
        cases this
  have hpart2 : ∀ p ∈ good, ∀ v, p v ≠ none → v.1 = false ∧ p v = some false :=
    fun p hp => (hgood_extract p hp).1
  let mapSlot : Equiv.Perm K → (Bool × T → Option Bool) :=
    fun π => PEqualNP.Outside.L_pcx_391.pinOf t b (fun k => len (π k))
  have hmaps : ∀ π ∈ slots, mapSlot π ∈ good := by
    intro π hπ
    simp only [slots, Finset.mem_filter, Finset.mem_univ, true_and] at hπ
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · intro c
      simp [mapSlot, PEqualNP.Outside.L_pcx_391.pinOf]
    · funext d
      exact PEqualNP.Outside.L_pcx_391.hist_pinOf_eq_source t b s hsum π hπ d
  have hlen_lt : ∀ i : K, len i < B + 1 := by
    intro i
    have := (hbounds i).2
    omega
  have hfib : ∀ p ∈ good, (slots.filter (fun π => mapSlot π = p)).card = copies := by
    intro p hp
    rcases (hgood_extract p hp).2 with ⟨f, hf_pos, hf_sum, hf_card, hp_eq⟩
    have hf_lt : ∀ k : K, f k < B + 1 := by
      intro k
      have hpos_card : 0 < (Finset.univ.filter (fun i : K => len i = f k)).card := by
        rw [← hf_card (f k)]
        exact Finset.card_pos.mpr ⟨k, by simp⟩
      rcases Finset.card_pos.mp hpos_card with ⟨i, hi⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [← hi]
      exact hlen_lt i
    rcases PEqualNP.Outside.L_pcx_391.exists_perm_of_card_filter_eq B f len hf_lt hlen_lt hf_card with ⟨π0, hπ0⟩
    have hcard_eq : (slots.filter (fun π => mapSlot π = p)).card =
        (Finset.univ.filter (fun τ : Equiv.Perm K => ∀ k, len (τ k) = len k)).card := by
      symm
      refine Finset.card_bij (fun τ _ => π0.trans τ) ?_ ?_ ?_
      · intro τ hτ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ
        simp only [slots, Finset.mem_filter, Finset.mem_univ, true_and]
        have hlen_eq : (fun k => len ((π0.trans τ) k)) = f := by
          funext k
          simp only [Equiv.trans_apply, hτ (π0 k), hπ0 k]
        refine ⟨?_, ?_⟩
        · intro c
          have : (∑ u : Fin 3, len ((π0.trans τ) (c, u))) = ∑ u : Fin 3, f (c, u) := by
            refine Finset.sum_congr rfl (fun u _ => congrFun hlen_eq (c, u))
          rw [this, hf_sum c]
        · dsimp only [mapSlot]
          rw [hlen_eq, hp_eq]
      · intro τ1 _ τ2 _ heq
        exact Equiv.ext fun k => by
          have := Equiv.congr_fun heq (π0.symm k)
          simpa using this
      · intro π hπ
        simp only [slots, Finset.mem_filter, Finset.mem_univ, true_and] at hπ
        rcases hπ with ⟨hπ_sum, hπ_map⟩
        have hlen_eq : (fun k => len (π k)) = f :=
          PEqualNP.Outside.L_pcx_391.pinOf_inj t b _ f
            (fun k => Nat.succ_pos _) hf_pos hπ_sum hf_sum (hπ_map.trans hp_eq)
        refine ⟨π0.symm.trans π, ?_, Equiv.ext fun k => by simp⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro k
        have h1 : len (π (π0.symm k)) = f (π0.symm k) := congrFun hlen_eq (π0.symm k)
        have h2 : len (π0 (π0.symm k)) = f (π0.symm k) := hπ0 (π0.symm k)
        simp only [Equiv.apply_symm_apply] at h2
        simpa only [Equiv.trans_apply] using h1.trans h2.symm
    rw [hcard_eq]
    exact PEqualNP.Outside.L_pcx_391.perm_preserving_card B len hlen_lt
  have hpart4 : copies * good.card = slots.card := by
    have hcard := Finset.card_eq_sum_card_fiberwise (f := mapSlot) (s := slots) (t := good)
      (fun π hπ => hmaps π hπ)
    rw [hcard, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]
  have hcopies_pos : 0 < copies :=
    PEqualNP.Outside.L_pcx_391.prod_pos_nat _ _ (fun j _ => Nat.factorial_pos _)
  have hpart3 : good.Nonempty ↔ slots.Nonempty := by
    rw [← Finset.card_pos, ← Finset.card_pos, ← hpart4]
    exact ⟨fun h => Nat.mul_pos hcopies_pos h, fun h => by
      by_contra h0
      have : good.card = 0 := by omega
      rw [this, mul_zero] at h
      omega⟩
  exact ⟨hpart1, hpart2, hpart3, hpart4⟩
