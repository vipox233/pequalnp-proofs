import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_388
import PEqualNP.Outside.L_lib_471

namespace PEqualNP.Outside.L_clb_088_aux

private def nx {s : ℕ} (state : Fin s → Bool) (b : Bool) : Fin s → Bool :=
  fun j => if h : j.val + 1 < s then state ⟨j.val + 1, h⟩ else b

private def stSeq {s : ℕ} (beta : ℕ → Bool) (p : Fin s → Bool) : ℕ → (Fin s → Bool)
  | 0 => p
  | k + 1 => nx (stSeq beta p k) (beta k)

private def yfun {s : ℕ} (p : Fin s → Bool) (beta : ℕ → Bool) (m : ℕ) : Bool :=
  if h : m < s then p ⟨m, h⟩ else beta (m - s)

private def bitsOf (n : ℕ) (b : Fin n → Bool) (k : ℕ) : Bool :=
  if h : k < n then b ⟨k, h⟩ else false

private def pw (t : ℕ) (b : Fin (t + 1) → Bool) (k : ℕ) : Bool :=
  b (Fin.ofNat (t + 1) k)

private def Good {s : ℕ} : (n : ℕ) → (Fin n → (Fin s → Bool) → Bool → Bool) →
    (Fin s → Bool) → (Fin s → Bool) → (Fin n → Bool) → Bool
  | 0, _, p, q, _ => decide (p = q)
  | n + 1, F, p, q, b =>
    F 0 p (b 0) && Good n (fun i => F i.succ) (nx p (b 0)) q (Fin.tail b)

private def Mat {s n : ℕ} (F : Fin n → (Fin s → Bool) → Bool → Bool) (i : Fin n) :
    Matrix (Fin s → Bool) (Fin s → Bool) ℕ :=
  Matrix.of fun p q => (Finset.univ.filter fun bit : Bool => F i p bit = true ∧ nx p bit = q).card

private theorem stSeq_shift {s : ℕ} (beta : ℕ → Bool) : ∀ (k : ℕ) (p : Fin s → Bool),
    stSeq beta p (k + 1) = stSeq (fun i => beta (i + 1)) (nx p (beta 0)) k := by
  intro k
  induction k with
  | zero => intro p; rfl
  | succ k ih =>
    intro p
    show nx (stSeq beta p (k + 1)) (beta (k + 1)) =
      nx (stSeq (fun i => beta (i + 1)) (nx p (beta 0)) k) (beta (k + 1))
    rw [ih p]

private theorem card_good_succ {s n : ℕ} (F : Fin (n + 1) → (Fin s → Bool) → Bool → Bool)
    (p q : Fin s → Bool) :
    (Finset.univ.filter fun b : Fin (n + 1) → Bool => Good (n + 1) F p q b = true).card =
      ∑ bit : Bool, if F 0 p bit = true then
        (Finset.univ.filter fun b : Fin n → Bool =>
          Good n (fun i => F i.succ) (nx p bit) q b = true).card
      else 0 := by
  rw [Finset.card_filter, ← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun bit _ => ?_)
  rw [Finset.card_filter]
  by_cases hF : F 0 p bit = true
  · simp [hF, Good, Fin.consEquiv_apply]
  · simp [hF, Good, Fin.consEquiv_apply]

private theorem prod_apply {s : ℕ} : ∀ (n : ℕ) (F : Fin n → (Fin s → Bool) → Bool → Bool)
    (p q : Fin s → Bool),
    (List.ofFn (fun i => Mat F i)).prod p q =
      (Finset.univ.filter fun b : Fin n → Bool => Good n F p q b = true).card := by
  intro n
  induction n with
  | zero =>
    intro F p q
    by_cases h : p = q
    · subst h
      simp [Good, Matrix.one_apply]
    · simp [Good, Matrix.one_apply, h]
  | succ n ih =>
    intro F p q
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply, card_good_succ]
    have hM : ∀ r, Mat F 0 p r =
        (Finset.univ.filter fun bit : Bool => F 0 p bit = true ∧ nx p bit = r).card :=
      fun r => rfl
    have hP : ∀ r, (List.ofFn fun i => Mat F i.succ).prod r q =
        (Finset.univ.filter fun b : Fin n → Bool =>
          Good n (fun i => F i.succ) r q b = true).card := fun r => ih (fun i => F i.succ) r q
    simp only [hM, hP]
    have hcard : ∀ r : Fin s → Bool,
        (Finset.univ.filter fun bit : Bool => F 0 p bit = true ∧ nx p bit = r).card *
          (Finset.univ.filter fun b : Fin n → Bool =>
            Good n (fun i => F i.succ) r q b = true).card =
        ∑ bit : Bool, if (F 0 p bit = true ∧ nx p bit = r) then
          (Finset.univ.filter fun b : Fin n → Bool =>
            Good n (fun i => F i.succ) r q b = true).card else 0 := by
      intro r
      rw [Finset.card_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun bit _ => ?_)
      split_ifs <;> simp_all
    simp only [hcard]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun bit _ => ?_)
    by_cases hF : F 0 p bit = true
    · simp [hF]
    · simp [hF]

private theorem good_iff {s : ℕ} : ∀ (n : ℕ) (F : Fin n → (Fin s → Bool) → Bool → Bool)
    (p q : Fin s → Bool) (b : Fin n → Bool),
    Good n F p q b = true ↔
      (stSeq (bitsOf n b) p n = q ∧
        ∀ (k : ℕ) (hk : k < n), F ⟨k, hk⟩ (stSeq (bitsOf n b) p k) (bitsOf n b k) = true) := by
  intro n
  induction n with
  | zero =>
    intro F p q b
    simp [Good, stSeq]
  | succ n ih =>
    intro F p q b
    have hb0 : bitsOf (n + 1) b 0 = b 0 := by simp [bitsOf]
    have htail : (fun i => bitsOf (n + 1) b (i + 1)) = bitsOf n (Fin.tail b) := by
      funext i
      unfold bitsOf
      by_cases h : i < n
      · simp [h, Fin.tail]
      · simp [h]
    have e1 : ∀ k, bitsOf (n + 1) b (k + 1) = bitsOf n (Fin.tail b) k := fun k => congrFun htail k
    constructor
    · intro h
      simp only [Good, Bool.and_eq_true] at h
      obtain ⟨h0, h1⟩ := h
      rw [ih] at h1
      obtain ⟨hq, hk⟩ := h1
      refine ⟨?_, ?_⟩
      · rw [stSeq_shift, htail, hb0]
        exact hq
      · intro k hk'
        cases k with
        | zero => simpa [stSeq, hb0] using h0
        | succ k =>
          rw [stSeq_shift, htail, hb0, e1]
          exact hk k (by omega)
    · rintro ⟨hq, hall⟩
      simp only [Good, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · have h0 := hall 0 (by omega)
        simpa [stSeq, hb0] using h0
      · rw [ih]
        refine ⟨?_, ?_⟩
        · rw [stSeq_shift, htail, hb0] at hq
          exact hq
        · intro k hk
          have h2 := hall (k + 1) (by omega)
          rw [stSeq_shift, htail, hb0, e1] at h2
          exact h2

private theorem stSeq_eq_yfun {s : ℕ} (beta : ℕ → Bool) (p : Fin s → Bool) :
    ∀ (k j : ℕ) (hj : j < s), stSeq beta p k ⟨j, hj⟩ = yfun p beta (k + j) := by
  intro k
  induction k with
  | zero => intro j hj; simp [stSeq, yfun, hj]
  | succ k ih =>
    intro j hj
    show nx (stSeq beta p k) (beta k) ⟨j, hj⟩ = yfun p beta (k + 1 + j)
    simp only [nx]
    by_cases h : j + 1 < s
    · rw [dif_pos h, ih (j + 1) h]
      congr 1
      omega
    · rw [dif_neg h]
      unfold yfun
      rw [dif_neg (by omega), show k + 1 + j - s = k by omega]

private theorem stSeq_agree {s : ℕ} (N : ℕ) (beta1 beta2 : ℕ → Bool) (p : Fin s → Bool)
    (hag : ∀ k, k < N → beta1 k = beta2 k) :
    ∀ m, m ≤ N → stSeq beta1 p m = stSeq beta2 p m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    show nx (stSeq beta1 p m) (beta1 m) = nx (stSeq beta2 p m) (beta2 m)
    rw [ih (by omega), hag m (by omega)]

private theorem yfun_per {s N : ℕ} (beta : ℕ → Bool) (p : Fin s → Bool) (hN : ∀ k, beta (k + N) = beta k)
    (hcl : stSeq beta p N = p) (m : ℕ) : yfun p beta (m + N) = yfun p beta m := by
  by_cases hm : m < s
  · have h1 := stSeq_eq_yfun beta p N m hm
    rw [hcl] at h1
    rw [Nat.add_comm m N, ← h1]
    simp [yfun, hm]
  · unfold yfun
    rw [dif_neg (by omega), dif_neg hm, show m + N - s = (m - s) + N by omega, hN]

private theorem yfun_mod {s N : ℕ} (beta : ℕ → Bool) (p : Fin s → Bool) (hN : ∀ k, beta (k + N) = beta k)
    (hcl : stSeq beta p N = p) (m : ℕ) : yfun p beta (m % N) = yfun p beta m := by
  have hq : ∀ q m, yfun p beta (m + N * q) = yfun p beta m := by
    intro q
    induction q with
    | zero => intro m; simp
    | succ q ih =>
      intro m
      rw [show m + N * (q + 1) = (m + N * q) + N by ring, yfun_per beta p hN hcl, ih]
  have h := hq (m / N) (m % N)
  rw [Nat.mod_add_div] at h
  exact h.symm

private theorem pw_per (t : ℕ) (b : Fin (t + 1) → Bool) (k : ℕ) : pw t b (k + (t + 1)) = pw t b k := by
  unfold pw
  congr 1
  apply Fin.ext
  show (k + (t + 1)) % (t + 1) = k % (t + 1)
  rw [Nat.add_mod_right]

private theorem ofNat_val (t : ℕ) (i : Fin (t + 1)) : Fin.ofNat (t + 1) i.val = i := by
  apply Fin.ext
  show i.val % (t + 1) = i.val
  exact Nat.mod_eq_of_lt i.isLt

private theorem good_closure {s t : ℕ} (test : Fin (t + 1) → (Fin s → Bool) → Bool → Bool)
    (p : Fin s → Bool) (b : Fin (t + 1) → Bool) (h : Good (t + 1) test p p b = true) :
    stSeq (pw t b) p (t + 1) = p ∧
      ∀ k (hk : k < t + 1), test ⟨k, hk⟩ (stSeq (pw t b) p k) (pw t b k) = true := by
  have hg := (good_iff (t + 1) test p p b).1 h
  have hag : ∀ m, m ≤ t + 1 → stSeq (bitsOf (t + 1) b) p m = stSeq (pw t b) p m := by
    apply stSeq_agree (t + 1)
    intro k hk
    simp [bitsOf, pw, hk, Fin.ofNat, Nat.mod_eq_of_lt hk]
  refine ⟨?_, ?_⟩
  · rw [← hag (t + 1) le_rfl]
    exact hg.1
  · intro k hk
    have h2 := hg.2 k hk
    rw [hag k (by omega)] at h2
    have hb : bitsOf (t + 1) b k = pw t b k := by
      simp [bitsOf, pw, hk, Fin.ofNat, Nat.mod_eq_of_lt hk]
    rwa [hb] at h2

private def Phi (t s : ℕ) (x : (Fin s → Bool) × (Fin (t + 1) → Bool)) : Fin (t + 1) → Bool :=
  fun i => yfun x.1 (pw t x.2) i.val

private def Psi (t s : ℕ) (w : Fin (t + 1) → Bool) : (Fin s → Bool) × (Fin (t + 1) → Bool) :=
  (fun j => w (Fin.ofNat (t + 1) j.val), fun k => w (Fin.ofNat (t + 1) (k.val + s)))

private theorem phi_ofNat (t s : ℕ) (test : Fin (t + 1) → (Fin s → Bool) → Bool → Bool)
    (x : (Fin s → Bool) × (Fin (t + 1) → Bool)) (h : Good (t + 1) test x.1 x.1 x.2 = true)
    (m : ℕ) : Phi t s x (Fin.ofNat (t + 1) m) = yfun x.1 (pw t x.2) m := by
  unfold Phi
  have hc := (good_closure test x.1 x.2 h).1
  exact yfun_mod (pw t x.2) x.1 (pw_per t x.2) hc m

private theorem psi_yfun (t s : ℕ) (w : Fin (t + 1) → Bool) (m : ℕ) :
    yfun (Psi t s w).1 (pw t (Psi t s w).2) m = w (Fin.ofNat (t + 1) m) := by
  by_cases hm : m < s
  · unfold yfun
    rw [dif_pos hm]
    rfl
  · unfold yfun
    rw [dif_neg hm]
    show w (Fin.ofNat (t + 1) ((Fin.ofNat (t + 1) (m - s)).val + s)) = w (Fin.ofNat (t + 1) m)
    congr 1
    apply Fin.ext
    show ((m - s) % (t + 1) + s) % (t + 1) = m % (t + 1)
    rw [Nat.mod_add_mod, show m - s + s = m by omega]

private theorem dir2 (t s : ℕ) (test : Fin (t + 1) → (Fin s → Bool) → Bool → Bool)
    (x : (Fin s → Bool) × (Fin (t + 1) → Bool)) (h : Good (t + 1) test x.1 x.1 x.2 = true) :
    ∀ a : Fin (t + 1),
      test a (fun pos : Fin s => Phi t s x (Fin.ofNat (t + 1) (a.val + pos.val)))
        (Phi t s x (Fin.ofNat (t + 1) (a.val + s))) = true := by
  intro a
  obtain ⟨hcl, hall⟩ := good_closure test x.1 x.2 h
  have hA := hall a.val a.isLt
  have e1 : (fun pos : Fin s => Phi t s x (Fin.ofNat (t + 1) (a.val + pos.val))) =
      stSeq (pw t x.2) x.1 a.val := by
    funext pos
    rw [phi_ofNat t s test x h]
    exact (stSeq_eq_yfun (pw t x.2) x.1 a.val pos.val pos.isLt).symm
  have e2 : Phi t s x (Fin.ofNat (t + 1) (a.val + s)) = pw t x.2 a.val := by
    rw [phi_ofNat t s test x h]
    unfold yfun
    rw [dif_neg (by omega), show a.val + s - s = a.val by omega]
  rw [e1, e2]
  exact hA

private theorem dir1 (t s : ℕ) (test : Fin (t + 1) → (Fin s → Bool) → Bool → Bool) (w : Fin (t + 1) → Bool)
    (hacc : ∀ a : Fin (t + 1), test a (fun pos : Fin s => w (Fin.ofNat (t + 1) (a.val + pos.val)))
      (w (Fin.ofNat (t + 1) (a.val + s))) = true) :
    Good (t + 1) test (Psi t s w).1 (Psi t s w).1 (Psi t s w).2 = true := by
  rw [good_iff]
  have hC : ∀ m, m ≤ t + 1 → ∀ j (hj : j < s),
      stSeq (bitsOf (t + 1) (Psi t s w).2) (Psi t s w).1 m ⟨j, hj⟩ = pw t w (m + j) := by
    intro m
    induction m with
    | zero => intro _ j hj; simp [stSeq, Psi, pw, hj]
    | succ m ih =>
      intro hm j hj
      show nx (stSeq (bitsOf (t + 1) (Psi t s w).2) (Psi t s w).1 m)
        (bitsOf (t + 1) (Psi t s w).2 m) ⟨j, hj⟩ = pw t w (m + 1 + j)
      simp only [nx]
      by_cases h : j + 1 < s
      · rw [dif_pos h, ih (by omega) (j + 1) h, show m + 1 + j = m + (j + 1) by omega]
      · rw [dif_neg h]
        have hbit : bitsOf (t + 1) (Psi t s w).2 m = pw t w (m + s) := by
          unfold bitsOf
          rw [dif_pos (by omega)]
          rfl
        rw [hbit, show m + 1 + j = m + s by omega]
  constructor
  · funext j
    show stSeq (bitsOf (t + 1) (Psi t s w).2) (Psi t s w).1 (t + 1) ⟨j.val, j.isLt⟩ =
      w (Fin.ofNat (t + 1) j.val)
    refine (hC (t + 1) le_rfl j.val j.isLt).trans ?_
    rw [Nat.add_comm (t + 1) j.val]
    exact pw_per t w j.val
  · intro k hk
    have hA := hacc ⟨k, hk⟩
    have e : stSeq (bitsOf (t + 1) (Psi t s w).2) (Psi t s w).1 k =
        fun pos : Fin s => w (Fin.ofNat (t + 1) (k + pos.val)) := by
      funext pos
      exact hC k (by omega) pos.val pos.isLt
    have e2 : bitsOf (t + 1) (Psi t s w).2 k = w (Fin.ofNat (t + 1) (k + s)) := by
      unfold bitsOf
      rw [dif_pos hk]
      rfl
    rw [e, e2]
    exact hA


private theorem trace_eq_card (t s : ℕ) (test : Fin (t + 1) → (Fin s → Bool) → Bool → Bool) :
    Matrix.trace (List.ofFn (fun i : Fin (t + 1) => Mat test i)).prod =
      (Finset.univ.filter (fun w : Fin (t + 1) → Bool =>
        ∀ a : Fin (t + 1),
          test a (fun pos : Fin s => w (Fin.ofNat (t + 1) (a.val + pos.val)))
            (w (Fin.ofNat (t + 1) (a.val + s))) = true)).card := by
  show ∑ p, (List.ofFn (fun i : Fin (t + 1) => Mat test i)).prod p p = _
  rw [Finset.sum_congr rfl (fun p _ => prod_apply (t + 1) test p p)]
  have hsum : ∑ p : Fin s → Bool,
      (Finset.univ.filter fun b : Fin (t + 1) → Bool => Good (t + 1) test p p b = true).card =
      (Finset.univ.filter fun x : (Fin s → Bool) × (Fin (t + 1) → Bool) =>
        Good (t + 1) test x.1 x.1 x.2 = true).card := by
    simp only [Finset.card_filter]
    rw [Fintype.sum_prod_type]
  rw [hsum]
  apply Finset.card_nbij' (Phi t s) (Psi t s)
  · intro x hx
    simp only [Finset.mem_coe, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, Set.mem_setOf_eq,
      true_and] at hx ⊢
    exact dir2 t s test x hx
  · intro w hw
    simp only [Finset.mem_coe, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, Set.mem_setOf_eq,
      true_and] at hw ⊢
    exact dir1 t s test w hw
  · intro x hx
    simp only [Finset.mem_coe, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, Set.mem_setOf_eq,
      true_and] at hx
    apply Prod.ext
    · funext j
      show Phi t s x (Fin.ofNat (t + 1) j.val) = x.1 j
      rw [phi_ofNat t s test x hx]
      unfold yfun
      rw [dif_pos j.isLt]
    · funext k
      show Phi t s x (Fin.ofNat (t + 1) (k.val + s)) = x.2 k
      rw [phi_ofNat t s test x hx]
      unfold yfun
      rw [dif_neg (by omega), show k.val + s - s = k.val by omega]
      unfold pw
      rw [ofNat_val]
  · intro w _
    funext i
    show Phi t s (Psi t s w) i = w i
    unfold Phi
    rw [psi_yfun, ofNat_val]

private abbrev Row := Nat → Bool

private theorem ite_eq_of_iff {α : Type*} {P Q : Prop} [Decidable P] [Decidable Q]
    (h : P ↔ Q) (a b : α) : (if P then a else b) = (if Q then a else b) := by
  by_cases hp : P
  · simp [hp, h.mp hp]
  · have hq : ¬ Q := fun hq => hp (h.mpr hq)
    simp [hp, hq]

private def patAt (w n word site : Nat) : Nat :=
  (List.range (w + 1)).foldl (fun (acc bit : Nat) =>
    acc ||| ((word.testBit ((site + bit) % n)).toNat <<< bit)) 0

private def totalCount (w n : Nat) (rows : Nat → Row) : Nat :=
  ((List.range (2 ^ n)).filter (fun word => (List.range n).all (fun site =>
    rows site (patAt w n word site)))).length

private def runAlg (p n S : Nat) (start : Fin S)
    (step : Nat → Nat → Fin S → Row → Fin S) (table : Nat → Row) : Fin S :=
  (List.range p).foldl (fun prev passId =>
    (List.range n).foldl (fun state siteId => step passId siteId state (table siteId)) prev) start

private def stateToNat {w : Nat} (st : Fin w → Bool) : Nat :=
  (List.range w).foldl (fun acc bit =>
    acc ||| ((if h : bit < w then st ⟨bit, h⟩ else false).toNat <<< bit)) 0

private def patVal {w : Nat} (st : Fin w → Bool) (b : Bool) : Nat :=
  stateToNat st ||| (b.toNat <<< w)

private def stepMat (w : Nat) (row : Row) : Matrix (Fin w → Bool) (Fin w → Bool) Nat :=
  Matrix.of (fun p q =>
    (Finset.univ.filter (fun bit : Bool =>
      row (patVal p bit) = true ∧ nx p bit = q)).card)

private def rowOfTest {w : Nat} (f : (Fin w → Bool) → Bool → Bool) : Row :=
  fun pat => f (fun j => pat.testBit j.val) (pat.testBit w)

private theorem foldl_bits_spec (f : Nat → Bool) :
    ∀ (k b : Nat),
      ((List.range k).foldl (fun (acc bit : Nat) => acc ||| ((f bit).toNat <<< bit)) 0).testBit b =
      if b < k then f b else false := by
  intro k
  induction k with
  | zero => intro b; simp
  | succ k ih =>
    intro b
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [Nat.testBit_or, ih b, Nat.testBit_shiftLeft]
    by_cases hbk : b < k
    · have hlt : b < k + 1 := by omega
      have hge : ¬ (k ≤ b) := by omega
      simp [hbk, hlt, hge]
    · by_cases hbe : b = k
      · subst hbe
        simp only [lt_self_iff_false, ↓reduceIte, Nat.lt_add_one, le_refl,
          decide_true, Nat.sub_self, Bool.true_and, Bool.false_or]
        cases f b <;> decide
      · have hgt : ¬ (b < k + 1) := by omega
        have hpos : b - k ≠ 0 := by omega
        have hzero : (f k).toNat.testBit (b - k) = false := by
          cases f k
          · simp
          · simp only [Bool.toNat_true, Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not]
            have hdiv0 : 1 / 2 ^ (b - k) = 0 := Nat.div_eq_of_lt (Nat.one_lt_two_pow hpos)
            simp [hdiv0]
        simp [hbk, hgt, hzero]

private theorem stateToNat_testBit {w : Nat} (st : Fin w → Bool) (b : Nat) :
    (stateToNat st).testBit b = if h : b < w then st ⟨b, h⟩ else false := by
  unfold stateToNat
  rw [foldl_bits_spec (fun bit => if h : bit < w then st ⟨bit, h⟩ else false) w b]
  by_cases h : b < w <;> simp [h]

private theorem stateToNat_lt {w : Nat} (st : Fin w → Bool) : stateToNat st < 2 ^ w := by
  by_contra h
  push Not at h
  have hne : stateToNat st / 2 ^ w ≠ 0 := by
    have : 0 < stateToNat st / 2 ^ w := Nat.div_pos h (by positivity)
    omega
  obtain ⟨k, hk⟩ : ∃ k, (stateToNat st / 2 ^ w).testBit k = true := by
    have hlog := Nat.testBit_log2 (n := stateToNat st / 2 ^ w) hne
    exact ⟨Nat.log2 (stateToNat st / 2 ^ w), hlog⟩
  have hbit : (stateToNat st).testBit (w + k) = true := by
    rw [Nat.testBit_eq_decide_div_mod_eq, pow_add, ← Nat.div_div_eq_div_mul]
    rw [← Nat.testBit_eq_decide_div_mod_eq]
    exact hk
  rw [stateToNat_testBit] at hbit
  have hnot : ¬ (w + k < w) := by omega
  simp [hnot] at hbit

private theorem patVal_testBit {w : Nat} (st : Fin w → Bool) (bit : Bool) (j : Nat) :
    (patVal st bit).testBit j =
      if h : j < w then st ⟨j, h⟩ else if j = w then bit else false := by
  unfold patVal
  rw [Nat.testBit_or, stateToNat_testBit, Nat.testBit_shiftLeft]
  by_cases hj : j < w
  · have hge : ¬ (w ≤ j) := by omega
    simp [hj, hge]
  · by_cases heq : j = w
    · subst heq
      simp only [lt_self_iff_false, ↓reduceDIte, ↓reduceIte, le_refl, decide_true,
        Nat.sub_self, Bool.true_and, Bool.false_or]
      cases bit <;> decide
    · have hpos : j - w ≠ 0 := by omega
      have hzero : bit.toNat.testBit (j - w) = false := by
        cases bit
        · simp
        · simp only [Bool.toNat_true, Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not]
          have hdiv0 : 1 / 2 ^ (j - w) = 0 := Nat.div_eq_of_lt (Nat.one_lt_two_pow hpos)
          simp [hdiv0]
      simp [hj, heq, hzero]

private theorem rowOfTest_patVal {w : Nat} (f : (Fin w → Bool) → Bool → Bool)
    (st : Fin w → Bool) (bit : Bool) :
    rowOfTest f (patVal st bit) = f st bit := by
  unfold rowOfTest
  have h1 : (fun j : Fin w => (patVal st bit).testBit j.val) = st := by
    funext j
    rw [patVal_testBit]
    simp [j.isLt]
  have h2 : (patVal st bit).testBit w = bit := by
    rw [patVal_testBit]
    simp
  rw [h1, h2]

private theorem stepMat_rowOfTest {w : Nat} (f : (Fin w → Bool) → Bool → Bool) :
    stepMat w (rowOfTest f) =
      Matrix.of (fun p q =>
        (Finset.univ.filter (fun bit : Bool => f p bit = true ∧ nx p bit = q)).card) := by
  ext p q
  simp only [stepMat, Matrix.of_apply, rowOfTest_patVal]

private theorem list_filter_length_eq_finset_card (N : Nat) (p : Nat → Bool) :
    ((List.range N).filter p).length =
      ((Finset.univ : Finset (Fin N)).filter (fun x => p x.val = true)).card := by
  have h1 : ((List.range N).filter p).length = ((Finset.range N).filter (fun x => p x = true)).card := by
    rw [← List.toFinset_card_of_nodup ((List.nodup_range).filter p)]
    congr 1
    ext x
    simp [List.mem_range, Finset.mem_filter, Finset.mem_range]
  rw [h1]
  refine Finset.card_bij (fun x hx => ⟨x, Finset.mem_range.mp (Finset.mem_filter.mp hx).1⟩) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp hx).2
  · intro x1 _ x2 _ h
    exact congrArg Fin.val h
  · intro x hx
    refine ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr x.isLt, (Finset.mem_filter.mp hx).2⟩, rfl⟩

private theorem finRange_filter_length_eq_finset_card (N : Nat) (p : Fin N → Bool) :
    ((List.finRange N).filter p).length =
      ((Finset.univ : Finset (Fin N)).filter (fun x => p x = true)).card := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange N).filter p)]
  congr 1
  ext x
  simp [List.mem_finRange, Finset.mem_filter]

private theorem totalCount_eq_trace (w n : Nat) (hn : 0 < n) (rows : Nat → Row) :
    totalCount w n rows =
      Matrix.trace (List.ofFn (fun i : Fin n => stepMat w (rows i.val))).prod := by
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  have hlib := trace_eq_card t w (fun i st b => rows i.val (patVal st b))
  have hstep : (fun i : Fin (t + 1) => stepMat w (rows i.val)) =
      (fun i : Fin (t + 1) => Mat (fun (i : Fin (t + 1)) st b => rows i.val (patVal st b)) i) := by
    funext i
    rfl
  rw [hstep, hlib]
  unfold totalCount
  rw [list_filter_length_eq_finset_card (2 ^ (t + 1))]
  refine Finset.card_bij
    (fun (word : Fin (2 ^ (t + 1))) _ => fun (a : Fin (t + 1)) => word.val.testBit a.val) ?_ ?_ ?_
  · intro word hword
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hword ⊢
    rw [List.all_eq_true] at hword
    intro a
    have ha := hword a.val (List.mem_range.mpr a.isLt)
    have hpat : patVal (fun pos : Fin w => word.val.testBit (Fin.ofNat (t + 1) (a.val + pos.val)).val)
        (word.val.testBit (Fin.ofNat (t + 1) (a.val + w)).val) = patAt w (t + 1) word.val a.val := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [patVal_testBit, patAt, foldl_bits_spec]
      by_cases h1 : j < w
      · have h2 : j < w + 1 := by omega
        simp only [h1, ↓reduceDIte, h2, ↓reduceIte, Fin.val_ofNat]
      · by_cases h2 : j = w
        · subst h2
          simp only [lt_self_iff_false, ↓reduceDIte, ↓reduceIte, Nat.lt_add_one, Fin.val_ofNat]
        · have h3 : ¬ (j < w + 1) := by omega
          simp [h1, h2, h3]
    rw [hpat]
    exact ha
  · intro w1 _ w2 _ h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < t + 1
    · exact congrFun h ⟨j, hj⟩
    · have h1 : w1.val.testBit j = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le w1.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
      have h2 : w2.val.testBit j = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le w2.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
      rw [h1, h2]
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    refine ⟨⟨stateToNat v, stateToNat_lt v⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [List.all_eq_true]
      intro site hsite
      have hsite' : site < t + 1 := List.mem_range.mp hsite
      have ha := hv ⟨site, hsite'⟩
      have hpat : patAt w (t + 1) (stateToNat v) site =
          patVal (fun pos : Fin w => v (Fin.ofNat (t + 1) (site + pos.val)))
            (v (Fin.ofNat (t + 1) (site + w))) := by
        apply Nat.eq_of_testBit_eq
        intro j
        rw [patAt, foldl_bits_spec, patVal_testBit]
        by_cases h1 : j < w
        · have h2 : j < w + 1 := by omega
          simp only [h1, ↓reduceDIte, h2, ↓reduceIte, stateToNat_testBit]
          have hmod : (site + j) % (t + 1) < t + 1 := Nat.mod_lt _ (by omega)
          simp only [hmod, ↓reduceDIte]
          rfl
        · by_cases h2 : j = w
          · rw [h2]
            simp only [lt_self_iff_false, ↓reduceDIte, ↓reduceIte, Nat.lt_add_one, stateToNat_testBit]
            have hmod : (site + w) % (t + 1) < t + 1 := Nat.mod_lt _ (by omega)
            simp only [hmod, ↓reduceDIte]
            rfl
          · have h3 : ¬ (j < w + 1) := by omega
            simp [h1, h2, h3]
      rw [hpat]
      exact ha
    · funext a
      rw [stateToNat_testBit]
      simp [a.isLt]

private theorem prefixProd_succ (w : Nat) (input : Nat → Row) (m : Nat) :
    (List.ofFn (fun i : Fin (m + 1) => stepMat w (input i.val))).prod =
      (List.ofFn (fun i : Fin m => stepMat w (input i.val))).prod * stepMat w (input m) := by
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_cons, List.prod_nil, mul_one]
  rfl

private theorem list_ofFn_add_prod {α : Type*} [Monoid α] (a b : Nat) (f : Fin (a + b) → α) :
    (List.ofFn f).prod =
      (List.ofFn (fun i : Fin a => f ⟨i.val, by omega⟩)).prod *
      (List.ofFn (fun j : Fin b => f ⟨a + j.val, by omega⟩)).prod := by
  rw [← List.prod_append]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn]
    split_ifs with hlt
    · simp
    · congr 1
      apply Fin.ext
      dsimp only
      omega


private theorem path_count {s : ℕ} (n : ℕ) (F : Fin n → (Fin s → Bool) → Bool → Bool)
    (p q : Fin s → Bool) :
    (List.ofFn (fun i => Mat F i)).prod p q =
      (Finset.univ.filter (fun x : Fin (n + s) → Bool =>
        (∀ j : Fin s, x ⟨j.val, by omega⟩ = p j ∧ x ⟨n + j.val, by omega⟩ = q j) ∧
        ∀ i : Fin n, F i (fun j : Fin s => x ⟨i.val + j.val, by omega⟩)
          (x ⟨i.val + s, by omega⟩) = true)).card := by
  rw [prod_apply]
  refine Finset.card_bij'
    (fun (b : Fin n → Bool) _ => fun m : Fin (n + s) => yfun p (bitsOf n b) m.val)
    (fun (x : Fin (n + s) → Bool) _ => fun k : Fin n => x ⟨k.val + s, by omega⟩) ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    obtain ⟨hq, hall⟩ := (good_iff n F p q b).1 hb
    refine ⟨fun j => ⟨?_, ?_⟩, fun i => ?_⟩
    · simp [yfun, j.isLt]
    · rw [← stSeq_eq_yfun (bitsOf n b) p n j.val j.isLt, hq]
    · have h := hall i.val i.isLt
      have e1 : (fun j : Fin s => yfun p (bitsOf n b) (i.val + j.val)) =
          stSeq (bitsOf n b) p i.val := by
        funext j
        exact (stSeq_eq_yfun (bitsOf n b) p i.val j.val j.isLt).symm
      have e2 : yfun p (bitsOf n b) (i.val + s) = bitsOf n b i.val := by
        unfold yfun
        rw [dif_neg (by omega), show i.val + s - s = i.val by omega]
      rw [e1, e2]
      exact h
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨hpq, hall⟩ := hx
    have hy : ∀ m (hm : m < n + s),
        yfun p (bitsOf n (fun k : Fin n => x ⟨k.val + s, by omega⟩)) m = x ⟨m, hm⟩ := by
      intro m hm
      unfold yfun
      by_cases h : m < s
      · rw [dif_pos h]
        exact ((hpq ⟨m, h⟩).1).symm
      · rw [dif_neg h]
        unfold bitsOf
        rw [dif_pos (by omega)]
        exact congrArg x (Fin.ext (Nat.sub_add_cancel (not_lt.mp h)))
    rw [good_iff]
    refine ⟨?_, ?_⟩
    · funext j
      rw [stSeq_eq_yfun _ p n j.val j.isLt, hy (n + j.val) (by omega)]
      exact (hpq j).2
    · intro k hk
      have h := hall ⟨k, hk⟩
      have e1 : stSeq (bitsOf n (fun k : Fin n => x ⟨k.val + s, by omega⟩)) p k =
          fun j : Fin s => x ⟨k + j.val, by omega⟩ := by
        funext j
        rw [stSeq_eq_yfun _ p k j.val j.isLt, hy (k + j.val) (by omega)]
      have e2 : bitsOf n (fun k : Fin n => x ⟨k.val + s, by omega⟩) k = x ⟨k + s, by omega⟩ := by
        unfold bitsOf
        rw [dif_pos hk]
      rw [e1, e2]
      exact h
  · intro b _
    funext k
    show yfun p (bitsOf n b) (k.val + s) = b k
    unfold yfun
    rw [dif_neg (by omega), show k.val + s - s = k.val by omega]
    unfold bitsOf
    rw [dif_pos k.isLt]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hpq, -⟩ := hx
    funext m
    show yfun p (bitsOf n (fun k : Fin n => x ⟨k.val + s, by omega⟩)) m.val = x m
    unfold yfun
    by_cases h : m.val < s
    · rw [dif_pos h]
      exact ((hpq ⟨m.val, h⟩).1).symm
    · rw [dif_neg h]
      unfold bitsOf
      rw [dif_pos (by omega)]
      exact congrArg x (Fin.ext (Nat.sub_add_cancel (not_lt.mp h)))

private def snocW {w : ℕ} (st : Fin w → Bool) (bit : Bool) : Fin (w + 1) → Bool :=
  fun o => if h : o.val < w then st ⟨o.val, h⟩ else bit

private theorem transfer_exists (d : ℕ) :
    ∃ F : Finset ((Fin d → Bool) × (Fin d → Bool)) → Fin (2 ^ (d + 1) - 1) →
        (Fin (d + 1) → Bool) → Bool → Bool,
      ∀ (allowed : Finset ((Fin d → Bool) × (Fin d → Bool))) (a b : Fin (d + 1) → Bool),
        (List.ofFn (fun i => Mat (F allowed) i)).prod a b =
          (if a = b then 1 else 0) +
          (if a 0 = false ∧ b 0 = true ∧
            ((fun j : Fin d => a j.succ), (fun j : Fin d => b j.succ)) ∈ allowed
           then 1 else 0) := by
  obtain ⟨base, port, -, -, hcount⟩ := PEqualNP.Outside.L_lib_388 d
  refine ⟨fun allowed i st bit =>
    base (i, snocW st bit) || decide (∃ e ∈ allowed, port e = (i, snocW st bit)), ?_⟩
  intro allowed a b
  rw [path_count, ← hcount allowed a b]
  have hsn : ∀ (x : Fin (2 ^ (d + 1) - 1 + (d + 1)) → Bool) (i : Fin (2 ^ (d + 1) - 1)),
      snocW (fun j : Fin (d + 1) => x ⟨i.val + j.val, by omega⟩) (x ⟨i.val + (d + 1), by omega⟩) =
        fun offset : Fin (d + 1 + 1) =>
          x (Fin.ofNat (2 ^ (d + 1) - 1 + d + 1) (i.val + offset.val)) := by
    intro x i
    funext o
    unfold snocW
    by_cases h : o.val < d + 1
    · rw [dif_pos h]
      refine congrArg x (Fin.ext ?_)
      show i.val + o.val = (i.val + o.val) % (2 ^ (d + 1) - 1 + d + 1)
      exact (Nat.mod_eq_of_lt (by omega)).symm
    · rw [dif_neg h]
      refine congrArg x (Fin.ext ?_)
      show i.val + (d + 1) = (i.val + o.val) % (2 ^ (d + 1) - 1 + d + 1)
      have ho : o.val = d + 1 := by omega
      rw [ho]
      exact (Nat.mod_eq_of_lt (by omega)).symm
  have h0 : ∀ (x : Fin (2 ^ (d + 1) - 1 + (d + 1)) → Bool) (j : Fin (d + 1)),
      x (Fin.ofNat (2 ^ (d + 1) - 1 + d + 1) j.val) = x ⟨j.val, by omega⟩ := by
    intro x j
    refine congrArg x (Fin.ext ?_)
    show j.val % (2 ^ (d + 1) - 1 + d + 1) = j.val
    exact Nat.mod_eq_of_lt (by omega)
  have h1 : ∀ (x : Fin (2 ^ (d + 1) - 1 + (d + 1)) → Bool) (j : Fin (d + 1)),
      x (Fin.ofNat (2 ^ (d + 1) - 1 + d + 1) (2 ^ (d + 1) - 1 + j.val)) =
        x ⟨2 ^ (d + 1) - 1 + j.val, by omega⟩ := by
    intro x j
    refine congrArg x (Fin.ext ?_)
    show (2 ^ (d + 1) - 1 + j.val) % (2 ^ (d + 1) - 1 + d + 1) = 2 ^ (d + 1) - 1 + j.val
    exact Nat.mod_eq_of_lt (by omega)
  refine Finset.card_bij' (fun x _ => x) (fun x _ => x) ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨hab, hall⟩ := hx
    refine ⟨fun j => ⟨?_, ?_⟩, fun i => ?_⟩
    · exact (h0 x j).trans (hab j).1
    · exact (h1 x j).trans (hab j).2
    · have h := hall i
      rw [hsn x i] at h
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | ⟨e, he, hpe⟩
      · exact Or.inl h
      · exact Or.inr (Finset.mem_image.mpr ⟨e, he, hpe⟩)
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨hab, hall⟩ := hx
    refine ⟨fun j => ⟨?_, ?_⟩, fun i => ?_⟩
    · exact (h0 x j).symm.trans (hab j).1
    · exact (h1 x j).symm.trans (hab j).2
    · have h := hall i
      rw [hsn x i]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      rcases h with h | h
      · exact Or.inl h
      · obtain ⟨e, he, hpe⟩ := Finset.mem_image.mp h
        exact Or.inr ⟨e, he, hpe⟩

private def detRun {s : ℕ} : (n : ℕ) → (Fin n → (Fin s → Bool) → Bool) →
    (Fin s → Bool) → (Fin s → Bool)
  | 0, _, p => p
  | n + 1, f, p => detRun n (fun i => f i.succ) (nx p (f 0 p))

private def detOK {s : ℕ} : (n : ℕ) → (Fin n → (Fin s → Bool) → Bool) →
    (Fin n → (Fin s → Bool) → Bool) → (Fin s → Bool) → Bool
  | 0, _, _, _ => true
  | n + 1, g, f, p => g 0 p && detOK n (fun i => g i.succ) (fun i => f i.succ) (nx p (f 0 p))

private theorem det_prod {s : ℕ} : ∀ (n : ℕ) (F : Fin n → (Fin s → Bool) → Bool → Bool)
    (g f : Fin n → (Fin s → Bool) → Bool),
    (∀ i st bit, F i st bit = (g i st && (bit == f i st))) →
    ∀ p q, (List.ofFn (fun i => Mat F i)).prod p q =
      if detOK n g f p = true ∧ detRun n f p = q then 1 else 0 := by
  intro n
  induction n with
  | zero =>
    intro F g f hF p q
    simp [detOK, detRun, Matrix.one_apply]
  | succ n ih =>
    intro F g f hF p q
    rw [List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    have hM : ∀ r, Mat F 0 p r = if g 0 p = true ∧ nx p (f 0 p) = r then 1 else 0 := by
      intro r
      show (Finset.univ.filter fun bit : Bool => F 0 p bit = true ∧ nx p bit = r).card = _
      rw [Finset.card_filter, Fintype.sum_bool]
      cases hg : g 0 p <;> cases hf : f 0 p <;> simp [hF, hg, hf]
    have hP : ∀ r, (List.ofFn fun i : Fin n => Mat F i.succ).prod r q =
        if detOK n (fun i => g i.succ) (fun i => f i.succ) r = true ∧
          detRun n (fun i => f i.succ) r = q then 1 else 0 :=
      fun r => ih (fun i => F i.succ) (fun i => g i.succ) (fun i => f i.succ)
        (fun i => hF i.succ) r q
    simp only [hM, hP]
    rw [Finset.sum_eq_single (nx p (f 0 p))]
    · cases hg : g 0 p <;> simp [detOK, detRun, hg]
    · intro r _ hr
      have hne : ¬ (g 0 p = true ∧ nx p (f 0 p) = r) := fun h => hr h.2.symm
      simp [hne]
    · intro h
      exact absurd (Finset.mem_univ _) h

private theorem detOK_true {s : ℕ} : ∀ (n : ℕ) (g f : Fin n → (Fin s → Bool) → Bool)
    (p : Fin s → Bool), (∀ i st, g i st = true) → detOK n g f p = true := by
  intro n
  induction n with
  | zero => intro g f p _; rfl
  | succ n ih =>
    intro g f p hg
    show (g 0 p && detOK n (fun i => g i.succ) (fun i => f i.succ) (nx p (f 0 p))) = true
    rw [hg 0 p, ih _ _ _ (fun i st => hg i.succ st)]
    rfl

private theorem detRun_eq_foldl {s : ℕ} : ∀ (n : ℕ) (f : Fin n → (Fin s → Bool) → Bool)
    (p : Fin s → Bool),
    detRun n f p = (List.finRange n).foldl (fun st i => nx st (f i st)) p := by
  intro n
  induction n with
  | zero => intro f p; rfl
  | succ n ih =>
    intro f p
    rw [List.finRange_succ, List.foldl_cons, List.foldl_map]
    exact ih (fun i => f i.succ) (nx p (f 0 p))

private theorem nx_eq_snoc {d : ℕ} (s : Fin (d + 1) → Bool) (b : Bool) :
    nx s b = Fin.snoc (α := fun _ : Fin (d + 1) => Bool) (fun j : Fin d => s j.succ) b := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Fin.snoc_last]
    simp [nx]
  · rw [Fin.snoc_castSucc]
    have h : (Fin.castSucc i).val + 1 < d + 1 := by
      simp
    simp only [nx, dif_pos h]
    rfl

private theorem reset_exists (d m : ℕ) (hm : d + 1 ≤ m) :
    ∃ G : Fin m → (Fin (d + 1) → Bool) → Bool → Bool, ∀ p q : Fin (d + 1) → Bool,
      (List.ofFn (fun i => Mat G i)).prod p q =
        if p 0 = true ∧ (fun pos => xor (p pos) (decide (pos = 0))) = q then 1 else 0 := by
  obtain ⟨taps, bias, hrun⟩ :=
    (PEqualNP.Outside.L_lib_471 d m (fun pos => decide (pos = 0))).mpr (Or.inl hm)
  let fb : Fin m → (Fin (d + 1) → Bool) → Bool := fun row s =>
    (List.finRange d).foldl (fun acc bit => xor acc (taps row bit && s bit.succ))
      (xor (s 0) (bias row))
  let gd : Fin m → (Fin (d + 1) → Bool) → Bool := fun row s => decide (row.val ≠ 0) || s 0
  refine ⟨fun row st bit => gd row st && (bit == fb row st), ?_⟩
  intro p q
  rw [det_prod m _ gd fb (fun _ _ _ => rfl)]
  have hr : detRun m fb p = fun pos => xor (p pos) (decide (pos = 0)) := by
    rw [detRun_eq_foldl, ← hrun p]
    congr 1
    funext st row
    exact nx_eq_snoc st (fb row st)
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hok : detOK (m' + 1) gd fb p = p 0 := by
    show (gd 0 p && detOK m' (fun i => gd i.succ) (fun i => fb i.succ) (nx p (fb 0 p))) = p 0
    rw [detOK_true m' _ _ _ (fun i st => by simp [gd])]
    simp [gd]
  rw [hok, hr]

private def segProd (w : ℕ) (rows : Nat → Row) (start len : ℕ) :
    Matrix (Fin w → Bool) (Fin w → Bool) ℕ :=
  (List.ofFn (fun i : Fin len => stepMat w (rows (start + i.val)))).prod

private theorem segProd_add (w : ℕ) (rows : Nat → Row) (start a b : ℕ) :
    segProd w rows start (a + b) = segProd w rows start a * segProd w rows (start + a) b := by
  unfold segProd
  rw [list_ofFn_add_prod a b]
  simp only [Nat.add_assoc]

private theorem segProd_eq (w : ℕ) (rows : Nat → Row) (start len : ℕ)
    (F : Fin len → (Fin w → Bool) → Bool → Bool)
    (h : ∀ i : Fin len, rows (start + i.val) = rowOfTest (F i)) :
    segProd w rows start len = (List.ofFn (fun i => Mat F i)).prod := by
  unfold segProd
  congr 2
  funext i
  rw [h i, stepMat_rowOfTest]
  rfl

private def segRow {w : ℕ} (L m : ℕ) (F : Fin L → (Fin w → Bool) → Bool → Bool)
    (G : Fin m → (Fin w → Bool) → Bool → Bool) (site : ℕ) : Row :=
  if h : site < L then rowOfTest (F ⟨site, h⟩)
  else if h2 : site - L < m then rowOfTest (G ⟨site - L, h2⟩) else fun _ => false

private theorem half_prod {w : ℕ} (L m : ℕ) (F : Fin L → (Fin w → Bool) → Bool → Bool)
    (G : Fin m → (Fin w → Bool) → Bool → Bool) (rows : Nat → Row) (start : ℕ)
    (h : ∀ i, i < L + m → rows (start + i) = segRow L m F G i) :
    segProd w rows start (L + m) =
      (List.ofFn (fun i => Mat F i)).prod * (List.ofFn (fun i => Mat G i)).prod := by
  rw [segProd_add, segProd_eq w rows start L F ?_, segProd_eq w rows (start + L) m G ?_]
  · intro i
    rw [Nat.add_assoc, h (L + i.val) (by omega)]
    unfold segRow
    rw [dif_neg (by omega), dif_pos (by omega : L + i.val - L < m)]
    congr 2
    apply Fin.ext
    show L + i.val - L = i.val
    omega
  · intro i
    rw [h i.val (by omega)]
    unfold segRow
    rw [dif_pos i.isLt]

private def flipTag {d : ℕ} (q : Fin (d + 1) → Bool) : Fin (d + 1) → Bool :=
  fun pos => xor (q pos) (decide (pos = 0))

private theorem flipTag_flipTag {d : ℕ} (q : Fin (d + 1) → Bool) : flipTag (flipTag q) = q := by
  funext pos
  unfold flipTag
  cases q pos <;> cases decide (pos = 0) <;> rfl

private theorem flipTag_zero {d : ℕ} (q : Fin (d + 1) → Bool) : flipTag q 0 = !q 0 := by
  unfold flipTag
  cases q 0 <;> simp

private theorem flipTag_succ {d : ℕ} (q : Fin (d + 1) → Bool) (j : Fin d) :
    flipTag q j.succ = q j.succ := by
  unfold flipTag
  have h : decide (j.succ = 0) = false := by
    simp [Fin.succ_ne_zero]
  rw [h]
  cases q j.succ <;> rfl

private theorem cons_false_tail {d : ℕ} (p : Fin (d + 1) → Bool) (hp : p 0 = false) :
    (Fin.cons false (fun j : Fin d => p j.succ) : Fin (d + 1) → Bool) = p := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [Fin.cons_zero, hp]
  · rw [Fin.cons_succ]

private theorem trace_mul_sum {α : Type*} [Fintype α] (M N : Matrix α α ℕ) :
    Matrix.trace (M * N) = ∑ p, ∑ q, M p q * N q p := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

private theorem gadget_core (d L pad : ℕ)
    (FT : Finset ((Fin d → Bool) × (Fin d → Bool)) → Fin L →
      (Fin (d + 1) → Bool) → Bool → Bool)
    (hFT : ∀ (allowed : Finset ((Fin d → Bool) × (Fin d → Bool))) (a b : Fin (d + 1) → Bool),
      (List.ofFn (fun i => Mat (FT allowed) i)).prod a b =
        (if a = b then 1 else 0) +
        (if a 0 = false ∧ b 0 = true ∧
          ((fun j : Fin d => a j.succ), (fun j : Fin d => b j.succ)) ∈ allowed
         then 1 else 0))
    (G1 : Fin (d + 1) → (Fin (d + 1) → Bool) → Bool → Bool)
    (hG1 : ∀ p q : Fin (d + 1) → Bool, (List.ofFn (fun i => Mat G1 i)).prod p q =
      if p 0 = true ∧ flipTag p = q then 1 else 0)
    (G2 : Fin (d + 1 + pad) → (Fin (d + 1) → Bool) → Bool → Bool)
    (hG2 : ∀ p q : Fin (d + 1) → Bool, (List.ofFn (fun i => Mat G2 i)).prod p q =
      if p 0 = true ∧ flipTag p = q then 1 else 0)
    (A B : Finset ((Fin d → Bool) × (Fin d → Bool))) :
    totalCount (d + 1) ((L + (d + 1)) + (L + (d + 1 + pad))) (fun site =>
      if site < L + (d + 1) then segRow L (d + 1) (FT A) G1 site
      else segRow L (d + 1 + pad) (FT (B.image Prod.swap)) G2 (site - (L + (d + 1)))) =
        (A ∩ B).card := by
  let rows : Nat → Row := fun site =>
    if site < L + (d + 1) then segRow L (d + 1) (FT A) G1 site
    else segRow L (d + 1 + pad) (FT (B.image Prod.swap)) G2 (site - (L + (d + 1)))
  show totalCount (d + 1) ((L + (d + 1)) + (L + (d + 1 + pad))) rows = (A ∩ B).card
  rw [totalCount_eq_trace _ _ (by omega) rows]
  have hseg : ∀ (N : ℕ),
      (List.ofFn (fun i : Fin N => stepMat (d + 1) (rows i.val))).prod =
        segProd (d + 1) rows 0 N := by
    intro N
    unfold segProd
    simp only [Nat.zero_add]
  rw [hseg, segProd_add,
    half_prod L (d + 1) (FT A) G1 rows 0 ?_,
    half_prod L (d + 1 + pad) (FT (B.image Prod.swap)) G2 rows (0 + (L + (d + 1))) ?_]
  · have hN : ∀ (X : Finset ((Fin d → Bool) × (Fin d → Bool)))
        (G : Matrix (Fin (d + 1) → Bool) (Fin (d + 1) → Bool) ℕ),
        (∀ p q : Fin (d + 1) → Bool, G p q = if p 0 = true ∧ flipTag p = q then 1 else 0) →
        ∀ p q : Fin (d + 1) → Bool,
        ((List.ofFn (fun i => Mat (FT X) i)).prod * G) p q =
          if q 0 = false then
            (if p = flipTag q then 1 else 0) +
            (if p 0 = false ∧ ((fun j : Fin d => p j.succ), (fun j : Fin d => q j.succ)) ∈ X
              then 1 else 0)
          else 0 := by
      intro X G hG p q
      rw [Matrix.mul_apply, Finset.sum_eq_single (flipTag q)]
      · rw [hFT, hG, flipTag_flipTag, flipTag_zero]
        have htl : (fun j : Fin d => flipTag q j.succ) = fun j : Fin d => q j.succ :=
          funext (fun j => flipTag_succ q j)
        rw [htl]
        cases hq : q 0 <;> simp
      · intro s _ hs
        rw [hG]
        have hne : ¬ (s 0 = true ∧ flipTag s = q) := by
          intro h
          apply hs
          rw [← h.2, flipTag_flipTag]
        simp [hne]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hT : ∀ p q : Fin (d + 1) → Bool,
        ((List.ofFn (fun i => Mat (FT A) i)).prod * (List.ofFn (fun i => Mat G1 i)).prod) p q *
        ((List.ofFn (fun i => Mat (FT (B.image Prod.swap)) i)).prod *
          (List.ofFn (fun i => Mat G2 i)).prod) q p =
        if (p 0 = false ∧ q 0 = false) ∧
          ((fun j : Fin d => p j.succ), (fun j : Fin d => q j.succ)) ∈ A ∩ B then 1 else 0 := by
      intro p q
      rw [hN A _ hG1 p q, hN (B.image Prod.swap) _ hG2 q p]
      have hsw : ((fun j : Fin d => q j.succ), (fun j : Fin d => p j.succ)) ∈ B.image Prod.swap ↔
          ((fun j : Fin d => p j.succ), (fun j : Fin d => q j.succ)) ∈ B := by
        rw [Finset.mem_image]
        constructor
        · rintro ⟨e, he, hsw⟩
          have : e = ((fun j : Fin d => p j.succ), (fun j : Fin d => q j.succ)) := by
            rw [← Prod.swap_swap e, hsw]
            rfl
          rw [← this]
          exact he
        · intro h
          exact ⟨_, h, rfl⟩
      cases hp : p 0
      · cases hq : q 0
        · have h1 : p ≠ flipTag q := by
            intro h
            have := congrFun h 0
            rw [flipTag_zero, hp, hq] at this
            exact Bool.false_ne_true this
          have h2 : q ≠ flipTag p := by
            intro h
            have := congrFun h 0
            rw [flipTag_zero, hp, hq] at this
            exact Bool.false_ne_true this
          simp only [h1, h2, hsw, Finset.mem_inter, if_true, if_false, true_and, zero_add]
          by_cases hA : ((fun j : Fin d => p j.succ), (fun j : Fin d => q j.succ)) ∈ A <;>
            by_cases hB : ((fun j : Fin d => p j.succ), (fun j : Fin d => q j.succ)) ∈ B <;>
            simp [hA, hB]
        · simp
      · simp
    rw [trace_mul_sum]
    simp only [hT]
    rw [← Fintype.sum_prod_type', ← Finset.card_filter]
    refine Finset.card_bij'
      (fun (pq : (Fin (d + 1) → Bool) × (Fin (d + 1) → Bool)) _ =>
        ((fun j : Fin d => pq.1 j.succ), (fun j : Fin d => pq.2 j.succ)))
      (fun (e : (Fin d → Bool) × (Fin d → Bool)) _ =>
        ((Fin.cons false e.1 : Fin (d + 1) → Bool), (Fin.cons false e.2 : Fin (d + 1) → Bool)))
      ?_ ?_ ?_ ?_
    · intro pq hpq
      exact (Finset.mem_filter.mp hpq).2.2
    · intro e he
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨?_, ?_⟩, ?_⟩
      · show (Fin.cons false e.1 : Fin (d + 1) → Bool) 0 = false
        rfl
      · show (Fin.cons false e.2 : Fin (d + 1) → Bool) 0 = false
        rfl
      · simpa [Fin.cons_succ] using he
    · intro pq hpq
      obtain ⟨hp, hq⟩ := (Finset.mem_filter.mp hpq).2.1
      exact Prod.ext (cons_false_tail pq.1 hp) (cons_false_tail pq.2 hq)
    · intro e _
      simp [Fin.cons_succ]
  · intro i hi
    show (if 0 + (L + (d + 1)) + i < L + (d + 1) then _ else _) = _
    rw [if_neg (by omega)]
    congr 1
    omega
  · intro i hi
    show (if 0 + i < L + (d + 1) then _ else _) = _
    rw [if_pos (by omega), Nat.zero_add]

private theorem exists_ip_gadget (d n : Nat) (hn : 2 * ((2 ^ (d + 1) - 1) + (d + 1)) ≤ n) :
    ∃ (aliceRows bobRows : Finset ((Fin d → Bool) × (Fin d → Bool)) → Nat → Row),
      ∀ (A B : Finset ((Fin d → Bool) × (Fin d → Bool))),
        totalCount (d + 1) n (fun site =>
          if site < (2 ^ (d + 1) - 1) + (d + 1) then aliceRows A site
          else bobRows B (site - ((2 ^ (d + 1) - 1) + (d + 1)))) = (A ∩ B).card := by
  obtain ⟨FT, hFT⟩ := transfer_exists d
  obtain ⟨pad, rfl⟩ : ∃ pad, n =
      ((2 ^ (d + 1) - 1) + (d + 1)) + ((2 ^ (d + 1) - 1) + (d + 1 + pad)) :=
    ⟨n - 2 * ((2 ^ (d + 1) - 1) + (d + 1)), by omega⟩
  obtain ⟨G1, hG1⟩ := reset_exists d (d + 1) le_rfl
  obtain ⟨G2, hG2⟩ := reset_exists d (d + 1 + pad) (by omega)
  refine ⟨fun A => segRow _ (d + 1) (FT A) G1,
    fun B => segRow _ (d + 1 + pad) (FT (B.image Prod.swap)) G2, ?_⟩
  intro A B
  exact gadget_core d _ pad FT hFT G1 hG1 G2 hG2 A B

private def afterBobAux {X : Type*} {S : Nat} (start : Fin S)
    (runAlice runBob : Nat → Fin S → X → Fin S) : Nat → X → X → Fin S
  | 0, _, _ => start
  | r + 1, A, B => runBob r (runAlice r (afterBobAux start runAlice runBob r A B) A) B

private theorem rectangle_partition {X : Type} [Fintype X] [DecidableEq X]
    {S R a b p n H w : Nat}
    (hp : 0 < p) (hR : 0 < R) (hHn : H ≤ n)
    (aliceRows bobRows : X → Nat → Row) (tgt : X → X → Bool)
    (hgadget : ∀ (A B : X),
      (totalCount w n (fun site =>
        if site < H then aliceRows A site else bobRows B (site - H))).testBit 0 = tgt A B)
    (init : Fin R → Fin S) (update : Fin R → Nat → Nat → Fin S → Row → Fin S)
    (output : Fin R → Fin S → Bool)
    (hok : ∀ input : Nat → Row,
      a * R ≤ b * ((List.finRange R).filter (fun coin =>
        output coin (runAlg p n S (init coin) (update coin) input) ==
          (totalCount w n input).testBit 0)).length) :
    0 < S ∧
    ∃ (T : Fin (S ^ (2 * p - 1)) → Finset X × Finset X × (X → Bool)),
      (∑ τ : Fin (S ^ (2 * p - 1)), (T τ).1.card * (T τ).2.1.card = Fintype.card X ^ 2) ∧
      (a * Fintype.card X ^ 2 ≤ b * ∑ τ : Fin (S ^ (2 * p - 1)),
        (((T τ).1 ×ˢ (T τ).2.1).filter (fun AB => tgt AB.1 AB.2 = (T τ).2.2 AB.2)).card) := by
  have hS_pos : 0 < S := Fin.pos (init ⟨0, hR⟩)
  let glue : X → X → Nat → Row := fun A B site =>
    if site < H then aliceRows A site else bobRows B (site - H)
  let hit : Fin R → X × X → Bool := fun coin AB =>
    output coin (runAlg p n S (init coin) (update coin) (glue AB.1 AB.2)) == tgt AB.1 AB.2
  have hsum_all : a * R * Fintype.card (X × X) ≤
      b * ∑ coin : Fin R,
        ((Finset.univ : Finset (X × X)).filter (fun AB => hit coin AB = true)).card := by
    have h1 : ∀ AB : X × X,
        a * R ≤ b * ((Finset.univ : Finset (Fin R)).filter
          (fun coin => hit coin AB = true)).card := by
      intro AB
      have h := hok (glue AB.1 AB.2)
      rw [finRange_filter_length_eq_finset_card, hgadget AB.1 AB.2] at h
      exact h
    have h2 := Finset.sum_le_sum (s := (Finset.univ : Finset (X × X))) (fun AB _ => h1 AB)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm (Fintype.card (X × X)),
      ← Finset.mul_sum] at h2
    have hswap : (∑ AB : X × X,
        ((Finset.univ : Finset (Fin R)).filter (fun coin => hit coin AB = true)).card) =
        ∑ coin : Fin R,
          ((Finset.univ : Finset (X × X)).filter (fun AB => hit coin AB = true)).card := by
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    rw [hswap] at h2
    exact h2
  have hex_coin : ∃ coin0 : Fin R,
      a * Fintype.card (X × X) ≤
        b * ((Finset.univ : Finset (X × X)).filter (fun AB => hit coin0 AB = true)).card := by
    by_contra hnone
    push Not at hnone
    have hlt : b * ∑ coin : Fin R,
        ((Finset.univ : Finset (X × X)).filter (fun AB => hit coin AB = true)).card <
        ∑ _coin : Fin R, (a * Fintype.card (X × X)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_lt_sum_of_nonempty
        ⟨⟨0, hR⟩, Finset.mem_univ _⟩ (fun coin _ => hnone coin)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt
    have hmul : R * (a * Fintype.card (X × X)) = a * R * Fintype.card (X × X) := by ring
    omega
  obtain ⟨coin0, hcoin0⟩ := hex_coin
  have hcardXX : Fintype.card (X × X) = Fintype.card X ^ 2 := by
    rw [Fintype.card_prod, sq]
  rw [hcardXX] at hcoin0
  let start := init coin0
  let step := update coin0
  let out := output coin0
  let runAlice : Nat → Fin S → X → Fin S := fun passId st A =>
    (List.range H).foldl (fun s i => step passId i s (aliceRows A i)) st
  let runBob : Nat → Fin S → X → Fin S := fun passId st B =>
    (List.range (n - H)).foldl (fun s j => step passId (H + j) s (bobRows B j)) st
  have honePass : ∀ passId st A B,
      (List.range n).foldl (fun s siteId => step passId siteId s (glue A B siteId)) st =
        runBob passId (runAlice passId st A) B := by
    intro passId st A B
    have hrange : List.range n = List.range H ++ (List.range (n - H)).map (H + ·) := by
      have h1 : n = H + (n - H) := by omega
      conv_lhs => rw [h1, List.range_add]
    rw [hrange, List.foldl_append, List.foldl_map]
    have hA : (List.range H).foldl (fun s siteId => step passId siteId s (glue A B siteId)) st =
        runAlice passId st A := by
      dsimp only [runAlice]
      have hgen : ∀ (l : List Nat) (st0 : Fin S), (∀ x ∈ l, x < H) →
          l.foldl (fun s siteId => step passId siteId s (glue A B siteId)) st0 =
          l.foldl (fun s siteId => step passId siteId s (aliceRows A siteId)) st0 := by
        intro l
        induction l with
        | nil => intro _ _; rfl
        | cons x xs ih =>
          intro st0 hl
          simp only [List.foldl_cons]
          have hx : x < H := hl x List.mem_cons_self
          have hgx : glue A B x = aliceRows A x := by simp [glue, hx]
          rw [hgx]
          exact ih _ (fun y hy => hl y (List.mem_cons_of_mem x hy))
      exact hgen (List.range H) st (fun x hx => List.mem_range.mp hx)
    rw [hA]
    dsimp only [runBob]
    have hB : ∀ (l : List Nat) (st0 : Fin S),
        l.foldl (fun s j => step passId (H + j) s (glue A B (H + j))) st0 =
        l.foldl (fun s j => step passId (H + j) s (bobRows B j)) st0 := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons x xs ih =>
        intro st0
        simp only [List.foldl_cons]
        have hgx : glue A B (H + x) = bobRows B x := by
          have : ¬ (H + x < H) := by omega
          simp [glue, this]
        rw [hgx]
        exact ih _
    exact hB (List.range (n - H)) _
  let afterBob : Nat → X → X → Fin S := afterBobAux start runAlice runBob
  have hrun_eq : ∀ r A B,
      (List.range r).foldl (fun prev passId =>
        (List.range n).foldl
          (fun state siteId => step passId siteId state (glue A B siteId)) prev) start =
      afterBob r A B := by
    intro r A B
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih, honePass]
      rfl
  let Trans := (Fin (p - 1) → Fin S) × (Fin p → Fin S)
  have hcardTrans : Fintype.card Trans = S ^ (2 * p - 1) := by
    simp only [Trans, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    rw [← pow_add]
    congr 1
    omega
  let eT : Trans ≃ Fin (S ^ (2 * p - 1)) := Fintype.equivFinOfCardEq hcardTrans
  let trOf : X → X → Trans := fun A B =>
    (fun r : Fin (p - 1) => afterBob (r.val + 1) A B,
     fun r : Fin p => runAlice r.val (afterBob r.val A B) A)
  let Uset : Trans → Finset X := fun ts =>
    Finset.univ.filter (fun A =>
      ∀ r : Fin p,
        runAlice r.val (if h : r.val = 0 then start else ts.1 ⟨r.val - 1, by omega⟩) A = ts.2 r)
  let Vset : Trans → Finset X := fun ts =>
    Finset.univ.filter (fun B =>
      ∀ r : Fin (p - 1), runBob r.val (ts.2 ⟨r.val, by omega⟩) B = ts.1 r)
  let gFun : Trans → X → Bool := fun ts B => out (runBob (p - 1) (ts.2 ⟨p - 1, by omega⟩) B)
  have htr_iff : ∀ ts A B, trOf A B = ts ↔ A ∈ Uset ts ∧ B ∈ Vset ts := by
    intro ts A B
    constructor
    · intro h
      have h1 : ∀ r : Fin (p - 1), afterBob (r.val + 1) A B = ts.1 r :=
        fun r => congrFun (congrArg Prod.fst h) r
      have h2 : ∀ r : Fin p, runAlice r.val (afterBob r.val A B) A = ts.2 r :=
        fun r => congrFun (congrArg Prod.snd h) r
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      · intro r
        by_cases hr0 : r.val = 0
        · simp only [hr0, ↓reduceDIte]
          have := h2 r
          rw [hr0] at this
          exact this
        · simp only [hr0, ↓reduceDIte]
          have hsub : r.val - 1 + 1 = r.val := by omega
          have hprev := h1 ⟨r.val - 1, by omega⟩
          rw [← hprev, hsub]
          exact h2 r
      · intro r
        have hprev := h2 ⟨r.val, by omega⟩
        rw [← hprev]
        exact h1 r
    · intro ⟨hA, hB⟩
      have hA' := (Finset.mem_filter.mp hA).2
      have hB' := (Finset.mem_filter.mp hB).2
      have hrec : ∀ r, ∀ hr : r < p,
          afterBob r A B = (if h : r = 0 then start else ts.1 ⟨r - 1, by omega⟩) ∧
          runAlice r (afterBob r A B) A = ts.2 ⟨r, hr⟩ := by
        intro r
        induction r with
        | zero =>
          intro _
          refine ⟨by simp [afterBob, afterBobAux], ?_⟩
          have h := hA' ⟨0, hp⟩
          simpa [afterBob, afterBobAux] using h
        | succ r ih =>
          intro hr
          obtain ⟨_, ih2⟩ := ih (by omega)
          have hbob : afterBob (r + 1) A B = ts.1 ⟨r, by omega⟩ := by
            change runBob r (runAlice r (afterBob r A B) A) B = ts.1 ⟨r, by omega⟩
            rw [ih2]
            exact hB' ⟨r, by omega⟩
          refine ⟨by simp [hbob], ?_⟩
          have h := hA' ⟨r + 1, hr⟩
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte,
            Nat.add_sub_cancel] at h
          rw [hbob]
          exact h
      apply Prod.ext
      · funext r
        obtain ⟨_, ih2⟩ := hrec r.val (by omega)
        change runBob r.val (runAlice r.val (afterBob r.val A B) A) B = ts.1 r
        rw [ih2]
        exact hB' r
      · funext r
        exact (hrec r.val r.isLt).2
  have hout_eq : ∀ ts A B, trOf A B = ts →
      out (runAlg p n S start step (glue A B)) = gFun ts B := by
    intro ts A B h
    dsimp only [runAlg, gFun]
    rw [hrun_eq p A B]
    have hp1 : p = (p - 1) + 1 := by omega
    conv_lhs => rw [hp1]
    change out (runBob (p - 1) (runAlice (p - 1) (afterBob (p - 1) A B) A) B) =
      out (runBob (p - 1) (ts.2 ⟨p - 1, by omega⟩) B)
    have h2 := congrFun (congrArg Prod.snd h) ⟨p - 1, by omega⟩
    dsimp only [trOf] at h2
    rw [h2]
  refine ⟨hS_pos, fun τ => (Uset (eT.symm τ), Vset (eT.symm τ), gFun (eT.symm τ)), ?_, ?_⟩
  · rw [Equiv.sum_comp eT.symm (fun ts => (Uset ts).card * (Vset ts).card)]
    have hpart := Finset.card_eq_sum_card_fiberwise
      (f := fun AB : X × X => trOf AB.1 AB.2)
      (s := (Finset.univ : Finset (X × X)))
      (t := (Finset.univ : Finset Trans))
      (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ, hcardXX] at hpart
    rw [hpart]
    apply Finset.sum_congr rfl
    intro ts _
    rw [← Finset.card_product]
    congr 1
    ext ⟨A, B⟩
    simp [Finset.mem_product, htr_iff]
  · rw [Equiv.sum_comp eT.symm (fun ts =>
      (((Uset ts ×ˢ Vset ts).filter (fun AB => tgt AB.1 AB.2 = gFun ts AB.2)).card))]
    refine le_trans hcoin0 (Nat.mul_le_mul_left b ?_)
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := fun AB : X × X => trOf AB.1 AB.2)
      (s := (Finset.univ : Finset (X × X)).filter (fun AB => hit coin0 AB = true))
      (t := (Finset.univ : Finset Trans))
      (fun _ _ => Finset.mem_univ _)
    rw [hfib]
    apply Finset.sum_le_sum
    intro ts _
    apply Finset.card_le_card
    intro ⟨A, B⟩ hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hit, beq_iff_eq] at hmem
    obtain ⟨h1, h2⟩ := hmem
    have hrect := (htr_iff ts A B).mp h2
    have ho := hout_eq ts A B h2
    simp only [Finset.mem_filter, Finset.mem_product]
    refine ⟨hrect, ?_⟩
    rw [← ho]
    exact h1.symm

private def hd {α : Type} [DecidableEq α] (A B : Finset α) : ℤ := (-1) ^ (A ∩ B).card

private theorem hd_sq {α : Type} [DecidableEq α] (A B : Finset α) : hd A B * hd A B = 1 := by
  unfold hd
  rw [← pow_add, ← two_mul, pow_mul]
  simp

private theorem hd_flip {α : Type} [DecidableEq α] (A B : Finset α) (z : α) :
    hd (symmDiff A {z}) B = if z ∈ B then - hd A B else hd A B := by
  unfold hd
  by_cases hzB : z ∈ B
  · rw [if_pos hzB]
    by_cases hzA : z ∈ A
    · have hmem : z ∈ A ∩ B := Finset.mem_inter.mpr ⟨hzA, hzB⟩
      have hset : symmDiff A {z} ∩ B = (A ∩ B).erase z := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
        by_cases hx : x = z
        · subst hx
          simp [hzA]
        · simp [hx]
      have hpos : 0 < (A ∩ B).card := Finset.card_pos.mpr ⟨z, hmem⟩
      rw [hset, Finset.card_erase_of_mem hmem]
      obtain ⟨c, hc⟩ : ∃ c, (A ∩ B).card = c + 1 := ⟨(A ∩ B).card - 1, by omega⟩
      rw [hc, Nat.add_sub_cancel, pow_succ]
      ring
    · have hnmem : z ∉ A ∩ B := fun h => hzA (Finset.mem_inter.mp h).1
      have hset : symmDiff A {z} ∩ B = insert z (A ∩ B) := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
        by_cases hx : x = z
        · subst hx
          simp [hzA, hzB]
        · simp [hx]
      rw [hset, Finset.card_insert_of_notMem hnmem, pow_succ]
      ring
  · rw [if_neg hzB]
    have hset : symmDiff A {z} ∩ B = A ∩ B := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.mem_singleton]
      by_cases hx : x = z
      · subst hx
        simp [hzB]
      · simp [hx]
    rw [hset]

private theorem hd_orth {α : Type} [Fintype α] [DecidableEq α] (B B' : Finset α) :
    ∑ A : Finset α, hd A B * hd A B' = if B = B' then (2 : ℤ) ^ Fintype.card α else 0 := by
  by_cases h : B = B'
  · subst h
    rw [if_pos rfl]
    simp only [hd_sq]
    simp [Fintype.card_finset]
  · rw [if_neg h]
    obtain ⟨z, hz⟩ : ∃ z, ¬ (z ∈ B ↔ z ∈ B') := by
      by_contra hc
      push Not at hc
      exact h (Finset.ext hc)
    let e : Equiv.Perm (Finset α) :=
      Function.Involutive.toPerm (fun A => symmDiff A {z})
        (fun A => symmDiff_symmDiff_cancel_right _ _)
    have hneg : ∀ A, hd (e A) B * hd (e A) B' = - (hd A B * hd A B') := by
      intro A
      show hd (symmDiff A {z}) B * hd (symmDiff A {z}) B' = _
      rw [hd_flip, hd_flip]
      by_cases h1 : z ∈ B <;> by_cases h2 : z ∈ B'
      · exact absurd (iff_of_true h1 h2) hz
      · simp [h1, h2]
      · simp [h1, h2]
      · exact absurd (iff_of_false h1 h2) hz
    have hsum := Equiv.sum_comp e (fun A => hd A B * hd A B')
    simp only [hneg, Finset.sum_neg_distrib] at hsum
    linarith

private theorem rect_disc {α : Type} [Fintype α] [DecidableEq α]
    (U V : Finset (Finset α)) (σ : Finset α → ℤ) (hσ : ∀ B, σ B * σ B = 1) :
    (∑ A ∈ U, ∑ B ∈ V, σ B * hd A B) ^ 2 ≤
      (U.card : ℤ) * ((V.card : ℤ) * 2 ^ Fintype.card α) := by
  have h1 : (∑ A ∈ U, ∑ B ∈ V, σ B * hd A B) ^ 2 ≤
      (U.card : ℤ) * ∑ A ∈ U, (∑ B ∈ V, σ B * hd A B) ^ 2 := sq_sum_le_card_mul_sum_sq
  have h2 : ∑ A ∈ U, (∑ B ∈ V, σ B * hd A B) ^ 2 ≤
      ∑ A : Finset α, (∑ B ∈ V, σ B * hd A B) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U) (fun _ _ _ => sq_nonneg _)
  have h3 : ∑ A : Finset α, (∑ B ∈ V, σ B * hd A B) ^ 2 =
      (V.card : ℤ) * 2 ^ Fintype.card α := by
    calc ∑ A : Finset α, (∑ B ∈ V, σ B * hd A B) ^ 2
        = ∑ A : Finset α, ∑ B ∈ V, ∑ B' ∈ V, (σ B * hd A B) * (σ B' * hd A B') := by
          refine Finset.sum_congr rfl (fun A _ => ?_)
          rw [sq, Finset.sum_mul_sum]
      _ = ∑ B ∈ V, ∑ B' ∈ V, ∑ A : Finset α, (σ B * hd A B) * (σ B' * hd A B') := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun B _ => ?_)
          rw [Finset.sum_comm]
      _ = ∑ B ∈ V, ∑ B' ∈ V, σ B * σ B' * (if B = B' then (2 : ℤ) ^ Fintype.card α else 0) := by
          refine Finset.sum_congr rfl (fun B _ => Finset.sum_congr rfl (fun B' _ => ?_))
          rw [← hd_orth B B', Finset.mul_sum]
          refine Finset.sum_congr rfl (fun A _ => ?_)
          ring
      _ = ∑ B ∈ V, (2 : ℤ) ^ Fintype.card α := by
          refine Finset.sum_congr rfl (fun B hB => ?_)
          rw [Finset.sum_eq_single B]
          · rw [if_pos rfl, hσ B, one_mul]
          · intro B' _ hne
            rw [if_neg (fun h => hne h.symm), mul_zero]
          · intro h
            exact absurd hB h
      _ = (V.card : ℤ) * 2 ^ Fintype.card α := by
          rw [Finset.sum_const, nsmul_eq_mul]
  calc (∑ A ∈ U, ∑ B ∈ V, σ B * hd A B) ^ 2
      ≤ (U.card : ℤ) * ∑ A ∈ U, (∑ B ∈ V, σ B * hd A B) ^ 2 := h1
    _ ≤ (U.card : ℤ) * ∑ A : Finset α, (∑ B ∈ V, σ B * hd A B) ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
    _ = (U.card : ℤ) * ((V.card : ℤ) * 2 ^ Fintype.card α) := by rw [h3]

private theorem rect_count {α : Type} [Fintype α] [DecidableEq α]
    (U V : Finset (Finset α)) (g : Finset α → Bool) :
    (2 * (((U ×ˢ V).filter (fun AB => (AB.1 ∩ AB.2).card.testBit 0 = g AB.2)).card : ℤ) -
      (U.card : ℤ) * (V.card : ℤ)) ^ 2 ≤
      (U.card : ℤ) * ((V.card : ℤ) * 2 ^ Fintype.card α) := by
  let σ : Finset α → ℤ := fun B => if g B = true then -1 else 1
  have hσ : ∀ B, σ B * σ B = 1 := by
    intro B
    show (if g B = true then (-1 : ℤ) else 1) * (if g B = true then (-1 : ℤ) else 1) = 1
    cases g B <;> simp
  have hterm : ∀ A B : Finset α, σ B * hd A B =
      2 * (if (A ∩ B).card.testBit 0 = g B then (1 : ℤ) else 0) - 1 := by
    intro A B
    show (if g B = true then (-1 : ℤ) else 1) * (-1) ^ (A ∩ B).card = _
    rw [Nat.testBit_zero]
    rcases Nat.even_or_odd (A ∩ B).card with he | ho
    · have hm : (A ∩ B).card % 2 = 0 := Nat.even_iff.mp he
      rw [he.neg_one_pow]
      cases g B <;> simp [hm]
    · have hm : (A ∩ B).card % 2 = 1 := Nat.odd_iff.mp ho
      rw [ho.neg_one_pow]
      cases g B <;> simp [hm]
  have hsum : ∑ A ∈ U, ∑ B ∈ V, σ B * hd A B =
      2 * (((U ×ˢ V).filter (fun AB => (AB.1 ∩ AB.2).card.testBit 0 = g AB.2)).card : ℤ) -
        (U.card : ℤ) * (V.card : ℤ) := by
    rw [← Finset.sum_product' U V (fun A B => σ B * hd A B)]
    simp only [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const,
      Finset.card_product]
    simp
  rw [← hsum]
  exact rect_disc U V σ hσ

private theorem final_bound {K N num den : ℕ} (hN : 0 < N)
    (c u v : Fin K → ℕ)
    (hpart : ∑ τ, u τ * v τ = N ^ 2)
    (hdisc : ∀ τ, (2 * (c τ : ℤ) - (u τ : ℤ) * (v τ : ℤ)) ^ 2 ≤ (u τ : ℤ) * ((v τ : ℤ) * N))
    (hadv : (den + num) * N ^ 2 ≤ 2 * den * ∑ τ, c τ) :
    num ^ 2 * N ≤ den ^ 2 * K := by
  let e : Fin K → ℤ := fun τ => 2 * (c τ : ℤ) - (u τ : ℤ) * (v τ : ℤ)
  have hpartZ : ∑ τ, (u τ : ℤ) * (v τ : ℤ) = (N : ℤ) ^ 2 := by
    exact_mod_cast hpart
  have hadvZ : ((den : ℤ) + num) * (N : ℤ) ^ 2 ≤ 2 * den * ∑ τ, (c τ : ℤ) := by
    exact_mod_cast hadv
  have hsumE : ∑ τ, e τ = 2 * ∑ τ, (c τ : ℤ) - (N : ℤ) ^ 2 := by
    show ∑ τ, (2 * (c τ : ℤ) - (u τ : ℤ) * (v τ : ℤ)) = _
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hpartZ]
  have h1 : (num : ℤ) * (N : ℤ) ^ 2 ≤ den * ∑ τ, e τ := by
    rw [hsumE]
    nlinarith
  have h2 : (∑ τ, e τ) ^ 2 ≤ (K : ℤ) * ∑ τ, e τ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin K))) (f := e)
    simpa using this
  have h3 : ∑ τ, e τ ^ 2 ≤ (N : ℤ) ^ 3 := by
    calc ∑ τ, e τ ^ 2 ≤ ∑ τ, (u τ : ℤ) * ((v τ : ℤ) * N) := Finset.sum_le_sum (fun τ _ => hdisc τ)
      _ = (∑ τ, (u τ : ℤ) * (v τ : ℤ)) * N := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun τ _ => ?_)
          ring
      _ = (N : ℤ) ^ 3 := by rw [hpartZ]; ring
  have hNZ : (0 : ℤ) < N := by exact_mod_cast hN
  have h4 : ((num : ℤ) * (N : ℤ) ^ 2) ^ 2 ≤ ((den : ℤ) * ∑ τ, e τ) ^ 2 := by
    apply pow_le_pow_left₀ _ h1
    positivity
  have h5 : ((den : ℤ) * ∑ τ, e τ) ^ 2 ≤ (den : ℤ) ^ 2 * ((K : ℤ) * (N : ℤ) ^ 3) := by
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact le_trans h2 (mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _))
  have h6 : ((num : ℤ) ^ 2 * N) * (N : ℤ) ^ 3 ≤ ((den : ℤ) ^ 2 * K) * (N : ℤ) ^ 3 := by
    calc ((num : ℤ) ^ 2 * N) * (N : ℤ) ^ 3 = ((num : ℤ) * (N : ℤ) ^ 2) ^ 2 := by ring
      _ ≤ (den : ℤ) ^ 2 * ((K : ℤ) * (N : ℤ) ^ 3) := le_trans h4 h5
      _ = ((den : ℤ) ^ 2 * K) * (N : ℤ) ^ 3 := by ring
  have h7 : (num : ℤ) ^ 2 * N ≤ (den : ℤ) ^ 2 * K :=
    le_of_mul_le_mul_right h6 (by positivity)
  exact_mod_cast h7

private theorem main_result (d n p : Nat) (hp : 0 < p)
    (hn : 2 * ((2 ^ (d + 1) - 1) + (d + 1)) ≤ n)
    (S R num den : Nat) (hR : 0 < R)
    (init : Fin R → Fin S) (update : Fin R → Nat → Nat → Fin S → Row → Fin S)
    (output : Fin R → Fin S → Bool)
    (hok : ∀ input : Nat → Row,
      (den + num) * R ≤ 2 * den * ((List.finRange R).filter (fun coin =>
        output coin (runAlg p n S (init coin) (update coin) input) ==
          (totalCount (d + 1) n input).testBit 0)).length) :
    num ^ 2 * 2 ^ (4 ^ d) ≤ den ^ 2 * S ^ (2 * p - 1) := by
  obtain ⟨aliceRows, bobRows, hgadget⟩ := exists_ip_gadget d n hn
  have hHn : (2 ^ (d + 1) - 1) + (d + 1) ≤ n := by omega
  obtain ⟨-, T, hpart, hadv⟩ :=
    rectangle_partition (a := den + num) (b := 2 * den) hp hR hHn aliceRows bobRows
      (fun A B => (A ∩ B).card.testBit 0) (fun A B => by rw [hgadget A B])
      init update output hok
  have hcard : Fintype.card (Finset ((Fin d → Bool) × (Fin d → Bool))) = 2 ^ (4 ^ d) := by
    rw [Fintype.card_finset, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, ← mul_pow]
    norm_num
  have hcard2 : Fintype.card ((Fin d → Bool) × (Fin d → Bool)) = 4 ^ d := by
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← mul_pow]
    norm_num
  rw [hcard] at hpart hadv
  refine final_bound (N := 2 ^ (4 ^ d)) (by positivity)
    (fun τ => (((T τ).1 ×ˢ (T τ).2.1).filter
      (fun AB => (AB.1 ∩ AB.2).card.testBit 0 = (T τ).2.2 AB.2)).card)
    (fun τ => (T τ).1.card) (fun τ => (T τ).2.1.card) hpart ?_ hadv
  intro τ
  have h := rect_count (T τ).1 (T τ).2.1 (T τ).2.2
  rw [hcard2] at h
  exact_mod_cast h

end PEqualNP.Outside.L_clb_088_aux

theorem PEqualNP.Outside.L_clb_088 : (∀ (d n p : Nat), 0 < p →
  let w := d+1
  2*((2^w-1)+w) ≤ n →
  let Row := Nat → Bool
  let parity := fun (rows : Nat → Row) =>
    ((List.range (2^n)).filter (fun word => (List.range n).all (fun site =>
      let pat := (List.range (w+1)).foldl (fun (acc bit : Nat) =>
        acc ||| ((word.testBit ((site+bit)%n)).toNat <<< bit)) 0
      rows site pat))).length.testBit 0
  let run := fun (S : Nat) (start : Fin S)
      (step : Nat → Nat → Fin S → Row → Fin S) (table : Nat → Row) =>
    (List.range p).foldl (fun prev passId =>
      (List.range n).foldl (fun state siteId => step passId siteId state (table siteId)) prev) start
  ∀ (S R num den : Nat), 0 < R → 0 < den → num ≤ den →
    ∀ (init : Fin R → Fin S) (update : Fin R → Nat → Nat → Fin S → Row → Fin S)
      (output : Fin R → Fin S → Bool),
      (∀ input : Nat → Row,
        (den+num)*R ≤ 2*den*((List.finRange R).filter (fun coin =>
          output coin (run S (init coin) (update coin) input) == parity input)).length) →
      num^2 * 2^(4^d) ≤ den^2 * S^(2*p-1)) := by
  intro d n p hp w hn Row parity run S R num den hR _ _ init update output hok
  exact PEqualNP.Outside.L_clb_088_aux.main_result d n p hp hn S R num den hR
    init update output hok
