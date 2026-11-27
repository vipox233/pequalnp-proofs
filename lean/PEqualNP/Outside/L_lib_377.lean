import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_377

/-- Window shift: drop the first coordinate and append the new bit. -/
def nx {s : ℕ} (state : Fin s → Bool) (b : Bool) : Fin s → Bool :=
  fun j => if h : j.val + 1 < s then state ⟨j.val + 1, h⟩ else b

/-- Window states along a bit stream. -/
def stSeq {s : ℕ} (beta : ℕ → Bool) (p : Fin s → Bool) : ℕ → (Fin s → Bool)
  | 0 => p
  | k + 1 => nx (stSeq beta p k) (beta k)

/-- Infinite word read off from an initial window and a bit stream. -/
def yfun {s : ℕ} (p : Fin s → Bool) (beta : ℕ → Bool) (m : ℕ) : Bool :=
  if h : m < s then p ⟨m, h⟩ else beta (m - s)

/-- Bit stream of a finite bit vector (zero beyond its length). -/
def bitsOf (n : ℕ) (b : Fin n → Bool) (k : ℕ) : Bool :=
  if h : k < n then b ⟨k, h⟩ else false

/-- Periodic extension of a cyclic bit vector. -/
def pw (t : ℕ) (b : Fin (t + 1) → Bool) (k : ℕ) : Bool :=
  b (Fin.ofNat (t + 1) k)

/-- Walk predicate: the labelled walk from `p` to `q` reading `b` through tests `F`. -/
def Good {s : ℕ} : (n : ℕ) → (Fin n → (Fin s → Bool) → Bool → Bool) →
    (Fin s → Bool) → (Fin s → Bool) → (Fin n → Bool) → Bool
  | 0, _, p, q, _ => decide (p = q)
  | n + 1, F, p, q, b =>
    F 0 p (b 0) && Good n (fun i => F i.succ) (nx p (b 0)) q (Fin.tail b)

/-- One transfer matrix. -/
def Mat {s n : ℕ} (F : Fin n → (Fin s → Bool) → Bool → Bool) (i : Fin n) :
    Matrix (Fin s → Bool) (Fin s → Bool) ℕ :=
  Matrix.of fun p q => (Finset.univ.filter fun bit : Bool => F i p bit = true ∧ nx p bit = q).card

lemma stSeq_shift {s : ℕ} (beta : ℕ → Bool) : ∀ (k : ℕ) (p : Fin s → Bool),
    stSeq beta p (k + 1) = stSeq (fun i => beta (i + 1)) (nx p (beta 0)) k := by
  intro k
  induction k with
  | zero => intro p; rfl
  | succ k ih =>
    intro p
    show nx (stSeq beta p (k + 1)) (beta (k + 1)) =
      nx (stSeq (fun i => beta (i + 1)) (nx p (beta 0)) k) (beta (k + 1))
    rw [ih p]

lemma card_good_succ {s n : ℕ} (F : Fin (n + 1) → (Fin s → Bool) → Bool → Bool)
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

lemma prod_apply {s : ℕ} : ∀ (n : ℕ) (F : Fin n → (Fin s → Bool) → Bool → Bool)
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

lemma good_iff {s : ℕ} : ∀ (n : ℕ) (F : Fin n → (Fin s → Bool) → Bool → Bool)
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

lemma stSeq_eq_yfun {s : ℕ} (beta : ℕ → Bool) (p : Fin s → Bool) :
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

lemma stSeq_agree {s : ℕ} (N : ℕ) (beta1 beta2 : ℕ → Bool) (p : Fin s → Bool)
    (hag : ∀ k, k < N → beta1 k = beta2 k) :
    ∀ m, m ≤ N → stSeq beta1 p m = stSeq beta2 p m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    show nx (stSeq beta1 p m) (beta1 m) = nx (stSeq beta2 p m) (beta2 m)
    rw [ih (by omega), hag m (by omega)]

lemma yfun_per {s N : ℕ} (beta : ℕ → Bool) (p : Fin s → Bool) (hN : ∀ k, beta (k + N) = beta k)
    (hcl : stSeq beta p N = p) (m : ℕ) : yfun p beta (m + N) = yfun p beta m := by
  by_cases hm : m < s
  · have h1 := stSeq_eq_yfun beta p N m hm
    rw [hcl] at h1
    rw [Nat.add_comm m N, ← h1]
    simp [yfun, hm]
  · unfold yfun
    rw [dif_neg (by omega), dif_neg hm, show m + N - s = (m - s) + N by omega, hN]

lemma yfun_mod {s N : ℕ} (beta : ℕ → Bool) (p : Fin s → Bool) (hN : ∀ k, beta (k + N) = beta k)
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

lemma pw_per (t : ℕ) (b : Fin (t + 1) → Bool) (k : ℕ) : pw t b (k + (t + 1)) = pw t b k := by
  unfold pw
  congr 1
  apply Fin.ext
  show (k + (t + 1)) % (t + 1) = k % (t + 1)
  rw [Nat.add_mod_right]

lemma ofNat_val (t : ℕ) (i : Fin (t + 1)) : Fin.ofNat (t + 1) i.val = i := by
  apply Fin.ext
  show i.val % (t + 1) = i.val
  exact Nat.mod_eq_of_lt i.isLt

/-- Closed walks of length `t+1` give periodic streams: agreement and closure. -/
lemma good_closure {s t : ℕ} (test : Fin (t + 1) → (Fin s → Bool) → Bool → Bool)
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

def Phi (t s : ℕ) (x : (Fin s → Bool) × (Fin (t + 1) → Bool)) : Fin (t + 1) → Bool :=
  fun i => yfun x.1 (pw t x.2) i.val

def Psi (t s : ℕ) (w : Fin (t + 1) → Bool) : (Fin s → Bool) × (Fin (t + 1) → Bool) :=
  (fun j => w (Fin.ofNat (t + 1) j.val), fun k => w (Fin.ofNat (t + 1) (k.val + s)))

lemma phi_ofNat (t s : ℕ) (test : Fin (t + 1) → (Fin s → Bool) → Bool → Bool)
    (x : (Fin s → Bool) × (Fin (t + 1) → Bool)) (h : Good (t + 1) test x.1 x.1 x.2 = true)
    (m : ℕ) : Phi t s x (Fin.ofNat (t + 1) m) = yfun x.1 (pw t x.2) m := by
  unfold Phi
  have hc := (good_closure test x.1 x.2 h).1
  exact yfun_mod (pw t x.2) x.1 (pw_per t x.2) hc m

lemma psi_yfun (t s : ℕ) (w : Fin (t + 1) → Bool) (m : ℕ) :
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

lemma dir2 (t s : ℕ) (test : Fin (t + 1) → (Fin s → Bool) → Bool → Bool)
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

lemma dir1 (t s : ℕ) (test : Fin (t + 1) → (Fin s → Bool) → Bool → Bool) (w : Fin (t + 1) → Bool)
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

end PEqualNP.Outside.L_lib_377

open PEqualNP.Outside.L_lib_377 in
theorem PEqualNP.Outside.L_lib_377 : ∀ (t s : ℕ) (test : Fin (t + 1) → (Fin s → Bool) → Bool → Bool),
  let next := fun (state : Fin s → Bool) (b : Bool) (j : Fin s) =>
    if h : j.val + 1 < s then state ⟨j.val + 1, h⟩ else b
  let step := fun i : Fin (t + 1) =>
    (Matrix.of (fun p q : Fin s → Bool =>
      (Finset.univ.filter (fun bit : Bool =>
        test i p bit = true ∧ next p bit = q)).card) :
      Matrix (Fin s → Bool) (Fin s → Bool) ℕ)
  let accepts := fun w : Fin (t + 1) → Bool =>
    ∀ a : Fin (t + 1),
      test a (fun pos : Fin s => w (Fin.ofNat (t + 1) (a.val + pos.val)))
        (w (Fin.ofNat (t + 1) (a.val + s))) = true
  Matrix.trace (List.ofFn step).prod = (Finset.univ.filter accepts).card := by
  intro t s test next step accepts
  have hprod : List.ofFn step = List.ofFn (fun i : Fin (t + 1) => Mat test i) := rfl
  rw [hprod]
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
      true_and, accepts] at hx ⊢
    exact dir2 t s test x hx
  · intro w hw
    simp only [Finset.mem_coe, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, Set.mem_setOf_eq,
      true_and, accepts] at hw ⊢
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
