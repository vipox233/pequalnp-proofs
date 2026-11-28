import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25637_aux

def z2 (b : Bool) : ZMod 2 := if b then 1 else 0

lemma z2_inj {a b : Bool} (h : z2 a = z2 b) : a = b := by
  cases a <;> cases b <;> simp [z2] at h <;> rfl

lemma z2_xor (a b : Bool) : z2 (xor a b) = z2 a + z2 b := by
  cases a <;> cases b <;> decide

lemma z2_and (a b : Bool) : z2 (a && b) = z2 a * z2 b := by
  cases a <;> cases b <;> decide

lemma z2_decide (x : ZMod 2) : z2 (decide (x = 1)) = x := by
  revert x; decide

lemma z2_toNat (b : Bool) : ((b.toNat : ℕ) : ZMod 2) = z2 b := by
  cases b <;> rfl

def par (n : ℕ) : Bool := n % 2 == 1

lemma z2_par (n : ℕ) : z2 (par n) = (n : ZMod 2) := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rw [← ZMod.natCast_mod n 2]
  rcases h with h | h <;> simp [par, z2, h]

lemma z2_par_sum {α : Type*} (S : Finset α) (b : α → Bool) :
    z2 (par (∑ i ∈ S, (b i).toNat)) = ∑ i ∈ S, z2 (b i) := by
  rw [z2_par, Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => z2_toNat (b i)

def stepRun {W : Type*} (ask : ℕ → ℕ → W → Bool) (x : W) (n : ℕ) : ℕ :=
  (List.range n).foldl (fun h pos => h + ((ask pos h x).toNat <<< pos)) 0

lemma stepRun_succ {W : Type*} (ask : ℕ → ℕ → W → Bool) (x : W) (n : ℕ) :
    stepRun ask x (n + 1) =
      stepRun ask x n + ((ask n (stepRun ask x n) x).toNat <<< n) := by
  simp only [stepRun, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma stepRun_lt {W : Type*} (ask : ℕ → ℕ → W → Bool) (x : W) :
    ∀ n : ℕ, stepRun ask x n < 2 ^ n
  | 0 => by simp [stepRun]
  | n + 1 => by
      rw [stepRun_succ, Nat.shiftLeft_eq]
      have ih := stepRun_lt ask x n
      cases ask n (stepRun ask x n) x <;> simp [pow_succ] <;> omega

lemma testBit_add_shift {h n : ℕ} (hh : h < 2 ^ n) (b : Bool) (p : ℕ) :
    (h + (b.toNat <<< n)).testBit p =
      if p < n then h.testBit p else if p = n then b else false := by
  rw [Nat.shiftLeft_eq]
  cases b
  · simp only [Bool.toNat_false, zero_mul, add_zero]
    split_ifs with h1 h2
    · rfl
    · subst h2
      exact Nat.testBit_lt_two_pow hh
    · have hlt : h < 2 ^ p := lt_of_lt_of_le hh (Nat.pow_le_pow_right (by omega) (by omega))
      exact Nat.testBit_lt_two_pow hlt
  · simp only [Bool.toNat_true, one_mul]
    split_ifs with h1 h2
    · rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
      have hpow : 2 ^ n = 2 ^ p * 2 ^ (n - p) := by rw [← pow_add, Nat.add_sub_of_le (by omega)]
      have hdiv : (h + 2 ^ n) / 2 ^ p = h / 2 ^ p + 2 ^ (n - p) := by
        rw [hpow, Nat.add_mul_div_left _ _ (by positivity)]
      have heven : 2 ∣ 2 ^ (n - p) := by
        have hsub : 1 ≤ n - p := by omega
        have h2 : 2 ^ (n - p) = 2 * 2 ^ (n - p - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hsub]
        exact ⟨2 ^ (n - p - 1), h2⟩
      rw [hdiv]
      rcases heven with ⟨q, hq⟩
      rw [hq]
      simp [Nat.add_mul_mod_self_left]
    · subst h2
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have hdiv : (h + 2 ^ p) / 2 ^ p = 1 := by
        rw [Nat.add_div_right _ (by positivity), Nat.div_eq_of_lt hh]
      simp [hdiv]
    · have hlt : h + 2 ^ n < 2 ^ p := by
        have h2 : 2 ^ (n + 1) ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)
        rw [pow_succ] at h2
        omega
      exact Nat.testBit_lt_two_pow hlt

lemma stepRun_testBit {W : Type*} (ask : ℕ → ℕ → W → Bool) (x : W) :
    ∀ n p : ℕ, p < n → (stepRun ask x n).testBit p = ask p (stepRun ask x p) x
  | 0, _, hp => by omega
  | n + 1, p, hp => by
      rw [stepRun_succ, testBit_add_shift (stepRun_lt ask x n)]
      by_cases hpn : p < n
      · simp only [hpn, ↓reduceIte]
        exact stepRun_testBit ask x n p hpn
      · have hpeq : p = n := by omega
        subst hpeq
        simp

lemma stepRun_eq_iff {W : Type*} (ask : ℕ → ℕ → W → Bool) (x : W) (n path : ℕ)
    (hpath : path < 2 ^ n) :
    stepRun ask x n = path ↔
      ∀ u : Fin n, ask u.val (path % 2 ^ u.val) x = path.testBit u.val := by
  constructor
  · intro heq u
    have hprev : stepRun ask x u.val = path % 2 ^ u.val := by
      apply Nat.eq_of_testBit_eq
      intro p
      rw [Nat.testBit_mod_two_pow]
      by_cases hp : p < u.val
      · simp only [hp, decide_true, Bool.true_and]
        rw [stepRun_testBit ask x u.val p hp, ← heq,
          stepRun_testBit ask x n p (lt_trans hp u.isLt)]
      · simp only [hp, decide_false, Bool.false_and]
        exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (stepRun_lt ask x u.val)
          (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [← hprev, ← stepRun_testBit ask x n u.val u.isLt, heq]
  · intro hall
    have hprefix : ∀ r : ℕ, r ≤ n → stepRun ask x r = path % 2 ^ r := by
      intro r
      induction r with
      | zero => intro _; simp [stepRun, Nat.mod_one]
      | succ r ih =>
        intro hr
        have hrlt : r < n := by omega
        have hih := ih (by omega)
        apply Nat.eq_of_testBit_eq
        intro p
        rw [stepRun_succ, testBit_add_shift (stepRun_lt ask x r), Nat.testBit_mod_two_pow]
        by_cases hpr : p < r
        · have hpr1 : p < r + 1 := by omega
          simp only [hpr, hpr1, ↓reduceIte, decide_true, Bool.true_and]
          rw [hih, Nat.testBit_mod_two_pow]
          simp [hpr]
        · by_cases hpeq : p = r
          · subst hpeq
            simp only [lt_irrefl, ↓reduceIte, Nat.lt_succ_self, decide_true, Bool.true_and]
            rw [hih]
            exact hall ⟨p, hrlt⟩
          · have hnlt : ¬(p < r + 1) := by omega
            simp [hpr, hpeq, hnlt]
    have hfin := hprefix n (le_refl n)
    rwa [Nat.mod_eq_of_lt hpath] at hfin

def wordOf (k : ℕ) (w : Fin k → Bool) : Fin (2 ^ k) :=
  ⟨∑ q : Fin k, if w q then 2 ^ q.val else 0, by
    have hsum : ∑ q : Fin k, (if w q then 2 ^ q.val else 0) ≤ ∑ q : Fin k, 2 ^ q.val :=
      Finset.sum_le_sum fun q _ => by cases w q <;> simp
    have hgeom : ∑ q : Fin k, 2 ^ q.val = 2 ^ k - 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i)]
      have h1 := Nat.geomSum_eq (by omega : 2 ≤ 2) k
      simpa using h1
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
    omega⟩

lemma testBit_wordOf (k : ℕ) (w : Fin k → Bool) (q : Fin k) :
    (wordOf k w).val.testBit q.val = w q := by
  have haux : ∀ n : ℕ, ∀ g : ℕ → Bool, ∀ j : ℕ, j < n →
      (∑ i ∈ Finset.range n, if g i then 2 ^ i else 0).testBit j = g j := by
    intro n
    induction n with
    | zero => intro _ _ hj; omega
    | succ n ih =>
      intro g j hj
      rw [Finset.sum_range_succ]
      have hlt : ∑ i ∈ Finset.range n, (if g i then 2 ^ i else 0) < 2 ^ n := by
        have h1 : ∑ i ∈ Finset.range n, (if g i then 2 ^ i else 0) ≤ ∑ i ∈ Finset.range n, 2 ^ i :=
          Finset.sum_le_sum fun i _ => by cases g i <;> simp
        have h2 : ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1 := by
          have := Nat.geomSum_eq (by omega : 2 ≤ 2) n
          simpa using this
        have h3 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
        omega
      have hshift : (if g n then 2 ^ n else 0) = (g n).toNat <<< n := by
        rw [Nat.shiftLeft_eq]
        cases g n <;> simp
      rw [hshift, testBit_add_shift hlt]
      by_cases hjn : j < n
      · simp only [hjn, ↓reduceIte]
        exact ih g j hjn
      · have hjeq : j = n := by omega
        subst hjeq
        simp
  have hcongr :
      ∑ i : Fin k, (if w i then 2 ^ i.val else 0) =
      ∑ i : Fin k, (if (if h : i.val < k then w ⟨i.val, h⟩ else false) then 2 ^ i.val else 0) :=
    Finset.sum_congr rfl fun i _ => by simp [i.isLt]
  simp only [wordOf]
  rw [hcongr, Fin.sum_univ_eq_sum_range
    (fun i => if (if h : i < k then w ⟨i, h⟩ else false) then 2 ^ i else 0)]
  have h1 := haux k (fun i => if h : i < k then w ⟨i, h⟩ else false) q.val q.isLt
  simpa [q.isLt] using h1

lemma wordOf_testBit (k : ℕ) (x : Fin (2 ^ k)) :
    wordOf k (fun i : Fin k => x.val.testBit i.val) = x := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < k
  · exact testBit_wordOf k (fun i : Fin k => x.val.testBit i.val) ⟨j, hj⟩
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (wordOf k _).isLt
          (Nat.pow_le_pow_right (by omega) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt
          (Nat.pow_le_pow_right (by omega) (by omega)))]

def vec (k : ℕ) (q : Fin (2 ^ k)) : Fin k → ZMod 2 := fun i => z2 (q.val.testBit i.val)

def vecEquiv (k : ℕ) : Fin (2 ^ k) ≃ (Fin k → ZMod 2) where
  toFun := vec k
  invFun v := wordOf k (fun i => decide (v i = 1))
  left_inv q := by
    have h : (fun i : Fin k => decide (vec k q i = 1)) = fun i : Fin k => q.val.testBit i.val := by
      funext i
      exact z2_inj (z2_decide _)
    show wordOf k (fun i => decide (vec k q i = 1)) = q
    rw [h]
    exact wordOf_testBit k q
  right_inv v := by
    funext i
    simp only [vec, testBit_wordOf, z2_decide]

lemma vecEquiv_apply (k : ℕ) (q : Fin (2 ^ k)) : vecEquiv k q = vec k q := rfl

lemma vec_symm (k : ℕ) (v : Fin k → ZMod 2) : vec k ((vecEquiv k).symm v) = v :=
  (vecEquiv k).apply_symm_apply v

def lin (k : ℕ) (mask : Fin k → Bool) (q : Fin (2 ^ k)) : Bool :=
  par (∑ i : Fin k, (mask i && q.val.testBit i.val).toNat)

lemma z2_lin (k : ℕ) (mask : Fin k → Bool) (q : Fin (2 ^ k)) :
    z2 (lin k mask q) = ∑ i : Fin k, z2 (mask i) * vec k q i := by
  rw [lin, z2_par_sum]
  exact Finset.sum_congr rfl fun i _ => z2_and _ _

def quadP (k : ℕ) (g : Fin (2 ^ k) → Bool) : Prop :=
  ∃ (b : Bool) (l : Fin k → Bool) (a : Fin k → Fin k → Bool),
    ∀ q, g q = xor (xor b (lin k l q))
      (par (∑ i : Fin k, ∑ j : Fin k, (a i j && q.val.testBit i.val && q.val.testBit j.val).toNat))

def QuadForm (k : ℕ) (G : (Fin k → ZMod 2) → ZMod 2) : Prop :=
  ∃ (β : ZMod 2) (l : Fin k → ZMod 2) (α : Fin k → Fin k → ZMod 2),
    ∀ v, G v = β + ∑ i, l i * v i + ∑ i, ∑ j, α i j * v i * v j

lemma z2_quadShape (k : ℕ) (b : Bool) (l : Fin k → Bool) (a : Fin k → Fin k → Bool)
    (q : Fin (2 ^ k)) :
    z2 (xor (xor b (lin k l q)) (par (∑ i : Fin k, ∑ j : Fin k,
      (a i j && q.val.testBit i.val && q.val.testBit j.val).toNat))) =
    z2 b + ∑ i, z2 (l i) * vec k q i + ∑ i, ∑ j, z2 (a i j) * vec k q i * vec k q j := by
  rw [z2_xor, z2_xor, z2_lin, z2_par, Nat.cast_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [z2_toNat, z2_and, z2_and]
  rfl

lemma quadP_iff (k : ℕ) (g : Fin (2 ^ k) → Bool) :
    quadP k g ↔ QuadForm k (fun v => z2 (g ((vecEquiv k).symm v))) := by
  constructor
  · rintro ⟨b, l, a, h⟩
    refine ⟨z2 b, fun i => z2 (l i), fun i j => z2 (a i j), fun v => ?_⟩
    show z2 (g ((vecEquiv k).symm v)) = _
    rw [h, z2_quadShape, vec_symm]
  · rintro ⟨β, l, α, h⟩
    refine ⟨decide (β = 1), fun i => decide (l i = 1), fun i j => decide (α i j = 1), fun q => ?_⟩
    apply z2_inj
    have hq : z2 (g ((vecEquiv k).symm (vecEquiv k q))) = _ := h (vecEquiv k q)
    rw [Equiv.symm_apply_apply] at hq
    rw [hq, z2_quadShape]
    simp only [z2_decide, vecEquiv_apply]

def runP (k d : ℕ) (choose : ℕ → ℕ → Fin k → Bool) (q : Fin (2 ^ k)) : ℕ :=
  (List.range d).foldl (fun history t => history + ((lin k (choose t history) q).toNat <<< t)) 0

lemma runP_eq (k d : ℕ) (choose : ℕ → ℕ → Fin k → Bool) (q : Fin (2 ^ k)) :
    runP k d choose q = stepRun (fun t h x => lin k (choose t h) x) q d := rfl

def winOut (u s l : Fin 3 → Bool) (c0 : Bool) : Bool :=
  xor ((xor (u 0) (s 0)) && (xor (u 1) (s 1)) && (xor (u 2) (s 2)))
    (xor (xor (xor c0 (l 0 && u 0)) (l 1 && u 1)) (l 2 && u 2))

lemma z2_winOut (u s l : Fin 3 → Bool) (c0 : Bool) :
    z2 (winOut u s l c0) =
      (z2 (u 0) + z2 (s 0)) * (z2 (u 1) + z2 (s 1)) * (z2 (u 2) + z2 (s 2)) +
        (z2 c0 + ∑ j : Fin 3, z2 (l j) * z2 (u j)) := by
  rw [Fin.sum_univ_three, winOut]
  cases u 0 <;> cases u 1 <;> cases u 2 <;> cases s 0 <;> cases s 1 <;> cases s 2 <;>
    cases l 0 <;> cases l 1 <;> cases l 2 <;> cases c0 <;> decide

def sgn (v : ZMod 2) : ℤ := if v = 0 then 1 else -1

section Abstract

variable {V : Type*} [AddCommGroup V]

def IsAff (f : V → ZMod 2) : Prop := ∀ a b c, f (a + b + c) = f a + f b + f c

def IsQuad (Q : V → ZMod 2) : Prop :=
  ∀ a u v w, Q a + Q (a + u) + Q (a + v) + Q (a + w) + Q (a + u + v) + Q (a + u + w) +
    Q (a + v + w) + Q (a + u + v + w) = 0

def AffSet (A : Finset V) : Prop := ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a + b + c ∈ A

variable {ι : Type*} [DecidableEq ι]

def cube (f : ι → Fin 3 → V → ZMod 2) (i : ι) (a : V) : ZMod 2 := f i 0 a * f i 1 a * f i 2 a

def pat (f : ι → Fin 3 → V → ZMod 2) (S : Finset ι) (a : V) : ι → Fin 3 → ZMod 2 :=
  fun i j => if i ∈ S then f i j a else 0

end Abstract

lemma abs_sgn (a : ZMod 2) : |sgn a| = 1 := by
  revert a; decide

lemma two_mul_card_agree {α : Type*} (F : Finset α) (a b : α → Bool) :
    (2 * ((F.filter (fun q => a q == b q)).card : ℤ)) =
      F.card + ∑ q ∈ F, sgn (z2 (a q) + z2 (b q)) := by
  have h1 : ∀ q, sgn (z2 (a q) + z2 (b q)) = 2 * (if (a q == b q) = true then 1 else 0) - 1 := by
    intro q
    cases a q <;> cases b q <;> decide
  simp only [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  ring

section AbstractBasics

variable {V : Type*} [AddCommGroup V]

lemma z2_add_self (x : ZMod 2) : x + x = 0 := by
  revert x; decide

lemma z2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

lemma IsAff.const (c : ZMod 2) : IsAff (fun _ : V => c) := fun _ _ _ => by
  show c = c + c + c
  revert c; decide

lemma IsAff.add {f g : V → ZMod 2} (hf : IsAff f) (hg : IsAff g) : IsAff (fun a => f a + g a) :=
  fun a b c => by simp only [hf a b c, hg a b c]; ring

lemma IsAff.const_mul (c : ZMod 2) {f : V → ZMod 2} (hf : IsAff f) : IsAff (fun a => c * f a) :=
  fun a b c' => by simp only [hf a b c']; ring

lemma IsAff.sum {α : Type*} (s : Finset α) (F : α → V → ZMod 2) (h : ∀ i ∈ s, IsAff (F i)) :
    IsAff (fun a => ∑ i ∈ s, F i a) := fun a b c => by
  simp only [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i hi => h i hi a b c

lemma IsQuad.add {P Q : V → ZMod 2} (hP : IsQuad P) (hQ : IsQuad Q) :
    IsQuad (fun a => P a + Q a) := fun a u v w => by
  linear_combination hP a u v w + hQ a u v w

lemma IsQuad.const_mul (c : ZMod 2) {Q : V → ZMod 2} (hQ : IsQuad Q) :
    IsQuad (fun a => c * Q a) := fun a u v w => by
  linear_combination c * hQ a u v w

lemma IsQuad.sum {α : Type*} (s : Finset α) (F : α → V → ZMod 2) (h : ∀ i ∈ s, IsQuad (F i)) :
    IsQuad (fun a => ∑ i ∈ s, F i a) := fun a u v w => by
  simp only [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun i hi => h i hi a u v w

lemma IsAff.vertices {f : V → ZMod 2} (hf : IsAff f) (a u v w : V) :
    f (a + u) = f a + f u + f 0 ∧ f (a + v) = f a + f v + f 0 ∧ f (a + w) = f a + f w + f 0 ∧
    f (a + u + v) = f a + f u + f v ∧ f (a + u + w) = f a + f u + f w ∧
    f (a + v + w) = f a + f v + f w ∧ f (a + u + v + w) = f a + f u + f v + f w + f 0 := by
  have h1 : ∀ x y : V, f (x + y) = f x + f y + f 0 := fun x y => by
    have := hf x y 0
    rwa [add_zero] at this
  refine ⟨h1 a u, h1 a v, h1 a w, hf a u v, hf a u w, hf a v w, ?_⟩
  rw [hf (a + u) v w, h1 a u]
  ring

lemma IsAff.isQuad {f : V → ZMod 2} (hf : IsAff f) : IsQuad f :=
  fun a u v w => by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hf.vertices a u v w
  rw [e1, e2, e3, e4, e5, e6, e7]
  generalize f a = p, f u = q, f v = r, f w = s, f 0 = t
  revert p q r s t; decide

lemma IsAff.mul {f g : V → ZMod 2} (hf : IsAff f) (hg : IsAff g) :
    IsQuad (fun a => f a * g a) := fun a u v w => by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hf.vertices a u v w
  obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hg.vertices a u v w
  simp only [e1, e2, e3, e4, e5, e6, e7, d1, d2, d3, d4, d5, d6, d7]
  generalize f a = p, f u = q, f v = r, f w = s, f 0 = t
  generalize g a = p', g u = q', g v = r', g w = s', g 0 = t'
  revert p q r s t p' q' r' s' t'; decide

end AbstractBasics

lemma z2_two : (2 : ZMod 2) = 0 := rfl

lemma z2_add3 (c : ZMod 2) : c + c + c = c := by
  revert c
  decide

lemma z2_eq_add_one {x c : ZMod 2} (hx : x ≠ c) : x = c + 1 := by
  revert x c
  decide

lemma z2_ne_add_one (c : ZMod 2) : c ≠ c + 1 := by
  revert c
  decide

lemma z2_quadric_hits (κ1 κ2 c : ZMod 2) : ∃ β γ : ZMod 2, β * γ + κ1 * β + κ2 * γ = c := by
  revert κ1 κ2 c
  decide

lemma z2_third {x y c : ZMod 2} (hx : x ≠ c) (hy : y ≠ c) : x + c + y = c := by
  revert x y c
  decide

lemma sum_split_z2 {α M : Type*} [AddCommMonoid M] (A : Finset α) (X : α → ZMod 2) (F : α → M) :
    ∑ a ∈ A, F a =
      ∑ a ∈ A.filter (fun a => X a = 0), F a + ∑ a ∈ A.filter (fun a => X a = 1), F a := by
  rw [← Finset.sum_filter_add_sum_filter_not A (fun a => X a = 0) F]
  congr 1
  refine Finset.sum_congr (Finset.filter_congr fun a _ => ?_) fun _ _ => rfl
  generalize X a = x
  revert x
  decide

lemma abs_sum_sgn_le {α : Type*} (A : Finset α) (F : α → ZMod 2) :
    |∑ a ∈ A, sgn (F a)| ≤ (A.card : ℤ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simp [abs_sgn]

lemma AffSet.filter {V : Type*} [AddCommGroup V] {A : Finset V} (hA : AffSet A)
    {g : V → ZMod 2} (hg : IsAff g) (c : ZMod 2) : AffSet (A.filter (fun a => g a = c)) := by
  intro a ha b hb c' hc'
  rw [Finset.mem_filter] at ha hb hc' ⊢
  exact ⟨hA a ha.1 b hb.1 c' hc'.1, by rw [hg, ha.2, hb.2, hc'.2, z2_add3]⟩

lemma card_filter_of_flip {V : Type*} [AddCommGroup V] (h2 : ∀ v : V, v + v = 0)
    (R : Finset V) (X : V → ZMod 2) (e : V) (hinv : ∀ a ∈ R, a + e ∈ R)
    (hX : ∀ a, X (a + e) = X a + 1) (v : ZMod 2) :
    2 * (R.filter (fun a => X a = v)).card = R.card := by
  have hz : ∀ x : ZMod 2, x + 1 = v ↔ ¬x = v := by revert v; decide
  have hcancel : ∀ a : V, a + e + e = a := fun a => by rw [add_assoc, h2, add_zero]
  have hcard : (R.filter (fun a => X a = v)).card = (R.filter (fun a => ¬X a = v)).card := by
    refine Finset.card_nbij' (· + e) (· + e) ?_ ?_ (fun a _ => hcancel a) (fun a _ => hcancel a)
    · intro a ha
      rw [Finset.mem_coe, Finset.mem_filter] at ha ⊢
      exact ⟨hinv a ha.1, fun h => (hz _).1 ((hX a).symm.trans h) ha.2⟩
    · intro a ha
      rw [Finset.mem_coe, Finset.mem_filter] at ha ⊢
      exact ⟨hinv a ha.1, (hX a).trans ((hz _).2 ha.2)⟩
  have := Finset.card_filter_add_card_filter_not (s := R) (fun a => X a = v)
  omega

lemma IsQuad.deriv {V : Type*} [AddCommGroup V] (h2 : ∀ v : V, v + v = 0) {Q : V → ZMod 2}
    (hQ : IsQuad Q) (e : V) : IsAff (fun a => Q a + Q (a + e)) := by
  intro a b c
  have h := hQ a (a + b) (a + c) e
  have e1 : a + (a + b) = b := by rw [← add_assoc, h2, zero_add]
  have e2 : a + (a + c) = c := by rw [← add_assoc, h2, zero_add]
  have e3 : a + (a + b) + (a + c) = a + b + c := by rw [e1, add_left_comm, add_assoc]
  rw [e3, e1, e2] at h
  show Q (a + b + c) + Q (a + b + c + e) = Q a + Q (a + e) + (Q b + Q (b + e)) + (Q c + Q (c + e))
  linear_combination h - (Q a + Q (a + e) + Q b + Q (b + e) + Q c + Q (c + e)) * z2_two

lemma z2fun_add_self {α : Type*} (t : α → ZMod 2) : t + t = 0 := by
  funext j
  exact z2_add_self _

lemma pat_add_self {ι : Type*} (t : ι → Fin 3 → ZMod 2) : t + t = 0 := by
  funext i
  exact z2fun_add_self _

lemma pat_add3 {V : Type*} [AddCommGroup V] {ι : Type*} [DecidableEq ι]
    (f : ι → Fin 3 → V → ZMod 2) (hf : ∀ i j, IsAff (f i j)) (S : Finset ι) (a b c : V) :
    pat f S (a + b + c) = pat f S a + pat f S b + pat f S c := by
  funext i j
  by_cases hi : i ∈ S
  · simp only [pat, hi, ite_true, Pi.add_apply]
    exact hf i j a b c
  · simp only [pat, hi, ite_false, Pi.add_apply, add_zero]

lemma sum_cube_eq_of_pat {V : Type*} {ι : Type*} [DecidableEq ι] (f : ι → Fin 3 → V → ZMod 2)
    {S : Finset ι} {a b : V} (h : pat f S a = pat f S b) :
    ∑ i ∈ S, cube f i a = ∑ i ∈ S, cube f i b := by
  refine Finset.sum_congr rfl fun i hi => ?_
  have hj : ∀ j, f i j a = f i j b := fun j => by
    have := congr_fun (congr_fun h i) j
    simpa only [pat, hi, ite_true] using this
  simp only [cube, hj]

lemma image_pat_filter_of_flip {V : Type*} [AddCommGroup V] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (f : ι → Fin 3 → V → ZMod 2) (S : Finset ι) {A : Finset V} {X : V → ZMod 2}
    {e : V} (hinv : ∀ a ∈ A, a + e ∈ A) (hX : ∀ a, X (a + e) = X a + 1)
    (hpat : ∀ a, pat f S (a + e) = pat f S a) (v : ZMod 2) :
    (A.filter (fun a => X a = v)).image (pat f S) = A.image (pat f S) := by
  refine Finset.Subset.antisymm (Finset.image_subset_image (Finset.filter_subset _ _))
    fun t ht => ?_
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
  by_cases hv : X a = v
  · exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨ha, hv⟩)
  · rw [← hpat a]
    refine Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hinv a ha, ?_⟩)
    rw [hX]
    generalize X a = x at hv ⊢
    revert x v
    decide

lemma card_pat_le_two_mul {V : Type*} [AddCommGroup V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Fin 3 → V → ZMod 2) (hf : ∀ i j, IsAff (f i j)) (S : Finset ι) {A : Finset V}
    (hA : AffSet A) {g : V → ZMod 2} (hg : IsAff g) (c : ZMod 2)
    (hne : (A.filter (fun a => g a = c)).Nonempty) :
    (A.image (pat f S)).card ≤ 2 * ((A.filter (fun a => g a = c)).image (pat f S)).card := by
  by_cases hall : ∀ a ∈ A, g a = c
  · rw [Finset.filter_true_of_mem hall]
    omega
  · simp only [not_forall, exists_prop] at hall
    obtain ⟨p', hp', hgp'⟩ := hall
    obtain ⟨p, hp⟩ := hne
    rw [Finset.mem_filter] at hp
    have hsub : A.image (pat f S) ⊆ (A.filter (fun a => g a = c)).image (pat f S) ∪
        ((A.filter (fun a => g a = c)).image (pat f S)).image (· + (pat f S p + pat f S p')) := by
      intro t ht
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
      by_cases hga : g a = c
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨ha, hga⟩))
      · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨pat f S (a + p + p'),
          Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hA a ha p hp.1 p' hp', ?_⟩), ?_⟩)
        · rw [hg, hp.2]
          exact z2_third hga hgp'
        · rw [pat_add3 f hf, add_assoc (pat f S a), add_assoc (pat f S a), pat_add_self, add_zero]
    calc (A.image (pat f S)).card
        ≤ ((A.filter (fun a => g a = c)).image (pat f S)).card +
          (((A.filter (fun a => g a = c)).image (pat f S)).image
            (· + (pat f S p + pat f S p'))).card :=
          (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      _ ≤ 2 * ((A.filter (fun a => g a = c)).image (pat f S)).card := by
          have := Finset.card_image_le (s := (A.filter (fun a => g a = c)).image (pat f S))
            (f := (· + (pat f S p + pat f S p')))
          omega

def IsShift {V : Type*} [AddCommGroup V] {ι : Type*} [DecidableEq ι] (f : ι → Fin 3 → V → ZMod 2)
    (S : Finset ι) (i : ι) (A : Finset V) (u : Fin 3 → ZMod 2) (e : V) : Prop :=
  (∀ a ∈ A, a + e ∈ A) ∧ (∀ a, pat f S (a + e) = pat f S a) ∧ ∀ a j, f i j (a + e) = f i j a + u j

lemma isShift_of_pair {V : Type*} [AddCommGroup V] {ι : Type*} [DecidableEq ι]
    {f : ι → Fin 3 → V → ZMod 2} (hf : ∀ i j, IsAff (f i j)) (S : Finset ι) (i : ι) {A : Finset V}
    (hA : AffSet A) {a1 a2 : V} (h1 : a1 ∈ A) (h2 : a2 ∈ A) (h : pat f S a1 = pat f S a2) :
    IsShift f S i A (fun j => f i j a1 + f i j a2) (a1 + a2) := by
  refine ⟨fun a ha => ?_, fun a => ?_, fun a j => ?_⟩
  · rw [← add_assoc]
    exact hA a ha a1 h1 a2 h2
  · rw [← add_assoc, pat_add3 f hf, h, add_assoc, pat_add_self, add_zero]
  · rw [← add_assoc, hf i j, add_assoc]

lemma IsShift.add {V : Type*} [AddCommGroup V] {ι : Type*} [DecidableEq ι]
    {f : ι → Fin 3 → V → ZMod 2} {S : Finset ι} {i : ι} {A : Finset V} {u u' : Fin 3 → ZMod 2} {e e' : V}
    (h : IsShift f S i A u e) (h' : IsShift f S i A u' e') :
    IsShift f S i A (u + u') (e + e') := by
  refine ⟨fun a ha => ?_, fun a => ?_, fun a j => ?_⟩
  · rw [← add_assoc]
    exact h'.1 _ (h.1 a ha)
  · rw [← add_assoc, h'.2.1, h.2.1]
  · rw [← add_assoc, h'.2.2, h.2.2, Pi.add_apply, add_assoc]

lemma IsShift.flip {V : Type*} [AddCommGroup V] {ι : Type*} [DecidableEq ι]
    {f : ι → Fin 3 → V → ZMod 2} {S : Finset ι} {i : ι} {A : Finset V} {c : Fin 3} {e : V}
    (h : IsShift f S i A (Pi.single c 1) e) (a : V) : f i c (a + e) = f i c a + 1 := by
  rw [h.2.2, Pi.single_eq_same]

lemma IsShift.keep {V : Type*} [AddCommGroup V] {ι : Type*} [DecidableEq ι]
    {f : ι → Fin 3 → V → ZMod 2} {S : Finset ι} {i : ι} {A : Finset V} {c c' : Fin 3} {e : V}
    (h : IsShift f S i A (Pi.single c 1) e) (hc : c' ≠ c) (a : V) : f i c' (a + e) = f i c' a := by
  rw [h.2.2, Pi.single_eq_of_ne hc, add_zero]

lemma card_pat_insert_le {V : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → Fin 3 → V → ZMod 2} {S : Finset ι} {i : ι} (hi : i ∉ S) {A : Finset V}
    (U : Finset (Fin 3 → ZMod 2))
    (hU : ∀ a1 ∈ A, ∀ a2 ∈ A, pat f S a1 = pat f S a2 → (fun j => f i j a1 + f i j a2) ∈ U) :
    (A.image (pat f (insert i S))).card ≤ U.card * (A.image (pat f S)).card := by
  let ρ : (ι → Fin 3 → ZMod 2) → ι → Fin 3 → ZMod 2 := fun t i' j => if i' ∈ S then t i' j else 0
  have hρ : ∀ a, ρ (pat f (insert i S) a) = pat f S a := fun a => by
    funext i' j
    by_cases h : i' ∈ S
    · simp only [ρ, pat, h, Finset.mem_insert, or_true, ite_true]
    · simp only [ρ, pat, h, ite_false]
  have himg : (A.image (pat f (insert i S))).image ρ = A.image (pat f S) := by
    rw [Finset.image_image]
    exact Finset.image_congr fun a _ => hρ a
  rw [← himg]
  refine Finset.card_le_mul_card_image _ _ fun t' _ => ?_
  rcases ((A.image (pat f (insert i S))).filter (fun t => ρ t = t')).eq_empty_or_nonempty with
    h0 | ⟨t0, ht0⟩
  · rw [h0]
    exact Nat.zero_le _
  obtain ⟨hmem0, hρ0⟩ := Finset.mem_filter.mp ht0
  obtain ⟨a0, ha0, rfl⟩ := Finset.mem_image.mp hmem0
  have hblock : ∀ a j, pat f (insert i S) a i j = f i j a := fun a j => by
    simp only [pat, Finset.mem_insert, true_or, ite_true]
  refine Finset.card_le_card_of_injOn (fun t j => t i j + f i j a0) ?_ ?_
  · intro t ht
    obtain ⟨hmem, hρt⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ht)
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hmem
    have hpat : pat f S a = pat f S a0 := by rw [← hρ a, ← hρ a0, hρt, hρ0]
    simpa only [hblock, Finset.mem_coe] using hU a ha a0 ha0 hpat
  · intro t ht t2 ht2 heq
    obtain ⟨hmem, hρt⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ht)
    obtain ⟨hmem2, hρt2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ht2)
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hmem
    obtain ⟨a2, _, rfl⟩ := Finset.mem_image.mp hmem2
    have hpat : pat f S a = pat f S a2 := by rw [← hρ a, ← hρ a2, hρt, hρt2]
    funext i' j
    by_cases hi' : i' = i
    · subst hi'
      exact add_right_cancel (congr_fun heq j)
    · have := congr_fun (congr_fun hpat i') j
      simpa only [pat, Finset.mem_insert, hi', false_or] using this

lemma split_bound {V : Type*} [AddCommGroup V] {X Y Z G Q : V → ZMod 2} (hX : IsAff X)
    (hY : IsAff Y) (hZ : IsAff Z)
    (hQ : IsQuad Q) {A : Finset V} (hA : AffSet A) {e : ℕ} (Hyp : Finset V → Prop)
    (ih : ∀ (B : Finset V) (Q' : V → ZMod 2), AffSet B → IsQuad Q' → Hyp B →
      4 ^ e * |∑ a ∈ B, sgn (G a + Q' a)| ≤ 3 ^ e * (B.card : ℤ))
    (hpiece : ∀ v : ZMod 2, (A.filter (fun a => X a = v)).Nonempty →
      Hyp (A.filter (fun a => X a = v))) :
    4 ^ e * |∑ a ∈ A, sgn (X a * Y a * Z a + G a + Q a)| ≤ 3 ^ e * (A.card : ℤ) := by
  have key : ∀ v : ZMod 2,
      4 ^ e * |∑ a ∈ A.filter (fun a => X a = v), sgn (X a * Y a * Z a + G a + Q a)| ≤
        3 ^ e * ((A.filter (fun a => X a = v)).card : ℤ) := by
    intro v
    rcases (A.filter (fun a => X a = v)).eq_empty_or_nonempty with h0 | hne
    · rw [h0]
      simp
    · have hsum : ∑ a ∈ A.filter (fun a => X a = v), sgn (X a * Y a * Z a + G a + Q a) =
          ∑ a ∈ A.filter (fun a => X a = v), sgn (G a + (v * (Y a * Z a) + Q a)) := by
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [(Finset.mem_filter.mp ha).2]
        congr 1
        ring
      rw [hsum]
      exact ih _ _ (hA.filter hX v) (((hY.mul hZ).const_mul v).add hQ) (hpiece v hne)
  have hcard : (A.card : ℤ) = ((A.filter (fun a => X a = 0)).card : ℤ) +
      ((A.filter (fun a => X a = 1)).card : ℤ) := by
    have := sum_split_z2 A X (fun _ => (1 : ℤ))
    simpa using this
  rw [sum_split_z2 A X, hcard]
  have k0 := key 0
  have k1 := key 1
  have habs := abs_add_le
    (∑ a ∈ A.filter (fun a => X a = 0), sgn (X a * Y a * Z a + G a + Q a))
    (∑ a ∈ A.filter (fun a => X a = 1), sgn (X a * Y a * Z a + G a + Q a))
  have hpos : (0 : ℤ) ≤ 4 ^ e := by positivity
  nlinarith [mul_le_mul_of_nonneg_left habs hpos]

lemma corr_peel {V : Type*} [AddCommGroup V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h2 : ∀ v : V, v + v = 0) {f : ι → Fin 3 → V → ZMod 2} (hf : ∀ i j, IsAff (f i j))
    {S : Finset ι} {i : ι} {A : Finset V} {G Q : V → ZMod 2} {e : ℕ} (hA : AffSet A)
    (hQ : IsQuad Q) (hG : ∀ a b, pat f S a = pat f S b → G a = G b)
    (ih : ∀ (B : Finset V) (Q' : V → ZMod 2) (e' : ℕ), AffSet B → IsQuad Q' →
      2 ^ (2 * S.card + e') ≤ (B.image (pat f S)).card →
      4 ^ e' * |∑ a ∈ B, sgn (G a + Q' a)| ≤ 3 ^ e' * (B.card : ℤ))
    (hrank : 2 ^ (2 * S.card + e) ≤ (A.image (pat f S)).card) {e0 e1 e2 : V}
    (h0 : IsShift f S i A (Pi.single 0 1) e0) (h1 : IsShift f S i A (Pi.single 1 1) e1)
    (h2' : IsShift f S i A (Pi.single 2 1) e2) :
    4 ^ (e + 1) * |∑ a ∈ A, sgn (f i 0 a * f i 1 a * f i 2 a + G a + Q a)| ≤
      3 ^ (e + 1) * (A.card : ℤ) := by

  have hDaff : IsAff (fun a => Q a + Q (a + e0)) := hQ.deriv h2 e0
  have hcancel : ∀ a : V, a + e0 + e0 = a := fun a => by rw [add_assoc, h2, add_zero]
  have step1 : ∑ a ∈ A, sgn (f i 0 a * f i 1 a * f i 2 a + G a + Q a) =
      2 * ∑ a ∈ (A.filter (fun a => f i 0 a = 0)).filter
        (fun a => f i 1 a * f i 2 a = Q a + Q (a + e0)), sgn (G a + Q a) := by
    have hmove : ∑ a ∈ A.filter (fun a => f i 0 a = 0),
          sgn (f i 0 (a + e0) * f i 1 (a + e0) * f i 2 (a + e0) + G (a + e0) + Q (a + e0)) =
        ∑ a ∈ A.filter (fun a => f i 0 a = 1), sgn (f i 0 a * f i 1 a * f i 2 a + G a + Q a) := by
      refine Finset.sum_nbij' (· + e0) (· + e0) ?_ ?_ (fun a _ => hcancel a)
        (fun a _ => hcancel a) (fun a _ => rfl)
      · intro a ha
        rw [Finset.mem_filter] at ha ⊢
        exact ⟨h0.1 a ha.1, by rw [h0.flip, ha.2, zero_add]⟩
      · intro a ha
        rw [Finset.mem_filter] at ha ⊢
        exact ⟨h0.1 a ha.1, by rw [h0.flip, ha.2]; rfl⟩
    rw [sum_split_z2 A (f i 0), ← hmove, ← Finset.sum_add_distrib, Finset.mul_sum,
      Finset.sum_filter (fun a => f i 1 a * f i 2 a = Q a + Q (a + e0))]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [h0.flip, h0.keep (by decide : (1 : Fin 3) ≠ 0), h0.keep (by decide : (2 : Fin 3) ≠ 0),
      hG _ _ (h0.2.1 a), (Finset.mem_filter.mp ha).2, zero_mul, zero_mul, zero_add, zero_add,
      one_mul]
    generalize f i 1 a * f i 2 a = y
    generalize G a = γ
    generalize Q a = q
    generalize Q (a + e0) = q'
    revert y γ q q'
    decide

  obtain ⟨κ1, hκ1⟩ : ∃ κ, ∀ a, Q (a + e1) + Q (a + e1 + e0) = Q a + Q (a + e0) + κ :=
    ⟨Q e1 + Q (e1 + e0) + (Q 0 + Q (0 + e0)), fun a => by
      have := hDaff a e1 0
      simp only [add_zero] at this
      linear_combination this⟩
  obtain ⟨κ2, hκ2⟩ : ∃ κ, ∀ a, Q (a + e2) + Q (a + e2 + e0) = Q a + Q (a + e0) + κ :=
    ⟨Q e2 + Q (e2 + e0) + (Q 0 + Q (0 + e0)), fun a => by
      have := hDaff a e2 0
      simp only [add_zero] at this
      linear_combination this⟩
  obtain ⟨Dp, hDp⟩ : ∃ Dp : V → ZMod 2,
      ∀ a, Dp a = Q a + Q (a + e0) + κ1 * f i 1 a + κ2 * f i 2 a := ⟨_, fun _ => rfl⟩
  have hDpaff : IsAff Dp := by
    have := (hDaff.add ((hf i 1).const_mul κ1)).add ((hf i 2).const_mul κ2)
    rwa [show Dp = _ from funext hDp]
  have hDp1 : ∀ a, Dp (a + e1) = Dp a := fun a => by
    rw [hDp, hDp, hκ1, h1.flip, h1.keep (by decide : (2 : Fin 3) ≠ 1)]
    linear_combination κ1 * z2_two
  have hDp2 : ∀ a, Dp (a + e2) = Dp a := fun a => by
    rw [hDp, hDp, hκ2, h2'.flip, h2'.keep (by decide : (1 : Fin 3) ≠ 2)]
    linear_combination κ2 * z2_two

  obtain ⟨A0, hA0⟩ : ∃ A0, A0 = A.filter (fun a => f i 0 a = 0) := ⟨_, rfl⟩
  have hA0aff : AffSet A0 := hA0 ▸ hA.filter (hf i 0) 0
  have hA0card : 2 * A0.card = A.card := hA0 ▸ card_filter_of_flip h2 A (f i 0) e0 h0.1 h0.flip 0
  have hA0img : A0.image (pat f S) = A.image (pat f S) :=
    hA0 ▸ image_pat_filter_of_flip f S h0.1 h0.flip h0.2.1 0
  have hA0mem : ∀ a, a ∈ A0 ↔ a ∈ A ∧ f i 0 a = 0 := fun a => by rw [hA0, Finset.mem_filter]
  obtain ⟨R, hR⟩ : ∃ R : ZMod 2 → Finset V, ∀ c, R c = A0.filter (fun a => Dp a = c) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ZMod 2 → ZMod 2 → ZMod 2 → Finset V, ∀ c β γ,
      P c β γ = ((R c).filter (fun a => f i 1 a = β)).filter (fun a => f i 2 a = γ) :=
    ⟨_, fun _ _ _ => rfl⟩
  have hRaff : ∀ c, AffSet (R c) := fun c => by
    rw [hR]
    exact hA0aff.filter hDpaff c
  have hRinv : ∀ (c : ZMod 2) {c' : Fin 3} {e' : V}, IsShift f S i A (Pi.single c' 1) e' →
      c' ≠ 0 → (∀ a, Dp (a + e') = Dp a) → ∀ a ∈ R c, a + e' ∈ R c :=
    fun c c' e' hs hc hd a ha => by
    rw [hR, Finset.mem_filter, hA0mem] at ha ⊢
    exact ⟨⟨hs.1 a ha.1.1, (hs.keep hc.symm a).trans ha.1.2⟩, (hd a).trans ha.2⟩
  have hquarter : ∀ c β γ : ZMod 2, 4 * (P c β γ).card = (R c).card ∧
      (P c β γ).image (pat f S) = (R c).image (pat f S) ∧ AffSet (P c β γ) := by
    intro c β γ
    have hi1 := hRinv c h1 (by decide) hDp1
    have hi2 : ∀ a ∈ (R c).filter (fun a => f i 1 a = β),
        a + e2 ∈ (R c).filter (fun a => f i 1 a = β) := fun a ha => by
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨hRinv c h2' (by decide) hDp2 a ha.1,
        (h2'.keep (by decide : (1 : Fin 3) ≠ 2) a).trans ha.2⟩
    have c1 := card_filter_of_flip h2 _ (f i 1) e1 hi1 h1.flip β
    have c2 := card_filter_of_flip h2 _ (f i 2) e2 hi2 h2'.flip γ
    rw [hP]
    refine ⟨by omega, ?_, ((hRaff c).filter (hf i 1) β).filter (hf i 2) γ⟩
    rw [image_pat_filter_of_flip f S hi2 h2'.flip h2'.2.1 γ,
      image_pat_filter_of_flip f S hi1 h1.flip h1.2.1 β]

  have hcut : ∀ β γ : ZMod 2,
      ((A0.filter (fun a => f i 1 a * f i 2 a = Q a + Q (a + e0))).filter
        (fun a => f i 1 a = β)).filter (fun a => f i 2 a = γ) =
      P (β * γ + κ1 * β + κ2 * γ) β γ := by
    intro β γ
    rw [hP, hR]
    ext a
    simp only [Finset.mem_filter, hDp]
    constructor
    · rintro ⟨⟨⟨ha, hq⟩, hy⟩, hz⟩
      exact ⟨⟨⟨ha, by rw [← hq, hy, hz]⟩, hy⟩, hz⟩
    · rintro ⟨⟨⟨ha, hq⟩, hy⟩, hz⟩
      rw [hy, hz] at hq
      exact ⟨⟨⟨ha, by rw [hy, hz]; exact (add_right_cancel (add_right_cancel hq)).symm⟩, hy⟩, hz⟩
  obtain ⟨T, hT⟩ : ∃ T : ZMod 2 → ZMod 2 → ℤ, ∀ β γ,
      T β γ = |∑ a ∈ P (β * γ + κ1 * β + κ2 * γ) β γ, sgn (G a + Q a)| := ⟨_, fun _ _ => rfl⟩
  have hsum : |∑ a ∈ A, sgn (f i 0 a * f i 1 a * f i 2 a + G a + Q a)| ≤
      2 * (T 0 0 + T 0 1 + (T 1 0 + T 1 1)) := by
    rw [step1, ← hA0, abs_mul, abs_two, sum_split_z2 _ (f i 1),
      sum_split_z2 (A0.filter _ |>.filter (fun a => f i 1 a = 0)) (f i 2),
      sum_split_z2 (A0.filter _ |>.filter (fun a => f i 1 a = 1)) (f i 2),
      hcut, hcut, hcut, hcut, hT, hT, hT, hT]
    exact mul_le_mul_of_nonneg_left
      ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))) (by norm_num)

  have hfull : ∀ c : ZMod 2, R (c + 1) = ∅ → ∀ β γ : ZMod 2,
      6 * 4 ^ (e + 1) * |∑ a ∈ P c β γ, sgn (G a + Q a)| ≤ 3 ^ (e + 1) * (A.card : ℤ) := by
    intro c hc β γ
    obtain ⟨q4, qimg, qaff⟩ := hquarter c β γ
    have hRc : R c = A0 := by
      rw [hR]
      refine Finset.filter_true_of_mem fun a ha => ?_
      by_contra hne
      have hmem : a ∈ R (c + 1) := by
        rw [hR]
        exact Finset.mem_filter.mpr ⟨ha, z2_eq_add_one hne⟩
      rw [hc] at hmem
      exact absurd hmem (Finset.notMem_empty a)
    rw [hRc] at q4 qimg
    have hb := ih _ Q e qaff hQ (by rw [qimg, hA0img]; exact hrank)
    have hcard : (A.card : ℤ) = 8 * ((P c β γ).card : ℤ) := by
      exact_mod_cast (by omega : A.card = 8 * (P c β γ).card)
    rw [hcard, pow_succ, pow_succ]
    linarith

  have hhalf : (R 0).Nonempty → (R 1).Nonempty → ∀ c β γ : ZMod 2,
      9 * 4 ^ (e + 1) * |∑ a ∈ P c β γ, sgn (G a + Q a)| ≤ 3 ^ (e + 1) * (A.card : ℤ) := by
    rintro ⟨p0, hp0⟩ ⟨p1, hp1⟩ c β γ
    rw [hR, Finset.mem_filter] at hp0 hp1
    obtain ⟨q4, qimg, qaff⟩ := hquarter c β γ
    have hRcard : 2 * (R c).card = A0.card := by
      rw [hR]
      exact card_filter_of_flip h2 A0 Dp (p0 + p1)
        (fun a ha => by rw [← add_assoc]; exact hA0aff a ha p0 hp0.1 p1 hp1.1)
        (fun a => by rw [← add_assoc, hDpaff, hp0.2, hp1.2, add_zero]) c
    have hne : (A0.filter (fun a => Dp a = c)).Nonempty := by
      rcases z2_cases c with rfl | rfl
      · exact ⟨p0, Finset.mem_filter.mpr hp0⟩
      · exact ⟨p1, Finset.mem_filter.mpr hp1⟩
    have himg := card_pat_le_two_mul f hf S hA0aff hDpaff c hne
    rw [hA0img, ← hR, ← qimg] at himg
    have hcard : (A.card : ℤ) = 16 * ((P c β γ).card : ℤ) := by
      exact_mod_cast (by omega : A.card = 16 * (P c β γ).card)
    rw [hcard]
    cases e with
    | zero =>
      have hb := abs_sum_sgn_le (P c β γ) (fun a => G a + Q a)
      have hq0 : (0 : ℤ) ≤ ((P c β γ).card : ℤ) := Nat.cast_nonneg _
      rw [zero_add, pow_one, pow_one]
      linarith
    | succ e' =>
      have hpow : 2 ^ (2 * S.card + (e' + 1)) = 2 * 2 ^ (2 * S.card + e') := by
        rw [← add_assoc, pow_succ, mul_comm]
      have hb := ih _ Q e' qaff hQ (by omega)
      rw [pow_succ, pow_succ, pow_succ, pow_succ]
      linarith

  have hW : (0 : ℤ) ≤ 4 ^ (e + 1) := by positivity
  have hRR : (0 : ℤ) ≤ 3 ^ (e + 1) * (A.card : ℤ) := by positivity
  suffices hfin : 4 ^ (e + 1) * (2 * (T 0 0 + T 0 1 + (T 1 0 + T 1 1))) ≤
      3 ^ (e + 1) * (A.card : ℤ) from (mul_le_mul_of_nonneg_left hsum hW).trans hfin
  have hconst : ∀ c0 : ZMod 2, R (c0 + 1) = ∅ →
      4 ^ (e + 1) * (2 * (T 0 0 + T 0 1 + (T 1 0 + T 1 1))) ≤ 3 ^ (e + 1) * (A.card : ℤ) := by
    intro c0 hc0
    have hall : ∀ β γ : ZMod 2, 6 * 4 ^ (e + 1) * T β γ ≤ 3 ^ (e + 1) * (A.card : ℤ) ∧
        (β * γ + κ1 * β + κ2 * γ = c0 + 1 → T β γ = 0) := by
      intro β γ
      by_cases hc : β * γ + κ1 * β + κ2 * γ = c0
      · exact ⟨by rw [hT, hc]; exact hfull c0 hc0 β γ,
          fun h => absurd (hc.symm.trans h) (z2_ne_add_one c0)⟩
      · have hz : T β γ = 0 := by
          rw [hT, z2_eq_add_one hc, hP, hc0, Finset.filter_empty, Finset.filter_empty,
            Finset.sum_empty, abs_zero]
        exact ⟨by rw [hz, mul_zero]; exact hRR, fun _ => hz⟩
    obtain ⟨β0, γ0, hne⟩ := z2_quadric_hits κ1 κ2 (c0 + 1)
    have hz : 4 ^ (e + 1) * T β0 γ0 = 0 := by rw [(hall β0 γ0).2 hne, mul_zero]
    have h00 := (hall 0 0).1
    have h01 := (hall 0 1).1
    have h10 := (hall 1 0).1
    have h11 := (hall 1 1).1
    rcases z2_cases β0 with rfl | rfl <;> rcases z2_cases γ0 with rfl | rfl <;> linarith
  rcases (R 0).eq_empty_or_nonempty with h0e | h0n
  · exact hconst 1 h0e
  rcases (R 1).eq_empty_or_nonempty with h1e | h1n
  · exact hconst 0 (by rw [zero_add]; exact h1e)
  · have hh := hhalf h0n h1n
    have h00 := hh (0 * 0 + κ1 * 0 + κ2 * 0) 0 0
    have h01 := hh (0 * 1 + κ1 * 0 + κ2 * 1) 0 1
    have h10 := hh (1 * 0 + κ1 * 1 + κ2 * 0) 1 0
    have h11 := hh (1 * 1 + κ1 * 1 + κ2 * 1) 1 1
    rw [← hT] at h00 h01 h10 h11
    linarith

lemma corr_bound {V : Type*} [AddCommGroup V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h2 : ∀ v : V, v + v = 0) (f : ι → Fin 3 → V → ZMod 2) (hf : ∀ i j, IsAff (f i j))
    (S : Finset ι) (A : Finset V) (Q : V → ZMod 2) (e : ℕ) (hA : AffSet A) (hQ : IsQuad Q)
    (hrank : 2 ^ (2 * S.card + e) ≤ (A.image (pat f S)).card) :
    4 ^ e * |∑ a ∈ A, sgn (∑ i ∈ S, cube f i a + Q a)| ≤ 3 ^ e * (A.card : ℤ) := by
  induction S using Finset.induction_on generalizing A Q e with
  | empty =>
    have h1 : (A.image (pat f ∅)).card ≤ 1 := Finset.card_le_one.mpr fun x hx y hy => by
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
      rfl
    have he : e = 0 := by
      by_contra hne
      have := Nat.pow_le_pow_right (n := 2) two_pos (Nat.one_le_iff_ne_zero.mpr hne)
      rw [Finset.card_empty, mul_zero, zero_add] at hrank
      omega
    subst he
    simpa using abs_sum_sgn_le A _
  | insert i S hi ih =>
    rcases Nat.eq_zero_or_pos e with rfl | hepos
    · simpa using abs_sum_sgn_le A _
    rw [Finset.card_insert_of_notMem hi] at hrank
    have hsum : ∀ a, ∑ j ∈ insert i S, cube f j a =
        f i 0 a * f i 1 a * f i 2 a + ∑ j ∈ S, cube f j a := fun a => Finset.sum_insert hi
    simp only [hsum]
    classical

    let U : Finset (Fin 3 → ZMod 2) := Finset.univ.filter (fun u => ∃ e', IsShift f S i A u e')
    have hUmem : ∀ a1 ∈ A, ∀ a2 ∈ A, pat f S a1 = pat f S a2 →
        (fun j => f i j a1 + f i j a2) ∈ U := fun a1 h1 a2 h2' h =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, _, isShift_of_pair hf S i hA h1 h2' h⟩
    have hT := card_pat_insert_le hi U hUmem
    have h8 : Fintype.card (Fin 3 → ZMod 2) = 8 := by
      simp [ZMod.card]
    have ih' : ∀ (B : Finset V) (Q' : V → ZMod 2) (e' : ℕ), AffSet B → IsQuad Q' →
        2 ^ (2 * S.card + e') ≤ (B.image (pat f S)).card →
        4 ^ e' * |∑ a ∈ B, sgn (∑ j ∈ S, cube f j a + Q' a)| ≤ 3 ^ e' * (B.card : ℤ) :=
      fun B Q' e' hB hQ' hr => ih B Q' e' hB hQ' hr
    by_cases hfull : ∀ u, u ∈ U
    ·
      obtain ⟨e0, h0⟩ := (Finset.mem_filter.mp (hfull (Pi.single 0 1))).2
      obtain ⟨e1, h1⟩ := (Finset.mem_filter.mp (hfull (Pi.single 1 1))).2
      obtain ⟨e2, h2'⟩ := (Finset.mem_filter.mp (hfull (Pi.single 2 1))).2
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      have hU8 : U.card ≤ 8 := h8 ▸ Finset.card_le_univ U
      have hr : 2 ^ (2 * S.card + e') ≤ (A.image (pat f S)).card := by
        have hpow : 2 ^ (2 * (S.card + 1) + (e' + 1)) = 8 * 2 ^ (2 * S.card + e') := by ring
        have := Nat.mul_le_mul_right (A.image (pat f S)).card hU8
        omega
      exact corr_peel h2 hf hA hQ (fun a b h => sum_cube_eq_of_pat f h) ih' hr h0 h1 h2'
    ·
      simp only [not_forall] at hfull
      obtain ⟨w, hw⟩ := hfull
      have hUadd : ∀ u ∈ U, ∀ u' ∈ U, u + u' ∈ U := fun u hu u' hu' => by
        obtain ⟨e1, h1⟩ := (Finset.mem_filter.mp hu).2
        obtain ⟨e2, h2'⟩ := (Finset.mem_filter.mp hu').2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, _, h1.add h2'⟩
      have hU4 : U.card ≤ 4 := by
        have hdisj : Disjoint U (U.image (· + w)) := Finset.disjoint_left.mpr fun u hu hu' => by
          obtain ⟨u', hu'', rfl⟩ := Finset.mem_image.mp hu'
          have := hUadd _ hu _ hu''
          rw [add_comm u' w, add_assoc, z2fun_add_self, add_zero] at this
          exact hw this
        have hc := Finset.card_union_of_disjoint hdisj
        rw [Finset.card_image_of_injective _ (add_left_injective w)] at hc
        have := Finset.card_le_univ (U ∪ U.image (· + w))
        omega
      have hpow : 2 ^ (2 * (S.card + 1) + e) = 4 * 2 ^ (2 * S.card + e) := by ring
      have hr : 2 ^ (2 * S.card + e) ≤ (A.image (pat f S)).card := by
        have := Nat.mul_le_mul_right (A.image (pat f S)).card hU4
        omega
      have hmove : ∀ c : Fin 3, (∃ u ∈ U, u c = 1) → ∀ v : ZMod 2,
          2 ^ (2 * S.card + e) ≤ ((A.filter (fun a => f i c a = v)).image (pat f S)).card := by
        rintro c ⟨u, hu, huc⟩ v
        obtain ⟨e', hs⟩ := (Finset.mem_filter.mp hu).2
        rw [image_pat_filter_of_flip f S hs.1 (fun a => by rw [hs.2.2, huc]) hs.2.1 v]
        exact hr
      by_cases hs0 : ∃ u ∈ U, u 0 = 1
      · exact split_bound (hf i 0) (hf i 1) (hf i 2) hQ hA
          (fun B => 2 ^ (2 * S.card + e) ≤ (B.image (pat f S)).card)
          (fun B Q' hB hQ' hH => ih' B Q' e hB hQ' hH) (fun v _ => hmove 0 hs0 v)
      by_cases hs1 : ∃ u ∈ U, u 1 = 1
      · have hcomm : ∀ a, f i 0 a * f i 1 a * f i 2 a = f i 1 a * f i 0 a * f i 2 a :=
          fun a => by ring
        simp only [hcomm]
        exact split_bound (hf i 1) (hf i 0) (hf i 2) hQ hA
          (fun B => 2 ^ (2 * S.card + e) ≤ (B.image (pat f S)).card)
          (fun B Q' hB hQ' hH => ih' B Q' e hB hQ' hH) (fun v _ => hmove 1 hs1 v)
      ·
        simp only [not_exists, not_and] at hs0 hs1
        have hU2 : U.card ≤ 2 := by
          refine (Finset.card_le_card_of_injOn (fun u => u 2) (fun u _ => Finset.mem_univ _)
            fun u hu u' hu' h => ?_).trans (by simp [ZMod.card])
          funext j
          fin_cases j
          · exact (z2_cases (u 0)).resolve_right (hs0 u hu) |>.trans
              ((z2_cases (u' 0)).resolve_right (hs0 u' hu')).symm
          · exact (z2_cases (u 1)).resolve_right (hs1 u hu) |>.trans
              ((z2_cases (u' 1)).resolve_right (hs1 u' hu')).symm
          · exact h
        have hr2 : 2 * 2 ^ (2 * S.card + e) ≤ (A.image (pat f S)).card := by
          have := Nat.mul_le_mul_right (A.image (pat f S)).card hU2
          omega
        exact split_bound (hf i 0) (hf i 1) (hf i 2) hQ hA
          (fun B => 2 ^ (2 * S.card + e) ≤ (B.image (pat f S)).card)
          (fun B Q' hB hQ' hH => ih' B Q' e hB hQ' hH) (fun v hne => by
            have := card_pat_le_two_mul f hf S hA (hf i 0) v hne
            omega)

lemma card_cube_eq_one {V : Type*} [AddCommGroup V] {ι : Type*} [DecidableEq ι]
    (h2 : ∀ v : V, v + v = 0) (f : ι → Fin 3 → V → ZMod 2) (ε : ι → Fin 3 → V)
    (hflip : ∀ i j i' j' a, f i' j' (a + ε i j) = f i' j' a + if i' = i ∧ j' = j then 1 else 0)
    (i : ι) (A : Finset V) (hA : ∀ j, ∀ a ∈ A, a + ε i j ∈ A) :
    8 * (A.filter fun a => cube f i a = 1).card = A.card := by
  have hkeep : ∀ j c a, c ≠ j → f i c (a + ε i j) = f i c a := fun j c a h => by
    rw [hflip, ite_eq_right (fun h' => h h'.2), add_zero]
  have hmove : ∀ j a, f i j (a + ε i j) = f i j a + 1 := fun j a => by
    rw [hflip, ite_eq_left ⟨rfl, rfl⟩]
  have hz : ∀ x y z : ZMod 2, x * y * z = 1 ↔ x = 1 ∧ y = 1 ∧ z = 1 := by decide
  have hset : (A.filter fun a => cube f i a = 1) =
      ((A.filter fun a => f i 0 a = 1).filter fun a => f i 1 a = 1).filter
        fun a => f i 2 a = 1 := by
    ext a
    simp only [Finset.mem_filter, cube, hz, and_assoc]
  have h0 := card_filter_of_flip h2 A (f i 0) (ε i 0) (hA 0) (hmove 0) 1
  have h1 := card_filter_of_flip h2 (A.filter fun a => f i 0 a = 1) (f i 1) (ε i 1)
    (fun a ha => by
      rw [Finset.mem_filter] at ha ⊢
      exact ⟨hA 1 a ha.1, (hkeep 1 0 a (by decide)).trans ha.2⟩) (hmove 1) 1
  have h2' := card_filter_of_flip h2 ((A.filter fun a => f i 0 a = 1).filter fun a => f i 1 a = 1)
    (f i 2) (ε i 2)
    (fun a ha => by
      simp only [Finset.mem_filter] at ha ⊢
      exact ⟨⟨hA 2 a ha.1.1, (hkeep 2 0 a (by decide)).trans ha.1.2⟩,
        (hkeep 2 1 a (by decide)).trans ha.2⟩) (hmove 2) 1
  rw [hset]
  omega

lemma exact_count {V : Type*} [AddCommGroup V] {ι : Type*} [DecidableEq ι]
    (h2 : ∀ v : V, v + v = 0) (f : ι → Fin 3 → V → ZMod 2) (ε : ι → Fin 3 → V)
    (hflip : ∀ i j i' j' a, f i' j' (a + ε i j) = f i' j' a + if i' = i ∧ j' = j then 1 else 0)
    (S : Finset ι) (A : Finset V) (hA : ∀ i ∈ S, ∀ j, ∀ a ∈ A, a + ε i j ∈ A) :
    4 ^ S.card * ∑ a ∈ A, sgn (∑ i ∈ S, cube f i a) = 3 ^ S.card * (A.card : ℤ) := by
  induction S using Finset.induction_on generalizing A with
  | empty => simp [sgn]
  | insert i S hi ih =>
    have h8 : (8 : ℤ) * ((A.filter fun a => cube f i a = 1).card : ℤ) = A.card := by
      exact_mod_cast card_cube_eq_one h2 f ε hflip i A (hA i (Finset.mem_insert_self i S))
    have e1 := ih A fun i' hi' => hA i' (Finset.mem_insert_of_mem hi')
    have e2 := ih (A.filter fun a => cube f i a = 1) fun i' hi' j a ha => by
      have hne : ¬i = i' := fun h => hi (h ▸ hi')
      rw [Finset.mem_filter] at ha ⊢
      refine ⟨hA i' (Finset.mem_insert_of_mem hi') j a ha.1, ?_⟩
      simpa only [cube, hflip, hne, false_and, ite_false, add_zero] using ha.2
    have hsum : ∑ a ∈ A, sgn (∑ x ∈ insert i S, cube f x a) =
        ∑ a ∈ A, sgn (∑ x ∈ S, cube f x a) -
          2 * ∑ a ∈ A.filter (fun a => cube f i a = 1), sgn (∑ x ∈ S, cube f x a) := by
      rw [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_insert hi]
      generalize cube f i a = c
      generalize ∑ x ∈ S, cube f x a = g
      revert c g
      decide
    rw [hsum, Finset.card_insert_of_notMem hi, pow_succ, pow_succ]
    linear_combination 4 * e1 - 8 * e2 - 3 ^ S.card * h8

def form {k m : ℕ} (idx : Fin m → Fin 3 → Fin k) (s : Fin m → Fin 3 → Bool) :
    Fin m → Fin 3 → (Fin k → ZMod 2) → ZMod 2 := fun i j v => v (idx i j) + z2 (s i j)

def affPart {k m : ℕ} (idx : Fin m → Fin 3 → Fin k) (c0 : Fin m → Bool) (l : Fin m → Fin 3 → Bool)
    (i : Fin m) (v : Fin k → ZMod 2) : ZMod 2 := z2 (c0 i) + ∑ j : Fin 3, z2 (l i j) * v (idx i j)

lemma z2_target {k m : ℕ} (idx : Fin m → Fin 3 → Fin k) (s l : Fin m → Fin 3 → Bool)
    (c0 : Fin m → Bool) (out : Fin (2 ^ k) → Fin m → Bool) (active : Finset (Fin m))
    (q : Fin (2 ^ k))
    (hout : ∀ i, out q i = winOut (fun j => q.val.testBit (idx i j).val) (s i) (l i) (c0 i)) :
    z2 (par (∑ i ∈ active, (out q i).toNat)) =
      ∑ i ∈ active, (cube (form idx s) i (vec k q) + affPart idx c0 l i (vec k q)) := by
  rw [z2_par_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hout, z2_winOut]
  rfl

lemma mem_map_fiber {k : ℕ} {fiber : Finset (Fin (2 ^ k))} {P : Finset (Fin k)}
    {ref : Fin (2 ^ k)}
    (hfib : ∀ q, q ∈ fiber ↔ ∀ z ∈ P, q.val.testBit z.val = ref.val.testBit z.val)
    (v : Fin k → ZMod 2) :
    v ∈ fiber.map (vecEquiv k).toEmbedding ↔ ∀ z ∈ P, v z = vec k ref z := by
  have hv : ∀ z, z2 (((vecEquiv k).symm v).val.testBit z.val) = v z := congrFun (vec_symm k v)
  rw [Finset.mem_map_equiv, hfib]
  refine forall₂_congr fun z _ => ⟨fun h => ?_, fun h => z2_inj ((hv z).trans h)⟩
  rw [← hv z, h]
  rfl

lemma coord_isAff {k : ℕ} (z : Fin k) : IsAff (fun v : Fin k → ZMod 2 => v z) :=
  fun _ _ _ => rfl

lemma form_isAff {k m : ℕ} (idx : Fin m → Fin 3 → Fin k) (s : Fin m → Fin 3 → Bool)
    (i : Fin m) (j : Fin 3) : IsAff (form idx s i j) :=
  IsAff.add (coord_isAff (idx i j)) (IsAff.const (z2 (s i j)))

lemma lin_isAff {k : ℕ} (mask : Fin k → Bool) :
    IsAff (fun v : Fin k → ZMod 2 => ∑ i, z2 (mask i) * v i) :=
  IsAff.sum _ _ fun i _ => IsAff.const_mul _ (coord_isAff i)

lemma affPart_isAff {k m : ℕ} (idx : Fin m → Fin 3 → Fin k) (c0 : Fin m → Bool)
    (l : Fin m → Fin 3 → Bool) (i : Fin m) : IsAff (affPart idx c0 l i) :=
  IsAff.add (IsAff.const (z2 (c0 i)))
    (IsAff.sum Finset.univ (fun j (v : Fin k → ZMod 2) => z2 (l i j) * v (idx i j))
      fun j _ => IsAff.const_mul _ (coord_isAff (idx i j)))

lemma QuadForm.isQuad {k : ℕ} {G : (Fin k → ZMod 2) → ZMod 2} (hG : QuadForm k G) :
    IsQuad G := by
  obtain ⟨β, l, α, h⟩ := hG
  rw [show G = fun v => β + ∑ i, l i * v i + ∑ i, ∑ j, α i j * v i * v j from funext h]
  exact IsQuad.add
    (IsQuad.add (IsAff.isQuad (IsAff.const β))
      (IsQuad.sum _ _ fun i _ => IsAff.isQuad (IsAff.const_mul (l i) (coord_isAff i))))
    (IsQuad.sum _ _ fun i _ => IsQuad.sum _ _ fun j _ =>
      IsAff.mul (IsAff.const_mul (α i j) (coord_isAff i)) (coord_isAff j))

lemma affSet_of_fixed {k : ℕ} (A : Finset (Fin k → ZMod 2)) (P : Finset (Fin k))
    (r : Fin k → ZMod 2) (hA : ∀ v, v ∈ A ↔ ∀ z ∈ P, v z = r z) : AffSet A := by
  intro a ha b hb c hc
  rw [hA] at ha hb hc ⊢
  intro z hz
  rw [Pi.add_apply, Pi.add_apply, ha z hz, hb z hz, hc z hz, z2_add_self, zero_add]

lemma exists_block_values {k m : ℕ} (P : Finset (Fin k)) (r : Fin k → ZMod 2)
    (idx : Fin m → Fin 3 → Fin k) (hidx : ∀ i j i' j', idx i j = idx i' j' → i = i' ∧ j = j')
    (hP : ∀ i j, idx i j ∉ P) (s : Fin m → Fin 3 → Bool) (p : Fin m → Fin 3 → ZMod 2) :
    ∃ v : Fin k → ZMod 2, (∀ z ∈ P, v z = r z) ∧ ∀ i j, form idx s i j v = p i j := by
  have hinj : Function.Injective (fun ij : Fin m × Fin 3 => idx ij.1 ij.2) := fun a b h =>
    Prod.ext (hidx _ _ _ _ h).1 (hidx _ _ _ _ h).2
  refine ⟨Function.extend (fun ij : Fin m × Fin 3 => idx ij.1 ij.2)
    (fun ij => p ij.1 ij.2 + z2 (s ij.1 ij.2)) r, fun z hz => ?_, fun i j => ?_⟩
  · exact Function.extend_apply' _ _ _ fun ⟨ij, h⟩ => hP ij.1 ij.2 (h ▸ hz)
  · have h : Function.extend (fun ij : Fin m × Fin 3 => idx ij.1 ij.2)
        (fun ij => p ij.1 ij.2 + z2 (s ij.1 ij.2)) r (idx i j) = p i j + z2 (s i j) :=
      hinj.extend_apply _ r (i, j)
    show Function.extend _ _ r (idx i j) + z2 (s i j) = p i j
    rw [h, add_assoc, z2_add_self, add_zero]

lemma card_pat_fiber {k m : ℕ} (A : Finset (Fin k → ZMod 2)) (P : Finset (Fin k))
    (r : Fin k → ZMod 2) (hA : ∀ v, v ∈ A ↔ ∀ z ∈ P, v z = r z)
    (idx : Fin m → Fin 3 → Fin k) (hidx : ∀ i j i' j', idx i j = idx i' j' → i = i' ∧ j = j')
    (hP : ∀ i j, idx i j ∉ P) (s : Fin m → Fin 3 → Bool) (active : Finset (Fin m)) :
    8 ^ active.card ≤ (A.image (pat (form idx s) active)).card := by
  have hcard : (Finset.univ : Finset (↥active → Fin 3 → ZMod 2)).card = 8 ^ active.card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin,
      Fintype.card_coe]
    norm_num
  rw [← hcard]
  refine Finset.card_le_card_of_injOn
    (fun p i j => if h : i ∈ active then p ⟨i, h⟩ j else 0) (fun p _ => ?_) (fun p _ p' _ h => ?_)
  · obtain ⟨v, hv, hform⟩ := exists_block_values P r idx hidx hP s
      (fun i j => if h : i ∈ active then p ⟨i, h⟩ j else 0)
    refine Finset.mem_image.mpr ⟨v, (hA v).mpr hv, ?_⟩
    funext i j
    by_cases hi : i ∈ active <;> simp only [pat, hi, hform, ↓reduceIte, ↓reduceDIte]
  · funext ⟨i, hi⟩ j
    simpa only [hi, ↓reduceDIte] using congrFun (congrFun h i) j

lemma affSet_cut {V : Type*} [AddCommGroup V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → Fin 3 → V → ZMod 2) (hf : ∀ i j, IsAff (f i j)) (S : Finset ι) {A : Finset V}
    (hA : AffSet A) (g : ℕ → V → ZMod 2) (hg : ∀ t, IsAff (g t)) (c : ℕ → ZMod 2) (n : ℕ) :
    AffSet (A.filter (fun a => ∀ t < n, g t a = c t)) ∧
      ((A.filter (fun a => ∀ t < n, g t a = c t)).Nonempty →
        (A.image (pat f S)).card ≤
          2 ^ n * ((A.filter (fun a => ∀ t < n, g t a = c t)).image (pat f S)).card) := by
  induction n with
  | zero =>
    rw [Finset.filter_true_of_mem fun a _ t ht => absurd ht (Nat.not_lt_zero t)]
    exact ⟨hA, fun _ => by rw [pow_zero, one_mul]⟩
  | succ n ih =>
    have hstep : A.filter (fun a => ∀ t < n + 1, g t a = c t) =
        (A.filter (fun a => ∀ t < n, g t a = c t)).filter (fun a => g n a = c n) := by
      rw [Finset.filter_filter]
      exact Finset.filter_congr fun a _ => Nat.forall_lt_succ_right
    rw [hstep]
    refine ⟨ih.1.filter (hg n) (c n), fun hne => ?_⟩
    calc (A.image (pat f S)).card
        ≤ 2 ^ n * ((A.filter (fun a => ∀ t < n, g t a = c t)).image (pat f S)).card :=
          ih.2 (hne.mono (Finset.filter_subset _ _))
      _ ≤ 2 ^ n * (2 * _) :=
          Nat.mul_le_mul_left _ (card_pat_le_two_mul f hf S ih.1 (hg n) (c n) hne)
      _ = 2 ^ (n + 1) * _ := by ring

lemma runP_eq_iff (k d : ℕ) (choose : ℕ → ℕ → Fin k → Bool) (q : Fin (2 ^ k)) (h : ℕ)
    (hh : h < 2 ^ d) :
    runP k d choose q = h ↔
      ∀ t < d, ∑ i, z2 (choose t (h % 2 ^ t) i) * vec k q i = z2 (h.testBit t) := by
  rw [runP_eq, stepRun_eq_iff _ q d h hh]
  exact ⟨fun H t ht => (z2_lin k _ q).symm.trans (congrArg z2 (H ⟨t, ht⟩)),
    fun H u => z2_inj ((z2_lin k _ q).trans (H u.val u.isLt))⟩

lemma leaf_bound {k m : ℕ} (idx : Fin m → Fin 3 → Fin k) (s l : Fin m → Fin 3 → Bool)
    (c0 : Fin m → Bool) (out : Fin (2 ^ k) → Fin m → Bool) (active : Finset (Fin m)) (e : ℕ)
    (L : Finset (Fin (2 ^ k))) (g : Fin (2 ^ k) → Bool) (hg : quadP k g)
    (hout : ∀ q ∈ L, ∀ i,
      out q i = winOut (fun j => q.val.testBit (idx i j).val) (s i) (l i) (c0 i))
    (hL : AffSet (L.map (vecEquiv k).toEmbedding))
    (hrank : L.Nonempty → 2 ^ (2 * active.card + e) ≤
      ((L.map (vecEquiv k).toEmbedding).image (pat (form idx s) active)).card) :
    4 ^ e * (2 * (L.filter (fun q => g q == par (∑ i ∈ active, (out q i).toNat))).card) ≤
      (4 ^ e + 3 ^ e) * L.card := by
  rcases L.eq_empty_or_nonempty with rfl | hne
  · simp
  have hQ : IsQuad (fun v => z2 (g ((vecEquiv k).symm v)) + ∑ i ∈ active, affPart idx c0 l i v) :=
    IsQuad.add (QuadForm.isQuad ((quadP_iff k g).mp hg))
      (IsAff.isQuad (IsAff.sum active (fun i v => affPart idx c0 l i v)
        fun i _ => affPart_isAff idx c0 l i))
  have hc := corr_bound z2fun_add_self (form idx s) (form_isAff idx s) active _ _ e hL hQ
    (hrank hne)
  rw [Finset.sum_map, Finset.card_map] at hc
  have hsgn : ∀ q ∈ L, sgn (∑ i ∈ active, cube (form idx s) i (vec k q) +
      (z2 (g ((vecEquiv k).symm (vec k q))) + ∑ i ∈ active, affPart idx c0 l i (vec k q))) =
      sgn (z2 (g q) + z2 (par (∑ i ∈ active, (out q i).toNat))) := by
    intro q hq
    rw [z2_target idx s l c0 out active q (hout q hq), Finset.sum_add_distrib,
      show (vecEquiv k).symm (vec k q) = q from (vecEquiv k).symm_apply_apply q, add_left_comm]
  have hc' : 4 ^ e * |∑ q ∈ L, sgn (z2 (g q) + z2 (par (∑ i ∈ active, (out q i).toNat)))| ≤
      3 ^ e * (L.card : ℤ) := by
    rw [← Finset.sum_congr rfl hsgn]
    exact hc
  have hag := two_mul_card_agree L g (fun q => par (∑ i ∈ active, (out q i).toNat))
  have hZ : (4 : ℤ) ^ e *
      (2 * ((L.filter (fun q => g q == par (∑ i ∈ active, (out q i).toNat))).card : ℤ)) ≤
      (4 ^ e + 3 ^ e) * (L.card : ℤ) := by
    rw [hag, mul_add, add_mul]
    exact (add_le_add_iff_left _).mpr
      ((mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)).trans hc')
  exact_mod_cast hZ

lemma claim1 {k m : ℕ} (fiber : Finset (Fin (2 ^ k))) (P : Finset (Fin k)) (ref : Fin (2 ^ k))
    (hfib : ∀ q, q ∈ fiber ↔ ∀ z ∈ P, q.val.testBit z.val = ref.val.testBit z.val)
    (idx : Fin m → Fin 3 → Fin k) (hidx : ∀ i j i' j', idx i j = idx i' j' → i = i' ∧ j = j')
    (hP : ∀ i j, idx i j ∉ P) (s l : Fin m → Fin 3 → Bool) (c0 : Fin m → Bool)
    (out : Fin (2 ^ k) → Fin m → Bool)
    (hout : ∀ q ∈ fiber, ∀ i,
      out q i = winOut (fun j => q.val.testBit (idx i j).val) (s i) (l i) (c0 i))
    (active : Finset (Fin m)) (d : ℕ)
    (choose : ℕ → ℕ → Fin k → Bool) (leaf : ℕ → Fin (2 ^ k) → Bool)
    (hleaf : ∀ h, quadP k (leaf h)) :
    4 ^ (active.card - d) * (2 * (fiber.filter (fun q =>
        leaf (runP k d choose q) q == par (∑ i ∈ active, (out q i).toNat))).card) ≤
      (4 ^ (active.card - d) + 3 ^ (active.card - d)) * fiber.card := by
  rcases le_total active.card d with hsd | hds
  ·
    rw [Nat.sub_eq_zero_of_le hsd, pow_zero, pow_zero, one_mul]
    exact Nat.mul_le_mul_left 2 (Finset.card_filter_le _ _)
  obtain ⟨e, he⟩ : ∃ e, e = active.card - d := ⟨_, rfl⟩
  rw [← he]
  have hmem := mem_map_fiber hfib
  have hAff := affSet_of_fixed _ P (vec k ref) hmem
  have h8 := card_pat_fiber _ P (vec k ref) hmem idx hidx hP s active
  have hrun : ∀ q, runP k d choose q ∈ Finset.range (2 ^ d) := fun q =>
    Finset.mem_range.mpr (stepRun_lt _ q d)

  have hleafb : ∀ h ∈ Finset.range (2 ^ d),
      4 ^ e * (2 * ((fiber.filter (fun q => runP k d choose q = h)).filter (fun q =>
        leaf h q == par (∑ i ∈ active, (out q i).toNat))).card) ≤
      (4 ^ e + 3 ^ e) * (fiber.filter (fun q => runP k d choose q = h)).card := by
    intro h hh
    have hmap : (fiber.filter (fun q => runP k d choose q = h)).map (vecEquiv k).toEmbedding =
        (fiber.map (vecEquiv k).toEmbedding).filter (fun v =>
          ∀ t < d, ∑ i, z2 (choose t (h % 2 ^ t) i) * v i = z2 (h.testBit t)) := by
      rw [Finset.filter_map]
      congr 1
      exact Finset.filter_congr fun q _ => runP_eq_iff k d choose q h (Finset.mem_range.mp hh)
    obtain ⟨haff, hcard⟩ := affSet_cut (form idx s) (form_isAff idx s) active hAff
      (fun t v => ∑ i, z2 (choose t (h % 2 ^ t) i) * v i) (fun t => lin_isAff _)
      (fun t => z2 (h.testBit t)) d
    refine leaf_bound idx s l c0 out active e _ (leaf h) (hleaf h)
      (fun q hq => hout q (Finset.mem_filter.mp hq).1) (hmap ▸ haff) fun hne => ?_
    rw [hmap]
    have h2 : 2 ^ d * 2 ^ (2 * active.card + e) = 8 ^ active.card := by
      rw [← pow_add, show (8 : ℕ) = 2 ^ 3 from rfl, ← pow_mul]
      congr 1
      omega
    exact Nat.le_of_mul_le_mul_left
      (h2 ▸ h8.trans (hcard (hmap ▸ hne.map))) (pow_pos two_pos d)

  have hswap : ∀ h, (fiber.filter (fun q =>
        leaf (runP k d choose q) q == par (∑ i ∈ active, (out q i).toNat))).filter
        (fun q => runP k d choose q = h) =
      (fiber.filter (fun q => runP k d choose q = h)).filter (fun q =>
        leaf h q == par (∑ i ∈ active, (out q i).toNat)) := by
    intro h
    ext q
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨⟨hq, hag⟩, hr⟩ => ⟨⟨hq, hr⟩, hr ▸ hag⟩, fun ⟨⟨hq, hr⟩, hag⟩ => ⟨⟨hq, hr ▸ hag⟩, hr⟩⟩
  rw [Finset.card_eq_sum_card_fiberwise (f := runP k d choose) (t := Finset.range (2 ^ d))
      (s := fiber) fun q _ => hrun q,
    Finset.card_eq_sum_card_fiberwise (f := runP k d choose) (t := Finset.range (2 ^ d))
      fun q _ => hrun q,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun h hh => (hswap h) ▸ hleafb h hh

section QuadFormClosure

variable {k : ℕ}

lemma QuadForm.const (c : ZMod 2) : QuadForm k (fun _ => c) :=
  ⟨c, fun _ => 0, fun _ _ => 0, fun v => by simp⟩

lemma QuadForm.coord (i : Fin k) : QuadForm k (fun v => v i) :=
  ⟨0, fun i' => if i' = i then 1 else 0, fun _ _ => 0, fun v => by simp⟩

lemma QuadForm.coord_mul (i j : Fin k) : QuadForm k (fun v => v i * v j) :=
  ⟨0, fun _ => 0, fun i' j' => (if i' = i then 1 else 0) * (if j' = j then 1 else 0),
    fun v => by simp [ite_mul, mul_ite, Finset.sum_ite_eq']⟩

lemma QuadForm.add {G H : (Fin k → ZMod 2) → ZMod 2} (hG : QuadForm k G) (hH : QuadForm k H) :
    QuadForm k (fun v => G v + H v) := by
  obtain ⟨β, l, α, hG⟩ := hG
  obtain ⟨β', l', α', hH⟩ := hH
  refine ⟨β + β', fun i => l i + l' i, fun i j => α i j + α' i j, fun v => ?_⟩
  simp only [hG, hH, add_mul, Finset.sum_add_distrib]
  ring

lemma QuadForm.const_mul (c : ZMod 2) {G : (Fin k → ZMod 2) → ZMod 2} (hG : QuadForm k G) :
    QuadForm k (fun v => c * G v) := by
  obtain ⟨β, l, α, hG⟩ := hG
  refine ⟨c * β, fun i => c * l i, fun i j => c * α i j, fun v => ?_⟩
  simp only [hG, mul_add, Finset.mul_sum, mul_assoc]

lemma QuadForm.sum {α : Type*} (S : Finset α) (F : α → (Fin k → ZMod 2) → ZMod 2)
    (h : ∀ i ∈ S, QuadForm k (F i)) : QuadForm k (fun v => ∑ i ∈ S, F i v) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using QuadForm.const (k := k) 0
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact QuadForm.add (h a (Finset.mem_insert_self a S))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma QuadForm.shift_mul (i j : Fin k) (a b c : ZMod 2) :
    QuadForm k (fun v => c * (v i + a) * (v j + b)) := by
  have h : (fun v : Fin k → ZMod 2 => c * (v i + a) * (v j + b)) =
      fun v => c * (v i * v j + (b * v i + (a * v j + a * b))) := by
    funext v
    ring
  rw [h]
  exact QuadForm.const_mul c (QuadForm.add (QuadForm.coord_mul i j)
    (QuadForm.add (QuadForm.const_mul b (QuadForm.coord i))
    (QuadForm.add (QuadForm.const_mul a (QuadForm.coord j)) (QuadForm.const (a * b)))))

end QuadFormClosure

section Attain

variable {k m n : ℕ} (idx : Fin m → Fin 3 → Fin k) (s l : Fin m → Fin 3 → Bool)
  (c0 : Fin m → Bool) (w : Fin n → Fin m) (d : ℕ)

def askMask (t : ℕ) (z : Fin k) : Bool :=
  if h : t < n then decide (z = idx (w ⟨t, h⟩) 0) else false

def guessPoly (h : ℕ) (v : Fin k → ZMod 2) : ZMod 2 :=
  ∑ t : Fin n, (affPart idx c0 l (w t) v +
    if t.val < d then
      (z2 (h.testBit t.val) + z2 (s (w t) 0)) * form idx s (w t) 1 v * form idx s (w t) 2 v
    else 0)

def guess (h : ℕ) (q : Fin (2 ^ k)) : Bool := decide (guessPoly idx s l c0 w d h (vec k q) = 1)

lemma askMask_card (t : ℕ) :
    (Finset.univ.filter (fun z : Fin k => askMask idx w t z)).card ≤ 1 := by
  refine Finset.card_le_one.2 fun a ha b hb => ?_
  have ha' := (Finset.mem_filter.1 ha).2
  have hb' := (Finset.mem_filter.1 hb).2
  unfold askMask at ha' hb'
  split_ifs at ha' hb'
  rw [of_decide_eq_true ha', of_decide_eq_true hb']

lemma lin_askMask (t : Fin n) (q : Fin (2 ^ k)) :
    lin k (askMask idx w t.val) q = q.val.testBit (idx (w t) 0).val := by
  apply z2_inj
  have hmask : ∀ z, askMask idx w t.val z = decide (z = idx (w t) 0) := fun z => by
    simp only [askMask, t.isLt, dite_true]
  rw [z2_lin, Finset.sum_eq_single (idx (w t) 0)]
  · rw [hmask, decide_eq_true rfl]
    exact one_mul _
  · intro z _ hz
    rw [hmask, decide_eq_false hz]
    exact zero_mul _
  · exact fun h => absurd (Finset.mem_univ _) h

lemma runP_askMask_testBit (t : Fin n) (ht : t.val < d) (q : Fin (2 ^ k)) :
    (runP k d (fun t _ => askMask idx w t) q).testBit t.val = q.val.testBit (idx (w t) 0).val := by
  rw [runP_eq, stepRun_testBit _ _ d t.val ht]
  exact lin_askMask idx w t q

lemma guessPoly_quadForm (h : ℕ) : QuadForm k (guessPoly idx s l c0 w d h) := by
  refine QuadForm.sum Finset.univ _ fun t _ => QuadForm.add ?_ ?_
  · exact QuadForm.add (QuadForm.const _)
      (QuadForm.sum Finset.univ _ fun j _ => QuadForm.const_mul _ (QuadForm.coord _))
  · by_cases ht : t.val < d
    · simp only [ht, ite_true]
      exact QuadForm.shift_mul _ _ _ _ _
    · simp only [ht, ite_false]
      exact QuadForm.const 0

lemma z2_guess (h : ℕ) (q : Fin (2 ^ k)) :
    z2 (guess idx s l c0 w d h q) = guessPoly idx s l c0 w d h (vec k q) := z2_decide _

lemma guess_quadP (h : ℕ) : quadP k (guess idx s l c0 w d h) := by
  have hfun : (fun v => z2 (guess idx s l c0 w d h ((vecEquiv k).symm v))) =
      guessPoly idx s l c0 w d h := by
    funext v
    rw [z2_guess, vec_symm]
  rw [quadP_iff, hfun]
  exact guessPoly_quadForm idx s l c0 w d h

lemma guess_add_target (q : Fin (2 ^ k)) (tgt : Bool)
    (htgt : z2 tgt =
      ∑ t : Fin n, (cube (form idx s) (w t) (vec k q) + affPart idx c0 l (w t) (vec k q))) :
    z2 (guess idx s l c0 w d (runP k d (fun t _ => askMask idx w t) q) q) + z2 tgt =
      ∑ t ∈ Finset.univ.filter (fun t : Fin n => d ≤ t.val),
        cube (fun t => form idx s (w t)) t (vec k q) := by
  rw [z2_guess, htgt, guessPoly, ← Finset.sum_add_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases ht : t.val < d
  · rw [ite_eq_left ht, ite_eq_right (by omega), runP_askMask_testBit idx w d t ht q]
    change affPart idx c0 l (w t) (vec k q) + cube (form idx s) (w t) (vec k q) +
      (cube (form idx s) (w t) (vec k q) + affPart idx c0 l (w t) (vec k q)) = 0
    linear_combination
      (affPart idx c0 l (w t) (vec k q) + cube (form idx s) (w t) (vec k q)) * z2_two
  · rw [ite_eq_right ht, ite_eq_left (by omega)]
    change affPart idx c0 l (w t) (vec k q) + 0 +
      (cube (form idx s) (w t) (vec k q) + affPart idx c0 l (w t) (vec k q)) =
        cube (form idx s) (w t) (vec k q)
    linear_combination affPart idx c0 l (w t) (vec k q) * z2_two

end Attain

lemma card_fin_ge (n d : ℕ) : (Finset.univ.filter (fun t : Fin n => d ≤ t.val)).card = n - d := by
  have h : (Finset.univ.filter (fun t : Fin n => d ≤ t.val)).map Fin.valEmbedding =
      Finset.Ico d n := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    exact ⟨fun ⟨t, ht, hx⟩ => hx ▸ ⟨ht, t.isLt⟩, fun ⟨h1, h2⟩ => ⟨⟨x, h2⟩, h1, rfl⟩⟩
  rw [← Finset.card_map Fin.valEmbedding, h, Nat.card_Ico]

lemma sum_orderEmbOfFin {m : ℕ} (active : Finset (Fin m)) (F : Fin m → ZMod 2) :
    ∑ i ∈ active, F i = ∑ t : Fin active.card, F (active.orderEmbOfFin rfl t) := by
  have h := Finset.sum_map Finset.univ (active.orderEmbOfFin rfl).toEmbedding F
  rw [Finset.map_orderEmbOfFin_univ] at h
  exact h

lemma agree_count {k m n : ℕ} (fiber : Finset (Fin (2 ^ k))) (P : Finset (Fin k))
    (ref : Fin (2 ^ k))
    (hfib : ∀ q, q ∈ fiber ↔ ∀ z ∈ P, q.val.testBit z.val = ref.val.testBit z.val)
    (idx : Fin m → Fin 3 → Fin k) (hidx : ∀ i j i' j', idx i j = idx i' j' → i = i' ∧ j = j')
    (hP : ∀ i j, idx i j ∉ P) (s l : Fin m → Fin 3 → Bool) (c0 : Fin m → Bool)
    (w : Fin n → Fin m) (hw : Function.Injective w) (d : ℕ) (tgt : Fin (2 ^ k) → Bool)
    (htgt : ∀ q ∈ fiber, z2 (tgt q) =
      ∑ t : Fin n, (cube (form idx s) (w t) (vec k q) + affPart idx c0 l (w t) (vec k q))) :
    4 ^ (n - d) * (2 * (fiber.filter (fun q =>
        guess idx s l c0 w d (runP k d (fun t _ => askMask idx w t) q) q == tgt q)).card) =
      (4 ^ (n - d) + 3 ^ (n - d)) * fiber.card := by
  have hflip : ∀ (t : Fin n) (j : Fin 3) (t' : Fin n) (j' : Fin 3) (a : Fin k → ZMod 2),
      form idx s (w t') j' (a + Pi.single (idx (w t) j) 1) =
        form idx s (w t') j' a + if t' = t ∧ j' = j then 1 else 0 := by
    intro t j t' j' a
    by_cases h : t' = t ∧ j' = j
    · obtain ⟨rfl, rfl⟩ := h
      simp only [form, Pi.add_apply, Pi.single_eq_same, and_self, ite_true]
      ring
    · have hne : idx (w t') j' ≠ idx (w t) j := fun h' =>
        h ⟨hw (hidx _ _ _ _ h').1, (hidx _ _ _ _ h').2⟩
      simp only [form, Pi.add_apply, Pi.single_eq_of_ne hne, h, ite_false, add_zero]
  have hcount := exact_count z2fun_add_self
    (fun t => form idx s (w t)) (fun t j => Pi.single (idx (w t) j) 1) hflip
    (Finset.univ.filter (fun t : Fin n => d ≤ t.val)) (fiber.map (vecEquiv k).toEmbedding)
    (fun t _ j a ha => by
      rw [mem_map_fiber hfib] at ha ⊢
      intro z hz
      have hne : z ≠ idx (w t) j := fun h => hP (w t) j (h ▸ hz)
      rw [Pi.add_apply, Pi.single_eq_of_ne hne, add_zero]
      exact ha z hz)
  simp only [card_fin_ge, Finset.sum_map, Finset.card_map, Equiv.coe_toEmbedding,
    vecEquiv_apply] at hcount
  have hagree : (2 * ((fiber.filter (fun q =>
      guess idx s l c0 w d (runP k d (fun t _ => askMask idx w t) q) q == tgt q)).card : ℤ)) =
      fiber.card + ∑ q ∈ fiber, sgn (∑ t ∈ Finset.univ.filter (fun t : Fin n => d ≤ t.val),
        cube (fun t => form idx s (w t)) t (vec k q)) := by
    rw [two_mul_card_agree]
    exact congrArg _ (Finset.sum_congr rfl fun q hq => by
      rw [guess_add_target idx s l c0 w d q (tgt q) (htgt q hq)])
  have hint : (4 : ℤ) ^ (n - d) * (2 * ((fiber.filter (fun q =>
      guess idx s l c0 w d (runP k d (fun t _ => askMask idx w t) q) q == tgt q)).card : ℤ)) =
      (4 ^ (n - d) + 3 ^ (n - d)) * fiber.card := by
    rw [hagree]
    linear_combination hcount
  exact_mod_cast hint

lemma claim2 {k m : ℕ} (fiber : Finset (Fin (2 ^ k))) (P : Finset (Fin k)) (ref : Fin (2 ^ k))
    (hfib : ∀ q, q ∈ fiber ↔ ∀ z ∈ P, q.val.testBit z.val = ref.val.testBit z.val)
    (idx : Fin m → Fin 3 → Fin k) (hidx : ∀ i j i' j', idx i j = idx i' j' → i = i' ∧ j = j')
    (hP : ∀ i j, idx i j ∉ P) (s l : Fin m → Fin 3 → Bool) (c0 : Fin m → Bool)
    (out : Fin (2 ^ k) → Fin m → Bool)
    (hout : ∀ q ∈ fiber, ∀ i,
      out q i = winOut (fun j => q.val.testBit (idx i j).val) (s i) (l i) (c0 i))
    (active : Finset (Fin m)) (d : ℕ) :
    ∃ (fixed : ℕ → Fin k → Bool) (leaf : ℕ → Fin (2 ^ k) → Bool),
      (∀ h, quadP k (leaf h)) ∧
      (∀ t, (Finset.univ.filter (fun z : Fin k => fixed t z)).card ≤ 1) ∧
      4 ^ (active.card - d) * (2 * (fiber.filter (fun q =>
          leaf (runP k d (fun t _ => fixed t) q) q == par (∑ i ∈ active, (out q i).toNat))).card) =
        (4 ^ (active.card - d) + 3 ^ (active.card - d)) * fiber.card :=
  ⟨askMask idx (active.orderEmbOfFin rfl), guess idx s l c0 (active.orderEmbOfFin rfl) d,
    guess_quadP idx s l c0 _ d, askMask_card idx _,
    agree_count fiber P ref hfib idx hidx hP s l c0 _ (active.orderEmbOfFin rfl).injective d _
      fun q hq => by rw [z2_target idx s l c0 out active q (hout q hq), sum_orderEmbOfFin]⟩

def rot (k s word : ℕ) : ℕ :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def stepBit (k word j : ℕ) : Bool :=
  xor (word.testBit j) (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))

def step (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc j =>
    acc ||| ((xor (word.testBit j)
      (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0

def mix (k word : ℕ) : ℕ :=
  word ^^^ rot k 1 word ^^^ rot k (k - 1) word

def stateAt (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (row rounds key : ℕ) : ℕ :=
  (List.range rounds).foldl (fun prev tick =>
    step k (mix k prev) ^^^ rot k (2 * tick) key ^^^ (constant (tick + 1)).val) (rot k 1 key ^^^ row)

lemma stateAt_zero (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (row key : ℕ) :
    stateAt k constant row 0 key = rot k 1 key ^^^ row := rfl

lemma stateAt_succ (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (row s key : ℕ) :
    stateAt k constant row (s + 1) key =
      step k (mix k (stateAt k constant row s key)) ^^^ rot k (2 * s) key ^^^
        (constant (s + 1)).val := by
  simp [stateAt, List.range_succ]

lemma rot_lt (k s word : ℕ) : rot k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma xor_lt {k a b : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : a ^^^ b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  have hpow := Nat.pow_le_pow_right Nat.zero_lt_two hj
  simp [Nat.testBit_xor, Nat.testBit_lt_two_pow (ha.trans_le hpow),
    Nat.testBit_lt_two_pow (hb.trans_le hpow)]

lemma testBit_rot {k s word b : ℕ} (hw : word < 2 ^ k) (hb : b < k) :
    (rot k s word).testBit b = word.testBit ((b + k - s % k) % k) := by
  have hk : 0 < k := by omega
  have hs : s % k < k := Nat.mod_lt _ hk
  simp only [rot, Nat.testBit_mod_two_pow, hb, decide_true, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : s % k ≤ b
  · have hz : word.testBit (k - s % k + b) = false :=
      Nat.testBit_lt_two_pow (hw.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
    have he : (b + k - s % k) % k = b - s % k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, hz, he]
  · have he : (b + k - s % k) % k = k - s % k + b := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, he]

lemma testBit_foldl_or (p : ℕ → Bool) (xs : List ℕ) (acc i : ℕ) :
    (xs.foldl (fun a j => a ||| ((p j).toNat <<< j)) acc).testBit i =
      (acc.testBit i || (decide (i ∈ xs) && p i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons j xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hji : j = i
    · subst j
      cases p i <;> simp
    · by_cases hle : j ≤ i
      · have hsub : 1 ≤ i - j := by omega
        have hbt : (p j).toNat.testBit (i - j) = false := by
          cases p j
          · simp
          · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 1 < 2 ^ 1)
              (Nat.pow_le_pow_right Nat.zero_lt_two hsub))
        simp [hle, hbt, Ne.symm hji]
      · simp [hle, Ne.symm hji]

lemma testBit_step_all (k word b : ℕ) :
    (step k word).testBit b = (decide (b < k) && stepBit k word b) := by
  unfold step stepBit
  rw [testBit_foldl_or]
  simp

lemma testBit_step {k word b : ℕ} (hb : b < k) :
    (step k word).testBit b = stepBit k word b := by
  simp [testBit_step_all, hb]

lemma step_lt (k word : ℕ) : step k word < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro b hb
  simp [testBit_step_all, Nat.not_lt_of_ge hb]

lemma stateAt_lt (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (row : Fin (2 ^ k)) (rounds key : ℕ) :
    stateAt k constant row.val rounds key < 2 ^ k := by
  cases rounds with
  | zero => exact xor_lt (rot_lt k 1 key) row.isLt
  | succ s =>
    rw [stateAt_succ]
    exact xor_lt (xor_lt (step_lt k _) (rot_lt k _ _)) (constant (s + 1)).isLt

lemma testBit_mix {k word b : ℕ} (hk : 2 ≤ k) (hw : word < 2 ^ k) (hb : b < k) :
    (mix k word).testBit b =
      xor (xor (word.testBit b) (word.testBit ((b + k - 1) % k)))
        (word.testBit ((b + 1) % k)) := by
  unfold mix
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rot hw hb, testBit_rot hw hb]
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2]
  have h3 : (b + k - (k - 1)) % k = (b + 1) % k := by congr 1; omega
  rw [h3]

lemma mod_sub_eq {k p s : ℕ} (hk : 0 < k) (hsp : s ≤ p) :
    (p % k + k - s % k) % k = (p - s) % k := by
  have hdiv : p - s + s = p := Nat.sub_add_cancel hsp
  have h1 : (p % k + k - s % k + s % k) % k = p % k := by
    have hlt : s % k < k := Nat.mod_lt s hk
    have hadd : p % k + k - s % k + s % k = p % k + k := by omega
    rw [hadd, Nat.add_mod_right, Nat.mod_mod]
  have h2 : ((p - s) % k + s % k) % k = p % k := by
    rw [Nat.mod_add_mod, Nat.add_mod_mod, hdiv]
  set A := (p % k + k - s % k) % k
  set B := (p - s) % k
  set C := s % k
  have ha : A < k := Nat.mod_lt _ hk
  have hb : B < k := Nat.mod_lt _ hk
  have hs : C < k := Nat.mod_lt s hk
  have h3 : (A + C) % k = (B + C) % k := by
    rw [Nat.mod_add_mod, h1, ← h2]
  by_cases h1lt : A + C < k <;> by_cases h2lt : B + C < k
  · rw [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_of_lt h2lt] at h3; omega
  · rw [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h3; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h2lt] at h3; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h3; omega

lemma testBit_stateAt_succ {k : ℕ} (hk : 2 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row : Fin (2 ^ k)) (s : ℕ) (key : Fin (2 ^ k)) (q : ℕ) (hq : 1 ≤ q) :
    (stateAt k constant row.val (s + 1) key.val).testBit (q % k) =
      let prev := fun r : ℕ => (stateAt k constant row.val s key.val).testBit (r % k)
      let m0 := xor (xor (prev q) (prev (q - 1))) (prev (q + 1))
      let m1 := xor (xor (prev (q + 1)) (prev q)) (prev (q + 2))
      let m2 := xor (xor (prev (q + 2)) (prev (q + 1))) (prev (q + 3))
      let st := xor m0 (!m1 && m2)
      xor (xor st ((rot k (2 * s) key.val).testBit (q % k)))
        ((constant (s + 1)).val.testBit (q % k)) := by
  have hk0 : 0 < k := by omega
  rw [stateAt_succ, Nat.testBit_xor, Nat.testBit_xor, testBit_step (Nat.mod_lt q hk0)]
  unfold stepBit
  have hm : ∀ d : ℕ, (mix k (stateAt k constant row.val s key.val)).testBit ((q % k + d) % k) =
      xor (xor ((stateAt k constant row.val s key.val).testBit ((q + d) % k))
               ((stateAt k constant row.val s key.val).testBit ((q + d - 1) % k)))
          ((stateAt k constant row.val s key.val).testBit ((q + d + 1) % k)) := by
    intro d
    have hlt : (q % k + d) % k < k := Nat.mod_lt _ hk0
    rw [testBit_mix hk (stateAt_lt k constant row s key.val) hlt]
    have h0 : (q % k + d) % k = (q + d) % k := Nat.mod_add_mod q k d
    have h1 : ((q + d) % k + k - 1) % k = (q + d - 1) % k := by
      have h1m : 1 = 1 % k := (Nat.mod_eq_of_lt (by omega)).symm
      conv_lhs => rw [h1m]
      exact mod_sub_eq hk0 (by omega)
    have h2 : ((q + d) % k + 1) % k = (q + d + 1) % k := Nat.mod_add_mod (q + d) k 1
    rw [h0, h1, h2]
  have hm0 := hm 0
  simp only [Nat.add_zero, Nat.mod_mod] at hm0
  have hm1 := hm 1
  have hm2 := hm 2
  have he1 : q + 1 - 1 = q := by omega
  have he2 : q + 2 - 1 = q + 1 := by omega
  have he3 : q + 1 + 1 = q + 2 := by omega
  have he4 : q + 2 + 1 = q + 3 := by omega
  rw [he1, he3] at hm1
  rw [he2, he4] at hm2
  rw [hm0, hm1, hm2]

def rawTwoRound (old6 old7 alpha beta e0 y0 y1 y2 : Bool) : Bool :=
  let old8 := xor old6 old7
  let z0 := xor old6 y0
  let z1 := xor (xor old8 y0) y1
  let z2 := xor (xor y0 y1) y2
  let f4 := beta
  let f5 := xor (!alpha) beta
  let f6 := xor alpha z0
  let f7 := xor beta (!z0 && z1)
  let f8 := xor (xor (xor z0 (!z1 && z2)) y0) e0
  let w5 := xor (xor f4 f5) f6
  let w6 := xor (xor f5 f6) f7
  let w7 := xor (xor f6 f7) f8
  xor w5 (!w6 && w7)

lemma rawTwoRound_decomp (old6 old7 alpha beta e0 y0 y1 y2 : Bool) :
    let d0 := old6
    let d1 := old7
    let d2 := xor (xor (xor (xor true old7) alpha) beta) e0
    let res := fun a b c => xor (rawTwoRound old6 old7 alpha beta e0 a b c)
      ((xor a d0) && (xor b d1) && (xor c d2))
    let c0 := res false false false
    let l0 := xor (res true false false) c0
    let l1 := xor (res false true false) c0
    let l2 := xor (res false false true) c0
    rawTwoRound old6 old7 alpha beta e0 y0 y1 y2 =
      xor ((xor y0 d0) && (xor y1 d1) && (xor y2 d2))
        (xor (xor (xor c0 (l0 && y0)) (l1 && y1)) (l2 && y2)) := by
  cases old6 <;> cases old7 <;> cases alpha <;> cases beta <;>
    cases e0 <;> cases y0 <;> cases y1 <;> cases y2 <;> rfl

lemma bool_xor_cancel (a b : Bool) : xor (xor a b) b = a := by
  cases a <;> cases b <;> rfl

lemma guarded_two_round_formula {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row ref : Fin (2 ^ k)) (p : ℕ)
    (hgood :
      let old := fun j : ℕ => (stateAt k constant row.val 0 ref.val).testBit ((p + j) % k)
      let first := fun j : ℕ => (stateAt k constant row.val 1 ref.val).testBit ((p + j) % k)
      let τ := xor (xor (old 6) (old 7)) (old 8)
      let α := xor (xor (xor (old 5) (old 6)) (old 7))
        (xor ((rot k 0 ref.val).testBit ((p + 6) % k)) ((constant 1).val.testBit ((p + 6) % k)))
      let β := xor τ
        (xor ((rot k 0 ref.val).testBit ((p + 7) % k)) ((constant 1).val.testBit ((p + 7) % k)))
      τ = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
        xor (first 4) (first 5) = !α ∧ first 4 = β) :
    ∃ (s0 s1 s2 c0 l0 l1 l2 : Bool),
      ∀ key : Fin (2 ^ k),
        (∀ j : Fin 9,
          (stateAt k constant row.val 0 key.val).testBit ((p + j.val) % k) =
          (stateAt k constant row.val 0 ref.val).testBit ((p + j.val) % k)) →
        let u0 := key.val.testBit ((p + 8) % k)
        let u1 := key.val.testBit ((p + 9) % k)
        let u2 := key.val.testBit ((p + 10) % k)
        (stateAt k constant row.val 2 key.val).testBit ((p + 5) % k) =
          xor ((xor u0 s0) && (xor u1 s1) && (xor u2 s2))
            (xor (xor (xor c0 (l0 && u0)) (l1 && u1)) (l2 && u2)) := by
  have hk0 : 0 < k := by omega
  have hk2 : 2 ≤ k := by omega
  let oldRef := fun j : ℕ => (stateAt k constant row.val 0 ref.val).testBit ((p + j) % k)
  let firstRef := fun j : ℕ => (stateAt k constant row.val 1 ref.val).testBit ((p + j) % k)
  let τ := xor (xor (oldRef 6) (oldRef 7)) (oldRef 8)
  let inj1_6 := xor ((rot k 0 ref.val).testBit ((p + 6) % k)) ((constant 1).val.testBit ((p + 6) % k))
  let inj1_7 := xor ((rot k 0 ref.val).testBit ((p + 7) % k)) ((constant 1).val.testBit ((p + 7) % k))
  let α := xor (xor (xor (oldRef 5) (oldRef 6)) (oldRef 7)) inj1_6
  let β := xor τ inj1_7
  rcases hgood with ⟨hτ, _, hf45, hf4⟩
  have hτ' : τ = false := hτ
  have hf4' : firstRef 4 = β := hf4
  have hf45' : xor (firstRef 4) (firstRef 5) = !α := hf45
  let row9 := row.val.testBit ((p + 9) % k)
  let row10 := row.val.testBit ((p + 10) % k)
  let row11 := row.val.testBit ((p + 11) % k)
  let c18 := (constant 1).val.testBit ((p + 8) % k)
  let e0 := xor row9 c18
  let i25 := xor ((rot k 2 ref.val).testBit ((p + 5) % k)) ((constant 2).val.testBit ((p + 5) % k))
  let d0 := oldRef 6
  let d1 := oldRef 7
  let d2 := xor (xor (xor (xor true (oldRef 7)) α) β) e0
  let res := fun a b c => xor (rawTwoRound (oldRef 6) (oldRef 7) α β e0 a b c)
    ((xor a d0) && (xor b d1) && (xor c d2))
  let rc0 := res false false false
  let rl0 := xor (res true false false) rc0
  let rl1 := xor (res false true false) rc0
  let rl2 := xor (res false false true) rc0
  let s0 := xor d0 row9
  let s1 := xor d1 row10
  let s2 := xor d2 row11
  let c0 := xor (xor (xor (xor rc0 (rl0 && row9)) (rl1 && row10)) (rl2 && row11)) i25
  refine ⟨s0, s1, s2, c0, rl0, rl1, rl2, ?_⟩
  intro key hpin u0 u1 u2
  have hbit0 : ∀ (kw : Fin (2 ^ k)) (j : ℕ), 1 ≤ j →
      (stateAt k constant row.val 0 kw.val).testBit ((p + j) % k) =
      xor (kw.val.testBit ((p + j - 1) % k)) (row.val.testBit ((p + j) % k)) := by
    intro kw j hj
    rw [stateAt_zero, Nat.testBit_xor, testBit_rot kw.isLt (Nat.mod_lt _ hk0)]
    have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    have hsub := mod_sub_eq hk0 (p := p + j) (s := 1) (by omega)
    rw [h1m] at hsub ⊢
    rw [hsub]
  have hkey_pin : ∀ r : ℕ, r < 8 →
      key.val.testBit ((p + r) % k) = ref.val.testBit ((p + r) % k) := by
    intro r hr
    have hp1 := hpin ⟨r + 1, by omega⟩
    rw [hbit0 key (r + 1) (by omega), hbit0 ref (r + 1) (by omega)] at hp1
    have hsub : p + (r + 1) - 1 = p + r := by omega
    rw [hsub] at hp1
    have := congr_arg (fun b => xor b (row.val.testBit ((p + (r + 1)) % k))) hp1
    simpa [bool_xor_cancel] using this
  have hrot0_eq : ∀ (kw : Fin (2 ^ k)) (q : ℕ),
      (rot k 0 kw.val).testBit (q % k) = kw.val.testBit (q % k) := by
    intro kw q
    rw [testBit_rot kw.isLt (Nat.mod_lt _ hk0)]
    simp [Nat.zero_mod, Nat.add_mod_right]
  have hrot2_eq : ∀ (kw : Fin (2 ^ k)),
      (rot k 2 kw.val).testBit ((p + 5) % k) = kw.val.testBit ((p + 3) % k) := by
    intro kw
    rw [testBit_rot kw.isLt (Nat.mod_lt _ hk0)]
    have h2m : 2 % k = 2 := Nat.mod_eq_of_lt (by omega)
    have hsub := mod_sub_eq hk0 (p := p + 5) (s := 2) (by omega)
    rw [h2m] at hsub ⊢
    have hp3 : p + 5 - 2 = p + 3 := by omega
    rw [hsub, hp3]
  have hold_eq : ∀ j : ℕ, j < 9 →
      (stateAt k constant row.val 0 key.val).testBit ((p + j) % k) = oldRef j :=
    fun j hj => hpin ⟨j, hj⟩
  have hfirst4 : (stateAt k constant row.val 1 key.val).testBit ((p + 4) % k) = β := by
    rw [← hf4']
    change (stateAt k constant row.val 1 key.val).testBit ((p + 4) % k) =
      (stateAt k constant row.val 1 ref.val).testBit ((p + 4) % k)
    rw [testBit_stateAt_succ hk2 constant row 0 key (p + 4) (by omega),
        testBit_stateAt_succ hk2 constant row 0 ref (p + 4) (by omega)]
    have ha3 : p + 4 - 1 = p + 3 := by omega
    have ha5 : p + 4 + 1 = p + 5 := by omega
    have ha6 : p + 4 + 2 = p + 6 := by omega
    have ha7 : p + 4 + 3 = p + 7 := by omega
    simp only [ha3, ha5, ha6, ha7, mul_zero, hrot0_eq, hold_eq 3 (by omega),
      hold_eq 4 (by omega), hold_eq 5 (by omega), hold_eq 6 (by omega), hold_eq 7 (by omega),
      hkey_pin 4 (by omega)]
    rfl
  have hfirst5 : (stateAt k constant row.val 1 key.val).testBit ((p + 5) % k) = xor (!α) β := by
    have hf5 : firstRef 5 = xor (!α) β := by
      have h1 := congr_arg (fun b => xor b (firstRef 4)) hf45'
      have hcomm : xor (xor (firstRef 4) (firstRef 5)) (firstRef 4) = firstRef 5 := by
        cases firstRef 4 <;> cases firstRef 5 <;> rfl
      rw [hcomm, hf4'] at h1
      exact h1
    rw [← hf5]
    change (stateAt k constant row.val 1 key.val).testBit ((p + 5) % k) =
      (stateAt k constant row.val 1 ref.val).testBit ((p + 5) % k)
    rw [testBit_stateAt_succ hk2 constant row 0 key (p + 5) (by omega),
        testBit_stateAt_succ hk2 constant row 0 ref (p + 5) (by omega)]
    have ha4 : p + 5 - 1 = p + 4 := by omega
    have ha6 : p + 5 + 1 = p + 6 := by omega
    have ha7 : p + 5 + 2 = p + 7 := by omega
    have ha8 : p + 5 + 3 = p + 8 := by omega
    simp only [ha4, ha6, ha7, ha8, mul_zero, hrot0_eq, hold_eq 4 (by omega),
      hold_eq 5 (by omega), hold_eq 6 (by omega), hold_eq 7 (by omega), hold_eq 8 (by omega),
      hkey_pin 5 (by omega)]
    rfl
  let y0 := xor u0 row9
  let y1 := xor u1 row10
  let y2 := xor u2 row11
  have hy0_eq : (stateAt k constant row.val 0 key.val).testBit ((p + 9) % k) = y0 := by
    rw [hbit0 key 9 (by omega)]
    have : p + 9 - 1 = p + 8 := by omega
    rw [this]
  have hy1_eq : (stateAt k constant row.val 0 key.val).testBit ((p + 10) % k) = y1 := by
    rw [hbit0 key 10 (by omega)]
    have : p + 10 - 1 = p + 9 := by omega
    rw [this]
  have hy2_eq : (stateAt k constant row.val 0 key.val).testBit ((p + 11) % k) = y2 := by
    rw [hbit0 key 11 (by omega)]
    have : p + 11 - 1 = p + 10 := by omega
    rw [this]
  have hold8_eq : oldRef 8 = xor (oldRef 6) (oldRef 7) := by
    have : xor (xor (oldRef 6) (oldRef 7)) (oldRef 8) = false := hτ
    cases h6 : oldRef 6 <;> cases h7 : oldRef 7 <;> cases h8 : oldRef 8 <;> simp_all
  have hfirst6 : (stateAt k constant row.val 1 key.val).testBit ((p + 6) % k) =
      xor α (xor (oldRef 6) y0) := by
    rw [testBit_stateAt_succ hk2 constant row 0 key (p + 6) (by omega)]
    have ha5 : p + 6 - 1 = p + 5 := by omega
    have ha7 : p + 6 + 1 = p + 7 := by omega
    have ha8 : p + 6 + 2 = p + 8 := by omega
    have ha9 : p + 6 + 3 = p + 9 := by omega
    simp only [ha5, ha7, ha8, ha9, mul_zero, hrot0_eq, hold_eq 5 (by omega),
      hold_eq 6 (by omega), hold_eq 7 (by omega), hold_eq 8 (by omega), hy0_eq,
      hkey_pin 6 (by omega)]
    have hα_def : α = xor (xor (xor (oldRef 5) (oldRef 6)) (oldRef 7))
        (xor (ref.val.testBit ((p + 6) % k)) ((constant 1).val.testBit ((p + 6) % k))) := by
      simp only [α, inj1_6, hrot0_eq]
    rw [hα_def, hold8_eq]
    cases oldRef 5 <;> cases oldRef 6 <;> cases oldRef 7 <;> cases y0 <;>
      cases ref.val.testBit ((p + 6) % k) <;> cases (constant 1).val.testBit ((p + 6) % k) <;> rfl
  have hfirst7 : (stateAt k constant row.val 1 key.val).testBit ((p + 7) % k) =
      xor β (!(xor (oldRef 6) y0) && xor (xor (xor (oldRef 6) (oldRef 7)) y0) y1) := by
    rw [testBit_stateAt_succ hk2 constant row 0 key (p + 7) (by omega)]
    have ha6 : p + 7 - 1 = p + 6 := by omega
    have ha8 : p + 7 + 1 = p + 8 := by omega
    have ha9 : p + 7 + 2 = p + 9 := by omega
    have ha10 : p + 7 + 3 = p + 10 := by omega
    simp only [ha6, ha8, ha9, ha10, mul_zero, hrot0_eq, hold_eq 6 (by omega),
      hold_eq 7 (by omega), hold_eq 8 (by omega), hy0_eq, hy1_eq, hkey_pin 7 (by omega)]
    have hβ_def : β = xor (ref.val.testBit ((p + 7) % k)) ((constant 1).val.testBit ((p + 7) % k)) := by
      simp only [β, hτ', inj1_7, hrot0_eq, Bool.false_xor]
    rw [hβ_def, hold8_eq]
    cases oldRef 6 <;> cases oldRef 7 <;> cases y0 <;> cases y1 <;>
      cases ref.val.testBit ((p + 7) % k) <;> cases (constant 1).val.testBit ((p + 7) % k) <;> rfl
  have hfirst8 : (stateAt k constant row.val 1 key.val).testBit ((p + 8) % k) =
      xor (xor (xor (xor (oldRef 6) y0)
        (!(xor (xor (xor (oldRef 6) (oldRef 7)) y0) y1) && xor (xor y0 y1) y2)) y0) e0 := by
    rw [testBit_stateAt_succ hk2 constant row 0 key (p + 8) (by omega)]
    have ha7 : p + 8 - 1 = p + 7 := by omega
    have ha9 : p + 8 + 1 = p + 9 := by omega
    have ha10 : p + 8 + 2 = p + 10 := by omega
    have ha11 : p + 8 + 3 = p + 11 := by omega
    simp only [ha7, ha9, ha10, ha11, mul_zero, hrot0_eq, hold_eq 7 (by omega),
      hold_eq 8 (by omega), hy0_eq, hy1_eq, hy2_eq]
    have hu0_y0 : key.val.testBit ((p + 8) % k) = xor y0 row9 := by
      simp only [y0, u0, bool_xor_cancel]
    rw [hu0_y0, hold8_eq]
    simp only [e0, c18]
    cases oldRef 6 <;> cases oldRef 7 <;> cases y0 <;> cases y1 <;> cases y2 <;>
      cases row9 <;> cases (constant 1).val.testBit ((p + 8) % k) <;> rfl
  rw [testBit_stateAt_succ hk2 constant row 1 key (p + 5) (by omega)]
  have ha4 : p + 5 - 1 = p + 4 := by omega
  have ha6 : p + 5 + 1 = p + 6 := by omega
  have ha7 : p + 5 + 2 = p + 7 := by omega
  have ha8 : p + 5 + 3 = p + 8 := by omega
  simp only [ha4, ha6, ha7, ha8, mul_one, hfirst4, hfirst5, hfirst6, hfirst7, hfirst8]
  have hi25_eq :
      xor ((rot k 2 key.val).testBit ((p + 5) % k)) ((constant 2).val.testBit ((p + 5) % k)) = i25 := by
    simp only [i25, hrot2_eq, hkey_pin 3 (by omega)]
  have hxor_assoc : ∀ a b c : Bool, xor (xor a b) c = xor a (xor b c) := by
    intro a b c; cases a <;> cases b <;> cases c <;> rfl
  rw [hxor_assoc, hi25_eq]
  have hraw :
      xor (xor (xor (xor (!α) β) β) (xor α (xor (oldRef 6) y0)))
        (!(xor (xor (xor α (xor (oldRef 6) y0)) (xor (!α) β))
          (xor β (!(xor (oldRef 6) y0) && xor (xor (xor (oldRef 6) (oldRef 7)) y0) y1))) &&
          xor (xor (xor β (!(xor (oldRef 6) y0) && xor (xor (xor (oldRef 6) (oldRef 7)) y0) y1))
            (xor α (xor (oldRef 6) y0)))
            (xor (xor (xor (xor (oldRef 6) y0)
              (!(xor (xor (xor (oldRef 6) (oldRef 7)) y0) y1) && xor (xor y0 y1) y2)) y0) e0)) =
      rawTwoRound (oldRef 6) (oldRef 7) α β e0 y0 y1 y2 := by
    simp only [rawTwoRound]
    cases oldRef 6 <;> cases oldRef 7 <;> cases α <;> cases β <;> cases e0 <;>
      cases y0 <;> cases y1 <;> cases y2 <;> rfl
  rw [hraw, rawTwoRound_decomp]
  have hshift : ∀ a0 a1 a2 r0 r1 r2 q0 q1 q2 k0 k1 k2 k3 k4 : Bool,
      xor (xor ((xor (xor a0 r0) q0) && (xor (xor a1 r1) q1) && (xor (xor a2 r2) q2))
          (xor (xor (xor k0 (k1 && xor a0 r0)) (k2 && xor a1 r1)) (k3 && xor a2 r2))) k4 =
      xor ((xor a0 (xor q0 r0)) && (xor a1 (xor q1 r1)) && (xor a2 (xor q2 r2)))
          (xor (xor (xor (xor (xor (xor (xor k0 (k1 && r0)) (k2 && r1)) (k3 && r2)) k4)
            (k1 && a0)) (k2 && a1)) (k3 && a2)) := by
    intro a0 a1 a2 r0 r1 r2 q0 q1 q2 k0 k1 k2 k3 k4
    apply z2_inj
    simp only [z2_xor, z2_and]
    ring
  exact hshift u0 u1 u2 row9 row10 row11 d0 d1 d2 rc0 rl0 rl1 rl2 i25

lemma main_proof :
    ∀ (k : ℕ), 0 < k → ∀ (constant : ℕ → Fin (2 ^ k)) (m : ℕ) (starts : Fin m → ℕ),
    Function.Injective (fun z : Fin m × Fin 12 => (starts z.1 + z.2.val) % k) →
    ∀ (row ref : Fin (2 ^ k)),
    (∀ i : Fin m,
      let old := fun j : ℕ => (stateAt k constant row.val 0 ref.val).testBit ((starts i + j) % k)
      let first := fun j : ℕ => (stateAt k constant row.val 1 ref.val).testBit ((starts i + j) % k)
      let τ := xor (xor (old 6) (old 7)) (old 8)
      let α := xor (xor (xor (old 5) (old 6)) (old 7))
        (xor ((rot k 0 ref.val).testBit ((starts i + 6) % k)) ((constant 1).val.testBit ((starts i + 6) % k)))
      let β := xor τ
        (xor ((rot k 0 ref.val).testBit ((starts i + 7) % k)) ((constant 1).val.testBit ((starts i + 7) % k)))
      τ = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
        xor (first 4) (first 5) = !α ∧ first 4 = β) →
    ∀ (pin : Finset (Fin k)),
    (∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i + j.val) % k) →
    (∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i + 9 + j.val) % k) →
    ∀ (active : Finset (Fin m)) (d : ℕ),
    let K := Fin (2 ^ k)
    let fiber := (Finset.univ : Finset K).filter (fun q =>
      ∀ z ∈ pin, (stateAt k constant row.val 0 q.val).testBit (z.val % k) =
        (stateAt k constant row.val 0 ref.val).testBit (z.val % k))
    let target := fun (q : K) => par (∑ i ∈ active,
      ((stateAt k constant row.val 2 q.val).testBit ((starts i + 5) % k)).toNat)
    let agree := fun (choose : ℕ → ℕ → Fin k → Bool) (leaf : ℕ → K → Bool) =>
      (fiber.filter (fun q => leaf (runP k d choose q) q == target q)).card
    let e := active.card - d
    (∀ (choose : ℕ → ℕ → Fin k → Bool) (leaf : ℕ → K → Bool),
      (∀ h, quadP k (leaf h)) →
      4 ^ e * (2 * agree choose leaf) ≤ (4 ^ e + 3 ^ e) * fiber.card) ∧
    (∃ (fixed : ℕ → Fin k → Bool) (leaf : ℕ → K → Bool),
      (∀ h, quadP k (leaf h)) ∧
      (∀ t, (Finset.univ.filter (fun z : Fin k => fixed t z)).card ≤ 1) ∧
      4 ^ e * (2 * agree (fun t _ => fixed t) leaf) = (4 ^ e + 3 ^ e) * fiber.card) := by
  intro k hk constant m starts hinj row ref hgood pin hpin_in hpin_out active d K fiber target agree
    e

  have hk12 : Fin m → 12 ≤ k := fun i0 => by
    let g : Fin m × Fin 12 → Fin k := fun z => ⟨(starts z.1 + z.2.val) % k, Nat.mod_lt _ hk⟩
    have hg : Function.Injective g := fun z₁ z₂ h => hinj (congr_arg Fin.val h)
    have hc := Fintype.card_le_of_injective g hg
    simp only [Fintype.card_prod, Fintype.card_fin] at hc
    have hm : 1 ≤ m := Nat.one_le_of_lt i0.isLt
    nlinarith

  have hformula : ∀ i : Fin m, ∃ (s0 s1 s2 c0 l0 l1 l2 : Bool), ∀ key ∈ fiber,
      (stateAt k constant row.val 2 key.val).testBit ((starts i + 5) % k) =
        xor ((xor (key.val.testBit ((starts i + 8) % k)) s0) &&
            (xor (key.val.testBit ((starts i + 9) % k)) s1) &&
            (xor (key.val.testBit ((starts i + 10) % k)) s2))
          (xor (xor (xor c0 (l0 && key.val.testBit ((starts i + 8) % k)))
            (l1 && key.val.testBit ((starts i + 9) % k)))
            (l2 && key.val.testBit ((starts i + 10) % k))) := by
    intro i
    rcases guarded_two_round_formula (hk12 i) constant row ref (starts i) (hgood i) with
      ⟨s0, s1, s2, c0, l0, l1, l2, hf⟩
    refine ⟨s0, s1, s2, c0, l0, l1, l2, fun key hkey => hf key ?_⟩
    intro j
    rcases hpin_in i j with ⟨z, hzpin, hzval⟩
    have hz := (Finset.mem_filter.mp hkey).2 z hzpin
    rw [Nat.mod_eq_of_lt z.isLt, hzval] at hz
    exact hz
  choose s0 s1 s2 c0 l0 l1 l2 hout using hformula

  let pinRaw : Finset (Fin k) := pin.image (fun z => ⟨(z.val + k - 1) % k, Nat.mod_lt _ hk⟩)
  have hfiber_iff : ∀ q : K, q ∈ fiber ↔
      ∀ z ∈ pinRaw, q.val.testBit z.val = ref.val.testBit z.val := by
    intro q
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, pinRaw, Finset.mem_image,
      forall_exists_index, and_imp]
    have hbit : ∀ (x : K) (z : Fin k),
        (stateAt k constant row.val 0 x.val).testBit (z.val % k) =
        xor (x.val.testBit ((z.val + k - 1) % k)) (row.val.testBit z.val) := by
      intro x z
      rw [Nat.mod_eq_of_lt z.isLt, stateAt_zero, Nat.testBit_xor, testBit_rot x.isLt z.isLt]
      rcases Nat.lt_or_ge 1 k with h1 | h1
      · rw [Nat.mod_eq_of_lt h1]
      · have hk1 : k = 1 := Nat.le_antisymm h1 hk
        subst hk1
        simp only [Nat.mod_one]
    constructor
    · intro h z' z hz hq
      subst hq
      have h1 := h z hz
      rw [hbit q z, hbit ref z] at h1
      have := congr_arg (fun b => xor b (row.val.testBit z.val)) h1
      simpa [bool_xor_cancel] using this
    · intro h z hz
      rw [hbit q z, hbit ref z, h _ z hz rfl]

  let idx : Fin m → Fin 3 → Fin k := fun i j => ⟨(starts i + 8 + j.val) % k, Nat.mod_lt _ hk⟩
  have hidx : ∀ i j i' j', idx i j = idx i' j' → i = i' ∧ j = j' := by
    intro i j i' j' hEq
    have hv : (starts i + 8 + j.val) % k = (starts i' + 8 + j'.val) % k := congr_arg Fin.val hEq
    have h1 := hinj (a₁ := (i, ⟨8 + j.val, by omega⟩)) (a₂ := (i', ⟨8 + j'.val, by omega⟩)) (by
      show (starts i + (8 + j.val)) % k = (starts i' + (8 + j'.val)) % k
      rw [← Nat.add_assoc, ← Nat.add_assoc]
      exact hv)
    simp only [Prod.mk.injEq, Fin.mk.injEq] at h1
    exact ⟨h1.1, Fin.ext (by omega)⟩
  have hP : ∀ i j, idx i j ∉ pinRaw := by
    intro i j hmem
    rcases Finset.mem_image.mp hmem with ⟨z, hzpin, hzq⟩
    have h1 : (z.val + k - 1) % k = (starts i + 8 + j.val) % k := congr_arg Fin.val hzq
    have h2 : z.val = (starts i + 9 + j.val) % k := by
      have hadd : (z.val + k - 1 + 1) % k = z.val := by
        have : z.val + k - 1 + 1 = z.val + k := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt z.isLt]
      have hadd2 : (starts i + 8 + j.val + 1) % k = (starts i + 9 + j.val) % k := by
        congr 1; omega
      rw [← hadd, ← Nat.mod_add_mod, h1, Nat.mod_add_mod, hadd2]
    exact hpin_out i j z hzpin h2
  let out : K → Fin m → Bool := fun q i =>
    (stateAt k constant row.val 2 q.val).testBit ((starts i + 5) % k)
  have hout' : ∀ q ∈ fiber, ∀ i, out q i = winOut (fun j => q.val.testBit (idx i j).val)
      ![s0 i, s1 i, s2 i] ![l0 i, l1 i, l2 i] (c0 i) := fun q hq i => hout i q hq
  exact ⟨fun choose leaf hleaf =>
      claim1 fiber pinRaw ref hfiber_iff idx hidx hP _ _ c0 out hout' active d choose leaf hleaf,
    claim2 fiber pinRaw ref hfiber_iff idx hidx hP _ _ c0 out hout' active d⟩

end PEqualNP.Outside.L_meta_25637_aux

open PEqualNP.Outside.L_meta_25637_aux in
theorem PEqualNP.Outside.L_meta_25637 : ∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc cell =>
      acc ||| ((xor (word.testBit cell)
        (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))).toNat <<< cell)) 0
  let state := fun (row rounds key : Nat) =>
    (List.range rounds).foldl (fun prev tick =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * tick) key ^^^
        (constant (tick + 1)).val) (rot 1 key ^^^ row)
  let injected := fun (round key pos : Nat) =>
    xor ((rot (2 * (round - 1)) key).testBit (pos % k))
      ((constant round).val.testBit (pos % k))
  let bit := fun (row round key pos : Nat) => (state row round key).testBit (pos % k)
  ∀ (m : Nat) (starts : Fin m → Nat),
  Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val)%k) →
  let good := fun (row ref : Fin (2^k)) (p : Nat) =>
    let old := fun (j : Nat) => bit row.val 0 ref.val (p+j)
    let first := fun (j : Nat) => bit row.val 1 ref.val (p+j)
    let τ := xor (xor (old 6) (old 7)) (old 8)
    let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injected 1 ref.val (p+6))
    let β := xor τ (injected 1 ref.val (p+7))
    τ = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
      xor (first 4) (first 5) = !α ∧ first 4 = β
  ∀ (row ref : Fin (2^k)), (∀ i, good row ref (starts i)) →
  ∀ pin : Finset (Fin k),
  (∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i+j.val)%k) →
  (∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val)%k) →
  ∀ (active : Finset (Fin m)) (d : Nat),
  let K := Fin (2^k)
  let bitOf := fun (q : K) (i : Fin k) => q.val.testBit i.val
  let par := fun (n : Nat) => n % 2 == 1
  let lin := fun (mask : Fin k → Bool) (q : K) =>
    par (∑ i : Fin k, (mask i && bitOf q i).toNat)
  let quad := fun (g : K → Bool) => ∃ (b : Bool) (l : Fin k → Bool) (a : Fin k → Fin k → Bool),
    ∀ q, g q = xor (xor b (lin l q))
      (par (∑ i : Fin k, ∑ j : Fin k, (a i j && bitOf q i && bitOf q j).toNat))
  let fiber := (Finset.univ : Finset K).filter (fun q =>
    ∀ z ∈ pin, bit row.val 0 q.val z.val = bit row.val 0 ref.val z.val)
  let target := fun (q : K) => par (∑ i ∈ active, (bit row.val 2 q.val (starts i+5)).toNat)
  let run := fun (choose : Nat → Nat → Fin k → Bool) (q : K) =>
    (List.range d).foldl (fun history t =>
      history + ((lin (choose t history) q).toNat <<< t)) 0
  let agree := fun (choose : Nat → Nat → Fin k → Bool) (leaf : Nat → K → Bool) =>
    (fiber.filter (fun q => leaf (run choose q) q == target q)).card
  let e := active.card - d
  (∀ (choose : Nat → Nat → Fin k → Bool) (leaf : Nat → K → Bool),
    (∀ h, quad (leaf h)) →
    4^e * (2 * agree choose leaf) ≤ (4^e+3^e)*fiber.card) ∧
  (∃ (fixed : Nat → Fin k → Bool) (leaf : Nat → K → Bool),
    (∀ h, quad (leaf h)) ∧
    (∀ t, (Finset.univ.filter (fun z : Fin k => fixed t z)).card ≤ 1) ∧
    4^e * (2 * agree (fun t _ => fixed t) leaf) = (4^e+3^e)*fiber.card) := by
  intro k hk constant rot0 step0 state0 injected0 bit0 m starts hinj good0 row ref hgood pin hpin_in
    hpin_out active d
  exact main_proof k hk constant m starts hinj row ref hgood pin hpin_in hpin_out active d
