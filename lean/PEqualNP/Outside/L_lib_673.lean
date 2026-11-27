import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log

namespace PEqualNP.Outside.L_lib_673

private abbrev Word (n : ℕ) := Fin n → Bool
private abbrev Lit (n : ℕ) := Fin n × Bool
private abbrev CNF (n : ℕ) := Finset (Lit n × Lit n)
private abbrev B4 := Bool × Bool × Bool × Bool

private def sat {n : ℕ} (C : CNF n) (w : Word n) : Bool :=
  decide (∀ c ∈ C, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)

private def high {n : ℕ} (s : ℕ) (G : CNF n) : Prop :=
  2 ^ n * (2 ^ (s - 1) + 1) ≤
    2 ^ s * (Finset.univ.filter (fun x : Word n => sat G x = true)).card

private def nontaut {n : ℕ} (c : Lit n × Lit n) : Prop :=
  ¬ (c.1.1 = c.2.1 ∧ c.1.2 ≠ c.2.2)

private def sameClause {n : ℕ} (c d : Lit n × Lit n) : Prop :=
  (c.1 = d.1 ∧ c.2 = d.2) ∨ (c.1 = d.2 ∧ c.2 = d.1)

private def disjoint4 {n : ℕ} (c1 c2 : Lit n × Lit n) : Prop :=
  c1.1.1 ≠ c1.2.1 ∧ c1.1.1 ≠ c2.1.1 ∧ c1.1.1 ≠ c2.2.1 ∧
    c1.2.1 ≠ c2.1.1 ∧ c1.2.1 ≠ c2.2.1 ∧ c2.1.1 ≠ c2.2.1

private def hasClause {n : ℕ} (A : CNF n) (L1 L2 : Lit n) : Prop :=
  ∃ c ∈ A, nontaut c ∧ sameClause c (L1, L2)

private lemma bool_eq_not_of_ne {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all

private lemma bool_eq_of_ne_not {a b : Bool} (h : a ≠ !b) : a = b := by
  cases a <;> cases b <;> simp_all

private lemma bool_not_ne_self (b : Bool) : (!b) ≠ b := by
  cases b <;> decide

private lemma card_word (n : ℕ) : Fintype.card (Word n) = 2 ^ n := by
  simp [Word]

private lemma card_filter_add_not {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    (s.filter P).card + (s.filter (fun x => ¬ P x)).card = s.card := by
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  calc
    ∑ x ∈ s, ((if P x then (1 : ℕ) else 0) + if ¬ P x then 1 else 0) = ∑ _x ∈ s, (1 : ℕ) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : P x <;> simp [hx]
    _ = s.card := by simp

private lemma involution_two_mul_card_le {α : Type*} [Fintype α]
    (P : α → Prop) [DecidablePred P]
    (f : α → α) (hinv : ∀ x, f (f x) = x) (hdisj : ∀ x, P x → ¬ P (f x)) :
    2 * (Finset.univ.filter P).card ≤ Fintype.card α := by
  have hle : (Finset.univ.filter P).card ≤ (Finset.univ.filter (fun x => ¬ P x)).card := by
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hdisj x hx
    · intro x _ y _ hxy
      have := congrArg f hxy
      rwa [hinv x, hinv y] at this
  have htot := card_filter_add_not (Finset.univ : Finset α) P
  rw [Finset.card_univ] at htot
  omega

private lemma pow_succ_bernoulli (m : ℕ) : ∀ k : ℕ, m ^ (k + 1) + (k + 1) * m ^ k ≤ (m + 1) ^ (k + 1)
  | 0 => by simp
  | k + 1 => by
    have ih := pow_succ_bernoulli m k
    have hmul : (m + 1) * (m ^ (k + 1) + (k + 1) * m ^ k) ≤ (m + 1) ^ (k + 1 + 1) := by
      rw [pow_succ' (m + 1) (k + 1)]
      exact Nat.mul_le_mul_left (m + 1) ih
    have hexp : (m + 1) * (m ^ (k + 1) + (k + 1) * m ^ k) =
        m ^ (k + 1 + 1) + (k + 1 + 1) * m ^ (k + 1) + (k + 1) * m ^ k := by
      have h1 : (m + 1) * (m ^ (k + 1) + (k + 1) * m ^ k) =
          m * m ^ (k + 1) + m * ((k + 1) * m ^ k) + m ^ (k + 1) + (k + 1) * m ^ k := by
        rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, Nat.one_mul, Nat.one_mul]
        omega
      have h2 : m * m ^ (k + 1) = m ^ (k + 1 + 1) := (pow_succ' m (k + 1)).symm
      have h3 : m * ((k + 1) * m ^ k) = (k + 1) * m ^ (k + 1) := by
        rw [mul_left_comm, ← pow_succ']
      have h4 : (k + 1) * m ^ (k + 1) + m ^ (k + 1) = (k + 1 + 1) * m ^ (k + 1) := by
        rw [Nat.add_mul (k + 1) 1 (m ^ (k + 1)), Nat.one_mul]
      omega
    omega

private lemma pow_le_of_mul_le (t k Q M : ℕ) (ht : 1 ≤ t) (hM : t * M ≤ (t - 1) * Q) :
    2 ^ k * M ^ (t * k) ≤ Q ^ (t * k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' ht
  have hbern : 2 * m ^ (m + 1) ≤ (m + 1) ^ (m + 1) := by
    have h1 := pow_succ_bernoulli m m
    have h2 : (m + 1) * m ^ m = m ^ (m + 1) + m ^ m := by
      rw [Nat.add_mul, Nat.one_mul, ← pow_succ']
    omega
  have hk : 2 ^ k * m ^ ((m + 1) * k) ≤ (m + 1) ^ ((m + 1) * k) := by
    have hpow := Nat.pow_le_pow_left hbern k
    rw [mul_pow, ← pow_mul, ← pow_mul] at hpow
    exact hpow
  have hM' : (m + 1) * M ≤ m * Q := by simpa using hM
  have hpowM : ((m + 1) * M) ^ ((m + 1) * k) ≤ (m * Q) ^ ((m + 1) * k) :=
    Nat.pow_le_pow_left hM' ((m + 1) * k)
  rw [mul_pow, mul_pow] at hpowM
  have hcomb : (m + 1) ^ ((m + 1) * k) * (2 ^ k * M ^ ((m + 1) * k)) ≤
      (m + 1) ^ ((m + 1) * k) * Q ^ ((m + 1) * k) :=
    calc
      (m + 1) ^ ((m + 1) * k) * (2 ^ k * M ^ ((m + 1) * k))
        = 2 ^ k * ((m + 1) ^ ((m + 1) * k) * M ^ ((m + 1) * k)) := by ac_rfl
      _ ≤ 2 ^ k * (m ^ ((m + 1) * k) * Q ^ ((m + 1) * k)) := Nat.mul_le_mul_left (2 ^ k) hpowM
      _ = (2 ^ k * m ^ ((m + 1) * k)) * Q ^ ((m + 1) * k) := by ac_rfl
      _ ≤ (m + 1) ^ ((m + 1) * k) * Q ^ ((m + 1) * k) := Nat.mul_le_mul_right _ hk
  exact Nat.le_of_mul_le_mul_left hcomb (Nat.pow_pos (Nat.succ_pos m))

private lemma poly_succ_sq (a : ℕ) : a * (a + 2) + 1 = (a + 1) ^ 2 := by
  rw [sq, Nat.mul_add, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, mul_comm a 2]
  omega

private lemma poly_cubic_le (a : ℕ) :
    a * (a + 2) ^ 2 ≤ (a + 1) * (a * (a + 2) + (a + 1)) := by
  have h1 : a * (a + 2) ^ 2 = a * (a * a) + 4 * (a * a) + 4 * a := by
    rw [sq]
    have h2 : (a + 2) * (a + 2) = a * a + 4 * a + 4 := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, mul_comm a 2]
      omega
    rw [h2, Nat.mul_add, Nat.mul_add, mul_left_comm a 4 a, mul_comm a 4]
  have h2 : (a + 1) * (a * (a + 2) + (a + 1)) = a * (a * a) + 4 * (a * a) + 4 * a + 1 := by
    have hm : a * (a + 2) + (a + 1) = a * a + 3 * a + 1 := by
      rw [Nat.mul_add, mul_comm a 2]
      omega
    rw [hm, Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one,
      mul_left_comm a 3 a]
    omega
  omega

private lemma succ_pow_succ_le_four (m : ℕ) (hm : 1 ≤ m) :
    (m + 1) ^ (m + 1) ≤ 4 * m ^ (m + 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hm
  clear hm
  induction d with
  | zero => decide
  | succ d ih =>
    let a := d + 1
    have ha_pos : 0 < a + 1 := Nat.succ_pos a
    have hstep : (a + 2) ^ (a + 2) * a ^ (a + 1) ≤ (a + 1) ^ (2 * a + 3) := by
      let A := a * (a + 2)
      have hA1 : A + 1 = (a + 1) ^ 2 := poly_succ_sq a
      have hbern := pow_succ_bernoulli A a
      rw [hA1, ← pow_mul] at hbern
      have hmul_poly : a * (a + 2) ^ 2 ≤ (a + 1) * (A + (a + 1)) := poly_cubic_le a
      have hA_pow : A ^ a = a ^ a * (a + 2) ^ a := mul_pow a (a + 2) a
      have hLHS : (a + 2) ^ (a + 2) * a ^ (a + 1) = A ^ a * (a * (a + 2) ^ 2) := by
        rw [hA_pow, pow_add (a + 2) a 2, pow_succ a a]
        ac_rfl
      have hRHS : (a + 1) ^ (2 * a + 3) = (a + 1) * (a + 1) ^ (2 * (a + 1)) := by
        have he : 2 * a + 3 = 2 * (a + 1) + 1 := by omega
        rw [he, pow_succ']
      have hmid : A ^ (a + 1) + (a + 1) * A ^ a = A ^ a * (A + (a + 1)) := by
        rw [pow_succ, Nat.mul_add, mul_comm (a + 1) (A ^ a)]
      rw [hLHS, hRHS]
      calc
        A ^ a * (a * (a + 2) ^ 2)
          ≤ A ^ a * ((a + 1) * (A + (a + 1))) := Nat.mul_le_mul_left _ hmul_poly
        _ = (a + 1) * (A ^ a * (A + (a + 1))) := by ac_rfl
        _ = (a + 1) * (A ^ (a + 1) + (a + 1) * A ^ a) := by rw [hmid]
        _ ≤ (a + 1) * (a + 1) ^ (2 * (a + 1)) := Nat.mul_le_mul_left _ hbern
    have hcomb : (a + 1) ^ (a + 1) * (a + 2) ^ (a + 2) ≤
        (a + 1) ^ (a + 1) * (4 * (a + 1) ^ (a + 2)) := by
      have hih : (a + 1) ^ (a + 1) ≤ 4 * a ^ (a + 1) := ih
      have hexp : 2 * a + 3 = (a + 1) + (a + 2) := by omega
      calc
        (a + 1) ^ (a + 1) * (a + 2) ^ (a + 2)
          ≤ (4 * a ^ (a + 1)) * (a + 2) ^ (a + 2) := Nat.mul_le_mul_right _ hih
        _ = 4 * ((a + 2) ^ (a + 2) * a ^ (a + 1)) := by ac_rfl
        _ ≤ 4 * (a + 1) ^ (2 * a + 3) := Nat.mul_le_mul_left 4 hstep
        _ = 4 * ((a + 1) ^ (a + 1) * (a + 1) ^ (a + 2)) := by rw [hexp, pow_add]
        _ = (a + 1) ^ (a + 1) * (4 * (a + 1) ^ (a + 2)) := by ac_rfl
    exact Nat.le_of_mul_le_mul_left hcomb (Nat.pow_pos ha_pos)

private lemma pow_le_four_mul_pred_pow (s k : ℕ) (hs : 2 ≤ s) (hk : k ≤ s - 1) :
    s ^ k ≤ 4 * (s - 1) ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hs
  have hsm : m + 2 - 1 = m + 1 := by omega
  rw [hsm]
  have hm1 : 1 ≤ m + 1 := by omega
  have h1 := succ_pow_succ_le_four (m + 1) hm1
  have h2 : (m + 2) ^ (m + 1) ≤ 4 * (m + 1) ^ (m + 1) := by
    have hmul : (m + 2) * (m + 2) ^ (m + 1) ≤ (m + 2) * (4 * (m + 1) ^ (m + 1)) := by
      calc
        (m + 2) * (m + 2) ^ (m + 1)
          = (m + 2) ^ ((m + 1) + 1) := (pow_succ' _ _).symm
        _ ≤ 4 * (m + 1) ^ ((m + 1) + 1) := h1
        _ = (m + 1) * (4 * (m + 1) ^ (m + 1)) := by rw [pow_succ']; ac_rfl
        _ ≤ (m + 2) * (4 * (m + 1) ^ (m + 1)) :=
          Nat.mul_le_mul_right _ (Nat.le_succ _)
    exact Nat.le_of_mul_le_mul_left hmul (Nat.succ_pos _)
  have hsub : k + (m + 1 - k) = m + 1 := by omega
  have hsplit : (m + 1) ^ (m + 1) = (m + 1) ^ k * (m + 1) ^ (m + 1 - k) := by
    rw [← pow_add, hsub]
  have hcomb : (m + 2) ^ k * (m + 1) ^ (m + 1 - k) ≤
      (4 * (m + 1) ^ k) * (m + 1) ^ (m + 1 - k) := by
    calc
      (m + 2) ^ k * (m + 1) ^ (m + 1 - k)
        ≤ (m + 2) ^ k * (m + 2) ^ (m + 1 - k) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ _) _)
      _ = (m + 2) ^ (m + 1) := by rw [← pow_add, hsub]
      _ ≤ 4 * (m + 1) ^ (m + 1) := h2
      _ = (4 * (m + 1) ^ k) * (m + 1) ^ (m + 1 - k) := by rw [hsplit]; ac_rfl
  exact Nat.le_of_mul_le_mul_right hcomb (Nat.pow_pos (Nat.succ_pos m))

private lemma card_forall_in {α : Type*} [Fintype α] [DecidableEq α]
    (q : ℕ) (S : Finset α) :
    (Finset.univ.filter (fun f : Fin q → α => ∀ j : Fin q, f j ∈ S)).card = S.card ^ q := by
  have heq : Finset.univ.filter (fun f : Fin q → α => ∀ j : Fin q, f j ∈ S) =
      Fintype.piFinset (fun _ : Fin q => S) := by
    ext f
    simp [Fintype.mem_piFinset]
  rw [heq, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private lemma card_word_eq_on {n : ℕ} (S : Finset (Fin n)) (v : Fin n → Bool) :
    (Finset.univ.filter (fun w : Word n => ∀ i ∈ S, w i = v i)).card = 2 ^ (n - S.card) := by
  let t : Fin n → Finset Bool := fun i => if i ∈ S then {v i} else Finset.univ
  have heq : Finset.univ.filter (fun w : Word n => ∀ i ∈ S, w i = v i) = Fintype.piFinset t := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, t]
    constructor
    · intro h i
      by_cases hi : i ∈ S
      · simp [hi, h i hi]
      · simp [hi]
    · intro h i hi
      have := h i
      simpa [hi] using this
  rw [heq, Fintype.card_piFinset]
  have hcard : ∀ i : Fin n, (t i).card = if i ∈ S then 1 else 2 := by
    intro i
    dsimp only [t]
    split_ifs <;> simp
  simp_rw [hcard]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  have htot := card_filter_add_not (Finset.univ : Finset (Fin n)) (fun i => i ∈ S)
  have hS : (Finset.univ.filter (fun i : Fin n => i ∈ S)).card = S.card := by
    congr 1; ext i; simp
  rw [Finset.card_univ, Fintype.card_fin, hS] at htot
  congr 1
  omega

private lemma card_fin_hit_avoid {n s : ℕ} (hs : 0 < s) (k : Fin n) (E : Finset (Fin n))
    (hk : k ∉ E) :
    (Finset.univ.filter (fun r : Fin n → Fin s =>
      (r k).val = 0 ∧ ∀ v ∈ E, (r v).val ≠ 0)).card =
      (s - 1) ^ E.card * s ^ (n - 1 - E.card) := by
  let z0 : Fin s := ⟨0, hs⟩
  let t : Fin n → Finset (Fin s) := fun i =>
    if i = k then {z0} else if i ∈ E then Finset.univ.erase z0 else Finset.univ
  have heq : Finset.univ.filter (fun r : Fin n → Fin s =>
      (r k).val = 0 ∧ ∀ v ∈ E, (r v).val ≠ 0) = Fintype.piFinset t := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, t]
    constructor
    · rintro ⟨hrk, hrE⟩ i
      by_cases hik : i = k
      · subst hik
        simp [z0, Fin.ext_iff, hrk]
      · by_cases hiE : i ∈ E
        · simp [hik, hiE, z0, Fin.ext_iff, hrE i hiE]
        · simp [hik, hiE]
    · intro h
      refine ⟨?_, ?_⟩
      · have h1 := h k
        simp only [↓reduceIte, Finset.mem_singleton, z0, Fin.ext_iff] at h1
        exact h1
      · intro v hv
        have hvk : v ≠ k := fun he => hk (he ▸ hv)
        have h1 := h v
        simp only [hvk, ↓reduceIte, hv, Finset.mem_erase, Finset.mem_univ, and_true, z0] at h1
        exact fun h0 => h1 (Fin.ext h0)
  rw [heq, Fintype.card_piFinset]
  rw [← Finset.mul_prod_erase Finset.univ (fun i => (t i).card) (Finset.mem_univ k)]
  have htk : (t k).card = 1 := by simp [t]
  rw [htk, one_mul]
  have hrest : ∀ i ∈ Finset.univ.erase k, (t i).card = if i ∈ E then s - 1 else s := by
    intro i hi
    have hik : i ≠ k := (Finset.mem_erase.mp hi).1
    dsimp only [t]
    simp only [hik, ↓reduceIte]
    split_ifs
    · rw [Finset.card_erase_of_mem (Finset.mem_univ z0), Finset.card_univ, Fintype.card_fin]
    · rw [Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_congr rfl hrest, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hE1 : ((Finset.univ.erase k).filter (fun i => i ∈ E)).card = E.card := by
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h => h.2, fun h => ⟨fun he => hk (he ▸ h), h⟩⟩
  have htot := card_filter_add_not (Finset.univ.erase k) (fun i => i ∈ E)
  have herk : (Finset.univ.erase k).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  rw [hE1, herk] at htot
  rw [hE1]
  have hE2 : ((Finset.univ.erase k).filter (fun i => i ∉ E)).card = n - 1 - E.card := by omega
  rw [hE2]

private def toggle4 {n : ℕ} (k1 k2 k3 k4 : Fin n) (t : B4) (w : Word n) : Word n :=
  fun i =>
    if i = k1 then xor (w i) t.1
    else if i = k2 then xor (w i) t.2.1
    else if i = k3 then xor (w i) t.2.2.1
    else if i = k4 then xor (w i) t.2.2.2
    else w i

private lemma toggle4_invol {n : ℕ} (k1 k2 k3 k4 : Fin n) (t : B4) (w : Word n) :
    toggle4 k1 k2 k3 k4 t (toggle4 k1 k2 k3 k4 t w) = w := by
  funext i
  simp only [toggle4]
  split_ifs <;> simp

private lemma card_pred4 {n : ℕ} (k1 k2 k3 k4 : Fin n)
    (h12 : k1 ≠ k2) (h13 : k1 ≠ k3) (h14 : k1 ≠ k4)
    (h23 : k2 ≠ k3) (h24 : k2 ≠ k4) (h34 : k3 ≠ k4)
    (P : B4 → Bool) :
    16 * (Finset.univ.filter (fun w : Word n => P (w k1, w k2, w k3, w k4) = true)).card =
      (Finset.univ.filter (fun t : B4 => P t = true)).card * 2 ^ n := by
  let proj : Word n → B4 := fun w => (w k1, w k2, w k3, w k4)
  let fib : B4 → Finset (Word n) := fun t => Finset.univ.filter (fun w => proj w = t)
  have hfib : ∀ t : B4, (fib t).card = (fib (false, false, false, false)).card := by
    rintro ⟨t1, t2, t3, t4⟩
    refine Finset.card_bij (fun w _ => toggle4 k1 k2 k3 k4 (t1, t2, t3, t4) w) ?_ ?_ ?_
    · intro w hw
      simp only [fib, proj, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hw ⊢
      rcases hw with ⟨hw1, hw2, hw3, hw4⟩
      simp [toggle4, h12.symm, h13.symm, h14.symm, h23.symm, h24.symm, h34.symm,
        hw1, hw2, hw3, hw4]
    · intro w1 _ w2 _ h
      have := congrArg (toggle4 k1 k2 k3 k4 (t1, t2, t3, t4)) h
      rwa [toggle4_invol, toggle4_invol] at this
    · intro w hw
      refine ⟨toggle4 k1 k2 k3 k4 (t1, t2, t3, t4) w, ?_,
        toggle4_invol k1 k2 k3 k4 (t1, t2, t3, t4) w⟩
      simp only [fib, proj, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hw ⊢
      rcases hw with ⟨hw1, hw2, hw3, hw4⟩
      simp [toggle4, h12.symm, h13.symm, h14.symm, h23.symm, h24.symm, h34.symm,
        hw1, hw2, hw3, hw4]
  have hcount : ∀ Q : B4 → Bool,
      (Finset.univ.filter (fun w : Word n => Q (proj w) = true)).card =
        (Finset.univ.filter (fun t : B4 => Q t = true)).card *
          (fib (false, false, false, false)).card := by
    intro Q
    rw [Finset.card_eq_sum_card_fiberwise (f := proj)
      (t := Finset.univ.filter (fun t : B4 => Q t = true))]
    · calc
        ∑ t ∈ Finset.univ.filter (fun t : B4 => Q t = true),
            ((Finset.univ.filter (fun w : Word n => Q (proj w) = true)).filter
              (fun w => proj w = t)).card
          = ∑ t ∈ Finset.univ.filter (fun t : B4 => Q t = true), (fib t).card := by
              refine Finset.sum_congr rfl ?_
              intro t ht
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
              congr 1
              ext w
              simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · intro h; exact h.2
              · intro h; exact ⟨h ▸ ht, h⟩
        _ = ∑ _t ∈ Finset.univ.filter (fun t : B4 => Q t = true),
              (fib (false, false, false, false)).card := by
              refine Finset.sum_congr rfl ?_
              intro t _; exact hfib t
        _ = (Finset.univ.filter (fun t : B4 => Q t = true)).card *
              (fib (false, false, false, false)).card := by
              rw [Finset.sum_const, Nat.nsmul_eq_mul]
    · intro w hw
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact hw
  have htot := hcount (fun _ => true)
  simp only [Finset.filter_true, Finset.card_univ, card_word] at htot
  have hB4' : Fintype.card B4 = 16 := by decide
  rw [hB4'] at htot
  rw [hcount P, htot]
  ac_rfl

private def predC1C2 (b1 b2 b3 b4 : Bool) (t : B4) : Bool :=
  (t.1 != b1 || t.2.1 != b2) && (t.2.2.1 != b3 || t.2.2.2 != b4)

private lemma card_predC1C2 (b1 b2 b3 b4 : Bool) :
    (Finset.univ.filter (fun t : B4 => predC1C2 b1 b2 b3 b4 t = true)).card = 9 := by
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> decide

private lemma card_predEq (v1 v2 v3 v4 : Bool) :
    (Finset.univ.filter (fun t : B4 =>
      ((t.1 == v1) && (t.2.1 == v2) && (t.2.2.1 == v3) && (t.2.2.2 == v4)) = true)).card = 1 := by
  cases v1 <;> cases v2 <;> cases v3 <;> cases v4 <;> decide

private lemma card_predNeq (v1 v2 v3 v4 : Bool) :
    (Finset.univ.filter (fun t : B4 =>
      (!((t.1 == v1) && (t.2.1 == v2) && (t.2.2.1 == v3) && (t.2.2.2 == v4))) = true)).card = 15 := by
  cases v1 <;> cases v2 <;> cases v3 <;> cases v4 <;> decide

private lemma extend_card_four {n : ℕ} (hn : 4 ≤ n) (S : Finset (Fin n)) (hS : S.card ≤ 4) :
    ∃ k1 k2 k3 k4 : Fin n,
      k1 ≠ k2 ∧ k1 ≠ k3 ∧ k1 ≠ k4 ∧ k2 ≠ k3 ∧ k2 ≠ k4 ∧ k3 ≠ k4 ∧
      ∀ i ∈ S, i = k1 ∨ i = k2 ∨ i = k3 ∨ i = k4 := by
  have hex : ∀ m : ℕ, ∀ T : Finset (Fin n), T.card + m = 4 →
      ∃ U : Finset (Fin n), T ⊆ U ∧ U.card = 4 := by
    intro m
    induction m with
    | zero =>
      intro T hT
      exact ⟨T, Finset.Subset.refl T, by omega⟩
    | succ m ih =>
      intro T hT
      have hlt : T.card < (Finset.univ : Finset (Fin n)).card := by
        rw [Finset.card_univ, Fintype.card_fin]; omega
      obtain ⟨x, _, hxT⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      obtain ⟨U, hTU, hUc⟩ := ih (insert x T) (by rw [Finset.card_insert_of_notMem hxT]; omega)
      exact ⟨U, Finset.Subset.trans (Finset.subset_insert x T) hTU, hUc⟩
  obtain ⟨U, hSU, hU4⟩ := hex (4 - S.card) S (by omega)
  have h1ne : U.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨k1, hk1⟩ := h1ne
  let U1 := U.erase k1
  have hU1c : U1.card = 3 := by rw [Finset.card_erase_of_mem hk1, hU4]
  obtain ⟨k2, hk2⟩ := Finset.card_pos.mp (show 0 < U1.card by omega)
  let U2 := U1.erase k2
  have hU2c : U2.card = 2 := by rw [Finset.card_erase_of_mem hk2, hU1c]
  obtain ⟨k3, hk3⟩ := Finset.card_pos.mp (show 0 < U2.card by omega)
  let U3 := U2.erase k3
  have hU3c : U3.card = 1 := by rw [Finset.card_erase_of_mem hk3, hU2c]
  obtain ⟨k4, hk4⟩ := Finset.card_pos.mp (show 0 < U3.card by omega)
  have hk2' := Finset.mem_erase.mp hk2
  have hk3' := Finset.mem_erase.mp hk3
  have hk3'' := Finset.mem_erase.mp hk3'.2
  have hk4' := Finset.mem_erase.mp hk4
  have hk4'' := Finset.mem_erase.mp hk4'.2
  have hk4''' := Finset.mem_erase.mp hk4''.2
  have hU3eq : U3 = {k4} := Finset.card_eq_one.mp hU3c |>.elim fun y hy => by
    rw [hy] at hk4 ⊢
    rw [Finset.mem_singleton.mp hk4]
  refine ⟨k1, k2, k3, k4, hk2'.1.symm, hk3''.1.symm, hk4'''.1.symm,
    hk3'.1.symm, hk4''.1.symm, hk4'.1.symm, ?_⟩
  intro i hi
  have hiU : i ∈ U := hSU hi
  by_cases e1 : i = k1
  · exact Or.inl e1
  · have hi1 : i ∈ U1 := Finset.mem_erase.mpr ⟨e1, hiU⟩
    by_cases e2 : i = k2
    · exact Or.inr (Or.inl e2)
    · have hi2 : i ∈ U2 := Finset.mem_erase.mpr ⟨e2, hi1⟩
      by_cases e3 : i = k3
      · exact Or.inr (Or.inr (Or.inl e3))
      · have hi3 : i ∈ U3 := Finset.mem_erase.mpr ⟨e3, hi2⟩
        rw [hU3eq, Finset.mem_singleton] at hi3
        exact Or.inr (Or.inr (Or.inr hi3))

private lemma exists_cal (n : ℕ) (hn : 3 ≤ n) :
    let qcal := 16 * (1 + 4 * (1 + Nat.clog 2 (n + 1)))
    ∃ T : Fin qcal → Word n,
      ∀ (S : Finset (Fin n)), S.card ≤ 4 → ∀ f : Word n,
        ∃ r : Fin qcal, ∀ i ∈ S, T r i = f i := by
  intro qcal
  by_cases hn3 : n = 3
  · subst hn3
    let e := Fintype.equivFin (Word 3)
    have hcard : Fintype.card (Word 3) = 8 := by rw [card_word]; decide
    have hqge : Fintype.card (Word 3) ≤ qcal := by
      rw [hcard]
      dsimp only [qcal]
      omega
    refine ⟨fun r => if h : r.val < Fintype.card (Word 3) then e.symm ⟨r.val, h⟩ else fun _ => false, ?_⟩
    intro S _ f
    let r : Fin qcal := ⟨(e f).val, lt_of_lt_of_le (e f).isLt hqge⟩
    refine ⟨r, fun i _ => ?_⟩
    have hlt : r.val < Fintype.card (Word 3) := (e f).isLt
    simp only [hlt, ↓reduceDIte, r, Fin.eta, Equiv.symm_apply_apply]
  · have hn4 : 4 ≤ n := by omega
    let L := Nat.clog 2 (n + 1)
    have hL : n + 1 ≤ 2 ^ L := Nat.le_pow_clog (by decide : 1 < 2) (n + 1)
    let Idx := (Fin n × Fin n × Fin n × Fin n) × B4
    let S_idx : Finset Idx := Finset.univ.filter fun p =>
      p.1.1 ≠ p.1.2.1 ∧ p.1.1 ≠ p.1.2.2.1 ∧ p.1.1 ≠ p.1.2.2.2 ∧
        p.1.2.1 ≠ p.1.2.2.1 ∧ p.1.2.1 ≠ p.1.2.2.2 ∧ p.1.2.2.1 ≠ p.1.2.2.2
    let badSet : Idx → Finset (Fin qcal → Word n) := fun p =>
      Finset.univ.filter fun T => ∀ r : Fin qcal,
        !((T r p.1.1 == p.2.1) && (T r p.1.2.1 == p.2.2.1) &&
          (T r p.1.2.2.1 == p.2.2.2.1) && (T r p.1.2.2.2 == p.2.2.2.2)) = true
    have hbad_card : ∀ p ∈ S_idx,
        16 ^ qcal * (badSet p).card = 15 ^ qcal * (2 ^ n) ^ qcal := by
      intro p hp
      simp only [S_idx, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rcases hp with ⟨h12, h13, h14, h23, h24, h34⟩
      let goodW : Finset (Word n) := Finset.univ.filter fun w =>
        !((w p.1.1 == p.2.1) && (w p.1.2.1 == p.2.2.1) &&
          (w p.1.2.2.1 == p.2.2.2.1) && (w p.1.2.2.2 == p.2.2.2.2)) = true
      have hbad_eq : badSet p = Finset.univ.filter (fun T : Fin qcal → Word n => ∀ r, T r ∈ goodW) := by
        ext T
        simp [badSet, goodW]
      rw [hbad_eq, card_forall_in]
      have h1 := card_pred4 p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 h12 h13 h14 h23 h24 h34
        (fun t : B4 => !((t.1 == p.2.1) && (t.2.1 == p.2.2.1) &&
          (t.2.2.1 == p.2.2.2.1) && (t.2.2.2 == p.2.2.2.2)))
      rw [card_predNeq] at h1
      change 16 * goodW.card = 15 * 2 ^ n at h1
      have hpow := congrArg (· ^ qcal) h1
      rw [mul_pow, mul_pow] at hpow
      exact hpow
    have hS_le : S_idx.card ≤ 16 * n ^ 4 := by
      have h1 : S_idx.card ≤ Fintype.card Idx := by
        rw [← Finset.card_univ]
        exact Finset.card_le_card (Finset.filter_subset _ _)
      have h2 : Fintype.card Idx = 16 * n ^ 4 := by
        have hB4' : Fintype.card B4 = 16 := by decide
        simp only [Idx, Fintype.card_prod, Fintype.card_fin, hB4']
        have h4 : n ^ 4 = n * (n * (n * n)) := by
          simp only [pow_succ, pow_zero, one_mul]
          ac_rfl
        rw [h4]
        ac_rfl
      omega
    have hunion : 16 ^ qcal * (S_idx.biUnion badSet).card ≤
        16 * n ^ 4 * (15 ^ qcal * (2 ^ n) ^ qcal) := by
      have h1 : (S_idx.biUnion badSet).card ≤ ∑ p ∈ S_idx, (badSet p).card :=
        Finset.card_biUnion_le
      calc
        16 ^ qcal * (S_idx.biUnion badSet).card
          ≤ 16 ^ qcal * ∑ p ∈ S_idx, (badSet p).card := Nat.mul_le_mul_left _ h1
        _ = ∑ p ∈ S_idx, 16 ^ qcal * (badSet p).card := Finset.mul_sum _ _ _
        _ = ∑ _p ∈ S_idx, (15 ^ qcal * (2 ^ n) ^ qcal) :=
            Finset.sum_congr rfl hbad_card
        _ = S_idx.card * (15 ^ qcal * (2 ^ n) ^ qcal) := by rw [Finset.sum_const, Nat.nsmul_eq_mul]
        _ ≤ 16 * n ^ 4 * (15 ^ qcal * (2 ^ n) ^ qcal) := Nat.mul_le_mul_right _ hS_le
    have h15_16 : 2 * 15 ^ 16 ≤ 16 ^ 16 := by decide
    let m := 1 + 4 * (1 + L)
    have hpow_m : 2 ^ m * 15 ^ qcal ≤ 16 ^ qcal := by
      have h := Nat.pow_le_pow_left h15_16 m
      rw [mul_pow, ← pow_mul, ← pow_mul] at h
      exact h
    have hn4_lt : 16 * n ^ 4 < 2 ^ m := by
      have hnlt : n < 2 ^ L := by omega
      have hpow4 : n ^ 4 < (2 ^ L) ^ 4 := Nat.pow_lt_pow_left hnlt (by decide)
      rw [← pow_mul] at hpow4
      have h16_eq : 16 * 2 ^ (L * 4) = 2 ^ (4 + 4 * L) := by
        have h24 : (16 : ℕ) = 2 ^ 4 := by decide
        rw [h24, ← pow_add, mul_comm L 4]
      have hm_eq : m = (4 + 4 * L) + 1 := by dsimp only [m]; omega
      have hmul := Nat.mul_lt_mul_of_pos_left hpow4 (by decide : 0 < 16)
      rw [h16_eq] at hmul
      rw [hm_eq, pow_succ]
      exact lt_of_lt_of_le hmul (Nat.le_mul_of_pos_right _ (by decide))
    have hstrict : 16 ^ qcal * (S_idx.biUnion badSet).card < 16 ^ qcal * (2 ^ n) ^ qcal := by
      have hpos1 : 0 < 15 ^ qcal * (2 ^ n) ^ qcal :=
        Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (Nat.pow_pos (by decide)))
      calc
        16 ^ qcal * (S_idx.biUnion badSet).card
          ≤ 16 * n ^ 4 * (15 ^ qcal * (2 ^ n) ^ qcal) := hunion
        _ < 2 ^ m * (15 ^ qcal * (2 ^ n) ^ qcal) := Nat.mul_lt_mul_of_pos_right hn4_lt hpos1
        _ = (2 ^ m * 15 ^ qcal) * (2 ^ n) ^ qcal := by ac_rfl
        _ ≤ 16 ^ qcal * (2 ^ n) ^ qcal := Nat.mul_le_mul_right _ hpow_m
    have hlt_card : (S_idx.biUnion badSet).card < (Finset.univ : Finset (Fin qcal → Word n)).card := by
      have htot : (Finset.univ : Finset (Fin qcal → Word n)).card = (2 ^ n) ^ qcal := by
        rw [Finset.card_univ, Fintype.card_fun, card_word, Fintype.card_fin]
      rw [htot]
      exact Nat.lt_of_mul_lt_mul_left hstrict
    obtain ⟨T, _, hT⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt_card
    refine ⟨T, ?_⟩
    intro S hS f
    obtain ⟨k1, k2, k3, k4, h12, h13, h14, h23, h24, h34, hcov⟩ := extend_card_four hn4 S hS
    let p : Idx := ((k1, k2, k3, k4), (f k1, f k2, f k3, f k4))
    have hpS : p ∈ S_idx := by
      simp only [S_idx, Finset.mem_filter, Finset.mem_univ, true_and, p]
      exact ⟨h12, h13, h14, h23, h24, h34⟩
    have hTnot : T ∉ badSet p := fun hmem => hT (Finset.mem_biUnion.mpr ⟨p, hpS, hmem⟩)
    simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and, p,
      Bool.not_eq_true', not_forall] at hTnot
    obtain ⟨r, hr⟩ := hTnot
    have hmatch : T r k1 = f k1 ∧ T r k2 = f k2 ∧ T r k3 = f k3 ∧ T r k4 = f k4 := by
      by_contra h
      apply hr
      cases e1 : (T r k1 == f k1) <;> cases e2 : (T r k2 == f k2) <;>
        cases e3 : (T r k3 == f k3) <;> cases e4 : (T r k4 == f k4) <;> simp_all
    refine ⟨r, fun i hi => ?_⟩
    rcases hcov i hi with rfl | rfl | rfl | rfl
    · exact hmatch.1
    · exact hmatch.2.1
    · exact hmatch.2.2.1
    · exact hmatch.2.2.2

private lemma sat_iff_nontaut {n : ℕ} (A : CNF n) (w : Word n) :
    sat A w = true ↔ ∀ c ∈ A, nontaut c → w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2 := by
  simp only [sat, decide_eq_true_eq]
  constructor
  · intro h c hc _; exact h c hc
  · intro h c hc
    by_cases hnt : nontaut c
    · exact h c hc hnt
    · simp only [nontaut, not_not] at hnt
      rcases hnt with ⟨h1, h2⟩
      rw [← h1]
      cases hw : w c.1.1 <;> cases hb1 : c.1.2 <;> cases hb2 : c.2.2 <;> simp_all

private lemma no_unit_of_above_half {n : ℕ} (A : CNF n)
    (hN : 2 ^ n < 2 * (Finset.univ.filter (fun w => sat A w = true)).card)
    (c : Lit n × Lit n) (hc : c ∈ A) (hnt : nontaut c) : c.1.1 ≠ c.2.1 := by
  intro heq
  have hb : c.1.2 = c.2.2 := by
    by_contra hne
    exact hnt ⟨heq, hne⟩
  let f : Word n → Word n := fun w i => if i = c.1.1 then !(w i) else w i
  have hinv : ∀ w, f (f w) = w := by
    intro w; funext i; simp only [f]; split_ifs <;> simp
  have hdisj : ∀ w, sat A w = true → ¬ sat A (f w) = true := by
    intro w hw hfw
    have h1 := (sat_iff_nontaut A w).mp hw c hc hnt
    have h2 := (sat_iff_nontaut A (f w)).mp hfw c hc hnt
    simp [f, ← heq, ← hb] at h1 h2
    cases hwi : w c.1.1 <;> cases hc1 : c.1.2 <;> simp_all
  have hle := involution_two_mul_card_le (fun w => sat A w = true) f hinv hdisj
  rw [card_word] at hle
  omega

private lemma no_shared_var_opp {n : ℕ} (A : CNF n)
    (hN : 2 ^ n < 2 * (Finset.univ.filter (fun w => sat A w = true)).card)
    (i j1 j2 : Fin n) (b1 d1 d2 : Bool) (hj1 : j1 ≠ i) (hj2 : j2 ≠ i)
    (h1 : ∀ w, sat A w = true → w i ≠ b1 ∨ w j1 ≠ d1)
    (h2 : ∀ w, sat A w = true → w i ≠ !b1 ∨ w j2 ≠ d2) : False := by
  let f : Word n → Word n := fun w k =>
    if w i = b1 then (if k = j1 then !(w k) else w k)
    else (if k = j2 then !(w k) else w k)
  have hfi : ∀ w, f w i = w i := by
    intro w
    simp only [f]
    split_ifs <;> simp_all [hj1.symm, hj2.symm]
  have hinv : ∀ w, f (f w) = w := by
    intro w
    funext k
    simp only [f, hfi w]
    split_ifs <;> simp
  have hdisj : ∀ w, sat A w = true → ¬ sat A (f w) = true := by
    intro w hw hfw
    by_cases hwi : w i = b1
    · have h1w := h1 w hw
      have h1f := h1 (f w) hfw
      have hfwi : f w i = b1 := by rw [hfi, hwi]
      have hfwj : f w j1 = !(w j1) := by simp [f, hwi]
      rw [hwi] at h1w
      rw [hfwi, hfwj] at h1f
      cases hwj : w j1 <;> cases d1 <;> simp_all
    · have hwi' : w i = !b1 := by cases h : w i <;> cases b1 <;> simp_all
      have h2w := h2 w hw
      have h2f := h2 (f w) hfw
      have hfwi : f w i = !b1 := by rw [hfi, hwi']
      have hfwj : f w j2 = !(w j2) := by simp [f, hwi]
      rw [hwi'] at h2w
      rw [hfwi, hfwj] at h2f
      cases hwj : w j2 <;> cases d2 <;> simp_all
  have hle := involution_two_mul_card_le (fun w => sat A w = true) f hinv hdisj
  rw [card_word] at hle
  omega

private lemma exists_fix_one_in {n : ℕ}
    (i1 i2 i3 i4 ja jb : Fin n) (b1 b2 b3 b4 da db : Bool)
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h14 : i1 ≠ i4)
    (h23 : i2 ≠ i3) (_h24 : i2 ≠ i4) (h34 : i3 ≠ i4)
    (hja : ja = i1 ∨ ja = i2 ∨ ja = i3 ∨ ja = i4)
    (hjb1 : jb ≠ i1) (hjb2 : jb ≠ i2) (hjb3 : jb ≠ i3) (hjb4 : jb ≠ i4) :
    ∃ (k1 k2 k3 k4 : Fin n) (v1 v2 v3 v4 : Bool),
      k1 ≠ k2 ∧ k1 ≠ k3 ∧ k1 ≠ k4 ∧ k2 ≠ k3 ∧ k2 ≠ k4 ∧ k3 ≠ k4 ∧
      ∀ w : Word n, w k1 = v1 → w k2 = v2 → w k3 = v3 → w k4 = v4 →
        (w i1 ≠ b1 ∨ w i2 ≠ b2) ∧ (w i3 ≠ b3 ∨ w i4 ≠ b4) ∧ w ja = da ∧ w jb = db := by
  rcases hja with hja | hja | hja | hja
  · rw [hja]
    refine ⟨i1, i2, i3, jb, da, !b2, !b3, db,
      h12, h13, hjb1.symm, h23, hjb2.symm, hjb3.symm, ?_⟩
    intro w h1 h2 h3 h4
    exact ⟨Or.inr (by rw [h2]; cases b2 <;> decide),
      Or.inl (by rw [h3]; cases b3 <;> decide), h1, h4⟩
  · rw [hja]
    refine ⟨i1, i2, i3, jb, !b1, da, !b3, db,
      h12, h13, hjb1.symm, h23, hjb2.symm, hjb3.symm, ?_⟩
    intro w h1 h2 h3 h4
    exact ⟨Or.inl (by rw [h1]; cases b1 <;> decide),
      Or.inl (by rw [h3]; cases b3 <;> decide), h2, h4⟩
  · rw [hja]
    refine ⟨i1, i3, i4, jb, !b1, da, !b4, db,
      h13, h14, hjb1.symm, h34, hjb3.symm, hjb4.symm, ?_⟩
    intro w h1 h2 h3 h4
    exact ⟨Or.inl (by rw [h1]; cases b1 <;> decide),
      Or.inr (by rw [h3]; cases b4 <;> decide), h2, h4⟩
  · rw [hja]
    refine ⟨i1, i3, i4, jb, !b1, !b3, da, db,
      h13, h14, hjb1.symm, h34, hjb3.symm, hjb4.symm, ?_⟩
    intro w h1 h2 h3 h4
    exact ⟨Or.inl (by rw [h1]; cases b1 <;> decide),
      Or.inl (by rw [h2]; cases b3 <;> decide), h3, h4⟩

private lemma exists_fix_third_clause {n : ℕ}
    (i1 i2 i3 i4 j1 j2 : Fin n) (b1 b2 b3 b4 d1 d2 : Bool)
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h14 : i1 ≠ i4)
    (h23 : i2 ≠ i3) (h24 : i2 ≠ i4) (h34 : i3 ≠ i4)
    (hj12 : j1 ≠ j2)
    (hns1 : ¬ sameClause ((j1, d1), (j2, d2)) ((i1, b1), (i2, b2)))
    (hns2 : ¬ sameClause ((j1, d1), (j2, d2)) ((i3, b3), (i4, b4))) :
    ∃ (k1 k2 k3 k4 : Fin n) (v1 v2 v3 v4 : Bool),
      k1 ≠ k2 ∧ k1 ≠ k3 ∧ k1 ≠ k4 ∧ k2 ≠ k3 ∧ k2 ≠ k4 ∧ k3 ≠ k4 ∧
      ∀ w : Word n, w k1 = v1 → w k2 = v2 → w k3 = v3 → w k4 = v4 →
        (w i1 ≠ b1 ∨ w i2 ≠ b2) ∧ (w i3 ≠ b3 ∨ w i4 ≠ b4) ∧ w j1 = d1 ∧ w j2 = d2 := by
  by_cases hj1 : j1 = i1 ∨ j1 = i2 ∨ j1 = i3 ∨ j1 = i4
  · by_cases hj2 : j2 = i1 ∨ j2 = i2 ∨ j2 = i3 ∨ j2 = i4
    · let v1 : Bool := if j1 = i1 then d1 else if j2 = i1 then d2 else !b1
      let v2 : Bool := if j1 = i2 then d1 else if j2 = i2 then d2 else !b2
      let v3 : Bool := if j1 = i3 then d1 else if j2 = i3 then d2 else !b3
      let v4 : Bool := if j1 = i4 then d1 else if j2 = i4 then d2 else !b4
      refine ⟨i1, i2, i3, i4, v1, v2, v3, v4, h12, h13, h14, h23, h24, h34, ?_⟩
      intro w hw1 hw2 hw3 hw4
      have hsat1 : v1 ≠ b1 ∨ v2 ≠ b2 := by
        by_contra h
        push Not at h
        rcases h with ⟨hv1, hv2⟩
        by_cases ha1 : j1 = i1
        · subst ha1
          have h1d : d1 = b1 := by simpa [v1] using hv1
          by_cases hb2 : j2 = i2
          · subst hb2
            have h2d : d2 = b2 := by simpa [v2, hj12] using hv2
            exact hns1 (Or.inl ⟨by simp [h1d], by simp [h2d]⟩)
          · simp [v2, h12, hb2] at hv2
        · by_cases hb1 : j2 = i1
          · subst hb1
            have h2d : d2 = b1 := by simpa [v1, ha1] using hv1
            by_cases ha2 : j1 = i2
            · subst ha2
              have h1d : d1 = b2 := by simpa [v2] using hv2
              exact hns1 (Or.inr ⟨by simp [h1d], by simp [h2d]⟩)
            · simp [v2, ha2, h12] at hv2
          · simp [v1, ha1, hb1] at hv1
      have hsat2 : v3 ≠ b3 ∨ v4 ≠ b4 := by
        by_contra h
        push Not at h
        rcases h with ⟨hv3, hv4⟩
        by_cases ha3 : j1 = i3
        · subst ha3
          have h1d : d1 = b3 := by simpa [v3] using hv3
          by_cases hb4 : j2 = i4
          · subst hb4
            have h2d : d2 = b4 := by simpa [v4, hj12] using hv4
            exact hns2 (Or.inl ⟨by simp [h1d], by simp [h2d]⟩)
          · simp [v4, h34, hb4] at hv4
        · by_cases hb3 : j2 = i3
          · subst hb3
            have h2d : d2 = b3 := by simpa [v3, ha3] using hv3
            by_cases ha4 : j1 = i4
            · subst ha4
              have h1d : d1 = b4 := by simpa [v4] using hv4
              exact hns2 (Or.inr ⟨by simp [h1d], by simp [h2d]⟩)
            · simp [v4, ha4, h34] at hv4
          · simp [v3, ha3, hb3] at hv3
      have hwj1 : w j1 = d1 := by
        rcases hj1 with rfl | rfl | rfl | rfl
        · simpa [v1] using hw1
        · simpa [v2] using hw2
        · simpa [v3] using hw3
        · simpa [v4] using hw4
      have hwj2 : w j2 = d2 := by
        rcases hj2 with rfl | rfl | rfl | rfl
        · simpa [v1, hj12] using hw1
        · simpa [v2, hj12] using hw2
        · simpa [v3, hj12] using hw3
        · simpa [v4, hj12] using hw4
      exact ⟨by rwa [hw1, hw2], by rwa [hw3, hw4], hwj1, hwj2⟩
    · push Not at hj2
      exact exists_fix_one_in i1 i2 i3 i4 j1 j2 b1 b2 b3 b4 d1 d2
        h12 h13 h14 h23 h24 h34 hj1 hj2.1 hj2.2.1 hj2.2.2.1 hj2.2.2.2
  · push Not at hj1
    by_cases hj2 : j2 = i1 ∨ j2 = i2 ∨ j2 = i3 ∨ j2 = i4
    · rcases exists_fix_one_in i1 i2 i3 i4 j2 j1 b1 b2 b3 b4 d2 d1
        h12 h13 h14 h23 h24 h34 hj2 hj1.1 hj1.2.1 hj1.2.2.1 hj1.2.2.2 with
        ⟨k1, k2, k3, k4, v1, v2, v3, v4, hk12, hk13, hk14, hk23, hk24, hk34, h⟩
      refine ⟨k1, k2, k3, k4, v1, v2, v3, v4, hk12, hk13, hk14, hk23, hk24, hk34, ?_⟩
      intro w h1 h2 h3 h4
      rcases h w h1 h2 h3 h4 with ⟨hs1, hs2, hwb, hwa⟩
      exact ⟨hs1, hs2, hwa, hwb⟩
    · push Not at hj2
      refine ⟨i1, i3, j1, j2, !b1, !b3, d1, d2,
        h13, hj1.1.symm, hj2.1.symm, hj1.2.2.1.symm, hj2.2.2.1.symm, hj12, ?_⟩
      intro w h1 h2 h3 h4
      exact ⟨Or.inl (by rw [h1]; cases b1 <;> decide),
        Or.inl (by rw [h2]; cases b3 <;> decide), h3, h4⟩

private lemma exists_fix_unit_third {n : ℕ}
    (i1 i2 i3 i4 j : Fin n) (b1 b2 b3 b4 d : Bool)
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h14 : i1 ≠ i4)
    (h23 : i2 ≠ i3) (h24 : i2 ≠ i4) (h34 : i3 ≠ i4) :
    ∃ (S : Finset (Fin n)) (f : Word n), S.card ≤ 4 ∧
      ∀ w : Word n, (∀ i ∈ S, w i = f i) →
        (w i1 ≠ b1 ∨ w i2 ≠ b2) ∧ (w i3 ≠ b3 ∨ w i4 ≠ b4) ∧ w j = d := by
  let f : Word n := fun k =>
    if k = j then d
    else if k = i1 then !b1
    else if k = i2 then !b2
    else if k = i3 then !b3
    else !b4
  by_cases hj1 : j = i1
  · refine ⟨{i1, i2, i3}, f, by
      exact le_trans (Finset.card_insert_le _ _)
        (by exact Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) (by simp))), ?_⟩
    intro w hw
    have hw1 : w i1 = d := by simpa [f, hj1] using hw i1 (by simp)
    have hw2 : w i2 = !b2 := by simpa [f, hj1, h12.symm] using hw i2 (by simp)
    have hw3 : w i3 = !b3 := by simpa [f, hj1, h13.symm, h23.symm] using hw i3 (by simp)
    exact ⟨Or.inr (by rw [hw2]; cases b2 <;> decide),
      Or.inl (by rw [hw3]; cases b3 <;> decide), hj1 ▸ hw1⟩
  · by_cases hj3 : j = i3
    · refine ⟨{i1, i3, i4}, f, by
        exact le_trans (Finset.card_insert_le _ _)
          (by exact Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) (by simp))), ?_⟩
      intro w hw
      have hw1 : w i1 = !b1 := by simpa [f, hj3, h13] using hw i1 (by simp)
      have hw3 : w i3 = d := by simpa [f, hj3] using hw i3 (by simp)
      have hw4 : w i4 = !b4 := by
        simpa [f, hj3, h34.symm, h14.symm, h24.symm] using hw i4 (by simp)
      exact ⟨Or.inl (by rw [hw1]; cases b1 <;> decide),
        Or.inr (by rw [hw4]; cases b4 <;> decide), hj3 ▸ hw3⟩
    · refine ⟨{j, i1, i3}, f, by
        exact le_trans (Finset.card_insert_le _ _)
          (by exact Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) (by simp))), ?_⟩
      intro w hw
      have hwj : w j = d := by simpa [f] using hw j (by simp)
      have hw1 : w i1 = !b1 := by simpa [f, Ne.symm hj1] using hw i1 (by simp)
      have hw3 : w i3 = !b3 := by
        simpa [f, Ne.symm hj3, h13.symm, h23.symm] using hw i3 (by simp)
      exact ⟨Or.inl (by rw [hw1]; cases b1 <;> decide),
        Or.inl (by rw [hw3]; cases b3 <;> decide), hwj⟩

private lemma high_structure {n : ℕ} (A : CNF n)
    (hN : 2 ^ n < 2 * (Finset.univ.filter (fun w => sat A w = true)).card) :
    (∀ c ∈ A, ¬ nontaut c) ∨
    (∃ L0 : Lit n, ∀ c ∈ A, nontaut c → c.1 = L0 ∨ c.2 = L0) ∨
    (∃ c1 ∈ A, ∃ c2 ∈ A, nontaut c1 ∧ nontaut c2 ∧ disjoint4 c1 c2 ∧
      ∀ c ∈ A, nontaut c → sameClause c c1 ∨ sameClause c c2) := by
  by_cases hempty : ∀ c ∈ A, ¬ nontaut c
  · exact Or.inl hempty
  by_cases hstar : ∃ L0 : Lit n, ∀ c ∈ A, nontaut c → c.1 = L0 ∨ c.2 = L0
  · exact Or.inr (Or.inl hstar)
  have hnounit : ∀ c ∈ A, nontaut c → c.1.1 ≠ c.2.1 := no_unit_of_above_half A hN
  by_cases hdisj : ∃ c1 ∈ A, ∃ c2 ∈ A, nontaut c1 ∧ nontaut c2 ∧
      c1.1 ≠ c2.1 ∧ c1.1 ≠ c2.2 ∧ c1.2 ≠ c2.1 ∧ c1.2 ≠ c2.2
  · rcases hdisj with ⟨c1, hc1, c2, hc2, hnt1, hnt2, hd11, hd12, hd21, hd22⟩
    have h12 : c1.1.1 ≠ c1.2.1 := hnounit c1 hc1 hnt1
    have h34 : c2.1.1 ≠ c2.2.1 := hnounit c2 hc2 hnt2
    have h13 : c1.1.1 ≠ c2.1.1 := by
      intro heq
      have hb : c2.1.2 = !c1.1.2 := by
        cases h1 : c1.1.2 <;> cases h2 : c2.1.2
        · exfalso; exact hd11 (Prod.ext heq (h1.trans h2.symm))
        · rfl
        · rfl
        · exfalso; exact hd11 (Prod.ext heq (h1.trans h2.symm))
      exact no_shared_var_opp A hN c1.1.1 c1.2.1 c2.2.1 c1.1.2 c1.2.2 c2.2.2
        h12.symm (heq ▸ h34.symm)
        (fun w hw => (sat_iff_nontaut A w).mp hw c1 hc1 hnt1)
        (fun w hw => by
          have := (sat_iff_nontaut A w).mp hw c2 hc2 hnt2
          rwa [← heq, hb] at this)
    have h14 : c1.1.1 ≠ c2.2.1 := by
      intro heq
      have hb : c2.2.2 = !c1.1.2 := by
        cases h1 : c1.1.2 <;> cases h2 : c2.2.2
        · exfalso; exact hd12 (Prod.ext heq (h1.trans h2.symm))
        · rfl
        · rfl
        · exfalso; exact hd12 (Prod.ext heq (h1.trans h2.symm))
      exact no_shared_var_opp A hN c1.1.1 c1.2.1 c2.1.1 c1.1.2 c1.2.2 c2.1.2
        h12.symm (heq ▸ h34)
        (fun w hw => (sat_iff_nontaut A w).mp hw c1 hc1 hnt1)
        (fun w hw => by
          have := (sat_iff_nontaut A w).mp hw c2 hc2 hnt2
          rw [← heq, hb] at this
          exact this.symm)
    have h23 : c1.2.1 ≠ c2.1.1 := by
      intro heq
      have hb : c2.1.2 = !c1.2.2 := by
        cases h1 : c1.2.2 <;> cases h2 : c2.1.2
        · exfalso; exact hd21 (Prod.ext heq (h1.trans h2.symm))
        · rfl
        · rfl
        · exfalso; exact hd21 (Prod.ext heq (h1.trans h2.symm))
      exact no_shared_var_opp A hN c1.2.1 c1.1.1 c2.2.1 c1.2.2 c1.1.2 c2.2.2
        h12 (heq ▸ h34.symm)
        (fun w hw => ((sat_iff_nontaut A w).mp hw c1 hc1 hnt1).symm)
        (fun w hw => by
          have := (sat_iff_nontaut A w).mp hw c2 hc2 hnt2
          rwa [← heq, hb] at this)
    have h24 : c1.2.1 ≠ c2.2.1 := by
      intro heq
      have hb : c2.2.2 = !c1.2.2 := by
        cases h1 : c1.2.2 <;> cases h2 : c2.2.2
        · exfalso; exact hd22 (Prod.ext heq (h1.trans h2.symm))
        · rfl
        · rfl
        · exfalso; exact hd22 (Prod.ext heq (h1.trans h2.symm))
      exact no_shared_var_opp A hN c1.2.1 c1.1.1 c2.1.1 c1.2.2 c1.1.2 c2.1.2
        h12 (heq ▸ h34)
        (fun w hw => ((sat_iff_nontaut A w).mp hw c1 hc1 hnt1).symm)
        (fun w hw => by
          have := (sat_iff_nontaut A w).mp hw c2 hc2 hnt2
          rw [← heq, hb] at this
          exact this.symm)
    have hall : ∀ c3 ∈ A, nontaut c3 → sameClause c3 c1 ∨ sameClause c3 c2 := by
      intro c3 hc3 hnt3
      by_contra hno
      push Not at hno
      rcases exists_fix_third_clause c1.1.1 c1.2.1 c2.1.1 c2.2.1 c3.1.1 c3.2.1
        c1.1.2 c1.2.2 c2.1.2 c2.2.2 c3.1.2 c3.2.2
        h12 h13 h14 h23 h24 h34 (hnounit c3 hc3 hnt3) hno.1 hno.2 with
        ⟨k1, k2, k3, k4, v1, v2, v3, v4, hk12, hk13, hk14, hk23, hk24, hk34, hfix⟩
      let S_sat := Finset.univ.filter (fun w : Word n => sat A w = true)
      let S_c12 := Finset.univ.filter (fun w : Word n =>
        predC1C2 c1.1.2 c1.2.2 c2.1.2 c2.2.2 (w c1.1.1, w c1.2.1, w c2.1.1, w c2.2.1) = true)
      let S_fix := Finset.univ.filter (fun w : Word n =>
        ((w k1 == v1) && (w k2 == v2) && (w k3 == v3) && (w k4 == v4)) = true)
      have hsub1 : S_sat ⊆ S_c12 := by
        intro w hw
        simp only [S_sat, S_c12, Finset.mem_filter, Finset.mem_univ, true_and, predC1C2,
          Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne] at hw ⊢
        exact ⟨(sat_iff_nontaut A w).mp hw c1 hc1 hnt1, (sat_iff_nontaut A w).mp hw c2 hc2 hnt2⟩
      have hsub2 : S_fix ⊆ S_c12 := by
        intro w hw
        simp only [S_fix, S_c12, Finset.mem_filter, Finset.mem_univ, true_and, predC1C2,
          Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at hw ⊢
        rcases hw with ⟨⟨⟨hw1, hw2⟩, hw3⟩, hw4⟩
        have hf := hfix w hw1 hw2 hw3 hw4
        exact ⟨hf.1, hf.2.1⟩
      have hdisjS : Disjoint S_sat S_fix := by
        rw [Finset.disjoint_left]
        intro w hw1 hw2
        simp only [S_sat, Finset.mem_filter, Finset.mem_univ, true_and] at hw1
        simp only [S_fix, Finset.mem_filter, Finset.mem_univ, true_and,
          Bool.and_eq_true, beq_iff_eq] at hw2
        rcases hw2 with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        have hf := hfix w h1 h2 h3 h4
        have hc3s := (sat_iff_nontaut A w).mp hw1 c3 hc3 hnt3
        rcases hc3s with ha | hb
        · exact ha hf.2.2.1
        · exact hb hf.2.2.2
      have hcard_le : S_sat.card + S_fix.card ≤ S_c12.card := by
        rw [← Finset.card_union_of_disjoint hdisjS]
        exact Finset.card_le_card (Finset.union_subset hsub1 hsub2)
      have hS_sat : S_sat.card = (Finset.univ.filter (fun w => sat A w = true)).card := rfl
      have hS_c12 : 16 * S_c12.card = 9 * 2 ^ n := by
        have := card_pred4 c1.1.1 c1.2.1 c2.1.1 c2.2.1 h12 h13 h14 h23 h24 h34
          (predC1C2 c1.1.2 c1.2.2 c2.1.2 c2.2.2)
        rw [card_predC1C2] at this
        exact this
      have hS_fix : 16 * S_fix.card = 1 * 2 ^ n := by
        have := card_pred4 k1 k2 k3 k4 hk12 hk13 hk14 hk23 hk24 hk34
          (fun t : B4 => (t.1 == v1) && (t.2.1 == v2) && (t.2.2.1 == v3) && (t.2.2.2 == v4))
        rw [card_predEq] at this
        exact this
      omega
    exact Or.inr (Or.inr ⟨c1, hc1, c2, hc2, hnt1, hnt2, ⟨h12, h13, h14, h23, h24, h34⟩, hall⟩)
  · exfalso
    push Not at hempty hstar hdisj
    rcases hempty with ⟨c1, hc1, hnt1⟩
    rcases hstar c1.1 with ⟨c2, hc2, hnt2, h21, h22⟩
    have h12_share : c1.2 = c2.1 ∨ c1.2 = c2.2 := by
      by_contra h
      push Not at h
      exact h.2 (hdisj c1 hc1 c2 hc2 hnt1 hnt2 h21.symm h22.symm h.1)
    let L1 := c1.1
    let L2 := c1.2
    let L3 := if c2.1 = L2 then c2.2 else c2.1
    have hc2_eq : (c2.1 = L2 ∧ c2.2 = L3) ∨ (c2.1 = L3 ∧ c2.2 = L2) := by
      rcases h12_share with h | h
      · left; exact ⟨h.symm, by simp [L3, L2, h.symm]⟩
      · by_cases h' : c2.1 = L2
        · left; exact ⟨h', by simp [L3, h']⟩
        · right; exact ⟨by simp [L3, h'], h.symm⟩
    have hL3neL1 : L3 ≠ L1 := by
      rcases hc2_eq with ⟨_, e2⟩ | ⟨e1, _⟩
      · rw [← e2]; exact h22
      · rw [← e1]; exact h21
    rcases hstar L2 with ⟨c3, hc3, hnt3, h31, h32⟩
    have hL1_in_c3 : L1 = c3.1 ∨ L1 = c3.2 := by
      by_contra h
      push Not at h
      exact h32.symm (hdisj c1 hc1 c3 hc3 hnt1 hnt3 h.1 h.2 h31.symm)
    have hL3_in_c3 : L3 = c3.1 ∨ L3 = c3.2 := by
      by_contra h
      push Not at h
      rcases hc2_eq with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact h.2 (e2 ▸ hdisj c2 hc2 c3 hc3 hnt2 hnt3
          (e1.symm ▸ h31.symm) (e1.symm ▸ h32.symm) (e2.symm ▸ h.1))
      · exact h32.symm (e2 ▸ hdisj c2 hc2 c3 hc3 hnt2 hnt3
          (e1.symm ▸ h.1) (e1.symm ▸ h.2) (e2.symm ▸ h31.symm))
    have hc3_eq : (c3.1 = L1 ∧ c3.2 = L3) ∨ (c3.1 = L3 ∧ c3.2 = L1) := by
      rcases hL1_in_c3 with h1 | h1 <;> rcases hL3_in_c3 with h3 | h3
      · exfalso; exact hL3neL1 (h3.trans h1.symm)
      · left; exact ⟨h1.symm, h3.symm⟩
      · right; exact ⟨h3.symm, h1.symm⟩
      · exfalso; exact hL3neL1 (h3.trans h1.symm)
    let f : Word n → Word n := fun w i =>
      if i = L1.1 ∨ i = L2.1 ∨ i = L3.1 then !(w i) else w i
    have hinv : ∀ w, f (f w) = w := by
      intro w; funext i; simp only [f]; split_ifs <;> simp
    have hnot_ne : ∀ (a b : Bool), ((!a) ≠ b) ↔ a = b := by decide
    have hdisj3 : ∀ w, sat A w = true → ¬ sat A (f w) = true := by
      intro w hw hfw
      have hs1 : w L1.1 ≠ L1.2 ∨ w L2.1 ≠ L2.2 := (sat_iff_nontaut A w).mp hw c1 hc1 hnt1
      have hs2 := (sat_iff_nontaut A w).mp hw c2 hc2 hnt2
      have hs3 := (sat_iff_nontaut A w).mp hw c3 hc3 hnt3
      have hf1 : f w L1.1 ≠ L1.2 ∨ f w L2.1 ≠ L2.2 := (sat_iff_nontaut A (f w)).mp hfw c1 hc1 hnt1
      have hf2 := (sat_iff_nontaut A (f w)).mp hfw c2 hc2 hnt2
      have hf3 := (sat_iff_nontaut A (f w)).mp hfw c3 hc3 hnt3
      have hfw1 : f w L1.1 = !(w L1.1) := by simp [f]
      have hfw2 : f w L2.1 = !(w L2.1) := by simp [f]
      have hfw3 : f w L3.1 = !(w L3.1) := by simp [f]
      have hs2' : w L2.1 ≠ L2.2 ∨ w L3.1 ≠ L3.2 := by
        rcases hc2_eq with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rwa [e1, e2] at hs2
        · rw [e1, e2] at hs2; exact hs2.symm
      have hs3' : w L1.1 ≠ L1.2 ∨ w L3.1 ≠ L3.2 := by
        rcases hc3_eq with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rwa [e1, e2] at hs3
        · rw [e1, e2] at hs3; exact hs3.symm
      have hf2' : f w L2.1 ≠ L2.2 ∨ f w L3.1 ≠ L3.2 := by
        rcases hc2_eq with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rwa [e1, e2] at hf2
        · rw [e1, e2] at hf2; exact hf2.symm
      have hf3' : f w L1.1 ≠ L1.2 ∨ f w L3.1 ≠ L3.2 := by
        rcases hc3_eq with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rwa [e1, e2] at hf3
        · rw [e1, e2] at hf3; exact hf3.symm
      rw [hfw1, hfw2, hnot_ne, hnot_ne] at hf1
      rw [hfw2, hfw3, hnot_ne, hnot_ne] at hf2'
      rw [hfw1, hfw3, hnot_ne, hnot_ne] at hf3'
      by_cases h1 : w L1.1 = L1.2
      · have h2 : w L2.1 ≠ L2.2 := hs1.resolve_left (not_not.mpr h1)
        have h3 : w L3.1 ≠ L3.2 := hs3'.resolve_left (not_not.mpr h1)
        exact hf2'.elim h2 h3
      · have h2 : w L2.1 = L2.2 := hf1.resolve_left h1
        have h3 : w L3.1 = L3.2 := hf3'.resolve_left h1
        exact hs2'.elim (fun hn => hn h2) (fun hn => hn h3)
    have hle := involution_two_mul_card_le (fun w => sat A w = true) f hinv hdisj3
    rw [card_word] at hle
    omega

private lemma card_star_sat {n : ℕ} (L0 : Lit n) (K : Finset (Fin n)) (hK0 : L0.1 ∉ K)
    (d : Fin n → Bool) :
    (Finset.univ.filter (fun w : Word n => w L0.1 ≠ L0.2 ∨ ∀ k ∈ K, w k ≠ d k)).card =
      2 ^ (n - 1) + 2 ^ (n - 1 - K.card) := by
  let S := Finset.univ.filter (fun w : Word n => w L0.1 ≠ L0.2 ∨ ∀ k ∈ K, w k ≠ d k)
  have hsplit := card_filter_add_not S (fun w => w L0.1 = L0.2)
  have hA : (S.filter (fun w => w L0.1 = L0.2)).card = 2 ^ (n - 1 - K.card) := by
    let v : Fin n → Bool := fun i => if i = L0.1 then L0.2 else !(d i)
    have heq : S.filter (fun w => w L0.1 = L0.2) =
        Finset.univ.filter (fun w : Word n => ∀ i ∈ insert L0.1 K, w i = v i) := by
      ext w
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, v]
      constructor
      · rintro ⟨hor, heq0⟩ i (rfl | hiK)
        · simp [heq0]
        · have hne : i ≠ L0.1 := fun h => hK0 (h ▸ hiK)
          have hwk := hor.resolve_left (not_not.mpr heq0) i hiK
          simp only [hne, ↓reduceIte]
          cases hw : w i <;> cases hd : d i <;> simp_all
      · intro h
        have h0 : w L0.1 = L0.2 := by simpa using h L0.1 (Or.inl rfl)
        refine ⟨Or.inr fun k hk => ?_, h0⟩
        have hne : k ≠ L0.1 := fun he => hK0 (he ▸ hk)
        have hwk := h k (Or.inr hk)
        simp only [hne, ↓reduceIte] at hwk
        rw [hwk]
        cases d k <;> decide
    rw [heq, card_word_eq_on, Finset.card_insert_of_notMem hK0]
    congr 1
    omega
  have hB : (S.filter (fun w => ¬ w L0.1 = L0.2)).card = 2 ^ (n - 1) := by
    have heq : S.filter (fun w => ¬ w L0.1 = L0.2) =
        Finset.univ.filter (fun w : Word n => ∀ i ∈ ({L0.1} : Finset (Fin n)), w i = !(L0.2)) := by
      ext w
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hne⟩ i rfl
        cases hw : w L0.1 <;> cases hb : L0.2 <;> simp_all
      · intro h
        have hne : w L0.1 ≠ L0.2 := by
          rw [h L0.1 rfl]
          cases L0.2 <;> decide
        exact ⟨Or.inl hne, hne⟩
    rw [heq, card_word_eq_on, Finset.card_singleton]
  change S.card = _
  omega

private lemma high_iff_star_card {n s : ℕ} (hs : 1 ≤ s) (hsn : s ≤ n) (k : ℕ) (hk : k + 1 ≤ n) :
    2 ^ n * (2 ^ (s - 1) + 1) ≤ 2 ^ s * (2 ^ (n - 1) + 2 ^ (n - 1 - k)) ↔ k ≤ s - 1 := by
  have hpow1 : 2 ^ s * 2 ^ (n - 1) = 2 ^ n * 2 ^ (s - 1) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hpow2 : 2 ^ s * 2 ^ (n - 1 - k) = 2 ^ (s + (n - 1 - k)) := (pow_add 2 s (n - 1 - k)).symm
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one, hpow1, hpow2]
  constructor
  · intro h
    have hle : 2 ^ n ≤ 2 ^ (s + (n - 1 - k)) := by omega
    have hexp := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle
    omega
  · intro h
    have hexp : n ≤ s + (n - 1 - k) := by omega
    have hle : 2 ^ n ≤ 2 ^ (s + (n - 1 - k)) := Nat.pow_le_pow_right (by decide : 0 < 2) hexp
    omega

private lemma high_of_above_half {n s : ℕ} (hs : 1 ≤ s) (A : CNF n) (hA : high s A) :
    2 ^ n < 2 * (Finset.univ.filter (fun w : Word n => sat A w = true)).card := by
  let N := (Finset.univ.filter (fun w : Word n => sat A w = true)).card
  let t := 2 ^ (s - 1)
  have ht_pos : 0 < t := Nat.pow_pos (by decide)
  have h2s : 2 ^ s = 2 * t := by
    have hs1 : s = (s - 1) + 1 := by omega
    conv_lhs => rw [hs1, pow_succ']
  have hQpos : 0 < 2 ^ n := Nat.pow_pos (by decide)
  have h1 : t * 2 ^ n + 2 ^ n ≤ t * (2 * N) := by
    have h2 : 2 ^ n * (t + 1) ≤ (2 * t) * N := by dsimp only [high] at hA; rwa [h2s] at hA
    have hl : 2 ^ n * (t + 1) = t * 2 ^ n + 2 ^ n := by rw [Nat.mul_add, Nat.mul_one, mul_comm]
    have hr : (2 * t) * N = t * (2 * N) := by ac_rfl
    omega
  exact Nat.lt_of_mul_lt_mul_left (show t * 2 ^ n < t * (2 * N) by omega)

private lemma high_disj2_iff {n s : ℕ} (hs : 3 ≤ s) (c1 c2 : Lit n × Lit n)
    (hd : disjoint4 c1 c2) (A : CNF n)
    (hsat : ∀ w : Word n,
      sat A w = predC1C2 c1.1.2 c1.2.2 c2.1.2 c2.2.2 (w c1.1.1, w c1.2.1, w c2.1.1, w c2.2.1)) :
    high s A ↔ 4 ≤ s := by
  have hN16 : 16 * (Finset.univ.filter (fun w : Word n => sat A w = true)).card = 9 * 2 ^ n := by
    have h1 := card_pred4 c1.1.1 c1.2.1 c2.1.1 c2.2.1
      hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2
      (predC1C2 c1.1.2 c1.2.2 c2.1.2 c2.2.2)
    rw [card_predC1C2] at h1
    convert h1 using 2
    congr 1
    ext w
    simp [hsat]
  have h2s : 2 * 2 ^ (s - 1) = 2 ^ s := by
    have hs1 : s = (s - 1) + 1 := by omega
    conv_rhs => rw [hs1, pow_succ']
  have hQpos : 0 < 2 ^ n := Nat.pow_pos (by decide)
  constructor
  · intro hA
    have h16 := Nat.mul_le_mul_left 16 hA
    have hR : 16 * (2 ^ s * (Finset.univ.filter (fun w : Word n => sat A w = true)).card) =
        9 * 2 ^ s * 2 ^ n := by
      calc
        16 * (2 ^ s * (Finset.univ.filter (fun w : Word n => sat A w = true)).card)
          = 2 ^ s * (16 * (Finset.univ.filter (fun w : Word n => sat A w = true)).card) := by ac_rfl
        _ = 2 ^ s * (9 * 2 ^ n) := by rw [hN16]
        _ = 9 * 2 ^ s * 2 ^ n := by ac_rfl
    have hL : 16 * (2 ^ n * (2 ^ (s - 1) + 1)) = (8 * 2 ^ s + 16) * 2 ^ n := by
      calc
        16 * (2 ^ n * (2 ^ (s - 1) + 1))
          = (8 * (2 * 2 ^ (s - 1)) + 16) * 2 ^ n := by
              rw [Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.add_mul]
              have h16_8 : 16 * (2 ^ n * 2 ^ (s - 1)) = 8 * (2 * 2 ^ (s - 1)) * 2 ^ n := by
                have h28 : 16 = 8 * 2 := rfl
                rw [h28]; ac_rfl
              rw [h16_8, mul_comm 16 (2 ^ n)]
        _ = (8 * 2 ^ s + 16) * 2 ^ n := by rw [h2s]
    rw [hL, hR] at h16
    have hle : 8 * 2 ^ s + 16 ≤ 9 * 2 ^ s := Nat.le_of_mul_le_mul_right h16 hQpos
    have h16le : 2 ^ 4 ≤ 2 ^ s := by
      have : (2 : ℕ) ^ 4 = 16 := by decide
      omega
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h16le
  · intro hs4
    have h16le : 16 ≤ 2 ^ s := by
      have : (2 : ℕ) ^ 4 = 16 := by decide
      rw [← this]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) hs4
    have h16 : 16 * (2 ^ n * (2 ^ (s - 1) + 1)) ≤
        16 * (2 ^ s * (Finset.univ.filter (fun w : Word n => sat A w = true)).card) := by
      have hR : 16 * (2 ^ s * (Finset.univ.filter (fun w : Word n => sat A w = true)).card) =
          9 * 2 ^ s * 2 ^ n := by
        calc
          16 * (2 ^ s * (Finset.univ.filter (fun w : Word n => sat A w = true)).card)
            = 2 ^ s * (16 * (Finset.univ.filter (fun w : Word n => sat A w = true)).card) := by ac_rfl
          _ = 2 ^ s * (9 * 2 ^ n) := by rw [hN16]
          _ = 9 * 2 ^ s * 2 ^ n := by ac_rfl
      have hL : 16 * (2 ^ n * (2 ^ (s - 1) + 1)) = (8 * 2 ^ s + 16) * 2 ^ n := by
        calc
          16 * (2 ^ n * (2 ^ (s - 1) + 1))
            = (8 * (2 * 2 ^ (s - 1)) + 16) * 2 ^ n := by
                rw [Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.add_mul]
                have h16_8 : 16 * (2 ^ n * 2 ^ (s - 1)) = 8 * (2 * 2 ^ (s - 1)) * 2 ^ n := by
                  have h28 : 16 = 8 * 2 := rfl
                  rw [h28]; ac_rfl
                rw [h16_8, mul_comm 16 (2 ^ n)]
          _ = (8 * 2 ^ s + 16) * 2 ^ n := by rw [h2s]
      rw [hL, hR]
      exact Nat.mul_le_mul_right (2 ^ n) (by omega)
    exact Nat.le_of_mul_le_mul_left h16 (by decide : 0 < 16)

private def calIdx {qcal qunif : ℕ} (r : Fin qcal) : Fin (qcal + qunif) :=
  ⟨r.val, Nat.lt_of_lt_of_le r.isLt (Nat.le_add_right qcal qunif)⟩

private def unifIdx {qcal qunif : ℕ} (t : Fin qunif) : Fin (qcal + qunif) :=
  ⟨qcal + t.val, Nat.add_lt_add_left t.isLt qcal⟩

open Classical in
private noncomputable def hull {n qcal qunif : ℕ} (T : Fin qcal → Word n)
    (a : Fin (qcal + qunif) → Bool) : CNF n :=
  Finset.univ.filter fun c : Lit n × Lit n =>
    nontaut c ∧ ∀ r : Fin qcal, a (calIdx r) = true → T r c.1.1 ≠ c.1.2 ∨ T r c.2.1 ≠ c.2.2

private lemma mem_hull {n qcal qunif : ℕ} (T : Fin qcal → Word n)
    (a : Fin (qcal + qunif) → Bool) (c : Lit n × Lit n) :
    c ∈ hull T a ↔ nontaut c ∧ ∀ r : Fin qcal, a (calIdx r) = true →
      T r c.1.1 ≠ c.1.2 ∨ T r c.2.1 ≠ c.2.2 := by
  simp [hull]

private def isStarHull {n : ℕ} (H : CNF n) : Prop :=
  ∃ L0 : Lit n, ∀ c ∈ H, c.1 = L0 ∨ c.2 = L0

private def isDisj2Hull {n : ℕ} (H : CNF n) : Prop :=
  ∃ c1 ∈ H, ∃ c2 ∈ H, disjoint4 c1 c2 ∧ ∀ c ∈ H, sameClause c c1 ∨ sameClause c c2

private def flipAt {n s : ℕ} (w : Word n) (i0 : Fin n) (m : Fin n → Fin s) : Word n :=
  fun k => if k ≠ i0 ∧ (m k).val = 0 then !(w k) else w k

private def firstSeed {n s qcal qunif q2 : ℕ} (T : Fin qcal → Word n)
    (seed : (Fin qunif → Word n) × (Fin q2 → Fin n → Fin s)) (i : Fin (qcal + qunif)) : Word n :=
  if h : i.val < qcal then T ⟨i.val, h⟩
  else seed.1 ⟨i.val - qcal, by omega⟩

private lemma firstSeed_cal {n s qcal qunif q2 : ℕ} (T : Fin qcal → Word n)
    (seed : (Fin qunif → Word n) × (Fin q2 → Fin n → Fin s)) (r : Fin qcal) :
    firstSeed T seed (calIdx r) = T r := by
  simp [firstSeed, calIdx, r.isLt]

private lemma firstSeed_unif {n s qcal qunif q2 : ℕ} (T : Fin qcal → Word n)
    (seed : (Fin qunif → Word n) × (Fin q2 → Fin n → Fin s)) (t : Fin qunif) :
    firstSeed T seed (unifIdx t) = seed.1 t := by
  have hnot : ¬ qcal + t.val < qcal := by omega
  simp [firstSeed, unifIdx, hnot]

private def hasPassOn {n s qcal qunif q2 : ℕ}
    (seed : (Fin qunif → Word n) × (Fin q2 → Fin n → Fin s))
    (a : Fin (qcal + qunif) → Bool) (L0 : Lit n) : Prop :=
  ∃ t : Fin qunif, seed.1 t L0.1 = L0.2 ∧ a (unifIdx t) = true

open Classical in
private noncomputable def secondSeedCore {n s qcal qunif q2 : ℕ} (H : CNF n)
    (seed : (Fin qunif → Word n) × (Fin q2 → Fin n → Fin s))
    (a : Fin (qcal + qunif) → Bool) (j : Fin q2) : Word n :=
  if hS : H ≠ ∅ ∧ isStarHull H then
    let L0 := Classical.choose hS.2
    if hP : hasPassOn seed a L0 then
      let t := Classical.choose hP
      flipAt (seed.1 t) L0.1 (seed.2 j)
    else fun _ => false
  else fun _ => false

private noncomputable def secondSeed {n s qcal qunif q2 : ℕ} (T : Fin qcal → Word n)
    (seed : (Fin qunif → Word n) × (Fin q2 → Fin n → Fin s))
    (a : Fin (qcal + qunif) → Bool) (j : Fin q2) : Word n :=
  secondSeedCore (hull T a) seed a j

open Classical in
private noncomputable def reportSeedCore {n s qcal qunif q2 : ℕ} (H : CNF n)
    (seed : (Fin qunif → Word n) × (Fin q2 → Fin n → Fin s))
    (a : Fin (qcal + qunif) → Bool) (b : Fin q2 → Bool) : Option (CNF n) :=
  if H = ∅ then
    some ∅
  else if hS : isStarHull H then
    let L0 := Classical.choose hS
    if hP : hasPassOn seed a L0 then
      let t := Classical.choose hP
      let wstar := seed.1 t
      let U : Finset (Fin n) := Finset.univ.filter fun k =>
        k ≠ L0.1 ∧ ∀ j : Fin q2, b j = true → (seed.2 j k).val ≠ 0
      if U.card ≤ s - 1 ∧
          ∀ k ∈ U, ∃ j : Fin q2, b j = false ∧
            ∀ u ∈ U, ((seed.2 j u).val = 0 ↔ u = k) then
        some (U.image fun k => (L0, (k, !(wstar k))))
      else none
    else none
  else if hD : 4 ≤ s ∧ isDisj2Hull H then
    let c1 := Classical.choose hD.2
    let c2 := Classical.choose (Classical.choose_spec hD.2).2
    some ({c1, c2} : CNF n)
  else none

private noncomputable def reportSeed {n s qcal qunif q2 : ℕ} (T : Fin qcal → Word n)
    (seed : (Fin qunif → Word n) × (Fin q2 → Fin n → Fin s))
    (a : Fin (qcal + qunif) → Bool) (b : Fin q2 → Bool) : Option (CNF n) :=
  reportSeedCore (hull T a) seed a b

private lemma secondSeed_star_eq {n s qcal qunif q2 : ℕ} (T : Fin qcal → Word n)
    (seed : (Fin qunif → Word n) × (Fin q2 → Fin n → Fin s))
    (a : Fin (qcal + qunif) → Bool) (H0 : CNF n)
    (hHa : hull T a = H0) (hH0_ne : H0 ≠ ∅) (hH0_star : isStarHull H0)
    (hP : hasPassOn seed a (Classical.choose hH0_star)) (j : Fin q2) :
    secondSeed T seed a j =
      flipAt (seed.1 (Classical.choose hP)) (Classical.choose hH0_star).1 (seed.2 j) := by
  dsimp only [secondSeed]
  rw [hHa]
  dsimp only [secondSeedCore]
  split_ifs with hS
  · rfl
  · exact absurd ⟨hH0_ne, hH0_star⟩ hS

private lemma reportSeed_empty_isSome {n s qcal qunif q2 : ℕ} (T : Fin qcal → Word n)
    (seed : (Fin qunif → Word n) × (Fin q2 → Fin n → Fin s))
    (a : Fin (qcal + qunif) → Bool) (b : Fin q2 → Bool)
    (hHa : hull T a = ∅) :
    (reportSeed T seed a b).isSome = true := by
  dsimp only [reportSeed]
  rw [hHa]
  dsimp only [reportSeedCore]
  simp

private lemma reportSeed_star_isSome {n s qcal qunif q2 : ℕ} (T : Fin qcal → Word n)
    (seed : (Fin qunif → Word n) × (Fin q2 → Fin n → Fin s))
    (a : Fin (qcal + qunif) → Bool) (b : Fin q2 → Bool) (H0 : CNF n)
    (hHa : hull T a = H0) (hH0_ne : H0 ≠ ∅) (hH0_star : isStarHull H0)
    (hP : hasPassOn seed a (Classical.choose hH0_star))
    (hCert :
      let L0 := Classical.choose hH0_star
      let U : Finset (Fin n) := Finset.univ.filter fun k =>
        k ≠ L0.1 ∧ ∀ j : Fin q2, b j = true → (seed.2 j k).val ≠ 0
      U.card ≤ s - 1 ∧
        ∀ k ∈ U, ∃ j : Fin q2, b j = false ∧ ∀ u ∈ U, ((seed.2 j u).val = 0 ↔ u = k)) :
    (reportSeed T seed a b).isSome = true := by
  dsimp only [reportSeed]
  rw [hHa]
  dsimp only [reportSeedCore]
  simp only [hH0_ne, ↓reduceIte, hH0_star, ↓reduceDIte, hP]
  split_ifs with hC
  · rfl
  · exact absurd hCert hC

private lemma reportSeed_disj2_isSome {n s qcal qunif q2 : ℕ} (T : Fin qcal → Word n)
    (seed : (Fin qunif → Word n) × (Fin q2 → Fin n → Fin s))
    (a : Fin (qcal + qunif) → Bool) (b : Fin q2 → Bool) (H0 : CNF n)
    (hHa : hull T a = H0) (hH0_ne : H0 ≠ ∅) (hH0_not_star : ¬ isStarHull H0)
    (hs4 : 4 ≤ s) (hH0_disj : isDisj2Hull H0) :
    (reportSeed T seed a b).isSome = true := by
  dsimp only [reportSeed]
  rw [hHa]
  dsimp only [reportSeedCore]
  simp only [hH0_ne, ↓reduceIte, hH0_not_star, ↓reduceDIte]
  split_ifs with hD
  · rfl
  · exact absurd ⟨hs4, hH0_disj⟩ hD

private lemma sub_hull {n s qcal qunif q2 : ℕ} (T : Fin qcal → Word n)
    (seed : (Fin qunif → Word n) × (Fin q2 → Fin n → Fin s)) (A : CNF n)
    (c : Lit n × Lit n) (hc : c ∈ A) (hnt : nontaut c) :
    c ∈ hull T (fun i => sat A (firstSeed T seed i)) := by
  rw [mem_hull]
  refine ⟨hnt, fun r hr => ?_⟩
  rw [firstSeed_cal] at hr
  exact (sat_iff_nontaut A (T r)).mp hr c hc hnt

open Classical in
private lemma star_sat_of_pass {n : ℕ} (A : CNF n) (L0 : Lit n) (wstar : Word n)
    (hstar : ∀ c ∈ A, nontaut c → c.1 = L0 ∨ c.2 = L0)
    (hw0 : wstar L0.1 = L0.2) (hwsat : sat A wstar = true) :
    let K := Finset.univ.filter fun k : Fin n => k ≠ L0.1 ∧ hasClause A L0 (k, !(wstar k))
    ∀ z : Word n, sat A z = true ↔ z L0.1 ≠ L0.2 ∨ ∀ k ∈ K, z k = wstar k := by
  intro K z
  have hK : ∀ k : Fin n, k ∈ K ↔ k ≠ L0.1 ∧ hasClause A L0 (k, !(wstar k)) := fun k => by
    simp [K]
  rw [sat_iff_nontaut]
  constructor
  · intro hz
    by_cases hz0 : z L0.1 = L0.2
    · right
      intro k hk
      rw [hK] at hk
      rcases hk with ⟨_, c, hc, hnt, hsc⟩
      have hzc := hz c hc hnt
      rcases hsc with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2] at hzc
        exact bool_eq_of_ne_not (hzc.resolve_left (not_not.mpr hz0))
      · rw [e1, e2] at hzc
        exact bool_eq_of_ne_not (hzc.resolve_right (not_not.mpr hz0))
    · exact Or.inl hz0
  · intro hz c hc hnt
    have hwc := (sat_iff_nontaut A wstar).mp hwsat c hc hnt
    rcases hstar c hc hnt with h1 | h2
    · have hne2 : wstar c.2.1 ≠ c.2.2 := by
        rw [h1] at hwc
        exact hwc.resolve_left (not_not.mpr hw0)
      have hk_ne : c.2.1 ≠ L0.1 := by
        intro heq
        rw [heq, hw0] at hne2
        exact hnt ⟨by rw [h1, heq], by rw [h1]; exact hne2⟩
      have hcd : c.2.2 = !(wstar c.2.1) := (bool_eq_not_of_ne hne2.symm)
      rcases hz with hz0 | hzK
      · left; rwa [h1]
      · right
        have hmem : c.2.1 ∈ K :=
          (hK c.2.1).mpr ⟨hk_ne, c, hc, hnt, Or.inl ⟨h1, Prod.ext rfl hcd⟩⟩
        rw [hzK c.2.1 hmem, hcd]
        exact (bool_not_ne_self _).symm
    · have hne1 : wstar c.1.1 ≠ c.1.2 := by
        rw [h2] at hwc
        exact hwc.resolve_right (not_not.mpr hw0)
      have hk_ne : c.1.1 ≠ L0.1 := by
        intro heq
        rw [heq, hw0] at hne1
        exact hnt ⟨by rw [h2, heq], by rw [h2]; exact Ne.symm hne1⟩
      have hcd : c.1.2 = !(wstar c.1.1) := (bool_eq_not_of_ne hne1.symm)
      rcases hz with hz0 | hzK
      · right; rwa [h2]
      · left
        have hmem : c.1.1 ∈ K :=
          (hK c.1.1).mpr ⟨hk_ne, c, hc, hnt, Or.inr ⟨Prod.ext rfl hcd, h2⟩⟩
        rw [hzK c.1.1 hmem, hcd]
        exact (bool_not_ne_self _).symm

private lemma sat_image_star {n : ℕ} (L0 : Lit n) (wstar : Word n) (U : Finset (Fin n))
    (z : Word n) :
    sat (U.image fun k => (L0, (k, !(wstar k)))) z = true ↔
      z L0.1 ≠ L0.2 ∨ ∀ k ∈ U, z k = wstar k := by
  simp only [sat, decide_eq_true_eq, Finset.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · intro h
    by_cases hz0 : z L0.1 = L0.2
    · right
      intro k hk
      have hne := (h k hk).resolve_left (not_not.mpr hz0)
      cases hzk : z k <;> cases hwk : wstar k <;> simp_all
    · exact Or.inl hz0
  · intro h k hk
    rcases h with hz0 | hU
    · exact Or.inl hz0
    · right
      rw [hU k hk]
      cases wstar k <;> decide

open Classical in
private lemma sound_protocol {n s qcal qunif q2 : ℕ} (hs : 3 ≤ s) (hsn : s ≤ n)
    (T : Fin qcal → Word n)
    (hT : ∀ (S : Finset (Fin n)), S.card ≤ 4 → ∀ f : Word n,
      ∃ r : Fin qcal, ∀ i ∈ S, T r i = f i)
    (seed : (Fin qunif → Word n) × (Fin q2 → Fin n → Fin s))
    (A B : CNF n)
    (hres : reportSeed T seed (fun i => sat A (firstSeed T seed i))
      (fun j => sat A (secondSeed T seed (fun i => sat A (firstSeed T seed i)) j)) = some B) :
    high s A ∧ ∀ z : Word n, sat B z = sat A z := by
  let a : Fin (qcal + qunif) → Bool := fun i => sat A (firstSeed T seed i)
  let b : Fin q2 → Bool := fun j => sat A (secondSeed T seed a j)
  let H := hull T a
  have hsubH : ∀ c ∈ A, nontaut c → c ∈ H := sub_hull T seed A
  change reportSeedCore H seed a b = some B at hres
  dsimp only [reportSeedCore] at hres
  by_cases hH0 : H = ∅
  · simp only [hH0, ↓reduceIte] at hres
    injection hres with hB
    subst hB
    have hsat_true : ∀ z : Word n, sat A z = true := by
      intro z
      refine (sat_iff_nontaut A z).mpr fun c hc hnt => ?_
      have hmem := hsubH c hc hnt
      rw [hH0] at hmem
      exact absurd hmem (Finset.notMem_empty c)
    have hcard : (Finset.univ.filter (fun z : Word n => sat A z = true)).card = 2 ^ n := by
      have : Finset.univ.filter (fun z : Word n => sat A z = true) = Finset.univ := by
        ext z; simp [hsat_true z]
      rw [this, Finset.card_univ, card_word]
    have hhigh : high s A := by
      dsimp only [high]
      rw [hcard]
      have h2s : 2 ^ (s - 1) + 1 ≤ 2 ^ s := by
        have h1 : 1 ≤ 2 ^ (s - 1) := Nat.one_le_pow _ _ (by decide)
        have h2 : 2 ^ s = 2 ^ (s - 1) + 2 ^ (s - 1) := by
          have hs1 : s = (s - 1) + 1 := by omega
          conv_lhs => rw [hs1, pow_succ', two_mul]
        omega
      calc
        2 ^ n * (2 ^ (s - 1) + 1) ≤ 2 ^ n * 2 ^ s := Nat.mul_le_mul_left _ h2s
        _ = 2 ^ s * 2 ^ n := mul_comm _ _
    refine ⟨hhigh, fun z => ?_⟩
    rw [hsat_true z]
    simp [sat]
  simp only [hH0, ↓reduceIte] at hres
  change (if hS : isStarHull H then _ else _) = some B at hres
  by_cases hS : isStarHull H
  · simp only [hS, ↓reduceDIte] at hres
    let L0 := Classical.choose hS
    have hL0 : ∀ c ∈ H, c.1 = L0 ∨ c.2 = L0 := Classical.choose_spec hS
    have hstarA : ∀ c ∈ A, nontaut c → c.1 = L0 ∨ c.2 = L0 :=
      fun c hc hnt => hL0 c (hsubH c hc hnt)
    change (if hP : hasPassOn seed a L0 then _ else none) = some B at hres
    have hP : hasPassOn seed a L0 := by
      by_contra hno
      simp only [hno, ↓reduceDIte] at hres
      cases hres
    simp only [hP, ↓reduceDIte] at hres
    let t := Classical.choose hP
    have ht : seed.1 t L0.1 = L0.2 ∧ a (unifIdx t) = true := Classical.choose_spec hP
    let wstar := seed.1 t
    let U : Finset (Fin n) := Finset.univ.filter fun k =>
      k ≠ L0.1 ∧ ∀ j : Fin q2, b j = true → (seed.2 j k).val ≠ 0
    change (if U.card ≤ s - 1 ∧
        ∀ k ∈ U, ∃ j : Fin q2, b j = false ∧ ∀ u ∈ U, ((seed.2 j u).val = 0 ↔ u = k)
      then some (U.image fun k => (L0, (k, !(wstar k)))) else none) = some B at hres
    split_ifs at hres with hCert
    injection hres with hB
    have hw0 : wstar L0.1 = L0.2 := ht.1
    have hwsat : sat A wstar = true := by
      have h1 := ht.2
      dsimp only [a] at h1
      rwa [firstSeed_unif] at h1
    let K := Finset.univ.filter fun k : Fin n => k ≠ L0.1 ∧ hasClause A L0 (k, !(wstar k))
    have hsatA := star_sat_of_pass A L0 wstar hstarA hw0 hwsat
    have hflip : ∀ j : Fin q2, b j = true ↔ ∀ k ∈ K, (seed.2 j k).val ≠ 0 := by
      intro j
      have hsec : secondSeed T seed a j = flipAt wstar L0.1 (seed.2 j) :=
        secondSeed_star_eq T seed a H rfl hH0 hS hP j
      dsimp only [b]
      rw [hsec, hsatA]
      have hfi : flipAt wstar L0.1 (seed.2 j) L0.1 = L0.2 := by
        simp [flipAt, hw0]
      rw [hfi]
      simp only [ne_eq, not_true_eq_false, false_or]
      constructor
      · intro h k hk
        have hne : k ≠ L0.1 := (Finset.mem_filter.mp hk).2.1
        have hwk := h k hk
        intro h0
        have hfl : flipAt wstar L0.1 (seed.2 j) k = !(wstar k) := by
          dsimp only [flipAt]
          split_ifs with hc
          · rfl
          · exact absurd ⟨hne, h0⟩ hc
        rw [hfl] at hwk
        exact bool_not_ne_self (wstar k) hwk
      · intro h k hk
        have hne : k ≠ L0.1 := (Finset.mem_filter.mp hk).2.1
        have h0 := h k hk
        simp [flipAt, hne, h0]
    have hKU : K ⊆ U := by
      intro k hk
      simp only [K, U, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      refine ⟨hk.1, fun j hj => (hflip j).mp hj k ?_⟩
      simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hk
    have hUK : U ⊆ K := by
      intro k hk
      obtain ⟨j, hjf, hiso⟩ := hCert.2 k hk
      have hnotall : ¬ ∀ u ∈ K, (seed.2 j u).val ≠ 0 := by
        intro hall
        have hbt := (hflip j).mpr hall
        rw [hbt] at hjf
        exact Bool.noConfusion hjf
      push Not at hnotall
      obtain ⟨u, huK, hu0⟩ := hnotall
      have huU : u ∈ U := hKU huK
      have huk : u = k := (hiso u huU).mp hu0
      rwa [← huk]
    have hUeqK : U = K := Finset.Subset.antisymm hUK hKU
    have hsat_eq : ∀ z : Word n, sat B z = sat A z := by
      intro z
      rw [← hB]
      apply Bool.eq_iff_iff.mpr
      rw [sat_image_star, hsatA, hUeqK]
    have hK0 : L0.1 ∉ K := by simp [K]
    have hKcard : K.card ≤ s - 1 := by rw [← hUeqK]; exact hCert.1
    have hKlt : K.card + 1 ≤ n := by
      have : (insert L0.1 K).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      rw [Finset.card_insert_of_notMem hK0, Finset.card_univ, Fintype.card_fin] at this
      exact this
    have hcardA : (Finset.univ.filter (fun z : Word n => sat A z = true)).card =
        2 ^ (n - 1) + 2 ^ (n - 1 - K.card) := by
      have heq : Finset.univ.filter (fun z : Word n => sat A z = true) =
          Finset.univ.filter (fun z : Word n => z L0.1 ≠ L0.2 ∨ ∀ k ∈ K, z k ≠ !(wstar k)) := by
        ext z
        rw [Finset.mem_filter, Finset.mem_filter, hsatA]
        simp only [Finset.mem_univ, true_and]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · right; intro k hk; rw [h k hk]; exact (bool_not_ne_self _).symm
        · rintro (h | h)
          · exact Or.inl h
          · right; intro k hk; exact bool_eq_of_ne_not (h k hk)
      rw [heq, card_star_sat L0 K hK0 (fun k => !(wstar k))]
    have hhigh : high s A := by
      dsimp only [high]
      rw [hcardA]
      exact (high_iff_star_card (by omega) hsn K.card hKlt).mpr hKcard
    exact ⟨hhigh, hsat_eq⟩
  simp only [hS, ↓reduceDIte] at hres
  change (if hD : 4 ≤ s ∧ isDisj2Hull H then _ else none) = some B at hres
  split_ifs at hres with hD
  injection hres with hB
  let c1 := Classical.choose hD.2
  have hc1_spec := Classical.choose_spec hD.2
  let c2 := Classical.choose hc1_spec.2
  have hc2_spec := Classical.choose_spec hc1_spec.2
  change ({c1, c2} : CNF n) = B at hB
  have hc1H : c1 ∈ H := hc1_spec.1
  have hc2H : c2 ∈ H := hc2_spec.1
  have hd : disjoint4 c1 c2 := hc2_spec.2.1
  have hallH : ∀ c ∈ H, sameClause c c1 ∨ sameClause c c2 := hc2_spec.2.2
  have hhas1 : ∃ c ∈ A, nontaut c ∧ sameClause c c1 := by
    by_contra hno
    push Not at hno
    let f : Word n := fun k =>
      if k = c1.1.1 then c1.1.2
      else if k = c1.2.1 then c1.2.2
      else !(c2.1.2)
    let S : Finset (Fin n) := {c1.1.1, c1.2.1, c2.1.1}
    have hScard : S.card ≤ 4 :=
      le_trans (Finset.card_insert_le _ _)
        (Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) (by simp)))
    obtain ⟨r, hr⟩ := hT S hScard f
    have hr1 : T r c1.1.1 = c1.1.2 := by simpa [f, S] using hr c1.1.1 (by simp [S])
    have hr2 : T r c1.2.1 = c1.2.2 := by
      simpa [f, S, hd.1.symm] using hr c1.2.1 (by simp [S])
    have hr3 : T r c2.1.1 = !(c2.1.2) := by
      simpa [f, S, hd.2.1.symm, hd.2.2.2.1.symm] using hr c2.1.1 (by simp [S])
    have hsat_r : sat A (T r) = true := by
      refine (sat_iff_nontaut A (T r)).mpr fun c hc hnt => ?_
      have hsc := hallH c (hsubH c hc hnt)
      have hsc2 : sameClause c c2 := hsc.resolve_left (hno c hc hnt)
      rcases hsc2 with ⟨e1, _⟩ | ⟨_, e2⟩
      · left; rw [e1, hr3]; cases c2.1.2 <;> decide
      · right; rw [e2, hr3]; cases c2.1.2 <;> decide
    have hc1_sat := ((mem_hull T a c1).mp hc1H).2 r (by
      dsimp only [a]; rw [firstSeed_cal]; exact hsat_r)
    exact hc1_sat.elim (fun h => h hr1) (fun h => h hr2)
  have hhas2 : ∃ c ∈ A, nontaut c ∧ sameClause c c2 := by
    by_contra hno
    push Not at hno
    let f : Word n := fun k =>
      if k = c2.1.1 then c2.1.2
      else if k = c2.2.1 then c2.2.2
      else !(c1.1.2)
    let S : Finset (Fin n) := {c2.1.1, c2.2.1, c1.1.1}
    have hScard : S.card ≤ 4 :=
      le_trans (Finset.card_insert_le _ _)
        (Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) (by simp)))
    obtain ⟨r, hr⟩ := hT S hScard f
    have hr1 : T r c2.1.1 = c2.1.2 := by simpa [f, S] using hr c2.1.1 (by simp [S])
    have hr2 : T r c2.2.1 = c2.2.2 := by
      simpa [f, S, hd.2.2.2.2.2.symm] using hr c2.2.1 (by simp [S])
    have hr3 : T r c1.1.1 = !(c1.1.2) := by
      simpa [f, S, hd.2.1, hd.2.2.1] using hr c1.1.1 (by simp [S])
    have hsat_r : sat A (T r) = true := by
      refine (sat_iff_nontaut A (T r)).mpr fun c hc hnt => ?_
      have hsc := hallH c (hsubH c hc hnt)
      have hsc1 : sameClause c c1 := hsc.resolve_right (hno c hc hnt)
      rcases hsc1 with ⟨e1, _⟩ | ⟨_, e2⟩
      · left; rw [e1, hr3]; cases c1.1.2 <;> decide
      · right; rw [e2, hr3]; cases c1.1.2 <;> decide
    have hc2_sat := ((mem_hull T a c2).mp hc2H).2 r (by
      dsimp only [a]; rw [firstSeed_cal]; exact hsat_r)
    exact hc2_sat.elim (fun h => h hr1) (fun h => h hr2)
  have hsatA_pred : ∀ w : Word n,
      sat A w = predC1C2 c1.1.2 c1.2.2 c2.1.2 c2.2.2 (w c1.1.1, w c1.2.1, w c2.1.1, w c2.2.1) := by
    intro w
    apply Bool.eq_iff_iff.mpr
    rw [sat_iff_nontaut]
    simp only [predC1C2, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne]
    constructor
    · intro hw
      rcases hhas1 with ⟨d1, hd1, hnt1, hsc1⟩
      rcases hhas2 with ⟨d2, hd2, hnt2, hsc2⟩
      have hs1 := hw d1 hd1 hnt1
      have hs2 := hw d2 hd2 hnt2
      constructor
      · rcases hsc1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rwa [e1, e2] at hs1
        · rw [e1, e2] at hs1; exact hs1.symm
      · rcases hsc2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rwa [e1, e2] at hs2
        · rw [e1, e2] at hs2; exact hs2.symm
    · rintro ⟨hs1, hs2⟩ c hc hnt
      rcases hallH c (hsubH c hc hnt) with (⟨e1, e2⟩ | ⟨e1, e2⟩) | (⟨e1, e2⟩ | ⟨e1, e2⟩)
      · rw [e1, e2]; exact hs1
      · rw [e1, e2]; exact hs1.symm
      · rw [e1, e2]; exact hs2
      · rw [e1, e2]; exact hs2.symm
  have hsat_eq : ∀ z : Word n, sat B z = sat A z := by
    intro z
    rw [← hB, hsatA_pred z]
    apply Bool.eq_iff_iff.mpr
    simp only [sat, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
      forall_eq, predC1C2, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne]
  have hhigh : high s A := (high_disj2_iff hs c1 c2 hd A hsatA_pred).mpr hD.1
  exact ⟨hhigh, hsat_eq⟩

open Classical in
private lemma complete_protocol {n s : ℕ} (hs : 3 ≤ s) (hsn : s ≤ n)
    (T : Fin (16 * (1 + 4 * (1 + Nat.clog 2 (n + 1)))) → Word n)
    (hT : ∀ (S : Finset (Fin n)), S.card ≤ 4 → ∀ f : Word n,
      ∃ r : Fin (16 * (1 + 4 * (1 + Nat.clog 2 (n + 1)))), ∀ i ∈ S, T r i = f i)
    (A : CNF n) (hA : high s A) :
    let L := Nat.clog 2 (n + 1)
    let qcal := 16 * (1 + 4 * (1 + L))
    let qunif := 4 * 2 ^ s
    let q2 := 4 * s * (L + 4)
    let Seed := (Fin qunif → Word n) × (Fin q2 → Fin n → Fin s)
    3 * Fintype.card Seed ≤
      4 * (Finset.univ.filter fun seed : Seed =>
        let a := fun i => sat A (firstSeed T seed i)
        let b := fun j => sat A (secondSeed T seed a j)
        (reportSeed T seed a b).isSome = true).card := by
  intro L qcal qunif q2 Seed
  have hN : 2 ^ n < 2 * (Finset.univ.filter (fun w : Word n => sat A w = true)).card :=
    high_of_above_half (by omega) A hA
  let H0 : CNF n := Finset.univ.filter fun c : Lit n × Lit n =>
    nontaut c ∧ ∀ r : Fin qcal, sat A (T r) = true → T r c.1.1 ≠ c.1.2 ∨ T r c.2.1 ≠ c.2.2
  have hH0_mem : ∀ c : Lit n × Lit n, c ∈ H0 ↔
      nontaut c ∧ ∀ r : Fin qcal, sat A (T r) = true → T r c.1.1 ≠ c.1.2 ∨ T r c.2.1 ≠ c.2.2 :=
    fun c => by simp [H0]
  have hH_eq : ∀ seed : Seed, hull T (fun i => sat A (firstSeed T seed i)) = H0 := by
    intro seed
    ext c
    rw [mem_hull, hH0_mem]
    simp only [firstSeed_cal]
    exact Iff.rfl
  rcases high_structure A hN with hempty | hstar | hdisj
  · have hH0_empty : H0 = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro c hc
      rw [hH0_mem] at hc
      let f : Word n := fun k => if k = c.1.1 then c.1.2 else c.2.2
      let S : Finset (Fin n) := {c.1.1, c.2.1}
      have hScard : S.card ≤ 4 := le_trans (Finset.card_insert_le _ _) (by simp)
      obtain ⟨r, hr⟩ := hT S hScard f
      have hr1 : T r c.1.1 = c.1.2 := by simpa [f, S] using hr c.1.1 (by simp [S])
      have hr2 : T r c.2.1 = c.2.2 := by
        have h := hr c.2.1 (by simp [S])
        dsimp only [f] at h
        split_ifs at h with h12
        · have hb : c.1.2 = c.2.2 := by
            by_contra hne
            exact hc.1 ⟨h12.symm, hne⟩
          rwa [← hb]
        · exact h
      have hsat_r : sat A (T r) = true :=
        (sat_iff_nontaut A (T r)).mpr (fun d hd hnt => (hempty d hd hnt).elim)
      exact (hc.2 r hsat_r).elim (fun h => h hr1) (fun h => h hr2)
    have hall : (Finset.univ.filter fun seed : Seed =>
        let a := fun i => sat A (firstSeed T seed i)
        let b := fun j => sat A (secondSeed T seed a j)
        (reportSeed T seed a b).isSome = true) = Finset.univ := by
      ext seed
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact reportSeed_empty_isSome T seed _ _ (by rw [hH_eq seed, hH0_empty])
    rw [hall, Finset.card_univ]
    omega
  · by_cases hempty : ∀ c ∈ A, ¬ nontaut c
    · have hH0_empty : H0 = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro c hc
        rw [hH0_mem] at hc
        let f : Word n := fun k => if k = c.1.1 then c.1.2 else c.2.2
        let S : Finset (Fin n) := {c.1.1, c.2.1}
        have hScard : S.card ≤ 4 := le_trans (Finset.card_insert_le _ _) (by simp)
        obtain ⟨r, hr⟩ := hT S hScard f
        have hr1 : T r c.1.1 = c.1.2 := by simpa [f, S] using hr c.1.1 (by simp [S])
        have hr2 : T r c.2.1 = c.2.2 := by
          have h := hr c.2.1 (by simp [S])
          dsimp only [f] at h
          split_ifs at h with h12
          · have hb : c.1.2 = c.2.2 := by
              by_contra hne
              exact hc.1 ⟨h12.symm, hne⟩
            rwa [← hb]
          · exact h
        have hsat_r : sat A (T r) = true :=
          (sat_iff_nontaut A (T r)).mpr (fun d hd hnt => (hempty d hd hnt).elim)
        exact (hc.2 r hsat_r).elim (fun h => h hr1) (fun h => h hr2)
      have hall : (Finset.univ.filter fun seed : Seed =>
          let a := fun i => sat A (firstSeed T seed i)
          let b := fun j => sat A (secondSeed T seed a j)
          (reportSeed T seed a b).isSome = true) = Finset.univ := by
        ext seed
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact reportSeed_empty_isSome T seed _ _ (by rw [hH_eq seed, hH0_empty])
      rw [hall, Finset.card_univ]
      omega
    · push Not at hempty
      rcases hempty with ⟨c0, hc0A, hnt0⟩
      have hH0_ne : H0 ≠ ∅ := by
        intro h0
        have hmem : c0 ∈ H0 := by
          let seed0 : Seed := (fun _ _ => false, fun _ _ => ⟨0, by omega⟩)
          have h1 := sub_hull T seed0 A c0 hc0A hnt0
          rwa [hH_eq seed0] at h1
        rw [h0] at hmem
        exact Finset.notMem_empty c0 hmem
      rcases hstar with ⟨L0, hL0⟩
      have hH0_star : isStarHull H0 := by
        refine ⟨L0, fun c hc => ?_⟩
        by_contra hno
        push Not at hno
        rw [hH0_mem] at hc
        let f : Word n := fun k =>
          if k = L0.1 then !(L0.2)
          else if k = c.1.1 then c.1.2
          else c.2.2
        let S : Finset (Fin n) := {L0.1, c.1.1, c.2.1}
        have hScard : S.card ≤ 4 :=
          le_trans (Finset.card_insert_le _ _)
            (Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) (by simp)))
        obtain ⟨r, hr⟩ := hT S hScard f
        have hr0 : T r L0.1 = !(L0.2) := by simpa [f, S] using hr L0.1 (by simp [S])
        have hr1 : T r c.1.1 = c.1.2 := by
          have h := hr c.1.1 (by simp [S])
          dsimp only [f] at h
          by_cases h10 : c.1.1 = L0.1
          · simp only [h10, ↓reduceIte] at h
            have hb : c.1.2 = !(L0.2) := by
              cases h1 : c.1.2 <;> cases h2 : L0.2
              · exfalso; exact hno.1 (Prod.ext h10 (h1.trans h2.symm))
              · rfl
              · rfl
              · exfalso; exact hno.1 (Prod.ext h10 (h1.trans h2.symm))
            rw [h10, hb]; exact h
          · simp only [h10, ↓reduceIte] at h
            exact h
        have hr2 : T r c.2.1 = c.2.2 := by
          have h := hr c.2.1 (by simp [S])
          dsimp only [f] at h
          split_ifs at h with h20 h21
          · have hb : c.2.2 = !(L0.2) := by
              cases h1 : c.2.2 <;> cases h2 : L0.2
              · exfalso; exact hno.2 (Prod.ext h20 (h1.trans h2.symm))
              · rfl
              · rfl
              · exfalso; exact hno.2 (Prod.ext h20 (h1.trans h2.symm))
            rwa [hb]
          · have hb : c.1.2 = c.2.2 := by
              by_contra hne
              exact hc.1 ⟨h21.symm, hne⟩
            rwa [← hb]
          · exact h
        have hsat_r : sat A (T r) = true := by
          refine (sat_iff_nontaut A (T r)).mpr fun d hd hntd => ?_
          rcases hL0 d hd hntd with hd1 | hd2
          · left; rw [hd1, hr0]; cases L0.2 <;> decide
          · right; rw [hd2, hr0]; cases L0.2 <;> decide
        exact (hc.2 r hsat_r).elim (fun h => h hr1) (fun h => h hr2)
      let Lp := Classical.choose hH0_star
      have hLpH : ∀ c ∈ H0, c.1 = Lp ∨ c.2 = Lp := Classical.choose_spec hH0_star
      have hLpA : ∀ c ∈ A, nontaut c → c.1 = Lp ∨ c.2 = Lp := by
        intro c hc hnt
        let seed0 : Seed := (fun _ _ => false, fun _ _ => ⟨0, by omega⟩)
        have hmem := sub_hull T seed0 A c hc hnt
        rw [hH_eq seed0] at hmem
        exact hLpH c hmem
      have hno_both : ∀ k : Fin n, k ≠ Lp.1 →
          ¬ (hasClause A Lp (k, true) ∧ hasClause A Lp (k, false)) := by
        rintro k _ ⟨⟨c1, hc1, hnt1, hsc1⟩, ⟨c2, hc2, hnt2, hsc2⟩⟩
        have hsub : Finset.univ.filter (fun w : Word n => sat A w = true) ⊆
            Finset.univ.filter (fun w : Word n => ∀ i ∈ ({Lp.1} : Finset (Fin n)), w i = !(Lp.2)) := by
          intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hw ⊢
          intro i hi
          subst hi
          by_contra hne
          have hwL : w Lp.1 = Lp.2 := bool_eq_of_ne_not hne
          have hs1 := (sat_iff_nontaut A w).mp hw c1 hc1 hnt1
          have hs2 := (sat_iff_nontaut A w).mp hw c2 hc2 hnt2
          have h1 : w k ≠ true := by
            rcases hsc1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · rw [e1, e2] at hs1; exact hs1.resolve_left (not_not.mpr hwL)
            · rw [e1, e2] at hs1; exact hs1.resolve_right (not_not.mpr hwL)
          have h2 : w k ≠ false := by
            rcases hsc2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · rw [e1, e2] at hs2; exact hs2.resolve_left (not_not.mpr hwL)
            · rw [e1, e2] at hs2; exact hs2.resolve_right (not_not.mpr hwL)
          cases hwk : w k
          · exact h2 hwk
          · exact h1 hwk
        have hle := Finset.card_le_card hsub
        rw [card_word_eq_on, Finset.card_singleton] at hle
        have h2n : 2 * 2 ^ (n - 1) = 2 ^ n := by
          have hn1 : n = (n - 1) + 1 := by omega
          conv_rhs => rw [hn1, pow_succ']
        omega
      let Kp : Finset (Fin n) := Finset.univ.filter fun k =>
        k ≠ Lp.1 ∧ ∃ d : Bool, hasClause A Lp (k, d)
      let dp : Fin n → Bool := fun k => decide (hasClause A Lp (k, true))
      have hKp_has : ∀ k ∈ Kp, hasClause A Lp (k, dp k) := by
        intro k hk
        simp only [Kp, Finset.mem_filter, Finset.mem_univ, true_and] at hk
        rcases hk with ⟨hne, d, hd⟩
        by_cases ht : hasClause A Lp (k, true)
        · dsimp only [dp]; rw [decide_eq_true ht]; exact ht
        · dsimp only [dp]; rw [decide_eq_false ht]
          cases d
          · exact hd
          · exact absurd hd ht
      have hsat_Kp : ∀ w : Word n,
          sat A w = true ↔ w Lp.1 ≠ Lp.2 ∨ ∀ k ∈ Kp, w k ≠ dp k := by
        intro w
        rw [sat_iff_nontaut]
        constructor
        · intro hw
          by_cases hw0 : w Lp.1 = Lp.2
          · right
            intro k hk
            rcases hKp_has k hk with ⟨c, hc, hnt, hsc⟩
            have hwc := hw c hc hnt
            rcases hsc with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · rw [e1, e2] at hwc; exact hwc.resolve_left (not_not.mpr hw0)
            · rw [e1, e2] at hwc; exact hwc.resolve_right (not_not.mpr hw0)
          · exact Or.inl hw0
        · intro hw c hc hnt
          have hnounit := no_unit_of_above_half A hN c hc hnt
          rcases hw with hw0 | hwK
          · rcases hLpA c hc hnt with h1 | h2
            · left; rwa [h1]
            · right; rwa [h2]
          · rcases hLpA c hc hnt with h1 | h2
            · have hk_ne : c.2.1 ≠ Lp.1 := by rw [← h1]; exact hnounit.symm
              have hmem : c.2.1 ∈ Kp := by
                simp only [Kp, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨hk_ne, c.2.2, c, hc, hnt, Or.inl ⟨h1, rfl⟩⟩
              have hd_eq : c.2.2 = dp c.2.1 := by
                have h1' := hKp_has c.2.1 hmem
                have h2' : hasClause A Lp (c.2.1, c.2.2) := ⟨c, hc, hnt, Or.inl ⟨h1, rfl⟩⟩
                cases hd1 : c.2.2 <;> cases hd2 : dp c.2.1
                · rfl
                · exfalso; rw [hd2] at h1'; rw [hd1] at h2'; exact hno_both c.2.1 hk_ne ⟨h1', h2'⟩
                · exfalso; rw [hd2] at h1'; rw [hd1] at h2'; exact hno_both c.2.1 hk_ne ⟨h2', h1'⟩
                · rfl
              right; rw [hd_eq]; exact hwK c.2.1 hmem
            · have hk_ne : c.1.1 ≠ Lp.1 := by rw [← h2]; exact hnounit
              have hmem : c.1.1 ∈ Kp := by
                simp only [Kp, Finset.mem_filter, Finset.mem_univ, true_and]
                exact ⟨hk_ne, c.1.2, c, hc, hnt, Or.inr ⟨rfl, h2⟩⟩
              have hd_eq : c.1.2 = dp c.1.1 := by
                have h1' := hKp_has c.1.1 hmem
                have h2' : hasClause A Lp (c.1.1, c.1.2) := ⟨c, hc, hnt, Or.inr ⟨rfl, h2⟩⟩
                cases hd1 : c.1.2 <;> cases hd2 : dp c.1.1
                · rfl
                · exfalso; rw [hd2] at h1'; rw [hd1] at h2'; exact hno_both c.1.1 hk_ne ⟨h1', h2'⟩
                · exfalso; rw [hd2] at h1'; rw [hd1] at h2'; exact hno_both c.1.1 hk_ne ⟨h2', h1'⟩
                · rfl
              left; rw [hd_eq]; exact hwK c.1.1 hmem
      have hKp0 : Lp.1 ∉ Kp := by simp [Kp]
      have hKp_lt : Kp.card + 1 ≤ n := by
        have : (insert Lp.1 Kp).card ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        rw [Finset.card_insert_of_notMem hKp0, Finset.card_univ, Fintype.card_fin] at this
        exact this
      have hcardA : (Finset.univ.filter (fun w : Word n => sat A w = true)).card =
          2 ^ (n - 1) + 2 ^ (n - 1 - Kp.card) := by
        have heq : Finset.univ.filter (fun w : Word n => sat A w = true) =
            Finset.univ.filter (fun w : Word n => w Lp.1 ≠ Lp.2 ∨ ∀ k ∈ Kp, w k ≠ dp k) := by
          ext w; simp [hsat_Kp]
        rw [heq, card_star_sat Lp Kp hKp0 dp]
      have hKp_le : Kp.card ≤ s - 1 := by
        have h1 : 2 ^ n * (2 ^ (s - 1) + 1) ≤ 2 ^ s * (2 ^ (n - 1) + 2 ^ (n - 1 - Kp.card)) := by
          dsimp only [high] at hA
          rwa [hcardA] at hA
        exact (high_iff_star_card (by omega) hsn Kp.card hKp_lt).mp h1
      let U1 := Fin qunif → Word n
      let U2 := Fin q2 → Fin n → Fin s
      let G1 : Finset U1 := Finset.univ.filter fun u1 =>
        ∃ t : Fin qunif, u1 t Lp.1 = Lp.2 ∧ sat A (u1 t) = true
      let B1 : Finset U1 := Finset.univ.filter fun u1 =>
        ¬ ∃ t : Fin qunif, u1 t Lp.1 = Lp.2 ∧ sat A (u1 t) = true
      let G2 : Finset U2 := Finset.univ.filter fun u2 =>
        ∀ k : Fin n, k ≠ Lp.1 →
          ∃ j : Fin q2, (u2 j k).val = 0 ∧ ∀ v ∈ Kp.erase k, (u2 j v).val ≠ 0
      let B2 : Finset U2 := Finset.univ.filter fun u2 =>
        ¬ ∀ k : Fin n, k ≠ Lp.1 →
          ∃ j : Fin q2, (u2 j k).val = 0 ∧ ∀ v ∈ Kp.erase k, (u2 j v).val ≠ 0
      have hG1B1 : G1.card + B1.card = Fintype.card U1 := by
        have h := card_filter_add_not (Finset.univ : Finset U1)
          (fun u1 => ∃ t : Fin qunif, u1 t Lp.1 = Lp.2 ∧ sat A (u1 t) = true)
        rwa [Finset.card_univ] at h
      have hG2B2 : G2.card + B2.card = Fintype.card U2 := by
        have h := card_filter_add_not (Finset.univ : Finset U2)
          (fun u2 => ∀ k : Fin n, k ≠ Lp.1 →
            ∃ j : Fin q2, (u2 j k).val = 0 ∧ ∀ v ∈ Kp.erase k, (u2 j v).val ≠ 0)
        rwa [Finset.card_univ] at h
      have hB1_bound : 16 * B1.card ≤ Fintype.card U1 := by
        let GoodW : Finset (Word n) := Finset.univ.filter fun w =>
          w Lp.1 = Lp.2 ∧ sat A w = true
        let BadW : Finset (Word n) := Finset.univ.filter fun w =>
          ¬ (w Lp.1 = Lp.2 ∧ sat A w = true)
        have hGW_eq : GoodW = Finset.univ.filter (fun w : Word n =>
            ∀ i ∈ insert Lp.1 Kp, w i = if i = Lp.1 then Lp.2 else !(dp i)) := by
          ext w
          simp only [GoodW, Finset.mem_filter, Finset.mem_univ, true_and, hsat_Kp,
            Finset.mem_insert]
          constructor
          · rintro ⟨hw0, hor⟩ i (rfl | hiK)
            · simp [hw0]
            · have hne : i ≠ Lp.1 := fun he => hKp0 (he ▸ hiK)
              have hwi := hor.resolve_left (not_not.mpr hw0) i hiK
              simp only [hne, ↓reduceIte]
              exact bool_eq_not_of_ne hwi
          · intro h
            have hw0 : w Lp.1 = Lp.2 := by simpa using h Lp.1 (Or.inl rfl)
            refine ⟨hw0, Or.inr fun k hk => ?_⟩
            have hne : k ≠ Lp.1 := fun he => hKp0 (he ▸ hk)
            have hwk := h k (Or.inr hk)
            simp only [hne, ↓reduceIte] at hwk
            rw [hwk]
            cases dp k <;> decide
        have hGW_card : GoodW.card = 2 ^ (n - 1 - Kp.card) := by
          rw [hGW_eq, card_word_eq_on, Finset.card_insert_of_notMem hKp0]
          congr 1; omega
        have hBW_sum : GoodW.card + BadW.card = 2 ^ n := by
          have h := card_filter_add_not (Finset.univ : Finset (Word n))
            (fun w => w Lp.1 = Lp.2 ∧ sat A w = true)
          rwa [Finset.card_univ, card_word] at h
        have h2s_GW : 2 ^ n ≤ 2 ^ s * GoodW.card := by
          rw [hGW_card, ← pow_add]
          exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
        have h2s_BW : 2 ^ s * BadW.card ≤ (2 ^ s - 1) * 2 ^ n := by
          have h1 : 2 ^ s * GoodW.card + 2 ^ s * BadW.card = 2 ^ s * 2 ^ n := by
            rw [← Nat.mul_add, hBW_sum]
          have h2 : (2 ^ s - 1) * 2 ^ n + 2 ^ n = 2 ^ s * 2 ^ n := by
            have hpos : 1 ≤ 2 ^ s := Nat.one_le_pow _ _ (by decide)
            calc
              (2 ^ s - 1) * 2 ^ n + 2 ^ n = (2 ^ s - 1) * 2 ^ n + 1 * 2 ^ n := by rw [Nat.one_mul]
              _ = ((2 ^ s - 1) + 1) * 2 ^ n := (Nat.add_mul _ _ _).symm
              _ = 2 ^ s * 2 ^ n := by rw [Nat.sub_add_cancel hpos]
          omega
        have hB1_eq : B1 = Finset.univ.filter (fun u1 : U1 => ∀ t : Fin qunif, u1 t ∈ BadW) := by
          ext u1
          simp [B1, BadW]
        rw [hB1_eq, card_forall_in]
        have hU1_card : Fintype.card U1 = (2 ^ n) ^ qunif := by
          simp [U1]
        rw [hU1_card]
        have hpow := pow_le_of_mul_le (2 ^ s) 4 (2 ^ n) BadW.card
          (Nat.one_le_pow _ _ (by decide)) h2s_BW
        have h16_eq : (2 : ℕ) ^ 4 = 16 := by decide
        have hq_eq : 2 ^ s * 4 = qunif := mul_comm _ _
        rwa [h16_eq, hq_eq] at hpow
      have hB2_bound : 16 * B2.card ≤ Fintype.card U2 := by
        let Bad2k : Fin n → Finset U2 := fun k =>
          Finset.univ.filter fun u2 =>
            ∀ j : Fin q2, ¬ ((u2 j k).val = 0 ∧ ∀ v ∈ Kp.erase k, (u2 j v).val ≠ 0)
        have hB2_sub : B2 ⊆ (Finset.univ.erase Lp.1).biUnion Bad2k := by
          intro u2 hu2
          simp only [B2, Finset.mem_filter, Finset.mem_univ, true_and, not_forall,
            not_exists] at hu2
          rcases hu2 with ⟨k, hkne, hkbad⟩
          refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_erase.mpr ⟨hkne, Finset.mem_univ k⟩, ?_⟩
          simp only [Bad2k, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hkbad
        have hU2_card : Fintype.card U2 = (s ^ n) ^ q2 := by
          simp [U2]
        have hBad2k_le : ∀ k ∈ Finset.univ.erase Lp.1,
            2 ^ (L + 4) * (Bad2k k).card ≤ (s ^ n) ^ q2 := by
          intro k _
          let E := Kp.erase k
          let P_k : Finset (Fin n → Fin s) := Finset.univ.filter fun r =>
            (r k).val = 0 ∧ ∀ v ∈ E, (r v).val ≠ 0
          let Q_k : Finset (Fin n → Fin s) := Finset.univ.filter fun r =>
            ¬ ((r k).val = 0 ∧ ∀ v ∈ E, (r v).val ≠ 0)
          have hPk_card : P_k.card = (s - 1) ^ E.card * s ^ (n - 1 - E.card) :=
            card_fin_hit_avoid (by omega) k E (Finset.notMem_erase k Kp)
          have hPQ_sum : P_k.card + Q_k.card = s ^ n := by
            have h := card_filter_add_not (Finset.univ : Finset (Fin n → Fin s))
              (fun r => (r k).val = 0 ∧ ∀ v ∈ E, (r v).val ≠ 0)
            rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
            exact h
          have hE_le : E.card ≤ s - 1 := le_trans (Finset.card_erase_le) hKp_le
          have h4s_Pk : s ^ n ≤ 4 * s * P_k.card := by
            rw [hPk_card]
            have hpow_sn : s ^ n = s * s ^ E.card * s ^ (n - 1 - E.card) := by
              rw [mul_assoc, ← pow_add, ← pow_succ']
              congr 1; omega
            have hsk := pow_le_four_mul_pred_pow s E.card (by omega) hE_le
            calc
              s ^ n = s ^ E.card * (s * s ^ (n - 1 - E.card)) := by rw [hpow_sn]; ac_rfl
              _ ≤ (4 * (s - 1) ^ E.card) * (s * s ^ (n - 1 - E.card)) :=
                Nat.mul_le_mul_right _ hsk
              _ = 4 * s * ((s - 1) ^ E.card * s ^ (n - 1 - E.card)) := by ac_rfl
          have h4s_Qk : 4 * s * Q_k.card ≤ (4 * s - 1) * s ^ n := by
            have h1 : 4 * s * P_k.card + 4 * s * Q_k.card = 4 * s * s ^ n := by
              rw [← Nat.mul_add, hPQ_sum]
            have h2 : (4 * s - 1) * s ^ n + s ^ n = 4 * s * s ^ n := by
              calc
                (4 * s - 1) * s ^ n + s ^ n = (4 * s - 1) * s ^ n + 1 * s ^ n := by rw [Nat.one_mul]
                _ = ((4 * s - 1) + 1) * s ^ n := (Nat.add_mul _ _ _).symm
                _ = 4 * s * s ^ n := by rw [Nat.sub_add_cancel (by omega)]
            omega
          have hBad2k_eq : Bad2k k = Finset.univ.filter (fun u2 : U2 => ∀ j : Fin q2, u2 j ∈ Q_k) := by
            ext u2
            simp [Bad2k, Q_k, E]
          rw [hBad2k_eq, card_forall_in]
          exact pow_le_of_mul_le (4 * s) (L + 4) (s ^ n) Q_k.card (by omega) h4s_Qk
        have hunion : 2 ^ (L + 4) * B2.card ≤ (Finset.univ.erase Lp.1).card * (s ^ n) ^ q2 := by
          have h1 : B2.card ≤ ∑ k ∈ Finset.univ.erase Lp.1, (Bad2k k).card :=
            le_trans (Finset.card_le_card hB2_sub) Finset.card_biUnion_le
          calc
            2 ^ (L + 4) * B2.card
              ≤ 2 ^ (L + 4) * ∑ k ∈ Finset.univ.erase Lp.1, (Bad2k k).card :=
                Nat.mul_le_mul_left _ h1
            _ = ∑ k ∈ Finset.univ.erase Lp.1, 2 ^ (L + 4) * (Bad2k k).card :=
                Finset.mul_sum _ _ _
            _ ≤ ∑ _k ∈ Finset.univ.erase Lp.1, (s ^ n) ^ q2 :=
                Finset.sum_le_sum hBad2k_le
            _ = (Finset.univ.erase Lp.1).card * (s ^ n) ^ q2 := by
                rw [Finset.sum_const, Nat.nsmul_eq_mul]
        have hL : n + 1 ≤ 2 ^ L := Nat.le_pow_clog (by decide : 1 < 2) (n + 1)
        have her_le : (Finset.univ.erase Lp.1).card ≤ 2 ^ L := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ Lp.1), Finset.card_univ, Fintype.card_fin]
          omega
        have h2L4 : 2 ^ (L + 4) = 2 ^ L * 16 := by
          rw [pow_add]
          have : (2 : ℕ) ^ 4 = 16 := by decide
          rw [this]
        have hmul_le : 2 ^ L * (16 * B2.card) ≤ 2 ^ L * (s ^ n) ^ q2 := by
          calc
            2 ^ L * (16 * B2.card) = 2 ^ (L + 4) * B2.card := by rw [h2L4]; ac_rfl
            _ ≤ (Finset.univ.erase Lp.1).card * (s ^ n) ^ q2 := hunion
            _ ≤ 2 ^ L * (s ^ n) ^ q2 := Nat.mul_le_mul_right _ her_le
        rw [hU2_card]
        exact Nat.le_of_mul_le_mul_left hmul_le (Nat.pow_pos (by decide))
      have hgood_sub : G1 ×ˢ G2 ⊆ Finset.univ.filter fun seed : Seed =>
          let a := fun i => sat A (firstSeed T seed i)
          let b := fun j => sat A (secondSeed T seed a j)
          (reportSeed T seed a b).isSome = true := by
        rintro ⟨u1, u2⟩ hmem
        simp only [Finset.mem_product, G1, G2, Finset.mem_filter, Finset.mem_univ,
          true_and] at hmem ⊢
        rcases hmem with ⟨hu1, hu2⟩
        let a : Fin (qcal + qunif) → Bool := fun i => sat A (firstSeed T (u1, u2) i)
        let b : Fin q2 → Bool := fun j => sat A (secondSeed T (u1, u2) a j)
        have hHa : hull T a = H0 := hH_eq (u1, u2)
        have hP : hasPassOn (u1, u2) a Lp := by
          rcases hu1 with ⟨t, ht1, ht2⟩
          refine ⟨t, ht1, ?_⟩
          dsimp only [a]
          rw [firstSeed_unif]
          exact ht2
        let t := Classical.choose hP
        have ht_spec : u1 t Lp.1 = Lp.2 ∧ a (unifIdx t) = true := Classical.choose_spec hP
        let wstar := u1 t
        have hwsat : sat A wstar = true := by
          have h1 := ht_spec.2
          dsimp only [a] at h1
          rwa [firstSeed_unif] at h1
        have hw_Kp : ∀ k ∈ Kp, wstar k ≠ dp k :=
          ((hsat_Kp wstar).mp hwsat).resolve_left (not_not.mpr ht_spec.1)
        have hsec_eq : ∀ j : Fin q2, secondSeed T (u1, u2) a j = flipAt wstar Lp.1 (u2 j) :=
          fun j => secondSeed_star_eq T (u1, u2) a H0 hHa hH0_ne hH0_star hP j
        have hb_iff : ∀ j : Fin q2, b j = true ↔ ∀ k ∈ Kp, (u2 j k).val ≠ 0 := by
          intro j
          dsimp only [b]
          rw [hsec_eq j, hsat_Kp]
          have hfi : flipAt wstar Lp.1 (u2 j) Lp.1 = Lp.2 := by
            simp [flipAt, wstar, ht_spec.1]
          rw [hfi]
          simp only [ne_eq, not_true_eq_false, false_or]
          constructor
          · intro h k hk
            have hne : k ≠ Lp.1 := fun he => hKp0 (he ▸ hk)
            have hwk := h k hk
            have hworig := hw_Kp k hk
            intro h0
            have hfl : flipAt wstar Lp.1 (u2 j) k = !(wstar k) := by
              dsimp only [flipAt]
              split_ifs with hc
              · rfl
              · exact absurd ⟨hne, h0⟩ hc
            rw [hfl] at hwk
            exact hwk (by rw [bool_eq_not_of_ne hworig, Bool.not_not])
          · intro h k hk
            have h0 := h k hk
            simp only [flipAt, h0, and_false, ↓reduceIte]
            exact hw_Kp k hk
        let U : Finset (Fin n) := Finset.univ.filter fun k =>
          k ≠ Lp.1 ∧ ∀ j : Fin q2, b j = true → (u2 j k).val ≠ 0
        have hU_eq : U = Kp := by
          ext k
          simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hkne, hsurv⟩
            by_contra hkKp
            obtain ⟨j, hj0, hjE⟩ := hu2 k hkne
            have hbt : b j = true := by
              rw [hb_iff]
              intro v hv
              have hvk : v ≠ k := fun he => hkKp (he ▸ hv)
              exact hjE v (Finset.mem_erase.mpr ⟨hvk, hv⟩)
            exact hsurv j hbt hj0
          · intro hkKp
            have hkne : k ≠ Lp.1 := fun he => hKp0 (he ▸ hkKp)
            exact ⟨hkne, fun j hbt => (hb_iff j).mp hbt k hkKp⟩
        have hCert : U.card ≤ s - 1 ∧
            ∀ k ∈ U, ∃ j : Fin q2, b j = false ∧ ∀ v ∈ U, ((u2 j v).val = 0 ↔ v = k) := by
          rw [hU_eq]
          refine ⟨hKp_le, fun k hk => ?_⟩
          have hkne : k ≠ Lp.1 := fun he => hKp0 (he ▸ hk)
          obtain ⟨j, hj0, hjE⟩ := hu2 k hkne
          refine ⟨j, ?_, ?_⟩
          · cases hbj : b j
            · rfl
            · exfalso; exact (hb_iff j).mp hbj k hk hj0
          · intro v hv
            constructor
            · intro hv0
              by_contra hvk
              exact hjE v (Finset.mem_erase.mpr ⟨hvk, hv⟩) hv0
            · intro hvk
              rwa [hvk]
        exact reportSeed_star_isSome T (u1, u2) a b H0 hHa hH0_ne hH0_star hP hCert
      have hG1_15 : 15 * Fintype.card U1 ≤ 16 * G1.card := by omega
      have hG2_15 : 15 * Fintype.card U2 ≤ 16 * G2.card := by omega
      have hprod : 225 * Fintype.card Seed ≤ 256 * (G1 ×ˢ G2).card := by
        have hSeed : Fintype.card Seed = Fintype.card U1 * Fintype.card U2 := Fintype.card_prod U1 U2
        rw [hSeed, Finset.card_product]
        have h225 : 225 = 15 * 15 := rfl
        have h256 : 256 = 16 * 16 := rfl
        rw [h225, h256]
        calc
          15 * 15 * (Fintype.card U1 * Fintype.card U2)
            = (15 * Fintype.card U1) * (15 * Fintype.card U2) := by ac_rfl
          _ ≤ (16 * G1.card) * (16 * G2.card) := Nat.mul_le_mul hG1_15 hG2_15
          _ = 16 * 16 * (G1.card * G2.card) := by ac_rfl
      have hle_filt := Finset.card_le_card hgood_sub
      omega
  · rcases hdisj with ⟨c1, hc1, c2, hc2, hnt1, hnt2, hd, hallA⟩
    have hsatA_pred : ∀ w : Word n,
        sat A w = predC1C2 c1.1.2 c1.2.2 c2.1.2 c2.2.2 (w c1.1.1, w c1.2.1, w c2.1.1, w c2.2.1) := by
      intro w
      apply Bool.eq_iff_iff.mpr
      rw [sat_iff_nontaut]
      simp only [predC1C2, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne]
      constructor
      · intro hw; exact ⟨hw c1 hc1 hnt1, hw c2 hc2 hnt2⟩
      · rintro ⟨hs1, hs2⟩ c hc hnt
        rcases hallA c hc hnt with (⟨e1, e2⟩ | ⟨e1, e2⟩) | (⟨e1, e2⟩ | ⟨e1, e2⟩)
        · rw [e1, e2]; exact hs1
        · rw [e1, e2]; exact hs1.symm
        · rw [e1, e2]; exact hs2
        · rw [e1, e2]; exact hs2.symm
    have hs4 : 4 ≤ s := (high_disj2_iff hs c1 c2 hd A hsatA_pred).mp hA
    have hc1H0 : c1 ∈ H0 := by
      let seed0 : Seed := (fun _ _ => false, fun _ _ => ⟨0, by omega⟩)
      have h1 := sub_hull T seed0 A c1 hc1 hnt1
      rwa [hH_eq seed0] at h1
    have hc2H0 : c2 ∈ H0 := by
      let seed0 : Seed := (fun _ _ => false, fun _ _ => ⟨0, by omega⟩)
      have h1 := sub_hull T seed0 A c2 hc2 hnt2
      rwa [hH_eq seed0] at h1
    have hH0_ne : H0 ≠ ∅ := by
      intro h0; rw [h0] at hc1H0; exact Finset.notMem_empty c1 hc1H0
    have hH0_not_star : ¬ isStarHull H0 := by
      rintro ⟨L0, hL0⟩
      rcases hL0 c1 hc1H0 with h1 | h1 <;> rcases hL0 c2 hc2H0 with h2 | h2
      · exact hd.2.1 (by rw [h1, h2])
      · exact hd.2.2.1 (by rw [h1, h2])
      · exact hd.2.2.2.1 (by rw [h1, h2])
      · exact hd.2.2.2.2.1 (by rw [h1, h2])
    have hH0_disj : isDisj2Hull H0 := by
      refine ⟨c1, hc1H0, c2, hc2H0, hd, fun c hc => ?_⟩
      by_contra hno
      push Not at hno
      rw [hH0_mem] at hc
      by_cases heq : c.1.1 = c.2.1
      · have hb : c.1.2 = c.2.2 := by
          by_contra hne
          exact hc.1 ⟨heq, hne⟩
        obtain ⟨S, f, hSc, hfix⟩ := exists_fix_unit_third
          c1.1.1 c1.2.1 c2.1.1 c2.2.1 c.1.1 c1.1.2 c1.2.2 c2.1.2 c2.2.2 c.1.2
          hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2
        obtain ⟨r, hr⟩ := hT S hSc f
        have hfr := hfix (T r) hr
        have hsat_r : sat A (T r) = true := by
          rw [hsatA_pred]
          simp only [predC1C2, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne]
          exact ⟨hfr.1, hfr.2.1⟩
        exact (hc.2 r hsat_r).elim (fun h => h hfr.2.2) (fun h => h (by rw [← heq, ← hb]; exact hfr.2.2))
      · obtain ⟨k1, k2, k3, k4, v1, v2, v3, v4, hk12, hk13, hk14, hk23, hk24, hk34, hfix⟩ :=
          exists_fix_third_clause c1.1.1 c1.2.1 c2.1.1 c2.2.1 c.1.1 c.2.1
            c1.1.2 c1.2.2 c2.1.2 c2.2.2 c.1.2 c.2.2
            hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2 heq hno.1 hno.2
        let f : Word n := fun k =>
          if k = k1 then v1 else if k = k2 then v2 else if k = k3 then v3 else v4
        let S : Finset (Fin n) := {k1, k2, k3, k4}
        have hSc : S.card ≤ 4 :=
          le_trans (Finset.card_insert_le _ _)
            (Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _)
              (Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) (by simp)))))
        obtain ⟨r, hr⟩ := hT S hSc f
        have hr1 : T r k1 = v1 := by simpa [f, S] using hr k1 (by simp [S])
        have hr2 : T r k2 = v2 := by simpa [f, S, hk12.symm] using hr k2 (by simp [S])
        have hr3 : T r k3 = v3 := by simpa [f, S, hk13.symm, hk23.symm] using hr k3 (by simp [S])
        have hr4 : T r k4 = v4 := by
          simpa [f, S, hk14.symm, hk24.symm, hk34.symm] using hr k4 (by simp [S])
        have hfr := hfix (T r) hr1 hr2 hr3 hr4
        have hsat_r : sat A (T r) = true := by
          rw [hsatA_pred]
          simp only [predC1C2, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne]
          exact ⟨hfr.1, hfr.2.1⟩
        exact (hc.2 r hsat_r).elim (fun h => h hfr.2.2.1) (fun h => h hfr.2.2.2)
    have hall : (Finset.univ.filter fun seed : Seed =>
        let a := fun i => sat A (firstSeed T seed i)
        let b := fun j => sat A (secondSeed T seed a j)
        (reportSeed T seed a b).isSome = true) = Finset.univ := by
      ext seed
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact reportSeed_disj2_isSome T seed _ _ H0 (hH_eq seed) hH0_ne hH0_not_star hs4 hH0_disj
    rw [hall, Finset.card_univ]
    omega

end PEqualNP.Outside.L_lib_673

theorem PEqualNP.Outside.L_lib_673 : ∀ (n s : ℕ), 3 ≤ s → s ≤ n →
  let W := Fin n → Bool
  let Lit := Fin n × Bool
  let F := Finset (Lit × Lit)
  let sat := fun (C : F) (w : W) => decide (∀ c ∈ C,
    w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)
  let high := fun (G : F) =>
    2 ^ n * (2 ^ (s - 1) + 1) ≤
      2 ^ s * (Finset.univ.filter (fun x => sat G x = true)).card
  let L := Nat.clog 2 (n + 1)
  let q₁ := 16 * (1 + 4 * (1 + L)) + 4 * 2 ^ s
  let q₂ := 4 * s * (L + 4)
  ∃ M : ℕ, 0 < M ∧
    ∃ (first : Fin M → Fin q₁ → W)
      (second : Fin M → (Fin q₁ → Bool) → Fin q₂ → W)
      (report : Fin M → (Fin q₁ → Bool) → (Fin q₂ → Bool) → Option F),
      ∀ A : F,
        let result := fun seed : Fin M =>
          let a := fun i => sat A (first seed i)
          let b := fun j => sat A (second seed a j)
          report seed a b
        (∀ t B, result t = some B → high A ∧ ∀ z, sat B z = sat A z) ∧
        (high A → 3 * M ≤
          4 * (Finset.univ.filter (fun u : Fin M => (result u).isSome = true)).card) := by
  intro n s hs hsn W Lit F sat_loc high_loc L q₁ q₂
  let qcal := 16 * (1 + 4 * (1 + L))
  let qunif := 4 * 2 ^ s
  let Seed := (Fin qunif → PEqualNP.Outside.L_lib_673.Word n) × (Fin q₂ → Fin n → Fin s)
  let M := Fintype.card Seed
  let eSeed : Seed ≃ Fin M := Fintype.equivFin Seed
  have hMpos : 0 < M := by
    dsimp only [M]
    have : Nonempty Seed := ⟨(fun _ _ => false, fun _ _ => ⟨0, by omega⟩)⟩
    exact Fintype.card_pos
  obtain ⟨T, hT⟩ := PEqualNP.Outside.L_lib_673.exists_cal n (by omega)
  refine ⟨M, hMpos,
    fun u => PEqualNP.Outside.L_lib_673.firstSeed T (eSeed.symm u),
    fun u => PEqualNP.Outside.L_lib_673.secondSeed T (eSeed.symm u),
    fun u => PEqualNP.Outside.L_lib_673.reportSeed T (eSeed.symm u), ?_⟩
  intro A result
  constructor
  · intro t B hres
    exact PEqualNP.Outside.L_lib_673.sound_protocol hs hsn T hT (eSeed.symm t) A B hres
  · intro hA
    have hcomp := PEqualNP.Outside.L_lib_673.complete_protocol hs hsn T hT A hA
    have hbij : (Finset.univ.filter fun u : Fin M => (result u).isSome = true).card =
        (Finset.univ.filter fun seed : Seed =>
          let a := fun i => PEqualNP.Outside.L_lib_673.sat A
            (PEqualNP.Outside.L_lib_673.firstSeed T seed i)
          let b := fun j => PEqualNP.Outside.L_lib_673.sat A
            (PEqualNP.Outside.L_lib_673.secondSeed T seed a j)
          (PEqualNP.Outside.L_lib_673.reportSeed T seed a b).isSome = true).card := by
      refine Finset.card_bij (fun u _ => eSeed.symm u) ?_ ?_ ?_
      · intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        exact hu
      · intro u1 _ u2 _ h
        exact eSeed.symm.injective h
      · intro seed hseed
        refine ⟨eSeed seed, ?_, eSeed.symm_apply_apply seed⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, result,
          Equiv.symm_apply_apply] at hseed ⊢
        exact hseed
    rw [hbij]
    exact hcomp
