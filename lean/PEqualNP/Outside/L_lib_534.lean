import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_534

def cnt {n m : ℕ} (w : Fin n → Fin m) (i : Fin m) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun pos => w pos = i)).card

def S (n m : ℕ) (k : Fin m → ℕ) : Finset (Fin n → Fin m) :=
  (Finset.univ : Finset (Fin n → Fin m)).filter (fun w => ∀ i, cnt w i = k i)

lemma cnt_cons {n m : ℕ} (j : Fin m) (u : Fin n → Fin m) (i : Fin m) :
    cnt (Fin.cons j u : Fin (n + 1) → Fin m) i = cnt u i + if j = i then 1 else 0 := by
  unfold cnt
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

lemma sum_cnt {n m : ℕ} (w : Fin n → Fin m) : ∑ i, cnt w i = n := by
  unfold cnt
  rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (w x))]
  simp

lemma cnt_le {n m : ℕ} (w : Fin n → Fin m) (i : Fin m) : cnt w i ≤ n := by
  unfold cnt
  calc _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

lemma card_S_succ {n m : ℕ} (k : Fin m → ℕ) :
    (S (n + 1) m k).card =
      ∑ j, if 1 ≤ k j then (S n m (Function.update k j (k j - 1))).card else 0 := by
  unfold S
  rw [Finset.card_filter]
  have hsplit : (∑ w : Fin (n + 1) → Fin m, if (∀ i, cnt w i = k i) then 1 else 0) =
      ∑ p : Fin m × (Fin n → Fin m),
        if (∀ i, cnt (Fin.cons p.1 p.2 : Fin (n + 1) → Fin m) i = k i) then 1 else 0 :=
    (Fintype.sum_equiv (Fin.consEquiv (fun _ => Fin m)) _ _ (fun p => rfl)).symm
  rw [hsplit, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [cnt_cons]
  split_ifs with hj
  · rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    refine if_congr ⟨fun h i => ?_, fun h i => ?_⟩ rfl rfl
    · have hi := h i
      by_cases hij : i = j
      · subst hij
        simp only [Function.update_self]
        simp only [ite_true] at hi
        omega
      · rw [Function.update_of_ne hij]
        simp only [Ne.symm hij, ite_false, add_zero] at hi
        exact hi
    · have hi := h i
      by_cases hij : i = j
      · subst hij
        simp only [Function.update_self] at hi
        simp only [ite_true]
        omega
      · rw [Function.update_of_ne hij] at hi
        simp only [Ne.symm hij, ite_false, add_zero]
        exact hi
  · refine Finset.sum_eq_zero (fun u _ => ?_)
    rw [if_neg]
    intro h
    have hj' := h j
    simp only [ite_true] at hj'
    omega

lemma card_S_mul : ∀ (n : ℕ) {m : ℕ} (k : Fin m → ℕ), ∑ i, k i = n →
    (S n m k).card * ∏ i, (k i).factorial = n.factorial := by
  intro n
  induction n with
  | zero =>
    intro m k hk
    have hk0 : ∀ i, k i = 0 := fun i => (Finset.sum_eq_zero_iff.1 hk) i (Finset.mem_univ i)
    have hS : S 0 m k = Finset.univ := by
      unfold S
      apply Finset.filter_true_of_mem
      intro w _ i
      rw [hk0 i]
      unfold cnt
      simp
    rw [hS]
    simp [hk0]
  | succ n ih =>
    intro m k hk
    rw [card_S_succ, Finset.sum_mul]
    have hterm : ∀ j, (if 1 ≤ k j then (S n m (Function.update k j (k j - 1))).card else 0) *
        ∏ i, (k i).factorial = k j * n.factorial := by
      intro j
      split_ifs with hj
      · have hsum' : ∑ i, Function.update k j (k j - 1) i = n := by
          rw [Finset.sum_update_of_mem (Finset.mem_univ j), Finset.sdiff_singleton_eq_erase]
          have := Finset.add_sum_erase Finset.univ k (Finset.mem_univ j)
          omega
        have e : ∀ i ∈ Finset.univ.erase j,
            (Function.update k j (k j - 1) i).factorial = (k i).factorial := by
          intro i hi
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
        have hfac : (k j).factorial = k j * (k j - 1).factorial := by
          have h1 : k j = (k j - 1) + 1 := by omega
          conv_lhs => rw [h1]
          rw [Nat.factorial_succ, ← h1]
        have hprod : ∏ i, (k i).factorial =
            k j * ∏ i, (Function.update k j (k j - 1) i).factorial := by
          rw [← Finset.mul_prod_erase Finset.univ (fun i => (k i).factorial) (Finset.mem_univ j),
            ← Finset.mul_prod_erase Finset.univ
              (fun i => (Function.update k j (k j - 1) i).factorial) (Finset.mem_univ j),
            Finset.prod_congr rfl e]
          simp only [Function.update_self]
          rw [hfac]
          ring
        rw [hprod, ← mul_assoc, mul_comm _ (k j), mul_assoc, ih _ hsum']
      · rw [zero_mul, show k j = 0 by omega, zero_mul]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.sum_mul, hk, Nat.factorial_succ]

lemma coord (a k : ℕ) : a ^ k * a.factorial ≤ a ^ a * k.factorial := by
  rcases le_total k a with h | h
  · have e : k.factorial * a.descFactorial (a - k) = a.factorial := by
      have := Nat.factorial_mul_descFactorial (Nat.sub_le a k)
      rwa [Nat.sub_sub_self h] at this
    have hd := Nat.descFactorial_le_pow a (a - k)
    have hp : a ^ a = a ^ k * a ^ (a - k) := by
      rw [← pow_add]
      congr 1
      omega
    rw [← e, hp]
    calc a ^ k * (k.factorial * a.descFactorial (a - k))
        = (a ^ k * k.factorial) * a.descFactorial (a - k) := by ring
      _ ≤ (a ^ k * k.factorial) * a ^ (a - k) := Nat.mul_le_mul_left _ hd
      _ = a ^ k * a ^ (a - k) * k.factorial := by ring
  · have e : a.factorial * k.descFactorial (k - a) = k.factorial := by
      have := Nat.factorial_mul_descFactorial (Nat.sub_le k a)
      rwa [Nat.sub_sub_self h] at this
    have hd : a ^ (k - a) ≤ k.descFactorial (k - a) := by
      have h1 := Nat.pow_sub_le_descFactorial k (k - a)
      have h2 : k + 1 - (k - a) = a + 1 := by omega
      rw [h2] at h1
      exact le_trans (Nat.pow_le_pow_left (Nat.le_succ a) _) h1
    have hp : a ^ k = a ^ a * a ^ (k - a) := by
      rw [← pow_add]
      congr 1
      omega
    rw [← e, hp]
    calc a ^ a * a ^ (k - a) * a.factorial
        = (a ^ a * a.factorial) * a ^ (k - a) := by ring
      _ ≤ (a ^ a * a.factorial) * k.descFactorial (k - a) := Nat.mul_le_mul_left _ hd
      _ = a ^ a * (a.factorial * k.descFactorial (k - a)) := by ring

lemma key {n m : ℕ} (a k : Fin m → ℕ) (ha : ∑ i, a i = n) :
    (S n m k).card * ∏ i, a i ^ k i ≤ (S n m a).card * ∏ i, a i ^ a i := by
  by_cases hk : ∑ i, k i = n
  · have e1 := card_S_mul n k hk
    have e2 := card_S_mul n a ha
    have hP : 0 < (∏ i, (k i).factorial) * ∏ i, (a i).factorial :=
      Nat.mul_pos (Finset.prod_pos (fun i _ => Nat.factorial_pos _))
        (Finset.prod_pos (fun i _ => Nat.factorial_pos _))
    have hc : ∏ i, (a i ^ k i * (a i).factorial) ≤ ∏ i, (a i ^ a i * (k i).factorial) :=
      Finset.prod_le_prod (fun i _ => coord (a i) (k i))
    refine Nat.le_of_mul_le_mul_right ?_ hP
    calc (S n m k).card * (∏ i, a i ^ k i) * ((∏ i, (k i).factorial) * ∏ i, (a i).factorial)
        = ((S n m k).card * ∏ i, (k i).factorial) * ∏ i, (a i ^ k i * (a i).factorial) := by
          rw [Finset.prod_mul_distrib]
          ring
      _ = n.factorial * ∏ i, (a i ^ k i * (a i).factorial) := by rw [e1]
      _ ≤ n.factorial * ∏ i, (a i ^ a i * (k i).factorial) := Nat.mul_le_mul_left _ hc
      _ = ((S n m a).card * ∏ i, (a i).factorial) * ∏ i, (a i ^ a i * (k i).factorial) := by
          rw [e2]
      _ = (S n m a).card * (∏ i, a i ^ a i) * ((∏ i, (k i).factorial) * ∏ i, (a i).factorial) := by
          rw [Finset.prod_mul_distrib]
          ring
  · have hS : S n m k = ∅ := by
      unfold S
      apply Finset.filter_false_of_mem
      intro w _ h
      apply hk
      rw [← sum_cnt w]
      exact Finset.sum_congr rfl (fun i _ => (h i).symm)
    rw [hS]
    simp

lemma prod_comp_eq {n m : ℕ} (a : Fin m → ℕ) (w : Fin n → Fin m) :
    ∏ p, a (w p) = ∏ i, a i ^ cnt w i := by
  rw [← Finset.prod_fiberwise Finset.univ w (fun p => a (w p))]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have e : ∀ p ∈ (Finset.univ : Finset (Fin n)).filter (fun p => w p = i), a (w p) = a i :=
    fun p hp => by rw [(Finset.mem_filter.1 hp).2]
  rw [Finset.prod_congr rfl e, Finset.prod_const]
  rfl

lemma sum_words {n m : ℕ} (a : Fin m → ℕ) (ha : ∑ i, a i = n) :
    ∑ w : Fin n → Fin m, ∏ p, a (w p) = n ^ n := by
  rw [← Fintype.prod_sum (fun (_ : Fin n) (i : Fin m) => a i)]
  simp [ha]

theorem main (m n : ℕ) (a : Fin m → ℕ) (hsum : ∑ i, a i = n) :
    (S n m a).card * ∏ i, a i ^ a i ≤ n ^ n ∧
      n ^ n ≤ (n + 1) ^ m * (S n m a).card * ∏ i, a i ^ a i := by
  have hw : ∀ w : Fin n → Fin m, ∏ p, a (w p) = ∏ i, a i ^ cnt w i := prod_comp_eq a
  constructor
  · rw [← sum_words a hsum, Finset.card_eq_sum_ones, Finset.sum_mul]
    calc ∑ w ∈ S n m a, 1 * ∏ i, a i ^ a i = ∑ w ∈ S n m a, ∏ p, a (w p) := by
          refine Finset.sum_congr rfl (fun w hw' => ?_)
          rw [one_mul, hw]
          have h := (Finset.mem_filter.1 hw').2
          exact Finset.prod_congr rfl (fun i _ => by rw [h i])
      _ ≤ ∑ w : Fin n → Fin m, ∏ p, a (w p) := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  · let K : Finset (Fin m → ℕ) := Fintype.piFinset (fun _ => Finset.range (n + 1))
    have hmaps : ∀ w ∈ (Finset.univ : Finset (Fin n → Fin m)), (fun i => cnt w i) ∈ K := by
      intro w _
      simp only [K, Fintype.mem_piFinset, Finset.mem_range]
      intro i
      exact Nat.lt_succ_of_le (cnt_le w i)
    have hK : K.card = (n + 1) ^ m := by simp [K, Fintype.card_piFinset]
    rw [← sum_words a hsum]
    simp_rw [hw]
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun w => ∏ i, a i ^ cnt w i)]
    calc ∑ k ∈ K, ∑ w ∈ Finset.univ with (fun i => cnt w i) = k, ∏ i, a i ^ cnt w i
        = ∑ k ∈ K, (S n m k).card * ∏ i, a i ^ k i := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.card_eq_sum_ones, Finset.sum_mul]
          refine Finset.sum_congr ?_ (fun w hw' => ?_)
          · unfold S
            ext w
            simp [funext_iff]
          · have h := (Finset.mem_filter.1 hw').2
            rw [one_mul]
            exact Finset.prod_congr rfl (fun i _ => by rw [h i])
      _ ≤ ∑ k ∈ K, (S n m a).card * ∏ i, a i ^ a i :=
          Finset.sum_le_sum (fun k _ => key a k hsum)
      _ = (n + 1) ^ m * (S n m a).card * ∏ i, a i ^ a i := by
          rw [Finset.sum_const, hK, smul_eq_mul]
          ring

end PEqualNP.Outside.L_lib_534

theorem PEqualNP.Outside.L_lib_534 : (∀ (m n : ℕ) (a : Fin m → ℕ), 0 < n → (∑ i, a i) = n →
  let T := ((Finset.univ : Finset (Fin n → Fin m)).filter (fun w =>
    ∀ i, ((Finset.univ : Finset (Fin n)).filter (fun pos => w pos = i)).card = a i)).card
  let W := ∏ i, (a i)^(a i)
  T*W ≤ n^n ∧ n^n ≤ (n+1)^m*T*W) := by
  intro m n a _ hsum
  exact PEqualNP.Outside.L_lib_534.main m n a hsum
