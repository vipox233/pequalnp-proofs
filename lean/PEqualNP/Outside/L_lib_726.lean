import PEqualNP.Defs
import Mathlib.Data.Nat.Dist

namespace PEqualNP.Outside.L_lib_726_aux

lemma natDist_sq_int (a b : ℕ) : ((Nat.dist a b : ℕ) : ℤ) ^ 2 = ((a : ℤ) - (b : ℤ)) ^ 2 := by
  by_cases h : a ≤ b
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h]
    ring
  · have hle : b ≤ a := by omega
    rw [Nat.dist_eq_sub_of_le_right hle, Nat.cast_sub hle]

def edgeSign {n : ℕ} (π : Equiv.Perm (Fin n)) (e : Fin n → Bool) (z : Fin n → Bool) (i : Fin n) : ℤ :=
  if z i ≠ xor (z (π i)) (e (π i)) then 1 else -1

lemma sum_edgeSign {n : ℕ} (π : Equiv.Perm (Fin n)) (e : Fin n → Bool) (z : Fin n → Bool)
    (m : Finset (Fin n)) :
    ∑ i ∈ m, edgeSign π e z i =
      2 * ((m.filter (fun i => z i ≠ xor (z (π i)) (e (π i)))).card : ℤ) - (m.card : ℤ) := by
  rw [← Finset.sum_filter_add_sum_filter_not m (fun i => z i ≠ xor (z (π i)) (e (π i)))]
  have h1 :
      ∑ i ∈ m.filter (fun i => z i ≠ xor (z (π i)) (e (π i))), edgeSign π e z i =
        ((m.filter (fun i => z i ≠ xor (z (π i)) (e (π i)))).card : ℤ) := by
    trans (∑ _i ∈ m.filter (fun i => z i ≠ xor (z (π i)) (e (π i))), (1 : ℤ))
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      have h := (Finset.mem_filter.mp hi).2
      simp [edgeSign, h]
    · rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have h2 :
      ∑ i ∈ m.filter (fun i => ¬ z i ≠ xor (z (π i)) (e (π i))), edgeSign π e z i =
        -((m.filter (fun i => ¬ z i ≠ xor (z (π i)) (e (π i)))).card : ℤ) := by
    trans (∑ _i ∈ m.filter (fun i => ¬ z i ≠ xor (z (π i)) (e (π i))), (-1 : ℤ))
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      have h := (Finset.mem_filter.mp hi).2
      simp [edgeSign, h]
    · rw [Finset.sum_const, nsmul_eq_mul]
      ring
  have hcard :
      (m.filter (fun i => z i ≠ xor (z (π i)) (e (π i)))).card +
        (m.filter (fun i => ¬ z i ≠ xor (z (π i)) (e (π i)))).card = m.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext i
      simp only [Finset.mem_union, Finset.mem_filter]
      tauto
    · rw [Finset.disjoint_left]
      intro i h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hcard_z :
      ((m.filter (fun i => z i ≠ xor (z (π i)) (e (π i)))).card : ℤ) +
        ((m.filter (fun i => ¬ z i ≠ xor (z (π i)) (e (π i)))).card : ℤ) = (m.card : ℤ) := by
    exact_mod_cast hcard
  rw [h1, h2]
  linarith

lemma edgeSign_flip_self {n : ℕ} (π : Equiv.Perm (Fin n)) (e : Fin n → Bool) (z : Fin n → Bool)
    (v : Fin n) (hmove : π v ≠ v) :
    edgeSign π e (Function.update z v (!(z v))) v = -edgeSign π e z v := by
  simp only [edgeSign, Function.update_self, Function.update_of_ne hmove]
  cases z v <;> cases z (π v) <;> cases e (π v) <;> decide

lemma edgeSign_flip_other {n : ℕ} (π : Equiv.Perm (Fin n)) (e : Fin n → Bool) (z : Fin n → Bool)
    (v k : Fin n) (hk1 : k ≠ v) (hk2 : π k ≠ v) :
    edgeSign π e (Function.update z v (!(z v))) k = edgeSign π e z k := by
  simp only [edgeSign, Function.update_of_ne hk1, Function.update_of_ne hk2]

lemma sum_flip_zero {n : ℕ} (v : Fin n) (f : (Fin n → Bool) → ℤ)
    (hneg : ∀ z, f (Function.update z v (!(z v))) = -f z) :
    ∑ z : Fin n → Bool, f z = 0 := by
  let σ : Equiv.Perm (Fin n → Bool) :=
    { toFun := fun z => Function.update z v (!(z v))
      invFun := fun z => Function.update z v (!(z v))
      left_inv := fun z => by
        funext i
        by_cases h : i = v
        · subst h; simp
        · simp [h]
      right_inv := fun z => by
        funext i
        by_cases h : i = v
        · subst h; simp
        · simp [h] }
  have h1 : ∑ z : Fin n → Bool, f (σ z) = ∑ z : Fin n → Bool, f z :=
    Fintype.sum_equiv σ _ _ (fun _ => rfl)
  have h2 : ∑ z : Fin n → Bool, f (σ z) = -(∑ z : Fin n → Bool, f z) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun z _ => hneg z)
  linarith

lemma sum_edgeSign_pair_zero {n : ℕ} (π : Equiv.Perm (Fin n)) (e : Fin n → Bool)
    (i k : Fin n) (hi : π i ≠ i) (hk : π k ≠ k) (hne1 : k ≠ i) (hne2 : k ≠ π i) :
    ∑ z : Fin n → Bool, edgeSign π e z i * edgeSign π e z k = 0 := by
  by_cases h : π k = i
  · refine sum_flip_zero k _ (fun z => ?_)
    rw [edgeSign_flip_self π e z k hk, edgeSign_flip_other π e z k i hne1.symm hne2.symm]
    ring
  · refine sum_flip_zero i _ (fun z => ?_)
    rw [edgeSign_flip_self π e z i hi, edgeSign_flip_other π e z i k hne1 h]
    ring

lemma edgeSign_mul_le_one {n : ℕ} (π : Equiv.Perm (Fin n)) (e : Fin n → Bool)
    (z : Fin n → Bool) (i k : Fin n) :
    edgeSign π e z i * edgeSign π e z k ≤ 1 := by
  dsimp only [edgeSign]
  split_ifs <;> norm_num

lemma single_perm_second_moment {n : ℕ} (π : Equiv.Perm (Fin n)) (e : Fin n → Bool) :
    let X := Fin n → Bool
    let m := (Finset.univ : Finset (Fin n)).filter (fun i => π i ≠ i)
    let imb := fun z : X =>
      Nat.dist (2 * (m.filter (fun i => z i ≠ xor (z (π i)) (e (π i)))).card) m.card
    ∑ z : X, (imb z) ^ 2 ≤ 2 ^ n * (2 * m.card) := by
  dsimp only
  let X := Fin n → Bool
  let m : Finset (Fin n) := Finset.univ.filter (fun i => π i ≠ i)
  let imb : X → ℕ := fun z =>
    Nat.dist (2 * (m.filter (fun i => z i ≠ xor (z (π i)) (e (π i)))).card) m.card
  suffices hz : (∑ z : X, ((imb z : ℕ) : ℤ) ^ 2) ≤ (2 ^ n : ℤ) * (2 * (m.card : ℤ)) by
    exact_mod_cast hz
  have hexp : ∀ z : X, ((imb z : ℕ) : ℤ) ^ 2 =
      ∑ i ∈ m, ∑ k ∈ m, edgeSign π e z i * edgeSign π e z k := by
    intro z
    have h1 := natDist_sq_int (2 * (m.filter (fun i => z i ≠ xor (z (π i)) (e (π i)))).card) m.card
    have h2 := sum_edgeSign π e z m
    have hcast : ((2 * (m.filter (fun i => z i ≠ xor (z (π i)) (e (π i)))).card : ℕ) : ℤ) =
        2 * ((m.filter (fun i => z i ≠ xor (z (π i)) (e (π i)))).card : ℤ) := by
      push_cast; rfl
    dsimp only [imb]
    rw [h1, hcast, ← h2, sq, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => Finset.mul_sum _ _ _)
  simp_rw [hexp]
  rw [Finset.sum_comm]
  have hinner : ∀ i ∈ m,
      ∑ z : X, ∑ k ∈ m, edgeSign π e z i * edgeSign π e z k ≤ (2 ^ n : ℤ) * 2 := by
    intro i hi
    rw [Finset.sum_comm]
    have hhi : π i ≠ i := (Finset.mem_filter.mp hi).2
    have hsub :
        ∑ k ∈ m, ∑ z : X, edgeSign π e z i * edgeSign π e z k =
          ∑ k ∈ m ∩ {i, π i}, ∑ z : X, edgeSign π e z i * edgeSign π e z k := by
      symm
      refine Finset.sum_subset Finset.inter_subset_left (fun k hk hnot => ?_)
      have hhk : π k ≠ k := (Finset.mem_filter.mp hk).2
      have hnotpair : k ∉ ({i, π i} : Finset (Fin n)) := fun hp =>
        hnot (Finset.mem_inter.mpr ⟨hk, hp⟩)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnotpair
      exact sum_edgeSign_pair_zero π e i k hhi hhk hnotpair.1 hnotpair.2
    rw [hsub]
    have hterm : ∀ k ∈ m ∩ {i, π i},
        ∑ z : X, edgeSign π e z i * edgeSign π e z k ≤ (2 ^ n : ℤ) := by
      intro k _
      calc ∑ z : X, edgeSign π e z i * edgeSign π e z k
          ≤ ∑ _z : X, (1 : ℤ) := Finset.sum_le_sum (fun z _ => edgeSign_mul_le_one π e z i k)
        _ = (Fintype.card X : ℤ) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        _ = (2 ^ n : ℤ) := by
            rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
            push_cast; rfl
    have hcard_le : ((m ∩ {i, π i}).card : ℤ) ≤ 2 := by
      have h1 : (m ∩ {i, π i}).card ≤ ({i, π i} : Finset (Fin n)).card :=
        Finset.card_le_card Finset.inter_subset_right
      have h2 : ({i, π i} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
      exact_mod_cast le_trans h1 h2
    calc ∑ k ∈ m ∩ {i, π i}, ∑ z : X, edgeSign π e z i * edgeSign π e z k
        ≤ ∑ _k ∈ m ∩ {i, π i}, (2 ^ n : ℤ) := Finset.sum_le_sum hterm
      _ = ((m ∩ {i, π i}).card : ℤ) * (2 ^ n : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (2 ^ n : ℤ) := by
          have hpos : (0 : ℤ) ≤ (2 ^ n : ℤ) := by positivity
          nlinarith
      _ = (2 ^ n : ℤ) * 2 := mul_comm _ _
  calc ∑ i ∈ m, ∑ z : X, ∑ k ∈ m, edgeSign π e z i * edgeSign π e z k
      ≤ ∑ _i ∈ m, ((2 ^ n : ℤ) * 2) := Finset.sum_le_sum hinner
    _ = (m.card : ℤ) * ((2 ^ n : ℤ) * 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = (2 ^ n : ℤ) * (2 * (m.card : ℤ)) := by ring

end PEqualNP.Outside.L_lib_726_aux

theorem PEqualNP.Outside.L_lib_726 : (∀ (n r : ℕ) (P : Fin r → Equiv.Perm (Fin n)) (e : Fin n → Bool),
  let X := Fin n → Bool
  let moved := fun j : Fin r => Finset.univ.filter (fun i : Fin n => P j i ≠ i)
  let imbalance := fun (z : X) (j : Fin r) =>
    let m := moved j
    let D := (m.filter (fun i => z i ≠ xor (z (P j i)) (e (P j i)))).card
    Nat.dist (2*D) m.card
  let total := ∑ j : Fin r, (moved j).card
  (∑ z : X, ∑ j : Fin r, (imbalance z j)^2) ≤ 2^n * (2*total) ∧
    ∀ A : ℕ, 0 < A →
      (Finset.univ.filter (fun z : X => ∃ j : Fin r, A ≤ imbalance z j)).card * A^2
        ≤ 2^n * (2*total)) := by
  intro n r P e
  dsimp only
  let X := Fin n → Bool
  let moved : Fin r → Finset (Fin n) := fun j => Finset.univ.filter (fun i : Fin n => P j i ≠ i)
  let imbalance : X → Fin r → ℕ := fun z j =>
    Nat.dist (2 * ((moved j).filter (fun i => z i ≠ xor (z (P j i)) (e (P j i)))).card) (moved j).card
  let total : ℕ := ∑ j : Fin r, (moved j).card
  have hmain : (∑ z : X, ∑ j : Fin r, (imbalance z j) ^ 2) ≤ 2 ^ n * (2 * total) := by
    rw [Finset.sum_comm]
    calc ∑ j : Fin r, ∑ z : X, (imbalance z j) ^ 2
        ≤ ∑ j : Fin r, 2 ^ n * (2 * (moved j).card) :=
          Finset.sum_le_sum (fun j _ => PEqualNP.Outside.L_lib_726_aux.single_perm_second_moment (P j) e)
      _ = 2 ^ n * ∑ j : Fin r, 2 * (moved j).card := (Finset.mul_sum _ _ _).symm
      _ = 2 ^ n * (2 * total) := by rw [← Finset.mul_sum]
  refine ⟨hmain, fun A _ => ?_⟩
  let bad : Finset X := Finset.univ.filter (fun z : X => ∃ j : Fin r, A ≤ imbalance z j)
  have hbad : bad.card * A ^ 2 ≤ ∑ z : X, ∑ j : Fin r, (imbalance z j) ^ 2 := by
    calc bad.card * A ^ 2
        = ∑ _z ∈ bad, A ^ 2 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ z ∈ bad, ∑ j : Fin r, (imbalance z j) ^ 2 := by
          refine Finset.sum_le_sum (fun z hz => ?_)
          obtain ⟨j0, hj0⟩ := (Finset.mem_filter.mp hz).2
          calc A ^ 2 ≤ (imbalance z j0) ^ 2 := Nat.pow_le_pow_left hj0 2
            _ ≤ ∑ j : Fin r, (imbalance z j) ^ 2 :=
                Finset.single_le_sum (f := fun j => (imbalance z j) ^ 2)
                  (fun _ _ => Nat.zero_le _) (Finset.mem_univ j0)
      _ ≤ ∑ z : X, ∑ j : Fin r, (imbalance z j) ^ 2 :=
          Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  exact le_trans hbad hmain
