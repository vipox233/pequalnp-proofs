import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1397

def Fits (r q : Nat) (s : Fin q → Nat) : Prop :=
  ∃ (ord : Equiv.Perm (Fin q)) (W : Fin q → Nat → Finset (Fin r)),
    (∀ i j, j+1 < s i → W i j ⊂ W i (j+1)) ∧
    ∀ i k, ord i < ord k → ∀ a < s i, ∀ b < s k, ¬ W k b ⊆ W i a

theorem chain_card (r : Nat) (W : Nat → Finset (Fin r)) (m : Nat)
    (hc : ∀ j, j + 1 < m → W j ⊂ W (j+1)) :
    ∀ j, j < m → W 0 ⊆ W j ∧ (W 0).card + j ≤ (W j).card := by
  intro j
  induction j with
  | zero => intro _; exact ⟨subset_refl _, le_refl _⟩
  | succ j ih =>
    intro hj
    obtain ⟨h1, h2⟩ := ih (by omega)
    have h3 := hc j hj
    exact ⟨h1.trans h3.subset, by have := Finset.card_lt_card h3; omega⟩

theorem fwd (r q : Nat) (s : Fin q → Nat) (hs : ∀ i, 0 < s i) (h : Fits r q s) :
    Finset.univ.sum (fun i => 2^(s i-1)) ≤ 2^r := by
  obtain ⟨ord, W, hc, ha⟩ := h
  have key : ∀ i, W i 0 ⊆ W i (s i - 1) ∧ (W i 0).card + (s i - 1) ≤ (W i (s i - 1)).card :=
    fun i => chain_card r (W i) (s i) (hc i) (s i - 1) (by have := hs i; omega)
  let I : Fin q → Finset (Finset (Fin r)) := fun i => Finset.Icc (W i 0) (W i (s i - 1))
  have hI : ∀ i, 2^(s i - 1) ≤ (I i).card := by
    intro i
    show 2^(s i - 1) ≤ (Finset.Icc (W i 0) (W i (s i - 1))).card
    rw [Finset.card_Icc_finset (key i).1]
    exact Nat.pow_le_pow_right (by norm_num) (by have := (key i).2; omega)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin q))) I := by
    intro i _ k _ hik
    show Disjoint (I i) (I k)
    rw [Finset.disjoint_left]
    intro X hXi hXk
    simp only [I, Finset.mem_Icc] at hXi hXk
    have hne : ord i ≠ ord k := fun e => hik (ord.injective e)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ha i k hlt (s i - 1) (by have := hs i; omega) 0 (hs k) (hXk.1.trans hXi.2)
    · exact ha k i hlt (s k - 1) (by have := hs k; omega) 0 (hs i) (hXi.1.trans hXk.2)
  calc Finset.univ.sum (fun i => 2^(s i-1)) ≤ Finset.univ.sum (fun i => (I i).card) :=
        Finset.sum_le_sum (fun i _ => hI i)
    _ = (Finset.univ.biUnion I).card := (Finset.card_biUnion hdisj).symm
    _ ≤ Fintype.card (Finset (Fin r)) := Finset.card_le_univ _
    _ = 2^r := by rw [Fintype.card_finset, Fintype.card_fin]

def bits (r n : Nat) : Finset (Fin r) := Finset.univ.filter (fun j : Fin r => n.testBit j.val = true)

theorem mem_bits (r n : Nat) (j : Fin r) : j ∈ bits r n ↔ n.testBit j.val = true := by
  simp [bits]

theorem bits_le (r x y : Nat) (hx : x < 2^r) (h : bits r x ⊆ bits r y) : x ≤ y := by
  have e : x &&& y = x := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hxi : x.testBit i with
    | false => simp
    | true =>
      have hi : i < r := by
        by_contra hc
        have h2 : x.testBit i = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))
        rw [hxi] at h2
        exact absurd h2 (by decide)
      have h3 : y.testBit i = true := by
        have := h ((mem_bits r x ⟨i, hi⟩).mpr hxi)
        rw [mem_bits] at this
        exact this
      rw [h3]
      rfl
  calc x = x &&& y := e.symm
    _ ≤ y := Nat.and_le_right

theorem bits_chain (r c j : Nat) (hc : 2^(j+1) ∣ c) (hj : j < r) :
    bits r (c + 2^j - 1) ⊂ bits r (c + 2^(j+1) - 1) := by
  obtain ⟨d, rfl⟩ := hc
  have p1 := Nat.two_pow_pos j
  have p2 := Nat.two_pow_pos (j+1)
  have e1 : 2^(j+1) * d + 2^j - 1 = 2^(j+1) * d + (2^j - 1) := by omega
  have e2 : 2^(j+1) * d + 2^(j+1) - 1 = 2^(j+1) * d + (2^(j+1) - 1) := by omega
  have l1 : 2^j - 1 < 2^(j+1) := by rw [pow_succ]; omega
  have l2 : 2^(j+1) - 1 < 2^(j+1) := by omega
  have t1 : ∀ b, (2^(j+1) * d + (2^j - 1)).testBit b =
      if b < j + 1 then decide (b < j) else d.testBit (b - (j+1)) := by
    intro b; rw [Nat.testBit_two_pow_mul_add d l1, Nat.testBit_two_pow_sub_one]
  have t2 : ∀ b, (2^(j+1) * d + (2^(j+1) - 1)).testBit b =
      if b < j + 1 then decide (b < j + 1) else d.testBit (b - (j+1)) := by
    intro b; rw [Nat.testBit_two_pow_mul_add d l2, Nat.testBit_two_pow_sub_one]
  have hsub : bits r (2^(j+1) * d + (2^j - 1)) ⊆ bits r (2^(j+1) * d + (2^(j+1) - 1)) := by
    intro b hb
    rw [mem_bits, t1] at hb
    rw [mem_bits, t2]
    split_ifs at hb ⊢ with h1
    · simp only [decide_eq_true_eq] at hb ⊢
      omega
    · exact hb
  rw [e1, e2]
  refine (Finset.ssubset_iff_of_subset hsub).mpr ⟨⟨j, hj⟩, ?_, ?_⟩
  · rw [mem_bits, t2]
    simp
  · rw [mem_bits, t1]
    simp

theorem bwd (r q : Nat) (s : Fin q → Nat) (hs : ∀ i, 0 < s i)
    (h : Finset.univ.sum (fun i => 2^(s i-1)) ≤ 2^r) : Fits r q s := by
  let σ : Equiv.Perm (Fin q) := Tuple.sort (fun i => OrderDual.toDual (s i))
  have hmono : ∀ p p' : Fin q, p ≤ p' → s (σ p') ≤ s (σ p) := by
    intro p p' hpp
    exact Tuple.monotone_sort (fun i => OrderDual.toDual (s i)) hpp
  let f : Fin q → Nat := fun p => 2^(s (σ p) - 1)
  let c : Fin q → Nat := fun p => (Finset.Iio p).sum f
  have hc_dvd : ∀ p, 2^(s (σ p) - 1) ∣ c p := by
    intro p
    show 2^(s (σ p) - 1) ∣ (Finset.Iio p).sum f
    apply Finset.dvd_sum
    intro p' hp'
    rw [Finset.mem_Iio] at hp'
    exact Nat.pow_dvd_pow 2 (by have := hmono p' p hp'.le; omega)
  have hc_e : ∀ p, c p + f p = (Finset.Iic p).sum f := by
    intro p
    show (Finset.Iio p).sum f + f p = (Finset.Iic p).sum f
    rw [Finset.Iic_eq_cons_Iio, Finset.sum_cons, add_comm]
  have hc_tot : ∀ p, c p + f p ≤ 2^r := by
    intro p
    rw [hc_e]
    calc (Finset.Iic p).sum f ≤ Finset.univ.sum f :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = Finset.univ.sum (fun i => 2^(s i - 1)) := Equiv.sum_comp σ (fun i => 2^(s i - 1))
      _ ≤ 2^r := h
  have hc_mono : ∀ p p', p < p' → c p + f p ≤ c p' := by
    intro p p' hpp
    rw [hc_e]
    show (Finset.Iic p).sum f ≤ (Finset.Iio p').sum f
    apply Finset.sum_le_sum_of_subset
    intro x hx
    rw [Finset.mem_Iic] at hx
    rw [Finset.mem_Iio]
    exact lt_of_le_of_lt hx hpp
  have hf : ∀ i, f (σ.symm i) = 2^(s i - 1) := by
    intro i
    show 2^(s (σ (σ.symm i)) - 1) = 2^(s i - 1)
    rw [Equiv.apply_symm_apply]
  refine ⟨σ.symm, fun i j => bits r (c (σ.symm i) + 2^j - 1), ?_, ?_⟩
  · intro i j hj
    have hd := hc_dvd (σ.symm i)
    rw [Equiv.apply_symm_apply] at hd
    have ht := hc_tot (σ.symm i)
    rw [hf] at ht
    apply bits_chain r (c (σ.symm i)) j
    · exact (Nat.pow_dvd_pow 2 (by omega)).trans hd
    · have h2 : 2^(s i - 1) ≤ 2^r := by omega
      have := (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
      omega
  · intro i k hik a ha b hb hsub
    have h1 := hc_tot (σ.symm k)
    have h2 := hc_mono (σ.symm i) (σ.symm k) hik
    rw [hf] at h1 h2
    have h3 : 2^a ≤ 2^(s i - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 2^b ≤ 2^(s k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 := Nat.two_pow_pos a
    have h6 := Nat.two_pow_pos b
    have := bits_le r _ _ (by omega) hsub
    omega

theorem logfacts (q : Nat) (hq : 0 < q) : 2 ^ Nat.log2 q ≤ q ∧ q < 2 ^ (Nat.log2 q + 1) :=
  ⟨Nat.log2_self_le (by omega), Nat.lt_log2_self⟩

theorem t_le_r (r q : Nat) (hq : 0 < q) (hqr : q ≤ 2^r) : Nat.log2 q ≤ r := by
  have h1 := Nat.log2_self_le (n := q) (by omega)
  have h2 : 2 ^ Nat.log2 q ≤ 2 ^ r := le_trans h1 hqr
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2

theorem succ_le_two_pow (k : Nat) : k + 1 ≤ 2^k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem conv (n s : Nat) : 2^n * (s + 1 - n) ≤ 2^s := by
  rcases Nat.lt_or_ge s n with h | h
  · have : s + 1 - n = 0 := by omega
    rw [this]; simp
  · obtain ⟨k, rfl⟩ : ∃ k, s = n + k := ⟨s - n, by omega⟩
    have : n + k + 1 - n = k + 1 := by omega
    rw [this, pow_add]
    exact Nat.mul_le_mul_left _ (succ_le_two_pow k)

theorem upper (r q : Nat) (hq : 0 < q) (hqr : q ≤ 2^r) (s : Fin q → Nat) (hs : ∀ i, 0 < s i)
    (h : Finset.univ.sum (fun i => 2^(s i-1)) ≤ 2^r) :
    Finset.univ.sum s ≤ q*(r-Nat.log2 q)+(2^(Nat.log2 q+1)-q) := by
  have ht := t_le_r r q hq hqr
  have hl := logfacts q hq
  set t := Nat.log2 q with ht_def
  set n := r - t with hn
  have h1 : ∀ i, 2^n * (s i + 1 - n) ≤ 2 * 2^(s i - 1) := by
    intro i
    have h0 := conv n (s i)
    have h2 : 2 * 2^(s i - 1) = 2^(s i) := by
      rw [← pow_succ']; congr 1; have := hs i; omega
    rw [h2]; exact h0
  have h3 : Finset.univ.sum (fun i => 2^n * (s i + 1 - n)) ≤
      Finset.univ.sum (fun i => 2 * 2^(s i - 1)) :=
    Finset.sum_le_sum (fun i _ => h1 i)
  rw [← Finset.mul_sum, ← Finset.mul_sum] at h3
  have h4 : 2 * 2^r = 2^n * 2^(t+1) := by
    rw [← pow_add, ← pow_succ']; congr 1; omega
  have h5 : Finset.univ.sum (fun i => s i + 1 - n) ≤ 2^(t+1) := by
    have h7 : 2^n * Finset.univ.sum (fun i => s i + 1 - n) ≤ 2^n * 2^(t+1) := by
      calc _ ≤ 2 * Finset.univ.sum (fun i => 2^(s i - 1)) := h3
        _ ≤ 2 * 2^r := by omega
        _ = _ := h4
    exact Nat.le_of_mul_le_mul_left h7 (by positivity)
  have h6 : Finset.univ.sum (fun i => s i + 1) ≤ Finset.univ.sum (fun i => (s i + 1 - n) + n) :=
    Finset.sum_le_sum (fun i _ => by omega)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h6
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h6
  have h7 : q ≤ 2^(t+1) := le_of_lt hl.2
  have h8 : Finset.univ.sum (fun i => s i) = Finset.univ.sum s := rfl
  omega

theorem sum_split (q a : Nat) (h : a ≤ q) (X Y : Nat) :
    Finset.univ.sum (fun i : Fin q => if i.val < a then X else Y) = a * X + (q - a) * Y := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < a then X else Y) q]
  obtain ⟨m, rfl⟩ : ∃ m, q = a + m := ⟨q - a, by omega⟩
  rw [Finset.sum_range_add]
  have e1 : (Finset.range a).sum (fun i => if i < a then X else Y) =
      (Finset.range a).sum (fun _ => X) :=
    Finset.sum_congr rfl (fun i hi => by have := Finset.mem_range.mp hi; split_ifs <;> omega)
  have e2 : (Finset.range m).sum (fun i => if a + i < a then X else Y) =
      (Finset.range m).sum (fun _ => Y) :=
    Finset.sum_congr rfl (fun i _ => by split_ifs <;> omega)
  rw [e1, e2]
  simp

def sA (q n a : Nat) (i : Fin q) : Nat := if i.val < a then n + 1 else n

theorem attain (r q : Nat) (hq : 0 < q) (hqr : q ≤ 2^r) :
    ∃ s : Fin q → Nat, (∀ i, 0 < s i) ∧ Finset.univ.sum (fun i => 2^(s i-1)) ≤ 2^r ∧
      Finset.univ.sum s = q*(r-Nat.log2 q)+(2^(Nat.log2 q+1)-q) := by
  have ht := t_le_r r q hq hqr
  have hl := logfacts q hq
  set t := Nat.log2 q with ht_def
  set n := r - t with hn
  set a := 2^(t+1) - q with ha
  have hpow : 2^(t+1) = 2 * 2^t := by rw [pow_succ]; ring
  have haq : a ≤ q := by omega
  have ha0 : n = 0 → a = q := by
    intro h0
    have hrt : r = t := by omega
    rw [hrt] at hqr
    omega
  refine ⟨sA q n a, ?_, ?_, ?_⟩
  · intro i
    by_cases h0 : n = 0
    · have h1 := ha0 h0
      have h2 : i.val < a := by omega
      simp [sA, h2]
    · unfold sA
      split_ifs <;> omega
  · have e : Finset.univ.sum (fun i : Fin q => 2^(sA q n a i - 1))
        = Finset.univ.sum (fun i : Fin q => if i.val < a then 2^n else 2^(n-1)) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold sA
      split_ifs <;> rfl
    rw [e, sum_split q a haq]
    by_cases h0 : n = 0
    · have h1 := ha0 h0
      rw [h1, h0]
      simp
      omega
    · have e2 : 2^n = 2 * 2^(n-1) := by rw [← pow_succ']; congr 1; omega
      have e3 : 2^r = 2^(t+1) * 2^(n-1) := by rw [← pow_add]; congr 1; omega
      rw [e2, e3]
      have h8 : a + q = 2^(t+1) := by omega
      have h9 : a * (2 * 2^(n-1)) + (q - a) * 2^(n-1) = (a + q) * 2^(n-1) := by
        obtain ⟨m, hm⟩ : ∃ m, q = a + m := ⟨q - a, by omega⟩
        rw [hm, Nat.add_sub_cancel_left]
        ring
      rw [h9, h8]
  · show Finset.univ.sum (fun i : Fin q => if i.val < a then n + 1 else n) = q * n + a
    rw [sum_split q a haq]
    have h1 : (q - a) * n + a * n = q * n := by rw [← Nat.add_mul, Nat.sub_add_cancel haq]
    have h2 : a * (n + 1) = a * n + a := by ring
    omega

end PEqualNP.Outside.L_lib_1397

theorem PEqualNP.Outside.L_lib_1397 : ∀ (r q : Nat), 0 < q → q ≤ 2^r →
  let fits := fun (s : Fin q → Nat) =>
    ∃ (ord : Equiv.Perm (Fin q)) (W : Fin q → Nat → Finset (Fin r)),
      (∀ i j, j+1 < s i → W i j ⊂ W i (j+1)) ∧
      ∀ i k, ord i < ord k → ∀ a < s i, ∀ b < s k, ¬ W k b ⊆ W i a
  let t := Nat.log2 q
  let cap := q*(r-t)+(2^(t+1)-q)
  (∀ s : Fin q → Nat, (∀ i, 0 < s i) →
    (fits s ↔ Finset.univ.sum (fun i => 2^(s i-1)) ≤ 2^r)) ∧
  (∀ s : Fin q → Nat, (∀ i, 0 < s i) → fits s → Finset.univ.sum s ≤ cap) ∧
  ∃ s : Fin q → Nat, (∀ i, 0 < s i) ∧ fits s ∧ Finset.univ.sum s = cap := by
  intro r q hq hqr fits t cap
  refine ⟨fun s hs => ⟨PEqualNP.Outside.L_lib_1397.fwd r q s hs,
      PEqualNP.Outside.L_lib_1397.bwd r q s hs⟩,
    fun s hs hf => PEqualNP.Outside.L_lib_1397.upper r q hq hqr s hs
      (PEqualNP.Outside.L_lib_1397.fwd r q s hs hf), ?_⟩
  obtain ⟨s, hs, hsum, hcap⟩ := PEqualNP.Outside.L_lib_1397.attain r q hq hqr
  exact ⟨s, hs, PEqualNP.Outside.L_lib_1397.bwd r q s hs hsum, hcap⟩
