import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29727_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

abbrev F2 := ZMod 2

def chi (a : F2) : ℤ := if a = 1 then -1 else 1

lemma zmod2_eq_zero_or_one (a : F2) : a = 0 ∨ a = 1 := by
  decide +revert

lemma zmod2_add_self (a : F2) : a + a = 0 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> decide

lemma zmod2_sub_eq_add (a b : F2) : a - b = a + b := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> decide

lemma chi_zero : chi 0 = 1 := by decide

lemma chi_one : chi 1 = -1 := by decide

lemma chi_add (a b : F2) : chi (a + b) = chi a * chi b := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;> decide

lemma chi_mul_self (a : F2) : chi a * chi a = 1 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> decide

lemma abs_chi (a : F2) : |chi a| = 1 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> decide

def boolToF2 (b : Bool) : F2 := if b then 1 else 0

lemma decide_boolToF2 (b : Bool) : decide (boolToF2 b = 1) = b := by
  cases b <;> decide

lemma boolToF2_decide (a : F2) : boolToF2 (decide (a = 1)) = a := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> decide

lemma boolToF2_not (b : Bool) : boolToF2 (!b) = 1 + boolToF2 b := by
  cases b <;> decide

lemma boolToF2_xor (a b : Bool) : boolToF2 (a ^^ b) = boolToF2 a + boolToF2 b := by
  cases a <;> cases b <;> decide

lemma boolToF2_and (a b : Bool) : boolToF2 (a && b) = boolToF2 a * boolToF2 b := by
  cases a <;> cases b <;> decide

lemma dotProduct_add_left {n : ℕ} (x y z : Fin n → F2) :
    dotProduct (x + y) z = dotProduct x z + dotProduct y z := by
  simp only [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dotProduct_add_right {n : ℕ} (x y z : Fin n → F2) :
    dotProduct x (y + z) = dotProduct x y + dotProduct x z := by
  simp only [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dotProduct_zero_left {n : ℕ} (z : Fin n → F2) : dotProduct 0 z = 0 := by
  simp [dotProduct]

lemma dotProduct_zero_right {n : ℕ} (x : Fin n → F2) : dotProduct x 0 = 0 := by
  simp [dotProduct]

lemma sum_chi_dotProduct {d : ℕ} (u : Fin d → F2) :
    (∑ y : Fin d → F2, chi (dotProduct y u)) = if u = 0 then (2 ^ d : ℤ) else 0 := by
  split_ifs with hu
  · subst hu
    simp only [dotProduct_zero_right, chi_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, ZMod.card, nsmul_eq_mul, mul_one, Nat.cast_pow,
      Nat.cast_ofNat]
  · have hne : ∃ i : Fin d, u i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hu (funext h)
    rcases hne with ⟨i₀, hi₀⟩
    have hui : u i₀ = 1 := by
      rcases zmod2_eq_zero_or_one (u i₀) with h0 | h1
      · exact (hi₀ h0).elim
      · exact h1
    let e : Fin d → F2 := fun i => if i = i₀ then 1 else 0
    have heu : dotProduct e u = 1 := by
      simp only [dotProduct, e, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, hui]
    have hshift : (∑ y : Fin d → F2, chi (dotProduct (y + e) u)) =
        ∑ y : Fin d → F2, chi (dotProduct y u) :=
      Fintype.sum_equiv (Equiv.addRight e) _ _ (fun _ => rfl)
    have hneg : (∑ y : Fin d → F2, chi (dotProduct (y + e) u)) =
        -(∑ y : Fin d → F2, chi (dotProduct y u)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [dotProduct_add_left, heu, chi_add, chi_one]
      ring
    linarith

lemma exists_pow2_window (k : ℕ) (hk : 128 ≤ k) :
    ∃ t : ℕ, 512 * k ≤ 2 ^ t ∧ 2 ^ t < 1024 * k := by
  have hex : ∃ t : ℕ, 512 * k ≤ 2 ^ t := ⟨512 * k, le_of_lt Nat.lt_two_pow_self⟩
  classical
  let t := Nat.find hex
  have ht : 512 * k ≤ 2 ^ t := Nat.find_spec hex
  have ht0 : 0 < t := by
    by_contra h0
    have hteq : t = 0 := by omega
    rw [hteq] at ht
    omega
  have hprev : 2 ^ (t - 1) < 512 * k := Nat.lt_of_not_ge (Nat.find_min hex (by omega))
  have hpow : 2 ^ t = 2 * 2 ^ (t - 1) := by
    have : t = (t - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ]
    ring
  exact ⟨t, ht, by omega⟩

def bitsToNat : ∀ {N : ℕ}, (Fin N → F2) → ℕ
  | 0, _ => 0
  | _ + 1, b => (if b 0 = 1 then 1 else 0) + 2 * bitsToNat (fun i => b i.succ)

lemma bitsToNat_lt {N : ℕ} (b : Fin N → F2) : bitsToNat b < 2 ^ N := by
  induction N with
  | zero => simp [bitsToNat]
  | succ n ih =>
    simp only [bitsToNat, pow_succ]
    have h := ih (fun i => b i.succ)
    split_ifs <;> omega

lemma bitsToNat_testBit {N : ℕ} (b : Fin N → F2) (r : ℕ) (hr : r < N) :
    (bitsToNat b).testBit r = decide (b ⟨r, hr⟩ = 1) := by
  induction N generalizing r with
  | zero => omega
  | succ n ih =>
    simp only [bitsToNat]
    cases r with
    | zero =>
      rw [Nat.testBit_zero]
      split_ifs with h
      · have hmod : (1 + 2 * bitsToNat (fun i => b i.succ)) % 2 = 1 := by omega
        simp [hmod, h]
      · have hmod : (0 + 2 * bitsToNat (fun i => b i.succ)) % 2 = 0 := by omega
        simp [hmod, h]
    | succ r' =>
      rw [Nat.testBit_succ]
      have hdiv : ((if b 0 = 1 then 1 else 0) + 2 * bitsToNat (fun i => b i.succ)) / 2 =
          bitsToNat (fun i => b i.succ) := by
        split_ifs <;> omega
      rw [hdiv]
      exact ih (fun i => b i.succ) r' (by omega)

lemma bitsToNat_fin_testBit {N : ℕ} (b : Fin N → F2) (r : ℕ) (hr : r < N) :
    (if (⟨bitsToNat b, bitsToNat_lt b⟩ : Fin (2 ^ N)).val.testBit r then (1 : F2) else 0) =
      b ⟨r, hr⟩ := by
  change (if (bitsToNat b).testBit r then (1 : F2) else 0) = b ⟨r, hr⟩
  rw [bitsToNat_testBit b r hr]
  exact boolToF2_decide (b ⟨r, hr⟩)

lemma linear_surj_fiber_card {A B : ℕ} (f : (Fin A → F2) → (Fin B → F2))
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsurj : Function.Surjective f) (y : Fin B → F2) :
    (Finset.univ.filter (fun x => f x = y)).card =
      (Finset.univ.filter (fun x => f x = 0)).card := by
  rcases hsurj y with ⟨x₀, hx₀⟩
  refine Finset.card_bij (fun x _ => x + x₀) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hadd, hx, hx₀]
    ext i
    exact zmod2_add_self (y i)
  · intro x₁ _ x₂ _ h
    have h' : x₁ + x₀ + x₀ = x₂ + x₀ + x₀ := congrArg (· + x₀) h
    ext i
    have hi := congrFun h' i
    simp only [Pi.add_apply, add_assoc, zmod2_add_self, add_zero] at hi
    exact hi
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    refine ⟨z + x₀, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hadd, hz, hx₀, zero_add]
    · ext i
      simp only [Pi.add_apply, add_assoc, zmod2_add_self, add_zero]

lemma add_surj_preimage_card {A B : ℕ} (f : (Fin A → F2) → (Fin B → F2))
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsurj : Function.Surjective f) (P : (Fin B → F2) → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun x => P (f x))).card * 2 ^ B =
      (Finset.univ.filter P).card * 2 ^ A := by
  let K := (Finset.univ.filter (fun x => f x = 0)).card
  have hfib : ∀ y : Fin B → F2, (Finset.univ.filter (fun x => f x = y)).card = K :=
    linear_surj_fiber_card f hadd hsurj
  have hpart : ∀ S : Finset (Fin B → F2),
      (Finset.univ.filter (fun x => f x ∈ S)).card = S.card * K := by
    intro S
    have hbi := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter (fun x => f x ∈ S)) (t := S) (f := f)
      (fun x hx => (Finset.mem_filter.mp hx).2)
    rw [hbi]
    have hcongr : ∀ y ∈ S,
        ((Finset.univ.filter (fun x => f x ∈ S)).filter (fun x => f x = y)).card = K := by
      intro y hy
      have heq : (Finset.univ.filter (fun x => f x ∈ S)).filter (fun x => f x = y) =
          Finset.univ.filter (fun x => f x = y) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hy, h⟩⟩
      rw [heq, hfib y]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul]
  have htot := hpart Finset.univ
  have huniv : Finset.univ.filter (fun x : Fin A → F2 => f x ∈ (Finset.univ : Finset (Fin B → F2))) =
      Finset.univ := by ext x; simp
  rw [huniv] at htot
  have hcardA : (Finset.univ : Finset (Fin A → F2)).card = 2 ^ A := by
    simp [Fintype.card_fun, ZMod.card]
  have hcardB : (Finset.univ : Finset (Fin B → F2)).card = 2 ^ B := by
    simp [Fintype.card_fun, ZMod.card]
  rw [hcardA, hcardB] at htot
  have hP := hpart (Finset.univ.filter P)
  have hPeq : Finset.univ.filter (fun x => f x ∈ Finset.univ.filter P) =
      Finset.univ.filter (fun x => P (f x)) := by ext x; simp
  rw [hPeq] at hP
  calc
    (Finset.univ.filter (fun x => P (f x))).card * 2 ^ B
        = (Finset.univ.filter P).card * K * 2 ^ B := by rw [hP]
    _ = (Finset.univ.filter P).card * (2 ^ B * K) := by ring
    _ = (Finset.univ.filter P).card * 2 ^ A := by rw [← htot]

def tapeVec (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (b : Fin (k + m - 1) → F2)
    (j : Fin m) (i : Fin k) : F2 :=
  b ⟨j.val + i.val, by omega⟩

lemma sum_pow_split (m a c : ℕ) :
    (∑ z : Fin m → F2,
      a ^ (Finset.univ.filter (fun j : Fin m => z j = 0)).card *
      c ^ (Finset.univ.filter (fun j : Fin m => z j = 1)).card) = (a + c) ^ m := by
  induction m with
  | zero =>
    simp
  | succ n ih =>
    let e : (Fin (n + 1) → F2) ≃ F2 × (Fin n → F2) :=
      { toFun := fun z => (z 0, fun i => z i.succ)
        invFun := fun p => Fin.cons p.1 p.2
        left_inv := fun z => by
          ext i
          refine Fin.cases ?_ ?_ i <;> simp
        right_inv := fun p => by
          ext <;> simp }
    rw [Fintype.sum_equiv e _ (fun p =>
      a ^ ((if p.1 = 0 then 1 else 0) + (Finset.univ.filter (fun j : Fin n => p.2 j = 0)).card) *
      c ^ ((if p.1 = 1 then 1 else 0) + (Finset.univ.filter (fun j : Fin n => p.2 j = 1)).card))]
    · rw [Fintype.sum_prod_type]
      have hsum2 : ∀ g : F2 → ℕ, (∑ x : F2, g x) = g 0 + g 1 := by
        intro g
        exact Fin.sum_univ_two g
      rw [hsum2]
      have h0 : (∑ y : Fin n → F2,
          a ^ ((if (0 : F2) = 0 then 1 else 0) + (Finset.univ.filter (fun j => y j = 0)).card) *
          c ^ ((if (0 : F2) = 1 then 1 else 0) + (Finset.univ.filter (fun j => y j = 1)).card)) =
          a * (a + c) ^ n := by
        rw [← ih, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        have h01 : (0 : F2) ≠ 1 := by decide
        simp only [ite_true, h01, ite_false, zero_add]
        rw [pow_add, pow_one]
        ring
      have h1 : (∑ y : Fin n → F2,
          a ^ ((if (1 : F2) = 0 then 1 else 0) + (Finset.univ.filter (fun j => y j = 0)).card) *
          c ^ ((if (1 : F2) = 1 then 1 else 0) + (Finset.univ.filter (fun j => y j = 1)).card)) =
          c * (a + c) ^ n := by
        rw [← ih, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        have h10 : (1 : F2) ≠ 0 := by decide
        simp only [ite_true, h10, ite_false, zero_add]
        rw [pow_add, pow_one]
        ring
      rw [h0, h1, pow_succ]
      ring
    · intro z
      have hcard : ∀ v : F2,
          (Finset.univ.filter (fun j : Fin (n + 1) => z j = v)).card =
            (if z 0 = v then 1 else 0) +
              (Finset.univ.filter (fun j : Fin n => z j.succ = v)).card := by
        intro v
        rw [Fin.card_filter_univ_succ]
        split_ifs <;> omega
      rw [hcard 0, hcard 1]
      rfl

lemma bias_pos_card_bound (m : ℕ) :
    let q := m / 28
    (Finset.univ.filter (fun z : Fin m → F2 =>
      m < 14 * (∑ j : Fin m, chi (z j)))).card *
      15 ^ (15 * q) * 13 ^ (m - 15 * q) ≤ 28 ^ m := by
  intro q
  let S := Finset.univ.filter (fun z : Fin m → F2 => m < 14 * (∑ j : Fin m, chi (z j)))
  have hle : ∀ z ∈ S,
      15 ^ (15 * q) * 13 ^ (m - 15 * q) ≤
        15 ^ (Finset.univ.filter (fun j : Fin m => z j = 0)).card *
        13 ^ (Finset.univ.filter (fun j : Fin m => z j = 1)).card := by
    intro z hz
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    let c0 := (Finset.univ.filter (fun j : Fin m => z j = 0)).card
    let c1 := (Finset.univ.filter (fun j : Fin m => z j = 1)).card
    have hsum_c : c0 + c1 = m := by
      have hunion : Finset.univ.filter (fun j : Fin m => z j = 0) ∪
          Finset.univ.filter (fun j : Fin m => z j = 1) = Finset.univ := by
        ext j
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact zmod2_eq_zero_or_one (z j)
      have hdisj : Disjoint (Finset.univ.filter (fun j : Fin m => z j = 0))
          (Finset.univ.filter (fun j : Fin m => z j = 1)) := by
        rw [Finset.disjoint_filter]
        intro j _ h0 h1
        rw [h0] at h1
        exact absurd h1 (by decide)
      have h := Finset.card_union_of_disjoint hdisj
      rw [hunion, Finset.card_univ, Fintype.card_fin] at h
      exact h.symm
    have hchi_sum : (∑ j : Fin m, chi (z j)) = (c0 : ℤ) - (c1 : ℤ) := by
      have h1 : ∀ j : Fin m, chi (z j) = (if z j = 0 then (1 : ℤ) else 0) -
          (if z j = 1 then (1 : ℤ) else 0) := by
        intro j
        rcases zmod2_eq_zero_or_one (z j) with h0 | h1
        · simp [h0, chi_zero]
        · simp [h1, chi_one]
      simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_boole]
      rfl
    have hc0 : 15 * q ≤ c0 := by
      rw [hchi_sum] at hz
      have hq : 28 * q ≤ m := Nat.mul_div_le m 28
      omega
    have hdiff : c0 - 15 * q + c1 = m - 15 * q := by omega
    calc
      15 ^ (15 * q) * 13 ^ (m - 15 * q)
          = 15 ^ (15 * q) * 13 ^ (c0 - 15 * q + c1) := by rw [hdiff]
      _ = 15 ^ (15 * q) * 13 ^ (c0 - 15 * q) * 13 ^ c1 := by rw [pow_add]; ring
      _ ≤ 15 ^ (15 * q) * 15 ^ (c0 - 15 * q) * 13 ^ c1 := by
            gcongr; norm_num
      _ = 15 ^ (15 * q + (c0 - 15 * q)) * 13 ^ c1 := by rw [pow_add]
      _ = 15 ^ c0 * 13 ^ c1 := by rw [Nat.add_sub_cancel' hc0]
  calc
    S.card * 15 ^ (15 * q) * 13 ^ (m - 15 * q)
        = S.card * (15 ^ (15 * q) * 13 ^ (m - 15 * q)) := by ring
    _ = ∑ _z ∈ S, (15 ^ (15 * q) * 13 ^ (m - 15 * q)) := by
          rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ z ∈ S,
          15 ^ (Finset.univ.filter (fun j : Fin m => z j = 0)).card *
          13 ^ (Finset.univ.filter (fun j : Fin m => z j = 1)).card :=
          Finset.sum_le_sum hle
    _ ≤ ∑ z : Fin m → F2,
          15 ^ (Finset.univ.filter (fun j : Fin m => z j = 0)).card *
          13 ^ (Finset.univ.filter (fun j : Fin m => z j = 1)).card :=
          Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ = (15 + 13) ^ m := sum_pow_split m 15 13
    _ = 28 ^ m := by norm_num

lemma bias_abs_card_bound (m : ℕ) :
    (Finset.univ.filter (fun z : Fin m → F2 =>
      (m : ℤ) < 14 * |∑ j : Fin m, chi (z j)|)).card ≤
      2 * (Finset.univ.filter (fun z : Fin m → F2 =>
        (m : ℤ) < 14 * (∑ j : Fin m, chi (z j)))).card := by
  let Spos := Finset.univ.filter (fun z : Fin m → F2 => (m : ℤ) < 14 * (∑ j : Fin m, chi (z j)))
  let Sneg := Finset.univ.filter (fun z : Fin m → F2 => (m : ℤ) < 14 * -(∑ j : Fin m, chi (z j)))
  have hsub : Finset.univ.filter (fun z : Fin m → F2 => (m : ℤ) < 14 * |∑ j : Fin m, chi (z j)|) ⊆
      Spos ∪ Sneg := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Spos, Sneg] at hz ⊢
    rcases le_or_gt 0 (∑ j : Fin m, chi (z j)) with hge | hlt
    · left; rwa [abs_of_nonneg hge] at hz
    · right; rwa [abs_of_neg hlt] at hz
  have hneg_eq : Sneg.card = Spos.card := by
    refine Finset.card_bij (fun z _ => fun j => z j + 1) ?_ ?_ ?_
    · intro z hz
      simp only [Sneg, Spos, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      have hflip : (∑ j : Fin m, chi (z j + 1)) = -(∑ j : Fin m, chi (z j)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [chi_add, chi_one]; ring
      rwa [hflip]
    · intro z₁ _ z₂ _ h
      ext j
      have hj := congrFun h j
      have hj' : z₁ j + 1 + 1 = z₂ j + 1 + 1 := congrArg (· + 1) hj
      simp only [add_assoc, zmod2_add_self, add_zero] at hj'
      exact hj'
    · intro z hz
      refine ⟨fun j => z j + 1, ?_, ?_⟩
      · simp only [Sneg, Spos, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        have hflip : (∑ j : Fin m, chi (z j + 1)) = -(∑ j : Fin m, chi (z j)) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [chi_add, chi_one]; ring
        rw [hflip, neg_neg]
        exact hz
      · ext j
        simp only [add_assoc, zmod2_add_self, add_zero]
  calc
    (Finset.univ.filter (fun z : Fin m → F2 => (m : ℤ) < 14 * |∑ j : Fin m, chi (z j)|)).card
        ≤ (Spos ∪ Sneg).card := Finset.card_le_card hsub
    _ ≤ Spos.card + Sneg.card := Finset.card_union_le _ _
    _ = 2 * Spos.card := by rw [hneg_eq]; ring

lemma bias_arith_helper (k m : ℕ) (hk : 128 ≤ k) (hm : 512 * k ≤ m) :
    let q := m / 28
    4 * 2 ^ k * 28 ^ m < 2 ^ m * 15 ^ (15 * q) * 13 ^ (m - 15 * q) := by
  intro q
  let r := m % 28
  have hmr : m = 28 * q + r := (Nat.div_add_mod m 28).symm
  have hrlt : r < 28 := Nat.mod_lt m (by norm_num)
  have hsub : m - 15 * q = 13 * q + r := by omega
  have hq : 18 * k ≤ q := by omega
  have h1 : 16 * 14 ^ 28 ≤ 15 * (15 ^ 15 * 13 ^ 13) := by norm_num
  have h2 : 3 * 15 ^ 18 ≤ 16 ^ 18 := by norm_num
  have h3 : 14 ^ 27 < 8 * 13 ^ 27 := by norm_num
  have h4 : 32 * 2 ^ 10 < 3 ^ 10 := by norm_num
  have hr_pow : 14 ^ r ≤ 8 * 13 ^ r := by
    have hstep : 14 ^ r * 13 ^ (27 - r) ≤ 14 ^ r * 14 ^ (27 - r) := by
      gcongr; norm_num
    have hmul : 14 ^ r * 13 ^ (27 - r) < 8 * 13 ^ r * 13 ^ (27 - r) := by
      calc
        14 ^ r * 13 ^ (27 - r) ≤ 14 ^ r * 14 ^ (27 - r) := hstep
        _ = 14 ^ (r + (27 - r)) := (pow_add 14 r (27 - r)).symm
        _ = 14 ^ 27 := by rw [Nat.add_sub_cancel' (by omega)]
        _ < 8 * 13 ^ 27 := h3
        _ = 8 * 13 ^ (r + (27 - r)) := by rw [Nat.add_sub_cancel' (by omega)]
        _ = 8 * 13 ^ r * 13 ^ (27 - r) := by rw [pow_add]; ring
    exact le_of_lt (Nat.lt_of_mul_lt_mul_right hmul)
  have hq_pow : 16 ^ q * (14 ^ 28) ^ q ≤ 15 ^ q * (15 ^ 15 * 13 ^ 13) ^ q := by
    rw [← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left h1 q
  have h15_16 : 3 ^ k * 15 ^ q ≤ 16 ^ q := by
    have h18 : 3 ^ k * (15 ^ 18) ^ k ≤ (16 ^ 18) ^ k := by
      rw [← mul_pow]
      exact Nat.pow_le_pow_left h2 k
    have hle : 15 ^ (q - 18 * k) ≤ 16 ^ (q - 18 * k) := Nat.pow_le_pow_left (by norm_num) _
    calc
      3 ^ k * 15 ^ q = 3 ^ k * 15 ^ (18 * k + (q - 18 * k)) := by
            rw [Nat.add_sub_cancel' hq]
      _ = (3 ^ k * (15 ^ 18) ^ k) * 15 ^ (q - 18 * k) := by rw [pow_add, pow_mul]; ring
      _ ≤ (16 ^ 18) ^ k * 16 ^ (q - 18 * k) := Nat.mul_le_mul h18 hle
      _ = 16 ^ (18 * k + (q - 18 * k)) := by rw [← pow_mul, ← pow_add]
      _ = 16 ^ q := by rw [Nat.add_sub_cancel' hq]
  have hk_pow : 32 * 2 ^ k < 3 ^ k := by
    have hrem : 2 ^ (k - 10) ≤ 3 ^ (k - 10) := Nat.pow_le_pow_left (by norm_num) _
    calc
      32 * 2 ^ k = 32 * 2 ^ (10 + (k - 10)) := by rw [Nat.add_sub_cancel' (by omega)]
      _ = (32 * 2 ^ 10) * 2 ^ (k - 10) := by rw [pow_add]; ring
      _ < 3 ^ 10 * 3 ^ (k - 10) := Nat.mul_lt_mul_of_lt_of_le h4 hrem (by positivity)
      _ = 3 ^ (10 + (k - 10)) := (pow_add 3 10 (k - 10)).symm
      _ = 3 ^ k := by rw [Nat.add_sub_cancel' (by omega)]
  have hmain : 4 * 2 ^ k * 14 ^ m < 15 ^ (15 * q) * 13 ^ (m - 15 * q) := by
    have hpos16 : 0 < 16 ^ q := by positivity
    suffices hs : 16 ^ q * (4 * 2 ^ k * 14 ^ m) < 16 ^ q * (15 ^ (15 * q) * 13 ^ (m - 15 * q)) by
      exact Nat.lt_of_mul_lt_mul_left hs
    rw [hsub]
    have h14m : 14 ^ m = (14 ^ 28) ^ q * 14 ^ r := by
      conv_lhs => rw [hmr, pow_add, pow_mul]
    have h1513 : 15 ^ (15 * q) * 13 ^ (13 * q + r) = (15 ^ 15 * 13 ^ 13) ^ q * 13 ^ r := by
      rw [pow_add, mul_pow, ← pow_mul, ← pow_mul]; ring
    rw [h14m, h1513]
    calc
      16 ^ q * (4 * 2 ^ k * ((14 ^ 28) ^ q * 14 ^ r))
          = (4 * 2 ^ k * 14 ^ r) * (16 ^ q * (14 ^ 28) ^ q) := by ring
      _ ≤ (4 * 2 ^ k * (8 * 13 ^ r)) * (15 ^ q * (15 ^ 15 * 13 ^ 13) ^ q) := by
            exact Nat.mul_le_mul (by gcongr) hq_pow
      _ = (32 * 2 ^ k) * (15 ^ q * ((15 ^ 15 * 13 ^ 13) ^ q * 13 ^ r)) := by ring
      _ < 3 ^ k * (15 ^ q * ((15 ^ 15 * 13 ^ 13) ^ q * 13 ^ r)) := by
            exact Nat.mul_lt_mul_of_pos_right hk_pow (by positivity)
      _ = (3 ^ k * 15 ^ q) * ((15 ^ 15 * 13 ^ 13) ^ q * 13 ^ r) := by ring
      _ ≤ 16 ^ q * ((15 ^ 15 * 13 ^ 13) ^ q * 13 ^ r) := by
            exact Nat.mul_le_mul_right _ h15_16
  have h28 : 28 ^ m = 2 ^ m * 14 ^ m := by
    have : (28 : ℕ) = 2 * 14 := by norm_num
    rw [this, mul_pow]
  rw [h28]
  calc
    4 * 2 ^ k * (2 ^ m * 14 ^ m) = 2 ^ m * (4 * 2 ^ k * 14 ^ m) := by ring
    _ < 2 ^ m * (15 ^ (15 * q) * 13 ^ (m - 15 * q)) :=
          Nat.mul_lt_mul_of_pos_left hmain (by positivity)
    _ = 2 ^ m * 15 ^ (15 * q) * 13 ^ (m - 15 * q) := by ring

def psiBuild (k m : ℕ) (w : Fin k → F2) (i₀ : Fin k) (z : Fin m → F2) (n : ℕ) : F2 :=
  if h1 : i₀.val ≤ n ∧ n < i₀.val + m then
    z ⟨n - i₀.val, by omega⟩ +
      (Finset.univ.filter (fun i : Fin k => i.val < i₀.val)).attach.sum (fun p =>
        w p.1 * psiBuild k m w i₀ z (n - i₀.val + p.1.val))
  else 0
termination_by n
decreasing_by
  have hi := (Finset.mem_filter.mp p.2).2
  omega

lemma psiMap_surj (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (w : Fin k → F2) (hw : w ≠ 0) :
    Function.Surjective (fun b : Fin (k + m - 1) → F2 =>
      fun j : Fin m => dotProduct w (tapeVec k m hk hm b j)) := by
  have hex : ∃ i : Fin k, w i = 1 := by
    by_contra h
    push_neg at h
    apply hw
    ext i
    rcases zmod2_eq_zero_or_one (w i) with h0 | h1
    · exact h0
    · exact (h i h1).elim
  let supp := Finset.univ.filter (fun i : Fin k => w i = 1)
  have hsupp_ne : supp.Nonempty := by
    rcases hex with ⟨i, hi⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let i₀ : Fin k := supp.max' hsupp_ne
  have hi₀_mem : w i₀ = 1 := (Finset.mem_filter.mp (Finset.max'_mem supp hsupp_ne)).2
  have hi₀_max : ∀ i : Fin k, i₀ < i → w i = 0 := by
    intro i hi
    rcases zmod2_eq_zero_or_one (w i) with h0 | h1
    · exact h0
    · have hle : i ≤ i₀ := Finset.le_max' supp i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩)
      exact absurd hi (not_lt_of_ge hle)
  intro z
  let build : ℕ → F2 := psiBuild k m w i₀ z
  let b : Fin (k + m - 1) → F2 := fun r => build r.val
  refine ⟨b, ?_⟩
  ext j
  change dotProduct w (tapeVec k m hk hm b j) = z j
  simp only [dotProduct, tapeVec, b]
  have hsplit : (∑ i : Fin k, w i * build (j.val + i.val)) =
      w i₀ * build (j.val + i₀.val) +
        ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < i₀.val),
          w i * build (j.val + i.val) := by
    have hzero : ∀ i : Fin k, i₀.val < i.val → w i * build (j.val + i.val) = 0 := by
      intro i hi
      rw [hi₀_max i hi, zero_mul]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter (fun i : Fin k => i.val ≤ i₀.val)))]
    · have heq : Finset.univ.filter (fun i : Fin k => i.val ≤ i₀.val) =
          insert i₀ (Finset.univ.filter (fun i : Fin k => i.val < i₀.val)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      rw [heq, Finset.sum_insert]
      simp
    · intro i _ hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
      exact hzero i hi
  rw [hsplit, hi₀_mem, one_mul]
  have hbuild_eq : build (j.val + i₀.val) =
      z j + ∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val < i₀.val),
        w i * build (j.val + i.val) := by
    dsimp only [build]
    rw [psiBuild]
    have hcond : i₀.val ≤ j.val + i₀.val ∧ j.val + i₀.val < i₀.val + m := ⟨by omega, by omega⟩
    rw [dif_pos hcond]
    have hj_sub : (⟨j.val + i₀.val - i₀.val, by omega⟩ : Fin m) = j := by
      ext; simp
    rw [hj_sub]
    congr 1
    rw [← Finset.sum_attach (Finset.univ.filter (fun i : Fin k => i.val < i₀.val))]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    have hidx : j.val + i₀.val - i₀.val + p.1.val = j.val + p.1.val := by omega
    rw [hidx]
  rw [hbuild_eq, add_assoc, zmod2_add_self, add_zero]

def phiBuild (k m : ℕ) (S : Finset (Fin m)) (j₀ : Fin m) (hj₀_max : ∀ j ∈ S, j ≤ j₀)
    (y : Fin k → F2) (n : ℕ) : F2 :=
  if h1 : j₀.val ≤ n ∧ n < j₀.val + k then
    y ⟨n - j₀.val, by omega⟩ +
      (S.erase j₀).attach.sum (fun p =>
        phiBuild k m S j₀ hj₀_max y (p.1.val + (n - j₀.val)))
  else 0
termination_by n
decreasing_by
  have hj := Finset.mem_erase.mp p.2
  have hle := hj₀_max p.1 hj.2
  have hlt : p.1.val < j₀.val := lt_of_le_of_ne hle (Fin.val_ne_of_ne hj.1)
  omega

lemma phiMap_surj (k m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m) (S : Finset (Fin m)) (hS : S.Nonempty) :
    Function.Surjective (fun b : Fin (k + m - 1) → F2 =>
      fun i : Fin k => ∑ j ∈ S, tapeVec k m hk hm b j i) := by
  let j₀ : Fin m := S.max' hS
  have hj₀_mem : j₀ ∈ S := Finset.max'_mem S hS
  have hj₀_max : ∀ j ∈ S, j ≤ j₀ := fun j hj => Finset.le_max' S j hj
  intro y
  let build : ℕ → F2 := phiBuild k m S j₀ hj₀_max y
  let b : Fin (k + m - 1) → F2 := fun r => build r.val
  refine ⟨b, ?_⟩
  ext i
  change (∑ j ∈ S, build (j.val + i.val)) = y i
  rw [← Finset.add_sum_erase S _ hj₀_mem]
  have hbuild_eq : build (j₀.val + i.val) =
      y i + ∑ j ∈ S.erase j₀, build (j.val + i.val) := by
    dsimp only [build]
    rw [phiBuild]
    have hcond : j₀.val ≤ j₀.val + i.val ∧ j₀.val + i.val < j₀.val + k := ⟨by omega, by omega⟩
    rw [dif_pos hcond]
    have hi_sub : (⟨j₀.val + i.val - j₀.val, by omega⟩ : Fin k) = i := by
      ext; simp
    rw [hi_sub]
    congr 1
    rw [← Finset.sum_attach (S.erase j₀)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    have hidx : p.1.val + (j₀.val + i.val - j₀.val) = p.1.val + i.val := by omega
    rw [hidx]
  rw [hbuild_eq, add_assoc, zmod2_add_self, add_zero]

lemma weight_card_bound (k : ℕ) :
    (Finset.univ.filter (fun y : Fin k → F2 =>
      (Finset.univ.filter (fun i : Fin k => y i = 1)).card ≤ k / 32)).card *
      16 ^ (k - k / 32) ≤ 17 ^ k := by
  let S := Finset.univ.filter (fun y : Fin k → F2 =>
    (Finset.univ.filter (fun i : Fin k => y i = 1)).card ≤ k / 32)
  have hle : ∀ y ∈ S,
      16 ^ (k - k / 32) ≤
        16 ^ (Finset.univ.filter (fun i : Fin k => y i = 0)).card *
        1 ^ (Finset.univ.filter (fun i : Fin k => y i = 1)).card := by
    intro y hy
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [one_pow, mul_one]
    have hsum : (Finset.univ.filter (fun i : Fin k => y i = 0)).card +
        (Finset.univ.filter (fun i : Fin k => y i = 1)).card = k := by
      have hunion : Finset.univ.filter (fun i : Fin k => y i = 0) ∪
          Finset.univ.filter (fun i : Fin k => y i = 1) = Finset.univ := by
        ext i; simp [zmod2_eq_zero_or_one]
      have hdisj : Disjoint (Finset.univ.filter (fun i : Fin k => y i = 0))
          (Finset.univ.filter (fun i : Fin k => y i = 1)) := by
        rw [Finset.disjoint_filter]
        intro i _ h0 h1; rw [h0] at h1; exact absurd h1 (by decide)
      have h := Finset.card_union_of_disjoint hdisj
      rw [hunion, Finset.card_univ, Fintype.card_fin] at h
      exact h.symm
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  calc
    S.card * 16 ^ (k - k / 32)
        = ∑ _y ∈ S, 16 ^ (k - k / 32) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ y ∈ S,
          16 ^ (Finset.univ.filter (fun i : Fin k => y i = 0)).card *
          1 ^ (Finset.univ.filter (fun i : Fin k => y i = 1)).card :=
          Finset.sum_le_sum hle
    _ ≤ ∑ y : Fin k → F2,
          16 ^ (Finset.univ.filter (fun i : Fin k => y i = 0)).card *
          1 ^ (Finset.univ.filter (fun i : Fin k => y i = 1)).card :=
          Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ = (16 + 1) ^ k := sum_pow_split k 16 1
    _ = 17 ^ k := by norm_num

lemma poly_lt_exp_helper (k : ℕ) (hk : 128 ≤ k) :
    2 ^ 336 * k ^ 32 < 2 ^ (6 * k) := by
  induction k, hk using Nat.le_induction with
  | base =>
    have h128 : (128 : ℕ) = 2 ^ 7 := by norm_num
    rw [h128, ← pow_mul, ← pow_add]
    exact Nat.pow_lt_pow_right (by norm_num) (by norm_num)
  | succ n hn ih =>
    have hstep : (n + 1) ^ 32 < 64 * n ^ 32 := by
      have h129 : 129 ^ 32 < 64 * 128 ^ 32 := by norm_num
      have hratio : 128 * (n + 1) ≤ 129 * n := by omega
      have hpow := Nat.pow_le_pow_left hratio 32
      rw [mul_pow, mul_pow] at hpow
      have h2 : 128 ^ 32 * (n + 1) ^ 32 < 128 ^ 32 * (64 * n ^ 32) := by
        calc
          128 ^ 32 * (n + 1) ^ 32 ≤ 129 ^ 32 * n ^ 32 := hpow
          _ < (64 * 128 ^ 32) * n ^ 32 := Nat.mul_lt_mul_of_pos_right h129 (by positivity)
          _ = 128 ^ 32 * (64 * n ^ 32) := by ring
      exact Nat.lt_of_mul_lt_mul_left h2
    calc
      2 ^ 336 * (n + 1) ^ 32 < 2 ^ 336 * (64 * n ^ 32) :=
            Nat.mul_lt_mul_of_pos_left hstep (by positivity)
      _ = 64 * (2 ^ 336 * n ^ 32) := by ring
      _ < 64 * 2 ^ (6 * n) := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
      _ = 2 ^ (6 * (n + 1)) := by
            have h64 : (64 : ℕ) = 2 ^ 6 := by norm_num
            rw [h64, ← pow_add]
            congr 1; omega

lemma weight_arith_helper (k m : ℕ) (hk : 128 ≤ k) (hm : m < 1024 * k) :
    4 * m ^ 4 * (Finset.univ.filter (fun y : Fin k → F2 =>
      (Finset.univ.filter (fun i : Fin k => y i = 1)).card ≤ k / 32)).card < 2 ^ k := by
  let W := (Finset.univ.filter (fun y : Fin k → F2 =>
    (Finset.univ.filter (fun i : Fin k => y i = 1)).card ≤ k / 32)).card
  have hW : W * 16 ^ (k - k / 32) ≤ 17 ^ k := weight_card_bound k
  suffices h8 : (4 * m ^ 4 * W) ^ 8 < (2 ^ k) ^ 8 by
    by_contra hge
    push_neg at hge
    exact not_lt_of_ge (Nat.pow_le_pow_left hge 8) h8
  have h16 : (16 ^ (k - k / 32)) ^ 8 ≥ 2 ^ (31 * k) := by
    have h16eq : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [h16eq, ← pow_mul, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h17 : (17 ^ k) ^ 8 < 2 ^ (33 * k) := by
    rw [← pow_mul, mul_comm k 8, pow_mul]
    have h17_8 : 17 ^ 8 < 2 ^ 33 := by norm_num
    have h := Nat.pow_lt_pow_left h17_8 (by omega : k ≠ 0)
    rwa [← pow_mul 2 33 k] at h
  have hm8 : (4 * m ^ 4) ^ 8 ≤ 2 ^ 336 * k ^ 32 := by
    have hmlt : m ≤ 1024 * k := le_of_lt hm
    have hc : (4 * 1024 ^ 4) ^ 8 = 2 ^ 336 := by
      have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
      have h1024 : (1024 : ℕ) = 2 ^ 10 := by norm_num
      rw [h4, h1024, ← pow_mul, ← pow_add, ← pow_mul]
      rfl
    calc
      (4 * m ^ 4) ^ 8 ≤ (4 * (1024 * k) ^ 4) ^ 8 := by gcongr
      _ = (4 * 1024 ^ 4) ^ 8 * k ^ 32 := by ring
      _ = 2 ^ 336 * k ^ 32 := by rw [hc]
  have hpos : 0 < (16 ^ (k - k / 32)) ^ 8 := by positivity
  suffices hs : (4 * m ^ 4 * W) ^ 8 * (16 ^ (k - k / 32)) ^ 8 <
      (2 ^ k) ^ 8 * (16 ^ (k - k / 32)) ^ 8 by
    exact Nat.lt_of_mul_lt_mul_right hs
  calc
    (4 * m ^ 4 * W) ^ 8 * (16 ^ (k - k / 32)) ^ 8
        = (4 * m ^ 4) ^ 8 * (W * 16 ^ (k - k / 32)) ^ 8 := by ring
    _ ≤ (2 ^ 336 * k ^ 32) * (17 ^ k) ^ 8 :=
          Nat.mul_le_mul hm8 (Nat.pow_le_pow_left hW 8)
    _ < 2 ^ (6 * k) * 2 ^ (33 * k) :=
          Nat.mul_lt_mul'' (poly_lt_exp_helper k hk) h17
    _ = 2 ^ (8 * k) * 2 ^ (31 * k) := by rw [← pow_add, ← pow_add]; congr 1; omega
    _ ≤ (2 ^ k) ^ 8 * (16 ^ (k - k / 32)) ^ 8 := by
          rw [← pow_mul, mul_comm k 8]
          exact Nat.mul_le_mul_left _ h16

lemma card_small_subsets_le (m : ℕ) (hm : 1 ≤ m) :
    (Finset.univ.filter (fun S : Finset (Fin m) => 1 ≤ S.card ∧ S.card ≤ 4)).card ≤ m ^ 4 := by
  let f : Fin m × Fin m × Fin m × Fin m → Finset (Fin m) :=
    fun p => {p.1, p.2.1, p.2.2.1, p.2.2.2}
  have hsub : Finset.univ.filter (fun S : Finset (Fin m) => 1 ≤ S.card ∧ S.card ≤ 4) ⊆
      Finset.univ.image f := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
    let L := S.toList
    have hLlen : 1 ≤ L.length ∧ L.length ≤ 4 := by
      simp [L, hS.1, hS.2]
    have hLmem : ∀ x, x ∈ L ↔ x ∈ S := fun x => Finset.mem_toList
    let g : ℕ → Fin m := fun idx => L.getD idx a
    have hg_mem : ∀ idx, g idx ∈ S := by
      intro idx
      dsimp only [g]
      by_cases hlt : idx < L.length
      · rw [List.getD_eq_getElem _ _ hlt]
        exact (hLmem _).mp (List.getElem_mem hlt)
      · rw [List.getD_eq_default _ _ (le_of_not_gt hlt)]
        exact ha
    refine ⟨(g 0, g 1, g 2, g 3), ?_⟩
    ext x
    simp only [f, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      · exact hg_mem 0
      · exact hg_mem 1
      · exact hg_mem 2
      · exact hg_mem 3
    · intro hx
      have hxL : x ∈ L := (hLmem x).mpr hx
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hxL
      have hidx4 : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
      rcases hidx4 with rfl | rfl | rfl | rfl
      · left; exact (List.getD_eq_getElem L a hidx).symm
      · right; left; exact (List.getD_eq_getElem L a hidx).symm
      · right; right; left; exact (List.getD_eq_getElem L a hidx).symm
      · right; right; right; exact (List.getD_eq_getElem L a hidx).symm
  calc
    (Finset.univ.filter (fun S : Finset (Fin m) => 1 ≤ S.card ∧ S.card ≤ 4)).card
        ≤ (Finset.univ.image f).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin m × Fin m × Fin m × Fin m)).card := Finset.card_image_le
    _ = m ^ 4 := by simp [pow_succ]; ring

lemma exists_good_tape (k m : ℕ) (hk : 128 ≤ k) (hm1 : 512 * k ≤ m) (hm2 : m < 1024 * k) :
    ∃ s : Fin (2 ^ (k + m - 1)),
      let v : Fin m → Fin k → F2 := fun j i => if s.val.testBit (j.val + i.val) then 1 else 0
      (∀ w : Fin k → F2, w ≠ 0 → 14 * |∑ j : Fin m, chi (dotProduct w (v j))| ≤ (m : ℤ)) ∧
      (∀ S : Finset (Fin m), 1 ≤ S.card → S.card ≤ 4 →
        k / 32 < (Finset.univ.filter (fun i : Fin k => (∑ j ∈ S, v j i) = 1)).card ∧
        (Finset.univ.filter (fun i : Fin k => (∑ j ∈ S, v j i) = 1)).card < k - k / 32) := by
  have hk1 : 1 ≤ k := by omega
  have hm0 : 1 ≤ m := by omega
  let N := k + m - 1
  let badBias : Finset (Fin N → F2) :=
    Finset.univ.filter (fun b =>
      ∃ w : Fin k → F2, w ≠ 0 ∧ (m : ℤ) < 14 * |∑ j : Fin m, chi (dotProduct w (tapeVec k m hk1 hm0 b j))|)
  let badIndep : Finset (Fin N → F2) :=
    Finset.univ.filter (fun b =>
      ∃ S : Finset (Fin m), 1 ≤ S.card ∧ S.card ≤ 4 ∧
        ((Finset.univ.filter (fun i : Fin k => (∑ j ∈ S, tapeVec k m hk1 hm0 b j i) = 1)).card ≤ k / 32 ∨
         k - k / 32 ≤ (Finset.univ.filter (fun i : Fin k => (∑ j ∈ S, tapeVec k m hk1 hm0 b j i) = 1)).card))
  have hbadBias : badBias.card * 2 < 2 ^ N := by
    let badW : (Fin k → F2) → Finset (Fin N → F2) := fun w =>
      Finset.univ.filter (fun b => (m : ℤ) < 14 * |∑ j : Fin m, chi (dotProduct w (tapeVec k m hk1 hm0 b j))|)
    have hsub : badBias ⊆ (Finset.univ.filter (fun w : Fin k → F2 => w ≠ 0)).biUnion badW := by
      intro b hb
      simp only [badBias, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rcases hb with ⟨w, hw, hgt⟩
      exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ b, hgt⟩⟩
    have hperW : ∀ w : Fin k → F2, w ≠ 0 →
        (badW w).card * 2 ^ m =
          (Finset.univ.filter (fun z : Fin m → F2 => (m : ℤ) < 14 * |∑ j : Fin m, chi (z j)|)).card *
            2 ^ N := by
      intro w hw
      have hadd : ∀ b₁ b₂ : Fin N → F2,
          (fun j : Fin m => dotProduct w (tapeVec k m hk1 hm0 (b₁ + b₂) j)) =
          (fun j : Fin m => dotProduct w (tapeVec k m hk1 hm0 b₁ j)) +
          (fun j : Fin m => dotProduct w (tapeVec k m hk1 hm0 b₂ j)) := by
        intro b₁ b₂; ext j
        simp only [Pi.add_apply, dotProduct, tapeVec, mul_add, Finset.sum_add_distrib]
      exact add_surj_preimage_card _ hadd (psiMap_surj k m hk1 hm0 w hw)
        (fun z : Fin m → F2 => (m : ℤ) < 14 * |∑ j : Fin m, chi (z j)|)
    let Mabs := (Finset.univ.filter (fun z : Fin m → F2 => (m : ℤ) < 14 * |∑ j : Fin m, chi (z j)|)).card
    let Mpos := (Finset.univ.filter (fun z : Fin m → F2 => (m : ℤ) < 14 * (∑ j : Fin m, chi (z j)))).card
    have hsum_le : badBias.card * 2 ^ m ≤ 2 ^ k * (Mabs * 2 ^ N) := by
      calc
        badBias.card * 2 ^ m
            ≤ ((Finset.univ.filter (fun w : Fin k → F2 => w ≠ 0)).biUnion badW).card * 2 ^ m :=
              Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
        _ ≤ (∑ w ∈ Finset.univ.filter (fun w : Fin k → F2 => w ≠ 0), (badW w).card) * 2 ^ m :=
              Nat.mul_le_mul_right _ Finset.card_biUnion_le
        _ = ∑ w ∈ Finset.univ.filter (fun w : Fin k → F2 => w ≠ 0), ((badW w).card * 2 ^ m) :=
              Finset.sum_mul _ _ _
        _ = ∑ w ∈ Finset.univ.filter (fun w : Fin k → F2 => w ≠ 0), (Mabs * 2 ^ N) := by
              refine Finset.sum_congr rfl (fun w hw => ?_)
              exact hperW w (Finset.mem_filter.mp hw).2
        _ = (Finset.univ.filter (fun w : Fin k → F2 => w ≠ 0)).card * (Mabs * 2 ^ N) := by
              rw [Finset.sum_const, smul_eq_mul]
        _ ≤ 2 ^ k * (Mabs * 2 ^ N) := by
              refine Nat.mul_le_mul_right _ ?_
              calc
                (Finset.univ.filter (fun w : Fin k → F2 => w ≠ 0)).card
                    ≤ (Finset.univ : Finset (Fin k → F2)).card := Finset.card_filter_le _ _
                _ = 2 ^ k := by simp [Fintype.card_fun, ZMod.card]
    let q := m / 28
    have hMabs : Mabs ≤ 2 * Mpos := bias_abs_card_bound m
    have hMpos : Mpos * 15 ^ (15 * q) * 13 ^ (m - 15 * q) ≤ 28 ^ m := bias_pos_card_bound m
    have harith := bias_arith_helper k m hk hm1
    have hprod_lt : badBias.card * 2 * (2 ^ m * 15 ^ (15 * q) * 13 ^ (m - 15 * q)) <
        2 ^ N * (2 ^ m * 15 ^ (15 * q) * 13 ^ (m - 15 * q)) := by
      calc
        badBias.card * 2 * (2 ^ m * 15 ^ (15 * q) * 13 ^ (m - 15 * q))
            = (badBias.card * 2 ^ m) * (2 * 15 ^ (15 * q) * 13 ^ (m - 15 * q)) := by ring
        _ ≤ (2 ^ k * (Mabs * 2 ^ N)) * (2 * 15 ^ (15 * q) * 13 ^ (m - 15 * q)) :=
              Nat.mul_le_mul_right _ hsum_le
        _ ≤ (2 ^ k * (2 * Mpos * 2 ^ N)) * (2 * 15 ^ (15 * q) * 13 ^ (m - 15 * q)) := by gcongr
        _ = 2 ^ N * (4 * 2 ^ k * (Mpos * 15 ^ (15 * q) * 13 ^ (m - 15 * q))) := by ring
        _ ≤ 2 ^ N * (4 * 2 ^ k * 28 ^ m) := by gcongr
        _ < 2 ^ N * (2 ^ m * 15 ^ (15 * q) * 13 ^ (m - 15 * q)) :=
              Nat.mul_lt_mul_of_pos_left harith (by positivity)
    exact Nat.lt_of_mul_lt_mul_right hprod_lt
  have hbadIndep : badIndep.card * 2 < 2 ^ N := by
    let Sset := Finset.univ.filter (fun S : Finset (Fin m) => 1 ≤ S.card ∧ S.card ≤ 4)
    let badS : Finset (Fin m) → Finset (Fin N → F2) := fun S =>
      Finset.univ.filter (fun b =>
        (Finset.univ.filter (fun i : Fin k => (∑ j ∈ S, tapeVec k m hk1 hm0 b j i) = 1)).card ≤ k / 32 ∨
        k - k / 32 ≤ (Finset.univ.filter (fun i : Fin k => (∑ j ∈ S, tapeVec k m hk1 hm0 b j i) = 1)).card)
    have hsub : badIndep ⊆ Sset.biUnion badS := by
      intro b hb
      simp only [badIndep, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rcases hb with ⟨S, h1, h4, hor⟩
      exact Finset.mem_biUnion.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, h1, h4⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ b, hor⟩⟩
    let W := (Finset.univ.filter (fun y : Fin k → F2 =>
      (Finset.univ.filter (fun i : Fin k => y i = 1)).card ≤ k / 32)).card
    let W2 := (Finset.univ.filter (fun y : Fin k → F2 =>
      (Finset.univ.filter (fun i : Fin k => y i = 1)).card ≤ k / 32 ∨
      k - k / 32 ≤ (Finset.univ.filter (fun i : Fin k => y i = 1)).card)).card
    have hW2 : W2 ≤ 2 * W := by
      let Wlo := Finset.univ.filter (fun y : Fin k → F2 =>
        (Finset.univ.filter (fun i : Fin k => y i = 1)).card ≤ k / 32)
      let Whi := Finset.univ.filter (fun y : Fin k → F2 =>
        k - k / 32 ≤ (Finset.univ.filter (fun i : Fin k => y i = 1)).card)
      have hsubW : Finset.univ.filter (fun y : Fin k → F2 =>
          (Finset.univ.filter (fun i : Fin k => y i = 1)).card ≤ k / 32 ∨
          k - k / 32 ≤ (Finset.univ.filter (fun i : Fin k => y i = 1)).card) ⊆ Wlo ∪ Whi := by
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Wlo, Whi] at hy ⊢
        exact hy
      have hhi_eq : Whi.card = Wlo.card := by
        refine Finset.card_bij (fun y _ => fun i => y i + 1) ?_ ?_ ?_
        · intro y hy
          simp only [Whi, Wlo, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
          have hcomp : (Finset.univ.filter (fun i : Fin k => y i + 1 = 1)).card +
              (Finset.univ.filter (fun i : Fin k => y i = 1)).card = k := by
            have h0 : Finset.univ.filter (fun i : Fin k => y i + 1 = 1) =
                Finset.univ.filter (fun i : Fin k => y i = 0) := by
              ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              rcases zmod2_eq_zero_or_one (y i) with h | h <;> simp [h]
            rw [h0]
            have hunion : Finset.univ.filter (fun i : Fin k => y i = 0) ∪
                Finset.univ.filter (fun i : Fin k => y i = 1) = Finset.univ := by
              ext i; simp [zmod2_eq_zero_or_one]
            have hdisj : Disjoint (Finset.univ.filter (fun i : Fin k => y i = 0))
                (Finset.univ.filter (fun i : Fin k => y i = 1)) := by
              rw [Finset.disjoint_filter]
              intro i _ h1 h2; rw [h1] at h2; exact absurd h2 (by decide)
            have h := Finset.card_union_of_disjoint hdisj
            rw [hunion, Finset.card_univ, Fintype.card_fin] at h
            exact h.symm
          omega
        · intro y₁ _ y₂ _ h
          ext i
          have hi := congrFun h i
          have hi' : y₁ i + 1 + 1 = y₂ i + 1 + 1 := congrArg (· + 1) hi
          simp only [add_assoc, zmod2_add_self, add_zero] at hi'
          exact hi'
        · intro y hy
          refine ⟨fun i => y i + 1, ?_, ?_⟩
          · simp only [Whi, Wlo, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
            have hcomp : (Finset.univ.filter (fun i : Fin k => y i + 1 = 1)).card +
                (Finset.univ.filter (fun i : Fin k => y i = 1)).card = k := by
              have h0 : Finset.univ.filter (fun i : Fin k => y i + 1 = 1) =
                  Finset.univ.filter (fun i : Fin k => y i = 0) := by
                ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                rcases zmod2_eq_zero_or_one (y i) with h | h <;> simp [h]
              rw [h0]
              have hunion : Finset.univ.filter (fun i : Fin k => y i = 0) ∪
                  Finset.univ.filter (fun i : Fin k => y i = 1) = Finset.univ := by
                ext i; simp [zmod2_eq_zero_or_one]
              have hdisj : Disjoint (Finset.univ.filter (fun i : Fin k => y i = 0))
                  (Finset.univ.filter (fun i : Fin k => y i = 1)) := by
                rw [Finset.disjoint_filter]
                intro i _ h1 h2; rw [h1] at h2; exact absurd h2 (by decide)
              have h := Finset.card_union_of_disjoint hdisj
              rw [hunion, Finset.card_univ, Fintype.card_fin] at h
              exact h.symm
            omega
          · ext i; simp only [add_assoc, zmod2_add_self, add_zero]
      calc
        W2 ≤ (Wlo ∪ Whi).card := Finset.card_le_card hsubW
        _ ≤ Wlo.card + Whi.card := Finset.card_union_le _ _
        _ = 2 * W := by rw [hhi_eq]; ring
    have hperS : ∀ S ∈ Sset, (badS S).card * 2 ^ k = W2 * 2 ^ N := by
      intro S hS
      have hne : S.Nonempty := Finset.card_pos.mp (by have := (Finset.mem_filter.mp hS).2.1; omega)
      have hadd : ∀ b₁ b₂ : Fin N → F2,
          (fun i : Fin k => ∑ j ∈ S, tapeVec k m hk1 hm0 (b₁ + b₂) j i) =
          (fun i : Fin k => ∑ j ∈ S, tapeVec k m hk1 hm0 b₁ j i) +
          (fun i : Fin k => ∑ j ∈ S, tapeVec k m hk1 hm0 b₂ j i) := by
        intro b₁ b₂; ext i
        simp only [Pi.add_apply, tapeVec, Finset.sum_add_distrib]
      exact add_surj_preimage_card _ hadd (phiMap_surj k m hk1 hm0 S hne)
        (fun y : Fin k → F2 =>
          (Finset.univ.filter (fun i : Fin k => y i = 1)).card ≤ k / 32 ∨
          k - k / 32 ≤ (Finset.univ.filter (fun i : Fin k => y i = 1)).card)
    have hsum_le : badIndep.card * 2 ^ k ≤ m ^ 4 * (W2 * 2 ^ N) := by
      calc
        badIndep.card * 2 ^ k
            ≤ (Sset.biUnion badS).card * 2 ^ k := Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
        _ ≤ (∑ S ∈ Sset, (badS S).card) * 2 ^ k := Nat.mul_le_mul_right _ Finset.card_biUnion_le
        _ = ∑ S ∈ Sset, ((badS S).card * 2 ^ k) := Finset.sum_mul _ _ _
        _ = ∑ _S ∈ Sset, (W2 * 2 ^ N) := Finset.sum_congr rfl hperS
        _ = Sset.card * (W2 * 2 ^ N) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ m ^ 4 * (W2 * 2 ^ N) := Nat.mul_le_mul_right _ (card_small_subsets_le m hm0)
    have harith := weight_arith_helper k m hk hm2
    have hlt : badIndep.card * 2 * 2 ^ k < 2 ^ N * 2 ^ k := by
      calc
        badIndep.card * 2 * 2 ^ k = 2 * (badIndep.card * 2 ^ k) := by ring
        _ ≤ 2 * (m ^ 4 * (W2 * 2 ^ N)) := Nat.mul_le_mul_left 2 hsum_le
        _ ≤ 2 * (m ^ 4 * (2 * W * 2 ^ N)) := by gcongr
        _ = 2 ^ N * (4 * m ^ 4 * W) := by ring
        _ < 2 ^ N * 2 ^ k := Nat.mul_lt_mul_of_pos_left harith (by positivity)
    exact Nat.lt_of_mul_lt_mul_right hlt
  have hunion_lt : (badBias ∪ badIndep).card < (Finset.univ : Finset (Fin N → F2)).card := by
    have hcard : (Finset.univ : Finset (Fin N → F2)).card = 2 ^ N := by
      simp [Fintype.card_fun, ZMod.card]
    rw [hcard]
    have h1 := Finset.card_union_le badBias badIndep
    omega
  have hne : (Finset.univ \ (badBias ∪ badIndep)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : (Finset.univ : Finset (Fin N → F2)) ⊆ badBias ∪ badIndep :=
      Finset.sdiff_eq_empty_iff_subset.mp hemp
    exact not_le_of_gt hunion_lt (Finset.card_le_card hsub)
  rcases hne with ⟨b, hb⟩
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or] at hb
  let s : Fin (2 ^ N) := ⟨bitsToNat b, bitsToNat_lt b⟩
  refine ⟨s, ?_, ?_⟩
  · intro w hw
    have hb1 := hb.1
    simp only [badBias, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and,
      not_lt] at hb1
    have hvec : ∀ (j : Fin m) (i : Fin k),
        (if s.val.testBit (j.val + i.val) then (1 : F2) else 0) =
        tapeVec k m hk1 hm0 b j i := fun j i => bitsToNat_fin_testBit b (j.val + i.val) (by omega)
    have hres := hb1 w hw
    have heq : (∑ j : Fin m, chi (dotProduct w (fun i => if s.val.testBit (j.val + i.val) then (1 : F2) else 0))) =
        ∑ j : Fin m, chi (dotProduct w (tapeVec k m hk1 hm0 b j)) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 2; ext i; exact hvec j i
    rw [heq]
    exact hres
  · intro S h1 h4
    have hb2 := hb.2
    simp only [badIndep, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and,
      not_or, not_le] at hb2
    have hvec : ∀ (j : Fin m) (i : Fin k),
        (if s.val.testBit (j.val + i.val) then (1 : F2) else 0) =
        tapeVec k m hk1 hm0 b j i := fun j i => bitsToNat_fin_testBit b (j.val + i.val) (by omega)
    have hres := hb2 S h1 h4
    simp_rw [hvec]
    exact hres

lemma foldl_wires_length (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g rest ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

lemma circuit_wires_length (gs : List Gate) (o : ℕ) (x : List Bool) :
    (Circuit.wires ⟨gs, o⟩ x).length = x.length + gs.length :=
  foldl_wires_length gs x

lemma foldl_wires_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun idx => acc.getD idx false)]) w).getD i false =
      w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hi' : i < (w ++ [g.op.eval (g.inputs.map fun idx => w.getD idx false)]).length := by
      simp; omega
    rw [ih _ hi']
    simp only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi',
      List.getElem_append_left hi]

lemma circuit_wires_append_prefix (g₁ g₂ : List Gate) (o₁ o₂ : ℕ) (x : List Bool) (i : ℕ)
    (hi : i < x.length + g₁.length) :
    (Circuit.wires ⟨g₁ ++ g₂, o₂⟩ x).getD i false = (Circuit.wires ⟨g₁, o₁⟩ x).getD i false := by
  simp only [Circuit.wires, List.foldl_append]
  exact foldl_wires_prefix g₂ (Circuit.wires ⟨g₁, o₁⟩ x) i (by rw [circuit_wires_length]; exact hi)

lemma circuit_wires_input (gs : List Gate) (o : ℕ) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (Circuit.wires ⟨gs, o⟩ x).getD i false = x.getD i false :=
  foldl_wires_prefix gs x i hi

lemma foldl_wires_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    let w' := gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w
    ((gs ++ [g]).foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w) =
      w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)] := by
  simp [List.foldl_append]

lemma foldl_wires_snoc_last (gs : List Gate) (g : Gate) (w : List Bool) :
    let w' := gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w
    ((gs ++ [g]).foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w).getD
      (w.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => w'.getD i false) := by
  intro w'
  rw [foldl_wires_snoc]
  have hlen : w'.length = w.length + gs.length := foldl_wires_length gs w
  have hlt : w.length + gs.length < (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]).length := by
    simp [hlen]
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_append_right (by omega)]
  simp [hlen]

def AON2Gate (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧
  (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))

def buildShiftStage (n : ℕ) (zWire notZWire : ℕ) (ws : List ℕ) (shift : ℕ) (count : ℕ)
    (gs : List Gate) : List Gate × List ℕ :=
  match count with
  | 0 => (gs, [])
  | p + 1 =>
    let res := buildShiftStage n zWire notZWire ws shift p gs
    let gs1 := res.1
    let acc := res.2
    let a := ws.getD p 0
    let b := ws.getD (p + shift) 0
    let base := n + gs1.length
    let g1 : Gate := ⟨.and, [notZWire, a]⟩
    let g2 : Gate := ⟨.and, [zWire, b]⟩
    let g3 : Gate := ⟨.or, [base, base + 1]⟩
    (gs1 ++ [g1, g2, g3], acc ++ [base + 2])

lemma buildShiftStage_spec (n : ℕ) (zWire notZWire : ℕ) (ws : List ℕ) (shift count : ℕ)
    (gs : List Gate) (hz : zWire < n + gs.length) (hnz : notZWire < n + gs.length)
    (hws : ∀ p < count, ws.getD p 0 < n + gs.length ∧ ws.getD (p + shift) 0 < n + gs.length)
    (hRB : ReadsBack n ⟨gs, 0⟩) (hAON : ∀ g ∈ gs, AON2Gate g) :
    let res := buildShiftStage n zWire notZWire ws shift count gs
    res.1.length = gs.length + 3 * count ∧
    res.2.length = count ∧
    (∃ extra, res.1 = gs ++ extra) ∧
    ReadsBack n ⟨res.1, 0⟩ ∧
    (∀ g ∈ res.1, AON2Gate g) ∧
    (∀ p < count, res.2.getD p 0 < n + res.1.length) ∧
    (∀ x : List Bool, x.length = n →
      let w0 := Circuit.wires ⟨gs, 0⟩ x
      let w1 := Circuit.wires ⟨res.1, 0⟩ x
      w0.getD notZWire false = !(w0.getD zWire false) →
      ∀ p < count,
        w1.getD (res.2.getD p 0) false =
          if w0.getD zWire false then w0.getD (ws.getD (p + shift) 0) false
          else w0.getD (ws.getD p 0) false) := by
  induction count with
  | zero =>
    refine ⟨by simp [buildShiftStage], by simp [buildShiftStage], ⟨[], by simp [buildShiftStage]⟩,
      hRB, hAON, by intro p hp; omega, by intro x _ _ p hp; omega⟩
  | succ p ih =>
    have hws' : ∀ q < p, ws.getD q 0 < n + gs.length ∧ ws.getD (q + shift) 0 < n + gs.length :=
      fun q hq => hws q (by omega)
    rcases ih hws' with ⟨hlen1, hlen2, ⟨extra, hextra⟩, hRB1, hAON1, hlt1, heval1⟩
    set res1 := buildShiftStage n zWire notZWire ws shift p gs
    set gs1 := res1.1
    set acc := res1.2
    set a := ws.getD p 0
    set b := ws.getD (p + shift) 0
    set base := n + gs1.length
    set g1 : Gate := ⟨.and, [notZWire, a]⟩
    set g2 : Gate := ⟨.and, [zWire, b]⟩
    set g3 : Gate := ⟨.or, [base, base + 1]⟩
    have ha : a < base := by
      have := (hws p (by omega)).1; omega
    have hb : b < base := by
      have := (hws p (by omega)).2; omega
    have hz1 : zWire < base := by omega
    have hnz1 : notZWire < base := by omega
    have hgs_eq : (buildShiftStage n zWire notZWire ws shift (p + 1) gs).1 =
        ((gs1 ++ [g1]) ++ [g2]) ++ [g3] := by
      simp [buildShiftStage, res1, gs1, a, b, base, g1, g2, g3, List.append_assoc]
    have hacc_eq : (buildShiftStage n zWire notZWire ws shift (p + 1) gs).2 = acc ++ [base + 2] := by
      change res1.2 ++ [n + res1.1.length + 2] = acc ++ [base + 2]
      rfl
    have hlen1' : (buildShiftStage n zWire notZWire ws shift (p + 1) gs).1.length =
        gs.length + 3 * (p + 1) := by
      rw [hgs_eq]; simp [hlen1]; omega
    have hlen2' : (buildShiftStage n zWire notZWire ws shift (p + 1) gs).2.length = p + 1 := by
      rw [hacc_eq]; simp [hlen2]
    have hextra' : ∃ e, (buildShiftStage n zWire notZWire ws shift (p + 1) gs).1 = gs ++ e := by
      refine ⟨extra ++ [g1, g2, g3], ?_⟩
      rw [hgs_eq, hextra]; simp [List.append_assoc]
    have hRB_step : ∀ (L : List Gate) (g : Gate), ReadsBack n ⟨L, 0⟩ →
        (∀ i ∈ g.inputs, i < n + L.length) → ReadsBack n ⟨L ++ [g], 0⟩ := by
      intro L g hRBL hgin j hj i hi
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hlt : j < L.length
      · have hget : gateAt ⟨L ++ [g], 0⟩ j = gateAt ⟨L, 0⟩ j := by
          simp only [gateAt, List.getD_eq_getElem _ _ hlt,
            List.getD_eq_getElem _ _ (by simp; omega : j < (L ++ [g]).length),
            List.getElem_append_left hlt]
        rw [hget] at hi; exact hRBL j hlt i hi
      · have hjeq : j = L.length := by omega
        subst hjeq
        have hget : gateAt ⟨L ++ [g], 0⟩ L.length = g := by
          simp only [gateAt, List.getD_eq_getElem _ _ (by simp : L.length < (L ++ [g]).length),
            List.getElem_append_right (le_refl _)]
          simp
        rw [hget] at hi; exact hgin i hi
    have hRB' : ReadsBack n ⟨(buildShiftStage n zWire notZWire ws shift (p + 1) gs).1, 0⟩ := by
      rw [hgs_eq]
      refine hRB_step _ g3 (hRB_step _ g2 (hRB_step _ g1 hRB1 ?_) ?_) ?_
      · intro i hi; simp [g1] at hi; rcases hi with rfl | rfl <;> omega
      · intro i hi; simp [g2] at hi; rcases hi with rfl | rfl <;> simp <;> omega
      · intro i hi; simp [g3] at hi; rcases hi with rfl | rfl <;> simp <;> omega
    have hAON' : ∀ g ∈ (buildShiftStage n zWire notZWire ws shift (p + 1) gs).1, AON2Gate g := by
      rw [hgs_eq]
      intro g hg
      simp only [List.mem_append, List.mem_singleton] at hg
      rcases hg with ((h | rfl) | rfl) | rfl
      · exact hAON1 g h
      · exact ⟨by simp [g1], Or.inl rfl⟩
      · exact ⟨by simp [g2], Or.inl rfl⟩
      · exact ⟨by simp [g3], Or.inr (Or.inl rfl)⟩
    have hlt' : ∀ q < p + 1,
        (buildShiftStage n zWire notZWire ws shift (p + 1) gs).2.getD q 0 <
          n + (buildShiftStage n zWire notZWire ws shift (p + 1) gs).1.length := by
      intro q hq
      rw [hacc_eq, hlen1']
      by_cases hqp : q < p
      · have hqacc : q < acc.length := by omega
        rw [List.getD_eq_getElem _ _ (by simp [hlen2]; omega), List.getElem_append_left hqacc,
          ← List.getD_eq_getElem _ _ hqacc]
        have h1 : acc.getD q 0 < n + gs1.length := hlt1 q hqp
        have hlen_gs1 : gs1.length = gs.length + 3 * p := hlen1
        exact lt_of_lt_of_le h1 (by rw [hlen_gs1]; omega)
      · have hqe : q = p := by omega
        rw [hqe]
        rw [List.getD_eq_getElem _ _ (by simp [hlen2]), List.getElem_append_right (by omega)]
        simp [hlen2, base, hlen1]; omega
    refine ⟨hlen1', hlen2', hextra', hRB', hAON', hlt', ?_⟩
    intro x hx w0 w1 hnot q hq
    have hw0_len : w0.length = n + gs.length := by
      dsimp only [w0]; rw [circuit_wires_length, hx]
    have hw1_old_len : (Circuit.wires ⟨gs1, 0⟩ x).length = base := by
      rw [circuit_wires_length, hx]
    have hw_gs1_w0 : ∀ u < n + gs.length, (Circuit.wires ⟨gs1, 0⟩ x).getD u false = w0.getD u false := by
      intro u hu
      change (Circuit.wires ⟨gs1, 0⟩ x).getD u false = (Circuit.wires ⟨gs, 0⟩ x).getD u false
      rw [hextra]
      exact circuit_wires_append_prefix gs extra 0 0 x u (by omega)
    have hw_w1_gs1 : ∀ u < base, w1.getD u false = (Circuit.wires ⟨gs1, 0⟩ x).getD u false := by
      intro u hu
      have h3 : (buildShiftStage n zWire notZWire ws shift (p + 1) gs).1 = gs1 ++ [g1, g2, g3] := by
        rw [hgs_eq]; simp [List.append_assoc]
      change (Circuit.wires ⟨(buildShiftStage n zWire notZWire ws shift (p + 1) gs).1, 0⟩ x).getD u false = _
      rw [h3]
      exact circuit_wires_append_prefix gs1 [g1, g2, g3] 0 0 x u (by omega)
    by_cases hqp : q < p
    · have hqacc : q < acc.length := by omega
      have hacc_get : (buildShiftStage n zWire notZWire ws shift (p + 1) gs).2.getD q 0 = acc.getD q 0 := by
        rw [hacc_eq, List.getD_eq_getElem _ _ (by simp [hlen2]; omega), List.getElem_append_left hqacc,
          List.getD_eq_getElem _ _ hqacc]
      rw [hacc_get, hw_w1_gs1 _ (hlt1 q hqp)]
      exact heval1 x hx hnot q hqp
    · have hqe : q = p := by omega
      rw [hqe]
      have hacc_get : (buildShiftStage n zWire notZWire ws shift (p + 1) gs).2.getD p 0 = base + 2 := by
        rw [hacc_eq, List.getD_eq_getElem _ _ (by simp [hlen2]), List.getElem_append_right (by omega)]
        simp [hlen2]
      rw [hacc_get]
      let fstep : List Bool → Gate → List Bool :=
        fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]
      let wa := Circuit.wires ⟨gs1, 0⟩ x
      let wb := fstep wa g1
      let wc := fstep wb g2
      let wd := fstep wc g3
      have hwd : w1 = wd := by
        have h3 : (buildShiftStage n zWire notZWire ws shift (p + 1) gs).1 = gs1 ++ [g1, g2, g3] := by
          rw [hgs_eq]; simp [List.append_assoc]
        simp [w1, Circuit.wires, h3, List.foldl_append, fstep, wa, wb, wc, wd]
      have hwa_len : wa.length = base := hw1_old_len
      have hwb_len : wb.length = base + 1 := by simp [wb, fstep, hwa_len]
      have hwc_len : wc.length = base + 2 := by simp [wc, fstep, hwb_len]
      have hwd_len : wd.length = base + 3 := by simp [wd, fstep, hwc_len]
      have hwb_old : ∀ u < base, wb.getD u false = wa.getD u false := by
        intro u hu
        simp only [wb, fstep]
        rw [List.getD_eq_getElem _ _ (by simp [hwa_len]; omega),
          List.getElem_append_left (by omega), List.getD_eq_getElem _ _ (by omega)]
      have hwb_new : wb.getD base false = (wa.getD notZWire false && wa.getD a false) := by
        simp only [wb, fstep]
        rw [List.getD_eq_getElem _ _ (by simp [hwa_len]),
          List.getElem_append_right (by omega)]
        simp [hwa_len, g1, GateOp.eval]
      have hwc_old : ∀ u < base + 1, wc.getD u false = wb.getD u false := by
        intro u hu
        simp only [wc, fstep]
        rw [List.getD_eq_getElem _ _ (by simp [hwb_len]; omega),
          List.getElem_append_left (by omega), List.getD_eq_getElem _ _ (by omega)]
      have hwc_new : wc.getD (base + 1) false = (wb.getD zWire false && wb.getD b false) := by
        simp only [wc, fstep]
        rw [List.getD_eq_getElem _ _ (by simp [hwb_len]),
          List.getElem_append_right (by omega)]
        simp [hwb_len, g2, GateOp.eval]
      have hwd_new : wd.getD (base + 2) false = (wc.getD base false || wc.getD (base + 1) false) := by
        simp only [wd, fstep]
        rw [List.getD_eq_getElem _ _ (by simp [hwc_len]),
          List.getElem_append_right (by omega)]
        simp [hwc_len, g3, GateOp.eval]
      rw [hwd, hwd_new, hwc_old base (by omega), hwb_new, hwc_new,
        hwb_old zWire hz1, hwb_old b hb,
        hw_gs1_w0 notZWire hnz, hw_gs1_w0 zWire hz,
        hw_gs1_w0 a (hws p (by omega)).1, hw_gs1_w0 b (hws p (by omega)).2, hnot]
      cases w0.getD zWire false <;> simp [a, b]

def buildBarrelShifter (k t : ℕ) (notZWires : List ℕ) (wFalse wTrue : ℕ) (sVal : ℕ) :
    ∀ r : ℕ, List Gate → List Gate × List ℕ
  | 0, gs =>
    (gs, List.ofFn (fun p : Fin (k + 2 ^ t - 1) => if sVal.testBit p.val then wTrue else wFalse))
  | step + 1, gs =>
    let res := buildBarrelShifter k t notZWires wFalse wTrue sVal step gs
    let r := t - 1 - step
    buildShiftStage (k + t) (k + r) (notZWires.getD r 0) res.2 (2 ^ r) (k + 2 ^ r - 1) res.1

lemma testBit_eq_mod2 (n r : ℕ) : n.testBit r = decide ((n / 2 ^ r) % 2 = 1) := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm, Nat.and_one_is_mod]
  have hlt : (n / 2 ^ r) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  by_cases h1 : (n / 2 ^ r) % 2 = 1
  · simp [h1]
  · have h0 : (n / 2 ^ r) % 2 = 0 := by omega
    simp [h0]

lemma testBit_div_pow_split (j r : ℕ) :
    (j / 2 ^ r) * 2 ^ r = (j / 2 ^ (r + 1)) * 2 ^ (r + 1) + if j.testBit r then 2 ^ r else 0 := by
  rw [testBit_eq_mod2]
  have hdiv2 : j / 2 ^ (r + 1) = (j / 2 ^ r) / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [hdiv2]
  have hmod := Nat.div_add_mod (j / 2 ^ r) 2
  have hlt : (j / 2 ^ r) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  by_cases h1 : (j / 2 ^ r) % 2 = 1
  · simp only [h1, decide_true, ite_true]
    rw [pow_succ]
    have hq : j / 2 ^ r = 2 * ((j / 2 ^ r) / 2) + 1 := by omega
    conv_lhs => rw [hq]
    ring
  · have h0 : (j / 2 ^ r) % 2 = 0 := by omega
    simp only [h0, show decide ((0 : ℕ) = 1) = false by decide, Bool.false_eq_true, ite_false, add_zero]
    rw [pow_succ]
    have hq : j / 2 ^ r = 2 * ((j / 2 ^ r) / 2) := by omega
    conv_lhs => rw [hq]
    ring

lemma buildBarrelShifter_spec (k t : ℕ) (hk : 1 ≤ k) (notZWires : List ℕ)
    (wFalse wTrue sVal : ℕ) (gs : List Gate)
    (hF : wFalse < k + t + gs.length) (hT : wTrue < k + t + gs.length)
    (hnz : ∀ r < t, notZWires.getD r 0 < k + t + gs.length)
    (hRB : ReadsBack (k + t) ⟨gs, 0⟩) (hAON : ∀ g ∈ gs, AON2Gate g) :
    ∀ step ≤ t,
      let res := buildBarrelShifter k t notZWires wFalse wTrue sVal step gs
      let rem := t - step
      res.1.length = gs.length + 3 * (step * k + (2 ^ t - 2 ^ rem) - step) ∧
      res.2.length = k + 2 ^ rem - 1 ∧
      (∃ extra, res.1 = gs ++ extra) ∧
      ReadsBack (k + t) ⟨res.1, 0⟩ ∧
      (∀ g ∈ res.1, AON2Gate g) ∧
      (∀ p < k + 2 ^ rem - 1, res.2.getD p 0 < k + t + res.1.length) ∧
      (∀ (row : Fin k → Bool) (j : Fin (2 ^ t)),
        let x := List.ofFn row ++ List.ofFn (fun z : Fin t => j.val.testBit z.val)
        let w0 := Circuit.wires ⟨gs, 0⟩ x
        let w1 := Circuit.wires ⟨res.1, 0⟩ x
        w0.getD wFalse false = false →
        w0.getD wTrue false = true →
        (∀ r < t, w0.getD (notZWires.getD r 0) false = !(j.val.testBit r)) →
        ∀ p < k + 2 ^ rem - 1,
          w1.getD (res.2.getD p 0) false = sVal.testBit (p + (j.val / 2 ^ rem) * 2 ^ rem)) := by
  intro step hstep
  induction step with
  | zero =>
    have hrem : t - 0 = t := by omega
    refine ⟨by simp [buildBarrelShifter], by simp [buildBarrelShifter, hrem],
      ⟨[], by simp [buildBarrelShifter]⟩, hRB, hAON, ?_, ?_⟩
    · intro p hp
      simp only [buildBarrelShifter, hrem] at hp ⊢
      rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hp), List.getElem_ofFn]
      split_ifs <;> omega
    · intro row j x w0 w1 hwf hwt _ p hp
      dsimp only [w0, w1, buildBarrelShifter] at hwf hwt ⊢
      rw [hrem] at hp ⊢
      have hget : (List.ofFn (fun q : Fin (k + 2 ^ t - 1) => if sVal.testBit q.val then wTrue else wFalse)).getD p 0 =
          if sVal.testBit p then wTrue else wFalse := by
        rw [List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact hp), List.getElem_ofFn]
      rw [hget]
      have hdiv0 : j.val / 2 ^ t = 0 := Nat.div_eq_of_lt j.isLt
      rw [hdiv0, zero_mul, add_zero]
      split_ifs with hbit
      · rw [hwt, hbit]
      · rw [hwf, Bool.eq_false_iff.mpr hbit]
  | succ s ih =>
    have hih := ih (by omega)
    set prev := buildBarrelShifter k t notZWires wFalse wTrue sVal s gs
    rcases hih with ⟨hlen1, hlen2, ⟨extra1, hextra1⟩, hRB1, hAON1, hlt1, heval1⟩
    let r := t - 1 - s
    have hr_lt : r < t := by omega
    have hrem_prev : t - s = r + 1 := by omega
    have hrem_cur : t - (s + 1) = r := by omega
    have hz_lt : k + r < k + t + prev.1.length := by omega
    have hnz_lt : notZWires.getD r 0 < k + t + prev.1.length := by
      have := hnz r hr_lt
      have : gs.length ≤ prev.1.length := by rw [hextra1]; simp
      omega
    have hpow2 : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [pow_succ]; ring
    have hpow_ts : 2 ^ (t - s) = 2 ^ r + 2 ^ r := by rw [hrem_prev, hpow2]
    have h1pow : 1 ≤ 2 ^ r := Nat.one_le_pow _ _ (by norm_num)
    have hws_lt : ∀ p < k + 2 ^ r - 1,
        prev.2.getD p 0 < k + t + prev.1.length ∧
        prev.2.getD (p + 2 ^ r) 0 < k + t + prev.1.length := by
      intro p hp
      constructor
      · exact hlt1 p (by omega)
      · exact hlt1 (p + 2 ^ r) (by omega)
    have hspec := buildShiftStage_spec (k + t) (k + r) (notZWires.getD r 0) prev.2 (2 ^ r)
      (k + 2 ^ r - 1) prev.1 hz_lt hnz_lt hws_lt hRB1 hAON1
    rcases hspec with ⟨hslen1, hslen2, ⟨extra2, hextra2⟩, hsRB, hsAON, hslt, hseval⟩
    have hcur_eq : buildBarrelShifter k t notZWires wFalse wTrue sVal (s + 1) gs =
        buildShiftStage (k + t) (k + r) (notZWires.getD r 0) prev.2 (2 ^ r) (k + 2 ^ r - 1) prev.1 := rfl
    rw [hcur_eq]
    have hpow_le1 : 2 ^ (r + 1) ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hpow_le2 : 2 ^ r ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hlen_calc : prev.1.length + 3 * (k + 2 ^ r - 1) =
        gs.length + 3 * ((s + 1) * k + (2 ^ t - 2 ^ r) - (s + 1)) := by
      rw [hlen1, hrem_prev]
      have h2 : s ≤ s * k := Nat.le_mul_of_pos_right s (by omega)
      have h3 : (s + 1) * k = s * k + k := by ring
      omega
    refine ⟨by rw [hslen1, hrem_cur]; exact hlen_calc,
      by rw [hslen2, hrem_cur],
      ⟨extra1 ++ extra2, by rw [hextra2, hextra1, List.append_assoc]⟩,
      hsRB, hsAON, by rw [hrem_cur]; exact hslt, ?_⟩
    intro row j x w0 w1 hwf hwt hnz_ev p hp
    rw [hrem_cur] at hp ⊢
    have hxlen : x.length = k + t := by simp [x]
    have hprev_w0 : ∀ u < k + t + gs.length,
        (Circuit.wires ⟨prev.1, 0⟩ x).getD u false = w0.getD u false := by
      intro u hu
      change (Circuit.wires ⟨prev.1, 0⟩ x).getD u false = (Circuit.wires ⟨gs, 0⟩ x).getD u false
      rw [hextra1]
      exact circuit_wires_append_prefix gs extra1 0 0 x u (by omega)
    have hz_val : (Circuit.wires ⟨prev.1, 0⟩ x).getD (k + r) false = j.val.testBit r := by
      rw [hprev_w0 (k + r) (by omega)]
      have hw0_x : w0.getD (k + r) false = x.getD (k + r) false :=
        circuit_wires_input gs 0 x (k + r) (by omega)
      rw [hw0_x]
      have hlt : k + r < x.length := by omega
      rw [List.getD_eq_getElem _ _ hlt]
      simp only [x, List.getElem_append_right (by simp : (List.ofFn row).length ≤ k + r)]
      simp [hr_lt]
    have hnz_val : (Circuit.wires ⟨prev.1, 0⟩ x).getD (notZWires.getD r 0) false =
        !((Circuit.wires ⟨prev.1, 0⟩ x).getD (k + r) false) := by
      rw [hprev_w0 _ (hnz r hr_lt), hnz_ev r hr_lt, hz_val]
    have hse := hseval x hxlen hnz_val p hp
    rw [hse, hz_val]
    have hp1 : p < k + 2 ^ (t - s) - 1 := by omega
    have hp2 : p + 2 ^ r < k + 2 ^ (t - s) - 1 := by omega
    have hev1 := heval1 row j hwf hwt hnz_ev p hp1
    have hev2 := heval1 row j hwf hwt hnz_ev (p + 2 ^ r) hp2
    rw [hev1, hev2, hrem_prev]
    have hsplit := testBit_div_pow_split j.val r
    rw [hsplit]
    split_ifs <;> congr 1 <;> omega

def buildDotAnds (n : ℕ) (ws : List ℕ) (count : ℕ) (gs : List Gate) : List Gate × List ℕ :=
  match count with
  | 0 => (gs, [])
  | i + 1 =>
    let res := buildDotAnds n ws i gs
    let base := n + res.1.length
    (res.1 ++ [⟨.and, [i, ws.getD i 0]⟩], res.2 ++ [base])

lemma buildDotAnds_spec (n : ℕ) (ws : List ℕ) (count : ℕ) (hcn : count ≤ n)
    (gs : List Gate) (hws : ∀ i < count, ws.getD i 0 < n + gs.length)
    (hRB : ReadsBack n ⟨gs, 0⟩) (hAON : ∀ g ∈ gs, AON2Gate g) :
    let res := buildDotAnds n ws count gs
    res.1.length = gs.length + count ∧
    res.2.length = count ∧
    (∃ extra, res.1 = gs ++ extra) ∧
    ReadsBack n ⟨res.1, 0⟩ ∧
    (∀ g ∈ res.1, AON2Gate g) ∧
    (∀ i < count, res.2.getD i 0 < n + res.1.length) ∧
    (∀ x : List Bool, x.length = n →
      ∀ i < count,
        (Circuit.wires ⟨res.1, 0⟩ x).getD (res.2.getD i 0) false =
          (x.getD i false && (Circuit.wires ⟨gs, 0⟩ x).getD (ws.getD i 0) false)) := by
  induction count with
  | zero =>
    refine ⟨by simp [buildDotAnds], by simp [buildDotAnds], ⟨[], by simp [buildDotAnds]⟩,
      hRB, hAON, by intro i hi; omega, by intro x _ i hi; omega⟩
  | succ i ih =>
    have hih := ih (by omega) (fun q hq => hws q (by omega))
    dsimp only at hih
    set res1 := buildDotAnds n ws i gs
    rcases hih with ⟨hlen1, hlen2, ⟨extra, hextra⟩, hRB1, hAON1, hlt1, heval1⟩
    set g : Gate := ⟨.and, [i, ws.getD i 0]⟩
    have hgin : ∀ u ∈ g.inputs, u < n + res1.1.length := by
      intro u hu
      simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · omega
      · have := hws i (by omega); omega
    have hRB' : ReadsBack n ⟨res1.1 ++ [g], 0⟩ := by
      intro j hj u hu
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hlt : j < res1.1.length
      · have hget : gateAt ⟨res1.1 ++ [g], 0⟩ j = gateAt ⟨res1.1, 0⟩ j := by
          simp only [gateAt, List.getD_eq_getElem _ _ hlt,
            List.getD_eq_getElem _ _ (by simp; omega : j < (res1.1 ++ [g]).length),
            List.getElem_append_left hlt]
        rw [hget] at hu; exact hRB1 j hlt u hu
      · have hjeq : j = res1.1.length := by omega
        subst hjeq
        have hget : gateAt ⟨res1.1 ++ [g], 0⟩ res1.1.length = g := by
          simp only [gateAt, List.getD_eq_getElem _ _ (by simp : res1.1.length < (res1.1 ++ [g]).length),
            List.getElem_append_right (le_refl _)]
          simp
        rw [hget] at hu; exact hgin u hu
    have hAON' : ∀ g' ∈ res1.1 ++ [g], AON2Gate g' := by
      intro g' hg'
      simp only [List.mem_append, List.mem_singleton] at hg'
      rcases hg' with h | rfl
      · exact hAON1 g' h
      · exact ⟨by simp [g], Or.inl rfl⟩
    have hdef : buildDotAnds n ws (i + 1) gs = (res1.1 ++ [g], res1.2 ++ [n + res1.1.length]) := rfl
    rw [hdef]
    refine ⟨by simp [hlen1]; omega,
      by simp [hlen2],
      ⟨extra ++ [g], by rw [hextra, List.append_assoc]⟩,
      hRB', hAON', ?_, ?_⟩
    · intro q hq
      by_cases hqi : q < i
      · have hq2 : q < res1.2.length := by omega
        rw [List.getD_eq_getElem (res1.2 ++ [n + res1.1.length]) 0 (by simp [hlen2]; omega),
          List.getElem_append_left hq2, ← List.getD_eq_getElem res1.2 0 hq2]
        have hlt_q : res1.2.getD q 0 < n + res1.1.length := hlt1 q hqi
        simp only [List.length_append, List.length_singleton]; omega
      · have hqe : q = i := by omega
        rw [hqe]
        rw [List.getD_eq_getElem (res1.2 ++ [n + res1.1.length]) 0 (by simp [hlen2]),
          List.getElem_append_right (by omega)]
        simp [hlen2]
    · intro x hx q hq
      by_cases hqi : q < i
      · have hq2 : q < res1.2.length := by omega
        rw [List.getD_eq_getElem (res1.2 ++ [n + res1.1.length]) 0 (by simp [hlen2]; omega),
          List.getElem_append_left hq2, ← List.getD_eq_getElem res1.2 0 hq2]
        have hlt_q : res1.2.getD q 0 < n + res1.1.length := hlt1 q hqi
        rw [circuit_wires_append_prefix res1.1 [g] 0 0 x (res1.2.getD q 0) (by omega)]
        exact heval1 x hx q hqi
      · have hqe : q = i := by omega
        rw [hqe]
        rw [List.getD_eq_getElem (res1.2 ++ [n + res1.1.length]) 0 (by simp [hlen2]),
          List.getElem_append_right (by omega)]
        simp only [hlen2, Nat.sub_self, List.getElem_cons_zero]
        have hnew := foldl_wires_snoc_last res1.1 g x
        simp only [Circuit.wires] at hnew ⊢
        rw [hx] at hnew
        rw [hnew]
        have hi_w : (Circuit.wires ⟨res1.1, 0⟩ x).getD i false = x.getD i false :=
          circuit_wires_input res1.1 0 x i (by omega)
        have hws_w : (Circuit.wires ⟨res1.1, 0⟩ x).getD (ws.getD i 0) false =
            (Circuit.wires ⟨gs, 0⟩ x).getD (ws.getD i 0) false := by
          rw [hextra]
          exact circuit_wires_append_prefix gs extra 0 0 x (ws.getD i 0) (by have := hws i (by omega); omega)
        simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true]
        change ((Circuit.wires ⟨res1.1, 0⟩ x).getD i false &&
            (Circuit.wires ⟨res1.1, 0⟩ x).getD (ws.getD i 0) false) = _
        rw [hi_w, hws_w]
        rfl

def buildXorFoldAON (n : ℕ) : List ℕ → List Gate → List Gate × ℕ
  | [], gs => (gs, 0)
  | [a], gs => (gs, a)
  | a :: b :: rest, gs =>
    let base := n + gs.length
    let g1 : Gate := ⟨.or, [a, b]⟩
    let g2 : Gate := ⟨.and, [a, b]⟩
    let g3 : Gate := ⟨.not, [base + 1]⟩
    let g4 : Gate := ⟨.and, [base, base + 2]⟩
    buildXorFoldAON n ((base + 3) :: rest) (gs ++ [g1, g2, g3, g4])
termination_by ws _ => ws.length

lemma buildXorFoldAON_spec (n : ℕ) (ws : List ℕ) (hws_ne : ws ≠ []) (gs : List Gate)
    (hws_lt : ∀ w ∈ ws, w < n + gs.length)
    (hRB : ReadsBack n ⟨gs, 0⟩) (hAON : ∀ g ∈ gs, AON2Gate g) :
    let res := buildXorFoldAON n ws gs
    res.1.length = gs.length + 4 * (ws.length - 1) ∧
    (∃ extra, res.1 = gs ++ extra) ∧
    ReadsBack n ⟨res.1, 0⟩ ∧
    (∀ g ∈ res.1, AON2Gate g) ∧
    res.2 < n + res.1.length ∧
    (∀ x : List Bool, x.length = n →
      (Circuit.wires ⟨res.1, 0⟩ x).getD res.2 false =
        ws.foldl (fun acc w => acc ^^ (Circuit.wires ⟨gs, 0⟩ x).getD w false) false) := by
  induction hlen : ws.length using Nat.strongRecOn generalizing ws gs with
  | _ len ih =>
    match ws with
    | [] => exact (hws_ne rfl).elim
    | [a] =>
      subst hlen
      simp only [buildXorFoldAON, List.length_singleton, Nat.sub_self, mul_zero, add_zero]
      refine ⟨trivial, ⟨[], by simp⟩, hRB, hAON, hws_lt a (by simp), ?_⟩
      intro x _
      simp
    | a :: b :: rest =>
      subst hlen
      let base := n + gs.length
      let g1 : Gate := ⟨.or, [a, b]⟩
      let g2 : Gate := ⟨.and, [a, b]⟩
      let g3 : Gate := ⟨.not, [base + 1]⟩
      let g4 : Gate := ⟨.and, [base, base + 2]⟩
      let gs1 := gs ++ [g1, g2, g3, g4]
      have ha : a < base := hws_lt a (by simp)
      have hb : b < base := hws_lt b (by simp)
      have hRB_step : ∀ (L : List Gate) (g : Gate), ReadsBack n ⟨L, 0⟩ →
          (∀ i ∈ g.inputs, i < n + L.length) → ReadsBack n ⟨L ++ [g], 0⟩ := by
        intro L g hRBL hgin j hj i hi
        simp only [List.length_append, List.length_singleton] at hj
        by_cases hlt : j < L.length
        · have hget : gateAt ⟨L ++ [g], 0⟩ j = gateAt ⟨L, 0⟩ j := by
            simp only [gateAt, List.getD_eq_getElem _ _ hlt,
              List.getD_eq_getElem _ _ (by simp; omega : j < (L ++ [g]).length),
              List.getElem_append_left hlt]
          rw [hget] at hi; exact hRBL j hlt i hi
        · have hjeq : j = L.length := by omega
          subst hjeq
          have hget : gateAt ⟨L ++ [g], 0⟩ L.length = g := by
            simp only [gateAt, List.getD_eq_getElem _ _ (by simp : L.length < (L ++ [g]).length),
              List.getElem_append_right (le_refl _)]
            simp
          rw [hget] at hi; exact hgin i hi
      have hgs1_eq : gs1 = (((gs ++ [g1]) ++ [g2]) ++ [g3]) ++ [g4] := by
        simp [gs1, List.append_assoc]
      have hRB1 : ReadsBack n ⟨gs1, 0⟩ := by
        rw [hgs1_eq]
        refine hRB_step _ g4 (hRB_step _ g3 (hRB_step _ g2 (hRB_step _ g1 hRB ?_) ?_) ?_) ?_
        · intro i hi; simp [g1] at hi; rcases hi with rfl | rfl <;> omega
        · intro i hi; simp [g2] at hi; rcases hi with rfl | rfl <;> simp <;> omega
        · intro i hi; simp [g3] at hi; subst hi; simp; omega
        · intro i hi; simp [g4] at hi; rcases hi with rfl | rfl <;> simp <;> omega
      have hAON1 : ∀ g ∈ gs1, AON2Gate g := by
        intro g hg
        simp only [gs1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with h | rfl | rfl | rfl | rfl
        · exact hAON g h
        · exact ⟨by simp [g1], Or.inr (Or.inl rfl)⟩
        · exact ⟨by simp [g2], Or.inl rfl⟩
        · exact ⟨by simp [g3], Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
        · exact ⟨by simp [g4], Or.inl rfl⟩
      have hws1_lt : ∀ w ∈ (base + 3) :: rest, w < n + gs1.length := by
        intro w hw
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hmem
        · simp [gs1, base]; omega
        · have := hws_lt w (by simp [hmem]); simp [gs1]; omega
      have hrec := ih ((base + 3) :: rest).length (by simp) ((base + 3) :: rest) (by simp)
        gs1 hws1_lt hRB1 hAON1 rfl
      dsimp only at hrec
      rcases hrec with ⟨hlen_r, ⟨extra, hextra⟩, hRB2, hAON2, hout, heval⟩
      have hres_eq : buildXorFoldAON n (a :: b :: rest) gs =
          buildXorFoldAON n ((base + 3) :: rest) gs1 := by
        simp [buildXorFoldAON, base, g1, g2, g3, g4, gs1]
      rw [hres_eq]
      refine ⟨by
          simp only [List.length_cons, gs1, List.length_append, List.length_nil] at hlen_r ⊢
          omega,
        ⟨[g1, g2, g3, g4] ++ extra, by rw [hextra]; simp [gs1, List.append_assoc]⟩,
        hRB2, hAON2, hout, ?_⟩
      intro x hx
      rw [heval x hx]
      have hwa_len : (Circuit.wires ⟨gs, 0⟩ x).length = base := by
        rw [circuit_wires_length, hx]
      let fstep : List Bool → Gate → List Bool :=
        fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]
      let wa := Circuit.wires ⟨gs, 0⟩ x
      let wb := fstep wa g1
      let wc := fstep wb g2
      let wd := fstep wc g3
      let we := fstep wd g4
      have hwe : Circuit.wires ⟨gs1, 0⟩ x = we := by
        simp [Circuit.wires, gs1, List.foldl_append, fstep, wa, wb, wc, wd, we]
      have hwa_len' : wa.length = base := hwa_len
      have hwb_len : wb.length = base + 1 := by simp [wb, fstep, hwa_len']
      have hwc_len : wc.length = base + 2 := by simp [wc, fstep, hwb_len]
      have hwd_len : wd.length = base + 3 := by simp [wd, fstep, hwc_len]
      have hwb_old : ∀ u < base, wb.getD u false = wa.getD u false := by
        intro u hu
        simp only [wb, fstep]
        rw [List.getD_eq_getElem _ _ (by simp [hwa_len']; omega),
          List.getElem_append_left (by omega), List.getD_eq_getElem _ _ (by omega)]
      have hwb_new : wb.getD base false = (wa.getD a false || wa.getD b false) := by
        simp only [wb, fstep]
        rw [List.getD_eq_getElem _ _ (by simp [hwa_len']),
          List.getElem_append_right (by omega)]
        simp [hwa_len', g1, GateOp.eval]
      have hwc_old : ∀ u < base + 1, wc.getD u false = wb.getD u false := by
        intro u hu
        simp only [wc, fstep]
        rw [List.getD_eq_getElem _ _ (by simp [hwb_len]; omega),
          List.getElem_append_left (by omega), List.getD_eq_getElem _ _ (by omega)]
      have hwc_new : wc.getD (base + 1) false = (wb.getD a false && wb.getD b false) := by
        simp only [wc, fstep]
        rw [List.getD_eq_getElem _ _ (by simp [hwb_len]),
          List.getElem_append_right (by omega)]
        simp [hwb_len, g2, GateOp.eval]
      have hwd_old : ∀ u < base + 2, wd.getD u false = wc.getD u false := by
        intro u hu
        simp only [wd, fstep]
        rw [List.getD_eq_getElem _ _ (by simp [hwc_len]; omega),
          List.getElem_append_left (by omega), List.getD_eq_getElem _ _ (by omega)]
      have hwd_new : wd.getD (base + 2) false = !(wc.getD (base + 1) false) := by
        simp only [wd, fstep]
        rw [List.getD_eq_getElem _ _ (by simp [hwc_len]),
          List.getElem_append_right (by omega)]
        simp [hwc_len, g3, GateOp.eval]
      have hwe_new : we.getD (base + 3) false = (wd.getD base false && wd.getD (base + 2) false) := by
        simp only [we, fstep]
        rw [List.getD_eq_getElem _ _ (by simp [hwd_len]),
          List.getElem_append_right (by omega)]
        simp [hwd_len, g4, GateOp.eval]
      have hxor : (Circuit.wires ⟨gs1, 0⟩ x).getD (base + 3) false =
          (wa.getD a false ^^ wa.getD b false) := by
        rw [hwe, hwe_new, hwd_old base (by omega), hwc_old base (by omega), hwb_new,
          hwd_new, hwc_new, hwb_old a ha, hwb_old b hb]
        cases wa.getD a false <;> cases wa.getD b false <;> rfl
      have hrest_eq : ∀ u ∈ rest,
          (Circuit.wires ⟨gs1, 0⟩ x).getD u false = wa.getD u false := by
        intro u hu
        exact circuit_wires_append_prefix gs [g1, g2, g3, g4] 0 0 x u
          (by rw [hx]; exact hws_lt u (by simp [hu]))
      simp only [List.foldl_cons, Bool.false_xor]
      rw [hxor]
      have hfold_congr : ∀ (L : List ℕ) (init : Bool), (∀ u ∈ L, (Circuit.wires ⟨gs1, 0⟩ x).getD u false = wa.getD u false) →
          L.foldl (fun acc w => acc ^^ (Circuit.wires ⟨gs1, 0⟩ x).getD w false) init =
          L.foldl (fun acc w => acc ^^ wa.getD w false) init := by
        intro L
        induction L with
        | nil => intro init _; rfl
        | cons u us ihL =>
          intro init hL
          simp only [List.foldl_cons]
          rw [hL u (by simp)]
          exact ihL _ (fun v hv => hL v (by simp [hv]))
      exact hfold_congr rest _ hrest_eq

lemma foldl_xor_eq_dotProduct {k : ℕ} (f : Fin k → Bool) :
    (List.ofFn f).foldl (fun acc b => acc ^^ b) false =
      decide ((∑ i : Fin k, boolToF2 (f i)) = 1) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.foldl_cons, Bool.false_xor, Fin.sum_univ_succ]
    have hshift : ∀ (L : List Bool) (init : Bool),
        L.foldl (fun acc b => acc ^^ b) init = (init ^^ L.foldl (fun acc b => acc ^^ b) false) := by
      intro L
      induction L with
      | nil => intro init; simp
      | cons c cs ihL =>
        intro init
        simp only [List.foldl_cons, Bool.false_xor]
        rw [ihL (init ^^ c), ihL c, Bool.xor_assoc]
    rw [hshift, ih (fun i => f i.succ)]
    have h := boolToF2_xor (f 0) (decide ((∑ i : Fin n, boolToF2 (f i.succ)) = 1))
    rw [boolToF2_decide] at h
    have h2 := congrArg (fun a : F2 => decide (a = 1)) h
    rw [decide_boolToF2] at h2
    exact h2

lemma exists_small_eval_circuit (k t : ℕ) (hk : 128 ≤ k) (hm2 : 2 ^ t < 1024 * k)
    (s : Fin (2 ^ (k + 2 ^ t - 1))) :
    let v : Fin (2 ^ t) → Fin k → F2 := fun j i => if s.val.testBit (j.val + i.val) then 1 else 0
    ∃ B : Circuit,
      ReadsBack (k + t) B ∧
      B.output < k + t + B.size ∧
      B.size ≤ 3080 * k + 3 * k * t ∧
      (∀ gate ∈ B.gates, gate.inputs.length ≤ 2 ∧
        (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))) ∧
      (∀ (row : Fin k → Bool) (j : Fin (2 ^ t)),
        B.eval (List.ofFn row ++ List.ofFn (fun z : Fin t => j.val.testBit z.val)) =
          decide (dotProduct (fun i => if row i then 1 else 0) (v j) = 1)) := by
  intro v
  let n := k + t
  let gNot0 : Gate := ⟨.not, [0]⟩
  let gFalse : Gate := ⟨.and, [0, n]⟩
  let gTrue : Gate := ⟨.or, [0, n]⟩
  let gs0 : List Gate := [gNot0, gFalse, gTrue] ++ List.ofFn (fun r : Fin t => ⟨.not, [k + r.val]⟩)
  let wFalse := n + 1
  let wTrue := n + 2
  let notZWires : List ℕ := List.ofFn (fun r : Fin t => n + 3 + r.val)
  have hgs0_len : gs0.length = 3 + t := by simp [gs0]; omega
  have hRB0 : ReadsBack n ⟨gs0, 0⟩ := by
    intro j hj u hu
    rw [hgs0_len] at hj
    by_cases hj3 : j < 3
    · have hcase : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hcase with rfl | rfl | rfl
      · have hg : gateAt ⟨gs0, 0⟩ 0 = gNot0 := by simp [gateAt, gs0]
        rw [hg] at hu; simp [gNot0] at hu; omega
      · have hg : gateAt ⟨gs0, 0⟩ 1 = gFalse := by simp [gateAt, gs0]
        rw [hg] at hu; simp [gFalse] at hu; rcases hu with rfl | rfl <;> omega
      · have hg : gateAt ⟨gs0, 0⟩ 2 = gTrue := by simp [gateAt, gs0]
        rw [hg] at hu; simp [gTrue] at hu; rcases hu with rfl | rfl <;> omega
    · have hgt : gateAt ⟨gs0, 0⟩ j = ⟨.not, [k + (j - 3)]⟩ := by
        simp only [gateAt, List.getD_eq_getElem _ _ (by rw [hgs0_len]; exact hj), gs0]
        rw [List.getElem_append_right (by simp; omega)]
        simp [show j - 3 < t by omega]
      rw [hgt] at hu
      simp only [List.mem_singleton] at hu
      omega
  have hAON0 : ∀ g ∈ gs0, AON2Gate g := by
    intro g hg
    simp only [gs0, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_ofFn] at hg
    rcases hg with (rfl | rfl | rfl) | ⟨r, rfl⟩
    · exact ⟨by simp [gNot0], Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
    · exact ⟨by simp [gFalse], Or.inl rfl⟩
    · exact ⟨by simp [gTrue], Or.inr (Or.inl rfl)⟩
    · exact ⟨by simp, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
  have hF_lt : wFalse < n + gs0.length := by rw [hgs0_len]; omega
  have hT_lt : wTrue < n + gs0.length := by rw [hgs0_len]; omega
  have hnz_lt : ∀ r < t, notZWires.getD r 0 < n + gs0.length := by
    intro r hr
    rw [hgs0_len]
    have hrlen : r < notZWires.length := by simp [notZWires, hr]
    rw [List.getD_eq_getElem _ _ hrlen]
    simp only [notZWires, List.getElem_ofFn]
    omega
  have hsh := buildBarrelShifter_spec k t (by omega) notZWires wFalse wTrue s.val gs0
    hF_lt hT_lt hnz_lt hRB0 hAON0 t (le_refl t)
  rcases hsh with ⟨hsh_len1, hsh_len2, ⟨extra_sh, hextra_sh⟩, hsh_RB, hsh_AON, hsh_lt, hsh_ev⟩
  set shRes := buildBarrelShifter k t notZWires wFalse wTrue s.val t gs0
  have hsh_lt_k : ∀ i < k, shRes.2.getD i 0 < n + shRes.1.length := by
    intro i hi
    exact hsh_lt i (by simp; omega)
  have hda := buildDotAnds_spec n shRes.2 k (by omega) shRes.1 hsh_lt_k hsh_RB hsh_AON
  rcases hda with ⟨hda_len1, hda_len2, ⟨extra_da, hextra_da⟩, hda_RB, hda_AON, hda_lt, hda_ev⟩
  set daRes := buildDotAnds n shRes.2 k shRes.1
  have hda_ne : daRes.2 ≠ [] := by
    intro h
    have := hda_len2
    rw [h] at this
    simp at this
    omega
  have hda_mem_lt : ∀ w ∈ daRes.2, w < n + daRes.1.length := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    have hi' : i < k := by omega
    rw [← List.getD_eq_getElem _ _ hi]
    exact hda_lt i hi'
  have hxf := buildXorFoldAON_spec n daRes.2 hda_ne daRes.1 hda_mem_lt hda_RB hda_AON
  rcases hxf with ⟨hxf_len1, ⟨extra_xf, hextra_xf⟩, hxf_RB, hxf_AON, hxf_out, hxf_ev⟩
  set xfRes := buildXorFoldAON n daRes.2 daRes.1
  let B : Circuit := ⟨xfRes.1, xfRes.2⟩
  refine ⟨B, hxf_RB, hxf_out, ?_, hxf_AON, ?_⟩
  · change xfRes.1.length ≤ 3080 * k + 3 * k * t
    rw [hxf_len1, hda_len1, hda_len2, hsh_len1, hgs0_len]
    simp only [Nat.sub_self, pow_zero]
    have hpow_ge : 1 ≤ 2 ^ t := Nat.one_le_pow _ _ (by norm_num)
    have htk : t ≤ k * t := by
      calc t = 1 * t := (one_mul t).symm
      _ ≤ k * t := Nat.mul_le_mul_right t (by omega)
    have hcomm : t * k = k * t := mul_comm t k
    rw [hcomm, mul_assoc 3 k t]
    generalize k * t = kt at htk ⊢
    omega
  · intro row j
    let x := List.ofFn row ++ List.ofFn (fun z : Fin t => j.val.testBit z.val)
    have hxlen : x.length = n := by simp [x, n]
    have hgs0_ev :
        (Circuit.wires ⟨gs0, 0⟩ x).getD wFalse false = false ∧
        (Circuit.wires ⟨gs0, 0⟩ x).getD wTrue false = true ∧
        (∀ r < t, (Circuit.wires ⟨gs0, 0⟩ x).getD (notZWires.getD r 0) false = !(j.val.testBit r)) := by
      let fstep : List Bool → Gate → List Bool :=
        fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]
      let wa := fstep x gNot0
      let wb := fstep wa gFalse
      let wc := fstep wb gTrue
      have hwc_eq : Circuit.wires ⟨[gNot0, gFalse, gTrue], 0⟩ x = wc := by
        simp [Circuit.wires, fstep, wa, wb, wc]
      have hwa_len : wa.length = n + 1 := by simp [wa, fstep, hxlen]
      have hwb_len : wb.length = n + 2 := by simp [wb, fstep, hwa_len]
      have hwc_len : wc.length = n + 3 := by simp [wc, fstep, hwb_len]
      have hwa_old : ∀ u < n, wa.getD u false = x.getD u false := by
        intro u hu
        simp only [wa, fstep]
        rw [List.getD_eq_getElem _ _ (by simp [hxlen]; omega),
          List.getElem_append_left (by omega), List.getD_eq_getElem _ _ (by omega)]
      have hwa_new : wa.getD n false = !(x.getD 0 false) := by
        simp only [wa, fstep]
        rw [List.getD_eq_getElem _ _ (by simp [hxlen]),
          List.getElem_append_right (by omega)]
        simp [hxlen, gNot0, GateOp.eval]
      have hwb_old : ∀ u < n + 1, wb.getD u false = wa.getD u false := by
        intro u hu
        simp only [wb, fstep]
        rw [List.getD_eq_getElem _ _ (by simp [hwa_len]; omega),
          List.getElem_append_left (by omega), List.getD_eq_getElem _ _ (by omega)]
      have hwb_new : wb.getD (n + 1) false = false := by
        simp only [wb, fstep]
        rw [List.getD_eq_getElem _ _ (by simp [hwa_len]),
          List.getElem_append_right (by omega)]
        simp only [List.length_append, hwa_len, List.length_singleton, Nat.sub_self,
          List.getElem_cons_zero, gFalse, GateOp.eval, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true, hwa_old 0 (by omega), hwa_new]
        cases x.getD 0 false <;> rfl
      have hwc_old : ∀ u < n + 2, wc.getD u false = wb.getD u false := by
        intro u hu
        simp only [wc, fstep]
        rw [List.getD_eq_getElem _ _ (by simp [hwb_len]; omega),
          List.getElem_append_left (by omega), List.getD_eq_getElem _ _ (by omega)]
      have hwc_new : wc.getD (n + 2) false = true := by
        simp only [wc, fstep]
        rw [List.getD_eq_getElem _ _ (by simp [hwb_len]),
          List.getElem_append_right (by omega)]
        simp only [List.length_append, hwb_len, List.length_singleton, Nat.sub_self,
          List.getElem_cons_zero, gTrue, GateOp.eval, List.map_cons, List.map_nil,
          List.any_cons, List.any_nil, id_eq, Bool.or_false, hwb_old 0 (by omega),
          hwb_old n (by omega), hwa_old 0 (by omega), hwa_new]
        cases x.getD 0 false <;> rfl
      have hpre_gs0 : ∀ u < n + 3, (Circuit.wires ⟨gs0, 0⟩ x).getD u false = wc.getD u false := by
        intro u hu
        simp only [Circuit.wires, gs0, List.foldl_append]
        have h := foldl_wires_prefix (List.ofFn (fun r : Fin t => ⟨.not, [k + r.val]⟩)) wc u (by omega)
        simpa [Circuit.wires, fstep, wa, wb, wc] using h
      refine ⟨?_, ?_, ?_⟩
      · rw [hpre_gs0 wFalse (by omega), hwc_old wFalse (by omega), hwb_new]
      · rw [hpre_gs0 wTrue (by omega), hwc_new]
      · intro r hr
        have hnz_r : notZWires.getD r 0 = n + 3 + r := by
          have hrlen : r < notZWires.length := by simp [notZWires, hr]
          rw [List.getD_eq_getElem _ _ hrlen]
          simp only [notZWires, List.getElem_ofFn]
        rw [hnz_r]
        have hsplit_not : List.ofFn (fun z : Fin t => (⟨.not, [k + z.val]⟩ : Gate)) =
            (List.ofFn (fun z : Fin r => (⟨.not, [k + z.val]⟩ : Gate)) ++ [⟨.not, [k + r]⟩]) ++
            List.ofFn (fun z : Fin (t - r - 1) => (⟨.not, [k + (r + 1 + z.val)]⟩ : Gate)) := by
          refine List.ext_getElem ?_ ?_
          · simp; omega
          · intro idx h1 h2
            simp only [List.length_ofFn] at h1
            simp only [List.getElem_ofFn]
            by_cases hlt : idx < r
            · rw [List.getElem_append_left (by simp; omega),
                List.getElem_append_left (by simp; omega)]
              simp
            · by_cases heq : idx = r
              · subst heq
                rw [List.getElem_append_left (by simp),
                  List.getElem_append_right (by simp)]
                simp
              · rw [List.getElem_append_right (by simp; omega)]
                simp; omega
        let L1 := [gNot0, gFalse, gTrue] ++ List.ofFn (fun z : Fin r => (⟨.not, [k + z.val]⟩ : Gate))
        let L2 := List.ofFn (fun z : Fin (t - r - 1) => (⟨.not, [k + (r + 1 + z.val)]⟩ : Gate))
        have hgs0_sp : gs0 = (L1 ++ [⟨.not, [k + r]⟩]) ++ L2 := by
          simp [gs0, hsplit_not, L1, L2, List.append_assoc]
        have hL1_len : L1.length = 3 + r := by simp [L1]; omega
        have hpre2 := circuit_wires_append_prefix (L1 ++ [⟨.not, [k + r]⟩]) L2 0 0 x (n + 3 + r)
          (by simp [hxlen, hL1_len]; omega)
        have hlast := foldl_wires_snoc_last L1 ⟨.not, [k + r]⟩ x
        rw [hxlen, hL1_len] at hlast
        have hkr_w : (Circuit.wires ⟨L1, 0⟩ x).getD (k + r) false = x.getD (k + r) false :=
          circuit_wires_input L1 0 x (k + r) (by omega)
        have hkr_x : x.getD (k + r) false = j.val.testBit r := by
          rw [List.getD_eq_getElem _ _ (by omega)]
          simp only [x, List.getElem_append_right (by simp : (List.ofFn row).length ≤ k + r)]
          simp [hr]
        rw [hgs0_sp, hpre2]
        have hidx : n + 3 + r = n + (3 + r) := by omega
        rw [hidx]
        simp only [Circuit.wires] at hlast ⊢
        rw [hlast]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
        exact congrArg Bool.not (by rw [← hkr_x]; exact hkr_w)
    change (Circuit.wires ⟨xfRes.1, 0⟩ x).getD xfRes.2 false = _
    rw [hxf_ev x hxlen]
    have hmap_da : daRes.2.map (fun w => (Circuit.wires ⟨daRes.1, 0⟩ x).getD w false) =
        List.ofFn (fun i : Fin k => row i && s.val.testBit (i.val + j.val)) := by
      refine List.ext_getElem ?_ ?_
      · simp [hda_len2]
      · intro i h1 h2
        simp only [List.length_map, hda_len2] at h1
        simp only [List.getElem_map, List.getElem_ofFn]
        rw [← List.getD_eq_getElem _ _ (by omega : i < daRes.2.length)]
        rw [hda_ev x hxlen i h1]
        have hrow_i : x.getD i false = row ⟨i, h1⟩ := by
          rw [List.getD_eq_getElem _ _ (by omega)]
          simp [x, h1]
        have hsh_i := hsh_ev row j hgs0_ev.1 hgs0_ev.2.1 hgs0_ev.2.2 i (by simp; omega)
        simp only [Nat.sub_self, pow_zero, Nat.div_one, mul_one] at hsh_i
        rw [hrow_i, hsh_i]
    have hfold_map : ∀ (L : List ℕ) (f : ℕ → Bool) (init : Bool),
        L.foldl (fun acc w => acc ^^ f w) init = (L.map f).foldl (fun acc b => acc ^^ b) init := by
      intro L f
      induction L with
      | nil => intro init; rfl
      | cons a as ihL => intro init; simp [ihL]
    rw [hfold_map, hmap_da, foldl_xor_eq_dotProduct]
    congr 2
    simp only [dotProduct, v]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [boolToF2_and, Nat.add_comm i.val j.val]
    rfl

def LegalGate (g : Gate) : Prop :=
  (g.op = .and ∧ g.inputs.length = 2) ∨
  (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨
  (g.op = .not ∧ g.inputs.length = 1)

noncomputable def andCost (gs : List Gate) : ℕ :=
  gs.countP (fun z => @decide (z.op = .and) (Classical.propDecidable _))

lemma andCost_append (g₁ g₂ : List Gate) :
    andCost (g₁ ++ g₂) = andCost g₁ + andCost g₂ := by
  simp [andCost, List.countP_append]

lemma andCost_nil : andCost [] = 0 := rfl

lemma andCost_and (a b : ℕ) : andCost [⟨.and, [a, b]⟩] = 1 := by
  simp [andCost]

lemma andCost_not (a : ℕ) : andCost [⟨.not, [a]⟩] = 0 := by
  simp [andCost]

lemma andCost_mod2 (ins : List ℕ) : andCost [⟨.mod 2, ins⟩] = 0 := by
  simp [andCost]

lemma readsBack_push (n : ℕ) (gs : List Gate) (g : Gate)
    (hRB : ReadsBack n ⟨gs, 0⟩) (hgin : ∀ i ∈ g.inputs, i < n + gs.length) :
    ReadsBack n ⟨gs ++ [g], 0⟩ := by
  intro j hj i hi
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < gs.length
  · have hget : gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
      simp only [gateAt, List.getD_eq_getElem _ _ hlt,
        List.getD_eq_getElem _ _ (by simp; omega : j < (gs ++ [g]).length),
        List.getElem_append_left hlt]
    rw [hget] at hi; exact hRB j hlt i hi
  · have hjeq : j = gs.length := by omega
    subst hjeq
    have hget : gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by
      simp only [gateAt, List.getD_eq_getElem _ _ (by simp : gs.length < (gs ++ [g]).length),
        List.getElem_append_right (le_refl _)]
      simp
    rw [hget] at hi; exact hgin i hi

def mkConstFalse (n : ℕ) (gs : List Gate) : List Gate × ℕ :=
  let base := n + gs.length
  (gs ++ [⟨.mod 2, []⟩, ⟨.not, [base]⟩], base + 1)

lemma mkConstFalse_spec (n : ℕ) (gs : List Gate)
    (hRB : ReadsBack n ⟨gs, 0⟩) (hL : ∀ g ∈ gs, LegalGate g) :
    let res := mkConstFalse n gs
    andCost res.1 = andCost gs ∧
    (∃ extra, res.1 = gs ++ extra) ∧
    ReadsBack n ⟨res.1, 0⟩ ∧
    (∀ g ∈ res.1, LegalGate g) ∧
    res.2 < n + res.1.length ∧
    (∀ x : List Bool, x.length = n → (Circuit.wires ⟨res.1, 0⟩ x).getD res.2 false = false) := by
  let base := n + gs.length
  let g1 : Gate := ⟨.mod 2, []⟩
  let g2 : Gate := ⟨.not, [base]⟩
  have hRB1 : ReadsBack n ⟨(gs ++ [g1]) ++ [g2], 0⟩ :=
    readsBack_push n (gs ++ [g1]) g2
      (readsBack_push n gs g1 hRB (by simp [g1]))
      (by intro i hi; simp [g2] at hi; subst hi; simp [base])
  refine ⟨by simp [mkConstFalse, andCost, List.countP_append],
    ⟨[g1, g2], rfl⟩,
    by simpa [mkConstFalse, g1, g2, List.append_assoc] using hRB1,
    ?_, by simp [mkConstFalse]; omega, ?_⟩
  · intro g hg
    simp only [mkConstFalse, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | rfl | rfl
    · exact hL g h
    · exact Or.inr (Or.inl ⟨rfl, by simp⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · intro x hx
    let wa := Circuit.wires ⟨gs, 0⟩ x
    have hwa_len : wa.length = base := by dsimp only [wa]; rw [circuit_wires_length, hx]
    simp only [mkConstFalse, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change ((wa ++ [GateOp.eval (.mod 2) []]) ++
      [GateOp.eval .not [(wa ++ [GateOp.eval (.mod 2) []]).getD base false]]).getD (base + 1) false = false
    have h1 : (wa ++ [GateOp.eval (.mod 2) []]).getD base false = true := by
      rw [List.getD_eq_getElem _ _ (by simp [hwa_len]), List.getElem_append_right (by omega)]
      simp [hwa_len, GateOp.eval]
    rw [h1]
    rw [List.getD_eq_getElem _ _ (by simp [hwa_len]), List.getElem_append_right (by simp [hwa_len])]
    simp [hwa_len, GateOp.eval]

def mkXorLegal (n : ℕ) (a b : ℕ) (gs : List Gate) : List Gate × ℕ :=
  let base := n + gs.length
  (gs ++ [⟨.mod 2, [a, b]⟩, ⟨.not, [base]⟩], base + 1)

lemma mkXorLegal_spec (n a b : ℕ) (gs : List Gate)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hRB : ReadsBack n ⟨gs, 0⟩) (hL : ∀ g ∈ gs, LegalGate g) :
    let res := mkXorLegal n a b gs
    andCost res.1 = andCost gs ∧
    (∃ extra, res.1 = gs ++ extra) ∧
    ReadsBack n ⟨res.1, 0⟩ ∧
    (∀ g ∈ res.1, LegalGate g) ∧
    res.2 < n + res.1.length ∧
    (∀ x : List Bool, x.length = n →
      (Circuit.wires ⟨res.1, 0⟩ x).getD res.2 false =
        ((Circuit.wires ⟨gs, 0⟩ x).getD a false ^^ (Circuit.wires ⟨gs, 0⟩ x).getD b false)) := by
  let base := n + gs.length
  let g1 : Gate := ⟨.mod 2, [a, b]⟩
  let g2 : Gate := ⟨.not, [base]⟩
  have hRB1 : ReadsBack n ⟨(gs ++ [g1]) ++ [g2], 0⟩ :=
    readsBack_push n (gs ++ [g1]) g2
      (readsBack_push n gs g1 hRB (by intro i hi; simp [g1] at hi; rcases hi with rfl | rfl <;> omega))
      (by intro i hi; simp [g2] at hi; subst hi; simp [base])
  refine ⟨by simp [mkXorLegal, andCost, List.countP_append],
    ⟨[g1, g2], rfl⟩,
    by simpa [mkXorLegal, g1, g2, List.append_assoc] using hRB1,
    ?_, by simp [mkXorLegal]; omega, ?_⟩
  · intro g hg
    simp only [mkXorLegal, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | rfl | rfl
    · exact hL g h
    · exact Or.inr (Or.inl ⟨rfl, by simp⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · intro x hx
    let wa := Circuit.wires ⟨gs, 0⟩ x
    have hwa_len : wa.length = base := by dsimp only [wa]; rw [circuit_wires_length, hx]
    simp only [mkXorLegal, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change ((wa ++ [GateOp.eval (.mod 2) [wa.getD a false, wa.getD b false]]) ++
      [GateOp.eval .not [(wa ++ [GateOp.eval (.mod 2) [wa.getD a false, wa.getD b false]]).getD base false]]).getD
        (base + 1) false = (wa.getD a false ^^ wa.getD b false)
    have h1 : (wa ++ [GateOp.eval (.mod 2) [wa.getD a false, wa.getD b false]]).getD base false =
        GateOp.eval (.mod 2) [wa.getD a false, wa.getD b false] := by
      rw [List.getD_eq_getElem _ _ (by simp [hwa_len]), List.getElem_append_right (by omega)]
      simp [hwa_len]
    rw [h1, List.getD_eq_getElem _ _ (by simp [hwa_len]), List.getElem_append_right (by simp [hwa_len])]
    simp only [List.length_append, hwa_len, List.length_singleton, Nat.sub_self,
      List.getElem_cons_zero, GateOp.eval, List.headD_cons]
    cases wa.getD a false <;> cases wa.getD b false <;> decide

def mkAndLegal (n a b : ℕ) (gs : List Gate) : List Gate × ℕ :=
  let base := n + gs.length
  (gs ++ [⟨.and, [a, b]⟩], base)

lemma mkAndLegal_spec (n a b : ℕ) (gs : List Gate)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hRB : ReadsBack n ⟨gs, 0⟩) (hL : ∀ g ∈ gs, LegalGate g) :
    let res := mkAndLegal n a b gs
    andCost res.1 = andCost gs + 1 ∧
    (∃ extra, res.1 = gs ++ extra) ∧
    ReadsBack n ⟨res.1, 0⟩ ∧
    (∀ g ∈ res.1, LegalGate g) ∧
    res.2 < n + res.1.length ∧
    (∀ x : List Bool, x.length = n →
      (Circuit.wires ⟨res.1, 0⟩ x).getD res.2 false =
        ((Circuit.wires ⟨gs, 0⟩ x).getD a false && (Circuit.wires ⟨gs, 0⟩ x).getD b false)) := by
  let g1 : Gate := ⟨.and, [a, b]⟩
  have hRB1 := readsBack_push n gs g1 hRB
    (by intro i hi; simp [g1] at hi; rcases hi with rfl | rfl <;> omega)
  refine ⟨by simp [mkAndLegal, andCost_append, andCost_and],
    ⟨[g1], rfl⟩, hRB1, ?_, by simp [mkAndLegal], ?_⟩
  · intro g hg
    simp only [mkAndLegal, List.mem_append, List.mem_singleton] at hg
    rcases hg with h | rfl
    · exact hL g h
    · exact Or.inl ⟨rfl, rfl⟩
  · intro x hx
    have h := foldl_wires_snoc_last gs g1 x
    rw [hx] at h
    simpa [mkAndLegal, Circuit.wires, g1, GateOp.eval] using h

def mkOrLegal (n a b : ℕ) (gs : List Gate) : List Gate × ℕ :=
  let base := n + gs.length
  (gs ++ [⟨.not, [a]⟩, ⟨.not, [b]⟩, ⟨.and, [base, base + 1]⟩, ⟨.not, [base + 2]⟩], base + 3)

lemma mkOrLegal_spec (n a b : ℕ) (gs : List Gate)
    (ha : a < n + gs.length) (hb : b < n + gs.length)
    (hRB : ReadsBack n ⟨gs, 0⟩) (hL : ∀ g ∈ gs, LegalGate g) :
    let res := mkOrLegal n a b gs
    andCost res.1 = andCost gs + 1 ∧
    (∃ extra, res.1 = gs ++ extra) ∧
    ReadsBack n ⟨res.1, 0⟩ ∧
    (∀ g ∈ res.1, LegalGate g) ∧
    res.2 < n + res.1.length ∧
    (∀ x : List Bool, x.length = n →
      (Circuit.wires ⟨res.1, 0⟩ x).getD res.2 false =
        ((Circuit.wires ⟨gs, 0⟩ x).getD a false || (Circuit.wires ⟨gs, 0⟩ x).getD b false)) := by
  let base := n + gs.length
  let g1 : Gate := ⟨.not, [a]⟩
  let g2 : Gate := ⟨.not, [b]⟩
  let g3 : Gate := ⟨.and, [base, base + 1]⟩
  let g4 : Gate := ⟨.not, [base + 2]⟩
  have hRB1 : ReadsBack n ⟨(((gs ++ [g1]) ++ [g2]) ++ [g3]) ++ [g4], 0⟩ :=
    readsBack_push n (((gs ++ [g1]) ++ [g2]) ++ [g3]) g4
      (readsBack_push n ((gs ++ [g1]) ++ [g2]) g3
        (readsBack_push n (gs ++ [g1]) g2
          (readsBack_push n gs g1 hRB (by intro i hi; simp [g1] at hi; subst hi; omega))
          (by intro i hi; simp [g2] at hi; subst hi; simp; omega))
        (by intro i hi; simp [g3] at hi; rcases hi with rfl | rfl <;> simp [base] <;> omega))
      (by intro i hi; simp [g4] at hi; subst hi; simp [base]; omega)
  refine ⟨by
      have h : andCost (gs ++ [g1, g2, g3, g4]) = andCost gs + 1 := by
        simp [andCost, List.countP_append, g1, g2, g3, g4]
      exact h,
    ⟨[g1, g2, g3, g4], rfl⟩,
    by simpa [mkOrLegal, g1, g2, g3, g4, List.append_assoc] using hRB1,
    ?_, by simp [mkOrLegal]; omega, ?_⟩
  · intro g hg
    simp only [mkOrLegal, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | rfl | rfl | rfl | rfl
    · exact hL g h
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · intro x hx
    let fstep : List Bool → Gate → List Bool :=
      fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]
    let wa := Circuit.wires ⟨gs, 0⟩ x
    let wb := fstep wa g1
    let wc := fstep wb g2
    let wd := fstep wc g3
    let we := fstep wd g4
    have hwe : Circuit.wires ⟨(mkOrLegal n a b gs).1, 0⟩ x = we := by
      simp [mkOrLegal, Circuit.wires, List.foldl_append, fstep, wa, wb, wc, wd, we, g1, g2, g3, g4, base]
    have hwa_len : wa.length = base := by dsimp only [wa]; rw [circuit_wires_length, hx]
    have hwb_len : wb.length = base + 1 := by simp [wb, fstep, hwa_len]
    have hwc_len : wc.length = base + 2 := by simp [wc, fstep, hwb_len]
    have hwd_len : wd.length = base + 3 := by simp [wd, fstep, hwc_len]
    have hwb_old : ∀ u < base, wb.getD u false = wa.getD u false := by
      intro u hu
      simp only [wb, fstep]
      rw [List.getD_eq_getElem _ _ (by simp [hwa_len]; omega),
        List.getElem_append_left (by omega), List.getD_eq_getElem _ _ (by omega)]
    have hwb_new : wb.getD base false = !(wa.getD a false) := by
      simp only [wb, fstep]
      rw [List.getD_eq_getElem _ _ (by simp [hwa_len]), List.getElem_append_right (by omega)]
      simp [hwa_len, g1, GateOp.eval]
    have hwc_old : ∀ u < base + 1, wc.getD u false = wb.getD u false := by
      intro u hu
      simp only [wc, fstep]
      rw [List.getD_eq_getElem _ _ (by simp [hwb_len]; omega),
        List.getElem_append_left (by omega), List.getD_eq_getElem _ _ (by omega)]
    have hwc_new : wc.getD (base + 1) false = !(wb.getD b false) := by
      simp only [wc, fstep]
      rw [List.getD_eq_getElem _ _ (by simp [hwb_len]), List.getElem_append_right (by omega)]
      simp [hwb_len, g2, GateOp.eval]
    have hwd_new : wd.getD (base + 2) false = (wc.getD base false && wc.getD (base + 1) false) := by
      simp only [wd, fstep]
      rw [List.getD_eq_getElem _ _ (by simp [hwc_len]), List.getElem_append_right (by omega)]
      simp [hwc_len, g3, GateOp.eval]
    have hwe_new : we.getD (base + 3) false = !(wd.getD (base + 2) false) := by
      simp only [we, fstep]
      rw [List.getD_eq_getElem _ _ (by simp [hwd_len]), List.getElem_append_right (by omega)]
      simp [hwd_len, g4, GateOp.eval]
    rw [hwe]
    change we.getD (base + 3) false = (wa.getD a false || wa.getD b false)
    rw [hwe_new, hwd_new, hwc_old base (by omega), hwb_new, hwc_new, hwb_old b hb]
    cases wa.getD a false <;> cases wa.getD b false <;> rfl

def mkFALegal (n a b c : ℕ) (gs : List Gate) : List Gate × ℕ × ℕ :=
  let r1 := mkXorLegal n a c gs
  let r2 := mkXorLegal n b c r1.1
  let r3 := mkXorLegal n r1.2 b r2.1
  let r4 := mkAndLegal n r1.2 r2.2 r3.1
  let r5 := mkXorLegal n c r4.2 r4.1
  (r5.1, r3.2, r5.2)

lemma mkFALegal_spec (n a b c : ℕ) (gs : List Gate)
    (ha : a < n + gs.length) (hb : b < n + gs.length) (hc : c < n + gs.length)
    (hRB : ReadsBack n ⟨gs, 0⟩) (hL : ∀ g ∈ gs, LegalGate g) :
    let res := mkFALegal n a b c gs
    andCost res.1 = andCost gs + 1 ∧
    (∃ extra, res.1 = gs ++ extra) ∧
    ReadsBack n ⟨res.1, 0⟩ ∧
    (∀ g ∈ res.1, LegalGate g) ∧
    res.2.1 < n + res.1.length ∧
    res.2.2 < n + res.1.length ∧
    (∀ x : List Bool, x.length = n →
      let w0 := Circuit.wires ⟨gs, 0⟩ x
      let w1 := Circuit.wires ⟨res.1, 0⟩ x
      (w0.getD a false).toNat + (w0.getD b false).toNat + (w0.getD c false).toNat =
        (w1.getD res.2.1 false).toNat + 2 * (w1.getD res.2.2 false).toNat) := by
  have h1 := mkXorLegal_spec n a c gs ha hc hRB hL
  set r1 := mkXorLegal n a c gs
  rcases h1 with ⟨hc1, ⟨e1, he1⟩, hRB1, hL1, hw1, hev1⟩
  have hlen1 : gs.length ≤ r1.1.length := by rw [he1]; simp
  have h2 := mkXorLegal_spec n b c r1.1 (by omega) (by omega) hRB1 hL1
  set r2 := mkXorLegal n b c r1.1
  rcases h2 with ⟨hc2, ⟨e2, he2⟩, hRB2, hL2, hw2, hev2⟩
  have hlen2 : r1.1.length ≤ r2.1.length := by rw [he2]; simp
  have h3 := mkXorLegal_spec n r1.2 b r2.1 (by omega) (by omega) hRB2 hL2
  set r3 := mkXorLegal n r1.2 b r2.1
  rcases h3 with ⟨hc3, ⟨e3, he3⟩, hRB3, hL3, hw3, hev3⟩
  have hlen3 : r2.1.length ≤ r3.1.length := by rw [he3]; simp
  have h4 := mkAndLegal_spec n r1.2 r2.2 r3.1 (by omega) (by omega) hRB3 hL3
  set r4 := mkAndLegal n r1.2 r2.2 r3.1
  rcases h4 with ⟨hc4, ⟨e4, he4⟩, hRB4, hL4, hw4, hev4⟩
  have hlen4 : r3.1.length ≤ r4.1.length := by rw [he4]; simp
  have h5 := mkXorLegal_spec n c r4.2 r4.1 (by omega) hw4 hRB4 hL4
  set r5 := mkXorLegal n c r4.2 r4.1
  rcases h5 with ⟨hc5, ⟨e5, he5⟩, hRB5, hL5, hw5, hev5⟩
  have hlen5 : r4.1.length ≤ r5.1.length := by rw [he5]; simp
  refine ⟨by simp [mkFALegal, r1, r2, r3, r4, r5, hc5, hc4, hc3, hc2, hc1],
    ⟨e1 ++ e2 ++ e3 ++ e4 ++ e5, by
      simp only [mkFALegal, r1, r2, r3, r4, r5]
      rw [he5, he4, he3, he2, he1]; simp [List.append_assoc]⟩,
    hRB5, hL5, by change r3.2 < n + r5.1.length; omega, hw5, ?_⟩
  intro x hx
  have hpre : ∀ (gA gB : List Gate) (e : List Gate), gB = gA ++ e →
      ∀ u < n + gA.length,
        (Circuit.wires ⟨gB, 0⟩ x).getD u false = (Circuit.wires ⟨gA, 0⟩ x).getD u false := by
    intro gA gB e he u hu
    rw [he]
    exact circuit_wires_append_prefix gA e 0 0 x u (by omega)
  have h_r1_gs : ∀ u < n + gs.length,
      (Circuit.wires ⟨r1.1, 0⟩ x).getD u false = (Circuit.wires ⟨gs, 0⟩ x).getD u false :=
    hpre gs r1.1 e1 he1
  have h_r2_r1 : ∀ u < n + r1.1.length,
      (Circuit.wires ⟨r2.1, 0⟩ x).getD u false = (Circuit.wires ⟨r1.1, 0⟩ x).getD u false :=
    hpre r1.1 r2.1 e2 he2
  have h_r3_r2 : ∀ u < n + r2.1.length,
      (Circuit.wires ⟨r3.1, 0⟩ x).getD u false = (Circuit.wires ⟨r2.1, 0⟩ x).getD u false :=
    hpre r2.1 r3.1 e3 he3
  have h_r4_r3 : ∀ u < n + r3.1.length,
      (Circuit.wires ⟨r4.1, 0⟩ x).getD u false = (Circuit.wires ⟨r3.1, 0⟩ x).getD u false :=
    hpre r3.1 r4.1 e4 he4
  have h_r5_r4 : ∀ u < n + r4.1.length,
      (Circuit.wires ⟨r5.1, 0⟩ x).getD u false = (Circuit.wires ⟨r4.1, 0⟩ x).getD u false :=
    hpre r4.1 r5.1 e5 he5
  let va := (Circuit.wires ⟨gs, 0⟩ x).getD a false
  let vb := (Circuit.wires ⟨gs, 0⟩ x).getD b false
  let vc := (Circuit.wires ⟨gs, 0⟩ x).getD c false
  have hv1 : (Circuit.wires ⟨r1.1, 0⟩ x).getD r1.2 false = (va ^^ vc) := hev1 x hx
  have hv2 : (Circuit.wires ⟨r2.1, 0⟩ x).getD r2.2 false = (vb ^^ vc) := by
    rw [hev2 x hx, h_r1_gs b hb, h_r1_gs c hc]
  have hv3 : (Circuit.wires ⟨r3.1, 0⟩ x).getD r3.2 false = ((va ^^ vc) ^^ vb) := by
    rw [hev3 x hx, h_r2_r1 r1.2 hw1, hv1, h_r2_r1 b (by omega), h_r1_gs b hb]
  have hv4 : (Circuit.wires ⟨r4.1, 0⟩ x).getD r4.2 false = ((va ^^ vc) && (vb ^^ vc)) := by
    rw [hev4 x hx, h_r3_r2 r1.2 (by omega), h_r2_r1 r1.2 hw1, hv1, h_r3_r2 r2.2 hw2, hv2]
  have hv5 : (Circuit.wires ⟨r5.1, 0⟩ x).getD r5.2 false = (vc ^^ ((va ^^ vc) && (vb ^^ vc))) := by
    rw [hev5 x hx, h_r4_r3 c (by omega), h_r3_r2 c (by omega), h_r2_r1 c (by omega), h_r1_gs c hc, hv4]
  have hs_val : (Circuit.wires ⟨r5.1, 0⟩ x).getD r3.2 false = ((va ^^ vc) ^^ vb) := by
    rw [h_r5_r4 r3.2 (by omega), h_r4_r3 r3.2 hw3, hv3]
  change va.toNat + vb.toNat + vc.toNat =
    ((Circuit.wires ⟨r5.1, 0⟩ x).getD r3.2 false).toNat +
    2 * ((Circuit.wires ⟨r5.1, 0⟩ x).getD r5.2 false).toNat
  rw [hs_val, hv5]
  cases va <;> cases vb <;> cases vc <;> decide

def buildParityWire (k : ℕ) (mask : Fin k → F2) (gs : List Gate) : List Gate × ℕ :=
  let r0 := mkConstFalse k gs
  let idxs := (List.finRange k).filter (fun i => decide (mask i = 1))
  idxs.foldl (fun st i => mkXorLegal k st.2 i.val st.1) r0

lemma buildParityWire_spec (k : ℕ) (mask : Fin k → F2) (gs : List Gate)
    (hRB : ReadsBack k ⟨gs, 0⟩) (hL : ∀ g ∈ gs, LegalGate g) :
    let res := buildParityWire k mask gs
    andCost res.1 = andCost gs ∧
    (∃ extra, res.1 = gs ++ extra) ∧
    ReadsBack k ⟨res.1, 0⟩ ∧
    (∀ g ∈ res.1, LegalGate g) ∧
    res.2 < k + res.1.length ∧
    (∀ y : Fin k → F2,
      (Circuit.wires ⟨res.1, 0⟩ (List.ofFn (fun i : Fin k => decide (y i = 1)))).getD res.2 false =
        decide (dotProduct y mask = 1)) := by
  let r0 := mkConstFalse k gs
  rcases mkConstFalse_spec k gs hRB hL with ⟨hc0, ⟨e0, he0⟩, hRB0, hL0, hw0, hev0⟩
  let step : ∀ (L : List (Fin k)) (st : List Gate × ℕ),
      andCost st.1 = andCost gs →
      (∃ e, st.1 = gs ++ e) →
      ReadsBack k ⟨st.1, 0⟩ →
      (∀ g ∈ st.1, LegalGate g) →
      st.2 < k + st.1.length →
      let res := L.foldl (fun p i => mkXorLegal k p.2 i.val p.1) st
      andCost res.1 = andCost gs ∧
      (∃ e, res.1 = gs ++ e) ∧
      ReadsBack k ⟨res.1, 0⟩ ∧
      (∀ g ∈ res.1, LegalGate g) ∧
      res.2 < k + res.1.length ∧
      (∀ y : Fin k → F2,
        let x := List.ofFn (fun i : Fin k => decide (y i = 1))
        (Circuit.wires ⟨res.1, 0⟩ x).getD res.2 false =
          L.foldl (fun acc i => acc ^^ decide (y i = 1))
            ((Circuit.wires ⟨st.1, 0⟩ x).getD st.2 false)) := by
    intro L
    induction L with
    | nil =>
      intro st hcs hex hRBs hLs hws
      exact ⟨hcs, hex, hRBs, hLs, hws, fun _ => rfl⟩
    | cons a as ih =>
      intro st hcs ⟨e, he⟩ hRBs hLs hws
      let st1 := mkXorLegal k st.2 a.val st.1
      rcases mkXorLegal_spec k st.2 a.val st.1 hws (by omega) hRBs hLs with
        ⟨hc1, ⟨e1, he1⟩, hRB1, hL1, hw1, hev1⟩
      have hrec := ih st1 (by rw [hc1, hcs]) ⟨e ++ e1, by rw [he1, he, List.append_assoc]⟩
        hRB1 hL1 hw1
      rcases hrec with ⟨hc2, hex2, hRB2, hL2, hw2, hev2⟩
      refine ⟨hc2, hex2, hRB2, hL2, hw2, ?_⟩
      intro y
      let x := List.ofFn (fun i : Fin k => decide (y i = 1))
      have hxlen : x.length = k := by simp [x]
      simp only [List.foldl_cons]
      rw [hev2 y, hev1 x hxlen]
      have ha_val : (Circuit.wires ⟨st.1, 0⟩ x).getD a.val false = decide (y a = 1) := by
        rw [circuit_wires_input st.1 0 x a.val (by omega)]
        rw [List.getD_eq_getElem _ _ (by omega)]
        simp [x]
      rw [ha_val]
  have hrun := step ((List.finRange k).filter (fun i => decide (mask i = 1))) r0
    hc0 ⟨e0, he0⟩ hRB0 hL0 hw0
  rcases hrun with ⟨hc, hex, hRB', hL', hw', hev⟩
  refine ⟨hc, hex, hRB', hL', hw', ?_⟩
  intro y
  let x := List.ofFn (fun i : Fin k => decide (y i = 1))
  have hxlen : x.length = k := by simp [x]
  dsimp only [buildParityWire]
  rw [hev y, hev0 x hxlen]
  have hfold_sum : ∀ (L : List (Fin k)) (init : Bool),
      L.foldl (fun acc i => acc ^^ decide (y i = 1)) init =
        decide (boolToF2 init + (L.map (fun i => y i)).sum = 1) := by
    intro L
    induction L with
    | nil =>
      intro init
      simp [decide_boolToF2]
    | cons a as ihL =>
      intro init
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ihL, boolToF2_xor, boolToF2_decide, add_assoc]
  rw [hfold_sum]
  simp only [boolToF2, Bool.false_eq_true, ite_false, zero_add]
  congr 2
  have hsum_eq : (((List.finRange k).filter (fun i => decide (mask i = 1))).map (fun i => y i)).sum =
      dotProduct y mask := by
    have hnodup : ((List.finRange k).filter (fun i => decide (mask i = 1))).Nodup :=
      (List.nodup_finRange k).filter _
    rw [← List.sum_toFinset _ hnodup]
    have hfinset : ((List.finRange k).filter (fun i => decide (mask i = 1))).toFinset =
        Finset.univ.filter (fun i : Fin k => mask i = 1) := by
      ext i; simp
    rw [hfinset]
    simp only [dotProduct]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin k => mask i = 1)]
    have h0 : (∑ i ∈ Finset.univ.filter (fun i : Fin k => ¬mask i = 1), y i * mask i) = 0 := by
      refine Finset.sum_eq_zero (fun i hi => ?_)
      have hne : mask i ≠ 1 := (Finset.mem_filter.mp hi).2
      rcases zmod2_eq_zero_or_one (mask i) with h0 | h1
      · rw [h0, mul_zero]
      · exact (hne h1).elim
    rw [h0, add_zero]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [(Finset.mem_filter.mp hi).2, mul_one]
  exact hsum_eq

def reduceCol (n : ℕ) (c : Bool) : List ℕ → List Gate → List Gate × List ℕ
  | [], gs => (gs, [])
  | [a], gs => if c then (gs, [a]) else (gs, [])
  | [a, b], gs =>
    if c then
      let r := mkOrLegal n a b gs
      (r.1, [r.2])
    else
      let r := mkAndLegal n a b gs
      (r.1, [r.2])
  | a :: b :: d :: rest, gs =>
    let r := mkFALegal n a b d gs
    let resRec := reduceCol n c (r.2.1 :: rest) r.1
    (resRec.1, r.2.2 :: resRec.2)
termination_by ws _ => ws.length

lemma reduceCol_spec (n : ℕ) (c : Bool) (ws : List ℕ) (gs : List Gate)
    (hws : ∀ w ∈ ws, w < n + gs.length)
    (hRB : ReadsBack n ⟨gs, 0⟩) (hL : ∀ g ∈ gs, LegalGate g) :
    let res := reduceCol n c ws gs
    andCost res.1 + res.2.length ≤ andCost gs + ws.length ∧
    res.2.length = (ws.length + c.toNat) / 2 ∧
    (∃ extra, res.1 = gs ++ extra) ∧
    ReadsBack n ⟨res.1, 0⟩ ∧
    (∀ g ∈ res.1, LegalGate g) ∧
    (∀ w ∈ res.2, w < n + res.1.length) ∧
    (∀ x : List Bool, x.length = n →
      let w0 := Circuit.wires ⟨gs, 0⟩ x
      let w1 := Circuit.wires ⟨res.1, 0⟩ x
      (res.2.map (fun u => (w1.getD u false).toNat)).sum =
        ((ws.map (fun u => (w0.getD u false).toNat)).sum + c.toNat) / 2) := by
  induction hlen : ws.length using Nat.strongRecOn generalizing ws gs with
  | _ len ih =>
    match ws with
    | [] =>
      subst hlen
      simp only [reduceCol, List.length_nil]
      refine ⟨by simp, by cases c <;> decide, ⟨[], by simp⟩, hRB, hL, by simp, ?_⟩
      intro x _; cases c <;> simp
    | [a] =>
      subst hlen
      cases c
      · simp only [reduceCol, Bool.false_eq_true, ite_false, List.length_nil, List.length_singleton]
        refine ⟨by omega, by decide, ⟨[], by simp⟩, hRB, hL, by simp, ?_⟩
        intro x _
        simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, add_zero, Bool.toNat_false]
        cases (Circuit.wires ⟨gs, 0⟩ x).getD a false <;> decide
      · simp only [reduceCol, ite_true, List.length_singleton]
        refine ⟨le_refl _, by decide, ⟨[], by simp⟩, hRB, hL, hws, ?_⟩
        intro x _
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Bool.toNat_true]
        cases (Circuit.wires ⟨gs, 0⟩ x).getD a false <;> decide
    | [a, b] =>
      subst hlen
      have ha : a < n + gs.length := hws a (by simp)
      have hb : b < n + gs.length := hws b (by simp)
      cases c
      · simp only [reduceCol, Bool.false_eq_true, ite_false, List.length_cons, List.length_nil]
        have hs := mkAndLegal_spec n a b gs ha hb hRB hL
        dsimp only at hs
        rcases hs with ⟨hc, hex, hRB1, hL1, hw1, hev1⟩
        refine ⟨by omega, by decide, hex, hRB1, hL1,
          by intro w hw; simp at hw; subst hw; exact hw1, ?_⟩
        intro x hx
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Bool.toNat_false]
        rw [hev1 x hx]
        cases (Circuit.wires ⟨gs, 0⟩ x).getD a false <;>
        cases (Circuit.wires ⟨gs, 0⟩ x).getD b false <;> decide
      · simp only [reduceCol, ite_true, List.length_cons, List.length_nil]
        have hs := mkOrLegal_spec n a b gs ha hb hRB hL
        dsimp only at hs
        rcases hs with ⟨hc, hex, hRB1, hL1, hw1, hev1⟩
        refine ⟨by omega, by decide, hex, hRB1, hL1,
          by intro w hw; simp at hw; subst hw; exact hw1, ?_⟩
        intro x hx
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Bool.toNat_true]
        rw [hev1 x hx]
        cases (Circuit.wires ⟨gs, 0⟩ x).getD a false <;>
        cases (Circuit.wires ⟨gs, 0⟩ x).getD b false <;> decide
    | a :: b :: d :: rest =>
      subst hlen
      have ha : a < n + gs.length := hws a (by simp)
      have hb : b < n + gs.length := hws b (by simp)
      have hd : d < n + gs.length := hws d (by simp)
      have hfa_s := mkFALegal_spec n a b d gs ha hb hd hRB hL
      dsimp only at hfa_s
      set r := mkFALegal n a b d gs
      rcases hfa_s with ⟨hc1, ⟨e1, he1⟩, hRB1, hL1, hs1, hcar1, hev1⟩
      have hlen1 : gs.length ≤ r.1.length := by rw [he1]; simp
      have hws1 : ∀ w ∈ r.2.1 :: rest, w < n + r.1.length := by
        intro w hw
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hmem
        · exact hs1
        · have := hws w (by simp [hmem]); omega
      have hrec := ih (r.2.1 :: rest).length (by simp) (r.2.1 :: rest) r.1 hws1 hRB1 hL1 rfl
      dsimp only at hrec
      set rr := reduceCol n c (r.2.1 :: rest) r.1
      rcases hrec with ⟨hc2, hlen2, ⟨e2, he2⟩, hRB2, hL2, hlt2, hev2⟩
      have hlen2_le : r.1.length ≤ rr.1.length := by rw [he2]; simp
      have heq_def : reduceCol n c (a :: b :: d :: rest) gs = (rr.1, r.2.2 :: rr.2) := by
        rw [reduceCol]
      rw [heq_def]
      refine ⟨?_, ?_, ⟨e1 ++ e2, by rw [he2, he1, List.append_assoc]⟩, hRB2, hL2, ?_, ?_⟩
      · have hcost_r : andCost r.1 = andCost gs + 1 := hc1
        have hcost_rr : andCost rr.1 + rr.2.length ≤ andCost r.1 + (rest.length + 1) := by
          simpa only [List.length_cons] using hc2
        simp only [List.length_cons]
        omega
      · have hlen_rr : rr.2.length = (rest.length + 1 + c.toNat) / 2 := by
          simpa only [List.length_cons] using hlen2
        simp only [List.length_cons]
        omega
      · intro w hw
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hmem
        · exact lt_of_lt_of_le hcar1 (Nat.add_le_add_left hlen2_le n)
        · exact hlt2 w hmem
      · intro x hx
        have hpre1 : ∀ u < n + gs.length,
            (Circuit.wires ⟨r.1, 0⟩ x).getD u false = (Circuit.wires ⟨gs, 0⟩ x).getD u false := by
          intro u hu
          rw [he1]
          exact circuit_wires_append_prefix gs e1 0 0 x u (by omega)
        have hpre2 : ∀ u < n + r.1.length,
            (Circuit.wires ⟨rr.1, 0⟩ x).getD u false = (Circuit.wires ⟨r.1, 0⟩ x).getD u false := by
          intro u hu
          rw [he2]
          exact circuit_wires_append_prefix r.1 e2 0 0 x u (by omega)
        simp only [List.map_cons, List.sum_cons]
        rw [hpre2 r.2.2 hcar1, hev2 x hx]
        have hrest_map : rest.map (fun u => ((Circuit.wires ⟨r.1, 0⟩ x).getD u false).toNat) =
            rest.map (fun u => ((Circuit.wires ⟨gs, 0⟩ x).getD u false).toNat) := by
          refine List.map_congr_left (fun u hu => ?_)
          rw [hpre1 u (hws u (by simp [hu]))]
        simp only [List.map_cons, List.sum_cons, hrest_map]
        have hfa := hev1 x hx
        omega

def reduceCols (n : ℕ) (Cconst : ℕ) : ℕ → ℕ → List ℕ → List Gate → List Gate × List ℕ
  | 0, _, ws, gs => (gs, ws)
  | rem + 1, bitIdx, ws, gs =>
    let r := reduceCol n (Cconst.testBit bitIdx) ws gs
    reduceCols n Cconst rem (bitIdx + 1) r.2 r.1

lemma reduceCols_spec (n Cconst : ℕ) :
    ∀ (steps bitIdx : ℕ) (ws : List ℕ) (gs : List Gate),
      (∀ w ∈ ws, w < n + gs.length) →
      ReadsBack n ⟨gs, 0⟩ →
      (∀ g ∈ gs, LegalGate g) →
      let res := reduceCols n Cconst steps bitIdx ws gs
      andCost res.1 + res.2.length ≤ andCost gs + ws.length ∧
      res.2.length = (ws.length + (Cconst / 2 ^ bitIdx) % 2 ^ steps) / 2 ^ steps ∧
      (∃ extra, res.1 = gs ++ extra) ∧
      ReadsBack n ⟨res.1, 0⟩ ∧
      (∀ g ∈ res.1, LegalGate g) ∧
      (∀ w ∈ res.2, w < n + res.1.length) ∧
      (∀ x : List Bool, x.length = n →
        let w0 := Circuit.wires ⟨gs, 0⟩ x
        let w1 := Circuit.wires ⟨res.1, 0⟩ x
        (res.2.map (fun u => (w1.getD u false).toNat)).sum =
          ((ws.map (fun u => (w0.getD u false).toNat)).sum + (Cconst / 2 ^ bitIdx) % 2 ^ steps) /
            2 ^ steps) := by
  intro steps
  induction steps with
  | zero =>
    intro bitIdx ws gs hws hRB hL
    refine ⟨le_refl _, by simp [reduceCols, Nat.mod_one], ⟨[], by simp [reduceCols]⟩, hRB, hL, hws, ?_⟩
    intro x _
    simp [reduceCols, Nat.mod_one]
  | succ s ih =>
    intro bitIdx ws gs hws hRB hL
    have hr_s := reduceCol_spec n (Cconst.testBit bitIdx) ws gs hws hRB hL
    dsimp only at hr_s
    set r := reduceCol n (Cconst.testBit bitIdx) ws gs
    rcases hr_s with ⟨hc1, hlen1, ⟨e1, he1⟩, hRB1, hL1, hlt1, hev1⟩
    have hih := ih (bitIdx + 1) r.2 r.1 hlt1 hRB1 hL1
    dsimp only at hih
    rcases hih with ⟨hc2, hlen2, ⟨e2, he2⟩, hRB2, hL2, hlt2, hev2⟩
    have hbit : (Cconst.testBit bitIdx).toNat = (Cconst / 2 ^ bitIdx) % 2 := by
      rw [testBit_eq_mod2]
      have hlt : (Cconst / 2 ^ bitIdx) % 2 < 2 := Nat.mod_lt _ (by norm_num)
      by_cases h1 : (Cconst / 2 ^ bitIdx) % 2 = 1
      · simp [h1]
      · have h0 : (Cconst / 2 ^ bitIdx) % 2 = 0 := by omega
        simp [h0]
    have hdiv_combine : ∀ (A : ℕ),
        ((A + (Cconst / 2 ^ bitIdx) % 2) / 2 + (Cconst / 2 ^ (bitIdx + 1)) % 2 ^ s) / 2 ^ s =
          (A + (Cconst / 2 ^ bitIdx) % 2 ^ (s + 1)) / 2 ^ (s + 1) := by
      intro A
      let Q := Cconst / 2 ^ bitIdx
      have hQ1 : Cconst / 2 ^ (bitIdx + 1) = Q / 2 := by
        simp only [Q, pow_succ, Nat.div_div_eq_div_mul]
      rw [hQ1]
      have hmod_split : Q % 2 ^ (s + 1) = Q % 2 + 2 * ((Q / 2) % 2 ^ s) := by
        have hpos : 0 < 2 ^ s := by positivity
        have hlt2 : Q % 2 < 2 := Nat.mod_lt Q (by norm_num)
        have hlt_s : (Q / 2) % 2 ^ s < 2 ^ s := Nat.mod_lt (Q / 2) hpos
        have hrem_lt : Q % 2 + 2 * ((Q / 2) % 2 ^ s) < 2 ^ (s + 1) := by
          rw [pow_succ']; omega
        have hdecomp : Q = 2 ^ (s + 1) * ((Q / 2) / 2 ^ s) + (Q % 2 + 2 * ((Q / 2) % 2 ^ s)) := by
          have h1 := Nat.div_add_mod Q 2
          have h2 := Nat.div_add_mod (Q / 2) (2 ^ s)
          rw [pow_succ']
          linarith
        conv_lhs => rw [hdecomp]
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrem_lt]
      rw [hmod_split, pow_succ', ← Nat.div_div_eq_div_mul]
      have hdiv2 : (A + (Q % 2 + 2 * (Q / 2 % 2 ^ s))) / 2 =
          (A + Q % 2) / 2 + Q / 2 % 2 ^ s := by omega
      rw [hdiv2]
    refine ⟨?_, ?_,
      ⟨e1 ++ e2, by simp only [reduceCols]; rw [he2, he1, List.append_assoc]⟩,
      hRB2, hL2, hlt2, ?_⟩
    · change andCost (reduceCols n Cconst s (bitIdx + 1) r.2 r.1).1 +
        (reduceCols n Cconst s (bitIdx + 1) r.2 r.1).2.length ≤ andCost gs + ws.length
      have h1 : andCost r.1 + r.2.length ≤ andCost gs + ws.length := hc1
      have h2 : andCost (reduceCols n Cconst s (bitIdx + 1) r.2 r.1).1 +
          (reduceCols n Cconst s (bitIdx + 1) r.2 r.1).2.length ≤ andCost r.1 + r.2.length := hc2
      omega
    · simp only [reduceCols]
      rw [hlen2, hlen1, hbit, hdiv_combine]
    · intro x hx
      simp only [reduceCols]
      rw [hev2 x hx, hev1 x hx, hbit, hdiv_combine]

lemma exists_exact_maj_circuit (k m : ℕ) (v : Fin m → Fin k → F2)
    (J : Finset (Fin m)) (hJ : 1 ≤ J.card) :
    let maj := fun x : Fin k → F2 => decide
      (J.card ≤ 2 * (J.filter (fun j => dotProduct x (v j) = 1)).card)
    let legal := fun (C : Circuit) =>
      ReadsBack k C ∧ (∀ z ∈ C.gates, LegalGate z)
    let cost := fun (C : Circuit) => andCost C.gates
    let bit := fun (C : Circuit) (x : Fin k → F2) =>
      C.eval (List.ofFn (fun i : Fin k => decide (x i = 1)))
    ∃ H, legal H ∧ H.output < k + H.size ∧ cost H ≤ J.card - 1 ∧ ∀ x, bit H x = maj x := by
  intro maj legal cost bit
  let buildParities : List (Fin m) → List Gate → List Gate × List ℕ := fun L gs =>
    L.foldl (fun st j =>
      let r := buildParityWire k (v j) st.1
      (r.1, st.2 ++ [r.2])) (gs, [])
  have hbp : ∀ (L : List (Fin m)),
      let res := buildParities L []
      andCost res.1 = 0 ∧
      res.2.length = L.length ∧
      ReadsBack k ⟨res.1, 0⟩ ∧
      (∀ g ∈ res.1, LegalGate g) ∧
      (∀ w ∈ res.2, w < k + res.1.length) ∧
      (∀ (y : Fin k → F2),
        let x := List.ofFn (fun i : Fin k => decide (y i = 1))
        (res.2.map (fun u => ((Circuit.wires ⟨res.1, 0⟩ x).getD u false).toNat)).sum =
          (L.map (fun j => (decide (dotProduct y (v j) = 1)).toNat)).sum) := by
    intro L
    have hgen : ∀ (L : List (Fin m)) (st : List Gate × List ℕ),
        andCost st.1 = 0 →
        ReadsBack k ⟨st.1, 0⟩ →
        (∀ g ∈ st.1, LegalGate g) →
        (∀ w ∈ st.2, w < k + st.1.length) →
        let res := L.foldl (fun p j =>
          let r := buildParityWire k (v j) p.1
          (r.1, p.2 ++ [r.2])) st
        andCost res.1 = 0 ∧
        res.2.length = st.2.length + L.length ∧
        (∃ e, res.1 = st.1 ++ e) ∧
        ReadsBack k ⟨res.1, 0⟩ ∧
        (∀ g ∈ res.1, LegalGate g) ∧
        (∀ w ∈ res.2, w < k + res.1.length) ∧
        (∀ y : Fin k → F2,
          let x := List.ofFn (fun i : Fin k => decide (y i = 1))
          (res.2.map (fun u => ((Circuit.wires ⟨res.1, 0⟩ x).getD u false).toNat)).sum =
            (st.2.map (fun u => ((Circuit.wires ⟨st.1, 0⟩ x).getD u false).toNat)).sum +
            (L.map (fun j => (decide (dotProduct y (v j) = 1)).toNat)).sum) := by
      intro L
      induction L with
      | nil =>
        intro st hc hRB hL hlt
        exact ⟨hc, by simp, ⟨[], by simp⟩, hRB, hL, hlt, fun _ => by simp⟩
      | cons j js ih =>
        intro st hc hRB hL hlt
        have hr_s := buildParityWire_spec k (v j) st.1 hRB hL
        dsimp only at hr_s
        set r := buildParityWire k (v j) st.1
        rcases hr_s with ⟨hcr, ⟨er, her⟩, hRBr, hLr, hwr, hevr⟩
        have hlenr : st.1.length ≤ r.1.length := by rw [her]; simp
        have hltr : ∀ w ∈ st.2 ++ [r.2], w < k + r.1.length := by
          intro w hw
          simp only [List.mem_append, List.mem_singleton] at hw
          rcases hw with h | rfl
          · have := hlt w h; omega
          · exact hwr
        have hih := ih (r.1, st.2 ++ [r.2]) (by rw [hcr, hc]) hRBr hLr hltr
        dsimp only at hih
        rcases hih with ⟨hc2, hlen2, ⟨e2, he2⟩, hRB2, hL2, hlt2, hev2⟩
        simp only [List.foldl_cons]
        refine ⟨hc2, ?_, ⟨er ++ e2, by rw [he2, her, List.append_assoc]⟩, hRB2, hL2, hlt2, ?_⟩
        · change (List.foldl (fun p j => let r := buildParityWire k (v j) p.1; (r.1, p.2 ++ [r.2]))
            (r.1, st.2 ++ [r.2]) js).2.length = st.2.length + (j :: js).length
          rw [hlen2]
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        intro y
        let x := List.ofFn (fun i : Fin k => decide (y i = 1))
        have hxlen : x.length = k := by simp [x]
        simp only [List.foldl_cons, List.map_cons, List.sum_cons]
        rw [hev2 y]
        have hmap_pre : st.2.map (fun u => ((Circuit.wires ⟨r.1, 0⟩ (List.ofFn (fun i : Fin k => decide (y i = 1)))).getD u false).toNat) =
            st.2.map (fun u => ((Circuit.wires ⟨st.1, 0⟩ (List.ofFn (fun i : Fin k => decide (y i = 1)))).getD u false).toNat) := by
          refine List.map_congr_left (fun u hu => ?_)
          have hpre : (Circuit.wires ⟨r.1, 0⟩ x).getD u false =
              (Circuit.wires ⟨st.1, 0⟩ x).getD u false := by
            rw [her]
            exact circuit_wires_append_prefix st.1 er 0 0 x u (by rw [hxlen]; exact hlt u hu)
          exact congrArg Bool.toNat hpre
        simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero, hmap_pre, hevr y]
        ring
    rcases hgen L ([], []) rfl (by intro j hj; simp at hj) (by intro g hg; simp at hg)
      (by intro w hw; simp at hw) with ⟨hc, hlen, _, hRB, hL, hlt, hev⟩
    exact ⟨hc, by simpa using hlen, hRB, hL, hlt, fun y => by simpa using hev y⟩
  let Jlist := J.toList
  have hJlen : Jlist.length = J.card := Finset.length_toList J
  have hbp_s := hbp Jlist
  set pRes := buildParities Jlist []
  rcases hbp_s with ⟨hpc, hplen, hpRB, hpL, hplt, hpev⟩
  let N := J.card
  let T := (N + 1) / 2
  have hT_le : T ≤ N := by omega
  have hT_pos : 1 ≤ T := by omega
  let L := N
  have hN_lt : N < 2 ^ L := Nat.lt_two_pow_self
  have h2L_pos : 0 < 2 ^ L := by positivity
  let Cconst := 2 ^ L - T
  have hC_lt : Cconst < 2 ^ L := by omega
  have hcr_s := reduceCols_spec k Cconst L 0 pRes.2 pRes.1 hplt hpRB hpL
  set cRes := reduceCols k Cconst L 0 pRes.2 pRes.1
  rcases hcr_s with ⟨hcc, hclen, _, hcRB, hcL, hclt, hcev⟩
  have hdiv_eq_one : ∀ a : ℕ, 2 ^ L ≤ a → a < 2 * 2 ^ L → a / 2 ^ L = 1 := by
    intro a hlo hhi
    have h1 : 1 ≤ a / 2 ^ L := (Nat.le_div_iff_mul_le h2L_pos).mpr (by omega)
    have h2 : a / 2 ^ L < 2 := (Nat.div_lt_iff_lt_mul h2L_pos).mpr (by omega)
    omega
  have hclen_eq : cRes.2.length = 1 := by
    rw [hclen, hplen, hJlen, pow_zero, Nat.div_one, Nat.mod_eq_of_lt hC_lt]
    exact hdiv_eq_one (N + Cconst) (by omega) (by omega)
  have hcost_le : andCost cRes.1 ≤ N - 1 := by
    rw [hclen_eq, hpc, hplen, hJlen] at hcc
    omega
  obtain ⟨outW, hout_eq⟩ : ∃ outW, cRes.2 = [outW] := by
    cases h : cRes.2 with
    | nil => rw [h] at hclen_eq; simp at hclen_eq
    | cons a as =>
      cases as with
      | nil => exact ⟨a, rfl⟩
      | cons b bs => rw [h] at hclen_eq; simp at hclen_eq
  let H : Circuit := ⟨cRes.1, outW⟩
  refine ⟨H, ⟨hcRB, hcL⟩, hclt outW (by rw [hout_eq]; simp), hcost_le, ?_⟩
  intro y
  let x := List.ofFn (fun i : Fin k => decide (y i = 1))
  have hxlen : x.length = k := by simp [x]
  have hsum_y := hcev x hxlen
  rw [hout_eq] at hsum_y
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    pow_zero, Nat.div_one, Nat.mod_eq_of_lt hC_lt] at hsum_y
  rw [hpev y] at hsum_y
  have hcnt : (Jlist.map (fun j => (decide (dotProduct y (v j) = 1)).toNat)).sum =
      (J.filter (fun j => dotProduct y (v j) = 1)).card := by
    have hnodup : Jlist.Nodup := Finset.nodup_toList J
    have h := List.sum_toFinset (fun j => (decide (dotProduct y (v j) = 1)).toNat) hnodup
    have hto : Jlist.toFinset = J := by ext z; simp [Jlist]
    rw [hto] at h
    rw [← h]
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with hp <;> simp [hp]
  rw [hcnt] at hsum_y
  let cnt := (J.filter (fun j => dotProduct y (v j) = 1)).card
  have hcnt_le : cnt ≤ N := Finset.card_filter_le _ _
  change (Circuit.wires ⟨cRes.1, 0⟩ x).getD outW false = decide (N ≤ 2 * cnt)
  have hiff : N ≤ 2 * cnt ↔ T ≤ cnt := by omega
  by_cases hcond : N ≤ 2 * cnt
  · have hTcnt : T ≤ cnt := hiff.mp hcond
    have hdiv1 : (cnt + Cconst) / 2 ^ L = 1 := hdiv_eq_one (cnt + Cconst) (by omega) (by omega)
    rw [hdiv1] at hsum_y
    simp only [hcond, decide_true]
    cases hval : (Circuit.wires ⟨cRes.1, 0⟩ x).getD outW false
    · rw [hval] at hsum_y; simp at hsum_y
    · rfl
  · have hTcnt : cnt < T := by omega
    have hdiv0 : (cnt + Cconst) / 2 ^ L = 0 := Nat.div_eq_of_lt (by omega)
    rw [hdiv0] at hsum_y
    simp only [hcond, decide_false]
    cases hval : (Circuit.wires ⟨cRes.1, 0⟩ x).getD outW false
    · rfl
    · rw [hval] at hsum_y; simp at hsum_y

lemma holder_124_int {α : Type*} (S : Finset α) (f : α → ℤ) :
    (∑ x ∈ S, f x ^ 2) ^ 3 ≤ (∑ x ∈ S, |f x|) ^ 2 * (∑ x ∈ S, f x ^ 4) := by
  let a : α → ℤ := fun x => |f x|
  have ha : ∀ x, 0 ≤ a x := fun x => abs_nonneg (f x)
  have hsq : ∀ x, f x ^ 2 = a x ^ 2 := fun x => (sq_abs (f x)).symm
  have hq : ∀ x, f x ^ 4 = a x ^ 4 := fun x => by
    have : f x ^ 4 = (f x ^ 2) ^ 2 := by ring
    rw [this, hsq]; ring
  simp_rw [hsq, hq]
  let s1 := ∑ x ∈ S, a x
  let s2 := ∑ x ∈ S, a x ^ 2
  let s3 := ∑ x ∈ S, a x ^ 3
  let s4 := ∑ x ∈ S, a x ^ 4
  have h13 : s2 ^ 2 ≤ s1 * s3 := by
    have hnn : 0 ≤ ∑ x ∈ S, ∑ y ∈ S, a x * a y * (a x - a y) ^ 2 :=
      Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ =>
        mul_nonneg (mul_nonneg (ha x) (ha y)) (sq_nonneg _)))
    have hexp : (∑ x ∈ S, ∑ y ∈ S, a x * a y * (a x - a y) ^ 2) = 2 * (s1 * s3 - s2 ^ 2) := by
      have hterm : ∀ x y, a x * a y * (a x - a y) ^ 2 =
          a x ^ 3 * a y + a x * a y ^ 3 - 2 * (a x ^ 2 * a y ^ 2) := fun x y => by ring
      simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul]
      simp only [s1, s2, s3]
      ring
    linarith
  have h24 : s3 ^ 2 ≤ s2 * s4 := by
    have hnn : 0 ≤ ∑ x ∈ S, ∑ y ∈ S, a x ^ 2 * a y ^ 2 * (a x - a y) ^ 2 :=
      Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ =>
        mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)))
    have hexp : (∑ x ∈ S, ∑ y ∈ S, a x ^ 2 * a y ^ 2 * (a x - a y) ^ 2) = 2 * (s2 * s4 - s3 ^ 2) := by
      have hterm : ∀ x y, a x ^ 2 * a y ^ 2 * (a x - a y) ^ 2 =
          a x ^ 4 * a y ^ 2 + a x ^ 2 * a y ^ 4 - 2 * (a x ^ 3 * a y ^ 3) := fun x y => by ring
      simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul]
      simp only [s2, s3, s4]
      ring
    linarith
  have hs1 : 0 ≤ s1 := Finset.sum_nonneg (fun x _ => ha x)
  have hs2 : 0 ≤ s2 := Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have hs3 : 0 ≤ s3 := Finset.sum_nonneg (fun x _ => pow_nonneg (ha x) 3)
  change s2 ^ 3 ≤ s1 ^ 2 * s4
  by_cases hs2z : s2 = 0
  · rw [hs2z]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun x _ => pow_nonneg (ha x) 4))
  · have hs2pos : 0 < s2 := lt_of_le_of_ne hs2 (Ne.symm hs2z)
    have hchain : s2 * s2 ^ 3 ≤ s2 * (s1 ^ 2 * s4) := by
      calc
        s2 * s2 ^ 3 = (s2 ^ 2) ^ 2 := by ring
        _ ≤ (s1 * s3) ^ 2 := by nlinarith
        _ = s1 ^ 2 * s3 ^ 2 := by ring
        _ ≤ s1 ^ 2 * (s2 * s4) := mul_le_mul_of_nonneg_left h24 (sq_nonneg _)
        _ = s2 * (s1 ^ 2 * s4) := by ring
    exact le_of_mul_le_mul_left hchain hs2pos

lemma cauchy_schwarz_int {α : Type*} (S : Finset α) (f : α → ℤ) :
    (∑ x ∈ S, f x) ^ 2 ≤ (S.card : ℤ) * (∑ x ∈ S, f x ^ 2) := by
  have hnn : 0 ≤ ∑ x ∈ S, ∑ y ∈ S, (f x - f y) ^ 2 :=
    Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => sq_nonneg _))
  have hexp : (∑ x ∈ S, ∑ y ∈ S, (f x - f y) ^ 2) =
      2 * ((S.card : ℤ) * (∑ x ∈ S, f x ^ 2) - (∑ x ∈ S, f x) ^ 2) := by
    have hterm : ∀ x y, (f x - f y) ^ 2 = f x ^ 2 + f y ^ 2 - 2 * (f x * f y) := fun x y => by ring
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul]
    have hc1 : (∑ x ∈ S, ∑ _y ∈ S, f x ^ 2) = (S.card : ℤ) * (∑ x ∈ S, f x ^ 2) := by
      simp [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    have hc2 : (∑ _x ∈ S, ∑ y ∈ S, f y ^ 2) = (S.card : ℤ) * (∑ y ∈ S, f y ^ 2) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hc1, hc2]
    ring
  linarith

lemma maj_gain_lower_bound {d m : ℕ} (J : Finset (Fin m)) (u : Fin m → Fin d → F2)
    (c0 : Fin m → F2)
    (h4wise : ∀ S : Finset (Fin m), 1 ≤ S.card → S.card ≤ 4 → (∑ j ∈ S, u j) ≠ 0) :
    let majBit : (Fin d → F2) → Bool := fun y =>
      decide (J.card ≤ 2 * (J.filter (fun j => dotProduct y (u j) + c0 j = 1)).card)
    let majGain : ℤ :=
      2 * (∑ y : Fin d → F2, ((J.filter (fun j => majBit y = decide (dotProduct y (u j) + c0 j = 1))).card : ℤ)) -
        (2 ^ d : ℤ) * (J.card : ℤ)
    0 ≤ majGain ∧ ((2 ^ d : ℤ) ^ 2 * (J.card : ℤ) ≤ 3 * majGain ^ 2) := by
  intro majBit majGain
  let Z : (Fin d → F2) → Fin m → ℤ := fun y j => chi (dotProduct y (u j) + c0 j)
  let S : (Fin d → F2) → ℤ := fun y => ∑ j ∈ J, Z y j
  have hgain_eq : majGain = ∑ y : Fin d → F2, |S y| := by
    have hper : ∀ y : Fin d → F2,
        2 * ((J.filter (fun j => majBit y = decide (dotProduct y (u j) + c0 j = 1))).card : ℤ) -
          (J.card : ℤ) = |S y| := by
      intro y
      let J1 := J.filter (fun j => dotProduct y (u j) + c0 j = 1)
      let J0 := J.filter (fun j => dotProduct y (u j) + c0 j ≠ 1)
      have hsumJ : J1.card + J0.card = J.card := Finset.card_filter_add_card_filter_not _
      have hSy : S y = (J0.card : ℤ) - (J1.card : ℤ) := by
        simp only [S, Z, chi]
        rw [← Finset.sum_filter_add_sum_filter_not J (fun j => dotProduct y (u j) + c0 j = 1)]
        have h1 : (∑ j ∈ J1, if dotProduct y (u j) + c0 j = 1 then (-1 : ℤ) else 1) = -(J1.card : ℤ) := by
          have hcon : ∀ j ∈ J1, (if dotProduct y (u j) + c0 j = 1 then (-1 : ℤ) else 1) = -1 := by
            intro j hj; simp [(Finset.mem_filter.mp hj).2]
          rw [Finset.sum_congr rfl hcon, Finset.sum_const, nsmul_eq_mul]
          ring
        have h0 : (∑ j ∈ J0, if dotProduct y (u j) + c0 j = 1 then (-1 : ℤ) else 1) = (J0.card : ℤ) := by
          have hcon : ∀ j ∈ J0, (if dotProduct y (u j) + c0 j = 1 then (-1 : ℤ) else 1) = 1 := by
            intro j hj; simp [(Finset.mem_filter.mp hj).2]
          rw [Finset.sum_congr rfl hcon, Finset.sum_const, nsmul_eq_mul, mul_one]
        change (∑ j ∈ J1, _) + (∑ j ∈ J0, _) = _
        rw [h1, h0]
        ring
      by_cases hm : J.card ≤ 2 * J1.card
      · have hmb : majBit y = true := by simp [majBit, J1, hm]
        have hf : J.filter (fun j => majBit y = decide (dotProduct y (u j) + c0 j = 1)) = J1 := by
          ext j; simp [hmb, J1]
        rw [hf, hSy]
        have hle : (J0.card : ℤ) - (J1.card : ℤ) ≤ 0 := by omega
        rw [abs_of_nonpos hle]
        omega
      · have hmb : majBit y = false := by simp [majBit, J1, hm]
        have hf : J.filter (fun j => majBit y = decide (dotProduct y (u j) + c0 j = 1)) = J0 := by
          ext j; simp [hmb, J0]
        rw [hf, hSy]
        have hge : 0 ≤ (J0.card : ℤ) - (J1.card : ℤ) := by omega
        rw [abs_of_nonneg hge]
        omega
    have hcard_univ : (Finset.univ : Finset (Fin d → F2)).card = 2 ^ d := by
      simp [Fintype.card_fun, ZMod.card]
    calc
      majGain = (∑ y : Fin d → F2,
          (2 * ((J.filter (fun j => majBit y = decide (dotProduct y (u j) + c0 j = 1))).card : ℤ) -
            (J.card : ℤ))) := by
        simp only [majGain, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
          hcard_univ, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      _ = ∑ y : Fin d → F2, |S y| := Finset.sum_congr rfl (fun y _ => hper y)
  have hS2 : (∑ y : Fin d → F2, S y ^ 2) = (2 ^ d : ℤ) * (J.card : ℤ) := by
    have hsq : ∀ y, S y ^ 2 = ∑ j₁ ∈ J, ∑ j₂ ∈ J, Z y j₁ * Z y j₂ := by
      intro y
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j₁ _ => Finset.mul_sum J (fun j₂ => Z y j₂) (Z y j₁))
    simp_rw [hsq]
    rw [Finset.sum_comm]
    have hswap : (∑ j₁ ∈ J, ∑ y : Fin d → F2, ∑ j₂ ∈ J, Z y j₁ * Z y j₂) =
        ∑ j₁ ∈ J, ∑ j₂ ∈ J, ∑ y : Fin d → F2, Z y j₁ * Z y j₂ :=
      Finset.sum_congr rfl (fun j₁ _ => Finset.sum_comm)
    rw [hswap]
    have hpair : ∀ j₁ ∈ J, ∀ j₂ ∈ J,
        (∑ y : Fin d → F2, Z y j₁ * Z y j₂) = if j₁ = j₂ then (2 ^ d : ℤ) else 0 := by
      intro j₁ _ j₂ _
      have hprod : ∀ y, Z y j₁ * Z y j₂ =
          chi (c0 j₁ + c0 j₂) * chi (dotProduct y (u j₁ + u j₂)) := by
        intro y
        simp only [Z, ← chi_add, dotProduct_add_right]
        congr 1; ring
      simp_rw [hprod, ← Finset.mul_sum, sum_chi_dotProduct]
      by_cases heq : j₁ = j₂
      · subst heq
        have hu0 : u j₁ + u j₁ = 0 := by ext r; exact zmod2_add_self _
        have hc0 : c0 j₁ + c0 j₁ = 0 := zmod2_add_self _
        simp [hu0, hc0, chi_zero]
      · have hne : u j₁ + u j₂ ≠ 0 := by
          have h := h4wise {j₁, j₂} (by rw [Finset.card_pair heq]; omega) (by rw [Finset.card_pair heq]; omega)
          rwa [Finset.sum_pair heq] at h
        simp [heq, hne]
    calc
      (∑ j₁ ∈ J, ∑ j₂ ∈ J, ∑ y : Fin d → F2, Z y j₁ * Z y j₂)
          = ∑ j₁ ∈ J, ∑ j₂ ∈ J, (if j₁ = j₂ then (2 ^ d : ℤ) else 0) :=
            Finset.sum_congr rfl (fun j₁ hj₁ => Finset.sum_congr rfl (fun j₂ hj₂ => hpair j₁ hj₁ j₂ hj₂))
      _ = ∑ j₁ ∈ J, (2 ^ d : ℤ) := by
            refine Finset.sum_congr rfl (fun j₁ hj₁ => ?_)
            simp [hj₁]
      _ = (2 ^ d : ℤ) * (J.card : ℤ) := by simp [mul_comm]
  have hS4 : (∑ y : Fin d → F2, S y ^ 4) ≤ 3 * (2 ^ d : ℤ) * (J.card : ℤ) ^ 2 := by
    have hq : ∀ y, S y ^ 4 =
        ∑ j₁ ∈ J, ∑ j₂ ∈ J, ∑ j₃ ∈ J, ∑ j₄ ∈ J, Z y j₁ * Z y j₂ * Z y j₃ * Z y j₄ := by
      intro y
      have h4 : S y ^ 4 = S y * (S y * (S y * S y)) := by ring
      rw [h4]
      simp only [S]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j₁ _ => ?_)
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j₂ _ => ?_)
      rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j₃ _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j₄ _ => by ring)
    simp_rw [hq]
    rw [Finset.sum_comm]
    have hsw1 : ∀ j₁, (∑ y : Fin d → F2, ∑ j₂ ∈ J, ∑ j₃ ∈ J, ∑ j₄ ∈ J,
        Z y j₁ * Z y j₂ * Z y j₃ * Z y j₄) =
        ∑ j₂ ∈ J, ∑ j₃ ∈ J, ∑ j₄ ∈ J, ∑ y : Fin d → F2,
        Z y j₁ * Z y j₂ * Z y j₃ * Z y j₄ := by
      intro j₁
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j₂ _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j₃ _ => Finset.sum_comm)
    simp_rw [hsw1]
    have hquad : ∀ j₁ ∈ J, ∀ j₂ ∈ J, ∀ j₃ ∈ J, ∀ j₄ ∈ J,
        (∑ y : Fin d → F2, Z y j₁ * Z y j₂ * Z y j₃ * Z y j₄) ≤
          if (j₁ = j₂ ∧ j₃ = j₄) ∨ (j₁ = j₃ ∧ j₂ = j₄) ∨ (j₁ = j₄ ∧ j₂ = j₃) then (2 ^ d : ℤ) else 0 := by
      intro j₁ _ j₂ _ j₃ _ j₄ _
      have hprod : ∀ y, Z y j₁ * Z y j₂ * Z y j₃ * Z y j₄ =
          chi (c0 j₁ + c0 j₂ + c0 j₃ + c0 j₄) * chi (dotProduct y (u j₁ + u j₂ + u j₃ + u j₄)) := by
        intro y
        simp only [Z, ← chi_add, dotProduct_add_right]
        congr 1; ring
      simp_rw [hprod, ← Finset.mul_sum, sum_chi_dotProduct]
      by_cases hmatch : (j₁ = j₂ ∧ j₃ = j₄) ∨ (j₁ = j₃ ∧ j₂ = j₄) ∨ (j₁ = j₄ ∧ j₂ = j₃)
      · rw [if_pos hmatch]
        have hu0 : u j₁ + u j₂ + u j₃ + u j₄ = 0 := by
          rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · ext r; simp only [Pi.add_apply, Pi.zero_apply]; rw [zmod2_add_self, zero_add, zmod2_add_self]
          · ext r; simp only [Pi.add_apply, Pi.zero_apply]
            have : u j₁ r + u j₂ r + u j₁ r + u j₂ r = (u j₁ r + u j₁ r) + (u j₂ r + u j₂ r) := by ring
            rw [this, zmod2_add_self, zmod2_add_self, add_zero]
          · ext r; simp only [Pi.add_apply, Pi.zero_apply]
            have : u j₁ r + u j₂ r + u j₂ r + u j₁ r = (u j₁ r + u j₁ r) + (u j₂ r + u j₂ r) := by ring
            rw [this, zmod2_add_self, zmod2_add_self, add_zero]
        have hc0 : c0 j₁ + c0 j₂ + c0 j₃ + c0 j₄ = 0 := by
          rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [zmod2_add_self, zero_add, zmod2_add_self]
          · have : c0 j₁ + c0 j₂ + c0 j₁ + c0 j₂ = (c0 j₁ + c0 j₁) + (c0 j₂ + c0 j₂) := by ring
            rw [this, zmod2_add_self, zmod2_add_self, add_zero]
          · have : c0 j₁ + c0 j₂ + c0 j₂ + c0 j₁ = (c0 j₁ + c0 j₁) + (c0 j₂ + c0 j₂) := by ring
            rw [this, zmod2_add_self, zmod2_add_self, add_zero]
        simp [hu0, hc0, chi_zero]
      · rw [if_neg hmatch]
        have hne : u j₁ + u j₂ + u j₃ + u j₄ ≠ 0 := by
          let symDiff := Finset.univ.filter (fun j : Fin m =>
            ((if j = j₁ then 1 else 0) + (if j = j₂ then 1 else 0) +
             (if j = j₃ then 1 else 0) + (if j = j₄ then 1 else 0)) % 2 = 1)
          have hsum_sd : (∑ j ∈ symDiff, u j) = u j₁ + u j₂ + u j₃ + u j₄ := by
            ext r
            simp only [Finset.sum_apply, Pi.add_apply]
            have htot : (∑ j : Fin m,
                ((if j = j₁ then (1 : F2) else 0) + (if j = j₂ then 1 else 0) +
                 (if j = j₃ then 1 else 0) + (if j = j₄ then 1 else 0)) * u j r) =
                u j₁ r + u j₂ r + u j₃ r + u j₄ r := by
              simp only [add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
                Finset.sum_ite_eq', Finset.mem_univ, ite_true]
            rw [← htot]
            rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin m =>
              ((if j = j₁ then 1 else 0) + (if j = j₂ then 1 else 0) +
               (if j = j₃ then 1 else 0) + (if j = j₄ then 1 else 0)) % 2 = 1)]
            have hcoef : ∀ j : Fin m,
                ((if j = j₁ then (1 : F2) else 0) + (if j = j₂ then 1 else 0) +
                 (if j = j₃ then 1 else 0) + (if j = j₄ then 1 else 0)) =
                if ((if j = j₁ then 1 else 0) + (if j = j₂ then 1 else 0) +
                    (if j = j₃ then 1 else 0) + (if j = j₄ then 1 else 0)) % 2 = 1 then 1 else 0 := by
              intro j
              have hbool : ∀ a b c e : Bool,
                  (boolToF2 a + boolToF2 b + boolToF2 c + boolToF2 e) =
                  if (a.toNat + b.toNat + c.toNat + e.toNat) % 2 = 1 then (1 : F2) else 0 := by
                decide
              have h1 : ∀ p : Prop, [Decidable p] → (if p then (1 : F2) else 0) = boolToF2 (decide p) := by
                intro p _; by_cases hp : p <;> simp [hp, boolToF2]
              have h2 : ∀ p : Prop, [Decidable p] → (if p then (1 : ℕ) else 0) = (decide p).toNat := by
                intro p _; by_cases hp : p <;> simp [hp]
              rw [h1 (j = j₁), h1 (j = j₂), h1 (j = j₃), h1 (j = j₄),
                  h2 (j = j₁), h2 (j = j₂), h2 (j = j₃), h2 (j = j₄)]
              exact hbool _ _ _ _
            have h0 : (∑ j ∈ Finset.univ.filter (fun j : Fin m =>
                ¬((if j = j₁ then 1 else 0) + (if j = j₂ then 1 else 0) +
                  (if j = j₃ then 1 else 0) + (if j = j₄ then 1 else 0)) % 2 = 1),
                ((if j = j₁ then (1 : F2) else 0) + (if j = j₂ then 1 else 0) +
                 (if j = j₃ then 1 else 0) + (if j = j₄ then 1 else 0)) * u j r) = 0 := by
              refine Finset.sum_eq_zero (fun j hj => ?_)
              rw [hcoef j, if_neg (Finset.mem_filter.mp hj).2, zero_mul]
            rw [h0, add_zero]
            refine Finset.sum_congr rfl (fun j hj => ?_)
            rw [hcoef j, if_pos (Finset.mem_filter.mp hj).2, one_mul]
          have hsub4 : symDiff ⊆ {j₁, j₂, j₃, j₄} := by
            intro j hj
            simp only [symDiff, Finset.mem_filter, Finset.mem_univ, true_and] at hj
            simp only [Finset.mem_insert, Finset.mem_singleton]
            by_contra hnot
            push_neg at hnot
            simp [hnot.1, hnot.2.1, hnot.2.2.1, hnot.2.2.2] at hj
          have hcard_le4 : symDiff.card ≤ 4 := by
            calc
              symDiff.card ≤ ({j₁, j₂, j₃, j₄} : Finset (Fin m)).card := Finset.card_le_card hsub4
              _ ≤ 4 := by
                have := Finset.card_insert_le j₁ {j₂, j₃, j₄}
                have := Finset.card_insert_le j₂ {j₃, j₄}
                have := Finset.card_insert_le j₃ {j₄}
                simp at *
                omega
          have hcard_ge1 : 1 ≤ symDiff.card := by
            by_contra h0
            have hemp : symDiff = ∅ := Finset.card_eq_zero.mp (by omega)
            have hnotmem : ∀ j : Fin m, j ∉ symDiff := fun j => by rw [hemp]; simp
            have h1 := hnotmem j₁
            have h2 := hnotmem j₂
            have h3 := hnotmem j₃
            simp only [symDiff, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2 h3
            by_cases e12 : j₁ = j₂ <;> by_cases e13 : j₁ = j₃ <;> by_cases e14 : j₁ = j₄ <;>
            by_cases e23 : j₂ = j₃ <;> by_cases e24 : j₂ = j₄ <;> by_cases e34 : j₃ = j₄
            all_goals
              try exact hmatch (Or.inl ⟨e12, e34⟩)
              try exact hmatch (Or.inr (Or.inl ⟨e13, e24⟩))
              try exact hmatch (Or.inr (Or.inr ⟨e14, e23⟩))
            all_goals
              simp [e12, e13, e14, e23, e24, e34, Ne.symm] at h1 h2 h3
              try omega
            all_goals
              exfalso
              try exact e13 (e12.trans e23)
              try exact e14 (e12.trans e24)
              try exact e24 (e12.symm.trans e14)
              try exact e23 (e12.symm.trans e13)
              try exact e34 (e13.symm.trans e14)
              try exact e34 (e23.symm.trans e24)
              try exact e14 (e13.trans e34)
              try exact e24 (e23.trans e34)
              try exact e12 (e13.trans e23.symm)
              try exact e12 (e14.trans e24.symm)
              try exact e13 (e14.trans e34.symm)
              try exact e23 (e24.trans e34.symm)
          rw [← hsum_sd]
          exact h4wise symDiff hcard_ge1 hcard_le4
        simp [hne]
    have hle_sum : (∑ j₁ ∈ J, ∑ j₂ ∈ J, ∑ j₃ ∈ J, ∑ j₄ ∈ J,
        ∑ y : Fin d → F2, Z y j₁ * Z y j₂ * Z y j₃ * Z y j₄) ≤
        ∑ j₁ ∈ J, ∑ j₂ ∈ J, ∑ j₃ ∈ J, ∑ j₄ ∈ J,
          ((if j₁ = j₂ ∧ j₃ = j₄ then (2 ^ d : ℤ) else 0) +
           (if j₁ = j₃ ∧ j₂ = j₄ then (2 ^ d : ℤ) else 0) +
           (if j₁ = j₄ ∧ j₂ = j₃ then (2 ^ d : ℤ) else 0)) := by
      refine Finset.sum_le_sum (fun j₁ hj₁ => Finset.sum_le_sum (fun j₂ hj₂ =>
        Finset.sum_le_sum (fun j₃ hj₃ => Finset.sum_le_sum (fun j₄ hj₄ => ?_))))
      calc
        (∑ y : Fin d → F2, Z y j₁ * Z y j₂ * Z y j₃ * Z y j₄)
            ≤ if (j₁ = j₂ ∧ j₃ = j₄) ∨ (j₁ = j₃ ∧ j₂ = j₄) ∨ (j₁ = j₄ ∧ j₂ = j₃) then (2 ^ d : ℤ) else 0 :=
              hquad j₁ hj₁ j₂ hj₂ j₃ hj₃ j₄ hj₄
        _ ≤ (if j₁ = j₂ ∧ j₃ = j₄ then (2 ^ d : ℤ) else 0) +
            (if j₁ = j₃ ∧ j₂ = j₄ then (2 ^ d : ℤ) else 0) +
            (if j₁ = j₄ ∧ j₂ = j₃ then (2 ^ d : ℤ) else 0) := by
              have hpos : (0 : ℤ) ≤ 2 ^ d := by positivity
              have h3or : ∀ (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R],
                  (if P ∨ Q ∨ R then (2 ^ d : ℤ) else 0) ≤
                    (if P then (2 ^ d : ℤ) else 0) + (if Q then (2 ^ d : ℤ) else 0) +
                    (if R then (2 ^ d : ℤ) else 0) := by
                intro P Q R _ _ _
                by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;>
                simp [hP, hQ, hR] <;> linarith
              exact h3or _ _ _
    have hcount1 : (∑ j₁ ∈ J, ∑ j₂ ∈ J, ∑ j₃ ∈ J, ∑ j₄ ∈ J,
        if j₁ = j₂ ∧ j₃ = j₄ then (2 ^ d : ℤ) else 0) = (2 ^ d : ℤ) * (J.card : ℤ) ^ 2 := by
      have hinner : ∀ j₁ ∈ J, (∑ j₂ ∈ J, ∑ j₃ ∈ J, ∑ j₄ ∈ J,
          if j₁ = j₂ ∧ j₃ = j₄ then (2 ^ d : ℤ) else 0) = (2 ^ d : ℤ) * (J.card : ℤ) := by
        intro j₁ hj₁
        have hstep : ∀ j₂ ∈ J, (∑ j₃ ∈ J, ∑ j₄ ∈ J,
            if j₁ = j₂ ∧ j₃ = j₄ then (2 ^ d : ℤ) else 0) =
            if j₁ = j₂ then (2 ^ d : ℤ) * (J.card : ℤ) else 0 := by
          intro j₂ _
          by_cases h12 : j₁ = j₂
          · simp only [h12, true_and, ite_true]
            have : ∀ j₃ ∈ J, (∑ j₄ ∈ J, if j₃ = j₄ then (2 ^ d : ℤ) else 0) = (2 ^ d : ℤ) := by
              intro j₃ hj₃; simp [hj₃]
            rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_comm]
          · simp [h12]
        rw [Finset.sum_congr rfl hstep]
        simp [hj₁]
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
      ring
    have hcount2 : (∑ j₁ ∈ J, ∑ j₂ ∈ J, ∑ j₃ ∈ J, ∑ j₄ ∈ J,
        if j₁ = j₃ ∧ j₂ = j₄ then (2 ^ d : ℤ) else 0) = (2 ^ d : ℤ) * (J.card : ℤ) ^ 2 := by
      have hinner : ∀ j₁ ∈ J, (∑ j₂ ∈ J, ∑ j₃ ∈ J, ∑ j₄ ∈ J,
          if j₁ = j₃ ∧ j₂ = j₄ then (2 ^ d : ℤ) else 0) = (2 ^ d : ℤ) * (J.card : ℤ) := by
        intro j₁ hj₁
        have hstep : ∀ j₂ ∈ J, (∑ j₃ ∈ J, ∑ j₄ ∈ J,
            if j₁ = j₃ ∧ j₂ = j₄ then (2 ^ d : ℤ) else 0) = (2 ^ d : ℤ) := by
          intro j₂ hj₂
          have h3 : ∀ j₃ ∈ J, (∑ j₄ ∈ J, if j₁ = j₃ ∧ j₂ = j₄ then (2 ^ d : ℤ) else 0) =
              if j₁ = j₃ then (2 ^ d : ℤ) else 0 := by
            intro j₃ _
            by_cases h13 : j₁ = j₃ <;> simp [h13, hj₂]
          rw [Finset.sum_congr rfl h3]
          simp [hj₁]
        rw [Finset.sum_congr rfl hstep, Finset.sum_const, nsmul_eq_mul, mul_comm]
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
      ring
    have hcount3 : (∑ j₁ ∈ J, ∑ j₂ ∈ J, ∑ j₃ ∈ J, ∑ j₄ ∈ J,
        if j₁ = j₄ ∧ j₂ = j₃ then (2 ^ d : ℤ) else 0) = (2 ^ d : ℤ) * (J.card : ℤ) ^ 2 := by
      have hinner : ∀ j₁ ∈ J, (∑ j₂ ∈ J, ∑ j₃ ∈ J, ∑ j₄ ∈ J,
          if j₁ = j₄ ∧ j₂ = j₃ then (2 ^ d : ℤ) else 0) = (2 ^ d : ℤ) * (J.card : ℤ) := by
        intro j₁ hj₁
        have hstep : ∀ j₂ ∈ J, (∑ j₃ ∈ J, ∑ j₄ ∈ J,
            if j₁ = j₄ ∧ j₂ = j₃ then (2 ^ d : ℤ) else 0) = (2 ^ d : ℤ) := by
          intro j₂ hj₂
          have h3 : ∀ j₃ ∈ J, (∑ j₄ ∈ J, if j₁ = j₄ ∧ j₂ = j₃ then (2 ^ d : ℤ) else 0) =
              if j₂ = j₃ then (2 ^ d : ℤ) else 0 := by
            intro j₃ _
            by_cases h23 : j₂ = j₃ <;> simp [h23, hj₁]
          rw [Finset.sum_congr rfl h3]
          simp [hj₂]
        rw [Finset.sum_congr rfl hstep, Finset.sum_const, nsmul_eq_mul, mul_comm]
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
      ring
    calc
      (∑ j₁ ∈ J, ∑ j₂ ∈ J, ∑ j₃ ∈ J, ∑ j₄ ∈ J,
          ∑ y : Fin d → F2, Z y j₁ * Z y j₂ * Z y j₃ * Z y j₄)
          ≤ ∑ j₁ ∈ J, ∑ j₂ ∈ J, ∑ j₃ ∈ J, ∑ j₄ ∈ J,
              ((if j₁ = j₂ ∧ j₃ = j₄ then (2 ^ d : ℤ) else 0) +
               (if j₁ = j₃ ∧ j₂ = j₄ then (2 ^ d : ℤ) else 0) +
               (if j₁ = j₄ ∧ j₂ = j₃ then (2 ^ d : ℤ) else 0)) := hle_sum
      _ = (∑ j₁ ∈ J, ∑ j₂ ∈ J, ∑ j₃ ∈ J, ∑ j₄ ∈ J,
              if j₁ = j₂ ∧ j₃ = j₄ then (2 ^ d : ℤ) else 0) +
          (∑ j₁ ∈ J, ∑ j₂ ∈ J, ∑ j₃ ∈ J, ∑ j₄ ∈ J,
              if j₁ = j₃ ∧ j₂ = j₄ then (2 ^ d : ℤ) else 0) +
          (∑ j₁ ∈ J, ∑ j₂ ∈ J, ∑ j₃ ∈ J, ∑ j₄ ∈ J,
              if j₁ = j₄ ∧ j₂ = j₃ then (2 ^ d : ℤ) else 0) := by
            simp only [Finset.sum_add_distrib]
      _ = 3 * (2 ^ d : ℤ) * (J.card : ℤ) ^ 2 := by rw [hcount1, hcount2, hcount3]; ring
  have hnonneg : 0 ≤ majGain := by
    rw [hgain_eq]
    exact Finset.sum_nonneg (fun y _ => abs_nonneg _)
  refine ⟨hnonneg, ?_⟩
  by_cases hJ0 : J.card = 0
  · simp [hJ0]; positivity
  · have hJpos : (0 : ℤ) < J.card := by omega
    have h2pos : (0 : ℤ) < 2 ^ d := by positivity
    have hH := holder_124_int (Finset.univ : Finset (Fin d → F2)) S
    rw [hS2, ← hgain_eq] at hH
    have hchain : ((2 ^ d : ℤ) * (J.card : ℤ)) ^ 3 ≤
        majGain ^ 2 * (3 * (2 ^ d : ℤ) * (J.card : ℤ) ^ 2) :=
      le_trans hH (mul_le_mul_of_nonneg_left hS4 (sq_nonneg _))
    have hfac : ((2 ^ d : ℤ) * (J.card : ℤ) ^ 2) * ((2 ^ d : ℤ) ^ 2 * (J.card : ℤ)) ≤
        ((2 ^ d : ℤ) * (J.card : ℤ) ^ 2) * (3 * majGain ^ 2) := by
      linarith
    exact le_of_mul_le_mul_left hfac (by positivity)

lemma circuit_wire_decomp {k d : ℕ} (x0 : Fin k → F2) (iota : (Fin d → F2) → (Fin k → F2))
    (hiota_add : ∀ y₁ y₂, iota (y₁ + y₂) = iota y₁ + iota y₂)
    (C : Circuit) (hRB : ReadsBack k C) (hL : ∀ g ∈ C.gates, LegalGate g) :
    ∃ (vecs : List (Fin d → F2)) (c : ℕ → F2) (alpha : ℕ → Fin d → F2) (h : ℕ → (Fin d → F2) → F2),
      vecs.length ≤ 2 * andCost C.gates ∧
      (∀ w < k + C.gates.length, ∀ y : Fin d → F2,
        boolToF2 ((Circuit.wires C (List.ofFn (fun i : Fin k => decide ((x0 + iota y) i = 1)))).getD w false) =
          c w + dotProduct (alpha w) y + h w y) ∧
      (∀ w < k + C.gates.length, ∀ y z : Fin d → F2,
        (∀ a ∈ vecs, dotProduct a z = 0) → h w (y + z) = h w y) := by
  have hgen : ∀ (gs : List Gate), ReadsBack k ⟨gs, 0⟩ → (∀ g ∈ gs, LegalGate g) →
      ∃ (vecs : List (Fin d → F2)) (c : ℕ → F2) (alpha : ℕ → Fin d → F2) (h : ℕ → (Fin d → F2) → F2),
        vecs.length ≤ 2 * andCost gs ∧
        (∀ w < k + gs.length, ∀ y : Fin d → F2,
          boolToF2 ((Circuit.wires ⟨gs, 0⟩ (List.ofFn (fun i : Fin k => decide ((x0 + iota y) i = 1)))).getD w false) =
            c w + dotProduct (alpha w) y + h w y) ∧
        (∀ w < k + gs.length, ∀ y z : Fin d → F2,
          (∀ a ∈ vecs, dotProduct a z = 0) → h w (y + z) = h w y) := by
    intro gs
    induction gs using List.reverseRecOn with
    | nil =>
      intro _ _
      let alpha0 : ℕ → Fin d → F2 := fun w r =>
        if hw : w < k then iota (fun j => if j = r then 1 else 0) ⟨w, hw⟩ else 0
      let c0 : ℕ → F2 := fun w => if hw : w < k then x0 ⟨w, hw⟩ else 0
      refine ⟨[], c0, alpha0, fun _ _ => 0, by simp [andCost], ?_, by simp⟩
      intro w hw y
      simp only [List.length_nil, add_zero] at hw
      simp only [Circuit.wires, List.foldl_nil]
      rw [List.getD_eq_getElem _ _ (by simp; exact hw), List.getElem_ofFn, boolToF2_decide]
      simp only [Pi.add_apply, c0, alpha0, dif_pos hw, add_zero]
      congr 1
      have hy_expand : y = ∑ r : Fin d, (if y r = 1 then (fun j : Fin d => if j = r then (1 : F2) else 0) else 0) := by
        ext j
        simp only [Finset.sum_apply]
        have h1 : ∀ r : Fin d, (if y r = 1 then (fun j : Fin d => if j = r then (1 : F2) else 0) else 0) j =
            if r = j then y j else 0 := by
          intro r
          by_cases hrj : r = j
          · subst hrj
            rcases zmod2_eq_zero_or_one (y r) with hr | hr <;> simp [hr]
          · have hne : j ≠ r := Ne.symm hrj
            split_ifs <;> simp [hrj, hne]
        simp_rw [h1]
        simp
      have hiota0 : iota 0 = 0 := by
        have h := hiota_add 0 0
        rw [add_zero] at h
        have h2 : iota 0 + iota 0 = iota 0 + (iota 0 + iota 0) := congrArg (iota 0 + ·) h
        ext i
        have hi := congrFun h2 i
        simp only [Pi.add_apply, Pi.zero_apply] at hi ⊢
        rw [zmod2_add_self, add_zero] at hi
        exact hi.symm
      have hiota_sum : ∀ (S : Finset (Fin d)) (f : Fin d → Fin d → F2),
          iota (∑ r ∈ S, f r) = ∑ r ∈ S, iota (f r) := by
        intro S f
        induction S using Finset.induction with
        | empty => simp [hiota0]
        | insert a s ha ihS => rw [Finset.sum_insert ha, hiota_add, ihS, Finset.sum_insert ha]
      conv_lhs => rw [hy_expand, hiota_sum]
      simp only [Finset.sum_apply, dotProduct]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rcases zmod2_eq_zero_or_one (y r) with h0 | h1
      · simp [h0, hiota0]
      · simp [h1]
    | append_singleton prev g ih =>
      intro hRBp hLp
      have hRB_prev : ReadsBack k ⟨prev, 0⟩ := by
        intro j hj i hi
        dsimp only at hj
        have hj' : j < (prev ++ [g]).length := by simp only [List.length_append, List.length_singleton]; omega
        have hget : gateAt ⟨prev ++ [g], 0⟩ j = gateAt ⟨prev, 0⟩ j := by
          simp only [gateAt, List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj',
            List.getElem_append_left hj]
        rw [← hget] at hi
        exact hRBp j hj' i hi
      have hL_prev : ∀ g' ∈ prev, LegalGate g' := fun g' hg' => hLp g' (by simp [hg'])
      have hg_L : LegalGate g := hLp g (by simp)
      have hg_in : ∀ i ∈ g.inputs, i < k + prev.length := by
        intro i hi
        have hget : gateAt ⟨prev ++ [g], 0⟩ prev.length = g := by
          simp only [gateAt, List.getD_eq_getElem _ _ (by simp : prev.length < (prev ++ [g]).length),
            List.getElem_append_right (le_refl _)]
          simp
        rw [← hget] at hi
        exact hRBp prev.length (by simp) i hi
      rcases ih hRB_prev hL_prev with ⟨vecs, c, alpha, h, hvecs_len, hrep, hinv⟩
      let idx := k + prev.length
      have hval_old : ∀ w < idx, ∀ y : Fin d → F2,
          (Circuit.wires ⟨prev ++ [g], 0⟩ (List.ofFn (fun i : Fin k => decide ((x0 + iota y) i = 1)))).getD w false =
            (Circuit.wires ⟨prev, 0⟩ (List.ofFn (fun i : Fin k => decide ((x0 + iota y) i = 1)))).getD w false := by
        intro w hw y
        exact circuit_wires_append_prefix prev [g] 0 0 _ w (by simp; exact hw)
      have hval_new : ∀ y : Fin d → F2,
          (Circuit.wires ⟨prev ++ [g], 0⟩ (List.ofFn (fun i : Fin k => decide ((x0 + iota y) i = 1)))).getD idx false =
            g.op.eval (g.inputs.map fun i =>
              (Circuit.wires ⟨prev, 0⟩ (List.ofFn (fun i : Fin k => decide ((x0 + iota y) i = 1)))).getD i false) := by
        intro y
        have hlenx : (List.ofFn (fun i : Fin k => decide ((x0 + iota y) i = 1))).length = k := by simp
        have hsn := foldl_wires_snoc_last prev g (List.ofFn (fun i : Fin k => decide ((x0 + iota y) i = 1)))
        rw [hlenx] at hsn
        exact hsn
      rcases hg_L with ⟨hop, hlen2⟩ | ⟨hop, hle2⟩ | ⟨hop, hlen1⟩
      · obtain ⟨a, b, hab⟩ : ∃ a b, g.inputs = [a, b] := by
          cases h1 : g.inputs with
          | nil => rw [h1] at hlen2; simp at hlen2
          | cons u us =>
            cases us with
            | nil => rw [h1] at hlen2; simp at hlen2
            | cons v vs =>
              cases vs with
              | nil => exact ⟨u, v, rfl⟩
              | cons _ _ => rw [h1] at hlen2; simp at hlen2
        have ha : a < idx := hg_in a (by rw [hab]; simp)
        have hb : b < idx := hg_in b (by rw [hab]; simp)
        let vecs' := alpha a :: alpha b :: vecs
        let hnew : (Fin d → F2) → F2 := fun y =>
          (c a + dotProduct (alpha a) y + h a y) * (c b + dotProduct (alpha b) y + h b y)
        refine ⟨vecs', fun w => if w = idx then 0 else c w,
          fun w => if w = idx then 0 else alpha w,
          fun w => if w = idx then hnew else h w, ?_, ?_, ?_⟩
        · have hcost : andCost (prev ++ [g]) = andCost prev + 1 := by
            rw [andCost_append]; simp [andCost, hop]
          rw [hcost]
          simp only [vecs', List.length_cons]
          omega
        · intro w hw y
          simp only [List.length_append, List.length_singleton] at hw
          by_cases hweq : w = idx
          · subst hweq
            simp only [ite_true, dotProduct_zero_left, zero_add]
            rw [hval_new y, hop, hab]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, boolToF2_and, hrep a ha y, hrep b hb y, hnew]
          · have hwlt : w < idx := by omega
            simp only [hweq, ite_false]
            rw [hval_old w hwlt y]
            exact hrep w hwlt y
        · intro w hw y z hz
          simp only [List.length_append, List.length_singleton] at hw
          have hza : dotProduct (alpha a) z = 0 := hz (alpha a) (by simp [vecs'])
          have hzb : dotProduct (alpha b) z = 0 := hz (alpha b) (by simp [vecs'])
          have hz_old : ∀ v ∈ vecs, dotProduct v z = 0 := fun v hv => hz v (by simp [vecs', hv])
          by_cases hweq : w = idx
          · subst hweq
            simp only [ite_true, hnew]
            rw [dotProduct_add_right, dotProduct_add_right, hza, hzb, add_zero, add_zero,
              hinv a ha y z hz_old, hinv b hb y z hz_old]
          · have hwlt : w < idx := by omega
            simp only [hweq, ite_false]
            exact hinv w hwlt y z hz_old
      · have hcost : andCost (prev ++ [g]) = andCost prev := by
          rw [andCost_append]; simp [andCost, hop]
        cases h1 : g.inputs with
        | nil =>
          refine ⟨vecs, fun w => if w = idx then 1 else c w,
            fun w => if w = idx then 0 else alpha w,
            fun w => if w = idx then (fun _ => 0) else h w, by rw [hcost]; exact hvecs_len, ?_, ?_⟩
          · intro w hw y
            simp only [List.length_append, List.length_singleton] at hw
            by_cases hweq : w = idx
            · subst hweq
              simp only [ite_true, dotProduct_zero_left, add_zero]
              rw [hval_new y, hop, h1]
              simp only [List.map_nil, GateOp.eval]
              decide
            · have hwlt : w < idx := by omega
              simp only [hweq, ite_false]
              rw [hval_old w hwlt y]
              exact hrep w hwlt y
          · intro w hw y z hz
            simp only [List.length_append, List.length_singleton] at hw
            by_cases hweq : w = idx
            · subst hweq; simp
            · have hwlt : w < idx := by omega
              simp only [hweq, ite_false]
              exact hinv w hwlt y z hz
        | cons a rest =>
          cases rest with
          | nil =>
            have ha : a < idx := hg_in a (by rw [h1]; simp)
            refine ⟨vecs, fun w => if w = idx then 1 + c a else c w,
              fun w => if w = idx then alpha a else alpha w,
              fun w => if w = idx then h a else h w, by rw [hcost]; exact hvecs_len, ?_, ?_⟩
            · intro w hw y
              simp only [List.length_append, List.length_singleton] at hw
              by_cases hweq : w = idx
              · subst hweq
                simp only [ite_true]
                rw [hval_new y, hop, h1]
                have hmod1 : ∀ b : Bool, boolToF2 (GateOp.eval (.mod 2) [b]) = 1 + boolToF2 b := by
                  intro b; cases b <;> decide
                simp only [List.map_cons, List.map_nil]
                rw [hmod1, hrep a ha y]
                ring
              · have hwlt : w < idx := by omega
                simp only [hweq, ite_false]
                rw [hval_old w hwlt y]
                exact hrep w hwlt y
            · intro w hw y z hz
              simp only [List.length_append, List.length_singleton] at hw
              by_cases hweq : w = idx
              · subst hweq; simp only [ite_true]; exact hinv a ha y z hz
              · have hwlt : w < idx := by omega
                simp only [hweq, ite_false]
                exact hinv w hwlt y z hz
          | cons b rest2 =>
            cases rest2 with
            | nil =>
              have ha : a < idx := hg_in a (by rw [h1]; simp)
              have hb : b < idx := hg_in b (by rw [h1]; simp)
              refine ⟨vecs, fun w => if w = idx then 1 + c a + c b else c w,
                fun w => if w = idx then alpha a + alpha b else alpha w,
                fun w => if w = idx then (fun y => h a y + h b y) else h w,
                by rw [hcost]; exact hvecs_len, ?_, ?_⟩
              · intro w hw y
                simp only [List.length_append, List.length_singleton] at hw
                by_cases hweq : w = idx
                · subst hweq
                  simp only [ite_true]
                  rw [hval_new y, hop, h1]
                  have hmod2 : ∀ b₁ b₂ : Bool,
                      boolToF2 (GateOp.eval (.mod 2) [b₁, b₂]) = 1 + boolToF2 b₁ + boolToF2 b₂ := by
                    intro b₁ b₂; cases b₁ <;> cases b₂ <;> decide
                  simp only [List.map_cons, List.map_nil]
                  rw [hmod2, hrep a ha y, hrep b hb y, dotProduct_add_left]
                  ring
                · have hwlt : w < idx := by omega
                  simp only [hweq, ite_false]
                  rw [hval_old w hwlt y]
                  exact hrep w hwlt y
              · intro w hw y z hz
                simp only [List.length_append, List.length_singleton] at hw
                by_cases hweq : w = idx
                · subst hweq; simp only [ite_true]
                  rw [hinv a ha y z hz, hinv b hb y z hz]
                · have hwlt : w < idx := by omega
                  simp only [hweq, ite_false]
                  exact hinv w hwlt y z hz
            | cons _ _ => rw [h1] at hle2; simp at hle2
      · obtain ⟨a, ha_eq⟩ : ∃ a, g.inputs = [a] := by
          cases h1 : g.inputs with
          | nil => rw [h1] at hlen1; simp at hlen1
          | cons u us =>
            cases us with
            | nil => exact ⟨u, rfl⟩
            | cons _ _ => rw [h1] at hlen1; simp at hlen1
        have ha : a < idx := hg_in a (by rw [ha_eq]; simp)
        have hcost : andCost (prev ++ [g]) = andCost prev := by
          rw [andCost_append]; simp [andCost, hop]
        refine ⟨vecs, fun w => if w = idx then 1 + c a else c w,
          fun w => if w = idx then alpha a else alpha w,
          fun w => if w = idx then h a else h w, by rw [hcost]; exact hvecs_len, ?_, ?_⟩
        · intro w hw y
          simp only [List.length_append, List.length_singleton] at hw
          by_cases hweq : w = idx
          · subst hweq
            simp only [ite_true]
            rw [hval_new y, hop, ha_eq]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons, boolToF2_not,
              hrep a ha y]
            ring
          · have hwlt : w < idx := by omega
            simp only [hweq, ite_false]
            rw [hval_old w hwlt y]
            exact hrep w hwlt y
        · intro w hw y z hz
          simp only [List.length_append, List.length_singleton] at hw
          by_cases hweq : w = idx
          · subst hweq; simp only [ite_true]; exact hinv a ha y z hz
          · have hwlt : w < idx := by omega
            simp only [hweq, ite_false]
            exact hinv w hwlt y z hz
  exact hgen C.gates hRB hL

lemma kernel_card_ge {d : ℕ} (vecs : List (Fin d → F2)) :
    let K := Finset.univ.filter (fun z : Fin d → F2 => ∀ a ∈ vecs, dotProduct a z = 0)
    2 ^ d ≤ 2 ^ vecs.length * K.card := by
  intro K
  let L : (Fin d → F2) → (Fin vecs.length → F2) := fun z i => dotProduct (vecs.get i) z
  have hL_add : ∀ y z, L (y + z) = L y + L z := by
    intro y z; ext i
    simp only [L, Pi.add_apply, dotProduct_add_right]
  have hK_eq : K = Finset.univ.filter (fun z : Fin d → F2 => L z = 0) := by
    ext z
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; ext i; exact h (vecs.get i) (List.get_mem vecs i)
    · intro h a ha
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      exact congrFun h ⟨i, hi⟩
  have hfib_le : ∀ v : Fin vecs.length → F2,
      (Finset.univ.filter (fun z : Fin d → F2 => L z = v)).card ≤ K.card := by
    intro v
    by_cases hne : (Finset.univ.filter (fun z : Fin d → F2 => L z = v)).Nonempty
    · rcases hne with ⟨z₀, hz₀⟩
      have hz₀' : L z₀ = v := (Finset.mem_filter.mp hz₀).2
      rw [hK_eq]
      have hbij : (Finset.univ.filter (fun z : Fin d → F2 => L z = v)).card =
          (Finset.univ.filter (fun z : Fin d → F2 => L z = 0)).card := by
        refine Finset.card_bij (fun z _ => z + z₀) ?_ ?_ ?_
        · intro z hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
          rw [hL_add, hz, hz₀']
          ext i; exact zmod2_add_self (v i)
        · intro z₁ _ z₂ _ h
          have h' : z₁ + z₀ + z₀ = z₂ + z₀ + z₀ := congrArg (· + z₀) h
          ext r
          have hr := congrFun h' r
          simp only [Pi.add_apply, add_assoc, zmod2_add_self, add_zero] at hr
          exact hr
        · intro z hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
          refine ⟨z + z₀, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hL_add, hz, hz₀', zero_add]
          · ext r; simp only [Pi.add_apply, add_assoc, zmod2_add_self, add_zero]
      exact le_of_eq hbij
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp
  have htot : (Finset.univ : Finset (Fin d → F2)).card =
      ∑ v : Fin vecs.length → F2, (Finset.univ.filter (fun z : Fin d → F2 => L z = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  have hcard_d : (Finset.univ : Finset (Fin d → F2)).card = 2 ^ d := by
    simp [Fintype.card_fun, ZMod.card]
  have hcard_r : (Finset.univ : Finset (Fin vecs.length → F2)).card = 2 ^ vecs.length := by
    simp [Fintype.card_fun, ZMod.card]
  calc
    2 ^ d = ∑ v : Fin vecs.length → F2, (Finset.univ.filter (fun z : Fin d → F2 => L z = v)).card := by
          rw [← hcard_d, htot]
    _ ≤ ∑ _v : Fin vecs.length → F2, K.card := Finset.sum_le_sum (fun v _ => hfib_le v)
    _ = 2 ^ vecs.length * K.card := by rw [Finset.sum_const, hcard_r, smul_eq_mul]

lemma circuit_gain_upper_bound {d m : ℕ} (J : Finset (Fin m)) (u : Fin m → Fin d → F2)
    (c0 : Fin m → F2) (gBit : (Fin d → F2) → Bool) (dec : Bool → Fin m → Bool)
    (K : Finset (Fin d → F2)) (cOut : F2) (alphaOut : Fin d → F2) (hOut : (Fin d → F2) → F2)
    (hK0 : (0 : Fin d → F2) ∈ K)
    (hKadd : ∀ z₁ ∈ K, ∀ z₂ ∈ K, z₁ + z₂ ∈ K)
    (hKcard : 16 ≤ K.card)
    (hg_rep : ∀ y, boolToF2 (gBit y) = cOut + dotProduct alphaOut y + hOut y)
    (hh_inv : ∀ y, ∀ z ∈ K, hOut (y + z) = hOut y)
    (hu_ne0 : ∀ j : Fin m, u j ≠ 0)
    (hu_inj : Function.Injective u)
    (hbias : ∀ a : Fin d → F2, a ≠ 0 → 14 * |∑ j : Fin m, chi (dotProduct a (u j))| ≤ (m : ℤ)) :
    let decGain : ℤ :=
      2 * (∑ y : Fin d → F2, ((J.filter (fun j => dec (gBit y) j = decide (dotProduct y (u j) + c0 j = 1))).card : ℤ)) -
        (2 ^ d : ℤ) * (J.card : ℤ)
    0 ≤ decGain → 224 * decGain ^ 2 ≤ 29 * (2 ^ d : ℤ) ^ 2 * (m : ℤ) := by
  intro decGain hnonneg
  let Fhat : (Fin d → F2) → ℤ := fun w =>
    ∑ y : Fin d → F2, chi (boolToF2 (gBit y)) * chi (dotProduct y w)
  have hFhat_zero : ∀ w : Fin d → F2, (∃ z ∈ K, dotProduct (w + alphaOut) z = 1) → Fhat w = 0 := by
    intro w ⟨z, hzK, hdot1⟩
    have hshift : (∑ y : Fin d → F2, chi (boolToF2 (gBit (y + z))) * chi (dotProduct (y + z) w)) = Fhat w :=
      Fintype.sum_equiv (Equiv.addRight z) _ _ (fun _ => rfl)
    have hneg : (∑ y : Fin d → F2, chi (boolToF2 (gBit (y + z))) * chi (dotProduct (y + z) w)) = -Fhat w := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [hg_rep (y + z), hg_rep y, hh_inv y z hzK, dotProduct_add_right, dotProduct_add_left]
      have hcomm : dotProduct z w = dotProduct w z := by
        simp only [dotProduct, mul_comm]
      rw [hcomm]
      have hsum : (cOut + (dotProduct alphaOut y + dotProduct alphaOut z) + hOut y) +
          (dotProduct y w + dotProduct w z) =
          (cOut + dotProduct alphaOut y + hOut y + dotProduct y w) + dotProduct (w + alphaOut) z := by
        rw [dotProduct_add_left]
        ring
      rw [← chi_add, ← chi_add, hsum, hdot1, chi_add, chi_one]
      ring
    linarith
  have hparseval : (∑ w : Fin d → F2, Fhat w ^ 2) = (2 ^ d : ℤ) ^ 2 := by
    have hsq : ∀ w, Fhat w ^ 2 =
        ∑ y₁ : Fin d → F2, ∑ y₂ : Fin d → F2,
          chi (boolToF2 (gBit y₁)) * chi (boolToF2 (gBit y₂)) * chi (dotProduct (y₁ + y₂) w) := by
      intro w
      simp only [Fhat, sq, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y₁ _ => Finset.sum_congr rfl (fun y₂ _ => ?_))
      rw [dotProduct_add_left, chi_add]
      ring
    simp_rw [hsq]
    rw [Finset.sum_comm]
    have hsw : ∀ y₁, (∑ w : Fin d → F2, ∑ y₂ : Fin d → F2,
        chi (boolToF2 (gBit y₁)) * chi (boolToF2 (gBit y₂)) * chi (dotProduct (y₁ + y₂) w)) =
        ∑ y₂ : Fin d → F2, chi (boolToF2 (gBit y₁)) * chi (boolToF2 (gBit y₂)) *
          ∑ w : Fin d → F2, chi (dotProduct w (y₁ + y₂)) := by
      intro y₁
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y₂ _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      have hcomm : dotProduct (y₁ + y₂) w = dotProduct w (y₁ + y₂) := by
        simp only [dotProduct, mul_comm]
      rw [hcomm]
    simp_rw [hsw, sum_chi_dotProduct]
    have hinner : ∀ y₁ : Fin d → F2,
        (∑ y₂ : Fin d → F2, chi (boolToF2 (gBit y₁)) * chi (boolToF2 (gBit y₂)) *
          (if y₁ + y₂ = 0 then (2 ^ d : ℤ) else 0)) = (2 ^ d : ℤ) := by
      intro y₁
      have heq_cond : ∀ y₂ : Fin d → F2, (y₁ + y₂ = 0) ↔ (y₂ = y₁) := by
        intro y₂
        constructor
        · intro h
          ext r
          have hr := congrFun h r
          have hr' : y₁ r + (y₁ r + y₂ r) = y₁ r + 0 := congrArg (y₁ r + ·) hr
          simp only [← add_assoc, zmod2_add_self, zero_add, add_zero] at hr'
          exact hr'
        · rintro rfl; ext r; exact zmod2_add_self (y₂ r)
      have hite : ∀ y₂ : Fin d → F2,
          chi (boolToF2 (gBit y₁)) * chi (boolToF2 (gBit y₂)) * (if y₁ + y₂ = 0 then (2 ^ d : ℤ) else 0) =
          if y₂ = y₁ then (2 ^ d : ℤ) else 0 := by
        intro y₂
        by_cases hy : y₂ = y₁
        · subst hy
          have h0 : y₂ + y₂ = 0 := (heq_cond y₂).mpr rfl
          simp [h0, chi_mul_self]
        · have hne : y₁ + y₂ ≠ 0 := mt (heq_cond y₂).mp hy
          simp [hy, hne]
      simp_rw [hite]
      simp
    simp_rw [hinner]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      ZMod.card, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    ring
  have hgain_le : decGain ≤ ∑ j ∈ J, |Fhat (u j)| := by
    have hcard_univ : (Finset.univ : Finset (Fin d → F2)).card = 2 ^ d := by
      simp [Fintype.card_fun, ZMod.card]
    have hexp : decGain = ∑ j ∈ J, ∑ y : Fin d → F2,
        chi (boolToF2 (dec (gBit y) j)) * chi (dotProduct y (u j) + c0 j) := by
      have hper : ∀ y : Fin d → F2,
          2 * ((J.filter (fun j => dec (gBit y) j = decide (dotProduct y (u j) + c0 j = 1))).card : ℤ) -
            (J.card : ℤ) =
            ∑ j ∈ J, chi (boolToF2 (dec (gBit y) j)) * chi (dotProduct y (u j) + c0 j) := by
        intro y
        have hterm : ∀ j : Fin m,
            chi (boolToF2 (dec (gBit y) j)) * chi (dotProduct y (u j) + c0 j) =
              2 * (if dec (gBit y) j = decide (dotProduct y (u j) + c0 j = 1) then (1 : ℤ) else 0) - 1 := by
          intro j
          rcases zmod2_eq_zero_or_one (dotProduct y (u j) + c0 j) with h0 | h1
          · rw [h0, chi_zero]
            cases dec (gBit y) j <;> decide
          · rw [h1, chi_one]
            cases dec (gBit y) j <;> decide
        simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole,
          Finset.sum_const, nsmul_eq_mul, mul_one]
      calc
        decGain = ∑ y : Fin d → F2,
            (2 * ((J.filter (fun j => dec (gBit y) j = decide (dotProduct y (u j) + c0 j = 1))).card : ℤ) -
              (J.card : ℤ)) := by
          simp only [decGain, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
            hcard_univ, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        _ = ∑ y : Fin d → F2, ∑ j ∈ J,
              chi (boolToF2 (dec (gBit y) j)) * chi (dotProduct y (u j) + c0 j) :=
          Finset.sum_congr rfl (fun y _ => hper y)
        _ = ∑ j ∈ J, ∑ y : Fin d → F2,
              chi (boolToF2 (dec (gBit y) j)) * chi (dotProduct y (u j) + c0 j) := Finset.sum_comm
    rw [hexp]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have hzero : (∑ y : Fin d → F2, chi (dotProduct y (u j))) = 0 := by
      rw [sum_chi_dotProduct, if_neg (hu_ne0 j)]
    have hcases : (∀ b, dec b j = false) ∨ (∀ b, dec b j = true) ∨
        (∀ b, dec b j = b) ∨ (∀ b, dec b j = !b) := by
      cases hf : dec false j <;> cases ht : dec true j
      · left; intro b; cases b <;> assumption
      · right; right; left; intro b; cases b <;> assumption
      · right; right; right; intro b; cases b <;> assumption
      · right; left; intro b; cases b <;> assumption
    have hfactor : ∀ s : ℤ, (∑ y : Fin d → F2, s * chi (dotProduct y (u j) + c0 j)) = 0 := by
      intro s
      have : ∀ y, s * chi (dotProduct y (u j) + c0 j) = (s * chi (c0 j)) * chi (dotProduct y (u j)) := by
        intro y; rw [chi_add]; ring
      simp_rw [this, ← Finset.mul_sum, hzero, mul_zero]
    rcases hcases with hff | htt | hid | hnot
    · have hval : (∑ y : Fin d → F2, chi (boolToF2 (dec (gBit y) j)) * chi (dotProduct y (u j) + c0 j)) = 0 := by
        simp_rw [hff, show chi (boolToF2 false) = 1 from by decide]
        exact hfactor 1
      rw [hval]; exact abs_nonneg _
    · have hval : (∑ y : Fin d → F2, chi (boolToF2 (dec (gBit y) j)) * chi (dotProduct y (u j) + c0 j)) = 0 := by
        simp_rw [htt, show chi (boolToF2 true) = -1 from by decide]
        exact hfactor (-1)
      rw [hval]; exact abs_nonneg _
    · have hval : (∑ y : Fin d → F2, chi (boolToF2 (dec (gBit y) j)) * chi (dotProduct y (u j) + c0 j)) =
          chi (c0 j) * Fhat (u j) := by
        simp only [Fhat, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [hid, chi_add]; ring
      rw [hval]
      rcases zmod2_eq_zero_or_one (c0 j) with h0 | h1
      · rw [h0, chi_zero, one_mul]; exact le_abs_self _
      · rw [h1, chi_one]; linarith [neg_le_abs (Fhat (u j))]
    · have hval : (∑ y : Fin d → F2, chi (boolToF2 (dec (gBit y) j)) * chi (dotProduct y (u j) + c0 j)) =
          -(chi (c0 j) * Fhat (u j)) := by
        simp only [Fhat, Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [hnot, boolToF2_not, chi_add, chi_one, chi_add]; ring
      rw [hval]
      rcases zmod2_eq_zero_or_one (c0 j) with h0 | h1
      · rw [h0, chi_zero, one_mul]; exact neg_le_abs _
      · rw [h1, chi_one]; linarith [le_abs_self (Fhat (u j))]
  let JK := J.filter (fun j => ∀ z ∈ K, dotProduct (u j + alphaOut) z = 0)
  have hsum_JK : (∑ j ∈ J, |Fhat (u j)|) = ∑ j ∈ JK, |Fhat (u j)| := by
    rw [← Finset.sum_filter_add_sum_filter_not J (fun j => ∀ z ∈ K, dotProduct (u j + alphaOut) z = 0)]
    have h0 : (∑ j ∈ J.filter (fun j => ¬∀ z ∈ K, dotProduct (u j + alphaOut) z = 0), |Fhat (u j)|) = 0 := by
      refine Finset.sum_eq_zero (fun j hj => ?_)
      have hne := (Finset.mem_filter.mp hj).2
      push_neg at hne
      rcases hne with ⟨z, hzK, hnz⟩
      have h1 : dotProduct (u j + alphaOut) z = 1 := by
        rcases zmod2_eq_zero_or_one (dotProduct (u j + alphaOut) z) with h0 | h1
        · exact (hnz h0).elim
        · exact h1
      rw [hFhat_zero (u j) ⟨z, hzK, h1⟩, abs_zero]
    rw [h0, add_zero]
  have hcs : (∑ j ∈ JK, |Fhat (u j)|) ^ 2 ≤ (JK.card : ℤ) * (∑ j ∈ JK, Fhat (u j) ^ 2) := by
    have h := cauchy_schwarz_int JK (fun j => |Fhat (u j)|)
    simpa only [sq_abs] using h
  have hsum_sq_le : (∑ j ∈ JK, Fhat (u j) ^ 2) ≤ (2 ^ d : ℤ) ^ 2 := by
    have h2 : (∑ j ∈ JK, Fhat (u j) ^ 2) = ∑ w ∈ JK.image u, Fhat w ^ 2 := by
      rw [Finset.sum_image (fun a _ b _ h => hu_inj h)]
    rw [h2]
    have hle := Finset.sum_le_univ_sum_of_nonneg (s := JK.image u) (f := fun w => Fhat w ^ 2)
      (fun _ => sq_nonneg _)
    exact le_trans hle (le_of_eq hparseval)
  have hdec_sq : decGain ^ 2 ≤ (JK.card : ℤ) * (2 ^ d : ℤ) ^ 2 := by
    have h1 : decGain ^ 2 ≤ (∑ j ∈ JK, |Fhat (u j)|) ^ 2 := by
      rw [← hsum_JK]
      exact pow_le_pow_left₀ hnonneg hgain_le 2
    exact le_trans h1 (le_trans hcs (mul_le_mul_of_nonneg_left hsum_sq_le (Nat.cast_nonneg _)))
  have hK_sum_nonneg : ∀ j : Fin m,
      (∑ z ∈ K, chi (dotProduct (u j + alphaOut) z)) =
        if ∀ z ∈ K, dotProduct (u j + alphaOut) z = 0 then (K.card : ℤ) else 0 := by
    intro j
    split_ifs with hall
    · rw [Finset.sum_congr rfl (fun z hz => by rw [hall z hz, chi_zero])]
      simp
    · push_neg at hall
      rcases hall with ⟨z₀, hz₀K, hnz⟩
      have hdot1 : dotProduct (u j + alphaOut) z₀ = 1 := by
        rcases zmod2_eq_zero_or_one (dotProduct (u j + alphaOut) z₀) with h0 | h1
        · exact (hnz h0).elim
        · exact h1
      have hshift : (∑ z ∈ K, chi (dotProduct (u j + alphaOut) (z + z₀))) =
          ∑ z ∈ K, chi (dotProduct (u j + alphaOut) z) := by
        refine Finset.sum_bij (fun z _ => z + z₀) ?_ ?_ ?_ ?_
        · intro z hz; exact hKadd z hz z₀ hz₀K
        · intro z₁ _ z₂ _ h
          have h' : z₁ + z₀ + z₀ = z₂ + z₀ + z₀ := congrArg (· + z₀) h
          ext r
          have hr := congrFun h' r
          simp only [Pi.add_apply, add_assoc, zmod2_add_self, add_zero] at hr
          exact hr
        · intro z hz
          refine ⟨z + z₀, hKadd z hz z₀ hz₀K, ?_⟩
          ext r; simp only [Pi.add_apply, add_assoc, zmod2_add_self, add_zero]
        · intro z _; rfl
      have hneg : (∑ z ∈ K, chi (dotProduct (u j + alphaOut) (z + z₀))) =
          -(∑ z ∈ K, chi (dotProduct (u j + alphaOut) z)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        rw [dotProduct_add_right, hdot1, chi_add, chi_one]; ring
      linarith
  have hJK_bound : 224 * (JK.card : ℤ) ≤ 29 * (m : ℤ) := by
    have hlow : (K.card : ℤ) * (JK.card : ℤ) ≤
        ∑ j : Fin m, ∑ z ∈ K, chi (dotProduct (u j + alphaOut) z) := by
      have hle_univ : (∑ j ∈ JK, (K.card : ℤ)) ≤
          ∑ j : Fin m, ∑ z ∈ K, chi (dotProduct (u j + alphaOut) z) := by
        calc
          (∑ j ∈ JK, (K.card : ℤ))
              = ∑ j ∈ JK, ∑ z ∈ K, chi (dotProduct (u j + alphaOut) z) := by
                refine Finset.sum_congr rfl (fun j hj => ?_)
                rw [hK_sum_nonneg j, if_pos (Finset.mem_filter.mp hj).2]
          _ ≤ ∑ j : Fin m, ∑ z ∈ K, chi (dotProduct (u j + alphaOut) z) := by
                refine Finset.sum_le_univ_sum_of_nonneg (fun j => ?_)
                rw [hK_sum_nonneg j]
                split_ifs <;> positivity
      simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hle_univ
    have hswap : (∑ j : Fin m, ∑ z ∈ K, chi (dotProduct (u j + alphaOut) z)) =
        (m : ℤ) + ∑ z ∈ K.erase 0, chi (dotProduct alphaOut z) *
          ∑ j : Fin m, chi (dotProduct z (u j)) := by
      rw [Finset.sum_comm, ← Finset.add_sum_erase K _ hK0]
      have hz0 : (∑ j : Fin m, chi (dotProduct (u j + alphaOut) 0)) = (m : ℤ) := by
        simp [dotProduct_zero_right, chi_zero]
      rw [hz0]
      congr 1
      refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hcomm : dotProduct (u j) z = dotProduct z (u j) := by
        simp only [dotProduct, mul_comm]
      rw [dotProduct_add_left, chi_add, hcomm]
      ring
    have h14 : 14 * ((K.card : ℤ) * (JK.card : ℤ)) ≤ ((K.card : ℤ) + 13) * (m : ℤ) := by
      have hterm : ∀ z ∈ K.erase 0,
          14 * (chi (dotProduct alphaOut z) * ∑ j : Fin m, chi (dotProduct z (u j))) ≤ (m : ℤ) := by
        intro z hz
        have hzne : z ≠ 0 := (Finset.mem_erase.mp hz).1
        have hb := hbias z hzne
        rcases zmod2_eq_zero_or_one (dotProduct alphaOut z) with h0 | h1
        · rw [h0, chi_zero, one_mul]
          linarith [le_abs_self (∑ j : Fin m, chi (dotProduct z (u j)))]
        · rw [h1, chi_one]
          linarith [neg_le_abs (∑ j : Fin m, chi (dotProduct z (u j)))]
      have hsum_er : 14 * (∑ z ∈ K.erase 0, chi (dotProduct alphaOut z) *
          ∑ j : Fin m, chi (dotProduct z (u j))) ≤ ((K.erase 0).card : ℤ) * (m : ℤ) := by
        rw [Finset.mul_sum]
        calc
          (∑ z ∈ K.erase 0, 14 * (chi (dotProduct alphaOut z) * ∑ j : Fin m, chi (dotProduct z (u j))))
              ≤ ∑ _z ∈ K.erase 0, (m : ℤ) := Finset.sum_le_sum hterm
          _ = ((K.erase 0).card : ℤ) * (m : ℤ) := by simp
      have hcard_er : ((K.erase 0).card : ℤ) = (K.card : ℤ) - 1 := by
        rw [Finset.card_erase_of_mem hK0]
        have hpos : 1 ≤ K.card := Finset.card_pos.mpr ⟨0, hK0⟩
        omega
      rw [hcard_er] at hsum_er
      linarith
    have hKpos : (0 : ℤ) < K.card := by omega
    have hK16 : (16 : ℤ) ≤ K.card := by omega
    have hmul : (K.card : ℤ) * (224 * (JK.card : ℤ)) ≤ (K.card : ℤ) * (29 * (m : ℤ)) := by
      have hm0 : (0 : ℤ) ≤ m := Nat.cast_nonneg m
      nlinarith
    exact le_of_mul_le_mul_left hmul hKpos
  calc
    224 * decGain ^ 2 ≤ 224 * ((JK.card : ℤ) * (2 ^ d : ℤ) ^ 2) :=
          mul_le_mul_of_nonneg_left hdec_sq (by norm_num)
    _ = (224 * (JK.card : ℤ)) * (2 ^ d : ℤ) ^ 2 := by ring
    _ ≤ (29 * (m : ℤ)) * (2 ^ d : ℤ) ^ 2 :=
          mul_le_mul_of_nonneg_right hJK_bound (sq_nonneg _)
    _ = 29 * (2 ^ d : ℤ) ^ 2 * (m : ℤ) := by ring

lemma slice_final_contradiction (d m Jcard : ℕ) (majGainZ decGainZ : ℤ)
    (hm_pos : 1 ≤ m) (hJm : m ≤ 2 * Jcard)
    (hmaj_sq : (2 ^ d : ℤ) ^ 2 * (Jcard : ℤ) ≤ 3 * majGainZ ^ 2)
    (h9_10 : 9 * majGainZ ≤ 10 * max 0 decGainZ)
    (hmaj_nn : 0 ≤ majGainZ)
    (hdec_ub : 0 ≤ decGainZ → 224 * decGainZ ^ 2 ≤ 29 * (2 ^ d : ℤ) ^ 2 * (m : ℤ)) :
    False := by
  have hJpos : (0 : ℤ) < Jcard := by omega
  have h2pos : (0 : ℤ) < (2 ^ d : ℤ) ^ 2 := by positivity
  have hmpos : (0 : ℤ) < m := by omega
  have hmaj_pos : 0 < majGainZ := by
    by_contra hle0
    have h0 : majGainZ = 0 := by omega
    rw [h0] at hmaj_sq
    nlinarith
  have hdec_pos : 0 < decGainZ := by
    by_contra hle0
    have hmax0 : max 0 decGainZ = 0 := max_eq_left (by omega)
    rw [hmax0] at h9_10
    omega
  have h9_10' : 9 * majGainZ ≤ 10 * decGainZ := by
    rwa [max_eq_right (le_of_lt hdec_pos)] at h9_10
  have hub := hdec_ub (le_of_lt hdec_pos)
  have hsq9_10 : 81 * majGainZ ^ 2 ≤ 100 * decGainZ ^ 2 := by nlinarith
  have hmJ : (m : ℤ) ≤ 2 * (Jcard : ℤ) := by exact_mod_cast hJm
  have hlow_m : (2 ^ d : ℤ) ^ 2 * (m : ℤ) ≤ 6 * majGainZ ^ 2 := by nlinarith
  have hpos_m : (0 : ℤ) < (2 ^ d : ℤ) ^ 2 * (m : ℤ) := mul_pos h2pos hmpos
  nlinarith

lemma slice_param_exists (k m : ℕ) (hk : 128 ≤ k)
    (v : Fin m → Fin k → F2)
    (hbias : ∀ w : Fin k → F2, w ≠ 0 → 14 * |∑ j : Fin m, chi (dotProduct w (v j))| ≤ (m : ℤ))
    (hindep : ∀ S : Finset (Fin m), 1 ≤ S.card → S.card ≤ 4 →
      k / 32 < (Finset.univ.filter (fun i : Fin k => (∑ j ∈ S, v j i) = 1)).card ∧
      (Finset.univ.filter (fun i : Fin k => (∑ j ∈ S, v j i) = 1)).card < k - k / 32)
    (P : Finset (Fin k)) (hP : P.card ≤ k / 32) (pins : Fin k → F2) (par : F2) :
    let d := k - P.card - 1
    let X := (Finset.univ : Finset (Fin k → F2)).filter (fun x =>
      (∀ i ∈ P, x i = pins i) ∧ (∑ i : Fin k, x i) = par)
    ∃ (x0 : Fin k → F2) (iota : (Fin d → F2) → (Fin k → F2))
      (u : Fin m → Fin d → F2) (c0 : Fin m → F2),
      (∀ y₁ y₂, iota (y₁ + y₂) = iota y₁ + iota y₂) ∧
      X.card = 2 ^ d ∧
      (∀ F : (Fin k → F2) → ℕ, (∑ x ∈ X, F x) = ∑ y : Fin d → F2, F (x0 + iota y)) ∧
      (∀ y j, dotProduct (x0 + iota y) (v j) = dotProduct y (u j) + c0 j) ∧
      (∀ S : Finset (Fin m), 1 ≤ S.card → S.card ≤ 4 → (∑ j ∈ S, u j) ≠ 0) ∧
      (∀ j : Fin m, u j ≠ 0) ∧
      Function.Injective u ∧
      (∀ a : Fin d → F2, a ≠ 0 → 14 * |∑ j : Fin m, chi (dotProduct a (u j))| ≤ (m : ℤ)) := by
  intro d X
  let Pc : Finset (Fin k) := Finset.univ \ P
  have hPc_card : Pc.card = k - P.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  have hPc_ne : Pc.Nonempty := Finset.card_pos.mp (by omega)
  let p0 : Fin k := hPc_ne.choose
  have hp0_mem : p0 ∈ Pc := hPc_ne.choose_spec
  have hp0_notP : p0 ∉ P := (Finset.mem_sdiff.mp hp0_mem).2
  let Q : Finset (Fin k) := Pc.erase p0
  have hQ_card : Q.card = d := by
    rw [Finset.card_erase_of_mem hp0_mem, hPc_card]
  let eQ : Fin d ≃ Q := (Fintype.equivFinOfCardEq (by simp [hQ_card])).symm
  let free : Fin d → Fin k := fun r => (eQ r).1
  have hfree_memQ : ∀ r, free r ∈ Q := fun r => (eQ r).2
  have hfree_inj : Function.Injective free := fun r₁ r₂ h => eQ.injective (Subtype.ext h)
  have hfree_notP : ∀ r, free r ∉ P := fun r =>
    (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase (hfree_memQ r))).2
  have hfree_nep0 : ∀ r, free r ≠ p0 := fun r => (Finset.mem_erase.mp (hfree_memQ r)).1
  have hpart_univ : ∀ i : Fin k, i ∈ P ∨ i = p0 ∨ ∃ r : Fin d, free r = i := by
    intro i
    by_cases hiP : i ∈ P
    · exact Or.inl hiP
    · by_cases hip0 : i = p0
      · exact Or.inr (Or.inl hip0)
      · right; right
        have hiQ : i ∈ Q := Finset.mem_erase.mpr ⟨hip0, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiP⟩⟩
        exact ⟨eQ.symm ⟨i, hiQ⟩, by simp [free]⟩
  let x0 : Fin k → F2 := fun i =>
    if i ∈ P then pins i
    else if i = p0 then par + ∑ t ∈ P, pins t
    else 0
  let iota : (Fin d → F2) → (Fin k → F2) := fun y i =>
    if hi : i ∈ Q then y (eQ.symm ⟨i, hi⟩)
    else if i = p0 then ∑ r : Fin d, y r
    else 0
  have hiota_add : ∀ y₁ y₂, iota (y₁ + y₂) = iota y₁ + iota y₂ := by
    intro y₁ y₂; ext i
    simp only [iota, Pi.add_apply]
    split_ifs
    · rfl
    · exact Finset.sum_add_distrib
    · simp
  have hiota_free : ∀ y r, iota y (free r) = y r := by
    intro y r
    simp only [iota, dif_pos (hfree_memQ r)]
    have hsub : (⟨free r, hfree_memQ r⟩ : Q) = eQ r := by ext; rfl
    rw [hsub, Equiv.symm_apply_apply]
  have hiota_p0 : ∀ y, iota y p0 = ∑ r : Fin d, y r := by
    intro y
    have hp0_notQ : p0 ∉ Q := Finset.notMem_erase p0 Pc
    simp [iota, hp0_notQ]
  have hiota_P : ∀ y, ∀ i ∈ P, iota y i = 0 := by
    intro y i hiP
    have hi_notQ : i ∉ Q := fun h => (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase h)).2 hiP
    have hi_nep0 : i ≠ p0 := fun h => hp0_notP (h ▸ hiP)
    simp [iota, hi_notQ, hi_nep0]
  have hiota_inj : Function.Injective iota := by
    intro y₁ y₂ h
    ext r
    have hr := congrFun h (free r)
    rwa [hiota_free, hiota_free] at hr
  have hiota_ne0 : ∀ a : Fin d → F2, a ≠ 0 → iota a ≠ 0 := by
    intro a ha h0
    apply ha
    apply hiota_inj
    rw [h0]
    ext i; simp [iota]
  have hsum_split : ∀ f : Fin k → F2,
      (∑ i : Fin k, f i) = (∑ i ∈ P, f i) + f p0 + ∑ r : Fin d, f (free r) := by
    intro f
    have hQsum : (∑ i ∈ Q, f i) = ∑ r : Fin d, f (free r) := by
      refine (Finset.sum_bij (fun r _ => free r) (fun r _ => hfree_memQ r)
        (fun _ _ _ _ h => hfree_inj h) ?_ (fun _ _ => rfl)).symm
      intro i hiQ
      exact ⟨eQ.symm ⟨i, hiQ⟩, Finset.mem_univ _, by simp [free]⟩
    rw [← hQsum]
    have hPc_sum : (∑ i ∈ Pc, f i) = f p0 + ∑ i ∈ Q, f i :=
      (Finset.add_sum_erase Pc f hp0_mem).symm
    have huniv : P ∪ Pc = Finset.univ := by
      ext i; simp [Pc]
    have hdisj : Disjoint P Pc := Finset.disjoint_sdiff
    rw [← huniv, Finset.sum_union hdisj, hPc_sum, add_assoc]
  have hmemX : ∀ y : Fin d → F2, x0 + iota y ∈ X := by
    intro y
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro i hiP
      simp only [Pi.add_apply, x0, if_pos hiP, hiota_P y i hiP, add_zero]
    · rw [hsum_split]
      have hPsum : (∑ i ∈ P, (x0 + iota y) i) = ∑ i ∈ P, pins i := by
        refine Finset.sum_congr rfl (fun i hiP => ?_)
        simp [x0, hiP, hiota_P y i hiP]
      have hp0val : (x0 + iota y) p0 = (par + ∑ t ∈ P, pins t) + ∑ r : Fin d, y r := by
        simp [x0, hp0_notP, hiota_p0]
      have hQsum : (∑ r : Fin d, (x0 + iota y) (free r)) = ∑ r : Fin d, y r := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        simp [x0, hfree_notP r, hfree_nep0 r, hiota_free]
      rw [hPsum, hp0val, hQsum]
      have hrearr : (∑ i ∈ P, pins i) + ((par + ∑ t ∈ P, pins t) + ∑ r : Fin d, y r) + ∑ r : Fin d, y r =
          par + ((∑ i ∈ P, pins i) + (∑ t ∈ P, pins t)) + ((∑ r : Fin d, y r) + (∑ r : Fin d, y r)) := by
        ring
      rw [hrearr, zmod2_add_self, zmod2_add_self, add_zero, add_zero]
  have hbijX : ∀ x ∈ X, ∃! y : Fin d → F2, x0 + iota y = x := by
    intro x hx
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    let y : Fin d → F2 := fun r => x (free r)
    refine ⟨y, ?_, ?_⟩
    · ext i
      rcases hpart_univ i with hiP | rfl | ⟨r, rfl⟩
      · simp [x0, hiP, hiota_P y i hiP, hx.1 i hiP]
      · simp only [Pi.add_apply, x0, if_neg hp0_notP, ite_true, hiota_p0]
        have hxs := hsum_split x
        rw [hx.2] at hxs
        have hPeq : (∑ t ∈ P, x t) = ∑ t ∈ P, pins t :=
          Finset.sum_congr rfl (fun t ht => hx.1 t ht)
        rw [hPeq] at hxs
        have h2 : par + (∑ t ∈ P, pins t) + (∑ r : Fin d, y r) =
            ((∑ t ∈ P, pins t) + x p0 + ∑ r : Fin d, y r) + (∑ t ∈ P, pins t) + ∑ r : Fin d, y r := by
          rw [← hxs]
        have h3 : ((∑ t ∈ P, pins t) + x p0 + ∑ r : Fin d, y r) + (∑ t ∈ P, pins t) + ∑ r : Fin d, y r =
            x p0 + ((∑ t ∈ P, pins t) + (∑ t ∈ P, pins t)) + ((∑ r : Fin d, y r) + (∑ r : Fin d, y r)) := by
          ring
        rw [h2, h3, zmod2_add_self, zmod2_add_self, add_zero, add_zero]
      · simp [x0, hfree_notP r, hfree_nep0 r, hiota_free, y]
    · intro y' hy'
      ext r
      have hr := congrFun hy' (free r)
      simp only [Pi.add_apply, x0, if_neg (hfree_notP r), if_neg (hfree_nep0 r), zero_add,
        hiota_free] at hr
      exact hr
  have hXcard : X.card = 2 ^ d := by
    have hbij : X.card = (Finset.univ : Finset (Fin d → F2)).card := by
      refine (Finset.card_bij (fun y _ => x0 + iota y) (fun y _ => hmemX y) ?_ ?_).symm
      · intro y₁ _ y₂ _ h
        apply hiota_inj
        ext i
        have hi := congrFun h i
        have hi' : x0 i + (x0 i + iota y₁ i) = x0 i + (x0 i + iota y₂ i) := congrArg (x0 i + ·) hi
        simp only [← add_assoc, zmod2_add_self, zero_add] at hi'
        exact hi'
      · intro x hx
        rcases (hbijX x hx).exists with ⟨y, hy⟩
        exact ⟨y, Finset.mem_univ y, hy⟩
    rw [hbij]
    simp [Fintype.card_fun, ZMod.card]
  have hsumX : ∀ (F : (Fin k → F2) → ℕ),
      (∑ x ∈ X, F x) = ∑ y : Fin d → F2, F (x0 + iota y) := by
    intro F
    refine (Finset.sum_bij (fun y _ => x0 + iota y) (fun y _ => hmemX y) ?_ ?_ (fun _ _ => rfl)).symm
    · intro y₁ _ y₂ _ h
      apply hiota_inj
      ext i
      have hi := congrFun h i
      have hi' : x0 i + (x0 i + iota y₁ i) = x0 i + (x0 i + iota y₂ i) := congrArg (x0 i + ·) hi
      simp only [← add_assoc, zmod2_add_self, zero_add] at hi'
      exact hi'
    · intro x hx
      rcases (hbijX x hx).exists with ⟨y, hy⟩
      exact ⟨y, Finset.mem_univ y, hy⟩
  let rho : (Fin k → F2) → (Fin d → F2) := fun w r => w (free r) + w p0
  have hadj : ∀ (y : Fin d → F2) (w : Fin k → F2), dotProduct (iota y) w = dotProduct y (rho w) := by
    intro y w
    simp only [dotProduct]
    rw [hsum_split (fun i => iota y i * w i)]
    have hP0 : (∑ i ∈ P, iota y i * w i) = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [hiota_P y i hi, zero_mul])
    rw [hP0, zero_add, hiota_p0, Finset.sum_mul]
    simp only [hiota_free, rho, mul_add, Finset.sum_add_distrib]
    ring
  have hrho_zero_wt : ∀ w : Fin k → F2, rho w = 0 →
      (Finset.univ.filter (fun i : Fin k => w i = 1)).card ≤ k / 32 ∨
      k - k / 32 ≤ (Finset.univ.filter (fun i : Fin k => w i = 1)).card := by
    intro w hr0
    have hconst : ∀ r : Fin d, w (free r) = w p0 := by
      intro r
      have h := congrFun hr0 r
      simp only [rho, Pi.zero_apply] at h
      have h' : w (free r) + w p0 + w p0 = 0 + w p0 := congrArg (· + w p0) h
      rwa [add_assoc, zmod2_add_self, add_zero, zero_add] at h'
    rcases zmod2_eq_zero_or_one (w p0) with hp0 | hp1
    · left
      have hsub : Finset.univ.filter (fun i : Fin k => w i = 1) ⊆ P := by
        intro i hi
        have hw1 : w i = 1 := (Finset.mem_filter.mp hi).2
        rcases hpart_univ i with hiP | rfl | ⟨r, rfl⟩
        · exact hiP
        · rw [hp0] at hw1; exact absurd hw1 (by decide)
        · rw [hconst r, hp0] at hw1; exact absurd hw1 (by decide)
      exact le_trans (Finset.card_le_card hsub) hP
    · right
      have hsub : Pc ⊆ Finset.univ.filter (fun i : Fin k => w i = 1) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hi_notP : i ∉ P := (Finset.mem_sdiff.mp hi).2
        rcases hpart_univ i with hiP | rfl | ⟨r, rfl⟩
        · exact (hi_notP hiP).elim
        · exact hp1
        · rw [hconst r, hp1]
      have hle := Finset.card_le_card hsub
      rw [hPc_card] at hle
      omega
  let u : Fin m → Fin d → F2 := fun j => rho (v j)
  let c0 : Fin m → F2 := fun j => dotProduct x0 (v j)
  have hdot_eq : ∀ (y : Fin d → F2) (j : Fin m),
      dotProduct (x0 + iota y) (v j) = dotProduct y (u j) + c0 j := by
    intro y j
    rw [dotProduct_add_left, hadj, add_comm]
  have h4wise : ∀ S : Finset (Fin m), 1 ≤ S.card → S.card ≤ 4 → (∑ j ∈ S, u j) ≠ 0 := by
    intro S h1 h4 h0
    have hsum_rho : (∑ j ∈ S, u j) = rho (fun i => ∑ j ∈ S, v j i) := by
      ext r
      simp only [Finset.sum_apply, u, rho, Finset.sum_add_distrib]
    rw [hsum_rho] at h0
    have hwt := hrho_zero_wt (fun i => ∑ j ∈ S, v j i) h0
    have hgood := hindep S h1 h4
    omega
  have hu_ne0 : ∀ j : Fin m, u j ≠ 0 := by
    intro j
    have h := h4wise {j} (by simp) (by simp)
    simpa using h
  have hu_inj : Function.Injective u := by
    intro j₁ j₂ heq
    by_contra hne
    have h := h4wise {j₁, j₂} (by rw [Finset.card_pair hne]; omega) (by rw [Finset.card_pair hne]; omega)
    rw [Finset.sum_pair hne, heq] at h
    apply h
    ext r; exact zmod2_add_self _
  have hu_bias : ∀ a : Fin d → F2, a ≠ 0 → 14 * |∑ j : Fin m, chi (dotProduct a (u j))| ≤ (m : ℤ) := by
    intro a ha
    have h := hbias (iota a) (hiota_ne0 a ha)
    have heq : (∑ j : Fin m, chi (dotProduct a (u j))) = ∑ j : Fin m, chi (dotProduct (iota a) (v j)) :=
      Finset.sum_congr rfl (fun j _ => by rw [hadj])
    rwa [heq]
  exact ⟨x0, iota, u, c0, hiota_add, hXcard, hsumX, hdot_eq, h4wise, hu_ne0, hu_inj, hu_bias⟩

lemma slice_circuit_lower_bound (k m : ℕ) (hk : 128 ≤ k) (hm1 : 512 * k ≤ m)
    (v : Fin m → Fin k → F2)
    (hbias : ∀ w : Fin k → F2, w ≠ 0 → 14 * |∑ j : Fin m, chi (dotProduct w (v j))| ≤ (m : ℤ))
    (hindep : ∀ S : Finset (Fin m), 1 ≤ S.card → S.card ≤ 4 →
      k / 32 < (Finset.univ.filter (fun i : Fin k => (∑ j ∈ S, v j i) = 1)).card ∧
      (Finset.univ.filter (fun i : Fin k => (∑ j ∈ S, v j i) = 1)).card < k - k / 32)
    (J : Finset (Fin m)) (hJm : m ≤ 2 * J.card)
    (P : Finset (Fin k)) (hP : P.card ≤ k / 32) (pins : Fin k → F2) (par : F2)
    (C : Circuit) (hRB : ReadsBack k C) (hL : ∀ z ∈ C.gates, LegalGate z)
    (dec : Bool → Fin m → Bool) :
    let X := (Finset.univ : Finset (Fin k → F2)).filter (fun x =>
      (∀ i ∈ P, x i = pins i) ∧ (∑ i : Fin k, x i) = par)
    let maj := fun x : Fin k → F2 => decide
      (J.card ≤ 2 * (J.filter (fun j => dotProduct x (v j) = 1)).card)
    let bit := fun (x : Fin k → F2) =>
      C.eval (List.ofFn (fun i : Fin k => decide (x i = 1)))
    let gain := fun (f : (Fin k → F2) → Fin m → Bool) =>
      2 * (∑ x ∈ X, (J.filter (fun j => f x j = decide (dotProduct x (v j) = 1))).card) -
        X.card * J.card
    9 * gain (fun x _ => maj x) ≤ 10 * gain (fun x j => dec (bit x) j) →
      k ≤ 2 * andCost C.gates + P.card + 4 := by
  intro X maj bit gain happrox
  by_contra hlt
  push_neg at hlt
  let d := k - P.card - 1
  have hd_ge : 2 * andCost C.gates + 4 ≤ d := by omega
  rcases slice_param_exists k m hk v hbias hindep P hP pins par with
    ⟨x0, iota, u, c0, hiota_add, hXcard, hsumX, hdot_eq, h4wise, hu_ne0, hu_inj, hu_bias⟩
  rcases maj_gain_lower_bound J u c0 h4wise with ⟨hmaj_nn, hmaj_sq⟩
  let majGainZ : ℤ :=
    2 * (∑ y : Fin d → F2, ((J.filter (fun j => decide (J.card ≤ 2 * (J.filter (fun j' => dotProduct y (u j') + c0 j' = 1)).card) =
      decide (dotProduct y (u j) + c0 j = 1))).card : ℤ)) - (2 ^ d : ℤ) * (J.card : ℤ)
  have hXcard' : X.card = 2 ^ d := hXcard
  have hmaj_nat_eq : (gain (fun x _ => maj x) : ℤ) = majGainZ := by
    simp only [gain]
    rw [hXcard', hsumX (fun x => (J.filter (fun j => maj x = decide (dotProduct x (v j) = 1))).card)]
    have hsum_eq : (∑ y : Fin d → F2,
        (J.filter (fun j => maj (x0 + iota y) = decide (dotProduct (x0 + iota y) (v j) = 1))).card) =
        ∑ y : Fin d → F2,
          (J.filter (fun j => decide (J.card ≤ 2 * (J.filter (fun j' => dotProduct y (u j') + c0 j' = 1)).card) =
            decide (dotProduct y (u j) + c0 j = 1))).card := by
      refine Finset.sum_congr rfl (fun y _ => ?_)
      simp only [maj, hdot_eq]
    rw [hsum_eq]
    have hle : 2 ^ d * J.card ≤ 2 * ∑ y : Fin d → F2,
        (J.filter (fun j => decide (J.card ≤ 2 * (J.filter (fun j' => dotProduct y (u j') + c0 j' = 1)).card) =
          decide (dotProduct y (u j) + c0 j = 1))).card := by
      have hcast : ((2 ^ d * J.card : ℕ) : ℤ) ≤ ((2 * ∑ y : Fin d → F2,
          (J.filter (fun j => decide (J.card ≤ 2 * (J.filter (fun j' => dotProduct y (u j') + c0 j' = 1)).card) =
            decide (dotProduct y (u j) + c0 j = 1))).card : ℕ) : ℤ) := by
        push_cast
        have hnn : (0 : ℤ) ≤ majGainZ := hmaj_nn
        simp only [majGainZ] at hnn
        linarith
      exact Int.ofNat_le.mp hcast
    rw [Nat.cast_sub hle]
    push_cast
    rfl
  rcases circuit_wire_decomp x0 iota hiota_add C hRB hL with
    ⟨vecs, cW, alphaW, hW, hvecs_len, hrepW, hinvW⟩
  let K : Finset (Fin d → F2) := Finset.univ.filter (fun z => ∀ a ∈ vecs, dotProduct a z = 0)
  have hK0 : (0 : Fin d → F2) ∈ K := by
    simp [K, dotProduct_zero_right]
  have hKadd : ∀ z₁ ∈ K, ∀ z₂ ∈ K, z₁ + z₂ ∈ K := by
    intro z₁ hz₁ z₂ hz₂
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and] at hz₁ hz₂ ⊢
    intro a ha
    rw [dotProduct_add_right, hz₁ a ha, hz₂ a ha, add_zero]
  have hKcard : 16 ≤ K.card := by
    have h := kernel_card_ge vecs
    have hpow : 2 ^ (vecs.length + 4) ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_add] at hpow
    have h4 : (2 : ℕ) ^ 4 = 16 := by norm_num
    rw [h4] at hpow
    have hmul : 2 ^ vecs.length * 16 ≤ 2 ^ vecs.length * K.card := le_trans hpow h
    exact Nat.le_of_mul_le_mul_left hmul (by positivity)
  let gBit : (Fin d → F2) → Bool := fun y => bit (x0 + iota y)
  have hg_decomp : ∃ (cOut : F2) (alphaOut : Fin d → F2) (hOut : (Fin d → F2) → F2),
      (∀ y, boolToF2 (gBit y) = cOut + dotProduct alphaOut y + hOut y) ∧
      (∀ y, ∀ z ∈ K, hOut (y + z) = hOut y) := by
    by_cases hout : C.output < k + C.gates.length
    · refine ⟨cW C.output, alphaW C.output, hW C.output, ?_, ?_⟩
      · intro y
        exact hrepW C.output hout y
      · intro y z hz
        exact hinvW C.output hout y z (Finset.mem_filter.mp hz).2
    · refine ⟨0, 0, fun _ => 0, ?_, by simp⟩
      intro y
      have hlenw : (Circuit.wires C (List.ofFn (fun i : Fin k => decide ((x0 + iota y) i = 1)))).length =
          k + C.gates.length := by
        rw [Circuit.wires, foldl_wires_length, List.length_ofFn]
      have hfalse : gBit y = false := by
        simp only [gBit, bit, Circuit.eval]
        rw [List.getD_eq_default _ _ (by omega)]
      simp [hfalse, boolToF2, dotProduct_zero_left]
  rcases hg_decomp with ⟨cOut, alphaOut, hOut, hg_rep, hh_inv⟩
  let decGainZ : ℤ :=
    2 * (∑ y : Fin d → F2, ((J.filter (fun j => dec (gBit y) j = decide (dotProduct y (u j) + c0 j = 1))).card : ℤ)) -
      (2 ^ d : ℤ) * (J.card : ℤ)
  have hdec_nat_le : (gain (fun x j => dec (bit x) j) : ℤ) ≤ max 0 decGainZ := by
    simp only [gain]
    rw [hXcard', hsumX (fun x => (J.filter (fun j => dec (bit x) j = decide (dotProduct x (v j) = 1))).card)]
    have hsum_eq : (∑ y : Fin d → F2,
        (J.filter (fun j => dec (bit (x0 + iota y)) j = decide (dotProduct (x0 + iota y) (v j) = 1))).card) =
        ∑ y : Fin d → F2,
          (J.filter (fun j => dec (gBit y) j = decide (dotProduct y (u j) + c0 j = 1))).card := by
      refine Finset.sum_congr rfl (fun y _ => ?_)
      simp only [gBit, hdot_eq]
    rw [hsum_eq]
    by_cases hle : 2 ^ d * J.card ≤ 2 * ∑ y : Fin d → F2,
        (J.filter (fun j => dec (gBit y) j = decide (dotProduct y (u j) + c0 j = 1))).card
    · rw [Nat.cast_sub hle]
      push_cast
      exact le_max_right 0 _
    · have h0 : 2 * (∑ y : Fin d → F2,
          (J.filter (fun j => dec (gBit y) j = decide (dotProduct y (u j) + c0 j = 1))).card) -
          2 ^ d * J.card = 0 := Nat.sub_eq_zero_of_le (le_of_not_ge hle)
      rw [h0, Nat.cast_zero]
      exact le_max_left 0 _
  have h9_10 : 9 * majGainZ ≤ 10 * max 0 decGainZ := by
    have happroxZ : 9 * (gain (fun x _ => maj x) : ℤ) ≤ 10 * (gain (fun x j => dec (bit x) j) : ℤ) := by
      exact_mod_cast happrox
    rw [hmaj_nat_eq] at happroxZ
    linarith
  have hdec_ub := circuit_gain_upper_bound J u c0 gBit dec K cOut alphaOut hOut
    hK0 hKadd hKcard hg_rep hh_inv hu_ne0 hu_inj hu_bias
  exact slice_final_contradiction d m J.card majGainZ decGainZ (by omega) hJm
    hmaj_sq h9_10 hmaj_nn hdec_ub

end PEqualNP.Outside.L_meta_29727_aux

theorem PEqualNP.Outside.L_meta_29727 :
    ∀ k : ℕ, 128 ≤ k →
      let F := ZMod 2
      let V := Fin k → F
      ∃ t : ℕ, let m := 2^t
        512*k ≤ m ∧ m < 1024*k ∧
        ∃ (s : Fin (2^(k+m-1))) (B : PEqualNP.CircuitLowerBounds.Circuit),
          let v := fun (j : Fin m) (i : Fin k) =>
            if s.val.testBit (j.val+i.val) then (1 : F) else 0
          PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+t) B ∧
          B.output < k+t+B.size ∧ B.size ≤ 3080*k+3*k*t ∧
          (∀ gate ∈ B.gates, gate.inputs.length ≤ 2 ∧
            (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))) ∧
          (∀ (row : Fin k → Bool) (j : Fin m),
            B.eval (List.ofFn row ++ List.ofFn (fun z : Fin t => j.val.testBit z.val)) =
              decide (dotProduct (fun i => if row i then 1 else 0) (v j) = 1)) ∧
          ∀ (J : Finset (Fin m)), m ≤ 2*J.card →
            let maj := fun x : V => decide
              (J.card ≤ 2*(J.filter (fun j => dotProduct x (v j) = 1)).card)
            let legal := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
              PEqualNP.MetaComplexity.NestedCover.ReadsBack k C ∧
              (∀ z ∈ C.gates, (z.op = .and ∧ z.inputs.length = 2) ∨
                (z.op = .mod 2 ∧ z.inputs.length ≤ 2) ∨
                (z.op = .not ∧ z.inputs.length = 1))
            let cost := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
              C.gates.countP (fun z => @decide (z.op = .and) (Classical.propDecidable _))
            let bit := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (x : V) =>
              C.eval (List.ofFn (fun i : Fin k => decide (x i = 1)))
            (∃ H, legal H ∧ H.output < k+H.size ∧ cost H ≤ J.card-1 ∧ ∀ x, bit H x = maj x) ∧
            ∀ (P : Finset (Fin k)), P.card ≤ k/32 → ∀ (pins : V) (par : F),
              let X := (Finset.univ : Finset V).filter (fun x =>
                (∀ i ∈ P, x i = pins i) ∧ (∑ i : Fin k, x i) = par)
              let gain := fun (f : V → Fin m → Bool) =>
                2*(∑ x ∈ X, (J.filter (fun j => f x j = decide (dotProduct x (v j) = 1))).card) -
                  X.card*J.card
              ∀ C, legal C → ∀ dec : Bool → Fin m → Bool,
                9*gain (fun x _ => maj x) ≤ 10*gain (fun x j => dec (bit C x) j) →
                  k ≤ 2*cost C+P.card+4 := by
  intro k hk F V
  rcases PEqualNP.Outside.L_meta_29727_aux.exists_pow2_window k hk with ⟨t, hm1, hm2⟩
  refine ⟨t, hm1, hm2, ?_⟩
  rcases PEqualNP.Outside.L_meta_29727_aux.exists_good_tape k (2 ^ t) hk hm1 hm2 with
    ⟨s, hbias, hindep⟩
  rcases PEqualNP.Outside.L_meta_29727_aux.exists_small_eval_circuit k t hk hm2 s with
    ⟨B, hBRB, hBout, hBsize, hBAON, hBeval⟩
  refine ⟨s, B, hBRB, hBout, hBsize, hBAON, hBeval, ?_⟩
  intro J hJm
  refine ⟨?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_29727_aux.exists_exact_maj_circuit k (2 ^ t)
      (fun j i => if s.val.testBit (j.val + i.val) then (1 : F) else 0) J (by omega)
  · intro P hP pins par X gain C hC dec happrox
    exact PEqualNP.Outside.L_meta_29727_aux.slice_circuit_lower_bound k (2 ^ t) hk hm1
      (fun j i => if s.val.testBit (j.val + i.val) then (1 : F) else 0)
      hbias hindep J hJm P hP pins par C hC.1 hC.2 dec happrox

