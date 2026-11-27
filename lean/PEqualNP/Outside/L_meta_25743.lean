import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25743_aux

def bSign (b : Bool) : ℤ := if b then -1 else 1

lemma bSign_xor (a b : Bool) : bSign (xor a b) = bSign a * bSign b := by
  cases a <;> cases b <;> rfl

lemma bSign_sq (b : Bool) : bSign b * bSign b = 1 := by
  cases b <;> rfl

lemma bSign_ne_eq (a b : Bool) :
    (if a ≠ b then (2 : ℤ) else 0) = 1 - bSign a * bSign b := by
  cases a <;> cases b <;> decide

lemma bSign_not (b : Bool) : bSign (!b) = -bSign b := by
  cases b <;> rfl

lemma nat_le_two_pow_pred (a : ℕ) (ha : 2 ≤ a) : a ≤ 2 ^ (a - 1) := by
  induction a with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 1
    · subst hn; norm_num
    · have hih := ih (by omega)
      have hsub : n + 1 - 1 = (n - 1) + 1 := by omega
      rw [hsub, pow_succ]
      omega

lemma two_pow_ge_two_mul (b : ℕ) (hb : 1 ≤ b) : b ≤ 2 ^ b := by
  induction b with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn; norm_num
    · have := ih (by omega)
      rw [pow_succ]
      omega

lemma mul_add_lt_mul {q M j b : ℕ} (hq : q < M) (hj : j < b) : q * b + j < M * b := by
  have h1 : q * b + j < (q + 1) * b := by rw [Nat.add_mul, one_mul]; omega
  exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right b hq)

lemma bernoulli_half (b M : ℕ) (hb : 1 ≤ b) (hM : 1 ≤ M) (h2M : 2 ^ b ≤ 2 * M) :
    2 * (2 ^ b - 2) ^ M ≤ (2 ^ b) ^ M := by
  by_cases hb1 : b = 1
  · subst hb1
    simp only [pow_one, Nat.sub_self, zero_pow (by omega : M ≠ 0), mul_zero]
    exact Nat.zero_le _
  · have hge2 : 2 ≤ 2 ^ b := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
    have hsplit : 2 ^ b = (2 ^ b - 2) + 2 := (Nat.sub_add_cancel hge2).symm
    have hbin : ∀ m : ℕ, 1 ≤ m → (2 ^ b - 2) ^ m + 2 * m * (2 ^ b - 2) ^ (m - 1) ≤ (2 ^ b) ^ m := by
      intro m hm
      induction m with
      | zero => omega
      | succ n ih =>
        by_cases hn : n = 0
        · subst hn
          simp only [zero_add, pow_one, Nat.sub_self, pow_zero, mul_one]
          omega
        · have hih := ih (by omega)
          have hpow1 : (2 ^ b) ^ (n + 1) = (2 ^ b) ^ n * ((2 ^ b - 2) + 2) := by
            rw [pow_succ, ← hsplit]
          have hsub : n = (n - 1) + 1 := by omega
          have hpow2 : (2 ^ b - 2) ^ n = (2 ^ b - 2) ^ (n - 1) * (2 ^ b - 2) := by
            conv_lhs => rw [hsub, pow_succ]
          calc (2 ^ b - 2) ^ (n + 1) + 2 * (n + 1) * (2 ^ b - 2) ^ n
              = (2 ^ b - 2) ^ n * (2 ^ b - 2) + 2 * n * (2 ^ b - 2) ^ n + 2 * (2 ^ b - 2) ^ n := by
                  rw [pow_succ]; ring
            _ = ((2 ^ b - 2) ^ n + 2 * n * (2 ^ b - 2) ^ (n - 1)) * (2 ^ b - 2) +
                  2 * (2 ^ b - 2) ^ n := by
                  rw [hpow2]; ring
            _ ≤ ((2 ^ b - 2) ^ n + 2 * n * (2 ^ b - 2) ^ (n - 1)) * (2 ^ b - 2) +
                  ((2 ^ b - 2) ^ n + 2 * n * (2 ^ b - 2) ^ (n - 1)) * 2 := by
                  have : 2 * (2 ^ b - 2) ^ n ≤
                      ((2 ^ b - 2) ^ n + 2 * n * (2 ^ b - 2) ^ (n - 1)) * 2 := by omega
                  omega
            _ = ((2 ^ b - 2) ^ n + 2 * n * (2 ^ b - 2) ^ (n - 1)) * ((2 ^ b - 2) + 2) := by ring
            _ ≤ (2 ^ b) ^ n * ((2 ^ b - 2) + 2) := Nat.mul_le_mul_right _ hih
            _ = (2 ^ b) ^ (n + 1) := hpow1.symm
    have hMsub : (2 ^ b - 2) ^ M = (2 ^ b - 2) * (2 ^ b - 2) ^ (M - 1) := by
      conv_lhs => rw [show M = (M - 1) + 1 by omega, pow_succ, Nat.mul_comm]
    have hle : (2 ^ b - 2) ^ M ≤ 2 * M * (2 ^ b - 2) ^ (M - 1) := by
      rw [hMsub]
      exact Nat.mul_le_mul_right _ (by omega)
    have hbM := hbin M hM
    omega

lemma thin_order {α : Type*} [DecidableEq α] (K : α → α → ℤ)
    (hsym : ∀ x y, K x y = K y x) (hdiag : ∀ x, K x x = 1)
    (s : Finset α) (hinit : (s.card : ℤ) ^ 2 ≤ 4 * ∑ x ∈ s, ∑ y ∈ s, K x y) :
    ∃ l : List α, l.Nodup ∧ l.toFinset = s ∧
      ∀ t ≤ s.card, (t : ℤ) ^ 2 ≤ 4 * ∑ x ∈ (l.take t).toFinset, ∑ y ∈ (l.take t).toFinset, K x y := by
  induction hn : s.card generalizing s with
  | zero =>
    have hs : s = ∅ := Finset.card_eq_zero.mp hn
    subst hs
    refine ⟨[], List.nodup_nil, rfl, ?_⟩
    intro t ht
    have ht0 : t = 0 := by omega
    subst ht0; simp
  | succ m ih =>
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    let deg : α → ℤ := fun u => ∑ y ∈ s, K u y
    obtain ⟨u, hu, hmin⟩ := Finset.exists_min_image s deg hne
    let s' := s.erase u
    have hs'_card : s'.card = m := by rw [Finset.card_erase_of_mem hu, hn]; omega
    have hdeg_le : (m + 1 : ℤ) * deg u ≤ ∑ x ∈ s, ∑ y ∈ s, K x y := by
      calc (m + 1 : ℤ) * deg u
          = ∑ _x ∈ s, deg u := by simp [hn]
        _ ≤ ∑ x ∈ s, deg x := Finset.sum_le_sum (fun x hx => hmin x hx)
        _ = ∑ x ∈ s, ∑ y ∈ s, K x y := rfl
    have hdel : (∑ x ∈ s', ∑ y ∈ s', K x y) = (∑ x ∈ s, ∑ y ∈ s, K x y) - 2 * deg u + 1 := by
      have h1 : (∑ x ∈ s, ∑ y ∈ s, K x y) =
          (∑ y ∈ s, K u y) + ∑ x ∈ s', ∑ y ∈ s, K x y :=
        (Finset.add_sum_erase s (fun x => ∑ y ∈ s, K x y) hu).symm
      have h2 : (∑ x ∈ s', ∑ y ∈ s, K x y) =
          (∑ x ∈ s', K x u) + ∑ x ∈ s', ∑ y ∈ s', K x y := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro x _
        exact (Finset.add_sum_erase s (fun y => K x y) hu).symm
      have h3 : (∑ x ∈ s', K x u) = deg u - 1 := by
        have hu1 : deg u = K u u + ∑ y ∈ s', K u y :=
          (Finset.add_sum_erase s (fun y => K u y) hu).symm
        have hsym_sum : (∑ x ∈ s', K x u) = ∑ y ∈ s', K u y :=
          Finset.sum_congr rfl (fun x _ => hsym x u)
        rw [hsym_sum]
        rw [hdiag u] at hu1
        omega
      rw [h1, h2, h3]
      dsimp only [deg]
      ring
    have hinit' : (s'.card : ℤ) ^ 2 ≤ 4 * ∑ x ∈ s', ∑ y ∈ s', K x y := by
      rw [hs'_card, hdel]
      by_cases hm0 : m = 0
      · subst hm0
        have hs'e : s' = ∅ := Finset.card_eq_zero.mp hs'_card
        have hsum0 : (∑ x ∈ s', ∑ y ∈ s', K x y) = 0 := by rw [hs'e]; simp
        rw [← hdel, hsum0]; simp
      · have hmul : (m + 1 : ℤ) * (4 * ((∑ x ∈ s, ∑ y ∈ s, K x y) - 2 * deg u + 1)) ≥
            (m + 1 : ℤ) * (m : ℤ) ^ 2 := by
          have hm1 : (0 : ℤ) ≤ (m : ℤ) - 1 := by omega
          have hinit_m : ((m + 1 : ℤ)) ^ 2 ≤ 4 * ∑ x ∈ s, ∑ y ∈ s, K x y := by
            simpa [hn] using hinit
          nlinarith
        nlinarith
    obtain ⟨l', hnd', hto', hpref'⟩ := ih s' hinit' hs'_card
    have hu_not_l' : u ∉ l' := by
      intro hmem
      have : u ∈ s' := hto' ▸ List.mem_toFinset.mpr hmem
      exact (Finset.mem_erase.mp this).1 rfl
    have hto_u : (l' ++ [u]).toFinset = s := by
      rw [List.toFinset_append, hto', List.toFinset_cons, List.toFinset_nil, Finset.union_comm,
        Finset.insert_union, Finset.empty_union, Finset.insert_erase hu]
    refine ⟨l' ++ [u], ?_, hto_u, ?_⟩
    · rw [List.nodup_append]
      exact ⟨hnd', List.nodup_singleton u, fun a ha b hb => by
        rw [List.mem_singleton.mp hb]; rintro rfl; exact hu_not_l' ha⟩
    · intro t ht
      by_cases htm : t ≤ m
      · have hlen : l'.length = m := by
          rw [← List.toFinset_card_of_nodup hnd', hto', hs'_card]
        rw [List.take_append_of_le_length (by omega)]
        exact hpref' t (by omega)
      · have ht_eq : t = m + 1 := by omega
        subst ht_eq
        have hlen : (l' ++ [u]).length = m + 1 := by
          rw [List.length_append, List.length_singleton, ← List.toFinset_card_of_nodup hnd', hto', hs'_card]
        rw [List.take_of_length_le (by omega), hto_u]
        simpa [hn] using hinit

lemma perm_of_equal_fibers {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (f g : α → β)
    (hcard : ∀ b : β, (Finset.univ.filter (fun a => f a = b)).card =
      (Finset.univ.filter (fun a => g a = b)).card) :
    ∃ π : Equiv.Perm α, ∀ a : α, g (π a) = f a := by
  classical
  let ef : α ≃ Σ b : β, {a : α // f a = b} :=
    { toFun := fun a => ⟨f a, ⟨a, rfl⟩⟩
      invFun := fun p => p.2.1
      left_inv := fun _ => rfl
      right_inv := fun ⟨b, ⟨a, ha⟩⟩ => by subst ha; rfl }
  let eg : α ≃ Σ b : β, {a : α // g a = b} :=
    { toFun := fun a => ⟨g a, ⟨a, rfl⟩⟩
      invFun := fun p => p.2.1
      left_inv := fun _ => rfl
      right_inv := fun ⟨b, ⟨a, ha⟩⟩ => by subst ha; rfl }
  have hfib : ∀ b : β, Nonempty ({a : α // f a = b} ≃ {a : α // g a = b}) := by
    intro b
    apply Fintype.card_eq.mp
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact hcard b
  let eFib : ∀ b : β, {a : α // f a = b} ≃ {a : α // g a = b} := fun b => Classical.choice (hfib b)
  let eMid : (Σ b : β, {a : α // f a = b}) ≃ (Σ b : β, {a : α // g a = b}) :=
    Equiv.sigmaCongrRight eFib
  refine ⟨ef.trans (eMid.trans eg.symm), ?_⟩
  intro a
  exact (eFib (f a) ⟨a, rfl⟩).2

lemma list_to_perm {N : ℕ} (l : List (Fin N)) (hnd : l.Nodup) (hfull : l.toFinset = Finset.univ) :
    ∃ order : Equiv.Perm (Fin N), ∀ h ≤ N,
      Finset.univ.filter (fun i : Fin N => (order i).val < h) = (l.take h).toFinset := by
  have hlen : l.length = N := by
    rw [← List.toFinset_card_of_nodup hnd, hfull, Finset.card_univ, Fintype.card_fin]
  have hbij : Function.Bijective (fun i : Fin N => l.get ⟨i.val, by omega⟩) := by
    have hinj : Function.Injective (fun i : Fin N => l.get ⟨i.val, by omega⟩) := by
      intro i1 i2 hEq
      have h := (List.nodup_iff_injective_get.mp hnd) hEq
      exact Fin.ext (congrArg (fun x : Fin l.length => x.val) h)
    exact ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  let idx : Fin N ≃ Fin N := Equiv.ofBijective _ hbij
  refine ⟨idx.symm, ?_⟩
  intro h _
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
  constructor
  · intro hlt
    have hx : x = l.get ⟨(idx.symm x).val, by omega⟩ := (idx.apply_symm_apply x).symm
    rw [hx]
    have htake : l.get ⟨(idx.symm x).val, by omega⟩ =
        (l.take h).get ⟨(idx.symm x).val, by rw [List.length_take]; omega⟩ := by
      simp [List.get_eq_getElem]
    rw [htake]
    exact List.get_mem _ _
  · intro hmem
    rw [List.mem_iff_getElem] at hmem
    rcases hmem with ⟨j, hj, hEq⟩
    have hjh : j < h := by rw [List.length_take] at hj; omega
    have hjN : j < N := by rw [List.length_take] at hj; omega
    have hget : idx ⟨j, hjN⟩ = x := by
      change l.get ⟨j, by omega⟩ = x
      rw [List.get_eq_getElem, ← hEq, List.getElem_take]
    have hsym : idx.symm x = ⟨j, hjN⟩ := by rw [← hget, idx.symm_apply_apply]
    rw [hsym]
    exact hjh

lemma sum_two_pow_lt (n : ℕ) : (∑ j ∈ Finset.range n, 2 ^ j) < 2 ^ n := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, pow_succ]; omega

lemma sum_bits_lt (n : ℕ) (g : ℕ → Bool) :
    (∑ j ∈ Finset.range n, if g j then 2 ^ j else 0) < 2 ^ n := by
  calc (∑ j ∈ Finset.range n, if g j then 2 ^ j else 0)
      ≤ ∑ j ∈ Finset.range n, 2 ^ j :=
        Finset.sum_le_sum (fun j _ => by split_ifs; exact le_rfl; exact Nat.zero_le _)
    _ < 2 ^ n := sum_two_pow_lt n

lemma sum_bits_testBit (n : ℕ) (g : ℕ → Bool) (i : ℕ) :
    (∑ j ∈ Finset.range n, if g j then 2 ^ j else 0).testBit i = if i < n then g i else false := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hltm : (∑ j ∈ Finset.range m, if g j then 2 ^ j else 0) < 2 ^ m := sum_bits_lt m g
    by_cases hgm : g m = true
    · simp only [hgm, ite_true]
      have hadd : (∑ j ∈ Finset.range m, if g j then 2 ^ j else 0) + 2 ^ m =
          (∑ j ∈ Finset.range m, if g j then 2 ^ j else 0) ||| 2 ^ m := by
        rw [Nat.add_comm, ← Nat.mul_one (2 ^ m), Nat.two_pow_add_eq_or_of_lt hltm, Nat.mul_one, Nat.or_comm]
      rw [hadd, Nat.testBit_or, ih, Nat.testBit_two_pow]
      by_cases him : i < m
      · have hne : m ≠ i := by omega
        have hlt' : i < m + 1 := by omega
        simp [him, hne, hlt']
      · by_cases hieq : i = m
        · subst hieq; simp [hgm]
        · have hne : m ≠ i := by omega
          have hnot : ¬ i < m + 1 := by omega
          simp [him, hne, hnot]
    · have hgf : g m = false := Bool.eq_false_iff.mpr hgm
      simp only [hgf, Bool.false_eq_true, ite_false, Nat.add_zero]
      rw [ih]
      by_cases him : i < m
      · have hlt' : i < m + 1 := by omega
        simp [him, hlt']
      · by_cases hieq : i = m
        · subst hieq; simp [hgf]
        · have hnot : ¬ i < m + 1 := by omega
          simp [him, hnot]

def fin_bit_equiv (k : ℕ) : (Fin (2 ^ k)) ≃ (Fin k → Bool) :=
  { toFun := fun x j => x.val.testBit j.val
    invFun := fun f => ⟨∑ j : Fin k, if f j then 2 ^ j.val else 0, by
      calc (∑ j : Fin k, if f j then 2 ^ j.val else 0)
          ≤ ∑ j : Fin k, 2 ^ j.val :=
            Finset.sum_le_sum (fun j _ => by split_ifs; exact le_rfl; exact Nat.zero_le _)
        _ = ∑ j ∈ Finset.range k, 2 ^ j := Fin.sum_univ_eq_sum_range (fun j => 2 ^ j) k
        _ < 2 ^ k := sum_two_pow_lt k⟩
    left_inv := fun x => by
      ext
      apply Nat.eq_of_testBit_eq
      intro i
      dsimp only
      have hrew : (∑ j : Fin k, if x.val.testBit j.val then 2 ^ j.val else 0) =
          ∑ j ∈ Finset.range k, if x.val.testBit j then 2 ^ j else 0 :=
        Fin.sum_univ_eq_sum_range (fun j => if x.val.testBit j then 2 ^ j else 0) k
      rw [hrew, sum_bits_testBit]
      by_cases hik : i < k
      · simp [hik]
      · simp only [hik, ite_false]
        exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (by omega)))).symm
    right_inv := fun f => by
      ext j
      dsimp only
      let g : ℕ → Bool := fun t => if h : t < k then f ⟨t, h⟩ else false
      have hrew : (∑ t : Fin k, if f t then 2 ^ t.val else 0) =
          ∑ t ∈ Finset.range k, if g t then 2 ^ t else 0 := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl; intro t _
        simp [g, t.isLt]
      rw [hrew, sum_bits_testBit]
      simp [g, j.isLt] }

lemma fin_bit_equiv_testBit (k : ℕ) (x : Fin (2 ^ k)) (j : Fin k) :
    fin_bit_equiv k x j = x.val.testBit j.val := rfl

lemma card_mod_fiber (k a : ℕ) (hak : a ≤ k) (j : Fin (2 ^ a)) :
    (Finset.univ.filter (fun z : Fin (2 ^ k) => z.val % 2 ^ a = j.val)).card = 2 ^ k / 2 ^ a := by
  have hdiv : 2 ^ k / 2 ^ a = 2 ^ (k - a) := by
    rw [← Nat.pow_sub_mul_pow 2 hak, Nat.mul_div_cancel _ (by positivity)]
  rw [hdiv]
  let e : Fin (2 ^ (k - a)) → Fin (2 ^ k) := fun q =>
    ⟨q.val * 2 ^ a + j.val, by
      have h1 : q.val + 1 ≤ 2 ^ (k - a) := q.isLt
      have h2 : (q.val + 1) * 2 ^ a ≤ 2 ^ (k - a) * 2 ^ a := Nat.mul_le_mul_right _ h1
      rw [Nat.pow_sub_mul_pow 2 hak] at h2
      have := j.isLt
      nlinarith⟩
  have hcard : (Finset.univ : Finset (Fin (2 ^ (k - a)))).card = 2 ^ (k - a) := by simp
  rw [← hcard]
  symm
  refine Finset.card_bij (fun q _ => e q) ?_ ?_ ?_
  · intro q _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    dsimp only [e]
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt j.isLt]
  · intro q1 _ q2 _ hEq
    have hval := congrArg Fin.val hEq
    dsimp only [e] at hval
    have hpos : 0 < 2 ^ a := by positivity
    ext
    have : q1.val * 2 ^ a = q2.val * 2 ^ a := by omega
    exact Nat.eq_of_mul_eq_mul_right hpos this
  · intro z hz
    have hzm : z.val % 2 ^ a = j.val := (Finset.mem_filter.mp hz).2
    have hqlt : z.val / 2 ^ a < 2 ^ (k - a) := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), Nat.pow_sub_mul_pow 2 hak]
      exact z.isLt
    refine ⟨⟨z.val / 2 ^ a, hqlt⟩, Finset.mem_univ _, ?_⟩
    ext
    dsimp only [e]
    have hdm := Nat.div_add_mod z.val (2 ^ a)
    rw [hzm] at hdm
    linarith

def firstConstFrom {M : ℕ} (hM : 0 < M) (c : Fin M → Bool) (u : Fin M) : Fin M :=
  match (List.finRange M).find? (fun s => c ⟨(u.val + s.val) % M, Nat.mod_lt _ hM⟩) with
  | some s => ⟨(u.val + s.val) % M, Nat.mod_lt _ hM⟩
  | none => u

lemma firstConstFrom_rot {M : ℕ} (hM : 0 < M) (c : Fin M → Bool) (u : Fin M) :
    let rotC : Fin M → Bool := fun m => c ⟨(m.val + M - 1) % M, Nat.mod_lt _ hM⟩
    let u1 : Fin M := ⟨(u.val + 1) % M, Nat.mod_lt _ hM⟩
    firstConstFrom hM rotC u1 = ⟨((firstConstFrom hM c u).val + 1) % M, Nat.mod_lt _ hM⟩ := by
  intro rotC u1
  have hpred : ∀ s : Fin M,
      rotC ⟨(u1.val + s.val) % M, Nat.mod_lt _ hM⟩ =
        c ⟨(u.val + s.val) % M, Nat.mod_lt _ hM⟩ := by
    intro s
    dsimp only [rotC, u1]
    congr 1; ext; dsimp only
    have h1 : ((u.val + 1) % M + s.val) % M = (u.val + s.val + 1) % M := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      congr 1; omega
    rw [h1]
    have h2 : ((u.val + s.val + 1) % M + M - 1) % M = (u.val + s.val) % M := by
      have hlt : (u.val + s.val + 1) % M < M := Nat.mod_lt _ hM
      have h3 : ((u.val + s.val + 1) % M + M - 1) % M =
          ((u.val + s.val + 1) % M + (M - 1)) % M := by congr 1; omega
      rw [h3, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have h4 : u.val + s.val + 1 + (M - 1) = u.val + s.val + M := by omega
      rw [h4, Nat.add_mod_right]
    exact h2
  unfold firstConstFrom
  have hfind : (List.finRange M).find? (fun s => rotC ⟨(u1.val + s.val) % M, Nat.mod_lt _ hM⟩) =
      (List.finRange M).find? (fun s => c ⟨(u.val + s.val) % M, Nat.mod_lt _ hM⟩) := by
    congr 1; funext s; exact hpred s
  rw [hfind]
  cases h : (List.finRange M).find? (fun s => c ⟨(u.val + s.val) % M, Nat.mod_lt _ hM⟩) with
  | none => rfl
  | some s =>
    ext; dsimp only [u1]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    conv_rhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    congr 1; omega

lemma firstConstFrom_hit {M : ℕ} (hM : 0 < M) (c : Fin M → Bool) (u : Fin M)
    (hex : ∃ m : Fin M, c m = true) :
    c (firstConstFrom hM c u) = true := by
  unfold firstConstFrom
  cases h : (List.finRange M).find? (fun s => c ⟨(u.val + s.val) % M, Nat.mod_lt _ hM⟩) with
  | some s =>
    simpa using List.find?_some h
  | none =>
    exfalso
    rcases hex with ⟨m, hm⟩
    let s : Fin M := ⟨(m.val + M - u.val) % M, Nat.mod_lt _ hM⟩
    have hsm : s ∈ List.finRange M := List.mem_finRange s
    have hnone := List.find?_eq_none.mp h s hsm
    have heq : (⟨(u.val + s.val) % M, Nat.mod_lt _ hM⟩ : Fin M) = m := by
      ext; dsimp only [s]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have h1 : u.val + (m.val + M - u.val) = m.val + M := by have := u.isLt; omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt m.isLt]
    rw [heq, hm] at hnone
    exact hnone rfl

def bitsNat {k : ℕ} (f : Fin k → Bool) (off len : ℕ) (hbound : off + len ≤ k) : Fin (2 ^ len) :=
  ⟨∑ j : Fin len, if f ⟨off + j.val, by omega⟩ then 2 ^ j.val else 0, by
    calc (∑ j : Fin len, if f ⟨off + j.val, by omega⟩ then 2 ^ j.val else 0)
        ≤ ∑ j : Fin len, 2 ^ j.val :=
          Finset.sum_le_sum (fun j _ => by split_ifs; exact le_rfl; exact Nat.zero_le _)
      _ = ∑ j ∈ Finset.range len, 2 ^ j := Fin.sum_univ_eq_sum_range (fun j => 2 ^ j) len
      _ < 2 ^ len := sum_two_pow_lt len⟩

lemma bitsNat_testBit {k : ℕ} (f : Fin k → Bool) (off len : ℕ) (hbound : off + len ≤ k)
    (j : Fin len) :
    (bitsNat f off len hbound).val.testBit j.val = f ⟨off + j.val, by omega⟩ := by
  let ff : Fin len → Bool := fun l => f ⟨off + l.val, by omega⟩
  have h1 : bitsNat f off len hbound = (fin_bit_equiv len).symm ff := rfl
  rw [← fin_bit_equiv_testBit, h1, (fin_bit_equiv len).apply_symm_apply]

lemma bitsNat_eq_iff {k : ℕ} (f g : Fin k → Bool) (off len : ℕ) (hbound : off + len ≤ k) :
    bitsNat f off len hbound = bitsNat g off len hbound ↔
      ∀ j : Fin len, f ⟨off + j.val, by omega⟩ = g ⟨off + j.val, by omega⟩ := by
  let ff : Fin len → Bool := fun j => f ⟨off + j.val, by omega⟩
  let gg : Fin len → Bool := fun j => g ⟨off + j.val, by omega⟩
  have hf : bitsNat f off len hbound = (fin_bit_equiv len).symm ff := rfl
  have hg : bitsNat g off len hbound = (fin_bit_equiv len).symm gg := rfl
  rw [hf, hg, Equiv.apply_eq_iff_eq]
  exact ⟨fun h j => congrFun h j, fun h => funext h⟩

lemma decoder_optimal_and_cost {N : ℕ} (order : Equiv.Perm (Fin N)) (T : Fin N → Fin N → Bool) :
    let exposed := fun h : ℕ => Finset.univ.filter (fun i : Fin N => h ≤ (order i).val)
    let cost := fun (h : ℕ) (out : Finset (Fin N) → Finset (Fin N) → Bool) =>
      (Finset.univ.filter (fun z : Fin N × Fin N =>
        out ({z.1, z.2} : Finset (Fin N)) (exposed h ∩ {z.1}) ≠ T z.1 z.2)).card
    ∃ D : Finset (Fin N) → Finset (Fin N) → Bool, ∀ h : ℕ, h ≤ N →
      (∀ other, cost h D ≤ cost h other) ∧
      let H := Finset.univ.filter (fun i : Fin N => (order i).val < h)
      (4 * cost h D : ℤ) = (h : ℤ) ^ 2 - ∑ x ∈ H, ∑ y ∈ H, bSign (T x y) * bSign (T y x) := by
  classical
  intro exposed cost
  let D : Finset (Fin N) → Finset (Fin N) → Bool := fun s1 s2 =>
    if h2 : s2.Nonempty then
      let x := h2.choose
      if hdiff : (s1 \ s2).Nonempty then T x hdiff.choose else T x x
    else
      if h1 : s1.Nonempty then
        let x := (Finset.exists_min_image s1 (fun i => (order i).val) h1).choose
        if hdiff : (s1.erase x).Nonempty then T x hdiff.choose else T x x
      else false
  have hD_exposed : ∀ h (x y : Fin N), h ≤ (order x).val →
      D ({x, y} : Finset (Fin N)) (exposed h ∩ {x}) = T x y := by
    intro h x y hx
    have hinter : exposed h ∩ {x} = {x} := by
      ext z; simp only [Finset.mem_inter, exposed, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      exact ⟨fun hz => hz.2, fun hz => ⟨hz ▸ hx, hz⟩⟩
    rw [hinter]
    have h2 : ({x} : Finset (Fin N)).Nonempty := Finset.singleton_nonempty x
    dsimp only [D]
    simp only [h2, dite_true]
    have hx_ch : h2.choose = x := Finset.mem_singleton.mp h2.choose_spec
    rw [hx_ch]
    by_cases hxy : x = y
    · subst hxy
      have hdiff : ¬ (({x, x} : Finset (Fin N)) \ {x}).Nonempty := by simp
      simp only [hdiff, dite_false]
    · have hsdiff : ({x, y} : Finset (Fin N)) \ {x} = {y} := by
        ext z; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl, hne⟩
          · exact absurd rfl hne
          · rfl
        · rintro rfl; exact ⟨Or.inr rfl, Ne.symm hxy⟩
      have hdiff : (({x, y} : Finset (Fin N)) \ {x}).Nonempty := by rw [hsdiff]; exact Finset.singleton_nonempty y
      simp only [hdiff, dite_true]
      have hy_ch : hdiff.choose = y :=
        Finset.mem_singleton.mp ((Finset.ext_iff.mp hsdiff _).mp hdiff.choose_spec)
      rw [hy_ch]
  have hD_hidden_le : ∀ h (x y : Fin N), (order x).val < h → (order x).val ≤ (order y).val →
      D ({x, y} : Finset (Fin N)) (exposed h ∩ {x}) = T x y := by
    intro h x y hx hle
    have hinter : exposed h ∩ {x} = ∅ := by
      ext z; simp only [Finset.mem_inter, exposed, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      intro hz hzx; subst hzx; omega
    rw [hinter]
    dsimp only [D]
    simp only [Finset.not_nonempty_empty, dite_false]
    have h1 : ({x, y} : Finset (Fin N)).Nonempty := Finset.insert_nonempty x {y}
    simp only [h1, dite_true]
    have hmin_spec := (Finset.exists_min_image ({x, y} : Finset (Fin N)) (fun i => (order i).val) h1).choose_spec
    set xmin := (Finset.exists_min_image ({x, y} : Finset (Fin N)) (fun i => (order i).val) h1).choose
    have hxmin_eq : xmin = x := by
      have hmem := hmin_spec.1
      have hle_x := hmin_spec.2 x (Finset.mem_insert_self x {y})
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact h
      · rw [h] at hle_x
        have heq : (order y).val = (order x).val := by omega
        exact h.trans (order.injective (Fin.ext heq))
    rw [hxmin_eq]
    by_cases hxy : x = y
    · subst hxy
      have hdiff : ¬ (({x, x} : Finset (Fin N)).erase x).Nonempty := by simp
      simp only [hdiff, dite_false]
    · have herase : ({x, y} : Finset (Fin N)).erase x = {y} := by
        ext z; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hne, rfl | rfl⟩
          · exact absurd rfl hne
          · rfl
        · rintro rfl; exact ⟨Ne.symm hxy, Or.inr rfl⟩
      have hdiff : (({x, y} : Finset (Fin N)).erase x).Nonempty := by rw [herase]; exact Finset.singleton_nonempty y
      simp only [hdiff, dite_true]
      have hy_ch : hdiff.choose = y :=
        Finset.mem_singleton.mp ((Finset.ext_iff.mp herase _).mp hdiff.choose_spec)
      rw [hy_ch]
  have hD_hidden_gt : ∀ h (x y : Fin N), (order x).val < h → (order y).val < (order x).val →
      D ({x, y} : Finset (Fin N)) (exposed h ∩ {x}) = T y x := by
    intro h x y hx hgt
    have hinter_x : exposed h ∩ {x} = ∅ := by
      ext z; simp only [Finset.mem_inter, exposed, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      intro hz hzx; subst hzx; omega
    have hinter_y : exposed h ∩ {y} = ∅ := by
      ext z; simp only [Finset.mem_inter, exposed, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      intro hz hzy; subst hzy; omega
    have hpair : ({x, y} : Finset (Fin N)) = {y, x} := Finset.pair_comm x y
    rw [hinter_x, hpair, ← hinter_y]
    exact hD_hidden_le h y x (by omega) (by omega)
  refine ⟨D, ?_⟩
  intro h hh
  let H := Finset.univ.filter (fun i : Fin N => (order i).val < h)
  have hD_err_set : Finset.univ.filter (fun z : Fin N × Fin N =>
      D ({z.1, z.2} : Finset (Fin N)) (exposed h ∩ {z.1}) ≠ T z.1 z.2) =
      Finset.univ.filter (fun z : Fin N × Fin N =>
        z.1 ∈ H ∧ z.2 ∈ H ∧ (order z.2).val < (order z.1).val ∧ T z.2 z.1 ≠ T z.1 z.2) := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, H]
    by_cases hx : (order x).val < h
    · by_cases hlt : (order y).val < (order x).val
      · rw [hD_hidden_gt h x y hx hlt]
        have hy : (order y).val < h := by omega
        simp [hx, hy, hlt]
      · rw [hD_hidden_le h x y hx (by omega)]
        simp [hlt]
    · rw [hD_exposed h x y (by omega)]
      simp [hx]
  constructor
  · intro other
    dsimp only [cost]
    rw [hD_err_set]
    let badD := Finset.univ.filter (fun z : Fin N × Fin N =>
      z.1 ∈ H ∧ z.2 ∈ H ∧ (order z.2).val < (order z.1).val ∧ T z.2 z.1 ≠ T z.1 z.2)
    let badO := Finset.univ.filter (fun z : Fin N × Fin N =>
      other ({z.1, z.2} : Finset (Fin N)) (exposed h ∩ {z.1}) ≠ T z.1 z.2)
    have hpick : ∀ z ∈ badD, z ∈ badO ∨ (z.2, z.1) ∈ badO := by
      intro ⟨x, y⟩ hz
      rcases (Finset.mem_filter.mp hz).2 with ⟨hxH, hyH, hlt, hne⟩
      have hx : (order x).val < h := (Finset.mem_filter.mp hxH).2
      have hy : (order y).val < h := (Finset.mem_filter.mp hyH).2
      have hinter_x : exposed h ∩ {x} = ∅ := by
        ext u; simp only [Finset.mem_inter, exposed, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
        intro hu hux; subst hux; omega
      have hinter_y : exposed h ∩ {y} = ∅ := by
        ext u; simp only [Finset.mem_inter, exposed, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
        intro hu huy; subst huy; omega
      by_cases h1 : other ({x, y} : Finset (Fin N)) ∅ ≠ T x y
      · left; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hinter_x]; exact h1⟩
      · right
        push Not at h1
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [hinter_y, Finset.pair_comm y x, h1]
        exact Ne.symm hne
    let mapO : Fin N × Fin N → Fin N × Fin N := fun z =>
      if z ∈ badO then z else (z.2, z.1)
    refine Finset.card_le_card_of_injOn mapO ?_ ?_
    · intro z hz
      dsimp only [mapO]
      split_ifs with h1
      · exact h1
      · exact (hpick z hz).resolve_left h1
    · intro z1 hz1 z2 hz2 hEq
      have h1lt : (order z1.2).val < (order z1.1).val := (Finset.mem_filter.mp hz1).2.2.2.1
      have h2lt : (order z2.2).val < (order z2.1).val := (Finset.mem_filter.mp hz2).2.2.2.1
      dsimp only [mapO] at hEq
      split_ifs at hEq with ha hb
      · exact hEq
      · exfalso
        have hfst : z1.1 = z2.2 := congrArg Prod.fst hEq
        have hsnd : z1.2 = z2.1 := congrArg Prod.snd hEq
        rw [hfst, hsnd] at h1lt; omega
      · exfalso
        have hfst : z1.2 = z2.1 := congrArg Prod.fst hEq
        have hsnd : z1.1 = z2.2 := congrArg Prod.snd hEq
        rw [← hfst, ← hsnd] at h2lt; omega
      · exact Prod.ext (congrArg Prod.snd hEq) (congrArg Prod.fst hEq)
  · dsimp only [cost]
    rw [hD_err_set]
    have hHcard : H.card = h := by
      have hbij : H.card = (Finset.univ.filter (fun j : Fin N => j.val < h)).card := by
        refine Finset.card_bij (fun i _ => order i) ?_ ?_ ?_
        · intro i hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
        · intro i1 _ i2 _ heq; exact order.injective heq
        · intro j hj
          exact ⟨order.symm j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            rw [order.apply_symm_apply]; exact (Finset.mem_filter.mp hj).2⟩, order.apply_symm_apply j⟩
      rw [hbij]
      have hrange : (Finset.univ.filter (fun j : Fin N => j.val < h)).card = (Finset.range h).card := by
        refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
        · intro j hj; exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
        · intro j1 _ j2 _ heq; exact Fin.ext heq
        · intro n hn
          have hnh : n < h := Finset.mem_range.mp hn
          exact ⟨⟨n, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnh⟩, rfl⟩
      rw [hrange, Finset.card_range]
    have hdiff_sum : (h : ℤ) ^ 2 - ∑ x ∈ H, ∑ y ∈ H, bSign (T x y) * bSign (T y x) =
        ∑ x ∈ H, ∑ y ∈ H, (if T x y ≠ T y x then (2 : ℤ) else 0) := by
      have hsq : (h : ℤ) ^ 2 = ∑ _x ∈ H, ∑ _y ∈ H, (1 : ℤ) := by
        simp [hHcard, sq]
      rw [hsq, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro x _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro y _
      exact (bSign_ne_eq (T x y) (T y x)).symm
    rw [hdiff_sum]
    have hprod_sum : (∑ x ∈ H, ∑ y ∈ H, (if T x y ≠ T y x then (2 : ℤ) else 0)) =
        2 * (((H ×ˢ H).filter (fun z => T z.1 z.2 ≠ T z.2 z.1)).card : ℤ) := by
      rw [← Finset.sum_product', ← Finset.sum_filter]
      simp [mul_comm]
    rw [hprod_sum]
    have hcard_double : ((H ×ˢ H).filter (fun z => T z.1 z.2 ≠ T z.2 z.1)).card =
        2 * (Finset.univ.filter (fun z : Fin N × Fin N =>
          z.1 ∈ H ∧ z.2 ∈ H ∧ (order z.2).val < (order z.1).val ∧ T z.2 z.1 ≠ T z.1 z.2)).card := by
      let A := Finset.univ.filter (fun z : Fin N × Fin N =>
        z.1 ∈ H ∧ z.2 ∈ H ∧ (order z.2).val < (order z.1).val ∧ T z.2 z.1 ≠ T z.1 z.2)
      let B := Finset.univ.filter (fun z : Fin N × Fin N =>
        z.1 ∈ H ∧ z.2 ∈ H ∧ (order z.1).val < (order z.2).val ∧ T z.1 z.2 ≠ T z.2 z.1)
      have hpart : (H ×ˢ H).filter (fun z => T z.1 z.2 ≠ T z.2 z.1) = A ∪ B := by
        ext ⟨x, y⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_union, Finset.mem_univ, true_and, A, B]
        constructor
        · rintro ⟨⟨hx, hy⟩, hne⟩
          have hxy : x ≠ y := fun heq => hne (by rw [heq])
          have hord : (order x).val ≠ (order y).val := fun heq => hxy (order.injective (Fin.ext heq))
          rcases lt_or_gt_of_ne hord with hlt | hgt
          · right; exact ⟨hx, hy, hlt, hne⟩
          · left; exact ⟨hx, hy, hgt, Ne.symm hne⟩
        · rintro (⟨hx, hy, _, hne⟩ | ⟨hx, hy, _, hne⟩)
          · exact ⟨⟨hx, hy⟩, Ne.symm hne⟩
          · exact ⟨⟨hx, hy⟩, hne⟩
      have hdisj : Disjoint A B := by
        rw [Finset.disjoint_left]
        intro z hA hB
        have h1 := (Finset.mem_filter.mp hA).2.2.2.1
        have h2 := (Finset.mem_filter.mp hB).2.2.2.1
        omega
      have hAB : B.card = A.card := by
        refine Finset.card_bij (fun z _ => (z.2, z.1)) ?_ ?_ ?_
        · intro z hz
          rcases (Finset.mem_filter.mp hz).2 with ⟨h1, h2, hlt, hne⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2, h1, hlt, hne⟩
        · intro z1 _ z2 _ hEq
          exact Prod.ext (congrArg Prod.snd hEq) (congrArg Prod.fst hEq)
        · intro z hz
          rcases (Finset.mem_filter.mp hz).2 with ⟨h1, h2, hlt, hne⟩
          exact ⟨(z.2, z.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2, h1, hlt, hne⟩, rfl⟩
      rw [hpart, Finset.card_union_of_disjoint hdisj, hAB]
      dsimp only [A]
      omega
    rw [hcard_double]
    push_cast; ring

def rotIdx (k M b : ℕ) (hM : 0 < M) (hb : 0 < b) (hMb : M * b ≤ k) : Fin k ≃ Fin k :=
  { toFun := fun i =>
      if h : i.val < M * b then
        ⟨((i.val / b + 1) % M) * b + i.val % b,
          lt_of_lt_of_le (mul_add_lt_mul (Nat.mod_lt _ hM) (Nat.mod_lt _ hb)) hMb⟩
      else i
    invFun := fun i =>
      if h : i.val < M * b then
        ⟨((i.val / b + M - 1) % M) * b + i.val % b,
          lt_of_lt_of_le (mul_add_lt_mul (Nat.mod_lt _ hM) (Nat.mod_lt _ hb)) hMb⟩
      else i
    left_inv := fun i => by
      by_cases h : i.val < M * b
      · have hlt1 : ((i.val / b + 1) % M) * b + i.val % b < M * b :=
          mul_add_lt_mul (Nat.mod_lt _ hM) (Nat.mod_lt _ hb)
        simp only [h, hlt1, dite_true]
        ext; dsimp only
        have hdiv1 : (((i.val / b + 1) % M) * b + i.val % b) / b = (i.val / b + 1) % M := by
          rw [Nat.mul_comm _ b, Nat.mul_add_div hb, Nat.div_eq_of_lt (Nat.mod_lt _ hb), Nat.add_zero]
        have hmod1 : (((i.val / b + 1) % M) * b + i.val % b) % b = i.val % b := by
          rw [Nat.mul_add_mod_self_right, Nat.mod_mod]
        rw [hdiv1, hmod1]
        have hqlt : i.val / b < M := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
        have hback : ((i.val / b + 1) % M + M - 1) % M = i.val / b := by
          have h3 : ((i.val / b + 1) % M + M - 1) % M = ((i.val / b + 1) % M + (M - 1)) % M := by
            congr 1; omega
          rw [h3, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have h4 : i.val / b + 1 + (M - 1) = i.val / b + M := by omega
          rw [h4, Nat.add_mod_right, Nat.mod_eq_of_lt hqlt]
        rw [hback, Nat.mul_comm, Nat.div_add_mod]
      · simp only [h, dite_false]
    right_inv := fun i => by
      by_cases h : i.val < M * b
      · have hlt1 : ((i.val / b + M - 1) % M) * b + i.val % b < M * b :=
          mul_add_lt_mul (Nat.mod_lt _ hM) (Nat.mod_lt _ hb)
        simp only [h, hlt1, dite_true]
        ext; dsimp only
        have hdiv1 : (((i.val / b + M - 1) % M) * b + i.val % b) / b = (i.val / b + M - 1) % M := by
          rw [Nat.mul_comm _ b, Nat.mul_add_div hb, Nat.div_eq_of_lt (Nat.mod_lt _ hb), Nat.add_zero]
        have hmod1 : (((i.val / b + M - 1) % M) * b + i.val % b) % b = i.val % b := by
          rw [Nat.mul_add_mod_self_right, Nat.mod_mod]
        rw [hdiv1, hmod1]
        have hqlt : i.val / b < M := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
        have hback : ((i.val / b + M - 1) % M + 1) % M = i.val / b := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have h4 : i.val / b + M - 1 + 1 = i.val / b + M :=
            Nat.sub_add_cancel (Nat.le_add_left_of_le hM)
          rw [h4, Nat.add_mod_right, Nat.mod_eq_of_lt hqlt]
        rw [hback, Nat.mul_comm, Nat.div_add_mod]
      · simp only [h, dite_false] }

lemma rot_fib_helper (k d t L : ℕ) (hd : 0 < 2 ^ d) (ht : 0 < 2 ^ t)
    (hMb : 2 ^ d * 2 ^ t < k) (hu_b : 2 ^ d * 2 ^ t + 1 + d ≤ k)
    (hAct : (Finset.univ.filter (fun f : Fin k → Bool =>
      f ⟨2 ^ d * 2 ^ t, hMb⟩ = false)).card = 2 ^ d * L) :
    let M := 2 ^ d
    let b := 2 ^ t
    let isConst : (Fin k → Bool) → Fin M → Bool := fun f m =>
      decide ((∀ j : Fin b, f ⟨m.val * b + j.val,
        lt_trans (mul_add_lt_mul m.isLt j.isLt) hMb⟩ = false) ∨
        (∀ j : Fin b, f ⟨m.val * b + j.val,
        lt_trans (mul_add_lt_mul m.isLt j.isLt) hMb⟩ = true))
    let uOf : (Fin k → Bool) → Fin M := fun f => bitsNat f (M * b + 1) d hu_b
    let ownerF : (Fin k → Bool) → Fin M := fun f => firstConstFrom hd (isConst f) (uOf f)
    ∀ m : Fin M, (Finset.univ.filter (fun f : Fin k → Bool =>
      f ⟨M * b, hMb⟩ = false ∧ ownerF f = m)).card = L := by
  intro M b isConst uOf ownerF
  let ri := rotIdx k M b hd ht (le_of_lt hMb)
  let Rfun : (Fin k → Bool) → (Fin k → Bool) := fun f =>
    let u1 : Fin M := ⟨((uOf f).val + 1) % M, Nat.mod_lt _ hd⟩
    fun i =>
      if h1 : M * b + 1 ≤ i.val ∧ i.val < M * b + 1 + d then
        u1.val.testBit (i.val - (M * b + 1))
      else f (ri.symm i)
  let Rinv : (Fin k → Bool) → (Fin k → Bool) := fun f =>
    let u0 : Fin M := ⟨((uOf f).val + M - 1) % M, Nat.mod_lt _ hd⟩
    fun i =>
      if h1 : M * b + 1 ≤ i.val ∧ i.val < M * b + 1 + d then
        u0.val.testBit (i.val - (M * b + 1))
      else f (ri i)
  have hRu : ∀ f, uOf (Rfun f) = ⟨((uOf f).val + 1) % M, Nat.mod_lt _ hd⟩ := by
    intro f
    apply (fin_bit_equiv d).injective
    ext j
    rw [fin_bit_equiv_testBit, fin_bit_equiv_testBit, bitsNat_testBit]
    dsimp only [Rfun]
    have hin : M * b + 1 ≤ M * b + 1 + j.val ∧ M * b + 1 + j.val < M * b + 1 + d := by
      have := j.isLt; omega
    rw [dif_pos hin]
    congr 1; exact Nat.add_sub_cancel_left _ _
  have hRinv_u : ∀ f, uOf (Rinv f) = ⟨((uOf f).val + M - 1) % M, Nat.mod_lt _ hd⟩ := by
    intro f
    apply (fin_bit_equiv d).injective
    ext j
    rw [fin_bit_equiv_testBit, fin_bit_equiv_testBit, bitsNat_testBit]
    dsimp only [Rinv]
    have hin : M * b + 1 ≤ M * b + 1 + j.val ∧ M * b + 1 + j.val < M * b + 1 + d := by
      have := j.isLt; omega
    rw [dif_pos hin]
    congr 1; exact Nat.add_sub_cancel_left _ _
  have hR_left : ∀ f, Rinv (Rfun f) = f := by
    intro f; ext i
    by_cases h1 : M * b + 1 ≤ i.val ∧ i.val < M * b + 1 + d
    · dsimp only [Rinv]
      rw [dif_pos h1, hRu]
      have hback : (((uOf f).val + 1) % M + M - 1) % M = (uOf f).val := by
        have h3 : (((uOf f).val + 1) % M + M - 1) % M = (((uOf f).val + 1) % M + (M - 1)) % M := by
          congr 1; omega
        rw [h3, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have h4 : (uOf f).val + 1 + (M - 1) = (uOf f).val + M := by omega
        rw [h4, Nat.add_mod_right, Nat.mod_eq_of_lt (uOf f).isLt]
      rw [hback]
      let j : Fin d := ⟨i.val - (M * b + 1), by omega⟩
      have htb := bitsNat_testBit f (M * b + 1) d hu_b j
      change (uOf f).val.testBit j.val = f i
      rw [htb]; congr 1; ext; dsimp only [j]; omega
    · dsimp only [Rinv]
      simp only [h1, dite_false]
      have hnot : ¬ (M * b + 1 ≤ (ri i).val ∧ (ri i).val < M * b + 1 + d) := by
        by_cases hlt : i.val < M * b
        · have : (ri i).val < M * b := by
            simp only [ri, rotIdx, Equiv.coe_fn_mk, hlt, dite_true]
            exact mul_add_lt_mul (Nat.mod_lt _ hd) (Nat.mod_lt _ ht)
          omega
        · have : ri i = i := by simp only [ri, rotIdx, Equiv.coe_fn_mk, hlt, dite_false]
          rw [this]; exact h1
      dsimp only [Rfun]
      simp only [hnot, dite_false, ri.symm_apply_apply]
  have hR_right : ∀ f, Rfun (Rinv f) = f := by
    intro f; ext i
    by_cases h1 : M * b + 1 ≤ i.val ∧ i.val < M * b + 1 + d
    · dsimp only [Rfun]
      rw [dif_pos h1, hRinv_u]
      have hback : (((uOf f).val + M - 1) % M + 1) % M = (uOf f).val := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have h4 : (uOf f).val + M - 1 + 1 = (uOf f).val + M := by omega
        rw [h4, Nat.add_mod_right, Nat.mod_eq_of_lt (uOf f).isLt]
      rw [hback]
      let j : Fin d := ⟨i.val - (M * b + 1), by omega⟩
      have htb := bitsNat_testBit f (M * b + 1) d hu_b j
      change (uOf f).val.testBit j.val = f i
      rw [htb]; congr 1; ext; dsimp only [j]; omega
    · dsimp only [Rfun]
      simp only [h1, dite_false]
      have hnot : ¬ (M * b + 1 ≤ (ri.symm i).val ∧ (ri.symm i).val < M * b + 1 + d) := by
        by_cases hlt : i.val < M * b
        · have : (ri.symm i).val < M * b := by
            simp only [ri, rotIdx, Equiv.coe_fn_symm_mk, hlt, dite_true]
            exact mul_add_lt_mul (Nat.mod_lt _ hd) (Nat.mod_lt _ ht)
          omega
        · have : ri.symm i = i := by simp only [ri, rotIdx, Equiv.coe_fn_symm_mk, hlt, dite_false]
          rw [this]; exact h1
      dsimp only [Rinv]
      simp only [hnot, dite_false, ri.apply_symm_apply]
  have hR_split : ∀ f, Rfun f ⟨M * b, hMb⟩ = f ⟨M * b, hMb⟩ := by
    intro f
    dsimp only [Rfun]
    have h1 : ¬ (M * b + 1 ≤ M * b ∧ M * b < M * b + 1 + d) := by omega
    simp only [h1, dite_false]
    have hnot : ¬ (M * b < M * b) := by omega
    have hri : ri.symm ⟨M * b, hMb⟩ = ⟨M * b, hMb⟩ := by
      simp only [ri, rotIdx, Equiv.coe_fn_symm_mk, hnot, dite_false]
    rw [hri]
  have hR_const : ∀ f (m : Fin M),
      isConst (Rfun f) m = isConst f ⟨(m.val + M - 1) % M, Nat.mod_lt _ hd⟩ := by
    intro f m
    have hbit : ∀ j : Fin b, Rfun f ⟨m.val * b + j.val, lt_trans (mul_add_lt_mul m.isLt j.isLt) hMb⟩ =
        f ⟨((m.val + M - 1) % M) * b + j.val,
          lt_trans (mul_add_lt_mul (Nat.mod_lt _ hd) j.isLt) hMb⟩ := by
      intro j
      have hlt : m.val * b + j.val < M * b := mul_add_lt_mul m.isLt j.isLt
      have hnot : ¬ (M * b + 1 ≤ m.val * b + j.val ∧ m.val * b + j.val < M * b + 1 + d) := by omega
      dsimp only [Rfun]
      simp only [hnot, dite_false]
      congr 1
      simp only [ri, rotIdx, Equiv.coe_fn_symm_mk, hlt, dite_true]
      ext; dsimp only
      have hdiv1 : (m.val * b + j.val) / b = m.val := by
        rw [Nat.mul_comm _ b, Nat.mul_add_div ht, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
      have hmod1 : (m.val * b + j.val) % b = j.val := by
        rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt j.isLt]
      rw [hdiv1, hmod1]
    dsimp only [isConst]
    simp_rw [hbit]
  have hR_owner : ∀ f, ownerF (Rfun f) = ⟨((ownerF f).val + 1) % M, Nat.mod_lt _ hd⟩ := by
    intro f
    dsimp only [ownerF]
    have hc : isConst (Rfun f) = fun m => isConst f ⟨(m.val + M - 1) % M, Nat.mod_lt _ hd⟩ :=
      funext (hR_const f)
    rw [hc, hRu]
    exact firstConstFrom_rot hd (isConst f) (uOf f)
  have hstep : ∀ m : Fin M,
      (Finset.univ.filter (fun f : Fin k → Bool => f ⟨M * b, hMb⟩ = false ∧ ownerF f = m)).card =
      (Finset.univ.filter (fun f : Fin k → Bool =>
        f ⟨M * b, hMb⟩ = false ∧ ownerF f = ⟨(m.val + 1) % M, Nat.mod_lt _ hd⟩)).card := by
    intro m
    refine Finset.card_bij (fun f _ => Rfun f) ?_ ?_ ?_
    · intro f hf
      rcases (Finset.mem_filter.mp hf).2 with ⟨hf0, hfm⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hR_split, hf0], by rw [hR_owner, hfm]⟩
    · intro f1 _ f2 _ hEq
      have := congrArg Rinv hEq
      rw [hR_left, hR_left] at this; exact this
    · intro g' hg'
      rcases (Finset.mem_filter.mp hg').2 with ⟨hg0, hgm⟩
      refine ⟨Rinv g', Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, hR_right g'⟩
      · have := hR_split (Rinv g'); rw [hR_right, hg0] at this; exact this.symm
      · have ho := hR_owner (Rinv g'); rw [hR_right, hgm] at ho
        ext
        have hval := congrArg Fin.val ho
        dsimp only at hval
        have hback : (((ownerF (Rinv g')).val + 1) % M + M - 1) % M = (ownerF (Rinv g')).val := by
          have h3 : (((ownerF (Rinv g')).val + 1) % M + M - 1) % M =
              (((ownerF (Rinv g')).val + 1) % M + (M - 1)) % M := by congr 1; omega
          rw [h3, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have h4 : (ownerF (Rinv g')).val + 1 + (M - 1) = (ownerF (Rinv g')).val + M := by omega
          rw [h4, Nat.add_mod_right, Nat.mod_eq_of_lt (ownerF (Rinv g')).isLt]
        have hback2 : ((m.val + 1) % M + M - 1) % M = m.val := by
          have h3 : ((m.val + 1) % M + M - 1) % M = ((m.val + 1) % M + (M - 1)) % M := by
            congr 1; omega
          rw [h3, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have h4 : m.val + 1 + (M - 1) = m.val + M := by omega
          rw [h4, Nat.add_mod_right, Nat.mod_eq_of_lt m.isLt]
        rw [← hback, ← hval, hback2]
  have hall_eq : ∀ n (hn : n < M),
      (Finset.univ.filter (fun f : Fin k → Bool => f ⟨M * b, hMb⟩ = false ∧ ownerF f = ⟨n, hn⟩)).card =
      (Finset.univ.filter (fun f : Fin k → Bool => f ⟨M * b, hMb⟩ = false ∧ ownerF f = ⟨0, hd⟩)).card := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ s ih =>
      intro hs
      have hprev := ih (by omega)
      have hst := hstep ⟨s, by omega⟩
      have hmod : (s + 1) % M = s + 1 := Nat.mod_eq_of_lt hs
      have hfin : (⟨(s + 1) % M, Nat.mod_lt _ hd⟩ : Fin M) = ⟨s + 1, hs⟩ := Fin.ext hmod
      rw [hfin] at hst
      omega
  have hsum_all : (∑ m : Fin M, (Finset.univ.filter (fun f : Fin k → Bool =>
      f ⟨M * b, hMb⟩ = false ∧ ownerF f = m)).card) = M * L := by
    rw [← hAct, Finset.card_eq_sum_ones,
      ← Finset.sum_fiberwise_of_maps_to (g := ownerF) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl; intro m _
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.filter_filter]
  have hconst_sum : (∑ m : Fin M, (Finset.univ.filter (fun f : Fin k → Bool =>
      f ⟨M * b, hMb⟩ = false ∧ ownerF f = m)).card) =
      M * (Finset.univ.filter (fun f : Fin k → Bool =>
        f ⟨M * b, hMb⟩ = false ∧ ownerF f = ⟨0, hd⟩)).card := by
    calc (∑ m : Fin M, _)
        = ∑ _m : Fin M, (Finset.univ.filter (fun f : Fin k → Bool =>
            f ⟨M * b, hMb⟩ = false ∧ ownerF f = ⟨0, hd⟩)).card :=
          Finset.sum_congr rfl (fun m _ => hall_eq m.val m.isLt)
      _ = M * _ := by simp
  have h0 : (Finset.univ.filter (fun f : Fin k → Bool =>
      f ⟨M * b, hMb⟩ = false ∧ ownerF f = ⟨0, hd⟩)).card = L := by
    have : M * (Finset.univ.filter (fun f : Fin k → Bool =>
        f ⟨M * b, hMb⟩ = false ∧ ownerF f = ⟨0, hd⟩)).card = M * L := by omega
    exact Nat.eq_of_mul_eq_mul_left hd this
  intro m
  rw [hall_eq m.val m.isLt, h0]

lemma v_split_helper (k d t B : ℕ) (hd : 0 < 2 ^ d) (ht : 0 < 2 ^ t)
    (hMb : 2 ^ d * 2 ^ t < k) (hu_b : 2 ^ d * 2 ^ t + 1 + d ≤ k)
    (hv_b : 2 ^ d * 2 ^ t + 1 + d + t ≤ k) :
    let M := 2 ^ d
    let b := 2 ^ t
    let isConst : (Fin k → Bool) → Fin M → Bool := fun f m =>
      decide ((∀ j : Fin b, f ⟨m.val * b + j.val,
        lt_trans (mul_add_lt_mul m.isLt j.isLt) hMb⟩ = false) ∨
        (∀ j : Fin b, f ⟨m.val * b + j.val,
        lt_trans (mul_add_lt_mul m.isLt j.isLt) hMb⟩ = true))
    let uOf : (Fin k → Bool) → Fin M := fun f => bitsNat f (M * b + 1) d hu_b
    let vOf : (Fin k → Bool) → Fin b := fun f => bitsNat f (M * b + 1 + d) t hv_b
    let ownerF : (Fin k → Bool) → Fin M := fun f => firstConstFrom hd (isConst f) (uOf f)
    ∀ m : Fin M, (Finset.univ.filter (fun f : Fin k → Bool =>
      f ⟨M * b, hMb⟩ = false ∧ ownerF f = m)).card = b * B →
    ∀ q : Fin b, (Finset.univ.filter (fun f : Fin k → Bool =>
      f ⟨M * b, hMb⟩ = false ∧ ownerF f = m ∧ vOf f = q)).card = B := by
  intro M b isConst uOf vOf ownerF m htot q
  have hv_eq : ∀ q1 q2 : Fin b,
      (Finset.univ.filter (fun f : Fin k → Bool =>
        f ⟨M * b, hMb⟩ = false ∧ ownerF f = m ∧ vOf f = q1)).card =
      (Finset.univ.filter (fun f : Fin k → Bool =>
        f ⟨M * b, hMb⟩ = false ∧ ownerF f = m ∧ vOf f = q2)).card := by
    intro q1 q2
    let sw (qt : Fin b) (f : Fin k → Bool) : Fin k → Bool := fun i =>
      if h1 : M * b + 1 + d ≤ i.val ∧ i.val < M * b + 1 + d + t then
        qt.val.testBit (i.val - (M * b + 1 + d))
      else f i
    have hsw_v : ∀ qt f, vOf (sw qt f) = qt := by
      intro qt f
      apply (fin_bit_equiv t).injective
      ext l
      rw [fin_bit_equiv_testBit, fin_bit_equiv_testBit, bitsNat_testBit]
      dsimp only [sw]
      have hin : M * b + 1 + d ≤ M * b + 1 + d + l.val ∧ M * b + 1 + d + l.val < M * b + 1 + d + t := by
        have := l.isLt; omega
      rw [dif_pos hin]
      congr 1; exact Nat.add_sub_cancel_left _ _
    have hsw_keep : ∀ qt f, sw qt f ⟨M * b, hMb⟩ = f ⟨M * b, hMb⟩ ∧ ownerF (sw qt f) = ownerF f := by
      intro qt f
      have hsp : sw qt f ⟨M * b, hMb⟩ = f ⟨M * b, hMb⟩ := by
        dsimp only [sw]; have h1 : ¬ (M * b + 1 + d ≤ M * b ∧ M * b < M * b + 1 + d + t) := by omega
        simp only [h1, dite_false]
      have hu : uOf (sw qt f) = uOf f := by
        rw [bitsNat_eq_iff]; intro l; dsimp only [sw]
        have h1 : ¬ (M * b + 1 + d ≤ M * b + 1 + l.val ∧ M * b + 1 + l.val < M * b + 1 + d + t) := by
          have := l.isLt; omega
        simp only [h1, dite_false]
      have hc : isConst (sw qt f) = isConst f := by
        funext m'; dsimp only [isConst]
        have hbit : ∀ j' : Fin b, sw qt f ⟨m'.val * b + j'.val, lt_trans (mul_add_lt_mul m'.isLt j'.isLt) hMb⟩ =
            f ⟨m'.val * b + j'.val, lt_trans (mul_add_lt_mul m'.isLt j'.isLt) hMb⟩ := by
          intro j'; dsimp only [sw]
          have hlt := mul_add_lt_mul m'.isLt j'.isLt
          have h1 : ¬ (M * b + 1 + d ≤ m'.val * b + j'.val ∧ m'.val * b + j'.val < M * b + 1 + d + t) := by omega
          simp only [h1, dite_false]
        simp_rw [hbit]
      exact ⟨hsp, by dsimp only [ownerF]; rw [hc, hu]⟩
    have hsw_inv : ∀ qt1 qt2 f, vOf f = qt1 → sw qt1 (sw qt2 f) = f := by
      intro qt1 qt2 f hv1; ext i
      by_cases h1 : M * b + 1 + d ≤ i.val ∧ i.val < M * b + 1 + d + t
      · dsimp only [sw]; rw [dif_pos h1, ← hv1]
        let l : Fin t := ⟨i.val - (M * b + 1 + d), by omega⟩
        have htb := bitsNat_testBit f (M * b + 1 + d) t hv_b l
        change (vOf f).val.testBit l.val = f i
        rw [htb]; congr 1; ext; dsimp only [l]; omega
      · dsimp only [sw]; simp only [h1, dite_false]
    refine Finset.card_bij (fun f _ => sw q2 f) ?_ ?_ ?_
    · intro f hf
      rcases (Finset.mem_filter.mp hf).2 with ⟨hf0, hfm, _⟩
      have hk := hsw_keep q2 f
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk.1.trans hf0, hk.2.trans hfm, hsw_v q2 f⟩
    · intro f1 hf1 f2 hf2 hEq
      have hv1 := (Finset.mem_filter.mp hf1).2.2.2
      have hv2 := (Finset.mem_filter.mp hf2).2.2.2
      have := congrArg (sw q1) hEq
      rw [hsw_inv q1 q2 f1 hv1, hsw_inv q1 q2 f2 hv2] at this; exact this
    · intro f hf
      rcases (Finset.mem_filter.mp hf).2 with ⟨hf0, hfm, hfv⟩
      have hk := hsw_keep q1 f
      exact ⟨sw q1 f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk.1.trans hf0, hk.2.trans hfm, hsw_v q1 f⟩,
        hsw_inv q2 q1 f hfv⟩
  have hsum_v : (∑ q' : Fin b, (Finset.univ.filter (fun f : Fin k → Bool =>
      f ⟨M * b, hMb⟩ = false ∧ ownerF f = m ∧ vOf f = q')).card) = b * B := by
    rw [← htot, Finset.card_eq_sum_ones,
      ← Finset.sum_fiberwise_of_maps_to (g := vOf) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl; intro q' _
    rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.filter_filter]
    congr 1; ext f; simp [and_assoc]
  have hconst_v : (∑ q' : Fin b, (Finset.univ.filter (fun f : Fin k → Bool =>
      f ⟨M * b, hMb⟩ = false ∧ ownerF f = m ∧ vOf f = q')).card) =
      b * (Finset.univ.filter (fun f : Fin k → Bool =>
        f ⟨M * b, hMb⟩ = false ∧ ownerF f = m ∧ vOf f = q)).card := by
    calc (∑ q' : Fin b, _) = ∑ _q' : Fin b, _ := Finset.sum_congr rfl (fun q' _ => hv_eq q' q)
      _ = b * _ := by simp
  have hmul_eq : b * (Finset.univ.filter (fun f : Fin k → Bool =>
      f ⟨M * b, hMb⟩ = false ∧ ownerF f = m ∧ vOf f = q)).card = b * B := by omega
  exact Nat.eq_of_mul_eq_mul_left ht hmul_eq

lemma inact_fib_helper (k a off : ℕ) (ha : 1 ≤ a) (hbound : off + 1 + (a - 1) ≤ k)
    (q : Fin (2 ^ (a - 1))) :
    (Finset.univ.filter (fun f : Fin k → Bool =>
      f ⟨off, by omega⟩ = true ∧ bitsNat f (off + 1) (a - 1) hbound = q)).card = 2 ^ (k - a) := by
  let fixed : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => off ≤ i.val ∧ i.val < off + a)
  have hfixed_card : fixed.card = a := by
    have hbij : fixed.card = (Finset.range a).card := by
      refine Finset.card_bij (fun i _ => i.val - off) ?_ ?_ ?_
      · intro i hi; exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hi).2; omega)
      · intro i1 hi1 i2 hi2 hEq
        have h1 := (Finset.mem_filter.mp hi1).2; have h2 := (Finset.mem_filter.mp hi2).2
        ext; omega
      · intro n hn
        have hna := Finset.mem_range.mp hn
        refine ⟨⟨off + n, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩, by dsimp; omega⟩
    rw [hbij, Finset.card_range]
  let target : Fin k → Bool := fun i =>
    if i.val = off then true
    else if off + 1 ≤ i.val ∧ i.val < off + a then q.val.testBit (i.val - (off + 1))
    else false
  have hfilt_eq : Finset.univ.filter (fun f : Fin k → Bool =>
        f ⟨off, by omega⟩ = true ∧ bitsNat f (off + 1) (a - 1) hbound = q) =
      Finset.univ.filter (fun f : Fin k → Bool => ∀ i ∈ fixed, f i = target i) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, fixed]
    constructor
    · rintro ⟨hf0, hfq⟩ i ⟨hlo, hhi⟩
      dsimp only [target]
      by_cases heq : i.val = off
      · rw [if_pos heq]
        have : i = ⟨off, by omega⟩ := Fin.ext heq
        rw [this, hf0]
      · have hin : off + 1 ≤ i.val ∧ i.val < off + a := by omega
        rw [if_neg heq, if_pos hin]
        let l : Fin (a - 1) := ⟨i.val - (off + 1), by omega⟩
        have htb := bitsNat_testBit f (off + 1) (a - 1) hbound l
        rw [hfq] at htb
        change f i = q.val.testBit l.val
        rw [htb]; congr 1; ext; dsimp only [l]; omega
    · intro hall
      refine ⟨?_, ?_⟩
      · have h1 := hall ⟨off, by omega⟩ ⟨by dsimp; omega, by dsimp; omega⟩
        simpa [target] using h1
      · apply (fin_bit_equiv (a - 1)).injective
        ext l
        rw [fin_bit_equiv_testBit, fin_bit_equiv_testBit, bitsNat_testBit]
        have h1 := hall ⟨off + 1 + l.val, by have := l.isLt; omega⟩ ⟨by dsimp; omega, by dsimp; have := l.isLt; omega⟩
        rw [h1]; dsimp only [target]
        have hne : off + 1 + l.val ≠ off := by omega
        have hin : off + 1 ≤ off + 1 + l.val ∧ off + 1 + l.val < off + a := by
          have := l.isLt; omega
        rw [if_neg hne, if_pos hin]
        congr 1; exact Nat.add_sub_cancel_left _ _
  rw [hfilt_eq]
  let eFree : {f : Fin k → Bool // ∀ i ∈ fixed, f i = target i} ≃ ({i : Fin k // i ∉ fixed} → Bool) :=
    { toFun := fun f i => f.1 i.1
      invFun := fun h => ⟨fun i => if hi : i ∈ fixed then target i else h ⟨i, hi⟩, fun i hi => by simp [hi]⟩
      left_inv := fun f => by ext i; by_cases hi : i ∈ fixed <;> simp [hi, f.2]
      right_inv := fun h => by ext i; simp [i.2] }
  rw [← Fintype.card_subtype, Fintype.card_congr eFree, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin, hfixed_card]

lemma nc_card_helper (k d t : ℕ) (hd : 0 < 2 ^ d) (ht : 0 < 2 ^ t)
    (hMb : 2 ^ d * 2 ^ t < k) (hu_b : 2 ^ d * 2 ^ t + 1 + d ≤ k)
    (m : Fin (2 ^ d)) :
    let M := 2 ^ d
    let b := 2 ^ t
    let isConst : (Fin k → Bool) → Fin M → Bool := fun f m' =>
      decide ((∀ j : Fin b, f ⟨m'.val * b + j.val,
        lt_trans (mul_add_lt_mul m'.isLt j.isLt) hMb⟩ = false) ∨
        (∀ j : Fin b, f ⟨m'.val * b + j.val,
        lt_trans (mul_add_lt_mul m'.isLt j.isLt) hMb⟩ = true))
    let uOf : (Fin k → Bool) → Fin M := fun f => bitsNat f (M * b + 1) d hu_b
    (Finset.univ.filter (fun f : Fin k → Bool =>
      f ⟨M * b, hMb⟩ = false ∧ uOf f = m ∧ ∀ m' : Fin M, isConst f m' = false)).card =
      (2 ^ b - 2) ^ M * 2 ^ (k - M * b - 1 - d) := by
  intro M b isConst uOf
  have hMb' : M * b < k := hMb
  have hu_b' : M * b + 1 + d ≤ k := hu_b
  let nonConstB : Finset (Fin b → Bool) := Finset.univ.filter (fun v =>
    ¬ ((∀ j, v j = false) ∨ (∀ j, v j = true)))
  have hncB_card : nonConstB.card = 2 ^ b - 2 := by
    have hcomp : (Finset.univ \ nonConstB).card = 2 := by
      have heq : Finset.univ \ nonConstB = {fun _ => false, fun _ => true} := by
        ext v
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter,
          not_not, Finset.mem_insert, Finset.mem_singleton, nonConstB]
        constructor
        · rintro (h0 | h1)
          · left; exact funext h0
          · right; exact funext h1
        · rintro (rfl | rfl)
          · left; intro _; rfl
          · right; intro _; rfl
      rw [heq, Finset.card_pair]
      intro hEq
      have := congrFun hEq ⟨0, ht⟩
      exact absurd this (by decide)
    have htot : (Finset.univ : Finset (Fin b → Bool)).card = 2 ^ b := by simp
    have hle2 : nonConstB.card + (Finset.univ \ nonConstB).card = 2 ^ b := by
      rw [← Finset.card_union_of_disjoint Finset.disjoint_sdiff,
        Finset.union_sdiff_of_subset (Finset.subset_univ _), htot]
    omega
  let freeIdx : Finset (Fin k) := Finset.univ.filter (fun i : Fin k =>
    M * b ≤ i.val ∧ i.val ≠ M * b ∧ ¬ (M * b + 1 ≤ i.val ∧ i.val < M * b + 1 + d))
  have hfree_card : freeIdx.card = k - M * b - 1 - d := by
    let used : Finset (Fin k) := Finset.univ.filter (fun i : Fin k => i.val < M * b + 1 + d)
    have hused_card : used.card = M * b + 1 + d := by
      have hbij : used.card = (Finset.range (M * b + 1 + d)).card := by
        refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
        · intro i hi; exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
        · intro i1 _ i2 _ heq; exact Fin.ext heq
        · intro n hn
          have hlt := Finset.mem_range.mp hn
          exact ⟨⟨n, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, rfl⟩
      rw [hbij, Finset.card_range]
    have hcompl : freeIdx = Finset.univ \ used := by
      ext i; simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, freeIdx, used]; omega
    rw [hcompl, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hused_card]
    omega
  let Snc := Finset.univ.filter (fun f : Fin k → Bool =>
    f ⟨M * b, hMb⟩ = false ∧ uOf f = m ∧ ∀ m' : Fin M, isConst f m' = false)
  let eNC : {f : Fin k → Bool // f ∈ Snc} ≃
      ((Fin M → {v : Fin b → Bool // v ∈ nonConstB}) × ({i : Fin k // i ∈ freeIdx} → Bool)) :=
    { toFun := fun f =>
        (fun m' => ⟨fun j => f.1 ⟨m'.val * b + j.val, lt_trans (mul_add_lt_mul m'.isLt j.isLt) hMb⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
              have hnc := (Finset.mem_filter.mp f.2).2.2.2 m'
              dsimp only [isConst] at hnc
              exact decide_eq_false_iff_not.mp hnc⟩⟩,
         fun i => f.1 i.1)
      invFun := fun p =>
        ⟨fun i =>
          if h1 : i.val < M * b then
            (p.1 ⟨i.val / b, Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm b M])⟩).1
              ⟨i.val % b, Nat.mod_lt _ ht⟩
          else if h2 : i.val = M * b then false
          else if h3 : M * b + 1 ≤ i.val ∧ i.val < M * b + 1 + d then
            m.val.testBit (i.val - (M * b + 1))
          else p.2 ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_not_lt h1, h2, h3⟩⟩,
         Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
           have hnot1 : ¬ (M * b < M * b) := by omega
           simp only [hnot1, dite_false, dite_true], by
           apply (fin_bit_equiv d).injective
           ext l
           rw [fin_bit_equiv_testBit, fin_bit_equiv_testBit, bitsNat_testBit]
           have hltl := l.isLt
           have hn1 : ¬ (M * b + 1 + l.val < M * b) := by omega
           have hn2 : M * b + 1 + l.val ≠ M * b := by omega
           have h3 : M * b + 1 ≤ M * b + 1 + l.val ∧ M * b + 1 + l.val < M * b + 1 + d := by omega
           rw [dif_neg hn1, dif_neg hn2, dif_pos h3]
           congr 1; exact Nat.add_sub_cancel_left _ _, by
           intro m'
           dsimp only [isConst]
           apply decide_eq_false
           have hbit : ∀ j : Fin b,
               (if h1 : m'.val * b + j.val < M * b then
                 (p.1 ⟨(m'.val * b + j.val) / b, Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm b M])⟩).1
                   ⟨(m'.val * b + j.val) % b, Nat.mod_lt _ ht⟩
                else if h2 : m'.val * b + j.val = M * b then false
                else if h3 : M * b + 1 ≤ m'.val * b + j.val ∧ m'.val * b + j.val < M * b + 1 + d then
                  m.val.testBit (m'.val * b + j.val - (M * b + 1))
                else p.2 ⟨⟨m'.val * b + j.val, lt_trans (mul_add_lt_mul m'.isLt j.isLt) hMb⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_not_lt h1, h2, h3⟩⟩) = (p.1 m').1 j := by
             intro j
             have hlt : m'.val * b + j.val < M * b := mul_add_lt_mul m'.isLt j.isLt
             rw [dif_pos hlt]
             have hdiv1 : (m'.val * b + j.val) / b = m'.val := by
               rw [Nat.mul_comm _ b, Nat.mul_add_div ht, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
             have hmod1 : (m'.val * b + j.val) % b = j.val := by
               rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt j.isLt]
             have hf1 : (⟨(m'.val * b + j.val) / b, Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm b M])⟩ : Fin M) = m' := Fin.ext hdiv1
             have hf2 : (⟨(m'.val * b + j.val) % b, Nat.mod_lt _ ht⟩ : Fin b) = j := Fin.ext hmod1
             rw [hf1, hf2]
           simp_rw [hbit]
           exact (Finset.mem_filter.mp (p.1 m').2).2⟩⟩
      left_inv := fun f => by
        apply Subtype.ext; funext i
        by_cases h1 : i.val < M * b
        · simp only [h1, dite_true]
          apply congrArg f.1; ext; dsimp only; rw [Nat.mul_comm, Nat.div_add_mod]
        · simp only [h1, dite_false]
          by_cases h2 : i.val = M * b
          · simp only [h2, dite_true]
            have hi : i = ⟨M * b, hMb⟩ := Fin.ext h2
            rw [hi, (Finset.mem_filter.mp f.2).2.1]
          · simp only [h2, dite_false]
            by_cases h3 : M * b + 1 ≤ i.val ∧ i.val < M * b + 1 + d
            · rw [dif_pos h3]
              have hu : uOf f.1 = m := (Finset.mem_filter.mp f.2).2.2.1
              let l : Fin d := ⟨i.val - (M * b + 1), by omega⟩
              have htb : (uOf f.1).val.testBit l.val = f.1 ⟨M * b + 1 + l.val, by have := l.isLt; omega⟩ :=
                bitsNat_testBit f.1 (M * b + 1) d hu_b l
              rw [hu] at htb
              change m.val.testBit l.val = f.1 i
              rw [htb]; apply congrArg f.1; ext; dsimp only [l]; omega
            · rw [dif_neg h3]
      right_inv := fun p => by
        apply Prod.ext
        · funext m'; apply Subtype.ext; funext j
          have hlt : m'.val * b + j.val < M * b := mul_add_lt_mul m'.isLt j.isLt
          dsimp only; rw [dif_pos hlt]
          have hdiv1 : (m'.val * b + j.val) / b = m'.val := by
            rw [Nat.mul_comm _ b, Nat.mul_add_div ht, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
          have hmod1 : (m'.val * b + j.val) % b = j.val := by
            rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt j.isLt]
          have hf1 : (⟨(m'.val * b + j.val) / b, Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm b M])⟩ : Fin M) = m' := Fin.ext hdiv1
          have hf2 : (⟨(m'.val * b + j.val) % b, Nat.mod_lt _ ht⟩ : Fin b) = j := Fin.ext hmod1
          rw [hf1, hf2]
        · funext i
          rcases (Finset.mem_filter.mp i.2).2 with ⟨h1, h2, h3⟩
          have hn1 : ¬ (i.val < M * b) := by omega
          dsimp only; rw [dif_neg hn1, dif_neg h2, dif_neg h3] }
  have hSnc : Snc.card = Fintype.card {f : Fin k → Bool // f ∈ Snc} := (Fintype.card_coe Snc).symm
  rw [hSnc, Fintype.card_congr eNC, Fintype.card_prod, Fintype.card_fun, Fintype.card_coe,
    hncB_card, Fintype.card_fin, Fintype.card_fun, Fintype.card_coe, hfree_card, Fintype.card_bool]

lemma active_blocks_helper (k a d t B : ℕ)
    (h2b_le : 2 * 2 ^ t ≤ a) (hM_pos : 0 < 2 ^ d) (hb_pos : 0 < 2 ^ t)
    (hd_add_t : d + t = a - 1) (h2Mb_eq : 2 * (2 ^ d * 2 ^ t) = 2 ^ a)
    (hB_eq : B = 2 ^ (k - a)) (ha_le_k : a ≤ k)
    (hMb_lt : 2 ^ d * 2 ^ t < k) (hu_bound : 2 ^ d * 2 ^ t + 1 + d ≤ k)
    (hv_bound : 2 ^ d * 2 ^ t + 1 + d + t ≤ k)
    (g : Fin (2 ^ k) → Fin (2 ^ a)) (flip : Fin (2 ^ k) → Bool)
    (K : Fin (2 ^ k) → Fin (2 ^ k) → ℤ)
    (hrot_fib : ∀ m : Fin (2 ^ d),
      (Finset.univ.filter (fun f : Fin k → Bool =>
        f ⟨2 ^ d * 2 ^ t, hMb_lt⟩ = false ∧
        firstConstFrom hM_pos (fun m' =>
          decide ((∀ j : Fin (2 ^ t), f ⟨m'.val * 2 ^ t + j.val,
            lt_trans (mul_add_lt_mul m'.isLt j.isLt) hMb_lt⟩ = false) ∨
            (∀ j : Fin (2 ^ t), f ⟨m'.val * 2 ^ t + j.val,
            lt_trans (mul_add_lt_mul m'.isLt j.isLt) hMb_lt⟩ = true)))
          (bitsNat f (2 ^ d * 2 ^ t + 1) d hu_bound) = m)).card = 2 ^ t * B)
    (hK_fact : ∀ x y, K x y =
      (bSign (flip x) * bSign (x.val.testBit (g y).val)) *
      (bSign (flip y) * bSign (y.val.testBit (g x).val)))
    (hg_act : ∀ x, fin_bit_equiv k x ⟨2 ^ d * 2 ^ t, hMb_lt⟩ = false →
      (g x).val = (firstConstFrom hM_pos (fun m' =>
          decide ((∀ j : Fin (2 ^ t), fin_bit_equiv k x ⟨m'.val * 2 ^ t + j.val,
            lt_trans (mul_add_lt_mul m'.isLt j.isLt) hMb_lt⟩ = false) ∨
            (∀ j : Fin (2 ^ t), fin_bit_equiv k x ⟨m'.val * 2 ^ t + j.val,
            lt_trans (mul_add_lt_mul m'.isLt j.isLt) hMb_lt⟩ = true)))
          (bitsNat (fin_bit_equiv k x) (2 ^ d * 2 ^ t + 1) d hu_bound)).val * 2 ^ t +
        (bitsNat (fin_bit_equiv k x) (2 ^ d * 2 ^ t + 1 + d) t hv_bound).val)
    (hflip_act : ∀ x, fin_bit_equiv k x ⟨2 ^ d * 2 ^ t, hMb_lt⟩ = false →
      flip x =
        let f := fin_bit_equiv k x
        let m := firstConstFrom hM_pos (fun m' =>
          decide ((∀ j : Fin (2 ^ t), f ⟨m'.val * 2 ^ t + j.val,
            lt_trans (mul_add_lt_mul m'.isLt j.isLt) hMb_lt⟩ = false) ∨
            (∀ j : Fin (2 ^ t), f ⟨m'.val * 2 ^ t + j.val,
            lt_trans (mul_add_lt_mul m'.isLt j.isLt) hMb_lt⟩ = true)))
          (bitsNat f (2 ^ d * 2 ^ t + 1) d hu_bound)
        decide (∀ j : Fin (2 ^ t), f ⟨m.val * 2 ^ t + j.val,
          lt_trans (mul_add_lt_mul m.isLt j.isLt) hMb_lt⟩ = true)) :
    let M := 2 ^ d
    let b := 2 ^ t
    let eBits := fin_bit_equiv k
    let isConst : (Fin k → Bool) → Fin M → Bool := fun f m =>
      decide ((∀ j : Fin b, f ⟨m.val * b + j.val,
        lt_trans (mul_add_lt_mul m.isLt j.isLt) hMb_lt⟩ = false) ∨
        (∀ j : Fin b, f ⟨m.val * b + j.val,
        lt_trans (mul_add_lt_mul m.isLt j.isLt) hMb_lt⟩ = true))
    let uOf : (Fin k → Bool) → Fin M := fun f => bitsNat f (M * b + 1) d hu_bound
    let ownerF : (Fin k → Bool) → Fin M := fun f => firstConstFrom hM_pos (isConst f) (uOf f)
    let blockSet : Fin M → Finset (Fin (2 ^ k)) := fun m =>
      Finset.univ.filter (fun x : Fin (2 ^ k) => eBits x ⟨M * b, hMb_lt⟩ = false ∧ ownerF (eBits x) = m)
    (∀ m m' : Fin M, m ≠ m' → ∀ y ∈ blockSet m', (∑ x ∈ blockSet m, K x y) = 0) ∧
    (∀ m : Fin M, ((blockSet m).card : ℤ) ^ 2 ≤ 4 * ∑ x ∈ blockSet m, ∑ y ∈ blockSet m, K x y) := by
  intro M b eBits isConst uOf ownerF blockSet
  let L := b * B
  let vOf : (Fin k → Bool) → Fin b := fun f => bitsNat f (M * b + 1 + d) t hv_bound
  have hMb_lt' : M * b < k := hMb_lt
  have hu_bound' : M * b + 1 + d ≤ k := hu_bound
  have h2Mb_eq' : 2 * (M * b) = 2 ^ a := h2Mb_eq
  have h2b_le' : 2 * b ≤ a := h2b_le
  have hb_pos' : 1 ≤ b := hb_pos
  have hM_pos' : 0 < M := hM_pos
  have hblock_card : ∀ m : Fin M, (blockSet m).card = L := by
    intro m
    have hbij : (blockSet m).card = (Finset.univ.filter (fun f : Fin k → Bool =>
        f ⟨M * b, hMb_lt⟩ = false ∧ ownerF f = m)).card := by
      refine Finset.card_bij (fun x _ => eBits x) ?_ ?_ ?_
      · intro x hx; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
      · intro x1 _ x2 _ heq; exact eBits.injective heq
      · intro f hf
        exact ⟨eBits.symm f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rw [eBits.apply_symm_apply]; exact (Finset.mem_filter.mp hf).2⟩, eBits.apply_symm_apply f⟩
    rw [hbij, hrot_fib m]
  let τ : Fin M → (Fin k → Bool) → (Fin k → Bool) := fun m' f i =>
    if m'.val * b ≤ i.val ∧ i.val < (m'.val + 1) * b then !(f i) else f i
  have hτ_inv : ∀ m' f, τ m' (τ m' f) = f := by
    intro m' f; ext i; dsimp only [τ]; split_ifs <;> simp
  have hτ_pres : ∀ m' f,
      τ m' f ⟨M * b, hMb_lt⟩ = f ⟨M * b, hMb_lt⟩ ∧
      uOf (τ m' f) = uOf f ∧ vOf (τ m' f) = vOf f ∧ isConst (τ m' f) = isConst f := by
    intro m' f
    have hmb_le : (m'.val + 1) * b ≤ M * b := Nat.mul_le_mul_right b m'.isLt
    have hsp : τ m' f ⟨M * b, hMb_lt⟩ = f ⟨M * b, hMb_lt⟩ := by
      dsimp only [τ]; have h1 : ¬ (m'.val * b ≤ M * b ∧ M * b < (m'.val + 1) * b) := by omega
      rw [if_neg h1]
    have hu : uOf (τ m' f) = uOf f := by
      rw [bitsNat_eq_iff]; intro l; dsimp only [τ]
      have h1 : ¬ (m'.val * b ≤ M * b + 1 + l.val ∧ M * b + 1 + l.val < (m'.val + 1) * b) := by omega
      rw [if_neg h1]
    have hv : vOf (τ m' f) = vOf f := by
      rw [bitsNat_eq_iff]; intro l; dsimp only [τ]
      have h1 : ¬ (m'.val * b ≤ M * b + 1 + d + l.val ∧ M * b + 1 + d + l.val < (m'.val + 1) * b) := by omega
      rw [if_neg h1]
    have hc : isConst (τ m' f) = isConst f := by
      funext m
      by_cases hmm : m = m'
      · subst hmm
        dsimp only [isConst]
        have hbit : ∀ j : Fin b, τ m f ⟨m.val * b + j.val,
            lt_trans (mul_add_lt_mul m.isLt j.isLt) hMb_lt⟩ =
            !(f ⟨m.val * b + j.val,
            lt_trans (mul_add_lt_mul m.isLt j.isLt) hMb_lt⟩) := by
          intro j; dsimp only [τ]
          have hin : m.val * b ≤ m.val * b + j.val ∧ m.val * b + j.val < (m.val + 1) * b :=
            ⟨Nat.le_add_right _ _, by have := j.isLt; rw [Nat.add_mul, one_mul]; omega⟩
          rw [if_pos hin]
        simp_rw [hbit]
        apply decide_eq_decide.mpr
        simp only [Bool.not_eq_false', Bool.not_eq_true']
        exact or_comm
      · dsimp only [isConst]
        have hbit : ∀ j : Fin b, τ m' f ⟨m.val * b + j.val,
            lt_trans (mul_add_lt_mul m.isLt j.isLt) hMb_lt⟩ =
            f ⟨m.val * b + j.val,
            lt_trans (mul_add_lt_mul m.isLt j.isLt) hMb_lt⟩ := by
          intro j; dsimp only [τ]
          have hnot : ¬ (m'.val * b ≤ m.val * b + j.val ∧ m.val * b + j.val < (m'.val + 1) * b) := by
            intro ⟨hlo, hhi⟩
            have hj := j.isLt
            have hne : m.val ≠ m'.val := fun h => hmm (Fin.ext h)
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · have : (m.val + 1) * b ≤ m'.val * b := Nat.mul_le_mul_right b hlt
              rw [Nat.add_mul, one_mul] at this; omega
            · have : (m'.val + 1) * b ≤ m.val * b := Nat.mul_le_mul_right b hgt
              omega
          rw [if_neg hnot]
        simp_rw [hbit]
    exact ⟨hsp, hu, hv, hc⟩
  have hM_zero_ext : ∀ (m m' : Fin M), m ≠ m' → ∀ (q : Fin b) (l : Fin b),
      let Cm_q := (blockSet m).filter (fun x => vOf (eBits x) = q)
      (∑ x ∈ Cm_q, bSign (flip x) * bSign (x.val.testBit (m'.val * b + l.val))) = 0 := by
    intro m m' hne q l Cm_q
    let inv : Fin (2 ^ k) → Fin (2 ^ k) := fun x => eBits.symm (τ m' (eBits x))
    have hinv_inv : ∀ x, inv (inv x) = x := by
      intro x; dsimp only [inv]; rw [eBits.apply_symm_apply, hτ_inv, eBits.symm_apply_apply]
    have hinv_mem : ∀ x ∈ Cm_q, inv x ∈ Cm_q := by
      intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxB, hxv⟩
      rcases (Finset.mem_filter.mp hxB).2 with ⟨hx0, hxm⟩
      have hp := hτ_pres m' (eBits x)
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩
      · dsimp only [inv]; rw [eBits.apply_symm_apply, hp.1, hx0]
      · dsimp only [inv]; rw [eBits.apply_symm_apply]; dsimp only [ownerF]; rw [hp.2.2.2, hp.2.1]; exact hxm
      · dsimp only [inv]; rw [eBits.apply_symm_apply, hp.2.2.1, hxv]
    have hinv_neg : ∀ x ∈ Cm_q,
        bSign (flip (inv x)) * bSign ((inv x).val.testBit (m'.val * b + l.val)) =
        -(bSign (flip x) * bSign (x.val.testBit (m'.val * b + l.val))) := by
      intro x hx
      have hxB := (Finset.mem_filter.mp hx).1
      have hx0 : eBits x ⟨M * b, hMb_lt⟩ = false := (Finset.mem_filter.mp hxB).2.1
      have hix0 : eBits (inv x) ⟨M * b, hMb_lt⟩ = false :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp (hinv_mem x hx)).1).2.1
      rw [hflip_act x hx0, hflip_act (inv x) hix0]
      have hfl_eq :
          decide (∀ j : Fin b, eBits (inv x) ⟨(ownerF (eBits (inv x))).val * b + j.val,
            lt_trans (mul_add_lt_mul (ownerF (eBits (inv x))).isLt j.isLt) hMb_lt⟩ = true) =
          decide (∀ j : Fin b, eBits x ⟨(ownerF (eBits x)).val * b + j.val,
            lt_trans (mul_add_lt_mul (ownerF (eBits x)).isLt j.isLt) hMb_lt⟩ = true) := by
        have hp := hτ_pres m' (eBits x)
        have hown : ownerF (eBits (inv x)) = ownerF (eBits x) := by
          dsimp only [inv]; rw [eBits.apply_symm_apply]; dsimp only [ownerF]; rw [hp.2.2.2, hp.2.1]
        have hxm : ownerF (eBits x) = m := (Finset.mem_filter.mp hxB).2.2
        rw [hown, hxm]
        apply decide_eq_decide.mpr
        apply forall_congr'; intro j
        dsimp only [inv]; rw [eBits.apply_symm_apply]; dsimp only [τ]
        have hnot : ¬ (m'.val * b ≤ m.val * b + j.val ∧ m.val * b + j.val < (m'.val + 1) * b) := by
          intro ⟨hlo, hhi⟩
          have hj := j.isLt
          have hne_v : m.val ≠ m'.val := fun h => hne (Fin.ext h)
          rcases lt_or_gt_of_ne hne_v with hlt | hgt
          · have : (m.val + 1) * b ≤ m'.val * b := Nat.mul_le_mul_right b hlt
            rw [Nat.add_mul, one_mul] at this; omega
          · have : (m'.val + 1) * b ≤ m.val * b := Nat.mul_le_mul_right b hgt
            omega
        rw [if_neg hnot]
      have hbit_lt : m'.val * b + l.val < k := lt_trans (mul_add_lt_mul m'.isLt l.isLt) hMb_lt
      have hbit_flip : (inv x).val.testBit (m'.val * b + l.val) = !(x.val.testBit (m'.val * b + l.val)) := by
        have h1 := fin_bit_equiv_testBit k (inv x) ⟨m'.val * b + l.val, hbit_lt⟩
        have h2 := fin_bit_equiv_testBit k x ⟨m'.val * b + l.val, hbit_lt⟩
        rw [← h1, ← h2]
        dsimp only [eBits, inv]
        rw [(fin_bit_equiv k).apply_symm_apply]
        dsimp only [τ]
        have hin : m'.val * b ≤ m'.val * b + l.val ∧ m'.val * b + l.val < (m'.val + 1) * b :=
          ⟨Nat.le_add_right _ _, by have := l.isLt; rw [Nat.add_mul, one_mul]; omega⟩
        rw [if_pos hin]
      change bSign (decide _) * bSign ((inv x).val.testBit (m'.val * b + l.val)) =
        -(bSign (decide _) * bSign (x.val.testBit (m'.val * b + l.val)))
      rw [hfl_eq, hbit_flip, bSign_not]
      ring
    have hsum_neg : (∑ x ∈ Cm_q, bSign (flip x) * bSign (x.val.testBit (m'.val * b + l.val))) =
        -(∑ x ∈ Cm_q, bSign (flip x) * bSign (x.val.testBit (m'.val * b + l.val))) := by
      calc (∑ x ∈ Cm_q, bSign (flip x) * bSign (x.val.testBit (m'.val * b + l.val)))
          = ∑ x ∈ Cm_q, bSign (flip (inv x)) * bSign ((inv x).val.testBit (m'.val * b + l.val)) := by
            refine Finset.sum_bij (fun x _ => inv x) hinv_mem
              (fun x1 _ x2 _ h => by have := congrArg inv h; rw [hinv_inv, hinv_inv] at this; exact this)
              (fun y hy => ⟨inv y, hinv_mem y hy, hinv_inv y⟩) (fun x _ => by rw [hinv_inv])
        _ = ∑ x ∈ Cm_q, -(bSign (flip x) * bSign (x.val.testBit (m'.val * b + l.val))) :=
            Finset.sum_congr rfl hinv_neg
        _ = -(∑ x ∈ Cm_q, bSign (flip x) * bSign (x.val.testBit (m'.val * b + l.val))) :=
            Finset.sum_neg_distrib _
    omega
  have hinter_act_zero : ∀ (m m' : Fin M), m ≠ m' → ∀ y ∈ blockSet m',
      (∑ x ∈ blockSet m, K x y) = 0 := by
    intro m m' hne y hy
    have hy0 := (Finset.mem_filter.mp hy).2.1
    have hym := (Finset.mem_filter.mp hy).2.2
    have hgy : (g y).val = m'.val * b + (vOf (eBits y)).val := by
      have := hg_act y hy0; change (g y).val = (ownerF (eBits y)).val * b + (vOf (eBits y)).val at this
      rw [this, hym]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun x => vOf (eBits x)) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_eq_zero; intro q _
    have hK_rew : ∀ x ∈ (blockSet m).filter (fun x => vOf (eBits x) = q),
        K x y = (bSign (flip y) * bSign (y.val.testBit (m.val * b + q.val))) *
          (bSign (flip x) * bSign (x.val.testBit (m'.val * b + (vOf (eBits y)).val))) := by
      intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxB, hxq⟩
      have hx0 := (Finset.mem_filter.mp hxB).2.1
      have hxm := (Finset.mem_filter.mp hxB).2.2
      have hgx : (g x).val = m.val * b + q.val := by
        have := hg_act x hx0; change (g x).val = (ownerF (eBits x)).val * b + (vOf (eBits x)).val at this
        rw [this, hxm, hxq]
      rw [hK_fact x y, hgx, hgy]; ring
    rw [Finset.sum_congr rfl hK_rew, ← Finset.mul_sum, hM_zero_ext m m' hne q (vOf (eBits y)), mul_zero]
  have hM_int : ∀ (m : Fin M) (q l : Fin b),
      let Cm_q := (blockSet m).filter (fun x => vOf (eBits x) = q)
      (∑ x ∈ Cm_q, bSign (flip x) * bSign (x.val.testBit (m.val * b + l.val))) =
      ((Cm_q.filter (fun x => isConst (eBits x) m = true)).card : ℤ) := by
    intro m q l Cm_q
    have hsplit_cm : Cm_q = Cm_q.filter (fun x => isConst (eBits x) m = true) ∪
        Cm_q.filter (fun x => isConst (eBits x) m = false) := by
      ext x; simp only [Finset.mem_union, Finset.mem_filter]
      cases isConst (eBits x) m <;> simp
    have hdisj_cm : Disjoint (Cm_q.filter (fun x => isConst (eBits x) m = true))
        (Cm_q.filter (fun x => isConst (eBits x) m = false)) := by
      rw [Finset.disjoint_left]; intro x h1 h2
      have a1 := (Finset.mem_filter.mp h1).2; have a2 := (Finset.mem_filter.mp h2).2
      rw [a1] at a2; exact absurd a2 (by decide)
    conv_lhs => rw [hsplit_cm]; rw [Finset.sum_union hdisj_cm]
    have hpos_part : (∑ x ∈ Cm_q.filter (fun x => isConst (eBits x) m = true),
        bSign (flip x) * bSign (x.val.testBit (m.val * b + l.val))) =
        ((Cm_q.filter (fun x => isConst (eBits x) m = true)).card : ℤ) := by
      have hone : ∀ x ∈ Cm_q.filter (fun x => isConst (eBits x) m = true),
          bSign (flip x) * bSign (x.val.testBit (m.val * b + l.val)) = 1 := by
        intro x hx
        rcases Finset.mem_filter.mp hx with ⟨hxC, hxc⟩
        have hxB := (Finset.mem_filter.mp hxC).1
        have hx0 := (Finset.mem_filter.mp hxB).2.1
        have hxm : ownerF (eBits x) = m := (Finset.mem_filter.mp hxB).2.2
        rw [hflip_act x hx0]
        change bSign (decide (∀ j : Fin b, eBits x ⟨(ownerF (eBits x)).val * b + j.val,
          lt_trans (mul_add_lt_mul (ownerF (eBits x)).isLt j.isLt) hMb_lt⟩ = true)) *
          bSign (x.val.testBit (m.val * b + l.val)) = 1
        rw [hxm]
        have hbit_lt : m.val * b + l.val < k := lt_trans (mul_add_lt_mul m.isLt l.isLt) hMb_lt
        have htb := fin_bit_equiv_testBit k x ⟨m.val * b + l.val, hbit_lt⟩
        rw [← htb]
        dsimp only [isConst] at hxc
        rcases decide_eq_true_eq.mp hxc with hall0 | hall1
        · have hnot1 : ¬ ∀ j : Fin b, eBits x ⟨m.val * b + j.val,
              lt_trans (mul_add_lt_mul m.isLt j.isLt) hMb_lt⟩ = true := by
            intro h1
            have h0 := hall0 ⟨0, hb_pos⟩
            have h1' := h1 ⟨0, hb_pos⟩
            rw [h0] at h1'; exact absurd h1' (by decide)
          rw [decide_eq_false hnot1, hall0 l]; rfl
        · rw [decide_eq_true_eq.mpr hall1, hall1 l]; rfl
      rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hzero_part : (∑ x ∈ Cm_q.filter (fun x => isConst (eBits x) m = false),
        bSign (flip x) * bSign (x.val.testBit (m.val * b + l.val))) = 0 := by
      let Snc := Cm_q.filter (fun x => isConst (eBits x) m = false)
      let inv : Fin (2 ^ k) → Fin (2 ^ k) := fun x => eBits.symm (τ m (eBits x))
      have hinv_inv : ∀ x, inv (inv x) = x := by
        intro x; dsimp only [inv]; rw [eBits.apply_symm_apply, hτ_inv, eBits.symm_apply_apply]
      have hinv_mem : ∀ x ∈ Snc, inv x ∈ Snc := by
        intro x hx
        rcases Finset.mem_filter.mp hx with ⟨hxC, hxnc⟩
        rcases Finset.mem_filter.mp hxC with ⟨hxB, hxv⟩
        rcases (Finset.mem_filter.mp hxB).2 with ⟨hx0, hxm⟩
        have hp := hτ_pres m (eBits x)
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, ?_⟩, ?_⟩
        · dsimp only [inv]; rw [eBits.apply_symm_apply, hp.1, hx0]
        · dsimp only [inv]; rw [eBits.apply_symm_apply]; dsimp only [ownerF]; rw [hp.2.2.2, hp.2.1]; exact hxm
        · dsimp only [inv]; rw [eBits.apply_symm_apply, hp.2.2.1, hxv]
        · dsimp only [inv]; rw [eBits.apply_symm_apply, hp.2.2.2]; exact hxnc
      have hinv_neg : ∀ x ∈ Snc,
          bSign (flip (inv x)) * bSign ((inv x).val.testBit (m.val * b + l.val)) =
          -(bSign (flip x) * bSign (x.val.testBit (m.val * b + l.val))) := by
        intro x hx
        have hxnc := (Finset.mem_filter.mp hx).2
        have hxC := (Finset.mem_filter.mp hx).1
        have hxB := (Finset.mem_filter.mp hxC).1
        have hx0 := (Finset.mem_filter.mp hxB).2.1
        have hix0 := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp (hinv_mem x hx)).1).1).2.1
        have hxm : ownerF (eBits x) = m := (Finset.mem_filter.mp hxB).2.2
        have hixm : ownerF (eBits (inv x)) = m := (Finset.mem_filter.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp (hinv_mem x hx)).1).1).2.2
        have hixnc : isConst (eBits (inv x)) m = false := (Finset.mem_filter.mp (hinv_mem x hx)).2
        have hfl_x : flip x = false := by
          rw [hflip_act x hx0]
          change decide (∀ j : Fin b, eBits x ⟨(ownerF (eBits x)).val * b + j.val,
            lt_trans (mul_add_lt_mul (ownerF (eBits x)).isLt j.isLt) hMb_lt⟩ = true) = false
          rw [hxm]
          apply decide_eq_false; intro hall1
          have : isConst (eBits x) m = true := decide_eq_true_eq.mpr (Or.inr hall1)
          rw [this] at hxnc; exact absurd hxnc (by decide)
        have hfl_ix : flip (inv x) = false := by
          rw [hflip_act (inv x) hix0]
          change decide (∀ j : Fin b, eBits (inv x) ⟨(ownerF (eBits (inv x))).val * b + j.val,
            lt_trans (mul_add_lt_mul (ownerF (eBits (inv x))).isLt j.isLt) hMb_lt⟩ = true) = false
          rw [hixm]
          apply decide_eq_false; intro hall1
          have : isConst (eBits (inv x)) m = true := decide_eq_true_eq.mpr (Or.inr hall1)
          rw [this] at hixnc; exact absurd hixnc (by decide)
        have hbit_lt : m.val * b + l.val < k := lt_trans (mul_add_lt_mul m.isLt l.isLt) hMb_lt
        have hbit_flip : (inv x).val.testBit (m.val * b + l.val) = !(x.val.testBit (m.val * b + l.val)) := by
          have h1 := fin_bit_equiv_testBit k (inv x) ⟨m.val * b + l.val, hbit_lt⟩
          have h2 := fin_bit_equiv_testBit k x ⟨m.val * b + l.val, hbit_lt⟩
          rw [← h1, ← h2]
          dsimp only [eBits, inv]
          rw [(fin_bit_equiv k).apply_symm_apply]
          dsimp only [τ]
          have hin : m.val * b ≤ m.val * b + l.val ∧ m.val * b + l.val < (m.val + 1) * b :=
            ⟨Nat.le_add_right _ _, by have := l.isLt; rw [Nat.add_mul, one_mul]; omega⟩
          rw [if_pos hin]
        rw [hfl_x, hfl_ix, hbit_flip, bSign_not]
        ring
      have hsum_neg : (∑ x ∈ Snc, bSign (flip x) * bSign (x.val.testBit (m.val * b + l.val))) =
          -(∑ x ∈ Snc, bSign (flip x) * bSign (x.val.testBit (m.val * b + l.val))) := by
        calc (∑ x ∈ Snc, bSign (flip x) * bSign (x.val.testBit (m.val * b + l.val)))
            = ∑ x ∈ Snc, bSign (flip (inv x)) * bSign ((inv x).val.testBit (m.val * b + l.val)) := by
              refine Finset.sum_bij (fun x _ => inv x) hinv_mem
                (fun x1 _ x2 _ h => by have := congrArg inv h; rw [hinv_inv, hinv_inv] at this; exact this)
                (fun y hy => ⟨inv y, hinv_mem y hy, hinv_inv y⟩) (fun x _ => by rw [hinv_inv])
          _ = ∑ x ∈ Snc, -(bSign (flip x) * bSign (x.val.testBit (m.val * b + l.val))) :=
              Finset.sum_congr rfl hinv_neg
          _ = -(∑ x ∈ Snc, bSign (flip x) * bSign (x.val.testBit (m.val * b + l.val))) :=
              Finset.sum_neg_distrib _
      change (∑ x ∈ Snc, bSign (flip x) * bSign (x.val.testBit (m.val * b + l.val))) = 0
      omega
    rw [hpos_part, hzero_part, add_zero]
  have hblock_hit_ge : ∀ m : Fin M, L ≤ 2 * ((blockSet m).filter (fun x => isConst (eBits x) m = true)).card := by
    have hhit_eq : ∀ m : Fin M,
        ((blockSet m).filter (fun x => isConst (eBits x) m = true)).card =
        ((Finset.univ.filter (fun f : Fin k → Bool =>
          f ⟨M * b, hMb_lt⟩ = false ∧ ownerF f = m ∧ isConst f m = true)).card) := by
      intro m
      refine Finset.card_bij (fun x _ => eBits x) ?_ ?_ ?_
      · intro x hx
        rcases Finset.mem_filter.mp hx with ⟨hxB, hxc⟩
        rcases (Finset.mem_filter.mp hxB).2 with ⟨hx0, hxm⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx0, hxm, hxc⟩
      · intro x1 _ x2 _ heq; exact eBits.injective heq
      · intro f hf
        rcases (Finset.mem_filter.mp hf).2 with ⟨hf0, hfm, hfc⟩
        exact ⟨eBits.symm f, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          by rw [eBits.apply_symm_apply]; exact hf0, by rw [eBits.apply_symm_apply]; exact hfm⟩,
          by rw [eBits.apply_symm_apply]; exact hfc⟩, eBits.apply_symm_apply f⟩
    have hfail_le : ∀ m : Fin M,
        2 * (Finset.univ.filter (fun f : Fin k → Bool =>
          f ⟨M * b, hMb_lt⟩ = false ∧ ownerF f = m ∧ isConst f m = false)).card ≤ L := by
      intro m
      have hsub_fail : Finset.univ.filter (fun f : Fin k → Bool =>
            f ⟨M * b, hMb_lt⟩ = false ∧ ownerF f = m ∧ isConst f m = false) ⊆
          Finset.univ.filter (fun f : Fin k → Bool =>
            f ⟨M * b, hMb_lt⟩ = false ∧ uOf f = m ∧ ∀ m' : Fin M, isConst f m' = false) := by
        intro f hf
        rcases (Finset.mem_filter.mp hf).2 with ⟨hf0, hfm, hfnc⟩
        have hall_nc : ∀ m' : Fin M, isConst f m' = false := by
          intro m'
          by_contra hne
          have ht : isConst f m' = true := Bool.eq_true_of_not_eq_false hne
          have hhit := firstConstFrom_hit hM_pos (isConst f) (uOf f) ⟨m', ht⟩
          change isConst f (ownerF f) = true at hhit
          rw [hfm, hfnc] at hhit; exact absurd hhit (by decide)
        have hu_eq : uOf f = m := by
          have hnone : (List.finRange M).find? (fun s =>
              isConst f ⟨((uOf f).val + s.val) % M, Nat.mod_lt _ hM_pos⟩) = none := by
            rw [List.find?_eq_none]
            intro s _; rw [hall_nc]; decide
          have ho : ownerF f = uOf f := by
            dsimp only [ownerF, firstConstFrom]
            rw [hnone]
          rw [← ho, hfm]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf0, hu_eq, hall_nc⟩
      have hcard_le := Finset.card_le_card hsub_fail
      have hcard_nc := nc_card_helper k d t hM_pos hb_pos hMb_lt hu_bound m
      dsimp only at hcard_nc
      have hL_pow : L = (2 ^ b) ^ M * 2 ^ (k - M * b - 1 - d) := by
        change 2 ^ t * B = (2 ^ b) ^ M * 2 ^ (k - M * b - 1 - d)
        rw [hB_eq, ← pow_add, ← pow_mul, ← pow_add, Nat.mul_comm b M]
        congr 1; omega
      have h2M_ge : 2 ^ b ≤ 2 * M := by
        have h1 : 2 ^ b * b ≤ 2 ^ (2 * b) := by
          rw [two_mul, pow_add]
          exact Nat.mul_le_mul_left _ (two_pow_ge_two_mul b hb_pos')
        have h2 : 2 ^ (2 * b) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) h2b_le'
        have h3 : 2 ^ a = 2 * M * b := by rw [← h2Mb_eq']; ring
        have h4 : 2 ^ b * b ≤ (2 * M) * b := by omega
        exact Nat.le_of_mul_le_mul_right h4 hb_pos'
      have hbern := bernoulli_half b M hb_pos' hM_pos' h2M_ge
      calc 2 * (Finset.univ.filter (fun f : Fin k → Bool =>
              f ⟨M * b, hMb_lt⟩ = false ∧ ownerF f = m ∧ isConst f m = false)).card
          ≤ 2 * ((2 ^ b - 2) ^ M * 2 ^ (k - M * b - 1 - d)) := by
            rw [← hcard_nc]; exact Nat.mul_le_mul_left 2 hcard_le
        _ = (2 * (2 ^ b - 2) ^ M) * 2 ^ (k - M * b - 1 - d) := by ring
        _ ≤ (2 ^ b) ^ M * 2 ^ (k - M * b - 1 - d) := Nat.mul_le_mul_right _ hbern
        _ = L := hL_pow.symm
    intro m
    have hsplit_m : (Finset.univ.filter (fun f : Fin k → Bool =>
          f ⟨M * b, hMb_lt⟩ = false ∧ ownerF f = m)).card =
        (Finset.univ.filter (fun f : Fin k → Bool =>
          f ⟨M * b, hMb_lt⟩ = false ∧ ownerF f = m ∧ isConst f m = true)).card +
        (Finset.univ.filter (fun f : Fin k → Bool =>
          f ⟨M * b, hMb_lt⟩ = false ∧ ownerF f = m ∧ isConst f m = false)).card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext f; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
        cases isConst f m <;> tauto
      · rw [Finset.disjoint_left]; intro f h1 h2
        have a1 := (Finset.mem_filter.mp h1).2.2.2; have a2 := (Finset.mem_filter.mp h2).2.2.2
        rw [a1] at a2; exact absurd a2 (by decide)
    rw [hrot_fib m] at hsplit_m
    rw [hhit_eq m]
    have hfl := hfail_le m
    change b * B = _ at hsplit_m
    dsimp only [L] at hfl ⊢
    omega
  have hblock_sum_ge : ∀ m : Fin M,
      ((blockSet m).card : ℤ) ^ 2 ≤ 4 * ∑ x ∈ blockSet m, ∑ y ∈ blockSet m, K x y := by
    intro m
    have hsum_eq : (∑ x ∈ blockSet m, ∑ y ∈ blockSet m, K x y) =
        (((blockSet m).filter (fun x => isConst (eBits x) m = true)).card : ℤ) ^ 2 := by
      have hfib_x : (∑ x ∈ blockSet m, ∑ y ∈ blockSet m, K x y) =
          ∑ q : Fin b, ∑ l : Fin b,
            (∑ x ∈ (blockSet m).filter (fun x => vOf (eBits x) = q),
              bSign (flip x) * bSign (x.val.testBit (m.val * b + l.val))) *
            (∑ y ∈ (blockSet m).filter (fun y => vOf (eBits y) = l),
              bSign (flip y) * bSign (y.val.testBit (m.val * b + q.val))) := by
        rw [← Finset.sum_fiberwise_of_maps_to (g := fun x => vOf (eBits x)) (t := Finset.univ)
          (fun _ _ => Finset.mem_univ _)]
        apply Finset.sum_congr rfl; intro q _
        have hinner : ∀ x ∈ (blockSet m).filter (fun x => vOf (eBits x) = q),
            (∑ y ∈ blockSet m, K x y) =
            ∑ l : Fin b, ∑ y ∈ (blockSet m).filter (fun y => vOf (eBits y) = l),
              (bSign (flip x) * bSign (x.val.testBit (m.val * b + l.val))) *
              (bSign (flip y) * bSign (y.val.testBit (m.val * b + q.val))) := by
          intro x hx
          rcases Finset.mem_filter.mp hx with ⟨hxB, hxq⟩
          have hx0 := (Finset.mem_filter.mp hxB).2.1
          have hxm := (Finset.mem_filter.mp hxB).2.2
          have hgx : (g x).val = m.val * b + q.val := by
            have := hg_act x hx0; change (g x).val = (ownerF (eBits x)).val * b + (vOf (eBits x)).val at this
            rw [this, hxm, hxq]
          rw [← Finset.sum_fiberwise_of_maps_to (g := fun y => vOf (eBits y)) (t := Finset.univ)
            (fun _ _ => Finset.mem_univ _)]
          apply Finset.sum_congr rfl; intro l _
          apply Finset.sum_congr rfl; intro y hy
          rcases Finset.mem_filter.mp hy with ⟨hyB, hyl⟩
          have hy0 := (Finset.mem_filter.mp hyB).2.1
          have hym := (Finset.mem_filter.mp hyB).2.2
          have hgy : (g y).val = m.val * b + l.val := by
            have := hg_act y hy0; change (g y).val = (ownerF (eBits y)).val * b + (vOf (eBits y)).val at this
            rw [this, hym, hyl]
          rw [hK_fact x y, hgx, hgy]
        rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
        apply Finset.sum_congr rfl; intro l _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro x _
        rw [Finset.mul_sum]
      rw [hfib_x]
      simp_rw [hM_int]
      have hsq : (∑ q : Fin b, ∑ l : Fin b,
          ((((blockSet m).filter (fun x => vOf (eBits x) = q)).filter (fun x => isConst (eBits x) m = true)).card : ℤ) *
          ((((blockSet m).filter (fun y => vOf (eBits y) = l)).filter (fun x => isConst (eBits x) m = true)).card : ℤ)) =
          (∑ q : Fin b, ((((blockSet m).filter (fun x => vOf (eBits x) = q)).filter
            (fun x => isConst (eBits x) m = true)).card : ℤ)) ^ 2 := by
        rw [sq, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro q _
        rw [Finset.mul_sum]
      rw [hsq]
      congr 1
      have hnat : (∑ q : Fin b, (((blockSet m).filter (fun x => vOf (eBits x) = q)).filter
          (fun x => isConst (eBits x) m = true)).card) =
          ((blockSet m).filter (fun x => isConst (eBits x) m = true)).card := by
        rw [Finset.card_eq_sum_ones,
          ← Finset.sum_fiberwise_of_maps_to (g := fun x => vOf (eBits x)) (t := Finset.univ)
            (fun _ _ => Finset.mem_univ _)]
        apply Finset.sum_congr rfl; intro q _
        rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.filter_filter, Finset.filter_filter]
        congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, blockSet]; tauto
      exact_mod_cast hnat
    rw [hsum_eq, hblock_card m]
    have hge : (L : ℤ) ≤ 2 * (((blockSet m).filter (fun x => isConst (eBits x) m = true)).card : ℤ) := by
      exact_mod_cast hblock_hit_ge m
    nlinarith
  exact ⟨hinter_act_zero, hblock_sum_ge⟩

lemma order_and_bound_helper (N r a M b B L : ℕ)
    (ha_lt_4b : a < 4 * b) (hL_eq : L = b * B) (h2ML_eq : 2 * (M * L) = N)
    (hMb_eq : M * b = r / 2) (h2Mb_eq : 2 * (M * b) = r) (hrB_eq : r * B = N)
    (hB_pos : 0 < B) (hL_pos : 0 < L)
    (π : Equiv.Perm (Fin N)) (flip : Fin N → Bool)
    (blockSet : Fin M → Finset (Fin N)) (inactSet : Fin (r / 2) → Finset (Fin N))
    (ActSet : Finset (Fin N))
    (hblock_card : ∀ m : Fin M, (blockSet m).card = L)
    (hinact_card : ∀ s : Fin (r / 2), (inactSet s).card = B)
    (hdisj_blocks : ∀ m1 m2 : Fin M, m1 ≠ m2 → Disjoint (blockSet m1) (blockSet m2))
    (hdisj_inact : ∀ s1 s2 : Fin (r / 2), s1 ≠ s2 → Disjoint (inactSet s1) (inactSet s2))
    (hdisj_act_inact : ∀ m s, Disjoint (blockSet m) (inactSet s))
    (hAct_iff : ∀ x : Fin N, x ∈ ActSet ↔ ∃ m : Fin M, x ∈ blockSet m)
    (hUniv_cover : ∀ x : Fin N, (∃ m : Fin M, x ∈ blockSet m) ∨ (∃ s : Fin (r / 2), x ∈ inactSet s))
    (hinter_act_zero : ∀ m m' : Fin M, m ≠ m' → ∀ y ∈ blockSet m',
      (∑ x ∈ blockSet m, bSign (xor (x.val.testBit ((π y).val % r)) (flip x)) *
        bSign (xor (y.val.testBit ((π x).val % r)) (flip y))) = 0)
    (hblock_sum_ge : ∀ m : Fin M, ((blockSet m).card : ℤ) ^ 2 ≤
      4 * ∑ x ∈ blockSet m, ∑ y ∈ blockSet m,
        bSign (xor (x.val.testBit ((π y).val % r)) (flip x)) *
          bSign (xor (y.val.testBit ((π x).val % r)) (flip y)))
    (hstep_inact : ∀ (u : ℕ) (P : Finset (Fin N)) (hu : u < r / 2), P ⊆ inactSet ⟨u, hu⟩ →
      let prior := ActSet ∪ (Finset.univ.filter (fun s : Fin (r / 2) => s.val < u)).biUnion inactSet
      (∑ x ∈ prior, ∑ y ∈ prior,
        bSign (xor (x.val.testBit ((π y).val % r)) (flip x)) *
          bSign (xor (y.val.testBit ((π x).val % r)) (flip y))) ≤
      ∑ x ∈ prior ∪ P, ∑ y ∈ prior ∪ P,
        bSign (xor (x.val.testBit ((π y).val % r)) (flip x)) *
          bSign (xor (y.val.testBit ((π x).val % r)) (flip y))) :
    ∃ (order : Equiv.Perm (Fin N)) (D : Finset (Fin N) → Finset (Fin N) → Bool),
      ∀ h ≤ N,
        let exposed : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => h ≤ (order i).val)
        let cost (out : Finset (Fin N) → Finset (Fin N) → Bool) : ℕ :=
          (Finset.univ.filter (fun z : Fin N × Fin N =>
            out ({z.1, z.2} : Finset (Fin N)) (exposed ∩ {z.1}) ≠
              xor (z.1.val.testBit ((π z.2).val % r)) (flip z.1))).card
        (∀ other : Finset (Fin N) → Finset (Fin N) → Bool, cost D ≤ cost other) ∧
        128 * cost D + min (h ^ 2) (a * B * h) ≤ 32 * h ^ 2 := by
  let T : Fin N → Fin N → Bool := fun x y => xor (x.val.testBit ((π y).val % r)) (flip x)
  let K : Fin N → Fin N → ℤ := fun x y => bSign (T x y) * bSign (T y x)
  have hK_sym : ∀ x y, K x y = K y x := fun x y => mul_comm _ _
  have hK_diag : ∀ x, K x x = 1 := fun x => bSign_sq (T x x)
  have hthin : ∀ m : Fin M, ∃ l : List (Fin N), l.Nodup ∧ l.toFinset = blockSet m ∧
      ∀ s ≤ L, (s : ℤ) ^ 2 ≤ 4 * ∑ x ∈ (l.take s).toFinset, ∑ y ∈ (l.take s).toFinset, K x y := by
    intro m
    obtain ⟨l, hnd, hto, hp⟩ := thin_order K hK_sym hK_diag (blockSet m) (hblock_sum_ge m)
    exact ⟨l, hnd, hto, fun s hs => hp s (by rw [hblock_card m]; exact hs)⟩
  let blockList : Fin M → List (Fin N) := fun m => (hthin m).choose
  have hblockList_nd : ∀ m, (blockList m).Nodup := fun m => (hthin m).choose_spec.1
  have hblockList_to : ∀ m, (blockList m).toFinset = blockSet m := fun m => (hthin m).choose_spec.2.1
  have hblockList_len : ∀ m, (blockList m).length = L := fun m => by
    rw [← List.toFinset_card_of_nodup (hblockList_nd m), hblockList_to m, hblock_card m]
  have hblockList_pref : ∀ m s, s ≤ L →
      (s : ℤ) ^ 2 ≤ 4 * ∑ x ∈ ((blockList m).take s).toFinset,
        ∑ y ∈ ((blockList m).take s).toFinset, K x y := fun m => (hthin m).choose_spec.2.2
  let inactList : Fin (r / 2) → List (Fin N) := fun s => (inactSet s).toList
  have hinactList_nd : ∀ s, (inactList s).Nodup := fun s => Finset.nodup_toList _
  have hinactList_to : ∀ s, (inactList s).toFinset = inactSet s := fun s => by ext x; simp [inactList]
  have hinact_len : ∀ s : Fin (r / 2), (inactList s).length = B := fun s => by
    rw [← List.toFinset_card_of_nodup (hinactList_nd s), hinactList_to s, hinact_card s]
  let fullActList : List (Fin N) := (List.finRange M).flatMap blockList
  let fullInactList : List (Fin N) := (List.finRange (r / 2)).flatMap inactList
  let fullList : List (Fin N) := fullActList ++ fullInactList
  have hfullAct_nd : fullActList.Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun m _ => hblockList_nd m, ?_⟩
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hlt x hx1 hx2
    have hne : (List.finRange M)[i] ≠ (List.finRange M)[j] := by
      simp only [List.getElem_finRange]; intro h; have := congrArg Fin.val h; dsimp at this; omega
    have h1 : x ∈ blockSet (List.finRange M)[i] := hblockList_to _ ▸ List.mem_toFinset.mpr hx1
    have h2 : x ∈ blockSet (List.finRange M)[j] := hblockList_to _ ▸ List.mem_toFinset.mpr hx2
    exact Finset.disjoint_left.mp (hdisj_blocks _ _ hne) h1 h2
  have hfullInact_nd : fullInactList.Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun s _ => hinactList_nd s, ?_⟩
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hlt x hx1 hx2
    have hne : (List.finRange (r / 2))[i] ≠ (List.finRange (r / 2))[j] := by
      simp only [List.getElem_finRange]; intro h; have := congrArg Fin.val h; dsimp at this; omega
    have h1 : x ∈ inactSet (List.finRange (r / 2))[i] := hinactList_to _ ▸ List.mem_toFinset.mpr hx1
    have h2 : x ∈ inactSet (List.finRange (r / 2))[j] := hinactList_to _ ▸ List.mem_toFinset.mpr hx2
    exact Finset.disjoint_left.mp (hdisj_inact _ _ hne) h1 h2
  have hfull_nd : fullList.Nodup := by
    rw [List.nodup_append]
    refine ⟨hfullAct_nd, hfullInact_nd, ?_⟩
    intro x hx1 y hy2 hxy
    subst hxy
    rcases List.mem_flatMap.mp hx1 with ⟨m, _, hxm⟩
    rcases List.mem_flatMap.mp hy2 with ⟨s, _, hxs⟩
    exact Finset.disjoint_left.mp (hdisj_act_inact m s)
      (hblockList_to m ▸ List.mem_toFinset.mpr hxm) (hinactList_to s ▸ List.mem_toFinset.mpr hxs)
  have hfull_to : fullList.toFinset = Finset.univ := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true, fullList, List.mem_append,
      fullActList, fullInactList, List.mem_flatMap, List.mem_finRange, true_and]
    rcases hUniv_cover x with ⟨m, hxm⟩ | ⟨s, hxs⟩
    · exact Or.inl ⟨m, List.mem_toFinset.mp (hblockList_to m ▸ hxm)⟩
    · exact Or.inr ⟨s, List.mem_toFinset.mp (hinactList_to s ▸ hxs)⟩
  obtain ⟨order, horder⟩ := list_to_perm fullList hfull_nd hfull_to
  obtain ⟨D, hD⟩ := decoder_optimal_and_cost order T
  refine ⟨order, D, ?_⟩
  intro h hh
  obtain ⟨hD_opt, hD_cost⟩ := hD h hh
  refine ⟨hD_opt, ?_⟩
  let H := Finset.univ.filter (fun i : Fin N => (order i).val < h)
  have hH_eq : H = (fullList.take h).toFinset := horder h hh
  have hS_ge : (min (h ^ 2) (a * B * h) : ℤ) ≤ 32 * ∑ x ∈ H, ∑ y ∈ H, K x y := by
    have hfullAct_len : fullActList.length = M * L := by
      dsimp only [fullActList]
      rw [List.length_flatMap]
      have hmap : (List.finRange M).map (fun m => (blockList m).length) = List.replicate M L := by
        apply List.ext_getElem
        · simp
        · intro i hi1 hi2; simp [hblockList_len]
      rw [hmap, List.sum_replicate, smul_eq_mul]
    have htake_act : ∀ q (hq : q ≤ M) s (hs : s ≤ L) (hlt : q < M ∨ s = 0),
        (fullActList.take (q * L + s)).toFinset =
          ((Finset.univ.filter (fun m : Fin M => m.val < q)).biUnion blockSet) ∪
            (if hq' : q < M then ((blockList ⟨q, hq'⟩).take s).toFinset else ∅) := by
      intro q hq s hs hlt
      have hpref_len : ∀ n (hn : n ≤ M),
          ((List.finRange M).take n).flatMap blockList = fullActList.take (n * L) := by
        intro n hn
        have hsplit : List.finRange M = (List.finRange M).take n ++ (List.finRange M).drop n :=
          (List.take_append_drop n (List.finRange M)).symm
        have hlen_n : (((List.finRange M).take n).flatMap blockList).length = n * L := by
          rw [List.length_flatMap]
          have hm : (((List.finRange M).take n).map (fun m => (blockList m).length)) = List.replicate n L := by
            apply List.ext_getElem
            · simp [hn]
            · intro i hi1 hi2; simp [hblockList_len]
          rw [hm, List.sum_replicate, smul_eq_mul]
        dsimp only [fullActList]
        conv_rhs => rw [hsplit, List.flatMap_append, List.take_append_of_le_length (by omega),
          List.take_of_length_le (by omega)]
      by_cases hq' : q < M
      · simp only [hq', dite_true]
        have hsplit_q : List.finRange M =
            (List.finRange M).take q ++ [⟨q, hq'⟩] ++ (List.finRange M).drop (q + 1) := by
          have h1 : (List.finRange M).drop q = ⟨q, hq'⟩ :: (List.finRange M).drop (q + 1) := by
            rw [List.drop_eq_getElem_cons (by simp [hq'])]
            simp
          conv_lhs => rw [← List.take_append_drop q (List.finRange M), h1]
          simp [List.append_assoc]
        have hlen_q : (((List.finRange M).take q).flatMap blockList).length = q * L := by
          rw [hpref_len q (by omega), List.length_take, hfullAct_len]
          have : q * L ≤ M * L := Nat.mul_le_mul_right L (by omega)
          omega
        have htake_eq : fullActList.take (q * L + s) =
            ((List.finRange M).take q).flatMap blockList ++ (blockList ⟨q, hq'⟩).take s := by
          dsimp only [fullActList]
          conv_lhs => rw [hsplit_q, List.flatMap_append, List.flatMap_append, List.flatMap_singleton]
          rw [List.append_assoc, List.take_append, hlen_q, List.take_of_length_le (by omega),
            Nat.add_sub_cancel_left, List.take_append_of_le_length (by rw [hblockList_len]; exact hs)]
        rw [htake_eq, List.toFinset_append]
        congr 1
        ext x
        simp only [List.mem_toFinset, List.mem_flatMap, Finset.mem_biUnion, Finset.mem_filter,
          Finset.mem_univ, true_and]
        constructor
        · rintro ⟨m, hm, hxm⟩
          have hmlt : m.val < q := by
            rw [List.mem_iff_getElem] at hm
            rcases hm with ⟨i, hi, rfl⟩
            rw [List.length_take, List.length_finRange] at hi
            simp only [List.getElem_take, List.getElem_finRange, Fin.val_cast]
            omega
          exact ⟨m, hmlt, hblockList_to m ▸ List.mem_toFinset.mpr hxm⟩
        · rintro ⟨m, hmlt, hxm⟩
          refine ⟨m, ?_, List.mem_toFinset.mp (hblockList_to m ▸ hxm)⟩
          rw [List.mem_iff_getElem]
          refine ⟨m.val, by rw [List.length_take, List.length_finRange]; omega, ?_⟩
          simp
      · have hs0 : s = 0 := hlt.resolve_left hq'
        subst hs0
        simp only [hq', dite_false, Nat.add_zero, Finset.union_empty]
        have hqM : q = M := by omega
        subst hqM
        rw [List.take_of_length_le (by omega)]
        ext x
        simp only [List.mem_toFinset, fullActList, List.mem_flatMap, List.mem_finRange, true_and,
          Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ]
        constructor
        · rintro ⟨m, hxm⟩
          exact ⟨m, m.isLt, hblockList_to m ▸ List.mem_toFinset.mpr hxm⟩
        · rintro ⟨m, _, hxm⟩
          exact ⟨m, List.mem_toFinset.mp (hblockList_to m ▸ hxm)⟩
    have hact_sum_split : ∀ q (hq : q ≤ M) s (hs : s ≤ L) (hlt : q < M ∨ s = 0),
        let S := (fullActList.take (q * L + s)).toFinset
        (∑ x ∈ S, ∑ y ∈ S, K x y) =
          (∑ m ∈ Finset.univ.filter (fun m : Fin M => m.val < q),
            ∑ x ∈ blockSet m, ∑ y ∈ blockSet m, K x y) +
          (if hq' : q < M then
            ∑ x ∈ ((blockList ⟨q, hq'⟩).take s).toFinset,
              ∑ y ∈ ((blockList ⟨q, hq'⟩).take s).toFinset, K x y
           else 0) := by
      intro q hq s hs hlt S
      have hS := htake_act q hq s hs hlt
      let Aset := (Finset.univ.filter (fun m : Fin M => m.val < q)).biUnion blockSet
      let Pset := if hq' : q < M then ((blockList ⟨q, hq'⟩).take s).toFinset else ∅
      have hPsub : ∀ hq' : q < M, ((blockList ⟨q, hq'⟩).take s).toFinset ⊆ blockSet ⟨q, hq'⟩ := by
        intro hq' x hx
        rw [← hblockList_to ⟨q, hq'⟩, List.mem_toFinset]
        exact List.mem_of_mem_take (List.mem_toFinset.mp hx)
      have hdisjAP : Disjoint Aset Pset := by
        rw [Finset.disjoint_left]; intro x hxA hxP
        rcases Finset.mem_biUnion.mp hxA with ⟨m, hm, hxm⟩
        have hmlt := (Finset.mem_filter.mp hm).2
        dsimp only [Pset] at hxP
        split_ifs at hxP with hq'
        · have hxq := hPsub hq' hxP
          have hne : m ≠ ⟨q, hq'⟩ := fun h => by have := congrArg Fin.val h; dsimp at this; omega
          exact Finset.disjoint_left.mp (hdisj_blocks m ⟨q, hq'⟩ hne) hxm hxq
        · exact absurd hxP (Finset.notMem_empty _)
      have hdisjA : Set.PairwiseDisjoint (↑(Finset.univ.filter (fun m : Fin M => m.val < q))) blockSet := by
        intro m1 _ m2 _ hne; exact hdisj_blocks m1 m2 hne
      have hAP_zero : ∀ y ∈ Pset, (∑ x ∈ Aset, K x y) = 0 := by
        intro y hyP
        rw [Finset.sum_biUnion hdisjA]
        apply Finset.sum_eq_zero; intro m hm
        have hmlt := (Finset.mem_filter.mp hm).2
        dsimp only [Pset] at hyP
        split_ifs at hyP with hq'
        · have hyq := hPsub hq' hyP
          have hne : m ≠ ⟨q, hq'⟩ := fun h => by have := congrArg Fin.val h; dsimp at this; omega
          exact hinter_act_zero m ⟨q, hq'⟩ hne y hyq
        · exact absurd hyP (Finset.notMem_empty _)
      have hcross1 : (∑ x ∈ Aset, ∑ y ∈ Pset, K x y) = 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_eq_zero; intro y hyP
        exact hAP_zero y hyP
      have hcross2 : (∑ x ∈ Pset, ∑ y ∈ Aset, K x y) = 0 := by
        apply Finset.sum_eq_zero; intro x hxP
        rw [Finset.sum_congr rfl (fun y _ => hK_sym x y)]
        exact hAP_zero x hxP
      have hAA : (∑ x ∈ Aset, ∑ y ∈ Aset, K x y) =
          ∑ m ∈ Finset.univ.filter (fun m : Fin M => m.val < q),
            ∑ x ∈ blockSet m, ∑ y ∈ blockSet m, K x y := by
        dsimp only [Aset]
        rw [Finset.sum_biUnion hdisjA]
        apply Finset.sum_congr rfl; intro m hm
        have h1 : (∑ x ∈ blockSet m, ∑ y ∈ (Finset.univ.filter (fun m : Fin M => m.val < q)).biUnion blockSet, K x y) =
            ∑ m' ∈ Finset.univ.filter (fun m : Fin M => m.val < q), ∑ x ∈ blockSet m, ∑ y ∈ blockSet m', K x y := by
          conv_lhs => arg 2; ext x; rw [Finset.sum_biUnion hdisjA]
          rw [Finset.sum_comm]
        rw [h1, Finset.sum_eq_single m]
        · intro m' hm' hne
          rw [Finset.sum_comm]
          apply Finset.sum_eq_zero; intro y hy
          exact hinter_act_zero m m' (Ne.symm hne) y hy
        · intro hnot; exact absurd hm hnot
      have hS_eq : S = Aset ∪ Pset := hS
      rw [hS_eq, Finset.sum_union hdisjAP]
      have hsplit_inner : ∀ Z : Finset (Fin N),
          (∑ x ∈ Z, ∑ y ∈ Aset ∪ Pset, K x y) =
            (∑ x ∈ Z, ∑ y ∈ Aset, K x y) + (∑ x ∈ Z, ∑ y ∈ Pset, K x y) := by
        intro Z; rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro x _; exact Finset.sum_union hdisjAP
      rw [hsplit_inner Aset, hsplit_inner Pset, hcross1, hcross2, add_zero, zero_add, hAA]
      congr 1
      dsimp only [Pset]
      split_ifs <;> simp
    by_cases hact : h ≤ M * L
    · have htake_h : fullList.take h = fullActList.take h :=
        List.take_append_of_le_length (by omega)
      let q := h / L
      let s := h % L
      have hqs : q * L + s = h := by rw [Nat.mul_comm]; exact Nat.div_add_mod h L
      have hq_le : q ≤ M := by
        rw [Nat.div_le_iff_le_mul_add_pred hL_pos, Nat.mul_comm L M]
        omega
      have hs_le : s ≤ L := le_of_lt (Nat.mod_lt h hL_pos)
      have hlt : q < M ∨ s = 0 := by
        by_cases hqm : q < M
        · left; exact hqm
        · right
          have : q = M := by omega
          rw [this] at hqs; omega
      have hsum_h := hact_sum_split q hq_le s hs_le hlt
      rw [hqs, ← htake_h, ← hH_eq] at hsum_h
      have h4S : (q : ℤ) * (L : ℤ) ^ 2 + (s : ℤ) ^ 2 ≤ 4 * ∑ x ∈ H, ∑ y ∈ H, K x y := by
        rw [hsum_h, mul_add]
        have h1 : (q : ℤ) * (L : ℤ) ^ 2 ≤
            4 * ∑ m ∈ Finset.univ.filter (fun m : Fin M => m.val < q),
              ∑ x ∈ blockSet m, ∑ y ∈ blockSet m, K x y := by
          have hcard_q : (Finset.univ.filter (fun m : Fin M => m.val < q)).card = q := by
            have hbij : (Finset.univ.filter (fun m : Fin M => m.val < q)).card = (Finset.range q).card := by
              refine Finset.card_bij (fun m _ => m.val) ?_ ?_ ?_
              · intro m hm; exact Finset.mem_range.mpr (Finset.mem_filter.mp hm).2
              · intro m1 _ m2 _ heq; exact Fin.ext heq
              · intro n hn
                have hnq := Finset.mem_range.mp hn
                exact ⟨⟨n, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnq⟩, rfl⟩
            rw [hbij, Finset.card_range]
          rw [Finset.mul_sum]
          calc (q : ℤ) * (L : ℤ) ^ 2
              = ∑ _m ∈ Finset.univ.filter (fun m : Fin M => m.val < q), (L : ℤ) ^ 2 := by
                simp [hcard_q]
            _ ≤ ∑ m ∈ Finset.univ.filter (fun m : Fin M => m.val < q),
                  4 * ∑ x ∈ blockSet m, ∑ y ∈ blockSet m, K x y :=
                Finset.sum_le_sum (fun m _ => by
                  have := hblock_sum_ge m; rw [hblock_card m] at this; exact this)
        have h2 : (s : ℤ) ^ 2 ≤ 4 * (if hq' : q < M then
              ∑ x ∈ ((blockList ⟨q, hq'⟩).take s).toFinset,
                ∑ y ∈ ((blockList ⟨q, hq'⟩).take s).toFinset, K x y
            else 0) := by
          split_ifs with hq'
          · exact hblockList_pref ⟨q, hq'⟩ s hs_le
          · have hs0 : s = 0 := hlt.resolve_left hq'
            rw [hs0]; simp
        omega
      by_cases hq0 : q = 0
      · have hs_eq : s = h := by rw [hq0] at hqs; omega
        have hle1 : (h : ℤ) ^ 2 ≤ 4 * ∑ x ∈ H, ∑ y ∈ H, K x y := by
          rw [hq0, hs_eq] at h4S; simpa using h4S
        have hmin : (min (h ^ 2) (a * B * h) : ℤ) ≤ (h : ℤ) ^ 2 := by
          exact_mod_cast min_le_left (h ^ 2) (a * B * h)
        nlinarith
      · have hq1 : 1 ≤ q := Nat.pos_of_ne_zero hq0
        have hquad : (L : ℤ) * (h : ℤ) ≤ 2 * ((q : ℤ) * (L : ℤ) ^ 2 + (s : ℤ) ^ 2) := by
          have hh_eq : (h : ℤ) = (q : ℤ) * (L : ℤ) + (s : ℤ) := by exact_mod_cast hqs.symm
          rw [hh_eq]
          have hq1z : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq1
          nlinarith [sq_nonneg (2 * (L : ℤ) - (s : ℤ)), sq_nonneg ((s : ℤ))]
        have hab : (a : ℤ) * (B : ℤ) * (h : ℤ) ≤ 4 * (L : ℤ) * (h : ℤ) := by
          have ha4 : (a : ℤ) ≤ 4 * (b : ℤ) := by omega
          have hLz : (L : ℤ) = (b : ℤ) * (B : ℤ) := by exact_mod_cast hL_eq
          rw [hLz]
          have h1 : (a : ℤ) * (B : ℤ) ≤ 4 * (b : ℤ) * (B : ℤ) :=
            mul_le_mul_of_nonneg_right ha4 (by positivity)
          have h2 : (a : ℤ) * (B : ℤ) * (h : ℤ) ≤ (4 * (b : ℤ) * (B : ℤ)) * (h : ℤ) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
          linarith
        have hmin : (min (h ^ 2) (a * B * h) : ℤ) ≤ (a : ℤ) * (B : ℤ) * (h : ℤ) := by
          exact_mod_cast min_le_right (h ^ 2) (a * B * h)
        linarith
    · have hML_le : M * L ≤ h := by omega
      have hact_full : (fullActList.take (M * L)).toFinset = ActSet := by
        rw [List.take_of_length_le (by omega)]
        ext x
        simp only [List.mem_toFinset, fullActList, List.mem_flatMap, List.mem_finRange, true_and, hAct_iff]
        constructor
        · rintro ⟨m, hxm⟩
          exact ⟨m, hblockList_to m ▸ List.mem_toFinset.mpr hxm⟩
        · rintro ⟨m, hxm⟩
          exact ⟨m, List.mem_toFinset.mp (hblockList_to m ▸ hxm)⟩
      have hAct_sum : (M : ℤ) * (L : ℤ) ^ 2 ≤ 4 * ∑ x ∈ ActSet, ∑ y ∈ ActSet, K x y := by
        have hsum_M := hact_sum_split M le_rfl 0 (Nat.zero_le L) (Or.inr rfl)
        simp only [Nat.add_zero, lt_self_iff_false, dite_false, add_zero, hact_full] at hsum_M
        rw [hsum_M, Finset.mul_sum]
        have hfilt_univ : Finset.univ.filter (fun m : Fin M => m.val < M) = Finset.univ := by
          ext m; simp [m.isLt]
        rw [hfilt_univ]
        calc (M : ℤ) * (L : ℤ) ^ 2 = ∑ _m : Fin M, (L : ℤ) ^ 2 := by simp
          _ ≤ ∑ m : Fin M, 4 * ∑ x ∈ blockSet m, ∑ y ∈ blockSet m, K x y :=
              Finset.sum_le_sum (fun m _ => by
                have := hblock_sum_ge m; rw [hblock_card m] at this; exact this)
      have hmono : (∑ x ∈ ActSet, ∑ y ∈ ActSet, K x y) ≤ ∑ x ∈ H, ∑ y ∈ H, K x y := by
        have htake_full : fullList.take h = fullActList ++ fullInactList.take (h - M * L) := by
          dsimp only [fullList]
          rw [List.take_append, hfullAct_len, List.take_of_length_le (by omega)]
        have hprior_mono : ∀ u (hu : u ≤ r / 2),
            let priorU := ActSet ∪ (Finset.univ.filter (fun s : Fin (r / 2) => s.val < u)).biUnion inactSet
            (∑ x ∈ ActSet, ∑ y ∈ ActSet, K x y) ≤ ∑ x ∈ priorU, ∑ y ∈ priorU, K x y := by
          intro u
          induction u with
          | zero =>
            intro _
            have hempty : Finset.univ.filter (fun s : Fin (r / 2) => s.val < 0) = ∅ := by ext s; simp
            simp [hempty]
          | succ m ih =>
            intro hm
            have hprev := ih (by omega)
            have hstep := hstep_inact m (inactSet ⟨m, by omega⟩) (by omega) le_rfl
            have hunion : (ActSet ∪ (Finset.univ.filter (fun s : Fin (r / 2) => s.val < m)).biUnion inactSet) ∪
                inactSet ⟨m, by omega⟩ =
                ActSet ∪ (Finset.univ.filter (fun s : Fin (r / 2) => s.val < m + 1)).biUnion inactSet := by
              ext y
              simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · rintro ((hA | ⟨s, hlt, hys⟩) | hym)
                · exact Or.inl hA
                · exact Or.inr ⟨s, by omega, hys⟩
                · exact Or.inr ⟨⟨m, by omega⟩, by dsimp; omega, hym⟩
              · rintro (hA | ⟨s, hlt, hys⟩)
                · exact Or.inl (Or.inl hA)
                · by_cases heq : s.val = m
                  · have hs_eq : s = ⟨m, by omega⟩ := Fin.ext heq
                    rw [hs_eq] at hys; exact Or.inr hys
                  · exact Or.inl (Or.inr ⟨s, by omega, hys⟩)
            dsimp only at hstep
            rw [hunion] at hstep
            exact le_trans hprev hstep
        let rem := h - M * L
        let u := rem / B
        let s := rem % B
        have hus : u * B + s = rem := by rw [Nat.mul_comm]; exact Nat.div_add_mod rem B
        have hfullInact_len : fullInactList.length = (r / 2) * B := by
          dsimp only [fullInactList]; rw [List.length_flatMap]
          have hm : (List.finRange (r / 2)).map (fun q => (inactList q).length) = List.replicate (r / 2) B := by
            apply List.ext_getElem
            · simp
            · intro i hi1 hi2; simp [hinact_len]
          rw [hm, List.sum_replicate, smul_eq_mul]
        have hrem_le : rem ≤ (r / 2) * B := by
          have : M * L + (r / 2) * B = N := by
            calc M * L + (r / 2) * B = M * b * B + (r / 2) * B := by rw [hL_eq]; ring
              _ = (r / 2) * B + (r / 2) * B := by rw [hMb_eq]
              _ = 2 * ((r / 2) * B) := by ring
              _ = (2 * (M * b)) * B := by rw [hMb_eq]; ring
              _ = r * B := by rw [h2Mb_eq]
              _ = N := hrB_eq
          omega
        have hu_le : u ≤ r / 2 := by
          rw [Nat.div_le_iff_le_mul_add_pred hB_pos, Nat.mul_comm B]; omega
        have hs_le : s ≤ B := le_of_lt (Nat.mod_lt rem hB_pos)
        by_cases hu_lt : u < r / 2
        · have hsplit_u : List.finRange (r / 2) =
              (List.finRange (r / 2)).take u ++ [⟨u, hu_lt⟩] ++ (List.finRange (r / 2)).drop (u + 1) := by
            have h1 : (List.finRange (r / 2)).drop u = ⟨u, hu_lt⟩ :: (List.finRange (r / 2)).drop (u + 1) := by
              rw [List.drop_eq_getElem_cons (by simp [hu_lt])]; simp
            conv_lhs => rw [← List.take_append_drop u (List.finRange (r / 2)), h1]
            simp [List.append_assoc]
          have hlen_u : (((List.finRange (r / 2)).take u).flatMap inactList).length = u * B := by
            rw [List.length_flatMap]
            have hm : (((List.finRange (r / 2)).take u).map (fun q => (inactList q).length)) = List.replicate u B := by
              apply List.ext_getElem
              · simp [hu_le]
              · intro i hi1 hi2; simp [hinact_len]
            rw [hm, List.sum_replicate, smul_eq_mul]
          have htake_inact : fullInactList.take rem =
              ((List.finRange (r / 2)).take u).flatMap inactList ++ (inactList ⟨u, hu_lt⟩).take s := by
            dsimp only [fullInactList]
            conv_lhs => rw [← hus, hsplit_u, List.flatMap_append, List.flatMap_append, List.flatMap_singleton]
            rw [List.append_assoc, List.take_append, hlen_u, List.take_of_length_le (by omega),
              Nat.add_sub_cancel_left, List.take_append_of_le_length (by rw [hinact_len]; exact hs_le)]
          have hH_decomp : H = (ActSet ∪ (Finset.univ.filter (fun q : Fin (r / 2) => q.val < u)).biUnion inactSet) ∪
              ((inactList ⟨u, hu_lt⟩).take s).toFinset := by
            rw [hH_eq, htake_full, htake_inact, List.toFinset_append, List.toFinset_append,
              ← Finset.union_assoc]
            congr 1
            have hAct_to : fullActList.toFinset = ActSet := by
              have := hact_full; rw [List.take_of_length_le (by omega)] at this; exact this
            rw [hAct_to]
            congr 1
            ext y
            simp only [List.mem_toFinset, List.mem_flatMap, Finset.mem_biUnion, Finset.mem_filter,
              Finset.mem_univ, true_and]
            constructor
            · rintro ⟨q, hq, hyq⟩
              have hqlt : q.val < u := by
                rw [List.mem_iff_getElem] at hq
                rcases hq with ⟨i, hi, rfl⟩
                rw [List.length_take, List.length_finRange] at hi
                simp only [List.getElem_take, List.getElem_finRange, Fin.val_cast]
                omega
              exact ⟨q, hqlt, hinactList_to q ▸ List.mem_toFinset.mpr hyq⟩
            · rintro ⟨q, hqlt, hyq⟩
              refine ⟨q, ?_, List.mem_toFinset.mp (hinactList_to q ▸ hyq)⟩
              rw [List.mem_iff_getElem]
              refine ⟨q.val, by rw [List.length_take, List.length_finRange]; omega, ?_⟩
              simp
          have hPsub : ((inactList ⟨u, hu_lt⟩).take s).toFinset ⊆ inactSet ⟨u, hu_lt⟩ := by
            intro x hx
            rw [← hinactList_to ⟨u, hu_lt⟩, List.mem_toFinset]
            exact List.mem_of_mem_take (List.mem_toFinset.mp hx)
          rw [hH_decomp]
          exact le_trans (hprior_mono u hu_le) (hstep_inact u _ hu_lt hPsub)
        · have hu_eq : u = r / 2 := by omega
          have hs0 : s = 0 := by rw [hu_eq] at hus; omega
          have hrem_eq : rem = (r / 2) * B := by rw [← hus, hu_eq, hs0]; omega
          have hH_full : H = ActSet ∪ (Finset.univ.filter (fun q : Fin (r / 2) => q.val < r / 2)).biUnion inactSet := by
            rw [hH_eq, htake_full]
            have hrem_full : fullInactList.take (h - M * L) = fullInactList :=
              List.take_of_length_le (by rw [hfullInact_len]; dsimp only [rem] at hrem_eq; omega)
            rw [hrem_full, List.toFinset_append]
            have hAct_to : fullActList.toFinset = ActSet := by
              have := hact_full; rw [List.take_of_length_le (by omega)] at this; exact this
            rw [hAct_to]
            congr 1
            ext y
            simp only [List.mem_toFinset, fullInactList, List.mem_flatMap, List.mem_finRange, true_and,
              Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ]
            constructor
            · rintro ⟨q, hyq⟩
              exact ⟨q, q.isLt, hinactList_to q ▸ List.mem_toFinset.mpr hyq⟩
            · rintro ⟨q, _, hyq⟩
              exact ⟨q, List.mem_toFinset.mp (hinactList_to q ▸ hyq)⟩
          rw [hH_full]
          exact hprior_mono (r / 2) le_rfl
      have h4S : (M : ℤ) * (L : ℤ) ^ 2 ≤ 4 * ∑ x ∈ H, ∑ y ∈ H, K x y :=
        le_trans hAct_sum (by omega)
      have hmin : (min (h ^ 2) (a * B * h) : ℤ) ≤ (a : ℤ) * (B : ℤ) * (h : ℤ) := by
        exact_mod_cast min_le_right (h ^ 2) (a * B * h)
      have ha4 : (a : ℤ) ≤ 4 * (b : ℤ) := by omega
      have hN_eq : (2 : ℤ) * (M : ℤ) * (L : ℤ) = (N : ℤ) := by exact_mod_cast (by rw [← h2ML_eq]; ring : 2 * M * L = N)
      have hLz : (L : ℤ) = (b : ℤ) * (B : ℤ) := by exact_mod_cast hL_eq
      have hhh : (h : ℤ) ≤ (N : ℤ) := by exact_mod_cast hh
      have h8ML : (a : ℤ) * (B : ℤ) * (h : ℤ) ≤ 8 * ((M : ℤ) * (L : ℤ) ^ 2) := by
        calc (a : ℤ) * (B : ℤ) * (h : ℤ)
            ≤ (a : ℤ) * (B : ℤ) * (N : ℤ) := mul_le_mul_of_nonneg_left hhh (by positivity)
          _ = (a : ℤ) * (B : ℤ) * (2 * (M : ℤ) * (L : ℤ)) := by rw [← hN_eq]
          _ ≤ (4 * (b : ℤ)) * (B : ℤ) * (2 * (M : ℤ) * (L : ℤ)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha4 (by positivity)) (by positivity)
          _ = 8 * ((M : ℤ) * ((b : ℤ) * (B : ℤ)) * (L : ℤ)) := by ring
          _ = 8 * ((M : ℤ) * (L : ℤ) ^ 2) := by rw [← hLz]; ring
      linarith
  have hcost_eq : (4 * (Finset.univ.filter (fun z : Fin N × Fin N =>
      D ({z.1, z.2} : Finset (Fin N))
        (Finset.univ.filter (fun i : Fin N => h ≤ (order i).val) ∩ {z.1}) ≠
        xor (z.1.val.testBit ((π z.2).val % r)) (flip z.1))).card : ℤ) =
      (h : ℤ) ^ 2 - ∑ x ∈ H, ∑ y ∈ H, K x y := hD_cost
  have hfinal_z : (128 : ℤ) * ((Finset.univ.filter (fun z : Fin N × Fin N =>
      D ({z.1, z.2} : Finset (Fin N))
        (Finset.univ.filter (fun i : Fin N => h ≤ (order i).val) ∩ {z.1}) ≠
        xor (z.1.val.testBit ((π z.2).val % r)) (flip z.1))).card : ℤ) +
      (min (h ^ 2) (a * B * h) : ℤ) ≤ 32 * (h : ℤ) ^ 2 := by
    linarith
  exact_mod_cast hfinal_z

end PEqualNP.Outside.L_meta_25743_aux

theorem PEqualNP.Outside.L_meta_25743 :
    ∀ (k a : ℕ), 2 ≤ a → 2^a ≤ k →
      let N := 2^k
      let r := 2^a
      let B := N/r
      ∃ (π order : Equiv.Perm (Fin N)) (flip : Fin N → Bool),
        let exposed := fun h : ℕ => Finset.univ.filter (fun i : Fin N => h ≤ (order i).val)
        let cost := fun (h : ℕ) (out : Finset (Fin N) → Finset (Fin N) → Bool) =>
          (Finset.univ.filter (fun z : Fin N × Fin N =>
            out ({z.1,z.2} : Finset (Fin N)) (exposed h ∩ {z.1}) ≠
              xor (z.1.val.testBit ((π z.2).val % r)) (flip z.1))).card
        ∃ D : Finset (Fin N) → Finset (Fin N) → Bool, ∀ h : ℕ, h ≤ N →
          (∀ other, cost h D ≤ cost h other) ∧
            128*cost h D + min (h^2) (a*B*h) ≤ 32*h^2 := by
  classical
  intro k a ha hak N r B
  let t : ℕ := Nat.log 2 a - 1
  have hlog_ge : 1 ≤ Nat.log 2 a := by
    have h1 : Nat.log 2 2 ≤ Nat.log 2 a := Nat.log_mono_right ha
    have h2 : Nat.log 2 2 = 1 := by decide
    omega
  let b : ℕ := 2 ^ t
  have hb_pos : 1 ≤ b := Nat.one_le_pow t 2 (by norm_num)
  have h2b_le : 2 * b ≤ a := by
    have hpow : 2 ^ Nat.log 2 a ≤ a := Nat.pow_log_le_self 2 (by omega)
    have h1 : 2 * b = 2 ^ Nat.log 2 a := by
      dsimp only [b, t]
      conv_rhs => rw [show Nat.log 2 a = (Nat.log 2 a - 1) + 1 by omega, pow_succ, Nat.mul_comm]
    omega
  have ha_lt_4b : a < 4 * b := by
    have hpow : a < 2 ^ (Nat.log 2 a + 1) := Nat.lt_pow_succ_log_self (by norm_num) a
    have h1 : 4 * b = 2 ^ (Nat.log 2 a + 1) := by
      dsimp only [b, t]
      conv_rhs => rw [show Nat.log 2 a + 1 = (Nat.log 2 a - 1) + 2 by omega, pow_add]
      ring
    omega
  have ha_le_r2 : a ≤ 2 ^ (a - 1) := PEqualNP.Outside.L_meta_25743_aux.nat_le_two_pow_pred a ha
  have hr2_eq : r / 2 = 2 ^ (a - 1) := by
    dsimp only [r]
    conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
    exact Nat.mul_div_cancel _ (by norm_num)
  have ht_lt : t + 1 ≤ a - 1 := by
    have htb : t < b := Nat.lt_two_pow_self
    omega
  let d : ℕ := a - 1 - t
  have hd_add_t : d + t = a - 1 := by omega
  let M : ℕ := 2 ^ d
  have hM_pos : 0 < M := by positivity
  have hMb_eq : M * b = r / 2 := by
    dsimp only [M, b]
    rw [← pow_add, hd_add_t, hr2_eq]
  have h2Mb_eq : 2 * (M * b) = r := by
    rw [hMb_eq, hr2_eq]
    dsimp only [r]
    conv_rhs => rw [show a = (a - 1) + 1 by omega, pow_succ, Nat.mul_comm]
  have ha_le_k : a ≤ k := le_trans (by omega : a ≤ 2 ^ a) hak
  have hB_eq : B = 2 ^ (k - a) := by
    dsimp only [B, N, r]
    rw [← Nat.pow_sub_mul_pow 2 ha_le_k, Nat.mul_div_cancel _ (by positivity)]
  have hrB_eq : r * B = N := by
    rw [hB_eq]; dsimp only [r, N]; rw [Nat.mul_comm, Nat.pow_sub_mul_pow 2 ha_le_k]
  let L : ℕ := b * B
  have h2ML_eq : 2 * (M * L) = N := by
    calc 2 * (M * L) = (2 * (M * b)) * B := by dsimp only [L]; ring
      _ = r * B := by rw [h2Mb_eq]
      _ = N := hrB_eq
  have hMb_lt : M * b < k := by
    have : r / 2 < r := by rw [hr2_eq]; dsimp only [r]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hu_bound : M * b + 1 + d ≤ k := by omega
  have hv_bound : M * b + 1 + d + t ≤ k := by omega
  have hwinact_bound : M * b + 1 + (a - 1) ≤ k := by omega
  let eBits := PEqualNP.Outside.L_meta_25743_aux.fin_bit_equiv k
  let isConst : (Fin k → Bool) → Fin M → Bool := fun f m =>
    decide ((∀ j : Fin b, f ⟨m.val * b + j.val,
      lt_trans (PEqualNP.Outside.L_meta_25743_aux.mul_add_lt_mul m.isLt j.isLt) hMb_lt⟩ = false) ∨
      (∀ j : Fin b, f ⟨m.val * b + j.val,
      lt_trans (PEqualNP.Outside.L_meta_25743_aux.mul_add_lt_mul m.isLt j.isLt) hMb_lt⟩ = true))
  let uOf : (Fin k → Bool) → Fin M := fun f =>
    PEqualNP.Outside.L_meta_25743_aux.bitsNat f (M * b + 1) d hu_bound
  let vOf : (Fin k → Bool) → Fin b := fun f =>
    PEqualNP.Outside.L_meta_25743_aux.bitsNat f (M * b + 1 + d) t hv_bound
  let wInact : (Fin k → Bool) → Fin (r / 2) := fun f =>
    ⟨(PEqualNP.Outside.L_meta_25743_aux.bitsNat f (M * b + 1) (a - 1) hwinact_bound).val,
      lt_of_lt_of_eq (PEqualNP.Outside.L_meta_25743_aux.bitsNat f (M * b + 1) (a - 1) hwinact_bound).isLt
        hr2_eq.symm⟩
  let ownerF : (Fin k → Bool) → Fin M := fun f =>
    PEqualNP.Outside.L_meta_25743_aux.firstConstFrom hM_pos (isConst f) (uOf f)
  let gF : (Fin k → Bool) → Fin r := fun f =>
    if f ⟨M * b, hMb_lt⟩ = false then
      ⟨(ownerF f).val * b + (vOf f).val,
        lt_of_lt_of_le (PEqualNP.Outside.L_meta_25743_aux.mul_add_lt_mul (ownerF f).isLt (vOf f).isLt)
          (by omega)⟩
    else
      ⟨r / 2 + (wInact f).val, by have := (wInact f).isLt; omega⟩
  let g : Fin N → Fin r := fun x => gF (eBits x)
  have hAct_card : (Finset.univ.filter (fun f : Fin k → Bool => f ⟨M * b, hMb_lt⟩ = false)).card =
      M * L := by
    let eA : {f : Fin k → Bool // f ⟨M * b, hMb_lt⟩ = false} ≃
        ({i : Fin k // i ≠ ⟨M * b, hMb_lt⟩} → Bool) :=
      { toFun := fun f i => f.1 i.1
        invFun := fun h => ⟨fun i => if hi : i = ⟨M * b, hMb_lt⟩ then false else h ⟨i, hi⟩, by simp⟩
        left_inv := fun f => by
          ext i; by_cases hi : i = ⟨M * b, hMb_lt⟩
          · subst hi; simp [f.2]
          · simp [hi]
        right_inv := fun h => by ext i; simp [i.2] }
    have hc : (Finset.univ.filter (fun f : Fin k → Bool => f ⟨M * b, hMb_lt⟩ = false)).card =
        2 ^ (k - 1) := by
      rw [← Fintype.card_subtype, Fintype.card_congr eA, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
    rw [hc]
    have h2N : 2 * 2 ^ (k - 1) = N := by
      dsimp only [N]; conv_rhs => rw [show k = (k - 1) + 1 by omega, pow_succ, Nat.mul_comm]
    omega
  have hrot_fib : ∀ m : Fin M,
      (Finset.univ.filter (fun f : Fin k → Bool =>
        f ⟨M * b, hMb_lt⟩ = false ∧ ownerF f = m)).card = L :=
    PEqualNP.Outside.L_meta_25743_aux.rot_fib_helper k d t L hM_pos hb_pos hMb_lt hu_bound hAct_card
  have hfib_g : ∀ j : Fin r, (Finset.univ.filter (fun x : Fin N => g x = j)).card = B := by
    intro j
    have hbij_e : (Finset.univ.filter (fun x : Fin N => g x = j)).card =
        (Finset.univ.filter (fun f : Fin k → Bool => gF f = j)).card := by
      refine Finset.card_bij (fun x _ => eBits x) ?_ ?_ ?_
      · intro x hx; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
      · intro x1 _ x2 _ heq; exact eBits.injective heq
      · intro f hf
        exact ⟨eBits.symm f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          dsimp only [g]; rw [eBits.apply_symm_apply]; exact (Finset.mem_filter.mp hf).2⟩,
          eBits.apply_symm_apply f⟩
    rw [hbij_e]
    by_cases hj : j.val < r / 2
    · let m : Fin M := ⟨j.val / b, by rw [Nat.div_lt_iff_lt_mul hb_pos, hMb_eq]; exact hj⟩
      let q : Fin b := ⟨j.val % b, Nat.mod_lt _ hb_pos⟩
      have hfilt : Finset.univ.filter (fun f : Fin k → Bool => gF f = j) =
          Finset.univ.filter (fun f : Fin k → Bool =>
            f ⟨M * b, hMb_lt⟩ = false ∧ ownerF f = m ∧ vOf f = q) := by
        ext f
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, gF]
        by_cases hf0 : f ⟨M * b, hMb_lt⟩ = false
        · rw [if_pos hf0]
          simp only [hf0, true_and, Fin.ext_iff]
          constructor
          · intro hEq
            have h1 : (ownerF f).val = j.val / b := by
              rw [← hEq, Nat.mul_comm _ b, Nat.mul_add_div hb_pos, Nat.div_eq_of_lt (vOf f).isLt, Nat.add_zero]
            have h2 : (vOf f).val = j.val % b := by
              rw [← hEq, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (vOf f).isLt]
            exact ⟨h1, h2⟩
          · rintro ⟨hm, hq⟩
            rw [hm, hq]; dsimp only [m, q]
            rw [Nat.mul_comm, Nat.div_add_mod]
        · rw [if_neg hf0]
          simp only [Bool.eq_true_of_not_eq_false hf0, Bool.true_eq_false, false_and, iff_false]
          intro hEq
          have hval : r / 2 + (wInact f).val = j.val := congrArg Fin.val hEq
          omega
      rw [hfilt]
      exact PEqualNP.Outside.L_meta_25743_aux.v_split_helper k d t B hM_pos hb_pos hMb_lt hu_bound hv_bound m
        (hrot_fib m) q
    · let q : Fin (2 ^ (a - 1)) := ⟨j.val - r / 2, by rw [← hr2_eq]; have := j.isLt; omega⟩
      have hfilt : Finset.univ.filter (fun f : Fin k → Bool => gF f = j) =
          Finset.univ.filter (fun f : Fin k → Bool =>
            f ⟨M * b, hMb_lt⟩ = true ∧
              PEqualNP.Outside.L_meta_25743_aux.bitsNat f (M * b + 1) (a - 1) hwinact_bound = q) := by
        ext f
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, gF]
        by_cases hf0 : f ⟨M * b, hMb_lt⟩ = false
        · rw [if_pos hf0]
          simp only [hf0, Bool.false_eq_true, false_and, iff_false]
          intro hEq
          have hval : (ownerF f).val * b + (vOf f).val = j.val := congrArg Fin.val hEq
          have h1 := PEqualNP.Outside.L_meta_25743_aux.mul_add_lt_mul (ownerF f).isLt (vOf f).isLt
          omega
        · have hft : f ⟨M * b, hMb_lt⟩ = true := Bool.eq_true_of_not_eq_false hf0
          rw [if_neg hf0]
          simp only [hft, true_and, Fin.ext_iff]
          dsimp only [wInact, q]; omega
      rw [hfilt, hB_eq]
      exact PEqualNP.Outside.L_meta_25743_aux.inact_fib_helper k a (M * b) (by omega) hwinact_bound q
  obtain ⟨π, hπ⟩ := PEqualNP.Outside.L_meta_25743_aux.perm_of_equal_fibers g
    (fun z : Fin N => ⟨z.val % r, Nat.mod_lt _ (by positivity)⟩)
    (fun j => by
      rw [hfib_g j]
      have hc := PEqualNP.Outside.L_meta_25743_aux.card_mod_fiber k a ha_le_k j
      have hfilt : Finset.univ.filter (fun z : Fin N =>
          (⟨z.val % r, Nat.mod_lt _ (by positivity)⟩ : Fin r) = j) =
          Finset.univ.filter (fun z : Fin N => z.val % r = j.val) := by
        ext z; simp [Fin.ext_iff]
      rw [hfilt, hc])
  have hπ_mod : ∀ x : Fin N, (π x).val % r = (g x).val := fun x => congrArg Fin.val (hπ x)
  let blockSet : Fin M → Finset (Fin N) := fun m =>
    Finset.univ.filter (fun x : Fin N => eBits x ⟨M * b, hMb_lt⟩ = false ∧ ownerF (eBits x) = m)
  let inactSet : Fin (r / 2) → Finset (Fin N) := fun s =>
    Finset.univ.filter (fun x : Fin N => eBits x ⟨M * b, hMb_lt⟩ = true ∧ wInact (eBits x) = s)
  have hblock_card : ∀ m : Fin M, (blockSet m).card = L := by
    intro m
    have hbij : (blockSet m).card = (Finset.univ.filter (fun f : Fin k → Bool =>
        f ⟨M * b, hMb_lt⟩ = false ∧ ownerF f = m)).card := by
      refine Finset.card_bij (fun x _ => eBits x) ?_ ?_ ?_
      · intro x hx; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
      · intro x1 _ x2 _ heq; exact eBits.injective heq
      · intro f hf
        exact ⟨eBits.symm f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          rw [eBits.apply_symm_apply]; exact (Finset.mem_filter.mp hf).2⟩, eBits.apply_symm_apply f⟩
    rw [hbij, hrot_fib m]
  have hinact_card : ∀ s : Fin (r / 2), (inactSet s).card = B := by
    intro s
    have hge_j : r / 2 + s.val < r := by have := s.isLt; omega
    have heq_g : inactSet s = Finset.univ.filter (fun x : Fin N => g x = ⟨r / 2 + s.val, hge_j⟩) := by
      ext x
      simp only [inactSet, Finset.mem_filter, Finset.mem_univ, true_and, g, gF]
      by_cases hx0 : eBits x ⟨M * b, hMb_lt⟩ = false
      · rw [if_pos hx0]
        simp only [hx0, Bool.false_eq_true, false_and, false_iff]
        intro hEq
        have hval : (ownerF (eBits x)).val * b + (vOf (eBits x)).val = r / 2 + s.val := congrArg Fin.val hEq
        have h1 := PEqualNP.Outside.L_meta_25743_aux.mul_add_lt_mul (ownerF (eBits x)).isLt (vOf (eBits x)).isLt
        omega
      · have hxt : eBits x ⟨M * b, hMb_lt⟩ = true := Bool.eq_true_of_not_eq_false hx0
        rw [if_neg hx0]
        simp only [hxt, true_and, Fin.ext_iff]
        omega
    rw [heq_g, hfib_g]
  let flipAct : Fin N → Bool := fun x =>
    let f := eBits x
    let m := ownerF f
    decide (∀ j : Fin b, f ⟨m.val * b + j.val,
      lt_trans (PEqualNP.Outside.L_meta_25743_aux.mul_add_lt_mul m.isLt j.isLt) hMb_lt⟩ = true)
  let ActSet : Finset (Fin N) := Finset.univ.filter (fun x : Fin N => eBits x ⟨M * b, hMb_lt⟩ = false)
  let recFlip : ℕ → Fin N → Bool :=
    Nat.rec flipAct (fun s prev =>
      if hs : s < r / 2 then
        let prior : Finset (Fin N) := ActSet ∪
          Finset.univ.filter (fun y : Fin N => eBits y ⟨M * b, hMb_lt⟩ = true ∧ (wInact (eBits y)).val < s)
        let j_s : ℕ := r / 2 + s
        fun x =>
          if x ∈ inactSet ⟨s, hs⟩ then
            let score : ℤ := ∑ y ∈ prior,
              PEqualNP.Outside.L_meta_25743_aux.bSign (prev y) *
                PEqualNP.Outside.L_meta_25743_aux.bSign (y.val.testBit j_s) *
                PEqualNP.Outside.L_meta_25743_aux.bSign (x.val.testBit (g y).val)
            decide (score < 0)
          else prev x
      else prev)
  let flip : Fin N → Bool := recFlip (r / 2)
  have hflip_act : ∀ s x, x ∈ ActSet → recFlip s x = flipAct x := by
    intro s
    induction s with
    | zero => intro _ _; rfl
    | succ s ih =>
      intro x hx
      dsimp only [recFlip]
      by_cases hs : s < r / 2
      · rw [dif_pos hs]
        by_cases hxI : x ∈ inactSet ⟨s, hs⟩
        · exfalso
          have h1 := (Finset.mem_filter.mp hx).2
          have h2 := (Finset.mem_filter.mp hxI).2.1
          rw [h1] at h2; exact absurd h2 (by decide)
        · rw [if_neg hxI]; exact ih x hx
      · rw [dif_neg hs]; exact ih x hx
  have hflip_prior : ∀ s1 s2 x, s1 ≤ s2 →
      (eBits x ⟨M * b, hMb_lt⟩ = true → (wInact (eBits x)).val < s1) →
      recFlip s2 x = recFlip s1 x := by
    intro s1 s2 x hle hlt
    induction s2 with
    | zero =>
      have : s1 = 0 := by omega
      subst this; rfl
    | succ s ih =>
      by_cases heq : s1 = s + 1
      · subst heq; rfl
      · have hs1 : s1 ≤ s := by omega
        dsimp only [recFlip]
        by_cases hs : s < r / 2
        · rw [dif_pos hs]
          by_cases hxI : x ∈ inactSet ⟨s, hs⟩
          · exfalso
            have h1 := (Finset.mem_filter.mp hxI).2.1
            have h2 := (Finset.mem_filter.mp hxI).2.2
            have h3 := hlt h1
            rw [h2] at h3; dsimp at h3; omega
          · rw [if_neg hxI]; exact ih hs1
        · rw [dif_neg hs]; exact ih hs1
  have hflip_inact_step : ∀ s (hs : s < r / 2) x, x ∈ inactSet ⟨s, hs⟩ →
      let prior : Finset (Fin N) := ActSet ∪
        Finset.univ.filter (fun y : Fin N => eBits y ⟨M * b, hMb_lt⟩ = true ∧ (wInact (eBits y)).val < s)
      let score : ℤ := ∑ y ∈ prior,
        PEqualNP.Outside.L_meta_25743_aux.bSign (flip y) *
          PEqualNP.Outside.L_meta_25743_aux.bSign (y.val.testBit (r / 2 + s)) *
          PEqualNP.Outside.L_meta_25743_aux.bSign (x.val.testBit (g y).val)
      0 ≤ PEqualNP.Outside.L_meta_25743_aux.bSign (flip x) * score := by
    intro s hs x hxI prior score
    have hfx : flip x = recFlip (s + 1) x := by
      dsimp only [flip]
      apply hflip_prior (s + 1) (r / 2) x (by omega)
      intro _
      have hw := (Finset.mem_filter.mp hxI).2.2
      rw [hw]; dsimp; omega
    have hscore_eq : score = ∑ y ∈ prior,
        PEqualNP.Outside.L_meta_25743_aux.bSign (recFlip s y) *
          PEqualNP.Outside.L_meta_25743_aux.bSign (y.val.testBit (r / 2 + s)) *
          PEqualNP.Outside.L_meta_25743_aux.bSign (x.val.testBit (g y).val) := by
      apply Finset.sum_congr rfl; intro y hy
      have hfy : flip y = recFlip s y := by
        dsimp only [flip]
        apply hflip_prior s (r / 2) y (by omega)
        intro hyt
        rcases Finset.mem_union.mp hy with hyA | hyI
        · have := (Finset.mem_filter.mp hyA).2; rw [hyt] at this; exact absurd this (by decide)
        · exact (Finset.mem_filter.mp hyI).2.2
      rw [hfy]
    rw [hfx, hscore_eq]
    dsimp only [recFlip]
    rw [dif_pos hs, if_pos hxI]
    set sc := ∑ y ∈ prior,
      PEqualNP.Outside.L_meta_25743_aux.bSign (recFlip s y) *
        PEqualNP.Outside.L_meta_25743_aux.bSign (y.val.testBit (r / 2 + s)) *
        PEqualNP.Outside.L_meta_25743_aux.bSign (x.val.testBit (g y).val)
    by_cases hneg : sc < 0
    · simp only [decide_eq_true_eq.mpr hneg, PEqualNP.Outside.L_meta_25743_aux.bSign, ite_true]
      omega
    · simp only [decide_eq_false hneg, PEqualNP.Outside.L_meta_25743_aux.bSign, Bool.false_eq_true, ite_false]
      omega
  let T : Fin N → Fin N → Bool := fun x y => xor (x.val.testBit ((π y).val % r)) (flip x)
  let K : Fin N → Fin N → ℤ := fun x y =>
    PEqualNP.Outside.L_meta_25743_aux.bSign (T x y) * PEqualNP.Outside.L_meta_25743_aux.bSign (T y x)
  have hK_sym : ∀ x y, K x y = K y x := fun x y => mul_comm _ _
  have hK_fact : ∀ x y, K x y =
      (PEqualNP.Outside.L_meta_25743_aux.bSign (flip x) *
        PEqualNP.Outside.L_meta_25743_aux.bSign (x.val.testBit (g y).val)) *
      (PEqualNP.Outside.L_meta_25743_aux.bSign (flip y) *
        PEqualNP.Outside.L_meta_25743_aux.bSign (y.val.testBit (g x).val)) := by
    intro x y
    dsimp only [K, T]
    rw [hπ_mod y, hπ_mod x, PEqualNP.Outside.L_meta_25743_aux.bSign_xor,
      PEqualNP.Outside.L_meta_25743_aux.bSign_xor]
    ring
  have hact_res := PEqualNP.Outside.L_meta_25743_aux.active_blocks_helper k a d t B
    h2b_le hM_pos hb_pos hd_add_t h2Mb_eq hB_eq ha_le_k hMb_lt hu_bound hv_bound g flip K
    hrot_fib hK_fact
    (fun x hx0 => by dsimp only [g, gF]; rw [if_pos hx0])
    (fun x hx0 => hflip_act (r / 2) x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx0⟩))
  obtain ⟨hinter_act_zero, hblock_sum_ge⟩ := hact_res
  have hstep_inact : ∀ (u : ℕ) (P : Finset (Fin N)) (hu : u < r / 2), P ⊆ inactSet ⟨u, hu⟩ →
      let prior := ActSet ∪ (Finset.univ.filter (fun s : Fin (r / 2) => s.val < u)).biUnion inactSet
      (∑ x ∈ prior, ∑ y ∈ prior, K x y) ≤ ∑ x ∈ prior ∪ P, ∑ y ∈ prior ∪ P, K x y := by
    intro u P hu hP prior
    have hprior_eq : prior = ActSet ∪
        Finset.univ.filter (fun y : Fin N => eBits y ⟨M * b, hMb_lt⟩ = true ∧ (wInact (eBits y)).val < u) := by
      dsimp only [prior]; congr 1; ext y
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, inactSet]
      constructor
      · rintro ⟨s, hs, hyt, hys⟩; exact ⟨hyt, by rw [hys]; exact hs⟩
      · rintro ⟨hyt, hlt⟩; exact ⟨wInact (eBits y), hlt, hyt, rfl⟩
    rw [hprior_eq]
    set priorF := ActSet ∪
      Finset.univ.filter (fun y : Fin N => eBits y ⟨M * b, hMb_lt⟩ = true ∧ (wInact (eBits y)).val < u)
    have hdisj : Disjoint priorF P := by
      rw [Finset.disjoint_left]; intro x hxp hxP
      have hxI := hP hxP
      rcases (Finset.mem_filter.mp hxI).2 with ⟨hxt, hxw⟩
      rcases Finset.mem_union.mp hxp with hxA | hxI'
      · have := (Finset.mem_filter.mp hxA).2; rw [hxt] at this; exact absurd this (by decide)
      · have hlt := (Finset.mem_filter.mp hxI').2.2; rw [hxw] at hlt; dsimp at hlt; omega
    rw [Finset.sum_union hdisj]
    have hsplit_inner : ∀ Z : Finset (Fin N),
        (∑ x ∈ Z, ∑ y ∈ priorF ∪ P, K x y) =
          (∑ x ∈ Z, ∑ y ∈ priorF, K x y) + (∑ x ∈ Z, ∑ y ∈ P, K x y) := by
      intro Z; rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _; exact Finset.sum_union hdisj
    rw [hsplit_inner priorF, hsplit_inner P]
    have hcross_eq : (∑ x ∈ priorF, ∑ y ∈ P, K x y) = ∑ x ∈ P, ∑ y ∈ priorF, K x y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro y _; exact hK_sym y x
    have hcross_nn : 0 ≤ ∑ x ∈ P, ∑ y ∈ priorF, K x y := by
      apply Finset.sum_nonneg; intro x hxP
      have hxI := hP hxP
      have hgx : (g x).val = r / 2 + u := by
        rcases (Finset.mem_filter.mp hxI).2 with ⟨hxt, hxw⟩
        dsimp only [g, gF]
        have hne : eBits x ⟨M * b, hMb_lt⟩ ≠ false := by simp [hxt]
        rw [if_neg hne]; dsimp only; rw [hxw]
      have hrew : (∑ y ∈ priorF, K x y) =
          PEqualNP.Outside.L_meta_25743_aux.bSign (flip x) *
            ∑ y ∈ priorF, PEqualNP.Outside.L_meta_25743_aux.bSign (flip y) *
              PEqualNP.Outside.L_meta_25743_aux.bSign (y.val.testBit (r / 2 + u)) *
              PEqualNP.Outside.L_meta_25743_aux.bSign (x.val.testBit (g y).val) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro y _
        rw [hK_fact x y, hgx]; ring
      rw [hrew]
      exact hflip_inact_step u hu x hxI
    have hPP_nn : 0 ≤ ∑ x ∈ P, ∑ y ∈ P, K x y := by
      have hsq : (∑ x ∈ P, ∑ y ∈ P, K x y) =
          (∑ x ∈ P, PEqualNP.Outside.L_meta_25743_aux.bSign (flip x) *
            PEqualNP.Outside.L_meta_25743_aux.bSign (x.val.testBit (r / 2 + u))) ^ 2 := by
        rw [sq, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro x hxP
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro y hyP
        have hgx : (g x).val = r / 2 + u := by
          rcases (Finset.mem_filter.mp (hP hxP)).2 with ⟨hxt, hxw⟩
          dsimp only [g, gF]; have hne : eBits x ⟨M * b, hMb_lt⟩ ≠ false := by simp [hxt]
          rw [if_neg hne]; dsimp only; rw [hxw]
        have hgy : (g y).val = r / 2 + u := by
          rcases (Finset.mem_filter.mp (hP hyP)).2 with ⟨hxt, hxw⟩
          dsimp only [g, gF]; have hne : eBits y ⟨M * b, hMb_lt⟩ ≠ false := by simp [hxt]
          rw [if_neg hne]; dsimp only; rw [hxw]
        rw [hK_fact x y, hgx, hgy]
      rw [hsq]; exact sq_nonneg _
    omega
  have hdisj_blocks : ∀ m1 m2 : Fin M, m1 ≠ m2 → Disjoint (blockSet m1) (blockSet m2) := by
    intro m1 m2 hne; rw [Finset.disjoint_left]; intro x h1 h2
    exact hne ((Finset.mem_filter.mp h1).2.2.symm.trans (Finset.mem_filter.mp h2).2.2)
  have hdisj_inact : ∀ s1 s2 : Fin (r / 2), s1 ≠ s2 → Disjoint (inactSet s1) (inactSet s2) := by
    intro s1 s2 hne; rw [Finset.disjoint_left]; intro x h1 h2
    exact hne ((Finset.mem_filter.mp h1).2.2.symm.trans (Finset.mem_filter.mp h2).2.2)
  have hdisj_act_inact : ∀ m s, Disjoint (blockSet m) (inactSet s) := by
    intro m s; rw [Finset.disjoint_left]; intro x h1 h2
    have a1 := (Finset.mem_filter.mp h1).2.1; have a2 := (Finset.mem_filter.mp h2).2.1
    rw [a1] at a2; exact absurd a2 (by decide)
  have hAct_iff : ∀ x : Fin N, x ∈ ActSet ↔ ∃ m : Fin M, x ∈ blockSet m := by
    intro x
    simp only [ActSet, blockSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨ownerF (eBits x), h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  have hUniv_cover : ∀ x : Fin N, (∃ m : Fin M, x ∈ blockSet m) ∨ (∃ s : Fin (r / 2), x ∈ inactSet s) := by
    intro x
    by_cases hx0 : eBits x ⟨M * b, hMb_lt⟩ = false
    · exact Or.inl ⟨ownerF (eBits x), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx0, rfl⟩⟩
    · exact Or.inr ⟨wInact (eBits x), Finset.mem_filter.mpr ⟨Finset.mem_univ _, Bool.eq_true_of_not_eq_false hx0, rfl⟩⟩
  have hB_pos : 0 < B := by rw [hB_eq]; positivity
  have hL_pos : 0 < L := by dsimp only [L]; rw [hB_eq]; positivity
  obtain ⟨order, D, hres⟩ := PEqualNP.Outside.L_meta_25743_aux.order_and_bound_helper N r a M b B L
    ha_lt_4b rfl h2ML_eq hMb_eq h2Mb_eq hrB_eq hB_pos hL_pos π flip blockSet inactSet ActSet
    hblock_card hinact_card hdisj_blocks hdisj_inact hdisj_act_inact hAct_iff hUniv_cover
    hinter_act_zero hblock_sum_ge hstep_inact
  exact ⟨π, order, flip, D, hres⟩
