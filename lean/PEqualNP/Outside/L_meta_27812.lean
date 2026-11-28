import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27812_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

abbrev F2 := ZMod 2

abbrev Vec (k : ℕ) := Fin k → F2

def dot {k : ℕ} (x y : Vec k) : F2 := ∑ i : Fin k, x i * y i

lemma zmod2_eq_zero_or_one (x : F2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

lemma zmod2_add_self (x : F2) : x + x = 0 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> decide

lemma zmod2_sub_eq_add (x y : F2) : x - y = x + y := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one y with rfl | rfl <;> decide

lemma zmod2_ne_iff_add_one (x y : F2) : x ≠ y ↔ y + 1 = x := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one y with rfl | rfl <;> decide

lemma vec_add_self {k : ℕ} (x : Vec k) : x + x = 0 := by
  funext i; exact zmod2_add_self (x i)

lemma dot_add_left {k : ℕ} (x y z : Vec k) : dot (x + y) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_add_right {k : ℕ} (x y z : Vec k) : dot x (y + z) = dot x y + dot x z := by
  simp [dot, mul_add, Finset.sum_add_distrib]

lemma dot_smul_left {k : ℕ} (c : F2) (x y : Vec k) : dot (c • x) y = c * dot x y := by
  simp [dot, Finset.mul_sum, mul_assoc]

lemma dot_smul_right {k : ℕ} (c : F2) (x y : Vec k) : dot x (c • y) = c * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma dot_zero_left {k : ℕ} (y : Vec k) : dot 0 y = 0 := by
  simp [dot]

lemma dot_zero_right {k : ℕ} (x : Vec k) : dot x 0 = 0 := by
  simp [dot]

lemma dot_comm {k : ℕ} (x y : Vec k) : dot x y = dot y x := by
  simp only [dot]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma pow_succ_mul_sub_le (B : ℕ) : ∀ t : ℕ, t ≤ B → (B + 1) ^ t * (B - t) ≤ B ^ (t + 1) := by
  intro t
  induction t with
  | zero =>
    intro _
    simp
  | succ t ih =>
    intro ht
    have ht' : t ≤ B := by omega
    have hih := ih ht'
    have hstep : (B + 1) * (B - (t + 1)) ≤ (B - t) * B := by
      zify [ht, ht']
      nlinarith
    calc (B + 1) ^ (t + 1) * (B - (t + 1))
        = (B + 1) ^ t * ((B + 1) * (B - (t + 1))) := by ring
      _ ≤ (B + 1) ^ t * ((B - t) * B) := Nat.mul_le_mul_left _ hstep
      _ = ((B + 1) ^ t * (B - t)) * B := by ring
      _ ≤ B ^ (t + 1) * B := Nat.mul_le_mul_right B hih
      _ = B ^ (t + 2) := by ring

lemma nat_le_of_pow_le_pow_left {a b n : ℕ} (hn : n ≠ 0) (h : a ^ n ≤ b ^ n) : a ≤ b := by
  by_contra hlt
  have hgt : b < a := Nat.lt_of_not_le hlt
  have hpow : b ^ n < a ^ n := Nat.pow_lt_pow_left hgt hn
  omega

lemma pow_half_le_two_mul (k : ℕ) (hk : 0 < k) :
    (2 * k + 1) ^ k ≤ 2 * (2 * k) ^ k := by
  have h := pow_succ_mul_sub_le (2 * k) k (by omega)
  have hsub : 2 * k - k = k := by omega
  rw [hsub] at h
  have h2 : (2 * k + 1) ^ k * k ≤ (2 * (2 * k) ^ k) * k := by
    calc (2 * k + 1) ^ k * k
        ≤ (2 * k) ^ (k + 1) := h
      _ = (2 * (2 * k) ^ k) * k := by ring
  exact Nat.le_of_mul_le_mul_right h2 hk

def wt {m : ℕ} (y : Fin m → F2) : ℕ :=
  (Finset.univ.filter (fun j : Fin m => y j = 1)).card

lemma wt_le {m : ℕ} (y : Fin m → F2) : wt y ≤ m := by
  calc wt y ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
    _ = m := by simp

lemma wt_add_one {m : ℕ} (y : Fin m → F2) :
    wt (fun j => y j + 1) = m - wt y := by
  have hdisj : Disjoint (Finset.univ.filter (fun j : Fin m => y j = 1))
      (Finset.univ.filter (fun j : Fin m => y j + 1 = 1)) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [h1] at h2
    exact absurd h2 (by decide)
  have hunion : Finset.univ.filter (fun j : Fin m => y j = 1) ∪
      Finset.univ.filter (fun j : Fin m => y j + 1 = 1) = Finset.univ := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rcases zmod2_eq_zero_or_one (y j) with h | h
    · right; rw [h]; decide
    · left; exact h
  have hsum : wt y + wt (fun j => y j + 1) = m := by
    change (Finset.univ.filter (fun j : Fin m => y j = 1)).card +
      (Finset.univ.filter (fun j : Fin m => y j + 1 = 1)).card = m
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  omega

lemma sum_pow_wt (m A B : ℕ) :
    ∑ y : Fin m → F2, A ^ wt y * B ^ (m - wt y) = (A + B) ^ m := by
  induction m with
  | zero =>
    have huniq : (Finset.univ : Finset (Fin 0 → F2)) = {Fin.elim0} := by
      ext y
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      funext i; exact Fin.elim0 i
    rw [huniq, Finset.sum_singleton]
    simp [wt]
  | succ m ih =>
    have hwt_cons : ∀ (b : F2) (y : Fin m → F2),
        wt (Fin.cons (α := fun _ => F2) b y) = (if b = 1 then 1 else 0) + wt y := by
      intro b y
      unfold wt
      have hsplit : (Finset.univ.filter (fun j : Fin (m + 1) => Fin.cons (α := fun _ => F2) b y j = 1)).card =
          (if b = 1 then 1 else 0) +
          ((Finset.univ.filter (fun j : Fin m => y j = 1)).image Fin.succ).card := by
        have hdisj : Disjoint (if b = 1 then ({0} : Finset (Fin (m + 1))) else ∅)
            ((Finset.univ.filter (fun j : Fin m => y j = 1)).image Fin.succ) := by
          split_ifs
          · rw [Finset.disjoint_singleton_left]
            simp
          · exact Finset.disjoint_empty_left _
        have heq : Finset.univ.filter (fun j : Fin (m + 1) => Fin.cons (α := fun _ => F2) b y j = 1) =
            (if b = 1 then ({0} : Finset (Fin (m + 1))) else ∅) ∪
            (Finset.univ.filter (fun j : Fin m => y j = 1)).image Fin.succ := by
          ext j
          refine Fin.cases ?_ ?_ j
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.cons_zero,
              Finset.mem_union, Finset.mem_image, Fin.succ_ne_zero, and_false, exists_false, or_false]
            split_ifs with hb <;> simp [hb]
          · intro i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.cons_succ,
              Finset.mem_union, Finset.mem_image]
            constructor
            · intro hy; right; exact ⟨i, hy, rfl⟩
            · rintro (h0 | ⟨i', hi', hsucc⟩)
              · split_ifs at h0
                · rw [Finset.mem_singleton] at h0; exact absurd h0 (Fin.succ_ne_zero i)
                · exact absurd h0 (Finset.notMem_empty _)
              · cases Fin.succ_injective _ hsucc; exact hi'
        rw [heq, Finset.card_union_of_disjoint hdisj]
        congr 1
        split_ifs <;> simp
      rw [hsplit, Finset.card_image_of_injective _ (Fin.succ_injective m)]
    have hbij : ∑ y : Fin (m + 1) → F2, A ^ wt y * B ^ (m + 1 - wt y) =
        ∑ p : F2 × (Fin m → F2),
          A ^ wt (Fin.cons p.1 p.2) * B ^ (m + 1 - wt (Fin.cons p.1 p.2)) := by
      symm
      apply Finset.sum_bij (fun p _ => Fin.cons p.1 p.2)
      · intro _ _; exact Finset.mem_univ _
      · intro p1 _ p2 _ h
        have h0 : p1.1 = p2.1 := by
          have := congrFun h 0
          simpa using this
        have htl : p1.2 = p2.2 := by
          funext i
          have := congrFun h i.succ
          simpa using this
        exact Prod.ext h0 htl
      · intro y _
        refine ⟨(y 0, fun i => y i.succ), Finset.mem_univ _, ?_⟩
        funext j
        refine Fin.cases ?_ ?_ j
        · simp
        · intro i; simp
      · intro _ _; rfl
    rw [hbij, Fintype.sum_prod_type]
    have huniv2 : (Finset.univ : Finset F2) = {0, 1} := by decide
    rw [huniv2, Finset.sum_pair (by decide : (0 : F2) ≠ 1)]
    have h0 : ∑ y : Fin m → F2,
        A ^ wt (Fin.cons 0 y) * B ^ (m + 1 - wt (Fin.cons 0 y)) = B * (A + B) ^ m := by
      have hterm : ∀ y : Fin m → F2,
          A ^ wt (Fin.cons 0 y) * B ^ (m + 1 - wt (Fin.cons 0 y)) =
          B * (A ^ wt y * B ^ (m - wt y)) := by
        intro y
        rw [hwt_cons]
        have h01 : (0 : F2) ≠ 1 := by decide
        simp only [h01, ↓reduceIte, zero_add]
        have hle := wt_le y
        have hsub : m + 1 - wt y = (m - wt y) + 1 := by omega
        rw [hsub, pow_succ]
        ring
      simp_rw [hterm, ← Finset.mul_sum, ih]
    have h1 : ∑ y : Fin m → F2,
        A ^ wt (Fin.cons 1 y) * B ^ (m + 1 - wt (Fin.cons 1 y)) = A * (A + B) ^ m := by
      have hterm : ∀ y : Fin m → F2,
          A ^ wt (Fin.cons 1 y) * B ^ (m + 1 - wt (Fin.cons 1 y)) =
          A * (A ^ wt y * B ^ (m - wt y)) := by
        intro y
        rw [hwt_cons]
        simp only [↓reduceIte]
        have hsub : m + 1 - (1 + wt y) = m - wt y := by omega
        rw [hsub, Nat.add_comm 1 (wt y), pow_succ]
        ring
      simp_rw [hterm, ← Finset.mul_sum, ih]
    rw [h0, h1, pow_succ]
    ring

lemma card_toBits_bijective (N : ℕ) :
    Function.Bijective (fun (s : Fin (2 ^ N)) (t : Fin N) =>
      if s.val.testBit t.val then (1 : F2) else 0) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · intro s1 s2 h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < N
    · have hi' := congrFun h ⟨i, hi⟩
      dsimp only at hi'
      cases hb1 : s1.val.testBit i <;> cases hb2 : s2.val.testBit i
      · rfl
      · simp [hb1, hb2] at hi'
      · simp [hb1, hb2] at hi'
      · rfl
    · have h1 : s1.val.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le s1.isLt (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hi)))
      have h2 : s2.val.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le s2.isLt (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hi)))
      rw [h1, h2]
  · simp [Fintype.card_fin, ZMod.card]

lemma card_shift_linear_fiber (n L : ℕ) (hn : 0 < n) (hL : 0 < L)
    (c : Fin n → F2) (hc : c ≠ 0) (y : Fin L → F2) :
    (Finset.univ.filter (fun v : Fin (n + L - 1) → F2 =>
      (fun j : Fin L => ∑ i : Fin n, c i * v ⟨j.val + i.val, by omega⟩) = y)).card = 2 ^ (n - 1) := by
  let N := n + L - 1
  let Sc : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => c i = 1)
  have hSc_ne : Sc.Nonempty := by
    by_contra hempty
    apply hc
    funext i
    rcases zmod2_eq_zero_or_one (c i) with h0 | h1
    · exact h0
    · exfalso
      exact hempty ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩⟩
  let p : Fin n := Sc.max' hSc_ne
  have hcp : c p = 1 := (Finset.mem_filter.mp (Finset.max'_mem Sc hSc_ne)).2
  have hc_gt : ∀ i : Fin n, p < i → c i = 0 := by
    intro i hgt
    rcases zmod2_eq_zero_or_one (c i) with h0 | h1
    · exact h0
    · exfalso
      have hmem : i ∈ Sc := Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩
      have hle : i ≤ p := Finset.le_max' Sc i hmem
      exact not_le_of_gt hgt hle
  let Φ : (Fin N → F2) → (Fin L → F2) :=
    fun v j => ∑ i : Fin n, c i * v ⟨j.val + i.val, by omega⟩
  let Out := { t : Fin N // ¬ (p.val ≤ t.val ∧ t.val < p.val + L) }
  have hOut_card : Fintype.card Out = n - 1 := by
    let InS : Finset (Fin N) := Finset.univ.filter (fun t : Fin N => p.val ≤ t.val ∧ t.val < p.val + L)
    have hIn_card : InS.card = L := by
      have hbij : InS.card = (Finset.univ : Finset (Fin L)).card := by
        symm
        apply Finset.card_bij (fun (j : Fin L) _ => (⟨p.val + j.val, by omega⟩ : Fin N))
        · intro j _
          simp only [InS, Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        · intro j1 _ j2 _ h
          have hv : p.val + j1.val = p.val + j2.val := congrArg Fin.val h
          exact Fin.ext (by omega)
        · intro t ht
          simp only [InS, Finset.mem_filter, Finset.mem_univ, true_and] at ht
          refine ⟨⟨t.val - p.val, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp only; omega)⟩
      rw [hbij, Finset.card_univ, Fintype.card_fin]
    have hcomp : InS.card + (Finset.univ.filter (fun t : Fin N => ¬ (p.val ≤ t.val ∧ t.val < p.val + L))).card = N := by
      have hdisj : Disjoint InS (Finset.univ.filter (fun t : Fin N => ¬ (p.val ≤ t.val ∧ t.val < p.val + L))) := by
        rw [Finset.disjoint_left]
        intro t h1 h2
        simp only [InS, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact h2 h1
      have hunion : InS ∪ Finset.univ.filter (fun t : Fin N => ¬ (p.val ≤ t.val ∧ t.val < p.val + L)) = Finset.univ := by
        ext t
        simp only [InS, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact em _
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    rw [Fintype.card_subtype]
    omega
  let ψ : (Fin N → F2) → (Fin L → F2) × (Out → F2) :=
    fun v => (Φ v, fun t => v t.1)
  have hψ_bij : Function.Bijective ψ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, ?_⟩
    · intro v1 v2 hψ
      have hΦ : Φ v1 = Φ v2 := congrArg Prod.fst hψ
      have hOut : ∀ t : Out, v1 t.1 = v2 t.1 := fun t => congrFun (congrArg Prod.snd hψ) t
      have hall : ∀ k : ℕ, ∀ hk : k < N, v1 ⟨k, hk⟩ = v2 ⟨k, hk⟩ := by
        intro k
        induction k using Nat.strong_induction_on with
        | ind k ih =>
          intro hk
          by_cases hwin : p.val ≤ k ∧ k < p.val + L
          · let j : Fin L := ⟨k - p.val, by omega⟩
            have hj := congrFun hΦ j
            dsimp only [Φ] at hj
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p),
                ← Finset.add_sum_erase _ _ (Finset.mem_univ p)] at hj
            have hrest : ∑ i ∈ Finset.univ.erase p, c i * v1 ⟨j.val + i.val, by omega⟩ =
                ∑ i ∈ Finset.univ.erase p, c i * v2 ⟨j.val + i.val, by omega⟩ := by
              refine Finset.sum_congr rfl (fun i hi => ?_)
              have hne : i ≠ p := Finset.ne_of_mem_erase hi
              rcases lt_or_gt_of_ne hne with hlt | hgt
              · have hlt_k : j.val + i.val < k := by dsimp only [j]; omega
                rw [ih (j.val + i.val) hlt_k (by omega)]
              · rw [hc_gt i hgt, zero_mul, zero_mul]
            rw [hrest, hcp, one_mul, one_mul] at hj
            have heq_idx : (⟨j.val + p.val, by omega⟩ : Fin N) = ⟨k, hk⟩ := Fin.ext (by dsimp only [j]; omega)
            rw [heq_idx] at hj
            exact add_right_cancel hj
          · exact hOut ⟨⟨k, hk⟩, hwin⟩
      funext t
      exact hall t.val t.isLt
    · rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
          Fintype.card_fin, Fintype.card_fin, hOut_card, ZMod.card, ← pow_add]
      congr 1
      omega
  have hbij : (Finset.univ.filter (fun v : Fin N → F2 => Φ v = y)).card =
      (Finset.univ : Finset (Out → F2)).card := by
    apply Finset.card_bij (fun v _ => (ψ v).2)
    · intro _ _; exact Finset.mem_univ _
    · intro v1 hv1 v2 hv2 heq
      have h1 := (Finset.mem_filter.mp hv1).2
      have h2 := (Finset.mem_filter.mp hv2).2
      exact hψ_bij.1 (Prod.ext (h1.trans h2.symm) heq)
    · intro r _
      rcases hψ_bij.2 (y, r) with ⟨v, hv⟩
      refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, congrArg Prod.fst hv⟩, congrArg Prod.snd hv⟩
  rw [hbij, Finset.card_univ, Fintype.card_fun, hOut_card, ZMod.card]

lemma card_short_tail_bound (m g B : ℕ) (hg : g ≤ m) (hB : 0 < B) :
    (Finset.univ.filter (fun y : Fin m → F2 => wt y ≤ g)).card * B ^ m ≤
      (B + 1) ^ m * B ^ g := by
  let T : Finset (Fin m → F2) := Finset.univ.filter (fun y => wt y ≤ g)
  have hsum : T.card * B ^ (m - g) ≤ (B + 1) ^ m := by
    calc T.card * B ^ (m - g)
        = ∑ _y ∈ T, B ^ (m - g) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ y ∈ T, 1 ^ wt y * B ^ (m - wt y) := by
            refine Finset.sum_le_sum (fun y hy => ?_)
            rw [one_pow, one_mul]
            have hwy := (Finset.mem_filter.mp hy).2
            exact Nat.pow_le_pow_right hB (by omega)
      _ ≤ ∑ y : Fin m → F2, 1 ^ wt y * B ^ (m - wt y) :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ T)
      _ = (1 + B) ^ m := sum_pow_wt m 1 B
      _ = (B + 1) ^ m := by rw [Nat.add_comm]
  have hm_eq : m - g + g = m := by omega
  calc T.card * B ^ m
      = (T.card * B ^ (m - g)) * B ^ g := by rw [Nat.mul_assoc, ← pow_add, hm_eq]
    _ ≤ (B + 1) ^ m * B ^ g := Nat.mul_le_mul_right _ hsum

lemma card_short_product_bound (k m : ℕ) (hk : 64 ≤ k) (hm_lo : 512 * k ≤ m) (hm_hi : m ≤ 1024 * k) :
    let g := k / 32
    2 ^ (k / 16 + 2) *
      (Finset.univ.filter (fun S : Finset (Fin m) => 0 < S.card ∧ S.card ≤ g)).card *
      (Finset.univ.filter (fun z : Fin k → F2 => wt z ≤ g)).card ≤ 2 ^ k := by
  intro g
  let NS := (Finset.univ.filter (fun S : Finset (Fin m) => 0 < S.card ∧ S.card ≤ g)).card
  let Tm := (Finset.univ.filter (fun y : Fin m → F2 => wt y ≤ g)).card
  let Tk := (Finset.univ.filter (fun z : Fin k → F2 => wt z ≤ g)).card
  have hNS_le : NS ≤ Tm := by
    apply Finset.card_le_card_of_injOn (fun (S : Finset (Fin m)) (j : Fin m) => if j ∈ S then (1 : F2) else 0)
    · intro S hS
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      have hwt_eq : wt (fun j : Fin m => if j ∈ S then (1 : F2) else 0) = S.card := by
        unfold wt
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hj : j ∈ S <;> simp [hj]
      rw [hwt_eq]
      exact hS.2
    · intro S1 _ S2 _ heq
      ext j
      have hj := congrFun heq j
      dsimp only at hj
      by_cases h1 : j ∈ S1 <;> by_cases h2 : j ∈ S2 <;> simp [h1, h2] at hj ⊢
  have hTm_step : Tm ^ 16 ≤ 2 ^ (4 * k + 208 * g) := by
    have h1 := card_short_tail_bound m g 8192 (by omega) (by decide)
    have h16 := Nat.pow_le_pow_left h1 16
    have h8193 : 8193 ^ 4096 ≤ 2 * 8192 ^ 4096 := by
      simpa only [show 2 * 4096 + 1 = 8193 from rfl, show 2 * 4096 = 8192 from rfl] using
        pow_half_le_two_mul 4096 (by decide)
    have hm16 : 16 * m ≤ 4096 * (4 * k) := by omega
    have h8193_m : 8193 ^ (16 * m) ≤ 2 ^ (4 * k) * 8192 ^ (16 * m) := by
      have hpos : 0 < 8192 ^ (4096 * (4 * k) - 16 * m) := by positivity
      refine Nat.le_of_mul_le_mul_right ?_ hpos
      have hsplit : 16 * m + (4096 * (4 * k) - 16 * m) = 4096 * (4 * k) := by omega
      calc 8193 ^ (16 * m) * 8192 ^ (4096 * (4 * k) - 16 * m)
          ≤ 8193 ^ (16 * m) * 8193 ^ (4096 * (4 * k) - 16 * m) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _)
        _ = (8193 ^ 4096) ^ (4 * k) := by rw [← pow_add, hsplit, pow_mul]
        _ ≤ (2 * 8192 ^ 4096) ^ (4 * k) := Nat.pow_le_pow_left h8193 (4 * k)
        _ = 2 ^ (4 * k) * 8192 ^ (4096 * (4 * k)) := by rw [mul_pow, ← pow_mul]
        _ = 2 ^ (4 * k) * 8192 ^ (16 * m) * 8192 ^ (4096 * (4 * k) - 16 * m) := by
              rw [Nat.mul_assoc, ← pow_add, hsplit]
    have h8192_pow : (8192 ^ g) ^ 16 = 2 ^ (208 * g) := by
      have h8 : (8192 : ℕ) = 2 ^ 13 := by norm_num
      rw [h8, ← pow_mul, ← pow_mul]
      congr 1
      omega
    have hpos : 0 < 8192 ^ (16 * m) := by positivity
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Tm ^ 16 * 8192 ^ (16 * m)
        = (Tm * 8192 ^ m) ^ 16 := by rw [mul_pow, ← pow_mul, Nat.mul_comm m 16]
      _ ≤ (8193 ^ m * 8192 ^ g) ^ 16 := h16
      _ = 8193 ^ (16 * m) * (8192 ^ g) ^ 16 := by rw [mul_pow, ← pow_mul, Nat.mul_comm m 16]
      _ ≤ (2 ^ (4 * k) * 8192 ^ (16 * m)) * 2 ^ (208 * g) := by
            rw [h8192_pow]; exact Nat.mul_le_mul_right _ h8193_m
      _ = 2 ^ (4 * k + 208 * g) * 8192 ^ (16 * m) := by rw [pow_add]; ring
  have hTk_step : Tk ^ 16 ≤ 2 ^ (k + 80 * g) := by
    have h1 := card_short_tail_bound k g 32 (by omega) (by decide)
    have h16 := Nat.pow_le_pow_left h1 16
    have h33 : 33 ^ 16 ≤ 2 * 32 ^ 16 := by
      simpa only [show 2 * 16 + 1 = 33 from rfl, show 2 * 16 = 32 from rfl] using
        pow_half_le_two_mul 16 (by decide)
    have h33_k : 33 ^ (16 * k) ≤ 2 ^ k * 32 ^ (16 * k) := by
      calc 33 ^ (16 * k)
          = (33 ^ 16) ^ k := by rw [pow_mul]
        _ ≤ (2 * 32 ^ 16) ^ k := Nat.pow_le_pow_left h33 k
        _ = 2 ^ k * 32 ^ (16 * k) := by rw [mul_pow, ← pow_mul]
    have h32_pow : (32 ^ g) ^ 16 = 2 ^ (80 * g) := by
      have h32 : (32 : ℕ) = 2 ^ 5 := by norm_num
      rw [h32, ← pow_mul, ← pow_mul]
      congr 1
      omega
    have hpos : 0 < 32 ^ (16 * k) := by positivity
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Tk ^ 16 * 32 ^ (16 * k)
        = (Tk * 32 ^ k) ^ 16 := by rw [mul_pow, ← pow_mul, Nat.mul_comm k 16]
      _ ≤ (33 ^ k * 32 ^ g) ^ 16 := h16
      _ = 33 ^ (16 * k) * (32 ^ g) ^ 16 := by rw [mul_pow, ← pow_mul, Nat.mul_comm k 16]
      _ ≤ (2 ^ k * 32 ^ (16 * k)) * 2 ^ (80 * g) := by
            rw [h32_pow]; exact Nat.mul_le_mul_right _ h33_k
      _ = 2 ^ (k + 80 * g) * 32 ^ (16 * k) := by rw [pow_add]; ring
  have hpow16 : (2 ^ (k / 16 + 2) * NS * Tk) ^ 16 ≤ (2 ^ k) ^ 16 := by
    have hNS16 : NS ^ 16 ≤ 2 ^ (4 * k + 208 * g) :=
      le_trans (Nat.pow_le_pow_left hNS_le 16) hTm_step
    have hexp : 16 * (k / 16 + 2) + (4 * k + 208 * g) + (k + 80 * g) ≤ 16 * k := by omega
    calc (2 ^ (k / 16 + 2) * NS * Tk) ^ 16
        = 2 ^ (16 * (k / 16 + 2)) * NS ^ 16 * Tk ^ 16 := by
            rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm (k / 16 + 2) 16]
      _ ≤ 2 ^ (16 * (k / 16 + 2)) * 2 ^ (4 * k + 208 * g) * 2 ^ (k + 80 * g) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hNS16) hTk_step
      _ = 2 ^ (16 * (k / 16 + 2) + (4 * k + 208 * g) + (k + 80 * g)) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ (16 * k) := Nat.pow_le_pow_right (by decide) hexp
      _ = (2 ^ k) ^ 16 := by rw [Nat.mul_comm 16 k, pow_mul]
  exact nat_le_of_pow_le_pow_left (by decide : 16 ≠ 0) hpow16

lemma exists_good_seed (k m : ℕ) (hk : 64 ≤ k) (hm_lo : 512 * k ≤ m) (hm_hi : m ≤ 1024 * k) :
    ∃ s : Fin (2 ^ (k + m - 1)),
      ∀ S : Finset (Fin m), 0 < S.card → S.card ≤ k / 32 →
        let w := wt (fun i : Fin k => ∑ j ∈ S, if s.val.testBit (j.val + i.val) then (1 : F2) else 0)
        k / 32 < w ∧ w + k / 32 < k := by
  let N := k + m - 1
  let Seed := Fin (2 ^ N)
  let g := k / 32
  let win : Seed → Fin m → Fin k → F2 := fun s j i =>
    if s.val.testBit (j.val + i.val) then (1 : F2) else 0
  let toBits : Seed → (Fin N → F2) := fun s t =>
    if s.val.testBit t.val then (1 : F2) else 0
  have htoBits_bij : Function.Bijective toBits := card_toBits_bijective N
  let Sset : Finset (Finset (Fin m)) := Finset.univ.filter (fun S => 0 < S.card ∧ S.card ≤ g)
  let badS : Finset (Fin m) → Finset Seed := fun S =>
    Finset.univ.filter (fun s =>
      let w := wt (fun i : Fin k => ∑ j ∈ S, win s j i)
      ¬ (g < w ∧ w + g < k))
  let TkSet : Finset (Fin k → F2) := Finset.univ.filter (fun z => wt z ≤ g)
  let HkSet : Finset (Fin k → F2) := Finset.univ.filter (fun z => k ≤ wt z + g)
  have hHk_eq : HkSet.card = TkSet.card := by
    apply Finset.card_bij (fun (z : Fin k → F2) _ i => z i + 1)
    · intro z hz
      simp only [HkSet, TkSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      rw [wt_add_one z]
      have := wt_le z
      omega
    · intro z1 _ z2 _ heq
      funext i
      exact add_right_cancel (congrFun heq i)
    · intro z hz
      refine ⟨fun i => z i + 1, ?_, ?_⟩
      · simp only [HkSet, TkSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        rw [wt_add_one z]
        have := wt_le z
        omega
      · funext i
        dsimp only
        rw [add_assoc, zmod2_add_self, add_zero]
  have hbadS_card : ∀ S ∈ Sset, (badS S).card ≤ 2 * TkSet.card * 2 ^ (m - 1) := by
    intro S hS
    have hSpos : 0 < S.card := (Finset.mem_filter.mp hS).2.1
    let cS : Fin m → F2 := fun j => if j ∈ S then 1 else 0
    have hcS0 : cS ≠ 0 := by
      intro hc
      rcases Finset.card_pos.mp hSpos with ⟨j, hj⟩
      have h0 := congrFun hc j
      simp [cS, hj] at h0
    let φS : Seed → (Fin k → F2) := fun s i => ∑ j ∈ S, win s j i
    have hmaps : ∀ s ∈ badS S, φS s ∈ TkSet ∪ HkSet := by
      intro s hs
      have hbad := (Finset.mem_filter.mp hs).2
      simp only [Finset.mem_union, TkSet, HkSet, Finset.mem_filter, Finset.mem_univ, true_and]
      change ¬ (g < wt (φS s) ∧ wt (φS s) + g < k) at hbad
      omega
    have hfiber : ∀ z : Fin k → F2, ((badS S).filter (fun s => φS s = z)).card ≤ 2 ^ (m - 1) := by
      intro z
      have hle1 : ((badS S).filter (fun s => φS s = z)).card ≤
          (Finset.univ.filter (fun s : Seed => φS s = z)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
      have heq2 : (Finset.univ.filter (fun s : Seed => φS s = z)).card =
          (Finset.univ.filter (fun v : Fin (m + k - 1) → F2 =>
            (fun i : Fin k => ∑ j : Fin m, cS j * v ⟨i.val + j.val, by omega⟩) = z)).card := by
        apply Finset.card_bij (fun s _ t => toBits s ⟨t.val, by omega⟩)
        · intro s hs
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
          rw [← hs]
          funext i
          dsimp only [φS, cS, win, toBits]
          rw [← Finset.sum_subset (Finset.subset_univ S)]
          · refine Finset.sum_congr rfl (fun j hj => ?_)
            simp only [hj, ↓reduceIte, one_mul, Nat.add_comm i.val j.val]
          · intro j _ hj
            simp only [hj, ↓reduceIte, zero_mul]
        · intro s1 _ s2 _ h
          apply htoBits_bij.1
          funext t
          exact congrFun h ⟨t.val, by omega⟩
        · intro v hv
          rcases htoBits_bij.2 (fun t : Fin N => v ⟨t.val, by omega⟩) with ⟨s, hs⟩
          refine ⟨s, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
            rw [← hv]
            funext i
            dsimp only [φS, cS, win]
            rw [← Finset.sum_subset (Finset.subset_univ S)]
            · refine Finset.sum_congr rfl (fun j hj => ?_)
              have hbit := congrFun hs ⟨j.val + i.val, by omega⟩
              dsimp only [toBits] at hbit
              have hidx : (⟨j.val + i.val, by omega⟩ : Fin (m + k - 1)) = ⟨i.val + j.val, by omega⟩ :=
                Fin.ext (Nat.add_comm j.val i.val)
              rw [hidx] at hbit
              simp only [hj, ↓reduceIte, one_mul, hbit]
            · intro j _ hj
              simp only [hj, ↓reduceIte, zero_mul]
          · funext t
            exact congrFun hs ⟨t.val, by omega⟩
      rw [heq2] at hle1
      have hfib := card_shift_linear_fiber m k (by omega) (by omega) cS hcS0 z
      rw [hfib] at hle1
      exact hle1
    calc (badS S).card
        = ∑ z ∈ TkSet ∪ HkSet, ((badS S).filter (fun s => φS s = z)).card := by
            rw [Finset.card_eq_sum_card_fiberwise hmaps]
      _ ≤ ∑ _z ∈ TkSet ∪ HkSet, 2 ^ (m - 1) := Finset.sum_le_sum (fun z _ => hfiber z)
      _ = (TkSet ∪ HkSet).card * 2 ^ (m - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (TkSet.card + HkSet.card) * 2 ^ (m - 1) :=
            Nat.mul_le_mul_right _ (Finset.card_union_le TkSet HkSet)
      _ = 2 * TkSet.card * 2 ^ (m - 1) := by rw [hHk_eq]; ring
  have hS_total : (Sset.biUnion badS).card ≤ Sset.card * (2 * TkSet.card * 2 ^ (m - 1)) := by
    calc (Sset.biUnion badS).card
        ≤ ∑ S ∈ Sset, (badS S).card := Finset.card_biUnion_le
      _ ≤ ∑ _S ∈ Sset, (2 * TkSet.card * 2 ^ (m - 1)) := Finset.sum_le_sum hbadS_card
      _ = Sset.card * (2 * TkSet.card * 2 ^ (m - 1)) := by rw [Finset.sum_const, smul_eq_mul]
  have hboundS : 2 * (Sset.biUnion badS).card ≤ 2 ^ N := by
    have hs := card_short_product_bound k m hk hm_lo hm_hi
    have hpow_eq : 2 ^ k * 2 ^ (m - 1) = 2 ^ N := by
      rw [← pow_add]; congr 1; omega
    have hpow16 : 1 ≤ 2 ^ (k / 16) := Nat.one_le_two_pow
    calc 2 * (Sset.biUnion badS).card
        ≤ 2 * (Sset.card * (2 * TkSet.card * 2 ^ (m - 1))) := Nat.mul_le_mul_left 2 hS_total
      _ = (4 * Sset.card * TkSet.card) * 2 ^ (m - 1) := by ring
      _ ≤ (2 ^ (k / 16) * (4 * Sset.card * TkSet.card)) * 2 ^ (m - 1) :=
            Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ hpow16)
      _ = (2 ^ (k / 16 + 2) * Sset.card * TkSet.card) * 2 ^ (m - 1) := by
            rw [pow_add]; ring
      _ ≤ 2 ^ k * 2 ^ (m - 1) := Nat.mul_le_mul_right _ hs
      _ = 2 ^ N := hpow_eq
  have hlt : (Sset.biUnion badS).card < (Finset.univ : Finset Seed).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have hpos : 0 < 2 ^ N := Nat.two_pow_pos N
    omega
  obtain ⟨s, _, hs_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨s, fun S hS1 hS2 => ?_⟩
  by_contra hbad
  apply hs_not
  exact Finset.mem_biUnion.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS1, hS2⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ s, hbad⟩⟩

abbrev Sig (X : Type) := X → Bool

def GateOK (g : Gate) := g.inputs.length ≤ 2 ∧
  (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))

def Ready {X : Type} (N : Nat) (enc : X → List Bool) (d : Nat) (S : Set (Sig X)) :=
  ∃ gs : List Gate, gs.length ≤ d ∧ ReadsBack N ⟨gs, 0⟩ ∧ (∀ g ∈ gs, GateOK g) ∧
    ∀ f ∈ S, ∃ i < N + gs.length, ∀ x, ((Circuit.mk gs 0).wires (enc x)).getD i false = f x

lemma wlen (gs : List Gate) (xs : List Bool) :
    ((Circuit.mk gs 0).wires xs).length = xs.length + gs.length := by
  change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs).length = _
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp; omega

lemma weaken {X : Type} {N d c : Nat} {enc : X → List Bool} {S T : Set (Sig X)}
    (h : Ready N enc d S) (hc : d ≤ c) (hs : T ⊆ S) :
    Ready N enc c T := by
  obtain ⟨gs, hd, rb, fit, hw⟩ := h
  exact ⟨gs, hd.trans hc, rb, fit, fun f hf => hw f (hs hf)⟩

lemma emit {X : Type} {N d : Nat} {enc : X → List Bool} {S : Set (Sig X)}
    (len : ∀ x, (enc x).length = N) (h : Ready N enc d S) (op : GateOp)
    (deps : List (Sig X)) (f : Sig X) (hop : deps.length ≤ 2 ∧
      (op = .and ∨ op = .or ∨ (op = .not ∧ deps.length = 1)))
    (hd : ∀ z ∈ deps, z ∈ S) (val : ∀ x, op.eval (deps.map fun z => z x) = f x) :
    Ready N enc (d + 1) (insert f S) := by
  classical
  obtain ⟨gs, hb, hr, hf, hw⟩ := h
  let wire (z : Sig X) := if hz : z ∈ S then (hw z hz).choose else 0
  have spec (z : Sig X) (hz : z ∈ S) : wire z < N + gs.length ∧
      ∀ x, ((Circuit.mk gs 0).wires (enc x)).getD (wire z) false = z x := by
    simpa [wire, hz] using (hw z hz).choose_spec
  let g : Gate := ⟨op, deps.map wire⟩
  have snoc (x : X) : (Circuit.mk (gs ++ [g]) 0).wires (enc x) =
      (Circuit.mk gs 0).wires (enc x) ++ [f x] := by
    have mapped : (deps.map wire).map (fun i => ((Circuit.mk gs 0).wires (enc x)).getD i false) =
        deps.map (fun z => z x) := by
      rw [List.map_map]; apply List.map_congr_left; exact fun z hz => (spec z (hd z hz)).2 x
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change _ ++ [op.eval ((deps.map wire).map (fun i => ((Circuit.mk gs 0).wires (enc x)).getD i false))] = _
    rw [mapped, val]
  refine ⟨gs ++ [g], by simp; omega, ?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (gs ++ [g]).length at hj
    change i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hr j hj' i hi
    · have eq : j = gs.length := by simp at hj; omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      have hm : i ∈ deps.map wire := by simpa [g] using hi
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hm
      exact (spec z (hd z hz)).1
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hf z hz
    · obtain rfl := List.mem_singleton.mp hz
      simpa [GateOK, g] using hop
  · intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · refine ⟨N + gs.length, by simp, fun x => ?_⟩
      rw [snoc, List.getD_append_right _ _ _ _ (by simp [wlen, len])]
      simp [wlen, len]
    · obtain ⟨i, hi, he⟩ := hw z hz
      refine ⟨i, by simp; omega, fun x => ?_⟩
      rw [snoc, List.getD_append _ _ _ _ (by simpa [wlen, len] using hi), he]

def conj {X : Type} (a b : Sig X) : Sig X := fun x => a x && b x

def disj {X : Type} (a b : Sig X) : Sig X := fun x => a x || b x

def negB {X : Type} (a : Sig X) : Sig X := fun x => !a x

def parity {X : Type} (a b : Sig X) : Sig X := fun x => xor (a x) (b x)

lemma conjG {X : Type} {N d : Nat} {enc : X → List Bool} {S : Set (Sig X)}
    (len : ∀ x, (enc x).length = N) (h : Ready N enc d S) {a b : Sig X}
    (ha : a ∈ S) (hb : b ∈ S) : Ready N enc (d + 1) (insert (conj a b) S) :=
  emit len h .and [a, b] _ (by simp) (by simpa using And.intro ha hb) (by simp [conj, GateOp.eval])

lemma disjG {X : Type} {N d : Nat} {enc : X → List Bool} {S : Set (Sig X)}
    (len : ∀ x, (enc x).length = N) (h : Ready N enc d S) {a b : Sig X}
    (ha : a ∈ S) (hb : b ∈ S) : Ready N enc (d + 1) (insert (disj a b) S) :=
  emit len h .or [a, b] _ (by simp) (by simpa using And.intro ha hb) (by simp [disj, GateOp.eval])

lemma negG {X : Type} {N d : Nat} {enc : X → List Bool} {S : Set (Sig X)}
    (len : ∀ x, (enc x).length = N) (h : Ready N enc d S) {a : Sig X}
    (ha : a ∈ S) : Ready N enc (d + 1) (insert (negB a) S) :=
  emit len h .not [a] _ (by simp) (by simpa using ha) (by simp [negB, GateOp.eval])

lemma constG {X : Type} {N d : Nat} {enc : X → List Bool} {S : Set (Sig X)}
    (len : ∀ x, (enc x).length = N) (h : Ready N enc d S) (b : Bool) :
    Ready N enc (d + 1) (insert (fun _ => b) S) := by
  cases b
  · exact emit len h .or [] _ (by simp) (by simp) (by intro; rfl)
  · exact emit len h .and [] _ (by simp) (by simp) (by intro; rfl)

lemma xorG {X : Type} {N d : Nat} {enc : X → List Bool} {S : Set (Sig X)}
    (len : ∀ x, (enc x).length = N) (h : Ready N enc d S) {a b : Sig X}
    (ha : a ∈ S) (hb : b ∈ S) : Ready N enc (d + 4) (insert (parity a b) S) := by
  have eq : parity a b = conj (disj a b) (negB (conj a b)) := by
    funext x; cases e : a x <;> cases f : b x <;> simp [parity, conj, disj, negB, e, f]
  rw [eq]
  have h1 := conjG len h ha hb
  have h2 := disjG len h1 (Set.mem_insert_of_mem _ ha) (Set.mem_insert_of_mem _ hb)
  have h3 := negG len h2 (Set.mem_insert_of_mem _ (Set.mem_insert (conj a b) S))
  have h4 := conjG len h3 (Set.mem_insert_of_mem _ (Set.mem_insert (disj a b) _)) (Set.mem_insert _ _)
  exact weaken h4 le_rfl (by intro z hz; simp_all only [Set.mem_insert_iff]; tauto)

lemma muxG {X : Type} {N d : Nat} {enc : X → List Bool} {S : Set (Sig X)}
    (len : ∀ x, (enc x).length = N) (h : Ready N enc d S) {a b sel : Sig X}
    (ha : a ∈ S) (hb : b ∈ S) (hs : sel ∈ S) (hn : negB sel ∈ S) :
    Ready N enc (d + 3) (insert (fun x => if sel x then b x else a x) S) := by
  have eq : (fun x => if sel x then b x else a x) = disj (conj (negB sel) a) (conj sel b) := by
    funext x; cases e : sel x <;> simp [disj, conj, negB, e]
  rw [eq]
  have h1 := conjG len h hn ha
  have h2 := conjG len h1 (Set.mem_insert_of_mem _ hs) (Set.mem_insert_of_mem _ hb)
  have h3 := disjG len h2 (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) (Set.mem_insert _ _)
  exact weaken h3 le_rfl (by intro z hz; simp_all only [Set.mem_insert_iff]; tauto)

lemma batch {X : Type} {N d : Nat} {enc : X → List Bool} {S : Set (Sig X)}
    (h : Ready N enc d S) (f : Nat → Sig X) (b L : Nat)
    (build : ∀ i < L, ∀ {c U}, S ⊆ U → Ready N enc c U → Ready N enc (c + b) (insert (f i) U)) :
    Ready N enc (d + L * b) (S ∪ {g | ∃ i < L, g = f i}) := by
  induction L with
  | zero => simpa using h
  | succ L ih =>
    have prev := ih (fun i hi {c U} hs hr => build i (Nat.lt_succ_of_lt hi) hs hr)
    have step := build L (Nat.lt_succ_self _) Set.subset_union_left prev
    apply weaken step (by rw [Nat.succ_mul]; omega)
    intro g hg
    rcases hg with hg | ⟨i, hi, rfl⟩
    · exact Or.inr (Or.inl hg)
    · by_cases eq : i = L
      · exact Or.inl (congrArg f eq)
      · exact Or.inr (Or.inr ⟨i, by omega, rfl⟩)

def addr {X : Type} (bits : Nat → Sig X) : Nat → X → Nat
  | 0, _ => 0
  | q + 1, x => (if bits q x then 2 ^ q else 0) + addr bits q x

lemma decode {X : Type} (a : X → Nat) (q : Nat) (x : X) :
    addr (fun i v => (a v).testBit i) q x = a x % 2 ^ q := by
  induction q with
  | zero => simp [addr, Nat.mod_one]
  | succ q ih =>
    rw [addr, ih, Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    by_cases h : a x / 2 ^ q % 2 = 1
    · simp [h, Nat.add_comm]
    · have hz : a x / 2 ^ q % 2 = 0 := by omega
      simp [hz]

lemma sweep {X : Type} {N d : Nat} {enc : X → List Bool} {S : Set (Sig X)}
    (len : ∀ x, (enc x).length = N) (bits : Nat → Sig X) (u q : Nat)
    (T : Nat → Sig X) (h : Ready N enc d S) (hb : ∀ z < q, bits z ∈ S)
    (ht : ∀ i < u + 2 ^ q, T i ∈ S) :
    Ready N enc (d + 3 * (u * q + (2 ^ q - 1)) + q)
      (S ∪ {g | ∃ i < u + 1, g = fun x => T (addr bits q x + i) x}) := by
  induction q generalizing S d T with
  | zero =>
    apply weaken h (by simp)
    rintro g (hg | ⟨i, hi, rfl⟩)
    · exact hg
    · simpa [addr] using ht i (by simpa using hi)
  | succ q ih =>
    let L := u + 2 ^ q
    let T' (i : Nat) : Sig X := fun x => if bits q x then T (2 ^ q + i) x else T i x
    let S1 := insert (negB (bits q)) S
    let S2 := S1 ∪ {g | ∃ i < L, g = T' i}
    have h1 : Ready N enc (d + 1) S1 := negG len h (hb q (Nat.lt_succ_self _))
    have h2 : Ready N enc (d + 1 + L * 3) S2 := by
      apply batch h1 T' 3 L
      intro i hi c U sub pre
      have hwidth : 2 ^ (q + 1) = 2 ^ q * 2 := pow_succ _ _
      dsimp only [L] at hi
      exact muxG len pre (sub (Or.inr (ht i (by omega))))
        (sub (Or.inr (ht (2 ^ q + i) (by omega)))) (sub (Or.inr (hb q (Nat.lt_succ_self _))))
        (sub (Set.mem_insert _ _))
    have restBuilt := ih T' h2 (fun z hz => Or.inl (Or.inr (hb z (Nat.lt_succ_of_lt hz))))
      (fun i hi => Or.inr ⟨i, hi, rfl⟩)
    apply weaken restBuilt
    · have hmul : u * (q + 1) = u * q + u := Nat.mul_succ u q
      have hp := Nat.two_pow_pos q
      dsimp only [L]
      rw [pow_succ 2 q, hmul]
      omega
    · rintro g (hg | ⟨i, hi, rfl⟩)
      · exact Or.inl (Or.inl (Or.inr hg))
      · refine Or.inr ⟨i, hi, ?_⟩
        funext x; cases e : bits q x <;> simp [addr, T', e, Nat.add_assoc]

lemma dotG {X : Type} {N d k : Nat} {enc : X → List Bool} {S : Set (Sig X)}
    (len : ∀ x, (enc x).length = N) (a b : Fin k → Sig X)
    (h : Ready N enc d S) (ha : ∀ i, a i ∈ S) (hb : ∀ i, b i ∈ S)
    (hz : (fun _ : X => false) ∈ S) (K : Finset (Fin k)) :
    Ready N enc (d + 5 * K.card) (insert (fun x => decide ((K.filter
      (fun i => a i x && b i x)).card % 2 = 1)) S) := by
  classical
  induction K using Finset.induction_on with
  | empty => simpa [Set.insert_eq_of_mem hz] using h
  | @insert i K hi ih =>
    let prev : Sig X := fun x => decide ((K.filter (fun j => a j x && b j x)).card % 2 = 1)
    let term := conj (a i) (b i)
    have h1 := conjG len ih (Set.mem_insert_of_mem _ (ha i)) (Set.mem_insert_of_mem _ (hb i))
    have h2 := xorG len h1 (Set.mem_insert_of_mem term (Set.mem_insert prev S)) (Set.mem_insert term _)
    have eq : (fun x => decide ((((insert i K).filter (fun j => a j x && b j x)).card % 2) = 1)) =
        parity prev term := by
      funext x
      have notmem : i ∉ K.filter (fun j => a j x && b j x) := fun h => hi (Finset.mem_filter.mp h).1
      cases e : a i x && b i x
      · have off : ¬ (a i x && b i x) = true := by rw [e]; decide
        rw [Finset.filter_insert, ite_eq_right off]
        simp only [parity, prev, term, conj, e, Bool.xor_false]
      · simp only [Finset.filter_insert, e, ite_true, Finset.card_insert_of_notMem notmem,
          parity, prev, term, conj, Bool.xor_true]
        apply Bool.eq_iff_iff.mpr
        simp; omega
    rw [eq]
    apply weaken h2 (by rw [Finset.card_insert_of_notMem hi, Nat.mul_succ]; omega)
    intro g hg
    rcases Set.mem_insert_iff.mp hg with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inr (Or.inr e))

lemma decide_dot_eq_filter_mod {k : ℕ} (row b : Fin k → Bool) :
    decide (dot (fun i => if row i then (1 : F2) else 0)
      (fun i => if b i then (1 : F2) else 0) = 1) =
    decide (((Finset.univ : Finset (Fin k)).filter (fun i => row i && b i)).card % 2 = 1) := by
  apply decide_eq_decide.mpr
  have hsum : dot (fun i => if row i then (1 : F2) else 0)
      (fun i => if b i then (1 : F2) else 0) =
      (((Finset.univ : Finset (Fin k)).filter (fun i => row i && b i)).card : F2) := by
    unfold dot
    have hterm : ∀ i : Fin k,
        (if row i then (1 : F2) else 0) * (if b i then (1 : F2) else 0) =
        if (row i && b i) = true then (1 : F2) else 0 := by
      intro i
      cases row i <;> cases b i <;> decide
    simp_rw [hterm]
    rw [Finset.sum_boole]
  rw [hsum]
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast] at hv
    exact hv
  · intro h
    apply ZMod.val_injective 2
    rw [ZMod.val_natCast]
    exact h

lemma exists_tape_circuit (k t : ℕ) (hk : 0 < k) (s : Fin (2 ^ (k + 2 ^ t - 1))) :
    ∃ C : Circuit,
      ReadsBack (k + t) C ∧
      C.output < k + t + C.size ∧
      C.size ≤ 3 * ((k - 1) * t + (2 ^ t - 1)) + t + 5 * k + 2 ∧
      (∀ gate ∈ C.gates, GateOK gate) ∧
      ∀ (row : Fin k → Bool) (j : Fin (2 ^ t)),
        C.eval (List.ofFn row ++ List.ofFn (fun z : Fin t => j.val.testBit z.val)) =
          decide (dot (fun i => if row i then 1 else 0)
            (fun i => if s.val.testBit (j.val + i.val) then (1 : F2) else 0) = 1) := by
  classical
  let X := (Fin k → Bool) × Fin (2 ^ t)
  let N := k + t
  let bits (z : Nat) (x : X) := x.2.val.testBit z
  let rowS (i : Fin k) (x : X) := x.1 i
  let enc (x : X) := List.ofFn x.1 ++ List.ofFn (fun z : Fin t => bits z.val x)
  have len (x) : (enc x).length = N := by simp [enc, N]
  let A : Set (Sig X) := {f | ∃ i < N, ∀ x, (enc x).getD i false = f x}
  have start : Ready N enc 0 A := by
    refine ⟨[], le_rfl, ?_, by simp, ?_⟩
    · intro j hj; simp at hj
    · rintro f ⟨i, hi, h⟩; exact ⟨i, by simpa using hi, h⟩
  have atFn {q : Nat} (f : Fin q → Bool) (i : Fin q) : (List.ofFn f).getD i.val false = f i := by
    rw [List.getD_eq_getElem _ _ (by simp [i.isLt]), List.getElem_ofFn]
  have rmem (i : Fin k) : rowS i ∈ A := by
    refine ⟨i.val, by dsimp [N]; omega, fun x => ?_⟩
    dsimp only [enc, rowS]
    rw [List.getD_append _ _ _ _ (by simp [i.isLt]), atFn]
  have bmem (z : Nat) (hz : z < t) : bits z ∈ A := by
    refine ⟨k + z, by dsimp [N]; omega, fun x => ?_⟩
    dsimp only [enc]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simpa only [List.length_ofFn, Nat.add_sub_cancel_left] using
      atFn (fun i : Fin t => bits i.val x) ⟨z, hz⟩
  let Cst : Set (Sig X) := insert (fun _ => true) (insert (fun _ => false) A)
  have constants : Ready N enc 2 Cst := constG len (constG len start false) true
  let T (i : Nat) (_ : X) := s.val.testBit i
  have tin (i : Nat) : T i ∈ Cst := by
    cases e : s.val.testBit i <;> simp [Cst, T, e]
  let win (i : Fin k) (x : X) := T (addr bits t x + i.val) x
  let U := Cst ∪ {g | ∃ i < k - 1 + 1, g = fun x => T (addr bits t x + i) x}
  have built : Ready N enc (2 + 3 * ((k - 1) * t + (2 ^ t - 1)) + t) U :=
    sweep len bits (k - 1) t T constants (fun z hz => Or.inr (Or.inr (bmem z hz))) (fun i _ => tin i)
  have ws (i : Fin k) : win i ∈ U := Or.inr ⟨i.val, by omega, rfl⟩
  let out : Sig X := fun x => decide (((Finset.univ.filter (fun i : Fin k => rowS i x && win i x)).card % 2) = 1)
  obtain ⟨gs, hb, hr, hg, hw⟩ := dotG len rowS win built
    (fun i => Or.inl (Or.inr (Or.inr (rmem i)))) ws (Or.inl (Or.inr (Set.mem_insert _ _))) Finset.univ
  obtain ⟨i, hi, he⟩ := hw out (Set.mem_insert _ _)
  have decj (x : X) : addr bits t x = x.2.val :=
    (decode (fun x : X => x.2.val) t x).trans (Nat.mod_eq_of_lt x.2.isLt)
  refine ⟨⟨gs, i⟩, hr, hi, ?_, hg, ?_⟩
  · simp only [Finset.card_univ, Fintype.card_fin] at hb
    change gs.length ≤ _
    omega
  · intro r j
    rw [decide_dot_eq_filter_mod]
    simpa only [Circuit.eval, Circuit.wires, out, rowS, win, decj, T, enc, bits] using he (r, j)

def orth {k : ℕ} (S : Submodule F2 (Vec k)) : Submodule F2 (Vec k) :=
  { carrier := {w | ∀ x ∈ S, dot x w = 0}, zero_mem' := fun x _ => dot_zero_right x,
    smul_mem' := fun c _ ha x hx => by rw [dot_smul_right, ha x hx, mul_zero], add_mem' := fun ha hb x hx => by rw [dot_add_right, ha x hx, hb x hx, add_zero] }

lemma le_orth_orth {k : ℕ} (S : Submodule F2 (Vec k)) : S ≤ orth (orth S) := by
  intro x hx w hw
  rw [dot_comm]
  exact hw x hx

lemma finrank_orth_add {k : ℕ} (S : Submodule F2 (Vec k)) :
    Module.finrank F2 (orth S) + Module.finrank F2 S = k := by
  let b := Module.finBasis F2 S
  let d := Module.finrank F2 S
  let ev : Vec k →ₗ[F2] (Fin d → F2) :=
    { toFun := fun w i => dot (b i).1 w
      map_add' := fun w1 w2 => by funext i; exact dot_add_right _ w1 w2
      map_smul' := fun c w => by funext i; exact dot_smul_right c _ w }
  have hker : LinearMap.ker ev = orth S := by
    ext w
    simp only [LinearMap.mem_ker, orth, Submodule.mem_mk, AddSubmonoid.mem_mk,
      AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
    constructor
    · intro hw x hx
      have hx' : (⟨x, hx⟩ : S) ∈ Submodule.span F2 (Set.range b) := by
        rw [b.span_eq]; exact Submodule.mem_top
      let f : S →ₗ[F2] F2 :=
        { toFun := fun u => dot u.1 w
          map_add' := fun u1 u2 => dot_add_left u1.1 u2.1 w
          map_smul' := fun c u => dot_smul_left c u.1 w }
      have hle : Submodule.span F2 (Set.range b) ≤ LinearMap.ker f := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact congrFun hw i
      exact hle hx'
    · intro hw
      funext i
      exact hw (b i).1 (b i).2
  have hsurj : LinearMap.range ev = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨T, hST⟩ := Submodule.exists_isCompl S
    let g : S →ₗ[F2] F2 := b.constr F2 y
    let ψ : Vec k →ₗ[F2] F2 := g.comp (Submodule.projectionOnto S T hST)
    let w : Vec k := fun r => ψ (Pi.single r 1)
    refine ⟨w, ?_⟩
    funext i
    have hdot_psi : ∀ v : Vec k, dot v w = ψ v := by
      intro v
      have hv : v = ∑ r : Fin k, v r • Pi.single r (1 : F2) := by
        funext j
        simp [Pi.single_apply]
      conv_rhs => rw [hv]
      rw [map_sum]
      simp only [map_smul, smul_eq_mul, dot, w]
    change dot (b i).1 w = y i
    rw [hdot_psi (b i).1]
    change g (Submodule.projectionOnto S T hST (b i).1) = y i
    rw [Submodule.projectionOnto_apply_left hST (b i)]
    exact Module.Basis.constr_basis b F2 y i
  have hrn := ev.finrank_range_add_finrank_ker
  rw [hsurj, finrank_top, hker, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_fin] at hrn
  omega

lemma orth_orth {k : ℕ} (S : Submodule F2 (Vec k)) : orth (orth S) = S := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq (le_orth_orth S)
  have h1 := finrank_orth_add S
  have h2 := finrank_orth_add (orth S)
  omega

lemma orth_sup {k : ℕ} (A B : Submodule F2 (Vec k)) : orth (A ⊔ B) = orth A ⊓ orth B := by
  ext w
  simp only [orth, Submodule.mem_inf, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
  constructor
  · intro hw
    exact ⟨fun x hx => hw x (Submodule.mem_sup_left hx),
           fun x hx => hw x (Submodule.mem_sup_right hx)⟩
  · rintro ⟨hA, hB⟩ x hx
    rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
    rw [dot_add_left, hA a ha, hB b hb, zero_add]

def sliceL {k : ℕ} (P : Finset (Fin k)) : Submodule F2 (Vec k) :=
  { carrier := {h | (∀ i ∈ P, h i = 0) ∧ (∑ i : Fin k, h i) = 0}
    zero_mem' := ⟨fun _ _ => rfl, by simp⟩
    smul_mem' := fun c h hh => ⟨fun i hi => by simp [hh.1 i hi], by simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hh.2, mul_zero]⟩, add_mem' := fun ha hb => ⟨fun i hi => by simp [ha.1 i hi, hb.1 i hi], by simp only [Pi.add_apply, Finset.sum_add_distrib, ha.2, hb.2, zero_add]⟩ }

lemma slice_nonempty {k : ℕ} (P : Finset (Fin k)) (hPk : P.card < k) (pins : Vec k) (par : F2) :
    ((Finset.univ : Finset (Vec k)).filter (fun x =>
      (∀ i ∈ P, x i = pins i) ∧ (∑ i : Fin k, x i) = par)).Nonempty := by
  have hcompl_pos : 0 < (Finset.univ \ P).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨i0, hi0⟩ := Finset.card_pos.mp hcompl_pos
  have hi0_not : i0 ∉ P := (Finset.mem_sdiff.mp hi0).2
  let x0 : Vec k := fun i => if i ∈ P then pins i else if i = i0 then par + ∑ j ∈ P, pins j else 0
  refine ⟨x0, Finset.mem_filter.mpr ⟨Finset.mem_univ x0, ?_, ?_⟩⟩
  · intro i hi
    simp [x0, hi]
  · rw [← Finset.sum_add_sum_compl P]
    have hPsum : ∑ i ∈ P, x0 i = ∑ i ∈ P, pins i :=
      Finset.sum_congr rfl (fun i hi => by simp [x0, hi])
    have hCsum : ∑ i ∈ Pᶜ, x0 i = par + ∑ j ∈ P, pins j := by
      have hi0c : i0 ∈ Pᶜ := Finset.mem_compl.mpr hi0_not
      rw [← Finset.add_sum_erase _ _ hi0c]
      have hrest : ∑ i ∈ Pᶜ.erase i0, x0 i = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hne : i ≠ i0 := Finset.ne_of_mem_erase hi
        have hnotP : i ∉ P := Finset.mem_compl.mp (Finset.mem_of_mem_erase hi)
        simp [x0, hnotP, hne]
      rw [hrest, add_zero]
      simp [x0, hi0_not]
    rw [hPsum, hCsum]
    calc (∑ j ∈ P, pins j) + (par + ∑ j ∈ P, pins j)
        = par + ((∑ j ∈ P, pins j) + ∑ j ∈ P, pins j) := by ring
      _ = par + 0 := by rw [zmod2_add_self]
      _ = par := by rw [add_zero]

lemma mem_slice_iff_sub_mem {k : ℕ} (P : Finset (Fin k)) (pins : Vec k) (par : F2)
    {x0 y : Vec k}
    (hx0 : x0 ∈ (Finset.univ : Finset (Vec k)).filter (fun x =>
      (∀ i ∈ P, x i = pins i) ∧ (∑ i : Fin k, x i) = par)) :
    y ∈ (Finset.univ : Finset (Vec k)).filter (fun x =>
      (∀ i ∈ P, x i = pins i) ∧ (∑ i : Fin k, x i) = par) ↔ y - x0 ∈ sliceL P := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx0 ⊢
  change ((∀ i ∈ P, y i = pins i) ∧ ∑ i : Fin k, y i = par) ↔
    ((∀ i ∈ P, y i - x0 i = 0) ∧ ∑ i : Fin k, (y i - x0 i) = 0)
  rw [Finset.sum_sub_distrib, hx0.2]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => by rw [h1 i hi, hx0.1 i hi, sub_self], by rw [h2, sub_self]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i hi => by rw [← hx0.1 i hi]; exact sub_eq_zero.mp (h1 i hi), sub_eq_zero.mp h2⟩

lemma mem_orth_sliceL_wt {k : ℕ} {P : Finset (Fin k)} (hPk : P.card < k) {w : Vec k}
    (hw : w ∈ orth (sliceL P)) : wt w ≤ P.card ∨ k ≤ wt w + P.card := by
  have hcompl_pos : 0 < (Finset.univ \ P).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨i0, hi0⟩ := Finset.card_pos.mp hcompl_pos
  have hi0_not : i0 ∉ P := (Finset.mem_sdiff.mp hi0).2
  have hconst : ∀ i : Fin k, i ∉ P → w i = w i0 := by
    intro i hi
    let h : Vec k := Pi.single i (1 : F2) + Pi.single i0 (1 : F2)
    have hh : h ∈ sliceL P := by
      refine ⟨fun r hr => ?_, ?_⟩
      · have hr1 : r ≠ i := fun heq => hi (heq ▸ hr)
        have hr2 : r ≠ i0 := fun heq => hi0_not (heq ▸ hr)
        simp [h, hr1, hr2]
      · simp only [h, Pi.add_apply, Finset.sum_add_distrib, Pi.single_apply,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        exact zmod2_add_self 1
    have hdot : dot h w = 0 := hw h hh
    have hdot_eq : dot h w = w i + w i0 := by
      dsimp only [h]
      rw [dot_add_left]
      simp only [dot, Pi.single_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [hdot_eq] at hdot
    rcases zmod2_eq_zero_or_one (w i) with h1 | h1 <;>
      rcases zmod2_eq_zero_or_one (w i0) with h2 | h2 <;> simp_all
  rcases zmod2_eq_zero_or_one (w i0) with h0 | h1
  · left
    apply Finset.card_le_card
    intro i hi
    have hwi : w i = 1 := (Finset.mem_filter.mp hi).2
    by_contra hnot
    have heq := hconst i hnot
    rw [h0] at heq
    rw [heq] at hwi
    exact absurd hwi (by decide)
  · right
    have hsub : Pᶜ ⊆ Finset.univ.filter (fun i : Fin k => w i = 1) := by
      intro i hi
      have hnot : i ∉ P := Finset.mem_compl.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (hconst i hnot).trans h1⟩
    have hcard := Finset.card_le_card hsub
    have hpc : Pᶜ.card + P.card = k := by
      rw [Finset.card_compl, Fintype.card_fin]
      have : P.card ≤ k := le_of_lt hPk
      omega
    change Pᶜ.card ≤ wt w at hcard
    omega

lemma card_filter_dot_eq_half {k : ℕ} (S : Finset (Vec k)) (h w : Vec k)
    (hclosed : ∀ x ∈ S, x + h ∈ S) (hdot : dot h w = 1) (b : F2) :
    2 * (S.filter (fun x => b = dot x w)).card = S.card := by
  have heq : (S.filter (fun x => b = dot x w)).card =
      (S.filter (fun x => ¬ (b = dot x w))).card := by
    apply Finset.card_bij (fun x _ => x + h)
    · intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxS, hxb⟩
      refine Finset.mem_filter.mpr ⟨hclosed x hxS, ?_⟩
      rw [dot_add_left, hdot, ← hxb]
      intro hc
      rcases zmod2_eq_zero_or_one b with rfl | rfl <;> simp at hc
    · intro x1 _ x2 _ heq
      exact add_right_cancel heq
    · intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hyS, hyb⟩
      refine ⟨y + h, Finset.mem_filter.mpr ⟨hclosed y hyS, ?_⟩, ?_⟩
      · rw [dot_add_left, hdot]
        exact ((zmod2_ne_iff_add_one b (dot y w)).mp hyb).symm
      · rw [add_assoc, vec_add_self, add_zero]
  have hdisj : Disjoint (S.filter (fun x => b = dot x w)) (S.filter (fun x => ¬ (b = dot x w))) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hunion : S.filter (fun x => b = dot x w) ∪ S.filter (fun x => ¬ (b = dot x w)) = S := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  have htot : (S.filter (fun x => b = dot x w)).card + (S.filter (fun x => ¬ (b = dot x w))).card = S.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  omega

def sgn (a : F2) : ℤ := if a = 1 then -1 else 1

lemma sgn_zero : sgn 0 = 1 := by decide

lemma sgn_add (a b : F2) : sgn (a + b) = sgn a * sgn b := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one b with rfl | rfl <;> decide

lemma sgn_le_one (a : F2) : sgn a ≤ 1 := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> decide

lemma sum_sgn_eq_zero {k : ℕ} (S : Finset (Vec k)) (h w : Vec k)
    (hclosed : ∀ x ∈ S, x + h ∈ S) (hdot : dot h w = 1) :
    ∑ x ∈ S, sgn (dot x w) = 0 := by
  have hshift : ∑ x ∈ S, sgn (dot x w) = ∑ x ∈ S, sgn (dot (x + h) w) := by
    symm
    apply Finset.sum_bij (fun x _ => x + h)
    · intro x hx; exact hclosed x hx
    · intro x1 _ x2 _ heq; exact add_right_cancel heq
    · intro y hy; exact ⟨y + h, hclosed y hy, by rw [add_assoc, vec_add_self, add_zero]⟩
    · intro _ _; rfl
  have h2 : ∑ x ∈ S, sgn (dot x w) + ∑ x ∈ S, sgn (dot x w) = 0 := by
    conv_rhs => rw [show (0 : ℤ) = ∑ _x ∈ S, (0 : ℤ) by simp]
    conv_lhs => rhs; rw [hshift]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [dot_add_left, hdot, sgn_add]
    rcases zmod2_eq_zero_or_one (dot x w) with h0 | h1
    · simp [sgn, h0]
    · simp [sgn, h1]
  omega

lemma finrank_span_range_le {k q : ℕ} (p : Fin q → Vec k) :
    Module.finrank F2 (Submodule.span F2 (Set.range p)) ≤ q := by
  let L : (Fin q → F2) →ₗ[F2] Vec k :=
    { toFun := fun c => ∑ l : Fin q, c l • p l
      map_add' := fun c1 c2 => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }
  have hle : Submodule.span F2 (Set.range p) ≤ LinearMap.range L := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    refine ⟨Pi.single l 1, ?_⟩
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  calc Module.finrank F2 (Submodule.span F2 (Set.range p))
      ≤ Module.finrank F2 (LinearMap.range L) := Submodule.finrank_mono hle
    _ ≤ Module.finrank F2 (Fin q → F2) := LinearMap.finrank_range_le L
    _ = q := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

lemma holder_1_2_4 {α : Type*} (X : Finset α) (a : α → ℤ) (ha : ∀ x ∈ X, 0 ≤ a x) :
    (∑ x ∈ X, a x ^ 2) ^ 3 ≤ (∑ x ∈ X, a x) ^ 2 * (∑ x ∈ X, a x ^ 4) := by
  let s1 := ∑ x ∈ X, a x
  let s2 := ∑ x ∈ X, a x ^ 2
  let s3 := ∑ x ∈ X, a x ^ 3
  let s4 := ∑ x ∈ X, a x ^ 4
  have hs1 : 0 ≤ s1 := Finset.sum_nonneg ha
  have hs2 : 0 ≤ s2 := Finset.sum_nonneg (fun x _ => sq_nonneg (a x))
  have hs4 : 0 ≤ s4 := Finset.sum_nonneg (fun x _ => by positivity)
  by_cases h0 : s2 = 0
  · change s2 ^ 3 ≤ s1 ^ 2 * s4
    rw [h0]
    positivity
  · have hs2_pos : 0 < s2 := lt_of_le_of_ne hs2 (Ne.symm h0)
    have h13 : s2 ^ 2 ≤ s1 * s3 := by
      have hnn : 0 ≤ ∑ x ∈ X, ∑ y ∈ X, a x * a y * (a x - a y) ^ 2 :=
        Finset.sum_nonneg (fun x hx => Finset.sum_nonneg (fun y hy =>
          mul_nonneg (mul_nonneg (ha x hx) (ha y hy)) (sq_nonneg _)))
      have hid : ∑ x ∈ X, ∑ y ∈ X, a x * a y * (a x - a y) ^ 2 = 2 * (s1 * s3 - s2 ^ 2) := by
        have hexp : ∀ x y : α, a x * a y * (a x - a y) ^ 2 =
            a x ^ 3 * a y + a x * a y ^ 3 - 2 * (a x ^ 2 * a y ^ 2) := fun x y => by ring
        simp_rw [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        dsimp only [s1, s2, s3]
        ring
      linarith
    have h24 : s3 ^ 2 ≤ s2 * s4 := by
      have hnn : 0 ≤ ∑ x ∈ X, ∑ y ∈ X, (a x * a y ^ 2 - a y * a x ^ 2) ^ 2 :=
        Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => sq_nonneg _))
      have hid : ∑ x ∈ X, ∑ y ∈ X, (a x * a y ^ 2 - a y * a x ^ 2) ^ 2 = 2 * (s2 * s4 - s3 ^ 2) := by
        have hexp : ∀ x y : α, (a x * a y ^ 2 - a y * a x ^ 2) ^ 2 =
            a x ^ 2 * a y ^ 4 + a x ^ 4 * a y ^ 2 - 2 * (a x ^ 3 * a y ^ 3) := fun x y => by ring
        simp_rw [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
        dsimp only [s2, s3, s4]
        ring
      linarith
    have h4 : s2 ^ 3 * s2 ≤ (s1 ^ 2 * s4) * s2 := by
      calc s2 ^ 3 * s2
          = (s2 ^ 2) ^ 2 := by ring
        _ ≤ (s1 * s3) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h13 2
        _ = s1 ^ 2 * s3 ^ 2 := by ring
        _ ≤ s1 ^ 2 * (s2 * s4) := mul_le_mul_of_nonneg_left h24 (sq_nonneg _)
        _ = (s1 ^ 2 * s4) * s2 := by ring
    exact le_of_mul_le_mul_right h4 hs2_pos

lemma sum_filter_comm {α β : Type*} (A : Finset α) (B : Finset β) (R : α → β → Prop)
    [DecidablePred (fun p : α × β => R p.1 p.2)]
    [∀ a, DecidablePred (fun b => R a b)] [∀ b, DecidablePred (fun a => R a b)] :
    ∑ a ∈ A, (B.filter (fun b => R a b)).card = ∑ b ∈ B, (A.filter (fun a => R a b)).card := by
  simp_rw [Finset.card_filter]
  exact Finset.sum_comm

lemma flat_gain_le {k m q : ℕ} (v : Fin m → Vec k) (J : Finset (Fin m))
    (P : Finset (Fin k)) (pins : Vec k) (par : F2)
    (hindep : ∀ S : Finset (Fin m), 0 < S.card → S.card ≤ q + 1 → ∑ j ∈ S, v j ∉ orth (sliceL P))
    (tr : Vec k → (Fin q → F2))
    (hflat : ∀ x ∈ (Finset.univ : Finset (Vec k)).filter (fun x =>
      (∀ i ∈ P, x i = pins i) ∧ (∑ i : Fin k, x i) = par),
      ∃ p : Fin q → Vec k, ∀ y ∈ (Finset.univ : Finset (Vec k)).filter (fun x =>
        (∀ i ∈ P, x i = pins i) ∧ (∑ i : Fin k, x i) = par),
        tr y = tr x ↔ ∀ l : Fin q, dot y (p l) = dot x (p l))
    (dec : (Fin q → F2) → Fin m → F2) :
    let X := (Finset.univ : Finset (Vec k)).filter (fun x =>
      (∀ i ∈ P, x i = pins i) ∧ (∑ i : Fin k, x i) = par)
    2 * (∑ x ∈ X, (J.filter (fun j => dec (tr x) j = dot x (v j))).card) - X.card * J.card ≤
      q * X.card := by
  classical
  intro X
  suffices hmain : 2 * (∑ x ∈ X, (J.filter (fun j => dec (tr x) j = dot x (v j))).card) ≤
      X.card * J.card + q * X.card by omega
  let Fu : (Fin q → F2) → Finset (Vec k) := fun u => X.filter (fun x => tr x = u)
  have hsum_part : ∑ x ∈ X, (J.filter (fun j => dec (tr x) j = dot x (v j))).card =
      ∑ u : Fin q → F2, ∑ x ∈ Fu u, (J.filter (fun j => dec u j = dot x (v j))).card := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := tr) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun x hx => ?_))
    have htu : tr x = u := (Finset.mem_filter.mp hx).2
    simp only [htu]
  have hcard_part : X.card = ∑ u : Fin q → F2, (Fu u).card := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := tr) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  rw [hsum_part, hcard_part, Finset.mul_sum, Nat.mul_comm q, ← Nat.mul_add, Finset.sum_mul]
  refine Finset.sum_le_sum (fun u _ => ?_)
  by_cases hempty : (Fu u).Nonempty
  · obtain ⟨x1, hx1F⟩ := hempty
    have hx1X : x1 ∈ X := (Finset.mem_filter.mp hx1F).1
    have hx1tr : tr x1 = u := (Finset.mem_filter.mp hx1F).2
    obtain ⟨p, hp⟩ := hflat x1 hx1X
    let Pspan : Submodule F2 (Vec k) := Submodule.span F2 (Set.range p)
    let W : Submodule F2 (Vec k) := Pspan ⊔ orth (sliceL P)
    let K : Submodule F2 (Vec k) := orth W
    have hK_eq : K = orth Pspan ⊓ sliceL P := by
      dsimp only [K, W]
      rw [orth_sup, orth_orth]
    have hFu_closed : ∀ h ∈ K, ∀ y ∈ Fu u, y + h ∈ Fu u := by
      intro h hh y hyF
      have hyX : y ∈ X := (Finset.mem_filter.mp hyF).1
      have hytr : tr y = u := (Finset.mem_filter.mp hyF).2
      rw [hK_eq] at hh
      have hh_orthP : h ∈ orth Pspan := hh.1
      have hh_slice : h ∈ sliceL P := hh.2
      have hyhX : y + h ∈ X := by
        rw [mem_slice_iff_sub_mem P pins par hx1X]
        have hysub : y - x1 ∈ sliceL P := (mem_slice_iff_sub_mem P pins par hx1X).mp hyX
        have heq : y + h - x1 = (y - x1) + h := by abel
        rw [heq]
        exact (sliceL P).add_mem hysub hh_slice
      refine Finset.mem_filter.mpr ⟨hyhX, ?_⟩
      rw [← hx1tr, hp (y + h) hyhX]
      have hy_dots : ∀ l : Fin q, dot y (p l) = dot x1 (p l) :=
        (hp y hyX).mp (hytr.trans hx1tr.symm)
      intro l
      have hhl : dot h (p l) = 0 := by
        rw [dot_comm]
        exact hh_orthP (p l) (Submodule.subset_span ⟨l, rfl⟩)
      rw [dot_add_left, hhl, add_zero]
      exact hy_dots l
    let Jbad : Finset (Fin m) := J.filter (fun j => v j ∈ W)
    let Jgood : Finset (Fin m) := J.filter (fun j => v j ∉ W)
    have hbad_le : Jbad.card ≤ q := by
      by_contra hgt
      push Not at hgt
      obtain ⟨T, hTJ, hTcard⟩ := Finset.exists_subset_card_eq hgt
      have hdecomp : ∀ j : T, ∃ w : Pspan, ∃ z : orth (sliceL P), (w : Vec k) + (z : Vec k) = v j.1 := by
        intro j
        have hjW : v j.1 ∈ W := (Finset.mem_filter.mp (hTJ j.2)).2
        rcases Submodule.mem_sup.mp hjW with ⟨w, hw, z, hz, heq⟩
        exact ⟨⟨w, hw⟩, ⟨z, hz⟩, heq⟩
      let wSub : T → Pspan := fun j => (hdecomp j).choose
      let zSub : T → orth (sliceL P) := fun j => (hdecomp j).choose_spec.choose
      have hwz : ∀ j : T, (wSub j : Vec k) + (zSub j : Vec k) = v j.1 :=
        fun j => (hdecomp j).choose_spec.choose_spec
      have hnot_li : ¬ LinearIndependent F2 wSub := by
        intro hli
        have hcard_le := hli.fintype_card_le_finrank
        have hfin_le : Module.finrank F2 Pspan ≤ q := finrank_span_range_le p
        have hTfin : Fintype.card T = q + 1 := by simp [hTcard]
        omega
      rw [Fintype.linearIndependent_iff] at hnot_li
      push Not at hnot_li
      obtain ⟨c, hc_sum, j0, hj0⟩ := hnot_li
      let S : Finset (Fin m) := (Finset.univ.filter (fun j : T => c j = 1)).map (Function.Embedding.subtype _)
      have hS_pos : 0 < S.card := by
        refine Finset.card_pos.mpr ⟨j0.1, Finset.mem_map.mpr ⟨j0, Finset.mem_filter.mpr ⟨Finset.mem_univ j0, ?_⟩, rfl⟩⟩
        rcases zmod2_eq_zero_or_one (c j0) with h0 | h1
        · exact absurd h0 hj0
        · exact h1
      have hS_le : S.card ≤ q + 1 := by
        rw [Finset.card_map]
        calc (Finset.univ.filter (fun j : T => c j = 1)).card
            ≤ (Finset.univ : Finset T).card := Finset.card_filter_le _ _
          _ = q + 1 := by simp [hTcard]
      have hsum_v : ∑ j ∈ S, v j = ∑ j : T, c j • v j.1 := by
        rw [Finset.sum_map]
        symm
        rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter (fun j : T => c j = 1)))]
        · refine Finset.sum_congr rfl (fun j hj => ?_)
          have hcj : c j = 1 := (Finset.mem_filter.mp hj).2
          simp [hcj]
        · intro j _ hj
          have hcj : c j ≠ 1 := fun h => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩)
          rcases zmod2_eq_zero_or_one (c j) with h0 | h1
          · simp [h0]
          · exact absurd h1 hcj
      have hsum_w : ∑ j : T, c j • (wSub j : Vec k) = 0 := by
        have hcoe := congrArg (Subtype.val : Pspan → Vec k) hc_sum
        simpa [Submodule.coe_sum, Submodule.coe_smul] using hcoe
      have hsum_in_orth : ∑ j ∈ S, v j ∈ orth (sliceL P) := by
        rw [hsum_v]
        have hsplit : ∑ j : T, c j • v j.1 =
            (∑ j : T, c j • (wSub j : Vec k)) + ∑ j : T, c j • (zSub j : Vec k) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [← hwz j, smul_add]
        rw [hsplit, hsum_w, zero_add]
        exact (orth (sliceL P)).sum_mem (fun j _ => (orth (sliceL P)).smul_mem (c j) (zSub j).2)
      exact hindep S hS_pos hS_le hsum_in_orth
    have hswap : ∑ x ∈ Fu u, (J.filter (fun j => dec u j = dot x (v j))).card =
        ∑ j ∈ J, ((Fu u).filter (fun x => dec u j = dot x (v j))).card :=
      sum_filter_comm (Fu u) J (fun x j => dec u j = dot x (v j))
    rw [hswap, Finset.mul_sum]
    have hJsplit : Jbad ∪ Jgood = J := by
      ext j
      simp only [Jbad, Jgood, Finset.mem_union, Finset.mem_filter]
      tauto
    have hJdisj : Disjoint Jbad Jgood := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    conv_lhs => rw [← hJsplit]
    rw [Finset.sum_union hJdisj]
    have hsum_good : ∑ j ∈ Jgood, 2 * ((Fu u).filter (fun x => dec u j = dot x (v j))).card =
        Jgood.card * (Fu u).card := by
      have hterm : ∀ j ∈ Jgood, 2 * ((Fu u).filter (fun x => dec u j = dot x (v j))).card = (Fu u).card := by
        intro j hj
        have hnotW : v j ∉ W := (Finset.mem_filter.mp hj).2
        have hnotOK : v j ∉ orth K := by
          dsimp only [K]; rwa [orth_orth]
        have hex : ∃ h ∈ K, dot h (v j) ≠ 0 := by
          by_contra hall
          push Not at hall
          exact hnotOK hall
        obtain ⟨h, hhK, hhdot⟩ := hex
        have hhdot1 : dot h (v j) = 1 := by
          rcases zmod2_eq_zero_or_one (dot h (v j)) with h0 | h1
          · exact absurd h0 hhdot
          · exact h1
        exact card_filter_dot_eq_half (Fu u) h (v j) (hFu_closed h hhK) hhdot1 (dec u j)
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul]
    have hsum_bad : ∑ j ∈ Jbad, 2 * ((Fu u).filter (fun x => dec u j = dot x (v j))).card ≤
        2 * Jbad.card * (Fu u).card := by
      calc ∑ j ∈ Jbad, 2 * ((Fu u).filter (fun x => dec u j = dot x (v j))).card
          ≤ ∑ _j ∈ Jbad, 2 * (Fu u).card :=
            Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left 2 (Finset.card_filter_le _ _))
        _ = Jbad.card * (2 * (Fu u).card) := by rw [Finset.sum_const, smul_eq_mul]
        _ = 2 * Jbad.card * (Fu u).card := by ring
    have hJcard : Jbad.card + Jgood.card = J.card := by
      rw [← Finset.card_union_of_disjoint hJdisj, hJsplit]
    calc ∑ j ∈ Jbad, 2 * ((Fu u).filter (fun x => dec u j = dot x (v j))).card +
          ∑ j ∈ Jgood, 2 * ((Fu u).filter (fun x => dec u j = dot x (v j))).card
        ≤ 2 * Jbad.card * (Fu u).card + Jgood.card * (Fu u).card := by
          rw [hsum_good]; exact Nat.add_le_add_right hsum_bad _
      _ = (Fu u).card * (Jbad.card + Jgood.card + Jbad.card) := by ring
      _ ≤ (Fu u).card * (J.card + q) := by
          rw [hJcard]; exact Nat.mul_le_mul_left _ (Nat.add_le_add_left hbad_le _)
  · rw [Finset.not_nonempty_iff_eq_empty] at hempty
    simp [hempty]

lemma exists_js_gain_eq {k m q : ℕ} (v : Fin m → Vec k) (J : Finset (Fin m))
    (P : Finset (Fin k)) (pins : Vec k) (par : F2)
    (hqJ : q ≤ J.card)
    (h1 : ∀ j : Fin m, v j ∉ orth (sliceL P))
    (hXne : ((Finset.univ : Finset (Vec k)).filter (fun x =>
      (∀ i ∈ P, x i = pins i) ∧ (∑ i : Fin k, x i) = par)).Nonempty) :
    let X := (Finset.univ : Finset (Vec k)).filter (fun x =>
      (∀ i ∈ P, x i = pins i) ∧ (∑ i : Fin k, x i) = par)
    ∃ js : Fin q ↪ Fin m, (∀ i, js i ∈ J) ∧ ∃ dec : (Fin q → F2) → Fin m → F2,
      2 * (∑ x ∈ X, (J.filter (fun j => dec (fun i => dot x (v (js i))) j = dot x (v j))).card) -
        X.card * J.card = q * X.card := by
  classical
  intro X
  obtain ⟨R, hRJ, hRcard⟩ := Finset.exists_subset_card_eq hqJ
  let e : Fin q ≃ R := (R.equivFinOfCardEq hRcard).symm
  let js : Fin q ↪ Fin m := e.toEmbedding.trans (Function.Embedding.subtype _)
  have hjsJ : ∀ i : Fin q, js i ∈ J := fun i => hRJ (e i).2
  let dec : (Fin q → F2) → Fin m → F2 := fun u j =>
    if h : ∃ i : Fin q, js i = j then u h.choose else 0
  refine ⟨js, hjsJ, dec, ?_⟩
  obtain ⟨x0, hx0⟩ := hXne
  have hXclosed : ∀ h ∈ sliceL P, ∀ y ∈ X, y + h ∈ X := by
    intro h hh y hy
    rw [mem_slice_iff_sub_mem P pins par hx0] at hy ⊢
    have heq : y + h - x0 = (y - x0) + h := by abel
    rw [heq]
    exact (sliceL P).add_mem hy hh
  have hswap : ∑ x ∈ X, (J.filter (fun j => dec (fun i => dot x (v (js i))) j = dot x (v j))).card =
      ∑ j ∈ J, (X.filter (fun x => dec (fun i => dot x (v (js i))) j = dot x (v j))).card :=
    sum_filter_comm X J (fun x j => dec (fun i => dot x (v (js i))) j = dot x (v j))
  have htot : 2 * (∑ x ∈ X, (J.filter (fun j => dec (fun i => dot x (v (js i))) j = dot x (v j))).card) =
      X.card * J.card + q * X.card := by
    rw [hswap, Finset.mul_sum, ← Finset.sum_sdiff hRJ]
    have hsumR : ∑ j ∈ R, 2 * (X.filter (fun x => dec (fun i => dot x (v (js i))) j = dot x (v j))).card =
        2 * q * X.card := by
      have hterm : ∀ j ∈ R, 2 * (X.filter (fun x => dec (fun i => dot x (v (js i))) j = dot x (v j))).card =
          2 * X.card := by
        intro j hj
        let i0 : Fin q := e.symm ⟨j, hj⟩
        have hi0 : js i0 = j := by
          change (e (e.symm ⟨j, hj⟩)).1 = j
          simp
        have hpred : ∀ x : Vec k, dec (fun i => dot x (v (js i))) j = dot x (v j) := by
          intro x
          have hex : ∃ i : Fin q, js i = j := ⟨i0, hi0⟩
          simp only [dec, hex, ↓reduceDIte]
          have hch : hex.choose = i0 := js.injective (hex.choose_spec.trans hi0.symm)
          rw [hch, hi0]
        simp [hpred]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, hRcard]
      ring
    have hsumRest : ∑ j ∈ J \ R, 2 * (X.filter (fun x => dec (fun i => dot x (v (js i))) j = dot x (v j))).card =
        (J.card - q) * X.card := by
      have hterm : ∀ j ∈ J \ R, 2 * (X.filter (fun x => dec (fun i => dot x (v (js i))) j = dot x (v j))).card =
          X.card := by
        intro j hj
        have hnotR : j ∉ R := (Finset.mem_sdiff.mp hj).2
        have hnotEx : ¬ ∃ i : Fin q, js i = j := by
          rintro ⟨i, rfl⟩
          exact hnotR (e i).2
        have hpred : ∀ x : Vec k, dec (fun i => dot x (v (js i))) j = 0 := by
          intro x
          simp only [dec, hnotEx, ↓reduceDIte]
        simp_rw [hpred]
        have hex : ∃ h ∈ sliceL P, dot h (v j) ≠ 0 := by
          by_contra hall
          push Not at hall
          exact h1 j hall
        obtain ⟨h, hh, hhdot⟩ := hex
        have hhdot1 : dot h (v j) = 1 := by
          rcases zmod2_eq_zero_or_one (dot h (v j)) with h0 | h1'
          · exact absurd h0 hhdot
          · exact h1'
        exact card_filter_dot_eq_half X h (v j) (hXclosed h hh) hhdot1 0
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, Finset.card_sdiff,
        Finset.inter_eq_left.mpr hRJ, hRcard]
    rw [hsumR, hsumRest]
    have hJsplit : J.card = (J.card - q) + q := (Nat.sub_add_cancel hqJ).symm
    conv_rhs => rw [hJsplit]
    ring
  rw [htot]
  omega

lemma maj_gain_gt {k m q : ℕ} (v : Fin m → Vec k) (J : Finset (Fin m))
    (P : Finset (Fin k)) (pins : Vec k) (par : F2)
    (hk_pos : 0 < k) (hq_sq : q * q ≤ k) (hJ_lo : 256 * k ≤ J.card)
    (h4 : ∀ S : Finset (Fin m), 0 < S.card → S.card ≤ 4 → ∑ j ∈ S, v j ∉ orth (sliceL P))
    (hXne : ((Finset.univ : Finset (Vec k)).filter (fun x =>
      (∀ i ∈ P, x i = pins i) ∧ (∑ i : Fin k, x i) = par)).Nonempty) :
    let X := (Finset.univ : Finset (Vec k)).filter (fun x =>
      (∀ i ∈ P, x i = pins i) ∧ (∑ i : Fin k, x i) = par)
    let maj := fun x : Vec k =>
      if J.card ≤ 2 * (J.filter (fun j => dot x (v j) = 1)).card then (1 : F2) else 0
    9 * q * X.card <
      2 * (∑ x ∈ X, (J.filter (fun j => maj x = dot x (v j))).card) - X.card * J.card := by
  classical
  intro X maj
  obtain ⟨x0, hx0⟩ := hXne
  have hXpos : 0 < X.card := Finset.card_pos.mpr ⟨x0, hx0⟩
  have hXclosed : ∀ h ∈ sliceL P, ∀ y ∈ X, y + h ∈ X := by
    intro h hh y hy
    rw [mem_slice_iff_sub_mem P pins par hx0] at hy ⊢
    have heq : y + h - x0 = (y - x0) + h := by abel
    rw [heq]
    exact (sliceL P).add_mem hy hh
  have hsum_orth : ∀ w : Vec k, w ∉ orth (sliceL P) → ∑ x ∈ X, sgn (dot x w) = 0 := by
    intro w hw
    have hex : ∃ h ∈ sliceL P, dot h w ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hw hall
    obtain ⟨h, hh, hhdot⟩ := hex
    have hhdot1 : dot h w = 1 := by
      rcases zmod2_eq_zero_or_one (dot h w) with h0 | h1
      · exact absurd h0 hhdot
      · exact h1
    exact sum_sgn_eq_zero X h w (hXclosed h hh) hhdot1
  let Sx : Vec k → ℤ := fun x => ∑ j ∈ J, sgn (dot x (v j))
  have hmaj_row : ∀ x : Vec k,
      2 * ((J.filter (fun j => maj x = dot x (v j))).card : ℤ) - (J.card : ℤ) = |Sx x| := by
    intro x
    let J1 := J.filter (fun j => dot x (v j) = 1)
    let J0 := J.filter (fun j => dot x (v j) = 0)
    have hdisj : Disjoint J1 J0 := by
      rw [Finset.disjoint_left]
      intro j h1 h0
      have e1 := (Finset.mem_filter.mp h1).2
      have e0 := (Finset.mem_filter.mp h0).2
      rw [e1] at e0
      exact absurd e0 (by decide)
    have hunion : J1 ∪ J0 = J := by
      ext j
      simp only [J1, J0, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        rcases zmod2_eq_zero_or_one (dot x (v j)) with h0 | h1
        · right; exact ⟨h, h0⟩
        · left; exact ⟨h, h1⟩
    have hcards : J1.card + J0.card = J.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hSx : Sx x = (J0.card : ℤ) - (J1.card : ℤ) := by
      dsimp only [Sx]
      rw [← hunion, Finset.sum_union hdisj]
      have s1 : ∑ j ∈ J1, sgn (dot x (v j)) = -(J1.card : ℤ) := by
        have ht : ∀ j ∈ J1, sgn (dot x (v j)) = -1 := fun j hj => by
          rw [(Finset.mem_filter.mp hj).2]; rfl
        rw [Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul]; ring
      have s0 : ∑ j ∈ J0, sgn (dot x (v j)) = (J0.card : ℤ) := by
        have ht : ∀ j ∈ J0, sgn (dot x (v j)) = 1 := fun j hj => by
          rw [(Finset.mem_filter.mp hj).2]; rfl
        rw [Finset.sum_congr rfl ht, Finset.sum_const, nsmul_eq_mul]; ring
      rw [s1, s0]; ring
    by_cases hcond : J.card ≤ 2 * J1.card
    · have hmaj1 : maj x = 1 := by simp [maj, J1, hcond]
      have hfilt : J.filter (fun j => maj x = dot x (v j)) = J1 := by
        ext j
        simp only [Finset.mem_filter, J1, hmaj1, eq_comm]
      rw [hfilt, hSx]
      have hle0 : (J0.card : ℤ) - (J1.card : ℤ) ≤ 0 := by omega
      rw [abs_of_nonpos hle0]
      omega
    · have hmaj0 : maj x = 0 := by simp [maj, J1, hcond]
      have hfilt : J.filter (fun j => maj x = dot x (v j)) = J0 := by
        ext j
        simp only [Finset.mem_filter, J0, hmaj0, eq_comm]
      rw [hfilt, hSx]
      have hge0 : 0 ≤ (J0.card : ℤ) - (J1.card : ℤ) := by omega
      rw [abs_of_nonneg hge0]
      omega
  have hgain_int : 2 * ((∑ x ∈ X, (J.filter (fun j => maj x = dot x (v j))).card : ℕ) : ℤ) -
      (X.card : ℤ) * (J.card : ℤ) = ∑ x ∈ X, |Sx x| := by
    push_cast
    rw [Finset.mul_sum]
    have hXsub : (X.card : ℤ) * (J.card : ℤ) = ∑ _x ∈ X, (J.card : ℤ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hXsub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun x _ => hmaj_row x)
  have hpair_not_orth : ∀ j1 j2 : Fin m, j1 ≠ j2 → v j1 + v j2 ∉ orth (sliceL P) := by
    intro j1 j2 hne
    have hcard2 : ({j1, j2} : Finset (Fin m)).card = 2 := Finset.card_pair hne
    have hsum2 : ∑ j ∈ ({j1, j2} : Finset (Fin m)), v j = v j1 + v j2 := Finset.sum_pair hne
    rw [← hsum2]
    exact h4 {j1, j2} (by omega) (by omega)
  have hmom2 : ∑ x ∈ X, |Sx x| ^ 2 = (J.card : ℤ) * (X.card : ℤ) := by
    have hsq_eq : ∀ x : Vec k, |Sx x| ^ 2 = ∑ j1 ∈ J, ∑ j2 ∈ J, sgn (dot x (v j1 + v j2)) := by
      intro x
      rw [sq_abs, sq]
      dsimp only [Sx]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j1 _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j2 _ => ?_)
      rw [dot_add_right, sgn_add]
    simp_rw [hsq_eq]
    rw [Finset.sum_comm]
    have hinner : ∀ j1 ∈ J, ∑ x ∈ X, ∑ j2 ∈ J, sgn (dot x (v j1 + v j2)) = (X.card : ℤ) := by
      intro j1 hj1
      rw [Finset.sum_comm]
      rw [Finset.sum_eq_single j1]
      · simp [vec_add_self, dot_zero_right, sgn_zero]
      · intro j2 _ hne
        exact hsum_orth (v j1 + v j2) (hpair_not_orth j1 j2 (Ne.symm hne))
      · intro hnot; exact absurd hj1 hnot
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]
  let good4 : Fin m → Fin m → Fin m → Fin m → Prop := fun j1 j2 j3 j4 =>
    (j1 = j2 ∧ j3 = j4) ∨ (j1 = j3 ∧ j2 = j4) ∨ (j1 = j4 ∧ j2 = j3)
  have hquad_not_orth : ∀ j1 j2 j3 j4 : Fin m, ¬ good4 j1 j2 j3 j4 →
      v j1 + v j2 + v j3 + v j4 ∉ orth (sliceL P) := by
    intro j1 j2 j3 j4 hng
    have h1234 : ∀ a b : Vec k, a + a + b = b := fun a b => by rw [vec_add_self, zero_add]
    by_cases e12 : j1 = j2
    · have e34 : j3 ≠ j4 := fun h => hng (Or.inl ⟨e12, h⟩)
      rw [e12, vec_add_self, zero_add]
      exact hpair_not_orth j3 j4 e34
    · by_cases e13 : j1 = j3
      · have e24 : j2 ≠ j4 := fun h => hng (Or.inr (Or.inl ⟨e13, h⟩))
        have heq : v j1 + v j2 + v j3 + v j4 = v j2 + v j4 := by
          rw [e13]; calc v j3 + v j2 + v j3 + v j4 = (v j3 + v j3) + (v j2 + v j4) := by abel
            _ = v j2 + v j4 := by rw [vec_add_self, zero_add]
        rw [heq]; exact hpair_not_orth j2 j4 e24
      · by_cases e14 : j1 = j4
        · have e23 : j2 ≠ j3 := fun h => hng (Or.inr (Or.inr ⟨e14, h⟩))
          have heq : v j1 + v j2 + v j3 + v j4 = v j2 + v j3 := by
            rw [e14]; calc v j4 + v j2 + v j3 + v j4 = (v j4 + v j4) + (v j2 + v j3) := by abel
              _ = v j2 + v j3 := by rw [vec_add_self, zero_add]
          rw [heq]; exact hpair_not_orth j2 j3 e23
        · by_cases e23 : j2 = j3
          · have heq : v j1 + v j2 + v j3 + v j4 = v j1 + v j4 := by
              rw [e23]; calc v j1 + v j3 + v j3 + v j4 = v j1 + (v j3 + v j3) + v j4 := by abel
                _ = v j1 + v j4 := by rw [vec_add_self, add_zero]
            rw [heq]; exact hpair_not_orth j1 j4 e14
          · by_cases e24 : j2 = j4
            · have heq : v j1 + v j2 + v j3 + v j4 = v j1 + v j3 := by
                rw [e24]; calc v j1 + v j4 + v j3 + v j4 = (v j4 + v j4) + (v j1 + v j3) := by abel
                  _ = v j1 + v j3 := by rw [vec_add_self, zero_add]
              rw [heq]; exact hpair_not_orth j1 j3 e13
            · by_cases e34 : j3 = j4
              · have heq : v j1 + v j2 + v j3 + v j4 = v j1 + v j2 := by
                  rw [e34]; calc v j1 + v j2 + v j4 + v j4 = v j1 + v j2 + (v j4 + v j4) := by abel
                    _ = v j1 + v j2 := by rw [vec_add_self, add_zero]
                rw [heq]; exact hpair_not_orth j1 j2 e12
              · let Q : Finset (Fin m) := {j1, j2, j3, j4}
                have hQcard : Q.card = 4 := by
                  simp only [Q]
                  rw [Finset.card_insert_of_notMem (by simp [e12, e13, e14]),
                      Finset.card_insert_of_notMem (by simp [e23, e24]),
                      Finset.card_pair e34]
                have hQsum : ∑ j ∈ Q, v j = v j1 + v j2 + v j3 + v j4 := by
                  simp only [Q]
                  rw [Finset.sum_insert (by simp [e12, e13, e14]),
                      Finset.sum_insert (by simp [e23, e24]),
                      Finset.sum_pair e34]
                  abel
                rw [← hQsum]
                exact h4 Q (by omega) (by omega)
  have hmom4 : ∑ x ∈ X, |Sx x| ^ 4 ≤ 3 * (J.card : ℤ) ^ 2 * (X.card : ℤ) := by
    have h4_eq : ∀ x : Vec k, |Sx x| ^ 4 =
        ∑ j1 ∈ J, ∑ j2 ∈ J, ∑ j3 ∈ J, ∑ j4 ∈ J, sgn (dot x (v j1 + v j2 + v j3 + v j4)) := by
      intro x
      have h2 : Sx x * Sx x = ∑ j1 ∈ J, ∑ j2 ∈ J, sgn (dot x (v j1 + v j2)) := by
        dsimp only [Sx]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun j1 _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j2 _ => ?_)
        rw [dot_add_right, sgn_add]
      have hp4 : |Sx x| ^ 4 = (Sx x * Sx x) * (Sx x * Sx x) := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]; ring
      rw [hp4, h2, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j1 _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j2 _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j3 _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j4 _ => ?_)
      rw [← sgn_add, ← dot_add_right, ← add_assoc]
    simp_rw [h4_eq]
    have hswap4 : ∑ x ∈ X, ∑ j1 ∈ J, ∑ j2 ∈ J, ∑ j3 ∈ J, ∑ j4 ∈ J,
          sgn (dot x (v j1 + v j2 + v j3 + v j4)) =
        ∑ j1 ∈ J, ∑ j2 ∈ J, ∑ j3 ∈ J, ∑ j4 ∈ J,
          ∑ x ∈ X, sgn (dot x (v j1 + v j2 + v j3 + v j4)) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j1 _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j2 _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j3 _ => Finset.sum_comm)
    rw [hswap4]
    have hterm_le : ∀ j1 j2 j3 j4 : Fin m,
        ∑ x ∈ X, sgn (dot x (v j1 + v j2 + v j3 + v j4)) ≤
          (if j1 = j2 ∧ j3 = j4 then (X.card : ℤ) else 0) +
          (if j1 = j3 ∧ j2 = j4 then (X.card : ℤ) else 0) +
          (if j1 = j4 ∧ j2 = j3 then (X.card : ℤ) else 0) := by
      intro j1 j2 j3 j4
      by_cases hg : good4 j1 j2 j3 j4
      · have hleX : ∑ x ∈ X, sgn (dot x (v j1 + v j2 + v j3 + v j4)) ≤ (X.card : ℤ) := by
          calc ∑ x ∈ X, sgn (dot x (v j1 + v j2 + v j3 + v j4))
              ≤ ∑ _x ∈ X, (1 : ℤ) := Finset.sum_le_sum (fun x _ => sgn_le_one _)
            _ = (X.card : ℤ) := by simp
        have hnn : (0 : ℤ) ≤ (X.card : ℤ) := by positivity
        refine hleX.trans ?_
        split_ifs <;> first | linarith | exact absurd hg (by tauto)
      · rw [hsum_orth _ (hquad_not_orth j1 j2 j3 j4 hg)]
        have hnn : (0 : ℤ) ≤ (X.card : ℤ) := by positivity
        split_ifs <;> linarith
    have hsum1 : ∑ j1 ∈ J, ∑ j2 ∈ J, ∑ j3 ∈ J, ∑ j4 ∈ J,
        (if j1 = j2 ∧ j3 = j4 then (X.card : ℤ) else 0) = (J.card : ℤ) ^ 2 * (X.card : ℤ) := by
      have h1 : ∀ j1 ∈ J, ∑ j2 ∈ J, ∑ j3 ∈ J, ∑ j4 ∈ J,
          (if j1 = j2 ∧ j3 = j4 then (X.card : ℤ) else 0) = (J.card : ℤ) * (X.card : ℤ) := by
        intro j1 hj1
        rw [Finset.sum_eq_single j1]
        · have h2 : ∀ j3 ∈ J, ∑ j4 ∈ J, (if j1 = j1 ∧ j3 = j4 then (X.card : ℤ) else 0) = (X.card : ℤ) := by
            intro j3 hj3
            rw [Finset.sum_eq_single j3]
            · simp
            · intro j4 _ hne; simp [hne.symm]
            · intro hn; exact absurd hj3 hn
          rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]
        · intro j2 _ hne
          simp [hne.symm]
        · intro hn; exact absurd hj1 hn
      rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
      ring
    have hsum2 : ∑ j1 ∈ J, ∑ j2 ∈ J, ∑ j3 ∈ J, ∑ j4 ∈ J,
        (if j1 = j3 ∧ j2 = j4 then (X.card : ℤ) else 0) = (J.card : ℤ) ^ 2 * (X.card : ℤ) := by
      have h1 : ∀ j1 ∈ J, ∀ j2 ∈ J, ∑ j3 ∈ J, ∑ j4 ∈ J,
          (if j1 = j3 ∧ j2 = j4 then (X.card : ℤ) else 0) = (X.card : ℤ) := by
        intro j1 hj1 j2 hj2
        rw [Finset.sum_eq_single j1]
        · rw [Finset.sum_eq_single j2]
          · simp
          · intro j4 _ hne; simp [hne.symm]
          · intro hn; exact absurd hj2 hn
        · intro j3 _ hne; simp [hne.symm]
        · intro hn; exact absurd hj1 hn
      calc ∑ j1 ∈ J, ∑ j2 ∈ J, ∑ j3 ∈ J, ∑ j4 ∈ J,
            (if j1 = j3 ∧ j2 = j4 then (X.card : ℤ) else 0)
          = ∑ j1 ∈ J, ∑ _j2 ∈ J, (X.card : ℤ) :=
            Finset.sum_congr rfl (fun j1 hj1 => Finset.sum_congr rfl (fun j2 hj2 => h1 j1 hj1 j2 hj2))
        _ = (J.card : ℤ) ^ 2 * (X.card : ℤ) := by
            simp [Finset.sum_const]; ring
    have hsum3 : ∑ j1 ∈ J, ∑ j2 ∈ J, ∑ j3 ∈ J, ∑ j4 ∈ J,
        (if j1 = j4 ∧ j2 = j3 then (X.card : ℤ) else 0) = (J.card : ℤ) ^ 2 * (X.card : ℤ) := by
      have h1 : ∀ j1 ∈ J, ∀ j2 ∈ J, ∑ j3 ∈ J, ∑ j4 ∈ J,
          (if j1 = j4 ∧ j2 = j3 then (X.card : ℤ) else 0) = (X.card : ℤ) := by
        intro j1 hj1 j2 hj2
        rw [Finset.sum_eq_single j2]
        · rw [Finset.sum_eq_single j1]
          · simp
          · intro j4 _ hne; simp [hne.symm]
          · intro hn; exact absurd hj1 hn
        · intro j3 _ hne; simp [hne.symm]
        · intro hn; exact absurd hj2 hn
      calc ∑ j1 ∈ J, ∑ j2 ∈ J, ∑ j3 ∈ J, ∑ j4 ∈ J,
            (if j1 = j4 ∧ j2 = j3 then (X.card : ℤ) else 0)
          = ∑ j1 ∈ J, ∑ _j2 ∈ J, (X.card : ℤ) :=
            Finset.sum_congr rfl (fun j1 hj1 => Finset.sum_congr rfl (fun j2 hj2 => h1 j1 hj1 j2 hj2))
        _ = (J.card : ℤ) ^ 2 * (X.card : ℤ) := by
            simp [Finset.sum_const]; ring
    calc ∑ j1 ∈ J, ∑ j2 ∈ J, ∑ j3 ∈ J, ∑ j4 ∈ J, ∑ x ∈ X, sgn (dot x (v j1 + v j2 + v j3 + v j4))
        ≤ ∑ j1 ∈ J, ∑ j2 ∈ J, ∑ j3 ∈ J, ∑ j4 ∈ J,
            ((if j1 = j2 ∧ j3 = j4 then (X.card : ℤ) else 0) +
             (if j1 = j3 ∧ j2 = j4 then (X.card : ℤ) else 0) +
             (if j1 = j4 ∧ j2 = j3 then (X.card : ℤ) else 0)) :=
          Finset.sum_le_sum (fun j1 _ => Finset.sum_le_sum (fun j2 _ =>
            Finset.sum_le_sum (fun j3 _ => Finset.sum_le_sum (fun j4 _ => hterm_le j1 j2 j3 j4))))
      _ = (∑ j1 ∈ J, ∑ j2 ∈ J, ∑ j3 ∈ J, ∑ j4 ∈ J, (if j1 = j2 ∧ j3 = j4 then (X.card : ℤ) else 0)) +
          (∑ j1 ∈ J, ∑ j2 ∈ J, ∑ j3 ∈ J, ∑ j4 ∈ J, (if j1 = j3 ∧ j2 = j4 then (X.card : ℤ) else 0)) +
          (∑ j1 ∈ J, ∑ j2 ∈ J, ∑ j3 ∈ J, ∑ j4 ∈ J, (if j1 = j4 ∧ j2 = j3 then (X.card : ℤ) else 0)) := by
          simp_rw [Finset.sum_add_distrib]
      _ = 3 * (J.card : ℤ) ^ 2 * (X.card : ℤ) := by rw [hsum1, hsum2, hsum3]; ring
  have hhold := holder_1_2_4 X (fun x => |Sx x|) (fun x _ => abs_nonneg _)
  rw [hmom2] at hhold
  have hS1_nn : 0 ≤ ∑ x ∈ X, |Sx x| := Finset.sum_nonneg (fun x _ => abs_nonneg _)
  have hstep : ((J.card : ℤ) * (X.card : ℤ)) ^ 3 ≤
      (∑ x ∈ X, |Sx x|) ^ 2 * (3 * (J.card : ℤ) ^ 2 * (X.card : ℤ)) :=
    hhold.trans (mul_le_mul_of_nonneg_left hmom4 (sq_nonneg _))
  have hJpos : 0 < J.card := by omega
  have hJposZ : (0 : ℤ) < (J.card : ℤ) := by exact_mod_cast hJpos
  have hXposZ : (0 : ℤ) < (X.card : ℤ) := by exact_mod_cast hXpos
  have hJX_pos : (0 : ℤ) < (J.card : ℤ) ^ 2 * (X.card : ℤ) := by positivity
  have hlb : (J.card : ℤ) * (X.card : ℤ) ^ 2 ≤ 3 * (∑ x ∈ X, |Sx x|) ^ 2 := by
    have hmul : ((J.card : ℤ) * (X.card : ℤ) ^ 2) * ((J.card : ℤ) ^ 2 * (X.card : ℤ)) ≤
        (3 * (∑ x ∈ X, |Sx x|) ^ 2) * ((J.card : ℤ) ^ 2 * (X.card : ℤ)) := by
      calc ((J.card : ℤ) * (X.card : ℤ) ^ 2) * ((J.card : ℤ) ^ 2 * (X.card : ℤ))
          = ((J.card : ℤ) * (X.card : ℤ)) ^ 3 := by ring
        _ ≤ (∑ x ∈ X, |Sx x|) ^ 2 * (3 * (J.card : ℤ) ^ 2 * (X.card : ℤ)) := hstep
        _ = (3 * (∑ x ∈ X, |Sx x|) ^ 2) * ((J.card : ℤ) ^ 2 * (X.card : ℤ)) := by ring
    exact le_of_mul_le_mul_right hmul hJX_pos
  have hstrict_sq : ((9 * q * X.card : ℕ) : ℤ) ^ 2 < (∑ x ∈ X, |Sx x|) ^ 2 := by
    have hqZ : (q : ℤ) ^ 2 ≤ (k : ℤ) := by
      have : (q : ℤ) * (q : ℤ) ≤ (k : ℤ) := by exact_mod_cast hq_sq
      nlinarith
    have hJZ : 256 * (k : ℤ) ≤ (J.card : ℤ) := by exact_mod_cast hJ_lo
    have hX2_pos : (0 : ℤ) < (X.card : ℤ) ^ 2 := by positivity
    have hk_Z : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk_pos
    have h3 : 3 * ((9 * q * X.card : ℕ) : ℤ) ^ 2 < 3 * (∑ x ∈ X, |Sx x|) ^ 2 := by
      push_cast
      calc 3 * (9 * (q : ℤ) * (X.card : ℤ)) ^ 2
          = 243 * (q : ℤ) ^ 2 * (X.card : ℤ) ^ 2 := by ring
        _ ≤ 243 * (k : ℤ) * (X.card : ℤ) ^ 2 := by nlinarith
        _ < 256 * (k : ℤ) * (X.card : ℤ) ^ 2 := by nlinarith
        _ ≤ (J.card : ℤ) * (X.card : ℤ) ^ 2 := by nlinarith
        _ ≤ 3 * (∑ x ∈ X, |Sx x|) ^ 2 := hlb
    linarith
  have hstrict : ((9 * q * X.card : ℕ) : ℤ) < ∑ x ∈ X, |Sx x| := by
    by_contra hle
    push Not at hle
    have hsq := pow_le_pow_left₀ hS1_nn hle 2
    linarith
  omega

end PEqualNP.Outside.L_meta_27812_aux

open PEqualNP.Outside.L_meta_27812_aux in
theorem PEqualNP.Outside.L_meta_27812 : ∀ k : ℕ, 4096 ≤ k →
  let F := ZMod 2
  let V := Fin k → F
  let q := Nat.sqrt k
  let U := Fin q → F
  let dot := fun (x y : V) => ∑ i : Fin k, x i * y i
  ∃ t : ℕ, let m := 2^t
    512*k ≤ m ∧ m < 1024*k ∧
    ∃ (s : Fin (2^(k+m-1))) (C : PEqualNP.CircuitLowerBounds.Circuit),
      let v := fun (j : Fin m) (i : Fin k) =>
        if s.val.testBit (j.val+i.val) then (1 : F) else 0
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+t) C ∧
      C.output < k+t+C.size ∧ C.size ≤ 3080*k+3*k*t ∧
      (∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
        (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))) ∧
      (∀ (row : Fin k → Bool) (j : Fin m),
        C.eval (List.ofFn row ++ List.ofFn (fun z : Fin t => j.val.testBit z.val)) =
          decide (dot (fun i => if row i then 1 else 0) (v j) = 1)) ∧
      ∀ (J : Finset (Fin m)), m ≤ 2*J.card →
      ∀ (P : Finset (Fin k)), P.card ≤ k/32 → ∀ (pins : V) (par : F),
        let X := (Finset.univ : Finset V).filter (fun x =>
          (∀ i ∈ P, x i = pins i) ∧ (∑ i : Fin k, x i) = par)
        let flat := fun (tr : V → U) => ∀ x ∈ X, ∃ p : Fin q → V, ∀ y ∈ X,
          tr y = tr x ↔ ∀ l : Fin q, dot y (p l) = dot x (p l)
        let gain := fun (pred : V → Fin m → F) =>
          2*(∑ x ∈ X, (J.filter (fun j => pred x j = dot x (v j))).card) - X.card*J.card
        let maj := fun x : V =>
          if J.card ≤ 2*(J.filter (fun j => dot x (v j) = 1)).card then (1 : F) else 0
        X.Nonempty ∧
        (∀ tr, flat tr → ∀ dec : U → Fin m → F,
          gain (fun x j => dec (tr x) j) ≤ q*X.card) ∧
        (∃ js : Fin q ↪ Fin m, (∀ i, js i ∈ J) ∧ ∃ dec : U → Fin m → F,
          gain (fun x j => dec (fun i => dot x (v (js i))) j) = q*X.card) ∧
        9*q*X.card < gain (fun x _ => maj x) := by
  intro k hk F V q U dot'
  let t : ℕ := Nat.log 2 (1024 * k - 1)
  have hm_hi : 2 ^ t < 1024 * k := by
    have hle : 2 ^ t ≤ 1024 * k - 1 := Nat.pow_log_le_self 2 (by omega)
    omega
  have hm_lo : 512 * k ≤ 2 ^ t := by
    have hlt : 1024 * k - 1 < 2 ^ (t + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) _
    rw [pow_succ] at hlt
    omega
  obtain ⟨s, hs⟩ := exists_good_seed k (2 ^ t) (by omega) hm_lo (le_of_lt hm_hi)
  obtain ⟨C, hrb, hout, hsize, hgates, heval⟩ := exists_tape_circuit k t (by omega) s
  have hsize' : C.size ≤ 3080 * k + 3 * k * t := by
    have hkt : (k - 1) * t + t = k * t := by
      cases k with
      | zero => omega
      | succ k' => simp [Nat.succ_mul]
    have h3kt : 3 * k * t = 3 * (k * t) := Nat.mul_assoc 3 k t
    omega
  refine ⟨t, hm_lo, hm_hi, s, C, hrb, hout, hsize', hgates, heval, ?_⟩
  intro J hJ P hP pins par
  let v : Fin (2 ^ t) → Vec k := fun j i => if s.val.testBit (j.val + i.val) then (1 : F2) else 0
  have hPk : P.card < k := by omega
  have hXne := slice_nonempty P hPk pins par
  have hq_sq : q * q ≤ k := Nat.sqrt_le k
  have hq_lo : 64 ≤ q := Nat.le_sqrt.mpr (by omega)
  have hq_le_g : q + 1 ≤ k / 32 := by
    have h1 : 64 * q ≤ q * q := Nat.mul_le_mul_right q hq_lo
    omega
  have hindep_g : ∀ S : Finset (Fin (2 ^ t)), 0 < S.card → S.card ≤ k / 32 →
      ∑ j ∈ S, v j ∉ orth (sliceL P) := by
    intro S hS1 hS2 hmem
    have hw := mem_orth_sliceL_wt hPk hmem
    have hgood := hs S hS1 hS2
    have hwt_eq : wt (∑ j ∈ S, v j) =
        wt (fun i : Fin k => ∑ j ∈ S, if s.val.testBit (j.val + i.val) then (1 : F2) else 0) := by
      congr 1; funext i; exact Finset.sum_apply i S v
    rw [hwt_eq] at hw
    omega
  have hindep_q : ∀ S : Finset (Fin (2 ^ t)), 0 < S.card → S.card ≤ q + 1 →
      ∑ j ∈ S, v j ∉ orth (sliceL P) :=
    fun S hS1 hS2 => hindep_g S hS1 (hS2.trans hq_le_g)
  have hindep_1 : ∀ j : Fin (2 ^ t), v j ∉ orth (sliceL P) := by
    intro j
    have h1 := hindep_g {j} (by simp) (by simp; omega)
    simpa using h1
  have hindep_4 : ∀ S : Finset (Fin (2 ^ t)), 0 < S.card → S.card ≤ 4 →
      ∑ j ∈ S, v j ∉ orth (sliceL P) :=
    fun S hS1 hS2 => hindep_g S hS1 (by omega)
  have hJ_lo : 256 * k ≤ J.card := by omega
  have hqJ : q ≤ J.card := by
    have : q ≤ k := Nat.sqrt_le_self k
    omega
  refine ⟨hXne, ?_, ?_, ?_⟩
  · intro tr hflat dec
    exact flat_gain_le v J P pins par hindep_q tr hflat dec
  · exact exists_js_gain_eq v J P pins par hqJ hindep_1 hXne
  · exact maj_gain_gt v J P pins par (by omega) hq_sq hJ_lo hindep_4 hXne
