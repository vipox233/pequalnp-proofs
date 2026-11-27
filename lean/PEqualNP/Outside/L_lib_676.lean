import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_676

open Classical

abbrev W (n : ℕ) := Fin n → Bool
abbrev Lit (n : ℕ) := Fin n × Bool
abbrev Formula (n : ℕ) := Finset (Lit n × Lit n)

def sat {n : ℕ} (C : Formula n) (w : W n) : Bool :=
  decide (∀ c ∈ C, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)

def sol {n : ℕ} (G : Formula n) : Finset (W n) :=
  Finset.univ.filter (fun x => sat G x = true)

def high {n : ℕ} (s : ℕ) (G : Formula n) : Prop :=
  2 ^ n * (2 ^ (s - 1) + 1) ≤ 2 ^ s * (sol G).card

abbrev q1 (n : ℕ) : ℕ := 16 * (1 + 4 * (1 + Nat.clog 2 (n + 1)))
abbrev q2 (s : ℕ) : ℕ := 2 ^ s
abbrev q3 (n s : ℕ) : ℕ := s * (2 + Nat.clog 2 ((n + s - 1) / s))

-- ============================================================
-- Section 0: Basic counting and helper lemmas
-- ============================================================

lemma sat_eq_true_iff {n : ℕ} {C : Formula n} {w : W n} :
    sat C w = true ↔ ∀ c ∈ C, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2 := by
  simp only [sat, decide_eq_true_eq]

lemma sat_eq_false_iff {n : ℕ} {C : Formula n} {w : W n} :
    sat C w = false ↔ ∃ c ∈ C, w c.1.1 = c.1.2 ∧ w c.2.1 = c.2.2 := by
  rw [Bool.eq_false_iff, ne_eq, sat_eq_true_iff]
  push_neg
  rfl

lemma bool_ne_or_ne (x a b : Bool) (h : a ≠ b) : x ≠ a ∨ x ≠ b := by
  cases x <;> cases a <;> cases b <;> simp_all

lemma bool_eq_not_of_ne {x y : Bool} (h : x ≠ y) : x = !y := by
  cases x <;> cases y <;> simp_all

lemma bool_eq_of_ne_not {x y : Bool} (h : x ≠ !y) : x = y := by
  cases x <;> cases y <;> simp_all

lemma decide_eq_true_bool (b : Bool) : decide (b = true) = b := by
  cases b <;> rfl

lemma card_filter_add_card_filter_not {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hx : p x <;> simp [hx]
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_filter] at hx1 hx2
    exact hx2.2 hx1.2

lemma card_subcube {n : ℕ} (S : Finset (Fin n)) (f : Fin n → Bool) :
    (Finset.univ.filter (fun w : W n => ∀ i ∈ S, w i = f i)).card = 2 ^ (n - S.card) := by
  have heq : (Finset.univ.filter (fun w : W n => ∀ i ∈ S, w i = f i)).card =
      Fintype.card {w : W n // ∀ i ∈ S, w i = f i} := by
    rw [Fintype.card_subtype]
  rw [heq]
  let e : {w : W n // ∀ i ∈ S, w i = f i} ≃ ({i : Fin n // i ∉ S} → Bool) :=
    { toFun := fun w i => w.1 i.1
      invFun := fun g =>
        ⟨fun i => if h : i ∈ S then f i else g ⟨i, h⟩, by
          intro i hi
          simp [hi]⟩
      left_inv := fun w => by
        apply Subtype.ext
        funext i
        by_cases hi : i ∈ S
        · simp [hi, w.2 i hi]
        · simp [hi]
      right_inv := fun g => by
        funext i
        simp [i.2] }
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool]
  congr 1
  rw [Fintype.card_subtype]
  have hcompl : (Finset.univ.filter (fun i : Fin n => i ∉ S)) = Sᶜ := by
    ext i
    simp
  rw [hcompl, Finset.card_compl, Fintype.card_fin]

lemma card_sol_gt_half_of_high {n s : ℕ} (hs : 3 ≤ s) {G : Formula n} (h : high s G) :
    2 ^ n < 2 * (sol G).card := by
  unfold high at h
  have hs1 : s = (s - 1) + 1 := by omega
  have hpow : 2 ^ s = 2 ^ (s - 1) * 2 := by
    conv_lhs => rw [hs1, pow_succ]
  rw [hpow, mul_add, mul_one, mul_assoc] at h
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  have hlt : 2 ^ n * 2 ^ (s - 1) < 2 ^ (s - 1) * (2 * (sol G).card) := by omega
  rw [mul_comm (2 ^ n) (2 ^ (s - 1))] at hlt
  exact Nat.lt_of_mul_lt_mul_left hlt

lemma high_of_sol_subset {n s : ℕ} {H A : Formula n}
    (hsub : ∀ z, sat H z = true → sat A z = true) (hH : high s H) : high s A := by
  unfold high at hH ⊢
  have hcard : (sol H).card ≤ (sol A).card := by
    apply Finset.card_le_card
    intro x hx
    simp only [sol, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hsub x hx
  exact le_trans hH (Nat.mul_le_mul_left _ hcard)

lemma high_congr {n s : ℕ} {A B : Formula n} (h : ∀ z, sat B z = sat A z) :
    high s B ↔ high s A := by
  have hsol : sol B = sol A := by
    ext x
    simp [sol, h x]
  simp [high, hsol]

lemma card_sol_le_of_proj_pol {n k : ℕ} (G : Formula n) (f : Fin k → Fin n)
    (hf : Function.Injective f) (pol : Fin k → Bool)
    (P : (Fin k → Bool) → Prop) [DecidablePred P]
    (hP : ∀ w : W n, sat G w = true → P (fun i => decide (w (f i) = pol i))) :
    2 ^ k * (sol G).card ≤ (Finset.univ.filter P).card * 2 ^ n := by
  let proj : W n → (Fin k → Bool) := fun w i => decide (w (f i) = pol i)
  let fiber : (Fin k → Bool) → Finset (W n) :=
    fun v => Finset.univ.filter (fun w => proj w = v)
  have hsub : sol G ⊆ (Finset.univ.filter P).biUnion fiber := by
    intro w hw
    rw [Finset.mem_biUnion]
    refine ⟨proj w, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [sol, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      exact hP w hw
    · simp [fiber]
  have hfiber : ∀ v : Fin k → Bool, (fiber v).card = 2 ^ (n - k) := by
    intro v
    let S : Finset (Fin n) := Finset.univ.image f
    have hScard : S.card = k := by
      rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
    let g : Fin n → Bool := fun j =>
      if h : ∃ i : Fin k, f i = j then
        let i := Classical.choose h
        if v i then pol i else !pol i
      else false
    have hfeq : fiber v = Finset.univ.filter (fun w : W n => ∀ j ∈ S, w j = g j) := by
      ext w
      simp only [fiber, proj, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hproj j hj
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
        have h1 : decide (w (f i) = pol i) = v i := congrFun hproj i
        have hex : ∃ i' : Fin k, f i' = f i := ⟨i, rfl⟩
        have hch : Classical.choose hex = i := hf (Classical.choose_spec hex)
        simp only [g, dif_pos hex, hch]
        cases hw : w (f i) <;> cases hp : pol i <;> cases hv : v i <;> simp_all
      · intro hall
        funext i
        have hj : f i ∈ S := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
        have h1 := hall (f i) hj
        have hex : ∃ i' : Fin k, f i' = f i := ⟨i, rfl⟩
        have hch : Classical.choose hex = i := hf (Classical.choose_spec hex)
        simp only [g, dif_pos hex, hch] at h1
        cases hw : w (f i) <;> cases hp : pol i <;> cases hv : v i <;> simp_all
    rw [hfeq, card_subcube S g, hScard]
  have hle1 : (sol G).card ≤ (Finset.univ.filter P).card * 2 ^ (n - k) := by
    calc (sol G).card
        ≤ ((Finset.univ.filter P).biUnion fiber).card := Finset.card_le_card hsub
      _ ≤ ∑ v ∈ Finset.univ.filter P, (fiber v).card := Finset.card_biUnion_le
      _ = ∑ _v ∈ Finset.univ.filter P, 2 ^ (n - k) := Finset.sum_congr rfl (fun v _ => hfiber v)
      _ = (Finset.univ.filter P).card * 2 ^ (n - k) := by simp
  have hkn : k ≤ n := by
    have := Fintype.card_le_of_injective f hf
    simpa using this
  have hpow : 2 ^ k * 2 ^ (n - k) = 2 ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  calc 2 ^ k * (sol G).card
      ≤ 2 ^ k * ((Finset.univ.filter P).card * 2 ^ (n - k)) := Nat.mul_le_mul_left _ hle1
    _ = (Finset.univ.filter P).card * (2 ^ k * 2 ^ (n - k)) := by ring
    _ = (Finset.univ.filter P).card * 2 ^ n := by rw [hpow]

-- ============================================================
-- Section 1: Strength-4 covering pool existence
-- ============================================================

def Consistent4 {n : ℕ} (t : Fin 4 → Lit n) : Prop :=
  ∀ a b : Fin 4, (t a).1 = (t b).1 → (t a).2 = (t b).2

def Matches4 {n : ℕ} (t : Fin 4 → Lit n) (w : W n) : Prop :=
  ∀ a : Fin 4, w (t a).1 = (t a).2

def IsStrength4Pool {n m : ℕ} (P : Fin m → W n) : Prop :=
  ∀ t : Fin 4 → Lit n, Consistent4 t → ∃ r : Fin m, Matches4 t (P r)

lemma card_not_matches4_le {n : ℕ} (t : Fin 4 → Lit n) (ht : Consistent4 t) :
    16 * (Finset.univ.filter (fun w : W n => ¬ Matches4 t w)).card ≤ 15 * 2 ^ n := by
  let S : Finset (Fin n) := Finset.univ.image (fun a : Fin 4 => (t a).1)
  have hScard : S.card ≤ 4 := by
    calc S.card ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
      _ = 4 := by simp
  let f : Fin n → Bool := fun j =>
    if h : ∃ a : Fin 4, (t a).1 = j then (t (Classical.choose h)).2 else false
  have hmeq : Finset.univ.filter (fun w : W n => Matches4 t w) =
      Finset.univ.filter (fun w : W n => ∀ j ∈ S, w j = f j) := by
    ext w
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    constructor
    · intro hw j hj
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hj
      have hex : ∃ a' : Fin 4, (t a').1 = (t a).1 := ⟨a, rfl⟩
      simp only [f, dif_pos hex]
      rw [hw a]
      exact ht a (Classical.choose hex) (Classical.choose_spec hex).symm
    · intro hall a
      have hj : (t a).1 ∈ S := Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
      have h1 := hall (t a).1 hj
      have hex : ∃ a' : Fin 4, (t a').1 = (t a).1 := ⟨a, rfl⟩
      simp only [f, dif_pos hex] at h1
      rw [h1]
      exact ht (Classical.choose hex) a (Classical.choose_spec hex)
  have hgood : (Finset.univ.filter (fun w : W n => Matches4 t w)).card = 2 ^ (n - S.card) := by
    rw [hmeq, card_subcube]
  have hgood16 : 2 ^ n ≤ 16 * (Finset.univ.filter (fun w : W n => Matches4 t w)).card := by
    rw [hgood]
    have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [h16, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsum : (Finset.univ.filter (fun w : W n => Matches4 t w)).card +
      (Finset.univ.filter (fun w : W n => ¬ Matches4 t w)).card = 2 ^ n := by
    rw [card_filter_add_card_filter_not]
    simp [W]
  omega

lemma exists_strength4_pool (n : ℕ) :
    ∃ P : Fin (q1 n) → W n, IsStrength4Pool P := by
  let q := q1 n
  let badPools : Finset (Fin q → W n) :=
    Finset.univ.filter (fun P => ¬ IsStrength4Pool P)
  let miss (t : Fin 4 → Lit n) : Finset (Fin q → W n) :=
    Finset.univ.filter (fun P => ∀ r : Fin q, ¬ Matches4 t (P r))
  have hsub : badPools ⊆
      (Finset.univ.filter (fun t : Fin 4 → Lit n => Consistent4 t)).biUnion miss := by
    intro P hP
    simp only [badPools, Finset.mem_filter, Finset.mem_univ, true_and, IsStrength4Pool,
      not_forall, not_exists] at hP
    obtain ⟨t, ht, hmiss⟩ := hP
    rw [Finset.mem_biUnion]
    exact ⟨t, by simp [ht], by simp [miss, hmiss]⟩
  have hmiss_card : ∀ t : Fin 4 → Lit n,
      (miss t).card = (Finset.univ.filter (fun w : W n => ¬ Matches4 t w)).card ^ q := by
    intro t
    rw [show (miss t).card = Fintype.card {P : Fin q → W n // ∀ r : Fin q, ¬ Matches4 t (P r)} by
      rw [Fintype.card_subtype]]
    let e : {P : Fin q → W n // ∀ r : Fin q, ¬ Matches4 t (P r)} ≃
        (Fin q → {w : W n // ¬ Matches4 t w}) :=
      { toFun := fun P r => ⟨P.1 r, P.2 r⟩
        invFun := fun f => ⟨fun r => (f r).1, fun r => (f r).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_subtype, Fintype.card_fin]
  have hmiss_bound : ∀ t : Fin 4 → Lit n, Consistent4 t →
      16 ^ q * (miss t).card ≤ 15 ^ q * (2 ^ n) ^ q := by
    intro t ht
    rw [hmiss_card t, ← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left (card_not_matches4_le t ht) q
  have hbad_bound : 16 ^ q * badPools.card ≤ (16 * n ^ 4) * (15 ^ q * (2 ^ n) ^ q) := by
    calc 16 ^ q * badPools.card
        ≤ 16 ^ q * ((Finset.univ.filter (fun t : Fin 4 → Lit n => Consistent4 t)).biUnion miss).card :=
          Nat.mul_le_mul_left _ (Finset.card_le_card hsub)
      _ ≤ 16 ^ q * ∑ t ∈ Finset.univ.filter (fun t : Fin 4 → Lit n => Consistent4 t), (miss t).card :=
          Nat.mul_le_mul_left _ Finset.card_biUnion_le
      _ = ∑ t ∈ Finset.univ.filter (fun t : Fin 4 → Lit n => Consistent4 t), 16 ^ q * (miss t).card := by
          rw [Finset.mul_sum]
      _ ≤ ∑ _t ∈ Finset.univ.filter (fun t : Fin 4 → Lit n => Consistent4 t), (15 ^ q * (2 ^ n) ^ q) := by
          apply Finset.sum_le_sum
          intro t ht
          exact hmiss_bound t (Finset.mem_filter.mp ht).2
      _ = (Finset.univ.filter (fun t : Fin 4 → Lit n => Consistent4 t)).card * (15 ^ q * (2 ^ n) ^ q) := by
          simp
      _ ≤ Fintype.card (Fin 4 → Lit n) * (15 ^ q * (2 ^ n) ^ q) := by
          apply Nat.mul_le_mul_right
          simpa using Finset.card_filter_le (Finset.univ : Finset (Fin 4 → Lit n)) _
      _ = (16 * n ^ 4) * (15 ^ q * (2 ^ n) ^ q) := by
          have hcard4 : Fintype.card (Fin 4 → Lit n) = 16 * n ^ 4 := by
            simp [Lit, mul_pow]
            ring
          rw [hcard4]
  let m := 1 + 4 * (1 + Nat.clog 2 (n + 1))
  have hqm : q = 16 * m := rfl
  have hclog : n + 1 ≤ 2 ^ Nat.clog 2 (n + 1) := Nat.le_pow_clog (by norm_num) (n + 1)
  have h2m : 16 * n ^ 4 < 2 ^ m := by
    have hm_eq : m = 5 + 4 * Nat.clog 2 (n + 1) := by omega
    rw [hm_eq, pow_add, mul_comm 4 _, pow_mul]
    have hpow4 : (n + 1) ^ 4 ≤ (2 ^ Nat.clog 2 (n + 1)) ^ 4 := Nat.pow_le_pow_left hclog 4
    have hlt1 : n ^ 4 < (n + 1) ^ 4 := Nat.pow_lt_pow_left (Nat.lt_succ_self n) (by norm_num)
    have h32 : 2 ^ 5 = 32 := by norm_num
    rw [h32]
    have : 16 * n ^ 4 < 32 * (n + 1) ^ 4 := by
      have : n ^ 4 + 1 ≤ (n + 1) ^ 4 := hlt1
      omega
    exact lt_of_lt_of_le this (Nat.mul_le_mul_left 32 hpow4)
  have h1516 : 2 * 15 ^ 16 ≤ 16 ^ 16 := by norm_num
  have hstrict : (16 * n ^ 4) * 15 ^ q < 16 ^ q := by
    rw [hqm, pow_mul 15 16 m, pow_mul 16 16 m]
    have h1 : (16 * n ^ 4) * (15 ^ 16) ^ m < 2 ^ m * (15 ^ 16) ^ m :=
      Nat.mul_lt_mul_of_pos_right h2m (by positivity)
    have h2 : 2 ^ m * (15 ^ 16) ^ m ≤ (16 ^ 16) ^ m := by
      rw [← mul_pow]
      exact Nat.pow_le_pow_left h1516 m
    exact lt_of_lt_of_le h1 h2
  have hlt_all : badPools.card < (Finset.univ : Finset (Fin q → W n)).card := by
    have hcard_univ : (Finset.univ : Finset (Fin q → W n)).card = (2 ^ n) ^ q := by
      simp [W]
    rw [hcard_univ]
    have h1 : 16 ^ q * badPools.card < 16 ^ q * (2 ^ n) ^ q := by
      calc 16 ^ q * badPools.card
          ≤ (16 * n ^ 4) * (15 ^ q * (2 ^ n) ^ q) := hbad_bound
        _ = ((16 * n ^ 4) * 15 ^ q) * (2 ^ n) ^ q := by ring
        _ < 16 ^ q * (2 ^ n) ^ q := Nat.mul_lt_mul_of_pos_right hstrict (by positivity)
    exact Nat.lt_of_mul_lt_mul_left h1
  have hne : (Finset.univ \ badPools).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hle : (Finset.univ : Finset (Fin q → W n)).card ≤ badPools.card := by
      have hsub2 : (Finset.univ : Finset (Fin q → W n)) ⊆ badPools :=
        Finset.sdiff_eq_empty_iff_subset.mp hemp
      exact Finset.card_le_card hsub2
    omega
  obtain ⟨P, hP⟩ := hne
  rw [Finset.mem_sdiff] at hP
  simp only [badPools, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hP
  exact ⟨P, hP⟩

-- ============================================================
-- Section 2: Positive pair hull and Case 1 (no literal half)
-- ============================================================

def posHull {n m : ℕ} (P : Fin m → W n) (ans : Fin m → Bool) : Formula n :=
  Finset.univ.filter (fun c : Lit n × Lit n =>
    ∀ r : Fin m, ans r = true → P r c.1.1 ≠ c.1.2 ∨ P r c.2.1 ≠ c.2.2)

lemma subset_posHull {n m : ℕ} (P : Fin m → W n) (A : Formula n) :
    A ⊆ posHull P (fun r => sat A (P r)) := by
  intro c hc
  simp only [posHull, Finset.mem_filter, Finset.mem_univ, true_and]
  intro r hr
  exact (sat_eq_true_iff.mp hr) c hc

lemma sat_of_sat_posHull {n m : ℕ} (P : Fin m → W n) (A : Formula n) (z : W n)
    (hz : sat (posHull P (fun r => sat A (P r))) z = true) : sat A z = true := by
  rw [sat_eq_true_iff] at hz ⊢
  intro c hc
  exact hz c (subset_posHull P A hc)

def IsLitHalf {n : ℕ} (G : Formula n) (l : Lit n) : Prop :=
  ∀ w : W n, w l.1 = l.2 → sat G w = true

lemma isLitHalf_iff_clauses {n : ℕ} (G : Formula n) (l : Lit n) :
    IsLitHalf G l ↔
      ∀ c ∈ G, (c.1.1 = c.2.1 ∧ c.1.2 ≠ c.2.2) ∨ c.1 = (l.1, !l.2) ∨ c.2 = (l.1, !l.2) := by
  constructor
  · intro hG c hc
    by_contra hnot
    push_neg at hnot
    rcases hnot with ⟨hnt, hc1, hc2⟩
    let w : W n := fun j =>
      if j = c.1.1 then c.1.2
      else if j = c.2.1 then c.2.2
      else l.2
    have hwl : w l.1 = l.2 := by
      simp only [w]
      by_cases h1 : l.1 = c.1.1
      · rw [if_pos h1]
        by_contra hne
        exact hc1 (Prod.ext h1.symm (bool_eq_not_of_ne hne))
      · rw [if_neg h1]
        by_cases h2 : l.1 = c.2.1
        · rw [if_pos h2]
          by_contra hne
          exact hc2 (Prod.ext h2.symm (bool_eq_not_of_ne hne))
        · rw [if_neg h2]
    have hwc1 : w c.1.1 = c.1.2 := by simp [w]
    have hwc2 : w c.2.1 = c.2.2 := by
      simp only [w]
      by_cases h12 : c.2.1 = c.1.1
      · rw [if_pos h12]
        exact hnt h12.symm
      · simp [h12]
    have hsat := sat_eq_true_iff.mp (hG w hwl)
    rcases hsat c hc with h | h
    · exact h hwc1
    · exact h hwc2
  · intro hall w hwl
    rw [sat_eq_true_iff]
    intro c hc
    rcases hall c hc with ⟨h1, h2⟩ | h1 | h2
    · rw [← h1]
      exact bool_ne_or_ne (w c.1.1) c.1.2 c.2.2 h2
    · left
      rw [h1]
      simp [hwl]
    · right
      rw [h2]
      simp [hwl]

lemma isLitHalf_hull_iff {n m : ℕ} {P : Fin m → W n} (hP : IsStrength4Pool P)
    (A : Formula n) (l : Lit n) :
    IsLitHalf (posHull P (fun r => sat A (P r))) l ↔ IsLitHalf A l := by
  constructor
  · intro hH w hw
    exact sat_of_sat_posHull P A w (hH w hw)
  · intro hA
    rw [isLitHalf_iff_clauses]
    intro c hc
    by_contra hnot
    push_neg at hnot
    rcases hnot with ⟨hnt, hc1, hc2⟩
    let w : W n := fun j =>
      if j = c.1.1 then c.1.2
      else if j = c.2.1 then c.2.2
      else l.2
    have hwl : w l.1 = l.2 := by
      simp only [w]
      by_cases h1 : l.1 = c.1.1
      · rw [if_pos h1]
        by_contra hne
        exact hc1 (Prod.ext h1.symm (bool_eq_not_of_ne hne))
      · rw [if_neg h1]
        by_cases h2 : l.1 = c.2.1
        · rw [if_pos h2]
          by_contra hne
          exact hc2 (Prod.ext h2.symm (bool_eq_not_of_ne hne))
        · rw [if_neg h2]
    have hwc1 : w c.1.1 = c.1.2 := by simp [w]
    have hwc2 : w c.2.1 = c.2.2 := by
      simp only [w]
      by_cases h12 : c.2.1 = c.1.1
      · rw [if_pos h12]
        exact hnt h12.symm
      · simp [h12]
    let t : Fin 4 → Lit n := ![l, c.1, c.2, l]
    have hmt : Matches4 t w := by
      intro a
      fin_cases a <;> simp [t, hwl, hwc1, hwc2]
    have hcons : Consistent4 t := by
      intro a b hab
      rw [← hmt a, ← hmt b, hab]
    obtain ⟨r, hr⟩ := hP t hcons
    have hr0 : P r l.1 = l.2 := hr 0
    have hr1 : P r c.1.1 = c.1.2 := hr 1
    have hr2 : P r c.2.1 = c.2.2 := hr 2
    have hsatA : sat A (P r) = true := hA (P r) hr0
    simp only [posHull, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rcases hc r hsatA with h | h
    · exact h hr1
    · exact h hr2

lemma card_filter_fin_zero (P : (Fin 0 → Bool) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = if P Fin.elim0 then 1 else 0 := by
  have heq : (Finset.univ : Finset (Fin 0 → Bool)) = {Fin.elim0} := by
    ext f
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim f Fin.elim0
  rw [heq, Finset.filter_singleton]
  split_ifs <;> simp

lemma card_filter_fin_succ {k : ℕ} (P : (Fin (k + 1) → Bool) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      (Finset.univ.filter (fun v : Fin k → Bool => P (Fin.cons false v))).card +
      (Finset.univ.filter (fun v : Fin k → Bool => P (Fin.cons true v))).card := by
  rw [show (Finset.univ.filter P).card = Fintype.card {v : Fin (k + 1) → Bool // P v} by
    rw [Fintype.card_subtype]]
  let e : {v : Fin (k + 1) → Bool // P v} ≃
      {v : Fin k → Bool // P (Fin.cons false v)} ⊕ {v : Fin k → Bool // P (Fin.cons true v)} :=
    { toFun := fun v =>
        if h : v.1 0 = false then
          Sum.inl ⟨Fin.tail v.1, by
            have : Fin.cons false (Fin.tail v.1) = v.1 := by
              funext i; refine Fin.cases ?_ ?_ i
              · simp [h]
              · intro j; simp [Fin.tail]
            rw [this]; exact v.2⟩
        else
          Sum.inr ⟨Fin.tail v.1, by
            have ht : v.1 0 = true := by cases h0 : v.1 0 <;> simp_all
            have : Fin.cons true (Fin.tail v.1) = v.1 := by
              funext i; refine Fin.cases ?_ ?_ i
              · simp [ht]
              · intro j; simp [Fin.tail]
            rw [this]; exact v.2⟩
      invFun := fun s =>
        match s with
        | Sum.inl v => ⟨Fin.cons false v.1, v.2⟩
        | Sum.inr v => ⟨Fin.cons true v.1, v.2⟩
      left_inv := fun v => by
        dsimp only
        split_ifs with h
        · apply Subtype.ext; funext i; refine Fin.cases ?_ ?_ i <;> simp [h, Fin.tail]
        · have ht : v.1 0 = true := by cases h0 : v.1 0 <;> simp_all
          apply Subtype.ext; funext i; refine Fin.cases ?_ ?_ i <;> simp [ht, Fin.tail]
      right_inv := fun s => by
        cases s with
        | inl v =>
            dsimp only
            rw [dif_pos (by simp)]
            apply congrArg Sum.inl
            apply Subtype.ext; funext j; simp [Fin.tail]
        | inr v =>
            dsimp only
            rw [dif_neg (by simp)]
            apply congrArg Sum.inr
            apply Subtype.ext; funext j; simp [Fin.tail] }
  rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_subtype, Fintype.card_subtype]

lemma card_filter_prod {a b : ℕ}
    (P : (Fin a → Bool) → Prop) [DecidablePred P]
    (Q : (Fin b → Bool) → Prop) [DecidablePred Q] :
    (Finset.univ.filter fun v : Fin (a + b) → Bool =>
      P (fun i => v (Fin.castAdd b i)) ∧ Q (fun j => v (Fin.natAdd a j))).card =
      (Finset.univ.filter P).card * (Finset.univ.filter Q).card := by
  rw [show (Finset.univ.filter fun v : Fin (a + b) → Bool =>
        P (fun i => v (Fin.castAdd b i)) ∧ Q (fun j => v (Fin.natAdd a j))).card =
      Fintype.card {v : Fin (a + b) → Bool //
        P (fun i => v (Fin.castAdd b i)) ∧ Q (fun j => v (Fin.natAdd a j))} by
    rw [Fintype.card_subtype]]
  let e : {v : Fin (a + b) → Bool //
      P (fun i => v (Fin.castAdd b i)) ∧ Q (fun j => v (Fin.natAdd a j))} ≃
      {u : Fin a → Bool // P u} × {w : Fin b → Bool // Q w} :=
    { toFun := fun v =>
        (⟨fun i => v.1 (Fin.castAdd b i), v.2.1⟩, ⟨fun j => v.1 (Fin.natAdd a j), v.2.2⟩)
      invFun := fun p =>
        ⟨Fin.append p.1.1 p.2.1, by
          constructor
          · convert p.1.2 using 1; funext i; exact Fin.append_left _ _ i
          · convert p.2.2 using 1; funext j; exact Fin.append_right _ _ j⟩
      left_inv := fun v => by
        apply Subtype.ext
        funext k
        refine Fin.addCases ?_ ?_ k
        · intro i; exact Fin.append_left _ _ i
        · intro j; exact Fin.append_right _ _ j
      right_inv := fun p => by
        apply Prod.ext
        · apply Subtype.ext; funext i; exact Fin.append_left _ _ i
        · apply Subtype.ext; funext j; exact Fin.append_right _ _ j }
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_subtype, Fintype.card_subtype]

lemma card_K2_eq :
    (Finset.univ.filter fun v : Fin 2 → Bool => v 0 = false ∨ v 1 = false).card = 3 := by
  simp only [card_filter_fin_succ, card_filter_fin_zero]
  decide

lemma card_P3_eq :
    (Finset.univ.filter fun v : Fin 3 → Bool =>
      (v 0 = false ∨ v 1 = false) ∧ (v 1 = false ∨ v 2 = false)).card = 5 := by
  simp only [card_filter_fin_succ, card_filter_fin_zero]
  decide

lemma card_triangle_le :
    (Finset.univ.filter fun v : Fin 3 → Bool =>
      (v 0 = false ∨ v 1 = false) ∧ (v 1 = false ∨ v 2 = false) ∧
      (v 0 = false ∨ v 2 = false)).card = 4 := by
  simp only [card_filter_fin_succ, card_filter_fin_zero]
  decide

lemma card_P4_le :
    (Finset.univ.filter fun v : Fin 4 → Bool =>
      (v 0 = false ∨ v 1 = false) ∧ (v 1 = false ∨ v 2 = false) ∧
      (v 2 = false ∨ v 3 = false)).card = 8 := by
  simp only [card_filter_fin_succ, card_filter_fin_zero]
  decide

lemma card_P3K2_le :
    (Finset.univ.filter fun v : Fin 5 → Bool =>
      (v 0 = false ∨ v 1 = false) ∧ (v 1 = false ∨ v 2 = false) ∧
      (v 3 = false ∨ v 4 = false)).card = 15 := by
  have h := card_filter_prod (a := 3) (b := 2)
    (fun v => (v 0 = false ∨ v 1 = false) ∧ (v 1 = false ∨ v 2 = false))
    (fun v => v 0 = false ∨ v 1 = false)
  rw [card_P3_eq, card_K2_eq] at h
  convert h using 2
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h0 : (Fin.castAdd 2 (0 : Fin 3)) = (0 : Fin 5) := rfl
  have h1 : (Fin.castAdd 2 (1 : Fin 3)) = (1 : Fin 5) := rfl
  have h2 : (Fin.castAdd 2 (2 : Fin 3)) = (2 : Fin 5) := rfl
  have h3 : (Fin.natAdd 3 (0 : Fin 2)) = (3 : Fin 5) := rfl
  have h4 : (Fin.natAdd 3 (1 : Fin 2)) = (4 : Fin 5) := rfl
  simp only [h0, h1, h2, h3, h4, and_assoc]

lemma card_3K2_le :
    (Finset.univ.filter fun v : Fin 6 → Bool =>
      (v 0 = false ∨ v 1 = false) ∧ (v 2 = false ∨ v 3 = false) ∧
      (v 4 = false ∨ v 5 = false)).card = 27 := by
  have h22 : (Finset.univ.filter fun v : Fin 4 → Bool =>
      (v 0 = false ∨ v 1 = false) ∧ (v 2 = false ∨ v 3 = false)).card = 9 := by
    have h := card_filter_prod (a := 2) (b := 2)
      (fun v => v 0 = false ∨ v 1 = false)
      (fun v => v 0 = false ∨ v 1 = false)
    rw [card_K2_eq] at h
    convert h using 2
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have h := card_filter_prod (a := 2) (b := 4)
    (fun v => v 0 = false ∨ v 1 = false)
    (fun v => (v 0 = false ∨ v 1 = false) ∧ (v 2 = false ∨ v 3 = false))
  rw [card_K2_eq, h22] at h
  convert h using 2
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

lemma card_opp2_le :
    ∀ c1 c2 : Bool,
      (Finset.univ.filter fun v : Fin 2 → Bool =>
        (v 0 = false ∨ v 1 ≠ c1) ∧ (v 0 = true ∨ v 1 ≠ c2)).card ≤ 2 := by
  intro c1 c2
  cases c1 <;> cases c2 <;>
    simp only [card_filter_fin_succ, card_filter_fin_zero] <;>
    decide

lemma card_opp3_le :
    ∀ c1 c2 : Bool,
      (Finset.univ.filter fun v : Fin 3 → Bool =>
        (v 0 = false ∨ v 1 ≠ c1) ∧ (v 0 = true ∨ v 2 ≠ c2)).card ≤ 4 := by
  intro c1 c2
  cases c1 <;> cases c2 <;>
    simp only [card_filter_fin_succ, card_filter_fin_zero] <;>
    decide

lemma two_disjoint_clauses_of_no_litHalf {n : ℕ} (hn : 1 ≤ n) (A : Formula n)
    (hgt : 2 ^ n < 2 * (sol A).card) (hno : ∀ l : Lit n, ¬ IsLitHalf A l) :
    ∃ (u1 v1 u2 v2 : Fin n) (bu1 bv1 bu2 bv2 : Bool),
      ∀ w : W n, sat A w = true ↔
        (w u1 ≠ bu1 ∨ w v1 ≠ bv1) ∧ (w u2 ≠ bu2 ∨ w v2 ≠ bv2) := by
  -- Step 1: No unit clause
  have hno_unit : ∀ c ∈ A, c.1.1 = c.2.1 → c.1.2 ≠ c.2.2 := by
    intro c hc h12 heq
    have hsub : sol A ⊆ Finset.univ.filter (fun w : W n => ∀ j ∈ ({c.1.1} : Finset (Fin n)), w j = !c.1.2) := by
      intro w hw
      simp only [sol, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      intro j hj
      subst hj
      rcases (sat_eq_true_iff.mp hw) c hc with h | h
      · exact bool_eq_not_of_ne h
      · rw [← h12, ← heq] at h
        exact bool_eq_not_of_ne h
    have hcard : (sol A).card ≤ 2 ^ (n - 1) := by
      calc (sol A).card ≤ _ := Finset.card_le_card hsub
        _ = 2 ^ (n - ({c.1.1} : Finset (Fin n)).card) := card_subcube _ _
        _ = 2 ^ (n - 1) := by simp
    have h2 : 2 * 2 ^ (n - 1) = 2 ^ n := by
      have : n = (n - 1) + 1 := by omega
      conv_rhs => rw [this, pow_succ, mul_comm]
    omega
  -- Active proper clauses (symmetric)
  let act : Lit n → Lit n → Prop := fun l1 l2 =>
    l1.1 ≠ l2.1 ∧ ((l1, l2) ∈ A ∨ (l2, l1) ∈ A)
  have hact_symm : ∀ {l1 l2}, act l1 l2 → act l2 l1 := by
    intro l1 l2 ⟨hne, hmem⟩
    exact ⟨hne.symm, hmem.symm⟩
  have hact_sat : ∀ {l1 l2 w}, act l1 l2 → sat A w = true → w l1.1 ≠ l1.2 ∨ w l2.1 ≠ l2.2 := by
    intro l1 l2 w ⟨_, hmem⟩ hw
    have hw' := sat_eq_true_iff.mp hw
    rcases hmem with h | h
    · exact hw' (l1, l2) h
    · exact (hw' (l2, l1) h).symm
  -- Step 2: Consistent polarities
  have hpol_cons : ∀ {i b1 b2 l1 l2}, act (i, b1) l1 → act (i, b2) l2 → b1 = b2 := by
    intro i b1 b2 l1 l2 h1 h2
    by_contra hne_b
    have hb2 : b2 = !b1 := bool_eq_not_of_ne (Ne.symm hne_b)
    subst hb2
    by_cases hj : l1.1 = l2.1
    · let f : Fin 2 → Fin n := ![i, l1.1]
      have hf : Function.Injective f := by
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp [f] at hab ⊢
        · exact absurd hab h1.1
        · exact absurd hab.symm h1.1
      let pol : Fin 2 → Bool := ![b1, true]
      have hf0 : f 0 = i := rfl
      have hf1 : f 1 = l1.1 := rfl
      have hp0 : pol 0 = b1 := rfl
      have hp1 : pol 1 = true := rfl
      let P : (Fin 2 → Bool) → Prop := fun v =>
        (v 0 = false ∨ v 1 ≠ l1.2) ∧ (v 0 = true ∨ v 1 ≠ l2.2)
      have hP : ∀ w : W n, sat A w = true → P (fun k => decide (w (f k) = pol k)) := by
        intro w hw
        have s1 := hact_sat h1 hw
        have s2 := hact_sat h2 hw
        rw [← hj] at s2
        constructor
        · rcases s1 with h | h
          · left; dsimp only; rw [hf0, hp0]; exact decide_eq_false h
          · right; dsimp only; rw [hf1, hp1, decide_eq_true_bool]; exact h
        · rcases s2 with h | h
          · left; dsimp only; rw [hf0, hp0]; exact decide_eq_true (bool_eq_of_ne_not h)
          · right; dsimp only; rw [hf1, hp1, decide_eq_true_bool]; exact h
      have hbound := card_sol_le_of_proj_pol A f hf pol P hP
      have hcnt := card_opp2_le l1.2 l2.2
      have : 4 * (sol A).card ≤ 2 * 2 ^ n := by
        calc 4 * (sol A).card = 2 ^ 2 * (sol A).card := by norm_num
          _ ≤ (Finset.univ.filter P).card * 2 ^ n := hbound
          _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_right _ hcnt
      omega
    · let f : Fin 3 → Fin n := ![i, l1.1, l2.1]
      have hf : Function.Injective f := by
        intro a b hab
        fin_cases a <;> fin_cases b <;> simp [f] at hab ⊢
        · exact absurd hab h1.1
        · exact absurd hab h2.1
        · exact absurd hab.symm h1.1
        · exact absurd hab hj
        · exact absurd hab.symm h2.1
        · exact absurd hab.symm hj
      let pol : Fin 3 → Bool := ![b1, true, true]
      have hf0 : f 0 = i := rfl
      have hf1 : f 1 = l1.1 := rfl
      have hf2 : f 2 = l2.1 := rfl
      have hp0 : pol 0 = b1 := rfl
      have hp1 : pol 1 = true := rfl
      have hp2 : pol 2 = true := rfl
      let P : (Fin 3 → Bool) → Prop := fun v =>
        (v 0 = false ∨ v 1 ≠ l1.2) ∧ (v 0 = true ∨ v 2 ≠ l2.2)
      have hP : ∀ w : W n, sat A w = true → P (fun k => decide (w (f k) = pol k)) := by
        intro w hw
        have s1 := hact_sat h1 hw
        have s2 := hact_sat h2 hw
        constructor
        · rcases s1 with h | h
          · left; dsimp only; rw [hf0, hp0]; exact decide_eq_false h
          · right; dsimp only; rw [hf1, hp1, decide_eq_true_bool]; exact h
        · rcases s2 with h | h
          · left; dsimp only; rw [hf0, hp0]; exact decide_eq_true (bool_eq_of_ne_not h)
          · right; dsimp only; rw [hf2, hp2, decide_eq_true_bool]; exact h
      have hbound := card_sol_le_of_proj_pol A f hf pol P hP
      have hcnt := card_opp3_le l1.2 l2.2
      have : 8 * (sol A).card ≤ 4 * 2 ^ n := by
        calc 8 * (sol A).card = 2 ^ 3 * (sol A).card := by norm_num
          _ ≤ (Finset.univ.filter P).card * 2 ^ n := hbound
          _ ≤ 4 * 2 ^ n := Nat.mul_le_mul_right _ hcnt
      omega
  -- Define canonical polarity and edge relation E
  let pol : Fin n → Bool := fun i =>
    if h : ∃ b : Bool, ∃ l : Lit n, act (i, b) l then Classical.choose h else false
  have hpol_eq : ∀ {l1 l2}, act l1 l2 → l1.2 = pol l1.1 := by
    intro l1 l2 h
    have hex : ∃ b : Bool, ∃ l : Lit n, act (l1.1, b) l := ⟨l1.2, l2, h⟩
    simp only [pol, dif_pos hex]
    obtain ⟨l', hl'⟩ := Classical.choose_spec hex
    exact hpol_cons h hl'
  let E : Fin n → Fin n → Prop := fun i j => act (i, pol i) (j, pol j)
  have hE_ne : ∀ {i j}, E i j → i ≠ j := fun h => h.1
  have hE_symm : ∀ {i j}, E i j → E j i := fun h => hact_symm h
  have hE_sat : ∀ w : W n, sat A w = true ↔ ∀ i j, E i j → w i ≠ pol i ∨ w j ≠ pol j := by
    intro w
    constructor
    · intro hw i j hij
      exact hact_sat hij hw
    · intro hall
      rw [sat_eq_true_iff]
      intro c hc
      by_cases h12 : c.1.1 = c.2.1
      · have hne := hno_unit c hc h12
        rw [← h12]
        exact bool_ne_or_ne (w c.1.1) c.1.2 c.2.2 hne
      · have ha : act c.1 c.2 := ⟨h12, Or.inl hc⟩
        have hp1 : c.1.2 = pol c.1.1 := hpol_eq ha
        have hp2 : c.2.2 = pol c.2.1 := hpol_eq (hact_symm ha)
        have hE : E c.1.1 c.2.1 := by
          dsimp only [E]
          rwa [← hp1, ← hp2]
        have hres := hall c.1.1 c.2.1 hE
        rwa [← hp1, ← hp2] at hres
  -- Every vertex fails to cover all edges
  have hno_cover : ∀ i : Fin n, ∃ u v : Fin n, E u v ∧ u ≠ i ∧ v ≠ i := by
    intro i
    by_contra hall
    push_neg at hall
    apply hno (i, !pol i)
    intro w hw
    rw [hE_sat]
    intro u v huv
    by_cases hu : u = i
    · left; subst hu; simp [hw]
    · right
      have hv : v = i := by
        by_contra hv'
        exact hv' (hall u v huv hu)
      subst hv; simp [hw]
  -- Forbidden subgraphs
  have hno_tri : ∀ a b c : Fin n, E a b → E b c → E a c → False := by
    intro a b c hab hbc hac
    let f : Fin 3 → Fin n := ![a, b, c]
    have hf : Function.Injective f := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp [f] at hxy ⊢
      · exact absurd hxy (hE_ne hab)
      · exact absurd hxy (hE_ne hac)
      · exact absurd hxy.symm (hE_ne hab)
      · exact absurd hxy (hE_ne hbc)
      · exact absurd hxy.symm (hE_ne hac)
      · exact absurd hxy.symm (hE_ne hbc)
    let P : (Fin 3 → Bool) → Prop := fun v =>
      (v 0 = false ∨ v 1 = false) ∧ (v 1 = false ∨ v 2 = false) ∧ (v 0 = false ∨ v 2 = false)
    have hP : ∀ w : W n, sat A w = true → P (fun k => decide (w (f k) = pol (f k))) := by
      intro w hw
      rw [hE_sat] at hw
      refine ⟨?_, ?_, ?_⟩
      · rcases hw a b hab with h | h <;> simp [f, h]
      · rcases hw b c hbc with h | h <;> simp [f, h]
      · rcases hw a c hac with h | h <;> simp [f, h]
    have hb := card_sol_le_of_proj_pol A f hf (fun k => pol (f k)) P hP
    rw [card_triangle_le] at hb
    have : 8 * (sol A).card ≤ 4 * 2 ^ n := by simpa using hb
    omega
  have hno_P4 : ∀ a b c d : Fin n,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      E a b → E b c → E c d → False := by
    intro a b c d hab' hac' had' hbc' hbd' hcd' hab hbc hcd
    let f : Fin 4 → Fin n := ![a, b, c, d]
    have hf : Function.Injective f := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp [f] at hxy ⊢ <;>
        first | exact absurd hxy hab' | exact absurd hxy hac' | exact absurd hxy had'
              | exact absurd hxy hbc' | exact absurd hxy hbd' | exact absurd hxy hcd'
              | exact absurd hxy.symm hab' | exact absurd hxy.symm hac' | exact absurd hxy.symm had'
              | exact absurd hxy.symm hbc' | exact absurd hxy.symm hbd' | exact absurd hxy.symm hcd'
    let P : (Fin 4 → Bool) → Prop := fun v =>
      (v 0 = false ∨ v 1 = false) ∧ (v 1 = false ∨ v 2 = false) ∧ (v 2 = false ∨ v 3 = false)
    have hP : ∀ w : W n, sat A w = true → P (fun k => decide (w (f k) = pol (f k))) := by
      intro w hw
      rw [hE_sat] at hw
      refine ⟨?_, ?_, ?_⟩
      · rcases hw a b hab with h | h <;> simp [f, h]
      · rcases hw b c hbc with h | h <;> simp [f, h]
      · rcases hw c d hcd with h | h <;> simp [f, h]
    have hb := card_sol_le_of_proj_pol A f hf (fun k => pol (f k)) P hP
    rw [card_P4_le] at hb
    have : 16 * (sol A).card ≤ 8 * 2 ^ n := by simpa using hb
    omega
  have hno_P3K2 : ∀ a b c d e : Fin n,
      a ≠ b → a ≠ c → a ≠ d → a ≠ e → b ≠ c → b ≠ d → b ≠ e → c ≠ d → c ≠ e → d ≠ e →
      E a b → E b c → E d e → False := by
    intro a b c d e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hab hbc hde
    let f : Fin 5 → Fin n := ![a, b, c, d, e]
    have hf : Function.Injective f := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp [f] at hxy ⊢ <;>
        first | exact absurd hxy h1 | exact absurd hxy h2 | exact absurd hxy h3
              | exact absurd hxy h4 | exact absurd hxy h5 | exact absurd hxy h6
              | exact absurd hxy h7 | exact absurd hxy h8 | exact absurd hxy h9
              | exact absurd hxy h10 | exact absurd hxy.symm h1 | exact absurd hxy.symm h2
              | exact absurd hxy.symm h3 | exact absurd hxy.symm h4 | exact absurd hxy.symm h5
              | exact absurd hxy.symm h6 | exact absurd hxy.symm h7 | exact absurd hxy.symm h8
              | exact absurd hxy.symm h9 | exact absurd hxy.symm h10
    let P : (Fin 5 → Bool) → Prop := fun v =>
      (v 0 = false ∨ v 1 = false) ∧ (v 1 = false ∨ v 2 = false) ∧ (v 3 = false ∨ v 4 = false)
    have hP : ∀ w : W n, sat A w = true → P (fun k => decide (w (f k) = pol (f k))) := by
      intro w hw
      rw [hE_sat] at hw
      refine ⟨?_, ?_, ?_⟩
      · rcases hw a b hab with h | h <;> simp [f, h]
      · rcases hw b c hbc with h | h <;> simp [f, h]
      · rcases hw d e hde with h | h <;> simp [f, h]
    have hb := card_sol_le_of_proj_pol A f hf (fun k => pol (f k)) P hP
    rw [card_P3K2_le] at hb
    have : 32 * (sol A).card ≤ 15 * 2 ^ n := by simpa using hb
    omega
  have hno_3K2 : ∀ a b c d e g : Fin n,
      a ≠ b → a ≠ c → a ≠ d → a ≠ e → a ≠ g →
      b ≠ c → b ≠ d → b ≠ e → b ≠ g →
      c ≠ d → c ≠ e → c ≠ g →
      d ≠ e → d ≠ g → e ≠ g →
      E a b → E c d → E e g → False := by
    intro a b c d e g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 hab hcd heg
    let f : Fin 6 → Fin n := ![a, b, c, d, e, g]
    have hf : Function.Injective f := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp [f] at hxy ⊢ <;>
        first | exact absurd hxy h1 | exact absurd hxy h2 | exact absurd hxy h3
              | exact absurd hxy h4 | exact absurd hxy h5 | exact absurd hxy h6
              | exact absurd hxy h7 | exact absurd hxy h8 | exact absurd hxy h9
              | exact absurd hxy h10 | exact absurd hxy h11 | exact absurd hxy h12
              | exact absurd hxy h13 | exact absurd hxy h14 | exact absurd hxy h15
              | exact absurd hxy.symm h1 | exact absurd hxy.symm h2 | exact absurd hxy.symm h3
              | exact absurd hxy.symm h4 | exact absurd hxy.symm h5 | exact absurd hxy.symm h6
              | exact absurd hxy.symm h7 | exact absurd hxy.symm h8 | exact absurd hxy.symm h9
              | exact absurd hxy.symm h10 | exact absurd hxy.symm h11 | exact absurd hxy.symm h12
              | exact absurd hxy.symm h13 | exact absurd hxy.symm h14 | exact absurd hxy.symm h15
    let P : (Fin 6 → Bool) → Prop := fun v =>
      (v 0 = false ∨ v 1 = false) ∧ (v 2 = false ∨ v 3 = false) ∧ (v 4 = false ∨ v 5 = false)
    have hP : ∀ w : W n, sat A w = true → P (fun k => decide (w (f k) = pol (f k))) := by
      intro w hw
      rw [hE_sat] at hw
      refine ⟨?_, ?_, ?_⟩
      · rcases hw a b hab with h | h <;> simp [f, h]
      · rcases hw c d hcd with h | h <;> simp [f, h]
      · rcases hw e g heg with h | h <;> simp [f, h]
    have hb := card_sol_le_of_proj_pol A f hf (fun k => pol (f k)) P hP
    rw [card_3K2_le] at hb
    have : 64 * (sol A).card ≤ 27 * 2 ^ n := by simpa using hb
    omega
  -- Step 3: Existence of two disjoint edges
  have h2disj : ∃ u1 v1 u2 v2 : Fin n,
      E u1 v1 ∧ E u2 v2 ∧ u1 ≠ v1 ∧ u2 ≠ v2 ∧ u1 ≠ u2 ∧ u1 ≠ v2 ∧ v1 ≠ u2 ∧ v1 ≠ v2 := by
    obtain ⟨u1, v1, he1, _, _⟩ := hno_cover ⟨0, hn⟩
    obtain ⟨a, b, hab, hau1, hbu1⟩ := hno_cover u1
    by_cases hav1 : a = v1
    · subst hav1
      obtain ⟨x, y, hxy, hxv1, hyv1⟩ := hno_cover a
      by_cases hxu1 : x = u1
      · subst hxu1
        by_cases hyb : y = b
        · subst hyb; exact absurd (hno_tri x a y he1 hab hxy) id
        · exact ⟨a, b, x, y, hab, hxy, hE_ne hab, hE_ne hxy, hxv1.symm, hyv1.symm, hbu1, Ne.symm hyb⟩
      · by_cases hyu1 : y = u1
        · subst hyu1
          by_cases hxb : x = b
          · subst hxb; exact absurd (hno_tri y a x he1 hab (hE_symm hxy)) id
          · exact ⟨a, b, x, y, hab, hxy, hE_ne hab, hE_ne hxy, hxv1.symm, hyv1.symm, Ne.symm hxb, hbu1⟩
        · exact ⟨u1, a, x, y, he1, hxy, hE_ne he1, hE_ne hxy, Ne.symm hxu1, Ne.symm hyu1, Ne.symm hxv1, Ne.symm hyv1⟩
    · by_cases hbv1 : b = v1
      · subst hbv1
        have hba : E b a := hE_symm hab
        obtain ⟨x, y, hxy, hxv1, hyv1⟩ := hno_cover b
        by_cases hxu1 : x = u1
        · subst hxu1
          by_cases hya : y = a
          · subst hya; exact absurd (hno_tri x b y he1 hba hxy) id
          · exact ⟨b, a, x, y, hba, hxy, hE_ne hba, hE_ne hxy, hxv1.symm, hyv1.symm, hau1, Ne.symm hya⟩
        · by_cases hyu1 : y = u1
          · subst hyu1
            by_cases hxa : x = a
            · subst hxa; exact absurd (hno_tri y b x he1 hba (hE_symm hxy)) id
            · exact ⟨b, a, x, y, hba, hxy, hE_ne hba, hE_ne hxy, hxv1.symm, hyv1.symm, Ne.symm hxa, hau1⟩
          · exact ⟨u1, b, x, y, he1, hxy, hE_ne he1, hE_ne hxy, Ne.symm hxu1, Ne.symm hyu1, Ne.symm hxv1, Ne.symm hyv1⟩
      · exact ⟨u1, v1, a, b, he1, hab, hE_ne he1, hE_ne hab, Ne.symm hau1, Ne.symm hbu1, Ne.symm hav1, Ne.symm hbv1⟩
  obtain ⟨u1, v1, u2, v2, he1, he2, huv1, huv2, hu12, hu1v2, hv1u2, hv12⟩ := h2disj
  -- Step 4: No third edge exists
  have honly : ∀ x y : Fin n, E x y →
      (x = u1 ∧ y = v1) ∨ (x = v1 ∧ y = u1) ∨ (x = u2 ∧ y = v2) ∨ (x = v2 ∧ y = u2) := by
    intro x y hxy
    have hxy_ne : x ≠ y := hE_ne hxy
    by_contra hnot
    push_neg at hnot
    rcases hnot with ⟨hn1, hn2, hn3, hn4⟩
    by_cases hxu1 : x = u1
    · subst hxu1
      have hyv1 : y ≠ v1 := hn1 rfl
      by_cases hyu2 : y = u2
      · subst hyu2; exact hno_P4 v1 x y v2 huv1.symm hv1u2 hv12 hu12 hu1v2 huv2 (hE_symm he1) hxy he2
      · by_cases hyv2 : y = v2
        · subst hyv2; exact hno_P4 v1 x y u2 huv1.symm hv12 hv1u2 hu1v2 hu12 huv2.symm (hE_symm he1) hxy (hE_symm he2)
        · exact hno_P3K2 v1 x y u2 v2 huv1.symm hyv1.symm hv1u2 hv12 hxy_ne hu12 hu1v2 hyu2 hyv2 huv2 (hE_symm he1) hxy he2
    · by_cases hxv1 : x = v1
      · subst hxv1
        have hyu1 : y ≠ u1 := hn2 rfl
        by_cases hyu2 : y = u2
        · subst hyu2; exact hno_P4 u1 x y v2 huv1 hu12 hu1v2 hv1u2 hv12 huv2 he1 hxy he2
        · by_cases hyv2 : y = v2
          · subst hyv2; exact hno_P4 u1 x y u2 huv1 hu1v2 hu12 hv12 hv1u2 huv2.symm he1 hxy (hE_symm he2)
          · exact hno_P3K2 u1 x y u2 v2 huv1 hyu1.symm hu12 hu1v2 hxy_ne hv1u2 hv12 hyu2 hyv2 huv2 he1 hxy he2
      · by_cases hxu2 : x = u2
        · subst hxu2
          have hyv2 : y ≠ v2 := hn3 rfl
          by_cases hyu1 : y = u1
          · subst hyu1; exact hno_P4 v2 x y v1 huv2.symm hu1v2.symm hv12.symm hu12.symm hv1u2.symm huv1 (hE_symm he2) hxy he1
          · by_cases hyv1 : y = v1
            · subst hyv1; exact hno_P4 v2 x y u1 huv2.symm hv12.symm hu1v2.symm hv1u2.symm hu12.symm huv1.symm (hE_symm he2) hxy (hE_symm he1)
            · exact hno_P3K2 v2 x y u1 v1 huv2.symm hyv2.symm hu1v2.symm hv12.symm hxy_ne hu12.symm hv1u2.symm hyu1 hyv1 huv1 (hE_symm he2) hxy he1
        · by_cases hxv2 : x = v2
          · subst hxv2
            have hyu2 : y ≠ u2 := hn4 rfl
            by_cases hyu1 : y = u1
            · subst hyu1; exact hno_P4 u2 x y v1 huv2 hu12.symm hv1u2.symm hu1v2.symm hv12.symm huv1 he2 hxy he1
            · by_cases hyv1 : y = v1
              · subst hyv1; exact hno_P4 u2 x y u1 huv2 hv1u2.symm hu12.symm hv12.symm hu1v2.symm huv1.symm he2 hxy (hE_symm he1)
              · exact hno_P3K2 u2 x y u1 v1 huv2 hyu2.symm hu12.symm hv1u2.symm hxy_ne hu1v2.symm hv12.symm hyu1 hyv1 huv1 he2 hxy he1
          · by_cases hyu1 : y = u1
            · subst hyu1; exact hno_P3K2 v1 y x u2 v2 huv1.symm (Ne.symm hxv1) hv1u2 hv12 hxy_ne.symm hu12 hu1v2 hxu2 hxv2 huv2 (hE_symm he1) (hE_symm hxy) he2
            · by_cases hyv1 : y = v1
              · subst hyv1; exact hno_P3K2 u1 y x u2 v2 huv1 (Ne.symm hxu1) hu12 hu1v2 hxy_ne.symm hv1u2 hv12 hxu2 hxv2 huv2 he1 (hE_symm hxy) he2
              · by_cases hyu2 : y = u2
                · subst hyu2; exact hno_P3K2 v2 y x u1 v1 huv2.symm (Ne.symm hxv2) hu1v2.symm hv12.symm hxy_ne.symm hu12.symm hv1u2.symm hxu1 hxv1 huv1 (hE_symm he2) (hE_symm hxy) he1
                · by_cases hyv2 : y = v2
                  · subst hyv2; exact hno_P3K2 u2 y x u1 v1 huv2 (Ne.symm hxu2) hu12.symm hv1u2.symm hxy_ne.symm hu1v2.symm hv12.symm hxu1 hxv1 huv1 he2 (hE_symm hxy) he1
                  · exact hno_3K2 u1 v1 u2 v2 x y huv1 hu12 hu1v2 (Ne.symm hxu1) (Ne.symm hyu1) hv1u2 hv12 (Ne.symm hxv1) (Ne.symm hyv1) huv2 (Ne.symm hxu2) (Ne.symm hyu2) (Ne.symm hxv2) (Ne.symm hyv2) hxy_ne he1 he2 hxy
  refine ⟨u1, v1, u2, v2, pol u1, pol v1, pol u2, pol v2, fun w => ?_⟩
  rw [hE_sat]
  constructor
  · intro h
    exact ⟨h u1 v1 he1, h u2 v2 he2⟩
  · rintro ⟨h1, h2⟩ x y hxy
    rcases honly x y hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1
    · exact h1.symm
    · exact h2
    · exact h2.symm

lemma hull_exact_of_no_litHalf {n s m : ℕ} (hs : 3 ≤ s) (hsn : s ≤ n)
    {P : Fin m → W n} (hP : IsStrength4Pool P) (A : Formula n)
    (hhigh : high s A)
    (hno : ∀ l : Lit n, ¬ IsLitHalf (posHull P (fun r => sat A (P r))) l) :
    ∀ z : W n, sat (posHull P (fun r => sat A (P r))) z = sat A z := by
  have hnoA : ∀ l : Lit n, ¬ IsLitHalf A l := by
    intro l hl
    exact hno l ((isLitHalf_hull_iff hP A l).mpr hl)
  have hgt : 2 ^ n < 2 * (sol A).card := card_sol_gt_half_of_high hs hhigh
  obtain ⟨u1, v1, u2, v2, bu1, bv1, bu2, bv2, hchar⟩ :=
    two_disjoint_clauses_of_no_litHalf (by omega) A hgt hnoA
  intro z
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact sat_of_sat_posHull P A z
  · intro hzA
    rw [sat_eq_true_iff]
    intro c hc
    by_contra hviol
    push_neg at hviol
    rcases hviol with ⟨hc1, hc2⟩
    rcases (hchar z).mp hzA with ⟨h1, h2⟩
    have hm1 : ∃ m1 : Lit n, z m1.1 = m1.2 ∧
        (∀ w : W n, w m1.1 = m1.2 → w u1 ≠ bu1 ∨ w v1 ≠ bv1) := by
      rcases h1 with h | h
      · exact ⟨(u1, !bu1), bool_eq_not_of_ne h, fun w hw => Or.inl (by simp [hw])⟩
      · exact ⟨(v1, !bv1), bool_eq_not_of_ne h, fun w hw => Or.inr (by simp [hw])⟩
    have hm2 : ∃ m2 : Lit n, z m2.1 = m2.2 ∧
        (∀ w : W n, w m2.1 = m2.2 → w u2 ≠ bu2 ∨ w v2 ≠ bv2) := by
      rcases h2 with h | h
      · exact ⟨(u2, !bu2), bool_eq_not_of_ne h, fun w hw => Or.inl (by simp [hw])⟩
      · exact ⟨(v2, !bv2), bool_eq_not_of_ne h, fun w hw => Or.inr (by simp [hw])⟩
    obtain ⟨m1, hzm1, hsat1⟩ := hm1
    obtain ⟨m2, hzm2, hsat2⟩ := hm2
    let t : Fin 4 → Lit n := ![c.1, c.2, m1, m2]
    have hmt : Matches4 t z := by
      intro a
      fin_cases a <;> simp [t, hc1, hc2, hzm1, hzm2]
    have hcons : Consistent4 t := by
      intro a b hab
      rw [← hmt a, ← hmt b, hab]
    obtain ⟨r, hr⟩ := hP t hcons
    have hrA : sat A (P r) = true := (hchar (P r)).mpr ⟨hsat1 (P r) (hr 2), hsat2 (P r) (hr 3)⟩
    simp only [posHull, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    rcases hc r hrA with h | h
    · exact h (hr 0)
    · exact h (hr 1)

-- ============================================================
-- Section 3: Case 2 - Opposite branch subcube & Phase 2 bound
-- ============================================================

def setBit {n : ℕ} (w : W n) (i : Fin n) (b : Bool) : W n :=
  fun j => if j = i then b else w j

def flipList {n : ℕ} (w : W n) (S : List (Fin n)) : W n :=
  fun j => if j ∈ S then !w j else w j

def forcedSet {n : ℕ} (A : Formula n) (i : Fin n) (w0 : W n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j ≠ i ∧ sat A (flipList w0 [j]) = false)

lemma mem_forcedSet_iff {n : ℕ} {A : Formula n} {i : Fin n} {a : Bool} {w0 : W n}
    (hlit : IsLitHalf A (i, a)) (hw0i : w0 i = !a) (hw0sat : sat A w0 = true) (j : Fin n) :
    j ∈ forcedSet A i w0 ↔
      j ≠ i ∧ ∃ c ∈ A, c = ((i, !a), (j, !w0 j)) ∨ c = ((j, !w0 j), (i, !a)) := by
  simp only [forcedSet, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcl := (isLitHalf_iff_clauses A (i, a)).mp hlit
  have hw0sat' := sat_eq_true_iff.mp hw0sat
  constructor
  · rintro ⟨hji, hfl⟩
    refine ⟨hji, ?_⟩
    obtain ⟨c, hc, h1, h2⟩ := sat_eq_false_iff.mp hfl
    rcases hcl c hc with ⟨ht1, ht2⟩ | hc1 | hc2
    · exfalso
      rw [← ht1] at h2
      rw [h1] at h2
      exact ht2 h2
    · refine ⟨c, hc, Or.inl ?_⟩
      have hw0c := hw0sat' c hc
      have hne2 : w0 c.2.1 ≠ c.2.2 := by
        rcases hw0c with h | h
        · rw [hc1] at h; exact absurd hw0i h
        · exact h
      have h2j : c.2.1 = j := by
        by_contra hne
        simp only [flipList, List.mem_singleton, if_neg hne] at h2
        exact hne2 h2
      have h2b : c.2.2 = !w0 j := by
        rw [h2j] at hne2
        exact bool_eq_not_of_ne hne2.symm
      exact Prod.ext hc1 (Prod.ext h2j h2b)
    · refine ⟨c, hc, Or.inr ?_⟩
      have hw0c := hw0sat' c hc
      have hne1 : w0 c.1.1 ≠ c.1.2 := by
        rcases hw0c with h | h
        · exact h
        · rw [hc2] at h; exact absurd hw0i h
      have h1j : c.1.1 = j := by
        by_contra hne
        simp only [flipList, List.mem_singleton, if_neg hne] at h1
        exact hne1 h1
      have h1b : c.1.2 = !w0 j := by
        rw [h1j] at hne1
        exact bool_eq_not_of_ne hne1.symm
      exact Prod.ext (Prod.ext h1j h1b) hc2
  · rintro ⟨hji, c, hc, rfl | rfl⟩
    · refine ⟨hji, sat_eq_false_iff.mpr ⟨_, hc, ?_, ?_⟩⟩
      · simp [flipList, Ne.symm hji, hw0i]
      · simp [flipList]
    · refine ⟨hji, sat_eq_false_iff.mpr ⟨_, hc, ?_, ?_⟩⟩
      · simp [flipList]
      · simp [flipList, Ne.symm hji, hw0i]

lemma sat_opposite_iff {n : ℕ} {A : Formula n} {i : Fin n} {a : Bool} {w0 : W n}
    (hlit : IsLitHalf A (i, a)) (hw0i : w0 i = !a) (hw0sat : sat A w0 = true)
    (w : W n) (hwi : w i = !a) :
    sat A w = true ↔ ∀ j ∈ forcedSet A i w0, w j = w0 j := by
  have hcl := (isLitHalf_iff_clauses A (i, a)).mp hlit
  have hw0sat' := sat_eq_true_iff.mp hw0sat
  constructor
  · intro hwsat j hj
    obtain ⟨_, c, hc, rfl | rfl⟩ := (mem_forcedSet_iff hlit hw0i hw0sat j).mp hj
    · rcases (sat_eq_true_iff.mp hwsat) _ hc with h | h
      · exact absurd hwi h
      · exact bool_eq_of_ne_not h
    · rcases (sat_eq_true_iff.mp hwsat) _ hc with h | h
      · exact bool_eq_of_ne_not h
      · exact absurd hwi h
  · intro hall
    rw [sat_eq_true_iff]
    intro c hc
    rcases hcl c hc with ⟨ht1, ht2⟩ | hc1 | hc2
    · rw [← ht1]
      exact bool_ne_or_ne (w c.1.1) c.1.2 c.2.2 ht2
    · have hw0c := hw0sat' c hc
      have hne2 : w0 c.2.1 ≠ c.2.2 := by
        rcases hw0c with h | h
        · rw [hc1] at h; exact absurd hw0i h
        · exact h
      by_cases h2i : c.2.1 = i
      · right
        rw [h2i] at hne2 ⊢
        rw [hwi, ← hw0i]
        exact hne2
      · have h2b : c.2.2 = !w0 c.2.1 := bool_eq_not_of_ne hne2.symm
        have hmem : c.2.1 ∈ forcedSet A i w0 := by
          rw [mem_forcedSet_iff hlit hw0i hw0sat]
          exact ⟨h2i, c, hc, Or.inl (Prod.ext hc1 (Prod.ext rfl h2b))⟩
        right
        rw [hall c.2.1 hmem]
        exact hne2
    · have hw0c := hw0sat' c hc
      have hne1 : w0 c.1.1 ≠ c.1.2 := by
        rcases hw0c with h | h
        · exact h
        · rw [hc2] at h; exact absurd hw0i h
      by_cases h1i : c.1.1 = i
      · left
        rw [h1i] at hne1 ⊢
        rw [hwi, ← hw0i]
        exact hne1
      · have h1b : c.1.2 = !w0 c.1.1 := bool_eq_not_of_ne hne1.symm
        have hmem : c.1.1 ∈ forcedSet A i w0 := by
          rw [mem_forcedSet_iff hlit hw0i hw0sat]
          exact ⟨h1i, c, hc, Or.inr (Prod.ext (Prod.ext rfl h1b) hc2)⟩
        left
        rw [hall c.1.1 hmem]
        exact hne1

lemma sat_flipList_iff {n : ℕ} {A : Formula n} {i : Fin n} {a : Bool} {w0 : W n}
    (hlit : IsLitHalf A (i, a)) (hw0i : w0 i = !a) (hw0sat : sat A w0 = true)
    (S : List (Fin n)) (hiS : i ∉ S) :
    sat A (flipList w0 S) = true ↔ ∀ j ∈ S, j ∉ forcedSet A i w0 := by
  have hfl_i : flipList w0 S i = !a := by simp [flipList, hiS, hw0i]
  rw [sat_opposite_iff hlit hw0i hw0sat (flipList w0 S) hfl_i]
  constructor
  · intro hall j hjS hjK
    have h1 := hall j hjK
    simp only [flipList, if_pos hjS] at h1
    cases hw : w0 j <;> simp_all
  · intro hall j hjK
    by_cases hjS : j ∈ S
    · exact absurd hjK (hall j hjS)
    · simp [flipList, hjS]

lemma card_sol_of_litHalf_witness {n : ℕ} {A : Formula n} {i : Fin n} {a : Bool} {w0 : W n}
    (hlit : IsLitHalf A (i, a)) (hw0i : w0 i = !a) (hw0sat : sat A w0 = true) :
    (sol A).card = 2 ^ (n - 1) + 2 ^ (n - 1 - (forcedSet A i w0).card) := by
  let S1 := (sol A).filter (fun w => w i = a)
  let S2 := (sol A).filter (fun w => w i ≠ a)
  have hpart : (sol A).card = S1.card + S2.card := by
    exact (card_filter_add_card_filter_not (s := sol A) (p := fun w => w i = a)).symm
  have hS1 : S1 = Finset.univ.filter (fun w : W n => ∀ j ∈ ({i} : Finset (Fin n)), w j = a) := by
    ext w
    simp only [S1, sol, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hw⟩ j rfl; exact hw
    · intro h; exact ⟨hlit w (h i rfl), h i rfl⟩
  have hS1_card : S1.card = 2 ^ (n - 1) := by
    rw [hS1, card_subcube ({i}) (fun _ => a)]
    simp
  have hiK : i ∉ forcedSet A i w0 := by
    simp [forcedSet]
  have hS2 : S2 = Finset.univ.filter
      (fun w : W n => ∀ j ∈ insert i (forcedSet A i w0), w j = w0 j) := by
    ext w
    simp only [S2, sol, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨hwsat, hne⟩ j (rfl | hjK)
      · rw [hw0i]; exact bool_eq_not_of_ne hne
      · have hwi : w i = !a := bool_eq_not_of_ne hne
        exact (sat_opposite_iff hlit hw0i hw0sat w hwi).mp hwsat j hjK
    · intro hall
      have hwi : w i = !a := by rw [hall i (Or.inl rfl), hw0i]
      have hne : w i ≠ a := by rw [hwi]; cases a <;> decide
      exact ⟨(sat_opposite_iff hlit hw0i hw0sat w hwi).mpr (fun j hj => hall j (Or.inr hj)), hne⟩
  have hS2_card : S2.card = 2 ^ (n - 1 - (forcedSet A i w0).card) := by
    rw [hS2, card_subcube (insert i (forcedSet A i w0)) w0, Finset.card_insert_of_notMem hiK]
    congr 1
    omega
  rw [hpart, hS1_card, hS2_card]

lemma high_iff_card_forcedSet {n s : ℕ} (hs : 3 ≤ s) (hsn : s ≤ n)
    {A : Formula n} {i : Fin n} {a : Bool} {w0 : W n}
    (hlit : IsLitHalf A (i, a)) (hw0i : w0 i = !a) (hw0sat : sat A w0 = true) :
    high s A ↔ (forcedSet A i w0).card ≤ s - 1 := by
  unfold high
  rw [card_sol_of_litHalf_witness hlit hw0i hw0sat]
  have hK_le : (forcedSet A i w0).card ≤ n - 1 := by
    have hsub : forcedSet A i w0 ⊆ Finset.univ.erase i := by
      intro j hj
      simp only [forcedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact Finset.mem_erase.mpr ⟨hj.1, Finset.mem_univ j⟩
    have := Finset.card_le_card hsub
    simpa [Finset.card_erase_of_mem] using this
  have h1 : 2 ^ s * 2 ^ (n - 1) = 2 ^ n * 2 ^ (s - 1) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have h2 : 2 ^ s * 2 ^ (n - 1 - (forcedSet A i w0).card) =
      2 ^ (s + (n - 1 - (forcedSet A i w0).card)) := by
    rw [← pow_add]
  rw [mul_add, mul_one, mul_add, h1, h2]
  constructor
  · intro h
    have hle : 2 ^ n ≤ 2 ^ (s + (n - 1 - (forcedSet A i w0).card)) := by omega
    have hexp : n ≤ s + (n - 1 - (forcedSet A i w0).card) :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
    omega
  · intro h
    have hexp : n ≤ s + (n - 1 - (forcedSet A i w0).card) := by omega
    have hle : 2 ^ n ≤ 2 ^ (s + (n - 1 - (forcedSet A i w0).card)) :=
      Nat.pow_le_pow_right (by norm_num) hexp
    omega

def mkBranchFormula {n : ℕ} (i : Fin n) (a : Bool) (w0 : W n) (found : List (Fin n)) : Formula n :=
  found.toFinset.image (fun j => ((i, !a), (j, !w0 j)))

lemma sat_mkBranchFormula {n : ℕ} {A : Formula n} {i : Fin n} {a : Bool} {w0 : W n}
    (hlit : IsLitHalf A (i, a)) (hw0i : w0 i = !a) (hw0sat : sat A w0 = true)
    (found : List (Fin n)) (hfound : ∀ j : Fin n, j ∈ found ↔ j ∈ forcedSet A i w0) :
    ∀ z : W n, sat (mkBranchFormula i a w0 found) z = sat A z := by
  intro z
  apply Bool.eq_iff_iff.mpr
  by_cases hzi : z i = a
  · constructor
    · intro _; exact hlit z hzi
    · intro _
      rw [sat_eq_true_iff]
      intro c hc
      simp only [mkBranchFormula, Finset.mem_image, List.mem_toFinset] at hc
      rcases hc with ⟨j, _, rfl⟩
      left
      simp [hzi]
  · have hzi' : z i = !a := bool_eq_not_of_ne hzi
    rw [sat_opposite_iff hlit hw0i hw0sat z hzi', sat_eq_true_iff]
    constructor
    · intro h j hjK
      have hmem : ((i, !a), (j, !w0 j)) ∈ mkBranchFormula i a w0 found := by
        simp only [mkBranchFormula, Finset.mem_image, List.mem_toFinset]
        exact ⟨j, (hfound j).mpr hjK, rfl⟩
      rcases h _ hmem with h1 | h1
      · exact absurd hzi' h1
      · exact bool_eq_of_ne_not h1
    · intro h c hc
      simp only [mkBranchFormula, Finset.mem_image, List.mem_toFinset] at hc
      rcases hc with ⟨j, hjf, rfl⟩
      right
      have hzj := h j ((hfound j).mp hjf)
      rw [hzj]
      cases w0 j <;> simp

lemma two_mul_pred_pow_le (m : ℕ) (hm : 1 ≤ m) :
    2 * (m - 1) ^ m ≤ m ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
  simp only [Nat.add_sub_cancel]
  have haux : ∀ j : ℕ, k ^ (j + 1) + (j + 1) * k ^ j ≤ (k + 1) ^ (j + 1) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc k ^ (j + 2) + (j + 2) * k ^ (j + 1)
          ≤ k ^ (j + 2) + (j + 2) * k ^ (j + 1) + (j + 1) * k ^ j := Nat.le_add_right _ _
        _ = (k ^ (j + 1) + (j + 1) * k ^ j) * (k + 1) := by ring
        _ ≤ (k + 1) ^ (j + 1) * (k + 1) := Nat.mul_le_mul_right _ ih
        _ = (k + 1) ^ (j + 2) := by ring
  have hk := haux k
  have heq : k ^ (k + 1) + (k + 1) * k ^ k = 2 * k ^ (k + 1) + k ^ k := by
    rw [pow_succ]
    ring
  omega

lemma phase2_prob_bound {n s : ℕ} (hs : 3 ≤ s) (hsn : s ≤ n)
    {A : Formula n} {i : Fin n} {a : Bool}
    (hlit : IsLitHalf A (i, a)) (hhigh : high s A) :
    3 * Fintype.card (Fin (q2 s) → W n) ≤
      4 * (Finset.univ.filter (fun u : Fin (q2 s) → W n =>
        ∃ r : Fin (q2 s), sat A (setBit (u r) i (!a)) = true)).card := by
  let goodOpp : Finset (W n) :=
    Finset.univ.filter (fun w : W n => w i = !a ∧ sat A w = true)
  let goodW : Finset (W n) :=
    Finset.univ.filter (fun w : W n => sat A (setBit w i (!a)) = true)
  let badW : Finset (W n) :=
    Finset.univ.filter (fun w : W n => sat A (setBit w i (!a)) = false)
  have hsol_split : (sol A).card = 2 ^ (n - 1) + goodOpp.card := by
    let S1 := (sol A).filter (fun w => w i = a)
    let S2 := (sol A).filter (fun w => w i ≠ a)
    have hpart : (sol A).card = S1.card + S2.card :=
      (card_filter_add_card_filter_not (s := sol A) (p := fun w => w i = a)).symm
    have hS1 : S1 = Finset.univ.filter (fun w : W n => ∀ j ∈ ({i} : Finset (Fin n)), w j = a) := by
      ext w
      simp only [S1, sol, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hw⟩ j rfl; exact hw
      · intro h; exact ⟨hlit w (h i rfl), h i rfl⟩
    have hS1c : S1.card = 2 ^ (n - 1) := by
      rw [hS1, card_subcube ({i}) (fun _ => a)]; simp
    have hS2 : S2 = goodOpp := by
      ext w
      simp only [S2, goodOpp, sol, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hsat, hne⟩; exact ⟨bool_eq_not_of_ne hne, hsat⟩
      · rintro ⟨hwi, hsat⟩; exact ⟨hsat, by rw [hwi]; cases a <;> decide⟩
    rw [hpart, hS1c, hS2]
  have hgoodOpp_lb : 2 ^ n ≤ 2 ^ s * goodOpp.card := by
    unfold high at hhigh
    rw [hsol_split] at hhigh
    have h1 : 2 ^ s * 2 ^ (n - 1) = 2 ^ n * 2 ^ (s - 1) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [mul_add, mul_one, mul_add, h1] at hhigh
    omega
  have hgoodW_card : goodW.card = 2 * goodOpp.card := by
    rw [show goodW.card = Fintype.card {w : W n // sat A (setBit w i (!a)) = true} by
          rw [Fintype.card_subtype],
        show goodOpp.card = Fintype.card {w : W n // w i = !a ∧ sat A w = true} by
          rw [Fintype.card_subtype]]
    let e : {w : W n // sat A (setBit w i (!a)) = true} ≃
        Bool × {w : W n // w i = !a ∧ sat A w = true} :=
      { toFun := fun w => (w.1 i, ⟨setBit w.1 i (!a), by simp [setBit], w.2⟩)
        invFun := fun p => ⟨setBit p.2.1 i p.1, by
          have heq : setBit (setBit p.2.1 i p.1) i (!a) = p.2.1 := by
            funext j
            by_cases hj : j = i
            · subst hj; simp [setBit, p.2.2.1]
            · simp [setBit, hj]
          rw [heq]
          exact p.2.2.2⟩
        left_inv := fun w => by
          apply Subtype.ext
          funext j
          by_cases hj : j = i
          · subst hj; simp [setBit]
          · simp [setBit, hj]
        right_inv := fun p => by
          apply Prod.ext
          · simp [setBit]
          · apply Subtype.ext
            funext j
            by_cases hj : j = i
            · subst hj; simp [setBit, p.2.2.1]
            · simp [setBit, hj] }
    rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_bool]
  let m := 2 ^ (s - 1)
  have hm_pos : 1 ≤ m := Nat.one_le_pow _ _ (by norm_num)
  have h2m : 2 * m = q2 s := by
    dsimp only [m, q2]
    have : s = (s - 1) + 1 := by omega
    conv_rhs => rw [this, pow_succ, mul_comm]
  have hbadW_ub : m * badW.card ≤ (m - 1) * 2 ^ n := by
    have hsum : goodW.card + badW.card = 2 ^ n := by
      have := card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (W n))) (p := fun w : W n => sat A (setBit w i (!a)) = true)
      have hneg : Finset.univ.filter (fun w : W n => ¬ sat A (setBit w i (!a)) = true) = badW := by
        ext w; simp [badW]
      rw [hneg] at this
      simpa [W] using this
    have hgoodW_lb : 2 ^ n ≤ m * goodW.card := by
      rw [hgoodW_card]
      calc 2 ^ n ≤ 2 ^ s * goodOpp.card := hgoodOpp_lb
        _ = (2 * m) * goodOpp.card := by rw [h2m]
        _ = m * (2 * goodOpp.card) := by ring
    have hmul : m * goodW.card + m * badW.card = m * 2 ^ n := by
      rw [← mul_add, hsum]
    have hsub_eq : (m - 1) * 2 ^ n + 2 ^ n = m * 2 ^ n := by
      rw [Nat.sub_mul, one_mul]
      have : 2 ^ n ≤ m * 2 ^ n := Nat.le_mul_of_pos_left _ (by omega)
      omega
    omega
  let badTapes : Finset (Fin (q2 s) → W n) :=
    Finset.univ.filter (fun u => ∀ r : Fin (q2 s), sat A (setBit (u r) i (!a)) = false)
  have hbadTapes_card : badTapes.card = badW.card ^ (q2 s) := by
    rw [show badTapes.card = Fintype.card {u : Fin (q2 s) → W n // ∀ r, sat A (setBit (u r) i (!a)) = false} by
      rw [Fintype.card_subtype]]
    let e : {u : Fin (q2 s) → W n // ∀ r, sat A (setBit (u r) i (!a)) = false} ≃
        (Fin (q2 s) → {w : W n // sat A (setBit w i (!a)) = false}) :=
      { toFun := fun u r => ⟨u.1 r, u.2 r⟩
        invFun := fun f => ⟨fun r => (f r).1, fun r => (f r).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_subtype, Fintype.card_fin]
  have h4pow : 4 * (m - 1) ^ (q2 s) ≤ m ^ (q2 s) := by
    rw [← h2m, mul_comm 2 m, pow_mul, pow_mul]
    have h2 := two_mul_pred_pow_le m hm_pos
    have hsq := Nat.mul_le_mul h2 h2
    calc 4 * ((m - 1) ^ m) ^ 2 = (2 * (m - 1) ^ m) * (2 * (m - 1) ^ m) := by ring
      _ ≤ m ^ m * m ^ m := hsq
      _ = (m ^ m) ^ 2 := by ring
  have h4bad : 4 * badTapes.card ≤ Fintype.card (Fin (q2 s) → W n) := by
    have hcardT : Fintype.card (Fin (q2 s) → W n) = (2 ^ n) ^ (q2 s) := by simp [W]
    rw [hcardT, hbadTapes_card]
    have h1 : m ^ (q2 s) * (4 * badW.card ^ (q2 s)) ≤ m ^ (q2 s) * (2 ^ n) ^ (q2 s) := by
      calc m ^ (q2 s) * (4 * badW.card ^ (q2 s))
          = 4 * (m * badW.card) ^ (q2 s) := by rw [mul_pow]; ring
        _ ≤ 4 * ((m - 1) * 2 ^ n) ^ (q2 s) := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hbadW_ub _)
        _ = (4 * (m - 1) ^ (q2 s)) * (2 ^ n) ^ (q2 s) := by rw [mul_pow]; ring
        _ ≤ m ^ (q2 s) * (2 ^ n) ^ (q2 s) := Nat.mul_le_mul_right _ h4pow
    exact Nat.le_of_mul_le_mul_left h1 (Nat.pow_pos (by omega))
  have hcomp : (Finset.univ.filter (fun u : Fin (q2 s) → W n =>
      ∃ r : Fin (q2 s), sat A (setBit (u r) i (!a)) = true)).card + badTapes.card =
      Fintype.card (Fin (q2 s) → W n) := by
    have h1 := card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (q2 s) → W n)))
      (p := fun u => ∃ r : Fin (q2 s), sat A (setBit (u r) i (!a)) = true)
    have hneg : Finset.univ.filter (fun u : Fin (q2 s) → W n =>
        ¬ ∃ r : Fin (q2 s), sat A (setBit (u r) i (!a)) = true) = badTapes := by
      ext u
      simp [badTapes]
    rw [hneg] at h1
    simpa using h1
  omega

-- ============================================================
-- Section 4: Phase 3 block binary search state machine
-- ============================================================

def splitChunks {α : Type*} (L : ℕ) : ℕ → List α → List (List α)
  | 0, _ => []
  | _ + 1, [] => []
  | k + 1, xs => xs.take L :: splitChunks L k (xs.drop L)

lemma splitChunks_length_le {α : Type*} (L : ℕ) :
    ∀ (k : ℕ) (xs : List α), (splitChunks L k xs).length ≤ k
  | 0, _ => by simp [splitChunks]
  | _ + 1, [] => by simp [splitChunks]
  | k + 1, _ :: _ => by
      simp only [splitChunks, List.length_cons]
      exact Nat.succ_le_succ (splitChunks_length_le L k _)

lemma splitChunks_mem_length_le {α : Type*} (L : ℕ) :
    ∀ (k : ℕ) (xs : List α) (b : List α), b ∈ splitChunks L k xs → b.length ≤ L
  | 0, _, _, hb => by simp [splitChunks] at hb
  | _ + 1, [], _, hb => by simp [splitChunks] at hb
  | k + 1, x :: xs, b, hb => by
      simp only [splitChunks, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact List.length_take_le L (x :: xs)
      · exact splitChunks_mem_length_le L k _ b hb

lemma splitChunks_flatten {α : Type*} (L : ℕ) :
    ∀ (k : ℕ) (xs : List α), xs.length ≤ k * L → (splitChunks L k xs).flatten = xs
  | 0, xs, h => by
      simp only [zero_mul, Nat.le_zero, List.length_eq_zero_iff] at h
      subst h
      simp [splitChunks]
  | _ + 1, [], _ => by simp [splitChunks]
  | k + 1, x :: xs, h => by
      simp only [splitChunks, List.flatten_cons]
      have hdrop : ((x :: xs).drop L).length ≤ k * L := by
        simp only [List.length_drop]
        have : (k + 1) * L = k * L + L := by ring
        omega
      rw [splitChunks_flatten L k _ hdrop, List.take_append_drop]

inductive P3State (n : ℕ)
  | testBlock (found : List (Fin n)) (cur : List (Fin n)) (rem : List (List (Fin n)))
  | search (found : List (Fin n)) (left right rest : List (Fin n)) (rem : List (List (Fin n)))
  | done (found : List (Fin n))
  | abort

def p3Query {n : ℕ} : P3State n → List (Fin n)
  | .testBlock _ cur _ => cur
  | .search _ left _ _ _ => left
  | .done _ => []
  | .abort => []

def advanceBlock {n : ℕ} (found : List (Fin n)) : List (List (Fin n)) → P3State n
  | [] => .done found
  | b :: bs => .testBlock found b bs

def enterSearchOrFound {n : ℕ} (found : List (Fin n)) (target rest : List (Fin n))
    (rem : List (List (Fin n))) : P3State n :=
  match target with
  | [] => .abort
  | [x] =>
      match rest with
      | [] => advanceBlock (x :: found) rem
      | r :: rs => .testBlock (x :: found) (r :: rs) rem
  | a :: b :: tail =>
      let full := a :: b :: tail
      let mid := full.length / 2
      .search found (full.take mid) (full.drop mid) rest rem

def p3Step {n : ℕ} (s : ℕ) (st : P3State n) (ans : Bool) : P3State n :=
  match st with
  | .testBlock found cur rem =>
      match ans with
      | true => advanceBlock found rem
      | false =>
          if found.length + 1 ≥ s then
            .abort
          else
            enterSearchOrFound found cur [] rem
  | .search found left right rest rem =>
      match ans with
      | true => enterSearchOrFound found right rest rem
      | false => enterSearchOrFound found left (right ++ rest) rem
  | .done found => .done found
  | .abort => .abort

def p3Init (n s : ℕ) (i : Fin n) : P3State n :=
  let L := (n + s - 1) / s
  let U := (List.finRange n).filter (fun j => j ≠ i)
  advanceBlock [] (splitChunks L s U)

def p3Pot {n : ℕ} (s d : ℕ) : P3State n → ℕ
  | .testBlock found _ rem =>
      (1 + rem.length) + (s - 1 - found.length) * (1 + d)
  | .search found left right _ rem =>
      (1 + rem.length) + (s - 1 - (found.length + 1)) * (1 + d) +
        (1 + Nat.clog 2 (max left.length right.length))
  | .done _ => 0
  | .abort => 0

def p3IsTerminal {n : ℕ} : P3State n → Prop
  | .done _ => True
  | .abort => True
  | _ => False

def P3Inv {n : ℕ} (s L : ℕ) (i : Fin n) (K : Finset (Fin n)) (st : P3State n) : Prop :=
  match st with
  | .testBlock found cur rem =>
      found.Nodup ∧ (∀ x ∈ found, x ∈ K) ∧
      (cur ++ rem.flatten).Nodup ∧
      (∀ x ∈ cur ++ rem.flatten, x ∉ found ∧ x ≠ i) ∧
      (∀ x ∈ K, x ∈ found ∨ x ∈ cur ++ rem.flatten) ∧
      found.length ≤ s - 1 ∧
      cur.length ≤ L ∧ (∀ b ∈ rem, b.length ≤ L) ∧ 1 + rem.length ≤ s
  | .search found left right rest rem =>
      found.Nodup ∧ (∀ x ∈ found, x ∈ K) ∧
      (left ++ right ++ rest ++ rem.flatten).Nodup ∧
      (∀ x ∈ left ++ right ++ rest ++ rem.flatten, x ∉ found ∧ x ≠ i) ∧
      (∀ x ∈ K, x ∈ found ∨ x ∈ left ++ right ++ rest ++ rem.flatten) ∧
      found.length + 1 ≤ s - 1 ∧
      left ≠ [] ∧ right ≠ [] ∧
      (left ++ right ++ rest).length ≤ L ∧
      (∀ b ∈ rem, b.length ≤ L) ∧ 1 + rem.length ≤ s ∧
      (∃ x ∈ left ++ right, x ∈ K)
  | .done found =>
      found.Nodup ∧ (∀ x ∈ found, x ∈ K) ∧
      (∀ x ∈ K, x ∈ found) ∧
      found.length ≤ s - 1
  | .abort =>
      s ≤ K.card

lemma p3Pot_advanceBlock_le {n : ℕ} (s d : ℕ) (found : List (Fin n)) (rem : List (List (Fin n))) :
    p3Pot s d (advanceBlock found rem) ≤ rem.length + (s - 1 - found.length) * (1 + d) := by
  cases rem with
  | nil => simp [advanceBlock, p3Pot]
  | cons b bs => simp [advanceBlock, p3Pot]; omega

lemma p3Pot_enterSearchOrFound_lt {n : ℕ} (s d c : ℕ)
    (found target rest : List (Fin n)) (rem : List (List (Fin n)))
    (hlen : target.length ≤ 2 ^ c) :
    p3Pot s d (enterSearchOrFound found target rest rem) <
      (1 + rem.length) + (s - 1 - (found.length + 1)) * (1 + d) + (1 + c) := by
  match target with
  | [] =>
      simp only [enterSearchOrFound, p3Pot]
      omega
  | [x] =>
      cases rest with
      | nil =>
          simp only [enterSearchOrFound]
          have h1 := p3Pot_advanceBlock_le s d (x :: found) rem
          simp only [List.length_cons] at h1
          omega
      | cons r rs =>
          simp only [enterSearchOrFound, p3Pot, List.length_cons]
          omega
  | a :: b :: tail =>
      simp only [enterSearchOrFound, p3Pot]
      have hge2 : 2 ≤ (a :: b :: tail).length := by simp
      have hc1 : 1 ≤ c := by
        by_contra h0
        have hc0 : c = 0 := by omega
        subst hc0
        simp at hlen
      have hpow_split : 2 ^ c = 2 * 2 ^ (c - 1) := by
        have : c = (c - 1) + 1 := by omega
        conv_lhs => rw [this, pow_succ, mul_comm]
      have htake : ((a :: b :: tail).take ((a :: b :: tail).length / 2)).length ≤ 2 ^ (c - 1) := by
        rw [List.length_take]
        have : (a :: b :: tail).length / 2 ≤ 2 ^ (c - 1) := by omega
        exact le_trans (Nat.min_le_left _ _) this
      have hdrop : ((a :: b :: tail).drop ((a :: b :: tail).length / 2)).length ≤ 2 ^ (c - 1) := by
        rw [List.length_drop]
        omega
      have hmax : max ((a :: b :: tail).take ((a :: b :: tail).length / 2)).length
          ((a :: b :: tail).drop ((a :: b :: tail).length / 2)).length ≤ 2 ^ (c - 1) :=
        Nat.max_le.mpr ⟨htake, hdrop⟩
      have hclog : Nat.clog 2 (max ((a :: b :: tail).take ((a :: b :: tail).length / 2)).length
          ((a :: b :: tail).drop ((a :: b :: tail).length / 2)).length) ≤ c - 1 :=
        (Nat.clog_le_iff_le_pow (by norm_num)).mpr hmax
      omega

lemma p3Inv_advanceBlock {n : ℕ} {s L : ℕ} {i : Fin n} {K : Finset (Fin n)}
    {found : List (Fin n)} {rem : List (List (Fin n))}
    (hfn : found.Nodup) (hfk : ∀ x ∈ found, x ∈ K)
    (hrn : rem.flatten.Nodup) (hrdisj : ∀ x ∈ rem.flatten, x ∉ found ∧ x ≠ i)
    (hcov : ∀ x ∈ K, x ∈ found ∨ x ∈ rem.flatten)
    (hflen : found.length ≤ s - 1)
    (hblen : ∀ b ∈ rem, b.length ≤ L) (hrlen : rem.length ≤ s) :
    P3Inv s L i K (advanceBlock found rem) := by
  cases rem with
  | nil =>
      simp only [advanceBlock, P3Inv]
      refine ⟨hfn, hfk, ?_, hflen⟩
      intro x hx
      rcases hcov x hx with h | h
      · exact h
      · simp at h
  | cons b bs =>
      simp only [advanceBlock, P3Inv]
      simp only [List.flatten_cons] at hrn hrdisj hcov
      simp only [List.length_cons] at hrlen
      refine ⟨hfn, hfk, hrn, hrdisj, hcov, hflen,
        hblen b List.mem_cons_self,
        fun b' hb' => hblen b' (List.mem_cons_of_mem b hb'), by omega⟩

lemma p3Inv_enterSearchOrFound {n : ℕ} {s L : ℕ} {i : Fin n} {K : Finset (Fin n)}
    {found target rest : List (Fin n)} {rem : List (List (Fin n))}
    (hfn : found.Nodup) (hfk : ∀ x ∈ found, x ∈ K)
    (han : (target ++ rest ++ rem.flatten).Nodup)
    (hadisj : ∀ x ∈ target ++ rest ++ rem.flatten, x ∉ found ∧ x ≠ i)
    (hcov : ∀ x ∈ K, x ∈ found ∨ x ∈ target ++ rest ++ rem.flatten)
    (hflen : found.length + 1 ≤ s - 1)
    (htlen : (target ++ rest).length ≤ L)
    (hblen : ∀ b ∈ rem, b.length ≤ L) (hrlen : 1 + rem.length ≤ s)
    (hhit : ∃ x ∈ target, x ∈ K) :
    P3Inv s L i K (enterSearchOrFound found target rest rem) := by
  match target with
  | [] =>
      obtain ⟨x, hx, _⟩ := hhit
      simp at hx
  | [x] =>
      obtain ⟨y, hy, hyK⟩ := hhit
      simp only [List.mem_singleton] at hy
      subst y
      simp only [List.singleton_append, List.cons_append] at han hadisj hcov
      have hxnot : x ∉ rest ++ rem.flatten := (List.nodup_cons.mp han).1
      have hrestn : (rest ++ rem.flatten).Nodup := (List.nodup_cons.mp han).2
      have hx_disj : x ∉ found ∧ x ≠ i := hadisj x List.mem_cons_self
      have hfn' : (x :: found).Nodup := List.nodup_cons.mpr ⟨hx_disj.1, hfn⟩
      have hfk' : ∀ z ∈ x :: found, z ∈ K := by
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hyK
        · exact hfk z hz
      have hdisj' : ∀ z ∈ rest ++ rem.flatten, z ∉ x :: found ∧ z ≠ i := by
        intro z hz
        have h1 := hadisj z (List.mem_cons_of_mem x hz)
        refine ⟨?_, h1.2⟩
        simp only [List.mem_cons, not_or]
        refine ⟨?_, h1.1⟩
        rintro rfl
        exact hxnot hz
      have hcov' : ∀ z ∈ K, z ∈ x :: found ∨ z ∈ rest ++ rem.flatten := by
        intro z hz
        rcases hcov z hz with h | h
        · exact Or.inl (List.mem_cons_of_mem x h)
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl List.mem_cons_self
          · exact Or.inr h
      cases rest with
      | nil =>
          simp only [enterSearchOrFound]
          simp only [List.nil_append] at hrestn hdisj' hcov'
          exact p3Inv_advanceBlock hfn' hfk' hrestn hdisj' hcov'
            (by simpa using hflen) hblen (by omega)
      | cons r rs =>
          simp only [enterSearchOrFound, P3Inv]
          have hrl : (r :: rs).length ≤ L := by
            simp only [List.length_append, List.length_singleton] at htlen
            omega
          exact ⟨hfn', hfk', hrestn, hdisj', hcov', by simpa using hflen, hrl, hblen, hrlen⟩
  | a :: b :: tail =>
      simp only [enterSearchOrFound, P3Inv]
      let full := a :: b :: tail
      let mid := full.length / 2
      have hsplit : full.take mid ++ full.drop mid = full := List.take_append_drop mid full
      have hge2 : 2 ≤ full.length := by simp [full]
      have hltake : (full.take mid).length ≠ 0 := by
        rw [List.length_take]; omega
      have hldrop : (full.drop mid).length ≠ 0 := by
        rw [List.length_drop]; omega
      refine ⟨hfn, hfk, ?_, ?_, ?_, hflen,
        List.ne_nil_of_length_pos (Nat.pos_of_ne_zero hltake),
        List.ne_nil_of_length_pos (Nat.pos_of_ne_zero hldrop),
        ?_, hblen, hrlen, ?_⟩
      · rwa [hsplit]
      · rwa [hsplit]
      · rwa [hsplit]
      · rwa [hsplit]
      · rwa [hsplit]

lemma p3Step_inv_and_pot {n s L d : ℕ} {i : Fin n} {K : Finset (Fin n)}
    (hL : L ≤ 2 ^ d)
    (oracle : List (Fin n) → Bool)
    (horacle : ∀ S : List (Fin n), i ∉ S → (oracle S = true ↔ ∀ x ∈ S, x ∉ K))
    (st : P3State n) (hinv : P3Inv s L i K st) :
    P3Inv s L i K (p3Step s st (oracle (p3Query st))) ∧
    (¬ p3IsTerminal st → p3Pot s d (p3Step s st (oracle (p3Query st))) < p3Pot s d st) := by
  cases st with
  | done found =>
      exact ⟨hinv, fun h => absurd trivial h⟩
  | abort =>
      exact ⟨hinv, fun h => absurd trivial h⟩
  | testBlock found cur rem =>
      rcases hinv with ⟨hfn, hfk, han, hadisj, hcov, hflen, hclen, hblen, hrlen⟩
      have hicur : i ∉ cur := fun hi => (hadisj i (List.mem_append_left _ hi)).2 rfl
      have hor := horacle cur hicur
      simp only [p3Step, p3Query]
      cases hans : oracle cur
      · have hhit : ∃ x ∈ cur, x ∈ K := by
          by_contra hno
          push_neg at hno
          have ht := hor.mpr hno
          rw [hans] at ht
          exact Bool.false_ne_true ht
        by_cases hfull : found.length + 1 ≥ s
        · rw [if_pos hfull]
          constructor
          · simp only [P3Inv]
            obtain ⟨x, hxcur, hxK⟩ := hhit
            have hxf : x ∉ found := (hadisj x (List.mem_append_left _ hxcur)).1
            have hnodup' : (x :: found).Nodup := List.nodup_cons.mpr ⟨hxf, hfn⟩
            have hsub : (x :: found).toFinset ⊆ K := by
              intro y hy
              simp only [List.mem_toFinset, List.mem_cons] at hy
              rcases hy with rfl | hy
              · exact hxK
              · exact hfk y hy
            have hcard : (x :: found).length ≤ K.card := by
              rw [← List.toFinset_card_of_nodup hnodup']
              exact Finset.card_le_card hsub
            simp only [List.length_cons] at hcard
            omega
          · intro _
            simp only [p3Pot]
            omega
        · rw [if_neg hfull]
          have hflen' : found.length + 1 ≤ s - 1 := by omega
          constructor
          · exact p3Inv_enterSearchOrFound (rest := []) hfn hfk
              (by simpa using han) (by simpa using hadisj)
              (by simpa using hcov) hflen' (by simpa using hclen) hblen hrlen hhit
          · intro _
            have hlt := p3Pot_enterSearchOrFound_lt s d d found cur [] rem (le_trans hclen hL)
            change p3Pot s d (enterSearchOrFound found cur [] rem) <
              (1 + rem.length) + (s - 1 - found.length) * (1 + d)
            have hsub : (s - 1 - found.length) * (1 + d) =
                (s - 1 - (found.length + 1)) * (1 + d) + (1 + d) := by
              have : s - 1 - found.length = (s - 1 - (found.length + 1)) + 1 := by omega
              rw [this, add_mul, one_mul]
            omega
      · have hcur_clear : ∀ x ∈ cur, x ∉ K := hor.mp hans
        constructor
        · have hrn : rem.flatten.Nodup := (List.nodup_append.mp han).2.1
          have hrdisj : ∀ x ∈ rem.flatten, x ∉ found ∧ x ≠ i :=
            fun x hx => hadisj x (List.mem_append_right _ hx)
          have hcov' : ∀ x ∈ K, x ∈ found ∨ x ∈ rem.flatten := by
            intro x hx
            rcases hcov x hx with h | h
            · exact Or.inl h
            · rcases List.mem_append.mp h with h | h
              · exact absurd hx (hcur_clear x h)
              · exact Or.inr h
          exact p3Inv_advanceBlock hfn hfk hrn hrdisj hcov' hflen hblen (by omega)
        · intro _
          have h1 := p3Pot_advanceBlock_le s d found rem
          change p3Pot s d (advanceBlock found rem) <
            (1 + rem.length) + (s - 1 - found.length) * (1 + d)
          omega
  | search found left right rest rem =>
      rcases hinv with ⟨hfn, hfk, han, hadisj, hcov, hflen, hlne, hrne, hlen, hblen, hrlen, hhit⟩
      have hileft : i ∉ left := fun hi =>
        (hadisj i (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hi)))).2 rfl
      have hor := horacle left hileft
      let c := Nat.clog 2 (max left.length right.length)
      have hc_bound : max left.length right.length ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) _
      simp only [p3Step, p3Query]
      cases hans : oracle left
      · have hhitL : ∃ x ∈ left, x ∈ K := by
          by_contra hno
          push_neg at hno
          have ht := hor.mpr hno
          rw [hans] at ht
          exact Bool.false_ne_true ht
        constructor
        · have hassoc1 : left ++ (right ++ rest) ++ rem.flatten =
              left ++ right ++ rest ++ rem.flatten := by simp [List.append_assoc]
          have hassoc2 : (left ++ (right ++ rest)).length = (left ++ right ++ rest).length := by
            simp [List.length_append, Nat.add_assoc]
          exact p3Inv_enterSearchOrFound hfn hfk
            (by rwa [hassoc1]) (by rwa [hassoc1]) (by rwa [hassoc1])
            hflen (by rwa [hassoc2]) hblen hrlen hhitL
        · intro _
          have hlle : left.length ≤ 2 ^ c := le_trans (Nat.le_max_left _ _) hc_bound
          exact p3Pot_enterSearchOrFound_lt s d c found left (right ++ rest) rem hlle
      · have hleft_clear : ∀ x ∈ left, x ∉ K := hor.mp hans
        have hhitR : ∃ x ∈ right, x ∈ K := by
          obtain ⟨x, hx, hxK⟩ := hhit
          rcases List.mem_append.mp hx with h | h
          · exact absurd hxK (hleft_clear x h)
          · exact ⟨x, h, hxK⟩
        constructor
        · have hassoc : left ++ right ++ rest ++ rem.flatten =
              left ++ (right ++ rest ++ rem.flatten) := by simp [List.append_assoc]
          rw [hassoc] at han hadisj hcov
          have han' : (right ++ rest ++ rem.flatten).Nodup := (List.nodup_append.mp han).2.1
          have hadisj' : ∀ x ∈ right ++ rest ++ rem.flatten, x ∉ found ∧ x ≠ i :=
            fun x hx => hadisj x (List.mem_append_right _ hx)
          have hcov' : ∀ x ∈ K, x ∈ found ∨ x ∈ right ++ rest ++ rem.flatten := by
            intro x hx
            rcases hcov x hx with h | h
            · exact Or.inl h
            · rcases List.mem_append.mp h with h | h
              · exact absurd hx (hleft_clear x h)
              · exact Or.inr h
          have hlen' : (right ++ rest).length ≤ L := by
            simp only [List.length_append] at hlen ⊢; omega
          exact p3Inv_enterSearchOrFound hfn hfk han' hadisj' hcov' hflen hlen' hblen hrlen hhitR
        · intro _
          have hrle : right.length ≤ 2 ^ c := le_trans (Nat.le_max_right _ _) hc_bound
          exact p3Pot_enterSearchOrFound_lt s d c found right rest rem hrle

lemma p3Init_inv_and_pot {n s : ℕ} (hs : 3 ≤ s) (hsn : s ≤ n) (i : Fin n)
    (K : Finset (Fin n)) (hiK : i ∉ K) :
    let L := (n + s - 1) / s
    let d := Nat.clog 2 L
    P3Inv s L i K (p3Init n s i) ∧ p3Pot s d (p3Init n s i) ≤ q3 n s := by
  intro L d
  let U := (List.finRange n).filter (fun j => j ≠ i)
  have hU_nodup : U.Nodup := (List.nodup_finRange n).filter _
  have hU_len : U.length ≤ s * L := by
    have h1 : U.length ≤ n := by
      calc U.length ≤ (List.finRange n).length := List.length_filter_le _ _
        _ = n := List.length_finRange
    have h2 : n ≤ s * L := by
      have hdm := Nat.div_add_mod (n + s - 1) s
      have hmod := Nat.mod_lt (n + s - 1) (by omega : 0 < s)
      dsimp only [L]
      omega
    omega
  have hflat : (splitChunks L s U).flatten = U := splitChunks_flatten L s U hU_len
  have hchunks_len : (splitChunks L s U).length ≤ s := splitChunks_length_le L s U
  have hblen : ∀ b ∈ splitChunks L s U, b.length ≤ L := splitChunks_mem_length_le L s U
  have hinv : P3Inv s L i K (p3Init n s i) := by
    apply p3Inv_advanceBlock (List.nodup_nil) (by simp)
    · rwa [hflat]
    · intro x hx
      rw [hflat] at hx
      simp only [U, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hx
      exact ⟨by simp, hx⟩
    · intro x hx
      right
      rw [hflat]
      simp only [U, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
      rintro rfl
      exact hiK hx
    · simp only [List.length_nil]; omega
    · exact hblen
    · exact hchunks_len
  have hpot : p3Pot s d (p3Init n s i) ≤ q3 n s := by
    have h1 := p3Pot_advanceBlock_le s d [] (splitChunks L s U)
    simp only [List.length_nil, Nat.sub_zero] at h1
    calc p3Pot s d (p3Init n s i)
        ≤ (splitChunks L s U).length + (s - 1) * (1 + d) := h1
      _ ≤ s + (s - 1) * (1 + d) := Nat.add_le_add_right hchunks_len _
      _ ≤ s * (2 + d) := by
          have : (s - 1) * (1 + d) ≤ s * (1 + d) := Nat.mul_le_mul_right _ (by omega)
          have hmul : s * (2 + d) = s + s * (1 + d) := by ring
          omega
  exact ⟨hinv, hpot⟩

lemma p3Iter_inv_and_term {n s L d : ℕ} {i : Fin n} {K : Finset (Fin n)}
    (hL : L ≤ 2 ^ d)
    (oracle : List (Fin n) → Bool)
    (horacle : ∀ S : List (Fin n), i ∉ S → (oracle S = true ↔ ∀ x ∈ S, x ∉ K))
    (st0 : P3State n) (hinv0 : P3Inv s L i K st0) :
    ∀ t : ℕ,
      let st := (fun st => p3Step s st (oracle (p3Query st)))^[t] st0
      P3Inv s L i K st ∧ (p3Pot s d st0 ≤ t → p3IsTerminal st) := by
  intro t
  induction t generalizing st0 with
  | zero =>
      refine ⟨hinv0, fun hle => ?_⟩
      cases st0 with
      | done _ => trivial
      | abort => trivial
      | testBlock _ _ _ => simp [p3Pot] at hle
      | search _ _ _ _ _ => simp [p3Pot] at hle
  | succ t ih =>
      have h1 := p3Step_inv_and_pot hL oracle horacle st0 hinv0
      have hstep : (fun st => p3Step s st (oracle (p3Query st)))^[t + 1] st0 =
          (fun st => p3Step s st (oracle (p3Query st)))^[t] (p3Step s st0 (oracle (p3Query st0))) :=
        Function.iterate_succ_apply _ t st0
      rw [hstep]
      have hrec := ih (p3Step s st0 (oracle (p3Query st0))) h1.1
      refine ⟨hrec.1, fun hle => ?_⟩
      by_cases hterm : p3IsTerminal st0
      · cases st0 with
        | done _ =>
            apply hrec.2
            simp [p3Step, p3Pot]
        | abort =>
            apply hrec.2
            simp [p3Step, p3Pot]
        | testBlock _ _ _ => exact absurd hterm (by simp [p3IsTerminal])
        | search _ _ _ _ _ => exact absurd hterm (by simp [p3IsTerminal])
      · have hlt := h1.2 hterm
        exact hrec.2 (by omega)

-- ============================================================
-- Section 5: Oracle trace, adaptive learner, and final theorem
-- ============================================================

def runOracle {α : Type*} (oracle : α → Bool) (ask : List Bool → α) : ℕ → List Bool
  | 0 => []
  | k + 1 =>
      let past := runOracle oracle ask k
      past ++ [oracle (ask past)]

lemma foldl_range_eq_runOracle {α : Type*} (oracle : α → Bool) (ask : List Bool → α) (q : ℕ) :
    (List.range q).foldl (fun (past : List Bool) _ => past ++ [oracle (ask past)]) [] =
      runOracle oracle ask q := by
  induction q with
  | zero => rfl
  | succ k ih =>
      rw [List.range_succ, List.foldl_append, ih]
      rfl

lemma runOracle_length {α : Type*} (oracle : α → Bool) (ask : List Bool → α) (k : ℕ) :
    (runOracle oracle ask k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [runOracle, ih]

lemma runOracle_getElem {α : Type*} (oracle : α → Bool) (ask : List Bool → α)
    {k j : ℕ} (hj : j < k) :
    (runOracle oracle ask k)[j]'(by rw [runOracle_length]; exact hj) =
      oracle (ask (runOracle oracle ask j)) := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hjk : j < k
      · simp only [runOracle]
        rw [List.getElem_append_left (by rw [runOracle_length]; exact hjk)]
        exact ih hjk
      · have hjeq : j = k := by omega
        subst hjeq
        simp only [runOracle]
        rw [List.getElem_append_right (by rw [runOracle_length])]
        simp [runOracle_length]

lemma getD_runOracle_eq {α : Type*} (oracle : α → Bool) (ask : List Bool → α)
    {k j : ℕ} (hj : j < k) :
    (runOracle oracle ask k).getD j false = oracle (ask (runOracle oracle ask j)) := by
  rw [List.getD_eq_getElem _ _ (by rw [runOracle_length]; exact hj)]
  exact runOracle_getElem oracle ask hj

noncomputable def buildAsk {n s : ℕ} (pool : Fin (q1 n) → W n)
    (seed : Fin (q2 s) → W n) (past : List Bool) : W n :=
  if h1 : past.length < q1 n then
    pool ⟨past.length, h1⟩
  else
    let ans1 : Fin (q1 n) → Bool := fun r => past.getD r.val false
    let H := posHull pool ans1
    if hlit : ∃ l : Lit n, IsLitHalf H l then
      let l := Classical.choose hlit
      if h2 : past.length < q1 n + q2 s then
        setBit (seed ⟨past.length - q1 n, by omega⟩) l.1 (!l.2)
      else
        let ans2 : Fin (q2 s) → Bool := fun r => past.getD (q1 n + r.val) false
        if hpos : ∃ r : Fin (q2 s), ans2 r = true then
          let r0 := Classical.choose hpos
          let w0 := setBit (seed r0) l.1 (!l.2)
          let st := (past.drop (q1 n + q2 s)).foldl (p3Step s) (p3Init n s l.1)
          flipList w0 (p3Query st)
        else
          fun _ => false
    else
      fun _ => false

noncomputable def buildReport {n s : ℕ} (pool : Fin (q1 n) → W n)
    (seed : Fin (q2 s) → W n) (history : List Bool) : Option (Formula n) :=
  let ans1 : Fin (q1 n) → Bool := fun r => history.getD r.val false
  let H := posHull pool ans1
  if hlit : ∃ l : Lit n, IsLitHalf H l then
    let l := Classical.choose hlit
    let ans2 : Fin (q2 s) → Bool := fun r => history.getD (q1 n + r.val) false
    if hpos : ∃ r : Fin (q2 s), ans2 r = true then
      let r0 := Classical.choose hpos
      let w0 := setBit (seed r0) l.1 (!l.2)
      let st := (history.drop (q1 n + q2 s)).foldl (p3Step s) (p3Init n s l.1)
      match st with
      | .done found => some (mkBranchFormula l.1 l.2 w0 found)
      | _ => none
    else
      none
  else
    if high s H then some H else none

lemma buildAsk_phase1 {n s : ℕ} (pool : Fin (q1 n) → W n) (seed : Fin (q2 s) → W n)
    (past : List Bool) (h1 : past.length < q1 n) :
    buildAsk (s := s) pool seed past = pool ⟨past.length, h1⟩ := by
  unfold buildAsk
  rw [dif_pos h1]

lemma buildAsk_phase2 {n s : ℕ} (pool : Fin (q1 n) → W n) (seed : Fin (q2 s) → W n)
    (past : List Bool) (ans1 : Fin (q1 n) → Bool)
    (h1 : ¬ past.length < q1 n) (h2 : past.length < q1 n + q2 s)
    (hans1 : (fun r : Fin (q1 n) => past.getD r.val false) = ans1)
    (hlit : ∃ l : Lit n, IsLitHalf (posHull pool ans1) l) :
    buildAsk (s := s) pool seed past =
      setBit (seed ⟨past.length - q1 n, by omega⟩) (Classical.choose hlit).1 !(Classical.choose hlit).2 := by
  unfold buildAsk
  rw [dif_neg h1]
  dsimp only
  simp_rw [hans1]
  rw [dif_pos hlit, dif_pos h2]

lemma buildAsk_phase3 {n s : ℕ} (pool : Fin (q1 n) → W n) (seed : Fin (q2 s) → W n)
    (past : List Bool) (ans1 : Fin (q1 n) → Bool) (ans2 : Fin (q2 s) → Bool)
    (h1 : ¬ past.length < q1 n) (h2 : ¬ past.length < q1 n + q2 s)
    (hans1 : (fun r : Fin (q1 n) => past.getD r.val false) = ans1)
    (hlit : ∃ l : Lit n, IsLitHalf (posHull pool ans1) l)
    (hans2 : (fun r : Fin (q2 s) => past.getD (q1 n + r.val) false) = ans2)
    (hpos : ∃ r : Fin (q2 s), ans2 r = true) :
    buildAsk (s := s) pool seed past =
      let l := Classical.choose hlit
      let r0 := Classical.choose hpos
      let w0 := setBit (seed r0) l.1 (!l.2)
      flipList w0 (p3Query ((past.drop (q1 n + q2 s)).foldl (p3Step s) (p3Init n s l.1))) := by
  unfold buildAsk
  rw [dif_neg h1]
  dsimp only
  simp_rw [hans1]
  rw [dif_pos hlit, dif_neg h2]
  have hans2' : ∀ r : Fin (q2 s), past.getD (q1 n + r.val) false = ans2 r :=
    fun r => congrFun hans2 r
  simp_rw [hans2']
  rw [dif_pos hpos]

lemma buildReport_litHalf {n s : ℕ} (pool : Fin (q1 n) → W n) (seed : Fin (q2 s) → W n)
    (history : List Bool) (ans1 : Fin (q1 n) → Bool) (ans2 : Fin (q2 s) → Bool)
    (hans1 : (fun r : Fin (q1 n) => history.getD r.val false) = ans1)
    (hlit : ∃ l : Lit n, IsLitHalf (posHull pool ans1) l)
    (hans2 : (fun r : Fin (q2 s) => history.getD (q1 n + r.val) false) = ans2) :
    buildReport (s := s) pool seed history =
      let l := Classical.choose hlit
      if hpos : ∃ r : Fin (q2 s), ans2 r = true then
        let r0 := Classical.choose hpos
        let w0 := setBit (seed r0) l.1 (!l.2)
        match (history.drop (q1 n + q2 s)).foldl (p3Step s) (p3Init n s l.1) with
        | .done found => some (mkBranchFormula l.1 l.2 w0 found)
        | _ => none
      else none := by
  unfold buildReport
  dsimp only
  simp_rw [hans1]
  rw [dif_pos hlit]
  have hans2' : ∀ r : Fin (q2 s), history.getD (q1 n + r.val) false = ans2 r :=
    fun r => congrFun hans2 r
  simp_rw [hans2']

lemma buildReport_no_litHalf {n s : ℕ} (pool : Fin (q1 n) → W n) (seed : Fin (q2 s) → W n)
    (history : List Bool) (ans1 : Fin (q1 n) → Bool)
    (hans1 : (fun r : Fin (q1 n) => history.getD r.val false) = ans1)
    (hlit : ¬ ∃ l : Lit n, IsLitHalf (posHull pool ans1) l) :
    buildReport (s := s) pool seed history =
      if high s (posHull pool ans1) then some (posHull pool ans1) else none := by
  unfold buildReport
  dsimp only
  simp_rw [hans1]
  rw [dif_neg hlit]

end PEqualNP.Outside.L_lib_676

theorem PEqualNP.Outside.L_lib_676 :
    ∀ (n s : ℕ), 3 ≤ s → s ≤ n →
  let W := Fin n → Bool
  let Lit := Fin n × Bool
  let F := Finset (Lit × Lit)
  let sat := fun (C : F) (w : W) => decide (∀ c ∈ C,
    w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)
  let high := fun (G : F) =>
    2 ^ n * (2 ^ (s - 1) + 1) ≤
      2 ^ s * (Finset.univ.filter (fun x => sat G x = true)).card
  let q := 16 * (1 + 4 * (1 + Nat.clog 2 (n + 1))) + 2 ^ s +
    s * (2 + Nat.clog 2 ((n + s - 1) / s))
  let Tape := Fin (2 ^ s) → W
  ∃ (ask : Tape → List Bool → W) (report : Tape → List Bool → Option F), ∀ A : F,
    let result := fun seed : Tape =>
      let history := (List.range q).foldl (fun (past : List Bool) _ =>
        past ++ [sat A (ask seed past)]) []
      report seed history
    (∀ t B, result t = some B → high A ∧ ∀ z, sat B z = sat A z) ∧
    (high A → 3 * Fintype.card Tape ≤
      4 * (Finset.univ.filter (fun u : Tape => (result u).isSome = true)).card) := by
  open PEqualNP.Outside.L_lib_676 Classical in
  intro n s hs hsn
  obtain ⟨pool, hpool⟩ := exists_strength4_pool n
  refine ⟨buildAsk (s := s) pool, buildReport (s := s) pool, ?_⟩
  intro A
  let q := q1 n + q2 s + q3 n s
  change (∀ t B, buildReport (s := s) pool t
      ((List.range q).foldl (fun (past : List Bool) _ =>
        past ++ [sat A (buildAsk (s := s) pool t past)]) []) = some B →
      high s A ∧ ∀ z, sat B z = sat A z) ∧
    (high s A → 3 * Fintype.card (Fin (q2 s) → W n) ≤
      4 * (Finset.univ.filter (fun u : Fin (q2 s) → W n =>
        (buildReport (s := s) pool u
          ((List.range q).foldl (fun (past : List Bool) _ =>
            past ++ [sat A (buildAsk (s := s) pool u past)]) [])).isSome = true)).card)
  let H := posHull pool (fun r => sat A (pool r))
  have hans1 : ∀ (t : Fin (q2 s) → W n) (k : ℕ), q1 n ≤ k →
      (fun r : Fin (q1 n) => (runOracle (sat A) (buildAsk (s := s) pool t) k).getD r.val false) =
        (fun r => sat A (pool r)) := by
    intro t k hk
    funext r
    rw [getD_runOracle_eq (sat A) (buildAsk (s := s) pool t) (lt_of_lt_of_le r.isLt hk)]
    rw [buildAsk_phase1 pool t _ (by rw [runOracle_length]; exact r.isLt)]
    congr 2
    apply Fin.ext
    exact runOracle_length _ _ _
  have hhist : ∀ t : Fin (q2 s) → W n,
      (List.range q).foldl (fun (past : List Bool) _ =>
        past ++ [sat A (buildAsk (s := s) pool t past)]) [] =
        runOracle (sat A) (buildAsk (s := s) pool t) q :=
    fun t => foldl_range_eq_runOracle (sat A) (buildAsk (s := s) pool t) q
  by_cases hlit : ∃ l : Lit n, IsLitHalf H l
  · -- Case 2: H contains a literal half
    let l := Classical.choose hlit
    have hlH : IsLitHalf H l := Classical.choose_spec hlit
    have hlA : IsLitHalf A l := (isLitHalf_hull_iff hpool A l).mp hlH
    have hans2 : ∀ (t : Fin (q2 s) → W n) (k : ℕ), q1 n + q2 s ≤ k →
        (fun r : Fin (q2 s) =>
          (runOracle (sat A) (buildAsk (s := s) pool t) k).getD (q1 n + r.val) false) =
          (fun r => sat A (setBit (t r) l.1 (!l.2))) := by
      intro t k hk
      funext r
      have hrlt : q1 n + r.val < k := by omega
      rw [getD_runOracle_eq (sat A) (buildAsk (s := s) pool t) hrlt]
      have hlen := runOracle_length (sat A) (buildAsk (s := s) pool t) (q1 n + r.val)
      have h1 : ¬ (runOracle (sat A) (buildAsk (s := s) pool t) (q1 n + r.val)).length < q1 n := by
        omega
      have h2 : (runOracle (sat A) (buildAsk (s := s) pool t) (q1 n + r.val)).length < q1 n + q2 s := by
        omega
      rw [buildAsk_phase2 pool t _ (fun r => sat A (pool r)) h1 h2
        (hans1 t (q1 n + r.val) (by omega)) hlit]
      have hidx : (⟨(runOracle (sat A) (buildAsk (s := s) pool t) (q1 n + r.val)).length - q1 n,
          by omega⟩ : Fin (q2 s)) = r := by
        apply Fin.ext
        simp [hlen]
      rw [hidx]
    have hp3_exec : ∀ (t : Fin (q2 s) → W n)
        (hpos : ∃ r : Fin (q2 s), sat A (setBit (t r) l.1 (!l.2)) = true),
        let r0 := Classical.choose hpos
        let w0 := setBit (t r0) l.1 (!l.2)
        ∀ m : ℕ,
          ((runOracle (sat A) (buildAsk (s := s) pool t) (q1 n + q2 s + m)).drop (q1 n + q2 s)).foldl
            (p3Step s) (p3Init n s l.1) =
            (fun st => p3Step s st (sat A (flipList w0 (p3Query st))))^[m] (p3Init n s l.1) := by
      intro t hpos r0 w0 m
      induction m with
      | zero =>
          simp [List.drop_of_length_le (le_of_eq (runOracle_length _ _ _))]
      | succ m ih =>
          rw [show q1 n + q2 s + (m + 1) = (q1 n + q2 s + m) + 1 by omega, runOracle]
          rw [List.drop_append_of_le_length (by rw [runOracle_length]; omega)]
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
          rw [Function.iterate_succ_apply']
          congr 2
          have hplen := runOracle_length (sat A) (buildAsk (s := s) pool t) (q1 n + q2 s + m)
          have h1 : ¬ (runOracle (sat A) (buildAsk (s := s) pool t) (q1 n + q2 s + m)).length < q1 n := by
            omega
          have h2 : ¬ (runOracle (sat A) (buildAsk (s := s) pool t) (q1 n + q2 s + m)).length < q1 n + q2 s := by
            omega
          rw [buildAsk_phase3 pool t _ (fun r => sat A (pool r))
            (fun r => sat A (setBit (t r) l.1 (!l.2))) h1 h2
            (hans1 t (q1 n + q2 s + m) (by omega)) hlit
            (hans2 t (q1 n + q2 s + m) (by omega)) hpos]
          dsimp only
          rw [ih]
    have hres : ∀ t : Fin (q2 s) → W n,
        buildReport (s := s) pool t (runOracle (sat A) (buildAsk (s := s) pool t) q) =
        if hpos : ∃ r : Fin (q2 s), sat A (setBit (t r) l.1 (!l.2)) = true then
          let r0 := Classical.choose hpos
          let w0 := setBit (t r0) l.1 (!l.2)
          match (fun st => p3Step s st (sat A (flipList w0 (p3Query st))))^[q3 n s] (p3Init n s l.1) with
          | .done found => some (mkBranchFormula l.1 l.2 w0 found)
          | _ => none
        else none := by
      intro t
      rw [buildReport_litHalf pool t _ (fun r => sat A (pool r))
        (fun r => sat A (setBit (t r) l.1 (!l.2)))
        (hans1 t q (by dsimp [q]; omega)) hlit (hans2 t q (by dsimp [q]; omega))]
      dsimp only
      split_ifs with hpos
      · rw [show q = q1 n + q2 s + q3 n s from rfl, hp3_exec t hpos (q3 n s)]
      · rfl
    constructor
    · -- Soundness in Case 2
      intro t B hB
      rw [hhist t, hres t] at hB
      split_ifs at hB with hpos
      · dsimp only at hB
        let r0 := Classical.choose hpos
        let w0 := setBit (t r0) l.1 (!l.2)
        have hw0i : w0 l.1 = !l.2 := by simp [w0, setBit]
        have hw0sat : sat A w0 = true := Classical.choose_spec hpos
        let K := forcedSet A l.1 w0
        have hiK : l.1 ∉ K := by simp [K, forcedSet]
        let L := (n + s - 1) / s
        let d := Nat.clog 2 L
        have hL : L ≤ 2 ^ d := Nat.le_pow_clog (by norm_num) L
        have hinit := p3Init_inv_and_pot hs hsn l.1 K hiK
        have hor : ∀ S : List (Fin n), l.1 ∉ S →
            (sat A (flipList w0 S) = true ↔ ∀ x ∈ S, x ∉ K) :=
          fun S hS => sat_flipList_iff hlA hw0i hw0sat S hS
        have hfinal := p3Iter_inv_and_term (s := s) (L := L) (d := d) hL
          (fun S => sat A (flipList w0 S)) hor (p3Init n s l.1) hinit.1 (q3 n s)
        generalize hst : (fun st => p3Step s st (sat A (flipList w0 (p3Query st))))^[q3 n s]
            (p3Init n s l.1) = st at hB hfinal
        cases st with
        | done found =>
            simp only [Option.some.injEq] at hB
            subst hB
            rcases hfinal.1 with ⟨hfn, hfk, hcov, hflen⟩
            have hiff : ∀ j : Fin n, j ∈ found ↔ j ∈ K :=
              fun j => ⟨hfk j, hcov j⟩
            have hKcard : K.card ≤ s - 1 := by
              have hsub : K ⊆ found.toFinset := by
                intro j hj; exact List.mem_toFinset.mpr (hcov j hj)
              calc K.card ≤ found.toFinset.card := Finset.card_le_card hsub
                _ ≤ found.length := List.toFinset_card_le found
                _ ≤ s - 1 := hflen
            exact ⟨(high_iff_card_forcedSet hs hsn hlA hw0i hw0sat).mpr hKcard,
              sat_mkBranchFormula hlA hw0i hw0sat found hiff⟩
        | testBlock _ _ _ => simp at hB
        | search _ _ _ _ _ => simp at hB
        | abort => simp at hB
    · -- Completeness in Case 2
      intro hhigh
      have hprob := phase2_prob_bound hs hsn hlA hhigh
      refine le_trans hprob (Nat.mul_le_mul_left 4 (Finset.card_le_card ?_))
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      have ht' : ∃ r : Fin (q2 s), sat A (setBit (t r) l.1 (!l.2)) = true := ht
      rw [hhist t, hres t, dif_pos ht']
      dsimp only
      let r0 := Classical.choose ht'
      let w0 := setBit (t r0) l.1 (!l.2)
      have hw0i : w0 l.1 = !l.2 := by simp [w0, setBit]
      have hw0sat : sat A w0 = true := Classical.choose_spec ht'
      let K := forcedSet A l.1 w0
      have hiK : l.1 ∉ K := by simp [K, forcedSet]
      let L := (n + s - 1) / s
      let d := Nat.clog 2 L
      have hL : L ≤ 2 ^ d := Nat.le_pow_clog (by norm_num) L
      have hinit := p3Init_inv_and_pot hs hsn l.1 K hiK
      have hor : ∀ S : List (Fin n), l.1 ∉ S →
          (sat A (flipList w0 S) = true ↔ ∀ x ∈ S, x ∉ K) :=
        fun S hS => sat_flipList_iff hlA hw0i hw0sat S hS
      have hfinal := p3Iter_inv_and_term (s := s) (L := L) (d := d) hL
        (fun S => sat A (flipList w0 S)) hor (p3Init n s l.1) hinit.1 (q3 n s)
      have hterm := hfinal.2 hinit.2
      have hKle : K.card ≤ s - 1 := (high_iff_card_forcedSet hs hsn hlA hw0i hw0sat).mp hhigh
      generalize hst : (fun st => p3Step s st (sat A (flipList w0 (p3Query st))))^[q3 n s]
          (p3Init n s l.1) = st at hfinal hterm ⊢
      cases st with
      | done found => rfl
      | abort =>
          have hab : s ≤ K.card := hfinal.1
          omega
      | testBlock _ _ _ => exact absurd hterm (by simp [p3IsTerminal])
      | search _ _ _ _ _ => exact absurd hterm (by simp [p3IsTerminal])
  · -- Case 1: H contains no literal half
    have hno : ∀ l : Lit n, ¬ IsLitHalf H l := by
      intro l hl; exact hlit ⟨l, hl⟩
    have hres : ∀ t : Fin (q2 s) → W n,
        buildReport (s := s) pool t (runOracle (sat A) (buildAsk (s := s) pool t) q) =
          if high s H then some H else none := by
      intro t
      exact buildReport_no_litHalf pool t _ (fun r => sat A (pool r))
        (hans1 t q (by dsimp [q]; omega)) hlit
    constructor
    · -- Soundness in Case 1
      intro t B hB
      rw [hhist t, hres t] at hB
      by_cases hH : high s H
      · rw [if_pos hH] at hB
        simp only [Option.some.injEq] at hB
        subst hB
        have hhighA : high s A := high_of_sol_subset (sat_of_sat_posHull pool A) hH
        exact ⟨hhighA, hull_exact_of_no_litHalf hs hsn hpool A hhighA hno⟩
      · rw [if_neg hH] at hB
        simp at hB
    · -- Completeness in Case 1
      intro hhighA
      have hexact : ∀ z : W n, sat H z = sat A z :=
        hull_exact_of_no_litHalf hs hsn hpool A hhighA hno
      have hhighH : high s H := (high_congr hexact).mpr hhighA
      have heq : Finset.univ.filter (fun u : Fin (q2 s) → W n =>
          (buildReport (s := s) pool u
            ((List.range q).foldl (fun (past : List Bool) _ =>
              past ++ [sat A (buildAsk (s := s) pool u past)]) [])).isSome = true) =
          Finset.univ := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hhist u, hres u, if_pos hhighH]
        simp
      rw [heq, Finset.card_univ]
      omega
