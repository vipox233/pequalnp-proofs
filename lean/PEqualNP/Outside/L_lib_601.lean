import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_601

open Finset

lemma decide_eq_inv (b s : Bool) : decide (decide (b = s) = s) = b := by
  cases b <;> cases s <;> rfl

lemma card_cyl {n : ℕ} (T : Finset (Fin n)) (x : Fin n → Bool) :
    2 ^ T.card * (Finset.univ.filter (fun y : Fin n → Bool => ∀ i ∈ T, y i = x i)).card = 2 ^ n := by
  classical
  let A := {y : Fin n → Bool // ∀ i ∈ T, y i = x i}
  let B := {i : Fin n // i ∉ T} → Bool
  let e : A ≃ B :=
    { toFun := fun y i => y.1 i.1
      invFun := fun f => ⟨fun i => if h : i ∈ T then x i else f ⟨i, h⟩, by
        intro i hi; simp [hi]⟩
      left_inv := fun ⟨y, hy⟩ => by
        apply Subtype.ext
        funext i
        by_cases h : i ∈ T
        · simp [h, hy i h]
        · simp [h]
      right_inv := fun f => by
        funext ⟨i, hi⟩
        simp [hi] }
  have h1 : (Finset.univ.filter (fun y : Fin n → Bool => ∀ i ∈ T, y i = x i)).card = Fintype.card A := by
    rw [Fintype.card_subtype]
  have h2 : Fintype.card A = Fintype.card B := Fintype.card_congr e
  have h3 : Fintype.card B = 2 ^ (n - T.card) := by
    dsimp only [B]
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
  rw [h1, h2, h3, ← pow_add]
  have hle : T.card ≤ n := by
    have := Finset.card_le_univ T
    simpa using this
  rw [Nat.add_sub_of_le hle]

lemma card_pattern_signed {n m : ℕ} (sites : Fin m → Fin n) (hinj : Function.Injective sites)
    (signs : Fin m → Bool) (P : (Fin m → Bool) → Bool) :
    2 ^ m * (Finset.univ.filter (fun w : Fin n → Bool =>
      P (fun k => decide (w (sites k) = signs k)) = true)).card =
    (Finset.univ.filter (fun v : Fin m → Bool => P v = true)).card * 2 ^ n := by
  classical
  let R : Finset (Fin n) := Finset.univ.image sites
  have hRcard : R.card = m := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hmn : m ≤ n := by
    rw [← hRcard]
    have := Finset.card_le_univ R
    simpa using this
  let A := {w : Fin n → Bool // P (fun k => decide (w (sites k) = signs k)) = true}
  let B := {v : Fin m → Bool // P v = true} × ({i : Fin n // i ∉ R} → Bool)
  let e : A ≃ B :=
    { toFun := fun w =>
        (⟨fun k => decide (w.1 (sites k) = signs k), w.2⟩, fun i => w.1 i.1)
      invFun := fun p =>
        ⟨fun i =>
          if h : i ∈ R then
            let k := Classical.choose (Finset.mem_image.1 h)
            decide (p.1.1 k = signs k)
          else p.2 ⟨i, h⟩, by
          have heq : (fun k => decide ((if h : sites k ∈ R then
              let k' := Classical.choose (Finset.mem_image.1 h)
              decide (p.1.1 k' = signs k')
            else p.2 ⟨sites k, h⟩) = signs k)) = p.1.1 := by
            funext k
            have hk : sites k ∈ R := Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩
            simp only [hk, ↓reduceDIte]
            have hch : Classical.choose (Finset.mem_image.1 hk) = k :=
              hinj (Classical.choose_spec (Finset.mem_image.1 hk)).2
            simp only [hch, decide_eq_inv]
          rw [heq]
          exact p.1.2⟩
      left_inv := fun ⟨w, hw⟩ => by
        apply Subtype.ext
        funext i
        by_cases h : i ∈ R
        · simp only [h, ↓reduceDIte]
          have hspec := (Classical.choose_spec (Finset.mem_image.1 h)).2
          simp only [hspec, decide_eq_inv]
        · simp only [h, ↓reduceDIte]
      right_inv := fun ⟨⟨v, hv⟩, f⟩ => by
        apply Prod.ext
        · apply Subtype.ext
          funext k
          have hk : sites k ∈ R := Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩
          simp only [hk, ↓reduceDIte]
          have hch : Classical.choose (Finset.mem_image.1 hk) = k :=
            hinj (Classical.choose_spec (Finset.mem_image.1 hk)).2
          simp only [hch, decide_eq_inv]
        · funext ⟨i, hi⟩
          simp only [hi, ↓reduceDIte] }
  have h1 : (Finset.univ.filter (fun w : Fin n → Bool =>
      P (fun k => decide (w (sites k) = signs k)) = true)).card = Fintype.card A := by
    rw [Fintype.card_subtype]
  have h2 : Fintype.card A = Fintype.card B := Fintype.card_congr e
  have h3 : Fintype.card B =
      (Finset.univ.filter (fun v : Fin m → Bool => P v = true)).card * 2 ^ (n - m) := by
    dsimp only [B]
    rw [Fintype.card_prod, Fintype.card_subtype, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hRcard]
  rw [h1, h2, h3]
  have hpow : 2 ^ m * 2 ^ (n - m) = 2 ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hmn]
  calc 2 ^ m * ((Finset.univ.filter (fun v : Fin m → Bool => P v = true)).card * 2 ^ (n - m))
      = (Finset.univ.filter (fun v : Fin m → Bool => P v = true)).card * (2 ^ m * 2 ^ (n - m)) := by ring
    _ = (Finset.univ.filter (fun v : Fin m → Bool => P v = true)).card * 2 ^ n := by rw [hpow]

lemma cut_bound {n k : ℕ}
    (A : Finset ((Fin n × Bool) × (Fin n × Bool)))
    (S0 : Finset (Fin n → Bool))
    (hsub : Finset.univ.filter (fun w : Fin n → Bool =>
      decide (∀ c ∈ A, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2) = true) ⊆ S0)
    (hne : Finset.univ.filter (fun w : Fin n → Bool =>
      decide (∀ c ∈ A, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2) = true) ≠ S0)
    (hcert : ∀ x ∈ S0, ∃ T : Finset (Fin n), T.card ≤ k ∧
      ∀ y : Fin n → Bool, (∀ i ∈ T, y i = x i) → y ∈ S0) :
    2 ^ (k + 2) * (Finset.univ.filter (fun w : Fin n → Bool =>
      decide (∀ c ∈ A, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2) = true)).card + 2 ^ n ≤
    2 ^ (k + 2) * S0.card := by
  let S := Finset.univ.filter (fun w : Fin n → Bool =>
    decide (∀ c ∈ A, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2) = true)
  have hex : ∃ x ∈ S0, x ∉ S := by
    by_contra h
    apply hne
    apply Finset.Subset.antisymm hsub
    intro x hx
    by_contra hxS
    exact h ⟨x, hx, hxS⟩
  obtain ⟨x, hx0, hxS⟩ := hex
  have hviol : ∃ c ∈ A, x c.1.1 = c.1.2 ∧ x c.2.1 = c.2.2 := by
    by_contra hall
    apply hxS
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ x, decide_eq_true (fun c hc => ?_)⟩
    by_cases h1 : x c.1.1 = c.1.2
    · right
      intro h2
      exact hall ⟨c, hc, h1, h2⟩
    · exact Or.inl h1
  obtain ⟨c, hcA, hc1, hc2⟩ := hviol
  obtain ⟨T, hTcard, hTcert⟩ := hcert x hx0
  let T' : Finset (Fin n) := insert c.1.1 (insert c.2.1 T)
  have hT'card : T'.card ≤ k + 2 := by
    have h1 : T'.card ≤ (insert c.2.1 T).card + 1 := Finset.card_insert_le c.1.1 (insert c.2.1 T)
    have h2 : (insert c.2.1 T).card ≤ T.card + 1 := Finset.card_insert_le c.2.1 T
    omega
  let Cyl := Finset.univ.filter (fun y : Fin n → Bool => ∀ i ∈ T', y i = x i)
  have hCyl_sub : Cyl ⊆ S0 \ S := by
    intro y hy
    have hy' : ∀ i ∈ T', y i = x i := (Finset.mem_filter.1 hy).2
    rw [Finset.mem_sdiff]
    refine ⟨hTcert y (fun i hi => hy' i (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi))), ?_⟩
    intro hyS
    have hsat := of_decide_eq_true (Finset.mem_filter.1 hyS).2 c hcA
    have hy1 : y c.1.1 = c.1.2 := (hy' c.1.1 (Finset.mem_insert_self _ _)).trans hc1
    have hy2 : y c.2.1 = c.2.2 :=
      (hy' c.2.1 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))).trans hc2
    rcases hsat with h | h
    · exact h hy1
    · exact h hy2
  have hCyl_card : 2 ^ n ≤ 2 ^ (k + 2) * Cyl.card := by
    have hcc : 2 ^ T'.card * Cyl.card = 2 ^ n := card_cyl T' x
    have hpow : 2 ^ T'.card ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) hT'card
    have hmul : 2 ^ T'.card * Cyl.card ≤ 2 ^ (k + 2) * Cyl.card := Nat.mul_le_mul_right Cyl.card hpow
    omega
  have hle : Cyl.card ≤ (S0 \ S).card := Finset.card_le_card hCyl_sub
  have hsdiff : S.card + (S0 \ S).card = S0.card := by
    rw [add_comm]
    exact Finset.card_sdiff_add_card_eq_card hsub
  have hmul2 : 2 ^ (k + 2) * Cyl.card ≤ 2 ^ (k + 2) * (S0 \ S).card :=
    Nat.mul_le_mul_left (2 ^ (k + 2)) hle
  have hmul3 : 2 ^ (k + 2) * S.card + 2 ^ (k + 2) * (S0 \ S).card = 2 ^ (k + 2) * S0.card := by
    rw [← Nat.mul_add, hsdiff]
  change 2 ^ (k + 2) * S.card + 2 ^ n ≤ 2 ^ (k + 2) * S0.card
  omega

lemma count_unary : (Finset.univ.filter (fun v : Fin 1 → Bool => decide (v 0 = false) = true)).card = 1 := by
  decide

lemma count_conflict2 :
    (Finset.univ.filter (fun v : Fin 2 → Bool =>
      decide ((v 0 = true ∨ v 1 = false) ∧ (v 0 = false ∨ v 1 = false)) = true)).card = 2 := by
  decide

lemma count_conflict2b :
    (Finset.univ.filter (fun v : Fin 2 → Bool =>
      decide ((v 0 = false ∨ v 1 = false) ∧ (v 0 = true ∨ v 1 = true)) = true)).card = 2 := by
  decide

lemma count_conflict3 :
    (Finset.univ.filter (fun v : Fin 3 → Bool =>
      decide ((v 0 = false ∨ v 1 = false) ∧ (v 0 = true ∨ v 2 = false)) = true)).card = 4 := by
  decide

lemma count_k3 :
    (Finset.univ.filter (fun v : Fin 3 → Bool =>
      decide (¬(v 0 = true ∧ v 1 = true) ∧ ¬(v 1 = true ∧ v 2 = true) ∧ ¬(v 0 = true ∧ v 2 = true)) = true)).card = 4 := by
  decide

lemma count_2k2 :
    (Finset.univ.filter (fun v : Fin 4 → Bool =>
      decide (¬(v 0 = true ∧ v 1 = true) ∧ ¬(v 2 = true ∧ v 3 = true)) = true)).card = 9 := by
  decide

lemma count_p4 :
    (Finset.univ.filter (fun v : Fin 4 → Bool =>
      decide (¬(v 0 = true ∧ v 1 = true) ∧ ¬(v 1 = true ∧ v 2 = true) ∧ ¬(v 2 = true ∧ v 3 = true)) = true)).card = 8 := by
  decide

lemma count_shape :
    (Finset.univ.filter (fun v : Fin 5 → Bool =>
      decide (¬(v 0 = true ∧ (v 1 = true ∨ v 2 = true)) ∧ ¬(v 3 = true ∧ v 4 = true)) = true)).card = 15 := by
  decide

lemma count_3k2 :
    (Finset.univ.filter (fun v : Fin 6 → Bool =>
      decide (¬(v 0 = true ∧ v 1 = true) ∧ ¬(v 2 = true ∧ v 3 = true) ∧ ¬(v 4 = true ∧ v 5 = true)) = true)).card = 27 := by
  decide

lemma finish_low {n : ℕ} (A : Finset ((Fin n × Bool) × (Fin n × Bool)))
    (hshape_card : (∃ (sites : Fin 5 → Fin n) (signs : Fin 5 → Bool),
      Function.Injective sites ∧ ∀ word : Fin n → Bool,
        decide (∀ c ∈ A, word c.1.1 ≠ c.1.2 ∨ word c.2.1 ≠ c.2.2) =
          decide (¬(word (sites 0) = signs 0 ∧ (word (sites 1) = signs 1 ∨ word (sites 2) = signs 2)) ∧
            ¬(word (sites 3) = signs 3 ∧ word (sites 4) = signs 4))) →
      32 * (Finset.univ.filter (fun z : Fin n → Bool =>
        decide (∀ c ∈ A, z c.1.1 ≠ c.1.2 ∨ z c.2.1 ≠ c.2.2) = true)).card = 15 * 2 ^ n)
    (hlow : 16 * (Finset.univ.filter (fun z : Fin n → Bool =>
      decide (∀ c ∈ A, z c.1.1 ≠ c.1.2 ∨ z c.2.1 ≠ c.2.2) = true)).card ≤ 7 * 2 ^ n) :
    let W := Fin n → Bool
    let sat := fun (C : Finset ((Fin n × Bool) × (Fin n × Bool))) (w : W) =>
      decide (∀ c ∈ C, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)
    let Q := 2 ^ n
    let N := (Finset.univ.filter (fun z => sat A z = true)).card
    let cert := ∀ x : W, sat A x = true →
      ∃ T : Finset (Fin n), T.card ≤ 2 ∧
        ∀ y : W, (∀ i ∈ T, y i = x i) → sat A y = true
    let half := ∃ (j : Fin n) (v : Bool), ∀ p : W, p j = v → sat A p = true
    let shape := ∃ (sites : Fin 5 → Fin n) (signs : Fin 5 → Bool),
      Function.Injective sites ∧ ∀ word : W,
        let mark := fun k : Fin 5 => word (sites k) = signs k
        sat A word = decide (¬(mark 0 ∧ (mark 1 ∨ mark 2)) ∧ ¬(mark 3 ∧ mark 4))
    (Q ≤ 2 * N → half ∨ cert) ∧ (2 * N = Q → cert) ∧
      ((7 * Q < 16 * N ∧ 2 * N < Q) ↔ shape) ∧
      (shape → 32 * N = 15 * Q) := by
  intro W sat Q N cert half shape
  have hQpos : 0 < Q := Nat.pow_pos (by norm_num)
  have hlow' : 16 * N ≤ 7 * Q := hlow
  refine ⟨fun h => by omega, fun h => by omega, ?_, hshape_card⟩
  constructor
  · intro h; omega
  · intro hsh
    have h32 : 32 * N = 15 * Q := hshape_card hsh
    omega

lemma finish_half_core {n : ℕ} (A : Finset ((Fin n × Bool) × (Fin n × Bool)))
    (S0 : Finset (Fin n → Bool))
    (hshape_card : (∃ (sites : Fin 5 → Fin n) (signs : Fin 5 → Bool),
      Function.Injective sites ∧ ∀ word : Fin n → Bool,
        decide (∀ c ∈ A, word c.1.1 ≠ c.1.2 ∨ word c.2.1 ≠ c.2.2) =
          decide (¬(word (sites 0) = signs 0 ∧ (word (sites 1) = signs 1 ∨ word (sites 2) = signs 2)) ∧
            ¬(word (sites 3) = signs 3 ∧ word (sites 4) = signs 4))) →
      32 * (Finset.univ.filter (fun z : Fin n → Bool =>
        decide (∀ c ∈ A, z c.1.1 ≠ c.1.2 ∨ z c.2.1 ≠ c.2.2) = true)).card = 15 * 2 ^ n)
    (hsub : Finset.univ.filter (fun w : Fin n → Bool =>
      decide (∀ c ∈ A, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2) = true) ⊆ S0)
    (hcard0 : 2 * S0.card = 2 ^ n)
    (hcert0 : ∀ x ∈ S0, ∃ T : Finset (Fin n), T.card ≤ 2 ∧
      ∀ y : Fin n → Bool, (∀ i ∈ T, y i = x i) → y ∈ S0) :
    let W := Fin n → Bool
    let sat := fun (C : Finset ((Fin n × Bool) × (Fin n × Bool))) (w : W) =>
      decide (∀ c ∈ C, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)
    let Q := 2 ^ n
    let N := (Finset.univ.filter (fun z => sat A z = true)).card
    let cert := ∀ x : W, sat A x = true →
      ∃ T : Finset (Fin n), T.card ≤ 2 ∧
        ∀ y : W, (∀ i ∈ T, y i = x i) → sat A y = true
    let half := ∃ (j : Fin n) (v : Bool), ∀ p : W, p j = v → sat A p = true
    let shape := ∃ (sites : Fin 5 → Fin n) (signs : Fin 5 → Bool),
      Function.Injective sites ∧ ∀ word : W,
        let mark := fun k : Fin 5 => word (sites k) = signs k
        sat A word = decide (¬(mark 0 ∧ (mark 1 ∨ mark 2)) ∧ ¬(mark 3 ∧ mark 4))
    (Q ≤ 2 * N → half ∨ cert) ∧ (2 * N = Q → cert) ∧
      ((7 * Q < 16 * N ∧ 2 * N < Q) ↔ shape) ∧
      (shape → 32 * N = 15 * Q) := by
  intro W sat Q N cert half shape
  have hQpos : 0 < Q := Nat.pow_pos (by norm_num)
  by_cases heq : Finset.univ.filter (fun w : Fin n → Bool => sat A w = true) = S0
  · have hN : 2 * N = Q := by dsimp only [N, Q]; rw [heq]; exact hcard0
    have hcert : cert := by
      intro x hx
      have hx0 : x ∈ S0 := by rw [← heq]; exact Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩
      obtain ⟨T, hTc, hTy⟩ := hcert0 x hx0
      refine ⟨T, hTc, fun y hy => ?_⟩
      have hy0 : y ∈ S0 := hTy y hy
      rw [← heq] at hy0
      exact (Finset.mem_filter.1 hy0).2
    refine ⟨fun _ => Or.inr hcert, fun _ => hcert, ?_, hshape_card⟩
    constructor
    · intro h; omega
    · intro hsh
      have h32 : 32 * N = 15 * Q := hshape_card hsh
      omega
  · have hcut := cut_bound A S0 hsub heq hcert0
    have h16 : 2 ^ (2 + 2) = 16 := by norm_num
    rw [h16] at hcut
    have hlow : 16 * (Finset.univ.filter (fun z : Fin n → Bool =>
        decide (∀ c ∈ A, z c.1.1 ≠ c.1.2 ∨ z c.2.1 ≠ c.2.2) = true)).card ≤ 7 * 2 ^ n := by
      omega
    exact finish_low A hshape_card hlow

lemma main_proof (n : ℕ) (A : Finset ((Fin n × Bool) × (Fin n × Bool))) :
    let W := Fin n → Bool
    let sat := fun (C : Finset ((Fin n × Bool) × (Fin n × Bool))) (w : W) =>
      decide (∀ c ∈ C, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)
    let Q := 2 ^ n
    let N := (Finset.univ.filter (fun z => sat A z = true)).card
    let cert := ∀ x : W, sat A x = true →
      ∃ T : Finset (Fin n), T.card ≤ 2 ∧
        ∀ y : W, (∀ i ∈ T, y i = x i) → sat A y = true
    let half := ∃ (j : Fin n) (v : Bool), ∀ p : W, p j = v → sat A p = true
    let shape := ∃ (sites : Fin 5 → Fin n) (signs : Fin 5 → Bool),
      Function.Injective sites ∧ ∀ word : W,
        let mark := fun k : Fin 5 => word (sites k) = signs k
        sat A word = decide (¬(mark 0 ∧ (mark 1 ∨ mark 2)) ∧ ¬(mark 3 ∧ mark 4))
    (Q ≤ 2 * N → half ∨ cert) ∧ (2 * N = Q → cert) ∧
      ((7 * Q < 16 * N ∧ 2 * N < Q) ↔ shape) ∧
      (shape → 32 * N = 15 * Q) := by
  classical
  intro W sat Q N cert half shape
  have hQpos : 0 < Q := Nat.pow_pos (by norm_num)
  let S : Finset W := Finset.univ.filter (fun z => sat A z = true)
  have hN_eq : N = S.card := rfl
  have hQ_eq : Q = 2 ^ n := rfl
  have hshape_card : shape → 32 * N = 15 * Q := by
    rintro ⟨sites, signs, hinj, hsat⟩
    have heq : S = Finset.univ.filter (fun w : W =>
        decide (¬(decide (w (sites 0) = signs 0) = true ∧
          (decide (w (sites 1) = signs 1) = true ∨ decide (w (sites 2) = signs 2) = true)) ∧
          ¬(decide (w (sites 3) = signs 3) = true ∧ decide (w (sites 4) = signs 4) = true)) = true) := by
      ext w
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, hsat w, decide_eq_true_eq]
    have hpat := card_pattern_signed sites hinj signs
      (fun v : Fin 5 → Bool =>
        decide (¬(v 0 = true ∧ (v 1 = true ∨ v 2 = true)) ∧ ¬(v 3 = true ∧ v 4 = true)))
    rw [count_shape] at hpat
    have h32 : 2 ^ 5 = 32 := by norm_num
    rw [h32] at hpat
    rw [hN_eq, hQ_eq, heq]
    exact hpat
  by_cases hunary : ∃ c ∈ A, c.1.1 = c.2.1 ∧ c.1.2 = c.2.2
  · obtain ⟨c, hcA, h1, h2⟩ := hunary
    let u := c.1.1
    let a := c.1.2
    let S0 : Finset W := Finset.univ.filter (fun w : W => decide (w u = a) = false)
    have hsub : S ⊆ S0 := by
      intro w hw
      have hsat := of_decide_eq_true (Finset.mem_filter.1 hw).2 c hcA
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ w, ?_⟩
      simp only [decide_eq_false_iff_not]
      intro hwu
      rcases hsat with h | h
      · exact h hwu
      · rw [← h1, ← h2] at h; exact h hwu
    have hcard0 : 2 * S0.card = 2 ^ n := by
      let sites : Fin 1 → Fin n := fun _ => u
      have hinj : Function.Injective sites := fun i j _ => Subsingleton.elim i j
      have hpat := card_pattern_signed sites hinj (fun _ => a) (fun v : Fin 1 → Bool => decide (v 0 = false))
      rw [count_unary] at hpat
      have heq0 : S0 = Finset.univ.filter (fun w : W =>
          decide (decide (w (sites 0) = a) = false) = true) := by
        ext w; simp [S0, sites]
      rw [heq0]
      simpa using hpat
    have hcert0 : ∀ x ∈ S0, ∃ T : Finset (Fin n), T.card ≤ 2 ∧
        ∀ y : W, (∀ i ∈ T, y i = x i) → y ∈ S0 := by
      intro x hx
      refine ⟨{u}, by simp, fun y hy => ?_⟩
      have hxu : y u = x u := hy u (Finset.mem_singleton_self u)
      simpa [S0, hxu] using hx
    exact finish_half_core A S0 hshape_card hsub hcard0 hcert0
  · let hasLit : Fin n → Bool → Prop := fun i a =>
      ∃ c ∈ A, c.1.1 ≠ c.2.1 ∧ (c.1 = (i, a) ∨ c.2 = (i, a))
    by_cases hconf : ∃ i : Fin n, hasLit i false ∧ hasLit i true
    · obtain ⟨i, ⟨c1, hc1A, hne1, hor1⟩, ⟨c2, hc2A, hne2, hor2⟩⟩ := hconf
      have he1 : ∃ j1 : Fin n, ∃ b1 : Bool, j1 ≠ i ∧
          ∀ w : W, sat A w = true → w i ≠ false ∨ w j1 ≠ b1 := by
        rcases hor1 with h1 | h1
        · refine ⟨c1.2.1, c1.2.2, ?_, fun w hw => ?_⟩
          · intro heq; apply hne1; rw [heq]; exact congrArg Prod.fst h1
          · have hs := of_decide_eq_true hw c1 hc1A
            rw [h1] at hs; exact hs
        · refine ⟨c1.1.1, c1.1.2, ?_, fun w hw => ?_⟩
          · intro heq; apply hne1; rw [heq]; exact (congrArg Prod.fst h1).symm
          · have hs := of_decide_eq_true hw c1 hc1A
            rw [h1] at hs; exact hs.symm
      have he2 : ∃ j2 : Fin n, ∃ b2 : Bool, j2 ≠ i ∧
          ∀ w : W, sat A w = true → w i ≠ true ∨ w j2 ≠ b2 := by
        rcases hor2 with h2 | h2
        · refine ⟨c2.2.1, c2.2.2, ?_, fun w hw => ?_⟩
          · intro heq; apply hne2; rw [heq]; exact congrArg Prod.fst h2
          · have hs := of_decide_eq_true hw c2 hc2A
            rw [h2] at hs; exact hs
        · refine ⟨c2.1.1, c2.1.2, ?_, fun w hw => ?_⟩
          · intro heq; apply hne2; rw [heq]; exact (congrArg Prod.fst h2).symm
          · have hs := of_decide_eq_true hw c2 hc2A
            rw [h2] at hs; exact hs.symm
      obtain ⟨j1, b1, hj1, hsat1⟩ := he1
      obtain ⟨j2, b2, hj2, hsat2⟩ := he2
      let S0 : Finset W := Finset.univ.filter (fun w : W =>
        decide ((w i ≠ false ∨ w j1 ≠ b1) ∧ (w i ≠ true ∨ w j2 ≠ b2)) = true)
      have hsub : S ⊆ S0 := by
        intro w hw
        have hws := (Finset.mem_filter.1 hw).2
        exact Finset.mem_filter.2 ⟨Finset.mem_univ w, decide_eq_true ⟨hsat1 w hws, hsat2 w hws⟩⟩
      have hcert0 : ∀ x ∈ S0, ∃ T : Finset (Fin n), T.card ≤ 2 ∧
          ∀ y : W, (∀ k ∈ T, y k = x k) → y ∈ S0 := by
        intro x hx
        have hxs := of_decide_eq_true (Finset.mem_filter.1 hx).2
        cases hxi : x i
        · have hx1 : x j1 ≠ b1 := by
            rcases hxs.1 with h | h
            · exact absurd hxi h
            · exact h
          refine ⟨{i, j1}, Finset.card_le_two, fun y hy => ?_⟩
          have hyi : y i = false := (hy i (by simp)).trans hxi
          have hy1 : y j1 ≠ b1 := by rw [hy j1 (by simp)]; exact hx1
          exact Finset.mem_filter.2 ⟨Finset.mem_univ y, decide_eq_true ⟨Or.inr hy1, Or.inl (by simp [hyi])⟩⟩
        · have hx2 : x j2 ≠ b2 := by
            rcases hxs.2 with h | h
            · exact absurd hxi h
            · exact h
          refine ⟨{i, j2}, Finset.card_le_two, fun y hy => ?_⟩
          have hyi : y i = true := (hy i (by simp)).trans hxi
          have hy2 : y j2 ≠ b2 := by rw [hy j2 (by simp)]; exact hx2
          exact Finset.mem_filter.2 ⟨Finset.mem_univ y, decide_eq_true ⟨Or.inl (by simp [hyi]), Or.inr hy2⟩⟩
      have hcard0 : 2 * S0.card = 2 ^ n := by
        by_cases hj : j1 = j2
        · subst hj
          let sites : Fin 2 → Fin n := fun k => match k with | ⟨0, _⟩ => i | ⟨1, _⟩ => j1
          let sg2 : Fin 2 → Bool := fun k => match k with | ⟨0, _⟩ => false | ⟨1, _⟩ => b1
          have hinj : Function.Injective sites := by
            intro a b hab
            fin_cases a <;> fin_cases b <;> dsimp [sites] at hab ⊢ <;>
              first | rfl | exact absurd hab.symm hj1 | exact absurd hab hj1
          by_cases hb : b1 = b2
          · subst hb
            have hpat := card_pattern_signed sites hinj sg2
              (fun v : Fin 2 → Bool => decide ((v 0 = true ∨ v 1 = false) ∧ (v 0 = false ∨ v 1 = false)))
            rw [count_conflict2] at hpat
            have h4 : 2 ^ 2 = 4 := by norm_num
            rw [h4] at hpat
            have heq0 : S0 = Finset.univ.filter (fun w : W =>
                decide ((decide (w (sites 0) = sg2 0) = true ∨ decide (w (sites 1) = sg2 1) = false) ∧
                  (decide (w (sites 0) = sg2 0) = false ∨ decide (w (sites 1) = sg2 1) = false)) = true) := by
              ext w
              simp only [S0, sites, sg2, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
              cases hwi : w i <;> cases hwj : w j1 <;> cases b1 <;> simp
            dsimp only at hpat
            rw [← heq0] at hpat; omega
          · have hb2 : b2 = !b1 := by cases b1 <;> cases b2 <;> simp_all
            subst hb2
            have hpat := card_pattern_signed sites hinj sg2
              (fun v : Fin 2 → Bool => decide ((v 0 = false ∨ v 1 = false) ∧ (v 0 = true ∨ v 1 = true)))
            rw [count_conflict2b] at hpat
            have h4 : 2 ^ 2 = 4 := by norm_num
            rw [h4] at hpat
            have heq0 : S0 = Finset.univ.filter (fun w : W =>
                decide ((decide (w (sites 0) = sg2 0) = false ∨ decide (w (sites 1) = sg2 1) = false) ∧
                  (decide (w (sites 0) = sg2 0) = true ∨ decide (w (sites 1) = sg2 1) = true)) = true) := by
              ext w
              simp only [S0, sites, sg2, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
              cases hwi : w i <;> cases hwj : w j1 <;> cases b1 <;> simp
            dsimp only at hpat
            rw [← heq0] at hpat; omega
        · let sites : Fin 3 → Fin n := fun k => match k with
            | ⟨0, _⟩ => i | ⟨1, _⟩ => j1 | ⟨2, _⟩ => j2
          let sg3 : Fin 3 → Bool := fun k => match k with
            | ⟨0, _⟩ => false | ⟨1, _⟩ => b1 | ⟨2, _⟩ => b2
          have hinj : Function.Injective sites := by
            intro a b hab
            fin_cases a <;> fin_cases b <;> dsimp [sites] at hab ⊢ <;>
              first | rfl | exact absurd hab.symm hj1 | exact absurd hab.symm hj2
                    | exact absurd hab hj1 | exact absurd hab hj
                    | exact absurd hab hj2 | exact absurd hab.symm hj
          have hpat := card_pattern_signed sites hinj sg3
            (fun v : Fin 3 → Bool => decide ((v 0 = false ∨ v 1 = false) ∧ (v 0 = true ∨ v 2 = false)))
          rw [count_conflict3] at hpat
          have h8 : 2 ^ 3 = 8 := by norm_num
          rw [h8] at hpat
          have heq0 : S0 = Finset.univ.filter (fun w : W =>
              decide ((decide (w (sites 0) = sg3 0) = false ∨ decide (w (sites 1) = sg3 1) = false) ∧
                (decide (w (sites 0) = sg3 0) = true ∨ decide (w (sites 2) = sg3 2) = false)) = true) := by
            ext w
            simp only [S0, sites, sg3, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
            cases hwi : w i <;> cases hwj1 : w j1 <;> cases hwj2 : w j2 <;> cases b1 <;> cases b2 <;> simp
          dsimp only at hpat
          rw [← heq0] at hpat; omega
      exact finish_half_core A S0 hshape_card hsub hcard0 hcert0
    · let sgn : Fin n → Bool := fun i => decide (hasLit i true)
      let E : Fin n → Fin n → Prop := fun u v =>
        u ≠ v ∧ ∃ c ∈ A, (c.1.1 = u ∧ c.2.1 = v) ∨ (c.1.1 = v ∧ c.2.1 = u)
      have hE_symm : ∀ u v, E u v → E v u := by
        intro u v ⟨hne, c, hcA, hor⟩
        exact ⟨hne.symm, c, hcA, hor.symm⟩
      have hsign_of : ∀ (i : Fin n) (a : Bool), hasLit i a → sgn i = a := by
        intro i a hl
        cases a
        · simp only [sgn, decide_eq_false_iff_not]
          intro ht; exact hconf ⟨i, hl, ht⟩
        · simp only [sgn, decide_eq_true_eq]
          exact hl
      have hsat_iff_E : ∀ w : W, sat A w = true ↔
          ∀ u v : Fin n, E u v → ¬ (w u = sgn u ∧ w v = sgn v) := by
        intro w
        rw [decide_eq_true_eq]
        constructor
        · intro hsat u v ⟨hne, c, hcA, hor⟩ ⟨hwu, hwv⟩
          have hc := hsat c hcA
          rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have hs1 : sgn u = c.1.2 :=
              hsign_of u c.1.2 ⟨c, hcA, by rw [h1, h2]; exact hne, Or.inl (Prod.ext h1 rfl)⟩
            have hs2 : sgn v = c.2.2 :=
              hsign_of v c.2.2 ⟨c, hcA, by rw [h1, h2]; exact hne, Or.inr (Prod.ext h2 rfl)⟩
            rw [hs1] at hwu; rw [← h1] at hwu
            rw [hs2] at hwv; rw [← h2] at hwv
            rcases hc with h | h
            · exact h hwu
            · exact h hwv
          · have hs1 : sgn v = c.1.2 :=
              hsign_of v c.1.2 ⟨c, hcA, by rw [h1, h2]; exact hne.symm, Or.inl (Prod.ext h1 rfl)⟩
            have hs2 : sgn u = c.2.2 :=
              hsign_of u c.2.2 ⟨c, hcA, by rw [h1, h2]; exact hne.symm, Or.inr (Prod.ext h2 rfl)⟩
            rw [hs1] at hwv; rw [← h1] at hwv
            rw [hs2] at hwu; rw [← h2] at hwu
            rcases hc with h | h
            · exact h hwv
            · exact h hwu
        · intro hall c hcA
          by_cases hsame : c.1.1 = c.2.1
          · by_cases hsb : c.1.2 = c.2.2
            · exact absurd ⟨c, hcA, hsame, hsb⟩ hunary
            · rw [← hsame]
              cases h1 : w c.1.1 <;> cases h2 : c.1.2 <;> cases h3 : c.2.2 <;> simp_all
          · have hE : E c.1.1 c.2.1 := ⟨hsame, c, hcA, Or.inl ⟨rfl, rfl⟩⟩
            have hs1 : sgn c.1.1 = c.1.2 := hsign_of c.1.1 c.1.2 ⟨c, hcA, hsame, Or.inl rfl⟩
            have hs2 : sgn c.2.1 = c.2.2 := hsign_of c.2.1 c.2.2 ⟨c, hcA, hsame, Or.inr rfl⟩
            have hnot := hall c.1.1 c.2.1 hE
            rw [hs1, hs2] at hnot
            by_cases h1 : w c.1.1 = c.1.2
            · right; intro h2; exact hnot ⟨h1, h2⟩
            · exact Or.inl h1
      by_cases hedge : ∃ u v : Fin n, E u v
      · by_cases h2match : ∃ a1 b1 a2 b2 : Fin n,
            E a1 b1 ∧ E a2 b2 ∧ a1 ≠ a2 ∧ a1 ≠ b2 ∧ b1 ≠ a2 ∧ b1 ≠ b2
        · obtain ⟨a1, b1, a2, b2, hE1, hE2, h12, h14, h23, h24⟩ := h2match
          have hab1 : a1 ≠ b1 := hE1.1
          have hab2 : a2 ≠ b2 := hE2.1
          by_cases h3edge : ∃ u v : Fin n, E u v ∧
              ¬ ((u = a1 ∧ v = b1) ∨ (u = b1 ∧ v = a1) ∨ (u = a2 ∧ v = b2) ∨ (u = b2 ∧ v = a2))
          · obtain ⟨u, v, hEuv, hnot12⟩ := h3edge
            have huv : u ≠ v := hEuv.1
            let M4 : Finset (Fin n) := {a1, b1, a2, b2}
            by_cases hu : u ∈ M4 <;> by_cases hv : v ∈ M4
            · have hp4 : ∃ p0 p1 p2 p3 : Fin n,
                  p0 ≠ p1 ∧ p0 ≠ p2 ∧ p0 ≠ p3 ∧ p1 ≠ p2 ∧ p1 ≠ p3 ∧ p2 ≠ p3 ∧
                  E p0 p1 ∧ E p1 p2 ∧ E p2 p3 := by
                simp only [M4, Finset.mem_insert, Finset.mem_singleton] at hu hv
                rcases hu with hu | hu | hu | hu <;> rcases hv with hv | hv | hv | hv <;>
                  rw [hu, hv] at hEuv hnot12 huv
                · exact absurd rfl huv
                · exact absurd (Or.inl ⟨rfl, rfl⟩) hnot12
                · exact ⟨b1, a1, a2, b2, hab1.symm, h23, h24, h12, h14, hab2, hE_symm _ _ hE1, hEuv, hE2⟩
                · exact ⟨b1, a1, b2, a2, hab1.symm, h24, h23, h14, h12, hab2.symm, hE_symm _ _ hE1, hEuv, hE_symm _ _ hE2⟩
                · exact absurd (Or.inr (Or.inl ⟨rfl, rfl⟩)) hnot12
                · exact absurd rfl huv
                · exact ⟨a1, b1, a2, b2, hab1, h12, h14, h23, h24, hab2, hE1, hEuv, hE2⟩
                · exact ⟨a1, b1, b2, a2, hab1, h14, h12, h24, h23, hab2.symm, hE1, hEuv, hE_symm _ _ hE2⟩
                · exact ⟨b1, a1, a2, b2, hab1.symm, h23, h24, h12, h14, hab2, hE_symm _ _ hE1, hE_symm _ _ hEuv, hE2⟩
                · exact ⟨a1, b1, a2, b2, hab1, h12, h14, h23, h24, hab2, hE1, hE_symm _ _ hEuv, hE2⟩
                · exact absurd rfl huv
                · exact absurd (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) hnot12
                · exact ⟨b1, a1, b2, a2, hab1.symm, h24, h23, h14, h12, hab2.symm, hE_symm _ _ hE1, hE_symm _ _ hEuv, hE_symm _ _ hE2⟩
                · exact ⟨a1, b1, b2, a2, hab1, h14, h12, h24, h23, hab2.symm, hE1, hE_symm _ _ hEuv, hE_symm _ _ hE2⟩
                · exact absurd (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) hnot12
                · exact absurd rfl huv
              obtain ⟨p0, p1, p2, p3, h01, h02, h03, h12', h13, h23', hEp1, hEp2, hEp3⟩ := hp4
              let S0 : Finset W := Finset.univ.filter (fun w : W =>
                decide (¬(w p0 = sgn p0 ∧ w p1 = sgn p1) ∧
                  ¬(w p1 = sgn p1 ∧ w p2 = sgn p2) ∧ ¬(w p2 = sgn p2 ∧ w p3 = sgn p3)) = true)
              have hsub : S ⊆ S0 := by
                intro w hw
                have hE := (hsat_iff_E w).1 (Finset.mem_filter.1 hw).2
                exact Finset.mem_filter.2 ⟨Finset.mem_univ w, decide_eq_true
                  ⟨hE p0 p1 hEp1, hE p1 p2 hEp2, hE p2 p3 hEp3⟩⟩
              have hcard0 : 2 * S0.card = 2 ^ n := by
                let sites : Fin 4 → Fin n := fun k => match k with
                  | ⟨0, _⟩ => p0 | ⟨1, _⟩ => p1 | ⟨2, _⟩ => p2 | ⟨3, _⟩ => p3
                have hinj : Function.Injective sites := by
                  intro x y hxy
                  fin_cases x <;> fin_cases y <;> dsimp [sites] at hxy ⊢ <;>
                    first | rfl | exact absurd hxy h01 | exact absurd hxy h02 | exact absurd hxy h03
                          | exact absurd hxy.symm h01 | exact absurd hxy h12' | exact absurd hxy h13
                          | exact absurd hxy.symm h02 | exact absurd hxy.symm h12' | exact absurd hxy h23'
                          | exact absurd hxy.symm h03 | exact absurd hxy.symm h13 | exact absurd hxy.symm h23'
                have hpat := card_pattern_signed sites hinj (fun k => sgn (sites k))
                  (fun v : Fin 4 → Bool =>
                    decide (¬(v 0 = true ∧ v 1 = true) ∧ ¬(v 1 = true ∧ v 2 = true) ∧ ¬(v 2 = true ∧ v 3 = true)))
                rw [count_p4] at hpat
                have h16 : 2 ^ 4 = 16 := by norm_num
                rw [h16] at hpat
                have heq0 : S0 = Finset.univ.filter (fun w : W =>
                    decide (¬(decide (w (sites 0) = sgn (sites 0)) = true ∧ decide (w (sites 1) = sgn (sites 1)) = true) ∧
                      ¬(decide (w (sites 1) = sgn (sites 1)) = true ∧ decide (w (sites 2) = sgn (sites 2)) = true) ∧
                      ¬(decide (w (sites 2) = sgn (sites 2)) = true ∧ decide (w (sites 3) = sgn (sites 3)) = true)) = true) := by
                  ext w
                  simp only [S0, sites, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
                dsimp only at hpat
                rw [← heq0] at hpat; omega
              have hcert0 : ∀ x ∈ S0, ∃ T : Finset (Fin n), T.card ≤ 2 ∧
                  ∀ y : W, (∀ k ∈ T, y k = x k) → y ∈ S0 := by
                intro x hx
                have ⟨hs1, hs2, hs3⟩ := of_decide_eq_true (Finset.mem_filter.1 hx).2
                by_cases h1 : x p1 = sgn p1
                · have h0 : x p0 ≠ sgn p0 := fun h => hs1 ⟨h, h1⟩
                  have h2 : x p2 ≠ sgn p2 := fun h => hs2 ⟨h1, h⟩
                  refine ⟨{p0, p2}, Finset.card_le_two, fun y hy => ?_⟩
                  have hy0 : y p0 ≠ sgn p0 := by rw [hy p0 (by simp)]; exact h0
                  have hy2 : y p2 ≠ sgn p2 := by rw [hy p2 (by simp)]; exact h2
                  exact Finset.mem_filter.2 ⟨Finset.mem_univ y, decide_eq_true
                    ⟨fun h => hy0 h.1, fun h => hy2 h.2, fun h => hy2 h.1⟩⟩
                · by_cases h2 : x p2 = sgn p2
                  · have h3 : x p3 ≠ sgn p3 := fun h => hs3 ⟨h2, h⟩
                    refine ⟨{p1, p3}, Finset.card_le_two, fun y hy => ?_⟩
                    have hy1 : y p1 ≠ sgn p1 := by rw [hy p1 (by simp)]; exact h1
                    have hy3 : y p3 ≠ sgn p3 := by rw [hy p3 (by simp)]; exact h3
                    exact Finset.mem_filter.2 ⟨Finset.mem_univ y, decide_eq_true
                      ⟨fun h => hy1 h.2, fun h => hy1 h.1, fun h => hy3 h.2⟩⟩
                  · refine ⟨{p1, p2}, Finset.card_le_two, fun y hy => ?_⟩
                    have hy1 : y p1 ≠ sgn p1 := by rw [hy p1 (by simp)]; exact h1
                    have hy2 : y p2 ≠ sgn p2 := by rw [hy p2 (by simp)]; exact h2
                    exact Finset.mem_filter.2 ⟨Finset.mem_univ y, decide_eq_true
                      ⟨fun h => hy1 h.2, fun h => hy1 h.1, fun h => hy2 h.1⟩⟩
              exact finish_half_core A S0 hshape_card hsub hcard0 hcert0
            · have hp3k2 : ∃ sites : Fin 5 → Fin n, Function.Injective sites ∧
                  E (sites 0) (sites 1) ∧ E (sites 0) (sites 2) ∧ E (sites 3) (sites 4) := by
                have hv_ne : v ≠ a1 ∧ v ≠ b1 ∧ v ≠ a2 ∧ v ≠ b2 := by
                  simp only [M4, Finset.mem_insert, Finset.mem_singleton, not_or] at hv
                  exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2⟩
                simp only [M4, Finset.mem_insert, Finset.mem_singleton] at hu
                rcases hu with hu | hu | hu | hu <;> rw [hu] at hEuv
                · refine ⟨fun k => match k with | ⟨0,_⟩ => a1 | ⟨1,_⟩ => b1 | ⟨2,_⟩ => v | ⟨3,_⟩ => a2 | ⟨4,_⟩ => b2,
                    ?_, hE1, hEuv, hE2⟩
                  intro x y hxy; fin_cases x <;> fin_cases y <;> dsimp at hxy ⊢ <;>
                    first | rfl | exact absurd hxy hab1 | exact absurd hxy.symm hab1
                          | exact absurd hxy hv_ne.1.symm | exact absurd hxy.symm hv_ne.1.symm
                          | exact absurd hxy h12 | exact absurd hxy.symm h12
                          | exact absurd hxy h14 | exact absurd hxy.symm h14
                          | exact absurd hxy hv_ne.2.1.symm | exact absurd hxy.symm hv_ne.2.1.symm
                          | exact absurd hxy h23 | exact absurd hxy.symm h23
                          | exact absurd hxy h24 | exact absurd hxy.symm h24
                          | exact absurd hxy hv_ne.2.2.1 | exact absurd hxy.symm hv_ne.2.2.1
                          | exact absurd hxy hv_ne.2.2.2 | exact absurd hxy.symm hv_ne.2.2.2
                          | exact absurd hxy hab2 | exact absurd hxy.symm hab2
                · refine ⟨fun k => match k with | ⟨0,_⟩ => b1 | ⟨1,_⟩ => a1 | ⟨2,_⟩ => v | ⟨3,_⟩ => a2 | ⟨4,_⟩ => b2,
                    ?_, hE_symm _ _ hE1, hEuv, hE2⟩
                  intro x y hxy; fin_cases x <;> fin_cases y <;> dsimp at hxy ⊢ <;>
                    first | rfl | exact absurd hxy hab1 | exact absurd hxy.symm hab1
                          | exact absurd hxy hv_ne.1.symm | exact absurd hxy.symm hv_ne.1.symm
                          | exact absurd hxy h12 | exact absurd hxy.symm h12
                          | exact absurd hxy h14 | exact absurd hxy.symm h14
                          | exact absurd hxy hv_ne.2.1.symm | exact absurd hxy.symm hv_ne.2.1.symm
                          | exact absurd hxy h23 | exact absurd hxy.symm h23
                          | exact absurd hxy h24 | exact absurd hxy.symm h24
                          | exact absurd hxy hv_ne.2.2.1 | exact absurd hxy.symm hv_ne.2.2.1
                          | exact absurd hxy hv_ne.2.2.2 | exact absurd hxy.symm hv_ne.2.2.2
                          | exact absurd hxy hab2 | exact absurd hxy.symm hab2
                · refine ⟨fun k => match k with | ⟨0,_⟩ => a2 | ⟨1,_⟩ => b2 | ⟨2,_⟩ => v | ⟨3,_⟩ => a1 | ⟨4,_⟩ => b1,
                    ?_, hE2, hEuv, hE1⟩
                  intro x y hxy; fin_cases x <;> fin_cases y <;> dsimp at hxy ⊢ <;>
                    first | rfl | exact absurd hxy hab1 | exact absurd hxy.symm hab1
                          | exact absurd hxy hv_ne.1.symm | exact absurd hxy.symm hv_ne.1.symm
                          | exact absurd hxy h12 | exact absurd hxy.symm h12
                          | exact absurd hxy h14 | exact absurd hxy.symm h14
                          | exact absurd hxy hv_ne.2.1.symm | exact absurd hxy.symm hv_ne.2.1.symm
                          | exact absurd hxy h23 | exact absurd hxy.symm h23
                          | exact absurd hxy h24 | exact absurd hxy.symm h24
                          | exact absurd hxy hv_ne.2.2.1 | exact absurd hxy.symm hv_ne.2.2.1
                          | exact absurd hxy hv_ne.2.2.2 | exact absurd hxy.symm hv_ne.2.2.2
                          | exact absurd hxy hab2 | exact absurd hxy.symm hab2
                · refine ⟨fun k => match k with | ⟨0,_⟩ => b2 | ⟨1,_⟩ => a2 | ⟨2,_⟩ => v | ⟨3,_⟩ => a1 | ⟨4,_⟩ => b1,
                    ?_, hE_symm _ _ hE2, hEuv, hE1⟩
                  intro x y hxy; fin_cases x <;> fin_cases y <;> dsimp at hxy ⊢ <;>
                    first | rfl | exact absurd hxy hab1 | exact absurd hxy.symm hab1
                          | exact absurd hxy hv_ne.1.symm | exact absurd hxy.symm hv_ne.1.symm
                          | exact absurd hxy h12 | exact absurd hxy.symm h12
                          | exact absurd hxy h14 | exact absurd hxy.symm h14
                          | exact absurd hxy hv_ne.2.1.symm | exact absurd hxy.symm hv_ne.2.1.symm
                          | exact absurd hxy h23 | exact absurd hxy.symm h23
                          | exact absurd hxy h24 | exact absurd hxy.symm h24
                          | exact absurd hxy hv_ne.2.2.1 | exact absurd hxy.symm hv_ne.2.2.1
                          | exact absurd hxy hv_ne.2.2.2 | exact absurd hxy.symm hv_ne.2.2.2
                          | exact absurd hxy hab2 | exact absurd hxy.symm hab2
              obtain ⟨sites, hinj, hE01, hE02, hE34⟩ := hp3k2
              let signs : Fin 5 → Bool := fun k => sgn (sites k)
              let S0 : Finset W := Finset.univ.filter (fun w : W =>
                decide (¬(w (sites 0) = signs 0 ∧ (w (sites 1) = signs 1 ∨ w (sites 2) = signs 2)) ∧
                  ¬(w (sites 3) = signs 3 ∧ w (sites 4) = signs 4)) = true)
              have hsub : S ⊆ S0 := by
                intro w hw
                have hE := (hsat_iff_E w).1 (Finset.mem_filter.1 hw).2
                refine Finset.mem_filter.2 ⟨Finset.mem_univ w, decide_eq_true ⟨?_, hE _ _ hE34⟩⟩
                rintro ⟨h0, h1 | h2⟩
                · exact hE _ _ hE01 ⟨h0, h1⟩
                · exact hE _ _ hE02 ⟨h0, h2⟩
              have hcard0 : 32 * S0.card = 15 * 2 ^ n := by
                have hpat := card_pattern_signed sites hinj signs
                  (fun v : Fin 5 → Bool =>
                    decide (¬(v 0 = true ∧ (v 1 = true ∨ v 2 = true)) ∧ ¬(v 3 = true ∧ v 4 = true)))
                rw [count_shape] at hpat
                have h32 : 2 ^ 5 = 32 := by norm_num
                rw [h32] at hpat
                have heq0 : S0 = Finset.univ.filter (fun w : W =>
                    decide (¬(decide (w (sites 0) = signs 0) = true ∧
                      (decide (w (sites 1) = signs 1) = true ∨ decide (w (sites 2) = signs 2) = true)) ∧
                      ¬(decide (w (sites 3) = signs 3) = true ∧ decide (w (sites 4) = signs 4) = true)) = true) := by
                  ext w; simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
                rw [heq0]; exact hpat
              have hcert0 : ∀ x ∈ S0, ∃ T : Finset (Fin n), T.card ≤ 3 ∧
                  ∀ y : W, (∀ k ∈ T, y k = x k) → y ∈ S0 := by
                intro x hx
                have ⟨hs1, hs2⟩ := of_decide_eq_true (Finset.mem_filter.1 hx).2
                have h34 : ∃ j ∈ ({sites 3, sites 4} : Finset (Fin n)), x j ≠ sgn j := by
                  by_cases h3 : x (sites 3) = signs 3
                  · exact ⟨sites 4, by simp, fun h4 => hs2 ⟨h3, h4⟩⟩
                  · exact ⟨sites 3, by simp, h3⟩
                obtain ⟨j34, hj34_mem, hj34_ne⟩ := h34
                have h34_ok : ∀ y : W, y j34 = x j34 → ¬(y (sites 3) = signs 3 ∧ y (sites 4) = signs 4) := by
                  intro y hy hboth
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hj34_mem
                  rcases hj34_mem with rfl | rfl
                  · exact hj34_ne (hy.symm.trans hboth.1)
                  · exact hj34_ne (hy.symm.trans hboth.2)
                by_cases h0 : x (sites 0) = signs 0
                · have h1 : x (sites 1) ≠ signs 1 := fun h => hs1 ⟨h0, Or.inl h⟩
                  have h2 : x (sites 2) ≠ signs 2 := fun h => hs1 ⟨h0, Or.inr h⟩
                  refine ⟨insert j34 {sites 1, sites 2}, ?_, fun y hy => ?_⟩
                  · have := Finset.card_insert_le j34 {sites 1, sites 2}
                    have := Finset.card_le_two (a := sites 1) (b := sites 2)
                    omega
                  · refine Finset.mem_filter.2 ⟨Finset.mem_univ y, decide_eq_true ⟨?_, h34_ok y (hy j34 (by simp))⟩⟩
                    rintro ⟨_, h1y | h2y⟩
                    · exact h1 ((hy (sites 1) (by simp)).symm.trans h1y)
                    · exact h2 ((hy (sites 2) (by simp)).symm.trans h2y)
                · refine ⟨{sites 0, j34}, by have := Finset.card_le_two (a := sites 0) (b := j34); omega, fun y hy => ?_⟩
                  refine Finset.mem_filter.2 ⟨Finset.mem_univ y, decide_eq_true ⟨?_, h34_ok y (hy j34 (by simp))⟩⟩
                  rintro ⟨h0y, _⟩
                  exact h0 ((hy (sites 0) (by simp)).symm.trans h0y)
              by_cases heqS : S = S0
              · have hsh : shape := by
                  refine ⟨sites, signs, hinj, fun word => ?_⟩
                  dsimp only
                  have hmem : word ∈ S ↔ word ∈ S0 := by rw [heqS]
                  simp only [S, S0, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
                  cases h1 : sat A word <;> cases h2 : decide (¬(word (sites 0) = signs 0 ∧
                    (word (sites 1) = signs 1 ∨ word (sites 2) = signs 2)) ∧
                    ¬(word (sites 3) = signs 3 ∧ word (sites 4) = signs 4))
                  · rfl
                  · exact absurd (hmem.2 h2) (by rw [h1]; decide)
                  · exact absurd (hmem.1 h1) (by rw [h2]; decide)
                  · rfl
                have h32 := hshape_card hsh
                refine ⟨fun h => by omega, fun h => by omega, ?_, hshape_card⟩
                exact ⟨fun _ => hsh, fun _ => by omega⟩
              · have hcut := cut_bound A S0 hsub heqS hcert0
                have h32 : 2 ^ (3 + 2) = 32 := by norm_num
                rw [h32] at hcut
                change 32 * S.card + 2 ^ n ≤ 32 * S0.card at hcut
                have hlow : 16 * S.card ≤ 7 * 2 ^ n := by omega
                exact finish_low A hshape_card hlow
            · have hp3k2 : ∃ sites : Fin 5 → Fin n, Function.Injective sites ∧
                  E (sites 0) (sites 1) ∧ E (sites 0) (sites 2) ∧ E (sites 3) (sites 4) := by
                have hu_ne : u ≠ a1 ∧ u ≠ b1 ∧ u ≠ a2 ∧ u ≠ b2 := by
                  simp only [M4, Finset.mem_insert, Finset.mem_singleton, not_or] at hu
                  exact ⟨hu.1, hu.2.1, hu.2.2.1, hu.2.2.2⟩
                simp only [M4, Finset.mem_insert, Finset.mem_singleton] at hv
                rcases hv with hv | hv | hv | hv <;> rw [hv] at hEuv
                · refine ⟨fun k => match k with | ⟨0,_⟩ => a1 | ⟨1,_⟩ => b1 | ⟨2,_⟩ => u | ⟨3,_⟩ => a2 | ⟨4,_⟩ => b2,
                    ?_, hE1, hE_symm _ _ hEuv, hE2⟩
                  intro x y hxy; fin_cases x <;> fin_cases y <;> dsimp at hxy ⊢ <;>
                    first | rfl | exact absurd hxy hab1 | exact absurd hxy.symm hab1
                          | exact absurd hxy hu_ne.1.symm | exact absurd hxy.symm hu_ne.1.symm
                          | exact absurd hxy h12 | exact absurd hxy.symm h12
                          | exact absurd hxy h14 | exact absurd hxy.symm h14
                          | exact absurd hxy hu_ne.2.1.symm | exact absurd hxy.symm hu_ne.2.1.symm
                          | exact absurd hxy h23 | exact absurd hxy.symm h23
                          | exact absurd hxy h24 | exact absurd hxy.symm h24
                          | exact absurd hxy hu_ne.2.2.1 | exact absurd hxy.symm hu_ne.2.2.1
                          | exact absurd hxy hu_ne.2.2.2 | exact absurd hxy.symm hu_ne.2.2.2
                          | exact absurd hxy hab2 | exact absurd hxy.symm hab2
                · refine ⟨fun k => match k with | ⟨0,_⟩ => b1 | ⟨1,_⟩ => a1 | ⟨2,_⟩ => u | ⟨3,_⟩ => a2 | ⟨4,_⟩ => b2,
                    ?_, hE_symm _ _ hE1, hE_symm _ _ hEuv, hE2⟩
                  intro x y hxy; fin_cases x <;> fin_cases y <;> dsimp at hxy ⊢ <;>
                    first | rfl | exact absurd hxy hab1 | exact absurd hxy.symm hab1
                          | exact absurd hxy hu_ne.1.symm | exact absurd hxy.symm hu_ne.1.symm
                          | exact absurd hxy h12 | exact absurd hxy.symm h12
                          | exact absurd hxy h14 | exact absurd hxy.symm h14
                          | exact absurd hxy hu_ne.2.1.symm | exact absurd hxy.symm hu_ne.2.1.symm
                          | exact absurd hxy h23 | exact absurd hxy.symm h23
                          | exact absurd hxy h24 | exact absurd hxy.symm h24
                          | exact absurd hxy hu_ne.2.2.1 | exact absurd hxy.symm hu_ne.2.2.1
                          | exact absurd hxy hu_ne.2.2.2 | exact absurd hxy.symm hu_ne.2.2.2
                          | exact absurd hxy hab2 | exact absurd hxy.symm hab2
                · refine ⟨fun k => match k with | ⟨0,_⟩ => a2 | ⟨1,_⟩ => b2 | ⟨2,_⟩ => u | ⟨3,_⟩ => a1 | ⟨4,_⟩ => b1,
                    ?_, hE2, hE_symm _ _ hEuv, hE1⟩
                  intro x y hxy; fin_cases x <;> fin_cases y <;> dsimp at hxy ⊢ <;>
                    first | rfl | exact absurd hxy hab1 | exact absurd hxy.symm hab1
                          | exact absurd hxy hu_ne.1.symm | exact absurd hxy.symm hu_ne.1.symm
                          | exact absurd hxy h12 | exact absurd hxy.symm h12
                          | exact absurd hxy h14 | exact absurd hxy.symm h14
                          | exact absurd hxy hu_ne.2.1.symm | exact absurd hxy.symm hu_ne.2.1.symm
                          | exact absurd hxy h23 | exact absurd hxy.symm h23
                          | exact absurd hxy h24 | exact absurd hxy.symm h24
                          | exact absurd hxy hu_ne.2.2.1 | exact absurd hxy.symm hu_ne.2.2.1
                          | exact absurd hxy hu_ne.2.2.2 | exact absurd hxy.symm hu_ne.2.2.2
                          | exact absurd hxy hab2 | exact absurd hxy.symm hab2
                · refine ⟨fun k => match k with | ⟨0,_⟩ => b2 | ⟨1,_⟩ => a2 | ⟨2,_⟩ => u | ⟨3,_⟩ => a1 | ⟨4,_⟩ => b1,
                    ?_, hE_symm _ _ hE2, hE_symm _ _ hEuv, hE1⟩
                  intro x y hxy; fin_cases x <;> fin_cases y <;> dsimp at hxy ⊢ <;>
                    first | rfl | exact absurd hxy hab1 | exact absurd hxy.symm hab1
                          | exact absurd hxy hu_ne.1.symm | exact absurd hxy.symm hu_ne.1.symm
                          | exact absurd hxy h12 | exact absurd hxy.symm h12
                          | exact absurd hxy h14 | exact absurd hxy.symm h14
                          | exact absurd hxy hu_ne.2.1.symm | exact absurd hxy.symm hu_ne.2.1.symm
                          | exact absurd hxy h23 | exact absurd hxy.symm h23
                          | exact absurd hxy h24 | exact absurd hxy.symm h24
                          | exact absurd hxy hu_ne.2.2.1 | exact absurd hxy.symm hu_ne.2.2.1
                          | exact absurd hxy hu_ne.2.2.2 | exact absurd hxy.symm hu_ne.2.2.2
                          | exact absurd hxy hab2 | exact absurd hxy.symm hab2
              obtain ⟨sites, hinj, hE01, hE02, hE34⟩ := hp3k2
              let signs : Fin 5 → Bool := fun k => sgn (sites k)
              let S0 : Finset W := Finset.univ.filter (fun w : W =>
                decide (¬(w (sites 0) = signs 0 ∧ (w (sites 1) = signs 1 ∨ w (sites 2) = signs 2)) ∧
                  ¬(w (sites 3) = signs 3 ∧ w (sites 4) = signs 4)) = true)
              have hsub : S ⊆ S0 := by
                intro w hw
                have hE := (hsat_iff_E w).1 (Finset.mem_filter.1 hw).2
                refine Finset.mem_filter.2 ⟨Finset.mem_univ w, decide_eq_true ⟨?_, hE _ _ hE34⟩⟩
                rintro ⟨h0, h1 | h2⟩
                · exact hE _ _ hE01 ⟨h0, h1⟩
                · exact hE _ _ hE02 ⟨h0, h2⟩
              have hcard0 : 32 * S0.card = 15 * 2 ^ n := by
                have hpat := card_pattern_signed sites hinj signs
                  (fun v : Fin 5 → Bool =>
                    decide (¬(v 0 = true ∧ (v 1 = true ∨ v 2 = true)) ∧ ¬(v 3 = true ∧ v 4 = true)))
                rw [count_shape] at hpat
                have h32 : 2 ^ 5 = 32 := by norm_num
                rw [h32] at hpat
                have heq0 : S0 = Finset.univ.filter (fun w : W =>
                    decide (¬(decide (w (sites 0) = signs 0) = true ∧
                      (decide (w (sites 1) = signs 1) = true ∨ decide (w (sites 2) = signs 2) = true)) ∧
                      ¬(decide (w (sites 3) = signs 3) = true ∧ decide (w (sites 4) = signs 4) = true)) = true) := by
                  ext w; simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
                rw [heq0]; exact hpat
              have hcert0 : ∀ x ∈ S0, ∃ T : Finset (Fin n), T.card ≤ 3 ∧
                  ∀ y : W, (∀ k ∈ T, y k = x k) → y ∈ S0 := by
                intro x hx
                have ⟨hs1, hs2⟩ := of_decide_eq_true (Finset.mem_filter.1 hx).2
                have h34 : ∃ j ∈ ({sites 3, sites 4} : Finset (Fin n)), x j ≠ sgn j := by
                  by_cases h3 : x (sites 3) = signs 3
                  · exact ⟨sites 4, by simp, fun h4 => hs2 ⟨h3, h4⟩⟩
                  · exact ⟨sites 3, by simp, h3⟩
                obtain ⟨j34, hj34_mem, hj34_ne⟩ := h34
                have h34_ok : ∀ y : W, y j34 = x j34 → ¬(y (sites 3) = signs 3 ∧ y (sites 4) = signs 4) := by
                  intro y hy hboth
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hj34_mem
                  rcases hj34_mem with rfl | rfl
                  · exact hj34_ne (hy.symm.trans hboth.1)
                  · exact hj34_ne (hy.symm.trans hboth.2)
                by_cases h0 : x (sites 0) = signs 0
                · have h1 : x (sites 1) ≠ signs 1 := fun h => hs1 ⟨h0, Or.inl h⟩
                  have h2 : x (sites 2) ≠ signs 2 := fun h => hs1 ⟨h0, Or.inr h⟩
                  refine ⟨insert j34 {sites 1, sites 2}, ?_, fun y hy => ?_⟩
                  · have := Finset.card_insert_le j34 {sites 1, sites 2}
                    have := Finset.card_le_two (a := sites 1) (b := sites 2)
                    omega
                  · refine Finset.mem_filter.2 ⟨Finset.mem_univ y, decide_eq_true ⟨?_, h34_ok y (hy j34 (by simp))⟩⟩
                    rintro ⟨_, h1y | h2y⟩
                    · exact h1 ((hy (sites 1) (by simp)).symm.trans h1y)
                    · exact h2 ((hy (sites 2) (by simp)).symm.trans h2y)
                · refine ⟨{sites 0, j34}, by have := Finset.card_le_two (a := sites 0) (b := j34); omega, fun y hy => ?_⟩
                  refine Finset.mem_filter.2 ⟨Finset.mem_univ y, decide_eq_true ⟨?_, h34_ok y (hy j34 (by simp))⟩⟩
                  rintro ⟨h0y, _⟩
                  exact h0 ((hy (sites 0) (by simp)).symm.trans h0y)
              by_cases heqS : S = S0
              · have hsh : shape := by
                  refine ⟨sites, signs, hinj, fun word => ?_⟩
                  dsimp only
                  have hmem : word ∈ S ↔ word ∈ S0 := by rw [heqS]
                  simp only [S, S0, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
                  cases h1 : sat A word <;> cases h2 : decide (¬(word (sites 0) = signs 0 ∧
                    (word (sites 1) = signs 1 ∨ word (sites 2) = signs 2)) ∧
                    ¬(word (sites 3) = signs 3 ∧ word (sites 4) = signs 4))
                  · rfl
                  · exact absurd (hmem.2 h2) (by rw [h1]; decide)
                  · exact absurd (hmem.1 h1) (by rw [h2]; decide)
                  · rfl
                have h32 := hshape_card hsh
                refine ⟨fun h => by omega, fun h => by omega, ?_, hshape_card⟩
                exact ⟨fun _ => hsh, fun _ => by omega⟩
              · have hcut := cut_bound A S0 hsub heqS hcert0
                have h32 : 2 ^ (3 + 2) = 32 := by norm_num
                rw [h32] at hcut
                change 32 * S.card + 2 ^ n ≤ 32 * S0.card at hcut
                have hlow : 16 * S.card ≤ 7 * 2 ^ n := by omega
                exact finish_low A hshape_card hlow
            · have hu_ne : u ≠ a1 ∧ u ≠ b1 ∧ u ≠ a2 ∧ u ≠ b2 := by
                simp only [M4, Finset.mem_insert, Finset.mem_singleton, not_or] at hu
                exact ⟨hu.1, hu.2.1, hu.2.2.1, hu.2.2.2⟩
              have hv_ne : v ≠ a1 ∧ v ≠ b1 ∧ v ≠ a2 ∧ v ≠ b2 := by
                simp only [M4, Finset.mem_insert, Finset.mem_singleton, not_or] at hv
                exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2⟩
              let sites : Fin 6 → Fin n := fun k => match k with
                | ⟨0,_⟩ => a1 | ⟨1,_⟩ => b1 | ⟨2,_⟩ => a2 | ⟨3,_⟩ => b2 | ⟨4,_⟩ => u | ⟨5,_⟩ => v
              have hinj : Function.Injective sites := by
                intro x y hxy; fin_cases x <;> fin_cases y <;> dsimp [sites] at hxy ⊢ <;>
                  first | rfl | exact absurd hxy hab1 | exact absurd hxy.symm hab1
                        | exact absurd hxy h12 | exact absurd hxy.symm h12
                        | exact absurd hxy h14 | exact absurd hxy.symm h14
                        | exact absurd hxy h23 | exact absurd hxy.symm h23
                        | exact absurd hxy h24 | exact absurd hxy.symm h24
                        | exact absurd hxy hab2 | exact absurd hxy.symm hab2
                        | exact absurd hxy huv | exact absurd hxy.symm huv
                        | exact absurd hxy hu_ne.1 | exact absurd hxy.symm hu_ne.1
                        | exact absurd hxy hu_ne.2.1 | exact absurd hxy.symm hu_ne.2.1
                        | exact absurd hxy hu_ne.2.2.1 | exact absurd hxy.symm hu_ne.2.2.1
                        | exact absurd hxy hu_ne.2.2.2 | exact absurd hxy.symm hu_ne.2.2.2
                        | exact absurd hxy hv_ne.1 | exact absurd hxy.symm hv_ne.1
                        | exact absurd hxy hv_ne.2.1 | exact absurd hxy.symm hv_ne.2.1
                        | exact absurd hxy hv_ne.2.2.1 | exact absurd hxy.symm hv_ne.2.2.1
                        | exact absurd hxy hv_ne.2.2.2 | exact absurd hxy.symm hv_ne.2.2.2
              let S0 : Finset W := Finset.univ.filter (fun w : W =>
                decide (¬(w a1 = sgn a1 ∧ w b1 = sgn b1) ∧
                  ¬(w a2 = sgn a2 ∧ w b2 = sgn b2) ∧ ¬(w u = sgn u ∧ w v = sgn v)) = true)
              have hsub : S ⊆ S0 := by
                intro w hw
                have hE := (hsat_iff_E w).1 (Finset.mem_filter.1 hw).2
                exact Finset.mem_filter.2 ⟨Finset.mem_univ w, decide_eq_true
                  ⟨hE a1 b1 hE1, hE a2 b2 hE2, hE u v hEuv⟩⟩
              have hcard0 : 64 * S0.card = 27 * 2 ^ n := by
                have hpat := card_pattern_signed sites hinj (fun k => sgn (sites k))
                  (fun z : Fin 6 → Bool =>
                    decide (¬(z 0 = true ∧ z 1 = true) ∧ ¬(z 2 = true ∧ z 3 = true) ∧ ¬(z 4 = true ∧ z 5 = true)))
                rw [count_3k2] at hpat
                have h64 : 2 ^ 6 = 64 := by norm_num
                rw [h64] at hpat
                have heq0 : S0 = Finset.univ.filter (fun w : W =>
                    decide (¬(decide (w (sites 0) = sgn (sites 0)) = true ∧ decide (w (sites 1) = sgn (sites 1)) = true) ∧
                      ¬(decide (w (sites 2) = sgn (sites 2)) = true ∧ decide (w (sites 3) = sgn (sites 3)) = true) ∧
                      ¬(decide (w (sites 4) = sgn (sites 4)) = true ∧ decide (w (sites 5) = sgn (sites 5)) = true)) = true) := by
                  ext w
                  simp only [S0, sites, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
                rw [heq0]; exact hpat
              have hle : S.card ≤ S0.card := Finset.card_le_card hsub
              have hlow : 16 * S.card ≤ 7 * 2 ^ n := by omega
              exact finish_low A hshape_card hlow
          · let sites : Fin 4 → Fin n := fun k => match k with
              | ⟨0,_⟩ => a1 | ⟨1,_⟩ => b1 | ⟨2,_⟩ => a2 | ⟨3,_⟩ => b2
            have hinj : Function.Injective sites := by
              intro x y hxy; fin_cases x <;> fin_cases y <;> dsimp [sites] at hxy ⊢ <;>
                first | rfl | exact absurd hxy hab1 | exact absurd hxy h12 | exact absurd hxy h14
                      | exact absurd hxy.symm hab1 | exact absurd hxy h23 | exact absurd hxy h24
                      | exact absurd hxy.symm h12 | exact absurd hxy.symm h23 | exact absurd hxy hab2
                      | exact absurd hxy.symm h14 | exact absurd hxy.symm h24 | exact absurd hxy.symm hab2
            have heqS : S = Finset.univ.filter (fun w : W =>
                decide (¬(decide (w (sites 0) = sgn (sites 0)) = true ∧ decide (w (sites 1) = sgn (sites 1)) = true) ∧
                  ¬(decide (w (sites 2) = sgn (sites 2)) = true ∧ decide (w (sites 3) = sgn (sites 3)) = true)) = true) := by
              ext w
              simp only [S, sites, Finset.mem_filter, Finset.mem_univ, true_and, hsat_iff_E, decide_eq_true_eq]
              constructor
              · intro hall; exact ⟨hall a1 b1 hE1, hall a2 b2 hE2⟩
              · rintro ⟨h1, h2⟩ u v huv
                have hor : (u = a1 ∧ v = b1) ∨ (u = b1 ∧ v = a1) ∨ (u = a2 ∧ v = b2) ∨ (u = b2 ∧ v = a2) := by
                  by_contra hno; exact h3edge ⟨u, v, huv, hno⟩
                rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact h1
                · exact fun h => h1 h.symm
                · exact h2
                · exact fun h => h2 h.symm
            have h16 : 16 * N = 9 * Q := by
              have hpat := card_pattern_signed sites hinj (fun k => sgn (sites k))
                (fun z : Fin 4 → Bool => decide (¬(z 0 = true ∧ z 1 = true) ∧ ¬(z 2 = true ∧ z 3 = true)))
              rw [count_2k2] at hpat
              have h16' : 2 ^ 4 = 16 := by norm_num
              rw [h16'] at hpat
              rw [hN_eq, hQ_eq, heqS]; exact hpat
            have hcert : cert := by
              intro x hx
              have hE := (hsat_iff_E x).1 hx
              have h1 : ∃ j1 ∈ ({a1, b1} : Finset (Fin n)), x j1 ≠ sgn j1 := by
                by_cases ha1 : x a1 = sgn a1
                · exact ⟨b1, by simp, fun hb1 => hE a1 b1 hE1 ⟨ha1, hb1⟩⟩
                · exact ⟨a1, by simp, ha1⟩
              have h2 : ∃ j2 ∈ ({a2, b2} : Finset (Fin n)), x j2 ≠ sgn j2 := by
                by_cases ha2 : x a2 = sgn a2
                · exact ⟨b2, by simp, fun hb2 => hE a2 b2 hE2 ⟨ha2, hb2⟩⟩
                · exact ⟨a2, by simp, ha2⟩
              obtain ⟨j1, hj1m, hj1ne⟩ := h1
              obtain ⟨j2, hj2m, hj2ne⟩ := h2
              refine ⟨{j1, j2}, Finset.card_le_two, fun y hy => (hsat_iff_E y).2 (fun u v huv => ?_)⟩
              have hor : (u = a1 ∧ v = b1) ∨ (u = b1 ∧ v = a1) ∨ (u = a2 ∧ v = b2) ∨ (u = b2 ∧ v = a2) := by
                by_contra hno; exact h3edge ⟨u, v, huv, hno⟩
              have hy1 : y j1 ≠ sgn j1 := by rw [hy j1 (by simp)]; exact hj1ne
              have hy2 : y j2 ≠ sgn j2 := by rw [hy j2 (by simp)]; exact hj2ne
              simp only [Finset.mem_insert, Finset.mem_singleton] at hj1m hj2m
              rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · rcases hj1m with rfl | rfl
                · exact fun h => hy1 h.1
                · exact fun h => hy1 h.2
              · rcases hj1m with rfl | rfl
                · exact fun h => hy1 h.2
                · exact fun h => hy1 h.1
              · rcases hj2m with rfl | rfl
                · exact fun h => hy2 h.1
                · exact fun h => hy2 h.2
              · rcases hj2m with rfl | rfl
                · exact fun h => hy2 h.2
                · exact fun h => hy2 h.1
            refine ⟨fun _ => Or.inr hcert, fun h => by omega, ?_, hshape_card⟩
            constructor
            · intro h; omega
            · intro hsh; have := hshape_card hsh; omega
        · obtain ⟨u0, v0, hE0⟩ := hedge
          have huv0 : u0 ≠ v0 := hE0.1
          by_cases hstar_u : ∀ x y : Fin n, E x y → x = u0 ∨ y = u0
          · have hhalf : half := by
              refine ⟨u0, !(sgn u0), fun p hp => (hsat_iff_E p).2 (fun x y hxy => ?_)⟩
              rcases hstar_u x y hxy with hx | hy
              · rintro ⟨h1, _⟩; rw [hx, hp] at h1; exact Bool.not_ne_self (sgn u0) h1
              · rintro ⟨_, h2⟩; rw [hy, hp] at h2; exact Bool.not_ne_self (sgn u0) h2
            let Sh : Finset W := Finset.univ.filter (fun w : W => decide (w u0 = sgn u0) = false)
            have hSh_sub : Sh ⊆ S := by
              intro w hw
              rw [Finset.mem_filter] at hw ⊢
              refine ⟨Finset.mem_univ w, (hsat_iff_E w).2 (fun x y hxy => ?_)⟩
              have hne : w u0 ≠ sgn u0 := decide_eq_false_iff_not.1 hw.2
              rcases hstar_u x y hxy with hx | hy
              · exact fun h => hne (hx ▸ h.1)
              · exact fun h => hne (hy ▸ h.2)
            let x0 : W := fun i => if i = u0 then sgn u0 else !(sgn i)
            have hx0_S : x0 ∈ S := by
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ x0, (hsat_iff_E x0).2 (fun x y hxy => ?_)⟩
              have hne := hxy.1
              rcases hstar_u x y hxy with hx | hy
              · rintro ⟨_, h2⟩
                have hyne : y ≠ u0 := by rw [← hx]; exact hne.symm
                dsimp [x0] at h2; simp only [hyne, ↓reduceIte] at h2
                exact Bool.not_ne_self (sgn y) h2
              · rintro ⟨h1, _⟩
                have hxne : x ≠ u0 := by rw [← hy]; exact hne
                dsimp [x0] at h1; simp only [hxne, ↓reduceIte] at h1
                exact Bool.not_ne_self (sgn x) h1
            have hx0_notSh : x0 ∉ Sh := by simp [Sh, x0]
            have hSh_card : 2 * Sh.card = Q := by
              let sites : Fin 1 → Fin n := fun _ => u0
              have hinj : Function.Injective sites := fun i j _ => Subsingleton.elim i j
              have hpat := card_pattern_signed sites hinj (fun _ => sgn u0) (fun v : Fin 1 → Bool => decide (v 0 = false))
              rw [count_unary] at hpat
              have heq0 : Sh = Finset.univ.filter (fun w : W =>
                  decide (decide (w (sites 0) = sgn u0) = false) = true) := by
                ext w; simp [Sh, sites]
              rw [heq0]; simpa [Q] using hpat
            have hgt : Q < 2 * N := by
              have hsub2 : insert x0 Sh ⊆ S := Finset.insert_subset_iff.2 ⟨hx0_S, hSh_sub⟩
              have hle := Finset.card_le_card hsub2
              rw [Finset.card_insert_of_notMem hx0_notSh] at hle
              rw [hN_eq]; omega
            refine ⟨fun _ => Or.inl hhalf, fun h => by omega, ?_, hshape_card⟩
            constructor
            · intro h; omega
            · intro hsh; have := hshape_card hsh; omega
          · by_cases hstar_v : ∀ x y : Fin n, E x y → x = v0 ∨ y = v0
            · have hhalf : half := by
                refine ⟨v0, !(sgn v0), fun p hp => (hsat_iff_E p).2 (fun x y hxy => ?_)⟩
                rcases hstar_v x y hxy with hx | hy
                · rintro ⟨h1, _⟩; rw [hx, hp] at h1; exact Bool.not_ne_self (sgn v0) h1
                · rintro ⟨_, h2⟩; rw [hy, hp] at h2; exact Bool.not_ne_self (sgn v0) h2
              let Sh : Finset W := Finset.univ.filter (fun w : W => decide (w v0 = sgn v0) = false)
              have hSh_sub : Sh ⊆ S := by
                intro w hw
                rw [Finset.mem_filter] at hw ⊢
                refine ⟨Finset.mem_univ w, (hsat_iff_E w).2 (fun x y hxy => ?_)⟩
                have hne : w v0 ≠ sgn v0 := decide_eq_false_iff_not.1 hw.2
                rcases hstar_v x y hxy with hx | hy
                · exact fun h => hne (hx ▸ h.1)
                · exact fun h => hne (hy ▸ h.2)
              let x0 : W := fun i => if i = v0 then sgn v0 else !(sgn i)
              have hx0_S : x0 ∈ S := by
                rw [Finset.mem_filter]
                refine ⟨Finset.mem_univ x0, (hsat_iff_E x0).2 (fun x y hxy => ?_)⟩
                have hne := hxy.1
                rcases hstar_v x y hxy with hx | hy
                · rintro ⟨_, h2⟩
                  have hyne : y ≠ v0 := by rw [← hx]; exact hne.symm
                  dsimp [x0] at h2; simp only [hyne, ↓reduceIte] at h2
                  exact Bool.not_ne_self (sgn y) h2
                · rintro ⟨h1, _⟩
                  have hxne : x ≠ v0 := by rw [← hy]; exact hne
                  dsimp [x0] at h1; simp only [hxne, ↓reduceIte] at h1
                  exact Bool.not_ne_self (sgn x) h1
              have hx0_notSh : x0 ∉ Sh := by simp [Sh, x0]
              have hSh_card : 2 * Sh.card = Q := by
                let sites : Fin 1 → Fin n := fun _ => v0
                have hinj : Function.Injective sites := fun i j _ => Subsingleton.elim i j
                have hpat := card_pattern_signed sites hinj (fun _ => sgn v0) (fun v : Fin 1 → Bool => decide (v 0 = false))
                rw [count_unary] at hpat
                have heq0 : Sh = Finset.univ.filter (fun w : W =>
                    decide (decide (w (sites 0) = sgn v0) = false) = true) := by
                  ext w; simp [Sh, sites]
                rw [heq0]; simpa [Q] using hpat
              have hgt : Q < 2 * N := by
                have hsub2 : insert x0 Sh ⊆ S := Finset.insert_subset_iff.2 ⟨hx0_S, hSh_sub⟩
                have hle := Finset.card_le_card hsub2
                rw [Finset.card_insert_of_notMem hx0_notSh] at hle
                rw [hN_eq]; omega
              refine ⟨fun _ => Or.inl hhalf, fun h => by omega, ?_, hshape_card⟩
              constructor
              · intro h; omega
              · intro hsh; have := hshape_card hsh; omega
            · have he_no_u : ∃ x y : Fin n, E x y ∧ x ≠ u0 ∧ y ≠ u0 := by
                by_contra h
                apply hstar_u
                intro x y hxy
                by_contra hor
                rw [not_or] at hor
                exact h ⟨x, y, hxy, hor.1, hor.2⟩
              have he_no_v : ∃ x y : Fin n, E x y ∧ x ≠ v0 ∧ y ≠ v0 := by
                by_contra h
                apply hstar_v
                intro x y hxy
                by_contra hor
                rw [not_or] at hor
                exact h ⟨x, y, hxy, hor.1, hor.2⟩
              obtain ⟨x1, y1, hEx1, hx1u, hy1u⟩ := he_no_u
              obtain ⟨x2, y2, hEx2, hx2v, hy2v⟩ := he_no_v
              have hw1 : ∃ w1 : Fin n, w1 ≠ u0 ∧ w1 ≠ v0 ∧ E v0 w1 := by
                by_cases h1 : x1 = v0
                · subst h1; exact ⟨y1, hy1u, hEx1.1.symm, hEx1⟩
                · by_cases h2 : y1 = v0
                  · subst h2; exact ⟨x1, hx1u, hEx1.1, hE_symm _ _ hEx1⟩
                  · exact absurd ⟨u0, v0, x1, y1, hE0, hEx1, hx1u.symm, hy1u.symm, Ne.symm h1, Ne.symm h2⟩ h2match
              have hw2 : ∃ w2 : Fin n, w2 ≠ u0 ∧ w2 ≠ v0 ∧ E u0 w2 := by
                by_cases h1 : x2 = u0
                · subst h1; exact ⟨y2, hEx2.1.symm, hy2v, hEx2⟩
                · by_cases h2 : y2 = u0
                  · subst h2; exact ⟨x2, hEx2.1, hx2v, hE_symm _ _ hEx2⟩
                  · exact absurd ⟨u0, v0, x2, y2, hE0, hEx2, Ne.symm h1, Ne.symm h2, hx2v.symm, hy2v.symm⟩ h2match
              obtain ⟨w1, hw1u, hw1v, hEvw1⟩ := hw1
              obtain ⟨w2, hw2u, hw2v, hEuw2⟩ := hw2
              have hw12 : w1 = w2 := by
                by_contra hne
                exact h2match ⟨v0, w1, u0, w2, hEvw1, hEuw2, huv0.symm, hw2v.symm, hw1u, hne⟩
              subst hw12
              let S0 : Finset W := Finset.univ.filter (fun w : W =>
                decide (¬(w u0 = sgn u0 ∧ w v0 = sgn v0) ∧
                  ¬(w v0 = sgn v0 ∧ w w1 = sgn w1) ∧ ¬(w u0 = sgn u0 ∧ w w1 = sgn w1)) = true)
              have hsub : S ⊆ S0 := by
                intro w hw
                have hE := (hsat_iff_E w).1 (Finset.mem_filter.1 hw).2
                exact Finset.mem_filter.2 ⟨Finset.mem_univ w, decide_eq_true
                  ⟨hE u0 v0 hE0, hE v0 w1 hEvw1, hE u0 w1 hEuw2⟩⟩
              have hcard0 : 2 * S0.card = 2 ^ n := by
                let sites : Fin 3 → Fin n := fun k => match k with
                  | ⟨0,_⟩ => u0 | ⟨1,_⟩ => v0 | ⟨2,_⟩ => w1
                have hinj : Function.Injective sites := by
                  intro a b hab; fin_cases a <;> fin_cases b <;> dsimp [sites] at hab ⊢ <;>
                    first | rfl | exact absurd hab huv0 | exact absurd hab hw1u.symm
                          | exact absurd hab.symm huv0 | exact absurd hab hw1v.symm
                          | exact absurd hab hw1u | exact absurd hab hw1v
                have hpat := card_pattern_signed sites hinj (fun k => sgn (sites k))
                  (fun v : Fin 3 → Bool =>
                    decide (¬(v 0 = true ∧ v 1 = true) ∧ ¬(v 1 = true ∧ v 2 = true) ∧ ¬(v 0 = true ∧ v 2 = true)))
                rw [count_k3] at hpat
                have h8 : 2 ^ 3 = 8 := by norm_num
                rw [h8] at hpat
                have heq0 : S0 = Finset.univ.filter (fun w : W =>
                    decide (¬(decide (w (sites 0) = sgn (sites 0)) = true ∧ decide (w (sites 1) = sgn (sites 1)) = true) ∧
                      ¬(decide (w (sites 1) = sgn (sites 1)) = true ∧ decide (w (sites 2) = sgn (sites 2)) = true) ∧
                      ¬(decide (w (sites 0) = sgn (sites 0)) = true ∧ decide (w (sites 2) = sgn (sites 2)) = true)) = true) := by
                  ext w
                  simp only [S0, sites, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
                dsimp only at hpat
                rw [← heq0] at hpat; omega
              have hcert0 : ∀ x ∈ S0, ∃ T : Finset (Fin n), T.card ≤ 2 ∧
                  ∀ y : W, (∀ k ∈ T, y k = x k) → y ∈ S0 := by
                intro x hx
                have ⟨hs1, hs2, hs3⟩ := of_decide_eq_true (Finset.mem_filter.1 hx).2
                by_cases hu : x u0 = sgn u0
                · have hv : x v0 ≠ sgn v0 := fun h => hs1 ⟨hu, h⟩
                  have hw : x w1 ≠ sgn w1 := fun h => hs3 ⟨hu, h⟩
                  refine ⟨{v0, w1}, Finset.card_le_two, fun y hy => ?_⟩
                  have hyv : y v0 ≠ sgn v0 := by rw [hy v0 (by simp)]; exact hv
                  have hyw : y w1 ≠ sgn w1 := by rw [hy w1 (by simp)]; exact hw
                  exact Finset.mem_filter.2 ⟨Finset.mem_univ y, decide_eq_true
                    ⟨fun h => hyv h.2, fun h => hyv h.1, fun h => hyw h.2⟩⟩
                · by_cases hv : x v0 = sgn v0
                  · have hw : x w1 ≠ sgn w1 := fun h => hs2 ⟨hv, h⟩
                    refine ⟨{u0, w1}, Finset.card_le_two, fun y hy => ?_⟩
                    have hyu : y u0 ≠ sgn u0 := by rw [hy u0 (by simp)]; exact hu
                    have hyw : y w1 ≠ sgn w1 := by rw [hy w1 (by simp)]; exact hw
                    exact Finset.mem_filter.2 ⟨Finset.mem_univ y, decide_eq_true
                      ⟨fun h => hyu h.1, fun h => hyw h.2, fun h => hyu h.1⟩⟩
                  · refine ⟨{u0, v0}, Finset.card_le_two, fun y hy => ?_⟩
                    have hyu : y u0 ≠ sgn u0 := by rw [hy u0 (by simp)]; exact hu
                    have hyv : y v0 ≠ sgn v0 := by rw [hy v0 (by simp)]; exact hv
                    exact Finset.mem_filter.2 ⟨Finset.mem_univ y, decide_eq_true
                      ⟨fun h => hyu h.1, fun h => hyv h.1, fun h => hyu h.1⟩⟩
              exact finish_half_core A S0 hshape_card hsub hcard0 hcert0
      · have hall_sat : ∀ w : W, sat A w = true := fun w =>
          (hsat_iff_E w).2 (fun u v huv => absurd ⟨u, v, huv⟩ hedge)
        have hN : N = Q := by
          rw [hN_eq, hQ_eq]
          have hfilt : S = Finset.univ := by
            ext w; simp [S, hall_sat w]
          rw [hfilt, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
        have hcert : cert := fun x _ => ⟨∅, by simp, fun y _ => hall_sat y⟩
        refine ⟨fun _ => Or.inr hcert, fun h => by omega, ?_, hshape_card⟩
        constructor
        · intro h; omega
        · intro hsh; have := hshape_card hsh; omega


lemma structural (n : ℕ) (A : Finset ((Fin n × Bool) × (Fin n × Bool)))
    (h : 2 ^ n ≤ 2 * (Finset.univ.filter (fun z : Fin n → Bool =>
        decide (∀ c ∈ A, z c.1.1 ≠ c.1.2 ∨ z c.2.1 ≠ c.2.2) = true)).card) :
    (∃ (j : Fin n) (v : Bool), ∀ p : Fin n → Bool, p j = v →
        decide (∀ c ∈ A, p c.1.1 ≠ c.1.2 ∨ p c.2.1 ≠ c.2.2) = true) ∨
    (∀ x : Fin n → Bool, decide (∀ c ∈ A, x c.1.1 ≠ c.1.2 ∨ x c.2.1 ≠ c.2.2) = true →
      ∃ T : Finset (Fin n), T.card ≤ 2 ∧
        ∀ y : Fin n → Bool, (∀ i ∈ T, y i = x i) →
          decide (∀ c ∈ A, y c.1.1 ≠ c.1.2 ∨ y c.2.1 ≠ c.2.2) = true) :=
  (main_proof n A).1 h

lemma suff (n : ℕ) (pool : Finset (Fin n → Bool))
    (hc : n = 0 ∨ ∀ S : Finset (Fin n), S.card ≤ 4 → ∀ pat : Fin n → Bool,
      ∃ x ∈ pool, ∀ bit ∈ S, x bit = pat bit)
    (A : Finset ((Fin n × Bool) × (Fin n × Bool))) :
    (2 ^ n ≤ 2 * (Finset.univ.filter (fun z : Fin n → Bool => ∀ i j : Fin n, ∃ v : ↥pool,
        decide (∀ c ∈ A, v.val c.1.1 ≠ c.1.2 ∨ v.val c.2.1 ≠ c.2.2) = true ∧
          v.val i = z i ∧ v.val j = z j)).card) ↔
    (2 ^ n ≤ 2 * (Finset.univ.filter (fun word : Fin n → Bool =>
        decide (∀ c ∈ A, word c.1.1 ≠ c.1.2 ∨ word c.2.1 ≠ c.2.2) = true)).card) := by
  constructor
  · intro h
    refine le_trans h (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    refine ⟨hz.1, decide_eq_true ?_⟩
    intro c hc'
    obtain ⟨v, hv, h1, h2⟩ := hz.2 c.1.1 c.2.1
    have h3 := of_decide_eq_true hv c hc'
    rw [h1, h2] at h3
    exact h3
  · intro h
    rcases hc with h0 | hcov
    · subst h0
      refine le_trans h (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
      intro z _
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, fun i => i.elim0⟩
    · rcases structural n A h with ⟨k, b, hhalf⟩ | hcert
      · have hcyl := card_cyl ({k} : Finset (Fin n)) (fun _ => b)
        have hsub : (Finset.univ.filter (fun y : Fin n → Bool =>
            ∀ i ∈ ({k} : Finset (Fin n)), y i = b)) ⊆
            (Finset.univ.filter (fun z : Fin n → Bool => ∀ i j : Fin n, ∃ v : ↥pool,
              decide (∀ c ∈ A, v.val c.1.1 ≠ c.1.2 ∨ v.val c.2.1 ≠ c.2.2) = true ∧
                v.val i = z i ∧ v.val j = z j)) := by
          intro z hz
          rw [Finset.mem_filter] at hz ⊢
          refine ⟨hz.1, fun i j => ?_⟩
          have hzk : z k = b := hz.2 k (Finset.mem_singleton_self k)
          obtain ⟨v, hv, hvS⟩ := hcov ({k, i, j} : Finset (Fin n))
            (le_trans Finset.card_le_three (by norm_num)) z
          refine ⟨⟨v, hv⟩, hhalf v ?_, hvS i (by simp), hvS j (by simp)⟩
          rw [hvS k (by simp), hzk]
        have hle := Finset.card_le_card hsub
        rw [Finset.card_singleton, pow_one] at hcyl
        omega
      · refine le_trans h (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
        intro z hz
        rw [Finset.mem_filter] at hz ⊢
        refine ⟨hz.1, fun i j => ?_⟩
        obtain ⟨T, hT, hTy⟩ := hcert z hz.2
        have hcard : (T ∪ {i, j}).card ≤ 4 :=
          calc (T ∪ {i, j}).card ≤ T.card + ({i, j} : Finset (Fin n)).card :=
                Finset.card_union_le _ _
            _ ≤ 2 + 2 := Nat.add_le_add hT Finset.card_le_two
        obtain ⟨v, hv, hvS⟩ := hcov (T ∪ {i, j}) hcard z
        exact ⟨⟨v, hv⟩, hTy v (fun t ht => hvS t (by simp [ht])), hvS i (by simp),
          hvS j (by simp)⟩

lemma nec_core (n m : ℕ) (pool : Finset (Fin n → Bool))
    (sites : Fin m → Fin n) (hinj : Function.Injective sites) (pat : Fin n → Bool)
    (hmiss : ∀ x ∈ pool, ∃ k, x (sites k) ≠ pat (sites k))
    (A1 A2 : Finset ((Fin n × Bool) × (Fin n × Bool)))
    (P1 P2 : (Fin m → Bool) → Bool)
    (h1 : ∀ w : Fin n → Bool, (∀ c ∈ A1, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2) ↔
      P1 (fun k => decide (w (sites k) = pat (sites k))) = true)
    (h2 : ∀ w : Fin n → Bool, (∀ c ∈ A2, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2) ↔
      P2 (fun k => decide (w (sites k) = pat (sites k))) = true)
    (hagree : ∀ v : Fin m → Bool, (∃ k, v k = false) → P1 v = P2 v)
    (hc1 : 2 ^ m ≤ 2 * (Finset.univ.filter (fun v : Fin m → Bool => P1 v = true)).card)
    (hc2 : 2 * (Finset.univ.filter (fun v : Fin m → Bool => P2 v = true)).card < 2 ^ m)
    (classify : (↥pool → Bool) → Bool)
    (hcorrect : ∀ A : Finset ((Fin n × Bool) × (Fin n × Bool)),
      classify (fun q => decide (∀ c ∈ A, q.val c.1.1 ≠ c.1.2 ∨ q.val c.2.1 ≠ c.2.2)) =
        decide (2 ^ n ≤ 2 * (Finset.univ.filter (fun word : Fin n → Bool =>
          decide (∀ c ∈ A, word c.1.1 ≠ c.1.2 ∨ word c.2.1 ≠ c.2.2) = true)).card)) :
    False := by
  have hlab : (fun q : ↥pool =>
      decide (∀ c ∈ A1, q.val c.1.1 ≠ c.1.2 ∨ q.val c.2.1 ≠ c.2.2)) =
      (fun q : ↥pool => decide (∀ c ∈ A2, q.val c.1.1 ≠ c.1.2 ∨ q.val c.2.1 ≠ c.2.2)) := by
    funext q
    apply decide_eq_decide.2
    rw [h1 q.val, h2 q.val]
    obtain ⟨k, hk⟩ := hmiss q.val q.property
    rw [hagree _ ⟨k, decide_eq_false hk⟩]
  have e1 : (Finset.univ.filter (fun word : Fin n → Bool =>
      decide (∀ c ∈ A1, word c.1.1 ≠ c.1.2 ∨ word c.2.1 ≠ c.2.2) = true)) =
      Finset.univ.filter (fun w : Fin n → Bool =>
        P1 (fun k => decide (w (sites k) = pat (sites k))) = true) :=
    Finset.filter_congr (fun w _ => decide_eq_true_iff.trans (h1 w))
  have e2 : (Finset.univ.filter (fun word : Fin n → Bool =>
      decide (∀ c ∈ A2, word c.1.1 ≠ c.1.2 ∨ word c.2.1 ≠ c.2.2) = true)) =
      Finset.univ.filter (fun w : Fin n → Bool =>
        P2 (fun k => decide (w (sites k) = pat (sites k))) = true) :=
    Finset.filter_congr (fun w _ => decide_eq_true_iff.trans (h2 w))
  have hN1 := card_pattern_signed sites hinj (fun k => pat (sites k)) P1
  have hN2 := card_pattern_signed sites hinj (fun k => pat (sites k)) P2
  have hpm : 0 < 2 ^ m := Nat.pow_pos (by norm_num)
  have hpn : 0 < 2 ^ n := Nat.pow_pos (by norm_num)
  have t1 : 2 ^ n ≤ 2 * (Finset.univ.filter (fun word : Fin n → Bool =>
      decide (∀ c ∈ A1, word c.1.1 ≠ c.1.2 ∨ word c.2.1 ≠ c.2.2) = true)).card := by
    rw [e1]
    apply Nat.le_of_mul_le_mul_left _ hpm
    have h3 := Nat.mul_le_mul_right (2 ^ n) hc1
    nlinarith
  have t2 : ¬ 2 ^ n ≤ 2 * (Finset.univ.filter (fun word : Fin n → Bool =>
      decide (∀ c ∈ A2, word c.1.1 ≠ c.1.2 ∨ word c.2.1 ≠ c.2.2) = true)).card := by
    rw [e2]
    intro hle
    have h3 := Nat.mul_le_mul_left (2 ^ m) hle
    have h4 := Nat.mul_lt_mul_of_pos_right hc2 hpn
    nlinarith
  have hA1 := hcorrect A1
  have hA2 := hcorrect A2
  rw [hlab] at hA1
  rw [hA1] at hA2
  exact t2 ((decide_eq_decide.1 hA2).1 t1)

lemma sel_prop (a p b q c r : Bool) :
    ((a ≠ (!p) ∨ b ≠ q) ∧ (a ≠ p ∨ c ≠ (!r))) ↔
      ((decide (a = p) || !decide (b = q)) && (!decide (a = p) || decide (c = r))) = true := by
  cases a <;> cases p <;> cases b <;> cases q <;> cases c <;> cases r <;> decide

lemma sel4_prop (a p b q c r d s : Bool) :
    ((a ≠ (!p) ∨ b ≠ q) ∧ (a ≠ p ∨ c ≠ (!r)) ∧ (b ≠ q ∨ d ≠ s)) ↔
      ((decide (a = p) || !decide (b = q)) && (!decide (a = p) || decide (c = r)) &&
        (!decide (b = q) || !decide (d = s))) = true := by
  cases a <;> cases p <;> cases b <;> cases q <;> cases c <;> cases r <;> cases d <;>
    cases s <;> decide

lemma sel3_prop (a p b q c r : Bool) :
    ((a ≠ (!p) ∨ b ≠ q) ∧ (a ≠ p ∨ c ≠ (!r)) ∧ (b ≠ q ∨ b ≠ q)) ↔
      ((decide (a = p) || !decide (b = q)) && (!decide (a = p) || decide (c = r)) &&
        !decide (b = q)) = true := by
  cases a <;> cases p <;> cases b <;> cases q <;> cases c <;> cases r <;> decide

lemma un_prop (a p : Bool) :
    (a ≠ (!p) ∨ a ≠ (!p)) ↔ decide (a = p) = true := by
  cases a <;> cases p <;> decide

lemma un2_prop (a p b q : Bool) :
    ((a ≠ (!p) ∨ a ≠ (!p)) ∧ (a ≠ p ∨ b ≠ q)) ↔
      (decide (a = p) && (!decide (a = p) || !decide (b = q))) = true := by
  cases a <;> cases p <;> cases b <;> cases q <;> decide

lemma un1_prop (a p : Bool) :
    ((a ≠ (!p) ∨ a ≠ (!p)) ∧ (a ≠ p ∨ a ≠ p)) ↔
      (decide (a = p) && !decide (a = p)) = true := by
  cases a <;> cases p <;> decide

lemma nec4 (n : ℕ) (pool : Finset (Fin n → Bool))
    (sites : Fin 4 → Fin n) (hinj : Function.Injective sites) (pat : Fin n → Bool)
    (hmiss : ∀ x ∈ pool, ∃ k, x (sites k) ≠ pat (sites k))
    (classify : (↥pool → Bool) → Bool)
    (hcorrect : ∀ A : Finset ((Fin n × Bool) × (Fin n × Bool)),
      classify (fun q => decide (∀ c ∈ A, q.val c.1.1 ≠ c.1.2 ∨ q.val c.2.1 ≠ c.2.2)) =
        decide (2 ^ n ≤ 2 * (Finset.univ.filter (fun word : Fin n → Bool =>
          decide (∀ c ∈ A, word c.1.1 ≠ c.1.2 ∨ word c.2.1 ≠ c.2.2) = true)).card)) :
    False :=
  nec_core n 4 pool sites hinj pat hmiss
    {((sites 0, !pat (sites 0)), (sites 1, pat (sites 1))),
      ((sites 0, pat (sites 0)), (sites 2, !pat (sites 2)))}
    {((sites 0, !pat (sites 0)), (sites 1, pat (sites 1))),
      ((sites 0, pat (sites 0)), (sites 2, !pat (sites 2))),
      ((sites 1, pat (sites 1)), (sites 3, pat (sites 3)))}
    (fun v => (v 0 || !v 1) && (!v 0 || v 2))
    (fun v => (v 0 || !v 1) && (!v 0 || v 2) && (!v 1 || !v 3))
    (by
      intro w
      simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
      exact sel_prop _ _ _ _ _ _)
    (by
      intro w
      simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
      exact sel4_prop _ _ _ _ _ _ _ _)
    (by decide) (by decide) (by decide) classify hcorrect

lemma nec3 (n : ℕ) (pool : Finset (Fin n → Bool))
    (sites : Fin 3 → Fin n) (hinj : Function.Injective sites) (pat : Fin n → Bool)
    (hmiss : ∀ x ∈ pool, ∃ k, x (sites k) ≠ pat (sites k))
    (classify : (↥pool → Bool) → Bool)
    (hcorrect : ∀ A : Finset ((Fin n × Bool) × (Fin n × Bool)),
      classify (fun q => decide (∀ c ∈ A, q.val c.1.1 ≠ c.1.2 ∨ q.val c.2.1 ≠ c.2.2)) =
        decide (2 ^ n ≤ 2 * (Finset.univ.filter (fun word : Fin n → Bool =>
          decide (∀ c ∈ A, word c.1.1 ≠ c.1.2 ∨ word c.2.1 ≠ c.2.2) = true)).card)) :
    False :=
  nec_core n 3 pool sites hinj pat hmiss
    {((sites 0, !pat (sites 0)), (sites 1, pat (sites 1))),
      ((sites 0, pat (sites 0)), (sites 2, !pat (sites 2)))}
    {((sites 0, !pat (sites 0)), (sites 1, pat (sites 1))),
      ((sites 0, pat (sites 0)), (sites 2, !pat (sites 2))),
      ((sites 1, pat (sites 1)), (sites 1, pat (sites 1)))}
    (fun v => (v 0 || !v 1) && (!v 0 || v 2))
    (fun v => (v 0 || !v 1) && (!v 0 || v 2) && !v 1)
    (by
      intro w
      simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
      exact sel_prop _ _ _ _ _ _)
    (by
      intro w
      simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
      exact sel3_prop _ _ _ _ _ _)
    (by decide) (by decide) (by decide) classify hcorrect

lemma nec2 (n : ℕ) (pool : Finset (Fin n → Bool))
    (sites : Fin 2 → Fin n) (hinj : Function.Injective sites) (pat : Fin n → Bool)
    (hmiss : ∀ x ∈ pool, ∃ k, x (sites k) ≠ pat (sites k))
    (classify : (↥pool → Bool) → Bool)
    (hcorrect : ∀ A : Finset ((Fin n × Bool) × (Fin n × Bool)),
      classify (fun q => decide (∀ c ∈ A, q.val c.1.1 ≠ c.1.2 ∨ q.val c.2.1 ≠ c.2.2)) =
        decide (2 ^ n ≤ 2 * (Finset.univ.filter (fun word : Fin n → Bool =>
          decide (∀ c ∈ A, word c.1.1 ≠ c.1.2 ∨ word c.2.1 ≠ c.2.2) = true)).card)) :
    False :=
  nec_core n 2 pool sites hinj pat hmiss
    {((sites 0, !pat (sites 0)), (sites 0, !pat (sites 0)))}
    {((sites 0, !pat (sites 0)), (sites 0, !pat (sites 0))),
      ((sites 0, pat (sites 0)), (sites 1, pat (sites 1)))}
    (fun v => v 0)
    (fun v => v 0 && (!v 0 || !v 1))
    (by
      intro w
      simp only [Finset.mem_singleton, forall_eq]
      exact un_prop _ _)
    (by
      intro w
      simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
      exact un2_prop _ _ _ _)
    (by decide) (by decide) (by decide) classify hcorrect

lemma nec1 (n : ℕ) (pool : Finset (Fin n → Bool))
    (sites : Fin 1 → Fin n) (hinj : Function.Injective sites) (pat : Fin n → Bool)
    (hmiss : ∀ x ∈ pool, ∃ k, x (sites k) ≠ pat (sites k))
    (classify : (↥pool → Bool) → Bool)
    (hcorrect : ∀ A : Finset ((Fin n × Bool) × (Fin n × Bool)),
      classify (fun q => decide (∀ c ∈ A, q.val c.1.1 ≠ c.1.2 ∨ q.val c.2.1 ≠ c.2.2)) =
        decide (2 ^ n ≤ 2 * (Finset.univ.filter (fun word : Fin n → Bool =>
          decide (∀ c ∈ A, word c.1.1 ≠ c.1.2 ∨ word c.2.1 ≠ c.2.2) = true)).card)) :
    False :=
  nec_core n 1 pool sites hinj pat hmiss
    {((sites 0, !pat (sites 0)), (sites 0, !pat (sites 0)))}
    {((sites 0, !pat (sites 0)), (sites 0, !pat (sites 0))),
      ((sites 0, pat (sites 0)), (sites 0, pat (sites 0)))}
    (fun v => v 0)
    (fun v => v 0 && !v 0)
    (by
      intro w
      simp only [Finset.mem_singleton, forall_eq]
      exact un_prop _ _)
    (by
      intro w
      simp only [Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
      exact un1_prop _ _)
    (by decide) (by decide) (by decide) classify hcorrect

lemma nec (n : ℕ) (hn : 0 < n) (pool : Finset (Fin n → Bool))
    (S : Finset (Fin n)) (hS : S.card ≤ 4) (pat : Fin n → Bool)
    (hmiss : ∀ x ∈ pool, ∃ bit ∈ S, x bit ≠ pat bit)
    (classify : (↥pool → Bool) → Bool)
    (hcorrect : ∀ A : Finset ((Fin n × Bool) × (Fin n × Bool)),
      classify (fun q => decide (∀ c ∈ A, q.val c.1.1 ≠ c.1.2 ∨ q.val c.2.1 ≠ c.2.2)) =
        decide (2 ^ n ≤ 2 * (Finset.univ.filter (fun word : Fin n → Bool =>
          decide (∀ c ∈ A, word c.1.1 ≠ c.1.2 ∨ word c.2.1 ≠ c.2.2) = true)).card)) :
    False := by
  obtain ⟨m, hm1, hm4, hSm, hmn⟩ : ∃ m, 1 ≤ m ∧ m ≤ 4 ∧ S.card ≤ m ∧ m ≤ n := by
    refine ⟨max S.card 1, le_max_right _ _, max_le hS (by norm_num), le_max_left _ _,
      max_le ?_ hn⟩
    simpa using Finset.card_le_univ S
  obtain ⟨S', hSS', hS'card⟩ := Finset.exists_superset_card_eq hSm (by simpa using hmn)
  have hmiss' : ∀ x ∈ pool, ∃ k, x ((S'.orderEmbOfFin hS'card) k) ≠
      pat ((S'.orderEmbOfFin hS'card) k) := by
    intro x hx
    obtain ⟨bit, hbit, hne⟩ := hmiss x hx
    have hr : bit ∈ Set.range (S'.orderEmbOfFin hS'card) := by
      rw [Finset.range_orderEmbOfFin]
      exact hSS' hbit
    obtain ⟨k, rfl⟩ := hr
    exact ⟨k, hne⟩
  have hinj : Function.Injective (S'.orderEmbOfFin hS'card) :=
    (S'.orderEmbOfFin hS'card).injective
  have hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
  rcases hm with rfl | rfl | rfl | rfl
  · exact nec1 n pool _ hinj pat hmiss' classify hcorrect
  · exact nec2 n pool _ hinj pat hmiss' classify hcorrect
  · exact nec3 n pool _ hinj pat hmiss' classify hcorrect
  · exact nec4 n pool _ hinj pat hmiss' classify hcorrect

end PEqualNP.Outside.L_lib_601

theorem PEqualNP.Outside.L_lib_601 : (∀ n : ℕ,
  let W := Fin n → Bool
  let Lit := Fin n × Bool
  let F := Finset (Lit × Lit)
  let sat := fun (C : F) (w : W) => decide (∀ c ∈ C,
    w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)
  let Q := 2 ^ n
  ∀ pool : Finset W,
    let correct := fun (classify : (↥pool → Bool) → Bool) => ∀ A : F,
      classify (fun query => sat A query.val) =
        decide (Q ≤ 2 * (Finset.univ.filter (fun word => sat A word = true)).card)
    let covers := ∀ S : Finset (Fin n), S.card ≤ 4 → ∀ pat : W,
      ∃ x ∈ pool, ∀ bit ∈ S, x bit = pat bit
    let decoder := fun (label : ↥pool → Bool) =>
      let hull := fun z : W => ∀ i j : Fin n, ∃ v : ↥pool,
        label v = true ∧ v.val i = z i ∧ v.val j = z j
      decide (Q ≤ 2 * (Finset.univ.filter hull).card)
    ((∃ classify, correct classify) ↔ n = 0 ∨ covers) ∧
      (n = 0 ∨ covers → correct decoder)) := by
  intro n W Lit F sat Q pool correct covers decoder
  have hsuff : n = 0 ∨ covers → correct decoder := by
    intro h A
    exact decide_eq_decide.2 (PEqualNP.Outside.L_lib_601.suff n pool h A)
  refine ⟨⟨?_, fun h => ⟨decoder, hsuff h⟩⟩, hsuff⟩
  rintro ⟨classify, hcl⟩
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hn0, hncov⟩ := hne
  have hex : ∃ S : Finset (Fin n), S.card ≤ 4 ∧ ∃ pat : W,
      ∀ x ∈ pool, ∃ bit ∈ S, x bit ≠ pat bit := by
    by_contra hno
    apply hncov
    intro S hS pat
    by_contra hx
    apply hno
    refine ⟨S, hS, pat, fun x hxp => ?_⟩
    by_contra hb
    apply hx
    refine ⟨x, hxp, fun bit hbit => ?_⟩
    by_contra hne
    exact hb ⟨bit, hbit, hne⟩
  obtain ⟨S, hS, pat, hmiss⟩ := hex
  exact PEqualNP.Outside.L_lib_601.nec n (Nat.pos_of_ne_zero hn0) pool S hS pat hmiss
    classify hcl
