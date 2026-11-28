import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1222

private def wordOf (n : ℕ) (w : Fin (2 ^ n)) : Fin n → Bool :=
  fun k => decide ((w.val / 2 ^ k.val) % 2 = 1)

private def finOfWord (n : ℕ) (f : Fin n → Bool) : Fin (2 ^ n) :=
  ⟨∑ k : Fin n, (f k).toNat * 2 ^ k.val, by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one]
      have h1 : (f 0).toNat ≤ 1 := by cases f 0 <;> decide
      have h2 : ∑ i : Fin n, (f i.succ).toNat * 2 ^ i.succ.val =
          2 * ∑ i : Fin n, (f i.succ).toNat * 2 ^ i.val := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Fin.val_succ, pow_succ]; ring
      have h3 := ih (fun i => f i.succ)
      rw [h2, pow_succ]
      omega⟩

private lemma wordOf_finOfWord (n : ℕ) (f : Fin n → Bool) : wordOf n (finOfWord n f) = f := by
  funext k
  have hbit : ∀ (m : ℕ) (g : Fin m → Bool) (i : Fin m),
      ((∑ j : Fin m, (g j).toNat * 2 ^ j.val) / 2 ^ i.val) % 2 = (g i).toNat := by
    intro m
    induction m with
    | zero => intro _ i; exact i.elim0
    | succ m ih =>
      intro g i
      have hsum : (∑ j : Fin (m + 1), (g j).toNat * 2 ^ j.val) =
          (g 0).toNat + 2 * ∑ j : Fin m, (g j.succ).toNat * 2 ^ j.val := by
        rw [Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Fin.val_succ, pow_succ]; ring
      refine Fin.cases ?_ (fun i' => ?_) i
      · rw [hsum]; simp only [Fin.val_zero, pow_zero, Nat.div_one]
        cases g 0 <;> simp
      · rw [hsum, Fin.val_succ, pow_succ']
        rw [← Nat.div_div_eq_div_mul]
        have hdiv2 : ((g 0).toNat + 2 * ∑ j : Fin m, (g j.succ).toNat * 2 ^ j.val) / 2 =
            ∑ j : Fin m, (g j.succ).toNat * 2 ^ j.val := by
          rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
          have : (g 0).toNat / 2 = 0 := by cases g 0 <;> decide
          omega
        rw [hdiv2]
        exact ih (fun j => g j.succ) i'
  unfold wordOf finOfWord
  dsimp only
  rw [hbit n f k]
  cases f k <;> decide

private lemma finOfWord_wordOf (n : ℕ) (w : Fin (2 ^ n)) : finOfWord n (wordOf n w) = w := by
  apply Fin.ext
  have hrec : ∀ (m x : ℕ), x < 2 ^ m →
      (∑ k : Fin m, (decide ((x / 2 ^ k.val) % 2 = 1)).toNat * 2 ^ k.val) = x := by
    intro m
    induction m with
    | zero => intro x hx; simp at hx ⊢; omega
    | succ m ih =>
      intro x hx
      rw [Fin.sum_univ_succ, Fin.val_zero, pow_zero, Nat.div_one, mul_one]
      have htail : (∑ i : Fin m, (decide ((x / 2 ^ i.succ.val) % 2 = 1)).toNat * 2 ^ i.succ.val) =
          2 * ∑ i : Fin m, (decide (((x / 2) / 2 ^ i.val) % 2 = 1)).toNat * 2 ^ i.val := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Fin.val_succ, pow_succ', Nat.div_div_eq_div_mul]
        ring
      rw [htail, ih (x / 2) (by rw [pow_succ'] at hx; omega)]
      have hmod : (decide (x % 2 = 1)).toNat = x % 2 := by
        rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]
      rw [hmod]
      omega
  exact hrec n w.val w.isLt

private def wordEquiv (n : ℕ) : Fin (2 ^ n) ≃ (Fin n → Bool) where
  toFun := wordOf n
  invFun := finOfWord n
  left_inv := finOfWord_wordOf n
  right_inv := wordOf_finOfWord n

private def graphOfArcs {V : Type} [DecidableEq V] [Fintype V] (arc : V → V → Bool) :
    (V × Bool) → Finset (V × Bool) := fun ⟨u, b⟩ =>
  if b then
    insert (u, false) ((Finset.univ.filter (fun v => arc u v = true)).image (fun v => (v, false)))
  else
    insert (u, true) ((Finset.univ.filter (fun v => arc v u = true)).image (fun v => (v, true)))

private lemma graphOfArcs_props {V : Type} [DecidableEq V] [Fintype V] (arc : V → V → Bool)
    (hirr : ∀ u, arc u u = false)
    (hout : ∀ u, (Finset.univ.filter (fun v => arc u v = true)).card ≤ 2)
    (hin : ∀ u, (Finset.univ.filter (fun v => arc v u = true)).card ≤ 2) :
    let G := graphOfArcs arc
    (∀ i, (i, true) ∈ G (i, false)) ∧
    (∀ p, p ∉ G p ∧ (G p).card ≤ 3) ∧
    (∀ p r, r ∈ G p ↔ p ∈ G r) ∧
    (∀ p, ∀ r ∈ G p, p.2 ≠ r.2) := by
  intro G
  have hmem_t : ∀ u v b, (v, b) ∈ G (u, true) ↔ b = false ∧ (v = u ∨ arc u v = true) := by
    intro u v b
    simp only [G, graphOfArcs, ↓reduceIte, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨w, hw, rfl, rfl⟩)
      · exact ⟨rfl, Or.inl rfl⟩
      · exact ⟨rfl, Or.inr hw⟩
    · rintro ⟨rfl, rfl | h⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨v, h, rfl, rfl⟩
  have hmem_f : ∀ u v b, (v, b) ∈ G (u, false) ↔ b = true ∧ (v = u ∨ arc v u = true) := by
    intro u v b
    simp only [G, graphOfArcs, Bool.false_eq_true, ↓reduceIte, Finset.mem_insert, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨w, hw, rfl, rfl⟩)
      · exact ⟨rfl, Or.inl rfl⟩
      · exact ⟨rfl, Or.inr hw⟩
    · rintro ⟨rfl, rfl | h⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨v, h, rfl, rfl⟩
  refine ⟨fun i => (hmem_f i i true).mpr ⟨rfl, Or.inl rfl⟩, ?_, ?_, ?_⟩
  · rintro ⟨u, b⟩
    cases b
    · refine ⟨fun h => by have := ((hmem_f u u false).mp h).1; simp at this, ?_⟩
      unfold G graphOfArcs; simp only [Bool.false_eq_true, ↓reduceIte]
      exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (Finset.card_image_le.trans (hin u)) 1)
    · refine ⟨fun h => by have := ((hmem_t u u true).mp h).1; simp at this, ?_⟩
      unfold G graphOfArcs; simp only [↓reduceIte]
      exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (Finset.card_image_le.trans (hout u)) 1)
  · rintro ⟨u, b1⟩ ⟨v, b2⟩
    cases b1 <;> cases b2
    · simp [hmem_f]
    · simp only [hmem_f, hmem_t, true_and]; exact ⟨fun h => h.imp Eq.symm id, fun h => h.imp Eq.symm id⟩
    · simp only [hmem_t, hmem_f, true_and]; exact ⟨fun h => h.imp Eq.symm id, fun h => h.imp Eq.symm id⟩
    · simp [hmem_t]
  · rintro ⟨u, b1⟩ ⟨v, b2⟩ h
    cases b1
    · dsimp only; rw [((hmem_f u v b2).mp h).1]; decide
    · dsimp only; rw [((hmem_t u v b2).mp h).1]; decide

private lemma transW_card_eq (a b : Bool) :
    ((Finset.univ : Finset Bool).filter (fun c => (a = true → c = true) ∧ (c = true → b = true))).card =
    (if a = true ∧ b = false then 0 else if a = b then 1 else 2) := by
  cases a <;> cases b <;> decide

private lemma detQ_card_mod2 (a b : Bool) :
    ((Finset.univ : Finset Bool).filter (fun q => (a = true → q = true) ∧ (q = true → b = true))).card % 2 =
    if a = b then 1 else 0 := by
  cases a <;> cases b <;> decide

private lemma detU_card_mod2 (y x d : Bool) :
    ((Finset.univ : Finset (Fin 4 → Bool)).filter (fun u =>
      if y then
        (x = true → u ⟨0, by decide⟩ = true) ∧ (d = true → u ⟨0, by decide⟩ = true) ∧
        (u ⟨1, by decide⟩ = true → u ⟨2, by decide⟩ = true) ∧ (u ⟨1, by decide⟩ = true → u ⟨3, by decide⟩ = true)
      else
        (x = true → d = true) ∧
        (u ⟨0, by decide⟩ = true → u ⟨1, by decide⟩ = true) ∧ (u ⟨2, by decide⟩ = true → u ⟨3, by decide⟩ = true))).card % 2 =
    if d = true ∨ x = y then 1 else 0 := by
  cases y <;> cases x <;> cases d <;> decide

private lemma chain2_card_mod2 :
    ((Finset.univ : Finset (Bool → Bool)).filter (fun a => a false = true → a true = true)).card % 2 = 1 := by
  decide

private lemma fork3_card_mod2 :
    ((Finset.univ : Finset (Fin 3 → Bool)).filter (fun a =>
      (a 0 = true → a 1 = true) ∧ (a 0 = true → a 2 = true))).card % 2 = 1 := by
  decide

private lemma side3_false_card :
    ((Finset.univ : Finset (Fin 3 → Bool)).filter (fun a => a 1 = true → a 2 = true)).card = 6 := by
  decide

private lemma side3_true_card :
    ((Finset.univ : Finset (Fin 3 → Bool)).filter (fun a =>
      (a 0 = true → a 1 = true) ∧ (a 0 = true → a 2 = true))).card = 5 := by
  decide

section MainProof
open scoped Classical

private lemma minCover_card_eq_mono {V : Type} [DecidableEq V] [Fintype V]
    (arc : V → V → Bool) (hirr : ∀ u, arc u u = false)
    (on : V → Bool) :
    let G := graphOfArcs arc
    let live := (Finset.univ : Finset (V × Bool)).filter (fun p => on p.1 = true)
    let cover := fun (C : Finset (V × Bool)) => C ⊆ live ∧
      ∀ p ∈ live, ∀ r ∈ G p, r ∈ live → p ∈ C ∨ r ∈ C
    ((Finset.univ : Finset (Finset (V × Bool))).filter
      (fun C => cover C ∧ ∀ W, cover W → C.card ≤ W.card)).card =
    ((Finset.univ : Finset (V → Bool)).filter (fun a =>
      (∀ u, on u = false → a u = false) ∧
      ∀ u v, on u = true → on v = true → arc u v = true → a u = true → a v = true)).card := by
  intro G live cover
  let S : Finset V := Finset.univ.filter (fun u => on u = true)
  have hmem_t : ∀ u v b, (v, b) ∈ G (u, true) ↔ b = false ∧ (v = u ∨ arc u v = true) := by
    intro u v b
    simp only [G, graphOfArcs, ↓reduceIte, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨w, hw, rfl, rfl⟩)
      · exact ⟨rfl, Or.inl rfl⟩
      · exact ⟨rfl, Or.inr hw⟩
    · rintro ⟨rfl, rfl | h⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨v, h, rfl, rfl⟩
  have hmem_f : ∀ u v b, (v, b) ∈ G (u, false) ↔ b = true ∧ (v = u ∨ arc v u = true) := by
    intro u v b
    simp only [G, graphOfArcs, Bool.false_eq_true, ↓reduceIte, Finset.mem_insert, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨w, hw, rfl, rfl⟩)
      · exact ⟨rfl, Or.inl rfl⟩
      · exact ⟨rfl, Or.inr hw⟩
    · rintro ⟨rfl, rfl | h⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨v, h, rfl, rfl⟩
  have hC0 : cover (S.image fun u => (u, false)) := by
    refine ⟨?_, ?_⟩
    · intro p hp; rcases Finset.mem_image.mp hp with ⟨u, hu, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩
    · rintro ⟨u, b1⟩ hp ⟨v, b2⟩ hr hrl
      cases b1
      · left; exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩, rfl⟩
      · have hb2 : b2 = false := ((hmem_t u v b2).mp hr).1
        subst hb2
        right; exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hrl).2⟩, rfl⟩
  have hC0_card : (S.image fun u => (u, false)).card = S.card :=
    Finset.card_image_of_injective S (fun _ _ h => (Prod.mk.inj h).1)
  have hge : ∀ W, cover W → S.card ≤ W.card := by
    intro W hW
    have hsub : S ⊆ W.image Prod.fst := by
      intro u hu
      have hon : on u = true := (Finset.mem_filter.mp hu).2
      have h1 : (u, false) ∈ live := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hon⟩
      have h2 : (u, true) ∈ live := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hon⟩
      rcases hW.2 (u, false) h1 (u, true) ((hmem_f u u true).mpr ⟨rfl, Or.inl rfl⟩) h2 with hf | ht
      · exact Finset.mem_image.mpr ⟨(u, false), hf, rfl⟩
      · exact Finset.mem_image.mpr ⟨(u, true), ht, rfl⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  have hmin_iff : ∀ C, (cover C ∧ ∀ W, cover W → C.card ≤ W.card) ↔
      (C ⊆ live ∧ (∀ u ∈ S, ((u, false) ∈ C) ≠ ((u, true) ∈ C)) ∧
       ∀ p ∈ live, ∀ r ∈ G p, r ∈ live → p ∈ C ∨ r ∈ C) := by
    intro C
    have hcard_eq : ∀ W, W ⊆ live → (∀ u ∈ S, (u, false) ∈ W ∨ (u, true) ∈ W) →
        (W.card = S.card ↔ ∀ u ∈ S, ((u, false) ∈ W) ≠ ((u, true) ∈ W)) := by
      intro W hsub hcov
      have hW_eq : W = S.biUnion fun u => W.filter (fun p => p.1 = u) := by
        ext p; simp only [Finset.mem_biUnion, Finset.mem_filter, S, Finset.mem_univ, true_and]
        constructor
        · intro hp; exact ⟨p.1, (Finset.mem_filter.mp (hsub hp)).2, hp, rfl⟩
        · rintro ⟨_, _, hp, _⟩; exact hp
      have hsum : W.card = ∑ u ∈ S, (W.filter (fun p => p.1 = u)).card := by
        conv_lhs => rw [hW_eq]
        refine Finset.card_biUnion fun u1 _ u2 _ hne => ?_
        dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro p h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      have hfib : ∀ u ∈ S, (W.filter (fun p => p.1 = u)).card =
          (if (u, false) ∈ W then 1 else 0) + (if (u, true) ∈ W then 1 else 0) := by
        intro u _
        have heq : W.filter (fun p => p.1 = u) =
            (if (u, false) ∈ W then {(u, false)} else ∅) ∪ (if (u, true) ∈ W then {(u, true)} else ∅) := by
          ext ⟨v, b⟩; simp only [Finset.mem_filter, Finset.mem_union]
          by_cases hvu : v = u
          · subst hvu; cases b <;> by_cases h1 : (v, false) ∈ W <;> by_cases h2 : (v, true) ∈ W <;> simp [h1, h2]
          · cases b <;> by_cases h1 : (u, false) ∈ W <;> by_cases h2 : (u, true) ∈ W <;> simp [h1, h2, hvu]
        rw [heq, Finset.card_union_of_disjoint]
        · split_ifs <;> simp
        · rw [Finset.disjoint_left]; intro p h1 h2
          split_ifs at h1 h2 <;> simp at h1 h2
          rw [h1] at h2; simp at h2
      have hge1 : ∀ u ∈ S, 1 ≤ (W.filter (fun p => p.1 = u)).card := by
        intro u hu; rw [hfib u hu]; rcases hcov u hu with h | h <;> split_ifs <;> omega
      constructor
      · intro hcard u hu
        have h1 : (W.filter (fun p => p.1 = u)).card = 1 := by
          by_contra hne
          have hgt : 1 < (W.filter (fun p => p.1 = u)).card := lt_of_le_of_ne (hge1 u hu) (Ne.symm hne)
          have hlt : ∑ _v ∈ S, 1 < ∑ v ∈ S, (W.filter (fun p => p.1 = v)).card :=
            Finset.sum_lt_sum (fun v hv => hge1 v hv) ⟨u, hu, hgt⟩
          simp only [Finset.sum_const, smul_eq_mul, mul_one] at hlt; omega
        rw [hfib u hu] at h1
        by_cases hf : (u, false) ∈ W <;> by_cases ht : (u, true) ∈ W <;> simp [hf, ht] at h1 ⊢
      · intro hne; rw [hsum]
        calc ∑ u ∈ S, (W.filter (fun p => p.1 = u)).card
            = ∑ _u ∈ S, 1 := Finset.sum_congr rfl fun u hu => by
              rw [hfib u hu]; have hne' := hne u hu
              by_cases hf : (u, false) ∈ W <;> by_cases ht : (u, true) ∈ W
              · exfalso; exact hne' (propext ⟨fun _ => ht, fun _ => hf⟩)
              · simp [hf, ht]
              · simp [hf, ht]
              · exfalso; exact hne' (propext ⟨fun h => absurd h hf, fun h => absurd h ht⟩)
          _ = S.card := by simp
    constructor
    · rintro ⟨hC, hmin⟩
      have hcard : C.card = S.card := le_antisymm ((hmin _ hC0).trans_eq hC0_card) (hge C hC)
      have hpair : ∀ u ∈ S, (u, false) ∈ C ∨ (u, true) ∈ C := fun u hu =>
        hC.2 (u, false) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩)
          (u, true) ((hmem_f u u true).mpr ⟨rfl, Or.inl rfl⟩)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩)
      exact ⟨hC.1, (hcard_eq C hC.1 hpair).mp hcard, hC.2⟩
    · rintro ⟨hsub, hne, hcov⟩
      have hpair : ∀ u ∈ S, (u, false) ∈ C ∨ (u, true) ∈ C := by
        intro u hu; have hne' := hne u hu
        by_cases hf : (u, false) ∈ C
        · exact Or.inl hf
        · by_cases ht : (u, true) ∈ C
          · exact Or.inr ht
          · exfalso; exact hne' (propext ⟨fun h => absurd h hf, fun h => absurd h ht⟩)
      have hcard : C.card = S.card := (hcard_eq C hsub hpair).mpr hne
      exact ⟨⟨hsub, hcov⟩, fun W hW => hcard.symm ▸ hge W hW⟩
  refine Finset.card_bij (fun C _ u => decide (on u = true ∧ (u, false) ∈ C)) ?_ ?_ ?_
  · intro C hC
    have hC' := (hmin_iff C).mp (Finset.mem_filter.mp hC).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun u hu => by simp [hu], fun u v hu hv huv hau => ?_⟩
    simp only [decide_eq_true_eq] at hau ⊢
    refine ⟨hv, ?_⟩
    have huS : u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩
    have hvS : v ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
    have huT : (u, true) ∉ C := fun h => hC'.2.1 u huS (propext ⟨fun _ => h, fun _ => hau.2⟩)
    rcases hC'.2.2 (u, true) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩) (v, false)
        ((hmem_t u v false).mpr ⟨rfl, Or.inr huv⟩) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩) with h1 | h2
    · exact absurd h1 huT
    · exact h2
  · intro C1 h1 C2 h2 heq
    have h1' := (hmin_iff C1).mp (Finset.mem_filter.mp h1).2
    have h2' := (hmin_iff C2).mp (Finset.mem_filter.mp h2).2
    ext ⟨u, b⟩
    by_cases hu : on u = true
    · have hf : (u, false) ∈ C1 ↔ (u, false) ∈ C2 := by
        have h := congrFun heq u
        simp only [hu, true_and] at h
        by_cases a1 : (u, false) ∈ C1 <;> by_cases a2 : (u, false) ∈ C2 <;> simp [a1, a2] at h ⊢
      cases b
      · exact hf
      · have huS : u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩
        have n1 := h1'.2.1 u huS; have n2 := h2'.2.1 u huS
        by_cases a1 : (u, false) ∈ C1
        · have a2 := hf.mp a1
          have t1 : (u, true) ∉ C1 := fun h => n1 (propext ⟨fun _ => h, fun _ => a1⟩)
          have t2 : (u, true) ∉ C2 := fun h => n2 (propext ⟨fun _ => h, fun _ => a2⟩)
          exact iff_of_false t1 t2
        · have a2 : (u, false) ∉ C2 := fun h => a1 (hf.mpr h)
          have t1 : (u, true) ∈ C1 := by by_contra h; exact n1 (propext ⟨fun x => absurd x a1, fun x => absurd x h⟩)
          have t2 : (u, true) ∈ C2 := by by_contra h; exact n2 (propext ⟨fun x => absurd x a2, fun x => absurd x h⟩)
          exact iff_of_true t1 t2
    · have n1 : (u, b) ∉ C1 := fun h => hu (Finset.mem_filter.mp (h1'.1 h)).2
      have n2 : (u, b) ∉ C2 := fun h => hu (Finset.mem_filter.mp (h2'.1 h)).2
      exact iff_of_false n1 n2
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    let C : Finset (V × Bool) := live.filter fun p => if p.2 then a p.1 = false else a p.1 = true
    refine ⟨C, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hmin_iff C]
      refine ⟨Finset.filter_subset _ _, ?_, ?_⟩
      · intro u hu
        have hon : on u = true := (Finset.mem_filter.mp hu).2
        have hlf : (u, false) ∈ live := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hon⟩
        have hlt : (u, true) ∈ live := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hon⟩
        simp only [C, Finset.mem_filter, hlf, hlt, true_and, Bool.false_eq_true, ↓reduceIte]
        cases ha_u : a u <;> decide
      · rintro ⟨u, b1⟩ hp ⟨v, b2⟩ hr hrl
        have hu : on u = true := (Finset.mem_filter.mp hp).2
        have hv : on v = true := (Finset.mem_filter.mp hrl).2
        simp only [C, Finset.mem_filter, hp, hrl, true_and]
        cases b1
        · rcases (hmem_f u v b2).mp hr with ⟨rfl, hvu | huv⟩
          · rw [hvu]; simp only [Bool.false_eq_true, ↓reduceIte]; cases a u <;> simp
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases hav : a v
            · right; rfl
            · left; exact ha.2 v u hv hu huv hav
        · rcases (hmem_t u v b2).mp hr with ⟨rfl, hvu | huv⟩
          · rw [hvu]; simp only [Bool.false_eq_true, ↓reduceIte]; cases a u <;> simp
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases hau : a u
            · left; rfl
            · right; exact ha.2 u v hu hv huv hau
    · funext u
      by_cases hu : on u = true
      · have hlf : (u, false) ∈ live := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩
        simp [C, hu, hlf]
      · have hof : on u = false := Bool.eq_false_iff.mpr hu
        simp [hu, ha.1 u hof]

private lemma case_n0 :
    let Word := Fin 0 → Bool
    let Table := Word → Bool
    ∃ (m : Nat) (G : (Fin m × Bool) → Finset (Fin m × Bool))
      (side : Fin m → Bool) (tag : Fin m → Option (Word × Bool)) (keep : Bool → Nat),
      m ≤ 15000*(0+1)*2^0 ∧ (∀ i, (i,true) ∈ G (i,false)) ∧
      (∀ p, p ∉ G p ∧ (G p).card ≤ 3) ∧ (∀ p r, r ∈ G p ↔ p ∈ G r) ∧
      (∀ p, ∀ r ∈ G p, p.2 ≠ r.2) ∧
      (∀ p, ((G p).filter (fun r => side r.1 ≠ side p.1)).card ≤ 1) ∧
      ((Finset.univ : Finset (Fin m × Bool)).filter (fun p =>
        side p.1 = false ∧ ∃ r ∈ G p, side r.1 = true)).card ≤ 0 ∧
      (∃ (l : Nat) (bag : Fin l → Finset (Fin m × Bool)),
        (∀ t, (bag t).card ≤ 0+37) ∧ (∀ p, ∃ t, p ∈ bag t) ∧
        (∀ p r, r ∈ G p → ∃ t, p ∈ bag t ∧ r ∈ bag t) ∧
        ∀ p s t u, s ≤ t → t ≤ u → p ∈ bag s → p ∈ bag u → p ∈ bag t) ∧
      ∀ f g : Table,
        let on := fun i => (tag i).elim true (fun p => decide ((if side i then g else f) p.1 = p.2))
        let live := (Finset.univ : Finset (Fin m × Bool)).filter (fun p => on p.1)
        let cover := fun (C : Finset (Fin m × Bool)) => C ⊆ live ∧
          ∀ p ∈ live, ∀ r ∈ G p, r ∈ live → p ∈ C ∨ r ∈ C
        let opt := ((Finset.univ : Finset (Finset (Fin m × Bool))).filter
          (fun C => cover C ∧ ∀ W, cover W → C.card ≤ W.card)).card
        (∀ b, ((Finset.univ : Finset (Fin m)).filter (fun i => side i = b ∧ on i = true)).card = keep b) ∧
        opt % 2 = ((Finset.univ : Finset Word).filter (fun y => f y && g y)).card % 2 := by
  let Word := Fin 0 → Bool
  let w0 : Word := fun i => i.elim0
  let arc : Fin 12 → Fin 12 → Bool := fun u v =>
    (decide (u.val = 1 ∧ v.val = 2)) ||
    (decide (u.val = 3 ∧ (v.val = 4 ∨ v.val = 5))) ||
    (decide (u.val = 7 ∧ v.val = 8)) ||
    (decide (u.val = 9 ∧ (v.val = 10 ∨ v.val = 11)))
  let G := graphOfArcs arc
  let side : Fin 12 → Bool := fun i => decide (6 ≤ i.val)
  let tag : Fin 12 → Option (Word × Bool) := fun i =>
    if i.val < 3 ∨ (6 ≤ i.val ∧ i.val < 9) then some (w0, false) else some (w0, true)
  let keep : Bool → Nat := fun _ => 3
  have hirr : ∀ u, arc u u = false := by decide
  have hout : ∀ u, (Finset.univ.filter (fun v => arc u v = true)).card ≤ 2 := by decide
  have hin : ∀ u, (Finset.univ.filter (fun v => arc v u = true)).card ≤ 2 := by decide
  rcases graphOfArcs_props arc hirr hout hin with ⟨hmatch, hdeg, hsym, hbip⟩
  have harc_side : ∀ u v : Fin 12, arc u v = true → side u = side v := by
    intro u v h; simp only [arc, Bool.or_eq_true, decide_eq_true_eq] at h
    simp only [side]; rcases h with ((⟨h1, h2⟩ | ⟨h1, h2 | h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2 | h2⟩ <;> simp [h1, h2]
  have hnocross : ∀ p, ∀ r ∈ G p, side r.1 = side p.1 := by
    rintro ⟨u, b1⟩ ⟨v, b2⟩ h
    cases b1 <;> simp only [G, graphOfArcs, Bool.false_eq_true, ↓reduceIte, Finset.mem_insert,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at h
    · rcases h with ⟨rfl, _⟩ | ⟨w, hw, rfl, _⟩
      · rfl
      · exact harc_side w u hw
    · rcases h with ⟨rfl, _⟩ | ⟨w, hw, rfl, _⟩
      · rfl
      · exact (harc_side u w hw).symm
  refine ⟨12, G, side, tag, keep, by decide, hmatch, hdeg, hsym, hbip, ?_, ?_, ?_, ?_⟩
  · intro p
    have hemp : (G p).filter (fun r => side r.1 ≠ side p.1) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro r hr; exact not_not.mpr (hnocross p r hr)
    rw [hemp]; simp
  · have hemp : (Finset.univ : Finset (Fin 12 × Bool)).filter (fun p =>
        side p.1 = false ∧ ∃ r ∈ G p, side r.1 = true) = ∅ := by
      rw [Finset.filter_eq_empty_iff]; intro p _; rintro ⟨hp, r, hr, hrt⟩
      have := hnocross p r hr; rw [hp, hrt] at this; simp at this
    rw [hemp]; simp
  · refine ⟨1, fun _ => Finset.univ, fun _ => by simp, fun p => ⟨0, Finset.mem_univ p⟩,
      fun p r _ => ⟨0, Finset.mem_univ p, Finset.mem_univ r⟩, fun _ _ _ _ _ _ _ _ => Finset.mem_univ _⟩
  · intro f g on live cover opt
    have hw_eq : ∀ y : Word, y = w0 := fun y => funext fun i => i.elim0
    have hcard_ip : ((Finset.univ : Finset Word).filter (fun y => f y && g y)).card =
        if (f w0 && g w0) = true then 1 else 0 := by
      have hu : (Finset.univ : Finset Word) = {w0} := by
        ext y; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]; exact hw_eq y
      rw [hu, Finset.filter_singleton]; cases hf : f w0 <;> cases hg : g w0 <;> simp [hf, hg]
    have hon_f : ∀ i : Fin 12, i.val < 6 → on i = decide (f w0 = !(decide (i.val < 3))) := by
      intro i hi
      have hs : side i = false := by simp only [side, decide_eq_false_iff_not]; omega
      unfold on tag; simp only [hs, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : i.val < 3
      · have hc : i.val < 3 ∨ 6 ≤ i.val ∧ i.val < 9 := Or.inl h3
        rw [if_pos hc]; simp [h3]
      · have hc : ¬ (i.val < 3 ∨ 6 ≤ i.val ∧ i.val < 9) := by omega
        rw [if_neg hc]; simp [h3]
    have hon_g : ∀ i : Fin 12, 6 ≤ i.val → on i = decide (g w0 = !(decide (i.val < 9))) := by
      intro i hi
      have hs : side i = true := by simp only [side, decide_eq_true_eq]; omega
      unfold on tag; simp only [hs, ↓reduceIte]
      by_cases h9 : i.val < 9
      · have hc : i.val < 3 ∨ 6 ≤ i.val ∧ i.val < 9 := Or.inr ⟨hi, h9⟩
        rw [if_pos hc]; simp [h9]
      · have hc : ¬ (i.val < 3 ∨ 6 ≤ i.val ∧ i.val < 9) := by omega
        rw [if_neg hc]; simp [h9]
    have hkeep : ∀ b, ((Finset.univ : Finset (Fin 12)).filter (fun i => side i = b ∧ on i = true)).card = 3 := by
      intro b
      have hcard_iv : ∀ lo : ℕ, lo + 3 ≤ 12 → ((Finset.univ : Finset (Fin 12)).filter (fun i => lo ≤ i.val ∧ i.val < lo + 3)).card = 3 := by
        intro lo hlo
        have hbij : ((Finset.univ : Finset (Fin 12)).filter (fun i => lo ≤ i.val ∧ i.val < lo + 3)).card = (Finset.univ : Finset (Fin 3)).card :=
          Finset.card_bij (fun i hi => ⟨i.val - lo, by have := (Finset.mem_filter.mp hi).2; omega⟩)
            (fun _ _ => Finset.mem_univ _)
            (fun i1 h1 i2 h2 heq => by have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; have := Fin.mk.inj heq; exact Fin.ext (by omega))
            (fun j _ => ⟨⟨lo + j.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, Fin.ext (by dsimp only; omega)⟩)
        rw [hbij]; simp
      cases b
      · cases hf : f w0
        · refine (congrArg Finset.card ?_).trans (hcard_iv 0 (by omega))
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, side, decide_eq_false_iff_not]
          by_cases hi : i.val < 6
          · rw [hon_f i hi, hf]; by_cases h3 : i.val < 3 <;> simp [h3] <;> omega
          · constructor <;> intro h <;> omega
        · refine (congrArg Finset.card ?_).trans (hcard_iv 3 (by omega))
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, side, decide_eq_false_iff_not]
          by_cases hi : i.val < 6
          · rw [hon_f i hi, hf]; by_cases h3 : i.val < 3 <;> simp [h3] <;> omega
          · constructor <;> intro h <;> omega
      · cases hg : g w0
        · refine (congrArg Finset.card ?_).trans (hcard_iv 6 (by omega))
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, side, decide_eq_true_eq]
          by_cases hi : 6 ≤ i.val
          · rw [hon_g i hi, hg]; by_cases h9 : i.val < 9 <;> simp [h9] <;> omega
          · constructor <;> intro h <;> omega
        · refine (congrArg Finset.card ?_).trans (hcard_iv 9 (by omega))
          ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, side, decide_eq_true_eq]
          by_cases hi : 6 ≤ i.val
          · rw [hon_g i hi, hg]; by_cases h9 : i.val < 9 <;> simp [h9] <;> omega
          · constructor <;> intro h <;> omega
    refine ⟨hkeep, ?_⟩
    have hopt_eq : opt = ((Finset.univ : Finset (Fin 12 → Bool)).filter (fun a =>
        (∀ u, on u = false → a u = false) ∧
        ∀ u v, on u = true → on v = true → arc u v = true → a u = true → a v = true)).card := by
      have hlive : live = (Finset.univ : Finset (Fin 12 × Bool)).filter (fun p => on p.1 = true) := by
        ext p; simp [live]
      refine (congrArg Finset.card ?_).trans ((minCover_card_eq_mono arc hirr on).trans (congrArg Finset.card ?_))
      · ext C; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; dsimp only [cover, G]; rw [hlive]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      · ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hopt_eq, hcard_ip]
    let Sside (b : Bool) : Finset (Fin 3 → Bool) :=
      if b then
        (Finset.univ : Finset (Fin 3 → Bool)).filter (fun a => (a 0 = true → a 1 = true) ∧ (a 0 = true → a 2 = true))
      else
        (Finset.univ : Finset (Fin 3 → Bool)).filter (fun a => a 1 = true → a 2 = true)
    have hScard : ∀ b : Bool, (Sside b).card = if b then 5 else 6 := by
      intro b; cases b
      · refine (congrArg Finset.card ?_).trans side3_false_card
        ext a; simp only [Sside, Bool.false_eq_true, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
      · refine (congrArg Finset.card ?_).trans side3_true_card
        ext a; simp only [Sside, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
    have hbij : ((Finset.univ : Finset (Fin 12 → Bool)).filter (fun a =>
          (∀ u, on u = false → a u = false) ∧
          ∀ u v, on u = true → on v = true → arc u v = true → a u = true → a v = true)).card =
        (Sside (f w0) ×ˢ Sside (g w0)).card := by
      refine Finset.card_bij (fun a _ =>
        (fun i : Fin 3 => a ⟨(if f w0 then 3 else 0) + i.val, by cases f w0 <;> simp <;> omega⟩,
         fun i : Fin 3 => a ⟨(if g w0 then 9 else 6) + i.val, by cases g w0 <;> simp <;> omega⟩)) ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        rw [Finset.mem_product]
        constructor
        · cases hf : f w0
          · simp only [Sside, hf, Bool.false_eq_true, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and, zero_add]
            intro h1; exact ha.2 ⟨1, by decide⟩ ⟨2, by decide⟩ (by rw [hon_f _ (by decide), hf]; decide) (by rw [hon_f _ (by decide), hf]; decide) (by decide) h1
          · simp only [Sside, hf, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨fun h0 => ha.2 ⟨3, by decide⟩ ⟨4, by decide⟩ (by rw [hon_f _ (by decide), hf]; decide) (by rw [hon_f _ (by decide), hf]; decide) (by decide) h0,
              fun h0 => ha.2 ⟨3, by decide⟩ ⟨5, by decide⟩ (by rw [hon_f _ (by decide), hf]; decide) (by rw [hon_f _ (by decide), hf]; decide) (by decide) h0⟩
        · cases hg : g w0
          · simp only [Sside, hg, Bool.false_eq_true, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
            intro h1; exact ha.2 ⟨7, by decide⟩ ⟨8, by decide⟩ (by rw [hon_g _ (by decide), hg]; decide) (by rw [hon_g _ (by decide), hg]; decide) (by decide) h1
          · simp only [Sside, hg, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨fun h0 => ha.2 ⟨9, by decide⟩ ⟨10, by decide⟩ (by rw [hon_g _ (by decide), hg]; decide) (by rw [hon_g _ (by decide), hg]; decide) (by decide) h0,
              fun h0 => ha.2 ⟨9, by decide⟩ ⟨11, by decide⟩ (by rw [hon_g _ (by decide), hg]; decide) (by rw [hon_g _ (by decide), hg]; decide) (by decide) h0⟩
      · intro a1 h1 a2 h2 heq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        rcases Prod.mk.inj heq with ⟨hL, hR⟩
        funext u
        by_cases h3 : u.val < 3
        · cases hf : f w0
          · have h := congrFun hL ⟨u.val, h3⟩; simp only [hf, Bool.false_eq_true, ↓reduceIte, zero_add] at h; exact h
          · have ho : on u = false := by rw [hon_f u (by omega), hf]; simp [h3]
            exact (h1.1 u ho).trans (h2.1 u ho).symm
        · by_cases h6 : u.val < 6
          · cases hf : f w0
            · have ho : on u = false := by rw [hon_f u h6, hf]; simp [h3]
              exact (h1.1 u ho).trans (h2.1 u ho).symm
            · have h := congrFun hL ⟨u.val - 3, by omega⟩; simp only [hf, ↓reduceIte] at h
              have hu : (⟨3 + (u.val - 3), by omega⟩ : Fin 12) = u := Fin.ext (by dsimp only; omega)
              rwa [hu] at h
          · by_cases h9 : u.val < 9
            · cases hg : g w0
              · have h := congrFun hR ⟨u.val - 6, by omega⟩; simp only [hg, Bool.false_eq_true, ↓reduceIte] at h
                have hu : (⟨6 + (u.val - 6), by omega⟩ : Fin 12) = u := Fin.ext (by dsimp only; omega)
                rwa [hu] at h
              · have ho : on u = false := by rw [hon_g u (by omega), hg]; simp [h9]
                exact (h1.1 u ho).trans (h2.1 u ho).symm
            · cases hg : g w0
              · have ho : on u = false := by rw [hon_g u (by omega), hg]; simp [h9]
                exact (h1.1 u ho).trans (h2.1 u ho).symm
              · have h := congrFun hR ⟨u.val - 9, by omega⟩; simp only [hg, ↓reduceIte] at h
                have hu : (⟨9 + (u.val - 9), by omega⟩ : Fin 12) = u := Fin.ext (by dsimp only; omega)
                rwa [hu] at h
      · rintro ⟨aL, aR⟩ hLR
        rw [Finset.mem_product] at hLR
        let a : Fin 12 → Bool := fun u =>
          if h3 : u.val < 3 then if f w0 then false else aL ⟨u.val, h3⟩
          else if h6 : u.val < 6 then if f w0 then aL ⟨u.val - 3, by omega⟩ else false
          else if h9 : u.val < 9 then if g w0 then false else aR ⟨u.val - 6, by omega⟩
          else if g w0 then aR ⟨u.val - 9, by omega⟩ else false
        refine ⟨a, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨fun u hu => ?_, fun u v hu hv huv hau => ?_⟩
          · dsimp only [a]
            by_cases h3 : u.val < 3
            · rw [hon_f u (by omega)] at hu; simp only [h3, ↓reduceIte, ↓reduceDIte] at hu ⊢
              cases hf : f w0 <;> simp [hf] at hu ⊢
            · by_cases h6 : u.val < 6
              · rw [hon_f u h6] at hu; simp only [h3, h6, ↓reduceIte, ↓reduceDIte] at hu ⊢
                cases hf : f w0 <;> simp [hf] at hu ⊢
              · by_cases h9 : u.val < 9
                · rw [hon_g u (by omega)] at hu; simp only [h3, h6, h9, ↓reduceIte, ↓reduceDIte] at hu ⊢
                  cases hg : g w0 <;> simp [hg] at hu ⊢
                · rw [hon_g u (by omega)] at hu; simp only [h3, h6, h9, ↓reduceIte, ↓reduceDIte] at hu ⊢
                  cases hg : g w0 <;> simp [hg] at hu ⊢
          · rcases hLR with ⟨hL, hR⟩
            simp only [arc, Bool.or_eq_true, decide_eq_true_eq] at huv
            rcases huv with ((⟨hu1, hv2⟩ | ⟨hu3, hv4 | hv5⟩) | ⟨hu7, hv8⟩) | ⟨hu9, hv10 | hv11⟩
            · have hu' : u = ⟨1, by decide⟩ := Fin.ext hu1; have hv' : v = ⟨2, by decide⟩ := Fin.ext hv2; subst hu' hv'
              cases hf : f w0
              · simp only [Sside, hf, Bool.false_eq_true, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and] at hL
                simp only [a, hf, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, Nat.reduceLT] at hau ⊢; exact hL hau
              · rw [hon_f _ (by decide), hf] at hu; simp at hu
            · have hu' : u = ⟨3, by decide⟩ := Fin.ext hu3; have hv' : v = ⟨4, by decide⟩ := Fin.ext hv4; subst hu' hv'
              cases hf : f w0
              · rw [hon_f _ (by decide), hf] at hu; simp at hu
              · simp only [Sside, hf, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and] at hL
                simp only [a, hf, ↓reduceIte, ↓reduceDIte, Nat.reduceLT, Nat.sub_self] at hau ⊢; exact hL.1 hau
            · have hu' : u = ⟨3, by decide⟩ := Fin.ext hu3; have hv' : v = ⟨5, by decide⟩ := Fin.ext hv5; subst hu' hv'
              cases hf : f w0
              · rw [hon_f _ (by decide), hf] at hu; simp at hu
              · simp only [Sside, hf, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and] at hL
                simp only [a, hf, ↓reduceIte, ↓reduceDIte, Nat.reduceLT, Nat.sub_self] at hau ⊢; exact hL.2 hau
            · have hu' : u = ⟨7, by decide⟩ := Fin.ext hu7; have hv' : v = ⟨8, by decide⟩ := Fin.ext hv8; subst hu' hv'
              cases hg : g w0
              · simp only [Sside, hg, Bool.false_eq_true, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and] at hR
                simp only [a, hg, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, Nat.reduceLT] at hau ⊢; exact hR hau
              · rw [hon_g _ (by decide), hg] at hu; simp at hu
            · have hu' : u = ⟨9, by decide⟩ := Fin.ext hu9; have hv' : v = ⟨10, by decide⟩ := Fin.ext hv10; subst hu' hv'
              cases hg : g w0
              · rw [hon_g _ (by decide), hg] at hu; simp at hu
              · simp only [Sside, hg, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and] at hR
                simp only [a, hg, ↓reduceIte, ↓reduceDIte, Nat.reduceLT, Nat.sub_self] at hau ⊢; exact hR.1 hau
            · have hu' : u = ⟨9, by decide⟩ := Fin.ext hu9; have hv' : v = ⟨11, by decide⟩ := Fin.ext hv11; subst hu' hv'
              cases hg : g w0
              · rw [hon_g _ (by decide), hg] at hu; simp at hu
              · simp only [Sside, hg, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and] at hR
                simp only [a, hg, ↓reduceIte, ↓reduceDIte, Nat.reduceLT, Nat.sub_self] at hau ⊢; exact hR.2 hau
        · apply Prod.ext <;> funext i
          · cases hf : f w0
            · dsimp only [a]; simp only [hf, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, zero_add, i.isLt]
            · dsimp only [a]; simp only [hf, ↓reduceIte]
              have h1 : ¬ 3 + i.val < 3 := by omega
              have h2 : 3 + i.val < 6 := by omega
              simp only [h1, h2, ↓reduceDIte]; congr 1; exact Fin.ext (by dsimp only; omega)
          · cases hg : g w0
            · dsimp only [a]; simp only [hg, Bool.false_eq_true, ↓reduceIte]
              have h1 : ¬ 6 + i.val < 3 := by omega
              have h2 : ¬ 6 + i.val < 6 := by omega
              have h3 : 6 + i.val < 9 := by omega
              simp only [h1, h2, h3, ↓reduceDIte]; congr 1; exact Fin.ext (by dsimp only; omega)
            · dsimp only [a]; simp only [hg, ↓reduceIte]
              have h1 : ¬ 9 + i.val < 3 := by omega
              have h2 : ¬ 9 + i.val < 6 := by omega
              have h3 : ¬ 9 + i.val < 9 := by omega
              simp only [h1, h2, h3, ↓reduceDIte]; congr 1; exact Fin.ext (by dsimp only; omega)
    rw [hbij, Finset.card_product, hScard, hScard]
    cases f w0 <;> cases g w0 <;> decide

end MainProof

private inductive PairV (t : ℕ) : Type
  | initReg (side : Bool) (k : Fin (t + 1))
  | bridge (k : Fin (t + 1))
  | regP (side : Bool) (w : Fin (2 ^ (t + 1))) (k : Fin (t + 1))
  | regX (side : Bool) (w : Fin (2 ^ (t + 1))) (k : Fin (t + 1))
  | detD (side : Bool) (w : Fin (2 ^ (t + 1))) (k : Fin (t + 1))
  | detQ (side : Bool) (w : Fin (2 ^ (t + 1))) (k : Fin t)
  | detU (side : Bool) (w : Fin (2 ^ (t + 1))) (k : Fin (t + 1)) (c : Fin 4)
  | detF (side : Bool) (w : Fin (2 ^ (t + 1))) (c : Fin 3)
  | padT (side : Bool) (w : Fin (2 ^ (t + 1))) (j : Fin (3 * (t + 1) + 1)) (b : Bool)
  deriving DecidableEq

private def pairVSumEquiv (t : ℕ) :
    PairV t ≃
      (Bool × Fin (t + 1)) ⊕
      Fin (t + 1) ⊕
      (Bool × Fin (2 ^ (t + 1)) × Fin (t + 1)) ⊕
      (Bool × Fin (2 ^ (t + 1)) × Fin (t + 1)) ⊕
      (Bool × Fin (2 ^ (t + 1)) × Fin (t + 1)) ⊕
      (Bool × Fin (2 ^ (t + 1)) × Fin t) ⊕
      (Bool × Fin (2 ^ (t + 1)) × Fin (t + 1) × Fin 4) ⊕
      (Bool × Fin (2 ^ (t + 1)) × Fin 3) ⊕
      (Bool × Fin (2 ^ (t + 1)) × Fin (3 * (t + 1) + 1) × Bool) where
  toFun
    | .initReg s k => Sum.inl (s, k)
    | .bridge k => Sum.inr (Sum.inl k)
    | .regP s w k => Sum.inr (Sum.inr (Sum.inl (s, w, k)))
    | .regX s w k => Sum.inr (Sum.inr (Sum.inr (Sum.inl (s, w, k))))
    | .detD s w k => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (s, w, k)))))
    | .detQ s w k => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (s, w, k))))))
    | .detU s w k c => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (s, w, k, c)))))))
    | .detF s w c => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (s, w, c))))))))
    | .padT s w j b => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (s, w, j, b))))))))
  invFun
    | Sum.inl (s, k) => .initReg s k
    | Sum.inr (Sum.inl k) => .bridge k
    | Sum.inr (Sum.inr (Sum.inl (s, w, k))) => .regP s w k
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl (s, w, k)))) => .regX s w k
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (s, w, k))))) => .detD s w k
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (s, w, k)))))) => .detQ s w k
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (s, w, k, c))))))) => .detU s w k c
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (s, w, c)))))))) => .detF s w c
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (s, w, j, b)))))))) => .padT s w j b
  left_inv u := by cases u <;> rfl
  right_inv u := by rcases u with ⟨s,k⟩ | k | ⟨s,w,k⟩ | ⟨s,w,k⟩ | ⟨s,w,k⟩ | ⟨s,w,k⟩ | ⟨s,w,k,c⟩ | ⟨s,w,c⟩ | ⟨s,w,j,b⟩ <;> rfl

private instance pairVFintype (t : ℕ) : Fintype (PairV t) :=
  Fintype.ofEquiv _ (pairVSumEquiv t).symm

private lemma pairV_card_le (t : ℕ) :
    Fintype.card (PairV t) ≤ 15000 * ((t + 1) + 1) * 2 ^ (t + 1) := by
  have hc : Fintype.card (PairV t) =
      2 * (t + 1) + (t + 1) + 2 * 2 ^ (t + 1) * (t + 1) + 2 * 2 ^ (t + 1) * (t + 1) +
      2 * 2 ^ (t + 1) * (t + 1) + 2 * 2 ^ (t + 1) * t + 2 * 2 ^ (t + 1) * ((t + 1) * 4) +
      2 * 2 ^ (t + 1) * 3 + 2 * 2 ^ (t + 1) * ((3 * (t + 1) + 1) * 2) := by
    rw [Fintype.card_congr (pairVSumEquiv t)]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    ring
  rw [hc]
  have hpow : 1 ≤ 2 ^ (t + 1) := Nat.one_le_pow _ _ (by decide)
  nlinarith

private def pairSide {t : ℕ} : PairV t → Bool
  | .initReg s _ => s
  | .bridge _ => false
  | .regP s _ _ => s
  | .regX s _ _ => s
  | .detD s _ _ => s
  | .detQ s _ _ => s
  | .detU s _ _ _ => s
  | .detF s _ _ => s
  | .padT s _ _ _ => s

private def pairTag {t : ℕ} : PairV t → Option ((Fin (t + 1) → Bool) × Bool)
  | .initReg _ _ => none
  | .bridge _ => none
  | .regP _ _ _ => none
  | .regX _ _ _ => none
  | .detD _ w _ => some (wordOf (t + 1) w, false)
  | .detQ _ w _ => some (wordOf (t + 1) w, false)
  | .detU _ w _ _ => some (wordOf (t + 1) w, false)
  | .detF _ w _ => some (wordOf (t + 1) w, false)
  | .padT _ w _ _ => some (wordOf (t + 1) w, true)

private def prevReg {t : ℕ} (s : Bool) (w : Fin (2 ^ (t + 1))) (k : Fin (t + 1)) : PairV t :=
  if h : w.val = 0 then .initReg s k else .regX s ⟨w.val - 1, by omega⟩ k

private def pairOut {t : ℕ} : PairV t → Finset (PairV t)
  | .initReg s k =>
    let w0 : Fin (2 ^ (t + 1)) := ⟨0, Nat.two_pow_pos _⟩
    {.regP s w0 k, if wordOf (t + 1) w0 k then .detU s w0 k ⟨0, by decide⟩ else .detD s w0 k}
  | .bridge k => {.initReg true k}
  | .regP s w k => {.regX s w k}
  | .regX s w k =>
    if h : w.val + 1 < 2 ^ (t + 1) then
      let w1 : Fin (2 ^ (t + 1)) := ⟨w.val + 1, h⟩
      {.regP s w1 k, if wordOf (t + 1) w1 k then .detU s w1 k ⟨0, by decide⟩ else .detD s w1 k}
    else if s = false then {.bridge k} else ∅
  | .detD s w k =>
    (if h : k.val < t then {.detQ s w ⟨k.val, h⟩} else ∅) ∪
    (if wordOf (t + 1) w k then {.detU s w k ⟨0, by decide⟩} else ∅)
  | .detQ s w k => {.detD s w k.succ}
  | .detU s w k c =>
    if wordOf (t + 1) w k then
      if c.val = 1 then {.detU s w k ⟨2, by decide⟩, .detU s w k ⟨3, by decide⟩} else ∅
    else
      if c.val = 0 then {.detU s w k ⟨1, by decide⟩}
      else if c.val = 2 then {.detU s w k ⟨3, by decide⟩} else ∅
  | .detF s w c =>
    if c.val = 0 then {.detF s w ⟨1, by decide⟩, .detF s w ⟨2, by decide⟩} else ∅
  | .padT s w j b =>
    if b = false then {.padT s w j true} else ∅

private def pairIn {t : ℕ} : PairV t → Finset (PairV t)
  | .initReg s k => if s = true then {.bridge k} else ∅
  | .bridge k => {.regX false ⟨2 ^ (t + 1) - 1, Nat.sub_lt (Nat.two_pow_pos _) (by decide)⟩ k}
  | .regP s w k => {prevReg s w k}
  | .regX s w k => {.regP s w k}
  | .detD s w k =>
    (if h : 0 < k.val then {.detQ s w ⟨k.val - 1, by omega⟩} else ∅) ∪
    (if wordOf (t + 1) w k = false then {prevReg s w k} else ∅)
  | .detQ s w k => {.detD s w k.castSucc}
  | .detU s w k c =>
    if wordOf (t + 1) w k then
      if c.val = 0 then {prevReg s w k, .detD s w k}
      else if c.val = 2 ∨ c.val = 3 then {.detU s w k ⟨1, by decide⟩} else ∅
    else
      if c.val = 1 then {.detU s w k ⟨0, by decide⟩}
      else if c.val = 3 then {.detU s w k ⟨2, by decide⟩} else ∅
  | .detF s w c =>
    if c.val = 1 ∨ c.val = 2 then {.detF s w ⟨0, by decide⟩} else ∅
  | .padT s w j b =>
    if b = true then {.padT s w j false} else ∅

private def pairArc {t : ℕ} (u v : PairV t) : Bool := decide (v ∈ pairOut u)

private lemma pairArc_iff_in {t : ℕ} (u v : PairV t) : v ∈ pairOut u ↔ u ∈ pairIn v := by
  cases u with
  | initReg s k =>
    cases v with
    | regP s' w k' =>
      simp only [pairOut, pairIn, prevReg, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · rcases PairV.regP.inj h with ⟨rfl, rfl, rfl⟩; simp
        · by_cases h1 : wordOf (t + 1) ⟨0, Nat.two_pow_pos _⟩ k = true
          · rw [if_pos h1] at h; cases h
          · rw [if_neg h1] at h; cases h
      · intro h
        by_cases hw0 : w.val = 0
        · rw [dif_pos hw0] at h
          rcases PairV.initReg.inj h with ⟨rfl, rfl⟩; left; congr 1; exact Fin.ext hw0
        · rw [dif_neg hw0] at h; cases h
    | detD s' w k' =>
      simp only [pairOut, pairIn, prevReg, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · cases h
        · by_cases h1 : wordOf (t + 1) ⟨0, Nat.two_pow_pos _⟩ k = true
          · rw [if_pos h1] at h; cases h
          · rw [if_neg h1] at h
            rcases PairV.detD.inj h with ⟨rfl, rfl, rfl⟩
            right; rw [if_pos (Bool.eq_false_iff.mpr h1), dif_pos rfl]; exact Finset.mem_singleton_self _
      · rintro (h | h)
        · split_ifs at h <;> simp at h
        · by_cases h1 : wordOf (t + 1) w k' = false
          · rw [if_pos h1] at h
            by_cases h2 : w.val = 0
            · rw [dif_pos h2, Finset.mem_singleton] at h
              rcases PairV.initReg.inj h with ⟨rfl, rfl⟩
              have hw : w = ⟨0, Nat.two_pow_pos _⟩ := Fin.ext h2
              subst hw; right; rw [if_neg (by rw [h1]; decide)]
            · rw [dif_neg h2, Finset.mem_singleton] at h; cases h
          · rw [if_neg h1] at h; simp at h
    | detU s' w k' c =>
      simp only [pairOut, pairIn, prevReg, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · cases h
        · by_cases h1 : wordOf (t + 1) ⟨0, Nat.two_pow_pos _⟩ k = true
          · rw [if_pos h1] at h
            rcases PairV.detU.inj h with ⟨rfl, rfl, rfl, rfl⟩
            rw [if_pos h1, if_pos rfl, dif_pos rfl]; simp
          · rw [if_neg h1] at h; cases h
      · intro h
        by_cases h1 : wordOf (t + 1) w k' = true
        · rw [if_pos h1] at h
          by_cases h2 : c.val = 0
          · rw [if_pos h2] at h
            rcases Finset.mem_insert.mp h with h | h
            · by_cases hw0 : w.val = 0
              · rw [dif_pos hw0] at h
                rcases PairV.initReg.inj h with ⟨rfl, rfl⟩
                have hw : w = ⟨0, Nat.two_pow_pos _⟩ := Fin.ext hw0
                subst hw; right; rw [if_pos h1]; congr 1; exact Fin.ext h2
              · rw [dif_neg hw0] at h; cases h
            · rw [Finset.mem_singleton] at h; cases h
          · rw [if_neg h2] at h; (try split_ifs at h) <;> simp at h
        · rw [if_neg h1] at h; (try split_ifs at h) <;> simp at h
    | _ =>
      simp only [pairOut, pairIn, prevReg, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      (try split_ifs) <;> simp
  | bridge k =>
    cases v with
    | initReg s k' =>
      simp only [pairOut, pairIn, Finset.mem_singleton]
      cases s <;> simp [eq_comm]
    | _ =>
      simp only [pairOut, pairIn, prevReg, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      (try split_ifs) <;> simp
  | regP s w k =>
    cases v with
    | regX s' w' k' => simp [pairOut, pairIn, eq_comm]
    | _ =>
      simp only [pairOut, pairIn, prevReg, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      (try split_ifs) <;> simp
  | regX s w k =>
    cases v with
    | bridge k' =>
      simp only [pairOut, pairIn, Finset.mem_singleton]
      by_cases h1 : w.val + 1 < 2 ^ (t + 1)
      · rw [dif_pos h1]
        constructor
        · rintro h; simp only [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with h | h
          · cases h
          · by_cases h3 : wordOf (t + 1) ⟨w.val + 1, h1⟩ k = true
            · rw [if_pos h3] at h; cases h
            · rw [if_neg h3] at h; cases h
        · intro h; rcases PairV.regX.inj h with ⟨rfl, hw, rfl⟩
          have := congrArg Fin.val hw; dsimp only at this; omega
      · rw [dif_neg h1]
        by_cases h2 : s = false
        · rw [if_pos h2, Finset.mem_singleton]
          constructor
          · intro h; rcases PairV.bridge.inj h with rfl; subst h2
            congr 1; exact Fin.ext (by have := w.isLt; dsimp only; omega)
          · intro h; rcases PairV.regX.inj h with ⟨rfl, _, rfl⟩; rfl
        · rw [if_neg h2]
          simp only [Finset.notMem_empty, false_iff]
          intro h; rcases PairV.regX.inj h with ⟨hs, _, _⟩; exact h2 hs
    | regP s' w' k' =>
      simp only [pairOut, pairIn, prevReg, Finset.mem_singleton]
      by_cases h1 : w.val + 1 < 2 ^ (t + 1)
      · rw [dif_pos h1]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (h | h)
          · rcases PairV.regP.inj h with ⟨rfl, rfl, rfl⟩
            rw [dif_neg (by dsimp only; omega)]; simp
          · by_cases h3 : wordOf (t + 1) ⟨w.val + 1, h1⟩ k = true
            · rw [if_pos h3] at h; cases h
            · rw [if_neg h3] at h; cases h
        · intro h
          by_cases hw0 : w'.val = 0
          · rw [dif_pos hw0] at h; cases h
          · rw [dif_neg hw0] at h
            rcases PairV.regX.inj h with ⟨rfl, hw, rfl⟩
            left; congr 1; apply Fin.ext; have := congrArg Fin.val hw; dsimp only at this ⊢; omega
      · rw [dif_neg h1]
        constructor
        · intro h; (try split_ifs at h) <;> simp at h
        · intro h
          by_cases hw0 : w'.val = 0
          · rw [dif_pos hw0] at h; cases h
          · rw [dif_neg hw0] at h
            rcases PairV.regX.inj h with ⟨rfl, hw, rfl⟩
            have hval := congrArg Fin.val hw; dsimp only at hval; have := w'.isLt; omega
    | detD s' w' k' =>
      simp only [pairOut, pairIn, prevReg]
      constructor
      · intro h
        by_cases h1 : w.val + 1 < 2 ^ (t + 1)
        · rw [dif_pos h1] at h
          simp only [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with h | h
          · cases h
          · by_cases h3 : wordOf (t + 1) ⟨w.val + 1, h1⟩ k = true
            · rw [if_pos h3] at h; cases h
            · rw [if_neg h3] at h
              rcases PairV.detD.inj h with ⟨rfl, rfl, rfl⟩
              rw [Finset.mem_union]; right
              rw [if_pos (Bool.eq_false_iff.mpr h3), dif_neg (by dsimp only; omega), Finset.mem_singleton]
              simp
        · rw [dif_neg h1] at h; (try split_ifs at h) <;> simp at h
      · intro h
        rw [Finset.mem_union] at h
        rcases h with h | h
        · (try split_ifs at h) <;> simp at h
        · by_cases h1 : wordOf (t + 1) w' k' = false
          · rw [if_pos h1] at h
            by_cases h2 : w'.val = 0
            · rw [dif_pos h2, Finset.mem_singleton] at h; cases h
            · rw [dif_neg h2, Finset.mem_singleton] at h
              rcases PairV.regX.inj h with ⟨rfl, hw, rfl⟩
              have hw' : w.val + 1 = w'.val := by have := congrArg Fin.val hw; dsimp only at this; omega
              have hlt : w.val + 1 < 2 ^ (t + 1) := by omega
              rw [dif_pos hlt]; simp only [Finset.mem_insert, Finset.mem_singleton]; right
              have heq : (⟨w.val + 1, hlt⟩ : Fin (2 ^ (t + 1))) = w' := Fin.ext hw'
              rw [heq, if_neg (by rw [h1]; decide)]
          · rw [if_neg h1] at h; simp at h
    | detU s' w' k' c =>
      simp only [pairOut, pairIn, prevReg]
      constructor
      · intro h
        by_cases h1 : w.val + 1 < 2 ^ (t + 1)
        · rw [dif_pos h1] at h
          simp only [Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with h | h
          · cases h
          · by_cases h3 : wordOf (t + 1) ⟨w.val + 1, h1⟩ k = true
            · rw [if_pos h3] at h
              rcases PairV.detU.inj h with ⟨rfl, rfl, rfl, rfl⟩
              rw [if_pos h3, if_pos rfl, dif_neg (by dsimp only; omega), Finset.mem_insert]
              left; simp
            · rw [if_neg h3] at h; cases h
        · rw [dif_neg h1] at h; (try split_ifs at h) <;> simp at h
      · intro h
        by_cases h1 : wordOf (t + 1) w' k' = true
        · rw [if_pos h1] at h
          by_cases h2 : c.val = 0
          · rw [if_pos h2] at h
            rcases Finset.mem_insert.mp h with h | h
            · by_cases hw0 : w'.val = 0
              · rw [dif_pos hw0] at h; cases h
              · rw [dif_neg hw0] at h
                rcases PairV.regX.inj h with ⟨rfl, hw, rfl⟩
                have hw' : w.val + 1 = w'.val := by have := congrArg Fin.val hw; dsimp only at this; omega
                have hlt : w.val + 1 < 2 ^ (t + 1) := by omega
                rw [dif_pos hlt]; simp only [Finset.mem_insert, Finset.mem_singleton]; right
                have heq : (⟨w.val + 1, hlt⟩ : Fin (2 ^ (t + 1))) = w' := Fin.ext hw'
                rw [heq, if_pos h1]; congr 1; exact Fin.ext h2
            · rw [Finset.mem_singleton] at h; cases h
          · rw [if_neg h2] at h; (try split_ifs at h) <;> simp at h
        · rw [if_neg h1] at h; (try split_ifs at h) <;> simp at h
    | _ =>
      simp only [pairOut, pairIn, prevReg, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      (try split_ifs) <;> simp
  | detD s w k =>
    cases v with
    | detQ s' w' k' =>
      simp only [pairOut, pairIn, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · by_cases h1 : k.val < t
          · rw [dif_pos h1, Finset.mem_singleton] at h; rcases PairV.detQ.inj h with ⟨rfl, rfl, rfl⟩; rfl
          · rw [dif_neg h1] at h; simp at h
        · (try split_ifs at h) <;> simp at h
      · intro h; rcases PairV.detD.inj h with ⟨rfl, rfl, rfl⟩
        left; rw [dif_pos (show k'.castSucc.val < t from k'.isLt)]; simp
    | detU s' w' k' c =>
      simp only [pairOut, pairIn, Finset.mem_union]
      constructor
      · rintro (h | h)
        · (try split_ifs at h) <;> simp at h
        · by_cases h1 : wordOf (t + 1) w k = true
          · rw [if_pos h1, Finset.mem_singleton] at h; rcases PairV.detU.inj h with ⟨rfl, rfl, rfl, rfl⟩
            rw [if_pos h1, if_pos rfl]; simp
          · rw [if_neg h1] at h; simp at h
      · intro h
        by_cases h1 : wordOf (t + 1) w' k' = true
        · rw [if_pos h1] at h
          by_cases h2 : c.val = 0
          · rw [if_pos h2] at h
            rcases Finset.mem_insert.mp h with h | h
            · unfold prevReg at h; (try split_ifs at h) <;> cases h
            · rw [Finset.mem_singleton] at h; rcases PairV.detD.inj h with ⟨rfl, rfl, rfl⟩
              right; rw [if_pos h1, Finset.mem_singleton]; congr 1; exact Fin.ext h2
          · rw [if_neg h2] at h; (try split_ifs at h) <;> simp at h
        · rw [if_neg h1] at h; (try split_ifs at h) <;> simp at h
    | _ =>
      simp only [pairOut, pairIn, prevReg, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      (try split_ifs) <;> simp
  | detQ s w k =>
    cases v with
    | detD s' w' k' =>
      simp only [pairOut, pairIn, Finset.mem_union, Finset.mem_singleton]
      constructor
      · intro h; rcases PairV.detD.inj h with ⟨rfl, rfl, rfl⟩
        left; rw [dif_pos (show 0 < k.succ.val by simp), Finset.mem_singleton]; simp
      · rintro (h | h)
        · by_cases h1 : 0 < k'.val
          · rw [dif_pos h1, Finset.mem_singleton] at h; rcases PairV.detQ.inj h with ⟨rfl, rfl, rfl⟩
            congr 1; apply Fin.ext; simp [Fin.val_succ]; omega
          · rw [dif_neg h1] at h; simp at h
        · by_cases h1 : wordOf (t + 1) w' k' = false
          · rw [if_pos h1, Finset.mem_singleton] at h; unfold prevReg at h; (try split_ifs at h) <;> cases h
          · rw [if_neg h1] at h; simp at h
    | _ =>
      simp only [pairOut, pairIn, prevReg, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      (try split_ifs) <;> simp
  | detU s w k c =>
    cases v with
    | detU s' w' k' c' =>
      by_cases heq : s = s' ∧ w = w' ∧ k = k'
      · rcases heq with ⟨rfl, rfl, rfl⟩
        simp only [pairOut, pairIn, prevReg]
        cases hwk : wordOf (t + 1) w k <;> fin_cases c <;> fin_cases c' <;> simp [hwk] <;> (try split_ifs) <;> simp
      · have hL : PairV.detU s' w' k' c' ∉ pairOut (PairV.detU s w k c) := by
          simp only [pairOut]; split_ifs <;> simp only [Finset.notMem_empty, Finset.mem_insert, Finset.mem_singleton, PairV.detU.injEq, not_false_eq_true, not_or]
          · exact ⟨fun h => heq ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm⟩, fun h => heq ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm⟩⟩
          · exact fun h => heq ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm⟩
          · exact fun h => heq ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm⟩
        have hR : PairV.detU s w k c ∉ pairIn (PairV.detU s' w' k' c') := by
          simp only [pairIn, prevReg]; split_ifs <;> simp only [Finset.notMem_empty, Finset.mem_insert, Finset.mem_singleton, PairV.detU.injEq, reduceCtorEq, not_false_eq_true, not_or]
          · exact ⟨trivial, trivial⟩
          · exact ⟨trivial, trivial⟩
          · exact fun h => heq ⟨h.1, h.2.1, h.2.2.1⟩
          · exact fun h => heq ⟨h.1, h.2.1, h.2.2.1⟩
          · exact fun h => heq ⟨h.1, h.2.1, h.2.2.1⟩
        exact iff_of_false hL hR
    | _ =>
      simp only [pairOut, pairIn, prevReg, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      (try split_ifs) <;> simp
  | detF s w c =>
    cases v with
    | detF s' w' c' =>
      by_cases heq : s = s' ∧ w = w'
      · rcases heq with ⟨rfl, rfl⟩; simp only [pairOut, pairIn]; fin_cases c <;> fin_cases c' <;> simp
      · have hL : PairV.detF s' w' c' ∉ pairOut (PairV.detF s w c) := by
          simp only [pairOut]; split_ifs <;> simp only [Finset.notMem_empty, Finset.mem_insert, Finset.mem_singleton, PairV.detF.injEq, not_false_eq_true, not_or]
          exact ⟨fun h => heq ⟨h.1.symm, h.2.1.symm⟩, fun h => heq ⟨h.1.symm, h.2.1.symm⟩⟩
        have hR : PairV.detF s w c ∉ pairIn (PairV.detF s' w' c') := by
          simp only [pairIn]; split_ifs <;> simp only [Finset.notMem_empty, Finset.mem_insert, Finset.mem_singleton, PairV.detF.injEq, not_false_eq_true]
          exact fun h => heq ⟨h.1, h.2.1⟩
        exact iff_of_false hL hR
    | _ =>
      simp only [pairOut, pairIn, prevReg, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      (try split_ifs) <;> simp
  | padT s w j b =>
    cases v with
    | padT s' w' j' b' =>
      simp only [pairOut, pairIn]
      cases b <;> cases b' <;> simp [eq_comm]
    | _ =>
      simp only [pairOut, pairIn, prevReg, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      (try split_ifs) <;> simp

private lemma pairArc_irrefl {t : ℕ} (u : PairV t) : pairArc u u = false := by
  unfold pairArc; rw [decide_eq_false_iff_not]
  cases u with
  | initReg s k => simp only [pairOut, Finset.mem_insert, Finset.mem_singleton]; split_ifs <;> simp
  | bridge k => simp [pairOut]
  | regP s w k => simp [pairOut]
  | regX s w k => simp only [pairOut]; split_ifs <;> simp
  | detD s w k => simp only [pairOut, Finset.mem_union]; split_ifs <;> simp
  | detQ s w k => simp [pairOut]
  | detU s w k c => simp only [pairOut]; split_ifs <;> simp <;> fin_cases c <;> simp at *
  | detF s w c => simp only [pairOut]; split_ifs <;> simp <;> fin_cases c <;> simp at *
  | padT s w j b => cases b <;> simp [pairOut]

private lemma pairArc_out_le {t : ℕ} (u : PairV t) :
    (Finset.univ.filter (fun v => pairArc u v = true)).card ≤ 2 := by
  have heq : Finset.univ.filter (fun v => pairArc u v = true) = pairOut u := by
    ext v; simp [pairArc]
  rw [heq]
  cases u with
  | initReg s k => exact (Finset.card_insert_le _ _).trans (by simp)
  | bridge k => simp [pairOut]
  | regP s w k => simp [pairOut]
  | regX s w k =>
    simp only [pairOut]; split_ifs <;> first | exact (Finset.card_insert_le _ _).trans (by simp) | simp
  | detD s w k =>
    simp only [pairOut]
    refine (Finset.card_union_le _ _).trans ?_
    have h1 : (if h : k.val < t then ({PairV.detQ s w ⟨k.val, h⟩} : Finset (PairV t)) else ∅).card ≤ 1 := by split_ifs <;> simp
    have h2 : (if wordOf (t + 1) w k = true then ({PairV.detU s w k ⟨0, by decide⟩} : Finset (PairV t)) else ∅).card ≤ 1 := by split_ifs <;> simp
    omega
  | detQ s w k => simp [pairOut]
  | detU s w k c =>
    simp only [pairOut]; split_ifs
    · exact (Finset.card_insert_le _ _).trans (by simp)
    · simp
    · simp
    · simp
    · simp
  | detF s w c =>
    simp only [pairOut]; split_ifs
    · exact (Finset.card_insert_le _ _).trans (by simp)
    · simp
  | padT s w j b => simp only [pairOut]; split_ifs <;> simp

private lemma pairArc_in_le {t : ℕ} (v : PairV t) :
    (Finset.univ.filter (fun u => pairArc u v = true)).card ≤ 2 := by
  have heq : Finset.univ.filter (fun u => pairArc u v = true) = pairIn v := by
    ext u; simp [pairArc, pairArc_iff_in]
  rw [heq]
  cases v with
  | initReg s k => simp only [pairIn]; split_ifs <;> simp
  | bridge k => simp [pairIn]
  | regP s w k => simp [pairIn]
  | regX s w k => simp [pairIn]
  | detD s w k =>
    simp only [pairIn]
    refine (Finset.card_union_le _ _).trans ?_
    have h1 : (if h : 0 < k.val then ({PairV.detQ s w ⟨k.val - 1, by omega⟩} : Finset (PairV t)) else ∅).card ≤ 1 := by split_ifs <;> simp
    have h2 : (if wordOf (t + 1) w k = false then ({prevReg s w k} : Finset (PairV t)) else ∅).card ≤ 1 := by split_ifs <;> simp
    omega
  | detQ s w k => simp [pairIn]
  | detU s w k c =>
    simp only [pairIn]; split_ifs
    · exact (Finset.card_insert_le _ _).trans (by simp)
    · simp
    · simp
    · simp
    · simp
    · simp
  | detF s w c => simp only [pairIn]; split_ifs <;> simp
  | padT s w j b => simp only [pairIn]; split_ifs <;> simp

private lemma pairArc_cross_iff {t : ℕ} (u v : PairV t) :
    pairArc u v = true ∧ pairSide u ≠ pairSide v ↔
    ∃ k : Fin (t + 1), u = .bridge k ∧ v = .initReg true k := by
  unfold pairArc; simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨huv, hne⟩
    cases u with
    | bridge k =>
      simp only [pairOut, Finset.mem_singleton] at huv; exact ⟨k, rfl, huv⟩
    | initReg s k =>
      simp only [pairOut, Finset.mem_insert, Finset.mem_singleton] at huv
      rcases huv with rfl | huv
      · simp [pairSide] at hne
      · split_ifs at huv <;> (subst huv; simp [pairSide] at hne)
    | regP s w k => simp only [pairOut, Finset.mem_singleton] at huv; subst huv; simp [pairSide] at hne
    | regX s w k =>
      simp only [pairOut] at huv
      by_cases h1 : w.val + 1 < 2 ^ (t + 1)
      · rw [dif_pos h1] at huv; simp only [Finset.mem_insert, Finset.mem_singleton] at huv
        rcases huv with rfl | huv
        · simp [pairSide] at hne
        · split_ifs at huv <;> (subst huv; simp [pairSide] at hne)
      · rw [dif_neg h1] at huv
        by_cases h2 : s = false
        · rw [if_pos h2, Finset.mem_singleton] at huv; subst huv; subst h2; simp [pairSide] at hne
        · rw [if_neg h2] at huv; simp at huv
    | detD s w k =>
      simp only [pairOut, Finset.mem_union] at huv
      rcases huv with h | h <;> (split_ifs at h <;> simp at h; subst h; simp [pairSide] at hne)
    | detQ s w k => simp only [pairOut, Finset.mem_singleton] at huv; subst huv; simp [pairSide] at hne
    | detU s w k c =>
      simp only [pairOut] at huv; split_ifs at huv <;> simp at huv
      · rcases huv with rfl | rfl <;> simp [pairSide] at hne
      · subst huv; simp [pairSide] at hne
      · subst huv; simp [pairSide] at hne
    | detF s w c =>
      simp only [pairOut] at huv; split_ifs at huv <;> simp at huv
      rcases huv with rfl | rfl <;> simp [pairSide] at hne
    | padT s w j b =>
      simp only [pairOut] at huv; split_ifs at huv <;> simp at huv
      subst huv; simp [pairSide] at hne
  · rintro ⟨k, rfl, rfl⟩; simp [pairOut, pairSide]

private def Bw (t : ℕ) : ℕ := 4 * (t + 1) + 2
private def M0 (t : ℕ) : ℕ := (t + 1) + 2 ^ (t + 1) * Bw t
private def R0 (t : ℕ) : ℕ := M0 t + (t + 1)
private def Ltot (t : ℕ) : ℕ := R0 t + 2 ^ (t + 1) * Bw t
private def Tstep (t : ℕ) (s : Bool) (w : ℕ) (k : ℕ) : ℕ :=
  (if s then R0 t else (t + 1)) + w * Bw t + k

private def bagLo {t : ℕ} : PairV t × Bool → ℕ
  | (.initReg false k, _) => k.val
  | (.initReg true k, _) => M0 t + k.val
  | (.bridge k, _) => M0 t + k.val
  | (.regP s w k, _) => Tstep t s w.val k.val
  | (.regX s w k, _) => Tstep t s w.val k.val
  | (.detD s w k, _) => Tstep t s w.val k.val
  | (.detQ s w k, _) => Tstep t s w.val (k.val + 1)
  | (.detU s w k _, _) => Tstep t s w.val k.val
  | (.detF s w _, _) => Tstep t s w.val (t + 1)
  | (.padT s w j _, _) => Tstep t s w.val ((t + 1) + 1 + j.val)

private def bagHi {t : ℕ} : PairV t × Bool → ℕ
  | (.initReg false k, false) => k.val
  | (.initReg false k, true) => Tstep t false 0 k.val
  | (.initReg true k, false) => M0 t + k.val
  | (.initReg true k, true) => Tstep t true 0 k.val
  | (.bridge k, _) => M0 t + k.val
  | (.regP s w k, _) => Tstep t s w.val k.val
  | (.regX s w k, false) => Tstep t s w.val k.val
  | (.regX s w k, true) =>
    if w.val + 1 < 2 ^ (t + 1) then Tstep t s (w.val + 1) k.val
    else if s = false then M0 t + k.val else Tstep t true w.val k.val
  | (.detD s w k, _) => if k.val + 1 < t + 1 then Tstep t s w.val (k.val + 1) else Tstep t s w.val k.val
  | (.detQ s w k, _) => Tstep t s w.val (k.val + 1)
  | (.detU s w k _, _) => Tstep t s w.val k.val
  | (.detF s w _, _) => Tstep t s w.val (t + 1)
  | (.padT s w j _, _) => Tstep t s w.val ((t + 1) + 1 + j.val)

private lemma bagLo_le_hi {t : ℕ} (v : PairV t × Bool) : bagLo v ≤ bagHi v := by
  rcases v with ⟨u, b⟩
  cases u with
  | initReg s k => cases s <;> cases b <;> simp only [bagLo, bagHi, Tstep, M0, R0, Bw, Bool.false_eq_true, ↓reduceIte] <;> omega
  | bridge k => simp [bagLo, bagHi]
  | regP s w k => simp [bagLo, bagHi]
  | regX s w k =>
    cases b
    · simp [bagLo, bagHi]
    · simp only [bagLo, bagHi]; split_ifs with h1 h2
      · simp only [Tstep, Bw]; nlinarith
      · simp only [Tstep, M0, h2, Bool.false_eq_true, ↓reduceIte]
        have hle : (w.val + 1) * Bw t ≤ 2 ^ (t + 1) * Bw t := Nat.mul_le_mul_right _ w.isLt
        have hmul : w.val * Bw t + Bw t = (w.val + 1) * Bw t := by ring
        unfold Bw at *; omega
      · have hs : s = true := Bool.eq_true_of_not_eq_false h2; subst hs; exact le_rfl
  | detD s w k => simp only [bagLo, bagHi, Tstep]; split_ifs <;> omega
  | detQ s w k => simp [bagLo, bagHi]
  | detU s w k c => simp [bagLo, bagHi]
  | detF s w c => simp [bagLo, bagHi]
  | padT s w j c => simp [bagLo, bagHi]

private lemma bagHi_lt {t : ℕ} (v : PairV t × Bool) : bagHi v < Ltot t := by
  have hpow : 1 ≤ 2 ^ (t + 1) := Nat.one_le_pow _ _ (by decide)
  have hstep_lt : ∀ (s : Bool) (w s0 : ℕ), w < 2 ^ (t + 1) → s0 < Bw t → Tstep t s w s0 < Ltot t := by
    intro s w s0 hw hs0
    unfold Tstep Ltot R0 M0
    have h1 : (w + 1) * Bw t ≤ 2 ^ (t + 1) * Bw t := Nat.mul_le_mul_right _ hw
    have h2 : w * Bw t + Bw t = (w + 1) * Bw t := by ring
    cases s <;> simp <;> omega
  rcases v with ⟨u, b⟩
  cases u with
  | initReg s k =>
    have hk := k.isLt
    cases s <;> cases b
    · simp only [bagHi, Ltot, R0, M0]; omega
    · exact hstep_lt false 0 k.val (by omega) (by unfold Bw; omega)
    · simp only [bagHi, Ltot, R0, M0, Bw]; nlinarith
    · exact hstep_lt true 0 k.val (by omega) (by unfold Bw; omega)
  | bridge k => have hk := k.isLt; simp only [bagHi, Ltot, R0, M0, Bw]; nlinarith
  | regP s w k => exact hstep_lt s w.val k.val w.isLt (by unfold Bw; omega)
  | regX s w k =>
    cases b
    · exact hstep_lt s w.val k.val w.isLt (by unfold Bw; omega)
    · simp only [bagHi]; split_ifs with h1 h2
      · exact hstep_lt s (w.val + 1) k.val h1 (by unfold Bw; omega)
      · have hk := k.isLt; simp only [Ltot, R0, M0, Bw]; nlinarith
      · exact hstep_lt true w.val k.val w.isLt (by unfold Bw; omega)
  | detD s w k =>
    simp only [bagHi]; split_ifs with h1
    · exact hstep_lt s w.val (k.val + 1) w.isLt (by unfold Bw; omega)
    · exact hstep_lt s w.val k.val w.isLt (by unfold Bw; omega)
  | detQ s w k => exact hstep_lt s w.val (k.val + 1) w.isLt (by unfold Bw; omega)
  | detU s w k c => exact hstep_lt s w.val k.val w.isLt (by unfold Bw; omega)
  | detF s w c => exact hstep_lt s w.val (t + 1) w.isLt (by unfold Bw; omega)
  | padT s w j c => exact hstep_lt s w.val ((t + 1) + 1 + j.val) w.isLt (by unfold Bw; omega)

private lemma pairArc_interval_meet {t : ℕ} (u v : PairV t) (h : v ∈ pairOut u) :
    bagLo (u, true) ≤ bagHi (v, false) ∧ bagLo (v, false) ≤ bagHi (u, true) := by
  have h1 : ∀ a b : PairV t × Bool, bagLo a ≤ bagHi a → bagLo b = bagHi a →
      bagLo a ≤ bagHi b ∧ bagLo b ≤ bagHi a := fun a b hle heq =>
    ⟨hle.trans (heq.symm.trans_le (bagLo_le_hi b)), heq.le⟩
  cases u with
  | initReg s k =>
    simp only [pairOut, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | h
    · exact h1 _ _ (bagLo_le_hi _) (by cases s <;> rfl)
    · split_ifs at h <;> (subst h; exact h1 _ _ (bagLo_le_hi _) (by cases s <;> rfl))
  | bridge k =>
    simp only [pairOut, Finset.mem_singleton] at h; subst h; simp [bagLo, bagHi]
  | regP s w k =>
    simp only [pairOut, Finset.mem_singleton] at h; subst h; simp [bagLo, bagHi]
  | regX s w k =>
    simp only [pairOut] at h
    by_cases h1' : w.val + 1 < 2 ^ (t + 1)
    · rw [dif_pos h1'] at h; simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | h
      · exact h1 _ _ (bagLo_le_hi _) (by simp [bagLo, bagHi, h1'])
      · split_ifs at h <;> (subst h; exact h1 _ _ (bagLo_le_hi _) (by simp [bagLo, bagHi, h1']))
    · rw [dif_neg h1'] at h
      by_cases h2' : s = false
      · rw [if_pos h2', Finset.mem_singleton] at h; subst h
        exact h1 _ _ (bagLo_le_hi _) (by simp [bagLo, bagHi, h1', h2'])
      · rw [if_neg h2'] at h; simp at h
  | detD s w k =>
    simp only [pairOut, Finset.mem_union] at h
    rcases h with h | h
    · split_ifs at h with hk
      · rw [Finset.mem_singleton] at h; subst h
        have hlt : k.val + 1 < t + 1 := by omega
        simp [bagLo, bagHi, hlt, Tstep]
      · simp at h
    · split_ifs at h with hw
      · rw [Finset.mem_singleton] at h; subst h
        simp only [bagLo, bagHi, Tstep]; split_ifs <;> omega
      · simp at h
  | detQ s w k =>
    simp only [pairOut, Finset.mem_singleton] at h; subst h
    simp only [bagLo, bagHi, Tstep, Fin.val_succ]; split_ifs <;> omega
  | detU s w k c =>
    simp only [pairOut] at h; split_ifs at h <;> simp at h
    · rcases h with rfl | rfl <;> simp [bagLo, bagHi]
    · subst h; simp [bagLo, bagHi]
    · subst h; simp [bagLo, bagHi]
  | detF s w c =>
    simp only [pairOut] at h; split_ifs at h <;> simp at h
    rcases h with rfl | rfl <;> simp [bagLo, bagHi]
  | padT s w j b =>
    simp only [pairOut] at h; split_ifs at h <;> simp at h
    subst h; simp [bagLo, bagHi]

set_option maxHeartbeats 600000 in
private lemma pairBag_card_le {t : ℕ} (τ : ℕ) (hτ : τ < Ltot t) :
    ((Finset.univ : Finset (PairV t × Bool)).filter (fun v => bagLo v ≤ τ ∧ τ ≤ bagHi v)).card ≤ (t + 1) + 37 := by
  let B := (Finset.univ : Finset (PairV t × Bool)).filter (fun v => bagLo v ≤ τ ∧ τ ≤ bagHi v)
  let isTip : PairV t × Bool → Bool := fun
    | (.initReg _ _, true) => true
    | (.regX _ _ _, true) => true
    | _ => false
  let tipK : PairV t × Bool → Fin (t + 1) → Bool := fun v k =>
    match v with
    | (.initReg _ k', true) => decide (k' = k)
    | (.regX _ _ k', true) => decide (k' = k)
    | _ => false
  have hsplit : B.card = (B.filter (fun v => isTip v = true)).card + (B.filter (fun v => isTip v = false)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext v; simp only [Finset.mem_union, Finset.mem_filter]; cases isTip v <;> simp
    · rw [Finset.disjoint_left]; intro v h1 h2
      have a := (Finset.mem_filter.mp h1).2; have b := (Finset.mem_filter.mp h2).2; rw [a] at b; simp at b
  have htip_k : ∀ k : Fin (t + 1), (B.filter (fun v => tipK v k = true)).card ≤ 2 := by
    intro k
    let activeK := B.filter (fun v => tipK v k = true)
    let tipIdx : PairV t × Bool → ℕ := fun
      | (.initReg false _, true) => 0
      | (.regX false w _, true) => w.val + 1
      | (.initReg true _, true) => 2 ^ (t + 1) + 1
      | (.regX true w _, true) => 2 ^ (t + 1) + 2 + w.val
      | _ => 0
    have hlt_ord : ∀ u ∈ activeK, ∀ v ∈ activeK, tipIdx u + 2 ≤ tipIdx v → False := by
      intro u hu v hv hgap
      have huB := (Finset.mem_filter.mp hu).1
      have hvB := (Finset.mem_filter.mp hv).1
      have huK := (Finset.mem_filter.mp hu).2
      have hvK := (Finset.mem_filter.mp hv).2
      have hulo := (Finset.mem_filter.mp huB).2.1
      have huhi := (Finset.mem_filter.mp huB).2.2
      have hvlo := (Finset.mem_filter.mp hvB).2.1
      have hvhi := (Finset.mem_filter.mp hvB).2.2
      have hstrict : bagHi u < bagLo v := by
        rcases u with ⟨u1, bu⟩; rcases v with ⟨v1, bv⟩
        cases u1 with
        | initReg su ku =>
          cases bu
          · simp [tipK] at huK
          · simp only [tipK, decide_eq_true_eq] at huK; subst huK
            cases v1 with
            | initReg sv kv =>
              cases bv
              · simp [tipK] at hvK
              · simp only [tipK, decide_eq_true_eq] at hvK; subst hvK
                cases su <;> cases sv <;> simp [tipIdx] at hgap
                simp only [bagHi, bagLo, Tstep, M0, R0, Bw, Bool.false_eq_true, ↓reduceIte]
                have hpow : 1 ≤ 2 ^ (t + 1) := Nat.one_le_pow _ _ (by decide)
                have hk := kv.isLt; nlinarith
            | regX sv wv kv =>
              cases bv
              · simp [tipK] at hvK
              · simp only [tipK, decide_eq_true_eq] at hvK; subst hvK
                cases su <;> cases sv <;> simp [tipIdx] at hgap
                · simp only [bagHi, bagLo, Tstep, Bool.false_eq_true, ↓reduceIte]
                  have h1 : 1 * Bw t ≤ wv.val * Bw t := Nat.mul_le_mul_right _ (by omega)
                  unfold Bw at *; omega
                · simp only [bagHi, bagLo, Tstep, R0, M0, Bw, Bool.false_eq_true, ↓reduceIte]
                  have hpow : 1 ≤ 2 ^ (t + 1) := Nat.one_le_pow _ _ (by decide)
                  have hk := kv.isLt; nlinarith
                · have := wv.isLt; omega
                · simp only [bagHi, bagLo, Tstep, ↓reduceIte]
                  have h1 : 1 * Bw t ≤ wv.val * Bw t := Nat.mul_le_mul_right _ (by omega)
                  unfold Bw at *; omega
            | _ => simp [tipK] at hvK
        | regX su wu ku =>
          cases bu
          · simp [tipK] at huK
          · simp only [tipK, decide_eq_true_eq] at huK; subst huK
            cases v1 with
            | initReg sv kv =>
              cases bv
              · simp [tipK] at hvK
              · simp only [tipK, decide_eq_true_eq] at hvK; subst hvK
                cases su <;> cases sv <;> simp [tipIdx] at hgap
                · simp only [bagHi, bagLo]
                  have hw1 : wu.val + 1 < 2 ^ (t + 1) := by omega
                  rw [if_pos hw1]; simp only [Tstep, M0, Bool.false_eq_true, ↓reduceIte]
                  have h1 : (wu.val + 2) * Bw t ≤ 2 ^ (t + 1) * Bw t := Nat.mul_le_mul_right _ (by omega)
                  have h2 : (wu.val + 1) * Bw t + Bw t = (wu.val + 2) * Bw t := by ring
                  have hk := kv.isLt; unfold Bw at *; omega
                · omega
            | regX sv wv kv =>
              cases bv
              · simp [tipK] at hvK
              · simp only [tipK, decide_eq_true_eq] at hvK; subst hvK
                cases su <;> cases sv <;> simp [tipIdx] at hgap
                · simp only [bagHi, bagLo]
                  have hw1 : wu.val + 1 < 2 ^ (t + 1) := by omega
                  rw [if_pos hw1]; simp only [Tstep, Bool.false_eq_true, ↓reduceIte]
                  have h1 : (wu.val + 2) * Bw t ≤ wv.val * Bw t := Nat.mul_le_mul_right _ (by omega)
                  have h2 : (wu.val + 1) * Bw t + Bw t = (wu.val + 2) * Bw t := by ring
                  unfold Bw at *; omega
                · simp only [bagHi, bagLo]; by_cases hw1 : wu.val + 1 < 2 ^ (t + 1)
                  · rw [if_pos hw1]; simp only [Tstep, R0, M0, Bool.false_eq_true, ↓reduceIte]
                    have h1 : (wu.val + 2) * Bw t ≤ 2 ^ (t + 1) * Bw t := Nat.mul_le_mul_right _ (by omega)
                    have h2 : (wu.val + 1) * Bw t + Bw t = (wu.val + 2) * Bw t := by ring
                    have hk := kv.isLt; unfold Bw at *; omega
                  · rw [if_neg hw1]; simp only [Tstep, R0, M0, Bw, ↓reduceIte]
                    have hk := kv.isLt; omega
                · have := wv.isLt; omega
                · simp only [bagHi, bagLo]
                  have hw1 : wu.val + 1 < 2 ^ (t + 1) := by omega
                  rw [if_pos hw1]; simp only [Tstep, ↓reduceIte]
                  have h1 : (wu.val + 2) * Bw t ≤ wv.val * Bw t := Nat.mul_le_mul_right _ (by omega)
                  have h2 : (wu.val + 1) * Bw t + Bw t = (wu.val + 2) * Bw t := by ring
                  unfold Bw at *; omega
            | _ => simp [tipK] at hvK
        | _ => simp [tipK] at huK
      omega
    have hinj : ∀ u ∈ activeK, ∀ v ∈ activeK, tipIdx u = tipIdx v → u = v := by
      intro u hu v hv heq
      have huK := (Finset.mem_filter.mp hu).2; have hvK := (Finset.mem_filter.mp hv).2
      rcases u with ⟨u1, bu⟩; rcases v with ⟨v1, bv⟩
      cases u1 with
      | initReg su ku =>
        cases bu
        · simp [tipK] at huK
        · simp only [tipK, decide_eq_true_eq] at huK; subst huK
          cases v1 with
          | initReg sv kv =>
            cases bv
            · simp [tipK] at hvK
            · simp only [tipK, decide_eq_true_eq] at hvK; subst hvK
              cases su <;> cases sv <;> simp [tipIdx] at heq; rfl; rfl
          | regX sv wv kv =>
            cases bv
            · simp [tipK] at hvK
            · simp only [tipK, decide_eq_true_eq] at hvK; subst hvK
              cases su <;> cases sv <;> simp [tipIdx] at heq <;> omega
          | _ => simp [tipK] at hvK
      | regX su wu ku =>
        cases bu
        · simp [tipK] at huK
        · simp only [tipK, decide_eq_true_eq] at huK; subst huK
          cases v1 with
          | initReg sv kv =>
            cases bv
            · simp [tipK] at hvK
            · simp only [tipK, decide_eq_true_eq] at hvK; subst hvK
              cases su <;> cases sv <;> simp [tipIdx] at heq <;> omega
          | regX sv wv kv =>
            cases bv
            · simp [tipK] at hvK
            · simp only [tipK, decide_eq_true_eq] at hvK; subst hvK
              cases su <;> cases sv <;> simp [tipIdx] at heq
              · congr 1; congr 1; exact Fin.ext heq
              · omega
              · omega
              · congr 1; congr 1; exact Fin.ext heq
          | _ => simp [tipK] at hvK
      | _ => simp [tipK] at huK
    change activeK.card ≤ 2
    by_cases hemp : activeK = ∅
    · rw [hemp]; simp
    · have hne : activeK.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
      let imgs := activeK.image tipIdx
      have hne_i : imgs.Nonempty := hne.image _
      let mn := imgs.min' hne_i
      have hsub : imgs ⊆ {mn, mn + 1} := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
        rcases Finset.mem_image.mp (Finset.min'_mem imgs hne_i) with ⟨u, hu, humn⟩
        have hle : mn ≤ tipIdx v := Finset.min'_le imgs _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
        have hlt2 : ¬ mn + 2 ≤ tipIdx v := fun h => hlt_ord u hu v hv (by omega)
        simp only [Finset.mem_insert, Finset.mem_singleton]; omega
      calc activeK.card = imgs.card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ ({mn, mn + 1} : Finset ℕ).card := Finset.card_le_card hsub
        _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  have htip_tight : (B.filter (fun v => isTip v = true)).card ≤ (t + 1) + 1 := by
    have hpair_ge2 : ∀ k1 k2 : Fin (t + 1), k1 ≠ k2 →
        ¬ (2 ≤ (B.filter (fun v => tipK v k1 = true)).card ∧
           2 ≤ (B.filter (fun v => tipK v k2 = true)).card) := by
      intro k1 k2 hne ⟨h1, h2⟩
      have hmod : ∀ k : Fin (t + 1),
          2 ≤ (B.filter (fun v => tipK v k = true)).card →
          ∃ u v, u ≠ v ∧ u ∈ B ∧ v ∈ B ∧ tipK u k = true ∧ tipK v k = true := by
        intro k hk
        rcases Finset.one_lt_card.mp (by omega : 1 < (B.filter (fun v => tipK v k = true)).card) with ⟨u, hu, v, hv, huv⟩
        exact ⟨u, v, huv, (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hv).1,
          (Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp hv).2⟩
      have hτ_mod : ∀ k : Fin (t + 1),
          2 ≤ (B.filter (fun v => tipK v k = true)).card →
          (τ < M0 t ∧ (τ - (t + 1)) % Bw t = k.val ∧ (t + 1) ≤ τ) ∨
          (M0 t ≤ τ ∧ τ < R0 t ∧ τ - M0 t = k.val) ∨
          (R0 t ≤ τ ∧ (τ - R0 t) % Bw t = k.val) := by
        intro k hk
        rcases hmod k hk with ⟨⟨u1, bu⟩, ⟨v1, bv⟩, huv, huB, hvB, huK, hvK⟩
        have hulo := (Finset.mem_filter.mp huB).2.1; have huhi := (Finset.mem_filter.mp huB).2.2
        have hvlo := (Finset.mem_filter.mp hvB).2.1; have hvhi := (Finset.mem_filter.mp hvB).2.2
        have hcommon : ∀ (a b : PairV t × Bool),
            bagLo a ≤ τ → τ ≤ bagHi a → bagLo b ≤ τ → τ ≤ bagHi b →
            tipK a k = true → tipK b k = true → a ≠ b →
            (∃ w, τ = Tstep t false w k.val ∧ w < 2 ^ (t + 1)) ∨ τ = M0 t + k.val ∨
            (∃ w, τ = Tstep t true w k.val ∧ w < 2 ^ (t + 1)) := by
          intro ⟨a1, ba⟩ ⟨b1, bb⟩ hal hah hbl hbh haK hbK hab
          have hpow : 1 ≤ 2 ^ (t + 1) := Nat.one_le_pow _ _ (by decide)
          cases a1 with
          | initReg sa ka =>
            cases ba
            · simp [tipK] at haK
            · simp only [tipK, decide_eq_true_eq] at haK; subst haK
              cases b1 with
              | initReg sb kb =>
                cases bb
                · simp [tipK] at hbK
                · simp only [tipK, decide_eq_true_eq] at hbK; subst hbK
                  cases sa <;> cases sb
                  · exact absurd rfl hab
                  · simp only [bagHi, bagLo, Tstep, M0, Bw, Bool.false_eq_true, ↓reduceIte] at hah hbl; have := kb.isLt; nlinarith
                  · simp only [bagHi, bagLo, Tstep, M0, Bw, Bool.false_eq_true, ↓reduceIte] at hbh hal; have := kb.isLt; nlinarith
                  · exact absurd rfl hab
              | regX sb wb kb =>
                cases bb
                · simp [tipK] at hbK
                · simp only [tipK, decide_eq_true_eq] at hbK; subst hbK
                  cases sa <;> cases sb
                  · simp only [bagHi, bagLo, Tstep, Bool.false_eq_true, ↓reduceIte] at hah hbl
                    have hwb : wb.val = 0 := by
                      by_contra hne0
                      have : 1 * Bw t ≤ wb.val * Bw t := Nat.mul_le_mul_right _ (by omega)
                      unfold Bw at *; omega
                    rw [hwb, zero_mul, add_zero] at hbl
                    left; exact ⟨0, by unfold Tstep; simp; omega, Nat.two_pow_pos _⟩
                  · simp only [bagHi, bagLo, Tstep, R0, M0, Bw, Bool.false_eq_true, ↓reduceIte] at hah hbl; have := kb.isLt; nlinarith
                  · simp only [bagHi, bagLo] at hbh hal
                    by_cases hlast : wb.val + 1 < 2 ^ (t + 1)
                    · rw [if_pos hlast] at hbh; simp only [Tstep, R0, M0, Bool.false_eq_true, ↓reduceIte] at hbh hal
                      have hle : (wb.val + 2) * Bw t ≤ 2 ^ (t + 1) * Bw t := Nat.mul_le_mul_right _ (by omega)
                      have hmul : (wb.val + 1) * Bw t + Bw t = (wb.val + 2) * Bw t := by ring
                      have := kb.isLt; unfold Bw at *; omega
                    · rw [if_neg hlast] at hbh; simp only [↓reduceIte] at hbh; right; left; omega
                  · simp only [bagHi, bagLo, Tstep, ↓reduceIte] at hah hbl
                    have hwb : wb.val = 0 := by
                      by_contra hne0
                      have : 1 * Bw t ≤ wb.val * Bw t := Nat.mul_le_mul_right _ (by omega)
                      unfold Bw at *; omega
                    rw [hwb, zero_mul, add_zero] at hbl
                    right; right; exact ⟨0, by unfold Tstep; simp; omega, Nat.two_pow_pos _⟩
              | _ => simp [tipK] at hbK
          | regX sa wa ka =>
            cases ba
            · simp [tipK] at haK
            · simp only [tipK, decide_eq_true_eq] at haK; subst haK
              cases b1 with
              | initReg sb kb =>
                cases bb
                · simp [tipK] at hbK
                · simp only [tipK, decide_eq_true_eq] at hbK; subst hbK
                  cases sa <;> cases sb
                  · simp only [bagHi, bagLo, Tstep, Bool.false_eq_true, ↓reduceIte] at hbh hal
                    have hwa : wa.val = 0 := by
                      by_contra hne0
                      have : 1 * Bw t ≤ wa.val * Bw t := Nat.mul_le_mul_right _ (by omega)
                      unfold Bw at *; omega
                    rw [hwa, zero_mul, add_zero] at hal
                    left; exact ⟨0, by unfold Tstep; simp; omega, Nat.two_pow_pos _⟩
                  · simp only [bagHi, bagLo] at hah hbl
                    by_cases hlast : wa.val + 1 < 2 ^ (t + 1)
                    · rw [if_pos hlast] at hah; simp only [Tstep, M0, Bool.false_eq_true, ↓reduceIte] at hah hbl
                      have hle : (wa.val + 2) * Bw t ≤ 2 ^ (t + 1) * Bw t := Nat.mul_le_mul_right _ (by omega)
                      have hmul : (wa.val + 1) * Bw t + Bw t = (wa.val + 2) * Bw t := by ring
                      have := kb.isLt; unfold Bw at *; omega
                    · rw [if_neg hlast] at hah; simp only [↓reduceIte] at hah; right; left; omega
                  · simp only [bagHi, bagLo, Tstep, R0, M0, Bw, Bool.false_eq_true, ↓reduceIte] at hbh hal; have := kb.isLt; nlinarith
                  · simp only [bagHi, bagLo, Tstep, ↓reduceIte] at hbh hal
                    have hwa : wa.val = 0 := by
                      by_contra hne0
                      have : 1 * Bw t ≤ wa.val * Bw t := Nat.mul_le_mul_right _ (by omega)
                      unfold Bw at *; omega
                    rw [hwa, zero_mul, add_zero] at hal
                    right; right; exact ⟨0, by unfold Tstep; simp; omega, Nat.two_pow_pos _⟩
              | regX sb wb kb =>
                cases bb
                · simp [tipK] at hbK
                · simp only [tipK, decide_eq_true_eq] at hbK; subst hbK
                  cases sa <;> cases sb
                  · have hne_w : wa.val ≠ wb.val := fun h => hab (by congr 1; congr 1; exact Fin.ext h)
                    by_cases hlt : wa.val < wb.val
                    · have h1 : wa.val + 1 < 2 ^ (t + 1) := by omega
                      simp only [bagHi, bagLo] at hah hbl; rw [if_pos h1] at hah; simp only [Tstep, Bool.false_eq_true, ↓reduceIte] at hah hbl
                      have hwb : wb.val = wa.val + 1 := by
                        by_contra hne1
                        have : (wa.val + 2) * Bw t ≤ wb.val * Bw t := Nat.mul_le_mul_right _ (by omega)
                        have : (wa.val + 1) * Bw t + Bw t = (wa.val + 2) * Bw t := by ring
                        unfold Bw at *; omega
                      rw [← hwb] at hah
                      left; exact ⟨wb.val, by unfold Tstep; simp; omega, wb.isLt⟩
                    · have h1 : wb.val + 1 < 2 ^ (t + 1) := by omega
                      simp only [bagHi, bagLo] at hbh hal; rw [if_pos h1] at hbh; simp only [Tstep, Bool.false_eq_true, ↓reduceIte] at hbh hal
                      have hwa : wa.val = wb.val + 1 := by
                        by_contra hne1
                        have : (wb.val + 2) * Bw t ≤ wa.val * Bw t := Nat.mul_le_mul_right _ (by omega)
                        have : (wb.val + 1) * Bw t + Bw t = (wb.val + 2) * Bw t := by ring
                        unfold Bw at *; omega
                      rw [← hwa] at hbh
                      left; exact ⟨wa.val, by unfold Tstep; simp; omega, wa.isLt⟩
                  · simp only [bagHi, bagLo] at hah hbl; by_cases h1 : wa.val + 1 < 2 ^ (t + 1)
                    · rw [if_pos h1] at hah; simp only [Tstep, R0, M0, Bool.false_eq_true, ↓reduceIte] at hah hbl
                      have hle : (wa.val + 2) * Bw t ≤ 2 ^ (t + 1) * Bw t := Nat.mul_le_mul_right _ (by omega)
                      have hmul : (wa.val + 1) * Bw t + Bw t = (wa.val + 2) * Bw t := by ring
                      have := kb.isLt; unfold Bw at *; omega
                    · rw [if_neg h1] at hah; simp only [Tstep, R0, M0, ↓reduceIte] at hah hbl; have := kb.isLt; omega
                  · simp only [bagHi, bagLo] at hbh hal; by_cases h1 : wb.val + 1 < 2 ^ (t + 1)
                    · rw [if_pos h1] at hbh; simp only [Tstep, R0, M0, Bool.false_eq_true, ↓reduceIte] at hbh hal
                      have hle : (wb.val + 2) * Bw t ≤ 2 ^ (t + 1) * Bw t := Nat.mul_le_mul_right _ (by omega)
                      have hmul : (wb.val + 1) * Bw t + Bw t = (wb.val + 2) * Bw t := by ring
                      have := kb.isLt; unfold Bw at *; omega
                    · rw [if_neg h1] at hbh; simp only [Tstep, R0, M0, ↓reduceIte] at hbh hal; have := kb.isLt; omega
                  · have hne_w : wa.val ≠ wb.val := fun h => hab (by congr 1; congr 1; exact Fin.ext h)
                    by_cases hlt : wa.val < wb.val
                    · have h1 : wa.val + 1 < 2 ^ (t + 1) := by omega
                      simp only [bagHi, bagLo] at hah hbl; rw [if_pos h1] at hah; simp only [Tstep, ↓reduceIte] at hah hbl
                      have hwb : wb.val = wa.val + 1 := by
                        by_contra hne1
                        have : (wa.val + 2) * Bw t ≤ wb.val * Bw t := Nat.mul_le_mul_right _ (by omega)
                        have : (wa.val + 1) * Bw t + Bw t = (wa.val + 2) * Bw t := by ring
                        unfold Bw at *; omega
                      rw [← hwb] at hah
                      right; right; exact ⟨wb.val, by unfold Tstep; simp; omega, wb.isLt⟩
                    · have h1 : wb.val + 1 < 2 ^ (t + 1) := by omega
                      simp only [bagHi, bagLo] at hbh hal; rw [if_pos h1] at hbh; simp only [Tstep, ↓reduceIte] at hbh hal
                      have hwa : wa.val = wb.val + 1 := by
                        by_contra hne1
                        have : (wb.val + 2) * Bw t ≤ wa.val * Bw t := Nat.mul_le_mul_right _ (by omega)
                        have : (wb.val + 1) * Bw t + Bw t = (wb.val + 2) * Bw t := by ring
                        unfold Bw at *; omega
                      rw [← hwa] at hbh
                      right; right; exact ⟨wa.val, by unfold Tstep; simp; omega, wa.isLt⟩
              | _ => simp [tipK] at hbK
          | _ => simp [tipK] at haK
        rcases hcommon ⟨u1, bu⟩ ⟨v1, bv⟩ hulo huhi hvlo hvhi huK hvK huv with ⟨w, rfl, hw⟩ | rfl | ⟨w, rfl, hw⟩
        · left; simp only [Tstep, M0, Bool.false_eq_true, ↓reduceIte]
          have hle : (w + 1) * Bw t ≤ 2 ^ (t + 1) * Bw t := Nat.mul_le_mul_right _ hw
          have hmul : w * Bw t + Bw t = (w + 1) * Bw t := by ring
          refine ⟨by unfold Bw at *; omega, ?_, by omega⟩
          have : (t + 1 + w * Bw t + k.val) - (t + 1) = k.val + w * Bw t := by omega
          rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by unfold Bw; omega)]
        · right; left; unfold R0; omega
        · right; right; simp only [Tstep, ↓reduceIte]
          refine ⟨by omega, ?_⟩
          have : (R0 t + w * Bw t + k.val) - R0 t = k.val + w * Bw t := by omega
          rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by unfold Bw; omega)]
      have hc1 := hτ_mod k1 h1; have hc2 := hτ_mod k2 h2
      rcases hc1 with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1⟩ | ⟨a1, b1⟩ <;>
        rcases hc2 with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2⟩ | ⟨a2, b2⟩
      · exact hne (Fin.ext (b1.symm.trans b2))
      · omega
      · unfold R0 at a2; omega
      · omega
      · exact hne (Fin.ext (c1.symm.trans c2))
      · omega
      · unfold R0 at a1; omega
      · omega
      · exact hne (Fin.ext (b1.symm.trans b2))
    have hpart : (B.filter (fun v => isTip v = true)).card =
        ∑ k : Fin (t + 1), (B.filter (fun v => tipK v k = true)).card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext ⟨u, b⟩; simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
        cases u <;> cases b <;> simp [isTip, tipK]
      · intro k1 _ k2 _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro ⟨u, b⟩ h1 h2
        have a1 := (Finset.mem_filter.mp h1).2; have a2 := (Finset.mem_filter.mp h2).2
        cases u <;> cases b <;> simp only [tipK, decide_eq_true_eq, Bool.false_eq_true] at a1 a2
        · exact hne (a1.symm.trans a2)
        · exact hne (a1.symm.trans a2)
    rw [hpart]
    by_cases hex : ∃ k0 : Fin (t + 1), 2 ≤ (B.filter (fun v => tipK v k0 = true)).card
    · rcases hex with ⟨k0, hk0⟩
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k0)]
      have hrest : ∑ k ∈ Finset.univ.erase k0, (B.filter (fun v => tipK v k = true)).card ≤
          ∑ _k ∈ Finset.univ.erase k0, 1 := Finset.sum_le_sum fun k hk => by
        have hne : k0 ≠ k := (Finset.mem_erase.mp hk).1.symm
        have := hpair_ge2 k0 k hne; omega
      have h1 := htip_k k0
      simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ k0), Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hrest
      omega
    · push_neg at hex
      calc ∑ k : Fin (t + 1), _ ≤ ∑ _k : Fin (t + 1), 1 := Finset.sum_le_sum fun k _ => by have := hex k; omega
        _ ≤ (t + 1) + 1 := by simp
  have hTstep_out : ∀ (s : Bool) (w : Fin (2 ^ (t + 1))) (r : ℕ), r < Bw t →
      t + 1 ≤ Tstep t s w.val r ∧ (Tstep t s w.val r < M0 t ∨ R0 t ≤ Tstep t s w.val r) := by
    intro s w r hr
    have hle : (w.val + 1) * Bw t ≤ 2 ^ (t + 1) * Bw t := Nat.mul_le_mul_right (Bw t) w.isLt
    have hmul : w.val * Bw t + Bw t = (w.val + 1) * Bw t := by ring
    cases s
    · simp only [Tstep, M0, R0, Bool.false_eq_true, ↓reduceIte]; exact ⟨by omega, Or.inl (by omega)⟩
    · simp only [Tstep, M0, R0, ↓reduceIte]; exact ⟨by omega, Or.inr (by omega)⟩
  have hnon_le : (B.filter (fun v => isTip v = false)).card ≤ 36 := by
    by_cases h0 : τ < t + 1
    · have hsub : B.filter (fun v => isTip v = false) ⊆ {(.initReg false ⟨τ, h0⟩, false)} := by
        intro ⟨u, b⟩ hu
        have hB := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
        have hT := (Finset.mem_filter.mp hu).2
        simp only [Finset.mem_singleton]
        cases u with
        | initReg s k =>
          cases b
          · cases s
            · simp only [bagLo, bagHi] at hB; exact Prod.ext (congrArg (PairV.initReg false) (Fin.ext (by dsimp only; omega))) rfl
            · simp only [bagLo, M0] at hB; omega
          · simp [isTip] at hT
        | bridge k => simp only [bagLo, M0] at hB; omega
        | regP s w k => have := (hTstep_out s w k.val (by unfold Bw; omega)).1; simp only [bagLo] at hB; omega
        | regX s w k =>
          cases b
          · have := (hTstep_out s w k.val (by unfold Bw; omega)).1; simp only [bagLo] at hB; omega
          · simp [isTip] at hT
        | detD s w k => have := (hTstep_out s w k.val (by unfold Bw; omega)).1; simp only [bagLo] at hB; omega
        | detQ s w k => have := (hTstep_out s w (k.val + 1) (by unfold Bw; omega)).1; simp only [bagLo] at hB; omega
        | detU s w k c => have := (hTstep_out s w k.val (by unfold Bw; omega)).1; simp only [bagLo] at hB; omega
        | detF s w c => have := (hTstep_out s w (t + 1) (by unfold Bw; omega)).1; simp only [bagLo] at hB; omega
        | padT s w j c => have := (hTstep_out s w ((t + 1) + 1 + j.val) (by unfold Bw; omega)).1; simp only [bagLo] at hB; omega
      exact (Finset.card_le_card hsub).trans (by simp)
    · by_cases hmid : M0 t ≤ τ ∧ τ < R0 t
      · let k0 : Fin (t + 1) := ⟨τ - M0 t, by unfold R0 at hmid; omega⟩
        let S : Finset (PairV t × Bool) := {(.bridge k0, false), (.bridge k0, true), (.initReg true k0, false)}
        have hsub : B.filter (fun v => isTip v = false) ⊆ S := by
          intro ⟨u, b⟩ hu
          have hB := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
          have hT := (Finset.mem_filter.mp hu).2
          cases u with
          | initReg s k =>
            cases b
            · cases s
              · simp only [bagHi, M0] at hB; have := k.isLt; omega
              · simp only [bagLo, bagHi] at hB
                have hk : k = k0 := Fin.ext (by dsimp only [k0]; omega)
                subst hk; simp [S]
            · simp [isTip] at hT
          | bridge k =>
            simp only [bagLo, bagHi] at hB
            have hk : k = k0 := Fin.ext (by dsimp only [k0]; omega)
            subst hk; cases b <;> simp [S]
          | regP s w k =>
            have h1 := (hTstep_out s w k.val (by unfold Bw; omega)).2
            simp only [bagLo, bagHi] at hB; rcases h1 with h1 | h1 <;> omega
          | regX s w k =>
            cases b
            · have h1 := (hTstep_out s w k.val (by unfold Bw; omega)).2
              simp only [bagLo, bagHi] at hB; rcases h1 with h1 | h1 <;> omega
            · simp [isTip] at hT
          | detD s w k =>
            have hlo := (hTstep_out s w k.val (by unfold Bw; omega)).2
            simp only [bagLo, bagHi] at hB
            by_cases hk : k.val + 1 < t + 1
            · rw [if_pos hk] at hB
              have hhi := (hTstep_out s w (k.val + 1) (by unfold Bw; omega)).2
              cases s
              · simp only [Tstep, M0, Bool.false_eq_true, ↓reduceIte] at hB hmid
                have hle : (w.val + 1) * Bw t ≤ 2 ^ (t + 1) * Bw t := Nat.mul_le_mul_right (Bw t) w.isLt
                have hmul : w.val * Bw t + Bw t = (w.val + 1) * Bw t := by ring
                have := k.isLt; unfold Bw at *; omega
              · simp only [Tstep, ↓reduceIte] at hB; omega
            · rw [if_neg hk] at hB; rcases hlo with hlo | hlo <;> omega
          | detQ s w k =>
            have h1 := (hTstep_out s w (k.val + 1) (by unfold Bw; omega)).2
            simp only [bagLo, bagHi] at hB; rcases h1 with h1 | h1 <;> omega
          | detU s w k c =>
            have h1 := (hTstep_out s w k.val (by unfold Bw; omega)).2
            simp only [bagLo, bagHi] at hB; rcases h1 with h1 | h1 <;> omega
          | detF s w c =>
            have h1 := (hTstep_out s w (t + 1) (by unfold Bw; omega)).2
            simp only [bagLo, bagHi] at hB; rcases h1 with h1 | h1 <;> omega
          | padT s w j c =>
            have h1 := (hTstep_out s w ((t + 1) + 1 + j.val) (by unfold Bw; omega)).2
            simp only [bagLo, bagHi] at hB; rcases h1 with h1 | h1 <;> omega
        exact (Finset.card_le_card hsub).trans (by
          refine (Finset.card_insert_le _ _).trans ?_
          refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
          simp)
      · let side0 : Bool := decide (R0 t ≤ τ)
        let base : ℕ := if side0 then R0 t else (t + 1)
        have hrange : base ≤ τ ∧ τ < base + 2 ^ (t + 1) * Bw t := by
          dsimp only [base, side0]
          by_cases hs : R0 t ≤ τ
          · simp only [hs, decide_true, ↓reduceIte]; exact ⟨trivial, hτ⟩
          · simp only [hs, decide_false, Bool.false_eq_true, ↓reduceIte]
            have hltM : τ < M0 t := by omega
            exact ⟨by omega, hltM⟩
        let w0 : Fin (2 ^ (t + 1)) := ⟨(τ - base) / Bw t, Nat.div_lt_of_lt_mul (by rw [mul_comm]; omega)⟩
        let s0 : ℕ := (τ - base) % Bw t
        have hτ_eq : τ = Tstep t side0 w0.val s0 := by
          dsimp only [Tstep, base, w0, s0]
          have hdm := Nat.div_add_mod (τ - base) (Bw t)
          dsimp only [base] at hdm hrange; rw [mul_comm] at hdm; omega
        have hmatch_sw : ∀ (s : Bool) (w : Fin (2 ^ (t + 1))) (r : ℕ), r < Bw t →
            Tstep t s w.val r = τ → s = side0 ∧ w = w0 ∧ r = s0 := by
          intro s w r hr heq
          have hs_eq : s = side0 := by
            by_contra hne
            have h1 : (w.val + 1) * Bw t ≤ 2 ^ (t + 1) * Bw t := Nat.mul_le_mul_right (Bw t) w.isLt
            have h2 : w.val * Bw t + Bw t = (w.val + 1) * Bw t := by ring
            cases s
            · have hs0 : side0 = true := Bool.eq_true_of_not_eq_false (Ne.symm hne)
              have hbase : base = R0 t := by simp only [base, hs0, ↓reduceIte]
              rw [hbase] at hrange; simp only [Tstep, Bool.false_eq_true, ↓reduceIte] at heq
              unfold R0 M0 at hrange; omega
            · have hs0 : side0 = false := Bool.eq_false_iff.mpr (Ne.symm hne)
              have hbase : base = t + 1 := by simp only [base, hs0, Bool.false_eq_true, ↓reduceIte]
              rw [hbase] at hrange; simp only [Tstep, ↓reduceIte] at heq
              simp only [R0, M0] at heq hrange; omega
          subst hs_eq
          have hmul : w.val * Bw t + r = τ - base := by
            dsimp only [Tstep] at heq; dsimp only [base] at hrange ⊢; omega
          have hw_eq : w.val = (τ - base) / Bw t := by
            rw [← hmul, mul_comm, Nat.mul_add_div (by unfold Bw; omega), Nat.div_eq_of_lt hr, add_zero]
          have hr_eq : r = (τ - base) % Bw t := by
            rw [← hmul, mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
          exact ⟨rfl, Fin.ext hw_eq, hr_eq⟩
        let locP : Finset (PairV t) :=
          (if hk : s0 < t + 1 then
            {.regP side0 w0 ⟨s0, hk⟩, .regX side0 w0 ⟨s0, hk⟩, .detD side0 w0 ⟨s0, hk⟩} ∪
            (Finset.univ : Finset (Fin 4)).image (fun c => .detU side0 w0 ⟨s0, hk⟩ c) ∪
            (if hk1 : 0 < s0 then {.detD side0 w0 ⟨s0 - 1, by omega⟩, .detQ side0 w0 ⟨s0 - 1, by omega⟩} else ∅)
          else ∅) ∪
          (if s0 = t + 1 then (Finset.univ : Finset (Fin 3)).image (fun c => .detF side0 w0 c) else ∅) ∪
          (if hj : (t + 1) + 1 ≤ s0 ∧ s0 < Bw t then
            {.padT side0 w0 ⟨s0 - ((t + 1) + 1), by unfold Bw at hj; omega⟩ false,
             .padT side0 w0 ⟨s0 - ((t + 1) + 1), by unfold Bw at hj; omega⟩ true}
          else ∅)
        have hloc_card : locP.card ≤ 18 := by
          have c1 : (if hk : s0 < t + 1 then
              ({PairV.regP side0 w0 ⟨s0, hk⟩, PairV.regX side0 w0 ⟨s0, hk⟩, PairV.detD side0 w0 ⟨s0, hk⟩} ∪
              (Finset.univ : Finset (Fin 4)).image (fun c => PairV.detU side0 w0 ⟨s0, hk⟩ c) ∪
              (if hk1 : 0 < s0 then {PairV.detD side0 w0 ⟨s0 - 1, by omega⟩, PairV.detQ side0 w0 ⟨s0 - 1, by omega⟩} else ∅))
            else ∅).card ≤ 9 := by
            by_cases hk : s0 < t + 1
            · rw [dif_pos hk]
              refine (Finset.card_union_le _ _).trans ?_
              have ca : ({PairV.regP side0 w0 ⟨s0, hk⟩, .regX side0 w0 ⟨s0, hk⟩, .detD side0 w0 ⟨s0, hk⟩} : Finset (PairV t)).card ≤ 3 :=
                (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ((Finset.card_insert_le _ _).trans (by simp)) 1)
              have cb : ((Finset.univ : Finset (Fin 4)).image (fun c => PairV.detU side0 w0 ⟨s0, hk⟩ c)).card ≤ 4 :=
                Finset.card_image_le.trans (by simp)
              have cc : (if hk1 : 0 < s0 then ({PairV.detD side0 w0 ⟨s0 - 1, by omega⟩, .detQ side0 w0 ⟨s0 - 1, by omega⟩} : Finset (PairV t)) else ∅).card ≤ 2 := by
                by_cases hk1 : 0 < s0
                · rw [dif_pos hk1]; exact (Finset.card_insert_le _ _).trans (by simp)
                · rw [dif_neg hk1]; simp
              have cab := Finset.card_union_le ({PairV.regP side0 w0 ⟨s0, hk⟩, .regX side0 w0 ⟨s0, hk⟩, .detD side0 w0 ⟨s0, hk⟩}) ((Finset.univ : Finset (Fin 4)).image (fun c => PairV.detU side0 w0 ⟨s0, hk⟩ c))
              omega
            · rw [dif_neg hk]; simp
          have c2 : (if s0 = t + 1 then (Finset.univ : Finset (Fin 3)).image (fun c => PairV.detF side0 w0 c) else ∅).card ≤ 3 := by
            split_ifs
            · exact Finset.card_image_le.trans (by simp)
            · simp
          have c3 : (if hj : (t + 1) + 1 ≤ s0 ∧ s0 < Bw t then
              ({PairV.padT side0 w0 ⟨s0 - ((t + 1) + 1), by unfold Bw at hj; omega⟩ false,
                .padT side0 w0 ⟨s0 - ((t + 1) + 1), by unfold Bw at hj; omega⟩ true} : Finset (PairV t))
            else ∅).card ≤ 2 := by
            split_ifs
            · exact (Finset.card_insert_le _ _).trans (by simp)
            · simp
          exact (Finset.card_union_le _ _).trans (Nat.add_le_add ((Finset.card_union_le _ _).trans (by omega)) c3)
        have hsub : B.filter (fun v => isTip v = false) ⊆ locP ×ˢ (Finset.univ : Finset Bool) := by
          intro ⟨u, b⟩ hu
          have hB := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
          have hT := (Finset.mem_filter.mp hu).2
          rw [Finset.mem_product]; refine ⟨?_, Finset.mem_univ _⟩
          cases u with
          | initReg s k =>
            cases b
            · cases s <;> simp [bagLo, bagHi] at hB
              · omega
              · exfalso; exact hmid ⟨by omega, by unfold R0; omega⟩
            · simp [isTip] at hT
          | bridge k =>
            simp [bagLo, bagHi] at hB; exfalso; exact hmid ⟨by omega, by unfold R0; omega⟩
          | regP s w k =>
            simp only [bagLo, bagHi] at hB
            rcases hmatch_sw s w k.val (by unfold Bw; omega) (by omega) with ⟨rfl, rfl, hks⟩
            refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
            rw [dif_pos (by omega)]
            refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
            simp only [Finset.mem_insert, Finset.mem_singleton]; left; congr 1; exact Fin.ext hks
          | regX s w k =>
            cases b
            · simp only [bagLo, bagHi] at hB
              rcases hmatch_sw s w k.val (by unfold Bw; omega) (by omega) with ⟨rfl, rfl, hks⟩
              refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
              rw [dif_pos (by omega)]
              refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
              simp only [Finset.mem_insert, Finset.mem_singleton]; right; left; congr 1; exact Fin.ext hks
            · simp [isTip] at hT
          | detD s w k =>
            simp only [bagLo, bagHi] at hB
            have hcase : Tstep t s w.val k.val = τ ∨ (k.val + 1 < t + 1 ∧ Tstep t s w.val (k.val + 1) = τ) := by
              split_ifs at hB with hlt
              · unfold Tstep at hB ⊢; omega
              · left; omega
            rcases hcase with heq | ⟨hlt, heq⟩
            · rcases hmatch_sw s w k.val (by unfold Bw; omega) heq with ⟨rfl, rfl, hks⟩
              refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
              rw [dif_pos (by omega)]
              refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
              simp only [Finset.mem_insert, Finset.mem_singleton]; right; right; congr 1; exact Fin.ext hks
            · rcases hmatch_sw s w (k.val + 1) (by unfold Bw; omega) heq with ⟨rfl, rfl, hks⟩
              refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
              rw [dif_pos (by omega)]
              refine Finset.mem_union_right _ ?_
              rw [dif_pos (by omega)]
              simp only [Finset.mem_insert, Finset.mem_singleton]; left; congr 1; exact Fin.ext (by dsimp only; omega)
          | detQ s w k =>
            simp only [bagLo, bagHi] at hB
            rcases hmatch_sw s w (k.val + 1) (by unfold Bw; omega) (by omega) with ⟨rfl, rfl, hks⟩
            refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
            rw [dif_pos (by omega)]
            refine Finset.mem_union_right _ ?_
            rw [dif_pos (by omega)]
            simp only [Finset.mem_insert, Finset.mem_singleton]; right; congr 1; exact Fin.ext (by dsimp only; omega)
          | detU s w k c =>
            simp only [bagLo, bagHi] at hB
            rcases hmatch_sw s w k.val (by unfold Bw; omega) (by omega) with ⟨rfl, rfl, hks⟩
            refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
            rw [dif_pos (by omega)]
            refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
            exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, by congr 1; exact Fin.ext hks.symm⟩
          | detF s w c =>
            simp only [bagLo, bagHi] at hB
            rcases hmatch_sw s w (t + 1) (by unfold Bw; omega) (by omega) with ⟨rfl, rfl, hks⟩
            refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
            rw [if_pos hks.symm]
            exact Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩
          | padT s w j b' =>
            simp only [bagLo, bagHi] at hB
            rcases hmatch_sw s w ((t + 1) + 1 + j.val) (by unfold Bw; omega) (by omega) with ⟨rfl, rfl, hks⟩
            refine Finset.mem_union_right _ ?_
            rw [dif_pos ⟨by omega, by unfold Bw; omega⟩]
            cases b'
            · simp only [Finset.mem_insert, Finset.mem_singleton]; left; congr 1; exact Fin.ext (by dsimp only; omega)
            · simp only [Finset.mem_insert, Finset.mem_singleton]; right; congr 1; exact Fin.ext (by dsimp only; omega)
        calc (B.filter (fun v => isTip v = false)).card
            ≤ (locP ×ˢ (Finset.univ : Finset Bool)).card := Finset.card_le_card hsub
          _ = locP.card * 2 := by simp
          _ ≤ 36 := by omega
  change B.card ≤ (t + 1) + 37; omega

section CountingSucc
open scoped Classical

private lemma card_mono_succ (t : ℕ) (f g : (Fin (t + 1) → Bool) → Bool) :
    let on : PairV t → Bool := fun i =>
      (pairTag i).elim true (fun p => decide ((if pairSide i then g else f) p.1 = p.2))
    ((Finset.univ : Finset (PairV t → Bool)).filter (fun a =>
      (∀ u, on u = false → a u = false) ∧
      ∀ u v, on u = true → on v = true → pairArc u v = true → a u = true → a v = true)).card % 2 =
    ((Finset.univ : Finset (Fin (t + 1) → Bool)).filter (fun y => f y && g y)).card % 2 := by
  intro on
  let W := 2 ^ (t + 1)
  let n := t + 1
  let tbl : Bool → Fin W → Bool := fun s w => (if s then g else f) (wordOf n w)
  have hon_init : ∀ s k, on (.initReg s k) = true := fun _ _ => rfl
  have hon_bridge : ∀ k, on (.bridge k) = true := fun _ => rfl
  have hon_regP : ∀ s w k, on (.regP s w k) = true := fun _ _ _ => rfl
  have hon_regX : ∀ s w k, on (.regX s w k) = true := fun _ _ _ => rfl
  have hon_detD : ∀ s w k, on (.detD s w k) = !(tbl s w) := fun s w k => by
    cases s
    · dsimp only [on, pairTag, pairSide, tbl, n, Option.elim]; cases f (wordOf (t + 1) w) <;> rfl
    · dsimp only [on, pairTag, pairSide, tbl, n, Option.elim]; cases g (wordOf (t + 1) w) <;> rfl
  have hon_detQ : ∀ s w k, on (.detQ s w k) = !(tbl s w) := fun s w k => by
    cases s
    · dsimp only [on, pairTag, pairSide, tbl, n, Option.elim]; cases f (wordOf (t + 1) w) <;> rfl
    · dsimp only [on, pairTag, pairSide, tbl, n, Option.elim]; cases g (wordOf (t + 1) w) <;> rfl
  have hon_detU : ∀ s w k c, on (.detU s w k c) = !(tbl s w) := fun s w k c => by
    cases s
    · dsimp only [on, pairTag, pairSide, tbl, n, Option.elim]; cases f (wordOf (t + 1) w) <;> rfl
    · dsimp only [on, pairTag, pairSide, tbl, n, Option.elim]; cases g (wordOf (t + 1) w) <;> rfl
  have hon_detF : ∀ s w c, on (.detF s w c) = !(tbl s w) := fun s w c => by
    cases s
    · dsimp only [on, pairTag, pairSide, tbl, n, Option.elim]; cases f (wordOf (t + 1) w) <;> rfl
    · dsimp only [on, pairTag, pairSide, tbl, n, Option.elim]; cases g (wordOf (t + 1) w) <;> rfl
  have hon_padT : ∀ s w j b, on (.padT s w j b) = tbl s w := fun s w j b => by
    cases s
    · dsimp only [on, pairTag, pairSide, tbl, n, Option.elim]; cases f (wordOf (t + 1) w) <;> rfl
    · dsimp only [on, pairTag, pairSide, tbl, n, Option.elim]; cases g (wordOf (t + 1) w) <;> rfl
  let Mono := (Finset.univ : Finset (PairV t → Bool)).filter (fun a =>
    (∀ u, on u = false → a u = false) ∧
    ∀ u v, on u = true → on v = true → pairArc u v = true → a u = true → a v = true)
  let RegProf := Bool × Fin (W + 1) → Fin n → Bool
  let regOf (a : PairV t → Bool) : RegProf := fun ⟨s, idx⟩ k =>
    if h : idx.val = 0 then a (.initReg s k) else a (.regX s ⟨idx.val - 1, by omega⟩ k)
  have hpart : Mono.card = ∑ X : RegProf, (Mono.filter (fun a => regOf a = X)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext a; simp
    · intro X1 _ X2 _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro a h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  let detBlock (X : RegProf) (s : Bool) (w : Fin W) : ℕ :=
    if tbl s w = false then
      ((Finset.univ : Finset ((Fin n → Bool) × (Fin t → Bool) × (Fin n → Fin 4 → Bool) × (Fin 3 → Bool))).filter (fun p =>
        let D := p.1; let Q := p.2.1; let U := p.2.2.1; let F := p.2.2.2
        (∀ k : Fin t, (D k.castSucc = true → Q k = true) ∧ (Q k = true → D k.succ = true)) ∧
        (∀ k : Fin n,
          if wordOf n w k then
            (X (s, ⟨w.val, by omega⟩) k = true → U k ⟨0, by decide⟩ = true) ∧
            (D k = true → U k ⟨0, by decide⟩ = true) ∧
            (U k ⟨1, by decide⟩ = true → U k ⟨2, by decide⟩ = true) ∧
            (U k ⟨1, by decide⟩ = true → U k ⟨3, by decide⟩ = true)
          else
            (X (s, ⟨w.val, by omega⟩) k = true → D k = true) ∧
            (U k ⟨0, by decide⟩ = true → U k ⟨1, by decide⟩ = true) ∧
            (U k ⟨2, by decide⟩ = true → U k ⟨3, by decide⟩ = true)) ∧
        (F ⟨0, by decide⟩ = true → F ⟨1, by decide⟩ = true) ∧
        (F ⟨0, by decide⟩ = true → F ⟨2, by decide⟩ = true))).card
    else
      ((Finset.univ : Finset (Fin (3 * n + 1) → Bool → Bool)).filter (fun P =>
        ∀ j, P j false = true → P j true = true)).card
  let transW (b1 b2 : Bool) : ℕ := if b1 = true ∧ b2 = false then 0 else if b1 = b2 then 1 else 2
  have hfib_card : ∀ X : RegProf,
      (Mono.filter (fun a => regOf a = X)).card =
      (∏ s : Bool, ∏ w : Fin W, ∏ k : Fin n, transW (X (s, ⟨w.val, by omega⟩) k) (X (s, ⟨w.val + 1, by omega⟩) k)) *
      (∏ k : Fin n, transW (X (false, ⟨W, Nat.lt_succ_self W⟩) k) (X (true, ⟨0, Nat.succ_pos W⟩) k)) *
      (∏ s : Bool, ∏ w : Fin W, detBlock X s w) := by
    intro X
    let RP := Fintype.piFinset fun swk : Bool × Fin W × Fin n =>
      (Finset.univ : Finset Bool).filter (fun b =>
        (X (swk.1, ⟨swk.2.1.val, by omega⟩) swk.2.2 = true → b = true) ∧
        (b = true → X (swk.1, ⟨swk.2.1.val + 1, by omega⟩) swk.2.2 = true))
    let BR := Fintype.piFinset fun k : Fin n =>
      (Finset.univ : Finset Bool).filter (fun b =>
        (X (false, ⟨W, Nat.lt_succ_self W⟩) k = true → b = true) ∧
        (b = true → X (true, ⟨0, Nat.succ_pos W⟩) k = true))
    let DetType := ((Fin n → Bool) × (Fin t → Bool) × (Fin n → Fin 4 → Bool) × (Fin 3 → Bool)) × (Fin (3 * n + 1) → Bool → Bool)
    let DET := Fintype.piFinset fun sw : Bool × Fin W =>
      (Finset.univ : Finset DetType).filter (fun p =>
        let D := p.1.1; let Q := p.1.2.1; let U := p.1.2.2.1; let F := p.1.2.2.2; let P := p.2
        if tbl sw.1 sw.2 = false then
          (P = fun _ _ => false) ∧
          (∀ k : Fin t, (D k.castSucc = true → Q k = true) ∧ (Q k = true → D k.succ = true)) ∧
          (∀ k : Fin n,
            if wordOf n sw.2 k then
              (X (sw.1, ⟨sw.2.val, by omega⟩) k = true → U k ⟨0, by decide⟩ = true) ∧
              (D k = true → U k ⟨0, by decide⟩ = true) ∧
              (U k ⟨1, by decide⟩ = true → U k ⟨2, by decide⟩ = true) ∧
              (U k ⟨1, by decide⟩ = true → U k ⟨3, by decide⟩ = true)
            else
              (X (sw.1, ⟨sw.2.val, by omega⟩) k = true → D k = true) ∧
              (U k ⟨0, by decide⟩ = true → U k ⟨1, by decide⟩ = true) ∧
              (U k ⟨2, by decide⟩ = true → U k ⟨3, by decide⟩ = true)) ∧
          (F ⟨0, by decide⟩ = true → F ⟨1, by decide⟩ = true) ∧
          (F ⟨0, by decide⟩ = true → F ⟨2, by decide⟩ = true)
        else
          (D = fun _ => false) ∧ (Q = fun _ => false) ∧ (U = fun _ _ => false) ∧ (F = fun _ => false) ∧
          (∀ j, P j false = true → P j true = true))
    have hRP_card : RP.card = ∏ s : Bool, ∏ w : Fin W, ∏ k : Fin n,
        transW (X (s, ⟨w.val, by omega⟩) k) (X (s, ⟨w.val + 1, by omega⟩) k) := by
      rw [Fintype.card_piFinset, Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun s _ => ?_
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun w _ => Finset.prod_congr rfl fun k _ => ?_
      exact transW_card_eq (X (s, ⟨w.val, by omega⟩) k) (X (s, ⟨w.val + 1, by omega⟩) k)
    have hBR_card : BR.card = ∏ k : Fin n, transW (X (false, ⟨W, Nat.lt_succ_self W⟩) k) (X (true, ⟨0, Nat.succ_pos W⟩) k) := by
      rw [Fintype.card_piFinset]
      refine Finset.prod_congr rfl fun k _ => ?_
      exact transW_card_eq (X (false, ⟨W, Nat.lt_succ_self W⟩) k) (X (true, ⟨0, Nat.succ_pos W⟩) k)
    have hDET_card : DET.card = ∏ s : Bool, ∏ w : Fin W, detBlock X s w := by
      rw [Fintype.card_piFinset, Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun w _ => ?_
      dsimp only [detBlock]
      by_cases htb : tbl s w = false
      · rw [if_pos htb]
        refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
        · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and, if_pos htb] at hp ⊢; exact hp.2
        · intro p1 h1 p2 h2 heq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, if_pos htb] at h1 h2
          exact Prod.ext heq (h1.1.trans h2.1.symm)
        · intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
          exact ⟨(q, fun _ _ => false), by simp only [Finset.mem_filter, Finset.mem_univ, true_and, if_pos htb]; exact hq, rfl⟩
      · rw [if_neg htb]
        refine Finset.card_bij (fun p _ => p.2) ?_ ?_ ?_
        · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and, if_neg htb] at hp ⊢; exact hp.2.2.2.2
        · intro p1 h1 p2 h2 heq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, if_neg htb] at h1 h2
          refine Prod.ext (Prod.ext (h1.1.trans h2.1.symm) (Prod.ext (h1.2.1.trans h2.2.1.symm)
            (Prod.ext (h1.2.2.1.trans h2.2.2.1.symm) (h1.2.2.2.1.trans h2.2.2.2.1.symm)))) heq
        · intro P hP
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP
          exact ⟨((fun _ => false, fun _ => false, fun _ _ => false, fun _ => false), P),
            by simp only [Finset.mem_filter, Finset.mem_univ, true_and, if_neg htb]; exact hP, rfl⟩
    rw [← hRP_card, ← hBR_card, ← hDET_card, ← Finset.card_product, ← Finset.card_product]
    refine Finset.card_bij
      (fun a _ => ((fun swk => a (.regP swk.1 swk.2.1 swk.2.2), fun k => a (.bridge k)),
        fun sw => ((fun k => a (.detD sw.1 sw.2 k), fun k => a (.detQ sw.1 sw.2 k),
          fun k c => a (.detU sw.1 sw.2 k c), fun c => a (.detF sw.1 sw.2 c)),
          fun j b => a (.padT sw.1 sw.2 j b)))) ?_ ?_ ?_
    · intro a ha
      simp only [Mono, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rcases ha with ⟨⟨hoff, harc⟩, hreg⟩
      have hprev_eq : ∀ s w k, a (prevReg s w k) = X (s, ⟨w.val, by omega⟩) k := by
        intro s w k; rw [← hreg]; dsimp only [prevReg, regOf]; split_ifs <;> rfl
      have hregX_eq : ∀ s w k, a (.regX s w k) = X (s, ⟨w.val + 1, by omega⟩) k := by
        intro s w k; rw [← hreg]; dsimp only [regOf]; rw [dif_neg (Nat.succ_ne_zero w.val)]; rfl
      have hinit_eq : ∀ s k, a (.initReg s k) = X (s, ⟨0, Nat.succ_pos W⟩) k := by
        intro s k; rw [← hreg]; rfl
      simp only [Finset.mem_product, RP, BR, DET, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨fun ⟨s, w, k⟩ => ⟨?_, ?_⟩, fun k => ⟨?_, ?_⟩⟩, fun ⟨s, w⟩ => ?_⟩
      · intro hx; rw [← hprev_eq s w k] at hx
        exact harc (prevReg s w k) (.regP s w k) (by unfold prevReg; split_ifs <;> rfl) rfl
          (by unfold pairArc; rw [decide_eq_true_eq, pairArc_iff_in]; simp [pairIn]) hx
      · intro hp; rw [← hregX_eq s w k]
        exact harc (.regP s w k) (.regX s w k) rfl rfl (by simp [pairArc, pairOut]) hp
      · intro hx
        have hW1 : a (.regX false ⟨W - 1, Nat.sub_lt (Nat.two_pow_pos _) (by decide)⟩ k) = X (false, ⟨W, Nat.lt_succ_self W⟩) k := by
          have := hregX_eq false ⟨W - 1, Nat.sub_lt (Nat.two_pow_pos _) (by decide)⟩ k
          have hWpos : 0 < W := Nat.two_pow_pos _
          have hW_eq : (⟨(W - 1) + 1, by omega⟩ : Fin (W + 1)) = ⟨W, Nat.lt_succ_self W⟩ := Fin.ext (by dsimp only; omega)
          rwa [hW_eq] at this
        rw [← hW1] at hx
        exact harc _ (.bridge k) rfl rfl (by unfold pairArc; rw [decide_eq_true_eq, pairArc_iff_in]; simp [pairIn, W]) hx
      · intro hb; rw [← hinit_eq true k]
        exact harc (.bridge k) (.initReg true k) rfl rfl (by simp [pairArc, pairOut]) hb
      · by_cases htb : tbl s w = false
        · rw [if_pos htb]
          have honD : ∀ k, on (.detD s w k) = true := fun k => by rw [hon_detD, htb]; rfl
          have honQ : ∀ k, on (.detQ s w k) = true := fun k => by rw [hon_detQ, htb]; rfl
          have honU : ∀ k c, on (.detU s w k c) = true := fun k c => by rw [hon_detU, htb]; rfl
          have honF : ∀ c, on (.detF s w c) = true := fun c => by rw [hon_detF, htb]; rfl
          refine ⟨funext fun j => funext fun b => hoff _ (by rw [hon_padT, htb]), ?_, ?_, ?_, ?_⟩
          · intro k
            refine ⟨fun h => harc (.detD s w k.castSucc) (.detQ s w k) (honD _) (honQ _) (by unfold pairArc; rw [decide_eq_true_eq, pairArc_iff_in]; simp [pairIn]) h,
              fun h => harc (.detQ s w k) (.detD s w k.succ) (honQ _) (honD _) (by simp [pairArc, pairOut]) h⟩
          · intro k
            by_cases hwk : wordOf n w k = true
            · rw [if_pos hwk]
              refine ⟨fun hx => ?_, fun hd => ?_, fun hu1 => ?_, fun hu1 => ?_⟩
              · rw [← hprev_eq s w k] at hx
                exact harc _ (.detU s w k ⟨0, by decide⟩) (by unfold prevReg; split_ifs <;> rfl) (honU _ _)
                  (by unfold pairArc; rw [decide_eq_true_eq, pairArc_iff_in]; simp [pairIn, hwk, n]) hx
              · exact harc (.detD s w k) (.detU s w k ⟨0, by decide⟩) (honD _) (honU _ _)
                  (by unfold pairArc; rw [decide_eq_true_eq, pairArc_iff_in]; simp [pairIn, hwk, n]) hd
              · exact harc (.detU s w k ⟨1, by decide⟩) (.detU s w k ⟨2, by decide⟩) (honU _ _) (honU _ _)
                  (by simp [pairArc, pairOut, hwk, n]) hu1
              · exact harc (.detU s w k ⟨1, by decide⟩) (.detU s w k ⟨3, by decide⟩) (honU _ _) (honU _ _)
                  (by simp [pairArc, pairOut, hwk, n]) hu1
            · rw [if_neg hwk]
              have hwkf : wordOf n w k = false := Bool.eq_false_iff.mpr hwk
              refine ⟨fun hx => ?_, fun hu0 => ?_, fun hu2 => ?_⟩
              · rw [← hprev_eq s w k] at hx
                exact harc _ (.detD s w k) (by unfold prevReg; split_ifs <;> rfl) (honD _)
                  (by unfold pairArc; rw [decide_eq_true_eq, pairArc_iff_in]; simp [pairIn, hwkf, n]) hx
              · exact harc (.detU s w k ⟨0, by decide⟩) (.detU s w k ⟨1, by decide⟩) (honU _ _) (honU _ _)
                  (by simp [pairArc, pairOut, hwkf, n]) hu0
              · exact harc (.detU s w k ⟨2, by decide⟩) (.detU s w k ⟨3, by decide⟩) (honU _ _) (honU _ _)
                  (by simp [pairArc, pairOut, hwkf, n]) hu2
          · exact harc (.detF s w ⟨0, by decide⟩) (.detF s w ⟨1, by decide⟩) (honF _) (honF _) (by simp [pairArc, pairOut])
          · exact harc (.detF s w ⟨0, by decide⟩) (.detF s w ⟨2, by decide⟩) (honF _) (honF _) (by simp [pairArc, pairOut])
        · rw [if_neg htb]
          have htbt : tbl s w = true := Bool.eq_true_of_not_eq_false htb
          refine ⟨funext fun k => hoff _ (by rw [hon_detD, htbt]; rfl),
            funext fun k => hoff _ (by rw [hon_detQ, htbt]; rfl),
            funext fun k => funext fun c => hoff _ (by rw [hon_detU, htbt]; rfl),
            funext fun c => hoff _ (by rw [hon_detF, htbt]; rfl),
            fun j h => harc (.padT s w j false) (.padT s w j true) (by rw [hon_padT, htbt]) (by rw [hon_padT, htbt]) (by simp [pairArc, pairOut]) h⟩
    · intro a1 h1 a2 h2 heq
      have hr1 := (Finset.mem_filter.mp h1).2; have hr2 := (Finset.mem_filter.mp h2).2
      funext u
      cases u with
      | initReg s k =>
        have e1 := congrFun (congrFun hr1 (s, ⟨0, Nat.succ_pos _⟩)) k
        have e2 := congrFun (congrFun hr2 (s, ⟨0, Nat.succ_pos _⟩)) k
        simpa [regOf] using e1.trans e2.symm
      | bridge k => exact congrFun (congrArg (fun p => p.1.2) heq) k
      | regP s w k => exact congrFun (congrArg (fun p => p.1.1) heq) (s, w, k)
      | regX s w k =>
        have e1 := congrFun (congrFun hr1 (s, ⟨w.val + 1, by omega⟩)) k
        have e2 := congrFun (congrFun hr2 (s, ⟨w.val + 1, by omega⟩)) k
        simpa [regOf] using e1.trans e2.symm
      | detD s w k => exact congrFun (congrArg (fun p => (p.2 (s, w)).1.1) heq) k
      | detQ s w k => exact congrFun (congrArg (fun p => (p.2 (s, w)).1.2.1) heq) k
      | detU s w k c => exact congrFun (congrFun (congrArg (fun p => (p.2 (s, w)).1.2.2.1) heq) k) c
      | detF s w c => exact congrFun (congrArg (fun p => (p.2 (s, w)).1.2.2.2) heq) c
      | padT s w j b => exact congrFun (congrFun (congrArg (fun p => (p.2 (s, w)).2) heq) j) b
    · rintro ⟨⟨rp, br⟩, det⟩ hmem
      simp only [Finset.mem_product, RP, BR, DET, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      rcases hmem with ⟨⟨hrp, hbr⟩, hdet⟩
      let a : PairV t → Bool := fun
        | .initReg s k => X (s, ⟨0, Nat.succ_pos W⟩) k
        | .bridge k => br k
        | .regP s w k => rp (s, w, k)
        | .regX s w k => X (s, ⟨w.val + 1, by omega⟩) k
        | .detD s w k => (det (s, w)).1.1 k
        | .detQ s w k => (det (s, w)).1.2.1 k
        | .detU s w k c => (det (s, w)).1.2.2.1 k c
        | .detF s w c => (det (s, w)).1.2.2.2 c
        | .padT s w j b => (det (s, w)).2 j b
      refine ⟨a, ?_, ?_⟩
      · simp only [Mono, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro u hu
          cases u with
          | initReg s k => simp [hon_init] at hu
          | bridge k => simp [hon_bridge] at hu
          | regP s w k => simp [hon_regP] at hu
          | regX s w k => simp [hon_regX] at hu
          | detD s w k =>
            have ht : tbl s w = true := by rw [hon_detD] at hu; cases h : tbl s w <;> simp [h] at hu ⊢
            have hd := hdet (s, w); rw [if_neg (by simp [ht])] at hd; exact congrFun hd.1 k
          | detQ s w k =>
            have ht : tbl s w = true := by rw [hon_detQ] at hu; cases h : tbl s w <;> simp [h] at hu ⊢
            have hd := hdet (s, w); rw [if_neg (by simp [ht])] at hd; exact congrFun hd.2.1 k
          | detU s w k c =>
            have ht : tbl s w = true := by rw [hon_detU] at hu; cases h : tbl s w <;> simp [h] at hu ⊢
            have hd := hdet (s, w); rw [if_neg (by simp [ht])] at hd; exact congrFun (congrFun hd.2.2.1 k) c
          | detF s w c =>
            have ht : tbl s w = true := by rw [hon_detF] at hu; cases h : tbl s w <;> simp [h] at hu ⊢
            have hd := hdet (s, w); rw [if_neg (by simp [ht])] at hd; exact congrFun hd.2.2.2.1 c
          | padT s w j b =>
            have hf : tbl s w = false := by rw [hon_padT] at hu; exact hu
            have hd := hdet (s, w); rw [if_pos hf] at hd; exact congrFun (congrFun hd.1 j) b
        · intro u v hu hv huv hau
          unfold pairArc at huv; rw [decide_eq_true_eq] at huv
          cases u with
          | initReg s k =>
            simp only [pairOut, Finset.mem_insert, Finset.mem_singleton] at huv
            rcases huv with rfl | huv
            · exact (hrp (s, ⟨0, Nat.two_pow_pos _⟩, k)).1 hau
            · split_ifs at huv with hwk
              · subst huv
                let w0 : Fin W := ⟨0, Nat.two_pow_pos _⟩
                have hf : tbl s w0 = false := by
                  have hv' : !(tbl s w0) = true := (hon_detU s w0 k ⟨0, by decide⟩).symm.trans hv
                  cases h : tbl s w0 <;> simp [h] at hv' ⊢
                have hd := hdet (s, w0); rw [if_pos hf] at hd
                have hdk := hd.2.2.1 k; rw [if_pos hwk] at hdk; exact hdk.1 hau
              · subst huv
                let w0 : Fin W := ⟨0, Nat.two_pow_pos _⟩
                have hf : tbl s w0 = false := by
                  have hv' : !(tbl s w0) = true := (hon_detD s w0 k).symm.trans hv
                  cases h : tbl s w0 <;> simp [h] at hv' ⊢
                have hd := hdet (s, ⟨0, Nat.two_pow_pos _⟩); rw [if_pos hf] at hd
                have hdk := hd.2.2.1 k; rw [if_neg hwk] at hdk; exact hdk.1 hau
          | bridge k =>
            simp only [pairOut, Finset.mem_singleton] at huv; subst huv; exact (hbr k).2 hau
          | regP s w k =>
            simp only [pairOut, Finset.mem_singleton] at huv; subst huv; exact (hrp (s, w, k)).2 hau
          | regX s w k =>
            simp only [pairOut] at huv
            by_cases h1 : w.val + 1 < 2 ^ (t + 1)
            · rw [dif_pos h1] at huv; simp only [Finset.mem_insert, Finset.mem_singleton] at huv
              rcases huv with rfl | huv
              · exact (hrp (s, ⟨w.val + 1, h1⟩, k)).1 hau
              · split_ifs at huv with hwk
                · subst huv
                  have hf : tbl s ⟨w.val + 1, h1⟩ = false := by
                    rw [hon_detU] at hv; cases h : tbl s ⟨w.val + 1, h1⟩ <;> simp [h] at hv ⊢
                  have hd := hdet (s, ⟨w.val + 1, h1⟩); rw [if_pos hf] at hd
                  have hdk := hd.2.2.1 k; rw [if_pos hwk] at hdk; exact hdk.1 hau
                · subst huv
                  have hf : tbl s ⟨w.val + 1, h1⟩ = false := by
                    rw [hon_detD] at hv; cases h : tbl s ⟨w.val + 1, h1⟩ <;> simp [h] at hv ⊢
                  have hd := hdet (s, ⟨w.val + 1, h1⟩); rw [if_pos hf] at hd
                  have hdk := hd.2.2.1 k; rw [if_neg hwk] at hdk; exact hdk.1 hau
            · rw [dif_neg h1] at huv
              by_cases h2 : s = false
              · rw [if_pos h2, Finset.mem_singleton] at huv; subst huv; subst h2
                have hWeq : (⟨w.val + 1, by omega⟩ : Fin (W + 1)) = ⟨W, Nat.lt_succ_self W⟩ := Fin.ext (by dsimp only; have := w.isLt; omega)
                dsimp only [a] at hau; rw [hWeq] at hau; exact (hbr k).1 hau
              · rw [if_neg h2] at huv; simp at huv
          | detD s w k =>
            have hf : tbl s w = false := by rw [hon_detD] at hu; cases h : tbl s w <;> simp [h] at hu ⊢
            have hd := hdet (s, w); rw [if_pos hf] at hd
            simp only [pairOut, Finset.mem_union] at huv
            rcases huv with h | h
            · split_ifs at h with hk
              · rw [Finset.mem_singleton] at h; subst h; exact (hd.2.1 ⟨k.val, hk⟩).1 hau
              · simp at h
            · split_ifs at h with hwk
              · rw [Finset.mem_singleton] at h; subst h
                have hdk := hd.2.2.1 k; rw [if_pos hwk] at hdk; exact hdk.2.1 hau
              · simp at h
          | detQ s w k =>
            have hf : tbl s w = false := by rw [hon_detQ] at hu; cases h : tbl s w <;> simp [h] at hu ⊢
            have hd := hdet (s, w); rw [if_pos hf] at hd
            simp only [pairOut, Finset.mem_singleton] at huv; subst huv; exact (hd.2.1 k).2 hau
          | detU s w k c =>
            have hf : tbl s w = false := by rw [hon_detU] at hu; cases h : tbl s w <;> simp [h] at hu ⊢
            have hd := hdet (s, w); rw [if_pos hf] at hd
            have hdk := hd.2.2.1 k
            simp only [pairOut] at huv; split_ifs at huv with hwk hc1 hc0 hc2
            · rw [if_pos hwk] at hdk
              have hc : c = ⟨1, by decide⟩ := Fin.ext hc1; subst hc
              rcases Finset.mem_insert.mp huv with rfl | h
              · exact hdk.2.2.1 hau
              · rw [Finset.mem_singleton] at h; subst h; exact hdk.2.2.2 hau
            · simp at huv
            · rw [if_neg hwk] at hdk
              have hc : c = ⟨0, by decide⟩ := Fin.ext hc0; subst hc
              rw [Finset.mem_singleton] at huv; subst huv; exact hdk.2.1 hau
            · rw [if_neg hwk] at hdk
              have hc : c = ⟨2, by decide⟩ := Fin.ext hc2; subst hc
              rw [Finset.mem_singleton] at huv; subst huv; exact hdk.2.2 hau
            · simp at huv
          | detF s w c =>
            have hf : tbl s w = false := by rw [hon_detF] at hu; cases h : tbl s w <;> simp [h] at hu ⊢
            have hd := hdet (s, w); rw [if_pos hf] at hd
            simp only [pairOut] at huv; split_ifs at huv with hc0
            · have hc : c = ⟨0, by decide⟩ := Fin.ext hc0; subst hc
              rcases Finset.mem_insert.mp huv with rfl | h
              · exact hd.2.2.2.1 hau
              · rw [Finset.mem_singleton] at h; subst h; exact hd.2.2.2.2 hau
            · simp at huv
          | padT s w j b =>
            have ht : tbl s w = true := by rw [hon_padT] at hu; exact hu
            have hd := hdet (s, w); rw [if_neg (by simp [ht])] at hd
            simp only [pairOut] at huv; split_ifs at huv with hb
            · subst hb; rw [Finset.mem_singleton] at huv; subst huv; exact hd.2.2.2.2 j hau
            · simp at huv
        · funext ⟨s, idx⟩ k; dsimp only [regOf]; split_ifs with h0
          · have : idx = ⟨0, Nat.succ_pos W⟩ := Fin.ext h0; subst this; rfl
          · dsimp only [a]; congr 2; exact Fin.ext (by dsimp only; omega)
      · apply Prod.ext
        · apply Prod.ext <;> funext _ <;> rfl
        · funext sw; rfl
  have hconst_check : ∀ X : RegProf,
      ((∏ s : Bool, ∏ w : Fin W, ∏ k : Fin n, transW (X (s, ⟨w.val, by omega⟩) k) (X (s, ⟨w.val + 1, by omega⟩) k)) *
       (∏ k : Fin n, transW (X (false, ⟨W, Nat.lt_succ_self W⟩) k) (X (true, ⟨0, Nat.succ_pos W⟩) k))) % 2 =
      if (∀ s idx k, X (s, idx) k = X (false, ⟨0, Nat.succ_pos W⟩) k) then 1 else 0 := by
    intro X
    have htw_mod : ∀ a b, transW a b % 2 = if a = b then 1 else 0 := by
      intro a b; cases a <;> cases b <;> decide
    have hprod_eq : ∀ {α : Type} (S : Finset α) (F : α → ℕ) (P : α → Prop),
        (∀ x ∈ S, F x % 2 = if P x then 1 else 0) →
        (∏ x ∈ S, F x) % 2 = if ∀ x ∈ S, P x then 1 else 0 := by
      intro α S F P
      refine Finset.induction_on S (by intro _; simp) fun a s ha ih hF => ?_
      rw [Finset.prod_insert ha, Nat.mul_mod, hF a (Finset.mem_insert_self _ _),
        ih (fun x hx => hF x (Finset.mem_insert_of_mem hx))]
      by_cases hPa : P a <;> by_cases hPs : ∀ x ∈ s, P x
      · rw [if_pos hPa, if_pos hPs, if_pos (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx'; exact hPa; exact hPs x hx')]
      · rw [if_pos hPa, if_neg hPs, if_neg (by intro h; exact hPs fun x hx => h x (Finset.mem_insert_of_mem hx))]
      · rw [if_neg hPa, if_pos hPs, if_neg (by intro h; exact hPa (h a (Finset.mem_insert_self _ _)))]
      · rw [if_neg hPa, if_neg hPs, if_neg (by intro h; exact hPa (h a (Finset.mem_insert_self _ _)))]
    have h1 : (∏ s : Bool, ∏ w : Fin W, ∏ k : Fin n, transW (X (s, ⟨w.val, by omega⟩) k) (X (s, ⟨w.val + 1, by omega⟩) k)) % 2 =
        if ∀ (s : Bool) (w : Fin W) (k : Fin n), X (s, ⟨w.val, by omega⟩) k = X (s, ⟨w.val + 1, by omega⟩) k then 1 else 0 := by
      rw [hprod_eq _ _ (fun s => ∀ w : Fin W, ∀ k : Fin n, X (s, ⟨w.val, by omega⟩) k = X (s, ⟨w.val + 1, by omega⟩) k)]
      · congr 1; exact propext ⟨fun h s w k => h s (Finset.mem_univ _) w k, fun h s _ w k => h s w k⟩
      · intro s _
        rw [hprod_eq _ _ (fun w : Fin W => ∀ k : Fin n, X (s, ⟨w.val, by omega⟩) k = X (s, ⟨w.val + 1, by omega⟩) k)]
        · congr 1; exact propext ⟨fun h w k => h w (Finset.mem_univ _) k, fun h w _ k => h w k⟩
        · intro w _
          rw [hprod_eq _ _ (fun k : Fin n => X (s, ⟨w.val, by omega⟩) k = X (s, ⟨w.val + 1, by omega⟩) k)]
          · congr 1; exact propext ⟨fun h k => h k (Finset.mem_univ _), fun h k _ => h k⟩
          · intro k _; rw [htw_mod]; split_ifs <;> rfl
    have h2 : (∏ k : Fin n, transW (X (false, ⟨W, Nat.lt_succ_self W⟩) k) (X (true, ⟨0, Nat.succ_pos W⟩) k)) % 2 =
        if ∀ k : Fin n, X (false, ⟨W, Nat.lt_succ_self W⟩) k = X (true, ⟨0, Nat.succ_pos W⟩) k then 1 else 0 := by
      rw [hprod_eq _ _ (fun k : Fin n => X (false, ⟨W, Nat.lt_succ_self W⟩) k = X (true, ⟨0, Nat.succ_pos W⟩) k)]
      · congr 1; exact propext ⟨fun h k => h k (Finset.mem_univ _), fun h k _ => h k⟩
      · intro k _; rw [htw_mod]; split_ifs <;> rfl
    rw [Nat.mul_mod, h1, h2]
    have hiff : ((∀ s (w : Fin W) (k : Fin n), X (s, ⟨w.val, by omega⟩) k = X (s, ⟨w.val + 1, by omega⟩) k) ∧
        ∀ k : Fin n, X (false, ⟨W, Nat.lt_succ_self W⟩) k = X (true, ⟨0, Nat.succ_pos W⟩) k) ↔
        ∀ s idx k, X (s, idx) k = X (false, ⟨0, Nat.succ_pos W⟩) k := by
      constructor
      · rintro ⟨hstep, hbr⟩ s idx k
        have hstep_all : ∀ s' (j : ℕ) (hj : j ≤ W), X (s', ⟨j, by omega⟩) k = X (s', ⟨0, Nat.succ_pos W⟩) k := by
          intro s' j
          induction j with
          | zero => intro _; rfl
          | succ j ih =>
            intro hj
            have h1' := hstep s' ⟨j, by omega⟩ k
            exact h1'.symm.trans (ih (by omega))
        have hbase := hstep_all s idx.val (by omega)
        have hidx : (⟨idx.val, by omega⟩ : Fin (W + 1)) = idx := Fin.ext rfl
        rw [hidx] at hbase
        cases s
        · exact hbase
        · rw [hbase, ← hbr k, hstep_all false W le_rfl]
      · intro hall
        exact ⟨fun s w k => (hall s _ k).trans (hall s _ k).symm, fun k => (hall false _ k).trans (hall true _ k).symm⟩
    by_cases hA : ∀ s (w : Fin W) (k : Fin n), X (s, ⟨w.val, by omega⟩) k = X (s, ⟨w.val + 1, by omega⟩) k
    · by_cases hB : ∀ k : Fin n, X (false, ⟨W, Nat.lt_succ_self W⟩) k = X (true, ⟨0, Nat.succ_pos W⟩) k
      · rw [if_pos hA, if_pos hB, if_pos (hiff.mp ⟨hA, hB⟩)]
      · rw [if_pos hA, if_neg hB, if_neg (fun h => hB (hiff.mpr h).2)]
    · rw [if_neg hA, if_neg (fun h => hA (hiff.mpr h).1)]; simp
  have hdet_mod : ∀ (x : Fin n → Bool) (s : Bool) (w : Fin W),
      detBlock (fun _ => x) s w % 2 =
      if tbl s w = false ∧ x = wordOf n w then 0 else 1 := by
    intro x s w
    dsimp only [detBlock]
    by_cases htb : tbl s w = false
    · rw [if_pos htb]
      let Sfull := (Finset.univ : Finset ((Fin n → Bool) × (Fin t → Bool) × (Fin n → Fin 4 → Bool) × (Fin 3 → Bool))).filter (fun p =>
        let D := p.1; let Q := p.2.1; let U := p.2.2.1; let F := p.2.2.2
        (∀ k : Fin t, (D k.castSucc = true → Q k = true) ∧ (Q k = true → D k.succ = true)) ∧
        (∀ k : Fin n,
          if wordOf n w k then
            (x k = true → U k ⟨0, by decide⟩ = true) ∧
            (D k = true → U k ⟨0, by decide⟩ = true) ∧
            (U k ⟨1, by decide⟩ = true → U k ⟨2, by decide⟩ = true) ∧
            (U k ⟨1, by decide⟩ = true → U k ⟨3, by decide⟩ = true)
          else
            (x k = true → D k = true) ∧
            (U k ⟨0, by decide⟩ = true → U k ⟨1, by decide⟩ = true) ∧
            (U k ⟨2, by decide⟩ = true → U k ⟨3, by decide⟩ = true)) ∧
        (F ⟨0, by decide⟩ = true → F ⟨1, by decide⟩ = true) ∧
        (F ⟨0, by decide⟩ = true → F ⟨2, by decide⟩ = true))
      have hpartD : Sfull.card = ∑ D : Fin n → Bool, (Sfull.filter (fun p => p.1 = D)).card := by
        rw [← Finset.card_biUnion]
        · congr 1; ext p; simp
        · intro D1 _ D2 _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro p h1 h2
          exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
      have hfibD : ∀ D : Fin n → Bool,
          (Sfull.filter (fun p => p.1 = D)).card % 2 =
          if (∀ k : Fin n, D k = D ⟨0, Nat.succ_pos t⟩) ∧
             (D ⟨0, Nat.succ_pos t⟩ = true ∨ x = wordOf n w) then 1 else 0 := by
        intro D
        let SQ := Fintype.piFinset fun k : Fin t =>
          (Finset.univ : Finset Bool).filter (fun q => (D k.castSucc = true → q = true) ∧ (q = true → D k.succ = true))
        let SU := Fintype.piFinset fun k : Fin n =>
          (Finset.univ : Finset (Fin 4 → Bool)).filter (fun u =>
            if wordOf n w k then
              (x k = true → u ⟨0, by decide⟩ = true) ∧ (D k = true → u ⟨0, by decide⟩ = true) ∧
              (u ⟨1, by decide⟩ = true → u ⟨2, by decide⟩ = true) ∧ (u ⟨1, by decide⟩ = true → u ⟨3, by decide⟩ = true)
            else
              (x k = true → D k = true) ∧
              (u ⟨0, by decide⟩ = true → u ⟨1, by decide⟩ = true) ∧ (u ⟨2, by decide⟩ = true → u ⟨3, by decide⟩ = true))
        let SF := (Finset.univ : Finset (Fin 3 → Bool)).filter (fun F =>
          (F ⟨0, by decide⟩ = true → F ⟨1, by decide⟩ = true) ∧ (F ⟨0, by decide⟩ = true → F ⟨2, by decide⟩ = true))
        have hbij : (Sfull.filter (fun p => p.1 = D)).card = SQ.card * SU.card * SF.card := by
          rw [← Finset.card_product, ← Finset.card_product]
          refine Finset.card_bij (fun p _ => ((p.2.1, p.2.2.1), p.2.2.2)) ?_ ?_ ?_
          · intro p hp
            simp only [Sfull, Finset.mem_filter, Finset.mem_univ, true_and] at hp
            rcases hp with ⟨⟨h1, h2, h3, h4⟩, rfl⟩
            simp only [Finset.mem_product, SQ, SU, SF, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨⟨h1, h2⟩, h3, h4⟩
          · intro p1 h1 p2 h2 heq
            have e1 := (Finset.mem_filter.mp h1).2; have e2 := (Finset.mem_filter.mp h2).2
            exact Prod.ext (e1.trans e2.symm)
              (Prod.ext (congrArg (fun q => q.1.1) heq) (Prod.ext (congrArg (fun q => q.1.2) heq) (congrArg (fun q => q.2) heq)))
          · rintro ⟨⟨Q, U⟩, F⟩ hmem
            simp only [Finset.mem_product, SQ, SU, SF, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
            exact ⟨(D, Q, U, F), by simp only [Sfull, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨⟨hmem.1.1, hmem.1.2, hmem.2.1, hmem.2.2⟩, trivial⟩, rfl⟩
        rw [hbij]
        have hSF : SF.card % 2 = 1 := fork3_card_mod2
        have hprod_eq : ∀ {α : Type} (S : Finset α) (F : α → ℕ) (P : α → Prop),
            (∀ a ∈ S, F a % 2 = if P a then 1 else 0) →
            (∏ a ∈ S, F a) % 2 = if ∀ a ∈ S, P a then 1 else 0 := by
          intro α S F P
          refine Finset.induction_on S (by intro _; simp) fun a s ha ih hF => ?_
          rw [Finset.prod_insert ha, Nat.mul_mod, hF a (Finset.mem_insert_self _ _),
            ih (fun b hb => hF b (Finset.mem_insert_of_mem hb))]
          by_cases hPa : P a <;> by_cases hPs : ∀ b ∈ s, P b
          · rw [if_pos hPa, if_pos hPs, if_pos (by intro b hb; rcases Finset.mem_insert.mp hb with rfl | hb'; exact hPa; exact hPs b hb')]
          · rw [if_pos hPa, if_neg hPs, if_neg (by intro h; exact hPs fun b hb => h b (Finset.mem_insert_of_mem hb))]
          · rw [if_neg hPa, if_pos hPs, if_neg (by intro h; exact hPa (h a (Finset.mem_insert_self _ _)))]
          · rw [if_neg hPa, if_neg hPs, if_neg (by intro h; exact hPa (h a (Finset.mem_insert_self _ _)))]
        have hSQ : SQ.card % 2 = if ∀ k : Fin t, D k.castSucc = D k.succ then 1 else 0 := by
          rw [Fintype.card_piFinset, hprod_eq _ _ (fun k : Fin t => D k.castSucc = D k.succ)]
          · congr 1; exact propext ⟨fun h k => h k (Finset.mem_univ _), fun h k _ => h k⟩
          · intro k _; rw [detQ_card_mod2]; split_ifs <;> rfl
        have hSU : SU.card % 2 = if ∀ k : Fin n, D k = true ∨ x k = wordOf n w k then 1 else 0 := by
          rw [Fintype.card_piFinset, hprod_eq _ _ (fun k : Fin n => D k = true ∨ x k = wordOf n w k)]
          · congr 1; exact propext ⟨fun h k => h k (Finset.mem_univ _), fun h k _ => h k⟩
          · intro k _; rw [detU_card_mod2]; split_ifs <;> rfl
        rw [Nat.mul_mod (SQ.card * SU.card), Nat.mul_mod SQ.card, hSQ, hSU, hSF]
        have hiff : ((∀ k : Fin t, D k.castSucc = D k.succ) ∧ (∀ k : Fin n, D k = true ∨ x k = wordOf n w k)) ↔
            ((∀ k : Fin n, D k = D ⟨0, Nat.succ_pos t⟩) ∧ (D ⟨0, Nat.succ_pos t⟩ = true ∨ x = wordOf n w)) := by
          constructor
          · rintro ⟨hD, hU⟩
            have hconst : ∀ (j : ℕ) (hj : j < n), D ⟨j, hj⟩ = D ⟨0, Nat.succ_pos t⟩ := by
              intro j; induction j with
              | zero => intro _; rfl
              | succ j ih => intro hj; exact (hD ⟨j, by omega⟩).symm.trans (ih (by omega))
            have hall : ∀ k : Fin n, D k = D ⟨0, Nat.succ_pos t⟩ := fun k => hconst k.val k.isLt
            refine ⟨hall, ?_⟩
            cases h0 : D ⟨0, Nat.succ_pos t⟩
            · right; funext k; have := hU k; rw [hall k, h0] at this; exact this.resolve_left (by decide)
            · left; rfl
          · rintro ⟨hall, hok⟩
            refine ⟨fun k => (hall k.castSucc).trans (hall k.succ).symm, fun k => ?_⟩
            rcases hok with h0 | hxw
            · left; rw [hall k, h0]
            · right; rw [hxw]
        by_cases h1 : ∀ k : Fin t, D k.castSucc = D k.succ
        · by_cases h2 : ∀ k : Fin n, D k = true ∨ x k = wordOf n w k
          · rw [if_pos h1, if_pos h2, if_pos (hiff.mp ⟨h1, h2⟩)]
          · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 (hiff.mpr h).2)]
        · rw [if_neg h1, if_neg (fun h => h1 (hiff.mpr h).1)]; simp
      have hsum_mod : Sfull.card % 2 =
          (∑ D : Fin n → Bool, if (∀ k : Fin n, D k = D ⟨0, Nat.succ_pos t⟩) ∧
            (D ⟨0, Nat.succ_pos t⟩ = true ∨ x = wordOf n w) then 1 else 0) % 2 := by
        rw [hpartD]
        have hMod : ∀ (S : Finset (Fin n → Bool)),
            (∑ D ∈ S, (Sfull.filter (fun p => p.1 = D)).card) ≡
            ∑ D ∈ S, (if (∀ k : Fin n, D k = D ⟨0, Nat.succ_pos t⟩) ∧
              (D ⟨0, Nat.succ_pos t⟩ = true ∨ x = wordOf n w) then 1 else 0) [MOD 2] := by
          intro S; refine Finset.induction_on S (by simp only [Finset.sum_empty]; rfl) fun D s hD ih => ?_
          rw [Finset.sum_insert hD, Finset.sum_insert hD]
          have hm1 : (Sfull.filter (fun p => p.1 = D)).card ≡
              (if (∀ k : Fin n, D k = D ⟨0, Nat.succ_pos t⟩) ∧
                (D ⟨0, Nat.succ_pos t⟩ = true ∨ x = wordOf n w) then 1 else 0) [MOD 2] := by
            change _ % 2 = _ % 2; rw [hfibD D]; split_ifs <;> decide
          exact hm1.add ih
        exact hMod Finset.univ
      rw [hsum_mod]
      let DT : Fin n → Bool := fun _ => true
      let DF : Fin n → Bool := fun _ => false
      have hneTF : DT ≠ DF := fun h => by have := congrFun h ⟨0, Nat.succ_pos t⟩; simp [DT, DF] at this
      have hsum_eq : (∑ D : Fin n → Bool, if (∀ k : Fin n, D k = D ⟨0, Nat.succ_pos t⟩) ∧
            (D ⟨0, Nat.succ_pos t⟩ = true ∨ x = wordOf n w) then 1 else 0) =
          1 + (if x = wordOf n w then 1 else 0) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ DT),
            ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hneTF.symm, Finset.mem_univ DF⟩)]
        have hrest : ∑ D ∈ (Finset.univ.erase DT).erase DF,
            (if (∀ k : Fin n, D k = D ⟨0, Nat.succ_pos t⟩) ∧ (D ⟨0, Nat.succ_pos t⟩ = true ∨ x = wordOf n w) then 1 else 0) = 0 :=
          Finset.sum_eq_zero fun D hD => by
            have hneF : D ≠ DF := (Finset.mem_erase.mp hD).1
            have hneT : D ≠ DT := (Finset.mem_erase.mp (Finset.mem_erase.mp hD).2).1
            rw [if_neg]; rintro ⟨hall, _⟩
            cases h0 : D ⟨0, Nat.succ_pos t⟩
            · exact hneF (funext fun k => (hall k).trans h0)
            · exact hneT (funext fun k => (hall k).trans h0)
        rw [hrest, add_zero]
        have hT : (if (∀ k : Fin n, DT k = DT ⟨0, Nat.succ_pos t⟩) ∧ (DT ⟨0, Nat.succ_pos t⟩ = true ∨ x = wordOf n w) then 1 else 0) = 1 := by
          rw [if_pos ⟨fun _ => rfl, Or.inl rfl⟩]
        have hF : (if (∀ k : Fin n, DF k = DF ⟨0, Nat.succ_pos t⟩) ∧ (DF ⟨0, Nat.succ_pos t⟩ = true ∨ x = wordOf n w) then 1 else 0) =
            if x = wordOf n w then 1 else 0 := by
          by_cases hx : x = wordOf n w
          · rw [if_pos ⟨fun _ => rfl, Or.inr hx⟩, if_pos hx]
          · rw [if_neg (by rintro ⟨_, h | h⟩; simp [DF] at h; exact hx h), if_neg hx]
        rw [hT, hF]
      rw [hsum_eq]
      by_cases hx : x = wordOf n w
      · rw [if_pos hx, if_pos ⟨htb, hx⟩]
      · rw [if_neg hx, if_neg (by rintro ⟨_, h⟩; exact hx h)]
    · rw [if_neg htb, if_neg (by rintro ⟨h, _⟩; exact htb h)]
      have hcardP : ((Finset.univ : Finset (Fin (3 * n + 1) → Bool → Bool)).filter (fun P =>
          ∀ j, P j false = true → P j true = true)).card =
          (Fintype.piFinset fun _j : Fin (3 * n + 1) =>
            (Finset.univ : Finset (Bool → Bool)).filter (fun a => a false = true → a true = true)).card := by
        congr 1; ext P; simp [Fintype.mem_piFinset]
      rw [hcardP, Fintype.card_piFinset]
      have hprod1 : ∀ {α : Type} (S : Finset α) (F : α → ℕ), (∀ a ∈ S, F a % 2 = 1) → (∏ a ∈ S, F a) % 2 = 1 := by
        intro α S F
        refine Finset.induction_on S (by intro _; simp) fun a s ha ih hF => ?_
        rw [Finset.prod_insert ha, Nat.mul_mod, hF a (Finset.mem_insert_self _ _), ih (fun b hb => hF b (Finset.mem_insert_of_mem hb))]
      exact hprod1 _ _ fun _ _ => chain2_card_mod2
  have hterm_mod : ∀ X : RegProf, (Mono.filter (fun a => regOf a = X)).card % 2 =
      if (∀ s idx k, X (s, idx) k = X (false, ⟨0, Nat.succ_pos W⟩) k) ∧
         (f (X (false, ⟨0, Nat.succ_pos W⟩)) && g (X (false, ⟨0, Nat.succ_pos W⟩))) = true then 1 else 0 := by
    intro X
    rw [hfib_card X, Nat.mul_mod, hconst_check X]
    by_cases hconst : ∀ s idx k, X (s, idx) k = X (false, ⟨0, Nat.succ_pos W⟩) k
    · rw [if_pos hconst, one_mul, Nat.mod_mod]
      let x := X (false, ⟨0, Nat.succ_pos W⟩)
      have hX_eq : X = fun _ => x := funext fun ⟨s, idx⟩ => funext fun k => hconst s idx k
      rw [hX_eq]
      have hprod_eq : ∀ {α : Type} (S : Finset α) (F : α → ℕ) (P : α → Prop),
          (∀ a ∈ S, F a % 2 = if P a then 1 else 0) →
          (∏ a ∈ S, F a) % 2 = if ∀ a ∈ S, P a then 1 else 0 := by
        intro α S F P
        refine Finset.induction_on S (by intro _; simp) fun a s ha ih hF => ?_
        rw [Finset.prod_insert ha, Nat.mul_mod, hF a (Finset.mem_insert_self _ _),
          ih (fun b hb => hF b (Finset.mem_insert_of_mem hb))]
        by_cases hPa : P a <;> by_cases hPs : ∀ b ∈ s, P b
        · rw [if_pos hPa, if_pos hPs, if_pos (by intro b hb; rcases Finset.mem_insert.mp hb with rfl | hb'; exact hPa; exact hPs b hb')]
        · rw [if_pos hPa, if_neg hPs, if_neg (by intro h; exact hPs fun b hb => h b (Finset.mem_insert_of_mem hb))]
        · rw [if_neg hPa, if_pos hPs, if_neg (by intro h; exact hPa (h a (Finset.mem_insert_self _ _)))]
        · rw [if_neg hPa, if_neg hPs, if_neg (by intro h; exact hPa (h a (Finset.mem_insert_self _ _)))]
      have hhalf : ∀ s : Bool, (∏ w : Fin W, detBlock (fun _ => x) s w) % 2 =
          if (if s then g else f) x = true then 1 else 0 := by
        intro s
        rw [hprod_eq _ _ (fun w : Fin W => ¬ (tbl s w = false ∧ x = wordOf n w))]
        · have hiff : (∀ w ∈ (Finset.univ : Finset (Fin W)), ¬ (tbl s w = false ∧ x = wordOf n w)) ↔
              (if s then g else f) x = true := by
            constructor
            · intro h
              have := h (finOfWord n x) (Finset.mem_univ _)
              simp only [tbl, wordOf_finOfWord, and_true] at this
              exact Bool.eq_true_of_not_eq_false this
            · intro ht w _ ⟨hf, hxw⟩
              simp only [tbl, ← hxw] at hf; rw [ht] at hf; simp at hf
          by_cases hsx : (if s then g else f) x = true
          · rw [if_pos (hiff.mpr hsx), if_pos hsx]
          · rw [if_neg (fun h' => hsx (hiff.mp h')), if_neg hsx]
        · intro w _; rw [hdet_mod x s w]; by_cases h : tbl s w = false ∧ x = wordOf n w <;> simp [h]
      rw [Fintype.prod_bool, Nat.mul_mod, hhalf true, hhalf false]
      cases hf : f x <;> cases hg : g x <;> simp [hf, hg]
    · rw [if_neg hconst, if_neg (by rintro ⟨h, _⟩; exact hconst h)]; simp
  have hMono_mod : Mono.card % 2 =
      (∑ X : RegProf, if (∀ s idx k, X (s, idx) k = X (false, ⟨0, Nat.succ_pos W⟩) k) ∧
        (f (X (false, ⟨0, Nat.succ_pos W⟩)) && g (X (false, ⟨0, Nat.succ_pos W⟩))) = true then 1 else 0) % 2 := by
    rw [hpart]
    have hMod : ∀ S : Finset RegProf,
        (∑ X ∈ S, (Mono.filter (fun a => regOf a = X)).card) ≡
        ∑ X ∈ S, (if (∀ s idx k, X (s, idx) k = X (false, ⟨0, Nat.succ_pos W⟩) k) ∧
          (f (X (false, ⟨0, Nat.succ_pos W⟩)) && g (X (false, ⟨0, Nat.succ_pos W⟩))) = true then 1 else 0) [MOD 2] := by
      intro S; refine Finset.induction_on S (by simp only [Finset.sum_empty]; rfl) fun X s hX ih => ?_
      rw [Finset.sum_insert hX, Finset.sum_insert hX]
      have hm1 : (Mono.filter (fun a => regOf a = X)).card ≡
          (if (∀ s idx k, X (s, idx) k = X (false, ⟨0, Nat.succ_pos W⟩) k) ∧
            (f (X (false, ⟨0, Nat.succ_pos W⟩)) && g (X (false, ⟨0, Nat.succ_pos W⟩))) = true then 1 else 0) [MOD 2] := by
        change _ % 2 = _ % 2; rw [hterm_mod X]; split_ifs <;> decide
      exact hm1.add ih
    exact hMod Finset.univ
  rw [hMono_mod]
  congr 1
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  refine Finset.card_bij (fun X _ => X (false, ⟨0, Nat.succ_pos W⟩)) ?_ ?_ ?_
  · intro X hX; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hX ⊢; exact hX.2
  · intro X1 h1 X2 h2 heq
    have hc1 := (Finset.mem_filter.mp h1).2.1; have hc2 := (Finset.mem_filter.mp h2).2.1
    funext ⟨s, idx⟩ k; rw [hc1 s idx k, hc2 s idx k, heq]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact ⟨fun _ => y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ _ _ => rfl, hy⟩, rfl⟩


private lemma card_minCover_congr {V1 V2 : Type} [DecidableEq V1] [Fintype V1]
    [DecidableEq V2] [Fintype V2] (e : V1 ≃ V2)
    (arc : V1 → V1 → Bool) (hirr : ∀ u, arc u u = false)
    (G2 : (V2 × Bool) → Finset (V2 × Bool))
    (on1 : V1 → Bool) (on2 : V2 → Bool)
    (hG : ∀ u v, Equiv.prodCongr e (Equiv.refl Bool) v ∈ G2 (Equiv.prodCongr e (Equiv.refl Bool) u) ↔ v ∈ graphOfArcs arc u)
    (hon : ∀ u, on2 (e u) = on1 u) :
    let live2 := (Finset.univ : Finset (V2 × Bool)).filter (fun p => on2 p.1)
    let cov2 := fun (C : Finset (V2 × Bool)) => C ⊆ live2 ∧ ∀ p ∈ live2, ∀ r ∈ G2 p, r ∈ live2 → p ∈ C ∨ r ∈ C
    ((Finset.univ : Finset (Finset (V2 × Bool))).filter (fun C => cov2 C ∧ ∀ W, cov2 W → C.card ≤ W.card)).card =
    ((Finset.univ : Finset (V1 → Bool)).filter (fun a =>
      (∀ u, on1 u = false → a u = false) ∧
      ∀ u v, on1 u = true → on1 v = true → arc u v = true → a u = true → a v = true)).card := by
  intro live2 cov2
  let G1 := graphOfArcs arc
  let live1 := (Finset.univ : Finset (V1 × Bool)).filter (fun p => on1 p.1 = true)
  let cov1 := fun (C : Finset (V1 × Bool)) => C ⊆ live1 ∧ ∀ p ∈ live1, ∀ r ∈ G1 p, r ∈ live1 → p ∈ C ∨ r ∈ C
  let eB : (V1 × Bool) ≃ (V2 × Bool) := Equiv.prodCongr e (Equiv.refl Bool)
  have hinv_img : ∀ W : Finset (V1 × Bool), (W.image eB).image eB.symm = W := by
    intro W; ext x; simp only [Finset.mem_image]
    exact ⟨fun ⟨_, ⟨y, hy, rfl⟩, h⟩ => by rw [eB.symm_apply_apply] at h; rwa [← h],
           fun hx => ⟨eB x, ⟨x, hx, rfl⟩, eB.symm_apply_apply x⟩⟩
  have hcov_iff : ∀ C : Finset (V2 × Bool), cov2 C ↔ cov1 (C.image eB.symm) := by
    intro C; constructor
    · rintro ⟨hsub, hedge⟩
      refine ⟨?_, ?_⟩
      · intro p hp; rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
        have hql := (Finset.mem_filter.mp (hsub hq)).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← hon]; simpa [eB] using hql⟩
      · intro p hp r hr hrl
        have h1 : eB p ∈ live2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [eB, hon] using (Finset.mem_filter.mp hp).2⟩
        have h2 : eB r ∈ live2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [eB, hon] using (Finset.mem_filter.mp hrl).2⟩
        rcases hedge (eB p) h1 (eB r) ((hG p r).mpr hr) h2 with h | h
        · left; exact Finset.mem_image.mpr ⟨eB p, h, eB.symm_apply_apply p⟩
        · right; exact Finset.mem_image.mpr ⟨eB r, h, eB.symm_apply_apply r⟩
    · rintro ⟨hsub, hedge⟩
      refine ⟨?_, ?_⟩
      · intro q hq
        have h1 := (Finset.mem_filter.mp (hsub (Finset.mem_image.mpr ⟨q, hq, rfl⟩))).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← hon] at h1; simpa [eB] using h1⟩
      · intro q hq r hr hrl
        have h1 : eB.symm q ∈ live1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← hon]; simpa [eB] using (Finset.mem_filter.mp hq).2⟩
        have h2 : eB.symm r ∈ live1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← hon]; simpa [eB] using (Finset.mem_filter.mp hrl).2⟩
        have hr0 : eB.symm r ∈ G1 (eB.symm q) := (hG _ _).mp (by rwa [eB.apply_symm_apply, eB.apply_symm_apply])
        rcases hedge _ h1 _ hr0 h2 with h | h
        · left; rcases Finset.mem_image.mp h with ⟨a, ha, heq⟩; rwa [← eB.symm.injective heq]
        · right; rcases Finset.mem_image.mp h with ⟨a, ha, heq⟩; rwa [← eB.symm.injective heq]
  have h1 : ((Finset.univ : Finset (Finset (V2 × Bool))).filter (fun C => cov2 C ∧ ∀ W, cov2 W → C.card ≤ W.card)).card =
      ((Finset.univ : Finset (Finset (V1 × Bool))).filter (fun C => cov1 C ∧ ∀ W, cov1 W → C.card ≤ W.card)).card := by
    refine Finset.card_bij (fun C _ => C.image eB.symm) ?_ ?_ ?_
    · intro C hC
      rcases (Finset.mem_filter.mp hC).2 with ⟨hcov, hmin⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcov_iff C).mp hcov, fun W hW => ?_⟩
      have hW' : cov2 (W.image eB) := (hcov_iff _).mpr (by rwa [hinv_img W])
      have hle := hmin (W.image eB) hW'
      rw [Finset.card_image_of_injective _ eB.injective] at hle
      rw [Finset.card_image_of_injective _ eB.symm.injective]
      exact hle
    · intro C1 _ C2 _ heq; ext x
      have := Finset.ext_iff.mp heq (eB.symm x)
      simpa [Finset.mem_image] using this
    · intro C0 hC0
      rcases (Finset.mem_filter.mp hC0).2 with ⟨hcov0, hmin0⟩
      refine ⟨C0.image eB, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcov_iff _).mpr ((hinv_img C0).symm ▸ hcov0), fun W hW => ?_⟩, hinv_img C0⟩
      have hle := hmin0 (W.image eB.symm) ((hcov_iff W).mp hW)
      rw [Finset.card_image_of_injective _ eB.symm.injective] at hle
      rw [Finset.card_image_of_injective _ eB.injective]
      exact hle
  exact h1.trans (minCover_card_eq_mono arc hirr on1)

private lemma case_succ (t : ℕ) :
    let n := t + 1
    let Word := Fin n → Bool
    let Table := Word → Bool
    ∃ (m : Nat) (G : (Fin m × Bool) → Finset (Fin m × Bool))
      (side : Fin m → Bool) (tag : Fin m → Option (Word × Bool)) (keep : Bool → Nat),
      m ≤ 15000*(n+1)*2^n ∧ (∀ i, (i,true) ∈ G (i,false)) ∧
      (∀ p, p ∉ G p ∧ (G p).card ≤ 3) ∧ (∀ p r, r ∈ G p ↔ p ∈ G r) ∧
      (∀ p, ∀ r ∈ G p, p.2 ≠ r.2) ∧
      (∀ p, ((G p).filter (fun r => side r.1 ≠ side p.1)).card ≤ 1) ∧
      ((Finset.univ : Finset (Fin m × Bool)).filter (fun p =>
        side p.1 = false ∧ ∃ r ∈ G p, side r.1 = true)).card ≤ n ∧
      (∃ (l : Nat) (bag : Fin l → Finset (Fin m × Bool)),
        (∀ t', (bag t').card ≤ n+37) ∧ (∀ p, ∃ t', p ∈ bag t') ∧
        (∀ p r, r ∈ G p → ∃ t', p ∈ bag t' ∧ r ∈ bag t') ∧
        ∀ p s t' u, s ≤ t' → t' ≤ u → p ∈ bag s → p ∈ bag u → p ∈ bag t') ∧
      ∀ f g : Table,
        let on := fun i => (tag i).elim true (fun p => decide ((if side i then g else f) p.1 = p.2))
        let live := (Finset.univ : Finset (Fin m × Bool)).filter (fun p => on p.1)
        let cover := fun (C : Finset (Fin m × Bool)) => C ⊆ live ∧
          ∀ p ∈ live, ∀ r ∈ G p, r ∈ live → p ∈ C ∨ r ∈ C
        let opt := ((Finset.univ : Finset (Finset (Fin m × Bool))).filter
          (fun C => cover C ∧ ∀ W, cover W → C.card ≤ W.card)).card
        (∀ b, ((Finset.univ : Finset (Fin m)).filter (fun i => side i = b ∧ on i = true)).card = keep b) ∧
        opt % 2 = ((Finset.univ : Finset Word).filter (fun y => f y && g y)).card % 2 := by
  let n := t + 1
  let W := 2 ^ n
  let m := Fintype.card (PairV t)
  let eqP : PairV t ≃ Fin m := Fintype.equivFin (PairV t)
  let eqPB : (PairV t × Bool) ≃ (Fin m × Bool) := Equiv.prodCongr eqP (Equiv.refl Bool)
  let G0 := graphOfArcs (@pairArc t)
  let G : (Fin m × Bool) → Finset (Fin m × Bool) := fun p => (G0 (eqPB.symm p)).image eqPB
  let side : Fin m → Bool := fun i => pairSide (eqP.symm i)
  let tag : Fin m → Option ((Fin n → Bool) × Bool) := fun i => pairTag (eqP.symm i)
  let keep : Bool → Nat := fun b =>
    (if b then n else 2 * n) + 2 * n * W + (6 * n + 2) * W
  rcases graphOfArcs_props (@pairArc t) pairArc_irrefl pairArc_out_le pairArc_in_le with ⟨h0m, h0d, h0s, h0b⟩
  have hG_iff : ∀ u v : PairV t × Bool, eqPB v ∈ G (eqPB u) ↔ v ∈ G0 u := by
    intro u v; simp only [G, Finset.mem_image, eqPB.symm_apply_apply]
    exact ⟨fun ⟨w, hw, heq⟩ => eqPB.injective heq ▸ hw, fun hv => ⟨v, hv, rfl⟩⟩
  refine ⟨m, G, side, tag, keep, pairV_card_le t, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have := h0m (eqP.symm i)
    have h1 := (hG_iff (eqP.symm i, false) (eqP.symm i, true)).mpr this
    simpa [eqPB] using h1
  · intro p
    obtain ⟨u, rfl⟩ : ∃ u, eqPB u = p := ⟨eqPB.symm p, eqPB.apply_symm_apply p⟩
    refine ⟨fun h => (h0d u).1 ((hG_iff u u).mp h), ?_⟩
    exact Finset.card_image_le.trans (by rw [eqPB.symm_apply_apply]; exact (h0d u).2)
  · intro p r
    obtain ⟨u, rfl⟩ : ∃ u, eqPB u = p := ⟨eqPB.symm p, eqPB.apply_symm_apply p⟩
    obtain ⟨v, rfl⟩ : ∃ v, eqPB v = r := ⟨eqPB.symm r, eqPB.apply_symm_apply r⟩
    rw [hG_iff, hG_iff]; exact h0s u v
  · intro p r hr
    obtain ⟨u, rfl⟩ : ∃ u, eqPB u = p := ⟨eqPB.symm p, eqPB.apply_symm_apply p⟩
    obtain ⟨v, rfl⟩ : ∃ v, eqPB v = r := ⟨eqPB.symm r, eqPB.apply_symm_apply r⟩
    exact h0b u v ((hG_iff u v).mp hr)
  · intro p
    obtain ⟨⟨u, b⟩, rfl⟩ : ∃ q, eqPB q = p := ⟨eqPB.symm p, eqPB.apply_symm_apply p⟩
    have hsub : ((G (eqPB (u, b))).filter (fun r => side r.1 ≠ side (eqPB (u, b)).1)).card =
        ((G0 (u, b)).filter (fun r => pairSide r.1 ≠ pairSide u)).card := by
      refine Finset.card_bij (fun r _ => eqPB.symm r) ?_ ?_ ?_
      · intro r hr
        rcases Finset.mem_filter.mp hr with ⟨hrG, hne⟩
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · have : eqPB (eqPB.symm r) ∈ G (eqPB (u, b)) := by rwa [eqPB.apply_symm_apply]
          exact (hG_iff _ _).mp this
        · simpa [side, eqPB] using hne
      · intro r1 _ r2 _ h; exact eqPB.symm.injective h
      · intro q hq
        rcases Finset.mem_filter.mp hq with ⟨hqG, hne⟩
        exact ⟨eqPB q, Finset.mem_filter.mpr ⟨(hG_iff _ _).mpr hqG, by simpa [side, eqPB] using hne⟩, eqPB.symm_apply_apply q⟩
    rw [hsub]
    cases b
    · by_cases hu : ∃ k, u = .initReg true k
      · rcases hu with ⟨k, rfl⟩
        have hsub1 : (G0 (.initReg true k, false)).filter (fun r => pairSide r.1 ≠ pairSide (.initReg true k)) ⊆ {(.bridge k, true)} := by
          rintro ⟨v, bv⟩ hv
          rcases Finset.mem_filter.mp hv with ⟨hvG, hne⟩
          simp only [G0, graphOfArcs, Bool.false_eq_true, ↓reduceIte, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hvG
          rcases hvG with h | ⟨w, hw, heq⟩
          · rcases Prod.mk.inj h with ⟨rfl, _⟩; exact absurd rfl hne
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            rcases (pairArc_cross_iff w (.initReg true k)).mp ⟨hw, hne⟩ with ⟨k', rfl, hk⟩
            have := (PairV.initReg.inj hk).2; subst this; simp
        exact (Finset.card_le_card hsub1).trans (by simp)
      · have hemp : (G0 (u, false)).filter (fun r => pairSide r.1 ≠ pairSide u) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; rintro ⟨v, bv⟩ hv hne
          simp only [G0, graphOfArcs, Bool.false_eq_true, ↓reduceIte, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hv
          rcases hv with h | ⟨w, hw, heq⟩
          · rcases Prod.mk.inj h with ⟨rfl, _⟩; exact hne rfl
          · rcases Prod.mk.inj heq with ⟨rfl, _⟩
            rcases (pairArc_cross_iff w u).mp ⟨hw, hne⟩ with ⟨k, _, rfl⟩
            exact hu ⟨k, rfl⟩
        rw [hemp]; simp
    · by_cases hu : ∃ k, u = .bridge k
      · rcases hu with ⟨k, rfl⟩
        have hsub1 : (G0 (.bridge k, true)).filter (fun r => pairSide r.1 ≠ pairSide (.bridge k)) ⊆ {(.initReg true k, false)} := by
          rintro ⟨v, bv⟩ hv
          rcases Finset.mem_filter.mp hv with ⟨hvG, hne⟩
          simp only [G0, graphOfArcs, ↓reduceIte, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hvG
          rcases hvG with h | ⟨w, hw, heq⟩
          · rcases Prod.mk.inj h with ⟨rfl, _⟩; exact absurd rfl hne
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            rcases (pairArc_cross_iff (.bridge k) w).mp ⟨hw, hne.symm⟩ with ⟨k', hk', rfl⟩
            have := PairV.bridge.inj hk'; subst this; simp
        exact (Finset.card_le_card hsub1).trans (by simp)
      · have hemp : (G0 (u, true)).filter (fun r => pairSide r.1 ≠ pairSide u) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; rintro ⟨v, bv⟩ hv hne
          simp only [G0, graphOfArcs, ↓reduceIte, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hv
          rcases hv with h | ⟨w, hw, heq⟩
          · rcases Prod.mk.inj h with ⟨rfl, _⟩; exact hne rfl
          · rcases Prod.mk.inj heq with ⟨rfl, _⟩
            rcases (pairArc_cross_iff u w).mp ⟨hw, hne.symm⟩ with ⟨k, rfl, _⟩
            exact hu ⟨k, rfl⟩
        rw [hemp]; simp
  · have hsub : (Finset.univ : Finset (Fin m × Bool)).filter (fun p =>
        side p.1 = false ∧ ∃ r ∈ G p, side r.1 = true) ⊆
        (Finset.univ : Finset (Fin n)).image (fun k => eqPB (.bridge k, true)) := by
      intro p hp
      obtain ⟨⟨u, b⟩, rfl⟩ : ∃ q, eqPB q = p := ⟨eqPB.symm p, eqPB.apply_symm_apply p⟩
      rcases (Finset.mem_filter.mp hp).2 with ⟨hsf, r, hrG, hst⟩
      obtain ⟨⟨v, bv⟩, rfl⟩ : ∃ q, eqPB q = r := ⟨eqPB.symm r, eqPB.apply_symm_apply r⟩
      have hsf' : pairSide u = false := by simpa [side, eqPB] using hsf
      have hst' : pairSide v = true := by simpa [side, eqPB] using hst
      have huv : (v, bv) ∈ G0 (u, b) := (hG_iff _ _).mp hrG
      have hne : pairSide u ≠ pairSide v := by rw [hsf', hst']; decide
      cases b
      · simp only [G0, graphOfArcs, Bool.false_eq_true, ↓reduceIte, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at huv
        rcases huv with h | ⟨w, hw, heq⟩
        · rcases Prod.mk.inj h with ⟨rfl, _⟩; exact absurd rfl hne
        · rcases Prod.mk.inj heq with ⟨rfl, _⟩
          rcases (pairArc_cross_iff w u).mp ⟨hw, hne.symm⟩ with ⟨k, rfl, rfl⟩
          simp [pairSide] at hsf'
      · simp only [G0, graphOfArcs, ↓reduceIte, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at huv
        rcases huv with h | ⟨w, hw, heq⟩
        · rcases Prod.mk.inj h with ⟨rfl, _⟩; exact absurd rfl hne
        · rcases Prod.mk.inj heq with ⟨rfl, _⟩
          rcases (pairArc_cross_iff u w).mp ⟨hw, hne⟩ with ⟨k, rfl, rfl⟩
          exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    calc ((Finset.univ : Finset (Fin m × Bool)).filter _).card
        ≤ ((Finset.univ : Finset (Fin n)).image (fun k => eqPB (.bridge k, true))).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := Fintype.card_fin n
  · refine ⟨Ltot t, fun τ => ((Finset.univ : Finset (PairV t × Bool)).filter (fun v => bagLo v ≤ τ.val ∧ τ.val ≤ bagHi v)).image eqPB, ?_, ?_, ?_, ?_⟩
    · intro τ; exact Finset.card_image_le.trans (pairBag_card_le τ.val τ.isLt)
    · intro p
      obtain ⟨v, rfl⟩ : ∃ v, eqPB v = p := ⟨eqPB.symm p, eqPB.apply_symm_apply p⟩
      refine ⟨⟨bagLo v, lt_of_le_of_lt (bagLo_le_hi v) (bagHi_lt v)⟩,
        Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl, bagLo_le_hi v⟩, rfl⟩⟩
    · intro p r hr
      obtain ⟨⟨u, bu⟩, rfl⟩ : ∃ q, eqPB q = p := ⟨eqPB.symm p, eqPB.apply_symm_apply p⟩
      obtain ⟨⟨v, bv⟩, rfl⟩ : ∃ q, eqPB q = r := ⟨eqPB.symm r, eqPB.apply_symm_apply r⟩
      have huv : (v, bv) ∈ G0 (u, bu) := (hG_iff _ _).mp hr
      have hmeet : bagLo (u, bu) ≤ bagHi (v, bv) ∧ bagLo (v, bv) ≤ bagHi (u, bu) := by
        cases bu
        · simp only [G0, graphOfArcs, Bool.false_eq_true, ↓reduceIte, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at huv
          rcases huv with h | ⟨w, hw, heq⟩
          · rcases Prod.mk.inj h with ⟨rfl, rfl⟩
            have hlo : bagLo (v, false) = bagLo (v, true) := by cases v with | initReg s _ => cases s <;> rfl | _ => rfl
            exact ⟨hlo.trans_le (bagLo_le_hi _), hlo.symm.trans_le (bagLo_le_hi _)⟩
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            have := pairArc_interval_meet w u (of_decide_eq_true hw)
            exact ⟨this.2, this.1⟩
        · simp only [G0, graphOfArcs, ↓reduceIte, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at huv
          rcases huv with h | ⟨w, hw, heq⟩
          · rcases Prod.mk.inj h with ⟨rfl, rfl⟩
            have hlo : bagLo (v, false) = bagLo (v, true) := by cases v with | initReg s _ => cases s <;> rfl | _ => rfl
            exact ⟨hlo.symm.trans_le (bagLo_le_hi _), hlo.trans_le (bagLo_le_hi _)⟩
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact pairArc_interval_meet u w (of_decide_eq_true hw)
      let τ : ℕ := max (bagLo (u, bu)) (bagLo (v, bv))
      have hτ_lt : τ < Ltot t := max_lt (lt_of_le_of_lt (bagLo_le_hi _) (bagHi_lt _)) (lt_of_le_of_lt (bagLo_le_hi _) (bagHi_lt _))
      refine ⟨⟨τ, hτ_lt⟩,
        Finset.mem_image.mpr ⟨(u, bu), Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_max_left _ _, max_le (bagLo_le_hi _) hmeet.2⟩, rfl⟩,
        Finset.mem_image.mpr ⟨(v, bv), Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_max_right _ _, max_le hmeet.1 (bagLo_le_hi _)⟩, rfl⟩⟩
    · intro p s τ u hst htu hs hu
      obtain ⟨v, rfl⟩ : ∃ v, eqPB v = p := ⟨eqPB.symm p, eqPB.apply_symm_apply p⟩
      rcases Finset.mem_image.mp hs with ⟨v1, hv1, heq1⟩
      rcases Finset.mem_image.mp hu with ⟨v2, hv2, heq2⟩
      rw [eqPB.injective heq1] at hv1; rw [eqPB.injective heq2] at hv2
      have h1 := (Finset.mem_filter.mp hv1).2; have h2 := (Finset.mem_filter.mp hv2).2
      have hst' : s.val ≤ τ.val := hst; have htu' : τ.val ≤ u.val := htu
      exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, by omega⟩, rfl⟩
  · intro f g on live cover opt
    let on0 : PairV t → Bool := fun u =>
      (pairTag u).elim true (fun p => decide ((if pairSide u then g else f) p.1 = p.2))
    have hon_eq : ∀ u, on (eqP u) = on0 u := fun u => by simp [on, on0, tag, side]
    refine ⟨?_, ?_⟩
    · intro b
      have hbij : ((Finset.univ : Finset (Fin m)).filter (fun i => side i = b ∧ on i = true)).card =
          ((Finset.univ : Finset (PairV t)).filter (fun u => pairSide u = b ∧ on0 u = true)).card := by
        refine Finset.card_bij (fun i _ => eqP.symm i) ?_ ?_ ?_
        · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          exact ⟨hi.1, by rw [← hon_eq, eqP.apply_symm_apply]; exact hi.2⟩
        · intro _ _ _ _ h; exact eqP.symm.injective h
        · intro u hu; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
          exact ⟨eqP u, by simp only [Finset.mem_filter, Finset.mem_univ, true_and, side, eqP.symm_apply_apply, hon_eq]; exact hu, eqP.symm_apply_apply u⟩
      rw [hbij]
      let A := (Finset.univ : Finset (PairV t)).filter (fun u => pairSide u = b ∧ on0 u = true)
      have hpart : A.card =
          (A.filter (fun u => (pairTag u).isNone = true)).card +
          ∑ w : Fin W, (A.filter (fun u => ∃ c, pairTag u = some (wordOf n w, c))).card := by
        have hdisj : Disjoint (A.filter (fun u => (pairTag u).isNone = true))
            ((Finset.univ : Finset (Fin W)).biUnion fun w => A.filter (fun u => ∃ c, pairTag u = some (wordOf n w, c))) := by
          rw [Finset.disjoint_left]; intro u h1 h2
          rcases Finset.mem_biUnion.mp h2 with ⟨w, _, hw⟩
          rcases (Finset.mem_filter.mp hw).2 with ⟨c, hc⟩
          have hn := (Finset.mem_filter.mp h1).2
          rw [hc] at hn; simp at hn
        have hunion : A = A.filter (fun u => (pairTag u).isNone = true) ∪
            (Finset.univ : Finset (Fin W)).biUnion fun w => A.filter (fun u => ∃ c, pairTag u = some (wordOf n w, c)) := by
          ext u; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
          constructor
          · intro hu; cases u with
            | initReg _ _ => left; exact ⟨hu, rfl⟩
            | bridge _ => left; exact ⟨hu, rfl⟩
            | regP _ _ _ => left; exact ⟨hu, rfl⟩
            | regX _ _ _ => left; exact ⟨hu, rfl⟩
            | detD _ w _ => right; exact ⟨w, hu, false, rfl⟩
            | detQ _ w _ => right; exact ⟨w, hu, false, rfl⟩
            | detU _ w _ _ => right; exact ⟨w, hu, false, rfl⟩
            | detF _ w _ => right; exact ⟨w, hu, false, rfl⟩
            | padT _ w _ _ => right; exact ⟨w, hu, true, rfl⟩
          · rintro (⟨hu, _⟩ | ⟨_, hu, _⟩) <;> exact hu
        conv_lhs => rw [hunion]
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_biUnion (by
          intro w1 _ w2 _ hne; dsimp only [Function.onFun]; rw [Finset.disjoint_left]; intro u h1 h2
          rcases (Finset.mem_filter.mp h1).2 with ⟨c1, hc1⟩
          rcases (Finset.mem_filter.mp h2).2 with ⟨c2, hc2⟩
          rw [hc1] at hc2
          have hw : wordOf n w1 = wordOf n w2 := (Prod.mk.inj (Option.some.inj hc2)).1
          exact hne ((wordEquiv n).injective hw))]
      rw [hpart]
      have hnone : (A.filter (fun u => (pairTag u).isNone = true)).card = (if b then n else 2 * n) + 2 * n * W := by
        let S0 : Finset (PairV t) :=
          (Finset.univ : Finset (Fin n)).image (fun k => .initReg b k) ∪
          (if b then ∅ else (Finset.univ : Finset (Fin n)).image .bridge) ∪
          ((Finset.univ : Finset (Fin W × Fin n)).image (fun wk => .regP b wk.1 wk.2) ∪
           (Finset.univ : Finset (Fin W × Fin n)).image (fun wk => .regX b wk.1 wk.2))
        have heq : A.filter (fun u => (pairTag u).isNone = true) = S0 := by
          ext u; simp only [A, S0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image]
          cases u with
          | initReg s k => cases s <;> cases b <;> simp [pairSide, pairTag, on0]
          | bridge k => cases b <;> simp [pairSide, pairTag, on0]
          | regP s w k => cases s <;> cases b <;> simp [pairSide, pairTag, on0]
          | regX s w k => cases s <;> cases b <;> simp [pairSide, pairTag, on0]
          | detD s w k => cases b <;> simp [pairTag]
          | detQ s w k => cases b <;> simp [pairTag]
          | detU s w k c => cases b <;> simp [pairTag]
          | detF s w c => cases b <;> simp [pairTag]
          | padT s w j c => cases b <;> simp [pairTag]
        rw [heq, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
        · rw [Finset.card_image_of_injective _ (fun _ _ h => (PairV.initReg.inj h).2),
              Finset.card_image_of_injective _ (fun _ _ h => Prod.ext (PairV.regP.inj h).2.1 (PairV.regP.inj h).2.2),
              Finset.card_image_of_injective _ (fun _ _ h => Prod.ext (PairV.regX.inj h).2.1 (PairV.regX.inj h).2.2)]
          cases b <;> simp [Finset.card_image_of_injective _ (fun _ _ h => PairV.bridge.inj h)] <;> ring
        · rw [Finset.disjoint_left]; intro u h1 h2; rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩; rcases Finset.mem_image.mp h2 with ⟨_, _, h⟩; cases h
        · rw [Finset.disjoint_left]; intro u h1 h2; rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩
          split_ifs at h2; simp at h2; rcases Finset.mem_image.mp h2 with ⟨_, _, h⟩; cases h
        · rw [Finset.disjoint_left]; intro u h1 h2
          rcases Finset.mem_union.mp h1 with h1 | h1
          · rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩
            rcases Finset.mem_union.mp h2 with h2 | h2 <;> (rcases Finset.mem_image.mp h2 with ⟨_, _, h⟩; cases h)
          · split_ifs at h1; simp at h1
            rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩
            rcases Finset.mem_union.mp h2 with h2 | h2 <;> (rcases Finset.mem_image.mp h2 with ⟨_, _, h⟩; cases h)
      have hon0_detD : ∀ s w k, on0 (.detD s w k) = !((if s then g else f) (wordOf n w)) := fun s w k => by
        cases s
        · dsimp only [on0, pairTag, pairSide, n, Option.elim]; cases f (wordOf (t + 1) w) <;> rfl
        · dsimp only [on0, pairTag, pairSide, n, Option.elim]; cases g (wordOf (t + 1) w) <;> rfl
      have hon0_detQ : ∀ s w k, on0 (.detQ s w k) = !((if s then g else f) (wordOf n w)) := fun s w k => by
        cases s
        · dsimp only [on0, pairTag, pairSide, n, Option.elim]; cases f (wordOf (t + 1) w) <;> rfl
        · dsimp only [on0, pairTag, pairSide, n, Option.elim]; cases g (wordOf (t + 1) w) <;> rfl
      have hon0_detU : ∀ s w k c, on0 (.detU s w k c) = !((if s then g else f) (wordOf n w)) := fun s w k c => by
        cases s
        · dsimp only [on0, pairTag, pairSide, n, Option.elim]; cases f (wordOf (t + 1) w) <;> rfl
        · dsimp only [on0, pairTag, pairSide, n, Option.elim]; cases g (wordOf (t + 1) w) <;> rfl
      have hon0_detF : ∀ s w c, on0 (.detF s w c) = !((if s then g else f) (wordOf n w)) := fun s w c => by
        cases s
        · dsimp only [on0, pairTag, pairSide, n, Option.elim]; cases f (wordOf (t + 1) w) <;> rfl
        · dsimp only [on0, pairTag, pairSide, n, Option.elim]; cases g (wordOf (t + 1) w) <;> rfl
      have hon0_padT : ∀ s w j c, on0 (.padT s w j c) = (if s then g else f) (wordOf n w) := fun s w j c => by
        cases s
        · dsimp only [on0, pairTag, pairSide, n, Option.elim]; cases f (wordOf (t + 1) w) <;> rfl
        · dsimp only [on0, pairTag, pairSide, n, Option.elim]; cases g (wordOf (t + 1) w) <;> rfl
      have hw_card : ∀ w : Fin W, (A.filter (fun u => ∃ c, pairTag u = some (wordOf n w, c))).card = 6 * n + 2 := by
        intro w
        by_cases hval : (if b then g else f) (wordOf n w) = true
        · have heq : A.filter (fun u => ∃ c, pairTag u = some (wordOf n w, c)) =
              (Finset.univ : Finset (Fin (3 * n + 1) × Bool)).image (fun jb => .padT b w jb.1 jb.2) := by
            ext u; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
            cases u with
            | initReg _ _ => simp [pairTag]
            | bridge _ => simp [pairTag]
            | regP _ _ _ => simp [pairTag]
            | regX _ _ _ => simp [pairTag]
            | detD s w' k =>
              constructor
              · rintro ⟨⟨hsb, h1⟩, _, h2⟩; dsimp only [pairSide] at hsb; subst hsb; have := (wordEquiv n).injective (Prod.mk.inj (Option.some.inj h2)).1; subst this; rw [hon0_detD, hval] at h1; simp at h1
              · rintro ⟨_, h⟩; cases h
            | detQ s w' k =>
              constructor
              · rintro ⟨⟨hsb, h1⟩, _, h2⟩; dsimp only [pairSide] at hsb; subst hsb; have := (wordEquiv n).injective (Prod.mk.inj (Option.some.inj h2)).1; subst this; rw [hon0_detQ, hval] at h1; simp at h1
              · rintro ⟨_, h⟩; cases h
            | detU s w' k c =>
              constructor
              · rintro ⟨⟨hsb, h1⟩, _, h2⟩; dsimp only [pairSide] at hsb; subst hsb; have := (wordEquiv n).injective (Prod.mk.inj (Option.some.inj h2)).1; subst this; rw [hon0_detU, hval] at h1; simp at h1
              · rintro ⟨_, h⟩; cases h
            | detF s w' c =>
              constructor
              · rintro ⟨⟨hsb, h1⟩, _, h2⟩; dsimp only [pairSide] at hsb; subst hsb; have := (wordEquiv n).injective (Prod.mk.inj (Option.some.inj h2)).1; subst this; rw [hon0_detF, hval] at h1; simp at h1
              · rintro ⟨_, h⟩; cases h
            | padT s w' j c =>
              constructor
              · rintro ⟨⟨rfl, _⟩, _, h2⟩
                have hw' := (wordEquiv n).injective (Prod.mk.inj (Option.some.inj h2)).1; subst hw'
                exact ⟨(j, c), rfl⟩
              · rintro ⟨⟨j', c'⟩, heq⟩; rcases PairV.padT.inj heq with ⟨rfl, rfl, rfl, rfl⟩
                exact ⟨⟨rfl, by rw [hon0_padT]; exact hval⟩, true, rfl⟩
          rw [heq, Finset.card_image_of_injective _ (fun _ _ h => Prod.ext (PairV.padT.inj h).2.2.1 (PairV.padT.inj h).2.2.2)]
          simp; omega
        · have hvalf : (if b then g else f) (wordOf n w) = false := Bool.eq_false_iff.mpr hval
          let SF : Finset (PairV t) :=
            (Finset.univ : Finset (Fin n)).image (fun k => .detD b w k) ∪
            (Finset.univ : Finset (Fin t)).image (fun k => .detQ b w k) ∪
            ((Finset.univ : Finset (Fin n × Fin 4)).image (fun kc => .detU b w kc.1 kc.2) ∪
             (Finset.univ : Finset (Fin 3)).image (fun c => .detF b w c))
          have heq : A.filter (fun u => ∃ c, pairTag u = some (wordOf n w, c)) = SF := by
            ext u; simp only [A, SF, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image]
            cases u with
            | initReg _ _ => simp [pairTag]
            | bridge _ => simp [pairTag]
            | regP _ _ _ => simp [pairTag]
            | regX _ _ _ => simp [pairTag]
            | padT s w' j c =>
              constructor
              · rintro ⟨⟨hsb, h1⟩, _, h2⟩; dsimp only [pairSide] at hsb; subst hsb; have := (wordEquiv n).injective (Prod.mk.inj (Option.some.inj h2)).1; subst this; rw [hon0_padT, hvalf] at h1; simp at h1
              · rintro ((⟨_, h⟩ | ⟨_, h⟩) | (⟨_, h⟩ | ⟨_, h⟩)) <;> cases h
            | detD s w' k =>
              constructor
              · rintro ⟨⟨rfl, _⟩, _, h2⟩; have := (wordEquiv n).injective (Prod.mk.inj (Option.some.inj h2)).1; subst this; left; left; exact ⟨k, rfl⟩
              · rintro ((⟨k', h⟩ | ⟨_, h⟩) | (⟨_, h⟩ | ⟨_, h⟩))
                · rcases PairV.detD.inj h with ⟨rfl, rfl, rfl⟩; exact ⟨⟨rfl, by rw [hon0_detD, hvalf]; rfl⟩, false, rfl⟩
                · cases h
                · cases h
                · cases h
            | detQ s w' k =>
              constructor
              · rintro ⟨⟨rfl, _⟩, _, h2⟩; have := (wordEquiv n).injective (Prod.mk.inj (Option.some.inj h2)).1; subst this; left; right; exact ⟨k, rfl⟩
              · rintro ((⟨_, h⟩ | ⟨k', h⟩) | (⟨_, h⟩ | ⟨_, h⟩))
                · cases h
                · rcases PairV.detQ.inj h with ⟨rfl, rfl, rfl⟩; exact ⟨⟨rfl, by rw [hon0_detQ, hvalf]; rfl⟩, false, rfl⟩
                · cases h
                · cases h
            | detU s w' k c =>
              constructor
              · rintro ⟨⟨rfl, _⟩, _, h2⟩; have := (wordEquiv n).injective (Prod.mk.inj (Option.some.inj h2)).1; subst this; right; left; exact ⟨(k, c), rfl⟩
              · rintro ((⟨_, h⟩ | ⟨_, h⟩) | (⟨kc, h⟩ | ⟨_, h⟩))
                · cases h
                · cases h
                · rcases PairV.detU.inj h with ⟨rfl, rfl, rfl, rfl⟩; exact ⟨⟨rfl, by rw [hon0_detU, hvalf]; rfl⟩, false, rfl⟩
                · cases h
            | detF s w' c =>
              constructor
              · rintro ⟨⟨rfl, _⟩, _, h2⟩; have := (wordEquiv n).injective (Prod.mk.inj (Option.some.inj h2)).1; subst this; right; right; exact ⟨c, rfl⟩
              · rintro ((⟨_, h⟩ | ⟨_, h⟩) | (⟨_, h⟩ | ⟨c', h⟩))
                · cases h
                · cases h
                · cases h
                · rcases PairV.detF.inj h with ⟨rfl, rfl, rfl⟩; exact ⟨⟨rfl, by rw [hon0_detF, hvalf]; rfl⟩, false, rfl⟩
          rw [heq, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
          · rw [Finset.card_image_of_injective _ (fun _ _ h => (PairV.detD.inj h).2.2),
                Finset.card_image_of_injective _ (fun _ _ h => (PairV.detQ.inj h).2.2),
                Finset.card_image_of_injective _ (fun _ _ h => Prod.ext (PairV.detU.inj h).2.2.1 (PairV.detU.inj h).2.2.2),
                Finset.card_image_of_injective _ (fun _ _ h => (PairV.detF.inj h).2.2)]
            simp; omega
          · rw [Finset.disjoint_left]; intro u h1 h2; rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩; rcases Finset.mem_image.mp h2 with ⟨_, _, h⟩; cases h
          · rw [Finset.disjoint_left]; intro u h1 h2; rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩; rcases Finset.mem_image.mp h2 with ⟨_, _, h⟩; cases h
          · rw [Finset.disjoint_left]; intro u h1 h2
            rcases Finset.mem_union.mp h1 with h1 | h1 <;> rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩ <;>
              rcases Finset.mem_union.mp h2 with h2 | h2 <;> (rcases Finset.mem_image.mp h2 with ⟨_, _, h⟩; cases h)
      rw [hnone, Finset.sum_congr rfl (fun w _ => hw_card w), Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      dsimp only [keep]; cases b <;> ring
    · dsimp only [opt]
      rw [card_minCover_congr eqP (@pairArc t) pairArc_irrefl G on0 on hG_iff hon_eq]
      exact card_mono_succ t f g

private lemma main_core (n : ℕ) :
    let Word := Fin n → Bool
    let Table := Word → Bool
    ∃ (m : Nat) (G : (Fin m × Bool) → Finset (Fin m × Bool))
      (side : Fin m → Bool) (tag : Fin m → Option (Word × Bool)) (keep : Bool → Nat),
      m ≤ 15000*(n+1)*2^n ∧ (∀ i, (i,true) ∈ G (i,false)) ∧
      (∀ p, p ∉ G p ∧ (G p).card ≤ 3) ∧ (∀ p r, r ∈ G p ↔ p ∈ G r) ∧
      (∀ p, ∀ r ∈ G p, p.2 ≠ r.2) ∧
      (∀ p, ((G p).filter (fun r => side r.1 ≠ side p.1)).card ≤ 1) ∧
      ((Finset.univ : Finset (Fin m × Bool)).filter (fun p =>
        side p.1 = false ∧ ∃ r ∈ G p, side r.1 = true)).card ≤ n ∧
      (∃ (l : Nat) (bag : Fin l → Finset (Fin m × Bool)),
        (∀ t, (bag t).card ≤ n+37) ∧ (∀ p, ∃ t, p ∈ bag t) ∧
        (∀ p r, r ∈ G p → ∃ t, p ∈ bag t ∧ r ∈ bag t) ∧
        ∀ p s t u, s ≤ t → t ≤ u → p ∈ bag s → p ∈ bag u → p ∈ bag t) ∧
      ∀ f g : Table,
        let on := fun i => (tag i).elim true (fun p => decide ((if side i then g else f) p.1 = p.2))
        let live := (Finset.univ : Finset (Fin m × Bool)).filter (fun p => on p.1)
        let cover := fun (C : Finset (Fin m × Bool)) => C ⊆ live ∧
          ∀ p ∈ live, ∀ r ∈ G p, r ∈ live → p ∈ C ∨ r ∈ C
        let opt := ((Finset.univ : Finset (Finset (Fin m × Bool))).filter
          (fun C => cover C ∧ ∀ W, cover W → C.card ≤ W.card)).card
        (∀ b, ((Finset.univ : Finset (Fin m)).filter (fun i => side i = b ∧ on i = true)).card = keep b) ∧
        opt % 2 = ((Finset.univ : Finset Word).filter (fun y => f y && g y)).card % 2 := by
  cases n with
  | zero => exact case_n0
  | succ t => exact case_succ t

end CountingSucc

private lemma filter_eq_of_iff {α : Type} [Fintype α] {p q : α → Prop}
    {dp : DecidablePred p} {dq : DecidablePred q} (h : ∀ x, p x ↔ q x) :
    (@Finset.filter α p dp Finset.univ) = (@Finset.filter α q dq Finset.univ) := by
  ext x; simp [h x]

private lemma filter_sub_eq_of_iff {α : Type} (s : Finset α) {p q : α → Prop}
    {dp : DecidablePred p} {dq : DecidablePred q} (h : ∀ x, p x ↔ q x) :
    (@Finset.filter α p dp s) = (@Finset.filter α q dq s) := by
  ext x; simp [h x]

private lemma ite_dec_eq {α : Type} {p : Prop} {d1 d2 : Decidable p} (a b : α) :
    @ite α p d1 a b = @ite α p d2 a b := by
  by_cases h : p <;> simp [h]

end PEqualNP.Outside.L_lib_1222

theorem PEqualNP.Outside.L_lib_1222 :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ n : Nat,
      let Word := Fin n → Bool
      let Table := Word → Bool
      ∃ (m : Nat) (G : (Fin m × Bool) → Finset (Fin m × Bool))
        (side : Fin m → Bool) (tag : Fin m → Option (Word × Bool)) (keep : Bool → Nat),
        m ≤ 15000*(n+1)*2^n ∧ (∀ i, (i,true) ∈ G (i,false)) ∧
        (∀ p, p ∉ G p ∧ (G p).card ≤ 3) ∧ (∀ p r, r ∈ G p ↔ p ∈ G r) ∧
        (∀ p, ∀ r ∈ G p, p.2 ≠ r.2) ∧
        (∀ p, ((G p).filter (fun r => side r.1 ≠ side p.1)).card ≤ 1) ∧
        ((Finset.univ : Finset (Fin m × Bool)).filter (fun p =>
          side p.1 = false ∧ ∃ r ∈ G p, side r.1 = true)).card ≤ n ∧
        (∃ (l : Nat) (bag : Fin l → Finset (Fin m × Bool)),
          (∀ t, (bag t).card ≤ n+37) ∧ (∀ p, ∃ t, p ∈ bag t) ∧
          (∀ p r, r ∈ G p → ∃ t, p ∈ bag t ∧ r ∈ bag t) ∧
          ∀ p s t u, s ≤ t → t ≤ u → p ∈ bag s → p ∈ bag u → p ∈ bag t) ∧
        ∀ f g : Table,
          let on := fun i => (tag i).elim true (fun p => decide ((if side i then g else f) p.1 = p.2))
          let live := (Finset.univ : Finset (Fin m × Bool)).filter (fun p => on p.1)
          let cover := fun (C : Finset (Fin m × Bool)) => C ⊆ live ∧
            ∀ p ∈ live, ∀ r ∈ G p, r ∈ live → p ∈ C ∨ r ∈ C
          let opt := ((Finset.univ : Finset (Finset (Fin m × Bool))).filter
            (fun C => cover C ∧ ∀ W, cover W → C.card ≤ W.card)).card
          (∀ b, ((Finset.univ : Finset (Fin m)).filter (fun i => side i = b ∧ on i = true)).card = keep b) ∧
          opt % 2 = ((Finset.univ : Finset Word).filter (fun y => f y && g y)).card % 2 := by
  intro n
  rcases PEqualNP.Outside.L_lib_1222.main_core n with
    ⟨m, G, side, tag, keep, hm, hmatch, hdeg, hsym, hbip, hcut1, hcutn, hpd, hfg⟩
  refine ⟨m, G, side, tag, keep, hm, hmatch, hdeg, hsym, hbip, ?_, ?_, hpd, ?_⟩
  · intro p
    refine le_of_eq_of_le (congrArg Finset.card (PEqualNP.Outside.L_lib_1222.filter_sub_eq_of_iff (G p) (fun _ => Iff.rfl))) (hcut1 p)
  · refine le_of_eq_of_le (congrArg Finset.card (PEqualNP.Outside.L_lib_1222.filter_eq_of_iff (fun _ => Iff.rfl))) hcutn
  · intro f g
    rcases hfg f g with ⟨hkeep, hopt⟩
    have hon_dec : ∀ i : Fin m,
        ((tag i).elim true fun q =>
          @decide ((@ite ((Fin n → Bool) → Bool) (side i = true) (Classical.propDecidable _) g f) q.1 = q.2)
            (Classical.propDecidable _)) =
        ((tag i).elim true fun q =>
          @decide ((@ite ((Fin n → Bool) → Bool) (side i = true) (instDecidableEqBool _ _) g f) q.1 = q.2)
            (instDecidableEqBool _ _)) := by
      intro i
      cases tag i with
      | none => rfl
      | some q =>
        dsimp only [Option.elim]
        rw [PEqualNP.Outside.L_lib_1222.ite_dec_eq (d1 := Classical.propDecidable _) (d2 := instDecidableEqBool _ _)]
        by_cases h : (if side i = true then g else f) q.1 = q.2 <;> simp [h]
    refine ⟨fun b => (congrArg Finset.card (PEqualNP.Outside.L_lib_1222.filter_eq_of_iff (fun i => by dsimp only; rw [hon_dec i]))).trans (hkeep b), ?_⟩
    · have hlive : @Finset.filter (Fin m × Bool)
          (fun p => ((tag p.1).elim true fun q =>
            @decide ((@ite ((Fin n → Bool) → Bool) (side p.1 = true) (Classical.propDecidable _) g f) q.1 = q.2)
              (Classical.propDecidable _)) = true)
          (fun p => Classical.propDecidable _) Finset.univ =
          @Finset.filter (Fin m × Bool)
          (fun p => ((tag p.1).elim true fun q =>
            @decide ((@ite ((Fin n → Bool) → Bool) (side p.1 = true) (instDecidableEqBool _ _) g f) q.1 = q.2)
              (instDecidableEqBool _ _)) = true)
          (fun p => instDecidableEqBool _ _) Finset.univ :=
        PEqualNP.Outside.L_lib_1222.filter_eq_of_iff (fun p => by rw [hon_dec p.1])
      have ho : ∀ (a1 a2 b1 b2 : ℕ), a1 = a2 → b1 = b2 → a2 % 2 = b2 % 2 → a1 % 2 = b1 % 2 := by
        intro a1 a2 b1 b2 h1 h2 h3; rw [h1, h2]; exact h3
      refine ho _ _ _ _ ?_ ?_ hopt
      · congr 1
        refine PEqualNP.Outside.L_lib_1222.filter_eq_of_iff fun C => ?_
        rw [hlive]
      · congr 1
        ext y; simp
