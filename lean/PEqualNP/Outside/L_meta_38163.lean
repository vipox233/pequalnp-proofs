import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38163

private lemma exists_other_two {r c : Nat}
    (rowOK : Fin r → Fin 3 → Prop) (colOK : Fin c → Fin 3 → Prop)
    (hcover : ∀ x y, ∃ i, rowOK x i ∧ colOK y i)
    (hnondeg : ∀ i, (∃ x, ¬ rowOK x i) ∧ (∃ y, ¬ colOK y i)) :
    (∀ x (i : Fin 3), ¬ rowOK x i → ∀ j : Fin 3, j ≠ i → rowOK x j) ∧
    (∀ y (i : Fin 3), ¬ colOK y i → ∀ j : Fin 3, j ≠ i → colOK y j) := by
  constructor
  · intro x i hxi j hji
    by_contra hxj
    obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
      fin_cases i <;> fin_cases j <;> simp_all
      · exact ⟨2, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
      · exact ⟨2, by decide, by decide⟩
      · exact ⟨0, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
      · exact ⟨0, by decide, by decide⟩
    obtain ⟨y, hyk⟩ := (hnondeg k).2
    obtain ⟨m, hxm, hym⟩ := hcover x y
    have hm : m = i ∨ m = j ∨ m = k := by
      fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases m <;> simp_all
    rcases hm with rfl | rfl | rfl
    · exact hxi hxm
    · exact hxj hxm
    · exact hyk hym
  · intro y i hyi j hji
    by_contra hyj
    obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
      fin_cases i <;> fin_cases j <;> simp_all
      · exact ⟨2, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
      · exact ⟨2, by decide, by decide⟩
      · exact ⟨0, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
      · exact ⟨0, by decide, by decide⟩
    obtain ⟨x, hxk⟩ := (hnondeg k).1
    obtain ⟨m, hxm, hym⟩ := hcover x y
    have hm : m = i ∨ m = j ∨ m = k := by
      fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases m <;> simp_all
    rcases hm with rfl | rfl | rfl
    · exact hyi hym
    · exact hyj hym
    · exact hxk hxm

private lemma part_one {r c : Nat}
    (rowOK : Fin r → Fin 3 → Prop) (colOK : Fin c → Fin 3 → Prop)
    (hcover : ∀ x y, ∃ i, rowOK x i ∧ colOK y i)
    (hnondeg : ∀ i, (∃ x, ¬ rowOK x i) ∧ (∃ y, ¬ colOK y i)) :
    ∃ (L : Fin 5 → Fin r → Prop) (R : Fin 5 → Fin c → Prop) (T : Fin 5 → Fin 3),
      (∀ x y, ∃! j : Fin 5, L j x ∧ R j y) ∧
      (∀ j x y, L j x → R j y → rowOK x (T j) ∧ colOK y (T j)) := by
  have ⟨hrow2, hcol2⟩ := exists_other_two rowOK colOK hcover hnondeg
  let L : Fin 5 → Fin r → Prop := fun j x =>
    match j with
    | ⟨0, _⟩ => rowOK x 0
    | ⟨1, _⟩ => ¬ rowOK x 0
    | ⟨2, _⟩ => ¬ rowOK x 0
    | ⟨3, _⟩ => rowOK x 0 ∧ rowOK x 1
    | ⟨4, _⟩ => rowOK x 0 ∧ ¬ rowOK x 1
  let R : Fin 5 → Fin c → Prop := fun j y =>
    match j with
    | ⟨0, _⟩ => colOK y 0
    | ⟨1, _⟩ => colOK y 1
    | ⟨2, _⟩ => ¬ colOK y 1
    | ⟨3, _⟩ => ¬ colOK y 0
    | ⟨4, _⟩ => ¬ colOK y 0
  let T : Fin 5 → Fin 3 := fun j =>
    match j with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => 2
    | ⟨3, _⟩ => 1
    | ⟨4, _⟩ => 2
  refine ⟨L, R, T, ?_, ?_⟩
  · intro x y
    by_cases hx0 : rowOK x 0
    · by_cases hy0 : colOK y 0
      · refine ⟨0, ⟨hx0, hy0⟩, ?_⟩
        intro j hj; fin_cases j <;> simp_all [L, R]
      · by_cases hx1 : rowOK x 1
        · refine ⟨3, ⟨⟨hx0, hx1⟩, hy0⟩, ?_⟩
          intro j hj; fin_cases j <;> simp_all [L, R]
        · refine ⟨4, ⟨⟨hx0, hx1⟩, hy0⟩, ?_⟩
          intro j hj; fin_cases j <;> simp_all [L, R]
    · by_cases hy1 : colOK y 1
      · refine ⟨1, ⟨hx0, hy1⟩, ?_⟩
        intro j hj; fin_cases j <;> simp_all [L, R]
      · refine ⟨2, ⟨hx0, hy1⟩, ?_⟩
        intro j hj; fin_cases j <;> simp_all [L, R]
  · intro j x y hL hR
    fin_cases j
    · exact ⟨hL, hR⟩
    · exact ⟨hrow2 x 0 hL 1 (by decide), hR⟩
    · exact ⟨hrow2 x 0 hL 2 (by decide), hcol2 y 1 hR 2 (by decide)⟩
    · exact ⟨hL.2, hcol2 y 0 hR 1 (by decide)⟩
    · exact ⟨hrow2 x 1 hL.2 2 (by decide), hcol2 y 0 hR 2 (by decide)⟩

private lemma part_upper {n r c : Nat}
    (rowOK : Fin r → Fin 3 → Prop) (colOK : Fin c → Fin 3 → Prop)
    (hcover : ∀ x y, ∃ i, rowOK x i ∧ colOK y i)
    (hnondeg : ∀ i, (∃ x, ¬ rowOK x i) ∧ (∃ y, ¬ colOK y i)) :
    ∃ (left : Fin (5^(n+1)) → (Fin (n+1) → Fin r) → Prop)
      (right : Fin (5^(n+1)) → (Fin (n+1) → Fin c) → Prop)
      (tag : Fin (5^(n+1)) → Fin (n+1) → Fin 3),
      (∀ x y, ∃! j : Fin (5^(n+1)), left j x ∧ right j y) ∧
      ∀ j x y, left j x → right j y → ∀ k, rowOK (x k) (tag j k) ∧ colOK (y k) (tag j k) := by
  obtain ⟨L, R, T, huniq, hok⟩ := part_one rowOK colOK hcover hnondeg
  let e : (Fin (n + 1) → Fin 5) ≃ Fin (5 ^ (n + 1)) :=
    (Fintype.equivFinOfCardEq (by simp)).symm.symm
  refine ⟨fun j x => ∀ k, L (e.symm j k) (x k),
          fun j y => ∀ k, R (e.symm j k) (y k),
          fun j k => T (e.symm j k), ?_, ?_⟩
  · intro x y
    choose f hf using fun k => huniq (x k) (y k)
    refine ⟨e f, ⟨fun k => by simpa using (hf k).1.1, fun k => by simpa using (hf k).1.2⟩, ?_⟩
    intro j ⟨hjL, hjR⟩
    apply e.symm.injective
    funext k
    simp only [Equiv.symm_apply_apply]
    exact (hf k).2 (e.symm j k) ⟨hjL k, hjR k⟩
  · intro j x y hL hR k
    exact hok (e.symm j k) (x k) (y k) (hL k) (hR k)

private lemma fin3_ne_add1 (t : Fin 3) : t ≠ t + 1 := by fin_cases t <;> decide
private lemma fin3_ne_add2 (t : Fin 3) : t ≠ t + 2 := by fin_cases t <;> decide
private lemma fin3_add1_ne_add2 (t : Fin 3) : t + 1 ≠ t + 2 := by fin_cases t <;> decide
private lemma fin3_forced2 (t x : Fin 3) (h1 : t ≠ x) (h2 : t + 1 ≠ x) : x = t + 2 := by
  fin_cases t <;> fin_cases x <;> simp_all
private lemma fin3_forced1 (t x : Fin 3) (h1 : t ≠ x) (h2 : t + 2 ≠ x) : x = t + 1 := by
  fin_cases t <;> fin_cases x <;> simp_all
private lemma card_two_of_mul_gt_two {a b : Nat} (ha : a ≤ 2) (hb : b ≤ 2) (hm : 2 < a * b) :
    2 ≤ a ∧ 2 ≤ b := by
  constructor
  · by_contra h; have : a ≤ 1 := by omega
    have : a * b ≤ 1 * 2 := Nat.mul_le_mul this hb; omega
  · by_contra h; have : b ≤ 1 := by omega
    have : a * b ≤ 2 * 1 := Nat.mul_le_mul ha this; omega

private lemma lower_3x3 {p : Nat}
    (L : Fin p → Fin 3 → Prop) (R : Fin p → Fin 3 → Prop) (T : Fin p → Fin 3)
    (hpart : ∀ a b : Fin 3, ∃! j : Fin p, L j a ∧ R j b)
    (havoid : ∀ j a b, L j a → R j b → a ≠ T j ∧ b ≠ T j) :
    5 ≤ p := by
  classical
  let A : Fin p → Finset (Fin 3) := fun j => Finset.univ.filter (fun a => L j a)
  let B : Fin p → Finset (Fin 3) := fun j => Finset.univ.filter (fun b => R j b)
  by_cases hbig : ∃ j0 : Fin p, 2 < (A j0).card * (B j0).card
  · obtain ⟨j0, hj0⟩ := hbig
    have hApos : (A j0).Nonempty := by
      by_contra h; rw [Finset.not_nonempty_iff_eq_empty.mp h] at hj0; simp at hj0
    have hBpos : (B j0).Nonempty := by
      by_contra h; rw [Finset.not_nonempty_iff_eq_empty.mp h] at hj0; simp at hj0
    obtain ⟨a0, ha0⟩ := hApos
    obtain ⟨b0, hb0⟩ := hBpos
    have ha0' : L j0 a0 := (Finset.mem_filter.mp ha0).2
    have hb0' : R j0 b0 := (Finset.mem_filter.mp hb0).2
    have hTA : T j0 ∉ A j0 := fun h => (havoid j0 (T j0) b0 (Finset.mem_filter.mp h).2 hb0').1 rfl
    have hTB : T j0 ∉ B j0 := fun h => (havoid j0 a0 (T j0) ha0' (Finset.mem_filter.mp h).2).2 rfl
    have hAsub : A j0 ⊆ Finset.univ.erase (T j0) := fun a ha =>
      Finset.mem_erase.mpr ⟨fun h => hTA (h ▸ ha), Finset.mem_univ a⟩
    have hBsub : B j0 ⊆ Finset.univ.erase (T j0) := fun b hb =>
      Finset.mem_erase.mpr ⟨fun h => hTB (h ▸ hb), Finset.mem_univ b⟩
    have hcard : (Finset.univ.erase (T j0) : Finset (Fin 3)).card = 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; decide
    have hAle : (A j0).card ≤ 2 := (Finset.card_le_card hAsub).trans hcard.le
    have hBle : (B j0).card ≤ 2 := (Finset.card_le_card hBsub).trans hcard.le
    have ⟨hAge, hBge⟩ := card_two_of_mul_gt_two hAle hBle hj0
    have hAeq : A j0 = Finset.univ.erase (T j0) :=
      Finset.eq_of_subset_of_card_le hAsub (by omega)
    have hBeq : B j0 = Finset.univ.erase (T j0) :=
      Finset.eq_of_subset_of_card_le hBsub (by omega)
    let t := T j0
    let u : Fin 3 := t + 1
    let v : Fin 3 := t + 2
    have htu : t ≠ u := fin3_ne_add1 t
    have htv : t ≠ v := fin3_ne_add2 t
    have huv : u ≠ v := fin3_add1_ne_add2 t
    have hLu : L j0 u := by
      have : u ∈ A j0 := by rw [hAeq]; exact Finset.mem_erase.mpr ⟨htu.symm, Finset.mem_univ _⟩
      exact (Finset.mem_filter.mp this).2
    have hLv : L j0 v := by
      have : v ∈ A j0 := by rw [hAeq]; exact Finset.mem_erase.mpr ⟨htv.symm, Finset.mem_univ _⟩
      exact (Finset.mem_filter.mp this).2
    have hRu : R j0 u := by
      have : u ∈ B j0 := by rw [hBeq]; exact Finset.mem_erase.mpr ⟨htu.symm, Finset.mem_univ _⟩
      exact (Finset.mem_filter.mp this).2
    have hRv : R j0 v := by
      have : v ∈ B j0 := by rw [hBeq]; exact Finset.mem_erase.mpr ⟨htv.symm, Finset.mem_univ _⟩
      exact (Finset.mem_filter.mp this).2
    obtain ⟨j1, hj1, _⟩ := hpart t u
    obtain ⟨j2, hj2, _⟩ := hpart u t
    obtain ⟨j3, hj3, _⟩ := hpart t v
    obtain ⟨j4, hj4, _⟩ := hpart v t
    have hT1 : T j1 = v := by
      have ⟨h1, h2⟩ := havoid j1 t u hj1.1 hj1.2
      exact fin3_forced2 t (T j1) h1 h2
    have hT2 : T j2 = v := by
      have ⟨h1, h2⟩ := havoid j2 u t hj2.1 hj2.2
      exact fin3_forced2 t (T j2) h2 h1
    have hT3 : T j3 = u := by
      have ⟨h1, h2⟩ := havoid j3 t v hj3.1 hj3.2
      exact fin3_forced1 t (T j3) h1 h2
    have hT4 : T j4 = u := by
      have ⟨h1, h2⟩ := havoid j4 v t hj4.1 hj4.2
      exact fin3_forced1 t (T j4) h2 h1
    have h01 : j0 ≠ j1 := fun h => htv (by rw [← hT1, ← h])
    have h02 : j0 ≠ j2 := fun h => htv (by rw [← hT2, ← h])
    have h03 : j0 ≠ j3 := fun h => htu (by rw [← hT3, ← h])
    have h04 : j0 ≠ j4 := fun h => htu (by rw [← hT4, ← h])
    have h13 : j1 ≠ j3 := fun h => huv.symm (by rw [← hT1, ← hT3, h])
    have h14 : j1 ≠ j4 := fun h => huv.symm (by rw [← hT1, ← hT4, h])
    have h23 : j2 ≠ j3 := fun h => huv.symm (by rw [← hT2, ← hT3, h])
    have h24 : j2 ≠ j4 := fun h => huv.symm (by rw [← hT2, ← hT4, h])
    have h12 : j1 ≠ j2 := by
      intro h
      have huu : L j1 u ∧ R j1 u := ⟨h ▸ hj2.1, hj1.2⟩
      obtain ⟨k, _, hk⟩ := hpart u u
      have := (hk j1 huu).trans (hk j0 ⟨hLu, hRu⟩).symm
      exact h01 this.symm
    have h34 : j3 ≠ j4 := by
      intro h
      have hvv : L j3 v ∧ R j3 v := ⟨h ▸ hj4.1, hj3.2⟩
      obtain ⟨k, _, hk⟩ := hpart v v
      have := (hk j3 hvv).trans (hk j0 ⟨hLv, hRv⟩).symm
      exact h03 this.symm
    let S : Finset (Fin p) := {j0, j1, j2, j3, j4}
    have hScard : S.card = 5 := by
      simp [S, h01, h02, h03, h04, h12, h13, h14, h23, h24, h34]
    have := Finset.card_le_univ S
    simpa [hScard] using this
  · push Not at hbig
    choose f hf using fun ab : Fin 3 × Fin 3 => hpart ab.1 ab.2
    have h9 : (Finset.univ : Finset (Fin 3 × Fin 3)).card =
        ∑ j : Fin p, ((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun ab => f ab = j)).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    have hfib : ∀ j : Fin p,
        ((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun ab => f ab = j)).card ≤ (A j).card * (B j).card := by
      intro j
      rw [← Finset.card_product]
      apply Finset.card_le_card
      intro ⟨a, b⟩ hab
      have hfj : f (a, b) = j := (Finset.mem_filter.mp hab).2
      have hLR : L j a ∧ R j b := hfj ▸ (hf (a, b)).1
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLR.1⟩,
                                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hLR.2⟩⟩
    have hsum : 9 ≤ ∑ _j : Fin p, 2 := by
      calc 9 = (Finset.univ : Finset (Fin 3 × Fin 3)).card := by decide
        _ = ∑ j : Fin p, ((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun ab => f ab = j)).card := h9
        _ ≤ ∑ j : Fin p, (A j).card * (B j).card := Finset.sum_le_sum (fun j _ => hfib j)
        _ ≤ ∑ _j : Fin p, 2 := Finset.sum_le_sum (fun j _ => hbig j)
    simp at hsum
    omega

private lemma part_lower {n r c p : Nat}
    (rowOK : Fin r → Fin 3 → Prop) (colOK : Fin c → Fin 3 → Prop)
    (hnondeg : ∀ i, (∃ x, ¬ rowOK x i) ∧ (∃ y, ¬ colOK y i))
    (left : Fin p → (Fin (n+1) → Fin r) → Prop)
    (right : Fin p → (Fin (n+1) → Fin c) → Prop)
    (tag : Fin p → Fin (n+1) → Fin 3)
    (hpart : ∀ x y, ∃! j : Fin p, left j x ∧ right j y)
    (hok : ∀ j x y, left j x → right j y → ∀ k, rowOK (x k) (tag j k) ∧ colOK (y k) (tag j k)) :
    5 * 3^n ≤ p := by
  classical
  choose xr hxr using fun i : Fin 3 => (hnondeg i).1
  choose yc hyc using fun i : Fin 3 => (hnondeg i).2
  let tailCol : Fin 3 → Fin 3 := fun a => a + 2
  let forcedTag : Fin 3 → Fin 3 := fun a => a + 1
  have hforced : ∀ a t : Fin 3, a ≠ t → tailCol a ≠ t → t = forcedTag a := by
    intro a t h1 h2; fin_cases a <;> fin_cases t <;> simp_all [tailCol, forcedTag]
  let mkRow : Fin 3 → (Fin n → Fin 3) → (Fin (n+1) → Fin r) := fun a0 atail k =>
    Fin.cases (xr a0) (fun k' => xr (atail k')) k
  let mkCol : Fin 3 → (Fin n → Fin 3) → (Fin (n+1) → Fin c) := fun b0 atail k =>
    Fin.cases (yc b0) (fun k' => yc (tailCol (atail k'))) k
  let fib : (Fin n → Fin 3) → Finset (Fin p) := fun atail =>
    Finset.univ.filter (fun j => ∀ k' : Fin n, tag j k'.succ = forcedTag (atail k'))
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin n → Fin 3)) fib := by
    intro a1 _ a2 _ hne
    change Disjoint (fib a1) (fib a2)
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    apply hne; funext k'
    have h1 := (Finset.mem_filter.mp hj1).2 k'
    have h2 := (Finset.mem_filter.mp hj2).2 k'
    have h3 : forcedTag (a1 k') = forcedTag (a2 k') := h1.symm.trans h2
    have hinj : Function.Injective forcedTag := by
      intro x y hxy; fin_cases x <;> fin_cases y <;> simp_all [forcedTag]
    exact hinj h3
  have hfib_card : ∀ atail : Fin n → Fin 3, 5 ≤ (fib atail).card := by
    intro atail
    let e := (fib atail).equivFin
    let hL : Fin (fib atail).card → Fin 3 → Prop := fun j a0 =>
      left (e.symm j).1 (mkRow a0 atail)
    let hR : Fin (fib atail).card → Fin 3 → Prop := fun j b0 =>
      right (e.symm j).1 (mkCol b0 atail)
    let hT : Fin (fib atail).card → Fin 3 := fun j => tag (e.symm j).1 0
    apply lower_3x3 hL hR hT
    · intro a0 b0
      obtain ⟨j, hj, hjuniq⟩ := hpart (mkRow a0 atail) (mkCol b0 atail)
      have hjmem : j ∈ fib atail := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, fun k' => ?_⟩
        have hok' := hok j (mkRow a0 atail) (mkCol b0 atail) hj.1 hj.2 k'.succ
        simp only [mkRow, mkCol, Fin.cases_succ] at hok'
        exact hforced (atail k') (tag j k'.succ)
          (fun h => hxr (atail k') (h ▸ hok'.1))
          (fun h => hyc (tailCol (atail k')) (h ▸ hok'.2))
      refine ⟨e ⟨j, hjmem⟩, ?_, ?_⟩
      · simpa [hL, hR] using hj
      · intro j' hj'
        have heq : (e.symm j').1 = j := hjuniq (e.symm j').1 hj'
        have : e.symm j' = ⟨j, hjmem⟩ := Subtype.ext heq
        exact e.symm_apply_eq.mp this
    · intro j a0 b0 hLa hRb
      have hok0 := hok (e.symm j).1 (mkRow a0 atail) (mkCol b0 atail) hLa hRb 0
      simp only [mkRow, mkCol, Fin.cases_zero] at hok0
      exact ⟨fun h => by dsimp only [hT] at h; rw [← h] at hok0; exact hxr a0 hok0.1,
             fun h => by dsimp only [hT] at h; rw [← h] at hok0; exact hyc b0 hok0.2⟩
  have hle : ∑ atail : Fin n → Fin 3, (fib atail).card ≤ p := by
    rw [← Finset.card_biUnion hdisj]
    exact (Finset.card_le_univ _).trans (by simp)
  have hsum : 5 * 3 ^ n ≤ ∑ atail : Fin n → Fin 3, (fib atail).card := by
    calc 5 * 3 ^ n = ∑ _atail : Fin n → Fin 3, 5 := by simp [mul_comm]
      _ ≤ ∑ atail : Fin n → Fin 3, (fib atail).card := Finset.sum_le_sum (fun a _ => hfib_card a)
  exact hsum.trans hle

end PEqualNP.Outside.L_meta_38163

theorem PEqualNP.Outside.L_meta_38163 : ∀ (n r c : Nat) (rowOK : Fin r → Fin 3 → Prop) (colOK : Fin c → Fin 3 → Prop),
  (∀ x y, ∃ i, rowOK x i ∧ colOK y i) →
  (∀ i, (∃ x, ¬ rowOK x i) ∧ (∃ y, ¬ colOK y i)) →
  let Rows := Fin (n+1) → Fin r
  let Cols := Fin (n+1) → Fin c
  let partition := fun (p : Nat) =>
    ∃ (left : Fin p → Rows → Prop) (right : Fin p → Cols → Prop)
      (tag : Fin p → Fin (n+1) → Fin 3),
      (∀ (x : Rows) (y : Cols), ∃! j : Fin p, left j x ∧ right j y) ∧
      ∀ (j : Fin p) (x : Rows) (y : Cols), left j x → right j y →
        ∀ k, rowOK (x k) (tag j k) ∧ colOK (y k) (tag j k)
  partition (5^(n+1)) ∧ ∀ p, partition p → 5 * 3^n ≤ p := by
  intro n r c rowOK colOK hcover hnondeg
  refine ⟨PEqualNP.Outside.L_meta_38163.part_upper rowOK colOK hcover hnondeg, ?_⟩
  intro p ⟨left, right, tag, hpart, hok⟩
  exact PEqualNP.Outside.L_meta_38163.part_lower rowOK colOK hnondeg left right tag hpart hok
