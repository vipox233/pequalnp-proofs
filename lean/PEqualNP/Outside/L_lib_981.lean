import PEqualNP.Defs
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum

namespace PEqualNP.Outside.L_lib_981_aux

open Finset

def nbr {m n : ℕ} (M : Fin m → Fin n → Bool) (X : Finset (Fin m)) : Finset (Fin n) :=
  Finset.univ.filter (fun x => ∃ a ∈ X, M a x = true)

theorem konig (m n : ℕ) (M : Fin m → Fin n → Bool) :
    ∃ (R : Finset (Fin m)) (C : Finset (Fin n)) (S : Finset (Fin m × Fin n)),
      (∀ a x, M a x = true → a ∈ R ∨ x ∈ C) ∧
      (∀ e ∈ S, M e.1 e.2 = true) ∧ Set.InjOn Prod.fst (S : Set (Fin m × Fin n)) ∧
      Set.InjOn Prod.snd (S : Set (Fin m × Fin n)) ∧ R.card + C.card ≤ S.card := by
  obtain ⟨X0, -, hX0⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset (Fin m)))
    (fun X => (X.card : ℤ) - ((nbr M X).card : ℤ)) Finset.univ_nonempty
  have hemp := hX0 ∅ (Finset.mem_univ _)
  have hnb0 : (nbr M ∅).card = 0 := by
    rw [Finset.card_eq_zero]
    ext x
    simp [nbr]
  simp only [Finset.card_empty, hnb0, Nat.cast_zero, sub_zero] at hemp
  set d := X0.card - (nbr M X0).card with hd
  let t : Fin m → Finset (Fin n ⊕ Fin d) := fun a =>
    (Finset.univ.filter (fun x => M a x = true)).disjSum Finset.univ
  have hall : ∀ s : Finset (Fin m), s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with hs | hs
    · rw [hs]
      simp
    · obtain ⟨a0, ha0⟩ := hs
      have hsub : (nbr M s).disjSum (Finset.univ : Finset (Fin d)) ⊆ s.biUnion t := by
        intro z hz
        rw [Finset.mem_biUnion]
        rcases z with x | z
        · rw [Finset.inl_mem_disjSum] at hz
          simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and] at hz
          obtain ⟨a, ha, hax⟩ := hz
          refine ⟨a, ha, ?_⟩
          simp only [t, Finset.inl_mem_disjSum, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hax
        · refine ⟨a0, ha0, ?_⟩
          simp only [t, Finset.inr_mem_disjSum, Finset.mem_univ]
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_disjSum, Finset.card_univ, Fintype.card_fin] at h1
      have h2 := hX0 s (Finset.mem_univ _)
      omega
  obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  have hfM : ∀ a x, f a = Sum.inl x → M a x = true := by
    intro a x hax
    have h1 := hft a
    rw [hax] at h1
    simp only [t, Finset.inl_mem_disjSum, Finset.mem_filter, Finset.mem_univ, true_and] at h1
    exact h1
  let S : Finset (Fin m × Fin n) := Finset.univ.filter (fun e => f e.1 = Sum.inl e.2)
  have hmemS : ∀ e, e ∈ S ↔ f e.1 = Sum.inl e.2 := by
    intro e
    simp [S]
  have hinj1 : Set.InjOn Prod.fst (S : Set (Fin m × Fin n)) := by
    intro e he e' he' heq
    rw [Finset.mem_coe, hmemS] at he he'
    have h1 : (Sum.inl e.2 : Fin n ⊕ Fin d) = Sum.inl e'.2 := by
      rw [← he, ← he', heq]
    exact Prod.ext heq (Sum.inl_injective h1)
  have hinj2 : Set.InjOn Prod.snd (S : Set (Fin m × Fin n)) := by
    intro e he e' he' heq
    rw [Finset.mem_coe, hmemS] at he he'
    have h1 : f e.1 = f e'.1 := by
      rw [he, he', heq]
    exact Prod.ext (hfinj h1) heq
  let D : Finset (Fin m) := Finset.univ.filter (fun a => ∃ z, f a = Sum.inr z)
  have hD : D.card ≤ d := by
    have h1 : D.image f ⊆ (∅ : Finset (Fin n)).disjSum (Finset.univ : Finset (Fin d)) := by
      intro w hw
      rw [Finset.mem_image] at hw
      obtain ⟨a, ha, rfl⟩ := hw
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨z, hz⟩ := ha
      rw [hz, Finset.inr_mem_disjSum]
      exact Finset.mem_univ z
    have h2 := Finset.card_le_card h1
    rw [Finset.card_image_of_injective _ hfinj, Finset.card_disjSum, Finset.card_empty,
      Finset.card_univ, Fintype.card_fin] at h2
    omega
  have hcov : (Finset.univ : Finset (Fin m)) ⊆ D ∪ S.image Prod.fst := by
    intro a _
    rw [Finset.mem_union]
    rcases hfa : f a with x | z
    · right
      rw [Finset.mem_image]
      exact ⟨(a, x), (hmemS (a, x)).2 hfa, rfl⟩
    · left
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨z, hfa⟩
  have hcard1 := Finset.card_le_card hcov
  have hcard2 := Finset.card_union_le D (S.image Prod.fst)
  rw [Finset.card_image_of_injOn hinj1] at hcard2
  rw [Finset.card_univ, Fintype.card_fin] at hcard1
  refine ⟨Finset.univ \ X0, nbr M X0, S, ?_, ?_, hinj1, hinj2, ?_⟩
  · intro a x hax
    by_cases ha : a ∈ X0
    · right
      simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a, ha, hax⟩
    · left
      simp [ha]
  · intro e he
    exact hfM e.1 e.2 ((hmemS e).1 he)
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ X0), Finset.card_univ, Fintype.card_fin]
    have hX0le : X0.card ≤ m := by
      have h3 := Finset.card_le_card (Finset.subset_univ X0)
      rw [Finset.card_univ, Fintype.card_fin] at h3
      exact h3
    omega

def validR {n m : ℕ} (u v : Fin m → Fin n) (A : Finset (Fin n)) (pin : Fin n → Option Bool)
    (M : Finset (Fin n × Fin n)) : Prop :=
  (∀ p ∈ M, p.1 ∈ A ∧ p.2 ∉ A ∧ pin p.1 = none ∧ pin p.2 = none ∧ ∃ e : Fin m,
    (u e = p.1 ∧ v e = p.2) ∨ (u e = p.2 ∧ v e = p.1)) ∧
  Set.InjOn Prod.fst (↑M : Set (Fin n × Fin n)) ∧ Set.InjOn Prod.snd (↑M : Set (Fin n × Fin n))

def matR {n m : ℕ} (u v : Fin m → Fin n) (A : Finset (Fin n)) (pin : Fin n → Option Bool)
    (w : Fin m → ℚ) : Matrix (Fin n → Bool) (Fin n → Bool) ℚ :=
  fun x y =>
    let s := fun i : Fin n => if i ∈ A then x i else y i
    if (∀ i, pin i = none ∨ pin i = some (s i)) then
      ∏ e : Fin m, (if s (u e) = s (v e) then 1 else w e) else 0

theorem rank_le_of_cover {n m : ℕ} (u v : Fin m → Fin n) (A : Finset (Fin n))
    (pin : Fin n → Option Bool) (R_cov C_cov : Finset (Fin n))
    (hcov : ∀ a b : Fin n, a ∈ A → b ∉ A → pin a = none → pin b = none →
      (∃ e : Fin m, (u e = a ∧ v e = b) ∨ (u e = b ∧ v e = a)) → a ∈ R_cov ∨ b ∈ C_cov)
    (w : Fin m → ℚ) :
    Matrix.rank (matR u v A pin w) ≤ 2 ^ (R_cov.card + C_cov.card) := by
  classical
  let Cfg := (R_cov → Bool) × (C_cov → Bool)
  let okL : (Fin n → Bool) → Prop := fun x => ∀ i ∈ A, pin i = none ∨ pin i = some (x i)
  let okR : (Fin n → Bool) → Prop := fun y => ∀ i ∉ A, pin i = none ∨ pin i = some (y i)
  let crossL : Fin n → Fin n → ℚ → Cfg → (Fin n → Bool) → ℚ := fun a b we c x =>
    match pin a, pin b with
    | some _, _ => 1
    | none, some bb => if x a = bb then 1 else we
    | none, none =>
      if _haR : a ∈ R_cov then 1
      else if hbC : b ∈ C_cov then (if x a = c.2 ⟨b, hbC⟩ then 1 else we)
      else 1
  let crossR : Fin n → Fin n → ℚ → Cfg → (Fin n → Bool) → ℚ := fun a b we c y =>
    match pin a, pin b with
    | some ba, _ => if ba = y b then 1 else we
    | none, some _ => 1
    | none, none =>
      if haR : a ∈ R_cov then (if c.1 ⟨a, haR⟩ = y b then 1 else we)
      else 1
  have hcross : ∀ (a b : Fin n) (we : ℚ) (c : Cfg) (x y : Fin n → Bool),
      a ∈ A → b ∉ A → okL x → okR y →
      (∀ r : R_cov, x r.1 = c.1 r) → (∀ r : C_cov, y r.1 = c.2 r) →
      (pin a = none → pin b = none → a ∈ R_cov ∨ b ∈ C_cov) →
      crossL a b we c x * crossR a b we c y = if x a = y b then 1 else we := by
    intro a b we c x y ha hb hokL hokR hcx hcy hcovab
    dsimp only [crossL, crossR]
    cases hpa : pin a with
    | some ba =>
      have hxa : x a = ba := by
        rcases hokL a ha with h | h
        · rw [hpa] at h; cases h
        · rw [hpa] at h; exact (Option.some.inj h).symm
      simp [hxa]
    | none =>
      cases hpb : pin b with
      | some bb =>
        have hyb : y b = bb := by
          rcases hokR b hb with h | h
          · rw [hpb] at h; cases h
          · rw [hpb] at h; exact (Option.some.inj h).symm
        simp [hyb]
      | none =>
        by_cases haR : a ∈ R_cov
        · simp only [dif_pos haR, one_mul, ← hcx ⟨a, haR⟩]
        · have hbC : b ∈ C_cov := (hcovab hpa hpb).resolve_left haR
          simp only [dif_neg haR, dif_pos hbC, mul_one, ← hcy ⟨b, hbC⟩]
  let facL : Cfg → (Fin n → Bool) → Fin m → ℚ := fun c x e =>
    if u e ∈ A then
      if v e ∈ A then (if x (u e) = x (v e) then 1 else w e)
      else crossL (u e) (v e) (w e) c x
    else
      if v e ∈ A then crossL (v e) (u e) (w e) c x
      else 1
  let facR : Cfg → (Fin n → Bool) → Fin m → ℚ := fun c y e =>
    if u e ∈ A then
      if v e ∈ A then 1
      else crossR (u e) (v e) (w e) c y
    else
      if v e ∈ A then crossR (v e) (u e) (w e) c y
      else (if y (u e) = y (v e) then 1 else w e)
  let P : Matrix (Fin n → Bool) Cfg ℚ := fun x c =>
    if okL x ∧ (∀ r : R_cov, x r.1 = c.1 r) then ∏ e : Fin m, facL c x e else 0
  let Q : Matrix Cfg (Fin n → Bool) ℚ := fun c y =>
    if okR y ∧ (∀ r : C_cov, y r.1 = c.2 r) then ∏ e : Fin m, facR c y e else 0
  have hPQ : P * Q = matR u v A pin w := by
    ext x y
    rw [Matrix.mul_apply]
    let c0 : Cfg := (fun r => x r.1, fun r => y r.1)
    have hsum : (∑ c : Cfg, P x c * Q c y) = P x c0 * Q c0 y := by
      apply Finset.sum_eq_single c0
      · intro c _ hne
        by_cases h1 : ∀ r : R_cov, x r.1 = c.1 r
        · have h2 : ¬ ∀ r : C_cov, y r.1 = c.2 r := by
            intro h2
            apply hne
            exact Prod.ext (funext (fun r => (h1 r).symm)) (funext (fun r => (h2 r).symm))
          dsimp only [Q]
          rw [if_neg (fun h => h2 h.2), mul_zero]
        · dsimp only [P]
          rw [if_neg (fun h => h1 h.2), zero_mul]
      · intro h; exact absurd (Finset.mem_univ c0) h
    rw [hsum]
    have hok_iff : (∀ i : Fin n, pin i = none ∨ pin i = some (if i ∈ A then x i else y i)) ↔
        okL x ∧ okR y := by
      constructor
      · intro h
        exact ⟨fun i hi => by simpa [hi] using h i, fun i hi => by simpa [hi] using h i⟩
      · rintro ⟨hL, hR⟩ i
        by_cases hi : i ∈ A
        · simpa [hi] using hL i hi
        · simpa [hi] using hR i hi
    dsimp only [matR]
    by_cases hok : okL x ∧ okR y
    · rw [if_pos (hok_iff.2 hok)]
      have hP0 : P x c0 = ∏ e : Fin m, facL c0 x e := by
        dsimp only [P, c0]
        rw [if_pos ⟨hok.1, fun _ => rfl⟩]
      have hQ0 : Q c0 y = ∏ e : Fin m, facR c0 y e := by
        dsimp only [Q, c0]
        rw [if_pos ⟨hok.2, fun _ => rfl⟩]
      rw [hP0, hQ0, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro e _
      dsimp only [facL, facR]
      by_cases hu : u e ∈ A <;> by_cases hv : v e ∈ A
      · simp [hu, hv]
      · simp only [if_pos hu, if_neg hv]
        exact hcross (u e) (v e) (w e) c0 x y hu hv hok.1 hok.2 (fun _ => rfl) (fun _ => rfl)
          (fun hpu hpv => hcov (u e) (v e) hu hv hpu hpv ⟨e, Or.inl ⟨rfl, rfl⟩⟩)
      · simp only [if_neg hu, if_pos hv]
        rw [hcross (v e) (u e) (w e) c0 x y hv hu hok.1 hok.2 (fun _ => rfl) (fun _ => rfl)
          (fun hpv hpu => hcov (v e) (u e) hv hu hpv hpu ⟨e, Or.inr ⟨rfl, rfl⟩⟩)]
        by_cases heq : y (u e) = x (v e)
        · rw [if_pos heq.symm, if_pos heq]
        · rw [if_neg (Ne.symm heq), if_neg heq]
      · simp [hu, hv]
    · rw [if_neg (fun h => hok (hok_iff.1 h))]
      by_cases hL : okL x
      · have hR : ¬ okR y := fun hR => hok ⟨hL, hR⟩
        dsimp only [Q]
        rw [if_neg (fun h => hR h.1), mul_zero]
      · dsimp only [P]
        rw [if_neg (fun h => hL h.1), zero_mul]
  rw [← hPQ]
  have hcard : Fintype.card Cfg = 2 ^ (R_cov.card + C_cov.card) := by
    simp only [Cfg, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
      pow_add]
  calc (P * Q).rank ≤ P.rank := Matrix.rank_mul_le_left P Q
    _ ≤ Fintype.card Cfg := Matrix.rank_le_card_width P
    _ = 2 ^ (R_cov.card + C_cov.card) := hcard

theorem lower_poly {n m : ℕ} (u v : Fin m → Fin n) (A : Finset (Fin n))
    (pin : Fin n → Option Bool) (M : Finset (Fin n × Fin n))
    (hM : validR u v A pin M) :
    ∃ poly : MvPolynomial (Fin m) ℚ,
      poly ≠ 0 ∧
      (∀ e : Fin m, poly.degreeOf e ≤ 2 ^ M.card) ∧
      (∀ w : Fin m → ℚ, MvPolynomial.eval w poly ≠ 0 →
        2 ^ M.card ≤ Matrix.rank (matR u v A pin w)) := by
  classical
  rcases hM with ⟨hMp, hinj1, hinj2⟩
  let edgeOf : M → Fin m := fun p => Classical.choose (hMp p.1 p.2).2.2.2.2
  have hedgeOf : ∀ p : M, (u (edgeOf p) = p.1.1 ∧ v (edgeOf p) = p.1.2) ∨
      (u (edgeOf p) = p.1.2 ∧ v (edgeOf p) = p.1.1) :=
    fun p => Classical.choose_spec (hMp p.1 p.2).2.2.2.2
  have hedge_inj : Function.Injective edgeOf := by
    intro p q hpq
    have hp := hedgeOf p
    have hq := hedgeOf q
    rw [hpq] at hp
    have hpA : p.1.1 ∈ A := (hMp p.1 p.2).1
    have hpB : p.1.2 ∉ A := (hMp p.1 p.2).2.1
    have hqA : q.1.1 ∈ A := (hMp q.1 q.2).1
    have hqB : q.1.2 ∉ A := (hMp q.1 q.2).2.1
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hq with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact Subtype.ext (Prod.ext (h1.symm.trans h3) (h2.symm.trans h4))
    · exact absurd (h1.symm.trans h3 ▸ hpA) hqB
    · exact absurd (h3.symm.trans h1 ▸ hqA) hpB
    · exact Subtype.ext (Prod.ext (h2.symm.trans h4) (h1.symm.trans h3))
  let s0 : Fin n → Bool := fun i => (pin i).getD false
  have hs0 : ∀ i, pin i = none ∨ pin i = some (s0 i) := by
    intro i
    cases h : pin i <;> simp [s0, h]
  let xsel : (M → Bool) → (Fin n → Bool) := fun α i =>
    if h : ∃ p : M, p.1.1 = i then α h.choose else s0 i
  let ysel : (M → Bool) → (Fin n → Bool) := fun β i =>
    if h : ∃ p : M, p.1.2 = i then β h.choose else s0 i
  let s_ab : (M → Bool) → (M → Bool) → (Fin n → Bool) := fun α β i =>
    if i ∈ A then xsel α i else ysel β i
  have hxsel_p : ∀ α (p : M), xsel α p.1.1 = α p := by
    intro α p
    have h : ∃ q : M, q.1.1 = p.1.1 := ⟨p, rfl⟩
    dsimp only [xsel]
    rw [dif_pos h]
    have hq : h.choose = p := Subtype.ext (hinj1 h.choose.2 p.2 h.choose_spec)
    rw [hq]
  have hysel_p : ∀ β (p : M), ysel β p.1.2 = β p := by
    intro β p
    have h : ∃ q : M, q.1.2 = p.1.2 := ⟨p, rfl⟩
    dsimp only [ysel]
    rw [dif_pos h]
    have hq : h.choose = p := Subtype.ext (hinj2 h.choose.2 p.2 h.choose_spec)
    rw [hq]
  have hsab_fst : ∀ α β (p : M), s_ab α β p.1.1 = α p := by
    intro α β p
    dsimp only [s_ab]
    rw [if_pos (hMp p.1 p.2).1, hxsel_p]
  have hsab_snd : ∀ α β (p : M), s_ab α β p.1.2 = β p := by
    intro α β p
    dsimp only [s_ab]
    rw [if_neg (hMp p.1 p.2).2.1, hysel_p]
  have hsab_ok : ∀ α β i, pin i = none ∨ pin i = some (s_ab α β i) := by
    intro α β i
    dsimp only [s_ab]
    by_cases hi : i ∈ A
    · rw [if_pos hi]
      dsimp only [xsel]
      by_cases h : ∃ p : M, p.1.1 = i
      · obtain ⟨p, rfl⟩ := h
        exact Or.inl (hMp p.1 p.2).2.2.1
      · rw [dif_neg h]
        exact hs0 i
    · rw [if_neg hi]
      dsimp only [ysel]
      by_cases h : ∃ p : M, p.1.2 = i
      · obtain ⟨p, rfl⟩ := h
        exact Or.inl (hMp p.1 p.2).2.2.2.1
      · rw [dif_neg h]
        exact hs0 i
  let MP : Matrix (M → Bool) (M → Bool) (MvPolynomial (Fin m) ℚ) := fun α β =>
    ∏ e : Fin m, (if s_ab α β (u e) = s_ab α β (v e) then 1 else MvPolynomial.X e)
  have hev : ∀ w : Fin m → ℚ,
      MvPolynomial.eval w MP.det = ((matR u v A pin w).submatrix xsel ysel).det := by
    intro w
    rw [RingHom.map_det]
    congr 1
    ext α β
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, matR]
    dsimp only [MP]
    have hok : ∀ i : Fin n, pin i = none ∨ pin i = some (if i ∈ A then xsel α i else ysel β i) :=
      hsab_ok α β
    rw [if_pos hok, map_prod]
    apply Finset.prod_congr rfl
    intro e _
    dsimp only [s_ab]
    split_ifs <;> simp
  let wstar : Fin m → ℚ := fun e => if e ∈ Finset.univ.image edgeOf then 2 else 1
  let N : Matrix (M → Bool) (M → Bool) ℚ := (matR u v A pin wstar).submatrix xsel ysel
  have hN_eq : ∀ α β, N α β = ∏ p : M, (if α p = β p then (1 : ℚ) else 2) := by
    intro α β
    simp only [N, Matrix.submatrix_apply, matR]
    have hok : ∀ i : Fin n, pin i = none ∨ pin i = some (if i ∈ A then xsel α i else ysel β i) :=
      hsab_ok α β
    rw [if_pos hok]
    change (∏ e : Fin m, if s_ab α β (u e) = s_ab α β (v e) then (1 : ℚ) else wstar e) = _
    have hsub : (∏ e : Fin m, if s_ab α β (u e) = s_ab α β (v e) then (1 : ℚ) else wstar e) =
        ∏ e ∈ Finset.univ.image edgeOf,
          if s_ab α β (u e) = s_ab α β (v e) then (1 : ℚ) else wstar e := by
      symm
      apply Finset.prod_subset (Finset.subset_univ _)
      intro e _ hne
      dsimp only [wstar]
      rw [if_neg hne, ite_self]
    rw [hsub, Finset.prod_image (fun a _ b _ h => hedge_inj h)]
    apply Finset.prod_congr rfl
    intro p _
    have hmem : edgeOf p ∈ Finset.univ.image edgeOf :=
      Finset.mem_image.2 ⟨p, Finset.mem_univ p, rfl⟩
    have hw : wstar (edgeOf p) = 2 := if_pos hmem
    rw [hw]
    rcases hedgeOf p with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · rw [hu, hv, hsab_fst, hsab_snd]
    · rw [hu, hv, hsab_snd, hsab_fst]
      by_cases heq : α p = β p
      · rw [if_pos heq.symm, if_pos heq]
      · rw [if_neg (Ne.symm heq), if_neg heq]
  let Ninv : Matrix (M → Bool) (M → Bool) ℚ := fun β γ =>
    ∏ p : M, (if β p = γ p then (-1 / 3 : ℚ) else (2 / 3 : ℚ))
  have hNNinv : N * Ninv = 1 := by
    ext α γ
    have hmul : (N * Ninv) α γ = ∏ p : M, ∑ b : Bool,
        (if α p = b then (1 : ℚ) else 2) * (if b = γ p then (-1 / 3 : ℚ) else (2 / 3 : ℚ)) := by
      rw [Matrix.mul_apply]
      symm
      rw [Finset.prod_univ_sum (t := fun _ : M => (Finset.univ : Finset Bool)),
        Fintype.piFinset_univ]
      apply Finset.sum_congr rfl
      intro β _
      rw [hN_eq α β]
      dsimp only [Ninv]
      rw [Finset.prod_mul_distrib]
    have hbool : ∀ a c : Bool,
        (∑ b : Bool, (if a = b then (1 : ℚ) else 2) *
          (if b = c then (-1 / 3 : ℚ) else (2 / 3 : ℚ))) = if a = c then 1 else 0 := by
      intro a c
      cases a <;> cases c <;> simp [Fintype.sum_bool] <;> norm_num
    rw [hmul]
    simp only [hbool, Matrix.one_apply]
    by_cases h : α = γ
    · subst h
      simp
    · rw [if_neg h]
      have hex : ∃ p : M, α p ≠ γ p := by
        by_contra hall
        push_neg at hall
        exact h (funext hall)
      obtain ⟨p, hp⟩ := hex
      exact Finset.prod_eq_zero (Finset.mem_univ p) (if_neg hp)
  have hNdet : N.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hNNinv
    rw [Matrix.det_mul, Matrix.det_one, h0, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨MP.det, ?_, ?_, ?_⟩
  · intro h0
    have h1 := hev wstar
    rw [h0, map_zero] at h1
    exact hNdet h1.symm
  · intro e
    have hentry : ∀ α β, (MP α β).degreeOf e ≤ 1 := by
      intro α β
      refine (MvPolynomial.degreeOf_prod_le _ _ _).trans ?_
      calc ∑ e' : Fin m, (if s_ab α β (u e') = s_ab α β (v e') then
            (1 : MvPolynomial (Fin m) ℚ) else MvPolynomial.X e').degreeOf e
          ≤ ∑ e' : Fin m, if e = e' then 1 else 0 := by
            refine Finset.sum_le_sum (fun e' _ => ?_)
            split_ifs <;> simp_all [MvPolynomial.degreeOf_X]
        _ = 1 := by simp
    rw [Matrix.det_apply]
    refine (MvPolynomial.degreeOf_sum_le _ _ _).trans (Finset.sup_le (fun σ _ => ?_))
    have hprod : (∏ i : M → Bool, MP (σ i) i).degreeOf e ≤ 2 ^ M.card := by
      refine (MvPolynomial.degreeOf_prod_le _ _ _).trans ?_
      calc ∑ i : M → Bool, (MP (σ i) i).degreeOf e
          ≤ ∑ _i : M → Bool, 1 := Finset.sum_le_sum (fun i _ => hentry _ _)
        _ = 2 ^ M.card := by
            simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h, one_smul]; exact hprod
    · rw [h, Units.neg_smul, one_smul, MvPolynomial.degreeOf_neg]; exact hprod
  · intro w hw
    rw [hev] at hw
    have h1 := Matrix.rank_submatrix_le (matR u v A pin w) xsel ysel
    have h2 : ((matR u v A pin w).submatrix xsel ysel).rank = Fintype.card (M → Bool) :=
      Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hw))
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at h2
    omega

end PEqualNP.Outside.L_lib_981_aux

theorem PEqualNP.Outside.L_lib_981 : (∀ (n m : ℕ) (u v : Fin m → Fin n),
  let I := Fin n
  let X := I → Bool
  let valid := fun (A : Finset I) (pin : I → Option Bool) (M : Finset (I × I)) =>
    (∀ p ∈ M, p.1 ∈ A ∧ p.2 ∉ A ∧ pin p.1 = none ∧ pin p.2 = none ∧ ∃ e : Fin m,
      (u e = p.1 ∧ v e = p.2) ∨ (u e = p.2 ∧ v e = p.1)) ∧
    Set.InjOn Prod.fst (↑M : Set (I × I)) ∧ Set.InjOn Prod.snd (↑M : Set (I × I))
  let ν := fun (A : Finset I) (pin : I → Option Bool) => ((Finset.univ : Finset (Finset (I × I))).filter
    (fun M : Finset (I × I) => @decide (valid A pin M) (Classical.propDecidable _))).sup Finset.card
  let mat := fun (A : Finset I) (pin : I → Option Bool) (w : Fin m → ℚ) => (fun (x y : X) =>
    let s := fun i : I => if i ∈ A then x i else y i
    if (∀ i, pin i = none ∨ pin i = some (s i)) then
      ∏ e : Fin m, (if s (u e) = s (v e) then 1 else w e) else 0 : Matrix X X ℚ)
  (∀ (A : Finset I) (pin : I → Option Bool) (w : Fin m → ℚ),
    Matrix.rank (mat A pin w) ≤ 2^(ν A pin)) ∧
    ∃ z : Fin m → ℕ, (∀ e, 2 ≤ z e ∧ z e ≤ (m+1)*16^(n+1)) ∧
      ∀ (A : Finset I) (pin : I → Option Bool),
        Matrix.rank (mat A pin (fun e => (z e : ℚ))) = 2^(ν A pin)) := by
  intro n m u v I X valid ν mat
  have hν_le : ∀ A pin M, PEqualNP.Outside.L_lib_981_aux.validR u v A pin M →
      M.card ≤ ν A pin := by
    intro A pin M hM
    exact Finset.le_sup (f := Finset.card)
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, @decide_eq_true _ (Classical.propDecidable _) hM⟩)
  have hν_att : ∀ A pin, ∃ M, PEqualNP.Outside.L_lib_981_aux.validR u v A pin M ∧
      M.card = ν A pin := by
    intro A pin
    have hne : (Finset.univ.filter
        (fun M : Finset (I × I) => @decide (valid A pin M) (Classical.propDecidable _))).Nonempty :=
      ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, @decide_eq_true _ (Classical.propDecidable _)
        ⟨fun p hp => by simp at hp, by simp [Set.InjOn], by simp [Set.InjOn]⟩⟩⟩
    obtain ⟨M, hM, hMν⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
    exact ⟨M, @of_decide_eq_true _ (Classical.propDecidable _) (Finset.mem_filter.1 hM).2,
      hMν.symm⟩
  have hν_le_n : ∀ A pin, ν A pin ≤ n := by
    intro A pin
    obtain ⟨M, hM, hMc⟩ := hν_att A pin
    rw [← hMc, ← Finset.card_image_of_injOn hM.2.1]
    exact (Finset.card_le_card (Finset.subset_univ _)).trans (by simp)
  have part1 : ∀ (A : Finset I) (pin : I → Option Bool) (w : Fin m → ℚ),
      Matrix.rank (mat A pin w) ≤ 2 ^ (ν A pin) := by
    intro A pin w
    let B : Fin n → Fin n → Bool := fun a b =>
      @decide (a ∈ A ∧ b ∉ A ∧ pin a = none ∧ pin b = none ∧ ∃ e : Fin m,
        (u e = a ∧ v e = b) ∨ (u e = b ∧ v e = a)) (Classical.propDecidable _)
    obtain ⟨R_cov, C_cov, S, hcov, hS, hinj1, hinj2, hcard⟩ :=
      PEqualNP.Outside.L_lib_981_aux.konig n n B
    have hSvalid : PEqualNP.Outside.L_lib_981_aux.validR u v A pin S := by
      refine ⟨fun p hp => ?_, hinj1, hinj2⟩
      exact @of_decide_eq_true _ (Classical.propDecidable _) (hS p hp)
    have hcov' : ∀ a b : Fin n, a ∈ A → b ∉ A → pin a = none → pin b = none →
        (∃ e : Fin m, (u e = a ∧ v e = b) ∨ (u e = b ∧ v e = a)) → a ∈ R_cov ∨ b ∈ C_cov := by
      intro a b ha hb hpa hpb he
      exact hcov a b (@decide_eq_true _ (Classical.propDecidable _) ⟨ha, hb, hpa, hpb, he⟩)
    exact (PEqualNP.Outside.L_lib_981_aux.rank_le_of_cover u v A pin R_cov C_cov hcov' w).trans
      (Nat.pow_le_pow_right (by norm_num) (hcard.trans (hν_le A pin S hSvalid)))
  refine ⟨part1, ?_⟩
  have hpoly : ∀ (A : Finset I) (pin : I → Option Bool), ∃ p : MvPolynomial (Fin m) ℚ, p ≠ 0 ∧
      (∀ e, p.degreeOf e ≤ 2 ^ (ν A pin)) ∧
      ∀ w, MvPolynomial.eval w p ≠ 0 → 2 ^ (ν A pin) ≤ Matrix.rank (mat A pin w) := by
    intro A pin
    obtain ⟨M, hM, hMc⟩ := hν_att A pin
    rw [← hMc]
    exact PEqualNP.Outside.L_lib_981_aux.lower_poly u v A pin M hM
  choose p hp0 hpd hpe using hpoly
  let Idx := Finset I × (I → Option Bool)
  let Qtot : MvPolynomial (Fin m) ℚ := ∏ ap : Idx, p ap.1 ap.2
  have hQ0 : Qtot ≠ 0 := Finset.prod_ne_zero_iff.2 (fun ap _ => hp0 ap.1 ap.2)
  have hcardIdx : Fintype.card Idx = 6 ^ n := by
    simp only [Idx, I, Fintype.card_prod, Fintype.card_finset, Fintype.card_fun,
      Fintype.card_option, Fintype.card_bool, Fintype.card_fin]
    rw [← mul_pow]
    norm_num
  have hQd : ∀ e : Fin m, Qtot.degreeOf e ≤ 16 ^ n := by
    intro e
    calc Qtot.degreeOf e
        ≤ ∑ ap : Idx, (p ap.1 ap.2).degreeOf e := MvPolynomial.degreeOf_prod_le _ _ _
      _ ≤ ∑ _ap : Idx, 2 ^ n :=
          Finset.sum_le_sum (fun ap _ =>
            (hpd ap.1 ap.2 e).trans (Nat.pow_le_pow_right (by norm_num) (hν_le_n ap.1 ap.2)))
      _ = 12 ^ n := by
          rw [Finset.sum_const, Finset.card_univ, hcardIdx, smul_eq_mul, ← mul_pow]
          norm_num
      _ ≤ 16 ^ n := Nat.pow_le_pow_left (by norm_num) n
  have hcardS : ((Finset.Icc 2 ((m + 1) * 16 ^ (n + 1))).image
      (fun t : ℕ => (t : ℚ))).card = (m + 1) * 16 ^ (n + 1) + 1 - 2 := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Nat.card_Icc]
  have hdeg : ∀ e : Fin m, Qtot.degreeOf e <
      ((Finset.Icc 2 ((m + 1) * 16 ^ (n + 1))).image (fun t : ℕ => (t : ℚ))).card := by
    intro e
    rw [hcardS]
    have h1 : 1 ≤ 16 ^ n := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 16 * 16 ^ n ≤ (m + 1) * 16 ^ (n + 1) := by
      calc 16 * 16 ^ n = 1 * (16 * 16 ^ n) := (one_mul _).symm
        _ ≤ (m + 1) * (16 * 16 ^ n) := Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.zero_le m))
        _ = (m + 1) * 16 ^ (n + 1) := by rw [pow_succ, mul_comm (16 ^ n) 16]
    have h3 := hQd e
    omega
  obtain ⟨x, hxS, hx⟩ : ∃ x : Fin m → ℚ, (∀ e, x e ∈
      (Finset.Icc 2 ((m + 1) * 16 ^ (n + 1))).image (fun t : ℕ => (t : ℚ))) ∧
      MvPolynomial.eval x Qtot ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hQ0 (MvPolynomial.eq_zero_of_eval_zero_at_prod_finset _ _ hdeg hcon)
  have hz : ∀ e, ∃ t : ℕ, t ∈ Finset.Icc 2 ((m + 1) * 16 ^ (n + 1)) ∧ (t : ℚ) = x e :=
    fun e => Finset.mem_image.1 (hxS e)
  choose z hzI hzx using hz
  refine ⟨z, fun e => Finset.mem_Icc.1 (hzI e), fun A pin => ?_⟩
  have hw : (fun e => (z e : ℚ)) = x := funext hzx
  apply le_antisymm (part1 A pin _)
  rw [hw]
  apply hpe A pin x
  intro h0
  apply hx
  rw [map_prod]
  exact Finset.prod_eq_zero (i := (A, pin)) (Finset.mem_univ _) h0
