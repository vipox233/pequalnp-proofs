import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_735

lemma add_self (x : ZMod 2) : x + x = 0 := by
  have h := ZMod.natCast_self 2
  linear_combination x * h

lemma sum_affine (a : ZMod 2) : ∑ x : ZMod 2, (a + x) = 1 := by
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [hu]
  simp [← add_assoc, add_self]

lemma monomial_sum {m : Nat} {J : Type*} [DecidableEq J]
    (T : Finset J) (coord : J → Option (Fin m))
    (hcard : T.card ≤ m) (a : J → ZMod 2) :
    (∑ u : Fin m → ZMod 2,
      ∏ j ∈ T, (a j + (coord j).elim 0 u)) =
    (if ∀ k : Fin m, ∃ j ∈ T, coord j = some k then 1 else 0) := by
  classical
  by_cases hc : ∀ k : Fin m, ∃ j ∈ T, coord j = some k
  · rw [ite_eq_left hc]
    choose g hg hcoord using hc
    let f : Fin m → T := fun k => ⟨g k, hg k⟩
    have hf : Function.Injective f := by
      intro k l h
      have e := congrArg (fun j : T => coord j.val) h
      simpa [f, hcoord] using e
    have hbij : Function.Bijective f := by
      apply (Fintype.bijective_iff_injective_and_card f).2
      refine ⟨hf, ?_⟩
      have hh := Fintype.card_le_of_injective f hf
      simpa only [Fintype.card_fin, Fintype.card_coe] using
        Nat.le_antisymm hh (by simpa using hcard)
    let e : Fin m ≃ T := Equiv.ofBijective f hbij
    have hp (u : Fin m → ZMod 2) :
        (∏ j ∈ T, (a j + (coord j).elim 0 u)) =
        ∏ k : Fin m, (a (g k) + u k) := by
      rw [← Finset.prod_coe_sort T]
      rw [← e.prod_comp]
      simp [e, f, hcoord]
    simp_rw [hp]
    rw [← Fintype.prod_sum]
    simp [sum_affine]
  · rw [ite_eq_right hc]
    push Not at hc
    obtain ⟨k, hk⟩ := hc
    let flip : (Fin m → ZMod 2) → (Fin m → ZMod 2) :=
      fun u => Function.update u k (u k + 1)
    have hcoord (j : J) (hj : j ∈ T) (u : Fin m → ZMod 2) :
        (coord j).elim 0 (flip u) = (coord j).elim 0 u := by
      cases he : coord j with
      | none => rfl
      | some l =>
        have hne : l ≠ k := by
          intro h; exact hk j hj (by simpa [h] using he)
        simp [flip, hne]
    apply Finset.sum_involution (fun u _ => flip u)
    · intro u hu
      have he :
          (∏ j ∈ T, (a j + (coord j).elim 0 (flip u))) =
          ∏ j ∈ T, (a j + (coord j).elim 0 u) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [hcoord j hj u]
      rw [he, add_self]
    · intro u hu hn he
      have h := congrFun he k
      simp [flip] at h
    · intro u hu
      exact Finset.mem_univ _
    · intro u hu
      ext l
      by_cases h : l = k
      · subst l; simp [flip, add_assoc, add_self]
      · simp [flip, h]

abbrev K := ZMod 2
abbrev U (m : Nat) := Fin m → K
abbrev H (h : Nat) := Fin h → K
abbrev I (m h : Nat) := U m × H h
abbrev W (m h : Nat) := I m h → I m h
abbrev V (m h : Nat) := I m h → K
abbrev J (m h : Nat) := I m h × (Fin m ⊕ Fin h)

def bit {m h : Nat} (x : W m h) (j : J m h) : K :=
  Sum.elim (x j.1).1 (x j.1).2 j.2

def Low {m h : Nat} (P : W m h → V m h) : Prop :=
  ∀ i, ∃ T : Finset (Finset (J m h)),
    (∀ mon ∈ T, mon.card ≤ m) ∧
    ∀ x, P x i = ∑ mon ∈ T, ∏ j ∈ mon, bit x j

def shift {m h : Nat} (u : U m) (x : W m h) : W m h :=
  fun i => ((x i).1 + u, (x i).2)

lemma low_shift_sum {m h : Nat} (P : W m h → V m h) (hP : Low P)
    (x y : W m h) (i : I m h) :
    (∑ u : U m, P (shift u x) i) = ∑ u : U m, P (shift u y) i := by
  classical
  obtain ⟨T, hT, hrep⟩ := hP i
  simp_rw [hrep]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mon hmon
  let coord : J m h → Option (Fin m) :=
    fun j => Sum.elim some (fun _ => none) j.2
  have he (z : W m h) (u : U m) (j : J m h) :
      bit (shift u z) j = bit z j + (coord j).elim 0 u := by
    rcases j with ⟨j, k | k⟩ <;> simp [bit, shift, coord]
  simp_rw [he]
  rw [monomial_sum mon coord (hT mon hmon),
    monomial_sum mon coord (hT mon hmon)]

lemma orbit_cover_bound {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] (e : B → Equiv.Perm A) (good bad : Finset A)
    (hcover : ∀ a, a ∈ good ∨ ∃ b, e b a ∈ bad) :
    Fintype.card A ≤ good.card + Fintype.card B * bad.card := by
  classical
  have hp (a : A) : 1 ≤ (if a ∈ good then 1 else 0) +
      ∑ b : B, if e b a ∈ bad then 1 else 0 := by
    rcases hcover a with ha | ⟨b, hb⟩
    · simp [ha]
    · have hh := Finset.single_le_sum
        (f := fun b : B => if e b a ∈ bad then (1 : Nat) else 0)
        (fun b _ => Nat.zero_le _) (Finset.mem_univ b)
      simp only [hb, ite_true] at hh
      omega
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset A)) (fun a _ => hp a)
  simp only [Finset.sum_add_distrib] at hh
  rw [Finset.sum_comm] at hh
  have he (b : B) :
      (∑ a : A, if e b a ∈ bad then (1 : Nat) else 0) = bad.card := by
    calc
      _ = ∑ a : A, if a ∈ bad then (1 : Nat) else 0 :=
        Equiv.sum_comp (e b) (fun a : A => if a ∈ bad then (1 : Nat) else 0)
      _ = _ := by simp
  simp_rw [he] at hh
  simpa using hh

lemma card_extensions_le {A : Type*} [Fintype A] [DecidableEq A]
    (S : Finset A) (f : S → A) :
    (Finset.univ.filter (fun p : Equiv.Perm A => ∀ a : S, p a = f a)).card ≤
      (Fintype.card A - S.card).factorial := by
  classical
  let X := Finset.univ.filter (fun p : Equiv.Perm A => ∀ a : S, p a = f a)
  by_cases hx : X.Nonempty
  · obtain ⟨q, hq⟩ := hx
    have hq' : ∀ a : S, q a = f a := (Finset.mem_filter.mp hq).2
    have key : ∀ p : Equiv.Perm A, (∀ a : S, p a = f a) ↔
        (∀ a, ¬ (a ∉ S) → (Equiv.mulLeft q⁻¹ p) a = a) := by
      intro p
      constructor
      · intro hp a ha
        have ha' : a ∈ S := by simpa using ha
        change q⁻¹ (p a) = a
        rw [Equiv.Perm.inv_eq_iff_eq, hp ⟨a, ha'⟩, hq' ⟨a, ha'⟩]
      · intro hp a
        have hh := hp a (not_not.mpr a.property)
        change q⁻¹ (p a) = a at hh
        rw [Equiv.Perm.inv_eq_iff_eq] at hh
        exact hh.trans (hq' a)
    let e := (Equiv.subtypeEquiv (Equiv.mulLeft q⁻¹) key).trans
      (Equiv.Perm.subtypeEquivSubtypePerm (fun a => a ∉ S)).symm
    have he : (Finset.univ.filter
        (fun p : Equiv.Perm A => ∀ a : S, p a = f a)).card =
        (Fintype.card A - S.card).factorial := by
      rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_perm,
        Fintype.card_subtype, Finset.filter_not, Finset.filter_mem_eq_inter,
        Finset.univ_inter, Finset.card_univ_sdiff]
    exact he.le
  · have he : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hx
    change X.card ≤ _
    simp [he]

lemma card_fiber_bound {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) (k : Nat)
    (hf : ∀ b, Fintype.card {a // f a = b} ≤ k) :
    Fintype.card A ≤ Fintype.card B * k := by
  classical
  calc
    _ = ∑ b, Fintype.card {a // f a = b} := by
      rw [← Fintype.card_sigma]
      exact Fintype.card_congr (Equiv.sigmaFiberEquiv f).symm
    _ ≤ ∑ _ : B, k := Finset.sum_le_sum (fun b _ => hf b)
    _ = _ := by simp

lemma card_transversals_le {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (S : Finset (A × B)) :
    (Finset.univ.filter (fun p : Equiv.Perm (A × B) =>
      Function.Bijective (fun i : S => (p i).1))).card ≤
        Fintype.card B ^ Fintype.card A * (Fintype.card A).factorial *
          (Fintype.card (A × B) - Fintype.card A).factorial := by
  classical
  let G := {p : Equiv.Perm (A × B) //
    Function.Bijective (fun i : S => (p i).1)}
  by_cases hg : Nonempty G
  · let q : G := Classical.choice hg
    have hS : S.card = Fintype.card A := by
      simpa using Fintype.card_of_bijective q.property
    let eS : S ≃ A := Equiv.ofBijective _ q.property
    let code : G → (S ≃ A) × (S → B) :=
      fun p => (Equiv.ofBijective _ p.property, fun i => (p.val i).2)
    have hf (v : (S ≃ A) × (S → B)) :
        Fintype.card {p : G // code p = v} ≤
        (Fintype.card (A × B) - Fintype.card A).factorial := by
      let f : S → A × B := fun i => (v.1 i, v.2 i)
      let E := {p : Equiv.Perm (A × B) // ∀ i : S, p i = f i}
      let emb : {p : G // code p = v} → E := fun p =>
        ⟨p.val.val, by
          intro i
          have h1 := congrArg (fun z : (S ≃ A) × (S → B) => z.1 i) p.property
          have h2 := congrArg (fun z : (S ≃ A) × (S → B) => z.2 i) p.property
          exact Prod.ext h1 h2⟩
      have hi : Function.Injective emb := by
        intro p r h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : E => z.val) h
      calc
        _ ≤ Fintype.card E := Fintype.card_le_of_injective emb hi
        _ ≤ _ := by
          simpa only [E, ← Fintype.card_subtype, hS] using card_extensions_le S f
    have hh := card_fiber_bound code _ hf
    rw [Fintype.card_prod, Fintype.card_equiv eS, Fintype.card_fun,
      Fintype.card_coe, hS] at hh
    simpa only [G, Fintype.card_subtype, mul_comm] using hh
  · have hh : (Finset.univ.filter (fun p : Equiv.Perm (A × B) =>
        Function.Bijective (fun i : S => (p i).1))) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro p hp h
      exact hg ⟨⟨p, h⟩⟩
    rw [hh]
    exact Nat.zero_le _

lemma vec_add_self {k : Nat} (u : Fin k → K) : u + u = 0 := by
  ext i
  exact add_self _

def prefixPerm {m h : Nat} (u : U m) : Equiv.Perm (I m h) where
  toFun i := (i.1 + u, i.2)
  invFun i := (i.1 + u, i.2)
  left_inv i := by simp [add_assoc, vec_add_self]
  right_inv i := by simp [add_assoc, vec_add_self]

def suffixPerm {m h : Nat} (t : H h) : Equiv.Perm (I m h) where
  toFun i := if i.1 = 0 then (i.1, i.2 + t) else i
  invFun i := if i.1 = 0 then (i.1, i.2 + t) else i
  left_inv i := by
    by_cases hi : i.1 = 0 <;> simp [hi, add_assoc, vec_add_self, Prod.ext_iff]
  right_inv i := by
    by_cases hi : i.1 = 0 <;> simp [hi, add_assoc, vec_add_self, Prod.ext_iff]

def unit {m h : Nat} (i : I m h) : V m h := fun j => if j = i then 1 else 0

lemma unit_injective {m h : Nat} : Function.Injective (@unit m h) := by
  intro i j hij
  by_contra h
  have hh := congrFun hij i
  simp [unit, h] at hh

lemma prefix_inv {m h : Nat} (u : U m) (p : Equiv.Perm (I m h)) (t : H h) :
    (prefixPerm u * p).symm (0, t) = p.symm (u, t) := by
  apply (prefixPerm u * p).injective
  simp [prefixPerm, Equiv.Perm.mul_apply, vec_add_self]

lemma units_support_bijective {m h : Nat} (p : Equiv.Perm (I m h))
    (g : U m → H h) (c : V m h)
    (hc : ∀ i, c i = ∑ u : U m, unit (p.symm (u, g u)) i) :
    Function.Bijective (fun i : (Finset.univ.filter (fun i => c i = 1)) => (p i).1) := by
  classical
  let f : U m → I m h := fun u => p.symm (u, g u)
  have hi : Function.Injective f := by
    intro u v he
    exact congrArg Prod.fst (p.symm.injective he)
  have hmem (i : I m h) : c i = 1 ↔ ∃ u, f u = i := by
    constructor
    · intro hci
      by_contra hn
      have hzero : c i = 0 := by
        rw [hc]
        apply Finset.sum_eq_zero
        intro u hu
        simp only [unit]
        rw [ite_eq_right (fun hh => hn ⟨u, hh.symm⟩)]
      exact one_ne_zero (hci.symm.trans hzero)
    · rintro ⟨u, rfl⟩
      rw [hc, Finset.sum_eq_single u]
      · simp [unit, f]
      · intro v hv hvu
        simp only [unit]
        rw [ite_eq_right]
        intro he
        exact hvu (hi he).symm
      · simp
  constructor
  · intro i j he
    obtain ⟨u, hu⟩ := (hmem i).mp (Finset.mem_filter.mp i.property).2
    obtain ⟨v, hv⟩ := (hmem j).mp (Finset.mem_filter.mp j.property).2
    have huv : u = v := by
      simpa [← hu, ← hv, f] using he
    exact Subtype.ext (hu.symm.trans (huv ▸ hv))
  · intro u
    refine ⟨⟨f u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmem _).mpr ⟨u, rfl⟩⟩⟩, ?_⟩
    simp [f]

abbrev Bad {m h : Nat} (P : W m h → V m h) (p : Equiv.Perm (I m h)) : Prop :=
  ∀ t : H h, P (fun i => p i) ≠ unit (p.symm (0, t))

lemma predictor_bound {m h : Nat} (P : W m h → V m h) (hP : Low P) :
    (2 ^ m * 2 ^ h).factorial ≤
      (2 ^ h) ^ (2 ^ m) * (2 ^ m).factorial * (2 ^ m * 2 ^ h - 2 ^ m).factorial +
      2 ^ m * (Finset.univ.filter (Bad P)).card := by
  classical
  let c : V m h := fun i => ∑ u : U m, P (shift u (fun _ => (0, 0))) i
  let S := Finset.univ.filter (fun i => c i = 1)
  let G := Finset.univ.filter (fun p : Equiv.Perm (I m h) =>
    Function.Bijective (fun i : S => (p i).1))
  let B := Finset.univ.filter (Bad P)
  have hcover : ∀ p : Equiv.Perm (I m h), p ∈ G ∨
      ∃ u : U m, Equiv.mulLeft (prefixPerm u) p ∈ B := by
    intro p
    by_cases hb : ∃ u : U m, Equiv.mulLeft (prefixPerm u) p ∈ B
    · exact Or.inr hb
    · left
      have hh : ∀ u : U m, ∃ t : H h,
          P (shift u (fun i => p i)) = unit (p.symm (u, t)) := by
        intro u
        have hn : ¬ Bad P (prefixPerm u * p) := by
          intro ht
          exact hb ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩⟩
        simp only [Bad, not_forall, not_not] at hn
        obtain ⟨t, ht⟩ := hn
        refine ⟨t, ?_⟩
        rw [prefix_inv] at ht
        exact ht
      choose g hg using hh
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, units_support_bijective p g c ?_⟩
      intro i
      calc
        _ = ∑ u : U m, P (shift u (fun j => p j)) i :=
          (low_shift_sum P hP _ _ i).symm
        _ = _ := by simp_rw [hg]
  have hh := orbit_cover_bound (fun u : U m => Equiv.mulLeft (prefixPerm u)) G B hcover
  have hg := card_transversals_le (A := U m) (B := H h) S
  have hcardU : Fintype.card (U m) = 2 ^ m := by simp [U, K, ZMod.card]
  have hcardH : Fintype.card (H h) = 2 ^ h := by simp [H, K, ZMod.card]
  have hcardI : Fintype.card (I m h) = 2 ^ m * 2 ^ h := by
    simp only [I, Fintype.card_prod, hcardU, hcardH]
  simp only [Fintype.card_perm, hcardI, hcardU] at hh
  simp only [hcardU, hcardH, hcardI] at hg
  exact hh.trans (Nat.add_le_add_right hg _)

lemma misses_le_absent {A V : Type*} [Fintype A] [DecidableEq V]
    (pred target : A → V) (hinj : Function.Injective target) :
    (Finset.univ.filter (fun a => ∀ t, pred a ≠ target t)).card ≤
      (Finset.univ.filter (fun t =>
        target t ∉ (Finset.univ.image pred))).card := by
  classical
  let hits := Finset.univ.filter (fun t => target t ∈ Finset.univ.image pred)
  let valid := Finset.univ.filter (fun a => ¬ ∀ t, pred a ≠ target t)
  have hsub : hits.image target ⊆ valid.image pred := by
    intro v hv
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ht).2
    apply Finset.mem_image.mpr
    refine ⟨a, Finset.mem_filter.mpr ⟨ha, ?_⟩, he⟩
    intro hn
    exact hn t he
  have hh : hits.card ≤ valid.card := by
    calc
      _ = (hits.image target).card := (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (valid.image pred).card := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_image_le
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset A)) (fun a => ∀ t, pred a ≠ target t)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset A)) (fun t => target t ∈ Finset.univ.image pred)
  dsimp [hits, valid] at hh
  simp only [ne_eq] at hh h1 h2 ⊢
  omega

lemma suffix_inv {m h : Nat} (t : H h) (p : Equiv.Perm (I m h)) :
    (suffixPerm t * p).symm (0, 0) = p.symm (0, t) := by
  apply (suffixPerm t * p).injective
  simp [suffixPerm, Equiv.Perm.mul_apply, vec_add_self]

def menu {m h : Nat} (P : H h → W m h → V m h) (x : W m h) : Finset (V m h) :=
  Finset.univ.image (fun a => P a x)

lemma absent_bound {m h : Nat} (P : H h → W m h → V m h) :
    (∑ p : Equiv.Perm (I m h), (Finset.univ.filter (fun t : H h =>
      unit (p.symm (0, t)) ∉ menu P (fun i => p i))).card) ≤
    2 ^ h * (Finset.univ.filter (fun p : Equiv.Perm (I m h) =>
      unit (p.symm (0, 0)) ∉ menu P (fun i => p i))).card +
    (Finset.univ.filter (fun v : Equiv.Perm (I m h) × H h =>
      menu P (fun i => (suffixPerm (m := m) v.2 * v.1) i) ≠ menu P (fun i => v.1 i))).card := by
  classical
  let missed (p : Equiv.Perm (I m h)) : Prop :=
    unit (p.symm (0, 0)) ∉ menu P (fun i => p i)
  let changed (p : Equiv.Perm (I m h)) (t : H h) : Prop :=
    menu P (fun i => (suffixPerm (m := m) t * p) i) ≠ menu P (fun i => p i)
  have hp (p : Equiv.Perm (I m h)) (t : H h) :
      (if unit (p.symm (0, t)) ∉ menu P (fun i => p i) then 1 else 0) ≤
      (if missed (suffixPerm t * p) then 1 else 0) +
      (if changed p t then 1 else 0) := by
    by_cases hc : changed p t
    · simp only [hc, ite_true]
      split_ifs <;> omega
    · have he : menu P (fun i => (suffixPerm (m := m) t * p) i) = menu P (fun i => p i) :=
        not_not.mp hc
      simp only [hc, ite_false, add_zero]
      simp only [missed, suffix_inv, he]
      exact le_rfl
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Equiv.Perm (I m h))))
    (fun p _ => Finset.sum_le_sum (s := (Finset.univ : Finset (H h))) (fun t _ => hp p t))
  simp only [Finset.sum_add_distrib] at hh
  have hm :
      (∑ p : Equiv.Perm (I m h), ∑ t : H h,
        if missed (suffixPerm t * p) then (1 : Nat) else 0) =
      2 ^ h * (Finset.univ.filter missed).card := by
    rw [Finset.sum_comm]
    have he (t : H h) :
        (∑ p : Equiv.Perm (I m h), if missed (suffixPerm t * p) then (1 : Nat) else 0) =
        (Finset.univ.filter missed).card := by
      calc
        _ = ∑ p : Equiv.Perm (I m h), if missed p then (1 : Nat) else 0 :=
          Equiv.sum_comp (Equiv.mulLeft (suffixPerm t)) (fun p => if missed p then (1 : Nat) else 0)
        _ = _ := by simp
    simp_rw [he]
    simp [H, K, ZMod.card]
  rw [hm] at hh
  simpa only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type,
    missed, changed] using hh

lemma main_bound {m h : Nat} (P : H h → W m h → V m h) (hP : ∀ a, Low (P a)) :
    2 ^ h * (2 ^ m * 2 ^ h).factorial ≤
    2 ^ h * ((2 ^ h) ^ (2 ^ m) * (2 ^ m).factorial *
      (2 ^ m * 2 ^ h - 2 ^ m).factorial) +
    2 ^ m * (2 ^ h * (Finset.univ.filter (fun p : Equiv.Perm (I m h) =>
      unit (p.symm (0, 0)) ∉ menu P (fun i => p i))).card +
    (Finset.univ.filter (fun v : Equiv.Perm (I m h) × H h =>
      menu P (fun i => (suffixPerm (m := m) v.2 * v.1) i) ≠
        menu P (fun i => v.1 i))).card) := by
  classical
  have hp := Finset.sum_le_sum (s := (Finset.univ : Finset (H h)))
    (fun a _ => predictor_bound (P a) (hP a))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hp
  have hcard : Fintype.card (H h) = 2 ^ h := by simp [H, K, ZMod.card]
  rw [hcard] at hp
  simp only [Nat.cast_id] at hp
  have hlocal (p : Equiv.Perm (I m h)) :
      (Finset.univ.filter (fun a : H h => Bad (P a) p)).card ≤
      (Finset.univ.filter (fun t : H h =>
        unit (p.symm (0, t)) ∉ menu P (fun i => p i))).card := by
    apply misses_le_absent
    intro t u he
    exact congrArg Prod.snd (p.symm.injective (unit_injective he))
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Equiv.Perm (I m h))))
    (fun p _ => hlocal p)
  have hswap :
      (∑ a : H h, (Finset.univ.filter (Bad (P a))).card) =
      ∑ p : Equiv.Perm (I m h), (Finset.univ.filter (fun a : H h => Bad (P a) p)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  rw [hswap] at hp
  have hx := hp.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (hsum.trans (absent_bound P))) _)
  convert hx using 1; ring

end PEqualNP.Outside.L_lib_735

theorem PEqualNP.Outside.L_lib_735 : (∀ (m h : Nat),
  let K := ZMod 2
  let U := Fin m → K
  let H := Fin h → K
  let I := U × H
  let W := I → I
  let V := I → K
  let J := I × (Fin m ⊕ Fin h)
  let b := 2^m
  let s := 2^h
  let n := b*s
  let bit := fun (x : W) (j : J) => Sum.elim (x j.1).1 (x j.1).2 j.2
  let low := fun (P : W → V) => ∀ i, ∃ T : Finset (Finset J),
    (∀ mon ∈ T, mon.card ≤ m) ∧ ∀ x, P x i = ∑ mon ∈ T, ∏ j ∈ mon, bit x j
  let unit := fun (i j : I) => if j = i then (1 : K) else 0
  let move := fun (p : Equiv.Perm I) (t : H) (i : I) =>
    if (p i).1 = 0 then ((p i).1, (p i).2+t) else p i
  ∀ P : H → W → V, (∀ a, low (P a)) →
    let menu := fun (x : W) => (Finset.univ : Finset H).image (fun a => P a x)
    let missed := (Finset.univ : Finset (Equiv.Perm I)).filter (fun p =>
      unit (p.symm (0,0)) ∉ menu (fun i => p i))
    let changed := (Finset.univ : Finset (Equiv.Perm I × H)).filter (fun v =>
      menu (move v.1 v.2) ≠ menu (fun i => v.1 i))
    let good := s^b * Nat.factorial b * Nat.factorial (n-b)
    s * Nat.factorial n ≤ s*good + b * (s*missed.card + changed.card)) := by
  intro m h K U H I W V J b s n bit low unit move P hP menu missed changed good
  exact PEqualNP.Outside.L_lib_735.main_bound P hP
