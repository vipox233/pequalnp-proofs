import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push

namespace PEqualNP.Outside.L_lib_732_aux

theorem uniquePrefix {U H : Type} [Fintype (U × H)]
    (M : U × H → Prop) (p : Equiv.Perm (U × H)) [∀ u : U, DecidablePred
      (fun i : U × H => (p i).1 = u ∧ M i)] :
    (∀ u : U, ((Finset.univ : Finset (U × H)).filter
      (fun i => (p i).1 = u ∧ M i)).card = 1) ↔
      Function.Bijective (fun i : {i // M i} => (p i).1) := by
  classical
  rw [Function.bijective_iff_existsUnique]
  simp only [Finset.card_eq_one_iff_existsUnique, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro h u
    obtain ⟨i, ⟨hi, hm⟩, uniq⟩ := h u
    exact ⟨⟨i, hm⟩, hi, fun j hj => Subtype.ext (uniq j ⟨hj, j.2⟩)⟩
  · intro h u
    obtain ⟨i, hi, uniq⟩ := h u
    exact ⟨i, ⟨hi, i.2⟩, fun j hj => congrArg Subtype.val (uniq ⟨j, hj.2⟩ hj.1)⟩

noncomputable def graphEquiv {U H : Type} (f : U → H) :
    U ≃ {j : U × H // j.2 = f j.1} where
  toFun u := ⟨(u, f u), rfl⟩
  invFun j := j.1.1
  left_inv _ := rfl
  right_inv j := Subtype.ext (Prod.ext rfl j.2.symm)

noncomputable def joinPermutation {U H : Type} (M : U × H → Prop)
    (e : {i // M i} ≃ U) (f : U → H)
    (g : {i // ¬ M i} ≃ {j : U × H // j.2 ≠ f j.1}) :
    Equiv.Perm (U × H) := by
  classical
  exact (Equiv.sumCompl M).symm.trans
    ((Equiv.sumCongr (e.trans (graphEquiv f)) g).trans
      (Equiv.sumCompl (fun j : U × H => j.2 = f j.1)))

theorem join_marked {U H : Type} (M : U × H → Prop)
    (e : {i // M i} ≃ U) (f : U → H)
    (g : {i // ¬ M i} ≃ {j : U × H // j.2 ≠ f j.1})
    (i : {i // M i}) :
    joinPermutation M e f g i = (e i, f (e i)) := by
  classical
  simp [joinPermutation, graphEquiv]

theorem join_unmarked {U H : Type} (M : U × H → Prop)
    (e : {i // M i} ≃ U) (f : U → H)
    (g : {i // ¬ M i} ≃ {j : U × H // j.2 ≠ f j.1})
    (i : {i // ¬ M i}) :
    joinPermutation M e f g i = g i := by
  classical
  simp [joinPermutation]

noncomputable def permutationChoices {U H : Type} (M : U × H → Prop) :
    (({i // M i} ≃ U) × (Σ f : U → H,
      {i // ¬ M i} ≃ {j : U × H // j.2 ≠ f j.1})) ≃
    {p : Equiv.Perm (U × H) // Function.Bijective (fun i : {i // M i} => (p i).1)} := by
  classical
  let build (q : ({i // M i} ≃ U) × (Σ f : U → H,
      {i // ¬ M i} ≃ {j : U × H // j.2 ≠ f j.1})) :
      {p : Equiv.Perm (U × H) // Function.Bijective (fun i : {i // M i} => (p i).1)} :=
    ⟨joinPermutation M q.1 q.2.1 q.2.2, by
      convert q.1.bijective using 1
      funext i
      rw [join_marked]⟩
  refine Equiv.ofBijective build ⟨?_, ?_⟩
  · rintro ⟨e, f, g⟩ ⟨e', f', g'⟩ heq
    have hp : joinPermutation M e f g = joinPermutation M e' f' g' := congrArg Subtype.val heq
    have hmark (i : {i // M i}) : (e i, f (e i)) = (e' i, f' (e' i)) := by
      simpa only [join_marked] using Equiv.congr_fun hp (i : U × H)
    have he : e = e' := Equiv.ext (fun i => congrArg Prod.fst (hmark i))
    subst e'
    have hf : f = f' := by
      funext u
      obtain ⟨i, rfl⟩ := e.surjective u
      exact congrArg Prod.snd (hmark i)
    subst f'
    have hg : g = g' := by
      apply Equiv.ext
      intro i
      apply Subtype.ext
      simpa only [join_unmarked] using Equiv.congr_fun hp (i : U × H)
    subst g'
    rfl
  · intro p
    let e : {i // M i} ≃ U := Equiv.ofBijective _ p.2
    let f (u : U) : H := (p.1 (e.symm u)).2
    have hprefix (i : {i // M i}) : e i = (p.1 i).1 := rfl
    have hmark (i : {i // M i}) : p.1 i = (e i, f (e i)) := by
      apply Prod.ext
      · exact (hprefix i).symm
      · simp [f]
    have graph_iff (i : U × H) : M i ↔ (p.1 i).2 = f (p.1 i).1 := by
      constructor
      · intro hi
        rw [hmark ⟨i, hi⟩]
      · intro hi
        let j := e.symm (p.1 i).1
        have hj : p.1 j = p.1 i := by
          rw [hmark j]
          rw [show e j = (p.1 i).1 from e.apply_symm_apply _]
          exact Prod.ext rfl hi.symm
        exact (p.1.injective hj) ▸ j.2
    let g : {i // ¬ M i} ≃ {j : U × H // j.2 ≠ f j.1} :=
      p.1.subtypeEquiv (fun i => not_congr (graph_iff i))
    refine ⟨⟨e, f, g⟩, Subtype.ext (Equiv.ext fun i => ?_)⟩
    change joinPermutation M e f g i = p.1 i
    by_cases hi : M i
    · rw [join_marked M e f g ⟨i, hi⟩]
      exact (hmark ⟨i, hi⟩).symm
    · exact join_unmarked M e f g ⟨i, hi⟩

theorem countTransversals {U H : Type} [Fintype U] [Fintype H]
    [DecidableEq U] [DecidableEq H] (M : U × H → Prop) [DecidablePred M] :
    let b := Fintype.card U
    let s := Fintype.card H
    let n := b * s
    ((Finset.univ : Finset (Equiv.Perm (U × H))).filter (fun p =>
      ∀ u : U, ((Finset.univ : Finset (U × H)).filter
        (fun i => (p i).1 = u ∧ M i)).card = 1)).card =
    (if ((Finset.univ : Finset (U × H)).filter M).card = b
     then s^b * Nat.factorial b * Nat.factorial (n-b) else 0) := by
  classical
  dsimp only
  let good (p : Equiv.Perm (U × H)) :=
    Function.Bijective (fun i : {i // M i} => (p i).1)
  have hc : ((Finset.univ : Finset (Equiv.Perm (U × H))).filter (fun p =>
      ∀ u : U, ((Finset.univ : Finset (U × H)).filter
        (fun i => (p i).1 = u ∧ M i)).card = 1)).card =
      Fintype.card {p // good p} := by
    rw [Fintype.card_subtype]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact uniquePrefix M p
  rw [hc, ← Fintype.card_subtype M]
  by_cases h : Fintype.card {i // M i} = Fintype.card U
  · rw [ite_eq_left h, ← Fintype.card_congr (permutationChoices M), Fintype.card_prod]
    let e : {i // M i} ≃ U := Fintype.equivOfCardEq h
    have hg (f : U → H) :
        Fintype.card ({i // ¬ M i} ≃ {j : U × H // j.2 ≠ f j.1}) =
        Nat.factorial (Fintype.card U * Fintype.card H - Fintype.card U) := by
      have hgraph := Fintype.card_congr (graphEquiv f)
      have hs := Fintype.card_subtype_compl M
      rw [Fintype.card_prod, h] at hs
      have ht := Fintype.card_subtype_compl (fun j : U × H => j.2 = f j.1)
      rw [Fintype.card_prod, ← hgraph] at ht
      rw [Fintype.card_equiv (Fintype.equivOfCardEq (hs.trans ht.symm)), hs]
    rw [Fintype.card_equiv e, h, Fintype.card_sigma]
    simp only [hg, Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
    ac_rfl
  · rw [ite_eq_right h]
    exact Fintype.card_eq_zero_iff.mpr ⟨fun p => h (Fintype.card_congr
      (Equiv.ofBijective _ p.2))⟩

end PEqualNP.Outside.L_lib_732_aux

open PEqualNP.Outside.L_lib_732_aux

theorem PEqualNP.Outside.L_lib_732 : (∀ (m h : Nat),
  let K := ZMod 2
  let U := Fin m → K
  let H := Fin h → K
  let I := U × H
  let W := I → I
  let V := I → K
  let b := 2^m
  let s := 2^h
  let n := b*s
  let unit := fun (i j : I) => if j = i then (1 : K) else 0
  let translate := fun (p : Equiv.Perm I) (u : U) (i : I) =>
    ((p i).1 + u, (p i).2)
  ∀ (P : W → V) (A : V),
    (∀ p : Equiv.Perm I, (∑ u : U, P (translate p u)) = A) →
      let cross := (Finset.univ : Finset (Equiv.Perm I)).filter (fun p =>
        ∀ u : U, ((Finset.univ : Finset I).filter (fun i => (p i).1 = u ∧ A i = 1)).card = 1)
      let bad := (Finset.univ : Finset (Equiv.Perm I)).filter (fun p =>
        ∀ i : I, (p i).1 = 0 → P (fun j => p j) ≠ unit i)
      cross.card = (if ((Finset.univ : Finset I).filter (fun i => A i = 1)).card = b
        then s^b * Nat.factorial b * Nat.factorial (n-b) else 0) ∧
        Nat.factorial n ≤ cross.card + b*bad.card) := by
  classical
  intro m h K U H I W V b s n unit translate P A hsum
  let Cross (p : Equiv.Perm I) := ∀ u : U,
    ((Finset.univ : Finset I).filter (fun i => (p i).1 = u ∧ A i = 1)).card = 1
  let Bad (p : Equiv.Perm I) :=
    ∀ i : I, (p i).1 = 0 → P (fun j => p j) ≠ unit i
  change ((Finset.univ : Finset (Equiv.Perm I)).filter Cross).card = _ ∧
    Nat.factorial n ≤ ((Finset.univ : Finset (Equiv.Perm I)).filter Cross).card +
      b * ((Finset.univ : Finset (Equiv.Perm I)).filter Bad).card
  have hb : Fintype.card U = b := by
    simp [U, K, b, ZMod.card]
  have hs : Fintype.card H = s := by
    simp [H, K, s, ZMod.card]
  have hn : Fintype.card I = n := by
    change Fintype.card (U × H) = _
    rw [Fintype.card_prod, hb, hs]
  constructor
  · have hc := countTransversals (U := U) (H := H) (fun i : I => A i = 1)
    dsimp only at hc
    rw [hb, hs] at hc
    exact hc
  · let shift (p : Equiv.Perm I) (u : U) : Equiv.Perm I :=
      p.trans ((Equiv.addRight u).prodCongr (Equiv.refl H))
    have hgood (p : Equiv.Perm I) (allGood : ∀ u : U, ¬Bad (shift p u)) :
        Cross p := by
      have hex (u : U) : ∃ i : I, (p i).1 + u = 0 ∧ P (translate p u) = unit i := by
        have hu := allGood u
        unfold Bad at hu
        push Not at hu
        obtain ⟨i, hi, hp⟩ := hu
        exact ⟨i, hi, hp⟩
      choose chosen hzero hchosen using hex
      have hprefix (u : U) : (p (chosen u)).1 = -u := by
        calc
          (p (chosen u)).1 = ((p (chosen u)).1 + u) + -u := by simp [add_assoc]
          _ = -u := by rw [hzero, zero_add]
      have hinj : Function.Injective chosen := by
        intro u v he
        have hu := hprefix u
        rw [he, hprefix] at hu
        exact neg_injective hu.symm
      have hsupport (j : I) : A j = 1 ↔ ∃ u, chosen u = j := by
        have heval : A j = ∑ u : U, unit (chosen u) j := by
          calc
            A j = (∑ u : U, (P (translate p u) : I → K)) j :=
              (congrFun (hsum p) j).symm
            _ = ∑ u : U, P (translate p u) j := Fintype.sum_apply j _
            _ = _ := Finset.sum_congr rfl (fun u _ => congrFun (hchosen u) j)
        constructor
        · intro hm
          by_contra! hz
          have hzeroA : A j = 0 := by
            rw [heval]
            simp [unit, fun u => Ne.symm (hz u)]
          change A j = (1 : ZMod 2) at hm
          exact zero_ne_one (hzeroA.symm.trans hm)
        · rintro ⟨u, rfl⟩
          rw [heval, Finset.sum_eq_single u]
          · simp [unit]
          · intro v _ hne
            exact ite_eq_right (fun H => hne (hinj H.symm))
          · simp
      change ∀ u : U, ((Finset.univ : Finset I).filter
        (fun i => (p i).1 = u ∧ A i = 1)).card = 1
      intro u
      rw [Finset.card_eq_one_iff_existsUnique]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨chosen (-u), ⟨by simp [hprefix], (hsupport _).2 ⟨-u, rfl⟩⟩, ?_⟩
      rintro j ⟨hp, ha⟩
      obtain ⟨v, rfl⟩ := (hsupport j).1 ha
      rw [hprefix] at hp
      have hv : v = -u := by
        simpa only [neg_neg] using congrArg Neg.neg hp
      exact congrArg chosen hv
    let outside := (Finset.univ : Finset (Equiv.Perm I)).filter (fun p => ¬Cross p)
    let failures := (Finset.univ : Finset (Equiv.Perm I)).filter Bad
    have hex (p : outside) : ∃ u : U, Bad (shift p.1 u) := by
      by_contra! hall
      exact (Finset.mem_filter.mp p.2).2 (hgood p.1 hall)
    choose pick hpick using hex
    let inject (p : outside) : U × failures :=
      (pick p, ⟨shift p.1 (pick p), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpick p⟩⟩)
    have hinj : Function.Injective inject := by
      intro p q hpq
      have hu : pick p = pick q := congrArg Prod.fst hpq
      have hp : shift p.1 (pick p) = shift q.1 (pick q) :=
        congrArg (fun t : U × failures => t.2.1) hpq
      rw [← hu] at hp
      apply Subtype.ext
      apply Equiv.ext
      intro j
      exact ((Equiv.addRight (pick p)).prodCongr (Equiv.refl H)).injective
        (Equiv.congr_fun hp j)
    have hle := Fintype.card_le_of_injective inject hinj
    rw [Fintype.card_prod, hb, Fintype.card_coe, Fintype.card_coe] at hle
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Equiv.Perm I))) Cross
    rw [Finset.card_univ, Fintype.card_perm, hn] at hsplit
    change _ + outside.card = _ at hsplit
    change _ ≤ _ + b * failures.card
    omega
