import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_731_aux

open scoped BigOperators

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

lemma zmod2_eq_zero_of_ne_one {x : ZMod 2} (hx : x ≠ 1) : x = 0 := by
  fin_cases x
  · rfl
  · exact absurd rfl hx

lemma sum_zmod2_fun_eq_zero_of_indep {m : ℕ} (r0 : Fin m) (f : (Fin m → ZMod 2) → ZMod 2)
    (hindep : ∀ u, f (Function.update u r0 (u r0 + 1)) = f u) :
    (∑ u : Fin m → ZMod 2, f u) = 0 := by
  let flip : (Fin m → ZMod 2) → (Fin m → ZMod 2) := fun u => Function.update u r0 (u r0 + 1)
  have hS01 : (∑ u : Fin m → ZMod 2, f u) =
      (∑ u ∈ Finset.univ.filter (fun u : Fin m → ZMod 2 => u r0 = 0), f u) +
      (∑ u ∈ Finset.univ.filter (fun u : Fin m → ZMod 2 => ¬ u r0 = 0), f u) :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ (fun u : Fin m → ZMod 2 => u r0 = 0) f).symm
  have hbij :
      (∑ u ∈ Finset.univ.filter (fun u : Fin m → ZMod 2 => u r0 = 0), f u) =
      ∑ u ∈ Finset.univ.filter (fun u : Fin m → ZMod 2 => ¬ u r0 = 0), f u := by
    refine Finset.sum_bij (fun u _ => flip u) ?_ ?_ ?_ fun u _ => (hindep u).symm
    · intro u hu
      have hu0 : u r0 = 0 := (Finset.mem_filter.mp hu).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simp only [flip, Function.update_self, hu0, zero_add]
      decide
    · intro u1 _ u2 _ heq
      ext r
      by_cases hr : r = r0
      · subst hr
        have h1 := congrFun heq r
        simp only [flip, Function.update_self] at h1
        have h2 := congrArg (fun z : ZMod 2 => z + 1) h1
        simp only [add_assoc, show (1 : ZMod 2) + 1 = 0 by decide, add_zero] at h2
        exact h2
      · have h1 := congrFun heq r
        simp only [flip, Function.update_of_ne hr] at h1
        exact h1
    · intro v hv
      have hv1 : v r0 = 1 := zmod2_eq_one_of_ne_zero (Finset.mem_filter.mp hv).2
      refine ⟨flip v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simp only [flip, Function.update_self, hv1]
        decide
      · ext r
        by_cases hr : r = r0
        · subst hr
          simp only [flip, Function.update_self, add_assoc,
            show (1 : ZMod 2) + 1 = 0 by decide, add_zero]
        · simp only [flip, Function.update_of_ne hr]
  rw [hS01, hbij, zmod2_add_self]

lemma sum_prod_zmod2_shift {m : ℕ} (c : Fin m → ZMod 2) :
    (∑ u : Fin m → ZMod 2, ∏ r : Fin m, (c r + u r)) = 1 := by
  have hbij : Function.Bijective (fun u : Fin m → ZMod 2 => fun r => c r + u r) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨fun v r => c r + v r, ?_, ?_⟩
    · intro u; ext r
      calc
        c r + (c r + u r) = (c r + c r) + u r := by ring
        _ = u r := by rw [zmod2_add_self, zero_add]
    · intro v; ext r
      calc
        c r + (c r + v r) = (c r + c r) + v r := by ring
        _ = v r := by rw [zmod2_add_self, zero_add]
  have h1 : (∑ u : Fin m → ZMod 2, ∏ r : Fin m, (c r + u r)) =
      ∑ v : Fin m → ZMod 2, ∏ r : Fin m, v r :=
    Fintype.sum_bijective (fun u r => c r + u r) hbij _ _ fun _ => rfl
  rw [h1]
  rw [Finset.sum_eq_single (fun _ : Fin m => (1 : ZMod 2))]
  · simp
  · intro v _ hv
    have hex : ∃ r : Fin m, v r ≠ 1 := by
      by_contra hall
      push Not at hall
      exact hv (funext hall)
    rcases hex with ⟨r, hr⟩
    exact Finset.prod_eq_zero (Finset.mem_univ r) (zmod2_eq_zero_of_ne_one hr)
  · intro h; exact absurd (Finset.mem_univ _) h

lemma sum_monomial_translate_eq {m h : ℕ}
    (mon : Finset (((Fin m → ZMod 2) × (Fin h → ZMod 2)) × (Fin m ⊕ Fin h)))
    (hcard : mon.card ≤ m) (p : Equiv.Perm ((Fin m → ZMod 2) × (Fin h → ZMod 2))) :
    (∑ u : Fin m → ZMod 2,
      ∏ j ∈ mon, Sum.elim ((p j.1).1 + u) (p j.1).2 j.2) =
      if ∀ r : Fin m, ∃ idx : (Fin m → ZMod 2) × (Fin h → ZMod 2), (idx, Sum.inl r) ∈ mon
      then 1 else 0 := by
  classical
  split_ifs with hall
  · let g : Fin m → ((Fin m → ZMod 2) × (Fin h → ZMod 2)) × (Fin m ⊕ Fin h) :=
      fun r => (Classical.choose (hall r), Sum.inl r)
    have hg_mem : ∀ r : Fin m, g r ∈ mon := fun r => Classical.choose_spec (hall r)
    have hg_inj : Function.Injective g := by
      intro r1 r2 heq
      have h2 := congrArg Prod.snd heq
      simp only [g, Sum.inl.injEq] at h2
      exact h2
    have hsub : Finset.univ.image g ⊆ mon := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨r, _, rfl⟩
      exact hg_mem r
    have hcard_img : (Finset.univ.image g).card = m := by
      rw [Finset.card_image_of_injective _ hg_inj, Finset.card_univ, Fintype.card_fin]
    have hmon_eq : mon = Finset.univ.image g :=
      (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    have hprod : ∀ u : Fin m → ZMod 2,
        (∏ j ∈ mon, Sum.elim ((p j.1).1 + u) (p j.1).2 j.2) =
          ∏ r : Fin m, ((p (Classical.choose (hall r))).1 r + u r) := by
      intro u
      conv_lhs => rw [hmon_eq]
      rw [Finset.prod_image (fun a _ b _ h => hg_inj h)]
      refine Finset.prod_congr rfl fun r _ => ?_
      simp [g]
    simp_rw [hprod]
    exact sum_prod_zmod2_shift (fun r => (p (Classical.choose (hall r))).1 r)
  · push Not at hall
    rcases hall with ⟨r0, hr0⟩
    refine sum_zmod2_fun_eq_zero_of_indep r0 _ fun u => ?_
    refine Finset.prod_congr rfl fun j hj => ?_
    rcases j with ⟨idx, r | s⟩
    · simp only [Sum.elim_inl, Pi.add_apply]
      have hne : r ≠ r0 := fun heq => by subst heq; exact hr0 idx hj
      rw [Function.update_of_ne hne]
    · simp only [Sum.elim_inr]

end PEqualNP.Outside.L_lib_731_aux

open PEqualNP.Outside.L_lib_731_aux

theorem PEqualNP.Outside.L_lib_731 :
    ∀ (m h : Nat),
      let K := ZMod 2
      let U := Fin m → K
      let H := Fin h → K
      let I := U × H
      let W := I → I
      let V := I → K
      let J := I × (Fin m ⊕ Fin h)
      let bit := fun (x : W) (j : J) => Sum.elim (x j.1).1 (x j.1).2 j.2
      let low := fun (P : W → V) => ∀ i, ∃ T : Finset (Finset J),
        (∀ mon ∈ T, mon.card ≤ m) ∧ ∀ x, P x i = ∑ mon ∈ T, ∏ j ∈ mon, bit x j
      let translate := fun (p : Equiv.Perm I) (u : U) (i : I) =>
        ((p i).1 + u, (p i).2)
      ∀ P : W → V, low P →
        ∃ A : V, (∀ p : Equiv.Perm I, (∑ u : U, P (translate p u)) = A) ∧
          ∀ i : I,
            let onErrors := (Finset.univ : Finset (Equiv.Perm I)).filter (fun p =>
              (p i).1 = 0 ∧ P (fun j => p j) i ≠ A i)
            let outside := (Finset.univ : Finset (Equiv.Perm I)).filter (fun p =>
              (p i).1 ≠ 0 ∧ P (fun j => p j) i ≠ 0)
            onErrors.card ≤ outside.card := by
  intro m h K U H I W V J bit low translate P hlow
  classical
  let A : V := ∑ u : U, P (translate (Equiv.refl I) u)
  have hconst : ∀ p : Equiv.Perm I, (∑ u : U, P (translate p u)) = A := by
    intro p
    ext i
    dsimp only [A, V]
    rw [Finset.sum_apply, Finset.sum_apply]
    rcases hlow i with ⟨T, hTcard, hTeval⟩
    have heval : ∀ q : Equiv.Perm I,
        (∑ u : U, P (translate q u) i) =
          ∑ mon ∈ T,
            if ∀ r : Fin m, ∃ idx : I, (idx, Sum.inl r) ∈ mon then (1 : ZMod 2) else 0 := by
      intro q
      simp_rw [hTeval]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun mon hmon => ?_
      exact sum_monomial_translate_eq mon (hTcard mon hmon) q
    rw [heval p, heval (Equiv.refl I)]
  refine ⟨A, hconst, fun i => ?_⟩
  intro onErrors outside
  let shiftPerm : Equiv.Perm I → U → Equiv.Perm I := fun p u =>
    p.trans (Equiv.prodCongr (Equiv.addRight u) (Equiv.refl H))
  have hshift_apply : ∀ (p : Equiv.Perm I) (u : U),
      (fun j : I => shiftPerm p u j) = translate p u := by
    intro p u; ext j <;> rfl
  have hex_u : ∀ p : Equiv.Perm I, p ∈ onErrors →
      ∃ u : U, u ≠ 0 ∧ P (translate p u) i ≠ 0 := by
    intro p hp
    have hneA : P (fun j => p j) i ≠ A i := (Finset.mem_filter.mp hp).2.2
    by_contra hall
    push Not at hall
    have hsum : (∑ u : U, P (translate p u) i) = P (translate p 0) i := by
      rw [Finset.sum_eq_single (0 : U)]
      · intro u _ hu0; exact hall u hu0
      · intro h0; exact absurd (Finset.mem_univ _) h0
    have hAeq : (∑ u : U, P (translate p u) i) = A i := by
      have h1 := congrFun (hconst p) i
      dsimp only [V] at h1
      rw [Finset.sum_apply] at h1
      exact h1
    have htr0 : translate p 0 = fun j => p j := by
      ext j <;> simp [translate]
    rw [htr0] at hsum
    exact hneA (hsum.symm.trans hAeq)
  let pick : Equiv.Perm I → Equiv.Perm I := fun p =>
    if hp : p ∈ onErrors then shiftPerm p (Classical.choose (hex_u p hp)) else p
  refine Finset.card_le_card_of_injOn pick ?_ ?_
  · intro p hp
    have hp' : p ∈ onErrors := Finset.mem_coe.mp hp
    simp only [pick, hp', ↓reduceDIte]
    have hp0 : (p i).1 = 0 := (Finset.mem_filter.mp hp').2.1
    have hu := Classical.choose_spec (hex_u p hp')
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩)
    · have h1 : (shiftPerm p (Classical.choose (hex_u p hp')) i).1 = Classical.choose (hex_u p hp') := by
        change (p i).1 + Classical.choose (hex_u p hp') = _
        rw [hp0, zero_add]
      rw [h1]
      exact hu.1
    · rw [hshift_apply]
      exact hu.2
  · intro p1 hp1 p2 hp2 heq
    have hp1' : p1 ∈ onErrors := Finset.mem_coe.mp hp1
    have hp2' : p2 ∈ onErrors := Finset.mem_coe.mp hp2
    simp only [pick, hp1', hp2', ↓reduceDIte] at heq
    have hp10 : (p1 i).1 = 0 := (Finset.mem_filter.mp hp1').2.1
    have hp20 : (p2 i).1 = 0 := (Finset.mem_filter.mp hp2').2.1
    have hu_eq : Classical.choose (hex_u p1 hp1') = Classical.choose (hex_u p2 hp2') := by
      have h1 : (p1 i).1 + Classical.choose (hex_u p1 hp1') =
          (p2 i).1 + Classical.choose (hex_u p2 hp2') :=
        congrArg (fun q : Equiv.Perm I => (q i).1) heq
      rw [hp10, hp20, zero_add, zero_add] at h1
      exact h1
    rw [hu_eq] at heq
    apply Equiv.ext; intro j
    have hj : ((p1 j).1 + Classical.choose (hex_u p2 hp2'), (p1 j).2) =
        ((p2 j).1 + Classical.choose (hex_u p2 hp2'), (p2 j).2) :=
      congrArg (fun q : Equiv.Perm I => q j) heq
    rcases Prod.mk.inj hj with ⟨hj1, hj2⟩
    exact Prod.ext (add_right_cancel hj1) hj2
