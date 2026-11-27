import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_710_aux

private abbrev K := ZMod 2
private abbrev I (b s : ℕ) := Fin b × Fin s

private lemma zmod2_add_self (x : K) : x + x = 0 := by
  revert x; decide

private lemma zmod2_add_cancel_right (x y : K) : x + y + y = x := by
  revert x y; decide

private lemma zmod2_eq_of_add_eq_zero {x y : K} (h : x + y = 0) : x = y := by
  revert x y h; decide

private lemma zmod2_swap_eq {a b c d : K} (h : a + d = b + c) : a + b = c + d := by
  revert a b c d h; decide

private lemma card_I (b s : ℕ) : Fintype.card (I b s) = b * s := by
  simp [I, Fintype.card_prod]

private lemma extend_inj {b s : ℕ} (u0 : Fin b) (v : Fin s → I b s) (hv : Function.Injective v) :
    ∃ p : Equiv.Perm (I b s), ∀ t : Fin s, p (u0, t) = v t := by
  let S : Finset (I b s) := Finset.univ.filter (fun x => x.1 = u0)
  let T : Finset (I b s) := Finset.univ.image v
  have hScard : S.card = s := by
    have hbij : S.card = (Finset.univ : Finset (Fin s)).card := by
      refine Finset.card_bij (fun x _ => x.2) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro x1 h1 x2 h2 heq
        have e1 : x1.1 = u0 := (Finset.mem_filter.1 h1).2
        have e2 : x2.1 = u0 := (Finset.mem_filter.1 h2).2
        exact Prod.ext (e1.trans e2.symm) heq
      · intro t _
        exact ⟨(u0, t), Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩, rfl⟩
    simpa using hbij
  have hTcard : T.card = s := by
    rw [Finset.card_image_of_injective _ hv, Finset.card_univ, Fintype.card_fin]
  have hcomp_card : Fintype.card {x : I b s // x ∉ S} = Fintype.card {x : I b s // x ∉ T} := by
    have c1 : Fintype.card {x : I b s // x ∉ S} = (Finset.univ \ S).card := by
      rw [Fintype.card_subtype]
      congr 1; ext x; simp
    have c2 : Fintype.card {x : I b s // x ∉ T} = (Finset.univ \ T).card := by
      rw [Fintype.card_subtype]
      congr 1; ext x; simp
    rw [c1, c2, Finset.card_sdiff, Finset.inter_univ, Finset.card_sdiff, Finset.inter_univ,
      hScard, hTcard]
  let eOut : {x : I b s // x ∉ S} ≃ {x : I b s // x ∉ T} := Fintype.equivOfCardEq hcomp_card
  let eIn : {x : I b s // x ∈ S} ≃ {x : I b s // x ∈ T} :=
    { toFun := fun x => ⟨v x.1.2, Finset.mem_image.2 ⟨x.1.2, Finset.mem_univ _, rfl⟩⟩
      invFun := fun y =>
        ⟨(u0, Classical.choose (Finset.mem_image.1 y.2)),
          Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
      left_inv := fun x => by
        apply Subtype.ext
        have hch := (Classical.choose_spec (Finset.mem_image.1
          (Finset.mem_image.2 ⟨x.1.2, Finset.mem_univ _, rfl⟩ : v x.1.2 ∈ T))).2
        have hteq : Classical.choose (Finset.mem_image.1
            (Finset.mem_image.2 ⟨x.1.2, Finset.mem_univ _, rfl⟩ : v x.1.2 ∈ T)) = x.1.2 :=
          hv hch
        have hu : x.1.1 = u0 := (Finset.mem_filter.1 x.2).2
        exact Prod.ext hu.symm hteq
      right_inv := fun y => by
        apply Subtype.ext
        exact (Classical.choose_spec (Finset.mem_image.1 y.2)).2 }
  let p : Equiv.Perm (I b s) :=
    { toFun := fun x => if hx : x ∈ S then (eIn ⟨x, hx⟩).1 else (eOut ⟨x, hx⟩).1
      invFun := fun y => if hy : y ∈ T then (eIn.symm ⟨y, hy⟩).1 else (eOut.symm ⟨y, hy⟩).1
      left_inv := fun x => by
        by_cases hx : x ∈ S
        · have hy : (eIn ⟨x, hx⟩).1 ∈ T := (eIn ⟨x, hx⟩).2
          simp only [hx, ↓reduceDIte, hy, Subtype.coe_eta, Equiv.symm_apply_apply]
        · have hy : (eOut ⟨x, hx⟩).1 ∉ T := (eOut ⟨x, hx⟩).2
          simp only [hx, ↓reduceDIte, hy, Subtype.coe_eta, Equiv.symm_apply_apply]
      right_inv := fun y => by
        by_cases hy : y ∈ T
        · have hx : (eIn.symm ⟨y, hy⟩).1 ∈ S := (eIn.symm ⟨y, hy⟩).2
          simp only [hy, ↓reduceDIte, hx, Subtype.coe_eta, Equiv.apply_symm_apply]
        · have hx : (eOut.symm ⟨y, hy⟩).1 ∉ S := (eOut.symm ⟨y, hy⟩).2
          simp only [hy, ↓reduceDIte, hx, Subtype.coe_eta, Equiv.apply_symm_apply] }
  refine ⟨p, fun t => ?_⟩
  have hm : (u0, t) ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
  simp [p, eIn, hm]

private lemma extend_two_disj {b s : ℕ} {u0 u1 : Fin b} (hu : u0 ≠ u1)
    (S0 S1 : Finset (I b s)) (h0 : S0.card = s) (h1 : S1.card = s) (hdisj : Disjoint S0 S1) :
    ∃ p : Equiv.Perm (I b s),
      Finset.univ.image (fun t : Fin s => p (u0, t)) = S0 ∧
      Finset.univ.image (fun t : Fin s => p (u1, t)) = S1 := by
  let e0 : Fin s ≃ {x : I b s // x ∈ S0} := Fintype.equivOfCardEq (by simp [h0])
  let e1 : Fin s ≃ {x : I b s // x ∈ S1} := Fintype.equivOfCardEq (by simp [h1])
  let Dom : Finset (I b s) := Finset.univ.filter (fun x => x.1 = u0 ∨ x.1 = u1)
  let Rng : Finset (I b s) := S0 ∪ S1
  have hDom_card : Dom.card = 2 * s := by
    let D0 : Finset (I b s) := Finset.univ.filter (fun x => x.1 = u0)
    let D1 : Finset (I b s) := Finset.univ.filter (fun x => x.1 = u1)
    have hd : Disjoint D0 D1 := by
      refine Finset.disjoint_left.2 fun x hx0 hx1 => hu ?_
      exact (Finset.mem_filter.1 hx0).2.symm.trans (Finset.mem_filter.1 hx1).2
    have hun : Dom = D0 ∪ D1 := by
      ext x; simp [Dom, D0, D1]
    have hc : ∀ u : Fin b, (Finset.univ.filter (fun x : I b s => x.1 = u)).card = s := by
      intro u
      have hb : (Finset.univ.filter (fun x : I b s => x.1 = u)).card =
          (Finset.univ : Finset (Fin s)).card := by
        refine Finset.card_bij (fun x _ => x.2) ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro x1 hx1 x2 hx2 heq
          exact Prod.ext ((Finset.mem_filter.1 hx1).2.trans (Finset.mem_filter.1 hx2).2.symm) heq
        · intro t _; exact ⟨(u, t), Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩, rfl⟩
      simpa using hb
    rw [hun, Finset.card_union_of_disjoint hd, hc u0, hc u1]
    ring
  have hRng_card : Rng.card = 2 * s := by
    rw [Finset.card_union_of_disjoint hdisj, h0, h1]; ring
  have hcomp_card : Fintype.card {x : I b s // x ∉ Dom} = Fintype.card {x : I b s // x ∉ Rng} := by
    have c1 : Fintype.card {x : I b s // x ∉ Dom} = (Finset.univ \ Dom).card := by
      rw [Fintype.card_subtype]; congr 1; ext x; simp
    have c2 : Fintype.card {x : I b s // x ∉ Rng} = (Finset.univ \ Rng).card := by
      rw [Fintype.card_subtype]; congr 1; ext x; simp
    rw [c1, c2, Finset.card_sdiff, Finset.inter_univ, Finset.card_sdiff, Finset.inter_univ,
      hDom_card, hRng_card]
  let eOut : {x : I b s // x ∉ Dom} ≃ {x : I b s // x ∉ Rng} := Fintype.equivOfCardEq hcomp_card
  let eIn : {x : I b s // x ∈ Dom} ≃ {x : I b s // x ∈ Rng} :=
    { toFun := fun x =>
        if h : x.1.1 = u0 then
          ⟨(e0 x.1.2).1, Finset.mem_union_left S1 (e0 x.1.2).2⟩
        else
          ⟨(e1 x.1.2).1, Finset.mem_union_right S0 (e1 x.1.2).2⟩
      invFun := fun y =>
        if h : y.1 ∈ S0 then
          ⟨(u0, e0.symm ⟨y.1, h⟩), Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl rfl⟩⟩
        else
          ⟨(u1, e1.symm ⟨y.1, Or.resolve_left (Finset.mem_union.1 y.2) h⟩),
            Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr rfl⟩⟩
      left_inv := fun x => by
        apply Subtype.ext
        by_cases hx0 : x.1.1 = u0
        · have hm0 : (e0 x.1.2).1 ∈ S0 := (e0 x.1.2).2
          simp only [hx0, ↓reduceDIte, hm0, Subtype.coe_eta, Equiv.symm_apply_apply]
          exact Prod.ext hx0.symm rfl
        · have hx1 : x.1.1 = u1 := Or.resolve_left (Finset.mem_filter.1 x.2).2 hx0
          have hm1 : (e1 x.1.2).1 ∉ S0 := Finset.disjoint_right.1 hdisj (e1 x.1.2).2
          simp only [hx0, ↓reduceDIte, hm1, Subtype.coe_eta, Equiv.symm_apply_apply]
          exact Prod.ext hx1.symm rfl
      right_inv := fun y => by
        apply Subtype.ext
        by_cases hy0 : y.1 ∈ S0
        · simp only [hy0, ↓reduceDIte, Equiv.apply_symm_apply]
        · simp only [hy0, ↓reduceDIte, hu.symm, Equiv.apply_symm_apply] }
  let p : Equiv.Perm (I b s) :=
    { toFun := fun x => if hx : x ∈ Dom then (eIn ⟨x, hx⟩).1 else (eOut ⟨x, hx⟩).1
      invFun := fun y => if hy : y ∈ Rng then (eIn.symm ⟨y, hy⟩).1 else (eOut.symm ⟨y, hy⟩).1
      left_inv := fun x => by
        by_cases hx : x ∈ Dom
        · have hy : (eIn ⟨x, hx⟩).1 ∈ Rng := (eIn ⟨x, hx⟩).2
          simp only [hx, ↓reduceDIte, hy, Subtype.coe_eta, Equiv.symm_apply_apply]
        · have hy : (eOut ⟨x, hx⟩).1 ∉ Rng := (eOut ⟨x, hx⟩).2
          simp only [hx, ↓reduceDIte, hy, Subtype.coe_eta, Equiv.symm_apply_apply]
      right_inv := fun y => by
        by_cases hy : y ∈ Rng
        · have hx : (eIn.symm ⟨y, hy⟩).1 ∈ Dom := (eIn.symm ⟨y, hy⟩).2
          simp only [hy, ↓reduceDIte, hx, Subtype.coe_eta, Equiv.apply_symm_apply]
        · have hx : (eOut.symm ⟨y, hy⟩).1 ∉ Dom := (eOut.symm ⟨y, hy⟩).2
          simp only [hy, ↓reduceDIte, hx, Subtype.coe_eta, Equiv.apply_symm_apply] }
  refine ⟨p, ?_, ?_⟩
  · ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨t, rfl⟩
      have hm : (u0, t) ∈ Dom := Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl rfl⟩
      simp only [p, Equiv.coe_fn_mk, hm, ↓reduceDIte, eIn]
      exact (e0 t).2
    · intro hy
      refine ⟨e0.symm ⟨y, hy⟩, ?_⟩
      have hm : (u0, e0.symm ⟨y, hy⟩) ∈ Dom := Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl rfl⟩
      simp only [p, Equiv.coe_fn_mk, hm, ↓reduceDIte, eIn, Equiv.apply_symm_apply]
  · ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨t, rfl⟩
      have hm : (u1, t) ∈ Dom := Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr rfl⟩
      simp only [p, Equiv.coe_fn_mk, hm, ↓reduceDIte, eIn, hu.symm]
      exact (e1 t).2
    · intro hy
      refine ⟨e1.symm ⟨y, hy⟩, ?_⟩
      have hm : (u1, e1.symm ⟨y, hy⟩) ∈ Dom := Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr rfl⟩
      simp only [p, Equiv.coe_fn_mk, hm, ↓reduceDIte, eIn, hu.symm, Equiv.apply_symm_apply]

private lemma f_comp_perm {b s : ℕ} (hb : 3 ≤ b)
    (f : (Fin s → I b s) → K) (h : K)
    (hconst : ∀ p : Equiv.Perm (I b s), (∑ u : Fin b, f (fun t => p (u, t))) = h)
    (v : Fin s → I b s) (hv : Function.Injective v) (σ : Equiv.Perm (Fin s)) :
    f (v ∘ σ) = f v := by
  let u0 : Fin b := ⟨0, by omega⟩
  rcases extend_inj u0 v hv with ⟨p, hp⟩
  let blk : Equiv.Perm (I b s) :=
    { toFun := fun x => (x.1, if x.1 = u0 then σ x.2 else x.2)
      invFun := fun x => (x.1, if x.1 = u0 then σ.symm x.2 else x.2)
      left_inv := fun ⟨u, t⟩ => by
        by_cases hx : u = u0 <;> simp [hx]
      right_inv := fun ⟨u, t⟩ => by
        by_cases hx : u = u0 <;> simp [hx] }
  let q : Equiv.Perm (I b s) := blk.trans p
  have heq : (∑ u : Fin b, f (fun t => q (u, t))) = ∑ u : Fin b, f (fun t => p (u, t)) := by
    rw [hconst q, hconst p]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ u0),
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ u0)] at heq
  have hrest :
      (∑ u ∈ Finset.univ.erase u0, f (fun t => q (u, t))) =
        ∑ u ∈ Finset.univ.erase u0, f (fun t => p (u, t)) := by
    refine Finset.sum_congr rfl fun u hu => ?_
    have hne : u ≠ u0 := (Finset.mem_erase.1 hu).1
    congr 1
    funext t
    simp [q, blk, hne]
  rw [hrest] at heq
  have h0 := add_right_cancel heq
  have hq0 : (fun t => q (u0, t)) = v ∘ σ := by
    funext t
    simp [q, blk, hp]
  have hp0 : (fun t => p (u0, t)) = v := funext hp
  rw [hq0, hp0] at h0
  exact h0

private noncomputable def setVal {b s : ℕ} (f : (Fin s → I b s) → K) (S : Finset (I b s)) : K :=
  if hS : S.card = s then
    f (fun t : Fin s => (Fintype.equivOfCardEq (by simp [hS] : Fintype.card (Fin s) =
      Fintype.card {x : I b s // x ∈ S}) t).1)
  else 0

private lemma setVal_image {b s : ℕ} (hb : 3 ≤ b)
    (f : (Fin s → I b s) → K) (h : K)
    (hconst : ∀ p : Equiv.Perm (I b s), (∑ u : Fin b, f (fun t => p (u, t))) = h)
    (v : Fin s → I b s) (hv : Function.Injective v) :
    setVal f (Finset.univ.image v) = f v := by
  have hcard : (Finset.univ.image v).card = s := by
    rw [Finset.card_image_of_injective _ hv, Finset.card_univ, Fintype.card_fin]
  unfold setVal
  simp only [hcard, ↓reduceDIte]
  let e : Fin s ≃ {x : I b s // x ∈ Finset.univ.image v} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_coe, hcard])
  let eV : Fin s ≃ {x : I b s // x ∈ Finset.univ.image v} :=
    { toFun := fun t => ⟨v t, Finset.mem_image.2 ⟨t, Finset.mem_univ _, rfl⟩⟩
      invFun := fun y => Classical.choose (Finset.mem_image.1 y.2)
      left_inv := fun t =>
        hv (Classical.choose_spec (Finset.mem_image.1
          (Finset.mem_image.2 ⟨t, Finset.mem_univ _, rfl⟩ : v t ∈ Finset.univ.image v))).2
      right_inv := fun y => Subtype.ext (Classical.choose_spec (Finset.mem_image.1 y.2)).2 }
  let σ : Equiv.Perm (Fin s) := e.trans eV.symm
  have hcomp : (fun t : Fin s => (e t).1) = v ∘ σ := by
    funext t
    change (e t).1 = (eV (eV.symm (e t))).1
    rw [Equiv.apply_symm_apply]
  change f (fun t : Fin s => (e t).1) = f v
  rw [hcomp]
  exact f_comp_perm hb f h hconst v hv σ

private lemma swap_two_blocks {b s : ℕ} (hb : 3 ≤ b)
    (f : (Fin s → I b s) → K) (h : K)
    (hconst : ∀ p : Equiv.Perm (I b s), (∑ u : Fin b, f (fun t => p (u, t))) = h)
    {A B : Finset (I b s)} (hA : A.card = s - 1) (hB : B.card = s - 1)
    (hAB : Disjoint A B) {x y : I b s} (hxy : x ≠ y)
    (hxA : x ∉ A) (hyA : y ∉ A) (hxB : x ∉ B) (hyB : y ∉ B) :
    setVal f (insert x A) + setVal f (insert y A) =
      setVal f (insert x B) + setVal f (insert y B) := by
  let u0 : Fin b := ⟨0, by omega⟩
  let u1 : Fin b := ⟨1, by omega⟩
  have hu : u0 ≠ u1 := by intro heq; simp [u0, u1] at heq
  have h1s : 1 ≤ s := by
    by_contra h0
    have hs0 : s = 0 := by omega
    subst hs0
    exact Fin.elim0 x.2
  have hS0 : (insert x A).card = s := by
    rw [Finset.card_insert_of_notMem hxA, hA]; omega
  have hS1 : (insert y B).card = s := by
    rw [Finset.card_insert_of_notMem hyB, hB]; omega
  have hdisj : Disjoint (insert x A) (insert y B) := by
    refine Finset.disjoint_left.2 fun z hz0 hz1 => ?_
    rcases Finset.mem_insert.1 hz0 with rfl | hzA
    · rcases Finset.mem_insert.1 hz1 with h' | hzB
      · exact hxy h'
      · exact hxB hzB
    · rcases Finset.mem_insert.1 hz1 with rfl | hzB
      · exact hyA hzA
      · exact Finset.disjoint_left.1 hAB hzA hzB
  rcases extend_two_disj hu (insert x A) (insert y B) hS0 hS1 hdisj with ⟨p, hp0, hp1⟩
  let q : Equiv.Perm (I b s) := p.trans (Equiv.swap x y)
  have heq : (∑ u : Fin b, f (fun t => p (u, t))) = ∑ u : Fin b, f (fun t => q (u, t)) := by
    rw [hconst p, hconst q]
  have hrest : ∀ u : Fin b, u ≠ u0 → u ≠ u1 →
      f (fun t => p (u, t)) = f (fun t => q (u, t)) := by
    intro u hu0 hu1
    congr 1
    funext t
    have hnx : p (u, t) ≠ x := by
      intro heqx
      have hx_mem : x ∈ insert x A := Finset.mem_insert_self x A
      rw [← hp0] at hx_mem
      rcases Finset.mem_image.1 hx_mem with ⟨t', _, ht'⟩
      have heq_in : (u, t) = (u0, t') := p.injective (heqx.trans ht'.symm)
      exact hu0 (congrArg Prod.fst heq_in)
    have hny : p (u, t) ≠ y := by
      intro heqy
      have hy_mem : y ∈ insert y B := Finset.mem_insert_self y B
      rw [← hp1] at hy_mem
      rcases Finset.mem_image.1 hy_mem with ⟨t', _, ht'⟩
      have heq_in : (u, t) = (u1, t') := p.injective (heqy.trans ht'.symm)
      exact hu1 (congrArg Prod.fst heq_in)
    simp [q, Equiv.swap_apply_of_ne_of_ne hnx hny]
  have hu1_mem : u1 ∈ Finset.univ.erase u0 := Finset.mem_erase.2 ⟨hu.symm, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ u0),
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ u0),
    ← Finset.add_sum_erase (Finset.univ.erase u0) _ hu1_mem,
    ← Finset.add_sum_erase (Finset.univ.erase u0) _ hu1_mem] at heq
  have htail :
      (∑ u ∈ (Finset.univ.erase u0).erase u1, f (fun t => p (u, t))) =
        ∑ u ∈ (Finset.univ.erase u0).erase u1, f (fun t => q (u, t)) := by
    refine Finset.sum_congr rfl fun u hu' => ?_
    have hne1 : u ≠ u1 := (Finset.mem_erase.1 hu').1
    have hne0 : u ≠ u0 := (Finset.mem_erase.1 (Finset.mem_erase.1 hu').2).1
    exact hrest u hne0 hne1
  rw [← add_assoc, ← add_assoc, htail] at heq
  have hpair := add_right_cancel heq
  have hinj_p : ∀ u : Fin b, Function.Injective (fun t : Fin s => p (u, t)) := fun u t1 t2 ht =>
    congrArg Prod.snd (p.injective ht)
  have hinj_q : ∀ u : Fin b, Function.Injective (fun t : Fin s => q (u, t)) := fun u t1 t2 ht =>
    congrArg Prod.snd (q.injective ht)
  have hq0 : Finset.univ.image (fun t : Fin s => q (u0, t)) = insert y A := by
    have himg : Finset.univ.image (fun t : Fin s => q (u0, t)) =
        (Finset.univ.image (fun t : Fin s => p (u0, t))).image (Equiv.swap x y) := by
      ext z; simp [q, Finset.mem_image]
    rw [himg, hp0]
    ext z
    simp only [Finset.mem_image, Finset.mem_insert]
    constructor
    · rintro ⟨w, hw | hwA, rfl⟩
      · exact Or.inl (by rw [hw, Equiv.swap_apply_left])
      · have hwx : w ≠ x := fun h' => hxA (h' ▸ hwA)
        have hwy : w ≠ y := fun h' => hyA (h' ▸ hwA)
        exact Or.inr (by rw [Equiv.swap_apply_of_ne_of_ne hwx hwy]; exact hwA)
    · rintro (hz | hzA)
      · exact ⟨x, Or.inl rfl, by rw [hz, Equiv.swap_apply_left]⟩
      · have hzx : z ≠ x := fun h' => hxA (h' ▸ hzA)
        have hzy : z ≠ y := fun h' => hyA (h' ▸ hzA)
        exact ⟨z, Or.inr hzA, Equiv.swap_apply_of_ne_of_ne hzx hzy⟩
  have hq1 : Finset.univ.image (fun t : Fin s => q (u1, t)) = insert x B := by
    have himg : Finset.univ.image (fun t : Fin s => q (u1, t)) =
        (Finset.univ.image (fun t : Fin s => p (u1, t))).image (Equiv.swap x y) := by
      ext z; simp [q, Finset.mem_image]
    rw [himg, hp1]
    ext z
    simp only [Finset.mem_image, Finset.mem_insert]
    constructor
    · rintro ⟨w, hw | hwB, rfl⟩
      · exact Or.inl (by rw [hw, Equiv.swap_apply_right])
      · have hwx : w ≠ x := fun h' => hxB (h' ▸ hwB)
        have hwy : w ≠ y := fun h' => hyB (h' ▸ hwB)
        exact Or.inr (by rw [Equiv.swap_apply_of_ne_of_ne hwx hwy]; exact hwB)
    · rintro (hz | hzB)
      · exact ⟨y, Or.inl rfl, by rw [hz, Equiv.swap_apply_right]⟩
      · have hzx : z ≠ x := fun h' => hxB (h' ▸ hzB)
        have hzy : z ≠ y := fun h' => hyB (h' ▸ hzB)
        exact ⟨z, Or.inr hzB, Equiv.swap_apply_of_ne_of_ne hzx hzy⟩
  rw [← setVal_image hb f h hconst _ (hinj_p u0), hp0,
    ← setVal_image hb f h hconst _ (hinj_p u1), hp1,
    ← setVal_image hb f h hconst _ (hinj_q u0), hq0,
    ← setVal_image hb f h hconst _ (hinj_q u1), hq1] at hpair
  exact zmod2_swap_eq hpair

private lemma diff_indep_bg {b s : ℕ} (hb : 3 ≤ b) (hs : 0 < s)
    (f : (Fin s → I b s) → K) (h : K)
    (hconst : ∀ p : Equiv.Perm (I b s), (∑ u : Fin b, f (fun t => p (u, t))) = h)
    {A A' : Finset (I b s)} (hA : A.card = s - 1) (hA' : A'.card = s - 1)
    {x y : I b s} (hxA : x ∉ A) (hyA : y ∉ A) (hxA' : x ∉ A') (hyA' : y ∉ A') :
    setVal f (insert x A) + setVal f (insert y A) =
      setVal f (insert x A') + setVal f (insert y A') := by
  by_cases hxy : x = y
  · subst hxy
    rw [zmod2_add_self, zmod2_add_self]
  · let forbid : Finset (I b s) := A ∪ A' ∪ {x, y}
    have hforb_card : forbid.card ≤ 2 * s := by
      have h1 := Finset.card_union_le (A ∪ A') {x, y}
      have h2 := Finset.card_union_le A A'
      have h3 : ({x, y} : Finset (I b s)).card ≤ 2 := Finset.card_le_two
      show (A ∪ A' ∪ {x, y}).card ≤ 2 * s
      omega
    have hrem : s - 1 ≤ (Finset.univ \ forbid).card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, card_I]
      have hbs : 3 * s ≤ b * s := Nat.mul_le_mul_right s hb
      omega
    rcases Finset.exists_subset_card_eq hrem with ⟨B, hBsub, hBcard⟩
    have hdisjA : Disjoint A B := by
      refine Finset.disjoint_left.2 fun w hwA hwB => ?_
      have hwF : w ∈ forbid := Finset.mem_union_left _ (Finset.mem_union_left _ hwA)
      exact (Finset.mem_sdiff.1 (hBsub hwB)).2 hwF
    have hdisjA' : Disjoint A' B := by
      refine Finset.disjoint_left.2 fun w hwA' hwB => ?_
      have hwF : w ∈ forbid := Finset.mem_union_left _ (Finset.mem_union_right _ hwA')
      exact (Finset.mem_sdiff.1 (hBsub hwB)).2 hwF
    have hxB : x ∉ B := fun hx =>
      (Finset.mem_sdiff.1 (hBsub hx)).2 (Finset.mem_union_right _ (by simp))
    have hyB : y ∉ B := fun hy =>
      (Finset.mem_sdiff.1 (hBsub hy)).2 (Finset.mem_union_right _ (by simp))
    rw [swap_two_blocks hb f h hconst hA hBcard hdisjA hxy hxA hyA hxB hyB,
      swap_two_blocks hb f h hconst hA' hBcard hdisjA' hxy hxA' hyA' hxB hyB]

private lemma const_of_single_swap {α : Type*} [DecidableEq α] (s : ℕ)
    (G : Finset α → K)
    (hswap : ∀ (A : Finset α) (x y : α), A.card = s - 1 → x ∉ A → y ∉ A →
      G (insert x A) = G (insert y A)) :
    ∀ (k : ℕ) (S1 S2 : Finset α), S1.card = s → S2.card = s → (S1 \ S2).card = k →
      G S1 = G S2
  | 0, S1, S2, h1, h2, hk => by
      have hsub : S1 ⊆ S2 := Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 hk)
      have heq : S1 = S2 := Finset.eq_of_subset_of_card_le hsub (by omega)
      rw [heq]
  | k + 1, S1, S2, h1, h2, hk => by
      have hne12 : (S1 \ S2).Nonempty := Finset.card_pos.1 (by omega)
      rcases hne12 with ⟨x, hx⟩
      have hx1 : x ∈ S1 := (Finset.mem_sdiff.1 hx).1
      have hx2 : x ∉ S2 := (Finset.mem_sdiff.1 hx).2
      have hne21 : (S2 \ S1).Nonempty := by
        by_contra hem
        rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hem
        have heq : S2 = S1 := Finset.eq_of_subset_of_card_le hem (by omega)
        subst heq
        exact hx2 hx1
      rcases hne21 with ⟨y, hy⟩
      have hy2 : y ∈ S2 := (Finset.mem_sdiff.1 hy).1
      have hy1 : y ∉ S1 := (Finset.mem_sdiff.1 hy).2
      let A := S1.erase x
      have hAcard : A.card = s - 1 := by
        rw [Finset.card_erase_of_mem hx1, h1]
      have hxA : x ∉ A := Finset.notMem_erase x S1
      have hyA : y ∉ A := fun h => hy1 (Finset.mem_of_mem_erase h)
      have hS1eq : insert x A = S1 := Finset.insert_erase hx1
      let S1' := insert y A
      have hS1'card : S1'.card = s := by
        rw [Finset.card_insert_of_notMem hyA, hAcard]
        have : 1 ≤ S1.card := Finset.card_pos.2 ⟨x, hx1⟩
        omega
      have hsdiff_eq : S1' \ S2 = (S1 \ S2).erase x := by
        ext w
        simp only [S1', A, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨rfl | ⟨hwx, hw1⟩, hw2⟩
          · exact absurd hy2 hw2
          · exact ⟨hwx, hw1, hw2⟩
        · rintro ⟨hwx, hw1, hw2⟩
          exact ⟨Or.inr ⟨hwx, hw1⟩, hw2⟩
      have hk' : (S1' \ S2).card = k := by
        rw [hsdiff_eq, Finset.card_erase_of_mem hx, hk]
        omega
      have hstep : G S1 = G S1' := by
        rw [← hS1eq]
        exact hswap A x y hAcard hxA hyA
      rw [hstep]
      exact const_of_single_swap s G hswap k S1' S2 hS1'card h2 hk'

end PEqualNP.Outside.L_lib_710_aux

theorem PEqualNP.Outside.L_lib_710 :
∀ (b s : Nat), 3 ≤ b → 0 < s →
  let I := Fin b × Fin s
  let K := ZMod 2
  ∀ f : (Fin s → I) → K,
    (∃ h : K, ∀ p : Equiv.Perm I, (∑ u : Fin b, f (fun t => p (u,t))) = h) ↔
    (∃ (c : K) (z : I → K), ∀ v : Fin s → I, Function.Injective v →
      f v = c + ∑ t : Fin s, z (v t)) := by
  intro b s hb hs I K f
  constructor
  · rintro ⟨h, hconst⟩
    let a0 : I := (⟨0, by omega⟩, ⟨0, hs⟩)
    have hbg_exists : ∀ x : I, ∃ B : Finset I, B.card = s - 1 ∧ a0 ∉ B ∧ x ∉ B := by
      intro x
      have hrem : s - 1 ≤ (Finset.univ \ ({a0, x} : Finset I)).card := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
          PEqualNP.Outside.L_lib_710_aux.card_I]
        have h2 : ({a0, x} : Finset I).card ≤ 2 := Finset.card_le_two
        have hbs : 3 * s ≤ b * s := Nat.mul_le_mul_right s hb
        omega
      rcases Finset.exists_subset_card_eq hrem with ⟨B, hBsub, hBcard⟩
      refine ⟨B, hBcard, ?_, ?_⟩
      · intro ha
        exact (Finset.mem_sdiff.1 (hBsub ha)).2 (by simp)
      · intro hx
        exact (Finset.mem_sdiff.1 (hBsub hx)).2 (by simp)
    let bg : I → Finset I := fun x => Classical.choose (hbg_exists x)
    let z : I → K := fun x =>
      PEqualNP.Outside.L_lib_710_aux.setVal f (insert x (bg x)) +
        PEqualNP.Outside.L_lib_710_aux.setVal f (insert a0 (bg x))
    have hdiff_z : ∀ (A : Finset I) (x y : I), A.card = s - 1 → x ∉ A → y ∉ A →
        PEqualNP.Outside.L_lib_710_aux.setVal f (insert x A) +
          PEqualNP.Outside.L_lib_710_aux.setVal f (insert y A) = z x + z y := by
      intro A x y hA hxA hyA
      have hrem : s - 1 ≤ (Finset.univ \ ({a0, x, y} : Finset I)).card := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
          PEqualNP.Outside.L_lib_710_aux.card_I]
        have h3 : ({a0, x, y} : Finset I).card ≤ 3 := by
          calc
            ({a0, x, y} : Finset I).card ≤ ({x, y} : Finset I).card + 1 := Finset.card_insert_le _ _
            _ ≤ 2 + 1 := Nat.add_le_add_right Finset.card_le_two 1
        have hbs : 3 * s ≤ b * s := Nat.mul_le_mul_right s hb
        omega
      rcases Finset.exists_subset_card_eq hrem with ⟨B, hBsub, hBcard⟩
      have haB : a0 ∉ B := fun ha => (Finset.mem_sdiff.1 (hBsub ha)).2 (by simp)
      have hxB : x ∉ B := fun hx => (Finset.mem_sdiff.1 (hBsub hx)).2 (by simp)
      have hyB : y ∉ B := fun hy => (Finset.mem_sdiff.1 (hBsub hy)).2 (by simp)
      have hsp_x := Classical.choose_spec (hbg_exists x)
      have hsp_y := Classical.choose_spec (hbg_exists y)
      have hzx : z x = PEqualNP.Outside.L_lib_710_aux.setVal f (insert x B) +
          PEqualNP.Outside.L_lib_710_aux.setVal f (insert a0 B) :=
        PEqualNP.Outside.L_lib_710_aux.diff_indep_bg hb hs f h hconst
          hsp_x.1 hBcard hsp_x.2.2 hsp_x.2.1 hxB haB
      have hzy : z y = PEqualNP.Outside.L_lib_710_aux.setVal f (insert y B) +
          PEqualNP.Outside.L_lib_710_aux.setVal f (insert a0 B) :=
        PEqualNP.Outside.L_lib_710_aux.diff_indep_bg hb hs f h hconst
          hsp_y.1 hBcard hsp_y.2.2 hsp_y.2.1 hyB haB
      have hxy : PEqualNP.Outside.L_lib_710_aux.setVal f (insert x A) +
          PEqualNP.Outside.L_lib_710_aux.setVal f (insert y A) =
          PEqualNP.Outside.L_lib_710_aux.setVal f (insert x B) +
            PEqualNP.Outside.L_lib_710_aux.setVal f (insert y B) :=
        PEqualNP.Outside.L_lib_710_aux.diff_indep_bg hb hs f h hconst
          hA hBcard hxA hyA hxB hyB
      rw [hzx, hzy, hxy]
      have hadd : ∀ p q r : K, (p + r) + (q + r) = p + q := by decide
      exact (hadd _ _ _).symm
    let G : Finset I → K := fun S => PEqualNP.Outside.L_lib_710_aux.setVal f S + ∑ w ∈ S, z w
    have hGswap : ∀ (A : Finset I) (x y : I), A.card = s - 1 → x ∉ A → y ∉ A →
        G (insert x A) = G (insert y A) := by
      intro A x y hA hxA hyA
      apply PEqualNP.Outside.L_lib_710_aux.zmod2_eq_of_add_eq_zero
      dsimp only [G]
      rw [Finset.sum_insert hxA, Finset.sum_insert hyA]
      have hd := hdiff_z A x y hA hxA hyA
      have halg : ∀ f1 f2 zx zy sa : K, f1 + f2 = zx + zy →
          (f1 + (zx + sa)) + (f2 + (zy + sa)) = 0 := by decide
      exact halg _ _ _ _ _ hd
    let S0 : Finset I := Finset.univ.image (fun t : Fin s => (⟨0, by omega⟩, t))
    have hS0card : S0.card = s := by
      rw [Finset.card_image_of_injective _ (fun t1 t2 ht => congrArg Prod.snd ht),
        Finset.card_univ, Fintype.card_fin]
    refine ⟨G S0, z, fun v hv => ?_⟩
    let S : Finset I := Finset.univ.image v
    have hScard : S.card = s := by
      rw [Finset.card_image_of_injective _ hv, Finset.card_univ, Fintype.card_fin]
    have hGeq : G S = G S0 :=
      PEqualNP.Outside.L_lib_710_aux.const_of_single_swap s G hGswap (S \ S0).card S S0 hScard hS0card rfl
    have hFv : PEqualNP.Outside.L_lib_710_aux.setVal f S = f v :=
      PEqualNP.Outside.L_lib_710_aux.setVal_image hb f h hconst v hv
    have hsum_v : (∑ w ∈ S, z w) = ∑ t : Fin s, z (v t) := by
      rw [Finset.sum_image (fun t1 _ t2 _ ht => hv ht)]
    dsimp only [G] at hGeq
    rw [hFv, hsum_v] at hGeq
    have hfin := congrArg (fun a : K => a + ∑ t : Fin s, z (v t)) hGeq
    rw [PEqualNP.Outside.L_lib_710_aux.zmod2_add_cancel_right] at hfin
    exact hfin
  · rintro ⟨c, z, hf⟩
    refine ⟨(b : K) * c + ∑ x : I, z x, fun p => ?_⟩
    have hstep : ∀ u : Fin b,
        f (fun t : Fin s => p (u, t)) = c + ∑ t : Fin s, z (p (u, t)) := by
      intro u
      exact hf (fun t => p (u, t)) (fun t1 t2 ht => congrArg Prod.snd (p.injective ht))
    simp_rw [hstep]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1
    rw [← Fintype.sum_prod_type']
    exact Equiv.sum_comp p z
