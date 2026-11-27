import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_666_aux

open Classical

abbrev K := ZMod 2

lemma z2_add_self (x : K) : x + x = 0 := by
  fin_cases x <;> decide

lemma z2_vec_add_self {n : ℕ} (v : Fin n → K) : v + v = 0 := by
  funext i
  exact z2_add_self (v i)

lemma fiber_card_of_surj {r d : ℕ} (hdr : d ≤ r)
    (f : (Fin r → K) →ₗ[K] (Fin d → K)) (hsurj : Function.Surjective f) (y : Fin d → K) :
    (Finset.univ.filter (fun v : Fin r → K => f v = y)).card = 2 ^ (r - d) := by
  let kerF := Finset.univ.filter (fun v : Fin r → K => f v = 0)
  have hfiber : ∀ z : Fin d → K,
      (Finset.univ.filter (fun v : Fin r → K => f v = z)).card = kerF.card := by
    intro z
    obtain ⟨v0, hv0⟩ := hsurj z
    symm
    refine Finset.card_bij (fun w _ => w + v0) ?_ ?_ ?_
    · intro w hw
      have hw0 : f w = 0 := (Finset.mem_filter.mp hw).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [map_add, hw0, hv0, zero_add]
    · intro w1 _ w2 _ hEq
      exact add_right_cancel hEq
    · intro v hv
      have hvz : f v = z := (Finset.mem_filter.mp hv).2
      refine ⟨v + v0, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [map_add, hvz, hv0, z2_vec_add_self]
      · rw [add_assoc, z2_vec_add_self, add_zero]
  have hpart : Fintype.card (Fin r → K) = Fintype.card (Fin d → K) * kerF.card := by
    have h1 : (Finset.univ : Finset (Fin r → K)).card =
        ∑ z : Fin d → K, (Finset.univ.filter (fun v : Fin r → K => f v = z)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext v; simp
      · intro z1 _ z2 _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro v h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    rw [Finset.card_univ] at h1
    rw [h1, Finset.sum_congr rfl (fun z _ => hfiber z), Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hV : Fintype.card (Fin r → K) = 2 ^ r := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hD : Fintype.card (Fin d → K) = 2 ^ d := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [hV, hD] at hpart
  have hpow : 2 ^ d * 2 ^ (r - d) = 2 ^ r := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hdr]
  have hpos : 0 < 2 ^ d := Nat.pow_pos (by omega)
  have hker : kerF.card = 2 ^ (r - d) :=
    Nat.eq_of_mul_eq_mul_left hpos (hpart.symm.trans hpow.symm)
  rw [hfiber y, hker]

lemma card_equiv_of_card_eq {α β : Type*} [Fintype α] [Fintype β] {N : ℕ}
    (hα : Fintype.card α = N) (hβ : Fintype.card β = N) :
    Nat.card (α ≃ β) = Nat.factorial N := by
  let eα : α ≃ Fin N := Fintype.equivFinOfCardEq hα
  let eβ : β ≃ Fin N := Fintype.equivFinOfCardEq hβ
  let e : (α ≃ β) ≃ Equiv.Perm (Fin N) :=
    { toFun := fun g => (eα.symm.trans g).trans eβ
      invFun := fun p => (eα.trans p).trans eβ.symm
      left_inv := fun g => by ext x; simp
      right_inv := fun p => by ext x; simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

noncomputable def flatCEquiv {r d : ℕ}
    (f : (Fin r → K) →ₗ[K] (Fin d → K))
    (tags : (Fin r → K) → (Fin r → K))
    (c : Fin d → K) :
    { p : Equiv.Perm (Fin r → K) // ∀ i : Fin r → K, f (p i) = c + f (tags i) } ≃
      ((j : Fin d → K) →
        { a : Fin r → K // f (tags a) = j } ≃
        { v : Fin r → K // f v = c + j }) :=
  let V := Fin r → K
  let D := Fin d → K
  let toFam : { p : Equiv.Perm V // ∀ i : V, f (p i) = c + f (tags i) } →
      ((j : D) → ({ a : V // f (tags a) = j } ≃ { v : V // f v = c + j })) := fun p j =>
    { toFun := fun a => ⟨p.1 a.1, by rw [p.2 a.1, a.2]⟩
      invFun := fun v => ⟨p.1.symm v.1, by
        have hp := p.2 (p.1.symm v.1)
        rw [Equiv.apply_symm_apply] at hp
        exact add_left_cancel (hp.symm.trans v.2)⟩
      left_inv := fun a => Subtype.ext (p.1.symm_apply_apply a.1)
      right_inv := fun v => Subtype.ext (p.1.apply_symm_apply v.1) }
  let ofFam : ((j : D) → ({ a : V // f (tags a) = j } ≃ { v : V // f v = c + j })) →
      { p : Equiv.Perm V // ∀ i : V, f (p i) = c + f (tags i) } := fun g =>
    let fwd : V → V := fun a => (g (f (tags a)) ⟨a, rfl⟩).1
    let bwd : V → V := fun v =>
      ((g (c + f v)).symm ⟨v, by rw [← add_assoc, z2_vec_add_self, zero_add]⟩).1
    have hleft : Function.LeftInverse bwd fwd := by
      intro a
      let j : D := f (tags a)
      let aSub : { x : V // f (tags x) = j } := ⟨a, rfl⟩
      let vSub : { x : V // f x = c + j } := g j aSub
      have hcfv : c + f vSub.1 = j := by rw [vSub.2, ← add_assoc, z2_vec_add_self, zero_add]
      have hcongr : ∀ (j1 j2 : D) (h1 : f vSub.1 = c + j1) (h2 : f vSub.1 = c + j2),
          j1 = j2 → ((g j1).symm ⟨vSub.1, h1⟩).1 = ((g j2).symm ⟨vSub.1, h2⟩).1 := by
        rintro j1 _ h1 h2 rfl; rfl
      change ((g (c + f vSub.1)).symm ⟨vSub.1, _⟩).1 = a
      rw [hcongr (c + f vSub.1) j _ vSub.2 hcfv]
      exact congrArg Subtype.val ((g j).symm_apply_apply aSub)
    have hright : Function.RightInverse bwd fwd := by
      intro v
      let j : D := c + f v
      let vSub : { x : V // f x = c + j } :=
        ⟨v, by dsimp only [j]; rw [← add_assoc, z2_vec_add_self, zero_add]⟩
      let aSub : { x : V // f (tags x) = j } := (g j).symm vSub
      have hcongr : ∀ (j1 j2 : D) (h1 : f (tags aSub.1) = j1) (h2 : f (tags aSub.1) = j2),
          j1 = j2 → (g j1 ⟨aSub.1, h1⟩).1 = (g j2 ⟨aSub.1, h2⟩).1 := by
        rintro j1 _ h1 h2 rfl; rfl
      change (g (f (tags aSub.1)) ⟨aSub.1, _⟩).1 = v
      rw [hcongr (f (tags aSub.1)) j _ aSub.2 aSub.2]
      exact congrArg Subtype.val ((g j).apply_symm_apply vSub)
    let p : Equiv.Perm V :=
      { toFun := fwd
        invFun := bwd
        left_inv := hleft
        right_inv := hright }
    ⟨p, fun a => (g (f (tags a)) ⟨a, rfl⟩).2⟩
  { toFun := toFam
    invFun := ofFam
    left_inv := fun p => Subtype.ext (Equiv.ext (fun _ => rfl))
    right_inv := fun g => by
      funext j
      refine Equiv.ext (fun a => Subtype.ext ?_)
      have hcongr : ∀ (j1 j2 : D) (h1 : f (tags a.1) = j1) (h2 : f (tags a.1) = j2),
          j1 = j2 → (g j1 ⟨a.1, h1⟩).1 = (g j2 ⟨a.1, h2⟩).1 := by
        rintro j1 _ h1 h2 rfl; rfl
      exact hcongr (f (tags a.1)) j rfl a.2 a.2 }

lemma flatC_card_eq {r d : ℕ} (hdr : d ≤ r)
    (f : (Fin r → K) →ₗ[K] (Fin d → K)) (hsurj : Function.Surjective f)
    (tags : (Fin r → K) → (Fin r → K))
    (hbal : ∀ j : Fin d → K,
      (Finset.univ.filter (fun a : Fin r → K => f (tags a) = j)).card = 2 ^ (r - d))
    (c : Fin d → K) :
    (Finset.univ.filter (fun p : Equiv.Perm (Fin r → K) =>
      ∀ i : Fin r → K, f (p i) = c + f (tags i))).card =
      (Nat.factorial (2 ^ (r - d))) ^ (2 ^ d) := by
  let FC := Finset.univ.filter (fun p : Equiv.Perm (Fin r → K) =>
    ∀ i : Fin r → K, f (p i) = c + f (tags i))
  let eSub : ↥FC ≃ { p : Equiv.Perm (Fin r → K) // ∀ i : Fin r → K, f (p i) = c + f (tags i) } :=
    { toFun := fun p => ⟨p.1, (Finset.mem_filter.mp p.2).2⟩
      invFun := fun p => ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.2⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 : FC.card = Nat.card ↥FC := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [show (Finset.univ.filter (fun p : Equiv.Perm (Fin r → K) =>
      ∀ i : Fin r → K, f (p i) = c + f (tags i))).card = FC.card from rfl]
  rw [h1, Nat.card_congr eSub, Nat.card_congr (flatCEquiv f tags c), Nat.card_pi]
  have hterm : ∀ j : Fin d → K,
      Nat.card ({ a : Fin r → K // f (tags a) = j } ≃ { v : Fin r → K // f v = c + j }) =
        Nat.factorial (2 ^ (r - d)) := by
    intro j
    refine card_equiv_of_card_eq ?_ ?_
    · rw [Fintype.card_subtype]; exact hbal j
    · rw [Fintype.card_subtype]; exact fiber_card_of_surj hdr f hsurj (c + j)
  simp_rw [hterm]
  rw [Finset.prod_const, Finset.card_univ,
    Fintype.card_fun, ZMod.card, Fintype.card_fin]

lemma main_proof (r d : ℕ) (hdr : d ≤ r)
    (f : (Fin r → K) →ₗ[K] (Fin d → K)) (hsurj : Function.Surjective f)
    (tags : (Fin r → K) → (Fin r → K)) :
    let V := Fin r → K
    let D := Fin d → K
    let flat := (Finset.univ : Finset (Equiv.Perm V)).filter (fun p =>
      ∃ c : D, ∀ i, f (p i + tags i) = c)
    let balanced := ∀ j : D,
      ((Finset.univ : Finset V).filter (fun a => f (tags a) = j)).card = 2 ^ (r - d)
    flat.card = if balanced then (2 ^ d) * (Nat.factorial (2 ^ (r - d))) ^ (2 ^ d) else 0 := by
  intro V D flat balanced
  have hcond_iff : ∀ (p : Equiv.Perm V) (c : D),
      (∀ i : V, f (p i + tags i) = c) ↔ (∀ i : V, f (p i) = c + f (tags i)) := by
    intro p c
    constructor
    · intro h i
      have hi := h i
      rw [map_add] at hi
      have h1 := congrArg (· + f (tags i)) hi
      rw [add_assoc, z2_vec_add_self, add_zero] at h1
      exact h1
    · intro h i
      rw [map_add, h i, add_assoc, z2_vec_add_self, add_zero]
  let flatC : D → Finset (Equiv.Perm V) := fun c =>
    Finset.univ.filter (fun p : Equiv.Perm V => ∀ i : V, f (p i) = c + f (tags i))
  have hflat_eq : flat = Finset.univ.biUnion flatC := by
    ext p
    simp only [flat, flatC, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    exact exists_congr (fun c => hcond_iff p c)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset D) : Set D) flatC := by
    intro c1 _ c2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p h1 h2
    have e1 := (Finset.mem_filter.mp h1).2 0
    have e2 := (Finset.mem_filter.mp h2).2 0
    exact hne (add_right_cancel (e1.symm.trans e2))
  have hflat_card : flat.card = ∑ c : D, (flatC c).card := by
    rw [hflat_eq, Finset.card_biUnion hdisj]
  by_cases hbal : balanced
  · simp only [hbal, ↓reduceIte, hflat_card]
    rw [Finset.sum_congr rfl (fun c _ => flatC_card_eq hdr f hsurj tags hbal c),
      Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  · simp only [hbal, ↓reduceIte, hflat_card]
    apply Finset.sum_eq_zero
    intro c _
    apply Finset.card_eq_zero.mpr
    ext p
    simp only [Finset.notMem_empty, iff_false]
    intro hp
    have hp' := (Finset.mem_filter.mp hp).2
    apply hbal
    intro j
    have hcard_eq : (Finset.univ.filter (fun a : V => f (tags a) = j)).card =
        (Finset.univ.filter (fun v : V => f v = c + j)).card := by
      refine Finset.card_bij (fun a _ => p a) ?_ ?_ ?_
      · intro a ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hp' a, (Finset.mem_filter.mp ha).2]⟩
      · intro a1 _ a2 _ hEq
        exact p.injective hEq
      · intro v hv
        refine ⟨p.symm v, ?_, p.apply_symm_apply v⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        have h1 := hp' (p.symm v)
        rw [p.apply_symm_apply] at h1
        exact add_left_cancel (h1.symm.trans (Finset.mem_filter.mp hv).2)
    rw [hcard_eq, fiber_card_of_surj hdr f hsurj (c + j)]

end PEqualNP.Outside.L_lib_666_aux

theorem PEqualNP.Outside.L_lib_666 :
∀ (r d : Nat), d ≤ r →
  let K := ZMod 2
  let V := Fin r → K
  let D := Fin d → K
  ∀ (f : V →ₗ[K] D), Function.Surjective f → ∀ tags : V → V,
    let flat := (Finset.univ : Finset (Equiv.Perm V)).filter (fun p =>
      ∃ c : D, ∀ i, f (p i + tags i) = c)
    let balanced := ∀ j : D,
      ((Finset.univ : Finset V).filter (fun a => f (tags a) = j)).card = 2^(r-d)
    flat.card = if balanced then (2^d)*(Nat.factorial (2^(r-d)))^(2^d) else 0 := by
  intro r d hdr
  dsimp only
  intro f hsurj tags
  exact PEqualNP.Outside.L_lib_666_aux.main_proof r d hdr f hsurj tags
