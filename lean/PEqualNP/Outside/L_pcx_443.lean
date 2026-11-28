import Mathlib

namespace PEqualNP.Outside.L_pcx_443

section Affine

open MvPolynomial

private def hard443 : ℕ → ℕ → ℕ → Prop :=
  let K := ZMod 2
  fun (r k D : ℕ) =>
    let I := Fin r → K
    let U := Fin k → K
    let P := MvPolynomial (Fin r ⊕ Fin k) K
    let val := fun (p : P) (i : I) (u : U) => MvPolynomial.eval (Sum.elim i u) p
    ∃ (F : I → Finset P) (w : I → U),
      (∀ i, ∀ p ∈ F i, p.totalDegree ≤ D) ∧
      (∀ i u, ∃ p ∈ F i, val p i u = 1) ∧
      ∀ i j, i ≠ j → ∀ p ∈ F i, val p j (w j) = 0

private theorem add_self443 (x : ZMod 2) : x + x = 0 := by
  rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]

private theorem eval_affine443 {σ : Type*} (p : MvPolynomial σ (ZMod 2))
    (hp : p.totalDegree ≤ 1) (x y z : σ → ZMod 2) :
    eval (x + y + z) p = eval x p + eval y p + eval z p := by
  classical
  simp only [eval_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  have hdeg : (s.sum fun _ e => e) ≤ 1 := (le_totalDegree hs).trans hp
  -- Each supported monomial is constant or a scalar multiple of one variable.
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdeg with hzero | hone
  · have hs0 : s = 0 := by
      ext a
      by_contra h
      have ha : a ∈ s.support := Finsupp.mem_support_iff.mpr (by simpa using h)
      have hle : s a ≤ s.sum (fun _ e => e) :=
        Finset.single_le_sum (fun b _ => Nat.zero_le (s b)) ha
      rw [hzero] at hle
      exact h (by simpa using hle)
    subst s
    simp [add_self443]
  · obtain ⟨a, rfl⟩ := (Finsupp.sum_eq_one_iff s).mp hone
    simp [Finsupp.support_single, Pi.add_apply, mul_add]

private theorem affine443 : ∀ r k : ℕ, hard443 r k 1 ↔ r ≤ 1 := by
  classical
  intro r k
  constructor
  · rintro ⟨F, w, hdeg, hcover, hzero⟩
    by_contra! hr
    -- Lift the three nonzero corners of a coordinate square using their witnesses.
    let a : Fin r := ⟨0, by omega⟩
    let b : Fin r := ⟨1, by omega⟩
    have hab : a ≠ b := by
      intro h
      have hv := congrArg Fin.val h
      simp [a, b] at hv
    let iA : Fin r → ZMod 2 := fun t => if t = a then 1 else 0
    let iB : Fin r → ZMod 2 := fun t => if t = b then 1 else 0
    let iAB := iA + iB
    have ha : 0 ≠ iA := by
      intro h
      have hAt := congrFun h a
      simp [iA] at hAt
    have hb : 0 ≠ iB := by
      intro h
      have hAt := congrFun h b
      simp [iB] at hAt
    have hab' : 0 ≠ iAB := by
      intro h
      have hAt := congrFun h a
      simp [iAB, iA, iB, hab] at hAt
    let u := w iA + w iB + w iAB
    obtain ⟨p, hp, hp1⟩ := hcover 0 u
    have hs : Sum.elim (0 : Fin r → ZMod 2) u =
        Sum.elim iA (w iA) + Sum.elim iB (w iB) + Sum.elim iAB (w iAB) := by
      funext t
      cases t with
      | inl t => exact (add_self443 (iA t + iB t)).symm
      | inr t => rfl
    change eval (Sum.elim (0 : Fin r → ZMod 2) u) p = 1 at hp1
    change (∀ i j, i ≠ j → ∀ p ∈ F i, eval (Sum.elim j (w j)) p = 0) at hzero
    rw [hs, eval_affine443 p (hdeg 0 p hp)] at hp1
    have hz : (0 : ZMod 2) = 1 := by
      simpa only [hzero 0 iA ha p hp, hzero 0 iB hb p hp, hzero 0 iAB hab' p hp, zero_add]
        using hp1
    exact zero_ne_one hz
  · intro hr
    let factor (i : Fin r → ZMod 2) (a : Fin r) : MvPolynomial (Fin r ⊕ Fin k) (ZMod 2) :=
      1 + (X (Sum.inl a) + C (i a))
    let pol (i : Fin r → ZMod 2) := ∏ a, factor i a
    refine ⟨fun i => {pol i}, fun _ => 0, ?_, ?_, ?_⟩
    · intro i p hp
      rw [Finset.mem_singleton.mp hp]
      calc
        (pol i).totalDegree ≤ ∑ a, (factor i a).totalDegree := totalDegree_finsetProd _ _
        _ ≤ ∑ _a : Fin r, 1 := by
          apply Finset.sum_le_sum
          intro a _
          have hf : (X (Sum.inl a) + C (i a) : MvPolynomial (Fin r ⊕ Fin k) (ZMod 2)).totalDegree ≤ 1 := by
            simpa using totalDegree_add (X (Sum.inl a) : MvPolynomial (Fin r ⊕ Fin k) (ZMod 2)) (C (i a))
          exact (totalDegree_add _ _).trans (by simpa [factor] using hf)
        _ = r := by simp
        _ ≤ 1 := hr
    · intro i u
      exact ⟨pol i, Finset.mem_singleton_self _, by simp [pol, factor, map_prod, map_add, add_self443]⟩
    · intro i j hij p hp
      rw [Finset.mem_singleton.mp hp]
      obtain ⟨a, ha⟩ : ∃ a, i a ≠ j a := by
        by_contra! h
        exact hij (funext h)
      have hbit : ∀ x y : ZMod 2, x ≠ y → 1 + (y + x) = 0 := by decide
      simp only [pol, factor, map_prod, map_add, map_one, eval_X, eval_C, Sum.elim_inl]
      exact Finset.prod_eq_zero (Finset.mem_univ a) (hbit (i a) (j a) ha)

end Affine

private theorem dim443 (r k D : ℕ) :
    (let K := ZMod 2
     let I := Fin r → K
     let U := Fin k → K
     let P := MvPolynomial (Fin r ⊕ Fin k) K
     let val := fun (p : P) (i : I) (u : U) => MvPolynomial.eval (Sum.elim i u) p
     ∃ (F : I → Finset P) (w : I → U),
       (∀ i, ∀ p ∈ F i, p.totalDegree ≤ D) ∧
       (∀ i u, ∃ p ∈ F i, val p i u = 1) ∧
       ∀ i j, i ≠ j → ∀ p ∈ F i, val p j (w j) = 0) →
      2 ^ r ≤ ∑ j ∈ Finset.range (D + 1), (r + k).choose j := by
  classical
  intro hard
  obtain ⟨F, w, hdeg, hcover, hvanish⟩ := hard
  let K := ZMod 2
  let I := Fin r → K
  let σ := Fin r ⊕ Fin k
  let S : Finset (Finset σ) := (Finset.range (D + 1)).biUnion (fun j => Finset.univ.powersetCard j)
  let lift (i : I) : σ → K := Sum.elim i (w i)
  -- Evaluate the squarefree monomials of degree at most D at the private lifts.
  let E : (↥S → K) →ₗ[K] (I → K) :=
    { toFun := fun a i => ∑ t : ↥S, a t * ∏ x ∈ t.val, lift i x
      map_add' := by
        intro a b
        funext i
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        funext i
        simp [smul_eq_mul, mul_assoc, Finset.mul_sum] }
  have hcard (p : MvPolynomial σ K) (hp : p.totalDegree ≤ D)
      (s : σ →₀ ℕ) (hs : s ∈ p.support) : s.support ∈ S := by
    have h : s.support.card ≤ D := calc
      s.support.card = ∑ x ∈ s.support, 1 := by simp
      _ ≤ s.sum (fun _ e => e) := by
        apply Finset.sum_le_sum
        intro x hx
        exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hx)
      _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hs
      _ ≤ D := hp
    exact Finset.mem_biUnion.mpr ⟨s.support.card, Finset.mem_range.mpr (by omega),
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩
  have hsingle (t : ↥S) (c : K) (i : I) :
      E (Pi.single t c) i = c * ∏ x ∈ t.val, lift i x := by
    change (∑ u : ↥S, (Pi.single t c : ↥S → K) u * ∏ x ∈ u.val, lift i x) = _
    rw [Finset.sum_eq_single t]
    · simp
    · intro u _ hut
      rw [Pi.single_eq_of_ne hut, zero_mul]
    · simp
  have hpoly (p : MvPolynomial σ K) (hp : p.totalDegree ≤ D) :
      ∃ a, ∀ i : I, E a i = MvPolynomial.eval (lift i) p := by
    refine ⟨∑ s ∈ p.support.attach, Pi.single
      (⟨s.val.support, hcard p hp s.val s.property⟩ : ↥S) (p.coeff s.val), ?_⟩
    intro i
    rw [map_sum, Finset.sum_apply]
    simp only [hsingle]
    rw [Finset.sum_attach p.support (fun s => p.coeff s * ∏ x ∈ s.support, lift i x)]
    conv_rhs => rw [p.as_sum]
    rw [MvPolynomial.eval_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [MvPolynomial.eval_monomial, Finsupp.prod]
    congr 1
    apply Finset.prod_congr rfl
    intro x hx
    have hpow : ∀ (a : ZMod 2) (n : ℕ), n ≠ 0 → a ^ n = a := by
      intro a n hn
      have ha : a = 0 ∨ a = 1 := by
        fin_cases a
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases ha with rfl | rfl
      · exact zero_pow hn
      · exact one_pow _
    exact (hpow _ _ (Finsupp.mem_support_iff.mp hx)).symm
  have hbasis : ∀ i : I, ∃ a, E a = Pi.single i (1 : K) := by
    intro i
    obtain ⟨p, hp, hev⟩ := hcover i (w i)
    obtain ⟨a, ha⟩ := hpoly p (hdeg i p hp)
    refine ⟨a, funext fun j => ?_⟩
    rw [ha]
    by_cases hji : j = i
    · subst j
      simpa using hev
    · rw [Pi.single_eq_of_ne hji]
      exact hvanish i j (Ne.symm hji) p hp
  choose a ha using hbasis
  have hsurj : Function.Surjective E := by
    intro f
    refine ⟨∑ i : I, f i • a i, ?_⟩
    funext j
    rw [map_sum, Finset.sum_apply]
    simp only [map_smul, ha, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [Pi.single_eq_of_ne (Ne.symm hij), mul_zero]
    · simp
  have hd := LinearMap.finrank_le_finrank_of_surjective hsurj
  rw [Module.finrank_pi, Module.finrank_pi] at hd
  have hS : S.card ≤ ∑ j ∈ Finset.range (D + 1), (r + k).choose j := by
    dsimp [S]
    exact Finset.card_biUnion_le.trans_eq (by simp [Finset.card_powersetCard, σ])
  exact (show 2 ^ r ≤ S.card by simpa [I, K, Fintype.card_fun] using hd).trans hS

open scoped BigOperators

private abbrev BlockAux443 (A : Type*) := {s : Finset A // 2 ≤ s.card}

section Block

variable {A : Type*} [LinearOrder A]

-- A stored squarefree monomial is read from one coordinate, including for
-- degrees zero and one, where the coordinate is a constant or an address bit.
private noncomputable def blockMonomial443 (s : Finset A) :
    MvPolynomial (A ⊕ BlockAux443 A) (ZMod 2) :=
  if h : 2 ≤ s.card then MvPolynomial.X (Sum.inr ⟨s, h⟩)
  else if h' : s.Nonempty then MvPolynomial.X (Sum.inl (s.max' h')) else 1

private def blockLift443 (i : A → ZMod 2) (s : BlockAux443 A) : ZMod 2 :=
  ∏ a ∈ s.val, i a

private lemma blockMonomialDegree443 (s : Finset A) :
    (blockMonomial443 s).totalDegree ≤ 1 := by
  unfold blockMonomial443
  split
  · simp
  · split <;> simp

private lemma blockMonomialEval443 (i : A → ZMod 2) (u : BlockAux443 A → ZMod 2)
    (s : Finset A) (hu : ∀ h : 2 ≤ s.card, u ⟨s, h⟩ = blockLift443 i ⟨s, h⟩) :
    MvPolynomial.eval (Sum.elim i u) (blockMonomial443 s) = ∏ a ∈ s, i a := by
  by_cases h : 2 ≤ s.card
  · simpa [blockMonomial443, h, blockLift443] using hu h
  by_cases hs : s.Nonempty
  · have hc : s.card = 1 := by have := hs.card_pos; omega
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
    simp [blockMonomial443]
  · have he := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp [blockMonomial443]

private def blockLast443 (s : BlockAux443 A) : A :=
  s.val.max' (Finset.card_pos.mp (by have := s.property; omega))

private lemma blockLastMem443 (s : BlockAux443 A) : blockLast443 s ∈ s.val :=
  Finset.max'_mem _ _

private noncomputable def blockConstraint443 (s : BlockAux443 A) :
    MvPolynomial (A ⊕ BlockAux443 A) (ZMod 2) :=
  MvPolynomial.X (Sum.inr s) -
    blockMonomial443 (s.val.erase (blockLast443 s)) * MvPolynomial.X (Sum.inl (blockLast443 s))

private lemma blockConstraintDegree443 (s : BlockAux443 A) :
    (blockConstraint443 s).totalDegree ≤ 2 := by
  unfold blockConstraint443
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le (by simp)
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simpa using Nat.add_le_add_right (blockMonomialDegree443 (s.val.erase (blockLast443 s))) 1

private lemma blockConstraintEval443 (i : A → ZMod 2) (s : BlockAux443 A) :
    MvPolynomial.eval (Sum.elim i (blockLift443 i)) (blockConstraint443 s) = 0 := by
  simp only [blockConstraint443, map_sub, map_mul, MvPolynomial.eval_X, Sum.elim_inr, Sum.elim_inl]
  rw [blockMonomialEval443 i (blockLift443 i) _ (fun _ => rfl)]
  rw [Finset.prod_erase_mul _ _ (blockLastMem443 s)]
  exact sub_self _

private lemma blockLiftUnique443 (i : A → ZMod 2) (u : BlockAux443 A → ZMod 2)
    (h : ∀ s, MvPolynomial.eval (Sum.elim i u) (blockConstraint443 s) = 0) :
    u = blockLift443 i := by
  have step (n : ℕ) : ∀ s : BlockAux443 A, s.val.card = n → u s = blockLift443 i s := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro s hn
      have hp : (s.val.erase (blockLast443 s)).card < n :=
        hn ▸ Finset.card_erase_lt_of_mem (blockLastMem443 s)
      have hm := blockMonomialEval443 i u (s.val.erase (blockLast443 s))
        (fun hs => ih _ hp ⟨_, hs⟩ rfl)
      have hs := h s
      simp only [blockConstraint443, map_sub, map_mul, MvPolynomial.eval_X, Sum.elim_inr,
        Sum.elim_inl] at hs
      rw [hm, Finset.prod_erase_mul _ _ (blockLastMem443 s)] at hs
      exact sub_eq_zero.mp hs
  funext s
  exact step _ s rfl

variable [Fintype A]

-- Expand the product of the affine bit tests, replacing each monomial by its
-- corresponding single coordinate.
private noncomputable def blockMark443 (i : A → ZMod 2) :
    MvPolynomial (A ⊕ BlockAux443 A) (ZMod 2) :=
  ∑ s ∈ (Finset.univ : Finset A).powerset,
    blockMonomial443 s * MvPolynomial.C (∏ a ∈ Finset.univ \ s, (1 - i a))

private lemma blockMarkDegree443 (i : A → ZMod 2) : (blockMark443 i).totalDegree ≤ 1 := by
  unfold blockMark443
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simpa only [MvPolynomial.totalDegree_C, Nat.add_zero] using blockMonomialDegree443 s

private lemma blockMarkEval443 (i j : A → ZMod 2) :
    MvPolynomial.eval (Sum.elim j (blockLift443 j)) (blockMark443 i) =
      if i = j then 1 else 0 := by
  classical
  simp only [blockMark443, map_sum, map_mul, MvPolynomial.eval_C,
    blockMonomialEval443 j (blockLift443 j) _ (fun _ => rfl)]
  rw [← Finset.prod_add]
  have hbit (x y : ZMod 2) : y + (1 - x) = if x = y then 1 else 0 := by
    fin_cases x <;> fin_cases y <;> decide
  simp only [hbit]
  split_ifs with h
  · subst j
    simp
  · obtain ⟨a, ha⟩ : ∃ a, i a ≠ j a := by
      by_contra! he
      exact h (funext he)
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [ha])

end Block

private lemma blockAuxCard443 (A : Type*) [Fintype A] [LinearOrder A] :
    Fintype.card (BlockAux443 A) = 2 ^ Fintype.card A - (1 + Fintype.card A) := by
  let u : Finset A := Finset.univ
  have he : ((Finset.univ : Finset (Finset A)).filter fun s => ¬ 2 ≤ s.card) =
      u.powersetCard 0 ∪ u.powersetCard 1 := by
    ext s
    simp only [u, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_powersetCard, Finset.subset_univ]
    omega
  have hd : Disjoint (u.powersetCard 0) (u.powersetCard 1) := by
    refine Finset.disjoint_left.mpr ?_
    intro s h0 h1
    have h0' := (Finset.mem_powersetCard.mp h0).2
    have h1' := (Finset.mem_powersetCard.mp h1).2
    omega
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Finset A))) (fun s => 2 ≤ s.card)
  rw [he, Finset.card_union_of_disjoint hd, Finset.card_powersetCard,
    Finset.card_powersetCard] at hsplit
  rw [Fintype.card_subtype]
  simp only [u, Finset.card_univ, Fintype.card_finset, Nat.choose_zero_right,
    Nat.choose_one_right] at hsplit
  omega

open MvPolynomial
open scoped BigOperators

private abbrev K443 := ZMod 2
private abbrev Poly443 (A B : Type) := MvPolynomial (A ⊕ B) K443


private lemma assemble443 (d r k : ℕ) (A B : Fin d → Type)
    [∀ t, Fintype (B t)]
    (ea : (Σ t, A t) ≃ Fin r) (eb : (Σ t, B t) ≃ Fin k)
    (c : ∀ t, B t → Poly443 (A t) (B t))
    (m : ∀ t, (A t → K443) → Poly443 (A t) (B t))
    (lift : ∀ t, (A t → K443) → B t → K443)
    (hc : ∀ t b, (c t b).totalDegree ≤ 2)
    (hm : ∀ t x, (m t x).totalDegree ≤ 1)
    (hc0 : ∀ t x b, eval (Sum.elim x (lift t x)) (c t b) = 0)
    (hcU : ∀ t x u, (∀ b, eval (Sum.elim x u) (c t b) = 0) → u = lift t x)
    (hmE : ∀ t x y, eval (Sum.elim y (lift t y)) (m t x) =
      (by classical exact if x = y then 1 else 0)) :
    ∃ (C : Finset (Poly443 (Fin r) (Fin k))) (mark : (Fin r → K443) → Poly443 (Fin r) (Fin k))
      (w : (Fin r → K443) → Fin k → K443),
      C.card ≤ k ∧ (∀ p ∈ C, p.totalDegree ≤ 2) ∧
      (∀ i, (mark i).totalDegree ≤ d) ∧
      (∀ i, ∀ p ∈ C, eval (Sum.elim i (w i)) p = 0) ∧
      (∀ i j, eval (Sum.elim j (w j)) (mark i) = if i = j then 1 else 0) ∧
      ∀ i u, eval (Sum.elim i u) (mark i) = 1 ∨ ∃ p ∈ C, eval (Sum.elim i u) p = 1 := by
  classical
  let x (i : Fin r → K443) (t : Fin d) (a : A t) := i (ea ⟨t,a⟩)
  let y (u : Fin k → K443) (t : Fin d) (b : B t) := u (eb ⟨t,b⟩)
  let w (i : Fin r → K443) (j : Fin k) := lift (eb.symm j).1 (x i (eb.symm j).1) (eb.symm j).2
  have hw (i : Fin r → K443) (t : Fin d) : y (w i) t = lift t (x i t) := by
    funext b
    dsimp only [y, w]
    rw [eb.symm_apply_apply]
  let f (t : Fin d) : A t ⊕ B t → Fin r ⊕ Fin k :=
    Sum.elim (fun a => Sum.inl (ea ⟨t,a⟩)) (fun b => Sum.inr (eb ⟨t,b⟩))
  have he (i : Fin r → K443) (u : Fin k → K443) (t : Fin d) (p : Poly443 (A t) (B t)) :
      eval (Sum.elim i u) (rename (f t) p) = eval (Sum.elim (x i t) (y u t)) p := by
    rw [eval_rename]
    have h : Sum.elim i u ∘ f t = Sum.elim (x i t) (y u t) := by
      funext a
      cases a <;> rfl
    rw [h]
  let ct (s : Σ t, B t) := rename (f s.1) (c s.1 s.2)
  let C := Finset.univ.image ct
  let mark (i : Fin r → K443) := ∏ t : Fin d, rename (f t) (m t (x i t))
  refine ⟨C, mark, w, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      C.card ≤ (Finset.univ : Finset (Σ t, B t)).card := Finset.card_image_le
      _ = k := by rw [Finset.card_univ, Fintype.card_congr eb, Fintype.card_fin]
  · intro p hp
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hp
    exact (totalDegree_rename_le _ _).trans (hc s.1 s.2)
  · intro i
    calc
      (mark i).totalDegree ≤ ∑ t : Fin d, (rename (f t) (m t (x i t))).totalDegree :=
        by
          unfold mark
          generalize (Finset.univ : Finset (Fin d)) = S
          induction S using Finset.induction_on with
          | empty => simp
          | @insert a S ha ih =>
            rw [Finset.prod_insert ha, Finset.sum_insert ha]
            exact (totalDegree_mul _ _).trans (Nat.add_le_add_left ih _)
      _ ≤ ∑ _t : Fin d, 1 := Finset.sum_le_sum fun t _ => (totalDegree_rename_le _ _).trans (hm t _)
      _ = d := by simp
  · intro i p hp
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hp
    rw [show ct s = rename (f s.1) (c s.1 s.2) from rfl, he, hw]
    exact hc0 _ _ _
  · intro i j
    change eval (Sum.elim j (w j)) (∏ t : Fin d, rename (f t) (m t (x i t))) = _
    simp only [map_prod, he, hw, hmE]
    by_cases hij : i = j
    · subst j
      simp
    · rw [ite_eq_right hij]
      have h : ∃ t, x i t ≠ x j t := by
        by_contra! hn
        apply hij
        funext a
        obtain ⟨⟨t, b⟩, rfl⟩ := ea.surjective a
        exact congrFun (hn t) b
      obtain ⟨t, ht⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ t) (ite_eq_right ht)
  · intro i u
    by_cases hu : ∃ p ∈ C, eval (Sum.elim i u) p = 1
    · exact Or.inr hu
    · left
      have h0 (t : Fin d) (b : B t) : eval (Sum.elim (x i t) (y u t)) (c t b) = 0 := by
        have hn : eval (Sum.elim i u) (ct ⟨t,b⟩) ≠ 1 := fun h =>
          hu ⟨_, Finset.mem_image.mpr ⟨⟨t,b⟩, Finset.mem_univ _, rfl⟩, h⟩
        change eval (Sum.elim i u) (rename (f t) (c t b)) ≠ 1 at hn
        rw [he] at hn
        generalize eval (Sum.elim (x i t) (y u t)) (c t b) = z at *
        fin_cases z
        · rfl
        · exact False.elim (hn rfl)
      have hU (t : Fin d) := hcU t (x i t) (y u t) (h0 t)
      change eval (Sum.elim i u) (∏ t : Fin d, rename (f t) (m t (x i t))) = _
      simp only [map_prod, he, hU, hmE, ite_eq_left, Finset.prod_const_one]

private def size443 (r d : ℕ) (t : Fin d) := if t.val < r % d then r / d + 1 else r / d

private lemma sumBlock443 (d b : ℕ) (hb : b ≤ d) (a c : ℕ) :
    (∑ t : Fin d, if t.val < b then a else c) = b*a + (d-b)*c := by
  classical
  have hcard : (Finset.univ.filter (fun t : Fin d => t.val < b)).card = b := by
    let f : Fin b ↪ Fin d := ⟨fun t => ⟨t.val, t.isLt.trans_le hb⟩,
      fun _ _ h => Fin.ext (congrArg (fun z : Fin d => z.val) h)⟩
    have he : Finset.univ.filter (fun t : Fin d => t.val < b) = Finset.univ.map f := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro ht
        exact ⟨⟨t.val, ht⟩, Fin.ext rfl⟩
      · intro ⟨s, hs⟩
        rw [← hs]
        exact s.isLt
    simp [he]
  have hn := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin d))) (fun t => t.val < b)
  simp only [Finset.card_univ, Fintype.card_fin, hcard] at hn
  simp only [Finset.sum_ite, Finset.sum_const, smul_eq_mul, hcard]
  rw [show (Finset.univ.filter fun t : Fin d => ¬ t.val < b).card = d - b by omega]

private lemma sumSize443 (r d : ℕ) (hd : 0 < d) : (∑ t : Fin d, size443 r d t) = r := by
  have hb := (Nat.mod_lt r hd).le
  unfold size443
  rw [sumBlock443 d _ hb, Nat.mul_add, Nat.mul_one]
  calc
    r % d * (r / d) + r % d + (d - r % d) * (r / d) =
        (r % d + (d - r % d)) * (r / d) + r % d := by rw [Nat.add_mul]; omega
    _ = r := by rw [Nat.add_sub_of_le hb]; exact Nat.div_add_mod r d

private lemma sumLarge443 (r d : ℕ) (hd : 0 < d)
    (hcard : ∀ n, Fintype.card {s : Finset (Fin n) // 2 ≤ s.card} = 2^n - (1+n)) :
    let extra := fun t : ℕ => 2^t - (1+t)
    (∑ t : Fin d, Fintype.card {s : Finset (Fin (size443 r d t)) // 2 ≤ s.card}) =
      (d-r%d)*extra (r/d) + (r%d)*extra (r/d+1) := by
  dsimp
  simp only [hcard]
  calc
    _ = ∑ t : Fin d, if t.val < r%d then 2^(r/d+1) - (1+(r/d+1))
        else 2^(r/d) - (1+(r/d)) := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases h : t.val < r%d <;> simp [size443, h]
    _ = _ := by rw [sumBlock443 d _ (Nat.mod_lt r hd).le, Nat.add_comm]


private theorem upper443 : ∀ r D : ℕ, 2 ≤ D →
  let K := ZMod 2
  let q := r / D
  let b := r % D
  let extra := fun t : ℕ => 2^t - (1+t)
  let k := (D-b)*extra q + b*extra (q+1)
  let I := Fin r → K
  let U := Fin k → K
  let P := MvPolynomial (Fin r ⊕ Fin k) K
  let val := fun (p : P) (i : I) (u : U) => MvPolynomial.eval (Sum.elim i u) p
  ∃ (C : Finset P) (mark : I → P) (w : I → U),
    C.card ≤ k ∧ (∀ c ∈ C, c.totalDegree ≤ 2) ∧
    (∀ i, (mark i).totalDegree ≤ D) ∧
    (∀ i, ∀ c ∈ C, val c i (w i) = 0) ∧
    (∀ i j, val (mark i) j (w j) = if i = j then 1 else 0) ∧
    ∀ i u, val (mark i) i u = 1 ∨ ∃ c ∈ C, val c i u = 1 := by
  classical
  intro r D hd
  dsimp
  let A (t : Fin D) := Fin (size443 r D t)
  let B (t : Fin D) := BlockAux443 (A t)
  let extra (n : ℕ) := 2^n - (1+n)
  let k := (D-r%D)*extra (r/D) + (r%D)*extra (r/D+1)
  have hA : Fintype.card (Σ t, A t) = r := by
    rw [Fintype.card_sigma]
    simpa only [A, Fintype.card_fin] using sumSize443 r D (by omega)
  have hB : Fintype.card (Σ t, B t) = k := by
    rw [Fintype.card_sigma]
    exact sumLarge443 r D (by omega) fun n => by
      simpa only [Fintype.card_fin] using blockAuxCard443 (Fin n)
  let ea : (Σ t, A t) ≃ Fin r := Fintype.equivOfCardEq (hA.trans (Fintype.card_fin r).symm)
  let eb : (Σ t, B t) ≃ Fin k := Fintype.equivOfCardEq (hB.trans (Fintype.card_fin k).symm)
  exact assemble443 D r k A B ea eb
    (fun _ => blockConstraint443) (fun _ => blockMark443) (fun _ => blockLift443)
    (fun _ => blockConstraintDegree443) (fun _ => blockMarkDegree443)
    (fun _ => blockConstraintEval443) (fun _ => blockLiftUnique443)
    (fun _ i j => by by_cases h : i = j <;> simpa [h] using blockMarkEval443 i j)

end PEqualNP.Outside.L_pcx_443

open PEqualNP.Outside.L_pcx_443

theorem PEqualNP.Outside.L_pcx_443 :
  let K := ZMod 2
  let hard := fun (r k D : ℕ) =>
    let I := Fin r → K
    let U := Fin k → K
    let P := MvPolynomial (Fin r ⊕ Fin k) K
    let val := fun (p : P) (i : I) (u : U) => MvPolynomial.eval (Sum.elim i u) p
    ∃ (F : I → Finset P) (w : I → U),
      (∀ i, ∀ p ∈ F i, p.totalDegree ≤ D) ∧
      (∀ i u, ∃ p ∈ F i, val p i u = 1) ∧
      ∀ i j, i ≠ j → ∀ p ∈ F i, val p j (w j) = 0
  (∀ r k, hard r k 1 ↔ r ≤ 1) ∧
  (∀ r k D, hard r k D → 2^r ≤ ∑ j ∈ Finset.range (D+1), (r+k).choose j) ∧
  ∀ r D : ℕ, 2 ≤ D →
    let q := r / D
    let b := r % D
    let extra := fun t : ℕ => 2^t - (1+t)
    let k := (D-b)*extra q + b*extra (q+1)
    let I := Fin r → K
    let U := Fin k → K
    let P := MvPolynomial (Fin r ⊕ Fin k) K
    let val := fun (p : P) (i : I) (u : U) => MvPolynomial.eval (Sum.elim i u) p
    ∃ (C : Finset P) (mark : I → P) (w : I → U),
      C.card ≤ k ∧ (∀ c ∈ C, c.totalDegree ≤ 2) ∧
      (∀ i, (mark i).totalDegree ≤ D) ∧
      (∀ i, ∀ c ∈ C, val c i (w i) = 0) ∧
      (∀ i j, val (mark i) j (w j) = if i = j then 1 else 0) ∧
      ∀ i u, val (mark i) i u = 1 ∨ ∃ c ∈ C, val c i u = 1 := by
  dsimp only
  exact ⟨affine443, dim443, upper443⟩
