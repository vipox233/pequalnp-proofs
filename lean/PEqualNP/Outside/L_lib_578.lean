import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_578_aux

theorem main_aux (K : Type) [Field K] (n l r : ℕ)
    (L : Fin l → Finset (Fin n)) (R : Fin r → Finset (Fin n))
    (hcov : ∀ v : Fin n, (∃ i, v ∈ L i) ∨ ∃ j, v ∈ R j) (d : ℕ) :
    let S := (Finset.univ : Finset (Fin n)).filter
      (fun v => (∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j)
    let Left := (i : Fin l) → ((↥(L i) → Bool) → Bool)
    let Right := (j : Fin r) → ((↥(R j) → Bool) → Bool)
    let count := fun (p : Left) (q : Right) =>
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
        (∀ i, p i (fun v => x v.val) = true) ∧
        (∀ j, q j (fun v => x v.val) = true))).card
    (∃ (A : Left → Fin d → K) (B : Right → Fin d → K),
      ∀ p q, (count p q : K) = ∑ j : Fin d, A p j * B q j) ↔
    2 ^ S.card ≤ d := by
  intro S Left Right count
  constructor
  · rintro ⟨A, B, hAB⟩
    let ext : (↥S → Bool) → (Fin n → Bool) := fun s v => if hv : v ∈ S then s ⟨v, hv⟩ else false
    let pOf : (↥S → Bool) → Left := fun s i loc => decide (loc = fun v => ext s v.val)
    let qOf : (↥S → Bool) → Right := fun s j loc => decide (loc = fun v => ext s v.val)
    have hcount : ∀ s₁ s₂ : ↥S → Bool, count (pOf s₁) (qOf s₂) = if s₁ = s₂ then 1 else 0 := by
      intro s₁ s₂
      by_cases hs : s₁ = s₂
      · subst hs
        rw [if_pos rfl]
        have hfilt : (Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
            (∀ i, pOf s₁ i (fun v => x v.val) = true) ∧
            (∀ j, qOf s₁ j (fun v => x v.val) = true)) = {ext s₁} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
            pOf, qOf, decide_eq_true_eq]
          constructor
          · rintro ⟨hL, hR⟩
            funext v
            rcases hcov v with ⟨i, hi⟩ | ⟨j, hj⟩
            · exact congrFun (hL i) ⟨v, hi⟩
            · exact congrFun (hR j) ⟨v, hj⟩
          · rintro rfl
            exact ⟨fun _ => rfl, fun _ => rfl⟩
        unfold count
        rw [hfilt, Finset.card_singleton]
      · rw [if_neg hs]
        have hfilt : (Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
            (∀ i, pOf s₁ i (fun v => x v.val) = true) ∧
            (∀ j, qOf s₂ j (fun v => x v.val) = true)) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro x _
          rintro ⟨hL, hR⟩
          apply hs
          funext v
          have hvS : (∃ i, v.val ∈ L i) ∧ ∃ j, v.val ∈ R j := (Finset.mem_filter.1 v.2).2
          obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hvS
          have h1 : x v.val = ext s₁ v.val := congrFun (of_decide_eq_true (hL i)) ⟨v.val, hi⟩
          have h2 : x v.val = ext s₂ v.val := congrFun (of_decide_eq_true (hR j)) ⟨v.val, hj⟩
          have heq : ext s₁ v.val = ext s₂ v.val := h1.symm.trans h2
          simp only [ext, v.2, ↓reduceDIte] at heq
          exact heq
        unfold count
        rw [hfilt, Finset.card_empty]
    let M : ((Fin d → K) →ₗ[K] ((↥S → Bool) → K)) :=
      { toFun := fun u s => ∑ j : Fin d, A (pOf s) j * u j
        map_add' := fun u1 u2 => by
          ext s
          simp [mul_add, Finset.sum_add_distrib]
        map_smul' := fun c u => by
          ext s
          simp [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring }
    have hsurj : Function.Surjective M := by
      intro w
      refine ⟨fun j => ∑ s₂ : ↥S → Bool, B (qOf s₂) j * w s₂, ?_⟩
      ext s₁
      change ∑ j : Fin d, A (pOf s₁) j * ∑ s₂ : ↥S → Bool, B (qOf s₂) j * w s₂ = w s₁
      have h1 : ∀ j : Fin d,
          A (pOf s₁) j * ∑ s₂ : ↥S → Bool, B (qOf s₂) j * w s₂ =
            ∑ s₂ : ↥S → Bool, (A (pOf s₁) j * B (qOf s₂) j) * w s₂ := by
        intro j
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s₂ _ => ?_
        ring
      simp only [h1]
      rw [Finset.sum_comm]
      have h2 : ∀ s₂ : ↥S → Bool,
          (∑ j : Fin d, (A (pOf s₁) j * B (qOf s₂) j) * w s₂) =
            (if s₁ = s₂ then (1 : K) else 0) * w s₂ := by
        intro s₂
        rw [← Finset.sum_mul, ← hAB (pOf s₁) (qOf s₂), hcount s₁ s₂]
        split_ifs <;> simp
      simp only [h2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    have hrn := LinearMap.finrank_range_add_finrank_ker M
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun,
      Module.finrank_pi, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at hrn
    omega
  · intro hd
    let PL := (Finset.univ : Finset (Fin n)).filter
      (fun v => (∃ i, v ∈ L i) ∧ ¬ ∃ j, v ∈ R j)
    let PR := (Finset.univ : Finset (Fin n)).filter
      (fun v => (¬ ∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j)
    have hpart : ∀ v : Fin n, v ∉ S → v ∉ PL → v ∈ PR := by
      intro v hS hPL
      simp only [S, PL, PR, Finset.mem_filter, Finset.mem_univ, true_and] at hS hPL ⊢
      rcases hcov v with hL | hR
      · exfalso
        by_cases hR : ∃ j, v ∈ R j
        · exact hS ⟨hL, hR⟩
        · exact hPL ⟨hL, hR⟩
      · refine ⟨?_, hR⟩
        intro hL
        exact hS ⟨hL, hR⟩
    let merge : (↥S → Bool) → (↥PL → Bool) → (↥PR → Bool) → (Fin n → Bool) :=
      fun s a b v =>
        if hS : v ∈ S then s ⟨v, hS⟩
        else if hPL : v ∈ PL then a ⟨v, hPL⟩
        else b ⟨v, hpart v hS hPL⟩
    have hmergeL : ∀ (s : ↥S → Bool) (a : ↥PL → Bool) (b1 b2 : ↥PR → Bool)
        (i : Fin l) (v : ↥(L i)), merge s a b1 v.val = merge s a b2 v.val := by
      intro s a b1 b2 i v
      unfold merge
      by_cases hS : v.val ∈ S
      · simp [hS]
      · have hPL : v.val ∈ PL := by
          simp only [S, PL, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
          refine ⟨⟨i, v.2⟩, fun hR => hS ⟨⟨i, v.2⟩, hR⟩⟩
        simp [hS, hPL]
    have hmergeR : ∀ (s : ↥S → Bool) (a1 a2 : ↥PL → Bool) (b : ↥PR → Bool)
        (j : Fin r) (v : ↥(R j)), merge s a1 b v.val = merge s a2 b v.val := by
      intro s a1 a2 b j v
      unfold merge
      by_cases hS : v.val ∈ S
      · simp [hS]
      · have hnotPL : v.val ∉ PL := by
          simp only [PL, Finset.mem_filter, Finset.mem_univ, true_and]
          intro h
          exact h.2 ⟨j, v.2⟩
        simp [hS, hnotPL]
    let pOk : Left → (↥S → Bool) → (↥PL → Bool) → Prop :=
      fun p s a => ∀ i, p i (fun v => merge s a (fun _ => false) v.val) = true
    let qOk : Right → (↥S → Bool) → (↥PR → Bool) → Prop :=
      fun q s b => ∀ j, q j (fun v => merge s (fun _ => false) b v.val) = true
    let cL : Left → (↥S → Bool) → ℕ := fun p s =>
      ((Finset.univ : Finset (↥PL → Bool)).filter (fun a => pOk p s a)).card
    let cR : Right → (↥S → Bool) → ℕ := fun q s =>
      ((Finset.univ : Finset (↥PR → Bool)).filter (fun b => qOk q s b)).card
    have hcount_sum : ∀ p q, count p q = ∑ s : ↥S → Bool, cL p s * cR q s := by
      intro p q
      let T : Finset ((↥S → Bool) × (↥PL → Bool) × (↥PR → Bool)) :=
        Finset.univ.filter (fun t => pOk p t.1 t.2.1 ∧ qOk q t.1 t.2.2)
      have hbij : count p q = T.card := by
        unfold count
        refine Finset.card_nbij'
          (fun x => (fun v => x v.val, fun v => x v.val, fun v => x v.val))
          (fun t => merge t.1 t.2.1 t.2.2) ?_ ?_ ?_ ?_
        · intro x hx
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, T] at hx ⊢
          have hmx : merge (fun v => x v.val) (fun v => x v.val) (fun v => x v.val) = x := by
            funext v
            unfold merge
            split_ifs <;> rfl
          constructor
          · intro i
            have heq : (fun v : ↥(L i) => merge (fun u => x u.val) (fun u => x u.val)
                (fun _ => false) v.val) = fun v : ↥(L i) => x v.val := by
              funext v
              exact (hmergeL (fun u => x u.val) (fun u => x u.val) (fun _ => false)
                (fun u => x u.val) i v).trans (congrFun hmx v.val)
            rw [heq]
            exact hx.1 i
          · intro j
            have heq : (fun v : ↥(R j) => merge (fun u => x u.val) (fun _ => false)
                (fun u => x u.val) v.val) = fun v : ↥(R j) => x v.val := by
              funext v
              exact (hmergeR (fun u => x u.val) (fun _ => false) (fun u => x u.val)
                (fun u => x u.val) j v).trans (congrFun hmx v.val)
            rw [heq]
            exact hx.2 j
        · rintro ⟨s, a, b⟩ ht
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, T] at ht ⊢
          constructor
          · intro i
            have heq : (fun v : ↥(L i) => merge s a b v.val) =
                fun v : ↥(L i) => merge s a (fun _ => false) v.val := by
              funext v
              exact hmergeL s a b (fun _ => false) i v
            rw [heq]
            exact ht.1 i
          · intro j
            have heq : (fun v : ↥(R j) => merge s a b v.val) =
                fun v : ↥(R j) => merge s (fun _ => false) b v.val := by
              funext v
              exact hmergeR s a (fun _ => false) b j v
            rw [heq]
            exact ht.2 j
        · intro x _
          funext v
          dsimp only [merge]
          split_ifs <;> rfl
        · rintro ⟨s, a, b⟩ _
          refine Prod.ext ?_ (Prod.ext ?_ ?_)
          · funext v
            simp [merge, v.2]
          · funext v
            have hnotS : v.val ∉ S := by
              have h1 := (Finset.mem_filter.1 v.2).2
              simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
              intro h2
              exact h1.2 h2.2
            simp [merge, hnotS, v.2]
          · funext v
            have h1 := (Finset.mem_filter.1 v.2).2
            have hnotS : v.val ∉ S := by
              simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
              intro h2
              exact h1.1 h2.1
            have hnotPL : v.val ∉ PL := by
              simp only [PL, Finset.mem_filter, Finset.mem_univ, true_and]
              intro h2
              exact h1.1 h2.1
            simp [merge, hnotS, hnotPL]
      rw [hbij]
      have hT : T.card = ∑ s : ↥S → Bool,
          (((Finset.univ : Finset (↥PL → Bool)).filter (fun a => pOk p s a)) ×ˢ
           ((Finset.univ : Finset (↥PR → Bool)).filter (fun b => qOk q s b))).card := by
        have h1 : T.card = ∑ s : ↥S → Bool,
            ∑ a : ↥PL → Bool, ∑ b : ↥PR → Bool, if pOk p s a ∧ qOk q s b then 1 else 0 := by
          unfold T
          rw [Finset.card_filter, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun s _ => Fintype.sum_prod_type _
        rw [h1]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.card_product, Finset.card_filter, Finset.card_filter, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases ha : pOk p s a <;> by_cases hb : qOk q s b <;> simp [ha, hb]
      rw [hT]
      refine Finset.sum_congr rfl fun s _ => Finset.card_product _ _
    have hcardS : Fintype.card (↥S → Bool) = 2 ^ S.card := by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
    let e : (↥S → Bool) ≃ Fin (2 ^ S.card) := Fintype.equivFinOfCardEq hcardS
    let A : Left → Fin d → K := fun p j =>
      if h : j.val < 2 ^ S.card then (cL p (e.symm ⟨j.val, h⟩) : K) else 0
    let B : Right → Fin d → K := fun q j =>
      if h : j.val < 2 ^ S.card then (cR q (e.symm ⟨j.val, h⟩) : K) else 0
    refine ⟨A, B, fun p q => ?_⟩
    rw [hcount_sum p q, Nat.cast_sum]
    have hsplit : ∑ j : Fin d, A p j * B q j =
        ∑ j ∈ (Finset.univ : Finset (Fin d)).filter (fun j : Fin d => j.val < 2 ^ S.card),
          A p j * B q j := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun j _ hj => ?_
      have hnot : ¬ j.val < 2 ^ S.card := by
        intro h
        exact hj (Finset.mem_filter.2 ⟨Finset.mem_univ j, h⟩)
      simp [A, B, hnot]
    rw [hsplit]
    refine Finset.sum_nbij'
      (fun s => ⟨(e s).val, lt_of_lt_of_le (e s).isLt hd⟩)
      (fun j => if h : j.val < 2 ^ S.card then e.symm ⟨j.val, h⟩ else e.symm ⟨0, by positivity⟩)
      ?_ ?_ ?_ ?_ ?_
    · intro s _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, (e s).isLt]
    · intro j _; exact Finset.mem_univ _
    · intro s _
      simp [(e s).isLt]
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      apply Fin.ext
      simp [hj]
    · intro s _
      simp [A, B, (e s).isLt, Nat.cast_mul]

end PEqualNP.Outside.L_lib_578_aux

theorem PEqualNP.Outside.L_lib_578 : ∀ (K : Type) [Field K] (n l r : ℕ)
  (L : Fin l → Finset (Fin n)) (R : Fin r → Finset (Fin n)),
  (∀ v : Fin n, (∃ i, v ∈ L i) ∨ ∃ j, v ∈ R j) →
  let S := (Finset.univ : Finset (Fin n)).filter
    (fun v => (∃ i, v ∈ L i) ∧ ∃ j, v ∈ R j)
  let Left := (i : Fin l) → ((↥(L i) → Bool) → Bool)
  let Right := (j : Fin r) → ((↥(R j) → Bool) → Bool)
  let count := fun (p : Left) (q : Right) =>
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
      (∀ i, p i (fun v => x v.val) = true) ∧
      (∀ j, q j (fun v => x v.val) = true))).card
  ∀ d : ℕ,
    (∃ (A : Left → Fin d → K) (B : Right → Fin d → K),
      ∀ p q, (count p q : K) = ∑ j : Fin d, A p j * B q j) ↔
    2 ^ S.card ≤ d := by
  intro K _ n l r L R hcov S Left Right count d
  exact PEqualNP.Outside.L_lib_578_aux.main_aux K n l r L R hcov d
