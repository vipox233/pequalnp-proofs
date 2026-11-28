import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1180

section Proof1180

variable {n t d k : ℕ}

private def extWord (v₀ : Fin n) (x' : {u : Fin n // u ≠ v₀} → Fin (d + 2)) (a : Fin (d + 2)) :
    Fin n → Fin (d + 2) :=
  fun u => if h : u = v₀ then a else x' ⟨u, h⟩

private lemma extWord_self (v₀ : Fin n) (x' : {u : Fin n // u ≠ v₀} → Fin (d + 2)) (a : Fin (d + 2)) :
    extWord v₀ x' a v₀ = a := by
  simp [extWord]

private lemma extWord_ne (v₀ : Fin n) (x' : {u : Fin n // u ≠ v₀} → Fin (d + 2)) (a : Fin (d + 2))
    {u : Fin n} (hu : u ≠ v₀) :
    extWord v₀ x' a u = x' ⟨u, hu⟩ := by
  simp [extWord, hu]

private def wordSplitEquiv (v₀ : Fin n) :
    (Fin n → Fin (d + 2)) ≃ ({u : Fin n // u ≠ v₀} → Fin (d + 2)) × Fin (d + 2) where
  toFun x := (fun u => x u.1, x v₀)
  invFun p := extWord v₀ p.1 p.2
  left_inv x := funext fun u => by
    by_cases h : u = v₀
    · subst h; simp [extWord]
    · simp [extWord, h]
  right_inv p := by
    rcases p with ⟨x', a⟩
    apply Prod.ext
    · funext ⟨u, hu⟩; simp [extWord, hu]
    · simp [extWord]

private def uncovered (scope : Fin t → Finset (Fin n)) (f : Fin k → Fin t → Fin n → Fin (d + 2)) :
    Finset (Fin n → Fin (d + 2)) :=
  Finset.univ.filter (fun x => ∀ i : Fin k, ∃ j : Fin t, ∀ v ∈ scope j, x v = f i j v)

private def shiftCoord (color : Fin k → Fin (d + 2)) (v₀ : Fin n)
    (f : Fin k → Fin t → Fin n → Fin (d + 2)) : Fin k → Fin t → Fin n → Fin (d + 2) :=
  fun i j v => if v = v₀ then color i else f i j v

private lemma uncovered_shiftCoord_le (scope : Fin t → Finset (Fin n))
    (color : Fin k → Fin (d + 2)) (hcolor : Function.Injective color) (v₀ : Fin n)
    (f : Fin k → Fin t → Fin n → Fin (d + 2)) :
    (uncovered scope (shiftCoord color v₀ f)).card ≤ (uncovered scope f).card := by
  classical
  let g := shiftCoord color v₀ f
  have hcard_sum : ∀ (h : Fin k → Fin t → Fin n → Fin (d + 2)),
      (uncovered scope h).card =
        ∑ x' : {u : Fin n // u ≠ v₀} → Fin (d + 2),
          (Finset.univ.filter (fun a : Fin (d + 2) => extWord v₀ x' a ∈ uncovered scope h)).card := by
    intro h
    let e := wordSplitEquiv (d := d) v₀
    have hbij : (uncovered scope h).card =
        (Finset.univ.filter (fun p : ({u : Fin n // u ≠ v₀} → Fin (d + 2)) × Fin (d + 2) =>
          extWord v₀ p.1 p.2 ∈ uncovered scope h)).card := by
      refine Finset.card_bij (fun x _ => e x) (fun x hx => ?_) (fun x₁ _ x₂ _ h12 => e.injective h12) (fun p hp => ?_)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have heq : extWord v₀ (e x).1 (e x).2 = x := e.left_inv x
        rwa [heq]
      · refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
        exact (Finset.mem_filter.mp hp).2
    rw [hbij]
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun p _ => ⟨p.1, p.2⟩)
      (fun p hp => by
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hp ⊢
        exact hp)
      (fun p₁ _ p₂ _ h12 => by
        cases p₁; cases p₂; simp at h12; exact Prod.ext h12.1 h12.2)
      (fun s hs => by
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hs
        exact ⟨(s.1, s.2), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩, rfl⟩)
  rw [hcard_sum g, hcard_sum f]
  refine Finset.sum_le_sum fun x' _ => ?_
  set As := Finset.univ.filter (fun a : Fin (d + 2) => extWord v₀ x' a ∈ uncovered scope g)
  set Af := Finset.univ.filter (fun a : Fin (d + 2) => extWord v₀ x' a ∈ uncovered scope f)
  have hmem_As : ∀ a : Fin (d + 2), a ∈ As ↔ ∀ i : Fin k, ∃ j : Fin t, ∀ v ∈ scope j, extWord v₀ x' a v = g i j v := by
    intro a; simp [As, uncovered]
  have hmem_Af : ∀ a : Fin (d + 2), a ∈ Af ↔ ∀ i : Fin k, ∃ j : Fin t, ∀ v ∈ scope j, extWord v₀ x' a v = f i j v := by
    intro a; simp [Af, uncovered]
  by_cases h0 : As.card = 0
  · omega
  · by_cases h1 : As.card = 1
    · obtain ⟨a₀, ha₀⟩ := Finset.card_pos.mp (by omega : 0 < As.card)
      have ha₀_spec := (hmem_As a₀).mp ha₀
      have hex_j : ∃ jj : Fin k → Fin t, ∀ i : Fin k, ∀ v ∈ scope (jj i), extWord v₀ x' a₀ v = g i (jj i) v :=
        ⟨fun i => (ha₀_spec i).choose, fun i => (ha₀_spec i).choose_spec⟩
      obtain ⟨jj, hjj⟩ := hex_j
      have huniq : ∀ i₁ i₂ : Fin k, v₀ ∈ scope (jj i₁) → v₀ ∈ scope (jj i₂) → i₁ = i₂ := by
        intro i₁ i₂ h1' h2'
        have e1 := hjj i₁ v₀ h1'
        have e2 := hjj i₂ v₀ h2'
        simp only [extWord_self, g, shiftCoord, ↓reduceIte] at e1 e2
        exact hcolor (e1.symm.trans e2)
      have hAf_nonempty : Af.Nonempty := by
        by_cases hhit : ∃ i₀ : Fin k, v₀ ∈ scope (jj i₀)
        · obtain ⟨i₀, hi₀⟩ := hhit
          refine ⟨f i₀ (jj i₀) v₀, (hmem_Af _).mpr fun i => ?_⟩
          refine ⟨jj i, fun v hv => ?_⟩
          by_cases hv0 : v = v₀
          · subst hv0
            have hieq : i = i₀ := huniq i i₀ hv hi₀
            subst hieq; simp [extWord_self]
          · have hmatch := hjj i v hv
            simp only [extWord_ne _ _ _ hv0, g, shiftCoord, if_neg hv0] at hmatch ⊢
            exact hmatch
        · push_neg at hhit
          refine ⟨a₀, (hmem_Af _).mpr fun i => ⟨jj i, fun v hv => ?_⟩⟩
          have hv0 : v ≠ v₀ := fun h => hhit i (h ▸ hv)
          have hmatch := hjj i v hv
          simp only [g, shiftCoord, if_neg hv0] at hmatch
          exact hmatch
      have hpos : 1 ≤ Af.card := Finset.card_pos.mpr hAf_nonempty
      omega
    · have hge2 : 1 < As.card := by omega
      obtain ⟨a₁, ha₁, a₂, ha₂, hne⟩ := Finset.one_lt_card.mp hge2
      have hAf_univ : Af = Finset.univ := by
        ext a; simp only [Finset.mem_univ, iff_true]
        rw [hmem_Af]
        intro i
        obtain ⟨j₁, hj₁⟩ := (hmem_As a₁).mp ha₁ i
        obtain ⟨j₂, hj₂⟩ := (hmem_As a₂).mp ha₂ i
        by_cases hv1 : v₀ ∈ scope j₁
        · have hv2 : v₀ ∉ scope j₂ := by
            intro hv2'
            have e1 := hj₁ v₀ hv1
            have e2 := hj₂ v₀ hv2'
            simp only [extWord_self, g, shiftCoord, ↓reduceIte] at e1 e2
            exact hne (e1.trans e2.symm)
          refine ⟨j₂, fun v hv => ?_⟩
          have hvn : v ≠ v₀ := fun h => hv2 (h ▸ hv)
          have hmatch := hj₂ v hv
          simp only [extWord_ne _ _ _ hvn, g, shiftCoord, if_neg hvn] at hmatch ⊢
          exact hmatch
        · refine ⟨j₁, fun v hv => ?_⟩
          have hvn : v ≠ v₀ := fun h => hv1 (h ▸ hv)
          have hmatch := hj₁ v hv
          simp only [extWord_ne _ _ _ hvn, g, shiftCoord, if_neg hvn] at hmatch ⊢
          exact hmatch
      rw [hAf_univ]
      exact Finset.card_le_univ As

private lemma uncovered_constant_le (scope : Fin t → Finset (Fin n))
    (color : Fin k → Fin (d + 2)) (hcolor : Function.Injective color)
    (f : Fin k → Fin t → Fin n → Fin (d + 2)) :
    (uncovered scope (fun i _ _ => color i)).card ≤ (uncovered scope f).card := by
  let step (m : ℕ) : Fin k → Fin t → Fin n → Fin (d + 2) :=
    fun i j v => if v.val < m then color i else f i j v
  have hmono : ∀ m ≤ n, (uncovered scope (step m)).card ≤ (uncovered scope f).card := by
    intro m hm
    induction m with
    | zero =>
      have h0 : step 0 = f := by funext i j v; simp [step]
      rw [h0]
    | succ m ih =>
      let v₀ : Fin n := ⟨m, by omega⟩
      have hnext : step (m + 1) = shiftCoord color v₀ (step m) := by
        funext i j v
        dsimp only [step, shiftCoord, v₀]
        by_cases hv : v = ⟨m, by omega⟩
        · subst hv; simp
        · have hne : v.val ≠ m := fun h => hv (Fin.ext h)
          rw [if_neg hv]
          by_cases hlt : v.val < m
          · rw [if_pos (by omega), if_pos hlt]
          · rw [if_neg (by omega), if_neg hlt]
      rw [hnext]
      exact (uncovered_shiftCoord_le scope color hcolor v₀ (step m)).trans (ih (by omega))
  have hn : step n = fun i _ _ => color i := by
    funext i j v; simp [step, v.isLt]
  rw [← hn]
  exact hmono n le_rfl

end Proof1180

end PEqualNP.Outside.L_lib_1180

open PEqualNP.Outside.L_lib_1180 in
theorem PEqualNP.Outside.L_lib_1180 :
∀ (n t d : Nat) (scope : Fin t → Finset (Fin n)),
  let Word := Fin n → Fin (d + 2)
  let Signing := Fin t → Word
  let labels := (Finset.univ : Finset (Fin t))
  let cube := (Finset.univ : Finset Word)
  let pass := fun (s : Signing) (x : Word) => labels.toList.all (fun j =>
    (scope j).toList.any (fun v => x v != s j v))
  let covered := fun {k : Nat} (f : Fin k → Signing) =>
    cube.filter (fun x => (List.finRange k).any (fun i => pass (f i) x))
  ∀ (k : Nat) (color : Fin k → Fin (d + 2)), Function.Injective color →
    let constant : Fin k → Signing := fun i _ _ => color i
    (∀ f : Fin k → Signing, (covered f).card ≤ (covered constant).card) ∧
    (covered constant = cube ↔ ¬ ∃ edge : Fin k → Fin t,
      ∀ i j : Fin k, i ≠ j → scope (edge i) ∩ scope (edge j) = ∅) := by
  classical
  intro n t d scope Word Signing labels cube pass covered k color hcolor constant
  have hpass_iff : ∀ (s : Signing) (x : Word),
      pass s x = true ↔ ∀ j : Fin t, ∃ v ∈ scope j, x v ≠ s j v := by
    intro s x
    simp only [pass, List.all_eq_true, List.any_eq_true, Finset.mem_toList, labels, Finset.mem_univ,
      true_implies, bne_iff_ne]
  have hcov_iff : ∀ (f : Fin k → Signing) (x : Word),
      x ∈ covered f ↔ ¬(∀ i : Fin k, ∃ j : Fin t, ∀ v ∈ scope j, x v = f i j v) := by
    intro f x
    simp only [covered, Finset.mem_filter, cube, Finset.mem_univ, true_and, List.any_eq_true,
      List.mem_finRange, hpass_iff]
    push_neg
    rfl
  have hcompl : ∀ (f : Fin k → Signing),
      (covered f).card + (uncovered scope f).card = cube.card := by
    intro f
    have hdisj : Disjoint (covered f) (uncovered scope f) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [hcov_iff] at hx1
      exact hx1 (Finset.mem_filter.mp hx2).2
    have hunion : covered f ∪ uncovered scope f = cube := by
      ext x; simp only [Finset.mem_union, hcov_iff, uncovered, Finset.mem_filter, cube, Finset.mem_univ, true_and]
      exact iff_true_intro (Or.symm (em _))
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  constructor
  · intro f
    have h1 := hcompl f
    have h2 := hcompl constant
    have hle := uncovered_constant_le scope color hcolor f
    change (uncovered scope constant).card ≤ (uncovered scope f).card at hle
    omega
  · constructor
    · intro hcov ⟨edge, hdisj⟩
      -- Construct word x with x v = color i for v ∈ scope (edge i)
      let x : Word := fun v =>
        if h : ∃ i : Fin k, v ∈ scope (edge i) then color h.choose else 0
      have hx_in : x ∈ covered constant := by rw [hcov]; exact Finset.mem_univ x
      rw [hcov_iff] at hx_in
      refine hx_in fun i => ⟨edge i, fun v hv => ?_⟩
      have hex : ∃ i' : Fin k, v ∈ scope (edge i') := ⟨i, hv⟩
      have hch : hex.choose = i := by
        by_contra hne
        have hinter : v ∈ scope (edge hex.choose) ∩ scope (edge i) :=
          Finset.mem_inter.mpr ⟨hex.choose_spec, hv⟩
        rw [hdisj hex.choose i hne] at hinter
        exact Finset.notMem_empty v hinter
      simp only [x, dif_pos hex, hch, constant]
    · intro hno
      ext x
      simp only [cube, Finset.mem_univ, iff_true]
      rw [hcov_iff]
      intro hall
      refine hno ⟨fun i => (hall i).choose, fun i j hne => ?_⟩
      rw [Finset.eq_empty_iff_forall_notMem]
      intro v hv
      rcases Finset.mem_inter.mp hv with ⟨hvi, hvj⟩
      have ei := (hall i).choose_spec v hvi
      have ej := (hall j).choose_spec v hvj
      dsimp only [constant] at ei ej
      exact hne (hcolor (ei.symm.trans ej))
