import Mathlib

namespace PEqualNP.Outside.L_lib_554_aux

theorem inter_det {k p : ℕ} (g : (Fin k → Bool) → Bool) (V : Fin p → Finset (Fin k)) :
    ∀ T : Finset (Fin p), (∀ o ∈ T, ∀ x y : Fin k → Bool, (∀ j ∈ V o, x j = y j) → g x = g y) →
    ∀ x y : Fin k → Bool,
      (∀ j ∈ Finset.univ.filter (fun j : Fin k => ∀ o ∈ T, j ∈ V o), x j = y j) → g x = g y := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _ x y hxy
    have : x = y := funext fun j => hxy j (by simp)
    rw [this]
  | insert a T ha ih =>
    intro h x y hxy
    let z : Fin k → Bool := fun j => if j ∈ V a then x j else y j
    have e1 : g x = g z := by
      apply h a (Finset.mem_insert_self _ _)
      intro j hj
      simp [z, hj]
    have e2 : g z = g y := by
      apply ih (fun o ho => h o (Finset.mem_insert_of_mem ho))
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      by_cases hja : j ∈ V a
      · simp only [z, hja, ite_true]
        apply hxy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, forall_eq_or_imp]
        exact ⟨hja, hj⟩
      · simp [z, hja]
    rw [e1, e2]

theorem hall_bound {m k : ℕ} (D : (Fin k → Bool) → Fin m → Bool) (hD : Function.Surjective D)
    (C : Fin m → Finset (Fin k)) (hC : ∀ i x y, (∀ j ∈ C i, x j = y j) → D x i = D y i)
    (S : Finset (Fin m)) : S.card ≤ (S.biUnion C).card := by
  classical
  set U := S.biUnion C with hU
  let g : (U → Bool) → (S → Bool) := fun u i =>
    D (fun j => if h : j ∈ U then u ⟨j, h⟩ else false) i.val
  have hg : Function.Surjective g := by
    intro t
    obtain ⟨x, hx⟩ := hD (fun i => if h : i ∈ S then t ⟨i, h⟩ else false)
    refine ⟨fun j => x j.val, ?_⟩
    funext i
    have : D (fun j => if h : j ∈ U then x j else false) i.val = D x i.val := by
      apply hC
      intro j hj
      have hjU : j ∈ U := Finset.mem_biUnion.2 ⟨i.val, i.property, hj⟩
      simp [hjU]
    show D (fun j => if h : j ∈ U then x j else false) i.val = t i
    rw [this, hx]
    simp
  have := Fintype.card_le_of_surjective g hg
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at this
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

end PEqualNP.Outside.L_lib_554_aux

theorem PEqualNP.Outside.L_lib_554 : ∀ (m k p : ℕ) (need : Fin m → Finset (Fin p)) (view : Fin p → Finset (Fin k)),
  let common := fun i : Fin m => Finset.univ.filter
    (fun j : Fin k => ∀ o ∈ need i, j ∈ view o)
  let same := fun (S : Finset (Fin k)) (x y : Fin k → Bool) => ∀ j ∈ S, x j = y j
  let decodable := fun D : (Fin k → Bool) → Fin m → Bool =>
    ∀ (i : Fin m) (o : Fin p), o ∈ need i → ∀ x y, same (view o) x y → D x i = D y i
  (∀ D : (Fin k → Bool) → Fin m → Bool, Function.Surjective D → decodable D →
    (∀ (i : Fin m) (x y : Fin k → Bool), same (common i) x y → D x i = D y i) ∧
    ∀ S : Finset (Fin m), S.card ≤ (S.biUnion common).card) ∧
  ((∃ D : (Fin k → Bool) → Fin m → Bool, Function.Surjective D ∧ decodable D) ↔
    ∃ f : Fin m ↪ Fin k, ∀ i, f i ∈ common i) := by
  intro m k p need view common same decodable
  have part1 : ∀ D : (Fin k → Bool) → Fin m → Bool, Function.Surjective D → decodable D →
      (∀ (i : Fin m) (x y : Fin k → Bool), same (common i) x y → D x i = D y i) ∧
      ∀ S : Finset (Fin m), S.card ≤ (S.biUnion common).card := by
    intro D hD hdec
    have h1 : ∀ (i : Fin m) (x y : Fin k → Bool), same (common i) x y → D x i = D y i :=
      fun i => PEqualNP.Outside.L_lib_554_aux.inter_det (fun x => D x i) view (need i)
        (fun o ho x y hxy => hdec i o ho x y hxy)
    exact ⟨h1, PEqualNP.Outside.L_lib_554_aux.hall_bound D hD common h1⟩
  refine ⟨part1, ⟨?_, ?_⟩⟩
  · rintro ⟨D, hD, hdec⟩
    obtain ⟨f, hf, hfc⟩ :=
      (Finset.all_card_le_biUnion_card_iff_exists_injective common).1 (part1 D hD hdec).2
    exact ⟨⟨f, hf⟩, hfc⟩
  · rintro ⟨f, hf⟩
    classical
    refine ⟨fun x i => x (f i), ?_, ?_⟩
    · intro t
      refine ⟨fun j => decide (∃ i, f i = j ∧ t i = true), ?_⟩
      funext i
      cases ht : t i <;> simp [f.injective.eq_iff, ht]
    · intro i o ho x y hxy
      exact hxy (f i) ((Finset.mem_filter.1 (hf i)).2 o ho)
