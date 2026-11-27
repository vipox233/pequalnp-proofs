import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_451 : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
  let bag : Fin n → Set (Fin n ⊕ (Fin n × Fin n)) := fun v =>
    {z | z = Sum.inl v ∨ ∃ a b : Fin n,
      z = Sum.inr (a, b) ∧ G.Adj a b ∧ (v = a ∨ v = b)}
  (∃ S : Finset (Fin n), k ≤ S.card ∧
    ∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b) ↔
  ∃ T : Finset (Set (Fin n ⊕ (Fin n × Fin n))), k ≤ T.card ∧
    (∀ B ∈ T, ∃ v, B = bag v) ∧ ∀ B ∈ T, ∀ C ∈ T, B ≠ C → Disjoint B C := by
  classical
  intro n k G bag

  have mem_inl : ∀ v w, Sum.inl w ∈ bag v ↔ w = v := by simp [bag]
  have mem_inr : ∀ v x y, Sum.inr (x, y) ∈ bag v ↔ G.Adj x y ∧ (v = x ∨ v = y) := by
    simp [bag]

  have inj : Function.Injective bag := fun v w h =>
    (mem_inl w v).1 (h ▸ (mem_inl v v).2 rfl)

  have disj : ∀ a b, a ≠ b → (Disjoint (bag a) (bag b) ↔ ¬ G.Adj a b) := by
    intro a b hne
    refine ⟨fun h hab => Set.disjoint_left.1 h ((mem_inr a a b).2 ⟨hab, Or.inl rfl⟩)
      ((mem_inr b a b).2 ⟨hab, Or.inr rfl⟩), fun hab => ?_⟩
    rw [Set.disjoint_left]
    rintro (w | ⟨x, y⟩) ha hb
    · exact hne ((mem_inl a w).1 ha ▸ (mem_inl b w).1 hb)
    · rw [mem_inr] at ha hb
      rcases ha with ⟨hxy, rfl | rfl⟩ <;> rcases hb.2 with rfl | rfl
      exacts [hne rfl, hab hxy, hab hxy.symm, hne rfl]
  constructor

  · rintro ⟨S, hk, hS⟩
    refine ⟨S.image bag, by rwa [Finset.card_image_of_injective _ inj], ?_, ?_⟩
    · intro B hB
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hB
      exact ⟨v, rfl⟩
    · simp only [Finset.mem_image]
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hne
      exact (disj a b fun h => hne (h ▸ rfl)).2 (hS a ha b hb)

  · rintro ⟨T, hk, hT, hdisj⟩
    let S := Finset.univ.filter fun v => bag v ∈ T
    have hTS : T ⊆ S.image bag := fun B hB => by
      obtain ⟨v, rfl⟩ := hT B hB
      exact Finset.mem_image_of_mem bag (by simpa [S] using hB)
    refine ⟨S, hk.trans ((Finset.card_le_card hTS).trans Finset.card_image_le), ?_⟩
    intro a ha b hb hab
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    have hne := G.ne_of_adj hab
    exact (disj a b hne).1 (hdisj _ ha _ hb (inj.ne hne)) hab
