import PEqualNP.Defs

-- L-lib-450: forward, pick one true literal per clause and take its graph; first coordinates are distinct,
-- and two picks on the same variable agree since both are true under a. Backward, distinct first coordinates
-- and card m make every clause index occur; set a v to true exactly when some pick sets v to true.

namespace PEqualNP.Outside.L_lib_450_aux
end PEqualNP.Outside.L_lib_450_aux

open PEqualNP.Outside.L_lib_450_aux in
theorem PEqualNP.Outside.L_lib_450 :
    ∀ (m n : ℕ) (F : Fin m → Finset (Fin n × Bool)),
      (∃ a : Fin n → Bool, ∀ i, ∃ l ∈ F i, a l.1 = l.2) ↔
      ∃ K : Finset (Fin m × (Fin n × Bool)), K.card = m ∧
        (∀ p ∈ K, p.2 ∈ F p.1) ∧
        ∀ p ∈ K, ∀ q ∈ K, p ≠ q →
          p.1 ≠ q.1 ∧ (p.2.1 = q.2.1 → p.2.2 = q.2.2)
      := by
  intro m n F
  constructor
  · rintro ⟨a, ha⟩
    choose f hfF hfa using ha
    refine ⟨Finset.univ.image (fun i => (i, f i)), ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (fun i j h => congrArg Prod.fst h)]
      simp
    · intro p hp
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
      obtain ⟨i, rfl⟩ := hp
      exact hfF i
    · intro p hp q hq hpq
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp hq
      obtain ⟨i, rfl⟩ := hp
      obtain ⟨j, rfl⟩ := hq
      refine ⟨fun hij => hpq (by subst hij; rfl), fun h => ?_⟩
      dsimp only at h ⊢
      rw [← hfa i, ← hfa j, h]
  · rintro ⟨K, hcard, hKF, hK⟩
    have hinj : Set.InjOn Prod.fst (K : Set (Fin m × (Fin n × Bool))) := by
      intro p hp q hq h
      by_contra hne
      exact (hK p hp q hq hne).1 h
    have himg : K.image Prod.fst = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [Finset.card_image_of_injOn hinj, hcard, Fintype.card_fin])
    refine ⟨fun v => decide (∃ p ∈ K, p.2.1 = v ∧ p.2.2 = true), fun i => ?_⟩
    have hi : i ∈ K.image Prod.fst := himg ▸ Finset.mem_univ i
    obtain ⟨p, hpK, rfl⟩ := Finset.mem_image.mp hi
    refine ⟨p.2, hKF p hpK, ?_⟩
    dsimp only
    cases hb : p.2.2
    · rw [decide_eq_false_iff_not]
      rintro ⟨q, hqK, hq1, hq2⟩
      have hne : p ≠ q := by
        intro h
        rw [h] at hb
        rw [hb] at hq2
        exact Bool.false_ne_true hq2
      have h2 := (hK p hpK q hqK hne).2 hq1.symm
      rw [hb, hq2] at h2
      exact Bool.false_ne_true h2
    · rw [decide_eq_true_iff]
      exact ⟨p, hpK, rfl, hb⟩
