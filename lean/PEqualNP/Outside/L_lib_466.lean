import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_466 : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
  G.Colorable k ↔
  ∃ I : Finset (Fin n × Fin k), I.card = n ∧
    ∀ p ∈ I, ∀ q ∈ I, p ≠ q → p.1 ≠ q.1 ∧ (G.Adj p.1 q.1 → p.2 ≠ q.2) := by
  intro n k G
  constructor
  · rintro ⟨C⟩
    refine ⟨Finset.univ.image (fun v => (v, C v)), ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (fun a b h => by simpa using congrArg Prod.fst h)]
      simp
    · intro p hp q hq hpq
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hq
      refine ⟨fun h => hpq (by simp_all), fun hadj => ?_⟩
      exact C.valid hadj
  · rintro ⟨I, hcard, h⟩
    have hinj : Set.InjOn (fun p : Fin n × Fin k => p.1) (I : Set (Fin n × Fin k)) := by
      intro p hp q hq hpq
      by_contra hne
      exact (h p hp q hq hne).1 hpq
    have himg : I.image (fun p => p.1) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injOn hinj, hcard]
      simp
    have hex : ∀ v : Fin n, ∃ p ∈ I, p.1 = v := fun v => by
      have : v ∈ I.image (fun p => p.1) := by rw [himg]; exact Finset.mem_univ v
      obtain ⟨p, hp, hpv⟩ := Finset.mem_image.1 this
      exact ⟨p, hp, hpv⟩
    choose p hpI hp1 using hex
    refine ⟨SimpleGraph.Coloring.mk (fun v => (p v).2) ?_⟩
    intro u v hadj
    have hne : p u ≠ p v := by
      intro heq
      have : u = v := by rw [← hp1 u, ← hp1 v, heq]
      exact G.ne_of_adj hadj this
    exact (h _ (hpI u) _ (hpI v) hne).2 (by rw [hp1 u, hp1 v]; exact hadj)
