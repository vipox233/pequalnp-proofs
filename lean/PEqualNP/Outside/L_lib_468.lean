import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_468 : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  let E : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)
  let star : Fin n → Finset (Fin n × Fin n) := fun v =>
    E.filter (fun p => p.1 = v ∨ p.2 = v)
  (∃ T : Finset (Fin n), T.card ≤ k ∧ G.IsVertexCover (↑T)) ↔
    ∃ F : Finset (Finset (Fin n × Fin n)), F ⊆ Finset.univ.image star ∧
      F.card ≤ k ∧ ∀ e ∈ E, ∃ A ∈ F, e ∈ A := by
  intro n k G _ E star
  constructor
  · rintro ⟨T, hT, hc⟩
    refine ⟨T.image star, ?_, (Finset.card_image_le).trans hT, ?_⟩
    · intro A hA
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hA
      exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
    · intro e he
      have he' := he
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at he'
      rcases hc he'.2 with h | h
      · exact ⟨star e.1, Finset.mem_image.mpr ⟨e.1, h, rfl⟩, Finset.mem_filter.mpr ⟨he, Or.inl rfl⟩⟩
      · exact ⟨star e.2, Finset.mem_image.mpr ⟨e.2, h, rfl⟩, Finset.mem_filter.mpr ⟨he, Or.inr rfl⟩⟩
  · rintro ⟨F, hF, hk, hc⟩
    classical
    have hex : ∀ A ∈ F, ∃ v, star v = A := by
      intro A hA
      obtain ⟨v, _, h⟩ := Finset.mem_image.mp (hF hA)
      exact ⟨v, h⟩
    let g : F → Fin n := fun A => (hex A.1 A.2).choose
    have hg : ∀ A : F, star (g A) = A.1 := fun A => (hex A.1 A.2).choose_spec
    refine ⟨F.attach.image g, (Finset.card_image_le).trans (by simpa using hk), ?_⟩
    intro a b hab
    rcases lt_trichotomy a b with h | h | h
    · have he : (a, b) ∈ E := by
        simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h, hab⟩
      obtain ⟨A, hA, heA⟩ := hc _ he
      have hgA : star (g ⟨A, hA⟩) = A := hg ⟨A, hA⟩
      rw [← hgA] at heA
      simp only [star, Finset.mem_filter] at heA
      rcases heA.2 with h1 | h1
      · left; simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]; exact ⟨⟨A, hA⟩, Finset.mem_attach _ _, h1.symm⟩
      · right; simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]; exact ⟨⟨A, hA⟩, Finset.mem_attach _ _, h1.symm⟩
    · exact absurd h (G.ne_of_adj hab)
    · have he : (b, a) ∈ E := by
        simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨h, hab.symm⟩
      obtain ⟨A, hA, heA⟩ := hc _ he
      have hgA : star (g ⟨A, hA⟩) = A := hg ⟨A, hA⟩
      rw [← hgA] at heA
      simp only [star, Finset.mem_filter] at heA
      rcases heA.2 with h1 | h1
      · right; simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]; exact ⟨⟨A, hA⟩, Finset.mem_attach _ _, h1.symm⟩
      · left; simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]; exact ⟨⟨A, hA⟩, Finset.mem_attach _ _, h1.symm⟩
