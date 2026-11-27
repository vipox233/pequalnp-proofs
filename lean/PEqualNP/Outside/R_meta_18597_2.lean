import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18597_2
    (hOutAndEdgeSound :
      have G : SimpleGraph (Fin (42 : ℕ)) :=
        SimpleGraph.fromRel fun (x3 x4 : Fin (42 : ℕ)) =>
          ↑x3 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x4 ∧ (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]
      ∀ (x1 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)),
        x1.WellFormed → x1.Computes G →
        x1.outVars = ∅ ∧
          ∀ g ∈ x1.outGates, ∀ u ∈ x1.leftVars g, ∀ v ∈ x1.rightVars g, G.Adj u v)
    (hNoThreeRepGates :
      have G : SimpleGraph (Fin (42 : ℕ)) :=
        SimpleGraph.fromRel fun (x3 x4 : Fin (42 : ℕ)) =>
          ↑x3 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x4 ∧ (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]
      ∀ (x1 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)),
        (x1.WellFormed ∧ x1.Computes G ∧
          (∀ (x4 : Fin x1.size), Disjoint (x1.leftVars x4) (x1.rightVars x4)) ∧
          x1.size ≤ (20 : ℕ) ∧ x1.outVars = ∅ ∧
          ∀ g ∈ x1.outGates, ∀ u ∈ x1.leftVars g, ∀ v ∈ x1.rightVars g, G.Adj u v) →
        have cov : Fin x1.size → Fin (21 : ℕ) → Fin (21 : ℕ) → Prop := fun g d u =>
          Fin.castAdd (21 : ℕ) u ∈ x1.leftVars g ∧ Fin.natAdd (21 : ℕ) (u + d) ∈ x1.rightVars g ∨
          Fin.natAdd (21 : ℕ) (u + d) ∈ x1.leftVars g ∧ Fin.castAdd (21 : ℕ) u ∈ x1.rightVars g
        have fst : Fin x1.size → Fin (21 : ℕ) → Fin (21 : ℕ) → Prop := fun g d u =>
          cov g d u ∧ ∀ g' < g, ¬cov g' d u
        have rep : Fin x1.size → Fin (21 : ℕ) → Prop := fun g d =>
          ↑d ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)] ∧
          ∃ (u1 u2 : Fin (21 : ℕ)), u1 ≠ u2 ∧ fst g d u1 ∧ fst g d u2
        ∀ (g1 g2 g3 : Fin x1.size) (d1 d2 d3 : Fin (21 : ℕ)),
          g1 < g2 → g2 < g3 → rep g1 d1 → rep g2 d2 → rep g3 d3 → False) :
    (∀ (x1 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)),   x1.WellFormed →     x1.Computes (SimpleGraph.fromRel fun (x3 x4 : Fin (42 : ℕ)) => ↑x3 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x4 ∧ (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) →       (∀ (x4 : Fin x1.size), Disjoint (x1.leftVars x4) (x1.rightVars x4)) →         x1.size ≤ (20 : ℕ) →           have x6 : Finset (Fin (21 : ℕ)) := {(0 : Fin (21 : ℕ)), (5 : Fin (21 : ℕ)), (7 : Fin (21 : ℕ)), (17 : Fin (21 : ℕ)), (20 : Fin (21 : ℕ))};           have x7 : Fin (21 : ℕ) → Fin (21 : ℕ) → Finset (Fin (42 : ℕ)) := fun (x7 x8 : Fin (21 : ℕ)) => {Fin.castAdd (21 : ℕ) x8, Fin.natAdd (21 : ℕ) (x8 + x7)};           have x8 : Fin x1.size → Fin (21 : ℕ) → Fin (21 : ℕ) → Prop := fun (x8 : Fin x1.size) (x9 x10 : Fin (21 : ℕ)) => (∃ x11 ∈ x1.leftVars x8, x11 ∈ x7 x9 x10) ∧ ∃ x11 ∈ x1.rightVars x8, x11 ∈ x7 x9 x10;           have x9 : Fin x1.size → Fin (21 : ℕ) → Fin (21 : ℕ) → Prop := fun (x9 : Fin x1.size) (x10 x11 : Fin (21 : ℕ)) => x8 x9 x10 x11 ∧ ∀ x12 < x9, ¬x8 x12 x10 x11;           have x10 : Fin x1.size → Fin (21 : ℕ) → Prop := fun (x10 : Fin x1.size) (x11 : Fin (21 : ℕ)) => ∃ (x12 : Fin (21 : ℕ)) (x13 : Fin (21 : ℕ)), x12 ≠ x13 ∧ x9 x10 x11 x12 ∧ x9 x10 x11 x13;           {x11 : Fin x1.size | ∃ x12 ∈ x6, x10 x11 x12}.ncard ≤ (2 : ℕ)) := by
  intro x1 hWF hComp hDisj hSz x6 x7 x8 x9 x10
  rcases hOutAndEdgeSound x1 hWF hComp with ⟨hOutEmpty, hEdgeSound⟩
  have hcov : x8 = fun (g : Fin x1.size) (d u : Fin 21) =>
      Fin.castAdd 21 u ∈ x1.leftVars g ∧ Fin.natAdd 21 (u + d) ∈ x1.rightVars g ∨
      Fin.natAdd 21 (u + d) ∈ x1.leftVars g ∧ Fin.castAdd 21 u ∈ x1.rightVars g := by
    funext g' d u
    apply propext
    constructor
    · rintro ⟨⟨a, haL, ha7⟩, ⟨b, hbR, hb7⟩⟩
      simp only [x7, Finset.mem_insert, Finset.mem_singleton] at ha7 hb7
      rcases ha7 with rfl | rfl <;> rcases hb7 with rfl | rfl
      · exact absurd hbR (Finset.disjoint_left.mp (hDisj g') haL)
      · exact Or.inl ⟨haL, hbR⟩
      · exact Or.inr ⟨haL, hbR⟩
      · exact absurd hbR (Finset.disjoint_left.mp (hDisj g') haL)
    · rintro (⟨hL, hR⟩ | ⟨hL, hR⟩)
      · exact ⟨⟨Fin.castAdd 21 u, hL, by simp [x7]⟩, ⟨Fin.natAdd 21 (u + d), hR, by simp [x7]⟩⟩
      · exact ⟨⟨Fin.natAdd 21 (u + d), hL, by simp [x7]⟩, ⟨Fin.castAdd 21 u, hR, by simp [x7]⟩⟩
  have hmem6 : ∀ d : Fin 21, d ∈ x6 → d.val ∈ [(0 : ℕ), 5, 7, 17, 20] := by
    intro d hd
    simp only [x6, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact hd
  have hrep : ∀ g : Fin x1.size, (∃ d ∈ x6, x10 g d) →
      ∃ d : Fin 21, d.val ∈ [(0 : ℕ), 5, 7, 17, 20] ∧
      ∃ (u1 u2 : Fin 21), u1 ≠ u2 ∧
        ((Fin.castAdd 21 u1 ∈ x1.leftVars g ∧ Fin.natAdd 21 (u1 + d) ∈ x1.rightVars g ∨
          Fin.natAdd 21 (u1 + d) ∈ x1.leftVars g ∧ Fin.castAdd 21 u1 ∈ x1.rightVars g) ∧
         ∀ g' < g, ¬(Fin.castAdd 21 u1 ∈ x1.leftVars g' ∧ Fin.natAdd 21 (u1 + d) ∈ x1.rightVars g' ∨
           Fin.natAdd 21 (u1 + d) ∈ x1.leftVars g' ∧ Fin.castAdd 21 u1 ∈ x1.rightVars g')) ∧
        ((Fin.castAdd 21 u2 ∈ x1.leftVars g ∧ Fin.natAdd 21 (u2 + d) ∈ x1.rightVars g ∨
          Fin.natAdd 21 (u2 + d) ∈ x1.leftVars g ∧ Fin.castAdd 21 u2 ∈ x1.rightVars g) ∧
         ∀ g' < g, ¬(Fin.castAdd 21 u2 ∈ x1.leftVars g' ∧ Fin.natAdd 21 (u2 + d) ∈ x1.rightVars g' ∨
           Fin.natAdd 21 (u2 + d) ∈ x1.leftVars g' ∧ Fin.castAdd 21 u2 ∈ x1.rightVars g')) := by
    rintro g ⟨d, hd6, u1, u2, hne, h1, h2⟩
    refine ⟨d, hmem6 d hd6, u1, u2, hne, ?_, ?_⟩
    · dsimp only [x9] at h1; rw [hcov] at h1; exact h1
    · dsimp only [x9] at h2; rw [hcov] at h2; exact h2
  by_contra hgt
  let S : Set (Fin x1.size) := {g | ∃ d ∈ x6, x10 g d}
  have hfin : S.Finite := Set.toFinite S
  have hcard : 2 < hfin.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card S hfin]
    exact Nat.lt_of_not_ge hgt
  rcases Finset.two_lt_card.mp hcard with ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
  rcases hrep a (hfin.mem_toFinset.mp ha) with ⟨da, hda⟩
  rcases hrep b (hfin.mem_toFinset.mp hb) with ⟨db, hdb⟩
  rcases hrep c (hfin.mem_toFinset.mp hc) with ⟨dc, hdc⟩
  have hno := hNoThreeRepGates x1 ⟨hWF, hComp, hDisj, hSz, hOutEmpty, hEdgeSound⟩
  rcases lt_or_gt_of_ne hab with h1 | h1
  · rcases lt_or_gt_of_ne hbc with h2 | h2
    · exact hno a b c da db dc h1 h2 hda hdb hdc
    · rcases lt_or_gt_of_ne hac with h3 | h3
      · exact hno a c b da dc db h3 h2 hda hdc hdb
      · exact hno c a b dc da db h3 h1 hdc hda hdb
  · rcases lt_or_gt_of_ne hac with h2 | h2
    · exact hno b a c db da dc h1 h2 hdb hda hdc
    · rcases lt_or_gt_of_ne hbc with h3 | h3
      · exact hno b c a db dc da h3 h2 hdb hdc hda
      · exact hno c b a dc db da h3 h1 hdc hdb hda
