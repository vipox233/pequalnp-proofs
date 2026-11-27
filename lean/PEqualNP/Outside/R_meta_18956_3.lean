import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18956_3
    (hNoBotTop :
      ∀ (B : Set (Set (Fin (26 : ℕ) → Bool))) (L : List (Set (Fin (26 : ℕ) → Bool)))
        (idx : ℕ) (s a b : Set (Fin (26 : ℕ) → Bool)),
        L.Nodup →
        (∀ t ∈ L, t ∉ ({∅, Set.univ} : Set (Set (Fin (26 : ℕ) → Bool))) ∪ B) →
        L[idx]? = Option.some s →
        (a ∈ ({∅, Set.univ} : Set (Set (Fin (26 : ℕ) → Bool))) ∪ B ∨ a ∈ List.take idx L) →
        (b ∈ ({∅, Set.univ} : Set (Set (Fin (26 : ℕ) → Bool))) ∪ B ∨ b ∈ List.take idx L) →
        (s = a ∩ b ∨ s = a ∪ b) →
        (a ∈ B ∨ a ∈ List.take idx L) ∧ (b ∈ B ∨ b ∈ List.take idx L) ∧ a ≠ b)
    (hVarBasisOnly :
      have x1 : Set (Set (Fin (26 : ℕ) → Bool)) :=
        Set.range fun (x1 : Fin (26 : ℕ)) => {x2 : Fin (26 : ℕ) → Bool | x2 x1 = Bool.true};
      have x2 : Set (Fin (26 : ℕ) → Bool) :=
        {x2 : Fin (26 : ℕ) → Bool | ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)),
          (↑x3 + ↑x4) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
          x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true};
      ∀ (x3 : List (Set (Fin (26 : ℕ) → Bool))),
        x3.length ≤ (62 : ℕ) →
        x3.Nodup →
        (∀ x6 ∈ x3, x6 ∉ ({∅, Set.univ} : Set (Set (Fin (26 : ℕ) → Bool))) ∪ x1) →
        (∀ (x7 : ℕ) (x8 : Set (Fin (26 : ℕ) → Bool)),
          x3[x7]? = Option.some x8 →
          ∃ (x10 : Set (Fin (26 : ℕ) → Bool)), (x10 ∈ x1 ∨ x10 ∈ List.take x7 x3) ∧
            ∃ (x11 : Set (Fin (26 : ℕ) → Bool)), (x11 ∈ x1 ∨ x11 ∈ List.take x7 x3) ∧
              x10 ≠ x11 ∧ (x8 = x10 ∩ x11 ∨ x8 = x10 ∪ x11)) →
        x2 ∉ x3) :
    (have x1 : Set (Set (Fin (26 : ℕ) → Bool)) := {∅, Set.univ} ∪ Set.range fun (x1 : Fin (26 : ℕ)) => {x2 : Fin (26 : ℕ) → Bool | x2 x1 = Bool.true}; have x2 : Set (Fin (26 : ℕ) → Bool) := {x2 : Fin (26 : ℕ) → Bool | ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (↑x3 + ↑x4) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true}; ∀ (x3 : List (Set (Fin (26 : ℕ) → Bool))), x3.length ≤ (62 : ℕ) → x3.Nodup → (∀ x6 ∈ x3, x6 ∉ x1) → (∀ (x7 : ℕ) (x8 : Set (Fin (26 : ℕ) → Bool)), x3[x7]? = Option.some x8 → ∃ (x10 : Set (Fin (26 : ℕ) → Bool)), (x10 ∈ x1 ∨ x10 ∈ List.take x7 x3) ∧ ∃ (x11 : Set (Fin (26 : ℕ) → Bool)), (x11 ∈ x1 ∨ x11 ∈ List.take x7 x3) ∧ (x8 = x10 ∩ x11 ∨ x8 = x10 ∪ x11)) → x2 ∉ x3) := by
  intro x1 x2 x3 hlen hnd hnotB hstep
  apply hVarBasisOnly x3 hlen hnd hnotB
  intro idx s hs
  rcases hstep idx s hs with ⟨a, ha, b, hb, hcomb⟩
  have hclean := hNoBotTop (Set.range fun (i : Fin 26) => {f : Fin 26 → Bool | f i = true}) x3 idx s a b hnd hnotB hs ha hb hcomb
  exact ⟨a, hclean.1, b, hclean.2.1, hclean.2.2, hcomb⟩
