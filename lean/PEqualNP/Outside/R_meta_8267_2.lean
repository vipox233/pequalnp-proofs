import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8267_2
    (hRestrictEdges :
      have step : Set (Set (Fin 42 × Fin 42)) → Set (Fin 42 × Fin 42) × Set (Fin 42 × Fin 42) → Set (Set (Fin 42 × Fin 42)) :=
        fun F p => {S | S ∈ F ∨ p.1 ∈ F ∧ p.2 ∈ F ∧ S ⊆ p.1 ∪ p.2};
      have init : Set (Fin 42) → Set (Set (Fin 42 × Fin 42)) :=
        fun V => {S | S = ∅ ∨ ∃ v ∈ V, ∀ e ∈ S, e.1 = v ∨ e.2 = v};
      ∀ (E : Set (Fin 42 × Fin 42)) (xs : List (Set (Fin 42 × Fin 42) × Set (Fin 42 × Fin 42))),
        (∀ (V : Set (Fin 42)), (∀ e ∈ E, e.1 ∈ V ∨ e.2 ∈ V) → E ∈ List.foldl step (init V) xs) →
        ∃ (ys : List (Set (Fin 42 × Fin 42) × Set (Fin 42 × Fin 42))),
          ys.length = xs.length ∧
          (∀ p ∈ ys, p.1 ⊆ E ∧ p.2 ⊆ E) ∧
          ∀ (V : Set (Fin 42)), (∀ e ∈ E, e.1 ∈ V ∨ e.2 ∈ V) → E ∈ List.foldl step (init V) ys)
    (hRestrictedLB :
      have x3 : Set (Fin 42 × Fin 42) :=
        {e | e.1.1 < 21 ∧ 21 ≤ e.2.1 ∧ (e.2.1 + 21 - e.1.1) % 21 ∈ [0, 5, 7, 17, 20]};
      have step : Set (Set (Fin 42 × Fin 42)) → Set (Fin 42 × Fin 42) × Set (Fin 42 × Fin 42) → Set (Set (Fin 42 × Fin 42)) :=
        fun F p => {S | S ∈ F ∨ p.1 ∈ F ∧ p.2 ∈ F ∧ S ⊆ p.1 ∪ p.2};
      have init : Set (Fin 42) → Set (Set (Fin 42 × Fin 42)) :=
        fun V => {S | S = ∅ ∨ ∃ v ∈ V, ∀ e ∈ S, e.1 = v ∨ e.2 = v};
      ∀ (ys : List (Set (Fin 42 × Fin 42) × Set (Fin 42 × Fin 42))),
        (∀ p ∈ ys, p.1 ⊆ x3 ∧ p.2 ⊆ x3) →
        (∀ (V : Set (Fin 42)), (∀ e ∈ x3, e.1 ∈ V ∨ e.2 ∈ V) → x3 ∈ List.foldl step (init V) ys) →
        104 ≤ ys.length) :
    (let x1 : Type := Fin (42 : ℕ); let x2 : Type := x1 × x1; have x3 : Set x2 := {x3 : x2 | ↑x3.1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x3.2 ∧ (↑x3.2 + (21 : ℕ) - ↑x3.1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]}; have x4 : Set (Set x2) → Set x2 × Set x2 → Set (Set x2) := fun (x4 : Set (Set x2)) (x5 : Set x2 × Set x2) => {x6 : Set x2 | x6 ∈ x4 ∨ x5.1 ∈ x4 ∧ x5.2 ∈ x4 ∧ x6 ⊆ x5.1 ∪ x5.2}; have x5 : Set x1 → Set (Set x2) := fun (x5 : Set x1) => {x6 : Set x2 | x6 = ∅ ∨ ∃ x7 ∈ x5, ∀ x8 ∈ x6, x8.1 = x7 ∨ x8.2 = x7}; ∀ (x6 : List (Set x2 × Set x2)), (∀ (x7 : Set x1), (∀ x8 ∈ x3, x8.1 ∈ x7 ∨ x8.2 ∈ x7) → x3 ∈ List.foldl x4 (x5 x7) x6) → (104 : ℕ) ≤ x6.length) :=
  fun x6 h =>
    Exists.elim (hRestrictEdges _ x6 h) fun ys hys =>
      Eq.subst hys.1 (hRestrictedLB ys hys.2.1 hys.2.2)
