import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18958_2
    (hElimConst :
      ∀ (n : ℕ),
      let V : Set (Set (Fin n → Bool)) := Set.range fun (i : Fin n) => {x : Fin n → Bool | x i = Bool.true};
      let B : Set (Set (Fin n → Bool)) := {∅, Set.univ} ∪ V;
      ∀ (L : List (Set (Fin n → Bool))),
        L.Nodup →
        (∀ s ∈ L, s ∉ B) →
        (∀ (k : ℕ) (s : Set (Fin n → Bool)), L[k]? = Option.some s →
          ∃ (a : Set (Fin n → Bool)), (a ∈ B ∨ a ∈ List.take k L) ∧
          ∃ (b : Set (Fin n → Bool)), (b ∈ B ∨ b ∈ List.take k L) ∧
          (s = a ∩ b ∨ s = a ∪ b)) →
        ∀ (k : ℕ) (s : Set (Fin n → Bool)), L[k]? = Option.some s →
          ∃ (a : Set (Fin n → Bool)), (a ∈ V ∨ a ∈ List.take k L) ∧
          ∃ (b : Set (Fin n → Bool)), (b ∈ V ∨ b ∈ List.take k L) ∧
          (s = a ∩ b ∨ s = a ∪ b))
    (hNoVarDAG :
      let V : Set (Set (Fin (26 : ℕ) → Bool)) := Set.range fun (i : Fin (26 : ℕ)) => {x : Fin (26 : ℕ) → Bool | x i = Bool.true};
      let B : Set (Set (Fin (26 : ℕ) → Bool)) := {∅, Set.univ} ∪ V;
      let T : Set (Fin (26 : ℕ) → Bool) := {x : Fin (26 : ℕ) → Bool | ∃ (p q : Fin (13 : ℕ)), (↑p + ↑q) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x (Fin.castAdd (13 : ℕ) p) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) q) = Bool.true};
      ∀ (L : List (Set (Fin (26 : ℕ) → Bool))),
        L.length ≤ (62 : ℕ) →
        L.Nodup →
        (∀ s ∈ L, s ∉ B) →
        T ∉ L →
        (∀ (k : ℕ) (s : Set (Fin (26 : ℕ) → Bool)), L[k]? = Option.some s →
          ∃ (a : Set (Fin (26 : ℕ) → Bool)), (a ∈ V ∨ a ∈ List.take k L) ∧
          ∃ (b : Set (Fin (26 : ℕ) → Bool)), (b ∈ V ∨ b ∈ List.take k L) ∧
          (s = a ∩ b ∨ s = a ∪ b)) →
        ∀ a ∈ L, ∀ b ∈ L, a ≠ b → T ⊆ a → a ≠ T → T ⊆ b → b ≠ T → a ∩ b ≠ T) :
    (have x1 : Set (Set (Fin (26 : ℕ) → Bool)) := {∅, Set.univ} ∪ Set.range fun (x1 : Fin (26 : ℕ)) => {x2 : Fin (26 : ℕ) → Bool | x2 x1 = Bool.true}; have x2 : Set (Fin (26 : ℕ) → Bool) := {x2 : Fin (26 : ℕ) → Bool | ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (↑x3 + ↑x4) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true}; ∀ (x3 : List (Set (Fin (26 : ℕ) → Bool))), x3.length ≤ (62 : ℕ) → x3.Nodup → (∀ x6 ∈ x3, x6 ∉ x1) → x2 ∉ x3 → (∀ (x8 : ℕ) (x9 : Set (Fin (26 : ℕ) → Bool)), x3[x8]? = Option.some x9 → ∃ (x11 : Set (Fin (26 : ℕ) → Bool)), (x11 ∈ x1 ∨ x11 ∈ List.take x8 x3) ∧ ∃ (x12 : Set (Fin (26 : ℕ) → Bool)), (x12 ∈ x1 ∨ x12 ∈ List.take x8 x3) ∧ (x9 = x11 ∩ x12 ∨ x9 = x11 ∪ x12)) → ∀ x9 ∈ x3, ∀ x11 ∈ x3, x9 ≠ x11 → x2 ⊆ x9 → x9 ≠ x2 → x2 ⊆ x11 → x11 ≠ x2 → x9 ∩ x11 ≠ x2) :=
  fun x3 hLen hNd hNotB hNotT hStep =>
    hNoVarDAG x3 hLen hNd hNotB hNotT (hElimConst 26 x3 hNd hNotB hStep)
