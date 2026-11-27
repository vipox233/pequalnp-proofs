import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18862_2
    (hPruneDAG :
      ∀ (n : ℕ),
      let V : Set (Set (Fin n → Bool)) := Set.range fun (i : Fin n) => {x : Fin n → Bool | x i = Bool.true};
      let B : Set (Set (Fin n → Bool)) := {∅, Set.univ} ∪ V;
      ∀ (L : List (Set (Fin n → Bool))),
        (∀ (k : ℕ) (s : Set (Fin n → Bool)), L[k]? = Option.some s →
          ∃ (a : Set (Fin n → Bool)), (a ∈ B ∨ a ∈ List.take k L) ∧
          ∃ (b : Set (Fin n → Bool)), (b ∈ B ∨ b ∈ List.take k L) ∧
          (s = a ∩ b ∨ s = a ∪ b)) →
        ∃ (L' : List (Set (Fin n → Bool))),
          L'.length ≤ L.length ∧
          L'.Nodup ∧
          (∀ s ∈ L', s ∉ B) ∧
          (∀ s ∈ L, s ∈ B ∨ s ∈ L') ∧
          (∀ (k : ℕ) (s : Set (Fin n → Bool)), L'[k]? = Option.some s →
            ∃ (a : Set (Fin n → Bool)), (a ∈ V ∨ a ∈ List.take k L') ∧
            ∃ (b : Set (Fin n → Bool)), (b ∈ V ∨ b ∈ List.take k L') ∧
            (s = a ∩ b ∨ s = a ∪ b)))
    (hCleanNoInter :
      let V : Set (Set (Fin (26 : ℕ) → Bool)) := Set.range fun (i : Fin (26 : ℕ)) => {x : Fin (26 : ℕ) → Bool | x i = Bool.true};
      let B : Set (Set (Fin (26 : ℕ) → Bool)) := {∅, Set.univ} ∪ V;
      let T : Set (Fin (26 : ℕ) → Bool) := {x : Fin (26 : ℕ) → Bool | ∃ (p q : Fin (13 : ℕ)), (↑p + ↑q) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x (Fin.castAdd (13 : ℕ) p) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) q) = Bool.true};
      ∀ (L : List (Set (Fin (26 : ℕ) → Bool))),
        L.length ≤ (62 : ℕ) →
        L.Nodup →
        (∀ s ∈ L, s ∉ B) →
        (∀ (k : ℕ) (s : Set (Fin (26 : ℕ) → Bool)), L[k]? = Option.some s →
          ∃ (a : Set (Fin (26 : ℕ) → Bool)), (a ∈ V ∨ a ∈ List.take k L) ∧
          ∃ (b : Set (Fin (26 : ℕ) → Bool)), (b ∈ V ∨ b ∈ List.take k L) ∧
          (s = a ∩ b ∨ s = a ∪ b)) →
        ∀ (a b : Set (Fin (26 : ℕ) → Bool)), (a ∈ B ∨ a ∈ L) → (b ∈ B ∨ b ∈ L) → a ∩ b ≠ T) :
    (have x1 : Set (Set (Fin (26 : ℕ) → Bool)) := {∅, Set.univ} ∪ Set.range fun (x1 : Fin (26 : ℕ)) => {x2 : Fin (26 : ℕ) → Bool | x2 x1 = Bool.true}; ∀ (x2 : List (Set (Fin (26 : ℕ) → Bool))), x2.length ≤ (62 : ℕ) → (∀ (x4 : ℕ) (x5 : Set (Fin (26 : ℕ) → Bool)), x2[x4]? = Option.some x5 → ∃ x7 ∈ x1 ∪ ↑(List.take x4 x2).toFinset, ∃ x8 ∈ x1 ∪ ↑(List.take x4 x2).toFinset, x5 = x7 ∩ x8 ∨ x5 = x7 ∪ x8) → ∀ x5 ∈ x1 ∪ ↑x2.toFinset, ∀ x7 ∈ x1 ∪ ↑x2.toFinset, x5 ∩ x7 ≠ {x9 : Fin (26 : ℕ) → Bool | ∃ (x10 : Fin (13 : ℕ)) (x11 : Fin (13 : ℕ)), (↑x10 + ↑x11) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x9 (Fin.castAdd (13 : ℕ) x10) = Bool.true ∧ x9 (Fin.natAdd (13 : ℕ) x11) = Bool.true}) :=
  fun x2 hLen hStep x5 hx5 x7 hx7 =>
    Exists.elim
      (hPruneDAG 26 x2 fun k s hk =>
        Exists.elim (hStep k s hk) fun a ha =>
          Exists.elim ha.2 fun b hb =>
            ⟨a, Or.elim ha.1 Or.inl (fun h => Or.inr (List.mem_toFinset.mp (Finset.mem_coe.mp h))),
             b, Or.elim hb.1 Or.inl (fun h => Or.inr (List.mem_toFinset.mp (Finset.mem_coe.mp h))),
             hb.2⟩)
      fun L' hL' =>
        hCleanNoInter L'
          (Nat.le_trans hL'.1 hLen)
          hL'.2.1
          hL'.2.2.1
          hL'.2.2.2.2
          x5 x7
          (Or.elim hx5 Or.inl (fun h => hL'.2.2.2.1 x5 (List.mem_toFinset.mp (Finset.mem_coe.mp h))))
          (Or.elim hx7 Or.inl (fun h => hL'.2.2.2.1 x7 (List.mem_toFinset.mp (Finset.mem_coe.mp h))))
