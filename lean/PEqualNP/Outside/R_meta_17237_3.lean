import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17237_3
    (hReindex :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ) (f : Fin (22 : ℕ) → Fin (25 : ℕ)),
        PEqualNP.MetaComplexity.Monotone2 C →
        C.output < (22 : ℕ) + C.size →
        w < (22 : ℕ) + C.size →
        ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (w' : ℕ),
          PEqualNP.MetaComplexity.Monotone2 D ∧
          D.size = C.size ∧
          D.output < (25 : ℕ) + D.size ∧
          w' < (25 : ℕ) + D.size ∧
          ∀ (x : Fin (25 : ℕ) → Bool),
            (D.wires (List.ofFn x)).getD D.output Bool.false = (C.wires (List.ofFn fun (k : Fin (22 : ℕ)) => x (f k))).getD C.output Bool.false ∧
            (D.wires (List.ofFn x)).getD w' Bool.false = (C.wires (List.ofFn fun (k : Fin (22 : ℕ)) => x (f k))).getD w Bool.false)
    (hCompact22 :
      let adj : Fin (9 : ℕ) → Fin (13 : ℕ) → Prop := fun i j =>
        (([(1 : ℕ), (3 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (9 : ℕ), (10 : ℕ), (11 : ℕ)].getD (i : ℕ) (0 : ℕ)) + (j : ℕ) + (1 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ),
        PEqualNP.MetaComplexity.Monotone2 C ∧
        C.size ≤ (45 : ℕ) ∧
        C.output < (22 : ℕ) + C.size ∧
        w < (22 : ℕ) + C.size ∧
        (∀ (i : Fin (9 : ℕ)) (j : Fin (13 : ℕ)), adj i j →
          (C.wires (List.ofFn fun (k : Fin (22 : ℕ)) => Decidable.decide (k = Fin.castAdd (13 : ℕ) i ∨ k = Fin.natAdd (9 : ℕ) j))).getD C.output Bool.false = Bool.true) ∧
        (∀ (y : Fin (22 : ℕ) → Bool),
          (∀ (i : Fin (9 : ℕ)) (j : Fin (13 : ℕ)), adj i j → y (Fin.castAdd (13 : ℕ) i) = Bool.false ∨ y (Fin.natAdd (9 : ℕ) j) = Bool.false) →
          (C.wires (List.ofFn y)).getD C.output Bool.false = Bool.false ∧
          (y (10 : Fin (22 : ℕ)) = Bool.false → y (12 : Fin (22 : ℕ)) = Bool.false → y (18 : Fin (22 : ℕ)) = Bool.false → (C.wires (List.ofFn y)).getD w Bool.false = Bool.false)) ∧
        (∀ (k : Fin (22 : ℕ)), k.val ∈ [(10 : ℕ), (12 : ℕ), (18 : ℕ)] →
          (C.wires (List.ofFn fun (j : Fin (22 : ℕ)) => Decidable.decide (j = k))).getD w Bool.false = Bool.true)) :
    (have x1 : Fin (25 : ℕ) → Fin (25 : ℕ) → Prop := fun (x1 x2 : Fin (25 : ℕ)) => ↑x1 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x2 ∧ (↑x1 + ↑x2 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x1 ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)]; have x2 : Finset (Fin (25 : ℕ)) := {(13 : Fin (25 : ℕ)), (15 : Fin (25 : ℕ)), (21 : Fin (25 : ℕ))}; have x3 : Finset (Fin (25 : ℕ)) → Prop := fun (x3 : Finset (Fin (25 : ℕ))) => ¬∃ x4 ∈ x3, ∃ x5 ∈ x3, x1 x4 x5; have x4 : Finset (Fin (25 : ℕ)) → Finset (Fin (25 : ℕ)) → Prop := fun (x4 x5 : Finset (Fin (25 : ℕ))) => x5 ⊆ x4 ∧ x3 x5 ∧ ∀ x6 ∈ x4, x6 ∉ x5 → ¬x3 (Insert.insert x6 x5); ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x5 ∧     x5.size ≤ (45 : ℕ) ∧       x5.output < (25 : ℕ) + x5.size ∧         x6 < (25 : ℕ) + x5.size ∧           have x7 : Finset (Fin (25 : ℕ)) → ℕ → Bool := fun (x7 : Finset (Fin (25 : ℕ))) (x8 : ℕ) => (x5.wires (List.ofFn fun (x9 : Fin (25 : ℕ)) => Decidable.decide (x9 ∈ x7))).getD x8 Bool.false;           (∀ (x8 x9 : Fin (25 : ℕ)), x1 x8 x9 → x7 {x8, x9} x5.output = Bool.true) ∧ (∀ (x8 : Finset (Fin (25 : ℕ))), x4 Finset.univ x8 → x7 x8 x5.output = Bool.false) ∧ (∀ x8 ∈ x2, x7 {x8} x6 = Bool.true) ∧ ∀ (x8 : Finset (Fin (25 : ℕ))), x4 (Finset.univ \ x2) x8 → x7 x8 x6 = Bool.false) := by
  let f : Fin (22 : ℕ) → Fin (25 : ℕ) := fun k =>
    Fin.ofNat (25 : ℕ) ([(1 : ℕ), (3 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (9 : ℕ), (10 : ℕ), (11 : ℕ), (12 : ℕ), (13 : ℕ), (14 : ℕ), (15 : ℕ), (16 : ℕ), (17 : ℕ), (18 : ℕ), (19 : ℕ), (20 : ℕ), (21 : ℕ), (22 : ℕ), (23 : ℕ), (24 : ℕ)].getD k.val (0 : ℕ))
  have hfInj : ∀ k₁ k₂ : Fin (22 : ℕ), f k₁ = f k₂ → k₁ = k₂ := by decide
  have hEdgeFwd : ∀ a b : Fin (25 : ℕ),
      (↑a < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑b ∧ (↑a + ↑b + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑a ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)]) →
      ∃ (i : Fin (9 : ℕ)) (j : Fin (13 : ℕ)),
        (([(1 : ℕ), (3 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (9 : ℕ), (10 : ℕ), (11 : ℕ)].getD (i : ℕ) (0 : ℕ)) + (j : ℕ) + (1 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
        f (Fin.castAdd (13 : ℕ) i) = a ∧ f (Fin.natAdd (9 : ℕ) j) = b := by decide
  have hEdgeBwd : ∀ (i : Fin (9 : ℕ)) (j : Fin (13 : ℕ)),
      (([(1 : ℕ), (3 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (9 : ℕ), (10 : ℕ), (11 : ℕ)].getD (i : ℕ) (0 : ℕ)) + (j : ℕ) + (1 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] →
      (↑(f (Fin.castAdd (13 : ℕ) i)) < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑(f (Fin.natAdd (9 : ℕ) j)) ∧
        (↑(f (Fin.castAdd (13 : ℕ) i)) + ↑(f (Fin.natAdd (9 : ℕ) j)) + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
        ↑(f (Fin.castAdd (13 : ℕ) i)) ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)]) := by decide
  have hW : ∀ z : Fin (25 : ℕ), z ∈ ({(13 : Fin (25 : ℕ)), (15 : Fin (25 : ℕ)), (21 : Fin (25 : ℕ))} : Finset (Fin (25 : ℕ))) →
      ∃ k : Fin (22 : ℕ), k.val ∈ [(10 : ℕ), (12 : ℕ), (18 : ℕ)] ∧ f k = z := by decide
  have hF10 : f (10 : Fin (22 : ℕ)) = (13 : Fin (25 : ℕ)) := by decide
  have hF12 : f (12 : Fin (22 : ℕ)) = (15 : Fin (25 : ℕ)) := by decide
  have hF18 : f (18 : Fin (22 : ℕ)) = (21 : Fin (25 : ℕ)) := by decide
  obtain ⟨C, w, hM, hSz, hOut, hWlt, hPos, hNeg, hSing⟩ := hCompact22
  obtain ⟨D, w', hDM, hDSz, hDOut, hDWlt, hDEval⟩ := hReindex C w f hM hOut hWlt
  dsimp only
  refine ⟨D, w', hDM, hDSz.symm ▸ hSz, hDOut, hDWlt, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    obtain ⟨i, j, hij, hfa, hfb⟩ := hEdgeFwd a b hab
    rw [(hDEval _).1]
    have hfun : (fun k : Fin (22 : ℕ) => Decidable.decide (f k ∈ ({a, b} : Finset (Fin (25 : ℕ))))) =
        (fun k : Fin (22 : ℕ) => Decidable.decide (k = Fin.castAdd (13 : ℕ) i ∨ k = Fin.natAdd (9 : ℕ) j)) := by
      funext k
      rw [decide_eq_decide]
      exact ⟨fun hk => Or.elim (Finset.mem_insert.mp hk) (fun h1 => Or.inl (hfInj _ _ (h1.trans hfa.symm))) (fun h2 => Or.inr (hfInj _ _ ((Finset.mem_singleton.mp h2).trans hfb.symm))),
        fun hk => Or.elim hk (fun h1 => Finset.mem_insert.mpr (Or.inl (h1 ▸ hfa))) (fun h2 => Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (h2 ▸ hfb))))⟩
    rw [hfun]
    exact hPos i j hij
  · intro S hS
    rw [(hDEval _).1]
    refine (hNeg _ (fun i j hij => ?_)).1
    by_cases hi : f (Fin.castAdd (13 : ℕ) i) ∈ S
    · refine Or.inr (decide_eq_false (fun hj => hS.2.1 ⟨f (Fin.castAdd (13 : ℕ) i), hi, f (Fin.natAdd (9 : ℕ) j), hj, hEdgeBwd i j hij⟩))
    · exact Or.inl (decide_eq_false hi)
  · intro z hz
    obtain ⟨k, hk, hfk⟩ := hW z hz
    rw [(hDEval _).2]
    have hfun : (fun j : Fin (22 : ℕ) => Decidable.decide (f j ∈ ({z} : Finset (Fin (25 : ℕ))))) =
        (fun j : Fin (22 : ℕ) => Decidable.decide (j = k)) := by
      funext j
      rw [decide_eq_decide]
      exact ⟨fun hj => hfInj _ _ ((Finset.mem_singleton.mp hj).trans hfk.symm), fun hj => Finset.mem_singleton.mpr (hj ▸ hfk)⟩
    rw [hfun]
    exact hSing k hk
  · intro S hS
    rw [(hDEval _).2]
    have hind : ∀ (i : Fin (9 : ℕ)) (j : Fin (13 : ℕ)),
        (([(1 : ℕ), (3 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ), (7 : ℕ), (9 : ℕ), (10 : ℕ), (11 : ℕ)].getD (i : ℕ) (0 : ℕ)) + (j : ℕ) + (1 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] →
        Decidable.decide (f (Fin.castAdd (13 : ℕ) i) ∈ S) = Bool.false ∨ Decidable.decide (f (Fin.natAdd (9 : ℕ) j) ∈ S) = Bool.false := by
      intro i j hij
      by_cases hi : f (Fin.castAdd (13 : ℕ) i) ∈ S
      · exact Or.inr (decide_eq_false (fun hj => hS.2.1 ⟨f (Fin.castAdd (13 : ℕ) i), hi, f (Fin.natAdd (9 : ℕ) j), hj, hEdgeBwd i j hij⟩))
      · exact Or.inl (decide_eq_false hi)
    refine (hNeg _ hind).2 ?_ ?_ ?_
    · exact decide_eq_false (fun h => (Finset.mem_sdiff.mp (hS.1 h)).2 (hF10 ▸ (by decide : (13 : Fin (25 : ℕ)) ∈ ({(13 : Fin (25 : ℕ)), (15 : Fin (25 : ℕ)), (21 : Fin (25 : ℕ))} : Finset (Fin (25 : ℕ))))))
    · exact decide_eq_false (fun h => (Finset.mem_sdiff.mp (hS.1 h)).2 (hF12 ▸ (by decide : (15 : Fin (25 : ℕ)) ∈ ({(13 : Fin (25 : ℕ)), (15 : Fin (25 : ℕ)), (21 : Fin (25 : ℕ))} : Finset (Fin (25 : ℕ))))))
    · exact decide_eq_false (fun h => (Finset.mem_sdiff.mp (hS.1 h)).2 (hF18 ▸ (by decide : (21 : Fin (25 : ℕ)) ∈ ({(13 : Fin (25 : ℕ)), (15 : Fin (25 : ℕ)), (21 : Fin (25 : ℕ))} : Finset (Fin (25 : ℕ))))))
