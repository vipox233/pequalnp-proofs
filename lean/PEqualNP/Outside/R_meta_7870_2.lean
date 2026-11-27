import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7870_2
    (hNorm28 :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
        ∃ (C' : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.Monotone2 C' ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack (28 : ℕ) C' ∧
          C'.size = C.size ∧
          (∀ (inp : List Bool), inp.length = (28 : ℕ) → C'.wires inp = C.wires inp) ∧
          ∀ j < C.size,
            (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval [Bool.false, Bool.true] = Bool.true →
            (PEqualNP.MetaComplexity.NestedCover.gateAt C' j).op.eval [Bool.false, Bool.true] = Bool.true)
    (hRed7870 : let x1 : Type := Fin (13 : ℕ); have x2 : Finset x1 := {(0 : x1), (1 : x1), (3 : x1), (9 : x1)}; let x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => ∃ x5 ∈ x2, x3 = x4 + x5; let x4 : Finset x1 → x1 → Prop := fun (x4 : Finset x1) (x5 : x1) => ∀ x6 ∈ x4, ¬x3 x6 x5; let x5 : Type := Fin (26 : ℕ) → Bool; have x6 : x1 → x1 → Fin (26 : ℕ) → Bool := fun (x6 x7 : x1) (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x6 ∨ x8 = Fin.natAdd (13 : ℕ) x7); have x7 : Finset x1 → Fin (26 : ℕ) → Bool := fun (x7 : Finset x1) (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x7, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x4 x7 x9); have x8 : Finset x1 → Prop := fun (x8 : Finset x1) => (∀ x9 ∉ x8, ∃ (x11 : x1), x4 x8 x11 ∧ x3 x9 x11) ∧ ((∃ (x9 : x1), ∀ x10 ∈ x8, x3 x10 x9) ∨ ∃ (x9 : x1), ∀ (x10 : x1), x4 x8 x10 → x3 x9 x10); ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x9 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (28 : ℕ) x9 →     have x11 : ℕ → x5 → Bool := fun (x11 : ℕ) (x12 : x5) => (x9.wires (List.ofFn x12 ++ [Bool.true, Bool.false])).getD x11 Bool.false;     have x12 : (x5 → Bool) → Prop := fun (x12 : x5 → Bool) => ∀ (x13 x14 : x1), x3 x13 x14 → x12 (x6 x13 x14) = Bool.true;     have x13 : ℕ × ℕ → x5 → Bool := fun (x13 : ℕ × ℕ) (x14 : x5) => x11 x13.1 x14 || x11 x13.2 x14;     have x14 : Finset (ℕ × ℕ) → Prop := fun (x14 : Finset (ℕ × ℕ)) => ∀ (x15 : Finset x1), x8 x15 → ∃ x17 ∈ x14, ¬x13 x17 (x7 x15) = Bool.true;     ∀ (x15 : Finset (ℕ × ℕ)), (2 : ℕ) ≤ x15.card → x9.size + (2 : ℕ) * x15.card ≤ (64 : ℕ) → (∀ x18 ∈ x15, x12 (x13 x18) ∧ ¬x12 (x11 x18.1) ∧ ¬x12 (x11 x18.2)) → x14 x15 → (20 : ℕ) ≤ {x20 ∈ Finset.range x9.size | (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x20).op.eval [Bool.false, Bool.true] = Bool.true}.card → x15.card ≤ (22 : ℕ) → (∀ x22 ∈ x15, ¬x14 (x15.erase x22)) → False) :
    let x1 : Type := Fin (13 : ℕ); have x2 : Finset x1 := {(0 : x1), (1 : x1), (3 : x1), (9 : x1)}; let x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => ∃ x5 ∈ x2, x3 = x4 + x5; let x4 : Finset x1 → x1 → Prop := fun (x4 : Finset x1) (x5 : x1) => ∀ x6 ∈ x4, ¬x3 x6 x5; let x5 : Type := Fin (26 : ℕ) → Bool; have x6 : x1 → x1 → Fin (26 : ℕ) → Bool := fun (x6 x7 : x1) (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x6 ∨ x8 = Fin.natAdd (13 : ℕ) x7); have x7 : Finset x1 → Fin (26 : ℕ) → Bool := fun (x7 : Finset x1) (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x7, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x4 x7 x9); have x8 : Finset x1 → Prop := fun (x8 : Finset x1) => (∀ x9 ∉ x8, ∃ (x11 : x1), x4 x8 x11 ∧ x3 x9 x11) ∧ ((∃ (x9 : x1), ∀ x10 ∈ x8, x3 x10 x9) ∨ ∃ (x9 : x1), ∀ (x10 : x1), x4 x8 x10 → x3 x9 x10); ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x9 →     have x11 : ℕ → x5 → Bool := fun (x11 : ℕ) (x12 : x5) => (x9.wires (List.ofFn x12 ++ [Bool.true, Bool.false])).getD x11 Bool.false;     have x12 : (x5 → Bool) → Prop := fun (x12 : x5 → Bool) => ∀ (x13 x14 : x1), x3 x13 x14 → x12 (x6 x13 x14) = Bool.true;     have x13 : ℕ × ℕ → x5 → Bool := fun (x13 : ℕ × ℕ) (x14 : x5) => x11 x13.1 x14 || x11 x13.2 x14;     have x14 : Finset (ℕ × ℕ) → Prop := fun (x14 : Finset (ℕ × ℕ)) => ∀ (x15 : Finset x1), x8 x15 → ∃ x17 ∈ x14, ¬x13 x17 (x7 x15) = Bool.true;     ∀ (x15 : Finset (ℕ × ℕ)), (2 : ℕ) ≤ x15.card → x9.size + (2 : ℕ) * x15.card ≤ (64 : ℕ) → (∀ x18 ∈ x15, x12 (x13 x18) ∧ ¬x12 (x11 x18.1) ∧ ¬x12 (x11 x18.2)) → x14 x15 → (20 : ℕ) ≤ {x20 ∈ Finset.range x9.size | (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x20).op.eval [Bool.false, Bool.true] = Bool.true}.card → x15.card ≤ (22 : ℕ) → (∀ x22 ∈ x15, ¬x14 (x15.erase x22)) → False :=
  fun x9 hmono x15 hcard2 hsz64 hcov hx14 hor20 hcard22 hmin15 => by
    obtain ⟨C', hC'_mono, hC'_RB, hC'_sz, hC'_wires, hC'_or⟩ := hNorm28 x9 hmono
    have hC'_same : ∀ (f : Fin 26 → Bool),
        C'.wires (List.ofFn f ++ [Bool.true, Bool.false]) =
        x9.wires (List.ofFn f ++ [Bool.true, Bool.false]) := by
      intro f
      exact hC'_wires _ (by rw [List.length_append, List.length_ofFn, List.length_cons, List.length_singleton])
    have hor20' : (20 : ℕ) ≤ {x20 ∈ Finset.range C'.size | (PEqualNP.MetaComplexity.NestedCover.gateAt C' x20).op.eval [Bool.false, Bool.true] = Bool.true}.card := by
      refine le_trans hor20 (Finset.card_le_card ?_)
      intro j hj
      rw [Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨hC'_sz ▸ hj.1, hC'_or j hj.1 hj.2⟩
    refine hRed7870 C' hC'_mono hC'_RB x15 hcard2 (by rw [hC'_sz]; exact hsz64) ?_ ?_ hor20' hcard22 ?_
    · intro x18 hx18
      have h0 := hcov x18 hx18
      refine ⟨?_, ?_, ?_⟩
      · intro a b hab; simpa only [hC'_same] using h0.1 a b hab
      · intro hbad; exact h0.2.1 (fun a b hab => by simpa only [hC'_same] using hbad a b hab)
      · intro hbad; exact h0.2.2 (fun a b hab => by simpa only [hC'_same] using hbad a b hab)
    · intro s hs
      obtain ⟨e, he, hfalse⟩ := hx14 s hs
      exact ⟨e, he, by simpa only [hC'_same] using hfalse⟩
    · intro e he hsub
      apply hmin15 e he
      intro s hs
      obtain ⟨e', he', hfalse⟩ := hsub s hs
      exact ⟨e', he', by simpa only [hC'_same] using hfalse⟩
