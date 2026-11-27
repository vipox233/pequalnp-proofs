import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17237_1
    (hCircuit :
      have E : List ℕ :=
        [(38 : ℕ), (44 : ℕ), (48 : ℕ), (49 : ℕ), (92 : ℕ), (96 : ℕ), (97 : ℕ), (99 : ℕ),
         (116 : ℕ), (120 : ℕ), (121 : ℕ), (123 : ℕ), (140 : ℕ), (144 : ℕ), (145 : ℕ), (147 : ℕ),
         (164 : ℕ), (168 : ℕ), (169 : ℕ), (171 : ℕ), (188 : ℕ), (192 : ℕ), (193 : ℕ), (195 : ℕ),
         (240 : ℕ), (241 : ℕ), (243 : ℕ), (249 : ℕ), (264 : ℕ), (265 : ℕ), (267 : ℕ), (273 : ℕ),
         (288 : ℕ), (289 : ℕ), (291 : ℕ), (297 : ℕ)];
      have W : Finset (Fin (25 : ℕ)) := {(13 : Fin (25 : ℕ)), (15 : Fin (25 : ℕ)), (21 : Fin (25 : ℕ))};
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ),
        PEqualNP.MetaComplexity.Monotone2 C ∧
        C.size ≤ (45 : ℕ) ∧
        C.output < (25 : ℕ) + C.size ∧
        w < (25 : ℕ) + C.size ∧
        have val : Finset (Fin (25 : ℕ)) → ℕ → Bool := fun S k =>
          (C.wires (List.ofFn fun (i : Fin (25 : ℕ)) => Decidable.decide (i ∈ S))).getD k Bool.false;
        (∀ (a b : Fin (25 : ℕ)), (25 : ℕ) * (a : ℕ) + (b : ℕ) ∈ E → val {a, b} C.output = Bool.true) ∧
        (∀ (S : Finset (Fin (25 : ℕ))), (∀ a ∈ S, ∀ b ∈ S, (25 : ℕ) * (a : ℕ) + (b : ℕ) ∉ E) → val S C.output = Bool.false) ∧
        (∀ z ∈ W, val {z} w = Bool.true) ∧
        (∀ (S : Finset (Fin (25 : ℕ))), (∀ z ∈ W, z ∉ S) → (∀ a ∈ S, ∀ b ∈ S, (25 : ℕ) * (a : ℕ) + (b : ℕ) ∉ E) → val S w = Bool.false))
    (hEquiv :
      ∀ (a b : Fin (25 : ℕ)),
        ((a : ℕ) < (12 : ℕ) ∧ (12 : ℕ) ≤ (b : ℕ) ∧
          ((a : ℕ) + (b : ℕ) + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
          (a : ℕ) ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)]) ↔
        (25 : ℕ) * (a : ℕ) + (b : ℕ) ∈
          [(38 : ℕ), (44 : ℕ), (48 : ℕ), (49 : ℕ), (92 : ℕ), (96 : ℕ), (97 : ℕ), (99 : ℕ),
           (116 : ℕ), (120 : ℕ), (121 : ℕ), (123 : ℕ), (140 : ℕ), (144 : ℕ), (145 : ℕ), (147 : ℕ),
           (164 : ℕ), (168 : ℕ), (169 : ℕ), (171 : ℕ), (188 : ℕ), (192 : ℕ), (193 : ℕ), (195 : ℕ),
           (240 : ℕ), (241 : ℕ), (243 : ℕ), (249 : ℕ), (264 : ℕ), (265 : ℕ), (267 : ℕ), (273 : ℕ),
           (288 : ℕ), (289 : ℕ), (291 : ℕ), (297 : ℕ)]) :
    (have x1 : Fin (25 : ℕ) → Fin (25 : ℕ) → Prop := fun (x1 x2 : Fin (25 : ℕ)) => ↑x1 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x2 ∧ (↑x1 + ↑x2 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x1 ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)]; have x2 : Finset (Fin (25 : ℕ)) := {(13 : Fin (25 : ℕ)), (15 : Fin (25 : ℕ)), (21 : Fin (25 : ℕ))}; have x3 : Finset (Fin (25 : ℕ)) → Prop := fun (x3 : Finset (Fin (25 : ℕ))) => ¬∃ x4 ∈ x3, ∃ x5 ∈ x3, x1 x4 x5; have x4 : Finset (Fin (25 : ℕ)) → Finset (Fin (25 : ℕ)) → Prop := fun (x4 x5 : Finset (Fin (25 : ℕ))) => x5 ⊆ x4 ∧ x3 x5 ∧ ∀ x6 ∈ x4, x6 ∉ x5 → ¬x3 (Insert.insert x6 x5); ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x5 ∧     x5.size ≤ (45 : ℕ) ∧       x5.output < (25 : ℕ) + x5.size ∧         x6 < (25 : ℕ) + x5.size ∧           have x7 : Finset (Fin (25 : ℕ)) → ℕ → Bool := fun (x7 : Finset (Fin (25 : ℕ))) (x8 : ℕ) => (x5.wires (List.ofFn fun (x9 : Fin (25 : ℕ)) => Decidable.decide (x9 ∈ x7))).getD x8 Bool.false;           (∀ (x8 x9 : Fin (25 : ℕ)), x1 x8 x9 → x7 {x8, x9} x5.output = Bool.true) ∧ (∀ (x8 : Finset (Fin (25 : ℕ))), x4 Finset.univ x8 → x7 x8 x5.output = Bool.false) ∧ (∀ x8 ∈ x2, x7 {x8} x6 = Bool.true) ∧ ∀ (x8 : Finset (Fin (25 : ℕ))), x4 (Finset.univ \ x2) x8 → x7 x8 x6 = Bool.false) := by
  obtain ⟨C, w, hMono, hSize, hOut, hW, hPos, hNeg, hWPos, hWNeg⟩ := hCircuit
  refine ⟨C, w, hMono, hSize, hOut, hW, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact hPos a b ((hEquiv a b).mp hab)
  · intro S hS
    apply hNeg S
    intro a ha b hb hmem
    exact hS.2.1 ⟨a, ha, b, hb, (hEquiv a b).mpr hmem⟩
  · intro z hz
    exact hWPos z hz
  · intro S hS
    apply hWNeg S
    · intro z hz hzS
      exact (Finset.mem_sdiff.mp (hS.1 hzS)).2 hz
    · intro a ha b hb hmem
      exact hS.2.1 ⟨a, ha, b, hb, (hEquiv a b).mpr hmem⟩
