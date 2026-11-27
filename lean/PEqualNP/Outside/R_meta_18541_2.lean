import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18541_2
    (hSingerEquiv :
      (∀ (q : Fin 13), q ∈ PEqualNP.HeptadCover.singerLines3 0 ↔ q ∈ ([0, 1, 3, 9] : List (Fin 13))) ∧
      ∀ (x : Fin 26 → Bool),
        (([2, 4, 5, 6, 7, 8, 10, 11, 12] : List (Fin 13)).any
            (fun p => x (Fin.castAdd 13 p) && ([0, 1, 3, 9] : List (Fin 13)).any (fun d => x (Fin.natAdd 13 (p - d)))) = true ↔
          ∃ (p l : Fin 13), p ∉ PEqualNP.HeptadCover.singerLines3 0 ∧ l ≠ 0 ∧ p ∈ PEqualNP.HeptadCover.singerLines3 l ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) ∧
        ∀ q ∈ ([0, 1, 3, 9] : List (Fin 13)),
          (([0, 1, 3, 9] : List (Fin 13)).any
            (fun d => decide (d ≠ q) && x (Fin.natAdd 13 (q - d))) = true ↔
          ∃ (l : Fin 13), l ≠ 0 ∧ q ∈ PEqualNP.HeptadCover.singerLines3 l ∧ x (Fin.natAdd 13 l) = true))
    (hAG23Circuit :
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (W : Fin 13 → ℕ),
        C.size ≤ 50 ∧ PEqualNP.TopForm.IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        C.output < 26 + C.size ∧
        (∀ q ∈ ([0, 1, 3, 9] : List (Fin 13)), W q < 26 + C.size ∧ W q ≠ q.1) ∧
        ∀ (x : Fin 26 → Bool),
          C.eval (List.ofFn x) =
            ([2, 4, 5, 6, 7, 8, 10, 11, 12] : List (Fin 13)).any
              (fun p => x (Fin.castAdd 13 p) && ([0, 1, 3, 9] : List (Fin 13)).any (fun d => x (Fin.natAdd 13 (p - d)))) ∧
          ∀ q ∈ ([0, 1, 3, 9] : List (Fin 13)),
            PEqualNP.BlindGate.wireValue C 26 x (W q) =
              ([0, 1, 3, 9] : List (Fin 13)).any (fun d => decide (d ≠ q) && x (Fin.natAdd 13 (q - d)))) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (13 : ℕ) → ℕ), x1.size ≤ (50 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧ (∀ x3 ∈ x1.gates, x3.inputs.Nodup) ∧ x1.output < (26 : ℕ) + x1.size ∧ (∀ x3 ∈ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)), x2 x3 < (26 : ℕ) + x1.size ∧ x2 x3 ≠ ↑x3) ∧ ∀ (x3 : Fin (26 : ℕ) → Bool), (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 ∉ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)) ∧ x5 ≠ (0 : Fin (13 : ℕ)) ∧ x4 ∈ PEqualNP.HeptadCover.singerLines3 x5 ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) ∧ ∀ x4 ∈ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)), PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x3 (x2 x4) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)), x6 ≠ (0 : Fin (13 : ℕ)) ∧ x4 ∈ PEqualNP.HeptadCover.singerLines3 x6 ∧ x3 (Fin.natAdd (13 : ℕ) x6) = Bool.true) :=
  Exists.elim hAG23Circuit fun C h1 =>
  Exists.elim h1 fun W h2 =>
    ⟨C, W, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1,
      (fun q hq => h2.2.2.2.2.1 q ((hSingerEquiv.1 q).mp hq)),
      (fun x =>
        ⟨Iff.trans ⟨fun h => Eq.trans (h2.2.2.2.2.2 x).1.symm h, fun h => Eq.trans (h2.2.2.2.2.2 x).1 h⟩ (hSingerEquiv.2 x).1,
         fun q hq =>
          let hqL := (hSingerEquiv.1 q).mp hq
          Iff.trans
            ⟨fun h => Eq.trans ((h2.2.2.2.2.2 x).2 q hqL).symm h,
             fun h => Eq.trans ((h2.2.2.2.2.2 x).2 q hqL) h⟩
            ((hSingerEquiv.2 x).2 q hqL)⟩)⟩
