import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17205_3
    (hMono :
      let ext : (Fin 17 → Bool) → List Bool := fun x =>
        List.ofFn x ++ [x 13 || x 14, x 13 || x 14 || x 9, x 15 || x 11, x 15 || x 11 || x 10, x 16 || x 12, x 16 || x 12 || x 8]
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
        ∀ (x y : Fin 17 → Bool), (∀ i : Fin 17, x i = true → y i = true) →
          C.eval (ext x) = true → C.eval (ext y) = true)
    (hCert :
      let ext : (Fin 17 → Bool) → List Bool := fun x =>
        List.ofFn x ++ [x 13 || x 14, x 13 || x 14 || x 9, x 15 || x 11, x 15 || x 11 || x 10, x 16 || x 12, x 16 || x 12 || x 8]
      let tgt : Fin 6 → Fin 4 → Fin 17 := fun a b =>
        Fin.ofNat 17 (if b.val = 0 then 6 + a.val / 3 else 8 + if a.val < 3 then 3 * a.val + (b.val - 1) else 3 * (b.val - 1) + (a.val - 3))
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 28 ∧ C.output < 23 + C.size ∧
        (∀ (a : Fin 6) (b : Fin 4), C.eval (ext (fun i : Fin 17 => decide (i = Fin.ofNat 17 a.val ∨ i = tgt a b))) = true) ∧
        (∀ (u : Fin 6 → Bool), C.eval (ext (fun i : Fin 17 => if h : i.val < 6 then u ⟨i.val, h⟩ else decide (∀ (a : Fin 6), u a = true → ∀ (b : Fin 4), i ≠ tgt a b))) = false)) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (28 : ℕ) ∧ x1.output < (23 : ℕ) + x1.size ∧ ∀ (x2 : Fin (17 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [x2 (13 : Fin (17 : ℕ)) || x2 (14 : Fin (17 : ℕ)), x2 (13 : Fin (17 : ℕ)) || x2 (14 : Fin (17 : ℕ)) || x2 (9 : Fin (17 : ℕ)), x2 (15 : Fin (17 : ℕ)) || x2 (11 : Fin (17 : ℕ)), x2 (15 : Fin (17 : ℕ)) || x2 (11 : Fin (17 : ℕ)) || x2 (10 : Fin (17 : ℕ)), x2 (16 : Fin (17 : ℕ)) || x2 (12 : Fin (17 : ℕ)), x2 (16 : Fin (17 : ℕ)) || x2 (12 : Fin (17 : ℕ)) || x2 (8 : Fin (17 : ℕ))]) = Bool.true ↔ ∃ (x3 : Fin (6 : ℕ)) (x4 : Fin (4 : ℕ)), x2 (Fin.ofNat (17 : ℕ) ↑x3) = Bool.true ∧ x2 (Fin.ofNat (17 : ℕ) (if ↑x4 = (0 : ℕ) then (6 : ℕ) + ↑x3 / (3 : ℕ) else (8 : ℕ) + if ↑x3 < (3 : ℕ) then (3 : ℕ) * ↑x3 + (↑x4 - (1 : ℕ)) else (3 : ℕ) * (↑x4 - (1 : ℕ)) + (↑x3 - (3 : ℕ)))) = Bool.true) := by
  dsimp only at hMono hCert
  obtain ⟨C, hM, hSz, hOut, hPos, hNeg⟩ := hCert
  refine ⟨C, hM, hSz, hOut, ?_⟩
  intro x2
  constructor
  · intro hEv
    refine Classical.byContradiction fun hNo => ?_
    let u : Fin 6 → Bool := fun a => x2 (Fin.ofNat 17 a.val)
    let y : Fin 17 → Bool := fun i =>
      if h : i.val < 6 then u ⟨i.val, h⟩
      else decide (∀ (a : Fin 6), u a = true → ∀ (b : Fin 4), i ≠ Fin.ofNat 17 (if b.val = 0 then 6 + a.val / 3 else 8 + if a.val < 3 then 3 * a.val + (b.val - 1) else 3 * (b.val - 1) + (a.val - 3)))
    have hle : ∀ i : Fin 17, x2 i = true → y i = true := by
      intro i hi
      dsimp only [y]
      split
      · rename_i hlt
        dsimp only [u]
        have heq : Fin.ofNat 17 (⟨i.val, hlt⟩ : Fin 6).val = i :=
          Fin.ext (Nat.mod_eq_of_lt i.isLt)
        rw [heq]
        exact hi
      · rw [decide_eq_true_eq]
        intro a hua b hib
        apply hNo
        refine ⟨a, b, hua, ?_⟩
        rw [← hib]
        exact hi
    have hTrue : C.eval (List.ofFn y ++ [y 13 || y 14, y 13 || y 14 || y 9, y 15 || y 11, y 15 || y 11 || y 10, y 16 || y 12, y 16 || y 12 || y 8]) = true :=
      hMono C hM x2 y hle hEv
    have hFalse : C.eval (List.ofFn y ++ [y 13 || y 14, y 13 || y 14 || y 9, y 15 || y 11, y 15 || y 11 || y 10, y 16 || y 12, y 16 || y 12 || y 8]) = false :=
      hNeg u
    rw [hTrue] at hFalse
    cases hFalse
  · intro hEx
    obtain ⟨a, b, ha, hb⟩ := hEx
    let z : Fin 17 → Bool := fun i =>
      decide (i = Fin.ofNat 17 a.val ∨ i = Fin.ofNat 17 (if b.val = 0 then 6 + a.val / 3 else 8 + if a.val < 3 then 3 * a.val + (b.val - 1) else 3 * (b.val - 1) + (a.val - 3)))
    have hle : ∀ i : Fin 17, z i = true → x2 i = true := by
      intro i hi
      dsimp only [z] at hi
      rw [decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
    exact hMono C hM z x2 hle (hPos a b)
