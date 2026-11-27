import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18500_2
    (hSetDAG :
      let x1 : Type := Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))
      have x3 : Fin (25 : ℕ) → Set x1 := fun (x3 : Fin (25 : ℕ)) => {x4 : x1 | if ↑x3 < (12 : ℕ) then Fin.ofNat (13 : ℕ) (↑x3 + (1 : ℕ)) ∈ x4.1 else Fin.ofNat (13 : ℕ) (↑x3 - (12 : ℕ)) ∈ x4.2};
      have x4 : Set x1 := {x4 : x1 | ∃ x5 ∈ x4.1, ∃ x6 ∈ x4.2, (([(0 : ℕ), (4357 : ℕ), (6274 : ℕ), (3137 : ℕ), (5664 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (177 : ℕ), (4184 : ℕ), (2092 : ℕ), (1046 : ℕ)] : List ℕ).getD x5.val (0 : ℕ)).testBit x6.val = Bool.true};
      have x5 : Set x1 := {x5 : x1 | ∃ x6 ∈ x5.2, (523 : ℕ).testBit x6.val = Bool.true};
      ∃ (x6 : List (Bool × ℕ × ℕ)) (x7 : ℕ) (x8 : ℕ),
        have x9 : List (Set x1) := List.foldl (fun (x9 : List (Set x1)) (x10 : Bool × ℕ × ℕ) => x9.concat (if x10.1 = Bool.true then x9.getD x10.2.1 ∅ ∩ x9.getD x10.2.2 ∅ else x9.getD x10.2.1 ∅ ∪ x9.getD x10.2.2 ∅)) (List.ofFn x3) x6;
        x6.length ≤ (61 : ℕ) ∧ x7 < (25 : ℕ) + x6.length ∧ x8 < (25 : ℕ) + x6.length ∧ x9.getD x7 ∅ = x4 ∧ x5 \ x4 ⊆ x9.getD x8 ∅ ∧ x9.getD x8 ∅ ⊆ x5 ∪ x4)
    (hTableEquiv :
      (∀ (a b : Fin (13 : ℕ)),
        (([(0 : ℕ), (4357 : ℕ), (6274 : ℕ), (3137 : ℕ), (5664 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (177 : ℕ), (4184 : ℕ), (2092 : ℕ), (1046 : ℕ)] : List ℕ).getD a.val (0 : ℕ)).testBit b.val = Bool.true ↔
          (a ≠ (0 : Fin (13 : ℕ)) ∧ (a + b).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])) ∧
      (∀ (b : Fin (13 : ℕ)),
        (523 : ℕ).testBit b.val = Bool.true ↔ b.val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])) :
    (let x1 : Type := Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)); have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x3 : Fin (25 : ℕ) → Set x1 := fun (x3 : Fin (25 : ℕ)) => {x4 : x1 | if ↑x3 < (12 : ℕ) then Fin.ofNat (13 : ℕ) (↑x3 + (1 : ℕ)) ∈ x4.1 else Fin.ofNat (13 : ℕ) (↑x3 - (12 : ℕ)) ∈ x4.2}; have x4 : Set x1 := {x4 : x1 | ∃ x5 ∈ x4.1, x5 ≠ (0 : Fin (13 : ℕ)) ∧ ∃ x6 ∈ x4.2, x5 + x6 ∈ x2}; have x5 : Set x1 := {x5 : x1 | ∃ x6 ∈ x5.2, x6 ∈ x2}; ∃ (x6 : List (Bool × ℕ × ℕ)) (x7 : ℕ) (x8 : ℕ),   have x9 : List (Set x1) := List.foldl (fun (x9 : List (Set x1)) (x10 : Bool × ℕ × ℕ) => x9.concat (if x10.1 = Bool.true then x9.getD x10.2.1 ∅ ∩ x9.getD x10.2.2 ∅ else x9.getD x10.2.1 ∅ ∪ x9.getD x10.2.2 ∅)) (List.ofFn x3) x6;   x6.length ≤ (61 : ℕ) ∧ x7 < (25 : ℕ) + x6.length ∧ x8 < (25 : ℕ) + x6.length ∧ x9.getD x7 ∅ = x4 ∧ x5 \ x4 ⊆ x9.getD x8 ∅ ∧ x9.getD x8 ∅ ⊆ x5 ∪ x4) := by
  have hMem : ∀ s : Fin (13 : ℕ), s.val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ↔ s ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) := by decide
  intro x1 x2 x3 x4 x5
  have hx4 : ({p : x1 | ∃ a ∈ p.1, ∃ b ∈ p.2, (([(0 : ℕ), (4357 : ℕ), (6274 : ℕ), (3137 : ℕ), (5664 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (177 : ℕ), (4184 : ℕ), (2092 : ℕ), (1046 : ℕ)] : List ℕ).getD a.val (0 : ℕ)).testBit b.val = Bool.true} : Set x1) = x4 := by
    refine Set.ext (fun p => ?_)
    refine exists_congr (fun a => and_congr_right (fun _ => ?_))
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨b, hb, hbit⟩ := h
      have h1 := (hTableEquiv.1 a b).mp hbit
      exact ⟨h1.1, b, hb, (hMem (a + b)).mp h1.2⟩
    · obtain ⟨ha0, b, hb, hmem⟩ := h
      exact ⟨b, hb, (hTableEquiv.1 a b).mpr ⟨ha0, (hMem (a + b)).mpr hmem⟩⟩
  have hx5 : ({p : x1 | ∃ b ∈ p.2, (523 : ℕ).testBit b.val = Bool.true} : Set x1) = x5 := by
    refine Set.ext (fun p => exists_congr (fun b => and_congr_right (fun _ => (hTableEquiv.2 b).trans (hMem b))))
  obtain ⟨x6, x7, x8, hLen, h7, h8, hEq4, hSub1, hSub2⟩ := hSetDAG
  rw [hx4] at hEq4 hSub1 hSub2
  rw [hx5] at hSub1 hSub2
  exact ⟨x6, x7, x8, hLen, h7, h8, hEq4, hSub1, hSub2⟩
