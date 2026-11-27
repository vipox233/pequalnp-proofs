import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7782_2
    (hSetDAG :
      have x1 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := List.map (fun (x1 : (Fin (26 : ℕ) → Bool) → Bool) (x2 : Bool) => {x3 : Fin (26 : ℕ) → Bool | x1 x3 = x2}) ((List.ofFn fun (x1 : Fin (26 : ℕ)) (x2 : Fin (26 : ℕ) → Bool) => x2 x1) ++ [fun (x1 : Fin (26 : ℕ) → Bool) => x1 (0 : Fin (26 : ℕ)) || x1 (1 : Fin (26 : ℕ))]);
      have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (([(0 : ℕ), (0 : ℕ), (6274 : ℕ), (0 : ℕ), (5664 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (0 : ℕ), (4184 : ℕ), (2092 : ℕ), (1046 : ℕ)] : List ℕ).getD x4.val (0 : ℕ)).testBit x3.val = Bool.true ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true;
      ∃ (x3 : List (Bool → Set (Fin (26 : ℕ) → Bool))) (x4 : Bool → Set (Fin (26 : ℕ) → Bool)),
        x3.length ≤ (43 : ℕ) ∧
        x4 ∈ x1 ++ x3 ∧
        (∀ (x5 : Fin x3.length),
          have x6 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := x1 ++ List.take (↑x5) x3;
          ∃ x7 ∈ x6, ∃ x8 ∈ x6, ∃ (x9 : Bool), ∀ (x10 : Bool), x3.get x5 x10 ⊆ if x10 = x9 then x7 x10 ∪ x8 x10 else x7 x10 ∩ x8 x10) ∧
        ∀ (x5 : Fin (26 : ℕ) → Bool), (x2 x5 → x5 ∈ x4 Bool.true) ∧ (¬x2 x5 → x5 ∈ x4 Bool.false))
    (hTableEquiv :
      ∀ (x3 x4 : Fin (13 : ℕ)),
        (([(0 : ℕ), (0 : ℕ), (6274 : ℕ), (0 : ℕ), (5664 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (0 : ℕ), (4184 : ℕ), (2092 : ℕ), (1046 : ℕ)] : List ℕ).getD x4.val (0 : ℕ)).testBit x3.val = Bool.true ↔
          (↑x4 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ (↑x3 + ↑x4) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])) :
    (have x1 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := List.map (fun (x1 : (Fin (26 : ℕ) → Bool) → Bool) (x2 : Bool) => {x3 : Fin (26 : ℕ) → Bool | x1 x3 = x2}) ((List.ofFn fun (x1 : Fin (26 : ℕ)) (x2 : Fin (26 : ℕ) → Bool) => x2 x1) ++ [fun (x1 : Fin (26 : ℕ) → Bool) => x1 (0 : Fin (26 : ℕ)) || x1 (1 : Fin (26 : ℕ))]); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), ↑x4 ∉ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ (↑x3 + ↑x4) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∃ (x3 : List (Bool → Set (Fin (26 : ℕ) → Bool))) (x4 : Bool → Set (Fin (26 : ℕ) → Bool)),   x3.length ≤ (43 : ℕ) ∧     x4 ∈ x1 ++ x3 ∧       (∀ (x5 : Fin x3.length),           have x6 : List (Bool → Set (Fin (26 : ℕ) → Bool)) := x1 ++ List.take (↑x5) x3;           ∃ x7 ∈ x6, ∃ x8 ∈ x6, ∃ (x9 : Bool), ∀ (x10 : Bool), x3.get x5 x10 ⊆ if x10 = x9 then x7 x10 ∪ x8 x10 else x7 x10 ∩ x8 x10) ∧         ∀ (x5 : Fin (26 : ℕ) → Bool), (x2 x5 → x5 ∈ x4 Bool.true) ∧ (¬x2 x5 → x5 ∈ x4 Bool.false)) := by
  intro x1 x2
  obtain ⟨x3, x4, hLen, hMem, hStep, hAcc⟩ := hSetDAG
  refine ⟨x3, x4, hLen, hMem, hStep, fun x5 => ?_⟩
  have hEq : (∃ (a b : Fin (13 : ℕ)),
      (([(0 : ℕ), (0 : ℕ), (6274 : ℕ), (0 : ℕ), (5664 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (0 : ℕ), (4184 : ℕ), (2092 : ℕ), (1046 : ℕ)] : List ℕ).getD b.val (0 : ℕ)).testBit a.val = Bool.true ∧
      x5 (Fin.castAdd (13 : ℕ) a) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) b) = Bool.true) ↔ x2 x5 :=
    exists_congr (fun a => exists_congr (fun b => Iff.trans (and_congr_left' (hTableEquiv a b)) and_assoc))
  exact ⟨fun h => (hAcc x5).1 (hEq.mpr h), fun hn => (hAcc x5).2 (fun h => hn (hEq.mp h))⟩
