import PEqualNP.Defs

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_17621_2
    (hFirstAnd :
      have x1 : List ℕ := List.range (13 : ℕ);
      have x2 : ℕ → ℕ → Bool := fun (x2 x3 : ℕ) => [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains ((x2 + (13 : ℕ) - x3) % (13 : ℕ));
      have x3 : List ℕ → ℕ := fun (x3 : List ℕ) => List.foldr (fun (x4 x5 : ℕ) => (2 : ℕ) ^ x4 ||| x5) (0 : ℕ) x3;
      have x4 : List ℕ → List ℕ → ℕ := fun (x4 x5 : List ℕ) => x3 x4 ||| x3 x5 <<< (13 : ℕ);
      have x5 : List ℕ := List.flatMap (fun (x5 : ℕ) => List.map (fun (x6 : ℕ) => x4 [x6] [x5]) (List.filter (fun (x6 : ℕ) => x2 x6 x5) x1)) x1;
      have x6 : List ℕ := List.flatMap (fun (x6 : ℕ) => List.flatMap (fun (x7 : List ℕ) => [x4 x7 (List.filter (fun (x8 : ℕ) => x7.all fun (x9 : ℕ) => !x2 x9 x8) x1), x4 (List.filter (fun (x8 : ℕ) => x7.all fun (x9 : ℕ) => !x2 x8 x9) x1) x7]) (List.sublistsLen x6 x1)) (List.range (4 : ℕ));
      have x7 : List (ℕ × Bool) := List.map (fun (x7 : ℕ) => (x7, Bool.true)) x5 ++ List.map (fun (x7 : ℕ) => (x7, Bool.false)) x6;
      have x8 : (ℕ × Bool → Bool) → ℕ := fun (x8 : ℕ × Bool → Bool) => List.foldr Nat.bit (0 : ℕ) (List.map x8 x7);
      have x9 : List ℕ := List.ofFn fun (x9 : Fin (26 : ℕ)) => x8 fun (x10 : ℕ × Bool) => x10.1.testBit ↑x9;
      have x10 : List ℕ → Bool × ℕ × ℕ → List ℕ := fun (x10 : List ℕ) (x11 : Bool × ℕ × ℕ) =>
        have x12 : ℕ := x10.getD x11.2.1 (0 : ℕ);
        have x13 : ℕ := x10.getD x11.2.2 (0 : ℕ);
        x10 ++ [if x11.1 = Bool.true then x12 ||| x13 else x12 &&& x13];
      ∀ (x12 : List (Bool × ℕ × ℕ)),
        x12.length ≤ (61 : ℕ) →
        (∀ (x15 : Fin x12.length),
          have x16 : Bool × ℕ × ℕ := x12.getD ↑x15 (Bool.false, (0 : ℕ), (0 : ℕ));
          x16.2.1 ≠ x16.2.2 ∧ Max.max x16.2.1 x16.2.2 < (27 : ℕ) + ↑x15) →
        (∀ (x16 x17 : Fin (26 : ℕ)), x16 ≠ x17 → ∃ x19 ∈ (Bool.false, (0 : ℕ), (13 : ℕ)) :: x12, (x19.2.1 = ↑x16 ∨ x19.2.2 = ↑x16) ∧ x19.2.1 ≠ ↑x17 ∧ x19.2.2 ≠ ↑x17) →
        x8 Prod.snd ∉ List.foldl x10 (x10 x9 (Bool.false, (0 : ℕ), (13 : ℕ))) x12)
    (hFirstOr :
      have x1 : List ℕ := List.range (13 : ℕ);
      have x2 : ℕ → ℕ → Bool := fun (x2 x3 : ℕ) => [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains ((x2 + (13 : ℕ) - x3) % (13 : ℕ));
      have x3 : List ℕ → ℕ := fun (x3 : List ℕ) => List.foldr (fun (x4 x5 : ℕ) => (2 : ℕ) ^ x4 ||| x5) (0 : ℕ) x3;
      have x4 : List ℕ → List ℕ → ℕ := fun (x4 x5 : List ℕ) => x3 x4 ||| x3 x5 <<< (13 : ℕ);
      have x5 : List ℕ := List.flatMap (fun (x5 : ℕ) => List.map (fun (x6 : ℕ) => x4 [x6] [x5]) (List.filter (fun (x6 : ℕ) => x2 x6 x5) x1)) x1;
      have x6 : List ℕ := List.flatMap (fun (x6 : ℕ) => List.flatMap (fun (x7 : List ℕ) => [x4 x7 (List.filter (fun (x8 : ℕ) => x7.all fun (x9 : ℕ) => !x2 x9 x8) x1), x4 (List.filter (fun (x8 : ℕ) => x7.all fun (x9 : ℕ) => !x2 x8 x9) x1) x7]) (List.sublistsLen x6 x1)) (List.range (4 : ℕ));
      have x7 : List (ℕ × Bool) := List.map (fun (x7 : ℕ) => (x7, Bool.true)) x5 ++ List.map (fun (x7 : ℕ) => (x7, Bool.false)) x6;
      have x8 : (ℕ × Bool → Bool) → ℕ := fun (x8 : ℕ × Bool → Bool) => List.foldr Nat.bit (0 : ℕ) (List.map x8 x7);
      have x9 : List ℕ := List.ofFn fun (x9 : Fin (26 : ℕ)) => x8 fun (x10 : ℕ × Bool) => x10.1.testBit ↑x9;
      have x10 : List ℕ → Bool × ℕ × ℕ → List ℕ := fun (x10 : List ℕ) (x11 : Bool × ℕ × ℕ) =>
        have x12 : ℕ := x10.getD x11.2.1 (0 : ℕ);
        have x13 : ℕ := x10.getD x11.2.2 (0 : ℕ);
        x10 ++ [if x11.1 = Bool.true then x12 ||| x13 else x12 &&& x13];
      ∀ (x11 : Bool × ℕ × ℕ) (x12 : List (Bool × ℕ × ℕ)),
        x11 ∈ [(Bool.true, (0 : ℕ), (1 : ℕ)), (Bool.true, (0 : ℕ), (13 : ℕ)), (Bool.true, (0 : ℕ), (14 : ℕ))] →
        x12.length ≤ (61 : ℕ) →
        (∀ (x15 : Fin x12.length),
          have x16 : Bool × ℕ × ℕ := x12.getD ↑x15 (Bool.false, (0 : ℕ), (0 : ℕ));
          x16.2.1 ≠ x16.2.2 ∧ Max.max x16.2.1 x16.2.2 < (27 : ℕ) + ↑x15) →
        (∀ (x16 x17 : Fin (26 : ℕ)), x16 ≠ x17 → ∃ x19 ∈ x11 :: x12, (x19.2.1 = ↑x16 ∨ x19.2.2 = ↑x16) ∧ x19.2.1 ≠ ↑x17 ∧ x19.2.2 ≠ ↑x17) →
        x8 Prod.snd ∉ List.foldl x10 (x10 x9 x11) x12) :
    (have x1 : List ℕ := List.range (13 : ℕ); have x2 : ℕ → ℕ → Bool := fun (x2 x3 : ℕ) => [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains ((x2 + (13 : ℕ) - x3) % (13 : ℕ)); have x3 : List ℕ → ℕ := fun (x3 : List ℕ) => List.foldr (fun (x4 x5 : ℕ) => (2 : ℕ) ^ x4 ||| x5) (0 : ℕ) x3; have x4 : List ℕ → List ℕ → ℕ := fun (x4 x5 : List ℕ) => x3 x4 ||| x3 x5 <<< (13 : ℕ); have x5 : List ℕ := List.flatMap (fun (x5 : ℕ) => List.map (fun (x6 : ℕ) => x4 [x6] [x5]) (List.filter (fun (x6 : ℕ) => x2 x6 x5) x1)) x1; have x6 : List ℕ := List.flatMap (fun (x6 : ℕ) => List.flatMap (fun (x7 : List ℕ) => [x4 x7 (List.filter (fun (x8 : ℕ) => x7.all fun (x9 : ℕ) => !x2 x9 x8) x1), x4 (List.filter (fun (x8 : ℕ) => x7.all fun (x9 : ℕ) => !x2 x8 x9) x1) x7]) (List.sublistsLen x6 x1)) (List.range (4 : ℕ)); have x7 : List (ℕ × Bool) := List.map (fun (x7 : ℕ) => (x7, Bool.true)) x5 ++ List.map (fun (x7 : ℕ) => (x7, Bool.false)) x6; have x8 : (ℕ × Bool → Bool) → ℕ := fun (x8 : ℕ × Bool → Bool) => List.foldr Nat.bit (0 : ℕ) (List.map x8 x7); have x9 : List ℕ := List.ofFn fun (x9 : Fin (26 : ℕ)) => x8 fun (x10 : ℕ × Bool) => x10.1.testBit ↑x9; have x10 : List ℕ → Bool × ℕ × ℕ → List ℕ := fun (x10 : List ℕ) (x11 : Bool × ℕ × ℕ) =>   have x12 : ℕ := x10.getD x11.2.1 (0 : ℕ);   have x13 : ℕ := x10.getD x11.2.2 (0 : ℕ);   x10 ++ [if x11.1 = Bool.true then x12 ||| x13 else x12 &&& x13]; ∀ (x11 : Bool × ℕ × ℕ) (x12 : List (Bool × ℕ × ℕ)),   x11 ∈ [(Bool.false, (0 : ℕ), (13 : ℕ)), (Bool.true, (0 : ℕ), (1 : ℕ)), (Bool.true, (0 : ℕ), (13 : ℕ)), (Bool.true, (0 : ℕ), (14 : ℕ))] →     x12.length ≤ (61 : ℕ) →       (∀ (x15 : Fin x12.length),           have x16 : Bool × ℕ × ℕ := x12.getD ↑x15 (Bool.false, (0 : ℕ), (0 : ℕ));           x16.2.1 ≠ x16.2.2 ∧ Max.max x16.2.1 x16.2.2 < (27 : ℕ) + ↑x15) →         (∀ (x16 x17 : Fin (26 : ℕ)), x16 ≠ x17 → ∃ x19 ∈ x11 :: x12, (x19.2.1 = ↑x16 ∨ x19.2.2 = ↑x16) ∧ x19.2.1 ≠ ↑x17 ∧ x19.2.2 ≠ ↑x17) → x8 Prod.snd ∉ List.foldl x10 (x10 x9 x11) x12) := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 hMem hLen hValid hSep
  exact Or.elim (List.mem_cons.mp hMem)
    (fun hEq => by subst hEq; exact hFirstAnd x12 hLen hValid hSep)
    (fun hTail => hFirstOr x11 x12 hTail hLen hValid hSep)
