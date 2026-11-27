import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18061_1
    (hCompile :
      ∀ (prog : List (Bool × ℕ × ℕ)),
        prog.length = (62 : ℕ) →
        ∃ (x3 : Fin (62 : ℕ) → Bool × Fin (89 : ℕ) × Fin (89 : ℕ)),
          (∀ (x4 : Fin (62 : ℕ)), Max.max ↑(x3 x4).2.1 ↑(x3 x4).2.2 < (27 : ℕ) + ↑x4) ∧
          ∀ (init : List Bool),
            init.length = (27 : ℕ) →
            (List.foldl
              (fun (x6 : List Bool) (x7 : Bool × Fin (89 : ℕ) × Fin (89 : ℕ)) =>
                have x8 : Bool := x6.getD (↑x7.2.1) Bool.false;
                have x9 : Bool := x6.getD (↑x7.2.2) Bool.false;
                x6 ++ [bif x7.1 then x8 || x9 else x8 && x9])
              init (List.ofFn x3)).getD (88 : ℕ) Bool.false =
            (List.foldl
              (fun (x6 : List Bool) (x7 : Bool × ℕ × ℕ) =>
                have x8 : Bool := x6.getD (x7.2.1 % x6.length) Bool.false;
                have x9 : Bool := x6.getD (x7.2.2 % x6.length) Bool.false;
                x6 ++ [bif x7.1 then x8 || x9 else x8 && x9])
              init prog).getD (88 : ℕ) Bool.false)
    (hProg :
      ∃ (x2 : Fin (4 : ℕ)) (prog : List (Bool × ℕ × ℕ)),
        prog.length = (62 : ℕ) ∧
        have x4 : Fin (26 : ℕ) := if ↑x2 = (1 : ℕ) then (1 : Fin (26 : ℕ)) else if ↑x2 = (3 : ℕ) then (14 : Fin (26 : ℕ)) else (13 : Fin (26 : ℕ));
        have x5 : (Fin (26 : ℕ) → Bool) → Bool := fun (x5 : Fin (26 : ℕ) → Bool) =>
          (List.foldl
            (fun (x6 : List Bool) (x7 : Bool × ℕ × ℕ) =>
              have x8 : Bool := x6.getD (x7.2.1 % x6.length) Bool.false;
              have x9 : Bool := x6.getD (x7.2.2 % x6.length) Bool.false;
              x6 ++ [bif x7.1 then x8 || x9 else x8 && x9])
            (List.ofFn fun (x6 : Fin ((26 : ℕ) + (1 : ℕ))) =>
              Fin.lastCases
                (if ↑x2 = (0 : ℕ) then x5 (0 : Fin (26 : ℕ)) && x5 x4 else x5 (0 : Fin (26 : ℕ)) || x5 x4)
                x5 x6)
            prog).getD (88 : ℕ) Bool.false;
        (∀ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))],
          (x5 fun (x9 : Fin (26 : ℕ)) => Decidable.decide (x9 = Fin.castAdd (13 : ℕ) (x7 + x8) ∨ x9 = Fin.natAdd (13 : ℕ) x7)) = Bool.true) ∧
        ∀ x6 ∈ [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))],
          ∀ x8 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))],
            ∀ (x10 : Fin (13 : ℕ)) (x11 : Bool),
              have x12 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x12 x13 : ℕ) (x14 : Fin (13 : ℕ)) =>
                if x11 = Bool.true then x13.testBit ↑(-(x8 * x14 + x10)) else x12.testBit ↑(x8 * x14 + x10);
              x5 (Fin.append (x12 x6.1 x6.2) (x12 x6.2 x6.1)) = Bool.false) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∃ (x2 : Fin (4 : ℕ)) (x3 : Fin (62 : ℕ) → Bool × Fin (89 : ℕ) × Fin (89 : ℕ)),   (∀ (x4 : Fin (62 : ℕ)), Max.max ↑(x3 x4).2.1 ↑(x3 x4).2.2 < (27 : ℕ) + ↑x4) ∧     have x4 : Fin (26 : ℕ) := if ↑x2 = (1 : ℕ) then (1 : Fin (26 : ℕ)) else if ↑x2 = (3 : ℕ) then (14 : Fin (26 : ℕ)) else (13 : Fin (26 : ℕ));     have x5 : (Fin (26 : ℕ) → Bool) → Bool := fun (x5 : Fin (26 : ℕ) → Bool) =>       (List.foldl             (fun (x6 : List Bool) (x7 : Bool × Fin (89 : ℕ) × Fin (89 : ℕ)) =>               have x8 : Bool := x6.getD (↑x7.2.1) Bool.false;               have x9 : Bool := x6.getD (↑x7.2.2) Bool.false;               x6 ++ [bif x7.1 then x8 || x9 else x8 && x9])             (List.ofFn fun (x6 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (if ↑x2 = (0 : ℕ) then x5 (0 : Fin (26 : ℕ)) && x5 x4 else x5 (0 : Fin (26 : ℕ)) || x5 x4) x5 x6) (List.ofFn x3)).getD         (88 : ℕ) Bool.false;     (∀ (x6 x7 : Fin (13 : ℕ)), (∃ x8 ∈ x1, x6 = x7 + x8) → (x5 fun (x9 : Fin (26 : ℕ)) => Decidable.decide (x9 = Fin.castAdd (13 : ℕ) x6 ∨ x9 = Fin.natAdd (13 : ℕ) x7)) = Bool.true) ∧       ∀ x6 ∈ [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))],         ∀ x8 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))],           ∀ (x10 : Fin (13 : ℕ)) (x11 : Bool),             have x12 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x12 x13 : ℕ) (x14 : Fin (13 : ℕ)) => if x11 = Bool.true then x13.testBit ↑(-(x8 * x14 + x10)) else x12.testBit ↑(x8 * x14 + x10);             x5 (Fin.append (x12 x6.1 x6.2) (x12 x6.2 x6.1)) = Bool.false) :=
  Exists.elim hProg fun x2 h1 =>
    Exists.elim h1 fun prog hP =>
      Exists.elim (hCompile prog hP.1) fun x3 hC =>
        ⟨x2, x3, hC.1,
          fun x6 x7 hEdge =>
            Exists.elim hEdge fun x8 hx8 =>
              hx8.2.symm ▸ (hC.2 _ (List.length_ofFn ..)).trans
                (hP.2.1 x7 x8
                  (Or.elim (Finset.mem_insert.mp hx8.1)
                    (fun h => h ▸ List.mem_cons_self ..)
                    (fun h1 => Or.elim (Finset.mem_insert.mp h1)
                      (fun h => h ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
                      (fun h2 => Or.elim (Finset.mem_insert.mp h2)
                        (fun h => h ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
                        (fun h3 => (Finset.mem_singleton.mp h3) ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))))),
          fun x6 hx6 x8 hx8 x10 x11 =>
            (hC.2 _ (List.length_ofFn ..)).trans (hP.2.2 x6 hx6 x8 hx8 x10 x11)⟩
