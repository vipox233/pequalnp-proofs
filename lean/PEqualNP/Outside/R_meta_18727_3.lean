import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18727_3
    (hCompileAO2 :
      ∀ (prog : List (Bool × ℕ × ℕ)) (out : ℕ),
        (∀ i < prog.length,
          (prog.getD i (Bool.false, (0 : ℕ), (0 : ℕ))).2.1 < (prog.getD i (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 ∧
          (prog.getD i (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 < (27 : ℕ) + i) →
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
          C.size = prog.length ∧
          C.output = out ∧
          PEqualNP.TopForm.IsAO2 (27 : ℕ) C ∧
          (∀ g ∈ C.gates, g.inputs.Nodup) ∧
          ∀ (w : List Bool),
            C.eval w =
              (List.foldl (fun (acc : List Bool) (g : Bool × ℕ × ℕ) =>
                acc ++ [if g.1 = Bool.true then acc.getD g.2.1 Bool.false && acc.getD g.2.2 Bool.false
                      else acc.getD g.2.1 Bool.false || acc.getD g.2.2 Bool.false])
                w prog).getD out Bool.false)
    (hProg18727 :
      have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x2 x3 : Fin (13 : ℕ)) (x4 : Fin (26 : ℕ)) => Decidable.decide (x4 = Fin.castAdd (13 : ℕ) x2 ∨ x4 = Fin.natAdd (13 : ℕ) x3);
      have x3 : (Fin (26 : ℕ) → Bool) → List Bool := fun (x3 : Fin (26 : ℕ) → Bool) => List.ofFn x3 ++ [x3 (0 : Fin (26 : ℕ)) || x3 (1 : Fin (26 : ℕ))];
      let ev : List (Bool × ℕ × ℕ) → ℕ → List Bool → Bool := fun prog out w =>
        (List.foldl (fun (acc : List Bool) (g : Bool × ℕ × ℕ) =>
          acc ++ [if g.1 = Bool.true then acc.getD g.2.1 Bool.false && acc.getD g.2.2 Bool.false
                else acc.getD g.2.1 Bool.false || acc.getD g.2.2 Bool.false])
          w prog).getD out Bool.false;
      ∃ (prog : List (Bool × ℕ × ℕ)) (out : ℕ),
        prog.length ≤ (28 : ℕ) ∧
        (27 : ℕ) ≤ out ∧
        out < (27 : ℕ) + prog.length ∧
        (∀ i < prog.length,
          (prog.getD i (Bool.false, (0 : ℕ), (0 : ℕ))).2.1 < (prog.getD i (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 ∧
          (prog.getD i (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 < (27 : ℕ) + i) ∧
        (∀ (x5 x6 : Fin (13 : ℕ)),
          x6 ∈ [(12 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (4 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ)), (10 : Fin (13 : ℕ)), (11 : Fin (13 : ℕ))] →
          x1 x5 x6 → ev prog out (x3 (x2 x5 x6)) = Bool.true) ∧
        ∀ (x5 : Fin (26 : ℕ) → Bool),
          ev prog out (x3 x5) = Bool.true →
          ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)),
            x1 x7 x8 ∧ x5 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x8) = Bool.true) :
    (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x2 x3 : Fin (13 : ℕ)) (x4 : Fin (26 : ℕ)) => Decidable.decide (x4 = Fin.castAdd (13 : ℕ) x2 ∨ x4 = Fin.natAdd (13 : ℕ) x3); have x3 : (Fin (26 : ℕ) → Bool) → List Bool := fun (x3 : Fin (26 : ℕ) → Bool) => List.ofFn x3 ++ [x3 (0 : Fin (26 : ℕ)) || x3 (1 : Fin (26 : ℕ))]; ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size ≤ (28 : ℕ) ∧ (27 : ℕ) ≤ x4.output ∧ x4.output < (27 : ℕ) + x4.size ∧ PEqualNP.TopForm.IsAO2 (27 : ℕ) x4 ∧ (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧ (∀ (x5 x6 : Fin (13 : ℕ)), x6 ∈ [(12 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (4 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ)), (10 : Fin (13 : ℕ)), (11 : Fin (13 : ℕ))] → x1 x5 x6 → x4.eval (x3 (x2 x5 x6)) = Bool.true) ∧ ∀ (x5 : Fin (26 : ℕ) → Bool), x4.eval (x3 x5) = Bool.true → ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), x1 x7 x8 ∧ x5 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x8) = Bool.true) :=
  Exists.elim hProg18727 fun prog h1 =>
  Exists.elim h1 fun out h =>
  Exists.elim (hCompileAO2 prog out h.2.2.2.1) fun C hC =>
    ⟨C, hC.1 ▸ h.1, hC.2.1 ▸ h.2.1, hC.2.1 ▸ hC.1 ▸ h.2.2.1, hC.2.2.1, hC.2.2.2.1,
      fun a b hb hab => (hC.2.2.2.2 _).trans (h.2.2.2.2.1 a b hb hab),
      fun x hx => h.2.2.2.2.2 x ((hC.2.2.2.2 _).symm.trans hx)⟩
