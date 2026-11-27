import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17409_2
    (hEvalSpec :
      let x1 : List (Finset ℕ × Finset ℕ) → Finset ℕ → List Bool → Bool :=
        fun (g : List (Finset ℕ × Finset ℕ)) (out : Finset ℕ) (inp : List Bool) =>
          let w : List Bool :=
            List.foldl (fun (acc : List Bool) (p : Finset ℕ × Finset ℕ) =>
              acc ++ [Decidable.decide (∀ u ∈ p.1, acc.getD u Bool.false = Bool.true) ||
                      Decidable.decide (∀ u ∈ p.2, acc.getD u Bool.false = Bool.true)])
              (inp ++ [Bool.false]) g;
          Decidable.decide (∀ u ∈ out, w.getD u Bool.false = Bool.true);
      let x2 : Fin (21 : ℕ) → Fin (21 : ℕ) → Bool :=
        fun (p l : Fin (21 : ℕ)) =>
          [(↑p + (20 : ℕ)) % (21 : ℕ), ↑p, (↑p + (5 : ℕ)) % (21 : ℕ),
           (↑p + (7 : ℕ)) % (21 : ℕ), (↑p + (17 : ℕ)) % (21 : ℕ)].contains ↑l;
      ∀ (x3 x6 x7 : List (Finset ℕ × Finset ℕ)) (x4 x9 : Finset ℕ) (x8 : Fin (21 : ℕ) → Finset ℕ),
        (∀ (f : Fin (42 : ℕ) → Bool), x1 x3 x4 (List.ofFn f) = Bool.true ↔
          ∃ (p l : Fin (21 : ℕ)), x2 p l = Bool.true ∧
            f (Fin.castAdd (21 : ℕ) p) = Bool.true ∧ f (Fin.natAdd (21 : ℕ) l) = Bool.true) →
        x1 x7 x9 (List.ofFn fun (_ : Fin (21 : ℕ)) => Bool.false) = Bool.false →
        (∀ (p0 : Fin (21 : ℕ)) (y : Fin (21 : ℕ) → Bool),
          x1 x7 x9 (List.ofFn fun (p : Fin (21 : ℕ)) =>
            Decidable.decide (p = p0) && x1 x6 (x8 p) (List.ofFn y)) =
          Decidable.decide (∃ (l : Fin (21 : ℕ)), x2 p0 l = Bool.true ∧ y l = Bool.true)) →
        ∀ (x10 x11 : Fin (21 : ℕ) → Bool),
          ((x10 = fun (_ : Fin (21 : ℕ)) => Bool.false) ∨
           ∃ (p0 : Fin (21 : ℕ)), x10 = fun (p : Fin (21 : ℕ)) => Decidable.decide (p = p0)) →
          x1 x7 x9 (List.ofFn fun (p : Fin (21 : ℕ)) => x10 p && x1 x6 (x8 p) (List.ofFn x11)) =
          x1 x3 x4 (List.ofFn (Fin.append x10 x11)))
    (hDecomposeClean :
      let x1 : List (Finset ℕ × Finset ℕ) → Finset ℕ → List Bool → Bool :=
        fun (g : List (Finset ℕ × Finset ℕ)) (out : Finset ℕ) (inp : List Bool) =>
          let w : List Bool :=
            List.foldl (fun (acc : List Bool) (p : Finset ℕ × Finset ℕ) =>
              acc ++ [Decidable.decide (∀ u ∈ p.1, acc.getD u Bool.false = Bool.true) ||
                      Decidable.decide (∀ u ∈ p.2, acc.getD u Bool.false = Bool.true)])
              (inp ++ [Bool.false]) g;
          Decidable.decide (∀ u ∈ out, w.getD u Bool.false = Bool.true);
      let x2 : Fin (21 : ℕ) → Fin (21 : ℕ) → Bool :=
        fun (p l : Fin (21 : ℕ)) =>
          [(↑p + (20 : ℕ)) % (21 : ℕ), ↑p, (↑p + (5 : ℕ)) % (21 : ℕ),
           (↑p + (7 : ℕ)) % (21 : ℕ), (↑p + (17 : ℕ)) % (21 : ℕ)].contains ↑l;
      ∀ (x3 : List (Finset ℕ × Finset ℕ)) (x4 : Finset ℕ),
        x4.Nonempty →
        (∀ (f : Fin (42 : ℕ) → Bool), x1 x3 x4 (List.ofFn f) = Bool.true ↔
          ∃ (p l : Fin (21 : ℕ)), x2 p l = Bool.true ∧
            f (Fin.castAdd (21 : ℕ) p) = Bool.true ∧ f (Fin.natAdd (21 : ℕ) l) = Bool.true) →
        ∃ (x6 x7 : List (Finset ℕ × Finset ℕ)) (x8 : Fin (21 : ℕ) → Finset ℕ) (x9 : Finset ℕ),
          x6.length + x7.length ≤ x3.length ∧
          x1 x7 x9 (List.ofFn fun (_ : Fin (21 : ℕ)) => Bool.false) = Bool.false ∧
          ∀ (p0 : Fin (21 : ℕ)) (y : Fin (21 : ℕ) → Bool),
            x1 x7 x9 (List.ofFn fun (p : Fin (21 : ℕ)) =>
              Decidable.decide (p = p0) && x1 x6 (x8 p) (List.ofFn y)) =
            Decidable.decide (∃ (l : Fin (21 : ℕ)), x2 p0 l = Bool.true ∧ y l = Bool.true)) :
    (have x1 : List (Finset ℕ × Finset ℕ) → Finset ℕ → List Bool → Bool := fun (x1 : List (Finset ℕ × Finset ℕ)) (x2 : Finset ℕ) (x3 : List Bool) =>   have x4 : List Bool := List.foldl (fun (x4 : List Bool) (x5 : Finset ℕ × Finset ℕ) => x4 ++ [Decidable.decide (∀ x6 ∈ x5.1, x4.getD x6 Bool.false = Bool.true) || Decidable.decide (∀ x6 ∈ x5.2, x4.getD x6 Bool.false = Bool.true)]) (x3 ++ [Bool.false]) x1;   Decidable.decide (∀ x5 ∈ x2, x4.getD x5 Bool.false = Bool.true); have x2 : Fin (21 : ℕ) → Fin (21 : ℕ) → Bool := fun (x2 x3 : Fin (21 : ℕ)) => [(↑x2 + (20 : ℕ)) % (21 : ℕ), ↑x2, (↑x2 + (5 : ℕ)) % (21 : ℕ), (↑x2 + (7 : ℕ)) % (21 : ℕ), (↑x2 + (17 : ℕ)) % (21 : ℕ)].contains ↑x3; ∀ (x3 : List (Finset ℕ × Finset ℕ)) (x4 : Finset ℕ), (∀ (x5 : Fin (42 : ℕ) → Bool), x1 x3 x4 (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (21 : ℕ)) (x7 : Fin (21 : ℕ)), x2 x6 x7 = Bool.true ∧ x5 (Fin.castAdd (21 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (21 : ℕ) x7) = Bool.true) → ∃ (x6 : List (Finset ℕ × Finset ℕ)) (x7 : List (Finset ℕ × Finset ℕ)) (x8 : Fin (21 : ℕ) → Finset ℕ) (x9 : Finset ℕ), x6.length + x7.length ≤ x3.length ∧ ∀ (x10 x11 : Fin (21 : ℕ) → Bool), ((x10 = fun (x12 : Fin (21 : ℕ)) => Bool.false) ∨ ∃ (x12 : Fin (21 : ℕ)), x10 = fun (x13 : Fin (21 : ℕ)) => Decidable.decide (x13 = x12)) → x1 x7 x9 (List.ofFn fun (x13 : Fin (21 : ℕ)) => x10 x13 && x1 x6 (x8 x13) (List.ofFn x11)) = x1 x3 x4 (List.ofFn (Fin.append x10 x11))) :=
  fun x3 x4 hSpec =>
    let hNE : x4.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr fun hEmp =>
        Exists.elim
          ((hSpec fun _ => Bool.false).mp
            (hEmp ▸ (decide_eq_true fun _ hw => False.elim (Finset.notMem_empty _ hw))))
          fun _ hp => Exists.elim hp fun _ hl => Bool.false_ne_true hl.2.1
    Exists.elim (hDecomposeClean x3 x4 hNE hSpec) fun x6 hx6 =>
      Exists.elim hx6 fun x7 hx7 =>
        Exists.elim hx7 fun x8 hx8 =>
          Exists.elim hx8 fun x9 hx9 =>
            ⟨x6, x7, x8, x9, hx9.1, hEvalSpec x3 x6 x7 x4 x9 x8 hSpec hx9.2.1 hx9.2.2⟩
