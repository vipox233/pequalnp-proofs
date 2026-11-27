import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17147_2
    (hAll52 :
      let inc : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop :=
        fun (p l : Fin (13 : ℕ)) =>
          p - l = (0 : Fin (13 : ℕ)) ∨ p - l = (1 : Fin (13 : ℕ)) ∨
          p - l = (3 : Fin (13 : ℕ)) ∨ p - l = (9 : Fin (13 : ℕ));
      let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool :=
        fun (p l : Fin (13 : ℕ)) =>
          (List.ofFn fun (a : Fin (13 : ℕ)) => Decidable.decide (a = p)) ++
          List.ofFn fun (b : Fin (13 : ℕ)) => Decidable.decide (b = l);
      let x3 : Finset (Fin (13 : ℕ)) → List Bool :=
        fun (q : Finset (Fin (13 : ℕ))) =>
          (List.ofFn fun (a : Fin (13 : ℕ)) => Decidable.decide (a ∈ q)) ++
          List.ofFn fun (b : Fin (13 : ℕ)) => Decidable.decide (∀ p ∈ q, ¬inc p b);
      ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Bool),
        (PEqualNP.MetaComplexity.Monotone2 x5 ∧
         (∀ (k : Fin x5.gates.length), ∀ w ∈ (x5.gates.get k).inputs, w < (27 : ℕ) + ↑k) ∧
         (∀ (p l : Fin (13 : ℕ)), inc p l → x5.eval (x2 p l ++ [x7]) = Bool.true) ∧
         (∀ (q : Finset (Fin (13 : ℕ))), q.card = (4 : ℕ) →
           (∀ (l : Fin (13 : ℕ)), (q.filter fun (p : Fin (13 : ℕ)) => inc p l).card ≤ (2 : ℕ)) →
           x5.eval (x3 q ++ [x7]) = Bool.false) ∧
         (∃ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
           x5.gates[k]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and)) →
        (63 : ℕ) ≤ x5.size)
    (hUniqueMissing :
      let inc : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop :=
        fun (p l : Fin (13 : ℕ)) =>
          p - l = (0 : Fin (13 : ℕ)) ∨ p - l = (1 : Fin (13 : ℕ)) ∨
          p - l = (3 : Fin (13 : ℕ)) ∨ p - l = (9 : Fin (13 : ℕ));
      let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool :=
        fun (p l : Fin (13 : ℕ)) =>
          (List.ofFn fun (a : Fin (13 : ℕ)) => Decidable.decide (a = p)) ++
          List.ofFn fun (b : Fin (13 : ℕ)) => Decidable.decide (b = l);
      let x3 : Finset (Fin (13 : ℕ)) → List Bool :=
        fun (q : Finset (Fin (13 : ℕ))) =>
          (List.ofFn fun (a : Fin (13 : ℕ)) => Decidable.decide (a ∈ q)) ++
          List.ofFn fun (b : Fin (13 : ℕ)) => Decidable.decide (∀ p ∈ q, ¬inc p b);
      ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin (13 : ℕ)) (x7 : Bool),
        (PEqualNP.MetaComplexity.Monotone2 x5 ∧
         (∀ (k : Fin x5.gates.length), ∀ w ∈ (x5.gates.get k).inputs, w < (27 : ℕ) + ↑k) ∧
         inc (0 : Fin (13 : ℕ)) x6 ∧
         x5.eval (x2 (0 : Fin (13 : ℕ)) x6 ++ [x7]) = Bool.false ∧
         (∀ (p l : Fin (13 : ℕ)), inc p l → p ≠ (0 : Fin (13 : ℕ)) ∨ l ≠ x6 →
           x5.eval (x2 p l ++ [x7]) = Bool.true) ∧
         (∀ (q : Finset (Fin (13 : ℕ))), q.card = (4 : ℕ) →
           (∀ (l : Fin (13 : ℕ)), (q.filter fun (p : Fin (13 : ℕ)) => inc p l).card ≤ (2 : ℕ)) →
           x5.eval (x3 q ++ [x7]) = Bool.false) ∧
         (∃ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
           x5.gates[k]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and)) →
        (63 : ℕ) ≤ x5.size) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin (13 : ℕ)) (x7 : Bool), PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x9 : Fin x5.gates.length), ∀ x10 ∈ (x5.gates.get x9).inputs, x10 < (27 : ℕ) + ↑x9) → (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x1 → x10 ≠ (0 : Fin (13 : ℕ)) ∨ x11 ≠ x6 → x5.eval (x2 x10 x11 ++ [x7]) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), x4 x11 → x5.eval (x3 x11 ++ [x7]) = Bool.false) → (∃ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 ∧ x13.op = PEqualNP.CircuitLowerBounds.GateOp.and) → (63 : ℕ) ≤ x5.size) :=
  fun x5 x6 x7 hM hRB hPos hQuad hAnd =>
    let x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}
    let inc : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop :=
      fun p l => p - l = (0 : Fin (13 : ℕ)) ∨ p - l = (1 : Fin (13 : ℕ)) ∨ p - l = (3 : Fin (13 : ℕ)) ∨ p - l = (9 : Fin (13 : ℕ))
    let hIncIff : ∀ (p l : Fin (13 : ℕ)), (p - l ∈ x1) ↔ inc p l :=
      fun p l =>
        Finset.mem_insert.trans
          (or_congr_right (Finset.mem_insert.trans
            (or_congr_right (Finset.mem_insert.trans
              (or_congr_right Finset.mem_singleton)))))
    let hPos' : ∀ (p l : Fin (13 : ℕ)), inc p l → p ≠ (0 : Fin (13 : ℕ)) ∨ l ≠ x6 →
        x5.eval (((List.ofFn fun (a : Fin (13 : ℕ)) => Decidable.decide (a = p)) ++
                  List.ofFn fun (b : Fin (13 : ℕ)) => Decidable.decide (b = l)) ++ [x7]) = Bool.true :=
      fun p l hinc hne => hPos p l ((hIncIff p l).mpr hinc) hne
    let hQuad' : ∀ (q : Finset (Fin (13 : ℕ))), q.card = (4 : ℕ) →
        (∀ (l : Fin (13 : ℕ)), (q.filter fun (p : Fin (13 : ℕ)) => inc p l).card ≤ (2 : ℕ)) →
        x5.eval (((List.ofFn fun (a : Fin (13 : ℕ)) => Decidable.decide (a ∈ q)) ++
                  List.ofFn fun (b : Fin (13 : ℕ)) => Decidable.decide (∀ p ∈ q, ¬inc p b)) ++ [x7]) = Bool.false :=
      fun q hq hdeg =>
        Eq.trans
          (congrArg x5.eval
            (congrArg (fun u => u ++ [x7])
              (congrArg (List.append (List.ofFn fun (a : Fin (13 : ℕ)) => Decidable.decide (a ∈ q)))
                (congrArg List.ofFn
                  (funext fun b =>
                    (decide_eq_decide.mpr
                      (forall_congr' fun p => imp_congr_right fun _ => not_congr (hIncIff p b))).symm)))))
          (hQuad q ⟨hq, fun l =>
            Eq.mp
              (congrArg (fun s : Finset (Fin (13 : ℕ)) => s.card ≤ (2 : ℕ))
                (Finset.filter_congr fun p _ => (hIncIff p l).symm))
              (hdeg l)⟩)
    Or.elim (Classical.em (inc (0 : Fin (13 : ℕ)) x6))
      (fun h06 =>
        Or.elim (Bool.eq_false_or_eq_true
          (x5.eval (((List.ofFn fun (a : Fin (13 : ℕ)) => Decidable.decide (a = (0 : Fin (13 : ℕ)))) ++
                     List.ofFn fun (b : Fin (13 : ℕ)) => Decidable.decide (b = x6)) ++ [x7])))
          (fun hT =>
            hAll52 x5 x7
              ⟨hM, hRB,
               fun p l hinc =>
                 Or.elim (Classical.em (p = (0 : Fin (13 : ℕ))))
                   (fun hp => Or.elim (Classical.em (l = x6))
                     (fun hl => hp.symm ▸ hl.symm ▸ hT)
                     (fun hl => hPos' p l hinc (Or.inr hl)))
                   (fun hp => hPos' p l hinc (Or.inl hp)),
               hQuad', hAnd⟩)
          (fun hF => hUniqueMissing x5 x6 x7 ⟨hM, hRB, h06, hF, hPos', hQuad', hAnd⟩))
      (fun hNot06 =>
        hAll52 x5 x7
          ⟨hM, hRB,
           fun p l hinc =>
             hPos' p l hinc
               (Or.elim (Classical.em (p = (0 : Fin (13 : ℕ))))
                 (fun hp => Or.inr fun hl => hNot06 (hp ▸ hl ▸ hinc))
                 Or.inl),
           hQuad', hAnd⟩)
