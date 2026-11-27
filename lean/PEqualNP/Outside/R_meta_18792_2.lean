import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18792_2
    (hAll52 :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Bool),
        let inc : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop :=
          fun (p l : Fin (13 : ℕ)) =>
            p - l = (0 : Fin (13 : ℕ)) ∨ p - l = (1 : Fin (13 : ℕ)) ∨
            p - l = (3 : Fin (13 : ℕ)) ∨ p - l = (9 : Fin (13 : ℕ));
        let mkIn : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool :=
          fun (f g : Fin (13 : ℕ) → Bool) => (List.ofFn f ++ List.ofFn g) ++ [x4];
        (PEqualNP.MetaComplexity.Monotone2 x1 ∧
         PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 ∧
         (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (27 : ℕ) x1 ∧
         (∀ (p l : Fin (13 : ℕ)), inc p l →
           x1.eval (mkIn (fun (a : Fin (13 : ℕ)) => Decidable.decide (a = p))
                         (fun (b : Fin (13 : ℕ)) => Decidable.decide (b = l))) = Bool.true) ∧
         (∀ (q : Finset (Fin (13 : ℕ))), q.card = (4 : ℕ) →
           (∀ (l : Fin (13 : ℕ)), (q.filter fun (p : Fin (13 : ℕ)) => inc p l).card ≤ (2 : ℕ)) →
           x1.eval (mkIn (fun (a : Fin (13 : ℕ)) => Decidable.decide (a ∈ q))
                         (fun (b : Fin (13 : ℕ)) => Decidable.decide (∀ p ∈ q, ¬inc p b))) = Bool.false) ∧
         (∀ (p1 p2 l1 l2 : Fin (13 : ℕ)),
           ¬inc p1 l1 → ¬inc p1 l2 → ¬inc p2 l1 → ¬inc p2 l2 →
           x1.eval (mkIn (fun (a : Fin (13 : ℕ)) => Decidable.decide (a = p1 ∨ a = p2))
                         (fun (b : Fin (13 : ℕ)) => Decidable.decide (b = l1 ∨ b = l2))) = Bool.false) ∧
         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
        (63 : ℕ) ≤ x1.size)
    (hUniqueMissing :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),
        let inc : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop :=
          fun (p l : Fin (13 : ℕ)) =>
            p - l = (0 : Fin (13 : ℕ)) ∨ p - l = (1 : Fin (13 : ℕ)) ∨
            p - l = (3 : Fin (13 : ℕ)) ∨ p - l = (9 : Fin (13 : ℕ));
        let mkIn : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool :=
          fun (f g : Fin (13 : ℕ) → Bool) => (List.ofFn f ++ List.ofFn g) ++ [x4];
        (PEqualNP.MetaComplexity.Monotone2 x1 ∧
         PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 ∧
         (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (27 : ℕ) x1 ∧
         inc x2 x3 ∧
         x1.eval (mkIn (fun (a : Fin (13 : ℕ)) => Decidable.decide (a = x2))
                       (fun (b : Fin (13 : ℕ)) => Decidable.decide (b = x3))) = Bool.false ∧
         (∀ (p l : Fin (13 : ℕ)), inc p l → p ≠ x2 ∨ l ≠ x3 →
           x1.eval (mkIn (fun (a : Fin (13 : ℕ)) => Decidable.decide (a = p))
                         (fun (b : Fin (13 : ℕ)) => Decidable.decide (b = l))) = Bool.true) ∧
         (∀ (q : Finset (Fin (13 : ℕ))), q.card = (4 : ℕ) →
           (∀ (l : Fin (13 : ℕ)), (q.filter fun (p : Fin (13 : ℕ)) => inc p l).card ≤ (2 : ℕ)) →
           x1.eval (mkIn (fun (a : Fin (13 : ℕ)) => Decidable.decide (a ∈ q))
                         (fun (b : Fin (13 : ℕ)) => Decidable.decide (∀ p ∈ q, ¬inc p b))) = Bool.false) ∧
         (∀ (p1 p2 l1 l2 : Fin (13 : ℕ)),
           ¬inc p1 l1 → ¬inc p1 l2 → ¬inc p2 l1 → ¬inc p2 l2 →
           x1.eval (mkIn (fun (a : Fin (13 : ℕ)) => Decidable.decide (a = p1 ∨ a = p2))
                         (fun (b : Fin (13 : ℕ)) => Decidable.decide (b = l1 ∨ b = l2))) = Bool.false) ∧
         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
        (63 : ℕ) ≤ x1.size) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 →       (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (27 : ℕ) x1 →         have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => ((List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ [x4];         (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x8 → x10 ≠ x2 ∨ x11 ≠ x3 → x1.eval (x9 {x10} {x11}) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) → (∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x11 | x14 - x13 ∈ x8}.card ≤ (2 : ℕ)) → x1.eval (x9 x11 {x14 : Fin (13 : ℕ) | ∀ x15 ∈ x11, x15 - x14 ∉ x8}) = Bool.false) → (∀ (x12 x13 x14 x15 : Fin (13 : ℕ)), x12 - x14 ∉ x8 → x12 - x15 ∉ x8 → x13 - x14 ∉ x8 → x13 - x15 ∉ x8 → x1.eval (x9 {x12, x13} {x14, x15}) = Bool.false) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (63 : ℕ) ≤ x1.size) :=
  fun x1 x2 x3 x4 hM hRB hAP hPos hQuad hBlk hTop =>
    let x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}
    let inc : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop :=
      fun p l => p - l = (0 : Fin (13 : ℕ)) ∨ p - l = (1 : Fin (13 : ℕ)) ∨ p - l = (3 : Fin (13 : ℕ)) ∨ p - l = (9 : Fin (13 : ℕ))
    let hIncIff : ∀ (p l : Fin (13 : ℕ)), (p - l ∈ x8) ↔ inc p l :=
      fun p l =>
        Finset.mem_insert.trans
          (or_congr_right (Finset.mem_insert.trans
            (or_congr_right (Finset.mem_insert.trans
              (or_congr_right Finset.mem_singleton)))))
    let hPos' : ∀ (p l : Fin (13 : ℕ)), inc p l → p ≠ x2 ∨ l ≠ x3 →
        x1.eval (((List.ofFn fun (a : Fin (13 : ℕ)) => Decidable.decide (a = p)) ++
                  List.ofFn fun (b : Fin (13 : ℕ)) => Decidable.decide (b = l)) ++ [x4]) = Bool.true :=
      fun p l hinc hne =>
        Eq.trans
          (congrArg x1.eval
            (congrArg (fun u => u ++ [x4])
              (congrArg₂ List.append
                (congrArg List.ofFn (funext fun a => (decide_eq_decide.mpr Finset.mem_singleton).symm))
                (congrArg List.ofFn (funext fun b => (decide_eq_decide.mpr Finset.mem_singleton).symm)))))
          (hPos p l ((hIncIff p l).mpr hinc) hne)
    let hQuad' : ∀ (q : Finset (Fin (13 : ℕ))), q.card = (4 : ℕ) →
        (∀ (l : Fin (13 : ℕ)), (q.filter fun (p : Fin (13 : ℕ)) => inc p l).card ≤ (2 : ℕ)) →
        x1.eval (((List.ofFn fun (a : Fin (13 : ℕ)) => Decidable.decide (a ∈ q)) ++
                  List.ofFn fun (b : Fin (13 : ℕ)) => Decidable.decide (∀ p ∈ q, ¬inc p b)) ++ [x4]) = Bool.false :=
      fun q hq hdeg =>
        Eq.trans
          (congrArg x1.eval
            (congrArg (fun u => u ++ [x4])
              (congrArg (List.append (List.ofFn fun (a : Fin (13 : ℕ)) => Decidable.decide (a ∈ q)))
                (congrArg List.ofFn
                  (funext fun b =>
                    (decide_eq_decide.mpr
                      ((Finset.mem_filter.trans (and_iff_right (Finset.mem_univ b))).trans
                        (forall_congr' fun p => imp_congr_right fun _ => not_congr (hIncIff p b)))).symm)))))
          (hQuad q hq fun l =>
            Eq.mp
              (congrArg (fun s : Finset (Fin (13 : ℕ)) => s.card ≤ (2 : ℕ))
                (Finset.filter_congr fun p _ => (hIncIff p l).symm))
              (hdeg l))
    let hBlk' : ∀ (p1 p2 l1 l2 : Fin (13 : ℕ)),
        ¬inc p1 l1 → ¬inc p1 l2 → ¬inc p2 l1 → ¬inc p2 l2 →
        x1.eval (((List.ofFn fun (a : Fin (13 : ℕ)) => Decidable.decide (a = p1 ∨ a = p2)) ++
                  List.ofFn fun (b : Fin (13 : ℕ)) => Decidable.decide (b = l1 ∨ b = l2)) ++ [x4]) = Bool.false :=
      fun p1 p2 l1 l2 h11 h12 h21 h22 =>
        Eq.trans
          (congrArg x1.eval
            (congrArg (fun u => u ++ [x4])
              (congrArg₂ List.append
                (congrArg List.ofFn (funext fun a =>
                  (decide_eq_decide.mpr (Finset.mem_insert.trans (or_congr_right Finset.mem_singleton))).symm))
                (congrArg List.ofFn (funext fun b =>
                  (decide_eq_decide.mpr (Finset.mem_insert.trans (or_congr_right Finset.mem_singleton))).symm)))))
          (hBlk p1 p2 l1 l2
            (fun h => h11 ((hIncIff p1 l1).mp h))
            (fun h => h12 ((hIncIff p1 l2).mp h))
            (fun h => h21 ((hIncIff p2 l1).mp h))
            (fun h => h22 ((hIncIff p2 l2).mp h)))
    Or.elim (Classical.em (inc x2 x3))
      (fun h23 =>
        Or.elim (Bool.eq_false_or_eq_true
          (x1.eval (((List.ofFn fun (a : Fin (13 : ℕ)) => Decidable.decide (a = x2)) ++
                     List.ofFn fun (b : Fin (13 : ℕ)) => Decidable.decide (b = x3)) ++ [x4])))
          (fun hT =>
            hAll52 x1 x4
              ⟨hM, hRB, hAP,
               fun p l hinc =>
                 Or.elim (Classical.em (p = x2))
                   (fun hp => Or.elim (Classical.em (l = x3))
                     (fun hl => hp.symm ▸ hl.symm ▸ hT)
                     (fun hl => hPos' p l hinc (Or.inr hl)))
                   (fun hp => hPos' p l hinc (Or.inl hp)),
               hQuad', hBlk', hTop⟩)
          (fun hF => hUniqueMissing x1 x2 x3 x4 ⟨hM, hRB, hAP, h23, hF, hPos', hQuad', hBlk', hTop⟩))
      (fun hNot23 =>
        hAll52 x1 x4
          ⟨hM, hRB, hAP,
           fun p l hinc =>
             hPos' p l hinc
               (Or.elim (Classical.em (p = x2))
                 (fun hp => Or.inr fun hl => hNot23 (hp ▸ hl ▸ hinc))
                 Or.inl),
           hQuad', hBlk', hTop⟩)
