import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17237_2
    (hFullCircuit :
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ),
        PEqualNP.MetaComplexity.Monotone2 C ∧
        C.size ≤ (45 : ℕ) ∧
        C.output < (25 : ℕ) + C.size ∧
        w < (25 : ℕ) + C.size ∧
        ∀ (x : Fin (25 : ℕ) → Bool),
          have E : Prop := ∃ (a b : Fin (25 : ℕ)),
            (a : ℕ) < (12 : ℕ) ∧ (12 : ℕ) ≤ (b : ℕ) ∧
            ([(0 : ℕ), (6274 : ℕ), (0 : ℕ), (5664 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (0 : ℕ), (4184 : ℕ), (2092 : ℕ), (1046 : ℕ)].getD (a : ℕ) (0 : ℕ)).testBit ((b : ℕ) - (12 : ℕ)) = Bool.true ∧
            x a = Bool.true ∧ x b = Bool.true;
          ((C.wires (List.ofFn x)).getD C.output Bool.false = Bool.true ↔ E) ∧
          (¬E → (C.wires (List.ofFn x)).getD w Bool.false = (x (13 : Fin (25 : ℕ)) || x (15 : Fin (25 : ℕ)) || x (21 : Fin (25 : ℕ)))))
    (hRowEquiv :
      ∀ (a b : Fin (25 : ℕ)),
        ((a : ℕ) < (12 : ℕ) ∧ (12 : ℕ) ≤ (b : ℕ) ∧
          ([(0 : ℕ), (6274 : ℕ), (0 : ℕ), (5664 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (0 : ℕ), (4184 : ℕ), (2092 : ℕ), (1046 : ℕ)].getD (a : ℕ) (0 : ℕ)).testBit ((b : ℕ) - (12 : ℕ)) = Bool.true) ↔
        ((a : ℕ) < (12 : ℕ) ∧ (12 : ℕ) ≤ (b : ℕ) ∧
          ((a : ℕ) + (b : ℕ) + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
          (a : ℕ) ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)])) :
    (have x1 : Fin (25 : ℕ) → Fin (25 : ℕ) → Prop := fun (x1 x2 : Fin (25 : ℕ)) => ↑x1 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x2 ∧ (↑x1 + ↑x2 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x1 ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)]; have x2 : Finset (Fin (25 : ℕ)) := {(13 : Fin (25 : ℕ)), (15 : Fin (25 : ℕ)), (21 : Fin (25 : ℕ))}; have x3 : Finset (Fin (25 : ℕ)) → Prop := fun (x3 : Finset (Fin (25 : ℕ))) => ¬∃ x4 ∈ x3, ∃ x5 ∈ x3, x1 x4 x5; have x4 : Finset (Fin (25 : ℕ)) → Finset (Fin (25 : ℕ)) → Prop := fun (x4 x5 : Finset (Fin (25 : ℕ))) => x5 ⊆ x4 ∧ x3 x5 ∧ ∀ x6 ∈ x4, x6 ∉ x5 → ¬x3 (Insert.insert x6 x5); ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x5 ∧     x5.size ≤ (45 : ℕ) ∧       x5.output < (25 : ℕ) + x5.size ∧         x6 < (25 : ℕ) + x5.size ∧           have x7 : Finset (Fin (25 : ℕ)) → ℕ → Bool := fun (x7 : Finset (Fin (25 : ℕ))) (x8 : ℕ) => (x5.wires (List.ofFn fun (x9 : Fin (25 : ℕ)) => Decidable.decide (x9 ∈ x7))).getD x8 Bool.false;           (∀ (x8 x9 : Fin (25 : ℕ)), x1 x8 x9 → x7 {x8, x9} x5.output = Bool.true) ∧ (∀ (x8 : Finset (Fin (25 : ℕ))), x4 Finset.univ x8 → x7 x8 x5.output = Bool.false) ∧ (∀ x8 ∈ x2, x7 {x8} x6 = Bool.true) ∧ ∀ (x8 : Finset (Fin (25 : ℕ))), x4 (Finset.univ \ x2) x8 → x7 x8 x6 = Bool.false) := by
  dsimp only
  exact Exists.elim hFullCircuit fun C hC =>
    Exists.elim hC fun w h =>
      ⟨C, w, h.1, h.2.1, h.2.2.1, h.2.2.2.1,
        fun a b hab =>
          let hr := (hRowEquiv a b).mpr hab
          (h.2.2.2.2 (fun i => Decidable.decide (i ∈ ({a, b} : Finset (Fin (25 : ℕ)))))).1.mpr
            ⟨a, b, hr.1, hr.2.1, hr.2.2,
              decide_eq_true (Finset.mem_insert_self a {b}),
              decide_eq_true (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))⟩,
        fun S hS =>
          Bool.eq_false_iff.mpr fun ht =>
            Exists.elim ((h.2.2.2.2 (fun i => Decidable.decide (i ∈ S))).1.mp ht) fun a ha =>
              Exists.elim ha fun b hb =>
                hS.2.1 ⟨a, of_decide_eq_true hb.2.2.2.1, b, of_decide_eq_true hb.2.2.2.2,
                  (hRowEquiv a b).mp ⟨hb.1, hb.2.1, hb.2.2.1⟩⟩,
        fun z hz =>
          have hNoEdge : ¬∃ (a b : Fin (25 : ℕ)),
              (a : ℕ) < (12 : ℕ) ∧ (12 : ℕ) ≤ (b : ℕ) ∧
              ([(0 : ℕ), (6274 : ℕ), (0 : ℕ), (5664 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (0 : ℕ), (4184 : ℕ), (2092 : ℕ), (1046 : ℕ)].getD (a : ℕ) (0 : ℕ)).testBit ((b : ℕ) - (12 : ℕ)) = Bool.true ∧
              Decidable.decide (a ∈ ({z} : Finset (Fin (25 : ℕ)))) = Bool.true ∧
              Decidable.decide (b ∈ ({z} : Finset (Fin (25 : ℕ)))) = Bool.true :=
            fun he => Exists.elim he fun a ha => Exists.elim ha fun b hb =>
              let ha1 : a = z := Finset.mem_singleton.mp (of_decide_eq_true hb.2.2.2.1)
              let hb1 : b = z := Finset.mem_singleton.mp (of_decide_eq_true hb.2.2.2.2)
              Nat.not_lt.mpr (Eq.trans hb1 ha1.symm ▸ hb.2.1) hb.1
          let hval := (h.2.2.2.2 (fun i => Decidable.decide (i ∈ ({z} : Finset (Fin (25 : ℕ)))))).2 hNoEdge
          Or.elim (Finset.mem_insert.mp hz)
            (fun h13 =>
              let ht : Decidable.decide ((13 : Fin (25 : ℕ)) ∈ ({z} : Finset (Fin (25 : ℕ)))) = Bool.true :=
                decide_eq_true (Finset.mem_singleton.mpr h13.symm)
              Eq.trans hval (Eq.trans (congrArg (fun t => (t || _) || _) ht) (Eq.trans (congrArg (· || _) (Bool.true_or _)) (Bool.true_or _))))
            fun hz1 =>
              Or.elim (Finset.mem_insert.mp hz1)
                (fun h15 =>
                  let ht : Decidable.decide ((15 : Fin (25 : ℕ)) ∈ ({z} : Finset (Fin (25 : ℕ)))) = Bool.true :=
                    decide_eq_true (Finset.mem_singleton.mpr h15.symm)
                  Eq.trans hval (Eq.trans (congrArg (fun t => (_ || t) || _) ht) (Eq.trans (congrArg (· || _) (Bool.or_true _)) (Bool.true_or _))))
                (fun hz2 =>
                  let h21 := Finset.mem_singleton.mp hz2
                  let ht : Decidable.decide ((21 : Fin (25 : ℕ)) ∈ ({z} : Finset (Fin (25 : ℕ)))) = Bool.true :=
                    decide_eq_true (Finset.mem_singleton.mpr h21.symm)
                  Eq.trans hval (Eq.trans (congrArg (_ || ·) ht) (Bool.or_true _))),
        fun S hS =>
          have hNoEdge : ¬∃ (a b : Fin (25 : ℕ)),
              (a : ℕ) < (12 : ℕ) ∧ (12 : ℕ) ≤ (b : ℕ) ∧
              ([(0 : ℕ), (6274 : ℕ), (0 : ℕ), (5664 : ℕ), (2832 : ℕ), (1416 : ℕ), (708 : ℕ), (354 : ℕ), (0 : ℕ), (4184 : ℕ), (2092 : ℕ), (1046 : ℕ)].getD (a : ℕ) (0 : ℕ)).testBit ((b : ℕ) - (12 : ℕ)) = Bool.true ∧
              Decidable.decide (a ∈ S) = Bool.true ∧
              Decidable.decide (b ∈ S) = Bool.true :=
            fun he => Exists.elim he fun a ha => Exists.elim ha fun b hb =>
              hS.2.1 ⟨a, of_decide_eq_true hb.2.2.2.1, b, of_decide_eq_true hb.2.2.2.2,
                (hRowEquiv a b).mp ⟨hb.1, hb.2.1, hb.2.2.1⟩⟩
          let hval := (h.2.2.2.2 (fun i => Decidable.decide (i ∈ S))).2 hNoEdge
          let h13 : Decidable.decide ((13 : Fin (25 : ℕ)) ∈ S) = Bool.false :=
            decide_eq_false fun hm => (Finset.mem_sdiff.mp (hS.1 hm)).2 (Finset.mem_insert_self _ _)
          let h15 : Decidable.decide ((15 : Fin (25 : ℕ)) ∈ S) = Bool.false :=
            decide_eq_false fun hm => (Finset.mem_sdiff.mp (hS.1 hm)).2 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
          let h21 : Decidable.decide ((21 : Fin (25 : ℕ)) ∈ S) = Bool.false :=
            decide_eq_false fun hm => (Finset.mem_sdiff.mp (hS.1 hm)).2 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
          Eq.trans hval (congrArg₂ or (congrArg₂ or h13 h15) h21)⟩
