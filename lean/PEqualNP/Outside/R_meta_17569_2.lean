import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17569_2
    (hExtendIndepToMax :
      ∀ (x1 : SimpleGraph (Fin (42 : ℕ))) (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ))
        (i : Finset (Fin (42 : ℕ))),
        (∀ a ∈ i, ∀ b ∈ i, ¬x1.Adj a b) →
        x2.eval i = Bool.true →
        ∃ (s : Finset (Fin (42 : ℕ))),
          Maximal (fun (t : Finset (Fin (42 : ℕ))) => ∀ a ∈ t, ∀ b ∈ t, ¬x1.Adj a b) s ∧
          x2.eval s = Bool.true)
    (hExistsFalsePosIndep :
      have x1 : SimpleGraph (Fin (42 : ℕ)) :=
        SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) =>
          ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]
      ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) (x10 : Fin x2.size)
        (x11 : Finset (Fin (42 : ℕ) × Fin (42 : ℕ))),
        have x9 : Fin x2.size → Fin (42 : ℕ) × Fin (42 : ℕ) → Prop := fun g e =>
          e.1 ∈ x2.leftVars g ∧ e.2 ∈ x2.rightVars g ∨ e.2 ∈ x2.leftVars g ∧ e.1 ∈ x2.rightVars g
        (x2.WellFormed ∧ x2.outVars = ∅ ∧
          (∀ (g : Fin x2.size) (v : Fin (42 : ℕ)), x2.gateVal [v].toFinset g = Bool.false) ∧
          (∀ (g : Fin x2.size), Disjoint (x2.leftVars g) (x2.rightVars g)) ∧
          (x2.size = (19 : ℕ) ∨ x2.size = (20 : ℕ)) ∧
          (∀ (u v : Fin (42 : ℕ)), x1.Adj u v → x2.eval [u, v].toFinset = Bool.true) ∧
          x10 ∉ x2.outGates ∧ x11.card = (6 : ℕ) ∧
          ∀ e ∈ x11,
            ↑e.1 < (21 : ℕ) ∧ x1.Adj e.1 e.2 ∧ x9 x10 e ∧
            (∀ g ∈ x2.outGates, ¬x9 g e) ∧
            ∃ g ∈ x2.outGates,
              Relation.ReflTransGen
                (fun (a b : Fin x2.size) =>
                  (a ∈ x2.leftGates b ∨ a ∈ x2.rightGates b) ∧ x2.gateVal [e.1, e.2].toFinset b = Bool.true)
                x10 g) →
        ∃ (i : Finset (Fin (42 : ℕ))),
          (∀ a ∈ i, ∀ b ∈ i, ¬x1.Adj a b) ∧ x2.eval i = Bool.true) :
    (have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)),   x2.WellFormed →     x2.outVars = ∅ →       (∀ (x5 : Fin x2.size) (x6 : Fin (42 : ℕ)), x2.gateVal {x6} x5 = Bool.false) →         (∀ (x6 : Fin x2.size), Disjoint (x2.leftVars x6) (x2.rightVars x6)) →           x2.size = (19 : ℕ) ∨ x2.size = (20 : ℕ) →             (∀ (x8 x9 : Fin (42 : ℕ)), x1.Adj x8 x9 → x2.eval {x8, x9} = Bool.true) →               (have x9 : Fin x2.size → Fin (42 : ℕ) × Fin (42 : ℕ) → Prop := fun (x9 : Fin x2.size) (x10 : Fin (42 : ℕ) × Fin (42 : ℕ)) => x10.1 ∈ x2.leftVars x9 ∧ x10.2 ∈ x2.rightVars x9 ∨ x10.2 ∈ x2.leftVars x9 ∧ x10.1 ∈ x2.rightVars x9;                 ∃ x10 ∉ x2.outGates, ∃ (x11 : Finset (Fin (42 : ℕ) × Fin (42 : ℕ))), x11.card = (6 : ℕ) ∧ ∀ x12 ∈ x11, ↑x12.1 < (21 : ℕ) ∧ x1.Adj x12.1 x12.2 ∧ x9 x10 x12 ∧ (∀ x14 ∈ x2.outGates, ¬x9 x14 x12) ∧ ∃ x14 ∈ x2.outGates, Relation.ReflTransGen (fun (x15 x16 : Fin x2.size) => (x15 ∈ x2.leftGates x16 ∨ x15 ∈ x2.rightGates x16) ∧ x2.gateVal {x12.1, x12.2} x16 = Bool.true) x10 x14) →                 ∃ (x10 : Finset (Fin (42 : ℕ))), Maximal (fun (x11 : Finset (Fin (42 : ℕ))) => ∀ x12 ∈ x11, ∀ x14 ∈ x11, ¬x1.Adj x12 x14) x10 ∧ x2.eval x10 = Bool.true) :=
  fun x2 hWF hOut hSing hDisj hSz hEdges hEx =>
    have h1 : ∀ a : Fin (42 : ℕ), ({a} : Finset (Fin (42 : ℕ))) = [a].toFinset := fun a =>
      Finset.ext fun _ => Finset.mem_singleton.trans (List.mem_singleton.symm.trans List.mem_toFinset.symm)
    have h2 : ∀ a b : Fin (42 : ℕ), ({a, b} : Finset (Fin (42 : ℕ))) = [a, b].toFinset := fun a b =>
      Finset.ext fun x =>
        (Finset.mem_insert.trans (or_congr_right Finset.mem_singleton)).trans
          ((List.mem_cons.trans (or_congr_right List.mem_singleton)).symm.trans List.mem_toFinset.symm)
    hEx.elim fun x10 hx10 =>
      hx10.2.elim fun x11 hx11 =>
        (hExistsFalsePosIndep x2 x10 x11
          ⟨hWF, hOut,
            fun g v => Eq.subst (motive := fun s => x2.gateVal s g = Bool.false) (h1 v) (hSing g v),
            hDisj, hSz,
            fun u v huv => Eq.subst (motive := fun s => x2.eval s = Bool.true) (h2 u v) (hEdges u v huv),
            hx10.1, hx11.1,
            fun e he =>
              have h := hx11.2 e he
              ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
                Eq.subst
                  (motive := fun s =>
                    ∃ g ∈ x2.outGates,
                      Relation.ReflTransGen
                        (fun (a b : Fin x2.size) =>
                          (a ∈ x2.leftGates b ∨ a ∈ x2.rightGates b) ∧ x2.gateVal s b = Bool.true)
                        x10 g)
                  (h2 e.1 e.2) h.2.2.2.2⟩⟩).elim
          fun i hi => hExtendIndepToMax _ x2 i hi.1 hi.2
