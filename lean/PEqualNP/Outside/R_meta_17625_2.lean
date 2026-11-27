import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17625_2
    (hAccount :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle G →
        G.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        G.edgeFinset.card +
          (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
          (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card +
          (PEqualNP.TopForm.junk G C).card +
          (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
          C.size + (PEqualNP.TopForm.Ustar G C).card + (1 : ℕ))
    (hUstarCharge :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        G.IsBipartite →
        ¬G.IsAcyclic →
        PEqualNP.TopForm.NoFourCycle G →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (∃ x10 < C.size,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ¬PEqualNP.TopForm.BelowF G C x10 ∧
          ∃ (x11 : Fin n × Fin n) (x12 : Fin n × Fin n),
            s(x11.1, x11.2) ≠ s(x12.1, x12.2) ∧
            ∀ x13 ∈ [x11, x12],
              G.Adj x13.1 x13.2 ∧
              PEqualNP.ReadK.readsAtMost C n [↑x13.1, ↑x13.2] (1 : ℕ) = Bool.false ∧
              PEqualNP.EdgeOwnership.gateVal n C x10 (PEqualNP.EdgeOwnership.pairInput x13.1 x13.2) = Bool.true) →
        ∀ (M : Finset (Fin n)) (mate : ↥M → Fin n),
          Function.Injective mate →
          (∀ (a : ↥M), mate a ∉ M ∧ G.Adj (↑a) (mate a)) →
          (PEqualNP.TopForm.Ustar G C).card + M.card ≤
            (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
            (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card +
            (PEqualNP.TopForm.junk G C).card +
            (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card)
    (hWireBudget :
      ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 n C →
        (0 : ℕ) < C.size →
        let refs := C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs
        let inputRefs := refs.toFinset.filter (fun w => w < n)
        C.size + (1 : ℕ) ≤ inputRefs.card + (refs.length - refs.toFinset.card)) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x2.IsBipartite →     ¬x2.IsAcyclic →       PEqualNP.TopForm.NoFourCycle x2 →         PEqualNP.TopForm.IsLeastAO x2 x4 →           PEqualNP.TopForm.TopForm x2 x4 →             (∃ x10 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.BelowF x2 x4 x10 ∧ ∃ (x11 : Fin x1 × Fin x1) (x12 : Fin x1 × Fin x1), s(x11.1, x11.2) ≠ s(x12.1, x12.2) ∧ ∀ x13 ∈ [x11, x12], x2.Adj x13.1 x13.2 ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x13.1, ↑x13.2] (1 : ℕ) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x13.1 x13.2) = Bool.true) →               ∀ (x11 : Finset (Fin x1)) (x12 : ↥x11 → Fin x1),                 Function.Injective x12 →                   (∀ (x14 : ↥x11), x12 x14 ∉ x11 ∧ x2.Adj (↑x14) (x12 x14)) →                     have x15 : List ℕ := List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates;                     have x16 : Finset ℕ := {x16 ∈ x15.toFinset | x16 < x1};                     x2.edgeFinset.card + x11.card - x16.card ≤ x15.length - x15.toFinset.card) := by
  classical
  intro x1 x2 x3 x4 hBip hCyc hC4 hLeast hTop hWit x11 x12 hInj hEdges
  have hPos : (0 : ℕ) < x4.size := Nat.zero_lt_of_lt hWit.choose_spec.1
  have hNE : x2.edgeFinset.Nonempty := by
    have hEx := hWit.choose_spec.2.2.2
    exact ⟨s(hEx.choose.1, hEx.choose.2),
      SimpleGraph.mem_edgeFinset.mpr (hEx.choose_spec.choose_spec.2 hEx.choose List.mem_cons_self).1⟩
  have hAcc := @hAccount x1 x2 x3 x4 hC4 hNE hLeast hTop
  have hChg := @hUstarCharge x1 x2 x3 x4 hBip hCyc hC4 hLeast hTop hWit x11 x12 hInj hEdges
  have hWire := hWireBudget x1 x4 hLeast.1 hPos
  dsimp only at hWire ⊢
  omega
