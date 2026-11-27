import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17625_3
    (hBicliqueExtract :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        G.IsBipartite →
        ¬G.IsAcyclic →
        PEqualNP.TopForm.NoFourCycle G →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (∃ j < C.size,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ¬PEqualNP.TopForm.BelowF G C j ∧
          ∃ (e1 e2 : Fin n × Fin n),
            s(e1.1, e1.2) ≠ s(e2.1, e2.2) ∧
            ∀ e ∈ [e1, e2],
              G.Adj e.1 e.2 ∧
              PEqualNP.ReadK.readsAtMost C n [↑e.1, ↑e.2] (1 : ℕ) = Bool.false ∧
              PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput e.1 e.2) = Bool.true) →
        have refs : List ℕ := List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs C.gates;
        have inRefs : Finset ℕ := refs.toFinset.filter (fun w => w < n);
        ∃ (k : ℕ) (A B : Fin k → Finset (Fin n)),
          (∀ i, (A i).Nonempty ∧ (B i).Nonempty) ∧
          (∀ i, ∀ u ∈ A i, ∀ v ∈ B i, G.Adj u v) ∧
          (∀ u v, G.Adj u v → ∃ i, (u ∈ A i ∧ v ∈ B i) ∨ (v ∈ A i ∧ u ∈ B i)) ∧
          (∑ i : Fin k, ((A i).card + (B i).card)) ≤ inRefs.card + (refs.length - refs.toFinset.card))
    (hMatchingBicliqueBound :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (k : ℕ) (A B : Fin k → Finset (Fin n)),
        PEqualNP.TopForm.NoFourCycle G →
        (∀ i, (A i).Nonempty ∧ (B i).Nonempty) →
        (∀ i, ∀ u ∈ A i, ∀ v ∈ B i, G.Adj u v) →
        (∀ u v, G.Adj u v → ∃ i, (u ∈ A i ∧ v ∈ B i) ∨ (v ∈ A i ∧ u ∈ B i)) →
        ∀ (M : Finset (Fin n)) (mate : ↥M → Fin n),
          Function.Injective mate →
          (∀ (a : ↥M), mate a ∉ M ∧ G.Adj (↑a) (mate a)) →
          G.edgeFinset.card + M.card ≤ ∑ i : Fin k, ((A i).card + (B i).card)) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x2.IsBipartite →     ¬x2.IsAcyclic →       PEqualNP.TopForm.NoFourCycle x2 →         PEqualNP.TopForm.IsLeastAO x2 x4 →           PEqualNP.TopForm.TopForm x2 x4 →             (∃ x10 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.BelowF x2 x4 x10 ∧ ∃ (x11 : Fin x1 × Fin x1) (x12 : Fin x1 × Fin x1), s(x11.1, x11.2) ≠ s(x12.1, x12.2) ∧ ∀ x13 ∈ [x11, x12], x2.Adj x13.1 x13.2 ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x13.1, ↑x13.2] (1 : ℕ) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x13.1 x13.2) = Bool.true) →               ∀ (x11 : Finset (Fin x1)) (x12 : ↥x11 → Fin x1),                 Function.Injective x12 →                   (∀ (x14 : ↥x11), x12 x14 ∉ x11 ∧ x2.Adj (↑x14) (x12 x14)) →                     have x15 : List ℕ := List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates;                     have x16 : Finset ℕ := {x16 ∈ x15.toFinset | x16 < x1};                     x2.edgeFinset.card + x11.card - x16.card ≤ x15.length - x15.toFinset.card) :=
  fun x1 x2 _ x4 hBip hCyc hC4 hLeast hTop hWit M mate hInj hEdges =>
    Exists.elim (hBicliqueExtract x1 x2 x4 hBip hCyc hC4 hLeast hTop hWit) fun k hk =>
      Exists.elim hk fun A hA =>
        Exists.elim hA fun B hB =>
          Nat.sub_le_iff_le_add'.mpr
            (Nat.le_trans
              (hMatchingBicliqueBound x1 x2 k A B hC4 hB.1 hB.2.1 hB.2.2.1 M mate hInj hEdges)
              hB.2.2.2)
