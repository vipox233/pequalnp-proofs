import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18593_2
    (hStarCover :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle G →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        ∃ (V : Finset (Fin n)),
          (∀ e ∈ PEqualNP.TopForm.starEdges G C, ∃ v ∈ V, v ∈ e) ∧
          V.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card)
    (hUstarBudget :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        have J := PEqualNP.TopForm.junk G C;
        have O := (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card;
        have K := (PEqualNP.TopForm.centreless G C).card;
        have U := PEqualNP.TopForm.Ustar G C;
        G.IsBipartite → ¬G.IsAcyclic → PEqualNP.TopForm.NoFourCycle G →
        PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        (2 : ℕ) ≤ J.card → (1 : ℕ) ≤ O → (3 : ℕ) ≤ K + O →
        (5 : ℕ) ≤ (2 : ℕ) * K + J.card + O → (3 : ℕ) ≤ U.card →
        (∀ (W : Finset (Fin n)), (∀ e ∈ U, ∃ v ∈ W, v ∈ e) → (2 : ℕ) * K + J.card + O < W.card + U.card) →
        (∃ g ∈ J, ∃ (a b c d : Fin n), s(a, b) ∈ U ∧ s(c, d) ∈ U ∧ s(a, b) ≠ s(c, d) ∧ PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput a b) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput c d) = Bool.true) →
        ∃ (W : Finset (Fin n)),
          (∀ e ∈ U, ∃ v ∈ W, v ∈ e) ∧
          G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card + W.card ≤ C.size + (1 : ℕ)) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.IsBipartite → ¬x2.IsAcyclic → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (∀ (x10 : Finset (Fin x1)), x2.IsVertexCover ↑x10 → x4.size + (1 : ℕ) < x2.edgeFinset.card + x10.card) → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → (1 : ℕ) ≤ (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card → (3 : ℕ) ≤ (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card → (5 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x2 x4).card → (∀ (x16 : Finset (Fin x1)), (∀ x17 ∈ PEqualNP.TopForm.Ustar x2 x4, ∃ x19 ∈ x16, x19 ∈ x17) → (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card < x16.card + (PEqualNP.TopForm.Ustar x2 x4).card) → (∃ x17 ∈ PEqualNP.TopForm.junk x2 x4, ∃ (x18 : Fin x1) (x19 : Fin x1) (x20 : Fin x1) (x21 : Fin x1), s(x18, x19) ∈ PEqualNP.TopForm.Ustar x2 x4 ∧ s(x20, x21) ∈ PEqualNP.TopForm.Ustar x2 x4 ∧ s(x18, x19) ≠ s(x20, x21) ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x17 (PEqualNP.EdgeOwnership.pairInput x18 x19) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x17 (PEqualNP.EdgeOwnership.pairInput x20 x21) = Bool.true) → False) := by
  exact fun n G inst C hBip hNA hC4 hLeast hTF hVC hJ hO hCO hD hU hUcov hJunk =>
    Exists.elim (hStarCover n G C hC4 hLeast hTF) fun V1 hV1 =>
      Exists.elim (hUstarBudget n G C hBip hNA hC4 hLeast hTF hJ hO hCO hD hU hUcov hJunk) fun V2 hV2 =>
        have hCov : G.IsVertexCover ↑(V1 ∪ V2) := fun u v huv =>
          let he : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
          Or.elim (Decidable.em (s(u, v) ∈ PEqualNP.TopForm.starEdges G C))
            (fun hs => Exists.elim (hV1.1 s(u, v) hs) fun w hw =>
              Or.elim (Sym2.mem_iff.mp hw.2)
                (fun hwu => Or.inl (Finset.mem_coe.mpr (Finset.mem_union_left V2 (hwu ▸ hw.1))))
                (fun hwv => Or.inr (Finset.mem_coe.mpr (Finset.mem_union_left V2 (hwv ▸ hw.1)))))
            (fun hns => Exists.elim (hV2.1 s(u, v) (Finset.mem_sdiff.mpr ⟨he, hns⟩)) fun w hw =>
              Or.elim (Sym2.mem_iff.mp hw.2)
                (fun hwu => Or.inl (Finset.mem_coe.mpr (Finset.mem_union_right V1 (hwu ▸ hw.1))))
                (fun hwv => Or.inr (Finset.mem_coe.mpr (Finset.mem_union_right V1 (hwv ▸ hw.1)))))
        have hCard : G.edgeFinset.card + (V1 ∪ V2).card ≤ C.size + (1 : ℕ) :=
          le_trans (Nat.add_le_add_left (Finset.card_union_le V1 V2) G.edgeFinset.card)
            (le_trans (Nat.add_assoc G.edgeFinset.card V1.card V2.card ▸
              Nat.add_le_add_right (Nat.add_le_add_left hV1.2 G.edgeFinset.card) V2.card)
              hV2.2)
        Nat.not_lt.mpr hCard (hVC (V1 ∪ V2) hCov)
