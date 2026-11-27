import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18900_2
    (hGirth8ToNoC4C6 :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)),
        Disjoint A B ∧
        (∀ u v : Fin n, G.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)) ∧
        (∀ (u : Fin n) (w : G.Walk u u), w.IsCycle → 8 ≤ w.length) →
        (∀ a b c d : Fin n, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬G.Adj d a) ∧
        (∀ a b c d e f : Fin n, a ≠ c → a ≠ e → c ≠ e → b ≠ d → b ≠ f → d ≠ f →
          G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d e → G.Adj e f → ¬G.Adj f a))
    (hPairKillNoC4C6 :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (I A B : Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (Disjoint A B ∧ A ∪ B = Finset.univ \ I ∧ A.card = B.card ∧ 3 ≤ A.card ∧
         (∀ u v : Fin n, G.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)) ∧
         (∀ v ∉ I, (G.neighborSet v).ncard = 3) ∧
         (∀ a b c d : Fin n, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬G.Adj d a) ∧
         (∀ a b c d e f : Fin n, a ≠ c → a ≠ e → c ≠ e → b ≠ d → b ≠ f → d ≠ f →
           G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d e → G.Adj e f → ¬G.Adj f a) ∧
         PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧
         (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
         PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
         C.size + 1 < 4 * A.card) →
        ∃ (u v : Fin n), u ∉ I ∧ v ∉ I ∧ u ≠ v ∧ ¬G.Adj u v ∧
          ∃ (k : ℕ), k + 8 ≤ C.size ∧
            PEqualNP.MetaComplexity.HasCircuitSize n
              (fun y => PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (Function.update (Function.update y u false) v false)) k) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 x5 x6 : Finset (Fin x1)), Disjoint x5 x6 → x5 ∪ x6 = Finset.univ \ x4 → x5.card = x6.card → (3 : ℕ) ≤ x5.card → (∀ (x11 x12 : Fin x1), x2.Adj x11 x12 → x11 ∈ x5 ∧ x12 ∈ x6 ∨ x11 ∈ x6 ∧ x12 ∈ x5) → (∀ x12 ∉ x4, (x2.neighborSet x12).ncard = (3 : ℕ)) → (∀ (x13 : Fin x1) (x14 : x2.Walk x13 x13), x14.IsCycle → (8 : ℕ) ≤ x14.length) → ∀ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit x1 x14 → (∃ x16 ∈ x14.gates, x16.op = PEqualNP.CircuitLowerBounds.GateOp.not) → PEqualNP.MetaComplexity.circuitFun x1 x14 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x14.size + (1 : ℕ) < (4 : ℕ) * x5.card → ∃ (x19 : Fin x1) (x20 : Fin x1), x19 ∉ x4 ∧ x20 ∉ x4 ∧ x19 ≠ x20 ∧ ¬x2.Adj x19 x20 ∧ ∃ (x21 : ℕ), x21 + (8 : ℕ) ≤ x14.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x22 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ (Function.update (Function.update x22 x19 Bool.false) x20 Bool.false)) x21) :=
  fun n G _ I A B hDisj hUni hCard h3 hBip hDeg hGirth C hMin hNot hFun hSz =>
    let hNo := hGirth8ToNoC4C6 n G A B ⟨hDisj, hBip, hGirth⟩
    hPairKillNoC4C6 n G I A B C ⟨hDisj, hUni, hCard, h3, hBip, hDeg, hNo.1, hNo.2, hMin, hNot, hFun, hSz⟩
