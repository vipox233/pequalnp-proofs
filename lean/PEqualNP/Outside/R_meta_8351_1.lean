import Mathlib.Combinatorics.SimpleGraph.Girth
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8351_1
    (hOtherGate : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n) (g : ℕ),
      have ga := PEqualNP.MetaComplexity.NestedCover.gateAt C g;
      PEqualNP.MetaComplexity.IsMinimalCircuit n C ∧
      g < C.gates.length ∧
      (List.take (bif ga.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) ga.inputs).contains (↑v) = Bool.true ∧
      ga.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      (∀ (u : Fin n), u ≠ v → ¬ga.inputs.Perm [↑v, ↑u]) →
      ∃ h < g, ga.inputs.Perm [↑v, n + h])
    (hMain : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin x1) (g h : ℕ),
      have ga := PEqualNP.MetaComplexity.NestedCover.gateAt x5;
      have x6 := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;
      have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Bool := fun k gt => (List.take (bif gt.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) gt.inputs).contains k;
      have x9 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun u => List.filter (x7 ↑u) x5.gates;
      (∀ u ∉ x4, (x2.neighborSet u).ncard = (3 : ℕ)) ∧
      (7 : ℕ∞) ≤ x2.egirth ∧
      (∀ u w, x2.Adj u w → u ∉ x4) ∧
      PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 ∧
      PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 ∧
      (∀ u ∉ x4, (x9 u).length ≤ (3 : ℕ) ∧ ((x9 u).length = (3 : ℕ) → ∀ gt ∈ x9 u, gt.op = PEqualNP.CircuitLowerBounds.GateOp.or)) ∧
      v ∉ x4 ∧ g < x5.gates.length ∧ h < g ∧ (x9 v).length = (1 : ℕ) ∧
      (ga g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (ga g).inputs.Perm [↑v, x1 + h] ∧
      (¬∃ u ∉ x4, ∃ j < x5.gates.length, x7 (↑u) (ga j) = Bool.true ∧ (ga j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∧ (3 : ℕ) ≤ ({i ∈ Finset.range x5.gates.length | i ≠ j ∧ (x7 (↑u) (ga i) = Bool.true ∨ j < i ∧ x7 (x1 + j) (ga i) = Bool.true)}).card) →
      ∃ u ∉ x4, ∃ (k : ℕ), k + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun y => x6 (Function.update y u Bool.false)) k) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains x7;   have x8 : Fin x1 → ℕ → Finset ℕ := fun (x8 : Fin x1) (x9 : ℕ) => {x10 ∈ Finset.range x5.gates.length | x10 ≠ x9 ∧ (x7 (↑x8) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10) = Bool.true ∨ x9 < x10 ∧ x7 (x1 + x9) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10) = Bool.true)};   have x9 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x9 : Fin x1) => List.filter (x7 ↑x9) x5.gates;   (∀ x10 ∉ x4, (x2.neighborSet x10).ncard = (3 : ℕ)) → (7 : ℕ∞) ≤ x2.egirth → (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∉ x4) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ x15 ∉ x4, (x9 x15).length ≤ (3 : ℕ) ∧ ((x9 x15).length = (3 : ℕ) → ∀ x18 ∈ x9 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, ∃ x17 < x5.gates.length, (x9 x16).length = (1 : ℕ) ∧ x7 (↑x16) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x17) = Bool.true ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x17).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ (x18 : Fin x1), x18 ≠ x16 → ¬(PEqualNP.MetaComplexity.NestedCover.gateAt x5 x17).inputs.Perm [↑x16, ↑x18]) → (¬∃ x17 ∉ x4, ∃ x18 < x5.gates.length, x7 (↑x17) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x18) = Bool.true ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x18).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∧ (3 : ℕ) ≤ (x8 x17 x18).card) → ∃ x18 ∉ x4, ∃ (x19 : ℕ), x19 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x20 : Fin x1 → Bool) => x6 (Function.update x20 x18 Bool.false)) x19) := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 x9 hdeg hgirth hadj hmin hfun hfan hex hnobad
  rcases hex with ⟨v, hv, g, hg, hlen1, hread, hor, hnoperm⟩
  rcases hOtherGate x1 x5 v g ⟨hmin, hg, hread, hor, hnoperm⟩ with ⟨h, hlt, hperm⟩
  exact @hMain x1 x2 x3 x4 x5 v g h ⟨hdeg, hgirth, hadj, hmin, hfun, hfan, hv, hg, hlt, hlen1, hor, hperm, hnobad⟩
