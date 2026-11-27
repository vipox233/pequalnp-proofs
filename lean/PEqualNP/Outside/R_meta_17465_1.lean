import Mathlib.Combinatorics.SimpleGraph.Acyclic
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17465_1
    (hExtract : ∀ (x1 x2 : ℕ) (E : Finset (Fin x1 × Fin x2)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (PEqualNP.ReadTwo.Lin fun (a : Fin x1) (b : Fin x2) => (a, b) ∈ E) →
      PEqualNP.TopForm.IsAO2 (x1 + x2) C →
      PEqualNP.MetaComplexity.circuitFun (x1 + x2) C = PEqualNP.ReadTwo.fpl x1 (fun (a : Fin x1) (b : Fin x2) => (a, b) ∈ E) →
      ∃ (k : ℕ) (A : Fin k → Finset (Fin x1)) (B : Fin k → Finset (Fin x2)),
        (∀ i, (A i).Nonempty ∧ (B i).Nonempty) ∧
        (∀ i, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ E) ∧
        (∀ e ∈ E, ∃ i, e.1 ∈ A i ∧ e.2 ∈ B i) ∧
        (∑ i : Fin k, ((A i).card + (B i).card)) ≤ C.size + (1 : ℕ))
    (hCover : ∀ (x1 x2 : ℕ) (E : Finset (Fin x1 × Fin x2)) (k : ℕ)
      (A : Fin k → Finset (Fin x1)) (B : Fin k → Finset (Fin x2)),
      (PEqualNP.ReadTwo.Lin fun (a : Fin x1) (b : Fin x2) => (a, b) ∈ E) →
      (∀ i, (A i).Nonempty ∧ (B i).Nonempty) →
      (∀ i, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ E) →
      (∀ e ∈ E, ∃ i, e.1 ∈ A i ∧ e.2 ∈ B i) →
      ∃ (X : Finset (Fin x1)) (Y : Finset (Fin x2)),
        (∀ e ∈ E, e.1 ∈ X ∨ e.2 ∈ Y) ∧
        E.card + X.card + Y.card ≤ ∑ i : Fin k, ((A i).card + (B i).card))
    (hCore : ∀ (x1 x2 : ℕ) (E : Finset (Fin x1 × Fin x2)) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (X : Finset (Fin x1)) (Y : Finset (Fin x2)),
      have G : SimpleGraph (Fin (x1 + x2)) := SimpleGraph.fromRel fun (u v : Fin (x1 + x2)) => ∃ e ∈ E, u = Fin.castAdd x2 e.1 ∧ v = Fin.natAdd x1 e.2;
      have S : Set (Fin x1 × Fin x2) := {e : Fin x1 × Fin x2 | e ∈ E ∧ ∃ (C' : PEqualNP.CircuitLowerBounds.Circuit), C'.size < C.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x2) C' ∧ PEqualNP.MetaComplexity.circuitFun (x1 + x2) C' = PEqualNP.ReadTwo.fpl x1 (fun (a : Fin x1) (b : Fin x2) => (a, b) ∈ E.erase e)};
      (6 : ℕ) ≤ E.card →
      (∀ e ∈ E, ¬((∀ e' ∈ E, e'.1 = e.1 → e' = e) ∨ ∀ e' ∈ E, e'.2 = e.2 → e' = e)) →
      C.size + (3 : ℕ) ≤ (2 : ℕ) * E.card →
      PEqualNP.TopForm.IsAO2 (x1 + x2) C →
      PEqualNP.MetaComplexity.circuitFun (x1 + x2) C = PEqualNP.ReadTwo.fpl x1 (fun (a : Fin x1) (b : Fin x2) => (a, b) ∈ E) →
      (PEqualNP.ReadTwo.Lin fun (a : Fin x1) (b : Fin x2) => (a, b) ∈ E) →
      ¬G.IsAcyclic →
      (∀ (v : Fin (x1 + x2)),
        have d : ℕ := (G.neighborSet v).ncard;
        have r : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) C ↑v;
        (2 : ℕ) ≤ d → r.card ≤ d ∧ (d = r.card → ∀ g ∈ r, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.readers (x1 + x2) C g ⊆ r)) →
      Set.InjOn Prod.fst S →
      Set.InjOn Prod.snd S →
      (∀ e ∈ E, e.1 ∈ X ∨ e.2 ∈ Y) →
      E.card + X.card + Y.card ≤ C.size + (1 : ℕ) →
      X.card + Y.card + (2 : ℕ) ≤ E.card →
      False) :
    (∀ (x1 x2 : ℕ),   have x3 : Finset (Fin x1 × Fin x2) → SimpleGraph (Fin (x1 + x2)) := fun (x3 : Finset (Fin x1 × Fin x2)) => SimpleGraph.fromRel fun (x4 x5 : Fin (x1 + x2)) => ∃ x6 ∈ x3, x4 = Fin.castAdd x2 x6.1 ∧ x5 = Fin.natAdd x1 x6.2;   have x4 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x5 ∧ PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 = PEqualNP.ReadTwo.fpl x1 fun (x6 : Fin x1) (x7 : Fin x2) => (x6, x7) ∈ x4;   have x5 : Finset (Fin x1 × Fin x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Finset (Fin x1 × Fin x2)) (x6 : Fin x1 × Fin x2) => (∀ x7 ∈ x5, x7.1 = x6.1 → x7 = x6) ∨ ∀ x7 ∈ x5, x7.2 = x6.2 → x7 = x6;   have x6 : Finset (Fin x1 × Fin x2) → Prop := fun (x6 : Finset (Fin x1 × Fin x2)) =>     (6 : ℕ) ≤ x6.card ∧       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit),         have x8 : Set (Fin x1 × Fin x2) := {x8 : Fin x1 × Fin x2 | x8 ∈ x6 ∧ (x5 x6 x8 ∨ ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x9.size < x7.size ∧ x4 (x6.erase x8) x9)};         x7.size + (3 : ℕ) ≤ (2 : ℕ) * x6.card ∧           x4 x6 x7 ∧             (PEqualNP.ReadTwo.Lin fun (x9 : Fin x1) (x10 : Fin x2) => (x9, x10) ∈ x6) ∧               ¬(x3 x6).IsAcyclic ∧                 (∀ (x9 : Fin (x1 + x2)),                     have x10 : ℕ := ((x3 x6).neighborSet x9).ncard;                     have x11 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) x7 ↑x9;                     (2 : ℕ) ≤ x10 → x11.card ≤ x10 ∧ (x10 = x11.card → ∀ x14 ∈ x11, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.readers (x1 + x2) x7 x14 ⊆ x11)) ∧                   Set.InjOn Prod.fst x8 ∧ Set.InjOn Prod.snd x8;   ∀ (x7 : Finset (Fin x1 × Fin x2)), (∀ x8 ∈ x7, ¬x5 x7 x8) → ¬x6 x7) := by
  intro x1 x2 x3 x4 x5 x6 E hNoDeg1 hE6
  exact Exists.elim hE6.2 fun C hC =>
    have hSz : C.size + 3 ≤ 2 * E.card := hC.1
    have hAO : PEqualNP.TopForm.IsAO2 (x1 + x2) C := hC.2.1.1
    have hFun := hC.2.1.2
    have hLin := hC.2.2.1
    have hCyc := hC.2.2.2.1
    have hFan := hC.2.2.2.2.1
    have hInj1 := hC.2.2.2.2.2.1
    have hInj2 := hC.2.2.2.2.2.2
    have hSub : {e : Fin x1 × Fin x2 | e ∈ E ∧ ∃ (C' : PEqualNP.CircuitLowerBounds.Circuit), C'.size < C.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x2) C' ∧ PEqualNP.MetaComplexity.circuitFun (x1 + x2) C' = PEqualNP.ReadTwo.fpl x1 (fun (a : Fin x1) (b : Fin x2) => (a, b) ∈ E.erase e)} ⊆
        {x8 : Fin x1 × Fin x2 | x8 ∈ E ∧ (x5 E x8 ∨ ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x9.size < C.size ∧ x4 (E.erase x8) x9)} :=
      fun _ he => ⟨he.1, Or.inr he.2⟩
    Exists.elim (hExtract x1 x2 E C hLin hAO hFun) fun k hk =>
      Exists.elim hk fun A hA =>
        Exists.elim hA fun B hB =>
          Exists.elim (hCover x1 x2 E k A B hLin hB.1 hB.2.1 hB.2.2.1) fun X hX =>
            Exists.elim hX fun Y hY =>
              have hCost : ∑ i : Fin k, ((A i).card + (B i).card) ≤ C.size + 1 := hB.2.2.2
              have hVC : E.card + X.card + Y.card ≤ ∑ i : Fin k, ((A i).card + (B i).card) := hY.2
              hCore x1 x2 E C X Y hE6.1 hNoDeg1 hSz hAO hFun hLin hCyc hFan
                (hInj1.mono hSub) (hInj2.mono hSub) hY.1 (by omega) (by omega)
