import Mathlib.Combinatorics.SimpleGraph.Acyclic
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17465_3
    (hNoShrink :
      ∀ (x1 x2 : ℕ) (E : Finset (Fin x1 × Fin x2)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        have G : SimpleGraph (Fin (x1 + x2)) := SimpleGraph.fromRel fun (u v : Fin (x1 + x2)) => ∃ e ∈ E, u = Fin.castAdd x2 e.1 ∧ v = Fin.natAdd x1 e.2;
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
        (∀ e ∈ E, ∀ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (x1 + x2) C' → PEqualNP.MetaComplexity.circuitFun (x1 + x2) C' = PEqualNP.ReadTwo.fpl x1 (fun (a : Fin x1) (b : Fin x2) => (a, b) ∈ E.erase e) → C.size ≤ C'.size) →
        False)
    (hHasShrink :
      ∀ (x1 x2 : ℕ) (E : Finset (Fin x1 × Fin x2)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        have G : SimpleGraph (Fin (x1 + x2)) := SimpleGraph.fromRel fun (u v : Fin (x1 + x2)) => ∃ e ∈ E, u = Fin.castAdd x2 e.1 ∧ v = Fin.natAdd x1 e.2;
        have S : Set (Fin x1 × Fin x2) := {e : Fin x1 × Fin x2 | e ∈ E ∧ ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, C'.size < C.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x2) C' ∧ PEqualNP.MetaComplexity.circuitFun (x1 + x2) C' = PEqualNP.ReadTwo.fpl x1 (fun (a : Fin x1) (b : Fin x2) => (a, b) ∈ E.erase e)};
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
        S.Nonempty →
        Set.InjOn Prod.fst S →
        Set.InjOn Prod.snd S →
        False) :
    ∀ (x1 x2 : ℕ),   have x3 : Finset (Fin x1 × Fin x2) → SimpleGraph (Fin (x1 + x2)) := fun (x3 : Finset (Fin x1 × Fin x2)) => SimpleGraph.fromRel fun (x4 x5 : Fin (x1 + x2)) => ∃ x6 ∈ x3, x4 = Fin.castAdd x2 x6.1 ∧ x5 = Fin.natAdd x1 x6.2;   have x4 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x5 ∧ PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 = PEqualNP.ReadTwo.fpl x1 fun (x6 : Fin x1) (x7 : Fin x2) => (x6, x7) ∈ x4;   have x5 : Finset (Fin x1 × Fin x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Finset (Fin x1 × Fin x2)) (x6 : Fin x1 × Fin x2) => (∀ x7 ∈ x5, x7.1 = x6.1 → x7 = x6) ∨ ∀ x7 ∈ x5, x7.2 = x6.2 → x7 = x6;   have x6 : Finset (Fin x1 × Fin x2) → Prop := fun (x6 : Finset (Fin x1 × Fin x2)) =>     (6 : ℕ) ≤ x6.card ∧       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit),         have x8 : Set (Fin x1 × Fin x2) := {x8 : Fin x1 × Fin x2 | x8 ∈ x6 ∧ (x5 x6 x8 ∨ ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x9.size < x7.size ∧ x4 (x6.erase x8) x9)};         x7.size + (3 : ℕ) ≤ (2 : ℕ) * x6.card ∧           x4 x6 x7 ∧             (PEqualNP.ReadTwo.Lin fun (x9 : Fin x1) (x10 : Fin x2) => (x9, x10) ∈ x6) ∧               ¬(x3 x6).IsAcyclic ∧                 (∀ (x9 : Fin (x1 + x2)),                     have x10 : ℕ := ((x3 x6).neighborSet x9).ncard;                     have x11 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) x7 ↑x9;                     (2 : ℕ) ≤ x10 → x11.card ≤ x10 ∧ (x10 = x11.card → ∀ x14 ∈ x11, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.readers (x1 + x2) x7 x14 ⊆ x11)) ∧                   Set.InjOn Prod.fst x8 ∧ Set.InjOn Prod.snd x8;   ∀ (x7 : Finset (Fin x1 × Fin x2)), (∀ x8 ∈ x7, ¬x5 x7 x8) → ¬x6 x7 := by
  classical
  intro x1 x2 x3 x4 x5 x6 E hNoDeg1 hE6
  rcases hE6 with ⟨hCard, C, hSz, hComp, hLin, hCyc, hFan, hInj1, hInj2⟩
  have hAO : PEqualNP.TopForm.IsAO2 (x1 + x2) C := hComp.1
  have hFun : PEqualNP.MetaComplexity.circuitFun (x1 + x2) C =
      PEqualNP.ReadTwo.fpl x1 (fun (a : Fin x1) (b : Fin x2) => (a, b) ∈ E) := hComp.2
  let S : Set (Fin x1 × Fin x2) :=
    {e : Fin x1 × Fin x2 | e ∈ E ∧ ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, C'.size < C.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x2) C' ∧ PEqualNP.MetaComplexity.circuitFun (x1 + x2) C' = PEqualNP.ReadTwo.fpl x1 (fun (a : Fin x1) (b : Fin x2) => (a, b) ∈ E.erase e)}
  have hSub : S ⊆ {x8 : Fin x1 × Fin x2 | x8 ∈ E ∧ (x5 E x8 ∨ ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x9.size < C.size ∧ x4 (E.erase x8) x9)} :=
    fun _ he => ⟨he.1, Or.inr he.2⟩
  by_cases hSne : S.Nonempty
  · exact hHasShrink x1 x2 E C hCard hNoDeg1 hSz hAO hFun hLin hCyc hFan hSne (hInj1.mono hSub) (hInj2.mono hSub)
  · have hMin : ∀ e ∈ E, ∀ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (x1 + x2) C' →
        PEqualNP.MetaComplexity.circuitFun (x1 + x2) C' = PEqualNP.ReadTwo.fpl x1 (fun (a : Fin x1) (b : Fin x2) => (a, b) ∈ E.erase e) →
        C.size ≤ C'.size := by
      intro e he C' hAO' hFun'
      by_contra hlt
      exact hSne ⟨e, he, C', Nat.lt_of_not_le hlt, hAO', hFun'⟩
    exact hNoShrink x1 x2 E C hCard hNoDeg1 hSz hAO hFun hLin hCyc hFan hMin
