import Mathlib.Combinatorics.SimpleGraph.Acyclic
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17467_2
    (hExtract :
      ∀ (x1 x2 : ℕ) (E : Finset (Fin x1 × Fin x2)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (PEqualNP.ReadTwo.Lin fun (a : Fin x1) (b : Fin x2) => (a, b) ∈ E) →
        PEqualNP.TopForm.IsAO2 (x1 + x2) C →
        PEqualNP.MetaComplexity.circuitFun (x1 + x2) C = PEqualNP.ReadTwo.fpl x1 (fun (a : Fin x1) (b : Fin x2) => (a, b) ∈ E) →
        ∃ (k : ℕ) (A : Fin k → Finset (Fin x1)) (B : Fin k → Finset (Fin x2)),
          (∀ i, (A i).Nonempty ∧ (B i).Nonempty) ∧
          (∀ i, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ E) ∧
          (∀ e ∈ E, ∃ i, e.1 ∈ A i ∧ e.2 ∈ B i) ∧
          (∑ i : Fin k, ((A i).card + (B i).card)) ≤ C.size + (1 : ℕ))
    (hCover :
      ∀ (x1 x2 : ℕ) (E : Finset (Fin x1 × Fin x2)) (k : ℕ)
        (A : Fin k → Finset (Fin x1)) (B : Fin k → Finset (Fin x2)),
        (PEqualNP.ReadTwo.Lin fun (a : Fin x1) (b : Fin x2) => (a, b) ∈ E) →
        (∀ i, (A i).Nonempty ∧ (B i).Nonempty) →
        (∀ i, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ E) →
        (∀ e ∈ E, ∃ i, e.1 ∈ A i ∧ e.2 ∈ B i) →
        ∃ (X : Finset (Fin x1)) (Y : Finset (Fin x2)),
          (∀ e ∈ E, e.1 ∈ X ∨ e.2 ∈ Y) ∧
          E.card + X.card + Y.card ≤ ∑ i : Fin k, ((A i).card + (B i).card))
    (hCore :
      ∀ (a b : ℕ),
        let T : Type := Finset (Fin a × Fin b);
        have comp : T → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun F C => PEqualNP.TopForm.IsAO2 (a + b) C ∧ PEqualNP.MetaComplexity.circuitFun (a + b) C = PEqualNP.ReadTwo.fpl a fun i j => (i, j) ∈ F;
        have leaf : T → Fin a × Fin b → Prop := fun F e => (∀ f ∈ F, f.1 = e.1 → f = e) ∨ ∀ f ∈ F, f.2 = e.2 → f = e;
        have P : T → Prop := fun E =>
          have G : SimpleGraph (Fin (a + b)) := SimpleGraph.fromRel fun u v => ∃ e ∈ E, u = Fin.castAdd b e.1 ∧ v = Fin.natAdd a e.2;
          (6 : ℕ) ≤ E.card ∧
            ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
              have S : Set (Fin a × Fin b) := {e | e ∈ E ∧ (leaf E e ∨ ∃ D, D.size < C.size ∧ comp (E.erase e) D)};
              C.size + (3 : ℕ) ≤ (2 : ℕ) * E.card ∧ comp E C ∧
              (PEqualNP.ReadTwo.Lin fun i j => (i, j) ∈ E) ∧ ¬G.IsAcyclic ∧
              (∀ (v : Fin (a + b)),
                have d : ℕ := (G.neighborSet v).ncard;
                have R : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) C ↑v;
                (2 : ℕ) ≤ d → R.card ≤ d ∧ (d = R.card → ∀ k ∈ R, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.readers (a + b) C k ⊆ R)) ∧
              Set.InjOn Prod.fst S ∧ Set.InjOn Prod.snd S;
        ∀ (E : T) (X : Finset (Fin a)) (Y : Finset (Fin b)),
          P E → (∃ e ∈ E, leaf E e) →
          (∀ e ∈ E, e.1 ∈ X ∨ e.2 ∈ Y) →
          X.card + Y.card + (2 : ℕ) ≤ E.card →
          ∃ E' ⊂ E, P E') :
    (∀ (x1 x2 : ℕ),   have x3 : Finset (Fin x1 × Fin x2) → SimpleGraph (Fin (x1 + x2)) := fun (x3 : Finset (Fin x1 × Fin x2)) => SimpleGraph.fromRel fun (x4 x5 : Fin (x1 + x2)) => ∃ x6 ∈ x3, x4 = Fin.castAdd x2 x6.1 ∧ x5 = Fin.natAdd x1 x6.2;   have x4 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x5 ∧ PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 = PEqualNP.ReadTwo.fpl x1 fun (x6 : Fin x1) (x7 : Fin x2) => (x6, x7) ∈ x4;   have x5 : Finset (Fin x1 × Fin x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Finset (Fin x1 × Fin x2)) (x6 : Fin x1 × Fin x2) => (∀ x7 ∈ x5, x7.1 = x6.1 → x7 = x6) ∨ ∀ x7 ∈ x5, x7.2 = x6.2 → x7 = x6;   have x6 : Finset (Fin x1 × Fin x2) → Prop := fun (x6 : Finset (Fin x1 × Fin x2)) =>     (6 : ℕ) ≤ x6.card ∧       ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit),         have x8 : Set (Fin x1 × Fin x2) := {x8 : Fin x1 × Fin x2 | x8 ∈ x6 ∧ (x5 x6 x8 ∨ ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), x9.size < x7.size ∧ x4 (x6.erase x8) x9)};         x7.size + (3 : ℕ) ≤ (2 : ℕ) * x6.card ∧           x4 x6 x7 ∧             (PEqualNP.ReadTwo.Lin fun (x9 : Fin x1) (x10 : Fin x2) => (x9, x10) ∈ x6) ∧               ¬(x3 x6).IsAcyclic ∧                 (∀ (x9 : Fin (x1 + x2)),                     have x10 : ℕ := ((x3 x6).neighborSet x9).ncard;                     have x11 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) x7 ↑x9;                     (2 : ℕ) ≤ x10 → x11.card ≤ x10 ∧ (x10 = x11.card → ∀ x14 ∈ x11, (PEqualNP.MetaComplexity.NestedCover.gateAt x7 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.TopForm.readers (x1 + x2) x7 x14 ⊆ x11)) ∧                   Set.InjOn Prod.fst x8 ∧ Set.InjOn Prod.snd x8;   ∀ (x7 : Finset (Fin x1 × Fin x2)), x6 x7 → (∃ x9 ∈ x7, x5 x7 x9) → ∃ x10 ⊂ x7, x6 x10) := by
  intro x1 x2 x3 x4 x5 x6 E h6 hLeaf
  obtain ⟨hCard, C, hSz, hComp, hLin, hNA, hR, hInj1, hInj2⟩ := h6
  obtain ⟨k, A, B, hNE, hSub, hCov, hSum⟩ := hExtract x1 x2 E C hLin hComp.1 hComp.2
  obtain ⟨X, Y, hXY, hBound⟩ := hCover x1 x2 E k A B hLin hNE hSub hCov
  exact hCore x1 x2 E X Y ⟨hCard, C, hSz, hComp, hLin, hNA, hR, hInj1, hInj2⟩ hLeaf hXY (by omega)
