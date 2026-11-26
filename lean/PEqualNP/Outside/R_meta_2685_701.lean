import Mathlib
import PEqualNP.Defs

-- A cut of the two-level replacement statement along the lift move.
-- A gate is BELOW the function when its value is at most the value of the circuit, as functions.
-- Child 1 (lift, any AND/OR circuit of fan-in exactly two, any function): some no-larger circuit
-- for the same function has every gate below the function read only by OR gates that are below
-- the function (lift normal form); and if every AND gate of the given circuit is below the
-- function, the same holds in the new one.
-- Child 2 (the open part): a least circuit in lift normal form for a 4-cycle-free incidence that
-- has an AND gate not below the function has a no-larger replacement all of whose AND gates are
-- below the function.
-- Child 3 (star blocks): a circuit in lift normal form for an incidence function, all of whose
-- AND gates are below the function, is two-level: its AND gates read a point OR and a line OR.
theorem PEqualNP.Outside.R_meta_2685_701 :
    (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧
        PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧
        D.size ≤ C.size ∧
        (∀ i j : ℕ,
          PEqualNP.EdgeOwnership.gateVal n D i ≤ PEqualNP.MetaComplexity.circuitFun n D →
          n + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs →
          (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          PEqualNP.EdgeOwnership.gateVal n D j ≤ PEqualNP.MetaComplexity.circuitFun n D) ∧
        ((∀ j : ℕ,
            (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            PEqualNP.EdgeOwnership.gateVal n C j ≤ PEqualNP.MetaComplexity.circuitFun n C) →
          ∀ j : ℕ,
            (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            PEqualNP.EdgeOwnership.gateVal n D j ≤ PEqualNP.MetaComplexity.circuitFun n D)) →
    (∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      PEqualNP.TopForm.IsAO2 (Np + Nl) C →
      (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) →
      (∀ D' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (Np + Nl) D' →
        PEqualNP.MetaComplexity.circuitFun (Np + Nl) D' = PEqualNP.MetaComplexity.circuitFun (Np + Nl) C →
        C.size ≤ D'.size) →
      (∀ i j : ℕ,
        PEqualNP.EdgeOwnership.gateVal (Np + Nl) C i ≤ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C →
        Np + Nl + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        PEqualNP.EdgeOwnership.gateVal (Np + Nl) C j ≤ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C) →
      (∃ j : ℕ,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ¬ PEqualNP.EdgeOwnership.gateVal (Np + Nl) C j ≤ PEqualNP.MetaComplexity.circuitFun (Np + Nl) C) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (Np + Nl) D ∧
        PEqualNP.MetaComplexity.circuitFun (Np + Nl) D = PEqualNP.MetaComplexity.circuitFun (Np + Nl) C ∧
        D.size ≤ C.size ∧
        ∀ j : ℕ,
          (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          PEqualNP.EdgeOwnership.gateVal (Np + Nl) D j ≤ PEqualNP.MetaComplexity.circuitFun (Np + Nl) D) →
    (∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 (Np + Nl) D →
      (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) →
      (∀ i j : ℕ,
        PEqualNP.EdgeOwnership.gateVal (Np + Nl) D i ≤ PEqualNP.MetaComplexity.circuitFun (Np + Nl) D →
        Np + Nl + i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D j).inputs →
        (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        PEqualNP.EdgeOwnership.gateVal (Np + Nl) D j ≤ PEqualNP.MetaComplexity.circuitFun (Np + Nl) D) →
      (∀ j : ℕ,
        (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        PEqualNP.EdgeOwnership.gateVal (Np + Nl) D j ≤ PEqualNP.MetaComplexity.circuitFun (Np + Nl) D) →
      ∃ P L : Finset ℕ,
        (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧
        (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧
        ∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P))) →
    ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ), PEqualNP.TopForm.IsAO2 (Np + Nl) D ∧ (∀ y : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D y = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true)) ∧ D.size ≤ C.size ∧ (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧ ∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
  intro lift core star Np Nl I _ C hfree hAO hfun
  classical
  have hex : ∃ s : ℕ, ∃ E : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 (Np + Nl) E ∧
      PEqualNP.MetaComplexity.circuitFun (Np + Nl) E = PEqualNP.MetaComplexity.circuitFun (Np + Nl) C ∧
      E.size = s :=
    ⟨C.size, C, hAO, rfl, rfl⟩
  obtain ⟨C0, hC0AO, hC0fun, hC0size⟩ := Nat.find_spec hex
  have hmin : ∀ E : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (Np + Nl) E →
      PEqualNP.MetaComplexity.circuitFun (Np + Nl) E = PEqualNP.MetaComplexity.circuitFun (Np + Nl) C →
      C0.size ≤ E.size := by
    intro E h1 h2
    rw [hC0size]
    exact Nat.find_min' hex ⟨E, h1, h2, rfl⟩
  obtain ⟨D, hDAO, hDfun, hDsize, hDnormal, -⟩ := lift (Np + Nl) C0 hC0AO
  have hDC : PEqualNP.MetaComplexity.circuitFun (Np + Nl) D =
      PEqualNP.MetaComplexity.circuitFun (Np + Nl) C := hDfun.trans hC0fun
  have hDcomp : ∀ y : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D y =
      decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ y (Fin.castAdd Nl p) = true ∧
        y (Fin.natAdd Np l) = true) :=
    fun y => (congrFun hDC y).trans (hfun y)
  have hDle : D.size ≤ C.size := hDsize.trans (hmin C hAO rfl)
  have hDleast : ∀ E : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (Np + Nl) E →
      PEqualNP.MetaComplexity.circuitFun (Np + Nl) E = PEqualNP.MetaComplexity.circuitFun (Np + Nl) D →
      D.size ≤ E.size :=
    fun E h1 h2 => hDsize.trans (hmin E h1 (h2.trans hDC))
  by_cases hjunk : ∃ j : ℕ,
      (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      ¬ PEqualNP.EdgeOwnership.gateVal (Np + Nl) D j ≤ PEqualNP.MetaComplexity.circuitFun (Np + Nl) D
  · obtain ⟨E, hEAO, hEfun, hEsize, hEclean⟩ :=
      core Np Nl I D hfree hDAO hDcomp hDleast hDnormal hjunk
    obtain ⟨F, hFAO, hFfun, hFsize, hFnormal, hFclean⟩ := lift (Np + Nl) E hEAO
    have hFC : PEqualNP.MetaComplexity.circuitFun (Np + Nl) F =
        PEqualNP.MetaComplexity.circuitFun (Np + Nl) C := hFfun.trans (hEfun.trans hDC)
    have hFcomp : ∀ y : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) F y =
        decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ y (Fin.castAdd Nl p) = true ∧
          y (Fin.natAdd Np l) = true) :=
      fun y => (congrFun hFC y).trans (hfun y)
    obtain ⟨P, L, hP, hL, hAnd⟩ := star Np Nl I F hFAO hFcomp hFnormal (hFclean hEclean)
    exact ⟨F, P, L, hFAO, hFcomp, (hFsize.trans hEsize).trans hDle, hP, hL, hAnd⟩
  · have hclean : ∀ j : ℕ,
        (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        PEqualNP.EdgeOwnership.gateVal (Np + Nl) D j ≤ PEqualNP.MetaComplexity.circuitFun (Np + Nl) D := by
      intro j hop
      by_contra hne
      exact hjunk ⟨j, hop, hne⟩
    obtain ⟨P, L, hP, hL, hAnd⟩ := star Np Nl I D hDAO hDcomp hDnormal hclean
    exact ⟨D, P, L, hDAO, hDcomp, hDle, hP, hL, hAnd⟩
