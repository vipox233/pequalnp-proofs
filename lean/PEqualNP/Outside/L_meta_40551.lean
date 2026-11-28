import PEqualNP.Defs
import PEqualNP.Outside.L_meta_32014

open scoped BigOperators

namespace PEqualNP.Outside.L_meta_40551

theorem methods_32022_from_32014 (hprev : ∀ (N t B : ℕ), 8 ≤ N → t ≤ N →
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (h : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N+h) C ∧ C.output < N+N+h+C.size ∧
    ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))
  let uses := fun (C : Circ) (j : ℕ) => C.output = j ∨ ∃ g ∈ C.gates, j ∈ g.inputs
  let named := fun (C : Circ) (R S : Finset X) =>
    (∀ x : X, uses C x.val → x ∈ R) ∧ (∀ y : X, uses C (N+y.val) → y ∈ S)
  let table := fun (h : ℕ) (C : Circ) (w : Fin h → Bool) (x y : X) =>
    C.eval (PEqualNP.Represents.oneEach x y ++ List.ofFn w)
  let code := fun (h j : ℕ) (i : Fin h) => j.testBit i.val
  let loss := fun (H : X → X → Bool) (U : Finset X) =>
    ((Finset.univ : Finset (X × X)).filter (fun z =>
      H z.1 z.2 ≠ decide (z.2-z.1 ∈ U))).card
  let fits := fun (h : ℕ) (C : Circ) (budget : ℕ) =>
    legal h C ∧ (∃ R S : Finset X, named C R S ∧ R.card+S.card ≤ budget) ∧
    ∀ w : Fin h → Bool, loss (table h C w) ∅ ≤ 1
  let K := min N (B^2/4)
  let value := ((N*t : ℕ) : ℝ) - ((K-2*(N-t) : ℕ) : ℝ)/(K : ℝ)
  (∀ (h : ℕ) (C : Circ) (P : (Fin h → Bool) → ℝ),
    fits h C B → (∀ w, 0 ≤ P w) → (∑ w, P w) = 1 →
    ∃ U : Finset X, U.card = t ∧ value ≤ ∑ w, P w * (loss (table h C w) U : ℝ)) ∧
  (∃ (p h : ℕ) (C : Circ), 0 < p ∧ p ≤ N ∧ p ≤ 2^h ∧ 2^h ≤ 2*p ∧
    fits h C B ∧ C.size ≤ 10*p+h+2 ∧
    ∀ U : Finset X, U.card = t →
      (∑ j : Fin p, (loss (table h C (code h j.val)) U : ℝ))/(p : ℝ) ≤ value) ∧
  ∀ a : ℕ, N = 2^(2*a) → N < 2*t → t < N →
    let r := 2^a
    let h := 2*a
    let ideal := ((N*t : ℕ) : ℝ) - ((2*t-N : ℕ) : ℝ)/(N : ℝ)
    let risk := fun (C : Circ) (U : Finset X) =>
      (∑ w : Fin h → Bool, (loss (table h C w) U : ℝ))/(N : ℝ)
    (∀ C : Circ, legal h C → (∀ w : Fin h → Bool, loss (table h C w) ∅ ≤ 1) →
      (∀ U : Finset X, U.card = t → risk C U ≤ ideal) → 2*r+h ≤ C.size+1) ∧
    ∃ C : Circ, fits h C (2*r) ∧ C.size ≤ 6*(r-1)+h+1 ∧
      ∀ U : Finset X, U.card = t → risk C U = ideal) : ¬ (let N : ℕ := 16
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (h : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N+h) C ∧ C.output < N+N+h+C.size ∧
    ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))
  let table := fun (h : ℕ) (C : Circ) (w : Fin h → Bool) (x y : X) =>
    C.eval (PEqualNP.Represents.oneEach x y ++ List.ofFn w)
  let loss := fun (H : X → X → Bool) (U : Finset X) =>
    ((Finset.univ : Finset (X × X)).filter (fun z =>
      H z.1 z.2 ≠ decide (z.2-z.1 ∈ U))).card
  ∃ C : Circ, legal 4 C ∧ C.size ≤ 10 ∧
    (∀ w : Fin 4 → Bool, loss (table 4 C w) ∅ ≤ 1) ∧
    ∀ U : Finset X, U.card = 9 →
      (∑ w : Fin 4 → Bool, loss (table 4 C w) U) ≤ 2302) := by
  classical
  intro witness
  obtain ⟨C, legal, size, emptyLoss, budget⟩ := witness
  have lower := ((hprev 16 9 0 (by decide) (by decide)).2.2 2 (by decide) (by decide) (by decide)).1
  have gateBound := lower C legal emptyLoss (by
    intro U hU
    have hb := budget U hU
    push_cast at *
    norm_num [div_le_iff₀] at *
    exact_mod_cast hb)
  norm_num at gateBound
  omega

end PEqualNP.Outside.L_meta_40551

theorem PEqualNP.Outside.L_meta_40551 :
¬ (let N : ℕ := 16
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (h : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N+h) C ∧ C.output < N+N+h+C.size ∧
    ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))
  let table := fun (h : ℕ) (C : Circ) (w : Fin h → Bool) (x y : X) =>
    C.eval (PEqualNP.Represents.oneEach x y ++ List.ofFn w)
  let loss := fun (H : X → X → Bool) (U : Finset X) =>
    ((Finset.univ : Finset (X × X)).filter (fun z =>
      H z.1 z.2 ≠ decide (z.2-z.1 ∈ U))).card
  ∃ C : Circ, legal 4 C ∧ C.size ≤ 10 ∧
    (∀ w : Fin 4 → Bool, loss (table 4 C w) ∅ ≤ 1) ∧
    ∀ U : Finset X, U.card = 9 →
      (∑ w : Fin 4 → Bool, loss (table 4 C w) U) ≤ 2302) :=
  PEqualNP.Outside.L_meta_40551.methods_32022_from_32014 PEqualNP.Outside.L_meta_32014
