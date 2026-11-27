import PEqualNP.Defs

-- Dual intersection bound plus monotone gate-op normalization (.eval [true, false] -> .or via GateOp.casesOn, size = |or| + |and|).
theorem PEqualNP.Outside.R_meta_9002_3
    (hDualInter :
      ∀ (n q : ℕ) (R : Fin n → Fin n → Prop) [DecidableRel R],
        (∀ p1 p2 : Fin n, p1 ≠ p2 → ∃! l : Fin n, R p1 l ∧ R p2 l) →
        ∀ l1 l2 : Fin n, l1 ≠ l2 → Fintype.card { p : Fin n // R p l1 ∧ R p l2 } ≤ (1 : ℕ))
    (hNormalized :
      ∀ (q n : ℕ) (R : Fin n → Fin n → Prop) [DecidableRel R]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        (200 : ℕ) ≤ q →
        n = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ l : Fin n, Fintype.card { p : Fin n // R p l } = q + (1 : ℕ)) →
        (∀ p1 p2 : Fin n, p1 ≠ p2 → ∃! l : Fin n, R p1 l ∧ R p2 l) →
        (∀ l1 l2 : Fin n, l1 ≠ l2 → Fintype.card { p : Fin n // R p l1 ∧ R p l2 } ≤ (1 : ℕ)) →
        (∀ g ∈ C.gates,
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          g.inputs.length ≤ (2 : ℕ)) →
        (∀ p l : Fin n, R p l →
          (PEqualNP.MetaComplexity.circuitFun (n + n) C fun i =>
            Decidable.decide (i = Fin.castAdd n p ∨ i = Fin.natAdd n l)) = Bool.true) →
        (∀ f : Fin (n + n) → Bool,
          Fintype.card { l : Fin n // f (Fin.natAdd n l) = Bool.true } ≤ q →
          (¬∃ p l : Fin n, R p l ∧ f (Fin.castAdd n p) = Bool.true ∧ f (Fin.natAdd n l) = Bool.true) →
          PEqualNP.MetaComplexity.circuitFun (n + n) C f = Bool.false) →
        have orCount : ℕ :=
          (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate =>
            PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => Bool)
              g.op Bool.false Bool.true Bool.false (fun _ => Bool.false) Bool.false) C.gates).length;
        (2 : ℕ) * q ^ (2 : ℕ) + (1 : ℕ) ≤ orCount →
        (100 : ℕ) * (orCount + (q + (1 : ℕ)) / (2 : ℕ)) < n * q →
        n * q ≤ (100 : ℕ) * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3]
      (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      (200 : ℕ) ≤ x1 →
      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
      (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →
      PEqualNP.MetaComplexity.Monotone2 x5 →
      (∀ (x11 x12 : Fin x2), x3 x11 x12 →
        (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) =>
          Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) →
      (∀ (x12 : Fin (x2 + x2) → Bool),
        Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 →
        (¬∃ (x14 : Fin x2) (x15 : Fin x2),
          x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) →
        PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) →
      have x13 : ℕ :=
        (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) =>
          x13.op.eval [Bool.true, Bool.false]) x5.gates).length;
      have x14 : ℕ :=
        (List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) =>
          !x14.op.eval [Bool.true, Bool.false]) x5.gates).length;
      (2 : ℕ) * x1 ^ (2 : ℕ) + (1 : ℕ) ≤ x13 →
      (100 : ℕ) * (x13 + (x1 + (1 : ℕ)) / (2 : ℕ)) < x2 * x1 →
      x2 * x1 ≤ (100 : ℕ) * (x13 + x14) := by
  intro x1 x2 x3 _ x5 hq hn hdeg huniq hmono htrue hfalse x13 x14 h13 hlt
  have hmono' : ∀ g ∈ x5.gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    rcases hmono g hg with ⟨hop, hlen⟩
    exact ⟨by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hop, hlen⟩
  let isOr : PEqualNP.CircuitLowerBounds.Gate → Bool := fun g =>
    PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => Bool)
      g.op Bool.false Bool.true Bool.false (fun _ => Bool.false) Bool.false
  have horEq :
      (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate =>
        g.op.eval [Bool.true, Bool.false]) x5.gates) =
      (List.filter isOr x5.gates) := by
    suffices h : ∀ gs : List PEqualNP.CircuitLowerBounds.Gate,
        (∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        gs.filter (fun g => g.op.eval [Bool.true, Bool.false]) =
          gs.filter isOr by
      exact h x5.gates (fun g hg => (hmono' g hg).1)
    intro gs hgs
    induction gs with
    | nil => rfl
    | cons g gs ih =>
      have ih' := ih (fun g' hg' => hgs g' (by simp [hg']))
      rcases hgs g (by simp) with hop | hop
      · rw [List.filter_cons, List.filter_cons]
        have hev : g.op.eval [Bool.true, Bool.false] = Bool.false := by
          rw [hop]; rfl
        have his : isOr g = Bool.false := by
          dsimp [isOr]; rw [hop]
        rw [hev, his]
        exact ih'
      · rw [List.filter_cons, List.filter_cons]
        have hev : g.op.eval [Bool.true, Bool.false] = Bool.true := by
          rw [hop]; rfl
        have his : isOr g = Bool.true := by
          dsimp [isOr]; rw [hop]
        rw [hev, his]
        exact congrArg (g :: ·) ih'
  have hsum :
      (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate =>
        g.op.eval [Bool.true, Bool.false]) x5.gates).length +
      (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate =>
        !g.op.eval [Bool.true, Bool.false]) x5.gates).length = x5.size := by
    change _ = x5.gates.length
    induction x5.gates with
    | nil => rfl
    | cons g gs ih =>
      cases h : g.op.eval [Bool.true, Bool.false] <;> simp [h, ih] <;> omega
  have hx13 : x13 = (List.filter isOr x5.gates).length := by
    change (List.filter (fun g : PEqualNP.CircuitLowerBounds.Gate =>
      g.op.eval [Bool.true, Bool.false]) x5.gates).length = _
    rw [horEq]
  have hinter : ∀ l1 l2 : Fin x2, l1 ≠ l2 →
      Fintype.card { p : Fin x2 // x3 p l1 ∧ x3 p l2 } ≤ 1 :=
    hDualInter x2 x1 x3 huniq
  have h13' : (2 : ℕ) * x1 ^ (2 : ℕ) + (1 : ℕ) ≤ (List.filter isOr x5.gates).length := by
    rw [← hx13]; exact h13
  have hlt' : (100 : ℕ) * ((List.filter isOr x5.gates).length + (x1 + (1 : ℕ)) / (2 : ℕ)) < x2 * x1 := by
    rw [← hx13]; exact hlt
  have hres := hNormalized x1 x2 x3 x5 hq hn hdeg huniq hinter hmono' htrue hfalse h13' hlt'
  rw [← hsum] at hres
  exact hres
