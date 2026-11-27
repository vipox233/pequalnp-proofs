import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18794_2
    (hShift : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin (13 : ℕ)) (b : Bool),
      have σ : ℕ → ℕ := fun w =>
        if w < (13 : ℕ) then (w + s.val) % (13 : ℕ)
        else if w < (26 : ℕ) then (13 : ℕ) + (w - (13 : ℕ) + s.val) % (13 : ℕ)
        else w;
      have D : PEqualNP.CircuitLowerBounds.Circuit :=
        { gates := C.gates.map fun g => { op := g.op, inputs := g.inputs.map σ }, output := σ C.output };
      D.size = C.size ∧
      (PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.Monotone2 D) ∧
      (PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) D) ∧
      PEqualNP.TopForm.andPairs (27 : ℕ) D = PEqualNP.TopForm.andPairs (27 : ℕ) C ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt D (D.size - (1 : ℕ))).op =
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.size - (1 : ℕ))).op ∧
      ∀ (fA fB : Fin (13 : ℕ) → Bool),
        D.eval ((List.ofFn fA ++ List.ofFn fB) ++ [b]) =
          C.eval ((List.ofFn (fun i => fA (i + s)) ++ List.ofFn (fun j => fB (j + s))) ++ [b]))
    (hNormLB : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (d : Fin (13 : ℕ)) (b : Bool),
      have ev : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → Bool :=
        fun fA fB => C.eval ((List.ofFn fA ++ List.ofFn fB) ++ [b]);
      have inc : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool :=
        fun u v => [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains (u - v).val;
      PEqualNP.MetaComplexity.Monotone2 C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) C ∧
      (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (27 : ℕ) C ∧
      (∀ (a c : Fin (13 : ℕ)), inc a c = Bool.true → a ≠ d ∨ c ≠ (0 : Fin (13 : ℕ)) →
        ev (fun i => decide (i = a)) (fun j => decide (j = c)) = Bool.true) ∧
      (∀ (A B : Finset (Fin (13 : ℕ))), A.card = (4 : ℕ) →
        (∀ c : Fin (13 : ℕ), (A.filter (fun a => inc a c = Bool.true)).card ≤ (2 : ℕ)) →
        (∀ c : Fin (13 : ℕ), c ∈ B ↔ ∀ a ∈ A, inc a c = Bool.false) →
        ev (fun i => decide (i ∈ A)) (fun j => decide (j ∈ B)) = Bool.false) ∧
      (∀ (a1 a2 c1 c2 : Fin (13 : ℕ)),
        inc a1 c1 = Bool.false → inc a1 c2 = Bool.false → inc a2 c1 = Bool.false → inc a2 c2 = Bool.false →
        ev (fun i => decide (i = a1 ∨ i = a2)) (fun j => decide (j = c1 ∨ j = c2)) = Bool.false) ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C (C.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      (63 : ℕ) ≤ C.size) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 →       (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (27 : ℕ) x1 →         have x8 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → List Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => ((List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x9)) ++ List.ofFn fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x10)) ++ [x4];         (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x8 → x10 ≠ x2 ∨ x11 ≠ x3 → x1.eval (x9 {x10} {x11}) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) → (∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x11 | x14 - x13 ∈ x8}.card ≤ (2 : ℕ)) → x1.eval (x9 x11 {x14 : Fin (13 : ℕ) | ∀ x15 ∈ x11, x15 - x14 ∉ x8}) = Bool.false) → (∀ (x12 x13 x14 x15 : Fin (13 : ℕ)), x12 - x14 ∉ x8 → x12 - x15 ∉ x8 → x13 - x14 ∉ x8 → x13 - x15 ∉ x8 → x1.eval (x9 {x12, x13} {x14, x15}) = Bool.false) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or → (63 : ℕ) ≤ x1.size) := by
  intro C x2 x3 x4 hMono hRB hAP x8 x9 h1 h2 h3 hOr
  have hinc : ∀ u : Fin (13 : ℕ), u ∈ x8 ↔ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains u.val = Bool.true := by decide
  have hincF : ∀ u : Fin (13 : ℕ), u ∉ x8 ↔ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains u.val = Bool.false := by decide
  let σ : ℕ → ℕ := fun w =>
    if w < (13 : ℕ) then (w + (-x3).val) % (13 : ℕ)
    else if w < (26 : ℕ) then (13 : ℕ) + (w - (13 : ℕ) + (-x3).val) % (13 : ℕ)
    else w
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
    { gates := C.gates.map fun g => { op := g.op, inputs := g.inputs.map σ }, output := σ C.output }
  rcases hShift C (-x3) x4 with ⟨hsz, hMono', hRB', hAP', hOr', hEval⟩
  have h1' : ∀ (a c : Fin (13 : ℕ)), [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains (a - c).val = Bool.true →
      a ≠ x2 - x3 ∨ c ≠ (0 : Fin (13 : ℕ)) →
      D.eval ((List.ofFn (fun i => decide (i = a)) ++ List.ofFn (fun j => decide (j = c))) ++ [x4]) = Bool.true := by
    intro a c hac hne
    rw [hEval]
    have hfA : (fun i : Fin (13 : ℕ) => decide (i + -x3 = a)) = fun i => decide (i ∈ ({a + x3} : Finset (Fin (13 : ℕ)))) :=
      funext fun i => decide_eq_decide.mpr (add_neg_eq_iff_eq_add.trans Finset.mem_singleton.symm)
    have hfB : (fun j : Fin (13 : ℕ) => decide (j + -x3 = c)) = fun j => decide (j ∈ ({c + x3} : Finset (Fin (13 : ℕ)))) :=
      funext fun j => decide_eq_decide.mpr (add_neg_eq_iff_eq_add.trans Finset.mem_singleton.symm)
    rw [hfA, hfB]
    have hdiff : (a + x3) - (c + x3) ∈ x8 := by
      rw [add_sub_add_right_eq_sub, hinc]; exact hac
    have hne' : a + x3 ≠ x2 ∨ c + x3 ≠ x3 := Or.elim hne
      (fun ha => Or.inl fun h => ha (eq_sub_of_add_eq h))
      (fun hc => Or.inr fun h => hc (add_right_cancel (h.trans (zero_add x3).symm)))
    exact h1 (a + x3) (c + x3) hdiff hne'
  have h2' : ∀ (A B : Finset (Fin (13 : ℕ))), A.card = (4 : ℕ) →
      (∀ c : Fin (13 : ℕ), (A.filter (fun a => [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains (a - c).val = Bool.true)).card ≤ (2 : ℕ)) →
      (∀ c : Fin (13 : ℕ), c ∈ B ↔ ∀ a ∈ A, [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains (a - c).val = Bool.false) →
      D.eval ((List.ofFn (fun i => decide (i ∈ A)) ++ List.ofFn (fun j => decide (j ∈ B))) ++ [x4]) = Bool.false := by
    intro A B hcard hdeg hB
    rw [hEval]
    have hAcard : (A.image (· + x3)).card = (4 : ℕ) :=
      (Finset.card_image_of_injective A (add_left_injective x3)).trans hcard
    have hAdeg : ∀ c : Fin (13 : ℕ), {a ∈ A.image (· + x3) | a - c ∈ x8}.card ≤ (2 : ℕ) := by
      intro c
      have heq : {a ∈ A.image (· + x3) | a - c ∈ x8} =
          (A.filter (fun a => [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains (a - (c - x3)).val = Bool.true)).image (· + x3) := by
        apply Finset.ext
        intro u
        rw [Finset.mem_filter, Finset.mem_image, Finset.mem_image]
        constructor
        · rintro ⟨⟨a, ha, rfl⟩, hmem⟩
          refine ⟨a, Finset.mem_filter.mpr ⟨ha, ?_⟩, rfl⟩
          have hs : a - (c - x3) = a + x3 - c := by rw [sub_sub_eq_add_sub, add_sub_right_comm]
          rw [hs, ← hinc]; exact hmem
        · rintro ⟨a, ha, rfl⟩
          rcases Finset.mem_filter.mp ha with ⟨haA, hmem⟩
          refine ⟨⟨a, haA, rfl⟩, ?_⟩
          have hs : a + x3 - c = a - (c - x3) := by rw [sub_sub_eq_add_sub, add_sub_right_comm]
          rw [hs, hinc]; exact hmem
      rw [heq, Finset.card_image_of_injective _ (add_left_injective x3)]
      exact hdeg (c - x3)
    have hfA : (fun i : Fin (13 : ℕ) => decide (i + -x3 ∈ A)) = fun i => decide (i ∈ A.image (· + x3)) := by
      funext i
      apply decide_eq_decide.mpr
      rw [Finset.mem_image]
      constructor
      · intro hi; exact ⟨i + -x3, hi, neg_add_cancel_right i x3⟩
      · rintro ⟨a, ha, rfl⟩; rw [add_neg_cancel_right]; exact ha
    have hfB : (fun j : Fin (13 : ℕ) => decide (j + -x3 ∈ B)) =
        fun j => decide (j ∈ Finset.univ.filter (fun c : Fin (13 : ℕ) => ∀ a ∈ A.image (· + x3), a - c ∉ x8)) := by
      funext j
      apply decide_eq_decide.mpr
      rw [hB, Finset.mem_filter]
      constructor
      · intro hj
        refine ⟨Finset.mem_univ j, ?_⟩
        intro a ha
        rcases Finset.mem_image.mp ha with ⟨u, hu, rfl⟩
        rw [hincF]
        have hs : u + x3 - j = u - (j + -x3) := by rw [← sub_eq_add_neg, sub_sub_eq_add_sub, add_sub_right_comm]
        rw [hs]; exact hj u hu
      · rintro ⟨_, hj⟩ u hu
        have h1 := hj (u + x3) (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
        rw [hincF] at h1
        have hs : u + x3 - j = u - (j + -x3) := by rw [← sub_eq_add_neg, sub_sub_eq_add_sub, add_sub_right_comm]
        rw [← hs]; exact h1
    rw [hfA, hfB]
    exact h2 (A.image (· + x3)) hAcard hAdeg
  have h3' : ∀ (a1 a2 c1 c2 : Fin (13 : ℕ)),
      [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains (a1 - c1).val = Bool.false →
      [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains (a1 - c2).val = Bool.false →
      [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains (a2 - c1).val = Bool.false →
      [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains (a2 - c2).val = Bool.false →
      D.eval ((List.ofFn (fun i => decide (i = a1 ∨ i = a2)) ++ List.ofFn (fun j => decide (j = c1 ∨ j = c2))) ++ [x4]) = Bool.false := by
    intro a1 a2 c1 c2 h11 h12 h21 h22
    rw [hEval]
    have hfA : (fun i : Fin (13 : ℕ) => decide (i + -x3 = a1 ∨ i + -x3 = a2)) =
        fun i => decide (i ∈ ({a1 + x3, a2 + x3} : Finset (Fin (13 : ℕ)))) :=
      funext fun i => decide_eq_decide.mpr
        ((or_congr add_neg_eq_iff_eq_add add_neg_eq_iff_eq_add).trans
          (Finset.mem_insert.trans (or_congr_right Finset.mem_singleton)).symm)
    have hfB : (fun j : Fin (13 : ℕ) => decide (j + -x3 = c1 ∨ j + -x3 = c2)) =
        fun j => decide (j ∈ ({c1 + x3, c2 + x3} : Finset (Fin (13 : ℕ)))) :=
      funext fun j => decide_eq_decide.mpr
        ((or_congr add_neg_eq_iff_eq_add add_neg_eq_iff_eq_add).trans
          (Finset.mem_insert.trans (or_congr_right Finset.mem_singleton)).symm)
    rw [hfA, hfB]
    exact h3 (a1 + x3) (a2 + x3) (c1 + x3) (c2 + x3)
      (by rw [add_sub_add_right_eq_sub, hincF]; exact h11)
      (by rw [add_sub_add_right_eq_sub, hincF]; exact h12)
      (by rw [add_sub_add_right_eq_sub, hincF]; exact h21)
      (by rw [add_sub_add_right_eq_sub, hincF]; exact h22)
  exact hsz ▸ hNormLB D (x2 - x3) x4 ⟨hMono' hMono, hRB' hRB, hAP'.symm ▸ hAP, h1', h2', h3', hOr'.trans hOr⟩
