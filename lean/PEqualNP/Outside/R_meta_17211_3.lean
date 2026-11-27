import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17211_3
    (hTruncateSwap : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 x7 : ℕ),
      have a : ℕ := min x6 x7;
      have b : ℕ := max x6 x7;
      have D : PEqualNP.CircuitLowerBounds.Circuit :=
        { gates := (C.gates.take (x5 + (1 : ℕ))).set x5 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] }, output := (26 : ℕ) + x5 };
      PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      C.output = (26 : ℕ) + x5 ∧ C.gates[x5]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x6, x7] } →
      a < b ∧ b < (26 : ℕ) + x5 ∧ D.size = x5 + (1 : ℕ) ∧ D.size ≤ C.size ∧
      PEqualNP.TopForm.IsAO2 (26 : ℕ) D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
      D.gates[x5]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] } ∧
      ∀ y : List Bool, D.eval y = C.eval y ∧
        (D.wires y).getD a Bool.false = (C.wires y).getD a Bool.false ∧
        (D.wires y).getD b Bool.false = (C.wires y).getD b Bool.false)
    (hTopOrderedLB : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x5 a b : ℕ),
      have inc : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun u v => [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains (u - v).val;
      have p2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun u v => (List.ofFn fun i => decide (i = u)) ++ List.ofFn fun j => decide (j = v);
      have p4 : Finset (Fin (13 : ℕ)) → List Bool := fun A => (List.ofFn fun i => decide (i ∈ A)) ++ List.ofFn fun j => decide (∀ u ∈ A, inc u j = Bool.false);
      PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      C.size = x5 + (1 : ℕ) ∧ C.output = (26 : ℕ) + x5 ∧
      C.gates[x5]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] } ∧
      (26 : ℕ) ≤ a ∧ a < b ∧ b < (26 : ℕ) + x5 ∧
      (∀ u v : Fin (13 : ℕ), C.eval (p2 u v) = inc u v) ∧
      (∀ A : Finset (Fin (13 : ℕ)), A.card = (4 : ℕ) → (∀ v : Fin (13 : ℕ), (A.filter (fun u => inc u v = Bool.true)).card ≤ (2 : ℕ)) → C.eval (p4 A) = Bool.false) ∧
      (∃ u v : Fin (13 : ℕ), inc u v = Bool.true ∧ (C.wires (p2 u v)).getD a Bool.false = Bool.true ∧ (C.wires (p2 u v)).getD b Bool.false = Bool.false) ∧
      (∃ u v : Fin (13 : ℕ), inc u v = Bool.true ∧ (C.wires (p2 u v)).getD b Bool.false = Bool.true ∧ (C.wires (p2 u v)).getD a Bool.false = Bool.false) →
      (64 : ℕ) ≤ C.size) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 x7 : ℕ), PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 → (∀ x9 ∈ x4.gates, x9.inputs.Nodup) → x4.output = (26 : ℕ) + x5 → x4.gates[x5]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x6, x7] : PEqualNP.CircuitLowerBounds.Gate } → (26 : ℕ) ≤ x6 → (26 : ℕ) ≤ x7 → (∀ (x14 x15 : Fin (13 : ℕ)), x4.eval (x2 x14 x15) = Decidable.decide (x14 - x15 ∈ x1)) → (∀ (x15 : Finset (Fin (13 : ℕ))), x15.card = (4 : ℕ) → (∀ (x17 : Fin (13 : ℕ)), {x18 ∈ x15 | x18 - x17 ∈ x1}.card ≤ (2 : ℕ)) → x4.eval (x3 x15) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 - x17 ∈ x1 ∧ (x4.wires (x2 x16 x17)).getD x6 Bool.false = Bool.true ∧ (x4.wires (x2 x16 x17)).getD x7 Bool.false = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 - x18 ∈ x1 ∧ (x4.wires (x2 x17 x18)).getD x7 Bool.false = Bool.true ∧ (x4.wires (x2 x17 x18)).getD x6 Bool.false = Bool.false) → (64 : ℕ) ≤ x4.size) := by
  intro x1 x2 x3 C x5 x6 x7 hAO hNod hOut hGate h6 h7 hP2 hP4 hW1 hW2
  have hinc : ∀ u : Fin (13 : ℕ), u ∈ x1 ↔ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains u.val = Bool.true := by decide
  have hincF : ∀ u : Fin (13 : ℕ), u ∉ x1 ↔ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains u.val = Bool.false := by decide
  have hincDec : ∀ u : Fin (13 : ℕ), Decidable.decide (u ∈ x1) = [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains u.val := by decide
  let a : ℕ := min x6 x7
  let b : ℕ := max x6 x7
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
    { gates := (C.gates.take (x5 + (1 : ℕ))).set x5 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] }, output := (26 : ℕ) + x5 }
  rcases hTruncateSwap C x5 x6 x7 ⟨hAO, hNod, hOut, hGate⟩ with ⟨hab, hbhi, hDsz, hDle, hDAO, hDNod, hDGate, hDW⟩
  have hDP2 : ∀ u v : Fin (13 : ℕ), D.eval ((List.ofFn fun i => decide (i = u)) ++ List.ofFn fun j => decide (j = v)) = [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains (u - v).val := by
    intro u v
    exact ((hDW (x2 u v)).1.trans (hP2 u v)).trans (hincDec (u - v))
  have hDP4 : ∀ A : Finset (Fin (13 : ℕ)), A.card = (4 : ℕ) →
      (∀ v : Fin (13 : ℕ), (A.filter (fun u => [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains (u - v).val = Bool.true)).card ≤ (2 : ℕ)) →
      D.eval ((List.ofFn fun i => decide (i ∈ A)) ++ List.ofFn fun j => decide (∀ u ∈ A, [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains (u - j).val = Bool.false)) = Bool.false := by
    intro A hcard hdeg
    have hdeg' : ∀ v : Fin (13 : ℕ), {u ∈ A | u - v ∈ x1}.card ≤ (2 : ℕ) := by
      intro v
      have hf : {u ∈ A | u - v ∈ x1} = A.filter (fun u => [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains (u - v).val = Bool.true) := by
        apply Finset.ext; intro u; rw [Finset.mem_filter, Finset.mem_filter, hinc]
      rw [hf]; exact hdeg v
    have hfn : (fun j : Fin (13 : ℕ) => decide (∀ u ∈ A, [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains (u - j).val = Bool.false)) =
        fun j => Decidable.decide (∀ u ∈ A, u - j ∉ x1) :=
      funext fun j => decide_eq_decide.mpr (forall_congr' fun u => imp_congr_right fun _ => (hincF (u - j)).symm)
    rw [hfn]
    exact (hDW (x3 A)).1.trans (hP4 A hcard hdeg')
  have hDW1 : ∃ u v : Fin (13 : ℕ), [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains (u - v).val = Bool.true ∧ (D.wires (x2 u v)).getD a Bool.false = Bool.true ∧ (D.wires (x2 u v)).getD b Bool.false = Bool.false := by
    rcases le_total x6 x7 with hle | hge
    · rcases hW1 with ⟨u, v, huv, h6t, h7f⟩
      refine ⟨u, v, (hinc (u - v)).mp huv, ?_, ?_⟩
      · rw [(hDW (x2 u v)).2.1]; show (C.wires (x2 u v)).getD (min x6 x7) false = true; rw [min_eq_left hle]; exact h6t
      · rw [(hDW (x2 u v)).2.2]; show (C.wires (x2 u v)).getD (max x6 x7) false = false; rw [max_eq_right hle]; exact h7f
    · rcases hW2 with ⟨u, v, huv, h7t, h6f⟩
      refine ⟨u, v, (hinc (u - v)).mp huv, ?_, ?_⟩
      · rw [(hDW (x2 u v)).2.1]; show (C.wires (x2 u v)).getD (min x6 x7) false = true; rw [min_eq_right hge]; exact h7t
      · rw [(hDW (x2 u v)).2.2]; show (C.wires (x2 u v)).getD (max x6 x7) false = false; rw [max_eq_left hge]; exact h6f
  have hDW2 : ∃ u v : Fin (13 : ℕ), [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)].contains (u - v).val = Bool.true ∧ (D.wires (x2 u v)).getD b Bool.false = Bool.true ∧ (D.wires (x2 u v)).getD a Bool.false = Bool.false := by
    rcases le_total x6 x7 with hle | hge
    · rcases hW2 with ⟨u, v, huv, h7t, h6f⟩
      refine ⟨u, v, (hinc (u - v)).mp huv, ?_, ?_⟩
      · rw [(hDW (x2 u v)).2.2]; show (C.wires (x2 u v)).getD (max x6 x7) false = true; rw [max_eq_right hle]; exact h7t
      · rw [(hDW (x2 u v)).2.1]; show (C.wires (x2 u v)).getD (min x6 x7) false = false; rw [min_eq_left hle]; exact h6f
    · rcases hW1 with ⟨u, v, huv, h6t, h7f⟩
      refine ⟨u, v, (hinc (u - v)).mp huv, ?_, ?_⟩
      · rw [(hDW (x2 u v)).2.2]; show (C.wires (x2 u v)).getD (max x6 x7) false = true; rw [max_eq_left hge]; exact h6t
      · rw [(hDW (x2 u v)).2.1]; show (C.wires (x2 u v)).getD (min x6 x7) false = false; rw [min_eq_right hge]; exact h7f
  exact Nat.le_trans (hTopOrderedLB D x5 a b ⟨hDAO, hDNod, hDsz, rfl, hDGate, le_min h6 h7, hab, hbhi, hDP2, hDP4, hDW1, hDW2⟩) hDle
