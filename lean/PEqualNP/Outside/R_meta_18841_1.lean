import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_18841_1
    (hOutOr : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit), (∀ u v : Fin 26, G.Adj u v ↔ ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ (u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l ∨ v = Fin.castAdd 13 p ∧ u = Fin.natAdd 13 l)) → IsLeastAO G C → junk G C ≠ ∅ → C.output + 1 = 26 + C.size → (gateAt C (C.size - 1)).op = GateOp.or → 65 ≤ C.size)
    (hOutTop : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit), (∀ u v : Fin 26, G.Adj u v ↔ ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧ (u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l ∨ v = Fin.castAdd 13 p ∧ u = Fin.natAdd 13 l)) → IsLeastAO G C → junk G C ≠ ∅ → C.output + 1 = 26 + C.size → (gateAt C (C.size - 1)).op = GateOp.and → BelowF G C (C.size - 1) → 65 ≤ C.size) :
    (∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.junk x1 x3 ≠ ∅ → (65 : ℕ) ≤ x3.size) := by
  intro G inst C hG hLeast hJunk
  have hAO2 := hLeast.1
  have hFun := hLeast.2.1
  have hMin := hLeast.2.2
  let stp : List Bool → Gate → List Bool := fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hFoldLen : ∀ (l : List Gate) (xs : List Bool), (l.foldl stp xs).length = xs.length + l.length := by
    intro l xs
    induction l using List.reverseRecOn with
    | nil => simp
    | append_singleton l g ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hstepLen : ∀ w : List Bool, (stp w g).length = w.length + 1 := fun w => by simp [stp]
      rw [hstepLen, ih, List.length_append, List.length_singleton]
      omega
  have hPres : ∀ (l : List Gate) (xs : List Bool) (w : ℕ), w < xs.length → (l.foldl stp xs).getD w false = xs.getD w false := by
    intro l xs w hw
    induction l using List.reverseRecOn with
    | nil => rfl
    | append_singleton l g ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      dsimp only [stp]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hFoldLen]; omega), ← List.getD_eq_getElem?_getD]
      exact ih
  have hOutGe : 26 ≤ C.output := by
    by_contra ho_lt
    have ho : C.output < 26 := Nat.lt_of_not_ge ho_lt
    let x : Fin 26 → Bool := fun z => decide (z.val = C.output)
    have hEvalT : C.eval (List.ofFn x) = true := by
      change (C.gates.foldl stp (List.ofFn x)).getD C.output false = true
      rw [hPres C.gates (List.ofFn x) C.output (by simp [ho])]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [ho]), Option.getD_some, List.getElem_ofFn]
      simp [x]
    have hGraphF : graphFun G ∅ x = false := by
      change (decide (∃ a ∈ (∅ : Finset (Fin 26)), x a = true) || decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = false
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
        decide_eq_false_iff_not, not_exists, not_and]
      intro u v hadj hu hv
      have hne := G.ne_of_adj hadj
      simp only [x, decide_eq_true_eq] at hu hv
      exact hne (Fin.ext (by omega))
    have hc := congrFun hFun x
    change C.eval (List.ofFn x) = graphFun G ∅ x at hc
    rw [hEvalT, hGraphF] at hc
    simp at hc
  have hOutLt : C.output < 26 + C.gates.length := by
    by_contra ho_ge
    have ho : 26 + C.gates.length ≤ C.output := Nat.le_of_not_lt ho_ge
    let x : Fin 26 → Bool := fun z => decide (z = Fin.castAdd 13 (0 : Fin 13) ∨ z = Fin.natAdd 13 (0 : Fin 13))
    have hEvalF : C.eval (List.ofFn x) = false := by
      change (C.gates.foldl stp (List.ofFn x)).getD C.output false = false
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hFoldLen, List.length_ofFn]; omega)]
      rfl
    have hGraphT : graphFun G ∅ x = true := by
      have hadj : G.Adj (Fin.castAdd 13 (0 : Fin 13)) (Fin.natAdd 13 (0 : Fin 13)) :=
        (hG _ _).mpr ⟨(0 : Fin 13), (0 : Fin 13), Or.inl rfl, Or.inl ⟨rfl, rfl⟩⟩
      change (decide (∃ a ∈ (∅ : Finset (Fin 26)), x a = true) || decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      right
      exact ⟨Fin.castAdd 13 (0 : Fin 13), Fin.natAdd 13 (0 : Fin 13), hadj, by simp [x], by simp [x]⟩
    have hc := congrFun hFun x
    change C.eval (List.ofFn x) = graphFun G ∅ x at hc
    rw [hEvalF, hGraphT] at hc
    simp at hc
  let k : ℕ := C.output - 26 + 1
  have hk_le : k ≤ C.gates.length := by omega
  let D : Circuit := ⟨C.gates.take k, C.output⟩
  have hD_ao2 : IsAO2 26 D := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      exact hAO2.1 g (List.mem_of_mem_take hg)
    · intro j hj i hi
      have hjk : j < k := by simp only [D, List.length_take] at hj; omega
      have hjC : j < C.gates.length := by omega
      have hg_eq : gateAt D j = gateAt C j := by
        change D.gates.getD j ⟨GateOp.or, []⟩ = C.gates.getD j ⟨GateOp.or, []⟩
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        have hcat := List.take_append_drop k C.gates
        have hget : D.gates[j]? = C.gates[j]? := by
          change (C.gates.take k)[j]? = C.gates[j]?
          conv_rhs => rw [← hcat]
          rw [List.getElem?_append_left (by rw [List.length_take]; omega)]
        rw [hget]
      rw [hg_eq] at hi
      exact hAO2.2.1 j hjC i hi
    · intro g hg
      exact hAO2.2.2 g (List.mem_of_mem_take hg)
  have hD_fun : circuitFun 26 D = graphFun G ∅ := by
    funext x
    rw [← congrFun hFun x]
    change (D.gates.foldl stp (List.ofFn x)).getD C.output false =
      (C.gates.foldl stp (List.ofFn x)).getD C.output false
    have hcat := List.take_append_drop k C.gates
    have hDlen : ((C.gates.take k).foldl stp (List.ofFn x)).length = 26 + k := by
      rw [hFoldLen, List.length_ofFn, List.length_take]
      omega
    conv_rhs => rw [← hcat, List.foldl_append]
    exact (hPres (C.gates.drop k) ((C.gates.take k).foldl stp (List.ofFn x)) C.output (by rw [hDlen]; omega)).symm
  have hC_le_D : C.size ≤ D.size := hMin D hD_ao2 hD_fun
  have hOutLast : C.output + 1 = 26 + C.size := by
    have hDs : D.size = k := by change (C.gates.take k).length = k; rw [List.length_take]; omega
    have hCs : C.size = C.gates.length := rfl
    have hk_def : k = C.output - 26 + 1 := rfl
    omega
  have hCs : C.size = C.gates.length := rfl
  have hPos : 0 < C.size := by rw [hCs]; omega
  have hLastMem : gateAt C (C.size - 1) ∈ C.gates := by
    have hlt : C.size - 1 < C.gates.length := by omega
    change C.gates.getD (C.size - 1) ⟨GateOp.or, []⟩ ∈ C.gates
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    exact List.getElem_mem hlt
  rcases hAO2.1 _ hLastMem with hAnd | hOr
  · refine hOutTop G C hG hLeast hJunk hOutLast hAnd fun x hx => ?_
    have hc := congrFun hFun x
    change C.eval (List.ofFn x) = graphFun G ∅ x at hc
    have hgv : gateVal 26 C (C.size - 1) x = C.eval (List.ofFn x) := by
      change (C.wires (List.ofFn x)).getD (26 + (C.size - 1)) false = (C.wires (List.ofFn x)).getD C.output false
      rw [show 26 + (C.size - 1) = C.output by omega]
    rw [← hc, ← hgv]
    exact hx
  · exact hOutOr G C hG hLeast hJunk hOutLast hOr
