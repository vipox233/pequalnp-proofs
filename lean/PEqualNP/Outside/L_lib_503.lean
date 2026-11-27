import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_503_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private noncomputable def isAnd (g : Gate) : Bool :=
  @decide (g.op = GateOp.and) (Classical.propDecidable _)

private noncomputable def countAnd (gs : List Gate) : ℕ :=
  gs.countP isAnd

private def wiresL (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private def ReadsBackL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

private def AdmGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∧ g.inputs.length = 2) ∨
  (g.op = GateOp.mod 2 ∧ g.inputs.length ≤ 2) ∨
  (g.op = GateOp.not ∧ g.inputs.length = 1)

private def mkInput (n : ℕ) (x : Fin n → ZMod 2) : List Bool :=
  List.ofFn (fun i : Fin n => decide (x i = 1))

private theorem b2z_decide_eq_one (z : ZMod 2) : b2z (decide (z = 1)) = z := by
  fin_cases z <;> rfl

private theorem b2z_and (b1 b2 : Bool) : b2z (b1 && b2) = b2z b1 * b2z b2 := by
  cases b1 <;> cases b2 <;> decide

private theorem b2z_not (b1 : Bool) : b2z (!b1) = b2z b1 + 1 := by
  cases b1 <;> decide

private theorem b2z_mod2_0 : b2z (GateOp.eval (GateOp.mod 2) []) = 1 := by
  decide

private theorem b2z_mod2_1 (b1 : Bool) :
    b2z (GateOp.eval (GateOp.mod 2) [b1]) = b2z b1 + 1 := by
  cases b1 <;> decide

private theorem b2z_mod2_2 (b1 b2 : Bool) :
    b2z (GateOp.eval (GateOp.mod 2) [b1, b2]) = b2z b1 + b2z b2 + 1 := by
  cases b1 <;> cases b2 <;> decide

private theorem wiresL_len (gs : List Gate) (x : List Bool) :
    (wiresL gs x).length = x.length + gs.length := by
  unfold wiresL
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem getD_snoc {α : Type} (l : List α) (v d : α) (i : ℕ) :
    (l ++ [v]).getD i d = if i < l.length then l.getD i d else if i = l.length then v else d := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by simp; omega)]
    rfl

private theorem dot_single {n : ℕ} (i : Fin n) (x : Fin n → ZMod 2) :
    dotProduct (Pi.single i (1 : ZMod 2)) x = x i := by
  simp [dotProduct, Pi.single_apply]

private theorem dot_zero {n : ℕ} (x : Fin n → ZMod 2) :
    dotProduct (0 : Fin n → ZMod 2) x = 0 := by
  simp [dotProduct]

private theorem dot_add_left {n : ℕ} (a b x : Fin n → ZMod 2) :
    dotProduct (a + b) x = dotProduct a x + dotProduct b x := by
  simp [dotProduct, add_mul, Finset.sum_add_distrib]

private theorem dot_add_right {n : ℕ} (a x y : Fin n → ZMod 2) :
    dotProduct a (x + y) = dotProduct a x + dotProduct a y := by
  simp [dotProduct, mul_add, Finset.sum_add_distrib]

private theorem dot_smul_right {n : ℕ} (a : Fin n → ZMod 2) (r : ZMod 2) (x : Fin n → ZMod 2) :
    dotProduct a (r • x) = r • dotProduct a x := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

private def linMapOf {n k : ℕ} (A : Fin k → (Fin n → ZMod 2)) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun x j := dotProduct (A j) x
  map_add' x y := by
    funext j
    exact dot_add_right (A j) x y
  map_smul' r x := by
    funext j
    exact dot_smul_right (A j) r x

private theorem wires_rep (n : ℕ) (gs : List Gate)
    (hback : ReadsBackL n gs) (hadm : ∀ g ∈ gs, AdmGate g) :
    ∃ (A : Fin (2 * countAnd gs) → (Fin n → ZMod 2))
      (G : ℕ → (Fin (2 * countAnd gs) → ZMod 2) → ZMod 2)
      (a : ℕ → (Fin n → ZMod 2)),
      ∀ (i : ℕ), i < n + gs.length → ∀ (x : Fin n → ZMod 2),
        b2z ((wiresL gs (mkInput n x)).getD i false) =
          G i (fun k => dotProduct (A k) x) + dotProduct (a i) x := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨Fin.elim0, fun _ _ => 0,
      fun i => if h : i < n then Pi.single ⟨i, h⟩ 1 else 0, ?_⟩
    intro i hi x
    simp only [List.length_nil, Nat.add_zero] at hi
    simp only [wiresL, List.foldl_nil, zero_add, hi, ↓reduceDIte, dot_single]
    unfold mkInput
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
    exact b2z_decide_eq_one (x ⟨i, hi⟩)
  | append_singleton gs gate ih =>
    have hback0 : ReadsBackL n gs := by
      intro j hj i hi
      have h1 := hback j (by simp; omega)
      have heq : (gs ++ [gate]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        rw [getD_snoc]; simp [hj]
      rw [heq] at h1
      exact h1 i hi
    have hback_gate : ∀ i ∈ gate.inputs, i < n + gs.length := by
      have h1 := hback gs.length (by simp)
      have heq : (gs ++ [gate]).getD gs.length ⟨GateOp.or, []⟩ = gate := by
        rw [getD_snoc]; simp
      rw [heq] at h1
      exact h1
    have hadm0 : ∀ g ∈ gs, AdmGate g := fun g hg => hadm g (List.mem_append_left _ hg)
    have hadm_gate : AdmGate gate := hadm gate (List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨A, G, a, hrep⟩ := ih hback0 hadm0
    have hw_step : ∀ x : Fin n → ZMod 2,
        wiresL (gs ++ [gate]) (mkInput n x) =
          wiresL gs (mkInput n x) ++
            [gate.op.eval (gate.inputs.map fun i => (wiresL gs (mkInput n x)).getD i false)] := by
      intro x
      unfold wiresL
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hw_len : ∀ x : Fin n → ZMod 2, (wiresL gs (mkInput n x)).length = n + gs.length := by
      intro x
      rw [wiresL_len]
      simp [mkInput]
    have hcnt : countAnd (gs ++ [gate]) = countAnd gs + if isAnd gate then 1 else 0 := by
      unfold countAnd
      rw [List.countP_append, List.countP_cons, List.countP_nil]
      cases isAnd gate <;> simp
    rcases hadm_gate with ⟨hop, hlen⟩ | ⟨hop, hlen⟩ | ⟨hop, hlen⟩
    · have his : isAnd gate = true := by
        unfold isAnd
        rw [hop]
        exact @decide_eq_true _ (Classical.propDecidable _) rfl
      have hcnt1 : countAnd (gs ++ [gate]) = countAnd gs + 1 := by
        rw [hcnt, his]; simp
      cases hinp : gate.inputs with
      | nil => simp [hinp] at hlen
      | cons i1 rest =>
        cases rest with
        | nil => simp [hinp] at hlen
        | cons i2 rest2 =>
          cases rest2 with
          | cons _ _ => simp [hinp] at hlen
          | nil =>
            have hi1 : i1 < n + gs.length := hback_gate i1 (by rw [hinp]; simp)
            have hi2 : i2 < n + gs.length := hback_gate i2 (by rw [hinp]; simp)
            have h2s : 2 * countAnd (gs ++ [gate]) = 2 * countAnd gs + 2 := by rw [hcnt1]; omega
            let A' : Fin (2 * countAnd (gs ++ [gate])) → (Fin n → ZMod 2) := fun k =>
              if hk : k.val < 2 * countAnd gs then A ⟨k.val, hk⟩
              else if k.val = 2 * countAnd gs then a i1 else a i2
            let proj : (Fin (2 * countAnd (gs ++ [gate])) → ZMod 2) → (Fin (2 * countAnd gs) → ZMod 2) :=
              fun u k => u ⟨k.val, by omega⟩
            let k1 : Fin (2 * countAnd (gs ++ [gate])) := ⟨2 * countAnd gs, by omega⟩
            let k2 : Fin (2 * countAnd (gs ++ [gate])) := ⟨2 * countAnd gs + 1, by omega⟩
            let G' : ℕ → (Fin (2 * countAnd (gs ++ [gate])) → ZMod 2) → ZMod 2 := fun i u =>
              if i < n + gs.length then G i (proj u)
              else (G i1 (proj u) + u k1) * (G i2 (proj u) + u k2)
            let a' : ℕ → (Fin n → ZMod 2) := fun i =>
              if i < n + gs.length then a i else 0
            refine ⟨A', G', a', ?_⟩
            intro i hi x
            have hproj : proj (fun k => dotProduct (A' k) x) = (fun k => dotProduct (A k) x) := by
              funext k
              simp only [proj, A', k.isLt, ↓reduceDIte]
            have hk1 : dotProduct (A' k1) x = dotProduct (a i1) x := by
              simp [A', k1]
            have hk2 : dotProduct (A' k2) x = dotProduct (a i2) x := by
              simp [A', k2]
            rw [hw_step x, getD_snoc, hw_len x]
            by_cases hilt : i < n + gs.length
            · simp only [G', a', hilt, ↓reduceIte, hproj]
              exact hrep i hilt x
            · have heqi : i = n + gs.length := by
                simp only [List.length_append, List.length_singleton] at hi
                omega
              subst heqi
              simp only [G', a', Nat.lt_irrefl, ↓reduceIte, hproj, hk1, hk2, dot_zero, add_zero]
              rw [hop, hinp]
              simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
                id_eq, Bool.and_true]
              rw [b2z_and, hrep i1 hi1 x, hrep i2 hi2 x]
    · have his : isAnd gate = false := by
        unfold isAnd
        rw [hop]
        exact @decide_eq_false _ (Classical.propDecidable _) (by intro h; cases h)
      have hcnt0 : countAnd (gs ++ [gate]) = countAnd gs := by
        rw [hcnt, his]; simp
      have hgate_rep : ∃ (g0 : (Fin (2 * countAnd gs) → ZMod 2) → ZMod 2) (a0 : Fin n → ZMod 2),
          ∀ x : Fin n → ZMod 2,
            b2z (gate.op.eval (gate.inputs.map fun i => (wiresL gs (mkInput n x)).getD i false)) =
              g0 (fun k => dotProduct (A k) x) + dotProduct a0 x := by
        cases hinp : gate.inputs with
        | nil =>
          refine ⟨fun _ => 1, 0, fun x => ?_⟩
          rw [hop, List.map_nil, b2z_mod2_0, dot_zero, add_zero]
        | cons i1 rest =>
          cases rest with
          | nil =>
            have hi1 : i1 < n + gs.length := hback_gate i1 (by rw [hinp]; simp)
            refine ⟨fun u => G i1 u + 1, a i1, fun x => ?_⟩
            rw [hop, List.map_cons, List.map_nil, b2z_mod2_1, hrep i1 hi1 x]
            ring
          | cons i2 rest2 =>
            cases rest2 with
            | cons _ _ => simp [hinp] at hlen
            | nil =>
              have hi1 : i1 < n + gs.length := hback_gate i1 (by rw [hinp]; simp)
              have hi2 : i2 < n + gs.length := hback_gate i2 (by rw [hinp]; simp)
              refine ⟨fun u => G i1 u + G i2 u + 1, a i1 + a i2, fun x => ?_⟩
              rw [hop, List.map_cons, List.map_cons, List.map_nil, b2z_mod2_2,
                hrep i1 hi1 x, hrep i2 hi2 x, dot_add_left]
              ring
      obtain ⟨g0, a0, hg0⟩ := hgate_rep
      rw [hcnt0]
      refine ⟨A, fun i u => if i < n + gs.length then G i u else g0 u,
        fun i => if i < n + gs.length then a i else a0, ?_⟩
      intro i hi x
      rw [hw_step x, getD_snoc, hw_len x]
      by_cases hilt : i < n + gs.length
      · simp only [hilt, ↓reduceIte]
        exact hrep i hilt x
      · have heqi : i = n + gs.length := by
          simp only [List.length_append, List.length_singleton] at hi
          omega
        subst heqi
        simp only [Nat.lt_irrefl, ↓reduceIte]
        exact hg0 x
    · have his : isAnd gate = false := by
        unfold isAnd
        rw [hop]
        exact @decide_eq_false _ (Classical.propDecidable _) (by intro h; cases h)
      have hcnt0 : countAnd (gs ++ [gate]) = countAnd gs := by
        rw [hcnt, his]; simp
      cases hinp : gate.inputs with
      | nil => simp [hinp] at hlen
      | cons i1 rest =>
        cases rest with
        | cons _ _ => simp [hinp] at hlen
        | nil =>
          have hi1 : i1 < n + gs.length := hback_gate i1 (by rw [hinp]; simp)
          rw [hcnt0]
          refine ⟨A, fun i u => if i < n + gs.length then G i u else G i1 u + 1,
            fun i => if i < n + gs.length then a i else a i1, ?_⟩
          intro i hi x
          rw [hw_step x, getD_snoc, hw_len x]
          by_cases hilt : i < n + gs.length
          · simp only [hilt, ↓reduceIte]
            exact hrep i hilt x
          · have heqi : i = n + gs.length := by
              simp only [List.length_append, List.length_singleton] at hi
              omega
            subst heqi
            simp only [Nat.lt_irrefl, ↓reduceIte, hop, hinp, List.map_cons, List.map_nil,
              GateOp.eval, List.headD_cons]
            rw [b2z_not, hrep i1 hi1 x]
            ring

theorem solve_503 (n : ℕ) (C : Circuit) (f : (Fin n → ZMod 2) → ZMod 2)
    (hadm : ReadsBack n C ∧ ∀ g ∈ C.gates, AdmGate g)
    (heval : ∀ x : Fin n → ZMod 2, C.eval (mkInput n x) = decide (f x = 1)) :
    ∃ (L : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin (2 * countAnd C.gates) → ZMod 2))
      (g : (Fin (2 * countAnd C.gates) → ZMod 2) → ZMod 2) (a : Fin n → ZMod 2),
      ∀ x : Fin n → ZMod 2, f x = g (L x) + dotProduct a x := by
  obtain ⟨A, G, a, hrep⟩ := wires_rep n C.gates hadm.1 hadm.2
  by_cases hout : C.output < n + C.gates.length
  · refine ⟨linMapOf A, G C.output, a C.output, fun x => ?_⟩
    have h1 := hrep C.output hout x
    have h2 : (wiresL C.gates (mkInput n x)).getD C.output false = C.eval (mkInput n x) := rfl
    rw [h2, heval x, b2z_decide_eq_one] at h1
    exact h1
  · refine ⟨linMapOf A, fun _ => 0, 0, fun x => ?_⟩
    have hlen : (C.wires (mkInput n x)).length = n + C.gates.length := by
      have := wiresL_len C.gates (mkInput n x)
      simpa [mkInput, wiresL, Circuit.wires] using this
    have hfalse : C.eval (mkInput n x) = false := by
      unfold Circuit.eval
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    have hf0 : f x = 0 := by
      have h1 := heval x
      rw [hfalse] at h1
      have := b2z_decide_eq_one (f x)
      rw [← h1] at this
      exact this.symm
    rw [hf0, dot_zero, add_zero]

end PEqualNP.Outside.L_lib_503_aux

theorem PEqualNP.Outside.L_lib_503 : ∀ n : ℕ,
  let V := Fin n → ZMod 2
  let admissible := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
    (∀ g ∈ C.gates,
      (g.op = .and ∧ g.inputs.length = 2) ∨
      (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨
      (g.op = .not ∧ g.inputs.length = 1))
  let cost := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    C.gates.countP (fun g => @decide (g.op = .and) (Classical.propDecidable _))
  let input := fun (x : V) => List.ofFn (fun i : Fin n => decide (x i = 1))
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (f : V → ZMod 2),
    admissible C → (∀ x : V, C.eval (input x) = decide (f x = 1)) →
    ∃ (L : V →ₗ[ZMod 2] (Fin (2*cost C) → ZMod 2))
      (g : (Fin (2*cost C) → ZMod 2) → ZMod 2) (a : V),
      ∀ x : V, f x = g (L x) + dotProduct a x := by
  intro n V admissible cost input C f hadm heval
  exact PEqualNP.Outside.L_lib_503_aux.solve_503 n C f hadm heval
