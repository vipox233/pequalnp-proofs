import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_504_aux

open PEqualNP.CircuitLowerBounds

private abbrev Vec (n : ℕ) := Fin n → ZMod 2

private abbrev Aff (n k : ℕ) := (Fin n → ZMod 2) × (Fin k → ZMod 2) × ZMod 2

private def evalAff {n k : ℕ} (d : Aff n k) (x : Vec n) (P : Fin k → ZMod 2) : ZMod 2 :=
  dotProduct d.1 x + (∑ r : Fin k, d.2.1 r * P r) + d.2.2

private def zeroAff (n k : ℕ) : Aff n k := (0, 0, 0)

private def oneAff (n k : ℕ) : Aff n k := (0, 0, 1)

private def addConstAff {n k : ℕ} (d : Aff n k) (c : ZMod 2) : Aff n k :=
  (d.1, d.2.1, d.2.2 + c)

private def addAff {n k : ℕ} (d1 d2 : Aff n k) : Aff n k :=
  (d1.1 + d2.1, d1.2.1 + d2.2.1, d1.2.2 + d2.2.2)

private def liftAff {n k : ℕ} (d : Aff n k) : Aff n (k + 1) :=
  (d.1, Fin.snoc d.2.1 0, d.2.2)

private lemma evalAff_zero {n k : ℕ} (x : Vec n) (P : Fin k → ZMod 2) :
    evalAff (zeroAff n k) x P = 0 := by
  simp [evalAff, zeroAff]

private lemma evalAff_one {n k : ℕ} (x : Vec n) (P : Fin k → ZMod 2) :
    evalAff (oneAff n k) x P = 1 := by
  simp [evalAff, oneAff]

private lemma evalAff_addConst {n k : ℕ} (d : Aff n k) (c : ZMod 2) (x : Vec n)
    (P : Fin k → ZMod 2) :
    evalAff (addConstAff d c) x P = evalAff d x P + c := by
  simp only [evalAff, addConstAff]
  ring

private lemma evalAff_add {n k : ℕ} (d1 d2 : Aff n k) (x : Vec n) (P : Fin k → ZMod 2) :
    evalAff (addAff d1 d2) x P = evalAff d1 x P + evalAff d2 x P := by
  simp only [evalAff, addAff, add_dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

private lemma evalAff_lift {n k : ℕ} (d : Aff n k) (x : Vec n) (P : Fin k → ZMod 2) (v : ZMod 2) :
    evalAff (liftAff d) x (Fin.snoc P v) = evalAff d x P := by
  simp only [evalAff, liftAff]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero]

private def lastVarAff (n k : ℕ) : Aff n (k + 1) :=
  (0, Pi.single (Fin.last k) 1, 0)

private lemma evalAff_lastVar {n k : ℕ} (x : Vec n) (P : Fin k → ZMod 2) (v : ZMod 2) :
    evalAff (lastVarAff n k) x (Fin.snoc P v) = v := by
  simp only [evalAff, lastVarAff, zero_dotProduct, zero_add, add_zero]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have h0 : ∑ i : Fin k, (Pi.single (M := fun _ : Fin (k + 1) => ZMod 2) (Fin.last k) 1 i.castSucc) * P i = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have hne : i.castSucc ≠ Fin.last k := Fin.castSucc_ne_last i
    simp [Pi.single_eq_of_ne hne]
  rw [h0, zero_add, Pi.single_eq_same, one_mul]

private def StepList (n : ℕ) : ℕ → Type
  | 0 => PUnit
  | s + 1 => StepList n s × (Aff n s × Aff n s)

private def instFintypeStepList (n : ℕ) : ∀ s : ℕ, Fintype (StepList n s)
  | 0 => inferInstanceAs (Fintype PUnit)
  | s + 1 =>
      letI := instFintypeStepList n s
      inferInstanceAs (Fintype (StepList n s × (Aff n s × Aff n s)))

private lemma card_aff (n k : ℕ) : Fintype.card (Aff n k) = 2 ^ (n + k + 1) := by
  simp only [Aff, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  rw [← pow_succ, ← pow_add, ← add_assoc]

private lemma card_stepList (n s : ℕ) :
    @Fintype.card (StepList n s) (instFintypeStepList n s) = 2 ^ (s ^ 2 + 2 * n * s + s) := by
  induction s with
  | zero =>
      change Fintype.card PUnit = 2 ^ (0 ^ 2 + 2 * n * 0 + 0)
      simp
  | succ s ih =>
      let _inst : Fintype (StepList n s) := instFintypeStepList n s
      change Fintype.card (StepList n s × (Aff n s × Aff n s)) = _
      rw [Fintype.card_prod, Fintype.card_prod, ih, card_aff]
      rw [← pow_add, ← pow_add]
      congr 1
      ring

private def evalSteps {n : ℕ} : ∀ {s : ℕ}, StepList n s → Vec n → (Fin s → ZMod 2)
  | 0, _, _ => Fin.elim0
  | _ + 1, (prev, (d1, d2)), x =>
      let P := evalSteps prev x
      Fin.snoc P (evalAff d1 x P * evalAff d2 x P)

private def evalCode {n s : ℕ} (code : StepList n s × Aff n s) (x : Vec n) : ZMod 2 :=
  evalAff code.2 x (evalSteps code.1 x)

private def padCode {n : ℕ} : ∀ {k : ℕ} (d : ℕ), StepList n k × Aff n k →
    StepList n (k + d) × Aff n (k + d)
  | _, 0, code => code
  | _, d + 1, code =>
      let prev := padCode d code
      ((prev.1, (zeroAff n _, zeroAff n _)), liftAff prev.2)

private lemma evalCode_padCode {n k : ℕ} (d : ℕ) (code : StepList n k × Aff n k) (x : Vec n) :
    evalCode (padCode d code) x = evalCode code x := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [padCode, evalCode, evalSteps]
      rw [evalAff_lift]
      exact ih

private def evalWires (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma evalWires_nil (x : List Bool) : evalWires [] x = x := rfl

private lemma evalWires_append_singleton (gs : List Gate) (g : Gate) (x : List Bool) :
    evalWires (gs ++ [g]) x =
      evalWires gs x ++ [g.op.eval (g.inputs.map fun i => (evalWires gs x).getD i false)] := by
  simp [evalWires, List.foldl_append]

private lemma evalWires_length (gs : List Gate) (x : List Bool) :
    (evalWires gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [evalWires]
  | append_singleton gs g ih =>
      rw [evalWires_append_singleton, List.length_append, List.length_singleton, ih,
        List.length_append, List.length_singleton]
      omega

private lemma getD_append_singleton_lt {α : Type*} (l : List α) (a d : α) (i : ℕ)
    (hi : i < l.length) :
    (l ++ [a]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_append_singleton_eq {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD]

private lemma getD_append_singleton_gt {α : Type*} (l : List α) (a d : α) (i : ℕ)
    (hi : l.length < i) :
    (l ++ [a]).getD i d = d := by
  have hge : (l ++ [a]).length ≤ i := by
    rw [List.length_append, List.length_singleton]
    omega
  simp [List.getD, List.getElem?_eq_none hge]

private lemma zmod2_not_decide (a : ZMod 2) :
    (!decide (a = 1)) = decide (a + 1 = 1) := by
  fin_cases a <;> decide

private lemma zmod2_and_decide (a b : ZMod 2) :
    (decide (a = 1) && decide (b = 1)) = decide (a * b = 1) := by
  fin_cases a <;> fin_cases b <;> decide

private lemma zmod2_mod2_one (a : ZMod 2) :
    GateOp.eval (.mod 2) [decide (a = 1)] = decide (a + 1 = 1) := by
  fin_cases a <;> decide

private lemma zmod2_mod2_two (a b : ZMod 2) :
    GateOp.eval (.mod 2) [decide (a = 1), decide (b = 1)] = decide (a + b + 1 = 1) := by
  fin_cases a <;> fin_cases b <;> decide

private lemma zmod2_eq_of_decide_eq (a b : ZMod 2) (h : decide (a = 1) = decide (b = 1)) :
    a = b := by
  fin_cases a <;> fin_cases b
  · rfl
  · exfalso; exact absurd h (by decide)
  · exfalso; exact absurd h (by decide)
  · rfl

private noncomputable def andCount (gs : List Gate) : ℕ :=
  gs.countP (fun g => @decide (g.op = .and) (Classical.propDecidable _))

private lemma evalCode_cast {n a b : ℕ} (h : a = b) (code : StepList n a × Aff n a) (x : Vec n) :
    evalCode (h ▸ code) x = evalCode code x := by
  subst h
  rfl

private lemma simulate_gates (n : ℕ) (gs : List Gate)
    (hadm : ∀ g ∈ gs,
      (g.op = .and ∧ g.inputs.length = 2) ∨
      (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨
      (g.op = .not ∧ g.inputs.length = 1)) :
    ∃ (st : StepList n (andCount gs)) (wireAff : ℕ → Aff n (andCount gs)),
      ∀ (i : ℕ) (x : Vec n),
        (evalWires gs (List.ofFn (fun j : Fin n => decide (x j = 1)))).getD i false =
          decide (evalAff (wireAff i) x (evalSteps st x) = 1) := by
  induction gs using List.reverseRecOn with
  | nil =>
      rw [show andCount [] = 0 from rfl]
      refine ⟨PUnit.unit, fun i => if h : i < n then (Pi.single ⟨i, h⟩ 1, Fin.elim0, 0) else zeroAff n 0, ?_⟩
      intro i x
      rw [evalWires_nil]
      by_cases h : i < n
      · simp only [h, ↓reduceDIte]
        have hget : (List.ofFn (fun j : Fin n => decide (x j = 1))).getD i false = decide (x ⟨i, h⟩ = 1) := by
          simp [List.getD, h]
        rw [hget]
        congr 1
        simp only [evalAff, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
        unfold dotProduct
        simp only [Pi.single_apply, ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq' Finset.univ (⟨i, h⟩ : Fin n)]
        simp
      · simp only [h, ↓reduceDIte]
        rw [evalAff_zero]
        have hge : (List.ofFn (fun j : Fin n => decide (x j = 1))).length ≤ i := by
          rw [List.length_ofFn]
          omega
        rw [List.getD, List.getElem?_eq_none hge]
        decide
  | append_singleton gs g ih =>
      have hadm_gs : ∀ g' ∈ gs,
          (g'.op = .and ∧ g'.inputs.length = 2) ∨
          (g'.op = .mod 2 ∧ g'.inputs.length ≤ 2) ∨
          (g'.op = .not ∧ g'.inputs.length = 1) :=
        fun g' hg' => hadm g' (List.mem_append_left _ hg')
      obtain ⟨st, wireAff, hwire⟩ := ih hadm_gs
      have hg := hadm g (List.mem_append_right _ (List.mem_singleton_self g))
      have hlen : ∀ x : Vec n,
          (evalWires gs (List.ofFn (fun j : Fin n => decide (x j = 1)))).length = n + gs.length := by
        intro x
        rw [evalWires_length, List.length_ofFn]
      rcases hg with ⟨hop, hlen_in⟩ | ⟨hop, hlen_in⟩ | ⟨hop, hlen_in⟩
      · have hcount : andCount (gs ++ [g]) = andCount gs + 1 := by
          simp [andCount, List.countP_append, hop]
        rw [hcount]
        rcases hlist : g.inputs with _ | ⟨u1, _ | ⟨u2, rest⟩⟩
        · rw [hlist] at hlen_in; simp at hlen_in
        · rw [hlist] at hlen_in; simp at hlen_in
        · rcases rest with _ | ⟨u3, _⟩
          · let st' : StepList n (andCount gs + 1) := (st, (wireAff u1, wireAff u2))
            let wireAff' : ℕ → Aff n (andCount gs + 1) := fun i =>
              if i < n + gs.length then liftAff (wireAff i)
              else if i = n + gs.length then lastVarAff n (andCount gs)
              else zeroAff n (andCount gs + 1)
            refine ⟨st', wireAff', fun i x => ?_⟩
            rw [evalWires_append_singleton]
            by_cases hlt : i < n + gs.length
            · have hlt' : i < (evalWires gs (List.ofFn (fun j : Fin n => decide (x j = 1)))).length := by
                rw [hlen x]; exact hlt
              rw [getD_append_singleton_lt _ _ _ _ hlt', hwire i x]
              simp only [wireAff', hlt, ↓reduceIte, st', evalSteps, evalAff_lift]
            · by_cases heq : i = n + gs.length
              · subst heq
                have hlenx := hlen x
                conv_lhs => rw [← hlenx, getD_append_singleton_eq]
                simp only [wireAff', lt_irrefl, ↓reduceIte, st', evalSteps, evalAff_lastVar]
                rw [hop, hlist]
                simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
                  id_eq, Bool.and_true]
                rw [hwire u1 x, hwire u2 x, zmod2_and_decide]
              · have hgt : (evalWires gs (List.ofFn (fun j : Fin n => decide (x j = 1)))).length < i := by
                  rw [hlen x]; omega
                rw [getD_append_singleton_gt _ _ _ _ hgt]
                simp only [wireAff', hlt, heq, ↓reduceIte, evalAff_zero]
                decide
          · rw [hlist] at hlen_in; simp at hlen_in
      · have hcount : andCount (gs ++ [g]) = andCount gs := by
          simp [andCount, List.countP_append, hop]
        rw [hcount]
        have hgate : ∃ d_new : Aff n (andCount gs), ∀ x : Vec n,
            g.op.eval (g.inputs.map fun i => (evalWires gs (List.ofFn (fun j : Fin n => decide (x j = 1)))).getD i false) =
              decide (evalAff d_new x (evalSteps st x) = 1) := by
          rcases hlist : g.inputs with _ | ⟨u1, _ | ⟨u2, rest⟩⟩
          · refine ⟨oneAff n (andCount gs), fun x => ?_⟩
            rw [hop, evalAff_one]
            simp only [List.map_nil, GateOp.eval]
            decide
          · refine ⟨addConstAff (wireAff u1) 1, fun x => ?_⟩
            rw [hop, List.map_cons, List.map_nil, hwire u1 x, zmod2_mod2_one, evalAff_addConst]
          · rcases rest with _ | ⟨u3, _⟩
            · refine ⟨addConstAff (addAff (wireAff u1) (wireAff u2)) 1, fun x => ?_⟩
              rw [hop, List.map_cons, List.map_cons, List.map_nil, hwire u1 x, hwire u2 x,
                zmod2_mod2_two, evalAff_addConst, evalAff_add]
            · rw [hlist] at hlen_in; simp at hlen_in
        obtain ⟨d_new, hd_new⟩ := hgate
        let wireAff' : ℕ → Aff n (andCount gs) := fun i =>
          if i < n + gs.length then wireAff i
          else if i = n + gs.length then d_new
          else zeroAff n (andCount gs)
        refine ⟨st, wireAff', fun i x => ?_⟩
        rw [evalWires_append_singleton]
        by_cases hlt : i < n + gs.length
        · have hlt' : i < (evalWires gs (List.ofFn (fun j : Fin n => decide (x j = 1)))).length := by
            rw [hlen x]; exact hlt
          rw [getD_append_singleton_lt _ _ _ _ hlt', hwire i x]
          simp only [wireAff', hlt, ↓reduceIte]
        · by_cases heq : i = n + gs.length
          · subst heq
            have hlenx := hlen x
            conv_lhs => rw [← hlenx, getD_append_singleton_eq]
            rw [hd_new x]
            simp only [wireAff', lt_irrefl, ↓reduceIte]
          · have hgt : (evalWires gs (List.ofFn (fun j : Fin n => decide (x j = 1)))).length < i := by
              rw [hlen x]; omega
            rw [getD_append_singleton_gt _ _ _ _ hgt]
            simp only [wireAff', hlt, heq, ↓reduceIte, evalAff_zero]
            decide
      · have hcount : andCount (gs ++ [g]) = andCount gs := by
          simp [andCount, List.countP_append, hop]
        rw [hcount]
        rcases hlist : g.inputs with _ | ⟨u1, rest⟩
        · rw [hlist] at hlen_in; simp at hlen_in
        · rcases rest with _ | ⟨u2, _⟩
          · let d_new : Aff n (andCount gs) := addConstAff (wireAff u1) 1
            let wireAff' : ℕ → Aff n (andCount gs) := fun i =>
              if i < n + gs.length then wireAff i
              else if i = n + gs.length then d_new
              else zeroAff n (andCount gs)
            refine ⟨st, wireAff', fun i x => ?_⟩
            rw [evalWires_append_singleton]
            by_cases hlt : i < n + gs.length
            · have hlt' : i < (evalWires gs (List.ofFn (fun j : Fin n => decide (x j = 1)))).length := by
                rw [hlen x]; exact hlt
              rw [getD_append_singleton_lt _ _ _ _ hlt', hwire i x]
              simp only [wireAff', hlt, ↓reduceIte]
            · by_cases heq : i = n + gs.length
              · subst heq
                have hlenx := hlen x
                conv_lhs => rw [← hlenx, getD_append_singleton_eq]
                simp only [wireAff', lt_irrefl, ↓reduceIte, d_new]
                rw [hop, hlist, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons,
                  hwire u1 x, zmod2_not_decide, evalAff_addConst]
              · have hgt : (evalWires gs (List.ofFn (fun j : Fin n => decide (x j = 1)))).length < i := by
                  rw [hlen x]; omega
                rw [getD_append_singleton_gt _ _ _ _ hgt]
                simp only [wireAff', hlt, heq, ↓reduceIte, evalAff_zero]
                decide
          · rw [hlist] at hlen_in; simp at hlen_in

private lemma main_bound (n s : ℕ) (family : Finset (Vec n → ZMod 2))
    (hmem : ∀ f ∈ family, ∃ C : Circuit,
      (PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
        (∀ g ∈ C.gates,
          (g.op = .and ∧ g.inputs.length = 2) ∨
          (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨
          (g.op = .not ∧ g.inputs.length = 1))) ∧
      andCount C.gates ≤ s ∧
      ∀ x : Vec n, C.eval (List.ofFn (fun i : Fin n => decide (x i = 1))) = decide (f x = 1)) :
    family.card ≤ 2 ^ (s ^ 2 + 2 * n * s + 2 * s + n + 1) := by
  classical
  let _inst : Fintype (StepList n s) := instFintypeStepList n s
  have hsub : family ⊆ (Finset.univ : Finset (StepList n s × Aff n s)).image evalCode := by
    intro f hf
    obtain ⟨C, ⟨_, hadm⟩, hcost, heval⟩ := hmem f hf
    obtain ⟨st, wireAff, hwire⟩ := simulate_gates n C.gates hadm
    have hkeq : andCount C.gates + (s - andCount C.gates) = s := Nat.add_sub_cancel' hcost
    let padded0 : StepList n (andCount C.gates + (s - andCount C.gates)) ×
        Aff n (andCount C.gates + (s - andCount C.gates)) :=
      padCode (s - andCount C.gates) (st, wireAff C.output)
    let code : StepList n s × Aff n s := hkeq ▸ padded0
    refine Finset.mem_image.mpr ⟨code, Finset.mem_univ code, ?_⟩
    funext x
    rw [evalCode_cast hkeq padded0 x, evalCode_padCode]
    have h1 := heval x
    have h2 := hwire C.output x
    change (evalWires C.gates (List.ofFn (fun i : Fin n => decide (x i = 1)))).getD C.output false =
      decide (f x = 1) at h1
    rw [h2] at h1
    exact zmod2_eq_of_decide_eq _ _ h1
  calc
    family.card ≤ ((Finset.univ : Finset (StepList n s × Aff n s)).image evalCode).card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (StepList n s × Aff n s)).card := Finset.card_image_le
    _ = Fintype.card (StepList n s × Aff n s) := Finset.card_univ
    _ = @Fintype.card (StepList n s) (instFintypeStepList n s) * Fintype.card (Aff n s) :=
      Fintype.card_prod _ _
    _ = 2 ^ (s ^ 2 + 2 * n * s + s) * 2 ^ (n + s + 1) := by
      rw [card_stepList, card_aff]
    _ = 2 ^ (s ^ 2 + 2 * n * s + 2 * s + n + 1) := by
      rw [← pow_add]
      congr 1
      ring

end PEqualNP.Outside.L_lib_504_aux

theorem PEqualNP.Outside.L_lib_504 :
∀ n : ℕ,
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
  ∀ (s : ℕ) (family : Finset (V → ZMod 2)),
    (∀ f ∈ family, ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      admissible C ∧ cost C ≤ s ∧ ∀ x : V, C.eval (input x) = decide (f x = 1)) →
    family.card ≤ 2^(s^2 + 2*n*s + 2*s + n + 1) := by
  intro n V admissible cost input s family hmem
  exact PEqualNP.Outside.L_lib_504_aux.main_bound n s family hmem
