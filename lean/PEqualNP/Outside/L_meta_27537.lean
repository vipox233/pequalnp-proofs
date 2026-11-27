import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27537_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl step w

lemma wires_eq_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

lemma W_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (W gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hfold : W (g :: gs) w = W gs (step w g) := rfl
    rw [hfold]
    have hlen : i < (step w g).length := by
      simp only [step, List.length_append, List.length_singleton]
      omega
    rw [ih (step w g) hlen]
    simp only [step, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hi]

lemma W_getD_add (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
    (hin : ∀ i ∈ (gs.get ⟨j, hj⟩).inputs, i < w.length + j) :
    (W gs w).getD (w.length + j) false =
      (gs.get ⟨j, hj⟩).op.eval ((gs.get ⟨j, hj⟩).inputs.map fun i => (W gs w).getD i false) := by
  induction gs generalizing w j with
  | nil => cases hj
  | cons g gs ih =>
    have hfold : W (g :: gs) w = W gs (step w g) := rfl
    rw [hfold]
    cases j with
    | zero =>
      simp only [Nat.add_zero] at hin ⊢
      have hlen : w.length < (step w g).length := by
        simp only [step, List.length_append, List.length_singleton]
        omega
      rw [W_getD_lt gs (step w g) w.length hlen]
      have hget0 : (g :: gs).get ⟨0, hj⟩ = g := rfl
      rw [hget0] at hin ⊢
      have hstep : (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp only [step, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (le_refl _)]
        simp
      rw [hstep]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hil : i < w.length := hin i hi
      rw [W_getD_lt gs (step w g) i (by simp only [step, List.length_append, List.length_singleton]; omega)]
      simp only [step, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left hil]
    | succ j' =>
      have hj' : j' < gs.length := by simp at hj; omega
      have hgetS : (g :: gs).get ⟨j' + 1, hj⟩ = gs.get ⟨j', hj'⟩ := rfl
      rw [hgetS] at hin ⊢
      have hrew : w.length + (j' + 1) = (step w g).length + j' := by
        simp only [step, List.length_append, List.length_singleton]
        omega
      rw [hrew]
      exact ih (step w g) j' hj' (fun i hi => by
        have := hin i hi
        simp only [step, List.length_append, List.length_singleton]
        omega)

def wireVal (C : Circuit) (x : Fin 9 → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wireVal_lt9 (C : Circuit) (x : Fin 9 → Bool) (i : Fin 9) :
    wireVal C x i.val = x i := by
  unfold wireVal
  rw [wires_eq_W, W_getD_lt C.gates (List.ofFn x) i.val (by simp [i.isLt])]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

lemma wireVal_nat (C : Circuit) (x : Fin 9 → Bool) (w : ℕ) (hw : w < 9) :
    wireVal C x w = x ⟨w, hw⟩ :=
  wireVal_lt9 C x ⟨w, hw⟩

lemma wireVal_gate (C : Circuit) (x : Fin 9 → Bool) (j : Fin C.gates.length)
    (hin : ∀ i ∈ (C.gates.get j).inputs, i < 9 + j.val) :
    wireVal C x (9 + j.val) =
      (C.gates.get j).op.eval ((C.gates.get j).inputs.map (wireVal C x)) := by
  unfold wireVal
  rw [wires_eq_W]
  have hlen : (List.ofFn x).length = 9 := by simp
  have h := W_getD_add C.gates (List.ofFn x) j.val j.isLt (by rw [hlen]; exact hin)
  rw [hlen] at h
  exact h

def Restricted (x : Fin 9 → Bool) : Prop := x 0 = true ∧ x 3 = false

def IsConst (C : Circuit) (w : ℕ) : Prop :=
  ∀ x y : Fin 9 → Bool, Restricted x → Restricted y → wireVal C x w = wireVal C y w

def NormalGate (C : Circuit) : Prop :=
  ∀ j : Fin C.gates.length,
    ((C.gates.get j).op = GateOp.not ∧ ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
    (((C.gates.get j).op = GateOp.and ∨ (C.gates.get j).op = GateOp.or) ∧
      ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])

lemma normal_inputs_lt {C : Circuit} (hNF : NormalGate C) (j : Fin C.gates.length) :
    ∀ i ∈ (C.gates.get j).inputs, i < 9 + j.val := by
  rcases hNF j with ⟨_, a, ha, hin⟩ | ⟨_, a, b, hab, hb, hin⟩
  · intro i hi
    rw [hin] at hi
    simp at hi
    omega
  · intro i hi
    rw [hin] at hi
    simp at hi
    rcases hi with rfl | rfl <;> omega

lemma normal_inputs_len {C : Circuit} (hNF : NormalGate C) (j : Fin C.gates.length) :
    (C.gates.get j).inputs.length ≤ 2 := by
  rcases hNF j with ⟨_, a, _, hin⟩ | ⟨_, a, b, _, _, hin⟩
  · rw [hin]; simp
  · rw [hin]; simp

def V7 : Finset ℕ := {1, 2, 4, 5, 6, 7, 8}

lemma V7_card : V7.card = 7 := by decide

lemma V7_essential (v : ℕ) (hv : v ∈ V7) :
    ∃ x y : Fin 9 → Bool, Restricted x ∧ Restricted y ∧
      (∀ i : Fin 9, i.val ≠ v → x i = y i) ∧ pm3 x ≠ pm3 y := by
  simp only [V7, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨fun i => decide (i = 0 ∨ i = 5 ∨ i = 6),
      fun i => decide (i = 0 ∨ i = 1 ∨ i = 5 ∨ i = 6),
      ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, by decide⟩
    intro i hi; fin_cases i <;> simp_all
  · refine ⟨fun i => decide (i = 0 ∨ i = 4 ∨ i = 6),
      fun i => decide (i = 0 ∨ i = 2 ∨ i = 4 ∨ i = 6),
      ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, by decide⟩
    intro i hi; fin_cases i <;> simp_all
  · refine ⟨fun i => decide (i = 0 ∨ i = 8),
      fun i => decide (i = 0 ∨ i = 4 ∨ i = 8),
      ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, by decide⟩
    intro i hi; fin_cases i <;> simp_all
  · refine ⟨fun i => decide (i = 0 ∨ i = 7),
      fun i => decide (i = 0 ∨ i = 5 ∨ i = 7),
      ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, by decide⟩
    intro i hi; fin_cases i <;> simp_all
  · refine ⟨fun i => decide (i = 0 ∨ i = 1 ∨ i = 5),
      fun i => decide (i = 0 ∨ i = 1 ∨ i = 5 ∨ i = 6),
      ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, by decide⟩
    intro i hi; fin_cases i <;> simp_all
  · refine ⟨fun i => decide (i = 0 ∨ i = 5),
      fun i => decide (i = 0 ∨ i = 5 ∨ i = 7),
      ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, by decide⟩
    intro i hi; fin_cases i <;> simp_all
  · refine ⟨fun i => decide (i = 0 ∨ i = 4),
      fun i => decide (i = 0 ∨ i = 4 ∨ i = 8),
      ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, by decide⟩
    intro i hi; fin_cases i <;> simp_all

section ClassicalPart

open Classical

noncomputable def src (C : Circuit) (w : ℕ) : ℕ :=
  if h : 9 ≤ w ∧ w - 9 < C.gates.length then
    let j : Fin C.gates.length := ⟨w - 9, h.2⟩
    let g := C.gates.get j
    if ¬ IsConst C w then
      match g.inputs with
      | [a, b] =>
        if _ha : a < w ∧ b < w ∧ IsConst C a ∧ ¬ IsConst C b then src C b
        else if _hb : a < w ∧ b < w ∧ IsConst C b ∧ ¬ IsConst C a then src C a
        else w
      | _ => w
    else w
  else w
termination_by w

lemma wireVal_not_const_and {C : Circuit} (a b : ℕ)
    (ha : IsConst C a) (hnc : ¬ ∀ x y : Fin 9 → Bool, Restricted x → Restricted y →
      (wireVal C x a && wireVal C x b) = (wireVal C y a && wireVal C y b)) :
    ∀ x : Fin 9 → Bool, Restricted x → wireVal C x a = true := by
  intro x hx
  by_contra hfalse
  have hxa : wireVal C x a = false := by cases h : wireVal C x a <;> simp_all
  apply hnc
  intro u v hu hv
  have hua : wireVal C u a = false := (ha u x hu hx).trans hxa
  have hva : wireVal C v a = false := (ha v x hv hx).trans hxa
  simp [hua, hva]

lemma wireVal_not_const_or {C : Circuit} (a b : ℕ)
    (ha : IsConst C a) (hnc : ¬ ∀ x y : Fin 9 → Bool, Restricted x → Restricted y →
      (wireVal C x a || wireVal C x b) = (wireVal C y a || wireVal C y b)) :
    ∀ x : Fin 9 → Bool, Restricted x → wireVal C x a = false := by
  intro x hx
  by_contra htrue
  have hxa : wireVal C x a = true := by cases h : wireVal C x a <;> simp_all
  apply hnc
  intro u v hu hv
  have hua : wireVal C u a = true := (ha u x hu hx).trans hxa
  have hva : wireVal C v a = true := (ha v x hv hx).trans hxa
  simp [hua, hva]

lemma src_props (C : Circuit) (hNF : NormalGate C)
    (h0c : IsConst C 0) (h3c : IsConst C 3) (h9c : IsConst C 9) (h10c : IsConst C 10) :
    ∀ w : ℕ, w < 9 + C.gates.length → ¬ IsConst C w →
      src C w ≤ w ∧
      (∀ x : Fin 9 → Bool, Restricted x → wireVal C x w = wireVal C x (src C w)) ∧
      ((src C w < 9 ∧ src C w ≠ 0 ∧ src C w ≠ 3) ∨
        ∃ j : Fin C.gates.length, 2 ≤ j.val ∧ src C w = 9 + j.val ∧
          ¬ IsConst C (9 + j.val) ∧ ∀ i ∈ (C.gates.get j).inputs, ¬ IsConst C i) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlt hnc
    by_cases hge : 9 ≤ w
    · have hjlt : w - 9 < C.gates.length := by omega
      let j : Fin C.gates.length := ⟨w - 9, hjlt⟩
      have hwj : 9 + j.val = w := by simp [j]; omega
      have hj2 : 2 ≤ j.val := by
        by_contra hlt2
        have : j.val = 0 ∨ j.val = 1 := by omega
        rcases this with h0 | h1
        · have : w = 9 := by omega
          exact hnc (this ▸ h9c)
        · have : w = 10 := by omega
          exact hnc (this ▸ h10c)
      have hgate_eq : ∀ x : Fin 9 → Bool,
          wireVal C x w = (C.gates.get j).op.eval ((C.gates.get j).inputs.map (wireVal C x)) := by
        intro x
        rw [← hwj]
        exact wireVal_gate C x j (normal_inputs_lt hNF j)
      rcases hNF j with ⟨hop, a, ha, hin⟩ | ⟨hop, a, b, hab, hb, hin⟩
      · have hanc : ¬ IsConst C a := by
          intro hac
          apply hnc
          intro x y hx hy
          rw [hgate_eq x, hgate_eq y, hop, hin]
          simp [GateOp.eval, hac x y hx hy]
        have hsrc : src C w = w := by
          rw [src]
          simp only [hge, hjlt, and_self, dite_true, hnc, not_false_eq_true, ite_true]
          have hgin : (C.gates.get ⟨w - 9, hjlt⟩).inputs = [a] := hin
          rw [hgin]
        rw [hsrc]
        refine ⟨le_refl w, fun _ _ => rfl, Or.inr ⟨j, hj2, hwj.symm, hwj.symm ▸ hnc, ?_⟩⟩
        intro i hi
        rw [hin] at hi
        simp at hi
        exact hi ▸ hanc
      · have haw : a < w := by omega
        have hbw : b < w := by omega
        have hnotboth : ¬ (IsConst C a ∧ IsConst C b) := by
          rintro ⟨hac, hbc⟩
          apply hnc
          intro x y hx hy
          rw [hgate_eq x, hgate_eq y, hin]
          rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval, hac x y hx hy, hbc x y hx hy]
        by_cases hac : IsConst C a
        · have hbnc : ¬ IsConst C b := fun hbc => hnotboth ⟨hac, hbc⟩
          have hsrc : src C w = src C b := by
            rw [src]
            simp only [hge, hjlt, and_self, dite_true, hnc, not_false_eq_true, ite_true]
            have hgin : (C.gates.get ⟨w - 9, hjlt⟩).inputs = [a, b] := hin
            rw [hgin]
            simp [haw, hbw, hac, hbnc]
          have hih := ih b hbw (by omega) hbnc
          rw [hsrc]
          refine ⟨le_trans hih.1 (le_of_lt hbw), ?_, hih.2.2⟩
          intro x hx
          rw [← hih.2.1 x hx, hgate_eq x, hin]
          rcases hop with hop | hop
          · rw [hop]
            have hat : wireVal C x a = true := wireVal_not_const_and a b hac (by
              intro hcon
              apply hnc
              intro u v hu hv
              rw [hgate_eq u, hgate_eq v, hop, hin]
              simpa [GateOp.eval] using hcon u v hu hv) x hx
            simp [GateOp.eval, hat]
          · rw [hop]
            have haf : wireVal C x a = false := wireVal_not_const_or a b hac (by
              intro hcon
              apply hnc
              intro u v hu hv
              rw [hgate_eq u, hgate_eq v, hop, hin]
              simpa [GateOp.eval] using hcon u v hu hv) x hx
            simp [GateOp.eval, haf]
        · by_cases hbc : IsConst C b
          · have hsrc : src C w = src C a := by
              rw [src]
              simp only [hge, hjlt, and_self, dite_true, hnc, not_false_eq_true, ite_true]
              have hgin : (C.gates.get ⟨w - 9, hjlt⟩).inputs = [a, b] := hin
              rw [hgin]
              simp [haw, hbw, hac, hbc]
            have hih := ih a haw (by omega) hac
            rw [hsrc]
            refine ⟨le_trans hih.1 (le_of_lt haw), ?_, hih.2.2⟩
            intro x hx
            rw [← hih.2.1 x hx, hgate_eq x, hin]
            rcases hop with hop | hop
            · rw [hop]
              have hbt : wireVal C x b = true := wireVal_not_const_and b a hbc (by
                intro hcon
                apply hnc
                intro u v hu hv
                rw [hgate_eq u, hgate_eq v, hop, hin]
                simpa [GateOp.eval, Bool.and_comm] using hcon u v hu hv) x hx
              simp [GateOp.eval, hbt]
            · rw [hop]
              have hbf : wireVal C x b = false := wireVal_not_const_or b a hbc (by
                intro hcon
                apply hnc
                intro u v hu hv
                rw [hgate_eq u, hgate_eq v, hop, hin]
                simpa [GateOp.eval, Bool.or_comm] using hcon u v hu hv) x hx
              simp [GateOp.eval, hbf]
          · have hsrc : src C w = w := by
              rw [src]
              simp only [hge, hjlt, and_self, dite_true, hnc, not_false_eq_true, ite_true]
              have hgin : (C.gates.get ⟨w - 9, hjlt⟩).inputs = [a, b] := hin
              rw [hgin]
              simp [hac, hbc]
            rw [hsrc]
            refine ⟨le_refl w, fun _ _ => rfl, Or.inr ⟨j, hj2, hwj.symm, hwj.symm ▸ hnc, ?_⟩⟩
            intro i hi
            rw [hin] at hi
            simp at hi
            rcases hi with rfl | rfl
            · exact hac
            · exact hbc
    · have hw9 : w < 9 := by omega
      have hsrc : src C w = w := by
        rw [src]
        simp [hge]
      rw [hsrc]
      refine ⟨le_refl w, fun _ _ => rfl, Or.inl ⟨hw9, ?_, ?_⟩⟩
      · intro h0; exact hnc (h0 ▸ h0c)
      · intro h3; exact hnc (h3 ▸ h3c)

lemma main_proof :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
        (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pm3 x) ∧
        C.output + 1 = 9 + C.size ∧
        NormalGate C ∧
        (∀ j : Fin C.gates.length,
          (∃ x y : Fin 9 → Bool,
            (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
          ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
            (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
        (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
          ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
        C.gates.head? = some ⟨GateOp.or, [0, 1]⟩ ∧
        C.gates.tail.head? = some ⟨GateOp.and, [3, 8]⟩) := by
  rintro ⟨C, _, hSize, hEval, hOut, hNF, _, hUse, hHead, hTail⟩
  have hLenLe : C.gates.length ≤ 11 := hSize
  cases hgs : C.gates with
  | nil => simp [hgs] at hHead
  | cons g0 rest =>
    rw [hgs] at hHead hTail
    simp only [List.head?_cons, Option.some.injEq] at hHead
    cases rest with
    | nil => simp at hTail
    | cons g1 rest2 =>
      simp only [List.tail_cons, List.head?_cons, Option.some.injEq] at hTail
      have hLenGe2 : 2 ≤ C.gates.length := by rw [hgs]; simp
      have hg0 : C.gates.get ⟨0, by omega⟩ = ⟨GateOp.or, [0, 1]⟩ := by
        simp [hgs, hHead]
      have hg1 : C.gates.get ⟨1, by omega⟩ = ⟨GateOp.and, [3, 8]⟩ := by
        simp [hgs, hTail]
      have hEvalWire : ∀ x : Fin 9 → Bool, wireVal C x C.output = pm3 x := fun x => hEval x
      have hOutEq : C.output = 9 + (C.gates.length - 1) := by
        change C.output + 1 = 9 + C.gates.length at hOut
        omega
      have hW9 : ∀ x : Fin 9 → Bool, wireVal C x 9 = (x 0 || x 1) := by
        intro x
        have h := wireVal_gate C x ⟨0, by omega⟩ (normal_inputs_lt hNF ⟨0, by omega⟩)
        rw [hg0] at h
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          Bool.or_false, id_eq] at h
        rw [wireVal_nat C x 0 (by omega), wireVal_nat C x 1 (by omega)] at h
        exact h
      have hW10 : ∀ x : Fin 9 → Bool, wireVal C x 10 = (x 3 && x 8) := by
        intro x
        have h := wireVal_gate C x ⟨1, by omega⟩ (normal_inputs_lt hNF ⟨1, by omega⟩)
        rw [hg1] at h
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq] at h
        rw [wireVal_nat C x 3 (by omega), wireVal_nat C x 8 (by omega)] at h
        exact h
      have hLenGt2 : 2 < C.gates.length := by
        by_contra hle2
        have heq2 : C.gates.length = 2 := by omega
        have hout10 : C.output = 10 := by omega
        let xw : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 4 ∨ i = 8)
        have h1 := hEvalWire xw
        rw [hout10, hW10 xw] at h1
        have h2 : (xw 3 && xw 8) = false := by decide
        have h3 : pm3 xw = true := by decide
        rw [h2, h3] at h1
        exact Bool.false_ne_true h1
      have h0c : IsConst C 0 := by
        intro x y hx hy
        rw [wireVal_nat C x 0 (by omega), wireVal_nat C y 0 (by omega)]
        exact hx.1.trans hy.1.symm
      have h3c : IsConst C 3 := by
        intro x y hx hy
        rw [wireVal_nat C x 3 (by omega), wireVal_nat C y 3 (by omega)]
        exact hx.2.trans hy.2.symm
      have h9c : IsConst C 9 := by
        intro x y hx hy
        rw [hW9 x, hW9 y, hx.1, hy.1]
        simp
      have h10c : IsConst C 10 := by
        intro x y hx hy
        rw [hW10 x, hW10 y, hx.2, hy.2]
        simp
      have hOutNotConst : ¬ IsConst C C.output := by
        intro hcon
        let xa : Fin 9 → Bool := fun i => decide (i = 0)
        let xb : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 4 ∨ i = 8)
        have h1 := hcon xa xb ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
        rw [hEvalWire xa, hEvalWire xb] at h1
        have h2 : pm3 xa = false := by decide
        have h3 : pm3 xb = true := by decide
        rw [h2, h3] at h1
        exact Bool.false_ne_true h1
      have hUse9 : ∃ k : Fin C.gates.length, 2 ≤ k.val ∧ 9 ∈ (C.gates.get k).inputs := by
        obtain ⟨k, hkgt, hkmem⟩ := hUse ⟨0, by omega⟩ (show 0 + 1 < C.gates.length by omega)
        dsimp only at hkgt hkmem
        refine ⟨k, ?_, hkmem⟩
        by_contra hlt2
        have hk1 : k = ⟨1, by omega⟩ := Fin.ext (show k.val = 1 by omega)
        rw [hk1, hg1] at hkmem
        simp at hkmem
      have hUse10 : ∃ k : Fin C.gates.length, 2 ≤ k.val ∧ 10 ∈ (C.gates.get k).inputs := by
        obtain ⟨k, hkgt, hkmem⟩ := hUse ⟨1, by omega⟩ (show 1 + 1 < C.gates.length by omega)
        dsimp only at hkgt hkmem
        exact ⟨k, by omega, hkmem⟩
      have hUse0 : ∃ k : Fin C.gates.length, 2 ≤ k.val ∧ 0 ∈ (C.gates.get k).inputs := by
        by_contra hno
        push Not at hno
        let x0 : Fin 9 → Bool := fun i => decide (i = 1 ∨ i = 4 ∨ i = 8)
        let x1 : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 8)
        have hall : ∀ w : ℕ, w < 9 + C.gates.length → w ≠ 0 → wireVal C x0 w = wireVal C x1 w := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hlt hne
            by_cases h9 : w < 9
            · rw [wireVal_nat C x0 w h9, wireVal_nat C x1 w h9]
              have hne' : (⟨w, h9⟩ : Fin 9) ≠ 0 := fun h => hne (congrArg Fin.val h)
              simp [x0, x1, hne']
            · by_cases hw9 : w = 9
              · rw [hw9, hW9 x0, hW9 x1]; decide
              · by_cases hw10 : w = 10
                · rw [hw10, hW10 x0, hW10 x1]; decide
                · let k : Fin C.gates.length := ⟨w - 9, by omega⟩
                  have hwk : 9 + k.val = w := by simp [k]; omega
                  have hk2 : 2 ≤ k.val := by simp [k]; omega
                  rw [← hwk, wireVal_gate C x0 k (normal_inputs_lt hNF k),
                    wireVal_gate C x1 k (normal_inputs_lt hNF k)]
                  congr 1
                  apply List.map_congr_left
                  intro a ha
                  have halt : a < w := by rw [← hwk]; exact normal_inputs_lt hNF k a ha
                  have hane : a ≠ 0 := fun h0 => hno k hk2 (h0 ▸ ha)
                  exact ih a halt (by omega) hane
        have hEqOut := hall C.output (by omega) (by omega)
        rw [hEvalWire x0, hEvalWire x1] at hEqOut
        have h2 : pm3 x0 = false := by decide
        have h3 : pm3 x1 = true := by decide
        rw [h2, h3] at hEqOut
        exact Bool.false_ne_true hEqOut
      have hUse3 : ∃ k : Fin C.gates.length, 2 ≤ k.val ∧ 3 ∈ (C.gates.get k).inputs := by
        by_contra hno
        push Not at hno
        let y0 : Fin 9 → Bool := fun i => decide (i = 2 ∨ i = 7)
        let y1 : Fin 9 → Bool := fun i => decide (i = 2 ∨ i = 3 ∨ i = 7)
        have hall : ∀ w : ℕ, w < 9 + C.gates.length → w ≠ 3 → wireVal C y0 w = wireVal C y1 w := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hlt hne
            by_cases h9 : w < 9
            · rw [wireVal_nat C y0 w h9, wireVal_nat C y1 w h9]
              have hne' : (⟨w, h9⟩ : Fin 9) ≠ 3 := fun h => hne (congrArg Fin.val h)
              simp [y0, y1, hne']
            · by_cases hw9 : w = 9
              · rw [hw9, hW9 y0, hW9 y1]; decide
              · by_cases hw10 : w = 10
                · rw [hw10, hW10 y0, hW10 y1]; decide
                · let k : Fin C.gates.length := ⟨w - 9, by omega⟩
                  have hwk : 9 + k.val = w := by simp [k]; omega
                  have hk2 : 2 ≤ k.val := by simp [k]; omega
                  rw [← hwk, wireVal_gate C y0 k (normal_inputs_lt hNF k),
                    wireVal_gate C y1 k (normal_inputs_lt hNF k)]
                  congr 1
                  apply List.map_congr_left
                  intro a ha
                  have halt : a < w := by rw [← hwk]; exact normal_inputs_lt hNF k a ha
                  have hane : a ≠ 3 := fun h3 => hno k hk2 (h3 ▸ ha)
                  exact ih a halt (by omega) hane
        have hEqOut := hall C.output (by omega) (by omega)
        rw [hEvalWire y0, hEvalWire y1] at hEqOut
        have h2 : pm3 y0 = false := by decide
        have h3 : pm3 y1 = true := by decide
        rw [h2, h3] at hEqOut
        exact Bool.false_ne_true hEqOut
      let G2 : Finset (Fin C.gates.length) := Finset.univ.filter fun j => 2 ≤ j.val
      let Gconst : Finset (Fin C.gates.length) := G2.filter fun j => IsConst C (9 + j.val)
      let Gpass : Finset (Fin C.gates.length) := G2.filter fun j =>
        ¬ IsConst C (9 + j.val) ∧ ∃ a ∈ (C.gates.get j).inputs, IsConst C a
      let Grem : Finset (Fin C.gates.length) := G2.filter fun j =>
        ¬ IsConst C (9 + j.val) ∧ ∀ a ∈ (C.gates.get j).inputs, ¬ IsConst C a
      have hG2_card : G2.card = C.gates.length - 2 := by
        have hcompl : G2 = Finset.univ \ {⟨0, by omega⟩, ⟨1, by omega⟩} := by
          ext j
          simp only [G2, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
            Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
          omega
        have hpair : ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin C.gates.length)).card = 2 := by
          rw [Finset.card_pair]
          intro h
          have := congrArg Fin.val h
          simp at this
        rw [hcompl, Finset.card_sdiff, Finset.inter_univ, Finset.card_fin, hpair]
      have hPart : Gconst.card + Gpass.card + Grem.card = G2.card := by
        have h1 : Disjoint Gconst Gpass := by
          rw [Finset.disjoint_left]
          intro j hj1 hj2
          simp only [Gconst, Gpass, Finset.mem_filter] at hj1 hj2
          exact hj2.2.1 hj1.2
        have h2 : Disjoint (Gconst ∪ Gpass) Grem := by
          rw [Finset.disjoint_left]
          intro j hj1 hj2
          simp only [Finset.mem_union, Gconst, Gpass, Grem, Finset.mem_filter] at hj1 hj2
          rcases hj1 with hj1 | hj1
          · exact hj2.2.1 hj1.2
          · obtain ⟨a, ha, hac⟩ := hj1.2.2
            exact hj2.2.2 a ha hac
        have hunion : (Gconst ∪ Gpass) ∪ Grem = G2 := by
          ext j
          simp only [Finset.mem_union, Gconst, Gpass, Grem, Finset.mem_filter]
          constructor
          · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
          · intro hj
            by_cases hc : IsConst C (9 + j.val)
            · exact Or.inl (Or.inl ⟨hj, hc⟩)
            · by_cases hex : ∃ a ∈ (C.gates.get j).inputs, IsConst C a
              · exact Or.inl (Or.inr ⟨hj, hc, hex⟩)
              · push Not at hex
                exact Or.inr ⟨hj, hc, hex⟩
        rw [← hunion, Finset.card_union_of_disjoint h2, Finset.card_union_of_disjoint h1]
      let K0 : Finset ℕ := {0, 3, 9, 10}
      let S : Finset ℕ := K0 ∪ Gconst.image fun j => 9 + j.val
      have hS_card : S.card = 4 + Gconst.card := by
        have hdisj : Disjoint K0 (Gconst.image fun j => 9 + j.val) := by
          rw [Finset.disjoint_left]
          intro w hw1 hw2
          simp only [Finset.mem_image, Gconst, G2, Finset.mem_filter] at hw2
          obtain ⟨j, ⟨⟨_, hj2⟩, _⟩, rfl⟩ := hw2
          simp only [K0, Finset.mem_insert, Finset.mem_singleton] at hw1
          omega
        have hK0 : K0.card = 4 := by decide
        have hinj : Set.InjOn (fun j : Fin C.gates.length => 9 + j.val) ↑Gconst := by
          intro a _ b _ hab
          dsimp only at hab
          exact Fin.ext (by omega)
        rw [Finset.card_union_of_disjoint hdisj, hK0, Finset.card_image_of_injOn hinj]
      have hS_const : ∀ w ∈ S, IsConst C w := by
        intro w hw
        simp only [S, K0, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          Finset.mem_image, Gconst, Finset.mem_filter] at hw
        rcases hw with (rfl | rfl | rfl | rfl) | ⟨j, ⟨_, hcj⟩, rfl⟩
        · exact h0c
        · exact h3c
        · exact h9c
        · exact h10c
        · exact hcj
      have hS_used : ∀ w ∈ S, ∃ k ∈ G2, w ∈ (C.gates.get k).inputs := by
        intro w hw
        simp only [S, K0, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          Finset.mem_image, Gconst, G2, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        rcases hw with (rfl | rfl | rfl | rfl) | ⟨j, ⟨hj2, hcj⟩, rfl⟩
        · exact hUse0
        · exact hUse3
        · exact hUse9
        · exact hUse10
        · have hjlt : j.val + 1 < C.gates.length := by
            by_contra hge
            have hlast : 9 + j.val = C.output := by omega
            exact hOutNotConst (hlast ▸ hcj)
          obtain ⟨k, hkgt, hkmem⟩ := hUse j hjlt
          exact ⟨k, by omega, hkmem⟩
      let E : Finset (ℕ × Fin C.gates.length) :=
        (S ×ˢ G2).filter fun p => p.1 ∈ (C.gates.get p.2).inputs
      have hE_ge : S.card ≤ E.card := by
        have hsub : S ⊆ E.image Prod.fst := by
          intro w hw
          obtain ⟨k, hk, hmem⟩ := hS_used w hw
          refine Finset.mem_image.mpr ⟨(w, k), ?_, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hw, hk⟩, hmem⟩
        exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
      have hE_le : E.card ≤ 2 * Gconst.card + Gpass.card := by
        have hsub : E ⊆ (Gconst ∪ Gpass).biUnion fun k =>
            (S.filter fun w => w ∈ (C.gates.get k).inputs).image fun w => (w, k) := by
          intro p hp
          simp only [E, Finset.mem_filter, Finset.mem_product] at hp
          rcases hp with ⟨⟨hwS, hkG2⟩, hmem⟩
          rw [Finset.mem_biUnion]
          refine ⟨p.2, ?_, ?_⟩
          · rw [Finset.mem_union]
            by_cases hc : IsConst C (9 + p.2.val)
            · exact Or.inl (Finset.mem_filter.mpr ⟨hkG2, hc⟩)
            · exact Or.inr (Finset.mem_filter.mpr ⟨hkG2, hc, p.1, hmem, hS_const p.1 hwS⟩)
          · exact Finset.mem_image.mpr ⟨p.1, Finset.mem_filter.mpr ⟨hwS, hmem⟩, rfl⟩
        have h1 := le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
        have hdisj_cp : Disjoint Gconst Gpass := by
          rw [Finset.disjoint_left]
          intro j hj1 hj2
          simp only [Gconst, Gpass, Finset.mem_filter] at hj1 hj2
          exact hj2.2.1 hj1.2
        rw [Finset.sum_union hdisj_cp] at h1
        have hc_bound : ∑ k ∈ Gconst,
            ((S.filter fun w => w ∈ (C.gates.get k).inputs).image fun w => (w, k)).card ≤
            2 * Gconst.card := by
          calc ∑ k ∈ Gconst,
                ((S.filter fun w => w ∈ (C.gates.get k).inputs).image fun w => (w, k)).card
              ≤ ∑ k ∈ Gconst, 2 := by
                apply Finset.sum_le_sum
                intro k _
                calc ((S.filter fun w => w ∈ (C.gates.get k).inputs).image fun w => (w, k)).card
                    ≤ (S.filter fun w => w ∈ (C.gates.get k).inputs).card := Finset.card_image_le
                  _ ≤ (C.gates.get k).inputs.toFinset.card := by
                      apply Finset.card_le_card
                      intro w hw
                      simp only [Finset.mem_filter] at hw
                      exact List.mem_toFinset.mpr hw.2
                  _ ≤ (C.gates.get k).inputs.length := List.toFinset_card_le _
                  _ ≤ 2 := normal_inputs_len hNF k
            _ = 2 * Gconst.card := by simp [Nat.mul_comm]
        have hp_bound : ∑ k ∈ Gpass,
            ((S.filter fun w => w ∈ (C.gates.get k).inputs).image fun w => (w, k)).card ≤
            Gpass.card := by
          calc ∑ k ∈ Gpass,
                ((S.filter fun w => w ∈ (C.gates.get k).inputs).image fun w => (w, k)).card
              ≤ ∑ k ∈ Gpass, 1 := by
                apply Finset.sum_le_sum
                intro k hk
                calc ((S.filter fun w => w ∈ (C.gates.get k).inputs).image fun w => (w, k)).card
                    ≤ (S.filter fun w => w ∈ (C.gates.get k).inputs).card := Finset.card_image_le
                  _ ≤ 1 := by
                      rw [Finset.card_le_one]
                      intro w1 hw1 w2 hw2
                      simp only [Finset.mem_filter] at hw1 hw2
                      simp only [Gpass, Finset.mem_filter] at hk
                      have hwc1 : IsConst C w1 := hS_const w1 hw1.1
                      have hwc2 : IsConst C w2 := hS_const w2 hw2.1
                      rcases hNF k with ⟨hop, a, _, hin⟩ | ⟨hop, a, b, _, _, hin⟩
                      · rw [hin] at hw1 hw2
                        simp at hw1 hw2
                        omega
                      · rw [hin] at hw1 hw2
                        simp at hw1 hw2
                        by_contra hne
                        have hboth : IsConst C a ∧ IsConst C b := by
                          rcases hw1.2 with rfl | rfl <;> rcases hw2.2 with rfl | rfl
                          · exact absurd rfl hne
                          · exact ⟨hwc1, hwc2⟩
                          · exact ⟨hwc2, hwc1⟩
                          · exact absurd rfl hne
                        apply hk.2.1
                        intro x y hx hy
                        rw [wireVal_gate C x k (normal_inputs_lt hNF k),
                          wireVal_gate C y k (normal_inputs_lt hNF k), hin]
                        rcases hop with hop | hop <;> rw [hop] <;>
                          simp [GateOp.eval, hboth.1 x y hx hy, hboth.2 x y hx hy]
            _ = Gpass.card := by simp
        omega
      have hGrem_le5 : Grem.card ≤ 5 := by omega
      have hSrcAll := src_props C hNF h0c h3c h9c h10c
      have hOutSrc := hSrcAll C.output (by omega) hOutNotConst
      have hOutInGrem : ∃ jout ∈ Grem, src C C.output = 9 + jout.val := by
        rcases hOutSrc.2.2 with ⟨hlt9, hne0, hne3⟩ | ⟨j, hj2, hjeq, hjnc, hjins⟩
        · exfalso
          have hmemV7 : src C C.output ∈ V7 := by
            simp only [V7, Finset.mem_insert, Finset.mem_singleton]
            omega
          have hother : ∃ v ∈ V7, v ≠ src C C.output := by
            by_cases h1 : src C C.output = 1
            · exact ⟨2, by decide, by omega⟩
            · exact ⟨1, by decide, by omega⟩
          obtain ⟨v, hvV7, hvne⟩ := hother
          obtain ⟨x, y, hx, hy, hagree, hdiff⟩ := V7_essential v hvV7
          apply hdiff
          rw [← hEvalWire x, ← hEvalWire y, hOutSrc.2.1 x hx, hOutSrc.2.1 y hy]
          rw [wireVal_nat C x (src C C.output) hlt9, wireVal_nat C y (src C C.output) hlt9]
          exact hagree ⟨src C C.output, hlt9⟩ (by simpa using hvne.symm)
        · refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj2⟩, hjnc, hjins⟩, hjeq⟩
      obtain ⟨jout, hjoutGrem, hjoutEq⟩ := hOutInGrem
      let inSrc (k : Fin C.gates.length) : List ℕ := (C.gates.get k).inputs.map (src C)
      let ClosedSets : Finset (Finset (Fin C.gates.length)) :=
        Grem.powerset.filter fun R => jout ∈ R ∧ ∀ k ∈ R, ∀ j ∈ Grem, 9 + j.val ∈ inSrc k → j ∈ R
      have hGremMem : Grem ∈ ClosedSets := by
        simp only [ClosedSets, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.Subset.refl _, hjoutGrem, fun _ _ j hj _ => hj⟩
      obtain ⟨R, hRmem, hRmin⟩ := Finset.exists_min_image ClosedSets Finset.card ⟨Grem, hGremMem⟩
      simp only [ClosedSets, Finset.mem_filter, Finset.mem_powerset] at hRmem
      rcases hRmem with ⟨hRsub, hjoutR, hRclosed⟩
      have hR_used : ∀ j ∈ R.erase jout, ∃ k ∈ R, 9 + j.val ∈ inSrc k := by
        intro j hj
        by_contra hno
        push Not at hno
        have hne : j ≠ jout := (Finset.mem_erase.mp hj).1
        have hjR : j ∈ R := (Finset.mem_erase.mp hj).2
        have hErMem : R.erase j ∈ ClosedSets := by
          simp only [ClosedSets, Finset.mem_filter, Finset.mem_powerset]
          refine ⟨Finset.Subset.trans (Finset.erase_subset j R) hRsub,
            Finset.mem_erase.mpr ⟨hne.symm, hjoutR⟩, ?_⟩
          intro k hk j' hj' hmem
          have hkR : k ∈ R := (Finset.mem_erase.mp hk).2
          have hj'R : j' ∈ R := hRclosed k hkR j' hj' hmem
          have hj'ne : j' ≠ j := fun heq => hno k hkR (heq ▸ hmem)
          exact Finset.mem_erase.mpr ⟨hj'ne, hj'R⟩
        have hcard := hRmin (R.erase j) hErMem
        have hlt : (R.erase j).card < R.card := Finset.card_erase_lt_of_mem hjR
        omega
      have hV7_used : ∀ v ∈ V7, ∃ k ∈ R, v ∈ inSrc k := by
        intro v hvV7
        by_contra hno
        push Not at hno
        obtain ⟨x, y, hx, hy, hagree, hdiff⟩ := V7_essential v hvV7
        have hallR : ∀ n : ℕ, ∀ k ∈ R, k.val = n → wireVal C x (9 + k.val) = wireVal C y (9 + k.val) := by
          intro n
          induction n using Nat.strong_induction_on with
          | ind n ih =>
            intro k hkR hkn
            have hkGrem : k ∈ Grem := hRsub hkR
            have hkGrem' := Finset.mem_filter.mp hkGrem
            rw [wireVal_gate C x k (normal_inputs_lt hNF k),
              wireVal_gate C y k (normal_inputs_lt hNF k)]
            congr 1
            apply List.map_congr_left
            intro a ha
            have halt : a < 9 + k.val := normal_inputs_lt hNF k a ha
            have hanc : ¬ IsConst C a := hkGrem'.2.2 a ha
            have hsp := hSrcAll a (by omega) hanc
            rw [hsp.2.1 x hx, hsp.2.1 y hy]
            have hmemIn : src C a ∈ inSrc k := List.mem_map.mpr ⟨a, ha, rfl⟩
            rcases hsp.2.2 with ⟨hlt9, _, _⟩ | ⟨j, hj2, hjeq, hjnc, hjins⟩
            · have hne : src C a ≠ v := fun heq => hno k hkR (heq ▸ hmemIn)
              rw [wireVal_nat C x (src C a) hlt9, wireVal_nat C y (src C a) hlt9]
              exact hagree ⟨src C a, hlt9⟩ hne
            · have hjGrem : j ∈ Grem :=
                Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj2⟩, hjnc, hjins⟩
              have hjR : j ∈ R := hRclosed k hkR j hjGrem (hjeq ▸ hmemIn)
              have hjlt : j.val < n := by
                have := hsp.1
                omega
              rw [hjeq]
              exact ih j.val hjlt j hjR rfl
        apply hdiff
        rw [← hEvalWire x, ← hEvalWire y, hOutSrc.2.1 x hx, hOutSrc.2.1 y hy, hjoutEq]
        exact hallR jout.val jout hjoutR rfl
      let Wset : Finset ℕ := V7 ∪ (R.erase jout).image fun j => 9 + j.val
      have hW_card : Wset.card = 7 + (R.card - 1) := by
        have hdisj : Disjoint V7 ((R.erase jout).image fun j => 9 + j.val) := by
          rw [Finset.disjoint_left]
          intro w hw1 hw2
          simp only [Finset.mem_image] at hw2
          obtain ⟨j, _, rfl⟩ := hw2
          simp only [V7, Finset.mem_insert, Finset.mem_singleton] at hw1
          omega
        have hinj : Set.InjOn (fun j : Fin C.gates.length => 9 + j.val) ↑(R.erase jout) := by
          intro a _ b _ hab
          dsimp only at hab
          exact Fin.ext (by omega)
        rw [Finset.card_union_of_disjoint hdisj, V7_card,
          Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hjoutR]
      have hW_sub : Wset ⊆ R.biUnion fun k => (inSrc k).toFinset := by
        intro w hw
        rw [Finset.mem_biUnion]
        simp only [Wset, Finset.mem_union, Finset.mem_image] at hw
        rcases hw with hwV7 | ⟨j, hjEr, rfl⟩
        · obtain ⟨k, hkR, hmem⟩ := hV7_used w hwV7
          exact ⟨k, hkR, List.mem_toFinset.mpr hmem⟩
        · obtain ⟨k, hkR, hmem⟩ := hR_used j hjEr
          exact ⟨k, hkR, List.mem_toFinset.mpr hmem⟩
      have hW_le : Wset.card ≤ 2 * R.card := by
        calc Wset.card
            ≤ (R.biUnion fun k => (inSrc k).toFinset).card := Finset.card_le_card hW_sub
          _ ≤ ∑ k ∈ R, (inSrc k).toFinset.card := Finset.card_biUnion_le
          _ ≤ ∑ k ∈ R, 2 := by
              apply Finset.sum_le_sum
              intro k _
              calc (inSrc k).toFinset.card
                  ≤ (inSrc k).length := List.toFinset_card_le _
                _ = (C.gates.get k).inputs.length := List.length_map _
                _ ≤ 2 := normal_inputs_len hNF k
          _ = 2 * R.card := by simp [Nat.mul_comm]
      have hR_pos : 1 ≤ R.card := Finset.card_pos.mpr ⟨jout, hjoutR⟩
      have hR_le5 : R.card ≤ 5 := le_trans (Finset.card_le_card hRsub) hGrem_le5
      omega

end ClassicalPart

end PEqualNP.Outside.L_meta_27537_aux

theorem PEqualNP.Outside.L_meta_27537 :
¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩) :=
  PEqualNP.Outside.L_meta_27537_aux.main_proof
