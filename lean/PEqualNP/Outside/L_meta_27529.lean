import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27529_aux

open PEqualNP.CircuitLowerBounds

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def runGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl stepWire w

lemma wires_eq_runGates (C : Circuit) (x : List Bool) :
    C.wires x = runGates C.gates x := rfl

lemma runGates_append (gs1 gs2 : List Gate) (w : List Bool) :
    runGates (gs1 ++ gs2) w = runGates gs2 (runGates gs1 w) :=
  List.foldl_append

lemma runGates_length (gs : List Gate) (w : List Bool) :
    (runGates gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [runGates]
  | cons g gs ih =>
    simp only [runGates, List.foldl_cons] at ih ⊢
    rw [ih]
    simp [stepWire]
    omega

lemma runGates_agree_of_not_mem (gs : List Gate) (w1 w2 : List Bool) (u : Nat)
    (hlen : w1.length = w2.length)
    (hinit : ∀ i, i ≠ u → w1.getD i false = w2.getD i false)
    (hnot : ∀ g ∈ gs, u ∉ g.inputs) :
    ∀ i, i ≠ u → (runGates gs w1).getD i false = (runGates gs w2).getD i false := by
  induction gs generalizing w1 w2 with
  | nil =>
    exact hinit
  | cons g gs ih =>
    have hg : u ∉ g.inputs := hnot g (List.mem_cons_self ..)
    have hrest : ∀ g' ∈ gs, u ∉ g'.inputs := fun g' hg' => hnot g' (List.mem_cons_of_mem _ hg')
    have hbit : g.op.eval (g.inputs.map fun i => w1.getD i false) =
        g.op.eval (g.inputs.map fun i => w2.getD i false) := by
      congr 1
      refine List.map_congr_left fun i hi => ?_
      exact hinit i (fun h => hg (h ▸ hi))
    have hstep_len : (stepWire w1 g).length = (stepWire w2 g).length := by
      simp [stepWire, hlen]
    have hstep_ag : ∀ i, i ≠ u → (stepWire w1 g).getD i false = (stepWire w2 g).getD i false := by
      intro i hi
      by_cases hlt : i < w1.length
      · simp only [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
          List.getElem?_append_left (by omega : i < w2.length)]
        simpa [List.getD_eq_getElem?_getD] using hinit i hi
      · by_cases heq : i = w1.length
        · subst heq
          have h1 : (stepWire w1 g).getD w1.length false = g.op.eval (g.inputs.map fun i => w1.getD i false) := by
            simp [stepWire, List.getD_eq_getElem?_getD]
          have h2 : (stepWire w2 g).getD w1.length false = g.op.eval (g.inputs.map fun i => w2.getD i false) := by
            rw [hlen]; simp [stepWire, List.getD_eq_getElem?_getD]
          rw [h1, h2]
          exact hbit
        · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by simp [stepWire]; omega),
            List.getElem?_eq_none (by simp [stepWire]; omega)]
    exact ih (stepWire w1 g) (stepWire w2 g) hstep_len hstep_ag hrest

def pm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def mkIn (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool) : Fin 9 → Bool :=
  fun i => match i.val with
    | 0 => a0 | 1 => a1 | 2 => a2
    | 3 => a3 | 4 => a4 | 5 => a5
    | 6 => a6 | 7 => a7 | _ => a8

lemma input_witness (u : Nat) (hu : u < 9) :
    ∃ x y : Fin 9 → Bool,
      (∀ i : Fin 9, i.val ≠ u → x i = y i) ∧
      (x 0 || x 1) = (y 0 || y 1) ∧
      (x 3 && x 4) = (y 3 && y 4) ∧
      pm3 x ≠ pm3 y := by
  match u with
  | 0 =>
    refine ⟨mkIn true true false false false true false true false,
            mkIn false true false false false true false true false,
            by decide, by decide, by decide, by decide⟩
  | 1 =>
    refine ⟨mkIn true true false true false false false false true,
            mkIn true false false true false false false false true,
            by decide, by decide, by decide, by decide⟩
  | 2 =>
    refine ⟨mkIn false false true true false false false true false,
            mkIn false false false true false false false true false,
            by decide, by decide, by decide, by decide⟩
  | 3 =>
    refine ⟨mkIn false true false true false false false false true,
            mkIn false true false false false false false false true,
            by decide, by decide, by decide, by decide⟩
  | 4 =>
    refine ⟨mkIn true false false false true false false false true,
            mkIn true false false false false false false false true,
            by decide, by decide, by decide, by decide⟩
  | 5 =>
    refine ⟨mkIn true false false false false true false true false,
            mkIn true false false false false false false true false,
            by decide, by decide, by decide, by decide⟩
  | 6 =>
    refine ⟨mkIn false true false false false true true false false,
            mkIn false true false false false true false false false,
            by decide, by decide, by decide, by decide⟩
  | 7 =>
    refine ⟨mkIn true false false false false true false true false,
            mkIn true false false false false true false false false,
            by decide, by decide, by decide, by decide⟩
  | 8 =>
    refine ⟨mkIn true false false false true false false false true,
            mkIn true false false false true false false false false,
            by decide, by decide, by decide, by decide⟩
  | n + 9 => omega

lemma flatMap_inputs_length_le (gs : List Gate) (h2 : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap fun g => g.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h2 g (List.mem_cons_self ..)
    have hrest := ih (fun g' hg' => h2 g' (List.mem_cons_of_mem _ hg'))
    omega

lemma wires_prefix_two (x : Fin 9 → Bool) :
    let g0 : Gate := ⟨GateOp.or, [0, 1]⟩
    let g1 : Gate := ⟨GateOp.and, [3, 4]⟩
    let w := runGates [g0, g1] (List.ofFn x)
    w.length = 11 ∧
    (∀ i : Fin 9, w.getD i.val false = x i) ∧
    w.getD 9 false = (x 0 || x 1) ∧
    w.getD 10 false = (x 3 && x 4) := by
  intro g0 g1 w
  have hfn : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := by
    simp [List.ofFn_succ]
  have hw : w = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 0 || x 1, x 3 && x 4] := by
    dsimp only [w, g0, g1]
    rw [hfn]
    simp [runGates, stepWire, GateOp.eval]
  rw [hw]
  refine ⟨rfl, ?_, rfl, rfl⟩
  intro i
  fin_cases i <;> rfl

lemma main_proof :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pm3 x) ∧
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
      C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩) := by
  rintro ⟨C, hfan, hsize, heval, hout, _, _, hused, hhead, htail⟩
  rcases hgs : C.gates with _ | ⟨g0, _ | ⟨g1, rest⟩⟩
  · rw [hgs] at hhead; cases hhead
  · rw [hgs] at htail; cases htail
  · rw [hgs] at hhead htail
    simp only [List.head?_cons, List.tail_cons, Option.some.injEq] at hhead htail
    subst hhead htail
    have hlen : C.gates.length = rest.length + 2 := by rw [hgs]; simp
    have hsz : C.size = rest.length + 2 := hlen
    have hout_eq : C.output = rest.length + 10 := by omega
    have hrest_pos : 1 ≤ rest.length := by
      by_contra h0
      have hnil : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hnil
      let x0 := mkIn false false false true true false false false false
      have he0 := heval x0
      have hpre := wires_prefix_two x0
      have hce : C.eval (List.ofFn x0) = (runGates [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [3, 4]⟩] (List.ofFn x0)).getD 10 false := by
        unfold Circuit.eval
        rw [wires_eq_runGates, hgs, hout_eq]
        rfl
      rw [hce, hpre.2.2.2] at he0
      have hbad : (x0 3 && x0 4) ≠ pm3 x0 := by decide
      exact hbad he0
    let L : List Nat := rest.flatMap fun g => g.inputs
    have hLlen : L.length ≤ 2 * rest.length := by
      apply flatMap_inputs_length_le
      intro g hg
      exact (hfan g (by rw [hgs]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg))).2
    have hsub : Finset.range (rest.length + 10) ⊆ L.toFinset := by
      intro u hu
      have hult : u < rest.length + 10 := Finset.mem_range.mp hu
      rw [List.mem_toFinset]
      by_cases hu9 : u < 9
      · by_contra hnot
        have hnotg : ∀ g ∈ rest, u ∉ g.inputs := by
          intro g hg hin
          exact hnot (List.mem_flatMap.mpr ⟨g, hg, hin⟩)
        obtain ⟨x, y, hxy, hg0, hg1, hpm⟩ := input_witness u hu9
        have hxpre := wires_prefix_two x
        have hypre := wires_prefix_two y
        have hinit : ∀ i, i ≠ u →
            (runGates [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [3, 4]⟩] (List.ofFn x)).getD i false =
            (runGates [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [3, 4]⟩] (List.ofFn y)).getD i false := by
          intro i hi
          by_cases hi9 : i < 9
          · have h1 := hxpre.2.1 ⟨i, hi9⟩
            have h2 := hypre.2.1 ⟨i, hi9⟩
            rw [h1, h2]
            exact hxy ⟨i, hi9⟩ hi
          · by_cases hi9e : i = 9
            · subst hi9e; rw [hxpre.2.2.1, hypre.2.2.1, hg0]
            · by_cases hi10 : i = 10
              · subst hi10; rw [hxpre.2.2.2, hypre.2.2.2, hg1]
              · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
                  List.getElem?_eq_none (by rw [hxpre.1]; omega),
                  List.getElem?_eq_none (by rw [hypre.1]; omega)]
        have hag := runGates_agree_of_not_mem rest _ _ u (hxpre.1.trans hypre.1.symm) hinit hnotg
          C.output (by omega)
        have hsplit : C.gates = [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [3, 4]⟩] ++ rest := by
          rw [hgs]; rfl
        have hce : C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
          unfold Circuit.eval
          rw [wires_eq_runGates, wires_eq_runGates, hsplit, runGates_append, runGates_append]
          exact hag
        rw [heval x, heval y] at hce
        exact hpm hce
      · have hjlt : u - 9 < C.gates.length := by omega
        have hj1 : u - 9 + 1 < C.gates.length := by omega
        obtain ⟨k, hjk, hmem⟩ := hused ⟨u - 9, hjlt⟩ hj1
        have hu_eq : 9 + (u - 9) = u := by omega
        rw [hu_eq] at hmem
        have hk2 : 2 ≤ k.val := by
          by_contra hklt
          have hk1 : k.val = 1 := by omega
          have hgk : C.gates.get k = ⟨GateOp.and, [3, 4]⟩ := by
            simp only [List.get_eq_getElem]
            have h1 : C.gates[k.val] = C.gates[1]'(by omega) := by congr 1
            rw [h1]
            simp [hgs]
          rw [hgk] at hmem
          simp at hmem
          omega
        have hkmem : C.gates.get k ∈ rest := by
          have hkrest : k.val - 2 < rest.length := by omega
          have heq : C.gates.get k = rest[k.val - 2]'hkrest := by
            simp only [List.get_eq_getElem]
            rcases Nat.exists_eq_add_of_le hk2 with ⟨t, ht⟩
            have h1 : C.gates[k.val] = C.gates[t + 2]'(by omega) := by congr 1; omega
            have h2 : rest[k.val - 2]'hkrest = rest[t]'(by omega) := by congr 1; omega
            rw [h1, h2]
            simp [hgs]
          rw [heq]
          exact List.getElem_mem hkrest
        exact List.mem_flatMap.mpr ⟨C.gates.get k, hkmem, hmem⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    have hto := List.toFinset_card_le L
    omega

end PEqualNP.Outside.L_meta_27529_aux

theorem PEqualNP.Outside.L_meta_27529 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩)) :=
  PEqualNP.Outside.L_meta_27529_aux.main_proof
