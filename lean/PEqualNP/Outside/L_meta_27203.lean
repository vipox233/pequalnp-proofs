import Mathlib.Data.Finset.Interval
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27203_aux

open PEqualNP.CircuitLowerBounds

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_stepWire_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepWire, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_stepWire_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by
      simp only [stepWire, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (stepWire w g) hlt]
    simp only [stepWire, List.getD_eq_getElem _ _ hi,
      List.getD_eq_getElem _ _ (by simp; omega : i < (w ++ [_]).length),
      List.getElem_append_left hi]

lemma wire_getD_input (C : Circuit) (x : Fin 9 → Bool) (i : Fin 9) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  unfold Circuit.wires
  change (C.gates.foldl stepWire (List.ofFn x)).getD i.val false = x i
  have hi : i.val < (List.ofFn x).length := by simp
  rw [foldl_stepWire_prefix C.gates (List.ofFn x) i.val hi, List.getD_eq_getElem _ _ hi,
    List.getElem_ofFn]

lemma wire_getD_gate (C : Circuit) (x : Fin 9 → Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires (List.ofFn x)).getD (9 + j) false =
      (C.gates[j]'hj).op.eval
        ((C.gates[j]'hj).inputs.map fun i =>
          ((C.gates.take j).foldl stepWire (List.ofFn x)).getD i false) := by
  unfold Circuit.wires
  change (C.gates.foldl stepWire (List.ofFn x)).getD (9 + j) false = _
  have hsplit : C.gates = C.gates.take j ++ (C.gates[j]'hj) :: C.gates.drop (j + 1) := by
    have h1 : C.gates.take j ++ C.gates.drop j = C.gates := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = (C.gates[j]'hj) :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2, h1]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pref := (C.gates.take j).foldl stepWire (List.ofFn x)
  have hlen : pref.length = 9 + j := by
    rw [foldl_stepWire_len, List.length_ofFn, List.length_take]
    omega
  have hlt : 9 + j < (stepWire pref (C.gates[j]'hj)).length := by
    simp only [stepWire, List.length_append, List.length_cons, List.length_nil, hlen]
    omega
  rw [foldl_stepWire_prefix (C.gates.drop (j + 1)) (stepWire pref (C.gates[j]'hj)) (9 + j) hlt]
  dsimp only [stepWire]
  have hlt' : 9 + j < (pref ++ [(C.gates[j]'hj).op.eval ((C.gates[j]'hj).inputs.map fun i => pref.getD i false)]).length := by
    simp only [List.length_append, List.length_cons, List.length_nil, hlen]
    omega
  rw [List.getD_eq_getElem _ _ hlt', List.getElem_append_right (by omega : pref.length ≤ 9 + j)]
  simp only [hlen, Nat.sub_self, List.getElem_cons_zero]

lemma wire_getD_gate_full (C : Circuit) (x : Fin 9 → Bool) (j : ℕ) (hj : j < C.gates.length)
    (hback : ∀ i ∈ (C.gates[j]'hj).inputs, i < 9 + j) :
    (C.wires (List.ofFn x)).getD (9 + j) false =
      (C.gates[j]'hj).op.eval
        ((C.gates[j]'hj).inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
  rw [wire_getD_gate C x j hj]
  congr 1
  refine List.map_congr_left ?_
  intro i hi
  have hlt : i < 9 + j := hback i hi
  unfold Circuit.wires
  change ((C.gates.take j).foldl stepWire (List.ofFn x)).getD i false =
    (C.gates.foldl stepWire (List.ofFn x)).getD i false
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  conv_rhs => rw [hsplit]
  rw [List.foldl_append]
  have hlen : ((C.gates.take j).foldl stepWire (List.ofFn x)).length = 9 + j := by
    rw [foldl_stepWire_len, List.length_ofFn, List.length_take]
    omega
  rw [foldl_stepWire_prefix (C.gates.drop j) _ i (by omega)]

def pm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def mkIn (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool) : Fin 9 → Bool
  | ⟨0, _⟩ => b0
  | ⟨1, _⟩ => b1
  | ⟨2, _⟩ => b2
  | ⟨3, _⟩ => b3
  | ⟨4, _⟩ => b4
  | ⟨5, _⟩ => b5
  | ⟨6, _⟩ => b6
  | ⟨7, _⟩ => b7
  | ⟨8, _⟩ => b8

def witX (v : Fin 9) : Fin 9 → Bool :=
  match v with
  | ⟨0, _⟩ => mkIn false false false false false true false true false
  | ⟨1, _⟩ => mkIn false false false true false false false false true
  | ⟨2, _⟩ => mkIn false false false true false false false true false
  | ⟨3, _⟩ => mkIn false false true false false false false true false
  | ⟨4, _⟩ => mkIn false false true false false false true false false
  | ⟨5, _⟩ => mkIn true false false false false false false true false
  | ⟨6, _⟩ => mkIn false true false false false true false false false
  | ⟨7, _⟩ => mkIn true false false false false true false false false
  | ⟨8, _⟩ => mkIn true false false false true false false false false

def witY (v : Fin 9) : Fin 9 → Bool :=
  fun i => if i = v then true else witX v i

lemma wit_props (v : Fin 9) :
    (∀ i : Fin 9, i ≠ v → witX v i = witY v i) ∧
    (witX v 0 && witX v 4) = (witY v 0 && witY v 4) ∧
    (witX v 2 && witX v 5) = (witY v 2 && witY v 5) ∧
    pm3 (witX v) ≠ pm3 (witY v) := by
  have hall : ∀ v : Fin 9,
      (∀ i : Fin 9, i ≠ v → witX v i = witY v i) ∧
      (witX v 0 && witX v 4) = (witY v 0 && witY v 4) ∧
      (witX v 2 && witX v 5) = (witY v 2 && witY v 5) ∧
      pm3 (witX v) ≠ pm3 (witY v) := by
    decide
  exact hall v

lemma agree_of_unused (C : Circuit)
    (hback : ∀ (j : ℕ) (hj : j < C.gates.length), ∀ i ∈ (C.gates[j]'hj).inputs, i < 9 + j)
    (v : Fin 9)
    (hunused : ∀ (j : ℕ) (hj : j < C.gates.length), 2 ≤ j → v.val ∉ (C.gates[j]'hj).inputs)
    (x y : Fin 9 → Bool)
    (hxy_in : ∀ i : Fin 9, i ≠ v → x i = y i)
    (h9 : (C.wires (List.ofFn x)).getD 9 false = (C.wires (List.ofFn y)).getD 9 false)
    (h10 : (C.wires (List.ofFn x)).getD 10 false = (C.wires (List.ofFn y)).getD 10 false) :
    ∀ w : ℕ, w < 9 + C.gates.length → w ≠ v.val →
      (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hne
    by_cases h9lt : w < 9
    · have hfx := wire_getD_input C x ⟨w, h9lt⟩
      have hfy := wire_getD_input C y ⟨w, h9lt⟩
      rw [hfx, hfy]
      exact hxy_in ⟨w, h9lt⟩ (fun h => hne (congrArg Fin.val h))
    · by_cases hw9 : w = 9
      · subst hw9; exact h9
      · by_cases hw10 : w = 10
        · subst hw10; exact h10
        · have hj2 : 2 ≤ w - 9 := by omega
          have hjlt : w - 9 < C.gates.length := by omega
          have hw_eq : 9 + (w - 9) = w := by omega
          rw [← hw_eq, wire_getD_gate_full C x (w - 9) hjlt (hback (w - 9) hjlt),
            wire_getD_gate_full C y (w - 9) hjlt (hback (w - 9) hjlt)]
          congr 1
          refine List.map_congr_left ?_
          intro u hu
          have hult : u < 9 + (w - 9) := hback (w - 9) hjlt u hu
          have hune : u ≠ v.val := fun h => hunused (w - 9) hjlt hj2 (h ▸ hu)
          exact ih u (by omega) (by omega) hune

lemma list_flatMap_length_le_two (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 : g.inputs.length ≤ 2 := h g List.mem_cons_self
    have h2 : (gs.flatMap Gate.inputs).length ≤ 2 * gs.length :=
      ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg'))
    omega

lemma mem_drop_of_ge {α : Type*} (l : List α) (d j : ℕ) (hj : j < l.length) (hd : d ≤ j) :
    l[j]'hj ∈ l.drop d := by
  have hj' : j - d < (l.drop d).length := by rw [List.length_drop]; omega
  have hidx : d + (j - d) = j := by omega
  have h : (l.drop d)[j - d]'hj' = l[j]'hj := by
    simp only [List.getElem_drop, hidx]
  rw [← h]
  exact List.getElem_mem hj'

theorem main_proof :
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
      C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∧
      C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 5]⟩) := by
  rintro ⟨C, _, hSize, hEval, hOut, hShape, _, hUsed, hHead, hTail⟩
  have hS_le : C.gates.length ≤ 11 := hSize
  cases hg0 : C.gates with
  | nil => simp [hg0] at hHead
  | cons g0 rest0 =>
    simp only [hg0, List.head?_cons, Option.some.injEq] at hHead
    subst hHead
    cases hg1 : rest0 with
    | nil => simp [hg0, hg1] at hTail
    | cons g1 tail =>
      simp only [hg0, hg1, List.tail_cons, List.head?_cons, Option.some.injEq] at hTail
      subst hTail
      have hge2 : 2 ≤ C.gates.length := by rw [hg0, hg1]; simp
      have hback : ∀ (j : ℕ) (hj : j < C.gates.length), ∀ i ∈ (C.gates[j]'hj).inputs, i < 9 + j := by
        intro j hj i hi
        have hs := hShape ⟨j, hj⟩
        simp only [List.get_eq_getElem] at hs
        rcases hs with ⟨_, a, ha, hinp⟩ | ⟨_, a, b, hab, hb, hinp⟩
        · rw [hinp] at hi
          simp only [List.mem_singleton] at hi
          omega
        · rw [hinp] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl <;> omega
      have hg0_val : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 0 && x 4) := by
        intro x
        have h := wire_getD_gate_full C x 0 (by omega) (hback 0 (by omega))
        have hg0e : C.gates[0]'(by omega) = ⟨.and, [0, 4]⟩ := by simp [hg0]
        rw [hg0e] at h
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
          Bool.and_true] at h
        have h0 : (C.wires (List.ofFn x)).getD 0 false = x 0 := wire_getD_input C x 0
        have h4 : (C.wires (List.ofFn x)).getD 4 false = x 4 := wire_getD_input C x 4
        rw [h0, h4] at h
        exact h
      have hg1_val : ∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 10 false = (x 2 && x 5) := by
        intro x
        have h := wire_getD_gate_full C x 1 (by omega) (hback 1 (by omega))
        have hg1e : C.gates[1]'(by omega) = ⟨.and, [2, 5]⟩ := by simp [hg0, hg1]
        rw [hg1e] at h
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
          Bool.and_true] at h
        have h2 : (C.wires (List.ofFn x)).getD 2 false = x 2 := wire_getD_input C x 2
        have h5 : (C.wires (List.ofFn x)).getD 5 false = x 5 := wire_getD_input C x 5
        rw [h2, h5] at h
        exact h
      have hTailEq : tail = C.gates.drop 2 := by simp [hg0, hg1]
      have hSlots_in : ∀ v : Fin 9, v.val ∈ tail.flatMap Gate.inputs := by
        intro v
        by_contra hnot
        have hunused : ∀ (j : ℕ) (hj : j < C.gates.length), 2 ≤ j → v.val ∉ (C.gates[j]'hj).inputs := by
          intro j hj hj2 hmem
          apply hnot
          refine List.mem_flatMap.mpr ⟨C.gates[j]'hj, ?_, hmem⟩
          rw [hTailEq]
          exact mem_drop_of_ge C.gates 2 j hj hj2
        obtain ⟨hxy, h9e, h10e, hpm⟩ := wit_props v
        have h9w : (C.wires (List.ofFn (witX v))).getD 9 false =
            (C.wires (List.ofFn (witY v))).getD 9 false := by
          rw [hg0_val, hg0_val, h9e]
        have h10w : (C.wires (List.ofFn (witX v))).getD 10 false =
            (C.wires (List.ofFn (witY v))).getD 10 false := by
          rw [hg1_val, hg1_val, h10e]
        have hout_lt : C.output < 9 + C.gates.length := by
          change C.output + 1 = 9 + C.gates.length at hOut
          omega
        have hout_ne : C.output ≠ v.val := by
          change C.output + 1 = 9 + C.gates.length at hOut
          have := v.isLt
          omega
        have heq_out := agree_of_unused C hback v hunused (witX v) (witY v) hxy h9w h10w
          C.output hout_lt hout_ne
        have hevX : C.eval (List.ofFn (witX v)) = pm3 (witX v) := hEval (witX v)
        have hevY : C.eval (List.ofFn (witY v)) = pm3 (witY v) := hEval (witY v)
        exact hpm (hevX.symm.trans (heq_out.trans hevY))
      have hSlots_gate : ∀ j : ℕ, j + 1 < C.gates.length → 9 + j ∈ tail.flatMap Gate.inputs := by
        intro j hjlt
        obtain ⟨k, hjk, hmem⟩ := hUsed ⟨j, by omega⟩ hjlt
        dsimp only at hjk hmem
        have hk2 : 2 ≤ k.val := by
          by_contra hlt2
          have hk1 : k.val = 1 := by omega
          have hmem' : 9 + j ∈ (C.gates[k.val]'k.isLt).inputs := by
            simpa only [List.get_eq_getElem] using hmem
          have hgk : C.gates[k.val]'k.isLt = ⟨.and, [2, 5]⟩ := by
            simp only [hk1, hg0, hg1, List.getElem_cons_succ, List.getElem_cons_zero]
          rw [hgk] at hmem'
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem'
          omega
        refine List.mem_flatMap.mpr ⟨C.gates[k.val]'k.isLt, ?_, by simpa only [List.get_eq_getElem] using hmem⟩
        rw [hTailEq]
        exact mem_drop_of_ge C.gates 2 k.val k.isLt hk2
      have hreq_sub : Finset.range (8 + C.gates.length) ⊆ (tail.flatMap Gate.inputs).toFinset := by
        intro w hw
        rw [List.mem_toFinset]
        rw [Finset.mem_range] at hw
        by_cases hw9 : w < 9
        · exact hSlots_in ⟨w, hw9⟩
        · have h := hSlots_gate (w - 9) (by omega)
          have hw_eq : 9 + (w - 9) = w := by omega
          rwa [hw_eq] at h
      have htail_len : tail.length = C.gates.length - 2 := by rw [hTailEq, List.length_drop]
      have htail_le2 : ∀ g ∈ tail, g.inputs.length ≤ 2 := by
        intro g hg
        rw [hTailEq] at hg
        obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hg
        have hjlt : 2 + idx < C.gates.length := by simp at hidx; omega
        have hs := hShape ⟨2 + idx, hjlt⟩
        simp only [List.get_eq_getElem] at hs
        rw [List.getElem_drop]
        rcases hs with ⟨_, a, _, hinp⟩ | ⟨_, a, b, _, _, hinp⟩ <;> simp [hinp]
      have hlen_le : (tail.flatMap Gate.inputs).length ≤ 2 * tail.length :=
        list_flatMap_length_le_two tail htail_le2
      have hcard_le : (Finset.range (8 + C.gates.length)).card ≤ (tail.flatMap Gate.inputs).toFinset.card :=
        Finset.card_le_card hreq_sub
      have hfin_le : (tail.flatMap Gate.inputs).toFinset.card ≤ (tail.flatMap Gate.inputs).length :=
        List.toFinset_card_le _
      rw [Finset.card_range] at hcard_le
      omega

end PEqualNP.Outside.L_meta_27203_aux

theorem PEqualNP.Outside.L_meta_27203 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 5]⟩) :=
  PEqualNP.Outside.L_meta_27203_aux.main_proof
