import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22244_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def gates : List Gate := [⟨.or, [5, 8]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 13]⟩, ⟨.and, [1, 14]⟩, ⟨.and, [2, 12]⟩, ⟨.and, [3, 15]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [21, 19]⟩]
def circuit : Circuit := ⟨gates, 22⟩
def inputs : List ℕ := [63, 4032, 258048, 16515072, 266305, 532610, 1065220, 2130440, 4260880, 8521760]

def valid (g : Gate) : Bool :=
  match g.op, g.inputs with
  | .and, [_, _] | .or, [_, _] => true
  | _, _ => false

def nstep (cols : List ℕ) (g : Gate) : List ℕ :=
  cols ++ [match g.op, g.inputs with
    | .and, [a, b] => cols.getD a 0 &&& cols.getD b 0
    | .or, [a, b] => cols.getD a 0 ||| cols.getD b 0
    | _, _ => 0]

def bstep (wires : List Bool) (g : Gate) : List Bool :=
  wires ++ [g.op.eval (g.inputs.map fun j => wires.getD j false)]

theorem read_bit (cs : List ℕ) (i k : ℕ) :
    (cs.map (fun c => c.testBit k)).getD i false = (cs.getD i 0).testBit k := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases cs[i]? <;> simp

theorem option_bit (c : Option ℕ) (k : ℕ) :
    (c.map (fun j => j.testBit k)).getD false = (c.getD 0).testBit k := by
  cases c <;> simp

theorem bstep_of_nstep (cs : List ℕ) (k : ℕ) (g : Gate) (h : valid g = true) :
    (nstep cs g).map (fun c => c.testBit k) = bstep (cs.map (fun c => c.testBit k)) g := by
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;>
    simp_all [valid, nstep, bstep, GateOp.eval, option_bit, Nat.testBit_and, Nat.testBit_or]

theorem fold_bit (gs : List Gate) (cs : List ℕ) (k : ℕ) (hg : ∀ g ∈ gs, valid g = true) :
    (gs.foldl nstep cs).map (fun c => c.testBit k) =
      gs.foldl bstep (cs.map (fun c => c.testBit k)) := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih _ (fun h hh => hg h (List.mem_cons_of_mem _ hh))]
      rw [bstep_of_nstep cs k g (hg g List.mem_cons_self)]

theorem all_valid : gates.all valid = true := by decide +kernel

theorem mono : Monotone2 circuit := by
  intro g hg
  have h := List.all_eq_true.mp all_valid g hg
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp_all [valid]

set_option maxRecDepth 12000 in
theorem input_bits : ∀ (u : Fin 4) (v : Fin 6),
    inputs.map (fun c => c.testBit (6 * u.val + v.val)) = oneEach u v := by
  decide +kernel

set_option maxRecDepth 12000 in
theorem packed_output : (gates.foldl nstep inputs).getD 22 0 = 808954 := by
  decide +kernel

theorem represents : Represents (fun (u : Fin 4) (v : Fin 6) =>
    (808954 : ℕ).testBit (6 * u.val + v.val)) circuit := by
  intro u v
  change ((gates.foldl bstep (oneEach u v)).getD 22 false) = _
  rw [← input_bits u v, ← fold_bit gates inputs (6 * u.val + v.val) (List.all_eq_true.mp all_valid)]
  rw [read_bit, packed_output]

end PEqualNP.Outside.L_meta_22244_aux

theorem PEqualNP.Outside.L_meta_22244 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808954 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22244_aux.circuit, PEqualNP.Outside.L_meta_22244_aux.mono,
    by decide, PEqualNP.Outside.L_meta_22244_aux.represents⟩
