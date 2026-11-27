import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25430_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C_ : Circuit := ⟨[⟨.or, [2, 1]⟩, ⟨.or, [3, 0]⟩, ⟨.and, [7, 6]⟩, ⟨.not, [8]⟩, ⟨.or, [9, 7]⟩, ⟨.not, [9]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [12, 9]⟩, ⟨.and, [5, 3]⟩, ⟨.or, [13, 14]⟩], 15⟩

def fullM : ℕ := 2 ^ 36 - 1

def gateCol (g : Gate) (cs : List ℕ) : ℕ :=
  match g.op, g.inputs with
  | .and, [a, b] => cs.getD a 0 &&& cs.getD b 0
  | .or,  [a, b] => cs.getD a 0 ||| cs.getD b 0
  | .not, [a]    => fullM ^^^ cs.getD a 0
  | _,    _      => 0

def okG (g : Gate) : Bool :=
  match g.op, g.inputs with
  | .and, [_, _] => true
  | .or,  [_, _] => true
  | .not, [_]    => true
  | _,    _      => false

def inCols : List ℕ := [1090785407, 2181574594, 4363383044, 8740700680, 18241094672, 68191127584]

def pcols (gs : List Gate) (cs : List ℕ) : List ℕ :=
  gs.foldl (fun acc g => acc ++ [gateCol g acc]) cs

theorem testBit_gateCol (k : ℕ) (hk : k < 36) (g : Gate) (hg : okG g = true) (cs : List ℕ) (w : List Bool)
    (h : ∀ i, (cs.getD i 0).testBit k = w.getD i false) :
    (gateCol g cs).testBit k = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [okG] at hg
  · simp only [gateCol, GateOp.eval, List.map, List.all, id_eq, Bool.and_true, Nat.testBit_and, h a, h b]
  · simp only [gateCol, GateOp.eval, List.map, List.any, id_eq, Bool.or_false, Nat.testBit_or, h a, h b]
  · simp only [gateCol, fullM, GateOp.eval, List.map, List.headD, Nat.testBit_xor,
      Nat.testBit_two_pow_sub_one, decide_eq_true hk, Bool.true_xor, h a]

theorem testBit_pcols (k : ℕ) (hk : k < 36) (gs : List Gate) (hgs : ∀ g ∈ gs, okG g = true) :
    ∀ (cs : List ℕ) (w : List Bool), cs.length = w.length →
      (∀ i, (cs.getD i 0).testBit k = w.getD i false) →
      (∀ i, ((pcols gs cs).getD i 0).testBit k =
            (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false) := by
  induction gs with
  | nil => intro cs w _ h i; exact h i
  | cons g gs ih =>
    intro cs w hlen h
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [hlen]
    · intro i
      by_cases hi : i < cs.length
      · have hi' : i < w.length := hlen ▸ hi
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
            List.getElem_append_left hi, List.getElem_append_left hi',
            ← List.getD_eq_getElem cs 0 hi, ← List.getD_eq_getElem w false hi']
        exact h i
      · by_cases heq : i = cs.length
        · subst heq
          have h1 : (cs ++ [gateCol g cs]).getD cs.length 0 = gateCol g cs := by simp
          have h2 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD cs.length false =
                    g.op.eval (g.inputs.map fun i => w.getD i false) := by rw [hlen]; simp
          rw [h1, h2]
          exact testBit_gateCol k hk g (hgs g List.mem_cons_self) cs w h
        · have h1 : (cs ++ [gateCol g cs]).length ≤ i := by simp; omega
          have h2 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length ≤ i := by simp; omega
          rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]
          exact Nat.zero_testBit k

theorem inCols_lt (i j m : Fin 6) :
    (inCols.getD m.val 0).testBit (6 * i.val + j.val) = decide (m = i ∨ m = j) := by
  revert i j m; decide +kernel

theorem inCols_ok (i j : Fin 6) (m : ℕ) :
    (inCols.getD m 0).testBit (6 * i.val + j.val) =
    (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)).getD m false := by
  by_cases hm : m < 6
  · rw [List.getD_eq_getElem (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) false (by rw [List.length_ofFn]; exact hm), List.getElem_ofFn]
    exact inCols_lt i j ⟨m, hm⟩
  · have ha : inCols.length ≤ m := by change 6 ≤ m; omega
    have hb : (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)).length ≤ m := by rw [List.length_ofFn]; omega
    rw [List.getD_eq_default _ _ ha, List.getD_eq_default _ _ hb]
    exact Nat.zero_testBit _

theorem wf_ : FanInTwo C_ := by
  intro g hg
  have h1 := List.all_eq_true.1 (by decide : C_.gates.all okG = true) g hg
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [okG] at h1
  · exact ⟨by simp, by simp⟩
  · exact ⟨by simp, by simp⟩
  · exact ⟨by simp, by simp⟩

theorem targ_ok (i j : Fin 6) :
    (16372952505 : ℕ).testBit (6 * i.val + j.val) = (14896569 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  revert i j; decide +kernel

theorem eval_ok (i j : Fin 6) :
    C_.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
    (14896569 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  have hk : 6 * i.val + j.val < 36 := by omega
  have h := testBit_pcols (6 * i.val + j.val) hk C_.gates
    (List.all_eq_true.1 (by decide : C_.gates.all okG = true))
    inCols (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j))
    (by simp [inCols]) (inCols_ok i j) C_.output
  have heval : (pcols C_.gates inCols).getD C_.output 0 = 16372952505 := by decide +kernel
  rw [Circuit.eval, Circuit.wires, ← h, heval, targ_ok]

end PEqualNP.Outside.L_meta_25430_aux

theorem PEqualNP.Outside.L_meta_25430 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (14896569 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25430_aux.C_, PEqualNP.Outside.L_meta_25430_aux.wf_, by decide, PEqualNP.Outside.L_meta_25430_aux.eval_ok⟩
