import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20369_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.or, [6, 14]⟩, ⟨GateOp.or, [1, 13]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [12, 18]⟩, ⟨GateOp.or, [21, 19]⟩, ⟨GateOp.or, [0, 17]⟩, ⟨GateOp.or, [23, 20]⟩, ⟨GateOp.or, [6, 11]⟩, ⟨GateOp.or, [25, 12]⟩, ⟨GateOp.or, [26, 17]⟩, ⟨GateOp.or, [5, 16]⟩, ⟨GateOp.or, [28, 20]⟩, ⟨GateOp.or, [11, 16]⟩, ⟨GateOp.or, [30, 18]⟩, ⟨GateOp.or, [4, 15]⟩, ⟨GateOp.or, [32, 19]⟩, ⟨GateOp.or, [8, 15]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [9, 15]⟩, ⟨GateOp.and, [22, 24]⟩, ⟨GateOp.and, [27, 29]⟩, ⟨GateOp.and, [31, 33]⟩, ⟨GateOp.and, [0, 34]⟩, ⟨GateOp.and, [35, 36]⟩, ⟨GateOp.or, [37, 38]⟩, ⟨GateOp.or, [42, 39]⟩, ⟨GateOp.or, [43, 40]⟩, ⟨GateOp.or, [44, 41]⟩], 45⟩

def gateCol (g : Gate) (cs : List ℕ) : ℕ :=
  match g.op, g.inputs with
  | .and, [a, b] => cs.getD a 0 &&& cs.getD b 0
  | .or,  [a, b] => cs.getD a 0 ||| cs.getD b 0
  | _,    _      => 0

def isBinAO (g : Gate) : Bool :=
  (match g.op with | .and => true | .or => true | _ => false) && (g.inputs.length == 2)

def inCols : List ℕ :=
  [0x00000000000000ff, 0x000000000000ff00, 0x0000000000ff0000, 0x00000000ff000000,
   0x000000ff00000000, 0x0000ff0000000000, 0x00ff000000000000, 0xff00000000000000,
   0x0101010101010101, 0x0202020202020202, 0x0404040404040404, 0x0808080808080808,
   0x1010101010101010, 0x2020202020202020, 0x4040404040404040, 0x8080808080808080]

def pcols (gs : List Gate) (cs : List ℕ) : List ℕ :=
  gs.foldl (fun acc g => acc ++ [gateCol g acc]) cs

theorem testBit_gateCol (k : ℕ) (g : Gate) (hg : isBinAO g = true) (cs : List ℕ) (w : List Bool)
    (h : ∀ i, (cs.getD i 0).testBit k = w.getD i false) :
    (gateCol g cs).testBit k = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rcases g with ⟨op, ins⟩
  rcases ins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp [isBinAO] at hg
  cases op <;> simp at hg
  · simp only [gateCol, GateOp.eval, List.map, List.all, id_eq, Bool.and_true, Nat.testBit_and, h a, h b]
  · simp only [gateCol, GateOp.eval, List.map, List.any, id_eq, Bool.or_false, Nat.testBit_or, h a, h b]

theorem testBit_pcols (k : ℕ) (gs : List Gate) (hgs : ∀ g ∈ gs, isBinAO g = true) :
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
          exact testBit_gateCol k g (hgs g List.mem_cons_self) cs w h
        · have h1 : (cs ++ [gateCol g cs]).length ≤ i := by simp; omega
          have h2 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length ≤ i := by simp; omega
          rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]
          exact Nat.zero_testBit k

theorem inCols_fin (u v : Fin 8) (j : Fin 16) :
    (inCols.getD j.val 0).testBit (8 * u.val + v.val) = (oneEach u v).getD j.val false := by
  revert u v j
  decide +kernel

theorem inCols_ok (u v : Fin 8) (i : ℕ) :
    (inCols.getD i 0).testBit (8 * u.val + v.val) = (oneEach u v).getD i false := by
  by_cases hi : i < 16
  · exact inCols_fin u v ⟨i, hi⟩
  · have h1 : inCols.length ≤ i := by simp [inCols]; omega
    have h2 : (oneEach u v).length ≤ i := by simp [oneEach]; omega
    rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]
    exact Nat.zero_testBit _

theorem mono_ : Monotone2 C_ := by
  intro g hg
  have h1 := List.all_eq_true.1 (by decide : C_.gates.all isBinAO = true) g hg
  simp only [isBinAO, Bool.and_eq_true, beq_iff_eq] at h1
  refine ⟨?_, by omega⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem rep_ : Represents (fun u v : Fin 8 => (8982322578471014385 : ℕ).testBit (8 * u.val + v.val)) C_ := by
  intro u v
  have h := testBit_pcols (8 * u.val + v.val) C_.gates
    (List.all_eq_true.1 (by decide : C_.gates.all isBinAO = true))
    inCols (oneEach u v) (by simp [inCols, oneEach]) (inCols_ok u v) C_.output
  have heval : (pcols C_.gates inCols).getD C_.output 0 = 8982322578471014385 := by decide +kernel
  rw [Circuit.eval, Circuit.wires, ← h, heval]

end PEqualNP.Outside.L_meta_20369_aux

theorem PEqualNP.Outside.L_meta_20369 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8982322578471014385 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨PEqualNP.Outside.L_meta_20369_aux.C_, PEqualNP.Outside.L_meta_20369_aux.mono_, by decide, PEqualNP.Outside.L_meta_20369_aux.rep_⟩
