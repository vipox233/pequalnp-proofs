import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23634_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [11, 7]⟩, ⟨GateOp.or, [12, 8]⟩, ⟨GateOp.or, [13, 9]⟩, ⟨GateOp.or, [5, 10]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [14, 15]⟩, ⟨GateOp.and, [16, 17]⟩, ⟨GateOp.or, [18, 19]⟩], 20⟩

def gateCol (g : Gate) (cs : List ℕ) : ℕ :=
  match g.op, g.inputs with
  | .and, [a, b] => cs.getD a 0 &&& cs.getD b 0
  | .or,  [a, b] => cs.getD a 0 ||| cs.getD b 0
  | _,    _      => 0

def isBinAO (g : Gate) : Bool :=
  (match g.op with | .and => true | .or => true | _ => false) && (g.inputs.length == 2)

def inCols : List ℕ :=
  List.ofFn (fun i : Fin 4 => (63 : ℕ) <<< (6 * i.val)) ++
  List.ofFn (fun j : Fin 6 => (266305 : ℕ) <<< j.val)

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

theorem bit_63 (t : ℕ) : (63 : ℕ).testBit t = decide (t < 6) := by
  have h : (63 : ℕ) = 2 ^ 6 - 1 := by decide
  rw [h, Nat.testBit_two_pow_sub_one]

theorem bit_col0 (k : Fin 24) : (266305 : ℕ).testBit k.val = decide (k.val % 6 = 0) := by
  revert k; decide

theorem inCols_ok (u : Fin 4) (v : Fin 6) (i : ℕ) :
    (inCols.getD i 0).testBit (6 * u.val + v.val) = (oneEach u v).getD i false := by
  by_cases h1 : i < 4
  · rw [inCols, oneEach, List.getD_append _ _ _ _ (by simp [h1]), List.getD_append _ _ _ _ (by simp [h1]),
        List.getD_eq_getElem _ _ (by simp [h1]), List.getD_eq_getElem _ _ (by simp [h1]),
        List.getElem_ofFn, List.getElem_ofFn, Nat.testBit_shiftLeft, bit_63]
    by_cases he : i = u.val
    · subst he
      have hge : 6 * u.val ≤ 6 * u.val + v.val := by omega
      have hlt : 6 * u.val + v.val - 6 * u.val < 6 := by omega
      simp [hge, hlt, Fin.ext_iff]
    · have hbad : ¬ (6 * i ≤ 6 * u.val + v.val ∧ 6 * u.val + v.val - 6 * i < 6) := by omega
      cases hge : decide (6 * i ≤ 6 * u.val + v.val)
      · simp [Fin.ext_iff, he]
      · have hge' : 6 * i ≤ 6 * u.val + v.val := of_decide_eq_true hge
        have hnotlt : ¬ (6 * u.val + v.val - 6 * i < 6) := fun h => hbad ⟨hge', h⟩
        simp [hnotlt, Fin.ext_iff, he]
  · by_cases h2 : i < 10
    · have hl1 : (List.ofFn (fun k : Fin 4 => (63 : ℕ) <<< (6 * k.val))).length ≤ i := by simp; omega
      have hl2 : (List.ofFn (fun k : Fin 4 => decide (k = u))).length ≤ i := by simp; omega
      rw [inCols, oneEach, List.getD_append_right _ _ _ _ hl1, List.getD_append_right _ _ _ _ hl2]
      simp only [List.length_ofFn]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
          List.getElem_ofFn, List.getElem_ofFn, Nat.testBit_shiftLeft]
      by_cases hge : i - 4 ≤ 6 * u.val + v.val
      · have hk : 6 * u.val + v.val - (i - 4) < 24 := by omega
        rw [decide_eq_true hge, Bool.true_and, bit_col0 ⟨6 * u.val + v.val - (i - 4), hk⟩]
        by_cases he : i - 4 = v.val
        · have hmod : (6 * u.val + v.val - (i - 4)) % 6 = 0 := by omega
          simp [hmod, Fin.ext_iff, he]
        · have hmod : (6 * u.val + v.val - (i - 4)) % 6 ≠ 0 := by omega
          simp [hmod, Fin.ext_iff, he]
      · have hne : i - 4 ≠ v.val := by omega
        rw [decide_eq_false hge, Bool.false_and]
        simp [Fin.ext_iff, hne]
    · have ha : inCols.length ≤ i := by simp [inCols]; omega
      have hb : (oneEach u v).length ≤ i := by simp [oneEach]; omega
      rw [List.getD_eq_default _ _ ha, List.getD_eq_default _ _ hb]
      exact Nat.zero_testBit _

theorem mono_ : Monotone2 C_ := by
  intro g hg
  have h1 := List.all_eq_true.1 (by decide : C_.gates.all isBinAO = true) g hg
  simp only [isBinAO, Bool.and_eq_true, beq_iff_eq] at h1
  refine ⟨?_, by omega⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem rep_ : Represents (fun (u : Fin 4) (v : Fin 6) => (274940 : ℕ).testBit (6 * u.val + v.val)) C_ := by
  intro u v
  have h := testBit_pcols (6 * u.val + v.val) C_.gates
    (List.all_eq_true.1 (by decide : C_.gates.all isBinAO = true))
    inCols (oneEach u v) (by simp [inCols, oneEach]) (inCols_ok u v) C_.output
  have heval : (pcols C_.gates inCols).getD C_.output 0 = 274940 := by decide +kernel
  rw [Circuit.eval, Circuit.wires, ← h, heval]

end PEqualNP.Outside.L_meta_23634_aux

theorem PEqualNP.Outside.L_meta_23634 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (274940 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_23634_aux.C_, PEqualNP.Outside.L_meta_23634_aux.mono_, by decide, PEqualNP.Outside.L_meta_23634_aux.rep_⟩
