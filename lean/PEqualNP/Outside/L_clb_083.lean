import Mathlib
import PEqualNP.Defs
import PEqualNP.CircuitLowerBounds.L008
import PEqualNP.Outside.L_lib_377

namespace PEqualNP.Outside.L_clb_083_aux

open PEqualNP.CircuitLowerBounds

def evalLit (y : List Bool) : Bool ⊕ (ℕ × Bool) → Bool
  | Sum.inl b => b
  | Sum.inr (idx, false) => y.getD idx false
  | Sum.inr (idx, true) => !(y.getD idx false)

def litGate : Bool ⊕ (ℕ × Bool) → Gate
  | Sum.inl false => ⟨GateOp.or, []⟩
  | Sum.inl true => ⟨GateOp.and, []⟩
  | Sum.inr (idx, false) => ⟨GateOp.or, [idx]⟩
  | Sum.inr (idx, true) => ⟨GateOp.not, [idx]⟩

def shiftGate (m : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (· + m)⟩

def substCircuit (m : ℕ) (lits : List (Bool ⊕ (ℕ × Bool))) (C : Circuit) (negOut : Bool) : Circuit :=
  let base := lits.map litGate ++ C.gates.map (shiftGate m)
  if negOut then
    ⟨base ++ [⟨GateOp.not, [m + C.output]⟩], m + lits.length + C.gates.length⟩
  else
    ⟨base, m + C.output⟩

theorem foldl_append_prefix (gs : List Gate) (y x : List Bool) :
    (gs.map (shiftGate y.length)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (y ++ x) =
    y ++ gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hmap : ((shiftGate y.length g).inputs.map fun i => (y ++ x).getD i false) =
        (g.inputs.map fun i => x.getD i false) := by
      simp only [shiftGate, List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      by_cases hi : i < x.length
      · rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
          List.getD_eq_getElem _ _ hi,
          List.getElem_append_right (by omega)]
        congr 1
        omega
      · have hge1 : (y ++ x).length ≤ i + y.length := by rw [List.length_append]; omega
        have hge2 : x.length ≤ i := by omega
        simp [List.getD, List.getElem?_eq_none hge1, List.getElem?_eq_none hge2]
    have hstep : (y ++ x) ++ [(shiftGate y.length g).op.eval
        ((shiftGate y.length g).inputs.map fun i => (y ++ x).getD i false)] =
        y ++ (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := by
      rw [hmap, List.append_assoc]
      rfl
    rw [hstep]
    exact ih _

theorem foldl_litGates (lits : List (Bool ⊕ (ℕ × Bool))) (y pre : List Bool)
    (hlits : ∀ s ∈ lits, ∀ idx neg, s = Sum.inr (idx, neg) → idx < y.length) :
    (lits.map litGate).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (y ++ pre) =
    y ++ (pre ++ lits.map (evalLit y)) := by
  induction lits generalizing pre with
  | nil => simp
  | cons s lits ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hval : (litGate s).op.eval ((litGate s).inputs.map fun i => (y ++ pre).getD i false) =
        evalLit y s := by
      rcases s with b | ⟨idx, neg⟩
      · cases b <;> rfl
      · have hidx : idx < y.length := hlits _ (List.mem_cons_self ..) idx neg rfl
        have hget : (y ++ pre).getD idx false = y.getD idx false := by
          rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
            List.getD_eq_getElem _ _ hidx, List.getElem_append_left hidx]
        cases neg
        · dsimp only [litGate, evalLit, GateOp.eval]
          simp only [List.map_cons, List.map_nil, hget, List.any_cons, List.any_nil, id_eq,
            Bool.or_false]
        · dsimp only [litGate, evalLit, GateOp.eval]
          simp only [List.map_cons, List.map_nil, hget, List.headD_cons]
    rw [hval, List.append_assoc]
    have ih' := ih (pre ++ [evalLit y s]) (fun s' hs' => hlits s' (List.mem_cons_of_mem _ hs'))
    simpa [List.append_assoc] using ih'

theorem wires_base (lits : List (Bool ⊕ (ℕ × Bool))) (C : Circuit) (y : List Bool)
    (hlits : ∀ s ∈ lits, ∀ idx neg, s = Sum.inr (idx, neg) → idx < y.length) :
    ((lits.map litGate ++ C.gates.map (shiftGate y.length)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y) =
    y ++ C.wires (lits.map (evalLit y)) := by
  rw [List.foldl_append]
  have h1 := foldl_litGates lits y [] hlits
  simp only [List.append_nil, List.nil_append] at h1
  rw [h1]
  exact foldl_append_prefix C.gates y (lits.map (evalLit y))

theorem eval_substCircuit (lits : List (Bool ⊕ (ℕ × Bool))) (C : Circuit) (negOut : Bool)
    (y : List Bool)
    (hlits : ∀ s ∈ lits, ∀ idx neg, s = Sum.inr (idx, neg) → idx < y.length) :
    (substCircuit y.length lits C negOut).eval y =
      if negOut then !(C.eval (lits.map (evalLit y))) else C.eval (lits.map (evalLit y)) := by
  have hbase := wires_base lits C y hlits
  have hwlen : (C.wires (lits.map (evalLit y))).length = lits.length + C.gates.length := by
    have hfold : ∀ (gs : List Gate) (x : List Bool),
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length =
          x.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro x; simp
      | cons g gs ih =>
        intro x
        simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
        omega
    simpa [Circuit.wires] using hfold C.gates (lits.map (evalLit y))
  have hget : (y ++ C.wires (lits.map (evalLit y))).getD (y.length + C.output) false =
      C.eval (lits.map (evalLit y)) := by
    unfold Circuit.eval
    by_cases ho : C.output < (C.wires (lits.map (evalLit y))).length
    · rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
        List.getD_eq_getElem _ _ ho,
        List.getElem_append_right (by omega)]
      congr 1
      omega
    · have h1 : (y ++ C.wires (lits.map (evalLit y))).length ≤ y.length + C.output := by
        rw [List.length_append]; omega
      have h2 : (C.wires (lits.map (evalLit y))).length ≤ C.output := by omega
      simp [List.getD, List.getElem?_eq_none h1, List.getElem?_eq_none h2]
  cases negOut
  · change ((lits.map litGate ++ C.gates.map (shiftGate y.length)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y).getD
        (y.length + C.output) false = C.eval (lits.map (evalLit y))
    rw [hbase, hget]
  · change (((lits.map litGate ++ C.gates.map (shiftGate y.length)) ++
        [(⟨GateOp.not, [y.length + C.output]⟩ : Gate)]).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) y).getD
        (y.length + lits.length + C.gates.length) false = !(C.eval (lits.map (evalLit y)))
    rw [List.foldl_append, hbase, List.foldl_cons, List.foldl_nil]
    have hlen : (y ++ C.wires (lits.map (evalLit y))).length =
        y.length + lits.length + C.gates.length := by
      rw [List.length_append, hwlen]; omega
    rw [List.getD_eq_getElem _ _ (by rw [List.length_append, List.length_singleton, hlen]; omega),
      List.getElem_append_right (by omega)]
    simp only [hlen, Nat.sub_self, List.getElem_singleton, GateOp.eval, List.map_cons,
      List.map_nil, List.headD_cons, hget]

theorem foldl_depths_length (gs : List Gate) (d : List ℕ) :
    (gs.foldl (fun acc g => acc ++ [(g.inputs.map fun i => acc.getD i 0).foldr max 0 + 1]) d).length =
      d.length + gs.length := by
  induction gs generalizing d with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

theorem foldl_depths_litGates (lits : List (Bool ⊕ (ℕ × Bool))) (m : ℕ) (pre : List ℕ)
    (hpre : ∀ x ∈ pre, x ≤ 1)
    (hlits : ∀ s ∈ lits, ∀ idx neg, s = Sum.inr (idx, neg) → idx < m) :
    ∃ suf : List ℕ, suf.length = lits.length ∧ (∀ x ∈ suf, x ≤ 1) ∧
      (lits.map litGate).foldl
        (fun d g => d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + 1])
        (List.replicate m 0 ++ pre) =
      List.replicate m 0 ++ (pre ++ suf) := by
  induction lits generalizing pre with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons s lits ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hval : ((litGate s).inputs.map fun i => (List.replicate m 0 ++ pre).getD i 0).foldr max 0 + 1 ≤ 1 := by
      rcases s with b | ⟨idx, neg⟩
      · cases b <;> simp [litGate]
      · have hidx : idx < m := hlits _ (List.mem_cons_self ..) idx neg rfl
        have hget : (List.replicate m 0 ++ pre).getD idx 0 = 0 := by
          rw [List.getD_eq_getElem _ _ (by rw [List.length_append, List.length_replicate]; omega),
            List.getElem_append_left (by rw [List.length_replicate]; exact hidx),
            List.getElem_replicate]
        cases neg <;> (dsimp only [litGate]; simp only [List.map_cons, List.map_nil, hget, List.foldr_cons, List.foldr_nil]; omega)
    let v := ((litGate s).inputs.map fun i => (List.replicate m 0 ++ pre).getD i 0).foldr max 0 + 1
    have hpre' : ∀ x ∈ pre ++ [v], x ≤ 1 := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hpre x hx
      · rw [List.mem_singleton.mp hx]; exact hval
    obtain ⟨suf, hlen, hsuf, heq⟩ :=
      ih (pre ++ [v]) hpre' (fun s' hs' => hlits s' (List.mem_cons_of_mem _ hs'))
    refine ⟨v :: suf, by simp [hlen], ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hval
      · exact hsuf x hx
    · rw [List.append_assoc]
      have hcons : pre ++ [v] ++ suf = pre ++ v :: suf := by simp [List.append_assoc]
      rw [← hcons]
      exact heq

theorem foldl_depths_shift (gs : List Gate) (m : ℕ) (d₁ d₂ : List ℕ)
    (hlen : d₁.length = d₂.length)
    (hle : ∀ i, d₁.getD i 0 ≤ d₂.getD i 0 + 1) :
    ∀ i,
      ((gs.map (shiftGate m)).foldl
        (fun d g => d ++ [(g.inputs.map fun j => d.getD j 0).foldr max 0 + 1])
        (List.replicate m 0 ++ d₁)).getD (m + i) 0 ≤
      (gs.foldl
        (fun d g => d ++ [(g.inputs.map fun j => d.getD j 0).foldr max 0 + 1])
        d₂).getD i 0 + 1 := by
  induction gs generalizing d₁ d₂ with
  | nil =>
    intro i
    simp only [List.map_nil, List.foldl_nil]
    by_cases hi : i < d₁.length
    · rw [List.getD_eq_getElem _ _ (by rw [List.length_append, List.length_replicate]; omega),
        List.getElem_append_right (by rw [List.length_replicate]; omega)]
      have hidx : m + i - (List.replicate m 0).length = i := by rw [List.length_replicate]; omega
      simp only [hidx]
      rw [← List.getD_eq_getElem _ 0 hi]
      exact hle i
    · have hge : (List.replicate m 0 ++ d₁).length ≤ m + i := by
        rw [List.length_append, List.length_replicate]; omega
      simp [List.getD, List.getElem?_eq_none hge]
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    let v1 := ((shiftGate m g).inputs.map fun j => (List.replicate m 0 ++ d₁).getD j 0).foldr max 0 + 1
    let v2 := (g.inputs.map fun j => d₂.getD j 0).foldr max 0 + 1
    have hv : v1 ≤ v2 + 1 := by
      have hfoldr : ∀ (ins : List ℕ),
          ((ins.map (· + m)).map fun j => (List.replicate m 0 ++ d₁).getD j 0).foldr max 0 ≤
          (ins.map fun j => d₂.getD j 0).foldr max 0 + 1 := by
        intro ins
        induction ins with
        | nil => simp
        | cons a ins ih_ins =>
          simp only [List.map_cons, List.foldr_cons]
          have ha : (List.replicate m 0 ++ d₁).getD (a + m) 0 ≤ d₂.getD a 0 + 1 := by
            by_cases ha' : a < d₁.length
            · rw [List.getD_eq_getElem _ _ (by rw [List.length_append, List.length_replicate]; omega),
                List.getElem_append_right (by rw [List.length_replicate]; omega)]
              have hidx : a + m - (List.replicate m 0).length = a := by rw [List.length_replicate]; omega
              simp only [hidx]
              rw [← List.getD_eq_getElem _ 0 ha']
              exact hle a
            · have hge : (List.replicate m 0 ++ d₁).length ≤ a + m := by
                rw [List.length_append, List.length_replicate]; omega
              simp [List.getD, List.getElem?_eq_none hge]
          omega
      have := hfoldr g.inputs
      dsimp only [v1, v2, shiftGate]
      omega
    have hlen' : (d₁ ++ [v1]).length = (d₂ ++ [v2]).length := by simp [hlen]
    have hle' : ∀ i, (d₁ ++ [v1]).getD i 0 ≤ (d₂ ++ [v2]).getD i 0 + 1 := by
      intro i
      by_cases hi : i < d₁.length
      · have h1 : (d₁ ++ [v1]).getD i 0 = d₁.getD i 0 := by
          rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
            List.getElem_append_left hi, ← List.getD_eq_getElem _ 0 hi]
        have hi2 : i < d₂.length := by omega
        have h2 : (d₂ ++ [v2]).getD i 0 = d₂.getD i 0 := by
          rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
            List.getElem_append_left hi2, ← List.getD_eq_getElem _ 0 hi2]
        rw [h1, h2]
        exact hle i
      · by_cases heq : i = d₁.length
        · subst heq
          have h1 : (d₁ ++ [v1]).getD d₁.length 0 = v1 := by
            rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
            simp
          have h2 : (d₂ ++ [v2]).getD d₁.length 0 = v2 := by
            rw [List.getD_eq_getElem _ _ (by simp [hlen]), List.getElem_append_right (by omega)]
            simp [hlen]
          rw [h1, h2]
          exact hv
        · have hge : (d₁ ++ [v1]).length ≤ i := by simp; omega
          simp [List.getD, List.getElem?_eq_none hge]
    rw [List.append_assoc]
    exact ih (d₁ ++ [v1]) (d₂ ++ [v2]) hlen' hle'

theorem depth_substCircuit (m : ℕ) (lits : List (Bool ⊕ (ℕ × Bool))) (C : Circuit) (negOut : Bool)
    (hlits : ∀ s ∈ lits, ∀ idx neg, s = Sum.inr (idx, neg) → idx < m) :
    (substCircuit m lits C negOut).depth m ≤ C.depth lits.length + 2 := by
  obtain ⟨suf, hsuflen, hsuf, hlit_eq⟩ := foldl_depths_litGates lits m [] (by simp) hlits
  simp only [List.append_nil, List.nil_append] at hlit_eq
  have hle_init : ∀ i, suf.getD i 0 ≤ (List.replicate lits.length 0).getD i 0 + 1 := by
    intro i
    by_cases hi : i < suf.length
    · rw [List.getD_eq_getElem _ _ hi]
      have hx : suf[i] ≤ 1 := hsuf _ (List.getElem_mem hi)
      omega
    · have hge : suf.length ≤ i := by omega
      simp [List.getD, List.getElem?_eq_none hge]
  have hshift := foldl_depths_shift C.gates m suf (List.replicate lits.length 0)
    (by simp [hsuflen]) hle_init C.output
  cases negOut
  · unfold substCircuit Circuit.depth Circuit.depths
    simp only [Bool.false_eq_true, ↓reduceIte, List.foldl_append]
    rw [hlit_eq]
    have h1 : ((C.gates.map (shiftGate m)).foldl
        (fun d g => d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + 1])
        (List.replicate m 0 ++ suf)).getD (m + C.output) 0 ≤ C.depth lits.length + 1 := hshift
    exact Nat.le_trans h1 (Nat.le_succ _)
  · unfold substCircuit Circuit.depth Circuit.depths
    simp only [↓reduceIte, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hlit_eq]
    let D := (C.gates.map (shiftGate m)).foldl
      (fun d g => d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + 1])
      (List.replicate m 0 ++ suf)
    have hDlen : D.length = m + lits.length + C.gates.length := by
      dsimp only [D]
      rw [foldl_depths_length, List.length_append, List.length_replicate, hsuflen, List.length_map]
    have hget : (D ++ [([m + C.output].map fun i => D.getD i 0).foldr max 0 + 1]).getD
        (m + lits.length + C.gates.length) 0 = D.getD (m + C.output) 0 + 1 := by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_append, List.length_singleton, hDlen]; omega),
        List.getElem_append_right (by omega)]
      simp [hDlen]
    change (D ++ [([m + C.output].map fun i => D.getD i 0).foldr max 0 + 1]).getD
        (m + lits.length + C.gates.length) 0 ≤ C.depth lits.length + 2
    rw [hget]
    exact Nat.add_le_add_right hshift 1

theorem substCircuit_gates_ok (p m : ℕ) (lits : List (Bool ⊕ (ℕ × Bool))) (C : Circuit)
    (negOut : Bool) (B : ℕ) (hB : 1 ≤ B)
    (hC : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not, GateOp.mod p} : Set GateOp) ∧
      g.inputs.length ≤ B) :
    ∀ g ∈ (substCircuit m lits C negOut).gates,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not, GateOp.mod p} : Set GateOp) ∧
      g.inputs.length ≤ B := by
  have hlit_ok : ∀ g ∈ lits.map litGate,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not, GateOp.mod p} : Set GateOp) ∧
      g.inputs.length ≤ B := by
    intro g hg
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hg
    rcases s with b | ⟨idx, neg⟩
    · cases b <;> simp [litGate]
    · cases neg <;> simp [litGate, hB]
  have hsh_ok : ∀ g ∈ C.gates.map (shiftGate m),
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not, GateOp.mod p} : Set GateOp) ∧
      g.inputs.length ≤ B := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    simpa [shiftGate] using hC g' hg'
  intro g hg
  cases negOut
  · simp only [substCircuit, Bool.false_eq_true, ↓reduceIte, List.mem_append] at hg
    rcases hg with hg | hg
    · exact hlit_ok g hg
    · exact hsh_ok g hg
  · simp only [substCircuit, ↓reduceIte, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · exact hlit_ok g hg
    · exact hsh_ok g hg
    · simp [hB]

theorem substCircuit_size (m : ℕ) (lits : List (Bool ⊕ (ℕ × Bool))) (C : Circuit) (negOut : Bool) :
    (substCircuit m lits C negOut).size ≤ lits.length + C.size + 1 := by
  cases negOut <;> simp [substCircuit, Circuit.size] <;> omega

def litsMod3 (m : ℕ) : List (Bool ⊕ (ℕ × Bool)) :=
  [Sum.inl true, Sum.inl false, Sum.inl false, Sum.inl true] ++
    (List.range m).flatMap (fun i =>
      [Sum.inr (i, true), Sum.inr (i, false), Sum.inr (i, false), Sum.inl true])

def litsMod2 (m : ℕ) : List (Bool ⊕ (ℕ × Bool)) :=
  [Sum.inl true, Sum.inl false, Sum.inl false, Sum.inl false] ++
    (List.range m).flatMap (fun i =>
      [Sum.inr (i, true), Sum.inr (i, false), Sum.inr (i, false), Sum.inr (i, true)])

theorem litsMod3_length (m : ℕ) : (litsMod3 m).length = 4 * (m + 1) := by
  unfold litsMod3
  rw [List.length_append, List.length_flatMap]
  simp
  omega

theorem litsMod2_length (m : ℕ) : (litsMod2 m).length = 4 * (m + 1) := by
  unfold litsMod2
  rw [List.length_append, List.length_flatMap]
  simp
  omega

theorem litsMod3_bounds (m : ℕ) :
    ∀ s ∈ litsMod3 m, ∀ idx neg, s = Sum.inr (idx, neg) → idx < m := by
  intro s hs idx neg heq
  subst heq
  simp only [litsMod3, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_range] at hs
  rcases hs with h | ⟨i, hi, h⟩
  · rcases h with h | h | h | h <;> cases h
  · rcases h with h | h | h | h <;> cases h <;> exact hi

theorem litsMod2_bounds (m : ℕ) :
    ∀ s ∈ litsMod2 m, ∀ idx neg, s = Sum.inr (idx, neg) → idx < m := by
  intro s hs idx neg heq
  subst heq
  simp only [litsMod2, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_range] at hs
  rcases hs with h | ⟨i, hi, h⟩
  · rcases h with h | h | h | h <;> cases h
  · rcases h with h | h | h | h <;> cases h <;> exact hi

def blockMod3 (b : Bool) : List Bool :=
  [!b, b, b, true]

def blockMod2 (b : Bool) : List Bool :=
  [!b, b, b, !b]

def encMod3 (y : List Bool) : List Bool :=
  [true, false, false, true] ++ y.flatMap blockMod3

def encMod2 (y : List Bool) : List Bool :=
  [true, false, false, false] ++ y.flatMap blockMod2

theorem range_flatMap_getD (f : Bool → List Bool) (y : List Bool) :
    (List.range y.length).flatMap (fun i => f (y.getD i false)) = y.flatMap f := by
  induction y using List.reverseRecOn with
  | nil => simp
  | append_singleton y b ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.flatMap_append,
      List.flatMap_singleton, List.flatMap_append, List.flatMap_singleton]
    have hlast : (y ++ [b]).getD y.length false = b := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
      simp
    rw [hlast]
    congr 1
    rw [← ih]
    apply List.flatMap_congr
    intro i hi
    have hlt : i < y.length := List.mem_range.mp hi
    have hget : (y ++ [b]).getD i false = y.getD i false := by
      rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega),
        List.getElem_append_left hlt, ← List.getD_eq_getElem _ false hlt]
    rw [hget]

theorem map_litsMod3 (y : List Bool) :
    (litsMod3 y.length).map (evalLit y) = encMod3 y := by
  unfold litsMod3 encMod3
  rw [List.map_append, List.map_flatMap]
  congr 1
  exact range_flatMap_getD blockMod3 y

theorem map_litsMod2 (y : List Bool) :
    (litsMod2 y.length).map (evalLit y) = encMod2 y := by
  unfold litsMod2 encMod2
  rw [List.map_append, List.map_flatMap]
  congr 1
  exact range_flatMap_getD blockMod2 y

abbrev M2 := Matrix (Fin 1 → Bool) (Fin 1 → Bool) (ZMod 2)

def matOfBlock (blk : List Bool) : M2 :=
  Matrix.of fun p q =>
    if blk.getD ((if p 0 then 1 else 0) + (if q 0 then 2 else 0)) false = true then 1 else 0

def matI : M2 := matOfBlock [true, false, false, true]
def matF : M2 := matOfBlock [false, true, true, true]
def matP : M2 := matOfBlock [true, false, false, false]
def matS : M2 := matOfBlock [false, true, true, false]

theorem matI_eq_one : matI = 1 := by
  ext p q
  have hp : p = fun _ => p 0 := funext fun j => by fin_cases j; rfl
  have hq : q = fun _ => q 0 := funext fun j => by fin_cases j; rfl
  rw [hp, hq]
  cases p 0 <;> cases q 0 <;> decide

theorem matF_pow_three : matF ^ 3 = 1 := by
  rw [← matI_eq_one]
  ext p q
  have hp : p = fun _ => p 0 := funext fun j => by fin_cases j; rfl
  have hq : q = fun _ => q 0 := funext fun j => by fin_cases j; rfl
  rw [hp, hq]
  cases p 0 <;> cases q 0 <;> decide

theorem matS_pow_two : matS ^ 2 = 1 := by
  rw [← matI_eq_one]
  ext p q
  have hp : p = fun _ => p 0 := funext fun j => by fin_cases j; rfl
  have hq : q = fun _ => q 0 := funext fun j => by fin_cases j; rfl
  rw [hp, hq]
  cases p 0 <;> cases q 0 <;> decide

theorem trace_matF_pow (c : ℕ) :
    Matrix.trace (matF ^ c) = if c % 3 = 0 then 0 else 1 := by
  have hdiv : c = 3 * (c / 3) + c % 3 := (Nat.div_add_mod c 3).symm
  conv_lhs => rw [hdiv, pow_add, pow_mul, matF_pow_three, one_pow, one_mul]
  have hlt : c % 3 < 3 := Nat.mod_lt c (by omega)
  have hcases : c % 3 = 0 ∨ c % 3 = 1 ∨ c % 3 = 2 := by omega
  rcases hcases with h | h | h <;> rw [h] <;> decide

theorem trace_matP_matS_pow (c : ℕ) :
    Matrix.trace (matP * matS ^ c) = if c % 2 = 0 then 1 else 0 := by
  have hdiv : c = 2 * (c / 2) + c % 2 := (Nat.div_add_mod c 2).symm
  conv_lhs => rw [hdiv, pow_add, pow_mul, matS_pow_two, one_pow, one_mul]
  have hlt : c % 2 < 2 := Nat.mod_lt c (by omega)
  have hcases : c % 2 = 0 ∨ c % 2 = 1 := by omega
  rcases hcases with h | h <;> rw [h] <;> decide

theorem flatten_length_four : ∀ (l : List (List Bool)),
    (∀ b ∈ l, b.length = 4) → l.flatten.length = 4 * l.length
  | [], _ => by simp
  | c :: l', hl => by
    rw [List.flatten_cons, List.length_append, hl c (List.mem_cons_self ..),
      flatten_length_four l' (fun x hx => hl x (List.mem_cons_of_mem _ hx)), List.length_cons]
    omega

theorem getD_blocks (hd : List Bool) (bs : List (List Bool)) (hhd : hd.length = 4)
    (hbs : ∀ b ∈ bs, b.length = 4) (i : Fin (bs.length + 1)) (off : ℕ) (hoff : off < 4) :
    (hd ++ bs.flatten).getD (4 * i.val + off) false =
      (if h : i.val = 0 then hd else bs.getD (i.val - 1) []).getD off false := by
  cases hi : i.val with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, ↓reduceDIte]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hhd]; omega),
      List.getD_eq_getElem _ _ (by omega), List.getElem_append_left (by omega)]
  | succ k =>
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte, Nat.add_sub_cancel]
    have hk : k < bs.length := by omega
    have hflat : ∀ (l : List (List Bool)) (idx : ℕ), (∀ b ∈ l, b.length = 4) → idx < l.length →
        l.flatten.getD (4 * idx + off) false = (l.getD idx []).getD off false := by
      intro l
      induction l with
      | nil => intro _ _ h; simp at h
      | cons b l ih =>
        intro idx hl hidx
        have hb4 : b.length = 4 := hl b (List.mem_cons_self ..)
        cases idx with
        | zero =>
          simp only [Nat.mul_zero, Nat.zero_add, List.flatten_cons, List.getD_cons_zero]
          rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hb4]; omega),
            List.getD_eq_getElem _ _ (by omega), List.getElem_append_left (by omega)]
        | succ idx' =>
          simp only [List.flatten_cons, List.getD_cons_succ]
          have hlen_fl := flatten_length_four l (fun x hx => hl x (List.mem_cons_of_mem _ hx))
          rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hb4, hlen_fl]; simp at hidx; omega),
            List.getElem_append_right (by omega)]
          have hsub : 4 * (idx' + 1) + off - b.length = 4 * idx' + off := by omega
          simp only [hsub]
          rw [← List.getD_eq_getElem _ false (by rw [hlen_fl]; simp at hidx; omega)]
          exact ih idx' (fun x hx => hl x (List.mem_cons_of_mem _ hx)) (by simp at hidx; omega)
    have hlen_fl := flatten_length_four bs hbs
    rw [List.getD_eq_getElem _ _ (by rw [List.length_append, hhd, hlen_fl]; omega),
      List.getElem_append_right (by omega)]
    have hsub : 4 * (k + 1) + off - hd.length = 4 * k + off := by omega
    simp only [hsub]
    rw [← List.getD_eq_getElem _ false (by rw [hlen_fl]; omega)]
    exact hflat bs k hbs hk

theorem trace_nat_to_zmod2 (t : ℕ) (x : List Bool) :
    let n := t + 1
    let test : Fin n → (Fin 1 → Bool) → Bool → Bool := fun i p b =>
      x.getD (4 * i.val + (if p 0 then 1 else 0) + (if b then 2 else 0)) false
    let stepZ : Fin n → M2 := fun i =>
      Matrix.of fun p q => if test i p (q 0) = true then 1 else 0
    (((Finset.univ : Finset (Fin n → Bool)).filter (fun w =>
      ∀ i : Fin n, x.getD
        (4 * i.val + (if w i then 1 else 0) +
          (if w (Fin.ofNat (t + 1) (i.val + 1)) then 2 else 0)) false = true)).card : ZMod 2) =
    Matrix.trace (List.ofFn stepZ).prod := by
  intro n test stepZ
  have hlib := PEqualNP.Outside.L_lib_377 t 1 test
  dsimp only at hlib
  have hacc : (Finset.univ.filter fun w : Fin n → Bool =>
      ∀ a : Fin n,
        test a (fun pos : Fin 1 => w (Fin.ofNat (t + 1) (a.val + pos.val)))
          (w (Fin.ofNat (t + 1) (a.val + 1))) = true) =
      (Finset.univ.filter fun w : Fin n → Bool =>
        ∀ i : Fin n, x.getD
          (4 * i.val + (if w i then 1 else 0) +
            (if w (Fin.ofNat (t + 1) (i.val + 1)) then 2 else 0)) false = true) := by
    congr 1
    funext w
    apply propext
    apply forall_congr'
    intro i
    dsimp only [test]
    have h0 : Fin.ofNat (t + 1) (i.val + (0 : Fin 1).val) = i := by
      ext
      show (i.val + 0) % (t + 1) = i.val
      rw [Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
    simp only [h0]
  rw [← hacc, ← hlib]
  let f := RingHom.mapMatrix (Nat.castRingHom (ZMod 2)) (m := Fin 1 → Bool)
  have hcast : ∀ M : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℕ,
      ((Matrix.trace M : ℕ) : ZMod 2) = Matrix.trace (f M) := by
    intro M
    simp [Matrix.trace, Matrix.diag, f]
  rw [hcast, map_list_prod]
  congr 2
  rw [List.map_ofFn]
  congr 1
  funext i
  ext p q
  simp only [Function.comp_apply, f, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    stepZ, map_natCast]
  have hnext : ∀ bit : Bool, ((fun j : Fin 1 =>
      if h : j.val + 1 < 1 then p ⟨j.val + 1, h⟩ else bit) = q) ↔ bit = q 0 := by
    intro bit
    constructor
    · intro h
      have := congrFun h 0
      simpa using this
    · intro h
      funext j
      fin_cases j
      simpa using h
  have hcard : (Finset.univ.filter fun bit : Bool =>
      test i p bit = true ∧
        (fun j : Fin 1 => if h : j.val + 1 < 1 then p ⟨j.val + 1, h⟩ else bit) = q).card =
      if test i p (q 0) = true then 1 else 0 := by
    have hf : (Finset.univ.filter fun bit : Bool =>
        test i p bit = true ∧
          (fun j : Fin 1 => if h : j.val + 1 < 1 then p ⟨j.val + 1, h⟩ else bit) = q) =
        (Finset.univ.filter fun bit : Bool => test i p bit = true ∧ bit = q 0) := by
      ext bit
      rw [Finset.mem_filter, Finset.mem_filter]
      exact and_congr_right fun _ => and_congr_right fun _ => hnext bit
    rw [hf]
    by_cases ht : test i p (q 0) = true
    · have hs : (Finset.univ.filter fun bit : Bool => test i p bit = true ∧ bit = q 0) = {q 0} := by
        ext bit
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨_, rfl⟩; rfl
        · rintro rfl; exact ⟨ht, rfl⟩
      rw [hs, Finset.card_singleton, if_pos ht]
    · have hs : (Finset.univ.filter fun bit : Bool => test i p bit = true ∧ bit = q 0) = ∅ := by
        ext bit
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨h1, rfl⟩
        exact ht h1
      rw [hs, Finset.card_empty, if_neg ht]
  rw [hcard]
  split_ifs <;> simp

theorem prod_mat_mod3 (y : List Bool) :
    (List.ofFn fun i : Fin (y.length + 1) =>
      matOfBlock (if i.val = 0 then [true, false, false, true]
        else blockMod3 (y.getD (i.val - 1) false))).prod =
    matF ^ (y.count true) := by
  rw [List.ofFn_succ, List.prod_cons]
  have h0 : matOfBlock (if (0 : Fin (y.length + 1)).val = 0 then [true, false, false, true]
      else blockMod3 (y.getD ((0 : Fin (y.length + 1)).val - 1) false)) = 1 := by
    simpa [matI] using matI_eq_one
  rw [h0, one_mul]
  have h1 : (List.ofFn fun i : Fin y.length =>
      matOfBlock (if i.succ.val = 0 then [true, false, false, true]
        else blockMod3 (y.getD (i.succ.val - 1) false))) =
      y.map (fun b => if b then matF else 1) := by
    apply List.ext_getElem
    · simp
    · intro k hk _
      simp only [List.getElem_ofFn, List.getElem_map, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero,
        and_false, ↓reduceIte, Nat.add_sub_cancel]
      have hk' : k < y.length := by simpa using hk
      have hget : y.getD k false = y[k]'hk' := List.getD_eq_getElem _ _ hk'
      rw [hget]
      cases y[k]'hk'
      · simpa [blockMod3, matI] using matI_eq_one
      · rfl
  rw [h1]
  clear h0 h1
  induction y with
  | nil => simp
  | cons b y ih =>
    cases b
    · simp [ih]
    · simp [ih, pow_succ']

theorem prod_mat_mod2 (y : List Bool) :
    (List.ofFn fun i : Fin (y.length + 1) =>
      matOfBlock (if i.val = 0 then [true, false, false, false]
        else blockMod2 (y.getD (i.val - 1) false))).prod =
    matP * matS ^ (y.count true) := by
  rw [List.ofFn_succ, List.prod_cons]
  congr 1
  have h1 : (List.ofFn fun i : Fin y.length =>
      matOfBlock (if i.succ.val = 0 then [true, false, false, false]
        else blockMod2 (y.getD (i.succ.val - 1) false))) =
      y.map (fun b => if b then matS else 1) := by
    apply List.ext_getElem
    · simp
    · intro k hk _
      simp only [List.getElem_ofFn, List.getElem_map, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero,
        and_false, ↓reduceIte, Nat.add_sub_cancel]
      have hk' : k < y.length := by simpa using hk
      have hget : y.getD k false = y[k]'hk' := List.getD_eq_getElem _ _ hk'
      rw [hget]
      cases y[k]'hk'
      · simpa [blockMod2, matI] using matI_eq_one
      · rfl
  rw [h1]
  clear h1
  induction y with
  | nil => simp
  | cons b y ih =>
    cases b
    · simp [ih]
    · simp [ih, pow_succ']

theorem encMod3_length (y : List Bool) : (encMod3 y).length = 4 * (y.length + 1) := by
  rw [← map_litsMod3, List.length_map, litsMod3_length]

theorem encMod2_length (y : List Bool) : (encMod2 y).length = 4 * (y.length + 1) := by
  rw [← map_litsMod2, List.length_map, litsMod2_length]

theorem natCast_zmod2_eq_one (k : ℕ) : (k : ZMod 2) = 1 ↔ k % 2 = 1 := by
  have h1 : (1 : ZMod 2) = ((1 : ℕ) : ZMod 2) := rfl
  rw [h1, ZMod.natCast_eq_natCast_iff]
  show k % 2 = 1 % 2 ↔ k % 2 = 1
  rfl

theorem encMod3_card_mod2 (y : List Bool) :
    ((Finset.univ : Finset (Fin (y.length + 1) → Bool)).filter (fun w =>
      ∀ i : Fin (y.length + 1), (encMod3 y).getD
        (4 * i.val + (if w i then 1 else 0) +
          (if w (Fin.ofNat (y.length + 1) (i.val + 1)) then 2 else 0)) false = true)).card % 2 = 1 ↔
    y.count true % 3 ≠ 0 := by
  have htz := trace_nat_to_zmod2 y.length (encMod3 y)
  dsimp only at htz
  have hstep : (List.ofFn fun i : Fin (y.length + 1) =>
      (Matrix.of fun p q : Fin 1 → Bool =>
        if (encMod3 y).getD (4 * i.val + (if p 0 then 1 else 0) + (if q 0 then 2 else 0)) false = true
        then (1 : ZMod 2) else 0)) =
      (List.ofFn fun i : Fin (y.length + 1) =>
        matOfBlock (if i.val = 0 then [true, false, false, true]
          else blockMod3 (y.getD (i.val - 1) false))) := by
    congr 1
    funext i
    ext p q
    simp only [Matrix.of_apply, matOfBlock]
    have hoff : (if p 0 then 1 else 0) + (if q 0 then 2 else 0) < 4 := by
      cases p 0 <;> cases q 0 <;> simp
    have hgb := getD_blocks [true, false, false, true] (y.map blockMod3) rfl
      (fun b hb => by obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb; rfl)
      ⟨i.val, by rw [List.length_map]; exact i.isLt⟩
      ((if p 0 then 1 else 0) + (if q 0 then 2 else 0)) hoff
    have henc : encMod3 y = [true, false, false, true] ++ (y.map blockMod3).flatten := by
      simp [encMod3, List.flatMap]
    rw [henc, Nat.add_assoc]
    have hgb' : ([true, false, false, true] ++ (y.map blockMod3).flatten).getD
        (4 * i.val + ((if p 0 then 1 else 0) + (if q 0 then 2 else 0))) false =
        (if i.val = 0 then [true, false, false, true] else blockMod3 (y.getD (i.val - 1) false)).getD
          ((if p 0 then 1 else 0) + (if q 0 then 2 else 0)) false := by
      rw [hgb]
      by_cases h0 : i.val = 0
      · simp [h0]
      · simp only [h0, ↓reduceDIte, ↓reduceIte]
        have hlt : i.val - 1 < y.length := by omega
        have hget : (y.map blockMod3).getD (i.val - 1) [] = blockMod3 (y.getD (i.val - 1) false) := by
          rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlt), List.getElem_map,
            List.getD_eq_getElem _ _ hlt]
        rw [hget]
    rw [hgb']
  rw [hstep, prod_mat_mod3, trace_matF_pow] at htz
  by_cases h3 : y.count true % 3 = 0
  · simp only [h3, ↓reduceIte, ne_eq, not_true_eq_false, iff_false] at htz ⊢
    intro h1
    have := (natCast_zmod2_eq_one _).mpr h1
    rw [htz] at this
    exact zero_ne_one this
  · simp only [h3, ↓reduceIte, ne_eq, not_false_eq_true, iff_true] at htz ⊢
    exact (natCast_zmod2_eq_one _).mp htz

theorem encMod2_card_mod2 (y : List Bool) :
    ((Finset.univ : Finset (Fin (y.length + 1) → Bool)).filter (fun w =>
      ∀ i : Fin (y.length + 1), (encMod2 y).getD
        (4 * i.val + (if w i then 1 else 0) +
          (if w (Fin.ofNat (y.length + 1) (i.val + 1)) then 2 else 0)) false = true)).card % 2 = 1 ↔
    y.count true % 2 = 0 := by
  have htz := trace_nat_to_zmod2 y.length (encMod2 y)
  dsimp only at htz
  have hstep : (List.ofFn fun i : Fin (y.length + 1) =>
      (Matrix.of fun p q : Fin 1 → Bool =>
        if (encMod2 y).getD (4 * i.val + (if p 0 then 1 else 0) + (if q 0 then 2 else 0)) false = true
        then (1 : ZMod 2) else 0)) =
      (List.ofFn fun i : Fin (y.length + 1) =>
        matOfBlock (if i.val = 0 then [true, false, false, false]
          else blockMod2 (y.getD (i.val - 1) false))) := by
    congr 1
    funext i
    ext p q
    simp only [Matrix.of_apply, matOfBlock]
    have hoff : (if p 0 then 1 else 0) + (if q 0 then 2 else 0) < 4 := by
      cases p 0 <;> cases q 0 <;> simp
    have hgb := getD_blocks [true, false, false, false] (y.map blockMod2) rfl
      (fun b hb => by obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb; rfl)
      ⟨i.val, by rw [List.length_map]; exact i.isLt⟩
      ((if p 0 then 1 else 0) + (if q 0 then 2 else 0)) hoff
    have henc : encMod2 y = [true, false, false, false] ++ (y.map blockMod2).flatten := by
      simp [encMod2, List.flatMap]
    rw [henc, Nat.add_assoc]
    have hgb' : ([true, false, false, false] ++ (y.map blockMod2).flatten).getD
        (4 * i.val + ((if p 0 then 1 else 0) + (if q 0 then 2 else 0))) false =
        (if i.val = 0 then [true, false, false, false] else blockMod2 (y.getD (i.val - 1) false)).getD
          ((if p 0 then 1 else 0) + (if q 0 then 2 else 0)) false := by
      rw [hgb]
      by_cases h0 : i.val = 0
      · simp [h0]
      · simp only [h0, ↓reduceDIte, ↓reduceIte]
        have hlt : i.val - 1 < y.length := by omega
        have hget : (y.map blockMod2).getD (i.val - 1) [] = blockMod2 (y.getD (i.val - 1) false) := by
          rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hlt), List.getElem_map,
            List.getD_eq_getElem _ _ hlt]
        rw [hget]
    rw [hgb']
  rw [hstep, prod_mat_mod2, trace_matP_matS_pow] at htz
  by_cases h2 : y.count true % 2 = 0
  · simp only [h2, ↓reduceIte, iff_true] at htz ⊢
    exact (natCast_zmod2_eq_one _).mp htz
  · simp only [h2, ↓reduceIte, iff_false] at htz ⊢
    intro h1
    have := (natCast_zmod2_eq_one _).mpr h1
    rw [htz] at this
    exact zero_ne_one this

end PEqualNP.Outside.L_clb_083_aux

theorem PEqualNP.Outside.L_clb_083 : (let L : Language Bool := {x : List Bool | ∃ t : ℕ,
  let n := t + 1
  x.length = 4 * n ∧
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun w =>
      ∀ i : Fin n, x.getD
        (4 * i.val + (if w i then 1 else 0) +
          (if w (Fin.ofNat (t + 1) (i.val + 1)) then 2 else 0)) false = true)).card % 2 = 1}
∀ p : ℕ, Nat.Prime p → L ∉ PEqualNP.CircuitLowerBounds.AC0Mod p) := by
  intro L p hp hL
  obtain ⟨poly, d, hSD⟩ := hL
  let Q : Polynomial ℕ :=
    Polynomial.C 4 * (Polynomial.X + 1) +
      poly.comp (Polynomial.C 4 * (Polynomial.X + 1)) + Polynomial.C 2
  have hQ : ∀ m : ℕ, Q.eval m = 4 * (m + 1) + poly.eval (4 * (m + 1)) + 2 := by
    intro m
    simp [Q, Polynomial.eval_comp]
  by_cases hp2 : p = 2
  · subst hp2
    apply PEqualNP.CircuitLowerBounds.L008 2 3 Nat.prime_two Nat.prime_three (by decide)
    refine ⟨Q, d + 2, fun m => ?_⟩
    obtain ⟨C, hCg, hCs, hCd, hCdec⟩ := hSD (4 * (m + 1))
    dsimp only at hCg hCs
    let lits := PEqualNP.Outside.L_clb_083_aux.litsMod3 m
    have hlits_len : lits.length = 4 * (m + 1) := PEqualNP.Outside.L_clb_083_aux.litsMod3_length m
    have hlits_b := PEqualNP.Outside.L_clb_083_aux.litsMod3_bounds m
    refine ⟨PEqualNP.Outside.L_clb_083_aux.substCircuit m lits C true, ?_, ?_, ?_, ?_⟩
    · refine PEqualNP.Outside.L_clb_083_aux.substCircuit_gates_ok 2 m lits C true (Q.eval m)
        (by rw [hQ]; omega) (fun g hg => ?_)
      have hg' := hCg g hg
      exact ⟨hg'.1, hg'.2.trans (by rw [hQ]; omega)⟩
    · dsimp only
      have hsz := PEqualNP.Outside.L_clb_083_aux.substCircuit_size m lits C true
      rw [hlits_len] at hsz
      rw [hQ]
      omega
    · have hdp := PEqualNP.Outside.L_clb_083_aux.depth_substCircuit m lits C true hlits_b
      rw [hlits_len] at hdp
      omega
    · intro y hy
      have hev := PEqualNP.Outside.L_clb_083_aux.eval_substCircuit
        (PEqualNP.Outside.L_clb_083_aux.litsMod3 y.length) C true y
        (PEqualNP.Outside.L_clb_083_aux.litsMod3_bounds y.length)
      rw [PEqualNP.Outside.L_clb_083_aux.map_litsMod3] at hev
      have hdec := hCdec (PEqualNP.Outside.L_clb_083_aux.encMod3 y)
        (by rw [PEqualNP.Outside.L_clb_083_aux.encMod3_length, hy])
      have hmem : PEqualNP.Outside.L_clb_083_aux.encMod3 y ∈ L ↔ y.count true % 3 ≠ 0 := by
        constructor
        · rintro ⟨t, hlen, hcard⟩
          have ht : t = y.length := by
            rw [PEqualNP.Outside.L_clb_083_aux.encMod3_length] at hlen
            omega
          subst ht
          exact (PEqualNP.Outside.L_clb_083_aux.encMod3_card_mod2 y).mp hcard
        · intro hne
          exact ⟨y.length, PEqualNP.Outside.L_clb_083_aux.encMod3_length y,
            (PEqualNP.Outside.L_clb_083_aux.encMod3_card_mod2 y).mpr hne⟩
      have hne_iff : ((!C.eval (PEqualNP.Outside.L_clb_083_aux.encMod3 y)) = true) ↔
          ¬(C.eval (PEqualNP.Outside.L_clb_083_aux.encMod3 y) = true) := by
        cases C.eval (PEqualNP.Outside.L_clb_083_aux.encMod3 y) <;> simp
      change (PEqualNP.Outside.L_clb_083_aux.substCircuit m
        (PEqualNP.Outside.L_clb_083_aux.litsMod3 m) C true).eval y = true ↔
        y.count true % 3 = 0
      rw [← hy, hev, if_pos rfl, hne_iff, hdec, hmem]
      tauto
  · apply PEqualNP.CircuitLowerBounds.L008 p 2 hp Nat.prime_two hp2
    refine ⟨Q, d + 2, fun m => ?_⟩
    obtain ⟨C, hCg, hCs, hCd, hCdec⟩ := hSD (4 * (m + 1))
    dsimp only at hCg hCs
    let lits := PEqualNP.Outside.L_clb_083_aux.litsMod2 m
    have hlits_len : lits.length = 4 * (m + 1) := PEqualNP.Outside.L_clb_083_aux.litsMod2_length m
    have hlits_b := PEqualNP.Outside.L_clb_083_aux.litsMod2_bounds m
    refine ⟨PEqualNP.Outside.L_clb_083_aux.substCircuit m lits C false, ?_, ?_, ?_, ?_⟩
    · refine PEqualNP.Outside.L_clb_083_aux.substCircuit_gates_ok p m lits C false (Q.eval m)
        (by rw [hQ]; omega) (fun g hg => ?_)
      have hg' := hCg g hg
      exact ⟨hg'.1, hg'.2.trans (by rw [hQ]; omega)⟩
    · dsimp only
      have hsz := PEqualNP.Outside.L_clb_083_aux.substCircuit_size m lits C false
      rw [hlits_len] at hsz
      rw [hQ]
      omega
    · have hdp := PEqualNP.Outside.L_clb_083_aux.depth_substCircuit m lits C false hlits_b
      rw [hlits_len] at hdp
      omega
    · intro y hy
      have hev := PEqualNP.Outside.L_clb_083_aux.eval_substCircuit
        (PEqualNP.Outside.L_clb_083_aux.litsMod2 y.length) C false y
        (PEqualNP.Outside.L_clb_083_aux.litsMod2_bounds y.length)
      rw [PEqualNP.Outside.L_clb_083_aux.map_litsMod2] at hev
      have hdec := hCdec (PEqualNP.Outside.L_clb_083_aux.encMod2 y)
        (by rw [PEqualNP.Outside.L_clb_083_aux.encMod2_length, hy])
      have hmem : PEqualNP.Outside.L_clb_083_aux.encMod2 y ∈ L ↔ y.count true % 2 = 0 := by
        constructor
        · rintro ⟨t, hlen, hcard⟩
          have ht : t = y.length := by
            rw [PEqualNP.Outside.L_clb_083_aux.encMod2_length] at hlen
            omega
          subst ht
          exact (PEqualNP.Outside.L_clb_083_aux.encMod2_card_mod2 y).mp hcard
        · intro heq
          exact ⟨y.length, PEqualNP.Outside.L_clb_083_aux.encMod2_length y,
            (PEqualNP.Outside.L_clb_083_aux.encMod2_card_mod2 y).mpr heq⟩
      change (PEqualNP.Outside.L_clb_083_aux.substCircuit m
        (PEqualNP.Outside.L_clb_083_aux.litsMod2 m) C false).eval y = true ↔
        y.count true % 2 = 0
      rw [← hy, hev, if_neg Bool.false_ne_true, hdec, hmem]
