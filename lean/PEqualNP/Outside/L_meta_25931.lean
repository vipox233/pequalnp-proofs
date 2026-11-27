import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25931

abbrev PMGate := PEqualNP.CircuitLowerBounds.Gate
abbrev PMOp := PEqualNP.CircuitLowerBounds.GateOp
abbrev PMCircuit := PEqualNP.CircuitLowerBounds.Circuit

def pmPerm (swapRows swapCols : Bool) (i : Fin 9) : Fin 9 :=
  (if swapRows then
    if swapCols then [1, 0, 2, 7, 6, 8, 4, 3, 5] else [0, 1, 2, 6, 7, 8, 3, 4, 5]
  else
    if swapCols then [1, 0, 2, 4, 3, 5, 7, 6, 8] else [0, 1, 2, 3, 4, 5, 6, 7, 8]
  : List (Fin 9)).getD i.val 0

lemma pmPermTwice (r c : Bool) (i : Fin 9) :
    pmPerm r c (pmPerm r c i) = i := by
  revert r c i
  decide

def pmWire (r c : Bool) (i : ℕ) : ℕ :=
  if h : i < 9 then (pmPerm r c ⟨i, h⟩).val else i

lemma pmWireInput (r c : Bool) {i : ℕ} (hi : i < 9) :
    pmWire r c i = (pmPerm r c ⟨i, hi⟩).val := by
  simp [pmWire, hi]

lemma pmWireInternal (r c : Bool) {i : ℕ} (hi : 9 ≤ i) :
    pmWire r c i = i := by
  simp [pmWire, show ¬ i < 9 by omega]

lemma pmWireTwice (r c : Bool) (i : ℕ) :
    pmWire r c (pmWire r c i) = i := by
  by_cases hi : i < 9
  · have hval := pmWireInput r c hi
    have hlt : pmWire r c i < 9 := hval ▸ (pmPerm r c ⟨i, hi⟩).isLt
    have hfin : (⟨pmWire r c i, hlt⟩ : Fin 9) = pmPerm r c ⟨i, hi⟩ := Fin.ext hval
    rw [pmWireInput r c hlt, hfin, pmPermTwice]
  · rw [pmWireInternal r c (show 9 ≤ i by omega), pmWireInternal r c (show 9 ≤ i by omega)]

lemma pmWireEarlier (r c : Bool) {i j : ℕ} (hi : i < 9 + j) :
    pmWire r c i < 9 + j := by
  by_cases h : i < 9
  · rw [pmWireInput r c h]
    exact lt_of_lt_of_le (pmPerm r c ⟨i, h⟩).isLt (Nat.le_add_right 9 j)
  · rwa [pmWireInternal r c (show 9 ≤ i by omega)]


lemma pmWireBelow (r c : Bool) {i n : ℕ} (hn : 9 ≤ n) (hi : i < n) :
    pmWire r c i < n := by
  by_cases h : i < 9
  · rw [pmWireInput r c h]
    exact lt_of_lt_of_le (pmPerm r c ⟨i, h⟩).isLt hn
  · rwa [pmWireInternal r c (show 9 ≤ i by omega)]

def pmStep (w : List Bool) (g : PMGate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

def pmRawRename (r c : Bool) (g : PMGate) : PMGate :=
  ⟨g.op, g.inputs.map (pmWire r c)⟩

lemma pmGetLast (w : List Bool) (x : Bool) :
    (w ++ [x]).getD w.length false = x := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  simp

lemma pmFoldPrefix (gs : List PMGate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl pmStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [pmStep]; omega)]
    unfold pmStep
    rw [List.getD_append _ _ _ _ hi]

def pmRel (r c : Bool) (w v : List Bool) : Prop :=
  9 ≤ w.length ∧ v.length = w.length ∧
    ∀ i, v.getD (pmWire r c i) false = w.getD i false

lemma pmRelStep (r c : Bool) (w v : List Bool) (g : PMGate) (h : pmRel r c w v) :
    pmRel r c (pmStep w g) (pmStep v (pmRawRename r c g)) := by
  obtain ⟨hl, he, hm⟩ := h
  have hv : (pmRawRename r c g).op.eval
      ((pmRawRename r c g).inputs.map (fun i => v.getD i false)) =
      g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
    simp only [pmRawRename, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hm i
  refine ⟨by simp [pmStep]; omega, by simp [pmStep, he], ?_⟩
  intro i
  simp only [pmStep, hv]
  rcases Nat.lt_trichotomy i w.length with hi | hi | hi
  · have hj : pmWire r c i < v.length := by rw [he]; exact pmWireBelow r c hl hi
    rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ hi]
    exact hm i
  · have hj : pmWire r c i = v.length := by
      rw [pmWireInternal r c (show 9 ≤ i by omega)]
      omega
    rw [hj, hi, pmGetLast, pmGetLast]
  · rw [pmWireInternal r c (show 9 ≤ i by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma pmRelFold (r c : Bool) (gs : List PMGate) (w v : List Bool) (h : pmRel r c w v) :
    pmRel r c (gs.foldl pmStep w) ((gs.map (pmRawRename r c)).foldl pmStep v) := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    exact ih _ _ (pmRelStep r c w v g h)

lemma pmRelInit (r c : Bool) (x : Fin 9 → Bool) :
    pmRel r c (List.ofFn (fun a => x (pmPerm r c a))) (List.ofFn x) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i
  by_cases hi : i < 9
  · rw [pmWireInput r c hi]
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_ofFn]
  · rw [pmWireInternal r c (show 9 ≤ i by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def pmOrder (a b : ℕ) : ℕ × ℕ :=
  if a ≤ b then (a, b) else (b, a)

def pmInputs (op : PMOp) (ins : List ℕ) : List ℕ :=
  match op, ins with
  | .and, [a, b] => [(pmOrder a b).1, (pmOrder a b).2]
  | .or, [a, b] => [(pmOrder a b).1, (pmOrder a b).2]
  | _, ins => ins

lemma pmInputPerm (op : PMOp) (ins : List ℕ) :
    (pmInputs op ins).Perm ins := by
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, tail⟩⟩⟩ <;> try rfl
  all_goals
    simp only [pmInputs, pmOrder]
    split
    · rfl
    · exact List.Perm.swap a b []

lemma pmSortValue (w : List Bool) (op : PMOp) (ins : List ℕ) :
    op.eval ((pmInputs op ins).map (fun i => w.getD i false)) =
      op.eval (ins.map (fun i => w.getD i false)) := by
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, tail⟩⟩⟩ <;> try rfl
  all_goals
    simp only [pmInputs, pmOrder]
    split <;> simp [PEqualNP.CircuitLowerBounds.GateOp.eval, Bool.and_comm, Bool.or_comm]

def pmSortGate (g : PMGate) : PMGate := ⟨g.op, pmInputs g.op g.inputs⟩

def pmRenameGate (r c : Bool) (g : PMGate) : PMGate :=
  pmSortGate (pmRawRename r c g)

def pmRename (r c : Bool) (C : PMCircuit) : PMCircuit :=
  ⟨(C.gates.map (pmRawRename r c)).map
    pmSortGate, C.output⟩

lemma pmSortFold (gates : List PMGate) (w : List Bool) :
    (gates.map pmSortGate).foldl pmStep w =
      gates.foldl pmStep w := by
  induction gates generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.foldl_cons, ih]
    simp only [pmStep, pmSortGate, pmSortValue]

lemma pmWireValue (r c : Bool) (C : PMCircuit) (x : Fin 9 → Bool) (i : ℕ) :
    ((pmRename r c C).wires (List.ofFn x)).getD (pmWire r c i) false =
      (C.wires (List.ofFn (fun a => x (pmPerm r c a)))).getD i false := by
  change (((C.gates.map (pmRawRename r c)).map pmSortGate).foldl pmStep
    (List.ofFn x)).getD (pmWire r c i) false = _
  rw [pmSortFold]
  exact (pmRelFold r c C.gates _ _ (pmRelInit r c x)).2.2 i

def pmMatching (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

lemma pmMatchingPerm (r c : Bool) (x : Fin 9 → Bool) :
    pmMatching (fun a => x (pmPerm r c a)) = pmMatching x := by
  cases r <;> cases c <;>
    simp [pmMatching, pmPerm, List.getD_eq_getElem?_getD] <;> ac_rfl

def pmAndPairs : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (0, 4), (0, 5), (2, 3), (2, 5), (2, 9), (3, 4),
   (3, 5), (3, 6), (3, 7), (3, 8), (3, 9), (5, 8), (5, 9)]

def pmOrPairs : List (ℕ × ℕ) := (0, 1) :: pmAndPairs
def pmNotInputs : List ℕ := [0, 2, 3, 5, 9]

def pmPair (r c : Bool) (a b : ℕ) : ℕ × ℕ :=
  pmOrder (pmWire r c a) (pmWire r c b)

set_option maxHeartbeats 2000000 in
lemma pmAndCover :
    ∀ a b : Fin 10, a < b → (a.val, b.val) ∉ ([(0, 1), (0, 9), (1, 9)] : List (ℕ × ℕ)) →
      ∃ r c : Bool, pmPair r c a.val b.val ∈ pmAndPairs := by decide

set_option maxHeartbeats 2000000 in
lemma pmOrCover :
    ∀ a b : Fin 10, a < b → (a.val, b.val) ∉ ([(0, 9), (1, 9)] : List (ℕ × ℕ)) →
      ∃ r c : Bool, pmPair r c a.val b.val ∈ pmOrPairs := by decide

lemma pmNotCover :
    ∀ a : Fin 10, ∃ r c : Bool, pmWire r c a.val ∈ pmNotInputs := by decide

def pmFirst : PMGate := ⟨.and, [0, 1]⟩

lemma pmRenameFirst (r c : Bool) : pmRenameGate r c pmFirst = pmFirst := by
  cases r <;> cases c <;> rfl

lemma pmTwoGates (C : PMCircuit)
    (hfirst : C.gates.head? = some pmFirst)
    (hout : C.output + 1 = 9 + C.size)
    (heval : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pmMatching x) :
    ∃ second rest, C.gates = pmFirst :: second :: rest := by
  cases hg : C.gates with
  | nil => simp [hg] at hfirst
  | cons first tail =>
    have hfirst' : first = pmFirst := by simpa [hg] using hfirst
    subst first
    cases tail with
    | nil =>
      have houtput : C.output = 9 := by
        simp [PEqualNP.CircuitLowerBounds.Circuit.size, hg] at hout
        omega
      have hC : C = ⟨[pmFirst], 9⟩ := by
        cases C
        simp_all
      let x : Fin 9 → Bool := fun i => decide (i ≠ 0)
      have hwrong : (⟨[pmFirst], 9⟩ : PMCircuit).eval (List.ofFn x) ≠ pmMatching x := by decide
      exact (hwrong (by simpa [hC] using heval x)).elim
    | cons second rest =>
      exact ⟨second, rest, rfl⟩

def pmStart (x : Fin 9 → Bool) : List Bool :=
  List.ofFn x ++ [x 0 && x 1]

lemma pmFirstStep (x : Fin 9 → Bool) :
    pmStep (List.ofFn x) pmFirst = pmStart x := by
  simp [pmStep, pmFirst, pmStart,
    PEqualNP.CircuitLowerBounds.GateOp.eval, List.getD_eq_getElem?_getD]

lemma pmStart0 (x : Fin 9 → Bool) : (pmStart x).getD 0 false = x 0 := by
  unfold pmStart
  rw [List.getD_append _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma pmStart1 (x : Fin 9 → Bool) : (pmStart x).getD 1 false = x 1 := by
  unfold pmStart
  rw [List.getD_append _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma pmStart9 (x : Fin 9 → Bool) : (pmStart x).getD 9 false = (x 0 && x 1) := by
  simp only [pmStart, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]
  simp

def pmSecond (x : Fin 9 → Bool) (g : PMGate) : Bool :=
  g.op.eval (g.inputs.map (fun i => (pmStart x).getD i false))

lemma pmEarlyWire (C : PMCircuit) (g : PMGate) (rest : List PMGate)
    (h : C.gates = pmFirst :: g :: rest) (x : Fin 9 → Bool) (i : ℕ) (hi : i < 11) :
    (C.wires (List.ofFn x)).getD i false =
      (pmStart x ++ [pmSecond x g]).getD i false := by
  change (C.gates.foldl pmStep (List.ofFn x)).getD i false = _
  rw [h, List.foldl_cons, List.foldl_cons, pmFirstStep]
  apply pmFoldPrefix
  simpa [pmStep, pmStart] using hi

lemma pmSecondWire (C : PMCircuit) (g : PMGate) (rest : List PMGate)
    (h : C.gates = pmFirst :: g :: rest) (x : Fin 9 → Bool) :
    (C.wires (List.ofFn x)).getD 10 false = pmSecond x g := by
  rw [pmEarlyWire C g rest h x 10 (by decide)]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp [pmStart])]
  simp [pmStart]

lemma pmBeforeSecond (C : PMCircuit) (g : PMGate) (rest : List PMGate)
    (h : C.gates = pmFirst :: g :: rest) (x : Fin 9 → Bool) (i : ℕ) (hi : i < 10) :
    (C.wires (List.ofFn x)).getD i false = (pmStart x).getD i false := by
  rw [pmEarlyWire C g rest h x i (by omega)]
  rw [List.getD_append _ _ _ _ (by simpa [pmStart] using hi)]

lemma pmRedundantAnd (a b : ℕ)
    (h : (a, b) ∈ ([(0, 1), (0, 9), (1, 9)] : List (ℕ × ℕ))) :
    ∃ i < 10, ∀ x, pmSecond x ⟨.and, [a, b]⟩ = (pmStart x).getD i false := by
  refine ⟨9, by decide, ?_⟩
  intro x
  simp at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [-List.getD_eq_getElem?_getD, pmSecond, PEqualNP.CircuitLowerBounds.GateOp.eval, pmStart0, pmStart1, pmStart9, h0, h1]

lemma pmRedundantOr (a b : ℕ)
    (h : (a, b) ∈ ([(0, 9), (1, 9)] : List (ℕ × ℕ))) :
    ∃ i < 10, ∀ x, pmSecond x ⟨.or, [a, b]⟩ = (pmStart x).getD i false := by
  simp at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨0, by decide, fun x => ?_⟩
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp [-List.getD_eq_getElem?_getD, pmSecond, PEqualNP.CircuitLowerBounds.GateOp.eval, pmStart0, pmStart9, h0, h1]
  · refine ⟨1, by decide, fun x => ?_⟩
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp [-List.getD_eq_getElem?_getD, pmSecond, PEqualNP.CircuitLowerBounds.GateOp.eval, pmStart1, pmStart9, h0, h1]

def pmShape (j : ℕ) (g : PMGate) : Prop :=
  (g.op = .not ∧ ∃ a, a < 9 + j ∧ g.inputs = [a]) ∨
    ((g.op = .and ∨ g.op = .or) ∧ ∃ a b, a < b ∧ b < 9 + j ∧ g.inputs = [a, b])

def pmCanonical (g : PMGate) : Prop :=
  (∃ a b, (a, b) ∈ pmAndPairs ∧ g = ⟨.and, [a, b]⟩) ∨
  (∃ a b, (a, b) ∈ pmOrPairs ∧ g = ⟨.or, [a, b]⟩) ∨
  (∃ a, a ∈ pmNotInputs ∧ g = ⟨.not, [a]⟩)

lemma pmChooseSecond (g : PMGate) (hshape : pmShape 1 g)
    (hnored : ¬ ∃ i < 10, ∀ x, pmSecond x g = (pmStart x).getD i false) :
    ∃ r c : Bool, pmCanonical (pmRenameGate r c g) := by
  rcases hshape with ⟨hop, a, ha, hargs⟩ | ⟨hop, a, b, hab, hb, hargs⟩
  · have hg : g = ⟨.not, [a]⟩ := by cases g; simp_all
    obtain ⟨r, c, hr⟩ := pmNotCover ⟨a, ha⟩
    exact ⟨r, c, Or.inr (Or.inr ⟨pmWire r c a, hr, by rw [hg]; rfl⟩)⟩
  · have ha : a < 10 := by omega
    rcases hop with hop | hop
    · have hg : g = ⟨.and, [a, b]⟩ := by cases g; simp_all
      have hb' : (a, b) ∉ ([(0, 1), (0, 9), (1, 9)] : List (ℕ × ℕ)) := by
        intro bad
        apply hnored
        rw [hg]
        exact pmRedundantAnd a b bad
      obtain ⟨r, c, hr⟩ := pmAndCover ⟨a, ha⟩ ⟨b, hb⟩ hab hb'
      exact ⟨r, c, Or.inl ⟨(pmPair r c a b).1, (pmPair r c a b).2, hr, by rw [hg]; rfl⟩⟩
    · have hg : g = ⟨.or, [a, b]⟩ := by cases g; simp_all
      have hb' : (a, b) ∉ ([(0, 9), (1, 9)] : List (ℕ × ℕ)) := by
        intro bad
        apply hnored
        rw [hg]
        exact pmRedundantOr a b bad
      obtain ⟨r, c, hr⟩ := pmOrCover ⟨a, ha⟩ ⟨b, hb⟩ hab hb'
      exact ⟨r, c, Or.inr (Or.inl ⟨(pmPair r c a b).1, (pmPair r c a b).2, hr, by rw [hg]; rfl⟩)⟩

lemma pmRenameGates (r c : Bool) (C : PMCircuit) :
    (pmRename r c C).gates = C.gates.map (pmRenameGate r c) := by
  simp [pmRename, pmRenameGate, List.map_map, Function.comp_def]

lemma pmRenameLength (r c : Bool) (C : PMCircuit) :
    (pmRename r c C).gates.length = C.gates.length := by
  simp [pmRenameGates]

lemma pmRenameGet (r c : Bool) (C : PMCircuit) (j : ℕ)
    (hj : j < C.gates.length) (hj' : j < (pmRename r c C).gates.length) :
    (pmRename r c C).gates.get ⟨j, hj'⟩ = pmRenameGate r c (C.gates.get ⟨j, hj⟩) := by
  simp [pmRename, pmRenameGate]

lemma pmRenameHas (r c : Bool) (g : PMGate) (i : ℕ) (hi : i ∈ g.inputs) :
    pmWire r c i ∈ (pmRenameGate r c g).inputs := by
  change pmWire r c i ∈ pmInputs g.op (g.inputs.map (pmWire r c))
  rw [(pmInputPerm _ _).mem_iff]
  exact List.mem_map.mpr ⟨i, hi, rfl⟩

lemma pmRenameShape (r c : Bool) (j : ℕ) (g : PMGate)
    (h : pmShape j g) : pmShape j (pmRenameGate r c g) := by
  rcases h with ⟨hop, a, ha, hargs⟩ | ⟨hop, a, b, hab, hb, hargs⟩
  · have hg : g = ⟨.not, [a]⟩ := by cases g; simp_all
    subst g
    exact Or.inl ⟨rfl, pmWire r c a, pmWireEarlier r c ha, rfl⟩
  · have ha : a < 9 + j := lt_trans hab hb
    have hra := pmWireEarlier r c ha
    have hrb := pmWireEarlier r c hb
    have hne : pmWire r c a ≠ pmWire r c b := by
      intro eq
      have := congrArg (pmWire r c) eq
      rw [pmWireTwice, pmWireTwice] at this
      omega
    let p := pmPair r c a b
    have hord : p.1 < p.2 ∧ p.2 < 9 + j := by
      dsimp [p, pmPair, pmOrder]
      split <;> simp only <;> omega
    refine Or.inr ⟨hop, p.1, p.2, hord.1, hord.2, ?_⟩
    change pmInputs g.op (g.inputs.map (pmWire r c)) = [p.1, p.2]
    rw [hargs]
    rcases hop with hop | hop <;> rw [hop] <;> rfl

end PEqualNP.Outside.L_meta_25931

open PEqualNP.Outside.L_meta_25931

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_25931 : (∀ s : ℕ,
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩) →
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ s ∧
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∧
    (C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 2]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 3]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 5]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 9]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 4]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 5]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 6]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 7]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 8]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 9]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 8]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 9]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 4]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 5]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 3]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 9]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 5]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 8]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 9]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 8]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 9]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [2]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [3]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [5]⟩ ∨
     C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9]⟩)) := by
  intro s h
  rcases h with ⟨C, hfan, hsize, heval, houtput, hshape, hdistinct, hused, hfirst⟩
  change (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pmMatching x) at heval
  change C.gates.head? = some pmFirst at hfirst
  obtain ⟨second, rest, hlist⟩ := pmTwoGates C hfirst houtput heval
  let j : Fin C.gates.length := ⟨1, by simp [hlist]⟩
  have hgetSecond : C.gates.get j = second := by
    have hsome : C.gates[1]? = some second := by simp [hlist]
    have hsome' : C.gates[1]? = some (C.gates.get j) := by
      rw [List.getElem?_eq_getElem (show 1 < C.gates.length from j.isLt)]
      rfl
    exact Option.some.inj (hsome'.symm.trans hsome)
  have hshapeSecond : pmShape 1 second := by
    have hs : pmShape 1 (C.gates.get j) := hshape j
    rwa [hgetSecond] at hs
  have hnoRedundancy : ¬ ∃ i < 10, ∀ x, pmSecond x second = (pmStart x).getD i false := by
    rintro ⟨i, hi, hv⟩
    obtain ⟨x, hx⟩ := (hdistinct j).2 i hi
    apply hx
    change (C.wires (List.ofFn x)).getD 10 false = (C.wires (List.ofFn x)).getD i false
    rw [pmSecondWire C second rest hlist, pmBeforeSecond C second rest hlist x i hi]
    exact hv x
  obtain ⟨r, c, hrep⟩ := pmChooseSecond second hshapeSecond hnoRedundancy
  let D := pmRename r c C
  have hlen : D.gates.length = C.gates.length := pmRenameLength r c C
  have hsizes : D.size = C.size := hlen
  have hout : D.output = C.output := rfl
  have houtputInternal : 9 ≤ C.output := by
    have hpositive : 1 ≤ C.size := by simp [PEqualNP.CircuitLowerBounds.Circuit.size, hlist]
    omega
  let oldIndex : Fin D.gates.length → Fin C.gates.length :=
    fun i => ⟨i.val, by simpa only [hlen] using i.isLt⟩
  have hget (i : Fin D.gates.length) :
      D.gates.get i = pmRenameGate r c (C.gates.get (oldIndex i)) :=
    pmRenameGet r c C i.val (oldIndex i).isLt i.isLt
  have htransport (x : Fin 9 → Bool) (i : ℕ) :
      (D.wires (List.ofFn (fun a => x (pmPerm r c a)))).getD (pmWire r c i) false =
        (C.wires (List.ofFn x)).getD i false := by
    simpa [D, pmPermTwice] using pmWireValue r c C (fun a => x (pmPerm r c a)) i
  refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have hg' : g ∈ C.gates.map (pmRenameGate r c) := by
      simpa only [D, pmRenameGates] using hg
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hg'
    refine ⟨(hfan original ho).1, ?_⟩
    change (pmInputs original.op (original.inputs.map (pmWire r c))).length ≤ 2
    rw [(pmInputPerm _ _).length_eq, List.length_map]
    exact (hfan original ho).2
  · rw [hsizes]
    exact hsize
  · intro x
    change (D.wires (List.ofFn x)).getD C.output false = pmMatching x
    have hw := pmWireValue r c C x C.output
    rw [pmWireInternal r c houtputInternal] at hw
    change (D.wires (List.ofFn x)).getD C.output false =
      C.eval (List.ofFn (fun a => x (pmPerm r c a))) at hw
    rw [hw, heval, pmMatchingPerm]
  · simpa only [hout, hsizes] using houtput
  · intro i
    change pmShape i.val (D.gates.get i)
    rw [hget i]
    exact pmRenameShape r c i.val (C.gates.get (oldIndex i)) (hshape (oldIndex i))
  · intro i
    have hold := hdistinct (oldIndex i)
    have hi : 9 ≤ 9 + i.val := by omega
    constructor
    · obtain ⟨x, y, hxy⟩ := hold.1
      refine ⟨fun a => x (pmPerm r c a), fun a => y (pmPerm r c a), ?_⟩
      have hx := htransport x (9 + i.val)
      have hy := htransport y (9 + i.val)
      rw [pmWireInternal r c hi] at hx hy
      rw [hx, hy]
      exact hxy
    · intro k hk
      let k' := pmWire r c k
      have hk' : k' < 9 + (oldIndex i).val := pmWireEarlier r c hk
      obtain ⟨x, hx⟩ := hold.2 k' hk'
      refine ⟨fun a => x (pmPerm r c a), ?_⟩
      have hsame := htransport x (9 + i.val)
      have hprevious := htransport x k'
      have hkback : pmWire r c k' = k := pmWireTwice r c k
      rw [pmWireInternal r c hi] at hsame
      rw [hkback] at hprevious
      rw [hsame, hprevious]
      exact hx
  · intro i hi
    have hi' : (oldIndex i).val + 1 < C.gates.length := by
      simpa only [oldIndex, hlen] using hi
    obtain ⟨k, hlt, hm⟩ := hused (oldIndex i) hi'
    let nk : Fin D.gates.length := ⟨k.val, by simpa only [hlen] using k.isLt⟩
    refine ⟨nk, hlt, ?_⟩
    rw [hget nk]
    have hw := pmRenameHas r c (C.gates.get (oldIndex nk)) (9 + i.val) hm
    simpa only [pmWireInternal r c (show 9 ≤ 9 + i.val by omega)] using hw
  · change D.gates.head? = some pmFirst
    simp [D, pmRenameGates, hlist, pmRenameFirst]
  · have htail : D.gates.tail.head? = some (pmRenameGate r c second) := by
      simp [D, pmRenameGates, hlist]
    rw [htail]
    rcases hrep with ⟨a, b, hm, hg⟩ | ⟨a, b, hm, hg⟩ | ⟨a, hm, hg⟩
    · rw [hg]
      simpa [pmAndPairs] using hm
    · rw [hg]
      simpa [pmOrPairs, pmAndPairs] using hm
    · rw [hg]
      simpa [pmNotInputs] using hm
