import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket
import Mathlib.Data.List.GetD
import Mathlib.Tactic.IntervalCases

namespace PEqualNP.Outside.L_meta_50868

abbrev EnumTable := Fin 6 → Bool

def enumTable (m : Nat) : EnumTable := fun t => m.testBit t.val

def enumInit : List EnumTable := [enumTable 62, enumTable 60, enumTable 56, enumTable 48,
  enumTable 32, enumTable 0, enumTable 63]

def enumEncode (f : EnumTable) : BitVec 6 :=
  BitVec.ofBoolListLE [f 0, f 1, f 2, f 3, f 4, f 5]

lemma enumEncode_bit (f : EnumTable) (i : Fin 6) : (enumEncode f).getLsbD i.val = f i := by
  unfold enumEncode
  rw [BitVec.getLsbD_ofBoolListLE]
  fin_cases i <;> rfl

lemma enumEncode_table (m : Nat) : enumEncode (enumTable m) = BitVec.ofNat 6 m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [enumEncode_bit (enumTable m) ⟨i, hi⟩]
  simp only [BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and, enumTable]

lemma enumEncode_and (a b : EnumTable) :
    enumEncode (fun t => a t && b t) = (enumEncode a &&& enumEncode b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and]
  rw [enumEncode_bit (fun t => a t && b t) ⟨i, hi⟩, enumEncode_bit a ⟨i, hi⟩,
    enumEncode_bit b ⟨i, hi⟩]

lemma enumEncode_or (a b : EnumTable) :
    enumEncode (fun t => a t || b t) = (enumEncode a ||| enumEncode b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or]
  rw [enumEncode_bit (fun t => a t || b t) ⟨i, hi⟩, enumEncode_bit a ⟨i, hi⟩,
    enumEncode_bit b ⟨i, hi⟩]

lemma enumEncode_not (a : EnumTable) : enumEncode (fun t => !a t) = ~~~enumEncode a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  rw [enumEncode_bit (fun t => !a t) ⟨i, hi⟩, enumEncode_bit a ⟨i, hi⟩]

lemma enumEncode_inj : Function.Injective enumEncode := by
  intro a b hab
  funext i
  rw [← enumEncode_bit a i, hab, enumEncode_bit b i]

def enumPush (f : EnumTable) (bank : List EnumTable) : List EnumTable :=
  if (bank.map enumEncode).contains (enumEncode f) then bank else f :: bank

lemma enumPush_of_mem {f : EnumTable} {bank : List EnumTable} (h : f ∈ bank) :
    enumPush f bank = bank := by
  have hc : (bank.map enumEncode).contains (enumEncode f) = true :=
    List.contains_iff_mem.mpr (List.mem_map.mpr ⟨f, h, rfl⟩)
  simp only [enumPush, hc, ite_true]

lemma enumMemPush {f g : EnumTable} {bank : List EnumTable} (h : g ∈ bank) :
    g ∈ enumPush f bank := by
  unfold enumPush
  split
  · exact h
  · exact List.mem_cons_of_mem _ h

lemma enumPush_mem (f : EnumTable) (bank : List EnumTable) : f ∈ enumPush f bank := by
  unfold enumPush
  split
  · obtain ⟨g, hg, he⟩ := List.mem_map.mp (List.contains_iff_mem.mp (by assumption))
    exact enumEncode_inj he ▸ hg
  · exact List.mem_cons_self

def enumPushCode (f : BitVec 6) (bank : List (BitVec 6)) : List (BitVec 6) :=
  if bank.contains f then bank else f :: bank

lemma enumMapPush (f : EnumTable) (bank : List EnumTable) :
    (enumPush f bank).map enumEncode = enumPushCode (enumEncode f) (bank.map enumEncode) := by
  unfold enumPush enumPushCode
  split <;> rfl

def enumMissing (bank : List (BitVec 6)) : Nat :=
  (if bank.contains 6 then 0 else 1) + (if bank.contains 14 then 0 else 1) +
    (if bank.contains 44 then 0 else 1)

lemma enumMissing_push (f : BitVec 6) (bank : List (BitVec 6)) :
    enumMissing bank ≤ enumMissing (enumPushCode f bank) + 1 := by
  unfold enumPushCode
  split
  · omega
  · by_cases h6 : f = 6
    · subst f
      simp only [enumMissing, List.contains_cons, beq_self_eq_true, Bool.true_or,
        show ((14 : BitVec 6) == 6) = false by decide,
        show ((44 : BitVec 6) == 6) = false by decide, Bool.false_or, ite_true, Nat.zero_add]
      split <;> omega
    · by_cases h14 : f = 14
      · subst f
        simp only [enumMissing, List.contains_cons, beq_self_eq_true, Bool.true_or,
          show ((6 : BitVec 6) == 14) = false by decide,
          show ((44 : BitVec 6) == 14) = false by decide, Bool.false_or, ite_true, Nat.add_zero]
        split <;> omega
      · by_cases h44 : f = 44
        · subst f
          simp only [enumMissing, List.contains_cons, beq_self_eq_true, Bool.true_or,
            show ((6 : BitVec 6) == 44) = false by decide,
            show ((14 : BitVec 6) == 44) = false by decide, Bool.false_or, ite_true, Nat.add_zero]
          split <;> omega
        · have n6 : (6 : BitVec 6) ≠ f := fun h => h6 h.symm
          have n14 : (14 : BitVec 6) ≠ f := fun h => h14 h.symm
          have n44 : (44 : BitVec 6) ≠ f := fun h => h44 h.symm
          simp only [enumMissing, List.contains_cons, beq_false_of_ne n6,
            beq_false_of_ne n14, beq_false_of_ne n44, Bool.false_or]
          omega

def enumChoices (nots : Nat) (bank : List (BitVec 6)) : List (BitVec 6 × Nat) :=
  let binary := bank.flatMap fun a => bank.flatMap fun b => [(a &&& b, nots), (a ||| b, nots)]
  let unary := match nots with
    | 0 => []
    | n+1 => bank.map fun a => (~~~a, n)
  (binary ++ unary).eraseDups

def enumCore : Nat → Nat → List (BitVec 6) → Bool
  | 0, _, bank => enumMissing bank == 0
  | steps+1, nots, bank =>
    if enumMissing bank = 0 then true
    else if enumMissing bank > steps+1 then false
    else enumCore steps nots bank ||
      (enumChoices nots bank).any (fun p => enumCore steps p.2 (enumPushCode p.1 bank))

lemma enumCore_le {steps nots : Nat} {bank : List (BitVec 6)}
    (h : enumCore steps nots bank = true) : enumMissing bank ≤ steps := by
  cases steps with
  | zero => simpa [enumCore] using h
  | succ steps =>
    by_cases hz : enumMissing bank = 0
    · omega
    · by_contra hn
      simp [enumCore, hz, show steps + 1 < enumMissing bank by omega] at h

def enumPossible (steps nots : Nat) (bank : List EnumTable) : Bool :=
  enumCore steps nots (bank.map enumEncode)

lemma enumDone {steps nots : Nat} {bank : List EnumTable}
    (h6 : enumTable 6 ∈ bank) (h14 : enumTable 14 ∈ bank) (h44 : enumTable 44 ∈ bank) :
    enumPossible steps nots bank = true := by
  have hc (m : Nat) (h : enumTable m ∈ bank) :
      (bank.map enumEncode).contains (BitVec.ofNat 6 m) = true := by
    rw [← enumEncode_table m]
    exact List.contains_iff_mem.mpr (List.mem_map.mpr ⟨_, h, rfl⟩)
  have c6 : (bank.map enumEncode).contains (6 : BitVec 6) = true := hc 6 h6
  have c14 : (bank.map enumEncode).contains (14 : BitVec 6) = true := hc 14 h14
  have c44 : (bank.map enumEncode).contains (44 : BitVec 6) = true := hc 44 h44
  have hz : enumMissing (bank.map enumEncode) = 0 := by
    simp only [enumMissing, c6, c14, c44, ite_true, Nat.zero_add]
  cases steps <;> simp [enumPossible, enumCore, hz]

lemma enumSkip {steps nots : Nat} {bank : List EnumTable}
    (h : enumPossible steps nots bank = true) : enumPossible (steps+1) nots bank = true := by
  have hn := enumCore_le h
  have hle : ¬ steps + 1 < enumMissing (bank.map enumEncode) := by omega
  unfold enumPossible at *
  simp [enumCore, hle, h]

lemma enumStep {steps used rem : Nat} {bank : List EnumTable} {f : EnumTable}
    (hm : (enumEncode f, rem) ∈ enumChoices used (bank.map enumEncode))
    (h : enumPossible steps rem (enumPush f bank) = true) :
    enumPossible (steps+1) used bank = true := by
  unfold enumPossible at *
  rw [enumMapPush] at h
  have hn := enumCore_le h
  have hp := enumMissing_push (enumEncode f) (bank.map enumEncode)
  have hle : ¬ steps + 1 < enumMissing (bank.map enumEncode) := by omega
  have hj : (enumChoices used (bank.map enumEncode)).any
      (fun p => enumCore steps p.2 (enumPushCode p.1 (bank.map enumEncode))) = true :=
    List.any_eq_true.mpr ⟨_, hm, h⟩
  simp [enumCore, hle, hj]

lemma enumAnd {steps nots : Nat} {bank : List EnumTable} {a b : EnumTable}
    (ha : a ∈ bank) (hb : b ∈ bank)
    (h : enumPossible steps nots (enumPush (fun t => a t && b t) bank) = true) :
    enumPossible (steps+1) nots bank = true := by
  apply enumStep _ h
  rw [enumEncode_and]
  apply List.mem_eraseDups.mpr
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨_, List.mem_map.mpr ⟨a, ha, rfl⟩,
    List.mem_flatMap.mpr ⟨_, List.mem_map.mpr ⟨b, hb, rfl⟩, List.mem_cons_self⟩⟩

lemma enumOr {steps nots : Nat} {bank : List EnumTable} {a b : EnumTable}
    (ha : a ∈ bank) (hb : b ∈ bank)
    (h : enumPossible steps nots (enumPush (fun t => a t || b t) bank) = true) :
    enumPossible (steps+1) nots bank = true := by
  apply enumStep _ h
  rw [enumEncode_or]
  apply List.mem_eraseDups.mpr
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨_, List.mem_map.mpr ⟨a, ha, rfl⟩,
    List.mem_flatMap.mpr ⟨_, List.mem_map.mpr ⟨b, hb, rfl⟩,
      List.mem_cons_of_mem _ List.mem_cons_self⟩⟩

lemma enumNot {steps nots : Nat} {bank : List EnumTable} {a : EnumTable}
    (ha : a ∈ bank)
    (h : enumPossible steps nots (enumPush (fun t => !a t) bank) = true) :
    enumPossible (steps+1) (nots+1) bank = true := by
  apply enumStep _ h
  rw [enumEncode_not]
  apply List.mem_eraseDups.mpr
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨a, ha, rfl⟩, rfl⟩

def enumCodes : List (BitVec 6) := [62, 60, 56, 48, 32, 0, 63]

lemma enumInit_codes : enumInit.map enumEncode = enumCodes := by rfl

lemma enumFirstChoices : enumChoices 2 enumCodes =
    [(62, 2), (60, 2), (56, 2), (48, 2), (32, 2), (0, 2), (63, 2), (1, 1), (3, 1), (7, 1), (15, 1), (31, 1), (63, 1), (0, 1)] := by rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma enumFour0 : enumCore 4 2 [62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma enumFour1 : enumCore 4 1 [1, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma enumFour2 : enumCore 4 1 [3, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma enumFour3 : enumCore 4 1 [7, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma enumFour4 : enumCore 4 1 [15, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma enumFour5 : enumCore 4 1 [31, 62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma enumFour6 : enumCore 4 1 [62, 60, 56, 48, 32, 0, 63] = false := by decide +kernel

lemma enumImpossible : enumPossible 5 2 enumInit = false := by
  unfold enumPossible
  rw [enumInit_codes, enumCore]
  have hm : enumMissing enumCodes = 3 := by decide
  have hs : enumCore 4 2 enumCodes = false := enumFour0
  rw [hm, if_neg (by decide), if_neg (by decide), hs]
  have hall : (enumChoices 2 enumCodes).any
      (fun p => enumCore 4 p.2 (enumPushCode p.1 enumCodes)) = false := by
    apply List.any_eq_false.mpr
    intro p hp
    rw [enumFirstChoices] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Bool.eq_false_iff.mp enumFour0
    · exact Bool.eq_false_iff.mp enumFour0
    · exact Bool.eq_false_iff.mp enumFour0
    · exact Bool.eq_false_iff.mp enumFour0
    · exact Bool.eq_false_iff.mp enumFour0
    · exact Bool.eq_false_iff.mp enumFour0
    · exact Bool.eq_false_iff.mp enumFour0
    · exact Bool.eq_false_iff.mp enumFour1
    · exact Bool.eq_false_iff.mp enumFour2
    · exact Bool.eq_false_iff.mp enumFour3
    · exact Bool.eq_false_iff.mp enumFour4
    · exact Bool.eq_false_iff.mp enumFour5
    · exact Bool.eq_false_iff.mp enumFour6
    · exact Bool.eq_false_iff.mp enumFour6
  simp only [hall, Bool.false_or]

open PEqualNP.CircuitLowerBounds

lemma gateClassNot (g : Gate) (w : Fin 6 → List Bool) (bank : List (Fin 6 → Bool))
    (hbase : ∀ i ∈ g.inputs, (fun t => (w t).getD i false) ∈ bank)
    (h0 : (fun _ => false) ∈ bank) (hop : g.op = .not) :
    let out := fun t => g.op.eval (g.inputs.map fun i => (w t).getD i false)
    ∃ a ∈ bank, out = fun t => !a t := by
  dsimp only
  rw [hop]
  cases h : g.inputs with
  | nil =>
    exact ⟨fun _ => false, h0, rfl⟩
  | cons i tail =>
    exact ⟨fun t => (w t).getD i false, hbase i (by simp [h]), rfl⟩

lemma gateClassOther (g : Gate) (w : Fin 6 → List Bool) (bank : List (Fin 6 → Bool))
    (hbase : ∀ i ∈ g.inputs, (fun t => (w t).getD i false) ∈ bank)
    (h0 : (fun _ => false) ∈ bank) (h1 : (fun _ => true) ∈ bank)
    (hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hop : g.op ≠ .not) :
    let out := fun t => g.op.eval (g.inputs.map fun i => (w t).getD i false)
    out ∈ bank ∨ (∃ a ∈ bank, ∃ b ∈ bank, out = fun t => a t && b t) ∨
      (∃ a ∈ bank, ∃ b ∈ bank, out = fun t => a t || b t) := by
  dsimp only
  have hop' : g.op = .and ∨ g.op = .or := by
    have h : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hfan.1
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hop h).elim
  cases hins : g.inputs with
  | nil =>
    left
    rcases hop' with h | h <;> rw [h]
    · exact h1
    · exact h0
  | cons i tail =>
    have hi := hbase i (by simp [hins])
    cases tail with
    | nil =>
      left
      rcases hop' with h | h <;> simpa [h, GateOp.eval] using hi
    | cons j tail =>
      have hj := hbase j (by simp [hins])
      cases tail with
      | nil =>
        rcases hop' with h | h <;> rw [h]
        · exact Or.inr (Or.inl ⟨_, hi, _, hj, by simp [GateOp.eval]⟩)
        · exact Or.inr (Or.inr ⟨_, hi, _, hj, by simp [GateOp.eval]⟩)
      | cons k tail =>
        have hh := hfan.2
        rw [hins] at hh
        simp at hh

open PEqualNP.CircuitLowerBounds

private def emit (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def wireTable (w : Fin 6 → List Bool) (i : ℕ) : EnumTable :=
  fun t => (w t).getD i false

private def initialRows (t : Fin 6) : List Bool :=
  List.ofFn (fun i : Fin 5 => decide (i.val < t.val)) ++ [false, true]

private def isNegation (g : Gate) : Bool :=
  @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq _ _)

private lemma initialRows_length (t : Fin 6) : (initialRows t).length = 7 := by
  simp [initialRows]

private lemma initialRows_mem (i : ℕ) (hi : i < 7) : wireTable initialRows i ∈ enumInit := by
  interval_cases i <;> decide

private lemma run_search (gs : List Gate) (k : ℕ) (w : Fin 6 → List Bool)
    (steps nots : ℕ) (bank : List EnumTable)
    (hlen : ∀ t, (w t).length = k)
    (hbank : ∀ i < k, wireTable w i ∈ bank)
    (h0 : (fun _ => false) ∈ bank) (h1 : (fun _ => true) ∈ bank)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hread : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < k+j)
    (hsize : gs.length ≤ steps)
    (hnot : (gs.filter isNegation).length ≤ nots)
    (hgoal : ∀ b : List EnumTable,
      (∀ i < k + gs.length, wireTable (fun t => gs.foldl emit (w t)) i ∈ b) →
      (fun t : Fin 6 => (6 : Nat).testBit t.val) ∈ b ∧
      (fun t : Fin 6 => (14 : Nat).testBit t.val) ∈ b ∧
      (fun t : Fin 6 => (44 : Nat).testBit t.val) ∈ b) :
    enumPossible steps nots bank = true := by
  induction gs generalizing k w steps nots bank with
  | nil =>
    have ⟨h6, h14, h44⟩ := hgoal bank (by simpa using hbank)
    exact enumDone h6 h14 h44
  | cons g gs ih =>
    cases steps with
    | zero => simp at hsize
    | succ steps =>
      let w' : Fin 6 → List Bool := fun t => emit (w t) g
      let f : EnumTable := fun t => g.op.eval (g.inputs.map fun i => (w t).getD i false)
      have hf : ∀ i ∈ g.inputs, wireTable w i ∈ bank := by
        intro i hi
        apply hbank
        simpa using hread 0 (by simp) i (by simpa using hi)
      have hf' : ∀ i ∈ g.inputs, (fun t => (w t).getD i false) ∈ bank := hf
      have hlen' (t : Fin 6) : (w' t).length = k+1 := by simp [w', emit, hlen]
      have hprev (i : ℕ) (hi : i < k) : wireTable w' i = wireTable w i := by
        funext t
        exact List.getD_append _ _ _ _ (by simpa [hlen] using hi)
      have hout : wireTable w' k = f := by
        funext t
        simp [w', wireTable, emit, hlen, f]
      have hrec (b : List EnumTable) (hb : ∀ a ∈ bank, a ∈ b) (hfb : f ∈ b)
          (nb : ℕ) (hn : (gs.filter isNegation).length ≤ nb) :
          enumPossible steps nb b = true := by
        apply ih (k+1) w' steps nb b hlen' ?_ (hb _ h0) (hb _ h1) ?_ ?_ ?_ hn ?_
        · intro i hi
          by_cases h : i < k
          · rw [hprev i h]
            exact hb _ (hbank i h)
          · have he : i = k := by omega
            simpa only [he, hout] using hfb
        · intro a ha
          exact hfan a (List.mem_cons_of_mem _ ha)
        · intro j hj i hi
          have hh := hread (j+1) (by simpa using hj) i (by simpa using hi)
          omega
        · simpa using hsize
        · intro B hB
          apply hgoal B
          intro i hi
          apply hB
          simp only [List.length_cons] at hi
          omega
      have take (nb : ℕ) (hn : (gs.filter isNegation).length ≤ nb) :
          enumPossible steps nb (enumPush f bank) = true :=
        hrec _ (fun a ha => enumMemPush ha) (enumPush_mem f bank) nb hn
      by_cases hop : g.op = GateOp.not
      · cases nots with
        | zero => simp [isNegation, hop] at hnot
        | succ nots =>
          obtain ⟨a, ha, he⟩ := gateClassNot g w bank hf' h0 hop
          have hn : (gs.filter isNegation).length ≤ nots := by
            simpa [List.filter_cons, show isNegation g = true by simp [isNegation, hop]] using hnot
          have hh := take nots hn
          change f = _ at he
          rw [he] at hh
          exact enumNot ha hh
      · have hn : (gs.filter isNegation).length ≤ nots := by
          simpa [List.filter_cons, show isNegation g = false by simp [isNegation, hop]] using hnot
        rcases gateClassOther g w bank hf' h0 h1 (hfan g (by simp)) hop with h | h | h
        · exact enumSkip (hrec bank (fun _ h => h) h nots hn)
        · obtain ⟨a, ha, b, hb, he⟩ := h
          have hh := take nots hn
          change f = _ at he
          rw [he] at hh
          exact enumAnd ha hb hh
        · obtain ⟨a, ha, b, hb, he⟩ := h
          have hh := take nots hn
          change f = _ at he
          rw [he] at hh
          exact enumOr ha hb hh

end PEqualNP.Outside.L_meta_50868

theorem PEqualNP.Outside.L_meta_50868 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (6 : Nat).testBit t.val ∧
    w.getD q.val false = (14 : Nat).testBit t.val ∧
    w.getD r.val false = (44 : Nat).testBit t.val)) := by
  intro h
  rcases h with ⟨D, p, q, r, hfan, hread, hnot, hsize, hval⟩
  have ht := PEqualNP.Outside.L_meta_50868.run_search D.gates 7
    PEqualNP.Outside.L_meta_50868.initialRows 5 2 PEqualNP.Outside.L_meta_50868.enumInit
    PEqualNP.Outside.L_meta_50868.initialRows_length PEqualNP.Outside.L_meta_50868.initialRows_mem
    (by decide) (by decide) hfan hread hsize hnot ?_
  · exact (show false ≠ true by decide)
      (PEqualNP.Outside.L_meta_50868.enumImpossible.symm.trans ht)
  · intro b hb
    have hp := hb p.val p.isLt
    have hq := hb q.val q.isLt
    have hr := hb r.val r.isLt
    have hp' : _ = (fun t : Fin 6 => (6 : Nat).testBit t.val) :=
      funext fun t => (hval t).1
    have hq' : _ = (fun t : Fin 6 => (14 : Nat).testBit t.val) :=
      funext fun t => (hval t).2.1
    have hr' : _ = (fun t : Fin 6 => (44 : Nat).testBit t.val) :=
      funext fun t => (hval t).2.2
    exact ⟨hp' ▸ hp, hq' ▸ hq, hr' ▸ hr⟩
