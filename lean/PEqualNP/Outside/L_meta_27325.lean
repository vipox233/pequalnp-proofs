import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_27325

def feed (wires : List Bool) (gate : Gate) : List Bool :=
  wires ++ [gate.op.eval (gate.inputs.map fun idx => wires.getD idx false)]

def reads (gates : List Gate) (output : Nat) : List Nat :=
  gates.flatMap Gate.inputs ++ [output]

lemma agrees (gates : List Gate) (output : Nat) (left right : List Bool)
    (len : left.length = right.length)
    (eqv : ∀ idx ∈ reads gates output, idx < left.length →
      left.getD idx false = right.getD idx false) :
    (gates.foldl feed left).getD output false = (gates.foldl feed right).getD output false := by
  induction gates generalizing left right with
  | nil =>
    by_cases small : output < left.length
    · exact eqv output (by simp [reads]) small
    · simp [List.getD_eq_default, Nat.le_of_not_gt small, ← len]
  | cons gate tail ih =>
    have same : gate.inputs.map (fun i => left.getD i false) =
        gate.inputs.map (fun i => right.getD i false) := by
      apply List.map_congr_left
      intro idx mem
      by_cases small : idx < left.length
      · exact eqv idx (by simp [reads, mem]) small
      · simp [List.getD_eq_default, Nat.le_of_not_gt small, ← len]
    apply ih
    · simp [feed, len]
    · intro idx mem _
      by_cases small : idx < left.length
      · simp only [feed, List.getD_append _ _ _ _ small,
          List.getD_append _ _ _ _ (len ▸ small)]
        exact eqv idx (by simpa [reads, or_assoc] using Or.inr (a := idx ∈ gate.inputs) mem) small
      · simp only [feed, List.getD_append_right _ _ _ _ (Nat.le_of_not_gt small),
          List.getD_append_right _ _ _ _ (len ▸ Nat.le_of_not_gt small), len, same]

lemma inputsBound (gates : List Gate) (bound : ∀ g ∈ gates, g.inputs.length ≤ 2) :
    (gates.flatMap Gate.inputs).length ≤ 2 * gates.length := by
  induction gates with
  | nil => simp
  | cons gate tail ih =>
    have first := bound gate (by simp)
    have rest := ih (fun g mem => bound g (by simp [mem]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

def input (row : Nat) (idx : Fin 9) : Bool := row.testBit idx.val

def matching (row : Nat) : Bool :=
  let x := input row
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def firstGate : Gate := ⟨.and, [0, 4]⟩
def secondGate : Gate := ⟨.or, [1, 9]⟩
def base (row : Nat) : List Bool := feed (feed (List.ofFn (input row)) firstGate) secondGate

lemma baseLen (row : Nat) : (base row).length = 11 := by simp [base, feed]

def witness (idx : Fin 9) : Nat × Nat :=
  [(161,160),(115,113),(84,80),(140,132),(84,68),(98,66),(84,20),(140,12),(266,10)].getD idx.val (0,0)

lemma rawWitness : ∀ idx : Fin 9,
    let p := witness idx
    matching p.1 ≠ matching p.2 ∧ ∀ j : Fin 11, j.val ≠ idx.val →
      (base p.1).getD j.val false = (base p.2).getD j.val false := by decide

def represents (gates : List Gate) (output : Nat) (rows : Nat → List Bool) : Prop :=
  ∀ row, (gates.foldl feed (rows row)).getD output false = matching row

lemma budget (tail : List Gate) (output : Nat) (small : tail.length ≤ 9)
    (bound : ∀ g ∈ tail, g.inputs.length ≤ 2) (works : represents tail output base)
    (live : ∀ i, 10 ≤ i → i < 11 + tail.length → i ∈ reads tail output) :
    tail.length = 9 ∧ (reads tail output).length = 19 ∧
      (reads tail output).Nodup ∧ 9 ∉ reads tail output := by
  let required := (Finset.range (11 + tail.length)).erase 9
  have card : required.card = 10 + tail.length := by
    dsimp [required]
    rw [Finset.card_erase_of_mem (by simp; omega), Finset.card_range]
    omega
  have incl : required ⊆ (reads tail output).toFinset := by
    intro idx hi
    simp only [required, Finset.mem_erase, Finset.mem_range] at hi
    apply List.mem_toFinset.mpr
    by_cases low : idx < 9
    · by_contra absent
      let j : Fin 9 := ⟨idx,low⟩
      obtain ⟨diff,rest⟩ := rawWitness j
      apply diff
      rw [← works, ← works]
      apply agrees _ _ _ _ (by simp [baseLen])
      intro wire mem lim
      exact rest ⟨wire, by simpa [baseLen] using lim⟩ (by intro h; change wire = idx at h; exact absent (h ▸ mem))
    · exact live idx (by omega) hi.2
  have upper := inputsBound tail bound
  have readLimit : (reads tail output).length ≤ 2 * tail.length + 1 := by simpa [reads] using upper
  have lowCard := Finset.card_le_card incl
  have highCard := (reads tail output).toFinset_card_le
  have size : tail.length = 9 := by omega
  have count : (reads tail output).length = 19 := by omega
  refine ⟨size, count, List.nodup_iff_le_length_dedup.mpr ?_, ?_⟩
  · rw [← List.card_toFinset]; omega
  · have eq := Finset.eq_of_subset_of_card_le incl (by omega)
    intro mem
    simpa [required] using (show 9 ∈ required from eq.symm ▸ List.mem_toFinset.mpr mem)

def binary (isOr : Bool) (lhs rhs : Nat) : Gate :=
  ⟨if isOr then .or else .and, [lhs, rhs]⟩

def extend (rows : Nat → List Bool) (gate : Gate) (row : Nat) := feed (rows row) gate

def clash (rows : Nat → List Bool) (width : Nat) (used : List Nat) (pair : Nat × Nat) : Bool :=
  matching pair.1 != matching pair.2 && (List.range width).all fun idx =>
    used.contains idx || (rows pair.1).getD idx false == (rows pair.2).getD idx false

lemma exclude (gates : List Gate) (output width : Nat) (rows : Nat → List Bool)
    (works : represents gates output rows) (size : ∀ row, (rows row).length = width)
    (used : List Nat) (disjoint : ∀ idx ∈ reads gates output, idx ∉ used)
    (pairs : List (Nat × Nat)) : pairs.any (clash rows width used) ≠ true := by
  intro hit
  obtain ⟨pair, _, bad⟩ := List.any_eq_true.mp hit
  simp only [clash, Bool.and_eq_true, bne_iff_ne, List.all_eq_true] at bad
  apply bad.1
  rw [← works, ← works]
  apply agrees _ _ _ _ (by simp [size])
  intro idx mem small
  have eqv := bad.2 idx (List.mem_range.mpr (by simpa [size] using small))
  simpa [List.contains_eq_mem, disjoint idx mem] using eqv

def pairsA : List (Nat × Nat) :=
  [(84,20),(98,66),(172,168),(225,97),(229,228),(311,295),(303,47),(157,149),
   (123,121),(158,30),(86,82),(169,137),(84,68),(106,42),(458,202),(140,132),(163,162)]

def pairsB : List (Nat × Nat) :=
  [(84,20),(98,66),(172,168),(225,97),(229,228),(309,293),(303,47),(103,101),
   (159,151),(158,30),(169,137),(330,322),(458,202),(84,70),(311,295)]

set_option maxHeartbeats 8000000 in
lemma thirdCheck : ∀ (a b : Fin 11) (op : Bool), a < b → a.val ≠ 9 → b.val ≠ 9 →
    ((a.val = 1 ∨ a.val = 8) ∧ b.val = 10 ∧ op = false) ∨
    pairsA.any (clash (extend base (binary op a.val b.val)) 12 [9,a.val,b.val]) = true := by decide

def prior (flag : Bool) : Nat := if flag then 8 else 1

set_option maxHeartbeats 8000000 in
lemma fourthCheck : ∀ (flag : Bool) (a b : Fin 12) (op : Bool), a < b →
    a.val ∉ [9,prior flag,10] → b.val ∉ [9,prior flag,10] →
    pairsB.any (clash (extend (extend base (binary false (prior flag) 10)) (binary op a.val b.val))
      13 [9,prior flag,10,a.val,b.val]) = true := by decide

lemma finish (rest : List Gate) (output : Nat) (a b : Fin 11) (c d : Fin 12)
    (op nextOp : Bool) (ab : a < b) (cd : c < d)
    (works : represents (binary op a b :: binary nextOp c d :: rest) output base)
    (unique : (a.val :: b.val :: c.val :: d.val :: reads rest output).Nodup)
    (missing : 9 ∉ a.val :: b.val :: c.val :: d.val :: reads rest output) : False := by
  let rows := extend base (binary op a b)
  have size : ∀ row, (rows row).length = 12 := by simp [rows, extend, feed, baseLen]
  have hworks : represents (binary nextOp c d :: rest) output rows := works
  simp only [List.nodup_cons, List.mem_cons, not_or] at unique missing
  have fresh : ∀ idx ∈ reads (binary nextOp c d :: rest) output, idx ∉ [9,a.val,b.val] := by
    intro idx mem
    change idx ∈ c.val :: d.val :: reads rest output at mem
    simp only [List.mem_cons] at mem
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    aesop
  have noHit := exclude _ _ _ rows hworks size _ fresh pairsA
  have casesAB := (thirdCheck a b op ab (by aesop) (by aesop)).resolve_right noHit
  obtain ⟨left, right, opEq⟩ := casesAB
  obtain ⟨flag, old⟩ : ∃ flag, a.val = prior flag := by
    rcases left with left | left
    · exact ⟨false,left⟩
    · exact ⟨true,left⟩
  let lastRows := extend rows (binary nextOp c d)
  have lastWorks : represents rest output lastRows := works
  have lastSize : ∀ row, (lastRows row).length = 13 := by simp [lastRows, extend, feed, size]
  have lastFresh : ∀ idx ∈ reads rest output, idx ∉ [9,a.val,b.val,c.val,d.val] := by
    intro idx mem
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    aesop
  have fail := exclude _ _ _ lastRows lastWorks lastSize _ lastFresh pairsB
  apply fail
  dsimp only [lastRows, rows]
  rw [old, right, opEq]
  apply fourthCheck flag c d nextOp cd <;> rw [← old, ← right] <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] <;> aesop

def standard (gate : Gate) (width : Nat) : Prop :=
  (gate.op = .not ∧ ∃ a, a < width ∧ gate.inputs = [a]) ∨
    ((gate.op = .and ∨ gate.op = .or) ∧ ∃ a b, a < b ∧ b < width ∧ gate.inputs = [a,b])

lemma asBinary (gate : Gate) (width : Nat) (shape : standard gate width)
    (two : gate.inputs.length = 2) :
    ∃ (a b : Fin width) (op : Bool), a < b ∧ gate = binary op a b := by
  rcases gate with ⟨op, ins⟩
  rcases shape with ⟨_, a, _, h⟩ | ⟨ops,a,b,ab,lt,insEq⟩
  · change ins = [a] at h
    simp [h] at two
  · refine ⟨⟨a,lt_trans ab lt⟩, ⟨b,lt⟩, ?_⟩
    rcases ops with hop | hop
    · exact ⟨false, ab, by cases hop; cases insEq; rfl⟩
    · exact ⟨true, ab, by cases hop; cases insEq; rfl⟩

end PEqualNP.Outside.L_meta_27325

open PEqualNP.Outside.L_meta_27325

theorem PEqualNP.Outside.L_meta_27325 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 9]⟩)) := by
  rintro ⟨⟨gates,output⟩, fan, limit, computes, last, normal, _, live, front, second⟩
  change gates.head? = some firstGate at front
  change gates.tail.head? = some secondGate at second
  obtain ⟨tail, rfl⟩ : ∃ tail, gates = firstGate :: secondGate :: tail := by
    cases gates with
    | nil => contradiction
    | cons g gs =>
      cases gs with
      | nil => contradiction
      | cons h tail => exact ⟨tail, by rw [Option.some.inj front, Option.some.inj second]⟩
  let allGates := firstGate :: secondGate :: tail
  have bound : ∀ g ∈ tail, g.inputs.length ≤ 2 := fun g mem =>
    (fan g (by change g ∈ firstGate :: secondGate :: tail; simp [mem])).2
  have works : represents tail output base := fun row => computes (input row)
  change tail.length + 1 + 1 ≤ 11 at limit
  change output + 1 = 9 + (tail.length + 1 + 1) at last
  have alive : ∀ idx, 10 ≤ idx → idx < 11 + tail.length → idx ∈ reads tail output := by
    intro idx low high
    by_cases final : idx = output
    · simp [reads, final]
    let j : Fin allGates.length := ⟨idx - 9, by simp [allGates]; omega⟩
    obtain ⟨k, _, used⟩ := live j (by change idx - 9 + 1 < tail.length + 1 + 1; omega)
    have fixed : 9 + j.val = idx := by dsimp [j]; omega
    rw [fixed] at used
    let gate := allGates.get k
    have use : idx ∈ gate.inputs := used
    have mem : gate ∈ firstGate :: secondGate :: tail := List.get_mem allGates k
    simp only [List.mem_cons] at mem
    rcases mem with first | second | inTail
    · rw [first] at use; simp [firstGate] at use; omega
    · rw [second] at use; simp [secondGate] at use; omega
    · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨gate,inTail,use⟩)
  obtain ⟨size, count, uniq, absent⟩ := budget tail output (by omega) bound works alive
  cases tail with
  | nil => contradiction
  | cons third more =>
    cases more with
    | nil => simp at size
    | cons fourth rest =>
      have ht := bound third (by simp)
      have hf := bound fourth (by simp)
      have hr := inputsBound rest (fun g mem => bound g (by simp [mem]))
      simp only [reads, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at count
      simp only [List.length_cons] at size
      have thirdShape : standard third 11 := normal ⟨2, by simp⟩
      have fourthShape : standard fourth 12 := normal ⟨3, by simp⟩
      obtain ⟨a,b,op,ab,rfl⟩ := asBinary third 11 thirdShape (by omega)
      obtain ⟨c,d,nextOp,cd,rfl⟩ := asBinary fourth 12 fourthShape (by omega)
      exact finish rest output a b c d op nextOp ab cd works uniq absent
