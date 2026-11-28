import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_30254.Seven

def packedLimbs (xs : List Nat) : Nat := xs.foldl (fun a z => (a <<< 60) + z) 0

abbrev Forest := Nat → Nat × Nat

def unpack (packed width index : Nat) : Nat :=
  (packed >>> (width * index)) &&& ((1 <<< width) - 1)

def decodeNode (parentWidth width packed index : Nat) : Nat × Nat :=
  let entry := unpack packed width index
  (entry &&& ((1 <<< parentWidth) - 1), entry >>> parentWidth)

def treeBlock (start count : Nat) (check : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ next i => check i && next (i + 1)) count) start

theorem treeBlock_at {start count i : Nat} {check : Nat → Bool}
    (h : treeBlock start count check = true) (lo : start ≤ i) (hi : i < start + count) :
    check i = true := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    change (check start && treeBlock (start + 1) count check) = true at h
    rcases Bool.and_eq_true_iff.mp h with ⟨here, rest⟩
    by_cases eq : i = start
    · simpa [eq] using here
    · exact ih rest (by omega) (by omega)

theorem treeBlock_merge {start left right : Nat} {check : Nat → Bool}
    (a : treeBlock start left check = true)
    (b : treeBlock (start + left) right check = true) :
    treeBlock start (left + right) check = true := by
  induction left generalizing start with
  | zero => simpa using b
  | succ left ih =>
    rw [Nat.succ_add]
    change (check start && treeBlock (start + 1) (left + right) check) = true
    change (check start && treeBlock (start + 1) left check) = true at a
    rcases Bool.and_eq_true_iff.mp a with ⟨here, rest⟩
    exact Bool.and_eq_true_iff.mpr ⟨here, ih rest (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using b)⟩

abbrev Word := Nat

abbrev RowState := Nat × List Word × List (Word × Word × Word)

abbrev CutCheck := RowState → Bool

def rootWords (base : List Word) (token : Nat) : List Word :=
  List.rec (motive := fun _ => Nat → List Word) (fun _ => [])
    (fun word _ next bits =>
      let tail := next (bits >>> 1)
      if bits &&& 1 == 0 then tail else word :: tail) base token

def rootState (base : List Word) (fuel token : Nat) : RowState :=
  (fuel, rootWords base token, [])

def insertWord (w : Word) (ws : List Word) : List Word :=
  List.rec [w] (fun a tail next => if w ≤ a then w :: a :: tail else a :: next) ws

abbrev Bound := Nat × List Word × Nat × Word

def maskFlat (mask word : Nat) : Bool :=
  let v := word &&& mask
  v == 0 || v == mask

def flatCount (mask : Nat) (words : List Word) : Nat :=
  List.rec 0 (fun word _ count => if maskFlat mask word then count + 1 else count) words

def AvailableWord (mask : Nat) (bank : List Word) (word : Word) : Prop :=
  word = 0 ∨ word = mask ∨ word ∈ bank

theorem restrictWord (mask : Nat) (word : Word) : word &&& mask &&& mask = word &&& mask := by
  simp

def AgreesAt (i j : Nat) (word : Word) : Prop :=
  word.testBit i = word.testBit j

def properWord (mask word : Word) : Prop := word ≠ 0 ∧ word ≠ mask

def binWord (isOr : Bool) (a b : Word) : Word :=
  if isOr then a ||| b else a &&& b

variable {mask : Nat} {target : Word}

def wordRep (mask : Nat) (ws : List Word) (w : Word) : Prop :=
  w ∈ ws ∨ ¬properWord mask w

def Masked (mask word : Nat) : Prop := word &&& mask = word

theorem insertWordMem {x w : Word} {ws : List Word} :
    x ∈ insertWord w ws ↔ x = w ∨ x ∈ ws := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change x ∈ (if w ≤ a then w :: a :: tail else a :: insertWord w tail) ↔ _
    split <;> simp [ih, or_assoc, or_left_comm]

theorem insertWordNodup {w : Word} {ws : List Word} (nd : ws.Nodup) (fresh : w ∉ ws) :
    (insertWord w ws).Nodup := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change (if w ≤ a then w :: a :: tail else a :: insertWord w tail).Nodup
    split
    · exact List.nodup_cons.mpr ⟨fresh, nd⟩
    have hn := List.nodup_cons.mp nd
    have hnot : w ≠ a ∧ w ∉ tail := by simpa using fresh
    exact List.nodup_cons.mpr ⟨by simp [insertWordMem, hnot.1.symm, hn.1], ih hn.2 hnot.2⟩

theorem insertWordSet (w : Word) (ws : List Word) :
    (insertWord w ws).toFinset = insert w ws.toFinset := by
  ext x
  simp [insertWordMem]

theorem eraseWordSet {ws : List Word} (nd : ws.Nodup) (w : Word) :
    (ws.erase w).toFinset = ws.toFinset.erase w := by
  ext x
  simp [nd.mem_erase_iff, and_comm]

def keepWord (save : Bool) (w : Word) (ws : List Word) : List Word :=
  if save then ws else ws.erase w

theorem keepNodup {ws : List Word} (nd : ws.Nodup) (save : Bool) (w : Word) :
    (keepWord save w ws).Nodup := by
  cases save
  · exact nd.erase _
  · exact nd

theorem keepSubset (save : Bool) (w : Word) (ws : List Word) :
    ∀ v ∈ keepWord save w ws, v ∈ ws := by
  cases save
  · exact fun _ h => List.mem_of_mem_erase h
  · exact fun _ h => h

theorem keepSet {ws : List Word} (nd : ws.Nodup) {w : Word} {U : Finset Word}
    (eq : ws.toFinset = insert w U) :
    (keepWord (decide (w ∈ U)) w ws).toFinset = U := by
  by_cases hw : w ∈ U
  · simp [keepWord, hw, eq, Finset.insert_eq_of_mem hw]
  · simp [keepWord, hw, eraseWordSet nd, eq]

theorem keepPairSet {ws : List Word} (nd : ws.Nodup) {a b : Word} {U : Finset Word}
    (ab : a ≠ b) (eq : ws.toFinset = insert a (insert b U)) :
    (keepWord (decide (b ∈ U)) b (keepWord (decide (a ∈ U)) a ws)).toFinset = U := by
  have x : decide (a ∈ insert b U) = decide (a ∈ U) := by simp [ab]
  have h := keepSet nd eq
  rw [x] at h
  exact keepSet (keepNodup nd _ _) h

theorem getWord {ws : List Word} {x : Word} (h : x ∈ ws) :
    ws.getD (ws.idxOf x) 0 = x := by
  have inb := List.idxOf_lt_length_iff.mpr h
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inb] using
    List.getElem_idxOf inb

theorem rootWordSublist (base : List Word) (token : Nat) : (rootWords base token).Sublist base := by
  induction base generalizing token with
  | nil => exact List.Sublist.slnil
  | cons w ws ih =>
    change (if token &&& 1 == 0 then rootWords ws (token >>> 1)
      else w :: rootWords ws (token >>> 1)).Sublist (w :: ws)
    split
    · exact (ih _).cons _
    · exact (ih _).cons₂ _

theorem rootToken (base : List Word) (S : Finset Word) :
    ∃ token < 2 ^ base.length, (rootWords base token).toFinset = base.toFinset ∩ S := by
  induction base with
  | nil => exact ⟨0, by simp, by simp [rootWords]⟩
  | cons w ws ih =>
    obtain ⟨token, htoken, ih⟩ := ih
    let bit : Nat := if w ∈ S then 1 else 0
    have hbit : bit < 2 := by dsimp [bit]; split <;> decide
    let code := 2 * token + bit
    have low : code &&& 1 = bit := by
      rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      dsimp [code]
      omega
    have high : code >>> 1 = token := by
      rw [Nat.shiftRight_eq_div_pow]
      change code / 2 = token
      dsimp [code]
      omega
    refine ⟨code, ?_, ?_⟩
    · simp only [List.length_cons, pow_succ]
      dsimp [code]
      omega
    · change (if code &&& 1 == 0 then rootWords ws (code >>> 1)
        else w :: rootWords ws (code >>> 1)).toFinset = _
      rw [low, high]
      by_cases hw : w ∈ S
      · simp [bit, hw, ih]
      · simp [bit, hw, ih]

theorem positiveInMask {i : Nat} (mt : Masked mask target) (ht : target.testBit i = true) :
    mask.testBit i = true := by
  have h := congrArg (fun n : Nat => n.testBit i) mt
  simpa [Nat.testBit_and, ht] using h

variable {rows : Nat}

def fullMask (rows : Nat) : Nat := 2 ^ rows - 1

theorem notNat (v : BitVec rows) : (~~~v).toNat = fullMask rows ^^^ v.toNat := by
  rw [← BitVec.xor_allOnes, BitVec.toNat_xor, Nat.xor_comm, BitVec.toNat_allOnes]
  rfl

theorem toNatAvailable (bank : List (BitVec rows)) (i : Nat) :
    AvailableWord (fullMask rows) (bank.map BitVec.toNat) (bank.getD i 0).toNat := by
  rw [List.getD_eq_getElem?_getD]
  cases h : bank[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (Or.inr (List.mem_map_of_mem (List.mem_of_getElem? h)))

abbrev maskedFlat (m a : Word) : Prop := a &&& m = 0 ∨ a &&& m = m

def flatSet (m : Word) (s : Finset (Word)) := s.filter (maskedFlat m)

def visibleWords (m : Word) (s : Finset (Word)) := s.image fun w => w &&& m

theorem flIns {m a : Word} {s : Finset (Word)} (ha : a ∉ s) :
    (flatSet m (insert a s)).card = (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases f : maskedFlat m a <;> simp [flatSet,Finset.filter_insert,f,ha]

theorem flLe (m a : Word) (s : Finset (Word)) :
    (flatSet m (insert a s)).card ≤ (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases old : a ∈ s
  · rw [Finset.insert_eq_of_mem old]
    omega
  · rw [flIns old]

theorem prIns (m a : Word) (s : Finset (Word)) :
    visibleWords m (insert a s) = insert (a &&& m) (visibleWords m s) := Finset.image_insert ..

theorem cofNot {mask m : Nat} (sub : mask &&& m = m) (a : Word) :
    (mask ^^^ a) &&& m = m ^^^ (a &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h := congrArg (fun w : Nat => w.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at h ⊢
  cases he : m.testBit i
  · simp
  · have hm : mask.testBit i = true := by simpa [he] using h
    simp [hm]

theorem cofBinary (m a b : Word) (d : Bool) :
    binWord d a b &&& m = binWord d (a &&& m) (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases d <;> simp only [binWord, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and, Nat.testBit_or] <;>
    cases m.testBit i <;> simp

theorem flNot {mask m : Nat} (sub : mask &&& m = m) (a : Word) :
    maskedFlat m (mask ^^^ a) ↔ maskedFlat m a := by
  unfold maskedFlat
  rw [cofNot sub]
  constructor <;> intro h
  · rcases h with h | h
    · right
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
    · left
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
  · rcases h with h | h <;> simp [h]

def projectedStock (m : Word) (s : Finset (Word)) := insert 0 (insert m (visibleWords m s))

theorem flatCountCard (mask : Nat) {words : List Word} (nodup : words.Nodup) :
    flatCount mask words = (flatSet mask words.toFinset).card := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    have nd := List.nodup_cons.mp nodup
    have fresh : w ∉ ws.toFinset := by simpa using nd.1
    have bool : maskFlat mask w = true ↔ maskedFlat mask w := by
      simp [maskFlat, maskedFlat]
    change (if maskFlat mask w then flatCount mask ws + 1 else flatCount mask ws) = _
    rw [List.toFinset_cons, flIns fresh, ih nd.2]
    by_cases h : maskedFlat mask w
    · simp [h, bool.mpr h]
    · have no : maskFlat mask w = false := Bool.eq_false_iff.mpr (fun ht => h (bool.mp ht))
      simp [h, no]

abbrev PointWire (rows : Nat) := Fin rows → Bool

def encodePoint (f : PointWire rows) : BitVec rows :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem encodeBit (f : PointWire rows) (i : Fin rows) :
    (encodePoint f).getLsbD i.val = f i := by
  simp only [encodePoint, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

theorem encodeAnd (a b : PointWire rows) :
    encodePoint (fun i => a i && b i) = encodePoint a &&& encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]

theorem encodeOr (a b : PointWire rows) :
    encodePoint (fun i => a i || b i) = encodePoint a ||| encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]

def pointWord (f : PointWire rows) : Word := (encodePoint f).toNat

def relabel (sourceIndex : Fin rows → Fin rows) (word : Word) : Word :=
  pointWord fun i => word.testBit (sourceIndex i).val

theorem pointZero : pointWord (fun _ : Fin rows => false) = 0 := by
  have eq : encodePoint (fun _ : Fin rows => false) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp
  simp [pointWord, eq]

theorem relabelZero (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex 0 = 0 := by
  simpa [relabel] using (pointZero (rows := rows))

theorem relabelAnd (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a &&& b) = relabel sourceIndex a &&& relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_and, pointWord, encodeAnd, BitVec.toNat_and]

theorem relabelOr (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a ||| b) = relabel sourceIndex a ||| relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_or, pointWord, encodeOr, BitVec.toNat_or]

theorem relabelXor (sourceIndex : Fin rows → Fin rows) (a b : Word) :
    relabel sourceIndex (a ^^^ b) = relabel sourceIndex a ^^^ relabel sourceIndex b := by
  have eq : encodePoint (fun i => (a ^^^ b).testBit (sourceIndex i).val) =
      encodePoint (fun i => a.testBit (sourceIndex i).val) ^^^
      encodePoint (fun i => b.testBit (sourceIndex i).val) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_xor, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
    exact Nat.testBit_xor ..
  simpa only [relabel, pointWord, BitVec.toNat_xor] using congrArg BitVec.toNat eq

theorem relabelBit (sourceIndex : Fin rows → Fin rows) (word : Word) (i : Fin rows) :
    (relabel sourceIndex word).testBit i.val = word.testBit (sourceIndex i).val :=
  encodeBit _ i

theorem relabelOutside (sourceIndex : Fin rows → Fin rows) (word i : Word) (h : rows ≤ i) :
    (relabel sourceIndex word).testBit i = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le (show (encodePoint _).toNat < 2 ^ rows from BitVec.isLt _)
    (Nat.pow_le_pow_right (by decide) h)

theorem relabelInj (sourceIndex : Fin rows → Fin rows) (onto : Function.Surjective sourceIndex)
    {a b : Word} (ba : Masked (fullMask rows) a) (bb : Masked (fullMask rows) b)
    (eq : relabel sourceIndex a = relabel sourceIndex b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · obtain ⟨j, h⟩ := onto ⟨i, inside⟩
    have bit := congrArg (fun w : Nat => w.testBit j.val) eq
    simpa only [relabelBit, h] using bit
  · have ea := congrArg (fun w : Nat => w.testBit i) ba
    have eb := congrArg (fun w : Nat => w.testBit i) bb
    simp only [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, inside, decide_false,
      Bool.and_false] at ea eb
    rw [← ea, ← eb]

namespace PackedRect

def full : ℕ := 2 ^ 144 - 1

end PackedRect

abbrev Witness := Word × Nat × Nat

def witnessWord (w : Witness) : Word := w.1

def essentialB (mask target : Word) (stock : List Word) (entry : Witness) : Bool :=
  let (w,p,n) := entry
  mask.testBit p && mask.testBit n && target.testBit p && !target.testBit n &&
    (w.testBit p != w.testBit n) &&
    stock.all (fun x => x == w || x.testBit p == x.testBit n)

def unpackWitnesses (stock : List Word) (codes : List Nat) : List Witness :=
  List.rec [] (fun code _ rest =>
    (stock.getD (code >>> 18) 0, (code >>> 9) &&& 511, code &&& 511) :: rest) codes

def DagAuto (mask goal : Word) (select : Fin rows → Fin rows) : Prop :=
  Function.Surjective select ∧ relabel select mask = mask ∧ relabel select goal = goal

abbrev WordMoveStep := List (Word × Nat) × List (Word × Nat)

abbrev WordMove := List WordMoveStep

def mixStep (m : WordMoveStep) (w : Word) : Word :=
  let left := List.rec 0 (fun (part,n) _ acc => ((w &&& part) <<< n) ||| acc) m.1
  let right := List.rec 0 (fun (part,n) _ acc => ((w &&& part) >>> n) ||| acc) m.2
  left ||| right

def BitLinear (f : Word → Word) : Prop :=
  ∀ w i, (f w).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (2 ^ j)).testBit i = true

theorem bitLinearZero : BitLinear (fun _ => 0) := by
  simp [BitLinear]

theorem bitLinearOr {f g : Word → Word} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f w ||| g w) := by
  intro w i
  change ((f w ||| g w).testBit i = true) ↔ _
  simp only [Nat.testBit_or, Bool.or_eq_true]
  rw [hf w i, hg w i]
  constructor
  · rintro (⟨j,hw,hj⟩ | ⟨j,hw,hj⟩)
    · exact ⟨j,hw,Or.inl hj⟩
    · exact ⟨j,hw,Or.inr hj⟩
  · rintro ⟨j,hw,hj | hj⟩
    · exact Or.inl ⟨j,hw,hj⟩
    · exact Or.inr ⟨j,hw,hj⟩

theorem bitLinearLeft (mask n : Nat) : BitLinear (fun w => (w &&& mask) <<< n) := by
  intro w i
  simp only [Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hw, hm⟩
    exact ⟨i-n,hw,h,rfl,hm⟩
  · rintro ⟨j,hw,h,rfl,hm⟩
    exact ⟨h,hw,hm⟩

theorem bitLinearRight (mask n : Nat) : BitLinear (fun w => (w &&& mask) >>> n) := by
  intro w i
  simp only [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hw,hm⟩
    exact ⟨n+i,hw,rfl,hm⟩
  · rintro ⟨j,hw,rfl,hm⟩
    exact ⟨hw,hm⟩

theorem mixStepLinear (move : WordMoveStep) : BitLinear (mixStep move) := by
  obtain ⟨left, right⟩ := move
  unfold mixStep
  apply bitLinearOr
  · induction left with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearLeft part count) ih
  · induction right with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearRight part count) ih

def mixMove (move : WordMove) (w : Word) : Word :=
  (List.rec (motive := fun _ => Word → Word) id
    (fun step _ next w => next (mixStep step w)) move) w

theorem bitLinearId : BitLinear id := by
  intro w i
  change w.testBit i = true ↔ ∃ j, w.testBit j = true ∧ (2 ^ j).testBit i = true
  simp [Nat.testBit_two_pow]

theorem bitLinearComp {f g : Word → Word} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f (g w)) := by
  intro w i
  change (f (g w)).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (g (2 ^ j))).testBit i = true
  rw [hf]
  constructor
  · rintro ⟨j,gj,fj⟩
    obtain ⟨k,wk,gk⟩ := (hg w j).mp gj
    exact ⟨k,wk,(hf (g (2^k)) i).mpr ⟨j,gk,fj⟩⟩
  · rintro ⟨j,wj,h⟩
    obtain ⟨k,gk,fk⟩ := (hf (g (2^j)) i).mp h
    exact ⟨k,(hg w k).mpr ⟨j,wj,gk⟩,fk⟩

theorem mixMoveLinear (move : WordMove) : BitLinear (mixMove move) := by
  induction move with
  | nil => exact bitLinearId
  | cons op ops ih =>
    change BitLinear (fun w => mixMove ops (mixStep op w))
    exact bitLinearComp ih (mixStepLinear op)

def permuteAxes (axes : List Nat) (offset row : Nat) : Nat :=
  offset ^^^ (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun j _ next i => (if row.testBit i then 1 <<< j else 0) ||| next (i + 1)) axes) 0

theorem relabelLinear (select : Fin rows → Fin rows) : BitLinear (relabel select) := by
  intro w i
  by_cases inside : i < rows
  · let ii : Fin rows := ⟨i,inside⟩
    change (relabel select w).testBit ii.val = true ↔ _
    rw [relabelBit]
    constructor
    · intro h
      refine ⟨(select ii).val,h,?_⟩
      change (relabel select (2 ^ (select ii).val)).testBit ii.val = true
      rw [relabelBit, Nat.testBit_two_pow]
      simp
    · rintro ⟨j,h,bit⟩
      change (relabel select (2^j)).testBit ii.val = true at bit
      rw [relabelBit, Nat.testBit_two_pow, decide_eq_true_eq] at bit
      exact bit ▸ h
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]
    simp [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]

theorem wordMoveAgreement {select : Fin rows → Fin rows} {mask : Word} {move : WordMove}
    (bounded : Masked (fullMask rows) mask)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = relabel select (2 ^ i.val))
    {w : Word} (masked : Masked mask w) : mixMove move w = relabel select w := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [mixMoveLinear, relabelLinear]
  have source {j : Nat} (bit : w.testBit j = true) :
      mixMove move (2^j) = relabel select (2^j) := by
    have m : mask.testBit j = true := by
      have eq := congrArg (fun x : Nat => x.testBit j) masked
      simpa [Nat.testBit_and, bit] using eq
    have within : j < rows := by
      have eq := congrArg (fun x : Nat => x.testBit j) bounded
      simpa [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, m] using eq
    exact basis ⟨j,within⟩ m
  constructor <;> rintro ⟨j,hj,hi⟩
  · exact ⟨j,hj,by rwa [← source hj]⟩
  · exact ⟨j,hj,by rwa [source hj]⟩

theorem relabelBasis {select inverse : Fin rows → Fin rows}
    (left : ∀ i, inverse (select i) = i) :
    ∀ j : Fin rows, select (inverse j) = j →
      relabel select (2 ^ j.val) = 2 ^ (inverse j).val := by
  intro j right
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · let pos : Fin rows := ⟨i,inside⟩
    change (relabel select (2 ^ j.val)).testBit pos.val = _
    rw [relabelBit, Nat.testBit_two_pow, Nat.testBit_two_pow]
    apply (Bool.eq_iff_iff).mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro eq
      have e : j = select pos := Fin.ext eq
      rw [e,left]
    · intro eq
      have hp : inverse j = pos := Fin.ext eq
      rw [← hp, right]
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside), Nat.testBit_two_pow]
    have ne : (inverse j).val ≠ i := by have := (inverse j).isLt; omega
    simp [ne]

theorem dagAutoFromMove {select inverse : Fin rows → Fin rows} {mask goal : Word} {move : WordMove}
    (left : ∀ i, inverse (select i) = i)
    (right : ∀ i, select (inverse i) = i)
    (bm : Masked (fullMask rows) mask)
    (gm : Masked mask goal)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val)
    (sameMask : mixMove move mask = mask) (sameGoal : mixMove move goal = goal) :
    DagAuto mask goal select ∧ ∀ w, Masked mask w → mixMove move w = relabel select w := by
  have agree {w : Word} (hw : Masked mask w) : mixMove move w = relabel select w :=
    wordMoveAgreement bm (fun i h => (basis i h).trans (relabelBasis left i (right i)).symm) hw
  exact ⟨⟨fun i => ⟨inverse i,right i⟩,(agree (by simp [Masked])).symm.trans sameMask,
    (agree gm).symm.trans sameGoal⟩,fun _ h => agree h⟩

theorem maskedBelow {mask w : Word} (bm : Masked (fullMask rows) mask)
    (bw : Masked mask w) : Masked (fullMask rows) w := by
  unfold Masked at *
  rw [← bw, Nat.land_assoc, bm, bw]

theorem maskedTransfer {mask w : Word} {select : Fin rows → Fin rows}
    (same : relabel select mask = mask) (hw : Masked mask w) :
    Masked mask (relabel select w) := by
  unfold Masked at *
  rw [← same, ← relabelAnd, hw]

def dagForceWord {α : Type} (word : Word) (cont : Word → α) : α :=
  Nat.rec (cont 0) (fun k _ => cont (k + 1)) word

theorem dagForceWordEq {α : Type} (word : Word) (cont : Word → α) :
    dagForceWord word cont = cont word := by cases word <;> rfl

def dagForceWords (words : List Word) (cont : List Word → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Word → Bool) → Bool) (fun k => k [])
    (fun w _ next k => dagForceWord w (fun v => next (fun rest => k (v :: rest)))) words) cont

theorem dagForceWordsEq (words : List Word) (cont : List Word → Bool) :
    dagForceWords words cont = cont words := by
  induction words generalizing cont with
  | nil => rfl
  | cons w ws ih =>
    change dagForceWord w (fun v => dagForceWords ws (fun rest => cont (v :: rest))) = _
    rw [dagForceWordEq, ih]

abbrev DagLink := Nat × Nat

abbrev DagLinks := Nat → Nat → Option DagLink

def dagPartition (directed : Bool) (ws : List Word) : Word → Word → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      Nat.beq p 0 || Nat.beq n 0 ||
      dagForceWord (p &&& w) (fun up =>
        dagForceWord (n &&& w) (fun down =>
          rest up down &&
            dagForceWord (p ^^^ up) (fun offP =>
              dagForceWord (if directed then n else n ^^^ down) (rest offP))))) ws

theorem dagOffBits {v w : Word} {i : Nat} (bit : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at bit
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at bit ⊢

theorem dagPartitionSound {directed : Bool} {ws : List Word} {positive negative : Word}
    (fail : dagPartition directed ws positive negative = false) :
    ∃ p n, positive.testBit p = true ∧ negative.testBit n = true ∧
      ∀ w ∈ ws, if directed then w.testBit p = true → w.testBit n = true
                  else w.testBit p = w.testBit n := by
  have nonempty {w : Word} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all
    apply hn
    apply Nat.eq_of_testBit_eq
    intro i
    simp [all i]
  induction ws generalizing positive negative with
  | nil =>
    change (Nat.beq positive 0 || Nat.beq negative 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p,hp⟩ := nonempty (w := positive) (fun eq => by simp [eq] at fail)
    obtain ⟨n,hn⟩ := nonempty (w := negative) (fun eq => by simp [eq] at fail)
    exact ⟨p,n,hp,hn,by simp⟩
  | cons w ws ih =>
    change (Nat.beq positive 0 || Nat.beq negative 0 ||
      dagForceWord (positive &&& w) (fun up =>
        dagForceWord (negative &&& w) (fun down =>
          dagPartition directed ws up down &&
            dagForceWord (positive ^^^ up) (fun offP =>
              dagForceWord (if directed then negative else negative ^^^ down)
                (dagPartition directed ws offP))))) = false at fail
    simp only [dagForceWordEq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p,n,hp,hn,agree⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p,n,hp.1,hn.1,?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | tail
      · simp [hp.2, hn.2]
      · exact agree _ tail
    · obtain ⟨p,n,hp,hn,agree⟩ := ih off
      have hp' := dagOffBits hp
      cases mode : directed
      · have hn' : negative.testBit n = true ∧ w.testBit n = false := by
          apply dagOffBits
          simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn'.1,?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2, hn'.2]
        · simpa [mode] using agree _ tail
      · have hn' : negative.testBit n = true := by simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn',?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2]
        · simpa [mode] using agree _ tail

abbrev DagSample := Nat × Nat

abbrev DagSignals := Word × Word

abbrev DagCounts := Word × Word × Word

def dagForceCache (tags : List DagSignals) (use : List DagSignals → Bool) : Bool :=
  (List.rec (motive := fun _ => (List DagSignals → Bool) → Bool) (fun k => k [])
    (fun tag _ next k =>
      dagForceWord tag.1 (fun up => dagForceWord tag.2 (fun down =>
        next (fun tail => k ((up,down)::tail))))) tags) use

theorem dagForceCacheEq (tags : List DagSignals) (use : List DagSignals → Bool) :
    dagForceCache tags use = use tags := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag rest ih =>
    obtain ⟨a,b⟩ := tag
    change dagForceWord a (fun up => dagForceWord b (fun down =>
      dagForceCache rest (fun tail => use ((up,down)::tail)))) = _
    simp only [dagForceWordEq, ih]

def dagSignalContrast (directed : Bool) (full : Word) (tag : DagSignals) : Word :=
  if directed then tag.1 &&& (tag.2 ^^^ full) else tag.1 ^^^ tag.2

def dagCountStep (acc : DagCounts) (column : Word) : DagCounts :=
  (acc.1 ||| column, acc.2.1 ||| (acc.1 &&& column), acc.2.2 ||| (acc.2.1 &&& column))

def dagCountSigns (directed : Bool) (full : Word) (tags : List DagSignals)
    (use : DagCounts → Bool) : Bool :=
  (List.rec (motive := fun _ => (DagCounts → Bool) → Bool) (fun k => k (0,0,0))
    (fun tag _ more k =>
      dagForceWord (dagSignalContrast directed full tag) (fun column =>
        more (fun acc =>
          dagForceWord (acc.1 ||| column) (fun once =>
            dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
              dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => k (once,twice,thrice)))))))
    tags) use

theorem dagCountSignsEq (directed : Bool) (full : Word) (tags : List DagSignals)
    (use : DagCounts → Bool) : dagCountSigns directed full tags use =
    use (tags.foldr (fun tag acc => dagCountStep acc (dagSignalContrast directed full tag)) (0,0,0)) := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag tags ih =>
    change dagForceWord (dagSignalContrast directed full tag) (fun column =>
      dagCountSigns directed full tags (fun acc =>
        dagForceWord (acc.1 ||| column) (fun once =>
          dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
            dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => use (once,twice,thrice)))))) = _
    simp only [dagForceWordEq, ih]
    rfl

def dagPairReject (mask goal : Word) (directed : Bool) (ws : List Word) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    let p := code &&& 511
    let n := code >>> 9
    goal.testBit p && mask.testBit n && !goal.testBit n &&
      ws.all (fun w => if directed then !(w.testBit p) || w.testBit n
                       else w.testBit p == w.testBit n)

abbrev DagTagged := Word × DagSignals

def dagTagBases (stock : List Word) (positive negative width : Nat) : List DagTagged :=
  (List.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun w _ next i => (w, unpack positive width i, unpack negative width i) :: next (i+1)) stock) 0

def dagTagRoot (bank : List DagTagged) (token : Nat) : List DagTagged :=
  (List.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun tag _ next k =>
      if Nat.beq (k &&& 1) 0 then next (k >>> 1) else tag :: next (k >>> 1)) bank) token

def dagTagKeep (keep : Bool) (w : Word) (bank : List DagTagged) : List DagTagged :=
  if keep then bank
  else List.rec [] (fun tag tail next => if Nat.beq tag.1 w then tail else tag :: next) bank

def dagTagInsert (tag : DagTagged) (bank : List DagTagged) : List DagTagged :=
  List.rec [tag] (fun old tail next => if Nat.ble tag.1 old.1 then tag :: old :: tail else old :: next) bank

def dagStateOK (mask : Word) (ws : List Word) : Bool :=
  (ws.dedup.length == ws.length) && ws.all (fun w => w &&& mask == w)

theorem dagStateOKSpec {mask : Word} {ws : List Word} (ok : dagStateOK mask ws = true) :
    ws.Nodup ∧ ∀ w ∈ ws, Masked mask w := by
  simp only [dagStateOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  exact ⟨List.nodup_iff_length_dedup_eq.mpr ok.1, ok.2⟩

theorem dagInsertLength (w : Word) (ws : List Word) :
    (insertWord w ws).length = ws.length + 1 := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change (if w ≤ a then w :: a :: ws else a :: insertWord w ws).length = _
    split <;> simp [ih]

theorem dagKeepLength (keep : Bool) (w : Word) (ws : List Word) :
    ws.length - (if keep then 0 else 1) ≤ (keepWord keep w ws).length := by
  cases keep
  · exact List.le_length_erase
  · simp [keepWord]

theorem dagKeepMem {ws : List Word} {x w : Word} {keep : Bool}
    (nd : ws.Nodup) (h : w ∈ keepWord keep x ws) : w ∈ ws ∧ (keep = true ∨ w ≠ x) := by
  cases keep
  · simpa [keepWord, nd.mem_erase_iff, and_comm] using h
  · simpa [keepWord] using h

theorem dagKeepNodup {ws : List Word} (nd : ws.Nodup) (keep : Bool) (x : Word) :
    (keepWord keep x ws).Nodup := by
  cases keep
  · exact nd.erase x
  · exact nd

theorem readWordMasked {mask : Word} {ws : List Word}
    (all : ∀ w ∈ ws, Masked mask w) (i : Nat) : Masked mask (ws.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => simp [Masked]
  | some w => exact all w (List.mem_of_getElem? h)

def DagMovesOK (mask goal : Word) (width : Nat) (moves : Array WordMove) : Prop :=
  ∀ (i : Nat) (m : WordMove), moves[i]? = some m →
    ∃ select : Fin width → Fin width, DagAuto mask goal select ∧
      ∀ w, Masked mask w → mixMove m w = relabel select w

abbrev DagMoveRecord (width : Nat) := WordMove × (Fin width → Fin width) × (Fin width → Fin width)

def dagMoves (cert : List (DagMoveRecord width)) : Array WordMove := (cert.map Prod.fst).toArray

def dagMoveRecordProps {width : Nat} (mask goal : Word) (entry : DagMoveRecord width) : Prop :=
  let (move, select, inverse) := entry
  (∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal

def dagMoveRecordOK {width : Nat} (mask goal : Word) (entry : DagMoveRecord width) : Bool :=
  let (move, select, inverse) := entry
  decide ((∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal)

theorem dagMoveRecordSpec {width : Nat} {mask goal : Word} {entry : DagMoveRecord width}
    (ok : dagMoveRecordOK mask goal entry = true) : dagMoveRecordProps mask goal entry := by
  rcases entry with ⟨move,select,inverse⟩
  unfold dagMoveRecordProps
  exact of_decide_eq_true ok

theorem dagMovesOfCheck {width : Nat} {mask goal : Word} {cert : List (DagMoveRecord width)}
    (ok : cert.all (dagMoveRecordOK mask goal) = true) :
    DagMovesOK mask goal width (dagMoves cert) := by
  intro i m get
  simp only [dagMoves, List.getElem?_toArray, List.getElem?_map] at get
  cases e : cert[i]? with
  | none => simp [e] at get
  | some entry =>
    have eq : entry.1 = m := by simpa [e] using get
    rcases entry with ⟨move,select,inverse⟩
    obtain ⟨left,right,bm,gm,basis,mm,mg⟩ :=
      dagMoveRecordSpec (List.all_eq_true.mp ok _ (List.mem_of_getElem? e))
    subst m
    exact ⟨select, dagAutoFromMove left right bm gm basis mm mg⟩

def projectDAGStock (mask : Word) (source : List Word) (indices : List Nat) : List Word :=
  List.rec [] (fun i _ rest => (mask &&& source.getD i 0) :: rest) indices

theorem stockMaskedOfCheck {mask : Word} {stock : List Word}
    (h : stock.all (fun w => w &&& mask == w) = true) :
    ∀ w ∈ stock, Masked mask w := by
  intro w hw
  exact beq_iff_eq.mp (List.all_eq_true.mp h w hw)

def dagShift (mask : Word) (move : WordMove) (word : Word) : Word :=
  mixMove move (word &&& mask)

def dagShiftUnique (mask : Word) (move : WordMove) : Nat → Word → Bool :=
  Nat.rec (fun _ => true) (fun i next occupied =>
    if mask.testBit i then
      dagForceWord (mixMove move (2^i)) (fun col =>
        Nat.beq (col &&& occupied) 0 && dagForceWord (occupied ||| col) next)
    else next occupied)

theorem dagShiftLinear (mask : Word) (move : WordMove) : BitLinear (dagShift mask move) := by
  apply bitLinearComp (mixMoveLinear move)
  simpa using bitLinearRight mask 0

theorem dagShiftBasis (mask : Word) (move : WordMove) (i : Nat) :
    dagShift mask move (2 ^ i) = if mask.testBit i then mixMove move (2^i) else 0 := by
  have select : 2 ^ i &&& mask = if mask.testBit i then 2^i else 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases same : i = j
    · subst j
      simp only [Nat.testBit_and, Nat.testBit_two_pow, decide_true, Bool.true_and]
      cases mask.testBit i <;> simp
    · cases h : mask.testBit i <;> simp [Nat.testBit_and, Nat.testBit_two_pow, same, h]
  rw [dagShift, select]
  split
  · rfl
  · apply Nat.eq_of_testBit_eq
    intro j
    apply Bool.eq_iff_iff.mpr
    rw [mixMoveLinear]
    simp

theorem dagShiftUniqueSpec {mask : Word} {move : WordMove} {n : Nat} {occupied : Word}
    (ok : dagShiftUnique mask move n occupied = true) :
    (∀ j < n, ∀ b, (dagShift mask move (2^j)).testBit b = true → occupied.testBit b = false) ∧
    (∀ j < n, ∀ k < n, ∀ b, (dagShift mask move (2^j)).testBit b = true →
      (dagShift mask move (2^k)).testBit b = true → j = k) := by
  induction n generalizing occupied with
  | zero => simp
  | succ n ih =>
    let col := mixMove move (2^n)
    change (if mask.testBit n then dagForceWord col (fun w =>
      Nat.beq (w &&& occupied) 0 && dagForceWord (occupied ||| w) (dagShiftUnique mask move n))
      else dagShiftUnique mask move n occupied) = true at ok
    cases active : mask.testBit n
    · simp [active,dagForceWordEq] at ok
      obtain ⟨existing,unique⟩ := ih ok
      have dead : dagShift mask move (2^n) = 0 := by simp [dagShiftBasis,active]
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · simp [same,dead] at h
        · exact existing j (by omega) b h
      · intro j hj k hk b a c
        by_cases e : j = n
        · simp [e,dead] at a
        by_cases e' : k = n
        · simp [e',dead] at c
        exact unique j (by omega) k (by omega) b a c
    · simp only [active,ite_true,dagForceWordEq,Bool.and_eq_true] at ok
      have disjoint := Nat.beq_eq.mp ok.1
      obtain ⟨existing,unique⟩ := ih ok.2
      have colEq : dagShift mask move (2^n) = col := by simp [dagShiftBasis,active,col]
      have old {j b : Nat} (hj : j < n) (h : (dagShift mask move (2^j)).testBit b = true) :
          occupied.testBit b = false ∧ col.testBit b = false := by
        simpa [Nat.testBit_or, Bool.or_eq_false_iff] using existing j hj b h
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · rw [same,colEq] at h
          have bit := congrArg (fun w => Nat.testBit w b) disjoint
          simpa [Nat.testBit_and,h] using bit
        · exact (old (by omega) h).1
      · intro j hj k hk b a c
        by_cases e : j = n
        · by_cases e' : k = n
          · exact e.trans e'.symm
          · rw [e,colEq,(old (by omega) c).2] at a
            contradiction
        by_cases e' : k = n
        · rw [e',colEq,(old (by omega) a).2] at c
          contradiction
        exact unique j (by omega) k (by omega) b a c

theorem dagShiftGates {mask : Word} {move : WordMove} {width : Nat}
    (bounded : Masked (fullMask width) mask) (checked : dagShiftUnique mask move width 0 = true) :
    (∀ a b, dagShift mask move (a &&& b) = dagShift mask move a &&& dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ||| b) = dagShift mask move a ||| dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ^^^ b) = dagShift mask move a ^^^ dagShift mask move b) := by
  let f := dagShift mask move
  have lin := dagShiftLinear mask move
  have uniq {j k i : Nat} (hj : (f (2^j)).testBit i = true) (hk : (f (2^k)).testBit i = true) : j = k := by
    have within {m : Nat} (a : (f (2^m)).testBit i = true) : m < width := by
      by_contra! big
      have eq := congrArg (fun w => Nat.testBit w m) bounded
      have zero : mask.testBit m = false := by
        simpa [Masked,fullMask,Nat.testBit_and,Nat.testBit_two_pow_sub_one,show ¬m < width by omega] using eq.symm
      simp [f,dagShiftBasis,zero] at a
    exact (dagShiftUniqueSpec checked).2 j (within hj) k (within hk) i hj hk
  refine ⟨?_,?_,?_⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [Nat.testBit_and, Bool.and_eq_true, lin, lin, lin]
    constructor
    · rintro ⟨j,hj,h⟩
      rw [Nat.testBit_and, Bool.and_eq_true] at hj
      exact ⟨⟨j,hj.1,h⟩,⟨j,hj.2,h⟩⟩
    · rintro ⟨⟨j,hj,q⟩,⟨k,hk,r⟩⟩
      have same := uniq q r
      subst k
      exact ⟨j,by simp [Nat.testBit_and,hj,hk],q⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [lin (a ||| b) i, Nat.testBit_or, Bool.or_eq_true, lin a i, lin b i]
    simp only [Nat.testBit_or, Bool.or_eq_true]
    constructor
    · rintro ⟨j,(left | right),same⟩
      · exact Or.inl ⟨j,left,same⟩
      · exact Or.inr ⟨j,right,same⟩
    · rintro (⟨j,left,same⟩ | ⟨j,right,same⟩)
      · exact ⟨j,Or.inl left,same⟩
      · exact ⟨j,Or.inr right,same⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    have l := lin a i
    have r := lin b i
    have v := lin (a ^^^ b) i
    cases pa : (f a).testBit i <;> cases pb : (f b).testBit i
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      have disj : a.testBit j = true ∨ b.testBit j = true := by
        rw [Nat.testBit_xor] at hj
        cases aj : a.testBit j <;> cases bj : b.testBit j <;> simp [aj,bj] at hj ⊢
      rcases disj with da | db
      · have := l.mpr ⟨j,da,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this
      · have := r.mpr ⟨j,db,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := r.mp pb
      have notA : a.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := l.mpr ⟨j,yes,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this)
      exact ⟨j,by simp [Nat.testBit_xor,notA,hj],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := l.mp pa
      have notB : b.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := r.mpr ⟨j,yes,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this)
      exact ⟨j,by simp [Nat.testBit_xor,hj,notB],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      obtain ⟨a',ha,q⟩ := l.mp pa
      obtain ⟨b',hb,r⟩ := r.mp pb
      have ea := uniq h q
      have eb := uniq h r
      rw [← ea] at ha
      rw [← eb] at hb
      simp [Nat.testBit_xor,ha,hb] at hj

def hcsGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0

def hcsStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [hcsGateVal bank g]

theorem hcsGetDBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp

theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]

theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]

theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]

theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]

def hcsCheckPow (p : Nat → Bool) : Nat → Nat → Bool
  | 0, s => p s
  | k + 1, s => hcsCheckPow p k s && hcsCheckPow p k (s + 2 ^ k)

theorem hcsCheckPow_spec {p : Nat → Bool} {k s i : Nat}
    (h : hcsCheckPow p k s = true) (lo : s ≤ i) (hi : i < s + 2 ^ k) : p i = true := by
  induction k generalizing s with
  | zero =>
    have e : i = s := by omega
    simpa [hcsCheckPow, e] using h
  | succ k ih =>
    simp only [hcsCheckPow, Bool.and_eq_true] at h
    by_cases hlt : i < s + 2 ^ k
    · exact ih h.1 lo hlt
    · exact ih h.2 (by omega) (by rw [Nat.pow_succ] at hi; omega)

def GateWordMono (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  ∃ a b, AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b)

theorem gateMonoOfAvailable {mask : Nat} {bank : List Word} {w : Word}
    (av : AvailableWord mask bank w) : GateWordMono mask bank w :=
  ⟨w, 0, av, Or.inl rfl, Or.inr (by simp)⟩

def maskFlatF (mask word : Word) : Bool :=
  dagForceWord (word &&& mask) (fun v => v == 0 || v == mask)

theorem maskFlatF_eq (mask word : Word) : maskFlatF mask word = maskFlat mask word := by
  simp [maskFlatF, maskFlat, dagForceWordEq]

def flatCountF (mask : Word) (words : List Word) : Nat :=
  List.rec 0 (fun word _ count => if maskFlatF mask word then count + 1 else count) words

theorem flatCountF_eq (mask : Word) (words : List Word) : flatCountF mask words = flatCount mask words := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    change (if maskFlatF mask w then flatCountF mask ws + 1 else flatCountF mask ws) =
      (if maskFlat mask w then flatCount mask ws + 1 else flatCount mask ws)
    rw [maskFlatF_eq, ih]

def dagBoundHeaderOK (target : Word) (bound : Bound) : Bool :=
  let (mask, _, _, goal) := bound
  (target &&& mask) == goal && goal != 0 && goal != mask

abbrev DagLinkList := Nat → List (Nat × Nat × Nat)

def dagUnpackLinksGo (data width tokenBits destBits tokMask destMask : Nat) : Nat → Nat → List (Nat × Nat × Nat)
  | 0, _ => []
  | n + 1, pos =>
      dagForceWord (unpack data width pos) (fun code =>
        dagForceWord (code &&& tokMask) (fun tk =>
          dagForceWord ((code >>> tokenBits) &&& destMask) (fun ds =>
            dagForceWord (code >>> (tokenBits + destBits)) (fun au =>
              (tk, ds, au) :: dagUnpackLinksGo data width tokenBits destBits tokMask destMask n (pos + 1)))))

def dagExtractLinks (index data indexWidth sizeBits tokenBits destBits autoBits : Nat) : DagLinkList :=
  fun parent =>
    dagForceWord (unpack index indexWidth parent) (fun entry =>
      dagForceWord (entry &&& fullMask sizeBits) (fun size =>
        dagForceWord (entry >>> sizeBits) (fun offset =>
          dagUnpackLinksGo data (tokenBits + destBits + autoBits) tokenBits destBits
            (fullMask tokenBits) (fullMask destBits) size offset)))

def dagFindLink : List (Nat × Nat × Nat) → Nat → Option DagLink
  | [], _ => none
  | (tk, ds, au) :: rest, token =>
      if Nat.beq tk token then some (ds, au) else dagFindLink rest token

def dagForceLinkList (ls : List (Nat × Nat × Nat)) (cont : List (Nat × Nat × Nat) → Bool) : Bool :=
  (List.rec (motive := fun _ => (List (Nat × Nat × Nat) → Bool) → Bool) (fun k => k [])
    (fun e _ next k =>
      dagForceWord e.1 (fun tk =>
        dagForceWord e.2.1 (fun ds =>
          dagForceWord e.2.2 (fun au =>
            next (fun rest => k ((tk, ds, au) :: rest)))))) ls) cont

theorem dagForceLinkListEq (ls : List (Nat × Nat × Nat)) (cont : List (Nat × Nat × Nat) → Bool) :
    dagForceLinkList ls cont = cont ls := by
  induction ls generalizing cont with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨tk, ds, au⟩ := e
    change dagForceWord tk (fun tk' => dagForceWord ds (fun ds' => dagForceWord au (fun au' =>
      dagForceLinkList es (fun rest => cont ((tk', ds', au') :: rest))))) = _
    rw [dagForceWordEq, dagForceWordEq, dagForceWordEq, ih]

def dagHighest7 (value : Word) : Nat :=
  (Nat.rec (motive := fun _ => Word → Nat → Nat) (fun _ offset => offset)
    (fun i next w offset =>
      let shift := 1 <<< i
      dagForceWord (w >>> shift) (fun upper =>
        if Nat.beq upper 0 then next w offset else next upper (offset + shift))) 7) value 0

def dagSamplePairOK (mask goal : Word) (code : Nat) : Bool :=
  let p := code &&& 511
  let n := code >>> 9
  goal.testBit p && mask.testBit n && !goal.testBit n && Nat.blt p 256 && Nat.blt n 256

def dagSampleValid (mask goal : Word) (sample : DagSample) : Bool :=
  treeBlock 0 sample.2 (fun k => dagSamplePairOK mask goal (unpack sample.1 18 k))

def dagPackWords256 (ws : List Word) : Word :=
  List.rec 0 (fun w _ tail => (w &&& fullMask 256) ||| (tail <<< 256)) ws

def dagLaneMarks256 (n : Nat) : Word :=
  Nat.rec 0 (fun _ more => 1 ||| (more <<< 256)) n

def dagOmitted256 (aBit bBit : Word) (left right : Bool) : Word :=
  (if left then 0 else aBit) ||| (if right then 0 else bBit)

theorem dagPackBits256 {ws : List Word} {i row : Nat} (inside : i < ws.length) (width : row < 256) :
    (dagPackWords256 ws).testBit (256 * i + row) = (ws.getD i 0).testBit row := by
  induction ws generalizing i with
  | nil => simp at inside
  | cons w ws ih =>
    change ((w &&& fullMask 256) ||| (dagPackWords256 ws <<< 256)).testBit (256 * i + row) = _
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft]
    cases i with
    | zero =>
      rw [fullMask, Nat.testBit_two_pow_sub_one]
      simp [width, Nat.not_le.mpr width]
    | succ i =>
      have hi : i < ws.length := by simpa using inside
      have crossed : 256 ≤ 256 * i.succ + row := by omega
      have offset : 256 * i.succ + row - 256 = 256 * i + row := by omega
      have past : ¬ 256 * i.succ + row < 256 := by omega
      rw [fullMask, Nat.testBit_two_pow_sub_one]
      simp [crossed, offset, past, ih hi]

theorem dagMarkBits256 {length i : Nat} (inside : i < length) :
    (dagLaneMarks256 length).testBit (256 * i) = true := by
  induction length generalizing i with
  | zero => omega
  | succ length ih =>
    change (1 ||| (dagLaneMarks256 length <<< 256)).testBit (256 * i) = true
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have hi : i < length := by omega
      have crossed : 256 ≤ 256 * i.succ := by omega
      have offset : 256 * i.succ - 256 = 256 * i := by omega
      simp [crossed, offset, ih hi]

def dagPackedPair256 (packed marks erased out : Word) (directed : Bool) (code : Nat) : Bool :=
  dagForceWord (code &&& 511) (fun p =>
    dagForceWord (code >>> 9) (fun n =>
      let gateOK := if directed then !out.testBit p || out.testBit n else out.testBit p == out.testBit n
      gateOK &&
        dagForceWord ((packed >>> p) &&& marks) (fun up =>
          dagForceWord ((packed >>> n) &&& marks) (fun down =>
            let contrast := if directed then up &&& (down ^^^ marks) else up ^^^ down
            Nat.beq (contrast &&& (marks ^^^ erased)) 0))))

theorem dagPackedPair256Sound {mask goal out : Word} {ws : List Word} {directed : Bool}
    {code a b : Nat} {left right : Bool}
    (nd : ws.Nodup) (pairOK : dagSamplePairOK mask goal code = true)
    (checked : dagPackedPair256 (dagPackWords256 ws) (dagLaneMarks256 ws.length)
      (dagOmitted256 (1 <<< (256 * a)) (1 <<< (256 * b)) left right) out directed code = true) :
    dagPairReject mask goal directed
      (out :: keepWord right (ws.getD b 0) (keepWord left (ws.getD a 0) ws)) [code] = true := by
  apply List.any_eq_true.mpr
  refine ⟨code, List.mem_cons_self, ?_⟩
  simp only [dagSamplePairOK, Bool.and_eq_true, Nat.blt_eq] at pairOK
  obtain ⟨⟨⟨⟨hp, hn⟩, neg⟩, wp⟩, wn⟩ := pairOK
  simp only [dagPackedPair256, dagForceWordEq, Bool.and_eq_true] at checked
  obtain ⟨output, closure⟩ := checked
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨
    Bool.and_eq_true_iff.mpr ⟨hp, hn⟩, neg⟩, List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl | later
  · exact output
  have rightMem := dagKeepMem (dagKeepNodup nd left (ws.getD a 0)) later
  have leftMem := dagKeepMem nd rightMem.1
  obtain ⟨i, inside, eq⟩ := List.mem_iff_getElem.mp leftMem.1
  have atIndex : ws.getD i 0 = w := by
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside] using eq
  have omitted : (dagOmitted256 (1 <<< (256 * a)) (1 <<< (256 * b)) left right).testBit (256 * i) = false := by
    have cleared (j : Nat) (keep : Bool) (h : keep = true ∨ w ≠ ws.getD j 0) :
        (if keep then 0 else 1 <<< (256 * j)).testBit (256 * i) = false := by
      rcases h with yes | diff
      · simp [yes]
      · have ne : i ≠ j := fun same => diff (same ▸ atIndex).symm
        cases keep <;> simp [Nat.shiftLeft_eq, Nat.testBit_two_pow, show 256 * j ≠ 256 * i by omega]
    simp [dagOmitted256, Nat.testBit_or, cleared a left leftMem.2, cleared b right rightMem.2]
  let p := code &&& 511
  let n := code >>> 9
  let marks := dagLaneMarks256 ws.length
  let signal := dagPackWords256 ws
  have mark : marks.testBit (256 * i) = true := dagMarkBits256 inside
  have test {j : Nat} (within : j < 256) :
      ((signal >>> j) &&& marks).testBit (256 * i) = w.testBit j := by
    rw [Nat.testBit_and, Nat.testBit_shiftRight, mark, Bool.and_true,
      Nat.add_comm j, dagPackBits256 inside within, atIndex]
  have h := congrArg (fun word => Nat.testBit word (256 * i)) (Nat.beq_eq.mp closure)
  simp only [Nat.zero_testBit] at h
  change (((if directed then (signal >>> p &&& marks) &&& ((signal >>> n &&& marks) ^^^ marks)
      else (signal >>> p &&& marks) ^^^ (signal >>> n &&& marks)) &&&
    (marks ^^^ dagOmitted256 (1 <<< (256 * a)) (1 <<< (256 * b)) left right)).testBit (256 * i)) = false at h
  have pt := test (j := p) wp
  have nt := test (j := n) wn
  cases directed <;> cases px : w.testBit p <;> cases nx : w.testBit n <;>
    simp [px, nx, pt, nt, Nat.testBit_and, Nat.testBit_xor, mark, omitted, p, n] at h ⊢

def dagSampleKill256 (sample : DagSample) (full : Word) (counts : DagCounts)
    (xC yC outC packed marks aBit bBit out : Word) (directed ka kb : Bool) : Bool :=
  let dx := if ka then 0 else xC
  let dy := if kb then 0 else yC
  let rest := counts.2.2 ||| (counts.2.1 ^^^ (counts.2.1 &&& dx &&& dy)) |||
    (counts.1 ^^^ (counts.1 &&& (dx ||| dy)))
  dagForceWord ((rest ||| outC) ^^^ full) (fun missing =>
    if Nat.beq missing 0 then false
    else dagForceWord (dagHighest7 missing) (fun idx =>
      if Nat.blt idx sample.2 then
        dagForceWord (unpack sample.1 18 idx) (fun code =>
          dagPackedPair256 packed marks (dagOmitted256 aBit bBit ka kb) out directed code)
      else false))

def dagNodeBoundsGo (bounds : Array Bound) (dataPacked cutBits : Nat) : Nat → Nat → List Bound
  | 0, _ => []
  | n + 1, pos =>
      match bounds[unpack dataPacked cutBits pos]? with
      | none => dagNodeBoundsGo bounds dataPacked cutBits n (pos + 1)
      | some b => b :: dagNodeBoundsGo bounds dataPacked cutBits n (pos + 1)

theorem dagNodeBoundsGo_mem {bounds : Array Bound} {dataPacked cutBits : Nat} :
    ∀ cnt off b, b ∈ dagNodeBoundsGo bounds dataPacked cutBits cnt off → b ∈ bounds.toList := by
  intro cnt
  induction cnt with
  | zero => intro _ _ h; cases h
  | succ n ih =>
    intro off b h
    unfold dagNodeBoundsGo at h
    split at h
    · exact ih _ _ h
    next x hx =>
      rcases List.mem_cons.mp h with rfl | h
      · exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? hx)
      · exact ih _ _ h

def dagNodeBounds (bounds : Array Bound) (idxPacked dataPacked indexWidth sizeBits cutBits i : Nat) : List Bound :=
  let entry := unpack idxPacked indexWidth i
  dagNodeBoundsGo bounds dataPacked cutBits (entry &&& fullMask sizeBits) (entry >>> sizeBits)

theorem dagNodeBounds_mem {bounds : Array Bound} {idxPacked dataPacked indexWidth sizeBits cutBits i : Nat} :
    ∀ b ∈ dagNodeBounds bounds idxPacked dataPacked indexWidth sizeBits cutBits i, b ∈ bounds.toList :=
  fun b h => dagNodeBoundsGo_mem _ _ b h

def normWord (mask w : Word) : Word :=
  if w < mask ^^^ w then w else mask ^^^ w

theorem xor_cancel_left (mask w : Word) : mask ^^^ (mask ^^^ w) = w := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem normWord_symm (mask w : Word) : normWord mask (mask ^^^ w) = normWord mask w := by
  unfold normWord
  rw [xor_cancel_left]
  by_cases h : w < mask ^^^ w
  · have h' : ¬(mask ^^^ w < w) := Nat.lt_asymm h
    simp [h, h']
  · by_cases h' : mask ^^^ w < w
    · simp [h, h']
    · have eq : w = mask ^^^ w := Nat.le_antisymm (Nat.le_of_not_lt h') (Nat.le_of_not_lt h)
      rw [if_neg h', if_neg h]; exact eq

theorem normWord_eq_or (mask w : Word) : normWord mask w = w ∨ normWord mask w = mask ^^^ w := by
  unfold normWord; split <;> simp

theorem normWord_idem (mask w : Word) : normWord mask (normWord mask w) = normWord mask w := by
  rcases normWord_eq_or mask w with h | h
  · rw [h, h]
  · rw [h, normWord_symm, h]

theorem normWord_zero (mask : Word) : normWord mask 0 = 0 := by
  unfold normWord
  rw [Nat.xor_zero]
  by_cases h : 0 < mask
  · rw [if_pos h]
  · have hm : mask = 0 := Nat.eq_zero_of_not_pos h
    rw [hm]; rfl

theorem normWord_mask (mask : Word) : normWord mask mask = 0 := by
  have h : normWord mask (mask ^^^ 0) = normWord mask 0 := normWord_symm mask 0
  rwa [Nat.xor_zero, normWord_zero] at h

theorem masked_xor {mask w : Word} (hw : Masked mask w) : Masked mask (mask ^^^ w) := by
  apply Nat.eq_of_testBit_eq; intro i
  have bit := congrArg (fun n : Nat => n.testBit i) hw
  simp only [Nat.testBit_and, Nat.testBit_xor] at bit ⊢
  cases hm : mask.testBit i <;> simp_all

theorem masked_norm {mask w : Word} (hw : Masked mask w) : Masked mask (normWord mask w) := by
  rcases normWord_eq_or mask w with h | h
  · rw [h]; exact hw
  · rw [h]; exact masked_xor hw

theorem proper_xor {mask w : Word} (hp : properWord mask w) : properWord mask (mask ^^^ w) := by
  refine ⟨?_, ?_⟩
  · intro h
    have := congrArg (fun x => mask ^^^ x) h
    rw [xor_cancel_left, Nat.xor_zero] at this
    exact hp.2 this
  · intro h
    have := congrArg (fun x => mask ^^^ x) h
    rw [xor_cancel_left, Nat.xor_self] at this
    exact hp.1 this

theorem proper_norm {mask w : Word} (hp : properWord mask w) : properWord mask (normWord mask w) := by
  rcases normWord_eq_or mask w with h | h
  · rw [h]; exact hp
  · rw [h]; exact proper_xor hp

theorem demorgan_and {mask a b : Word} (ma : Masked mask a) (mb : Masked mask b) :
    mask ^^^ (a &&& b) = (mask ^^^ a) ||| (mask ^^^ b) := by
  apply Nat.eq_of_testBit_eq; intro i
  have ba := congrArg (fun n : Nat => n.testBit i) ma
  have bb := congrArg (fun n : Nat => n.testBit i) mb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] at ba bb ⊢
  cases hm : mask.testBit i <;> cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

theorem demorgan_or {mask a b : Word} (ma : Masked mask a) (mb : Masked mask b) :
    mask ^^^ (a ||| b) = (mask ^^^ a) &&& (mask ^^^ b) := by
  apply Nat.eq_of_testBit_eq; intro i
  have ba := congrArg (fun n : Nat => n.testBit i) ma
  have bb := congrArg (fun n : Nat => n.testBit i) mb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] at ba bb ⊢
  cases hm : mask.testBit i <;> cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all

theorem masked_and_self_xor {mask a : Word} (ma : Masked mask a) : a &&& (mask ^^^ a) = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  have ba := congrArg (fun n : Nat => n.testBit i) ma
  simp only [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit] at ba ⊢
  cases hm : mask.testBit i <;> cases ha : a.testBit i <;> simp_all

theorem masked_or_self_xor {mask a : Word} (ma : Masked mask a) : a ||| (mask ^^^ a) = mask := by
  apply Nat.eq_of_testBit_eq; intro i
  have ba := congrArg (fun n : Nat => n.testBit i) ma
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] at ba ⊢
  cases hm : mask.testBit i <;> cases ha : a.testBit i <;> simp_all

theorem masked_or_mask {mask a : Word} (ma : Masked mask a) : a ||| mask = mask := by
  apply Nat.eq_of_testBit_eq; intro i
  have ba := congrArg (fun n : Nat => n.testBit i) ma
  simp only [Nat.testBit_and, Nat.testBit_or] at ba ⊢
  cases hm : mask.testBit i <;> cases ha : a.testBit i <;> simp_all

def AvBin (mask : Word) (bank : List Word) (w : Word) : Prop :=
  w = 0 ∨ w = mask ∨ w ∈ bank ∨ (mask ^^^ w) ∈ bank

theorem avBin_not {mask : Word} {bank : List Word} {w : Word}
    (h : AvBin mask bank w) : AvBin mask bank (mask ^^^ w) := by
  rcases h with rfl | hmask | hm | hm
  · exact Or.inr (Or.inl (Nat.xor_zero mask))
  · rw [hmask]; exact Or.inl (Nat.xor_self mask)
  · exact Or.inr (Or.inr (Or.inr (by rwa [xor_cancel_left])))
  · exact Or.inr (Or.inr (Or.inl hm))

theorem avBin_weaken {mask : Word} {small big : List Word} {w : Word}
    (sub : ∀ x ∈ small, AvBin mask big x) (av : AvBin mask small w) : AvBin mask big w := by
  rcases av with rfl | rfl | h | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact sub w h
  · simpa [xor_cancel_left] using avBin_not (sub (mask ^^^ w) h)

theorem avBin_of_av {mask : Word} {bank : List Word} {w : Word}
    (h : AvailableWord mask bank w) : AvBin mask bank w := by
  rcases h with rfl | rfl | hm
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl hm))

theorem masked_avBin {mask : Word} {bank : List Word} {w : Word}
    (all : ∀ x ∈ bank, Masked mask x) (av : AvBin mask bank w) : Masked mask w := by
  rcases av with rfl | rfl | hm | hm
  · simp [Masked]
  · simp [Masked]
  · exact all _ hm
  · simpa [xor_cancel_left] using masked_xor (all _ hm)

def GateBin (mask : Word) (bank : List Word) (out : Word) : Prop :=
  ∃ a b, AvBin mask bank a ∧ AvBin mask bank b ∧ (out = a &&& b ∨ out = a ||| b)

theorem gateBin_weaken {mask : Word} {small big : List Word} {out : Word}
    (sub : ∀ x ∈ small, AvBin mask big x) (g : GateBin mask small out) : GateBin mask big out := by
  rcases g with ⟨a, b, ha, hb, eq⟩
  exact ⟨a, b, avBin_weaken sub ha, avBin_weaken sub hb, eq⟩

theorem masked_gateBin {mask : Word} {bank : List Word} {out : Word}
    (all : ∀ x ∈ bank, Masked mask x) (g : GateBin mask bank out) : Masked mask out := by
  rcases g with ⟨a, b, ha, hb, rfl | rfl⟩
  · have ma := masked_avBin all ha; have mb := masked_avBin all hb
    simp only [Masked] at ma mb ⊢; rw [Nat.land_assoc, mb]
  · have ma := masked_avBin all ha; have mb := masked_avBin all hb
    apply Nat.eq_of_testBit_eq; intro i
    have ba := congrArg (fun n : Nat => n.testBit i) ma
    have bb := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at ba bb ⊢
    cases hm : mask.testBit i <;> simp_all

def WordBuildsBin (mask : Word) (roots : List Word) : List Word → Prop
  | [] => True
  | w :: ws => GateBin mask roots w ∧ WordBuildsBin mask (w :: roots) ws

def BinLower (mask : Word) (roots : List Word) (target : Word) (minimum : Nat) : Prop :=
  ∀ values, WordBuildsBin mask roots values →
    AvBin mask (values ++ roots) target → minimum ≤ values.length

theorem buildsBin_weaken {mask : Word} {small big values : List Word}
    (supply : ∀ w ∈ small, AvBin mask big w) (build : WordBuildsBin mask small values) :
    WordBuildsBin mask big values := by
  induction values generalizing small big with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gateBin_weaken supply build.1, ih ?_ build.2⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
    · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hx)))) (supply _ hw)

theorem buildsBin_append {mask : Word} {roots first second : List Word}
    (left : WordBuildsBin mask roots first)
    (right : WordBuildsBin mask (first ++ roots) second) :
    WordBuildsBin mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact right
  | cons w ws ih =>
    refine ⟨left.1, ih left.2 ?_⟩
    exact buildsBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (by
      simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hx)))) right

def binOp4 (mask : Word) (op : Nat) (a b : Word) : Word :=
  if op == 0 then a &&& b
  else if op == 1 then a ||| b
  else if op == 2 then a &&& (mask ^^^ b)
  else (mask ^^^ a) &&& b

def normBinOp4 (mask : Word) (op : Nat) (a b : Word) : Word :=
  normWord mask (binOp4 mask op a b)

def swapOp4 (op : Nat) : Nat :=
  if op == 2 then 3 else if op == 3 then 2 else op

theorem swapOp4_lt {op : Nat} (h : op < 4) : swapOp4 op < 4 := by
  unfold swapOp4
  split
  · decide
  · split
    · decide
    · exact h

theorem binOp4_swap (mask : Word) {op : Nat} (hop : op < 4) (a b : Word) :
    binOp4 mask (swapOp4 op) b a = binOp4 mask op a b := by
  have : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;>
    simp [binOp4, swapOp4, Nat.land_comm, Nat.lor_comm]

theorem normBinOp4_swap (mask : Word) {op : Nat} (hop : op < 4) (a b : Word) :
    normBinOp4 mask (swapOp4 op) b a = normBinOp4 mask op a b := by
  unfold normBinOp4; rw [binOp4_swap mask hop]

theorem gateBin_normBinOp4 {mask : Word} {bank : List Word} {op : Nat} {a b : Word}
    (hop : op < 4) (ma : Masked mask a) (mb : Masked mask b)
    (ha : AvBin mask bank a) (hb : AvBin mask bank b) :
    GateBin mask bank (normBinOp4 mask op a b) := by
  have hna := avBin_not ha
  have hnb := avBin_not hb
  have mna := masked_xor ma
  have mnb := masked_xor mb
  have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  unfold normBinOp4
  rcases normWord_eq_or mask (binOp4 mask op a b) with heq | heq
  · rw [heq]
    rcases hcase with rfl | rfl | rfl | rfl
    · exact ⟨a, b, ha, hb, Or.inl rfl⟩
    · exact ⟨a, b, ha, hb, Or.inr rfl⟩
    · exact ⟨a, mask ^^^ b, ha, hnb, Or.inl rfl⟩
    · exact ⟨mask ^^^ a, b, hna, hb, Or.inl rfl⟩
  · rw [heq]
    rcases hcase with rfl | rfl | rfl | rfl
    · exact ⟨mask ^^^ a, mask ^^^ b, hna, hnb, Or.inr (demorgan_and ma mb)⟩
    · exact ⟨mask ^^^ a, mask ^^^ b, hna, hnb, Or.inl (demorgan_or ma mb)⟩
    · refine ⟨mask ^^^ a, b, hna, hb, Or.inr ?_⟩
      change mask ^^^ (a &&& (mask ^^^ b)) = (mask ^^^ a) ||| b
      rw [demorgan_and ma mnb, xor_cancel_left]
    · refine ⟨a, mask ^^^ b, ha, hnb, Or.inr ?_⟩
      change mask ^^^ ((mask ^^^ a) &&& b) = a ||| (mask ^^^ b)
      rw [demorgan_and mna mb, xor_cancel_left]

def LiveBin (mask target : Word) : Nat → Finset Word → Prop
  | 0, S => S = {normWord mask target} ∧ properWord mask target
  | k + 1, S =>
    ∃ (U : Finset Word) (a b : Word) (op : Nat),
      op < 4 ∧ S = insert a (insert b U) ∧
      properWord mask a ∧ properWord mask b ∧ a ≠ b ∧
      normWord mask a = a ∧ normWord mask b = b ∧
      normBinOp4 mask op a b ∉ insert a (insert b U) ∧
      LiveBin mask target k (insert (normBinOp4 mask op a b) U)

theorem LiveBin.stop {mask target : Word} (hp : properWord mask target) :
    LiveBin mask target 0 {normWord mask target} := ⟨rfl, hp⟩

theorem LiveBin.step {mask target : Word} {k : Nat} {U : Finset Word} {a b : Word} {op : Nat}
    (hop : op < 4) (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
    (na : normWord mask a = a) (nb : normWord mask b = b)
    (hfresh : normBinOp4 mask op a b ∉ insert a (insert b U))
    (tail : LiveBin mask target k (insert (normBinOp4 mask op a b) U)) :
    LiveBin mask target (k + 1) (insert a (insert b U)) :=
  ⟨U, a, b, op, hop, rfl, ha, hb, hab, na, nb, hfresh, tail⟩

theorem LiveBin.ind {mask target : Word}
    {motive : ∀ (k : Nat) (S : Finset Word), LiveBin mask target k S → Prop}
    (stop : ∀ (hp : properWord mask target), motive 0 {normWord mask target} (LiveBin.stop hp))
    (step : ∀ {k : Nat} {U : Finset Word} {a b : Word} {op : Nat}
      (hop : op < 4) (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
      (na : normWord mask a = a) (nb : normWord mask b = b)
      (hfresh : normBinOp4 mask op a b ∉ insert a (insert b U))
      (tail : LiveBin mask target k (insert (normBinOp4 mask op a b) U)),
      motive k (insert (normBinOp4 mask op a b) U) tail →
      motive (k + 1) (insert a (insert b U)) (LiveBin.step hop ha hb hab na nb hfresh tail))
    {k : Nat} {S : Finset Word} (h : LiveBin mask target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U, a, b, op, hop, rfl, ha, hb, hab, na, nb, hf, tail⟩ := h
    exact step hop ha hb hab na nb hf tail (ih tail)

theorem liveBinProps {mask target : Word} {k : Nat} {S : Finset Word}
    (h : LiveBin mask target k S) : ∀ a ∈ S, properWord mask a ∧ normWord mask a = a := by
  induction h using LiveBin.ind with
  | stop hp =>
    intro a ha
    rw [Finset.mem_singleton.mp ha]
    exact ⟨proper_norm hp, normWord_idem mask target⟩
  | step hop ha hb hab na nb hf tail ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨⟨ha, na⟩, ⟨hb, nb⟩, fun w hw => ih w (Finset.mem_insert_of_mem hw)⟩

theorem liveBinSize {mask target : Word} {k : Nat} {S : Finset Word}
    (h : LiveBin mask target k S) : S.card ≤ k + 1 := by
  induction h using LiveBin.ind with
  | stop => simp
  | @step k U a b op hop ha hb hab na nb hf tail ih =>
    have hu : normBinOp4 mask op a b ∉ U := fun hm =>
      hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega

def binWitness (mask : Word) (nws : List Word) (w : Word) : Prop :=
  ∃ op a b, op < 4 ∧ a ∈ nws ∧ b ∈ nws ∧ properWord mask a ∧ properWord mask b ∧
    normWord mask a = a ∧ normWord mask b = b ∧ a ≠ b ∧ w = normBinOp4 mask op a b

theorem classifyGateBin {mask : Word} {bank : List Word} {out : Word}
    (all : ∀ w ∈ bank, Masked mask w) (g : GateBin mask bank out) :
    wordRep mask (bank.map (normWord mask)) (normWord mask out) ∨
    binWitness mask (bank.map (normWord mask)) (normWord mask out) := by
  let nbank := bank.map (normWord mask)
  have c0 : wordRep mask nbank 0 := Or.inr fun h => h.1 rfl
  have cnorm (x : Word) (hx : AvBin mask bank x) :
      x = 0 ∨ x = mask ∨ (normWord mask x ∈ nbank ∧ properWord mask (normWord mask x)) := by
    by_cases hz : x = 0
    · exact Or.inl hz
    by_cases hm : x = mask
    · exact Or.inr (Or.inl hm)
    have hp : properWord mask x := ⟨hz, hm⟩
    refine Or.inr (Or.inr ⟨?_, proper_norm hp⟩)
    rcases (hx.resolve_left hz).resolve_left hm with hmem | hmem
    · exact List.mem_map_of_mem hmem
    · rw [← normWord_symm]; exact List.mem_map_of_mem hmem
  rcases g with ⟨a, b, ha, hb, eq⟩
  have ma := masked_avBin all ha
  have mb := masked_avBin all hb
  have trivial_word (w : Word) (hw : AvBin mask bank w) : wordRep mask nbank (normWord mask w) := by
    rcases cnorm w hw with rfl | rfl | ⟨hm, _⟩
    · rw [normWord_zero]; exact c0
    · rw [normWord_mask]; exact c0
    · exact Or.inl hm
  rcases cnorm a ha with rfl | rfl | ⟨hma, pa⟩
  · rcases eq with rfl | rfl
    · simp only [Nat.zero_and, normWord_zero]; exact Or.inl c0
    · simp only [Nat.zero_or]; exact Or.inl (trivial_word b hb)
  · rcases eq with rfl | rfl
    · rw [Nat.land_comm, mb]; exact Or.inl (trivial_word b hb)
    · rw [Nat.lor_comm, masked_or_mask mb, normWord_mask]; exact Or.inl c0
  rcases cnorm b hb with rfl | rfl | ⟨hmb, pb⟩
  · rcases eq with rfl | rfl
    · simp only [Nat.and_zero, normWord_zero]; exact Or.inl c0
    · simp only [Nat.or_zero]; exact Or.inl (trivial_word a ha)
  · rcases eq with rfl | rfl
    · rw [ma]; exact Or.inl (trivial_word a ha)
    · rw [masked_or_mask ma, normWord_mask]; exact Or.inl c0
  let na := normWord mask a
  let nb := normWord mask b
  have mna : Masked mask na := masked_norm ma
  have mnb : Masked mask nb := masked_norm mb
  by_cases same : na = nb
  · have hrel : b = a ∨ b = mask ^^^ a := by
      rcases normWord_eq_or mask a with ea | ea <;> rcases normWord_eq_or mask b with eb | eb
      · left; exact eb.symm.trans (same.symm.trans ea)
      · right
        have h1 : a = mask ^^^ b := ea.symm.trans (same.trans eb)
        have := congrArg (fun z => mask ^^^ z) h1
        rw [xor_cancel_left] at this; exact this.symm
      · right; exact eb.symm.trans (same.symm.trans ea)
      · left
        have h1 : mask ^^^ a = mask ^^^ b := ea.symm.trans (same.trans eb)
        have := congrArg (fun z => mask ^^^ z) h1
        rw [xor_cancel_left, xor_cancel_left] at this; exact this.symm
    rcases hrel with rfl | rfl <;> rcases eq with rfl | rfl
    · rw [Nat.and_self]; exact Or.inl (Or.inl hma)
    · rw [Nat.or_self]; exact Or.inl (Or.inl hma)
    · rw [masked_and_self_xor ma, normWord_zero]; exact Or.inl c0
    · rw [masked_or_self_xor ma, normWord_mask]; exact Or.inl c0
  have ea : a = na ∨ a = mask ^^^ na := by
    rcases normWord_eq_or mask a with h | h
    · exact Or.inl h.symm
    · right; have := congrArg (fun z => mask ^^^ z) h; rw [xor_cancel_left] at this; exact this.symm
  have eb : b = nb ∨ b = mask ^^^ nb := by
    rcases normWord_eq_or mask b with h | h
    · exact Or.inl h.symm
    · right; have := congrArg (fun z => mask ^^^ z) h; rw [xor_cancel_left] at this; exact this.symm
  have mkWit (op : Nat) (hop : op < 4) (heq : normWord mask out = normBinOp4 mask op na nb) :
      binWitness mask nbank (normWord mask out) :=
    ⟨op, na, nb, hop, hma, hmb, pa, pb, normWord_idem mask a, normWord_idem mask b, same, heq⟩
  right
  rcases eq with hout | hout <;> rcases ea with hea | hea <;> rcases eb with heb | heb
  · exact mkWit 0 (by decide) (by rw [hout, hea, heb]; rfl)
  · exact mkWit 2 (by decide) (by rw [hout, hea, heb]; rfl)
  · exact mkWit 3 (by decide) (by rw [hout, hea, heb]; rfl)
  · exact mkWit 1 (by decide) (by rw [hout, hea, heb, ← demorgan_or mna mnb, normWord_symm]; rfl)
  · exact mkWit 1 (by decide) (by rw [hout, hea, heb]; rfl)
  · exact mkWit 3 (by decide) (by
      have h1 : mask ^^^ ((mask ^^^ na) &&& nb) = na ||| (mask ^^^ nb) := by
        rw [demorgan_and (masked_xor mna) mnb, xor_cancel_left]
      rw [hout, hea, heb, ← h1, normWord_symm]; rfl)
  · exact mkWit 2 (by decide) (by
      have h1 : mask ^^^ (na &&& (mask ^^^ nb)) = (mask ^^^ na) ||| nb := by
        rw [demorgan_and mna (masked_xor mnb), xor_cancel_left]
      rw [hout, hea, heb, ← h1, normWord_symm]; rfl)
  · exact mkWit 0 (by decide) (by rw [hout, hea, heb, ← demorgan_and mna mnb, normWord_symm]; rfl)

theorem pullBin {mask target : Word} {nws : List Word} {z : Word} {k : Nat} {S : Finset Word}
    (h : LiveBin mask target k S)
    (hz : wordRep mask nws z ∨ binWitness mask nws z) (sub : ∀ a ∈ S, a ∈ nws ++ [z]) :
    ∃ k' S', k' ≤ k + 1 ∧ LiveBin mask target k' S' ∧ ∀ a ∈ S', a ∈ nws := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ nws
    · refine ⟨k, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ nws ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := (liveBinProps h z hm).1
      rcases hz with hr | ⟨op, a, b, hop, ha, hb, pa, pb, na, nb, hab, eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (normBinOp4 mask op a b)
        have ht : LiveBin mask target k (insert (normBinOp4 mask op a b) U) := by
          simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ nws := by
          intro v hv
          obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hmem
        have hf : normBinOp4 mask op a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨k + 1, insert a (insert b U), Nat.le_refl _,
          LiveBin.step hop pa pb hab na nb hf ht, by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, S, by omega, h, ?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

theorem extractBinLive {mask target : Word} {roots values : List Word}
    (all : ∀ w ∈ roots, Masked mask w) (builds : WordBuildsBin mask roots values)
    (hit : AvBin mask (values ++ roots) target) (p : properWord mask target) :
    ∃ k S, k ≤ values.length ∧ LiveBin mask target k S ∧ ∀ w ∈ S, w ∈ roots.map (normWord mask) := by
  have hm : normWord mask target ∈ (values ++ roots).map (normWord mask) := by
    rcases (hit.resolve_left p.1).resolve_left p.2 with hmem | hmem
    · exact List.mem_map_of_mem hmem
    · rw [← normWord_symm]; exact List.mem_map_of_mem hmem
  induction values generalizing roots with
  | nil =>
    exact ⟨0, {normWord mask target}, Nat.zero_le _, LiveBin.stop p, by simpa using hm⟩
  | cons w ws ih =>
    have next : ∀ v ∈ w :: roots, Masked mask v := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact masked_gateBin all builds.1
      · exact all _ hv
    have ht : AvBin mask (ws ++ w :: roots) target := by
      rcases hit with rfl | rfl | hmem | hmem
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl (by simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hmem)))
      · exact Or.inr (Or.inr (Or.inr (by simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hmem)))
    have hm' : normWord mask target ∈ (ws ++ w :: roots).map (normWord mask) := by
      rcases (ht.resolve_left p.1).resolve_left p.2 with hmem | hmem
      · exact List.mem_map_of_mem hmem
      · rw [← normWord_symm]; exact List.mem_map_of_mem hmem
    obtain ⟨k, S, hk, live, sub⟩ := ih next builds.2 ht hm'
    have available : ∀ v ∈ S, v ∈ roots.map (normWord mask) ++ [normWord mask w] := by
      intro v h
      simpa [List.map_cons, or_comm] using sub v h
    obtain ⟨k', S', hk', hl, hsub⟩ := pullBin live (classifyGateBin all builds.1) available
    exact ⟨k', S', by simp only [List.length_cons]; omega, hl, hsub⟩

theorem agreesNorm {i j mask w : Word} (m : AgreesAt i j mask) (hw : AgreesAt i j w) :
    AgreesAt i j (normWord mask w) := by
  rcases normWord_eq_or mask w with h | h
  · rw [h]; exact hw
  · rw [h]; simp only [AgreesAt, Nat.testBit_xor] at m hw ⊢; rw [m, hw]

theorem liveBinAgrees {mask target : Word} {i j k : Nat} {S : Finset Word}
    (h : LiveBin mask target k S) (m : AgreesAt i j mask)
    (all : ∀ w ∈ S, AgreesAt i j w) : AgreesAt i j target := by
  induction h using LiveBin.ind with
  | stop =>
    have hn := all _ (Finset.mem_singleton_self _)
    rcases normWord_eq_or mask target with h | h
    · rwa [h] at hn
    · rw [h] at hn
      change mask.testBit i = mask.testBit j at m
      change (mask ^^^ target).testBit i = (mask ^^^ target).testBit j at hn
      rw [Nat.testBit_xor, Nat.testBit_xor, m] at hn
      change target.testBit i = target.testBit j
      cases hmj : mask.testBit j <;> cases hti : target.testBit i <;> cases htj : target.testBit j <;> simp_all
  | @step k U a b op hop pa pb hab na nb hf tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · unfold normBinOp4
      apply agreesNorm m
      have aa : a.testBit i = a.testBit j := all a (Finset.mem_insert_self _ _)
      have bb : b.testBit i = b.testBit j := all b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      have mm : mask.testBit i = mask.testBit j := m
      have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl <;>
        simp [binOp4, AgreesAt, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, aa, bb, mm]
    · exact all _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))

theorem dagPartitionLiveBin {mask goal : Word} {ws : List Word} {k : Nat}
    (goalMask : Masked mask goal) (live : LiveBin mask goal k ws.toFinset) :
    dagPartition false ws goal (mask ^^^ goal) = true := by
  by_contra fail
  have openPair : dagPartition false ws goal (mask ^^^ goal) = false := by
    cases h : dagPartition false ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p, n, hp, hn, agree⟩ := dagPartitionSound openPair
  have pm := positiveInMask goalMask hp
  have nm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have implied := fun ht : goal.testBit n = true => positiveInMask goalMask ht
    cases hm : mask.testBit n <;> cases ht : goal.testBit n <;> simp_all
  have same := liveBinAgrees live (pm.trans nm.1.symm) (fun w hw => by
    simpa [AgreesAt] using agree w (List.mem_toFinset.mp hw))
  simp [AgreesAt, hp, nm.2] at same

theorem dagPairsOpenBin {mask goal : Word} {ws : List Word} {pairs : List Nat} {k : Nat}
    (masked : Masked mask goal) (live : LiveBin mask goal k ws.toFinset) :
    dagPairReject mask goal false ws pairs = false := by
  apply Bool.eq_false_iff.mpr
  intro close
  obtain ⟨code, _, check⟩ := List.any_eq_true.mp close
  simp only [Bool.and_eq_true, Bool.not_eq_true, List.all_eq_true] at check
  obtain ⟨⟨⟨hp, mn⟩, hn⟩, bank⟩ := check
  have neg : goal.testBit (code >>> 9) = false := by simpa using hn
  have h := liveBinAgrees live ((positiveInMask masked hp).trans mn.symm) (fun w hw => by
    have pair := bank _ (List.mem_toFinset.mp hw)
    simpa [AgreesAt] using pair)
  simp [AgreesAt, hp, neg] at h

theorem essentialRequiredBin {mask target : Word} {stock : List Word} {entry : Witness}
    {S : Finset Word} {k : Nat}
    (ok : essentialB mask target stock entry = true)
    (sub : ∀ w ∈ S, w ∈ stock.map (normWord mask)) (live : LiveBin mask target k S) :
    normWord mask (witnessWord entry) ∈ S := by
  obtain ⟨w, p, n⟩ := entry
  simp only [essentialB, Bool.and_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨mp, mn⟩, tp⟩, tn⟩, unequal⟩, rest⟩ := ok
  by_contra no
  have all : ∀ x ∈ S, AgreesAt p n x := by
    intro x hx
    obtain ⟨orig, omem, rfl⟩ := List.mem_map.mp (sub x hx)
    have horig : orig ≠ w := fun e => no (by simpa [witnessWord, e] using hx)
    have h := List.all_eq_true.mp rest orig omem
    have hag : AgreesAt p n orig := by simpa [horig, AgreesAt] using h
    exact agreesNorm (mp.trans mn.symm) hag
  have agree := liveBinAgrees live (mp.trans mn.symm) all
  have falseBit : target.testBit n = false := by simpa using tn
  simp [AgreesAt, tp, falseBit] at agree

theorem essentialWordsInBin {mask target : Word} {stock : List Word} {witnesses : List Witness}
    {S : Finset Word} {k : Nat}
    (ok : witnesses.all (essentialB mask target stock) = true)
    (sub : ∀ w ∈ S, w ∈ stock.map (normWord mask)) (live : LiveBin mask target k S) :
    (witnesses.map (fun e => normWord mask (witnessWord e))).toFinset ⊆ S := by
  intro w hw
  obtain ⟨entry, mem, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
  exact essentialRequiredBin (List.all_eq_true.mp ok entry mem) sub live

def buildableBin (m g : Word) : Nat → Finset Word → Prop
  | 0, s => g ∈ s ∨ (m ^^^ g) ∈ s
  | n + 1, s => buildableBin m g n s ∨
      ∃ a b, (a ∈ s ∨ m ^^^ a ∈ s) ∧ (b ∈ s ∨ m ^^^ b ∈ s) ∧
        ∃ d : Bool, buildableBin m g n (insert (binWord d a b) s)

theorem supplyPoolBin {m g : Word} {n : Nat} {s q : Finset Word}
    (sub : ∀ w ∈ s, w ∈ q ∨ m ^^^ w ∈ q) (h : buildableBin m g n s) : buildableBin m g n q := by
  induction n generalizing s q with
  | zero =>
    rcases h with h1 | h1
    · exact sub g h1
    · rcases sub (m ^^^ g) h1 with h2 | h2
      · exact Or.inr h2
      · rw [xor_cancel_left] at h2; exact Or.inl h2
  | succ n ih =>
    have subPair {x : Word} (hx : x ∈ s ∨ m ^^^ x ∈ s) : x ∈ q ∨ m ^^^ x ∈ q := by
      rcases hx with h1 | h1
      · exact sub x h1
      · rcases sub (m ^^^ x) h1 with h2 | h2
        · exact Or.inr h2
        · rw [xor_cancel_left] at h2; exact Or.inl h2
    rcases h with h | ⟨a, b, ha, hb, d, h⟩
    · exact Or.inl (ih sub h)
    · refine Or.inr ⟨a, b, subPair ha, subPair hb, d, ih ?_ h⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact Or.inl (Finset.mem_insert_self _ _)
      · rcases sub w hw with hq | hq
        · exact Or.inl (Finset.mem_insert_of_mem hq)
        · exact Or.inr (Finset.mem_insert_of_mem hq)

theorem buildableBinWords {mask goal n : Nat} {pool : Finset Word} {bank : List Word}
    (h : buildableBin mask goal n pool) (supply : ∀ w ∈ pool, AvBin mask bank w) :
    ∃ values, values.length ≤ n ∧ WordBuildsBin mask bank values ∧
      AvBin mask (values ++ bank) goal := by
  induction n generalizing pool bank with
  | zero =>
    refine ⟨[], Nat.le_refl _, trivial, ?_⟩
    rcases h with h1 | h1
    · exact supply goal h1
    · simpa [xor_cancel_left] using avBin_not (supply _ h1)
  | succ n ih =>
    have supPair {w : Word} (hw : w ∈ pool ∨ mask ^^^ w ∈ pool) : AvBin mask bank w := by
      rcases hw with h1 | h1
      · exact supply w h1
      · simpa [xor_cancel_left] using avBin_not (supply _ h1)
    rcases h with h | ⟨a, b, ha, hb, d, h⟩
    · obtain ⟨values, cap, build, hit⟩ := ih h supply
      exact ⟨values, by omega, build, hit⟩
    · let w := binWord d a b
      have g : GateBin mask bank w :=
        ⟨a, b, supPair ha, supPair hb, by cases d <;> simp [w, binWord]⟩
      have growing : ∀ v ∈ insert w pool, AvBin mask (w :: bank) v := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
        · exact avBin_weaken (fun _ hh => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hh)))) (supply _ hv)
      obtain ⟨values, budget, build, hit⟩ := ih h growing
      refine ⟨w :: values, by simp only [List.length_cons]; omega, ⟨g, build⟩, ?_⟩
      exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (by
        simp only [List.mem_append, List.mem_cons] at hx ⊢; tauto)))) hit

theorem cofBinOp4 {mask m : Word} (sub : mask &&& m = m) {op : Nat} (hop : op < 4) (a b : Word) :
    binOp4 mask op a b &&& m = binOp4 m op (a &&& m) (b &&& m) := by
  have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  rcases hcase with rfl | rfl | rfl | rfl
  · exact cofBinary m a b false
  · exact cofBinary m a b true
  · change (a &&& (mask ^^^ b)) &&& m = (a &&& m) &&& (m ^^^ (b &&& m))
    rw [← cofNot sub b]; exact cofBinary m a (mask ^^^ b) false
  · change ((mask ^^^ a) &&& b) &&& m = (m ^^^ (a &&& m)) &&& (b &&& m)
    rw [← cofNot sub a]; exact cofBinary m (mask ^^^ a) b false

theorem flNorm {mask m : Word} (sub : mask &&& m = m) (a : Word) :
    maskedFlat m (normWord mask a) ↔ maskedFlat m a := by
  rcases normWord_eq_or mask a with h | h
  · rw [h]
  · rw [h]; exact flNot sub a

theorem flBothOp4 {mask m : Word} (sub : mask &&& m = m) {op : Nat} (hop : op < 4) {a b : Word}
    (ha : maskedFlat m a) (hb : maskedFlat m b) : maskedFlat m (normBinOp4 mask op a b) := by
  rw [normBinOp4, flNorm sub]
  unfold maskedFlat at *
  rw [cofBinOp4 sub hop]
  have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  rcases hcase with rfl | rfl | rfl | rfl <;>
    rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    simp [binOp4, ha, hb]

theorem simpleBinOp4 {mask m : Word} (sub : mask &&& m = m) {op : Nat} (hop : op < 4) {a b : Word}
    (h : maskedFlat m a ∨ maskedFlat m b) :
    binOp4 mask op a b &&& m = 0 ∨ binOp4 mask op a b &&& m = m ∨
    binOp4 mask op a b &&& m = a &&& m ∨ binOp4 mask op a b &&& m = m ^^^ (a &&& m) ∨
    binOp4 mask op a b &&& m = b &&& m ∨ binOp4 mask op a b &&& m = m ^^^ (b &&& m) := by
  rw [cofBinOp4 sub hop]
  have top1 (x : Word) : m &&& (x &&& m) = x &&& m := by
    rw [Nat.land_comm x m, ← Nat.land_assoc]; simp
  have top2 (x : Word) : m ||| (x &&& m) = m := by rw [Nat.lor_comm]; exact masked_or_mask (restrictWord m x)
  have top3 (x : Word) : (m ^^^ (x &&& m)) &&& m = m ^^^ (x &&& m) :=
    masked_xor (restrictWord m x)
  have right1 (x : Word) : (x &&& m) &&& m = x &&& m := restrictWord m x
  have right2 (x : Word) : (x &&& m) ||| m = m := by rw [Nat.lor_comm, top2]
  have right3 (x : Word) : m &&& (m ^^^ (x &&& m)) = m ^^^ (x &&& m) := by
    rw [Nat.land_comm]; exact top3 x
  have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
  rcases hcase with rfl | rfl | rfl | rfl <;> rcases h with (ha | ha) | (hb | hb) <;>
    simp [binOp4, *, top1, top2, top3, right1, right2, right3]

theorem maskedBuildBin {mask goal : Word} {k : Nat} {s : Finset Word}
    (run : LiveBin mask goal k s) (m : Word) (submask : mask &&& m = m)
    (properGoal : ¬ maskedFlat m goal) :
    ∃ n, n + (flatSet m s).card ≤ k ∧ buildableBin m (goal &&& m) n (projectedStock m s) := by
  induction run using LiveBin.ind with
  | stop =>
    refine ⟨0, ?_, ?_⟩
    · have pgn : ¬ maskedFlat m (normWord mask goal) := by rwa [flNorm submask]
      simp only [flatSet, Finset.filter_singleton, pgn, ite_false, Finset.card_empty,
        Nat.add_zero, Nat.le_refl]
    · rcases normWord_eq_or mask goal with h | h
      · left; simp [projectedStock, visibleWords, h]
      · right; rw [← cofNot submask goal, ← h]; simp [projectedStock, visibleWords]
  | @step k u a b op hop pa pb ab na nb fresh tail ih =>
    let v := normBinOp4 mask op a b
    obtain ⟨n, cap, built⟩ := ih
    have nn : v ∉ u := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    change n + (flatSet m (insert v u)).card ≤ k at cap
    rw [flIns nn] at cap
    have ca := flLe m a (insert b u)
    have cb := flLe m b u
    have hv_rel : v &&& m = binOp4 mask op a b &&& m ∨
        v &&& m = m ^^^ (binOp4 mask op a b &&& m) := by
      rcases normWord_eq_or mask (binOp4 mask op a b) with h | h
      · left; simp [v, normBinOp4, h]
      · right; simp [v, normBinOp4, h, cofNot submask]
    by_cases simple : maskedFlat m a ∨ maskedFlat m b
    · have budget : n + (flatSet m (insert a (insert b u))).card ≤ k + 1 := by
        by_cases fa : maskedFlat m a <;> by_cases fb : maskedFlat m b <;>
          simp only [fa, fb, ite_true, ite_false] at ca cb simple
        all_goals first | have vf : maskedFlat m v := flBothOp4 submask hop fa fb; simp only [vf, ite_true] at cap; omega | omega | tauto
      refine ⟨n, budget, supplyPoolBin ?_ built⟩
      intro w hw
      simp only [projectedStock, prIns, Finset.mem_insert] at hw ⊢
      rcases hw with rfl | rfl | rfl | h
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr (Or.inl rfl))
      · have sc := simpleBinOp4 submask hop simple
        rcases hv_rel with e | e <;> rw [e]
        · rcases sc with c | c | c | c | c | c <;> rw [c]
          · exact Or.inl (Or.inl rfl)
          · exact Or.inl (Or.inr (Or.inl rfl))
          · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · exact Or.inr (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · rcases sc with c | c | c | c | c | c <;> rw [c]
          · exact Or.inl (Or.inr (Or.inl (Nat.xor_zero m)))
          · exact Or.inl (Or.inl (Nat.xor_self m))
          · exact Or.inr (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inl (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · exact Or.inl (by rw [xor_cancel_left]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · have fa : ¬maskedFlat m a := fun h => simple (Or.inl h)
      have fb : ¬maskedFlat m b := fun h => simple (Or.inr h)
      simp only [fa, fb, ite_false] at ca cb
      have ha_in : a &&& m ∈ projectedStock m (insert a (insert b u)) := by simp [projectedStock, prIns]
      have hb_in : b &&& m ∈ projectedStock m (insert a (insert b u)) := by simp [projectedStock, prIns]
      have hna_in : m ^^^ (m ^^^ (a &&& m)) ∈ projectedStock m (insert a (insert b u)) := by
        rwa [xor_cancel_left]
      have hnb_in : m ^^^ (m ^^^ (b &&& m)) ∈ projectedStock m (insert a (insert b u)) := by
        rwa [xor_cancel_left]
      have mkStep {a' b' : Word} {d : Bool}
          (ha' : a' ∈ projectedStock m (insert a (insert b u)) ∨ m ^^^ a' ∈ projectedStock m (insert a (insert b u)))
          (hb' : b' ∈ projectedStock m (insert a (insert b u)) ∨ m ^^^ b' ∈ projectedStock m (insert a (insert b u)))
          (heq : binOp4 mask op a b &&& m = binWord d a' b') :
          ∃ n', n' + (flatSet m (insert a (insert b u))).card ≤ k + 1 ∧
            buildableBin m (goal &&& m) n' (projectedStock m (insert a (insert b u))) := by
        refine ⟨n + 1, by omega, Or.inr ⟨a', b', ha', hb', d, supplyPoolBin ?_ built⟩⟩
        intro w hw
        simp only [projectedStock, prIns, Finset.mem_insert] at hw ⊢
        rcases hw with rfl | rfl | rfl | h
        · exact Or.inl (Or.inr (Or.inl rfl))
        · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
        · rcases hv_rel with e | e
          · exact Or.inl (Or.inl (e.trans heq))
          · exact Or.inr (by rw [e, xor_cancel_left]; exact Or.inl heq)
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
      have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · exact mkStep (d := false) (Or.inl ha_in) (Or.inl hb_in) (cofBinOp4 (op := 0) submask (by decide) a b)
      · exact mkStep (d := true) (Or.inl ha_in) (Or.inl hb_in) (cofBinOp4 (op := 1) submask (by decide) a b)
      · exact mkStep (d := false) (Or.inl ha_in) (Or.inr hnb_in) (cofBinOp4 (op := 2) submask (by decide) a b)
      · exact mkStep (d := false) (Or.inr hna_in) (Or.inl hb_in) (cofBinOp4 (op := 3) submask (by decide) a b)

theorem essentialLiftBin {mask target : Word} {stock cutStock : List Word} {witnesses : List Witness}
    {minimum cut prior : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (submask : mask &&& cut = cut)
    (cutProper : properWord cut (target &&& cut))
    (supplies : ∀ w ∈ stock, AvBin cut cutStock (w &&& cut))
    (known : BinLower cut cutStock (target &&& cut) prior)
    (bound : minimum ≤ prior + (flatSet cut (witnesses.map (fun e => normWord mask (witnessWord e))).toFinset).card) :
    BinLower mask stock target minimum := by
  intro values build hit
  obtain ⟨k, S, hk, live, sub⟩ := extractBinLive masked build hit proper
  have subW := essentialWordsInBin ok sub live
  have subFlat : flatSet cut (witnesses.map (fun e => normWord mask (witnessWord e))).toFinset ⊆ flatSet cut S :=
    Finset.filter_subset_filter _ subW
  have card := Finset.card_le_card subFlat
  have pf : ¬maskedFlat cut target := by simpa [maskedFlat, properWord] using cutProper
  obtain ⟨n, budget, built⟩ := maskedBuildBin live cut submask pf
  have starts : ∀ w ∈ projectedStock cut S, AvBin cut cutStock w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image] at hw
    rcases hw with rfl | rfl | ⟨x, hx, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · obtain ⟨orig, omem, rfl⟩ := List.mem_map.mp (sub x hx)
      rcases normWord_eq_or mask orig with e | e
      · rw [e]; exact supplies _ omem
      · rw [e, cofNot submask]; exact avBin_not (supplies _ omem)
  obtain ⟨ys, len, built', out⟩ := buildableBinWords built starts
  have lower := known ys built' out
  omega

def normWordFast (mask w : Word) : Word :=
  dagForceWord (mask ^^^ w) (fun c => if Nat.blt w c then w else c)

theorem normWordFast_eq (mask w : Word) : normWordFast mask w = normWord mask w := by
  simp [normWordFast, normWord, dagForceWordEq, Nat.blt_eq]

def normBinOp4Fast (mask op x y : Word) : Word :=
  normWordFast mask (binOp4 mask op x y)

theorem normBinOp4Fast_eq (mask op x y : Word) : normBinOp4Fast mask op x y = normBinOp4 mask op x y :=
  normWordFast_eq mask (binOp4 mask op x y)

def availableNormB (bank : List Word) (v : Word) : Bool :=
  v == 0 || bank.contains v

theorem availableNormB_spec {mask : Word} {orig bank : List Word} {w : Word}
    (mw : Masked mask w) (hbank : ∀ x ∈ bank, AvBin mask orig x)
    (h : availableNormB bank (normWord mask w) = true) : AvBin mask orig w := by
  simp only [availableNormB, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at h
  rcases h with hz | hm
  · rcases normWord_eq_or mask w with e | e
    · exact Or.inl (e.symm.trans hz)
    · have : mask ^^^ w = 0 := e.symm.trans hz
      have h1 : w = mask := by
        have h2 := congrArg (fun z => mask ^^^ z) this
        rw [xor_cancel_left, Nat.xor_zero] at h2
        exact h2
      exact Or.inr (Or.inl h1)
  · have hav := hbank _ hm
    rcases normWord_eq_or mask w with e | e
    · rwa [e] at hav
    · rw [e] at hav
      have := avBin_not hav
      rwa [xor_cancel_left] at this

def stockWordBinF (mask : Word) (nstock needed : List Word) (word : Word) : List Word :=
  dagForceWord (normWordFast mask (word &&& mask)) (fun v =>
    if availableNormB nstock v || needed.contains v then needed else v :: needed)

def recipeStartBinF (mask : Word) (nstock words : List Word) : List Word :=
  (List.rec (motive := fun _ => List Word → List Word) id
    (fun word _ next seen => next (stockWordBinF mask nstock seen word)) words) []

def recipeClosureBinF (mask : Word) (nstock : List Word) (history : List (Word × Word × Word))
    (start : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) id
    (fun (out, a, b) _ next seen =>
      next (dagForceWord (normWordFast mask (out &&& mask)) (fun vo =>
        if seen.contains vo then
          stockWordBinF mask nstock (stockWordBinF mask nstock seen a) b else seen)))
    history start

def recipeGateBinNorm (mask : Word) (nbank : List Word) (v ma mb : Word) : Bool :=
  availableNormB nbank (normWordFast mask ma) && availableNormB nbank (normWordFast mask mb) &&
    (v == normWordFast mask (ma &&& mb) || v == normWordFast mask (ma ||| mb) ||
     v == normWordFast mask (ma &&& (mask ^^^ mb)) || v == normWordFast mask ((mask ^^^ ma) &&& mb))

theorem recipeGateBinNorm_spec {mask : Word} {orig nbank : List Word} {v ma mb : Word}
    (hma : Masked mask ma) (hmb : Masked mask mb)
    (hbank : ∀ x ∈ nbank, AvBin mask orig x)
    (h : recipeGateBinNorm mask nbank v ma mb = true) : GateBin mask orig v := by
  simp only [recipeGateBinNorm, normWordFast_eq, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨ha, hb⟩, eq⟩ := h
  have havA := availableNormB_spec hma hbank ha
  have havB := availableNormB_spec hmb hbank hb
  rcases eq with ((rfl | rfl) | rfl) | rfl
  · exact gateBin_normBinOp4 (op := 0) (by decide) hma hmb havA havB
  · exact gateBin_normBinOp4 (op := 1) (by decide) hma hmb havA havB
  · exact gateBin_normBinOp4 (op := 2) (by decide) hma hmb havA havB
  · exact gateBin_normBinOp4 (op := 3) (by decide) hma hmb havA havB

def replayRecipesBinF (mask : Word) (needed : List Word) : List (Word × Word × Word) → List Word → List Word
  | [], _ => []
  | (w, a, b) :: rs, nbank =>
      dagForceWord (normWordFast mask (w &&& mask)) (fun v =>
        if needed.contains v && !availableNormB nbank v then
          dagForceWord (a &&& mask) (fun ma =>
            dagForceWord (b &&& mask) (fun mb =>
              if recipeGateBinNorm mask nbank v ma mb then
                v :: replayRecipesBinF mask needed rs (v :: nbank)
              else replayRecipesBinF mask needed rs nbank))
        else replayRecipesBinF mask needed rs nbank)

theorem replayRecipesBinFBuilds (mask : Word) (needed : List Word) (recipes : List (Word × Word × Word))
    (orig nbank : List Word) (hbank : ∀ x ∈ nbank, AvBin mask orig x) :
    WordBuildsBin mask orig (replayRecipesBinF mask needed recipes nbank) ∧
      ∀ x ∈ replayRecipesBinF mask needed recipes nbank, x ∈ replayRecipesBinF mask needed recipes nbank := by
  refine ⟨?_, fun _ h => h⟩
  induction recipes generalizing orig nbank with
  | nil => trivial
  | cons recipe recipes ih =>
    obtain ⟨w, a, b⟩ := recipe
    change WordBuildsBin mask orig (dagForceWord (normWordFast mask (w &&& mask)) (fun v =>
      if needed.contains v && !availableNormB nbank v then
        dagForceWord (a &&& mask) (fun ma =>
          dagForceWord (b &&& mask) (fun mb =>
            if recipeGateBinNorm mask nbank v ma mb then
              v :: replayRecipesBinF mask needed recipes (v :: nbank)
            else replayRecipesBinF mask needed recipes nbank))
      else replayRecipesBinF mask needed recipes nbank))
    simp only [dagForceWordEq, normWordFast_eq]
    split
    · split
      · rename_i h1 h2
        refine ⟨recipeGateBinNorm_spec (restrictWord mask a) (restrictWord mask b) hbank h2, ?_⟩
        apply ih (normWord mask (w &&& mask) :: orig) (normWord mask (w &&& mask) :: nbank)
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
        · exact avBin_weaken (fun y hy => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hy)))) (hbank x hx)
      · exact ih orig nbank hbank
    · exact ih orig nbank hbank

def dagBoundClosesBinNoHdr (state : RowState) (bound : Bound) : Bool :=
  let (mask, nstock, lower, _) := bound
  let (fuel, ws, history) := state
  dagForceWord (fuel - flatCountF mask ws) (fun remaining =>
    if Nat.blt remaining lower then
      dagForceWords (recipeStartBinF mask nstock ws) (fun start =>
        if Nat.blt (start.length + remaining) lower then
          dagForceWords (recipeClosureBinF mask nstock history start) (fun needed =>
            if Nat.blt (needed.length + remaining) lower then
              dagForceWords (replayRecipesBinF mask needed history.reverse nstock) (fun replay =>
                Nat.blt (replay.length + remaining) lower &&
                  ws.all (fun w => dagForceWord (normWordFast mask (w &&& mask)) (fun v =>
                    availableNormB (replay ++ nstock) v)))
            else false)
        else false)
    else false)

def dagKnownClosesBinNoHdr (bounds : List Bound) (state : RowState) : Bool :=
  List.rec false (fun bound _ later => dagBoundClosesBinNoHdr state bound || later) bounds

def dagFilterForceBoundsBin (target : Word) (bounds : List Bound) (cont : List Bound → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Bound → Bool) → Bool) (fun k => k [])
    (fun b _ next k =>
      dagForceWord b.1 (fun m' =>
        dagForceWord b.2.2.2 (fun g' =>
          if (target &&& m') == g' && g' != 0 && g' != m' then
            dagForceWords (b.2.1.map (fun w => normWordFast m' w)) (fun nst' =>
              next (fun rest => k ((m', nst', b.2.2.1, g') :: rest)))
          else next k))) bounds) cont

theorem dagFilterForceBoundsBinEq (target : Word) (bounds : List Bound) (cont : List Bound → Bool) :
    dagFilterForceBoundsBin target bounds cont =
      cont ((bounds.filter (dagBoundHeaderOK target)).map (fun b => (b.1, b.2.1.map (normWord b.1), b.2.2.1, b.2.2.2))) := by
  induction bounds generalizing cont with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨m, st, lo, g⟩ := b
    change dagForceWord m (fun m' => dagForceWord g (fun g' =>
      if (target &&& m') == g' && g' != 0 && g' != m' then
        dagForceWords (st.map (fun w => normWordFast m' w)) (fun nst' =>
          dagFilterForceBoundsBin target bs (fun rest => cont ((m', nst', lo, g') :: rest)))
      else dagFilterForceBoundsBin target bs cont)) = _
    simp only [dagForceWordEq, dagForceWordsEq, List.filter_cons, dagBoundHeaderOK]
    have hm : st.map (fun w => normWordFast m w) = st.map (normWord m) := by
      congr 1; funext w; exact normWordFast_eq m w
    by_cases hc : ((target &&& m) == g && g != 0 && g != m) = true
    · simp only [hc, ite_true, hm, List.map_cons]; exact ih _
    · simp only [Bool.not_eq_true] at hc; simp only [hc, Bool.false_eq_true, ite_false]; exact ih _

def dagBoundClosesBinFast (target : Word) (state : RowState) (bound : Bound) : Bool :=
  let (mask, nstock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    dagForceWord (fuel - flatCountF mask ws) (fun remaining =>
      if Nat.blt remaining lower then
        dagForceWords (recipeStartBinF mask nstock ws) (fun start =>
          if Nat.blt (start.length + remaining) lower then
            dagForceWords (recipeClosureBinF mask nstock history start) (fun needed =>
              if Nat.blt (needed.length + remaining) lower then
                dagForceWords (replayRecipesBinF mask needed history.reverse nstock) (fun replay =>
                  Nat.blt (replay.length + remaining) lower &&
                    ws.all (fun w => dagForceWord (normWordFast mask (w &&& mask)) (fun v =>
                      availableNormB (replay ++ nstock) v)))
              else false)
          else false)
      else false)

def availableBinB (mask : Word) (bank : List Word) (w : Word) : Bool :=
  w == 0 || w == mask || bank.contains w || bank.contains (mask ^^^ w)

theorem availableBinB_spec {mask : Word} {bank : List Word} {v : Word} :
    availableBinB mask bank v = true ↔ AvBin mask bank v := by
  simp [availableBinB, AvBin, or_assoc]

def stockWordBin (mask : Word) (stock needed : List Word) (word : Word) : List Word :=
  let v := normWord mask (word &&& mask)
  if availableBinB mask stock v || needed.contains v then needed else v :: needed

def recipeStartBin (mask : Word) (stock words : List Word) : List Word :=
  (List.rec (motive := fun _ => List Word → List Word) id
    (fun word _ next seen => next (stockWordBin mask stock seen word)) words) []

def recipeClosureBin (mask : Word) (stock : List Word) (history : List (Word × Word × Word))
    (start : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) id
    (fun (out, a, b) _ next seen =>
      next (if seen.contains (normWord mask (out &&& mask)) then
        stockWordBin mask stock (stockWordBin mask stock seen a) b else seen))
    history start

def recipeGateBin (mask : Word) (bank : List Word) (w a b : Word) : Bool :=
  availableBinB mask bank a && availableBinB mask bank b &&
    (w == normWord mask (a &&& b) || w == normWord mask (a ||| b) ||
     w == normWord mask (a &&& (mask ^^^ b)) || w == normWord mask ((mask ^^^ a) &&& b))

theorem recipeGateBin_spec {mask : Word} {bank : List Word} {v a b : Word}
    (ma : Masked mask a) (mb : Masked mask b)
    (h : recipeGateBin mask bank v a b = true) : GateBin mask bank v := by
  simp only [recipeGateBin, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, availableBinB_spec] at h
  obtain ⟨⟨ha, hb⟩, eq⟩ := h
  rcases eq with ((rfl | rfl) | rfl) | rfl
  · exact gateBin_normBinOp4 (op := 0) (by decide) ma mb ha hb
  · exact gateBin_normBinOp4 (op := 1) (by decide) ma mb ha hb
  · exact gateBin_normBinOp4 (op := 2) (by decide) ma mb ha hb
  · exact gateBin_normBinOp4 (op := 3) (by decide) ma mb ha hb

def replayRecipesBin (mask : Word) (needed : List Word) (recipes : List (Word × Word × Word))
    (bank : List Word) : List Word :=
  List.rec (motive := fun _ => List Word → List Word) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := normWord mask (w &&& mask)
      if needed.contains v && !availableBinB mask bank v &&
          recipeGateBin mask bank v (a &&& mask) (b &&& mask) then
        v :: next (v :: bank)
      else next bank) recipes bank

theorem replayRecipesBinBuilds (mask : Word) (needed : List Word) (recipes : List (Word × Word × Word))
    (bank : List Word) : WordBuildsBin mask bank (replayRecipesBin mask needed recipes bank) := by
  induction recipes generalizing bank with
  | nil => trivial
  | cons recipe recipes ih =>
    obtain ⟨w, a, b⟩ := recipe
    change WordBuildsBin mask bank
      (if needed.contains (normWord mask (w &&& mask)) && !availableBinB mask bank (normWord mask (w &&& mask)) &&
          recipeGateBin mask bank (normWord mask (w &&& mask)) (a &&& mask) (b &&& mask) then
        normWord mask (w &&& mask) :: replayRecipesBin mask needed recipes (normWord mask (w &&& mask) :: bank)
      else replayRecipesBin mask needed recipes bank)
    split
    · rename_i yes
      exact ⟨recipeGateBin_spec (restrictWord mask a) (restrictWord mask b) (Bool.and_eq_true_iff.mp yes).2, ih _⟩
    · exact ih _

def dagBoundClosesBin (target : Word) (state : RowState) (bound : Bound) : Bool :=
  let (mask, stock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    dagForceWord (fuel - flatCount mask ws) (fun remaining =>
      if Nat.blt remaining lower then
        dagForceWords (recipeStartBin mask stock ws) (fun start =>
          if Nat.blt (start.length + remaining) lower then
            dagForceWords (recipeClosureBin mask stock history start) (fun needed =>
              if Nat.blt (needed.length + remaining) lower then
                dagForceWords (replayRecipesBin mask needed history.reverse stock) (fun replay =>
                  decide (replay.length + remaining < lower) &&
                    ws.all (fun w => availableBinB mask (replay ++ stock) (w &&& mask)))
              else false)
          else false)
      else false)

def dagKnownClosesBin (target : Word) (bounds : List Bound) (state : RowState) : Bool :=
  List.rec false (fun bound _ later => dagBoundClosesBin target state bound || later) bounds

def KnownBin (bounds : List Bound) : Prop :=
  ∀ bound ∈ bounds, BinLower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1

theorem extendKnownBin {bound : Bound} {bounds : List Bound}
    (old : KnownBin bounds)
    (new : BinLower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1) :
    KnownBin (bound :: bounds) := by
  intro x h
  rcases List.mem_cons.mp h with rfl | h
  · exact new
  · exact old _ h

def BinViable (mask target : Word) (state : RowState) : Prop :=
  state.2.1.Nodup ∧ ∃ k, k ≤ state.1 ∧ LiveBin mask target k state.2.1.toFinset

theorem boundClosesBinSound {mask target : Word} {state : RowState} {bound : Bound}
    (known : BinLower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (submask : mask &&& bound.1 = bound.1)
    (viable : BinViable mask target state) :
    dagBoundClosesBin target state bound = false := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨cut, stock, minimum, goal⟩ := bound
  obtain ⟨nd, k, steps, live⟩ := viable
  change k ≤ fuel at steps
  change LiveBin mask target k ws.toFinset at live
  apply Bool.eq_false_iff.mpr
  intro hc
  let needed := recipeClosureBin cut stock history (recipeStartBin cut stock ws)
  let replay := replayRecipesBin cut needed history.reverse stock
  simp only [dagBoundClosesBin, dagForceWordEq, dagForceWordsEq, Nat.blt_eq,
    Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hc
  obtain ⟨⟨⟨goalEq, nonzero⟩, nonflat⟩, scan⟩ := hc
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  rcases Bool.and_eq_true_iff.mp scan with ⟨length, sources⟩
  simp only [decide_eq_true_eq] at length
  have hlen : replay.length + (fuel - flatCount cut ws) < minimum := length
  have pn : ¬maskedFlat cut target := by simpa [maskedFlat, goalEq] using And.intro nonzero nonflat
  obtain ⟨n, hn, build⟩ := maskedBuildBin live cut submask pn
  rw [← flatCountCard cut nd] at hn
  change n + flatCount cut ws ≤ k at hn
  have supply : ∀ w ∈ projectedStock cut ws.toFinset, AvBin cut (replay ++ stock) w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image,
      List.mem_toFinset] at hw
    rcases hw with rfl | rfl | ⟨v, hv, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact availableBinB_spec.mp (List.all_eq_true.mp sources v hv)
  obtain ⟨ys, hy, built, avail⟩ := buildableBinWords build supply
  have both := buildsBin_append (replayRecipesBinBuilds cut needed history.reverse stock) built
  have hit : AvBin cut ((replay ++ ys) ++ stock) goal := by
    rw [← goalEq]
    exact avBin_weaken (fun v hv => Or.inr (Or.inr (Or.inl (by
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using hv)))) avail
  have enough := known (replay ++ ys) both hit
  simp only [List.length_append] at enough
  omega

theorem knownClosesBinSound {mask target : Word} {bounds : List Bound} {state : RowState}
    (known : KnownBin bounds) (submask : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (viable : BinViable mask target state) :
    dagKnownClosesBin target bounds state = false := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (dagBoundClosesBin target state bound || dagKnownClosesBin target bounds state) = false
    rw [boundClosesBinSound (known _ List.mem_cons_self) (submask _ List.mem_cons_self) viable]
    exact ih (fun b hb => known b (List.mem_cons_of_mem _ hb))
      (fun b hb => submask b (List.mem_cons_of_mem _ hb))

theorem boundClosesBinFastSound {mask target : Word} {state : RowState} {bound : Bound}
    (known : BinLower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (submask : mask &&& bound.1 = bound.1)
    (viable : BinViable mask target state) :
    dagBoundClosesBinFast target state (bound.1, bound.2.1.map (normWord bound.1), bound.2.2.1, bound.2.2.2) = false := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨cut, stock, minimum, goal⟩ := bound
  obtain ⟨nd, k, steps, live⟩ := viable
  change k ≤ fuel at steps
  change LiveBin mask target k ws.toFinset at live
  apply Bool.eq_false_iff.mpr
  intro hc
  let nstock := stock.map (normWord cut)
  let needed := recipeClosureBinF cut nstock history (recipeStartBinF cut nstock ws)
  let replay := replayRecipesBinF cut needed history.reverse nstock
  simp only [dagBoundClosesBinFast, dagForceWordEq, dagForceWordsEq, flatCountF_eq, normWordFast_eq,
    Nat.blt_eq, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hc
  obtain ⟨⟨⟨goalEq, nonzero⟩, nonflat⟩, scan⟩ := hc
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  rcases Bool.and_eq_true_iff.mp scan with ⟨length, sources⟩
  have hlen : replay.length + (fuel - flatCount cut ws) < minimum := Nat.blt_eq.mp length
  have pn : ¬maskedFlat cut target := by simpa [maskedFlat, goalEq] using And.intro nonzero nonflat
  obtain ⟨n, hn, build⟩ := maskedBuildBin live cut submask pn
  rw [← flatCountCard cut nd] at hn
  change n + flatCount cut ws ≤ k at hn
  have hnst : ∀ x ∈ nstock, AvBin cut stock x := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    rcases normWord_eq_or cut s with e | e
    · rw [e]; exact Or.inr (Or.inr (Or.inl hs))
    · rw [e]; exact Or.inr (Or.inr (Or.inr (by rwa [xor_cancel_left])))
  have hrep := (replayRecipesBinFBuilds cut needed history.reverse stock nstock hnst).1
  have hbank : ∀ x ∈ replay ++ nstock, AvBin cut (replay ++ stock) x := by
    intro x hx
    rcases List.mem_append.mp hx with hr | hs
    · exact Or.inr (Or.inr (Or.inl (List.mem_append_left stock hr)))
    · exact avBin_weaken (fun y hy => Or.inr (Or.inr (Or.inl (List.mem_append_right replay hy)))) (hnst x hs)
  have supply : ∀ w ∈ projectedStock cut ws.toFinset, AvBin cut (replay ++ stock) w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image,
      List.mem_toFinset] at hw
    rcases hw with rfl | rfl | ⟨v, hv, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact availableNormB_spec (restrictWord cut v) hbank (List.all_eq_true.mp sources v hv)
  obtain ⟨ys, hy, built, avail⟩ := buildableBinWords build supply
  have both := buildsBin_append hrep built
  have hit : AvBin cut ((replay ++ ys) ++ stock) goal := by
    rw [← goalEq]
    exact avBin_weaken (fun v hv => Or.inr (Or.inr (Or.inl (by
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using hv)))) avail
  have enough := known (replay ++ ys) both hit
  simp only [List.length_append] at enough
  omega

theorem knownClosesBinNoHdrSound {mask target : Word} {bounds : List Bound} {state : RowState}
    (known : KnownBin bounds) (submask : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (hdr : ∀ b ∈ bounds, dagBoundHeaderOK target b = true)
    (viable : BinViable mask target state) :
    dagKnownClosesBinNoHdr (bounds.map (fun b => (b.1, b.2.1.map (normWord b.1), b.2.2.1, b.2.2.2))) state = false := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (dagBoundClosesBinNoHdr state (bound.1, bound.2.1.map (normWord bound.1), bound.2.2.1, bound.2.2.2) ||
      dagKnownClosesBinNoHdr (bounds.map (fun b => (b.1, b.2.1.map (normWord b.1), b.2.2.1, b.2.2.2))) state) = false
    have h1 := boundClosesBinFastSound (known _ List.mem_cons_self) (submask _ List.mem_cons_self) viable
    have hh := hdr bound List.mem_cons_self
    have heq : dagBoundClosesBinNoHdr state (bound.1, bound.2.1.map (normWord bound.1), bound.2.2.1, bound.2.2.2) =
        dagBoundClosesBinFast target state (bound.1, bound.2.1.map (normWord bound.1), bound.2.2.1, bound.2.2.2) := by
      obtain ⟨f, ws, hist⟩ := state
      obtain ⟨m, st, lo, g⟩ := bound
      simp only [dagBoundHeaderOK] at hh
      simp only [dagBoundClosesBinNoHdr, dagBoundClosesBinFast, hh, Bool.true_and]
    rw [heq, h1]
    exact ih (fun b hb => known b (List.mem_cons_of_mem _ hb))
      (fun b hb => submask b (List.mem_cons_of_mem _ hb))
      (fun b hb => hdr b (List.mem_cons_of_mem _ hb))

theorem buildsBinMap {m n : Word} (f : Word → Word)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots bank : List Word}
    (supply : ∀ v ∈ roots, AvBin n bank (f v))
    {values : List Word} (h : WordBuildsBin m roots values) :
    WordBuildsBin n bank (values.map f) := by
  have av {bank roots : List Word} {v : Word}
      (src : ∀ v ∈ roots, AvBin n bank (f v))
      (h : AvBin m roots v) : AvBin n bank (f v) := by
    rcases h with rfl | rfl | hv | hv
    · exact Or.inl zero
    · exact Or.inr (Or.inl ones)
    · exact src _ hv
    · have h1 := src _ hv; rw [invert] at h1; simpa [xor_cancel_left] using avBin_not h1
  induction values generalizing roots bank with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨?_, ih ?_ h.2⟩
    · rcases h.1 with ⟨a, b, ha, hb, eq | eq⟩
      · exact ⟨f a, f b, av supply ha, av supply hb, Or.inl (eq ▸ meet a b)⟩
      · exact ⟨f a, f b, av supply ha, av supply hb, Or.inr (eq ▸ join a b)⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
      · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hx)))) (supply _ hw)

theorem lowerBinMap {m n : Word} (f : Word → Word)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots bank : List Word} {goal : Word} {minimum : Nat}
    (supply : ∀ v ∈ roots, AvBin n bank (f v))
    (bound : BinLower n bank (f goal) minimum) :
    BinLower m roots goal minimum := by
  intro values build hit
  suffices AvBin n (values.map f ++ bank) (f goal) by
    simpa using bound (values.map f) (buildsBinMap f zero ones invert meet join supply build) this
  rcases hit with rfl | rfl | mem | mem
  · exact Or.inl zero
  · exact Or.inr (Or.inl ones)
  · rcases List.mem_append.mp mem with hv | hr
    · exact Or.inr (Or.inr (Or.inl (List.mem_append_left _ (List.mem_map_of_mem hv))))
    · exact avBin_weaken (fun w hw => Or.inr (Or.inr (Or.inl (List.mem_append_right _ hw)))) (supply _ hr)
  · rcases List.mem_append.mp mem with hv | hr
    · have h1 : f (m ^^^ goal) ∈ values.map f ++ bank := List.mem_append_left _ (List.mem_map_of_mem hv)
      rw [invert] at h1
      exact Or.inr (Or.inr (Or.inr h1))
    · have h1 := supply _ hr
      rw [invert] at h1
      exact avBin_weaken (fun w hw => Or.inr (Or.inr (Or.inl (List.mem_append_right _ hw))))
        (by simpa [xor_cancel_left] using avBin_not h1)

theorem suppliesBinOfCheck {oldMask : Word} {old new : List Word} {rename : Word → Word}
    (h : new.all (fun w => availableBinB oldMask old (rename w)) = true) :
    ∀ w ∈ new, AvBin oldMask old (rename w) := by
  intro w hw
  exact availableBinB_spec.mp (List.all_eq_true.mp h w hw)

def dagShiftCheckBin (width mask goal oldMask oldGoal : Word) (stock old : List Word) (move : WordMove) : Bool :=
  Nat.beq (mask &&& fullMask width) mask && dagShiftUnique mask move width 0 &&
    Nat.beq (dagShift mask move mask) oldMask && Nat.beq (dagShift mask move goal) oldGoal &&
    stock.all (fun w => availableBinB oldMask old (dagShift mask move w))

theorem dagShiftLowerBin {width mask goal oldMask oldGoal : Word} {stock old : List Word} {min : Nat}
    (move : WordMove) (origin : BinLower oldMask old oldGoal min)
    (ok : dagShiftCheckBin width mask goal oldMask oldGoal stock old move = true) :
    BinLower mask stock goal min := by
  simp only [dagShiftCheckBin, Bool.and_eq_true, Nat.beq_eq] at ok
  obtain ⟨⟨⟨⟨bounded, unique⟩, masks⟩, goals⟩, supply⟩ := ok
  obtain ⟨andG, orG, xorG⟩ := dagShiftGates bounded unique
  have zero : dagShift mask move 0 = 0 := by
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr; rw [dagShiftLinear]; simp
  apply lowerBinMap (dagShift mask move) zero masks (fun w => by rw [xorG, masks]) andG orG (suppliesBinOfCheck supply)
  rwa [goals]

def gateTokenBin (a b op keep : Nat) : Nat := ((a * 64 + b) * 4 + op) * 4 + keep

theorem gateTokenBinFields {a b op keep : Nat} (hb : b < 64) (ho : op < 4) (hk : keep < 4) :
    gateTokenBin a b op keep % 4 = keep ∧
    gateTokenBin a b op keep / 4 % 4 = op ∧
    gateTokenBin a b op keep / (4 * 4 * 64) = a ∧
    gateTokenBin a b op keep / (4 * 4) % 64 = b := by
  unfold gateTokenBin; omega

def normStock (mask : Word) (stock : List Word) : List Word :=
  List.rec [] (fun w _ rest => insertWord (normWord mask w) rest) stock

theorem normStockSet (mask : Word) (stock : List Word) :
    (normStock mask stock).toFinset = (stock.map (normWord mask)).toFinset := by
  induction stock with
  | nil => simp [normStock]
  | cons w ws ih =>
    change (insertWord (normWord mask w) (normStock mask ws)).toFinset = _
    rw [insertWordSet, ih]; simp

def childStateBin (mask token : Nat) (state : RowState) : Option RowState :=
  let (fuel, ws, history) := state
  let keep := token % 4
  let op := (token / 4) % 4
  let a := token / (4 * 4 * 64)
  let b := (token / (4 * 4)) % 64
  if fuel == 0 || b ≥ ws.length || a ≥ b then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let w := normBinOp4 mask op x y
    if w == 0 || w == mask || ws.contains w then none
    else
      let rest := if keep.testBit 0 then ws else ws.erase x
      let rest := if keep.testBit 1 then rest else rest.erase y
      some (fuel - 1, insertWord w rest, (w, x, y) :: history)

def dagDirectChildBin (mask : Word) (state : RowState) (a b op keep x y out : Nat) : Option RowState :=
  let (fuel, ws, history) := state
  if fuel == 0 || b ≥ ws.length || a ≥ b then none
  else if out == 0 || out == mask || ws.contains out then none
  else
    let rest := keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
    some (fuel - 1, insertWord out rest, (out, x, y) :: history)

theorem dagDirectChildBinEq {mask a b op keep : Nat} {state : RowState}
    (hb : b < 64) (hop : op < 4) (hk : keep < 4) :
    let x := state.2.1.getD a 0
    let y := state.2.1.getD b 0
    dagDirectChildBin mask state a b op keep x y (normBinOp4 mask op x y) =
      childStateBin mask (gateTokenBin a b op keep) state := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨keepEq, opEq, aEq, bEq⟩ := gateTokenBinFields (a := a) hb hop hk
  simp only [childStateBin, dagDirectChildBin, keepWord, keepEq, opEq, aEq, bEq]

def dagTraceBin (mask : Word) (nstock : List Word) (fuel : Nat) (forest : Forest)
    (i : Nat) : Option RowState :=
  (Nat.rec (motive := fun _ => Nat → Option RowState) (fun _ => none)
    (fun _ previous j =>
      let (parent, token) := forest j
      if parent == 0 then
        if token < 2 ^ nstock.length then some (rootState nstock fuel token) else none
      else (previous (parent - 1)).bind (childStateBin mask token)) (fuel + 1)) i

def dagMoveWordsBin (mask : Word) (m : WordMove) (ws : List Word) : List Word :=
  List.rec [] (fun w _ next => insertWord (normWord mask (mixMove m w)) next) ws

theorem dagMoveSetBin {mask : Word} {m : WordMove} {ws : List Word} {select : Fin rows → Fin rows}
    (agree : ∀ w ∈ ws, mixMove m w = relabel select w) :
    (dagMoveWordsBin mask m ws).toFinset = ws.toFinset.image (fun w => normWord mask (relabel select w)) := by
  induction ws with
  | nil => simp [dagMoveWordsBin]
  | cons w ws ih =>
    change (insertWord (normWord mask (mixMove m w)) (dagMoveWordsBin mask m ws)).toFinset = _
    rw [insertWordSet, ih (fun u hu => agree _ (List.mem_cons_of_mem _ hu)),
      agree _ List.mem_cons_self, List.toFinset_cons, Finset.image_insert]

def dagRefBin (mask : Word) (count : Nat) (states : Nat → Option RowState)
    (moves : Array WordMove) (links : DagLinks) (parent token : Nat) (state : RowState) : Bool :=
  match links parent token with
  | none => false
  | some (destination, auto) =>
    Nat.blt destination count &&
      match states destination with
      | none => false
      | some saved =>
        saved.1 == state.1 &&
          if auto == 0 then saved.2.1 == state.2.1
          else match moves[auto - 1]? with
               | none => false
               | some m => saved.2.1 == dagMoveWordsBin mask m state.2.1

theorem liveBinMaskedImage {mask goal : Word} {select : Fin rows → Fin rows}
    (auto : DagAuto mask goal select) (maskBounds : Masked (fullMask rows) mask)
    {k : Nat} {S : Finset Word} (live : LiveBin mask goal k S)
    (masked : ∀ w ∈ S, Masked mask w) :
    LiveBin mask goal k (S.image (fun w => normWord mask (relabel select w))) := by
  let g := relabel select
  let f := fun w => normWord mask (g w)
  have hmask : g mask = mask := auto.2.1
  have hxor (w : Word) : g (mask ^^^ w) = mask ^^^ g w := by dsimp only [g]; rw [relabelXor, auto.2.1]
  have fnrm (w : Word) : f (normWord mask w) = f w := by
    rcases normWord_eq_or mask w with h | h
    · rw [h]
    · simp only [f, h, hxor, normWord_symm]
  have injG {a b : Word} (ma : Masked mask a) (mb : Masked mask b) : g a = g b → a = b :=
    relabelInj select auto.1 (maskedBelow maskBounds ma) (maskedBelow maskBounds mb)
  have injF {a b : Word} (ma : Masked mask a) (mb : Masked mask b)
      (na : normWord mask a = a) (nb : normWord mask b = b) (eq : f a = f b) : a = b := by
    have hrel : g a = g b ∨ g a = mask ^^^ g b := by
      rcases normWord_eq_or mask (g a) with ea | ea <;> rcases normWord_eq_or mask (g b) with eb | eb
      · left; exact ea.symm.trans (eq.trans eb)
      · right; exact ea.symm.trans (eq.trans eb)
      · right
        have h1 : mask ^^^ g a = g b := ea.symm.trans (eq.trans eb)
        have := congrArg (fun z => mask ^^^ z) h1; rw [xor_cancel_left] at this; exact this
      · left
        have h1 : mask ^^^ g a = mask ^^^ g b := ea.symm.trans (eq.trans eb)
        have := congrArg (fun z => mask ^^^ z) h1; rw [xor_cancel_left, xor_cancel_left] at this; exact this
    rcases hrel with h1 | h1
    · exact injG ma mb h1
    · rw [← hxor] at h1
      have h2 := injG ma (masked_xor mb) h1
      rw [← na, h2, normWord_symm, nb]
  have properF {a : Word} (ma : Masked mask a) (ha : properWord mask a) : properWord mask (f a) := by
    apply proper_norm
    exact ⟨fun eq => ha.1 (injG ma (by simp [Masked]) (eq.trans (relabelZero select).symm)),
      fun eq => ha.2 (injG ma (by simp [Masked]) (eq.trans hmask.symm))⟩
  have freshImage {T : Finset Word} {v : Word} (hv : v ∉ T) (mv : Masked mask v) (nv : normWord mask v = v)
      (ms : ∀ w ∈ T, Masked mask w) (ns : ∀ w ∈ T, normWord mask w = w) : f v ∉ T.image f := by
    intro hw
    obtain ⟨w, hs, eq⟩ := Finset.mem_image.mp hw
    exact hv (injF (ms w hs) mv (ns w hs) nv eq ▸ hs)
  have opImage {a b : Word} (ma : Masked mask a) (mb : Masked mask b) {op : Nat} (hop : op < 4) :
      ∃ op', op' < 4 ∧ f (normBinOp4 mask op a b) = normBinOp4 mask op' (f a) (f b) := by
    have mfa : Masked mask (f a) := masked_norm (maskedTransfer hmask ma)
    have mfb : Masked mask (f b) := masked_norm (maskedTransfer hmask mb)
    have ga_rel : g a = f a ∨ g a = mask ^^^ f a := by
      rcases normWord_eq_or mask (g a) with h | h
      · exact Or.inl h.symm
      · right; have := congrArg (fun z => mask ^^^ z) h; rw [xor_cancel_left] at this; exact this.symm
    have gb_rel : g b = f b ∨ g b = mask ^^^ f b := by
      rcases normWord_eq_or mask (g b) with h | h
      · exact Or.inl h.symm
      · right; have := congrArg (fun z => mask ^^^ z) h; rw [xor_cancel_left] at this; exact this.symm
    have hstep : f (normBinOp4 mask op a b) = normWord mask (binOp4 mask op (g a) (g b)) := by
      rw [normBinOp4, fnrm]
      have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · simp [f, binOp4, g, relabelAnd]
      · simp [f, binOp4, g, relabelOr]
      · simp [f, binOp4, g, relabelAnd, hxor]
      · simp [f, binOp4, g, relabelAnd, hxor]
    rw [hstep]
    have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
    rcases hcase with rfl | rfl | rfl | rfl <;> rcases ga_rel with hga | hga <;> rcases gb_rel with hgb | hgb
    · exact ⟨0, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨2, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨3, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨1, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ f a) &&& (mask ^^^ f b)) = _; rw [← demorgan_or mfa mfb, normWord_symm]; rfl⟩
    · exact ⟨1, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨3, by decide, by
        rw [hga, hgb]; change normWord mask (f a ||| (mask ^^^ f b)) = _
        have h1 : mask ^^^ ((mask ^^^ f a) &&& f b) = f a ||| (mask ^^^ f b) := by
          rw [demorgan_and (masked_xor mfa) mfb, xor_cancel_left]
        rw [← h1, normWord_symm]; rfl⟩
    · exact ⟨2, by decide, by
        rw [hga, hgb]; change normWord mask ((mask ^^^ f a) ||| f b) = _
        have h1 : mask ^^^ (f a &&& (mask ^^^ f b)) = (mask ^^^ f a) ||| f b := by
          rw [demorgan_and mfa (masked_xor mfb), xor_cancel_left]
        rw [← h1, normWord_symm]; rfl⟩
    · exact ⟨0, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ f a) ||| (mask ^^^ f b)) = _; rw [← demorgan_and mfa mfb, normWord_symm]; rfl⟩
    · exact ⟨2, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨0, by decide, by rw [hga, hgb]; change normWord mask (f a &&& (mask ^^^ (mask ^^^ f b))) = _; rw [xor_cancel_left]; rfl⟩
    · exact ⟨1, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ f a) &&& (mask ^^^ f b)) = _; rw [← demorgan_or mfa mfb, normWord_symm]; rfl⟩
    · exact ⟨3, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ f a) &&& (mask ^^^ (mask ^^^ f b))) = _; rw [xor_cancel_left]; rfl⟩
    · exact ⟨3, by decide, by rw [hga, hgb]; rfl⟩
    · exact ⟨1, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ f a) &&& (mask ^^^ f b)) = _; rw [← demorgan_or mfa mfb, normWord_symm]; rfl⟩
    · exact ⟨0, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ (mask ^^^ f a)) &&& f b) = _; rw [xor_cancel_left]; rfl⟩
    · exact ⟨2, by decide, by rw [hga, hgb]; change normWord mask ((mask ^^^ (mask ^^^ f a)) &&& (mask ^^^ f b)) = _; rw [xor_cancel_left]; rfl⟩
  induction live using LiveBin.ind with
  | stop hp =>
    rw [Finset.image_singleton]
    have hfg : f (normWord mask goal) = normWord mask goal := by
      rw [fnrm]; simp only [f, g, auto.2.2]
    change LiveBin mask goal 0 {f (normWord mask goal)}
    rw [hfg]
    exact LiveBin.stop hp
  | @step k U a b op hop pa pb ab na nb fresh tail ih =>
    let v := normBinOp4 mask op a b
    have ma := masked a (Finset.mem_insert_self ..)
    have mb := masked b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have mv : Masked mask v := by
      apply masked_norm
      have hcase : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 := by omega
      rcases hcase with rfl | rfl | rfl | rfl
      · exact masked_gateBin (bank := [a, b]) (by simpa using And.intro ma mb)
          ⟨a, b, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inl rfl⟩
      · exact masked_gateBin (bank := [a, b]) (by simpa using And.intro ma mb)
          ⟨a, b, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inr rfl⟩
      · exact masked_gateBin (bank := [a, b]) (by simpa using And.intro ma mb)
          ⟨a, mask ^^^ b, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inr (by rw [xor_cancel_left]; simp))), Or.inl rfl⟩
      · exact masked_gateBin (bank := [a, b]) (by simpa using And.intro ma mb)
          ⟨mask ^^^ a, b, Or.inr (Or.inr (Or.inr (by rw [xor_cancel_left]; simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inl rfl⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU))
    have hns : ∀ w ∈ insert a (insert b U), normWord mask w = w := fun w hw =>
      (liveBinProps (LiveBin.step hop pa pb ab na nb fresh tail) w hw).2
    obtain ⟨op', hop', fve⟩ := opImage ma mb hop
    have ht := ih hnew
    have hf := freshImage fresh mv (normWord_idem mask _) masked hns
    change LiveBin mask goal (k + 1) ((insert a (insert b U)).image f)
    rw [Finset.image_insert] at ht
    change LiveBin mask goal k (insert (f v) (U.image f)) at ht
    rw [fve] at ht
    rw [Finset.image_insert, Finset.image_insert, fve] at hf
    rw [Finset.image_insert, Finset.image_insert]
    exact LiveBin.step hop' (properF ma pa) (properF mb pb)
      (fun h => ab (injF ma mb na nb h)) (normWord_idem mask _) (normWord_idem mask _) hf ht

theorem dagLinkedBin {mask goal : Word} {width count : Nat} {states : Nat → Option RowState}
    {moves : Array WordMove} {links : DagLinks} {parent token : Nat} {state : RowState}
    (bounds : Masked (fullMask width) mask)
    (valid : DagMovesOK mask goal width moves)
    (masked : ∀ w ∈ state.2.1, Masked mask w)
    (ok : dagRefBin mask count states moves links parent token state = true)
    {k : Nat} (live : LiveBin mask goal k state.2.1.toFinset) :
    ∃ i saved, i < count ∧ states i = some saved ∧ saved.1 = state.1 ∧
      LiveBin mask goal k saved.2.1.toFinset := by
  unfold dagRefBin at ok
  split at ok
  · contradiction
  next destination auto h =>
    have hd := Nat.blt_eq.mp (Bool.and_eq_true_iff.mp ok).1
    have finish := (Bool.and_eq_true_iff.mp ok).2
    cases eq : states destination with
    | none => simp [eq] at finish
    | some saved =>
      simp only [eq, Bool.and_eq_true, beq_iff_eq] at finish
      refine ⟨destination, saved, hd, eq, finish.1, ?_⟩
      have last := finish.2
      split at last
      · have same : saved.2.1 = state.2.1 := beq_iff_eq.mp last
        rwa [same]
      · split at last
        · contradiction
        next m hm =>
          obtain ⟨select, hauto, agree⟩ := valid _ _ hm
          have same : saved.2.1 = dagMoveWordsBin mask m state.2.1 := beq_iff_eq.mp last
          rw [same, dagMoveSetBin (fun w hw => agree w (masked w hw))]
          exact liveBinMaskedImage hauto bounds live (fun w hw => masked _ (List.mem_toFinset.mp hw))

def dagLocalBinFast (mask goal ngoal negGoal : Word) (cut : CutCheck) (state : RowState) : Bool :=
  let (fuel, ws, _) := state
  ws.length > fuel + 1 ||
    (!ws.contains ngoal &&
      (fuel == 0 || cut state || !dagPartition false ws goal negGoal))

def dagLocalBin (mask goal : Word) (cut : CutCheck) (state : RowState) : Bool :=
  let (fuel, ws, _) := state
  ws.length > fuel + 1 ||
    (!ws.contains (normWord mask goal) &&
      (fuel == 0 || cut state || !dagPartition false ws goal (mask ^^^ goal)))

theorem dagLocalBinFast_eq (mask goal : Word) (cut : CutCheck) (state : RowState) :
    dagLocalBinFast mask goal (normWord mask goal) (mask ^^^ goal) cut state =
      dagLocalBin mask goal cut state := rfl

theorem dagLocalBinOpen {mask goal : Word} {cut : CutCheck} {state : RowState}
    (masked : Masked mask goal) (viable : BinViable mask goal state) (noCut : cut state = false) :
    dagLocalBin mask goal cut state = false := by
  obtain ⟨fuel, ws, history⟩ := state
  have ⟨nd, k, cap, live⟩ := viable
  change k ≤ fuel at cap
  have card := liveBinSize live
  rw [List.toFinset_card_of_nodup nd] at card
  change ws.length ≤ k + 1 at card
  have fit : ¬ ws.length > fuel + 1 := by omega
  by_cases hz : fuel = 0
  · have kz : k = 0 := by omega
    subst k
    obtain ⟨eq, _⟩ := live
    have hm : normWord mask goal ∈ ws := List.mem_toFinset.mp (by rw [eq]; simp)
    simp [dagLocalBin, fit, hm]
  have sep := dagPartitionLiveBin masked live
  simp [dagLocalBin, fit, hz, sep, noCut]

def dagSizeFloorBin (n keep : Nat) : Nat :=
  (n - (if keep.testBit 0 then 0 else 1) - (if keep.testBit 1 then 0 else 1)) + 1

def dagTooWideBin (n fuel token : Nat) : Bool :=
  dagSizeFloorBin n (token % 4) > (fuel - 1) + 1

theorem dagWideChildBin {mask token : Nat} {state child : RowState}
    (eval : childStateBin mask token state = some child)
    (wide : dagTooWideBin state.2.1.length state.1 token = true) :
    child.2.1.length > child.1 + 1 := by
  obtain ⟨fuel, ws, history⟩ := state
  let keep := token % 4
  let op := token / 4 % 4
  let i := token / (4 * 4 * 64)
  let j := token / (4 * 4) % 64
  let x := ws.getD i 0
  let y := ws.getD j 0
  let z := normBinOp4 mask op x y
  let a := keep.testBit 0
  let b := keep.testBit 1
  let rest := keepWord b y (keepWord a x ws)
  let bad : Bool := fuel == 0 || j ≥ ws.length || i ≥ j
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z, x, y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb, hs] at eval
  have eq : (fuel - 1, insertWord z rest, (z, x, y) :: history) = child := by simpa [hb, hs] using eval
  rw [← eq]
  change (insertWord z rest).length > fuel - 1 + 1
  rw [dagInsertLength]
  have h1 := dagKeepLength a x ws
  have h2 := dagKeepLength b y (keepWord a x ws)
  have h : ws.length - (if a then 0 else 1) - (if b then 0 else 1) + 1 > fuel - 1 + 1 :=
    of_decide_eq_true wide
  dsimp only [rest]
  omega

def dagTagStepBin (mask full token : Word) (bank : List DagTagged) : List DagTagged :=
  let keep := token % 4
  let op := token / 4 % 4
  let x := bank.getD (token / (4 * 4 * 64)) (0, 0, 0)
  let y := bank.getD (token / (4 * 4) % 64) (0, 0, 0)
  let raw := binOp4 mask op x.1 y.1
  let comp := mask ^^^ raw
  let up0 := binOp4 full op x.2.1 y.2.1
  let dn0 := binOp4 full op x.2.2 y.2.2
  let tag := if raw < comp then (raw, up0, dn0) else (comp, full ^^^ up0, full ^^^ dn0)
  dagTagInsert tag (dagTagKeep (keep.testBit 1) y.1 (dagTagKeep (keep.testBit 0) x.1 bank))

def dagTraceTagsBin (mask width : Word) (root : List DagTagged) (fuel : Nat) (forest : Forest)
    (i : Nat) : List DagSignals :=
  let tags := (Nat.rec (motive := fun _ => Nat → List DagTagged) (fun _ => [])
    (fun _ previous j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then dagTagRoot root token
      else dagTagStepBin mask (fullMask width) token (previous (parent - 1))) (fuel + 1)) i
  List.rec [] (fun tag _ rest => tag.2 :: rest) tags

def dagCheckChildrenBin (mask goal : Word) (cut : CutCheck)
    (reference : Nat → RowState → Bool) (state : RowState) (sample : DagSample) (tags : List DagSignals) : Bool :=
  let n := state.2.1.length
  dagForceWord (normWordFast mask goal) (fun ngoal =>
  dagForceWord (mask ^^^ goal) (fun negGoal =>
  (n ≤ 64) && !state.2.1.contains ngoal &&
  dagForceWord (dagPackWords256 state.2.1) (fun packed =>
    dagForceWord (dagLaneMarks256 n) (fun marks =>
      dagForceCache tags (fun tags =>
    dagForceWord (fullMask sample.2) (fun full =>
      dagCountSigns false full tags (fun normal =>
        treeBlock 0 n (fun a =>
          dagForceWord (state.2.1.getD a 0) (fun x =>
            dagForceWord (1 <<< (256 * a)) (fun aBit =>
              let xs := tags.getD a (0, 0)
              dagForceWord (dagSignalContrast false full xs) (fun xC =>
                treeBlock (a + 1) (n - (a + 1)) (fun b =>
                  dagForceWord (state.2.1.getD b 0) (fun y =>
                    dagForceWord (1 <<< (256 * b)) (fun bBit =>
                      let ys := tags.getD b (0, 0)
                      dagForceWord (dagSignalContrast false full ys) (fun yC =>
                        treeBlock 0 4 (fun op =>
                          dagForceWord (normBinOp4Fast mask op x y) (fun out =>
                            if out == 0 || out == mask || state.2.1.contains out then true else
                            dagForceWord (binOp4 full op xs.1 ys.1) (fun up =>
                              dagForceWord (binOp4 full op xs.2 ys.2) (fun down =>
                                dagForceWord (dagSignalContrast false full (up, down)) (fun outC =>
                                  treeBlock 0 4 (fun keep =>
                                    let ka := keep.testBit 0
                                    let kb := keep.testBit 1
                                    let nAfter := n - (if ka then 0 else 1) - (if kb then 0 else 1) + 1
                                    if Nat.blt state.1 nAfter then true
                                    else if dagSampleKill256 sample full normal xC yC outC packed marks aBit bBit out false ka kb then true
                                    else match dagDirectChildBin mask state a b op keep x y out with
                                    | none => true
                                    | some (fuel, ws, history) => dagForceWords ws (fun forced =>
                                      let child := (fuel, forced, history)
                                      let token := gateTokenBin a b op keep
                                      reference token child || dagLocalBinFast mask goal ngoal negGoal cut child))))))))))))))))))))))

theorem dagEarlyOpenBin256 {mask goal a b op keep out : Nat} {state child : RowState}
    {sample : DagSample} (full : Word) (counts : DagCounts) (xC yC outC : Word)
    (masked : Masked mask goal) (viable : BinViable mask goal child)
    (parent : state.2.1.Nodup) (svalid : dagSampleValid mask goal sample = true)
    (eval : dagDirectChildBin mask state a b op keep
      (state.2.1.getD a 0) (state.2.1.getD b 0) out = some child) :
    dagSampleKill256 sample full counts xC yC outC
      (dagPackWords256 state.2.1) (dagLaneMarks256 state.2.1.length)
      (1 <<< (256 * a)) (1 <<< (256 * b)) out false (keep.testBit 0) (keep.testBit 1) = false := by
  obtain ⟨fuel, ws, history⟩ := state
  let x := ws.getD a 0
  let y := ws.getD b 0
  apply Bool.eq_false_iff.mpr
  intro closed
  unfold dagSampleKill256 at closed
  simp only [dagForceWordEq] at closed
  generalize hmiss :
    (((counts.2.2 ||| (counts.2.1 ^^^ (counts.2.1 &&& (if keep.testBit 0 then 0 else xC) &&& (if keep.testBit 1 then 0 else yC))) |||
       (counts.1 ^^^ (counts.1 &&& ((if keep.testBit 0 then 0 else xC) ||| (if keep.testBit 1 then 0 else yC))))) ||| outC) ^^^ full) = missing at closed
  by_cases hm : Nat.beq missing 0 = true
  · simp only [hm, ite_true] at closed; cases closed
  · simp only [Bool.not_eq_true] at hm
    simp only [hm, Bool.false_eq_true, ite_false] at closed
    by_cases hlt : Nat.blt (dagHighest7 missing) sample.2 = true
    · simp only [hlt, ite_true] at closed
      have hidx : dagHighest7 missing < sample.2 := Nat.blt_eq.mp hlt
      have pairOK := treeBlock_at svalid (Nat.zero_le _) (by simpa using hidx)
      have closed' := dagPackedPair256Sound parent pairOK closed
      let bad : Bool := fuel == 0 || b ≥ ws.length || a ≥ b
      let stale : Bool := out == 0 || out == mask || ws.contains out
      let bank := keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
      change (if bad then none else if stale then none else
        some (fuel - 1, insertWord out bank, (out, x, y) :: history)) = some child at eval
      by_cases h : bad = true
      · simp [h] at eval
      by_cases h' : stale = true
      · simp [h, h'] at eval
      have eq : (fuel - 1, insertWord out bank, (out, x, y) :: history) = child := by simpa [h, h'] using eval
      subst child
      obtain ⟨nd, k, cap, live⟩ := viable
      have same : (out :: bank).toFinset = (insertWord out bank).toFinset := by
        ext w
        simp only [List.mem_toFinset, List.mem_cons, insertWordMem]
      have refuses := dagPairsOpenBin (pairs := [unpack sample.1 18 (dagHighest7 missing)]) masked
        (show LiveBin mask goal k (out :: bank).toFinset by rwa [same])
      exact Bool.noConfusion (closed'.symm.trans refuses)
    · simp only [Bool.not_eq_true] at hlt
      simp only [hlt, Bool.false_eq_true, ite_false] at closed

theorem dagChildAtBin {mask goal : Word} {cut : CutCheck} {ref : Nat → RowState → Bool}
    {state child : RowState} {sample : DagSample} {tags : List DagSignals} {a b op keep : Nat}
    (checked : dagCheckChildrenBin mask goal cut ref state sample tags = true)
    (svalid : dagSampleValid mask goal sample = true)
    (ha : a < state.2.1.length) (hab : a < b) (hb : b < state.2.1.length) (hop : op < 4) (hk : keep < 4)
    (eval : childStateBin mask (gateTokenBin a b op keep) state = some child)
    (masked : Masked mask goal) (viable : BinViable mask goal child) (nd : state.2.1.Nodup)
    (openChild : dagLocalBin mask goal cut child = false) :
    ref (gateTokenBin a b op keep) child = true := by
  have narrow : Nat.blt state.1 (state.2.1.length - (if keep.testBit 0 then 0 else 1) - (if keep.testBit 1 then 0 else 1) + 1) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hlt : state.1 < state.2.1.length - (if keep.testBit 0 then 0 else 1) - (if keep.testBit 1 then 0 else 1) + 1 := Nat.blt_eq.mp h
    have hb64 : b < 64 := by
      simp only [dagCheckChildrenBin, dagForceWordEq, dagForceCacheEq, dagCountSignsEq, normWordFast_eq,
        Bool.and_eq_true, decide_eq_true_eq] at checked
      omega
    obtain ⟨ke, _, _, _⟩ := gateTokenBinFields (a := a) hb64 hop hk
    have hpos : 0 < state.1 := by
      rcases state with ⟨sf, sws, shist⟩
      by_contra! hz
      have h0 : sf = 0 := by omega
      subst h0
      simp [childStateBin] at eval
    have hwide : dagTooWideBin state.2.1.length state.1 (gateTokenBin a b op keep) = true := by
      simp only [dagTooWideBin, dagSizeFloorBin, ke, decide_eq_true_eq]
      omega
    have tooMany := dagWideChildBin eval hwide
    obtain ⟨f, w, path⟩ := child
    simp [dagLocalBin, tooMany] at openChild
  simp only [dagCheckChildrenBin, dagForceCacheEq, dagForceWordEq, dagCountSignsEq, normWordFast_eq, normBinOp4Fast_eq,
    Bool.and_eq_true, decide_eq_true_eq] at checked
  have width := checked.1.1
  have atA := treeBlock_at checked.2 (i := a) (Nat.zero_le _) (by simpa using ha)
  have atB := treeBlock_at atA (i := b) (by omega) (by omega)
  have atOp := treeBlock_at atB (i := op) (Nat.zero_le _) (by simpa using hop)
  have fields := dagDirectChildBinEq (mask := mask) (state := state) (a := a) (b := b) (op := op)
    (keep := keep) (by omega) hop hk
  have direct := fields.trans eval
  have notStale : (normBinOp4 mask op (state.2.1.getD a 0) (state.2.1.getD b 0) == 0 ||
      normBinOp4 mask op (state.2.1.getD a 0) (state.2.1.getD b 0) == mask ||
      state.2.1.contains (normBinOp4 mask op (state.2.1.getD a 0) (state.2.1.getD b 0))) = false := by
    apply Bool.eq_false_iff.mpr
    intro hs
    rcases state with ⟨f, ws, hist⟩
    dsimp only [dagDirectChildBin] at hs direct
    by_cases hbad : (f == 0 || b ≥ ws.length || a ≥ b) = true
    · simp only [hbad, ite_true] at direct; cases direct
    · simp only [Bool.not_eq_true] at hbad
      simp only [hbad, Bool.false_eq_true, ite_false, hs, ite_true] at direct
      cases direct
  simp only [notStale, Bool.false_eq_true, ite_false] at atOp
  have atKeep := treeBlock_at atOp (i := keep) (Nat.zero_le _) (by simpa using hk)
  have early := fun full counts xC yC outC => dagEarlyOpenBin256 full counts xC yC outC masked viable nd svalid direct
  rcases child with ⟨fuel, ws, history⟩
  simpa only [narrow, Bool.false_eq_true, ite_false, fields, eval, dagForceWordsEq, early,
    dagLocalBinFast_eq, openChild, Bool.or_false] using atKeep

def HasChildBin (mask : Nat) (state child : RowState) : Prop :=
  ∃ a b op keep, a < state.2.1.length ∧ a < b ∧ b < state.2.1.length ∧ op < 4 ∧ keep < 4 ∧
    childStateBin mask (gateTokenBin a b op keep) state = some child

theorem binaryChildBin {mask fuel a b op : Nat} {ws : List Word}
    {history : List (Word × Word × Word)} {x y : Word} {keep : Nat}
    (hop : op < 4) (hab : a < b) (hb : b < ws.length) (hb64 : b < 64)
    (hf : fuel ≠ 0) (hk : keep < 4)
    (hx : ws.getD a 0 = x) (hy : ws.getD b 0 = y)
    (p : properWord mask (normBinOp4 mask op x y)) (fresh : normBinOp4 mask op x y ∉ ws) :
    childStateBin mask (gateTokenBin a b op keep) (fuel, ws, history) =
      some (fuel - 1, insertWord (normBinOp4 mask op x y)
        (keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)),
        (normBinOp4 mask op x y, x, y) :: history) := by
  obtain ⟨ke, ope, aa, bb⟩ := gateTokenBinFields (a := a) hb64 hop hk
  simp only [childStateBin, ke, ope, aa, bb, hx, hy]
  simp_all [Nat.not_le_of_lt hab, Nat.not_le_of_lt hb, keepWord, properWord]

theorem stepProgressBin {mask fuel k op : Nat} {x y target : Word} {U : Finset Word}
    {ws : List Word} {history : List (Word × Word × Word)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel) (hop : op < 4)
    (he : ws.toFinset = insert x (insert y U)) (xy : x ≠ y)
    (ordered : ws.idxOf x < ws.idxOf y) (fresh : normBinOp4 mask op x y ∉ insert x (insert y U))
    (tail : LiveBin mask target k (insert (normBinOp4 mask op x y) U)) :
    ∃ child, HasChildBin mask (fuel, ws, history) child ∧ BinViable mask target child := by
  let a := ws.idxOf x
  let b := ws.idxOf y
  have xm : x ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ym : y ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ha : a < ws.length := List.idxOf_lt_length_iff.mpr xm
  have hb : b < ws.length := List.idxOf_lt_length_iff.mpr ym
  have hab : a < b := ordered
  have hx : ws.getD a 0 = x := getWord xm
  have hy : ws.getD b 0 = y := getWord ym
  let v := normBinOp4 mask op x y
  have p := (liveBinProps tail v (Finset.mem_insert_self _ _)).1
  let saveX := decide (x ∈ U)
  let saveY := decide (y ∈ U)
  let keep := (if saveX then 1 else 0) + (if saveY then 2 else 0)
  have fields : keep < 4 ∧ keep.testBit 0 = saveX ∧ keep.testBit 1 = saveY := by
    unfold keep; cases saveX <;> cases saveY <;> decide
  obtain ⟨keepLt, bx, by'⟩ := fields
  have fn : v ∉ ws := by simpa [← List.mem_toFinset, he] using fresh
  let rest := keepWord saveY y (keepWord saveX x ws)
  let child : RowState := (fuel - 1, insertWord v rest, (v, x, y) :: history)
  refine ⟨child, ⟨a, b, op, keep, ha, hab, hb, hop, keepLt, ?_⟩, ?_⟩
  · have eq := binaryChildBin (fuel := fuel) (history := history) hop hab hb (by omega) (by omega) keepLt hx hy p fn
    rw [bx, by'] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup (keepNodup nd saveX x) saveY y)
      (fun h => fn (keepSubset saveX x ws _ (keepSubset saveY y _ _ h))), k, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveBin mask target k (insertWord v rest).toFinset
    rw [insertWordSet, keepPairSet nd xy he]
    exact tail

theorem wordProgressBin {mask target : Word} {state : RowState}
    (width : state.2.1.length ≤ 64) (h : BinViable mask target state) :
    normWord mask target ∈ state.2.1 ∨ ∃ child, HasChildBin mask state child ∧ BinViable mask target child := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨nd, k, cap, live⟩ := h
  cases k with
  | zero =>
    obtain ⟨eq, _⟩ := live
    left
    change ws.toFinset = {normWord mask target} at eq
    rw [← List.mem_toFinset, eq]; simp
  | succ k =>
    right
    obtain ⟨U, x, y, op, hop, eq, px, py, xy, nx, ny, fresh, tail⟩ := live
    have xm : x ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have ym : y ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have diff : ws.idxOf x ≠ ws.idxOf y := by
      intro same; apply xy; rw [← getWord xm, same, getWord ym]
    by_cases hord : ws.idxOf x < ws.idxOf y
    · exact stepProgressBin nd width cap hop eq xy hord fresh tail
    · have eq' : ws.toFinset = insert y (insert x U) := by rw [eq, Finset.insert_comm]
      have fresh' : normBinOp4 mask (swapOp4 op) y x ∉ insert y (insert x U) := by
        rw [normBinOp4_swap mask hop, Finset.insert_comm]; exact fresh
      have tail' : LiveBin mask target k (insert (normBinOp4 mask (swapOp4 op) y x) U) := by
        rw [normBinOp4_swap mask hop]; exact tail
      exact stepProgressBin nd width cap (swapOp4_lt hop) eq' xy.symm (by omega) fresh' tail'

theorem childStateBinData {mask token : Nat} {state child : RowState}
    (eval : childStateBin mask token state = some child)
    (masked : ∀ w ∈ state.2.1, Masked mask w) :
    child.1 < state.1 ∧ ∀ w ∈ child.2.1, Masked mask w := by
  obtain ⟨fuel, ws, history⟩ := state
  let keep := token % 4
  let op := token / 4 % 4
  let a := token / (4 * 4 * 64)
  let b := token / (4 * 4) % 64
  let x := ws.getD a 0
  let y := ws.getD b 0
  let z := normBinOp4 mask op x y
  let rest := keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
  let bad : Bool := fuel == 0 || b ≥ ws.length || a ≥ b
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z, x, y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb, hs] at eval
  have eq : (fuel - 1, insertWord z rest, (z, x, y) :: history) = child := by simpa [hb, hs] using eval
  subst child
  have pos : 0 < fuel := by
    by_contra! h
    have he : fuel = 0 := by omega
    simp [bad, he] at hb
  refine ⟨by dsimp; omega, ?_⟩
  have mx : Masked mask x := readWordMasked masked a
  have my : Masked mask y := readWordMasked masked b
  have hm : Masked mask z := by
    apply masked_norm
    unfold binOp4
    split
    · exact masked_gateBin (bank := [x, y]) (by simpa using And.intro mx my)
        ⟨x, y, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inl rfl⟩
    split
    · exact masked_gateBin (bank := [x, y]) (by simpa using And.intro mx my)
        ⟨x, y, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inr rfl⟩
    split
    · exact masked_gateBin (bank := [x, y]) (by simpa using And.intro mx my)
        ⟨x, mask ^^^ y, Or.inr (Or.inr (Or.inl (by simp))), Or.inr (Or.inr (Or.inr (by rw [xor_cancel_left]; simp))), Or.inl rfl⟩
    · exact masked_gateBin (bank := [x, y]) (by simpa using And.intro mx my)
        ⟨mask ^^^ x, y, Or.inr (Or.inr (Or.inr (by rw [xor_cancel_left]; simp))), Or.inr (Or.inr (Or.inl (by simp))), Or.inl rfl⟩
  intro w hw
  rcases insertWordMem.mp hw with rfl | other
  · exact hm
  · apply masked w
    apply keepSubset (keep.testBit 0) x ws w
    exact keepSubset (keep.testBit 1) y _ w other

def dagCheckNodeBin (mask goal : Word) (nodeBounds : Nat → List Bound)
    (count : Nat) (states : Nat → Option RowState) (moves : Array WordMove) (linkList : DagLinkList)
    (sample : DagSample) (tags : Nat → List DagSignals) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, history) =>
    dagForceWord goal (fun goal' =>
      dagFilterForceBoundsBin goal' (nodeBounds i) (fun activeBounds =>
        dagForceLinkList (linkList (i + 1)) (fun nlinks =>
          dagForceWords ws (fun forced =>
            dagStateOK mask forced && dagCheckChildrenBin mask goal' (dagKnownClosesBinNoHdr activeBounds)
              (dagRefBin mask count states moves (fun _ tok => dagFindLink nlinks tok) 0)
              (fuel, forced, history) sample (tags i)))))

def dagAllowedRootBin (mask : Word) (witnesses : List Witness) (ws : List Word) : Bool :=
  witnesses.all (fun entry => ws.contains (normWord mask (witnessWord entry)))

def dagCheckRootsBin (mask goal : Word) (cut : CutCheck)
    (witnesses : List Witness) (reference : Nat → RowState → Bool) (nstock : List Word)
    (fuel : Nat) : Bool :=
  treeBlock 0 (2 ^ nstock.length) fun token =>
    let state := rootState nstock fuel token
    !dagAllowedRootBin mask witnesses state.2.1 || dagLocalBin mask goal cut state || reference token state

theorem dagAllNodesBin {mask goal : Word} {width fuel count : Nat}
    {nstock : List Word} {nodeBounds : Nat → List Bound} {forest : Forest} {moves : Array WordMove}
    {linkList : DagLinkList} {sample : DagSample} {tags : Nat → List DagSignals}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal)
    (svalid : dagSampleValid mask goal sample = true)
    (cutSound : ∀ i s, BinViable mask goal s →
      dagKnownClosesBinNoHdr (((nodeBounds i).filter (dagBoundHeaderOK goal)).map
        (fun b => (b.1, b.2.1.map (normWord b.1), b.2.2.1, b.2.2.2))) s = false)
    (autos : DagMovesOK mask goal width moves)
    (verified : treeBlock 0 count (dagCheckNodeBin mask goal nodeBounds count
      (dagTraceBin mask nstock fuel forest) moves linkList sample tags) = true) :
    ∀ cap i saved, i < count → dagTraceBin mask nstock fuel forest i = some saved →
      saved.1 = cap → ∀ k, k ≤ cap → ¬LiveBin mask goal k saved.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i s iBound stateEq sFuel k kBound live
    rcases s with ⟨remaining, words, history⟩
    let s : RowState := (remaining, words, history)
    let states := dagTraceBin mask nstock fuel forest
    change states i = some s at stateEq
    have checked := treeBlock_at verified (Nat.zero_le i) (by simpa using iBound)
    change dagCheckNodeBin mask goal nodeBounds count states moves linkList sample tags i = true at checked
    simp only [dagCheckNodeBin, stateEq, dagForceWordEq, dagFilterForceBoundsBinEq, dagForceLinkListEq,
      dagForceWordsEq, Bool.and_eq_true] at checked
    obtain ⟨nd, masked⟩ := dagStateOKSpec checked.1
    have ok := checked.2
    have viable : BinViable mask goal s := ⟨nd, k, sFuel ▸ kBound, live⟩
    have scanned := ok
    simp only [dagCheckChildrenBin, dagForceWordEq, normWordFast_eq, Bool.and_eq_true, decide_eq_true_eq] at scanned
    have wide := scanned.1.1
    have absent := scanned.1.2
    rcases wordProgressBin wide viable with hit | ⟨child, possible, cv⟩
    · simpa [hit] using absent
    obtain ⟨a, b, op, keep, ha, hab, hb, hop, hk, eval⟩ := possible
    have r := dagChildAtBin ok svalid ha hab hb hop hk eval goalMask cv nd
      (dagLocalBinOpen goalMask cv (cutSound i _ cv))
    have ⟨less, cm⟩ := childStateBinData eval masked
    have below : child.1 < cap := sFuel ▸ less
    obtain ⟨_, k', fits, clive⟩ := cv
    obtain ⟨j, dest, bound, restore, fuelEq, tail⟩ := dagLinkedBin maskBounds autos cm r clive
    exact ih child.1 below j dest bound restore fuelEq k' fits tail

theorem lowerDagBin {mask goal : Word} {width fuel count : Nat}
    {stock : List Word} {forest : Forest} {moves : Array WordMove} {linkList : DagLinkList}
    {sample : DagSample} {tags : Nat → List DagSignals}
    {bounds : List Bound} {nodeBounds : Nat → List Bound} {witnesses : List Witness}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal) (proper : properWord mask goal)
    (svalid : dagSampleValid mask goal sample = true)
    (autos : DagMovesOK mask goal width moves)
    (stockMasked : ∀ w ∈ stock, Masked mask w)
    (nstockNd : (normStock mask stock).Nodup)
    (essential : witnesses.all (essentialB mask goal stock) = true)
    (known : KnownBin bounds) (submasks : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (nodeSub : ∀ i b, b ∈ nodeBounds i → b ∈ bounds)
    (rootCheck : dagCheckRootsBin mask goal (dagKnownClosesBin goal bounds) witnesses
      (dagRefBin mask count (dagTraceBin mask (normStock mask stock) fuel forest) moves
        (fun p tok => dagFindLink (linkList p) tok) 0)
      (normStock mask stock) fuel = true)
    (nodeCheck : treeBlock 0 count (dagCheckNodeBin mask goal nodeBounds
      count (dagTraceBin mask (normStock mask stock) fuel forest) moves linkList sample tags) = true) :
    BinLower mask stock goal (fuel + 1) := by
  intro values build hit
  by_contra! small
  obtain ⟨k, S, hk, live, sub⟩ := extractBinLive stockMasked build hit proper
  let nstock := normStock mask stock
  have included : S ⊆ nstock.toFinset := by
    intro w hw
    rw [normStockSet, List.mem_toFinset]
    exact sub w hw
  obtain ⟨token, tokenBound, eq⟩ := rootToken nstock S
  rw [Finset.inter_eq_right.mpr included] at eq
  let state := rootState nstock fuel token
  have eq' : state.2.1.toFinset = S := eq
  have v : BinViable mask goal state := by
    refine ⟨(rootWordSublist nstock token).nodup nstockNd, k, ?_, ?_⟩
    · change k ≤ fuel; omega
    · rwa [eq']
  have cutOpen (s : RowState) (h : BinViable mask goal s) : dagKnownClosesBin goal bounds s = false :=
    knownClosesBinSound known submasks h
  have nodeCutOpen (i : Nat) (s : RowState) (h : BinViable mask goal s) :
      dagKnownClosesBinNoHdr (((nodeBounds i).filter (dagBoundHeaderOK goal)).map
        (fun b => (b.1, b.2.1.map (normWord b.1), b.2.2.1, b.2.2.2))) s = false :=
    knownClosesBinNoHdrSound
      (fun b hb => known b (nodeSub i b (List.mem_filter.mp hb).1))
      (fun b hb => submasks b (nodeSub i b (List.mem_filter.mp hb).1))
      (fun b hb => (List.mem_filter.mp hb).2) h
  have openRoot := dagLocalBinOpen goalMask v (cutOpen _ v)
  have allowed : dagAllowedRootBin mask witnesses state.2.1 = true := by
    apply List.all_eq_true.mpr
    intro entry mem
    apply List.contains_iff_mem.mpr
    rw [← List.mem_toFinset, eq']
    exact essentialRequiredBin (List.all_eq_true.mp essential entry mem) sub live
  have checked := treeBlock_at rootCheck (Nat.zero_le token) (by simpa using tokenBound)
  change (!dagAllowedRootBin mask witnesses state.2.1 || dagLocalBin mask goal (dagKnownClosesBin goal bounds) state ||
    dagRefBin mask count (dagTraceBin mask nstock fuel forest) moves
      (fun p tok => dagFindLink (linkList p) tok) 0 token state) = true at checked
  simp only [allowed, openRoot, Bool.not_true, Bool.false_or] at checked
  have finish := dagAllNodesBin maskBounds goalMask svalid nodeCutOpen autos nodeCheck
  have fits : k ≤ fuel := by omega
  have still : LiveBin mask goal k state.2.1.toFinset := by rwa [eq']
  have nstockMasked : ∀ w ∈ nstock, Masked mask w := by
    intro w hw
    have h1 : w ∈ nstock.toFinset := List.mem_toFinset.mpr hw
    rw [normStockSet, List.mem_toFinset] at h1
    obtain ⟨orig, omem, rfl⟩ := List.mem_map.mp h1
    exact masked_norm (stockMasked orig omem)
  have stateMask : ∀ w ∈ state.2.1, Masked mask w := by
    intro w hw
    exact nstockMasked _ ((rootWordSublist nstock token).subset hw)
  obtain ⟨i, s, hi, restore, cap, plan⟩ := dagLinkedBin maskBounds autos stateMask checked still
  exact finish fuel i s hi restore cap k fits plan

theorem hcsGateWordMono {rows : Nat} (bank : List (BitVec rows))
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or)
    (hlen : g.inputs.length ≤ 2) :
    GateWordMono (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank g).toNat := by
  obtain ⟨op, ins⟩ := g
  have zeroAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) 0 := Or.inl rfl
  have maskAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) (fullMask rows) := Or.inr (Or.inl rfl)
  rcases hop with rfl | rfl
  · cases ins with
    | nil => exact gateMonoOfAvailable (by simpa [hcsGateVal, fullMask] using maskAv)
    | cons a t =>
      cases t with
      | nil => exact gateMonoOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inl (by simp [hcsGateVal, BitVec.toNat_and])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact gateMonoOfAvailable (by simpa [hcsGateVal] using zeroAv)
    | cons a t =>
      cases t with
      | nil => exact gateMonoOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inr (by simp [hcsGateVal, BitVec.toNat_or])⟩
        | cons c t => simp at hlen

def isNotOp : PEqualNP.CircuitLowerBounds.GateOp → Bool
  | PEqualNP.CircuitLowerBounds.GateOp.not => true
  | _ => false

def countNonNot : List PEqualNP.CircuitLowerBounds.Gate → Nat
  | [] => 0
  | g :: rest => (if isNotOp g.op then 0 else 1) + countNonNot rest

theorem hcsBuildsBin {rows : Nat} (raw : List (BitVec rows)) (bank : List Word)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (sub0 : ∀ v ∈ raw, AvBin (fullMask rows) bank v.toNat)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    ∃ vs, vs.length ≤ countNonNot gs ∧ WordBuildsBin (fullMask rows) bank vs ∧
      ∀ v ∈ gs.foldl hcsStep raw, AvBin (fullMask rows) (vs ++ bank) v.toNat := by
  induction gs generalizing raw bank with
  | nil => exact ⟨[], Nat.le_refl _, trivial, fun v hv => sub0 v hv⟩
  | cons g gs ih =>
    let v := hcsGateVal raw g
    have hg := hfan g List.mem_cons_self
    have hop := hg.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    have avRaw (i : Nat) : AvBin (fullMask rows) bank (raw.getD i 0).toNat := by
      rw [List.getD_eq_getElem?_getD]
      cases h : raw[i]? with
      | none => exact Or.inl rfl
      | some a => exact sub0 a (List.mem_of_getElem? h)
    rcases hop with h_and | h_or | h_not
    · have gm : GateWordMono (fullMask rows) (raw.map BitVec.toNat) v.toNat :=
        hcsGateWordMono raw g (Or.inl h_and) hg.2
      have gbin : GateBin (fullMask rows) bank v.toNat := by
        rcases gm with ⟨a, b, ha, hb, eq⟩
        exact ⟨a, b, avBin_weaken (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact sub0 y hy) (avBin_of_av ha),
          avBin_weaken (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact sub0 y hy) (avBin_of_av hb), eq⟩
      have sub1 : ∀ u ∈ hcsStep raw g, AvBin (fullMask rows) (v.toNat :: bank) u.toNat := by
        intro u hu
        simp only [hcsStep, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hx)))) (sub0 u hu)
        · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
      obtain ⟨xs, len, built, reach⟩ := ih (hcsStep raw g) (v.toNat :: bank) sub1 (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      refine ⟨v.toNat :: xs, ?_, ⟨gbin, built⟩, fun u hu => ?_⟩
      · simp only [countNonNot, h_and, isNotOp, Bool.false_eq_true, ite_false, List.length_cons]; omega
      · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (by
          simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hx)))) (reach u hu)
    · have gm : GateWordMono (fullMask rows) (raw.map BitVec.toNat) v.toNat :=
        hcsGateWordMono raw g (Or.inr h_or) hg.2
      have gbin : GateBin (fullMask rows) bank v.toNat := by
        rcases gm with ⟨a, b, ha, hb, eq⟩
        exact ⟨a, b, avBin_weaken (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact sub0 y hy) (avBin_of_av ha),
          avBin_weaken (fun x hx => by obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx; exact sub0 y hy) (avBin_of_av hb), eq⟩
      have sub1 : ∀ u ∈ hcsStep raw g, AvBin (fullMask rows) (v.toNat :: bank) u.toNat := by
        intro u hu
        simp only [hcsStep, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ hx)))) (sub0 u hu)
        · exact Or.inr (Or.inr (Or.inl List.mem_cons_self))
      obtain ⟨xs, len, built, reach⟩ := ih (hcsStep raw g) (v.toNat :: bank) sub1 (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      refine ⟨v.toNat :: xs, ?_, ⟨gbin, built⟩, fun u hu => ?_⟩
      · simp only [countNonNot, h_or, isNotOp, Bool.false_eq_true, ite_false, List.length_cons]; omega
      · exact avBin_weaken (fun x hx => Or.inr (Or.inr (Or.inl (by
          simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hx)))) (reach u hu)
    · have hv : AvBin (fullMask rows) bank v.toNat := by
        obtain ⟨op, ins⟩ := g
        simp only at h_not; subst op
        cases ins with
        | nil =>
          have : v.toNat = fullMask rows ^^^ 0 := by simpa [v, hcsGateVal] using notNat (0 : BitVec rows)
          rw [this]; exact avBin_not (Or.inl rfl)
        | cons a _ =>
          have : v.toNat = fullMask rows ^^^ (raw.getD a 0).toNat := by
            simpa [v, hcsGateVal] using notNat (raw.getD a 0)
          rw [this]; exact avBin_not (avRaw a)
      have sub1 : ∀ u ∈ hcsStep raw g, AvBin (fullMask rows) bank u.toNat := by
        intro u hu
        simp only [hcsStep, List.mem_append, List.mem_singleton] at hu
        rcases hu with hu | rfl
        · exact sub0 u hu
        · exact hv
      obtain ⟨xs, len, built, reach⟩ := ih (hcsStep raw g) bank sub1 (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      refine ⟨xs, ?_, built, reach⟩
      simp only [countNonNot, h_not, isNotOp, ite_true, Nat.zero_add]; exact len

theorem hcsBinLowerEq {m1 m2 g1 g2 min : Nat} {b1 b2 : List Word}
    (hm : m1 = m2) (hb : b1 = b2) (hg : g1 = g2)
    (h : BinLower m1 b1 g1 min) : BinLower m2 b2 g2 min := by
  subst hm; subst hb; subst hg; exact h

def ms0 : WordMoveStep := ([((packedLimbs [0xaaaa,0x5555aaaa5555aaa,0xa5555aaaa5555aa,0xaa5555aaaa5555a,0xaaa5555aaaa5555]), 0), ((packedLimbs [0xaaaa0000aaaa000,0xaaaa0000aaaa00,0xaaaa0000aaaa0,0xaaaa0000aaaa]), 15)], [((packedLimbs [0x5555,0x55550000555,0x500005555000055,0x550000555500005,0x555000055550000]), 15)])

def ms1 : WordMoveStep := ([((packedLimbs [0x9999,0x999999999999999,0x999999999999999,0x999999999999999,0x999999999999999]), 0), ((packedLimbs [0x2222,0x222222222222222,0x222222222222222,0x222222222222222,0x222222222222222]), 1)], [((packedLimbs [0x4444,0x444444444444444,0x444444444444444,0x444444444444444,0x444444444444444]), 1)])

def ms2 : WordMoveStep := ([((packedLimbs [0xc3c3,0xc3c3c3c3c3c3c3c,0x3c3c3c3c3c3c3c3,0xc3c3c3c3c3c3c3c,0x3c3c3c3c3c3c3c3]), 0), ((packedLimbs [0xc0c,0xc0c0c0c0c0c0c0,0xc0c0c0c0c0c0c0c,0xc0c0c0c0c0c0c0,0xc0c0c0c0c0c0c0c]), 2)], [((packedLimbs [0x3030,0x303030303030303,0x30303030303030,0x303030303030303,0x30303030303030]), 2)])

def ms3 : WordMoveStep := ([((packedLimbs [0xf00f,0xf00ff00ff00ff00,0xff00ff00ff00ff0,0xff00ff00ff00ff,0xff00ff00ff00f]), 0), ((packedLimbs [0xf0,0xf000f000f000f,0xf000f000f000,0xf000f000f000f00,0xf000f000f000f0]), 4)], [((packedLimbs [0xf00,0xf000f000f000f0,0xf000f000f000f,0xf000f000f000,0xf000f000f000f00]), 4)])

def ms4 : WordMoveStep := ([((packedLimbs [0xa5a5,0xa5a5a5a5a5a5a5a,0x5a5a5a5a5a5a5a5,0xa5a5a5a5a5a5a5a,0x5a5a5a5a5a5a5a5]), 0), ((packedLimbs [0xa0a,0xa0a0a0a0a0a0a0,0xa0a0a0a0a0a0a0a,0xa0a0a0a0a0a0a0,0xa0a0a0a0a0a0a0a]), 3)], [((packedLimbs [0x5050,0x505050505050505,0x50505050505050,0x505050505050505,0x50505050505050]), 3)])

def ms5 : WordMoveStep := ([((packedLimbs [0xffffffff000,0xffffffff00,0xffffffff0,0xffffffff]), 32)], [((packedLimbs [0xffff,0xffff00000000fff,0xfffff00000000ff,0xffffff00000000f,0xfffffff00000000]), 32)])

def ms6 : WordMoveStep := ([((packedLimbs [0xff,0xff00ff00ff00f,0xf00ff00ff00ff00,0xff00ff00ff00ff0,0xff00ff00ff00ff]), 8)], [((packedLimbs [0xff00,0xff00ff00ff00ff0,0xff00ff00ff00ff,0xff00ff00ff00f,0xf00ff00ff00ff00]), 8)])

def ms7 : WordMoveStep := ([((packedLimbs [0xcccc,0xcccc33333333ccc,0xccccc33333333cc,0xcccccc33333333c,0xccccccc33333333]), 0), ((packedLimbs [0xcccccccc000,0xcccccccc00,0xcccccccc0,0xcccccccc]), 30)], [((packedLimbs [0x3333,0x333300000000333,0x333330000000033,0x333333000000003,0x333333300000000]), 30)])

def ms8 : WordMoveStep := ([((packedLimbs [0xcc33,0xcc33cc33cc33cc3,0x3cc33cc33cc33cc,0x33cc33cc33cc33c,0xc33cc33cc33cc33]), 0), ((packedLimbs [0xcc,0xcc00cc00cc00c,0xc00cc00cc00cc00,0xcc00cc00cc00cc0,0xcc00cc00cc00cc]), 6)], [((packedLimbs [0x3300,0x330033003300330,0x33003300330033,0x3300330033003,0x300330033003300]), 6)])

def ms9 : WordMoveStep := ([((packedLimbs [0xff00,0xff00ff00ff0000f,0xf00ff00ff00ffff,0xff00ff00ff000,0xff00ff00ff00ff]), 0), ((packedLimbs [0xff0,0xff00ff00ff0000,0xf,0xf00ff00ff00ff00]), 56)], [((packedLimbs [0xff,0xff00ff00ff000,0x0,0xff00ff00ff00ff0,0x0]), 56)])

def ms10 : WordMoveStep := ([((packedLimbs [0xff00,0xff0000ff00ffff0,0xff0000ff00ffff,0xff0000ff00fff,0xf00ff0000ff00ff]), 0), ((packedLimbs [0xff00ff00000,0xff00ff0000,0xff00ff000,0xff00ff00]), 24)], [((packedLimbs [0xff,0xff0000000000f,0xf00ff0000000000,0xff00ff000000000,0xff00ff00000000]), 24)])

def ms11 : WordMoveStep := ([((packedLimbs [0xff00,0xffff0000ffff0,0xffff0000ffff,0xffff0000fff,0xf0000ffff0000ff]), 0), ((packedLimbs [0xff000000ff00000,0xff000000ff0000,0xff000000ff000,0xff000000ff00]), 8)], [((packedLimbs [0xff,0xff000000f,0xf000000ff000000,0xff000000ff00000,0xff000000ff0000]), 8)])

def ms12 : WordMoveStep := ([((packedLimbs [0xffff,0xffff00000000000,0xffffffffff,0xffffff000000000,0xffffffff]), 0), ((packedLimbs [0xfff,0xfffff0000000000,0xf,0xfffffff00000000]), 32)], [((packedLimbs [0xffffffff000,0x0,0xffffffff0,0x0]), 32)])

def ms13 : WordMoveStep := ([((packedLimbs [0xffff,0xffff0000000,0xffff0000ffffff,0xff0000ffff00000,0xffff0000ffff]), 0), ((packedLimbs [0xfff,0xf0000ffff000000,0xf,0xfff0000ffff0000]), 48)], [((packedLimbs [0xffff0000ffff000,0x0,0xffff0000ffff0,0x0]), 48)])

def ms14 : WordMoveStep := ([((packedLimbs [0xffff,0xfffffff,0xf00000000ffffff,0xff00000000fffff,0xfff00000000ffff]), 0), ((packedLimbs [0xffff0000000,0xffff000000,0xffff00000,0xffff0000]), 16)], [((packedLimbs [0xffff00000000000,0xffff0000000000,0xffff000000000,0xffff00000000]), 16)])

def ms15 : WordMoveStep := ([((packedLimbs [0xf0f0,0xf0ff0f00f0ff0f,0xf0ff0f00f0ff0,0xf00f0ff0f00f0ff,0xf00f0ff0f00f0f]), 0), ((packedLimbs [0xf0f00000f0f0000,0xf0f00000f0f000,0xf0f00000f0f00,0xf0f00000f0f0]), 12)], [((packedLimbs [0xf0f,0xf0f00000f0,0xf00000f0f00000f,0xf00000f0f00000,0xf0f00000f0f0000]), 12)])

def ms16 : WordMoveStep := ([((packedLimbs [0xf0f0,0xf0f00f0f0f0ff0f,0xf0f00f0f0f0ff0,0xf0f0f00f0f0f0ff,0xf0f0f00f0f0f0f]), 0), ((packedLimbs [0xf0f0f0f0000,0xf0f0f0f000,0xf0f0f0f00,0xf0f0f0f0]), 28)], [((packedLimbs [0xf0f,0xf0f000000000f0,0xf0f0f000000000f,0xf0f0f000000000,0xf0f0f0f00000000]), 28)])

def ms17 : WordMoveStep := ([((packedLimbs [0xaa55,0xaa55aa55aa55aa5,0x5aa55aa55aa55aa,0x55aa55aa55aa55a,0xa55aa55aa55aa55]), 0), ((packedLimbs [0xaa,0xaa00aa00aa00a,0xa00aa00aa00aa00,0xaa00aa00aa00aa0,0xaa00aa00aa00aa]), 7)], [((packedLimbs [0x5500,0x550055005500550,0x55005500550055,0x5500550055005,0x500550055005500]), 7)])

def ms18 : WordMoveStep := ([((packedLimbs [0xaaaa,0xaaaa55555555aaa,0xaaaaa55555555aa,0xaaaaaa55555555a,0xaaaaaaa55555555]), 0), ((packedLimbs [0xaaaaaaaa000,0xaaaaaaaa00,0xaaaaaaaa0,0xaaaaaaaa]), 31)], [((packedLimbs [0x5555,0x555500000000555,0x555550000000055,0x555555000000005,0x555555500000000]), 31)])

def ms19 : WordMoveStep := ([((packedLimbs [0xaaaa,0xaaaaaaaaaaaa555,0x5555555555555aa,0xaaaaaaaaaaaaaa5,0x555555555555555]), 0), ((packedLimbs [0xaaa,0xaaaaaaaaaaaaa00,0xa,0xaaaaaaaaaaaaaaa]), 63)], [((packedLimbs [0x5555,0x555555555555000,0x55,0x555555555555550,0x0]), 63)])

def ms20 : WordMoveStep := ([((packedLimbs [0xf0f0,0xf0f0f0f0f0f00f0,0xf0f0f0f0f0f0ff0,0xf0f0f0f0f0f0f00,0xf0f0f0f0f0f0f0f]), 0), ((packedLimbs [0xf0f,0xf0f0f0f0f0f000,0xf,0xf0f0f0f0f0f0f0]), 60)], [((packedLimbs [0xf0f,0xf0f0f0f0f0f000,0xf,0xf0f0f0f0f0f0f0,0x0]), 60)])

def ms21 : WordMoveStep := ([((packedLimbs [0x3333,0x333333333333333,0x333333333333333,0x333333333333333,0x333333333333333]), 2)], [((packedLimbs [0xcccc,0xccccccccccccccc,0xccccccccccccccc,0xccccccccccccccc,0xccccccccccccccc]), 2)])

def ms22 : WordMoveStep := ([((packedLimbs [0xcccc,0x3333cccc3333ccc,0xc3333cccc3333cc,0xcc3333cccc3333c,0xccc3333cccc3333]), 0), ((packedLimbs [0xcccc0000cccc000,0xcccc0000cccc00,0xcccc0000cccc0,0xcccc0000cccc]), 14)], [((packedLimbs [0x3333,0x33330000333,0x300003333000033,0x330000333300003,0x333000033330000]), 14)])

def ms23 : WordMoveStep := ([((packedLimbs [0xcccc,0xcccccccccccc333,0x3333333333333cc,0xcccccccccccccc3,0x333333333333333]), 0), ((packedLimbs [0xccc,0xccccccccccccc00,0xc,0xccccccccccccccc]), 62)], [((packedLimbs [0x3333,0x333333333333000,0x33,0x333333333333330,0x0]), 62)])

def ms24 : WordMoveStep := ([((packedLimbs [0x5555,0x555555555555555,0x555555555555555,0x555555555555555,0x555555555555555]), 1)], [((packedLimbs [0xaaaa,0xaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaa]), 1)])

def sBase : List Word := [(packedLimbs [0xaaaa,0xaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaa]), (packedLimbs [0xcccc,0xccccccccccccccc,0xccccccccccccccc,0xccccccccccccccc,0xccccccccccccccc]), (packedLimbs [0xf0f0,0xf0f0f0f0f0f0f0f,0xf0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f,0xf0f0f0f0f0f0f0]), (packedLimbs [0xff00,0xff00ff00ff00ff0,0xff00ff00ff00ff,0xff00ff00ff00f,0xf00ff00ff00ff00]), (packedLimbs [0xffff,0xffff0000fff,0xf0000ffff0000ff,0xff0000ffff0000f,0xfff0000ffff0000]), (packedLimbs [0xffff,0xffff00000000fff,0xfffff00000000ff,0xffffff00000000f,0xfffffff00000000]), (packedLimbs [0xffff,0xffffffffffff000,0xff,0xffffffffffffff0,0x0]), (packedLimbs [0xffff,0xfffffffffffffff,0xfffffffffffff00,0x0,0x0])]

def sGoal : Word := (packedLimbs [0xffff,0xfffefffffefefff,0xefffcfefaee00ff,0xfffffefffffefef,0xffefffcfefaee00])

def s0M : Word := (packedLimbs [0x1100110,0x110011])

abbrev s0G : Word := sGoal &&& s0M

abbrev s0W : List Word := projectDAGStock s0M sBase [2, 4, 6]

def s0E := unpackWitnesses s0W [10256, 272388, 559108]

abbrev s0N : List Word := normStock s0M s0W

def s0C : List Bound := []

def s0S : DagSample := ((packedLimbs [0x50001100,0x14201402050201,0x100844080500814]), 9)

def s0L : DagLinkList := dagExtractLinks 0x9 0x7 2 1 3 1 1

def s0D : Forest := fun i => decodeNode 1 4 0xe i

def s0T := dagTraceTagsBin s0M 9 (dagTagBases s0N 0x4c11843 0x7ebdbd7 9) 3 s0D

def s0St := dagTraceBin s0M s0N 3 s0D

def s0Mv := dagMoves ([] : List (DagMoveRecord 256))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0A : DagMovesOK s0M s0G 256 s0Mv := dagMovesOfCheck (by decide +kernel)

def s0NB : Nat → List Bound := dagNodeBounds s0C.toArray 0 0 2 1 1

def s0Ck := dagCheckNodeBin s0M s0G s0NB 1 s0St s0Mv s0L s0S s0T

def s0RA (token : Nat) : Bool :=
  let s := rootState s0N 3 token
  !dagAllowedRootBin s0M s0E s.2.1 || dagLocalBin s0M s0G (dagKnownClosesBin s0G s0C) s ||
  dagRefBin s0M 1 s0St s0Mv (fun p tok => dagFindLink (s0L p) tok) 0 token s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0RB0 : treeBlock 0 8 s0RA = true := by decide +kernel

theorem s0RV : treeBlock 0 8 s0RA = true := s0RB0

theorem s0R : dagCheckRootsBin s0M s0G (dagKnownClosesBin s0G s0C) s0E (dagRefBin s0M 1 s0St s0Mv (fun p tok => dagFindLink (s0L p) tok) 0) s0N 3 = true := s0RV

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Bl0 : treeBlock 0 1 s0Ck = true := by decide +kernel

theorem s0Bk : treeBlock 0 1 s0Ck = true := s0Bl0

theorem s0K : KnownBin s0C := (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Bin : BinLower s0M s0W s0G 4 := by
  apply lowerDagBin _ _ _ _ s0A _ _ _ s0K _ (fun _ b hb => dagNodeBounds_mem b hb) s0R s0Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s0C, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h

def s1M : Word := (packedLimbs [0x3300330,0x330033])

abbrev s1G : Word := sGoal &&& s1M

abbrev s1W : List Word := projectDAGStock s1M sBase [0, 2, 4, 6]

def s1F : Bound := (s1M, s1W, 5, s1G)

def s1E := unpackWitnesses s1W [8720, 272400, 532993, 819713]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Bin : BinLower s1M s1W s1G 5 := by
  apply essentialLiftBin (witnesses := s1E) (cut := s0M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesBinOfCheck (old := s0W) (by decide +kernel)
  · exact s0Bin
  · decide +kernel

def s2M : Word := (packedLimbs [0x110011001100110,0x11001100110011])

abbrev s2G : Word := sGoal &&& s2M

abbrev s2W : List Word := projectDAGStock s2M sBase [2, 4, 5, 6]

def s2F : Bound := (s2M, s2W, 5, s2G)

def s2E := unpackWitnesses s2W [10256, 272388, 542724, 821252]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Bin : BinLower s2M s2W s2G 5 := by
  apply essentialLiftBin (witnesses := s2E) (cut := s0M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesBinOfCheck (old := s0W) (by decide +kernel)
  · exact s0Bin
  · decide +kernel

def s3M : Word := (packedLimbs [0x50005000500050,0x5000500050005])

abbrev s3G : Word := sGoal &&& s3M

abbrev s3W : List Word := projectDAGStock s3M sBase [1, 4, 5, 6]

def s3E := unpackWitnesses s3W [17440, 303168, 541698, 820226]

abbrev s3N : List Word := normStock s3M s3W

def s3C : List Bound := []

def s3S : DagSample := ((packedLimbs [0x6050201084032,0x10c86022090882,0x50001400042100,0x880022011080422]), 13)

def s3L : DagLinkList := dagExtractLinks 0x9 0xf 2 1 4 1 1

def s3D : Forest := fun i => decodeNode 1 5 0x1e i

def s3T := dagTraceTagsBin s3M 13 (dagTagBases s3N 0x830267f0e478d 0xebe38fd5ef7ff 13) 3 s3D

def s3St := dagTraceBin s3M s3N 3 s3D

def s3Mv := dagMoves ([] : List (DagMoveRecord 256))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s3A : DagMovesOK s3M s3G 256 s3Mv := dagMovesOfCheck (by decide +kernel)

def s3NB : Nat → List Bound := dagNodeBounds s3C.toArray 0 0 2 1 1

def s3Ck := dagCheckNodeBin s3M s3G s3NB 1 s3St s3Mv s3L s3S s3T

def s3RA (token : Nat) : Bool :=
  let s := rootState s3N 3 token
  !dagAllowedRootBin s3M s3E s.2.1 || dagLocalBin s3M s3G (dagKnownClosesBin s3G s3C) s ||
  dagRefBin s3M 1 s3St s3Mv (fun p tok => dagFindLink (s3L p) tok) 0 token s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s3RB0 : treeBlock 0 16 s3RA = true := by decide +kernel

theorem s3RV : treeBlock 0 16 s3RA = true := s3RB0

theorem s3R : dagCheckRootsBin s3M s3G (dagKnownClosesBin s3G s3C) s3E (dagRefBin s3M 1 s3St s3Mv (fun p tok => dagFindLink (s3L p) tok) 0) s3N 3 = true := s3RV

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s3Bl0 : treeBlock 0 1 s3Ck = true := by decide +kernel

theorem s3Bk : treeBlock 0 1 s3Ck = true := s3Bl0

theorem s3K : KnownBin s3C := (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s3Bin : BinLower s3M s3W s3G 4 := by
  apply lowerDagBin _ _ _ _ s3A _ _ _ s3K _ (fun _ b hb => dagNodeBounds_mem b hb) s3R s3Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s3C, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h

def s4M : Word := (packedLimbs [0x33000000330,0x3300000033])

abbrev s4G : Word := sGoal &&& s4M

abbrev s4W : List Word := projectDAGStock s4M sBase [0, 2, 5, 6]

def s4F : Bound := (s4M, s4W, 4, s4G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Bin : BinLower s4M s4W s4G 4 := dagShiftLowerBin (width := 256) [ms0, ms1, ms2, ms3] s3Bin (by decide +kernel)

def s5M : Word := (packedLimbs [0x30003000000000,0x3000300000000])

abbrev s5G : Word := sGoal &&& s5M

abbrev s5W : List Word := projectDAGStock s5M sBase [0, 4, 6]

def s5F : Bound := (s5M, s5W, 4, s5G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5Bin : BinLower s5M s5W s5G 4 := dagShiftLowerBin (width := 256) [ms4, ms1, ms5] s0Bin (by decide +kernel)

def s6M : Word := (packedLimbs [0x110011000,0x11001100])

abbrev s6G : Word := sGoal &&& s6M

abbrev s6W : List Word := projectDAGStock s6M sBase [2, 4, 6]

def s6F : Bound := (s6M, s6W, 4, s6G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Bin : BinLower s6M s6W s6G 4 := dagShiftLowerBin (width := 256) [ms6] s0Bin (by decide +kernel)

def s7M : Word := (packedLimbs [0x11,0x1100110011001,0x100110011001100])

abbrev s7G : Word := sGoal &&& s7M

abbrev s7W : List Word := projectDAGStock s7M sBase [2, 4, 5, 6]

def s7F : Bound := (s7M, s7W, 5, s7G)

def s7E := unpackWitnesses s7W [14360, 276492, 544776, 825356]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Bin : BinLower s7M s7W s7G 5 := by
  apply essentialLiftBin (witnesses := s7E) (cut := s6M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesBinOfCheck (old := s6W) (by decide +kernel)
  · exact s6Bin
  · decide +kernel

def s8M : Word := (packedLimbs [0x330033000000000,0x33003300000000])

abbrev s8G : Word := sGoal &&& s8M

abbrev s8W : List Word := projectDAGStock s8M sBase [0, 2, 4, 6]

def s8F : Bound := (s8M, s8W, 5, s8G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Bin : BinLower s8M s8W s8G 5 := dagShiftLowerBin (width := 256) [ms4, ms1, ms7, ms8] s7Bin (by decide +kernel)

def s9M : Word := 0x33003300330033

abbrev s9G : Word := sGoal &&& s9M

abbrev s9W : List Word := projectDAGStock s9M sBase [0, 2, 4, 5]

def s9F : Bound := (s9M, s9W, 4, s9G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s9Bin : BinLower s9M s9W s9G 4 := dagShiftLowerBin (width := 256) [ms0, ms1, ms2, ms3, ms9] s3Bin (by decide +kernel)

def s10M : Word := (packedLimbs [0x330033003300330,0x33003300330033])

abbrev s10G : Word := sGoal &&& s10M

abbrev s10W : List Word := projectDAGStock s10M sBase [0, 2, 4, 5, 6]

def s10F : Bound := (s10M, s10W, 7, s10G)

def s10E := unpackWitnesses s10W [8720, 272400, 532993, 804868, 1081857]

abbrev s10N : List Word := normStock s10M s10W

def s10C : List Bound := [s1F, s2F, s4F, s5F, s8F, s9F]

def s10S : DagSample := ((packedLimbs [0x80c4026100184c,0x50100446050108,0x440031001140231,0x544041109044,0x25001104224020,0x946031108c40a25,0x500050108940,0xa24109848050000,0x908044001040844,0x20502050000448,0x41009044024008,0x442014080440824]), 40)

def s10L : DagLinkList := dagExtractLinks 0xd59 0x15c28c1f 3 1 7 2 1

def s10D : Forest := fun i => decodeNode 2 9 0x5c91a7c i

def s10T := dagTraceTagsBin s10M 40 (dagTagBases s10N (packedLimbs [0x14030,0xd7715ff5864c9ea,0x609f93bc711eba0,0xc5fee8b65fb229f]) (packedLimbs [0xbdb6c,0xc7fd7ffff6ef9fe,0x7bffbffef9e1e29,0xd7fefefffffafbf]) 40) 6 s10D

def s10St := dagTraceBin s10M s10N 6 s10D

def s10Mv := dagMoves ([] : List (DagMoveRecord 256))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10A : DagMovesOK s10M s10G 256 s10Mv := dagMovesOfCheck (by decide +kernel)

def s10NB : Nat → List Bound := dagNodeBounds s10C.toArray 0x121605 0x3445688 7 3 3

def s10Ck := dagCheckNodeBin s10M s10G s10NB 3 s10St s10Mv s10L s10S s10T

def s10RA (token : Nat) : Bool :=
  let s := rootState s10N 6 token
  !dagAllowedRootBin s10M s10E s.2.1 || dagLocalBin s10M s10G (dagKnownClosesBin s10G s10C) s ||
  dagRefBin s10M 3 s10St s10Mv (fun p tok => dagFindLink (s10L p) tok) 0 token s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10RB0 : treeBlock 0 32 s10RA = true := by decide +kernel

theorem s10RV : treeBlock 0 32 s10RA = true := s10RB0

theorem s10R : dagCheckRootsBin s10M s10G (dagKnownClosesBin s10G s10C) s10E (dagRefBin s10M 3 s10St s10Mv (fun p tok => dagFindLink (s10L p) tok) 0) s10N 6 = true := s10RV

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10Bl0 : treeBlock 0 3 s10Ck = true := by decide +kernel

theorem s10Bk : treeBlock 0 3 s10Ck = true := s10Bl0

theorem s10K : KnownBin s10C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) s9Bin) s8Bin) s5Bin) s4Bin) s2Bin) s1Bin)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10Bin : BinLower s10M s10W s10G 7 := by
  apply lowerDagBin _ _ _ _ s10A _ _ _ s10K _ (fun _ b hb => dagNodeBounds_mem b hb) s10R s10Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s10C, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def s11M : Word := (packedLimbs [0x333333330,0x33333333])

abbrev s11G : Word := sGoal &&& s11M

abbrev s11W : List Word := projectDAGStock s11M sBase [0, 2, 3, 4, 6]

def s11F : Bound := (s11M, s11W, 7, s11G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s11Bin : BinLower s11M s11W s11G 7 := dagShiftLowerBin (width := 256) [ms4, ms10] s10Bin (by decide +kernel)

def s12M : Word := (packedLimbs [0x1111000011110,0x111100001111])

abbrev s12G : Word := sGoal &&& s12M

abbrev s12W : List Word := projectDAGStock s12M sBase [2, 3, 5, 6]

def s12F : Bound := (s12M, s12W, 4, s12G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Bin : BinLower s12M s12W s12G 4 := dagShiftLowerBin (width := 256) [ms2, ms11, ms12] s3Bin (by decide +kernel)

def s13M : Word := 0x1111111111111111

abbrev s13G : Word := sGoal &&& s13M

abbrev s13W : List Word := projectDAGStock s13M sBase [2, 3, 4, 5]

def s13F : Bound := (s13M, s13W, 4, s13G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Bin : BinLower s13M s13W s13G 4 := dagShiftLowerBin (width := 256) [ms2, ms11, ms10, ms9] s3Bin (by decide +kernel)

def s14M : Word := (packedLimbs [0x11,0x111111111111111,0x111111111111111])

abbrev s14G : Word := sGoal &&& s14M

abbrev s14W : List Word := projectDAGStock s14M sBase [2, 3, 4, 5, 6]

def s14F : Bound := (s14M, s14W, 7, s14G)

def s14E := unpackWitnesses s14W [10256, 282656, 534532, 804868, 1083396]

abbrev s14N : List Word := normStock s14M s14W

def s14C : List Bound := [s2F, s12F, s6F, s13F, s7F]

def s14S : DagSample := ((packedLimbs [0x1014041,0xa0205800070201c,0x300906028100e00,0x34040e0c070181,0xc030140c140181c,0x6130084c241103,0x1c060909028020,0xb000440c0a01844,0x2070181400090c,0x68001406038000,0xa090680c0e00014,0x201102050201404,0x24080501028021,0x104028020500824]), 45)

def s14L : DagLinkList := dagExtractLinks 0xe38c70341 (packedLimbs [0x403cb84ba8433,0x4b20431023001f]) 6 3 12 3 1

def s14D : Forest := fun i => decodeNode 2 9 0xf396c351a7c i

def s14T := dagTraceTagsBin s14M 45 (dagTagBases s14N (packedLimbs [0xc6e8121f994,0x84bc52b43f5a300,0xefccc976e03f8b9,0xf553f947ae6c77]) (packedLimbs [0x1fff8d63fff4,0x3fb0865f3f7eaf1,0xef7edb7fe33fffd,0x7f77f7bf6feed7f]) 45) 6 s14D

def s14St := dagTraceBin s14M s14N 6 s14D

def s14Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 6, 5, 4, 7] 0 i.val)

def s14Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 6, 5, 4, 7] 0 i.val)

def s14Mv := dagMoves ([([ms13], s14Mp0, s14Mi0)] : List (DagMoveRecord 256))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s14A : DagMovesOK s14M s14G 256 s14Mv := dagMovesOfCheck (by decide +kernel)

def s14NB : Nat → List Bound := dagNodeBounds s14C.toArray 0x4064a5084 0x409688 7 3 3

def s14Ck := dagCheckNodeBin s14M s14G s14NB 5 s14St s14Mv s14L s14S s14T

def s14RA (token : Nat) : Bool :=
  let s := rootState s14N 6 token
  !dagAllowedRootBin s14M s14E s.2.1 || dagLocalBin s14M s14G (dagKnownClosesBin s14G s14C) s ||
  dagRefBin s14M 5 s14St s14Mv (fun p tok => dagFindLink (s14L p) tok) 0 token s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s14RB0 : treeBlock 0 32 s14RA = true := by decide +kernel

theorem s14RV : treeBlock 0 32 s14RA = true := s14RB0

theorem s14R : dagCheckRootsBin s14M s14G (dagKnownClosesBin s14G s14C) s14E (dagRefBin s14M 5 s14St s14Mv (fun p tok => dagFindLink (s14L p) tok) 0) s14N 6 = true := s14RV

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s14Bl0 : treeBlock 0 5 s14Ck = true := by decide +kernel

theorem s14Bk : treeBlock 0 5 s14Ck = true := s14Bl0

theorem s14K : KnownBin s14C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) s7Bin) s13Bin) s6Bin) s12Bin) s2Bin)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s14Bin : BinLower s14M s14W s14G 7 := by
  apply lowerDagBin _ _ _ _ s14A _ _ _ s14K _ (fun _ b hb => dagNodeBounds_mem b hb) s14R s14Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s14C, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def s15M : Word := (packedLimbs [0x3,0x30303030303030,0x303030303030303])

abbrev s15G : Word := sGoal &&& s15M

abbrev s15W : List Word := projectDAGStock s15M sBase [0, 3, 4, 5, 6]

def s15F : Bound := (s15M, s15W, 7, s15G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Bin : BinLower s15M s15W s15G 7 := dagShiftLowerBin (width := 256) [ms4, ms1, ms10] s14Bin (by decide +kernel)

def s16M : Word := (packedLimbs [0x303000003030,0x30300000303])

abbrev s16G : Word := sGoal &&& s16M

abbrev s16W : List Word := projectDAGStock s16M sBase [0, 3, 5, 6]

def s16F : Bound := (s16M, s16W, 4, s16G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16Bin : BinLower s16M s16W s16G 4 := dagShiftLowerBin (width := 256) [ms1, ms9, ms11, ms14] s3Bin (by decide +kernel)

def s17M : Word := 0x33330000000000003333

abbrev s17G : Word := sGoal &&& s17M

abbrev s17W : List Word := projectDAGStock s17M sBase [0, 2, 3, 6]

def s17F : Bound := (s17M, s17W, 4, s17G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s17Bin : BinLower s17M s17W s17G 4 := dagShiftLowerBin (width := 256) [ms1, ms15, ms10] s3Bin (by decide +kernel)

def s18M : Word := 0x333300003333

abbrev s18G : Word := sGoal &&& s18M

abbrev s18W : List Word := projectDAGStock s18M sBase [0, 2, 3, 5]

def s18F : Bound := (s18M, s18W, 4, s18G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Bin : BinLower s18M s18W s18G 4 := dagShiftLowerBin (width := 256) [ms0, ms1, ms16, ms9, ms2] s3Bin (by decide +kernel)

def s19M : Word := (packedLimbs [0x3333000033330,0x333300003333])

abbrev s19G : Word := sGoal &&& s19M

abbrev s19W : List Word := projectDAGStock s19M sBase [0, 2, 3, 5, 6]

def s19F : Bound := (s19M, s19W, 7, s19G)

def s19E := unpackWitnesses s19W [4616, 280608, 528897, 804868, 1081857]

abbrev s19N : List Word := normStock s19M s19W

def s19C : List Bound := [s12F, s16F, s4F, s17F, s18F]

def s19S : DagSample := ((packedLimbs [0xb04025101,0xa0c028201840825,0x9840a41000940,0x4c00114c041008,0x901044108941844,0x8340a24061309,0x4c060240041028,0x94c06102824100d,0x301a04241109849,0x68000a0180d028,0x340024000240044,0x21108044201041,0x28100a00241020,0x904024040240209]), 46)

def s19L : DagLinkList := dagExtractLinks 0xc0c0b11a01 (packedLimbs [0xc1331c43,0xaa10d18338510da,0x4334908ca043080,0xcc90230404c001f]) 8 4 12 3 3

def s19D : Forest := fun i => decodeNode 2 9 0x993349a7c i

def s19T := dagTraceTagsBin s19M 46 (dagTagBases s19N (packedLimbs [0x2c135c09976c3,0xb100dbe23cd3efd,0x1c6179c0175bcd1,0xbe4f522b2b0f86f]) (packedLimbs [0x3f3d4f59dfeef,0xafe957e77dfffeb,0x1eebfbd8fedfec7,0xff6f9fbfbb6fe7f]) 46) 6 s19D

def s19St := dagTraceBin s19M s19N 6 s19D

def s19Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 5, 4, 3, 6, 7] 0 i.val)

def s19Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 5, 4, 3, 6, 7] 0 i.val)

def s19Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 5, 6, 4, 2, 3, 7] 0 i.val)

def s19Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 5, 6, 4, 2, 3, 7] 0 i.val)

def s19Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 6, 5, 7] 0 i.val)

def s19Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 6, 5, 7] 0 i.val)

def s19Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 3, 6, 4, 0, 5, 7] 0 i.val)

def s19Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 0, 2, 4, 6, 3, 7] 0 i.val)

def s19Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 0, 2, 4, 6, 3, 7] 0 i.val)

def s19Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 3, 6, 4, 0, 5, 7] 0 i.val)

def s19Mp5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 6, 3, 4, 0, 2, 7] 0 i.val)

def s19Mi5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 6, 3, 4, 0, 2, 7] 0 i.val)

def s19Mv := dagMoves ([([ms4, ms10], s19Mp0, s19Mi0), ([ms16, ms9], s19Mp1, s19Mi1), ([ms17, ms12], s19Mp2, s19Mi2), ([ms18, ms4, ms3, ms9], s19Mp3, s19Mi3), ([ms4, ms17, ms19, ms18], s19Mp4, s19Mi4), ([ms18, ms20], s19Mp5, s19Mi5)] : List (DagMoveRecord 256))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19A : DagMovesOK s19M s19G 256 s19Mv := dagMovesOfCheck (by decide +kernel)

def s19NB : Nat → List Bound := dagNodeBounds s19C.toArray 0xc30a45 0xc688 6 3 3

def s19Ck := dagCheckNodeBin s19M s19G s19NB 4 s19St s19Mv s19L s19S s19T

def s19RA (token : Nat) : Bool :=
  let s := rootState s19N 6 token
  !dagAllowedRootBin s19M s19E s.2.1 || dagLocalBin s19M s19G (dagKnownClosesBin s19G s19C) s ||
  dagRefBin s19M 4 s19St s19Mv (fun p tok => dagFindLink (s19L p) tok) 0 token s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19RB0 : treeBlock 0 32 s19RA = true := by decide +kernel

theorem s19RV : treeBlock 0 32 s19RA = true := s19RB0

theorem s19R : dagCheckRootsBin s19M s19G (dagKnownClosesBin s19G s19C) s19E (dagRefBin s19M 4 s19St s19Mv (fun p tok => dagFindLink (s19L p) tok) 0) s19N 6 = true := s19RV

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Bl0 : treeBlock 0 4 s19Ck = true := by decide +kernel

theorem s19Bk : treeBlock 0 4 s19Ck = true := s19Bl0

theorem s19K : KnownBin s19C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) s18Bin) s17Bin) s4Bin) s16Bin) s12Bin)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Bin : BinLower s19M s19W s19G 7 := by
  apply lowerDagBin _ _ _ _ s19A _ _ _ s19K _ (fun _ b hb => dagNodeBounds_mem b hb) s19R s19Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s19C, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def s20M : Word := 0x3333333333333333

abbrev s20G : Word := sGoal &&& s20M

abbrev s20W : List Word := projectDAGStock s20M sBase [0, 2, 3, 4, 5]

def s20F : Bound := (s20M, s20W, 7, s20G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s20Bin : BinLower s20M s20W s20G 7 := dagShiftLowerBin (width := 256) [ms13] s19Bin (by decide +kernel)

def s21M : Word := (packedLimbs [0x550055000,0x55005500])

abbrev s21G : Word := sGoal &&& s21M

abbrev s21W : List Word := projectDAGStock s21M sBase [1, 2, 4, 6]

def s21F : Bound := (s21M, s21W, 5, s21G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Bin : BinLower s21M s21W s21G 5 := dagShiftLowerBin (width := 256) [ms7, ms8, ms21, ms6] s7Bin (by decide +kernel)

def s22M : Word := (packedLimbs [0x55,0x5500550055005,0x500550055005500])

abbrev s22G : Word := sGoal &&& s22M

abbrev s22W : List Word := projectDAGStock s22M sBase [1, 2, 4, 5, 6]

def s22F : Bound := (s22M, s22W, 6, s22G)

def s22E := unpackWitnesses s22W [5128, 276504, 538636, 806920, 1087500]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s22Bin : BinLower s22M s22W s22G 6 := by
  apply essentialLiftBin (witnesses := s22E) (cut := s21M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesBinOfCheck (old := s21W) (by decide +kernel)
  · exact s21Bin
  · decide +kernel

def s23M : Word := (packedLimbs [0x33,0x333333000000003,0x333333300000000])

abbrev s23G : Word := sGoal &&& s23M

abbrev s23W : List Word := projectDAGStock s23M sBase [0, 2, 3, 4, 6]

def s23F : Bound := (s23M, s23W, 6, s23G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Bin : BinLower s23M s23W s23G 6 := dagShiftLowerBin (width := 256) [ms4, ms1, ms10] s22Bin (by decide +kernel)

def s24M : Word := (packedLimbs [0x3,0x30303000000000,0x303030300000000])

abbrev s24G : Word := sGoal &&& s24M

abbrev s24W : List Word := projectDAGStock s24M sBase [0, 3, 4, 6]

def s24F : Bound := (s24M, s24W, 5, s24G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s24Bin : BinLower s24M s24W s24G 5 := dagShiftLowerBin (width := 256) [ms4, ms1, ms10] s7Bin (by decide +kernel)

def s25M : Word := (packedLimbs [0x33,0x3300330033003,0x300330033003300])

abbrev s25G : Word := sGoal &&& s25M

abbrev s25W : List Word := projectDAGStock s25M sBase [0, 2, 4, 5, 6]

def s25F : Bound := (s25M, s25W, 6, s25G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Bin : BinLower s25M s25W s25G 6 := dagShiftLowerBin (width := 256) [ms1] s22Bin (by decide +kernel)

def s26M : Word := 0x303030303030303

abbrev s26G : Word := sGoal &&& s26M

abbrev s26W : List Word := projectDAGStock s26M sBase [0, 3, 4, 5]

def s26F : Bound := (s26M, s26W, 4, s26G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26Bin : BinLower s26M s26W s26G 4 := dagShiftLowerBin (width := 256) [ms1, ms9, ms14] s3Bin (by decide +kernel)

def s27M : Word := 0x33333333

abbrev s27G : Word := sGoal &&& s27M

abbrev s27W : List Word := projectDAGStock s27M sBase [0, 2, 3, 4]

def s27F : Bound := (s27M, s27W, 4, s27G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s27Bin : BinLower s27M s27W s27G 4 := dagShiftLowerBin (width := 256) [ms1, ms15, ms10, ms20, ms3] s3Bin (by decide +kernel)

def s28M : Word := (packedLimbs [0x30303030,0x3030303])

abbrev s28G : Word := sGoal &&& s28M

abbrev s28W : List Word := projectDAGStock s28M sBase [0, 3, 4, 6]

def s28F : Bound := (s28M, s28W, 5, s28G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s28Bin : BinLower s28M s28W s28G 5 := dagShiftLowerBin (width := 256) [ms4, ms1, ms10] s2Bin (by decide +kernel)

def s29M : Word := (packedLimbs [0x33,0x333333333333333,0x333333333333333])

abbrev s29G : Word := sGoal &&& s29M

abbrev s29W : List Word := projectDAGStock s29M sBase [0, 2, 3, 4, 5, 6]

def s29F : Bound := (s29M, s29W, 10, s29G)

def s29E := unpackWitnesses s29W [4616, 272400, 528897, 795137, 1067012, 1344001]

abbrev s29N : List Word := normStock s29M s29W

def s29C : List Bound := [s11F, s14F, s15F, s20F, s19F, s23F, s10F, s24F, s25F, s26F, s18F, s7F, s8F, s27F, s28F, s1F]

def s29S : DagSample := ((packedLimbs [0x80d01,0x24081600251301,0x409050200440224,0x41100a44000349,0x1c040704029241,0x240019101a09009,0x81c08070300d01,0x828300a00815040,0x640a1420130082c,0x180904031060903,0x14201a08049020,0x24c024041a03011,0x20440245020700,0x215080703009241,0x604224021144025,0x240a02031040e04,0x38021302038060,0xb0c061108a43028,0x301900a11021043,0x58301c060110c1,0x402019180d00a15,0x241300229108246,0x2804034080d200,0x500a45009846070,0x900231029041,0x814109040225061,0x30004410844301c,0x1040825061101,0x81c001404261000,0x44c068108c4020d,0x500a09028901,0x809000246031000,0xa09068201040a25,0xc0e06038028344,0x225201408044081,0x404024060342011,0x80500814100a00,0x844009041009020,0x901028008440209]), 128)

def s29L : DagLinkList := dagExtractLinks (packedLimbs [0xb,0x105882c41620b10,0x5882c41620b1058,0x82c41620b00d802,0xc01600af0d782bc,0x15e0ae0d702b815,0xc0ae0560aac3560,0xab05582ac1560ab,0x5582ac1522a61d,0x1128433e29f04f8,0x27c13e09f04e8a7,0x413a09d04e82741,0x3a09a1ca9648722,0x18f1441e1c30267,0xb33c0dd46d6a691,0x330d942b6a581ac,0x1600a655112805,0x308942490a4051c,0x274d362198cc824,0xad139080c05e001]) (packedLimbs [0xaa4402a00c0a6,0x440a900f0ac01c2,0xb00d0aac60a9b14,0xab460a9b141a64,0x60aa317aa6c522a,0x1178a64522a2101,0xa6c6029b142a403,0xc29007198470261,0x18078450e6b1869,0xac512880f86c032,0x1e0074784582801,0xb09e03c1a808c9c,0x3e1a00c894c612,0x6b16684c5126116,0x8664321c80f8560,0x3225812095870a1,0x3180644406101c0,0x920381480c28cc6,0xea1318862440241,0xe88c06e2101888,0xe85923210460022,0x2281b08804c2180,0xb184c612131445e,0x4322081748003e1,0xf80f47c03c1e80d,0x4520321e0074760,0x6c1d00b073462d2,0xb1087086e1b80b3,0x66c7099b1825ec5,0x5991c066460179,0x141560701581806,0xc0581481406a85c,0x5681f06802819d1,0x8864c6218b14060,0x46e1791885d06e1,0x6b1445802c15d18,0x85406e148188500,0x1d1381b04c02c12,0x90e04885911a1bb,0x3a8618ea1464484,0xb90a126408438ba,0x1053a0610e81444,0x404b10812440043,0xb8104260230f91,0x323c43e0900cc3c,0x19ce318d380630,0x880cc200330ed18,0x8390630db18c34c,0x51c5310c1e4320c,0x81b8300630b8188,0x2c0430a80f82803,0x30600c82746348c,0x18d25053c7b18a1,0xec5209218c22853,0x8210d1e4620791,0x491c06e46818d18,0x620701781a0530,0x601491604305808,0xc14c630481b8100,0x3e03c14d0ac5343,0x310f0685381a10f,0x283303114c0a44,0x30210ce02423418,0x14c060434080cc0,0x402300804c0003f]) 13 5 13 7 2

def s29D : Forest := fun i => decodeNode 6 19 (packedLimbs [0x34f68c1,0x9a10316286001ca,0x807d101b2101e42,0x3e7d8b2f1169e0,0x243b87070070e10,0xe9b42cb4841680d,0x8c8131901632c51,0x600bac00f9801eb,0x3c6006ac00758,0x362e02c5e8c4b2,0x1b960162a058510,0xb8980a13a3120c6,0x2418a0811b90231,0x2106e3d8a2780b0,0xea311a06e340c46,0x8074d0361802c30,0x8705a164a437120,0x4b200924010c822,0x60e0191e8c42418,0xc463188c51100dc,0x2018c4031080431,0x7c200cc4a3186,0x8630d0a61a10c32,0x290605e0c0a6181,0x48301186c63080d,0xc100f8282982453,0x4886090cc10218,0x202304026080fc0]) i

def s29T := dagTraceTagsBin s29M 128 (dagTagBases s29N (packedLimbs [0xedd8be7b98ac,0xbe66a9264d3928c,0xcf3cc3e07f684ee,0x18f5dfc70da28f9,0x7eca4b7dfc0394f,0x1747413bb03ff6e,0xea931f76a41e6c6,0x3af9178be80fdab,0xce55ef358fd3efb,0x41e167fa081ddaf,0xefba7622ef73c3,0x3d4fdf36f5f6d17,0x7e35352ff9f1f9f]) (packedLimbs [0xeebfffbffebb,0xff6fe9e64dfb27e,0xcffdcffbffaaddd,0x7df5e7efaf378fe,0x3edf6b7bb65bb7c,0xf3e75dbb777fb6c,0xffbb7f7eb5fffdf,0xf6fbcfbbba1efbf,0xefffef3d9fff7fb,0x75f3effaee5cdcf,0xbddfa7efaef7ff1,0xeda5df2ff77eddf,0x7dffffeff9f3fff]) 128) 9 s29D

def s29St := dagTraceBin s29M s29N 9 s29D

def s29Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 5, 4, 3, 6, 7] 0 i.val)

def s29Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 5, 4, 3, 6, 7] 0 i.val)

def s29Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 6, 5, 4, 7] 0 i.val)

def s29Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 6, 5, 4, 7] 0 i.val)

def s29Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 5, 6, 3, 4, 7] 0 i.val)

def s29Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 5, 6, 3, 4, 7] 0 i.val)

def s29Mv := dagMoves ([([ms4, ms10], s29Mp0, s29Mi0), ([ms13], s29Mp1, s29Mi1), ([ms4, ms10, ms13], s29Mp2, s29Mi2)] : List (DagMoveRecord 256))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29A : DagMovesOK s29M s29G 256 s29Mv := dagMovesOfCheck (by decide +kernel)

def s29NB : Nat → List Bound := dagNodeBounds s29C.toArray (packedLimbs [0x4502281140898,0xc4c224311188844,0x422031008804402,0x2010f187843c21c,0x30e0868c3061630,0xb0850c282141091,0x840c1c60c305182,0xc0c60430118084,0x5f88fb17d0be8,0x1f04f627a8bd41e,0xa0f41798bc49e02,0xf007803b4dcb0e2,0x36dbb4a5950c826,0x29b0156f2b4355c,0xa9d13d29b34b2a4,0x1916a87440b1e24,0xe886aa32a9850ad,0x64ca2150dec5b42,0x3a0cd04240d4006]) (packedLimbs [0x210031000401000,0x42018c0929062,0x210c01802018c00,0x188283148310409,0x20d0720c41020e6,0x290620812839862,0x81284882939062,0x4a0c520c4102481,0x4a0c520c41020e6,0x25062906208149,0x228831054628c20,0x728a303d451a925,0x20c4a418a418820,0x524625250629062,0x81a51880d28c0d,0x5a0e629062081a8,0x398a4188205a0e6,0x290620818b41cc5,0x20c410398831483,0x1040f59cc520c41,0x2507314831040a,0x418a418820620e6,0x29062080c418820]) 13 4 5

def s29Ck := dagCheckNodeBin s29M s29G s29NB 87 s29St s29Mv s29L s29S s29T

def s29RA (token : Nat) : Bool :=
  let s := rootState s29N 9 token
  !dagAllowedRootBin s29M s29E s.2.1 || dagLocalBin s29M s29G (dagKnownClosesBin s29G s29C) s ||
  dagRefBin s29M 87 s29St s29Mv (fun p tok => dagFindLink (s29L p) tok) 0 token s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29RB0 : treeBlock 0 64 s29RA = true := by decide +kernel

theorem s29RV : treeBlock 0 64 s29RA = true := s29RB0

theorem s29R : dagCheckRootsBin s29M s29G (dagKnownClosesBin s29G s29C) s29E (dagRefBin s29M 87 s29St s29Mv (fun p tok => dagFindLink (s29L p) tok) 0) s29N 9 = true := s29RV

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Bl0 : treeBlock 0 32 s29Ck = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Bl32 : treeBlock 32 32 s29Ck = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Bl64 : treeBlock 64 23 s29Ck = true := by decide +kernel

theorem s29Bk : treeBlock 0 87 s29Ck = true := (@treeBlock_merge 0 32 55 s29Ck s29Bl0 (@treeBlock_merge 32 32 23 s29Ck s29Bl32 s29Bl64))

theorem s29K : KnownBin s29C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) s1Bin) s28Bin) s27Bin) s8Bin) s7Bin) s18Bin) s26Bin) s25Bin) s24Bin) s10Bin) s23Bin) s19Bin) s20Bin) s15Bin) s14Bin) s11Bin)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Bin : BinLower s29M s29W s29G 10 := by
  apply lowerDagBin _ _ _ _ s29A _ _ _ s29K _ (fun _ b hb => dagNodeBounds_mem b hb) s29R s29Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s29C, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def s30M : Word := (packedLimbs [0xf000f000f000f0,0xf000f000f000f])

abbrev s30G : Word := sGoal &&& s30M

abbrev s30W : List Word := projectDAGStock s30M sBase [0, 1, 4, 5, 6]

def s30F : Bound := (s30M, s30W, 7, s30G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s30Bin : BinLower s30M s30W s30G 7 := dagShiftLowerBin (width := 256) [ms0, ms7, ms4, ms8, ms20] s14Bin (by decide +kernel)

def s31M : Word := (packedLimbs [0x550055005500550,0x55005500550055])

abbrev s31G : Word := sGoal &&& s31M

abbrev s31W : List Word := projectDAGStock s31M sBase [1, 2, 4, 5, 6]

def s31F : Bound := (s31M, s31W, 6, s31G)

def s31E := unpackWitnesses s31W [17440, 272400, 534532, 803842, 1082370]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Bin : BinLower s31M s31W s31G 6 := by
  apply essentialLiftBin (witnesses := s31E) (cut := s2M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesBinOfCheck (old := s2W) (by decide +kernel)
  · exact s2Bin
  · decide +kernel

def s32M : Word := (packedLimbs [0xff000000ff0,0xff000000ff])

abbrev s32G : Word := sGoal &&& s32M

abbrev s32W : List Word := projectDAGStock s32M sBase [0, 1, 2, 5, 6]

def s32F : Bound := (s32M, s32W, 5, s32G)

def s32E := unpackWitnesses s32W [33344, 279584, 542752, 803842, 1081857]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s32Bin : BinLower s32M s32W s32G 5 := by
  apply essentialLiftBin (witnesses := s32E) (cut := s4M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesBinOfCheck (old := s4W) (by decide +kernel)
  · exact s4Bin
  · decide +kernel

def s33M : Word := 0x55005500550055

abbrev s33G : Word := sGoal &&& s33M

abbrev s33W : List Word := projectDAGStock s33M sBase [1, 2, 4, 5]

def s33F : Bound := (s33M, s33W, 4, s33G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s33Bin : BinLower s33M s33W s33G 4 := dagShiftLowerBin (width := 256) [ms22, ms2, ms3, ms10, ms9] s3Bin (by decide +kernel)

def s34M : Word := 0xff00ff00ff00ff

abbrev s34G : Word := sGoal &&& s34M

abbrev s34W : List Word := projectDAGStock s34M sBase [0, 1, 2, 4, 5]

def s34F : Bound := (s34M, s34W, 5, s34G)

def s34E := unpackWitnesses s34W [8720, 279584, 534544, 795137, 1065986]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Bin : BinLower s34M s34W s34G 5 := by
  apply essentialLiftBin (witnesses := s34E) (cut := s33M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesBinOfCheck (old := s33W) (by decide +kernel)
  · exact s33Bin
  · decide +kernel

def s35M : Word := (packedLimbs [0x5500550,0x550055])

abbrev s35G : Word := sGoal &&& s35M

abbrev s35W : List Word := projectDAGStock s35M sBase [1, 2, 4, 6]

def s35F : Bound := (s35M, s35W, 5, s35G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s35Bin : BinLower s35M s35W s35G 5 := dagShiftLowerBin (width := 256) [ms7, ms15, ms8, ms20] s2Bin (by decide +kernel)

def s36M : Word := (packedLimbs [0xff00ff0,0xff00ff])

abbrev s36G : Word := sGoal &&& s36M

abbrev s36W : List Word := projectDAGStock s36M sBase [0, 1, 2, 4, 6]

def s36F : Bound := (s36M, s36W, 6, s36G)

def s36E := unpackWitnesses s36W [8720, 296000, 534544, 795137, 1081857]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Bin : BinLower s36M s36W s36G 6 := by
  apply essentialLiftBin (witnesses := s36E) (cut := s35M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesBinOfCheck (old := s35W) (by decide +kernel)
  · exact s35Bin
  · decide +kernel

def s37M : Word := (packedLimbs [0xff00ff000000000,0xff00ff00000000])

abbrev s37G : Word := sGoal &&& s37M

abbrev s37W : List Word := projectDAGStock s37M sBase [0, 1, 2, 4, 6]

def s37F : Bound := (s37M, s37W, 6, s37G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Bin : BinLower s37M s37W s37G 6 := dagShiftLowerBin (width := 256) [ms4, ms18, ms17] s22Bin (by decide +kernel)

def s38M : Word := (packedLimbs [0xf0000000f0,0xf0000000f])

abbrev s38G : Word := sGoal &&& s38M

abbrev s38W : List Word := projectDAGStock s38M sBase [0, 1, 5, 6]

def s38F : Bound := (s38M, s38W, 4, s38G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Bin : BinLower s38M s38W s38G 4 := dagShiftLowerBin (width := 256) [ms0, ms4, ms3] s3Bin (by decide +kernel)

def s39M : Word := (packedLimbs [0xff00ff00ff00ff0,0xff00ff00ff00ff])

abbrev s39G : Word := sGoal &&& s39M

abbrev s39W : List Word := projectDAGStock s39M sBase [0, 1, 2, 4, 5, 6]

def s39F : Bound := (s39M, s39W, 9, s39G)

def s39E := unpackWitnesses s39W [8720, 279584, 534544, 795137, 1065986, 1344001]

abbrev s39N : List Word := normStock s39M s39W

def s39C : List Bound := [s30F, s10F, s31F, s32F, s34F, s36F, s37F, s33F, s35F, s38F]

def s39S : DagSample := ((packedLimbs [0x20944,0x34180888061200,0x542041020446024,0x19042052029040,0xa24028444032081,0x440c14201444061,0x20582422021140,0x8150104c0432301,0x400443101400043,0x18400450088c6,0x14101080643101,0x100245028540a45,0x200900c16008942,0x450091480411301,0x848022181c02034,0x90cc070000540,0x13200446011019,0x80a25100440031,0x100c42032100940,0xa14108880261100,0x8c4041001400215,0x80c42442008c40,0x140084c0423180,0xd006220184c0611,0x109840044001084,0x211108902013181,0x402413090442016,0x90584231021104,0x241090504225001,0x460311088c0011,0x8800240188c8,0x50201102050011,0x80814201082432,0x180c88041020900,0x241100900211080,0x444022080500422]), 118)

def s39L : DagLinkList := dagExtractLinks (packedLimbs [0x4809,0x12024048090120,0x238c618850c610c,0x208410460841082,0x1005f8be17a2f41,0xe83b2724e05c037,0x16e0d85b0351628,0xad941a534827d4e,0x191b1e42d00d001]) (packedLimbs [0x5006c4c42051464,0x560205086c54440,0x5006c5646c54460,0x5686c54c604e019,0x4a011530605006c,0x5006c4e06c4c428,0x4a46c4406d48059,0x320211c01140061,0x3e0393003146029,0x220211a0114486d,0x428592e02240c61,0x2c432220323a83e,0x3ec622042918421,0x3c06e3a01e38c60,0x36c5034c4032c6e,0x30c622e46e2c462,0x1e429164212a06e,0x2806d2606c24065,0x220622042b1e423,0x1c85f1a8531842b,0x164231485f12853,0x1005f0e0530c02f,0xa02b0802706023,0x4019020110003f]) 11 4 13 6 1

def s39D : Forest := fun i => decodeNode 5 18 (packedLimbs [0x436,0x618c178304c0d92,0x3640850e236300,0xb2b014a90da942c,0xa58c28631180dc6,0xf198c05628158,0x805637118c44237,0x108c44037100da4,0x36100ca4031108,0x5632118d0be2429,0x888562211890be1,0x429840be1029840,0x5e10158404e1011,0x8403210088407e0]) i

def s39T := dagTraceTagsBin s39M 118 (dagTagBases s39N (packedLimbs [0x615531a1a367,0x42162531a9a837f,0xa9f7eef32b4fb6d,0xb7b5ec9da9fd5d1,0xfa36eed3fac07ed,0xef3eedede53edbd,0x76d6c1617bda320,0xc2f114e80daea9e,0x50eebaef5fd70be,0x84758ddfba47e56,0xbac74dc0c2e54f7,0xfa6ff1df37e16bf]) (packedLimbs [0xff47fffda37f,0x7cf8ed619fab77f,0xebffdfbb2fefa3f,0xf7ffee8fe5dfddb,0xfe7dc6d3fff2fff,0xefbffffffdfffbd,0xff6af7bffbfe73e,0xfbfcf7f81dbfb9f,0x59efbbf5e5ff5bb,0x553fdd97aa7ff76,0xf9ffdfdfff7cedf,0xffffffffffe76ff]) 118) 8 s39D

def s39St := dagTraceBin s39M s39N 8 s39D

def s39Mv := dagMoves ([] : List (DagMoveRecord 256))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39A : DagMovesOK s39M s39G 256 s39Mv := dagMovesOfCheck (by decide +kernel)

def s39NB : Nat → List Bound := dagNodeBounds s39C.toArray (packedLimbs [0xd,0x1a0340680d01a0,0x340680d01a03406,0x71ce19c330e33c0,0x76d6d0d91b035c6,0xb8561aa3542a855,0xa8350298d30a25,0x2620c3a7650aa11,0xb9b828e3202b805]) (packedLimbs [0x32430430974312,0x222202442865432,0x108654321065432,0x107654321076543,0x210654321076543,0x210654321087654,0x210765421065210]) 11 4 4

def s39Ck := dagCheckNodeBin s39M s39G s39NB 44 s39St s39Mv s39L s39S s39T

def s39RA (token : Nat) : Bool :=
  let s := rootState s39N 8 token
  !dagAllowedRootBin s39M s39E s.2.1 || dagLocalBin s39M s39G (dagKnownClosesBin s39G s39C) s ||
  dagRefBin s39M 44 s39St s39Mv (fun p tok => dagFindLink (s39L p) tok) 0 token s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39RB0 : treeBlock 0 64 s39RA = true := by decide +kernel

theorem s39RV : treeBlock 0 64 s39RA = true := s39RB0

theorem s39R : dagCheckRootsBin s39M s39G (dagKnownClosesBin s39G s39C) s39E (dagRefBin s39M 44 s39St s39Mv (fun p tok => dagFindLink (s39L p) tok) 0) s39N 8 = true := s39RV

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Bl0 : treeBlock 0 32 s39Ck = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Bl32 : treeBlock 32 12 s39Ck = true := by decide +kernel

theorem s39Bk : treeBlock 0 44 s39Ck = true := (@treeBlock_merge 0 32 12 s39Ck s39Bl0 s39Bl32)

theorem s39K : KnownBin s39C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) s38Bin) s35Bin) s33Bin) s37Bin) s36Bin) s34Bin) s32Bin) s31Bin) s10Bin) s30Bin)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Bin : BinLower s39M s39W s39G 9 := by
  apply lowerDagBin _ _ _ _ s39A _ _ _ s39K _ (fun _ b hb => dagNodeBounds_mem b hb) s39R s39Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s39C, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def s40M : Word := (packedLimbs [0xffffffff0,0xffffffff])

abbrev s40G : Word := sGoal &&& s40M

abbrev s40W : List Word := projectDAGStock s40M sBase [0, 1, 2, 3, 4, 6]

def s40F : Bound := (s40M, s40W, 9, s40G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Bin : BinLower s40M s40W s40G 9 := dagShiftLowerBin (width := 256) [ms4, ms10] s39Bin (by decide +kernel)

def s41M : Word := (packedLimbs [0x555555550,0x55555555])

abbrev s41G : Word := sGoal &&& s41M

abbrev s41W : List Word := projectDAGStock s41M sBase [1, 2, 3, 4, 6]

def s41F : Bound := (s41M, s41W, 7, s41G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Bin : BinLower s41M s41W s41G 7 := dagShiftLowerBin (width := 256) [ms7, ms15, ms20] s14Bin (by decide +kernel)

def s42M : Word := (packedLimbs [0x5,0x50505050505050,0x505050505050505])

abbrev s42G : Word := sGoal &&& s42M

abbrev s42W : List Word := projectDAGStock s42M sBase [1, 3, 4, 5, 6]

def s42F : Bound := (s42M, s42W, 7, s42G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s42Bin : BinLower s42M s42W s42G 7 := dagShiftLowerBin (width := 256) [ms2, ms11, ms12] s14Bin (by decide +kernel)

def s43M : Word := 0x5555555555555555

abbrev s43G : Word := sGoal &&& s43M

abbrev s43W : List Word := projectDAGStock s43M sBase [1, 2, 3, 4, 5]

def s43F : Bound := (s43M, s43W, 7, s43G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Bin : BinLower s43M s43W s43G 7 := dagShiftLowerBin (width := 256) [ms22, ms16, ms9, ms8] s14Bin (by decide +kernel)

def s44M : Word := (packedLimbs [0x55,0x555555555555555,0x555555555555555])

abbrev s44G : Word := sGoal &&& s44M

abbrev s44W : List Word := projectDAGStock s44M sBase [1, 2, 3, 4, 5, 6]

def s44F : Bound := (s44M, s44W, 9, s44G)

def s44E := unpackWitnesses s44W [5128, 272400, 529410, 796676, 1065986, 1344514]

abbrev s44N : List Word := normStock s44M s44W

def s44C : List Bound := [s41F, s14F, s42F, s43F, s31F, s22F]

def s44S : DagSample := ((packedLimbs [0x240a0041a020582,0x42203028180a030,0x50100e010c81844,0x9028040e301c00,0x44001082432201,0x100c1603038184c,0xa0180e000500,0x24001409068301,0xa000220c070181c,0xc068241a181c02,0x41620108000a040,0xa02050100a08050,0x100884024020900,0x84408050100a020,0x50044201088040a]), 50)

def s44L : DagLinkList := dagExtractLinks 0x9 0x3f 2 1 6 1 1

def s44D : Forest := fun i => decodeNode 1 7 0x7e i

def s44T := dagTraceTagsBin s44M 50 (dagTagBases s44N (packedLimbs [0x824c9bec8f7a372,0xac23cefe1732cfc,0x390e5fba75daf5c,0xebd76f76f68f75,0x1f7fec5bc7d6bbb]) (packedLimbs [0xa54e9ffebffe346,0xfe2fefff377abfe,0xbb1f7fbfbf7bffd,0xefdffff7ffdf7d,0x3fdffddfe7f7bff]) 50) 8 s44D

def s44St := dagTraceBin s44M s44N 8 s44D

def s44Mv := dagMoves ([] : List (DagMoveRecord 256))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44A : DagMovesOK s44M s44G 256 s44Mv := dagMovesOfCheck (by decide +kernel)

def s44NB : Nat → List Bound := dagNodeBounds s44C.toArray 0x6 0x2c688 6 3 3

def s44Ck := dagCheckNodeBin s44M s44G s44NB 1 s44St s44Mv s44L s44S s44T

def s44RA (token : Nat) : Bool :=
  let s := rootState s44N 8 token
  !dagAllowedRootBin s44M s44E s.2.1 || dagLocalBin s44M s44G (dagKnownClosesBin s44G s44C) s ||
  dagRefBin s44M 1 s44St s44Mv (fun p tok => dagFindLink (s44L p) tok) 0 token s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44RB0 : treeBlock 0 64 s44RA = true := by decide +kernel

theorem s44RV : treeBlock 0 64 s44RA = true := s44RB0

theorem s44R : dagCheckRootsBin s44M s44G (dagKnownClosesBin s44G s44C) s44E (dagRefBin s44M 1 s44St s44Mv (fun p tok => dagFindLink (s44L p) tok) 0) s44N 8 = true := s44RV

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44Bl0 : treeBlock 0 1 s44Ck = true := by decide +kernel

theorem s44Bk : treeBlock 0 1 s44Ck = true := s44Bl0

theorem s44K : KnownBin s44C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) s22Bin) s31Bin) s43Bin) s42Bin) s14Bin) s41Bin)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44Bin : BinLower s44M s44W s44G 9 := by
  apply lowerDagBin _ _ _ _ s44A _ _ _ s44K _ (fun _ b hb => dagNodeBounds_mem b hb) s44R s44Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s44C, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def s45M : Word := 0xf0f0f0f0f0f0f0f

abbrev s45G : Word := sGoal &&& s45M

abbrev s45W : List Word := projectDAGStock s45M sBase [0, 1, 3, 4, 5]

def s45F : Bound := (s45M, s45W, 7, s45G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s45Bin : BinLower s45M s45W s45G 7 := dagShiftLowerBin (width := 256) [ms18, ms22, ms4, ms3, ms8, ms23] s14Bin (by decide +kernel)

def s46M : Word := 0x555500005555

abbrev s46G : Word := sGoal &&& s46M

abbrev s46W : List Word := projectDAGStock s46M sBase [1, 2, 3, 5]

def s46F : Bound := (s46M, s46W, 5, s46G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Bin : BinLower s46M s46W s46G 5 := dagShiftLowerBin (width := 256) [ms22, ms16, ms9] s2Bin (by decide +kernel)

def s47M : Word := 0xffff0000ffff

abbrev s47G : Word := sGoal &&& s47M

abbrev s47W : List Word := projectDAGStock s47M sBase [0, 1, 2, 3, 5]

def s47F : Bound := (s47M, s47W, 6, s47G)

def s47E := unpackWitnesses s47W [4616, 267272, 542752, 791041, 1065986]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47Bin : BinLower s47M s47W s47G 6 := by
  apply essentialLiftBin (witnesses := s47E) (cut := s46M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesBinOfCheck (old := s46W) (by decide +kernel)
  · exact s46Bin
  · decide +kernel

def s48M : Word := 0xffff0000ffff0000

abbrev s48G : Word := sGoal &&& s48M

abbrev s48W : List Word := projectDAGStock s48M sBase [0, 1, 2, 3, 5]

def s48F : Bound := (s48M, s48W, 6, s48G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s48Bin : BinLower s48M s48W s48G 6 := dagShiftLowerBin (width := 256) [ms1, ms4, ms18, ms11, ms17, ms9, ms24, ms6] s22Bin (by decide +kernel)

def s49M : Word := 0xffffffff

abbrev s49G : Word := sGoal &&& s49M

abbrev s49W : List Word := projectDAGStock s49M sBase [0, 1, 2, 3, 4]

def s49F : Bound := (s49M, s49W, 5, s49G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Bin : BinLower s49M s49W s49G 5 := dagShiftLowerBin (width := 256) [ms4, ms1, ms11, ms10] s34Bin (by decide +kernel)

def s50M : Word := 0xffffffffffffffff

abbrev s50G : Word := sGoal &&& s50M

abbrev s50W : List Word := projectDAGStock s50M sBase [0, 1, 2, 3, 4, 5]

def s50F : Bound := (s50M, s50W, 9, s50G)

def s50E := unpackWitnesses s50W [4616, 267272, 534544, 791041, 1057281, 1328130]

abbrev s50N : List Word := normStock s50M s50W

def s50C : List Bound := [s20F, s45F, s43F, s34F, s47F, s48F, s49F]

def s50S : DagSample := ((packedLimbs [0x1019060,0x500a240c0283009,0x2094080a080281,0x82c04070001a060,0xa020320c0640826,0x98000b028942,0x1a0082c2016008,0x88000e020382013,0x905002230008c3,0x38000c80423000,0xa0240a008340a09,0x108a4101a018886,0x38008c44211018,0x44021306028100d,0x9044241a108240,0x9028340623040,0x380024090c81809,0x184c24160904c1,0x80e0c0684223060,0x344225180c40011,0x504231010281,0x28100a00022000,0x284024020900814,0xc070181c100880,0x422080440209080,0x501009040280211]), 85)

def s50L : DagLinkList := dagExtractLinks 0x182cd8b162c5176a8601 (packedLimbs [0x482e20,0x7ad8c07c503620,0x1417480b9302f18,0x158809c2046003f]) 7 3 12 4 1

def s50D : Forest := fun i => decodeNode 4 16 (packedLimbs [0x5c901e4c5,0x3c40305d205c20,0x2b10271023103f0]) i

def s50T := dagTraceTagsBin s50M 85 (dagTagBases s50N (packedLimbs [0x1cfecbd3,0x6384872c17ff95d,0x9a88092e79b940f,0xd9f3d9b3cb4bfbf,0xf7a759bf07bb205,0xa67b02f216e5f17,0x3a4fe4f5ccfd067,0xe8b87f1adb6c977,0x81d1ffa7e9a273f]) (packedLimbs [0x37ffeaf7,0xe287a7bd77ffddf,0xfffff7af773b47f,0xdffbf996dbeffdf,0xefbddbff97f9395,0xfffbfbf3f6e5fbf,0x3e79bcf5cddf7e7,0xecbbffbafffffff,0xffdafdffe9b6f7f]) 85) 8 s50D

def s50St := dagTraceBin s50M s50N 8 s50D

def s50Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 5, 4, 3, 6, 7] 0 i.val)

def s50Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 5, 4, 3, 6, 7] 0 i.val)

def s50Mv := dagMoves ([([ms4, ms10], s50Mp0, s50Mi0)] : List (DagMoveRecord 256))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50A : DagMovesOK s50M s50G 256 s50Mv := dagMovesOfCheck (by decide +kernel)

def s50NB : Nat → List Bound := dagNodeBounds s50C.toArray (packedLimbs [0x200f9753,0x69a2d04f99c5e05]) (packedLimbs [0x19e6358d1,0x1ac688d63445888]) 9 3 3

def s50Ck := dagCheckNodeBin s50M s50G s50NB 10 s50St s50Mv s50L s50S s50T

def s50RA (token : Nat) : Bool :=
  let s := rootState s50N 8 token
  !dagAllowedRootBin s50M s50E s.2.1 || dagLocalBin s50M s50G (dagKnownClosesBin s50G s50C) s ||
  dagRefBin s50M 10 s50St s50Mv (fun p tok => dagFindLink (s50L p) tok) 0 token s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50RB0 : treeBlock 0 64 s50RA = true := by decide +kernel

theorem s50RV : treeBlock 0 64 s50RA = true := s50RB0

theorem s50R : dagCheckRootsBin s50M s50G (dagKnownClosesBin s50G s50C) s50E (dagRefBin s50M 10 s50St s50Mv (fun p tok => dagFindLink (s50L p) tok) 0) s50N 8 = true := s50RV

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Bl0 : treeBlock 0 10 s50Ck = true := by decide +kernel

theorem s50Bk : treeBlock 0 10 s50Ck = true := s50Bl0

theorem s50K : KnownBin s50C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) s49Bin) s48Bin) s47Bin) s34Bin) s43Bin) s45Bin) s20Bin)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Bin : BinLower s50M s50W s50G 9 := by
  apply lowerDagBin _ _ _ _ s50A _ _ _ s50K _ (fun _ b hb => dagNodeBounds_mem b hb) s50R s50Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s50C, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def s51M : Word := (packedLimbs [0xf,0xf0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f])

abbrev s51G : Word := sGoal &&& s51M

abbrev s51W : List Word := projectDAGStock s51M sBase [0, 1, 3, 4, 5, 6]

def s51F : Bound := (s51M, s51W, 9, s51G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Bin : BinLower s51M s51W s51G 9 := dagShiftLowerBin (width := 256) [ms1, ms4, ms9, ms11, ms14] s44Bin (by decide +kernel)

def s52M : Word := 0xffff000000000000ffff

abbrev s52G : Word := sGoal &&& s52M

abbrev s52W : List Word := projectDAGStock s52M sBase [0, 1, 2, 3, 6]

def s52F : Bound := (s52M, s52W, 5, s52G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s52Bin : BinLower s52M s52W s52G 5 := dagShiftLowerBin (width := 256) [ms1, ms4, ms10, ms11] s32Bin (by decide +kernel)

def s53M : Word := (packedLimbs [0xf0f00000f0f0,0xf0f00000f0f])

abbrev s53G : Word := sGoal &&& s53M

abbrev s53W : List Word := projectDAGStock s53M sBase [0, 1, 3, 5, 6]

def s53F : Bound := (s53M, s53W, 6, s53G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s53Bin : BinLower s53M s53W s53G 6 := dagShiftLowerBin (width := 256) [ms1, ms4, ms9, ms11, ms14] s31Bin (by decide +kernel)

def s54M : Word := (packedLimbs [0x5555000055550,0x555500005555])

abbrev s54G : Word := sGoal &&& s54M

abbrev s54W : List Word := projectDAGStock s54M sBase [1, 2, 3, 5, 6]

def s54F : Bound := (s54M, s54W, 6, s54G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s54Bin : BinLower s54M s54W s54G 6 := dagShiftLowerBin (width := 256) [ms2, ms11, ms12] s31Bin (by decide +kernel)

def s55M : Word := 0xf0f00000f0f

abbrev s55G : Word := sGoal &&& s55M

abbrev s55W : List Word := projectDAGStock s55M sBase [0, 1, 3, 5]

def s55F : Bound := (s55M, s55W, 5, s55G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Bin : BinLower s55M s55W s55G 5 := dagShiftLowerBin (width := 256) [ms18, ms22, ms4, ms3, ms9] s2Bin (by decide +kernel)

def s56M : Word := (packedLimbs [0x505000005050,0x50500000505])

abbrev s56G : Word := sGoal &&& s56M

abbrev s56W : List Word := projectDAGStock s56M sBase [1, 3, 5, 6]

def s56F : Bound := (s56M, s56W, 5, s56G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Bin : BinLower s56M s56W s56G 5 := dagShiftLowerBin (width := 256) [ms2, ms11, ms12] s2Bin (by decide +kernel)

def s57M : Word := 0x55550000000000005555

abbrev s57G : Word := sGoal &&& s57M

abbrev s57W : List Word := projectDAGStock s57M sBase [1, 2, 3, 6]

def s57F : Bound := (s57M, s57W, 4, s57G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s57Bin : BinLower s57M s57W s57G 4 := dagShiftLowerBin (width := 256) [ms15, ms10] s3Bin (by decide +kernel)

def s58M : Word := (packedLimbs [0xffff0000ffff0,0xffff0000ffff])

abbrev s58G : Word := sGoal &&& s58M

abbrev s58W : List Word := projectDAGStock s58M sBase [0, 1, 2, 3, 5, 6]

def s58F : Bound := (s58M, s58W, 9, s58G)

def s58E := unpackWitnesses s58W [4616, 267272, 542752, 791041, 1065986, 1344001]

abbrev s58N : List Word := normStock s58M s58W

def s58C : List Bound := [s19F, s32F, s47F, s52F, s53F, s54F, s55F, s46F, s56F, s38F, s57F, s17F]

def s58S : DagSample := ((packedLimbs [0x20a00,0x229001a0002c100,0xb0020b03090080a,0x8c0061029108,0x4c031101044021,0x14084600924060a,0x41281049000940,0x4c01118000e060,0xa0024530190000d,0x24024000b240280,0x43010980c0a000,0x980222108a0080e,0x6090080d010380,0x45021300046008,0x904042200884044,0x30988061241104,0x68030881068200,0x90904a100249049,0x108904023030380,0x82610184182c101,0x480280088c4229,0x2094104c10094c,0x41300a0102c008,0x944029009840028,0x289090280108c1,0x844008344209028,0x240a25301a00622,0x6024100d040381,0x80d028344222109,0x4002206038180a,0x241a04223301840,0x41108940042000,0x280009241300623,0x201080044000904,0x261040a00844061,0x308041201100442,0x10280824100a00,0x422100884024009,0x40209040281009]), 128)

def s58L : DagLinkList := dagExtractLinks (packedLimbs [0x9c09c0,0x9c09a1981961903,0x900900900900900,0x9009009009008e1,0x8a2862860860860,0x860860860860860,0x8608608607e47c1,0x7c07c07c0763703,0x6a36816235854a7,0x36a303227030001]) (packedLimbs [0x362182d4305,0x8861b21416c202c,0x830560d9a40c548,0x8ea03150022ab1,0x814e2828c404e84,0x9e0d328362605c,0x4a09892164c2112,0x3058c38c25e0caa,0xa19228394388281,0xf8aa191f46e3c8,0x5c4c0a480109d01,0x9b78c073140de20,0x1a031320613c084,0x7808d8c4eaf8846,0x21b8bc315646eaa,0x8c459138aa21140,0x19140224e0e8903,0x61103e210743e0d,0x872190d04d18098,0x2c0f850194785f8,0xd0a7260fe441989,0x45f108a61d0fc32,0x19c542f0a856110,0x9c1a11c202b8204,0x60806c08098003f]) 12 5 12 6 1

def s58D : Forest := fun i => decodeNode 6 18 (packedLimbs [0x840a20c2806c,0x7b1810c50431010,0x8343c170b04c2e1,0x64a0582a0e48c41,0x1d0f8746e190b86,0x191b1405c40140,0xc45030161b84862,0x111384442100644,0x83a0c1b0303e0e0,0xe82836090c8204d,0x8130203e080c82,0x45f0514c143f050,0xcc142b0509c1423,0x406c1013040fc0]) i

def s58T := dagTraceTagsBin s58M 128 (dagTagBases s58N (packedLimbs [0xbb3d67a2febf,0xbf2d44c74325e1a,0xeeff2fa7e9cf80b,0x6976e3dfff7eda2,0xe67f99de5c0f08f,0x58065dd2f19d9b8,0x77dd996ef02ef0a,0x61b25fea36ab2ac,0x5071f1f5d78053f,0xf75f45f521c8850,0x78fac5ec7e0fdf,0x80499eff8a8abd7,0xaf7bdfdd2d283f7]) (packedLimbs [0xbbdf3fbfe7f7,0xffdfcfd5c2f1ede,0xefff3fdf7bdff3f,0x7f77f7ffff7efff,0xfeff9bf7cd4ff7f,0xb8df77f2f7fdb36,0x73fff9efffffbcf,0x75fdffdabefbbeb,0xf0f1fdf5ffcf7ff,0xffdff7faef4d6c6,0xfedf9e5feff4fff,0xefffd5fffd9cbfb,0xe7efdffd7d7e7ff]) 128) 8 s58D

def s58St := dagTraceBin s58M s58N 8 s58D

def s58Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 5, 4, 3, 6, 7] 0 i.val)

def s58Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 5, 4, 3, 6, 7] 0 i.val)

def s58Mv := dagMoves ([([ms4, ms10], s58Mp0, s58Mi0)] : List (DagMoveRecord 256))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58A : DagMovesOK s58M s58G 256 s58Mv := dagMovesOfCheck (by decide +kernel)

def s58NB : Nat → List Bound := dagNodeBounds s58C.toArray (packedLimbs [0x338670c,0xe19c338670ce19c,0x338670cc398328e,0x50ca194320df5b8,0x7702d8db0b43682,0xd05a0b41646c0d7,0x1ac34ce90d11a03,0x34e2c3c9690b212,0xb9d82ec3e03c007]) (packedLimbs [0x15ba93131001,0x22254140254087,0x543210a87543210,0x865432108654321,0x9543210a954321,0x54321076543210,0x765432108765420]) 11 4 4

def s58Ck := dagCheckNodeBin s58M s58G s58NB 46 s58St s58Mv s58L s58S s58T

def s58RA (token : Nat) : Bool :=
  let s := rootState s58N 8 token
  !dagAllowedRootBin s58M s58E s.2.1 || dagLocalBin s58M s58G (dagKnownClosesBin s58G s58C) s ||
  dagRefBin s58M 46 s58St s58Mv (fun p tok => dagFindLink (s58L p) tok) 0 token s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58RB0 : treeBlock 0 64 s58RA = true := by decide +kernel

theorem s58RV : treeBlock 0 64 s58RA = true := s58RB0

theorem s58R : dagCheckRootsBin s58M s58G (dagKnownClosesBin s58G s58C) s58E (dagRefBin s58M 46 s58St s58Mv (fun p tok => dagFindLink (s58L p) tok) 0) s58N 8 = true := s58RV

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58Bl0 : treeBlock 0 32 s58Ck = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58Bl32 : treeBlock 32 14 s58Ck = true := by decide +kernel

theorem s58Bk : treeBlock 0 46 s58Ck = true := (@treeBlock_merge 0 32 14 s58Ck s58Bl0 s58Bl32)

theorem s58K : KnownBin s58C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) s17Bin) s57Bin) s38Bin) s56Bin) s46Bin) s55Bin) s54Bin) s53Bin) s52Bin) s47Bin) s32Bin) s19Bin)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58Bin : BinLower s58M s58W s58G 9 := by
  apply lowerDagBin _ _ _ _ s58A _ _ _ s58K _ (fun _ b hb => dagNodeBounds_mem b hb) s58R s58Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s58C, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def s59M : Word := (packedLimbs [0xff,0xff00ff00ff00f,0xf00ff00ff00ff00])

abbrev s59G : Word := sGoal &&& s59M

abbrev s59W : List Word := projectDAGStock s59M sBase [0, 1, 2, 4, 5, 6]

def s59F : Bound := (s59M, s59W, 7, s59G)

def s59E := unpackWitnesses s59W [4616, 267272, 538648, 800780, 1069064, 1349644]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s59Bin : BinLower s59M s59W s59G 7 := by
  apply essentialLiftBin (witnesses := s59E) (cut := s22M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesBinOfCheck (old := s22W) (by decide +kernel)
  · exact s22Bin
  · decide +kernel

def s60M : Word := (packedLimbs [0xff,0xffffff00000000f,0xfffffff00000000])

abbrev s60G : Word := sGoal &&& s60M

abbrev s60W : List Word := projectDAGStock s60M sBase [0, 1, 2, 3, 4, 6]

def s60F : Bound := (s60M, s60W, 7, s60G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s60Bin : BinLower s60M s60W s60G 7 := dagShiftLowerBin (width := 256) [ms4, ms1, ms10] s59Bin (by decide +kernel)

def s61M : Word := (packedLimbs [0xff,0xff0000ffff0000f,0xfff0000ffff0000])

abbrev s61G : Word := sGoal &&& s61M

abbrev s61W : List Word := projectDAGStock s61M sBase [0, 1, 2, 3, 5, 6]

def s61F : Bound := (s61M, s61W, 7, s61G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s61Bin : BinLower s61M s61W s61G 7 := dagShiftLowerBin (width := 256) [ms2, ms11, ms12] s59Bin (by decide +kernel)

def s62M : Word := (packedLimbs [0xf,0xf0f0f000000000,0xf0f0f0f00000000])

abbrev s62G : Word := sGoal &&& s62M

abbrev s62W : List Word := projectDAGStock s62M sBase [0, 1, 3, 4, 6]

def s62F : Bound := (s62M, s62W, 6, s62G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s62Bin : BinLower s62M s62W s62G 6 := dagShiftLowerBin (width := 256) [ms4, ms10] s22Bin (by decide +kernel)

def s63M : Word := (packedLimbs [0x55,0x550000555500005,0x555000055550000])

abbrev s63G : Word := sGoal &&& s63M

abbrev s63W : List Word := projectDAGStock s63M sBase [1, 2, 3, 5, 6]

def s63F : Bound := (s63M, s63W, 6, s63G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63Bin : BinLower s63M s63W s63G 6 := dagShiftLowerBin (width := 256) [ms2, ms11, ms12] s22Bin (by decide +kernel)

def s64M : Word := (packedLimbs [0x5,0x50000050500000,0x505000005050000])

abbrev s64G : Word := sGoal &&& s64M

abbrev s64W : List Word := projectDAGStock s64M sBase [1, 3, 5, 6]

def s64F : Bound := (s64M, s64W, 5, s64G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s64Bin : BinLower s64M s64W s64G 5 := dagShiftLowerBin (width := 256) [ms2, ms11, ms12] s7Bin (by decide +kernel)

def s65M : Word := 0xf0f00000f0f0000

abbrev s65G : Word := sGoal &&& s65M

abbrev s65W : List Word := projectDAGStock s65M sBase [0, 1, 3, 5]

def s65F : Bound := (s65M, s65W, 5, s65G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s65Bin : BinLower s65M s65W s65G 5 := dagShiftLowerBin (width := 256) [ms18, ms2, ms1, ms11, ms8, ms9, ms21, ms6] s7Bin (by decide +kernel)

def s66M : Word := (packedLimbs [0xff00ff000,0xff00ff00])

abbrev s66G : Word := sGoal &&& s66M

abbrev s66W : List Word := projectDAGStock s66M sBase [0, 1, 2, 4, 6]

def s66F : Bound := (s66M, s66W, 6, s66G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s66Bin : BinLower s66M s66W s66G 6 := dagShiftLowerBin (width := 256) [ms1, ms18, ms17, ms24, ms6] s22Bin (by decide +kernel)

def s67M : Word := 0x5555000055550000

abbrev s67G : Word := sGoal &&& s67M

abbrev s67W : List Word := projectDAGStock s67M sBase [1, 2, 3, 5]

def s67F : Bound := (s67M, s67W, 5, s67G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Bin : BinLower s67M s67W s67G 5 := dagShiftLowerBin (width := 256) [ms2, ms7, ms11, ms8, ms9, ms21, ms6] s7Bin (by decide +kernel)

def s68M : Word := (packedLimbs [0xf0f0f0f0,0xf0f0f0f])

abbrev s68G : Word := sGoal &&& s68M

abbrev s68W : List Word := projectDAGStock s68M sBase [0, 1, 3, 4, 6]

def s68F : Bound := (s68M, s68W, 6, s68G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Bin : BinLower s68M s68W s68G 6 := dagShiftLowerBin (width := 256) [ms4, ms10] s31Bin (by decide +kernel)

def s69M : Word := (packedLimbs [0xf,0xf00000f0f00000,0xf0f00000f0f0000])

abbrev s69G : Word := sGoal &&& s69M

abbrev s69W : List Word := projectDAGStock s69M sBase [0, 1, 3, 5, 6]

def s69F : Bound := (s69M, s69W, 6, s69G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s69Bin : BinLower s69M s69W s69G 6 := dagShiftLowerBin (width := 256) [ms1, ms4, ms11, ms12] s22Bin (by decide +kernel)

def s70M : Word := (packedLimbs [0xf000f0,0xf000f])

abbrev s70G : Word := sGoal &&& s70M

abbrev s70W : List Word := projectDAGStock s70M sBase [0, 1, 4, 6]

def s70F : Bound := (s70M, s70W, 5, s70G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s70Bin : BinLower s70M s70W s70G 5 := dagShiftLowerBin (width := 256) [ms0, ms7, ms4, ms8, ms20] s2Bin (by decide +kernel)

def s71M : Word := (packedLimbs [0xf000f000000000,0xf000f00000000])

abbrev s71G : Word := sGoal &&& s71M

abbrev s71W : List Word := projectDAGStock s71M sBase [0, 1, 4, 6]

def s71F : Bound := (s71M, s71W, 5, s71G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Bin : BinLower s71M s71W s71G 5 := dagShiftLowerBin (width := 256) [ms4, ms7, ms8] s7Bin (by decide +kernel)

def s72M : Word := 0x50500000505

abbrev s72G : Word := sGoal &&& s72M

abbrev s72W : List Word := projectDAGStock s72M sBase [1, 3, 5]

def s72F : Bound := (s72M, s72W, 4, s72G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Bin : BinLower s72M s72W s72G 4 := dagShiftLowerBin (width := 256) [ms2, ms11, ms12] s0Bin (by decide +kernel)

def s73M : Word := 0xf0f0f0f

abbrev s73G : Word := sGoal &&& s73M

abbrev s73W : List Word := projectDAGStock s73M sBase [0, 1, 3, 4]

def s73F : Bound := (s73M, s73W, 4, s73G)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73Bin : BinLower s73M s73W s73G 4 := dagShiftLowerBin (width := 256) [ms1, ms0, ms4, ms9, ms16] s3Bin (by decide +kernel)

def s74M : Word := (packedLimbs [0xff,0xfffffffffffffff,0xfffffffffffffff])

abbrev s74G : Word := sGoal &&& s74M

abbrev s74W : List Word := projectDAGStock s74M sBase [0, 1, 2, 3, 4, 5, 6]

def s74E := unpackWitnesses s74W [4616, 267272, 534544, 791041, 1057281, 1328130, 1606145]

abbrev s74N : List Word := normStock s74M s74W

def s74C : List Bound := [s29F, s40F, s44F, s50F, s51F, s39F, s58F, s60F, s61F, s62F, s59F, s37F, s48F, s45F, s63F, s42F, s64F, s22F, s41F, s65F, s66F, s47F, s67F, s68F, s36F, s21F, s53F, s69F, s70F, s71F, s35F, s31F, s49F, s56F, s55F, s72F, s54F, s25F, s30F, s43F, s46F, s73F]

def s74S : DagSample := ((packedLimbs [0x20944,0x6804068c024021,0x184025010680815,0xc14024140190c2,0x1302034060b008,0x940c0a02098080e,0x8058101c091489,0x49200500223180,0xc80261020580c22,0x29046011008c42,0x442300a00a110c0,0x640423030504222,0x240a00a24108240,0xc26000a0100d301,0x90240a018880213,0x3118180a040380,0x50008341844018,0x440a45108900024,0x1040c16000880,0xa15301844211241,0x602411028244229,0x180d0305800110c,0x70241300011180,0xe01809000244241,0x184c00420c0e00,0x14028942416030,0x38182c0904c000a,0x181c0c0681088c8,0x410613024320c0,0x70181c201084225,0x90688050028343,0x1a180c48044108,0xc49068109842050,0x40a00623100a01,0x80e060340422011,0x80824021104022,0x100902011010280,0x241020502014008,0x44100900824100a]), 128)

def s74L : DagLinkList := dagExtractLinks (packedLimbs [0x7f03f81fc0fe,0x7f03f81fc0fe07,0xf03f81fc0fe07f0,0x3f81fa1fc0fd87e,0xc1f60fa0fc87e03,0xf00f70fb07d43e6,0x2f307983cc1e60f,0x307983cc1e60f30,0x7983cc1e60f1178,0x7bc3de0ef0768b,0xac5d41ea07487a4,0x1ce2e60f287941c,0x81de36b9f583aa1,0xd40ea03501a80d4,0x6a03501a80d406,0xa03501a80d406a0,0x3501a23d10670f3,0x43905c61620b009,0x7a3af7568aac554,0x1aa0538e9c14c1a,0x50d206901461a30,0x508a8414209f14f,0x827453819c04d86,0x6c13609a0c6b5f2,0x2e0c5f8a7c101e6,0xab248885005e001]) (packedLimbs [0x1d08a0ea04c752,0x19ba1183cc118e4,0x6c74421ba4181c,0xc882e7060722363,0x891c5b4886d8433,0x6b221b5210f6488,0x4e2c6169030b8e2,0x190066e0069570,0x8b780658c046dc,0x7eed640b6b185a,0xd8a3d008168030b,0x30145b7104d8c8e,0x6b6413381858808,0x2d40395a018b080,0xcd80046be033694,0x38b4210d58844ce,0x8535e2202a9089a,0x7100d188267830a,0xe910998104b4042,0x66421b280f18908,0x6bc450e4a40b0b1,0x4b7d0a5b808c64a,0x30b1a1797d0a5c3,0x462e28413141898,0x5905c088edf4413,0x21b97d0c5ba482,0x5d2316d823b6810,0x4b606e5a0312f31,0x4175086b8c515b2,0x19ad210d588c0a6,0x6c5202e2c90e15,0x48c0b00345743f2,0xb51c9558a2a9069,0x52830a9d1c94a0e,0x4a207e500362781,0x73218a384c41ce4,0x38a721453108290,0x471422209f10cea,0xc0e25605126020c,0xe80cc740269d472,0xc4839a6a1f9310e,0x49684eb14212391,0xccf48866c4314a2,0x14979084a40a336,0x4325018a480a47,0xc0423401348a38e,0x2c1c51d8a678842,0x3441921114ae888,0x462432280299200,0xcc6004222011468,0x39a2c145118e76e,0xc43334192191f90,0x88e48244e3a2212,0x10f8bc86554073,0x9c0219180cc5c04,0x27e0190f0089f51,0xcef20a57ac733d6,0x299e21caec8fd74,0x4723b22f1d1148e,0x487c5a432a70399,0x3814c8806670019,0xd0089bc1ccd98a,0x46ac423443919a1,0x48c88fc62472302,0x2f179148b889c5a,0x442990218b0084b,0x32140112ba391,0x541cca58a250873,0x274219090c85484,0x44c072910210f80,0xc83c04547073a48,0x29d2b1c8958a448,0x8732342991210e8,0x48e442452a003f4,0xf81c8800bc3e052,0x9e0274501087805,0xc140221da398e41,0xcc6d8e634c53196,0x218c21c85d0a42c,0x832152290a11084,0xc0fe2407e110390,0x801783c0a41c04e,0xd0210600fc2c07,0xc1403209831c331,0x8e1d88710863084,0x21c220cc1c8c60c,0x4430521982108e0,0xc0c606043810198,0x1008c040260007f]) 13 5 13 7 1

def s74D : Forest := fun i => decodeNode 7 20 (packedLimbs [0x219e6,0x8305e8305c2365c,0xc4048034c400cc3,0x3f40c413e6473e,0x6413e01cbec4029,0xc4128830a8421a7,0x1e27a30a442f24,0x831236412343723,0x4312362822421a2,0x628a1219a1421a0,0x21c1c01a1a43f18,0xa39166289683493,0xa39118391103f10,0x360e02e0ba3909,0x43f094390942709,0x2148901489a3888,0x629888398782887,0x6398723f0723907,0x2270721f0700c87,0xa39866298643906,0x22f062290621f06,0xc868398562905,0x621054390542905,0x23f052390522f05,0x229052270522105,0xc85a390483984,0x628844398442184,0x39046290343983,0x429834218322903,0x2f030290301703,0xa39828398263982,0x629826218243902,0x429024190222902,0x2210203f8203f02,0x390202f0202902,0x27020210201f82,0x1f020190283181,0x421812318122181,0x219812118102181,0x11810098103f80]) i

def s74T := dagTraceTagsBin s74M 128 (dagTagBases s74N (packedLimbs [0x7ac1fab18f6ef4,0xd88fa1ddcfb55b7,0xeb1d5ca164eebb8,0x1fe7fffce4db5bf,0xa9b7e62b50ddff6,0xa7522bf57f83f4b,0x6fe65cf9df2abff,0x5d4b97ff4b4772b,0x4d3b47f78dc2fc5,0x5997feedea329d2,0xd78c96ffec72bfd,0x7e2d6895ff35e6d,0xf5b1bbd11a9ffb7,0x5ff3b6fff76add7,0x87aff276e8fd7bf]) (packedLimbs [0xffd9feb5ba7cf4,0x7acff9dfdfb75bf,0xfb5fd9af7eee7b9,0x7defbffde5fbdff,0xb9f7f76f63fc7b6,0xbf3aebdfefd3f6f,0x7fe67dfdf7febff,0xddef9bff7b6f7bf,0x4fbb67ffaff2fd7,0x7adffbffffb3df6,0xd79d9effeefabff,0xff7b7b77ff7ce6d,0xbff1fbd5df9ffef,0xfff9ff7df7fffd7,0xe7fffaf6ebfffff]) 128) 11 s74D

def s74St := dagTraceBin s74M s74N 11 s74D

def s74Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 5, 4, 3, 6, 7] 0 i.val)

def s74Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 5, 4, 3, 6, 7] 0 i.val)

def s74Mv := dagMoves ([([ms4, ms10], s74Mp0, s74Mi0)] : List (DagMoveRecord 256))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s74A : DagMovesOK s74M s74G 256 s74Mv := dagMovesOfCheck (by decide +kernel)

def s74NB : Nat → List Bound := dagNodeBounds s74C.toArray (packedLimbs [0x9c609c6,0x9c419c219acb99,0x6b982a96cb96259,0x5c395639503936d,0x92c592a19243916,0x790c5906390418f,0xe38f648f038dab8,0xd818c698be48b83,0x8a4a892987ea862,0xe84cb836b81ec80,0x8b7f4a7e0a7ce97,0xb4d79cc786b76cd,0x752d73ac71ee700,0xf6e106c6d6a8f68,0xed676c65ec646c6,0x2cd60ef5f4d5deb,0x5c6c5b0b598c580,0xc562f548d52ed51,0x6c500b4e8c4ced4,0xb6c49ec484d46eb,0x454d438e4171400,0xb3df13c4d3a5039,0xa376d35cd346b3,0x2ec318b302b2eac,0x2c912aaf28b026c,0xf250e238c220c20,0xab1eee1d0f1b8c1,0x9ce184c16ad152c,0x138d122b10ac0f2,0xc0d8d0c690aec09,0x6c082a06cb04d00,0x3a9024b00eb0007]) (packedLimbs [0x1,0x1d6491389185102,0x405d0288185103,0x8100a207185103,0x8101740a206144,0xc2040718248098,0x3876081d8307450,0x3ce34c245103081,0x1c60d2420d81c6,0x205103081015287,0x1412ca203207095,0x24811520738d248,0x185103081004408,0x1c61440c1015407,0x1182074cc288185,0xc2040593185103,0x8100e2c81c5103,0x8101344f38d309,0x1c5103081016309,0x20718510304080a,0x248185103081013,0x289207185103081,0x202892061440c2,0x402881c61440c2,0x409512461440c2,0x402c9185103081,0x1644f38c206144,0xc204058e2881c6,0x1440c204030a207,0x185103081022511,0x2881c61440c2040,0x8a158b287185103,0x8101630a207185,0x10308101951240f,0x24718510308101d,0x59244e2481c6144,0xc204079c5d440e,0x2ca1c61440c2040,0x65444b287185103,0x810195d44d1408,0x1c61440c2040657,0x40a207185103081,0x102ca207185103,0x810112ca207185,0x10308100e30a207,0x18510308101c5d3,0x2881c61440c2040,0x79c6113ce247185,0x10308101c698248,0x1c61440c204078e,0x24718510308101e,0x609207185103081,0x1c4481c61440c2,0x4040e3081c6144,0xc204079c6081c6,0x1440c2040796510,0x38b287185103081,0x1438c2481c6144,0xc204040e30b207,0x18510308101648b,0x247185103081013,0x40b1c61440c2040,0x59038a1c61440c2,0x4030b289207185,0x10308101340a247,0x18510308100e30b,0x287185103081013,0x4502ca1c61440c2,0x4038c247185103,0x810164d030a1c6,0x1440c20404d140f,0x38d3061440c2040,0x79d59038d30b289,0x18510308101634c,0x2061440c2040756,0x49140e34c247185,0x10308101c60d309,0x1c61440c20408d6,0x4d03cd2881c6144,0xc2040389206144,0xc204049140e207,0x185103081017554,0x4081c61440c2040,0x615207185103081,0x1038d248185103,0x810102881c6144,0xc204038a207185,0x1030810232ca247,0x185103081019594,0x4d13ce3091c6144,0xc204079d50e30b,0x287185103081021,0x81951344c207185,0x10308101d69650c,0x2481c61440c2040,0x5944cc2c81c6144,0xc204038c2c91c6,0x1440c20404d030b,0x1c61440c204058b,0x24718510308101d,0x51340d247185103,0x8101d65444b289,0x1c61440c204058c,0x2c91c61440c2040,0xa606562881c6144,0xc20402ca2481c6,0x1440c2040753289,0x207185103081013,0x2ca207185103081,0x1d44b2881c6144,0xc2040449207185,0x10308101630b247,0x18510308101038a,0x20718510308100e,0x2ca2481c61440c2,0x4040f185103081,0x1a58e308185103,0x8101948b247185,0x1030810172c7185,0x1030810184491c6,0x1440c20407564d0,0x38c2c91c61440c2,0x404cd185103081,0x1540e2061440c2,0x4074b247185103,0x810061440c2040]) 16 5 6

def s74Ck := dagCheckNodeBin s74M s74G s74NB 118 s74St s74Mv s74L s74S s74T

def s74RA (token : Nat) : Bool :=
  let s := rootState s74N 11 token
  !dagAllowedRootBin s74M s74E s.2.1 || dagLocalBin s74M s74G (dagKnownClosesBin s74G s74C) s ||
  dagRefBin s74M 118 s74St s74Mv (fun p tok => dagFindLink (s74L p) tok) 0 token s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s74RB0 : treeBlock 0 128 s74RA = true := by decide +kernel

theorem s74RV : treeBlock 0 128 s74RA = true := s74RB0

theorem s74R : dagCheckRootsBin s74M s74G (dagKnownClosesBin s74G s74C) s74E (dagRefBin s74M 118 s74St s74Mv (fun p tok => dagFindLink (s74L p) tok) 0) s74N 11 = true := s74RV

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s74Bl0 : treeBlock 0 32 s74Ck = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s74Bl32 : treeBlock 32 32 s74Ck = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s74Bl64 : treeBlock 64 32 s74Ck = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s74Bl96 : treeBlock 96 22 s74Ck = true := by decide +kernel

theorem s74Bk : treeBlock 0 118 s74Ck = true := (@treeBlock_merge 0 64 54 s74Ck (@treeBlock_merge 0 32 32 s74Ck s74Bl0 s74Bl32) (@treeBlock_merge 64 32 22 s74Ck s74Bl64 s74Bl96))

theorem s74K : KnownBin s74C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) s73Bin) s46Bin) s43Bin) s30Bin) s25Bin) s54Bin) s72Bin) s55Bin) s56Bin) s49Bin) s31Bin) s35Bin) s71Bin) s70Bin) s69Bin) s53Bin) s21Bin) s36Bin) s68Bin) s67Bin) s47Bin) s66Bin) s65Bin) s41Bin) s22Bin) s64Bin) s42Bin) s63Bin) s45Bin) s48Bin) s37Bin) s59Bin) s62Bin) s61Bin) s60Bin) s58Bin) s39Bin) s51Bin) s50Bin) s44Bin) s40Bin) s29Bin)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s74Bin : BinLower s74M s74W s74G 12 := by
  apply lowerDagBin _ _ _ _ s74A _ _ _ s74K _ (fun _ b hb => dagNodeBounds_mem b hb) s74R s74Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s74C, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem hcsBinaryFloor {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n)) (min : Nat)
    (f : (Fin n → Bool) → Bool)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (binClaim : BinLower (fullMask (2 ^ n)) (raw.map BitVec.toNat) goal.toNat min)
    (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Nat)
    (hfan : ∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2)
    (hev : ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x) :
    min ≤ countNonNot gates := by
  have hfanSet : ∀ g ∈ gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    rcases hfan g hg with ⟨hop, hlen⟩
    refine ⟨?_, hlen⟩
    rcases hop with h1 | h1 | h1 <;> simp [h1]
  let eb := gates.foldl hcsStep raw
  have same : eb.getD o 0 = goal := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let y : Fin n → Bool := fun k => j.testBit k.val
    have hbank : raw.map (fun v => v.getLsbD j) = List.ofFn y :=
      beq_iff_eq.mp (hcsCheckPow_spec hRaw (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
    have hfg : goal.getLsbD j = f y :=
      beq_iff_eq.mp (hcsCheckPow_spec hGoal (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
    have hbits := hcsFoldBits raw ⟨j, hj⟩ gates hfanSet
    have hevj : (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, o⟩ (List.ofFn y)).getD o false = f y := hev y
    change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
      (List.ofFn y)).getD o false = f y at hevj
    rw [← hbank, ← hbits] at hevj
    rw [hfg, ← hevj, ← hcsGetDBit]
  obtain ⟨vs, len, built, reach⟩ := hcsBuildsBin raw (raw.map BitVec.toNat) gates
    (fun v hv => Or.inr (Or.inr (Or.inl (List.mem_map_of_mem hv)))) hfanSet
  have av : AvBin (fullMask (2 ^ n)) (vs ++ raw.map BitVec.toNat) goal.toNat := by
    rw [← same, List.getD_eq_getElem?_getD]
    cases hget : eb[o]? with
    | none => exact Or.inl rfl
    | some v => exact reach v (List.mem_of_getElem? hget)
  have lb := binClaim vs built av
  exact le_trans lb len
end PEqualNP.Outside.L_meta_30254.Seven

namespace PEqualNP.Outside.L_meta_30254
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def f (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7)



def onWit : List Gate := [⟨.or, [6, 7]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [3, 8]⟩, ⟨.and, [10, 8]⟩, ⟨.and, [0, 14]⟩, ⟨.and, [9, 13]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [19, 17]⟩, ⟨.or, [20, 18]⟩]

theorem onWitBasis : ∀ g ∈ onWit,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [onWit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem onWitCorrect : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨onWit, 21⟩ (List.ofFn x) = f x := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem onGraphCorrect : ∀ x : Fin 8 → Bool, f x = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel


theorem compareWith (lower : ∀ (gs : List Gate) (o : ℕ), FanInTwo ⟨gs,o⟩ →
    (∃ gate ∈ gs, gate.op = GateOp.not) → (∀ x : Fin 8 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = f x) → 14 ≤ gs.length) :
  ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ hc
  by_cases has : ∃ gate ∈ gs, gate.op = GateOp.not
  · have basis : FanInTwo ⟨gs,o⟩ := by
      intro gate hg
      have h := legal gate hg
      exact ⟨by rcases h.1 with h | h | h <;> simp [h], h.2⟩
    have bound := lower gs o basis has (fun x => (hc x).trans (onGraphCorrect x).symm)
    exact ⟨onWit,21,onWitBasis,bound,fun x => (onWitCorrect x).trans (onGraphCorrect x)⟩
  · refine ⟨gs,o,?_,le_rfl,hc⟩
    intro gate hg; obtain ⟨hp,hsize⟩ := legal gate hg
    exact ⟨hp.elim Or.inl (fun h => h.elim Or.inr (fun hn => (has ⟨gate,hg,hn⟩).elim)),hsize⟩
end PEqualNP.Outside.L_meta_30254

namespace PEqualNP.Outside.L_meta_30254.LeafRestriction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length
def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_legal (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1.toList, legal g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; exact ⟨Or.inl rfl, by simp⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; exact ⟨Or.inr (Or.inl rfl), by simp⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg; exact ⟨Or.inr (Or.inr rfl), by simp⟩
  · simp at hg
  · simp at hg

theorem isBinary_and (l : List ℕ) : isBinary ⟨GateOp.and, l⟩ = true := rfl
theorem isBinary_or (l : List ℕ) : isBinary ⟨GateOp.or, l⟩ = true := rfl
theorem isBinary_not (l : List ℕ) : isBinary ⟨GateOp.not, l⟩ = false := rfl

theorem simplify_binCost_le (op : GateOp) (m : ℕ) (ins : List Stat) :
    binaryCost (simplify op m ins).1.toList ≤ if isBinary ⟨op, []⟩ then 1 else 0 := by
  have hlen : ∀ o : Option Gate, binaryCost o.toList ≤ 1 := by
    intro o
    cases o with
    | none => simp [binaryCost]
    | some g => exact (List.length_filter_le _ _).trans (by simp)
  cases op
  · exact hlen _
  · exact hlen _
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simplify, simpNot, binaryCost, isBinary_not]
  · simp [simplify, binaryCost]
  · simp [simplify, binaryCost]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · rcases a with c | j <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with d | k <;> (try cases c) <;> (try cases d) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · rcases a with c | j <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with d | k <;> (try cases c) <;> (try cases d) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · rcases a with c | j <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem binaryCost_append (l1 l2 : List Gate) :
    binaryCost (l1 ++ l2) = binaryCost l1 + binaryCost l2 := by
  simp [binaryCost, List.filter_append]

theorem binaryCost_cons (g : Gate) (gs : List Gate) :
    binaryCost (g :: gs) = (if isBinary g then 1 else 0) + binaryCost gs := by
  simp only [binaryCost, List.filter_cons]
  cases isBinary g <;> simp [Nat.add_comm]

theorem elim_legal (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, legal g) → (∀ g ∈ (elim n gs acc).2, legal g) := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih
    intro g' hg'
    simp only [elimStep, List.mem_append] at hg'
    rcases hg' with hg' | hg'
    · exact h g' hg'
    · exact simplify_legal _ _ _ g' hg'

theorem elim_binCost_le (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    binaryCost (elim n gs acc).2 ≤ binaryCost acc.2 + binaryCost gs := by
  induction gs with
  | nil => intro acc; simp [elim, binaryCost]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : binaryCost (elimStep n acc g).2 ≤ binaryCost acc.2 + (if isBinary g then 1 else 0) := by
      simp only [elimStep, binaryCost_append]
      have hb := simplify_binCost_le g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
      have heq : isBinary ⟨g.op, []⟩ = isBinary g := rfl
      rw [heq] at hb
      omega
    rw [elim_cons, binaryCost_cons]
    omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, legal g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def AgreeNonConst (st : List Stat) (w1 w2 : List Bool) : Prop :=
  st.length = w1.length ∧ st.length = w2.length ∧
  ∀ i : ℕ, (∃ j : ℕ, st.getD i (Sum.inl false) = Sum.inr j) → w1.getD i false = w2.getD i false

theorem elim_agree_of_eq_binCost (n : ℕ) (gs : List Gate) :
    ∀ (w1 w2 : List Bool) (acc : List Stat × List Gate),
      (∀ g ∈ gs, legal g) →
      AgreeNonConst acc.1 w1 w2 →
      binaryCost (elim n gs acc).2 = binaryCost acc.2 + binaryCost gs →
      AgreeNonConst (elim n gs acc).1 (wiresFrom gs w1) (wiresFrom gs w2) := by
  induction gs with
  | nil => intro w1 w2 acc _ hag _; exact hag
  | cons g gs ih =>
    intro w1 w2 acc hok hag heq
    have hstep_le : binaryCost (elimStep n acc g).2 ≤ binaryCost acc.2 + (if isBinary g then 1 else 0) := by
      simp only [elimStep, binaryCost_append]
      have hb := simplify_binCost_le g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
      have heq' : isBinary ⟨g.op, []⟩ = isBinary g := rfl
      rw [heq'] at hb; omega
    have htail_le := elim_binCost_le n gs (elimStep n acc g)
    rw [elim_cons, binaryCost_cons] at heq
    have hstep_eq : binaryCost (elimStep n acc g).2 = binaryCost acc.2 + (if isBinary g then 1 else 0) := by omega
    have htail_eq : binaryCost (elim n gs (elimStep n acc g)).2 = binaryCost (elimStep n acc g).2 + binaryCost gs := by omega
    apply ih (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)])
             (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)])
             (elimStep n acc g)
             (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) _ htail_eq
    obtain ⟨hl1, hl2, hwi⟩ := hag
    refine ⟨by simp [elimStep, hl1], by simp [elimStep, hl2], ?_⟩
    intro i hi
    by_cases hil : i = acc.1.length
    · subst hil
      simp only [elimStep] at hi ⊢
      rw [getD_snoc_eq] at hi
      rw [hl1, getD_snoc_eq, ← hl1, hl2, getD_snoc_eq]
      have hgok := hok g List.mem_cons_self
      obtain ⟨op, args⟩ := g
      obtain ⟨hop, hlen⟩ := hgok
      dsimp only [elimStep] at hi hstep_eq
      rw [binaryCost_append] at hstep_eq
      rcases hop with rfl | rfl | rfl
      · rw [isBinary_and] at hstep_eq
        rcases args with _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, l⟩⟩⟩
        · simp [simplify, simpAnd, binaryCost] at hstep_eq
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rw [List.map_cons, List.map_nil, h1] at hstep_eq
            simp [simplify, simpAnd, binaryCost] at hstep_eq
          · rw [List.map_cons, List.map_nil, h1] at hstep_eq
            simp [simplify, simpAnd, binaryCost] at hstep_eq
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rcases h2 : acc.1.getD k2 (Sum.inl false) with d | b <;>
              (rw [List.map_cons, List.map_cons, List.map_nil, h1, h2] at hstep_eq;
               simp [simplify, simpAnd, binaryCost] at hstep_eq)
          · rcases h2 : acc.1.getD k2 (Sum.inl false) with d | b
            · rw [List.map_cons, List.map_cons, List.map_nil, h1, h2] at hstep_eq
              simp [simplify, simpAnd, binaryCost] at hstep_eq
            · have e1 := hwi k1 ⟨a, h1⟩
              have e2 := hwi k2 ⟨b, h2⟩
              simp [GateOp.eval, List.getD_eq_getElem?_getD] at e1 e2 ⊢
              rw [e1, e2]
        · simp at hlen
      · rw [isBinary_or] at hstep_eq
        rcases args with _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, l⟩⟩⟩
        · simp [simplify, simpOr, binaryCost] at hstep_eq
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rw [List.map_cons, List.map_nil, h1] at hstep_eq
            simp [simplify, simpOr, binaryCost] at hstep_eq
          · rw [List.map_cons, List.map_nil, h1] at hstep_eq
            simp [simplify, simpOr, binaryCost] at hstep_eq
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rcases h2 : acc.1.getD k2 (Sum.inl false) with d | b <;>
              (rw [List.map_cons, List.map_cons, List.map_nil, h1, h2] at hstep_eq;
               simp [simplify, simpOr, binaryCost] at hstep_eq)
          · rcases h2 : acc.1.getD k2 (Sum.inl false) with d | b
            · rw [List.map_cons, List.map_cons, List.map_nil, h1, h2] at hstep_eq
              simp [simplify, simpOr, binaryCost] at hstep_eq
            · have e1 := hwi k1 ⟨a, h1⟩
              have e2 := hwi k2 ⟨b, h2⟩
              simp [GateOp.eval, List.getD_eq_getElem?_getD] at e1 e2 ⊢
              rw [e1, e2]
        · simp at hlen
      · rcases args with _ | ⟨k1, l⟩
        · simp [simplify, simpNot] at hi
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rw [List.map_cons, h1] at hi
            simp [simplify, simpNot] at hi
          · have e1 := hwi k1 ⟨a, h1⟩
            simp [GateOp.eval, List.getD_eq_getElem?_getD] at e1 ⊢
            rw [e1]
    · simp only [elimStep] at hi ⊢
      rw [getD_snoc_ne _ _ _ _ hil] at hi
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact hwi i hi
end PEqualNP.Outside.L_meta_30254.LeafRestriction

namespace PEqualNP.Outside.L_meta_30254.LeafRestriction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def minor (x : Fin 7 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 3) || (x 0 && x 4) || (x 2 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6)
def embed (b : Bool) (x : Fin 7 → Bool) : Fin 8 → Bool :=
  ![x 6, x 3, b, x 4, x 5, x 0, x 1, x 2]
def initial : List Stat := [.inr 6, .inr 3, .inl false, .inr 4, .inr 5, .inr 0, .inr 1, .inr 2]

theorem minorCorrect : ∀ x, f (embed false x) = minor x := by decide +kernel

private theorem initialInv (x : Fin 7 → Bool) :
    Inv 7 (List.ofFn x) (List.ofFn (embed false x)) (initial, []) := by
  refine ⟨by simp [initial], ?_⟩
  intro i
  by_cases h : i < 8
  · interval_cases i <;> constructor <;> first | rfl | norm_num [initial, statValid]
  · rw [List.getD_eq_default initial _ (by simpa [initial] using Nat.le_of_not_gt h),
      List.getD_eq_default (List.ofFn (embed false x)) _ (by simpa using Nat.le_of_not_gt h)]
    exact ⟨trivial, rfl⟩

private def probe : Fin 7 → Bool := fun i => decide (i = 1)

private theorem initialAgree : AgreeNonConst initial
    (List.ofFn (embed false probe)) (List.ofFn (embed true probe)) := by
  refine ⟨rfl,rfl,?_⟩
  intro i hi
  by_cases h : i < 8
  · interval_cases i <;> first | rfl | simp [initial] at hi
  · rw [List.getD_eq_default (List.ofFn _) _ (by simpa using Nat.le_of_not_gt h),
      List.getD_eq_default (List.ofFn _) _ (by simpa using Nat.le_of_not_gt h)]

theorem liftMinor (bound : ∀ (gs : List Gate) (o : ℕ), FanInTwo ⟨gs,o⟩ →
    (∀ y, Circuit.eval ⟨gs,o⟩ (List.ofFn y) = minor y) → 12 ≤ binaryCost gs)
    (gs : List Gate) (o : ℕ) (basis : FanInTwo ⟨gs,o⟩)
    (hasNot : ∃ gate ∈ gs, gate.op = GateOp.not)
    (computes : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = f x) : 14 ≤ gs.length := by
  have hg : ∀ g ∈ gs, legal g := by
    intro g h; have hp := basis g h
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp.1, hp.2⟩
  let res := elim 7 gs (initial, [])
  have evalRes (y : Fin 7 → Bool) :
      statVal (wiresFrom res.2 (List.ofFn y)) (res.1.getD o (.inl false)) = minor y := by
    have ok := inv_elim 7 (List.ofFn y) (by simp) gs _ _ hg (initialInv y)
    exact (ok.2 o).2.trans ((computes (embed false y)).trans (minorCorrect y))
  obtain ⟨o', hout⟩ : ∃ o', res.1.getD o (.inl false) = .inr o' := by
    cases hs : res.1.getD o (.inl false) with
    | inr v => exact ⟨v,rfl⟩
    | inl c =>
      have h0 := evalRes (fun _ => false); have h1 := evalRes (fun _ => true)
      rw [hs] at h0 h1
      exact Bool.noConfusion (show false = true from h0.symm.trans h1)
  have small : binaryCost res.2 < binaryCost gs := by
    have le := elim_binCost_le 7 gs (initial, [])
    change binaryCost res.2 ≤ 0 + binaryCost gs at le
    by_contra bad
    have eq : binaryCost res.2 = binaryCost ([] : List Gate) + binaryCost gs := by
      change binaryCost res.2 = 0 + binaryCost gs; omega
    have same := (elim_agree_of_eq_binCost 7 gs _ _ (initial, []) hg initialAgree eq).2.2 o ⟨o',hout⟩
    have h0 := computes (embed false probe); have h1 := computes (embed true probe)
    exact Bool.noConfusion (show false = true from h0.symm.trans (same.trans h1))
  have cost := bound res.2 o' (by
    intro g h
    obtain ⟨op, fan⟩ := elim_legal 7 gs (initial, []) (by simp) g h
    exact ⟨by rcases op with h | h | h <;> simp [h], fan⟩) (by
      intro y; have eq := evalRes y; rw [hout] at eq; exact eq)
  obtain ⟨g,hg',hop⟩ := hasNot
  have lt : binaryCost gs < gs.length :=
    (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
      ⟨g,hg', by simp [isBinary, hop]⟩
  omega

end PEqualNP.Outside.L_meta_30254.LeafRestriction

namespace PEqualNP.Outside.L_meta_30254
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Seven

theorem countEq (gs : List Gate) : LeafRestriction.binaryCost gs = countNonNot gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [LeafRestriction.binaryCost_cons, countNonNot, ih]
    obtain ⟨op, ins⟩ := g
    cases op <;> rfl

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem minorFloor (gs : List Gate) (o : ℕ) (legal : FanInTwo ⟨gs,o⟩)
    (hc : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = LeafRestriction.minor x) :
    12 ≤ LeafRestriction.binaryCost gs := by
  let raw : List (BitVec 128) := [BitVec.ofNat 128 (packedLimbs [0xaa,0xaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaa]), BitVec.ofNat 128 (packedLimbs [0xcc,0xccccccccccccccc,0xccccccccccccccc]), BitVec.ofNat 128 (packedLimbs [0xf0,0xf0f0f0f0f0f0f0f,0xf0f0f0f0f0f0f0]), BitVec.ofNat 128 (packedLimbs [0xff,0xff00ff00ff00f,0xf00ff00ff00ff00]), BitVec.ofNat 128 (packedLimbs [0xff,0xff0000ffff0000f,0xfff0000ffff0000]), BitVec.ofNat 128 (packedLimbs [0xff,0xffffff00000000f,0xfffffff00000000]), BitVec.ofNat 128 (packedLimbs [0xff,0xffffffffffffff0,0x0])]
  let goal : BitVec 128 := BitVec.ofNat 128 (packedLimbs [0xff,0xfffffefffffefef,0xffefffcfefaee00])
  have hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin 7 => r.testBit j.val) 7 0 = true := by decide +kernel
  have hGoal : hcsCheckPow (fun r => goal.getLsbD r == LeafRestriction.minor (fun j : Fin 7 => r.testBit j.val)) 7 0 = true := by decide +kernel
  have binRoot : BinLower (fullMask 128) (raw.map BitVec.toNat) goal.toNat 12 :=
    hcsBinLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) s74Bin
  rw [countEq]
  exact hcsBinaryFloor (n := 7) raw goal 12 _ hRaw hGoal binRoot gs o (by
    intro g hg; simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using legal g hg) hc
end PEqualNP.Outside.L_meta_30254

theorem PEqualNP.Outside.L_meta_30254 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  exact PEqualNP.Outside.L_meta_30254.compareWith (PEqualNP.Outside.L_meta_30254.LeafRestriction.liftMinor PEqualNP.Outside.L_meta_30254.minorFloor)
