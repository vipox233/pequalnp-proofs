import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_32199.Contraction
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
def GateWord (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  (∃ a, AvailableWord mask bank a ∧ out = mask ^^^ a) ∨
  (∃ a b, AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b))
def WordBuilds (mask : Nat) (roots : List Word) : List Word → Prop
  | [] => True
  | w :: ws => GateWord mask roots w ∧ WordBuilds mask (w :: roots) ws
def Lower (mask : Nat) (roots : List Word) (target : Word) (minimum : Nat) : Prop :=
  ∀ values, WordBuilds mask roots values →
    AvailableWord mask (values ++ roots) target → minimum ≤ values.length
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
def full : ℕ := 22300745198530623141535718272648361505980415
def IsRect (R : ℕ → Prop) : Prop :=
  ∀ e i e' i' : ℕ, e < 12 → i < 12 → e' < 12 → i' < 12 →
    R (12 * e + i) → R (12 * e' + i') → R (12 * e + i')
def Part (zs : List ((ℕ → Prop) × ℕ)) : Prop :=
  (∀ z ∈ zs, IsRect z.1) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → q < 144) ∧
  (zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False)) ∧
  (∀ q, q < 144 → ∃ z ∈ zs, z.1 q) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true)
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
def GateWordMono (mask : Nat) (bank : List Word) (out : Word) : Prop :=
  ∃ a b, AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b)
def WordBuildsMono (mask : Nat) (roots : List Word) : List Word → Prop
  | [] => True
  | w :: ws => GateWordMono mask roots w ∧ WordBuildsMono mask (w :: roots) ws
def MonoLower (mask : Nat) (roots : List Word) (target : Word) (minimum : Nat) : Prop :=
  ∀ values, WordBuildsMono mask roots values →
    AvailableWord mask (values ++ roots) target → minimum ≤ values.length
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
theorem essentialLowerBin {mask target : Word} {stock : List Word} {witnesses : List Witness} {minimum : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (bound : minimum ≤ (witnesses.map (fun e => normWord mask (witnessWord e))).toFinset.card - 1) :
    BinLower mask stock target minimum := by
  intro values build hit
  obtain ⟨k, S, hk, live, sub⟩ := extractBinLive masked build hit proper
  have card := Finset.card_le_card (essentialWordsInBin ok sub live)
  have size := liveBinSize live
  omega
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
theorem countNonNot_le_sub {gs : List PEqualNP.CircuitLowerBounds.Gate}
    (h : ∃ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) :
    countNonNot gs + 1 ≤ gs.length := by
  induction gs with
  | nil => obtain ⟨_, hm, _⟩ := h; simp at hm
  | cons g gs ih =>
    have hle : ∀ l, countNonNot l ≤ l.length := by
      intro l; induction l with
      | nil => simp [countNonNot]
      | cons x xs ihx => simp only [countNonNot, List.length_cons]; cases isNotOp x.op <;> simp <;> omega
    obtain ⟨g', hm, hop⟩ := h
    rcases List.mem_cons.mp hm with rfl | hm
    · simp only [countNonNot, hop, isNotOp, ite_true, Nat.zero_add, List.length_cons]
      have := hle gs; omega
    · have := ih ⟨g', hm, hop⟩
      simp only [countNonNot, List.length_cons]
      cases isNotOp g.op <;> simp <;> omega
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
end PEqualNP.Outside.L_meta_32199.Contraction

namespace PEqualNP.Outside.L_meta_32199.Donor
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
def mask256:Nat:=2 ^ 256 - 1
def negD (d w:Nat):Nat:=(w^^^mask256)&&&d
def andD (d a b:Nat):Nat:=(a&&&b)&&&d
def orD (d a b:Nat):Nat:=(a|||b)&&&d
def opD (d:Nat) (op:Nat) (a b:Nat):Nat :=
  if op==0 then andD d a b
  else if op==1 then orD d a b
  else if op==2 then andD d a (negD d b)
  else andD d (negD d a) b
def allowedB (u:Bool) (op:Nat):Bool :=
  decide (op < 2)||(u&&decide (op < 4))
def flipOp (op:Nat):Nat :=
  if op==2 then 3 else if op==3 then 2 else op
def nrmD (u:Bool) (d w:Nat):Nat :=
  if u&&w.testBit 0 then negD d w else w&&&d
def kept {α : Type} (b:Bool) (x : α) (xs:List α):List α :=
  if b then x :: xs else xs
def RunD (u:Bool) (d y:Nat) (t : ℕ) (ws:List Nat) : Prop :=
  ∀ P : ℕ → List Nat → Prop,P 0 [y] →
    (∀ {s xs zs},List.Perm xs zs → P s xs → P s zs) →
    (∀ {s a b r} (op:Nat) (ka kb:Bool),
      allowedB u op = true →
      opD d op a b ≠ 0 →
      opD d op a b ≠ d →
      opD d op a b ∉ (a :: b :: r) →
      P s (opD d op a b :: kept ka a (kept kb b r)) →
      P (s + 1) (a :: b :: r)) → P t ws
section
variable {u:Bool} {d y:Nat}
theorem Run.done : RunD u d y 0 [y]:=fun _ dn _ _=>dn
theorem Run.perm {s xs zs} (p : List.Perm xs zs) (h : RunD u d y s xs) :
    RunD u d y s zs:=fun P dn q b=>q p (h P dn q b)
theorem Run.two {s a b r} (op:Nat) (ka kb:Bool)
    (hop : allowedB u op = true)
    (h0 : opD d op a b ≠ 0) (hd : opD d op a b ≠ d) (hm : opD d op a b ∉ (a :: b :: r))
    (h : RunD u d y s (opD d op a b :: kept ka a (kept kb b r))) :
    RunD u d y (s + 1) (a :: b :: r):=fun P dn q v=>v op ka kb hop h0 hd hm (h P dn q v)
theorem Run.fold {P : ∀ t ws,RunD u d y t ws → Prop}
    (done : P 0 [y] Run.done)
    (perm : ∀ {s xs zs} (hp : List.Perm xs zs) (h : RunD u d y s xs),
      P s xs h → P s zs (Run.perm hp h))
    (two : ∀ {s a b r} (op:Nat) (ka kb:Bool)
      (hop : allowedB u op = true)
      (h0 : opD d op a b ≠ 0) (hd : opD d op a b ≠ d) (hm : opD d op a b ∉ (a :: b :: r))
      (h : RunD u d y s (opD d op a b :: kept ka a (kept kb b r))),
      P _ _ h → P _ _ (Run.two op ka kb hop h0 hd hm h))
    {t ws} (h : RunD u d y t ws) : P t ws h:=by
  have hex:=h (fun s xs=>∃ h' : RunD u d y s xs,P s xs h')
    ⟨Run.done,done⟩
    (fun hp ⟨h',ih⟩=>⟨Run.perm hp h',perm hp h' ih⟩)
    (fun op ka kb hop h0 hd hm ⟨h',ih⟩=>⟨Run.two op ka kb hop h0 hd hm h',two op ka kb hop h0 hd hm h' ih⟩)
  exact hex.elim fun _ hp=>hp
end
theorem allowed_cases {u:Bool} {op:Nat} (h : allowedB u op = true) :
    op = 0 ∨ op = 1 ∨ (u = true ∧ op = 2) ∨ (u = true ∧ op = 3):=by
  simp only [allowedB,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with h | ⟨hu,h⟩
  · omega
  · have : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3:=by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl ⟨hu,rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hu,rfl⟩))
theorem opD_comm {u:Bool} (d:Nat) {op:Nat} (hop : allowedB u op = true) (a b:Nat) :
    opD d op a b = opD d (flipOp op) b a:=by
  rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
    simp [opD,flipOp,andD,orD,Nat.and_comm,Nat.or_comm]
theorem flipOp_allowed {u:Bool} {op:Nat} (hop : allowedB u op = true) :
    allowedB u (flipOp op) = true:=by
  rcases allowed_cases hop with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [allowedB,flipOp]
theorem kept_map {α β : Type} (e : α → β) (b:Bool) (x : α) (xs:List α) :
    (kept b x xs).map e = kept b (e x) (xs.map e):=by cases b <;> simp [kept]
theorem mem_kept {α : Type} (b:Bool) (x a : α) (xs:List α) :
    a ∈ kept b x xs ↔ (b = true ∧ a = x) ∨ a ∈ xs:=by cases b <;> simp [kept]
theorem nodup_kept {α : Type} (b:Bool) (x : α) (xs:List α) (h : xs.Nodup) (hx : x ∉ xs) :
    (kept b x xs).Nodup:=by
  cases b
  · simpa [kept] using h
  · simpa [kept] using And.intro hx h
theorem keep_perm {α : Type} {xs ys:List α} (p : xs.Perm ys) (b:Bool) (a : α) :
    (kept b a xs).Perm (kept b a ys):=by cases b <;> simpa [kept] using p
theorem run_len {u d y s xs} (h : RunD u d y s xs) :
    xs.length ≤ s + 1:=by
  induction h using Run.fold with
  | done=>simp
  | perm hp _ ih=>rwa [← hp.length_eq]
  | two _ ka kb _ _ _ _ _ ih=>cases ka <;> cases kb <;> simp_all [kept] <;> omega
theorem zero_done {u d y t ws} (h : RunD u d y t ws) :
    t = 0 → ws = [y]:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>intro ht; rw [ih ht] at p; exact List.perm_singleton.1 p.symm
  | two=>simp
def IsConst (d w:Nat) : Prop:=(w&&&d) = 0 ∨ (w&&&d) = d
def isConstB (d w:Nat):Bool:=(w&&&d==0)||(w&&&d==d)
theorem isConstB_iff (d w:Nat) : isConstB d w = true ↔ IsConst d w:=by
  simp [isConstB,IsConst]
def Avail (u:Bool) (d:Nat) (bank:List Nat) (w:Nat) : Prop :=
  IsConst d w ∨ (∃ v ∈ bank,(v&&&d) = (w&&&d)) ∨ (u = true ∧ ∃ v ∈ bank,(v&&&d) = negD d w)
def availB (u:Bool) (d:Nat) (bank:List Nat) (w:Nat):Bool :=
  let m:=w&&&d
  m==0||m==d||bank.any (fun v=>(v&&&d)==m) ||
    (u&&bank.any (fun v=>(v&&&d)==negD d w))
theorem availB_iff (u:Bool) (d:Nat) (bank:List Nat) (w:Nat) :
    availB u d bank w = true ↔ Avail u d bank w:=by
  simp [availB,Avail,IsConst,or_assoc]
def NatReach (u:Bool) (d:Nat) (roots:List Nat):Nat → List Nat → Prop
  | 0,bank=>bank = roots
  | p + 1,bank =>
    ∃ b a c op,allowedB u op = true ∧ bank = opD d op a c :: b ∧
      NatReach u d roots p b ∧ Avail u d b a ∧ Avail u d b c
def Lower (u:Bool) (d:Nat) (roots:List Nat) (T:Nat) (L:Nat) : Prop :=
  ∀ p bank,NatReach u d roots p bank → Avail u d bank T → L ≤ p
theorem opD_and_sub {d d1:Nat} (hd : d&&&mask256 = d) (hsub : d&&&d1 = d) (op a b:Nat) :
    opD d1 op a b&&&d = opD d op a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  have h1:=congrArg (fun v=>v.testBit i) hd
  have h2:=congrArg (fun v=>v.testBit i) hsub
  unfold opD
  split_ifs <;> simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] at * <;>
    cases hi : d.testBit i <;> simp_all
theorem negD_invol {d:Nat} (hd : d&&&mask256 = d) (a:Nat) :
    negD d (negD d a) = a&&&d:=by
  apply Nat.eq_of_testBit_eq; intro i
  have h1:=congrArg (fun v=>v.testBit i) hd
  simp only [negD,Nat.testBit_and,Nat.testBit_xor] at *
  cases hi : d.testBit i <;> cases ha : a.testBit i <;> simp_all
theorem negD_mask (d a:Nat) : negD d (a&&&d) = negD d a:=by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [negD,Nat.testBit_and,Nat.testBit_xor]
  cases d.testBit i <;> simp
theorem opD_mask_self (d op a b:Nat) : opD d op a b&&&d = opD d op a b:=by
  apply Nat.eq_of_testBit_eq; intro i
  unfold opD; split_ifs <;> simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor] <;>
    cases d.testBit i <;> simp
theorem negD_const {d:Nat} (hd : d&&&mask256 = d) {a:Nat} (hc : IsConst d a) :
    IsConst d (negD d a):=by
  rcases hc with h0 | h1
  · right; apply Nat.eq_of_testBit_eq; intro i
    have h0i:=congrArg (fun v=>v.testBit i) h0
    have hdi:=congrArg (fun v=>v.testBit i) hd
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
  · left; apply Nat.eq_of_testBit_eq; intro i
    have h1i:=congrArg (fun v=>v.testBit i) h1
    have hdi:=congrArg (fun v=>v.testBit i) hd
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at *
    cases h1' : d.testBit i <;> cases h2' : a.testBit i <;> simp_all
theorem avail_cons {u:Bool} {d:Nat} {bank:List Nat} (z w:Nat) (h : Avail u d bank w) :
    Avail u d (z :: bank) w:=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨hu,v,hv,he⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl ⟨v,List.mem_cons_of_mem _ hv,he⟩)
  · exact Or.inr (Or.inr ⟨hu,v,List.mem_cons_of_mem _ hv,he⟩)
theorem avail_of_eq {u:Bool} {d:Nat} {bank:List Nat} {v w:Nat}
    (he : v&&&d = w&&&d) (h : Avail u d bank v) : Avail u d bank w:=by
  rcases h with (h0 | h1) | ⟨x,hx,hxe⟩ | ⟨hu,x,hx,hxe⟩
  · exact Or.inl (Or.inl (he.symm.trans h0))
  · exact Or.inl (Or.inr (he.symm.trans h1))
  · exact Or.inr (Or.inl ⟨x,hx,hxe.trans he⟩)
  · exact Or.inr (Or.inr ⟨hu,x,hx,hxe.trans (by rw [← negD_mask,he,negD_mask])⟩)
theorem avail_neg {d:Nat} (hd : d&&&mask256 = d) {bank:List Nat} {w:Nat}
    (h : Avail true d bank w) : Avail true d bank (negD d w):=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨_,v,hv,he⟩
  · exact Or.inl (negD_const hd hc)
  · refine Or.inr (Or.inr ⟨rfl,v,hv,?_⟩)
    rw [negD_invol hd,he]
  · refine Or.inr (Or.inl ⟨v,hv,?_⟩)
    rw [he]; simp [negD,Nat.and_assoc,Nat.and_self]
theorem opD_const_left {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {op:Nat}
    (hop : allowedB u op = true) {a b:Nat} (hc : IsConst d a) :
    (opD d op a b&&&d = 0) ∨ (opD d op a b&&&d = d) ∨
      (opD d op a b&&&d = b&&&d) ∨ (u = true ∧ opD d op a b&&&d = negD d b):=by
  rcases allowed_cases hop with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · rcases hc with h0 | h1
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,andD,Nat.testBit_and,Nat.zero_testBit,beq_self_eq_true,ite_true] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      simp only [opD,andD,Nat.testBit_and,beq_self_eq_true,ite_true] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,orD,Nat.testBit_and,Nat.testBit_or,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      simp only [opD,orD,Nat.testBit_and,Nat.testBit_or,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · right; right; right; refine ⟨hu,?_⟩
      apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · rcases hc with h0 | h1
    · right; right; left; apply Nat.eq_of_testBit_eq; intro i
      have h0i:=congrArg (fun v=>v.testBit i) h0
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
    · left; apply Nat.eq_of_testBit_eq; intro i
      have h1i:=congrArg (fun v=>v.testBit i) h1
      have hdi:=congrArg (fun v=>v.testBit i) hd
      simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit,beq_self_eq_true,ite_true,ite_false] at *
      cases hd' : d.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
theorem countP_kept_ge {α : Type} (p : α → Bool) (b:Bool) (a : α) (xs:List α) :
    xs.countP p ≤ (kept b a xs).countP p:=by
  cases b <;> simp [kept,List.countP_cons] <;> split <;> omega
theorem contraction {u:Bool} {d d1 T:Nat} (hd : d&&&mask256 = d) (hsub : d&&&d1 = d)
    (hnc : ¬ IsConst d T) {s ws} (h : RunD u d1 T s ws) {roots p bank}
    (hp:NatReach u d roots p bank) (hs : ∀ w ∈ ws,Avail u d bank w) :
    ∃ q next,NatReach u d roots q next ∧ Avail u d next T ∧
      q + ws.countP (isConstB d) ≤ p + s:=by
  induction h using Run.fold generalizing p bank with
  | done =>
    have hfalse : isConstB d T = false:=by
      cases hc : isConstB d T with
      | false=>rfl
      | true=>exact absurd ((isConstB_iff d T).1 hc) hnc
    exact ⟨p,bank,hp,hs T (by simp),by simp [hfalse]⟩
  | perm eq _ ih =>
    obtain ⟨q,next,hq,ht,hle⟩:=ih hp (fun w hw=>hs w (eq.mem_iff.1 hw))
    rw [eq.countP_eq] at hle
    exact ⟨q,next,hq,ht,hle⟩
  | @two s a b r op ka kb hop _ _ _ _ ih =>
    have ha:=hs a List.mem_cons_self
    have hb:=hs b (List.mem_cons_of_mem _ List.mem_cons_self)
    set z1:=opD d1 op a b
    set z0:=opD d op a b
    have hz_eq : z1&&&d = z0&&&d:=by
      rw [opD_and_sub hd hsub,opD_mask_self]
    by_cases hcab : IsConst d a ∨ IsConst d b
    · have hz_av : Avail u d bank z1:=by
        apply avail_of_eq hz_eq.symm
        rcases hcab with hca | hcb
        · rcases opD_const_left hd hop hca with h0 | h1 | he | ⟨rfl,hn⟩
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm hb
          · exact avail_of_eq (by rw [hn]; simp [negD,Nat.and_assoc,Nat.and_self]) (avail_neg hd hb)
        · dsimp only [z0]; rw [opD_comm d hop a b]
          rcases opD_const_left hd (flipOp_allowed hop) hcb with h0 | h1 | he | ⟨rfl,hn⟩
          · exact Or.inl (Or.inl h0)
          · exact Or.inl (Or.inr h1)
          · exact avail_of_eq he.symm ha
          · exact avail_of_eq (by rw [hn]; simp [negD,Nat.and_assoc,Nat.and_self]) (avail_neg hd ha)
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r),Avail u d bank w:=by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept,mem_kept] at hw
          rcases hw with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hw
          · exact ha
          · exact hb
          · exact hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw))
      obtain ⟨q,next,hq,ht,hle⟩:=ih hp hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      have hcost : (if isConstB d a = true then 1 else 0) + (if isConstB d b = true then 1 else 0)
          ≤ 1 + (if isConstB d z1 = true then 1 else 0):=by
        rcases hcab with hca | hcb
        · have ha1 : isConstB d a = true:=(isConstB_iff _ _).2 hca
          rcases opD_const_left hd hop hca with h0 | h1 | he | ⟨_,hn⟩
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inl (hz_eq.trans h0))
            simp [ha1,hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inr (hz_eq.trans h1))
            simp [ha1,hz1]; split <;> omega
          · have hzb : isConstB d z1 = isConstB d b:=by simp only [isConstB,hz_eq.trans he]
            simp [ha1,hzb]
          · have hzb : isConstB d z1 = isConstB d b:=by
              apply Bool.eq_iff_iff.2; rw [isConstB_iff,isConstB_iff]
              have hnm : negD d b&&&d = negD d b:=by simp [negD,Nat.and_assoc,Nat.and_self]
              constructor
              · intro hz; have hnb : IsConst d (negD d b):=by
                  rcases hz with h0 | h1
                  · exact Or.inl (hnm.trans (hn.symm.trans (hz_eq.symm.trans h0)))
                  · exact Or.inr (hnm.trans (hn.symm.trans (hz_eq.symm.trans h1)))
                have h2:=negD_const hd hnb
                rw [negD_invol hd] at h2
                rcases h2 with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)]
              · intro hb'; have hnb:=negD_const hd hb'
                rcases hnb with h0 | h1
                · exact Or.inl (hz_eq.trans (hn.trans (hnm.symm.trans h0)))
                · exact Or.inr (hz_eq.trans (hn.trans (hnm.symm.trans h1)))
            simp [ha1,hzb]
        · have hb1 : isConstB d b = true:=(isConstB_iff _ _).2 hcb
          have hz_eq' : z1&&&d = opD d (flipOp op) b a&&&d:=by rw [hz_eq]; dsimp only [z0]; rw [opD_comm d hop a b]
          rcases opD_const_left hd (flipOp_allowed hop) hcb with h0 | h1 | he | ⟨_,hn⟩
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inl (hz_eq'.trans h0))
            simp [hb1,hz1]; split <;> omega
          · have hz1 : isConstB d z1 = true:=(isConstB_iff _ _).2 (Or.inr (hz_eq'.trans h1))
            simp [hb1,hz1]; split <;> omega
          · have hza : isConstB d z1 = isConstB d a:=by simp only [isConstB,hz_eq'.trans he]
            simp [hb1,hza]
          · have hza : isConstB d z1 = isConstB d a:=by
              apply Bool.eq_iff_iff.2; rw [isConstB_iff,isConstB_iff]
              have hnm : negD d a&&&d = negD d a:=by simp [negD,Nat.and_assoc,Nat.and_self]
              constructor
              · intro hz; have hna : IsConst d (negD d a):=by
                  rcases hz with h0 | h1
                  · exact Or.inl (hnm.trans (hn.symm.trans (hz_eq'.symm.trans h0)))
                  · exact Or.inr (hnm.trans (hn.symm.trans (hz_eq'.symm.trans h1)))
                have h2:=negD_const hd hna
                rw [negD_invol hd] at h2
                rcases h2 with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)]
              · intro ha'; have hna:=negD_const hd ha'
                rcases hna with h0 | h1
                · exact Or.inl (hz_eq'.trans (hn.trans (hnm.symm.trans h0)))
                · exact Or.inr (hz_eq'.trans (hn.trans (hnm.symm.trans h1)))
            simp [hb1,hza]
      simp only [List.countP_cons] at hle ⊢
      exact ⟨q,next,hq,ht,by omega⟩
    · have hna : isConstB d a = false:=by
        cases h : isConstB d a with | false=>rfl | true=>exact absurd (Or.inl ((isConstB_iff _ _).1 h)) hcab
      have hnb : isConstB d b = false:=by
        cases h : isConstB d b with | false=>rfl | true=>exact absurd (Or.inr ((isConstB_iff _ _).1 h)) hcab
      have hreach':NatReach u d roots (p + 1) (z0 :: bank):=⟨bank,a,b,op,hop,rfl,hp,ha,hb⟩
      have hz_av : Avail u d (z0 :: bank) z1:=Or.inr (Or.inl ⟨z0,List.mem_cons_self,hz_eq.symm⟩)
      have hs' : ∀ w ∈ z1 :: kept ka a (kept kb b r),Avail u d (z0 :: bank) w:=by
        intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact hz_av
        · rw [mem_kept,mem_kept] at hw
          rcases hw with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hw
          · exact avail_cons _ _ ha
          · exact avail_cons _ _ hb
          · exact avail_cons _ _ (hs w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
      obtain ⟨q,next,hq,ht,hle⟩:=ih hreach' hs'
      have hkr : r.countP (isConstB d) ≤ (kept ka a (kept kb b r)).countP (isConstB d) :=
        le_trans (countP_kept_ge _ kb b r) (countP_kept_ge _ ka a _)
      simp only [List.countP_cons,hna,hnb,Bool.false_eq_true,ite_false] at hle ⊢
      exact ⟨q,next,hq,ht,by omega⟩
theorem nrmD_mask (u:Bool) (d w:Nat) : nrmD u d w&&&d = nrmD u d w:=by
  unfold nrmD; split <;> simp [negD,Nat.and_assoc,Nat.and_self]
theorem nrmD_of_bit0_false (u:Bool) (d w:Nat) (hw : w.testBit 0 = false) :
    nrmD u d w = w&&&d:=by
  simp [nrmD,hw]
theorem nrmD_and_d {d:Nat} (hd0 : d.testBit 0 = true) (u:Bool) (w:Nat) :
    nrmD u d (w&&&d) = nrmD u d w:=by
  unfold nrmD
  rw [Nat.testBit_and,hd0,Bool.and_true,negD_mask,Nat.and_assoc,Nat.and_self]
theorem nrmD_neg {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true) (w:Nat) :
    nrmD true d (negD d w) = nrmD true d w:=by
  have hm0 : mask256.testBit 0 = true:=by decide
  unfold nrmD
  have hnb : (negD d w).testBit 0 = !w.testBit 0:=by
    simp only [negD,Nat.testBit_and,Nat.testBit_xor,hd0,hm0,Bool.and_true,Bool.xor_true]
  rw [hnb]
  cases hw : w.testBit 0
  · simp [negD_invol hd]
  · simp [negD,Nat.and_assoc,Nat.and_self]
theorem nrmD_const_iff {d:Nat} (hd : d&&&mask256 = d) (u:Bool) (w:Nat) :
    (nrmD u d w ≠ 0 ∧ nrmD u d w ≠ d) ↔ ¬ IsConst d w:=by
  unfold nrmD
  have hnm : negD d w&&&d = negD d w:=by simp [negD,Nat.and_assoc,Nat.and_self]
  split
  · constructor
    · rintro ⟨h0,h1⟩ hc
      rcases negD_const hd hc with hn0 | hn1
      · exact h0 (hnm.symm.trans hn0)
      · exact h1 (hnm.symm.trans hn1)
    · intro hnc; refine ⟨fun h0=>?_,fun h1=>?_⟩
      · have:=negD_const hd (a:=negD d w) (Or.inl (hnm.trans h0))
        rw [negD_invol hd] at this
        exact hnc (by rcases this with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)])
      · have:=negD_const hd (a:=negD d w) (Or.inr (hnm.trans h1))
        rw [negD_invol hd] at this
        exact hnc (by rcases this with e | e <;> [exact Or.inl (by simpa [Nat.and_assoc,Nat.and_self] using e); exact Or.inr (by simpa [Nat.and_assoc,Nat.and_self] using e)])
  · simp [IsConst,not_or]
theorem opD_bit {d:Nat} (hd : d&&&mask256 = d) (op a b i:Nat) (hdi : d.testBit i = true) :
    (opD d op a b).testBit i =
      if op==0 then a.testBit i&&b.testBit i
      else if op==1 then a.testBit i||b.testBit i
      else if op==2 then a.testBit i&&!(b.testBit i)
      else !(a.testBit i)&&b.testBit i:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hdi] at this; exact this
  unfold opD; split_ifs <;>
    simp only [andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,hdi,hmi,Bool.and_true,Bool.xor_true]
theorem nrmD_bit {d:Nat} (hd : d&&&mask256 = d) (w i:Nat) (hdi : d.testBit i = true) :
    (nrmD true d w).testBit i = if w.testBit 0 then !(w.testBit i) else w.testBit i:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hdi] at this; exact this
  unfold nrmD
  cases hw0 : w.testBit 0 <;>
    simp only [hw0,Bool.true_and,Bool.and_false,Bool.false_eq_true,ite_true,ite_false,
      negD,Nat.testBit_and,Nat.testBit_xor,hdi,hmi,Bool.and_true,Bool.xor_true]
theorem nrmD_opD {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (u:Bool) (op:Nat) (hop : allowedB u op = true) (a b:Nat) :
    ∃ op',allowedB u op' = true ∧
      nrmD u d (opD d op a b) = opD d op' (nrmD u d a) (nrmD u d b):=by
  cases u with
  | false =>
    rcases allowed_cases hop with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
    · exact ⟨0,rfl,by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [nrmD,opD,andD,Bool.false_and,Bool.false_eq_true,ite_false,beq_self_eq_true,ite_true,Nat.testBit_and]
        cases d.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,rfl,by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [nrmD,opD,orD,Bool.false_and,Bool.false_eq_true,ite_false]
        simp only [show (1==0) = false from rfl,show (1==1) = true from rfl,Bool.false_eq_true,ite_false,ite_true,Nat.testBit_and,Nat.testBit_or]
        cases d.testBit i <;> cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · contradiction
    · contradiction
  | true =>
    have h4 : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3:=by
      rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp
    have hbit : ∀ (e:Nat),
        (∀ i,d.testBit i = true →
          (nrmD true d (opD d op a b)).testBit i =
          (opD d e (nrmD true d a) (nrmD true d b)).testBit i) →
        nrmD true d (opD d op a b) = opD d e (nrmD true d a) (nrmD true d b):=by
      intro e h; apply Nat.eq_of_testBit_eq; intro i
      by_cases hdi : d.testBit i = true
      · exact h i hdi
      · have hf : d.testBit i = false:=Bool.eq_false_iff.2 hdi
        have h1:=congrArg (fun v=>v.testBit i) (nrmD_mask true d (opD d op a b))
        have h2:=congrArg (fun v=>v.testBit i) (opD_mask_self d e (nrmD true d a) (nrmD true d b))
        simp only [Nat.testBit_and,hf,Bool.and_false] at h1 h2; exact h1.symm.trans h2
    rcases h4 with rfl | rfl | rfl | rfl <;>
      cases ha0 : a.testBit 0 <;> cases hb0 : b.testBit 0
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨3,by decide,hbit 3 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨1,by decide,hbit 1 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨0,by decide,hbit 0 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
    · exact ⟨2,by decide,hbit 2 fun i hdi=>by rw [nrmD_bit hd _ i hdi,opD_bit hd _ _ _ 0 hd0,opD_bit hd _ _ _ i hdi,opD_bit hd _ _ _ i hdi,nrmD_bit hd a i hdi,nrmD_bit hd b i hdi,ha0,hb0]; cases a.testBit i <;> cases b.testBit i <;> rfl⟩
theorem avail_nrm_mem {u:Bool} {d:Nat} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    {b:List Nat} {w:Nat} (h : Avail u d b w) (hnc : ¬ IsConst d w) :
    nrmD u d w ∈ b.map (nrmD u d):=by
  rcases h with hc | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact absurd hc hnc
  · refine List.mem_map.2 ⟨v,hv,?_⟩
    rw [← nrmD_and_d hd0,he,nrmD_and_d hd0]
  · refine List.mem_map.2 ⟨v,hv,?_⟩
    rw [← nrmD_and_d hd0,he,nrmD_neg hd hd0]
theorem pull_two {u:Bool} {d Y k ws} (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hnd : ws.Nodup) (hprop : ∀ w ∈ ws,w ≠ 0 ∧ w ≠ d) (h : RunD u d Y k ws)
    {b:List Nat} {a c:Nat} (op:Nat) (hop : allowedB u op = true)
    (ha : Avail u d b a) (hc : Avail u d b c)
    (hsub : ∀ w ∈ ws,w ∈ nrmD u d (opD d op a c) :: b.map (nrmD u d)) :
    ∃ k' ws',k' ≤ k + 1 ∧ ws'.Nodup ∧ (∀ w ∈ ws',w ≠ 0 ∧ w ≠ d) ∧
      (∀ w ∈ ws',w ∈ b.map (nrmD u d)) ∧ RunD u d Y k' ws':=by
  set z:=nrmD u d (opD d op a c)
  by_cases hzm : z ∈ ws
  · by_cases hzb : z ∈ b.map (nrmD u d)
    · exact ⟨k,ws,by omega,hnd,hprop,fun w hw=>by
        rcases List.mem_cons.1 (hsub w hw) with rfl | hm
        · exact hzb
        · exact hm,h⟩
    · have hzp:=hprop z hzm
      obtain ⟨op',hop',hez⟩:=nrmD_opD hd hd0 u op hop a c
      have ha_nc : ¬ IsConst d a:=by
        intro hca
        have hznc : ¬ IsConst d (opD d op a c):=(nrmD_const_iff hd u _).1 hzp
        rcases opD_const_left hd hop hca with e0 | e1 | ec | ⟨rfl,en⟩
        · exact hznc (Or.inl e0)
        · exact hznc (Or.inr e1)
        · have hcn : ¬ IsConst d c:=fun hcc=>hznc (by rcases hcc with e | e <;> [exact Or.inl (ec.trans e); exact Or.inr (ec.trans e)])
          have hz_eq : z = nrmD u d c:=by dsimp only [z]; rw [← nrmD_and_d hd0 u (opD d op a c),ec,nrmD_and_d hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 hc hcn)
        · have hcn : ¬ IsConst d c:=fun hcc=>hznc (by
            rcases negD_const hd hcc with e | e
            · exact Or.inl (en.trans (by simpa [negD,Nat.and_assoc,Nat.and_self] using e))
            · exact Or.inr (en.trans (by simpa [negD,Nat.and_assoc,Nat.and_self] using e)))
          have hz_eq : z = nrmD true d c:=by dsimp only [z]; rw [← nrmD_and_d hd0 true (opD d op a c),en,nrmD_neg hd hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 hc hcn)
      have hc_nc : ¬ IsConst d c:=by
        intro hcc
        have hznc : ¬ IsConst d (opD d op a c):=(nrmD_const_iff hd u _).1 hzp
        have hcm : opD d op a c = opD d (flipOp op) c a:=opD_comm d hop a c
        rcases opD_const_left hd (flipOp_allowed hop) hcc with e0 | e1 | ea | ⟨rfl,en⟩
        · exact hznc (Or.inl (hcm.symm ▸ e0))
        · exact hznc (Or.inr (hcm.symm ▸ e1))
        · have hz_eq : z = nrmD u d a:=by
            dsimp only [z]; rw [← nrmD_and_d hd0 u (opD d op a c),hcm,ea,nrmD_and_d hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 ha ha_nc)
        · have hz_eq : z = nrmD true d a:=by
            dsimp only [z]; rw [← nrmD_and_d hd0 true (opD d op a c),hcm,en,nrmD_neg hd hd0]
          exact hzb (hz_eq ▸ avail_nrm_mem hd hd0 ha ha_nc)
      set a':=nrmD u d a
      set c':=nrmD u d c
      have ha'_mem : a' ∈ b.map (nrmD u d):=avail_nrm_mem hd hd0 ha ha_nc
      have hc'_mem : c' ∈ b.map (nrmD u d):=avail_nrm_mem hd hd0 hc hc_nc
      have ha'_prop : a' ≠ 0 ∧ a' ≠ d:=(nrmD_const_iff hd u a).2 ha_nc
      have hc'_prop : c' ≠ 0 ∧ c' ≠ d:=(nrmD_const_iff hd u c).2 hc_nc
      have hne_ac : a' ≠ c':=by
        intro heq
        have hz_eq : opD d op' a' a' = a' ∨ opD d op' a' a' = 0:=by
          rcases allowed_cases hop' with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
          · left; apply Nat.eq_of_testBit_eq; intro i
            have hm:=congrArg (fun v=>v.testBit i) (nrmD_mask u d a)
            change (a'&&&d).testBit i = a'.testBit i at hm
            simp only [opD,andD,Nat.testBit_and] at hm ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · left; apply Nat.eq_of_testBit_eq; intro i
            have hm:=congrArg (fun v=>v.testBit i) (nrmD_mask u d a)
            change (a'&&&d).testBit i = a'.testBit i at hm
            simp only [opD,orD,Nat.testBit_and,Nat.testBit_or] at hm ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · right; apply Nat.eq_of_testBit_eq; intro i
            have hdi:=congrArg (fun v=>v.testBit i) hd
            simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at hdi ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
          · right; apply Nat.eq_of_testBit_eq; intro i
            have hdi:=congrArg (fun v=>v.testBit i) hd
            simp only [opD,andD,negD,Nat.testBit_and,Nat.testBit_xor,Nat.zero_testBit] at hdi ⊢
            cases hd' : d.testBit i <;> cases ha' : a'.testBit i <;> simp_all
        have hez' : z = opD d op' a' a':=by
          have : z = opD d op' a' c':=hez
          rw [← heq] at this; exact this
        rcases hz_eq with e | e
        · exact hzb ((hez'.trans e).symm ▸ ha'_mem)
        · exact hzp.1 (hez'.trans e)
      set rest:=ws.erase z
      have hrest_nd : rest.Nodup:=hnd.erase z
      have hrest_sub : ∀ w ∈ rest,w ∈ b.map (nrmD u d):=by
        intro w hw
        have ⟨hne,hm⟩:=hnd.mem_erase_iff.1 hw
        rcases List.mem_cons.1 (hsub w hm) with rfl | hmb
        · exact absurd rfl hne
        · exact hmb
      have hrest_prop : ∀ w ∈ rest,w ≠ 0 ∧ w ≠ d:=fun w hw=>hprop w (List.mem_of_mem_erase hw)
      have hp1 : ws.Perm (z :: rest):=List.perm_cons_erase hzm
      have h1 : RunD u d Y k (opD d op' a' c' :: rest):=by
        rw [← hez]; exact Run.perm hp1 h
      set ka:=decide (a' ∈ rest)
      set kb:=decide (c' ∈ rest)
      set tail:=(rest.erase a').erase c'
      have htail_nd : tail.Nodup:=(hrest_nd.erase a').erase c'
      have hna_tail : a' ∉ tail:=by
        intro hm; exact hrest_nd.not_mem_erase (List.mem_of_mem_erase hm)
      have hnc_tail : c' ∉ tail:=(hrest_nd.erase a').not_mem_erase
      have hna_mid : a' ∉ kept kb c' tail:=by
        rw [mem_kept]; rintro (⟨_,h⟩ | h)
        · exact hne_ac h
        · exact hna_tail h
      have hrest_perm : rest.Perm (kept ka a' (kept kb c' tail)):=by
        refine (List.perm_ext_iff_of_nodup hrest_nd (nodup_kept ka a' _ (nodup_kept kb c' _ htail_nd hnc_tail) hna_mid)).2 ?_
        intro x
        rw [mem_kept,mem_kept,(hrest_nd.erase a').mem_erase_iff,hrest_nd.mem_erase_iff]
        by_cases hxa : x = a' <;> by_cases hxc : x = c' <;> by_cases hxr : x ∈ rest <;>
          simp_all [ka,kb]
      have h2:=Run.perm (hrest_perm.cons _) h1
      have hne0 : opD d op' a' c' ≠ 0:=fun h0=>hzp.1 (hez.trans h0)
      have hned : opD d op' a' c' ≠ d:=fun h1=>hzp.2 (hez.trans h1)
      have hnm : opD d op' a' c' ∉ (a' :: c' :: tail):=by
        rw [← hez,List.mem_cons,List.mem_cons]; rintro (e | e | hm)
        · exact hzb (by simpa [z,e] using ha'_mem)
        · exact hzb (by simpa [z,e] using hc'_mem)
        · exact hnd.not_mem_erase (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
      have h3 : RunD u d Y (k + 1) (a' :: c' :: tail):=Run.two op' ka kb hop' hne0 hned hnm h2
      have hnd3 : (a' :: c' :: tail).Nodup :=
        List.nodup_cons.2 ⟨by simp [hne_ac,hna_tail],List.nodup_cons.2 ⟨hnc_tail,htail_nd⟩⟩
      refine ⟨k + 1,a' :: c' :: tail,le_rfl,hnd3,?_,?_,h3⟩
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_prop
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_prop
          · exact hrest_prop w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
      · intro w hw; rcases List.mem_cons.1 hw with rfl | hw
        · exact ha'_mem
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact hc'_mem
          · exact hrest_sub w (List.mem_of_mem_erase (List.mem_of_mem_erase hw))
  · exact ⟨k,ws,by omega,hnd,hprop,fun w hw=>by
      rcases List.mem_cons.1 (hsub w hw) with rfl | hm
      · exact absurd hw hzm
      · exact hm,h⟩
theorem reach_to_run_aux {u:Bool} {d:Nat} {roots:List Nat} {p bank}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hr:NatReach u d roots p bank) :
    ∀ {Y k ws},ws.Nodup → (∀ w ∈ ws,w ≠ 0 ∧ w ≠ d) →
      (∀ w ∈ ws,w ∈ bank.map (nrmD u d)) → RunD u d Y k ws →
      ∃ k' ws',k' ≤ p + k ∧ ws'.Nodup ∧ (∀ w ∈ ws',w ≠ 0 ∧ w ≠ d) ∧
        (∀ w ∈ ws',w ∈ roots.map (nrmD u d)) ∧ RunD u d Y k' ws':=by
  induction p generalizing bank with
  | zero =>
    intro Y k ws hnd hprop hsub hrun
    subst hr
    exact ⟨k,ws,by omega,hnd,hprop,hsub,hrun⟩
  | succ p ih =>
    intro Y k ws hnd hprop hsub hrun
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=hr
    have hsub' : ∀ w ∈ ws,w ∈ nrmD u d (opD d op a c) :: b.map (nrmD u d):=by
      intro w hw; simpa [List.map_cons] using hsub w hw
    obtain ⟨k1,ws1,hk1,hnd1,hprop1,hsub1,hrun1⟩:=pull_two hd hd0 hnd hprop hrun op hop ha hc hsub'
    obtain ⟨k2,ws2,hk2,hnd2,hprop2,hsub2,hrun2⟩:=ih hrb hnd1 hprop1 hsub1 hrun1
    exact ⟨k2,ws2,by omega,hnd2,hprop2,hsub2,hrun2⟩
theorem reach_to_run {u:Bool} {d:Nat} {roots:List Nat} {T:Nat} {p bank}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hnc : ¬ IsConst d T) (hr:NatReach u d roots p bank) (ha : Avail u d bank T) :
    ∃ s ws,s ≤ p ∧ ws.Nodup ∧ (∀ w ∈ ws,w ∈ roots.map (·&&&d)) ∧ RunD u d (T&&&d) s ws:=by
  have hTmem : T&&&d ∈ bank.map (nrmD u d):=by
    have:=avail_nrm_mem hd hd0 ha hnc
    rwa [nrmD_of_bit0_false u d T hT0] at this
  have hprop : ∀ w ∈ [T&&&d],w ≠ 0 ∧ w ≠ d:=by
    intro w hw; rw [List.mem_singleton.1 hw]
    exact ⟨fun e=>hnc (Or.inl e),fun e=>hnc (Or.inr e)⟩
  have hsub : ∀ w ∈ [T&&&d],w ∈ bank.map (nrmD u d):=by
    intro w hw; rw [List.mem_singleton.1 hw]; exact hTmem
  obtain ⟨s,ws,hs,hnd,_,hsub',hrun⟩:=reach_to_run_aux hd hd0 hr (List.nodup_singleton _) hprop hsub Run.done
  have hrmap : roots.map (nrmD u d) = roots.map (·&&&d):=by
    apply List.map_congr_left
    intro r hr_m
    have h0:=List.all_eq_true.1 hR0 r hr_m
    simp only [Bool.not_eq_true'] at h0
    exact nrmD_of_bit0_false u d r h0
  rw [hrmap] at hsub'
  exact ⟨s,ws,by omega,hnd,hsub',hrun⟩
theorem runD_bits {u d y s ws} (hd : d&&&mask256 = d) (h : RunD u d y s ws) (i j:Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws,w.testBit i = w.testBit j) : y.testBit i = y.testBit j:=by
  have hmi : mask256.testBit i = true:=by
    have:=congrArg (fun v=>v.testBit i) hd; simp [Nat.testBit_and,hi] at this; exact this
  have hmj : mask256.testBit j = true:=by
    have:=congrArg (fun v=>v.testBit j) hd; simp [Nat.testBit_and,hj] at this; exact this
  induction h using Run.fold with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | two op ka kb hop _ _ _ _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · rcases allowed_cases hop with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
        simp [opD,andD,orD,negD,ha,hb,hi,hj,hmi,hmj]
    · rw [mem_kept,mem_kept] at hr
      rcases hr with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hr
      · exact ha
      · exact hb
      · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
theorem runD_bits_le_mono {d y s ws} (h : RunD false d y s ws) (i j:Nat)
    (hi : d.testBit i = true) (hj : d.testBit j = true)
    (hw : ∀ w ∈ ws,w.testBit i ≤ w.testBit j) : y.testBit i ≤ y.testBit j:=by
  induction h using Run.fold with
  | done=>exact hw _ (by simp)
  | perm hp _ ih=>exact ih (fun w h=>hw w (hp.mem_iff.1 h))
  | two op ka kb hop _ _ _ _ ih =>
    apply ih; have ha:=hw _ List.mem_cons_self; have hb:=hw _ (List.mem_cons_of_mem _ List.mem_cons_self)
    intro w hm
    rcases List.mem_cons.1 hm with rfl | hr
    · rcases allowed_cases hop with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · simp only [opD,andD,beq_self_eq_true,ite_true,Nat.testBit_and,hi,hj,Bool.and_true]; grind
      · simp only [opD,orD,beq_self_eq_true,ite_true,ite_false,Nat.testBit_and,Nat.testBit_or,hi,hj,Bool.and_true]; grind
      · contradiction
      · contradiction
    · rw [mem_kept,mem_kept] at hr
      rcases hr with ⟨_,rfl⟩ | ⟨_,rfl⟩ | hr
      · exact ha
      · exact hb
      · exact hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
def moveBits (tag d w:Nat):Nat :=
  ((w&&&tag) <<< d)|||((w >>> d)&&&tag) |||
    (w^^^((w&&&tag)|||(w&&&(tag <<< d))))
theorem moved (tag d i w:Nat) (h : (tag&&&(tag <<< d)) = 0) :
    (moveBits tag d w).testBit i =
      (if tag.testBit i then w.testBit (d + i)
       else if (tag <<< d).testBit i then w.testBit (i - d) else w.testBit i):=by
  have ht:=congrArg (fun v:Nat=>v.testBit i) h
  simp only [Nat.testBit_and,Nat.zero_testBit] at ht
  simp only [moveBits,Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_and,
    Nat.testBit_shiftRight,Nat.testBit_xor] at *
  by_cases hi : d ≤ i <;> simp [hi] at * <;> grind
theorem move_hom (tag d:Nat) (h : (tag&&&(tag <<< d)) = 0) (a b:Nat) :
    moveBits tag d (a&&&b) = (moveBits tag d a&&&moveBits tag d b) ∧
    moveBits tag d (a|||b) = (moveBits tag d a|||moveBits tag d b) ∧
    moveBits tag d (a^^^b) = (moveBits tag d a^^^moveBits tag d b):=by
  refine ⟨?_,?_,?_⟩ <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
    simp only [Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,moved tag d i _ h] <;>
    split_ifs <;> simp
theorem move_zero (tag d:Nat) (h : (tag&&&(tag <<< d)) = 0) : moveBits tag d 0 = 0:=by
  apply Nat.eq_of_testBit_eq; intro i; rw [moved tag d i 0 h]; split_ifs <;> simp
def applyMoves (ms:List (Nat × Nat)) (w:Nat):Nat :=
  ms.foldl (fun acc p=>moveBits p.1 p.2 acc) w
def moveOK256 (p:Nat × Nat):Bool :=
  (p.1&&&(p.1 <<< p.2)==0)&&(moveBits p.1 p.2 mask256==mask256)
theorem applyMoves_hom (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    (∀ a b,applyMoves ms (a&&&b) = applyMoves ms a&&&applyMoves ms b) ∧
    (∀ a b,applyMoves ms (a|||b) = applyMoves ms a|||applyMoves ms b) ∧
    (∀ a b,applyMoves ms (a^^^b) = applyMoves ms a^^^applyMoves ms b) ∧
    applyMoves ms 0 = 0 ∧ applyMoves ms mask256 = mask256:=by
  induction ms with
  | nil=>exact ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,rfl,rfl⟩
  | cons p ps ih =>
    simp only [List.all_cons,Bool.and_eq_true,moveOK256,beq_iff_eq] at hok
    obtain ⟨⟨hz,hm⟩,hps⟩:=hok
    obtain ⟨hand,hor,hxor,h0,h256⟩:=ih hps
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).1]; exact hand _ _
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).2.1]; exact hor _ _
    · intro a b; simp only [applyMoves,List.foldl_cons,(move_hom p.1 p.2 hz a b).2.2]; exact hxor _ _
    · simp only [applyMoves,List.foldl_cons,move_zero p.1 p.2 hz]; exact h0
    · simp only [applyMoves,List.foldl_cons,hm]; exact h256
theorem move_invol (tag d w:Nat) (h : (tag&&&(tag <<< d)) = 0) :
    moveBits tag d (moveBits tag d w) = w:=by
  apply Nat.eq_of_testBit_eq; intro i
  have ht:=congrArg (fun v:Nat=>v.testBit i) h
  simp only [Nat.testBit_and,Nat.zero_testBit] at ht
  rw [moved tag d i _ h]
  by_cases h1 : tag.testBit i = true
  · simp only [h1,ite_true,moved tag d (d + i) w h]
    have h2 : tag.testBit (d + i) = false:=by
      have htd:=congrArg (fun v:Nat=>v.testBit (d + i)) h
      simp only [Nat.testBit_and,Nat.testBit_shiftLeft,Nat.zero_testBit] at htd
      have hge : d ≤ d + i:=Nat.le_add_right d i
      have hsub : d + i - d = i:=Nat.add_sub_cancel_left d i
      simp [hge,hsub,h1] at htd; exact htd
    have h3 : (tag <<< d).testBit (d + i) = true:=by
      simp [Nat.testBit_shiftLeft,Nat.le_add_right,Nat.add_sub_cancel_left,h1]
    simp [h2,h3,Nat.add_sub_cancel_left]
  · simp only [h1,ite_false]
    by_cases h2 : (tag <<< d).testBit i = true
    · simp only [h2,ite_true,moved tag d (i - d) w h]
      rw [Nat.testBit_shiftLeft] at h2
      simp only [Bool.and_eq_true,decide_eq_true_eq] at h2
      simp [h2.2,Nat.add_sub_of_le h2.1]
    · simp [h1,h2,moved tag d i w h]
theorem applyMoves_inj (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true) :
    Function.Injective (applyMoves ms):=by
  induction ms with
  | nil=>intro a b h; exact h
  | cons p ps ih =>
    simp only [List.all_cons,Bool.and_eq_true,moveOK256,beq_iff_eq] at hok
    intro a b h
    simp only [applyMoves,List.foldl_cons] at h
    have h1:=ih hok.2 h
    have:=congrArg (moveBits p.1 p.2) h1
    rwa [move_invol p.1 p.2 a hok.1.1,move_invol p.1 p.2 b hok.1.1] at this
theorem applyMoves_opD (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2:Nat} (hd : applyMoves ms d2 = d1) (op a b:Nat) :
    applyMoves ms (opD d2 op a b) = opD d1 op (applyMoves ms a) (applyMoves ms b):=by
  obtain ⟨hand,hor,hxor,_,h256⟩:=applyMoves_hom ms hok
  unfold opD; split_ifs <;> simp only [andD,orD,negD,hand,hor,hxor,h256,hd]
theorem applyMoves_runD {u d Y s} (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd : applyMoves ms d = d) (hY : applyMoves ms Y = Y) {ws} (h : RunD u d Y s ws) :
    RunD u d Y s (ws.map (applyMoves ms)):=by
  obtain ⟨_,_,_,h0,_⟩:=applyMoves_hom ms hok
  have hinj:=applyMoves_inj ms hok
  rw [← hY]
  induction h using Run.fold with
  | done=>exact Run.done
  | perm hp _ ih=>exact Run.perm (hp.map _) ih
  | @two s a b r op ka kb hop hne0 hned hnm _ ih =>
    have eop:=applyMoves_opD ms hok hd op a b
    have e1 : (opD d op a b :: kept ka a (kept kb b r)).map (applyMoves ms) =
        opD d op (applyMoves ms a) (applyMoves ms b) ::
          kept ka (applyMoves ms a) (kept kb (applyMoves ms b) (r.map (applyMoves ms))):=by
      simp [kept_map,eop]
    rw [e1] at ih
    refine Run.two op ka kb hop ?_ ?_ ?_ ih
    · intro e; rw [← eop] at e; exact hne0 (hinj (e.trans h0.symm))
    · intro e; rw [← eop] at e; exact hned (hinj (e.trans hd.symm))
    · rw [← eop,← List.map_cons,← List.map_cons,List.mem_map]; rintro ⟨x,hx,he⟩; exact hnm (hinj he ▸ hx)
theorem reach_map_moves {u:Bool} (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    {d1 d2:Nat} (hd1 : d1&&&mask256 = d1) (hd : applyMoves ms d2 = d1)
    {roots1 roots2:List Nat} (hroots : ∀ r ∈ roots2,Avail u d1 roots1 (applyMoves ms r)) :
    ∀ {p bank},NatReach u d2 roots2 p bank →
      ∃ bank',NatReach u d1 roots1 p bank' ∧ ∀ v ∈ bank,Avail u d1 bank' (applyMoves ms v):=by
  obtain ⟨hand,_,hxor,h0,h256⟩:=applyMoves_hom ms hok
  have hav : ∀ {b b' w},(∀ v ∈ b,Avail u d1 b' (applyMoves ms v)) →
      Avail u d2 b w → Avail u d1 b' (applyMoves ms w):=by
    intro b b' w hbb hw
    rcases hw with (hz | h1) | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
    · exact Or.inl (Or.inl (by rw [← hd,← hand,hz,h0]))
    · exact Or.inl (Or.inr (by rw [← hd,← hand,h1]))
    · have hve : applyMoves ms v&&&d1 = applyMoves ms w&&&d1:=by rw [← hd,← hand,← hand,he]
      exact avail_of_eq hve (hbb v hv)
    · have hve : applyMoves ms v&&&d1 = negD d1 (applyMoves ms w)&&&d1:=by
        rw [← hd,← hand,he]; simp only [negD,hand,hxor,h256,hd,Nat.and_assoc,Nat.and_self]
      have hneg:=avail_neg hd1 (avail_of_eq hve (hbb v hv))
      exact avail_of_eq (by rw [negD_invol hd1,Nat.and_assoc,Nat.and_self]) hneg
  intro p
  induction p with
  | zero =>
    intro bank hr; subst hr
    exact ⟨roots1,rfl,hroots⟩
  | succ p ih =>
    intro bank hr
    obtain ⟨b,a,c,op,hop,rfl,hrb,ha,hc⟩:=hr
    obtain ⟨b',hrb',hbb⟩:=ih hrb
    have ha':=hav hbb ha; have hc':=hav hbb hc
    refine ⟨opD d1 op (applyMoves ms a) (applyMoves ms c) :: b',
      ⟨b',applyMoves ms a,applyMoves ms c,op,hop,rfl,hrb',ha',hc'⟩,?_⟩
    intro v hv; rcases List.mem_cons.1 hv with rfl | hv
    · exact Or.inr (Or.inl ⟨opD d1 op (applyMoves ms a) (applyMoves ms c),List.mem_cons_self,by
        rw [applyMoves_opD ms hok hd]⟩)
    · exact avail_cons _ _ (hbb v hv)
theorem lower_iso {u:Bool} {d1 d2 T1 T2 L:Nat} {roots1 roots2:List Nat}
    (ms:List (Nat × Nat)) (hok : ms.all moveOK256 = true)
    (hd1 : d1&&&mask256 = d1) (hd : applyMoves ms d2 = d1) (hT : applyMoves ms T2 = T1)
    (hroots : roots2.all (fun r=>availB u d1 roots1 (applyMoves ms r)) = true)
    (h1 : Lower u d1 roots1 T1 L) : Lower u d2 roots2 T2 L:=by
  obtain ⟨hand,_,hxor,h0,h256⟩:=applyMoves_hom ms hok
  have hr : ∀ r ∈ roots2,Avail u d1 roots1 (applyMoves ms r):=fun r hr =>
    (availB_iff u _ _ _).1 (List.all_eq_true.1 hroots r hr)
  intro p bank hreach ha
  obtain ⟨bank',hrb',hbb⟩:=reach_map_moves ms hok hd1 hd hr hreach
  apply h1 p bank' hrb'
  rcases ha with (hz | ho) | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact Or.inl (Or.inl (by rw [← hT,← hd,← hand,hz,h0]))
  · exact Or.inl (Or.inr (by rw [← hT,← hd,← hand,ho]))
  · have hve : applyMoves ms v&&&d1 = T1&&&d1:=by rw [← hT,← hd,← hand,← hand,he]
    exact avail_of_eq hve (hbb v hv)
  · have hve : applyMoves ms v&&&d1 = negD d1 T1&&&d1:=by
      rw [← hT,← hd,← hand,he]; simp only [negD,hand,hxor,h256,hd,Nat.and_assoc,Nat.and_self]
    have hneg:=avail_neg hd1 (avail_of_eq hve (hbb v hv))
    exact avail_of_eq (by rw [negD_invol hd1,Nat.and_assoc,Nat.and_self]) hneg
def pairOK (d T:Nat) (p:Nat × Nat):Bool :=
  d.testBit p.1&&d.testBit p.2&&(T.testBit p.1 != T.testBit p.2)
def essOK (d T:Nat) (roots:List Nat) (a:Nat) (p:Nat × Nat):Bool :=
  pairOK d T p&&roots.all (fun v=>(v==a)||(v.testBit p.1==v.testBit p.2))
theorem countP_ge_sublist (p:Nat → Bool) {xs ys:List Nat}
    (hnd : xs.Nodup) (hsub : ∀ a ∈ xs,a ∈ ys) (hall : ∀ a ∈ xs,p a = true) :
    xs.length ≤ ys.countP p:=by
  induction xs generalizing ys with
  | nil=>simp
  | cons a xs ih =>
    have ⟨hna,hnd'⟩:=List.nodup_cons.1 hnd
    have ham : a ∈ ys:=hsub a List.mem_cons_self
    have hperm : ys.Perm (a :: ys.erase a):=List.perm_cons_erase ham
    rw [hperm.countP_eq,List.countP_cons,hall a List.mem_cons_self]
    have ih':=ih hnd' (fun x hx=>by
      have hne : x ≠ a:=fun e=>hna (e ▸ hx)
      exact (List.mem_erase_of_ne hne).2 (hsub x (List.mem_cons_of_mem _ hx)))
      (fun x hx=>hall x (List.mem_cons_of_mem _ hx))
    simp only [ite_true,List.length_cons]
    omega
theorem lower_slice {u:Bool} {d dSub T TSub L:Nat} {roots rootsSub:List Nat}
    (hd : d&&&mask256 = d) (hd0 : d.testBit 0 = true)
    (hT0 : T.testBit 0 = false) (hR0 : roots.all (fun r=>!r.testBit 0) = true)
    (hdSub : dSub&&&mask256 = dSub) (hsub : dSub&&&d = dSub)
    (hT : T&&&dSub = TSub&&&dSub)
    (hnc : isConstB d T = false) (hncSub : isConstB dSub TSub = false)
    (hcov : roots.all (availB u dSub rootsSub) = true)
    (singles:List (Nat × Nat × Nat))
    (hs_nd : (singles.map Prod.fst).Nodup)
    (hs_ok : singles.all (fun e=>isConstB dSub e.1&&essOK d (T&&&d) (roots.map (·&&&d)) e.1 e.2) = true)
    (hprior : Lower u dSub rootsSub TSub L) :
    Lower u d roots T (L + singles.length):=by
  have hnc' : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hnc; contradiction
  have hncSub' : ¬ IsConst dSub (T&&&d):=by
    intro h
    have e : (T&&&d)&&&dSub = TSub&&&dSub:=by
      rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  intro p bank hr ha
  obtain ⟨s,ws,hs_le,hnd,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc' hr ha
  have hws_av : ∀ w ∈ ws,Avail u dSub rootsSub w:=by
    intro w hw
    obtain ⟨r,hr_m,rfl⟩:=List.mem_map.1 (hws_sub w hw)
    have hav:=(availB_iff u _ _ _).1 (List.all_eq_true.1 hcov r hr_m)
    exact avail_of_eq (by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub]) hav
  obtain ⟨q,next,hq,ht,hle⟩:=contraction hdSub hsub hncSub' hrun (p:=0) (bank:=rootsSub) rfl hws_av
  have hTSub_av : Avail u dSub next TSub:=avail_of_eq (by
    rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]) ht
  have hL : L ≤ q:=hprior q next hq hTSub_av
  have hsin_mem : ∀ a ∈ singles.map Prod.fst,a ∈ ws:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok (a',r1,r2) hm
    simp only [Bool.and_eq_true,essOK,pairOK,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at hok
    obtain ⟨_,⟨⟨hr1,hr2⟩,hdiff⟩,hiso⟩:=hok
    by_contra hnot
    apply hdiff
    apply runD_bits hd hrun r1 r2 hr1 hr2
    intro w hw
    rcases hiso w (hws_sub w hw) with rfl | heq
    · exact absurd hw hnot
    · exact heq
  have hsin_const : ∀ a ∈ singles.map Prod.fst,isConstB dSub a = true:=by
    intro a ha
    obtain ⟨⟨a',r1,r2⟩,hm,rfl⟩:=List.mem_map.1 ha
    have hok:=List.all_eq_true.1 hs_ok _ hm
    simp only [Bool.and_eq_true] at hok
    exact hok.1
  have hcnt:=countP_ge_sublist (isConstB dSub) hs_nd hsin_mem hsin_const
  simp only [List.length_map] at hcnt
  omega
def stepOp (u:Bool) (d:Nat) (st:Nat × List Nat) (g:Nat × Nat × Nat):Nat × List Nat :=
  if allowedB u g.1 then
    let om:=opD d g.1 g.2.1 g.2.2
    if availB u d st.2 om then st
    else if availB u d st.2 g.2.1&&availB u d st.2 g.2.2 then (st.1 + 1,om :: st.2)
    else st
  else st
def runOps (u:Bool) (d:Nat) (st:Nat × List Nat) (ops:List (Nat × Nat × Nat)):Nat × List Nat :=
  ops.foldl (stepOp u d) st
theorem avail_of_availB_pool {u:Bool} {d:Nat} (hd : d&&&mask256 = d)
    {bank pool:List Nat} (hsup : ∀ v ∈ pool,Avail u d bank v) {w:Nat}
    (hb : availB u d pool w = true) : Avail u d bank w:=by
  rcases (availB_iff u d pool w).1 hb with hc | ⟨v,hv,he⟩ | ⟨rfl,v,hv,he⟩
  · exact Or.inl hc
  · exact avail_of_eq he (hsup v hv)
  · have hneg:=avail_neg hd (hsup v hv)
    have he' : negD d v&&&d = w&&&d:=by
      rw [← negD_mask,he,negD_invol hd,Nat.and_assoc,Nat.and_self]
    exact avail_of_eq he' hneg
theorem stepOp_sound {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {roots bank:List Nat}
    (st:Nat × List Nat) (g:Nat × Nat × Nat)
    (hr:NatReach u d roots st.1 bank) (hsup : ∀ v ∈ st.2,Avail u d bank v) :
    ∃ bank',NatReach u d roots (stepOp u d st g).1 bank' ∧ ∀ v ∈ (stepOp u d st g).2,Avail u d bank' v:=by
  unfold stepOp; dsimp only
  split
  · rename_i hop
    split
    · exact ⟨bank,hr,hsup⟩
    · split
      · rename_i hab
        simp only [Bool.and_eq_true] at hab
        have ha:=avail_of_availB_pool hd hsup hab.1
        have hb:=avail_of_availB_pool hd hsup hab.2
        refine ⟨opD d g.1 g.2.1 g.2.2 :: bank,⟨bank,g.2.1,g.2.2,g.1,hop,rfl,hr,ha,hb⟩,?_⟩
        intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact Or.inr (Or.inl ⟨_,List.mem_cons_self,rfl⟩)
        · exact avail_cons _ _ (hsup v hv)
      · exact ⟨bank,hr,hsup⟩
  · exact ⟨bank,hr,hsup⟩
theorem runOps_sound {u:Bool} {d:Nat} (hd : d&&&mask256 = d) {roots:List Nat}
    (ops:List (Nat × Nat × Nat)) :
    ∀ (st:Nat × List Nat) (bank:List Nat),
      NatReach u d roots st.1 bank → (∀ v ∈ st.2,Avail u d bank v) →
      ∃ bank',NatReach u d roots (runOps u d st ops).1 bank' ∧ ∀ v ∈ (runOps u d st ops).2,Avail u d bank' v:=by
  induction ops with
  | nil=>intro st bank hr hsup; exact ⟨bank,hr,hsup⟩
  | cons g ops ih =>
    intro st bank hr hsup
    obtain ⟨bank1,hr1,hsup1⟩:=stepOp_sound hd st g hr hsup
    exact ih (stepOp u d st g) bank1 hr1 hsup1
def checkPool (u:Bool) (dSub LSub s:Nat) (st:Nat × List Nat) (ws:List Nat):Bool :=
  decide (s + st.1 < LSub + ws.countP (isConstB dSub))&&ws.all (availB u dSub st.2)
theorem checkPool_sound {u:Bool} {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hdSub : dSub&&&mask256 = dSub) (hsub : dSub&&&d = dSub)
    (hT : T&&&dSub = TSub&&&dSub) (hncSub : isConstB dSub TSub = false)
    (hprior : Lower u dSub rootsSub TSub LSub)
    (st:Nat × List Nat) (bank:List Nat)
    (hrb:NatReach u dSub rootsSub st.1 bank) (hsb : ∀ v ∈ st.2,Avail u dSub bank v)
    (hchk : checkPool u dSub LSub s st ws = true) :
    ¬ RunD u d (T&&&d) s ws:=by
  intro hrun
  simp only [checkPool,Bool.and_eq_true,decide_eq_true_eq] at hchk
  obtain ⟨hineq,hall⟩:=hchk
  have hws_av : ∀ w ∈ ws,Avail u dSub bank w:=fun w hw =>
    avail_of_availB_pool hdSub hsb (List.all_eq_true.1 hall w hw)
  have hnc' : ¬ IsConst dSub (T&&&d):=by
    intro h; have e : (T&&&d)&&&dSub = TSub&&&dSub:=by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]
    rcases h with h0 | h1
    · exact absurd ((isConstB_iff _ _).2 (Or.inl (e.symm.trans h0))) (by simp [hncSub])
    · exact absurd ((isConstB_iff _ _).2 (Or.inr (e.symm.trans h1))) (by simp [hncSub])
  obtain ⟨q,next,hq,ht,hle⟩:=contraction hdSub hsub hnc' hrun hrb hws_av
  have hL:=hprior q next hq (avail_of_eq (by rw [Nat.and_assoc,Nat.and_comm d dSub,hsub,hT]) ht)
  omega
def subValidB (d dSub T TSub:Nat):Bool :=
  (dSub&&&mask256==dSub)&&(dSub&&&d==dSub)&&(T&&&dSub==TSub&&&dSub)&&!(isConstB dSub TSub)
theorem cpcs {u:Bool} {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hv : subValidB d dSub T TSub = true)
    (hprior : Lower u dSub rootsSub TSub LSub)
    (ops:List (Nat × Nat × Nat)) (g:Nat × Nat × Nat)
    (hchk : checkPool u dSub LSub s (stepOp u dSub (runOps u dSub (0,rootsSub) ops) g) ws = true) :
    ¬ RunD u d (T&&&d) s ws:=by
  simp only [subValidB,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hv
  have hsup0 : ∀ v ∈ rootsSub,Avail u dSub rootsSub v:=fun v hv=>Or.inr (Or.inl ⟨v,hv,rfl⟩)
  obtain ⟨bank1,hr1,hsup1⟩:=runOps_sound hv.1.1.1 ops (0,rootsSub) rootsSub rfl hsup0
  obtain ⟨bank2,hr2,hsup2⟩:=stepOp_sound hv.1.1.1 _ g hr1 hsup1
  exact checkPool_sound hv.1.1.1 hv.1.1.2 hv.1.2 hv.2 hprior _ bank2 hr2 hsup2 hchk
theorem checkRootSub_sound {u:Bool} {d dSub T TSub LSub s:Nat} {rootsSub ws:List Nat}
    (hv : subValidB d dSub T TSub = true)
    (hprior : Lower u dSub rootsSub TSub LSub)
    (hchk : checkPool u dSub LSub s (0,rootsSub) ws = true) :
    ¬ RunD u d (T&&&d) s ws:=by
  simp only [subValidB,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at hv
  exact checkPool_sound hv.1.1.1 hv.1.1.2 hv.1.2 hv.2 hprior (0,rootsSub) rootsSub rfl (fun v hv=>Or.inr (Or.inl ⟨v,hv,rfl⟩)) hchk
def coversP (u:Bool) (pairs:List (Nat × Nat)) (ws:List Nat):Bool :=
  if !u then
    pairs.all (fun p=>ws.any (fun w=>!w.testBit p.1&&w.testBit p.2))
  else
    pairs.all (fun p=>ws.any (fun w=>w.testBit p.1 != w.testBit p.2))
theorem coversP_ok {u:Bool} {d T s:Nat} (hd : d&&&mask256 = d)
    (pairs:List (Nat × Nat))
    (hpairs : pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&!(T&&&d).testBit p.1&&(T&&&d).testBit p.2) = true)
    {ws:List Nat} (h : RunD u d (T&&&d) s ws) : coversP u pairs ws = true:=by
  cases u with
  | false =>
    simp only [coversP,Bool.not_false,ite_true,List.all_eq_true,List.any_eq_true]
    intro ⟨u1,v1⟩ hm
    have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
    by_contra! hall
    have hle:=runD_bits_le_mono h v1 u1 hp.1.1.2 hp.1.1.1 (fun w hw=>by
      have hbad:=hall w hw
      cases hu : w.testBit u1 <;> cases hv : w.testBit v1 <;> simp_all)
    rw [hp.1.2,hp.2] at hle; contradiction
  | true =>
    simp only [coversP,Bool.not_true,Bool.false_eq_true,ite_false,List.all_eq_true,List.any_eq_true,bne_iff_ne]
    intro ⟨u1,v1⟩ hm
    have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
    simp only [Bool.and_eq_true,Bool.not_eq_true'] at hp
    by_contra! hall
    have heq:=runD_bits hd h u1 v1 hp.1.1.1 hp.1.1.2 hall
    rw [hp.1.2,hp.2] at heq; contradiction
def unorientedCov (pairs:List (Nat × Nat)) (ws:List Nat):Bool :=
  pairs.all (fun p=>ws.any (fun w=>w.testBit p.1 != w.testBit p.2))
theorem unorientedCov_ok {u:Bool} {d T s:Nat} (hd : d&&&mask256 = d)
    (pairs:List (Nat × Nat))
    (hpairs : pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&((T&&&d).testBit p.1 != (T&&&d).testBit p.2)) = true)
    {ws:List Nat} (h : RunD u d (T&&&d) s ws) : unorientedCov pairs ws = true:=by
  simp only [unorientedCov,List.all_eq_true,List.any_eq_true,bne_iff_ne]
  intro ⟨u1,v1⟩ hm
  have hp:=List.all_eq_true.1 hpairs (u1,v1) hm
  simp only [Bool.and_eq_true,bne_iff_ne] at hp
  by_contra! hall
  have heq:=runD_bits hd h u1 v1 hp.1.1 hp.1.2 hall
  exact hp.2 heq
def maskP (m:Nat):Nat:=2 ^ m - 1
def projBit (rs:List Nat) (w:Nat):Nat :=
  rs.foldr (fun r acc=>(acc <<< 1)|||(if w.testBit r then 1 else 0)) 0
theorem projBit_testBit (rs:List Nat) (w:Nat) (i:Nat) :
    (projBit rs w).testBit i = if h : i < rs.length then w.testBit rs[i] else false:=by
  induction rs generalizing i with
  | nil=>simp [projBit]
  | cons r rs ih =>
    cases i with
    | zero =>
      simp only [projBit,List.foldr_cons,Nat.testBit_or,Nat.testBit_shiftLeft,
        Nat.not_le.2 Nat.zero_lt_one,decide_false,Bool.false_and,Bool.false_or,
        List.length_cons,Nat.zero_lt_succ,dite_true,List.getElem_cons_zero]
      cases w.testBit r <;> simp
    | succ i =>
      simp only [projBit,List.foldr_cons,Nat.testBit_or,Nat.testBit_shiftLeft,
        Nat.succ_le_succ (Nat.zero_le i),decide_true,Bool.true_and,Nat.add_sub_cancel,
        List.length_cons,Nat.succ_lt_succ_iff,List.getElem_cons_succ]
      have h1 : (if w.testBit r = true then 1 else 0).testBit (i + 1) = false:=by
        cases w.testBit r <;> simp [Nat.testBit_succ]
      rw [h1,Bool.or_false]; exact ih i
def opP (mp op:Nat) (pa pb:Nat):Nat :=
  if op==0 then pa&&&pb
  else if op==1 then pa|||pb
  else if op==2 then pa&&&(pb^^^mp)
  else (pa^^^mp)&&&pb
theorem projBit_opD {dm:Nat} (hd : dm&&&mask256 = dm) {rs:List Nat}
    (hrs : ∀ r ∈ rs,dm.testBit r = true) (op a b:Nat) :
    projBit rs (opD dm op a b) = opP (maskP rs.length) op (projBit rs a) (projBit rs b):=by
  apply Nat.eq_of_testBit_eq; intro i
  by_cases hi : i < rs.length
  · have hdr:=hrs rs[i] (List.getElem_mem hi)
    have hmr : mask256.testBit rs[i] = true:=by
      have:=congrArg (fun v=>v.testBit rs[i]) hd; simp [Nat.testBit_and,hdr] at this; exact this
    unfold opD opP
    split_ifs <;>
      simp only [projBit_testBit,hi,dite_true,andD,orD,negD,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,
        maskP,Nat.testBit_two_pow_sub_one,decide_true,hdr,hmr,Bool.and_true,Bool.xor_true] <;>
      (cases a.testBit rs[i] <;> cases b.testBit rs[i] <;> rfl)
  · unfold opD opP
    split_ifs <;>
      simp only [projBit_testBit,hi,dite_false,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,
        maskP,Nat.testBit_two_pow_sub_one,decide_false,Bool.false_and,Bool.and_false,Bool.false_or,Bool.xor_false]
theorem foldl_or_testBit {α : Type} (g : α → Nat) (xs:List α) (acc i:Nat) :
    (xs.foldl (fun a x=>a|||g x) acc).testBit i = (acc.testBit i||xs.any (fun x=>(g x).testBit i)):=by
  induction xs generalizing acc with
  | nil=>simp
  | cons x xs ih =>
    simp only [List.foldl_cons,ih,Nat.testBit_or,List.any_cons,Bool.or_assoc]
def colB (mp:Nat) (oriented:Bool) (p:Nat × Nat):Nat :=
  if oriented then (p.1^^^mp)&&&p.2 else p.1^^^p.2
def coversD (u:Bool) (mp:Nat) (dws:List (Nat × Nat × Nat)):Bool :=
  dws.foldl (fun acc d=>acc|||colB mp (!u) d.2) 0==mp
theorem coversD_eq (u:Bool) (pairs:List (Nat × Nat)) (ws:List Nat) :
    coversD u (maskP pairs.length) (ws.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))) =
      coversP u pairs ws:=by
  set r1s:=pairs.map Prod.fst
  set r2s:=pairs.map Prod.snd
  set mp:=maskP pairs.length
  have hr1 : r1s.length = pairs.length:=List.length_map _
  have hr2 : r2s.length = pairs.length:=List.length_map _
  unfold coversD coversP
  cases u with
  | false =>
    simp only [Bool.not_false,colB,ite_true]
    apply Bool.eq_iff_iff.2; rw [beq_iff_eq,List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.1 hpr
      have hb:=congrArg (fun v=>v.testBit i) heq
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map] at hb
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one,hi,decide_true] at hb
      obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 hb
      simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,
        Nat.testBit_two_pow_sub_one,decide_true,Bool.xor_true] at hwt
      exact List.any_eq_true.2 ⟨w,hw,by simpa [r1s,r2s] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map]
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi,decide_true]
        obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w,hw,by
          simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,
            Nat.testBit_two_pow_sub_one,decide_true,Bool.xor_true,r1s,r2s,List.getElem_map]
          exact hwt⟩
      · simp only [hi,decide_false,List.any_eq_false]
        intro w _
        simp only [Function.comp_def,Nat.testBit_and,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_false,
          Nat.testBit_two_pow_sub_one,decide_false,Bool.xor_false,Bool.and_false,not_false_eq_true,Bool.false_eq_true]
  | true =>
    simp only [Bool.not_true,colB,Bool.false_eq_true,ite_false]
    apply Bool.eq_iff_iff.2; rw [beq_iff_eq,List.all_eq_true]
    constructor
    · intro heq pr hpr
      obtain ⟨i,hi,rfl⟩:=List.mem_iff_getElem.1 hpr
      have hb:=congrArg (fun v=>v.testBit i) heq
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map] at hb
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one,hi,decide_true] at hb
      obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 hb
      simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true] at hwt
      exact List.any_eq_true.2 ⟨w,hw,by simpa [r1s,r2s,bne] using hwt⟩
    · intro hall
      apply Nat.eq_of_testBit_eq; intro i
      rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,List.any_map]
      simp only [mp,maskP,Nat.testBit_two_pow_sub_one]
      by_cases hi : i < pairs.length
      · simp only [hi,decide_true]
        obtain ⟨w,hw,hwt⟩:=List.any_eq_true.1 (hall pairs[i] (List.getElem_mem hi))
        exact List.any_eq_true.2 ⟨w,hw,by
          simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_true,r1s,r2s,List.getElem_map]
          simpa [bne] using hwt⟩
      · simp only [hi,decide_false,List.any_eq_false]
        intro w _
        simp only [Function.comp_def,Nat.testBit_xor,projBit_testBit,hr1,hr2,hi,dite_false,
          Bool.xor_false,Bool.false_eq_true,not_false_eq_true]
theorem erase_map_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (f : α → β) (hinj : Function.Injective f) (xs:List α) (a : α) :
    (xs.map f).erase (f a) = (xs.erase a).map f:=by
  induction xs with
  | nil=>rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.erase_cons]
    by_cases h : x = a
    · subst h; simp
    · have hf : (f x==f a) = false:=beq_false_of_ne (fun e=>h (hinj e))
      have hx : (x==a) = false:=beq_false_of_ne h
      simp [hf,hx,ih]
def value6 (a b c d e f:Bool):Nat :=
  let x:=b.toNat + c.toNat
  let y:=(!e).toNat + (!f).toNat
  if a then (if d then y else max x (max y (x + y - 1))) else (if d then 0 else x)
theorem value6_and : ∀ a b c d e f g h i j l m:Bool,
    value6 (a&&g) (b&&h) (c&&i) (d&&j) (e&&l) (f&&m)
      ≤ value6 a b c d e f + value6 g h i j l m:=by decide +kernel
theorem value6_or : ∀ a b c d e f g h i j l m:Bool,
    value6 (a||g) (b||h) (c||i) (d||j) (e||l) (f||m)
      ≤ value6 a b c d e f + value6 g h i j l m:=by decide +kernel
theorem score_bound {d y s ws} (h : RunD false d y s ws) (hl : ws.length = s + 1)
    (v:Nat → Nat) (hand : ∀ a b,v (andD d a b) ≤ v a + v b)
    (hor : ∀ a b,v (orD d a b) ≤ v a + v b) : v y ≤ (ws.map v).sum:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>rw [← (p.map v).sum_eq]; exact ih (p.length_eq.trans hl)
  | two op ka kb hop _ _ _ h ih =>
    have hh:=run_len h; cases ka <;> cases kb <;> simp [kept] at hh hl <;> try omega
    have ih':=ih (by simp [kept]; omega)
    rcases allowed_cases hop with rfl | rfl | ⟨hc,_⟩ | ⟨hc,_⟩
    · simp only [opD,beq_self_eq_true,ite_true,kept,Bool.false_eq_true,ite_false,List.map_cons,List.sum_cons] at ih' ⊢
      grw [← Nat.add_assoc,← hand]; exact ih'
    · simp only [opD,beq_self_eq_true,ite_true,ite_false,kept,Bool.false_eq_true,List.map_cons,List.sum_cons] at ih' ⊢
      grw [← Nat.add_assoc,← hor]; exact ih'
    · contradiction
    · contradiction
def eval6 (a b c d e f v:Nat):=value6 (v.testBit a) (v.testBit b) (v.testBit c)
    (v.testBit d) (v.testBit e) (v.testBit f)
theorem eval6_bound {dm y s ws} (h : RunD false dm y s ws) (hl : ws.length = s + 1)
    (a b c d e f:Nat)
    (ha : dm.testBit a = true) (hb : dm.testBit b = true) (hc : dm.testBit c = true)
    (hd : dm.testBit d = true) (he : dm.testBit e = true) (hf : dm.testBit f = true) :
    eval6 a b c d e f y ≤ (ws.map (eval6 a b c d e f)).sum:=by
  apply score_bound h hl
  · intro v w
    simpa only [eval6,andD,Nat.testBit_and,ha,hb,hc,hd,he,hf,Bool.and_true] using value6_and
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
  · intro v w
    simpa only [eval6,orD,Nat.testBit_and,Nat.testBit_or,ha,hb,hc,hd,he,hf,Bool.and_true] using value6_or
      (v.testBit a) (v.testBit b) (v.testBit c) (v.testBit d) (v.testBit e) (v.testBit f)
      (w.testBit a) (w.testBit b) (w.testBit c) (w.testBit d) (w.testBit e) (w.testBit f)
def sumBelow (v:Nat → Nat):List Nat → Nat → Bool
  | [],n=>n != 0
  | w :: ws,n=>decide (v w < n)&&sumBelow v ws (n - v w)
theorem sumBelow_iff (v:Nat → Nat) (ws:List Nat) (n:Nat) :
    sumBelow v ws n = true ↔ (ws.map v).sum < n:=by
  induction ws generalizing n with
  | nil=>simp [sumBelow]
  | cons w ws ih=>rw [sumBelow,Bool.and_eq_true,decide_eq_true_eq,ih,List.map_cons,List.sum_cons]; omega
def scoreCheck (dm y s:Nat) (ws:List Nat) (code:Nat):Bool :=
  let a:=code&&&255
  let b:=(code >>> 8)&&&255
  let c:=(code >>> 16)&&&255
  let d:=(code >>> 24)&&&255
  let e:=(code >>> 32)&&&255
  let f:=(code >>> 40)&&&255
  dm.testBit a&&dm.testBit b&&dm.testBit c&&dm.testBit d&&dm.testBit e&&dm.testBit f &&
    ws.length==s + 1&&sumBelow (eval6 a b c d e f) ws (eval6 a b c d e f y)
theorem scoreCheck_no {dm y s ws} (h : RunD false dm y s ws) (code:Nat) :
    scoreCheck dm y s ws code = false:=by
  unfold scoreCheck
  by_cases hok : dm.testBit (code&&&255) = true ∧ dm.testBit ((code >>> 8)&&&255) = true ∧
      dm.testBit ((code >>> 16)&&&255) = true ∧ dm.testBit ((code >>> 24)&&&255) = true ∧
      dm.testBit ((code >>> 32)&&&255) = true ∧ dm.testBit ((code >>> 40)&&&255) = true ∧
      ws.length = s + 1
  · obtain ⟨ha,hb,hc,hd,he,hf,hl⟩:=hok
    simp only [ha,hb,hc,hd,he,hf,hl,beq_self_eq_true,Bool.true_and]
    by_contra hbad
    have hsum:=(sumBelow_iff _ _ _).1 (Bool.eq_true_of_not_eq_false hbad)
    exact (Nat.not_lt_of_ge (eval6_bound h hl _ _ _ _ _ _ ha hb hc hd he hf)) hsum
  · by_contra hbad
    have ht:=Bool.eq_true_of_not_eq_false hbad
    simp only [Bool.and_eq_true,beq_iff_eq] at ht
    exact hok ⟨ht.1.1.1.1.1.1.1,ht.1.1.1.1.1.1.2,ht.1.1.1.1.1.2,ht.1.1.1.1.2,ht.1.1.1.2,ht.1.1.2,ht.1.2⟩
def scr (u:Bool) (dm y s:Nat) (pool:List Nat) (zs:List Nat):Bool :=
  !u&&zs.length==s + 1&&pool.any (scoreCheck dm y s zs)
theorem scr_no {u:Bool} {dm y s:Nat} (pool:List Nat) {zs:List Nat}
    (h : RunD u dm y s zs) : scr u dm y s pool zs = false:=by
  cases u with
  | true=>simp [scr]
  | false =>
    unfold scr; simp only [Bool.not_false,Bool.true_and]
    rw [Bool.and_eq_false_iff]; right; rw [List.any_eq_false]
    intro x _; rw [scoreCheck_no h x]; simp
def opsOf (u:Bool):List Nat:=if u then [0,1,2,3] else [0,1]
theorem mem_opsOf {u:Bool} {op:Nat} (hop : allowedB u op = true) : op ∈ opsOf u:=by
  rcases allowed_cases hop with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> decide
  · cases u <;> decide
  · decide
  · decide
def nextD (u:Bool) (dm:Nat) (slack:Nat) (ws:List Nat) (f : (Nat × Nat × Nat) → List Nat → Bool):Bool :=
  ws.any fun a =>
    let ra:=ws.erase a
    ra.any fun b =>
      a ≤ b&&(let r:=ra.erase b
        (opsOf u).any fun op =>
          let w:=opD dm op a b
          let g:=(op,a,b)
          w != 0&&w != dm&&!(ws.contains w) &&
            (f g (w :: r)||(slack ≥ 1&&(f g (w :: a :: r)||f g (w :: b :: r))) ||
              (slack ≥ 2&&f g (w :: a :: b :: r))))
theorem nextD_two_sorted {u:Bool} {dm y a b rest} {op:Nat} {ka kb:Bool} {s ws}
    (hop : allowedB u op = true) (hab : a ≤ b)
    (p : (a :: b :: rest).Perm ws)
    (h0 : opD dm op a b ≠ 0) (hd : opD dm op a b ≠ dm) (hnm : opD dm op a b ∉ (a :: b :: rest))
    (h : RunD u dm y s (opD dm op a b :: kept ka a (kept kb b rest)))
    (f : (Nat × Nat × Nat) → List Nat → Bool) (hf : ∀ g ys,RunD u dm y s ys → f g ys = true) :
    nextD u dm (s + 2 - ws.length) ws f = true:=by
  have ha:=p.mem_iff.1 List.mem_cons_self
  have pp:=(p.trans (List.perm_cons_erase ha)).cons_inv
  have hb:=pp.mem_iff.1 List.mem_cons_self
  have pr:=(pp.trans (List.perm_cons_erase hb)).cons_inv
  have hh:=run_len h; have hl:=p.length_eq; simp only [List.length_cons] at hl hh
  have hnc : ws.contains (opD dm op a b) = false:=by
    cases h : ws.contains (opD dm op a b) with
    | false=>rfl
    | true=>exact absurd (p.mem_iff.2 (by simpa using h)) hnm
  have h0b : (opD dm op a b != 0) = true:=bne_iff_ne.2 h0
  have hdb : (opD dm op a b != dm) = true:=bne_iff_ne.2 hd
  apply List.any_eq_true.2 ⟨a,ha,?_⟩
  apply List.any_eq_true.2 ⟨b,hb,?_⟩
  rw [Bool.and_eq_true]; refine ⟨decide_eq_true hab,?_⟩
  apply List.any_eq_true.2 ⟨op,mem_opsOf hop,?_⟩
  simp only [h0b,hdb,hnc,Bool.not_false,Bool.true_and]
  have ht:=hf (op,a,b) _ (Run.perm ((keep_perm (keep_perm pr kb b) ka a).cons _) h)
  cases ka <;> cases kb <;> simp [kept] at ht hh <;>
    simp only [ht,Bool.true_or,Bool.or_true,Bool.and_true] <;>
    first | (simp [show 2 ≤ s + 2 - ws.length by omega]) | (simp [show 1 ≤ s + 2 - ws.length by omega])
theorem nextD_two {u:Bool} {dm y a b rest} {op:Nat} {ka kb:Bool} {s ws}
    (hop : allowedB u op = true) (p : (a :: b :: rest).Perm ws)
    (h0 : opD dm op a b ≠ 0) (hd : opD dm op a b ≠ dm) (hnm : opD dm op a b ∉ (a :: b :: rest))
    (h : RunD u dm y s (opD dm op a b :: kept ka a (kept kb b rest)))
    (f : (Nat × Nat × Nat) → List Nat → Bool) (hf : ∀ g ys,RunD u dm y s ys → f g ys = true) :
    nextD u dm (s + 2 - ws.length) ws f = true:=by
  rcases le_total a b with hab | hba
  · exact nextD_two_sorted hop hab p h0 hd hnm h f hf
  · have he : opD dm op a b = opD dm (flipOp op) b a:=opD_comm dm hop a b
    have hnm' : opD dm (flipOp op) b a ∉ (b :: a :: rest):=by
      rw [← he]; intro hm; exact hnm ((List.Perm.swap _ _ _).mem_iff.1 hm)
    apply nextD_two_sorted (op:=flipOp op) (ka:=kb) (kb:=ka) (flipOp_allowed hop) hba
      ((List.Perm.swap _ _ _).trans p) (he ▸ h0) (he ▸ hd) hnm' _ f hf
    rw [he] at h; apply Run.perm (List.Perm.cons _ ?_) h
    cases ka <;> cases kb <;> simp [kept]; exact List.Perm.swap _ _ _
theorem nextD_complete {u:Bool} {dm y t ws} (h : RunD u dm y t ws) :
    ∀ s,t = s + 1 → ∀ zs,ws.Perm zs → ∀ f : (Nat × Nat × Nat) → List Nat → Bool,
      (∀ g ys,RunD u dm y s ys → f g ys = true) →
      nextD u dm (s + 2 - zs.length) zs f = true:=by
  induction h using Run.fold with
  | done=>simp
  | perm p _ ih=>intro s he zs q; exact ih s he zs (p.trans q)
  | two op ka kb hop h0 hd hnm h _=>intro s he zs p f hf; cases he; exact nextD_two hop p h0 hd hnm h f hf
def span (f:Nat → Bool):Nat → Nat → Bool
  | 0,_=>true
  | n + 1,i=>f i&&span f n (i + 1)
theorem span_ok {f n o} (h : span f n o = true) : ∀ i,o ≤ i → i < o + n → f i = true:=by
  induction n generalizing o with
  | zero=>omega
  | succ n ih =>
    simp only [span,Bool.and_eq_true] at h; intro i hi hj
    rcases Nat.eq_or_lt_of_le hi with rfl | hi
    · exact h.1
    · exact ih h.2 i (by omega) (by omega)
theorem range_split {P:Nat → Prop} {lo mid hi:Nat}
    (h1 : ∀ i,lo ≤ i → i < mid → P i) (h2 : ∀ i,mid ≤ i → i < hi → P i) :
    ∀ i,lo ≤ i → i < hi → P i:=fun i hlo hhi =>
  if h : i < mid then h1 i hlo h else h2 i (Nat.le_of_not_lt h) hhi
def fld (T w i:Nat):Nat :=
  (T >>> (w * i))&&&(if w==32 then 4294967295 else if w==52 then 4503599627370495 else if w==256 then mask256 else 2 ^ w - 1)
def bsr (read:Nat → Nat) (h:Nat):Nat → Nat → Nat → Nat
  | 0,lo,_=>lo
  | f + 1,lo,hi =>
    if lo + 1 < hi then
      (if read ((lo + hi) / 2) ≤ h then bsr read h f ((lo + hi) / 2) hi
       else bsr read h f lo ((lo + hi) / 2))
    else lo
def hw256 (seed w:Nat):Nat :=
  let x:=(((w&&&4294967295)^^^seed) * 2654435761 +
            (((w >>> 32)&&&4294967295)^^^seed) * 2246822519 +
            (((w >>> 64)&&&4294967295)^^^seed) * 3266489917 +
            (((w >>> 96)&&&4294967295)^^^seed) * 668265263 +
            (((w >>> 128)&&&4294967295)^^^seed) * 374761393 +
            (((w >>> 160)&&&4294967295)^^^seed) * 1274126177 +
            (((w >>> 192)&&&4294967295)^^^seed) * 2869860233 +
            (((w >>> 224)&&&4294967295)^^^seed) * 1640531527)&&&4294967295
  let y:=((x^^^(x >>> 16)) * 2246822519)&&&4294967295
  ((y^^^(y >>> 13)) * 3266489917)&&&4294967295
def hz (seed:Nat):List Nat → Nat
  | []=>0
  | w :: t=>hw256 seed w + hz seed t
def hk (seed:Nat) (zs:List Nat):Nat:=hz seed zs&&&1048575
def found (S:Nat → Nat → List Nat) (N:Nat → Nat) (idx:Nat → List Nat → Nat)
    (s:Nat) (zs:List Nat):Bool :=
  decide (idx s zs < N s)&&zs.isPerm (S s (idx s zs))
def foundH (S:Nat → Nat → List Nat) (N:Nat → Nat) (htAt:Nat → Nat → Nat)
    (idxH:Nat → Nat → Nat) (s h:Nat) (zs:List Nat):Bool :=
  let i:=idxH s h
  decide (i < N s)&&(htAt s i==h)&&zs.isPerm (S s i)
def nextD_decor (u:Bool) (dm mp:Nat) (slack:Nat) (dws:List (Nat × Nat × Nat))
    (f : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool):Bool :=
  dws.any fun da =>
    let a:=da.1
    let ra:=dws.erase da
    ra.any fun db =>
      let b:=db.1
      a ≤ b&&(let r:=ra.erase db
        (opsOf u).any fun op =>
          let w:=opD dm op a b
          let g:=(op,a,b)
          w != 0&&w != dm&&!(dws.any (fun x=>x.1==w)) &&
            let dw:=(w,opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
            (f g (dw :: r)||(slack ≥ 1&&(f g (dw :: da :: r)||f g (dw :: db :: r))) ||
              (slack ≥ 2&&f g (dw :: da :: db :: r))))
theorem nextD_decor_gen (u:Bool) (dm mp:Nat) (dec:Nat → Nat × Nat × Nat)
    (hfst : ∀ w,(dec w).1 = w)
    (hop : ∀ op a b,(opD dm op a b,opP mp op (dec a).2.1 (dec b).2.1,opP mp op (dec a).2.2 (dec b).2.2) = dec (opD dm op a b))
    (slack:Nat) (ws:List Nat) (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    nextD_decor u dm mp slack (ws.map dec) g = nextD u dm slack ws (fun opab zs=>g opab (zs.map dec)):=by
  have hinj : Function.Injective dec:=fun x y h=>by rw [← hfst x,← hfst y,h]
  have herase : ∀ (l:List Nat) x,(l.map dec).erase (dec x) = (l.erase x).map dec :=
    fun l x=>erase_map_inj dec hinj l x
  have hcont : ∀ (l:List Nat) w,(l.map dec).any (fun x=>x.1==w) = l.contains w:=by
    intro l w; apply Bool.eq_iff_iff.2; simp [hfst]
  unfold nextD_decor nextD
  simp only [List.any_map,Function.comp_def,hfst,herase,hcont,hop,List.map_cons]
theorem nextD_decor_eq (u:Bool) {dm:Nat} (hd : dm&&&mask256 = dm)
    (pairs:List (Nat × Nat))
    (hr1 : ∀ r ∈ pairs.map Prod.fst,dm.testBit r = true)
    (hr2 : ∀ r ∈ pairs.map Prod.snd,dm.testBit r = true)
    (slack:Nat) (ws:List Nat) (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    let dec:=fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w)
    nextD_decor u dm (maskP pairs.length) slack (ws.map dec) g =
      nextD u dm slack ws (fun opab zs=>g opab (zs.map dec)):=by
  intro dec
  apply nextD_decor_gen
  · intro w; rfl
  · intro op a b
    simp only [dec,projBit_opD hd hr1,projBit_opD hd hr2,List.length_map]
def addC (x:Nat) (c:Nat × Nat × Nat):Nat × Nat × Nat :=
  (c.1|||x,c.2.1|||(c.1&&&x),c.2.2|||(c.2.1&&&x))
def cov3 (mp:Nat) (d:Bool) (dws:List (Nat × Nat × Nat)):Nat × Nat × Nat :=
  dws.foldl (fun c dw=>addC (colB mp d dw.2) c) (0,0,0)
def takeOne (c:Nat × Nat × Nat) (x:Nat):Nat:=(c.1^^^x)|||c.2.1
def takeTwo (c:Nat × Nat × Nat) (x y:Nat):Nat :=
  (c.1^^^(x|||y))|||(c.2.1&&&(x^^^y))|||c.2.2
theorem cov3_bit (mp:Nat) (d:Bool) (dws:List (Nat × Nat × Nat)) (i:Nat) :
    let k:=dws.countP (fun dw=>(colB mp d dw.2).testBit i)
    (cov3 mp d dws).1.testBit i = decide (1 ≤ k) ∧
    (cov3 mp d dws).2.1.testBit i = decide (2 ≤ k) ∧
    (cov3 mp d dws).2.2.testBit i = decide (3 ≤ k):=by
  have hgen : ∀ (xs:List (Nat × Nat × Nat)) (c:Nat × Nat × Nat) (k0:Nat),
      (c.1.testBit i = decide (1 ≤ k0) ∧ c.2.1.testBit i = decide (2 ≤ k0) ∧ c.2.2.testBit i = decide (3 ≤ k0)) →
      let k:=k0 + xs.countP (fun dw=>(colB mp d dw.2).testBit i)
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).1.testBit i = decide (1 ≤ k) ∧
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).2.1.testBit i = decide (2 ≤ k) ∧
      (xs.foldl (fun acc dw=>addC (colB mp d dw.2) acc) c).2.2.testBit i = decide (3 ≤ k):=by
    intro xs
    induction xs with
    | nil=>intro c k0 ⟨h1,h2,h3⟩; simp [h1,h2,h3]
    | cons dw xs ih =>
      intro c k0 ⟨h1,h2,h3⟩
      simp only [List.foldl_cons,List.countP_cons]
      have hc : (addC (colB mp d dw.2) c).1.testBit i =
            decide (1 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.1.testBit i =
            decide (2 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) ∧
          (addC (colB mp d dw.2) c).2.2.testBit i =
            decide (3 ≤ k0 + (if (colB mp d dw.2).testBit i then 1 else 0)):=by
        simp only [addC,Nat.testBit_or,Nat.testBit_and,h1,h2,h3]
        cases hb : (colB mp d dw.2).testBit i <;>
          rcases k0 with _ | _ | _ | k0 <;>
          simp [hb,Nat.le_add_left]
      have ih':=ih (addC (colB mp d dw.2) c) (k0 + (if (colB mp d dw.2).testBit i then 1 else 0)) hc
      cases hb : (colB mp d dw.2).testBit i <;> simp only [hb,↓reduceIte,Bool.false_eq_true,Nat.add_zero] at ih' ⊢
      · exact ih'
      · simpa only [Nat.add_assoc,Nat.add_comm 1] using ih'
  simpa only [cov3,Nat.zero_testBit,Nat.zero_add] using hgen dws (0,0,0) 0 (by simp)
theorem cov3_perm (mp:Nat) (d:Bool) {xs ys:List (Nat × Nat × Nat)} (p : xs.Perm ys) :
    cov3 mp d xs = cov3 mp d ys:=by
  have heq : ∀ i,(cov3 mp d xs).1.testBit i = (cov3 mp d ys).1.testBit i ∧
      (cov3 mp d xs).2.1.testBit i = (cov3 mp d ys).2.1.testBit i ∧
      (cov3 mp d xs).2.2.testBit i = (cov3 mp d ys).2.2.testBit i:=by
    intro i
    obtain ⟨a1,a2,a3⟩:=cov3_bit mp d xs i
    obtain ⟨b1,b2,b3⟩:=cov3_bit mp d ys i
    rw [p.countP_eq] at a1 a2 a3
    exact ⟨a1.trans b1.symm,a2.trans b2.symm,a3.trans b3.symm⟩
  apply Prod.ext
  · exact Nat.eq_of_testBit_eq (fun i=>(heq i).1)
  · apply Prod.ext
    · exact Nat.eq_of_testBit_eq (fun i=>(heq i).2.1)
    · exact Nat.eq_of_testBit_eq (fun i=>(heq i).2.2)
theorem takeOne_eq (mp:Nat) (d:Bool) (a:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    takeOne (cov3 mp d (a :: rest)) (colB mp d a.2) = (cov3 mp d rest).1:=by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1,h2,_⟩:=cov3_bit mp d (a :: rest) i
  obtain ⟨r1,_,_⟩:=cov3_bit mp d rest i
  simp only [takeOne,Nat.testBit_or,Nat.testBit_xor,h1,h2,r1,List.countP_cons]
  set k:=rest.countP (fun dw=>(colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> simp only [ha,Bool.false_eq_true,↓reduceIte] <;>
    rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 by omega,show 2 ≤ k + 3 by omega,decide_true,Bool.xor_false,Bool.or_true]
  · decide
  · decide
  · decide
  · simp only [show 1 ≤ k + 3 + 1 by omega,show 2 ≤ k + 3 + 1 by omega,show 1 ≤ k + 3 by omega,
      decide_true,Bool.xor_true,Bool.or_true,Bool.or_false]
theorem takeTwo_eq (mp:Nat) (d:Bool) (a b:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    takeTwo (cov3 mp d (a :: b :: rest)) (colB mp d a.2) (colB mp d b.2) = (cov3 mp d rest).1:=by
  apply Nat.eq_of_testBit_eq; intro i
  obtain ⟨h1,h2,h3⟩:=cov3_bit mp d (a :: b :: rest) i
  obtain ⟨r1,_,_⟩:=cov3_bit mp d rest i
  simp only [takeTwo,Nat.testBit_or,Nat.testBit_and,Nat.testBit_xor,h1,h2,h3,r1,List.countP_cons]
  set k:=rest.countP (fun dw=>(colB mp d dw.2).testBit i)
  cases ha : (colB mp d a.2).testBit i <;> cases hb : (colB mp d b.2).testBit i <;>
    simp only [ha,hb,Bool.false_eq_true,↓reduceIte] <;>
    rcases k with _ | _ | _ | k <;>
    (first | decide | simp only [
      show 1 ≤ k + 3 by omega,show 2 ≤ k + 3 by omega,show 3 ≤ k + 3 by omega,
      show 1 ≤ k + 3 + 1 by omega,show 2 ≤ k + 3 + 1 by omega,show 3 ≤ k + 3 + 1 by omega,
      show 1 ≤ k + 3 + 1 + 1 by omega,show 2 ≤ k + 3 + 1 + 1 by omega,show 3 ≤ k + 3 + 1 + 1 by omega,
      decide_true,Bool.xor_true,Bool.xor_false,Bool.or_true,Bool.or_false,Bool.and_true,Bool.and_false])
theorem cov3_coversD (u:Bool) (mp:Nat) (dw:Nat × Nat × Nat) (rest:List (Nat × Nat × Nat)) :
    ((cov3 mp (!u) rest).1|||colB mp (!u) dw.2==mp) = coversD u mp (dw :: rest):=by
  have e : ((cov3 mp (!u) rest).1|||colB mp (!u) dw.2) =
      (dw :: rest).foldl (fun acc x=>acc|||colB mp (!u) x.2) 0:=by
    apply Nat.eq_of_testBit_eq; intro i
    obtain ⟨h1,_,_⟩:=cov3_bit mp (!u) rest i
    rw [foldl_or_testBit,Nat.zero_testBit,Bool.false_or,Nat.testBit_or,h1,List.any_cons]
    have hp : decide (1 ≤ rest.countP (fun dw=>(colB mp (!u) dw.2).testBit i)) =
        rest.any (fun x=>(colB mp (!u) x.2).testBit i):=by
      rw [Bool.eq_iff_iff,decide_eq_true_eq,Nat.succ_le_iff,List.countP_pos_iff,List.any_eq_true]
    rw [hp,Bool.or_comm]
  unfold coversD; exact congrArg (·==mp) e
def nextD_cov (u:Bool) (dm mp slack:Nat) (dws:List (Nat × Nat × Nat))
    (f : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool):Bool :=
  let ori:=!u
  let cov:=cov3 mp ori dws
  dws.any fun da =>
    let a:=da.1
    let ca:=colB mp ori da.2
    let ra:=dws.erase da
    ra.any fun db =>
      let b:=db.1
      a ≤ b &&
        (let cb:=colB mp ori db.2
         let base0:=takeTwo cov ca cb
         let base1a:=takeOne cov cb
         let base1b:=takeOne cov ca
         let r:=ra.erase db
         (opsOf u).any fun op =>
           let pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
           let cz:=colB mp ori pz
           let ok0:=(base0|||cz)==mp
           let ok1a:=slack ≥ 1&&((base1a|||cz)==mp)
           let ok1b:=slack ≥ 1&&((base1b|||cz)==mp)
           let ok2:=slack ≥ 2&&((cov.1|||cz)==mp)
           (ok0||ok1a||ok1b||ok2) &&
           (let w:=opD dm op a b
            let g:=(op,a,b)
            w != 0&&w != dm&&!(dws.any (fun x=>x.1==w)) &&
              let dw:=(w,pz)
              ((ok0&&f g (dw :: r))||(ok1a&&f g (dw :: da :: r)) ||
               (ok1b&&f g (dw :: db :: r))||(ok2&&f g (dw :: da :: db :: r)))))
theorem nextD_cov_eq (u:Bool) (dm mp slack:Nat) (dws:List (Nat × Nat × Nat))
    (g : (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool) :
    nextD_cov u dm mp slack dws g =
      nextD_decor u dm mp slack dws (fun opab dzs=>coversD u mp dzs&&g opab dzs):=by
  unfold nextD_cov nextD_decor
  dsimp only
  apply Bool.eq_iff_iff.2; simp only [List.any_eq_true,Bool.or_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨da,hda,db,hdb,hab,op,hop,_,⟨⟨hw0,hwdm⟩,hnw⟩,hfx⟩
    refine ⟨da,hda,db,hdb,hab,op,hop,⟨⟨hw0,hwdm⟩,hnw⟩,?_⟩
    set pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
    set dw:=(opD dm op da.1 db.1,pz)
    set ra:=dws.erase da
    set r:=ra.erase db
    have hp : dws.Perm (da :: db :: r):=(List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
    have hc2:=cov3_perm mp (!u) hp
    have hca:=cov3_perm mp (!u) (hp.trans (List.Perm.swap _ _ _))
    have hcov0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: r):=by rw [hc2,takeTwo_eq]; exact cov3_coversD u mp dw r
    have hcov1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: r):=by rw [hca,takeOne_eq]; exact cov3_coversD u mp dw (da :: r)
    have hcov1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: db :: r):=by rw [hc2,takeOne_eq]; exact cov3_coversD u mp dw (db :: r)
    have hcov2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: db :: r):=by rw [hc2]; exact cov3_coversD u mp dw (da :: db :: r)
    rcases hfx with ((⟨hu0,hf0⟩ | ⟨⟨hsl1,hu1a⟩,hf1a⟩) | ⟨⟨hsl1,hu1b⟩,hf1b⟩) | ⟨⟨hsl2,hu2⟩,hf2⟩
    · left; left; exact ⟨hcov0 ▸ hu0,hf0⟩
    · left; right; exact ⟨hsl1,Or.inl ⟨hcov1a ▸ hu1a,hf1a⟩⟩
    · left; right; exact ⟨hsl1,Or.inr ⟨hcov1b ▸ hu1b,hf1b⟩⟩
    · right; exact ⟨hsl2,hcov2 ▸ hu2,hf2⟩
  · rintro ⟨da,hda,db,hdb,hab,op,hop,⟨⟨hw0,hwdm⟩,hnw⟩,hfx⟩
    refine ⟨da,hda,db,hdb,hab,op,hop,?_⟩
    set pz:=(opP mp op da.2.1 db.2.1,opP mp op da.2.2 db.2.2)
    set dw:=(opD dm op da.1 db.1,pz)
    set ra:=dws.erase da
    set r:=ra.erase db
    have hp : dws.Perm (da :: db :: r):=(List.perm_cons_erase hda).trans (List.Perm.cons _ (List.perm_cons_erase hdb))
    have hc2:=cov3_perm mp (!u) hp
    have hca:=cov3_perm mp (!u) (hp.trans (List.Perm.swap _ _ _))
    have hcov0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: r):=by rw [hc2,takeTwo_eq]; exact cov3_coversD u mp dw r
    have hcov1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: r):=by rw [hca,takeOne_eq]; exact cov3_coversD u mp dw (da :: r)
    have hcov1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: db :: r):=by rw [hc2,takeOne_eq]; exact cov3_coversD u mp dw (db :: r)
    have hcov2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) =
        coversD u mp (dw :: da :: db :: r):=by rw [hc2]; exact cov3_coversD u mp dw (da :: db :: r)
    rcases hfx with (⟨hc0,hg0⟩ | ⟨hsl1,⟨hc1a,hg1a⟩ | ⟨hc1b,hg1b⟩⟩) | ⟨hsl2,hc2',hg2⟩
    · have u0 : (takeTwo (cov3 mp (!u) dws) (colB mp (!u) da.2) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) = true:=hcov0.symm ▸ hc0
      exact ⟨Or.inl (Or.inl (Or.inl u0)),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inl (Or.inl ⟨u0,hg0⟩))⟩
    · have u1a : (takeOne (cov3 mp (!u) dws) (colB mp (!u) db.2)|||colB mp (!u) pz==mp) = true:=hcov1a.symm ▸ hc1a
      exact ⟨Or.inl (Or.inl (Or.inr ⟨hsl1,u1a⟩)),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inl (Or.inr ⟨⟨hsl1,u1a⟩,hg1a⟩))⟩
    · have u1b : (takeOne (cov3 mp (!u) dws) (colB mp (!u) da.2)|||colB mp (!u) pz==mp) = true:=hcov1b.symm ▸ hc1b
      exact ⟨Or.inl (Or.inr ⟨hsl1,u1b⟩),⟨⟨hw0,hwdm⟩,hnw⟩,Or.inl (Or.inr ⟨⟨hsl1,u1b⟩,hg1b⟩)⟩
    · have u2 : ((cov3 mp (!u) dws).1|||colB mp (!u) pz==mp) = true:=hcov2.symm ▸ hc2'
      exact ⟨Or.inr ⟨hsl2,u2⟩,⟨⟨hw0,hwdm⟩,hnw⟩,Or.inr ⟨⟨hsl2,u2⟩,hg2⟩⟩
def bar (u:Bool) (dm Y:Nat) (mp:Nat)
    (SD:Nat → Nat → List (Nat × Nat × Nat)) (S:Nat → Nat → List Nat)
    (N:Nat → Nat) (htAt idxH:Nat → Nat → Nat)
    (ori:List Nat → List Nat) (seed:Nat) (pool:List Nat)
    (mkCut:Nat → Nat → (Nat × Nat × Nat) → List Nat → Bool):Nat → Nat → Bool
  | 0,i=>!(S 0 i==[Y])
  | s + 1,i =>
    let dws:=SD (s + 1) i
    !(nextD_cov u dm mp (s + 2 - dws.length) dws fun g dzs =>
        let zs:=dzs.map Prod.fst
        !(scr u dm Y s pool zs)&&!(mkCut (s + 1) i g zs) &&
        (let cz:=ori zs
         let h:=hk seed cz
         !(foundH S N htAt idxH s h cz)))
def barP (u:Bool) (dm Y:Nat) (mp:Nat)
    (SD:Nat → Nat → List (Nat × Nat × Nat)) (S:Nat → Nat → List Nat)
    (N:Nat → Nat) (htAt idxH:Nat → Nat → Nat)
    (ori:List Nat → List Nat) (seed:Nat) (pool:List Nat)
    (mkPools:Nat → Nat → List (Nat × Nat × (Nat × List Nat))):Nat → Nat → Bool
  | 0,i=>!(S 0 i==[Y])
  | s + 1,i =>
    let dws:=SD (s + 1) i
    match mkPools (s + 1) i with
    | [] =>
      !(nextD_cov u dm mp (s + 2 - dws.length) dws fun _ dzs =>
          let zs:=dzs.map Prod.fst
          !(scr u dm Y s pool zs) &&
          (let cz:=ori zs; let h:=hk seed cz; !(foundH S N htAt idxH s h cz)))
    | p :: ps =>
      !(nextD_cov u dm mp (s + 2 - dws.length) dws fun g dzs =>
          let zs:=dzs.map Prod.fst
          !(scr u dm Y s pool zs) &&
          !((p :: ps).any fun e=>checkPool u e.1 e.2.1 s (stepOp u e.1 e.2.2 g) zs) &&
          (let cz:=ori zs; let h:=hk seed cz; !(foundH S N htAt idxH s h cz)))
theorem lower_of_search {u:Bool} {d T L:Nat} {roots:List Nat} {pairs:List (Nat × Nat)}
    (hinit : (d&&&mask256==d)&&d.testBit 0&&!(T.testBit 0)&&roots.all (fun r=>!r.testBit 0) &&
             !(isConstB d T)&&decide ((roots.map (·&&&d)).Nodup) &&
             pairs.all (fun p=>d.testBit p.1&&d.testBit p.2&&((T&&&d).testBit p.1 != (T&&&d).testBit p.2)) = true)
    (hpf : ∀ zs ∈ (roots.map (·&&&d)).sublists,zs ≠ roots.map (·&&&d) → unorientedCov pairs zs = false)
    (hno : ∀ s ≤ L - 1,RunD u d (T&&&d) s (roots.map (·&&&d)) → False) :
    Lower u d roots T L:=by
  simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true',decide_eq_true_eq] at hinit
  obtain ⟨⟨⟨⟨⟨⟨hd,hd0⟩,hT0⟩,hR0⟩,hncb⟩,hnd_xs'⟩,hpairs⟩:=hinit
  intro p bank hr ha
  by_contra! hsmall
  have hnc : ¬ IsConst d T:=fun h=>by rw [(isConstB_iff _ _).2 h] at hncb; contradiction
  obtain ⟨s,ws,hs_le,hnd,hws_sub,hrun⟩:=reach_to_run hd hd0 hT0 hR0 hnc hr ha
  have hperm_sub : ∃ zs,zs.Sublist (roots.map (·&&&d)) ∧ ws.Perm zs:=by
    refine ⟨(roots.map (·&&&d)).filter (fun x=>decide (x ∈ ws)),List.filter_sublist,?_⟩
    refine (List.perm_ext_iff_of_nodup hnd (List.Nodup.filter _ hnd_xs')).2 ?_
    intro x; simp only [List.mem_filter,decide_eq_true_eq]
    exact ⟨fun hx=>⟨hws_sub x hx,hx⟩,fun h=>h.2⟩
  obtain ⟨zs,hsub,hpz⟩:=hperm_sub
  have hrun':=Run.perm hpz hrun
  by_cases heq : zs = roots.map (·&&&d)
  · subst heq; exact hno s (by omega) hrun'
  · have hcov:=unorientedCov_ok hd pairs hpairs hrun'
    rw [hpf zs (List.mem_sublists.2 hsub) heq] at hcov; contradiction
theorem barP_eq (u:Bool) (dm Y mp:Nat) (SD S N htAt idxH ori seed pool mkPools s i) :
    barP u dm Y mp SD S N htAt idxH ori seed pool mkPools s i =
      bar u dm Y mp SD S N htAt idxH ori seed pool
        (fun s' i' g zs=>(mkPools s' i').any fun e=>checkPool u e.1 e.2.1 (s' - 1) (stepOp u e.1 e.2.2 g) zs) s i:=by
  cases s with
  | zero=>rfl
  | succ s =>
    unfold barP bar; dsimp only
    cases mkPools (s + 1) i with
    | nil=>simp
    | cons p ps=>rfl
theorem bar_all {u:Bool} {dm T:Nat} {pairs:List (Nat × Nat)} {r1s r2s mp SD S N htAt idxH ori seed pool mkCut cap}
    (hd : dm&&&mask256 = dm)
    (hr1_eq : r1s = pairs.map Prod.fst) (hr2_eq : r2s = pairs.map Prod.snd) (hmp_eq : mp = maskP pairs.length)
    (hSD : ∀ s j,SD s j = (S s j).map (fun w=>(w,projBit r1s w,projBit r2s w)))
    (hpairs : pairs.all (fun p=>dm.testBit p.1&&dm.testBit p.2&&!(T&&&dm).testBit p.1&&(T&&&dm).testBit p.2) = true)
    (hr : ∀ {v ys},RunD u dm (T&&&dm) v ys → RunD u dm (T&&&dm) v (ori ys))
    (hcut : ∀ {s i g ys},mkCut (s + 1) i g ys = true → ¬ RunD u dm (T&&&dm) s ys)
    (hc : ∀ s ≤ cap,∀ i < N s,bar u dm (T&&&dm) mp SD S N htAt idxH ori seed pool mkCut s i = true) :
    ∀ s ≤ cap,∀ i < N s,¬ RunD u dm (T&&&dm) s (S s i):=by
  subst hr1_eq hr2_eq hmp_eq
  have hr1 : ∀ r ∈ pairs.map Prod.fst,dm.testBit r = true:=by
    intro r hr'; obtain ⟨p,hp,rfl⟩:=List.mem_map.1 hr'
    have h:=List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.1
  have hr2 : ∀ r ∈ pairs.map Prod.snd,dm.testBit r = true:=by
    intro r hr'; obtain ⟨p,hp,rfl⟩:=List.mem_map.1 hr'
    have h:=List.all_eq_true.1 hpairs p hp; simp only [Bool.and_eq_true] at h; exact h.1.1.2
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi hh
    have hb:=hc s hs i hi
    cases s with
    | zero=>simp [bar,zero_done hh rfl] at hb
    | succ s =>
      by_contra! hn
      let F (g:Nat × Nat × Nat) (zs:List Nat) :=
        coversP u pairs zs&&!(scr u dm (T&&&dm) s pool zs)&&!(mkCut (s + 1) i g zs) &&
        (let cz:=ori zs
         let h:=hk seed cz
         !(foundH S N htAt idxH s h cz))
      have hF (g zs) (hz : RunD u dm (T&&&dm) s zs) : F g zs = true:=by
        have hcz:=hr hz
        have hcutf : mkCut (s + 1) i g zs = false:=by
          cases h : mkCut (s + 1) i g zs with
          | false=>rfl
          | true=>exact absurd hz (hcut h)
        simp only [F,coversP_ok hd pairs hpairs hz,scr_no pool hz,hcutf,Bool.not_false,Bool.true_and,foundH]
        simp only [Bool.not_eq_true',Bool.and_eq_false_imp,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq]
        rintro ⟨hj,_⟩
        by_contra! hp
        have p:=List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
        exact ih s (by omega) (by omega) _ hj (Run.perm p hcz)
      have hN:=nextD_complete hh s rfl _ (List.Perm.refl _) F hF
      dsimp only [bar] at hb
      rw [hSD,List.length_map,nextD_cov_eq,nextD_decor_eq u hd pairs hr1 hr2] at hb
      have hFeq : (fun g zs=>coversD u (maskP pairs.length) (zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))) &&
          (let zs':=(zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))).map Prod.fst
           !(scr u dm (T&&&dm) s pool zs')&&!(mkCut (s + 1) i g zs') &&
           (let cz:=ori zs'
            let h:=hk seed cz
            !(foundH S N htAt idxH s h cz)))) = F:=by
        funext g zs
        have hfst : (zs.map (fun w=>(w,projBit (pairs.map Prod.fst) w,projBit (pairs.map Prod.snd) w))).map Prod.fst = zs:=by
          simp [List.map_map,Function.comp_def]
        rw [coversD_eq,hfst]
        simp only [F,Bool.and_assoc]
      rw [hFeq,hN] at hb
      contradiction
def pickMin (seed:Nat) (orig:List Nat):List (List (Nat × Nat)) → List Nat → Nat → List Nat
  | [],best,_=>best
  | ms :: rest,best,bestH =>
    let img:=orig.map (applyMoves ms)
    let h:=hk seed img
    if h < bestH then pickMin seed orig rest img h else pickMin seed orig rest best bestH
theorem pickMin_runD {u:Bool} {dm Y v} (seed:Nat) (orig:List Nat) (h0 : RunD u dm Y v orig) :
    ∀ (syms:List (List (Nat × Nat))) (best:List Nat) (bestH:Nat),
      syms.all (fun ms=>ms.all moveOK256&&(applyMoves ms dm==dm)&&(applyMoves ms Y==Y)) = true →
      RunD u dm Y v best →
      RunD u dm Y v (pickMin seed orig syms best bestH)
  | [],_,_,_,hb=>hb
  | ms :: rest,best,bestH,hok,hb=>by
    simp only [List.all_cons,Bool.and_eq_true,beq_iff_eq] at hok
    unfold pickMin; dsimp only; split
    · exact pickMin_runD seed orig h0 rest _ _ hok.2 (applyMoves_runD ms hok.1.1.1 hok.1.1.2 hok.1.2 h0)
    · exact pickMin_runD seed orig h0 rest best bestH hok.2 hb
def xs256:List Nat :=
  [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
   0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
   0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
   0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
   0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
   0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
   0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
   0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def dom_187 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def roots_187 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_187 : Nat := 0xf0f0f0f0f0f0f0e00000000000000000f0e0f0a0e0c0a00
def dom_186 : Nat := 0x50505050505050500000000000000000505050505050505
def roots_186 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_186 : Nat := 0x50505050505050400000000000000000504050004040000
def dom_184 : Nat := 0x10101010101010100000000000000000101010101010101
def roots_184 : List Nat := [xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_184 : Nat := 0x10101010101010000000000000000000100010000000000
def dom_168 : Nat := 0x1010000010100000000000000000000010100000101
def roots_168 : List Nat := [xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_168 : Nat := 0x1010000010000000000000000000000010000000000
def dom_178 : Nat := 0x500050005000500000000000000000005000500050005
def roots_178 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_178 : Nat := 0x500050005000400000000000000000004000000040000
def dom_146 : Nat := 0x5000500000000000000000000000000050005
def roots_146 : List Nat := [xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_146 : Nat := 0x5000400000000000000000000000000040000
def dom_170 : Nat := 0x5050000050500000000000000000000050500000505
def roots_170 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_170 : Nat := 0x5050000050400000000000000000000050000000000
def dom_154 : Nat := 0x505050500000000000000000000000005050505
def roots_154 : List Nat := [xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_154 : Nat := 0x505050400000000000000000000000004040000
def dom_185 : Nat := 0x30303030303030300000000000000000303030303030303
def roots_185 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_185 : Nat := 0x30303030303030200000000000000000302030202000200
def dom_169 : Nat := 0x3030000030300000000000000000000030300000303
def roots_169 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_169 : Nat := 0x3030000030200000000000000000000030200000200
def dom_161 : Nat := 0x30000000300000000000000000000000300000003
def roots_161 : List Nat := [xs256.getD 0 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_161 : Nat := 0x30000000200000000000000000000000200000000
def dom_137 : Nat := 0x30300000000000000000000000000000303
def roots_137 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 7 0]
def goal_137 : Nat := 0x30200000000000000000000000000000200
def dom_41 : Nat := 0x30300000303
def roots_41 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 5 0]
def goal_41 : Nat := 0x30200000200
def dom_179 : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
def roots_179 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_179 : Nat := 0xf000f000f000e0000000000000000000e000a000c0000
def dom_177 : Nat := 0x300030003000300000000000000000003000300030003
def roots_177 : List Nat := [xs256.getD 0 0, xs256.getD 4 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_177 : Nat := 0x300030003000200000000000000000002000200000000
def dom_163 : Nat := 0xf0000000f00000000000000000000000f0000000f
def roots_163 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_163 : Nat := 0xf0000000e00000000000000000000000a00000000
def dom_147 : Nat := 0xf000f000000000000000000000000000f000f
def roots_147 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_147 : Nat := 0xf000e000000000000000000000000000c0000
def dom_171 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
def roots_171 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 5 0, xs256.getD 7 0]
def goal_171 : Nat := 0xf0f00000f0e000000000000000000000f0a00000a00
def dom_155 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def roots_155 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_155 : Nat := 0xf0f0f0e0000000000000000000000000e0c0a00
def dom_153 : Nat := 0x303030300000000000000000000000003030303
def roots_153 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 7 0]
def goal_153 : Nat := 0x303030200000000000000000000000002000200
def dom_139 : Nat := 0xf0f00000000000000000000000000000f0f
def roots_139 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 7 0]
def goal_139 : Nat := 0xf0e00000000000000000000000000000a00
def goal_185_l144 : Nat := 0x30303030303030300000000000000000303030203030200
def goal_169_l128 : Nat := 0x3030000030300000000000000000000030200000200
def dzo_185_2 : Nat := 0xc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c
def gzo_185_2_144 : Nat := 0xc0c0c0c0c0c0c0c00000000000000000c0c0c080c0c0800
def goal_171_l130 : Nat := 0xf0f00000f0f000000000000000000000f0e00000e0c
def dzo_171_16 : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f0000
def gzo_171_16_130 : Nat := 0xf0f00000f0f000000000000000000000f0e00000e0c0000
def dom_59 : Nat := 0xf0f0f0f0f0f0f0f
def roots_59 : List Nat := [xs256.getD 0 0, xs256.getD 1 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def goal_59 : Nat := 0xf0e0f0a0e0c0a00
def dom_57 : Nat := 0x303030303030303
def roots_57 : List Nat := [xs256.getD 0 0, xs256.getD 3 0, xs256.getD 4 0, xs256.getD 5 0]
def goal_57_l16 : Nat := 0x303030203030200
def dzo_57_2 : Nat := 0xc0c0c0c0c0c0c0c
def gzo_57_2_16 : Nat := 0xc0c0c080c0c0800
end PEqualNP.Outside.L_meta_32199.Donor
namespace PEqualNP.Outside.L_meta_32199.Donor
open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds
theorem chartBlocks (f : Nat → Bool) (n : Nat)
    (checks : ∀ k : Fin ((n + 11) / 12), span f (min 12 (n - 12*k.val)) (12*k.val) = true) :
    ∀ i < n, f i = true := by
  intro i hi
  have hk : i/12 < (n+11)/12 := by omega
  have v := checks ⟨i/12, hk⟩
  exact span_ok v i (by dsimp; omega) (by dsimp; omega)
namespace S_168
def pairsG : List (Nat × Nat) := [(8,40), (8,136), (32,40), (32,160), (128,136), (128,160)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3f
def pool6G : List Nat := []
def xsM : List Nat := roots_168.map (· &&& dom_168)
def goalM : Nat := goal_168 &&& dom_168
def NN : Nat → Nat
|2=>0x1
|3=>0x1
|_=>0
def HT : Nat → Nat → Nat
|2,0=>0xa17dd
|3,0=>0xa17dd
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xf0ccaa
|_,_=>0
def scatter (v : Nat) : Nat :=
  let lo := v &&& 0xf
  let v := lo ||| ((v ^^^ lo) <<< 124)
  let lo := v &&& 0x300000000000000000000000000000003
  let v := lo ||| ((v ^^^ lo) <<< 30)
  let lo := v &&& 0x10000000100000000000000000000000100000001
  let v := lo ||| ((v ^^^ lo) <<< 7)
  v
def stPool : Nat → Nat
|0=>0x924
|_=>0
def stOffB : Nat → Nat → Nat
|2,0=>0x3
|3,0=>0x33
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 3 then scatter (fld (dictB (i / 512) (i / 32 % 16)) 8 (i % 32)) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 2 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 6 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))
def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 2 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def mkPools (_ _ : Nat) : List (Nat × Nat × (Nat × List Nat)) := []
def mkCut (_ _ : Nat) (_ : Nat × Nat × Nat) (_ : List Nat) : Bool := false
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_168 goalM s ys := by simp [mkCut] at h
def cutRoot (_ : Nat) (_ : List Nat) : Bool := false
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_168 goalM v ys := by simp [cutRoot] at h
def symsG : List (List (Nat × Nat)) := [[(0xffffffff00000000ffffffff00000000, 96)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_168 == dom_168) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_168 goalM v ys) : RunD true dom_168 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s : Nat) := barP true dom_168 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checked (s : Nat) (hs : s ≤ 3) : ∀ i < NN s, bar true dom_168 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]
  change Z s i = true
  apply chartBlocks (Z s) (NN s) _ i hi
  interval_cases s <;> intro k <;> fin_cases k <;> decide +kernel
def RootG (s : Nat) : Bool :=
  scr true dom_168 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 2 2 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 3) (h : RunD true dom_168 goalM s xsM) : False := by
  have hmin : 2 ≤ s := by
    have hl := run_len h; change 3 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower true dom_168 roots_168 goal_168 4 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull
end S_168
theorem low_168 : Lower true dom_168 roots_168 goal_168 4 := S_168.noCircuit
theorem low_184 : Lower true dom_184 roots_184 goal_184 5 := by
  apply lower_slice (d:=dom_184) (dSub:=dom_168) (T:=goal_184) (TSub:=goal_168) (roots:=roots_184) (rootsSub:=roots_168) (singles:=[(0x10100000101000000000000000000000101000001010000, 128, 144)]) (hprior:=low_168) <;> decide +kernel
namespace S_146
theorem noCircuit : Lower true dom_146 roots_146 goal_146 4 :=
  lower_iso (d1:=dom_168) (roots1:=roots_168) (T1:=goal_168) [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) S_168.noCircuit
end S_146
theorem low_146 : Lower true dom_146 roots_146 goal_146 4 := S_146.noCircuit
theorem low_178 : Lower true dom_178 roots_178 goal_178 5 := by
  apply lower_slice (d:=dom_178) (dSub:=dom_146) (T:=goal_178) (TSub:=goal_146) (roots:=roots_178) (rootsSub:=roots_146) (singles:=[(0x500050000000000000000000000000005000500000000, 128, 160)]) (hprior:=low_146) <;> decide +kernel
theorem low_170 : Lower true dom_170 roots_170 goal_170 5 := by
  apply lower_slice (d:=dom_170) (dSub:=dom_168) (T:=goal_170) (TSub:=goal_168) (roots:=roots_170) (rootsSub:=roots_168) (singles:=[(0x4040000040400000000000000000000040400000404, 128, 130)]) (hprior:=low_168) <;> decide +kernel
theorem low_154 : Lower true dom_154 roots_154 goal_154 5 := by
  apply lower_slice (d:=dom_154) (dSub:=dom_146) (T:=goal_154) (TSub:=goal_146) (roots:=roots_154) (rootsSub:=roots_146) (singles:=[(0x500050000000000000000000000000005000500, 128, 136)]) (hprior:=low_146) <;> decide +kernel
namespace S_186
def pairsG : List (Nat × Nat) := [(2,18), (2,130), (8,40), (8,136), (10,26), (10,42), (10,138), (16,18), (16,144), (24,26), (24,56), (24,152), (32,40), (32,160), (34,42), (34,50), (34,162), (48,50), (48,56), (48,176), (128,130), (128,136), (128,144), (128,160)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_186.map (· &&& dom_186)
def goalM : Nat := goal_186 &&& dom_186
def NN : Nat → Nat
|3=>0x1
|4=>0x4
|5=>0xa
|6=>0x4
|7=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x31788
|4,0=>0x25d551c18c0ee180bc15
|5,0=>0x481f52ee801c65b198281588e12bc4066ab05e6d027af0243e
|6,0=>0x54d664de4722d7509523
|7,0=>0x54d66
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0x333300000f0f0a0afff0fff0fff0000000ff000011110000fffff0f0555550500000eeeefcfcfcfcfffffcfc0f0f0000ff0fff000f0f0f00ffaa0000ffffaaaacccccccc50555050ff00ff00ffff000033333322f0f0f0f0aaaaaaaaffffff00ffeecccc
|_,_=>0
def scatter (v : Nat) : Nat :=
  let lo := v &&& 0xffff
  let v := lo ||| ((v ^^^ lo) <<< 112)
  let lo := v &&& 0xff000000000000000000000000000000ff
  let v := lo ||| ((v ^^^ lo) <<< 24)
  let lo := v &&& 0xf0000000f00000000000000000000000f0000000f
  let v := lo ||| ((v ^^^ lo) <<< 12)
  let lo := v &&& 0x300030003000300000000000000000003000300030003
  let v := lo ||| ((v ^^^ lo) <<< 6)
  let lo := v &&& 0x10101010101010100000000000000000101010101010101
  let v := lo ||| ((v ^^^ lo) <<< 1)
  v
def stPool : Nat → Nat
|0=>0x14c3408a61a045408c3b0d0229823308a8c190515d0230cb53090f2c8681143430d022ccc828e5130d022c0c240cae408a3330482986b188c5020665250530ce3118a418820
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x4
|4,0=>0x26a3944a845
|5,0=>0x272c8684cf19b330654c918f3186
|6,0=>0xcab7dacb536
|7,0=>0x6a5
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 25 then scatter (fld (dictB (i / 512) (i / 32 % 16)) 32 (i % 32)) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 5 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 11 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))
def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 5 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x30d2992a32d830d28d40d09b29990b28d2bd40d33528f
|_=>0
def opOffB : Nat → Nat → Nat
|5,0=>0xa28262004200220200
|6,0=>0xf0e1d1c1
|7,0=>0xf0
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 12 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 31), wireSAt ((code >>> 7) &&& 31)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 8 (j % 64)
  readOps (v &&& 15) (v >>> 4)
def pmB : Nat → Nat → Nat
|5,0=>0x3c4a8005030800
|6,0=>0x3ffb6f
|7,0=>0x3b
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 6 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_184,5,runOps true dom_184 (0,roots_184) ops)] else [])++(if pm.testBit 1 then [(dom_178,5,runOps true dom_178 (0,roots_178) ops)] else [])++(if pm.testBit 2 then [(dom_170,5,runOps true dom_170 (0,roots_170) ops)] else [])++(if pm.testBit 3 then [(dom_154,5,runOps true dom_154 (0,roots_154) ops)] else [])++(if pm.testBit 4 then [(dom_168,4,runOps true dom_168 (0,roots_168) ops)] else [])++(if pm.testBit 5 then [(dom_146,4,runOps true dom_146 (0,roots_146) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_186 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_184 _ g hchk
    · exact cpcs (by decide +kernel) low_178 _ g hchk
    · exact cpcs (by decide +kernel) low_170 _ g hchk
    · exact cpcs (by decide +kernel) low_154 _ g hchk
    · exact cpcs (by decide +kernel) low_168 _ g hchk
    · exact cpcs (by decide +kernel) low_146 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_184 5 s (0, roots_184) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_186 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_184 h
def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_186 == dom_186) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_186 goalM v ys) : RunD true dom_186 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s : Nat) := barP true dom_186 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checked (s : Nat) (hs : s ≤ 7) : ∀ i < NN s, bar true dom_186 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]
  change Z s i = true
  apply chartBlocks (Z s) (NN s) _ i hi
  interval_cases s <;> intro k <;> fin_cases k <;> decide +kernel
def RootG (s : Nat) : Bool :=
  scr true dom_186 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 4 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 7) (h : RunD true dom_186 goalM s xsM) : False := by
  have hmin : 4 ≤ s := by
    have hl := run_len h; change 5 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower true dom_186 roots_186 goal_186 8 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull
end S_186
theorem low_186 : Lower true dom_186 roots_186 goal_186 8 := S_186.noCircuit
namespace S_161
theorem noCircuit : Lower true dom_161 roots_161 goal_161 4 :=
  lower_iso (d1:=dom_168) (roots1:=roots_168) (T1:=goal_168) [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7),(0x2222222222222222222222222222222222222222222222222222222222222222,1),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) S_168.noCircuit
end S_161
theorem low_161 : Lower true dom_161 roots_161 goal_161 4 := S_161.noCircuit
namespace S_137
theorem noCircuit : Lower true dom_137 roots_137 goal_137 4 :=
  lower_iso (d1:=dom_168) (roots1:=roots_168) (T1:=goal_168) [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7),(0x2222222222222222222222222222222222222222222222222222222222222222,1),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) S_168.noCircuit
end S_137
theorem low_137 : Lower true dom_137 roots_137 goal_137 4 := S_137.noCircuit
namespace S_41
theorem noCircuit : Lower true dom_41 roots_41 goal_41 4 :=
  lower_iso (d1:=dom_168) (roots1:=roots_168) (T1:=goal_168) [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7),(0x2222222222222222222222222222222222222222222222222222222222222222,1),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,2),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xffff0000ffff0000ffff0000ffff0000,112),(0xffff0000ffff00000000000000000000ffff0000ffff0000,48)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) S_168.noCircuit
end S_41
theorem low_41 : Lower true dom_41 roots_41 goal_41 4 := S_41.noCircuit
namespace S_169
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (1,129), (8,9), (8,40), (8,136), (32,33), (32,40), (32,160), (128,129), (128,136), (128,160)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0xfff
def pool6G : List Nat := []
def xsM : List Nat := roots_169.map (· &&& dom_169)
def goalM : Nat := goal_169 &&& dom_169
def NN : Nat → Nat
|3=>0x3
|4=>0x3
|5=>0x2
|6=>0x1
|_=>0
def HT : Nat → Nat → Nat
|3,0=>0x9c2c63901d21fd5
|4,0=>0x1d4141410202b7e
|5,0=>0xde1e401733
|6,0=>0xde1e4
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xe0efefe5554ff00fafafcfceeeeccccaaaaf0f0fe00
|_,_=>0
def scatter (v : Nat) : Nat :=
  let lo := v &&& 0xff
  let v := lo ||| ((v ^^^ lo) <<< 120)
  let lo := v &&& 0xf0000000000000000000000000000000f
  let v := lo ||| ((v ^^^ lo) <<< 28)
  let lo := v &&& 0x30000000300000000000000000000000300000003
  let v := lo ||| ((v ^^^ lo) <<< 6)
  v
def stPool : Nat → Nat
|0=>0x7132713271324726357321a73219137876543210
|_=>0
def stOffB : Nat → Nat → Nat
|3,0=>0x8411004
|4,0=>0x165454c5
|5,0=>0x811b5
|6,0=>0x244
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 11 then scatter (fld (dictB (i / 512) (i / 32 % 16)) 16 (i % 32)) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (fld (stPool (p / 128)) 4 (p % 128)) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 10 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))
def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 3 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 0 zs)
def opPool : Nat → Nat
|0=>0x324c5214c931485
|_=>0
def opOffB : Nat → Nat → Nat
|3,0=>0x180
|4,0=>0xc8000
|5,0=>0x3051
|6,0=>0x60
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := fld (opPool (p / 64)) 10 (p % 64)
    (code &&& 3, wireSAt ((code >>> 2) &&& 15), wireSAt ((code >>> 6) &&& 15)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 7 (j % 64)
  readOps (v &&& 15) (v >>> 4)
def pmB : Nat → Nat → Nat
|3,0=>0x30
|4,0=>0x300
|5,0=>0x7f
|6,0=>0xf
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 4 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_168,4,runOps true dom_168 (0,roots_168) ops)] else [])++(if pm.testBit 1 then [(dom_161,4,runOps true dom_161 (0,roots_161) ops)] else [])++(if pm.testBit 2 then [(dom_137,4,runOps true dom_137 (0,roots_137) ops)] else [])++(if pm.testBit 3 then [(dom_41,4,runOps true dom_41 (0,roots_41) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_169 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_168 _ g hchk
    · exact cpcs (by decide +kernel) low_161 _ g hchk
    · exact cpcs (by decide +kernel) low_137 _ g hchk
    · exact cpcs (by decide +kernel) low_41 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_168 4 s (0, roots_168) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_169 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_168 h
def symsG : List (List (Nat × Nat)) := [[(0xffffffff00000000ffffffff00000000, 96)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xffffffff00000000ffffffff00000000, 96)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_169 == dom_169) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 0 zs symsG zs (hk 0 zs)
theorem ori_ok {v ys} (h : RunD true dom_169 goalM v ys) : RunD true dom_169 goalM v (ori ys) :=
  pickMin_runD 0 ys h symsG ys (hk 0 ys) symsG_ok h
def Z (s : Nat) := barP true dom_169 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkPools s
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checked (s : Nat) (hs : s ≤ 6) : ∀ i < NN s, bar true dom_169 goalM mpG SD SS NN htAt idxH ori 0 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]
  change Z s i = true
  apply chartBlocks (Z s) (NN s) _ i hi
  interval_cases s <;> intro k <;> fin_cases k <;> decide +kernel
def RootG (s : Nat) : Bool :=
  scr true dom_169 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 4 3 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 6) (h : RunD true dom_169 goalM s xsM) : False := by
  have hmin : 3 ≤ s := by
    have hl := run_len h; change 4 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower true dom_169 roots_169 goal_169 7 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull
end S_169
theorem low_169 : Lower true dom_169 roots_169 goal_169 7 := S_169.noCircuit
theorem low_185 : Lower true dom_185 roots_185 goal_185 8 := by
  apply lower_slice (d:=dom_185) (dSub:=dom_169) (T:=goal_185) (TSub:=goal_169) (roots:=roots_185) (rootsSub:=roots_169) (singles:=[(0x30300000303000000000000000000000303000003030000, 128, 144)]) (hprior:=low_169) <;> decide +kernel
theorem low_177 : Lower true dom_177 roots_177 goal_177 5 := by
  apply lower_slice (d:=dom_177) (dSub:=dom_161) (T:=goal_177) (TSub:=goal_161) (roots:=roots_177) (rootsSub:=roots_161) (singles:=[(0x300000003000000000000000000000003000000030000, 128, 144)]) (hprior:=low_161) <;> decide +kernel
theorem low_163 : Lower true dom_163 roots_163 goal_163 5 := by
  apply lower_slice (d:=dom_163) (dSub:=dom_161) (T:=goal_163) (TSub:=goal_161) (roots:=roots_163) (rootsSub:=roots_161) (singles:=[(0xc0000000c00000000000000000000000c0000000c, 128, 130)]) (hprior:=low_161) <;> decide +kernel
theorem low_147 : Lower true dom_147 roots_147 goal_147 5 := by
  apply lower_slice (d:=dom_147) (dSub:=dom_146) (T:=goal_147) (TSub:=goal_146) (roots:=roots_147) (rootsSub:=roots_146) (singles:=[(0xa000a000000000000000000000000000a000a, 128, 129)]) (hprior:=low_146) <;> decide +kernel
namespace S_179
theorem noCircuit : Lower true dom_179 roots_179 goal_179 8 :=
  lower_iso (d1:=dom_186) (roots1:=roots_186) (T1:=goal_186) [(0x2222222222222222222222222222222222222222222222222222222222222222,1),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3),(0xffff000000000000ffff000000000000ffff000000000000ffff0000,16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) S_186.noCircuit
end S_179
theorem low_179 : Lower true dom_179 roots_179 goal_179 8 := S_179.noCircuit
theorem low_171 : Lower true dom_171 roots_171 goal_171 8 := by
  apply lower_slice (d:=dom_171) (dSub:=dom_169) (T:=goal_171) (TSub:=goal_169) (roots:=roots_171) (rootsSub:=roots_169) (singles:=[(0xc0c00000c0c000000000000000000000c0c00000c0c, 128, 130)]) (hprior:=low_169) <;> decide +kernel
theorem low_153 : Lower true dom_153 roots_153 goal_153 5 := by
  apply lower_slice (d:=dom_153) (dSub:=dom_137) (T:=goal_153) (TSub:=goal_137) (roots:=roots_153) (rootsSub:=roots_137) (singles:=[(0x303000000000000000000000000000003030000, 128, 144)]) (hprior:=low_137) <;> decide +kernel
theorem low_139 : Lower true dom_139 roots_139 goal_139 5 := by
  apply lower_slice (d:=dom_139) (dSub:=dom_137) (T:=goal_139) (TSub:=goal_137) (roots:=roots_139) (rootsSub:=roots_137) (singles:=[(0xc0c00000000000000000000000000000c0c, 128, 130)]) (hprior:=low_137) <;> decide +kernel
namespace S_155
theorem noCircuit : Lower true dom_155 roots_155 goal_155 8 :=
  lower_iso (d1:=dom_186) (roots1:=roots_186) (T1:=goal_186) [(0x2222222222222222222222222222222222222222222222222222222222222222,1),(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,7),(0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,3),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12),(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0,28)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) S_186.noCircuit
end S_155
theorem low_155 : Lower true dom_155 roots_155 goal_155 8 := S_155.noCircuit
theorem low_169_l128 : Lower true dom_169 roots_169 goal_169_l128 5 := by
  apply lower_slice (d:=dom_169) (dSub:=dom_41) (T:=goal_169_l128) (TSub:=goal_41) (roots:=roots_169) (rootsSub:=roots_41) (singles:=[(0x3030000030300000000000000000000000000000000, 0, 128)]) (hprior:=low_41) <;> decide +kernel
theorem low_185_l144 : Lower true dom_185 roots_185 goal_185_l144 6 := by
  apply lower_slice (d:=dom_185) (dSub:=dom_169) (T:=goal_185_l144) (TSub:=goal_169_l128) (roots:=roots_185) (rootsSub:=roots_169) (singles:=[(0x30300000303000000000000000000000303000003030000, 0, 16)]) (hprior:=low_169_l128) <;> decide +kernel
theorem lowZ_185_2_144 : Lower true dzo_185_2 roots_185 gzo_185_2_144 6 :=
  lower_iso (d1:=dom_185) (roots1:=roots_185) (T1:=goal_185_l144) [(dom_185, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_185_l144
theorem low_171_l130 : Lower true dom_171 roots_171 goal_171_l130 6 := by
  apply lower_slice (d:=dom_171) (dSub:=dom_169) (T:=goal_171_l130) (TSub:=goal_169_l128) (roots:=roots_171) (rootsSub:=roots_169) (singles:=[(0xc0c00000c0c000000000000000000000c0c00000c0c, 0, 2)]) (hprior:=low_169_l128) <;> decide +kernel
theorem lowZ_171_16_130 : Lower true dzo_171_16 roots_171 gzo_171_16_130 6 :=
  lower_iso (d1:=dom_171) (roots1:=roots_171) (T1:=goal_171_l130) [(dom_171, 16)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_171_l130
theorem low_57_l16 : Lower true dom_57 roots_57 goal_57_l16 5 := by
  apply lower_slice (d:=dom_57) (dSub:=dom_41) (T:=goal_57_l16) (TSub:=goal_41) (roots:=roots_57) (rootsSub:=roots_41) (singles:=[(0x303000003030000, 0, 16)]) (hprior:=low_41) <;> decide +kernel
theorem lowZ_57_2_16 : Lower true dzo_57_2 roots_57 gzo_57_2_16 5 :=
  lower_iso (d1:=dom_57) (roots1:=roots_57) (T1:=goal_57_l16) [(dom_57, 2)] (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) low_57_l16
theorem low_59 : Lower true dom_59 roots_59 goal_59 6 := by
  apply lower_slice (d:=dom_59) (dSub:=dzo_57_2) (T:=goal_59) (TSub:=gzo_57_2_16) (roots:=roots_59) (rootsSub:=roots_57) (singles:=[(0xc0c0c0c0c0c0c0c, 16, 18)]) (hprior:=lowZ_57_2_16) <;> decide +kernel
namespace S_187
def pairsG : List (Nat × Nat) := [(1,9), (1,33), (1,129), (2,18), (2,130), (3,11), (3,19), (3,35), (3,131), (8,9), (8,40), (8,136), (10,11), (10,26), (10,42), (10,138), (16,18), (16,144), (17,19), (17,25), (17,49), (17,145), (24,25), (24,26), (24,56), (24,152), (32,33), (32,40), (32,160), (34,35), (34,42), (34,50), (34,162), (48,49), (48,50), (48,56), (48,176), (128,129), (128,130), (128,136), (128,144), (128,160)]
def r1sG : List Nat := pairsG.map Prod.fst
def r2sG : List Nat := pairsG.map Prod.snd
def mpG : Nat := 0x3ffffffffff
def pool6G : List Nat := []
def xsM : List Nat := roots_187.map (· &&& dom_187)
def goalM : Nat := goal_187 &&& dom_187
def NN : Nat → Nat
|4=>0x33
|5=>0x129
|6=>0x29a
|7=>0x149
|8=>0x34
|9=>0x7
|10=>0x1
|_=>0
def HT : Nat → Nat → Nat
|4,0=>0x7ce2c6df9d54a974f3b84bbc747e65404c83f33239ae4364612f3492aecf26f7f22f1122985219571e2041dda61cedc1b2a91b2541a36319fca17fe117c8d1622013ecf133fa0f6c60e72e0ceaa0c81e0c0160bfec0bc2e0b6ac09d6b065ca05874051cd03f6b03d6b039e803411033270319002c1a0284d028040201b01f44
|5,0=>0x13eea137b713780135bf13421133f312c5112c4b12ac8123b8123a9123a61232d1230b12210120ee11bb61146a1122d10f7110cdc10721105e3103b8101390ff050fa9e0f2860ecfd0ec9b0e67a0e2b10e25a0e0280e0020df410d4a90d49b0cbbb0c97c0c8e60c7200c4c80c4950c1220c0160bff00beb30be010bb870bac80b2f90afea0af7e0ab290aad00a6490a5250a51d0a43809e8809af209623093c009153090970907508d6608c5308946085e40846507f8407f6807e4307b3307ae307a7b078d5075e2075d307508074e9070aa0703706c3a06bac05f42053aa04edd04e4d04e3404dd304d57044d5042be040e403dbe038510376a03694036830357c033a20312d02c6c02a29029470260a024b301e2501dc401cda01a1d017f0013fd013fc0115f01106010ae00f4700df300bc200a8e009f700847005a100410
|5,1=>0x4f81c4e7c84e5b04d5a84d4ac4877947de746a66449ea4492e4456e434ee41b5440bb83f66a3eeea3bfc53ba4a3990a397de38fde371e336eed36be835faa35bba359263576534bef3498c346f432659319ac3165a3127730ec62ff372fcec2fada2f2772e7622e0452d57d2d3a52cd8f2cc232bc052b33c2aa162a32629a7a293e52917b28d9a28ae427f5b274ee26fc226f9d2644a2618925ab424fa2249c42343721eba21957213ff20f6e20a0f209962090720611203af202701ff0f1fc791fae41f8b21f1d61ee4c1ec0f1e62e1e2b21d2961d2011d18c1c7751c4d01c3d01c3371c1e61bf8a1ba9a1b95d1b0361a9401a85e1a44819d101931018d0f187f7187ca1879f17fe117fd417df41784316ea4168d3167c6166fd16659164cb161e315b9a15b2215aee159ec158be1508414f4b14b5a148071467c1454913f69
|5,2=>0xf605ebd89ab7a23b4899a15a18beff877468527784f0782d0d7834977df176da57250b71c786bd456b2496a02469b896903b689ea6822f6788b66fd365637613f860f135f4b85d5895cb6c5c9825c2855bcef5a84d59f6958ec9576685632453577534d552bcd
|6,0=>0x6321060aa0609905ee405d9105d3305cf805c8505b3a059e40576c055d405541054e8054960534a0530e052e5052e00529b0528f051f1050c8050600504b04ff704e2c04dd504da504d2404cd004afb04ad804ad3049f6049c4049c30491f048ba047290471b046ff0469d0463f0457904506041df041ae0410303dcd03aee03ad803aac03a0a039980378603694034ba033b3030980302602f4c02da502d7702d4b02d4902d2f02c7602c1702b61029880288c028680276a026da025c202542024820243202404023800230b01ff101f6901ece01e2501e0801c6601bd401bcd01aaf01a9b018c3017e50173e0170c01663015b70143d01416012900113200d9900d5e00c6d00c2700b3e00aa0009e3009d5009ba009af0089e00814005fc005f4005f3004df004b7004100039a00387003830035b0025d001ec001940006b
|6,1=>0x10c2a1047f102d5101550fff10ffbf0fe220fe010fda60fb600fb010fa490fa1c0f9ea0f8c30f8af0f7d60f6130f48b0f3aa0f23f0edf90edf20ea580e91e0e8f20e74e0e53f0e4940e2360e1f90e1f70e0ed0e03d0de8b0dcd40daf50d54e0d3a80d39e0d2e00d2810d2590cdc40cd340ca880ca000c82e0c77a0c74a0c6950c4b80c2f30c2a00c1280c0f40c0800c0210be170bb190ba560b9c90b9c80b6f70b6060b5ce0b2220afe70ace60ab660ab360a97d0a94a0a8e00a6490a6200a4540a2210a1ce09f9c09f2209e9d09e7009cda0991e0991509722095420939809172090ec090990909708f6908e6208e3708df408bf408b8208b7408a8d0896308715086a10825907fba07d9707d8d07d7607b3207adb078e6078880786c07869074e907109070600703906e5206c2e06c0306a10069800674d0644b063dc06352
|6,2=>0x1f0871edfd1e7851e74a1e7321e4be1de371dbcf1d3f31d2691d2081d1bb1d18c1d0541ce831ce751ccbb1cb841ca4d1c9761c6331c4661c0f41be221bc251ba4c1b95d1b95c1b93a1b7e61b4d71b1711b1451b1011ac531ac501ac3b1aada1aabc1a75e1a69b1a43a1a3e51a35c1a1861a17919fe019eb919cab19c1019a38196fc1932e1919e18d31189411890918880187c8186441830f17fe117d1217a1a1762c176211752c16dd416c9516a1f16880166fd1619315d3f15c1815b8b15b07159c0154da1513d14fea14b4d1480f14748145931432713fd613f6913f4d13e2513d7513c1013a90139f213745136b6136ae1362d131d6131c71319f130aa1308912e7812a5a129d91270b1267411f7b11ea411ddd11bf011b8f11b18119fb11800117ee117b91179c11784115f7111e3111b71114810f9e10f7110ee610e4a
|6,3=>0x327383259c31f2631d0f31a69316c4315da313b23137a312773103e30db0307f33067e3043f300da2f92b2f5242f2772ee302e8ed2e4e52e2862e18e2dd982dd3b2dc962dbb82db932da962cc132cb032c8de2c4c92c2182c1742bb4e2b97e2b8832b64e2b3a42b3102b1ad2afc02aeed2aa3c2a9d42a6822a23e2a20f29f7229e9729cef29c3b29a22298f6298ce2973a295f3294c8293c7292122919628e522870e28595278ef27807277912730726e6126d7326cde26b2e2674f2673f2623125c12259362586f2586b258412578c252b1251ae2510b24ee424e8d24daf2428023d0d23cc4236b7232bb22a7f2271b22656223e92233421fb621eba21e6b21d34216d42169620e5c20e3820d7920c64203dd202e8202cd2023c2020c200802006c1fd8a1fd4b1fc791fb681fae01fad51f9211f91b1f8d61f5a71f4a01f3ab
|6,4=>0x70db0701376ff0b6f3026e74d6d6ad6cdff6c5a06ad386a26b6982e695c568f5965090624ad616f56137a60edd607fc5cb6c5bcb35b5f75aea75abb45a29559ef75958a5947759373576c95732a55ef455ef355adc555c15486c53b5453577534d5523d451d8a51b26512584fd004f2404f1104e9fb4e3294dedc4c5904c5694c2414b6dc4911948e9648d92483ec48042478dc464f145c494597c4589d44ef744e9b44972448ef4456e4403843e9142aec422f74226941b54410b540aa5407e5400863fcb63f7943f7933f31a3ee4c3e4ed3dd9c3db963dab63ca073c07d3b5533ab9e399643951b38ff138e07389453871c3863838436381ad3814937d0537b16376ec3739536eed36af63698b3694f3694a36508362883617d3609b3607435f5735f4135d8035bb9358c53566634851347c833e1f33d273389d337fb32c47
|6,5=>0xee80acdf7ab60f6ac858a6577a317ba2b27a0e789f0419d2419a4289829f96aae8de6883b18829277e3a97b1b67ac3278ac376da57676174bc0731ff72730710fb
|7,0=>0x13b6c13a951381b132d8131ae12e6512674120541200e11324111f01043b101b60fff10fc430fa300f9c60f5120f4ff0edb50e5c20e36c0e1250e04d0deb00dc260dbb00db200daf50d6e50d5120d2630d0290d0280cedf0cd430c8540c5370c4a80bff30be5c0bd2d0bbff0b6fd0b4c30b2010ad8f0a6f60a6200a4540a4230a2ec0a2e60a1ce09cd909ad4098de0958c0940f093350925f090da08da908b0b08374082220796b06ff50672e065c3064520639a0632f062a406223061920609a0602505f7405ce505a520579f056f8056380500304fd104b12048c5045a5043dc04304041ae03be903437033b30333502e9102d2f02bf002b2e02a4b0299102860026c20245b021710201601fc801d8601953016450151b00d5500be200b3e00b2a00a9700918008bf007dc007c7005f3004f0003fb003c60037f0020500063
|7,1=>0x3d2413c63f3c3643c0f73b53b39e5539e3739ddc38f433611931d0d31aa43148d3127730ee3307f330468300da2f9242f8e92f7182f41d2f0c62e26d2dc712da312d5ac2b48f2a95d2a64929a222956b290dd28e2628c2f28a86285a027e1b27841275202748f273d1272ac26fe726bb4267e42623125cb625ac425926254ca24c8c24b5523930231972308223058229be226a2221ad21eba21b2e21ae321958216962125720c611fe3f1fd8a1fc791fb4b1f4f01f4a01f11f1efcb1e5a41e44b1dc1c1da0c1d9d01d8d51d4751d0ae1cd841cd6e1c16e1bbcc1b69c1b6111b2371acdf1a8f91a10619db819cf119c79189ed18802187c8186501844117f6b17c67176c1175a31749e171e4170c21707716a0f169531674a164b11648c15b2215adc1595a154ae153bc14ebc14e8114a86148651466d1445a13faa13f7413e42
|7,2=>0xc99cdb674bb4cc2b0e65aebd2a3c65a2b279d24197433926218b4a37fe347cf8c79bb4760d1755ea74b017262c713aa701376e74d6d6ad68d5064df5624ad60edd60e5b5e2075dde85c86a5bdd4596b35887b5731956e36566ac55edf54e4c532d652dd05149e509ff4ee714ed594dbfe4da964ca8e4c67a4ad414a68f4a610478f64533d44ef744c414419043ff643e91436a7432bd42b6442aec42a84429f4412cb40f0740d173ff743fc203f6b23ed693ebad3e444
|8,0=>0xab2548cbdc737657038b6b73c6b09e624ad60edd603855031a4de524ab1749c7d49b9046f72442fd3e9a436ba635b6e3080b296d128d8b284ad273bb26312261b82536f22cbd2271e224f5220191daee1c0d21bc581b33b19a4816bc514ae212cae11517114e70d0fb0ad290a02a080960597c0582503dcc031ad02c81022f6012ee
|9,0=>0x8008144c572fdf81cead17b0011d0205e24
|10,0=>0x5e24
|_,_=>0
def dictB : Nat → Nat → Nat
|0,0=>0xccfeccfeccfcccfcccffccfeccffccfefffffafaf0f00000fafafafa00000000ffffffff00000000fafafafafafafafafffffafaffff0000fffffafafafaaaaafffffff0ffaaffa0ffffffaaaaaaaaaaf0f0f0f0f0f0a0a0f0f0f0f0f0f0f0f0ffffffffff32ff32fffefffeccccccccfefefefef0f0f0f0fffefffeffa0ffa0ffffffffaaaaaaaafffffafaf0f0f0f0ff33ff32ff30ff30aaaaaaaaaaaaaaaafffffefeccccccccfffffffaff00ff00ffffffffffff00000f0f0f0f0a0a0a0affffaaaaf0f0a0a0ffff0000ffff0000fafafefeaaaaaaaaccccccccccccccccff00ff00ff00ff00fffffffff0f0f0f0aaaaffffaaaaaaaa0000fffa0000fffa
|0,1=>0xff00ff00ee00eea8a8fcfca8a8a8a8eeeeeeeeeeeeeeeefffffcfcaaaaa8a8ffffaaaaffffaaaafffff0f0fffff0f0ffffffffccccccccffcfffceff00ff000f0f0f0f0f0f00005555555555550000fffff0f0aaaaa0a05555555555555050eeeefefeaaaaaaaaffffaaaafafaaaaa00000f0f00000a0afffffafaaaaaaaaafffffffaffaaff00fffffff0ffff0000fffffff0fff0ff00fffffff0fafa0000afafafafaaaaaaaafffffffaaaaaaaaaffff5550ffff0000000005005500ff000000ffff0000fafafffffcfcf0f00000fcfcfcfc00000000fcfcfcfcfcfcfcfcfffffcfcffff0000fffffefefafaaaaa000500055555505000cd00cdff32ff32
|0,2=>0xff33ff22ff33ff00fafafafafafaf0f00f0f0f0f0f0f0a0a3303330333033302ffaaffaa00000000ffaaffaaffaaffaafffafffaf0f0f0f0fffffffafffff0f0f3f3f3f3f3f3f0f0cfcfcfcfcfcfcccceeffecfceeeeececfffffafa000000000000f5f50000fafa0f0f05050f0f00000000ffff0000f0f0ffffffccff00ff000000fafa0000fafa050505050f0f0a0afffffffa00000000fffffffafffffffafffffafafffffafaffffffffff00ff00fffffffecccccccc0000000a0a0aaaaaaaaafefeaaaafefe0000ffff0000aaaafffff0faffff000000000404ccccccccccccccfeccccccfeccffcceeccffcceeffff0f0fffff00005555010155555050
|0,3=>0xa0f0a0f0a0a0a0a50555055505050500000fbfb0000fafaf0f0fffff0f0f0f00000f5f50000f0f0afafaeae00000000ccffccfcccffccfcf3f0f3f3f0f0f0f0ffffafaaffff0000fffffefe0000fafa0000ffff000000000000000f0f0f0000fffafffa00000000fffafffafffafffafffafffaaaaaaaaafff0fff000000000fff0fff0fff0fff00000fffa0000aaaafff0fffaff00ff000000fefe00000000ffffaaaa00000000333333313333333000000f0f00000000fffff0f0aaaaaaaafffffffffafafafafefefefeaaaaaaaaffffeeee00000000ffffeeeeffffeeeeffffffeeff00ff00fffffff0f0f0f0f05555505055555050aaaaafafaaaa0000
|0,4=>0x11110000aaaaaaffaaffaaaaaaaa00ff00ff00000000aaffa0f0aaaaa0a0aaaaafaff0f0f0f0000005050000aaaa11111111ffffaaaafafafafafafa00000f0f0f000f0f0f00030303030000f0f0000055550f0f00003333323230303030ffffeeeef0f0e0e000550050005500503333303033333030f5f5f5f5f0f0f0f00f0f0f0f00000000ff33ff22ff33ff22ffffffeeccccccccafafaeaeafafaeae0505050500000000fffff0f000000000ffffffaaffff00000f0f0f0a0f0f00000000ffaa0000f0a0fffffcfceeeeececffffaaaaffff0000fff5fff0f0f0f0f000ff00ff00ff00fcaaaaaaaaaaaaa0a0ffffccccffffcccc1111111111110000
|0,5=>0xffffffffffffaaaaf0f0f5f5f0f0f0f0cccfcccecccfcccefffffffaffffff00fffafffaff00ff00eeeeeeeeeeee0000ffffffffffffcccc00ff00ff00ff00ccfffffff000000000fffffff0fffffff0ffffff00ffffff003333333333033302000000ff550055aafffffffffffff0f0fffffefeffffaaaaff0fff0aff0fff0a000005050000f0f0fcfcfcfca8a8a8a85555444455554444dddddddddcdcdcdcfffffefef0f0f0f0aaaaafafffffaaaaffffeeeeffffe0e000ff00aa00aa00aa5555555500000000ffff5550ffff55505550555055505550ffff555000000000fffffcfcccccccccffffcccc00000000fffffcfcf0f0f0f0ffffeeeeffff0000
|0,6=>0xffffffffeeeeeeeef0f0f0f0ffffaaaa0f0f0e0e0f0f0e0e3333333333003300fffffffffcfcfcfcfefefefefefefefefcfcfcfcfcfc0000fffffff0ff11ff100000555500005050ccfeccfeccfeccfeeefeeefeaaaaaaaa515151515050505000ff00ff00cc00cc55555055555550540f0f0f0f0f0f0f00505055555050505000000000ff32ff3200cd00cd00000000aaaaafaf88888c8cbbbbbabaaaaaaaaaffaaffaaffaa000000000500ff00ff00ffffafafffff0000fafafffff0f0f0f00f0f0c0c0f0f0c0cffff0303ffff00000f0f0a0a0f0f0a0a3322333333223332330033333300332205050505050500003322332333003300aaffaafaaaffaafa
|0,7=>0xff30ff20ff33ff2200cc00dd00cc00dcffff00fa00000000f0f0b0b0f0f0a0a033010000ffff0000fffffefe00000000fffffefefffffefefffffffeff00ff000f0f0f0a0f0f0f0affff3232ffff3232555505055555000000005555ffaaffaaffff0f0fffff0a0affffff000000000000ff0000fafa0000fcfcfffeccccccccff33ff32ff00ff003333333333333330000005050000000000000000fefefefe33333333323232320f0f0f0f0e0e0e0e33103311331033105555555555555c5c00cf00cf00cc00cc0000fcfc0000fcfcfffffffaffff0000fffff0f5aaaaa0a000005555aaaaaaaafcfcececfcffecee5555555550505050ffff0000fafa0000
|0,8=>0x3311331133113300ff32ff320000000011111111555550503333333333330000ff00fffa00000000aaaaa0aaaaaaa0a8ffffffaa00000000ffffffaaffffffaafffffffaf0f0f0f0ff33ff30ff33ff30ffbbffbaaaaaaaaa0000ffff0000ccccccccfefeccccfefe5555545455555050f0f0f0f0f0f0f5a000000f0fffff0000ffddffdcff00ff0000ff00ff00fc00fcffffeeeeaaaaaaaaffffffccccccccccfffffafaaaaa000000000055ffff0000f0f5f0f5fafafafaffffffff55555550ff32ff32ff32ff3233333333333233320000555500000000fafafffffafafafa00ff00ff00ff00feccccfffeccccccccffff5555ffff5050aaaaffffaaaafafa
|0,9=>0xffffffff555550500f0f0b0b0f0f0a0adddddcdc00000000aaaaaaaa55555050fffafffafffa0000fff05550fff00000ffffffaafff0ffa0ccffccfccceeccecaaaaafafaaaaaaaa0a0a0f0f0a0a0a0a00cf00cf00cf00ceff33ff32ff33ff00eeee0e0eeeee000000005555ffff00005555555555555550fffcfffcff00ff00aaaaafaf00000000f5f5f4f4f0f0f0f0fffffefeaaaaaaaafff3fff2ff00ff00ffff00000000fafaffff5555ffff0000ff33ff32ff22ff2200000f0ffafafafaaaaaaaaaaaaaa8a8ffff0000fafafafafaff0000fafa000000000505f0f0f0f0cccc8888ffffaaaa3333333300000000ffffbbbbffffaaaafbfbfafaaaaaaaaa
|0,10=>0xffff00faffff00fa00fa00fa00fa00fa0000ff0500000000ffffffff0f0f0f0000ff00fffafafafaff00f000ff55f050fffffdfdfffffcfcfafafaaaffffffaa5555545455555454fffffcfcfffffcfc555554540000000000005550fff0fff0fffffefeeeeeeeeeffffafafffffaaaaffaaf0a0ffaaffaa00000505aaaaaaaa00000505fffffafaff33ff00ff33ff3200000000ffffaaaa00000000fffffafa333332323333323200ff00fa00ff00fa00000f0f55550a0affffffff0000fafaccccccccccffccfe0f0f0a0a0a0a0a0acfcfcfcfccccccccffffccccfafac8c8ffffeeeefcfcecec05050505f0f0f0f000ee00ef00ee00ee00000000fafafafa
|0,11=>0x323200003232ffffcdcd000000003232323232323232ffff32320000000000000000fffffefe551155105511551000000000555544440e0e00000e0e0e0e5555555555554444f5f5f5f5f5f5f4f4bbbbbbbbbbbbaaaa0000545400005454cfcfcfcfcececece00cf00cf00ce00cefffff0f5ffff00000000ffaa0000ffaa33333333333330300000005500000050fffff5f5fffff0f03333333330303030bbbbbbbbaaaaaaaaccccccccfefefefe0000eeee0000e0e0ffff3333ffff3300bbbbbbbbbbaabbaae0e0e0e0e0e0eeee00000000ffaaffaafffff0f000550050ffffffff00ff00f0ffff5454ffff545454545454545454540000abab00000000
|0,12=>0xfffffffffefefefeffffffff0000ffaa00fa00fa00fa00000f0f0a0a00000000cfcfcececccccccc00aa00ff00aa00faccccddddc0c0d0d000000000f0fff0faeeeeeeeee0e0e0e00f0f0d0d0f0f0c0cfdfdfdfdfcfcfcfcfffffffffffffff0ffffffff00000f0a00ff00f000ff00f000000000eeeeeeeef0f0f0f0fefefefefffff0fffffff0f00000f0ff0000f0f00000000000005550fbfbfbfbfafafafaffff00ffffff0000ffffffff0f0f0a0a00ff00ff00ff0000ff0fff0fff0fff00ffff0303ffff0202000000000000fffafefefefefefef0f0ff0fff0fff00ff00fffffffffffffafa0f0f0f0f05050500ffff0000fffffffaffffccccf0f0c0c0
|0,13=>0x3333333333303330fffffafaffffc8c8c8c8c8c8fafafafaff00ff55ff00ff003300331133003300ccccffffccccfcfcfffffff0ff00ff00ffaaf0a0ffaaf0a0ffffffffffaaf0a05555505555555050fff0fff0fff00000ffff3333ffff00000f0f03030f0f000000ff00ff00f000f0ccccccccccffccfcff00ff00fffafffaaaaabbbbaaaa000000ff00ff00aa00aaf0fff0fff0faf0faffffffff0f0f0f0a0505050005050500f5f5f5f0f5f5f5f0fafffafffafafafa0000faff0000fafa555555551111101003030303030300005555555555005500ffffffff00ff00faff00fff5ff00fff0aaaaaaaaaaaaaaa00f0f000f0f0f0000f3f3f3f3f0f0f0f0
|0,14=>0xffffff0fffffff0000ff000f00ff0000eeeeeeeeeeeee0e000000f0f00000c0cfffffffffffffcfc55555555555554543333030333330000ffffffffff33ff30ff00ff00ffffaaaaffff0505ffff0000ddddddddddddcccc00dd00dd00dd00ccff00ffffff00fff0000000ff000000f0eeeeeeeefffffefeffffffffffffff00555555555555550000ff00fa00ff0000aaaaafafa0a0a0a0eeeeeeee000000000303030303030202777775753333303033333232000000000a0a0a0a0f0f0f0a00ff00fa00aa00aa33333030333300003333333303030202ddddddddccccccccffaa0f0affaa0000aaaaaaaafffff0f0ffff5555ffff44440f0f0f0f0f0f0e0e
|0,15=>0xafafafafafafaaaaffffffaaf0f0f0a000fa00fa00000000ccfeccfecccccccc0055005500500050f0f0f0f0fffffafa30303030333332323333303000000000aaaaaaaaaaaafefefffffffccccccccc00000000ffffffaa0000ffff0000eeeef0f0f5f5f000f50000003232fafafafa0000fff00000f0f000000c0c44444c4cfafafafafafafa00050505ff000000000000eeee0000eeee1111101011111010ff11ff10ff11ff100000333300000000f0f0f3f3f0f0f0f0fbfb0000fafa00000f0a0f0a0f0a0f0af0f5f0f5f0f500000055005500550044f0fff0fff0fff0fa0000ffff0000fefe00000000fff0fff0f0f0f1f1f0f0f0f0ffffffffffaaffaa
|1,0=>0xaaaafffaaaaafffaff55ff50ff55ff50ff55ff500000000033332222333322220505050505000500afafafafafaaafaacccccfcfcccccccc0000333300003232ffffaaffffffaaaa0f0f0a0f0f0f0a0affff3333ffff222233333333222222225555111155550000fffffffffffafffa00000000fffafffaf0fff0fff0f0f0f0ffffffffffff5550ffffaaaaf0f0f0f000ff00aa00ff00aaf0f0fffff0f0fafaffffddddffffdcdc3333333333223322ffff3333ffff33220a0a0a0f0a0a0a0a1111111110101010aaffaaffaaffaaaaffffffffffffeeeeeeeeffffeeeeeeee00ee00ff00ee00eedddddddddddddcdcfcfcf8f8fffffafa0000dddd0000dcdc
|1,1=>0xf000f050f0f0f0f0fffffcfc000000000f0f0f0f0c0c0c0c00ff0005000000000000ffff0000fcfc00000000ffff545400000000ff00fffaccccddddcccccccc0f000a000f0f0a0a0f0f0f0a0a0a0a0a0000f5f50000f5f0ffff0505ffff0500fffffffff3f3f2f2ffffffff00fa00fafffff5f5fffff4f40000232300002222333333113333330000000000ffffccccf0f0f0f0fffffcfc00cc00cf00cc00cc00000000fffff0f05555555055555550aaaaaaaf00000000fffffffffff0fff0ffff0000fff0fff0555500555555005005050505ffff0000f0fff0fff0fff0f000000000ccffccee0000cccc0000fefeffffffff030302020000333300003030
|1,2=>0xfafffafffafefafe5f5f5f550f0f0f00fffffffafff0fff0000000005555505000f000a000ff00aa0000aaff0000aaee000000000000fafaff00ff00ff00fffa0fff0aff0f0f0a0af3f3f2f2f0f0f0f000003333ffff0000eeeee0e0fffff0f00000ffff0000fffaffffffffffffffaaf0f0f0f0f0f0f0a0ccccffffcccceeeeffff00ffffff00f00000fff00000fff0ff33ff32ff33ff320000afaf0000aaaaaaaaaaaabbbbbaba0101010100000000f1f1f1f1f0f0f0f00000000055505550ffffffff555055500000fafa0000f0f0fcfcfdfdfcfcfcfc00dd00dd00dc00dcff00ff00fffffffaffff0000fffffafaccccffffccccfefeffffaaffffffaafa
|1,3=>0xaaaafefe0000000005000500ff00ff00fffff3f3fffff0f0aaaaa2a2aaaaa0a0fff0fff0aaa0aaa0fffffefeffff0000ffffffffcfcfcecefafafafaffff0000ffff3131ffff3030fcfcfcfc000054540000555500005454fffff5f5ffff0000555555005555550000ff00af00ff00aa0000bbbb0000aaaaf0f0fbfbf0f0fafaffaaffafaaaaaaaaaaaaa0aaaaaaa0a0ff00ff5500000000f0f0f000ffffff00ccccffffcccccccc00cc00ff00cc00ccfefefefe0000000001010000ffff00003333333333333232aa00af00ff00ff0000ff00ff00ff00f0ffffaaafffffaaaa00ff000500ff0000ff00aa00ff33aa22f0f0f5f500000000fcfcfdfdcccccccc
|1,4=>0xf500f500f000f0000055550000444400af00af00aa00aaffaaffaaf0a0f0a0efefefefeeeeeeee0000fffffafafafacccccdcd0000000000000505000004040000010100000000ff00fa00fffffafafefeccccfefefefe0000505500005050fffffafaff00fa000000000000ff00fa00000f0ff0f0f0f0ffffffff00ff00aa0e0e0e0e0e0e0e0efffffffffffffffafff3fff2fff3fff2fffffafffffffafafafa00fafafa0000ff00ff0fff00ff0af5f5f5f5f5f5f0f055555550505050503333333333332222ffffaaaafffffffaf0f0e0e0ffffeeeeffffabab00000000000f000f000000005555555544444444aaaaa0a0bbbbb0b0ffeeffeecccccccc
|1,5=>0xfcfca8a8fcfca8a8ccccccccfffffcfc00ff00ff00fa00fa0000555000005550ccccc0c0fffff0f0f0f0f0f0fffffff0fafafafafa00fa00aaaaa0a0fffff0f0ffff0055ffff00000000555500005500eeee0000eeeeeeeedddddcdcdddddcdc00000e0e00000e0e030303030202020200000000ffffff00ff05ff05000000000f0f0f0f0f000f0003030000ffff0000ff00ffffff00ffaa00000055000000000055005500000000f0f0fffaf0f0fffaffff111100000000ff55ff55ff00ff003311331133003300aaffaaffaafaaafa0000111100000000f0fff0fff0fcf0fc0000000000fa00fa000000000f0a0f0affff5555ffff5500fff0fffffff0fff0
|1,6=>0x5050f0f0f0f0f0f0a0a0ffffaaaa
|_,_=>0
def scatter (v : Nat) : Nat :=
  let lo := v &&& 0xffffffff
  let v := lo ||| ((v ^^^ lo) <<< 96)
  let lo := v &&& 0xffff0000000000000000000000000000ffff
  let v := lo ||| ((v ^^^ lo) <<< 16)
  let lo := v &&& 0xff000000ff0000000000000000000000ff000000ff
  let v := lo ||| ((v ^^^ lo) <<< 8)
  let lo := v &&& 0xf000f000f000f0000000000000000000f000f000f000f
  let v := lo ||| ((v ^^^ lo) <<< 4)
  v
def stPkD : Nat → Nat
|0=>0x392fc4b0e83b0680f024020501b0180c00c04
|_=>0
def stPkT : Nat → Nat
|0=>0x6ff1630f104ff057ff206ff0162f107ff0136f0162f058ff108ff106ff0163f3520f3861f6721f106ff0672f017ff352ff308ff38f0f362ff107ff103f6016ff
|1=>0xf1085f107ff108ffef52f1083f10f4f32f5f016ff10ff60216f127ff0672f13f8681f5f1063f106f810f8f380ff16f3f1f63f127ff10f6f32e5f1072f10fff01
|2=>0x1524f10452f106fff20175f031f801623f02354f10583f10f85f15423f10362f3106ff532ef017f2910627f52470f1034ff3241ff0183ff2143ff35412f10385
|3=>0xf381f5f5324ff103f4f105f3f13628f1036ff0185ff01853f15742f1045ff03214f3540ff10279f51f7f83041ff10452f1385ff103f2f1042ff1035f82314ff0
|4=>0x75ff216f715234f108a5f1072ff10f58f5108ff03941f10326f10583f51083f1362ff1026ff05f78f21036f10257f0354ff138f0f10385f15ff78012f67170f2
|5=>0xf058f375183ff4302ff013f6103fc832415f50342f10bf891f7f2f10632f08751f1026ff31ff4613f45f10234f10572f10853f50781f104f5f1036ff0123f610
|6=>0x62f750ff80354ff1024ff10f72f104f2f10987f12453f52817f104ffa10f62f35241f01f63f5018ff1507f82671f06712f102df6012f4f105f87153f48058f1
|7=>0xf1054ff53f80f1032ff1038ff39861f2107ff1260ff1f762f216e3f02435f10785f3514ff3140ff3540ff01f62f0341ff1075f84205ff3520ff1f435f15403f1
|8=>0x72f10af46104fff01f72f05241f12354f32405f23541f10863f1fe32f3152ff109f73124ff43521f10bf6f13540f32f40f103f8602691f01435f103f5f32415
|9=>0xf12534f34621f13254f1045ff32450f10672f32450f1026ff0521f7103f4f13240f10a7f6032f5f5214ff03524f01875f1260f731f45f10f5ff50381f1094ff1
|10=>0x2d1f3504ff1524ff15204f106f8104f5f03241f105f2835204f2b760f1057f810a4ff1075ff1452ff03241f1057ff05127f30185f0153ff3524ff104afb02354
|11=>0x105f3f5240ff0241ff10324f1096f71072cf3240ff1b940f1b940f13054f51f7f854831f3520ff105ff813540f1027ff1270ff10ff2f052f3f3540ff1034ff03
|12=>0xf12f45f5107f801534f5ef32a10672f1084ff10324f1086c71052f715724f32054f10524f10af69354f0f10342f10362f10ff7610ff8901863f13540f532aff
|13=>0x35ff1324ef15720f3186ef106ff10f4ff10bff81078ff1035ff10672f0f452f01623f03245f10b4ff2104ff35421f58471f107f2f1035ff1043ff32450f5243
|14=>0xf1098f71052ff1086ff32415f10527f10785f1324ff10725f1f432f104aff5241ff10742f1024ff104fff206b1f102f3f01752f571f2802354f107f5f102fb71
|15=>0x103246f10563f8012354f10358f3254ff10325f3254ff10ff56104fff10ff28a9b40f1032ff1049fb52430f1032ff104d9b1032ff16720f4032ff10542f1034f
|16=>0x3514f501f83f102756f108f53f10372ff105234f052134f31584ef105f4f021f67201354f305241f035421f10385f105423f013452f105324f015324f1354f0f
|17=>0x104632f342850f501f72d012543f013f45f13540ff012453f10542ff21b760f51f7f2f513a4ef3152f4e102453f5413f2f104853f05241ff102435f012435f20
|18=>0x3245f012543f21345ff01f472f103f28f1042f3f103524f152034f310246f103524f43502ff15f342f10672f01f725f102435f2106f7f3018f103425f51f472f
|19=>0xf10562f7105ff283102f4620541ff015324f15240f20541ff103254f2043f5f1f62f37105423f012543f01f524f102435f032f41f105243f1032d6f02ff43f01
|20=>0x5321f132045f012453f032154f31f42f432a51f10246ff103425f13f425f10362cf201f6f7105f2f7215437f012354f10a75f10354ff105f83f0571f281027a5
|21=>0x2f3152f0f10f562f1027ff032514f042531f013456f2135f4e20341bf2034b1f205437f215f70f105483f13b402f3124f0f0234f5f052431f03f524f13245f04
|22=>0xb40ff012fb67203f61f23541f03f524f150247f103bf2f132f64e30421ff012354f1045f3f537028f401329f3145f2f05241ff102af56135042f21f475f0354f
|23=>0xbf15f423f102435f34512ff40125bf1054fff152403f105bfa813a540f53241f21560f7035f428012354f31f845f035412f05241ff0a9b41f05f2f4720163f21
|24=>0x34a1f01f725f135042f132405f013425f105f83713254f152934f0354f1f102a7f6215470f3b2940f132540f153f42f012453f10f2f47210f7f6103752f10542
|25=>0xf20453ff102354f210756f50a471f1085f3f3124f0f10234f103542f10324df0541f3f1052f37052431f10364ff103426f10863c13f425f1024f3b13240ff50
|26=>0x514830f1035f2f54203df1354f0f1029f4721f45ff23504ff31860f503241f034f25f1024a5f102493f10f462f50183f10f524f01f672a1037f2f012f45f5432
|27=>0x75f012543f50342ff032415f102456f109643f102437f10276ac13245ff054f32f132405f102f4ff54320ff51234f30f628f20453ff102354f1025ff712f435f
|28=>0xb01f632a05241ff1024aff201463f135428f1054f3f013452f210f67013524f103bf89103f85f40235f102f63701f853f10385cf10b742f1034f291402f5f10a
|29=>0x632f103f62f301485f132450f13540f105432f1f4632f235b14f0523f4f5027a1f10472ff315240f5102f47032415f32415ff103bf2f103452f154e32f102f46
|30=>0xf10324fc13a940f1052fff059431f513240f1035f2f50243f13540ff132405f145203f4152f3f10435ff012345f013f45f10b672f35241f104df5b102f5ff10f
|31=>0x4af5b103948f1450f2f1054ff105fa481057b2f53481f1024d5f3152f0f103452f1094f3f35602ff51243ff013425f3154e2f10524ff1023f4610385f134529
|32=>0xf0132f46035214f320f4561024a5f1450f2f21543f10f324f305419f21354ff02ff35b103524f03241af514803f50a871f301256f0241f3c015234f103245f1
|33=>0x45132f10462ff105243f2043f5f51038f1f4e52f103af56508471f53214ff152403f51f7f481052f37025ff470413f5f1027f105324f10a8f5f2145f3f1a9b4
|34=>0x25ff1430f2f5423f1f10362f20b41ff2354f0f1345f2f3041f2f2354b0f5108ff7104f9a104f63f1062f37135f24f1270f5f015324f205613f21354ff35204ff
|35=>0xf10324ff1023ff613254f102493f1087a5c052413f13254cf10324ff40931bf132054f1054aff0521f3f135402f10943ff10437ff31f426f13240f103452f413
|36=>0x13f1096f3710a4f5f21560f7105234f210756f1032f5f103542f10524f7052314f15f324f032415f0134f5f102f45f21f7e56105493f03f524f041253f5032af
|37=>0xf152430f302691f10b42df1034f29319860e032451f035ff4803241f15240ff10a8756130f42f05f324f40321fc03241ff5104f8f12034f123f45f10324f0524
|38=>0x54fff105324f102f7565240f3c02435bf1032f5f03541ff034851f03541ff154720f34520ff359480f1085f37032541f10345ff21346f104f52f1052f4710524
|39=>0x10943ff0324d1f15f423f2053f4f10f324f105a48f0153f4843250ff105f72810752ff0524f3f034612f103542f1035f48135402f312490f301528f102463f10
|40=>0x32451f5402f3f105237f052431f103ff2f103462f31048ff032415f1034af920354f132405f10275f31524ff5187a0f51207f50f7f8102435f052491f30f8f56
|41=>0x853a840f104bfa9132540f35240ff1420f3f013542f13240ff1054b2f10542ff3109f460324f5f032a54f015324f0324a1f1035fc813240ff10354ff035421f0
|42=>0x2a76f10342f10b728f13254cf513240f35204ff0354f2f052431f53240ff03241ff10543f10394f1032fc6102745f102475f5032d1f05241ff521f43f1035f4
|43=>0x1f56130548f02f345f103624f529430f43250f152904f1354f2f10324fc152430f0f63f2f03542f03541ff1024fff13542f015432f41b09fa104752f10325ff1
|44=>0xf31049ff051f847105324f105432f10483ff10254ff01543f02f475f1024f5f1054f2f032451f140235f035142f103528f103628f0351f480312f603541ff032
|45=>0x324f052f43713540bf103245f10ab6810632ff305f42f102543f132405f105237f03f524f105493f10b672f105f83d108475f1052f4f142503f210745f104f72
|46=>0x32f102345f105243f10342cf102f75f10345af03245f0123f4f51034df301254f105324f235f40f2104ff014f32f104afb9135402f10324ff029341f352ff105
|47=>0x2135ef103624f105ff28108463c03254ff035b14f309681f052413f035421f3109f6810a475f013452f51f472f4325c0f10254f1034bf95104fdf10a75ff0154
|48=>0x4632f10324ff105947f109683d125f43f10324ff03254ff012354f510f781034f5c10523ff10b948d43205ff102fb71035ff032541f032415f105472f104bf29
|49=>0x5f104835f352f40f1032af610f435f103f42f1032df6032415f319640f103524f032415f30524ff315204f10549ff10247f21034f032456f10325ff0321f5610
|50=>0x2405f132405f10ab64810325ff10a45ff1054f2f10325ff104d9b3240f5f10f432f013524f032415f152430f10325df1032d5f032415f5104aff105249f10324
|51=>0x43ff215b740e302ff4560124f35b31452f0f2104ff10324ff10324ff10354ff2354b1f105243f103254f1054bff10a485f105234f132504f528037f10325ff13
|52=>0x4630425f1f15f3f42f1054bf2a513240af1053f2f304521f1529430f203514f5120f43730f462f3012456f1529403f3102f4561205f47021354f5102437f1029
|53=>0x5f201543f10354ff0152f43f103245af103254f2043751f2035bf4f105243f103245f3024691f10435f2f410235f503241f310549ff1023f45f210f463f3102f
|54=>0x103b6428305241f20541f3f301245f302f45f0135f428104532f51430f2d02413f5f301f462f132a450f504123f21560e37312456ff10423f5f10529f37310f8
|55=>0xf437514302ff314520f03b2941f35421f510a8710f4632a51034ff13240f5f104523f3045612f51324a0f32405ff3105f483152f40e513f42f1054f3a403251f
|56=>0x52941325c0f10425f3f3142805f50431f2d013f524f1059483d4032f5f4032a15f150234f103542f10324df502a41f5032d41f31028f61052f3730415f2f1520
|57=>0x4f35b5102f730281f56103f5948103b62f1059843f21354f0f104372f214350ff103485f10324af3124e5f21450f3f401235f210345f0513f48012f435f13f4e
|58=>0x3f529f504231ff510243f1053f281052493f10324adf503241f5120f7105243ff315240f5137402f1053f42f1325f4e1029437f3152fe105f283f501f728012
|59=>0x541f2f213b40ff1034f52951370f2810452f3f352841f3025f4f1024af5b1035f428305214f203f45f50341f2f503241af135b402f21054f1025f3f012f453f4
|60=>0x52f373129460f503241f510243f20354b1f413520f10435f2f1032a54f32054f410235bf51430f2f3105428f103254cf3015428f310f45f210354ff0234f5f03
|61=>0x302f456f1032a54f1045632f512f47f0521f43f10354b2f10324d5f104563ff5132d40f213b460f1035428f1032456f501243f1032456f31524f0f21354f0f10
|62=>0xf2910562f3721034bf305241f21034f10324f304125f5142830f103542f1032f456103542bf1032f4f50412f3f2105bf47510483f103542ff105f324f103a45f
|63=>0x213f10425f3f03241f5c201345f30561f2f510a48f104235ff352941f102f354f213540f1042853f5104f72d3129640f10524f210543f210345f510483df1034
|64=>0x820354f5032a14f10563f281029b4730415f2f301245f310f845630528f4f30542ff512470f103a45f403f52f52134f31524f0f31098461032ac46103542f405
|65=>0xff10324f513240f513240f213540ff315294ef1056283f312f64e310462ff102f37561035bf2f324560f213540f1029637412a50bf4013529f21034bf51370f2
|66=>0x1352f310549ff3152904f1032f4561023f456103542f13b2940e352940ef204513f103254cf1032af5f41320f5c104562f10348a5c510437df102835ff354280
|67=>0x105472c105243f104375ff5107f2843520f51034df2104f63f401532f103245f031254f2035f41f401f52f1052f43f51324a0f30281f5f1035f4281052493f40
|68=>0x50324ff103b462f410532f40325c1f130254f30524f1052437f31028f461052f43710283d5f105623f10425f3f213540f3052491f103245ff1032a46f1035f2f
|69=>0xf310462f1032d5f105249f103245f105249ff104325ff210354f310524f1034f5295012f43710524f3f410352f02f5f437012f354f13240e5c103245f103245f
|70=>0x6103254cf1032d45f103254cf103254f10375628103254f103254f103542f1056423f10324f213540ff10324a5f410a9b10354f2c10563f2f10524f3c4132a50
|71=>0xc42035b1f512403f315420f3150f4835240f5032a41f21037456312405ff510432f2015f4374105293c3025f4f2104375f5124370f310562f310425ff1032ad5
|72=>0x3f5294103a59512034f3025641f402135f510324f3105f42f415023f305412f3102f5f3152840e5103a48302451f5132a40f210453f431520f3102845f410325
|73=>0x51037281035b428305124f1052943f410325f210354f310524f302154f35240ef3054281f4152f3f210354bf302154f510324af31524ef3104285f210354f401
|74=>0x431502451032a315240e315042f3120456430215f305241f431502512047f
|_=>0
def stPkH : Nat → Nat
|0=>0x22f0c4552089309108221c3042da084c11080820c4240e18800c8fe211f9083e8607bb40f5821e6223c20c77060eb911d2823a01073088e3891c408382406ee10dc081b442360286b900d5821a7103446067310cd10198203291063aa0c61018686304c05fc80bd41178082e8445ba18b608166622c80858840ae641570c2a82054900a78214a3028990504109f08138c426a084c30096821271424460475108c82114302218043410841810442202083f2807c600f30c1dca03a30872060e2101b88c364106b200d2821a0103348064410c418180882f8105e080b6c2162182b0c055200a70813d8c26a404a4a08ea211260209183f0907a140ec441c8a03565066900bf28170802a9c04ec20946010e301f1103b080688c0c0c015c20282004a1007b080d180138c0194401c600043
|1=>0x4260484821088420f2141b048286503c1a04984061080184ff811fd183f8027ea08fc0c1f6213e9087c860f8301ee823da107ad80f4511e6183c8c078618ef1c1dc223b50476480eb911d5883a63074880e8411cd323938c71c30e2981c2513820870040de619bb04372226d90cda061b310360926bc20d6891ac01354186a440d4011a70434c2069110d10a1a11033c98670c0cd881984332c28650c0c8e09900831e2063304c5821891230f0261430c1b0180432fc185eb44bba19750c2e8205c30cb78216d422d7045a880b490167842ca3058984b04115e182ba4056a18ac0c157402ab0455020a9109508229e1053484a5c21492828e4251428a18c14220281084f5249db01388626c224cc1c98921301025c824b410958a1284324e204958091451200923c44474088e0411aa0
|2=>0x5c890b8a0570032df045b870b6c416d402d8415ae08b58816a04ad3105a440b430166ca2cc0459430b220563902c49158604b045160202be3057842aed015cc0ab70a56a18ad08159092b02155c84aae4554862a80854e20a948552802a38154404a80914f8429e1053742a69014bc8a960452a10a504149902904951e04a34314584a8a1051044a16154200a8302504109fcc53e90a7d004f7049e4613c08276184ea209cd0538c0a6f0a4db209b0213509269204ce88996053201261644c01097c412e3225a444af0a958092a82254084a620941912720a4c2249608924a12420245914880490c1121202401147e408f7011d41a390246ca88d4211a2023221462808ba0d168122c04456108a6411391225414470288809108221e5143c00872050d8121a0843220860810ba021485
|3=>0x76820ecc21d8a83aec475a02eb011d5843a95074e42e9505d141ba10274008e7861cea039c4073504e6409cb0e3950872820e4a81c7c1b8e0271a08e2ca1c4983872270c80e1209c18837f596fa22df081bda0379826ee0add821ba88373a06e282dbe05b70436d046d630da541b410366446ca20d8c19b086360086be20d7681ada235a026b220d5d21aa91354086a502d4409a80834e2869a40d2d05a4c0b480268e08d1821a3003436268480cfa2d9e0333a0967220cdd819a21b321166204cbc51970432c5065508c9f0592c13240464490c84418f9231d4163644c69018c143169062882c4a0588813100461c50c314185a03098160e14c184182843033060440c00457f842fd0c5f612be8417c902f8405ed10bd4117a042f2505e280bc1017740aec125d608ba68173d02e620
|4=>0x9060d20812404447d528f8411e90a3c01c77108ea191cca23908470218e0011ba06368146c048d27119c463300c66008c70b1841a300245e188ba2116d822ca1458018ac0d1542229c8452808a10313c0a270244d2089a011288e2480c470688e011112621884424087f850f60a1d9243a10870430dc0a1ac143402866090c4a2180842f4085a910ae0614854272484d010904a11904214183d07070320d8441a1083401065020b41c15028280904862082840f20819830264604024070880a6100a860020bfe067f828fe8a1fc283f6217e908fc849f8883ef487daa0fb081f520be7837cc04f9031f1843e1507bea0f7611ee013da0c7b012f5d01ea41bd3027a308f4021e7283cca079484f2405e4083c70478a50f0c91e1203bf8377a60ef011dd843ba1077240edd09db00bb502
|5=>0xa960952822a46054800a8d8151206a18154204a8241500429f1253d40a77054e8229c1453630a6a414d1029940d3012a5e094b842965052b40a530349c4a928c52390a4501481068f40d1c18a3423468028ca051880a2c1945122898851220a209143a06868150c20a161142542841050644a0707408428082500089fc613f1827cc8cf70a9ea293d02279884f2209e2813be1277044ec189d6813a49274204e6819ca093902271284e1409bca53720a6d064d7389ac41351066980cd1069a00933c4267104cd40995073202a63824c518986613050660044bf0497c112f4425d314b84296e032d8225a824b318962a12c08257604ab83954112a05253844a6109484328c065041c9f0293c09270a24d884982392e812520e498149208922212408246c1c8c029141322502442048594
|6=>0xc0d01810c3019060220c030180102ff065fc14bf6117e822fc845f730beb037d00af9215f101be2017c00af7055ed04bd6917a902f4885e840bcaa379042f1885e220bc40178182ef505dc82bb6817620eeb04dd501ba80574c0ae8855d004b9e1173822e6145cb10b944171d86e2915c321b84036fd2adea0dbd00b76856e606dc00db702b6c216d112d9825b204b62416c082d7885ae10b58616ac06d5405a980b4ea169306d0c1d9f06b3c0967422ce0859a60b328165e06cb015940cb261164842c90058fc1b190b6281ac50058752b0c4161502c1c0d8202b020960022bf1857d20af8815e626bc0257644ae8915cc82b91057140adf035b41ab60256a18ad24159e06b28356410ac611584c2b01055f04ab9075681aac8255840aaf0155702a981d5210aa06153c82a72054c84
|7=>0xd6a21acd4359206b120d5f41ab90356606aa88d5103a9c0753046a501d4809a8c2351086a110d4101a7e034f2069c82d3611a68434c8869721d2e01a548749a0e9141d2201a3e0746c468b81d1223a20074380e8512d0625a080b408167f06cfc059f40b3e0167b02cf4099e4133b8a67514ce8419cc23390867120ce0419b90736a066b41cd4039a0173380e6601cca0398c4b308365f14cba2996c332d1065910cae29958232a2865340ca5019408b2720e4d40c988192907240564622c88459081b208264020c7e118f8231e8863c80c75818e6031bc263584c68038cc2318a263040c5e818b903164162c00c56818a507142062681c490388c0b110262014c3e11878430e4161a24c3401864830bd061620c290584c830900e1140c208183a07068160c04c16098284304a060750
|8=>0xea201d3e07a70174d10e9821d2c43a58074930e8e43d1c03a300f4540e8881d0d03a0c0f4080e8001cfe039f4073c81e7801cec0b9d0273908e7011cdc839ab073420e6605cc80b984173000e5d03cb40b960272b08e5231c9c63930872421e4603c8c0390d071e4ae3a09c71038e0071a81e300dc5c0b8b0271504e2811c4c83891071081e2001c3c8386a0f0c40e1701c2607844070585e0a01c1013810670120e0041bf90b7ea06fb81df405be04b7b126f424de609bc45378106ef04ddc11bb06375846ea40dd281ba04374006e710dcc41b948371d06e280dc281b840370206dec0db783b680b6c826d70cdac09b54136a206d218da301b3ca367086cd20d9a01b310365a06c982d9005b1c0b63046c600d8829b0c2361406c028d7c61af4835da26b982d6e15adc035b806b608
|9=>0xeea01dd403ba8077404ee801dcc43b91077101ee201dc403b80276f04edc11db443b61076b40ed501d9e17b300f6502ec805d8c13b10276108ec081d8003af9075e20eba81d6e13acc0f5802eac29d5803ab0075510ea821d4c83a92075140
|_=>0
def stPkX : Nat → Nat
|0=>0x204801fc7e1f45402c7c1a0371ec7a1e4781dc761d40113c741646e1b46c1ac271a86819c6618c621805f0d05e1745c1645815c561545414c0e0c0521445013c4e01c35128490b84811c461140e1100a10c4210440064070c43f0383d0f83d0f00e02c3501c38038370d8350b8340cc320c4300bc2e0b42c0ac070a829064280382708c220842007c1e0641805c1605413048110400e0340b0280801c0500400
|1=>0x9cd1208d00fc2733cce0f4cd330302d4cb0c0ca324c831c08318c51f0c430cb230881260c11c8011188928079300310007c2f8bd064bc2ecba2e4b80542a1f0b42cc5120424240b12c0192bc3d2b8ad2b0ab2a8a92a0a0184a70d4a401c6728c0b0643628481064a027c9c26c9a26454110512609716896254300280e2509309064248912404223c8e2348c0202b1508619c302248821c860d085210832080e
|2=>0x4700e0dc5129c4a46cd34682b01d17459154511338019281124451043d0e0c03519cb24344f4305d0c10b42909420a741d06411034081e11101400ff150fe150193f40801cfc3084a134d63ecf83dcf61082b1188f3d4f43cc46038982c8c235cf2054f13c0ef3b8ed094c53acec01ceb3a8e90d8e13a0c539c47394e438c08388e13806b0fc5d3788f374dc2842636c19204da364d835cd6354d4020d334870
|3=>0x5385d1505d5314b3dd4a5245d0d0515212b13c7551d2651945375441bd430c4c2418270381903836118150b9422c84d1e541004e119ca74fd3e4f4da4a8611852a2405138408314a74f0352d53b4e939384360dc514e0420dc354dc544d8d04d534205334c9314c12f1f04f4b92d02d2c4ad2a0c129039280f4612c851131272344a3852634ce01fd2549007038d31752348520204ba47d1e04c514051d0dc0e
|4=>0x3845164854400b21459063d8e6347d62c5162989620240f587618b5521853158460c8f1686f1f1826058036cb5054370202b1757e5f1425ed165e8245e4612d4905e0510dc595d8815d5745c8f25c5700ad6f2096e5b47b5b081470a75ad6a5a56859cf51c8275996458c5b1180729c511748f5815d368614a8b65715b5685456558555540c153548345455002cca53c0a02c3611837144341f04134c54490d7
|5=>0x445d72c162d408729c9720da02c440c1c70ddc634dc5399c470c24314750ddc21ec24705c0385bf000512c8826f8696f5bb6e9b96dc3d36db66a5251286f461b56d1b31688a6c9b12d5b06bc3729d616b4086b02b3d4b86a8db3ac9d6a12a69c81698b6694673b0814a88f315a468da25bda13450e228b9308d419cea6786f674b52ed9b6699916198091970785113d96205951506f144241acee64c082c834
|6=>0x9105228e17edf9331f7090647d8a6129f51185d3adf47cc083707c29df25d14d1c04a09c46055f17c0662c5ef229ee2c9ed23deb5845a2c94c241e95ade80ade62e1e5791e31185d51464789187844f1d47c0d9d42346f781df779dd19c460f5dc754b25303f2c9da14481105d9459d85f5d71287f7585d09027224817586f0dc905c051751d3749d1601cf38475240da2ac310549e13c67738a7185cd204ea
|7=>0x8418b2c8838b43d8407f8b0464162b23c34020c76461c23e2989ddb5bd0733a2609c31895d0890e32044f0da0d10a23888810f48b788b562db603a211188f36e2048a1f8748e830db09cee0905d86a195585b12a1885a13276118420f838360c56c380e1380b2530428308b3b20b384b229d0e82a098220709d047b00e430be6806709c7581a052c85480c3480a01800da52c367fdfe4602b0d9fc0d84623c41
|8=>0x93c4a0900e0d61f52e4d1a48f9304a000c03b4be92e4991e4619c2735e451acd30fd0515194208b02d88252cac9103f2424301c6728ca213e42382411cc672ca4025c5a8fd2209c912406f7d4f7128154a846285ed8f45d8f0e1118088ee3a881055313706639092388dc168d84610481548b584a354644a1758a118311100e8d00b60c5d8aa3319c278c8758c4014d8372082465cfc8c0f952cb90552a8bc35
|9=>0xd815986744c6731bd2a2f8b209e729c26f53031300732766e9b46616a6c1526a9366828d53176671bcb529e66994340206709df0990da4008f3788f038671112141d1e12a1e98cd398a178592701d0501cdd4649d380d61d43434cb2980d397e141765e8145d3d4313cc2b1284c02a5d944b28f4c529e5c05e5b34e5a522582c83729c30020e195cbe6e656670eb36864954b516a5494c5a6b85135e5109250
|10=>0x52a09d521486734c540f65c0dc08176935ac69a484a6a4673842703a914e45460e903e50505401a3cb91748f150caa3905005835308ea34674fca702a8c3b4418f92f1a4411500a0a9e0a2e8a22e89a2081a1e4d9a0340d84623c2ba1a8509c0e1908f401393dc8f0da11a122b34c371468331505a045d3b58f12a809fe7e9f0de0053612a7b9ea799e0812ecd729c1c315481d67760075054e1021189da75
|11=>0x41401488c5932a6a94d3a901c500817114052aa312851a885a8a097400b9275a11bc67516a136d6c4a96d22c3d23ea02c8342947535d8a620b61298301c721d4d0375bc22c2b1188f0905122c90a7c24204a72ca9e104a7a751c58e141bc5aa71b4644c7572051d47c1684a7802ba6c7c104540388f01c690d0eea68540d0d709d4ca64d34160ea6297150ed1042b2c8d7530ed34cc50900713696a54de23e94
|12=>0xd1225b25c60eb701c67368b25bc8b36eb6ad594ad0370d94c43ab347036ac9839203d0acb21a6b11bc4a18522680a22e4672c8dc6c84a4162bac0b5abc9d0da17a0aae02075168412d47211aad814513b45dab0a21d5043ad6b558a7a3cb2730241d4b5aac6b6b88129c752c9db17437698c5055a036c51aa9804605a0dc8152c901ecea624b5502731bcf7aa4310558b1280819e102797d471752b09da9c24
|13=>0xd88f146bc672118ac9d2d44f500758e1e023c697584c19ce19a46b1925c34e4f3b50523c64380361d47c37c3f0392348522aed221d4243848b0f4b229d0e28d561307c489b97d4518407e1643d6b84a781ae8702b2d4724308b368ed57c671189dae9b229c4611a0c3703d2c9f809c75488e08ee200d8b219c37ae4a11747fa1d370d96d3148f27a171a52a29eb80906b0205a8a054400814715e1d434174b2
|14=>0xa71bc9d1d5e01d4c51a467a0cd37803d204b278905488678acb52889d25c6b090a7191a529c8f611221057d23cb66d2140f4d312922680361bc6f12837470a729c901508f532611514c0c12ab05229f5831a45129c6752c0823c2754867380363086919e2e7806760d7f1686f168697eac012918386bf132699f8c20206723d2a2412aafabd414be23c6929c272c8821d507
|_=>0
def stPkGet (p : Nat) : Nat :=
  if p < 9533 then
    let t := fld (stPkT (p / 128)) 4 (p % 128)
    if t < 15 then fld (stPkD (t / 128)) 10 (t % 128) else
        let z := p / 8
        let h := fld (stPkH (z / 128)) 19 (z % 128)
        let e := (h >>> 8) + ((0x8776766576656554766565546554544376656554655454436554544354434332766565546554544365545443544343326554544354434332544343324332322176656554655454436554544354434332655454435443433254434332433232216554544354434332544343324332322154434332433232214332322132212110 >>> (4 * (h &&& ((1 <<< (p % 8))-1)))) &&& 15)
        fld (stPkX (e / 128)) 10 (e % 128)
  else 0
def stOffB : Nat → Nat → Nat
|4,0=>0xfa503d540f0503ad40e65038540dc5035d40d25033540c85030d40be502e540b4502bd40aa5029540a05026d409650245408c5021d4082501f54078501cd406e501a540645017d405a5015540505012d404650105403c500dd4032500b540285008d401e5006540145003d400a5001540005
|5,0=>0x9dd4271609ad82656097d82596094d824d6091d8241608ed8235608bd82296088d821d6085d82116082d8205607fd81f9607cd81ed6079d81e16076d81d56073d81c96070d81bd606dd81b1606ad81a56067d81996064d818d6061d8181605ed8175605bd816960591415e60561815260531814660501813a604d5412f604a5812360475811760445810b6041580ff6
|5,1=>0xfcd83ed60f9d83e160f6d83d560f3d83c960f0d83bd60edd83b160ead83a560e7d839960e4d838d60e1d838160ded837650dc1836a60d91835e60d61835260d31834660d01833a60cd1832e60ca1832350c75831760c45830b60c1582ff60be582f360bb582e850b8982dc60b5982d060b2982c460af982b860ac982ac60a9982a060a69829460a39828860a09827c6
|5,2=>0x15c1856a61595455f61565855361535854761505853b614d5852f614a5852361475851761445850b6141584ff613e584f3613b584e76138584db6135584cf6132584c3612f584b7612c584ab61295849f61265849361235848761205847c511d98470611a9846461179845861149844c611198440610ed4435610bd84296108d841d6105d84116102d840560ffd83f96
|5,3=>0x1bbd86e961b9146de61b6186d261b3186c661b0186ba61ad186ae61aa186a261a71869661a41868a61a11867e619e18672619b1866661981865a61951864e619218642618f18636618c1862a61891861e6186186126183186066180185fa617d185ee617a185e26177185d66174185ca6171185be616e185b2616b185a661681859a61651858e616218582615f185766
|5,4=>0x7e561f7d87d961f4d87cd61f1d87c161eed87b561ebd87a961e8d879d61e5d879161e2d878561dfd877961dcd876d61d9d876161d6d875561d3d874961d0d873d61cdd873161cad872561c7d871961c4d870d61c1d870161bed86f56
|6,0=>0x2679c99772641c98972609c97b725d1c96d72599c95f72561c95172529c943724f1c935724b9c92862485c91a7244dc90e5241dc900723e5c8f2723adc8e472375c8d67233dc8c872305c8ba722cdc8ac72295c89e7225dc89072225c882721edc874721b5c8667217dc85872145c84a72111883e620ddc830720a5c82362071c81572039c80772001c7f971fc9c7eb7
|6,1=>0x2d65cb5272d2dcb4472cf5cb3672cbdcb2872c85cb1a72c4dcb0c72c15cafe72bddcaf072ba98ae372b71cad572b39cac772b01cab972ac9caab72a91ca9d72a59ca8f72a21ca82629edca74729b5ca66729818a5972949ca4b72911ca3d728d9ca2f728a1ca217286d8a1472835ca06727fdc9f8727c5c9ea7278dc9dc7275989cf72721c9c1726e9c9b3726b1c9a57
|6,2=>0x3449cd0b73411ccfe633ddccf0733a5cce27336dccd4733398cc773301ccb9732c9ccab73291cc9d7325d8c9073225cc82731edcc74731b5cc667317dcc58731498c4b73111cc3d730d9cc2f730a1cc2173069cc1373031cc0572ff9cbf772fc1cbe972f89cbdb72f51cbcd72f19cbc062ee5cbb272eadcba472e75cb9672e3dcb8872e098b7b72dd1cb6d72d9d8b607
|6,3=>0x3b31cec573af9ceb773ac1cea973a89ce9b73a51ce8d73a19ce7f739e1ce71739a9ce6373971ce5573939ce4863905ce3a738cdce2d63899ce1f73861ce1173829ce03737f58df6737bdcde873785cdda7374dcdcc73715cdbe736ddcdb0736a5cda363671cd9573639cd8773601cd79735c9cd6b73591cd5d73559cd4f735258d42734edcd34734b5cd26734818d197
|6,4=>0x4215d07e741ddd070741a5d0627416dd05564139d04774101d039740c9d02b74091d01d74059d00f74021d00173fe9cff373fb1cfe663f7dcfd873f498fcb73f11cfbd73ed9cfaf73ea1cfa173e69cf9373e31cf8663dfdcf7873dc5cf6a73d8dcf5c73d55cf4f63d21cf4173ce9cf3373cb1cf2573c79cf1773c458f0a73c0dcefc73bd5ceee73b9dcee163b69ced37
|6,5=>0x48f9d237748c1d22974889d21b74851d20d74819d1ff747e1d1f1747ad91e474775d1d67473dd1c874705d1ba746cdd1ac74695d19e7465dd190746299183745f1d175745b9d16864585d15a7454dd14c74515d13e744e19131744a9d12374471d11574439d10774401d0f9743c9d0eb74391d0de6435dd0d074325d0c2742edd0b4742b5d0a67427dd09a5424dd08c7
|6,6=>0x4fe5d3f274fadd3e474f75d3d674f3dd3c874f05d3ba74ecdd3ac74e95d39e74e5dd39074e25d38274dedd37474db5d36674d7dd35874d45d34a74d0dd33c74cd5d32e74c9dd32074c65d31364c31d30574bfd92f874bc5d2ea74b8dd2dc74b55d2ce74b2192c174ae9d2b374ab1d2a574a79d29774a45928a74a11927d749d9d26f749a1d26174969d25374931d2457
|6,7=>0x56c595aa7568dd59d65659d58f75621d581755e9d574655b5d5667557dd55875545d54a7550dd53c754d99530654a5d5227546dd51475435d506753fdd4f8753c5d4ea7538dd4dc75355d4ce7531dd4c0752e5d4b2752add4a475275d4967523dd48875205d47a751cdd46c75195d45e7515dd45075125d442750f19435750bd942875085d41b65055940e7501dd4007
|6,8=>0x5da1d76175d69d75465d35d74675cfdd73875cc5d72b65c91d71d75c59d70f75c21d70355bf1d6f575bb9d6e775b8596da75b4dd6cc75b15d6be75addd6b075aa5d6a275a6dd69475a35d686759fdd678759c5d66a7598dd65c75955d64f65921d641758e9d633758b1d62575879d61775841d60a6580dd5fc757d5d5ee7579dd5e07576995d375731d5c5756f9d5b77
|6,9=>0x6485d91a7644dd90c76415d8fe763ddd8f0763a5d8e27636dd8d476335d8c6762fdd8b8762c5d8aa7628dd89d6625d989076225d882761edd874761b5d8667617dd85876145d84a76111983d760d9d82f760a1d82266071981576039d80776001d7fa65fcdd7ec75f95d7de75f5dd7d075f25d7c275eedd7b475eb5d7a675e7dd79965e49d78b75e11d77d75dd9d76f7
|6,10=>0x675999cf76721d9c1766e9d9b3766b1d9a576679d99776641d98976609d97b765d1d96d76599d95f76561d9517652d9944764f5d936764bdd9287
|7,0=>0x6eeddbb386eae1ba476e75db9586e39db8776e01db7886dc5db6986d89db5b76d4e1b4c76d121b3c86cd21b2c86c95db1d86c561b0d86c161afe76bdddaf076ba21ae086b65dad186b261ac276aeddab386aae1aa476a75da9586a361a85869f9da76869ba1a668697a1a5776941da4886905da39868c9da2a8688a1a1a8684dda0c7681219fc867d219ec8679219dc8
|7,1=>0x765a1d9067625dd81875e61d71875a9dd637756e1d5387531dd46674fa1d37774be1d2787481dd18874499d0a8740ddcfb873d59ced873961cde7735a1cce8731ddcbf872e1dcb1772a9dca28726ddc9477235dc85871f61c75871b61c65871761c55871361c46770fa1c37770c1dc2977089dc1a8704ddc0c770121bfc86fd21bed76f961bdf66f659bd186f29dbc28
|7,2=>0x7df5df7587db9df6777d859f5b67d51df4c87d15df3d87cd61f2e77c9a1f1e87c5ddf0f87c1e1f0077be21ef087ba21ee177b661ed187b261ec187ae61eb187aa61ea187a69de9287a2a1e82879edde73879b1de65779761e567793a1e46879019e38878c21e28878821e1887845de0987809ddfa877ca1dea8778a1dda8774dddcc777121dbc876d5ddae7769a1d9e8
|7,3=>0x856e2154785322144884f5e135884b6212588479e1168843a2106883fa20f8683c5e0ea7838a20da8834a20cb7830e20bb882ce20ac78295e09e7825a208e8821de07f881e5a071881a620627816a20537812e2043880f1e035780b9e02778085a01988049e00a8800ddffc77fd21fec87f95dfdd87f59dfce87f1ddfbf87ee1dfb087ea21fa087e699f9377e31df848
|7,4=>0x8cee233568cb6232588c7da31788c3e230788bfe22f878bc5e2ea78b8de2db88b4e22cc78b15e2bd88ad622ad88a99e29e88a5a228e88a1de280789e5e271889a9e2628896de255689362245888f62235888b9e2268887de2178883e220788801e1f9787c9e1ea8878de1dd68759e1ce8871de1c0786e5e1b1886a9e1a28866a21928862a2182885ede173885ae21638
|7,5=>0x237f88dde236f88d9e236078d62235178d29e3437
|8,0=>0x9401e4f9793c624ea7938a24db79351e4cd79319e4bf792de24b0792a224a17926624927922a2483791ee2474791b5e46589179e4577913e244879105e43a790ca242b79091e41c89055e40e7901a23ff78fde23f078fa5e3e278f71a3d488f3223c488ef5e3b588eb623a678e7a239688e3de3878
|9,0=>0x2530794a5e5227946de51479435e5076
|10,0=>0x25376
|_,_=>0
def wireSAt (i : Nat) : Nat := if i < 706 then scatter (fld (dictB (i / 512) (i / 32 % 16)) 64 (i % 32)) else 0
def readSt : Nat → Nat → List Nat
|0,_=>[]
  | n + 1, p => wireSAt (stPkGet p) :: readSt n (p + 1)
def SS (s j : Nat) : List Nat :=
  let v := fld (stOffB s (j / 64)) 18 (j % 64)
  readSt (v &&& 15) (v >>> 4)
def SD (s j : Nat) : List (Nat × Nat × Nat) := (SS s j).map (fun w => (w, projBit r1sG w, projBit r2sG w))
def htAt (s i : Nat) : Nat := fld (HT s (i / 128)) 20 (i % 128)
def idxH (s h : Nat) : Nat := bsr (htAt s) h 11 0 (NN s)
def idx (s : Nat) (zs : List Nat) : Nat := idxH s (hk 1 zs)
def opPkD : Nat → Nat
|0=>0x16c1444b00d12804c3b4890ec0443a27506d4d41b50106c5a41b0910512241416903c0440c4150308b40c1d503051406415018694061690181a80220436c03cb20530e404c1c01906d1801b2d406c4b81a00f05105414275050754141a503c3ac0f03303c03c0f00d0312240c27502403c062750183d40212c2fc06cb20302c806c6b05106c3a81b0900241440901319c0cc670180e80341a01302406c0901100814c0201900803c4b0130e403c1b0ee0680440f0e80188f4bf0502fc0ccb203306c5a01a0190ec14c3b00d0e80cc1b204050a740f0190e80c40c23d018a740203303c14c0f05102414c0903106c1a809033008044bf0530083b00203106c1ac1b06819c06c0f01b06c3a01b0ec06c4b01b0eb06c06c0201b06c04c1b0ef06c03c0305106c1a4030190100c41b0ed06c0341b03306c3a40401906c044030310ec1441b053010144140190301440c0190181441403106c0c41b0190180c41b051
|1=>0x1500344b00f1280cc4a00f0ec8f43a4890e92203a0130e80443a00f0e40cc350120ac06c2b0190940c4250190903bc1c00e0700341b55806cb581b20606c8141b1be06c6f01b19006c61c1b17406c5ac1b0f606c3d41b0f40689d414535051058142d5050468140f60503b4140da0500340f1be03c69c0c399030d740c2dd0308a40c1460303a80c091030044090f50243d00906b0240340700d019b2406579018e18062950188b4061650183d806091018084060110180340446501105404385010a740423d010694040de0101a40387100d0540324500c8f40318500c3740306900905c022070081cc0201360c1bd8305336c06cb50692c80c4b20132c8044a205119c04c3b2750ec8f03b0130ec03c3a29d06d1881b36806cc5c1b2d806c7201b13006806c1a00d050b581411903c3a80f013030b540c1be0302480c00d0192240609200d7d40352d0083bc0200d46014cdf00f2c80348a03119c14c67019
|2=>0x307c80c1a60306940c18a0305d80c11a0303a40c0de0302780979f024b60092b7024a2c092840248bc091bd0246f0091870245a00912c02430009091024240090730241a80906901aab4069a701a6140685101a0a4066950197d406585019404063b5018dc40635d0188b8061be0186f4061760185a8060d201831406069012614048ad0120d4047f5011fa8046710115e40452901140404416010e18042dd0108b804229010754041850105d80416d01051804145010464041060103a4040da010364040d10102740402100e6b80386600dec40375600d4040341600cac80329d00c7b40314500c4640310600c3b8030ed00c3a4030c500c25402460008b540222b008640021870085a8021690085a0020f50083d0020ed0082300206400414c010519481421705365004d6d01b3c8044bf23f2fc144bf0132fc044bf00d2e403cb603324006c8a0112280348106a19c0446700d16c0645405115006454011
|3=>0xf43a83b6c90ed84c3b48b0eced43b23f0ec2483aa0b0e965c3a48b0e8a7c3a2780e4c54390ef0e43ac300110c003c2b0110ac03c2603109406824537091054240ec08c0c41d03106e5941b92106e2b41b8ab06e1e01b83706e0d41b7b706db841b64906d7fc1b5d306d62c1b57f06d5ec1b55c06d4bc1b45906d07c1b41c06cf901b3dd06cf601b31506cb541b29806c9741b22b06c81c1b1ca06c6fc1b17506c5a81b15306c4f41b12f06c4701b09c06c1cc1b0650698901a48b0692241a2740687541a14406403c1900d05814c14ac5052714149290522e4147a9051ae4146ad0519141462e051894145dd05170414486050e181434d0509e8142390508b414226050818142050506b4141950505a8140f50503b8140d90502781400603d1800f36803c6f00f1af03c3a40f09303804c0c9390323b80c86d0321580c7e1031b240c6490318940c4710311680c3ce030dc40c309030b880c2d60308180c205
|4=>0xaa004e7d0308f8146281d78481be1201b8403be100338400c60400f78004ddb03376c0c1d300f7401a1d0033730145bc0136d014da90536a406da003367c1bd9f05367c06d940536500c18f05363c0c18f01b63006d8c01862c1a1830eb60c06d7300f5ac1456b01b5580cd520334a82452a0534a814521050464144fa00d3c8144f203137c14cdf01b36c04cbf1be2fc3bcbf06b2e8144b90332d48fcb506b2c8a7cb220b2c85a4b20f42c83aca30312881a8a203127814c9e0192754049d13f2400449000f204e14810691f00cc755011cc1447201b1c406c700311bd2a06f1d51bc5106f0ef1ac6f86b1bd1ac1486738319c5ac670ef19c03c66019194034640531683a45a0e81500485400e1340444c01b12d2204b011128b604a12e1283bc4a06b1281a84a06812814c411681040cc4100d0f475c3d1d50f45103d0eb
|_=>0
def opPkQ : Nat → Nat
|0=>0x3108e0582409400008065b00b00803004a20a0020d00e7d05805c070159114003078014840000d800381d0e07108c04344240001f015a240c030e40c00d3a0a002038d500c5e0700500e2725c74032258900039c160842c00c1e004d500c00070053c4240004e026173987b034015b83500800014c21fc030e40c0f8030940002006844961f80b04401094000f803018087b1193c00013809799181980008807
|1=>0x4d356887000064041d0e00001c0032802004042587e02c11006467462a0100e080bf0b403010020940001001000033508a024841cc03078011f4110000301172288020d00e198270002201d690080d000098682c00c02018038a45f11c0200d6d23002050015e06803c051c01b000740300036c53048066d86600c220104632c0200c13000d2260dc050030c45e07005010031440f021e73c00013809001cc
|2=>0x55826048061517900002021024041d0e0075d44900800014442ac0008807008051e02901da81f067034010fc0d00003010330bc100d4080f80300800016230bc10000160a02e00002020014940d13809394cf00800014040006e06006010031440f020112f0650d80115031000020207c0640101c051404c0081e01a4719436048011a427000020202c0f803018088c84d008340396b2080207c08021161c818
|3=>0x7e40100009941360b4030a802190144489c040082a800008081646703401035490a4048041a000136155b1f411618bf0b4037dc057140c080030e40c09400008060680017003390260a8027655e23409760c6188040fc0d00c040bc100d40800800370148bc170a4040740b00c0192c2f0400975a4d3000987c1e004167c08207c053ec450000100c3a110001040d01404004053144b05404014041e4400057b
|4=>0x8b4330400e07431000050081a000160081e0180944d70008160b403008068e05203c05068030b8000740b008060086f0680000c5103c08001ad388139587a05c089001200416955bb064040685605c002bc2b15c02008cd0000970c6b010148f4cb00813114000480109c6a0000e0f02a008140b4030ac0276d060100e73d5f120042ac000880761cb23e0050d402000050ac02068001fc030e40c6aa3c3a40e
|5=>0x4c429010145d0026040e0406803c0503400234090b5af16c03740851b00c930f20c00a42c03118026ba3a01c142842409c0097cdf05c040006e060062d82b0080e97505054040dc0a008064b5090cc109652300014034a403c059607a05c059688303c051a4021d8091180207c088f83200c04978750640597105054076f457008043b422010145309f028013087f0e40c46ccd00009528fe02c012541a00007
|6=>0x6dc660880433c100000548035000050e00000c040166338013504260480165c3600c0183c0b0640100803338094001d02c0184c1d0e0047bc8207c051040d01c052e410228098183d0280c0002b11c028e410134024489c04008842150200c1485103c0800c06070086f01901001988b3060010093e0680000d0707c05776140140c09c0000c1304405010015bc02000169848b06408008000140c10c0007c05
|7=>0x2a1660080736400008061ecb80280117c1b254072f0651b00c16803000164aa040f40a8d80f01413008200b0037c405034132a4a503c059a0a303c050081a000074f03d0280e750b23e0051200000c04694583f011570dd060062a08005407084240000940c030e40c30c230100e0cc100ac024c9390a0029992c068001a8000080e990c90080606c4b0b0030fda308c07678e615413948a503c05008780a404
|8=>0x630f9064055189812405044c42381626c3600806098530a80200a42384130405e070058cc040d00e3bc010340901400100060040039c1608411054040f053048068841a000163d03e00c05860f11380999404734140080007c050100303c0802803304134cdff0141300800234091100000c0c18c0b00c010cc1000808011b07240e9524f164190c00a008065d8026740c60d0b3a40e96d1c000130800300007
|9=>0x143b048011740301c051284b0540400c0603c0818c310080853c9d00c0124853048068ac2e0000e1102e000071a41009c00586691dc0c51c2e034001400307801444041901436461060017002105404624570080443479100010743103c059aa0206c134e03a03c05108380fc04610d80a002490001b00c0c00a23c140a00200005539ba05c040143b0480106001000090b80007c0586c2c00c0c534de10001
|10=>0xe8441140000881090007890a55c169c01b21800290a303c0574c891200466421090005a002088046ac573240265003078011ac040340e0003b048014a40200c01009bf08804008bd3a01614002078060282000c014fc1a09c000640501001784b00d405000b42780124853048060842409c00098120040963a0a044043dcb707005014110e40c450a005c01635622400305c0200c019bd1e0000c2b40006001
|11=>0x82e000070b42000c01008a709c002b0000080e6f866088042ec18004096d644190140f40a080030000d0080e3c87108c044101501014044650d8017182604801000db08003150380000702c0200c014001d02c012a10f04801429270140708401054046607006c0414868134029207c0640110a0e02c010f02a118020f803000051586005c0504db13a80e9826b180174d0b7070050097a080030180413c05
|12=>0x6c94508c07790d600c166e01a000075dc21054047a41800409000020780621005384130740b060011488303c051484903c054bcba0b8002107300c04008331700309025000015100007c051ac040d00e0095d0a404128780a4044dc210540425c94000070b03200c0801de313c050340000c047f8430000108419054040000200c0126d280041602c850d8010f011048010802f170039c4ec6800e8b89505c04
|13=>0x54c5d00c080007108c041f80b044013fc1d02c018781e004164550c0480100c3103c057f4b10280179567008040406803c053440007c050106106001834490440527c0a008062d4a1054041ec0200c015cc020d00e00c8c008149b904054040005b00c0c3401a000074550c048014f42000c09044c710c001401e004090f8030180800d90560162204202c0100c02070083cc3002802898940440400c6106001
|14=>0x65803338098ec0a2f40c07431000054d54306c042204202c015909a0fc048d10807c0502c260480108481054073d03e00c05018b501c051bc51134024400a04801114000080615031000050b0030080874889120042c03504405450a005c0199d6a0080909400010010000b0600109400008061943604801128170540406d4b1880400c3a03c051040d00c010100103c08544990dc010990d048018146d07008
|15=>0x500110e40c704d422809008ee088049c8fa064054400a0480100c000200645c7006c0065403044167cc37034015c40208c043b4220100e3144b0540404002000050c8030880466c0200c011a8000080e0f02a11c022044b054040080323c147a8400040963ca71d8090f03b0c80358c990dc011846e06006944a503c086ce4e164192a59300c05174030000500d8a3d805000971d00c95c7a05c05001e027401
|16=>0x2a480054040c80301c05690b42780100805054070106d070083b0f703405394350000500c6d070085480000c043fc1d02c013489812405168030000794c5605c044985d00c0500c0008c0766828008065f245190144382a0080e2204202c010103a03c0514c3b048010c00a008061503100005028021541334c87000013202500001028851b00c0ec7910001768ef0040901008060067e0f5034051e81701407
|17=>0xc03d028063405103c0801404048010940100009258a60101402879100019b46005c011b872060018704a054047ecdd060019282f170030001d02c012440500c130b4030ac02000260480116419000078300b0440137cfc044040844b0540467c02078064880007c053202500001001df274010f23f048011c047008040c80300007118023681339026048018481d02c018dc0f0140c00c020600602c7206001
|18=>0x154132cc180047108c040282000c1a000090002301e2c0cc10040be0240103c087c80d004100f40a7b4300284c00804770f60140224003230000591d0000c22c190100038813009a1039cb24c143300204c5f06c0703402020000440c01477031ee0c00a1b45e070054081d02c01094450000144c8303c058a01b0a4045503a03c080842c00c017544202c0110402034032b4000600100c00020067101d02c01
|19=>0x16734b8100080300401000091c81800437064013cc300298b10c0052018005a61040d00c220100d0a4042e410038060a4043f80b0040300005824110101a0440047c00030860000c00c930506f068000a846009ac1581709000058b802801580fd044020340090427002490bc10008230100a00c138881b0583a03c0506c8e058870000173837004af0ac020444901480054040940000494000075fc5f06e16
|20=>0x34da04c4d00807034e004c1b00c0900c020500538c0c0081e0180016c0300c04038100000506c03010a303c050982a008b60ac020dc030043c048011d4670341a09c006a5550306a0000e00c8f0502b0080c0100d0384202c0142433042431cc030a85700829010140c803010166081421436005de30413174030143c048011581701811048010002d00c02054041606005c02120046204c008ba0b80005c07
|21=>0x440180c1b04c8303c0550835014280ac0218c0b004691d8098000504c281300264803024d600c160c00a04e3503c0535ceb05035044051d419014040d00e00c4600844090001f41100c1110c00020180180313c0575c6201207044140a017008a005c013d40d015eb1380906c2d00c3d0280c2b8040512b080033300204c03068005642301026048014c018004020d00e6e41b010a105404164190081030009
|22=>0xc2a11c020640001c4a0540429c76024ac0000e0ec3200c0703c05008240006803c0582011010a20d00e0981200631160174383200d7d07005000280089c040050283700630160170081c0202f170037d4100141e004090b403004860000c0740b0046f06800130020381b188040e80f01426048010e84400019048012a8000149100c05468000056538c0c094000043f054042900f0140208c0409c0001e0b
|23=>0x1f019005f60640519c0d0101b00c0003400025a70b8000000204c1003c051a4270010807c050080001d3b02006298040505e0700500c190090707c0526c3600403068000080501e6c180171fc390300000c130445b00c5b168032780201830028012b80405111190140fc230100000c040000b0057e0700531862010200b00302c17005b43ac14040430002000c012482000c7d0440403c0504cf9064050842c
|24=>0x40000bc330415013c058641501061060011140000410070050c40202021054041484d0080311c02224480103b0480106845002200041627c0a005c81d00c05c4f0146b0101406c29010bb060010285a00c030700530c23010a60101412c150109a0fc040001e0040015413244030140d01c051040d010c710c007080b0040a0600102c7b0044a0900002c030043b0a80217c1b00c841cc031401e005fc06401
|25=>0x46302c012643700403000020740b0046302c012081f0142f040008741e004fa0640543c1200405010010c41c01410068000e0150104202c01204240000a0480108415010fb0280112815010d80a0027281f014780a404010ea038021dc0c20015011060100e008d70301c0140c02c0d004de100017e80a00436044010b800015e8004091f80b0049a670133b822010ca008040002d00c02054040283200c2f
|26=>0x40d040000581711c0200c0200c051dc0c06c040dc01070050540471c161040d168032f81303c053a0160600119c0d0b00313c0501014010010d00e05c0024c140780104009154133f411028100340300c012c40a064010f40a120040280302c011240522c192400300c131040d04401000021d4190a002008160e004044160ac0213002040000cc10000120041d02c0102812
|_=>0
def opPkGet (p : Nat) : Nat :=
  if p < 3446 then
    let q := fld (opPkQ (p / 128)) 10 (p % 128)
    fld (opPkD (q / 128)) 22 (q % 128)
  else 0
def opOffB : Nat → Nat → Nat
|4,0=>0x18601260000000000000000000000000000000000000000000000000000000000c600000000000000000000000000000000000000000000000000000000006600000000000000000006000000000000000000000000000000000000
|5,0=>0x73506e5000000000695000000000000000000000000000000000000064505f500000000000000000000000005a500000555050500000000000000000000000004b500000000000004650000000000000000000000000000041503c50000000003750000032502d502850000023500000000000001e5000000000000
|5,1=>0xd25000000000cd50c850c3500000be500000b95000000000000000000000b45000000000000000000000af500000000000000000000000000000aa5000000000a5500000000000000000a0500000000000009b5000009650000091508c500000000087500000825000000000000000000000000000000000000000007d50785
|5,2=>0x1135000010e5109500000000104500000000000000000ff500000000000000000fa50000000000000f550000000000000f050eb500000e65000000000000000000000e15000000000000000000000000000000000000000000000dc5000000000000000000000d7500000000000000000000
|5,3=>0x15950000154500000000000014f5000014a50000145500000000000000000000000000000000000000000000140513b500000000000000000000000000001365000000000000000013150000000012c5000000000000000000001275000000001225000000000000000000000000000011d5000000000000000011850000
|5,4=>0x18b5000018650000000018150000000000000000000000000000000000000000000000000000000017c5000017751725000016d5168500000000000000001635000015e5
|6,0=>0x23040000000022c4000000000000228422442204000021c42184214400002104000020c40000000020842044200400001fc41f841f4400000000000000001f041ec400001e841e441e041dc41d84000000001d4400001d041cc41c841c441c041bc41b841b441b0400001ac400001a841a4400001a0419c41984194419040000
|6,1=>0x2f842f442f042ec42e842e442e042dc42d842d442d0400002cc400002c8400002c4400002c042bc42b842b442b042ac42a842a442a0429c400002984294429040000000028c40000288428442804000027c427842744270426c40000268426442604000025c425842544250424c4248424442404000023c42384000000002344
|6,2=>0x3a4400003a0439c4000039843944390438c43884384400000000380437c4378437443704000036c436843644000000003604000035c43584354435040000000034c40000348434440000340433c4338400000000000033443304000032c432843244320431c431843144000000003104000030c430843044300400002fc4
|6,3=>0x47844744470446c400004684000000004644460445c445844544450444c444844444440443c4438400004344430442c442844244420441c441844144410440c440840000404440043fc43f843f44000000003f0400003ec43e843e443e043dc43d8400003d4400003d043cc43c843c443c0400003bc43b843b443b043ac43a84
|6,4=>0x538453440000530452c4528452440000520451c4518451440000510450c4508450440000000050044fc44f8400004f444f044ec44e844e4400004e044dc44d844d4400004d04000000004cc44c844c4400004c044bc44b844b444b044ac4000000004a844a444a0449c4498449444904000048c448844844480447c400000000
|6,5=>0x5e8400005e445e045dc45d845d4400005d045cc45c8400005c445c0400005bc45b845b4400005b04000000005ac45a8400005a4400005a0459c40000598459440000590458c458845844580457c45784000000005744570456c4568400005644560455c455845544550454c40000000000005484544400005404000053c4
|6,6=>0x6ac46a846a446a0469c469846944690468c468846844000000006804000067c467846744670466c4668400006644660465c40000658400006544650464c4000064846444640463c463846344630462c46284624462040000000061c4618400006144610460c4608460440000000060045fc45f845f4400005f04000000005ec4
|6,7=>0x75c4758400007544750474c47484744474040000000073c47384000000007344730472c4728472440000720471c471847144710470c47084000000000000704470046fc46f846f446f046ec46e846e440000000000006e0400006dc400006d846d44000000006d046cc400006c846c446c046bc46b8400006b446b04
|6,8=>0x8244820481c4818481448104000080c400000000000080848044000080047fc47f847f447f047ec47e847e447e0400007dc47d847d447d047cc47c847c44000000007c047bc47b847b447b047ac47a847a44000000007a0479c40000798400007944790478c478847844780477c477847744770476c476847644760400000000
|6,9=>0x8e848e448e048dc48d848d4400008d048cc48c848c4400008c0400008bc48b8400008b448b048ac48a8400008a4400008a0489c489848944890488c488848844880487c4878487448704000000000000000086c486848644860485c485848544850484c484848444840483c4838483440000830482c48284000000000000
|6,10=>0x92c4928492440000920491c40000918491440000910490c4908400000000904490048fc48f8400008f4400008f048ec400000000
|7,0=>0x9ed39ea39e739e439e139de39db39d839d539d239cf39cc39c939c639c339c039bd39ba39b739b439b139ae39ab39a839a539a2399f399c3999399639933990398d398a398739843981397e397b397839753972396f396c3969396639633960395d395a395739543951394e394b394839453942393f393c39393936393339303
|7,1=>0xaad3aaa3aa73aa43aa13a9e3a9b3a983a953a923a8f3a8c3a893a863a833a803a7d3a7a3a773a743a713a6e3a6b3a683a653a623a5f3a5c3a593a563a533a503a4d3a4a3a473a443a413a3e3a3b3a383a353a323a2f3a2c3a293a263a233a203a1d3a1a3a173a143a113a0e3a0b3a083a053a0239ff39fc39f939f639f339f03
|7,2=>0xb6a3b673b643b613b5e3b5b3b583b553b523b4f3b4c3b493b463b433b403b3d3b3a3b373b343b313b2e3b2b3b283b253b223b1f3b1c3b193b163b133b103b0d3b0a3b073b043b013afe3afb3af83af53af23aef3aec3ae93ae63ae330000ae03add3ada3ad73ad43ad13ace3acb3ac83ac53ac23abf3abc3ab93ab63ab33ab03
|7,3=>0xc2a3c273c243c213c1e3c1b3c183c153c123c0f3c0c3c093c063c033c003bfd3bfa3bf73bf43bf13bee3beb3be83be53be23bdf3bdc3bd93bd63bd33bd03bcd3bca3bc73bc43bc13bbe3bbb3bb83bb53bb23baf3bac3ba93ba63ba33ba03b9d3b9a3b973b943b913b8e3b8b3b883b853b823b7f3b7c3b793b763b733b703b6d3
|7,4=>0xcea3ce73ce43ce13cde3cdb3cd83cd53cd23ccf3ccc3cc93cc63cc33cc03cbd3cba3cb73cb43cb13cae3cab3ca83ca53ca23c9f3c9c3c993c963c933c903c8d3c8a3c873c843c813c7e3c7b3c783c753c723c6f3c6c3c693c663c633c603c5d3c5a3c573c543c513c4e3c4b3c483c453c423c3f3c3c3c393c363c333c303c2d3
|7,5=>0xd053d023cff3cfc3cf93cf63cf33cf03ced3
|8,0=>0xd6e2d6c2d6a2d682d662d642d622d602d5e2d5c2d5a2d582d562d542d522d502d4e2d4c2d4a2d482d462d442d422d402d3e2d3c2d3a2d382d362d342d322d302d2e2d2c2d2a2d282d262d242d222d202d1e2d1c2d1a2d182d162d142d122d102d0e2d0c2d0a2d082
|9,0=>0xd751d741d731d721d711d701d700
|10,0=>0xd760
|_,_=>0
def readOps : Nat → Nat → List (Nat × Nat × Nat)
|0,_=>[]
  | n + 1, p =>
    let code := opPkGet p
    (code &&& 3, wireSAt ((code >>> 2) &&& 1023), wireSAt ((code >>> 12) &&& 1023)) :: readOps n (p + 1)
def PO (s j : Nat) : List (Nat × Nat × Nat) :=
  let v := fld (opOffB s (j / 64)) 16 (j % 64)
  readOps (v &&& 15) (v >>> 4)
def pmB : Nat → Nat → Nat
|4,0=>0x2000002000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000040000000000000000000000080000000000000000000000000000000000000000000
|5,0=>0x2000000000000050004c00088000000060000000004400000000000000000000000000100000000000000000000000000200400000000000000000000000000000000000004000000000800000000000000000000000000100000000000000000020000000020000000000882008000000000400000000000010000000000000000000000000000000000000000000000004000000100000000000080200001000000000000028000000000000000000000000000000000000000000000400010000000000000000000000000000000080000000000880004000000000000000000000000000000100000000000000000008000000000000000000000000000000000000001000100000000000000080000002000000400300000020000000000000000000002000000000000000
|5,1=>0x1000800000000010000000000000000004000010000000000000100000000000000000000000000000000000000000000000000000000520000000000000000000000000000000000000220000000000000000000000000040000000000000200000000000000000000000080000000000000000100000000000000000000000000000000000000800000000000000000000000800000000000000000000000000000000000000001400000000400002000000000000014000000000000000000000028000000000000000000000010000000000000000001000000000000000040000040000000020000000000000000000000000020000000000000000000000000000000000000000000000000000000020020000000000000000000000001000000000000000000000000000
|5,2=>0x2800000000a000000000000040000000000000000000000000000000000000000000000000000000000000000000000880000000020005000000000400002000000000000000000000040000000020
|6,0=>0x80004000010100000100100010040008800110004200020080000000040000000000008000020002000000010000040004400010000200010000640101000080000100000000d400080010000000000000002800000048a04014000200000000604100200000001200020000008802800010000200000080000010000020001400020000c000140001000006002000080000000000000080000200000000000004000000000000000002400012000040000000050084400004000000001000004000400000000000008000f8000200000040000000400008000000000000000000000018002c00000001000023000020004402020000000000000a400000001000022010000008000010000b000800002000a8000000001400000001400040000000030000040000400010000280000
|6,1=>0x8000810800000110000000044000000000202000000400110000410002000a008008000400002000500040c0100000004000401000001404000000040a00001150000200010888a8000400002000000002000110002044002001000000000000001400004008080049000100000900100000200000000080000000060000400010000280844000000010010010000200008009e00002000000040000000000100048000000009200010000300002000880004000000000000080002800820400008a08000000002200008000c0000000000000800000000400002a00004001000000000000004400000002080002000008002000100000a000000000000002000a40004000010000000210000200000000100002000840000000000005a000004009000040002a00030000000010
|6,2=>0x900000000040000300180000200030000000000400020000400000010448a02000002280000004400080000008200000000000000400028000000002000000004200084000010005000380000000008000100008000448a0a0000420020000000000000010000800088000180000008200004000100001100064040120800000000000000000000800010000000009c000000400000600001c0000100210000800004001000000000040000600100000500000000040101001010000a0000000000010002808400040000000100000244000000880004000000008008008000400020000000110800000000000478000890401000000004000020002020009000000010000000000000084080000080800000005400800100400001000000002808080004000400000000000
|6,3=>0x20880002000000884c0008000042020000044000800000000000001c8010000000000000010000081405228080005400000000100010000540000c00102000a00080000000000000000008000020000500202000800802800040000240014000000000000000009000000001100000000040088800000000000012000000000002280000429010002a0010000000000080080000020001000120002000004000544000000080020000050001000000000000040000000000100002000100208000200002000000000201000000400000000020000000010000100800000000000b00458000800011000200008800040001500003000840002000000000000008000a800000000841004001400001800200000000000000500008000420008000000808000000000000010
|6,4=>0x1000008110100002040000080000000000a00008000280004000000041c00000002000040000000200c0115002280001000000000400000000040080010150004000010001000020800220101000008100400008010440000000000000000000080040000200000040000080001d80009020b4001e800200000a400040000800022280000000000881000002200000000000000020801000000000800150010000004000000006000000000000000100500042000000000c00b504042000400002000042200000410005080000000400044000010001400208000540802000000000100058000880401801100004c00008001102008000000000001000000200000000200000000024000080004000100010000100000800010002200044000a800010000200004000000000
|6,5=>0x80000150000a0000000020040000000000140208000000000400044008000000000000000400008011500002000000802000000000e00280000000000
|7,0=>0x8000b000fc080a8001911832000a0003b810150082204014009e8402d00820010fc2089c0057804c640054013a00003c016200254081b4000d0000c41444088a000220203e0000808020101f002cc10088041f0407d8017200030003891422002210081c04000040802028802bd0406c02142003e0407c00dd810280000a0105400068043000082080d4000cc011d0206e0000e0888810060023e000340000c20b58022a0008a0039814150007e00054005aa002c010682029500028041f00046000700204c0025c002b000d2101300005008230181240489001f900200004408076003c700580007c080f88c080022a001f6009e80401008290005a028280108000aa400040020c01058027e00014005f840130014a00234000a800448806c8009c0118001158004d002b0005640020
|7,1=>0x8c4002c0019c004b2017e450000882904060003e45010080881105804970045c081f8103f000040018c0082c006600802000548082c001f8022e010543003a04112000800446008aa18090002a410540040c01958000d002a60450c10220222a002de005ac000200a3e45016008a800b72002a00075005f8010c0202200012000e80003002ea010540808821030006e081f4203a810112002a01054800ac041880222040fc009f800130023e0105480820101500020400120088900010206e040564056810050082a001ea0208100050202a400540001400120000204012008a800158000600008008ac20238203a009f200121003d0002a45016101a90047000060810c0000000818024e40011005f10029000ac100de2019800158003b002b00802000018012b00279000480081
|7,2=>0x10052282a000108a0a8100e0002a0007c000f8011f00a2b0005c8001000012285e05004028a000110204e00054000a8040f0203e010040002401150003e10004045800010000ea002560004800220203c0403a005c800150207a45022003a8013f0082a0041402080001500a2a00454801fc00090020800414008a914050083e400520888800170202a00050401cc01150016e00020021c004100004700024008a800110017e01006021080015
|8,0=>0x8002e000dc800fc08b500a3e040ba800f804379016b0017e041e8007f2003f202f40807801770083e400ad025f8143f800ee204f50056c101f840ae001de004ec01278026e040de005e8117f8022e010ca028a914377005e005fe003fc02778003f042f4008f8017f0007f202f48a0dc00bd0003f000de028ac001d
|9,0=>0x40de003bc001f0006e202f400df8001f
|10,0=>0x3f
|_,_=>0
def PM (s j : Nat) : Nat := fld (pmB s (j / 128)) 19 (j % 128)
def mkPools (s i : Nat) : List (Nat × Nat × (Nat × List Nat)) :=
  let pm := PM s i
  if pm == 0 then [] else
    let ops := PO s i
    (if pm.testBit 0 then [(dom_186,8,runOps true dom_186 (0,roots_186) ops)] else [])++(if pm.testBit 1 then [(dom_185,8,runOps true dom_185 (0,roots_185) ops)] else [])++(if pm.testBit 2 then [(dom_179,8,runOps true dom_179 (0,roots_179) ops)] else [])++(if pm.testBit 3 then [(dom_171,8,runOps true dom_171 (0,roots_171) ops)] else [])++(if pm.testBit 4 then [(dom_155,8,runOps true dom_155 (0,roots_155) ops)] else [])++(if pm.testBit 5 then [(dom_169,7,runOps true dom_169 (0,roots_169) ops)] else [])++(if pm.testBit 6 then [(dzo_185_2,6,runOps true dzo_185_2 (0,roots_185) ops)] else [])++(if pm.testBit 7 then [(dzo_171_16,6,runOps true dzo_171_16 (0,roots_171) ops)] else [])++(if pm.testBit 8 then [(dom_59,6,runOps true dom_59 (0,roots_59) ops)] else [])++(if pm.testBit 9 then [(dom_184,5,runOps true dom_184 (0,roots_184) ops)] else [])++(if pm.testBit 10 then [(dom_178,5,runOps true dom_178 (0,roots_178) ops)] else [])++(if pm.testBit 11 then [(dom_170,5,runOps true dom_170 (0,roots_170) ops)] else [])++(if pm.testBit 12 then [(dom_154,5,runOps true dom_154 (0,roots_154) ops)] else [])++(if pm.testBit 13 then [(dom_177,5,runOps true dom_177 (0,roots_177) ops)] else [])++(if pm.testBit 14 then [(dom_153,5,runOps true dom_153 (0,roots_153) ops)] else [])++(if pm.testBit 15 then [(dom_163,5,runOps true dom_163 (0,roots_163) ops)] else [])++(if pm.testBit 16 then [(dom_147,5,runOps true dom_147 (0,roots_147) ops)] else [])++(if pm.testBit 17 then [(dom_139,5,runOps true dom_139 (0,roots_139) ops)] else [])++(if pm.testBit 18 then [(dom_41,4,runOps true dom_41 (0,roots_41) ops)] else [])
def mkCut (s i : Nat) (g : Nat × Nat × Nat) (zs : List Nat) : Bool := (mkPools s i).any fun e => checkPool true e.1 e.2.1 (s - 1) (stepOp true e.1 e.2.2 g) zs
theorem mkCut_sound {s i g ys} (h : mkCut (s + 1) i g ys = true) : ¬ RunD true dom_187 goalM s ys := by
  unfold mkCut mkPools at h; dsimp only at h
  split at h
  · simp at h
  · rw [List.any_eq_true] at h
    obtain ⟨e, he, hchk⟩ := h
    simp only [List.mem_append, List.mem_ite_nil_right, List.mem_singleton, or_assoc] at he
    rcases he with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩
    · exact cpcs (by decide +kernel) low_186 _ g hchk
    · exact cpcs (by decide +kernel) low_185 _ g hchk
    · exact cpcs (by decide +kernel) low_179 _ g hchk
    · exact cpcs (by decide +kernel) low_171 _ g hchk
    · exact cpcs (by decide +kernel) low_155 _ g hchk
    · exact cpcs (by decide +kernel) low_169 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_185_2_144 _ g hchk
    · exact cpcs (by decide +kernel) lowZ_171_16_130 _ g hchk
    · exact cpcs (by decide +kernel) low_59 _ g hchk
    · exact cpcs (by decide +kernel) low_184 _ g hchk
    · exact cpcs (by decide +kernel) low_178 _ g hchk
    · exact cpcs (by decide +kernel) low_170 _ g hchk
    · exact cpcs (by decide +kernel) low_154 _ g hchk
    · exact cpcs (by decide +kernel) low_177 _ g hchk
    · exact cpcs (by decide +kernel) low_153 _ g hchk
    · exact cpcs (by decide +kernel) low_163 _ g hchk
    · exact cpcs (by decide +kernel) low_147 _ g hchk
    · exact cpcs (by decide +kernel) low_139 _ g hchk
    · exact cpcs (by decide +kernel) low_41 _ g hchk
def cutRoot (s : Nat) (ws : List Nat) : Bool := checkPool true dom_186 8 s (0, roots_186) ws
theorem cutRoot_sound {v ys} (h : cutRoot v ys = true) : ¬ RunD true dom_187 goalM v ys := by
  unfold cutRoot at h
  exact checkRootSub_sound (by decide +kernel) low_186 h
def symsG : List (List (Nat × Nat)) := [[(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)]]
theorem symsG_ok : symsG.all (fun ms => ms.all moveOK256 && (applyMoves ms dom_187 == dom_187) && (applyMoves ms goalM == goalM)) = true := by decide +kernel
def ori (zs : List Nat) : List Nat := pickMin 1 zs symsG zs (hk 1 zs)
theorem ori_ok {v ys} (h : RunD true dom_187 goalM v ys) : RunD true dom_187 goalM v (ori ys) :=
  pickMin_runD 1 ys h symsG ys (hk 1 ys) symsG_ok h
def Z (s : Nat) := barP true dom_187 goalM mpG SD SS NN htAt idxH ori 1 pool6G mkPools s
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem checkLayer0 : ∀ i < NN 0, Z 0 i = true := by
  apply chartBlocks
  intro k
  fin_cases k <;> decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem checkLayer1 : ∀ i < NN 1, Z 1 i = true := by
  apply chartBlocks
  intro k
  fin_cases k <;> decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem checkLayer2 : ∀ i < NN 2, Z 2 i = true := by
  apply chartBlocks
  intro k
  fin_cases k <;> decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem checkLayer3 : ∀ i < NN 3, Z 3 i = true := by
  apply chartBlocks
  intro k
  fin_cases k <;> decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem checkLayer4 : ∀ i < NN 4, Z 4 i = true := by
  apply chartBlocks
  intro k
  fin_cases k <;> decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem checkLayer5 : ∀ i < NN 5, Z 5 i = true := by
  apply chartBlocks
  intro k
  fin_cases k <;> decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem checkLayer6 : ∀ i < NN 6, Z 6 i = true := by
  apply chartBlocks
  intro k
  fin_cases k <;> decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem checkLayer7 : ∀ i < NN 7, Z 7 i = true := by
  apply chartBlocks
  intro k
  fin_cases k <;> decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem checkLayer8 : ∀ i < NN 8, Z 8 i = true := by
  apply chartBlocks
  intro k
  fin_cases k <;> decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem checkLayer9 : ∀ i < NN 9, Z 9 i = true := by
  apply chartBlocks
  intro k
  fin_cases k <;> decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem checkLayer10 : ∀ i < NN 10, Z 10 i = true := by
  apply chartBlocks
  intro k
  fin_cases k <;> decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checked (s : Nat) (hs : s ≤ 10) : ∀ i < NN s, bar true dom_187 goalM mpG SD SS NN htAt idxH ori 1 pool6G mkCut s i = true := by
  intro i hi; change bar _ _ _ _ _ _ _ _ _ _ _ _ (fun s' i' g zs => (mkPools s' i').any fun e => checkPool true e.1 e.2.1 (s' - 1) (stepOp true e.1 e.2.2 g) zs) s i = true; rw [← barP_eq]
  change Z s i = true
  interval_cases s
  · exact checkLayer0 i hi
  · exact checkLayer1 i hi
  · exact checkLayer2 i hi
  · exact checkLayer3 i hi
  · exact checkLayer4 i hi
  · exact checkLayer5 i hi
  · exact checkLayer6 i hi
  · exact checkLayer7 i hi
  · exact checkLayer8 i hi
  · exact checkLayer9 i hi
  · exact checkLayer10 i hi
def RootG (s : Nat) : Bool :=
  scr true dom_187 goalM s pool6G xsM || cutRoot s xsM || found SS NN idx s (ori xsM)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rootChecked : span RootG 6 5 = true := by decide +kernel
theorem proper_failG : ∀ zs ∈ xsM.sublists, zs ≠ xsM → unorientedCov pairsG zs = false := by decide +kernel
theorem noRunFull (s : Nat) (hs : s ≤ 10) (h : RunD true dom_187 goalM s xsM) : False := by
  have hmin : 5 ≤ s := by
    have hl := run_len h; change 6 ≤ s + 1 at hl; omega
  have hr := span_ok rootChecked s hmin (by omega)
  unfold RootG at hr
  rw [scr_no pool6G h, Bool.false_or, Bool.or_eq_true] at hr
  rcases hr with hcut | hf
  · exact cutRoot_sound hcut h
  · rw [found, Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hf
    exact bar_all (pairs := pairsG) (by decide +kernel) rfl rfl (by decide +kernel) (fun _ _ => rfl) (by decide +kernel) ori_ok mkCut_sound checked s hs _ hf.1 (Run.perm hf.2 (ori_ok h))
theorem noCircuit : Lower true dom_187 roots_187 goal_187 11 :=
  lower_of_search (pairs := pairsG) (by decide +kernel) proper_failG noRunFull
end S_187
end PEqualNP.Outside.L_meta_32199.Donor

namespace PEqualNP.Outside.L_meta_32199.ArchiveBridge
open PEqualNP.Outside.L_meta_32199.Donor
open PEqualNP.Outside.L_meta_32199.Contraction

def Represents (d : Nat) (src dst : List Nat) : Prop :=
  ∀ w ∈ src, ∃ v ∈ dst, v &&& d = w &&& d

theorem complementMask (d w : Nat) (hd : d &&& mask256 = d) :
    (d ^^^ w) &&& d = negD d w := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h := congrArg (fun t : Nat => t.testBit i) hd
  simp only [negD,Nat.testBit_and,Nat.testBit_xor] at h ⊢
  cases ed : d.testBit i <;> cases ew : w.testBit i <;> simp_all

theorem availability {d w : Nat} {src dst : List Nat}
    (hd : d &&& mask256 = d) (rep : Represents d src dst)
    (hw : AvBin d src w) : Avail true d dst w := by
  rcases hw with rfl | rfl | h | h
  · exact Or.inl (Or.inl (by simp))
  · exact Or.inl (Or.inr (by simp))
  · exact Or.inr (Or.inl (rep _ h))
  · obtain ⟨v,hv,he⟩ := rep _ h
    exact Or.inr (Or.inr ⟨rfl,v,hv,he.trans (complementMask d w hd)⟩)

theorem binaryToReach {d : Nat} (hd : d &&& mask256 = d)
    (roots values : List Nat) :
    ∀ (p : Nat) (src bank : List Nat), NatReach true d roots p bank →
    Represents d src bank → WordBuildsBin d src values →
    ∃ dst, NatReach true d roots (p + values.length) dst ∧ Represents d (values ++ src) dst := by
  induction values with
  | nil =>
    intro p src bank reach rep _
    exact ⟨bank,by simpa using reach,by simpa using rep⟩
  | cons out tail ih =>
    intro p src bank reach rep step
    obtain ⟨gate,rest⟩ := step
    obtain ⟨a,b,ha,hb,hout⟩ := gate
    have ff : ∃ op, allowedB true op = true ∧ opD d op a b = out &&& d := by
      rcases hout with rfl | rfl
      · exact ⟨0,rfl,rfl⟩
      · exact ⟨1,rfl,rfl⟩
    obtain ⟨op,legal,val⟩ := ff
    let u := opD d op a b
    have next : NatReach true d roots (p+1) (u::bank) :=
      ⟨bank,a,b,op,legal,rfl,reach,availability hd rep ha,availability hd rep hb⟩
    have rep' : Represents d (out::src) (u::bank) := by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ⟨u,List.mem_cons_self,by simp [u,val]⟩
      · obtain ⟨v,hv,e⟩ := rep _ hw
        exact ⟨v,List.mem_cons_of_mem _ hv,e⟩
    obtain ⟨dst,hr,hs⟩ := ih (p+1) (out::src) (u::bank) next rep' rest
    refine ⟨dst,?_,?_⟩
    · simpa [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr
    · intro w hw
      apply hs
      simpa [List.mem_append,List.mem_cons,or_assoc,or_left_comm,or_comm] using hw

theorem transfer {d g L : Nat} {roots : List Nat}
    (hd : d &&& mask256 = d) (donor : Lower true d roots g L) :
    BinLower d (roots.map (fun w => w &&& d)) (g &&& d) L := by
  intro values build hit
  have rep : Represents d (roots.map (fun w => w &&& d)) roots := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
    exact ⟨v,hv,by simp⟩
  obtain ⟨dst,reach,rep'⟩ := binaryToReach hd roots values 0 _ roots rfl rep build
  have val := availability hd rep' hit
  apply donor values.length dst (by simpa using reach)
  exact avail_of_eq (by simp) val

theorem chart187 : BinLower dom_187 (roots_187.map (fun w => w &&& dom_187)) (goal_187 &&& dom_187) 11 :=
  transfer (by decide +kernel) S_187.noCircuit

end PEqualNP.Outside.L_meta_32199.ArchiveBridge

namespace PEqualNP.Outside.L_meta_32199.Words
def m0 : Nat := 0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3
def m1 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def m2 : Nat := 0x3030303030303030303030303030303030303030303030303030303030303030
def m3 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def m4 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def m5 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00
def m6 : Nat := 0xff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ff
def m7 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00
def m8 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
def m9 : Nat := 0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff
def m10 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00
def m11 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000
def m12 : Nat := 0xffffffff000000000000000000000000ffffffff00000000
def m13 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff0000
def m14 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def m15 : Nat := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def m16 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def m17 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def m18 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def m19 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def m20 : Nat := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
def m21 : Nat := 0x9999999999999999999999999999999999999999999999999999999999999999
def m22 : Nat := 0x2222222222222222222222222222222222222222222222222222222222222222
def m23 : Nat := 0x4444444444444444444444444444444444444444444444444444444444444444
def m24 : Nat := 0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55
def m25 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa
def m26 : Nat := 0x5500550055005500550055005500550055005500550055005500550055005500
def m27 : Nat := 0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5
def m28 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def m29 : Nat := 0x5050505050505050505050505050505050505050505050505050505050505050
def m30 : Nat := 0xffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff
def m31 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff0000
def m32 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff00000000
def m33 : Nat := 0xaaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555
def m34 : Nat := 0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa
def m35 : Nat := 0x5555555500000000555555550000000055555555000000005555555500000000
def m36 : Nat := 0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333
def m37 : Nat := 0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc
def m38 : Nat := 0x3333333300000000333333330000000033333333000000003333333300000000
def m39 : Nat := 0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333
def m40 : Nat := 0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc
def m41 : Nat := 0x3333000033330000333300003333000033330000333300003333000033330000
def m42 : Nat := 0xaaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555
def m43 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa
def m44 : Nat := 0x5555000055550000555500005555000055550000555500005555000055550000
def m45 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def m46 : Nat := 0xfffffffffffffffffffffffffffffffefffefffeffeeffeefefcfaf0eeccaa00
def m47 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def m48 : Nat := 0x5500005555000055550000555500005555000055550000555500005555000055
def m49 : Nat := 0xaa005500aa005500aa005500aa005500aa005500aa005500aa005500aa0055
def m50 : Nat := 0x500000500000000050000050
def m51 : Nat := 0x5000500000000000000000000000000050005
def m52 : Nat := 0x50000500000000000000000000000000500005
def m53 : Nat := 0x10000000000000000000000000000000000000
def m54 : Nat := 0x40000000000000000000000000000000000000
def m55 : Nat := 0x100000000000000000000000000000000
def m56 : Nat := 0x400000000000000000000000000000000
def m57 : Nat := 0x500000500000000000000000000000005000005
def m58 : Nat := 0x100000000000000000000000000000000000000
def m59 : Nat := 0x5000000000000000500000000000000050000000000000005
def m60 : Nat := 0x1000000000000000000000000000000000000000000000000
def m61 : Nat := 0x10000000000000000
def m62 : Nat := 0x101000000000000010100000000000001010000000000000101
def m63 : Nat := 0x10000000000000000000000000000000000
def m64 : Nat := 0xa000500000000000a0005
def m65 : Nat := 0x30300000000000003030000
def m66 : Nat := 0x50000050000000005000005
def m67 : Nat := 0xf0f0f0f000000000f0f0f0f
def m68 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def m69 : Nat := 0x101000000000000000000000000000000000000
def m70 : Nat := 0x202010100000000000000000000000000000000
def m71 : Nat := 0x404020200000000000000000000000000000000
def m72 : Nat := 0x808040400000000000000000000000000000000
def m73 : Nat := 0x80800000000000000000000000000000000
def m74 : Nat := 0x3000000000000000300000000000000030000000000000003
def m75 : Nat := 0x200000000000000000000000000000000
def m76 : Nat := 0x30300000000000000000000000000000303
def m77 : Nat := 0x20000000000000000000000000000000000
def m78 : Nat := 0xc0300000000000000000000000000000c03
def m79 : Nat := 0x40000000000000000000000000000000000
def m80 : Nat := 0x80000000000000000000000000000000000
def m81 : Nat := 0x300300000000000000000000000000003003
def m82 : Nat := 0x100000000000000000000000000000000000
def m83 : Nat := 0x200000000000000000000000000000000000
def m84 : Nat := 0xa0005000000000000000000000000000a0005
def m85 : Nat := 0x2000000000000000000000000000000000000
def m86 : Nat := 0x8000000000000000000000000000000000000
def m87 : Nat := 0x300000300000000000000000000000003000003
def m88 : Nat := 0xf0f0f0f000000000000000000000000f0f0f0f0
def m89 : Nat := 0xf0f0f0f00000000000000000f0f0f0f00000000
def m90 : Nat := 0xf0f00f0f000000000000000000000000f0f00f0f
def m91 : Nat := 0x20000000000000000000000000000000000000
def m92 : Nat := 0x80000000000000000000000000000000000000
def m93 : Nat := 0x110000001100000000000000000000001100000011
def m94 : Nat := 0x11000000001100000000000000000000110000000011
def m95 : Nat := 0x33330000333300000000000000000000333300003333
def m96 : Nat := 0x1010000000000000000000000000000000000000000
def m97 : Nat := 0x2020000000000000000000000000000000000000000
def m98 : Nat := 0x10100000000000000000000000000000000000000000
def m99 : Nat := 0x10100000000000000000000000000000000
def m100 : Nat := 0x20200000000000000000000000000000000000000000
def m101 : Nat := 0x20200000000000000000000000000000000
def m102 : Nat := 0x101000000000000000000000000000000000
def m103 : Nat := 0x202000000000000000000000000000000000
def m104 : Nat := 0x33330000333300000000000000000000cccc0000cccc
def m105 : Nat := 0x33330000333300000000000000003333000033330000
def m106 : Nat := 0xcc330000cc3300000000000000000000cc330000cc33
def m107 : Nat := 0x4000000000000000000000000000000000000000000
def m108 : Nat := 0x10000000000000000000000000000000000000000
def m109 : Nat := 0x8000000000000000000000000000000000000000000
def m110 : Nat := 0x20000000000000000000000000000000000000000
def m111 : Nat := 0x40000000000000000000000000000000000000000000
def m112 : Nat := 0x100000000000000000000000000000000000000000
def m113 : Nat := 0x80000000000000000000000000000000000000000000
def m114 : Nat := 0x200000000000000000000000000000000000000000
def m115 : Nat := 0x1000000000000000000000000000000000
def m116 : Nat := 0xcccc0000333300000000000000000000cccc00003333
def m117 : Nat := 0x40000000000000000000000000000000000000000
def m118 : Nat := 0x400000000000000000000000000000000000000000
def m119 : Nat := 0x80000000000000000000000000000000000000000
def m120 : Nat := 0x800000000000000000000000000000000000000000
def m121 : Nat := 0x5500550055005500000000000000000055005500550055
def m122 : Nat := 0x100000000000000000000000000000000000000000000
def m123 : Nat := 0x400000000000000000000000000000000000000000000
def m124 : Nat := 0x1000000000000000000000000000000000000000000000
def m125 : Nat := 0x1000000000000000000000000000000000000
def m126 : Nat := 0x4000000000000000000000000000000000000000000000
def m127 : Nat := 0x4000000000000000000000000000000000000
def m128 : Nat := 0x4000000000000000000000000000000000
def m129 : Nat := 0x55005500550055000000000000000000aa00aa00aa00aa
def m130 : Nat := 0x5500550055005500000000000000005500550055005500
def m131 : Nat := 0xaa005500aa0055000000000000000000aa005500aa0055
def m132 : Nat := 0x200000000000000000000000000000000000000000000
def m133 : Nat := 0x800000000000000000000000000000000000000000000
def m134 : Nat := 0x2000000000000000000000000000000000000000000000
def m135 : Nat := 0x8000000000000000000000000000000000000000000000
def m136 : Nat := 0xf0f0f0f000000000f0f0f0f0
def m137 : Nat := 0xf0f0f0f000000000f0f0f0f00000000
def m138 : Nat := 0xaa00aa00550055000000000000000000aa00aa00550055
def m139 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def m140 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def m141 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def m142 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def m143 : Nat := 0xf0f0f0f000000000f0f0f0f00000000f0f0f0f000000000f0f0f0f0
def m144 : Nat := 0xf0f0f0f000000000f0f0f0f00000000000000000000000000000000
def m145 : Nat := 0xf0f0f0f000000000f0f0f0f0f0f0f0f000000000f0f0f0f00000000
def m146 : Nat := 0xcccccccccccccccc0000000000000000cccccccccccccccc
def m147 : Nat := 0xf0f0f0f00f0f0f0ff0f0f0f00f0f0f0ff0f0f0f00f0f0f0ff0f0f0f00f0f0f0f
def m148 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0
def m149 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000
end PEqualNP.Outside.L_meta_32199.Words

namespace PEqualNP.Outside.L_meta_32199.Seeds10904
open PEqualNP.Outside.L_meta_32199.Contraction

def ms2 : WordMoveStep := ([(Words.m0, 0), (Words.m1, 2)], [(Words.m2, 2)])
def ms6 : WordMoveStep := ([(Words.m3, 8)], [(Words.m4, 8)])
def ms9 : WordMoveStep := ([(0xff00ff00ff00ff0000ff00ff00ff00ffff00ff00ff00ff0000ff00ff00ff00ff, 0), (Words.m5, 56)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000, 56)])
def ms10 : WordMoveStep := ([(Words.m6, 0), (Words.m7, 24)], [(Words.m8, 24)])
def ms11 : WordMoveStep := ([(Words.m9, 0), (Words.m10, 8)], [(Words.m11, 8)])
def ms12 : WordMoveStep := ([(0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff, 0), (Words.m12, 32)], [(0xffffffff000000000000000000000000ffffffff0000000000000000, 32)])
def ms13 : WordMoveStep := ([(0xffff0000ffff00000000ffff0000ffffffff0000ffff00000000ffff0000ffff, 0), (Words.m13, 48)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000, 48)])
def sBase : List Word := [Words.m14, Words.m15, Words.m16, Words.m4, Words.m17, Words.m18, Words.m19, Words.m20]
def sGoal : Word := 0xfffffffefffffefefffefffcfefaee00fffffffefffffefefffefffcfefaee00
def s0M : Word := 0x1100110000000000110011
abbrev s0G : Word := sGoal &&& s0M
abbrev s0W : List Word := projectDAGStock s0M sBase [2, 4, 6]
def s0E := unpackWitnesses s0W [10256, 272388, 559108]
abbrev s0N : List Word := normStock s0M s0W
def s0C : List Bound := []
def s0S : DagSample := (0x50001100014201402050201100844080500814, 9)
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
def s2M : Word := 0x110011001100110011001100110011
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
def s3M : Word := 0x50005000500050005000500050005
abbrev s3G : Word := sGoal &&& s3M
abbrev s3W : List Word := projectDAGStock s3M sBase [1, 4, 5, 6]
def s3E := unpackWitnesses s3W [17440, 303168, 541698, 820226]
abbrev s3N : List Word := normStock s3M s3W
def s3C : List Bound := []
def s3S : DagSample := (0x6050201084032010c86022090882050001400042100880022011080422, 13)
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
def s6M : Word := 0x110011000000000011001100
abbrev s6G : Word := sGoal &&& s6M
abbrev s6W : List Word := projectDAGStock s6M sBase [2, 4, 6]
def s6F : Bound := (s6M, s6W, 4, s6G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Bin : BinLower s6M s6W s6G 4 := dagShiftLowerBin (width := 256) [ms6] s0Bin (by decide +kernel)
def s7M : Word := 0x11001100110011001100110011001100
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
def s12M : Word := 0x1111000011110000111100001111
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
def s14M : Word := 0x11111111111111111111111111111111
abbrev s14G : Word := sGoal &&& s14M
abbrev s14W : List Word := projectDAGStock s14M sBase [2, 3, 4, 5, 6]
def s14E := unpackWitnesses s14W [10256, 282656, 534532, 804868, 1083396]
abbrev s14N : List Word := normStock s14M s14W
def s14C : List Bound := [s2F, s12F, s6F, s13F, s7F]
def s14S : DagSample := (0x1014041a0205800070201c300906028100e00034040e0c070181c030140c140181c06130084c24110301c060909028020b000440c0a0184402070181400090c068001406038000a090680c0e00014201102050201404024080501028021104028020500824, 45)
def s14L : DagLinkList := dagExtractLinks 0xe38c70341 0x403cb84ba843304b20431023001f 6 3 12 3 1
def s14D : Forest := fun i => decodeNode 2 9 0xf396c351a7c i
def s14T := dagTraceTagsBin s14M 45 (dagTagBases s14N 0xc6e8121f99484bc52b43f5a300efccc976e03f8b90f553f947ae6c77 0x1fff8d63fff43fb0865f3f7eaf1ef7edb7fe33fffd7f77f7bf6feed7f 45) 6 s14D
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

end PEqualNP.Outside.L_meta_32199.Seeds10904

namespace PEqualNP.Outside.L_meta_32199.Seeds16531
open PEqualNP.Outside.L_meta_32199.Contraction

def ms0 : WordMoveStep := ([(Words.m21, 0), (Words.m22, 1)], [(Words.m23, 1)])
def ms1 : WordMoveStep := ([(Words.m24, 0), (Words.m25, 7)], [(Words.m26, 7)])
def ms2 : WordMoveStep := ([(Words.m27, 0), (Words.m28, 3)], [(Words.m29, 3)])
def ms3 : WordMoveStep := ([(Words.m30, 0), (Words.m31, 16)], [(Words.m32, 16)])
def ms4 : WordMoveStep := ([(0x3333333333333333333333333333333333333333333333333333333333333333, 2)], [(Words.m15, 2)])
def ms5 : WordMoveStep := ([(Words.m3, 8)], [(Words.m4, 8)])
def ms6 : WordMoveStep := ([(Words.m33, 0), (Words.m34, 31)], [(Words.m35, 31)])
def ms7 : WordMoveStep := ([(0x5555555555555555555555555555555555555555555555555555555555555555, 1)], [(Words.m14, 1)])
def ms8 : WordMoveStep := ([(Words.m36, 0), (Words.m37, 30)], [(Words.m38, 30)])
def ms9 : WordMoveStep := ([(Words.m39, 0), (Words.m40, 14)], [(Words.m41, 14)])
def ms10 : WordMoveStep := ([(Words.m9, 0), (Words.m10, 8)], [(Words.m11, 8)])
def ms11 : WordMoveStep := ([(Words.m42, 0), (Words.m43, 15)], [(Words.m44, 15)])
def ms12 : WordMoveStep := ([(Words.m6, 0), (Words.m7, 24)], [(Words.m8, 24)])
def sBase : List Word := [Words.m14, Words.m15, Words.m16, Words.m4, Words.m17, Words.m18, Words.m19, Words.m20]
def sGoal : Word := 0xeeeaeaeaeee0e0a0
def s0M : Word := 0xcc000000cc
abbrev s0G : Word := sGoal &&& s0M
abbrev s0W : List Word := projectDAGStock s0M sBase [0, 2, 5]
def s0F : Bound := (s0M, s0W, 4, s0G)
def s0E := unpackWitnesses s0W [3590, 265731, 542211]
abbrev s0N : List Word := normStock s0M s0W
def s0C : List Bound := []
def s0S : DagSample := (0x4260108c0407110980c261108c06230301c0607, 9)
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
def s1M : Word := 0x44444444
abbrev s1G : Word := sGoal &&& s1M
abbrev s1W : List Word := projectDAGStock s1M sBase [2, 3, 4]
def s1F : Bound := (s1M, s1W, 4, s1G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Bin : BinLower s1M s1W s1G 4 := dagShiftLowerBin (width := 256) [ms0, ms1, ms2, ms3, ms4, ms5] s0Bin (by decide +kernel)
def s2M : Word := 0x4444444444444444
abbrev s2G : Word := sGoal &&& s2M
abbrev s2W : List Word := projectDAGStock s2M sBase [2, 3, 4, 5]
def s2F : Bound := (s2M, s2W, 5, s2G)
def s2E := unpackWitnesses s2W [7178, 269318, 535558, 805894]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Bin : BinLower s2M s2W s2G 5 := by
  apply essentialLiftBin (witnesses := s2E) (cut := s1M)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesBinOfCheck (old := s1W) (by decide +kernel)
  · exact s1Bin
  · decide +kernel
def s3M : Word := 0xcccccccc
abbrev s3G : Word := sGoal &&& s3M
abbrev s3W : List Word := projectDAGStock s3M sBase [0, 2, 3, 4]
def s3F : Bound := (s3M, s3W, 5, s3G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s3Bin : BinLower s3M s3W s3G 5 := dagShiftLowerBin (width := 256) [ms6, ms0, ms7, ms4] s2Bin (by decide +kernel)
def s4M : Word := 0xcccc0000cccc
abbrev s4G : Word := sGoal &&& s4M
abbrev s4W : List Word := projectDAGStock s4M sBase [0, 2, 3, 5]
def s4F : Bound := (s4M, s4W, 5, s4G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Bin : BinLower s4M s4W s4G 5 := dagShiftLowerBin (width := 256) [ms1, ms0, ms8, ms9, ms7, ms4] s2Bin (by decide +kernel)
def s5M : Word := 0xcc00cc00cc00cc
abbrev s5G : Word := sGoal &&& s5M
abbrev s5W : List Word := projectDAGStock s5M sBase [0, 2, 4, 5]
def s5F : Bound := (s5M, s5W, 5, s5G)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5Bin : BinLower s5M s5W s5G 5 := dagShiftLowerBin (width := 256) [ms1, ms0, ms3, ms7, ms4] s2Bin (by decide +kernel)
def s6M : Word := 0xcccccccccccccccc
abbrev s6G : Word := sGoal &&& s6M
abbrev s6W : List Word := projectDAGStock s6M sBase [0, 2, 3, 4, 5]
def s6E := unpackWitnesses s6W [3590, 265731, 531462, 797702, 1066499]
abbrev s6N : List Word := normStock s6M s6W
def s6C : List Bound := [s3F, s2F, s4F, s5F, s1F, s0F]
def s6S : DagSample := (0x10ac243a030d8440e0105c6416010cc14230908c14160506c241b110cc441601868142b0503c24330103c642319068162b150b864360905c062b0588c06330586c260701058540e05868261b150ac0426190e864330988c140e09868040e01068543a0101c26330108c2416110980c260181c44230188c141a03058241a030380c07, 58)
def s6L : DagLinkList := dagExtractLinks 0xa0280a02719c2709c2709c2709c2528c9d64e8d607001 0x1021e27c1403d0809c05c0e01e049108b407c4c0320d0170300882403a1244a28219041088300ba1605c2a01f1200c82805c080220900ea42108208840e04e060250281181008586c4fc2621d0a10e0d0770483361221a190ed088660603b0201990808c040260001f 10 4 13 5 3
def s6D : Forest := fun i => decodeNode 4 16 0x43ce840603c502e405d305c302e301d3442204e204a20462042203b10331013101f0 i
def s6T := dagTraceTagsBin s6M 58 (dagTagBases s6N 0x1d1182c0e67c71ec3bb5c78eeb61d0bf3146d8583fe99181b665334af8c71daa23f07a49f 0x3fff7ee0cf5ef5fdfffffffffffbd3fa79e7597bbfefbb6fa67bb17afefafcf93fb4fbdbf 58) 7 s6D
def s6St := dagTraceBin s6M s6N 7 s6D
def s6Mp0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s6Mi0 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 4, 3, 5, 6, 7] 0 i.val)
def s6Mp1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 5, 4, 6, 7] 0 i.val)
def s6Mi1 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 5, 4, 6, 7] 0 i.val)
def s6Mp2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 0, 4, 6, 7] 0 i.val)
def s6Mi2 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 1, 2, 0, 5, 3, 6, 7] 0 i.val)
def s6Mp3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 1, 2, 0, 5, 3, 6, 7] 0 i.val)
def s6Mi3 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 0, 4, 6, 7] 0 i.val)
def s6Mp4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 1, 2, 5, 0, 3, 6, 7] 0 i.val)
def s6Mi4 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 1, 2, 5, 0, 3, 6, 7] 0 i.val)
def s6Mp5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def s6Mi5 (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def s6Mv := dagMoves ([([ms10], s6Mp0, s6Mi0), ([ms1, ms3], s6Mp1, s6Mi1), ([ms11, ms1, ms12], s6Mp2, s6Mi2), ([ms1, ms6, ms11], s6Mp3, s6Mi3), ([ms11, ms12], s6Mp4, s6Mi4), ([ms6], s6Mp5, s6Mi5)] : List (DagMoveRecord 256))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6A : DagMovesOK s6M s6G 256 s6Mv := dagMovesOfCheck (by decide +kernel)
def s6NB : Nat → List Bound := dagNodeBounds s6C.toArray 0x11088442130180401e4e27038188b2469946c06 0x19811688663444688b1a22c688 9 3 3
def s6Ck := dagCheckNodeBin s6M s6G s6NB 17 s6St s6Mv s6L s6S s6T
def s6RA (token : Nat) : Bool :=
  let s := rootState s6N 7 token
  !dagAllowedRootBin s6M s6E s.2.1 || dagLocalBin s6M s6G (dagKnownClosesBin s6G s6C) s ||
  dagRefBin s6M 17 s6St s6Mv (fun p tok => dagFindLink (s6L p) tok) 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6RB0 : treeBlock 0 32 s6RA = true := by decide +kernel
theorem s6RV : treeBlock 0 32 s6RA = true := s6RB0
theorem s6R : dagCheckRootsBin s6M s6G (dagKnownClosesBin s6G s6C) s6E (dagRefBin s6M 17 s6St s6Mv (fun p tok => dagFindLink (s6L p) tok) 0) s6N 7 = true := s6RV
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Bl0 : treeBlock 0 17 s6Ck = true := by decide +kernel
theorem s6Bk : treeBlock 0 17 s6Ck = true := s6Bl0
theorem s6K : KnownBin s6C := (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (extendKnownBin (show KnownBin [] from fun _ h => False.elim (List.not_mem_nil h)) s0Bin) s1Bin) s5Bin) s4Bin) s2Bin) s3Bin)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Bin : BinLower s6M s6W s6G 8 := by
  apply lowerDagBin _ _ _ _ s6A _ _ _ s6K _ (fun _ b hb => dagNodeBounds_mem b hb) s6R s6Bk
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s6C, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

end PEqualNP.Outside.L_meta_32199.Seeds16531

namespace PEqualNP.Outside.L_meta_32199.DeepRows
open PEqualNP.Outside.L_meta_32199.Contraction
def raw : List Word := [Words.m14,Words.m15,Words.m16,Words.m4,Words.m17,Words.m18,Words.m19,Words.m20]
def full : Word := Words.m45
def goal : Word := Words.m46
def column (i : Nat) : Word := raw.getD i 0
def swapRows (i j : Nat) : WordMoveStep :=
  let lo := column i &&& (full ^^^ column j)
  let hi := column j &&& (full ^^^ column i)
  let k := 2^j - 2^i
  ([(full ^^^ (lo ||| hi),0),(lo,k)],[(hi,k)])
def flipRows (i : Nat) : WordMoveStep := ([(full ^^^ column i,2^i)],[(column i,2^i)])
def clearRows (i : Nat) : WordMoveStep := ([(full ^^^ column i,0)],[(column i,2^i)])
def oldMask : Word := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def oldGoal : Word := 0xf0f0f0f0f0f0f0e00000000000000000f0e0f0a0e0c0a00
def oldRoots : List Word := [0xa0a0a0a0a0a0a0a00000000000000000a0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c,0xf000f000f000f0000000000000000000f000f000f000f00,0xf0f00000f0f000000000000000000000f0f00000f0f0000,0xf0f0f0f0000000000000000000000000f0f0f0f00000000,0xf0f0f0f0f0f0f0f00000000000000000000000000000000]
abbrev Prior := BinLower oldMask oldRoots oldGoal 11
def atMask (m : Word) : Prop := BinLower m (raw.map (fun w => w &&& m)) (goal &&& m) 11
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem transport0 (prior : Prior) : atMask 0x2222111122221111222211112222111122221111222211112222111122221111 :=
  dagShiftLowerBin (width := 254) [swapRows 1 2,swapRows 4 5,swapRows 5 6,clearRows 6] prior (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem transport1 (prior : Prior) : atMask 0x3030030330300303303003033030030330300303303003033030030330300303 :=
  dagShiftLowerBin (width := 254) [swapRows 1 2,swapRows 4 5,swapRows 5 6,clearRows 6] prior (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem transport2 (prior : Prior) : atMask 0x3300003333000033330000333300003333000033330000333300003333000033 :=
  dagShiftLowerBin (width := 254) [swapRows 1 2,swapRows 4 5,swapRows 5 6,clearRows 6] prior (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem transport3 (prior : Prior) : atMask 0x3333000000003333333300000000333333330000000033333333000000003333 :=
  dagShiftLowerBin (width := 254) [swapRows 1 2,swapRows 5 6,clearRows 6] prior (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem transport4 (prior : Prior) : atMask 0x3333000033330000000033330000333333330000333300000000333300003333 :=
  dagShiftLowerBin (width := 254) [swapRows 1 2,swapRows 4 5,clearRows 6] prior (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem transport5 (prior : Prior) : atMask Words.m47 :=
  dagShiftLowerBin (width := 238) [swapRows 1 2,swapRows 4 5,swapRows 5 6] prior (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem transport6 (prior : Prior) : atMask 0x333300003333000033330000333333330000333300003333000033330000 :=
  dagShiftLowerBin (width := 238) [swapRows 1 2,swapRows 4 5,swapRows 5 6,clearRows 6] prior (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem transport7 (prior : Prior) : atMask Words.m48 :=
  dagShiftLowerBin (width := 255) [swapRows 0 1,swapRows 1 2,swapRows 4 5,swapRows 5 6,clearRows 6] prior (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem transport8 (prior : Prior) : atMask 0x8822441188224411882244118822441188224411882244118822441188224411 :=
  dagShiftLowerBin (width := 256) [swapRows 1 2,swapRows 4 5,swapRows 5 6,clearRows 2,clearRows 6] prior (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem transport9 (prior : Prior) : atMask 0x9900009999000099990000999900009999000099990000999900009999000099 :=
  dagShiftLowerBin (width := 256) [swapRows 1 2,swapRows 4 5,swapRows 5 6,clearRows 2,clearRows 6] prior (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem transport10 (prior : Prior) : atMask 0x9999000099990000000099990000999999990000999900000000999900009999 :=
  dagShiftLowerBin (width := 256) [swapRows 1 2,swapRows 4 5,clearRows 2,clearRows 6] prior (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem transport11 (prior : Prior) : atMask 0x999900009999000099990000999900009999000099990000999900009999 :=
  dagShiftLowerBin (width := 240) [swapRows 1 2,swapRows 4 5,swapRows 5 6,clearRows 2] prior (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem transport12 (prior : Prior) : atMask Words.m49 :=
  dagShiftLowerBin (width := 248) [swapRows 1 2,swapRows 2 3,swapRows 4 5,swapRows 5 6,clearRows 6] prior (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem transport13 (prior : Prior) : atMask 0xcc330000cc3300000000cc330000cc33cc330000cc3300000000cc330000cc33 :=
  dagShiftLowerBin (width := 256) [swapRows 1 2,swapRows 4 5,clearRows 2,clearRows 6] prior (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem transport14 (prior : Prior) : atMask 0xcc330000cc330000cc330000cc330000cc330000cc330000cc330000cc33 :=
  dagShiftLowerBin (width := 240) [swapRows 1 2,swapRows 4 5,swapRows 5 6,clearRows 2] prior (by decide +kernel)
end PEqualNP.Outside.L_meta_32199.DeepRows

namespace PEqualNP.Outside.L_meta_32199.DeepRows
theorem verifiedPrior : Prior := ArchiveBridge.chart187
end PEqualNP.Outside.L_meta_32199.DeepRows

namespace PEqualNP.Outside.L_meta_32199.RowBank
open PEqualNP.Outside.L_meta_32199.Contraction
open PEqualNP.Outside.L_meta_32199.DeepRows
def boundAt (m n : Nat) := BinLower m (raw.map (fun w => w &&& m)) (goal &&& m) n
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row0 : boundAt Words.m50 4 :=
  dagShiftLowerBin (width := 95) [([],[(0x100000000000000010000000,12),(0x400000000000000040000000,10),(0x100000000000000010,4),(0x400000000000000040,2)])] Seeds10904.s0Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row1 : boundAt Words.m51 4 :=
  dagShiftLowerBin (width := 147) [([(0x10001,0),(0x40004,2)],[(0x1000100000000000000000000000000000000,64),(0x4000400000000000000000000000000000000,62)])] Seeds10904.s0Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row2 : boundAt Words.m52 4 :=
  dagShiftLowerBin (width := 151) [([(0x1,0),(0x4,2)],[(Words.m53,68),(Words.m54,66),(Words.m55,64),(Words.m56,62),(0x100000,4),(0x400000,2)])] Seeds10904.s0Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3 : boundAt Words.m57 4 :=
  dagShiftLowerBin (width := 155) [([(0x1,0),(0x4,2)],[(Words.m58,72),(0x400000000000000000000000000000000000000,70),(Words.m55,64),(Words.m56,62),(0x1000000,8),(0x4000000,6)])] Seeds10904.s0Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row4 : boundAt Words.m59 4 :=
  dagShiftLowerBin (width := 195) [([(0x1,0),(0x4,2)],[(Words.m60,112),(0x4000000000000000000000000000000000000000000000000,110),(Words.m55,64),(Words.m56,62),(Words.m61,48),(0x40000000000000000,46)])] Seeds10904.s0Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row5 : boundAt Words.m62 4 :=
  dagShiftLowerBin (width := 201) [([(0x1,0)],[(0x100000000000000000000000000000000000000000000000000,116),(Words.m60,112),(Words.m63,68),(Words.m55,64),(0x1000000000000000000,52),(Words.m61,48),(0x100,4)])] Seeds10904.s0Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row6 : boundAt 0x3030000000000000303 4 :=
  dagShiftLowerBin (width := 74) [([(0x10000000000000001,0),(0x20000000000000002,3),(0x1000000000000000100,8),(0x2000000000000000200,11)],[])] Seeds10904.s0Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row7 : boundAt Words.m64 4 :=
  dagShiftLowerBin (width := 84) [([(0x10000000000000001,0),(0x800000000000000080000,1),(0x40000000000000004,14)],[(0x200000000000000020000,13)])] Seeds10904.s0Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row8 : boundAt Words.m65 4 :=
  dagShiftLowerBin (width := 90) [([],[(0x100000000000000010000,16),(0x200000000000000020000,13),(0x10000000000000001000000,8),(0x20000000000000002000000,5)])] Seeds10904.s0Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row9 : boundAt Words.m66 4 :=
  dagShiftLowerBin (width := 91) [([(0x10000000000000001,0),(0x40000000000000004,2)],[(0x10000000000000001000000,8),(0x40000000000000004000000,6)])] Seeds10904.s0Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row10 : boundAt Words.m67 7 :=
  dagShiftLowerBin (width := 92) [([(0x1,0),(0x20000000000000000000000,3),(0x20000,7),(0x2000000000000000000,11),(0x2,15),(0x40000000000000000000000,18),(0x40000,22),(0x4000000000000000000,26),(0x4,30),(0x80000000000000000000000,33),(0x80000,37),(0x8000000000000000000,41),(0x8,45),(0x1000000,48),(0x100,56),(0x2000000,63),(0x200,71),(0x4000000,78),(0x400,86),(0x8000000,93),(0x800,101)],[(0x100000000000000000000,68),(Words.m61,60),(0x200000000000000000000,53),(0x20000000000000000,45),(0x400000000000000000000,38),(0x40000000000000000,30),(0x800000000000000000000,23),(0x80000000000000000,15),(0x10000000000000000000000,12),(0x10000,8),(0x1000000000000000000,4)])] Seeds10904.s14Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row11 : boundAt Words.m68 8 :=
  dagShiftLowerBin (width := 156) [([(0x2020101,2),(0x4040202,17),(0x8080404,32),(0x808,47)],[(Words.m69,137),(Words.m70,122),(Words.m71,107),(Words.m72,92),(Words.m73,77),(0x1010000,13)])] Seeds16531.s6Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row12 : boundAt Words.m74 4 :=
  dagShiftLowerBin (width := 194) [([(0x1,0),(0x2,3)],[(Words.m60,112),(0x2000000000000000000000000000000000000000000000000,109),(Words.m55,64),(Words.m75,61),(Words.m61,48),(0x20000000000000000,45)])] Seeds10904.s0Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row13 : boundAt Words.m76 4 :=
  dagShiftLowerBin (width := 138) [([(0x1,0),(0x2,3),(0x100,8),(0x200,11)],[(Words.m55,64),(Words.m75,61),(Words.m63,56),(Words.m77,53)])] Seeds10904.s0Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row14 : boundAt Words.m78 4 :=
  dagShiftLowerBin (width := 140) [([(0x1,0),(0x2,3),(0x400,6),(0x800,9)],[(Words.m55,64),(Words.m75,61),(Words.m79,58),(Words.m80,55)])] Seeds10904.s0Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row15 : boundAt Words.m81 4 :=
  dagShiftLowerBin (width := 142) [([(0x1,0),(0x2,3),(0x1000,4),(0x2000,7)],[(Words.m55,64),(Words.m75,61),(Words.m82,60),(Words.m83,57)])] Seeds10904.s0Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row16 : boundAt Words.m84 4 :=
  dagShiftLowerBin (width := 148) [([(0x1,0),(0x80000,1),(0x4,14)],[(Words.m85,77),(Words.m55,64),(Words.m86,63),(Words.m56,50),(0x20000,13)])] Seeds10904.s0Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row17 : boundAt Words.m87 4 :=
  dagShiftLowerBin (width := 154) [([(0x1,0),(0x2,3)],[(Words.m58,72),(0x200000000000000000000000000000000000000,69),(Words.m55,64),(Words.m75,61),(0x1000000,8),(0x2000000,5)])] Seeds10904.s0Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row18 : boundAt Words.m88 8 :=
  dagShiftLowerBin (width := 156) [([(0x40402020,13),(0x80804040,28),(0x8080,43)],[(Words.m69,137),(Words.m70,122),(Words.m71,107),(Words.m72,92),(Words.m73,77),(0x10100000,17),(0x20201010,2)])] Seeds16531.s6Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row19 : boundAt Words.m89 8 :=
  dagShiftLowerBin (width := 156) [([(0x808040400000000,0),(0x80800000000,15)],[(Words.m69,137),(Words.m70,122),(Words.m71,107),(Words.m72,92),(Words.m73,77),(0x101000000000000,45),(0x202010100000000,30),(0x404020200000000,15)])] Seeds16531.s6Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row20 : boundAt Words.m90 8 :=
  dagShiftLowerBin (width := 160) [([(0x1,2),(0x400000,4),(0x400,9),(0x20000000,14),(0x4,16),(0x200000,21),(0x200,26),(0x80000000,28),(0x2,33),(0x800000,35),(0x800,40),(0x8,47)],[(0x1000000000000000000000000000000000000000,141),(Words.m53,134),(Words.m63,129),(0x4000000000000000000000000000000000000000,127),(Words.m55,122),(Words.m54,120),(Words.m79,115),(0x2000000000000000000000000000000000000000,110),(Words.m56,108),(Words.m91,103),(Words.m77,98),(0x8000000000000000000000000000000000000000,96),(Words.m75,91),(Words.m92,89),(Words.m80,84),(0x800000000000000000000000000000000,77),(0x10000000,17),(0x100000,10),(0x100,5),(0x40000000,3)])] Seeds16531.s6Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row21 : boundAt Words.m93 4 :=
  dagShiftLowerBin (width := 165) [([(0x11,0)],[(0x110000000000000000000000000000000000000000,80),(0x1100000000000000000000000000000000,64),(0x1100000000,16)])] Seeds10904.s0Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row22 : boundAt Words.m94 4 :=
  dagShiftLowerBin (width := 173) [([(0x11,0)],[(0x11000000000000000000000000000000000000000000,88),(0x1100000000000000000000000000000000,64),(0x110000000000,24)])] Seeds10904.s0Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row23 : boundAt Words.m95 8 :=
  dagShiftLowerBin (width := 174) [([(0x101,2),(0x202000000000,14),(0x202,17),(0x1010,30),(0x2020,45)],[(Words.m96,153),(Words.m97,138),(Words.m98,125),(Words.m99,122),(Words.m100,110),(Words.m101,107),(Words.m102,94),(Words.m103,79),(0x10100000000,29),(0x20200000000,14),(0x101000000000,1)])] Seeds16531.s6Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row24 : boundAt Words.m104 8 :=
  dagShiftLowerBin (width := 174) [([(0x404,0),(0x808000000000,12),(0x808,15),(0x4040,28),(0x8080,43)],[(Words.m96,153),(Words.m97,138),(Words.m98,125),(Words.m99,122),(Words.m100,110),(Words.m101,107),(Words.m102,94),(Words.m103,79),(0x40400000000,31),(0x80800000000,16),(0x404000000000,3)])] Seeds16531.s6Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row25 : boundAt Words.m105 8 :=
  dagShiftLowerBin (width := 174) [([(0x2020000,1),(0x10100000,14),(0x20200000,29)],[(Words.m96,153),(Words.m97,138),(Words.m98,125),(Words.m99,122),(Words.m100,110),(Words.m101,107),(Words.m102,94),(Words.m103,79),(0x101000000000000,45),(0x202000000000000,30),(0x1010000000000000,17),(0x1010000,14),(0x2020000000000000,2)])] Seeds16531.s6Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row26 : boundAt Words.m106 8 :=
  dagShiftLowerBin (width := 176) [([(0x400,0),(0x1,2),(0x800000000000,12),(0x2000000000,14),(0x800,15),(0x2,17),(0x4000,28),(0x10,30),(0x8000,43),(0x20,45)],[(Words.m107,155),(Words.m108,153),(Words.m109,140),(Words.m110,138),(Words.m111,127),(Words.m112,125),(Words.m79,124),(Words.m55,122),(Words.m113,112),(Words.m114,110),(Words.m80,109),(Words.m75,107),(0x400000000000000000000000000000000000,96),(Words.m115,94),(0x800000000000000000000000000000000000,81),(0x2000000000000000000000000000000000,79),(0x40000000000,31),(0x100000000,29),(0x80000000000,16),(0x200000000,14),(0x400000000000,3),(0x1000000000,1)])] Seeds16531.s6Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row27 : boundAt Words.m116 8 :=
  dagShiftLowerBin (width := 176) [([(0x1,2),(0x10,6),(0x80000000000,8),(0x800000000000,12),(0x800000000,15),(0x8000000000,19),(0x200,26),(0x2000,30),(0x2,33),(0x20,37)],[(Words.m107,147),(Words.m111,143),(Words.m117,140),(Words.m118,136),(Words.m63,129),(Words.m82,125),(Words.m55,122),(Words.m115,118),(Words.m109,116),(Words.m113,112),(Words.m119,109),(Words.m120,105),(Words.m77,98),(Words.m83,94),(Words.m75,91),(0x2000000000000000000000000000000000,87),(0x40000000000,23),(0x400000000000,19),(0x400000000,16),(0x4000000000,12),(0x100,5),(0x1000,1)])] Seeds16531.s6Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row28 : boundAt Words.m121 8 :=
  dagShiftLowerBin (width := 183) [([(0x1,2),(0x40000000000000,5),(0x40000,8),(0x4000000000,13),(0x4,16),(0x100000,22),(0x10,30),(0x400000,36),(0x40,44)],[(Words.m122,161),(Words.m108,153),(Words.m123,147),(Words.m117,139),(Words.m124,133),(Words.m125,130),(Words.m112,125),(Words.m55,122),(Words.m126,119),(Words.m127,116),(Words.m118,111),(Words.m56,108),(Words.m53,102),(Words.m115,94),(Words.m54,88),(Words.m128,80),(0x1000000000000,37),(0x100000000,29),(0x4000000000000,23),(0x400000000,15),(0x10000000000000,9),(0x10000,6),(0x1000000000,1)])] Seeds16531.s6Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row29 : boundAt Words.m129 8 :=
  dagShiftLowerBin (width := 183) [([(0x2,1),(0x80000000000000,4),(0x80000,7),(0x8000000000,12),(0x8,15),(0x200000,21),(0x20,29),(0x800000,35),(0x80,43)],[(Words.m122,161),(Words.m108,153),(Words.m123,147),(Words.m117,139),(Words.m124,133),(Words.m125,130),(Words.m112,125),(Words.m55,122),(Words.m126,119),(Words.m127,116),(Words.m118,111),(Words.m56,108),(Words.m53,102),(Words.m115,94),(Words.m54,88),(Words.m128,80),(0x2000000000000,38),(0x200000000,30),(0x8000000000000,24),(0x800000000,16),(0x20000000000000,10),(0x20000,7),(0x2000000000,2)])] Seeds16531.s6Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row30 : boundAt Words.m130 8 :=
  dagShiftLowerBin (width := 183) [([(0x4000000,0),(0x400000000000,5),(0x400,8),(0x10000000,14),(0x1000,22),(0x40000000,28),(0x4000,36)],[(Words.m122,161),(Words.m108,153),(Words.m123,147),(Words.m117,139),(Words.m124,133),(Words.m125,130),(Words.m112,125),(Words.m55,122),(Words.m126,119),(Words.m127,116),(Words.m118,111),(Words.m56,108),(Words.m53,102),(Words.m115,94),(Words.m54,88),(Words.m128,80),(0x100000000000000,45),(0x10000000000,37),(0x400000000000000,31),(0x40000000000,23),(0x1000000000000000,17),(0x1000000,14),(0x100000000000,9),(0x100,6),(0x4000000000000000,3)])] Seeds16531.s6Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row31 : boundAt Words.m131 8 :=
  dagShiftLowerBin (width := 184) [([(0x20000,1),(0x1,2),(0x80000000000000,4),(0x4000000000,5),(0x80000,7),(0x4,8),(0x200000,29),(0x10,30),(0x800000,35),(0x40,36)],[(Words.m132,154),(Words.m108,153),(Words.m133,148),(Words.m117,147),(Words.m134,126),(Words.m112,125),(Words.m85,123),(Words.m55,122),(Words.m135,120),(Words.m118,119),(Words.m86,117),(Words.m56,116),(Words.m91,95),(Words.m115,94),(Words.m92,89),(Words.m128,88),(0x2000000000000,30),(0x100000000,29),(0x8000000000000,24),(0x400000000,23),(0x20000000000000,2),(0x1000000000,1)])] Seeds16531.s6Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row32 : boundAt 0xa000500000000000a00050 4 :=
  dagShiftLowerBin (width := 88) [([(0x400000000000000040,10)],[(0x2000000000000000200000,17),(0x100000000000000010,4),(0x8000000000000000800000,3)])] Seeds10904.s0Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row33 : boundAt Words.m136 7 :=
  dagShiftLowerBin (width := 96) [([(0x200000,3),(0x20000000000000000000,7),(0x20,11),(0x400000000000000000000000,14),(0x400000,18),(0x40000000000000000000,22),(0x40,26),(0x800000000000000000000000,29),(0x800000,33),(0x80000000000000000000,37),(0x80,41),(0x10000000,44),(0x1000,52),(0x20000000,59),(0x2000,67),(0x40000000,74),(0x4000,82),(0x80000000,89),(0x8000,97)],[(0x1000000000000000000000,72),(0x100000000000000000,64),(0x2000000000000000000000,57),(0x200000000000000000,49),(0x4000000000000000000000,42),(0x400000000000000000,34),(0x8000000000000000000000,27),(0x800000000000000000,19),(0x100000000000000000000000,16),(0x100000,12),(0x10000000000000000000,8),(0x10,4),(0x200000000000000000000000,1)])] Seeds10904.s14Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row34 : boundAt Words.m137 7 :=
  dagShiftLowerBin (width := 124) [([(0x8000000000000000000000000000000,1),(0x8000000000000,5),(0x800000000000000000000000000,9),(0x800000000,13),(0x100000000000000,16),(0x10000000000,24),(0x200000000000000,31),(0x20000000000,39),(0x400000000000000,46),(0x40000000000,54),(0x800000000000000,61),(0x80000000000,69)],[(0x10000000000000000000000000000,100),(0x1000000000000000000000000,92),(0x20000000000000000000000000000,85),(0x2000000000000000000000000,77),(0x40000000000000000000000000000,70),(0x4000000000000000000000000,62),(0x80000000000000000000000000000,55),(0x8000000000000000000000000,47),(0x1000000000000000000000000000000,44),(0x1000000000000,40),(0x100000000000000000000000000,36),(0x100000000,32),(0x2000000000000000000000000000000,29),(0x2000000000000,25),(0x200000000000000000000000000,21),(0x200000000,17),(0x4000000000000000000000000000000,14),(0x4000000000000,10),(0x400000000000000000000000000,6),(0x400000000,2)])] Seeds10904.s14Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row35 : boundAt Words.m138 8 :=
  dagShiftLowerBin (width := 184) [([(0x8000000000000,0),(0x1,2),(0x80000000000000,4),(0x10,6),(0x800000000,15),(0x40000,17),(0x8000000000,19),(0x400000,21),(0x4,32),(0x40,36)],[(Words.m132,154),(Words.m134,150),(Words.m110,139),(Words.m125,137),(Words.m114,135),(Words.m53,133),(Words.m133,124),(Words.m55,122),(Words.m135,120),(Words.m115,118),(Words.m119,109),(Words.m127,107),(Words.m120,105),(Words.m54,103),(Words.m56,92),(Words.m128,88),(0x2000000000000,30),(0x20000000000000,26),(0x200000000,15),(0x10000,13),(0x2000000000,11),(0x100000,9)])] Seeds16531.s6Bin (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row36 (prior : boundAt Words.m139 12) : boundAt Words.m139 12 :=
  prior
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row37 (prior : boundAt Words.m140 9) : boundAt Words.m141 9 :=
  dagShiftLowerBin (width := 216) [([(0x550055000000000055005500000000005500550000000000550055,0),(0xaa00aa0000000000aa00aa0000000000aa00aa0000000000aa00aa,7)],[])] prior (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row38 (prior : boundAt Words.m142 10) : boundAt Words.m142 10 :=
  prior
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row39 (prior : boundAt Words.m142 10) : boundAt Words.m143 10 :=
  dagShiftLowerBin (width := 220) [([(Words.m144,0)],[(Words.m136,4)])] prior (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row40 (prior : boundAt Words.m142 10) : boundAt Words.m145 10 :=
  dagShiftLowerBin (width := 220) [([(Words.m144,0)],[(Words.m137,32)])] prior (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row41 (prior : boundAt Words.m140 9) : boundAt Words.m140 9 :=
  prior
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row42 : boundAt Words.m47 11 :=
  DeepRows.transport5 DeepRows.verifiedPrior
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row43 : boundAt Words.m49 11 :=
  DeepRows.transport12 DeepRows.verifiedPrior
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row44 : boundAt Words.m48 11 :=
  DeepRows.transport7 DeepRows.verifiedPrior
end PEqualNP.Outside.L_meta_32199.RowBank

namespace PEqualNP.Outside.L_meta_32199.Native.Cut9
open PEqualNP.Outside.L_meta_32199.Contraction

def globalRaw : List Word := [Words.m14,Words.m15,Words.m16,Words.m4,Words.m17,Words.m18,Words.m19,Words.m20]
def globalGoal : Word := Words.m46
def raw : List Word := [0x44444444000000004444444400000000444444440000000044444444,0x50505050000000005050505000000000505050500000000050505050,0x55005500000000005500550000000000550055000000000055005500,0x55550000000000005555000000000000555500000000000055550000,0x55555555000000000000000000000000555555550000000000000000,0x55555555000000005555555500000000000000000000000000000000]
def goal : Word := 0x55555555000000005555555400000000554455440000000044440000
def cut (m lb : Nat) : Bound := (m, globalRaw.map (fun w => w &&& m), lb, globalGoal &&& m)
def bounds : List Bound := [cut Words.m50 4,cut Words.m51 4,cut Words.m52 4,cut Words.m57 4,cut Words.m59 4,cut Words.m62 4]
abbrev mask : Word := Words.m140
def stock : List Word := normStock mask raw
def essential := unpackWitnesses raw [9232, 329856, 561216, 795650, 1082370, 1377282]
def forest : Forest := decodeNode 8 21 0x3102d888155050a06284fc142698a132850992284b90f23189d1445c86226431122160b906c508362140a13a050850283d8122e401132008790044c7e41c3e9131e98a0e6848730223780d1b0848d68406a42834c141958a0cac50624242fc171798a08ec5044420a200a5120c086c604343021c149058a48245e41229208055050a07e8603e4281e81b0f40b87a04c3d2149d9130e50a47045e382291c1134e08987043e3862c1b2160d88b06d05e356291aa148d50946a848352249a9104d485262c5030418179130bc89252421296281420c0a18c04c858268291291789487c4a044228301041487d8a03d0521d6290ea104748543a4261d2100e21806d0a0368301b4180d1080650603003c184180bc178598a42c849164280aa0c0540b82b0521462f0a31485188228841140268a3140480d82404c120128891443c0321e44c0e00a871148358a0164510b2280580642e0a414c520a42905117c288a6144410a00f85006c2802e140130a425842124208a61044b082248410a42084610421084200391001c0b80c850052188290a4158a00885104418821174100ba0805c040170241880c8dc064500321f01d1880a0c404c5102431012140090640483002237011188088ba0406e02031010174080b80404d020260100f808064048490142080914c04892024410121480908c048420204f01026808114040860202f0101180807c040260203f00
def links : DagLinkList := dagExtractLinks 0xc403100c403100c403100c4030e1c3830e0c3830e0c3830e0c3070a1c283081c203080c203080c203080c203080c203080c203061c183060c183060c183060c183060be9af81bd86f60bd82f60bc8aee2ba8aea0b98ae41b886e20b882e20b882e01b802de1b68ad24b406cc2b302ca1b282c62af92b83ac8eb20aa92a43a8869e2a7069c0a7029a1a6829a0a6829a0a682981a50a940a40a900a30a8c0a286843a00a7e19f067c09f027a19d8a7609d827419d027409c0a6e19b826e09b826e09b826e09b826e09b826e09b826e09b826e09a8a662998266099825e497825e0970652590a23288b0e2a18626142840a0c280960207f0df257b89daa7681d247025c007001c006f09b826d09b026c01ac26b01ac06a09a42678d9a2650d940638d7e85e0d7425b8d6c15531521521544250093844d092e34a0d1c6470116345050a53e24f42399ce4134a4b6e2d808971f947c11d8c668171439200ec001 0x6280c18c8486321018cc4062910384c41622105844415c0135860295200858905061b14184c506091718505060117182c506021417e4505480c1504305380c162830dcc14374c405b10836b0505aa0c37c44c5f10f1688305eb13b74c4258a0e17845c5d91336ec505ca1416a8405d11236f05c5c21416e8485cc17170c505aa1216ec425b21396a8425a20f56645c5911316243c5790f15e8305811315e8385711315a45c56b1415884855910154420d31141560445311414a450520141540345410e1524245421014e850d341414d05052b14148c50513141468485141733f4604fb1033d0604f20c0f803d3680854201929004542c504e91752e441b70146e604d36008734c415021433883a4e117534441b581450604d35808540c504fa1053645d4c9106de0514101353c0293080853b0604e3181368604b9141350524cb1493045e4b9148d40314a80a5260213f00752c0153f1140f643c4aa140d24304a2180d003049a1412406c4881712004c3b00f10e4314790a50a421c6d1b30506046a16104830459161028304711330905246a1490c8324020c11845e4591491444d4491311043e4290c90ec583e31410c8584291610905eb9c14906c524121490284a402120fe4493f1104c60213e10c4fa4293e3140f68383da0c0f444c3b80b8a40223c0170ec03c3c9124f04213bb140ec8303a91b0e6450b38180eac603a2160e7052391178e243e3620c2ca4602c0130de860372140d6830b21182c20602e8170ac04c380110da8402a0170a404037c180cc460374148ca4522d8134dac50364148d6c52352104ce45e321148c644d3490a8d0426310178c20522f8134b403d339082cb460b24180cc86032a140c883031a0c0a604c2b3140c4420b0c180c2830b00130c003c2fa0c0b204c2f4178bac522e2124b68502d20c0b205c2c4148aec5e2b3148aac412a2104a604d293140a206c2801309e0252490c48e4211680c46002d10004e8706021a0c09c4512511423e0611c81743e0212680642e01126113096015a2c148944522390ca440531600cc3c0211200746c04d24b140904512391406a05d1780f4560310e80848c0190880448b0522231488685221117c824532011064c05f90814c6804d0e00847e01f1f006c7a0171e004e7105f9bc17a490529b317a6ac539a314a76c4b9d312660c411da12c74849182104724531c112c6e4491211046c4291a908c684218c814e5403315008c3201399414266c4019a100644401881346205c1821405e4311710a45ac50162144568311511745205d1401704e02e0880884d0621291b8484501190fa36062115188430621031443e8620f21403a8320e20c03646e0d11883245d0c01b82e0620b01742a05c0a01342604c0900f82203286c17a1905285b17a14c5384b14a20c4987b1042084907a1041c453069124184410590a4144230490860405f80814c1004f0381340c04502810e0803f8180cc0802f01808c0401f00804c0003f 14 5 13 8 1
def nodeBounds : Nat → List Bound := dagNodeBounds bounds.toArray 0x1a83506a0d41a6748e90d21a4348690d21a4348690d21a4348690d21a4348690d21a4348690d21a2740e80d01a0340679cf19e33c66acc39832ce51ca192720e39c6388b10620c338630c618c318630c618c3186308e10c2184308610c2184304e01c0180300600bf37e2fc5f8be37c2f4de8bd17a2f45e1bc1766e8dc9b91706e05b9b716c6d4da8b43666c8d90b13622c4588b035e6bc578af15e2bc578af15c6b8570ab752a9d52aa3540e794e29972ea5549a9151ea38c628b312a1641a822fedf8be27a4f09d93a2724e09b935b6a2d0999322624c09792db594b05592a25249ed38a624b292919a22432845011f23c4748e11b9362688c91822c852c9d1232243ec750d31682884586c0980cc0d803 0x91390b52c963a494a228c60150956c55b14d348aa2a1354d34d56a5158d542c008229821aa9a6c082a020820ac0158080a91600440a1088220208242a2ab02a45348a6914d22c229a45815815229161 11 3 3
def sample : DagSample := (0x7121009440310208420310141a0622000c0000482012282402094002400c8428148304828048308803048888402210301a05128041201208305820300a0580c2600c462211900c00723900904022100820e1701c1e2a35100840e078884c, 42)
def tags := dagTraceTagsBin mask 42 (dagTagBases stock 0xfb3d58796b61faf9fe5c079feb9a7532ec156a9ec556fcfd88f5a130e9d5833 0x7bfbdc7b7bdf7ef1fe5c479feb9b7737be30ee9fd5f7dd6fcdfda7ffffffa3b 42) 8 forest
def states := dagTraceBin mask stock 8 forest
def rowPerm (ps : List (Nat × Nat)) (x : Fin 256) : Fin 256 :=
  Fin.ofNat 256 (ps.foldl (fun y ab =>
    if (((y >>> ab.1) ^^^ (y >>> ab.2)) &&& 1) = 1 then
      y ^^^ ((1 <<< ab.1) ||| (1 <<< ab.2)) else y) x.val)
def s16 : WordMoveStep := ([(0xcccccccccccccccc3333333333333333cccccccccccccccc3333333333333333,0),(Words.m146,62)],[(0x3333333333333333000000000000000033333333333333330000000000000000,62)])
def s34 : WordMoveStep := ([(Words.m9,0),(Words.m10,8)],[(Words.m11,8)])
def move0 : DagMoveRecord 256 := ([s16,s34], rowPerm [(3,4),(1,6)], rowPerm [(1,6),(3,4)])
def moves := dagMoves ([move0] : List (DagMoveRecord 256))
def scan := dagCheckNodeBin mask goal nodeBounds 199 states moves links sample tags
def root (token : Nat) : Bool :=
  let s := rootState stock 8 token
  !dagAllowedRootBin mask essential s.2.1 || dagLocalBin mask goal (dagKnownClosesBin goal bounds) s ||
    dagRefBin mask 199 states moves (fun p tok => dagFindLink (links p) tok) 0 token s

end PEqualNP.Outside.L_meta_32199.Native.Cut9

namespace PEqualNP.Outside.L_meta_32199.Native.Cut9
open PEqualNP.Outside.L_meta_32199.Contraction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block0 : treeBlock 0 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block16 : treeBlock 16 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block32 : treeBlock 32 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block48 : treeBlock 48 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block64 : treeBlock 64 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block80 : treeBlock 80 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block96 : treeBlock 96 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block112 : treeBlock 112 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block128 : treeBlock 128 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block144 : treeBlock 144 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block160 : treeBlock 160 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block176 : treeBlock 176 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block192 : treeBlock 192 7 scan = true := by decide +kernel
theorem nodeCheck : treeBlock 0 199 scan = true := (@treeBlock_merge 0 96 103 scan (@treeBlock_merge 0 48 48 scan (@treeBlock_merge 0 16 32 scan block0 (@treeBlock_merge 16 16 16 scan block16 block32)) (@treeBlock_merge 48 16 32 scan block48 (@treeBlock_merge 64 16 16 scan block64 block80))) (@treeBlock_merge 96 48 55 scan (@treeBlock_merge 96 16 32 scan block96 (@treeBlock_merge 112 16 16 scan block112 block128)) (@treeBlock_merge 144 32 23 scan (@treeBlock_merge 144 16 16 scan block144 block160) (@treeBlock_merge 176 16 7 scan block176 block192))))

end PEqualNP.Outside.L_meta_32199.Native.Cut9

namespace PEqualNP.Outside.L_meta_32199.Native.Cut9
open PEqualNP.Outside.L_meta_32199.Contraction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootCheck : treeBlock 0 64 root = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (known : KnownBin bounds) : BinLower mask raw goal 9 := by
  have autos : DagMovesOK mask goal 256 moves := dagMovesOfCheck (by decide +kernel)
  apply lowerDagBin (mask := mask) (goal := goal) (width := 256) (fuel := 8) (count := 199)
    (stock := raw) (forest := forest) (moves := moves) (linkList := links)
    (sample := sample) (tags := tags) (bounds := bounds) (nodeBounds := nodeBounds) (witnesses := essential)
    _ _ _ _ autos _ _ _ known _ (fun _ b hb => dagNodeBounds_mem b hb) rootCheck nodeCheck
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : bounds.all (fun b => mask &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem asCut (known : KnownBin bounds) :
    BinLower (cut mask 9).1 (cut mask 9).2.1 (cut mask 9).2.2.2 (cut mask 9).2.2.1 := by
  have supply : ∀ w ∈ globalRaw.map (fun a => a &&& mask), AvBin mask raw w := by
    intro w hw
    simp only [globalRaw, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold AvBin <;> decide +kernel
  intro values build hit
  apply lower known values (buildsBin_weaken supply build)
  apply avBin_weaken (small := values ++ globalRaw.map (fun a => a &&& mask)) (big := values ++ raw) ?_ hit
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · exact Or.inr (Or.inr (Or.inl (List.mem_append_left _ h)))
  · exact avBin_weaken (fun a ha => Or.inr (Or.inr (Or.inl (List.mem_append_right _ ha)))) (supply _ h)

end PEqualNP.Outside.L_meta_32199.Native.Cut9

namespace PEqualNP.Outside.L_meta_32199.Native.Cut10
open PEqualNP.Outside.L_meta_32199.Contraction

def globalRaw : List Word := [Words.m14,Words.m15,Words.m16,Words.m4,Words.m17,Words.m18,Words.m19,Words.m20]
def globalGoal : Word := Words.m46
def raw : List Word := [0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a,0xc0c0c0c000000000c0c0c0c000000000c0c0c0c000000000c0c0c0c,0xf000f00000000000f000f00000000000f000f00000000000f000f00,0xf0f0000000000000f0f0000000000000f0f0000000000000f0f0000,0xf0f0f0f0000000000000000000000000f0f0f0f0000000000000000,Words.m144]
def goal : Word := 0xf0f0f0f000000000f0f0f0e000000000f0e0f0e000000000e0c0a00
def cut (m lb : Nat) : Bound := (m, globalRaw.map (fun w => w &&& m), lb, globalGoal &&& m)
def bounds : List Bound := [cut 0x3030000000000000303 4,cut Words.m64 4,cut Words.m65 4,cut Words.m66 4,cut Words.m67 7,cut Words.m51 4,cut Words.m68 8,cut Words.m74 4,cut Words.m59 4,cut Words.m62 4]
abbrev mask : Word := Words.m142
def stock : List Word := normStock mask raw
def essential := unpackWitnesses raw [4616, 271376, 528897, 795650, 1081857, 1376769]
def forest : Forest := decodeNode 7 20 0xa3044830440163d22834028b40283401cad83125629a421023a311e8311e8301d8291d8309c82c9c02f1a83719a3117037170311701c9683615830154361543015230150309503015832144241342213024936361263212a31106311062e0d6280d2280d0280d42e0a42a0a831868288601e0601a06a3184837048310482f04829042310403704031840310402f04029840290462d8162b8162981627816258162381621814278142581423814218141f8141d8141b8141981025810218101d8101981015810118101f80
def links : DagLinkList := dagExtractLinks 0x8a022808a022808a022808a022808a022808906201870614285021408502140850214084061008402100840210083060818105f837e01f807e01f807e01e847515d407501d407501d407501c837009bc16e05a06680198266018c3600d7825e017025b056c0580d5824e2120644110824200f063c00f003618d803600d023400d003400b472d0084c21008400180001 0x1408c09e4604f8292851813e0c09c02c4d6282641812d8a09a4504c028a58143180c37c051460209f00c7140c29205145020a500e4f0062930603c0202400f1260c57c06248629a390811a0c08b050c32382101f0f80c078050458292211811a8c48b0624323161d185120c08705242830a0c165000bc780523f8371f5188f40dc78062a00309d80e4ea0d873060336281c21b0dd0c06c460350309a0180ce0c858c529f03092814c7c082320313242418a110c00923c0312f636173190b68c458c62a1031920144740822c031aba34555180ad8b854c50292281401409d0b84c854a4a3112c18c920a32c062160211180f08806843463208370fc1887a0bc3b0521c2310d81b8680c6320621802f0b814c580a52305f9282dc8415e3e0a72ac5f1562d8a315c4d8a624c4f1162588311c3d8871485f8942dc4215e1d0a61c84f0d42586211c2d0861483f0941d8420dc1d0670805b8302983012c140860803b030198100ac040460003f 14 6 13 7 1
def nodeBounds : Nat → List Bound := dagNodeBounds bounds.toArray 0x679ce39c331652c8590319629c3584704dfabe37a6ed5d8ba3726e45b3b2960ab9562aa550a99522a2540a794e29972ea51c848e518a2944286508a05bec798ecdcdb836c8d4996b0c5d8b4d56a8c4e693519a143e876cda9a23085c8aa13423640c758da1942b04607308c0c80a002 0x7757575771782595272021352198535257505257575757525052672529579571528282828252572697269726879715714521526572153218521531853216821721637219526487485757269572526972826972648297268085250826972697245764572182680264 11 3 4
def sample : DagSample := (0x14090020800880024022810422004822010400090082c001200864220908848a04201a04229001048044220120a0d00c048a05205128309008944301901a0c22190c260804220300141a0884ca05828144060b0c160301a0502c061308a44064340221008240204148a4024100c0, 49)
def tags := dagTraceTagsBin mask 49 (dagTagBases stock 0x1d89bfe1e986f7b3331da68ab5b27eed350edf7e59889849f7fbf712f32f7d03fceed5ff40 0x3de89fe9edc7efbfd3ddeecbb7bfffa5b78fdfbf8b889c4dfffbf797f33fffffffffffffc4 49) 9 forest
def states := dagTraceBin mask stock 9 forest
def rowPerm (ps : List (Nat × Nat)) (x : Fin 256) : Fin 256 :=
  Fin.ofNat 256 (ps.foldl (fun y ab =>
    if (((y >>> ab.1) ^^^ (y >>> ab.2)) &&& 1) = 1 then
      y ^^^ ((1 <<< ab.1) ||| (1 <<< ab.2)) else y) x.val)
def s03 : WordMoveStep := ([(Words.m24,0),(Words.m25,7)],[(Words.m26,7)])
def move0 : DagMoveRecord 256 := ([s03], rowPerm [(0,3)], rowPerm [(0,3)])
def moves := dagMoves ([move0] : List (DagMoveRecord 256))
def scan := dagCheckNodeBin mask goal nodeBounds 81 states moves links sample tags
def root (token : Nat) : Bool :=
  let s := rootState stock 9 token
  !dagAllowedRootBin mask essential s.2.1 || dagLocalBin mask goal (dagKnownClosesBin goal bounds) s ||
    dagRefBin mask 81 states moves (fun p tok => dagFindLink (links p) tok) 0 token s

end PEqualNP.Outside.L_meta_32199.Native.Cut10

namespace PEqualNP.Outside.L_meta_32199.Native.Cut10
open PEqualNP.Outside.L_meta_32199.Contraction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block0 : treeBlock 0 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block16 : treeBlock 16 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block32 : treeBlock 32 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block48 : treeBlock 48 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block64 : treeBlock 64 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block80 : treeBlock 80 1 scan = true := by decide +kernel
theorem nodeCheck : treeBlock 0 81 scan = true := (@treeBlock_merge 0 48 33 scan (@treeBlock_merge 0 16 32 scan block0 (@treeBlock_merge 16 16 16 scan block16 block32)) (@treeBlock_merge 48 16 17 scan block48 (@treeBlock_merge 64 16 1 scan block64 block80)))

end PEqualNP.Outside.L_meta_32199.Native.Cut10

namespace PEqualNP.Outside.L_meta_32199.Native.Cut10
open PEqualNP.Outside.L_meta_32199.Contraction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootCheck : treeBlock 0 64 root = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (known : KnownBin bounds) : BinLower mask raw goal 10 := by
  have autos : DagMovesOK mask goal 256 moves := dagMovesOfCheck (by decide +kernel)
  apply lowerDagBin (mask := mask) (goal := goal) (width := 256) (fuel := 9) (count := 81)
    (stock := raw) (forest := forest) (moves := moves) (linkList := links)
    (sample := sample) (tags := tags) (bounds := bounds) (nodeBounds := nodeBounds) (witnesses := essential)
    _ _ _ _ autos _ _ _ known _ (fun _ b hb => dagNodeBounds_mem b hb) rootCheck nodeCheck
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : bounds.all (fun b => mask &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem asCut (known : KnownBin bounds) :
    BinLower (cut mask 10).1 (cut mask 10).2.1 (cut mask 10).2.2.2 (cut mask 10).2.2.1 := by
  have supply : ∀ w ∈ globalRaw.map (fun a => a &&& mask), AvBin mask raw w := by
    intro w hw
    simp only [globalRaw, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold AvBin <;> decide +kernel
  intro values build hit
  apply lower known values (buildsBin_weaken supply build)
  apply avBin_weaken (small := values ++ globalRaw.map (fun a => a &&& mask)) (big := values ++ raw) ?_ hit
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · exact Or.inr (Or.inr (Or.inl (List.mem_append_left _ h)))
  · exact avBin_weaken (fun a ha => Or.inr (Or.inr (Or.inl (List.mem_append_right _ ha)))) (supply _ h)

end PEqualNP.Outside.L_meta_32199.Native.Cut10

namespace PEqualNP.Outside.L_meta_32199.Native.Cut12
open PEqualNP.Outside.L_meta_32199.Contraction

def globalRaw : List Word := [Words.m14,Words.m15,Words.m16,Words.m4,Words.m17,Words.m18,Words.m19,Words.m20]
def globalGoal : Word := Words.m46
def raw : List Word := [0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa,Words.m146,0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,Words.m5,Words.m13,Words.m12,0xffffffffffffffff00000000000000000000000000000000]
def goal : Word := 0xfffffffffffffffe0000000000000000fefcfaf0eeccaa00
def cut (m lb : Nat) : Bound := (m, globalRaw.map (fun w => w &&& m), lb, globalGoal &&& m)
def bounds : List Bound := [cut Words.m76 4,cut Words.m78 4,cut Words.m81 4,cut Words.m51 4,cut Words.m84 4,cut Words.m52 4,cut Words.m87 4,cut Words.m68 8,cut Words.m88 8,cut Words.m89 8,cut Words.m90 8,cut Words.m93 4,cut Words.m94 4,cut Words.m95 8,cut Words.m104 8,cut Words.m105 8,cut Words.m106 8,cut Words.m116 8,cut Words.m121 8,cut Words.m129 8,cut Words.m130 8,cut Words.m131 8]
abbrev mask : Word := Words.m139
def stock : List Word := normStock mask raw
def essential := unpackWitnesses raw [4616, 271376, 542752, 791041, 1057794, 1329156, 1638913]
def forest : Forest := decodeNode 8 21 0x11a3250c18842dc300e6110f2e90e172c7cb6436582182bc8b956434ab63e5421429c8414ec7ca44364fa1f2718f91ac7c884283ea181f10a0f802c7c220bcb1f1cd880e203c71428379081bd8f8dc06f622193092017c858ba8605c228ad91416c848b508c582282c11315d0baac44256237aa118d5003ea8017542122991414889ca087c4f4262791b1380289c44c4c21e2600912d8c0948304a2182510e1258f88ac504443e2200950d8c484c424262da0b14d058a08087c4063e1f2230f90f87c84c3e4369ea1b0f507a7b08c3c8461d0050e61186cc7d3563e1a90f0d00286842d3300b198054cd0ba6444e322211910f4ca1186244c30627173108b90da5c43a2e63015a0c0ac0785684c2a63e1490d4a4848504262721293a108990804c02c2684612a1209406848c5c2341811b1388588442835210149000948109c3e8421f6210f01b07a1183ac7d1c63e0e21306d07a34c48196280c0230618f82e0351700c8b00545803e2a01b1500b8a8054540262a8521422f0a10f4508782844212220092148440bc2203c110160890f84087220435102190800e44006a210520f63e87b1f03d8bc1ec520f22f07b108390da1c86c0e427872138390861c8420e42f06a148348bc1a4520d2268690f43489e1844e0c2218611083085a1845e0b2290591342c898168320a21c8510d42807c1484e0942184a1082484a12c5e08629042148218a40ec40074198300bc180460c84f0542702a10c150840a04f0502182913810886084420400f8200641002a08013046218190fc0c87c06433032190180fc0d886048320221f8110cc080b80403e0221180807c040260207f00
def links : DagLinkList := dagExtractLinks 0xa00140028005000a00140028005000a00140028005000a00140028005000a00140028005000a00140028005000a00140028005000a00140027e14fc09f813e867c0cf239d493a067404e809d013a027404e809d01390a710ce209c4138067004e009b8537026e04d829a85340a6614cc098c731826304c4197c72f825f04bc197812f025e04ba197032e025c04b6196c12d825a0cb2196412b8a5704ae095c12b825704ae095c12b82560cac095812a865504a8195012a025404a61948328865104a01940128024f0c96492c1250648148e191c1238247048e091832302422484090051f863f047e08fc11f823f047e08fc11f823f047e08fc11e0e38247008ccb17162c14488859d08960d241628283038e022bf297d86fa09f403e047acaf299e40bc237802ed95d81bae174c8e905d013965714cde25b4436046b84d495a3334036708cc8d95232816484c7118a230865fcabc99761ae635c82b6196c02d6159c8b289621ac215748ab99522aa025384a609472a8454f889c9537126834c84978d2e0a5824a089021174a1aa42487f2cf739cd135a06248b76952e275849a88760fc91cd633b05b609510bb80cd401c0001 0x17321a01cc46807180501a6030372a1c01ca860470a0c01c842d56901045a403106880841c601c17111301c443c070a1c01c0c7c36e91301ba43c36fa1f01be86c36f21c01bc86036d11701b444c36ca1301b283c06e91701b843406c90b01b6c7c06d21405a083806c90801b0c7c06ba1f01ae86c06b21f05a842c16a90f05aa43c06a90b01aac7c16a10a01a8c7c06580f019405c065a14019c421069a140da487006921801a285006800b019a4310679104198021064817019cc7c5e6b1c019ac4016610f019803c065a140194420064b1f019006f13f80840fe011163a0c818e43213f00840fc01106312004fa04003e80c012202c05b808017e45c35f913117e43c06280a011e02406290b011c024562220058887006221814f805013e01000f8030047807018201056191c55844701619184584460061914418445005c1104d7043145c10854f604113d80c40f6021047807815601d060909016c05c35b013116c03c05580b017e85c15e213017883c048805018108c05f914017c44c05ea17577847205e110955804d54101044f403103d008415601d05d91bc17446395681be50606313c80c40f202105c807c170017541004c16e42405b017015602c05b11401564405da91fa55647205a913815644235a223016887c359a17016684c055a0f0d5485c055213016446c05610f015642c058805015e43c358117016044c05790f015c024056b180158830353117014c44c05590c015045c05510e0516430146910174e47e74c11c814e44e34c1108d3845c354b230152c7c353c230150c5004e312014e87c34e2170148c6d050b13451683a53a010410c02d0530095748c72052b188148c425d021f973e872050213813e842146a0f410a03d5d1d1bd745463051b16c144c5374481be4ee06334480fd4ee033050b140516c4005021f0d3285034cb1354ec04104fb1f0d32c5c04f223013a87c04e2130d3687d34d21f013686d04d21b0d3284d04ca0f413108c545914050e42c149213150c83c549117050c43c04bc23152445014610f151685c145a13051043c04b005050843c045313050844c04ac23152045014610f011842c04a31f4126c7c5483134d1004d548217051684c045a0f052444c04910f0122014548113452043d04810b411e016047005411a85d5c611f9716472046113811644204510f411308c343214050e428443317050c83804411305088485c3b1f970cc72043b13810cc42042a1b410843a03781b0106c6004120c00dc06c04080f0d0085c04021300fec7c03f10d40e442103e9090ce244103890c40f842603d90956f48725bca1c00f484203ca1000e043103c00b00ef08c03a21400ec84803681b0cc805c03601b00ea03403a31700e6830038b1004d647c5b931f96e2c7203931380e2c4203820d4cd604103580c40d802d03780a40dc0255b6a1f9cd8872036a1380d88425b5b1c80d6c4283101f80d406c43101380d308c332a1400d0c7d033b1f0ccac4d332b1700cc84c332a1340ca83d03181040c8c48031b1400c408c030b1f00c00351140084050011516014444e04101380c40b002d029008549601d02f80640bc015513010444c03101300840ba01f01900740b801b02d805c0b401502c804d6b088202c21496ae48e92592080ae45e52591484ac44d12a91300ac43d02a90f249447f91591cd49444f515910d6a84725a991c00a8442029910249207f91501cd49204f515010c44a031012808409e01d5a922080a48525a882380a205e12801300a003c02780b0c9045d321117009044d021113009c43e02210f407843c02690e409843502590c807043101910c1444051111010445e03d02500e40920355a442080910525a2b239c88c82023b1f408cc7c022b178088c5201bb135c8648e71d920808645e31d914806e441118910005c04d5a131c8084c4259fa1fd67c87e59ea1cdc78872020a1b408086c01fa13c07c84e01ea10c078842118a0f5c6007f91201ccc6004f512010c05a03d59da239c7488201da17807485201ba13446284c59c9239c7048201c917807045201b913406c43d11690f166a47f59a11f966647391911c806a44f01a1138066443019110846243d01890b5c5e07f91181ccc5e04f511810d860c8e917b208460c5e117b14845c83a116a0e166048e997920806045e017914805c44d016913005883201320c1442451110910404643d01590e405443500f81b005203e00c80f165087e593a1cdc4c872014213804e8430132109c4447f71091ccc4444f310910c0404310129095648c8e711b208048c5e011b1496448820112149c3008e00f01b0c3005e610c208443052590b208042c52010310202e48e10e91f102e45e70b823803a06c30b8179a3f46318fb14dc3e86300fa0cdc3c06f70e818c63c05f18e814cc3c03f30e80cc03c02f00e808d63887f58da1f963487370ca1c803884f00da13803484300ca10963007f58b81cc03004f00b810d62c47e58a91ce42847200b113802a44300a110a41e07f90481cd41e04f504810c410031004008402601f00580740240190088054020013687e1cc61f063707b1cc01ec4370711fdc1a47e70611ce41647218711bc61a46e186118ca16462307113cc1a44e306110cc1644200710fc01a43e00610cc01643290501fe40e07328501bca0e063305013d40e04300500fc40e033684e1cc613063704b1cc012c4370421c8610862304210801083270391fe40c47318391bca0c463303913cc0c44300390fc00c43370201f860806e0028170c0804e00200fa207463781c18c807053481b14ce06c43981a18c206843401a0ce406463281914cc06433001908e40406f900818ca0405f280814c20404f080810d40403f50080cc40402f100808c00401f000804c00007f 15 5 13 8 5
def nodeBounds : Nat → List Bound := dagNodeBounds bounds.toArray 0xf49f48f48f48f41f40f40f40f40f39f38f38f31f29f28f28f28f21f19f18f11f09f08f08f01ef9ef1ef0ef0ef0ee9ee1ee0ee0ee0ecbebaeb8eb8eb1ea9ea1e99e98e91e90e74e70e69e61e60e59e51e49e41e39e31e29e21e20e0be01df2de9dd3dc9dbadb1db0da9da8d9ad91d89d81d72d62d59d58d4ad41d40d39d1cd11d09d01cf9cdccd1cc9cbacaaca1c99c91c89c81c79c71c69c61c59c4ac41c39c38c23c19c0ac01bf9beabe1bd2bc2bb9b9cb83b80b64b59b58b4ab48b48b41b39b31b29b21b12b10af4ae2acbaacaa1a7da5ca2e9fe9ea9da9d19bb9aa99a97596995a93c93190d9089089088e58cb8ba89c8838648528348147ed7da7b57a277d76a75a74372470b6f36e96be6b168666464b63a62a6135f45e25bd5b159b57c54752450b4fa4dc4b548d46544441d4113ed3e13bd3aa39337b35531f2fc2d52a627623f21c1fc1ce19e17514611d0ee0c50a408405d03c01c003 0x811098a584e00008028885110002b186104842308162d6c8562994650ac41204a320c411905276a5a223d2d3888a230412014a22a230ad6051ce40a40011c600240039c2c3d4ec034eb1aa2085460234647860190675602407a42b18829a3d2b1a563049a758c099b90302649901e704812025c890247034e502e50ab012855604ca298a6478a6414ac609353269d323c5323c4128a64d38e4d4c9a75c96d1a64d4c9ac4c40d5024f4c9a704a8f4c9a77b4e058c0d1a5a969ceb181273c2a302532025630264d3ac604aa2091c0939d63025a758de969c0f4c9a77b5437a5a71c9f269c927c9a75b49258e920264b1813269d6303d32051339024d3aa204b912381e9934eb1a64d3a64d3bd3269c0f4c9a703d3269de9934eb4c9a703d3269c0f4c9a74c9a77c9a74c9a70264d3a64d3c9a7 12 3 5
def sample : DagSample := (0x204000900220201a0c0490098008a42098402a05482010c820900082400a01082442390209050a8182400412182806281152885088402c008840621044b20504828840a09062b1118ac1c2e0a87438bc062301c1e11a0c46330a8d4603201a0c1c0f40240542e0aa547039402810088188d42a170385c46a30383c0e274021100814020870b8150e862390e0f0301a040244024, 66)
def tags := dagTraceTagsBin mask 66 (dagTagBases stock 0xf7d3eff9713302ede79fede7388be0d6ffffdfe660da711f68874beff03eabde078b3b3d9b28d31f83fd5a356c2e3a5ae1968ae402b9754ec3f 0x3f7d3eff9717703efff9fede738cbf0f7ffffdfe660db793f7f7bfbcd7a3eaffe479bbf4fe33cf33fa3ffbc90ee7cbadbe3bedfffdffffdcfc7f 66) 11 forest
def states := dagTraceBin mask stock 11 forest
def rowPerm (ps : List (Nat × Nat)) (x : Fin 256) : Fin 256 :=
  Fin.ofNat 256 (ps.foldl (fun y ab =>
    if (((y >>> ab.1) ^^^ (y >>> ab.2)) &&& 1) = 1 then
      y ^^^ ((1 <<< ab.1) ||| (1 <<< ab.2)) else y) x.val)
def s25 : WordMoveStep := ([(Words.m147,0),(Words.m148,28)],[(Words.m149,28)])
def s12 : WordMoveStep := ([(Words.m0,0),(Words.m1,2)],[(Words.m2,2)])
def s45 : WordMoveStep := ([(Words.m30,0),(Words.m31,16)],[(Words.m32,16)])
def s14 : WordMoveStep := ([(Words.m39,0),(Words.m40,14)],[(Words.m41,14)])
def s15 : WordMoveStep := ([(Words.m36,0),(Words.m37,30)],[(Words.m38,30)])
def s24 : WordMoveStep := ([(0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f,0),(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0,12)],[(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000,12)])
def s01 : WordMoveStep := ([(Words.m21,0),(Words.m22,1)],[(Words.m23,1)])
def s34 : WordMoveStep := ([(Words.m9,0),(Words.m10,8)],[(Words.m11,8)])
def s02 : WordMoveStep := ([(Words.m27,0),(Words.m28,3)],[(Words.m29,3)])
def s35 : WordMoveStep := ([(Words.m6,0),(Words.m7,24)],[(Words.m8,24)])
def s05 : WordMoveStep := ([(Words.m33,0),(Words.m34,31)],[(Words.m35,31)])
def s23 : WordMoveStep := ([(0xf00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f,0),(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0,4)],[(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00,4)])
def s03 : WordMoveStep := ([(Words.m24,0),(Words.m25,7)],[(Words.m26,7)])
def s04 : WordMoveStep := ([(Words.m42,0),(Words.m43,15)],[(Words.m44,15)])
def s13 : WordMoveStep := ([(0xcc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33,0),(0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc,6)],[(0x3300330033003300330033003300330033003300330033003300330033003300,6)])
def move0 : DagMoveRecord 256 := ([s25], rowPerm [(2,5)], rowPerm [(2,5)])
def move1 : DagMoveRecord 256 := ([s12,s45], rowPerm [(4,5),(1,2)], rowPerm [(1,2),(4,5)])
def move2 : DagMoveRecord 256 := ([s14], rowPerm [(1,4)], rowPerm [(1,4)])
def move3 : DagMoveRecord 256 := ([s14,s25], rowPerm [(2,5),(1,4)], rowPerm [(1,4),(2,5)])
def move4 : DagMoveRecord 256 := ([s15,s12,s24], rowPerm [(2,4),(1,2),(1,5)], rowPerm [(1,5),(1,2),(2,4)])
def move5 : DagMoveRecord 256 := ([s01,s34], rowPerm [(3,4),(0,1)], rowPerm [(0,1),(3,4)])
def move6 : DagMoveRecord 256 := ([s01,s25,s34], rowPerm [(3,4),(2,5),(0,1)], rowPerm [(0,1),(2,5),(3,4)])
def move7 : DagMoveRecord 256 := ([s01,s02,s34,s35], rowPerm [(3,5),(3,4),(0,2),(0,1)], rowPerm [(0,1),(0,2),(3,4),(3,5)])
def move8 : DagMoveRecord 256 := ([s01,s05,s02,s34,s23], rowPerm [(2,3),(3,4),(0,2),(0,5),(0,1)], rowPerm [(0,1),(0,5),(0,2),(3,4),(2,3)])
def move9 : DagMoveRecord 256 := ([s02,s01,s35,s34], rowPerm [(3,4),(3,5),(0,1),(0,2)], rowPerm [(0,2),(0,1),(3,5),(3,4)])
def move10 : DagMoveRecord 256 := ([s03], rowPerm [(0,3)], rowPerm [(0,3)])
def move11 : DagMoveRecord 256 := ([s03,s12,s45], rowPerm [(4,5),(1,2),(0,3)], rowPerm [(0,3),(1,2),(4,5)])
def move12 : DagMoveRecord 256 := ([s03,s14], rowPerm [(1,4),(0,3)], rowPerm [(0,3),(1,4)])
def move13 : DagMoveRecord 256 := ([s04,s01,s13], rowPerm [(1,3),(0,1),(0,4)], rowPerm [(0,4),(0,1),(1,3)])
def move14 : DagMoveRecord 256 := ([s04,s01,s25,s13], rowPerm [(1,3),(2,5),(0,1),(0,4)], rowPerm [(0,4),(0,1),(2,5),(1,3)])
def move15 : DagMoveRecord 256 := ([s04,s12,s01,s13,s35], rowPerm [(3,5),(1,3),(0,1),(1,2),(0,4)], rowPerm [(0,4),(1,2),(0,1),(1,3),(3,5)])
def move16 : DagMoveRecord 256 := ([s04,s15,s02,s13], rowPerm [(1,3),(0,2),(1,5),(0,4)], rowPerm [(0,4),(1,5),(0,2),(1,3)])
def move17 : DagMoveRecord 256 := ([s05,s01,s12,s23,s34], rowPerm [(3,4),(2,3),(1,2),(0,1),(0,5)], rowPerm [(0,5),(0,1),(1,2),(2,3),(3,4)])
def move18 : DagMoveRecord 256 := ([s05,s02,s23], rowPerm [(2,3),(0,2),(0,5)], rowPerm [(0,5),(0,2),(2,3)])
def moves := dagMoves ([move0,move1,move2,move3,move4,move5,move6,move7,move8,move9,move10,move11,move12,move13,move14,move15,move16,move17,move18] : List (DagMoveRecord 256))
def scan := dagCheckNodeBin mask goal nodeBounds 231 states moves links sample tags
def root (token : Nat) : Bool :=
  let s := rootState stock 11 token
  !dagAllowedRootBin mask essential s.2.1 || dagLocalBin mask goal (dagKnownClosesBin goal bounds) s ||
    dagRefBin mask 231 states moves (fun p tok => dagFindLink (links p) tok) 0 token s

end PEqualNP.Outside.L_meta_32199.Native.Cut12

namespace PEqualNP.Outside.L_meta_32199.Native.Cut12
open PEqualNP.Outside.L_meta_32199.Contraction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block0 : treeBlock 0 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block16 : treeBlock 16 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block32 : treeBlock 32 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block48 : treeBlock 48 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block64 : treeBlock 64 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block80 : treeBlock 80 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block96 : treeBlock 96 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block112 : treeBlock 112 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block128 : treeBlock 128 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block144 : treeBlock 144 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block160 : treeBlock 160 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block176 : treeBlock 176 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block192 : treeBlock 192 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block208 : treeBlock 208 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block224 : treeBlock 224 7 scan = true := by decide +kernel
theorem nodeCheck : treeBlock 0 231 scan = true := (@treeBlock_merge 0 112 119 scan (@treeBlock_merge 0 48 64 scan (@treeBlock_merge 0 16 32 scan block0 (@treeBlock_merge 16 16 16 scan block16 block32)) (@treeBlock_merge 48 32 32 scan (@treeBlock_merge 48 16 16 scan block48 block64) (@treeBlock_merge 80 16 16 scan block80 block96))) (@treeBlock_merge 112 64 55 scan (@treeBlock_merge 112 32 32 scan (@treeBlock_merge 112 16 16 scan block112 block128) (@treeBlock_merge 144 16 16 scan block144 block160)) (@treeBlock_merge 176 32 23 scan (@treeBlock_merge 176 16 16 scan block176 block192) (@treeBlock_merge 208 16 7 scan block208 block224))))

end PEqualNP.Outside.L_meta_32199.Native.Cut12

namespace PEqualNP.Outside.L_meta_32199.Native.Cut12
open PEqualNP.Outside.L_meta_32199.Contraction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootCheck : treeBlock 0 128 root = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (known : KnownBin bounds) : BinLower mask raw goal 12 := by
  have autos : DagMovesOK mask goal 256 moves := dagMovesOfCheck (by decide +kernel)
  apply lowerDagBin (mask := mask) (goal := goal) (width := 256) (fuel := 11) (count := 231)
    (stock := raw) (forest := forest) (moves := moves) (linkList := links)
    (sample := sample) (tags := tags) (bounds := bounds) (nodeBounds := nodeBounds) (witnesses := essential)
    _ _ _ _ autos _ _ _ known _ (fun _ b hb => dagNodeBounds_mem b hb) rootCheck nodeCheck
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : bounds.all (fun b => mask &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem asCut (known : KnownBin bounds) :
    BinLower (cut mask 12).1 (cut mask 12).2.1 (cut mask 12).2.2.2 (cut mask 12).2.2.1 := by
  have supply : ∀ w ∈ globalRaw.map (fun a => a &&& mask), AvBin mask raw w := by
    intro w hw
    simp only [globalRaw, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold AvBin <;> decide +kernel
  intro values build hit
  apply lower known values (buildsBin_weaken supply build)
  apply avBin_weaken (small := values ++ globalRaw.map (fun a => a &&& mask)) (big := values ++ raw) ?_ hit
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · exact Or.inr (Or.inr (Or.inl (List.mem_append_left _ h)))
  · exact avBin_weaken (fun a ha => Or.inr (Or.inr (Or.inl (List.mem_append_right _ ha)))) (supply _ h)

end PEqualNP.Outside.L_meta_32199.Native.Cut12

namespace PEqualNP.Outside.L_meta_32199.Native.Root
open PEqualNP.Outside.L_meta_32199.Contraction

def globalRaw : List Word := [Words.m14,Words.m15,Words.m16,Words.m4,Words.m17,Words.m18,Words.m19,Words.m20]
def globalGoal : Word := Words.m46
def raw : List Word := [Words.m14,Words.m15,Words.m16,Words.m4,Words.m17,Words.m18,Words.m19,Words.m20]
def goal : Word := Words.m46
def cut (m lb : Nat) : Bound := (m, globalRaw.map (fun w => w &&& m), lb, globalGoal &&& m)
def bounds : List Bound := [cut 0xa000500000000000a00050 4,cut Words.m50 4,cut Words.m136 7,cut Words.m137 7,cut Words.m121 8,cut Words.m129 8,cut Words.m130 8,cut Words.m138 8,cut Words.m139 12,cut Words.m141 9,cut Words.m142 10,cut Words.m143 10,cut Words.m145 10,cut Words.m140 9,cut Words.m47 11,cut Words.m49 11,cut Words.m48 11]
abbrev mask : Word := Words.m45
def stock : List Word := normStock mask raw
def essential := unpackWitnesses raw [4616, 271376, 542752, 791041, 1057794, 1329156, 1606145, 1901057]
def forest : Forest := decodeNode 7 20 0x846c9a4043a4837a4835836b38363382eb2a482fc482e44e2dc482aa41262412604726041264361fc4818a40176289744712c4910a4f10a4990a491044f10a410f8478f8470f8418f8410f4470ec490d64f0d2490d04f0d0490dc490a4490a24f0a2490a83989021894410864106441068478584705841054248504705a4104641846288424784247042418424104047040410402e8401f8401f04a418342f8342f034290302983a418262902229820360202f0283981421810278102181017810118107f80
def links : DagLinkList := dagExtractLinks 0xbf05f82fc17e0be0df02f437a0bd05e82f03761ba0dd02e81740b625b02d816c0b50da06d01680b11d78ab45581a91d38a9c14a2a3151068434209f14e8a703361981ca125012809404a02501280930c98234d1818b0c5822c10c5812be91e48f207903c05bd2d45643318578ab44590aa15446a014652018d183f5164872005a001 0x9d89c2742349a07c2692009b4806321f988872232138888422622729289c26524093488a4c2709748da3820497490a4424291c8da452709506d24c1b29108d2441748ec9c2312408f4902282708d89022a270888902181f0898902101f08206c2001f2860812181448004121d20884482208238800821fa1b07c4811e92015e46f55118c5e43f1510ce784901e12087d89056a1f95287216a13852842de62047b4805e518a78c811e31455805f54014c5802f14008d5646f53918c5643f1390cc7688e9d22766a89c1d21b46a86c1ba1746285c9782445e061158144758921cd278714931bd2486c89e1ad2086908f19c2386508318c20a5c0831822385f8921732785a49216027856092951244544611391444c07c9202385589214a2485049e1392484a07c1341ce4a07312810c48882514188448418e02052006f45818c380510f8134280410800bc1602311b208448828d820c340510500c41a02d10c23c4108e0fc2093d06e46c1882705d0f21241a8410e823a320838c0208260514de20c394824d518836c830d31443248f0c12382e4830b12091846f44918c2645d0610fc124330a8238280824901bd2206e0981742403f0880f82148387a23e1c88e86a2081e85f0721781a85286020c1805305d20e14c8205314a1248304914e0e08e0401b00e05ec2d1cc0d07342c14e0a87302a10e0807f8181cd0405f40814c0804f01810c0402f00808c000ff 13 5 13 7 2
def nodeBounds : Nat → List Bound := dagNodeBounds bounds.toArray 0x6002fa77a3bb9dd4ae296e3b525956c475d5aca5552a474e4a5251567cf3a49b9cc965c929591b479632b15487b425a0a90237eabe15e6aef4752b919bccd8669333558ecc43609af8d748b55591ab19526a364fa26952c8915453a154fce7863a99c50d8a6662fb961ca6a4d6233905473033616b0a5044e1b709c031c0ae005 0x7088e111c02008e0808e091c221dc62888e301cb1888e1008e2888e301c5111c9409ca1888e518a3111c628dc323982011cc011820808e6082023841011ca6088e1008e530a22394c1008e5308e111c91008e49844718a223926038a221dcb1880472ca3111cb30c0472ca3111c91888e4a0c22384470c8e191c6111c61888e111cb40c447088e51862235c32392830dc5111c51888e518a3111ca3148e518a3111ca28c447184e4986e4a06472989111cc4a0402394c4a04472502239283088e53123111c95a06e4ad061888d72503139051888e53c8e53128191ca7a0622394c7ad06241ca63d026b94c4a050729e8 13 4 5
def sample : DagSample := (0x8104224301902890148210a04000940024884c01208182400220508818ac442a0118ac542b0a8d41c2e042a0383c1428070b82816004420104854aa0aa54e0710c068c068383c0c0640703ca87422114389c150b900a0070780e0f188cc46a340204546a0389c62391c0e44633188d42a552a1590088060b050a84020900844024100c0, 59)
def tags := dagTraceTagsBin mask 59 (dagTagBases stock 0x18fa3fe7af081ffef7cbe377426ddfbd7e5fbc09ee2dce33226cd93a78fdffbb4a2d6bc0fbdfb003a8b32073ffdfff9d13fdf3f19d0f4e77ae7fa0 0xebf8bfefff191ffef7cbe3f74a6fffbd7e5fbe19ef2fcbeba0edd97b7cfdffbb4e2d7bc8fff7e0f3a8f7287bffdfffbd13fffbfff7ffffffef7fb0 59) 13 forest
def states := dagTraceBin mask stock 13 forest
def rowPerm (ps : List (Nat × Nat)) (x : Fin 256) : Fin 256 :=
  Fin.ofNat 256 (ps.foldl (fun y ab =>
    if (((y >>> ab.1) ^^^ (y >>> ab.2)) &&& 1) = 1 then
      y ^^^ ((1 <<< ab.1) ||| (1 <<< ab.2)) else y) x.val)
def s25 : WordMoveStep := ([(Words.m147,0),(Words.m148,28)],[(Words.m149,28)])
def s03 : WordMoveStep := ([(Words.m24,0),(Words.m25,7)],[(Words.m26,7)])
def move0 : DagMoveRecord 256 := ([s25], rowPerm [(2,5)], rowPerm [(2,5)])
def move1 : DagMoveRecord 256 := ([s03], rowPerm [(0,3)], rowPerm [(0,3)])
def move2 : DagMoveRecord 256 := ([s03,s25], rowPerm [(2,5),(0,3)], rowPerm [(0,3),(2,5)])
def moves := dagMoves ([move0,move1,move2] : List (DagMoveRecord 256))
def scan := dagCheckNodeBin mask goal nodeBounds 79 states moves links sample tags
def root (token : Nat) : Bool :=
  let s := rootState stock 13 token
  !dagAllowedRootBin mask essential s.2.1 || dagLocalBin mask goal (dagKnownClosesBin goal bounds) s ||
    dagRefBin mask 79 states moves (fun p tok => dagFindLink (links p) tok) 0 token s

end PEqualNP.Outside.L_meta_32199.Native.Root

namespace PEqualNP.Outside.L_meta_32199.Native.Root
open PEqualNP.Outside.L_meta_32199.Contraction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block0 : treeBlock 0 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block16 : treeBlock 16 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block32 : treeBlock 32 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block48 : treeBlock 48 16 scan = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem block64 : treeBlock 64 15 scan = true := by decide +kernel
theorem nodeCheck : treeBlock 0 79 scan = true := (@treeBlock_merge 0 32 47 scan (@treeBlock_merge 0 16 16 scan block0 block16) (@treeBlock_merge 32 16 31 scan block32 (@treeBlock_merge 48 16 15 scan block48 block64)))

end PEqualNP.Outside.L_meta_32199.Native.Root

namespace PEqualNP.Outside.L_meta_32199.Native.Root
open PEqualNP.Outside.L_meta_32199.Contraction

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootCheck : treeBlock 0 256 root = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lower (known : KnownBin bounds) : BinLower mask raw goal 14 := by
  have autos : DagMovesOK mask goal 256 moves := dagMovesOfCheck (by decide +kernel)
  apply lowerDagBin (mask := mask) (goal := goal) (width := 256) (fuel := 13) (count := 79)
    (stock := raw) (forest := forest) (moves := moves) (linkList := links)
    (sample := sample) (tags := tags) (bounds := bounds) (nodeBounds := nodeBounds) (witnesses := essential)
    _ _ _ _ autos _ _ _ known _ (fun _ b hb => dagNodeBounds_mem b hb) rootCheck nodeCheck
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · have h : bounds.all (fun b => mask &&& b.1 == b.1) = true := by decide +kernel
    intro b hb
    exact beq_iff_eq.mp (List.all_eq_true.mp h b hb)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem asCut (known : KnownBin bounds) :
    BinLower (cut mask 14).1 (cut mask 14).2.1 (cut mask 14).2.2.2 (cut mask 14).2.2.1 := by
  have supply : ∀ w ∈ globalRaw.map (fun a => a &&& mask), AvBin mask raw w := by
    intro w hw
    simp only [globalRaw, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold AvBin <;> decide +kernel
  intro values build hit
  apply lower known values (buildsBin_weaken supply build)
  apply avBin_weaken (small := values ++ globalRaw.map (fun a => a &&& mask)) (big := values ++ raw) ?_ hit
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · exact Or.inr (Or.inr (Or.inl (List.mem_append_left _ h)))
  · exact avBin_weaken (fun a ha => Or.inr (Or.inr (Or.inl (List.mem_append_right _ ha)))) (supply _ h)

end PEqualNP.Outside.L_meta_32199.Native.Root

namespace PEqualNP.Outside.L_meta_32199.Native.Cut9
open PEqualNP.Outside.L_meta_32199.Contraction
theorem certified : RowBank.boundAt Words.m140 9 := by
  apply asCut
  unfold bounds
  apply extendKnownBin (bound := cut Words.m50 4) _ (RowBank.row0)
  apply extendKnownBin (bound := cut Words.m51 4) _ (RowBank.row1)
  apply extendKnownBin (bound := cut Words.m52 4) _ (RowBank.row2)
  apply extendKnownBin (bound := cut Words.m57 4) _ (RowBank.row3)
  apply extendKnownBin (bound := cut Words.m59 4) _ (RowBank.row4)
  apply extendKnownBin (bound := cut Words.m62 4) _ (RowBank.row5)
  intro x hx
  contradiction
end PEqualNP.Outside.L_meta_32199.Native.Cut9

namespace PEqualNP.Outside.L_meta_32199.Native.Cut10
open PEqualNP.Outside.L_meta_32199.Contraction
theorem certified : RowBank.boundAt Words.m142 10 := by
  apply asCut
  unfold bounds
  apply extendKnownBin (bound := cut 0x3030000000000000303 4) _ (RowBank.row6)
  apply extendKnownBin (bound := cut Words.m64 4) _ (RowBank.row7)
  apply extendKnownBin (bound := cut Words.m65 4) _ (RowBank.row8)
  apply extendKnownBin (bound := cut Words.m66 4) _ (RowBank.row9)
  apply extendKnownBin (bound := cut Words.m67 7) _ (RowBank.row10)
  apply extendKnownBin (bound := cut Words.m51 4) _ (RowBank.row1)
  apply extendKnownBin (bound := cut Words.m68 8) _ (RowBank.row11)
  apply extendKnownBin (bound := cut Words.m74 4) _ (RowBank.row12)
  apply extendKnownBin (bound := cut Words.m59 4) _ (RowBank.row4)
  apply extendKnownBin (bound := cut Words.m62 4) _ (RowBank.row5)
  intro x hx
  contradiction
end PEqualNP.Outside.L_meta_32199.Native.Cut10

namespace PEqualNP.Outside.L_meta_32199.Native.Cut12
open PEqualNP.Outside.L_meta_32199.Contraction
theorem certified : RowBank.boundAt Words.m139 12 := by
  apply asCut
  unfold bounds
  apply extendKnownBin (bound := cut Words.m76 4) _ (RowBank.row13)
  apply extendKnownBin (bound := cut Words.m78 4) _ (RowBank.row14)
  apply extendKnownBin (bound := cut Words.m81 4) _ (RowBank.row15)
  apply extendKnownBin (bound := cut Words.m51 4) _ (RowBank.row1)
  apply extendKnownBin (bound := cut Words.m84 4) _ (RowBank.row16)
  apply extendKnownBin (bound := cut Words.m52 4) _ (RowBank.row2)
  apply extendKnownBin (bound := cut Words.m87 4) _ (RowBank.row17)
  apply extendKnownBin (bound := cut Words.m68 8) _ (RowBank.row11)
  apply extendKnownBin (bound := cut Words.m88 8) _ (RowBank.row18)
  apply extendKnownBin (bound := cut Words.m89 8) _ (RowBank.row19)
  apply extendKnownBin (bound := cut Words.m90 8) _ (RowBank.row20)
  apply extendKnownBin (bound := cut Words.m93 4) _ (RowBank.row21)
  apply extendKnownBin (bound := cut Words.m94 4) _ (RowBank.row22)
  apply extendKnownBin (bound := cut Words.m95 8) _ (RowBank.row23)
  apply extendKnownBin (bound := cut Words.m104 8) _ (RowBank.row24)
  apply extendKnownBin (bound := cut Words.m105 8) _ (RowBank.row25)
  apply extendKnownBin (bound := cut Words.m106 8) _ (RowBank.row26)
  apply extendKnownBin (bound := cut Words.m116 8) _ (RowBank.row27)
  apply extendKnownBin (bound := cut Words.m121 8) _ (RowBank.row28)
  apply extendKnownBin (bound := cut Words.m129 8) _ (RowBank.row29)
  apply extendKnownBin (bound := cut Words.m130 8) _ (RowBank.row30)
  apply extendKnownBin (bound := cut Words.m131 8) _ (RowBank.row31)
  intro x hx
  contradiction
end PEqualNP.Outside.L_meta_32199.Native.Cut12

namespace PEqualNP.Outside.L_meta_32199.Native.Root
open PEqualNP.Outside.L_meta_32199.Contraction
theorem certified : RowBank.boundAt Words.m45 14 := by
  apply asCut
  unfold bounds
  apply extendKnownBin (bound := cut 0xa000500000000000a00050 4) _ (RowBank.row32)
  apply extendKnownBin (bound := cut Words.m50 4) _ (RowBank.row0)
  apply extendKnownBin (bound := cut Words.m136 7) _ (RowBank.row33)
  apply extendKnownBin (bound := cut Words.m137 7) _ (RowBank.row34)
  apply extendKnownBin (bound := cut Words.m121 8) _ (RowBank.row28)
  apply extendKnownBin (bound := cut Words.m129 8) _ (RowBank.row29)
  apply extendKnownBin (bound := cut Words.m130 8) _ (RowBank.row30)
  apply extendKnownBin (bound := cut Words.m138 8) _ (RowBank.row35)
  apply extendKnownBin (bound := cut Words.m139 12) _ (RowBank.row36 PEqualNP.Outside.L_meta_32199.Native.Cut12.certified)
  apply extendKnownBin (bound := cut Words.m141 9) _ (RowBank.row37 PEqualNP.Outside.L_meta_32199.Native.Cut9.certified)
  apply extendKnownBin (bound := cut Words.m142 10) _ (RowBank.row38 PEqualNP.Outside.L_meta_32199.Native.Cut10.certified)
  apply extendKnownBin (bound := cut Words.m143 10) _ (RowBank.row39 PEqualNP.Outside.L_meta_32199.Native.Cut10.certified)
  apply extendKnownBin (bound := cut Words.m145 10) _ (RowBank.row40 PEqualNP.Outside.L_meta_32199.Native.Cut10.certified)
  apply extendKnownBin (bound := cut Words.m140 9) _ (RowBank.row41 PEqualNP.Outside.L_meta_32199.Native.Cut9.certified)
  apply extendKnownBin (bound := cut Words.m47 11) _ (RowBank.row42)
  apply extendKnownBin (bound := cut Words.m49 11) _ (RowBank.row43)
  apply extendKnownBin (bound := cut Words.m48 11) _ (RowBank.row44)
  intro x hx
  contradiction
end PEqualNP.Outside.L_meta_32199.Native.Root

namespace PEqualNP.Outside.L_meta_32199

open PEqualNP.CircuitLowerBounds

def upperGates : List Gate :=
  [⟨.or, [0, 1]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [13, 7]⟩, ⟨.and, [0, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [19, 16]⟩, ⟨.or, [20, 17]⟩, ⟨.or, [21, 18]⟩]

def graphList : List Nat := [0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7]

def edgeValue (s : List Bool) : Bool := decide (∃ i < graphList.length / 2,
  s.getD (graphList.getD (2*i) 0) false = true ∧ s.getD (graphList.getD (2*i+1) 0) false = true)

theorem upper_shape : ∀ g ∈ upperGates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g h
  simp only [upperGates, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact ⟨Or.inl rfl, by decide⟩ | exact ⟨Or.inr rfl, by decide⟩

theorem upper_length : upperGates.length = 15 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem upper_sem (x : Fin 8 → Bool) :
    Circuit.eval ⟨upperGates, 22⟩ (List.ofFn x) = edgeValue (List.ofFn x) := by
  have h : ∀ a b c d e f g h : Bool,
      Circuit.eval ⟨upperGates, 22⟩ [a,b,c,d,e,f,g,h] = edgeValue [a,b,c,d,e,f,g,h] := by decide
  simp only [List.ofFn_succ, List.ofFn_zero]
  apply h

end PEqualNP.Outside.L_meta_32199

namespace PEqualNP.Outside.L_meta_32199
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_32199.Contraction

def truthInputs : List (BitVec 256) := DeepRows.raw.map (BitVec.ofNat 256)
def truthGoal : BitVec 256 := BitVec.ofNat 256 DeepRows.goal

set_option maxHeartbeats 0 in
set_option maxRecDepth 15000 in
theorem countBinary (lb : BinLower (fullMask 256) DeepRows.raw DeepRows.goal 14)
    (gates : List Gate) (o : Nat) (hfan : FanInTwo ⟨gates, o⟩)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,o⟩ (List.ofFn x) = edgeValue (List.ofFn x)) :
    14 ≤ countNonNot gates := by
  let eb := gates.foldl hcsStep truthInputs
  have same : eb.getD o 0 = truthGoal := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let x : Fin 8 → Bool := fun k => j.testBit k.val
    have hbank : ∀ i : Fin 256, truthInputs.map (fun v => v.getLsbD i.val) =
        List.ofFn (fun k : Fin 8 => i.val.testBit k.val) := by decide +kernel
    have hgraph : ∀ i : Fin 256, truthGoal.getLsbD i.val =
        edgeValue (List.ofFn (fun k : Fin 8 => i.val.testBit k.val)) := by decide +kernel
    have bits := hcsFoldBits truthInputs ⟨j,hj⟩ gates hfan
    calc
      (eb.getD o 0).getLsbD j = (eb.map fun v => v.getLsbD j).getD o false := hcsGetDBit eb j o
      _ = edgeValue (List.ofFn x) := by
        dsimp only [eb]
        rw [bits, hbank ⟨j,hj⟩]
        exact he x
      _ = truthGoal.getLsbD j := (hgraph ⟨j,hj⟩).symm
  have hroot : truthInputs.map BitVec.toNat = DeepRows.raw := by decide +kernel
  have hr : ∀ v ∈ truthInputs, AvBin (fullMask 256) DeepRows.raw v.toNat := by
    intro v hv
    apply Or.inr (Or.inr (Or.inl ?_))
    rw [← hroot]
    exact List.mem_map_of_mem hv
  obtain ⟨vs, len, built, reach⟩ := hcsBuildsBin truthInputs DeepRows.raw gates hr hfan
  have av : AvBin (fullMask 256) (vs ++ DeepRows.raw) DeepRows.goal := by
    rw [show DeepRows.goal = truthGoal.toNat by decide +kernel, ← same, List.getD_eq_getElem?_getD]
    cases h : eb[o]? with
    | none => exact Or.inl rfl
    | some v => exact reach v (List.mem_of_getElem? h)
  exact (lb vs built av).trans len

theorem finish (lb : BinLower (fullMask 256) DeepRows.raw DeepRows.goal 14)
    (gates : List Gate) (o : Nat)
    (hg : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates,o⟩ (List.ofFn x) = edgeValue (List.ofFn x)) :
    ∃ (out : List Gate) (p : Nat),
      (∀ g ∈ out, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ out.length ≤ gates.length ∧
      ∀ x : Fin 8 → Bool, Circuit.eval ⟨out,p⟩ (List.ofFn x) = edgeValue (List.ofFn x) := by
  by_cases hn : ∃ g ∈ gates, g.op = .not
  · have hfan : FanInTwo ⟨gates,o⟩ := by
      intro g h
      obtain ⟨hop, len⟩ := hg g h
      refine ⟨?_, len⟩
      rcases hop with h | h | h <;> simp [h]
    have floor := countBinary lb gates o hfan he
    have used := countNonNot_le_sub hn
    refine ⟨upperGates,22,upper_shape,?_,upper_sem⟩
    change 15 ≤ gates.length
    omega
  · refine ⟨gates,o,?_,Nat.le_refl _,he⟩
    intro g h
    obtain ⟨hop, len⟩ := hg g h
    refine ⟨?_,len⟩
    rcases hop with h₁ | h₂ | h₃
    · exact Or.inl h₁
    · exact Or.inr h₂
    · exact (hn ⟨g,h,h₃⟩).elim

end PEqualNP.Outside.L_meta_32199

theorem PEqualNP.Outside.L_meta_32199 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 5, 0, 6, 1, 6, 3, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hg _ hu
  apply PEqualNP.Outside.L_meta_32199.finish _ gates o hg hu
  exact PEqualNP.Outside.L_meta_32199.Native.Root.certified
