import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40374

def chi (u : Nat → Bool) (i : Nat) : Bool :=
  xor (u i) (!(u (i+1)) && u (i+2))

def pack (n : Nat) (f : Nat → Bool) : Nat :=
  (List.range n).foldl (fun a i => if f i then a + 2^i else a) 0

def reply (n u : Nat) := pack n (chi u.testBit)

def sense (n u pulse : Nat) :=
  pack n (chi (fun i => xor (u.testBit i) (pulse.testBit i)))

def raw (k : Fin 3) : Nat := ![184, 146, 152] k
def rowPulse (k : Fin 3) : Nat := ![50, 63, 60] k
def colPulse (k : Fin 3) : Nat := ![29, 63, 55] k
def rowMask (k : Fin 3) : Nat := ![16777215, 4294967280, 4294967055] k
def colMask (k : Fin 3) : Nat := ![65295, 65520, 255] k
def allowed (k : Fin 3) (a b : Nat) :=
  (rowMask k).testBit a && (colMask k).testBit b
def select (a b : Nat) : Fin 3 :=
  if allowed 0 a b then 0 else if allowed 1 a b then 1 else 2

def rewind (n y tail : Nat) : Nat :=
  (List.range n).reverse.foldl (fun z i =>
    2*z + (xor (y.testBit i) (!(z.testBit 0) && z.testBit 1)).toNat) tail

def decode (n y obs pulse : Nat) : Nat :=
  (((List.range 4).map (rewind n y)).find? (fun z => sense n z pulse == obs)).getD 0

lemma rowWindow : ∀ k : Fin 3, ∀ t : Fin 7, (rowPulse k).testBit t =
    xor ((raw k).testBit (4+t.val)) (xor ((raw k).testBit (3+t.val)) ((raw k).testBit (2+t.val))) := by decide +kernel
lemma colWindow : ∀ k : Fin 3, ∀ t : Fin 6, (colPulse k).testBit t =
    xor ((raw k).testBit (4+t.val)) (xor ((raw k).testBit (2+t.val)) ((raw k).testBit t.val)) := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma covers : ∀ a : Fin 32, ∀ b : Fin 16, allowed (select a b) a b = true := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma rowRecovers : ∀ k : Fin 3, ∀ u : Fin 128, (rowMask k).testBit (reply 5 u) = true →
    decode 5 (reply 5 u) (sense 5 u (rowPulse k)) (rowPulse k) = u.val := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma colRecovers : ∀ k : Fin 3, ∀ u : Fin 64, (colMask k).testBit (reply 4 u) = true →
    decode 4 (reply 4 u) (sense 4 u (colPulse k)) (colPulse k) = u.val := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma rowFits : ∀ u : Fin 128, reply 5 u < 32 := by decide +kernel
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma colFits : ∀ u : Fin 64, reply 4 u < 16 := by decide +kernel

lemma pairedRecovery (r : Fin 128) (c : Fin 64) :
    let k := select (reply 5 r) (reply 4 c)
    decode 5 (reply 5 r) (sense 5 r (rowPulse k)) (rowPulse k) = r.val ∧
    decode 4 (reply 4 c) (sense 4 c (colPulse k)) (colPulse k) = c.val := by
  let a : Fin 32 := ⟨reply 5 r, rowFits r⟩
  let b : Fin 16 := ⟨reply 4 c, colFits c⟩
  have h := covers a b
  obtain ⟨hr, hc⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨rowRecovers _ _ hr, colRecovers _ _ hc⟩

lemma undoBit (a b : Bool) : xor (xor a b) b = a := by cases a <;> cases b <;> rfl

lemma step (u : Nat → Bool) (i : Nat) :
    xor (chi u i) (!(u (i+1)) && u (i+2)) = u i := undoBit _ _

lemma stripUnique (h : Nat) (u v : Nat → Bool)
    (heq : ∀ i < h, chi u i = chi v i) (h₀ : u h = v h) (h₁ : u (h+1) = v (h+1)) :
    ∀ i < h+2, u i = v i := by
  induction h with
  | zero =>
    intro i hi
    interval_cases i <;> assumption
  | succ h ih =>
    have ht : u h = v h := by
      calc u h = xor (chi u h) (!(u (h+1)) && u (h+2)) := (step _ _).symm
           _ = xor (chi v h) (!(v (h+1)) && v (h+2)) := by rw [heq h (by omega), h₀, h₁]
           _ = v h := step _ _
    intro i hi
    by_cases hs : i < h+2
    · exact ih (fun j hj => heq j (by omega)) ht h₀ i hs
    · have he : i = h+2 := by omega
      subst i
      exact h₁

lemma necessarySlope {p d K : Nat}
    (bounds : ∀ h, 5 ≤ h → ∃ g, 2*(h+2) ≤ g+9 ∧ d*g ≤ p*h+K) : 2*d ≤ p := by
  by_contra! hyp
  let H := K+5*d+6
  obtain ⟨g, lo, hi⟩ := bounds H (by dsimp [H]; omega)
  have a := Nat.mul_le_mul_left d lo
  have b : (p+1)*H ≤ (2*d)*H := Nat.mul_le_mul_right H (by omega)
  dsimp [H] at a b hi
  nlinarith

def word (width : Nat) (f : Nat → Bool) : Nat :=
  (BitVec.ofBoolListLE (List.ofFn (fun i : Fin width => f i.val))).toNat

lemma wordFits (k : Nat) (f : Nat → Bool) : word k f < 2^k := by
  simpa [word] using (BitVec.ofBoolListLE (List.ofFn (fun i : Fin k => f i.val))).isLt

lemma wordBit (k : Nat) (f : Nat → Bool) {i : Nat} (hi : i < k) :
    (word k f).testBit i = f i := by
  rw [word, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

def globalKey (k a x : Nat) : Nat :=
  word k (fun i => x.testBit ((i + (k - a%k)) % k))

lemma periodicBit {k a t : Nat} (ht : t < k) (x : Nat) :
    (globalKey k a x).testBit ((a+t)%k) = x.testBit t := by
  have hk : 0 < k := by omega
  have ha := Nat.mod_lt a hk
  rw [globalKey, wordBit _ _ (Nat.mod_lt _ hk)]
  congr 1
  calc ((a+t)%k + (k-a%k))%k
       = ((a%k+t)%k + (k-a%k))%k := by rw [Nat.mod_add_mod a k t]
     _ = (a%k+t+(k-a%k))%k := Nat.mod_add_mod _ _ _
     _ = (t+k)%k := by congr 1; omega
     _ = t := by simp [Nat.mod_eq_of_lt ht]

lemma rawSeparation : ∀ i j : Fin 3,
    (raw i).testBit 1 = (raw j).testBit 1 →
    (raw i).testBit 5 = (raw j).testBit 5 → i = j := by decide +kernel

def globalMenu (k a : Nat) := Finset.univ.image (fun i : Fin 3 => globalKey k a (raw i))

lemma menuCard {k a : Nat} (hk : 11 ≤ k) : (globalMenu k a).card = 3 := by
  have inj : Function.Injective (fun i : Fin 3 => globalKey k a (raw i)) := by
    intro i j he
    apply rawSeparation i j
    · simpa only [periodicBit (show 1 < k by omega)] using
        congrArg (fun z : Nat => z.testBit ((a+1)%k)) he
    · simpa only [periodicBit (show 5 < k by omega)] using
        congrArg (fun z : Nat => z.testBit ((a+5)%k)) he
  simp [globalMenu, Finset.card_image_of_injective _ inj]

lemma menuSubset (k a : Nat) : globalMenu k a ⊆ Finset.range (2^k) := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_range.mpr (wordFits _ _)

def shift (k start : Nat) (col : Bool) (x j : Nat) : Bool :=
  let bit := fun back : Nat => x.testBit ((start+j+k-back) % k)
  if col then xor (bit 1) (xor (bit 3) (bit 5))
  else xor (bit 0) (xor (bit 1) (bit 2))

lemma rowShift {h k : Nat} (start : Nat) (hh : 5 ≤ h) (hk : h+6 ≤ k)
    (i : Fin 3) (t : Fin 7) :
    shift k start false (globalKey k (start+h+k-9) (raw i)) (h-5+t.val) =
      (rowPulse i).testBit t.val := by
  have ht := t.isLt
  rw [rowWindow i t]
  simp only [shift, Bool.false_eq_true, ↓reduceIte]
  have idx (b : Nat) (hb : b ≤ 2) :
      start+(h-5+t.val)+k-b = start+h+k-9+(4-b+t.val) := by omega
  rw [idx 0 (by decide), idx 1 (by decide), idx 2 (by decide)]
  simp only [Nat.reduceSub]
  rw [periodicBit (by omega), periodicBit (by omega), periodicBit (by omega)]

lemma colShift {h k : Nat} (start : Nat) (hh : 5 ≤ h) (hk : h+6 ≤ k)
    (i : Fin 3) (t : Fin 6) :
    shift k start true (globalKey k (start+h+k-9) (raw i)) (h-4+t.val) =
      (colPulse i).testBit t.val := by
  have ht := t.isLt
  rw [colWindow i t]
  simp only [shift, ↓reduceIte]
  have idx (b : Nat) (hb : b ≤ 5) :
      start+(h-4+t.val)+k-b = start+h+k-9+(5-b+t.val) := by omega
  rw [idx 1 (by decide), idx 3 (by decide), idx 5 (by decide)]
  simp only [Nat.reduceSub, Nat.zero_add]
  rw [periodicBit (by omega), periodicBit (by omega), periodicBit (by omega)]

def suffix (n h u : Nat) : Fin (2^(n+2)) :=
  ⟨(u >>> (h-n)) % 2^(n+2), Nat.mod_lt _ (by positivity)⟩

lemma suffixBit {n h u i : Nat} (hi : i < n+2) :
    (suffix n h u).val.testBit i = u.testBit (h-n+i) := by
  simp [suffix, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, hi]

lemma packCongr {n : Nat} {f g : Nat → Bool} (he : ∀ i < n, f i = g i) :
    pack n f = pack n g := by
  have aux (l : List Nat) (hl : ∀ i ∈ l, i < n) (a : Nat) :
      l.foldl (fun z i => if f i then z+2^i else z) a =
      l.foldl (fun z i => if g i then z+2^i else z) a := by
    induction l generalizing a with
    | nil => rfl
    | cons j js ih =>
      simp only [List.foldl_cons]
      rw [he j (hl _ (by simp))]
      exact ih (fun i hi => hl i (by simp [hi])) _
  exact aux _ (by simp) 0

lemma chiLocal {u v : Nat → Bool} {s i : Nat}
    (h₀ : u i = v (s+i)) (h₁ : u (i+1) = v (s+(i+1)))
    (h₂ : u (i+2) = v (s+(i+2))) : chi u i = chi v (s+i) := by
  simp only [chi, h₀, h₁, h₂, Nat.add_assoc]

def tailReply (n h u : Nat) := pack n (fun i => chi u.testBit (h-n+i))
def tailObservation (n h k start : Nat) (col : Bool) (key u : Nat) :=
  pack n (fun i => chi (fun j => xor (u.testBit j) (shift k start col key j)) (h-n+i))

lemma packedReply (n h u : Nat) : reply n (suffix n h u) = tailReply n h u := by
  apply packCongr
  intro i hi
  apply chiLocal <;> apply suffixBit <;> omega

lemma packedObservation {n h k start key u pulse : Nat} {col : Bool}
    (hs : ∀ i < n+2, shift k start col key (h-n+i) = pulse.testBit i) :
    sense n (suffix n h u) pulse = tailObservation n h k start col key u := by
  apply packCongr
  intro i hi
  have bit (t : Nat) (ht : t < n+2) :
      xor ((suffix n h u).val.testBit t) (pulse.testBit t) =
        xor (u.testBit (h-n+t)) (shift k start col key (h-n+t)) := by rw [suffixBit ht, hs _ ht]
  apply chiLocal (s := h-n) <;> apply bit <;> omega

lemma fullSuffixRecovery {h k : Nat} (start r c : Nat) (hh : 5 ≤ h) (hk : h+6 ≤ k) :
    let a := tailReply 5 h r
    let b := tailReply 4 h c
    let i := select a b
    let key := globalKey k (start+h+k-9) (raw i)
    key ∈ globalMenu k (start+h+k-9) ∧
    decode 5 a (tailObservation 5 h k start false key r) (rowPulse i) = (suffix 5 h r).val ∧
    decode 4 b (tailObservation 4 h k start true key c) (colPulse i) = (suffix 4 h c).val := by
  dsimp only
  let i := select (tailReply 5 h r) (tailReply 4 h c)
  have hr := packedObservation (u := r) (fun t (ht : t < 5+2) => rowShift start hh hk i ⟨t, ht⟩)
  have hc := packedObservation (u := c) (fun t (ht : t < 4+2) => colShift start hh hk i ⟨t, ht⟩)
  have hpair := pairedRecovery (suffix 5 h r) (suffix 4 h c)
  dsimp only at hpair
  rw [packedReply, packedReply] at hpair
  obtain ⟨hpr, hpc⟩ := hpair
  exact ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
    hr ▸ hpr, hc ▸ hpc⟩

def rebuild (y : Nat → Bool) : Nat → Bool → Bool → Nat → Bool
  | 0, a, b, i => if i = 0 then a else b
  | h+1, a, b, i => if i = h+2 then b else rebuild y h (xor (y h) (!a && b)) a i

lemma rebuildCorrect (u : Nat → Bool) (h i : Nat) (hi : i < h+2) :
    rebuild (chi u) h (u h) (u (h+1)) i = u i := by
  induction h with
  | zero =>
    interval_cases i <;> rfl
  | succ h ih =>
    by_cases he : i = h+2
    · subst i
      simp [rebuild]
    · simp only [rebuild, ite_eq_right he, step]
      exact ih (by omega)

lemma recoveredBits {n h u : Nat} (hn : n ≤ h) (s : Nat) (he : s = (suffix n h u).val)
    (i : Nat) (hi : i < h+2) :
    rebuild (chi u.testBit) h (s.testBit n) (s.testBit (n+1)) i = u.testBit i := by
  subst s
  rw [suffixBit (by omega), suffixBit (by omega)]
  have e0 : h-n+n = h := by omega
  have e1 : h-n+(n+1) = h+1 := by omega
  rw [e0, e1]
  exact rebuildCorrect _ _ _ hi

def encoded {k : Nat} (f : Fin k → Bool) : Nat :=
  ∑ i : Fin k, if f i then 2^i.val else 0

lemma encodedStep {k : Nat} (f : Fin (k+1) → Bool) :
    encoded f = Nat.bit (f 0) (encoded (fun i : Fin k => f i.succ)) := by
  rw [encoded, Fin.sum_univ_succ, Nat.bit_val, encoded, Finset.mul_sum]
  have he (i : Fin k) :
      (if f i.succ then 2^i.succ.val else 0) =
        2*(if f i.succ then 2^i.val else 0) := by
    cases f i.succ <;> simp [pow_succ, Nat.mul_comm]
  simp_rw [he]
  cases f 0 <;> simp [Nat.add_comm]

lemma encodedTap {k : Nat} (f : Fin k → Bool) (i : Fin k) :
    (encoded f).testBit i.val = f i := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    rw [encodedStep]
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Nat.testBit_bit_zero _ _
    · let z := Nat.bit (f 0) (encoded (fun j : Fin k => f j.succ))
      change z.testBit (j.val+1) = _
      rw [Nat.add_comm j.val 1, ← Nat.testBit_shiftRight]
      simp only [z, Nat.bit_shiftRight_one]
      exact ih _ j

end PEqualNP.Outside.L_meta_40374

namespace PEqualNP.Outside.L_meta_40374.Lower

abbrev State := Nat → Bool
abbrev Signal := State → Bool

def zeroState : State := fun _ => false
def atom (a : Nat) : State := fun i => decide (i = a)
def pair (a b : Nat) : State := fun i => decide (i = a ∨ i = b)
def coordinate (i : Nat) : Signal := fun u => u i
def chi (i : Nat) : Signal := fun u => xor (u i) (!(u (i+1)) && u (i+2))
def first (z : Nat) (f : Signal) := xor (f zeroState) (f (atom z))
def mixed (j : Nat) (f : Signal) :=
  xor (xor (f zeroState) (f (atom (j+1)))) (xor (f (atom (j+2))) (f (pair (j+1) (j+2))))

lemma mixedCoordinate (j i : Nat) : mixed j (coordinate i) = false := by
  by_cases h : i = j+1 <;> by_cases g : i = j+2 <;>
    simp_all [mixed, coordinate, zeroState, atom, pair]

lemma mixedChi (j i : Nat) : mixed j (chi i) = decide (i = j) := by
  rcases lt_trichotomy (i+1) j with hl | he | hg
  · have h₀ : i ≠ j := by omega
    have h₁ : i ≠ j+1 := by omega
    have h₂ : i ≠ j+2 := by omega
    have h₃ : i+1 ≠ j+1 := by omega
    have h₄ : i+1 ≠ j+2 := by omega
    have h₅ : i+2 ≠ j+1 := by omega
    have h₆ : i+2 ≠ j+2 := by omega
    simp_all [mixed, chi, zeroState, atom, pair]
  · subst j
    have h₁ : i ≠ i+1+1 := by omega
    have h₂ : i ≠ i+1+2 := by omega
    simp [mixed, chi, zeroState, atom, pair, h₁, h₂]
  · rcases lt_trichotomy i (j+2) with h | h | h
    · have : i = j ∨ i = j+1 := by omega
      rcases this with rfl | rfl <;> simp [mixed, chi, zeroState, atom, pair]
    · subst i
      simp [mixed, chi, zeroState, atom, pair]
    · have h₀ : i ≠ j := by omega
      have h₁ : i ≠ j+1 := by omega
      have h₂ : i ≠ j+2 := by omega
      have h₃ : i+1 ≠ j+1 := by omega
      have h₄ : i+1 ≠ j+2 := by omega
      have h₅ : i+2 ≠ j+1 := by omega
      have h₆ : i+2 ≠ j+2 := by omega
      simp_all [mixed, chi, zeroState, atom, pair]

lemma firstCoordinate (z i : Nat) : first z (coordinate i) = decide (i=z) := by
  simp [first, coordinate, zeroState, atom]

lemma firstChi (z i : Nat) : first z (chi i) = xor (decide (i=z)) (decide (i+2=z)) := by
  by_cases h : i+1=z <;> by_cases h' : i+2=z <;>
    simp_all [first, chi, zeroState, atom]
  omega

def project (z : Nat) (f : Signal) : Bool :=
  xor (xor (first z f) (mixed z f)) (if 2 ≤ z then mixed (z-2) f else false)

lemma projectCoordinate (z i : Nat) : project z (coordinate i) = decide (i=z) := by
  simp [project, firstCoordinate, mixedCoordinate]

lemma projectChi (z i : Nat) : project z (chi i) = false := by
  simp only [project, firstChi, mixedChi]
  by_cases h : 2 ≤ z
  · have eqn : (i=z-2) ↔ (i+2=z) := by omega
    simp only [h, ↓reduceIte, eqn]
    cases decide (i=z) <;> cases decide (i+2=z) <;> rfl
  · have hn : i+2 ≠ z := by omega
    simp [h, hn]

lemma mixRegular (a b c d e f g h : Bool) :
    xor (xor (xor a e) (xor b f)) (xor (xor c g) (xor d h)) =
      xor (xor (xor a b) (xor c d)) (xor (xor e f) (xor g h)) := by
  revert a b c d e f g h
  decide

lemma interchange (a b c d : Bool) :
    xor (xor a c) (xor b d) = xor (xor a b) (xor c d) := by
  revert a b c d
  decide

lemma mixedXor (j : Nat) (f g : Signal) :
    mixed j (fun u => xor (f u) (g u)) = xor (mixed j f) (mixed j g) := mixRegular _ _ _ _ _ _ _ _

lemma firstXor (j : Nat) (f g : Signal) :
    first j (fun u => xor (f u) (g u)) = xor (first j f) (first j g) := interchange _ _ _ _

lemma projectXor (j : Nat) (f g : Signal) :
    project j (fun u => xor (f u) (g u)) = xor (project j f) (project j g) := by
  unfold project
  simp only [firstXor, mixedXor]
  split <;> try simp only [Bool.xor_false]
  · rw [interchange (first j f) (mixed j f) (first j g) (mixed j g)]
    exact interchange _ _ _ _
  · exact interchange _ _ _ _

lemma projectConst (j : Nat) (b : Bool) : project j (fun _ => b) = false := by
  simp [project, first, mixed]

abbrev Strips := Bool → State
abbrev StripSignal := Strips → Bool

def signature (bank : Bool) (z : Nat) (f : StripSignal) : Bool :=
  project z (fun u => f (fun c => if c = bank then u else zeroState))

lemma signatureConst (bank : Bool) (z : Nat) (b : Bool) :
    signature bank z (fun _ => b) = false := projectConst _ _

lemma signatureXor (bank : Bool) (z : Nat) (f g : StripSignal) :
    signature bank z (fun u => xor (f u) (g u)) =
      xor (signature bank z f) (signature bank z g) := projectXor _ _ _

lemma signatureCoordinate (bank c : Bool) (z i : Nat) :
    signature bank z (fun s => s c i) = (decide (c=bank) && decide (i=z)) := by
  by_cases hc : c = bank
  · simp only [signature, hc, ↓reduceIte, decide_true, Bool.true_and]
    exact projectCoordinate _ _
  · simp only [signature, hc, ↓reduceIte, decide_false, Bool.false_and]
    exact projectConst _ _

lemma signatureReply (bank c : Bool) (z i : Nat) :
    signature bank z (fun s => chi i (s c)) = false := by
  by_cases hc : c = bank
  · simp only [signature, hc, ↓reduceIte]
    exact projectChi _ _
  · simp only [signature, hc, ↓reduceIte]
    exact projectConst _ _

lemma affineTable : ∀ a b c d : Bool, xor (xor a b) (xor c d) = false →
    ∀ x y : Bool, (if x then (if y then d else c) else (if y then b else a)) =
      xor a (xor (x && xor a c) (y && xor a b)) := by decide

abbrev F := ZMod 2
abbrev Index (h : Nat) := Bool × Fin (h+2)

def fbit (b : Bool) : F := if b then 1 else 0
def vector (h : Nat) (f : StripSignal) (i : Index h) : F :=
  fbit (signature i.1 i.2.val f)

lemma vectorXor (h : Nat) (f g : StripSignal) :
    vector h (fun s => xor (f s) (g s)) = vector h f + vector h g := by
  funext i
  change fbit (signature _ _ _) = fbit (signature _ _ _) + fbit (signature _ _ _)
  rw [signatureXor]
  generalize signature i.1 i.2.val f = a
  generalize signature i.1 i.2.val g = b
  cases a <;> cases b <;> decide

lemma vectorConst (h : Nat) (b : Bool) : vector h (fun _ => b) = 0 := by
  funext i
  simp [vector, signatureConst, fbit]

lemma vectorReply (h : Nat) (c : Bool) (i : Nat) : vector h (fun s => chi i (s c)) = 0 := by
  funext a
  simp [vector, signatureReply, fbit]

lemma vectorCoordinate (h : Nat) (i : Index h) :
    vector h (fun s => s i.1 i.2.val) = Pi.single i 1 := by
  classical
  funext j
  by_cases he : i = j
  · subst j
    simp [vector, signatureCoordinate, fbit]
  · have hne : ¬ (i.1=j.1 ∧ i.2.val=j.2.val) := by
      rintro ⟨a,b⟩
      exact he (Prod.ext a (Fin.ext b))
    simp [vector, signatureCoordinate, fbit, Pi.single_eq_of_ne (Ne.symm he), hne]

lemma spanOutputs (h : Nat) (T : Submodule F (Index h → F))
    (ho : ∀ i : Index h, vector h (fun s => s i.1 i.2.val) ∈ T) :
    2*(h+2) ≤ Module.finrank F T := by
  classical
  have hs : ∀ i : Index h, Pi.single i (1:F) ∈ T := fun i => vectorCoordinate _ _ ▸ ho i
  have all : T = ⊤ := by
    apply top_unique
    intro v _
    have hv : ∑ i : Index h, v i • (Pi.single i (1:F) : Index h → F) = v := by
      funext j
      simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, mul_ite]
    rw [← hv]
    exact T.sum_mem (fun i _ => T.smul_mem _ (hs i))
  rw [all]
  simp

end PEqualNP.Outside.L_meta_40374.Lower

namespace PEqualNP.Outside.L_meta_40374.Cost
open PEqualNP.CircuitLowerBounds

abbrev F := ZMod 2
abbrev Signal (X : Type) := X → Bool

def nonlinear (g : Gate) :=
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def tap {X : Type} (w : List (Signal X)) (i : Nat) := w.getD i (fun _ => false)

def next {X : Type} (w : List (Signal X)) (g : Gate) : Signal X :=
  fun x => g.op.eval (g.inputs.map (fun i => tap w i x))

lemma affineBinary (q : Bool → Bool → Bool)
    (hq : xor (xor (q false false) (q false true)) (xor (q true false) (q true true)) = false)
    (u v : Bool) :
    q u v = xor (q false false)
      (xor (if xor (q false false) (q true false) then u else false)
           (if xor (q false false) (q false true) then v else false)) := by
  cases u <;> cases v <;>
    generalize q false false = a at * <;> generalize q false true = b at * <;>
    generalize q true false = c at * <;> generalize q true true = d at * <;>
    cases a <;> cases b <;> cases c <;> cases d <;> revert hq <;> decide

variable {X V : Type} [AddCommGroup V]

abbrev Measure (X V : Type) [AddCommGroup V] :=
  {v : Signal X → V // (∀ b, v (fun _ => b) = 0) ∧
    ∀ f g, v (fun x => xor (f x) (g x)) = v f + v g}

lemma Measure.const (m : Measure X V) (b : Bool) : m.val (fun _ => b) = 0 := m.property.1 b

lemma Measure.add (m : Measure X V) (f g : Signal X) :
    m.val (fun x => xor (f x) (g x)) = m.val f + m.val g := m.property.2 f g

variable [Module F V]

lemma masked (m : Measure X V) (S : Submodule F V) (q : Bool) {f : Signal X}
    (hf : m.val f ∈ S) : m.val (fun x => if q then f x else false) ∈ S := by
  cases q
  · change m.val (fun _ => false) ∈ S
    rw [m.const]; exact S.zero_mem
  · exact hf

lemma binaryMem (m : Measure X V) (S : Submodule F V) {f g : Signal X}
    (hf : m.val f ∈ S) (hg : m.val g ∈ S) (q : Bool → Bool → Bool)
    (hq : xor (xor (q false false) (q false true)) (xor (q true false) (q true true)) = false) :
    m.val (fun x => q (f x) (g x)) ∈ S := by
  let a : Signal X := fun _ => q false false
  let b : Signal X := fun x => if xor (q false false) (q true false) then f x else false
  let c : Signal X := fun x => if xor (q false false) (q false true) then g x else false
  have he : (fun x => q (f x) (g x)) = (fun x => xor (a x) (xor (b x) (c x))) :=
    funext (fun x => affineBinary q hq _ _)
  rw [he, m.add, m.add, m.const, zero_add]
  exact S.add_mem (masked m S _ hf) (masked m S _ hg)

lemma tapMem (m : Measure X V) (S : Submodule F V) {w : List (Signal X)}
    (hw : ∀ f ∈ w, m.val f ∈ S) (i : Nat) : m.val (tap w i) ∈ S := by
  by_cases h : i < w.length
  · simpa [tap, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h] using
      hw w[i] (List.getElem_mem h)
  · simp [tap, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : w.length ≤ i), m.const]

lemma freeGate (m : Measure X V) (S : Submodule F V) {w : List (Signal X)}
    (hw : ∀ f ∈ w, m.val f ∈ S) (g : Gate) (hl : g.inputs.length ≤ 2) (hn : nonlinear g = false) :
    m.val (next w g) ∈ S := by
  rcases g with ⟨op, ins⟩
  match ins with
  | [] =>
    change m.val (fun _ => op.eval []) ∈ S
    rw [m.const]; exact S.zero_mem
  | [i] =>
    let q := fun a (_ : Bool) => op.eval [a]
    have hq : xor (xor (q false false) (q false true)) (xor (q true false) (q true true)) = false := by simp [q]
    exact binaryMem m S (tapMem m S hw i) (tapMem m S hw i) q hq
  | [i,j] =>
    exact binaryMem m S (tapMem m S hw i) (tapMem m S hw j) (fun a b => op.eval [a,b])
      (by simpa [nonlinear] using hn)
  | _::_::_::_ => simp at hl

def run {X : Type} (gs : List Gate) (w : List (Signal X)) :=
  gs.foldl (fun v g => v ++ [next v g]) w

lemma runSpec (gs : List Gate) (w : List (Signal X)) (x : X) :
    (run gs w).map (fun f => f x) = (⟨gs, 0⟩ : Circuit).wires (w.map (fun f => f x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w ++ [next w g])).map _ =
      (⟨gs, 0⟩ : Circuit).wires
        (w.map (fun f => f x) ++ [g.op.eval (g.inputs.map (fun i => (w.map (fun f => f x)).getD i false))])
    rw [ih, List.map_append, List.map_singleton]
    congr 3
    unfold next tap
    congr 2
    funext i
    exact (List.getD_map w (fun _ => false) (fun f => f x)).symm

lemma extendOne [FiniteDimensional F V] (S : Submodule F V) (v : V) :
    Module.finrank F ↥(S ⊔ Submodule.span F {v}) ≤ Module.finrank F S + 1 := by
  have h := Submodule.finrank_add_le_finrank_add_finrank S (Submodule.span F {v})
  by_cases hv : v = 0
  · subst v
    rw [Submodule.span_zero_singleton, sup_bot_eq]
    omega
  · rw [finrank_span_singleton hv] at h
    exact h

lemma rankRun [FiniteDimensional F V] (m : Measure X V) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) (w : List (Signal X)) (S : Submodule F V)
    (hw : ∀ f ∈ w, m.val f ∈ S) :
    ∃ T : Submodule F V, S ≤ T ∧ Module.finrank F T ≤ Module.finrank F S + gs.countP nonlinear ∧
      ∀ f ∈ run gs w, m.val f ∈ T := by
  classical
  induction gs generalizing w S with
  | nil => exact ⟨S, le_rfl, by simp, hw⟩
  | cons g gs ih =>
    have hg' : ∀ a ∈ gs, a.inputs.length ≤ 2 := fun a ha => hg a (List.mem_cons_of_mem _ ha)
    have hl := hg g (List.mem_cons_self ..)
    have one : ∃ R : Submodule F V, S ≤ R ∧
        Module.finrank F R ≤ Module.finrank F S + (if nonlinear g then 1 else 0) ∧
        m.val (next w g) ∈ R := by
      cases hn : nonlinear g
      · exact ⟨S, le_rfl, by simp, freeGate m S hw g hl hn⟩
      · exact ⟨S ⊔ Submodule.span F {m.val (next w g)}, le_sup_left, extendOne S (m.val (next w g)),
          Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))⟩
    obtain ⟨R, hs, hr, hn⟩ := one
    have hnew : ∀ f ∈ w ++ [next w g], m.val f ∈ R := by
      intro f hf
      rcases List.mem_append.mp hf with hf | hf
      · exact hs (hw f hf)
      · simpa only [List.mem_singleton.mp hf] using hn
    obtain ⟨T, ht, hd, hall⟩ := ih hg' _ R hnew
    refine ⟨T, hs.trans ht, ?_, hall⟩
    rw [List.countP_cons]
    omega

lemma seedExtras [FiniteDimensional F V] (m : Measure X V) (S : Submodule F V) (fs : List (Signal X)) :
    ∃ T : Submodule F V, S ≤ T ∧ Module.finrank F T ≤ Module.finrank F S + fs.length ∧
      ∀ f ∈ fs, m.val f ∈ T := by
  induction fs generalizing S with
  | nil => exact ⟨S, le_rfl, by simp, by simp⟩
  | cons f fs ih =>
    let R := S ⊔ Submodule.span F {m.val f}
    have hs : S ≤ R := le_sup_left
    have hv : m.val f ∈ R := Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
    have hsize := extendOne S (m.val f)
    obtain ⟨T, hR, hd, hall⟩ := ih R
    refine ⟨T, hs.trans hR, ?_, ?_⟩
    · change Module.finrank F R ≤ _ at hsize
      simp only [List.length_cons]
      omega
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hR hv
      · exact hall g hg

lemma twoCircuits [FiniteDimensional F V] (m : Measure X V) (p d : List Gate)
    (hp : ∀ g ∈ p, g.inputs.length ≤ 2) (hd : ∀ g ∈ d, g.inputs.length ≤ 2)
    (input sensors decInput : List (Signal X)) (hi : ∀ f ∈ input, m.val f = 0)
    (hroute : ∀ f ∈ decInput, f ∈ run p input ∨ f ∈ sensors ∨ m.val f = 0) :
    ∃ T : Submodule F V, Module.finrank F T ≤ p.countP nonlinear + d.countP nonlinear + sensors.length ∧
      ∀ f ∈ run d decInput, m.val f ∈ T := by
  obtain ⟨P, _, hP, pmem⟩ := rankRun m p hp input ⊥ (fun f hf => by simp [hi f hf])
  obtain ⟨S, hPS, hS, smem⟩ := seedExtras m P sensors
  obtain ⟨T, _, hT, tmem⟩ := rankRun m d hd decInput S (fun f hf => by
    rcases hroute f hf with h | h | h
    · exact hPS (pmem f h)
    · exact smem f h
    · rw [h]; exact S.zero_mem)
  refine ⟨T, ?_, tmem⟩
  simp only [finrank_bot, zero_add] at hP
  omega

end PEqualNP.Outside.L_meta_40374.Cost

namespace PEqualNP.Outside.L_meta_40374
open PEqualNP.CircuitLowerBounds

def vectorMeasure (h : Nat) : Cost.Measure Lower.Strips (Lower.Index h → ZMod 2) :=
  ⟨Lower.vector h, Lower.vectorConst h, Lower.vectorXor h⟩

lemma dimensionBound (h : Nat) (P D : Circuit)
    (hp : ∀ g ∈ P.gates, g.inputs.length ≤ 2) (hd : ∀ g ∈ D.gates, g.inputs.length ≤ 2)
    (y samples ins : List Lower.StripSignal)
    (hy : ∀ f ∈ y, Lower.vector h f = 0)
    (hr : ∀ f ∈ ins, f ∈ Cost.run P.gates y ∨ f ∈ samples ∨ Lower.vector h f = 0)
    (out : Lower.Index h → Nat)
    (ho : ∀ (s : Lower.Strips) (i : Lower.Index h),
      (D.wires (ins.map (fun f => f s))).getD (out i) false = s i.1 i.2.val) :
    2*(h+2) ≤ P.gates.countP Cost.nonlinear + D.gates.countP Cost.nonlinear + samples.length := by
  obtain ⟨T, hT, hall⟩ := Cost.twoCircuits (vectorMeasure h) _ _ hp hd y samples ins hy hr
  apply Nat.le_trans (Lower.spanOutputs h T ?_) hT
  intro i
  have mem := Cost.tapMem (vectorMeasure h) T hall (out i)
  have eq : Cost.tap (Cost.run D.gates ins) (out i) = (fun s => s i.1 i.2.val) := by
    funext s
    have w := Cost.runSpec D.gates ins s
    have q := congrArg (fun l : List Bool => l.getD (out i) false) w
    calc Cost.tap (Cost.run D.gates ins) (out i) s =
          ((Cost.run D.gates ins).map (fun f => f s)).getD (out i) false :=
            (List.getD_map _ (fun _ => false) (fun f => f s)).symm
         _ = _ := q.trans (ho s i)
  exact eq ▸ mem

end PEqualNP.Outside.L_meta_40374

namespace PEqualNP.Outside.L_meta_40374
open PEqualNP.CircuitLowerBounds

def valid (w : Nat) (C : Circuit) :=
  PEqualNP.MetaComplexity.NestedCover.ReadsBack w C ∧ ∀ g ∈ C.gates, g.inputs.length ≤ 2

def feasible (h k start n p d K : Nat) : Prop :=
  let U := Fin n → Fin (2^(h+2))
  let w := 2*n*h
  let W := w+n*(k+9)
  let shift := fun (col : Bool) (x j : Nat) =>
    let bit := fun back : Nat => x.testBit ((start+j+k-back) % k)
    if col then xor (bit 1) (xor (bit 3) (bit 5))
    else xor (bit 0) (xor (bit 1) (bit 2))
  let observe := fun (col : Bool) (x u len : Nat) =>
    List.ofFn (fun i : Fin len =>
      chi (fun l => xor (u.testBit l) (shift col x l)) (h-len+i.val))
  ∃ (menu : Finset Nat) (P D : PEqualNP.CircuitLowerBounds.Circuit)
    (keyTap : Fin n → Fin k → Nat) (out : Fin n → Bool → Fin (h+2) → Nat),
    menu ⊆ Finset.range (2^k) ∧ menu.card = 3 ∧ valid w P ∧ valid W D ∧
    (∀ j i, keyTap j i < w+P.gates.length) ∧
    (∀ j col i, out j col i < W+D.gates.length) ∧
    d*(P.gates.countP Cost.nonlinear+D.gates.countP Cost.nonlinear) ≤ n*(p*h+K) ∧
    ∀ (r c : U),
      let reply := fun (u : Nat) => List.ofFn (fun i : Fin h => chi (fun l => u.testBit l) i)
      let y := (List.ofFn (fun j : Fin n => reply (r j).val ++ reply (c j).val)).flatten
      let pre := P.wires y
      let chosen := fun j : Fin n =>
        ∑ i : Fin k, if pre.getD (keyTap j i) false then 2^i.val else 0
      (∀ j, chosen j ∈ menu) ∧
      let data := (List.ofFn (fun j : Fin n =>
        List.ofFn (fun i : Fin k => (chosen j).testBit i) ++
        observe false (chosen j) (r j).val 5 ++ observe true (chosen j) (c j).val 4)).flatten
      let wires := D.wires (y ++ data)
      ∀ j col i, wires.getD (out j col i) false = (if col then c j else r j).val.testBit i

end PEqualNP.Outside.L_meta_40374

namespace PEqualNP.Outside.L_meta_40374
open PEqualNP.CircuitLowerBounds

def bank (h : Nat) (b : Bool) (s : Lower.Strips) : Fin (2^(h+2)) :=
  ⟨word (h+2) (s b), wordFits _ _⟩

def yBank (h : Nat) (b : Bool) : List Lower.StripSignal :=
  List.ofFn (fun i : Fin h => fun s => Lower.chi i (s b))

lemma yBankEval (h : Nat) (b : Bool) (s : Lower.Strips) :
    (yBank h b).map (fun f => f s) =
      List.ofFn (fun i : Fin h => chi (bank h b s).val.testBit i) := by
  rw [yBank, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  have hi := i.isLt
  simp only [Function.comp_apply, Lower.chi, chi, bank]
  rw [wordBit _ _ (by omega), wordBit _ _ (by omega), wordBit _ _ (by omega)]

lemma yBankZero {h b} {f : Lower.StripSignal} (hf : f ∈ yBank h b) : Lower.vector h f = 0 := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
  exact Lower.vectorReply _ _ _

lemma ofFnOne {α : Type} (f : Fin 1 → α) : List.ofFn f = [f 0] := by simp [List.ofFn_succ]

lemma tapEval (P : Circuit) (y : List Lower.StripSignal) (u : Nat) (s : Lower.Strips) :
    Cost.tap (Cost.run P.gates y) u s = (P.wires (y.map (fun f => f s))).getD u false := by
  have h := Cost.runSpec P.gates y s
  calc Cost.tap (Cost.run P.gates y) u s =
         ((Cost.run P.gates y).map (fun f => f s)).getD u false :=
             (List.getD_map _ (fun _ => false) (fun f => f s)).symm
       _ = _ := congrArg (fun l : List Bool => l.getD u false) h

def obsSignals (h k start len : Nat) (b : Bool) (key : Lower.Strips → Nat) : List Lower.StripSignal :=
  List.ofFn (fun i : Fin len => fun s =>
    chi (fun j => xor ((bank h b s).val.testBit j) (shift k start b (key s) j)) (h-len+i.val))

lemma oneCostLower {h k start p d K : Nat} (work : feasible h k start 1 p d K) :
    ∃ g, 2*(h+2) ≤ g+9 ∧ d*g ≤ p*h+K := by
  obtain ⟨menu,P,D,tap,out,_,_,hP,hD,_,_,hcost,hcorrect⟩ := work
  let y := yBank h false ++ yBank h true
  let pre := Cost.run P.gates y
  let keyBit (i : Fin k) : Lower.StripSignal := Cost.tap pre (tap 0 i)
  let key (s : Lower.Strips) := encoded (fun i => keyBit i s)
  let keys := List.ofFn keyBit
  let sensors := obsSignals h k start 5 false key ++ obsSignals h k start 4 true key
  let ins := y ++ (keys ++ sensors)
  have hy : ∀ f ∈ y, Lower.vector h f = 0 := by
    intro f hf
    rcases List.mem_append.mp hf with hf | hf <;> exact yBankZero hf
  have route : ∀ f ∈ ins, f ∈ pre ∨ f ∈ sensors ∨ Lower.vector h f = 0 := by
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact Or.inr (Or.inr (hy _ hf))
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
      by_cases hi : tap 0 i < pre.length
      · left
        simpa only [keyBit, Cost.tap, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
          Option.getD_some] using List.getElem_mem (l := pre) hi
      · right; right
        simp [keyBit, Cost.tap, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : pre.length ≤ tap 0 i),
          Lower.vectorConst]
    · exact Or.inr (Or.inl hf)
  have evalY (s : Lower.Strips) : y.map (fun f => f s) =
      List.ofFn (fun i : Fin h => chi (bank h false s).val.testBit i) ++
      List.ofFn (fun i : Fin h => chi (bank h true s).val.testBit i) := by
    rw [List.map_append, yBankEval, yBankEval]
  have keyDef (s : Lower.Strips) : key s =
      ∑ i : Fin k, if (P.wires (y.map (fun f => f s))).getD (tap 0 i) false then 2^i.val else 0 := by
    unfold key encoded
    apply Finset.sum_congr rfl; intro i _
    exact congrArg (fun b : Bool => if b then 2^i.val else 0) (tapEval P y (tap 0 i) s)
  have keyEval (s : Lower.Strips) : keys.map (fun f => f s) =
      List.ofFn (fun i : Fin k => (key s).testBit i.val) := by
    rw [List.map_ofFn]; apply congrArg List.ofFn
    funext i; exact (encodedTap _ i).symm
  have correct (s : Lower.Strips) (i : Lower.Index h) :
      (D.wires (ins.map (fun f => f s))).getD (out 0 i.1 i.2) false = s i.1 i.2.val := by
    have hc := (hcorrect (fun _ => bank h false s) (fun _ => bank h true s)).2 0 i.1 i.2
    simp only [ofFnOne, List.flatten_cons, List.flatten_nil, List.append_nil] at hc
    rw [← evalY s, ← keyDef s] at hc
    have ie : ins.map (fun f => f s) = y.map (fun f => f s) ++
        (List.ofFn (fun j : Fin k => (key s).testBit j.val) ++
        ((obsSignals h k start 5 false key).map (fun f => f s) ++
         (obsSignals h k start 4 true key).map (fun f => f s))) := by
      simp only [ins, sensors, List.map_append, keyEval]
    rw [ie]
    simp only [obsSignals, List.map_ofFn, List.append_assoc] at hc ⊢
    cases hi : i.1 <;> simp only [hi, Bool.false_eq_true, ↓reduceIte, bank, wordBit _ _ i.2.isLt, shift] at hc ⊢ <;> exact hc
  have lower := dimensionBound h P D hP.2 hD.2 y sensors ins hy route (fun i => out 0 i.1 i.2) correct
  have nine : sensors.length = 9 := by simp [sensors, obsSignals]
  exact ⟨_, nine ▸ lower, by simpa using hcost⟩

lemma postedNecessity {p d K : Nat} (hw : ∀ h k start n, 5 ≤ h → h+6 ≤ k → feasible h k start n p d K) :
    2*d ≤ p :=
  necessarySlope (fun h hh => oneCostLower (hw h (h+6) 0 1 hh (by omega)))

end PEqualNP.Outside.L_meta_40374

namespace PEqualNP.Outside.L_meta_40374.Build
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover
abbrev Sig := Cost.Signal

def legal : Nat → List Gate → Prop
  | _, [] => True
  | w, g :: gs => (∀ i ∈ g.inputs, i < w) ∧ g.inputs.length ≤ 2 ∧ legal (w+1) gs

lemma legalAppend {w : Nat} {as bs : List Gate} (a : legal w as) (b : legal (w+as.length) bs) :
    legal w (as++bs) := by
  induction as generalizing w with
  | nil => simpa using b
  | cons g gs ih =>
    refine ⟨a.1, a.2.1, ih a.2.2 ?_⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using b

lemma legalValid {w : Nat} {gs : List Gate} (h : legal w gs) :
    ReadsBack w (⟨gs,0⟩ : Circuit) ∧ ∀ g ∈ gs, g.inputs.length ≤ 2 := by
  induction gs generalizing w with
  | nil => exact ⟨by intro j hj; simp at hj, by simp⟩
  | cons g gs ih =>
    obtain ⟨rb, fan⟩ := ih h.2.2
    constructor
    · intro j hj i hi
      cases j with
      | zero => exact h.1 i hi
      | succ j =>
        have hprev := rb j (by simpa using hj) i (by simpa [gateAt, List.getD_eq_getElem?_getD] using hi)
        omega
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact h.2.1
      · exact fan a ha

variable {X : Type}

def Ext (a b : List (Sig X)) (cost : Nat) : Prop :=
  ∃ gs, legal a.length gs ∧ gs.countP Cost.nonlinear ≤ cost ∧ Cost.run gs a = b

lemma lengthRun (gs : List Gate) (a : List (Sig X)) : (Cost.run gs a).length = a.length + gs.length := by
  induction gs generalizing a with
  | nil => simp [Cost.run]
  | cons g gs ih =>
    change (Cost.run gs (a++[Cost.next a g])).length = _
    rw [ih]
    simp [Nat.add_assoc, Nat.add_comm]

lemma useOld (gs : List Gate) {a : List (Sig X)} {f : Sig X} (h : f ∈ a) : f ∈ Cost.run gs a := by
  induction gs generalizing a with
  | nil => exact h
  | cons g gs ih => exact ih (List.mem_append_left _ h)

lemma Ext.old {a b : List (Sig X)} {n : Nat} (e : Ext a b n) {f : Sig X} (h : f ∈ a) : f ∈ b := by
  obtain ⟨gs,_,_,rfl⟩ := e
  exact useOld gs h

lemma Ext.refl (a : List (Sig X)) : Ext a a 0 := ⟨[], trivial, by decide, rfl⟩

lemma Ext.trans {a b c : List (Sig X)} {n m : Nat} (e : Ext a b n) (e' : Ext b c m) : Ext a c (n+m) := by
  obtain ⟨gs,hg,hc,rfl⟩ := e
  obtain ⟨ts,ht,hc',rfl⟩ := e'
  rw [lengthRun] at ht
  exact ⟨gs++ts, legalAppend hg ht, by rw [List.countP_append]; omega, by simp [Cost.run, List.foldl_append]⟩

lemma Ext.mono {a b : List (Sig X)} {n m : Nat} (e : Ext a b n) (h : n ≤ m) : Ext a b m := by
  obtain ⟨gs,hg,hc,he⟩ := e
  exact ⟨gs,hg,hc.trans h,he⟩

lemma fetch {f : Sig X} {a : List (Sig X)} (h : f ∈ a) :
    ∃ i < a.length, Cost.tap a i = f := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp h
  exact ⟨i,hi,by simpa [Cost.tap, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using he⟩

lemma emit (a : List (Sig X)) (g : Gate) (v : Sig X) (n : Nat)
    (hr : ∀ i ∈ g.inputs, i < a.length) (hl : g.inputs.length ≤ 2)
    (hc : (if Cost.nonlinear g then 1 else 0) ≤ n) (he : Cost.next a g = v) :
    Ext a (a++[v]) n := by
  refine ⟨[g], ⟨hr,hl,trivial⟩, ?_, ?_⟩
  · simpa [List.countP_cons] using hc
  · simp [Cost.run, he]

lemma emitConst (a : List (Sig X)) (b : Bool) : Ext a (a++[fun _ => b]) 0 := by
  cases b
  · exact emit a ⟨.or, []⟩ _ 0 (by simp) (by decide) (by decide) rfl
  · exact emit a ⟨.and, []⟩ _ 0 (by simp) (by decide) (by decide) rfl

lemma emitNot (a : List (Sig X)) {f : Sig X} (hf : f ∈ a) : Ext a (a++[fun x => !(f x)]) 0 := by
  obtain ⟨i,hi,he⟩ := fetch hf
  exact emit a ⟨.not,[i]⟩ _ 0 (by simpa using hi) (by change 1 ≤ 2; decide) (by rfl)
    (by funext x; simp [Cost.next, GateOp.eval, he])

lemma emitBinary (a : List (Sig X)) {f g : Sig X} (hf : f ∈ a) (hg : g ∈ a)
    (op : GateOp) (fn : Bool → Bool → Bool) (n : Nat)
    (hfun : ∀ x y, op.eval [x,y] = fn x y)
    (hc : ∀ i j : Nat, (if Cost.nonlinear ⟨op,[i,j]⟩ then 1 else 0) ≤ n) :
    Ext a (a++[fun x => fn (f x) (g x)]) n := by
  obtain ⟨i,hi,he⟩ := fetch hf
  obtain ⟨j,hj,he'⟩ := fetch hg
  exact emit a ⟨op,[i,j]⟩ _ n (by intro t ht; simp at ht; rcases ht with rfl|rfl <;> assumption)
    (by change 2 ≤ 2; decide) (hc i j) (by funext x; simp [Cost.next, he, he', hfun])

lemma emitAnd (a : List (Sig X)) {f g : Sig X} (hf : f ∈ a) (hg : g ∈ a) :
    Ext a (a++[fun x => f x && g x]) 1 :=
  emitBinary a hf hg .and (· && ·) 1
    (by intro x y; cases x <;> cases y <;> rfl) (by intro _ _; rfl)

lemma emitXor (a : List (Sig X)) {f g : Sig X} (hf : f ∈ a) (hg : g ∈ a) :
    ∃ b, Ext a b 0 ∧ (fun x => xor (f x) (g x)) ∈ b := by
  let q := fun x => !(xor (f x) (g x))
  have xnor : Ext a (a++[q]) 0 := emitBinary a hf hg (.mod 2) (fun x y => !(xor x y)) 0
    (by intro x y; cases x <;> cases y <;> decide) (by intro _ _; rfl)
  have no := emitNot (a++[q]) (f:=q) (by simp)
  exact ⟨_, xnor.trans no, by simp [q]⟩

lemma emitMux (a : List (Sig X)) {b lo hi : Sig X}
    (hb : b ∈ a) (hl : lo ∈ a) (hh : hi ∈ a) :
    ∃ w, Ext a w 1 ∧ (fun x => if b x then hi x else lo x) ∈ w := by
  obtain ⟨v,e,hm⟩ := emitXor a hl hh
  have f := emitAnd v (e.old hb) hm
  obtain ⟨w,g,hw⟩ := emitXor _ (f.old (e.old hl))
    (List.mem_append_right v (List.mem_singleton_self (fun x => b x && xor (lo x) (hi x))))
  have identity : (fun x => xor (lo x) (b x && xor (lo x) (hi x))) =
      (fun x => if b x then hi x else lo x) := by
    funext x
    cases b x <;> cases lo x <;> cases hi x <;> rfl
  exact ⟨w,(e.trans f).trans g,identity ▸ hw⟩

def tableCost : Nat → Nat
  | 0 => 0
  | n+1 => tableCost n + tableCost n + 1

lemma emitTable {m : Nat} (a : List (Sig X)) (bits : Fin m → Sig X)
    (hb : ∀ i, bits i ∈ a) (q : (Fin m → Bool) → Bool) :
    ∃ w, Ext a w (tableCost m) ∧ (fun x => q (fun i => bits i x)) ∈ w := by
  induction m generalizing a with
  | zero =>
    let v := q Fin.elim0
    have he : (fun x => q (fun i => bits i x)) = (fun _ : X => v) := by
      funext x; congr 1; funext i; exact Fin.elim0 i
    exact ⟨_,emitConst a v,he ▸ (by simp)⟩
  | succ m ih =>
    let rest := fun i : Fin m => bits i.succ
    let ql := fun s : Fin m → Bool => q (Fin.cons false s)
    let qh := fun s : Fin m → Bool => q (Fin.cons true s)
    obtain ⟨v,e,hl⟩ := ih a rest (fun i => hb i.succ) ql
    obtain ⟨t,f,hr⟩ := ih v rest (fun i => e.old (hb i.succ)) qh
    obtain ⟨w,g,hw⟩ := emitMux t (f.old (e.old (hb 0))) (f.old hl) hr
    refine ⟨w,(e.trans f).trans g,?_⟩
    have he : (fun x => if bits 0 x then qh (fun i => rest i x) else ql (fun i => rest i x)) =
        (fun x => q (fun i => bits i x)) := by
      funext x
      cases hx : bits 0 x <;> simp only [Bool.false_eq_true, ↓reduceIte, qh, ql]
      all_goals
        apply congrArg q
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hx.symm
        · rfl
    exact he ▸ hw

lemma emitMany {ι : Type} (indices : List ι) (unitCost : Nat) (a : List (Sig X))
    (wanted : ι → Sig X)
    (one : ∀ w, (∀ f ∈ a, f ∈ w) → ∀ i ∈ indices,
      ∃ b, Ext w b unitCost ∧ wanted i ∈ b) :
    ∃ b, Ext a b (indices.length*unitCost) ∧ ∀ i ∈ indices, wanted i ∈ b := by
  induction indices generalizing a with
  | nil => exact ⟨a, by simpa using Ext.refl a, by simp⟩
  | cons i is ih =>
    obtain ⟨w,e,hw⟩ := one a (fun _ h => h) i (by simp)
    obtain ⟨b,f,hb⟩ := ih w (fun t ht j hj => one t (fun z hz => ht z (e.old hz)) j (by simp [hj]))
    refine ⟨b, ?_, ?_⟩
    · simpa [Nat.succ_mul, Nat.add_comm] using e.trans f
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact f.old hw
      · exact hb _ hj

lemma strip (h : Nat) (a : List (Sig X)) (u : Nat → Sig X)
    (hr : ∀ i < h, (fun x => xor (u i x) (!(u (i+1) x) && u (i+2) x)) ∈ a)
    (h₀ : u h ∈ a) (h₁ : u (h+1) ∈ a) :
    ∃ b, Ext a b h ∧ ∀ i < h+2, u i ∈ b := by
  induction h generalizing a with
  | zero =>
    exact ⟨a, Ext.refl a, by intro i hi; interval_cases i <;> assumption⟩
  | succ h ih =>
    have e := emitNot a h₀
    have f := emitAnd _ (List.mem_append_right a (List.mem_singleton_self (fun x => !(u (h+1) x)))) (e.old h₁)
    obtain ⟨v,g,hg⟩ := emitXor _ (f.old (e.old (hr h (by omega))))
      (List.mem_append_right _ (List.mem_singleton_self (fun x => !(u (h+1) x) && u (h+2) x)))
    have pre := (e.trans f).trans g
    have hu : u h ∈ v := by
      have z : (fun x => xor (xor (u h x) (!(u (h+1) x) && u (h+2) x)) (!(u (h+1) x) && u (h+2) x)) = u h := by
        funext x
        cases u h x <;> cases u (h+1) x <;> cases u (h+2) x <;> rfl
      exact z ▸ hg
    obtain ⟨b,en,all⟩ := ih v (fun i hi => pre.old (hr i (by omega))) hu (pre.old h₀)
    refine ⟨b, by simpa [Nat.add_comm] using pre.trans en, ?_⟩
    intro i hi
    by_cases hit : i < h+2
    · exact all i hit
    · have : i = h+2 := by omega
      subst i
      exact en.old (pre.old h₁)

lemma emitFunction {ι : Type} [Fintype ι] (a : List (Sig X)) (bits : ι → Sig X)
    (hb : ∀ i, bits i ∈ a) (q : (ι → Bool) → Bool) :
    ∃ b, Ext a b (tableCost (Fintype.card ι)) ∧ (fun x => q (fun i => bits i x)) ∈ b := by
  classical
  let e := Fintype.equivFin ι
  obtain ⟨b,he,hq⟩ := emitTable a (fun j => bits (e.symm j)) (fun j => hb _)
    (fun ys => q (fun i => ys (e i)))
  exact ⟨b,he,by simpa only [Equiv.symm_apply_apply] using hq⟩

lemma blocks {ι ο : Type} (indices : List ι) (unitCost : Nat) (a : List (Sig X))
    (wanted : ι → ο → Sig X)
    (one : ∀ w, (∀ f ∈ a, f ∈ w) → ∀ i ∈ indices,
      ∃ b, Ext w b unitCost ∧ ∀ o, wanted i o ∈ b) :
    ∃ b, Ext a b (indices.length*unitCost) ∧ ∀ i ∈ indices, ∀ o, wanted i o ∈ b := by
  induction indices generalizing a with
  | nil => exact ⟨a, by simpa using Ext.refl a, by simp⟩
  | cons i is ih =>
    obtain ⟨w,e,hw⟩ := one a (fun _ h => h) i (by simp)
    obtain ⟨b,f,hb⟩ := ih w (fun t ht j hj => one t (fun z hz => ht z (e.old hz)) j (by simp [hj]))
    refine ⟨b, ?_, ?_⟩
    · simpa [Nat.succ_mul, Nat.add_comm] using e.trans f
    · intro j hj o
      rcases List.mem_cons.mp hj with rfl | hj
      · exact f.old (hw o)
      · exact hb _ hj o

end PEqualNP.Outside.L_meta_40374.Build

namespace PEqualNP.Outside.L_meta_40374.Pair
open Build
variable {X : Type}
abbrev Slots := Fin 5 ⊕ Fin 4

def cut {m : Nat} (f : Fin m → Bool) := pack m (fun j => if hj : j < m then f ⟨j,hj⟩ else false)

lemma cutEval (m : Nat) (f : Nat → Bool) : cut (fun j : Fin m => f j.val) = pack m f :=
  packCongr (fun i hi => by simp [hi])

def taps (h : Nat) (u : Bool → X → Nat) : Slots → Sig X :=
  Sum.elim (fun i x => chi (u false x).testBit (h-5+i.val))
           (fun i x => chi (u true x).testBit (h-4+i.val))

def choice (data : Slots → Bool) := select (cut fun i => data (.inl i)) (cut fun i => data (.inr i))

def key (h k start : Nat) (u : Bool → X → Nat) (x : X) :=
  globalKey k (start+h+k-9) (raw (choice (fun j => taps h u j x)))

lemma choiceActual (h : Nat) (u : Bool → X → Nat) (x : X) :
    choice (fun j => taps h u j x) = select (tailReply 5 h (u false x)) (tailReply 4 h (u true x)) := by
  unfold choice
  change select (cut (fun j : Fin 5 => chi (u false x).testBit (h-5+j.val)))
    (cut (fun j : Fin 4 => chi (u true x).testBit (h-4+j.val))) = _
  rw [cutEval 5 (fun j => chi (u false x).testBit (h-5+j)), cutEval 4 (fun j => chi (u true x).testBit (h-4+j))]
  rfl

def preCost := Fintype.card (Fin 3 → Bool) * tableCost (Fintype.card Slots)
def decCost := Fintype.card (Bool × Bool) * tableCost (Fintype.card (Bool × Slots))

lemma makeKey (a : List (Sig X)) (h k start : Nat) (u : Bool → X → Nat)
    (ht : ∀ j, taps h u j ∈ a) :
    ∃ b, Ext a b preCost ∧ ∀ i : Fin k, (fun x => (key h k start u x).testBit i.val) ∈ b := by
  classical
  let value := fun (pat : Fin 3 → Bool) x => pat (choice (fun j => taps h u j x))
  obtain ⟨b,hb,mem⟩ := emitMany (Finset.univ : Finset (Fin 3 → Bool)).toList (tableCost (Fintype.card Slots)) a value
    (fun w hw pat _ => emitFunction w (taps h u) (fun j => hw _ (ht j)) (fun ds => pat (choice ds)))
  exact ⟨b, by simpa [preCost] using hb, fun i => mem (fun p => (globalKey k (start+h+k-9) (raw p)).testBit i.val) (by simp)⟩

def obs (h k start : Nat) (u : Bool → X → Nat) (b : Bool) (len : Nat) (i : Fin len) (x : X) :=
  chi (fun j => xor ((u b x).testBit j) (shift k start b (key h k start u x) j)) (h-len+i.val)

def sensors (h k start : Nat) (u : Bool → X → Nat) : Slots → Sig X :=
  Sum.elim (obs h k start u false 5) (obs h k start u true 4)

def measured (h k start : Nat) (u : Bool → X → Nat) (p : Bool × Slots) : Sig X :=
  if p.1 then sensors h k start u p.2 else taps h u p.2

def terminal (b : Bool × Bool) (ds : Bool × Slots → Bool) : Bool :=
  let orig := fun j => ds (false,j)
  let i := choice orig
  if b.1 then
    (decode 4 (cut fun j => orig (.inr j)) (cut fun j => ds (true,.inr j)) (colPulse i)).testBit (4+b.2.toNat)
  else
    (decode 5 (cut fun j => orig (.inl j)) (cut fun j => ds (true,.inl j)) (rowPulse i)).testBit (5+b.2.toNat)

lemma terminalActual (h k start : Nat) (hh : 5 ≤ h) (hk : h+6 ≤ k) (u : Bool → X → Nat)
    (b : Bool × Bool) (x : X) :
    terminal b (fun p => measured h k start u p x) = (u b.1 x).testBit (h+b.2.toNat) := by
  let ky := key h k start u x
  have he : ky = globalKey k (start+h+k-9) (raw (select (tailReply 5 h (u false x)) (tailReply 4 h (u true x)))) := by
    simp only [ky, key, choiceActual]
  have hr := fullSuffixRecovery start (u false x) (u true x) hh hk
  dsimp only at hr
  rw [← he] at hr
  have input5 : cut (fun j : Fin 5 => measured h k start u (false,.inl j) x) = tailReply 5 h (u false x) :=
    cutEval 5 (fun j => chi (u false x).testBit (h-5+j))
  have input4 : cut (fun j : Fin 4 => measured h k start u (false,.inr j) x) = tailReply 4 h (u true x) :=
    cutEval 4 (fun j => chi (u true x).testBit (h-4+j))
  have samp5 : cut (fun j : Fin 5 => measured h k start u (true,.inl j) x) = tailObservation 5 h k start false ky (u false x) :=
    cutEval 5 (fun j => chi (fun l => xor ((u false x).testBit l) (shift k start false ky l)) (h-5+j))
  have samp4 : cut (fun j : Fin 4 => measured h k start u (true,.inr j) x) = tailObservation 4 h k start true ky (u true x) :=
    cutEval 4 (fun j => chi (fun l => xor ((u true x).testBit l) (shift k start true ky l)) (h-4+j))
  obtain ⟨c,t⟩ := b
  have ht : t.toNat ≤ 1 := by cases t <;> decide
  have i := choiceActual h u x
  have adjusted (d : Nat) (hd : d ≤ h) : h-d+(d+t.toNat) = h+t.toNat := by omega
  cases c
  · change (decode 5 _ _ _).testBit (5+t.toNat) = _
    rw [input5, samp5, show choice (fun j => measured h k start u (false,j) x) = _ from i, hr.2.1,
      suffixBit (by omega), adjusted 5 hh]
  · change (decode 4 _ _ _).testBit (4+t.toNat) = _
    rw [input4, samp4, show choice (fun j => measured h k start u (false,j) x) = _ from i, hr.2.2,
      suffixBit (by omega), adjusted 4 (by omega)]

lemma makePair (a : List (Sig X)) (h k start : Nat) (hh : 5 ≤ h) (hk : h+6 ≤ k)
    (u : Bool → X → Nat)
    (hy : ∀ c i, i < h → (fun x => chi (u c x).testBit i) ∈ a)
    (ht : ∀ p, measured h k start u p ∈ a) :
    ∃ b, Ext a b (2*h+decCost) ∧ ∀ c (i : Fin (h+2)), (fun x => (u c x).testBit i.val) ∈ b := by
  classical
  let tail := fun (p : Bool × Bool) (x : X) => (u p.1 x).testBit (h+p.2.toNat)
  obtain ⟨w,ew,hw⟩ := emitMany (Finset.univ : Finset (Bool × Bool)).toList (tableCost (Fintype.card (Bool × Slots))) a tail
    (fun t old p _ => by
      obtain ⟨w, e, m⟩ := emitFunction t (measured h k start u) (fun i => old _ (ht i)) (terminal p)
      have he : (fun x => terminal p (fun j => measured h k start u j x)) = tail p := funext (terminalActual h k start hh hk u p)
      rw [he] at m
      exact ⟨w,e,m⟩)
  have tails (c b : Bool) := hw (c,b) (by simp)
  have step (v : List (Sig X)) (c : Bool) (extend : ∀ f ∈ w, f ∈ v) :
      ∃ z, Ext v z h ∧ ∀ i < h+2, (fun x => (u c x).testBit i) ∈ z := by
    apply strip h v (fun i x => (u c x).testBit i)
    · exact fun i hi => extend _ (ew.old (hy c i hi))
    · exact extend _ (tails c false)
    · exact extend _ (tails c true)
  obtain ⟨v,ev,hv⟩ := step w false (fun _ hf => hf)
  obtain ⟨b,eb,hb⟩ := step v true (fun _ hf => ev.old hf)
  refine ⟨b, ?_, ?_⟩
  · apply ((ew.trans ev).trans eb).mono
    simp [decCost]; omega
  · intro c i; cases c
    · exact eb.old (hv i.val i.isLt)
    · exact hb i.val i.isLt

end PEqualNP.Outside.L_meta_40374.Pair

namespace PEqualNP.Outside.L_meta_40374.Upper
open PEqualNP.CircuitLowerBounds
open Build

abbrev U (h n : Nat) := Fin n → Fin (2^(h+2))
abbrev World (h n : Nat) := U h n × U h n

def val {h n : Nat} (j : Fin n) (c : Bool) (s : World h n) : Nat :=
  (if c then s.2 j else s.1 j).val

def yRow {h n : Nat} (j : Fin n) (c : Bool) := List.ofFn (fun i : Fin h =>
  fun s : World h n => chi (val j c s).testBit i)

def ys (h n : Nat) := (List.ofFn (fun j : Fin n => yRow (h:=h) j false ++ yRow j true)).flatten

def ky (h k start : Nat) {n : Nat} (j : Fin n) := Pair.key h k start (val (h:=h) j)

def rowObs (h k start : Nat) {n : Nat} (j : Fin n) (c : Bool) (len : Nat) :=
  List.ofFn (Pair.obs h k start (val (h:=h) j) c len)

def data (h k start n : Nat) :=
  (List.ofFn (fun j : Fin n =>
    List.ofFn (fun i : Fin k => fun s : World h n => (ky h k start j s).testBit i.val) ++
    rowObs h k start j false 5 ++ rowObs h k start j true 4)).flatten

def decoderInput (h k start n : Nat) := ys h n ++ data h k start n

lemma member {α : Type} {n : Nat} (f : Fin n → List α) (j : Fin n) {v : α} (h : v ∈ f j) :
    v ∈ (List.ofFn f).flatten := List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨j,rfl⟩,h⟩

lemma len {α : Type} {n m : Nat} (f : Fin n → List α) (hl : ∀ j, (f j).length = m) :
    (List.ofFn f).flatten.length = n*m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, hl, ih _ (fun j => hl j.succ), Nat.succ_mul]
    omega

lemma ysLen (h n : Nat) : (ys h n).length = 2*n*h := by
  calc _ = n*(h+h) := len _ (by simp [yRow])
       _ = _ := by ring

lemma dinLen (h k start n : Nat) : (decoderInput h k start n).length = 2*n*h+n*(k+9) := by
  rw [decoderInput,List.length_append,ysLen]
  congr 1
  exact len _ (by simp [rowObs])

lemma yMem {h n : Nat} (j : Fin n) (c : Bool) {i : Nat} (hi : i < h) :
    (fun s : World h n => chi (val j c s).testBit i) ∈ ys h n := by
  apply member _ j
  have mem : (fun s : World h n => chi (val j c s).testBit i) ∈ yRow j c :=
    List.mem_ofFn.mpr ⟨⟨i,hi⟩,rfl⟩
  cases c
  · exact List.mem_append_left _ mem
  · exact List.mem_append_right _ mem

lemma tailMem {h n : Nat} (hh : 5 ≤ h) (j : Fin n) (t : Pair.Slots) :
    Pair.taps h (val j) t ∈ ys h n := by
  cases t with
  | inl i => exact yMem j false (by have := i.isLt; omega)
  | inr i => exact yMem j true (by have := i.isLt; omega)

lemma sensorMem {h k start n : Nat} (j : Fin n) (t : Pair.Slots) :
    Pair.sensors h k start (val j) t ∈ data h k start n := by
  apply member _ j
  cases t with
  | inl i => exact List.mem_append_left _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
  | inr i => exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

lemma measuredMem {h k start n : Nat} (hh : 5 ≤ h) (j : Fin n) (t : Bool × Pair.Slots) :
    Pair.measured h k start (val j) t ∈ decoderInput h k start n := by
  obtain ⟨b,t⟩ := t
  cases b
  · exact List.mem_append_left _ (tailMem hh j t)
  · exact List.mem_append_right _ (sensorMem j t)

lemma preProgram (h k start n : Nat) (hh : 5 ≤ h) :
    ∃ b, Ext (ys h n) b (n*Pair.preCost) ∧
      ∀ j : Fin n, ∀ i : Fin k, (fun s : World h n => (ky h k start j s).testBit i.val) ∈ b := by
  classical
  let v := fun (j : Fin n) (i : Fin k) (s : World h n) => (ky h k start j s).testBit i.val
  obtain ⟨b,he,hb⟩ := blocks (List.finRange n) Pair.preCost (ys h n) v
    (fun w hw j _ => Pair.makeKey w h k start (val j) (fun t => hw _ (tailMem hh j t)))
  exact ⟨b,by simpa using he,fun j => hb _ (by simp)⟩

lemma decProgram (h k start n : Nat) (hh : 5 ≤ h) (hk : h+6 ≤ k) :
    ∃ b, Ext (decoderInput h k start n) b (n*(2*h+Pair.decCost)) ∧
      ∀ (j : Fin n) (c : Bool) (i : Fin (h+2)), (fun s : World h n => (val j c s).testBit i.val) ∈ b := by
  let v := fun (j : Fin n) (p : Bool × Fin (h+2)) (s : World h n) => (val j p.1 s).testBit p.2.val
  obtain ⟨b,he,hb⟩ := blocks (List.finRange n) (2*h+Pair.decCost) (decoderInput h k start n) v
    (fun w hw j _ => by
      obtain ⟨b,e,hb⟩ := Pair.makePair w h k start hh hk (val j)
        (fun c i hi => hw _ (List.mem_append_left _ (yMem j c hi)))
        (fun t => hw _ (measuredMem hh j t))
      exact ⟨b,e,fun p => hb p.1 p.2⟩)
  exact ⟨b,by simpa using he,fun j c i => hb j (by simp) (c,i)⟩

lemma encodedFits {k : Nat} (f : Fin k → Bool) : encoded f < 2^k := by
  induction k with
  | zero => simp [encoded]
  | succ k ih =>
    rw [encodedStep, Nat.bit_val, pow_succ]
    have h := ih (fun i => f i.succ)
    cases f 0 <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

lemma encodedId {k x : Nat} (hx : x < 2^k) : encoded (fun i : Fin k => x.testBit i.val) = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · exact encodedTap _ ⟨i,hi⟩
  · have powle : 2^k ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow ((encodedFits _).trans_le powle), Nat.testBit_lt_two_pow (hx.trans_le powle)]

def original {h n} (s : World h n) : List Bool :=
  (List.ofFn (fun j : Fin n =>
    List.ofFn (fun i : Fin h => chi (val j false s).testBit i) ++
    List.ofFn (fun i : Fin h => chi (val j true s).testBit i))).flatten

def plugged (k start : Nat) {h n : Nat} (s : World h n) (chosen : Fin n → Nat) : List Bool :=
  let obs (j : Fin n) (b : Bool) (m : Nat) := List.ofFn (fun i : Fin m =>
    chi (fun l => xor ((val j b s).testBit l) (shift k start b (chosen j) l)) (h-m+i.val))
  (List.ofFn (fun j : Fin n => List.ofFn (fun i : Fin k => (chosen j).testBit i.val) ++
    obs j false 5 ++ obs j true 4)).flatten

lemma yPhysical {h n} (s : World h n) :
    (ys h n).map (fun f => f s) = original s := by
  simp only [ys, original, yRow, List.map_flatten, List.map_ofFn, Function.comp_def, List.map_append]

lemma dPhysical {h n} (k start : Nat) (s : World h n) :
    (decoderInput h k start n).map (fun f => f s) =
    original s ++ plugged k start s (fun j => ky h k start j s) := by
  simp only [decoderInput, List.map_append, yPhysical, data, plugged, rowObs, Pair.obs,
    ky, List.map_flatten, List.map_ofFn, Function.comp_def, List.map_append]

lemma physicalTap {X : Type} (gs : List Gate) (a : List (Sig X)) (i : Nat) (x : X) :
    Cost.tap (Cost.run gs a) i x = ((⟨gs,0⟩ : Circuit).wires (a.map (fun f => f x))).getD i false := by
  calc _ = ((Cost.run gs a).map (fun f => f x)).getD i false :=
             (List.getD_map _ (fun _ => false) (fun f => f x)).symm
       _ = _ := congrArg (fun l : List Bool => l.getD i false) (Cost.runSpec gs a x)

lemma kyFits (h k start : Nat) {n : Nat} (j : Fin n) (s : World h n) : ky h k start j s < 2^k := by
  unfold ky Pair.key globalKey
  exact wordFits _ _

set_option maxHeartbeats 1200000 in
lemma postedSufficiency (h k start n p d : Nat) (hh : 5 ≤ h) (hk : h+6 ≤ k) (rate : 2*d ≤ p) :
    feasible h k start n p d (d*(Pair.preCost+Pair.decCost)) := by
  classical
  obtain ⟨bp,⟨gp,lp,cp,rfl⟩,hp⟩ := preProgram h k start n hh
  obtain ⟨bd,⟨gd,ld,cd,rfl⟩,hd⟩ := decProgram h k start n hh hk
  choose kt ktBound ktSig using fun j i => fetch (hp j i)
  choose out outBound outSig using fun j c i => fetch (hd j c i)
  let P : Circuit := ⟨gp,0⟩
  let D : Circuit := ⟨gd,0⟩
  refine ⟨globalMenu k (start+h+k-9),P,D,kt,out,menuSubset _ _,menuCard (by omega),?_,?_,?_,?_,?_,?_⟩
  · simpa only [valid, P, ysLen] using legalValid lp
  · simpa only [valid, D, dinLen] using legalValid ld
  · intro j i; simpa only [lengthRun, ysLen] using ktBound j i
  · intro j c i; simpa only [lengthRun, dinLen] using outBound j c i
  · calc d*(gp.countP Cost.nonlinear+gd.countP Cost.nonlinear)
          ≤ d*(n*Pair.preCost+n*(2*h+Pair.decCost)) := Nat.mul_le_mul_left _ (Nat.add_le_add cp cd)
         _ = n*((2*d)*h+d*(Pair.preCost+Pair.decCost)) := by ring
         _ ≤ _ := Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_right _ rate) _)
  · intro r c
    let s : World h n := (r,c)
    let chosen := fun j : Fin n => encoded (fun i : Fin k =>
      (P.wires (original s)).getD (kt j i) false)
    change (∀ j, chosen j ∈ globalMenu k (start+h+k-9)) ∧ ∀ j col i,
      (D.wires (original s ++ plugged k start s chosen)).getD (out j col i) false = (val j col s).testBit i.val
    have keyEq : chosen = fun j => ky h k start j s := by
      funext j
      calc chosen j = encoded (fun i : Fin k => (ky h k start j s).testBit i.val) := by
             apply congrArg encoded
             funext i
             have he := congrFun (ktSig j i) s
             rw [physicalTap, yPhysical] at he
             exact he
           _ = _ := encodedId (kyFits h k start j s)
    rw [keyEq]
    constructor
    · intro j
      exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
    · intro j col i
      have he := congrFun (outSig j col i) s
      rw [physicalTap, dPhysical] at he
      exact he

end PEqualNP.Outside.L_meta_40374.Upper

theorem PEqualNP.Outside.L_meta_40374 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
        (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
let valid := fun (w : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.NestedCover.ReadsBack w C ∧
  ∀ g ∈ C.gates, g.inputs.length ≤ 2
let chi := fun (u : Nat → Bool) (i : Nat) => xor (u i) (!(u (i+1)) && u (i+2))
let feasible := fun (h k start n p d K : Nat) =>
  let U := Fin n → Fin (2^(h+2))
  let w := 2*n*h
  let W := w+n*(k+9)
  let shift := fun (col : Bool) (x j : Nat) =>
    let bit := fun back : Nat => x.testBit ((start+j+k-back) % k)
    if col then xor (bit 1) (xor (bit 3) (bit 5))
    else xor (bit 0) (xor (bit 1) (bit 2))
  let observe := fun (col : Bool) (x u len : Nat) =>
    List.ofFn (fun i : Fin len =>
      chi (fun l => xor (u.testBit l) (shift col x l)) (h-len+i.val))
  ∃ (menu : Finset Nat) (P D : PEqualNP.CircuitLowerBounds.Circuit)
    (keyTap : Fin n → Fin k → Nat) (out : Fin n → Bool → Fin (h+2) → Nat),
    menu ⊆ Finset.range (2^k) ∧ menu.card = 3 ∧ valid w P ∧ valid W D ∧
    (∀ j i, keyTap j i < w+P.gates.length) ∧
    (∀ j col i, out j col i < W+D.gates.length) ∧
    d*(P.gates.countP nonlinear+D.gates.countP nonlinear) ≤ n*(p*h+K) ∧
    ∀ (r c : U),
      let reply := fun (u : Nat) => List.ofFn (fun i : Fin h => chi (fun l => u.testBit l) i)
      let y := (List.ofFn (fun j : Fin n => reply (r j).val ++ reply (c j).val)).flatten
      let pre := P.wires y
      let chosen := fun j : Fin n =>
        ∑ i : Fin k, if pre.getD (keyTap j i) false then 2^i.val else 0
      (∀ j, chosen j ∈ menu) ∧
      let data := (List.ofFn (fun j : Fin n =>
        List.ofFn (fun i : Fin k => (chosen j).testBit i) ++
        observe false (chosen j) (r j).val 5 ++ observe true (chosen j) (c j).val 4)).flatten
      let wires := D.wires (y ++ data)
      ∀ j col i, wires.getD (out j col i) false = (if col then c j else r j).val.testBit i
∀ (p d : Nat), 0 < d →
  ((∃ K : Nat, ∀ (h k start n : Nat), 5 ≤ h → h+6 ≤ k → feasible h k start n p d K) ↔
  2*d ≤ p)) := by
  change ∀ p d : Nat, 0 < d →
    ((∃ K, ∀ h k start n, 5 ≤ h → h+6 ≤ k → PEqualNP.Outside.L_meta_40374.feasible h k start n p d K) ↔ 2*d ≤ p)
  intro p d _
  constructor
  · rintro ⟨K,h⟩
    exact PEqualNP.Outside.L_meta_40374.postedNecessity h
  · intro rate
    exact ⟨d*(PEqualNP.Outside.L_meta_40374.Pair.preCost+PEqualNP.Outside.L_meta_40374.Pair.decCost),
      fun h k start n hh hk => PEqualNP.Outside.L_meta_40374.Upper.postedSufficiency h k start n p d hh hk rate⟩
