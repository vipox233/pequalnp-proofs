import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25502_aux.Builder
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

abbrev BitFn (n : Nat) := (Fin n → Bool) → Bool

structure Bank (n : Nat) where
  gates : List Gate
  fan : FanInTwo ⟨gates,0⟩
  back : ReadsBack n ⟨gates,0⟩

namespace Bank
variable {n : Nat}

def val (B : Bank n) (i : Nat) (x : Fin n → Bool) : Bool :=
  ((⟨B.gates,0⟩ : Circuit).wires (List.ofFn x)).getD i false

def Has (B : Bank n) (f : BitFn n) : Prop :=
  ∃ i < n + B.gates.length, ∀ x, B.val i x = f x

def Ext (B D : Bank n) : Prop := ∀ {f}, B.Has f → D.Has f

def Grow (B : Bank n) (cost : Nat) (p : Bank n → Prop) : Prop :=
  ∃ D, B.Ext D ∧ D.gates.length ≤ B.gates.length + cost ∧ p D

def empty (n : Nat) : Bank n := ⟨[],by simp [FanInTwo],by simp [ReadsBack]⟩

lemma input (i : Fin n) : (empty n).Has (fun x => x i) := by
  refine ⟨i,i.isLt,?_⟩
  intro x
  simp [val,empty,Circuit.wires,List.getD_eq_getElem?_getD,i.isLt]

lemma Grow.pure (B : Bank n) {p : Bank n → Prop} (h : p B) : B.Grow 0 p :=
  ⟨B,fun h => h,by omega,h⟩

lemma Grow.weaken {B : Bank n} {p q : Bank n → Prop} {a b : Nat} (h : B.Grow a p)
    (hab : a ≤ b) (hpq : ∀ D, p D → q D) : B.Grow b q := by
  obtain ⟨D,e,c,t⟩ := h
  exact ⟨D,e,by omega,hpq D t⟩

lemma Grow.bind {B : Bank n} {p q : Bank n → Prop} {a b : Nat} (h : B.Grow a p)
    (f : ∀ D, B.Ext D → p D → D.Grow b q) : B.Grow (a+b) q := by
  obtain ⟨D,e,c,t⟩ := h
  obtain ⟨E,e',c',t'⟩ := f D e t
  exact ⟨E,fun h => e' (e h),by omega,t'⟩

private lemma wireLen (gs : List Gate) (x : List Bool) :
    ((⟨gs,0⟩ : Circuit).wires x).length = x.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp [Circuit.wires,List.foldl_append] at ih ⊢
    omega

private lemma gate (B : Bank n) (g : Gate)
    (ok : g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (back : ∀ i ∈ g.inputs, i < n+B.gates.length) :
    B.Grow 1 (fun D => D.Has (fun x => g.op.eval (g.inputs.map fun i => B.val i x))) := by
  let D : Bank n :=
    { gates := B.gates ++ [g]
      fan := by
        intro g' h
        change g' ∈ B.gates ++ [g] at h
        rcases List.mem_append.mp h with h|h
        · exact B.fan g' h
        · simpa using (show g' = g from List.mem_singleton.mp h) ▸ ok
      back := by
        intro j hj w hw
        change j < (B.gates ++ [g]).length at hj
        change w ∈ ((B.gates ++ [g]).getD j _).inputs at hw
        by_cases h : j < B.gates.length
        · rw [List.getD_append _ _ _ _ h] at hw
          exact B.back j h w hw
        · have he : j = B.gates.length := by simp at hj; omega
          subst j
          simp at hw
          exact back w hw }
  have hv (x : Fin n → Bool) :
      ((⟨D.gates,0⟩ : Circuit).wires (List.ofFn x)) =
        ((⟨B.gates,0⟩ : Circuit).wires (List.ofFn x)) ++
        [g.op.eval (g.inputs.map fun i => B.val i x)] := by
    simp [D,val,Circuit.wires,List.foldl_append]
  have hl (x : Fin n → Bool) :
      ((⟨B.gates,0⟩ : Circuit).wires (List.ofFn x)).length = n+B.gates.length := by
    simp [wireLen]
  refine ⟨D,?_,by simp [D],n+B.gates.length,by simp [D],?_⟩
  · intro f hf
    obtain ⟨i,hi,he⟩ := hf
    refine ⟨i,by simp [D]; omega,?_⟩
    intro x
    unfold val
    rw [hv,List.getD_append _ _ _ _ (by rw [hl]; exact hi)]
    exact he x
  · intro x
    unfold val
    rw [hv,← hl x]
    simp [val,List.getD_eq_getElem?_getD]

lemma const (B : Bank n) (b : Bool) : B.Grow 1 (fun D => D.Has (fun _ => b)) := by
  cases b with
  | false => simpa [GateOp.eval] using B.gate ⟨.or,[]⟩ (by simp) (by simp)
  | true => simpa [GateOp.eval] using B.gate ⟨.and,[]⟩ (by simp) (by simp)

lemma inv {B : Bank n} {f : BitFn n} (a : B.Has f) :
    B.Grow 1 (fun D => D.Has (fun x => !(f x))) := by
  obtain ⟨i,hi,he⟩ := a
  simpa [GateOp.eval,he] using B.gate ⟨.not,[i]⟩ (by simp) (by simpa using hi)

lemma meet {B : Bank n} {f g : BitFn n} (a : B.Has f) (b : B.Has g) :
    B.Grow 1 (fun D => D.Has (fun x => f x && g x)) := by
  obtain ⟨i,hi,he⟩ := a
  obtain ⟨j,hj,hf⟩ := b
  simpa [GateOp.eval,he,hf] using B.gate ⟨.and,[i,j]⟩ (by simp) (by simp [hi,hj])

lemma join {B : Bank n} {f g : BitFn n} (a : B.Has f) (b : B.Has g) :
    B.Grow 1 (fun D => D.Has (fun x => f x || g x)) := by
  obtain ⟨i,hi,he⟩ := a
  obtain ⟨j,hj,hf⟩ := b
  simpa [GateOp.eval,he,hf] using B.gate ⟨.or,[i,j]⟩ (by simp) (by simp [hi,hj])

lemma xor2 {B : Bank n} {f g : BitFn n} (a : B.Has f) (b : B.Has g) :
    B.Grow 4 (fun D => D.Has (fun x => xor (f x) (g x))) := by
  apply (meet a b).bind (b := 3)
  intro C e hab
  apply (inv hab).bind (b := 2)
  intro D e' hn
  apply (join (e' (e a)) (e' (e b))).bind (b := 1)
  intro E e'' hor
  apply (meet hor (e'' hn)).weaken (le_refl _)
  intro F h
  have eq (x) : ((f x || g x) && !(f x && g x)) = xor (f x) (g x) := by
    cases f x <;> cases g x <;> decide
  simpa only [eq] using h

lemma collect {α : Type} (B : Bank n) (l : List α) (f : α → BitFn n) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i ∈ l, D.Grow cost (fun E => E.Has (f i))) :
    B.Grow (l.length*cost) (fun D => ∀ i ∈ l, D.Has (f i)) := by
  induction l with
  | nil => simpa using (Grow.pure B (p:=fun D => ∀ i ∈ ([] : List α), D.Has (f i)) (by simp))
  | cons a l ih =>
    have t := ih (fun D e i hi => emit D e i (by simp [hi]))
    have out := t.bind (b:=cost) (q:=fun E => ∀ i ∈ a::l, E.Has (f i)) (by
      intro D e haveL
      obtain ⟨E,e',c',ha⟩ := emit D e a (by simp)
      refine ⟨E,e',c',?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | h
      · exact ha
      · exact e' (haveL i h))
    simpa [Nat.succ_mul] using out

lemma collectFin (B : Bank n) (m : Nat) (f : Fin m → BitFn n) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i, D.Grow cost (fun E => E.Has (f i))) :
    B.Grow (m*cost) (fun D => ∀ i, D.Has (f i)) := by
  simpa using B.collect (List.finRange m) f cost (fun D e i _ => emit D e i)

lemma finish {f : BitFn n} {b : Nat} (h : (empty n).Grow b (fun B => B.Has f)) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack n C ∧ C.size ≤ b ∧
      ∀ bits, C.eval (List.ofFn bits) = f bits := by
  obtain ⟨B,_,budget,i,_,he⟩ := h
  exact ⟨⟨B.gates,i⟩, B.fan, B.back, by simpa [Circuit.size, empty] using budget, he⟩

end Bank
end PEqualNP.Outside.L_meta_25502_aux.Builder

namespace PEqualNP.Outside.L_meta_25502_aux.Builder.Bank

variable {n : Nat}

lemma xorConst {B : Bank n} {f : BitFn n} (a : B.Has f) (b : Bool) :
    B.Grow 1 (fun D => D.Has (fun x => xor (f x) b)) := by
  cases b with
  | false =>
    have h := Grow.pure B (p:=fun D => D.Has f) a
    simpa using h.weaken (b:=1) (q:=fun D => D.Has f) (by decide) (fun _ t => t)
  | true => simpa using inv a

end PEqualNP.Outside.L_meta_25502_aux.Builder.Bank

namespace PEqualNP.Outside.L_meta_25502_aux
def chi (a b c : Bool) := xor a (!b && c)
def rot (k s w : Nat) := ((w <<< (s%k)) ||| (w >>> (k-s%k))) % 2^k
def flipAt (f : Nat → Bool) (i : Nat) := (f i).toNat <<< i
lemma flipBit (f : Nat → Bool) (i j : Nat) :
    (flipAt f i).testBit j = (if j=i then f i else false) := by
  unfold flipAt; rw [Nat.testBit_shiftLeft,Nat.testBit_bool_toNat]
  rcases lt_trichotomy j i with hl|he|hg
  · simp [Nat.not_le.mpr hl,Nat.ne_of_lt hl]
  · simp [he]
  · simp [Nat.le_of_lt hg,show j-i≠0 by omega,Nat.ne_of_gt hg]
lemma packBit (f : Nat → Bool) (l : List Nat) (acc j : Nat) :
  (l.foldl (fun z i => z ||| flipAt f i) acc).testBit j =
    (acc.testBit j || (decide (j∈l) && f j)) := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons,ih,Nat.testBit_or,flipBit]
    by_cases h : j=x
    · subst x; cases e : f j <;> simp [e,Bool.or_assoc]
    · simp [h]
def rawStep (k w : Nat) := (List.range k).foldl (fun z i =>
    z ||| flipAt (fun j => chi (w.testBit j) (w.testBit ((j+1)%k)) (w.testBit ((j+2)%k))) i) 0
lemma stepBit {k j} (h : j<k) (w : Nat) :
    (rawStep k w).testBit j = chi (w.testBit j) (w.testBit ((j+1)%k)) (w.testBit ((j+2)%k)) := by
  simp [rawStep,packBit,h]
lemma rotBit {k j s w : Nat} (h : j<k) (hs : s<k) (hw : w<2^k) :
    (rot k s w).testBit j = w.testBit (if j<s then k-s+j else j-s) := by
  simp only [rot,Nat.mod_eq_of_lt hs,Nat.testBit_mod_two_pow,h,decide_true,Bool.true_and,
    Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftRight]
  by_cases hj : j<s
  · simp [hj,Nat.not_le.mpr hj]
  · have big : w.testBit (k-s+j) = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hj,Nat.le_of_not_gt hj,big]
end PEqualNP.Outside.L_meta_25502_aux

namespace PEqualNP.Outside.L_meta_25502_aux
def idx (k : Nat) (j : Int) := (j % (k : Int)).toNat
def bits (k w : Nat) (j : Int) := w.testBit (idx k j)
lemma idxlt {k : Nat} (kp : 0 < k) (j : Int) : idx k j < k := by
  have h := Int.emod_lt_of_pos j (show (0:Int)<k by omega)
  unfold idx;omega
lemma idxSub {k s : Nat} (hs : s<k) (j : Int) :
    idx k (j-(s:Int)) = if idx k j<s then k-s+idx k j else idx k j-s := by
  have hp : (0:Int)<k := by omega
  have a := Int.emod_nonneg j (ne_of_gt hp)
  have b := Int.emod_lt_of_pos j hp
  unfold idx; rw [← Int.emod_sub_emod j (k:Int) (s:Int)]; split
  · next h =>
    rw [←Int.add_emod_left,Int.emod_eq_of_lt (by omega) (by omega)];omega
  · next h => rw [Int.emod_eq_of_lt (by omega) (by omega)];omega
lemma bitsRot {k s w : Nat} (hs : s<k) (hw : w<2^k) (j : Int) :
    bits k (rot k s w) j = bits k w (j-(s:Int)) := by
  unfold bits;rw [rotBit (idxlt (by omega) _) hs hw,idxSub hs]
lemma idxAdd {k : Nat} (kp : 0<k) (j : Int) (s : Nat) :
    (idx k j+s)%k = idx k (j+(s:Int)) := by
  have a := Int.emod_nonneg j (show (k:Int)≠0 by omega)
  unfold idx
  rw [←Int.emod_add_emod j (k:Int) (s:Int)]
  have eq : (j%(k:Int)+(s:Int)).toNat = (j%(k:Int)).toNat + s := by omega
  rw [@Int.toNat_emod (j%(k:Int)+(s:Int)) (k:Int) (by omega) (by omega),eq]
  rfl
lemma bitsStep {k : Nat} (kp : 0<k) (w : Nat) (j : Int) :
    bits k (rawStep k w) j = chi (bits k w j) (bits k w (j+1)) (bits k w (j+2)) := by
  unfold bits; rw [stepBit (idxlt kp _), idxAdd kp j 1,idxAdd kp j 2]; rfl
lemma bitsXor (k a b : Nat) (j : Int) : bits k (a ^^^ b) j = xor (bits k a j) (bits k b j) := Nat.testBit_xor ..
lemma stepBound (k w : Nat) : rawStep k w < 2^k := by
  have e : rawStep k w % 2^k = rawStep k w := by
    apply Nat.eq_of_testBit_eq; intro i
    by_cases h : i<k
    · simp [Nat.testBit_mod_two_pow,h]
    · simp [Nat.testBit_mod_two_pow,rawStep,packBit,h]
  rw [←e];exact Nat.mod_lt _ (by positivity)
def rInit (k w v : Nat) := rot k 3 w ^^^ v
end PEqualNP.Outside.L_meta_25502_aux

namespace PEqualNP.Outside.L_meta_25502_aux
namespace Eval
open Builder Builder.Bank
variable {n k : Nat}

abbrev Word (n : Nat) := (Fin n → Bool) → Nat
def HasWord (k : Nat) (B : Bank n) (W : Word n) : Prop :=
  ∀ j : Int, B.Has (fun x => bits k (W x) j)

lemma idxNat {i : Nat} (h : i<k) : idx k (i : Int) = i := by
  unfold idx
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  rfl

lemma wordLift {B D : Bank n} {W : Word n} (ext : B.Ext D) (h : HasWord k B W) :
    HasWord k D W := fun j => ext (h j)

lemma fromFin {B : Bank n} {W : Word n} (hk : 0<k)
    (h : ∀ i : Fin k, B.Has (fun x => (W x).testBit i.val)) : HasWord k B W :=
  fun j => h ⟨idx k j,idxlt hk j⟩

lemma wordBuild {B : Bank n} {W : Word n} (hk : 0<k) (c : Nat)
    (h : ∀ D : Bank n, B.Ext D → ∀ j:Int, D.Grow c (fun E => E.Has (fun x => bits k (W x) j))) :
    B.Grow (k*c) (fun D => HasWord k D W) := by
  apply (B.collectFin k (fun i x => (W x).testBit i.val) c ?_).weaken (le_refl _)
  · intro D hD; exact fromFin hk hD
  · intro D e i; simpa only [bits,idxNat i.isLt] using h D e i.val

lemma rotated {B : Bank n} {W : Word n} {s : Nat} (h : HasWord k B W) (hs : s<k)
    (hw : ∀x,W x<2^k) : HasWord k B (fun x => rot k s (W x)) := by
  intro j; simpa only [bitsRot hs (hw _)] using h (j-s)

lemma xorWords {B : Bank n} {W V : Word n} (hk : 0<k) (h : HasWord k B W) (v : HasWord k B V) :
    B.Grow (k*4) (fun D => HasWord k D (fun x => W x ^^^ V x)) := by
  apply wordBuild hk
  intro D e j
  simpa only [bitsXor] using xor2 (e (h j)) (e (v j))

lemma chiBit {B : Bank n} {a b c : BitFn n} (ha:B.Has a) (hb:B.Has b) (hc:B.Has c) :
    B.Grow 6 (fun D => D.Has (fun x => chi (a x) (b x) (c x))) := by
  apply (inv hb).bind (b:=5)
  intro D e hnot
  apply (meet hnot (e hc)).bind (b:=4)
  intro E f hh
  exact xor2 (f (e ha)) hh

lemma nonlinear {B : Bank n} {W : Word n} (hk:0<k) (h:HasWord k B W) :
    B.Grow (k*6) (fun D => HasWord k D (fun x => rawStep k (W x))) := by
  apply wordBuild hk
  intro D e j
  simpa only [bitsStep hk] using chiBit (e (h j)) (e (h (j+1))) (e (h (j+2)))

lemma xorConst {B : Bank n} {W : Word n} (hk:0<k) (h:HasWord k B W) (C:Nat) :
    B.Grow (k*1) (fun D => HasWord k D (fun x => W x ^^^ C)) := by
  apply wordBuild hk
  intro D e j
  simpa only [bitsXor] using Bank.xorConst (e (h j)) (bits k C j)

def round (k dist shift C w state : Nat) :=
  rawStep k (state ^^^ rot k dist state ^^^ rot k (k-dist) state) ^^^ rot k shift w ^^^ C

lemma oneRound {B : Bank n} {W V : Word n} {dist shift : Nat} (hk:0<k)
    (h1:dist<k) (h2:k-dist<k) (hs:shift<k) (C:Nat)
    (hW:HasWord k B W) (hV:HasWord k B V) (bw:∀ x,W x<2^k) (bv:∀ x,V x<2^k) :
    B.Grow (k*19) (fun E => HasWord k E (fun x => round k dist shift C (W x) (V x))) := by
  have a:=rotated hV h1 bv
  have b:=rotated hV h2 bv
  have key:=rotated hW hs bw
  obtain ⟨D,e,de,t⟩:=xorWords hk hV a
  obtain ⟨E,f,ef,u⟩:=xorWords hk t (wordLift e b)
  obtain ⟨F,g,fg,v⟩:=nonlinear hk u
  obtain ⟨G,j,gj,p⟩:=xorWords hk v (wordLift g (wordLift f (wordLift e key)))
  obtain ⟨H,m,mh,q⟩:=xorConst hk p C
  exact ⟨H,fun h=>m (j (g (f (e h)))),by omega,q⟩

lemma roundBound {k dist shift C w state : Nat} (hC:C<2^k) : round k dist shift C w state<2^k :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepBound ..) (Nat.mod_lt _ (by positivity))) hC

end Eval
end PEqualNP.Outside.L_meta_25502_aux

namespace PEqualNP.Outside.L_meta_25502_aux.Name
open Builder Builder.Bank PEqualNP.MetaComplexity

theorem nameIndexSucc {n : ℕ} (x : Fin (n + 1) → Bool) :
    tableIndex x = tableIndex (fun i : Fin n => x i.castSucc)
      + (if x (Fin.last n) = true then 2 ^ n else 0) := by
  unfold tableIndex
  rw [Fin.sum_univ_castSucc]
  rfl

theorem nameIndexLt : ∀ {n : ℕ} (x : Fin n → Bool), tableIndex x < 2 ^ n := by
  intro n
  induction n with
  | zero => intro x; simp [tableIndex]
  | succ n ih =>
    intro x
    rw [nameIndexSucc, pow_succ]
    have := ih (fun i : Fin n => x i.castSucc)
    split <;> omega

theorem nameIndexBit : ∀ {n : ℕ} (x : Fin n → Bool) (i : Fin n),
    Nat.testBit (tableIndex x) i = x i := by
  intro n
  induction n with
  | zero => intro x i; exact i.elim0
  | succ n ih =>
    intro x i
    have hlt := nameIndexLt (fun i : Fin n => x i.castSucc)
    rw [nameIndexSucc]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.val_last]
      by_cases h : x (Fin.last n) = true
      · simp only [h, ↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        rw [Nat.add_zero, Nat.testBit_lt_two_pow hlt]
    · have hj : (j.castSucc : ℕ) = (j : ℕ) := rfl
      rw [hj]
      by_cases h : x (Fin.last n) = true
      · simp only [h, ↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_gt j.isLt]
        exact ih _ j
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        rw [Nat.add_zero]
        exact ih _ j

def name {k n : Nat} (atWire : Fin k → Fin n) (x : Fin n → Bool) : Nat :=
  (Fin.ofNat (2^k) (tableIndex fun i : Fin k => x (atWire i))).val

lemma nameLt {k n : Nat} (atWire : Fin k → Fin n) (x : Fin n → Bool) :
    name atWire x < 2^k := (Fin.ofNat (2^k) (tableIndex fun i : Fin k => x (atWire i))).isLt

lemma nameBit {k n : Nat} (atWire : Fin k → Fin n) (x : Fin n → Bool) (i : Fin k) :
    (name atWire x).testBit i.val = x (atWire i) := by
  change ((tableIndex fun i : Fin k => x (atWire i)) % 2^k).testBit i.val = _
  rw [Nat.mod_eq_of_lt (nameIndexLt _), nameIndexBit]

lemma nameSig {k n : Nat} (hk : 0<k) (atWire : Fin k → Fin n) (j : Int) :
    (Bank.empty n).Has (fun x => bits k (name atWire x) j) := by
  let i : Fin k := ⟨idx k j,idxlt hk j⟩
  have e (x : Fin n → Bool) : bits k (name atWire x) j = x (atWire i) := nameBit atWire x i
  simpa only [e] using Bank.input (atWire i)

abbrev row (k : Nat) := name (fun i : Fin k => Fin.castAdd k i)
abbrev col (k : Nat) := name (fun i : Fin k => Fin.natAdd k i)

end PEqualNP.Outside.L_meta_25502_aux.Name

namespace PEqualNP.Outside.L_meta_25502_aux.FreeDP
open PEqualNP.Outside.L_meta_25502_aux.Builder

abbrev Guard (n : Nat) := Nat → BitFn n
abbrev State (d : Nat) := Fin (2^d)

def pattern {d : Nat} (s : State d) (bit : Bool) := s.val + (if bit then 2^d else 0)

lemma pattern_lt {d : Nat} (s : State d) (bit : Bool) : pattern s bit < 2^(d+1) := by
  have := s.isLt
  cases bit <;> simp [pattern,Nat.pow_succ] <;> omega

lemma pattern_mod {d : Nat} (s : State d) (bit : Bool) : pattern s bit % 2^d = s.val := by
  cases bit <;> simp [pattern,Nat.mod_eq_of_lt s.isLt]

lemma find_pattern {d w : Nat} (s : State d) (hm : w%2^d = s.val) :
    ∃ bit, pattern s bit = w%2^(d+1) := by
  rw [Nat.mod_pow_succ,hm]
  by_cases z : (w/2^d)%2=0
  · exact ⟨false,by simp [pattern,z]⟩
  · have o : (w/2^d)%2=1 := by omega
    exact ⟨true,by simp [pattern,o]⟩

def succState {d : Nat} (s : State d) (bit : Bool) : State d :=
  ⟨pattern s bit/2, by have := pattern_lt s bit; rw [Nat.pow_succ] at this; omega⟩

def active {n d : Nat} : List (Guard n) → State d → BitFn n
  | [],_ => fun _ => true
  | g::gs,s => fun x => (g (pattern s false) x && active gs (succState s false) x) ||
                          (g (pattern s true) x && active gs (succState s true) x)

def valid {n} (d : Nat) (gs : List (Guard n)) (w : Nat) (x : Fin n → Bool) : Prop :=
  ∀ i : Fin gs.length, gs[i.val] ((w/2^i.val)%2^(d+1)) x=true

lemma valid_cons {n d w : Nat} (g : Guard n) (gs : List (Guard n)) (x) :
    valid d (g::gs) w x ↔ g (w%2^(d+1)) x=true ∧ valid d gs (w/2) x := by
  have shift (i : Nat) : (w/2)/2^i = w/2^(i+1) := by
    rw [Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm 2]
  constructor
  · intro h
    refine ⟨by simpa using h ⟨0,by simp⟩,?_⟩
    intro j
    simpa [shift] using h ⟨j.val+1,by simp⟩
  · rintro ⟨a,b⟩ ⟨i,hi⟩
    cases i with
    | zero => simpa using a
    | succ i =>
      have h := b ⟨i,by simp at hi;omega⟩
      simpa [shift] using h

theorem active_iff {n d : Nat} (gs : List (Guard n)) (s : State d) (x) :
    active gs s x=true ↔ ∃ w : Fin (2^(gs.length+d)), w.val % 2^d=s.val ∧ valid d gs w.val x := by
  induction gs generalizing s with
  | nil =>
    constructor
    · intro _
      refine ⟨⟨s.val,by simp⟩,Nat.mod_eq_of_lt s.isLt,?_⟩
      intro i
      exact Fin.elim0 i
    · intro _; rfl
  | cons g gs ih =>
    have bridge : active (g::gs) s x=true ↔
        ∃ bit : Bool, g (pattern s bit) x=true ∧ active gs (succState s bit) x=true := by
      simp only [active,Bool.or_eq_true,Bool.and_eq_true]
      constructor
      · rintro (h|h)
        · exact ⟨false,h⟩
        · exact ⟨true,h⟩
      · rintro ⟨b,h⟩
        cases b
        · exact Or.inl h
        · exact Or.inr h
    rw [bridge]
    have bound : 2^((g::gs).length+d) = 2^(gs.length+d)*2 := by
      rw [List.length_cons,Nat.succ_add,Nat.pow_succ]
    constructor
    · rintro ⟨bit,hg,ht⟩
      obtain ⟨v,hv,good⟩ := (ih (succState s bit)).mp ht
      let p := pattern s bit
      let w := v.val*2+p%2
      change v.val % 2^d=p/2 at hv
      have div : w/2=v.val := by dsimp [w];omega
      have rem : w%2=p%2 := by dsimp [w];omega
      have full : w%2^(d+1) = p := by
        rw [Nat.pow_succ,Nat.mul_comm (2^d) 2,Nat.mod_mul,div,rem,hv]
        omega
      refine ⟨⟨w,by rw [bound];have := v.isLt;dsimp [w];omega⟩,?_,?_⟩
      · have q := congrArg (fun a => a%2^d) full
        simpa [Nat.pow_succ,p,pattern_mod] using q
      · apply (valid_cons g gs x).mpr
        exact ⟨by rwa [full],by rwa [div]⟩
    · rintro ⟨w,hs,hw⟩
      obtain ⟨bit,hb⟩ := find_pattern s hs
      obtain ⟨hg,ht⟩ := (valid_cons g gs x).mp hw
      refine ⟨bit,by rwa [hb],(ih _).mpr ⟨⟨w.val/2,by have := w.isLt;omega⟩,?_,ht⟩⟩
      change w.val/2%2^d = pattern s bit/2
      rw [hb,Nat.pow_succ,Nat.mod_mul_left_div_self]

end PEqualNP.Outside.L_meta_25502_aux.FreeDP

namespace PEqualNP.Outside.L_meta_25502_aux.FreeDP
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_25502_aux.Builder
open PEqualNP.Outside.L_meta_25502_aux.Builder.Bank

private abbrev Good (g : Gate) :=
  g.op ∈ ({GateOp.and,.or,.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private lemma keepOne {n} {B : Bank n} {f : BitFn n} (h : B.Has f) :
    B.Grow 1 (fun D => D.Has f) := ⟨B,fun x => x,by omega,h⟩

private lemma copyOne {n} (B : Bank n) (g : Gate) (good : Good g) (f : Nat → BitFn n)
    (hf : ∀ i, B.Has (f i)) :
    B.Grow 1 (fun D => D.Has (fun x => g.op.eval (g.inputs.map (fun i => f i x)))) := by
  obtain ⟨op,r⟩ := g
  obtain ⟨hop,hlen⟩ := good
  change op ∈ ({GateOp.and,.or,.not} : Set GateOp) at hop
  change r.length ≤ 2 at hlen
  change B.Grow 1 (fun D => D.Has (fun x => op.eval (r.map (fun i => f i x))))
  rcases r with _ | ⟨i, _ | ⟨j,_ | ⟨z,l⟩⟩⟩
  · rcases hop with h|h|h
    · rw [show op=.and from h]; exact B.const true
    · rw [show op=.or from h]; exact B.const false
    · rw [show op=.not from h]; exact B.const true
  · rcases hop with h|h|h
    · rw [show op=.and from h]; simpa [GateOp.eval] using keepOne (hf i)
    · rw [show op=.or from h]; simpa [GateOp.eval] using keepOne (hf i)
    · rw [show op=.not from h]; exact inv (hf i)
  · rcases hop with h|h|h
    · rw [show op=.and from h]; simpa [GateOp.eval] using meet (hf i) (hf j)
    · rw [show op=.or from h]; simpa [GateOp.eval] using join (hf i) (hf j)
    · rw [show op=.not from h]; exact inv (hf i)
  · simp at hlen

private def wire {n : Nat} (gs : List Gate) (i : Nat) (x : Fin n → Bool) : Bool :=
  ((⟨gs,0⟩ : Circuit).wires (List.ofFn x)).getD i false

private lemma copyLength (gs : List Gate) (x : List Bool) :
    ((⟨gs,0⟩ : Circuit).wires x).length = x.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp [Circuit.wires,List.foldl_append] at ih ⊢
    omega

private lemma wirePush {n : Nat} (gs : List Gate) (g : Gate) (j : Nat) (x : Fin n → Bool) :
    wire (gs++[g]) j x =
      if j<n+gs.length then wire gs j x else if j=n+gs.length then
        g.op.eval (g.inputs.map (fun i=>wire gs i x)) else false := by
  let ws := (⟨gs,0⟩ : Circuit).wires (List.ofFn x)
  let b := g.op.eval (g.inputs.map (fun i=>wire gs i x))
  have hl : ws.length=n+gs.length := by simp [ws,copyLength]
  have he : wire (gs++[g]) j x = (ws++[b]).getD j false := by
    simp [wire,ws,b,Circuit.wires,List.foldl_append]
  rw [he]
  split_ifs with a a
  · rw [List.getD_append _ _ _ _ (by omega)];rfl
  · rw [← hl] at a
    subst j
    simp [b]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

lemma copyGuard {n : Nat} (B : Bank n) (C : Circuit) (hf : FanInTwo C) (_hr : ReadsBack n C)
    (ins : ∀ j : Fin n, B.Has (fun x => x j)) (zero : B.Has (fun _ => false)) :
    B.Grow C.size (fun D => D.Has (fun x => C.eval (List.ofFn x))) := by
  have make (gs : List Gate) (good : ∀ g ∈ gs, Good g) :
      B.Grow gs.length (fun D => ∀ i, D.Has (wire gs i)) := by
    induction gs using List.reverseRecOn with
    | nil =>
      apply Grow.pure
      intro i
      by_cases hi : i<n
      · have eqn : @wire n [] i = (fun x => x ⟨i,hi⟩) := by
          funext x
          simp [wire,Circuit.wires,List.getD_eq_getElem?_getD,hi]
        rw [eqn]; exact ins ⟨i,hi⟩
      · have eqn : @wire n [] i = (fun _ => false) := by
          funext x
          simp [wire,Circuit.wires,List.getD_eq_getElem?_getD,hi]
        rw [eqn]; exact zero
    | append_singleton gs g ih =>
      obtain ⟨D,e,c,h⟩ := ih (fun z hz => good z (by simp [hz]))
      obtain ⟨E,f,d,t⟩ := copyOne D g (good g (by simp)) (wire gs) h
      refine ⟨E,fun a=>f (e a),by simp;omega,?_⟩
      intro j
      by_cases hl : j<n+gs.length
      · have eqn : @wire n (gs++[g]) j = wire gs j := by
          funext x; simp [wirePush,hl]
        rw [eqn]; exact f (h j)
      · by_cases hj : j=n+gs.length
        · have eqn : @wire n (gs++[g]) j = (fun x=>g.op.eval (g.inputs.map fun i=>wire gs i x)) := by
            funext x; simp [wirePush,hl,hj]
          rw [eqn]; exact t
        · have eqn : @wire n (gs++[g]) j = (fun _ => false) := by
            funext x; simp [wirePush,hl,hj]
          rw [eqn]; exact f (e zero)
  obtain ⟨D,e,c,h⟩ := make C.gates hf
  exact ⟨D,e,c,h C.output⟩

end PEqualNP.Outside.L_meta_25502_aux.FreeDP

namespace PEqualNP.Outside.L_meta_25502_aux.FreeDP
open PEqualNP.Outside.L_meta_25502_aux.Builder
open Bank

def Available {n : Nat} (d b : Nat) (B : Bank n) (g : Guard n) : Prop :=
  ∀ D : Bank n, B.Ext D → ∀ p<2^(d+1), D.Grow b (fun E => E.Has (g p))

lemma dpBuild {n : Nat} (B : Bank n) (d b : Nat) (gs : List (Guard n))
    (available : ∀ g ∈ gs, Available d b B g) (one : B.Has (fun _ => true)) :
    B.Grow (gs.length * (2^d*(2*b+3))) (fun E => ∀ s : State d,E.Has (active gs s)) := by
  induction gs with
  | nil =>
    simpa [active] using (Grow.pure B (p:=fun E => ∀ _ : State d,E.Has (fun _ => true)) (fun _=>one))
  | cons g gs ih =>
    obtain ⟨D,e,de,tail⟩ := ih (fun z hz => available z (by simp [hz]))
    have ag := available g (by simp)
    have emit (F : Bank n) (f : D.Ext F) (s : State d) :
        F.Grow (2*b+3) (fun E => E.Has (active (g::gs) s)) := by
      obtain ⟨G,j,fg,z⟩ := ag F (fun h=>f (e h)) _ (pattern_lt s false)
      obtain ⟨H,m,gh,o⟩ := ag G (fun h=>j (f (e h))) _ (pattern_lt s true)
      obtain ⟨K,k,hk,z'⟩ := meet (m z) (m (j (f (tail (succState s false)))))
      obtain ⟨L,l,kl,o'⟩ := meet (k o) (k (m (j (f (tail (succState s true))))))
      obtain ⟨M,a,lm,ans⟩ := join (l z') o'
      exact ⟨M,fun h=>a (l (k (m (j h)))),by omega,ans⟩
    obtain ⟨E,f,ef,yes⟩ := D.collectFin (2^d) (fun s => active (g::gs) s) (2*b+3) emit
    exact ⟨E,fun h => f (e h),by rw [List.length_cons,Nat.succ_mul];omega,yes⟩

private lemma orBits {n : Nat} {α : Type} {B : Bank n} (l : List α) (f : α → BitFn n)
    (zero : B.Has (fun _ => false)) (hf : ∀ i ∈ l,B.Has (f i)) :
    B.Grow l.length (fun D => D.Has (fun x=>l.any (fun i=>f i x))) := by
  induction l with
  | nil => simpa using Grow.pure B zero
  | cons a l ih =>
    have h := ih (fun i hi => hf i (by simp [hi]))
    simpa using h.bind (b:=1) (fun _ e v => join (e (hf a (by simp))) v)

lemma finishDP {n : Nat} (d b : Nat) (gs : List (Guard n))
    (ag : ∀ B : Bank n, (∀ i : Fin n,B.Has (fun x=>x i)) → B.Has (fun _=>false) →
      ∀ g ∈ gs, Available d b B g) :
    (Bank.empty n).Grow (2^d * (gs.length*(2*b+3)+1)+2)
      (fun D=>D.Has (fun x=>(List.finRange (2^d)).any (fun s=>active gs s x))) := by
  obtain ⟨B,e,eb,zero⟩ := Bank.const (Bank.empty n) false
  obtain ⟨D,f,bd,one⟩ := Bank.const B true
  obtain ⟨E,m,de,ans⟩ := dpBuild D d b gs (ag D (fun i=>f (e (Bank.input i))) (f zero)) one
  obtain ⟨F,j,ef,last⟩ := orBits (List.finRange (2^d)) (active gs) (m (f zero)) (fun s _=>ans s)
  refine ⟨F,fun h=>j (m (f (e h))),?_,last⟩
  simp only [List.length_finRange] at ef
  have eq : 2^d*(gs.length*(2*b+3)+1)=gs.length*(2^d*(2*b+3))+2^d := by ring
  rw [eq]
  omega

end PEqualNP.Outside.L_meta_25502_aux.FreeDP

namespace PEqualNP.Outside.L_meta_25502_aux
open FreeDP Builder in
theorem freeWindow : ∀ (n t d b : Nat)
  (guard : Fin t → Nat → (Fin n → Bool) → Bool),
  (∀ (i : Fin t) (pattern : Nat), pattern < 2 ^ (d + 1) →
    ∃ G : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo G ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack n G ∧
      G.size ≤ b ∧
      ∀ x : Fin n → Bool, G.eval (List.ofFn x) = guard i pattern x) →
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
    C.size ≤ 2 ^ d * (t * (2 * b + 3) + 1) + 2 ∧
    ∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔
      ∃ word : Fin (2 ^ (t + d)), ∀ i : Fin t,
        guard i ((word.val / 2 ^ i.val) % 2 ^ (d + 1)) x = true) := by
  intro n t d b guard hypothesis
  let gs := List.ofFn guard
  have len : gs.length=t := List.length_ofFn
  have grown := finishDP d b gs (by
    intro B ins zero g hg D ext p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
    obtain ⟨C,hf,hr,sz,correct⟩ := hypothesis i p hp
    apply (copyGuard D C hf hr (fun j=>ext (ins j)) (ext zero)).weaken sz
    intro E h
    simpa only [correct] using h)
  obtain ⟨C,hf,hr,sz,correct⟩ := Bank.finish grown
  refine ⟨C,hf,hr,by simpa only [len] using sz,?_⟩
  intro x
  rw [correct,List.any_eq_true]
  have matchGuard (w : Nat) : valid d gs w x ↔
      ∀ i : Fin t, guard i ((w/2^i.val)%2^(d+1)) x=true := by
    constructor
    · intro h i
      simpa [gs] using h ⟨i.val,by simp [gs]⟩
    · intro h i
      simpa [gs] using h ⟨i.val,by simpa only [←len] using i.isLt⟩
  constructor
  · rintro ⟨s,_,act⟩
    obtain ⟨w,_,hw⟩ := (active_iff gs s x).mp act
    exact ⟨⟨w.val,lt_of_lt_of_eq w.isLt (congrArg (fun l => 2^(l+d)) len)⟩,(matchGuard _).mp hw⟩
  · rintro ⟨w,hw⟩
    let s : State d := ⟨w.val % 2^d,Nat.mod_lt _ (by positivity)⟩
    exact ⟨s,List.mem_finRange _,(active_iff gs s x).mpr
      ⟨⟨w.val,lt_of_lt_of_eq w.isLt (congrArg (fun l => 2^(l+d)) len.symm)⟩,rfl,(matchGuard _).mpr hw⟩⟩

end PEqualNP.Outside.L_meta_25502_aux

namespace PEqualNP.Outside.L_meta_25502_aux.Guard502

def rowWord (k t w u : Nat) :=
  (List.range t).foldl (fun state j =>
    Eval.round k 1 (2*j) (3^(k+(j+1))%2^k) w state) (rot k 1 w ^^^ u)

def colSteps (k r t w v : Nat) :=
  (List.range t).foldl (fun state j =>
    Eval.round k 2 (3*(j+1)+1) (3^(k+(r+(j+1)))%2^k) w state) (rot k 3 w ^^^ v)

def colWord (k r w v : Nat) := colSteps k r r w v

def pick {k : Nat} : Option (Fin k) → Nat → Bool
  | none, _ => true
  | some j, w => !(w.testBit j.val)

end PEqualNP.Outside.L_meta_25502_aux.Guard502

namespace PEqualNP.Outside.L_meta_25502_aux.Zero502
open Builder Builder.Bank

def req (k d u w : Nat) (i : Fin k) : Bool :=
  if k-(k+1)/2 ≤ idx k ((i.val:Int)+d) then bits k u ((i.val:Int)+d) == bits k w i.val else true

def pred (k u v w : Nat) (i : Fin k) : Bool := req k 1 u w i && req k 3 v w i

private lemma idxNat {k i : Nat} (hi : i<k) : idx k (i:Int)=i := by
  unfold idx
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  rfl

private lemma idxAddBack {k : Nat} (hk : 0<k) (j d : Int) :
    idx k (((idx k (j-d):Nat):Int)+d)=idx k j := by
  have hc : ((idx k (j-d):Nat):Int) = (j-d)%(k:Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  rw [hc]
  unfold idx
  rw [Int.emod_add_emod]
  congr 2
  omega

private lemma req_iff {k d u w : Nat} (hk : 0<k) (hd : d<k) (hu : u<2^k) (hw : w<2^k) :
    (∀ i : Fin k, req k d u w i=true) ↔
      rot k d w ^^^ u < 2^(k-(k+1)/2) := by
  have ylt : rot k d w ^^^ u < 2^k :=
    Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) hu
  constructor
  · intro all
    apply Nat.lt_pow_two_of_testBit
    intro j hj
    by_cases lim : j<k
    · let i : Fin k := ⟨idx k ((j:Int)-d),idxlt hk _⟩
      have back : idx k ((i.val:Int)+d)=j := (idxAddBack hk (j:Int) (d:Int)).trans (idxNat lim)
      have recv := all i
      simp only [req,back,hj,ite_true,beq_iff_eq] at recv
      have v : bits k (rot k d w ^^^ u) (j:Int) = false := by
        rw [bitsXor,bitsRot hd hw]
        have recv' : u.testBit j = w.testBit (idx k ((j:Int)-d)) := by
          simpa only [bits,back,idxNat i.isLt,i] using recv
        simp only [bits,idxNat lim,recv']
        simp
      simpa only [bits,idxNat lim] using v
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le ylt (Nat.pow_le_pow_right (by decide) (by omega)))
  · intro bound i
    unfold req
    split
    · rename_i h
      have v : bits k (rot k d w ^^^ u) ((i.val:Int)+d) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) h))
      rw [bitsXor,bitsRot hd hw,show (i.val:Int)+d-d=i.val by omega] at v
      simp at v
      simpa using v.symm
    · rfl

lemma pass {k u v w : Nat} (hk : 5≤k) (hw : w<2^k) (hu : u<2^k) (hv : v<2^k) :
    (∀ i : Fin k, pred k u v w i=true) ↔
    (rot k 1 w ^^^ u < 2^(k-(k+1)/2)) ∧ (rInit k w v < 2^(k-(k+1)/2)) := by
  simpa only [pred,Bool.and_eq_true,forall_and,rInit] using
    (and_congr (req_iff (d:=1) (by omega : 0<k) (by omega) hu hw)
      (req_iff (d:=3) (by omega : 0<k) (by omega) hv hw))

lemma local_eq {k u v w z : Nat} (i : Fin k) (he : bits k w i.val = bits k z i.val) :
    pred k u v w i = pred k u v z i := by simp only [pred,req,he]

private lemma reqGrow {k n d w : Nat} (B : Bank n) (u : (Fin n → Bool) → Nat) (i : Fin k)
    (h : B.Has (fun x=>bits k (u x) ((i.val:Int)+d))) :
    B.Grow 1 (fun E=>E.Has (fun x=>req k d (u x) w i)) := by
  by_cases hi : k-(k+1)/2 ≤ idx k ((i.val:Int)+d)
  · have eq (x) : (bits k (u x) ((i.val:Int)+d) == bits k w i.val) =
        xor (bits k (u x) ((i.val:Int)+d)) (!(bits k w i.val)) := by
      cases bits k (u x) ((i.val:Int)+d) <;> cases bits k w i.val <;> rfl
    simpa only [req,hi,ite_true,eq] using Bank.xorConst h (!(bits k w i.val))
  · simpa only [req,hi,ite_false] using B.const true

lemma guard {k : Nat} (hk : 5≤k) (w : Nat) (i : Fin k) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+k) C ∧ C.size ≤ 3 ∧
      ∀ x : Fin (k+k)→Bool, C.eval (List.ofFn x) = pred k (Name.row k x) (Name.col k x) w i := by
  apply Bank.finish
  have a := Name.nameSig (k:=k) (by omega) (fun j : Fin k=>Fin.castAdd k j) ((i.val:Int)+1)
  have b := Name.nameSig (k:=k) (by omega) (fun j : Fin k=>Fin.natAdd k j) ((i.val:Int)+3)
  obtain ⟨D,e,ds,h₁⟩ := reqGrow (d:=1) (w:=w) (Bank.empty (k+k)) (Name.row k) i a
  obtain ⟨F,f,fs,h₂⟩ := reqGrow (d:=3) (w:=w) D (Name.col k) i (e b)
  obtain ⟨H,m,ms,h₃⟩ := meet (f h₁) h₂
  exact ⟨H,fun h=>m (f (e h)),by omega,h₃⟩

end PEqualNP.Outside.L_meta_25502_aux.Zero502

namespace PEqualNP.Outside.L_meta_25502_aux.Guard502
open Builder Builder.Bank Eval

private def foldWord (k dist init : Nat) (shift cn : Nat → Nat) (w v t : Nat) :=
  (List.range t).foldl (fun state j =>
    Eval.round k dist (shift j) (3^(k+cn j)%2^k) w state) (rot k init w ^^^ v)

private lemma fold_succ (k d init : Nat) (shift cn : Nat → Nat) (w v t : Nat) :
    foldWord k d init shift cn w v (t+1) =
      Eval.round k d (shift t) (3^(k+cn t)%2^k) w (foldWord k d init shift cn w v t) := by
  simp [foldWord,List.range_succ,List.foldl_append]

private lemma fold_lt (k d init : Nat) (shift cn : Nat → Nat) (w v : Nat)
    (hv : v<2^k) (t : Nat) : foldWord k d init shift cn w v t < 2^k := by
  cases t with
  | zero => exact Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) hv
  | succ t => rw [fold_succ]; exact roundBound (Nat.mod_lt _ (by positivity))

private lemma foldCost {n k : Nat} {B : Bank n} {V : Word n}
    {d init w : Nat} (hk : 0<k) (hd : d<k) (hd' : 0<d) (hi : init<k) (hw : w<2^k)
    (key : HasWord k B (fun _ => w)) (name : HasWord k B V) (bv : ∀x,V x<2^k)
    (shift cn : Nat → Nat) (t : Nat) (sh : ∀ j, j<t → shift j<k) :
    B.Grow (4*k + 19*k*t) (fun E => HasWord k E (fun x => foldWord k d init shift cn w (V x) t)) := by
  induction t with
  | zero =>
    apply (xorWords hk (rotated key hi (fun _=>hw)) name).weaken (by omega)
    intro E h
    exact h
  | succ t ih =>
    obtain ⟨E,e,ce,wh⟩ := ih (fun j hj => sh j (by omega))
    obtain ⟨F,f,cf,wo⟩ := oneRound (dist:=d) (shift:=shift t)
      hk hd (by omega) (sh t (by omega)) (3^(k+cn t)%2^k) (wordLift e key) wh (fun _ => hw)
      (fun x => fold_lt k d init shift cn w (V x) (bv x) t)
    refine ⟨F,fun h => f (e h),?_,?_⟩
    · rw [Nat.mul_succ]
      omega
    · simpa only [fold_succ] using wo

private lemma pickCost {n k : Nat} {D : Bank n} {V : Word n} (p : Option (Fin k))
    (one : D.Has (fun _=>true)) (word : HasWord k D V) :
    D.Grow 1 (fun E => E.Has (fun x=>pick p (V x))) := by
  cases p with
  | none => exact ⟨D,fun h=>h,by omega,one⟩
  | some j =>
    exact inv (show D.Has (fun x => (V x).testBit j.val) by
      simpa only [bits,idxNat j.isLt] using word j.val)

theorem guardCost {k r : Nat} (B : Bank (k+k)) (emptyExt : (Bank.empty _).Ext B)
    (hk : 5≤k) (hkr : 14*r≤k) (w : Nat) (hw : w<2^k) (p q : Option (Fin k)) :
    B.Grow (38*k*r+8*k+5) (fun D => D.Has (fun x =>
      pick p (rowWord k r w (Name.row k x)) && pick q (colWord k r w (Name.col k x)))) := by
  obtain ⟨C,bc,cc,h0⟩ := B.const false
  obtain ⟨D,cd,dc,h1⟩ := C.const true
  have orig : (Bank.empty _).Ext D := fun h => cd (bc (emptyExt h))
  have key : HasWord k D (fun _=>w) := by
    intro j
    cases h : bits k w j <;> simp only [h]
    · exact cd h0
    · exact h1
  have wrow : HasWord k D (Name.row k) :=
    fun j => orig (Name.nameSig (by omega) (fun i : Fin k => Fin.castAdd k i) j)
  have wcol : HasWord k D (Name.col k) :=
    fun j => orig (Name.nameSig (by omega) (fun i : Fin k => Fin.natAdd k i) j)
  have row : D.Grow (4*k+19*k*r) (fun E => HasWord k E (fun x => rowWord k r w (Name.row k x))) :=
    foldCost (d:=1) (init:=1) (by omega) (by omega) (by decide) (by omega)
      hw key wrow (Name.nameLt _) (fun j => 2*j) (fun j => j+1) r (by intro j hj;omega)
  obtain ⟨E,de,ec,srow⟩ := row
  have col : E.Grow (4*k+19*k*r) (fun F => HasWord k F (fun x => colWord k r w (Name.col k x))) :=
    foldCost (d:=2) (init:=3) (by omega) (by omega) (by decide) (by omega)
      hw (wordLift de key) (wordLift de wcol) (Name.nameLt _) (fun j => 3*(j+1)+1)
      (fun j => r+(j+1)) r (by intro j hj;omega)
  obtain ⟨F,ef,fc,scol⟩ := col
  have one := ef (de h1)
  obtain ⟨H,fh,hc,a⟩ := pickCost p one (wordLift ef srow)
  obtain ⟨J,hj,jc,b⟩ := pickCost q (fh one) (wordLift fh scol)
  obtain ⟨K,jk,kc,out⟩ := meet (hj a) b
  refine ⟨K,fun h => jk (hj (fh (ef (de (cd (bc h)))))),?_,out⟩
  have add : 38*k*r = 19*k*r+19*k*r := by ring
  rw [add]
  omega

end PEqualNP.Outside.L_meta_25502_aux.Guard502

namespace PEqualNP.Outside.L_meta_25502_aux.Local502
open Guard502

private theorem rightRot {k d x : Nat} (hd : 0<d) (dk : d<k) (hx : x<2^k) (j : Int) :
    bits k (rot k (k-d) x) j = bits k x (j+(d:Int)) := by
  rw [bitsRot (show k-d<k by omega) hx]
  have eq : j-((k-d:Nat):Int) = j+(d:Int)-(k:Int) := by omega
  simp [bits,idx,eq]

theorem oneRound {k d sh c w w' a b : Nat} (hd : 0<d) (dk : d<k) (hs : sh<k)
    (hw : w<2^k) (hw' : w'<2^k) (ha : a<2^k) (hb : b<2^k) (j : Int)
    (key : bits k w (j-(sh:Int))=bits k w' (j-(sh:Int)))
    (state : ∀ z : Int, j-(d:Int)≤z → z≤j+(d:Int)+2 → bits k a z=bits k b z) :
    bits k (Eval.round k d sh c w a) j=bits k (Eval.round k d sh c w' b) j := by
  have mix (z : Int) (lz : j≤z) (rz : z≤j+2) :
      bits k (a ^^^ rot k d a ^^^ rot k (k-d) a) z =
        bits k (b ^^^ rot k d b ^^^ rot k (k-d) b) z := by
    simp only [bitsXor,rightRot hd dk ha,rightRot hd dk hb,bitsRot dk ha,bitsRot dk hb]
    rw [state z (by omega) (by omega),state (z-(d:Int)) (by omega) (by omega),
      state (z+(d:Int)) (by omega) (by omega)]
  simp only [bitsXor] at mix
  simp only [Eval.round,bitsXor,bitsStep (show 0<k by omega),bitsRot hs hw,bitsRot hs hw',key]
  rw [mix j (by omega) (by omega),mix (j+1) (by omega) (by omega),mix (j+2) (by omega) (by omega)]

theorem rowSucc (k t w u : Nat) :
    rowWord k (t+1) w u = Eval.round k 1 (2*t) (3^(k+(t+1))%2^k) w (rowWord k t w u) := by
  simp [rowWord,List.range_succ,List.foldl_append]

theorem colSucc (k r t w v : Nat) :
    colSteps k r (t+1) w v = Eval.round k 2 (3*(t+1)+1) (3^(k+(r+(t+1)))%2^k) w (colSteps k r t w v) := by
  simp [colSteps,List.range_succ,List.foldl_append]

theorem rowBound {k u : Nat} (t w : Nat) (hu : u<2^k) : rowWord k t w u < 2^k := by
  cases t with
  | zero => exact Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) hu
  | succ t => rw [rowSucc];exact Eval.roundBound (Nat.mod_lt _ (by positivity))

theorem colBound {k v : Nat} (r t w : Nat) (hv : v<2^k) : colSteps k r t w v < 2^k := by
  cases t with
  | zero => exact Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) hv
  | succ t => rw [colSucc];exact Eval.roundBound (Nat.mod_lt _ (by positivity))

private theorem rowTrace {k w w' u : Nat} (hk : 5≤k) (hw : w<2^k) (hw' : w'<2^k) (hu : u<2^k) :
    ∀ (t : Nat), 14*t ≤ k → ∀ j : Int,
    (∀ i : Int, j-(2*(t:Int)+1) ≤ i → i ≤ j+3*(t:Int)-1 → bits k w i=bits k w' i) →
    bits k (rowWord k t w u) j=bits k (rowWord k t w' u) j := by
  intro t
  induction t with
  | zero =>
    intro _ j key
    change bits k (rot k 1 w ^^^ u) j=bits k (rot k 1 w' ^^^ u) j
    simp only [bitsXor,bitsRot (show 1<k by omega) hw,bitsRot (show 1<k by omega) hw']
    rw [key (j-((1:Nat):Int)) (by omega) (by omega)]
  | succ t ih =>
    intro tk j key
    rw [rowSucc,rowSucc]
    apply oneRound (by decide) (by omega) (by omega) hw hw' (rowBound t w hu) (rowBound t w' hu)
    · apply key <;> omega
    · intro z a b
      apply ih (by omega) z
      intro i l h
      exact key i (by omega) (by omega)

private theorem colTrace {k w w' v : Nat} (hk : 5≤k) (hw : w<2^k) (hw' : w'<2^k) (hv : v<2^k)
    (r : Nat) :
    ∀ (t : Nat), 14*t ≤ k → ∀ j : Int,
    (∀ i : Int, (j-2*(t:Int)-3 ≤ i ∨ j-3*(t:Int)-1 ≤ i) → i ≤ j+4*(t:Int)-3 → bits k w i=bits k w' i) →
    bits k (colSteps k r t w v) j=bits k (colSteps k r t w' v) j := by
  intro t
  induction t with
  | zero =>
    intro _ j key
    change bits k (rot k 3 w ^^^ v) j=bits k (rot k 3 w' ^^^ v) j
    simp only [bitsXor,bitsRot (show 3<k by omega) hw,bitsRot (show 3<k by omega) hw']
    rw [key (j-((3:Nat):Int)) (Or.inl (by omega)) (by omega)]
  | succ t ih =>
    intro tk j key
    rw [colSucc,colSucc]
    apply oneRound (by decide) (by omega) (by omega) hw hw' (colBound r t w hv) (colBound r t w' hv)
    · apply key
      · right;omega
      · omega
    · intro z a b
      apply ih (by omega) z
      intro i l h
      apply key
      · rcases l with l|l
        · left;omega
        · right;omega
      · omega

theorem joint {k r w w' u v : Nat} (hk : 5≤k) (hr : 1≤r) (hkr : 14*r≤k)
    (hw : w<2^k) (hw' : w'<2^k) (hu : u<2^k) (hv : v<2^k) (j : Int)
    (agr : ∀ i : Int, j-(3*(r:Int)+2) ≤ i → i ≤ j+(4*(r:Int)-2) → bits k w i=bits k w' i) :
    bits k (rowWord k r w u) j = bits k (rowWord k r w' u) j ∧
    bits k (colWord k r w v) j = bits k (colWord k r w' v) j := by
  constructor
  · apply rowTrace hk hw hw' hu r hkr j
    intro i l h
    exact agr i (by omega) (by omega)
  · apply colTrace hk hw hw' hv r r hkr j
    intro i l h
    exact agr i (by omega) (by omega)

theorem window {k r w w' u v : Nat} (hk : 5≤k) (hr : 1≤r) (hkr : 14*r≤k)
    (hw : w<2^k) (hw' : w'<2^k) (hu : u<2^k) (hv : v<2^k) (j : Int)
    (agr : ∀ p : Nat, p ≤ 7*r →
      bits k w (j-(3*(r:Int)+2)+(p:Int))=bits k w' (j-(3*(r:Int)+2)+(p:Int))) :
    bits k (rowWord k r w u) j = bits k (rowWord k r w' u) j ∧
    bits k (colWord k r w v) j = bits k (colWord k r w' v) j := by
  apply joint hk hr hkr hw hw' hu hv j
  intro i hi hj
  let p := (i-(j-(3*(r:Int)+2))).toNat
  have pval : j-(3*(r:Int)+2)+(p:Int)=i := by dsimp [p];omega
  have e := agr p (by dsimp [p];omega)
  rwa [pval] at e

end PEqualNP.Outside.L_meta_25502_aux.Local502

namespace PEqualNP.Outside.L_meta_25502_aux.Window502
open PEqualNP.MetaComplexity (tableIndex)

def decodeKey (k : Nat) (start : Int) (word : Nat) : Nat :=
  tableIndex fun j : Fin k => word.testBit (idx k ((j.val:Int)-start))

lemma decodeLt (k : Nat) (start : Int) (word : Nat) : decodeKey k start word < 2^k :=
  Name.nameIndexLt _

lemma decodeBit {j k : Nat} (start : Int) (word : Nat) (hj : j<k) :
    bits k (decodeKey k start word) (start+(j:Int)) = word.testBit j := by
  let q := idx k (start+(j:Int))
  let i : Fin k := ⟨q,idxlt (by omega) _⟩
  change (tableIndex _).testBit i.val = _
  rw [Name.nameIndexBit _ i]
  change word.testBit (idx k ((q:Int)-start)) = _
  have eqn : (q:Int) = (start+j)%(k:Int) := by
    unfold q idx
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  unfold idx
  rw [eqn,Int.emod_sub_emod]
  rw [show start+(j:Int)-start=(j:Int) by omega]
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  rfl

def capture (k len : Nat) (start : Int) (w : Nat) : Fin (2^len) :=
  ⟨tableIndex (fun i : Fin len => bits k w (start+i.val)),Name.nameIndexLt _⟩

lemma captureBit {k len j : Nat} (start : Int) (w : Nat) (hj:j<len) :
    (capture k len start w).val.testBit j = bits k w (start+j) :=
  Name.nameIndexBit _ ⟨j,hj⟩

def pattern (w i d : Nat) := (w / 2^i) % 2^(d+1)

lemma patternBit {d j} (w i : Nat) (hj : j≤d) :
    (pattern w i d).testBit j = w.testBit (i+j) := by
  simp only [pattern,Nat.testBit_mod_two_pow,show j<d+1 by omega,decide_true,Bool.true_and]
  rw [←Nat.shiftRight_eq_div_pow,Nat.testBit_shiftRight]

lemma windowEquiv {k t d : Nat} (_hk : 0<k) (fit : t+d≤k) (start : Int)
    (P : Fin t → Nat → Prop)
    (stable : ∀ (i : Fin t) {w v : Nat}, w<2^k → v<2^k →
      (∀ j : Nat, j≤d → bits k w (start+i.val+j)=bits k v (start+i.val+j)) →
      (P i w ↔ P i v)) :
    (∃ u : Fin (2^(t+d)), ∀ i : Fin t,
      P i (decodeKey k (start+i.val) (pattern u.val i.val d))) ↔
    ∃ w : Fin (2^k), ∀ i : Fin t, P i w.val := by
  constructor
  · rintro ⟨u,hu⟩
    refine ⟨⟨decodeKey k start u.val,decodeLt ..⟩,?_⟩
    intro i
    apply (stable i (decodeLt ..) (decodeLt ..) ?_).mp (hu i)
    intro j hj
    have hi := i.isLt
    have h1 : j<k := by omega
    have h2 : i.val+j<k := by omega
    rw [decodeBit _ _ h1,patternBit _ _ hj,
      show start+i.val+j=start+((i.val+j:Nat):Int) by omega,decodeBit _ _ h2]
  · rintro ⟨w,hw⟩
    let u := capture k (t+d) start w.val
    refine ⟨u,?_⟩
    intro i
    apply (stable i w.isLt (decodeLt ..) ?_).mp (hw i)
    intro j hj
    have hi := i.isLt
    rw [decodeBit _ _ (show j<k by omega),patternBit _ _ hj]
    rw [show u.val.testBit (i.val+j) = bits k w.val (start+((i.val+j:Nat):Int)) from
      captureBit start w.val (by omega)]
    congr 1
    omega

end PEqualNP.Outside.L_meta_25502_aux.Window502

namespace PEqualNP.Outside.L_meta_25502_aux.Window502
open Builder Builder.Bank
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

abbrev Inputs (k : Nat) := Fin (k+k) → Bool

def aggregate (k : Nat) (T : Inputs k → Nat → Bool) (x : Inputs k) :=
  (List.range (2^k)).any (fun w => T x w)

def Realizes (k cost : Nat) (ff : Inputs k → Bool) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ ReadsBack (k+k) C ∧ C.size ≤ cost ∧
    ∀ x : Inputs k, C.eval (List.ofFn x) = ff x

lemma compile {k t d b : Nat} (hk : 0<k) (fit : t+d≤k) (start : Int)
    (P : Fin t → Nat → Inputs k → Bool) (T : Inputs k → Nat → Bool)
    (guards : ∀ i w, w<2^k → Realizes k b (P i w))
    (locality : ∀ x i {w v}, w<2^k → v<2^k →
      (∀ j : Nat, j≤d → bits k w (start+(i.val:Int)+j)=bits k v (start+i.val+j)) →
      P i w x=P i v x)
    (character : ∀ x w, w<2^k → ((∀ i, P i w x=true) ↔ T x w=true)) :
    Realizes k (2^d*(t*(2*b+3)+1)+2) (aggregate k T) := by
  let cell := fun (i : Fin t) z => P i (decodeKey k (start+i.val) z)
  obtain ⟨C,hfan,back,budget,hc⟩ := PEqualNP.Outside.L_meta_25502_aux.freeWindow (k+k) t d b cell
    (fun i z _ => guards i _ (decodeLt k (start+i.val) z))
  refine ⟨C,hfan,back,budget,?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [hc]
  change (∃ u : Fin (2^(t+d)), ∀ i : Fin t,
    P i (decodeKey k (start+i.val) (pattern u.val i.val d)) x=true) ↔ _
  rw [windowEquiv hk fit start (fun i w => P i w x=true)
    (fun i _ _ ha hb agree => by rw [locality x i ha hb agree])]
  change _ ↔ (List.range (2^k)).any (fun w => T x w)=true
  rw [List.any_eq_true]
  constructor
  · rintro ⟨w,pass⟩;exact ⟨w.val,List.mem_range.mpr w.isLt,(character x w w.isLt).mp pass⟩
  · rintro ⟨w,hw,pass⟩
    have h := List.mem_range.mp hw
    exact ⟨⟨w,h⟩,(character x w h).mpr pass⟩

lemma cap {k r t d b : Nat} (hk : r≤k) (ht : t≤k) (hd : d≤7*r)
    (hb : b≤38*k*r+8*k+5) :
    2^d*(t*(2*b+3)+1)+2 ≤ 100*(k+1)^3*2^(7*r) := by
  have hb' : b≤38*k*k+8*k+5 := by
    have hh := Nat.mul_le_mul_left (38*k) hk
    omega
  have z : k*(2*b+3)+3 ≤ 100*(k+1)^3 := by
    calc k*(2*b+3)+3 ≤ k*(2*(38*k*k+8*k+5)+3)+3 := by gcongr
         _ ≤ _ := by nlinarith [Nat.zero_le (k*k*k),Nat.zero_le (k*k)]
  have pt : t*(2*b+3) ≤ k*(2*b+3) := Nat.mul_le_mul_right _ ht
  have sz : t*(2*b+3)+3 ≤ 100*(k+1)^3 := by omega
  have pow : (2:Nat)^d≤2^(7*r) := Nat.pow_le_pow_right (by decide) hd
  calc
    2^d*(t*(2*b+3)+1)+2 ≤ 2^d*(t*(2*b+3)+3) := by
      have hp := Nat.two_pow_pos d
      let a := t*(2*b+3)+1
      change 2^d*a+2 ≤ 2^d*(a+2)
      rw [Nat.mul_add (2^d) a 2]; omega
    _ ≤ 2^(7*r)*(100*(k+1)^3) := Nat.mul_le_mul pow sz
    _ = _ := Nat.mul_comm ..

lemma highRange {k low w : Nat} (lo : low≤k) (hw : w<2^k) :
    (∀ i : Fin (k-low), w.testBit (low+i.val)=false) ↔ w < 2^low := by
  constructor
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro j hj
    by_cases hlt : j<k
    · let i : Fin (k-low) := ⟨j-low,by omega⟩
      have e := h i
      rw [show low+i.val=j by dsimp [i];omega] at e
      exact e
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega)))
  · intro h i
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))

end PEqualNP.Outside.L_meta_25502_aux.Window502

namespace PEqualNP.Outside.L_meta_25502_aux.Graph502
open Window502 Guard502

def target (k r : Nat) (x : Inputs k) (w : Nat) : Bool :=
  decide (rowWord k r w (Name.row k x) < 2^(k-(k+1)/2)) &&
  decide (colWord k r w (Name.col k x) < 2^(k-(k+1)/2))

end PEqualNP.Outside.L_meta_25502_aux.Graph502

namespace PEqualNP.Outside.L_meta_25502_aux.Graph502
open Window502

lemma zero502 {k : Nat} (hk : 5≤k) :
    Realizes k (100*(k+1)^3*2^(7*0)) (aggregate k (target k 0)) := by
  let P := fun (i : Fin k) w (x : Inputs k) => Zero502.pred k (Name.row k x) (Name.col k x) w i
  have hh := compile (k:=k) (t:=k) (d:=0) (b:=3) (by omega) (by omega) 0 P (target k 0)
    (fun i w _ => Zero502.guard hk w i) (by
      intro x i w v hw hv h
      apply Zero502.local_eq
      simpa using h 0 (by omega))
    (by
      intro x w hw
      have a := Zero502.pass hk hw (Name.nameLt (fun j : Fin k => Fin.castAdd k j) x)
        (Name.nameLt (fun j : Fin k => Fin.natAdd k j) x)
      change (∀ i, Zero502.pred k (Name.row k x) (Name.col k x) w i = true) ↔
        (decide (rot k 1 w ^^^ (Name.row k x) < 2^(k-(k+1)/2)) &&
         decide (rInit k w (Name.col k x) < 2^(k-(k+1)/2))) = true
      rw [Bool.and_eq_true_iff]
      exact a.trans (and_congr decide_eq_true_eq.symm.to_iff decide_eq_true_eq.symm.to_iff))
  obtain ⟨C,fan,back,sz,ev⟩ := hh
  exact ⟨C,fan,back,sz.trans (cap (r:=0) (by omega) (by omega) (by omega) (by omega)),ev⟩

end PEqualNP.Outside.L_meta_25502_aux.Graph502

namespace PEqualNP.Outside.L_meta_25502_aux.Graph502
open Builder Builder.Bank Window502 Guard502

theorem positive502 {k r : Nat} (hk : 5≤k) (hr : 1≤r) (hkr : 14*r≤k) :
    Realizes k (100*(k+1)^3*2^(7*r)) (aggregate k (target k r)) := by
  let low := k-(k+1)/2
  let t := k-low
  let d := 7*r
  let start : Int := (low:Int)-(3*(r:Int)+2)
  let b := 38*k*r+8*k+5
  have hlow : low≤k := Nat.sub_le ..
  have fit : t+d≤k := by dsimp [t,d,low];omega
  let place (i : Fin t) : Fin k := ⟨low+i.val,by have := i.isLt; dsimp [t] at this;omega⟩
  let P (i : Fin t) (w : Nat) (x : Inputs k) :=
    pick (some (place i)) (rowWord k r w (Name.row k x)) &&
    pick (some (place i)) (colWord k r w (Name.col k x))
  have guards (i : Fin t) (w : Nat) (hw : w<2^k) : Realizes k b (P i w) :=
    Bank.finish (guardCost (Bank.empty _) (fun h=>h) hk hkr w hw (some (place i)) (some (place i)))
  have locality (x : Inputs k) (i : Fin t) {w v : Nat} (hw : w<2^k) (hv : v<2^k)
      (agr : ∀ j : Nat, j≤d → bits k w (start+(i.val:Int)+j) = bits k v (start+i.val+j)) :
      P i w x=P i v x := by
    have center : ((place i).val:Int)=(low:Int)+(i.val:Int) := by simp [place]
    obtain ⟨rEq,cEq⟩ := Local502.joint hk hr hkr hw hv (Name.nameLt _ x) (Name.nameLt _ x)
      ((place i).val:Int) (u:=Name.row k x) (v:=Name.col k x) (by
        intro y ly ry
        let a := (y-(start+i.val)).toNat
        have nn : 0 ≤ y-(start+i.val) := by dsimp [start];omega
        have av : (a:Int)=y-(start+i.val) := Int.toNat_of_nonneg nn
        have ad : a≤d := by dsimp [start,d] at av ⊢;omega
        have eqv : start+i.val+(a:Int) = y := by omega
        simpa only [eqv] using agr a ad)
    simp only [bits,Eval.idxNat (place i).isLt] at rEq cEq
    simp only [P,pick,rEq,cEq]
  have character (x : Inputs k) (w : Nat) (_ : w<2^k) :
      (∀ i : Fin t, P i w x=true) ↔ target k r x w=true := by
    have rwBound := Local502.rowBound r w (Name.nameLt (fun i : Fin k => Fin.castAdd k i) x)
    have cwBound := Local502.colBound r r w (Name.nameLt (fun i : Fin k => Fin.natAdd k i) x)
    have rowOK := highRange hlow (show rowWord k r w (Name.row k x)<2^k from rwBound)
    have colOK := highRange hlow (show colWord k r w (Name.col k x)<2^k from cwBound)
    simp only [P,pick,target,Bool.and_eq_true,Bool.not_eq_true',decide_eq_true_eq]
    constructor
    · intro both
      exact ⟨rowOK.mp (fun i => (both i).1),colOK.mp (fun i => (both i).2)⟩
    · rintro ⟨row,col⟩ i
      exact ⟨rowOK.mpr row i,colOK.mpr col i⟩
  obtain ⟨C,fan,back,cost,run⟩ := Window502.compile (by omega) fit start P (target k r)
    guards (fun x i _ _ hw hv a => locality x i hw hv a) character
  refine ⟨C,fan,back,cost.trans (cap (by omega) (by dsimp [t];omega) (by rfl) (by rfl)),run⟩

end PEqualNP.Outside.L_meta_25502_aux.Graph502

open PEqualNP.Outside.L_meta_25502_aux in
theorem PEqualNP.Outside.L_meta_25502 : ∀ (k r : Nat), 5 ≤ k → (k % 6 = 1 ∨ k % 6 = 5) → 14 * r ≤ k →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let constant := fun (j : Nat) => 3 ^ (k + j) % 2 ^ k
  let first := fun (rowKey rowName : Nat) =>
    (List.range r).foldl (fun rowState rowIndex =>
      step (rowState ^^^ rot 1 rowState ^^^ rot (k - 1) rowState) ^^^
        rot (2 * rowIndex) rowKey ^^^ constant (rowIndex + 1)) (rot 1 rowKey ^^^ rowName)
  let second := fun (colKey colName : Nat) =>
    (List.range r).foldl (fun colState colIndex =>
      step (colState ^^^ rot 2 colState ^^^ rot (k - 2) colState) ^^^
        rot (3 * (colIndex + 1) + 1) colKey ^^^ constant (r + (colIndex + 1)))
      (rot 3 colKey ^^^ colName)
  let h := (k + 1) / 2
  let graph : Fin (2 ^ k) → Fin (2 ^ k) → Bool := fun row col =>
    (List.range (2 ^ k)).any (fun w =>
      decide (first w row.val < 2 ^ (k - h)) && decide (second w col.val < 2 ^ (k - h)))
  let budget := 100 * (k + 1) ^ 3 * 2 ^ (7 * r)
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + k) C ∧
    C.size ≤ budget ∧
    ∀ bits : Fin (k + k) → Bool,
      C.eval (List.ofFn bits) = PEqualNP.Represents.adjFun (k := k) (l := k) graph bits := by
  intro k r hk _ hkr
  have h : Window502.Realizes k (100*(k+1)^3*2^(7*r))
      (Window502.aggregate k (Graph502.target k r)) := by
    cases r with
    | zero => exact Graph502.zero502 hk
    | succ t => exact Graph502.positive502 hk (by omega) hkr
  exact h
