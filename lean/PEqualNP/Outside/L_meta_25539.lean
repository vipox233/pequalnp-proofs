import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25539_aux.BuilderLib.Builder
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
end PEqualNP.Outside.L_meta_25539_aux.BuilderLib.Builder

namespace PEqualNP.Outside.L_meta_25539_aux.BuilderLib.Builder.Bank

variable {n : Nat}

lemma xorConst {B : Bank n} {f : BitFn n} (a : B.Has f) (b : Bool) :
    B.Grow 1 (fun D => D.Has (fun x => xor (f x) b)) := by
  cases b with
  | false =>
    have h := Grow.pure B (p:=fun D => D.Has f) a
    simpa using h.weaken (b:=1) (q:=fun D => D.Has f) (by decide) (fun _ t => t)
  | true => simpa using inv a

private def foldOp (all : Bool) (a b : Bool) : Bool := if all then a && b else a || b

private lemma emitFoldOp {B : Bank n} (all : Bool) {f g : BitFn n}
    (a : B.Has f) (b : B.Has g) :
    B.Grow 1 (fun D => D.Has (fun x => foldOp all (f x) (g x))) := by
  cases all with
  | true => exact meet a b
  | false => exact join a b

private lemma foldSlots {α : Type} (all : Bool) (B : Bank n) (l : List α)
    (f : α → BitFn n) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i ∈ l, D.Grow cost (fun E => E.Has (f i))) :
    B.Grow (1+l.length*(cost+1)) (fun D => D.Has (fun x =>
      if all then l.all (fun i => f i x) else l.any (fun i => f i x))) := by
  induction l with
  | nil =>
    simpa using B.const all
  | cons a l ih =>
    have t := ih (fun D e i hi => emit D e i (by simp [hi]))
    have out := t.bind (b:=cost+1)
      (q:=fun E => E.Has (fun x => if all then (a::l).all (fun i => f i x)
        else (a::l).any (fun i => f i x))) (by
      intro D e acc
      apply (emit D e a (by simp)).bind (b:=1)
      intro E e' ha
      have computed := emitFoldOp all ha (e' acc)
      cases all <;> simpa [foldOp] using computed)
    simpa [Nat.succ_mul,Nat.add_assoc] using out

lemma anySlots {α : Type} (B : Bank n) (l : List α) (f : α → BitFn n) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i ∈ l, D.Grow cost (fun E => E.Has (f i))) :
    B.Grow (1+l.length*(cost+1))
      (fun D => D.Has (fun x => l.any (fun i => f i x))) :=
  foldSlots false B l f cost emit

lemma allSlots {α : Type} (B : Bank n) (l : List α) (f : α → BitFn n) (cost : Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i ∈ l, D.Grow cost (fun E => E.Has (f i))) :
    B.Grow (1+l.length*(cost+1))
      (fun D => D.Has (fun x => l.all (fun i => f i x))) :=
  foldSlots true B l f cost emit

lemma allBits {α : Type} {B : Bank n} (l : List α) (f : α → BitFn n)
    (h : ∀ i ∈ l, B.Has (f i)) :
    B.Grow (1+l.length) (fun D => D.Has (fun x => l.all (fun i => f i x))) := by
  simpa using allSlots B l f 0 (fun D e i hi => Grow.pure D (e (h i hi)))

lemma anyBits {α : Type} {B : Bank n} (l : List α) (f : α → BitFn n)
    (h : ∀ i ∈ l, B.Has (f i)) :
    B.Grow (1+l.length) (fun D => D.Has (fun x => l.any (fun i => f i x))) := by
  simpa using anySlots B l f 0 (fun D e i hi => Grow.pure D (e (h i hi)))

end PEqualNP.Outside.L_meta_25539_aux.BuilderLib.Builder.Bank

namespace PEqualNP.Outside.L_meta_25539_aux.BuilderLib
def chi (a b c : Bool) := xor a (!b && c)
def rot (k s w : Nat) := ((w <<< (s % k)) ||| (w >>> (k-s % k))) % 2^k
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
end PEqualNP.Outside.L_meta_25539_aux.BuilderLib

namespace PEqualNP.Outside.L_meta_25539_aux.BuilderLib
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
  have eq : (j % (k:Int)+(s:Int)).toNat = (j % (k:Int)).toNat + s := by omega
  rw [@Int.toNat_emod (j % (k:Int)+(s:Int)) (k:Int) (by omega) (by omega),eq]
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
end PEqualNP.Outside.L_meta_25539_aux.BuilderLib

namespace PEqualNP.Outside.L_meta_25539_aux.BuilderLib
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
end PEqualNP.Outside.L_meta_25539_aux.BuilderLib

namespace PEqualNP.Outside.L_meta_25539_aux.BuilderLib

abbrev recoverKey (k z v : Nat) := rot k (k-3) (z ^^^ v)

lemma recoverKeyLt (k z v : Nat) : recoverKey k z v < 2^k :=
  Nat.mod_lt _ (by positivity)

private lemma wordEqBits {k a b : Nat} (ha : a<2^k) (hb : b<2^k)
    (h : ∀ j : Int, bits k a j = bits k b j) : a=b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<k
  · have e : idx k (i : Int) = i := by
      unfold idx
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      rfl
    simpa only [bits,e] using h (i : Int)
  · have hp : 2^k ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hp),Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hp)]

lemma rotUndo {k s w : Nat} (hs : 0<s) (hsk : s<k) (hw : w<2^k) :
    rot k (k-s) (rot k s w) = w := by
  apply wordEqBits (k:=k) (a:=rot k (k-s) (rot k s w)) (Nat.mod_lt _ (by positivity)) hw
  intro j
  have hb : rot k s w < 2^k := Nat.mod_lt _ (by positivity)
  rw [bitsRot (show k-s<k by omega) hb,bitsRot hsk hw]
  have q : j - ((k-s:Nat):Int) - (s:Int) = j - (k:Int) := by omega
  simp [bits,idx,q]

end PEqualNP.Outside.L_meta_25539_aux.BuilderLib

namespace PEqualNP.Outside.L_meta_25539_aux.Recovery.Col97
open PEqualNP.Outside.L_meta_25539_aux.BuilderLib
open Builder Builder.Bank Eval
variable {n k : Nat}

def recover1 (k x u : Nat) := rot k (k-1) (x ^^^ u)
def rowInit (k w u : Nat) := rot k 1 w ^^^ u

lemma recover1Lt (k x u : Nat) : recover1 k x u < 2^k := Nat.mod_lt _ (by positivity)

lemma recover1Init {w u : Nat} (hk : 16≤k) (hw : w<2^k) :
    recover1 k (rowInit k w u) u = w := by
  simp only [recover1,rowInit,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
  exact rotUndo (by decide) (by omega) hw

lemma initRecover1 {z u : Nat} (hk : 16≤k) (hz : z<2^k) (hu : u<2^k) :
    rowInit k (recover1 k z u) u = z := by
  have hi := rotUndo (k:=k) (s:=k-1) (w:=z ^^^ u) (by omega) (by omega) (Nat.xor_lt_two_pow hz hu)
  rw [show k-(k-1)=1 by omega] at hi
  simp only [rowInit,recover1,hi,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]

end PEqualNP.Outside.L_meta_25539_aux.Recovery.Col97

namespace PEqualNP.Outside.L_meta_25539_aux.BuilderLib.Name
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

end PEqualNP.Outside.L_meta_25539_aux.BuilderLib.Name

namespace PEqualNP.Outside.L_meta_25539_aux.BuilderLib.V37
open Builder Builder.Bank Eval
variable {k n : Nat} {B : Bank n}

lemma rotAny {W : Word n} (s : Nat) (hk : 0<k)
    (h : HasWord k B W) (hw : ∀x,W x<2^k) :
    HasWord k B (fun x => rot k s (W x)) := by
  simpa only [rot,Nat.mod_mod] using rotated h (Nat.mod_lt s hk) hw

lemma roundAny {W V : Word n} (hk : 0<k) (d sh c : Nat) (w : HasWord k B W) (v : HasWord k B V)
    (bw : ∀x,W x<2^k) (bv : ∀x,V x<2^k) :
    B.Grow (k*19) (fun D => HasWord k D (fun x => round k d sh c (W x) (V x))) := by
  have a := rotAny d hk v bv
  have b := rotAny (k-d) hk v bv
  have key := rotAny sh hk w bw
  obtain ⟨D,e,de,t⟩ := xorWords hk v a
  obtain ⟨E,f,ef,u⟩ := xorWords hk t (wordLift e b)
  obtain ⟨F,g,fg,p⟩ := nonlinear hk u
  obtain ⟨G,h,gh,q⟩ := xorWords hk p (wordLift g (wordLift f (wordLift e key)))
  obtain ⟨H,i,ih,q'⟩ := Eval.xorConst hk q c
  exact ⟨H,fun h' => i (h (g (f (e h')))),by omega,q'⟩

end PEqualNP.Outside.L_meta_25539_aux.BuilderLib.V37

namespace PEqualNP.Outside.L_meta_25539_aux.Line

def rot (k s word : Nat) : Nat :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def stepBit (k word j : Nat) : Bool :=
  xor (word.testBit j) (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))

def step (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc j =>
    acc ||| ((xor (word.testBit j)
      (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0

def mix (k word : Nat) : Nat :=
  word ^^^ rot k 1 word ^^^ rot k (k - 1) word

def stateAt (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (rounds key : Nat) : Nat :=
  (List.range rounds).foldl (fun prev tick =>
    step k (mix k prev) ^^^ rot k (2 * tick) key ^^^ (constant (tick + 1)).val) (rot k 1 key ^^^ u.val)

theorem stateAt_zero (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (key : Nat) :
    stateAt k u constant 0 key = rot k 1 key ^^^ u.val := rfl

theorem stateAt_succ (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (s key : Nat) :
    stateAt k u constant (s + 1) key =
      step k (mix k (stateAt k u constant s key)) ^^^ rot k (2 * s) key ^^^ (constant (s + 1)).val := by
  simp [stateAt, List.range_succ]

theorem rot_lt (k s word : Nat) : rot k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

theorem xor_lt {k a b : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : a ^^^ b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  have hpow := Nat.pow_le_pow_right Nat.zero_lt_two hj
  simp [Nat.testBit_xor, Nat.testBit_lt_two_pow (ha.trans_le hpow),
    Nat.testBit_lt_two_pow (hb.trans_le hpow)]

theorem testBit_rot {k s word b : Nat} (hw : word < 2 ^ k) (hb : b < k) :
    (rot k s word).testBit b = word.testBit ((b + k - s % k) % k) := by
  have hk : 0 < k := by omega
  have hs : s % k < k := Nat.mod_lt _ hk
  simp only [rot, Nat.testBit_mod_two_pow, hb, decide_true, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : s % k ≤ b
  · have hz : word.testBit (k - s % k + b) = false :=
      Nat.testBit_lt_two_pow (hw.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
    have he : (b + k - s % k) % k = b - s % k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, hz, he]
  · have he : (b + k - s % k) % k = k - s % k + b := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, he]

theorem testBit_foldl_or (p : Nat → Bool) (xs : List Nat) (acc i : Nat) :
    (xs.foldl (fun a j => a ||| ((p j).toNat <<< j)) acc).testBit i =
      (acc.testBit i || (decide (i ∈ xs) && p i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons j xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hji : j = i
    · subst j
      cases p i <;> simp
    · by_cases hle : j ≤ i
      · have hsub : 1 ≤ i - j := by omega
        have hbt : (p j).toNat.testBit (i - j) = false := by
          cases p j
          · simp
          · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 1 < 2 ^ 1)
              (Nat.pow_le_pow_right Nat.zero_lt_two hsub))
        simp [hle, hbt, Ne.symm hji]
      · simp [hle, Ne.symm hji]

theorem testBit_step_all (k word b : Nat) :
    (step k word).testBit b = (decide (b < k) && stepBit k word b) := by
  unfold step stepBit
  rw [testBit_foldl_or]
  simp

theorem testBit_step {k word b : Nat} (hb : b < k) :
    (step k word).testBit b = stepBit k word b := by
  simp [testBit_step_all, hb]

theorem step_lt (k word : Nat) : step k word < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro b hb
  simp [testBit_step_all, Nat.not_lt_of_ge hb]

theorem stateAt_lt (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (rounds key : Nat) :
    stateAt k u constant rounds key < 2 ^ k := by
  cases rounds with
  | zero => exact xor_lt (rot_lt k 1 key) u.isLt
  | succ s =>
    rw [stateAt_succ]
    exact xor_lt (xor_lt (step_lt k _) (rot_lt k _ _)) (constant (s + 1)).isLt

theorem testBit_mix {k word b : Nat} (hk : 2 ≤ k) (hw : word < 2 ^ k) (hb : b < k) :
    (mix k word).testBit b =
      xor (xor (word.testBit b) (word.testBit ((b + k - 1) % k)))
        (word.testBit ((b + 1) % k)) := by
  unfold mix
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rot hw hb, testBit_rot hw hb]
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2]
  have h3 : (b + k - (k - 1)) % k = (b + 1) % k := by congr 1; omega
  rw [h3]

theorem mod_sub_eq {k p s : Nat} (hk : 0 < k) (hsp : s ≤ p) :
    (p % k + k - s % k) % k = (p - s) % k := by
  have hdiv : p - s + s = p := Nat.sub_add_cancel hsp
  have h1 : (p % k + k - s % k + s % k) % k = p % k := by
    have hlt : s % k < k := Nat.mod_lt s hk
    have hadd : p % k + k - s % k + s % k = p % k + k := by omega
    rw [hadd, Nat.add_mod_right, Nat.mod_mod]
  have h2 : ((p - s) % k + s % k) % k = p % k := by
    rw [Nat.mod_add_mod, Nat.add_mod_mod, hdiv]
  set A := (p % k + k - s % k) % k
  set B := (p - s) % k
  set C := s % k
  have ha : A < k := Nat.mod_lt _ hk
  have hb : B < k := Nat.mod_lt _ hk
  have hs : C < k := Nat.mod_lt s hk
  have h3 : (A + C) % k = (B + C) % k := by
    rw [Nat.mod_add_mod, h1, ← h2]
  by_cases h1lt : A + C < k <;> by_cases h2lt : B + C < k
  · rw [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_of_lt h2lt] at h3; omega
  · rw [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h3; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h2lt] at h3; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h3; omega

def lineStep (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (src : Nat → Bool) : Nat → Nat → Bool
  | 0, p => src p
  | s + 1, p =>
    let prev := lineStep k u constant src s
    let m0 := xor (xor (prev p) (prev (p - 1))) (prev (p + 1))
    let m1 := xor (xor (prev (p + 1)) (prev p)) (prev (p + 2))
    let m2 := xor (xor (prev (p + 2)) (prev (p + 1))) (prev (p + 3))
    let st := xor m0 (!m1 && m2)
    let inj := xor (src (p + 1 - 2 * s)) (u.val.testBit ((p + 1 - 2 * s) % k))
    xor (xor st inj) ((constant (s + 1)).val.testBit (p % k))

theorem lineStep_succ (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (src : Nat → Bool) (s p : Nat) :
    lineStep k u constant src (s + 1) p =
      xor (xor (xor (xor (xor (lineStep k u constant src s p) (lineStep k u constant src s (p - 1)))
          (lineStep k u constant src s (p + 1)))
        (!(xor (xor (lineStep k u constant src s (p + 1)) (lineStep k u constant src s p))
          (lineStep k u constant src s (p + 2))) &&
         (xor (xor (lineStep k u constant src s (p + 2)) (lineStep k u constant src s (p + 1)))
          (lineStep k u constant src s (p + 3)))))
        (xor (src (p + 1 - 2 * s)) (u.val.testBit ((p + 1 - 2 * s) % k))))
        ((constant (s + 1)).val.testBit (p % k)) := rfl

theorem lineStep_eq_stateAt {k : Nat} (hk : 2 ≤ k) (u : Fin (2 ^ k))
    (constant : Nat → Fin (2 ^ k)) (key : Fin (2 ^ k)) :
    let src := fun pos : Nat => (rot k 1 key.val ^^^ u.val).testBit (pos % k)
    ∀ s p, 2 * s ≤ p → lineStep k u constant src s p = (stateAt k u constant s key.val).testBit (p % k) := by
  intro src s
  have hk_pos : 0 < k := by omega
  induction s with
  | zero => intro p _; rfl
  | succ s ih =>
    intro p hp
    rw [lineStep_succ, stateAt_succ, Nat.testBit_xor, Nat.testBit_xor, testBit_step (Nat.mod_lt p hk_pos)]
    unfold stepBit
    have hm : ∀ d, (mix k (stateAt k u constant s key.val)).testBit ((p % k + d) % k) =
        xor (xor (lineStep k u constant src s (p + d))
                 (lineStep k u constant src s (p + d - 1)))
            (lineStep k u constant src s (p + d + 1)) := by
      intro d
      have hlt : (p % k + d) % k < k := Nat.mod_lt _ hk_pos
      rw [testBit_mix hk (stateAt_lt k u constant s key.val) hlt]
      have h0 : (p % k + d) % k = (p + d) % k := Nat.mod_add_mod p k d
      have h1 : ((p + d) % k + k - 1) % k = (p + d - 1) % k := by
        have h1m : 1 = 1 % k := (Nat.mod_eq_of_lt (by omega)).symm
        conv_lhs => rw [h1m]
        exact mod_sub_eq hk_pos (by omega)
      have h2 : ((p + d) % k + 1) % k = (p + d + 1) % k := Nat.mod_add_mod (p + d) k 1
      rw [h0, h1, h2, ih (p + d) (by omega), ih (p + d - 1) (by omega), ih (p + d + 1) (by omega)]
    have hm0 := hm 0
    simp only [Nat.add_zero, Nat.mod_mod] at hm0
    have hm1 := hm 1
    have hm2 := hm 2
    have he1 : p + 1 - 1 = p := by omega
    have he2 : p + 2 - 1 = p + 1 := by omega
    have he3 : p + 1 + 1 = p + 2 := by omega
    have he4 : p + 2 + 1 = p + 3 := by omega
    rw [he1, he3] at hm1
    rw [he2, he4] at hm2
    rw [hm0, hm1, hm2]
    have hinj : xor (src (p + 1 - 2 * s)) (u.val.testBit ((p + 1 - 2 * s) % k)) =
        (rot k (2 * s) key.val).testBit (p % k) := by
      simp only [src, Nat.testBit_xor]
      have hrot1 : (rot k 1 key.val).testBit ((p + 1 - 2 * s) % k) =
          key.val.testBit ((p - 2 * s) % k) := by
        rw [testBit_rot key.isLt (Nat.mod_lt _ hk_pos)]
        have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
        have hsub : p + 1 - 2 * s - 1 = p - 2 * s := by omega
        rw [← hsub]
        have h1' := mod_sub_eq hk_pos (p := p + 1 - 2 * s) (s := 1) (by omega)
        rw [h1m] at h1' ⊢
        exact congrArg key.val.testBit h1'
      have hrot2 : (rot k (2 * s) key.val).testBit (p % k) =
          key.val.testBit ((p - 2 * s) % k) := by
        rw [testBit_rot key.isLt (Nat.mod_lt _ hk_pos), mod_sub_eq hk_pos (by omega)]
      rw [hrot1, hrot2]
      cases key.val.testBit ((p - 2 * s) % k) <;> cases u.val.testBit ((p + 1 - 2 * s) % k) <;> rfl
    rw [hinj]

theorem lineStep_agree_interval (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (f g : Nat → Bool) (lo hi : Nat) (hfg : ∀ p, lo ≤ p → p ≤ hi → f p = g p) :
    ∀ s p, max (lo + s) (lo + 2 * s - 3) ≤ p → p + 3 * s ≤ hi →
      lineStep k u constant f s p = lineStep k u constant g s p := by
  intro s
  induction s with
  | zero =>
    intro p h1 h2
    exact hfg p (by omega) (by omega)
  | succ s ih =>
    intro p h1 h2
    rw [lineStep_succ k u constant f s p, lineStep_succ k u constant g s p]
    have h0 := ih (p - 1) (by omega) (by omega)
    have h1' := ih p (by omega) (by omega)
    have h2' := ih (p + 1) (by omega) (by omega)
    have h3 := ih (p + 2) (by omega) (by omega)
    have h4 := ih (p + 3) (by omega) (by omega)
    have hi' := hfg (p + 1 - 2 * s) (by omega) (by omega)
    rw [h0, h1', h2', h3, h4, hi']

theorem lineStep_xor_pivot (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (f g : Nat → Bool) (s p : Nat) (hs : 4 ≤ s) (hp : 2 * s ≤ p)
    (hfg : ∀ q, p + 4 - 2 * s ≤ q → q ≤ p + 3 * s → f q = g q) :
    xor (lineStep k u constant f s p) (lineStep k u constant g s p) =
      xor (f (p + 3 - 2 * s)) (g (p + 3 - 2 * s)) := by
  have hs_eq : s = (s - 1) + 1 := by omega
  conv_lhs => rw [hs_eq, lineStep_succ k u constant f (s - 1) p, lineStep_succ k u constant g (s - 1) p]
  have h0 := lineStep_agree_interval k u constant f g (p + 4 - 2 * s) (p + 3 * s) hfg (s - 1) (p - 1) (by omega) (by omega)
  have h1 := lineStep_agree_interval k u constant f g (p + 4 - 2 * s) (p + 3 * s) hfg (s - 1) p (by omega) (by omega)
  have h2 := lineStep_agree_interval k u constant f g (p + 4 - 2 * s) (p + 3 * s) hfg (s - 1) (p + 1) (by omega) (by omega)
  have h3 := lineStep_agree_interval k u constant f g (p + 4 - 2 * s) (p + 3 * s) hfg (s - 1) (p + 2) (by omega) (by omega)
  have h4 := lineStep_agree_interval k u constant f g (p + 4 - 2 * s) (p + 3 * s) hfg (s - 1) (p + 3) (by omega) (by omega)
  have hidx : p + 1 - 2 * (s - 1) = p + 3 - 2 * s := by omega
  rw [h0, h1, h2, h3, h4, hidx]
  cases lineStep k u constant g (s - 1) (p - 1) <;>
  cases lineStep k u constant g (s - 1) p <;>
  cases lineStep k u constant g (s - 1) (p + 1) <;>
  cases lineStep k u constant g (s - 1) (p + 2) <;>
  cases lineStep k u constant g (s - 1) (p + 3) <;>
  cases u.val.testBit ((p + 3 - 2 * s) % k) <;>
  cases (constant (s - 1 + 1)).val.testBit (p % k) <;>
  cases f (p + 3 - 2 * s) <;>
  cases g (p + 3 - 2 * s) <;> rfl

def lInj {k : Nat} (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k)) (f : Nat → Bool) (t p : Nat) :=
  xor (xor (f (p + 3 - 2*t)) (u.val.testBit ((p+3-2*t) % k))) ((c t).val.testBit (p % k))
def lGuard {k : Nat} (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k)) (f : Nat → Bool) (t e : Nat) :=
  xor (xor (lineStep k u c f t (e-2)) (lineStep k u c f t (e-1))) (lineStep k u c f t e)
def lNear {k : Nat} (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k)) (f : Nat → Bool) (t e : Nat) :=
  lineStep k u c f t (e-2) == xor (lInj u c f t (e-1)) (lInj u c f t e)
def lFar {k : Nat} (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k)) (f : Nat → Bool) (t e : Nat) :=
  lineStep k u c f t (e-3) == lInj u c f t e
def lBranch {k : Nat} (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k)) (f : Nat → Bool) (t e : Nat) :=
  let b := lGuard u c f (t-1) e
  let next := lGuard u c f t (e-3+b.toNat)
  if b then 2+(lNear u c f t e).toNat+2*(lFar u c f t e).toNat+4*next.toNat else next.toNat
def gain (v : Nat) := if v<2 then v else 1+(v-2)/4+(if v=9 then 1 else 0)
def lTrace {k : Nat} (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k)) (f : Nat → Bool) (q len : Nat) :=
  (List.range len).foldl (fun (acc : Nat × Nat) j =>
    let v := lBranch u c f (5+2*j) acc.1
    (acc.1-6+gain v,acc.2+v*10^j)) (q-13,0)
end PEqualNP.Outside.L_meta_25539_aux.Line

namespace PEqualNP.Outside.L_meta_25539_aux.Line

def src {k : Nat} (u : Fin (2^k)) (key n : Nat) := (rot k 1 key ^^^ u.val).testBit (n % k)
def vary {k : Nat} (base : Fin (2^k)) (lo m : Nat) := base.val ^^^ rot k (lo+k-1) m
def cut (q : Nat) (f : Nat → Bool) (n : Nat) := if n<q then f n else false

theorem vary_lt {k : Nat} (base : Fin (2^k)) (lo m : Nat) : vary base lo m < 2^k :=
  xor_lt base.isLt (rot_lt _ _ _)

theorem src_vary {k q lo n : Nat} (hk : 6≤k) (hl : 0<lo) (hn : lo≤n) (hnq : n<q) (hq : q≤lo+k)
    (u base : Fin (2^k)) (m : Fin 64) :
    src u (vary base lo m.val) n = xor (src u base.val n) (m.val.testBit (n-lo)) := by
  have hpos : 0<k := by omega
  have hm : m.val < 2^k := m.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hk)
  have hone : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have hdiff : (n % k+k-1 % k)%k=(n-1)%k := mod_sub_eq hpos (by omega)
  have hshift : ((n-1)%k+k-(lo+k-1)%k)%k=n-lo := by
    have hc := mod_sub_eq (k:=k) (p:=n-1+k) (s:=lo+k-1) hpos (by omega)
    rw [Nat.add_mod_right, show n-1+k-(lo+k-1)=n-lo by omega, Nat.mod_eq_of_lt (by omega : n-lo<k)] at hc
    exact hc
  simp only [src,Nat.testBit_xor]
  rw [testBit_rot (vary_lt base lo m.val) (Nat.mod_lt _ hpos),testBit_rot base.isLt (Nat.mod_lt _ hpos),hdiff]
  simp only [vary,Nat.testBit_xor,testBit_rot hm (Nat.mod_lt _ hpos),hshift]
  generalize base.val.testBit ((n-1)%k) = a
  generalize m.val.testBit (n-lo) = b
  generalize u.val.testBit (n % k) = z
  cases a <;> cases b <;> cases z <;> rfl

theorem cut_tri {k q lo d : Nat} (hk : 6≤k) (hl : 0<lo) (hdq : lo+d<q) (hq : q≤lo+k)
    (u base : Fin (2^k)) (m n : Fin 64)
    (ag : ∀ j, d<j → j<6 → m.val.testBit j=n.val.testBit j) :
    let f := cut q (src u (vary base lo m.val))
    let g := cut q (src u (vary base lo n.val))
    (∀ p, lo+d<p → f p=g p) ∧ xor (f (lo+d)) (g (lo+d)) = xor (m.val.testBit d) (n.val.testBit d) := by
  dsimp only
  constructor
  · intro p hp
    by_cases h : p<q
    · simp only [cut,ite_eq_left h,src_vary hk hl (by omega : lo≤p) h hq]
      by_cases hj : p-lo<6
      · rw [ag _ (by omega) hj]
      · have hm : ∀ a : Fin 64, a.val.testBit (p-lo)=false := fun a =>
          Nat.testBit_lt_two_pow (a.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega : 6≤p-lo)))
        rw [hm m,hm n]
    · simp [cut,h]
  · simp only [cut,ite_eq_left hdq,src_vary hk hl (by omega : lo≤lo+d) hdq hq, Nat.add_sub_cancel_left]
    generalize src u base.val (lo+d)=x
    cases x <;> cases m.val.testBit d <;> cases n.val.testBit d <;> rfl

theorem gPivot {k s e : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (f g : Nat → Bool)
    (hs : 4≤s) (he : 2*s+2≤e)
    (ag : ∀j, e+1-2*s<j → f j=g j) :
    xor (lGuard u c f s e) (lGuard u c g s e) =
      xor (f (e+1-2*s)) (g (e+1-2*s)) := by
  have h₂ := lineStep_xor_pivot k u c f g s (e-2) hs (by omega) (fun j hj _ => ag _ (by omega))
  have hv : e-2+3-2*s=e+1-2*s := by omega
  rw [hv] at h₂
  have eqat (p : Nat) (h : e-1≤p) : lineStep k u c f s p=lineStep k u c g s p :=
    lineStep_agree_interval k u c f g (e+2-2*s) (p+3*s) (fun j hj _ => ag _ (by omega)) s p (by omega) (by omega)
  unfold lGuard
  rw [eqat (e-1) (by omega),eqat e (by omega),← h₂]
  generalize lineStep k u c f s (e-2)=a
  generalize lineStep k u c g s (e-2)=b
  generalize lineStep k u c g s (e-1)=z
  generalize lineStep k u c g s e=w
  cases a <;> cases b <;> cases z <;> cases w <;> rfl

theorem alignPivot {k t e : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (f g : Nat → Bool)
    (ht : 5≤t) (he : 2*t+3≤e) (b : Bool) :
    let d := if b then 2 else 3
    let V := if b then lNear u c else lFar u c
    (∀j, e+3-d-2*t<j → f j=g j) →
    xor (V f t e) (V g t e) = xor (f (e+3-d-2*t)) (g (e+3-d-2*t)) := by
  dsimp only
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> intro ag
  · have h := lineStep_xor_pivot k u c f g t (e-3) (by omega) (by omega) (fun j hj _ => ag _ (by omega))
    rw [show e-3+3-2*t=e+3-3-2*t by omega] at h
    unfold lFar lInj
    rw [ag (e+3-2*t) (by omega),←h]
    generalize lineStep k u c f t (e-3)=a
    generalize lineStep k u c g t (e-3)=b
    generalize xor (xor (g (e+3-2*t)) (u.val.testBit ((e+3-2*t)%k))) ((c t).val.testBit (e % k))=z
    cases a <;> cases b <;> cases z <;> rfl
  · have h := lineStep_xor_pivot k u c f g t (e-2) (by omega) (by omega) (fun j hj _ => ag _ (by omega))
    rw [show e-2+3-2*t=e+3-2-2*t by omega] at h
    unfold lNear lInj
    rw [ag (e+3-2*t) (by omega),ag (e-1+3-2*t) (by omega),←h]
    generalize lineStep k u c f t (e-2)=a
    generalize lineStep k u c g t (e-2)=b
    generalize xor (xor (xor (g (e-1+3-2*t)) (u.val.testBit ((e-1+3-2*t)%k))) ((c t).val.testBit ((e-1)%k))) (xor (xor (g (e+3-2*t)) (u.val.testBit ((e+3-2*t)%k))) ((c t).val.testBit (e % k)))=z
    cases a <;> cases b <;> cases z <;> rfl

end PEqualNP.Outside.L_meta_25539_aux.Line

namespace PEqualNP.Outside.L_meta_25539_aux.Line

theorem lTrace_succ {k : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (f : Nat→Bool) (q j : Nat) :
  lTrace u c f q (j+1) =
    let z := lTrace u c f q j
    let v := lBranch u c f (5+2*j) z.1
    (z.1-6+gain v,z.2+v*10^j) := by simp [lTrace,List.range_succ]

theorem branch_gain {k : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (f : Nat→Bool) (t e : Nat) :
    gain (lBranch u c f t e) ≤ 3 := by
  have h : ∀ b n f y : Bool, gain (if b then 2+n.toNat+2*f.toNat+4*y.toNat else y.toNat)≤3 := by decide
  exact h ..
theorem trace_bounds {k : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (f : Nat→Bool) (q j : Nat)
    (big : 10*j+35≤q) : q-13-6*j ≤ (lTrace u c f q j).1 ∧ (lTrace u c f q j).1 ≤ q-13 := by
  induction j with
  | zero => simp [lTrace]
  | succ j ih =>
    obtain ⟨lb,ub⟩ := ih (by omega)
    have gd := branch_gain u c f (5+2*j) (lTrace u c f q j).1
    rw [lTrace_succ]
    dsimp only
    omega

theorem branchLeft {k t e : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (f g : Nat→Bool)
    (ht : 5≤t) (he : 2*t+6≤e) (ag : ∀n, e-(2*t+2)≤n → f n=g n) :
    lBranch u c f t e=lBranch u c g t e := by
  have bitEq (s j : Nat) (hs : 4≤s) (hj : e-(2*t+2)+2*s-3≤j) :
      lineStep k u c f s j = lineStep k u c g s j :=
    lineStep_agree_interval k u c f g (e-(2*t+2)) (j+3*s) (fun n hn _ => ag _ hn) s j (by omega) (by omega)
  have guardEq (s j : Nat) (hs : 4≤s) (hj : e-(2*t+2)+2*s-1≤j) :
      lGuard u c f s j=lGuard u c g s j := by
    unfold lGuard
    rw [bitEq _ _ hs (by omega),bitEq _ _ hs (by omega),bitEq _ _ hs (by omega)]
  have injEq (j : Nat) (hj : e-1≤j) : lInj u c f t j=lInj u c g t j := by
    unfold lInj
    rw [ag _ (by omega)]
  have nearEq : lNear u c f t e=lNear u c g t e := by
    unfold lNear
    rw [bitEq _ _ (by omega) (by omega),injEq (e-1) (by omega),injEq e (by omega)]
  have farEq : lFar u c f t e=lFar u c g t e := by
    unfold lFar
    rw [bitEq _ _ (by omega) (by omega),injEq e (by omega)]
  unfold lBranch
  rw [guardEq (t-1) e (by omega) (by omega),nearEq,farEq]
  cases lGuard u c g (t-1) e <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> rw [guardEq t _ (by omega) (by omega)]

theorem histLeft {k : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (f g : Nat→Bool) (q p : Nat)
    (big : 10*p+35≤q) (ag : ∀n, (lTrace u c f q p).1-(2*(5+2*p)+2)+6≤n → f n=g n) :
    lTrace u c f q p=lTrace u c g q p := by
  induction p with
  | zero => rfl
  | succ p ih =>
    have lb := (trace_bounds u c f q p (by omega)).1
    have gd := branch_gain u c f (5+2*p) (lTrace u c f q p).1
    rw [lTrace_succ] at ag ⊢
    dsimp only at ag ⊢
    have old := ih (by omega) (fun n hn => ag n (by omega))
    have bb := branchLeft u c f g (t:=5+2*p) (e:=(lTrace u c f q p).1) (by omega) (by omega)
      (fun n hn => ag n (by omega))
    rw [lTrace_succ u c g,←old,bb]

end PEqualNP.Outside.L_meta_25539_aux.Line

namespace PEqualNP.Outside.L_meta_25539_aux.Line

def rawBit {k : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (t key n : Nat) :=
  (stateAt k u c t key).testBit (n % k)
def rawInj {k : Nat} (c : Nat→Fin (2^k)) (t key n : Nat) :=
  xor ((rot k (2*(t-1)) key).testBit (n % k)) ((c t).val.testBit (n % k))
def rawGuard {k : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (t key e : Nat) :=
  xor (xor (rawBit u c t key (e-2)) (rawBit u c t key (e-1))) (rawBit u c t key e)
def rawB {k : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (t e key : Nat) :=
  let h := rawGuard u c (t-1) key e
  let close := rawGuard u c t key (e-3+h.toNat)
  if h then
    let near := rawBit u c t key (e-2) == xor (rawInj c t key (e-1)) (rawInj c t key e)
    let far := rawBit u c t key (e-3) == rawInj c t key e
    2+near.toNat+2*far.toNat+4*close.toNat
  else close.toNat
def rawT {k : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (q len key : Nat) :=
  (List.range len).foldl (fun (acc : Nat × Nat) j =>
    let v := rawB u c (5+2*j) acc.1 key
    (acc.1-6+gain v,acc.2+v*10^j)) (q-13,0)

theorem injRaw {k t p key : Nat} (hk : 6≤k) (ht : 1≤t) (hp : 2*t≤p) (hw : key<2^k)
    (u : Fin (2^k)) (c : Nat→Fin (2^k)) :
    lInj u c (src u key) t p=rawInj c t key p := by
  have pos : 0<k := by omega
  have h1 := mod_sub_eq (k:=k) (s:=1) (p:=p+3-2*t) pos (by omega)
  have h2 := mod_sub_eq (k:=k) (s:=2*(t-1)) (p:=p) pos (by omega)
  have ha : p+3-2*t-1=p-2*(t-1) := by omega
  simp only [lInj,rawInj,src,Nat.testBit_xor,testBit_rot hw (Nat.mod_lt _ pos),h1,h2,ha]
  cases key.testBit ((p-2*(t-1))%k) <;> cases u.val.testBit ((p+3-2*t)%k) <;>
    cases (c t).val.testBit (p % k) <;> rfl

theorem branchRaw {k t e key : Nat} (hk : 6≤k) (ht : 5≤t) (he : 2*t+6≤e) (hw : key<2^k)
    (u : Fin (2^k)) (c : Nat→Fin (2^k)) :
    lBranch u c (src u key) t e=rawB u c t e key := by
  have bitEq (s j : Nat) (h : 2*s≤j) :
      lineStep k u c (src u key) s j=rawBit u c s key j :=
    lineStep_eq_stateAt (by omega) u c ⟨key,hw⟩ s j h
  have geq (s j : Nat) (h : 2*s+2≤j) : lGuard u c (src u key) s j=rawGuard u c s key j := by
    unfold lGuard rawGuard
    rw [bitEq _ _ (by omega),bitEq _ _ (by omega),bitEq _ _ (by omega)]
  unfold lBranch rawB lNear lFar
  rw [geq (t-1) e (by omega),bitEq t (e-2) (by omega),bitEq t (e-3) (by omega),
    injRaw hk (by omega) (by omega) hw,injRaw hk (by omega) (by omega) hw]
  cases rawGuard u c (t-1) key e <;> simp only [Bool.toNat_false,Bool.toNat_true] <;>
    rw [geq _ _ (by omega)]

theorem traceRaw {k q key : Nat} (hk : 6≤k) (hw : key<2^k) (u : Fin (2^k)) (c : Nat→Fin (2^k))
    (p : Nat) (hbig : 10*p+35≤q) : lTrace u c (src u key) q p=rawT u c q p key := by
  induction p with
  | zero => rfl
  | succ j ih =>
    have bound := (trace_bounds u c (src u key) q j (by omega)).1
    have h := ih (by omega)
    have hs : rawT u c q (j+1) key =
      let z := rawT u c q j key
      let v := rawB u c (5+2*j) z.1 key
      (z.1-6+gain v,z.2+v*10^j) := by simp [rawT,List.range_succ]
    rw [lTrace_succ,hs,←h]
    dsimp only
    rw [branchRaw hk (by omega) (by omega) hw]

end PEqualNP.Outside.L_meta_25539_aux.Line

namespace PEqualNP.Outside.L_meta_25539_aux.Line
namespace Right
variable {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k))
abbrev Src := Nat → Bool
def tri (a b d : Bool) := xor (xor a b) d
def grd (y : Src) (e : Nat) := tri (y (e-2)) (y (e-1)) (y e)
def cell (y : Src) (j : Nat → Bool) (p : Nat) :=
  xor (xor (tri (y (p-1)) (y p) (y (p+1)))
    (!(tri (y p) (y (p+1)) (y (p+2))) && tri (y (p+1)) (y (p+2)) (y (p+3)))) (j p)
lemma norm (a b d e f j v : Bool) :
    xor (xor (xor (xor (xor b a) d) (!(xor (xor d b) e) && xor (xor e d) f)) j) v =
    xor (xor (tri a b d) (!(tri b d e) && tri d e f)) (xor j v) := by
  cases a <;> cases b <;> cases d <;> cases e <;> cases f <;> cases j <;> cases v <;> decide
lemma stepEq (f : Src) (s p : Nat) :
    lineStep k u c f (s+1) p = cell (lineStep k u c f s) (lInj u c f (s+1)) p := by
  unfold cell lInj
  rw [show p+3-2*(s+1)=p+1-2*s by omega]
  exact norm ..
def PrefixEq (f g : Src) (e : Nat) := ∀ i, i≤e → f i=g i
lemma guardEq {f g : Src} {e : Nat} (h : PrefixEq f g e) : grd f e = grd g e := by
  unfold grd;rw [h _ (by omega),h _ (by omega),h _ (by omega)]
lemma move {f g a b : Src} {e : Nat} (lo : 6≤e) (h : PrefixEq f g e) (j : PrefixEq a b e) :
    PrefixEq (cell f a) (cell g b) (e-3+(grd f e).toNat) := by
  intro p hp
  by_cases le : p+3≤e
  · unfold cell;rw [h _ (by omega),h _ (by omega),h _ (by omega),h _ (by omega),h _ (by omega),j _ (by omega)]
  · cases hit : grd f e with
    | false => simp [hit] at hp;omega
    | true =>
      simp [hit] at hp
      have mid : tri (f p) (f (p+1)) (f (p+2))=true := by
        unfold grd at hit
        rw [show e-2=p by omega,show e-1=p+1 by omega] at hit
        rwa [show p+2=e by omega]
      have eq := guardEq h
      have midg : tri (g p) (g (p+1)) (g (p+2))=true := by rwa [←h _ (by omega),←h _ (by omega),←h _ (by omega)]
      simp only [cell,mid,midg,Bool.not_true,Bool.false_and,Bool.xor_false]
      rw [h _ (by omega),h _ (by omega),h _ (by omega),j _ (by omega)]
lemma special (x y z a b : Bool) :
    let q := xor (xor true (!x && y)) a
    let r := xor (xor x (!y && z)) b
    (!(tri b (xor a b) q) && tri (xor a b) q r) = false := by
  cases x <;> cases y <;> cases z <;> cases a <;> cases b <;> decide

lemma bonus (f j : Src) {e : Nat} (he : 6≤e) (hit : grd f e=true)
    (near : cell f j (e-2) = xor (j (e-1)) (j e)) (far : cell f j (e-3)=j e) :
    (!(tri (cell f j (e-3)) (cell f j (e-2)) (cell f j (e-1))) &&
      tri (cell f j (e-2)) (cell f j (e-1)) (cell f j e)) = false := by
  rw [near,far]
  simp only [cell,show e-1-1=e-2 by omega,show e-1+1=e by omega,
    show e-1+2=e+1 by omega,show e-1+3=e+2 by omega]
  change tri (f (e-2)) (f (e-1)) (f e)=true at hit
  rw [hit]
  exact special ..

end Right
end PEqualNP.Outside.L_meta_25539_aux.Line

namespace PEqualNP.Outside.L_meta_25539_aux.Line.Right
def letter (f a : Src) (e : Nat) :=
  let y := cell f a
  let h := grd f e
  let extra := grd y (e-3+h.toNat)
  if h then 2+(y (e-2)==xor (a (e-1)) (a e)).toNat+2*(y (e-3)==a e).toNat+4*extra.toNat
  else extra.toNat

lemma grow {f g a b j l : Src} {e : Nat} (he : 12≤e)
    (h : PrefixEq f g e) (ha : PrefixEq a b e) (hj : PrefixEq j l e) :
    letter f a e=letter g b e ∧
    PrefixEq (cell (cell f a) j) (cell (cell g b) l) (e-6+gain (letter f a e)) := by
  let y := cell f a
  let z := cell g b
  let mid := e-3+(grd f e).toNat
  have ma : PrefixEq y z mid := move (by omega) h ha
  have hmid : 6≤mid ∧ mid≤e := by dsimp [mid];cases grd f e <;> simp <;> omega
  have step2 := move hmid.1 ma (show PrefixEq j l mid from fun n hn => hj n (by omega))
  have eq0 := guardEq h
  have eq1 := guardEq ma
  cases hit : grd f e with
  | false =>
    have eqm : mid=e-3 := by simp [mid,hit]
    simp only [letter,hit,←eq0,Bool.false_eq_true,ite_false,Bool.toNat_false,Nat.add_zero]
    change (grd y (e-3)).toNat = (grd z (e-3)).toNat ∧ _
    have e1 : grd y (e-3)=grd z (e-3) := by simpa [eqm] using eq1
    refine ⟨congrArg Bool.toNat e1,?_⟩
    change PrefixEq _ _ (e-6+gain (grd y (e-3)).toNat)
    rw [eqm] at step2
    cases eh : grd y (e-3) <;> simpa [gain,eh,Nat.sub_sub] using step2
  | true =>
    have eqm : mid=e-2 := by simp [mid,hit];omega
    have nearEq : (y (e-2)==xor (a (e-1)) (a e)) = (z (e-2)==xor (b (e-1)) (b e)) := by
      rw [ma _ (by omega),ha _ (by omega),ha _ (by omega)]
    have farEq : (y (e-3)==a e)=(z (e-3)==b e) := by rw [ma _ (by omega),ha _ (by omega)]
    have e1 : grd y mid=grd z mid := eq1
    have letterA : letter f a e=2+(y (e-2)==xor (a (e-1)) (a e)).toNat+2*(y (e-3)==a e).toNat+4*(grd y mid).toNat := by simp [letter,hit,mid,y]
    have letterB : letter g b e=2+(z (e-2)==xor (b (e-1)) (b e)).toNat+2*(z (e-3)==b e).toNat+4*(grd z mid).toNat := by simp [letter,←eq0,hit,mid,z]
    refine ⟨by rw [letterA,letterB,nearEq,farEq,e1],?_⟩
    intro p hp
    by_cases sub : p≤mid-3+(grd y mid).toNat
    · exact step2 p sub
    · rw [letterA] at hp
      cases ne : (y (e-2)==xor (a (e-1)) (a e)) <;>
        cases fe : (y (e-3)==a e) <;> cases en : grd y mid <;>
        simp [ne,fe,en,gain] at hp sub <;> try omega
      have ep : p=e-3 := by omega
      subst p
      have fA := bonus f a (e:=e) (by omega) hit (beq_iff_eq.mp ne) (beq_iff_eq.mp fe)
      have fB := bonus g b (e:=e) (by omega) (eq0.symm.trans hit)
        (beq_iff_eq.mp (nearEq.symm.trans ne)) (beq_iff_eq.mp (farEq.symm.trans fe))
      change cell y j (e-3)=cell z l (e-3)
      unfold cell
      simp only [show e-3+1=e-2 by omega,show e-3+2=e-1 by omega,show e-3+3=e by omega]
      change (!tri (y (e-3)) (y (e-2)) (y (e-1)) && tri (y (e-2)) (y (e-1)) (y e))=false at fA
      change (!tri (z (e-3)) (z (e-2)) (z (e-1)) && tri (z (e-2)) (z (e-1)) (z e))=false at fB
      rw [fA,fB,ma (e-3-1) (by omega), ma (e-3) (by omega),ma (e-2) (by omega),hj _ (by omega)]
end PEqualNP.Outside.L_meta_25539_aux.Line.Right

namespace PEqualNP.Outside.L_meta_25539_aux
open PEqualNP.Outside.L_meta_25539_aux.Line

def delta (letter : Nat) :=
  (letter.testBit 0).toNat + (letter.testBit 3).toNat + ((letter % 16) == 15).toNat
def digit (v j : Nat) := (v >>> (4*j))%16
def gain (v n : Nat) := ((List.range n).map (fun j => delta (digit v j))).sum
def edge (q v j : Nat) := q-13-6*j+gain v j
def tick (j : Nat) := 5+2*j
def left (q v j : Nat) := edge q v j+3-2*tick j

def rawBit {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (w s p : Nat) :=
  (stateAt k u c s w).testBit (p % k)
def inj {k : Nat} (c : Nat → Fin (2^k)) (w s p : Nat) :=
  xor ((rot k (2*(s-1)) w).testBit (p % k)) ((c s).val.testBit (p % k))
def par {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (w t p : Nat) :=
  xor (xor (rawBit u c w t (p-2)) (rawBit u c w t (p-1))) (rawBit u c w t p)

def src {k : Nat} (u : Fin (2^k)) (w : Nat) := rot k 1 w ^^^ u.val
def rawDigit {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (w t e : Nat) :=
  let l := e+3-2*t
  let h := par u c w (t-1) e
  let b := if h then rawBit u c w t (e-2) == xor (inj c w t (e-1)) (inj c w t e)
    else (src u w).testBit ((l-2)%k)
  let a := if h then rawBit u c w t (e-3) == inj c w t e
    else (src u w).testBit ((l-3)%k)
  let n := par u c w t (e-3+h.toNat)
  h.toNat+2*b.toNat+4*a.toNat+8*n.toNat

def trace {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (q w a : Nat) :=
  (List.range a).foldl (fun (st : Nat×Nat) j =>
    let val:=rawDigit u c w (tick j) (q-13-6*j+st.1)
    (st.1+delta val,st.2 ||| (val <<< (4*j)))) (0,0)

lemma gainSucc (v n : Nat) : gain v (n+1)=gain v n+delta (digit v n) := by simp [gain,List.range_succ]
lemma gainBound (v : Nat) : ∀ n, gain v n ≤ 3*n := by
  intro n
  induction n with
  | zero => simp [gain]
  | succ n ih =>
    rw [gainSucc,Nat.mul_succ]
    unfold delta
    have := Bool.toNat_le ((digit v n).testBit 0)
    have := Bool.toNat_le ((digit v n).testBit 3)
    have := Bool.toNat_le ((digit v n % 16) == 15)
    omega

lemma digitLt (v j : Nat) : digit v j < 16 := Nat.mod_lt _ (by decide)
lemma rawDigitLt {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (w t e : Nat) :
    rawDigit u c w t e < 16 := by
  exact (show ∀ h b a n : Bool, h.toNat+2*b.toNat+4*a.toNat+8*n.toNat<16 by decide) _ _ _ _
lemma orPack {v j d : Nat} (hv : v < 16^j) :
    v ||| (d <<< (4*j)) = v + d*(16^j) := by
  rw [Nat.shiftLeft_eq]
  have power : 2^(4*j)=16^j := by rw [pow_mul]; rfl
  rw [power,Nat.add_comm,Nat.mul_comm d]
  rw [show 16^j=2^(4*j) by exact power.symm]
  rw [Nat.two_pow_add_eq_or_of_lt (by simpa only [power] using hv) d,Nat.or_comm]

lemma digDiv (v j : Nat) : digit v j = (v / 16^j)%16 := by
  rw [digit,Nat.shiftRight_eq_div_pow, pow_mul];rfl
lemma digAddSmall {v j n : Nat} (h : j<n) (z : Nat) :
    digit (v+z*16^n) j=digit v j := by
  rw [digDiv,digDiv]
  obtain ⟨d,rfl⟩ : ∃ d, n=(j+1)+d := ⟨n-(j+1),by omega⟩
  rw [pow_add,pow_succ]
  have eq : z*(16^j*16*16^d)=16^j*(16*(z*16^d)) := by ring
  rw [eq,Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

lemma digLast {v j : Nat} (hv : v<16^j) (z : Nat) (hz:z<16) :
    digit (v+z*16^j) j=z := by
  rw [digDiv,Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hv,Nat.zero_add,Nat.mod_eq_of_lt hz]

lemma traceSucc {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (q w a : Nat) :
    trace u c q w (a+1) =
      let prev:=trace u c q w a
      let val:=rawDigit u c w (tick a) (q-13-6*a+prev.1)
      (prev.1+delta val, prev.2 ||| (val <<< (4*a))) := by
  simp only [trace,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]

lemma normalized {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (q w a : Nat) :
    let t:=trace u c q w a
    t.2 < 16^a ∧ t.1=gain t.2 a ∧
      ∀ j < a, rawDigit u c w (tick j) (edge q t.2 j)=digit t.2 j := by
  induction a with
  | zero => simp [trace,gain]
  | succ n ih =>
    let t := trace u c q w n
    let d := rawDigit u c w (tick n) (q-13-6*n+t.1)
    have hd : d<16 := rawDigitLt .. 
    have hv : t.2 < 16^n := ih.1
    let v := t.2 + d*16^n
    have pre (j : Nat) (hj : j≤n) : gain v j=gain t.2 j := by
      unfold gain
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [digAddSmall (List.mem_range.mp hi |>.trans_le hj)]
    have last : digit v n = d := digLast hv d hd
    rw [traceSucc]
    change (t.2 ||| (d <<< (4*n))) < 16^(n+1) ∧ t.1+delta d=gain (t.2 ||| (d <<< (4*n))) (n+1) ∧ ∀ j<n+1,rawDigit u c w (tick j) (edge q (t.2 ||| (d <<< (4*n))) j)=digit (t.2 ||| (d <<< (4*n))) j
    rw [orPack hv]
    change v < 16^(n+1) ∧ t.1+delta d=gain v (n+1) ∧ _
    refine ⟨?_,by rw [gainSucc,pre n (by omega),last,ih.2.1],?_⟩
    · have h := Nat.mul_le_mul_right (16^n) (show d+1 ≤ 16 by omega)
      dsimp [v]; rw [pow_succ]; simp only [Nat.add_mul,Nat.one_mul] at h; omega
    · intro j hj
      by_cases he : j=n
      · subst j
        rw [last]
        unfold edge
        rw [pre n (by omega),←ih.2.1]
      · change rawDigit u c w (tick j) (q-13-6*j+gain v j)=digit v j
        rw [pre j (by omega),show digit v j=digit t.2 j by exact digAddSmall (by omega) d]
        exact ih.2.2 j (by omega)

lemma traceIff {k a v : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (q w : Nat) (hv : v<16^a) :
    (trace u c q w a).2=v ↔ ∀ j<a, rawDigit u c w (tick j) (edge q v j)=digit v j := by
  constructor
  · intro h
    simpa only [h] using (normalized u c q w a).2.2
  · intro good
    have aux (n : Nat) (hn : n≤a) :
        trace u c q w n = (gain v n, v % 16^n) := by
      induction n with
      | zero => simp [gain,trace,Nat.mod_one]
      | succ n ih =>
        rw [traceSucc,ih (by omega)]
        change (gain v n+delta (rawDigit u c w (tick n) (edge q v n)),
          v % 16^n ||| (rawDigit u c w (tick n) (edge q v n) <<< (4*n))) = _
        rw [good n (by omega), gainSucc, orPack (Nat.mod_lt _ (by positivity)),
          pow_succ, Nat.mod_mul,digDiv (v:=v) (j:=n)]
        rw [Nat.mul_comm (v / 16 ^ n % 16)]
    rw [aux a (by omega),Nat.mod_eq_of_lt hv]

end PEqualNP.Outside.L_meta_25539_aux

namespace PEqualNP.Outside.L_meta_25539_aux
namespace Solver

abbrev W (k : Nat) := Fin (2^k)
def flip {k : Nat} (x : W k) (p : Fin k) : W k :=
  ⟨x.val ^^^ (1 <<< p.val), Nat.xor_lt_two_pow x.isLt (by
    rw [Nat.one_shiftLeft]; exact Nat.pow_lt_pow_right (by decide) p.isLt)⟩
lemma flipBit {k : Nat} (x : W k) (p : Fin k) (j : Nat) :
    (flip x p).val.testBit j=xor (x.val.testBit j) (decide (p.val=j)) := by
  simp [flip,Nat.testBit_xor,Nat.one_shiftLeft,Nat.testBit_two_pow]

def put {k : Nat} (p : Nat → Fin k) (F : Nat → W k → Bool) (j : Nat) (x : W k) :=
  if F j x then flip x (p j) else x
def run {k : Nat} (p : Nat → Fin k) (F : Nat → W k → Bool) (seed : W k) : Nat → W k
  | 0 => seed
  | n+1 => put p F n (run p F seed n)
def Good {k : Nat} (F : Nat → W k → Bool) (n : Nat) (v : W k) := ∀ j<n, F j v=false
def Future {k : Nat} (p : Nat → Fin k) (n len : Nat) (j : Nat) := ∃ z, n≤z ∧ z<len ∧ (p z).val=j

theorem certified {k l : Nat} (p : Nat → Fin k) (F : Nat → W k → Bool) (seed : W k)
    (distinct : ∀ j<l, ∀ t<l, p j=p t → j=t)
    (tri : ∀ j<l, ∀ x y, Good F j x → Good F j y →
      (∀ b : Fin k, ¬Future p j l b.val → x.val.testBit b.val=y.val.testBit b.val) →
      xor (F j x) (x.val.testBit (p j).val)=xor (F j y) (y.val.testBit (p j).val)) :
    ∀ target, target=run p F seed l ↔ Good F l target ∧
      ∀ b:Fin k, ¬Future p 0 l b.val → target.val.testBit b.val=seed.val.testBit b.val := by
  have invariant (n : Nat) (hn : n≤l) : Good F n (run p F seed n) ∧
      (∀ b:Fin k, ¬Future p 0 n b.val →
        (run p F seed n).val.testBit b.val=seed.val.testBit b.val) ∧
      (∀ y, Good F n y →
        (∀ b:Fin k, ¬Future p 0 l b.val → y.val.testBit b.val=seed.val.testBit b.val) →
        ∀ b:Fin k, ¬Future p n l b.val →
          y.val.testBit b.val=(run p F seed n).val.testBit b.val) := by
    have stable (n : Nat) (hn : n≤l) (x y : W k) (gx : Good F n x)
        (same : ∀ b : Fin k, ¬Future p n l b.val → x.val.testBit b.val = y.val.testBit b.val) :
        Good F n y := by
      intro j hj
      induction j using Nat.strong_induction_on with
      | ind j ih =>
        have eq := tri j (by omega) x y (fun t ht => gx t (by omega)) (fun t ht => ih t ht (by omega))
          (fun b hb => same b (fun ⟨t,hl,hr,eq⟩ => hb ⟨t,by omega,hr,eq⟩))
        have thisBit := same (p j) (by
          rintro ⟨t,hl,hr,eq⟩
          have e := distinct t hr j (by omega) (Fin.ext eq)
          omega)
        rw [thisBit,gx j hj] at eq
        exact (Bool.xor_left_inj.mp eq).symm
    induction n with
    | zero =>
      refine ⟨fun _ h => by omega, fun _ _ => rfl, fun _ _ right => right⟩
    | succ n ih =>
      obtain ⟨hG,hOff,hUnique⟩ := ih (by omega)
      let x := run p F seed n
      let y := put p F n x
      have changed (j : Nat) : y.val.testBit j = xor (x.val.testBit j) (F n x && decide ((p n).val=j)) := by
        dsimp only [y,put]
        cases F n x <;> simp [flipBit]
      have keep (b:Fin k) (e:b≠p n) : y.val.testBit b.val=x.val.testBit b.val := by
        rw [changed];simp [show (p n).val≠b.val by intro h;exact e (Fin.ext h.symm)]
      have old := stable n (by omega) x y hG (fun b h => (keep b (by
        rintro rfl;exact h ⟨n,by omega,by omega,rfl⟩)).symm)
      have fix := tri n (by omega) y x old hG (fun b h => keep b (by
        rintro rfl;exact h ⟨n,by omega,by omega,rfl⟩))
      rw [changed] at fix
      have fixed : F n y=false := by
        simpa only [decide_true, Bool.and_true] using
          (show ∀ z c d : Bool, xor z (xor c d) = xor d c → z=false by decide) _ _ _ (by simpa using fix)
      refine ⟨?_,?_,?_⟩
      · intro j hj
        by_cases e:j=n
        · subst j;exact fixed
        · exact old j (by omega)
      · intro b h
        have off : ¬Future p 0 n b.val := fun ⟨j,hl,hr,eq⟩ => h ⟨j,hl,by omega,eq⟩
        have ne : b≠p n := by rintro rfl; exact h ⟨n,by omega,by omega,rfl⟩
        exact (keep b ne).trans (hOff b off)
      · intro z hz right b ho
        have upto := hUnique z (fun j hj => hz j (by omega)) right
        by_cases pe : b=p n
        · subst b
          have eq := tri n (by omega) z y (fun j hj => hz j (by omega)) old (fun j off =>
            (upto j off).trans (keep j (by rintro rfl;exact off ⟨n,by omega,by omega,rfl⟩)).symm)
          change z.val.testBit (p n).val=y.val.testBit (p n).val;simpa only [hz n (by omega),fixed,Bool.false_xor] using eq
        · have off : ¬Future p n l b.val := by
            rintro ⟨t,tl,tr,eq⟩
            by_cases tt:t=n
            · subst t;exact pe (Fin.ext eq.symm)
            · exact ho ⟨t,by omega,tr,eq⟩
          exact (upto b off).trans (keep b pe).symm
  intro target
  obtain ⟨ok,off,unique⟩:=invariant l (by omega)
  constructor
  · rintro rfl;exact ⟨ok,off⟩
  · rintro ⟨gt,h⟩
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases e:j<k
    · exact unique _ gt h ⟨j,e⟩ (fun ⟨t,hl,hr,_⟩ => by omega)
    · have mono : 2^k ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le target.isLt mono),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (run p F seed l).isLt mono)]

end Solver
end PEqualNP.Outside.L_meta_25539_aux

namespace PEqualNP.Outside.L_meta_25539_aux
open PEqualNP.Outside.L_meta_25539_aux.Line (rot stateAt)
open PEqualNP.Outside.L_meta_25539_aux.Recovery.Col97 (recover1Init initRecover1)
structure Layout (k : Nat) where
  r : Nat
  d : Nat
  i : Nat
  a : Nat
  v : Nat
  hr : 7 ≤ r
  hkd : k+3+d=5*r
  hd : d ≤ 3*((r-5)/2)
  hi : i<k
  him : i+(3*((r-5)/2)-d) ≤ k
  ha : a ≤ (r-5)/2
  hv : v<16^a
  eligible : a=0 ∨ d<gain v (a-1)+3*((r-5)/2+1-a)

namespace Layout
variable {k : Nat} (L : Layout k)
abbrev pairs := (L.r-5)/2
abbrev q := k+L.i+3*L.r-L.d
abbrev m := if L.a=L.pairs then gain L.v L.a-L.d else 0
abbrev N := 4*L.a+L.m
def hit (j : Nat) := L.v.testBit (4*j)
def off (j c : Nat) := if c=0 then 0 else if c=1 then 2 else if c=2 then 3 else if L.hit j then 4 else 5
def pp (t : Nat) := if t<4*L.a then left L.q L.v (t/4)-L.off (t/4) (t % 4)
  else L.q-k+(L.m-1-(t-4*L.a))
include L in
lemma kLarge : 16≤k := by have:=L.hr;have:=L.hkd;have:=L.hd;omega
def pv (t : Nat) : Fin k := ⟨L.pp t % k,Nat.mod_lt _ (by have:=L.kLarge;omega)⟩
def inputWord (u x : Fin (2^k)) : Fin (2^k) :=
  ⟨rot k (k-1) (x.val ^^^ u.val),Nat.mod_lt _ (by positivity)⟩
include L in
lemma srcRecover (u x : Fin (2^k)) : src u (inputWord u x).val=x.val :=
  initRecover1 L.kLarge x.isLt u.isLt
include L in
lemma keyRecover (u w : Fin (2^k)) : (inputWord u ⟨src u w.val,
    Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) u.isLt⟩).val=w.val :=
  recover1Init L.kLarge w.isLt

def probe (u : Fin (2^k)) (c : Nat → Fin (2^k)) (x : Fin (2^k)) (t : Nat) :=
  let w:=(inputWord u x).val
  let j:=t/4
  let e:=edge L.q L.v j
  let l:=left L.q L.v j
  let s:=tick j
  if t<4*L.a then
    if t % 4=0 then par u c w (s-1) e
    else if t % 4=1 then
      if L.hit j then rawBit u c w s (e-2) == xor (inj c w s (e-1)) (inj c w s e)
      else x.val.testBit ((l-2)%k)
    else if t % 4=2 then
      if L.hit j then rawBit u c w s (e-3) == inj c w s e
      else x.val.testBit ((l-3)%k)
    else par u c w s (e-3+(L.hit j).toNat)
  else (stateAt k u c L.r w).testBit (L.i+(L.m-1-(t-4*L.a)))
def target (tgt : Fin (2^L.m)) (t : Nat) := if t<4*L.a then L.v.testBit t else tgt.val.testBit (L.m-1-(t-4*L.a))
def err (u : Fin (2^k)) (c : Nat → Fin (2^k)) (tgt : Fin (2^L.m)) (t : Nat) (x : Fin (2^k)) :=
  xor (L.probe u c x t) (L.target tgt t)

lemma gainMono (v : Nat) {i n : Nat} (h : i≤n) :
    gain v i ≤ gain v n ∧ gain v n ≤ gain v i+3*(n-i) := by
  induction n with
  | zero => have : i=0 := by omega
            subst i; simp
  | succ n ih =>
    by_cases e:i=n+1
    · subst i;simp
    · obtain ⟨l,r⟩:=ih (by omega)
      have t : delta (digit v n) ≤ 3 := by
        unfold delta
        exact (show ∀ a b c:Bool,a.toNat+b.toNat+c.toNat≤3 by decide) _ _ _
      rw [gainSucc];omega

lemma interval (t : Nat) (ht:t<L.N) : L.q-k ≤ L.pp t ∧ L.pp t<L.q := by
  have h₁:=L.hr;have h₂:=L.hkd;have h₃:=L.hd;have hi:=L.hi;have ha:=L.ha
  have gainA:=gainBound L.v L.a
  have elig:=L.eligible
  by_cases h:t<4*L.a
  · have lt : t/4<L.a := by omega
    have m:=gainMono L.v (i:=t/4) (n:=L.a-1) (by omega)
    have ub:=gainBound L.v (t/4)
    have os : L.off (t/4) (t % 4) ≤ 5 := by unfold off;split_ifs <;>omega
    simp only [pp,h,ite_true,left,edge,tick,q]
    try dsimp only [pairs] at *
    omega
  · simp only [pp,h,ite_false]
    dsimp only [q,N,m,pairs] at *
    split at ht <;> split <;> omega

lemma pointwise (t : Nat) (h:t+1<L.N) : L.pp (t+1)<L.pp t := by
  have h₁:=L.hr;have h₂:=L.hkd;have h₃:=L.hd;have hi:=L.hi;have ha:=L.ha
  have bound:=gainBound L.v L.a
  have eligible:=L.eligible
  have el:=L.interval t (by omega)
  have er:=L.interval (t+1) h
  have qm : k ≤ L.q := by dsimp [q];omega
  by_cases right : t+1<4*L.a
  · have left' : t<4*L.a := by omega
    have lt : t/4 < L.a := by omega
    have lm:=gainMono L.v (i:=t/4) (n:=L.a-1) (by omega)
    have lb:=gainBound L.v (t/4)
    simp only [pp,right,left',ite_true,left,edge,tick]
    by_cases last : t % 4=3
    · have newJ : (t+1)/4=t/4+1 := by omega
      have zero : (t+1)%4=0 := by omega
      rw [newJ,zero,gainSucc]
      have dB:delta (digit L.v (t/4))≤3 := by
        unfold delta;exact (show ∀ a b c:Bool,a.toNat+b.toNat+c.toNat≤3 by decide) _ _ _
      simp only [off,last,reduceCtorEq,↓reduceIte]
      dsimp [q,pairs] at *;split <;>omega
    · have same : (t+1)/4=t/4 := by omega
      rw [same];unfold off
      dsimp only [q,pairs] at *
      split_ifs <;>omega
  · by_cases first : t<4*L.a
    · have index : t/4=L.a-1 := by omega
      have rem' : t % 4=3 := by omega
      have complete : L.a=L.pairs := by by_contra ne;simp [N,m,ne] at h;omega
      have gainLast := gainMono L.v (i:=L.a-1) (n:=L.a) (by omega)
      have pregain:=gainBound L.v (L.a-1)
      simp only [pp,first,right,ite_true,ite_false,off,rem',index,reduceCtorEq,↓reduceIte]
      dsimp only [left,edge,tick,q,N,m,pairs] at *;split_ifs <;>omega
    · simp only [pp,right,first,ite_false];dsimp only [N] at *;omega

lemma decreasing {j t : Nat} (h:j<t) (ht:t<L.N) : L.pp t<L.pp j := by
  induction t with
  | zero => omega
  | succ t ih =>
    have one:=L.pointwise t ht
    by_cases e : j=t
    · simpa [e] using one
    · exact lt_trans one (ih (by omega) (by omega))

lemma sameMod {x y : Nat} (xl:L.q-k≤x) (xr:x<L.q) (yl:L.q-k≤y) (yr:y<L.q) (eq:x % k=y % k) : x=y := by
  have h₁:=L.hr;have h₂:=L.hkd;have h₃:=L.hd
  have qm : k ≤ L.q := by dsimp [q];omega
  have deltaLt (a b:Nat) (h:a<b) (hr:b<a+k) (eq:a % k=b % k) : False := by
    have nd : k ∣ b-a := (Nat.modEq_iff_dvd' (Nat.le_of_lt h)).mp eq
    have positive : 0 < b-a := by omega
    have := Nat.le_of_dvd positive nd
    omega
  rcases lt_trichotomy x y with h|e|h
  · exact False.elim (deltaLt x y h (by omega) eq)
  · exact e
  · exact False.elim (deltaLt y x h (by omega) eq.symm)
end Layout
end PEqualNP.Outside.L_meta_25539_aux

namespace PEqualNP.Outside.L_meta_25539_aux
namespace Layout
open PEqualNP.Outside.L_meta_25539_aux.Line (stateAt)
variable {k : Nat} (L : Layout k)

lemma lengthBound : L.N ≤ k := by
  have h₁:=L.hr;have h₂:=L.hkd;have h₃:=L.hd;have ha:=L.ha
  have g := gainBound L.v L.a
  dsimp only [N,m,pairs];split <;>omega

lemma pivotInjective : ∀ j<L.N, ∀ t<L.N, L.pv j=L.pv t → j=t := by
  intro j hj t ht h
  have same : L.pp j=L.pp t := L.sameMod (L.interval j hj).1 (L.interval j hj).2
    (L.interval t ht).1 (L.interval t ht).2 (congrArg Fin.val h)
  rcases lt_trichotomy j t with e|e|e
  · have := L.decreasing e ht;omega
  · exact e
  · have := L.decreasing e hj;omega

lemma pastAgreement {t : Nat} (ht:t<L.N) {x y : Fin (2^k)}
    (same:∀ b:Fin k, ¬Solver.Future L.pv t L.N b.val → x.val.testBit b.val=y.val.testBit b.val)
    (j : Nat) (lo:L.pp t<j) (hr:j<L.q) : x.val.testBit (j % k)=y.val.testBit (j % k) := by
  apply same ⟨j % k,Nat.mod_lt _ (by have:=L.kLarge;omega)⟩
  rintro ⟨z,hz,hl,eq⟩
  have low: L.q-k ≤ j := by have := (L.interval t ht).1; omega
  have e := L.sameMod (L.interval z hl).1 (L.interval z hl).2 low hr eq
  by_cases ez:t=z
  · subst z;omega
  · have := L.decreasing (by omega : t<z) hl;omega

lemma digitBit (v j b : Nat) (h:b<4) : (digit v j).testBit b = v.testBit (4*j+b) := by
  change ((v >>> (4*j)) % 2^4).testBit b = v.testBit (4*j+b)
  rw [Nat.testBit_mod_two_pow];simp only [h,decide_true,Bool.true_and,Nat.testBit_shiftRight]

def nibble (h b a n : Bool) := h.toNat+2*b.toNat+4*a.toNat+8*n.toNat
private theorem nibbleBits : ∀ h b a n : Bool, ∀ v : Fin 16,
    nibble h b a n=v.val ↔ h=v.val.testBit 0 ∧ b=v.val.testBit 1 ∧
      a=v.val.testBit 2 ∧ n=v.val.testBit 3 := by decide +kernel

lemma group (u : Fin (2^k)) (c : Nat → Fin (2^k)) (x : Fin (2^k)) (j : Nat) (hj:j<L.a) :
    (∀ b : Fin 4, L.probe u c x (4*j+b.val)=L.v.testBit (4*j+b.val)) ↔
    rawDigit u c (inputWord u x).val (tick j) (edge L.q L.v j)=digit L.v j := by
  let w := (inputWord u x).val
  let e := edge L.q L.v j
  let l := left L.q L.v j
  let s := tick j
  let h := par u c w (s-1) e
  let b := fun h : Bool => if h then rawBit u c w s (e-2) == xor (inj c w s (e-1)) (inj c w s e)
    else x.val.testBit ((l-2)%k)
  let a := fun h : Bool => if h then rawBit u c w s (e-3) == inj c w s e else x.val.testBit ((l-3)%k)
  let n := fun h : Bool => par u c w s (e-3+h.toNat)
  let bit := fun i : Nat => L.v.testBit (4*j+i)
  have p (z : Fin 4) : L.probe u c x (4*j+z.val) =
      if z.val=0 then h else if z.val=1 then b (L.hit j) else if z.val=2 then a (L.hit j) else n (L.hit j) := by
    have hz := z.isLt
    have stop : 4*j+z.val<4*L.a := by omega
    simp only [probe,stop,ite_true, show (4*j+z.val)/4=j by omega,
      show (4*j+z.val)%4=z.val by omega]
    rfl
  have re : rawDigit u c w s e=nibble h (b h) (a h) (n h) := by
    simp only [rawDigit,nibble,w,srcRecover L]
    rfl
  have hd := nibbleBits h (b h) (a h) (n h) ⟨digit L.v j,digitLt ..⟩
  simp only [digitBit _ _ 0 (by decide),digitBit _ _ 1 (by decide),
    digitBit _ _ 2 (by decide),digitBit _ _ 3 (by decide),Nat.add_zero] at hd
  change _ ↔ rawDigit u c w s e = _
  rw [re,hd]
  have foot : L.hit j=L.v.testBit (4*j) := rfl
  constructor
  · intro all
    have p0:=all 0; have p1:=all 1; have p2:=all 2; have p3:=all 3
    rw [p] at p0 p1 p2 p3
    simp only [Fin.val_zero,Fin.val_one, Nat.add_zero,↓reduceIte, Nat.reduceEqDiff] at p0 p1 p2 p3
    rw [foot,←p0] at p1 p2 p3
    exact ⟨p0,p1,p2,p3⟩
  · rintro ⟨hh,bb,aa,nn⟩ z
    rw [p,foot,←hh]
    fin_cases z <;> first | exact hh | exact bb | exact aa | exact nn

lemma xorFalse (a b : Bool) : xor a b=false ↔ a=b := by cases a <;> cases b <;> decide

lemma prefixFrom {u x : Fin (2^k)} {c : Nat → Fin (2^k)} {tgt : Fin (2^L.m)} {t j : Nat}
    (ht:t ≤ 4*L.a) (hj:4*j ≤ t) (g : Solver.Good (L.err u c tgt) t x) :
    ∀ z<j, rawDigit u c (inputWord u x).val (tick z) (edge L.q L.v z)=digit L.v z := by
  intro z hz
  apply (L.group u c x z (by omega)).mp
  intro b
  have bt:=b.isLt
  have h:=g (4*z+b.val) (by omega)
  simpa only [err,target,show 4*z+b.val<4*L.a by omega,ite_true,xorFalse] using h

lemma slice {v z i m : Nat} (hz:z<2^m) :
    (v >>> i)%2^m=z ↔ ∀ j<m, v.testBit (i+j)=z.testBit j := by
  constructor
  · intro eq j hj
    have e:=congrArg (fun n : Nat=>n.testBit j) eq
    simpa [Nat.testBit_mod_two_pow,hj,Nat.testBit_shiftRight,Nat.add_comm] using e
  · intro f;apply Nat.eq_of_testBit_eq
    intro j
    by_cases h:j<m
    · simpa [Nat.testBit_mod_two_pow,h,Nat.testBit_shiftRight,Nat.add_comm] using f j h
    · simp [Nat.testBit_mod_two_pow,h,Nat.testBit_lt_two_pow (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide) (by omega : m≤j)))]

lemma goodIff (u x : Fin (2^k)) (c : Nat → Fin (2^k)) (tgt : Fin (2^L.m)) :
    Solver.Good (L.err u c tgt) L.N x ↔
      (trace u c L.q (inputWord u x).val L.a).2=L.v ∧
      ((stateAt k u c L.r (inputWord u x).val) >>> L.i)%2^L.m=tgt.val := by
  rw [traceIff _ _ _ _ L.hv, slice tgt.isLt]
  constructor
  · intro all
    refine ⟨L.prefixFrom (t:=4*L.a) (tgt:=tgt) (by omega) (by omega) (fun j hj=>all j (by dsimp [N];omega)),?_⟩
    intro j hj
    let t := 4*L.a+(L.m-1-j)
    have h : t<L.N := by dsimp [t,N];omega
    have e := all t h
    simpa only [err,probe,target, show ¬t<4*L.a by dsimp [t];omega,ite_false,
      show L.m-1-(t-4*L.a)=j by dsimp [t];omega,xorFalse] using e
  · rintro ⟨groups,final⟩ t ht
    unfold err
    rw [xorFalse]
    by_cases h : t<4*L.a
    · let b : Fin 4 := ⟨t % 4,Nat.mod_lt _ (by decide)⟩
      have eq := (L.group u c x (t/4) (by omega)).mpr (groups (t/4) (by omega)) b
      have et : 4*(t/4)+b.val=t := by dsimp [b];omega
      simpa only [target,h,ite_true,et] using eq
    · simpa only [probe,target,h,ite_false] using final (L.m-1-(t-4*L.a)) (by dsimp [N] at ht;omega)

end Layout
end PEqualNP.Outside.L_meta_25539_aux

namespace PEqualNP.Outside.L_meta_25539_aux
open PEqualNP.Outside.L_meta_25539_aux.Line

def word39 {k : Nat} (u w : Fin (2^k)) (j : Nat) := (src u w.val).testBit (j % k)

private lemma initial39 {k q : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k))
    {f g : Nat → Bool} (same : ∀ n, n<q → f n=g n) (s p : Nat) (h : p+3*s<q) :
    lineStep k u c f s p=lineStep k u c g s p := by
  induction s generalizing p with
  | zero => exact same p (by omega)
  | succ s ih =>
    rw [Right.stepEq,Right.stepEq]
    unfold Right.cell lInj
    rw [ih _ (by omega),ih _ (by omega),ih _ (by omega),ih _ (by omega),ih _ (by omega),same _ (by omega)]

private lemma letter39 {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (f : Nat → Bool) (s e : Nat) :
    lBranch u c f (s+1) e = Right.letter (lineStep k u c f s) (lInj u c f (s+1)) e := by
  simp only [lBranch,lGuard,lNear,lFar,Right.letter,Right.grd,Right.tri,Nat.add_one_sub_one,Right.stepEq]
  rfl

private lemma packedGain39 (h b a n mb ma : Bool) :
    PEqualNP.Outside.L_meta_25539_aux.Line.gain (if h then 2+b.toNat+2*a.toNat+4*n.toNat else n.toNat) =
    delta (h.toNat+2*(if h then b else mb).toNat+4*(if h then a else ma).toNat+8*n.toNat) := by
  revert h b a n mb ma
  decide

private lemma rawGain39 {k t e : Nat} (hk : 6≤k) (ht : 5≤t) (he : 2*t+6≤e)
    (u : Fin (2^k)) (c : Nat → Fin (2^k)) (w : Fin (2^k)) :
    PEqualNP.Outside.L_meta_25539_aux.Line.gain (lBranch u c (word39 u w) t e)=delta (rawDigit u c w.val t e) := by
  change PEqualNP.Outside.L_meta_25539_aux.Line.gain (lBranch u c (PEqualNP.Outside.L_meta_25539_aux.Line.src u w.val) t e) = _
  rw [branchRaw hk ht he w.isLt]
  exact packedGain39 ..

lemma cutPrefix39 {k q v j : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (w : Fin (2^k))
    (hk : 6≤k) (big : 10*j+35≤q)
    (pre : ∀ z<j, rawDigit u c w.val (tick z) (edge q v z)=digit v z) :
    Right.PrefixEq (lineStep k u c (word39 u w) (4+2*j))
      (lineStep k u c (cut q (word39 u w)) (4+2*j)) (edge q v j) := by
  let f := word39 u w
  let g := cut q f
  have same (n : Nat) (h : n<q) : f n=g n := by simp [g,cut,h]
  induction j with
  | zero =>
    intro p hp
    change p≤q-13 at hp
    exact initial39 u c same 4 p (by omega)
  | succ j ih =>
    let s := 4+2*j
    let e := edge q v j
    have lb : q-13-6*j≤e := by dsimp [e,edge];omega
    have top : e+13≤q := by have := gainBound v j;dsimp [e,edge];omega
    have he : 2*(s+1)+6≤e := by dsimp [s];omega
    have old : Right.PrefixEq (lineStep k u c f s) (lineStep k u c g s) e :=
      ih (by omega) (fun z hz => pre z (by omega))
    have injEq (t : Nat) : Right.PrefixEq (lInj u c f t) (lInj u c g t) e := by
      intro n hn
      unfold lInj
      rw [same _ (by omega)]
    have more := Right.grow (by dsimp [s] at he;omega : 12≤e) old (injEq (s+1)) (injEq (s+2))
    have value : PEqualNP.Outside.L_meta_25539_aux.Line.gain (Right.letter (lineStep k u c f s) (lInj u c f (s+1)) e)=delta (digit v j) := by
      rw [←letter39,rawGain39 hk (by dsimp [s];omega) he]
      rw [show s+1=tick j by dsimp [s,tick];omega]
      exact congrArg delta (pre j (by omega))
    rw [value] at more
    have next : edge q v (j+1)=e-6+delta (digit v j) := by
      dsimp [e,edge]
      rw [gainSucc]
      omega
    intro n hn
    rw [next] at hn
    have conv (a : Nat → Bool) : lineStep k u c a (4+2*(j+1)) n =
      Right.cell (Right.cell (lineStep k u c a s) (lInj u c a (s+1))) (lInj u c a (s+2)) n := by
      rw [show 4+2*(j+1)=(s+1)+1 by dsimp [s];omega,Right.stepEq]
      rw [show lineStep k u c a (s+1) = Right.cell (lineStep k u c a s) (lInj u c a (s+1)) by funext p;exact Right.stepEq ..]
    rw [conv,conv]
    exact more.2 n hn

end PEqualNP.Outside.L_meta_25539_aux

namespace PEqualNP.Outside.L_meta_25539_aux
open PEqualNP.Outside.L_meta_25539_aux.Line

theorem cutQueries39 {k q v j : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (w : Fin (2^k))
    (hk : 6≤k) (big : 10*j+35≤q)
    (pre : ∀ z<j, rawDigit u c w.val (tick z) (edge q v z)=digit v z) :
    let t := tick j
    let e := edge q v j
    let f := cut q (word39 u w)
    let h := par u c w.val (t-1) e
    h = lGuard u c f (t-1) e ∧
      (h=true → (rawBit u c w.val t (e-2) == xor (inj c w.val t (e-1)) (inj c w.val t e))=lNear u c f t e) ∧
      (h=true → (rawBit u c w.val t (e-3) == inj c w.val t e)=lFar u c f t e) ∧
      par u c w.val t (e-3+h.toNat) = lGuard u c f t (e-3+h.toNat) := by
  intro t e f h
  have st : t-1=4+2*j := by dsimp [t,tick];omega
  have s1 : t-1+1=t := by dsimp [t,tick];omega
  have lo : 2*t+6≤e := by dsimp [t,tick,e,edge];omega
  have top : e+13≤q := by have := gainBound v j;dsimp [e,edge];omega
  have old : Right.PrefixEq (lineStep k u c (word39 u w) (t-1)) (lineStep k u c f (t-1)) e := by
    rw [st]
    exact cutPrefix39 u c w hk big pre
  have sameInj : Right.PrefixEq (lInj u c (word39 u w) t) (lInj u c f t) e := by
    intro n hn
    simp [lInj,f,cut,show n+3-2*t<q by omega]
  have injLine (n : Nat) (hn : 2*t≤n) (en : n≤e) :
      inj c w.val t n=lInj u c f t n :=
    (injRaw hk (by omega) hn w.isLt u c).symm.trans (sameInj n en)
  have rawLine (s n : Nat) (bound : 2*s≤n) : rawBit u c w.val s n=lineStep k u c (word39 u w) s n :=
    (lineStep_eq_stateAt (by omega) u c w s n bound).symm
  have headRaw : h=Right.grd (lineStep k u c (word39 u w) (t-1)) e := by
    change xor (xor (rawBit u c _ _ _) (rawBit u c _ _ _)) (rawBit u c _ _ _) = _
    rw [rawLine _ _ (by omega),rawLine _ _ (by omega),rawLine _ _ (by omega)]
    rfl
  have asStep (a : Nat → Bool) : lineStep k u c a t=Right.cell (lineStep k u c a (t-1)) (lInj u c a t) := by
    funext n
    have eq := Right.stepEq u c a (t-1) n
    rwa [s1] at eq
  have more := Right.move (by omega : 6≤e) old sameInj
  rw [←asStep,←asStep,←headRaw] at more
  have mid (n : Nat) (start : 2*t≤n) (stop : n≤e-3+h.toNat) :
      rawBit u c w.val t n=lineStep k u c f t n := (rawLine t n start).trans (more n stop)
  refine ⟨headRaw.trans (Right.guardEq old),?_,?_,?_⟩
  · intro hit
    unfold lNear
    rw [mid _ (by omega) (by rw [hit];simp;omega),injLine _ (by omega) (by omega),injLine _ (by omega) (by omega)]
  · intro _
    unfold lFar
    rw [mid _ (by omega) (by omega),injLine _ (by omega) (by omega)]
  · unfold par lGuard
    rw [mid _ (by omega) (by omega),mid _ (by omega) (by omega),mid _ (by omega) (by omega)]

end PEqualNP.Outside.L_meta_25539_aux

namespace PEqualNP.Outside.L_meta_25539_aux
open PEqualNP.Outside.L_meta_25539_aux.Line

private lemma rollPrefix39 {k e q : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k))
    {f g : Nat → Bool} (same : ∀ n, n<q → f n=g n) (upper : e+4≤q) (old : Nat)
    (base : Right.PrefixEq (lineStep k u c f old) (lineStep k u c g old) e)
    (len pos : Nat) (hp : pos+3*len≤e) : lineStep k u c f (old+len) pos = lineStep k u c g (old+len) pos := by
  induction len generalizing pos with
  | zero => exact base pos (by omega)
  | succ len ih =>
    rw [show old+(len+1)=(old+len)+1 by omega,Right.stepEq,Right.stepEq]
    unfold Right.cell lInj
    rw [ih _ (by omega),ih _ (by omega),ih _ (by omega),ih _ (by omega),ih _ (by omega),same _ (by omega)]

theorem terminalPivot39 {k r d i pairs q v s : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k))
    (x y : Fin (2^k)) (hr : 7≤r) (hk : k+3+d=5*r) (periods : pairs=(r-5)/2)
    (width : q=k+i+3*r-d) (hd : d≤3*pairs) (hs : s<gain v pairs-d) (hi : i+s<k)
    (preX : ∀ z<pairs, rawDigit u c x.val (tick z) (edge q v z)=digit v z)
    (preY : ∀ z<pairs, rawDigit u c y.val (tick z) (edge q v z)=digit v z)
    (same : ∀ n, q+s-k<n → n<q → word39 u x n=word39 u y n) :
    xor ((stateAt k u c r x.val).testBit (i+s)) ((stateAt k u c r y.val).testBit (i+s)) =
      xor ((src u x.val).testBit ((q+s) % k)) ((src u y.val).testBit ((q+s) % k)) := by
  let p := k+i+s
  let a := 4+2*pairs
  have hP : 2*r≤p := by dsimp [p];omega
  have hm : p % k=i+s := by dsimp [p];rw [show k+i+s=(i+s)+k by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hi]
  have gl := gainBound v pairs
  have ep : p+3*(r-a)≤edge q v pairs := by dsimp [p,a,edge];omega
  have eb : edge q v pairs+4≤q := by dsimp [edge];omega
  have pivot : p+3-2*r=q+s-k := by dsimp [p];omega
  have pk : q+s-k<q := by omega
  have pm : (q+s-k)%k=(q+s)%k := by
    conv_rhs => rw [show q+s=(q+s-k)+k by omega,Nat.add_mod_right]
  have bridge (w : Fin (2^k)) (pre : ∀ z<pairs, rawDigit u c w.val (tick z) (edge q v z)=digit v z) :
      (stateAt k u c r w.val).testBit (i+s) = lineStep k u c (cut q (word39 u w)) r p := by
    have base := cutPrefix39 u c w (by omega) (by omega) pre
    have right := rollPrefix39 u c (f:=word39 u w) (g:=cut q (word39 u w))
      (fun n hn => by simp [cut,hn]) eb a base (r-a) p ep
    rw [show a+(r-a)=r by dsimp [a];omega] at right
    have fromRaw := lineStep_eq_stateAt (by omega : 2≤k) u c w r p hP
    rw [hm] at fromRaw
    exact fromRaw.symm.trans right
  rw [bridge x preX,bridge y preY]
  have deltaBit := lineStep_xor_pivot k u c (cut q (word39 u x)) (cut q (word39 u y)) r p (by omega) hP
    (fun n lo _ => by
      by_cases hn : n<q
      · simp only [cut,if_pos hn]; exact same n (by omega) hn
      · simp [cut,hn])
  rw [pivot] at deltaBit
  simpa only [cut,if_pos pk,word39,pm] using deltaBit

end PEqualNP.Outside.L_meta_25539_aux

namespace PEqualNP.Outside.L_meta_25539_aux
open PEqualNP.Outside.L_meta_25539_aux.Line (cut lNear lFar lGuard gPivot alignPivot stateAt)
namespace Layout
variable {k : Nat} (L : Layout k)

def lp (u : Fin (2^k)) (c : Nat → Fin (2^k)) (f : Nat → Bool) (n : Nat) :=
  let j:=n/4
  let t:=tick j
  let e:=edge L.q L.v j
  let l:=left L.q L.v j
  if n % 4=0 then lGuard u c f (t-1) e
  else if n % 4=1 then if L.hit j then lNear u c f t e else f (l-2)
  else if n % 4=2 then if L.hit j then lFar u c f t e else f (l-3)
  else lGuard u c f t (e-3+(L.hit j).toNat)

lemma guardBefore {u x : Fin (2^k)} {c : Nat → Fin (2^k)} {tgt : Fin (2^L.m)} {n : Nat}
    (hn:n<4*L.a) (hnz : n % 4≠0) (h : Solver.Good (L.err u c tgt) n x) :
    par u c (inputWord u x).val (tick (n/4)-1) (edge L.q L.v (n/4))=L.hit (n/4) := by
  have t:=h (4*(n/4)) (by omega)
  simpa only [err,probe,target,show 4*(n/4)<4*L.a by omega,ite_true,
    show 4*(n/4)/4=n/4 by omega,show 4*(n/4)%4=0 by omega,↓reduceIte,hit,xorFalse] using t

def trunc (u x : Fin (2^k)) := cut L.q (word39 u (inputWord u x))
lemma truncAt (u x : Fin (2^k)) (j : Nat) (h:j<L.q) :
    L.trunc u x j=x.val.testBit (j % k) := by simp [trunc,cut,word39,h,L.srcRecover]

lemma intoLine {u x : Fin (2^k)} {c : Nat → Fin (2^k)} {tgt : Fin (2^L.m)} {n : Nat}
    (hn:n<4*L.a) (ok : Solver.Good (L.err u c tgt) n x) :
    L.probe u c x n = L.lp u c (L.trunc u x) n := by
  let j:=n/4
  let t:=tick j
  let e:=edge L.q L.v j
  let l:=left L.q L.v j
  have h₁:=L.hr; have h₂:=L.hkd; have hd:=L.hd;have ha:=L.ha
  have big : 10*j+35≤L.q := by dsimp [q,j];omega
  have pre:=L.prefixFrom (j:=j) (t:=n) (by omega) (by dsimp [j];omega) ok
  obtain ⟨hh,bb,aa,nn⟩:=cutQueries39 u c (inputWord u x) (by have:=L.kLarge;omega) big pre
  have hl : l<L.q := by have:=gainBound L.v j;dsimp [l,left,edge,tick];omega
  simp only [probe,hn,ite_true,lp]
  by_cases zero:n % 4=0
  · simp only [zero,ite_true];exact hh
  · have hhit := L.guardBefore hn zero ok
    rw [hhit] at nn
    simp only [zero,ite_false]
    by_cases b:n % 4=1
    · simp only [b,ite_true]
      cases h:L.hit (n/4)
      · simp only [Bool.false_eq_true,ite_false];exact (L.truncAt _ _ _ (by change l-2<L.q;omega)).symm
      · simp only [ite_true];exact bb (hhit.trans h)
    · simp only [b,ite_false]
      by_cases a:n % 4=2
      · simp only [a,ite_true]
        cases h:L.hit (n/4)
        · simp only [Bool.false_eq_true,ite_false];exact (L.truncAt _ _ _ (by change l-3<L.q;omega)).symm
        · simp only [ite_true];exact aa (hhit.trans h)
      · simpa only [a,ite_false,j,trunc] using nn

lemma lineXor (u : Fin (2^k)) (c : Nat → Fin (2^k)) (n : Nat) (hn:n<4*L.a)
    (f g : Nat → Bool) (same : ∀ j, L.pp n<j → f j=g j) :
    xor (L.lp u c f n) (L.lp u c g n)=xor (f (L.pp n)) (g (L.pp n)) := by
  let j:=n/4
  let t:=tick j
  let e:=edge L.q L.v j
  have h₁:=L.hr; have h₂:=L.hkd; have hd:=L.hd;have ha:=L.ha
  have ht : 5≤t := by dsimp [t,tick];omega
  have he : 2*t+6≤e := by dsimp [e,t,edge,tick,q,j];omega
  simp only [pp,hn,ite_true,left,lp,off] at same ⊢
  by_cases z:n % 4=0
  · simp only [z,ite_true,Nat.sub_zero] at same ⊢
    have eq:e+1-2*(t-1)=e+3-2*t := by omega
    simpa only [eq] using gPivot u c f g (s:=t-1) (e:=e) (by omega) (by omega)
      (fun a ha=>same a (by change e+3-2*t<a;omega))
  · simp only [z,ite_false] at same ⊢
    by_cases one:n % 4=1
    · simp only [one,ite_true] at same ⊢
      cases h:L.hit (n/4)
      · rfl
      · simp only [ite_true]
        have eq:e+3-2-2*t=e+3-2*t-2 := by omega
        simpa only [ite_true,eq] using alignPivot u c f g ht (by omega : 2*t+3≤e) true
          (fun a ha=>same a (by change e+3-2-2*t<a at ha;change e+3-2*t-2<a;omega))
    · simp only [one,ite_false] at same ⊢
      by_cases two:n % 4=2
      · simp only [two,ite_true] at same ⊢
        cases h:L.hit (n/4)
        · rfl
        · simp only [ite_true]
          have eq:e+3-3-2*t=e+3-2*t-3 := by omega
          simpa only [Bool.false_eq_true,ite_false,eq] using alignPivot u c f g ht (by omega : 2*t+3≤e) false
            (fun a ha=>same a (by change e+3-3-2*t<a at ha;change e+3-2*t-3<a;omega))
      · simp only [two,ite_false] at same ⊢
        cases hh:L.hit (n/4) <;> simp only [hh,Bool.false_eq_true,ite_false,ite_true,Bool.toNat_false,Bool.toNat_true,Nat.add_zero] at same ⊢
        · have eq:e-3+1-2*t=e+3-2*t-5 := by omega
          simpa only [eq] using gPivot u c f g (s:=t) (by omega) (e:=e-3) (by omega) (fun a ha=>same a (by change e+3-2*t-5<a;omega))
        · have eq:e-3+1+1-2*t=e+3-2*t-4 := by omega
          simpa only [eq] using gPivot u c f g (s:=t) (by omega) (e:=e-3+1) (by omega) (fun a ha=>same a (by change e+3-2*t-4<a;omega))

theorem mainTri (u : Fin (2^k)) (c : Nat → Fin (2^k)) (tgt : Fin (2^L.m)) :
    ∀ n<L.N, ∀ x y, Solver.Good (L.err u c tgt) n x → Solver.Good (L.err u c tgt) n y →
      (∀ b : Fin k, ¬Solver.Future L.pv n L.N b.val → x.val.testBit b.val=y.val.testBit b.val) →
      xor (L.err u c tgt n x) (x.val.testBit (L.pv n).val)=
        xor (L.err u c tgt n y) (y.val.testBit (L.pv n).val) := by
  intro n hn x y hx hy agree
  have same:=L.pastAgreement hn agree
  suffices hd : xor (L.probe u c x n) (L.probe u c y n) =
      xor (x.val.testBit (L.pv n).val) (y.val.testBit (L.pv n).val) by
    exact (show ∀ a b c d e : Bool, xor a b=xor c d →
      xor (xor a e) c=xor (xor b e) d by decide) _ _ _ _ _ hd
  by_cases hist:n<4*L.a
  · rw [L.intoLine hist hx,L.intoLine hist hy]
    let f:=L.trunc u x
    let g:=L.trunc u y
    have sa (j) (hl:L.pp n<j) : f j=g j := by
      by_cases h:j<L.q
      · exact (L.truncAt _ _ j h).trans ((same j hl h).trans (L.truncAt _ _ j h).symm)
      · simp [f,g,trunc,cut,h]
    have e:=L.lineXor u c n hist f g sa
    simpa only [f,g,L.truncAt _ _ (L.pp n) (L.interval n hn).2,pv] using e
  · let s:=L.m-1-(n-4*L.a)
    have top : s<L.m := by dsimp [s];dsimp [N] at hn;omega
    have full : L.a=L.pairs := by by_contra ne;simp [m,ne] at top
    have bd:=gainBound L.v L.a
    have h1:=L.hr;have h2:=L.hkd;have hd:=L.hd;have hi:=L.him
    have out : L.i+s<k := by dsimp [m] at top;rw [ite_eq_left full] at top;dsimp [pairs] at full;omega
    have allX := L.prefixFrom (j:=L.a) (t:=4*L.a) (by omega) (by omega)
      (tgt:=tgt) (fun j hj=>hx j (by omega))
    have allY := L.prefixFrom (j:=L.a) (t:=4*L.a) (by omega) (by omega)
      (tgt:=tgt) (fun j hj=>hy j (by omega))
    have eq : L.pp n = L.q+s-k := by
      have : k≤L.q := by dsimp [q];omega
      simp only [pp,hist,ite_false];dsimp [s];omega
    have sw := terminalPivot39 u c (inputWord u x) (inputWord u y) L.hr L.hkd full (show L.q=k+L.i+3*L.r-L.d from rfl) (show L.d≤3*L.a by simpa only [full] using hd)
      (show s<gain L.v L.a-L.d by simpa only [m,full,ite_true] using top) out allX allY
      (fun j hp hq=>by simp only [word39,L.srcRecover];exact same j (by rw [eq];exact hp) hq)
    have em : (L.q+s)%k=L.pp n % k := by
      rw [eq];exact Nat.mod_eq_sub_mod (by dsimp [q];omega)
    simpa only [probe,hist,ite_false,s,pv,L.srcRecover,em] using sw

end Layout
end PEqualNP.Outside.L_meta_25539_aux

namespace PEqualNP.Outside.L_meta_25539_aux.Layout

variable {k : Nat} (L : Layout k)

def flag (p : Nat) :=
  (List.range L.a).any (fun j =>
    let l := left L.q L.v j
    let last := if L.v.testBit (4*j) then 4 else 5
    ([l,l-2,l-3,l-last] : List Nat).any (fun n => n % k == p)) ||
  (List.range L.m).any (fun s => (L.q+s) % k == p)

private lemma positions39 (j p : Nat) :
    let l := left L.q L.v j
    let last := if L.v.testBit (4*j) then 4 else 5
    ([l,l-2,l-3,l-last] : List Nat).any (fun n => n % k == p) = true ↔
      ∃ c<4, (l-L.off j c) % k = p := by
  intro l last
  simp only [List.any_cons,List.any_nil,Bool.or_eq_true,beq_iff_eq,Bool.false_eq_true,or_false]
  constructor
  · rintro (h|h|h|h)
    · exact ⟨0,by decide,by simpa [off] using h⟩
    · exact ⟨1,by decide,by simpa [off] using h⟩
    · exact ⟨2,by decide,by simpa [off] using h⟩
    · refine ⟨3,by decide,?_⟩
      cases hv : L.v.testBit (4*j) <;> simpa [off,hit,last,hv] using h
  · rintro ⟨c,hc,e⟩
    interval_cases c
    · exact Or.inl (by simpa [off] using e)
    · exact Or.inr (Or.inl (by simpa [off] using e))
    · exact Or.inr (Or.inr (Or.inl (by simpa [off] using e)))
    · apply Or.inr (Or.inr (Or.inr ?_))
      cases hv : L.v.testBit (4*j) <;> simpa [off,hit,last,hv] using e

private lemma tailMod39 (s : Nat) : (L.q-k+s) % k=(L.q+s) % k := by
  have cap : k≤L.q := by have := L.hd;have := L.hr;dsimp [q];omega
  have eq : L.q+s=L.q-k+s+k := by omega
  conv_rhs => rw [eq,Nat.add_mod_right]

lemma flagFuture (p : Nat) : L.flag p=true ↔ Solver.Future L.pv 0 L.N p := by
  change (_ || _) = true ↔ _
  rw [Bool.or_eq_true]
  constructor
  · rintro (branch|out)
    · obtain ⟨j,hj,atJ⟩ := List.any_eq_true.mp branch
      have hj := List.mem_range.mp hj
      obtain ⟨c,hc,cell⟩ := (L.positions39 j p).mp atJ
      refine ⟨4*j+c,by omega,by dsimp [N];omega,?_⟩
      simpa only [pv,pp,show 4*j+c<4*L.a by omega,ite_true,
        show (4*j+c)/4=j by omega,show (4*j+c)%4=c by omega] using cell
    · obtain ⟨s,hs,test⟩ := List.any_eq_true.mp out
      have hs := List.mem_range.mp hs
      have eq := beq_iff_eq.mp test
      let t := 4*L.a+(L.m-1-s)
      refine ⟨t,by omega,by dsimp [t,N];omega,?_⟩
      simpa only [pv,pp,show ¬t<4*L.a by dsimp [t];omega,ite_false,
        show L.m-1-(t-4*L.a)=s by dsimp [t];omega,tailMod39] using eq
  · rintro ⟨t,_,ht,eq⟩
    by_cases h:t<4*L.a
    · apply Or.inl
      apply List.any_eq_true.mpr
      refine ⟨t/4,List.mem_range.mpr (by omega),?_⟩
      apply (L.positions39 _ p).mpr
      refine ⟨t % 4,Nat.mod_lt _ (by decide),?_⟩
      simpa only [pv,pp,h,ite_true] using eq
    · apply Or.inr
      apply List.any_eq_true.mpr
      refine ⟨L.m-1-(t-4*L.a),List.mem_range.mpr (by dsimp [N] at ht;omega),?_⟩
      apply beq_iff_eq.mpr
      simpa only [pv,pp,h,ite_false,tailMod39] using eq

lemma flagFalse (p : Nat) : L.flag p=false ↔ ¬ Solver.Future L.pv 0 L.N p := by
  rw [←flagFuture]
  cases L.flag p <;> decide

end PEqualNP.Outside.L_meta_25539_aux.Layout

namespace PEqualNP.Outside.L_meta_25539_aux.Layout
open PEqualNP.Outside.L_meta_25539_aux.Line (stateAt)
variable {k : Nat} (L : Layout k)

theorem solutionIff (u w : Fin (2^k)) (c : Nat → Fin (2^k)) (tgt : Fin (2^L.m)) (seed : Fin (2^k))
    (cert : ∀ x, x=Solver.run L.pv (L.err u c tgt) seed L.N ↔
      Solver.Good (L.err u c tgt) L.N x ∧ ∀ b : Fin k, ¬Solver.Future L.pv 0 L.N b.val →
        x.val.testBit b.val=seed.val.testBit b.val) :
    w=inputWord u (Solver.run L.pv (L.err u c tgt) seed L.N) ↔
      (trace u c L.q w.val L.a).2=L.v ∧
      (∀ p : Fin k, L.flag p.val=false → (src u w.val).testBit p.val=seed.val.testBit p.val) ∧
      ((stateAt k u c L.r w.val) >>> L.i) % 2^L.m=tgt.val := by
  let x : Fin (2^k) := ⟨src u w.val,Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) u.isLt⟩
  let sol := Solver.run L.pv (L.err u c tgt) seed L.N
  have iw : inputWord u x=w := Fin.ext (L.keyRecover u w)
  have corr : w=inputWord u sol ↔ x=sol := by
    constructor
    · intro eq
      apply Fin.ext
      change src u w.val=sol.val
      rw [eq,L.srcRecover]
    · intro eq
      rw [←iw,eq]
  rw [corr,cert,L.goodIff,iw]
  constructor
  · rintro ⟨⟨tr,last⟩,off⟩
    exact ⟨tr,fun p hp => off p ((L.flagFalse p.val).mp hp),last⟩
  · rintro ⟨tr,off,last⟩
    exact ⟨⟨tr,last⟩,fun p hp => off p ((L.flagFalse p.val).mpr hp)⟩

end PEqualNP.Outside.L_meta_25539_aux.Layout

namespace PEqualNP.Outside.L_meta_25539_aux.Gates39
open PEqualNP.Outside.L_meta_25539_aux.BuilderLib (bits idx rot)
open PEqualNP.Outside.L_meta_25539_aux.BuilderLib.Builder
open PEqualNP.Outside.L_meta_25539_aux.BuilderLib.Builder.Bank
open PEqualNP.Outside.L_meta_25539_aux.BuilderLib.Eval
open PEqualNP.Outside.L_meta_25539_aux.BuilderLib.V37 (roundAny rotAny)
open PEqualNP.Outside.L_meta_25539_aux.Line (stateAt stateAt_zero stateAt_succ)
variable {k n : Nat}
abbrev Val := (Fin n → Bool) → Fin (2^k)
def available (B : Bank n) (V : Val (k:=k) (n:=n)) := HasWord k B (fun x => (V x).val)

lemma bitAt {D : Bank n} {X : Val (n:=n) (k:=k)} (av : available D X) (i : Nat) (hi:i<k) :
    D.Has (fun x => (X x).val.testBit i) := by simpa only [bits,idxNat hi] using av (i:Int)

lemma keyAv (L : Layout k) {D : Bank n} {X U : Val (n:=n) (k:=k)} (ax : available D X) (au : available D U) :
    D.Grow (4*k) (fun E => available E (fun x => Layout.inputWord (U x) (X x))) := by
  obtain ⟨E,e,sz,v⟩ := xorWords (by have := L.kLarge;omega) ax au
  exact ⟨E,e,by omega,rotAny (k-1) (by have := L.kLarge;omega) v (fun x => Nat.xor_lt_two_pow (X x).isLt (U x).isLt)⟩

lemma stateAv (L : Layout k) (D : Bank n) (U W : Val (n:=n) (k:=k)) (c : Nat → Fin (2^k))
    (au : available D U) (aw : available D W) (t : Nat) :
    D.Grow (4*k+19*k*t) (fun E => HasWord k E (fun x => stateAt k (U x) c t (W x).val)) := by
  have kp : 0<k := by have := L.kLarge;omega
  induction t with
  | zero =>
    obtain ⟨E,e,sz,h⟩ := xorWords kp (rotAny 1 kp aw (fun x => (W x).isLt)) au
    exact ⟨E,e,by omega,h⟩
  | succ t ih =>
    obtain ⟨E,e,sz,h⟩ := ih
    have bound (t : Nat) (x) : stateAt k (U x) c t (W x).val < 2^k := by
      cases t with
      | zero => exact Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) (U x).isLt
      | succ t =>
        rw [stateAt_succ]
        exact roundBound (dist:=1) (shift:=2*t) (w:=(W x).val) (state:=stateAt k (U x) c t (W x).val) (c (t+1)).isLt
    obtain ⟨F,f,sf,v⟩ := roundAny kp 1 (2*t) (c (t+1)).val (wordLift e aw) h (fun x=>(W x).isLt) (bound t)
    refine ⟨F,fun x => f (e x),by rw [Nat.mul_succ];omega,?_⟩
    intro z
    have eq (x : Fin n → Bool) : stateAt k (U x) c (t+1) (W x).val =
        round k 1 (2*t) (c (t+1)).val (W x).val (stateAt k (U x) c t (W x).val) := by
      rw [stateAt_succ];rfl
    simpa only [eq] using v z

lemma parAv (L : Layout k) {D : Bank n} (U W : Val (n:=n) (k:=k)) (c : Nat → Fin (2^k))
    (s e : Nat) (v : HasWord k D (fun x => stateAt k (U x) c s (W x).val)) :
    D.Grow 8 (fun F => F.Has (fun x => par (U x) c (W x).val s e)) := by
  have h (p : Nat) : D.Has (fun x => rawBit (U x) c (W x).val s p) := by
    change D.Has (fun x => (stateAt k (U x) c s (W x).val).testBit (p % k))
    have l := Nat.mod_lt p (show 0<k by have := L.kLarge;omega)
    simpa only [bits,idxNat l] using v ((p % k : Nat):Int)
  apply (xor2 (h (e-2)) (h (e-1))).bind (b:=4)
  intro E he val
  exact xor2 val (he (h e))

lemma injAv (L : Layout k) {D : Bank n} (W : Val (n:=n) (k:=k)) (c : Nat → Fin (2^k))
    (s e : Nat) (v : available D W) :
    D.Grow 1 (fun F => F.Has (fun x => inj c (W x).val s e)) := by
  have kp : 0<k := by have := L.kLarge;omega
  have key := rotAny (2*(s-1)) kp v (fun x => (W x).isLt)
  have bit := key ((e % k : Nat):Int)
  simp only [bits,idxNat (Nat.mod_lt e kp)] at bit
  exact Bank.xorConst bit ((c s).val.testBit (e % k))
end PEqualNP.Outside.L_meta_25539_aux.Gates39

namespace PEqualNP.Outside.L_meta_25539_aux.Gates39
open PEqualNP.Outside.L_meta_25539_aux.BuilderLib (bits)
open PEqualNP.Outside.L_meta_25539_aux.BuilderLib.Builder
open PEqualNP.Outside.L_meta_25539_aux.BuilderLib.Builder.Bank
open PEqualNP.Outside.L_meta_25539_aux.BuilderLib.Eval
open PEqualNP.Outside.L_meta_25539_aux.Line (stateAt)
variable {k n : Nat}
lemma eqWire {B : Bank n} {a b : BitFn n} (ha : B.Has a) (hb : B.Has b) :
    B.Grow 5 (fun D => D.Has (fun x => a x==b x)) := by
  apply (xor2 ha hb).bind (b:=1)
  intro D _ v
  have h (x) : (a x==b x) = !(xor (a x) (b x)) := by cases a x <;> cases b x <;> decide
  simpa only [h] using inv v

lemma probeAv (L : Layout k) (B : Bank n) (U X : Val (n:=n) (k:=k)) (c : Nat → Fin (2^k))
    (au : available B U) (ax : available B X) (t : Nat) :
    B.Grow (8*k+19*k*L.r+16) (fun E => E.Has (fun x => L.probe (U x) c (X x) t)) := by
  let j := t/4
  let e := edge L.q L.v j
  let l := left L.q L.v j
  let s := tick j
  let s' := if t<4*L.a then if t % 4=0 then s-1 else s else L.r
  let W := fun x => Layout.inputWord (U x) (X x)
  obtain ⟨D,h,hd,key⟩ := keyAv L ax au
  change available D W at key
  obtain ⟨E,h',he,sv⟩ := stateAv L D U W c (wordLift h au) key s'
  have kp : 0<k := by have := L.kLarge;omega
  have ok : s'≤L.r := by
    unfold s' s j tick
    have hm := L.ha;have hr := L.hr
    split_ifs <;> omega
  have stageCost : E.gates.length ≤ B.gates.length+8*k+19*k*L.r := by
    have small := Nat.mul_le_mul_left (19*k) ok
    omega
  have keyE := wordLift h' key
  have xE := wordLift h' (wordLift h ax)
  have snap (p : Nat) : E.Has (fun x => rawBit (U x) c (W x).val s' p) := by
    simpa only [rawBit,bits,idxNat (Nat.mod_lt p kp)] using sv ((p % k : Nat):Int)
  have output : E.Grow 16 (fun F => F.Has (fun x => L.probe (U x) c (X x) t)) := by
    by_cases hA : t<4*L.a
    · by_cases h0 : t % 4=0
      · have eq : s'=s-1 := by simp [s',hA,h0]
        have out := parAv L U W c s' e sv
        simpa only [Layout.probe,hA,h0,ite_true,eq,e,s,j,W] using out.weaken (b:=16) (by decide) (fun _ a=>a)
      · by_cases h1 : t % 4=1
        · by_cases hit : L.hit j=true
          · have eq : s'=s := by simp [s',hA,h0]
            have a := injAv L W c s' (e-1) keyE
            obtain ⟨F,f,cf,ij⟩ := a
            obtain ⟨G,g,cg,ij'⟩ := injAv L W c s' e (wordLift f keyE)
            obtain ⟨H,h2,c2,xj⟩ := xor2 (g ij) ij'
            obtain ⟨I,hi,ci,v⟩ := eqWire (h2 (g (f (snap (e-2))))) xj
            refine ⟨I,fun h => hi (h2 (g (f h))),by omega,?_⟩
            simpa only [Layout.probe,hA,h0,h1,ite_true,ite_false,show L.hit (t/4)=true from hit,eq,e,s,j,W,show (1:Nat)≠0 by decide,show (2:Nat)≠0 by decide,show (2:Nat)≠1 by decide] using v
          · have b := bitAt xE ((l-2)%k) (Nat.mod_lt _ kp)
            have h' : L.hit (t/4)=false := Bool.eq_false_iff.mpr hit
            apply (Grow.pure E (p:=fun D=>D.Has (fun x=>(X x).val.testBit ((l-2)%k))) b).weaken (by decide)
            intro D out
            simpa only [Layout.probe,hA,h0,h1,ite_true,ite_false,h',Bool.false_eq_true,l,j,show (1:Nat)≠0 by decide,show (2:Nat)≠0 by decide,show (2:Nat)≠1 by decide] using out
        · by_cases h2 : t % 4=2
          · by_cases hit : L.hit j=true
            · have eq : s'=s := by simp [s',hA,h0]
              obtain ⟨F,f,cf,ij⟩ := injAv L W c s' e keyE
              obtain ⟨G,g,cg,v⟩ := eqWire (f (snap (e-3))) ij
              refine ⟨G,fun h=>g (f h),by omega,?_⟩
              simpa only [Layout.probe,hA,h0,h1,h2,ite_true,ite_false,show L.hit (t/4)=true from hit,eq,e,s,j,W,show (1:Nat)≠0 by decide,show (2:Nat)≠0 by decide,show (2:Nat)≠1 by decide] using v
            · have bv := bitAt xE ((l-3)%k) (Nat.mod_lt _ kp)
              have h' : L.hit (t/4)=false := Bool.eq_false_iff.mpr hit
              apply (Grow.pure E (p:=fun D=>D.Has (fun x=>(X x).val.testBit ((l-3)%k))) bv).weaken (by decide)
              intro D out
              simpa only [Layout.probe,hA,h0,h1,h2,ite_true,ite_false,h',Bool.false_eq_true,l,j,show (1:Nat)≠0 by decide,show (2:Nat)≠0 by decide,show (2:Nat)≠1 by decide] using out
          · have eq : s'=s := by simp [s',hA,h0]
            have out := parAv L U W c s' (e-3+(L.hit j).toNat) sv
            simpa only [Layout.probe,hA,h0,h1,h2,ite_true,ite_false,eq,e,s,j,W] using out.weaken (b:=16) (by decide) (fun _ a=>a)
    · have eq : s'=L.r := by simp [s',hA]
      let atPos := L.i+(L.m-1-(t-4*L.a))
      by_cases less : atPos<k
      · have wire := sv (atPos:Int)
        simp only [bits,idxNat less,eq] at wire
        apply (Grow.pure E (p:=fun D=>D.Has (fun x=>(stateAt k (U x) c L.r (W x).val).testBit atPos)) wire).weaken (by decide)
        intro D out;simpa only [Layout.probe,hA,ite_false,atPos,W] using out
      · have bound (x) : stateAt k (U x) c L.r (W x).val < 2^k :=
          PEqualNP.Outside.L_meta_25539_aux.Line.stateAt_lt k (U x) c L.r (W x).val
        have zero (x) : (stateAt k (U x) c L.r (W x).val).testBit atPos=false :=
          Nat.testBit_lt_two_pow ((bound x).trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
        apply (E.const false).weaken (by decide)
        intro D out
        simp only [Layout.probe,hA,ite_false]
        change D.Has (fun x => (stateAt k (U x) c L.r (W x).val).testBit atPos)
        simpa only [zero] using out
  obtain ⟨F,g,gf,v⟩ := output
  exact ⟨F,fun x=>g (h' (h x)),by omega,v⟩
end PEqualNP.Outside.L_meta_25539_aux.Gates39

namespace PEqualNP.Outside.L_meta_25539_aux.Gates39
open PEqualNP.Outside.L_meta_25539_aux.BuilderLib (bits)
open PEqualNP.Outside.L_meta_25539_aux.BuilderLib.Name (name nameLt nameBit)
open PEqualNP.Outside.L_meta_25539_aux.BuilderLib.Builder
open PEqualNP.Outside.L_meta_25539_aux.BuilderLib.Builder.Bank
open PEqualNP.Outside.L_meta_25539_aux.BuilderLib.Eval
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
variable {k n : Nat}
def per (k r : Nat) := 12*k+19*k*r+17

lemma putAv (L : Layout k) (B : Bank n) (U X : Val (n:=n) (k:=k)) (c : Nat → Fin (2^k)) (target : Fin (2^L.m))
    (au : available B U) (ax : available B X) (t : Nat) :
    B.Grow (per k L.r) (fun D => available D (fun x => Solver.put L.pv (L.err (U x) c target) t (X x))) := by
  obtain ⟨E,e,ec,hp⟩ := probeAv L B U X c au ax t
  obtain ⟨F,f,fc,hv⟩ := Bank.xorConst hp (L.target target t)
  change F.Has (fun x => L.err (U x) c target t (X x)) at hv
  have kp : 0<k := by have := L.kLarge;omega
  have point (j : Fin k) (x : Fin n → Bool) :
      (Solver.put L.pv (L.err (U x) c target) t (X x)).val.testBit j.val =
        if (L.pv t).val=j.val then xor ((X x).val.testBit j.val) (L.err (U x) c target t (X x)) else (X x).val.testBit j.val := by
    unfold Solver.put
    split <;> rename_i cnd
    · rw [Solver.flipBit]; split <;> simp_all
    · split <;> simp_all
  have choices := F.collectFin k (fun j x => (Solver.put L.pv (L.err (U x) c target) t (X x)).val.testBit j.val) 4 (by
    intro G g j
    have b := g (f (e (bitAt ax j.val j.isLt)))
    by_cases equal : (L.pv t).val=j.val
    · simpa only [point,equal,ite_true] using xor2 b (g hv)
    · apply (Grow.pure G (p:=fun D=>D.Has (fun x => (X x).val.testBit j.val)) b).weaken (by decide)
      intro J wire;simpa only [point,equal,ite_false] using wire)
  obtain ⟨G,g,gc,bits⟩ := choices
  refine ⟨G,fun w=>g (f (e w)),?_,fromFin kp bits⟩
  unfold per;omega

lemma iterate (L : Layout k) (B : Bank n) (U : Val (n:=n) (k:=k)) (c : Nat → Fin (2^k)) (target : Fin (2^L.m))
    (au : available B U) (seed : Fin (2^k)) (t : Nat) :
    B.Grow (k+t*per k L.r) (fun D => available D (fun x => Solver.run L.pv (L.err (U x) c target) seed t)) := by
  induction t with
  | zero =>
    have kp : 0<k := by have := L.kLarge;omega
    obtain ⟨F,f,sz,v⟩ := B.collectFin k (fun j _ => seed.val.testBit j.val) 1 (fun D _ j => D.const _)
    exact ⟨F,f,by omega,fromFin kp v⟩
  | succ t ih =>
    obtain ⟨E,e,sz,v⟩ := ih
    obtain ⟨F,f,st,w⟩ := putAv L E U _ c target (wordLift e au) v t
    exact ⟨F,fun a=>f (e a),by rw [Nat.succ_mul];omega,w⟩

def nm {k : Nat} (x : Fin k → Bool) : Fin (2^k) := ⟨name id x,nameLt id x⟩
lemma nm_bits {k : Nat} (u : Fin (2^k)) : nm (fun b : Fin k => u.val.testBit b.val)=u := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq;intro j
  by_cases h:j<k
  · exact nameBit (k:=k) id (fun b : Fin k => u.val.testBit b.val) ⟨j,h⟩
  · have lim : 2^k≤2^j := Nat.pow_le_pow_right (by decide) (show k≤j by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (nm _).isLt lim),Nat.testBit_lt_two_pow (lt_of_lt_of_le u.isLt lim)]

theorem build (L : Layout k) (c : Nat → Fin (2^k)) (target : Fin (2^L.m))
    (seed : Fin (2^k)) (outBit : Fin k) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack k C ∧ C.size ≤ 128*(k+1)^2*(L.r+1) ∧
      ∀ name : Fin (2^k), C.eval ((List.range k).map (fun j=>name.val.testBit j)) =
       (Layout.inputWord name (Solver.run L.pv (L.err name c target) seed L.N)).val.testBit outBit.val := by
  have kp : 0<k := by have := L.kLarge;omega
  have nameOK : available (empty k) nm := by
    apply fromFin kp
    intro i
    have h (x : Fin k → Bool) : (nm x).val.testBit i.val=x i := nameBit id x i
    simpa only [h] using input i
  obtain ⟨D,e,sz,a⟩ := iterate L (empty k) nm c target nameOK seed L.N
  obtain ⟨E,f,st,w⟩ := keyAv L a (wordLift e nameOK)
  have NK : L.N≤k := by
    have h₁:=L.hr;have h₂:=L.hkd;have h₃:=L.hd;have ha:=L.ha
    have g := gainBound L.v L.a
    dsimp only [Layout.N,Layout.m,Layout.pairs];split <;>omega
  have cost : k+L.N*per k L.r+4*k ≤ 128*(k+1)^2*(L.r+1) := by
    calc
      _ ≤ k+k*per k L.r+4*k := by gcongr
      _ ≤ _ := by unfold per; nlinarith [Nat.zero_le (k^2*L.r),Nat.zero_le (k*L.r)]
  obtain ⟨C,h1,h2,szC,val⟩ := finish (b:=128*(k+1)^2*(L.r+1))
    (show (empty k).Grow _ (fun B=>B.Has _) from ⟨E,fun w=>f (e w),by omega,bitAt w _ outBit.isLt⟩)
  refine ⟨C,h1,h2,szC,?_⟩
  intro u
  have listEq : (List.range k).map (fun j=>u.val.testBit j) = List.ofFn (fun j : Fin k => u.val.testBit j.val) := by
    apply List.ext_getElem <;> simp
  rw [listEq,val,nm_bits]
end PEqualNP.Outside.L_meta_25539_aux.Gates39

open PEqualNP.Outside.L_meta_25539_aux in
theorem PEqualNP.Outside.L_meta_25539 :
∀ (k r d i : Nat), 7 ≤ r → k + 3 + d = 5 * r →
  let pairs := (r - 5) / 2
  d ≤ 3 * pairs → i < k → i + (3 * pairs - d) ≤ k →
  ∀ constant : Nat → Fin (2 ^ k),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc cell =>
      acc ||| ((xor (word.testBit cell)
        (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))).toNat <<< cell)) 0
  let state := fun (row rounds key : Nat) =>
    (List.range rounds).foldl (fun prev tick =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * tick) key ^^^
        (constant (tick + 1)).val) (rot 1 key ^^^ row)
  let injected := fun (round key pos : Nat) =>
    xor ((rot (2 * (round - 1)) key).testBit (pos % k))
      ((constant round).val.testBit (pos % k))
  let bit := fun (row round key pos : Nat) => (state row round key).testBit (pos % k)
  let guard := fun (row round key stop : Nat) =>
    xor (xor (bit row round key (stop - 2)) (bit row round key (stop - 1))) (bit row round key stop)
  let q := k + i + 3 * r - d
  let delta := fun (letter : Nat) =>
    (letter.testBit 0).toNat + (letter.testBit 3).toNat +
      ((letter % 16) == 15).toNat
  let prefixGain := fun (code length : Nat) =>
    ((List.range length).map (fun digitPos => delta ((code >>> (4 * digitPos)) % 16))).sum
  let trace := fun (row key length : Nat) =>
    ((List.range length).foldl (fun (st : Nat × Nat) j =>
      let t := 5 + 2 * j
      let edge := q - 13 - 6 * j + st.1
      let left := edge + 3 - 2 * t
      let x := rot 1 key ^^^ row
      let hit := guard row (t - 1) key edge
      let bbit := if hit then
        bit row t key (edge - 2) == xor (injected t key (edge - 1)) (injected t key edge)
        else x.testBit ((left - 2) % k)
      let abit := if hit then bit row t key (edge - 3) == injected t key edge
        else x.testBit ((left - 3) % k)
      let next := guard row t key (edge - 3 + hit.toNat)
      let digit := hit.toNat + 2 * bbit.toNat + 4 * abit.toNat + 8 * next.toNat
      (st.1 + delta digit, st.2 ||| (digit <<< (4 * j)))) (0, 0)).2
  ∀ (a : Nat) (code : Fin (16 ^ a)), a ≤ pairs →
    (a = 0 ∨ d < prefixGain code.val (a - 1) + 3 * (pairs + 1 - a)) →
    let m := if a = pairs then prefixGain code.val a - d else 0
    let pivot := fun (pos : Nat) =>
      (List.range a).any (fun idx =>
        let before := prefixGain code.val idx
        let t := 5 + 2 * idx
        let l := q - 13 - 6 * idx + before + 3 - 2 * t
        let last := if code.val.testBit (4 * idx) then 4 else 5
        ([l, l - 2, l - 3, l - last] : List Nat).any (fun v => v % k == pos)) ||
      (List.range m).any (fun outputPos => (q + outputPos) % k == pos)
    ∀ (seed : Fin (2 ^ k)) (target : Fin (2 ^ m)),
    ∃ getKey : Fin (2 ^ k) → Fin (2 ^ k),
      (∀ u w : Fin (2 ^ k), w = getKey u ↔
        trace u.val w.val a = code.val ∧
        (∀ pos : Fin k, pivot pos.val = false →
          (rot 1 w.val ^^^ u.val).testBit pos.val = seed.val.testBit pos.val) ∧
        (state u.val r w.val >>> i) % 2 ^ m = target.val) ∧
      (∀ outBit : Fin k, ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack k C ∧
        C.size ≤ 128 * (k + 1) ^ 2 * (r + 1) ∧
        ∀ name : Fin (2 ^ k),
          C.eval ((List.range k).map (fun inputBit => name.val.testBit inputBit)) =
            (getKey name).val.testBit outBit.val) := by
  intro k r d i hr hk pairs hd hi him constant rot step state injected bit guard q delta prefixGain trace a code ha eligible m pivot seed target
  let L : Layout k := ⟨r,d,i,a,code.val,hr,hk,hd,hi,him,ha,code.isLt,eligible⟩
  let getKey := fun u : Fin (2^k) => Layout.inputWord u (Solver.run L.pv (L.err u constant target) seed L.N)
  refine ⟨getKey,?_,?_⟩
  · intro u w
    exact L.solutionIff u w constant target seed
      (Solver.certified L.pv (L.err u constant target) seed L.pivotInjective (L.mainTri u constant target))
  · intro j
    exact Gates39.build L constant target seed j
