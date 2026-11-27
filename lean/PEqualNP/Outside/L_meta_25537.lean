import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25537_aux.Builder
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
end PEqualNP.Outside.L_meta_25537_aux.Builder

namespace PEqualNP.Outside.L_meta_25537_aux.Builder.Bank

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

lemma anyBits {α : Type} {B : Bank n} (l : List α) (f : α → BitFn n)
    (h : ∀ i ∈ l, B.Has (f i)) :
    B.Grow (1+l.length) (fun D => D.Has (fun x => l.any (fun i => f i x))) := by
  simpa using anySlots B l f 0 (fun D e i hi => Grow.pure D (e (h i hi)))

end PEqualNP.Outside.L_meta_25537_aux.Builder.Bank

namespace PEqualNP.Outside.L_meta_25537_aux
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
end PEqualNP.Outside.L_meta_25537_aux

namespace PEqualNP.Outside.L_meta_25537_aux
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
end PEqualNP.Outside.L_meta_25537_aux

namespace PEqualNP.Outside.L_meta_25537_aux
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

lemma roundBound {k dist shift C w state : Nat} (hC:C<2^k) : round k dist shift C w state<2^k :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepBound ..) (Nat.mod_lt _ (by positivity))) hC

end Eval
end PEqualNP.Outside.L_meta_25537_aux

namespace PEqualNP.Outside.L_meta_25537_aux.Eval
open Builder Builder.Bank
variable {n k : Nat}

def highIndices (k low:Nat) := (List.range k).filter (low ≤ ·)
lemma highEq {k low v:Nat} (bv:v<2^k) :
    (!(highIndices k low).any (fun i=>v.testBit i)) = decide (v<2^low) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true',List.any_eq_false,decide_eq_true_eq]
  constructor
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    by_cases small:i<k
    · simpa using h i (by simp [highIndices,small,hi])
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le bv (Nat.pow_le_pow_right (by decide) (by omega)))
  · intro h i hi
    have hlo:low ≤ i:=by simpa [highIndices] using (List.mem_filter.mp hi).2
    simp [Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hlo))]

lemma testHigh {B:Bank n} {W:Word n} (low:Nat) (h:HasWord k B W) (bw:∀x,W x<2^k) :
    B.Grow (k+2) (fun D=>D.Has (fun x=>decide (W x<2^low))) := by
  have emit (i:Nat) (hi:i∈highIndices k low) : B.Has (fun x=>(W x).testBit i) := by
    have ilt:i<k:=List.mem_range.mp (List.mem_filter.mp hi).1
    simpa only [bits,idxNat ilt] using h i
  obtain ⟨D,e,de,hD⟩:=anyBits (highIndices k low) (fun i x=>(W x).testBit i) emit
  obtain ⟨E,f,ef,v⟩:=inv hD
  have ln:(highIndices k low).length≤k:=by simpa [highIndices] using
    (List.length_filter_le (fun i:Nat=>decide (low ≤ i)) (List.range k))
  refine ⟨E,fun h=>f (e h),by omega,?_⟩
  simpa only [highEq (bw _)] using v

end PEqualNP.Outside.L_meta_25537_aux.Eval

namespace PEqualNP.Outside.L_meta_25537_aux.Guard502

def rowWord (k t w u : Nat) :=
  (List.range t).foldl (fun state j =>
    Eval.round k 1 (2*j) (3^(k+(j+1))%2^k) w state) (rot k 1 w ^^^ u)

def colSteps (k r t w v : Nat) :=
  (List.range t).foldl (fun state j =>
    Eval.round k 2 (3*(j+1)+1) (3^(k+(r+(j+1)))%2^k) w state) (rot k 3 w ^^^ v)

def colWord (k r w v : Nat) := colSteps k r r w v

end PEqualNP.Outside.L_meta_25537_aux.Guard502

namespace PEqualNP.Outside.L_meta_25537_aux.Name
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

end PEqualNP.Outside.L_meta_25537_aux.Name

namespace PEqualNP.Outside.L_meta_25537_aux
open PEqualNP.Outside.L_meta_25537_aux.Builder
open Bank

private theorem collectSumList {n : Nat} {α : Type} (B : Bank n) (l : List α) (f : α → BitFn n) (cost : α → Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i ∈ l, D.Grow (cost i) (fun E => E.Has (f i))) :
    B.Grow (l.map cost).sum (fun D => ∀ i ∈ l, D.Has (f i)) := by
  induction l with
  | nil => simpa using (Grow.pure B (p:=fun D => ∀ i ∈ ([] : List α), D.Has (f i)) (by simp))
  | cons a l ih =>
    obtain ⟨D,e,c,p⟩ := ih (fun D e i hi => emit D e i (by simp [hi]))
    obtain ⟨E,e',c',v⟩ := emit D e a (by simp)
    refine ⟨E,fun h => e' (e h),by simp;omega,?_⟩
    intro i hi
    rcases List.mem_cons.mp hi with rfl|hin
    · exact v
    · exact e' (p i hin)

theorem collectSum {n m : Nat} (B : Bank n) (f : Fin m → BitFn n) (cost : Fin m → Nat)
    (emit : ∀ D : Bank n, B.Ext D → ∀ i, D.Grow (cost i) (fun E => E.Has (f i))) :
    B.Grow (∑ i, cost i) (fun D => ∀ i, D.Has (f i)) := by
  have h := collectSumList B (List.finRange m) f cost (fun D e i _ => emit D e i)
  have eqn : ((List.finRange m).map cost).sum = ∑ i, cost i := by
    rw [←List.sum_ofFn]
    congr 1
    apply List.ext_getElem <;> simp
  simpa [eqn] using h

end PEqualNP.Outside.L_meta_25537_aux

namespace PEqualNP.Outside.L_meta_25537_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_25537_aux.Builder
open PEqualNP.Outside.L_meta_25537_aux.Builder.Bank

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

lemma copyProj {n : Nat} (B : Bank n) (C : Circuit) {k : Nat}
    (π : (Fin n→Bool)→Fin k→Bool) (hf : FanInTwo C) (_hr : ReadsBack k C)
    (ins : ∀ j : Fin k, B.Has (fun x => π x j)) (zero : B.Has (fun _=>false)) :
    B.Grow C.size (fun D => D.Has (fun x=>C.eval (List.ofFn (π x)))) := by
  let val (gs : List Gate) (i : Nat) := fun x => wire gs i (π x)
  have make (gs : List Gate) (good : ∀ g ∈ gs, Good g) :
      B.Grow gs.length (fun D => ∀ i, D.Has (val gs i)) := by
    induction gs using List.reverseRecOn with
    | nil =>
      apply Grow.pure
      intro i
      by_cases hi : i<k
      · have eqn : val [] i = (fun x => π x ⟨i,hi⟩) := by
          funext x
          simp [val,wire,Circuit.wires,List.getD_eq_getElem?_getD,hi]
        rw [eqn]; exact ins ⟨i,hi⟩
      · have eqn : val [] i = (fun _ => false) := by
          funext x
          simp [val,wire,Circuit.wires,List.getD_eq_getElem?_getD,hi]
        rw [eqn]; exact zero
    | append_singleton gs g ih =>
      obtain ⟨D,e,c,h⟩ := ih (fun z hz => good z (by simp [hz]))
      obtain ⟨E,f,d,t⟩ := copyOne D g (good g (by simp)) (val gs) h
      refine ⟨E,fun a=>f (e a),by simp;omega,?_⟩
      intro j
      by_cases hl : j<k+gs.length
      · have eqn : val (gs++[g]) j = val gs j := by
          funext x; simp [val,wirePush,hl]
        rw [eqn]; exact f (h j)
      · by_cases hj : j=k+gs.length
        · have eqn : val (gs++[g]) j = (fun x=>g.op.eval (g.inputs.map fun i=>val gs i x)) := by
            funext x; simp [val,wirePush,hl,hj]
          rw [eqn]; exact t
        · have eqn : val (gs++[g]) j = (fun _ => false) := by
            funext x; simp [val,wirePush,hl,hj]
          rw [eqn]; exact f (e zero)
  obtain ⟨D,e,c,h⟩ := make C.gates hf
  exact ⟨D,e,c,h C.output⟩

end PEqualNP.Outside.L_meta_25537_aux

namespace PEqualNP.Outside.L_meta_25537_aux
open PEqualNP.Outside.L_meta_25537_aux
open Builder Builder.Bank Eval Guard502
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

abbrev NamesIn (k : Nat) := Fin (k+k) → Bool
def rowFin (k : Nat) (x : NamesIn k) : Fin (2^k) := ⟨Name.row k x,Name.nameLt _ x⟩
def slotWord {k slots : Nat} (keyAt : Fin slots → Fin (2^k) → Fin (2^k)) (s : Fin slots)
    (x : NamesIn k) := (keyAt s (rowFin k x)).val
def accept (k r w : Nat) (x : NamesIn k) :=
  decide (rowWord k r w (Name.row k x)<2^(k-(k+1)/2)) &&
  decide (colWord k r w (Name.col k x)<2^(k-(k+1)/2))

lemma rowInput (k : Nat) (x : NamesIn k) :
    List.ofFn (fun j : Fin k => x (Fin.castAdd k j)) =
    (List.range k).map (fun j => (rowFin k x).val.testBit j) := by
  apply List.ext_getElem
  · simp
  · intro i hl hr
    have hi : i<k := by simpa using hl
    simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]
    exact (Name.nameBit (fun j : Fin k => Fin.castAdd k j) x ⟨i,hi⟩).symm

lemma anyEq {k r slots : Nat} (keyAt : Fin slots → Fin (2^k) → Fin (2^k))
    (cover : ∀ row w : Fin (2^k), rowWord k r w.val row.val < 2^(k-(k+1)/2) →
      ∃ s, keyAt s row=w) (x : NamesIn k) :
    (List.finRange slots).any (fun s => accept k r (slotWord keyAt s x) x) =
      (List.range (2^k)).any (fun w => accept k r w x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,List.mem_finRange,List.mem_range,true_and]
  constructor
  · rintro ⟨s,hs⟩
    exact ⟨slotWord keyAt s x,(keyAt s _).isLt,hs⟩
  · rintro ⟨w,hw,ha⟩
    have hpass : rowWord k r w (Name.row k x)<2^(k-(k+1)/2) :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp ha).1
    obtain ⟨s,hs⟩ := cover (rowFin k x) ⟨w,hw⟩ hpass
    exact ⟨s,by simpa only [slotWord,hs] using ha⟩

end PEqualNP.Outside.L_meta_25537_aux

namespace PEqualNP.Outside.L_meta_25537_aux.V37
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

def walk (k t d initial : Nat) (shift salt : Nat → Nat) (w u : Nat) : Nat :=
  (List.range t).foldl (fun x j => round k d (shift j) (3^(k+salt j)%2^k) w x) (rot k initial w ^^^ u)

lemma extendWalk (k t d initial : Nat) (sh salt : Nat → Nat) (w u : Nat) :
    walk k (t+1) d initial sh salt w u = round k d (sh t) (3^(k+salt t)%2^k) w (walk k t d initial sh salt w u) := by
  simp [walk,List.range_succ,List.foldl_append]

lemma walkBound (k t d initial : Nat) (sh salt : Nat → Nat) (w u : Nat) (bu : u<2^k) :
    walk k t d initial sh salt w u < 2^k := by
  cases t with
  | zero => exact Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) bu
  | succ t => rw [extendWalk];exact roundBound (Nat.mod_lt _ (by positivity))

lemma emitWalk {W U : Word n} (hk:0<k) (t d initial : Nat) (sh salt : Nat → Nat)
    (hw : HasWord k B W) (hu : HasWord k B U) (bw : ∀x,W x<2^k) (bu : ∀x,U x<2^k) :
    B.Grow (4*k+19*k*t) (fun D => HasWord k D (fun x => walk k t d initial sh salt (W x) (U x))) := by
  induction t with
  | zero =>
    simpa [walk,Nat.mul_comm] using xorWords hk (rotAny initial hk hw bw) hu
  | succ t ih =>
    obtain ⟨D,e,de,p⟩ := ih
    obtain ⟨E,f,ef,q⟩ := roundAny hk d (sh t) (3^(k+salt t)%2^k) (wordLift e hw) p bw (fun x => walkBound _ _ _ _ _ _ _ _ (bu x))
    refine ⟨E,fun v => f (e v),?_,?_⟩
    · rw [Nat.mul_succ];omega
    · simpa only [extendWalk] using q

lemma verify {W U V : Word n} (hk : 0<k) (r low : Nat)
    (hw : HasWord k B W) (hu : HasWord k B U) (hv : HasWord k B V)
    (bw : ∀x,W x<2^k) (bu : ∀x,U x<2^k) (bv : ∀x,V x<2^k) :
    B.Grow (38*k*r+10*k+5) (fun D => D.Has (fun x =>
      decide (Guard502.rowWord k r (W x) (U x)<2^low) && decide (Guard502.colWord k r (W x) (V x)<2^low))) := by
  obtain ⟨D,e,de,a⟩ := emitWalk hk r 1 1 (fun j => 2*j) (fun j => j+1) hw hu bw bu
  obtain ⟨E,f,ef,u⟩ := testHigh low a (fun x => walkBound _ _ _ _ _ _ _ _ (bu x))
  obtain ⟨F,g,fg,b⟩ := emitWalk hk r 2 3 (fun j => 3*(j+1)+1) (fun j => r+(j+1)) (wordLift f (wordLift e hw))
    (wordLift f (wordLift e hv)) bw bv
  obtain ⟨G,h,hg,v⟩ := testHigh low b (fun x => walkBound _ _ _ _ _ _ _ _ (bv x))
  obtain ⟨H,i,ih,p⟩ := meet (h (g u)) v
  refine ⟨H,fun v => i (h (g (f (e v)))),?_,p⟩
  simp only [Nat.mul_assoc] at *
  omega
end PEqualNP.Outside.L_meta_25537_aux.V37

namespace PEqualNP.Outside.L_meta_25537_aux
open PEqualNP.Outside.L_meta_25537_aux
open Builder Builder.Bank Eval Guard502
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem build37 (k r slots : Nat) (hk : 0<k) (hs : 0<slots)
    (keyAt : Fin slots → Fin (2^k) → Fin (2^k)) (part : Fin slots → Fin k → Circuit)
    (cover : ∀ row w : Fin (2^k), rowWord k r w.val row.val < 2^(k-(k+1)/2) →
      ∃ s,keyAt s row=w)
    (parts : ∀ s j, FanInTwo (part s j) ∧ ReadsBack k (part s j) ∧
      ∀ row : Fin (2^k), (part s j).eval ((List.range k).map fun i => row.val.testBit i) =
        (keyAt s row).val.testBit j.val) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack (k+k) C ∧
      C.size ≤ (∑ s, ∑ j, (part s j).size) + slots*(64*(k+1)*(r+1)) ∧
      ∀ x, C.eval (List.ofFn x)=(List.range (2^k)).any (fun w=>accept k r w x) := by
  let init := Bank.empty (k+k)
  let price (s : Fin slots) := ∑ j : Fin k, (part s j).size
  let budget := 38*k*r + 10*k + 5
  let f (s : Fin slots) (x : NamesIn k) := accept k r (slotWord keyAt s x) x
  obtain ⟨B,e,de,zero⟩ := init.const false
  have oneSlot (D : Bank (k+k)) (ext : B.Ext D) (s : Fin slots) :
      D.Grow (price s+budget) (fun E => E.Has (f s)) := by
    let W := slotWord keyAt s
    have getBit (E : Bank (k+k)) (ed : D.Ext E) (j : Fin k) :
        E.Grow (part s j).size (fun F => F.Has (fun x => (W x).testBit j.val)) := by
      let proj := fun (x : NamesIn k) (i : Fin k) => x (Fin.castAdd k i)
      obtain ⟨F,fe,cf,hv⟩ := copyProj E (part s j) proj (parts s j).1 (parts s j).2.1
        (fun i => ed (ext (e (Bank.input (Fin.castAdd k i))))) (ed (ext zero))
      refine ⟨F,fe,cf,?_⟩
      have eqn (x : NamesIn k) : (part s j).eval (List.ofFn (proj x)) = (W x).testBit j.val := by
        rw [show List.ofFn (proj x) = _ from rowInput k x]
        exact (parts s j).2.2 (rowFin k x)
      simpa only [eqn] using hv
    obtain ⟨E,a,ec,key⟩ := collectSum D (fun j x => (W x).testBit j.val) (fun j => (part s j).size) getBit
    have ew := fromFin hk key
    have row (i : Int) := a (ext (e (Name.nameSig (k:=k) hk (fun j => Fin.castAdd k j) i)))
    have col (i : Int) := a (ext (e (Name.nameSig (k:=k) hk (fun j => Fin.natAdd k j) i)))
    obtain ⟨F,b,fc,v⟩ := V37.verify hk r (k-(k+1)/2) ew row col
      (fun x=>(keyAt s (rowFin k x)).isLt) (Name.nameLt _) (Name.nameLt _)
    exact ⟨F,fun h=>b (a h),by dsimp [price,budget];omega,v⟩
  obtain ⟨D,d,cd,wires⟩ := collectSum B f (fun s => price s+budget) oneSlot
  obtain ⟨E,a,ce,t⟩ := anyBits (List.finRange slots) f (fun s _=>wires s)
  have sumCost : (∑ s : Fin slots, (price s+budget)) = (∑ s,price s) + slots*budget := by
    simp [Finset.sum_add_distrib,Nat.nsmul_eq_mul]
  have gap : budget+3≤64*(k+1)*(r+1) := by dsimp [budget];nlinarith [Nat.zero_le (k*r)]
  have mp := Nat.mul_le_mul_left slots gap
  rw [Nat.mul_add] at mp
  have total : E.gates.length ≤ (∑ s, ∑ j, (part s j).size) + slots*(64*(k+1)*(r+1)) := by
    rw [sumCost] at cd
    change B.gates.length ≤ 0+1 at de
    simp only [List.length_finRange] at ce
    change E.gates.length ≤ (∑ s,price s)+ _
    omega
  obtain ⟨idx,ilt,correct⟩ := t
  refine ⟨⟨E.gates,idx⟩,E.fan,E.back,total,?_⟩
  intro x
  exact (correct x).trans (anyEq keyAt cover x)
end PEqualNP.Outside.L_meta_25537_aux

open PEqualNP.Outside.L_meta_25537_aux in
theorem PEqualNP.Outside.L_meta_25537 : ∀ (k r slots : Nat), 0 < k → 0 < slots →
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
  ∀ (keyAt : Fin slots → Fin (2 ^ k) → Fin (2 ^ k))
    (part : Fin slots → Fin k → PEqualNP.CircuitLowerBounds.Circuit),
    (∀ (row w : Fin (2 ^ k)), first w.val row.val < 2 ^ (k - h) →
      ∃ s : Fin slots, keyAt s row = w) →
    (∀ (s : Fin slots) (b : Fin k),
      PEqualNP.MetaComplexity.FanInTwo (part s b) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack k (part s b) ∧
      ∀ row : Fin (2 ^ k),
        (part s b).eval ((List.range k).map (fun inputPos => row.val.testBit inputPos)) =
          (keyAt s row).val.testBit b.val) →
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + k) C ∧
    C.size ≤ (∑ s : Fin slots, ∑ b : Fin k, (part s b).size) +
      slots * (64 * (k + 1) * (r + 1)) ∧
    ∀ bits : Fin (k + k) → Bool,
      C.eval (List.ofFn bits) = PEqualNP.Represents.adjFun (k := k) (l := k) graph bits := by
  intro k r slots hk hs
  dsimp only
  intro keyAt part cover parts
  exact build37 k r slots hk hs keyAt part cover parts
