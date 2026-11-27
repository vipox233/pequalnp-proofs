import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25504
import PEqualNP.Outside.L_meta_25522


namespace PEqualNP.Outside.L_meta_25550_aux.Builder
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
end PEqualNP.Outside.L_meta_25550_aux.Builder

namespace PEqualNP.Outside.L_meta_25550_aux.Builder.Bank

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

end PEqualNP.Outside.L_meta_25550_aux.Builder.Bank

namespace PEqualNP.Outside.L_meta_25550_aux
def hist50 : Nat → (Nat → Bool) → List Bool
  | 0,_ => []
  | t+1,f => f t :: hist50 t f
lemma histLen50 (t : Nat) (f : Nat→Bool) : (hist50 t f).length=t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [hist50,ih]
lemma histRev50 (t : Nat) (f : Nat→Bool) : (hist50 t f).reverse=(List.range t).map f := by
  induction t with
  | zero => rfl
  | succ t ih => simp [hist50,ih,List.range_succ]
lemma histGet50 (t : Nat) (f : Nat→Bool) (j : Nat) :
    (hist50 t f).reverse.getD j false = if j<t then f j else false := by
  rw [histRev50]
  by_cases h:j<t
  · rw [ite_eq_left h,List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [ite_eq_right h,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simp;omega)];rfl
end PEqualNP.Outside.L_meta_25550_aux


namespace PEqualNP.Outside.L_meta_25550_aux
namespace WordCoding
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
def encodeBits (k:Nat) (x:Nat→Bool) : Fin (2^k) :=
 ⟨(List.range k).foldl (fun z i => z ||| flipAt x i) 0, by
  apply Nat.lt_pow_two_of_testBit
  intro i h
  simp [packBit,show ¬i<k by omega]⟩

lemma encBit {k i:Nat} (h:i<k) (x:Nat→Bool) : (encodeBits k x).val.testBit i=x i := by
 simp [encodeBits,packBit,h]

end WordCoding

def low50 (k q : Nat) := k-(q+1)-1
def pack50 (k q x : Nat) := x % (2^low50 k q) + ((x.testBit (k-1)).toNat <<< low50 k q)
def at50 (k q ext : Nat) (hist : List Bool) (p : Nat) :=
  if p<low50 k q then ext.testBit p else if p=k-1 then ext.testBit (low50 k q) else
    hist.reverse.getD (k-2-p) false
def startWord50 {k q : Nat} (ext : Nat) (hist : List Bool) : Fin (2^k) :=
  WordCoding.encodeBits k (at50 k q ext hist)
lemma startAt50 {k q : Nat} (ext : Nat) (hist : List Bool) {p : Nat} (hp : p<k) :
    (startWord50 (k:=k) (q:=q) ext hist).val.testBit p=at50 k q ext hist p :=
  WordCoding.encBit hp _
lemma packBits50 (k q x j : Nat) :
    (pack50 k q x).testBit j =
      if j<low50 k q then x.testBit j else (decide (j=low50 k q) && x.testBit (k-1)) := by
  unfold pack50
  rw [Nat.shiftLeft_eq,Nat.mul_comm (x.testBit (k-1)).toNat,Nat.add_comm,
    Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
  by_cases h : j<low50 k q
  · simp [h,Nat.testBit_mod_two_pow]
  · simp only [h,ite_false,Nat.testBit_bool_toNat]
    have eq : j-low50 k q=0 ↔ j=low50 k q := by omega
    simp [eq,Bool.and_comm]
lemma packBound50 {k q : Nat} (room : q+2≤k) (x : Nat) : pack50 k q x<2^(k-(q+1)) := by
  have l : k-(q+1)=low50 k q+1 := by unfold low50;omega
  rw [l,pow_succ]
  have h := Nat.mod_lt x (Nat.two_pow_pos (low50 k q))
  unfold pack50
  cases x.testBit (k-1) <;> simp only [Bool.toNat_false,Bool.toNat_true,Nat.shiftLeft_eq,Nat.zero_mul,Nat.one_mul] <;> omega
lemma packStart50 {k q ext : Nat} (room : q+2≤k) (he : ext<2^(k-(q+1))) (hist : List Bool) :
    pack50 k q (startWord50 (k:=k) (q:=q) ext hist).val=ext := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [packBits50]
  have l : low50 k q<k-1 := by unfold low50;omega
  by_cases h:j<low50 k q
  · simp only [h,ite_true,startAt50 _ _ (by omega : j<k),at50]
  · rw [ite_eq_right h,startAt50 _ _ (by omega : k-1<k)]
    by_cases same:j=low50 k q
    · subst j;simp [at50,show ¬k-1<low50 k q by omega]
    · have e : ext<2^j := he.trans_le (Nat.pow_le_pow_right (by decide) (by unfold low50 at *;omega))
      simp [same,Nat.testBit_lt_two_pow e]
lemma historyAgree50 {k q : Nat} (room : q+2≤k) (x : Fin (2^k)) (d : Nat) (p : Nat) (hp : p<k)
    (known : p<low50 k q ∨ p=k-1 ∨ k-2-p<d) :
    (startWord50 (k:=k) (q:=q) (pack50 k q x.val)
      (hist50 d (fun t=>x.val.testBit (k-2-t)))).val.testBit p=x.val.testBit p := by
  rw [startAt50 _ _ hp]
  by_cases low:p<low50 k q
  · simp [at50,low,packBits50]
  · by_cases top : p=k-1
    · subst p
      simp [at50,low,packBits50]
    · have small : k-2-p<d := known.elim (fun h=>False.elim (low h)) (fun h=>h.elim (fun h=>False.elim (top h)) id)
      simp only [at50,low,top,ite_false,histGet50,small,ite_true]
      rw [show k-2-(k-2-p)=p by omega]
lemma startPack50 {k q : Nat} (room : q+2≤k) (x : Fin (2^k)) :
    startWord50 (k:=k) (q:=q) (pack50 k q x.val)
      (hist50 (q+1) (fun t=>x.val.testBit (k-2-t)))=x := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp:p<k
  · exact historyAgree50 room x _ p hp (by unfold low50;omega)
  · have hh : 2^k≤2^p := Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_lt_two_pow ((startWord50 (k:=k) (q:=q) _ _).isLt.trans_le hh)).trans (Nat.testBit_lt_two_pow (x.isLt.trans_le hh)).symm
lemma startAssigned50 {k q t : Nat} (room : q+2≤k) (ht : t≤q) (ext : Nat) (hist : List Bool) :
    (startWord50 (k:=k) (q:=q) ext hist).val.testBit (k-2-t)=hist.reverse.getD t false := by
  rw [startAt50 _ _ (by omega)]
  have lo : ¬(k-2-t<low50 k q) := by unfold low50;omega
  have top : k-2-t≠k-1 := by omega
  simp [at50,lo,top,show k-2-(k-2-t)=t by omega]
lemma histStart50 {k q : Nat} (room : q+2≤k) (ext : Nat) (hist : List Bool) (hlen : hist.length=q+1) :
    hist50 (q+1) (fun t=>(startWord50 (k:=k) (q:=q) ext hist).val.testBit (k-2-t))=hist := by
  apply List.reverse_inj.mp
  apply List.ext_getElem
  · simp [histLen50,hlen]
  · intro j hj hj'
    have h : j<q+1 := by simpa [hlen] using hj'
    rw [←List.getD_eq_getElem _ false hj,←List.getD_eq_getElem _ false hj',histGet50,ite_eq_left h,
      startAssigned50 room (by omega)]
end PEqualNP.Outside.L_meta_25550_aux



namespace PEqualNP.Outside.L_meta_25550_aux

def legal50 (x : Nat) : Prop := x &&& (x >>> 1) = 0

instance (x : Nat) : Decidable (legal50 x) := inferInstanceAs (Decidable (_ = _))

theorem legalBits50 (x : Nat) :
    legal50 x ↔ ∀ j, (x.testBit j && x.testBit (j+1)) = false := by
  constructor
  · intro h j
    have e := congrArg (fun z : Nat => z.testBit j) h
    simpa [Nat.testBit_and, Nat.testBit_shiftRight, Nat.add_comm] using e
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    simpa [Nat.testBit_and, Nat.testBit_shiftRight, Nat.add_comm] using h j

private lemma legalBit50 (b : Bool) (x : Nat) : legal50 (Nat.bit b x) ↔
    (b && x.testBit 0) = false ∧ legal50 x := by
  rw [legalBits50, legalBits50]
  constructor
  · intro h
    exact ⟨by simpa only [Nat.testBit_bit_zero,Nat.testBit_bit_succ] using h 0,
      fun j => by simpa only [Nat.testBit_bit_succ] using h (j+1)⟩
  · rintro ⟨h0,h⟩ (_|j)
    · simpa only [Nat.testBit_bit_zero,Nat.testBit_bit_succ] using h0
    · simpa only [Nat.testBit_bit_succ] using h j

private def labels50 (d : Nat) := (Finset.range (2^d)).filter legal50

private lemma memLabels50 (d x : Nat) : x ∈ labels50 d ↔ x < 2^d ∧ legal50 x := by
  simp [labels50]

private lemma cardAdd50 (d : Nat) :
    (labels50 (d+2)).card = (labels50 (d+1)).card + (labels50 d).card := by
  let e := Nat.bit false
  let o := fun x => Nat.bit true (Nat.bit false x)
  have ev (x : Nat) : e x = 2*x := rfl
  have od (x : Nat) : o x = 2*(2*x)+1 := rfl
  have injE : Function.Injective e := fun x y h => by simp only [ev] at h; omega
  have injO : Function.Injective o := by intro x y h; simp only [od] at h; omega
  have dis : Disjoint ((labels50 (d+1)).image e) ((labels50 d).image o) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y,_,he⟩ := Finset.mem_image.mp hz'
    simp only [ev,od] at he
    omega
  have sets : labels50 (d+2) = (labels50 (d+1)).image e ∪ (labels50 d).image o := by
    ext z
    rw [Finset.mem_union,memLabels50]
    constructor
    · rintro ⟨hz,hleg⟩
      cases z using Nat.bitCasesOn with
      | bit b y =>
        cases b
        · left
          refine Finset.mem_image.mpr ⟨y,(memLabels50 ..).mpr ⟨?_,(legalBit50 _ _).mp hleg |>.2⟩,rfl⟩
          simp only [pow_succ, Nat.bit_val] at hz ⊢
          omega
        · right
          have hl := (legalBit50 _ _).mp hleg
          cases y using Nat.bitCasesOn with
          | bit a x =>
            cases a
            · refine Finset.mem_image.mpr ⟨x,(memLabels50 ..).mpr ⟨?_,(legalBit50 _ _).mp hl.2 |>.2⟩,rfl⟩
              simp only [Nat.bit_val,pow_succ] at hz
              omega
            · simp at hl
    · rintro (hz|hz)
      · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨bound,leg⟩ := (memLabels50 ..).mp hx
        refine ⟨?_,(legalBit50 _ _).mpr ⟨rfl,leg⟩⟩
        simp only [ev,pow_succ] at bound ⊢
        omega
      · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨bound,leg⟩ := (memLabels50 ..).mp hx
        refine ⟨?_,(legalBit50 _ _).mpr ⟨by simp,(legalBit50 _ _).mpr ⟨rfl,leg⟩⟩⟩
        simp only [od,pow_succ]
        omega
  rw [sets,Finset.card_union_of_disjoint dis,Finset.card_image_of_injective _ injE,Finset.card_image_of_injective _ injO]

theorem fibLabels50 (d : Nat) :
    (Finset.univ.filter (fun a : Fin (2^d) => a.val &&& (a.val >>> 1) = 0)).card = Nat.fib (d+2) := by
  have eqc : (Finset.univ.filter (fun a : Fin (2^d) => a.val &&& (a.val >>> 1) = 0)).card =
      (labels50 d).card := by
    apply Finset.card_bij (fun a _ => a.val)
    · intro a ha; exact (memLabels50 ..).mpr ⟨a.isLt,(Finset.mem_filter.mp ha).2⟩
    · intro a ha b hb he; exact Fin.ext he
    · intro x hx
      obtain ⟨bound,leg⟩ := (memLabels50 ..).mp hx
      exact ⟨⟨x,bound⟩,Finset.mem_filter.mpr ⟨by simp,leg⟩,rfl⟩
  rw [eqc]
  clear eqc
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    match d with
    | 0 => decide
    | 1 => decide
    | t+2 =>
      rw [cardAdd50, ih (t+1) (by omega), ih t (by omega), Nat.fib_add_two (n:=t+2), show t+1+2=t+2+1 by omega]
      omega

end PEqualNP.Outside.L_meta_25550_aux


namespace PEqualNP.Outside.L_meta_25550_aux.Probe50
open PEqualNP.Outside.L_meta_25504_aux (first rot rnd rot_lt rot_testBit rnd_lt rnd_testBit)
open PEqualNP.Outside.L_meta_25550_aux.Builder
open PEqualNP.Outside.L_meta_25550_aux.Builder.Bank

abbrev RawWord (n k : Nat) := (Fin n → Bool) → Fin (2^k)
abbrev Present {n k : Nat} (B : Bank n) (W : RawWord n k) :=
  ∀ j : Fin k, B.Has (fun x => (W x).val.testBit j.val)

def rawKey (k row start : Nat) := rot k (k-1) (start ^^^ row)

private lemma undo {k s w : Nat} (hs : 0<s) (hsk : s<k) (hw : w<2^k) :
    rot k (k-s) (rot k s w)=w := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases h : j<k
  · rw [rot_testBit k (k-s) _ j (rot_lt ..) h,Nat.mod_eq_of_lt (by omega : k-s<k),
      show j+k-(k-s)=j+s by omega,rot_testBit k s w _ hw (Nat.mod_lt _ (by omega)),
      Nat.mod_eq_of_lt hsk,show (j+s) % k+k-s=(j+s) % k+(k-s) by omega,Nat.mod_add_mod,
      show j+s+(k-s)=j+k by omega,Nat.add_mod_right,Nat.mod_eq_of_lt h]
  · have pow : 2^k≤2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (rot_lt ..) pow),Nat.testBit_lt_two_pow (lt_of_lt_of_le hw pow)]

lemma start_key {k row start : Nat} (hk : 13≤k) (hr : row<2^k) (hs : start<2^k) :
    rot k 1 (rawKey k row start) ^^^ row=start := by
  have h := undo (k:=k) (s:=k-1) (by omega) (by omega) (Nat.xor_lt_two_pow hs hr)
  rw [show k-(k-1)=1 by omega] at h
  simp only [rawKey,h,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]

lemma key_start {k row w : Nat} (hk : 13≤k) (hw : w<2^k) :
    rawKey k row (rot k 1 w ^^^ row)=w := by
  simp only [rawKey,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
  exact undo (by decide) (by omega) hw

private def tri (a b c : Bool) := xor (xor a b) c
private def newBit (a b c d e y z salt : Bool) :=
  xor (xor (xor (tri b a c) (!(tri c b d) && tri d c e)) (xor y z)) salt

private lemma triEmit {n} {B : Bank n} {a b c : BitFn n} (ha : B.Has a) (hb : B.Has b) (hc : B.Has c) :
    B.Grow 8 (fun D => D.Has (fun x => tri (a x) (b x) (c x))) := by
  apply (xor2 ha hb).bind (b:=4)
  intro D e h
  exact xor2 h (e hc)

private lemma nextEmit {n} {B : Bank n} {a b c d e y z : BitFn n}
    (ha : B.Has a) (hb : B.Has b) (hc : B.Has c) (hd : B.Has d) (he : B.Has e)
    (hy : B.Has y) (hz : B.Has z) (salt : Bool) :
    B.Grow 39 (fun D => D.Has (fun x => newBit (a x) (b x) (c x) (d x) (e x) (y x) (z x) salt)) := by
  obtain ⟨D,f,cf,u⟩ := triEmit hb ha hc
  obtain ⟨E,g,cg,v⟩ := triEmit (f hc) (f hb) (f hd)
  obtain ⟨F,h,ch,w⟩ := triEmit (g (f hd)) (g (f hc)) (g (f he))
  obtain ⟨G,p,cp,bv⟩ := inv (h v)
  obtain ⟨H,q,cq,bw⟩ := meet bv (p w)
  obtain ⟨I,r,cr,body⟩ := xor2 (q (p (h (g u)))) bw
  obtain ⟨J,s,cs,key⟩ := xor2 (r (q (p (h (g (f hy)))))) (r (q (p (h (g (f hz))))))
  obtain ⟨M,t,ct,both⟩ := xor2 (s body) key
  obtain ⟨L,v,cv,out⟩ := xorConst both salt
  exact ⟨L,fun hx => v (t (s (r (q (p (h (g (f hx)))))))),by omega,out⟩

private def stage (k : Nat) (c : Nat → Fin (2^k)) (row start : Nat) : Nat → Nat
  | 0 => start
  | t+1 => rnd k (c (t+1)).val (rawKey k row start) (stage k c row start t) t

private lemma bounded {k} (c : Nat → Fin (2^k)) (row start : Nat) (hs : start<2^k) (t : Nat) :
    stage k c row start t<2^k := by
  cases t with
  | zero => exact hs
  | succ t => exact rnd_lt k (c (t+1)).val _ _ t (c (t+1)).isLt

private def cost : Nat → Nat
  | 0 => 0
  | s+1 => 5*cost s+39

private def neighbor {k} (i : Fin k) (p : Fin 5) : Fin k :=
  match p.val with
  | 0 => ⟨(i.val+k-1) % k,Nat.mod_lt _ (by have := i.isLt; omega)⟩
  | 1 => i
  | 2 => ⟨(i.val+1) % k,Nat.mod_lt _ (by have := i.isLt; omega)⟩
  | 3 => ⟨(i.val+2) % k,Nat.mod_lt _ (by have := i.isLt; omega)⟩
  | _ => ⟨(i.val+3) % k,Nat.mod_lt _ (by have := i.isLt; omega)⟩

private theorem stageEmit {k n} (hk : 13≤k) (U X : RawWord n k) (c : Nat → Fin (2^k)) (s : Nat) :
    ∀ (B : Bank n) (i : Fin k), Present B U → Present B X →
      B.Grow (cost s) (fun D => D.Has (fun x => (stage k c (U x).val (X x).val s).testBit i.val)) := by
  induction s with
  | zero =>
    intro B i hu hx
    exact Grow.pure B (hx i)
  | succ s ih =>
    intro B i hu hx
    let V := fun x => stage k c (U x).val (X x).val s
    let idx := (i.val+k-(2*s) % k) % k
    let src : Fin k := ⟨(idx+k-(k-1) % k) % k,Nat.mod_lt _ (by omega)⟩
    let bit := fun j : Fin 5 => fun x => (V x).testBit (neighbor i j).val
    obtain ⟨D,g,cg,w⟩ := B.collectFin 5 bit (cost s) (fun F e j =>
      ih F (neighbor i j) (fun p => e (hu p)) (fun p => e (hx p)))
    obtain ⟨E,h,ch,next⟩ := nextEmit (w 0) (w 1) (w 2) (w 3) (w 4) (g (hx src)) (g (hu src))
      ((c (s+1)).val.testBit i.val)
    refine ⟨E,fun a => h (g a),by dsimp [cost]; omega,?_⟩
    have eqn (x : Fin n → Bool) :
        (stage k c (U x).val (X x).val (s+1)).testBit i.val =
        newBit (bit 0 x) (bit 1 x) (bit 2 x) (bit 3 x) (bit 4 x)
          ((X x).val.testBit src.val) ((U x).val.testBit src.val) ((c (s+1)).val.testBit i.val) := by
      rw [stage,rnd_testBit k (c (s+1)).val (rawKey k (U x).val (X x).val)
        (stage k c (U x).val (X x).val s) s i.val hk (bounded c _ _ (X x).isLt s) (rot_lt ..) i.isLt]
      rw [rawKey,rot_testBit _ _ _ _ (Nat.xor_lt_two_pow (X x).isLt (U x).isLt) (Nat.mod_lt _ (by omega)),
        Nat.testBit_xor]
      rfl
    simpa only [eqn] using next

theorem probe {n k : Nat} (hk : 13≤k) (B : Bank n) (U X : RawWord n k)
    (c : Nat → Fin (2^k)) (i : Fin k) (hu : Present B U) (hx : Present B X) :
    B.Grow 1209 (fun D => D.Has (fun x =>
      (first k c (U x).val (rawKey k (U x).val (X x).val)).testBit i.val)) := by
  have eqn (x : Fin n → Bool) :
      first k c (U x).val (rawKey k (U x).val (X x).val) = stage k c (U x).val (X x).val 3 := by
    unfold first
    rw [start_key hk (U x).isLt (X x).isLt]
    rfl
  simp only [eqn]
  exact stageEmit hk U X c 3 B i hu hx

theorem rawBits {n k : Nat} (hk : 13≤k) (B : Bank n) (U X : RawWord n k)
    (hu : Present B U) (hx : Present B X) :
    B.Grow (4*k) (fun D => ∀ j : Fin k,
      D.Has (fun x => (rawKey k (U x).val (X x).val).testBit j.val)) := by
  rw [Nat.mul_comm 4 k]
  apply B.collectFin k _ 4
  intro D e j
  let z : Fin k := ⟨(j.val+k-(k-1) % k) % k,Nat.mod_lt _ (by omega)⟩
  have eqn (x : Fin n → Bool) : (rawKey k (U x).val (X x).val).testBit j.val =
      xor ((X x).val.testBit z.val) ((U x).val.testBit z.val) := by
    rw [rawKey,rot_testBit _ _ _ _ (Nat.xor_lt_two_pow (X x).isLt (U x).isLt) j.isLt,Nat.testBit_xor]
  simpa only [eqn] using xor2 (e (hx z)) (e (hu z))

theorem first_lt (k : Nat) (c : Nat → Fin (2^k)) (row w : Nat) :
    first k c row w<2^k := by
  exact rnd_lt k (c 3).val w _ 2 (c 3).isLt

end PEqualNP.Outside.L_meta_25550_aux.Probe50


namespace PEqualNP.Outside.L_meta_25550_aux

def fork50 (ok : List Bool → Bool) (p : List Bool) :=
  ok (false::p) && ok (true::p)

def prefer50 (q : Nat) (ok : List Bool → Bool) (t : Nat) (p : List Bool) :=
  if t=q then true else fork50 ok (false::p)

def label50 (q : Nat) (ok : List Bool → Bool) (t : Nat) (p : List Bool) (b : Bool) :=
  fork50 ok p && (b == prefer50 q ok t p)

def choose50 (q : Nat) (ok : List Bool → Bool) (t : Nat) (p : List Bool) (l : Bool) :=
  if fork50 ok p then l == prefer50 q ok t p else ok (true::p)

def walk50 (q : Nat) (ok : List Bool → Bool) (label : Nat → Bool) : Nat → List Bool
  | 0 => []
  | t+1 =>
    let p := walk50 q ok label t
    choose50 q ok t p (label t) :: p

def encode50 (q : Nat) (ok : List Bool → Bool) (w : Nat → Bool) (t : Nat) :=
  label50 q ok t (hist50 t w) (w t)

def canonical50 (q : Nat) (ok : List Bool → Bool) (l : Nat → Bool) : Prop :=
  ∀ t, t≤q → l t = true → fork50 ok (walk50 q ok l t) = true

theorem chooseLabel50 (q : Nat) (ok : List Bool → Bool) (t : Nat) (p : List Bool) (b : Bool)
    (feasible : ok (b::p) = true) :
    choose50 q ok t p (label50 q ok t p b) = b := by
  unfold choose50 label50 fork50
  cases b <;> cases h0 : ok (false::p) <;> cases h1 : ok (true::p) <;>
    cases prefer50 q ok t p <;> simp_all

theorem labelChoose50 (q : Nat) (ok : List Bool → Bool) (t : Nat) (p : List Bool)
    (l : Bool) (valid : l=true → fork50 ok p=true) :
    label50 q ok t p (choose50 q ok t p l) = l := by
  unfold choose50 label50
  cases hf : fork50 ok p <;> cases prefer50 q ok t p <;> cases l <;> simp_all

theorem walkLength50 (q : Nat) (ok : List Bool → Bool) (l : Nat → Bool) (t : Nat) :
    (walk50 q ok l t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [walk50,ih]

theorem walkEncode50 (q : Nat) (ok : List Bool → Bool) (w : Nat → Bool)
    (pass : ∀ t, t≤q → ok (w t :: hist50 t w)=true) :
    ∀ t, t≤q+1 → walk50 q ok (encode50 q ok w) t = hist50 t w := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [walk50,ih (by omega),hist50]
    change choose50 q ok t (hist50 t w) (label50 q ok t (hist50 t w) (w t)) :: _ = _
    rw [chooseLabel50 _ _ _ _ _ (pass t (by omega))]

theorem canonicalEncode50 (q : Nat) (ok : List Bool → Bool) (w : Nat → Bool)
    (pass : ∀ t, t≤q → ok (w t :: hist50 t w)=true) :
    canonical50 q ok (encode50 q ok w) := by
  intro t ht hl
  rw [walkEncode50 q ok w pass t (by omega)]
  simpa [encode50,label50] using (show fork50 ok (hist50 t w) = true from by
    change (_ && _) = true at hl
    simpa using (Bool.and_eq_true_iff.mp hl).1)

theorem uniqueWalk50 (q : Nat) (ok : List Bool → Bool) (w l : Nat → Bool)
    (valid : canonical50 q ok l) (he : walk50 q ok l (q+1)=hist50 (q+1) w) :
    ∀ t, t≤q → l t=encode50 q ok w t := by
  have back (n : Nat) (eqn : walk50 q ok l n=hist50 n w) :
      ∀ t, t<n → t≤q → l t=encode50 q ok w t := by
    induction n with
    | zero => omega
    | succ n ih =>
      change _ :: walk50 q ok l n = _ :: hist50 n w at eqn
      obtain ⟨head,tail⟩ := List.cons.inj eqn
      intro t ht tq
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with lt|rfl
      · exact ih tail t lt tq
      · unfold encode50
        rw [←tail,←head,labelChoose50 q ok t _ _ (valid t tq)]
  exact fun t ht => back _ he t (by omega) ht

def oddSquares50 (q : Nat) (ok : List Bool → Bool) : Prop :=
  ∀ t, t<q → ∀ p : List Bool, p.length=t →
    ¬(fork50 ok (false::p)=true ∧ fork50 ok (true::p)=true)

theorem adjacentEncode50 (q : Nat) (ok : List Bool → Bool) (odd : oddSquares50 q ok)
    (w : Nat → Bool) (t : Nat) (ht : t<q) :
    (encode50 q ok w t && encode50 q ok w (t+1))=false := by
  let p := hist50 t w
  have crit := odd t ht p (histLen50 _ _)
  have hs : t≠q := by omega
  change ((fork50 ok p && (w t == prefer50 q ok t p)) &&
    (fork50 ok (w t::p) && (w (t+1) == prefer50 q ok (t+1) (w t::p))))=false
  rw [prefer50,ite_eq_right hs]
  cases hb : w t <;> cases h0 : fork50 ok (false::p) <;> cases h1 : fork50 ok (true::p) <;> simp_all

theorem legalEncode50 (q : Nat) (ok : List Bool → Bool) (odd : oddSquares50 q ok)
    (w : Nat → Bool) (tag : Fin (2^(q+1))) (bits : ∀ i, i≤q → tag.val.testBit i=encode50 q ok w i) :
    legal50 tag.val := by
  apply (legalBits50 _).mpr
  intro i
  by_cases h : i<q
  · rw [bits i (by omega),bits (i+1) (by omega)]
    exact adjacentEncode50 q ok odd w i h
  · have off : tag.val.testBit (i+1)=false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le tag.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [off,Bool.and_false]

theorem walkCongr50 (q : Nat) (ok : List Bool → Bool) {a b : Nat → Bool} (n : Nat)
    (agree : ∀ t, t<n → a t=b t) : walk50 q ok a n=walk50 q ok b n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [walk50,walk50,ih (fun t h => agree t (by omega)),agree n (by omega)]

end PEqualNP.Outside.L_meta_25550_aux


namespace PEqualNP.Outside.L_meta_25550_aux
open PEqualNP.Outside.L_meta_25504_aux (first rot)

def ok50 (k h q : Nat) (c : Nat → Fin (2^k)) (u y ext : Nat) (p : List Bool) : Bool :=
  if p.length≤1 then true else
    let d := p.length-2
    let z := startWord50 (k:=k) (q:=q) ext p
    (first k c u (Probe50.rawKey k u z.val)).testBit (k-1-d) == y.testBit (h-1-d)

def original50 (k row key : Nat) := rot k 1 key ^^^ row

def wordPath50 (k x t : Nat) := x.testBit (k-2-t)

end PEqualNP.Outside.L_meta_25550_aux


namespace PEqualNP.Outside.L_meta_25550_aux
open PEqualNP.Outside.L_meta_25504_aux (first rot rot_lt)

def Address50 (k q : Nat) := Fin (2^(k-(q+1))) × Fin (2^(q+1))

def addressStart50 (k h q : Nat) (c : Nat → Fin (2^k)) (u y : Nat) (a : Address50 k q) :=
  startWord50 (k:=k) (q:=q) a.1.val (walk50 q (ok50 k h q c u y a.1.val) a.2.val.testBit (q+1))

def decode50 (k h q : Nat) (c : Nat → Fin (2^k)) (u y : Nat) (a : Address50 k q) :=
  Probe50.rawKey k u (addressStart50 k h q c u y a).val

def good50 (k h q : Nat) (c : Nat → Fin (2^k)) (u y : Nat) (a : Address50 k q) : Prop :=
  canonical50 q (ok50 k h q c u y a.1.val) a.2.val.testBit ∧
  first k c u (decode50 k h q c u y a) >>> (k-h) = y

theorem originalPass50 {k h q : Nat} (hk : 13≤k) (hh : h≤k) (hq : q ≤ min h (k-11))
    (c : Nat → Fin (2^k)) (u w : Fin (2^k)) (y : Nat)
    (pass : first k c u.val w.val >>> (k-h)=y) :
    let x := original50 k u.val w.val
    ∀ t, t≤q → ok50 k h q c u.val y (pack50 k q x)
      (wordPath50 k x t :: hist50 t (wordPath50 k x)) = true := by
  let X : Fin (2^k) := ⟨original50 k u.val w.val,Nat.xor_lt_two_pow (rot_lt ..) u.isLt⟩
  change ∀ t, t≤q → ok50 k h q c u.val y (pack50 k q X.val)
    (wordPath50 k X.val t :: hist50 t (wordPath50 k X.val)) = true
  intro t ht
  cases t with
  | zero => rfl
  | succ t =>
    let trial := startWord50 (k:=k) (q:=q) (pack50 k q X.val) (hist50 (t+2) (wordPath50 k X.val))
    let z : Fin (2^k) := ⟨Probe50.rawKey k u.val trial.val,rot_lt ..⟩
    have phase : ∀ j : Fin 12, (rot k 1 z.val ^^^ u.val).testBit ((k-1-t+k-2+j.val) % k) =
        (rot k 1 w.val ^^^ u.val).testBit ((k-1-t+k-2+j.val) % k) := by
      intro j
      change (rot k 1 (Probe50.rawKey k u.val trial.val) ^^^ u.val).testBit _ = X.val.testBit _
      rw [Probe50.start_key hk u.isLt trial.isLt]
      apply historyAgree50 (q:=q) (by omega) X (t+2)
      · exact Nat.mod_lt _ (by omega)
      · rw [show k-1-t+k-2+j.val = k-3-t+j.val+k by omega,Nat.add_mod_right]
        by_cases inside : k-3-t+j.val<k
        · rw [Nat.mod_eq_of_lt inside]
          omega
        · left
          rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by have := j.isLt;omega)]
          unfold low50
          have := j.isLt
          omega
    have loc := PEqualNP.Outside.L_meta_25504_aux.main k hk c (⟨k-1-t,by omega⟩ : Fin k)
      u z u w phase (fun _ => rfl)
    have out := congrArg (fun z : Nat => z.testBit (h-1-t)) pass
    simp only [Nat.testBit_shiftRight,show k-h+(h-1-t)=k-1-t by omega] at out
    simp only [ok50,List.length_cons,histLen50,show ¬t+1+1≤1 by omega,ite_false,
      show t+1+1-2=t by omega,beq_iff_eq]
    exact loc.trans out

theorem sound50 {k h q : Nat} (hk : 13≤k) (room : q+2≤k)
    (c : Nat → Fin (2^k)) (u : Fin (2^k)) (y : Nat) (a : Address50 k q)
    (odd : oddSquares50 q (ok50 k h q c u.val y a.1.val))
    (good : good50 k h q c u.val y a) :
    legal50 a.2.val ∧ decode50 k h q c u.val y a<2^k ∧
      pack50 k q (original50 k u.val (decode50 k h q c u.val y a))=a.1.val ∧
      first k c u.val (decode50 k h q c u.val y a) >>> (k-h) = y := by
  let ok := ok50 k h q c u.val y a.1.val
  let p := walk50 q ok a.2.val.testBit (q+1)
  let X := addressStart50 k h q c u.val y a
  have recovered : original50 k u.val (decode50 k h q c u.val y a)=X.val :=
    Probe50.start_key hk u.isLt X.isLt
  have he : hist50 (q+1) (wordPath50 k X.val)=p :=
    histStart50 room a.1.val p (walkLength50 ..)
  refine ⟨legalEncode50 q ok odd (wordPath50 k X.val) a.2 ?_,rot_lt ..,?_,good.2⟩
  · exact uniqueWalk50 q ok _ a.2.val.testBit good.1 he.symm
  · rw [recovered]
    exact packStart50 room a.1.isLt p

theorem complete50 {k h q : Nat} (hk : 13≤k) (hh : h≤k) (hq : q ≤ min h (k-11))
    (c : Nat → Fin (2^k)) (u w : Fin (2^k)) (y : Nat) (pass : first k c u.val w.val >>> (k-h)=y) :
    ∃! a : Address50 k q, good50 k h q c u.val y a ∧ decode50 k h q c u.val y a=w.val := by
  have room : q+2≤k := by omega
  let X : Fin (2^k) := ⟨original50 k u.val w.val,Nat.xor_lt_two_pow (rot_lt ..) u.isLt⟩
  let ext : Fin (2^(k-(q+1))) := ⟨pack50 k q X.val,packBound50 room _⟩
  let ok := ok50 k h q c u.val y ext.val
  let path := wordPath50 k X.val
  let tag := WordCoding.encodeBits (q+1) (encode50 q ok path)
  let a : Address50 k q := (ext,tag)
  have bit (t : Nat) (ht : t≤q) : tag.val.testBit t=encode50 q ok path t := WordCoding.encBit (by omega) _
  have passNodes : ∀ t, t≤q → ok (path t :: hist50 t path)=true := originalPass50 hk hh hq c u w y pass
  have walked (t : Nat) (ht : t≤q+1) : walk50 q ok tag.val.testBit t=hist50 t path :=
    (walkCongr50 q ok t (fun j hj => bit j (by omega))).trans (walkEncode50 q ok path passNodes t ht)
  have Xeq : addressStart50 k h q c u.val y a=X := by
    unfold addressStart50
    change startWord50 ext.val (walk50 q ok tag.val.testBit (q+1))=X
    rw [walked _ le_rfl]
    exact startPack50 room X
  have key : decode50 k h q c u.val y a=w.val := by
    rw [decode50,Xeq]
    exact Probe50.key_start hk w.isLt
  refine ⟨a,⟨⟨?_,key ▸ pass⟩,key⟩,?_⟩
  · intro t ht hl
    change fork50 ok (walk50 q ok tag.val.testBit t)=true
    rw [walked t (by omega)]
    have he := bit t ht
    change tag.val.testBit t=true at hl
    rw [hl] at he
    change true=(_ && _) at he
    exact (Bool.and_eq_true_iff.mp he.symm).1
  · rintro ⟨e,b⟩ ⟨candidate,keyMatch⟩
    let addr : Address50 k q := (e,b)
    let p := walk50 q (ok50 k h q c u.val y e.val) b.val.testBit (q+1)
    have dx : addressStart50 k h q c u.val y addr=X := by
      apply Fin.ext
      calc (addressStart50 k h q c u.val y addr).val =
          original50 k u.val (decode50 k h q c u.val y addr) :=
            (Probe50.start_key hk u.isLt (addressStart50 k h q c u.val y addr).isLt).symm
        _ = X.val := congrArg (original50 k u.val) keyMatch
    have ee : e=ext := by
      apply Fin.ext
      change e.val = pack50 k q X.val
      rw [←dx]
      exact (packStart50 room e.isLt p).symm
    subst e
    have hist : hist50 (q+1) path = p := by
      change hist50 (q+1) (wordPath50 k X.val) = _
      rw [←dx]
      exact histStart50 room ext.val p (walkLength50 ..)
    have uniq := uniqueWalk50 q ok path b.val.testBit candidate.1 hist.symm
    have be : b=tag := by
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases h : j≤q
      · exact (uniq j h).trans (bit j h).symm
      · have cap : 2^(q+1)≤2^j := Nat.pow_le_pow_right (by decide) (by omega)
        rw [Nat.testBit_lt_two_pow (b.isLt.trans_le cap),Nat.testBit_lt_two_pow (tag.isLt.trans_le cap)]
    exact congrArg (Prod.mk ext) be

end PEqualNP.Outside.L_meta_25550_aux

namespace PEqualNP.Outside.L_meta_25550_aux
open PEqualNP.Outside.L_meta_25504_aux (rot first rot_lt rot_testBit)
private lemma twoHeads (p : List Bool) (a b : Bool) (j : Nat) :
    (b::a::p).reverse.getD j false =
      if j=p.length then a else if j=p.length+1 then b else p.reverse.getD j false := by
  simp only [List.reverse_cons]
  by_cases lo : j<p.length
  · rw [List.getD_append _ _ _ _ (by simp;omega),List.getD_append _ _ _ _ (by simpa)]
    simp [show j≠p.length by omega,show j≠p.length+1 by omega]
  · by_cases eq:j=p.length
    · subst j
      rw [List.getD_append _ _ _ _ (by simp),List.getD_append_right _ _ _ _ (by simp)]
      simp
    · rw [List.getD_append_right _ _ _ _ (by simp;omega)]
      simp only [List.length_append,List.length_reverse,List.length_singleton]
      by_cases eq':j=p.length+1
      · subst j;simp
      · have z : 1≤j-(p.length+1) := by omega
        rw [ite_eq_right eq,ite_eq_right eq']
        simp only [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (show [b].length≤j-(p.length+1) from z),
          List.getElem?_eq_none (by simp;omega : p.reverse.length≤j)]

private def sw {k q} (ext : Nat) (p : List Bool) (a b : Bool) := startWord50 (k:=k) (q:=q) ext (b::a::p)
private lemma swBit {k q t : Nat} (room : q+2≤k) (ht : t<q) (ext : Nat) (p : List Bool) (len:p.length=t)
    (a b : Bool) (j : Nat) (hj : j<k) :
    (sw (k:=k) (q:=q) ext p a b).val.testBit j =
      xor (xor ((sw (k:=k) (q:=q) ext p false false).val.testBit j) (a && decide (j=k-2-t)))
        (b && decide (j=k-3-t)) := by
  simp only [sw,startAt50 _ _ hj,at50,twoHeads,len]
  by_cases lo : j<low50 k q
  · have e : j≠k-2-t := by unfold low50 at lo;omega
    have e' : j≠k-3-t := by unfold low50 at lo;omega
    simp [lo,e,e']
  · by_cases top : j=k-1
    · simp [lo,top,show k-1≠k-2-t by omega,show k-1≠k-3-t by omega]
    · simp only [lo,top,ite_false]
      have h1 : k-2-j=t ↔ j=k-2-t := by omega
      have h2 : k-2-j=t+1 ↔ j=k-3-t := by omega
      have ne : k-2-t≠k-3-t := by omega
      by_cases e:j=k-2-t <;> by_cases f:j=k-3-t <;> simp_all

private def sk {k q} (u ext : Nat) (p : List Bool) (a b : Bool) :=
  Probe50.rawKey k u (sw (k:=k) (q:=q) ext p a b).val

private lemma rawBit {k : Nat} (hk : 13≤k) (u z : Fin (2^k)) (j : Nat) (lo : j<k) :
    (Probe50.rawKey k u.val z.val).testBit j =
      xor (z.val.testBit ((j+1) % k)) (u.val.testBit ((j+1) % k)) := by
  unfold Probe50.rawKey
  rw [rot_testBit k (k-1) _ j (Nat.xor_lt_two_pow z.isLt u.isLt) lo,Nat.mod_eq_of_lt (by omega : k-1<k),
    show j+k-(k-1)=j+1 by omega,Nat.testBit_xor]
private lemma skToggle {k q t : Nat} (hk : 13≤k) (room : q+4≤k) (ht : t<q) (u : Fin (2^k))
    (ext : Nat) (p : List Bool) (len:p.length=t) (a b : Bool) :
    sk (k:=k) (q:=q) u.val ext p a b = sk (k:=k) (q:=q) u.val ext p false false ^^^
      (if b then 2^(k-4-t) else 0) ^^^ (if a then 2^(k-3-t) else 0) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_xor]
  by_cases h:j<k
  · simp only [sk,rawBit hk _ _ j h]
    rw [swBit (by omega : q+2≤k) ht ext p len a b _ (Nat.mod_lt _ (by omega))]
    have nxt {v : Nat} (vp : 0<v) (vl:v<k) : ((j+1) % k=v) ↔ j=v-1 := by
      by_cases z : j+1<k
      · rw [Nat.mod_eq_of_lt z];omega
      · have e:j+1=k := by omega
        simp [e,Nat.ne_of_lt vp];omega
    have eq1 := nxt (v:=k-2-t) (by omega) (by omega)
    have eq2 := nxt (v:=k-3-t) (by omega) (by omega)
    rw [show k-2-t-1=k-3-t by omega] at eq1
    rw [show k-3-t-1=k-4-t by omega] at eq2
    simp only [eq1,eq2]
    have perm : ∀ v u a b c d:Bool,
        xor (xor (xor v (a && c)) (b && d)) u = xor (xor (xor v u) (b && d)) (a && c) := by decide
    rw [perm]
    have mask (b : Bool) (s : Nat) : (if b then 2^s else 0).testBit j = (b && decide (j=s)) := by
      cases b <;> simp [Nat.testBit_two_pow,eq_comm]
    rw [mask,mask]
  · have hbit (a b : Bool) : (sk (k:=k) (q:=q) u.val ext p a b).testBit j=false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (rot_lt ..) (Nat.pow_le_pow_right (by decide) (by omega)))
    cases a <;> cases b <;> simp [hbit,Nat.testBit_two_pow,show k-4-t≠j by omega,show k-3-t≠j by omega]

lemma oddOfWord50 {k h q : Nat} (hq : q ≤ min h (k-11)) (hk : 13≤k) (c : Nat→Fin (2^k))
    (u : Fin (2^k)) (y ext : Nat) : oddSquares50 q (ok50 k h q c u.val y ext) := by
  intro t ht p len
  rintro ⟨bad0,bad1⟩
  have room : q+4≤k := by omega
  let K := sk (k:=k) (q:=q) u.val ext p
  let i : Fin k := ⟨k-1-t,by omega⟩
  let f := fun w=>(first k c u.val w).testBit i.val
  have ok (a b : Bool) : f (K a b)=y.testBit (h-1-t) := by
    have e : ok50 k h q c u.val y ext (b::a::p)=true := by
      cases a <;> cases b <;> first
        | exact (Bool.and_eq_true_iff.mp bad0).1 | exact (Bool.and_eq_true_iff.mp bad0).2
        | exact (Bool.and_eq_true_iff.mp bad1).1 | exact (Bool.and_eq_true_iff.mp bad1).2
    simpa [ok50,List.length_cons,len,K,sk,sw,i,f] using e
  let base : Fin (2^k) := ⟨K false false,rot_lt ..⟩
  have odd := PEqualNP.Outside.L_meta_25522 k hk c u base i
  let A := 2^(k-4-t)
  let B := 2^(k-3-t)
  have indexA : (i.val+k-3) % k=k-4-t := by
    change (k-1-t+k-3) % k=_
    rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)];omega
  have indexB : (i.val+k-2) % k=k-3-t := by
    change (k-1-t+k-2) % k=_
    rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)];omega
  change xor (xor (f (K false false)) (f (K false false ^^^ (2^((i.val+k-3) % k)))))
    (xor (f (K false false ^^^ (2^((i.val+k-2) % k)))) (f (K false false ^^^ (2^((i.val+k-3) % k)) ^^^ (2^((i.val+k-2) % k)))))=true at odd
  rw [indexA,indexB] at odd
  have e1 : K false true=K false false ^^^ A := by simpa [K,A] using skToggle hk room ht u ext p len false true
  have e2 : K true false=K false false ^^^ B := by simpa [K,B] using skToggle hk room ht u ext p len true false
  have e3 : K true true=K false false ^^^ A ^^^ B := by simpa [K,A,B] using skToggle hk room ht u ext p len true true
  change xor (xor (f (K false false)) (f (K false false ^^^ A))) (xor (f (K false false ^^^ B)) (f (K false false ^^^ A ^^^ B)))=true at odd
  rw [←e3,←e2,←e1,ok,ok,ok,ok] at odd
  simp at odd

end PEqualNP.Outside.L_meta_25550_aux



namespace PEqualNP.Outside.L_meta_25550_aux.Emit50
open PEqualNP.Outside.L_meta_25550_aux.Builder
open PEqualNP.Outside.L_meta_25550_aux.Builder.Bank
open Probe50 (Present RawWord)
variable {n k h q : Nat}

def check (q : Nat) (ok : List Bool → Bool) (label : Nat → Bool) : Nat → Bool
  | 0 => true
  | t+1 => check q ok label t && (!label t || fork50 ok (walk50 q ok label t))

theorem checkIff (q : Nat) (ok : List Bool → Bool) (label : Nat → Bool) :
    check q ok label (q+1)=true ↔ canonical50 q ok label := by
  have aux (t : Nat) : check q ok label t=true ↔
      ∀ i, i<t → label i=true → fork50 ok (walk50 q ok label i)=true := by
    induction t with
    | zero => simp [check]
    | succ t ih =>
      rw [check,Bool.and_eq_true_iff,ih]
      have last : (!label t || fork50 ok (walk50 q ok label t))=true ↔
          (label t=true → fork50 ok (walk50 q ok label t)=true) := by
        cases label t <;> simp
      rw [last]
      constructor
      · rintro ⟨before,atT⟩ i lt
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ lt) with lt|rfl
        · exact before i lt
        · exact atT
      · intro all
        exact ⟨fun i h => all i (by omega),all t (by omega)⟩
  simpa only [canonical50,Nat.lt_succ_iff] using aux (q+1)

abbrev Hist (n : Nat) := (Fin n → Bool) → List Bool
def HistHas (B : Bank n) (H : Hist n) := ∀ j : Nat, B.Has (fun x => (H x).reverse.getD j false)

lemma extendHist {B D : Bank n} (e : B.Ext D) {H : Hist n} (a : HistHas B H) : HistHas D H :=
  fun j => e (a j)

private lemma revCons (b : Bool) (l : List Bool) (j : Nat) :
    (b::l).reverse.getD j false = if j=l.length then b else l.reverse.getD j false := by
  rw [List.reverse_cons]
  simp only [List.getD_eq_getElem?_getD]
  rcases lt_trichotomy j l.length with hl|eq|hg
  · rw [ite_eq_right (by omega),List.getElem?_append_left (by simpa using hl)]
  · subst j
    rw [ite_eq_left rfl,List.getElem?_append_right (by simp)]
    simp
  · rw [ite_eq_right (by omega),List.getElem?_eq_none (by simp; omega),List.getElem?_eq_none (by simp; omega)]

lemma consHas {B : Bank n} {H : Hist n} {b : BitFn n} {t : Nat} (len : ∀ x, (H x).length=t)
    (wh : HistHas B H) (wb : B.Has b) : HistHas B (fun x => b x :: H x) := by
  intro j
  by_cases eq : j=t
  · simpa only [revCons,len,eq,ite_true] using wb
  · simpa only [revCons,len,ite_eq_right eq] using wh j

lemma wordHas {B : Bank n} (room : q+2≤k) (E : RawWord n (k-(q+1))) (e : Present B E)
    {H : Hist n} (wh : HistHas B H) :
    Present B (fun x => startWord50 (k:=k) (q:=q) (E x).val (H x)) := by
  intro p
  have l : low50 k q<k-(q+1) := by unfold low50; omega
  by_cases low : p.val<low50 k q
  · simpa only [startAt50 _ _ p.isLt,at50,ite_eq_left low] using e ⟨p.val,by omega⟩
  · by_cases top : p.val=k-1
    · simpa only [startAt50 _ _ p.isLt,at50,ite_eq_right low,ite_eq_left top] using e ⟨low50 k q,l⟩
    · simpa only [startAt50 _ _ p.isLt,at50,ite_eq_right low,ite_eq_right top] using wh (k-2-p.val)

lemma eqEmit {B : Bank n} {a b : BitFn n} (ha : B.Has a) (hb : B.Has b) :
    B.Grow 5 (fun D => D.Has (fun x => a x == b x)) := by
  obtain ⟨D,e,sz,h1⟩ := xor2 ha hb
  obtain ⟨E,f,sc,h2⟩ := inv h1
  refine ⟨E,fun v => f (e v),by omega,?_⟩
  simpa only [show ∀ a b : Bool, (a == b)=!(xor a b) by decide] using h2

lemma okEmit (hk : 13≤k) (hp : 0<h) (room : q+2≤k) (B : Bank n) (U : RawWord n k)
    (Y : RawWord n h) (E : RawWord n (k-(q+1))) (c : Nat → Fin (2^k))
    (hu : Present B U) (hy : Present B Y) (he : Present B E) (H : Hist n) {s : Nat}
    (len : ∀ x, (H x).length=s) (wh : HistHas B H) :
    B.Grow 1214 (fun D => D.Has (fun x => ok50 k h q c (U x).val (Y x).val (E x).val (H x))) := by
  by_cases short : s≤1
  · simp only [ok50,len,ite_eq_left short]
    exact (B.const true).weaken (show 1≤1214 by decide) (fun _ v => v)
  · let X := fun x => startWord50 (k:=k) (q:=q) (E x).val (H x)
    let i : Fin k := ⟨k-1-(s-2),by omega⟩
    let j : Fin h := ⟨h-1-(s-2),by omega⟩
    obtain ⟨D,e,sz,w⟩ := Probe50.probe hk B U X c i hu (wordHas room E he wh)
    obtain ⟨F,f,sc,v⟩ := eqEmit w (e (hy j))
    exact ⟨F,fun a => f (e a),by omega,by simpa only [ok50,len,ite_eq_right short] using v⟩

lemma muxEmit {B : Bank n} {a b c : BitFn n} (ha : B.Has a) (hb : B.Has b) (hc : B.Has c) :
    B.Grow 4 (fun D => D.Has (fun x => if a x then b x else c x)) := by
  obtain ⟨D,e,sz,u⟩ := inv ha
  obtain ⟨E,f,sc,v⟩ := meet (e ha) (e hb)
  obtain ⟨F,g,sf,w⟩ := meet (f u) (f (e hc))
  obtain ⟨G,z,sg,y⟩ := join (g v) w
  refine ⟨G,fun h => z (g (f (e h))),by omega,?_⟩
  simpa only [show ∀ a b c : Bool, (if a then b else c)=((a && b) || (!a && c)) by decide] using y

end PEqualNP.Outside.L_meta_25550_aux.Emit50


namespace PEqualNP.Outside.L_meta_25550_aux.Emit50
open PEqualNP.Outside.L_meta_25550_aux.Builder
open PEqualNP.Outside.L_meta_25550_aux.Builder.Bank
open Probe50 (RawWord Present)
variable {n k h q : Nat}

private def corner (j : Fin 4) (p : List Bool) : List Bool :=
  match j.val with
  | 0 => false::p
  | 1 => true::p
  | 2 => false::false::p
  | _ => true::false::p

private abbrev testFn (k h q : Nat) (c : Nat → Fin (2^k)) (U : RawWord n k)
    (Y : RawWord n h) (E : RawWord n (k-(q+1))) (x : Fin n → Bool) :=
  ok50 k h q c (U x).val (Y x).val (E x).val

private lemma layer (hk : 13≤k) (hp : 0<h) (room : q+2≤k) (B : Bank n) (U : RawWord n k)
    (Y : RawWord n h) (E : RawWord n (k-(q+1))) (T : RawWord n (q+1)) (c : Nat → Fin (2^k))
    (hu : Present B U) (hy : Present B Y) (he : Present B E) (ht : Present B T)
    (fBit : B.Has (fun _ => false)) (tBit : B.Has (fun _ => true)) (t : Nat) (bound : t≤q)
    (H : Hist n) (len : ∀ x, (H x).length=t) (hist : HistHas B H) (acc : BitFn n) (wa : B.Has acc) :
    B.Grow 4900 (fun D =>
      D.Has (fun x => choose50 q (testFn k h q c U Y E x) t (H x) ((T x).val.testBit t)) ∧
      D.Has (fun x => acc x && (!((T x).val.testBit t) || fork50 (testFn k h q c U Y E x) (H x)))) := by
  let ok := testFn k h q c U Y E
  let label := fun x => (T x).val.testBit t
  have labelWire : B.Has label := ht ⟨t,by omega⟩
  have fH : HistHas B (fun x => false::H x) := consHas len hist fBit
  have tH : HistHas B (fun x => true::H x) := consHas len hist tBit
  have lenF (x) : (false::H x).length=t+1 := by simp [len]
  have stage (D : Bank n) (e : B.Ext D) (j : Fin 4) :
      D.Grow 1214 (fun G => G.Has (fun x => ok x (corner j (H x)))) := by
    have test (L : Hist n) (s : Nat) (lenL : ∀ x, (L x).length=s) (hL : HistHas B L) :=
      okEmit hk hp room D U Y E c (fun i => e (hu i)) (fun i => e (hy i)) (fun i => e (he i))
        L lenL (extendHist e hL)
    fin_cases j
    · exact test _ _ lenF fH
    · exact test _ (t+1) (fun x => by change (true::H x).length=_; simp [len]) tH
    · exact test _ (t+2) (fun x => by change (false::false::H x).length=_; simp [len])
        (consHas lenF fH fBit)
    · exact test _ (t+2) (fun x => by change (true::false::H x).length=_; simp [len])
        (consHas lenF fH tBit)
  obtain ⟨D,d,sd,w⟩ := B.collectFin 4 (fun j x => ok x (corner j (H x))) 1214 stage
  obtain ⟨F,f,sf,hpref⟩ := meet (w 2) (w 3)
  have pref : F.Has (fun x => prefer50 q (ok x) t (H x)) := by
    by_cases done : t=q
    · simpa only [prefer50,ite_eq_left done] using f (d tBit)
    · simp only [prefer50,ite_eq_right done,fork50]
      exact hpref
  obtain ⟨G,g,sg,fork⟩ := meet (f (w 0)) (f (w 1))
  have hfork : G.Has (fun x => fork50 (ok x) (H x)) := fork
  obtain ⟨I,i,si,compared⟩ := eqEmit (g (f (d labelWire))) (g pref)
  obtain ⟨J,j,sj,choice⟩ := muxEmit (i hfork) compared (i (g (f (w 1))))
  obtain ⟨K,z,sk,nolabel⟩ := inv (j (i (g (f (d labelWire)))))
  obtain ⟨L,l,sl,valid⟩ := join nolabel (z (j (i hfork)))
  obtain ⟨M,m,sm,all⟩ := meet (l (z (j (i (g (f (d wa))))))) valid
  exact ⟨M,fun z0 => m (l (z (j (i (g (f (d z0))))))),by omega,m (l (z choice)),all⟩

theorem build (hk : 13≤k) (hp : 0<h) (room : q+2≤k) (B : Bank n) (U : RawWord n k)
    (Y : RawWord n h) (E : RawWord n (k-(q+1))) (T : RawWord n (q+1)) (c : Nat → Fin (2^k))
    (hu : Present B U) (hy : Present B Y) (he : Present B E) (ht : Present B T) :
    B.Grow (2+4900*(q+1)) (fun D =>
      Present D (fun x => startWord50 (k:=k) (q:=q) (E x).val
        (walk50 q (ok50 k h q c (U x).val (Y x).val (E x).val) (T x).val.testBit (q+1))) ∧
      D.Has (fun x => check q (ok50 k h q c (U x).val (Y x).val (E x).val) (T x).val.testBit (q+1))) := by
  let ok := testFn k h q c U Y E
  let H := fun t x => walk50 q (ok x) (T x).val.testBit t
  let acc := fun t x => check q (ok x) (T x).val.testBit t
  obtain ⟨C,d,sd,wF⟩ := B.const false
  obtain ⟨D,e,se,wT⟩ := C.const true
  have steps (t : Nat) (bound : t≤q+1) : D.Grow (4900*t) (fun F => HistHas F (H t) ∧ F.Has (acc t)) := by
    induction t with
    | zero =>
      refine ⟨D,fun v => v,by omega,?_,wT⟩
      intro j
      simpa only [H,walk50,List.reverse_nil,List.getD_nil] using e wF
    | succ t ih =>
      obtain ⟨F,f,sf,hist,ha⟩ := ih (by omega)
      have len (x) : (H t x).length=t := walkLength50 .. 
      obtain ⟨G,g,sg,head,good⟩ := layer hk hp room F U Y E T c
        (fun i => f (e (d (hu i)))) (fun i => f (e (d (hy i)))) (fun i => f (e (d (he i))))
        (fun i => f (e (d (ht i)))) (f (e wF)) (f wT) t (by omega) (H t) len hist (acc t) ha
      have size : G.gates.length≤D.gates.length+4900*(t+1) := by
        rw [Nat.mul_succ]
        exact le_trans sg (by omega)
      refine ⟨G,fun v => g (f v),size,?_,?_⟩
      · exact consHas len (extendHist g hist) head
      · change G.Has (fun x => acc t x && (!((T x).val.testBit t) || fork50 (ok x) (H t x)))
        exact good
  obtain ⟨F,f,sf,hist,good⟩ := steps (q+1) le_rfl
  have size : F.gates.length≤B.gates.length+(2+4900*(q+1)) := le_trans sf (by omega)
  refine ⟨F,fun v => f (e (d v)),size,?_,?_⟩
  · exact wordHas room E (fun p => f (e (d (he p)))) hist
  · exact good

end PEqualNP.Outside.L_meta_25550_aux.Emit50


namespace PEqualNP.Outside.L_meta_25550_aux
open PEqualNP.Outside.L_meta_25504_aux (first)
open PEqualNP.Outside.L_meta_25550_aux.Builder
open Bank
open Probe50

private def match50 {k h n : Nat} (U X : RawWord n k) (Y : RawWord n h) (c : Nat→Fin (2^k))
    (j : Fin h) (x : Fin n→Bool) :=
  (first k c (U x).val (rawKey k (U x).val (X x).val)).testBit (k-h+j.val) == (Y x).val.testBit j.val

private theorem readHigh50 {k h n : Nat} (hk : 13≤k) (hh : h≤k) (B : Bank n)
    (U X : RawWord n k) (Y : RawWord n h) (c : Nat→Fin (2^k))
    (hu : Present B U) (hx : Present B X) (hy : Present B Y) :
    B.Grow (1+1215*h) (fun D => ∃ flag : BitFn n, D.Has flag ∧ ∀ x, flag x=true ↔
      first k c (U x).val (rawKey k (U x).val (X x).val) >>> (k-h)=(Y x).val) := by
  have emit (D : Bank n) (ext : B.Ext D) (j : Fin h) :
      D.Grow 1214 (fun F=>F.Has (match50 U X Y c j)) := by
    obtain ⟨E,p,cp,h0⟩ := probe hk D U X c (⟨k-h+j.val,by omega⟩ : Fin k)
      (fun i=>ext (hu i)) (fun i=>ext (hx i))
    obtain ⟨F,q,cq,h1⟩ := Emit50.eqEmit h0 (p (ext (hy j)))
    exact ⟨F,fun a=>q (p a),by omega,h1⟩
  obtain ⟨D,e,ce,hflag⟩ := B.allSlots (List.finRange h) (match50 U X Y c) 1214
    (fun D ext j _=>emit D ext j)
  refine ⟨D,e,by simp at ce;omega,_,hflag,?_⟩
  intro x
  simp only [List.all_eq_true,List.mem_finRange,true_implies,match50,beq_iff_eq]
  let v := first k c (U x).val (rawKey k (U x).val (X x).val)
  change (∀ i : Fin h, v.testBit (k-h+i.val)=(Y x).val.testBit i.val) ↔ v >>> (k-h)=(Y x).val
  constructor
  · intro bits
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_shiftRight]
    by_cases inw : i<h
    · exact bits ⟨i,inw⟩
    · have vb : v<2^k := first_lt .. 
      have a := vb.trans_le (Nat.pow_le_pow_right (by decide) (by omega : k≤k-h+i))
      have b := (Y x).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega : h ≤ i))
      rw [Nat.testBit_lt_two_pow a,Nat.testBit_lt_two_pow b]
  · intro eq i
    have h' := congrArg (fun w : Nat=>w.testBit i.val) eq
    simpa only [Nat.testBit_shiftRight] using h'

theorem finishGate50 {k h q n : Nat} (hk : 13≤k) (hh : h≤k) (hq : q ≤ min h (k-11))
    (B : Bank n) (U : RawWord n k) (Y : RawWord n h) (E : RawWord n (k-(q+1))) (T : RawWord n (q+1))
    (c : Nat→Fin (2^k)) (hu : Present B U) (hy : Present B Y)
    (built : B.Grow (2+4900*(q+1)) (fun D=>
      Present D (fun x=>addressStart50 k h q c (U x).val (Y x).val (E x,T x)) ∧
      ∃ flag : BitFn n, D.Has flag ∧ ∀ x, flag x=true ↔
        canonical50 q (ok50 k h q c (U x).val (Y x).val (E x).val) (T x).val.testBit)) :
    B.Grow (8192*(k+1)) (fun D=>
      (∃ flag : BitFn n,D.Has flag ∧ ∀ x, flag x=true ↔ good50 k h q c (U x).val (Y x).val (E x,T x)) ∧
      ∀ j : Fin k, D.Has (fun x=>(decode50 k h q c (U x).val (Y x).val (E x,T x)).testBit j.val)) := by
  let X := fun x=>addressStart50 k h q c (U x).val (Y x).val (E x,T x)
  obtain ⟨D,d,cd,pres,flag,hf,prop⟩ := built
  obtain ⟨J,j,cj,bits⟩ := rawBits hk D U X (fun i=>d (hu i)) pres
  obtain ⟨F,f,cf,high,hH,hEq⟩ := readHigh50 hk hh J U X Y c
    (fun i=>j (d (hu i))) (fun i=>j (pres i)) (fun i=>j (d (hy i)))
  obtain ⟨M,m,cm,final⟩ := meet (f (j hf)) hH
  refine ⟨M,fun a=>m (f (j (d a))),by omega,⟨_,final,?_⟩,fun i=>m (f (bits i))⟩
  intro x
  exact Bool.and_eq_true_iff.trans (and_congr (prop x) (hEq x))

end PEqualNP.Outside.L_meta_25550_aux


namespace PEqualNP.Outside.L_meta_25550_aux.Shell50

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_25550_aux.Builder
open Probe50

abbrev N (k h o t : Nat) := k+h+o+t

def block {n width : Nat} (port : Fin width → Fin n) : RawWord n width :=
  fun x => WordCoding.encodeBits width (fun p => if hp : p<width then x (port ⟨p,hp⟩) else false)

theorem blockBit {n width} (port : Fin width → Fin n) (x : Fin n → Bool) (i : Fin width) :
    (block port x).val.testBit i.val = x (port i) := by
  simp [block,WordCoding.encBit i.isLt,i.isLt]

theorem blockPresent {n width} (port : Fin width → Fin n) : Present (Bank.empty n) (block port) := by
  intro i
  simpa only [blockBit] using Bank.input (port i)

def row (k h o t : Nat) : RawWord (N k h o t) k :=
  block (fun i => ((i.castAdd h).castAdd o).castAdd t)
def target (k h o t : Nat) : RawWord (N k h o t) h :=
  block (fun i => ((i.natAdd k).castAdd o).castAdd t)
def exterior (k h o t : Nat) : RawWord (N k h o t) o :=
  block (fun i => (i.natAdd (k+h)).castAdd t)
def label (k h o t : Nat) : RawWord (N k h o t) t :=
  block (fun i => i.natAdd (k+h+o))

theorem inputPresent (k h o t : Nat) :
    let B := Bank.empty (N k h o t)
    Present B (row k h o t) ∧ Present B (target k h o t) ∧
    Present B (exterior k h o t) ∧ Present B (label k h o t) :=
  ⟨blockPresent _,blockPresent _,blockPresent _,blockPresent _⟩

def inputVec50 {k h o t : Nat}
    (u : Fin (2^k)) (y : Fin (2^h)) (a : Fin (2^o)) (l : Fin (2^t)) : Fin (N k h o t) → Bool :=
  Fin.append (Fin.append (Fin.append (fun i : Fin k => u.val.testBit i.val)
    (fun i : Fin h => y.val.testBit i.val)) (fun i : Fin o => a.val.testBit i.val))
    (fun i : Fin t => l.val.testBit i.val)

def dataBits50 (width number : Nat) := List.ofFn (fun i : Fin width => number.testBit i.val)

theorem inputList50 {k h o t} (u : Fin (2^k)) (y : Fin (2^h)) (a : Fin (2^o)) (l : Fin (2^t)) :
    List.ofFn (inputVec50 u y a l) =
      dataBits50 k u.val ++ dataBits50 h y.val ++ dataBits50 o a.val ++ dataBits50 t l.val := by
  simp [inputVec50,List.ofFn_fin_append,dataBits50]

private theorem finiteBits {k} (x y : Fin (2^k)) (low : ∀ j : Fin k, x.val.testBit j.val=y.val.testBit j.val) : x=y := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj:j<k
  · exact low ⟨j,hj⟩
  · have p : 2^k≤2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (x.isLt.trans_le p),Nat.testBit_lt_two_pow (y.isLt.trans_le p)]

theorem inputWords50 {k h o t} (u : Fin (2^k)) (y : Fin (2^h)) (a : Fin (2^o)) (l : Fin (2^t)) :
    let x := inputVec50 u y a l
    row k h o t x=u ∧ target k h o t x=y ∧ exterior k h o t x=a ∧ label k h o t x=l := by
  dsimp only
  refine ⟨finiteBits _ _ ?_,finiteBits _ _ ?_,finiteBits _ _ ?_,finiteBits _ _ ?_⟩ <;>
    intro j <;> simp [row,target,exterior,label,blockBit,inputVec50]

theorem foldBits50 {k} (w : Fin (2^k)) :
    (List.finRange k).foldl (fun a j => a ||| ((w.val.testBit j.val).toNat <<< j.val)) 0=w.val := by
  have mapped : (List.finRange k).map Fin.val = List.range k := by
    apply List.ext_getElem <;> simp
  have eq : (List.finRange k).foldl (fun a j => a ||| ((w.val.testBit j.val).toNat <<< j.val)) 0 =
      (List.range k).foldl (fun a j => a ||| WordCoding.flipAt w.val.testBit j) 0 := by
    rw [←mapped,List.foldl_map]
    rfl
  rw [eq]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [WordCoding.packBit]
  by_cases p : j<k
  · simp [p]
  · have pw : 2^k≤2^j := Nat.pow_le_pow_right (by decide) (by omega)
    simp [p,Nat.testBit_lt_two_pow (w.isLt.trans_le pw)]

theorem finish50 {n k : Nat} {B : Bank n} {flag : BitFn n} {key : RawWord n k}
    (hf : B.Has flag) (hk : Present B key) :
    ∃ (C : Circuit) (keyWire : Fin k → Nat),
      FanInTwo C ∧ ReadsBack n C ∧ C.size=B.gates.length ∧ C.output<n+C.size ∧
      (∀ j, keyWire j<n+C.size) ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = flag x ∧
        (List.finRange k).foldl (fun a j =>
          a ||| ((((C.wires (List.ofFn x)).getD (keyWire j) false).toNat) <<< j.val)) 0=(key x).val := by
  obtain ⟨output,outputBound,eval⟩:=hf
  choose keyWire keyBound keyBit using hk
  let C : Circuit := ⟨B.gates,output⟩
  refine ⟨C,keyWire,B.fan,B.back,rfl,outputBound,keyBound,fun x=>⟨eval x,?_⟩⟩
  have e (j : Fin k) : (C.wires (List.ofFn x)).getD (keyWire j) false=(key x).val.testBit j.val := keyBit j x
  simp only [e,foldBits50]

end PEqualNP.Outside.L_meta_25550_aux.Shell50

namespace PEqualNP.Outside.L_meta_25550_aux

open Shell50 Probe50
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_25550_aux.Builder
open PEqualNP.Outside.L_meta_25504_aux (first rot_lt)

abbrev GateResult50 (k h q : Nat) (c : Nat → Fin (2^k)) : Prop :=
  let o := k-(q+1)
  let t := q+1
  (Bank.empty (N k h o t)).Grow (8192*(k+1)) (fun D =>
    (∃ flag : BitFn (N k h o t), D.Has flag ∧ ∀ x, flag x=true ↔
      good50 k h q c (row k h o t x).val (target k h o t x).val (exterior k h o t x,label k h o t x)) ∧
    ∀ j : Fin k, D.Has (fun x=>
      (decode50 k h q c (row k h o t x).val (target k h o t x).val (exterior k h o t x,label k h o t x)).testBit j.val))

def data50 {k h q} (u : Fin (2^k)) (y : Fin (2^h)) (a : Address50 k q) :=
  dataBits50 k u.val ++ dataBits50 h y.val ++ dataBits50 (k-(q+1)) a.1.val ++ dataBits50 (q+1) a.2.val

def wireDecode50 {k} (C : Circuit) (keyWire : Fin k → Nat) (data : List Bool) :=
  (List.finRange k).foldl (fun result pos =>
    result ||| (((C.wires data).getD (keyWire pos) false).toNat <<< pos.val)) 0

theorem realize50 {k h q : Nat} (c : Nat → Fin (2^k)) (build : GateResult50 k h q c) :
    let n := N k h (k-(q+1)) (q+1)
    ∃ (C : Circuit) (wire : Fin k → Nat), FanInTwo C ∧ ReadsBack n C ∧
      C.size≤8192*(k+1) ∧ C.output<n+C.size ∧ (∀ j, wire j<n+C.size) ∧
      ∀ (u : Fin (2^k)) (y : Fin (2^h)) (a : Address50 k q),
        (C.eval (data50 u y a)=true ↔ good50 k h q c u.val y.val a) ∧
        wireDecode50 C wire (data50 u y a)=decode50 k h q c u.val y.val a := by
  let o := k-(q+1)
  let t := q+1
  let n := N k h o t
  obtain ⟨B,_,bound,⟨flag,hf,hfg⟩,hg⟩:=build
  let key : RawWord n k := fun x=>
    ⟨decode50 k h q c (row k h o t x).val (target k h o t x).val (exterior k h o t x,label k h o t x),rot_lt ..⟩
  obtain ⟨C,wire,fan,back,size,out,wb,correct⟩:=finish50 (key:=key) hf hg
  refine ⟨C,wire,fan,back,?_,out,wb,?_⟩
  · rw [size]
    simpa only [Bank.empty,List.length_nil,Nat.zero_add] using bound
  · intro u y a
    let x := inputVec50 u y a.1 a.2
    have hu := inputWords50 u y a.1 a.2
    obtain ⟨r,v,e,l⟩:=hu
    have de : List.ofFn x = data50 u y a := inputList50 u y a.1 a.2
    obtain ⟨eval,fold⟩:=correct x
    rw [←de,eval,hfg]
    change (_ ↔ _) ∧ wireDecode50 C wire (List.ofFn x)=_
    change wireDecode50 C wire (List.ofFn x)=decode50 k h q c
      (row k h o t x).val (target k h o t x).val (exterior k h o t x,label k h o t x) at fold
    change row k h o t x=u at r
    change target k h o t x=y at v
    change exterior k h o t x=a.1 at e
    change label k h o t x=a.2 at l
    rw [r,v,e,l] at fold ⊢
    exact ⟨Iff.rfl,fold⟩

theorem outer50
    (gate : ∀ (k h : Nat), 13≤k → 0<h → h≤k → ∀ c : Nat→Fin (2^k), GateResult50 k h (min h (k-11)) c)
    (odd : ∀ {k h q : Nat}, 13≤k → q ≤ min h (k-11) → ∀ (c : Nat→Fin (2^k)) (u : Fin (2^k)) (y ext : Nat),
      oddSquares50 q (ok50 k h q c u.val y ext)) :
    ∀ (k h : Nat), 13 ≤ k → 0 < h → h ≤ k → ∀ c : Nat → Fin (2 ^ k),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc j =>
      acc ||| ((xor (word.testBit j)
        (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0
  let start := fun (row key : Nat) => rot 1 key ^^^ row
  let first := fun (row key : Nat) =>
    (List.range 3).foldl (fun prev roundIndex =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * roundIndex) key ^^^ (c (roundIndex + 1)).val)
      (start row key)
  let q := min h (k - 11)
  let outside := k - (q + 1)
  let Address := Fin (2 ^ outside) × Fin (2 ^ (q + 1))
  let legal := fun (label : Nat) => label &&& (label >>> 1) = 0
  let bits := fun (width number : Nat) =>
    List.ofFn (fun place : Fin width => number.testBit place.val)
  let pack := fun (starting : Nat) =>
    starting % (2 ^ (outside - 1)) +
      ((starting.testBit (k - 1)).toNat <<< (outside - 1))
  let inputs := k + h + outside + (q + 1)
  (Finset.univ.filter (fun tag : Fin (2 ^ (q + 1)) => legal tag.val)).card =
    Nat.fib (q + 3) ∧
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (keyWire : Fin k → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
    C.size ≤ 8192 * (k + 1) ∧ C.output < inputs + C.size ∧
    (∀ j, keyWire j < inputs + C.size) ∧
    ∀ (u : Fin (2 ^ k)) (y : Fin (2 ^ h)),
      let dataIn := fun (address : Address) =>
        bits k u.val ++ bits h y.val ++ bits outside address.1.val ++ bits (q + 1) address.2.val
      let good := fun (offer : Address) => C.eval (dataIn offer) = true
      let decode := fun (slot : Address) =>
        let wires := C.wires (dataIn slot)
        (List.finRange k).foldl (fun result pos =>
          result ||| ((wires.getD (keyWire pos) false).toNat <<< pos.val)) 0
      (∀ candidate : Address, good candidate →
        legal candidate.2.val ∧ decode candidate < 2 ^ k ∧
        pack (start u.val (decode candidate)) = candidate.1.val ∧
        (first u.val (decode candidate) >>> (k - h)) = y.val) ∧
      (∀ w : Fin (2 ^ k), (first u.val w.val >>> (k - h)) = y.val →
        ∃! witness : Address, good witness ∧ decode witness = w.val) := by
  intro k h hk hp hh c
  let q := min h (k-11)
  have room : q+2≤k := by dsimp [q];omega
  obtain ⟨C,keyWire,fan,back,size,out,wb,spec⟩:=realize50 c (gate k h hk hp hh c)
  refine ⟨fibLabels50 (q+1),C,keyWire,fan,back,size,out,wb,?_⟩
  intro u y
  change (∀ a : Address50 k q, C.eval (data50 u y a)=true →
    legal50 a.2.val ∧ wireDecode50 C keyWire (data50 u y a)<2^k ∧
    pack50 k q (original50 k u.val (wireDecode50 C keyWire (data50 u y a)))=a.1.val ∧
    first k c u.val (wireDecode50 C keyWire (data50 u y a)) >>> (k-h)=y.val) ∧
    (∀ w : Fin (2^k), first k c u.val w.val >>> (k-h)=y.val →
      ∃! a : Address50 k q, C.eval (data50 u y a)=true ∧ wireDecode50 C keyWire (data50 u y a)=w.val)
  constructor
  · intro a ha
    rw [(spec u y a).2]
    exact sound50 hk room c u y.val a (odd hk (le_refl _) c u y.val a.1.val) ((spec u y a).1.mp ha)
  · intro w pass
    simpa only [fun a => (spec u y a).1,fun a => (spec u y a).2] using complete50 hk hh (q:=q) (le_refl _) c u w y.val pass

end PEqualNP.Outside.L_meta_25550_aux

namespace PEqualNP.Outside.L_meta_25550_aux
open Shell50 Probe50
open PEqualNP.Outside.L_meta_25550_aux.Builder

theorem gate50 (k h : Nat) (hk : 13≤k) (hp : 0<h) (hh : h≤k) (c : Nat→Fin (2^k)) :
    GateResult50 k h (min h (k-11)) c := by
  let q := min h (k-11)
  let o := k-(q+1)
  let B := Bank.empty (N k h o (q+1))
  let U := row k h o (q+1)
  let Y := target k h o (q+1)
  let E := exterior k h o (q+1)
  let T := label k h o (q+1)
  obtain ⟨hu,hy,he,ht⟩ := inputPresent k h o (q+1)
  apply finishGate50 (q:=q) hk hh (le_refl _) B U Y E T c hu hy
  have room : q+2≤k := by dsimp [q]; omega
  obtain ⟨D,f,sz,wx,wc⟩ := Emit50.build hk hp room B U Y E T c hu hy he ht
  exact ⟨D,f,sz,wx,_,wc,fun x=>Emit50.checkIff ..⟩

end PEqualNP.Outside.L_meta_25550_aux

open PEqualNP.Outside.L_meta_25550_aux in
theorem PEqualNP.Outside.L_meta_25550 : ∀ (k h : Nat), 13 ≤ k → 0 < h → h ≤ k → ∀ c : Nat → Fin (2 ^ k),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc j =>
      acc ||| ((xor (word.testBit j)
        (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0
  let start := fun (row key : Nat) => rot 1 key ^^^ row
  let first := fun (row key : Nat) =>
    (List.range 3).foldl (fun prev roundIndex =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * roundIndex) key ^^^ (c (roundIndex + 1)).val)
      (start row key)
  let q := min h (k - 11)
  let outside := k - (q + 1)
  let Address := Fin (2 ^ outside) × Fin (2 ^ (q + 1))
  let legal := fun (label : Nat) => label &&& (label >>> 1) = 0
  let bits := fun (width number : Nat) =>
    List.ofFn (fun place : Fin width => number.testBit place.val)
  let pack := fun (starting : Nat) =>
    starting % (2 ^ (outside - 1)) +
      ((starting.testBit (k - 1)).toNat <<< (outside - 1))
  let inputs := k + h + outside + (q + 1)
  (Finset.univ.filter (fun tag : Fin (2 ^ (q + 1)) => legal tag.val)).card =
    Nat.fib (q + 3) ∧
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (keyWire : Fin k → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
    C.size ≤ 8192 * (k + 1) ∧ C.output < inputs + C.size ∧
    (∀ j, keyWire j < inputs + C.size) ∧
    ∀ (u : Fin (2 ^ k)) (y : Fin (2 ^ h)),
      let dataIn := fun (address : Address) =>
        bits k u.val ++ bits h y.val ++ bits outside address.1.val ++ bits (q + 1) address.2.val
      let good := fun (offer : Address) => C.eval (dataIn offer) = true
      let decode := fun (slot : Address) =>
        let wires := C.wires (dataIn slot)
        (List.finRange k).foldl (fun result pos =>
          result ||| ((wires.getD (keyWire pos) false).toNat <<< pos.val)) 0
      (∀ candidate : Address, good candidate →
        legal candidate.2.val ∧ decode candidate < 2 ^ k ∧
        pack (start u.val (decode candidate)) = candidate.1.val ∧
        (first u.val (decode candidate) >>> (k - h)) = y.val) ∧
      (∀ w : Fin (2 ^ k), (first u.val w.val >>> (k - h)) = y.val →
        ∃! witness : Address, good witness ∧ decode witness = w.val) :=
  outer50 gate50 (fun hk hq c u y ext => oddOfWord50 hq hk c u y ext)
