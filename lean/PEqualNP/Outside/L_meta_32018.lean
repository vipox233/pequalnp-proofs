import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25620

namespace PEqualNP.Outside.L_meta_32018_aux
-- Uses the local two-round reduction from L-meta-25620, Git blob 72bf134da57c2f69a03aff5e77d53764e37bfca4, and the earlier L-lib-529 packing lemma from PR 40623.
namespace G32018
def x3 (a b c:Bool):Bool:=xor (xor a b) c
def model (a b c al be de f4 f5:Bool) (j:Nat):Bool:=
  if j=6 then xor al a else if j=7 then xor be (!a && b)
  else if j=8 then xor de ((a==b) && c) else if j=4 then f4 else f5
def localValue (D:Nat → Bool) (inj:Bool):Bool :=
  xor (xor (x3 (D 4) (D 5) (D 6)) (!(x3 (D 5) (D 6) (D 7)) && x3 (D 6) (D 7) (D 8))) inj
def gate (a b c D J:Bool):Bool :=
  xor (xor (!a) ((a||b) && (xor (xor a (!a && b)) (xor ((a==b)&&c) D)))) J



theorem local_gate (a b c al be de f4 f5 inj:Bool)
    (one:xor f4 f5= !al) (two:f4=be) :
    localValue (model a b c al be de f4 f5) inj=gate a b c (x3 al be de) inj := by
  subst f4
  cases a <;> cases b <;> cases c <;> cases al <;> cases be <;> cases de <;> cases f5 <;> cases inj <;>
    simp_all [localValue,model,gate,x3]

theorem derivative (a b c D J:Bool) : xor (gate a b c D J) (gate a b (!c) D J)=(a&&b) := by
  cases a <;>cases b <;>cases c <;>cases D <;>cases J <;>rfl

def code (a b c:Bool):Nat:=a.toNat+2*b.toNat+4*c.toNat
theorem code_bits (a b c:Bool) : (code a b c).testBit 0=a ∧ (code a b c).testBit 1=b ∧ (code a b c).testBit 2=c := by
  cases a <;>cases b <;>cases c <;>decide

def bitAt (s:Nat) (D J:Bool):Bool:=gate (s.testBit 0) (s.testBit 1) (s.testBit 2) D J
def parity (s q:Nat):Bool:=x3 (s.testBit 0 && q.testBit 0) (s.testBit 1 && q.testBit 1) (s.testBit 2 && q.testBit 2)
def sgn (v:Bool):Int:=if v then -1 else 1
def coeff (D J:Bool) (q:Nat):Int:=
  ((List.range 8).map fun s=>sgn (xor (bitAt s D J) (parity s q))).sum

def heavy (D:Bool):Nat:=if D then 1 else 2
theorem bounded (D J:Bool) (q:Nat) (lt:q < 8) :
    (coeff D J q)^2 = if q=heavy D then 36 else 4 := by
  have vals:q=0∨q=1∨q=2∨q=3∨q=4∨q=5∨q=6∨q=7:=by omega
  rcases vals with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>cases D <;>cases J <;>decide

end G32018

namespace G32018.Keys

def rotFn (k s word : Nat) : Nat :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
theorem rotFn_testBit {k s word i : Nat} (hk : 0 < k) (hw : word < 2 ^ k) (hi : i < k) :
    (rotFn k s word).testBit i = word.testBit ((i + k - s % k) % k) := by
  unfold rotFn
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hsm : s % k < k := Nat.mod_lt s hk
  by_cases hle : s % k ≤ i
  · have hge : k ≤ k - s % k + i := by omega
    have hhi : word.testBit (k - s % k + i) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) hge))
    have hmod : (i + k - s % k) % k = i - s % k := by
      have h1 : i + k - s % k = (i - s % k) + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hhi, Bool.or_false, decide_eq_true hle, Bool.true_and, hmod]
  · have hlt : i < s % k := by omega
    have hdec : decide (s % k ≤ i) = false := decide_eq_false (by omega)
    have hmod : (i + k - s % k) % k = i + (k - s % k) := by
      have h1 : i + k - s % k = i + (k - s % k) := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]
    rw [hdec, Bool.false_and, Bool.false_or, hmod, Nat.add_comm (k - s % k) i]

def old (k row key p:Nat):Bool := (rotFn k 1 key ^^^ row).testBit (p % k)
theorem zeroUnderlying {k row key pos:Nat} (hk:12 ≤ k) (bound:key < 2^k) :
    old k row key pos = xor (key.testBit ((pos+k-1) % k)) (row.testBit (pos % k)) := by
  unfold old
  rw [Nat.testBit_xor,rotFn_testBit (by omega) bound (Nat.mod_lt _ (by omega))]
  have h1 : 1 % k=1 := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  have a:pos % k+k-1=pos % k+(k-1):=by omega
  have b:pos+k-1=pos+(k-1):=by omega
  rw [a,b,Nat.mod_add_mod]

theorem mixBit (k a b c i:Nat) (hi:i < k):
    (((a^^^b^^^c) % 2^k).testBit i)=xor (xor (a.testBit i) (b.testBit i)) (c.testBit i) := by
  simp [Nat.testBit_mod_two_pow,Nat.testBit_xor,hi]
theorem blend {k row a b r p:Nat} (hk:12 ≤ k) (ha:a < 2^k) (hb:b < 2^k) (hr:r < 2^k):
    old k row ((a^^^b^^^r) % 2^k) p=xor (xor (old k row a p) (old k row b p)) (old k row r p) := by
  have hi:((p+k-1) % k) < k:=Nat.mod_lt _ (by omega)
  rw [zeroUnderlying hk (Nat.mod_lt _ (Nat.two_pow_pos _)),zeroUnderlying hk ha,zeroUnderlying hk hb,zeroUnderlying hk hr,mixBit _ _ _ _ _ hi]
  cases a.testBit ((p+k-1) % k) <;> cases b.testBit ((p+k-1) % k) <;>
    cases r.testBit ((p+k-1) % k) <;> cases row.testBit (p % k) <;>rfl

theorem periodic (k row key p:Nat): old k row key p = old k row key (p % k) := by
  simp [old]


theorem width {k m:Nat} (starts:Fin m → Nat) (hk:0 < k) (hm:0 < m)
    (inj:∀ x y:Fin m×Fin 12,(starts x.1+x.2.val) % k=(starts y.1+y.2.val) % k → x=y) :
    12 ≤ k := by
  apply Nat.le_of_not_gt
  intro lt
  let t:Fin m:=⟨0,hm⟩
  have ab:(starts t+(0:Fin 12).val) % k=(starts t+(⟨k,lt⟩:Fin 12).val) % k:=by
    simp
  have q:=congrArg (fun z:Fin m×Fin 12=>z.2.val) (inj (t,0) (t,⟨k,lt⟩) ab)
  have k0:k=0:=q.symm
  omega
end G32018.Keys

namespace G32018.Keys

def pack (n : Nat) (f : Nat → Bool) : Nat :=
  (List.range n).foldl (fun (acc bit : Nat) => acc ||| ((f bit).toNat <<< bit)) 0

theorem pack_bit (n : Nat) (f : Nat → Bool) (k : Nat) :
    (pack n f).testBit k = (decide (k < n) && f k) := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    rw [pack,List.range_succ,List.foldl_append]
    change ((pack n f) ||| ((f n).toNat <<< n)).testBit k = _
    rw [Nat.testBit_or,ih,Nat.testBit_shiftLeft,Nat.testBit_bool_toNat]
    rcases Nat.lt_trichotomy k n with h|h|h
    · have h₁ : ¬k ≥ n := by omega
      have h₂ : k < n+1 := by omega
      simp [h,h₁,h₂]
    · subst n; simp
    · have h₁ : ¬k < n := by omega
      have h₂ : ¬k < n+1 := by omega
      have h₃ : k-n≠0 := by omega
      simp [h₁,h₂,h₃]


theorem pack_bounded (k : Nat) (f : Nat → Bool) : pack k f < 2^k := by
  have eq : pack k f % 2^k=pack k f := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow,pack_bit]
    cases decide (i < k) <;> rfl
  exact eq ▸ Nat.mod_lt _ (Nat.two_pow_pos _)

abbrev Word (k:Nat):=Fin (2^k)
def chart (k:Nat) (row key:Word k) (p:Fin k) := old k row.val key.val p.val
def encode {k:Nat} (hk:0 < k) (row:Word k) (a:Fin k → Bool) : Word k :=
  let f:=fun i=> xor (a ⟨(i+1) % k,Nat.mod_lt _ hk⟩) (row.val.testBit ((i+1) % k))
  ⟨pack k f,pack_bounded ..⟩

theorem prev_next {k i:Nat} (hk:0 < k) (hi:i < k) : (((i+k-1) % k)+1) % k=i := by
  by_cases h:i=0
  · subst i
    have lt:k-1 < k:=by omega
    rw [Nat.zero_add,Nat.mod_eq_of_lt lt,show k-1+1=k by omega,Nat.mod_self]
  · have e:i+k-1=(i-1)+k:=by omega
    rw [e,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega : (i-1) < k)]
    rw [show i-1+1=i by omega,Nat.mod_eq_of_lt hi]

theorem next_prev {k i:Nat} (hk:0 < k) (hi:i < k) : ((((i+1) % k)+k-1) % k)=i := by
  have eq:((i+1) % k)+k-1=((i+1) % k)+(k-1):=by omega
  rw [eq,Nat.mod_add_mod]
  rw [show i+1+(k-1)=i+k by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hi]

theorem decode_encode {k:Nat} (hk:12 ≤ k) (row:Word k) (a:Fin k → Bool) :
    chart k row (encode (by omega) row a)=a := by
  funext p
  have bound:((p.val+k-1) % k) < k:=Nat.mod_lt _ (by omega)
  unfold chart
  rw [zeroUnderlying hk (encode (by omega) row a).isLt]
  unfold encode
  rw [Nat.mod_eq_of_lt p.isLt]
  simp only [pack_bit,bound,decide_true,Bool.true_and]
  let s:Fin k:=⟨(((p.val+k-1) % k)+1) % k,Nat.mod_lt _ (by omega)⟩
  change xor (xor (a s) (row.val.testBit s.val)) (row.val.testBit p.val)=a p
  have eq:s=p:=Fin.ext (prev_next (by omega) p.isLt)
  rw [eq]
  cases a p <;> cases row.val.testBit p.val <;> rfl

theorem encode_decode {k:Nat} (hk:12 ≤ k) (row q:Word k) :
    encode (by omega) row (chart k row q)=q := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi:i < k
  · have hp:(i+1) % k < k:=Nat.mod_lt _ (by omega)
    simp only [encode,pack_bit,hi,decide_true,Bool.true_and,chart]
    rw [zeroUnderlying hk q.isLt,next_prev (by omega) hi,Nat.mod_eq_of_lt hp]
    cases q.val.testBit i <;> cases row.val.testBit ((i+1) % k) <;>rfl
  · have le:2^k ≤ 2^i:=Nat.pow_le_pow_right (by decide) (by omega)
    simp only [encode,pack_bit,hi,decide_false,Bool.false_and]
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le q.isLt le)]

end G32018.Keys

namespace G32018.Actual
open G32018.Keys

def step (k word:Nat) :=
  (List.range k).foldl (fun acc cell=>acc ||| ((xor (word.testBit cell)
    (!(word.testBit ((cell+1) % k)) && word.testBit ((cell+2) % k))).toNat <<< cell)) 0
def state (k:Nat) (C:Nat → Fin (2^k)) (row rounds key:Nat) :=
  (List.range rounds).foldl (fun prev tick=>
    step k (prev ^^^ rotFn k 1 prev ^^^ rotFn k (k-1) prev) ^^^ rotFn k (2*tick) key ^^^
      (C (tick+1)).val) (rotFn k 1 key ^^^ row)
def bit (k:Nat) (C:Nat → Fin (2^k)) (row round key pos:Nat):Bool :=
    (state k C row round key).testBit (pos % k)
def inj (k:Nat) (C:Nat → Fin (2^k)) (r key pos:Nat):Bool :=
    xor ((rotFn k (2*(r-1)) key).testBit (pos % k)) ((C r).val.testBit (pos % k))

def fixed {k:Nat} (C:Nat → Fin (2^k)) (row ref:Fin (2^k)) (p:Nat) (key:Fin (2^k)) :=
  ∀j < 9,bit k C row.val 0 key.val (p+j)=bit k C row.val 0 ref.val (p+j)
def O (k:Nat) (C:Nat → Fin (2^k)) (row ref p j:Nat):Bool := bit k C row 0 ref (p+j)
def first (k:Nat) (C:Nat → Fin (2^k)) (row ref p j:Nat):Bool := bit k C row 1 ref (p+j)
def alpha {k:Nat} (C:Nat → Fin (2^k)) (row ref p:Nat):Bool :=
  xor (x3 (O k C row ref p 5) (O k C row ref p 6) (O k C row ref p 7))
    (inj k C 1 ref (p+6))
def tau {k:Nat} (C:Nat → Fin (2^k)) (row ref p:Nat):Bool:=
  x3 (O k C row ref p 6) (O k C row ref p 7) (O k C row ref p 8)
def beta {k:Nat} (C:Nat → Fin (2^k)) (row ref p:Nat):Bool:=
  xor (tau C row ref p) (inj k C 1 ref (p+7))
def delta {k:Nat} (C:Nat → Fin (2^k)) (row ref p:Nat):Bool:=
  x3 (xor (O k C row ref p 7) (O k C row ref p 8))
    (row.testBit ((p+9) % k)) ((C 1).val.testBit ((p+8) % k))

def triple {k:Nat} (C:Nat → Fin (2^k)) (row ref p q:Nat):Bool×Bool×Bool :=
  (xor (O k C row q p 9) (xor (O k C row ref p 7) (O k C row ref p 8)),
    xor (O k C row q p 10) (O k C row ref p 7),
    xor (O k C row q p 11) (O k C row ref p 8))
def slot {k:Nat} (C:Nat → Fin (2^k)) (row ref p q:Nat):Nat :=
  let t:=triple C row ref p q
  code t.1 t.2.1 t.2.2
def good {k:Nat} (C:Nat → Fin (2^k)) (row ref p:Nat) :=
  tau C row ref p=false ∧ x3 (first k C row ref p 3) (first k C row ref p 4) (first k C row ref p 5)=true ∧
  xor (first k C row ref p 4) (first k C row ref p 5)= !(alpha C row ref p) ∧ first k C row ref p 4=beta C row ref p

def tauD {k:Nat} (C:Nat → Fin (2^k)) (row ref p:Nat) := xor (O k C row ref p 6) (xor (O k C row ref p 7) (O k C row ref p 8))
def betaD {k:Nat} (C:Nat → Fin (2^k)) (row ref p:Nat) := xor (tauD C row ref p) (inj k C 1 ref (p+7))
def dModel {k:Nat} (C:Nat → Fin (2^k)) (row ref p s j:Nat) :=
  if j=6 then xor (alpha C row ref p) ((!tauD C row ref p) && s.testBit 0)
  else if j=7 then xor (betaD C row ref p) ((!s.testBit 0) && s.testBit 1)
  else if j=8 then xor (delta C row ref p) ((s.testBit 0==s.testBit 1) && s.testBit 2)
  else first k C row ref p j
def dNext {k:Nat} (C:Nat → Fin (2^k)) (row ref p s j:Nat) :=
  let mn:=fun h:Nat=>x3 (dModel C row ref p s (h-1)) (dModel C row ref p s h) (dModel C row ref p s (h+1))
  xor (xor (mn j) (!(mn (j+1)) && mn (j+2))) (inj k C 2 ref (p+j))

theorem modelSpecial {k:Nat} (C:Nat → Fin (2^k)) (row ref p s:Nat)
    (h:good C row ref p) :
    dNext C row ref p s 5 =
      bitAt s (x3 (alpha C row ref p) (beta C row ref p) (delta C row ref p)) (inj k C 2 ref (p+5)) := by
  let a:=s.testBit 0;let b:=s.testBit 1;let c:=s.testBit 2
  let α:=alpha C row ref p;let β:=beta C row ref p;let δ:=delta C row ref p
  let f4:=first k C row ref p 4;let f5:=first k C row ref p 5
  let j:=inj k C 2 ref (p+5)
  have e:tauD C row ref p=tau C row ref p:=by simp [tauD,tau,x3,Bool.xor_assoc]
  have ee:betaD C row ref p=β:=by simp [betaD,beta,β,e]
  have cor:=local_gate a b c α β δ f4 f5 j h.2.2.1 h.2.2.2
  calc
    _ = localValue (model a b c α β δ f4 f5) j := by
      simp [dNext,dModel,model,localValue,e,h.1,ee,a,b,c,α,β,δ,f4,f5,j,x3]
    _ = _ := cor

theorem bit_zero {k:Nat} (C:Nat → Fin (2^k)) (hk:0 < k) (row q:Word k) (p:Nat) :
    bit k C row.val 0 q.val p=chart k row q ⟨p % k,Nat.mod_lt _ hk⟩ := by
  simp [bit,state,chart,old]

end G32018.Actual

namespace G32018.Actual
open G32018.Keys
theorem donor_block {k:Nat} (hk:12 ≤ k) (C:Nat → Fin (2^k))
    (row ref q:Fin (2^k)) (p:Nat) (hasFixed:fixed C row ref p q) (goodness:good C row.val ref.val p):
    bit k C row.val 2 q.val (p+5)=bitAt (slot C row.val ref.val p q.val)
      (x3 (alpha C row.val ref.val p) (beta C row.val ref.val p) (delta C row.val ref.val p))
      (inj k C 2 ref.val (p+5)) := by
  
  
  have h:=PEqualNP.Outside.L_meta_25620 k (by omega) C hk row ref p
  let K:Finset (Fin (2^k)):=(Finset.univ : Finset _).filter (fun z=>
    (List.range 9).all (fun j=>bit k C row.val 0 z.val (p+j)==O k C row.val ref.val p j))
  have hq:q∈K:=by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    apply List.all_eq_true.mpr
    intro j hj
    exact beq_iff_eq.mpr (hasFixed j (List.mem_range.mp hj))
  have ve:=(h.1 q hq).2 (3:Fin 4)
  have exactD:bit k C row.val 2 q.val (p+5)=dNext C row.val ref.val p (slot C row.val ref.val p q.val) 5 := by
    exact ve
  exact exactD.trans (modelSpecial C row.val ref.val p _ goodness)


theorem group_width {k m:Nat} (hk:0 < k) (mpos:0 < m) (starts:Fin m → Nat)
    (distinct:Function.Injective (fun z:Fin m×Fin 12=>(starts z.1+z.2.val) % k)) :
    12 ≤ k := Keys.width starts hk mpos (fun _ _ h=>distinct h)
end G32018.Actual

namespace AC32018
open PEqualNP.CircuitLowerBounds

inductive AF where
 | const (b : Bool)
 | var (w : Nat)
 | plus (f g : AF)
 deriving Repr

def AF.ev (x : Nat → Bool) : AF → Bool
 | .const b => b
 | .var w => x w
 | .plus f g => xor (ev x f) (ev x g)

def AF.neg (f : AF) : AF := .plus f (.const true)

@[local simp] theorem AF.ev_neg (x : Nat → Bool) (a : AF) :
  (AF.neg a).ev x = !(a.ev x) := by cases h : a.ev x <;> simp [AF.neg, AF.ev,h]

inductive Tr (B : Type) where
 | leaf (b : B)
 | ask (a : AF) (no yes : Tr B)
def Tr.run {B} (x : Nat → Bool) : Tr B → B
 | .leaf b => b
 | .ask a l r => if a.ev x then r.run x else l.run x

def Tr.depth {B} : Tr B → Nat
 | .leaf _ => 0
 | .ask _ l r => max l.depth r.depth + 1

inductive GP where
 | give (a : AF)
 | ask (q no yes : AF)

def GP.run (x : Nat → Bool) : GP → AF
 | .give a => a
 | .ask q no yes => if q.ev x then yes else no

def GP.cost : GP → Nat
 | .give _ => 0
 | .ask .. => 1

def GP.bind {B : Type} (g : GP) (f : AF → Tr B) : Tr B :=
 match g with
 | .give a => f a
 | .ask q no yes => .ask q (f no) (f yes)

theorem GP.run_bind {B} (x) (g : GP) (f : AF → Tr B) :
 (g.bind f).run x = (f (g.run x)).run x := by
 cases g with
 | give => rfl
 | ask q no yes => cases h : q.ev x <;> simp [GP.bind,Tr.run,GP.run,h]

theorem GP.depth_bind {B} (g : GP) (f : AF → Tr B) (n)
 (h : ∀ a, (f a).depth ≤ n) : (g.bind f).depth ≤ g.cost + n := by
 cases g with
 | give a => simpa [GP.bind,GP.cost] using h a
 | ask q no yes =>
   simp only [GP.bind,Tr.depth,GP.cost]; have h1 := h no; have h2 := h yes; omega

def basis (op : GateOp) (l : Nat) : Prop :=
 l ≤ 2 ∧ (op = .and ∨ op = .or ∨ op = .mod 2 ∨ (op = .not ∧ l = 1))

noncomputable def charged (op : GateOp) (l : Nat) : Bool :=
 @decide ((op = .and ∨ op = .or) ∧ l = 2) (Classical.propDecidable _)

def plan : GateOp → List AF → GP
 | .and, [] => .give (.const true)
 | .and, [a] => .give a
 | .and, [a,b] => .ask a (.const false) b
 | .or, [] => .give (.const false)
 | .or, [a] => .give a
 | .or, [a,b] => .ask a b (.const true)
 | .not, [a] => .give a.neg
 | .mod _, [] => .give (.const true)
 | .mod _, [a] => .give a.neg
 | .mod _, [a,b] => .give (.neg (.plus a b))
 | _,_ => .give (.const false)

theorem plan_cost (op) (l : List AF) :
 (plan op l).cost = (charged op l.length).toNat := by
 cases l with
 | nil => cases op <;> simp [plan,GP.cost,charged]
 | cons a l => cases l with
   | nil => cases op <;> simp [plan,GP.cost,charged]
   | cons b l => cases l with
     | nil => cases op <;> simp [plan,GP.cost,charged]
     | cons d l => cases op <;> simp [plan,GP.cost,charged]

theorem plan_correct (op) (l : List AF) (x : Nat → Bool)
 (h : basis op l.length) :
 ((plan op l).run x).ev x = op.eval (l.map (AF.ev x)) := by
 obtain ⟨hl,ho⟩ := h
 cases l with
 | nil =>
   rcases ho with rfl | rfl | rfl | ⟨_,hh⟩ <;> first | contradiction | rfl
 | cons a l => cases l with
   | nil =>
     rcases ho with rfl | rfl | rfl | ⟨rfl,_⟩ <;>
       cases ha : a.ev x <;> simp [plan,GP.run,AF.ev_neg,GateOp.eval,ha]
   | cons b l => cases l with
     | nil =>
       rcases ho with rfl | rfl | rfl | ⟨_,hh⟩
       all_goals first | simp at hh | cases ha : a.ev x <;> cases hb : b.ev x <;> simp [plan,GP.run,AF.ev_neg,AF.ev,GateOp.eval,ha,hb]
     | cons c l => simp at hl

def app {B : Type} (g : Gate) (w : List AF) (k : List AF → Tr B) : Tr B :=
 (plan g.op (g.inputs.map (fun i => w.getD i (.const false)))).bind (fun a => k (w ++ [a]))

def work {B : Type} (gs : List Gate) (w : List AF) (k : List AF → Tr B) : Tr B :=
 match gs with
 | [] => k w
 | g::gs => app g w (fun w' => work gs w' k)

theorem AF.ev_getD (x) (w : List AF) (i : Nat) :
 (w.getD i (.const false)).ev x = (w.map (AF.ev x)).getD i false := by
 induction w generalizing i with
 | nil => rfl
 | cons a w ih => cases i with
   | zero => rfl
   | succ i => exact ih i

def evalGate (w : List Bool) (g : Gate) : List Bool :=
 w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

theorem ev_app (x : Nat → Bool) (g : Gate) (w : List AF)
 (hg : basis g.op g.inputs.length) :
 let p := plan g.op (g.inputs.map (fun i => w.getD i (.const false)))
 (w ++ [p.run x]).map (AF.ev x) = evalGate (w.map (AF.ev x)) g := by
 simp only [List.map_append,List.map_cons,List.map_nil,evalGate]
 congr 2
 rw [plan_correct]
 · simp only [List.map_map,Function.comp_def,AF.ev_getD]
 · simpa using hg

theorem work_runs {B : Type} (x : Nat → Bool) (gs : List Gate)
 (legal : ∀ g ∈ gs, basis g.op g.inputs.length)
 (w : List AF) (k : List AF → Tr B) (ref : List Bool → B)
 (ref_eq : ∀ w', (k w').run x = ref (w'.map (AF.ev x))) :
 (work gs w k).run x = ref (gs.foldl evalGate (w.map (AF.ev x))) := by
 induction gs generalizing w with
 | nil => exact ref_eq _
 | cons g gs ih =>
   simp only [work,app,GP.run_bind,List.foldl_cons]
   rw [ih (fun h hh => legal h (by simp [hh]))]
   rw [ev_app x g w (legal g (by simp))]

theorem work_depth {B : Type} (gs : List Gate) (w : List AF)
 (k : List AF → Tr B) (n : Nat) (kh : ∀ w', (k w').depth ≤ n) :
 (work gs w k).depth ≤ gs.countP (fun g => charged g.op g.inputs.length) + n := by
 induction gs generalizing w with
 | nil => simpa [work] using kh w
 | cons g gs ih =>
   simp only [work,app,List.countP_cons]
   apply Nat.le_trans (GP.depth_bind _ _ _ (fun a => ih (w ++ [a])))
   rw [plan_cost,List.length_map]
   cases h : charged g.op g.inputs.length <;> simp [h] <;> omega

def expose {B : Type} : (n : Nat) → (Fin n → AF) → ((Fin n → Bool) → Tr B) → Tr B
 | 0, _, k => k Fin.elim0
 | n+1, f, k =>
   .ask (f 0)
     (expose n (fun j => f j.succ) (fun s => k (Fin.cases false s)))
     (expose n (fun j => f j.succ) (fun s => k (Fin.cases true s)))

theorem expose_run {B} (n : Nat) (f : Fin n → AF) (k : (Fin n → Bool) → Tr B) (x) :
 (expose n f k).run x = (k (fun j => (f j).ev x)).run x := by
 induction n with
 | zero =>
   simp only [expose]; congr 2; funext j; exact Fin.elim0 j
 | succ n ih =>
   simp only [expose,Tr.run]; split <;> rename_i h <;> rw [ih] <;> congr 2 <;> funext j <;>
     refine Fin.cases ?_ (fun j => ?_) j <;> simp_all

theorem expose_depth {B} (n) (f : Fin n → AF) (k : (Fin n → Bool) → Tr B) (d : Nat)
 (hd : ∀ s, (k s).depth ≤ d) : (expose n f k).depth ≤ n + d := by
 induction n with
 | zero => simpa [expose] using hd Fin.elim0
 | succ n ih =>
   simp only [expose,Tr.depth]
   have h0 := ih (fun j => f j.succ) (fun s => k (Fin.cases false s)) (fun s => hd _)
   have h1 := ih (fun j => f j.succ) (fun s => k (Fin.cases true s)) (fun s => hd _)
   omega

def msgTree (k c : Nat) (C : Circuit) (tap : Fin c → Nat) : Tr (Fin c → Bool) :=
 work C.gates (List.ofFn (fun i : Fin k => AF.var i.val)) (fun w =>
   expose c (fun j => w.getD (tap j) (.const false)) Tr.leaf)

theorem msgTree_run (k c : Nat) (C : Circuit) (tap : Fin c → Nat)
 (hlegal : ∀ g ∈ C.gates, basis g.op g.inputs.length) (x : Nat → Bool) :
 (msgTree k c C tap).run x =
 fun j => (C.wires (List.ofFn (fun i : Fin k => x i.val))).getD (tap j) false := by
 unfold msgTree
 rw [work_runs x C.gates hlegal _ _ (fun vals j => vals.getD (tap j) false)]
 · simp only [List.map_ofFn]
   rfl
 · intro w
   rw [expose_run]
   funext j
   exact AF.ev_getD _ _ _

theorem msgTree_depth (k c : Nat) (C : Circuit) (tap : Fin c → Nat) :
 (msgTree k c C tap).depth ≤ 
 c + C.gates.countP (fun g => @decide
 ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)) := by
 unfold msgTree
 rw [Nat.add_comm]
 apply work_depth
 intro w
 have h := expose_depth c (fun j => w.getD (tap j) (.const false)) (@Tr.leaf _) 0 (fun _ => Nat.le_refl _)
 simpa using h

def Tr.trace {B} (x : Nat → Bool) : Tr B → List (AF × Bool)
 | .leaf _ => []
 | .ask a l r =>
   (a,a.ev x) :: (if a.ev x then r.trace x else l.trace x)

def satisfies (x : Nat → Bool) (p : List (AF × Bool)) : Prop :=
 ∀ e ∈ p, e.1.ev x = e.2

theorem Tr.trace_self {B} (t : Tr B) (x : Nat → Bool) : satisfies x (t.trace x) := by
 induction t with
 | leaf => simp [Tr.trace,satisfies]
 | ask a l r hl hr =>
   cases h : a.ev x <;> simp_all [Tr.trace,satisfies]

theorem Tr.trace_correct {B} (t : Tr B) (x y : Nat → Bool)
 (h : satisfies y (t.trace x)) : t.trace y = t.trace x ∧ t.run y = t.run x := by
 induction t with
 | leaf => exact ⟨rfl,rfl⟩
 | ask a l r hl hr =>
   have ht : a.ev y = a.ev x := h (a,a.ev x) (by simp [Tr.trace])
   cases e : a.ev x <;> simp_all [Tr.trace,Tr.run,satisfies]

theorem Tr.trace_length {B} (t : Tr B) (x : Nat → Bool) : (t.trace x).length ≤ t.depth := by
 induction t with
 | leaf => exact Nat.le_refl _
 | ask a l r hl hr =>
   cases h : a.ev x <;> simp [Tr.trace,Tr.depth,h] <;> omega

theorem Tr.trace_iff {B} (t : Tr B) (x y : Nat → Bool) :
 t.trace y = t.trace x ↔ satisfies y (t.trace x) :=
 ⟨fun h => h ▸ t.trace_self y, fun h => (t.trace_correct x y h).1⟩

end AC32018

namespace AC32018
abbrev BV (n : Nat) := Fin n → Bool
def zeroV {n} : BV n := fun _ => false
def addV {n} (x y : BV n) : BV n := fun j => xor (x j) (y j)
def tailV {n} (x : BV (n+1)) : BV n := fun j => x j.succ
def consV {n} (a : Bool) (x : BV n) : BV (n+1) := Fin.cases a x

@[local simp] theorem consV_zero {n} (a : Bool) (x : BV n) : consV a x 0 = a := rfl
@[local simp] theorem consV_succ {n} (a : Bool) (x : BV n) (i) : consV a x i.succ = x i := rfl
@[local simp] theorem tailV_consV {n} (a : Bool) (x : BV n) : tailV (consV a x) = x := rfl
@[local simp] theorem consV_tailV {n} (v : BV (n+1)) : consV (v 0) (tailV v) = v := by
  funext i; refine Fin.cases rfl (fun _ => rfl) i

structure Lin (n : Nat) where
 f : BV n → Bool
 lin : ∀ x y, f (addV x y) = xor (f x) (f y)

theorem Lin.zero {n} (p : Lin n) : p.f zeroV = false := by
 have h := p.lin zeroV zeroV
 have he : addV (zeroV : BV n) zeroV = zeroV := rfl
 rw [he] at h; cases h0 : p.f zeroV <;> simp_all

def Lin.nil {n} : Lin n := ⟨fun _ => false,fun _ _ => rfl⟩
def Lin.lead {n} (p : Lin (n+1)) : Bool := p.f (consV true zeroV)

theorem consV_add {n} (a b) (x y : BV n) :
 addV (consV a x) (consV b y) = consV (xor a b) (addV x y) := by
 funext i; refine Fin.cases rfl (fun j => rfl) i

def Lin.pull {n} (p : Lin (n+1)) (head : Lin n) : Lin n :=
 ⟨fun x => p.f (consV (head.f x) x), by
   intro x y
   rw [head.lin,← consV_add,p.lin]⟩

abbrev Lin.cut {n} (p : Lin (n+1)) : Lin n := p.pull Lin.nil

theorem Lin.form {n} (p : Lin (n+1)) (a : Bool) (v : BV n) :
 p.f (consV a v) = xor (a && p.lead) (p.cut.f v) := by
 cases a with
 | false => simp [Lin.cut,Lin.pull,Lin.nil]
 | true =>
   have h : (consV true v) = addV (consV true zeroV) (consV false v) := by
     rw [consV_add]; congr 1; funext i; simp [addV,zeroV]
   rw [h,p.lin]; rfl

theorem Lin.null_iff {n} (p : Lin (n+1)) (hp : p.lead = true) (a : Bool) (v : BV n) :
 p.f (consV a v) = false ↔ a = p.cut.f v := by
 rw [p.form,hp]; cases a <;> cases p.cut.f v <;> decide

def Null {n} (rows : List (Lin n)) (v : BV n) : Prop := ∀ p ∈ rows, p.f v = false

inductive Fan : Nat → Type where
 | done : Fan 0
 | free {n : Nat} (tail : Fan n) : Fan (n+1)
 | dep {n : Nat} (a : Lin n) (tail : Fan n) : Fan (n+1)

def Fan.rank : {n : Nat} → Fan n → Nat
 | _,.done => 0
 | _,.free q => q.rank + 1
 | _,.dep _ q => q.rank

def Fan.holds : {n : Nat} → Fan n → BV n → Prop
 | _,.done,_ => True
 | _,.free q,v => q.holds (tailV v)
 | _,.dep f q,v => v 0 = f.f (tailV v) ∧ q.holds (tailV v)

theorem Null.pull_iff {n} (rows : List (Lin (n+1))) (p : Lin n) (v : BV n) :
 Null (rows.map (fun r => r.pull p)) v ↔ Null rows (consV (p.f v) v) := by
 simp only [Null,List.forall_mem_map,Lin.pull]


theorem null_fan {n} (rows : List (Lin n)) : ∃ f : Fan n,
 (∀ v, f.holds v ↔ Null rows v) ∧ n ≤ f.rank + rows.length := by
 induction n with
 | zero =>
   refine ⟨.done,?_,by omega⟩
   intro v; have h0 : v = zeroV := funext (fun i => Fin.elim0 i)
   simp [h0,Fan.holds,Null,Lin.zero]
 | succ n ih =>
   by_cases h : ∃ p ∈ rows, p.lead = true
   · obtain ⟨p,hp,hp1⟩ := h
     obtain ⟨l,r,rr⟩ := List.append_of_mem hp
     subst rows
     let rs := (l ++ r).map (fun z => z.pull p.cut)
     obtain ⟨t,ht,hd⟩ := ih rs
     refine ⟨.dep p.cut t, ?_, ?_⟩
     · intro v
       simp only [Fan.holds,ht,rs,Null.pull_iff]
       constructor
       · rintro ⟨he,hrest⟩
         have hv : consV (p.cut.f (tailV v)) (tailV v) = v := by rw [←he,consV_tailV]
         rw [hv] at hrest
         have hzero := (p.null_iff hp1 (v 0) (tailV v)).2 he
         rw [consV_tailV] at hzero
         intro z hz
         rcases List.mem_append.1 hz with hz|hz
         · exact hrest z (List.mem_append_left r hz)
         · rcases List.mem_cons.1 hz with rfl|hz
           · exact hzero
           · exact hrest z (List.mem_append_right l hz)
       · intro hsolve
         have hp0 : p.f v = false := hsolve p (by simp)
         have he : v 0 = p.cut.f (tailV v) :=
           (p.null_iff hp1 _ _).1 (by simpa using hp0)
         refine ⟨he,?_⟩
         rw [← he,consV_tailV]
         intro z hz
         exact hsolve z (by simpa only [List.mem_append,List.mem_cons] using
           (show z ∈ l ∨ z = p ∨ z ∈ r from
             (List.mem_append.1 hz).imp id (.inr)))
     · simp only [rs,List.length_map,List.length_append,List.length_cons,Fan.rank] at *; omega
   · have hz : ∀ p ∈ rows,p.lead = false := by
       intro p hp; cases he:p.lead with | false => rfl | true => exact False.elim (h ⟨p,hp,he⟩)
     obtain ⟨t,ht,hd⟩ := ih (rows.map (fun z => z.pull Lin.nil))
     refine ⟨.free t, ?_, ?_⟩
     · intro v
       simp only [Fan.holds,ht,Null.pull_iff]
       have hform (p) (hp : p ∈ rows) : p.f v = p.f (consV false (tailV v)) := by
         conv => lhs; rw [← consV_tailV v,p.form,hz p hp]
         simp [Lin.cut,Lin.pull,Lin.nil]
       exact ⟨fun h p hp => (hform p hp).trans (h p hp),
              fun h p hp => (hform p hp).symm.trans (h p hp)⟩
     · simp only [List.length_map,Fan.rank] at *; omega


def Lin.coord {n} (j : Fin n) : Lin n := ⟨fun x => x j,fun _ _ => rfl⟩
def Lin.add {n} (p q : Lin n) : Lin n :=
 ⟨fun v => xor (p.f v) (q.f v),by
   intro x y; rw [p.lin,q.lin]; cases p.f x <;> cases p.f y <;>
    cases q.f x <;> cases q.f y <;> decide⟩

structure Feat (n : Nat) where
 bias : Bool
 lin : Lin n
def Feat.ev {n} (f : Feat n) (v : BV n) : Bool := xor f.bias (f.lin.f v)
def AF.linPart {n} (cs : Nat → Feat n) : AF → Lin n
 | .const _ => Lin.nil
 | .var j => (cs j).lin
 | .plus p q => (p.linPart cs).add (q.linPart cs)
def AF.biasPart {n} (cs : Nat → Feat n) : AF → Bool
 | .const b => b
 | .var j => (cs j).bias
 | .plus p q => xor (p.biasPart cs) (q.biasPart cs)

theorem AF.aff_eval {n} (q : AF) (cs : Nat → Feat n) (x : BV n) :
 q.ev (fun j => (cs j).ev x) = xor (q.biasPart cs) ((q.linPart cs).f x) := by
 induction q with
 | const b => cases b <;> rfl
 | var j => rfl
 | plus a b ha hb =>
   simp only [AF.ev,ha,hb,AF.biasPart,AF.linPart,Lin.add]
   cases a.biasPart cs <;> cases b.biasPart cs <;> cases (a.linPart cs).f x <;>
     cases (b.linPart cs).f x <;> decide

theorem AF.shift_iff {n} (q : AF) (cs : Nat → Feat n) (x y : BV n) :
 q.ev (fun j => (cs j).ev x) = q.ev (fun j => (cs j).ev y) ↔
 (q.linPart cs).f (addV x y) = false := by
 rw [q.aff_eval,q.aff_eval,(q.linPart cs).lin]; cases q.biasPart cs <;>
   cases (q.linPart cs).f x <;> cases (q.linPart cs).f y <;> decide

theorem satisfies_shift {n} (p : List (AF × Bool)) (cs : Nat → Feat n) (x y : BV n)
 (hy : satisfies (fun j => (cs j).ev y) p) :
 satisfies (fun j => (cs j).ev x) p ↔
 Null (p.map (fun e => e.1.linPart cs)) (addV x y) := by
 simp only [Null,List.forall_mem_map,satisfies]
 constructor
 · intro h e he; exact (e.1.shift_iff cs x y).1 ((h e he).trans (hy e he).symm)
 · intro h e he; exact ((e.1.shift_iff cs x y).2 (h e he)).trans (hy e he)

theorem trace_fan {B n} (t : Tr B) (cs : Nat → Feat n) (y : BV n) :
 ∃ f : Fan n, n ≤ f.rank + t.depth ∧
 ∀ x : BV n, t.trace (fun j => (cs j).ev x) = t.trace (fun j => (cs j).ev y) ↔
   f.holds (addV x y) := by
 let tr := t.trace (fun j => (cs j).ev y)
 obtain ⟨f,hs,hd⟩ := null_fan (tr.map (fun e => e.1.linPart cs))
 have ht := t.trace_length (fun j => (cs j).ev y)
 simp only [List.length_map] at hd; change tr.length ≤ t.depth at ht
 refine ⟨f,by omega,fun x => ?_⟩
 rw [Tr.trace_iff,satisfies_shift _ cs x y (t.trace_self _),hs]

def Fan.next {n} : Fan (n+1) → Fan n | .free q => q | .dep _ q => q
def Fan.gain {n} : Fan (n+1) → Nat | .free _ => 1 | .dep _ _ => 0
theorem Fan.rank_next {n} (f : Fan (n+1)) : f.rank = f.next.rank + f.gain := by
 cases f <;> rfl

def Fan.lift {n} : Fan (n+1) → BV n → List (BV (n+1))
 | .free _,v => [consV false v,consV true v]
 | .dep a _,v => [consV (a.f v) v]

theorem Fan.lift_len {n} (f : Fan (n+1)) (v : BV n) : (f.lift v).length = 2^f.gain := by
 cases f <;> rfl

theorem Fan.lift_nodup {n} (f : Fan (n+1)) (v : BV n) : (f.lift v).Nodup := by
 cases f with
 | free q =>
   simp only [Fan.lift,List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,List.nodup_nil,
      and_self,and_true,not_false_eq_true]
   intro h; exact Bool.noConfusion (congrFun h 0)
 | dep => simp [Fan.lift]

theorem Fan.lift_tail {n} (f : Fan (n+1)) {v : BV n} {x} (h : x ∈ f.lift v) :
 tailV x = v := by
 cases f <;> simp [Fan.lift] at h
 · rcases h with rfl|rfl <;> rfl
 · rw [h]; rfl

theorem Fan.holds_iff_lift {n} (f : Fan (n+1)) (x : BV (n+1)) :
 f.holds x ↔ f.next.holds (tailV x) ∧ x ∈ f.lift (tailV x) := by
 cases f with
 | free t =>
   simp only [Fan.holds,Fan.next,Fan.lift,List.mem_cons,List.not_mem_nil,or_false,and_iff_left_iff_imp]
   constructor
   · intro ht; refine ⟨ht,?_⟩; have h := consV_tailV x; cases e:x 0 <;> simp_all
   · exact And.left
 | dep a t =>
   simp only [Fan.holds,Fan.next,Fan.lift,List.mem_singleton]
   constructor
   · rintro ⟨he,ht⟩; exact ⟨ht,by rw [←he,consV_tailV]⟩
   · rintro ⟨ht,he⟩; exact ⟨by simpa using congrFun he 0,ht⟩

theorem flat_len_const {A B} (L : List A) (F : A → List B) (q : Nat)
 (h : ∀ a ∈ L,(F a).length = q) :
 (L.flatMap F).length = L.length * q := by
 induction L with
 | nil => simp
 | cons a l ih =>
   simp only [List.flatMap_cons,List.length_append,List.length_cons,h a (by simp),
    ih (fun a ha => h a (by simp [ha])),Nat.succ_mul,Nat.add_comm]

theorem flat_nodup_inv {A B} (L : List A) (F : A → List B) (I : B → A)
 (Lnd : L.Nodup) (Fnd : ∀ a,(F a).Nodup) (hi : ∀ a x, x ∈ F a → I x = a) :
 (L.flatMap F).Nodup := by
 induction L with
 | nil => simp
 | cons a as ih =>
   obtain ⟨ha,hnd⟩ := List.nodup_cons.1 Lnd
   simp only [List.flatMap_cons,List.nodup_iff_pairwise_ne,List.pairwise_append]
   refine ⟨Fnd a,ih hnd,?_⟩
   intro x hx y hy hxy; subst y
   obtain ⟨a',ha',hx'⟩ := List.mem_flatMap.1 hy
   have he := (hi a x hx).symm.trans (hi a' x hx')
   exact ha (he ▸ ha')

def Fan.drop {n : Nat} : (p : Nat) → Fan (n+p) → Fan n
 | 0,t => t | p+1,t => t.next.drop p
def Fan.upRank {n : Nat} : (p : Nat) → Fan (n+p) → Nat
 | 0,_ => 0 | p+1,t => t.next.upRank p + t.gain
def Fan.up {n : Nat} : (p : Nat) → Fan (n+p) → BV n → List (BV (n+p))
 | 0,_,v => [v]
 | p+1,t,v => (t.next.up p v).flatMap t.lift
def dropV {n : Nat} : (p : Nat) → BV (n+p) → BV n
 | 0,v => v | p+1,v => dropV p (tailV v)

theorem Fan.up_rank_add {n} (p : Nat) (t : Fan (n+p)) :
 t.rank = (t.drop p).rank + t.upRank p := by
 induction p with
 | zero => rfl
 | succ p ih => rw [t.rank_next,ih t.next]; simp [Fan.drop,Fan.upRank,Nat.add_assoc]

theorem Fan.up_rank_le {n} (p : Nat) (t : Fan (n+p)) : t.upRank p ≤ p := by
 induction p with
 | zero => exact Nat.le_refl _
 | succ p ih =>
   have h := ih t.next; have h2 : t.gain ≤ 1 := by cases t <;> simp [Fan.gain]
   simp only [Fan.upRank]; omega

theorem Fan.up_len {n} (p : Nat) (t : Fan (n+p)) (v : BV n) :
 (t.up p v).length = 2^t.upRank p := by
 induction p with
 | zero => rfl
 | succ p ih =>
   rw [Fan.up,flat_len_const _ _ (2^t.gain) (fun a _ => t.lift_len a),ih, Fan.upRank,Nat.pow_add]

theorem Fan.up_nodup {n} (p : Nat) (t : Fan (n+p)) (v : BV n) : (t.up p v).Nodup := by
 induction p with
 | zero => simp [Fan.up]
 | succ p ih =>
   exact flat_nodup_inv _ _ tailV (ih t.next) (t.lift_nodup) (fun a x hx => t.lift_tail hx)

theorem Fan.up_drop {n} (p : Nat) (t : Fan (n+p)) (v : BV n) {x} (h : x ∈ t.up p v) :
 dropV p x = v := by
 induction p with
 | zero => simpa [Fan.up,dropV] using h
 | succ p ih =>
   obtain ⟨y,hm,hl⟩ := List.mem_flatMap.1 h; rw [dropV,t.lift_tail hl]; exact ih t.next hm

theorem Fan.holds_iff_up {n} (p : Nat) (t : Fan (n+p)) (x : BV (n+p)) :
 t.holds x ↔ (t.drop p).holds (dropV p x) ∧ x ∈ t.up p (dropV p x) := by
 induction p with
 | zero => simp [Fan.drop,Fan.up,dropV]
 | succ p ih =>
   rw [t.holds_iff_lift,ih t.next (tailV x)]
   simp only [Fan.drop,dropV,Fan.up,List.mem_flatMap]
   constructor
   · rintro ⟨⟨hd,hu⟩,hl⟩; exact ⟨hd,tailV x,hu,hl⟩
   · rintro ⟨hd,y,hy,hl⟩; have hr := t.lift_tail hl; subst y; exact ⟨⟨hd,hy⟩,hl⟩

end AC32018

namespace G32018.Chart
open G32018.Keys
open AC32018

structure Layout (k n:Nat) where
 checked : 12 ≤ k
 pin : Fin k → Prop
 active : Fin n → Fin k
 active_inj : ∀ i j,active i=active j → i=j
 free : ∀i,¬pin (active i)
 off : Fin n → Bool

abbrev Extras {k n} (l:Layout k n):Type := {i:Fin k // ¬l.pin i ∧ ¬∃j,l.active j=i}
def activeBits {k n} (l:Layout k n) (row key:Word k) (i:Fin n) : Bool :=
  xor (chart k row key (l.active i)) (l.off i)
def extraBits {k n} (l:Layout k n) (row key:Word k) (i:Extras l) :=
  chart k row key i.val
def pinned {k n} (l:Layout k n) (row ref key:Word k) :=
  ∀i,l.pin i → chart k row key i=chart k row ref i

noncomputable def feature {k n} (l:Layout k n) (row ref:Word k) (e:Extras l → Bool) (i:Fin k):Feat n := by
  classical
  exact if hp:l.pin i then ⟨chart k row ref i,Lin.nil⟩
    else if ha:∃j,l.active j=i then
      let j:=Classical.choose ha
      ⟨l.off j,⟨fun x=>x j,fun _ _=>rfl⟩⟩
    else ⟨e ⟨i,hp,ha⟩,Lin.nil⟩
def flipConstant {n:Nat} (t:Feat n) (b:Bool) : Feat n := ⟨xor t.bias b,t.lin⟩
theorem flip_ev {n:Nat} (f:Feat n) (b:Bool) (x:BV n) :
    (flipConstant f b).ev x=xor (f.ev x) b := by
  unfold flipConstant Feat.ev
  cases f.bias <;> cases b <;> cases f.lin.f x <;>rfl

theorem feat_pin {k n} (l:Layout k n) (r z:Word k) (e:Extras l → Bool) (x:BV n)
    (i:Fin k) (hi:l.pin i): (feature l r z e i).ev x=chart k r z i := by
  unfold feature;rw [dif_pos hi]
  simp [Feat.ev,Lin.nil]
theorem feat_active {k n} (l:Layout k n) (r z:Word k) (e:Extras l → Bool) (x:BV n)
    (i:Fin n): (feature l r z e (l.active i)).ev x=xor (x i) (l.off i) := by
  have ex:∃j,l.active j=l.active i := ⟨i,rfl⟩
  have once : Classical.choose ex=i:=l.active_inj _ _ (Classical.choose_spec ex)
  unfold feature;rw [dif_neg (l.free i),dif_pos ex]
  change xor (l.off (Classical.choose ex)) (x (Classical.choose ex))=_
  rw [once,Bool.xor_comm]
theorem feat_extra {k n} (l:Layout k n) (r z:Word k) (e:Extras l → Bool) (x:BV n)
    (i:Extras l): (feature l r z e i.val).ev x=e i := by
  unfold feature;rw [dif_neg i.property.1,dif_neg i.property.2]
  simp [Feat.ev,Lin.nil]

noncomputable def packInput {k n} (l:Layout k n) (r z:Word k) (e:Extras l → Bool) (x:BV n) : Word k :=
  encode (by have t:=l.checked;omega) r (fun i=>(feature l r z e i).ev x)
theorem chart_pack {k n} (l:Layout k n) (r z:Word k) (e:Extras l → Bool) (x:BV n) :
    chart k r (packInput l r z e x)=fun i=>(feature l r z e i).ev x :=
  decode_encode l.checked r _
theorem pack_valid {k n} (l:Layout k n) (r z:Word k) (e:Extras l → Bool) (x:BV n):
    pinned l r z (packInput l r z e x) := by
  intro i hi;rw [chart_pack];exact feat_pin l _ _ _ _ _ hi
theorem pack_active {k n} (l:Layout k n) (r z:Word k) (e:Extras l → Bool) (x:BV n):
    activeBits l r (packInput l r z e x)=x := by
  funext i;unfold activeBits
  rw [chart_pack];dsimp only;rw [feat_active]
  cases x i <;> cases l.off i <;>rfl
theorem pack_extra {k n} (l:Layout k n) (r z:Word k) (e:Extras l → Bool) (x:BV n):
    extraBits l r (packInput l r z e x)=e := by
  funext i;unfold extraBits
  rw [chart_pack];exact feat_extra l _ _ _ _ i
theorem unpack_pack {k n} (l:Layout k n) (r z q:Word k) (on:pinned l r z q) :
    packInput l r z (extraBits l r q) (activeBits l r q)=q := by
  classical
  have eq : chart k r (packInput l r z (extraBits l r q) (activeBits l r q))=chart k r q := by
    funext i;rw [chart_pack];dsimp only
    by_cases hp:l.pin i
    · rw [feat_pin l _ _ _ _ _ hp,←on i hp]
    · by_cases ha:∃j,l.active j=i
      · obtain ⟨j,rfl⟩:=ha
        rw [feat_active]
        unfold activeBits
        cases chart k r q (l.active j) <;> cases l.off j <;>rfl
      · exact feat_extra l r z _ _ ⟨i,hp,ha⟩
  have v:=congrArg (encode (by have h:=l.checked;omega) r) eq
  rw [encode_decode l.checked,encode_decode l.checked] at v
  exact v

noncomputable def rawFeat {k n} (l:Layout k n) (row ref:Word k) (e:Extras l → Bool) (i:Nat):Feat n :=
  if hi:i < k then
    flipConstant (feature l row ref e ⟨(i+1) % k,Nat.mod_lt _ (by omega)⟩) (row.val.testBit ((i+1) % k))
  else ⟨false,Lin.nil⟩
theorem chart_raw {k n} (l:Layout k n) (row ref:Word k) (e:Extras l → Bool) (x:BV n) (i:Nat):
    (packInput l row ref e x).val.testBit i=(rawFeat l row ref e i).ev x := by
  unfold packInput encode rawFeat
  simp only [pack_bit]
  by_cases hi:i < k
  · rw [dif_pos hi,flip_ev];simp [hi]
  · rw [dif_neg hi];simp [hi,Feat.ev,Lin.nil]

end G32018.Chart

namespace G32018.Chart
open G32018.Keys
open AC32018

def locate {m:Nat} (j:Fin (3*m)):Fin m := ⟨j.val/3,by have :=j.isLt;omega⟩
def phase {m:Nat} (j:Fin (3*m)):Fin 3 := ⟨j.val % 3,by omega⟩
def groupSlot {m:Nat} (i:Fin m) (j:Fin 3):Fin (3*m) :=⟨3*i.val+j.val,by have :=i.isLt;have :=j.isLt;omega⟩
theorem locate_slot {m:Nat} (i:Fin m) (j:Fin 3):locate (groupSlot i j)=i := by
  apply Fin.ext
  change (3*i.val+j.val)/3=i.val
  have := j.isLt;omega
theorem phase_slot {m:Nat} (i:Fin m) (j:Fin 3):phase (groupSlot i j)=j := by
  apply Fin.ext
  change (3*i.val+j.val) % 3=j.val
  have :=j.isLt;omega

def groupIndex (k:Nat) {m:Nat} (hk:0 < k) (starts:Fin m → Nat) (i:Fin m) (j:Fin 3) : Fin k :=
   ⟨(starts i+9+j.val) % k,Nat.mod_lt _ hk⟩

theorem groupInj (k:Nat) {m:Nat} (hk:0 < k) (starts:Fin m → Nat)
    (inj:∀ a b:Fin m×Fin 12,(starts a.1+a.2.val) % k=(starts b.1+b.2.val) % k → a=b)
    (a b:Fin (3*m)) (eq:groupIndex k hk starts (locate a) (phase a)=groupIndex k hk starts (locate b) (phase b)):
    a=b := by
  let v (j:Fin (3*m)):Fin 12 := ⟨9+(phase j).val,by have :=(phase j).isLt;omega⟩
  have e:(locate a,v a)=(locate b,v b):=inj _ _ (by simpa [groupIndex,Nat.add_assoc,v] using congrArg Fin.val eq)
  have e₁:=congrArg (fun s:Fin m×Fin 12=>s.1.val) e
  have e₂:=congrArg (fun s:Fin m×Fin 12=>s.2.val) e
  change a.val/3=b.val/3 at e₁
  change 9+a.val % 3=9+b.val % 3 at e₂
  exact Fin.ext (by omega)

def mkLayout {k m:Nat} (hk:12 ≤ k) (starts:Fin m → Nat) (P:Fin k → Prop)
    (inj:∀ a b:Fin m×Fin 12,(starts a.1+a.2.val) % k=(starts b.1+b.2.val) % k → a=b)
    (unpin:∀ i j,¬P (groupIndex k (by omega) starts i j)) (off:Fin m → Fin 3 → Bool) : Layout k (3*m) :=
  ⟨hk,P,fun j=>groupIndex k (by omega) starts (locate j) (phase j),
    groupInj k (by omega) starts inj,fun j=>unpin (locate j) (phase j),fun j=>off (locate j) (phase j)⟩

def mix {k:Nat} (a b ref:Word k) : Word k :=
   ⟨(a.val^^^b.val^^^ref.val) % 2^k,Nat.mod_lt _ (Nat.two_pow_pos _)⟩
theorem mix_chart {k:Nat} (hk:12 ≤ k) (row a b ref:Word k) (p:Fin k) :
    chart k row (mix a b ref) p=xor (xor (chart k row a p) (chart k row b p)) (chart k row ref p) :=
   blend hk a.isLt b.isLt ref.isLt
theorem mix_pinned {k n:Nat} (l:Layout k n) (row a b ref:Word k)
    (pa:pinned l row ref a) (pb:pinned l row ref b):pinned l row ref (mix a b ref) := by
  intro p hp;rw [mix_chart l.checked,pa _ hp,pb _ hp]
  cases chart k row ref p <;>rfl
theorem mix_active {k n:Nat} (l:Layout k n) (row a b ref:Word k) :
    activeBits l row (mix a b ref)=addV (addV (activeBits l row a) (activeBits l row b)) (activeBits l row ref) := by
  funext j
  unfold activeBits addV
  dsimp only
  rw [mix_chart l.checked]
  cases chart k row a (l.active j) <;>cases chart k row b (l.active j) <;>
     cases chart k row ref (l.active j) <;>cases l.off j <;>rfl
end G32018.Chart

namespace AC32018
def Fan.enum : {n : Nat} → Fan n → List (BV n)
 | 0,.done => [zeroV]
 | _+1,t => t.next.enum.flatMap t.lift

theorem Fan.mem_enum {n} (t : Fan n) (x : BV n) : x ∈ t.enum ↔ t.holds x := by
 induction n with
 | zero =>
   cases t; have e:x=zeroV:=funext (fun i=>Fin.elim0 i); simp [Fan.enum,Fan.holds,e]
 | succ n ih =>
   rw [Fan.enum,List.mem_flatMap,t.holds_iff_lift]
   constructor
   · rintro ⟨y,hy,hx⟩; have he := t.lift_tail hx; subst y; exact ⟨(ih t.next _).1 hy,hx⟩
   · rintro ⟨h,hx⟩; exact ⟨_,(ih t.next _).2 h,hx⟩

theorem Fan.enum_len {n} (t : Fan n) : t.enum.length = 2^t.rank := by
 induction n with
 | zero => cases t; rfl
 | succ n ih =>
   rw [Fan.enum,flat_len_const _ _ (2^t.gain) (fun a _ => t.lift_len a),ih,t.rank_next,Nat.pow_add]

theorem Fan.enum_nodup {n} (t : Fan n) : t.enum.Nodup := by
 induction n with
 | zero => cases t; simp [Fan.enum]
 | succ n ih =>
   exact flat_nodup_inv _ _ tailV (ih t.next) (t.lift_nodup) (fun a x hx => t.lift_tail hx)

theorem Fan.enum_split {n} (p : Nat) (t : Fan (n+p)) :
 t.enum = (t.drop p).enum.flatMap (t.up p) := by
 induction p with
 | zero => simp [Fan.up,Fan.drop]
 | succ p ih =>
   rw [Fan.enum,ih t.next,List.flatMap_assoc]
   rfl

def word3 {n} (v : BV (n+3)) : Nat :=
 (v 0).toNat + 2*(tailV v 0).toNat + 4*(tailV (tailV v) 0).toNat

theorem word3_lt {n} (v : BV (n+3)) : word3 v < 8 := by
 unfold word3; cases v 0 <;> cases tailV v 0 <;> cases tailV (tailV v) 0 <;> decide

theorem word3_inj_over_tail {n} {v w : BV (n+3)} (h : word3 v = word3 w)
 (t : dropV 3 v = dropV 3 w) : v=w := by
 have he : v 0 = w 0 ∧ tailV v 0 = tailV w 0 ∧ tailV (tailV v) 0 = tailV (tailV w) 0 := by
   unfold word3 at h
   revert h; cases v 0 <;> cases tailV v 0 <;> cases tailV (tailV v) 0 <;> cases w 0 <;>
     cases tailV w 0 <;> cases tailV (tailV w) 0 <;> decide +revert
 obtain ⟨h1,h2,h3⟩ := he
 apply funext; intro i; refine Fin.cases h1 (fun j => ?_) i
 refine Fin.cases h2 (fun j => ?_) j
 refine Fin.cases h3 (fun j => ?_) j
 exact congrFun t j

def walk {α : Type} (xs:List α) (g : α → Nat) : Nat := (xs.map g).sum

theorem walk_const {A} (xs:List A) (q : Nat) : walk xs (fun _ => q) = xs.length*q := by
 induction xs with
 | nil => simp [walk]
 | cons a l ih => change q+walk l (fun _ => q)=_; rw [ih]; simp [Nat.add_comm,Nat.succ_mul]

theorem walk_le {A} (xs:List A) (f g : A → Nat) (h : ∀ x∈xs,f x ≤ g x) :
 walk xs f ≤ walk xs g := by
 induction xs with
 | nil => exact Nat.le_refl _
 | cons a l ih =>
   exact Nat.add_le_add (h a (by simp)) (ih (fun x hx=>h x (by simp [hx])))

theorem walk_ext {A} (xs:List A) (f g : A → Nat) (h : ∀ x∈xs,f x=g x) :
 walk xs f = walk xs g := by
 unfold walk; rw [List.map_congr_left h]

theorem walk_flat {A B} (xs:List A) (f:A → List B) (g:B → Nat) :
 walk (xs.flatMap f) g = walk xs (fun x=>walk (f x) g) := by
 induction xs with
 | nil => rfl
 | cons a l ih => unfold walk at *; simp only [List.flatMap_cons,List.map_append,List.sum_append,
    ih,List.map_cons,List.sum_cons]

theorem walk_mul {A} (xs:List A) (f:A → Nat) (q:Nat) :
 walk xs (fun x=>f x*q) = walk xs f*q := by
 induction xs with
 | nil => simp [walk]
 | cons a l ih => change f a*q+walk l (fun x=>f x*q) = (f a+walk l f)*q; rw [ih,Nat.add_mul]

theorem walk_single {A} (xs:List A) (hnd : xs.Nodup) (isHeavy:A → Bool)
 (single : ∀ x∈xs,∀ y∈xs,isHeavy x = true → isHeavy y = true → x = y) :
 walk xs (fun x=>if isHeavy x then 2 else 1) ≤ xs.length+1 := by
 induction xs with
 | nil => exact Nat.zero_le _
 | cons a l ih =>
   obtain ⟨hn,hd⟩ := List.nodup_cons.1 hnd
   have hl := ih hd (fun x hx y hy => single x (by simp [hx]) y (by simp [hy]))
   change (if isHeavy a then 2 else 1) + walk l _ ≤ _
   cases e : isHeavy a with
   | false => simp only [Bool.false_eq_true,ite_false,List.length_cons]; omega
   | true =>
     have hzero (x) (hx : x ∈ l) : isHeavy x = false := by
       cases h : isHeavy x with
       | false => rfl
       | true => have v := single a (by simp) x (by simp [hx]) e h; exact False.elim (hn (v ▸ hx))
     rw [walk_ext _ _ (fun _=>1) (fun x hx=> by simp [hzero x hx]),walk_const]
     simp; omega

theorem Fan.head_bound {n} (t : Fan (n+3)) (y : BV n) (hvy : Nat) :
 walk (t.up 3 y) (fun x => if word3 x = hvy then 2 else 1) ≤ 2^t.upRank 3+1 := by
 rw [← t.up_len 3 y]
 have v := walk_single _ (t.up_nodup 3 y) (fun x=>decide (word3 x = hvy)) (fun x hx z hz h1 h2 =>
   word3_inj_over_tail ((of_decide_eq_true h1).trans (of_decide_eq_true h2).symm)
     ((t.up_drop 3 y hx).trans (t.up_drop 3 y hz).symm))
 simpa only [decide_eq_true_eq] using v

def blockWeight : (m : Nat) → BV (3*m) → Nat
 | 0,_ => 1
 | m+1,x => (if word3 x = 0 then 2 else 1)*blockWeight m (dropV 3 x)

theorem Fan.block_step {m} (t : Fan (3*(m+1))) :
 walk t.enum (blockWeight (m+1)) ≤ 
 (2^t.upRank 3 + 1) * walk (t.drop 3).enum (blockWeight m) := by
 rw [t.enum_split 3,walk_flat,Nat.mul_comm (2^t.upRank 3+1),← walk_mul]
 apply walk_le
 intro v _
 simp only [blockWeight]
 calc
  _ = walk (t.up 3 v) (fun x => (if word3 x = 0 then 2 else 1) * blockWeight m v) :=
        walk_ext _ _ _ (fun x hx => by rw [t.up_drop 3 v hx])
  _ = walk (t.up 3 v) (fun x => if word3 x = 0 then 2 else 1) * blockWeight m v := walk_mul .. 
  _ ≤ (2^t.upRank 3+1) * blockWeight m v := Nat.mul_le_mul_right _ (t.head_bound v 0)
  _ = _ := Nat.mul_comm ..

theorem head_arith (q : Nat) (h : q ≤ 3) : (2^q+1)^3 * 16^q ≤ (2*(2^q))^3 * 9^q := by
 have h':q=0 ∨ q=1 ∨ q=2 ∨ q=3:=by omega
 rcases h' with rfl|rfl|rfl|rfl <;> decide

theorem Fan.moment {m} (t : Fan (3*m)) :
 (walk t.enum (blockWeight m))^3 * 16^t.rank ≤ ((2^m)*(2^t.rank))^3 * 9^t.rank := by
 induction m with
 | zero =>
   cases t; decide
 | succ m ih =>
   let s := t.drop 3
   let q := t.upRank 3
   have hr : t.rank = s.rank + q := t.up_rank_add 3
   have hs := ih s
   have hq := head_arith q (t.up_rank_le 3)
   have E := Nat.mul_le_mul_right (16^t.rank) (Nat.pow_le_pow_left t.block_step 3)
   change _ ≤ (((2^q+1)*walk s.enum (blockWeight m))^3)*16^t.rank at E
   calc
    _ ≤ _ := E
    _ = ((2^q+1)^3*16^q)*((walk s.enum (blockWeight m))^3*16^s.rank) := by
      rw [Nat.mul_pow,hr,Nat.pow_add]; ac_rfl
    _ ≤ ((2*2^q)^3*9^q)*(((2^m)*(2^s.rank))^3 * 9^s.rank) := Nat.mul_le_mul hq hs
    _ = _ := by
      rw [hr]; simp only [Nat.pow_add,Nat.pow_one,Nat.mul_pow]; first | ac_rfl | ring

theorem Fan.rate {m} (t : Fan (3*m)) (r : Nat) (hr : 3*r ≤ t.rank) :
 16^r * walk t.enum (blockWeight m) ≤ 9^r * (2^m * t.enum.length) := by
 rw [t.enum_len]
 let d := t.rank - 3*r
 have split : t.rank = 3*r+d := by omega
 have pos : 0 < 16^d := Nat.pow_pos (by decide)
 have h := t.moment
 let W := walk t.enum (blockWeight m)
 let Z := 2^m*2^t.rank
 change W^3*16^t.rank ≤ Z^3*9^t.rank at h
 rw [split,Nat.pow_add,Nat.pow_add] at h
 have g : (W^3*16^(3*r))*16^d ≤ (Z^3*9^(3*r))*16^d := by
   rw [Nat.mul_assoc,Nat.mul_assoc]
   exact Nat.le_trans h (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide : 9 ≤ 16) _)))
 have cube : (16^r*W)^3 ≤ (9^r*Z)^3 := by
   rw [Nat.mul_pow,Nat.mul_pow,← Nat.pow_mul,← Nat.pow_mul,Nat.mul_comm r 3,Nat.mul_comm _ (W^3),Nat.mul_comm _ (Z^3)]
   exact Nat.le_of_mul_le_mul_right g pos
 exact Nat.le_of_not_gt (fun h => Nat.not_le_of_gt (Nat.pow_lt_pow_left h (by decide : 3 ≠ 0)) cube)

end AC32018

namespace G32018.Corr

def localCorr (d j:Bool) (a b:Nat):Int :=
  ((List.range 8).map (fun y=>sgn (bitAt (a^^^y) d j)*sgn (bitAt (b^^^y) d j))).sum

theorem local_bound (d j:Bool) (a b:Nat) (ha:a < 8) (hb:b < 8) :
    (localCorr d j a b).natAbs ≤ if a=b then 8 else 4 := by
  have va:a=0∨a=1∨a=2∨a=3∨a=4∨a=5∨a=6∨a=7:=by omega
  have vb:b=0∨b=1∨b=2∨b=3∨b=4∨b=5∨b=6∨b=7:=by omega
  rcases va with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
   rcases vb with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
   cases d <;>cases j <;>decide

def all : Nat → List (List Nat)
| 0 => [[]]
| m+1 => (List.range 8).flatMap fun a => (all m).map (fun as=>a::as)
def fits : List Nat → Nat → Prop
| [],n => n=0
| a::as,n => a < 8 ∧ ∃ m,n=m+1 ∧ fits as m

def add : List Nat → List Nat → List Nat := List.zipWith (Nat.xor)
def value : List (Bool×Bool) → List Nat → Int
| [],_=>1
| _,[]=>1
| (d,j)::ds,a::as=>sgn (bitAt a d j)*value ds as
def weight : List Nat → List Nat → Nat
| [],_=>1
| _,[]=>1
| a::as,b::bs=>(if a=b then 2 else 1)*weight as bs

def sumI {A:Type} (l:List A) (f:A → Int):Int := (l.map f).sum
theorem sumI_cons {A:Type} (x:A) (l:List A) (f:A → Int) : sumI (x::l) f=f x+sumI l f := rfl
theorem sumI_nil {A:Type} (f:A → Int):sumI [] f=0:=rfl
theorem sumI_add {A:Type} (l:List A) (f g:A → Int) :
    sumI l (fun a=>f a+g a)=sumI l f+sumI l g := by
  induction l with
  | nil=>rfl
  | cons a as ih=>simp only [sumI_cons,ih];ac_rfl
theorem sumI_mul {A:Type} (l:List A) (d:Int) (f:A → Int):
    sumI l (fun a=>d*f a)=d*sumI l f := by
  induction l with
  | nil=>simp [sumI]
  | cons a as ih=>simp only [sumI_cons,Int.mul_add,ih]
theorem sumI_mul_right {A:Type} (l:List A) (d:Int) (f:A → Int):
    sumI l (fun a=>f a*d)=sumI l f*d := by
  simp only [Int.mul_comm _ d,sumI_mul]
theorem sumI_append {A:Type} (l r:List A) (f:A → Int) :
    sumI (l++r) f=sumI l f+sumI r f := by simp [sumI]
theorem sumI_map {A B:Type} (ls:List A) (g:A → B) (f:B → Int):
    sumI (ls.map g) f = sumI ls (fun a=>f (g a)) := by simp [sumI,List.map_map,Function.comp_def]
theorem sumI_flatMap {A B:Type} (l:List A) (g:A → List B) (f:B → Int):
    sumI (l.flatMap g) f = sumI l (fun a=>sumI (g a) f) := by
  induction l with
  | nil=>rfl
  | cons x xs ih=>rw [List.flatMap_cons,sumI_append,ih,sumI_cons]
theorem sumI_swap {A B:Type} (l:List A) (q:List B) (f:A → B → Int):
    sumI l (fun a=>sumI q (f a))=sumI q (fun b=>sumI l (fun a=>f a b)) := by
  induction l with
  | nil=>
    change 0=sumI q (fun _=>0)
    induction q with
    | nil=>rfl
    | cons q qs ih=>rw [sumI_cons,Int.zero_add,←ih]
  | cons a as ih=>simp only [sumI_cons,ih,sumI_add]

def corr (ds:List (Bool×Bool)) (a b:List Nat) : Int :=
    sumI (all ds.length) (fun y=>value ds (add a y)*value ds (add b y))

theorem corr_mul (d j:Bool) (ds:List (Bool×Bool)) (a b:Nat) (as bs:List Nat) :
    corr ((d,j)::ds) (a::as) (b::bs)=localCorr d j a b*corr ds as bs := by
  unfold corr
  rw [List.length_cons,all,sumI_flatMap]
  simp only [sumI_map,add,List.zipWith_cons_cons,value,Prod.fst,Prod.snd]
  have sep (y:Nat): sumI (all ds.length) (fun v=>
       (sgn (bitAt (a ^^^ y) d j)*value ds (List.zipWith Nat.xor as v))*
       (sgn (bitAt (b ^^^ y) d j)*value ds (List.zipWith Nat.xor bs v))) =
      (sgn (bitAt (a ^^^ y) d j)*sgn (bitAt (b ^^^ y) d j))*
      sumI (all ds.length) (fun v=>value ds (add as v)*value ds (add bs v)) := by
    rw [←sumI_mul]
    unfold sumI
    apply congrArg List.sum
    apply List.map_congr_left
    intro p _;change (_*_)*(_*_) = (_*_)*(_*_)
    change _*_*( _*_)= _*_*( _*_)
    ac_rfl
  calc
    _ = sumI (List.range 8) (fun y=>(sgn (bitAt (a^^^y) d j)*sgn (bitAt (b^^^y) d j))*corr ds as bs) :=
      congrArg (sumI (List.range 8)) (funext sep)
    _ = _ := by
      rw [sumI_mul_right]
      rfl

theorem cube_bound (ds:List (Bool×Bool)) (a b:List Nat)
    (aa:fits a ds.length) (bb:fits b ds.length):
    (corr ds a b).natAbs ≤ 4^ds.length*weight a b := by
  induction ds generalizing a b with
  | nil=>
    cases a with
    | cons x xs=>obtain ⟨_,_,q,_⟩:=aa;cases q
    | nil=>
      cases b with
      | cons x xs=>obtain ⟨_,_,q,_⟩:=bb;cases q
      | nil=>decide
  | cons D ds ih=>
    obtain ⟨d,j⟩:=D
    cases a with
    | nil=>cases aa
    | cons a as=>
      cases b with
      | nil=>cases bb
      | cons b bs=>
        obtain ⟨ha,na,ea,restA⟩:=aa
        obtain ⟨hb,nb,eb,restB⟩:=bb
        have atA:na=ds.length:=by simp at ea;omega
        have atB:nb=ds.length:=by simp at eb;omega
        subst na nb
        rw [corr_mul,Int.natAbs_mul]
        have q:=Nat.mul_le_mul (local_bound d j a b ha hb) (ih as bs restA restB)
        apply Nat.le_trans q
        change (if a=b then 8 else 4)*(4^ds.length*weight as bs) ≤ 
          4^(ds.length+1)*((if a=b then 2 else 1)*weight as bs)
        rw [Nat.pow_succ]
        by_cases ab:a=b
        · simp only [ab,ite_true]
          rw [show 8=4*2 by rfl]
          have e:(4*2)*(4^ds.length*weight as bs)=4^ds.length*4*(2*weight as bs):=by ac_rfl
          exact Nat.le_of_eq e
        · simp only [ab,ite_false,Nat.one_mul]
          have e:4*(4^ds.length*weight as bs)=4^ds.length*4*weight as bs:=by ac_rfl
          exact Nat.le_of_eq e

end G32018.Corr

namespace AC32018
open G32018.Corr
theorem addV_cancel {n} (x y : BV n) : addV (addV x y) y = x := by
 funext j; simp only [addV]; cases x j <;> cases y j <;> rfl
theorem addV_comm {n} (x y : BV n) : addV x y = addV y x := by
 funext j; exact Bool.xor_comm .. 

def words : (m : Nat) → BV (3*m) → List Nat
 | 0,_ => []
 | m+1,x => word3 x :: words m (dropV 3 x)

theorem fits_words (m : Nat) (v : BV (3*m)) : G32018.Corr.fits (words m v) m := by
 induction m with
 | zero => rfl
 | succ m ih => exact ⟨word3_lt _,m,rfl,ih _⟩

theorem word3_add_zero {n : Nat} (x y : BV (n+3)) : word3 (addV x y) = 0 ↔ word3 x = word3 y := by
 change (xor (x 0) (y 0)).toNat+2*(xor (tailV x 0) (tailV y 0)).toNat+
   4*(xor (tailV (tailV x) 0) (tailV (tailV y) 0)).toNat = 0 ↔ _
 unfold word3; cases x 0 <;> cases y 0 <;> cases tailV x 0 <;> cases tailV y 0 <;>
   cases tailV (tailV x) 0 <;> cases tailV (tailV y) 0 <;> decide

theorem pair_weight (m) (x y : BV (3*m)) :
 G32018.Corr.weight (words m x) (words m y) = blockWeight m (addV y x) := by
 induction m with
 | zero => rfl
 | succ m ih =>
   simp only [words,G32018.Corr.weight,blockWeight,word3_add_zero]
   rw [ih]; by_cases h:word3 x=word3 y
   · simp [h] <;> rfl
   · simp [h,Ne.symm h] <;> rfl

def unwords : (m : Nat) → List Nat → BV (3*m)
 | 0,_ => zeroV
 | m+1,xs => let a := xs.headD 0
             consV (a.testBit 0) (consV (a.testBit 1) (consV (a.testBit 2) (unwords m xs.tail)))

theorem unwords_words (m) (x : BV (3*m)) : unwords m (words m x) = x := by
 induction m with
 | zero => funext i; exact Fin.elim0 i
 | succ m ih =>
   apply word3_inj_over_tail
   · simp only [unwords,words,List.headD_cons,List.tail_cons]; unfold word3
     simp only [consV_zero,tailV_consV]
     cases x 0 <;> cases tailV x 0 <;> cases tailV (tailV x) 0 <;> rfl
   · exact ih (dropV 3 x)

theorem words_unwords {m} (xs) (h:G32018.Corr.fits xs m) : words m (unwords m xs) = xs := by
 induction m generalizing xs with
 | zero =>
   cases xs with | nil => rfl | cons a l => obtain ⟨_,_,he,_⟩:=h; cases he
 | succ m ih =>
   cases xs with
   | nil => cases h
   | cons a l =>
     obtain ⟨ha,u,he,hl⟩:=h; cases he
     simp only [words,unwords,List.headD_cons,List.tail_cons,dropV,tailV_consV]
     rw [ih l hl]
     congr 1
     have eq : a=0∨a=1∨a=2∨a=3∨a=4∨a=5∨a=6∨a=7 := by omega
     rcases eq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem mem_all_iff (m) (x : List Nat) : x ∈ G32018.Corr.all m ↔ G32018.Corr.fits x m := by
 induction m generalizing x with
 | zero => cases x <;> simp [G32018.Corr.all,G32018.Corr.fits]
 | succ m ih =>
   simp only [G32018.Corr.all,List.mem_flatMap,List.mem_map,List.mem_range]
   cases x with
   | nil => simp [G32018.Corr.fits]
   | cons a xs =>
     simp only [List.cons.injEq,G32018.Corr.fits,Nat.succ.injEq]
     constructor
     · rintro ⟨a,ha,b,hb,e1,e2⟩; subst_vars; exact ⟨ha,_,rfl,(ih _).1 hb⟩
     · rintro ⟨ha,m',he,hm⟩; cases he; exact ⟨_,ha,_,(ih _).2 hm,rfl,rfl⟩

theorem nodup_map_inj {A B} (xs : List A) (f : A → B) (inj : ∀ x y,f x=f y → x=y)
 (nd : xs.Nodup) : (xs.map f).Nodup := by
 apply List.pairwise_map.2
 exact nd.imp (fun h e => h (inj _ _ e))

theorem walk_perm {A} (xs ys : List A) (h : xs.Perm ys) (f : A → Nat) :
 walk xs f = walk ys f := by
 induction h with
 | nil => rfl
 | cons a h ih => exact congrArg (fun n=>f a+n) ih
 | swap a b l => change f _ + (f _ + _)=f _+(f _+_); ac_rfl
 | trans _ _ h1 h2 => exact h1.trans h2

theorem row_rate {B m} (t : Tr B) (cs : Nat → Feat (3*m))
 (S : List (BV (3*m))) (nd : S.Nodup) (a : BV (3*m))
 (hs : ∀x, x∈S ↔ t.trace (fun j=>(cs j).ev x) = t.trace (fun j=>(cs j).ev a))
 (r : Nat) (fit : 3*r+t.depth ≤ 3*m) :
 16^r * walk S (fun b=>G32018.Corr.weight (words m a) (words m b)) ≤ 9^r * (2^m*S.length) := by
 obtain ⟨f,hd,hf⟩:=trace_fan t cs a
 have hr : 3*r ≤ f.rank := by omega
 let T := S.map (fun b=>addV b a)
 have hnd : T.Nodup := nodup_map_inj _ _ (fun x y he=> by
   have h:=congrArg (fun v=>addV v a) he; simpa only [addV_cancel] using h) nd
 have pe : T.Perm f.enum := (List.perm_ext_iff_of_nodup hnd f.enum_nodup).2 (by
   intro z; rw [f.mem_enum]
   constructor
   · intro h; obtain ⟨b,hb,rfl⟩:=List.mem_map.1 h
     exact (hf b).1 ((hs b).1 hb)
   · intro h; apply List.mem_map.2; refine ⟨addV z a,?_,addV_cancel ..⟩
     apply (hs _).2; apply (hf _).2; simpa only [addV_cancel] using h)
 have e : walk S (fun b=>G32018.Corr.weight (words m a) (words m b)) = walk f.enum (blockWeight m) := by
   rw [←walk_perm T f.enum pe (blockWeight m)]
   simp only [T,walk,List.map_map,Function.comp_def,pair_weight]
 have eq : S.length=f.enum.length := by simpa only [T,List.length_map] using pe.length_eq
 rw [e,eq]; exact f.rate r hr

theorem pair_rate {B m} (t : Tr B) (cs : Nat → Feat (3*m))
 (S : List (BV (3*m))) (nd : S.Nodup)
 (hs : ∀a∈S,∀x, x∈S ↔ t.trace (fun j=>(cs j).ev x) = t.trace (fun j=>(cs j).ev a))
 (r : Nat) (fit : 3*r+t.depth ≤ 3*m) :
 16^r * walk S (fun a=> walk S (fun b=> G32018.Corr.weight (words m a) (words m b))) ≤ 
 S.length*(9^r*(2^m*S.length)) := by
 rw [Nat.mul_comm (16^r),←walk_mul,←walk_const S]
 apply walk_le
 intro a ha
 rw [Nat.mul_comm _ (16^r)]
 exact row_rate t cs S nd a (hs a ha) r fit

end AC32018

namespace G32018.Chart
open AC32018
open G32018.Corr

theorem drop_at {m:Nat} (x:BV (3*(m+1))) (j:Fin (3*m)) :
    dropV 3 x j=x ⟨j.val+3,by have :=j.isLt;omega⟩ := rfl
theorem group_succ {m:Nat} (i:Fin m) (j:Fin 3) :
    (⟨(groupSlot i j).val+3,by have h: (groupSlot i j).val < 3*m:=(groupSlot i j).isLt;omega⟩ : Fin (3*(m+1))) =
      groupSlot i.succ j := by
  apply Fin.ext;change 3*i.val+j.val+3=3*(i.val+1)+j.val;omega

theorem words_at (m:Nat) (x:BV (3*m)) (i:Fin m) :
    (words m x).getD i.val 0=code (x (groupSlot i 0)) (x (groupSlot i 1)) (x (groupSlot i 2)) := by
  induction m with
  | zero=>exact Fin.elim0 i
  | succ m ih=>
    refine Fin.cases ?_ (fun j=> ?_) i
    · rfl
    · change (word3 x :: words m (dropV 3 x)).getD (j.val+1) 0=_
      rw [List.getD_cons_succ,ih (dropV 3 x) j]
      simp only [drop_at,group_succ]

theorem signed_xor (a b:Bool):sgn (xor a b)=sgn a*sgn b := by
  cases a <;> cases b <;>rfl
def bitXor : List (Bool×Bool) → List Nat → Bool
| [],_=>false
| _,[]=>false
| (D,J)::ds,x::xs=>xor (bitAt x D J) (bitXor ds xs)
theorem sign_value (ds:List (Bool×Bool)) (xs:List Nat) :
    sgn (bitXor ds xs)=value ds xs := by
  induction ds generalizing xs with
  | nil=>rfl
  | cons h hs ih=>
    obtain ⟨D,J⟩:=h
    cases xs with
    | nil=>rfl
    | cons a as=>simp [bitXor,value,signed_xor,ih]

theorem list_parity (m:Nat) (par:Fin m → Bool×Bool) (x:BV (3*m)) :
    bitXor (List.ofFn par) (words m x) =
      ((List.ofFn (fun i:Fin m=>bitAt (code (x (groupSlot i 0)) (x (groupSlot i 1)) (x (groupSlot i 2)))
             (par i).1 (par i).2)).foldr xor false) := by
  induction m with
  | zero=>rfl
  | succ m ih=>
    rw [List.ofFn_succ,List.ofFn_succ]
    change xor _ (bitXor (List.ofFn (fun i=>par i.succ)) (words m (dropV 3 x))) =
      xor _ ((List.ofFn _).foldr xor false)
    rw [ih (fun i=>par i.succ) (dropV 3 x)]
    simp only [drop_at,group_succ]
    rfl

end G32018.Chart

namespace G32018.Finite
open G32018.Keys G32018.Chart G32018.Corr
open AC32018
open scoped BigOperators

noncomputable def fiber {k n:Nat} (l:Layout k n) (row ref:Word k) : Finset (Word k) := by
  classical
  exact (Finset.univ : Finset (Word k)).filter (pinned l row ref)

theorem mem_fiber {k n:Nat} (l:Layout k n) (row ref key:Word k) :
  key∈fiber l row ref ↔ pinned l row ref key := by
  classical
  simp [fiber]

theorem canonFilter {A:Type} (s:Finset A) (p:A → Prop) (inst:DecidablePred p) :
    @Finset.filter A p inst s=@Finset.filter A p (fun a=>Classical.propDecidable (p a)) s := by
  ext x; simp only [Finset.mem_filter]

theorem ratio_transport {A:Type} {s t:Finset A} {p q:A → Prop}
    {hp:DecidablePred p} {hq:DecidablePred q}
    (hs:s=t) (test:∀ a,p a ↔ q a) :
    ((@Finset.filter A p hp s).card:ℚ)/(s.card:ℚ) =
      ((@Finset.filter A q hq t).card:ℚ)/(t.card:ℚ) := by
  have filters : @Finset.filter A p hp s = @Finset.filter A q hq t := by
    ext a
    simp only [Finset.mem_filter,hs,test]
  rw [filters,hs]

theorem sumProd {A:Type} (f:Finset A) (g:A → A → Int) :
    (∑ z ∈ f.product f,g z.1 z.2) = (∑ a ∈ f,∑ b ∈ f,g a b) :=
  Finset.sum_product' f f g

theorem sumList {A:Type} (f:Finset A) (g:A → Int) :
    sumI f.toList g = ∑ a ∈ f,g a :=
  Finset.sum_map_toList f g

theorem signed_count {A:Type} (s:Finset A) (f g:A → Bool) :
  (∑x∈s,sgn (f x)*sgn (g x))=
    2*((s.filter (fun x=>f x=g x)).card:Int)-(s.card:Int) := by
  classical
  have pair (x:A):sgn (f x)*sgn (g x)=(2*(if f x=g x then 1 else 0)-1:ℤ) := by
    cases f x <;> cases g x <;> decide
  simp only [pair,Finset.sum_sub_distrib,←Finset.mul_sum,Finset.sum_boole,Finset.sum_const,nsmul_one]

theorem rat_convert (N q r:Nat) (pos:0 < N)
    (h:4^r*(2*(q:Int)-(N:Int)).natAbs ≤ 3^r*N) :
    (4:ℚ)^r*|2*((q:ℚ)/(N:ℚ))-1| ≤ (3:ℚ)^r := by
  let d:Int:=2*(q:Int)-(N:Int)
  have den:(0:ℚ) < N:=by exact_mod_cast pos
  have exactAbs:(((d.natAbs:Nat):ℚ))=|(d:ℚ)| := by
    rw [Nat.cast_natAbs (α:=ℚ),Int.cast_abs]
  change 4^r*d.natAbs ≤ 3^r*N at h
  have hb:(4:ℚ)^r*(d.natAbs:ℚ) ≤ (3:ℚ)^r*(N:ℚ) := by exact_mod_cast h
  rw [exactAbs] at hb
  have eq:2*((q:ℚ)/(N:ℚ))-1=(d:ℚ)/(N:ℚ) := by
    dsimp [d];push_cast
    field_simp [ne_of_gt den]
  rw [eq,abs_div,abs_of_pos den,←mul_div_assoc]
  apply (div_le_iff₀ den).2 hb

theorem threshold (rM slots:Nat) (p:ℚ)
    (rule:∀ r:Nat,3*r+slots ≤ 3*rM → (4:ℚ)^r*|2*p-1| ≤ (3:ℚ)^r)
    (good:(3:ℚ)/4 ≤ p) : 3*rM ≤ slots+8 := by
  by_contra no
  have h:=rule 3 (by omega)
  have bb:0 ≤ 2*p-1:=by linarith
  rw [abs_of_nonneg bb] at h
  norm_num at h
  linarith

end G32018.Finite

namespace G32018.Assemble
open G32018.Keys G32018.Chart G32018.Corr G32018.Actual G32018.Finite AC32018

def offsets {k:Nat} (C:Nat → Word k) (row ref:Word k) (p:Nat) (j:Fin 3):Bool :=
  if j.val=0 then xor (O k C row.val ref.val p 7) (O k C row.val ref.val p 8)
  else if j.val=1 then O k C row.val ref.val p 7 else O k C row.val ref.val p 8

theorem read_in {k:Nat} (C:Nat → Word k) (hk:0 < k) (row q:Word k) (p:Nat) :
   chart k row q ⟨p % k,Nat.mod_lt _ hk⟩=bit k C row.val 0 q.val p := (bit_zero C hk row q p).symm

theorem slot_align {k m:Nat} (hk:12 ≤ k) (C:Nat → Word k) (row ref q:Word k) (starts:Fin m → Nat)
    (P:Fin k → Prop)
    (inj:∀ a b:Fin m×Fin 12,(starts a.1+a.2.val) % k=(starts b.1+b.2.val) % k → a=b)
    (free:∀i j,¬P (groupIndex k (by omega) starts i j)) (i:Fin m) :
  let l:=mkLayout hk starts P inj free (fun a=>offsets C row ref (starts a))
  slot C row.val ref.val (starts i) q.val =
    code (activeBits l row q (groupSlot i 0)) (activeBits l row q (groupSlot i 1))
      (activeBits l row q (groupSlot i 2)) := by
  dsimp only
  unfold activeBits mkLayout
  simp only [locate_slot,phase_slot,groupIndex]
  simp [offsets,read_in C (by omega),slot,triple,O,Nat.add_assoc]

def params {k m:Nat} (C:Nat → Word k) (row ref:Word k) (starts:Fin m → Nat) (i:Fin m) : Bool×Bool :=
  let p:=starts i
  (x3 (alpha C row.val ref.val p) (beta C row.val ref.val p) (delta C row.val ref.val p),
    Actual.inj k C 2 ref.val (p+5))

theorem list_sum_xor (l:List Bool) : ((l.map Bool.toNat).sum % 2==1)=l.foldr xor false := by
  induction l with
  | nil=>rfl
  | cons b l ih=>
    rw [List.map_cons,List.sum_cons,List.foldr_cons,←ih]
    cases hb:b
    · simp
    · simp only [Bool.toNat_true]
      have max:(l.map Bool.toNat).sum % 2 < 2:=Nat.mod_lt _ (by decide)
      have casesN:(l.map Bool.toNat).sum % 2=0 ∨ (l.map Bool.toNat).sum % 2=1:=by omega
      rw [Nat.add_mod 1]
      rcases casesN with e|e <;>rw [e] <;>decide

theorem sum_ofFn {m:Nat} (f:Fin m → Bool) :
    ((List.ofFn f).map Bool.toNat).sum=∑i:Fin m,(f i).toNat := by
  induction m with
  | zero=>simp
  | succ m ih=>rw [List.ofFn_succ,List.map_cons,List.sum_cons,Fin.sum_univ_succ,ih]

theorem sign_truth {k m:Nat} (hk:12 ≤ k) (C:Nat → Word k) (row ref q:Word k) (starts:Fin m → Nat)
    (P:Fin k → Prop)
    (inj:∀ a b:Fin m×Fin 12,(starts a.1+a.2.val) % k=(starts b.1+b.2.val) % k → a=b)
    (free:∀i j,¬P (groupIndex k (by omega) starts i j))
    (goodAll:∀i,good C row.val ref.val (starts i)) (fix:∀i,fixed C row ref (starts i) q):
  let l:=mkLayout hk starts P inj free (fun a=>offsets C row ref (starts a))
  sgn ((∑i:Fin m,(bit k C row.val 2 q.val (starts i+5)).toNat) % 2==1)=
    value (List.ofFn (params C row ref starts)) (words m (activeBits l row q)) := by
  dsimp only
  let l:=mkLayout hk starts P inj free (fun a=>offsets C row ref (starts a))
  rw [←sum_ofFn,list_sum_xor,←sign_value,list_parity]
  have fEq : (fun i:Fin m=>bit k C row.val 2 q.val (starts i+5)) =
      (fun i:Fin m=>bitAt
        (code (activeBits l row q (groupSlot i 0)) (activeBits l row q (groupSlot i 1))
          (activeBits l row q (groupSlot i 2))) (params C row ref starts i).1 (params C row ref starts i).2) := by
    funext i
    rw [donor_block hk C row ref q (starts i) (fix i) (goodAll i),slot_align hk C row ref q starts P inj free i]
    rfl
  rw [fEq]
end G32018.Assemble

namespace G32018.Corr
theorem sumI_le {A:Type} (l:List A) (f g:A → Int) (h:∀a∈l,f a ≤ g a):
    sumI l f ≤ sumI l g := by
  induction l with
  | nil=>exact Int.le_refl _
  | cons a as ih=>
    simp only [sumI_cons]
    exact Int.add_le_add (h _ (by simp)) (ih (fun x he=>h x (by simp [he])))

theorem sumI_const {A:Type} (l:List A) (b:Int) : sumI l (fun _=>b)=(l.length:Int)*b := by
  induction l with
  | nil=>simp [sumI]
  | cons a as ih=>
    simp only [sumI_cons,ih,List.length_cons,Int.natCast_succ,Int.add_mul,Int.one_mul]
    ac_rfl

theorem int_ineq (a b:Int):2*(a*b) ≤ a*a+b*b := by
  have h:(0:Int) ≤ (a-b)*(a-b):=by
    by_cases n:0 ≤ a-b
    · exact Int.mul_nonneg n n
    · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  rw [Int.sub_mul,Int.mul_sub,Int.mul_sub,Int.mul_comm b a] at h
  omega

theorem cauchy {A:Type} (l:List A) (f:A → Int) :
    (sumI l f)*(sumI l f) ≤ (l.length:Int)*sumI l (fun a=>f a*f a) := by
  let s:=sumI l f
  let q:=sumI l (fun a=>f a*f a)
  have split1: sumI l (fun a=>sumI l (fun b=>2*(f a*f b)))=2*(s*s) := by
    simp only [sumI_mul];rw [sumI_mul_right]
  have split2: sumI l (fun a=>sumI l (fun b=>f a*f a+f b*f b))=2*((l.length:Int)*q) := by
    simp only [sumI_add,sumI_const]
    rw [sumI_mul]
    change ((l.length:Int)*q)+((l.length:Int)*q)=2*((l.length:Int)*q)
    omega
  have le:=sumI_le l (fun a=>sumI l (fun b=>2*(f a*f b)))
    (fun a=>sumI l (fun b=>f a*f a+f b*f b))
    (fun a _=>sumI_le l _ _ (fun b _=>int_ineq (f a) (f b)))
  rw [split1,split2] at le
  change s*s ≤ (l.length:Int)*q
  omega

def convolve (ds:List (Bool×Bool)) (S:List (List Nat)) (y:List Nat):Int :=
    sumI S (fun x=>value ds (add x y))
def bias (ds:List (Bool×Bool)) (S:List (List Nat)) (pred:List Nat → Bool):Int :=
    sumI (all ds.length) (fun y=>sgn (pred y)*convolve ds S y)

theorem size_all (m:Nat):(all m).length=8^m := by
  induction m with
  | zero=>rfl
  | succ m ih=>
    simp only [all,List.length_flatMap,List.length_map]
    have rep (R:List Nat): (R.map (fun _=>(all m).length)).sum=R.length*(all m).length := by
      induction R with
      | nil=>simp
      | cons a ar rh=>simp [rh,Nat.succ_mul,Nat.add_comm]
    rw [rep,List.length_range,ih,Nat.pow_succ,Nat.mul_comm]

theorem expand_square (ds:List (Bool×Bool)) (S:List (List Nat)) (y:List Nat) :
    (convolve ds S y)*(convolve ds S y)=
      sumI S (fun a=>sumI S (fun b=>value ds (add a y)*value ds (add b y))) := by
  unfold convolve
  simp only [sumI_mul]
  rw [sumI_mul_right]

theorem cauchy_bias (ds:List (Bool×Bool)) (S:List (List Nat)) (pred:List Nat → Bool) :
    bias ds S pred * bias ds S pred ≤ (8^ds.length:Nat)*(sumI S (fun a=>sumI S (corr ds a))) := by
  have q:=cauchy (all ds.length) (fun y=>sgn (pred y)*convolve ds S y)
  have toggle (y:List Nat):
    (sgn (pred y)*convolve ds S y)*(sgn (pred y)*convolve ds S y) =
      convolve ds S y*convolve ds S y := by
    have step: (sgn (pred y)*convolve ds S y)*(sgn (pred y)*convolve ds S y) =
      (sgn (pred y)*sgn (pred y))*(convolve ds S y*convolve ds S y) := by ac_rfl
    rw [step]
    have bit:(sgn (pred y)*sgn (pred y))=1 := by cases pred y <;> decide
    rw [bit,Int.one_mul]
  simp only [toggle,expand_square,size_all] at q
  have e : sumI (all ds.length) (fun y=>sumI S (fun a=>sumI S (fun b=>value ds (add a y)*value ds (add b y)))) =
      sumI S (fun a=>sumI S (corr ds a)) := by
    rw [sumI_swap]
    change sumI S _=sumI S _
    unfold corr
    have f : (fun a=>sumI (all ds.length) (fun y=>sumI S (fun b=>value ds (add a y)*value ds (add b y)))) =
        (fun a=>sumI S (fun b=>sumI (all ds.length) (fun y=>value ds (add a y)*value ds (add b y)))) :=
      funext (fun _=>sumI_swap ..)
    rw [f]
  rw [e] at q
  exact q

theorem absToLe (u:Int) (b:Nat) (h:u.natAbs ≤ b) : u ≤ b := by
  have q:u ≤ u.natAbs:=Int.le_natAbs
  omega

theorem cauchy_kernel (ds:List (Bool×Bool)) (S:List (List Nat)) (pred:List Nat → Bool)
    (fit:∀a∈S,fits a ds.length) :
    bias ds S pred * bias ds S pred ≤ (32^ds.length:Nat)*(sumI S (fun a=>sumI S (fun b=>weight a b))) := by
  have q:=cauchy_bias ds S pred
  have h : sumI S (fun a=>sumI S (corr ds a)) ≤ 
      sumI S (fun a=>sumI S (fun b=>(4^ds.length:Nat)*(weight a b:Int))) := by
    apply sumI_le
    intro a ha;apply sumI_le;intro b hb
    have cap:=absToLe _ _ (cube_bound ds a b (fit a ha) (fit b hb))
    exact cap
  have bigger := Int.mul_le_mul_of_nonneg_left h (Int.natCast_nonneg (8^ds.length))
  apply Int.le_trans q
  simp only [sumI_mul] at bigger
  rw [← Int.mul_assoc] at bigger
  have eq : (((8^ds.length:Nat):Int)*((4^ds.length:Nat):Int))=(32^ds.length:Nat) := by
    rw [←Int.natCast_mul,←Nat.mul_pow] <;> rfl
  rw [eq] at bigger
  exact bigger

end G32018.Corr

namespace AC32018
open G32018 G32018.Corr

theorem int_walk {A} (xs : List A) (f : A → Nat) :
 sumI xs (fun x=> (f x : Int)) = (walk xs f : Int) := by
 induction xs with
 | nil => rfl
 | cons a l ih => rw [sumI_cons,ih]; exact (Int.natCast_add ..).symm

theorem walk_map {A B} (xs:List A) (g:A → B) (f:B → Nat) :
 walk (xs.map g) f=walk xs (fun x=>f (g x)) := by simp [walk,List.map_map,Function.comp_def]

theorem leaf_rate {B} (ds : List (Bool×Bool)) (t : Tr B) (cs : Nat → Feat (3*ds.length))
 (S : List (BV (3*ds.length))) (nd : S.Nodup)
 (hs : ∀a∈S,∀x, x∈S ↔ t.trace (fun j=>(cs j).ev x) = t.trace (fun j=>(cs j).ev a))
 (pred : List Nat → Bool) (r : Nat) (fit : 3*r+t.depth ≤ 3*ds.length) :
 4^r * (bias ds (S.map (words ds.length)) pred).natAbs ≤ 3^r*8^ds.length*S.length := by
 let m := ds.length
 let W := walk S (fun a=>walk S (fun b=>weight (words m a) (words m b)))
 let Z := (bias ds (S.map (words m)) pred).natAbs
 have w := pair_rate t cs S nd hs r fit
 change 16^r*W ≤ S.length*(9^r*(2^m*S.length)) at w
 have b := cauchy_kernel ds (S.map (words m)) pred (by
   intro a ha; obtain ⟨v,_,rfl⟩ := List.mem_map.1 ha; exact fits_words _ _)
 simp only [int_walk,walk_map] at b
 rw [←Int.natAbs_mul_self,←Int.natCast_mul] at b
 have b' : Z^2 ≤ 32^m * W := by
   change (↑(Z*Z):Int) ≤ ↑(32^m*W) at b
   have ineq : Z*Z ≤ 32^m*W := Int.ofNat_le.mp b
   simpa [Nat.pow_succ] using ineq
 have pc : (4^r*Z)^2 ≤ (3^r*8^m*S.length)^2 := by
   calc
    _ = 16^r*Z^2 := by rw [Nat.mul_pow,←Nat.pow_mul,Nat.mul_comm r 2,Nat.pow_mul] <;> rfl
    _ ≤ 16^r*(32^m*W) := Nat.mul_le_mul_left _ b'
    _ = 32^m*(16^r*W) := by ac_rfl
    _ ≤ 32^m*(S.length*(9^r*(2^m*S.length))) := Nat.mul_le_mul_left _ w
    _ = (3^r*8^m*S.length)^2 := by
      have p9 : 9^r=(3^r)^2 := by rw [←Nat.pow_mul,Nat.mul_comm r 2,Nat.pow_mul] <;> rfl
      have p64 : 32^m*2^m=(8^m)^2 := by rw [←Nat.mul_pow,←Nat.pow_mul,Nat.mul_comm m 2,Nat.pow_mul] <;> rfl
      rw [Nat.mul_pow,Nat.mul_pow,← p9,← p64,Nat.pow_succ S.length 1,Nat.pow_one]; ac_rfl
 exact Nat.le_of_not_gt (fun h => Nat.not_le_of_gt (Nat.pow_lt_pow_left h (by decide : 2 ≠ 0)) pc)

def cubeBias {B} (ds : List (Bool×Bool)) (t : Tr B) (cs : Nat → Feat (3*ds.length))
 (xs : List (BV (3*ds.length))) (pred : B → List Nat → Bool) : Int :=
 sumI xs (fun x=>sumI (all ds.length) (fun y=>
  sgn (pred (t.run (fun j=>(cs j).ev x)) y)*value ds (add (words ds.length x) y)))

theorem cubeBias_leaf {B} (ds : List (Bool×Bool)) (t : Tr B) (cs : Nat → Feat (3*ds.length))
 (xs : List (BV (3*ds.length))) (pred : B → List Nat → Bool) (a : BV (3*ds.length))
 (h : ∀x∈xs, t.trace (fun j=>(cs j).ev x)=t.trace (fun j=>(cs j).ev a)) :
 cubeBias ds t cs xs pred = bias ds (xs.map (words ds.length)) (pred (t.run (fun j=>(cs j).ev a))) := by
 let A := t.run (fun j=>(cs j).ev a)
 have he (x) (hx:x∈xs) : t.run (fun j=>(cs j).ev x) = A :=
   (t.trace_correct _ _ ((t.trace_iff _ _).1 (h x hx))).2
 unfold cubeBias bias convolve
 rw [sumI_swap]; simp only [sumI_map]
 apply congrArg (sumI (all ds.length))
 funext y
 rw [←sumI_mul]
 unfold sumI; apply congrArg List.sum; apply List.map_congr_left
 intro x hx; rw [he x hx]

theorem sumI_split {A} (xs : List A) (p : A → Bool) (f:A → Int) :
 sumI xs f = sumI (xs.filter p) f + sumI (xs.filter (fun x=>!(p x))) f := by
 induction xs with
 | nil => rfl
 | cons a l ih =>
   cases h:p a <;> simp only [List.filter_cons,h,Bool.not_false,Bool.not_true,
     Bool.false_eq_true,Bool.true_eq,ite_true,ite_false,sumI_cons,ih] <;> ac_rfl

theorem length_split {A} (xs : List A) (p : A → Bool) :
 xs.length = (xs.filter p).length+(xs.filter (fun x=>!(p x))).length := by
 induction xs with
 | nil => rfl
 | cons a l ih =>
   cases h:p a <;> simp only [List.length_cons,List.filter_cons,h,Bool.not_false,Bool.not_true,
     Bool.false_eq_true,Bool.true_eq,ite_true,ite_false,List.length_cons] <;> omega

theorem cube_rate_closed {B} (ds : List (Bool×Bool)) (t : Tr B) (cs : Nat → Feat (3*ds.length))
 (xs : List (BV (3*ds.length))) (nd : xs.Nodup) (pred : B → List Nat → Bool)
 (closed : ∀a∈xs,∀x, t.trace (fun j=>(cs j).ev x) = t.trace (fun j=>(cs j).ev a) → x∈xs)
 (r : Nat) (fit : 3*r+t.depth ≤ 3*ds.length) :
 4^r * (cubeBias ds t cs xs pred).natAbs ≤ 3^r*8^ds.length*xs.length := by
 classical
 match xs with
 | [] => simp [cubeBias,sumI]
 | a::L =>
   let V := BV (3*ds.length)
   let tag := fun x:V=>t.trace (fun j=>(cs j).ev x)
   let eqA := fun x:V=> decide (tag x = tag a)
   let S := (a::L).filter eqA
   let U := (a::L).filter (fun x=>!(eqA x))
   have ae : eqA a = true := by simp [eqA]
   have hS (x:V) : x∈S ↔ tag x=tag a := by
     simp only [S,List.mem_filter,eqA,decide_eq_true_eq]
     exact ⟨And.right,fun e=>⟨closed a (by simp) x e,e⟩⟩
   have hU (x:V) : x∈U ↔ x∈a::L ∧ tag x≠tag a := by
     simp only [U,List.mem_filter,eqA,Bool.not_eq_true',decide_eq_false_iff_not]
   have hUsmall : U.length < (a::L).length := by
     simp only [U,List.filter_cons,ae,Bool.not_true, Bool.false_eq_true,ite_false,List.length_cons]
     exact Nat.lt_succ_of_le (List.length_filter_le ..)
   have hC (b:V) (hb:b∈U) (x:V) (hx:tag x=tag b) : x∈U := by
     obtain ⟨hb1,hb2⟩:=(hU b).1 hb
     exact (hU x).2 ⟨closed b hb1 x hx,fun e=> hb2 (hx.symm.trans e)⟩
   have sNd : S.Nodup := List.Pairwise.filter _ nd
   have uNd : U.Nodup := List.Pairwise.filter _ nd
   have rateU := cube_rate_closed ds t cs U uNd pred hC r fit
   have rateS := leaf_rate ds t cs S sNd (fun b hb x=> by
       change x∈S ↔ tag x=tag b; rw [(hS b).1 hb,hS])
     (pred (t.run (fun j=>(cs j).ev a))) r fit
   rw [←cubeBias_leaf ds t cs S pred a (fun x hx=>(hS x).1 hx)] at rateS
   have split : cubeBias ds t cs (a::L) pred = cubeBias ds t cs S pred + cubeBias ds t cs U pred :=
     sumI_split (a::L) eqA _
   have lens : (a::L).length = S.length+U.length := length_split _ eqA
   rw [split,lens,Nat.mul_add]
   calc
    _ ≤ 4^r*((cubeBias ds t cs S pred).natAbs+(cubeBias ds t cs U pred).natAbs) :=
        Nat.mul_le_mul_left _ (Int.natAbs_add_le ..)
    _ = _ := Nat.mul_add ..
    _ ≤ _ := Nat.add_le_add rateS rateU
termination_by xs.length
decreasing_by exact hUsmall

theorem cube_rate {B} (ds : List (Bool×Bool)) (t : Tr B) (cs : Nat → Feat (3*ds.length))
 (xs : List (BV (3*ds.length))) (nd : xs.Nodup) (allx : ∀x,x∈xs) (pred : B → List Nat → Bool)
 (r : Nat) (fit : 3*r+t.depth ≤ 3*ds.length) :
 4^r * (cubeBias ds t cs xs pred).natAbs ≤ 3^r*8^ds.length*xs.length :=
 cube_rate_closed ds t cs xs nd pred (fun _ _ x _=>allx x) r fit

end AC32018

namespace AC32018
open G32018 G32018.Corr PEqualNP.CircuitLowerBounds

theorem all_nodup (m:Nat) : (all m).Nodup := by
 induction m with
 | zero => simp [all]
 | succ m ih =>
   apply flat_nodup_inv (List.range 8) (fun a=>(all m).map (List.cons a)) (List.headD (fallback:=0)) List.nodup_range
   · intro a; apply nodup_map_inj _ _ _ ih; intro x y e; exact (List.cons.inj e).2
   · intro a x hx; obtain ⟨b,_,rfl⟩ := List.mem_map.1 hx; rfl

theorem words_inj (m) (x y : BV (3*m)) (h:words m x=words m y) : x=y := by
 have he:=congrArg (unwords m) h; simpa only [unwords_words] using he

theorem words_add (m) (x y : BV (3*m)) : words m (addV x y) = add (words m x) (words m y) := by
 induction m with
 | zero => rfl
 | succ m ih =>
   simp only [words,add,List.zipWith_cons_cons]
   congr 1
   · change code (xor (x 0) (y 0)) (xor (tailV x 0) (tailV y 0))
      (xor (tailV (tailV x) 0) (tailV (tailV y) 0)) = _
     unfold word3; cases x 0 <;> cases y 0 <;> cases tailV x 0 <;> cases tailV y 0 <;>
       cases tailV (tailV x) 0 <;> cases tailV (tailV y) 0 <;> rfl
   · exact ih (dropV 3 x) (dropV 3 y)

theorem addV_assoc {n} (x y z:BV n) : addV (addV x y) z = addV x (addV y z) := by
 funext i; exact Bool.xor_assoc ..

theorem words_shift_perm (m) (vs : List (BV (3*m))) (nd:vs.Nodup) (full:∀v,v∈vs) (r : BV (3*m)) :
 (vs.map (fun v=>words m (addV v r))).Perm (all m) := by
 apply (List.perm_ext_iff_of_nodup
  (nodup_map_inj _ _ (fun a b h=> by
   have u:=congrArg (fun w=>addV w r) (words_inj m _ _ h)
   simpa only [addV_cancel] using u) nd) (all_nodup m)).2
 intro x; rw [mem_all_iff]
 constructor
 · intro h; obtain ⟨b,_,rfl⟩:=List.mem_map.1 h; exact fits_words m _
 · intro h; exact List.mem_map.2 ⟨addV (unwords m x) r,full _,by rw [addV_cancel,words_unwords x h]⟩

theorem sumI_perm {A} (xs ys : List A) (h : xs.Perm ys) (f : A → Int) :
 sumI xs f = sumI ys f := by
 induction h with
 | nil => rfl
 | cons a h ih => exact congrArg (fun n=>f a+n) ih
 | swap a b l => change f _ + (f _ + _)=f _+(f _+_); ac_rfl
 | trans _ _ h1 h2 => exact h1.trans h2

theorem sumI_ext {A} (xs : List A) (f g : A → Int) (h : ∀x∈xs,f x=g x) :
 sumI xs f = sumI xs g := by unfold sumI; rw [List.map_congr_left h]

def vecBias {B} (ds:List (Bool×Bool)) (t:Tr B) (cs:Nat → Feat (3*ds.length))
 (xs ys: List (BV (3*ds.length))) (ref: BV (3*ds.length))
 (pred:B → BV (3*ds.length) → Bool) : Int :=
 sumI xs (fun x=>sumI ys (fun y=>sgn (pred (t.run (fun j=>(cs j).ev x)) y) *
   value ds (words ds.length (addV (addV x y) ref))))

theorem vec_rate {B} (ds:List (Bool×Bool)) (t:Tr B) (cs:Nat → Feat (3*ds.length))
 (xs ys: List (BV (3*ds.length))) (nx:xs.Nodup) (ax:∀x,x∈xs)
 (ny:ys.Nodup) (ay:∀y,y∈ys)
 (ref: BV (3*ds.length)) (pred:B → BV (3*ds.length) → Bool)
 (r:Nat) (fit:3*r+t.depth ≤ 3*ds.length) :
 4^r*(vecBias ds t cs xs ys ref pred).natAbs ≤ 3^r*ys.length*xs.length := by
 let m := ds.length
 let p := fun b y=>pred b (addV (unwords m y) ref)
 have h:=cube_rate ds t cs xs nx ax p r fit
 have pp:=words_shift_perm m ys ny ay ref
 have yy:ys.length=8^m:=by simpa only [List.length_map,size_all] using pp.length_eq
 rw [yy]
 suffices eq:vecBias ds t cs xs ys ref pred=cubeBias ds t cs xs p by rw [eq];exact h
 unfold vecBias cubeBias
 apply sumI_ext
 intro x _
 rw [← sumI_perm _ _ pp, sumI_map]
 apply sumI_ext
 intro y _
 dsimp only [p]; rw [unwords_words,addV_cancel,addV_assoc,words_add]
 

theorem circuit_rate (k c : Nat) (C:Circuit) (tap:Fin c → Nat)
 (hc:∀ g∈C.gates,basis g.op g.inputs.length) (ds:List (Bool×Bool))
 (cs:Nat → Feat (3*ds.length)) (xs ys:List (BV (3*ds.length)))
 (nx:xs.Nodup) (ax:∀ x,x∈xs) (ny:ys.Nodup) (ay:∀ y,y∈ys)
 (ref:BV (3*ds.length)) (read:(Fin c → Bool) → BV (3*ds.length) → Bool) (r:Nat)
 (fit:3*r+c+C.gates.countP (fun g => @decide
 ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)) ≤ 3*ds.length):
 4^r*(sumI xs (fun x=>sumI ys (fun y=>sgn (read (fun j=>
    (C.wires (List.ofFn (fun i:Fin k=>(cs i.val).ev x))).getD (tap j) false) y) *
   value ds (words ds.length (addV (addV x y) ref))))).natAbs ≤ 3^r*ys.length*xs.length := by
 let t:=msgTree k c C tap
 have dep:=msgTree_depth k c C tap
 have g:3*r+t.depth ≤ 3*ds.length := by dsimp only [t]; omega
 have b:=vec_rate ds t cs xs ys nx ax ny ay ref read r g
 simpa only [vecBias,t,msgTree_run k c C tap hc] using b

end AC32018

namespace AC32018
open G32018 G32018.Corr G32018.Keys G32018.Chart PEqualNP.CircuitLowerBounds

theorem key_enum_perm {k n} (l : Layout k n) (row ref : Word k)
 (Es:List (Extras l → Bool)) (Hs:List (BV n)) (Ks:List (Word k))
 (en:Es.Nodup) (eall:∀e,e∈Es) (hn:Hs.Nodup) (hall:∀x,x∈Hs)
 (kn:Ks.Nodup) (kiff:∀q,q∈Ks ↔ pinned l row ref q) :
 Ks.Perm (Es.flatMap (fun e=>Hs.map (packInput l row ref e))) := by
 apply (List.perm_ext_iff_of_nodup kn _).2
 · intro a; rw [kiff,List.mem_flatMap]
   constructor
   · intro ha; refine ⟨_,eall _,List.mem_map.2 ⟨_,hall _,unpack_pack l row ref a ha⟩⟩
   · rintro ⟨e,_,h⟩; obtain ⟨x,_,rfl⟩:=List.mem_map.1 h; exact pack_valid l row ref e x
 · apply flat_nodup_inv Es _ (extraBits l row) en
   · intro e; apply nodup_map_inj _ _ _ hn
     intro x y h; have z:= congrArg (activeBits l row) h; simpa only [pack_active] using z
   · intro e x hx; obtain ⟨_,_,rfl⟩:=List.mem_map.1 hx; exact pack_extra ..

theorem abs_sum_cap {A} (L:List A) (v:A → Int) (M a:Nat) (h:∀x∈L,a*(v x).natAbs ≤ M) :
 a*(sumI L v).natAbs ≤ M*L.length := by
 induction L with
 | nil => simp [sumI]
 | cons x L ih =>
   rw [sumI_cons,List.length_cons,Nat.mul_succ]
   have s:=Nat.mul_le_mul_left a (Int.natAbs_add_le (v x) (sumI L v))
   rw [Nat.mul_add] at s
   have u:=ih (fun b hb=>h b (by simp [hb]))
   have w:=h x (by simp)
   omega

theorem fiber_circuit_rate {k m:Nat} (l : Layout k (3*m)) (row ref : Fin (2^k))
 (ds : List (Bool×Bool)) (hd : ds.length=m) (c:Nat) (C:Circuit) (tap:Fin c → Nat)
 (hc:∀g∈C.gates,basis g.op g.inputs.length) (read:(Fin c → Bool) → Fin (2^k) → Bool)
 (Es:List (Extras l → Bool)) (Hs:List (BV (3*m))) (Ks:List (Fin (2^k)))
 (en:Es.Nodup) (eall:∀e,e∈Es) (hn:Hs.Nodup) (hall:∀x,x∈Hs) (kn:Ks.Nodup)
 (kiff:∀q,q∈Ks ↔ pinned l row ref q) (r:Nat)
 (fit:3*r+c+C.gates.countP (fun g=>charged g.op g.inputs.length) ≤ 3*m) :
 4^r * (sumI Ks (fun a=>sumI Ks (fun b=> sgn (read (fun j=>
 (C.wires (List.ofFn (fun i:Fin k=>a.val.testBit i.val))).getD (tap j) false) b) *
 value ds (words m (activeBits l row (mix a b ref)))))).natAbs ≤ 3^r * Ks.length * Ks.length := by
 subst m
 let m:=ds.length
 let pack:=packInput l row ref
 let term:=fun a b:Word k=>sgn (read (fun j=>
 (C.wires (List.ofFn (fun i:Fin k=>a.val.testBit i.val))).getD (tap j) false) b) *
 value ds (words m (activeBits l row (mix a b ref)))
 let slice:=fun e f : Extras l → Bool =>
   sumI Hs (fun x=>sumI Hs (fun y=>term (pack e x) (pack f y)))
 have bound (e f : Extras l → Bool) : 4^r*(slice e f).natAbs ≤ 3^r*Hs.length*Hs.length := by
   let pred := fun b y=>read b (pack f y)
   have b:=circuit_rate k c C tap hc ds (rawFeat l row ref e) Hs Hs hn hall hn hall (activeBits l row ref) pred r fit
   simpa only [slice,term,pack,mix_active,pack_active,chart_raw,pred,m] using b
 have perm:=key_enum_perm l row ref Es Hs Ks en eall hn hall kn kiff
 have len : Ks.length=Es.length*Hs.length :=
   perm.length_eq.trans (flat_len_const _ _ _ (fun _ _=>List.length_map (f:=_)))
 have reindex (f:Word k → Int) : sumI Ks f=sumI Es (fun e=>sumI Hs (fun x=>f (pack e x))) := by
   rw [sumI_perm _ _ perm,sumI_flatMap]
   simp only [sumI_map,pack]
 have eq:sumI Ks (fun a=>sumI Ks (fun b=>term a b))=sumI Es (fun e=>sumI Es (fun f=>slice e f)) := by
   rw [reindex]; apply sumI_ext; intro e _
   calc
    _ = sumI Hs (fun x=>sumI Es (fun f=>sumI Hs (fun y=>term (pack e x) (pack f y)))) :=
       sumI_ext _ _ _ (fun x _=>reindex _)
    _ = _ := sumI_swap .. 
 have top:=abs_sum_cap Es (fun e=>sumI Es (fun f=>slice e f))
   (3^r*Hs.length*Hs.length*Es.length) (4^r)
   (fun e _=>abs_sum_cap Es (slice e) _ _ (fun f _=>bound e f))
 change 4^r * (sumI Ks (fun a=>sumI Ks (fun b=>term a b))).natAbs ≤ _
 rw [eq,len]
 exact Nat.le_trans top (Nat.le_of_eq (by ac_rfl))
end AC32018

open G32018.Keys G32018.Chart G32018.Corr G32018.Actual G32018.Finite G32018.Assemble
open AC32018
open scoped BigOperators

set_option maxRecDepth 2400 in
set_option maxHeartbeats 900000 in
theorem provedExact : (∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
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
  ∀ (m : Nat) (starts : Fin m → Nat),
  0 < m → Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val) % k) → 
  let good := fun (row ref : Fin (2^k)) (p : Nat) =>
    let old := fun (j : Nat) => bit row.val 0 ref.val (p+j)
    let first := fun (j : Nat) => bit row.val 1 ref.val (p+j)
    let τ := xor (xor (old 6) (old 7)) (old 8)
    let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injected 1 ref.val (p+6))
    let β := xor τ (injected 1 ref.val (p+7))
    τ = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
      xor (first 4) (first 5) = !α ∧ first 4 = β
  ∀ (row ref : Fin (2^k)), (∀ i, good row ref (starts i)) → 
  ∀ pin : Finset (Fin k),
  (∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i+j.val) % k) → 
  (∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val) % k) → 
  let K := Fin (2^k)
  let fiber := (Finset.univ : Finset K).filter (fun key =>
    ∀ z ∈ pin, bit row.val 0 key.val z.val = bit row.val 0 ref.val z.val)
  let pairs := fiber.product fiber
  let truth := fun (left right : K) =>
    let key := (left.val ^^^ right.val ^^^ ref.val) % 2^k
    (∑ i : Fin m, (bit row.val 2 key (starts i+5)).toNat) % 2 == 1
  let agree := fun (guess : K → K → Bool) =>
    (((pairs.filter (fun z => guess z.1 z.2 = truth z.1 z.2)).card : ℚ) / (pairs.card : ℚ))
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (C : Circ) =>
    (∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < k+i.val) ∧
    (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
      (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  ∀ (C : Circ), legal C → ∀ (c : Nat) (tap : Fin c → Nat),
    (∀ j, tap j < k+C.gates.length) → 
    let send := fun (x : K) (j : Fin c) =>
      let raw := List.ofFn (fun i : Fin k => x.val.testBit i.val)
      (C.wires raw).getD (tap j) false
    ∀ read : (Fin c → Bool) → K → Bool,
      let p := agree (fun x y => read (send x) y)
      (∀ r : Nat, 3*r+c+cost C ≤ 3*m → 
        (4 : ℚ)^r * |2*p-1| ≤ (3 : ℚ)^r) ∧
      ((3 : ℚ)/4 ≤ p → 3*m ≤ c+cost C+8)) := by
  intro k hk constant rot' step' state' injected' bit'
  intro m starts hm disjoint good' row ref goodAll pin hpin free
  intro K' fiber' pairs' truth' agree' Circ' legal' cost' C legal c tap tapLegal send' read p'
  classical
  have hk' := G32018.Actual.group_width hk hm starts disjoint
  let hdis : ∀ a b : Fin m × Fin 12,
      (starts a.1+a.2.val) % k = (starts b.1+b.2.val) % k → a=b := fun _ _ h=>disjoint h
  let off:=fun i=>offsets constant row ref (starts i)
  have unp : ∀i j, ¬ (groupIndex k hk starts i j ∈ pin) := by
    intro i j inside
    exact free i j _ inside rfl
  let l := mkLayout hk' starts (fun j=>j∈pin) hdis unp off
  let ps:=params constant row ref starts
  let ds:=List.ofFn ps
  let f := G32018.Finite.fiber l row ref
  let pairs:=f.product f
  let out := fun (a b:Word k) =>
     (∑ i:Fin m,(bit k constant row.val 2 (mix a b ref).val (starts i+5)).toNat) % 2==1
  let msg:=fun (x:Word k) (j:Fin c)=>
    (C.wires (List.ofFn (fun i:Fin k=>x.val.testBit i.val))).getD (tap j) false
  let goodPairs:=pairs.filter (fun z=>read (msg z.1) z.2=out z.1 z.2)
  let p:ℚ := (goodPairs.card:ℚ)/(pairs.card:ℚ)
  let gCost:=C.gates.countP (fun h=>@decide
    ((h.op=PEqualNP.CircuitLowerBounds.GateOp.and ∨ h.op=PEqualNP.CircuitLowerBounds.GateOp.or) ∧ h.inputs.length=2)
    (Classical.propDecidable _))
  have f_eq : f = fiber' := by
    ext q
    change q∈G32018.Finite.fiber l row ref ↔ q∈fiber'
    simp only [mem_fiber,fiber',Finset.mem_filter,Finset.mem_univ,true_and,pinned,l,mkLayout]
    have eqkey (x:Word k) (j:Fin k) : bit k constant row.val 0 x.val j.val=chart k row x j := by
      have h:=bit_zero constant hk row x j.val
      have eq:(⟨j.val % k,Nat.mod_lt _ hk⟩:Fin k)=j:=Fin.ext (Nat.mod_eq_of_lt j.isLt)
      rwa [eq] at h
    change (∀ z∈pin,chart k row q z=chart k row ref z) ↔
      (∀ z∈pin,bit k constant row.val 0 q.val z.val=bit k constant row.val 0 ref.val z.val)
    simp only [eqkey]
  have pairs_eq : pairs = pairs' :=
    congrArg (fun s:Finset (Word k)=>s.product s) f_eq
  have hf0:ref∈f:=(mem_fiber l row ref ref).mpr (fun _ _=>rfl)
  have hN:0 < pairs.card:=Finset.card_pos.mpr ⟨(ref,ref),Finset.mem_product.mpr ⟨hf0,hf0⟩⟩
  have fixedOn (q:Word k) (hq:pinned l row ref q) (i:Fin m) : fixed constant row ref (starts i) q := by
    intro j hj
    obtain ⟨z,mem,hz⟩:=hpin i ⟨j,hj⟩
    have zz : (⟨(starts i+j) % k,Nat.mod_lt _ hk⟩:Fin k)=z := Fin.ext hz.symm
    simpa only [bit_zero constant hk row q,bit_zero constant hk row ref,zz] using hq z mem
  have exactSign (a b:Word k) (ha:a∈f) (hb:b∈f) :
      G32018.sgn (out a b)=value ds (words m (activeBits l row (mix a b ref))) := by
    have pA: pinned l row ref a := (mem_fiber ..).mp ha
    have pB: pinned l row ref b := (mem_fiber ..).mp hb
    exact sign_truth hk' constant row ref (mix a b ref) starts (fun z=>z∈pin) hdis unp goodAll
      (fun i=>fixedOn _ (mix_pinned l row a b ref pA pB) i)
  have isBasis:∀g∈C.gates,basis g.op g.inputs.length:=legal.2
  have rules : ∀ r:Nat,3*r+c+gCost ≤ 3*m → (4:ℚ)^r*|2*p-1| ≤ (3:ℚ)^r := by
    intro r budget
    let E:List (Extras l → Bool):=(Finset.univ : Finset (Extras l → Bool)).toList
    let V:List (BV (3*m)):=(Finset.univ : Finset (BV (3*m))).toList
    let K:=f.toList
    have eAll:∀e,e∈E:=by intro e; exact Finset.mem_toList.mpr (Finset.mem_univ _)
    have vAll:∀x,x∈V:=by intro x; exact Finset.mem_toList.mpr (Finset.mem_univ _)
    have kIff:∀q,q∈K ↔ pinned l row ref q := fun q=>Finset.mem_toList.trans (mem_fiber ..)
    have dlen:ds.length=m:=List.length_ofFn
    have fit:3*r+c+C.gates.countP (fun h=>charged h.op h.inputs.length) ≤ 3*m := by simpa only [charged,gCost] using budget
    have hh:=fiber_circuit_rate l row ref ds dlen c C tap isBasis read E V K
      (Finset.nodup_toList _) eAll (Finset.nodup_toList _) vAll (Finset.nodup_toList _) kIff r fit
    let I:=sumI K (fun a=>sumI K (fun b=>G32018.sgn (read (msg a) b)*value ds (words m (activeBits l row (mix a b ref)))))
    have hEq : I = ∑ z ∈ pairs,G32018.sgn (read (msg z.1) z.2)*G32018.sgn (out z.1 z.2) := by
      change sumI f.toList (fun a=>sumI f.toList _) =
        ∑ z ∈ f.product f,G32018.sgn (read (msg z.1) z.2)*G32018.sgn (out z.1 z.2)
      rw [sumProd f (fun a b=>G32018.sgn (read (msg a) b)*G32018.sgn (out a b)),sumList]
      apply Finset.sum_congr rfl
      intro a am
      rw [sumList]
      apply Finset.sum_congr rfl
      intro b bm
      rw [exactSign a b am bm]
    have corr:=signed_count pairs (fun z=>read (msg z.1) z.2) (fun z=>out z.1 z.2)
    change 4^r*I.natAbs ≤ 3^r*K.length*K.length at hh
    have productCard : f.card*f.card=pairs.card := (Finset.card_product f f).symm
    rw [hEq,corr,show K.length=f.card from Finset.length_toList _,Nat.mul_assoc,productCard] at hh
    exact rat_convert pairs.card goodPairs.card r hN (by
      simpa only [goodPairs,canonFilter] using hh)
  have final :
      (∀ r:Nat,3*r+c+gCost ≤ 3*m → (4:ℚ)^r*|2*p-1| ≤ (3:ℚ)^r) ∧
      ((3:ℚ)/4 ≤ p → 3*m ≤ c+gCost+8) :=
    ⟨rules,threshold m (c+gCost) p (fun r b=>rules r (by omega))⟩
  have p_eq : p = p' := by
    dsimp only [p,goodPairs,p',agree']
    apply ratio_transport pairs_eq
    intro z
    change (read (msg z.1) z.2=out z.1 z.2) ↔
      (read (send' z.1) z.2=truth' z.1 z.2)
    rfl
  have cost_eq : gCost = cost' C := rfl
  rw [←p_eq,←cost_eq]
  exact final

end PEqualNP.Outside.L_meta_32018_aux

theorem PEqualNP.Outside.L_meta_32018 : (∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
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
  ∀ (m : Nat) (starts : Fin m → Nat),
  0 < m → Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val) % k) →
  let good := fun (row ref : Fin (2^k)) (p : Nat) =>
    let old := fun (j : Nat) => bit row.val 0 ref.val (p+j)
    let first := fun (j : Nat) => bit row.val 1 ref.val (p+j)
    let τ := xor (xor (old 6) (old 7)) (old 8)
    let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injected 1 ref.val (p+6))
    let β := xor τ (injected 1 ref.val (p+7))
    τ = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
      xor (first 4) (first 5) = !α ∧ first 4 = β
  ∀ (row ref : Fin (2^k)), (∀ i, good row ref (starts i)) →
  ∀ pin : Finset (Fin k),
  (∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i+j.val) % k) →
  (∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val) % k) →
  let K := Fin (2^k)
  let fiber := (Finset.univ : Finset K).filter (fun key =>
    ∀ z ∈ pin, bit row.val 0 key.val z.val = bit row.val 0 ref.val z.val)
  let pairs := fiber.product fiber
  let truth := fun (left right : K) =>
    let key := (left.val ^^^ right.val ^^^ ref.val) % 2^k
    (∑ i : Fin m, (bit row.val 2 key (starts i+5)).toNat) % 2 == 1
  let agree := fun (guess : K → K → Bool) =>
    (((pairs.filter (fun z => guess z.1 z.2 = truth z.1 z.2)).card : ℚ) / (pairs.card : ℚ))
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (C : Circ) =>
    (∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < k+i.val) ∧
    (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
      (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  ∀ (C : Circ), legal C → ∀ (c : Nat) (tap : Fin c → Nat),
    (∀ j, tap j < k+C.gates.length) →
    let send := fun (x : K) (j : Fin c) =>
      let raw := List.ofFn (fun i : Fin k => x.val.testBit i.val)
      (C.wires raw).getD (tap j) false
    ∀ read : (Fin c → Bool) → K → Bool,
      let p := agree (fun x y => read (send x) y)
      (∀ r : Nat, 3*r+c+cost C ≤ 3*m →
        (4 : ℚ)^r * |2*p-1| ≤ (3 : ℚ)^r) ∧
      ((3 : ℚ)/4 ≤ p → 3*m ≤ c+cost C+8)) := PEqualNP.Outside.L_meta_32018_aux.provedExact
