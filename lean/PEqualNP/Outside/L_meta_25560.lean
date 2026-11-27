import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25560_aux.Inverse
def outsideBits (ps : List Nat) (x y : Nat) : Prop :=
  ∀ j, j ∉ ps → x.testBit j = y.testBit j
def visitBit (pivot : Nat → Nat) (guard : Nat → Nat → Bool) (x t : Nat) :=
  if guard t x then x ^^^ (1 <<< pivot t) else x
def guardOrder (p : Nat → Nat) (g : Nat → Nat → Bool) : List Nat → Prop
  | [] => True
  | t::ts => (∀ x y, outsideBits ((t::ts).map p) x y →
      xor (g t x) (g t y) = xor (x.testBit (p t)) (y.testBit (p t))) ∧ guardOrder p g ts
lemma visitOther (p : Nat → Nat) (g : Nat → Nat → Bool) (x t j : Nat) (ne : j ≠ p t) :
    (visitBit p g x t).testBit j = x.testBit j := by
  cases h : g t x <;> simp [visitBit,h,Nat.testBit_xor,Nat.shiftLeft_eq,Nat.testBit_two_pow,ne,Ne.symm ne]
lemma visitOwn (p : Nat → Nat) (g : Nat → Nat → Bool) (x t : Nat) :
    (visitBit p g x t).testBit (p t) = xor (x.testBit (p t)) (g t x) := by
  cases h : g t x <;> simp [visitBit,h,Nat.testBit_xor,Nat.shiftLeft_eq,Nat.testBit_two_pow]
theorem foldGuardIff (p : Nat → Nat) (g : Nat → Nat → Bool) (ts : List Nat)
    (hn : (ts.map p).Nodup) (ho : guardOrder p g ts) (x y : Nat) :
    ts.foldl (visitBit p g) x = y ↔ outsideBits (ts.map p) x y ∧ ∀ t∈ts, g t y=false := by
  induction ts generalizing x with
  | nil =>
    simp only [List.foldl_nil,List.map_nil,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true]
    constructor
    · rintro rfl; exact fun _ _ => rfl
    · intro h;exact Nat.eq_of_testBit_eq fun j => h j (by simp)
  | cons t ts ih =>
    obtain ⟨fresh,rest⟩ := List.nodup_cons.mp hn
    obtain ⟨eqg,after⟩ := ho
    rw [List.foldl_cons,ih rest after]
    constructor
    · rintro ⟨outside,valid⟩
      have free : outsideBits ((t::ts).map p) x y := by
        intro j hj
        have ne : j≠p t := by intro eq;apply hj;simp [eq]
        have mem : j∉ts.map p := by intro hm;apply hj;exact List.mem_cons_of_mem _ hm
        exact (visitOther p g x t j ne).symm.trans (outside j mem)
      have key := outside (p t) fresh
      rw [visitOwn] at key
      have relation := eqg x y free
      have zero : g t y=false := by
        revert key relation
        cases x.testBit (p t) <;> cases y.testBit (p t) <;> cases g t x <;> cases g t y <;> decide
      exact ⟨free,by intro a ha;rcases List.mem_cons.mp ha with eq|mem;exact eq.symm ▸ zero;exact valid _ mem⟩
    · rintro ⟨free,valid⟩
      have zero := valid t List.mem_cons_self
      have relation := eqg x y free
      have key : xor (x.testBit (p t)) (g t x) = y.testBit (p t) := by
        rw [zero] at relation
        revert relation
        cases x.testBit (p t) <;> cases y.testBit (p t) <;> cases g t x <;> decide
      refine ⟨?_,fun a mem => valid a (List.mem_cons_of_mem _ mem)⟩
      intro j hj
      by_cases eq : j=p t
      · subst j;exact (visitOwn p g x t).trans key
      · exact (visitOther p g x t j eq).trans (free j (by simp [eq,hj]))
end PEqualNP.Outside.L_meta_25560_aux.Inverse


namespace PEqualNP.Outside.L_meta_25560_aux.Inverse.Bits378
abbrev Sig := Int → Bool
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

def Agrees (x y : Sig) (lo hi : Int) : Prop := ∀ j, lo≤j → j≤hi → x j=y j

def lin (x : Sig) (i : Int) :=
  xor (xor (x i) (x (i-1))) (x (i+1))

def mix (x : Sig) (i : Int) :=
  chi (lin x i) (lin x (i+1)) (lin x (i+2))

def first (x u c1 : Sig) (j : Int) :=
  xor (xor (mix x j) (xor (x (j+1)) (u (j+1)))) (c1 j)

def output (x u c1 c2 : Sig) (i : Int) :=
  xor (xor (mix (first x u c1) i) (xor (x (i-1)) (u (i-1)))) (c2 i)

theorem xorCancelR (a b c : Bool) :
    xor (xor a c) (xor b c) = xor a b := by
  cases a <;> cases b <;> cases c <;> rfl

theorem xorCancelL (a b c : Bool) :
    xor (xor c a) (xor c b) = xor a b := by
  cases a <;> cases b <;> cases c <;> rfl

theorem linOn {x y : Sig} {i : Int} (h : Agrees x y (i-1) (i+1)) :
    lin x i = lin y i := by
  unfold lin
  rw [h i (by omega) (by omega), h (i-1) (by omega) (by omega), h (i+1) (by omega) (by omega)]

theorem mixOn {x y : Sig} {i : Int} (h : Agrees x y (i-1) (i+3)) :
    mix x i = mix y i := by
  have l (j : Int) (a : i ≤ j) (b : j ≤ i+2) : lin x j = lin y j :=
    linOn (fun t ht th => h t (by omega) (by omega))
  unfold mix
  rw [l i (by omega) (by omega), l (i+1) (by omega) (by omega), l (i+2) (by omega) (by omega)]

theorem mixDiff {x y : Sig} {i : Int} (h : Agrees x y i (i+3)) :
    xor (mix x i) (mix y i) = xor (x (i-1)) (y (i-1)) := by
  have l (j : Int) (a : i < j) (b : j ≤ i+2) : lin x j = lin y j :=
    linOn (fun t ht th => h t (by omega) (by omega))
  unfold mix chi
  rw [l (i+1) (by omega) (by omega), l (i+2) (by omega) (by omega),xorCancelR]
  unfold lin
  rw [h i (by omega) (by omega),h (i+1) (by omega) (by omega),xorCancelR,xorCancelL]

theorem firstOn {x y : Sig} (u c1 : Sig) {i : Int} (h : Agrees x y (i-1) (i+3)) :
    first x u c1 i = first y u c1 i := by
  unfold first
  rw [mixOn h,h (i+1) (by omega) (by omega)]

theorem firstDiff {x y : Sig} (u c1 : Sig) {i : Int} (h : Agrees x y i (i+3)) :
    xor (first x u c1 i) (first y u c1 i) = xor (x (i-1)) (y (i-1)) := by
  unfold first
  rw [h (i+1) (by omega) (by omega),xorCancelR,xorCancelR,mixDiff h]

theorem outputDiff {x y : Sig} (u c1 c2 : Sig) {i : Int} (h : Agrees x y (i-1) (i+6)) :
    xor (output x u c1 c2 i) (output y u c1 c2 i) = xor (x (i-2)) (y (i-2)) := by
  have hf : Agrees (first x u c1) (first y u c1) i (i+3) := by
    intro j a b
    apply firstOn
    intro t ht th
    exact h t (by omega) (by omega)
  have hj : Agrees x y (i-1) ((i-1)+3) := fun t ht th => h t ht (by omega)
  unfold output
  rw [h (i-1) (by omega) (by omega),xorCancelR,xorCancelR,mixDiff hf,firstDiff u c1 hj,
      show i-1-1 = i-2 by omega]


def initWord (k u w:Nat) := rot k 1 w ^^^ u
def rawLin1 (k x:Nat) := x ^^^ rot k 1 x ^^^ rot k (k-1) x
def roundWord (k w j cx x:Nat) := rawStep k (rawLin1 k x) ^^^ rot k (2*j) w ^^^ cx

lemma linBits {k x:Nat} (hk:2≤k) (hx:x<2^k) :
 bits k (rawLin1 k x) = lin (bits k x) := by
 funext j
 simp only [rawLin1,lin,bitsXor,bitsRot (show 1<k by omega) hx,bitsRot (show k-1<k by omega) hx]
 rw [show j-((k-1:Nat):Int)=(j+1)-(k:Int) by omega]
 simp [bits,idx]

lemma roundBound {k cx:Nat} (w j x:Nat) (hc:cx<2^k) : roundWord k w j cx x < 2^k :=
 Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepBound ..) (Nat.mod_lt _ (by positivity))) hc

end PEqualNP.Outside.L_meta_25560_aux.Inverse.Bits378

namespace PEqualNP.Outside.L_meta_25560_aux.Inverse.Bits378
def leftSpan (t : Nat) : Nat := max t (2*t-3)

def stages (x u : Sig) (cs : Nat → Sig) : Nat → Sig
  | 0 => x
  | t+1 => fun i =>
    let j := i+1-2*(t:Int)
    xor (xor (mix (stages x u cs t) i) (xor (x j) (u j))) (cs (t+1) i)

private theorem stageAgree {t : ℕ} {x y : Sig} (u : Sig) (cs : ℕ → Sig) (i : Int)
    (h : Agrees x y (i-(leftSpan t:Int)) (i+3*(t:Int))) :
    stages x u cs t i = stages y u cs t i := by
  induction t generalizing i with
  | zero => exact h i (by simp [leftSpan]) (by simp)
  | succ t ih =>
    have cover : (leftSpan t:Int)+1 ≤ (leftSpan (t+1):Int) := by
      dsimp [leftSpan]
      omega
    have lo : i-(leftSpan (t+1):Int) ≤ i+1-2*(t:Int) := by
      dsimp [leftSpan]
      omega
    have eqmix : mix (stages x u cs t) i = mix (stages y u cs t) i := by
      apply mixOn
      intro j h1 h2
      apply ih
      intro z hz zh
      exact h z (by omega) (by omega)
    simp only [stages,eqmix,h (i+1-2*(t:Int)) lo (by omega)]

theorem stageDiff {r : Nat} (hr : 1 ≤ r) (three : r ≠ 3) {x y : Sig}
    (u : Sig) (cs : Nat → Sig) (i : Int)
    (h : Agrees x y (i-(leftSpan r:Int)+1) (i+3*(r:Int))) :
    xor (stages x u cs r i) (stages y u cs r i) =
      xor (x (i-(leftSpan r:Int))) (y (i-(leftSpan r:Int))) := by
  by_cases r1 : r=1
  · subst r
    have hs (z : Sig) : stages z u cs 1 = first z u (cs 1) := by
      funext l; simp [stages,first]
    rw [hs,hs]
    have result := firstDiff u (cs 1) (i:=i) (x:=x) (y:=y)
    change xor (first x u (cs 1) i) (first y u (cs 1) i) = xor (x (i-1)) (y (i-1))
    apply result
    intro j jl jh
    exact h j (by norm_num [leftSpan]; omega) (by norm_num; omega)
  by_cases r2 : r=2
  · subst r
    have hs (z : Sig) : stages z u cs 2 = output z u (cs 1) (cs 2) := by
      have one : stages z u cs 1 = first z u (cs 1) := by funext j; simp [stages,first]
      funext l
      change xor (xor (mix (stages z u cs 1) l)
          (xor (z (l+1-2*(1:Int))) (u (l+1-2*(1:Int))))) (cs 2 l) = _
      rw [one,show l+1-2*(1:Int)=l-1 by omega]
      rfl
    rw [hs,hs]
    change xor (output x u (cs 1) (cs 2) i) (output y u (cs 1) (cs 2) i) =
      xor (x (i-2)) (y (i-2))
    apply outputDiff u (cs 1) (cs 2)
    intro j jl jh
    exact h j (by norm_num [leftSpan]; omega) (by norm_num; omega)
  cases r with
  | zero => omega
  | succ t =>
    have large : 3≤t := by omega
    have flank : (leftSpan (t+1) : Int) = 2*(t:Int)-1 := by dsimp [leftSpan]; omega
    have old : (leftSpan t : Int) = 2*(t:Int)-3 := by dsimp [leftSpan]; omega
    have mixEq : mix (stages x u cs t) i = mix (stages y u cs t) i := by
      apply mixOn
      intro j jl jh
      apply stageAgree
      intro z zl zh
      exact h z (by omega) (by omega)
    have pi : i+1-2*(t:Int) = i-(leftSpan (t+1):Int) := by omega
    simp only [stages,mixEq,pi,xorCancelR,xorCancelL]

end PEqualNP.Outside.L_meta_25560_aux.Inverse.Bits378

namespace PEqualNP.Outside.L_meta_25560_aux.Inverse.Bits378
def stateWord (k u w : Nat) (c : Nat → Fin (2^k)) (t : Nat) :=
  (List.range t).foldl (fun prev j => roundWord k w j (c (j+1)).val prev) (initWord k u w)

theorem stateSucc (k u w : Nat) (c : Nat → Fin (2^k)) (t : Nat) :
    stateWord k u w c (t+1) = roundWord k w t (c (t+1)).val (stateWord k u w c t) := by
  simp [stateWord,List.range_succ]

theorem stateBound (k u w : Nat) (c : Nat → Fin (2^k)) (hu:u<2^k) (t : Nat) :
    stateWord k u w c t < 2^k := by
  cases t with
  | zero => exact Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) hu
  | succ t => rw [stateSucc]; exact roundBound _ _ _ (c _).isLt

theorem injBits {k w : Nat} (u t : Nat) (hk : 1 < k) (hw:w<2^k) (j : Int) :
    bits k w (j - ((2*t:Nat):Int)) =
      xor (bits k (initWord k u w) (j+1-2*(t:Int))) (bits k u (j+1-2*(t:Int))) := by
  rw [initWord,bitsXor,bitsRot hk hw]
  rw [show j+1-2*(t:Int)-(1:Nat)=j-((2*t:Nat):Int) by omega]
  cases bits k w (j-((2*t:Nat):Int)) <;> cases bits k u (j+1-2*(t:Int)) <;> rfl

theorem stateBits {k w u : Nat} (c : Nat → Fin (2^k)) (hk:2≤k) (hw:w<2^k) (hu:u<2^k)
    (t : Nat) (ht:2*t<k) :
    bits k (stateWord k u w c t) =
      stages (bits k (initWord k u w)) (bits k u) (fun j => bits k (c j).val) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext j
    rw [stateSucc]
    simp only [roundWord,bitsXor,bitsStep (show 0<k by omega),
      linBits hk (stateBound k u w c hu t),bitsRot (show 2*t<k by omega) hw,
      ih (by omega),stages,mix]
    rw [injBits u t (by omega) hw]

end PEqualNP.Outside.L_meta_25560_aux.Inverse.Bits378

namespace PEqualNP.Outside.L_meta_25560_aux.Inverse
open PEqualNP.Outside.L_meta_25560_aux.Inverse.Bits378

def startRounds32 (k u : Nat) (c : Nat → Fin (2^k)) (t x : Nat) :=
  let w := rot k (k-1) (x ^^^ u)
  (List.range t).foldl (fun prev j => roundWord k w j (c (j+1)).val prev) x

def guard32 (k u : Nat) (c : Nat → Fin (2^k)) (t b x : Nat) : Bool :=
  let z := startRounds32 k u c (t-1) x
  xor (xor (z.testBit (b % k)) (z.testBit ((b+1)%k))) (z.testBit ((b+2)%k))

private lemma natIdx32 (k i : Nat) : idx k (i:Int)=i % k := by
  simp only [idx,←Int.natCast_mod,Int.toNat_natCast]

private lemma undo32 {k z : Nat} (hk : 2≤k) (hz : z<2^k) :
    rot k 1 (rot k (k-1) z) = z := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<k
  · have E : idx k (i:Int) = i := (natIdx32 k i).trans (Nat.mod_eq_of_lt hi)
    have inner : rot k (k-1) z < 2^k := Nat.mod_lt _ (Nat.two_pow_pos _)
    have H : bits k (rot k 1 (rot k (k-1) z)) i = bits k z i := by
      rw [bitsRot (show 1<k by omega) inner,
        bitsRot (show k-1<k by omega) hz]
      rw [show (i:Int)-(1:Nat)-((k-1:Nat):Int) = i-(k:Int) by omega]
      simp [bits,idx]
    simpa only [bits,E] using H
  · have power := Nat.pow_le_pow_right Nat.zero_lt_two (show k ≤ i by omega)
    have H : rot k 1 (rot k (k-1) z)<2^k := Nat.mod_lt _ (Nat.two_pow_pos _)
    rw [Nat.testBit_lt_two_pow (H.trans_le power),Nat.testBit_lt_two_pow (hz.trans_le power)]

private lemma lift32 {k u x t : Nat} (c : Nat → Fin (2^k)) (hk:2≤k)
    (hx:x<2^k) (hu:u<2^k) (ht : 2*t<k) :
    bits k (startRounds32 k u c t x) =
      stages (bits k x) (bits k u) (fun i => bits k (c i).val) t := by
  let w := rot k (k-1) (x ^^^ u)
  have iw : initWord k u w = x := by
    simp [initWord,w,undo32 hk (Nat.xor_lt_two_pow hx hu)]
  have H := stateBits (w:=w) (u:=u) c hk (Nat.mod_lt _ (Nat.two_pow_pos _)) hu t ht
  unfold stateWord at H
  rw [iw] at H
  exact H

theorem guardWindow32 {k u x y t b : Nat} (c : Nat → Fin (2^k))
    (hk:2≤k) (ht:5≤t) (wide:2*(t-1)<k) (low:2*t≤b+5)
    (hu:u<2^k) (hx:x<2^k) (hy:y<2^k)
    (same:∀ z : Nat, b+5-2*t<z → z≤b+3*t-1 → x.testBit (z % k)=y.testBit (z % k)) :
    xor (guard32 k u c t b x) (guard32 k u c t b y) =
      xor (x.testBit ((b+5-2*t)%k)) (y.testBit ((b+5-2*t)%k)) := by
  let p := b+5-2*t
  let s := t-1
  have flank : (leftSpan s:Int) = 2*(t:Int)-5 := by dsimp [s,leftSpan]; omega
  have base : (p:Int) = (b:Int)-(leftSpan s:Int) := by dsimp [p]; omega
  have bound (j : Int) (lo : (p:Int)<j) (hi : j≤(b:Int)+3*(t:Int)-1) :
      bits k x j = bits k y j := by
    have cast : (j.toNat:Int)=j := Int.toNat_of_nonneg (by omega)
    rw [←cast]
    simp only [bits,natIdx32]
    exact same _ (by change p<j.toNat; omega) (by omega)
  let X := bits k (startRounds32 k u c s x)
  let Y := bits k (startRounds32 k u c s y)
  have delta (a : Int) (ha : 0≤a) (ha' : a≤2) :
      xor (X (b+a)) (Y (b+a)) = xor (bits k x (p+a)) (bits k y (p+a)) := by
    have H := stageDiff (r:=s) (x:=bits k x) (y:=bits k y) (by dsimp [s];omega)
      (by dsimp [s];omega) (bits k u) (fun i => bits k (c i).val) ((b:Int)+a) (fun j lo hi =>
        bound j (by omega) (by dsimp [s] at hi;omega))
    dsimp only [X,Y]
    rw [lift32 c hk hx hu wide,lift32 c hk hy hu wide]
    rw [show (p:Int)+a=(b:Int)+a-(leftSpan s:Int) by omega]
    exact H
  have fixed (a : Int) (ha : 1≤a) (ha' : a≤2) : X (b+a)=Y (b+a) := by
    have H := delta a (by omega) ha'
    rw [bound (p+a) (by omega) (by omega)] at H
    simpa using H
  have H := delta 0 (by decide) (by decide)
  simp only [Int.add_zero] at H
  have represent (v : Nat) : guard32 k u c t b v =
      xor (xor (bits k (startRounds32 k u c s v) b) (bits k (startRounds32 k u c s v) ((b:Int)+1)))
        (bits k (startRounds32 k u c s v) ((b:Int)+2)) := by
    have a : (b:Int)+1=((b+1:Nat):Int) := by omega
    have b' : (b:Int)+2=((b+2:Nat):Int) := by omega
    simp only [guard32,s,a,b',bits,natIdx32]
  rw [represent,represent]
  change xor (xor (xor (X b) (X (b+1))) (X (b+2)))
      (xor (xor (Y b) (Y (b+1))) (Y (b+2))) = _
  rw [fixed 1 (by decide) (by decide),fixed 2 (by decide) (by decide),xorCancelR,xorCancelR]
  simpa only [bits,natIdx32,p] using H

end PEqualNP.Outside.L_meta_25560_aux.Inverse


namespace PEqualNP.Outside.L_meta_25560_aux.Inverse
lemma visitBound {k x t : Nat} (p : Nat → Nat) (g : Nat → Nat → Bool) (hp : p t < k)
    (hx : x < 2^k) : visitBit p g x t < 2^k := by
  unfold visitBit
  split
  · apply Nat.xor_lt_two_pow hx
    simpa [Nat.shiftLeft_eq] using (Nat.pow_lt_pow_right (by decide : 1 < 2) hp)
  · exact hx

lemma foldVisitBound {k : Nat} (p : Nat → Nat) (g : Nat → Nat → Bool) (ts : List Nat)
    (hp : ∀ t ∈ ts, p t < k) (x : Nat) (hx : x < 2^k) : ts.foldl (visitBit p g) x < 2^k := by
  induction ts generalizing x with
  | nil => exact hx
  | cons t ts ih =>
    apply ih (fun a ha => hp a (List.mem_cons_of_mem _ ha))
    exact visitBound p g (hp t List.mem_cons_self) hx

lemma foldVisitMod {k : Nat} (p : Nat → Nat) (g : Nat → Nat → Bool) (ts : List Nat)
    (hp : ∀ t ∈ ts, p t < k) (x : Nat) (hx : x < 2^k) :
    ts.foldl (visitBit p g) x = ts.foldl (visitBit p (fun t y => g t (y % 2^k))) x := by
  induction ts generalizing x with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.foldl_cons]
    have eq : visitBit p (fun u y => g u (y % 2^k)) x t = visitBit p g x t := by
      simp only [visitBit,Nat.mod_eq_of_lt hx]
    rw [eq]
    exact ih (fun a ha => hp a (List.mem_cons_of_mem _ ha)) _ (visitBound p g (hp t List.mem_cons_self) hx)


end PEqualNP.Outside.L_meta_25560_aux.Inverse

namespace PEqualNP.Outside.L_meta_25560_aux.Inverse

private lemma residueSep58 {k z j : Nat} (lt : z<j) (near : j<z+k) :
    j % k ≠ z % k := by
  intro same
  have eqn : (j-z)+z ≡ 0+z [MOD k] := by
    rw [show j-z+z=j by omega, Nat.zero_add]
    exact same
  have h := Nat.ModEq.add_right_cancel' z eqn
  change (j-z) % k=0 % k at h
  rw [Nat.mod_eq_of_lt (by omega),Nat.zero_mod] at h
  omega

theorem sweep58 {k r e i m : Nat} (row : Fin (2^k)) (c : Nat → Fin (2^k))
    (time deficit : Nat → Nat) (kp : 0<k) (er : e≤r) (kr : k+e+3=5*r)
    (bounds : ∀ j < m, 5≤time j ∧ time j≤r-e ∧ deficit j≤4*(r-time j))
    (ordered : ∀ j < m, ∀ h < m, j<h →
      time j<time h ∧ 5*time j+deficit j<5*time h+deficit h)
    (seed : Fin (2^k)) (target : Nat → Bool) :
    let P := i+3*r+k
    let J := fun j => P+5-(5*time j+deficit j)
    let p := fun j => J j % k
    let b := fun j => P-(3*time j+deficit j)
    let g := fun j x => guard32 k row.val c (time j) (b j) x
    let out := (List.range m).foldl (fun x j => if g j x=target j then x else x ^^^ (1 <<< p j)) seed.val
    let same := fun x : Nat => ∀ b<k, (∀ j < m, p j≠b) → x.testBit b = seed.val.testBit b
    out<2^k ∧ same out ∧ (∀ j < m, g j out=target j) ∧
      ∀ x : Fin (2^k), same x.val → (∀ j < m, g j x.val=target j) → x.val=out := by
  intro P J p b g out same
  let toggle := fun t x => xor (g t x) (target t)
  have hJ (t : Nat) (ht : t < m) : J t<P ∧ P<J t+k := by
    obtain ⟨lo,hi,last⟩ := bounds t ht
    dsimp [J,P]
    omega
  have decreasing {t v : Nat} (vt : v < m) (tv : t<v) : J v<J t := by
    have cap := bounds v vt
    obtain ⟨_,inc⟩ := ordered t (by omega) v vt tv
    dsimp [J,P]
    omega
  have sep {t v : Nat} (vt : v < m) (tv : t<v) : p t≠p v :=
    residueSep58 (decreasing vt tv) (by have := hJ v vt; have := hJ t (by omega); omega)
  have hn : ((List.range m).map p).Nodup := by
    apply List.Nodup.map_on _ List.nodup_range
    intro t ht v hv eqn
    rcases lt_trichotomy t v with lt|eq|gt
    · exact False.elim (sep (List.mem_range.mp hv) lt eqn)
    · exact eq
    · exact False.elim (sep (List.mem_range.mp ht) gt eqn.symm)
  have order (ls : List Nat) (sub : ∀ t∈ls,t < m) (sort : ls.Pairwise (·<·)) :
      guardOrder p (fun t y => toggle t (y % 2^k)) ls := by
    induction ls with
    | nil => trivial
    | cons t ts ih =>
      obtain ⟨before,later⟩ := List.pairwise_cons.mp sort
      have tm := sub t List.mem_cons_self
      obtain ⟨lo,hi,last⟩ := bounds t tm
      have JP : b t+5-2*time t=J t := by dsimp [b,J,P]; omega
      have maxB : b t+3*time t-1≤P := by dsimp [b,P]; omega
      refine ⟨?_,ih (fun v hv => sub v (List.mem_cons_of_mem t hv)) later⟩
      intro x y agree
      have fixed (j : Nat) (jl : b t+5-2*time t<j) (jr : j≤b t+3*time t-1) :
          x.testBit (j % k)=y.testBit (j % k) := by
        rw [JP] at jl
        apply agree
        intro hm
        obtain ⟨v,hv,eqn⟩ := List.mem_map.mp hm
        have vm := sub v hv
        have Jv : J v≤J t := by
          rcases List.mem_cons.mp hv with vt|rest
          · exact vt ▸ Nat.le_refl _
          · exact (decreasing vm (before v rest)).le
        exact residueSep58 (Jv.trans_lt jl) (by have := hJ v vm; omega) eqn.symm
      have sem := guardWindow32 (u:=row.val) (x:=x % 2^k) (y:=y % 2^k) (t:=time t) (b:=b t) c
        (by omega) lo (by omega) (by dsimp [b,P]; omega) row.isLt
        (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.mod_lt _ (Nat.two_pow_pos _)) (by
          intro j lj rj
          simpa [Nat.testBit_mod_two_pow,Nat.mod_lt _ kp] using fixed j lj rj)
      simp only [Nat.testBit_mod_two_pow,JP,decide_eq_true (Nat.mod_lt _ kp),Bool.true_and] at sem
      dsimp only [toggle,g,p]
      rw [PEqualNP.Outside.L_meta_25560_aux.Inverse.Bits378.xorCancelR]
      exact sem
  have hp : ∀ t∈List.range m, p t<k := fun t _ => Nat.mod_lt _ kp
  have H := foldGuardIff p (fun t x => toggle t (x % 2^k)) (List.range m) hn
    (order _ (fun _ h => List.mem_range.mp h) List.pairwise_lt_range) seed.val
  have app (x t : Nat) : (if g t x=target t then x else x ^^^ (1 <<< p t)) =
      visitBit p toggle x t := by
    unfold visitBit toggle
    cases g t x <;> cases target t <;> rfl
  have outEq : out = (List.range m).foldl (visitBit p toggle) seed.val := by
    simp only [out,app]
  have bound : out<2^k := outEq ▸ foldVisitBound p toggle (List.range m) hp seed.val seed.isLt
  have char (x : Nat) (hx : x<2^k) :
      out=x ↔ same x ∧ ∀ j < m,g j x=target j := by
    have f := H x
    rw [← foldVisitMod p toggle (List.range m) hp seed.val seed.isLt,←outEq] at f
    simp only [Nat.mod_eq_of_lt hx,List.mem_range] at f
    have off (b : Nat) : b∉(List.range m).map p ↔ ∀ j < m,p j≠b := by simp
    have outbits : outsideBits ((List.range m).map p) seed.val x ↔ same x := by
      constructor
      · intro h b lb vis
        exact (h b ((off b).mpr vis)).symm
      · intro h b vis
        by_cases lb : b<k
        · exact (h b lb ((off b).mp vis)).symm
        · have factor : 2^k≤2^b := Nat.pow_le_pow_of_le (by decide) (by omega)
          rw [Nat.testBit_lt_two_pow (seed.isLt.trans_le factor),Nat.testBit_lt_two_pow (hx.trans_le factor)]
    have cancel (a b : Bool) : xor a b = false ↔ a=b := by cases a <;> cases b <;> decide
    simpa only [outbits,toggle,cancel] using f
  obtain ⟨ss,ans⟩ := (char out bound).mp rfl
  exact ⟨bound,ss,ans,fun x sx gx => ((char x.val x.isLt).mpr ⟨sx,gx⟩).symm⟩

end PEqualNP.Outside.L_meta_25560_aux.Inverse

namespace PEqualNP.Outside.L_meta_25560_aux.Inverse
open Bits378

abbrev rot60 := Bits378.rot
def initial60 (k u key : ℕ) := rot60 k 1 key ^^^ u

def state60 (k u : ℕ) (c : ℕ → Fin (2^k)) (key t : ℕ) :=
  (List.range t).foldl (fun prev j => rawStep k (prev ^^^ rot60 k 1 prev ^^^ rot60 k (k-1) prev)
    ^^^ rot60 k (2*j) key ^^^ (c (j+1)).val) (initial60 k u key)

def guard60 (k r i u : ℕ) (c : ℕ → Fin (2^k)) (key t g : ℕ) :=
  let z := state60 k u c key (t-1)
  let b := (i+3*r+k-(3*t+g))%k
  xor (xor (z.testBit b) (z.testBit ((b+1)%k))) (z.testBit ((b+2)%k))

def pivot60 (k r i t g : ℕ) := (i+3*r+k+5-(5*t+g))%k

private theorem redo60 {k z : ℕ} (hk : 2 ≤ k) (hz : z  <  2^k) :
    rot60 k (k-1) (rot60 k 1 z) = z := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · have E : idx k (i:Int) = i := (natIdx32 k i).trans (Nat.mod_eq_of_lt hi)
    have inner : rot k 1 z  <  2^k := Nat.mod_lt _ (Nat.two_pow_pos _)
    have H : bits k (rot k (k-1) (rot k 1 z)) i = bits k z i := by
      rw [bitsRot (show k-1 < k by omega) inner, bitsRot (show 1 < k by omega) hz]
      rw [show (i:Int)-((k-1:Nat):Int)-(1:Nat) = i-(k:Int) by omega]
      simp [bits,idx]
    simpa only [bits,E] using H
  · have power := Nat.pow_le_pow_right Nat.zero_lt_two (show k ≤ i by omega)
    have H : rot60 k (k-1) (rot60 k 1 z)  <  2^k := Nat.mod_lt _ (Nat.two_pow_pos _)
    rw [Nat.testBit_lt_two_pow (H.trans_le power),Nat.testBit_lt_two_pow (hz.trans_le power)]

def keyInitial60 {k u : ℕ} (hk : 2 ≤ k) (hu : u  <  2^k) : Fin (2^k) ≃ Fin (2^k) where
  toFun key := ⟨initial60 k u key.val, Nat.xor_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _)) hu⟩
  invFun x := ⟨rot60 k (k-1) (x.val ^^^ u), Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  left_inv key := by apply Fin.ext; change rot60 k (k-1) ((rot60 k 1 key.val ^^^ u) ^^^ u) = _; simp [redo60 hk key.isLt]
  right_inv x := by
    apply Fin.ext
    change (rot k 1 (rot k (k-1) (x.val ^^^ u)) ^^^ u)=x.val
    rw [undo32 hk (Nat.xor_lt_two_pow x.isLt hu)]; simp

private theorem guard_raw {k u : ℕ} (hk : 2 ≤ k) (c : ℕ → Fin (2^k)) (key : Fin (2^k)) (r i t g : ℕ) :
    guard32 k u c t (i+3*r+k-(3*t+g)) (initial60 k u key.val) = guard60 k r i u c key.val t g := by
  unfold guard32 guard60
  have ez : startRounds32 k u c (t-1) (initial60 k u key.val) = state60 k u c key.val (t-1) := by
    unfold startRounds32 state60 initial60
    simp [redo60 hk key.isLt,rot60,rawLin1,roundWord] 
  rw [ez]
  simp only [Nat.mod_add_mod]

theorem trace_inverse {k r e i m u : ℕ} (c : ℕ → Fin (2^k)) (hk : 2 ≤ k) (hu : u < 2^k)
    (her : e ≤ r) (hkr : k+e+3=5*r) (time deficit : ℕ → ℕ)
    (bounds : ∀ j < m, 5≤time j ∧ time j≤r-e ∧ deficit j≤4*(r-time j))
    (ordered : ∀ j < m, ∀ h < m, j < h → time j < time h ∧ 5*time j+deficit j < 5*time h+deficit h)
    (target : ℕ → Bool) (seed : Fin (2^k)) :
    let p j := pivot60 k r i (time j) (deficit j)
    ((List.range m).map p).Nodup ∧ ∃! key : Fin (2^k),
      (∀ b < k, (∀ j < m, p j ≠ b) → (initial60 k u key.val).testBit b = seed.val.testBit b) ∧
      (∀ j < m, guard60 k r i u c key.val (time j) (deficit j) = target j) := by
  intro p
  let J := fun j => i+3*r+k+5-(5*time j+deficit j)
  have hJ j (hj : j < m) : J j < i+3*r+k ∧ i+3*r+k < J j+k := by
    obtain ⟨_,_,_⟩ := bounds j hj
    dsimp [J]; omega
  have sep {j h : ℕ} (hh : h < m) (jh : j < h) : p j ≠ p h := by
    have hj := hJ j (by omega); have hb := hJ h hh
    have ho := (ordered j (by omega) h hh jh).2
    have cap := bounds h hh
    exact residueSep58 (show J h < J j by dsimp [J]; omega) (show J j < J h + k by omega)
  constructor
  · apply List.Nodup.map_on _ List.nodup_range
    intro a ha b hb h
    rcases lt_trichotomy a b with lt | eq | gt
    · exact False.elim (sep (List.mem_range.mp hb) lt h)
    · exact eq
    · exact False.elim (sep (List.mem_range.mp ha) gt h.symm)
  · let eqv := keyInitial60 hk hu
    have H := sweep58 (i:=i) (⟨u,hu⟩ : Fin (2^k)) c time deficit (by omega) her hkr bounds ordered seed target
    dsimp only at H
    obtain ⟨hout,houtside,hbits,huniq⟩ := H
    let out : Fin (2^k) := ⟨_,hout⟩
    have ib (x : Fin (2^k)) : initial60 k u (eqv.symm x).val = x.val := congrArg Fin.val (eqv.apply_symm_apply x)
    refine ⟨eqv.symm out, ⟨?_,?_⟩, ?_⟩
    · rw [ib]; exact houtside
    · intro j hj
      rw [←guard_raw hk c,ib]
      exact hbits j hj
    · intro key h
      apply eqv.injective
      rw [Equiv.apply_symm_apply]
      exact Fin.ext (huniq (eqv key) h.1 (fun j hj => (guard_raw hk c key r i (time j) (deficit j)).trans (h.2 j hj)))

end PEqualNP.Outside.L_meta_25560_aux.Inverse

namespace PEqualNP.Outside.L_meta_25560_aux

def O60 (b : Nat→Bool) (n : Nat) := ((Finset.range n).filter (fun j=>b j=true)).card
def Z60 (b : Nat→Bool) (n : Nat) := ((Finset.range n).filter (fun j=>b j=false)).card

theorem Osucc60 (b : Nat→Bool) (n : Nat) : O60 b (n+1)=O60 b n+(b n).toNat := by
  cases h : b n  <;> simp [O60,Finset.range_add_one,Finset.filter_insert,h]

theorem Zsucc60 (b : Nat→Bool) (n : Nat) : Z60 b (n+1)=Z60 b n+(!b n).toNat := by
  cases h : b n  <;> simp [Z60,Finset.range_add_one,Finset.filter_insert,h]

theorem OZ60 (b : Nat→Bool) (n : Nat) : O60 b n+Z60 b n=n := by
  induction n with
  | zero => simp [O60,Z60]
  | succ n ih =>
    rw [Osucc60,Zsucc60]; cases b n  <;> simp_all  <;> omega

theorem Omono60 (b : Nat→Bool) : Monotone (O60 b) := by
  intro a c h; exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h))

theorem Zmono60 (b : Nat→Bool) : Monotone (Z60 b) := by
  intro a c h; exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h))

theorem leastStop60 (b : Nat→Bool) {N D m : Nat} (hs : N=m+D) (ht : O60 b N≤D) :
    ∃ L≤N, Z60 b L=m ∧ ∀j < L,Z60 b j < m := by
  have hex : ∃j, m≤Z60 b j := ⟨N,by have := OZ60 b N; omega⟩
  let L := Nat.find hex
  have found : m≤Z60 b L := Nat.find_spec hex
  have before (j : Nat) (hj : j < L) : Z60 b j < m := Nat.lt_of_not_ge (Nat.find_min hex hj)
  refine ⟨L,Nat.find_min' _ (by have := OZ60 b N; omega),?_,before⟩
  cases he : L with
  | zero => simp [he,Z60] at found ⊢; omega
  | succ n =>
    have := before n (by omega)
    have hs := Zsucc60 b n
    rw [he] at found
    have bone : (!b n).toNat≤1 := by cases b n <;> decide
    omega

def time60 (cut j : Nat) := cut+j+1
def deficit60 (D : Nat) (b : Nat→Bool) (j : Nat) := D-O60 b j
def pivot60 (k r i t g : Nat) := (i+3*r+k+5-(5*t+g))%k
def trace60 (k r i cut D : Nat) (b : Nat→Bool) (l : Nat) :=
  (List.range l).map (fun j=>(pivot60 k r i (time60 cut j) (deficit60 D b j), b j))
def even60 (tr : List (Nat×Bool)) := (tr.filter (fun item=>!item.2)).length

theorem traceSnoc60 (k r i cut D : Nat) (b : Nat→Bool) (l : Nat) :
    trace60 k r i cut D b (l+1)=trace60 k r i cut D b l ++
      [(pivot60 k r i (time60 cut l) (deficit60 D b l),b l)] := by simp [trace60,List.range_succ]
@[simp] theorem traceLength60 (k r i cut D : Nat) (b : Nat→Bool) (l : Nat) :
    (trace60 k r i cut D b l).length=l := by simp [trace60]
theorem traceEven60 (k r i cut D : Nat) (b : Nat→Bool) (l : Nat) :
    even60 (trace60 k r i cut D b l)=Z60 b l := by
  induction l with
  | zero => simp [even60,trace60,Z60]
  | succ l ih =>
    rw [traceSnoc60,Zsucc60]
    unfold even60 at ih ⊢
    cases b l  <;> simp [ih]
theorem traceSnd60 (k r i cut D : Nat) (b : Nat→Bool) (l : Nat) :
    (trace60 k r i cut D b l).map Prod.snd = (List.range l).map b := by simp [trace60, List.map_map,Function.comp_def]

theorem bounds60 {r e q : Nat} (hp : 0 < q) (hr : 3*e+2*q+3≤r)
    (b : Nat→Bool) {L : Nat}
    (hL : L≤r-e-(e+q+3)) (hz : ∀j < L, Z60 b j < (r-e-(e+q+3))-(e+q-1))
    (j : Nat) (hj : j < L) :
    5≤time60 (e+q+3) j ∧ time60 (e+q+3) j≤r-e ∧
    deficit60 (e+q-1) b j ≤ 4*(r-time60 (e+q+3) j) := by
  have := OZ60 b j; have := hz j hj
  unfold time60 deficit60
  omega

theorem ordered60 (cut D : Nat) (b : Nat→Bool) {j h : Nat} (hj : j < h) :
    time60 cut j < time60 cut h ∧
    5*time60 cut j+deficit60 D b j < 5*time60 cut h+deficit60 D b h := by
  have := OZ60 b j;have := OZ60 b h;have := Zmono60 b hj.le
  unfold time60 deficit60;omega

def next60 (k r i cut D m : Nat) (guard : Nat→Nat→Bool)
    (cfg : Bool × List (Nat×Bool)) (ix : Nat) : Bool × List (Nat×Bool) :=
  let tr := cfg.2
  let zeros := even60 tr
  let ones := tr.length-zeros
  if cfg.1 || decide (m≤zeros ∨ D < ones) then cfg
  else
    let t := time60 cut ix
    let g := D-ones
    if 4*(r-t) < g then (true,tr) else (false,tr++[(pivot60 k r i t g,guard t g)])
def run60 (k r i cut D m : Nat) (guard : Nat→Nat→Bool) (n : Nat) :=
  (List.range n).foldl (next60 k r i cut D m guard) (false,[])

theorem runSucc60 (k r i cut D m : Nat) (guard : Nat→Nat→Bool) (n : Nat) :
    run60 k r i cut D m guard (n+1)=next60 k r i cut D m guard (run60 k r i cut D m guard n) n := by
  simp [run60,List.range_succ]

theorem next_trace60 (k r i cut D m j : Nat) (guard : Nat→Nat→Bool) (b : Nat→Bool)
    (hz : Z60 b j < m) (ho : O60 b j≤D) (hfit : deficit60 D b j≤4*(r-time60 cut j))
    (hg : guard (time60 cut j) (deficit60 D b j)=b j) :
    next60 k r i cut D m guard (false,trace60 k r i cut D b j) j =
      (false,trace60 k r i cut D b (j+1)) := by
  have cnt : j-Z60 b j=O60 b j := by have := OZ60 b j; omega
  simp only [next60,traceEven60,traceLength60,cnt,Bool.false_or,decide_eq_true_eq]
  rw [if_neg (by omega),if_neg (by exact Nat.not_lt.mpr hfit),traceSnoc60]
  simpa only [deficit60] using congrArg (fun x=>(false,trace60 k r i cut D b j++
      [(pivot60 k r i (time60 cut j) (deficit60 D b j),x)])) hg

theorem scanPath60 (k r i cut D m : Nat) (guard : Nat→Nat→Bool) (b : Nat→Bool) {L N : Nat}
    (hL : L≤N) (hz : Z60 b L=m) (hpre : ∀ j < L,Z60 b j < m)
    (hO : ∀ j < L,O60 b j≤D) (hfit : ∀ j < L,deficit60 D b j≤4*(r-time60 cut j))
    (hg : ∀ j < L,guard (time60 cut j) (deficit60 D b j)=b j) :
    run60 k r i cut D m guard N=(false,trace60 k r i cut D b L) := by
  have prefAux (j : Nat) (hj : j≤L) : run60 k r i cut D m guard j=(false,trace60 k r i cut D b j) := by
    induction j with
    | zero => rfl
    | succ j ih => rw [runSucc60,ih (by omega)]; exact next_trace60 _ _ _ _ _ _ _ _ _ (hpre j (by omega)) (hO j (by omega)) (hfit j (by omega)) (hg j (by omega))
  induction N,hL using Nat.le_induction with
  | base => exact prefAux L (by omega)
  | succ j hj ih => rw [runSucc60,ih]; simp [next60,traceEven60,hz]


private def oracleO60 (cut D : Nat) (guard : Nat→Nat→Bool) : Nat→Nat
  | 0=>0
  | j+1=>oracleO60 cut D guard j+(guard (time60 cut j) (D-oracleO60 cut D guard j)).toNat
private def oracleB60 (cut D : Nat) (guard : Nat→Nat→Bool) (j : Nat) :=
  guard (time60 cut j) (D-oracleO60 cut D guard j)

private theorem oracleCorrect60 (cut D : Nat) (guard : Nat→Nat→Bool) (j : Nat) :
    guard (time60 cut j) (deficit60 D (oracleB60 cut D guard) j)=oracleB60 cut D guard j := by
  have counts (n : Nat) : O60 (oracleB60 cut D guard) n=oracleO60 cut D guard n := by
    induction n with
    | zero => simp [O60,oracleO60]
    | succ n ih => rw [Osucc60,ih];rfl
  simp only [deficit60,counts,oracleB60]

theorem acceptedHistory60 (k r i cut D m : Nat) (guard : Nat→Nat→Bool) (N : Nat)
    (hbad : (run60 k r i cut D m guard N).1=false)
    (haccept : even60 (run60 k r i cut D m guard N).2=m) :
    ∃ (b : Nat→Bool) (L : Nat), L≤N ∧ run60 k r i cut D m guard N=(false,trace60 k r i cut D b L) ∧
      Z60 b L=m ∧ (∀ j < L,Z60 b j < m) ∧ (∀ j < L,O60 b j≤D) ∧
      (∀ j < L,deficit60 D b j≤4*(r-time60 cut j)) ∧
      (∀ j < L,guard (time60 cut j) (deficit60 D b j)=b j) := by
  let b := oracleB60 cut D guard
  let tr := trace60 k r i cut D b
  let good := fun j => Z60 b j < m ∧ O60 b j≤D ∧ deficit60 D b j≤4*(r-time60 cut j)
  have bh (j : Nat) : guard (time60 cut j) (deficit60 D b j)=b j := oracleCorrect60 .. 
  have hist (n : Nat) : ∃ (l : Nat) (bad : Bool), l≤n ∧
      run60 k r i cut D m guard n=(bad,tr l) ∧ (∀ j < l,good j) ∧
      (l=n ∨ bad=true ∨ m≤Z60 b l ∨ D < O60 b l) := by
    induction n with
    | zero => exact ⟨0,false,by omega,rfl,fun j h=>by omega,Or.inl rfl⟩
    | succ n ih =>
      obtain ⟨l,bad,hl,he,hpre,hstatus⟩ := ih
      rw [runSucc60,he]
      have cnt : l-Z60 b l=O60 b l := by have := OZ60 b l;omega
      by_cases stop : bad=true ∨ m≤Z60 b l ∨ D < O60 b l
      · refine ⟨l,bad,by omega,?_,hpre,Or.inr stop⟩
        change next60 _ _ _ _ _ _ _ (bad,trace60 k r i cut D b l) n=_
        simp only [next60,traceEven60,traceLength60,cnt]
        rcases stop with e|e|e <;> simp [e,tr]
      · have el : l=n := hstatus.resolve_right stop
        subst l
        obtain rfl : bad=false := by cases bad <;> simp_all
        have hz : Z60 b n < m := by omega
        have ho : O60 b n ≤D := by omega
        by_cases fit : deficit60 D b n≤4*(r-time60 cut n)
        · refine ⟨n+1,false,by omega,next_trace60 k r i cut D m n guard b hz ho fit (bh n),?_,Or.inl rfl⟩
          intro j hj; rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with lt|rfl
          · exact hpre j lt
          · exact ⟨hz,ho,fit⟩
        · refine ⟨n,true,by omega,?_,hpre,Or.inr (Or.inl rfl)⟩
          change next60 _ _ _ _ _ _ _ (false,trace60 k r i cut D b n) n=_
          simp only [next60,traceEven60,traceLength60,cnt,Bool.false_or,decide_eq_true_eq]
          rw [if_neg (by omega),if_pos (by exact Nat.lt_of_not_ge fit)]
  obtain ⟨L,bad,hle,he,hpre,_⟩ := hist N
  rw [he] at hbad haccept
  dsimp only at hbad haccept
  subst bad
  exact ⟨b,L,hle,he,(traceEven60 ..).symm.trans haccept,
    fun j hj=>(hpre j hj).1,fun j hj=>(hpre j hj).2.1,
    fun j hj=>(hpre j hj).2.2,fun j _=>bh j⟩

end PEqualNP.Outside.L_meta_25560_aux

namespace PEqualNP.Outside.L_meta_25560_aux.Packing

def pack (l : List Bool) : ℕ := l.foldr (fun b a => b.toNat + 2*a) 0
def unpack (k a : ℕ) : List Bool := (List.range k).map a.testBit
def free (k : ℕ) (pv : List ℕ) : List ℕ := (List.range k).filter (fun i => decide (i∉pv))
def rest (k : ℕ) (pv : List ℕ) (x : ℕ) := (free k pv).map x.testBit
def encoded (k : ℕ) (tr : List (ℕ × Bool)) (x : ℕ) := pack (tr.map Prod.snd ++ rest k (tr.map Prod.fst) x)

theorem pack_lt (l : List Bool) : pack l < 2^l.length := by
  induction l with
  | nil => decide
  | cons a t ih =>
    change a.toNat+2*pack t < 2^(t.length+1)
    rw [pow_succ]; cases a <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> omega

theorem pack_bit {l : List Bool} {i} (hi : i<l.length) : (pack l).testBit i=l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    have e : pack (a::t)=Nat.bit a (pack t) := by rw [Nat.bit_val]; exact Nat.add_comm ..
    cases i with
    | zero => rw [e,Nat.testBit_bit_zero]; rfl
    | succ j => rw [e,Nat.testBit_bit_succ]; exact ih (by simpa using hi)

@[simp] theorem unpack_length (k a : ℕ) : (unpack k a).length=k := by simp [unpack]

theorem unpack_pack (l : List Bool) : unpack l.length (pack l)=l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [unpack,List.getElem_map,List.getElem_range,pack_bit h2]

theorem pack_unpack {k a : ℕ} (ha : a<2^k) : pack (unpack k a)=a := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases h : i<k
  · rw [pack_bit (by simpa : i<(unpack k a).length)]
    simp [unpack]
  · have e : 2^k≤2^i := Nat.pow_le_pow_right (by decide) (by omega)
    have hle : pack (unpack k a)<2^k := by simpa using pack_lt (unpack k a)
    rw [Nat.testBit_eq_false_of_lt (hle.trans_le e),Nat.testBit_eq_false_of_lt (ha.trans_le e)]

theorem free_mem {k b : ℕ} {pv : List ℕ} : b ∈ free k pv ↔ b<k ∧ b∉pv := by simp [free]

theorem free_nodup (k : ℕ) (pv : List ℕ) : (free k pv).Nodup :=
  List.Nodup.filter _ List.nodup_range

theorem free_length {k : ℕ} {pv : List ℕ} (hd : pv.Nodup) (hb : ∀ b∈pv,b<k) :
    (free k pv).length=k-pv.length := by
  have he : (free k pv).toFinset = Finset.range k \ pv.toFinset := by ext b; simp [free_mem]
  have hsub : pv.toFinset ⊆ Finset.range k := fun b h => Finset.mem_range.mpr (hb b (by simpa using h))
  rw [← List.toFinset_card_of_nodup (free_nodup k pv),he,Finset.card_sdiff_of_subset hsub,
    List.toFinset_card_of_nodup hd,Finset.card_range]

theorem pivots_length_le {k : ℕ} {pv : List ℕ} (hd : pv.Nodup) (hb : ∀ b∈pv,b<k) : pv.length ≤ k := by
  rw [← List.toFinset_card_of_nodup hd,← Finset.card_range k]
  apply Finset.card_le_card
  intro b h
  exact Finset.mem_range.mpr (hb b (by simpa using h))

theorem rest_eq_iff {k x y : ℕ} {pv : List ℕ} :
    rest k pv x=rest k pv y ↔ ∀ b<k, b∉pv → x.testBit b=y.testBit b := by
  unfold rest
  rw [List.map_inj_left]
  simp only [free_mem,and_imp]

def seed (k : ℕ) (pv : List ℕ) (tail : List Bool) : ℕ :=
  pack ((List.range k).map fun b => (tail[(free k pv).idxOf b]?).getD false)

theorem seed_lt (k : ℕ) (pv : List ℕ) (tail : List Bool) : seed k pv tail<2^k := by
  simpa [seed] using pack_lt ((List.range k).map fun b => (tail[(free k pv).idxOf b]?).getD false)

theorem rest_seed {k : ℕ} {pv : List ℕ} {tail : List Bool} (h : tail.length=(free k pv).length) :
    rest k pv (seed k pv tail)=tail := by
  refine List.ext_getElem (by simp [rest,h]) ?_
  intro i hl hr
  have hi : i<(free k pv).length := by simpa [rest] using hl
  have hpos := (free_mem.mp (List.getElem_mem hi)).1
  unfold rest at hl ⊢
  rw [List.getElem_map]
  change (pack _).testBit ((free k pv)[i])=tail[i]
  rw [pack_bit (by simpa using hpos),List.getElem_map,List.getElem_range,
    (free_nodup k pv).idxOf_getElem i hi, List.getElem?_eq_getElem hr]
  rfl

theorem encoded_length {k x : ℕ} {tr : List (ℕ × Bool)} (hd : (tr.map Prod.fst).Nodup)
    (hb : ∀ b ∈ tr.map Prod.fst, b<k) :
    (tr.map Prod.snd ++ rest k (tr.map Prod.fst) x).length=k := by
  have h := pivots_length_le hd hb
  simp only [List.length_map] at h
  simp only [rest,List.length_append,List.length_map,free_length hd hb]
  omega

theorem encoded_lt {k x : ℕ} {tr : List (ℕ × Bool)} (hd : (tr.map Prod.fst).Nodup)
    (hb : ∀ b ∈ tr.map Prod.fst, b<k) : encoded k tr x<2^k := by
  simpa only [encoded,encoded_length hd hb] using pack_lt (tr.map Prod.snd ++ rest k (tr.map Prod.fst) x)

theorem encoded_bits {k x : ℕ} {tr : List (ℕ × Bool)} (hd : (tr.map Prod.fst).Nodup)
    (hb : ∀ b ∈ tr.map Prod.fst, b<k) :
    unpack k (encoded k tr x)=tr.map Prod.snd ++ rest k (tr.map Prod.fst) x := by
  convert unpack_pack (tr.map Prod.snd ++ rest k (tr.map Prod.fst) x) using 2
  · exact (encoded_length hd hb).symm
  · rfl

theorem prefix_bit {k x : ℕ} {tr : List (ℕ × Bool)} {i} (hi : i<tr.length) :
    (encoded k tr x).testBit i = tr[i].2 := by
  have hp : i<(tr.map Prod.snd).length := by simpa using hi
  unfold encoded
  rw [pack_bit (by simp;omega),List.getElem_append_left hp,List.getElem_map]

theorem encode_from_slices {k a x : ℕ} {tr : List (ℕ × Bool)} (ha : a<2^k)
    (hhead : tr.map Prod.snd=(unpack k a).take tr.length)
    (htail : rest k (tr.map Prod.fst) x=(unpack k a).drop tr.length) : encoded k tr x=a := by
  unfold encoded
  rw [hhead,htail,List.take_append_drop,pack_unpack ha]

end PEqualNP.Outside.L_meta_25560_aux.Packing

namespace PEqualNP.Outside.L_meta_25560_aux.Packing

theorem head_equals_take {k a : ℕ} {tr : List (ℕ × Bool)} (hlen : tr.length≤k)
    (h : ∀ j (hj : j<tr.length), tr[j].2=a.testBit j) :
    tr.map Prod.snd=(unpack k a).take tr.length := by
  apply List.ext_getElem (by simp [List.length_take,Nat.min_eq_left hlen])
  intro i h1 h2
  have hi : i<tr.length := by simpa using h1
  rw [List.getElem_map,List.getElem_take]
  simp [unpack,h i hi]

theorem encoded_eq_iff_rest {k x y : ℕ} {tr : List (ℕ × Bool)} (hd : (tr.map Prod.fst).Nodup)
    (hb : ∀ b ∈ tr.map Prod.fst, b<k) :
    encoded k tr x=encoded k tr y ↔ ∀ b<k, b∉tr.map Prod.fst → x.testBit b=y.testBit b := by
  rw [← rest_eq_iff]
  constructor
  · intro eqn
    have h := congrArg (unpack k) eqn
    simp only [encoded_bits hd hb] at h
    exact List.append_cancel_left h
  · intro h
    unfold encoded
    rw [h]

theorem exists_seed_for_suffix {k a : ℕ} {tr : List (ℕ × Bool)} (hd : (tr.map Prod.fst).Nodup)
    (hb : ∀ b ∈ tr.map Prod.fst, b<k) :
    ∃ s : Fin (2^k), rest k (tr.map Prod.fst) s.val = (unpack k a).drop tr.length := by
  let suffix := (unpack k a).drop tr.length
  let pv := tr.map Prod.fst
  refine ⟨⟨seed k pv suffix,seed_lt ..⟩,?_⟩
  apply rest_seed
  simp [suffix,free_length hd hb]

theorem prepareAddress {k a : ℕ} {tr : List (ℕ × Bool)} (ha : a<2^k) (hd : (tr.map Prod.fst).Nodup)
    (hb : ∀ b ∈ tr.map Prod.fst, b<k) (h : ∀ j (hj : j<tr.length), tr[j].2=a.testBit j) :
    ∃ s : Fin (2^k), ∀ x, (∀ b<k, b∉tr.map Prod.fst → x.testBit b=s.val.testBit b) →
      encoded k tr x=a := by
  obtain ⟨s,hs⟩ := exists_seed_for_suffix (a:=a) hd hb
  refine ⟨s,fun x hx=>encode_from_slices ha (head_equals_take ?_ h) ((rest_eq_iff.mpr hx).trans hs)⟩
  simpa using pivots_length_le hd hb

end PEqualNP.Outside.L_meta_25560_aux.Packing

namespace PEqualNP.Outside.L_meta_25560_aux

theorem pathOracle60 {k r e q i u : ℕ} (c : ℕ → Fin (2^k)) (hq : 0 < q)
    (hr : 3*e+2*q+3 ≤ r) (hkr : k+e+3=5*r) (hu : u < 2^k)
    (B : ℕ → Bool) (L : ℕ) (hL : L ≤ r-e-(e+q+3))
    (hpre : ∀ j < L, Z60 B j < r-e-(e+q+3)-(e+q-1))
    (tail : List Bool) (htail : tail.length = k-L) :
    let cut := e+q+3
    let D := e+q-1
    let tr := trace60 k r i cut D B L
    (tr.map Prod.fst).Nodup ∧ (∀ b ∈ tr.map Prod.fst, b < k) ∧
    ∃! key : Fin (2^k), Packing.rest k (tr.map Prod.fst) (Inverse.initial60 k u key.val)=tail ∧
      ∀ j < L, Inverse.guard60 k r i u c key.val (time60 cut j) (deficit60 D B j) = B j := by
  intro cut D tr
  let pv := tr.map Prod.fst
  let p := fun j => Inverse.pivot60 k r i (time60 cut j) (deficit60 D B j)
  have pp : pv = (List.range L).map p := by simp [pv,tr,trace60,p,pivot60,Inverse.pivot60,List.map_map,Function.comp_def]
  have hh (seed : Fin (2^k)) := Inverse.trace_inverse (i:=i) c (by omega : 2 ≤ k) hu (by omega : e≤r) hkr
    (time60 cut) (deficit60 D B) (bounds60 hq hr B hL hpre) (fun _ _ _ _ h => ordered60 cut D B h) B seed
  have nd : pv.Nodup := pp ▸ (hh ⟨0,Nat.two_pow_pos _⟩).1
  have inside (b : ℕ) : b ∈ pv ↔ ∃ j < L, p j = b := by rw [pp]; simp
  have bounded : ∀ b ∈ pv, b < k := by
    intro b hb; obtain ⟨j,_,rfl⟩ := (inside b).mp hb
    exact Nat.mod_lt _ (by omega)
  have plen : pv.length = L := by simp [pp]
  have ht : tail.length=(Packing.free k pv).length := by rw [Packing.free_length nd bounded,plen,htail]
  let s : Fin (2^k) := ⟨Packing.seed k pv tail, Packing.seed_lt ..⟩
  have hs : Packing.rest k pv s.val = tail := Packing.rest_seed ht
  have equival (x : ℕ) : (∀ b < k, (∀ j < L, p j ≠ b) → x.testBit b=s.val.testBit b) ↔ Packing.rest k pv x=tail := by
    rw [←hs,Packing.rest_eq_iff]; simp only [inside,not_exists,not_and]
  obtain ⟨key,⟨ho,hg⟩,unique⟩ := (hh s).2
  refine ⟨nd,bounded,key,⟨(equival _).mp ho,hg⟩,?_⟩
  intro y hy
  exact unique y ⟨(equival _).mpr hy.1, hy.2⟩

end PEqualNP.Outside.L_meta_25560_aux

namespace PEqualNP.Outside.L_meta_25560_aux

private theorem countsPrefix60 {a b : Nat→Bool} {L : Nat} (hab : ∀ j < L, a j=b j)
    {j : Nat} (hj : j≤L) : O60 a j=O60 b j ∧ Z60 a j=Z60 b j := by
  have eqf (c : Bool) : (Finset.range j).filter (fun n=>a n=c)=(Finset.range j).filter (fun n=>b n=c) := by
    apply Finset.filter_congr
    intro n hn;rw [hab n (lt_of_lt_of_le (Finset.mem_range.mp hn) hj)]
  exact ⟨congrArg Finset.card (eqf true),congrArg Finset.card (eqf false)⟩

theorem histForCode60 (k r i cut D m : Nat) (guard : Nat→Nat→Bool) (N x : Nat)
    (hbad : (run60 k r i cut D m guard N).1=false)
    (hacc : even60 (run60 k r i cut D m guard N).2=m) :
    let res:=run60 k r i cut D m guard N
    let a:=Packing.encoded k res.2 x
    ∃ L≤N, res=(false,trace60 k r i cut D a.testBit L) ∧ Z60 a.testBit L=m ∧
      (∀ j < L,Z60 a.testBit j < m) ∧
      (∀ j < L,guard (time60 cut j) (deficit60 D a.testBit j)=a.testBit j) := by
  intro res a
  obtain ⟨b,L,hle,he,hz,hpre,_,_,hg⟩ := acceptedHistory60 k r i cut D m guard N hbad hacc
  have ef : res.2=trace60 k r i cut D b L := congrArg Prod.snd he
  have ab (j : Nat) (hj : j < L) : a.testBit j=b j := by
    have p := Packing.prefix_bit (k:=k) (x:=x) (tr:=trace60 k r i cut D b L) (i:=j) (by simpa only [traceLength60] using hj)
    change (Packing.encoded k res.2 x).testBit j=b j
    rw [ef]
    simpa only [trace60,List.getElem_map,List.getElem_range] using p
  have df (j : Nat) (hj : j≤L) : deficit60 D a.testBit j=deficit60 D b j := by
    simp only [deficit60,(countsPrefix60 ab hj).1]
  have tr : trace60 k r i cut D a.testBit L=trace60 k r i cut D b L := by
    unfold trace60
    apply List.map_congr_left
    intro j hj
    have h := List.mem_range.mp hj
    rw [df j h.le,ab j h]
  refine ⟨L,hle,he.trans (by rw [tr]),(countsPrefix60 ab (by rfl : L≤L)).2.trans hz,?_,?_⟩
  · intro j hj; rw [(countsPrefix60 ab hj.le).2]; exact hpre j hj
  · intro j hj; rw [df j hj.le,ab j hj]; exact hg j hj
end PEqualNP.Outside.L_meta_25560_aux

namespace PEqualNP.Outside.L_meta_25560_aux

theorem mainBij60 (k r e q : Nat) (c : Nat → Fin (2^k)) (u i : Nat)
    (hq : 0<q) (hr : 3*e+2*q+3≤r) (hkr : k+e+3=5*r) (hu : u<2^k) :
    let cut := e+q+3
    let N := r-e-cut
    let D := e+q-1
    let m := N-D
    let G := Inverse.guard60 k r i u c
    let scan := fun raw => run60 k r i cut D m (G raw) N
    let code := fun raw => Packing.encoded k (scan raw).2 (Inverse.initial60 k u raw)
    Set.BijOn code {raw | raw < 2^k ∧ ((scan raw).1=false ∧ even60 (scan raw).2=m)}
      {a | a < 2^k ∧ O60 a.testBit N≤D} := by
  classical
  intro cut N D m G scan code
  have hs : N=m+D := by dsimp only [N,D,m,cut]; omega
  have hNk : N≤k := by dsimp only [N,cut]; omega
  have hist (x) (hx : (scan x).1=false ∧ even60 (scan x).2=m) :
      ∃ L≤N, scan x=(false,trace60 k r i cut D (code x).testBit L) ∧
        Z60 (code x).testBit L=m ∧ (∀j<L,Z60 (code x).testBit j < m) ∧
        ∀ j<L,G x (time60 cut j) (deficit60 D (code x).testBit j)=(code x).testBit j :=
    histForCode60 k r i cut D m (G x) N (Inverse.initial60 k u x) hx.1 hx.2
  constructor
  · intro x hx
    obtain ⟨L,hL,run,hz,hpre,_⟩ := hist x hx.2
    have oracle := pathOracle60 (i:=i) c hq hr hkr hu (code x).testBit L hL hpre
      (List.replicate (k-L) false) (by simp)
    have tr : (scan x).2=trace60 k r i cut D (code x).testBit L := congrArg Prod.snd run
    constructor
    · change Packing.encoded _ _ _ < _
      rw [tr]; exact Packing.encoded_lt oracle.1 oracle.2.1
    · change O60 (code x).testBit N≤D
      have z := Zmono60 (code x).testBit hL
      have := OZ60 (code x).testBit N
      omega
  constructor
  · intro x hx y hy hxy
    obtain ⟨L,hL,rx,zx,px,gx⟩ := hist x hx.2
    obtain ⟨M,_,ry,zy,py,gy⟩ := hist y hy.2
    rw [←hxy] at ry zy py gy
    have eq : L = M := by
      rcases lt_trichotomy L M with h|h|h
      · have := py L h; omega
      · exact h
      · have := px M h; omega
    subst M
    let tr := trace60 k r i cut D (code x).testBit L
    let tail := Packing.rest k (tr.map Prod.fst) (Inverse.initial60 k u x)
    have combo := pathOracle60 (i:=i) c hq hr hkr hu (code x).testBit L hL px
      (List.replicate (k-L) false) (by simp)
    have hh : tail.length=k-L := by
      calc
        _ = (Packing.free k (tr.map Prod.fst)).length := by simp only [tail,Packing.rest,List.length_map]
        _ = k-(tr.map Prod.fst).length := Packing.free_length combo.1 combo.2.1
        _ = _ := by simp [tr]
    have one := (pathOracle60 (i:=i) c hq hr hkr hu (code x).testBit L hL px tail hh).2.2
    have trx : (scan x).2=tr := congrArg Prod.snd rx
    have try_ : (scan y).2=tr := congrArg Prod.snd ry
    have same : Packing.encoded k tr (Inverse.initial60 k u x)=Packing.encoded k tr (Inverse.initial60 k u y) := by
      change Packing.encoded k (scan x).2 _=Packing.encoded k (scan y).2 _ at hxy
      simpa only [trx,try_] using hxy
    have freey : Packing.rest k (tr.map Prod.fst) (Inverse.initial60 k u y)=tail :=
      (Packing.rest_eq_iff.mpr ((Packing.encoded_eq_iff_rest combo.1 combo.2.1).mp same)).symm
    obtain ⟨w,_,uniq⟩ := one
    exact congrArg Fin.val ((uniq (⟨x,hx.1⟩ : Fin (2^k)) ⟨rfl,gx⟩).trans
      (uniq (⟨y,hy.1⟩ : Fin (2^k)) ⟨freey,gy⟩).symm)
  · intro a ha
    obtain ⟨L,hL,hz,hpre⟩ := leastStop60 a.testBit hs ha.2
    let tr := trace60 k r i cut D a.testBit L
    let tail := (Packing.unpack k a).drop L
    have hl : tail.length=k-L := by simp [tail]
    obtain ⟨_,_,y,⟨hy,hg⟩,_⟩ := pathOracle60 (i:=i) c hq hr hkr hu a.testBit L hL hpre tail hl
    have run : scan y.val=(false,tr) := scanPath60 k r i cut D m (G y.val) a.testBit hL hz hpre
      (fun j hj => (Omono60 a.testBit (by omega : j≤N)).trans ha.2)
      (fun j hj => (bounds60 hq hr a.testBit hL hpre j hj).2.2) hg
    refine ⟨y.val,⟨y.isLt,?_,?_⟩,?_⟩
    · exact congrArg Prod.fst run
    · rw [run]; exact (traceEven60 ..).trans hz
    · change Packing.encoded k (scan y.val).2 _=a
      have eqtr : (scan y.val).2=tr := congrArg Prod.snd run
      rw [eqtr]
      apply Packing.encode_from_slices ha.1
      · apply Packing.head_equals_take
        · change (trace60 k r i cut D a.testBit L).length≤k
          rw [traceLength60]; omega
        · intro j h
          simp [tr,trace60]
      · simpa only [tr,traceLength60] using hy

end PEqualNP.Outside.L_meta_25560_aux

theorem PEqualNP.Outside.L_meta_25560 : (∀ (k r e q : ℕ) (constants : ℕ → Fin (2 ^ k)) (u i : ℕ),
  0 < q → 3 * e + 2 * q + 3 ≤ r → k + e + 3 = 5 * r → u < 2 ^ k → i < k →
  let cut := e + q + 3
  let N := r - e - cut
  let D := e + q - 1
  let m := N - D
  let rot := fun (s wordR : ℕ) =>
    ((wordR <<< (s % k)) ||| (wordR >>> (k - s % k))) % 2 ^ k
  let step := fun w : ℕ => (List.range k).foldl (fun v b =>
    v ||| ((xor (w.testBit b)
      (!(w.testBit ((b + 1) % k)) && w.testBit ((b + 2) % k))).toNat <<< b)) 0
  let state := fun (key rounds : ℕ) =>
    (List.range rounds).foldl (fun prev t =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^
        rot (2 * t) key ^^^ (constants (t + 1)).val) (rot 1 key ^^^ u)
  let evenCount := fun tr : List (ℕ × Bool) => (tr.filter (fun item => !item.2)).length
  let scan := fun subject : ℕ =>
    (List.range N).foldl (fun (cfg : Bool × List (ℕ × Bool)) ix =>
      let tr₀ := cfg.2
      let zeros := evenCount tr₀
      let ones := tr₀.length - zeros
      if cfg.1 || decide (m ≤ zeros ∨ D < ones) then cfg
      else
        let t₀ := cut + ix + 1
        let g := D - ones
        if 4 * (r - t₀) < g then (true, tr₀)
        else
          let z := state subject (t₀ - 1)
          let b₀ := (i + 3 * r + k - (3 * t₀ + g)) % k
          let oddGuard := xor (xor (z.testBit b₀) (z.testBit ((b₀ + 1) % k)))
            (z.testBit ((b₀ + 2) % k))
          let pivot := (i + 3 * r + k + 5 - (5 * t₀ + g)) % k
          (false, tr₀ ++ [(pivot, oddGuard)]))
      (false, [])
  let accepted := fun keyA : ℕ =>
    let result := scan keyA
    result.1 = false ∧ evenCount result.2 = m
  let encode := fun keyE : ℕ =>
    let trace := (scan keyE).2
    let pivots := trace.map Prod.fst
    let x := rot 1 keyE ^^^ u
    let rest := ((List.range k).filter (fun freeBit => decide (freeBit ∉ pivots))).map (fun p => x.testBit p)
    ((trace.map Prod.snd) ++ rest).foldr (fun bit acc => bit.toNat + 2 * acc) 0
  Set.BijOn encode {raw : ℕ | raw < 2 ^ k ∧ accepted raw}
    {addr : ℕ | addr < 2 ^ k ∧ ((Finset.range N).filter (fun lowBit => addr.testBit lowBit)).card ≤ D}) := by
  intro k r e q c u i hq hr hkr hu _hi
  exact PEqualNP.Outside.L_meta_25560_aux.mainBij60 k r e q c u i hq hr hkr hu
