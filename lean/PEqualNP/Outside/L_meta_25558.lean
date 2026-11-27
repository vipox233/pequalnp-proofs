import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25558_aux
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
end PEqualNP.Outside.L_meta_25558_aux


namespace PEqualNP.Outside.L_meta_25558_aux.Bits378
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

end PEqualNP.Outside.L_meta_25558_aux.Bits378

namespace PEqualNP.Outside.L_meta_25558_aux.Bits378
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

end PEqualNP.Outside.L_meta_25558_aux.Bits378

namespace PEqualNP.Outside.L_meta_25558_aux.Bits378
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

end PEqualNP.Outside.L_meta_25558_aux.Bits378

namespace PEqualNP.Outside.L_meta_25558_aux
open PEqualNP.Outside.L_meta_25558_aux.Bits378

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

end PEqualNP.Outside.L_meta_25558_aux


namespace PEqualNP.Outside.L_meta_25558_aux
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


end PEqualNP.Outside.L_meta_25558_aux

namespace PEqualNP.Outside.L_meta_25558_aux

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
    (bounds : ∀ j<m, 5≤time j ∧ time j≤r-e ∧ deficit j≤4*(r-time j))
    (ordered : ∀ j<m, ∀ h<m, j<h →
      time j<time h ∧ 5*time j+deficit j<5*time h+deficit h)
    (seed : Fin (2^k)) (target : Nat → Bool) :
    let P := i+3*r+k
    let J := fun j => P+5-(5*time j+deficit j)
    let p := fun j => J j % k
    let b := fun j => P-(3*time j+deficit j)
    let g := fun j x => guard32 k row.val c (time j) (b j) x
    let out := (List.range m).foldl (fun x j => if g j x=target j then x else x ^^^ (1 <<< p j)) seed.val
    let same := fun x : Nat => ∀ b<k, (∀ j<m, p j≠b) → x.testBit b = seed.val.testBit b
    out<2^k ∧ same out ∧ (∀ j<m, g j out=target j) ∧
      ∀ x : Fin (2^k), same x.val → (∀ j<m, g j x.val=target j) → x.val=out := by
  intro P J p b g out same
  let toggle := fun t x => xor (g t x) (target t)
  have hJ (t : Nat) (ht : t<m) : J t<P ∧ P<J t+k := by
    obtain ⟨lo,hi,last⟩ := bounds t ht
    dsimp [J,P]
    omega
  have decreasing {t v : Nat} (vt : v<m) (tv : t<v) : J v<J t := by
    have cap := bounds v vt
    obtain ⟨_,inc⟩ := ordered t (by omega) v vt tv
    dsimp [J,P]
    omega
  have sep {t v : Nat} (vt : v<m) (tv : t<v) : p t≠p v :=
    residueSep58 (decreasing vt tv) (by have := hJ v vt; have := hJ t (by omega); omega)
  have hn : ((List.range m).map p).Nodup := by
    apply List.Nodup.map_on _ List.nodup_range
    intro t ht v hv eqn
    rcases lt_trichotomy t v with lt|eq|gt
    · exact False.elim (sep (List.mem_range.mp hv) lt eqn)
    · exact eq
    · exact False.elim (sep (List.mem_range.mp ht) gt eqn.symm)
  have order (ls : List Nat) (sub : ∀ t∈ls,t<m) (sort : ls.Pairwise (·<·)) :
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
      rw [PEqualNP.Outside.L_meta_25558_aux.Bits378.xorCancelR]
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
      out=x ↔ same x ∧ ∀ j<m,g j x=target j := by
    have f := H x
    rw [← foldVisitMod p toggle (List.range m) hp seed.val seed.isLt,←outEq] at f
    simp only [Nat.mod_eq_of_lt hx,List.mem_range] at f
    have off (b : Nat) : b∉(List.range m).map p ↔ ∀ j<m,p j≠b := by simp
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

end PEqualNP.Outside.L_meta_25558_aux

open PEqualNP.Outside.L_meta_25558_aux in
theorem PEqualNP.Outside.L_meta_25558 :
∀ (k r e i m : ℕ) (row : Fin (2 ^ k)) (constants : ℕ → Fin (2 ^ k))
    (time deficit : ℕ → ℕ),
  0 < k → e ≤ r → k + e + 3 = 5 * r → i < k →
  (∀ j < m, 5 ≤ time j ∧ time j ≤ r - e ∧ deficit j ≤ 4 * (r - time j)) →
  (∀ j < m, ∀ h < m, j < h →
    time j < time h ∧ 5 * time j + deficit j < 5 * time h + deficit h) →
  let P := i + 3 * r + k
  let pivot := fun slot : ℕ => (P + 5 - (5 * time slot + deficit slot)) % k
  let rot := fun (s wordR : ℕ) => ((wordR <<< (s % k)) ||| (wordR >>> (k - s % k))) % 2 ^ k
  let step := fun w : ℕ => (List.range k).foldl (fun v b =>
    v ||| ((xor (w.testBit b)
      (!(w.testBit ((b + 1) % k)) && w.testBit ((b + 2) % k))).toNat <<< b)) 0
  let guard := fun (idx start : ℕ) =>
    let key := rot (k - 1) (start ^^^ row.val)
    let z := (List.range (time idx - 1)).foldl (fun prev t =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^
        rot (2 * t) key ^^^ (constants (t + 1)).val) start
    let b₀ := (P - (3 * time idx + deficit idx)) % k
    xor (xor (z.testBit b₀) (z.testBit ((b₀ + 1) % k))) (z.testBit ((b₀ + 2) % k))
  ∀ (seed : Fin (2 ^ k)) (target : ℕ → Bool),
    let out := (List.range m).foldl (fun word pos =>
      if guard pos word = target pos then word else word ^^^ (1 <<< pivot pos)) seed.val
    let sameSeed := fun subject : ℕ =>
      ∀ b < k, (∀ h < m, pivot h ≠ b) → subject.testBit b = seed.val.testBit b
    out < 2 ^ k ∧ sameSeed out ∧ (∀ j < m, guard j out = target j) ∧
      ∀ x : Fin (2 ^ k), sameSeed x.val → (∀ j < m, guard j x.val = target j) → x.val = out := by
  intro k r e i m row c time deficit hk he kr hi bounds ordered P pivot rot step guard seed target out same
  have H := sweep58 (i:=i) row c time deficit hk he kr bounds ordered seed target
  dsimp only at H
  have guardEq (j x : Nat) : guard j x =
      guard32 k row.val c (time j) (P-(3*time j+deficit j)) x := by
    let raw := P-(3*time j+deficit j)
    let z := startRounds32 k row.val c (time j - 1) x
    change xor (xor (z.testBit (raw % k)) (z.testBit ((raw % k+1) % k))) (z.testBit ((raw % k+2) % k)) = _
    simp only [Nat.mod_add_mod,guard32,z,raw]
  simpa only [out,same,guardEq,pivot,P] using H
