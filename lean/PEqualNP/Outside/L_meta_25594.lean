import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25594_aux
abbrev K := ZMod 2
def bit94 : Bool→K | false=>0 | true=>1
theorem bit_xor (x y : Bool) : bit94 (xor x y)=bit94 x+bit94 y := by cases x <;> cases y <;> decide
theorem bit_and (x y : Bool) : bit94 (x && y)=bit94 x*bit94 y := by cases x <;> cases y <;> decide
theorem bit_not (x : Bool) : bit94 (!x)=1+bit94 x := by cases x <;> decide
theorem bit_inj : Function.Injective bit94 := by intro a b;cases a <;> cases b <;> decide

theorem twoK94 : (2:K)=0 := by decide
theorem fourK94 : (4:K)=0 := by decide
theorem twice94 (x : K) : x+x=0 := by rw [←two_mul,twoK94,zero_mul]
abbrev Word94 (k : Nat) := Fin k→Bool
def add94 {k : Nat} (x y : Word94 k) : Word94 k := fun i=>xor (x i) (y i)
def D94 {k : Nat} (h : Word94 k) (f : Word94 k→K) (x : Word94 k) := f x+f (add94 x h)
theorem diffAdd94 {k} (h : Word94 k) (f g : Word94 k→K) (x : Word94 k) :
    D94 h (fun y=>f y+g y) x = D94 h f x+D94 h g x := by unfold D94;ring
theorem diffConst94 {k} (h : Word94 k) (a : K) (x : Word94 k) : D94 h (fun _=>a) x=0 := twice94 a
theorem diffMul94 {k} (h : Word94 k) (a : K) (f : Word94 k→K) (x : Word94 k) :
    D94 h (fun y=>a*f y) x = a*D94 h f x := by unfold D94;ring

theorem prodPol94 {k} (u v x : Word94 k) (f g : Word94 k→K)
    (ff : D94 v (D94 u f) x=0) (gg : D94 v (D94 u g) x=0) :
    D94 v (D94 u (fun y=>f y*g y)) x=
      D94 u f x*D94 v g x+D94 v f x*D94 u g x := by
  have corner (p : Word94 k→K) (h : D94 v (D94 u p) x=0) :
      p (add94 (add94 x v) u)=p x+p (add94 x u)+p (add94 x v) := by
    calc _ = p (add94 (add94 x v) u)+D94 v (D94 u p) x := by rw [h,add_zero]
         _ = _ := by unfold D94;ring_nf;simp [twoK94]
  simp only [D94]
  rw [corner f ff,corner g gg]
  ring_nf
  simp [twoK94,fourK94]

theorem polynomial94 {k} (l h u v x : Word94 k) (f g z : Word94 k→K)
    (B C E : Word94 k→Word94 k→K)
    (bf : ∀a b w,D94 b (D94 a f) w=B a b)
    (bg : ∀a b w,D94 b (D94 a g) w=C a b)
    (bz : ∀a b w,D94 b (D94 a z) w=E a b)
    (fl : B l h=0) (gl : C l h=0) :
    D94 v (D94 u (D94 h (D94 l (fun w=>z w+g w+f w*g w)))) x =
      (B l u*C h v+B l v*C h u)+(B h u*C l v+B h v*C l u) := by
  have first : D94 h (D94 l (fun w=>z w+g w+f w*g w)) =
    fun y=> (E l h+C l h)+(D94 l f y*D94 h g y + D94 h f y*D94 l g y) := by
    funext y
    have law := prodPol94 l h y f g ((bf ..).trans fl) ((bg ..).trans gl)
    simp only [D94] at bz bg law ⊢
    have bh := bz l h y;have ch := bg l h y
    linear_combination bh+ch+law
  rw [first]
  have inactive (a : Word94 k) (p : Word94 k→K) (Q : Word94 k→Word94 k→K)
      (src : ∀a b w,D94 b (D94 a p) w=Q a b) : D94 v (D94 u (D94 a p)) x=0 := by
    change D94 u (D94 a p) x + D94 u (D94 a p) (add94 x v)=0
    rw [src,src,twice94]
  have q1 := prodPol94 u v x (D94 l f) (D94 h g) (inactive l f B bf) (inactive h g C bg)
  have q2 := prodPol94 u v x (D94 h f) (D94 l g) (inactive h f B bf) (inactive l g C bg)
  rw [bf,bg,bf,bg] at q1 q2
  unfold D94 at q1 q2 ⊢
  linear_combination q1+q2+(E l h+C l h)*fourK94
end PEqualNP.Outside.L_meta_25594_aux


namespace PEqualNP.Outside.L_meta_25594_aux

def idx94 {k : Nat} (hk : 0<k) (s : Nat) : Fin k := ⟨s % k,Nat.mod_lt _ hk⟩
def anch94 {k : Nat} (d : Nat) (i : Fin k) := i.val+(k-d+2)
def at94 {k : Nat} (hk : 0<k) (d : Nat) (i : Fin k) (s : Nat) := idx94 hk (anch94 d i+s)
def dir94 {k : Nat} (p : Fin k) : Word94 k := fun i=>decide (i=p)
def sym94 {k : Nat} (p q : Fin k) (a b : Word94 k) : K :=
  bit94 (a p)*bit94 (b q)+bit94 (a q)*bit94 (b p)
def edge94 {k : Nat} (hk : 0<k) (d : Nat) (i : Fin k) (s : Nat) (a b : Word94 k) :=
  sym94 (at94 hk d i s) (at94 hk d i (s+1)) a b
def B94 {k : Nat} (hk : 0<k) (d : Nat) (i : Fin k) (s : Nat) (a b : Word94 k) :=
  edge94 hk d i s a b+edge94 hk d i (s+d) a b+edge94 hk d i (s+2*d) a b

theorem offEq94 {k s t : Nat} (hk : 0<k) (d : Nat) (i : Fin k) (hs : s<k) (ht : t<k) :
    at94 hk d i s=at94 hk d i t ↔ s=t := by
  constructor
  · intro h
    have m : anch94 d i+s ≡ anch94 d i+t [MOD k] := congrArg Fin.val h
    have hh := Nat.ModEq.add_left_cancel' (anch94 d i) m
    change s % k=t % k at hh
    rwa [Nat.mod_eq_of_lt hs,Nat.mod_eq_of_lt ht] at hh
  · rintro rfl;rfl

theorem sameArc94 {k d D : Nat} (hk : 0<k) (width : 2*D<k) (i j : Fin k) (a b : Nat) (al : a≤D) (bl : b≤D)
    (ha : at94 hk d i a=at94 hk d j 0) (hb : at94 hk d i b=at94 hk d j D) : i=j := by
  have am : anch94 d i+a ≡ anch94 d j [MOD k] := by change (anch94 d i+a) % k=(anch94 d j) % k;exact congrArg Fin.val ha
  have bm : anch94 d i+b ≡ anch94 d j+D [MOD k] := congrArg Fin.val hb
  have eq : anch94 d i+b ≡ anch94 d i+(a+D) [MOD k] := by simpa only [Nat.add_assoc] using bm.trans (am.add_right D).symm
  have ne := Nat.ModEq.add_left_cancel' (anch94 d i) eq
  change b % k=(a+D) % k at ne
  rw [Nat.mod_eq_of_lt (by omega : b<k),Nat.mod_eq_of_lt (by omega : a+D<k)] at ne
  have az : a=0 := by omega
  rw [az,Nat.add_zero] at am
  have ab := Nat.ModEq.add_right_cancel' (k-d+2) am
  change i.val % k=j.val % k at ab
  rwa [Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt,←Fin.ext_iff] at ab

theorem blockGone94 {k d : Nat} (hk : 0<k) (i p : Fin k) (s : Nat) (hs : s≤1)
    (sep : ∀j, j≤2*d+2→ at94 hk d i j≠p) (v : Word94 k) :
    B94 hk d i s (dir94 p) v=0 := by
  have e (t : Nat) (ht : t≤2*d+2) : bit94 (dir94 p (at94 hk d i t))=0 := by
    simp [dir94,sep t ht,bit94]
  unfold B94 edge94 sym94
  simp only [e _ (by omega : s≤2*d+2),e _ (by omega : s+1≤2*d+2),e _ (by omega : s+d≤2*d+2),
    e _ (by omega : s+d+1≤2*d+2),e _ (by omega : s+2*d≤2*d+2),e _ (by omega : s+2*d+1≤2*d+2),
    zero_mul,add_zero]

theorem endpoints94 {k d : Nat} (hk : 0<k) (hd : 0<d) (hw : 4*d+4<k) (i : Fin k) (v : Word94 k) :
    let lo := dir94 (at94 hk d i 0)
    let hi := dir94 (at94 hk d i (2*d+2))
    B94 hk d i 0 lo v = bit94 (v (at94 hk d i 1)) ∧ B94 hk d i 1 lo v=0 ∧
    B94 hk d i 0 hi v=0 ∧ B94 hk d i 1 hi v=bit94 (v (at94 hk d i (2*d+1))) := by
  dsimp only
  have lc (a : Nat) (ha : 0<a) (hb : a<k) : bit94 (dir94 (at94 hk d i 0) (at94 hk d i a))=0 := by
    have neq : at94 hk d i a≠at94 hk d i 0 := fun e=>by have :=(offEq94 hk d i hb hk).mp e;omega
    simp [dir94,neq,bit94]
  have hc (a : Nat) (ha : a<2*d+2) : bit94 (dir94 (at94 hk d i (2*d+2)) (at94 hk d i a))=0 := by
    have neq : at94 hk d i a≠at94 hk d i (2*d+2) := fun e=>by have :=(offEq94 hk d i (by omega) (by omega)).mp e;omega
    simp [dir94,neq,bit94]
  have self (a : Nat) : bit94 (dir94 (at94 hk d i a) (at94 hk d i a))=1 := by simp [dir94,bit94]
  unfold B94 edge94 sym94
  simp only [Nat.zero_add]
  rw [show 1+2*d+1=2*d+2 by omega,show 1+2*d=2*d+1 by omega]
  simp only [self,lc 1 (by omega) (by omega),lc 2 (by omega) (by omega),lc d (by omega) (by omega),
    lc (d+1) (by omega) (by omega),lc (2*d) (by omega) (by omega),lc (2*d+1) (by omega) (by omega),
    lc (1+d) (by omega) (by omega),lc (1+d+1) (by omega) (by omega),lc (2*d+2) (by omega) (by omega),
    hc 0 (by omega),hc 1 (by omega),hc 2 (by omega),hc d (by omega),hc (d+1) (by omega),
    hc (2*d) (by omega),hc (2*d+1) (by omega),hc (1+d) (by omega),hc (1+d+1) (by omega),
    zero_mul,one_mul,zero_add,add_zero,and_self]
end PEqualNP.Outside.L_meta_25594_aux


namespace PEqualNP.Outside.L_meta_25594_aux

def in94 {k : Nat} (hk : 0<k) (feedback : Word94 k→Word94 k) (ofs : Word94 k) (p : Nat) (x : Word94 k) : K :=
    bit94 (x (idx94 hk p)) + (1+bit94 (x (idx94 hk (p+1))))*bit94 (x (idx94 hk (p+2))) +
    bit94 (feedback x (idx94 hk p)) + bit94 (ofs (idx94 hk p))
def q94 {k : Nat} (hk : 0<k) (d : Nat) (feedback : Word94 k→Word94 k) (ofs : Word94 k)
    (i : Fin k) (s : Nat) (x : Word94 k) : K :=
  let p:=i.val+(k-d)+s
  in94 hk feedback ofs p x + in94 hk feedback ofs (p+d) x + in94 hk feedback ofs (p+2*d) x
def pol94 {k : Nat} (hk : 0<k) (d : Nat) (i : Fin k) (s : Nat) (a b : Word94 k) :=
  let p:=i.val+(k-d)+s
  let edge := fun j=>sym94 (idx94 hk (j+1)) (idx94 hk (j+2)) a b
  edge p+edge (p+d)+edge (p+2*d)

theorem inPol94 {k} (hk : 0<k) (fb : Word94 k→Word94 k) (ofs : Word94 k)
    (hf : ∀a b,fb (add94 a b)=add94 (fb a) (fb b)) (p : Nat) (a b x : Word94 k) :
    D94 b (D94 a (in94 hk fb ofs p)) x=sym94 (idx94 hk (p+1)) (idx94 hk (p+2)) a b := by
  simp only [D94,in94,sym94,hf,add94,bit_xor]
  ring_nf
  simp [twoK94,fourK94]

theorem qPol94 {k d} (hk : 0<k) (fb : Word94 k→Word94 k) (ofs : Word94 k)
    (hf : ∀a b,fb (add94 a b)=add94 (fb a) (fb b)) (i : Fin k) (s : Nat) (a b x : Word94 k) :
    D94 b (D94 a (q94 hk d fb ofs i s)) x=pol94 hk d i s a b := by
  let p:=i.val+(k-d)+s
  have h0:=inPol94 hk fb ofs hf p a b x
  have h1:=inPol94 hk fb ofs hf (p+d) a b x
  have h2:=inPol94 hk fb ofs hf (p+2*d) a b x
  dsimp only [D94,p] at h0 h1 h2
  dsimp only [D94,q94,pol94]
  linear_combination h0+h1+h2
theorem polNext94 {k d} (hk : 0<k) (i : Fin k) (s : Nat) (a b : Word94 k) :
    pol94 hk d i (s+1) a b=B94 hk d i s a b := by
  dsimp only [pol94,B94,edge94]
  have e (j : Nat) : sym94 (idx94 hk (i.val+(k-d)+(s+1)+j+1)) (idx94 hk (i.val+(k-d)+(s+1)+j+2)) a b =
      sym94 (at94 hk d i (s+j)) (at94 hk d i (s+j+1)) a b := by
    unfold at94 anch94
    rw [show i.val+(k-d)+(s+1)+j+1=i.val+(k-d+2)+(s+j) by omega,
        show i.val+(k-d)+(s+1)+j+2=i.val+(k-d+2)+(s+j+1) by omega]
  have e0 := e 0
  simp only [Nat.add_zero] at e0
  rw [e0,e d,e (2*d)]
end PEqualNP.Outside.L_meta_25594_aux


namespace PEqualNP.Outside.L_meta_25594_aux

def rawStep94 {k} (hk : 0<k) (x : Word94 k) (i : Fin k) :=
  xor (x i) (!(x (idx94 hk (i.val+1))) && x (idx94 hk (i.val+2)))
def rawMix94 {k} (hk : 0<k) (d : Nat) (x : Word94 k) (i : Fin k) :=
  xor (xor (x i) (x (idx94 hk (i.val+d)))) (x (idx94 hk (i.val+k-d)))
def middle94 {k} (hk : 0<k) (fb : Word94 k→Word94 k) (ofs x : Word94 k) := add94 (rawStep94 hk x) (add94 (fb x) ofs)
def output94 {k} (hk : 0<k) (d : Nat) (fb : Word94 k→Word94 k) (ofs x : Word94 k) :=
  rawStep94 hk (rawMix94 hk d (middle94 hk fb ofs x))

theorem idx_shift94 {k} (hk : 0<k) (a s : Nat) : idx94 hk ((idx94 hk a).val+s)=idx94 hk (a+s) :=
  Fin.ext (Nat.mod_add_mod a k s)
theorem idx_wrap94 {k} (hk : 0<k) (a : Nat) : idx94 hk (a+k)=idx94 hk a := Fin.ext (Nat.add_mod_right a k)

theorem midB94 {k} (hk : 0<k) (fb : Word94 k→Word94 k) (ofs x : Word94 k) (s : Nat) :
    bit94 (middle94 hk fb ofs x (idx94 hk s))=in94 hk fb ofs s x := by
  simp only [middle94,add94,rawStep94,idx_shift94,bit_xor,bit_and,bit_not,in94]
  ring
theorem mixB94 {k} (hk : 0<k) (d : Nat) (hd : d≤k) (fb : Word94 k→Word94 k) (ofs x : Word94 k)
    (i : Fin k) (s : Nat) :
    bit94 (rawMix94 hk d (middle94 hk fb ofs x) (idx94 hk (i.val+s)))=q94 hk d fb ofs i s x := by
  let a:=i.val+s
  let p:=i.val+(k-d)+s
  have left : idx94 hk ((idx94 hk a).val+k-d)=idx94 hk p := by
    rw [show (idx94 hk a).val+k-d=(idx94 hk a).val+(k-d) by omega,idx_shift94]
    congr 1;dsimp [p,a];omega
  have mid : idx94 hk (p+d)=idx94 hk a := by rw [show p+d=a+k by dsimp [a,p];omega,idx_wrap94]
  have right : idx94 hk (p+2*d)=idx94 hk (a+d) := by rw [show p+2*d=a+d+k by dsimp [a,p];omega,idx_wrap94]
  change bit94 (xor (xor (middle94 hk fb ofs x (idx94 hk a)) (middle94 hk fb ofs x (idx94 hk ((idx94 hk a).val+d))))
    (middle94 hk fb ofs x (idx94 hk ((idx94 hk a).val+k-d))))=in94 hk fb ofs p x+in94 hk fb ofs (p+d) x+in94 hk fb ofs (p+2*d) x
  rw [idx_shift94,left,←mid,←right]
  simp only [bit_xor,midB94]
  ring

theorem outEval94 {k} (hk : 0<k) (d : Nat) (hd : d≤k) (fb : Word94 k→Word94 k) (ofs x : Word94 k) (i : Fin k) :
    bit94 (output94 hk d fb ofs x i)=
      q94 hk d fb ofs i 0 x+q94 hk d fb ofs i 2 x+q94 hk d fb ofs i 1 x*q94 hk d fb ofs i 2 x := by
  have hh : idx94 hk (i.val+0)=i := Fin.ext (by simp [idx94,Nat.mod_eq_of_lt i.isLt])
  have h0 := mixB94 hk d hd fb ofs x i 0
  rw [hh] at h0
  simp only [output94,rawStep94,bit_xor,bit_and,bit_not,h0,mixB94 hk d hd fb ofs x i]
  ring
end PEqualNP.Outside.L_meta_25594_aux


namespace PEqualNP.Outside.L_meta_25594_aux

theorem bSym94 {k} (hk : 0<k) (d s : Nat) (i : Fin k) (a b : Word94 k) :
    B94 hk d i s a b=B94 hk d i s b a := by unfold B94 edge94 sym94;ring

theorem select94 {k} (hk : 0<k) (d : Nat) (hd : 0<d) (hw : 4*d+4<k)
    (fb : Word94 k→Word94 k) (hf : ∀a b,fb (add94 a b)=add94 (fb a) (fb b))
    (ofs : Word94 k) (j : Fin k) (u v x : Word94 k) (i : Fin k) :
    let l:=dir94 (at94 hk d j 0)
    let h:=dir94 (at94 hk d j (2*d+2))
    let p:=at94 hk d j 1
    let q:=at94 hk d j (2*d+1)
    D94 v (D94 u (D94 h (D94 l (fun w=>bit94 (output94 hk d fb ofs w i))))) x=
      if i=j then bit94 (u p)*bit94 (v q)+bit94 (v p)*bit94 (u q) else 0 := by
  intro l h p q
  let Q:=q94 hk d fb ofs i
  let B:=B94 hk d i
  have law (a b z : Word94 k) (s : Nat) : D94 b (D94 a (Q (s+1))) z=B s a b :=
    (qPol94 hk fb ofs hf i (s+1) a b z).trans (polNext94 hk i s a b)
  have eqF : (fun w=>bit94 (output94 hk d fb ofs w i))=fun w=>Q 0 w+Q 2 w+Q 1 w*Q 2 w :=
    funext (fun w=>outEval94 hk d (by omega) fb ofs w i)
  rw [eqF]
  have calc4 (a : B 0 l h=0) (b : B 1 l h=0) :=
    polynomial94 l h u v x (Q 1) (Q 2) (Q 0) (B 0) (B 1) (pol94 hk d i 0)
      (fun a b w=>law a b w 0) (fun a b w=>law a b w 1) (qPol94 hk fb ofs hf i 0) a b
  by_cases ij : i=j
  · subst i
    simp only [ite_true]
    have ep (z : Word94 k) : B 0 l z=bit94 (z p) ∧ B 1 l z=0 ∧ B 0 h z=0 ∧ B 1 h z=bit94 (z q) :=
      endpoints94 hk hd hw j z
    have no : p≠at94 hk d j (2*d+2) := fun e=>by
      have := (offEq94 hk d j (by omega : 1<k) (by omega : 2*d+2<k)).mp e;omega
    have eh : B 0 l h=0 := by rw [(ep h).1];simp [h,dir94,no,bit94]
    rw [calc4 eh (ep h).2.1,(ep u).1,(ep u).2.1,(ep u).2.2.1,(ep u).2.2.2,
      (ep v).1,(ep v).2.1,(ep v).2.2.1,(ep v).2.2.2]
    ring
  · simp only [ite_eq_right ij]
    by_cases aa : ∃ s, s≤2*d+2 ∧ at94 hk d i s=at94 hk d j 0
    · obtain ⟨a,al,az⟩ := aa
      have kill (s : Nat) (hs : s≤1) (z : Word94 k) : B s h z=0 :=
        blockGone94 hk i _ s hs (fun b bl eqn=>ij (sameArc94 hk (by omega) i j a b al bl az eqn)) z
      have c0 : B 0 l h=0 := (bSym94 hk d 0 i l h).trans (kill 0 (by omega) l)
      have c1 : B 1 l h=0 := (bSym94 hk d 1 i l h).trans (kill 1 (by omega) l)
      rw [calc4 c0 c1,kill 1 (by omega) v,kill 1 (by omega) u,kill 0 (by omega) u,kill 0 (by omega) v]
      ring
    · have kill (s : Nat) (hs : s≤1) (z : Word94 k) : B s l z=0 :=
        blockGone94 hk i _ s hs (fun a al eqn=>aa ⟨a,al,eqn⟩) z
      rw [calc4 (kill 0 (by omega) h) (kill 1 (by omega) h),kill 0 (by omega) u,kill 0 (by omega) v,
        kill 1 (by omega) u,kill 1 (by omega) v]
      ring
end PEqualNP.Outside.L_meta_25594_aux

namespace PEqualNP.Outside.L_meta_25594_aux

def boolDiff94 {k : Nat} (f : Word94 k→Bool) (h x : Word94 k) :=
  xor (f x) (f (add94 x h))

private theorem foldParity94 (xs : List Bool) (a : Bool) :
    bit94 (xs.foldl xor a) = bit94 a + (xs.map bit94).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons,ih,bit_xor]
    simp [add_assoc]

theorem maskedFour94 {k : Nat} (output : Word94 k→Fin k→Bool) (mask : Word94 k)
    (j : Fin k) (lo hi u v base : Word94 k) (det : K)
    (hlocal : ∀i, D94 v (D94 u (D94 hi (D94 lo (fun x=>bit94 (output x i))))) base =
      if i=j then det else 0) :
    let observed := fun x => (List.ofFn (fun i : Fin k => mask i && output x i)).foldl xor false
    bit94 (boolDiff94 (boolDiff94 (boolDiff94 (boolDiff94 observed lo) hi) u) v base) =
      bit94 (mask j)*det := by
  classical
  intro observed
  have sumParity (x : Word94 k) : bit94 (observed x) = ∑ i,bit94 (mask i)*bit94 (output x i) := by
    change bit94 ((List.ofFn (fun i : Fin k=>mask i && output x i)).foldl xor false)=_
    rw [foldParity94,List.map_ofFn,List.sum_ofFn]
    simp only [show bit94 false=0 from rfl,zero_add,Function.comp_apply,bit_and]
  calc
    _ = D94 v (D94 u (D94 hi (D94 lo (fun x => ∑ i,bit94 (mask i)*bit94 (output x i))))) base := by
      simp only [boolDiff94,bit_xor,D94,sumParity]
    _ = ∑ i,bit94 (mask i)*D94 v (D94 u (D94 hi (D94 lo (fun x=>bit94 (output x i))))) base := by
      simp only [D94,mul_add,Finset.sum_add_distrib]
    _ = _ := by simp [hlocal,mul_ite]

end PEqualNP.Outside.L_meta_25594_aux

open PEqualNP.Outside.L_meta_25594_aux in
theorem PEqualNP.Outside.L_meta_25594 :
∀ (k d : ℕ) (hk : 0 < k), 0 < d → 4 * d + 4 < k →
  let W := Fin k → Bool
  let idx := fun (n : ℕ) => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let add := fun (x y : W) (i : Fin k) => xor (x i) (y i)
  let step := fun (x : W) (i : Fin k) =>
    xor (x i) (!(x (idx (i.val + 1))) && x (idx (i.val + 2)))
  let mix := fun (x : W) (i : Fin k) =>
    xor (xor (x i) (x (idx (i.val + d)))) (x (idx (i.val + k - d)))
  let unit := fun (p : Fin k) (i : Fin k) => decide (i = p)
  let delta := fun (f : W → Bool) (h x : W) => xor (f x) (f (add x h))
  ∀ (feedback : W → W), (∀ x y, feedback (add x y) = add (feedback x) (feedback y)) →
  ∀ (offset mask : W),
    let observed := fun (z : W) =>
      let middle := add (step z) (add (feedback z) offset)
      let out := step (mix middle)
      (List.ofFn (fun bit : Fin k => mask bit && out bit)).foldl xor false
    ∀ (j : Fin k) (u v base : W),
      let lo := idx (j.val + k + 2 - d)
      let hi := idx (j.val + 4 + d)
      let a := idx (j.val + k + 3 - d)
      let b := idx (j.val + 3 + d)
      delta (delta (delta (delta observed (unit lo)) (unit hi)) u) v base =
        (mask j && xor (u a && v b) (u b && v a)) := by
  intro k d hk hd hw W idx add step mix unit delta fb hf ofs mask observed j u v base lo hi a b
  have el : at94 hk d j 0=lo := by
    change idx94 hk (j.val+(k-d+2)+0)=idx94 hk (j.val+k+2-d)
    congr 1;omega
  have eh : at94 hk d j (2*d+2)=hi := by
    change idx94 hk (j.val+(k-d+2)+(2*d+2))=idx94 hk (j.val+4+d)
    rw [show j.val+(k-d+2)+(2*d+2)=j.val+4+d+k by omega,idx_wrap94]
  have ea : at94 hk d j 1=a := by
    change idx94 hk (j.val+(k-d+2)+1)=idx94 hk (j.val+k+3-d)
    congr 1;omega
  have eb : at94 hk d j (2*d+1)=b := by
    change idx94 hk (j.val+(k-d+2)+(2*d+1))=idx94 hk (j.val+3+d)
    rw [show j.val+(k-d+2)+(2*d+1)=j.val+3+d+k by omega,idx_wrap94]
  let det := bit94 (u a)*bit94 (v b)+bit94 (v a)*bit94 (u b)
  have each (i : Fin k) : D94 v (D94 u (D94 (dir94 hi) (D94 (dir94 lo)
       (fun x=>bit94 (output94 hk d fb ofs x i))))) base = if i=j then det else 0 := by
    have h:=select94 hk d hd hw fb hf ofs j u v base i
    dsimp only at h
    rw [el,eh,ea,eb] at h
    exact h
  apply bit_inj
  calc _ = bit94 (mask j)*det := maskedFour94 (output94 hk d fb ofs) mask j (dir94 lo) (dir94 hi) u v base det each
       _ = _ := by simp only [det,bit_and,bit_xor];ring
