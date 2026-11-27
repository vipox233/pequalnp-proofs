import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25521_aux

abbrev Sig := Int → Bool
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

theorem halves {α:Type} [Fintype α] (n r:Nat) (cap:r≤n) (g:α → Nat → Bool)
 (size:Fintype.card α=2^n)
 (law:∀t,t<r → ∃f:α→α, (∀a,f (f a)=a) ∧
   (∀a,g (f a) t= !(g a t)) ∧ (∀a j,j<t → g (f a) j=g a j)) :
   (Finset.univ.filter (fun a:α => decide (∀ t:Fin r,g a t.val=false))).card = 2^(n-r) := by
 classical
 let S := fun m:Nat=> Finset.univ.filter (fun a:α => ∀j,j<m → g a j=false)
 have sm (m:Nat) (a:α) : a∈S m ↔ ∀j,j<m → g a j=false := by simp [S]
 have recu (t:Nat) (ht:t<r) : (S t).card = 2*(S (t+1)).card := by
  obtain ⟨f,inv,neg,old⟩:=law t ht
  let p:=fun a => g a t=false
  have stay {a:α} (ha:a∈S t) : f a∈S t := (sm _ _).mpr (fun j hj=> (old a j hj).trans ((sm _ _).mp ha j hj))
  have aa : (S t).filter p = S (t+1) := by
   ext a
   simp only [Finset.mem_filter,sm,p]
   constructor
   · rintro ⟨h,e⟩ j hj
     by_cases eq:j=t
     · rwa [eq]
     · exact h j (by omega)
   · intro h; exact ⟨fun j hj=>h j (by omega),h t (by omega)⟩
  have ab : ((S t).filter p).card = ((S t).filter (fun a=>¬p a)).card := by
   apply Finset.card_nbij' f f
   · intro a ha
     obtain ⟨h,e⟩:=Finset.mem_filter.mp ha
     refine Finset.mem_filter.mpr ⟨stay h,?_⟩
     change g a t=false at e
     change ¬g (f a) t=false
     rw [neg,e]; decide
   · intro a ha
     obtain ⟨h,e⟩:=Finset.mem_filter.mp ha
     refine Finset.mem_filter.mpr ⟨stay h,?_⟩
     change ¬g a t=false at e
     change g (f a) t=false
     rw [neg];cases hval:g a t <;> simp_all
   · exact fun a _=>inv a
   · exact fun a _=>inv a
  have hs : ((S t).filter p).card + ((S t).filter (fun a=>¬p a)).card = (S t).card :=
   Finset.card_filter_add_card_filter_not p
  rw [← ab,aa] at hs
  omega
 have count (m:Nat) (hm:m≤r) : (S m).card=2^(n-m) := by
  induction m with
  | zero => simpa [S] using size
  | succ m ih =>
    have a:=ih (by omega)
    have b:=recu m (by omega)
    have e:n-m = n-(m+1)+1 := by omega
    rw [e,pow_succ] at a;omega
 have same : Finset.univ.filter (fun a:α => decide (∀t:Fin r,g a t.val=false))=S r := by
  ext a
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq,sm]
  exact ⟨fun h t ht => h ⟨t,ht⟩,fun h t=>h t.val t.isLt⟩
 rw [same];exact count _ le_rfl

namespace Bdy
def lin (s : Sig) (j : Int) := xor (xor (s j) (s (j-1))) (s (j+1))
def mix (s : Sig) (j : Int) := chi (lin s j) (lin s (j+1)) (lin s (j+2))
def state (x w : Sig) (c : Nat → Sig) : Nat → Sig
  | 0 => x
  | t+1 => fun j => xor (xor (mix (state x w c t) j) (w (j-2*(t:Int)))) (c (t+1) j)
def guard (x w : Sig) (c : Nat → Sig) (P : Int) (t : Nat) :=
  lin (state x w c t) (P-3*(t:Int)-2)
def start (k row w : Nat) := rot k 1 w ^^^ row
def constBits {k : Nat} (c : Nat → Fin (2^k)) (t : Nat) := bits k (c t).val

def rawMix (k x : Nat) := rawStep k (x ^^^ rot k 1 x ^^^ rot k (k-1) x)
def rawState (k : Nat) (c : Nat → Fin (2^k)) (row w t : Nat) :=
  (List.range t).foldl (fun x s => rawMix k x ^^^ rot k (2*s) w ^^^ (c (s+1)).val) (start k row w)

theorem rawSucc {k} (c : Nat → Fin (2^k)) (row w t : Nat) :
    rawState k c row w (t+1) = rawMix k (rawState k c row w t) ^^^ rot k (2*t) w ^^^ (c (t+1)).val := by
  simp [rawState,List.range_succ,List.foldl_append]

theorem startLt {k row : Nat} (w : Nat) (hr : row<2^k) : start k row w<2^k :=
  Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) hr

theorem rawBound {k row : Nat} (c : Nat → Fin (2^k)) (w t : Nat) (hr : row<2^k) :
    rawState k c row w t < 2^k := by
  cases t with
  | zero => exact startLt w hr
  | succ t =>
    rw [rawSucc]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepBound ..) (Nat.mod_lt _ (by positivity))) (c _).isLt

theorem bitsMix {k x : Nat} (hk : 2≤k) (hx : x<2^k) (j : Int) :
    bits k (rawMix k x) j=mix (bits k x) j := by
  have linEq (z : Int) : bits k (x ^^^ rot k 1 x ^^^ rot k (k-1) x) z=lin (bits k x) z := by
    simp only [bitsXor,bitsRot (show 1<k by omega) hx,bitsRot (show k-1<k by omega) hx,lin]
    have e : z-((k-1:Nat):Int)=z+1-(k:Int) := by omega
    simp [bits,idx,e]
  simp only [rawMix,bitsStep (show 0<k by omega),linEq,mix]

theorem rawEq {k t row w : Nat} (c : Nat → Fin (2^k)) (hk : 2≤k) (ht : 2*t≤k)
    (hr : row<2^k) (hw : w<2^k) :
    bits k (rawState k c row w t)=state (bits k (start k row w)) (bits k w) (constBits c) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext j
    rw [rawSucc]
    simp only [bitsXor,bitsMix hk (rawBound c w t hr),ih (by omega),bitsRot (show 2*t<k by omega) hw,state,constBits]
    congr 3 <;> omega

def flipped (k w : Nat) (q : Int) := w ^^^ (1 <<< (idx k q))

theorem flippedLt {k w : Nat} (hk : 0<k) (hw : w<2^k) (q : Int) : flipped k w q<2^k := by
  unfold flipped
  rw [Nat.one_shiftLeft]
  exact Nat.xor_lt_two_pow hw (Nat.pow_lt_pow_right (by decide) (idxlt hk q))

theorem flippedBit (k w : Nat) (q z : Int) :
    bits k (flipped k w q) z=xor (bits k w z) (decide (idx k q=idx k z)) := by
  simp [flipped,bits,Nat.testBit_xor,Nat.one_shiftLeft,Nat.testBit_two_pow,beq_iff_eq,eq_comm]

theorem idxSep {k : Nat} {q z : Int} (lo : q-(k:Int)<z) (hi : z<q) : idx k q ≠ idx k z := by
  intro h
  have kp : (0:Int)<k := by omega
  have em : z%(k:Int)=q%(k:Int) := by
    unfold idx at h
    have hz := Int.emod_nonneg z (ne_of_gt kp)
    have hq := Int.emod_nonneg q (ne_of_gt kp)
    omega
  have div : (k:Int) ∣ q-z := Int.modEq_iff_dvd.mp em
  have := Int.le_of_dvd (show 0<q-z by omega) div
  omega

theorem flipAway {k w : Nat} {q z : Int} (lo : q-(k:Int)<z) (hi : z<q) :
    bits k (flipped k w q) z = bits k w z := by
  rw [flippedBit]
  simp [idxSep lo hi]

theorem flipAtKey (k w : Nat) (q : Int) : bits k (flipped k w q) q = !(bits k w q) := by
  rw [flippedBit]
  simp

theorem flipWrapped (k w : Nat) (q : Int) : bits k (flipped k w q) (q-(k:Int)) = !(bits k w (q-(k:Int))) := by
  rw [flippedBit]
  simp [idx]

theorem linAgree {a b : Sig} {j : Int}
    (same : ∀ z : Int, j-1 ≤ z → z ≤ j+1 → a z=b z) : lin a j=lin b j := by
  unfold lin
  rw [same j (by omega) (by omega),same (j-1) (by omega) (by omega),same (j+1) (by omega) (by omega)]

theorem mixAgree {a b : Sig} {j : Int}
    (same : ∀ z : Int, j-1 ≤ z → z ≤ j+3 → a z=b z) : mix a j=mix b j := by
  have l (v : Int) (h1 : j≤v) (h2 : v≤j+2) := linAgree (a:=a) (b:=b) (j:=v)
    (fun z hl hr => same z (by omega) (by omega))
  unfold mix
  rw [l j (by omega) (by omega),l (j+1) (by omega) (by omega),l (j+2) (by omega) (by omega)]

theorem mixEdge {a b : Sig} {j : Int}
    (same : ∀ z : Int, j-1 ≤ z → z ≤ j+2 → a z=b z) :
    xor (mix a j) (mix b j) = (xor (a (j+3)) (b (j+3)) && !(lin a (j+1))) := by
  have l (v : Int) (h1 : j≤v) (h2 : v≤j+1) := linAgree (a:=a) (b:=b) (j:=v)
    (fun z hl hr => same z (by omega) (by omega))
  have F : ∀ v w p q : Bool, xor (chi v w p) (chi v w q)= (xor p q && !w) := by decide
  have H : ∀ v p q : Bool, xor (xor v p) (xor v q)=xor p q := by decide
  unfold mix
  rw [←l j (by omega) (by omega),←l (j+1) (by omega) (by omega),F]
  congr 1
  unfold lin
  rw [same (j+2) (by omega) (by omega),same (j+2-1) (by omega) (by omega),H,
    show j+2+1=j+3 by omega]

theorem injectDelta (a b u v c : Bool) :
    xor (xor (xor a u) c) (xor (xor b v) c) = xor (xor a b) (xor u v) := by
  revert a b u v c
  decide

end Bdy
end PEqualNP.Outside.L_meta_25521_aux

namespace PEqualNP.Outside.L_meta_25521_aux.Bdy

def y521 (k u w : Nat) := lin (bits k (start k u w))

def Eq521 (k u w : Nat) (q : Int) : Nat → Prop
  | 0 => y521 k u w (q-1)=true
  | 1 => y521 k u w q=y521 k u w (q+1)
  | 2 => y521 k u w (q+1)=y521 k u w (q+2)
  | 3 => y521 k u w (q+3)=true
  | 4 => False
  | _ => True

def first521 (k u w c : Nat) := rawMix k (start k u w) ^^^ w ^^^ c

end PEqualNP.Outside.L_meta_25521_aux.Bdy

namespace PEqualNP.Outside.L_meta_25521_aux
namespace Overlap521
lemma hit {k r e i d : Nat} (hr : 4 ≤ r) (hk : 5 ≤ k) (width : k+3+e=5*r) (hd : d<5) :
    (∃ j < 4*r-3, (((i+r*k+1-r)%k)+j)%k = (((i+(2*r)*k+2-2*r)%k)+k-2+d)%k) ↔ d≤e := by
  let a := i+r*k+1-r
  let b := i+(2*r)*k+2-2*r
  let off := (r+1)*k+d-(r+1)
  have bnd : r ≤ r*k := Nat.le_mul_of_pos_right r (by omega)
  have ab : a+off=b+(k-2+d) := by
    dsimp [a,b,off]
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_assoc 2 r k]
    omega
  have eqn : ((a%k)+off)%k = (b%k+k-2+d)%k := by
    calc
      _ = (a+off)%k := Nat.mod_add_mod _ _ _
      _ = (b+(k-2+d))%k := by rw [ab]
      _ = (b%k+(k-2+d))%k := (Nat.mod_add_mod _ _ _).symm
      _ = _ := by congr 1 <;> omega
  change (∃ j < 4*r-3, (a%k+j)%k = (b%k+k-2+d)%k) ↔ _
  rw [←eqn]
  have equiv (j : Nat) : (a%k+j)%k=(a%k+off)%k ↔ j%k=off % k := by
    constructor
    · exact Nat.ModEq.add_left_cancel' (a%k)
    · intro h;exact Nat.ModEq.add_left _ h
  simp_rw [equiv]
  have test : (∃ j < 4*r-3, j%k=off % k) ↔ off % k<4*r-3 := by
    constructor
    · rintro ⟨j,hj,h⟩; rw [←h]; exact lt_of_le_of_lt (Nat.mod_le _ _) hj
    · intro h; exact ⟨_,h,Nat.mod_mod _ _⟩
  rw [test]
  by_cases h : k≤r
  · have small := Nat.mod_lt off (show 0<k by omega);omega
  · have oo : off = (k+d-r-1)+r*k := by dsimp [off];rw [Nat.add_mul,Nat.one_mul];omega
    rw [oo,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt (show k+d-r-1<k by omega)]
    omega
lemma inverse {k j q d : Nat} (hk:5 ≤ k) (hq:q<k) (hd:d<k) :
    idx k ((j:Int)-((q:Int)-2))=d ↔ j%k=(q+k-2+d)%k := by
  let a := k+2-q
  have left : idx k ((j:Int)-((q:Int)-2))=(j+a)%k := by
    unfold idx
    rw [←Int.add_emod_left,Int.toNat_emod (by omega) (by omega)]
    congr 1 <;> dsimp [a] <;> omega
  have right : ((q+k-2+d)+a)%k=d := by
    rw [show (q+k-2+d)+a=(d+k)+k by dsimp [a];omega,Nat.add_mod_right,Nat.add_mod_right,Nat.mod_eq_of_lt hd]
  rw [left]
  constructor
  · intro h;exact Nat.ModEq.add_right_cancel' a (h.trans right.symm)
  · intro h;exact (show (j+a)%k=((q+k-2+d)+a)%k from Nat.ModEq.add_right a h).trans right
end Overlap521
end PEqualNP.Outside.L_meta_25521_aux

namespace PEqualNP.Outside.L_meta_25521_aux.Bdy

private theorem dec521 {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    decide p = decide q := Bool.eq_iff_iff.mpr (by simpa using h)

private theorem flipWindow {k w : Nat} (q z : Int) (lo : q-(k:Int)<z) (hi : z<q+(k:Int)) :
    bits k (flipped k w q) z = xor (bits k w z) (decide (z=q)) := by
  rw [flippedBit]
  have comp : idx k q=idx k z ↔ z=q := by
    constructor
    · intro e
      rcases lt_trichotomy z q with h|h|h
      · exact False.elim (idxSep lo h e)
      · exact h
      · exact False.elim (idxSep (by omega : z-(k:Int)<q) h e.symm)
    · rintro rfl
      rfl
  rw [dec521 comp]

private theorem linearFlip {k u w : Nat} (hk : 5≤k) (hw : w<2^k) (q z : Int)
    (lo : q-(k:Int)+2<z) (hi : z<q+(k:Int)) :
    y521 k u (flipped k w q) z = xor (y521 k u w z) (decide (q≤z ∧ z≤q+2)) := by
  have hf := flippedLt (by omega) hw q
  have toggle (p : Int) (l : z-1≤p) (h : p≤z+1) :
      bits k (start k u (flipped k w q)) p =
        xor (bits k (start k u w) p) (decide (p=q+1)) := by
    simp only [start,bitsXor,bitsRot (show 1<k by omega) hw,bitsRot (show 1<k by omega) hf]
    rw [flipWindow q _ (by omega) (by omega),dec521 (show p-((1:Nat):Int)=q ↔ p=q+1 by omega)]
    exact (show ∀ a b c : Bool,xor (xor a c) b=xor (xor a b) c by decide) _ _ _
  unfold y521 lin
  rw [toggle z (by omega) (by omega),toggle (z-1) (by omega) (by omega),toggle (z+1) (by omega) (by omega)]
  have alg : ∀ a b c d e f : Bool,
    xor (xor (xor a d) (xor b e)) (xor c f) = xor (xor (xor a b) c) (xor (xor d e) f) := by decide
  rw [alg]
  congr 1
  by_cases e : z=q <;> by_cases f : z=q+1 <;> by_cases h : z=q+2 <;>
    simp_all [show z-1=q+1 ↔ z=q+2 by omega,show z+1=q+1 ↔ z=q by omega] <;> omega

private def mask521 (d : Nat) := decide (2≤d ∧ d≤4)
private def equation (a b : Bool) : Nat → Prop
  | 0 => a=true
  | 1 => a=b
  | 2 => a=b
  | 3 => b=true
  | 4 => False
  | _ => True

private theorem diffTable (d : Nat) (a b c w con : Bool) :
    (xor (xor (chi a b c) w) con =
      xor (xor (chi (xor a (mask521 d)) (xor b (mask521 (d+1))) (xor c (mask521 (d+2)))) (xor w (decide (d=2)))) con)
      ↔ equation b c d := by
  rcases d with _|(_|(_|(_|(_|d))))
  all_goals cases a <;> cases b <;> cases c <;> cases w <;> cases con <;> simp [mask521,equation,chi] <;> omega

theorem local521 {k u w c : Nat} (hk : 5≤k) (hw : w<2^k) (hu : u<2^k) (q : Int)
    (d : Nat) (hd : d<k) :
    bits k (first521 k u w c) (q-2+(d:Int)) =
      bits k (first521 k u (flipped k w q) c) (q-2+(d:Int)) ↔ Eq521 k u w q d := by
  let j := q-2+(d:Int)
  let f := flipped k w q
  have line (t : Nat) (ht : t≤2) :
      y521 k u f (j+(t:Int))=xor (y521 k u w (j+(t:Int))) (mask521 (d+t)) := by
    rw [show y521 k u f (j+(t:Int))=_ from linearFlip hk hw q _ (by dsimp [j];omega) (by dsimp [j];omega)]
    unfold mask521
    congr 2
    apply propext
    dsimp [j]
    omega
  have l0 := line 0 (by decide)
  have l1 := line 1 (by decide)
  have l2 := line 2 (by decide)
  norm_num at l0 l1 l2
  have key : bits k f j=xor (bits k w j) (decide (d=2)) := by
    rw [show bits k f j=_ from flipWindow q j (by dsimp [j];omega) (by dsimp [j];omega),
      dec521 (show j=q ↔ d=2 by dsimp [j];omega)]
  change bits k (first521 k u w c) j = bits k (first521 k u f c) j ↔ _
  simp only [first521,bitsXor,bitsMix (show 2≤k by omega) (startLt _ hu),mix]
  change (xor (xor (chi (y521 k u w j) (y521 k u w (j+1)) (y521 k u w (j+2))) _) _) =
    (xor (xor (chi (y521 k u f j) (y521 k u f (j+1)) (y521 k u f (j+2))) _) _) ↔ _
  rw [l0,l1,l2,key,diffTable]
  rcases d with _|(_|(_|(_|(_|d)))) <;> simp only [Eq521,equation] <;> dsimp [j] <;> ring_nf

theorem point521 {k u w c : Nat} (hk : 5≤k) (hw : w<2^k) (hu : u<2^k) (q j : Int) :
    bits k (first521 k u w c) j = bits k (first521 k u (flipped k w q) c) j ↔
      Eq521 k u w q (idx k (j-(q-2))) := by
  let d := idx k (j-(q-2))
  have cast : (d:Int)=(j-(q-2))%(k:Int) := by
    unfold d idx
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have e : idx k (q-2+(d:Int))=idx k j := by
    unfold idx
    rw [cast,Int.add_emod_emod,show q-2+(j-(q-2))=j by omega]
  simpa only [bits,e] using local521 (c:=c) hk hw hu q d (idxlt (by omega) _)

end PEqualNP.Outside.L_meta_25521_aux.Bdy

namespace PEqualNP.Outside.L_meta_25521_aux.Bdy
open scoped Classical

def fail521 (k u w : Nat) (q : Int) : Nat → Bool
  | 0 => !(y521 k u w (q-1))
  | 1 => xor (y521 k u w q) (y521 k u w (q+1))
  | 2 => xor (y521 k u w (q+1)) (y521 k u w (q+2))
  | 3 => !(y521 k u w (q+3))
  | _ => true

lemma fail521Eq {k u w d : Nat} (q : Int) (hd : d<4) :
    fail521 k u w q d = false ↔ Eq521 k u w q d := by
  interval_cases d <;> simp [fail521,Eq521]

private lemma seedBit521 {k w : Nat} (hk : 2≤k) (hw : w<2^k) (u : Nat) (j : Int) :
    bits k (start k u w) j = xor (bits k w (j-1)) (bits k u j) := by
  simp [start,bitsXor,bitsRot (show 1<k by omega) hw]

lemma ySame521 {k w : Nat} (hk : 2≤k) (hw : w<2^k) (u : Nat) {p j : Int}
    (lo : p-(k:Int)<j-2) (hi : j<p) :
    y521 k u (flipped k w p) j = y521 k u w j := by
  apply linAgree
  intro z hz hz'
  rw [seedBit521 hk (flippedLt (by omega) hw p),seedBit521 hk hw,
    flipAway (by omega : p-(k:Int)<z-1) (by omega : z-1<p)]

lemma yToggle521 {k w : Nat} (hk : 3≤k) (hw : w<2^k) (u : Nat) (p : Int) :
    y521 k u (flipped k w p) p = !(y521 k u w p) := by
  have hb := flippedLt (by omega) hw p
  simp only [y521,lin,seedBit521 (by omega : 2≤k) hb,seedBit521 (by omega : 2≤k) hw]
  rw [flipAway (by omega : p-(k:Int)<p-1) (by omega : p-1<p),
    flipAway (by omega : p-(k:Int)<p-1-1) (by omega : p-1-1<p),
    show p+1-1=p by omega,flipAtKey]
  simp

lemma flipLaw521 (k u : Nat) (hk : 8≤k) (q : Int) (t : Nat) (ht : t<4) :
    ∃ f : Fin (2^k) → Fin (2^k), (∀ a, f (f a)=a) ∧
      (∀ a, fail521 k u (f a).val q t = !(fail521 k u a.val q t)) ∧
      (∀ a j, j<t → fail521 k u (f a).val q j = fail521 k u a.val q j) := by
  let f (p : Int) (a : Fin (2^k)) : Fin (2^k) :=
    ⟨flipped k a.val p,flippedLt (by omega) a.isLt p⟩
  have invol (p : Int) (a : Fin (2^k)) : f p (f p a)=a := Fin.ext (by simp [f,flipped])
  have fixed (a : Fin (2^k)) (p j : Int) (h : p-(k:Int)<j-2) (h' : j<p) :
      y521 k u (f p a).val j = y521 k u a.val j := ySame521 (by omega) a.isLt u h h'
  have toggle (a : Fin (2^k)) (p : Int) :
      y521 k u (f p a).val p = !(y521 k u a.val p) := yToggle521 (by omega) a.isLt u p
  have casesT : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases casesT with rfl | rfl | rfl | rfl
  · refine ⟨f (q-1),invol _,fun a => ?_,fun _ _ h => (by omega : False).elim⟩
    simp only [fail521,toggle]
  · refine ⟨f (q+1),invol _,fun a => ?_,?_⟩
    · simp [fail521,fixed a (q+1) q (by omega) (by omega),toggle]
    · intro a j hj
      interval_cases j
      simp only [fail521,fixed a (q+1) (q-1) (by omega) (by omega)]
  · refine ⟨f (q+2),invol _,fun a => ?_,?_⟩
    · simp [fail521,fixed a (q+2) (q+1) (by omega) (by omega),toggle]
    · intro a j hj
      interval_cases j <;> simp only [fail521] <;> repeat' rw [fixed a (q+2) _ (by omega) (by omega)]
  · refine ⟨f (q+3),invol _,fun a => ?_,?_⟩
    · simp only [fail521,toggle]
    · intro a j hj
      interval_cases j <;> simp only [fail521] <;> repeat' rw [fixed a (q+3) _ (by omega) (by omega)]

theorem prefix521 (k u : Nat) (q : Int) (d : Nat) (hk : 8≤k) (hd : d≤4) :
    (Finset.univ.filter (fun w : Fin (2^k) => ∀ j : Fin d, Eq521 k u w.val q j.val)).card = 2^(k-d) := by
  have h := PEqualNP.Outside.L_meta_25521_aux.halves k d (by omega)
    (fun (w : Fin (2^k)) t => fail521 k u w.val q t) (Fintype.card_fin _)
    (fun t ht => flipLaw521 k u hk q t (by omega))
  rw [← h]
  congr 1
  ext w
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq]
  exact forall_congr' (fun j => (fail521Eq q (by have := j.isLt; omega)).symm)

theorem listFin521 (N : Nat) (p : Nat → Bool) :
    ((List.range N).filter p).length = (Finset.univ.filter (fun w : Fin N => p w.val)).card := by
  have eqr : (List.range N).toFinset = Finset.range N := by ext; simp
  have mem := (List.nodup_range (n:=N)).card_eq_countP (P:=fun i => p i = true)
  rw [eqr] at mem
  simp only [Bool.decide_eq_true] at mem
  rw [← List.countP_eq_length_filter, ← mem]
  apply Finset.card_bij (fun i hi => (⟨i,Finset.mem_range.mp (Finset.mem_filter.mp hi).1⟩ : Fin N))
  · intro i hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  · intro i hi j hj h; exact congrArg Fin.val h
  · intro b hb
    refine ⟨b.val,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr b.isLt,(Finset.mem_filter.mp hb).2⟩,rfl⟩

end PEqualNP.Outside.L_meta_25521_aux.Bdy

namespace PEqualNP.Outside.L_meta_25521_aux.Bdy

def agrees521 (k u c q left len w : Nat) : Bool :=
  (List.range len).all (fun j => (first521 k u w c).testBit ((left+j)%k) ==
    (first521 k u (w ^^^ (1 <<< q)) c).testBit ((left+j)%k))

private lemma idxSmall521 {k a : Nat} (ha : a<k) : idx k (a:Int)=a := by
  unfold idx
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  rfl

theorem window521 {k r e u i c w : Nat} (hr : 4≤r) (hk : 5≤k) (width : k+3+e=5*r)
    (point : ∀ q z : Int, bits k (first521 k u w c) z =
      bits k (first521 k u (flipped k w q) c) z ↔ Eq521 k u w q (idx k (z-(q-2)))) :
    let q := (i+(2*r)*k+2-2*r)%k
    let left := (i+r*k+1-r)%k
    agrees521 k u c q left (4*r-3) w = true ↔ ∀ d, d<5 → d≤e → Eq521 k u w q d := by
  let q := (i+(2*r)*k+2-2*r)%k
  let left := (i+r*k+1-r)%k
  have hq : q<k := Nat.mod_lt _ (by omega)
  let z (j : Nat) := (left+j)%k
  let t (j : Nat) := idx k ((z j:Int)-((q:Int)-2))
  have single (j : Nat) : ((first521 k u w c).testBit (z j) ==
      (first521 k u (w ^^^ (1 <<< q)) c).testBit (z j)) = true ↔ Eq521 k u w q (t j) := by
    have hz : idx k (z j:Int)=z j := idxSmall521 (a:=z j) (Nat.mod_lt _ (by omega))
    simpa only [bits,hz,flipped,idxSmall521 hq,beq_iff_eq] using point q (z j)
  have hit (d : Nat) (hd : d<5) : (∃ j<4*r-3, t j=d) ↔ d≤e := by
    dsimp only [t,z]
    simp_rw [Overlap521.inverse hk hq (by omega : d<k),Nat.mod_mod]
    exact Overlap521.hit hr hk width hd
  change (List.range (4*r-3)).all _ = true ↔ ∀ d, d<5 → d≤e → Eq521 k u w q d
  simp only [List.all_eq_true,List.mem_range]
  constructor
  · intro h d hd he
    obtain ⟨j,hj,eq⟩ := (hit d hd).mpr he
    exact eq ▸ (single j).mp (h j hj)
  · intro h j hj
    apply (single j).mpr
    by_cases hlt : t j<5
    · exact h _ hlt ((hit _ hlt).mp ⟨j,hj,rfl⟩)
    · have he : t j=t j-5+5 := by omega
      rw [he]
      trivial

end PEqualNP.Outside.L_meta_25521_aux.Bdy

namespace PEqualNP.Outside.L_meta_25521_aux.Bdy
open scoped Classical

theorem result521 {k r e : Nat} (hr : 4≤r) (hk : 5≤k) (width : k+3+e=5*r)
    (u i c : Nat) (hu : u<2^k) :
    let q := (i+(2*r)*k+2-2*r)%k
    let left := (i+r*k+1-r)%k
    ((List.range (2^k)).filter (agrees521 k u c q left (4*r-3))).length =
      if e<4 then 2^(k-(e+1)) else 0 := by
  let q := (i+(2*r)*k+2-2*r)%k
  let left := (i+r*k+1-r)%k
  let p := agrees521 k u c q left (4*r-3)
  change ((List.range (2^k)).filter p).length = _
  rw [listFin521]
  have spec (w : Fin (2^k)) : p w.val=true ↔ ∀ d, d<5 → d≤e → Eq521 k u w.val q d :=
    window521 hr hk width (fun z j => point521 hk w.isLt hu z j)
  by_cases h : e<4
  · rw [if_pos h,←prefix521 k u q (e+1) (by omega) (by omega)]
    congr 1
    ext w
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,spec]
    exact ⟨fun H d => H d.val (by have := d.isLt; omega) (by have := d.isLt; omega),
      fun H d _ hd => H ⟨d,by omega⟩⟩
  · rw [if_neg h,Finset.card_eq_zero,Finset.filter_eq_empty_iff]
    intro w _ hp
    exact ((spec w).mp hp 4 (by decide) (by omega))

end PEqualNP.Outside.L_meta_25521_aux.Bdy

theorem PEqualNP.Outside.L_meta_25521 :
∀ (k r e : Nat), 4 ≤ r → 5 ≤ k → k + 3 + e = 5 * r →
  ∀ (u i : Nat) (constant : Fin (2 ^ k)), u < 2 ^ k → i < k →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc b =>
      acc ||| ((xor (word.testBit b)
        (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0
  let first := fun (key : Nat) =>
    let x := rot 1 key ^^^ u
    step (x ^^^ rot 1 x ^^^ rot (k - 1) x) ^^^ key ^^^ constant.val
  let keyBit := (i + (2 * r) * k + 2 - 2 * r) % k
  let left := (i + r * k + 1 - r) % k
  let agrees := fun (w : Nat) =>
    let before := first w
    let after := first (w ^^^ (1 <<< keyBit))
    (List.range (4 * r - 3)).all (fun j =>
      before.testBit ((left + j) % k) == after.testBit ((left + j) % k))
  ((List.range (2 ^ k)).filter agrees).length =
    (if e < 4 then 2 ^ (k - (e + 1)) else 0) := by
  intro k r e hr hk width u i c hu _
  exact PEqualNP.Outside.L_meta_25521_aux.Bdy.result521 hr hk width u i c.val hu
