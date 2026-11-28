import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_33620

namespace PEqualNP.Outside.L_meta_36441

open PEqualNP.Outside.L_meta_33620_aux

def strips (h : Nat) := Finset.range (2^(h+2))

def zero (h u : Nat) := (Finset.range h).filter (fun j => Fbit u j)

def replies (h : Nat) := (strips h).image (zero h)

def fiber (h : Nat) (z : Finset Nat) := {u : Nat | u ∈ strips h ∧ zero h u = z}

def tail (h n : Nat) (p : Nat → Bool) (u : Nat) :=
  (Finset.range n).filter (fun j => FbitH p u (h-n+j))

def tap (k start x j back : Nat) := x.testBit ((start+j+k-back) % k)

def pulse (k start : Nat) (col : Bool) (x j : Nat) :=
  if col then xor (tap k start x j 1) (xor (tap k start x j 3) (tap k start x j 5))
  else xor (tap k start x j 0) (xor (tap k start x j 1) (tap k start x j 2))

def works (h k start r c : Nat) (B : Finset Nat) :=
  B ⊆ Finset.range (2^k) ∧ ∀ z ∈ replies h, ∀ w ∈ replies h, ∃ x ∈ B,
    Set.InjOn (tail h r (pulse k start false x)) (fiber h z) ∧
      Set.InjOn (tail h c (pulse k start true x)) (fiber h w)

lemma badFiber (h : Nat) (hh : 0 < h) (p : Nat → Bool) :
    ∃ z ∈ replies h, ¬ Set.InjOn (tail h h p) (fiber h z) := by
  classical
  by_contra hn
  have hg (z) (hz : z ∈ replies h) : Set.InjOn (tail h h p) (fiber h z) := by
    by_contra hbad
    exact hn ⟨z,hz,hbad⟩
  have hi : Set.InjOn (phi h p) (↑(strips h) : Set Nat) := by
    intro u hu v hv e
    apply hg (zero h u) (Finset.mem_image.mpr ⟨u,hu,rfl⟩)
    · exact ⟨hu,rfl⟩
    · exact ⟨hv,(congrArg Prod.fst e).symm⟩
    · simpa only [tail,Nat.sub_self,Nat.zero_add,phi] using congrArg Prod.snd e
  have hc := phi_card_le h hh p
  unfold strips at hi
  rw [Finset.card_image_of_injOn hi, Finset.card_range] at hc
  have hp : 0 < 2^(h+2) := by positivity
  omega

lemma lower (h k start : Nat) (hh : 0 < h) (B : Finset Nat)
    (hw : works h k start h h B) : 3 ≤ B.card := by
  classical
  have base : zero h 0 ∈ replies h :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by positivity),rfl⟩
  obtain ⟨x,hx,_,_⟩ := hw.2 _ base _ base
  obtain ⟨z,hz,hbadx⟩ := badFiber h hh (pulse k start false x)
  obtain ⟨y,hy,gry,_⟩ := hw.2 z hz _ base
  have hxy : x ≠ y := by rintro rfl; exact hbadx gry
  obtain ⟨w,hw',hbady⟩ := badFiber h hh (pulse k start true y)
  obtain ⟨t,ht,grt,gct⟩ := hw.2 z hz w hw'
  have hxt : x ≠ t := by rintro rfl; exact hbadx grt
  have hyt : y ≠ t := by rintro rfl; exact hbady gct
  have hs : ({x,y,t} : Finset Nat) ⊆ B := by
    intro j hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> assumption
  simpa [hxy,hxt,hyt] using Finset.card_le_card hs

def sig (n u : Nat) : Nat :=
  (u ^^^ ((u >>> 2) ^^^ ((u >>> 1) &&& (u >>> 2)))) % 2^n

def recover : Nat → Nat → Nat → Nat
  | 0, _, t => t
  | n+1, z, t =>
    let a := recover n (z/2) t
    2*a + (xor (z.testBit 0) (!(a.testBit 0) && a.testBit 1)).toNat

def decode (n m z out : Nat) :=
  let a := recover n z 0
  let b := recover n z 1
  let c := recover n z 2
  if sig n (a ^^^ m) = out then a
  else if sig n (b ^^^ m) = out then b
  else if sig n (c ^^^ m) = out then c
  else recover n z 3

def Cert (n m : Nat) (g : Nat → Prop) :=
  ∀ u : Fin (2^(n+2)), g (sig n u) →
    decode n m (sig n u) (sig n (u.val ^^^ m)) = u.val

def seeds : Finset Nat := {146,152,184}

def rowMask (a : Nat) := (a >>> 4) ^^^ ((a >>> 3) ^^^ (a >>> 2))

def colMask (a : Nat) := ((a >>> 4) ^^^ ((a >>> 2) ^^^ a)) % 64

def rowOK (a z : Nat) : Prop :=
  if a = 146 then 4 ≤ z else if a = 152 then z < 4 ∨ 8 ≤ z else z < 24

def colOK (a z : Nat) : Prop :=
  if a = 146 then 4 ≤ z else if a = 152 then z < 8 else z < 4 ∨ 8 ≤ z

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
lemma rowCert (a : Nat) (ha : a ∈ seeds) : Cert 5 (rowMask a) (rowOK a) := by
  simp only [seeds,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl <;> unfold Cert rowOK <;> decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
lemma colCert (a : Nat) (ha : a ∈ seeds) : Cert 4 (colMask a) (colOK a) := by
  simp only [seeds,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl <;> unfold Cert colOK <;> decide

lemma pick (z w : Nat) : ∃ a ∈ seeds, rowOK a z ∧ colOK a w := by
  by_cases h : rowOK 146 z ∧ colOK 146 w
  · exact ⟨146,by decide,h⟩
  by_cases h' : rowOK 152 z ∧ colOK 152 w
  · exact ⟨152,by decide,h'⟩
  refine ⟨184,by decide,?_⟩
  simp [rowOK,colOK] at *
  omega

def baseAddr (h k start : Nat) := start+(h-5)+k-4

def liftKey (h k start a : Nat) :=
  packBits (fun j => a.testBit ((j+(k-baseAddr h k start % k)) % k)) k

lemma liftBit (h k start a t : Nat) (ht : t < k) :
    (liftKey h k start a).testBit ((baseAddr h k start+t) % k) = a.testBit t := by
  let base := baseAddr h k start
  have hk : 0 < k := by omega
  have hb : base % k < k := Nat.mod_lt _ hk
  have addr : ((base+t) % k+(k-base % k)) % k = t := calc
    _ = ((base % k + t) % k + (k - base % k)) % k := by rw [Nat.mod_add_mod base k t]
    _ = (base % k + t + (k - base % k)) % k := Nat.mod_add_mod _ _ _
    _ = (t + k) % k := by congr 1; omega
    _ = t := by simp [Nat.mod_eq_of_lt ht]
  unfold liftKey
  rw [packBits_testBit_of_lt (Nat.mod_lt _ hk)]
  exact congrArg a.testBit addr

lemma rowPulse (h k start a i : Nat) (hh : 5 ≤ h) (hk : h+6 ≤ k) (hi : i < 7) :
    pulse k start false (liftKey h k start a) (h-5+i) = (rowMask a).testBit i := by
  have eqtap (b : Nat) (hb : b ≤ 4) :
      tap k start (liftKey h k start a) (h-5+i) b = a.testBit (4+i-b) := by
    unfold tap
    rw [show start+(h-5+i)+k-b = baseAddr h k start+(4+i-b) by unfold baseAddr; omega]
    exact liftBit h k start a _ (by omega)
  simp only [pulse,Bool.false_eq_true,↓reduceIte,eqtap 0 (by decide),eqtap 1 (by decide),
    eqtap 2 (by decide),rowMask,Nat.testBit_xor,Nat.testBit_shiftRight,Nat.sub_zero,
    show 4+i-1 = 3+i by omega, show 4+i-2 = 2+i by omega]

lemma colPulse (h k start a i : Nat) (hh : 5 ≤ h) (hk : h+6 ≤ k) (hi : i < 6) :
    pulse k start true (liftKey h k start a) (h-4+i) = (colMask a).testBit i := by
  have eqtap (b : Nat) (hb : b ≤ 5) :
      tap k start (liftKey h k start a) (h-4+i) b = a.testBit (5+i-b) := by
    unfold tap
    rw [show start+(h-4+i)+k-b = baseAddr h k start+(5+i-b) by unfold baseAddr; omega]
    exact liftBit h k start a _ (by omega)
  simp only [pulse,↓reduceIte,eqtap 1 (by decide),eqtap 3 (by decide),eqtap 5 (by decide),
    colMask,show (64 : Nat) = 2^6 by decide,Nat.testBit_mod_two_pow,decide_eq_true hi,
    Bool.true_and,Nat.testBit_xor,Nat.testBit_shiftRight,show 5+i-1 = 4+i by omega,
    show 5+i-3 = 2+i by omega,show 5+i-5 = i by omega]

lemma seedSmall (a : Nat) (ha : a ∈ seeds) : a < 2^11 := by
  simp only [seeds,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl <;> decide

lemma keyCard (h k start : Nat) (hk : 11 ≤ k) :
    (seeds.image (liftKey h k start)).card = 3 := by
  have hinj : Set.InjOn (liftKey h k start) (↑seeds : Set Nat) := by
    intro a ha b hb he
    apply eq_of_testBit_lt (seedSmall a ha) (seedSmall b hb)
    intro t ht
    have htk : t < k := by omega
    rw [← liftBit h k start a t htk, he, liftBit h k start b t htk]
  rw [Finset.card_image_of_injOn hinj]
  decide

def win (n o u : Nat) := (u >>> o) % 2^(n+2)

def viewSig (n o : Nat) (z : Finset Nat) := packBits (fun j => decide (o+j ∈ z)) n

lemma winLt (n o u : Nat) : win n o u < 2^(n+2) := Nat.mod_lt _ (by positivity)

lemma sigLt (n u : Nat) : sig n u < 2^n := Nat.mod_lt _ (by positivity)

lemma winBit (n o u i : Nat) (hi : i < n+2) :
    (win n o u).testBit i = u.testBit (o+i) := by
  simp [win,Nat.testBit_mod_two_pow,hi,Nat.testBit_shiftRight]

lemma sigBit (n u i : Nat) (hi : i < n) : (sig n u).testBit i = Fbit u i := by
  simp only [sig,Nat.testBit_mod_two_pow,decide_eq_true hi,Bool.true_and,Nat.testBit_xor,
    Nat.testBit_and,Nat.testBit_shiftRight,show 1+i=i+1 by omega,show 2+i=i+2 by omega,
    Fbit,polar]
  cases u.testBit i <;> cases u.testBit (i+1) <;> cases u.testBit (i+2) <;> rfl

lemma zeroBit (h u j : Nat) (hj : j < h) : decide (j ∈ zero h u) = Fbit u j := by
  simp [zero,hj]

lemma tailBitAt (h n : Nat) (p : Nat → Bool) (u j : Nat) (hj : j < n) :
    decide (j ∈ tail h n p u) = FbitH p u (h-n+j) := by
  simp [tail,hj]

lemma sigZero (h n o u : Nat) (hn : o+n ≤ h) :
    sig n (win n o u) = viewSig n o (zero h u) := by
  apply eq_of_testBit_lt (sigLt _ _) (packBits_lt _ _)
  intro j hj
  rw [sigBit _ _ _ hj,packBits_testBit_of_lt hj,zeroBit h u _ (by omega)]
  simp only [Fbit,winBit n o u j (by omega),winBit n o u (j+1) (by omega),
    winBit n o u (j+2) (by omega),Nat.add_assoc]

lemma sigTail (h n : Nat) (p : Nat → Bool) (m u : Nat)
    (hp : ∀ i < n+2, p (h-n+i) = m.testBit i) :
    sig n (win n (h-n) u ^^^ m) = viewSig n 0 (tail h n p u) := by
  apply eq_of_testBit_lt (sigLt _ _) (packBits_lt _ _)
  intro j hj
  rw [sigBit _ _ _ hj,packBits_testBit_of_lt hj,Nat.zero_add,tailBitAt _ _ _ _ _ hj]
  simp only [Fbit,FbitH,Nat.testBit_xor,winBit n (h-n) u j (by omega),
    winBit n (h-n) u (j+1) (by omega),winBit n (h-n) u (j+2) (by omega),Nat.add_assoc,
    hp j (by omega),hp (j+1) (by omega),hp (j+2) (by omega)]

lemma fiberUnique (u v : Nat) : ∀ h : Nat, (∀ j < h, Fbit u j = Fbit v j) →
    u.testBit h = v.testBit h → u.testBit (h+1) = v.testBit (h+1) →
    ∀ j < h+2, u.testBit j = v.testBit j := by
  intro h
  induction h with
  | zero =>
    intro _ e0 e1 j hj
    rcases (show j=0 ∨ j=1 by omega) with rfl | rfl <;> assumption
  | succ h ih =>
    intro he e1 e2 j hj
    have e0 : u.testBit h = v.testBit h := by
      have e := he h (by omega)
      unfold Fbit at e
      rw [e1,e2] at e
      exact allOnes_same_zero _ _ _ _ e
    by_cases hj' : j < h+2
    · exact ih (fun i hi => he i (by omega)) e0 e1 j hj'
    · obtain rfl : j = h+2 := by omega
      exact e2

lemma completeWindow (h n : Nat) (hn : n ≤ h) (z : Finset Nat) (u v : Nat)
    (hu : u ∈ fiber h z) (hv : v ∈ fiber h z)
    (e : win n (h-n) u = win n (h-n) v) : u = v := by
  have ez : zero h u = zero h v := hu.2.trans hv.2.symm
  have he (j : Nat) (hj : j < h) : Fbit u j = Fbit v j := by
    rw [← zeroBit h u j hj,ez,zeroBit h v j hj]
  have hw (i : Nat) (hi : i < n+2) :
      u.testBit (h-n+i) = v.testBit (h-n+i) := by
    rw [← winBit n (h-n) u i hi,e,winBit n (h-n) v i hi]
  apply eq_of_testBit_lt (Finset.mem_range.mp hu.1) (Finset.mem_range.mp hv.1)
  apply fiberUnique u v h he
  · simpa only [show h-n+n=h by omega] using hw n (by omega)
  · simpa only [show h-n+(n+1)=h+1 by omega] using hw (n+1) (by omega)

lemma tailInj (h n : Nat) (hn : n ≤ h) (z : Finset Nat) (p : Nat → Bool)
    (m : Nat) (g : Nat → Prop) (cert : Cert n m g) (hg : g (viewSig n (h-n) z))
    (hp : ∀ i < n+2, p (h-n+i) = m.testBit i) :
    Set.InjOn (tail h n p) (fiber h z) := by
  intro u hu v hv eqt
  have cz (t : Nat) (ht : t ∈ fiber h z) : sig n (win n (h-n) t) = viewSig n (h-n) z :=
    (sigZero h n (h-n) t (by omega)).trans (congrArg (viewSig n (h-n)) ht.2)
  have D (t : Nat) (ht : t ∈ fiber h z) :
      decode n m (viewSig n (h-n) z) (viewSig n 0 (tail h n p t)) = win n (h-n) t := by
    rw [← cz t ht, ← sigTail h n p m t hp]
    apply cert ⟨_,winLt _ _ _⟩
    change g (sig n (win n (h-n) t))
    rwa [cz t ht]
  apply completeWindow h n hn z u v hu hv
  have du := D u hu
  rw [eqt] at du
  exact du.symm.trans (D v hv)

lemma upper (h k start : Nat) (hh : 5 ≤ h) (hk : h+6 ≤ k) :
    ∃ B, B.card = 3 ∧ works h k start 5 4 B := by
  refine ⟨seeds.image (liftKey h k start),keyCard h k start (by omega),?_⟩
  constructor
  · intro x hx
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (packBits_lt _ _)
  · intro z _ w _
    obtain ⟨a,ha,hr,hc⟩ := pick (viewSig 5 (h-5) z) (viewSig 4 (h-4) w)
    refine ⟨liftKey h k start a,Finset.mem_image.mpr ⟨a,ha,rfl⟩,?_,?_⟩
    · exact tailInj h 5 hh z _ (rowMask a) (rowOK a) (rowCert a ha) hr
        (fun i hi => rowPulse h k start a i hh hk hi)
    · exact tailInj h 4 (by omega) w _ (colMask a) (colOK a) (colCert a ha) hc
        (fun i hi => colPulse h k start a i hh hk hi)

lemma main (h k start : Nat) (hh : 5 ≤ h) (hk : h+6 ≤ k) :
    (∃ B : Finset Nat, B.card = 3 ∧ works h k start 5 4 B) ∧
      ∀ B, works h k start h h B → 3 ≤ B.card :=
  ⟨upper h k start hh hk,lower h k start (by omega)⟩

end PEqualNP.Outside.L_meta_36441

theorem PEqualNP.Outside.L_meta_36441 : (∀ (h k start : Nat), 5 ≤ h → h+6 ≤ k →
  let strips := Finset.range (2^(h+2))
  let keys := Finset.range (2^k)
  let tap := fun (x j back : Nat) => x.testBit ((start+j+k-back) % k)
  let pulse := fun (col : Bool) (x j : Nat) =>
    if col then xor (tap x j 1) (xor (tap x j 3) (tap x j 5))
    else xor (tap x j 0) (xor (tap x j 1) (tap x j 2))
  let chi := fun (bits : Nat → Bool) (j : Nat) =>
    xor (bits j) (!(bits (j+1)) && bits (j+2))
  let zero := fun u : Nat =>
    (Finset.range h).filter (fun j => chi (fun i => u.testBit i) j)
  let replies := strips.image zero
  let fiber := fun (z : Finset Nat) => {u : Nat | u ∈ strips ∧ zero u = z}
  let tail := fun (col : Bool) (x len u : Nat) =>
    let bits := fun i : Nat => xor (u.testBit i) (pulse col x i)
    (Finset.range len).filter (fun j => chi bits (h-len+j))
  let works := fun (r c : Nat) (B : Finset Nat) =>
    B ⊆ keys ∧ ∀ z ∈ replies, ∀ w ∈ replies, ∃ x ∈ B,
      Set.InjOn (tail false x r) (fiber z) ∧ Set.InjOn (tail true x c) (fiber w)
  (∃ B, B.card = 3 ∧ works 5 4 B) ∧ ∀ B, works h h B → 3 ≤ B.card) := by
  intro h k start hh hk
  exact PEqualNP.Outside.L_meta_36441.main h k start hh hk
