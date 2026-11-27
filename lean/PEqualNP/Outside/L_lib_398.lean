import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_398

def Mass (w : ℕ) (rows : ℕ → ℕ → Bool) (h seed tail : ℕ) : ℕ :=
  ((List.range (2^(w+h))).filter (fun bits =>
      bits % (2^w) == seed && (bits >>> h) % (2^w) == tail &&
      (List.range h).all (fun i => rows i ((bits >>> i) % (2*(2^w)))))).length

def Cyclic (w : ℕ) (left right : ℕ → ℕ → Bool) : ℕ :=
  let L := 2*w+2
  let n := L+w
  ((List.range (2^n)).filter (fun word => (List.range n).all (fun site =>
    let pat := (List.range (w+1)).foldl (fun (acc bit : Nat) =>
      acc ||| ((word.testBit ((site+bit)%n)).toNat <<< bit)) 0
    if site < L then left site pat else right (site-L) pat))).length

theorem messageCount {d S : ℕ} (send : (Fin d → Bool) → Fin S)
    (answer : Fin S → Fin d → Bool)
    (decode : (Fin d → Bool) → Fin d → ℕ)
    (val : ∀ x i, decode x i = 2+(x i).toNat)
    (h : ∀ x i, answer (send x) i = (decode x i).testBit 0) : 2^d ≤ S := by
  have correct (x : Fin d → Bool) (i : Fin d) : answer (send x) i = x i := by
    rw [h,val]; cases x i <;> decide
  have inj : Function.Injective send := by
    intro x y hxy
    funext i
    rw [←correct x i, hxy, correct]
  simpa [Fintype.card_fun] using Fintype.card_le_of_injective send inj

theorem foldPairBound (D : ℕ) (hd : 0 < D) (p : ℕ → ℕ → Bool)
    (bound : ∀ s < D, ((Finset.range D).filter (fun t => p s t = true)).card ≤ 3) :
    ((List.range (D*D)).filter (fun i => p (i%D) (i/D))).length ≤ 3*D := by
  classical
  let pairs := (Finset.range (D*D)).filter (fun i => p (i%D) (i/D) = true)
  have lengthEq : ((List.range (D*D)).filter (fun i => p (i%D) (i/D))).length = pairs.card := by
    rw [←List.toFinset_card_of_nodup (List.nodup_range.filter _)]
    congr 1
    ext i
    simp [pairs]
  rw [lengthEq, Finset.card_eq_sum_card_fiberwise (f := fun i => i%D) (t := Finset.range D)
    (fun i _ => Finset.mem_range.mpr (Nat.mod_lt _ hd))]
  calc
    _ ≤ ∑ _i ∈ Finset.range D, 3 := by
      apply Finset.sum_le_sum
      intro s hs
      apply le_trans _ (bound s (Finset.mem_range.mp hs))
      apply Finset.card_le_card_of_injOn (fun i : ℕ => i / D)
      · intro i hi
        obtain ⟨hi, hmod⟩ := Finset.mem_filter.mp hi
        obtain ⟨hi, hp⟩ := Finset.mem_filter.mp hi
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
        · exact (Nat.div_lt_iff_lt_mul hd).mpr (Finset.mem_range.mp hi)
        · simpa [hmod] using hp
      · intro i hi j hj heq
        have hi' := (Finset.mem_filter.mp hi).2
        have hj' := (Finset.mem_filter.mp hj).2
        change i / D = j / D at heq
        have a := Nat.mod_add_div i D
        have b := Nat.mod_add_div j D
        rw [hi', heq] at a
        rw [hj'] at b
        omega
    _ = _ := by simp [Nat.mul_comm]



def closeProbe (w : ℕ) (q : Fin (2^w)) (_i pat : ℕ) : Bool :=
  pat.testBit 0 && (pat.testBit w == q.val.testBit _i)

private def closePat (w len word site : ℕ) : ℕ :=
  (List.range (w+1)).foldl (fun (acc bit : Nat) =>
    acc ||| ((word.testBit ((site+bit)%len)).toNat <<< bit)) 0
private theorem closeFold (g : ℕ → Bool) (n j : ℕ) :
    ((List.range n).foldl (fun acc i => acc ||| ((g i).toNat <<< i)) 0).testBit j =
      (decide (j < n) && g j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,Nat.testBit_or,ih]
    rcases lt_trichotomy j n with h|h|h
    · cases g n <;> simp [h,Nat.shiftLeft_eq,show j < n+1 by omega,show n ≠ j by omega]
    · subst h; cases g j <;> simp [Nat.shiftLeft_eq]
    · cases g n <;> simp [Nat.shiftLeft_eq,show ¬ j < n+1 by omega,show ¬j<n by omega,show n ≠ j by omega]

private theorem closeLeft (w L site word : ℕ) (hsite : site < L) :
    closePat w (L+w) word site = (word >>> site) % (2*2^w) := by
  apply Nat.eq_of_testBit_eq
  intro i
  unfold closePat
  rw [closeFold,show 2*2^w=2^(w+1) by rw [pow_succ,Nat.mul_comm],
    Nat.testBit_mod_two_pow,Nat.testBit_shiftRight]
  by_cases h : i<w+1
  · rw [Nat.mod_eq_of_lt (by omega : site+i < L+w)]
  · simp [h]

private theorem closeEnd (w L word : ℕ) (q : Fin (2^w)) (i : ℕ) (hi : i < w) :
    closeProbe w q i (closePat w (L+w) word (L+i)) = true ↔
      word.testBit (L+i) = true ∧ word.testBit i = q.val.testBit i := by
  unfold closeProbe closePat
  rw [closeFold,closeFold]
  have hh : (L+i+w)%(L+w) = i := by
    rw [show L+i+w=i+(L+w) by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
  simp [hh,Nat.mod_eq_of_lt (by omega : L+i<L+w)]

private theorem closeBound (w x z : ℕ) (hz : z < 2^w) :
    x % (2^w) = z ↔ ∀ i < w, x.testBit i = z.testBit i := by
  constructor
  · intro h i hi
    simpa [Nat.testBit_mod_two_pow,hi] using congrArg (fun t : ℕ => t.testBit i) h
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow]
    by_cases he : i < w
    · simpa [he] using h i he
    · have big := Nat.testBit_lt_two_pow (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_of_not_gt he)))
      simpa [he] using big.symm

def closeCyclic (w L : ℕ) (left right : ℕ → ℕ → Bool) : ℕ :=
  ((List.range (2^(L+w))).filter (fun word => (List.range (L+w)).all (fun site =>
    let pat := closePat w (L+w) word site
    if site < L then left site pat else right (site-L) pat))).length
def closeMass (w : ℕ) (rows : ℕ → ℕ → Bool) (h seed tail : ℕ) : ℕ :=
  ((List.range (2^(w+h))).filter (fun bits =>
    bits % (2^w) == seed && (bits >>> h) % (2^w) == tail &&
    (List.range h).all (fun i => rows i ((bits >>> i) % (2*2^w))))).length

theorem probeEquality (w L : ℕ) (q : Fin (2^w)) (rows : ℕ → ℕ → Bool) :
    closeCyclic w L rows (closeProbe w q) = closeMass w rows L q.val (2^w-1) := by
  unfold closeMass closeCyclic
  rw [show w+L=L+w by omega]
  congr 1
  apply List.filter_congr
  intro word _h
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true,List.mem_range,Bool.and_eq_true,beq_iff_eq]
  have low := closeBound w word q.val q.isLt
  have top := closeBound w (word >>> L) (2^w-1) (by have := Nat.two_pow_pos w; omega)
  have htop : (word >>> L) % (2^w) = 2^w-1 ↔ ∀ i < w, word.testBit (L+i) = true := by
    rw [top]
    constructor
    · intro h i hi
      simpa [Nat.testBit_shiftRight,Nat.testBit_two_pow_sub_one,hi,Nat.add_comm] using h i hi
    · intro h i hi
      simpa [Nat.testBit_shiftRight,Nat.testBit_two_pow_sub_one,hi,Nat.add_comm] using h i hi
  constructor
  · intro h
    have both (i : ℕ) (hi : i<w) : word.testBit (L+i) = true ∧ word.testBit i = q.val.testBit i := by
      apply (closeEnd w L word q i hi).1
      simpa using h (L+i) (by omega)
    refine ⟨⟨low.2 (fun i hi => (both i hi).2),htop.2 (fun i hi => (both i hi).1)⟩,?_⟩
    intro i hi
    simpa [hi,closeLeft w L i word hi] using h i (by omega)
  · rintro ⟨⟨hseed,htail⟩,hl⟩ site hsite
    by_cases hi : site<L
    · simpa [hi,closeLeft w L site word hi] using hl site hi
    · have hev := (closeEnd w L word q (site-L) (by omega)).2
        ⟨(htop.1 htail) _ (by omega),(low.1 hseed) _ (by omega)⟩
      simpa [hi,show L + (site-L) = site by omega] using hev


theorem cycleProbeMass (w : ℕ) (q : Fin (2^w)) (rows : ℕ → ℕ → Bool) :
    Cyclic w rows (closeProbe w q) = Mass w rows (2*w+2) q.val (2^w-1) :=
  probeEquality w (2*w+2) q rows


def libEncode (w : ℕ) (data : Fin (2^w) → Bool) (i p : ℕ) : Bool :=
  if i=0 then !p.testBit w || data ⟨p % 2^w, Nat.mod_lt _ (by positivity)⟩
  else if i=1 then !p.testBit (w-1) || p.testBit w
  else if i=2 then p.testBit w == p.testBit (w-2)
  else if i<w+2 then p.testBit w == p.testBit (w-1)
  else !(p % 2^w == 2^w-1) || p.testBit w

def libGood (w : ℕ) (rows : ℕ → ℕ → Bool) (h bits : ℕ) : Prop :=
  ∀ i<h, rows i ((bits >>> i) % (2*2^w)) = true

def libMass (w : ℕ) (rows : ℕ → ℕ → Bool) (h seed tail : ℕ) :=
  ((List.range (2^(w+h))).filter (fun bits =>
    bits % 2^w == seed && (bits >>> h) % 2^w == tail &&
    (List.range h).all (fun i => rows i ((bits >>> i) % (2*2^w))))).length

theorem libWindow {v i p k : ℕ} (h : i+p ≤ k) :
    ((v % 2^k) >>> i) % 2^p = (v >>> i) % 2^p := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have eq : k = i+(k-i) := by omega
  have hk : 2^k = 2^i * 2^(k-i) := by conv_lhs => rw [eq, pow_add]
  rw [hk, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact pow_dvd_pow 2 (by omega)

theorem libGoodPrefix (w : ℕ) (rows : ℕ → ℕ → Bool) (h bits : ℕ) :
    libGood w rows (h+1) bits ↔ libGood w rows h (bits % 2^(w+h)) ∧
      rows h ((bits >>> h) % (2*2^w)) = true := by
  have neq : 2*2^w = 2^(w+1) := by rw [pow_succ]; omega
  have win (i : ℕ) (hi : i<h) : ((bits % 2^(w+h)) >>> i) % (2*2^w) =
      (bits >>> i) % (2*2^w) := by rw [neq]; exact libWindow (by omega)
  constructor
  · intro hx
    exact ⟨fun i hi => by rw [win i hi]; exact hx _ (by omega), hx h (by omega)⟩
  · intro ⟨hx,hl⟩ i hi
    by_cases e : i=h
    · simpa [e] using hl
    · have hh : i<h := by omega
      rw [← win i hh]
      exact hx i hh

open Classical

theorem libMassCard (w h s t : ℕ) (R : ℕ → ℕ → Bool) :
    libMass w R h s t = ((Finset.range (2^(w+h))).filter (fun v =>
      v % 2^w = s ∧ (v >>> h) % 2^w = t ∧ libGood w R h v)).card := by
  classical
  unfold libMass
  let p := fun v : ℕ => v % 2^w == s && (v >>> h) % 2^w == t &&
    (List.range h).all (fun i => R i ((v >>> i) % (2*2^w)))
  change ((List.range (2^(w+h))).filter p).length = _
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  apply congrArg Finset.card
  ext v
  rw [Finset.mem_filter]
  simp [p,libGood, List.all_eq_true, and_assoc]

private theorem libMassFiber (w h s t : ℕ) (R : ℕ → ℕ → Bool) (ht : t<2^w) :
    libMass w R h s t = ∑ x ∈ Finset.range (2^h), (if
        (x+t*2^h) % 2^w = s ∧ libGood w R h (x+t*2^h) then 1 else 0) := by
  classical
  rw [libMassCard]
  let D : ℕ := 2^w
  let B : ℕ := 2^h
  have hb : 0<B := by dsimp [B]; positivity
  have e : (Finset.range (2^(w+h))).filter (fun v => v%D=s ∧ (v>>>h)%D=t ∧ libGood w R h v) =
      ((Finset.range B).filter (fun x => (x+t*B)%D=s ∧ libGood w R h (x+t*B))).image (fun x => x+t*B) := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_range, Finset.mem_image,Nat.shiftRight_eq_div_pow]
    change (v<2^(w+h) ∧ v%D=s ∧ v/B%D=t ∧ libGood w R h v) ↔ _
    rw [pow_add]
    constructor
    · rintro ⟨hv,hs,hm,hg⟩
      have hv' : v/B < D := (Nat.div_lt_iff_lt_mul hb).mpr hv
      have hh : v/B=t := by rwa [Nat.mod_eq_of_lt hv'] at hm
      have fix : v%B+t*B = v := by simpa [hh,Nat.mul_comm] using Nat.mod_add_div v B
      exact ⟨v%B,⟨Nat.mod_lt _ hb,by simpa [fix] using And.intro hs hg⟩,fix⟩
    · rintro ⟨x,⟨hx,hs,hg⟩,rfl⟩
      have hd : (x+t*B)/B=t := by rw [Nat.add_mul_div_right _ _ hb,Nat.div_eq_of_lt hx,zero_add]
      have hg' : x+t*B < D*B := (Nat.div_lt_iff_lt_mul hb).mp (show (x+t*B)/B < D by simpa only [hd] using ht)
      exact ⟨hg',hs,by rw [hd,Nat.mod_eq_of_lt ht],hg⟩
  rw [e, Finset.card_image_of_injective _ (fun x y hxy => by simpa only [Nat.add_right_cancel_iff] using hxy)]
  simp [Finset.sum_boole, D, B]

theorem libStep (w h s t : ℕ) (R : ℕ → ℕ → Bool) (ht : t<2^w) :
    libMass w R (h+1) s t =
      (if R h (2*t)=true then libMass w R h s ((2*t)%2^w) else 0) +
      (if R h (2*t+1)=true then libMass w R h s ((2*t+1)%2^w) else 0) := by
  classical
  let B : ℕ := 2^h
  let D : ℕ := 2^w
  have hb : 0<B := by dsimp [B]; positivity
  have hd : 0<D := by dsimp [D]; positivity
  let term := fun (x z : ℕ) => if (x+z*B)%D=s ∧ libGood w R (h+1) (x+z*B) then 1 else 0
  have split (z : ℕ) (hz : z<2*D) : (∑ x ∈ Finset.range B, term x z) =
      if R h z=true then libMass w R h s (z%D) else 0 := by
    have point (x : ℕ) (hx : x<B) : term x z =
        (if R h z=true then (if (x+(z%D)*B)%D=s ∧ libGood w R h (x+(z%D)*B) then 1 else 0) else 0) := by
      have lt0 : x+(z%D)*B<D*B := by
        have v := Nat.mod_lt z hd
        have h' := Nat.mul_le_mul_right B (show z%D+1 ≤ D by omega)
        rw [Nat.succ_mul] at h';omega
      have low : (x+z*B) % (D*B) = x+(z%D)*B := by
        have ez : z%D + D*(z/D) = z := Nat.mod_add_div z D
        conv_lhs => rw [←ez]
        have eq : x+(z%D+D*(z/D))*B = (x+(z%D)*B)+(D*B)*(z/D) := by ring
        rw [eq,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt lt0]
      have seed : (x+z*B)%D = (x+(z%D)*B)%D := by
        rw [←low, Nat.mod_mod_of_dvd]
        exact dvd_mul_right D B
      have late : ((x+z*B)>>>h)%(2*D)=z := by
        rw [Nat.shiftRight_eq_div_pow]
        change ((x+z*B)/B)%(2*D)=z
        rw [Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hx,zero_add,Nat.mod_eq_of_lt hz]
      unfold term
      rw [libGoodPrefix]
      rw [pow_add,low,seed,late]
      by_cases hz' : R h z=true <;> simp [hz']
    rw [Finset.sum_congr rfl (fun x hx => point x (Finset.mem_range.mp hx))]
    by_cases hh : R h z=true
    · simpa only [hh,ite_true] using (libMassFiber w h s (z%D) R (Nat.mod_lt _ hd)).symm
    · simp [hh]
  rw [libMassFiber _ _ _ _ _ ht]
  have hh : 2^(h+1)=B+B := by dsimp [B];rw [pow_succ];omega
  rw [hh,Finset.sum_range_add]
  have e0 (x : ℕ) : x+t*(B+B)=x+(2*t)*B := by ring
  have e1 (x : ℕ) : B+x+t*(B+B)=x+(2*t+1)*B := by ring
  simp_rw [e1,e0]
  change (∑ x ∈ Finset.range B, term x (2*t)) + (∑ x ∈ Finset.range B, term x (2*t+1)) = _
  rw [split,split] <;> change _ < 2 * 2^w <;> omega

theorem libLateGate {w j p : ℕ} (hw : 2≤w) (hp : p < 2*2^w) (data : Fin (2^w) → Bool) :
    libEncode w data (w+2+j) p = true ↔ ¬(p % 2^w = 2^w-1 ∧ p < 2^w) := by
  have h0 : w+2+j ≠ 0 := by omega
  have h1 : w+2+j ≠ 1 := by omega
  have h2 : w+2+j ≠ 2 := by omega
  have h3 : ¬ w+2+j < w+2 := by omega
  simp only [libEncode,h0,h1,h2,h3,if_false,Bool.or_eq_true,Bool.not_eq_true',beq_eq_false_iff_ne]
  have hbit : p.testBit w = true ↔ ¬ p < 2^w := by
    by_cases h : p < 2^w
    · simp [h,Nat.testBit_lt_two_pow h]
    · let D := 2^w
      have hpos : 0<D := by dsimp [D]; positivity
      have ht : p - D < D := by dsimp [D];omega
      have e : p = 2^w+(p-D) := by dsimp [D];omega
      have val : p.testBit w=true := by
        calc p.testBit w = (2^w+(p-D)).testBit w := congrArg (fun x : ℕ => x.testBit w) e
             _ = true := by rw [Nat.testBit_two_pow_add_eq,Nat.testBit_lt_two_pow ht]; rfl
      simp [h,val]
  rw [hbit]
  tauto

def libEarlyRules (h e : ℕ) (d : Bool) : Prop :=
  (0<h → e.testBit 0 = true → d = true) ∧
  (1<h → e.testBit 0 = true → e.testBit 1 = true) ∧
  (2<h → e.testBit 2 = e.testBit 0) ∧
  (∀ i, 3 ≤ i → i<h → e.testBit i = e.testBit (i-1))

theorem libEarlyCompat (w h b : ℕ) (hw : 2 ≤ w) (hh : h ≤ w+2)
    (data : Fin (2^w) → Bool) :
    libGood w (libEncode w data) h b ↔
      libEarlyRules h (b / 2^w) (data ⟨b%2^w,Nat.mod_lt _ (by positivity)⟩) := by
  let p (i : ℕ) := (b >>> i) % (2*2^w)
  have two : 2*2^w=2^(w+1) := by rw [pow_succ]; omega
  have bit (i j : ℕ) (hj : j ≤ w) : (p i).testBit j = b.testBit (i+j) := by
    have hj' : j<w+1 := by omega
    simp [p,two,Nat.testBit_mod_two_pow,hj']
  have first : p 0 % 2^w = b%2^w := by
    simp [p, Nat.mod_mod_of_dvd]
  have conv (i : ℕ) : (b / 2^w).testBit i = b.testBit (i+w) :=
    Nat.testBit_div_two_pow _ _
  have r0 : libEncode w data 0 (p 0) = true ↔
      (b/2^w).testBit 0=true → data ⟨b%2^w, Nat.mod_lt _ (by positivity)⟩=true := by
    simp [libEncode, bit,first,conv]; cases b.testBit w <;> simp
  have r1 : libEncode w data 1 (p 1) = true ↔
      (b/2^w).testBit 0=true → (b/2^w).testBit 1=true := by
    have hw' : 1+(w-1)=w := by omega
    simp [libEncode,bit,conv,hw']; cases b.testBit w <;> simp
  have r2 : libEncode w data 2 (p 2) = true ↔ (b/2^w).testBit 2=(b/2^w).testBit 0 := by
    have hw' : 2+(w-2)=w := by omega
    simp [libEncode,bit,conv,hw']
  have ri (i : ℕ) (hi : 3 ≤ i) (ih : i<h) : libEncode w data i (p i) = true ↔
      (b/2^w).testBit i=(b/2^w).testBit (i-1) := by
    have hw' : i+(w-1)=i-1+w := by omega
    simp [libEncode,show i≠0 by omega,show i≠1 by omega,show i≠2 by omega,show i<w+2 by omega,bit,conv,hw']
  constructor
  · intro hg
    exact ⟨fun h0 => r0.mp (hg 0 h0),fun h1 => r1.mp (hg 1 h1),
      fun h2 => r2.mp (hg 2 h2),fun i hi ih => (ri i hi ih).mp (hg _ ih)⟩
  · rintro ⟨h0,h1,h2,h3⟩ i ih
    rcases i with (_|_|_|i)
    · exact r0.mpr (h0 ih)
    · exact r1.mpr (h1 ih)
    · exact r2.mpr (h2 ih)
    · exact (ri _ (by omega) ih).mpr (h3 _ (by omega) ih)



theorem libEarlyClassify (h e : ℕ) (d : Bool) (he : e < 2^h) :
    libEarlyRules h e d ↔ e=0 ∨ e=2 ∨ (d=true ∧ e=2^h-1) := by
  constructor
  · rintro ⟨hr0,hr1,hr2,hr3⟩
    have high (i : ℕ) (ih : h ≤ i) : e.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le he (Nat.pow_le_pow_right (by decide) ih))
    have steady : ∀ i, 2 ≤ i → i < h → e.testBit i = e.testBit 0 := by
      intro i
      induction i with
      | zero => omega
      | succ i ih =>
        intro hi hlt
        by_cases hi2 : i=1
        · subst i; exact hr2 hlt
        · rw [hr3 _ (by omega) hlt]
          exact ih (by omega) (by omega)
    by_cases ht : e.testBit 0 = true
    · by_cases hh : h=0
      · subst h; simp at he; exact Or.inl (by omega)
      right; right
      refine ⟨hr0 (by omega) ht, Nat.eq_of_testBit_eq fun i => ?_⟩
      rw [Nat.testBit_two_pow_sub_one]
      by_cases hi : i<h
      · simp only [hi,decide_true]
        rcases i with (_|_|i)
        · exact ht
        · exact hr1 hi ht
        · exact (steady _ (by omega) hi).trans ht
      · simpa [hi] using high i (by omega)
    · have zero : e.testBit 0 = false := by cases h0 : e.testBit 0 <;> simp_all
      have zero' (i : ℕ) (hi : 2 ≤ i) : e.testBit i = false := by
        by_cases ih : i<h
        · exact (steady i hi ih).trans zero
        · exact high i (by omega)
      cases h1 : e.testBit 1 with
      | false =>
        left
        apply Nat.eq_of_testBit_eq
        rintro (_|_|i)
        · simpa using zero
        · simpa using h1
        · simpa using zero' (i+2) (by omega)
      | true =>
        right; left
        change e=2^1
        apply Nat.eq_of_testBit_eq
        intro i
        rw [Nat.testBit_two_pow]
        rcases i with (_|_|i)
        · exact zero
        · exact h1
        · simpa using zero' (i+2) (by omega)
  · rintro (rfl|rfl|⟨rfl,rfl⟩)
    · simp [libEarlyRules]
    · change libEarlyRules h (2^1) d
      simp [libEarlyRules]
      constructor
      · intro _; decide
      · intro i hi _
        change (2^1 : ℕ).testBit i = (2^1 : ℕ).testBit (i-1)
        simp only [Nat.testBit_two_pow, decide_eq_decide]
        omega
    · simp [libEarlyRules, Nat.testBit_two_pow_sub_one]
      exact ⟨by omega, by omega, fun i hi ih => by omega⟩



theorem libEarlyWords (w h bits seed : ℕ) (hw : 2 ≤ w) (hh : h ≤ w+2)
    (hb : bits < 2^(w+h)) (hs : seed < 2^w) (hm : bits % 2^w = seed)
    (data : Fin (2^w) → Bool) :
    libGood w (libEncode w data) h bits ↔ bits = seed ∨ bits = seed+2^(w+1) ∨
      (data ⟨seed,hs⟩ = true ∧ bits = seed+(2^h-1)*2^w) := by
  subst seed
  have hd : 0 < 2^w := by positivity
  have he : bits / 2^w < 2^h :=
    (Nat.div_lt_iff_lt_mul hd).mpr (by simpa [pow_add,Nat.mul_comm] using hb)
  have decomp : bits % 2^w + (bits/2^w)*2^w = bits := Nat.mod_add_div' _ _
  have val (a : ℕ) : bits/2^w = a ↔ bits = bits % 2^w + a*2^w := by
    constructor
    · intro eq; simpa [← eq] using decomp.symm
    · intro eq
      exact Nat.mul_right_cancel hd (Nat.add_left_cancel (decomp.trans eq))
  rw [libEarlyCompat _ _ _ hw hh, libEarlyClassify _ _ _ he,val 0,val 2,val (2^h-1)]
  simp [pow_succ, Nat.mul_comm]

theorem earlyTailBound (w h seed : ℕ) (hw : 2≤w) (hh : h≤w+2)
    (hs : seed<2^w) (data : Fin (2^w) → Bool)
    (early : ∀ bits, bits<2^(w+h) → bits % 2^w=seed → libGood w (libEncode w data) h bits →
      bits=seed ∨ bits=seed+2^(w+1) ∨ (data ⟨seed,hs⟩=true ∧ bits=seed+(2^h-1)*2^w)) :
    ((Finset.range (2^w)).filter (fun t => (libMass w (libEncode w data) h seed t).testBit 0 = true)).card ≤ 3 := by
  classical
  let output := fun bits : ℕ => (bits >>> h) % 2^w
  let dest : Finset ℕ := {output seed,output (seed+2^(w+1)),output (seed+(2^h-1)*2^w)}
  apply le_trans (Finset.card_le_card (t := dest) ?_)
  · dsimp [dest]; exact (Finset.card_insert_le ..).trans (by have hz : ({output (seed+2^(w+1)),output (seed+(2^h-1)*2^w)} : Finset ℕ).card ≤ 2 := Finset.card_le_two; omega)
  · intro t ht
    have hb := (Finset.mem_filter.mp ht).2
    let ls := (List.range (2^(w+h))).filter (fun bits =>
       bits % 2^w == seed && (bits >>> h)%2^w == t &&
         (List.range h).all (fun i => libEncode w data i ((bits >>> i)%(2*2^w))))
    have hne : ls ≠ [] := by
      intro he
      change ls.length.testBit 0 = true at hb
      simp [he] at hb
    obtain ⟨bits,hbits⟩ := List.exists_mem_of_ne_nil _ hne
    have hi := List.mem_filter.mp hbits
    have H : bits % 2^w=seed ∧ (bits>>>h)%2^w=t ∧ libGood w (libEncode w data) h bits := by
      simpa [libGood, Bool.and_eq_true, List.all_eq_true, and_assoc] using hi.2
    obtain h0|h1|⟨_,h2⟩ := early bits (List.mem_range.mp hi.1) H.1 H.2.2
    · simpa [dest,output,←H.2.1,h0]
    · simpa [dest,output,←H.2.1,h1]
    · simpa [dest,output,←H.2.1,h2]

theorem libMiddle (w seed : ℕ) (hw : 2 ≤ w) (hs : seed<2^w) (data : Fin (2^w) → Bool)
    (early : ∀ b, b<2^(w+(w+2)) → b%2^w=seed → (libGood w (libEncode w data) (w+2) b ↔
      b=seed ∨ b=seed+2^(w+1) ∨ (data ⟨seed,hs⟩=true ∧ b=seed+(2^(w+2)-1)*2^w))) (t : ℕ) :
    libMass w (libEncode w data) (w+2) seed t =
      (if t=0 then 2 else 0)+(if t=2^w-1 then (data ⟨seed,hs⟩).toNat else 0) := by
  classical
  rw [libMassCard]
  let D := 2^w
  let A := seed
  let B := seed+2^(w+1)
  let C := seed+(2^(w+2)-1)*D
  let tail (b : ℕ) := (b >>> (w+2)) % D
  have ds : seed<D := hs
  have dpos : 0<D := by dsimp [D]; positivity
  have four : 4 ≤ D := by dsimp [D]; exact Nat.pow_le_pow_right (by decide : 0<2) hw
  have p1 : 2^(w+1)=D*2 := by simp [D,pow_succ]
  have p2 : 2^(w+2)=D*4 := by simp [D,pow_add]
  have p3 : 2^(w+(w+2))=D*(D*4) := by rw [pow_add,p2]
  have a : A < D*4 := by dsimp [A]; omega
  have b : B < D*4 := by dsimp [B]; rw [p1]; omega
  have ac : A ≠ B := by dsimp [A,B]; rw [p1]; omega
  have large : D*4 ≤ C := by
    dsimp [C]; rw [p2]; have hm : 4*D ≤ (D*4-1)*D := Nat.mul_le_mul_right D (by omega); omega
  have bc : B ≠ C := by omega
  have ac' : A ≠ C := by omega
  have top : (D*4-1)*D + D = D*(D*4) := by
    rw [← Nat.succ_mul, show (D*4-1).succ = D*4 by omega, Nat.mul_comm]
  have bounds : A<2^(w+(w+2)) ∧ B<2^(w+(w+2)) ∧ C<2^(w+(w+2)) := by
    rw [p3]; dsimp [C] at *; rw [p2] at *; omega
  have mods : A%D=seed ∧ B%D=seed ∧ C%D=seed := by
    dsimp [A,B,C]; rw [p1]; simp [Nat.add_mod, Nat.mod_eq_of_lt ds, Nat.mul_comm D 2]
  have endC : tail C = D-1 := by
    have split : C = (seed+(D*4-D)) + (D*4)*(D-1) := by
      dsimp [C]; rw [p2]
      have e : (D*4)*(D-1)+D*4 = D*(D*4) := by
        rw [← Nat.mul_succ]; rw [show (D-1).succ=D by omega]; ring
      omega
    dsimp [tail]; rw [Nat.shiftRight_eq_div_pow,p2,split,Nat.add_mul_div_left _ _ (by omega)]
    rw [Nat.div_eq_of_lt (by omega), Nat.zero_add,Nat.mod_eq_of_lt (by omega)]
  have ends : tail A=0 ∧ tail B=0 := by
    dsimp [tail]; rw [Nat.shiftRight_eq_div_pow,Nat.shiftRight_eq_div_pow,p2,
      Nat.div_eq_of_lt a,Nat.div_eq_of_lt b]; simp
  let d := data ⟨seed,hs⟩
  let F : Finset ℕ := (if t=0 then {A,B} else ∅) ∪ (if t=D-1 ∧ d=true then {C} else ∅)
  have eq : ((Finset.range (2^(w+(w+2)))).filter (fun v => v%2^w=seed ∧
      (v >>> (w+2))%2^w=t ∧ libGood w (libEncode w data) (w+2) v)) = F := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range]
    change (v<2^(w+(w+2)) ∧ v%D=seed ∧ tail v=t ∧ _) ↔ _
    constructor
    · rintro ⟨hv,hm,ht,hg⟩
      rcases (early v hv hm).mp hg with rfl|rfl|⟨hd,rfl⟩
      · change tail A=t at ht
        simp [F,←ht,ends.1,A]
      · change tail B=t at ht
        simp [F,←ht,ends.2,B]
      · change tail C=t at ht
        change C ∈ F
        simp [F,←ht,endC,d,hd]
    · intro hv
      have mem : (t=0 ∧ (v=A ∨ v=B)) ∨ (t=D-1 ∧ d=true ∧ v=C) := by
        by_cases a0 : t=0 <;> by_cases a1 : t=D-1 <;> cases ed : d <;> simp_all [F] <;> tauto
      rcases mem with ⟨rfl,rfl|rfl⟩|⟨rfl,hd,rfl⟩
      · exact ⟨bounds.1,mods.1,ends.1,(early A bounds.1 mods.1).mpr (Or.inl rfl)⟩
      · exact ⟨bounds.2.1,mods.2.1,ends.2,(early B bounds.2.1 mods.2.1).mpr (Or.inr (Or.inl rfl))⟩
      · exact ⟨bounds.2.2,mods.2.2,endC,(early C bounds.2.2 mods.2.2).mpr (Or.inr (Or.inr ⟨hd,rfl⟩))⟩
  rw [eq]
  change F.card = (if t=0 then 2 else 0)+(if t=D-1 then d.toNat else 0)
  have ne : 0 ≠ D-1 := by omega
  by_cases h0 : t=0 <;> by_cases h1 : t=D-1 <;> cases hd : d <;> simp_all [F,Finset.card_insert_of_notMem]

def lateAmount (w j tail rare : ℕ) : ℕ :=
  (if 2^(w-j) ∣ tail then 2 else 0) + (if tail=2^w-1 then rare else 0)
def lateBranch (w j p rare : ℕ) : ℕ :=
  if p % 2^w = 2^w-1 ∧ p < 2^w then 0 else lateAmount w j (p%2^w) rare

theorem latePair (w j t rare : ℕ) (hj : j < w) (ht : t < 2^w) :
    lateBranch w j (2*t) rare + lateBranch w j (2*t+1) rare = lateAmount w (j+1) t rare := by
  let D := 2^w
  let d := 2^(w-j)
  let e := 2^(w-(j+1))
  have hdv : d ∣ D := pow_dvd_pow 2 (by omega)
  have dep : d=2*e := by
    dsimp [d,e]
    rw [show w-j=(w-(j+1))+1 by omega,pow_succ,Nat.mul_comm]
  have hD : 0<D := by dsimp [D]; positivity
  have Deven : 2 ∣ D := by
    exact dvd_trans (by rw [dep]; exact dvd_mul_right ..) hdv
  have eveniff : d ∣ ((2*t)%D) ↔ e ∣ t := by
    rw [Nat.dvd_mod_iff hdv, dep]
    exact Nat.mul_dvd_mul_iff_left (by decide)
  have odde : ¬ d ∣ ((2*t+1)%D) := by
    rw [Nat.dvd_mod_iff hdv,dep]
    intro h
    have he : 2 ∣ 2*t+1 := dvd_trans (dvd_mul_right ..) h
    omega
  have topEven : (2*t)%D ≠ D-1 := by
    have hEven : 2 ∣ ((2*t)%D) := (Nat.dvd_mod_iff Deven).2 (dvd_mul_right ..)
    omega
  have oddtop : ((2*t+1)%D=D-1 ∧ ¬2*t+1<D) ↔ t=D-1 := by
    change t<D at ht
    constructor
    · rintro ⟨eq,large⟩
      have sm : 2*t+1-D < D := by omega
      have modEq : (2*t+1)%D=2*t+1-D := by
        rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt sm]
      omega
    · intro h
      have sm : 2*t+1-D < D := by omega
      have ge : D ≤ 2*t+1 := by omega
      rw [Nat.mod_eq_sub_mod ge,Nat.mod_eq_of_lt sm]
      omega
  change (if (2*t)%D = D-1 ∧ 2*t<D then 0 else
      (if d ∣ (2*t)%D then 2 else 0)+(if (2*t)%D=D-1 then rare else 0)) +
    (if (2*t+1)%D=D-1 ∧ 2*t+1<D then 0 else
      (if d ∣ (2*t+1)%D then 2 else 0)+(if (2*t+1)%D=D-1 then rare else 0)) =
      (if e ∣ t then 2 else 0)+(if t=D-1 then rare else 0)
  simp only [topEven,false_and,ite_false,eveniff,odde,add_zero,zero_add]
  by_cases h : (2*t+1)%D=D-1 <;> by_cases lt : 2*t+1<D <;> simp_all


theorem lateParityBound (w j rare : ℕ) (get : ℕ → ℕ)
    (hg : ∀ t < 2^w, get t = lateAmount w j t rare) :
    ((Finset.range (2^w)).filter fun t => (get t).testBit 0 = true).card ≤ 1 := by
  classical
  have sub : ((Finset.range (2^w)).filter fun t => (get t).testBit 0 = true) ⊆ {2^w-1} := by
    intro t ht
    obtain ⟨hr,hb⟩ := Finset.mem_filter.mp ht
    apply Finset.mem_singleton.mpr
    by_contra hn
    rw [hg t (Finset.mem_range.mp hr)] at hb
    by_cases hd : 2^(w-j) ∣ t <;> simp [lateAmount, hn, hd] at hb
  simpa using Finset.card_le_card sub

theorem libLateInduction (w : ℕ) (hw : 2≤w) (data : Fin (2^w) → Bool) (s : Fin (2^w))
    (mid : ∀ t, libMass w (libEncode w data) (w+2) s.val t =
         (if t=0 then 2 else 0)+(if t=2^w-1 then (data s).toNat else 0)) :
    ∀ j≤w, ∀ t<2^w, libMass w (libEncode w data) (w+2+j) s.val t =
      lateAmount w j t (data s).toNat := by
  intro j
  induction j with
  | zero =>
    intro _ t ht
    rw [Nat.add_zero,mid]
    unfold lateAmount
    rw [Nat.sub_zero]
    have hd : 2^w ∣ t ↔ t=0 := by
      constructor
      · intro h
        exact (Nat.eq_zero_of_dvd_of_lt h ht)
      · rintro rfl; exact dvd_zero _
    simp only [hd]
  | succ j ih =>
    intro hj t ht
    have hj' : j < w := by omega
    have hd : 0 < 2^w := by positivity
    have branch (p : ℕ) (hp : p<2*2^w) :
        (if libEncode w data (w+2+j) p=true then libMass w (libEncode w data) (w+2+j) s.val (p%2^w) else 0) =
          lateBranch w j p (data s).toNat := by
      classical
      simp only [ih (by omega) _ (Nat.mod_lt _ hd), libLateGate hw hp]
      unfold lateBranch
      by_cases e : p%2^w=2^w-1 ∧ p<2^w <;> simp [e]
    rw [Nat.add_succ, libStep _ _ _ _ _ ht, branch (2*t) (by omega), branch (2*t+1) (by omega)]
    exact latePair w j t (data s).toNat hj' ht

theorem libEndMass (w : ℕ) (hw : 2≤w) (data : Fin (2^w) → Bool) (s z : Fin (2^w))
    (mid : ∀ t, libMass w (libEncode w data) (w+2) s.val t =
         (if t=0 then 2 else 0)+(if t=2^w-1 then (data s).toNat else 0)) :
    libMass w (libEncode w data) (2*w+2) s.val z.val =
      2 + (if z.val=2^w-1 then (data s).toNat else 0) := by
  have h := libLateInduction w hw data s mid w le_rfl z.val z.isLt
  simpa [lateAmount,show w+2+w=2*w+2 by omega] using h

theorem putTogether (finalMass : ∀ w, 2 ≤ w → ∀ (x : Fin (2^w) → Bool) (s z : Fin (2^w)), Mass w (libEncode w x) (2*w+2) s.val z.val = 2 + (if z.val = 2^w-1 then (x s).toNat else 0)) (prefixBound : ∀ w, 2 ≤ w → ∀ (x : Fin (2^w) → Bool) h, h ≤ 2*w+2 → ((List.range (2^w*2^w)).filter (fun i => (Mass w (libEncode w x) h (i%2^w) (i/2^w)).testBit 0)).length ≤ 3*2^w) : (∀ w : Nat, 2 ≤ w →
  let D := 2^w
  let stride := 2*D
  let L := 2*w+2
  let n := L+w
  let mass := fun (rows : Nat → Nat → Bool) (h seed tail : Nat) =>
    ((List.range (2^(w+h))).filter (fun bits =>
      bits % D == seed && (bits >>> h) % D == tail &&
      (List.range h).all (fun i => rows i ((bits >>> i) % stride)))).length
  let cyclic := fun (left right : Nat → Nat → Bool) =>
    ((List.range (2^n)).filter (fun word => (List.range n).all (fun site =>
      let pat := (List.range (w+1)).foldl (fun (acc bit : Nat) =>
        acc ||| ((word.testBit ((site+bit)%n)).toNat <<< bit)) 0
      if site < L then left site pat else right (site-L) pat))).length
  ∃ (encode : (Fin D → Bool) → Nat → Nat → Bool) (probe : Fin D → Nat → Nat → Bool),
    (∀ data : Fin D → Bool,
      (∀ h ≤ L, ((List.range (D*D)).filter (fun pair =>
        (mass (encode data) h (pair % D) (pair / D)).testBit 0)).length ≤ 3*D) ∧
      (∀ s z : Fin D, mass (encode data) L s.val z.val =
        2 + (if z.val = D-1 then (data s).toNat else 0)) ∧
      ∀ q : Fin D, cyclic (encode data) (probe q) = 2+(data q).toNat) ∧
    ∀ (S : Nat) (send : (Fin D → Bool) → Fin S) (answer : Fin S → Fin D → Bool),
      (∀ (payload : Fin D → Bool) (idx : Fin D),
        answer (send payload) idx = (cyclic (encode payload) (probe idx)).testBit 0) →
      2^D ≤ S) := by

  intro w hw
  dsimp only
  refine ⟨libEncode w, closeProbe w, ?_, ?_⟩
  · intro x
    refine ⟨prefixBound w hw x, finalMass w hw x, ?_⟩
    intro q
    change Cyclic w (libEncode w x) (closeProbe w q) = _
    rw [cycleProbeMass]
    have pos : 0 < 2^w := by positivity
    simpa using finalMass w hw x q ⟨2^w-1, by omega⟩
  · intro S send answer h
    apply messageCount send answer (fun x i => Cyclic w (libEncode w x) (closeProbe w i)) _ h
    intro x i
    rw [cycleProbeMass]
    have pos : 0 < 2^w := by positivity
    simpa using finalMass w hw x i ⟨2^w-1, by omega⟩

end PEqualNP.Outside.L_lib_398

open PEqualNP.Outside.L_lib_398

theorem PEqualNP.Outside.L_lib_398 : (∀ w : Nat, 2 ≤ w →
  let D := 2^w
  let stride := 2*D
  let L := 2*w+2
  let n := L+w
  let mass := fun (rows : Nat → Nat → Bool) (h seed tail : Nat) =>
    ((List.range (2^(w+h))).filter (fun bits =>
      bits % D == seed && (bits >>> h) % D == tail &&
      (List.range h).all (fun i => rows i ((bits >>> i) % stride)))).length
  let cyclic := fun (left right : Nat → Nat → Bool) =>
    ((List.range (2^n)).filter (fun word => (List.range n).all (fun site =>
      let pat := (List.range (w+1)).foldl (fun (acc bit : Nat) =>
        acc ||| ((word.testBit ((site+bit)%n)).toNat <<< bit)) 0
      if site < L then left site pat else right (site-L) pat))).length
  ∃ (encode : (Fin D → Bool) → Nat → Nat → Bool) (probe : Fin D → Nat → Nat → Bool),
    (∀ data : Fin D → Bool,
      (∀ h ≤ L, ((List.range (D*D)).filter (fun pair =>
        (mass (encode data) h (pair % D) (pair / D)).testBit 0)).length ≤ 3*D) ∧
      (∀ s z : Fin D, mass (encode data) L s.val z.val =
        2 + (if z.val = D-1 then (data s).toNat else 0)) ∧
      ∀ q : Fin D, cyclic (encode data) (probe q) = 2+(data q).toNat) ∧
    ∀ (S : Nat) (send : (Fin D → Bool) → Fin S) (answer : Fin S → Fin D → Bool),
      (∀ (payload : Fin D → Bool) (idx : Fin D),
        answer (send payload) idx = (cyclic (encode payload) (probe idx)).testBit 0) →
      2^D ≤ S) := by
  have mid (w : ℕ) (hw : 2 ≤ w) (x : Fin (2^w) → Bool) (s : Fin (2^w)) :=
    libMiddle w s.val hw s.isLt x (fun b hb hm => libEarlyWords w (w+2) b s.val hw le_rfl hb s.isLt hm x)
  apply putTogether
  · intro w hw x s z
    exact libEndMass w hw x s z (mid w hw x s)
  · intro w hw x h hh
    apply foldPairBound (2^w) (by positivity) (fun s t => (Mass w (libEncode w x) h s t).testBit 0)
    intro seed hs
    let s : Fin (2^w) := ⟨seed,hs⟩
    by_cases early : h ≤ w+2
    · apply earlyTailBound w h seed hw early hs x
      intro v hv hm hg
      exact (libEarlyWords w h v seed hw early hv hs hm x).mp hg
    · let j := h-(w+2)
      have hj : j≤w := by dsimp [j]; omega
      have eq : h=w+2+j := by dsimp [j]; omega
      rw [eq]
      exact (lateParityBound w j (x s).toNat _ (libLateInduction w hw x s (mid w hw x s) j hj)).trans (by decide)
