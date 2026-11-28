import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25883

namespace PEqualNP.Outside.L_meta_33632_aux

namespace ProbeCore
abbrev Strip := Nat → Bool
abbrev XY := Bool × Bool
def quad : List XY := [(false,false),(false,true),(true,false),(true,true)]
def tri : List XY := [(false,false),(false,true),(true,false)]
def square (p : XY) (j : Nat) := if j%2=0 then p.1 else p.2
def zero : Strip := fun _ => false
def endShift : Strip := fun j => decide (2≤j)
def row (c l r x y : Bool) := (c ^^ (r && x)) ^^ (l && y)
def cell (C δ z : Strip) (j : Nat) := row (C j) (δ (j+1)) (δ (j+2)) (z (j+1)) (z (j+2))
def hit (a : Nat) (C δ z : Strip) := (List.range a).any (cell C δ z)
def live (a : Nat) (C δ : Strip) := ∃ j<a, (C j || δ (j+1) || δ (j+2)) = true

theorem hitAt {a : Nat} {C δ z : Strip} {j : Nat}
    (hj : j<a) (h : cell C δ z j = true) : hit a C δ z = true :=
  List.any_eq_true.mpr ⟨j,List.mem_range.mpr hj,h⟩
theorem noHitAt {a : Nat} {C δ z : Strip} {j : Nat}
    (hj : j<a) (h : hit a C δ z = false) : cell C δ z j = false := by
  cases he : cell C δ z j
  · rfl
  · have b := hitAt hj he
    rw [h] at b
    contradiction

theorem countMono {α : Type} (L : List α) (f g : α → Bool)
    (h : ∀ x, f x = true → g x = true) : L.countP f ≤ L.countP g := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    rw [List.countP_cons,List.countP_cons]
    cases hf : f x
    · simp; omega
    · simp [h x hf]; omega

theorem rowSquare : ∀ (c l r s : Bool), (c || l || r) = true →
    2 ≤ quad.countP (fun p => row c l r (if s then p.1 else p.2)
                                      (if s then p.2 else p.1)) := by decide
theorem rowTriangle : ∀ (c l r : Bool), (c || l || r) = true →
    1 ≤ tri.countP (fun p => row c l r p.2 p.1) := by decide
theorem twoCoords : ∀ c0 c1 : Bool,
    3 ≤ quad.countP (fun p => (row c0 false true p.2 p.1) ||
                              (row c1 true true p.1 p.2)) := by decide

theorem squareCell (C δ : Strip) (j : Nat) (p : XY) :
    cell C δ (square p) j =
      row (C j) (δ (j+1)) (δ (j+2))
        (if (j+1)%2=0 then p.1 else p.2) (if (j+1)%2=0 then p.2 else p.1) := by
  have pair : (j+1)%2=0 ∧ (j+2)%2=1 ∨ (j+1)%2=1 ∧ (j+2)%2=0 := by omega
  rcases pair with ⟨x,y⟩|⟨x,y⟩ <;> simp [cell,square,x,y]

theorem squareHit (a : Nat) (C δ : Strip) (H : live a C δ) :
    2 ≤ (quad.map square).countP (hit a C δ) := by
  obtain ⟨j,hj,hl⟩ := H
  have hrow : 2 ≤ quad.countP (fun p => cell C δ (square p) j) := by
    by_cases hx : (j+1)%2=0
    · simpa [squareCell,hx] using rowSquare (C j) (δ (j+1)) (δ (j+2)) true hl
    · simpa [squareCell,hx] using rowSquare (C j) (δ (j+1)) (δ (j+2)) false hl
  rw [List.countP_map]
  have u := countMono quad (fun p => cell C δ (square p) j) (hit a C δ ∘ square)
    (fun p k => hitAt hj k)
  omega

theorem triHit (C δ : Strip) (H : live 1 C δ) :
    1 ≤ (tri.map square).countP (hit 1 C δ) := by
  obtain ⟨j,hj,hl⟩ := H
  have e : j=0 := by omega
  subst j
  rw [List.countP_map]
  have u := countMono tri (fun p => cell C δ (square p) 0) (hit 1 C δ ∘ square)
    (fun p k => hitAt (by decide : 0<1) k)
  have v : 1 ≤ tri.countP (fun p => cell C δ (square p) 0) := by
    simpa [cell,square] using rowTriangle (C 0) (δ 1) (δ 2) hl
  omega

theorem zeroRow (C δ : Strip) (j : Nat) : cell C δ zero j = C j := by
  unfold cell row zero; generalize C j = c; generalize δ (j+1) = l
  generalize δ (j+2) = r
  cases c <;> cases l <;> cases r <;> rfl

theorem endRowZero (C δ : Strip) :
    cell C δ endShift 0 = (C 0 ^^ δ 1) := by
  unfold cell row endShift
  generalize C 0 = c; generalize δ 1 = l; generalize δ 2 = r
  cases c <;> cases l <;> cases r <;> decide

theorem endRowRest (C δ : Strip) (j : Nat) (h : 1≤j) :
    cell C δ endShift j = ((C j ^^ δ (j+2)) ^^ δ (j+1)) := by
  have b : 2 ≤ j+1 := by omega
  have c : 2 ≤ j+2 := by omega
  simp [cell,row,endShift,b,c]

theorem squareIfNoExtra (a : Nat) (C δ : Strip) (ha : 2≤a) (H : live a C δ)
    (hz : hit a C δ zero = false) (he : hit a C δ endShift = false) :
    3 ≤ (quad.map square).countP (hit a C δ) := by
  have hc : ∀ j<a, C j = false := by
    intro j hj
    exact (zeroRow C δ j).symm.trans (noHitAt hj hz)
  have h1 : δ 1 = false := by
    have hh := noHitAt (show 0<a by omega) he
    rw [endRowZero, hc 0 (by omega)] at hh
    simpa using hh
  have link : ∀ j, 1≤j → j<a → δ (j+1)=δ (j+2) := by
    intro j h hj
    have hh := noHitAt hj he
    rw [endRowRest C δ j h, hc j hj] at hh
    generalize δ (j+1) = l at *; generalize δ (j+2) = r at *
    cases l <;> cases r <;> simp_all
  have common : ∀ i, i+2<a+2 → δ (i+2)=δ 2 := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro h
      have b := link (i+1) (by omega) (by omega)
      have e := ih (by omega)
      have : δ (i+1+2)=δ (i+2) := b.symm
      exact this.trans e
  cases h2 : δ 2
  · obtain ⟨j,hj,hl⟩ := H
    have d1 : δ (j+1)=false := by
      cases j with
      | zero => exact h1
      | succ j => simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using (common j (by omega)).trans h2
    have d2 := (common j (by omega)).trans h2
    simp [hc j hj,d1,d2] at hl
  · have h3 : δ 3 = true := (common 1 (by omega)).trans h2
    rw [List.countP_map]
    have m := countMono quad
      (fun p => cell C δ (square p) 0 || cell C δ (square p) 1)
      (hit a C δ ∘ square)
      (fun p h =>
        ((Bool.or_eq_true _ _).mp h).elim (hitAt (by omega : 0<a)) (hitAt (by omega : 1<a)))
    have t : 3 ≤ quad.countP (fun p => cell C δ (square p) 0 || cell C δ (square p) 1) := by
      simpa [cell,square,h1,h2,h3] using twoCoords (C 0) (C 1)
    omega

end ProbeCore

open ProbeCore
namespace ProbePlan
def block := quad.map square
def three := tri.map square
def repeatedBlock (e : Nat) := (List.replicate e block).flatten
def plan (a D : Nat) :=
  let e := D/2
  repeatedBlock e ++ (if D%2=0 then [] else
    if a=1 then three else [zero,endShift])
def cap (a D : Nat) := 2*D+(if a=1 ∧ D%2=1 then 1 else 0)

theorem lenBlock : block.length=4 := rfl
theorem lenThree : three.length=3 := rfl
theorem lenPrefix (e : Nat) : (repeatedBlock e).length = 4*e := by
  induction e with
  | zero => rfl
  | succ e ih =>
    have h : repeatedBlock (e+1) = block ++ repeatedBlock e := by
      simp [repeatedBlock,List.replicate_succ]
    rw [h,List.length_append,lenBlock,ih]
    omega

theorem countPrefix (e : Nat) (p : Strip → Bool) :
    (repeatedBlock e).countP p = e*(block.countP p) := by
  induction e with
  | zero => simp [repeatedBlock]
  | succ e ih =>
    have h : repeatedBlock (e+1) = block ++ repeatedBlock e := by
      simp [repeatedBlock,List.replicate_succ]
    rw [h,List.countP_append,ih,Nat.succ_mul,Nat.add_comm]

theorem planLength (a D : Nat) :
    (plan a D).length=cap a D := by
  have ha : D = D%2 + 2*(D/2) := (Nat.mod_add_div D 2).symm
  rcases Nat.mod_two_eq_zero_or_one D with h|h
  · simp [plan,cap,h,lenPrefix]; omega
  · by_cases ha1 : a=1
    · simp [plan,cap,h,ha1,lenPrefix,lenThree]; omega
    · simp [plan,cap,h,ha1,lenPrefix]; omega

theorem planDistance (a D : Nat) (ha : 0<a) (hD : 2≤D)
    (C δ : Strip) (H : live a C δ) :
    D ≤ (plan a D).countP (hit a C δ) := by
  let e := D/2
  have eD : D=D%2+2*e := (Nat.mod_add_div D 2).symm
  have h2 : 2≤block.countP (hit a C δ) := squareHit a C δ H
  have hbasic : e*2≤e*(block.countP (hit a C δ)) := Nat.mul_le_mul_left _ h2
  rcases Nat.mod_two_eq_zero_or_one D with h|h
  · simp [plan,h,countPrefix]
    change D ≤ e*(block.countP (hit a C δ))
    omega
  · by_cases ha1 : a=1
    · subst a
      have h3 : 1≤three.countP (hit 1 C δ) := triHit C δ H
      simp only [plan,h,Nat.one_ne_zero,ite_false,ite_true,List.countP_append,countPrefix]
      change D ≤ e*(block.countP (hit 1 C δ)) + three.countP (hit 1 C δ)
      omega
    · have hmin : 1≤e := by omega
      have hh : 2≤a := by omega
      simp only [plan,h,Nat.one_ne_zero,ite_false,ha1,List.countP_append,countPrefix]
      change D ≤ e*(block.countP (hit a C δ)) + [zero,endShift].countP (hit a C δ)
      cases hz : hit a C δ zero <;> cases he : hit a C δ endShift
      · have h4 : 3≤block.countP (hit a C δ) := squareIfNoExtra a C δ hh H hz he
        have r := Nat.mul_le_mul_left e h4
        omega
      · simp [hz,he]; omega
      · simp [hz,he]; omega
      · simp [hz,he]; omega

-- Differences of the concrete cubic-looking readout are affine in the
-- two varying probe coordinates; output offsets cancel with XOR.
def f (a b c : Bool) := a ^^ ((!b) && c)
theorem affineForm : ∀ (y0 b1 b2 d0 d1 d2 p1 p2 : Bool),
    ((f y0 (b1 ^^ p1) (b2 ^^ p2)) ^^
       (f (y0 ^^ d0) ((b1 ^^ p1) ^^ d1) ((b2 ^^ p2) ^^ d2))) =
       row ((((d0 ^^ d2) ^^ (d1&&d2)) ^^ (d2&&b1)) ^^ (d1&&b2)) d1 d2 p1 p2 := by decide

end ProbePlan

open ProbeCore
namespace ProbeLower
def phase (b δ : Strip) (j : Nat) :=
  xor (xor (xor (xor (δ j) (δ (j+2))) (δ (j+1) && δ (j+2)))
    (δ (j+2) && b (j+1))) (δ (j+1) && b (j+2))
def marker (a : Nat) : Strip := fun n => decide (n=a+1)
def const (b : Bool) : Strip := fun _ => b

theorem pulseRowLast (a : Nat) (z : Strip) (b : Bool) (j : Nat) (h : j<a) :
    cell (phase (const b) (marker a)) (marker a) z j =
      if j+1=a then !(b ^^ z a) else false := by
  have p : j≠a+1 := by omega
  have q : j≠a := by omega
  by_cases lt : j+1=a
  · have t : j+2=a+1 := by omega
    simp [cell,row,phase,const,marker,p,t,lt]
  · have n : j+2≠a+1 := by omega
    simp [cell,row,phase,const,marker,p,q,n,lt]

theorem pulseHit (a : Nat) (ha : a>0) (z : Strip) (b : Bool) :
    hit a (phase (const b) (marker a)) (marker a) z = !(b ^^ z a) := by
  apply Bool.eq_iff_iff.mpr
  simp only [hit,List.any_eq_true,List.mem_range]
  constructor
  · rintro ⟨j,hj,e⟩
    rw [pulseRowLast a z b j hj] at e
    by_cases t : j+1=a
    · simpa [t] using e
    · simp [t] at e
  · intro e
    refine ⟨a-1,by omega,?_⟩
    rw [pulseRowLast a z b (a-1) (by omega)]
    simp [show a-1+1=a by omega,e]

theorem pulseLive (a : Nat) (ha : a>0) (b : Bool) :
    live a (phase (const b) (marker a)) (marker a) := by
  refine ⟨a-1,by omega,?_⟩
  have e : a-1+2=a+1 := by omega
  simp [marker,e]

theorem countComplement {α : Type} (xs : List α) (p : α → Bool) :
    xs.countP p + xs.countP (fun x => !p x) = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.countP_cons,List.countP_cons]
    cases h : p x <;> simp <;> omega

theorem twoCategories (xs : List Strip) (a D : Nat) (ha : a>0)
    (assm : ∀ b δ, live a (phase b δ) δ → D ≤ xs.countP (hit a (phase b δ) δ)) :
    2*D ≤ xs.length := by
  have h0 := assm (const false) (marker a) (pulseLive a ha false)
  have h1 := assm (const true) (marker a) (pulseLive a ha true)
  have e0 : hit a (phase (const false) (marker a)) (marker a) = (fun z => !z a) := by
    funext z
    rw [pulseHit a ha]
    cases z a <;> rfl
  have e1 : hit a (phase (const true) (marker a)) (marker a) = (fun z => z a) := by
    funext z
    rw [pulseHit a ha]
    cases z a <;> rfl
  rw [e0] at h0
  rw [e1] at h1
  have h := countComplement xs (fun z => z a)
  omega

theorem parityFence (a b c d D : Nat)
    (h00 : D≤a+b) (h10 : D≤c+d)
    (h01 : D≤a+c) (h11 : D≤b+d)
    (h02 : D≤a+d) (h12 : D≤b+c) (odd : D%2=1) :
    2*D+1≤a+b+c+d := by omega

end ProbeLower

open ProbeCore ProbeLower ProbePlan
namespace ProbeParity
def single (a b c : Bool) : Strip := fun i => if i=0 then a else if i=1 then b else if i=2 then c else false
def affineName (c l r : Bool) := single ((c ^^ r) ^^ (l&&r)) l r

theorem singleLive (c l r : Bool) (h : (l||r)=true) :
    live 1 (phase (const false) (affineName c l r)) (affineName c l r) := by
  refine ⟨0,by decide,?_⟩
  simp [affineName,single]
  cases l <;> cases r <;> simp_all

theorem oneForm (c l r : Bool) :
    hit 1 (phase (const false) (affineName c l r)) (affineName c l r)
      = fun z => row c l r (z 1) (z 2) := by
  funext z
  unfold hit
  rw [show List.range 1 = [0] by decide]
  simp only [List.any_cons,List.any_nil,Bool.or_false]
  simp only [cell,phase,const,affineName,single]
  generalize z 1 = x
  generalize z 2 = y
  cases c <;> cases l <;> cases r <;> cases x <;> cases y <;> decide

abbrev Valid (xs : List Strip) (a D : Nat) :=
  ∀ b δ, live a (phase b δ) δ → D ≤ xs.countP (hit a (phase b δ) δ)
theorem balanceEvery (xs : List Strip) (D : Nat) (H : Valid xs 1 D)
    (c l r : Bool) (h : (l||r)=true) :
    D≤xs.countP (fun z => row c l r (z 1) (z 2)) := by
  have w := H (const false) (affineName c l r) (singleLive c l r h)
  simpa only [oneForm c l r] using w

def buckets (xs : List Strip) (x y : Bool) :=
  xs.countP (fun z => (z 1 == x) && (z 2 == y))

theorem bucketSum (xs : List Strip) :
    xs.length = buckets xs false false + buckets xs false true +
                  buckets xs true false + buckets xs true true := by
  induction xs with
  | nil => rfl
  | cons z xs ih =>
    cases e : z 1 <;> cases f : z 2 <;> simp [buckets,e,f] at * <;> omega

theorem rowTotals (xs : List Strip) :
    xs.countP (fun z => row true false true (z 1) (z 2))
        = buckets xs false false+buckets xs false true ∧
    xs.countP (fun z => row false false true (z 1) (z 2))
        = buckets xs true false+buckets xs true true ∧
    xs.countP (fun z => row true true false (z 1) (z 2))
        = buckets xs false false+buckets xs true false ∧
    xs.countP (fun z => row false true false (z 1) (z 2))
        = buckets xs false true+buckets xs true true ∧
    xs.countP (fun z => row true true true (z 1) (z 2))
        = buckets xs false false+buckets xs true true ∧
    xs.countP (fun z => row false true true (z 1) (z 2))
        = buckets xs false true+buckets xs true false := by
  induction xs with
  | nil => decide
  | cons z xs ih =>
    obtain ⟨a,b,c,d,e,f⟩ := ih
    cases z1 : z 1 <;> cases z2 : z 2 <;>
      simp [row,buckets,z1,z2] at * <;> omega

theorem oddFence (xs : List Strip) (D : Nat) (hD : D%2=1) (H : Valid xs 1 D) :
    2*D+1≤xs.length := by
  obtain ⟨e0,e1,e2,e3,e4,e5⟩ := rowTotals xs
  have c0 := balanceEvery xs D H true false true (by decide)
  have c1 := balanceEvery xs D H false false true (by decide)
  have c2 := balanceEvery xs D H true true false (by decide)
  have c3 := balanceEvery xs D H false true false (by decide)
  have c4 := balanceEvery xs D H true true true (by decide)
  have c5 := balanceEvery xs D H false true true (by decide)
  rw [e0] at c0; rw [e1] at c1; rw [e2] at c2
  rw [e3] at c3; rw [e4] at c4; rw [e5] at c5
  rw [bucketSum xs]
  exact parityFence _ _ _ _ D c0 c1 c2 c3 c4 c5 hD

theorem lower (xs : List Strip) (a D : Nat) (ha : 0<a) (H : Valid xs a D) :
    cap a D≤xs.length := by
  by_cases h : a=1 ∧ D%2=1
  · obtain ⟨r,d⟩ := h
    subst a
    simpa [cap,d] using oddFence xs D d H
  · simpa [cap,h] using twoCategories xs a D ha H

end ProbeParity

open ProbeCore ProbePlan ProbeLower ProbeParity
namespace CyclicWord
def rot (k s w : Nat) := ((w <<< (s % k)) ||| (w >>> (k-s%k))) % 2^k

theorem rotBit {k j s w : Nat} (h : j<k) (hs : s<k) (hw : w<2^k) :
    (rot k s w).testBit j = w.testBit (if j<s then k-s+j else j-s) := by
  simp only [rot,Nat.mod_eq_of_lt hs,Nat.testBit_mod_two_pow,h,decide_true,Bool.true_and,
    Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftRight]
  by_cases hj : j<s
  · simp [hj,Nat.not_le.mpr hj]
  · have big : w.testBit (k-s+j) = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hj,Nat.le_of_not_gt hj,big]

theorem modspec {x k : Nat} (h : x < 2*k) :
    (x % k = x ∧ x < k) ∨ (x % k + k = x ∧ k ≤ x) := by
  by_cases hx : x < k
  · left; exact ⟨Nat.mod_eq_of_lt hx, hx⟩
  · right; refine ⟨?_, by omega⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem rotBit' {k j w : Nat} (s : Nat) (h : j<k) (hw : w<2^k) :
    (rot k s w).testBit j = w.testBit ((j+k-s%k)%k) := by
  have hs : s % k < k := Nat.mod_lt _ (by omega)
  have e : rot k s w = rot k (s%k) w := by simp [rot]
  rw [e, rotBit h hs hw]
  congr 1
  rcases modspec (x := j+k-s%k) (k:=k) (by omega) with h1 | h1 <;> by_cases he : j < s%k <;> simp [he] <;> omega

theorem rot_lt (k s w : Nat) : rot k s w < 2^k := Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < (2 : Nat)))

def mix (k d z : Nat) := z ^^^ rot k d z ^^^ rot k (k-d) z

theorem mix_lt {k z : Nat} (d : Nat) (hz : z < 2^k) : mix k d z < 2^k :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hz (rot_lt _ _ _)) (rot_lt _ _ _)

theorem mixBit {k d j z : Nat} (hd : 0<d) (hdk : d<k) (h : j<k) (hz : z<2^k) :
    (mix k d z).testBit j
      = xor (xor (z.testBit j) (z.testBit ((j+k-d)%k))) (z.testBit ((j+d)%k)) := by
  have e : j+k-(k-d) = j+d := by omega
  simp only [mix, Nat.testBit_xor]
  rw [rotBit' d h hz, rotBit' (k-d) h hz, Nat.mod_eq_of_lt hdk,
    Nat.mod_eq_of_lt (show k-d<k by omega), e]

theorem flipBit (z q i : Nat) :
    (z ^^^ 2^q).testBit i = xor (z.testBit i) (decide (q = i)) := by
  simp [Nat.testBit_xor, Nat.testBit_two_pow]

theorem flip_lt {k z q : Nat} (hz : z < 2^k) (hq : q < k) : z ^^^ 2^q < 2^k :=
  Nat.xor_lt_two_pow hz (Nat.pow_lt_pow_right (by decide) hq)

theorem flip_flip (z q : Nat) : (z ^^^ 2^q) ^^^ 2^q = z := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

def ind (k d q j : Nat) : Bool :=
  xor (xor (decide (q = j)) (decide (q = (j+k-d)%k))) (decide (q = (j+d)%k))

theorem x6 : ∀ a b c d e f : Bool,
    xor (xor (xor a d) (xor b e)) (xor c f) = xor (xor (xor a b) c) (xor (xor d e) f) := by
  decide

theorem mixFlip {k d j z q : Nat} (hd : 0<d) (hdk : d<k) (h : j<k) (hz : z<2^k) (hq : q<k) :
    (mix k d (z ^^^ 2^q)).testBit j = xor ((mix k d z).testBit j) (ind k d q j) := by
  rw [mixBit hd hdk h (flip_lt hz hq), mixBit hd hdk h hz]
  simp only [flipBit, ind]
  exact x6 _ _ _ _ _ _

theorem mixLin {k d j r u : Nat} (hd : 0<d) (hdk : d<k) (h : j<k) (hr : r<2^k) (hu : u<2^k) :
    (mix k d (r ^^^ u)).testBit j = xor ((mix k d r).testBit j) ((mix k d u).testBit j) := by
  rw [mixBit hd hdk h (Nat.xor_lt_two_pow hr hu), mixBit hd hdk h hr, mixBit hd hdk h hu]
  simp only [Nat.testBit_xor]
  exact x6 _ _ _ _ _ _

theorem rotFlip {k j q key : Nat} (i : Nat) (h : j<k) (hq : q<k) (hkey : key<2^k) :
    (rot k i (key ^^^ 2^((q+k-i%k)%k))).testBit j
      = xor ((rot k i key).testBit j) (decide (q = j)) := by
  have hi : i % k < k := Nat.mod_lt _ (by omega)
  have hq' : (q+k-i%k)%k < k := Nat.mod_lt _ (by omega)
  rw [rotBit' i h (flip_lt hkey hq'), rotBit' i h hkey, flipBit]
  congr 1
  have : ((q+k-i%k)%k = (j+k-i%k)%k) ↔ (q = j) := by
    rcases modspec (x := q+k-i%k) (k:=k) (by omega) with h1 | h1 <;>
    rcases modspec (x := j+k-i%k) (k:=k) (by omega) with h2 | h2 <;> omega
  simp [this]

theorem keyFlip {k d j q key u : Nat} (i : Nat) (hd : 0<d) (hdk : d<k) (h : j<k) (hq : q<k)
    (hkey : key<2^k) (hu : u<2^k) :
    (mix k d (rot k i (key ^^^ 2^((q+k-i%k)%k)) ^^^ u)).testBit j
      = xor ((mix k d (rot k i key ^^^ u)).testBit j) (ind k d q j) := by
  have h1 : (j+k-d)%k < k := Nat.mod_lt _ (by omega)
  have h2 : (j+d)%k < k := Nat.mod_lt _ (by omega)
  rw [mixLin hd hdk h (rot_lt _ _ _) hu, mixLin hd hdk h (rot_lt _ _ _) hu,
    mixBit hd hdk h (rot_lt _ _ _), mixBit hd hdk h (rot_lt _ _ _),
    rotFlip i h hq hkey, rotFlip i h1 hq hkey, rotFlip i h2 hq hkey]
  simp only [ind]
  generalize (rot k i key).testBit j = A
  generalize (rot k i key).testBit ((j+k-d)%k) = B
  generalize (rot k i key).testBit ((j+d)%k) = C
  generalize (mix k d u).testBit j = U
  generalize decide (q = j) = D
  generalize decide (q = (j+k-d)%k) = E
  generalize decide (q = (j+d)%k) = F
  revert A B C U D E F; decide

theorem ind_iff {k d q j : Nat} (hd : 0<d) (hdk : 2*d<k) (hq : q<k) (hj : j<k) :
    ind k d q j = true ↔ (q = j ∨ q + d = j ∨ q + d = j + k ∨ q = j + d ∨ q + k = j + d) := by
  rcases modspec (x := j+k-d) (k:=k) (by omega) with h1 | h1 <;>
  rcases modspec (x := j+d) (k:=k) (by omega) with h2 | h2 <;>
  by_cases e1 : q = j <;> by_cases e2 : q = (j+k-d)%k <;> by_cases e3 : q = (j+d)%k <;>
  simp only [ind, e1, e2, e3, decide_true, decide_false] <;> simp <;> omega

theorem siteSpec {k t : Nat} (start : Nat) (ht : t < k) :
    start % k < k ∧ (((start+t)%k = start % k+t ∧ start % k+t < k) ∨
      ((start+t)%k + k = start % k+t ∧ k ≤ start % k+t)) := by
  have hs : start % k < k := Nat.mod_lt _ (by omega)
  refine ⟨hs, ?_⟩
  rw [← Nat.mod_add_mod]
  exact modspec (by omega)

def site (k start t : Nat) := (start+t)%k

theorem site_lt {k : Nat} (hk : 0<k) (start t : Nat) : site k start t < k := Nat.mod_lt _ hk

theorem indName {k d a t : Nat} (start : Nat) (hd : 0<d) (hk : a+2+2*d ≤ k) (ht : t < a+2) :
    ind k d ((site k start t + d)%k) (site k start t) = true := by
  have hs := site_lt (k:=k) (by omega) start t
  rw [ind_iff hd (by omega) (Nat.mod_lt _ (by omega)) hs]
  rcases modspec (x := site k start t + d) (k:=k) (by omega) with h|h <;> omega

theorem indName' {k d a t t' : Nat} (start : Nat) (hd : 0<d) (hk : a+2+2*d ≤ k) (ht : t < a+2)
    (ht' : t' < t) :
    ind k d ((site k start t + d)%k) (site k start t') = false := by
  have hs := site_lt (k:=k) (by omega) start t
  have hs' := site_lt (k:=k) (by omega) start t'
  rw [Bool.eq_false_iff, Ne, ind_iff hd (by omega) (Nat.mod_lt _ (by omega)) hs']
  obtain ⟨h0, h1⟩ := siteSpec (k:=k) (t:=t) start (by omega)
  obtain ⟨_, h2⟩ := siteSpec (k:=k) (t:=t') start (by omega)
  unfold site at *
  rcases modspec (x := (start+t)%k + d) (k:=k) (by omega) with h|h <;>
  rcases h1 with h1|h1 <;> rcases h2 with h2|h2 <;> omega

theorem indKey {k d a t : Nat} (start : Nat) (hd : 0<d) (hk : a+2+2*d ≤ k) (ht : t+1 < a+2) :
    ind k d ((site k start t + k - d)%k) (site k start t) = true := by
  have hs := site_lt (k:=k) (by omega) start t
  rw [ind_iff hd (by omega) (Nat.mod_lt _ (by omega)) hs]
  rcases modspec (x := site k start t + k - d) (k:=k) (by omega) with h|h <;> omega

theorem indKey' {k d a t : Nat} (start : Nat) (hd : 0<d) (hk : a+2+2*d ≤ k) (ht : t+1 < a+2) :
    ind k d ((site k start t + k - d)%k) (site k start (t+1)) = false := by
  have hs := site_lt (k:=k) (by omega) start t
  have hs' := site_lt (k:=k) (by omega) start (t+1)
  rw [Bool.eq_false_iff, Ne, ind_iff hd (by omega) (Nat.mod_lt _ (by omega)) hs']
  obtain ⟨h0, h1⟩ := siteSpec (k:=k) (t:=t) start (by omega)
  obtain ⟨_, h2⟩ := siteSpec (k:=k) (t:=t+1) start (by omega)
  unfold site at *
  rcases modspec (x := (start+t)%k + k - d) (k:=k) (by omega) with h|h <;>
  rcases h1 with h1|h1 <;> rcases h2 with h2|h2 <;> omega

def label (k d start init last c u x j : Nat) : Bool :=
  xor (xor ((mix k d (rot k init x ^^^ u)).testBit (site k start j))
      (!((mix k d (rot k init x ^^^ u)).testBit (site k start (j+1))) &&
        (mix k d (rot k init x ^^^ u)).testBit (site k start (j+2))))
    (xor ((rot k last x).testBit (site k start j)) (c.testBit (site k start j)))

def mixed (k d start u v j : Nat) : Bool :=
  ((mix k d u).testBit (site k start j) != (mix k d v).testBit (site k start j))

theorem yv {k d u v : Nat} (start init x j : Nat) (hd : 0<d) (hdk : d<k) (hu : u<2^k)
    (hv : v<2^k) :
    (mix k d (rot k init x ^^^ v)).testBit (site k start j)
      = xor ((mix k d (rot k init x ^^^ u)).testBit (site k start j)) (mixed k d start u v j) := by
  have hs := site_lt (k:=k) (by omega) start j
  rw [mixLin hd hdk hs (rot_lt _ _ _) hv, mixLin hd hdk hs (rot_lt _ _ _) hu]
  unfold mixed
  generalize (mix k d (rot k init x)).testBit (site k start j) = A
  generalize (mix k d u).testBit (site k start j) = B
  generalize (mix k d v).testBit (site k start j) = C
  revert A B C; decide

theorem labelDiff {k d u v : Nat} (start init last c x j : Nat) (hd : 0<d) (hdk : d<k)
    (hu : u<2^k) (hv : v<2^k) :
    (label k d start init last c u x j ≠ label k d start init last c v x j) ↔
      xor (mixed k d start u v j)
        (xor (!((mix k d (rot k init x ^^^ u)).testBit (site k start (j+1))) &&
            (mix k d (rot k init x ^^^ u)).testBit (site k start (j+2)))
          (!(xor ((mix k d (rot k init x ^^^ u)).testBit (site k start (j+1)))
              (mixed k d start u v (j+1))) &&
            xor ((mix k d (rot k init x ^^^ u)).testBit (site k start (j+2)))
              (mixed k d start u v (j+2)))) = true := by
  unfold label
  rw [yv start init x j hd hdk hu hv, yv start init x (j+1) hd hdk hu hv,
    yv start init x (j+2) hd hdk hu hv]
  generalize (mix k d (rot k init x ^^^ u)).testBit (site k start j) = P0
  generalize (mix k d (rot k init x ^^^ u)).testBit (site k start (j+1)) = P1
  generalize (mix k d (rot k init x ^^^ u)).testBit (site k start (j+2)) = P2
  generalize mixed k d start u v j = M0
  generalize mixed k d start u v (j+1) = M1
  generalize mixed k d start u v (j+2) = M2
  generalize xor ((rot k last x).testBit (site k start j)) (c.testBit (site k start j)) = L
  revert P0 P1 P2 M0 M1 M2 L; decide


end CyclicWord

open ProbeCore ProbePlan ProbeLower ProbeParity CyclicWord
namespace CyclicCore
def nameStrip (k d start u : Nat) : Strip :=
  fun j => (mix k d u).testBit (site k start j)
def probeStrip (k d start init x : Nat) : Strip :=
  fun j => nameStrip k d start (rot k init x) j
def stripXor (a b : Strip) : Strip := fun j => xor (a j) (b j)

-- Construct a word bit by bit via triangular flip witnesses.
theorem realize {k m : Nat} (g : Nat → Nat → Bool) (q : Nat → Nat) (t : Strip)
    (hq : ∀ i<m, q i<k)
    (flip : ∀ i<m, ∀ u<2^k, g (u ^^^ 2^(q i)) i = !g u i)
    (stable : ∀ i<m, ∀ j < i, ∀ u<2^k, g (u ^^^ 2^(q i)) j = g u j) :
    ∃ u<2^k, ∀ j<m, g u j=t j := by
  have aux : ∀ n, n≤m → ∃ u<2^k, ∀ j<n, g u j=t j := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨0,Nat.pow_pos (by decide),?_⟩
      intro j hj
      omega
    | succ n ih =>
      intro hn
      obtain ⟨u,hu,all⟩ := ih (by omega)
      by_cases e : g u n=t n
      · refine ⟨u,hu,?_⟩
        intro j hj
        by_cases b : j<n
        · exact all j b
        · have r : j=n := by omega
          simpa [r] using e
      · refine ⟨u ^^^ 2^(q n), flip_lt hu (hq n (by omega)),?_⟩
        intro j hj
        by_cases b : j<n
        · rw [stable n (by omega) j b u hu]
          exact all j b
        · have r : j=n := by omega
          subst j
          rw [flip n (by omega) u hu]
          cases hg : g u n <;> cases ht : t n <;> simp_all
  exact aux m (by omega)

theorem namesSurj (k d a start : Nat) (hd : 0<d) (hk : a+2+2*d≤k) (t : Strip) :
    ∃ u<2^k, ∀ j<a+2, nameStrip k d start u j=t j := by
  have hk0 : 0<k := by omega
  refine realize (nameStrip k d start) (fun j => (site k start j+d)%k) t
    (fun _ _ => Nat.mod_lt _ hk0) ?_ ?_
  · intro i hi u hu
    unfold nameStrip
    rw [mixFlip hd (by omega) (site_lt hk0 _ _) hu (Nat.mod_lt _ hk0), indName start hd hk hi]
    simp
  · intro i hi j hj u hu
    unfold nameStrip
    rw [mixFlip hd (by omega) (site_lt hk0 _ _) hu (Nat.mod_lt _ hk0),
      indName' start hd hk hi hj]
    simp

theorem probesSurj (k d a start init : Nat) (hd : 0<d) (hk : a+2+2*d≤k) (t : Strip) :
    ∃ x<2^k, ∀ j<a+2, probeStrip k d start init x j=t j := by
  have hk0 : 0<k := by omega
  let q : Nat → Nat := fun j => (site k start j+d)%k
  refine realize (probeStrip k d start init) (fun j => (q j+k-init % k)%k) t
    (fun _ _ => Nat.mod_lt _ hk0) ?_ ?_
  · intro i hi x hx
    have h := keyFlip init hd (by omega : d<k) (site_lt hk0 start i)
      (Nat.mod_lt (site k start i+d) hk0) hx (Nat.pow_pos (by decide : 0<(2:Nat)))
    rw [indName start hd hk hi] at h
    simpa [probeStrip,nameStrip,q] using h
  · intro i hi j hj x hx
    have h := keyFlip init hd (by omega : d<k) (site_lt hk0 start j)
      (Nat.mod_lt (site k start i+d) hk0) hx (Nat.pow_pos (by decide : 0<(2:Nat)))
    rw [indName' start hd hk hi hj] at h
    simpa [probeStrip,nameStrip,q] using h

-- Multiplex readout cancels its common last-rotation/constant offset.
theorem rawTruth : ∀ (p0 p1 p2 a0 a1 a2 b0 b1 b2 z : Bool),
  (xor (f (xor p0 a0) (xor p1 a1) (xor p2 a2)) z !=
   xor (f (xor p0 b0) (xor p1 b1) (xor p2 b2)) z) =
    cell (phase (ProbeParity.single a0 a1 a2)
       (stripXor (ProbeParity.single a0 a1 a2) (ProbeParity.single b0 b1 b2)))
      (stripXor (ProbeParity.single a0 a1 a2) (ProbeParity.single b0 b1 b2))
      (ProbeParity.single p0 p1 p2) 0 := by decide

theorem rawCell (k d a start init last c u v x j : Nat)
    (hd : 0<d) (hk : a+2+2*d≤k) (hu : u<2^k) (hv : v<2^k) :
    (label k d start init last c u x j != label k d start init last c v x j) =
    cell (phase (nameStrip k d start u) (stripXor (nameStrip k d start u) (nameStrip k d start v)))
      (stripXor (nameStrip k d start u) (nameStrip k d start v)) (probeStrip k d start init x) j := by
  have hk0 : 0<k := by omega
  have hdk : d<k := by omega
  have one (y j : Nat) (hy : y<2^k) :
      (mix k d (rot k init x ^^^ y)).testBit (site k start j) =
        xor (probeStrip k d start init x j) (nameStrip k d start y j) :=
     mixLin hd hdk (site_lt hk0 _ _) (rot_lt _ _ _) hy
  unfold label
  rw [one u j hu, one u (j+1) hu, one u (j+2) hu,
      one v j hv, one v (j+1) hv, one v (j+2) hv]
  exact rawTruth _ _ _ _ _ _ _ _ _ _

def replies (k d a start init last c u x : Nat) :=
  (List.range a).filter (label k d start init last c u x)

theorem repliesHit (k d a start init last c u v x : Nat)
   (hd : 0<d) (hk : a+2+2*d≤k) (hu : u<2^k) (hv : v<2^k) :
   (replies k d a start init last c u x ≠ replies k d a start init last c v x) ↔
    hit a (phase (nameStrip k d start u) (stripXor (nameStrip k d start u) (nameStrip k d start v)))
      (stripXor (nameStrip k d start u) (nameStrip k d start v)) (probeStrip k d start init x) = true := by
  constructor
  · intro neq
    by_cases h :
      hit a (phase (nameStrip k d start u) (stripXor (nameStrip k d start u) (nameStrip k d start v)))
        (stripXor (nameStrip k d start u) (nameStrip k d start v)) (probeStrip k d start init x) = true
    · exact h
    · exfalso
      apply neq
      apply List.filter_congr
      intro j hj
      have hh := noHitAt (List.mem_range.mp hj) (Bool.eq_false_iff.mpr h)
      rw [← rawCell k d a start init last c u v x j hd hk hu hv] at hh
      simpa using hh
  · intro h eq
    obtain ⟨j,hj,t⟩ := List.any_eq_true.mp h
    rw [← rawCell k d a start init last c u v x j hd hk hu hv] at t
    have same : label k d start init last c u x j = label k d start init last c v x j := by
      have s := (congrArg (fun L : List Nat => j ∈ L) eq)
      simp [replies,hj] at s
      exact s
    simp [same] at t

end CyclicCore

open ProbeCore ProbePlan ProbeLower ProbeParity CyclicWord CyclicCore
namespace CyclicTheorem

theorem cellRestrict {a : Nat} {b b' δ δ' p p' : Strip}
    (hb : ∀ j<a+2, b j=b' j) (hd : ∀ j<a+2, δ j=δ' j)
    (hp : ∀ j<a+2, p j=p' j) {j : Nat} (hj : j<a) :
    cell (phase b δ) δ p j=cell (phase b' δ') δ' p' j := by
  simp only [cell,phase,row]
  rw [hd j (by omega),hd (j+1) (by omega),hd (j+2) (by omega),
      hb (j+1) (by omega),hb (j+2) (by omega),hp (j+1) (by omega),hp (j+2) (by omega)]

theorem hitRestrict {a : Nat} {b b' δ δ' p p' : Strip}
    (hb : ∀ j<a+2, b j=b' j) (hd : ∀ j<a+2, δ j=δ' j)
    (hp : ∀ j<a+2, p j=p' j) :
    hit a (phase b δ) δ p=hit a (phase b' δ') δ' p' := by
  apply Bool.eq_iff_iff.mpr
  simp only [hit,List.any_eq_true,List.mem_range]
  constructor <;> rintro ⟨j,hj,h⟩
  · exact ⟨j,hj,(cellRestrict hb hd hp hj).symm.trans h⟩
  · exact ⟨j,hj,(cellRestrict hb hd hp hj).trans h⟩

theorem hitIsLive {a : Nat} {C δ p : Strip} (g : hit a C δ p=true) : live a C δ := by
  obtain ⟨j,hj,k⟩ := List.any_eq_true.mp g
  refine ⟨j,List.mem_range.mp hj,?_⟩
  unfold cell row at k
  generalize C j = c at *
  generalize δ (j+1) = l at *
  generalize δ (j+2) = r at *
  generalize p (j+1) = v at *
  generalize p (j+2) = w at *
  cases c <;> cases l <;> cases r <;> cases v <;> cases w <;> simp_all

theorem someHit {a : Nat} {C δ : Strip} (h : live a C δ) :
    ∃ p : Strip, hit a C δ p=true := by
  have cnt := squareHit a C δ h
  cases e : ((quad.map square).filter (hit a C δ)) with
  | nil =>
    rw [List.countP_eq_length_filter,e] at cnt
    simp at cnt
  | cons p ps =>
    refine ⟨p,?_⟩
    have z : p ∈ ((quad.map square).filter (hit a C δ)) := by
      rw [e]
      exact List.mem_cons_self
    exact (List.mem_filter.mp z).2

theorem wordsRealize (k d a start init : Nat) (hd : 0<d) (hk : a+2+2*d≤k)
    (L : List Strip) :
    ∃ Q : List Nat, Q.length=L.length ∧ (∀ x∈Q, x<2^k) ∧
      ∀ b δ, Q.countP (fun x => hit a (phase b δ) δ (probeStrip k d start init x))
            = L.countP (hit a (phase b δ) δ) := by
  induction L with
  | nil => exact ⟨[],rfl,by simp,by simp⟩
  | cons p L ih =>
    obtain ⟨Q,hlen,hbounds,e⟩ := ih
    obtain ⟨x,hx,hp⟩ := probesSurj k d a start init hd hk p
    refine ⟨x::Q,by simpa using congrArg Nat.succ hlen,?_ ,?_⟩
    · intro t ht
      rcases List.mem_cons.mp ht with rfl|hm
      · exact hx
      · exact hbounds t hm
    · intro b δ
      rw [List.countP_cons,List.countP_cons,e b δ]
      rw [hitRestrict (fun _ _ => rfl) (fun _ _ => rfl) hp]

def Actual (k d a start init last c D : Nat) (Q : List Nat) : Prop :=
  (∀ x∈Q, x<2^k) ∧
  ∀ u<2^k, ∀ v<2^k,
    (∃ x<2^k, replies k d a start init last c u x ≠ replies k d a start init last c v x) →
    D≤Q.countP (fun x => decide (replies k d a start init last c u x ≠ replies k d a start init last c v x))

theorem predicateBridge (k d a start init last c u v : Nat)
  (hd : 0<d) (hk : a+2+2*d≤k) (hu : u<2^k) (hv : v<2^k) :
  (fun x => decide (replies k d a start init last c u x ≠ replies k d a start init last c v x)) =
  (fun x => hit a (phase (nameStrip k d start u) (stripXor (nameStrip k d start u) (nameStrip k d start v)))
      (stripXor (nameStrip k d start u) (nameStrip k d start v)) (probeStrip k d start init x)) := by
  funext x
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using repliesHit k d a start init last c u v x hd hk hu hv

theorem actualUpper (k d a start init last c D q : Nat)
    (hd : 0<d) (ha : 0<a) (hk : a+2+2*d≤k) (hD : 2≤D)
    (hq : cap a D≤q) :
    ∃ Q : List Nat, Q.length=q ∧ Actual k d a start init last c D Q := by
  let L := plan a D ++ List.replicate (q-cap a D) zero
  have len : L.length=q := by
    simp [L,planLength]
    omega
  obtain ⟨Q,ql,bounds,cnt⟩ := wordsRealize k d a start init hd hk L
  refine ⟨Q,ql.trans len,bounds,?_⟩
  intro u hu v hv diff
  obtain ⟨x,_,s⟩ := diff
  rw [predicateBridge k d a start init last c u v hd hk hu hv,cnt]
  have live0 := hitIsLive ((repliesHit k d a start init last c u v x hd hk hu hv).mp s)
  have lower := planDistance a D ha hD _ _ live0
  simp only [L,List.countP_append]
  omega

theorem xorCancel (a b : Bool) : xor a (xor a b)=b := by
  cases a <;> cases b <;> rfl

theorem actualLower (k d a start init last c D : Nat)
    (hd : 0<d) (ha : 0<a) (hk : a+2+2*d≤k) (Q : List Nat)
    (H : Actual k d a start init last c D Q) :
    cap a D≤Q.length := by
  let L := Q.map (probeStrip k d start init)
  have valid : Valid L a D := by
    intro b δ live0
    obtain ⟨u,hu,bs⟩ := namesSurj k d a start hd hk b
    obtain ⟨v,hv,ds⟩ := namesSurj k d a start hd hk (stripXor b δ)
    have ds' : ∀ j<a+2, (stripXor (nameStrip k d start u) (nameStrip k d start v)) j=δ j := by
      intro j hj
      unfold stripXor
      rw [bs j hj,ds j hj]
      exact xorCancel _ _
    obtain ⟨p,ph⟩ := someHit live0
    obtain ⟨x,hx,ps⟩ := probesSurj k d a start init hd hk p
    have dd : replies k d a start init last c u x ≠ replies k d a start init last c v x :=
      (repliesHit k d a start init last c u v x hd hk hu hv).mpr
        ((hitRestrict bs ds' ps).trans ph)
    have w := H.2 u hu v hv ⟨x,hx,dd⟩
    rw [predicateBridge k d a start init last c u v hd hk hu hv] at w
    simp only [L,List.countP_map]
    have congr : (fun x => hit a (phase (nameStrip k d start u)
             (stripXor (nameStrip k d start u) (nameStrip k d start v)))
           (stripXor (nameStrip k d start u) (nameStrip k d start v)) (probeStrip k d start init x)) =
          (fun x => hit a (phase b δ) δ (probeStrip k d start init x)) := by
       funext y
       exact hitRestrict bs ds' (fun _ _ => rfl)
    rw [congr] at w
    exact w
  simpa [L] using lower L a D ha valid

theorem exactListOptimum (k d a start init last c D q : Nat)
    (hd : 0<d) (ha : 0<a) (hk : a+2+2*d≤k) (hD : 2≤D) :
    (∃ Q : List Nat, Q.length=q ∧ Actual k d a start init last c D Q) ↔ cap a D≤q := by
  constructor
  · rintro ⟨Q,ql,h⟩
    simpa only [ql] using actualLower k d a start init last c D hd ha hk Q h
  · exact actualUpper k d a start init last c D q hd ha hk hD

end CyclicTheorem

open ProbePlan CyclicCore CyclicTheorem CyclicWord
namespace CyclicIndexed

theorem ofFnFinRange {α : Type} {q : Nat} (f : Fin q → α) :
    List.ofFn f = (List.finRange q).map f := by
  rw [List.finRange,List.map_ofFn]; rfl

theorem packWords {q : Nat} (L : List Nat) (e : L.length=q) :
    ∃ f : Fin q→Nat, List.ofFn f=L := by
  let f : Fin q→Nat := fun i => L[i.val]'(by simp [e])
  refine ⟨f,?_⟩
  apply List.ext_getElem
  · simp [e]
  · intro i hi hj
    rw [List.getElem_ofFn]

theorem finCount {α : Type} {q : Nat} (keys : Fin q→α) (p : α→Bool) :
    (List.ofFn keys).countP p = (List.finRange q).countP (fun i => p (keys i)) := by
  rw [ofFnFinRange,List.countP_map]
  rfl

theorem exactFinOptimum (k d a start init last c D q : Nat)
    (hd : 0<d) (ha : 0<a) (hk : a+2+2*d≤k) (hD : 2≤D) :
    (∃ keys : Fin q→Nat, (∀ i, keys i<2^k) ∧
      ∀ u<2^k, ∀ v<2^k,
        (∃ x<2^k, replies k d a start init last c u x ≠ replies k d a start init last c v x) →
        D≤(List.finRange q).countP (fun i =>
          decide (replies k d a start init last c u (keys i) ≠ replies k d a start init last c v (keys i))))
        ↔ cap a D≤q := by
  constructor
  · rintro ⟨keys,hkeys,H⟩
    have al : Actual k d a start init last c D (List.ofFn keys) := by
      constructor
      · intro x hx
        rw [ofFnFinRange] at hx
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
        exact hkeys i
      · intro u hu v hv dif
        rw [finCount]
        exact H u hu v hv dif
    have h := actualLower k d a start init last c D hd ha hk (List.ofFn keys) al
    simpa using h
  · intro H
    obtain ⟨L,e,al⟩ := actualUpper k d a start init last c D q hd ha hk hD H
    obtain ⟨keys,kl⟩ := packWords L e
    refine ⟨keys,?_,?_⟩
    · intro i
      apply al.1
      rw [← kl,ofFnFinRange]
      exact List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
    · intro u hu v hv dif
      have h := al.2 u hu v hv dif
      rw [← kl,finCount] at h
      exact h

end CyclicIndexed

namespace FinsetBridge
open CyclicWord CyclicCore CyclicIndexed ProbePlan

theorem filterEq (a : Nat) (l r : Nat → Bool) :
    ((Finset.range a).filter (fun j => l j = true) =
      (Finset.range a).filter (fun j => r j = true)) ↔
    ((List.range a).filter l = (List.range a).filter r) := by
  constructor
  · intro e
    apply List.filter_congr
    intro j hj
    have t := congrArg (fun s : Finset Nat => j ∈ s) e
    have inRange : j<a := List.mem_range.mp hj
    have tl : l j = true ↔ r j = true := by
      simpa only [Finset.mem_filter,Finset.mem_range,inRange,true_and] using (Iff.of_eq t)
    exact Bool.eq_iff_iff.mpr tl
  · intro e
    ext j
    have t := congrArg (fun s : List Nat => j ∈ s) e
    simpa only [Finset.mem_filter,Finset.mem_range,List.mem_filter,List.mem_range]
      using (Iff.of_eq t)

theorem replyNe (k d a start init last c u v x : Nat) :
    ((Finset.range a).filter (fun j => label k d start init last c u x j = true) ≠
      (Finset.range a).filter (fun j => label k d start init last c v x j = true)) ↔
    (replies k d a start init last c u x ≠ replies k d a start init last c v x) := by
  unfold replies
  exact not_congr (filterEq a _ _)

theorem cardCount {q : Nat} (p : Fin q → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = (List.finRange q).countP (fun i => decide (p i)) := by
  simpa only [List.toFinset_finRange] using
    (List.Nodup.card_eq_countP (P := p) (List.nodup_finRange q))

theorem optimum (k d a start init last c D q : Nat)
    (hd : 0<d) (ha : 0<a) (hk : a+2+2*d≤k) (hD : 2≤D) :
    (∃ keys : Fin q → Nat, (∀ i, keys i ∈ Finset.range (2^k)) ∧
      ∀ u ∈ Finset.range (2^k), ∀ v ∈ Finset.range (2^k),
        (∃ x ∈ Finset.range (2^k),
           (Finset.range a).filter (fun j => label k d start init last c u x j = true) ≠
           (Finset.range a).filter (fun j => label k d start init last c v x j = true)) →
        D ≤ (Finset.univ.filter (fun i : Fin q =>
          (Finset.range a).filter (fun j => label k d start init last c u (keys i) j = true) ≠
          (Finset.range a).filter (fun j => label k d start init last c v (keys i) j = true))).card)
      ↔ cap a D≤q := by
  simp only [Finset.mem_range]
  simp_rw [replyNe,cardCount]
  exact exactFinOptimum k d a start init last c D q hd ha hk hD

end FinsetBridge

end PEqualNP.Outside.L_meta_33632_aux

theorem PEqualNP.Outside.L_meta_33632 :
∀ (k d a start init last c : Nat), 0 < d → 0 < a → a + 2 + 2*d ≤ k →
  let words := Finset.range (2^k)
  let rot := fun (s z : Nat) =>
    ((z <<< (s % k)) ||| (z >>> (k - s % k))) % 2^k
  let mix := fun z : Nat => z ^^^ rot d z ^^^ rot (k-d) z
  let site := fun j : Nat => (start+j) % k
  let label := fun (u x j : Nat) =>
    let y := mix (rot init x ^^^ u)
    xor (xor (y.testBit (site j))
      (!(y.testBit (site (j+1))) && y.testBit (site (j+2))))
      (xor ((rot last x).testBit (site j)) (c.testBit (site j)))
  let response := fun (u x : Nat) => (Finset.range a).filter (fun j => label u x j)
  ∀ D q : Nat, 2 ≤ D →
    let cost := 2*D + (if a = 1 ∧ D % 2 = 1 then 1 else 0)
    (∃ keys : Fin q → Nat, (∀ i, keys i ∈ words) ∧
      ∀ u ∈ words, ∀ v ∈ words,
        (∃ x ∈ words, response u x ≠ response v x) →
        D ≤ (Finset.univ.filter (fun i : Fin q => response u (keys i) ≠ response v (keys i))).card)
      ↔ cost ≤ q := by
  intro k d a start init last c hd ha hk
  dsimp only
  intro D q hD
  exact PEqualNP.Outside.L_meta_33632_aux.FinsetBridge.optimum k d a start init last c D q hd ha hk hD
