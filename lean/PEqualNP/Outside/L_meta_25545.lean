import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25545_aux.Rotation
def rot (k s w : Nat) := ((w <<< (s % k)) ||| (w >>> (k-s % k))) % 2^k
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
private lemma wordEqBits {k a b : Nat} (ha : a<2^k) (hb : b<2^k)
    (h : ∀ j : Int, bits k a j = bits k b j) : a=b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<k
  · have e : idx k (i : Int) = i := by
      unfold idx
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      rfl
    simpa only [bits,e] using h (i : Int)
  · have hp : 2^k ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hp),Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hp)]

lemma rotUndo {k s w : Nat} (hs : 0<s) (hsk : s<k) (hw : w<2^k) :
    rot k (k-s) (rot k s w) = w := by
  apply wordEqBits (k:=k) (a:=rot k (k-s) (rot k s w)) (Nat.mod_lt _ (by positivity)) hw
  intro j
  have hb : rot k s w < 2^k := Nat.mod_lt _ (by positivity)
  rw [bitsRot (show k-s<k by omega) hb,bitsRot hsk hw]
  have q : j - ((k-s:Nat):Int) - (s:Int) = j - (k:Int) := by omega
  simp [bits,idx,q]


end PEqualNP.Outside.L_meta_25545_aux.Rotation

namespace PEqualNP.Outside.L_meta_25545_aux.Recovery
namespace Col97
open PEqualNP.Outside.L_meta_25545_aux.Rotation
def recover1 (k x u : Nat) := rot k (k-1) (x ^^^ u)
def rowInit (k w u : Nat) := rot k 1 w ^^^ u

lemma recover1Lt (k x u : Nat) : recover1 k x u < 2^k := Nat.mod_lt _ (by positivity)

lemma recover1Init {w u : Nat} (hk : 16≤k) (hw : w<2^k) :
    recover1 k (rowInit k w u) u = w := by
  simp only [recover1,rowInit,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]
  exact rotUndo (by decide) (by omega) hw

lemma initRecover1 {z u : Nat} (hk : 16≤k) (hz : z<2^k) (hu : u<2^k) :
    rowInit k (recover1 k z u) u = z := by
  have hi := rotUndo (k:=k) (s:=k-1) (w:=z ^^^ u) (by omega) (by omega) (Nat.xor_lt_two_pow hz hu)
  rw [show k-(k-1)=1 by omega] at hi
  simp only [rowInit,recover1,hi,Nat.xor_assoc,Nat.xor_self,Nat.xor_zero]

end Col97

end PEqualNP.Outside.L_meta_25545_aux.Recovery

namespace PEqualNP.Outside.L_meta_25545_aux.Line

def rot (k s word : Nat) : Nat :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def stepBit (k word j : Nat) : Bool :=
  xor (word.testBit j) (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))

def step (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc j =>
    acc ||| ((xor (word.testBit j)
      (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0

def mix (k word : Nat) : Nat :=
  word ^^^ rot k 1 word ^^^ rot k (k - 1) word

def stateAt (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (rounds key : Nat) : Nat :=
  (List.range rounds).foldl (fun prev tick =>
    step k (mix k prev) ^^^ rot k (2 * tick) key ^^^ (constant (tick + 1)).val) (rot k 1 key ^^^ u.val)

theorem stateAt_zero (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (key : Nat) :
    stateAt k u constant 0 key = rot k 1 key ^^^ u.val := rfl

theorem stateAt_succ (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (s key : Nat) :
    stateAt k u constant (s + 1) key =
      step k (mix k (stateAt k u constant s key)) ^^^ rot k (2 * s) key ^^^ (constant (s + 1)).val := by
  simp [stateAt, List.range_succ]

theorem rot_lt (k s word : Nat) : rot k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

theorem xor_lt {k a b : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : a ^^^ b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  have hpow := Nat.pow_le_pow_right Nat.zero_lt_two hj
  simp [Nat.testBit_xor, Nat.testBit_lt_two_pow (ha.trans_le hpow),
    Nat.testBit_lt_two_pow (hb.trans_le hpow)]

theorem testBit_rot {k s word b : Nat} (hw : word < 2 ^ k) (hb : b < k) :
    (rot k s word).testBit b = word.testBit ((b + k - s % k) % k) := by
  have hk : 0 < k := by omega
  have hs : s % k < k := Nat.mod_lt _ hk
  simp only [rot, Nat.testBit_mod_two_pow, hb, decide_true, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : s % k ≤ b
  · have hz : word.testBit (k - s % k + b) = false :=
      Nat.testBit_lt_two_pow (hw.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
    have he : (b + k - s % k) % k = b - s % k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, hz, he]
  · have he : (b + k - s % k) % k = k - s % k + b := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, he]

theorem testBit_foldl_or (p : Nat → Bool) (xs : List Nat) (acc i : Nat) :
    (xs.foldl (fun a j => a ||| ((p j).toNat <<< j)) acc).testBit i =
      (acc.testBit i || (decide (i ∈ xs) && p i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons j xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hji : j = i
    · subst j
      cases p i <;> simp
    · by_cases hle : j ≤ i
      · have hsub : 1 ≤ i - j := by omega
        have hbt : (p j).toNat.testBit (i - j) = false := by
          cases p j
          · simp
          · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 1 < 2 ^ 1)
              (Nat.pow_le_pow_right Nat.zero_lt_two hsub))
        simp [hle, hbt, Ne.symm hji]
      · simp [hle, Ne.symm hji]

theorem testBit_step_all (k word b : Nat) :
    (step k word).testBit b = (decide (b < k) && stepBit k word b) := by
  unfold step stepBit
  rw [testBit_foldl_or]
  simp

theorem testBit_step {k word b : Nat} (hb : b < k) :
    (step k word).testBit b = stepBit k word b := by
  simp [testBit_step_all, hb]

theorem step_lt (k word : Nat) : step k word < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro b hb
  simp [testBit_step_all, Nat.not_lt_of_ge hb]

theorem stateAt_lt (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (rounds key : Nat) :
    stateAt k u constant rounds key < 2 ^ k := by
  cases rounds with
  | zero => exact xor_lt (rot_lt k 1 key) u.isLt
  | succ s =>
    rw [stateAt_succ]
    exact xor_lt (xor_lt (step_lt k _) (rot_lt k _ _)) (constant (s + 1)).isLt

theorem testBit_mix {k word b : Nat} (hk : 2 ≤ k) (hw : word < 2 ^ k) (hb : b < k) :
    (mix k word).testBit b =
      xor (xor (word.testBit b) (word.testBit ((b + k - 1) % k)))
        (word.testBit ((b + 1) % k)) := by
  unfold mix
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rot hw hb, testBit_rot hw hb]
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2]
  have h3 : (b + k - (k - 1)) % k = (b + 1) % k := by congr 1; omega
  rw [h3]

theorem mod_sub_eq {k p s : Nat} (hk : 0 < k) (hsp : s ≤ p) :
    (p % k + k - s % k) % k = (p - s) % k := by
  have hdiv : p - s + s = p := Nat.sub_add_cancel hsp
  have h1 : (p % k + k - s % k + s % k) % k = p % k := by
    have hlt : s % k < k := Nat.mod_lt s hk
    have hadd : p % k + k - s % k + s % k = p % k + k := by omega
    rw [hadd, Nat.add_mod_right, Nat.mod_mod]
  have h2 : ((p - s) % k + s % k) % k = p % k := by
    rw [Nat.mod_add_mod, Nat.add_mod_mod, hdiv]
  set A := (p % k + k - s % k) % k
  set B := (p - s) % k
  set C := s % k
  have ha : A < k := Nat.mod_lt _ hk
  have hb : B < k := Nat.mod_lt _ hk
  have hs : C < k := Nat.mod_lt s hk
  have h3 : (A + C) % k = (B + C) % k := by
    rw [Nat.mod_add_mod, h1, ← h2]
  by_cases h1lt : A + C < k <;> by_cases h2lt : B + C < k
  · rw [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_of_lt h2lt] at h3; omega
  · rw [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h3; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h2lt] at h3; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h3; omega

def lineStep (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (src : Nat → Bool) : Nat → Nat → Bool
  | 0, p => src p
  | s + 1, p =>
    let prev := lineStep k u constant src s
    let m0 := xor (xor (prev p) (prev (p - 1))) (prev (p + 1))
    let m1 := xor (xor (prev (p + 1)) (prev p)) (prev (p + 2))
    let m2 := xor (xor (prev (p + 2)) (prev (p + 1))) (prev (p + 3))
    let st := xor m0 (!m1 && m2)
    let inj := xor (src (p + 1 - 2 * s)) (u.val.testBit ((p + 1 - 2 * s) % k))
    xor (xor st inj) ((constant (s + 1)).val.testBit (p % k))

theorem lineStep_succ (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (src : Nat → Bool) (s p : Nat) :
    lineStep k u constant src (s + 1) p =
      xor (xor (xor (xor (xor (lineStep k u constant src s p) (lineStep k u constant src s (p - 1)))
          (lineStep k u constant src s (p + 1)))
        (!(xor (xor (lineStep k u constant src s (p + 1)) (lineStep k u constant src s p))
          (lineStep k u constant src s (p + 2))) &&
         (xor (xor (lineStep k u constant src s (p + 2)) (lineStep k u constant src s (p + 1)))
          (lineStep k u constant src s (p + 3)))))
        (xor (src (p + 1 - 2 * s)) (u.val.testBit ((p + 1 - 2 * s) % k))))
        ((constant (s + 1)).val.testBit (p % k)) := rfl

theorem lineStep_eq_stateAt {k : Nat} (hk : 2 ≤ k) (u : Fin (2 ^ k))
    (constant : Nat → Fin (2 ^ k)) (key : Fin (2 ^ k)) :
    let src := fun pos : Nat => (rot k 1 key.val ^^^ u.val).testBit (pos % k)
    ∀ s p, 2 * s ≤ p → lineStep k u constant src s p = (stateAt k u constant s key.val).testBit (p % k) := by
  intro src s
  have hk_pos : 0 < k := by omega
  induction s with
  | zero => intro p _; rfl
  | succ s ih =>
    intro p hp
    rw [lineStep_succ, stateAt_succ, Nat.testBit_xor, Nat.testBit_xor, testBit_step (Nat.mod_lt p hk_pos)]
    unfold stepBit
    have hm : ∀ d, (mix k (stateAt k u constant s key.val)).testBit ((p % k + d) % k) =
        xor (xor (lineStep k u constant src s (p + d))
                 (lineStep k u constant src s (p + d - 1)))
            (lineStep k u constant src s (p + d + 1)) := by
      intro d
      have hlt : (p % k + d) % k < k := Nat.mod_lt _ hk_pos
      rw [testBit_mix hk (stateAt_lt k u constant s key.val) hlt]
      have h0 : (p % k + d) % k = (p + d) % k := Nat.mod_add_mod p k d
      have h1 : ((p + d) % k + k - 1) % k = (p + d - 1) % k := by
        have h1m : 1 = 1 % k := (Nat.mod_eq_of_lt (by omega)).symm
        conv_lhs => rw [h1m]
        exact mod_sub_eq hk_pos (by omega)
      have h2 : ((p + d) % k + 1) % k = (p + d + 1) % k := Nat.mod_add_mod (p + d) k 1
      rw [h0, h1, h2, ih (p + d) (by omega), ih (p + d - 1) (by omega), ih (p + d + 1) (by omega)]
    have hm0 := hm 0
    simp only [Nat.add_zero, Nat.mod_mod] at hm0
    have hm1 := hm 1
    have hm2 := hm 2
    have he1 : p + 1 - 1 = p := by omega
    have he2 : p + 2 - 1 = p + 1 := by omega
    have he3 : p + 1 + 1 = p + 2 := by omega
    have he4 : p + 2 + 1 = p + 3 := by omega
    rw [he1, he3] at hm1
    rw [he2, he4] at hm2
    rw [hm0, hm1, hm2]
    have hinj : xor (src (p + 1 - 2 * s)) (u.val.testBit ((p + 1 - 2 * s) % k)) =
        (rot k (2 * s) key.val).testBit (p % k) := by
      simp only [src, Nat.testBit_xor]
      have hrot1 : (rot k 1 key.val).testBit ((p + 1 - 2 * s) % k) =
          key.val.testBit ((p - 2 * s) % k) := by
        rw [testBit_rot key.isLt (Nat.mod_lt _ hk_pos)]
        have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
        have hsub : p + 1 - 2 * s - 1 = p - 2 * s := by omega
        rw [← hsub]
        have h1' := mod_sub_eq hk_pos (p := p + 1 - 2 * s) (s := 1) (by omega)
        rw [h1m] at h1' ⊢
        exact congrArg key.val.testBit h1'
      have hrot2 : (rot k (2 * s) key.val).testBit (p % k) =
          key.val.testBit ((p - 2 * s) % k) := by
        rw [testBit_rot key.isLt (Nat.mod_lt _ hk_pos), mod_sub_eq hk_pos (by omega)]
      rw [hrot1, hrot2]
      cases key.val.testBit ((p - 2 * s) % k) <;> cases u.val.testBit ((p + 1 - 2 * s) % k) <;> rfl
    rw [hinj]

theorem lineStep_agree_interval (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (f g : Nat → Bool) (lo hi : Nat) (hfg : ∀ p, lo ≤ p → p ≤ hi → f p = g p) :
    ∀ s p, max (lo + s) (lo + 2 * s - 3) ≤ p → p + 3 * s ≤ hi →
      lineStep k u constant f s p = lineStep k u constant g s p := by
  intro s
  induction s with
  | zero =>
    intro p h1 h2
    exact hfg p (by omega) (by omega)
  | succ s ih =>
    intro p h1 h2
    rw [lineStep_succ k u constant f s p, lineStep_succ k u constant g s p]
    have h0 := ih (p - 1) (by omega) (by omega)
    have h1' := ih p (by omega) (by omega)
    have h2' := ih (p + 1) (by omega) (by omega)
    have h3 := ih (p + 2) (by omega) (by omega)
    have h4 := ih (p + 3) (by omega) (by omega)
    have hi' := hfg (p + 1 - 2 * s) (by omega) (by omega)
    rw [h0, h1', h2', h3, h4, hi']

theorem lineStep_xor_pivot (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (f g : Nat → Bool) (s p : Nat) (hs : 4 ≤ s) (hp : 2 * s ≤ p)
    (hfg : ∀ q, p + 4 - 2 * s ≤ q → q ≤ p + 3 * s → f q = g q) :
    xor (lineStep k u constant f s p) (lineStep k u constant g s p) =
      xor (f (p + 3 - 2 * s)) (g (p + 3 - 2 * s)) := by
  have hs_eq : s = (s - 1) + 1 := by omega
  conv_lhs => rw [hs_eq, lineStep_succ k u constant f (s - 1) p, lineStep_succ k u constant g (s - 1) p]
  have h0 := lineStep_agree_interval k u constant f g (p + 4 - 2 * s) (p + 3 * s) hfg (s - 1) (p - 1) (by omega) (by omega)
  have h1 := lineStep_agree_interval k u constant f g (p + 4 - 2 * s) (p + 3 * s) hfg (s - 1) p (by omega) (by omega)
  have h2 := lineStep_agree_interval k u constant f g (p + 4 - 2 * s) (p + 3 * s) hfg (s - 1) (p + 1) (by omega) (by omega)
  have h3 := lineStep_agree_interval k u constant f g (p + 4 - 2 * s) (p + 3 * s) hfg (s - 1) (p + 2) (by omega) (by omega)
  have h4 := lineStep_agree_interval k u constant f g (p + 4 - 2 * s) (p + 3 * s) hfg (s - 1) (p + 3) (by omega) (by omega)
  have hidx : p + 1 - 2 * (s - 1) = p + 3 - 2 * s := by omega
  rw [h0, h1, h2, h3, h4, hidx]
  cases lineStep k u constant g (s - 1) (p - 1) <;>
  cases lineStep k u constant g (s - 1) p <;>
  cases lineStep k u constant g (s - 1) (p + 1) <;>
  cases lineStep k u constant g (s - 1) (p + 2) <;>
  cases lineStep k u constant g (s - 1) (p + 3) <;>
  cases u.val.testBit ((p + 3 - 2 * s) % k) <;>
  cases (constant (s - 1 + 1)).val.testBit (p % k) <;>
  cases f (p + 3 - 2 * s) <;>
  cases g (p + 3 - 2 * s) <;> rfl

def lInj {k : Nat} (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k)) (f : Nat → Bool) (t p : Nat) :=
  xor (xor (f (p + 3 - 2*t)) (u.val.testBit ((p+3-2*t) % k))) ((c t).val.testBit (p % k))
def lGuard {k : Nat} (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k)) (f : Nat → Bool) (t e : Nat) :=
  xor (xor (lineStep k u c f t (e-2)) (lineStep k u c f t (e-1))) (lineStep k u c f t e)
def lNear {k : Nat} (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k)) (f : Nat → Bool) (t e : Nat) :=
  lineStep k u c f t (e-2) == xor (lInj u c f t (e-1)) (lInj u c f t e)
def lFar {k : Nat} (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k)) (f : Nat → Bool) (t e : Nat) :=
  lineStep k u c f t (e-3) == lInj u c f t e
def lBranch {k : Nat} (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k)) (f : Nat → Bool) (t e : Nat) :=
  let b := lGuard u c f (t-1) e
  let next := lGuard u c f t (e-3+b.toNat)
  if b then 2+(lNear u c f t e).toNat+2*(lFar u c f t e).toNat+4*next.toNat else next.toNat
def gain (v : Nat) := if v<2 then v else 1+(v-2)/4+(if v=9 then 1 else 0)
def lTrace {k : Nat} (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k)) (f : Nat → Bool) (q len : Nat) :=
  (List.range len).foldl (fun (acc : Nat × Nat) j =>
    let v := lBranch u c f (5+2*j) acc.1
    (acc.1-6+gain v,acc.2+v*10^j)) (q-13,0)
end PEqualNP.Outside.L_meta_25545_aux.Line

namespace PEqualNP.Outside.L_meta_25545_aux.Line
def src {k : Nat} (u : Fin (2^k)) (key n : Nat) := (rot k 1 key ^^^ u.val).testBit (n % k)
def cut (q : Nat) (f : Nat → Bool) (n : Nat) := if n<q then f n else false

theorem gPivot {k s e : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (f g : Nat → Bool)
    (hs : 4≤s) (he : 2*s+2≤e)
    (ag : ∀j, e+1-2*s<j → f j=g j) :
    xor (lGuard u c f s e) (lGuard u c g s e) =
      xor (f (e+1-2*s)) (g (e+1-2*s)) := by
  have h₂ := lineStep_xor_pivot k u c f g s (e-2) hs (by omega) (fun j hj _ => ag _ (by omega))
  have hv : e-2+3-2*s=e+1-2*s := by omega
  rw [hv] at h₂
  have eqat (p : Nat) (h : e-1≤p) : lineStep k u c f s p=lineStep k u c g s p :=
    lineStep_agree_interval k u c f g (e+2-2*s) (p+3*s) (fun j hj _ => ag _ (by omega)) s p (by omega) (by omega)
  unfold lGuard
  rw [eqat (e-1) (by omega),eqat e (by omega),← h₂]
  generalize lineStep k u c f s (e-2)=a
  generalize lineStep k u c g s (e-2)=b
  generalize lineStep k u c g s (e-1)=z
  generalize lineStep k u c g s e=w
  cases a <;> cases b <;> cases z <;> cases w <;> rfl

def rawInj {k : Nat} (c : Nat→Fin (2^k)) (t key n : Nat) :=
  xor ((rot k (2*(t-1)) key).testBit (n % k)) ((c t).val.testBit (n % k))
theorem injRaw {k t p key : Nat} (hk : 6≤k) (ht : 1≤t) (hp : 2*t≤p) (hw : key<2^k)
    (u : Fin (2^k)) (c : Nat→Fin (2^k)) :
    lInj u c (src u key) t p=rawInj c t key p := by
  have pos : 0<k := by omega
  have h1 := mod_sub_eq (k:=k) (s:=1) (p:=p+3-2*t) pos (by omega)
  have h2 := mod_sub_eq (k:=k) (s:=2*(t-1)) (p:=p) pos (by omega)
  have ha : p+3-2*t-1=p-2*(t-1) := by omega
  simp only [lInj,rawInj,src,Nat.testBit_xor,testBit_rot hw (Nat.mod_lt _ pos),h1,h2,ha]
  cases key.testBit ((p-2*(t-1)) % k) <;> cases u.val.testBit ((p+3-2*t) % k) <;>
    cases (c t).val.testBit (p % k) <;> rfl


end PEqualNP.Outside.L_meta_25545_aux.Line

namespace PEqualNP.Outside.L_meta_25545_aux.Line
namespace Right
variable {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k))
abbrev Src := Nat → Bool
def tri (a b d : Bool) := xor (xor a b) d
def grd (y : Src) (e : Nat) := tri (y (e-2)) (y (e-1)) (y e)
def cell (y : Src) (j : Nat → Bool) (p : Nat) :=
  xor (xor (tri (y (p-1)) (y p) (y (p+1)))
    (!(tri (y p) (y (p+1)) (y (p+2))) && tri (y (p+1)) (y (p+2)) (y (p+3)))) (j p)
lemma norm (a b d e f j v : Bool) :
    xor (xor (xor (xor (xor b a) d) (!(xor (xor d b) e) && xor (xor e d) f)) j) v =
    xor (xor (tri a b d) (!(tri b d e) && tri d e f)) (xor j v) := by
  cases a <;> cases b <;> cases d <;> cases e <;> cases f <;> cases j <;> cases v <;> decide
lemma stepEq (f : Src) (s p : Nat) :
    lineStep k u c f (s+1) p = cell (lineStep k u c f s) (lInj u c f (s+1)) p := by
  unfold cell lInj
  rw [show p+3-2*(s+1)=p+1-2*s by omega]
  exact norm ..
def PrefixEq (f g : Src) (e : Nat) := ∀ i, i≤e → f i=g i
lemma guardEq {f g : Src} {e : Nat} (h : PrefixEq f g e) : grd f e = grd g e := by
  unfold grd;rw [h _ (by omega),h _ (by omega),h _ (by omega)]
lemma move {f g a b : Src} {e : Nat} (lo : 6≤e) (h : PrefixEq f g e) (j : PrefixEq a b e) :
    PrefixEq (cell f a) (cell g b) (e-3+(grd f e).toNat) := by
  intro p hp
  by_cases le : p+3≤e
  · unfold cell;rw [h _ (by omega),h _ (by omega),h _ (by omega),h _ (by omega),h _ (by omega),j _ (by omega)]
  · cases hit : grd f e with
    | false => simp [hit] at hp;omega
    | true =>
      simp [hit] at hp
      have mid : tri (f p) (f (p+1)) (f (p+2))=true := by
        unfold grd at hit
        rw [show e-2=p by omega,show e-1=p+1 by omega] at hit
        rwa [show p+2=e by omega]
      have eq := guardEq h
      have midg : tri (g p) (g (p+1)) (g (p+2))=true := by rwa [←h _ (by omega),←h _ (by omega),←h _ (by omega)]
      simp only [cell,mid,midg,Bool.not_true,Bool.false_and,Bool.xor_false]
      rw [h _ (by omega),h _ (by omega),h _ (by omega),j _ (by omega)]
end Right
end PEqualNP.Outside.L_meta_25545_aux.Line

namespace PEqualNP.Outside.L_meta_25545_aux.Scan

def move (mode letter : Nat) : Nat × Nat :=
  let aligned := ((mode == 1) && letter.testBit 0 && letter.testBit 1) ||
    ((mode == 2) && letter.testBit 1)
  let hit := letter.testBit 2
  (if aligned then (if hit then 0 else 2) else 1, hit.toNat + (aligned && hit).toNat)

def scan (code length : Nat) (initial : Nat × Nat) : Nat × Nat :=
  (List.range length).foldl (fun (st : Nat × Nat) j =>
    let result := move st.1 ((code >>> (3*j)) % 8)
    (result.1,st.2+result.2)) initial

abbrev summary (code n : Nat) := scan code n (0,0)
def price (n depth : Nat) :=
  ((List.range (8^n)).map (fun w => 2^(2*n-((summary w n).2-depth)))).sum

theorem scan_succ (w n : Nat) (m h : Nat) :
    scan w (n+1) (m,h) =
      let res := move m (w % 8)
      scan (w/8) n (res.1,h+res.2) := by
  simp only [scan, List.range_succ_eq_map,List.foldl_cons,List.foldl_map]
  congr 2
  · funext a j
    simp only [Nat.mul_succ,Nat.shiftRight_eq_div_pow,pow_add,
      Nat.div_div_eq_div_mul]
    rw [show (2:Nat)^3=8 by decide,Nat.mul_comm (2^(3*j)) 8]

theorem scan_offset (w n m h : Nat) : scan w n (m,h) =
    ((scan w n (m,0)).1,h+(scan w n (m,0)).2) := by
  induction n generalizing w m h with
  | zero => simp [scan]
  | succ n ih =>
    rw [scan_succ,scan_succ]
    simp only [Nat.zero_add]
    rw [ih (w/8) _ (h+_),ih (w/8) _ (move m (w % 8)).2]
    simp only [Nat.add_assoc]

theorem scan_gain_le (w n m : Nat) : (scan w n (m,0)).2 ≤ 2*n := by
  induction n generalizing w m with
  | zero => simp [scan]
  | succ n ih =>
    rw [scan_succ,scan_offset]
    simp only [Nat.zero_add]
    have two (i a : Nat) : (move i a).2 ≤ 2 := by
      unfold move
      generalize a.testBit 0=A
      generalize a.testBit 1=B
      generalize a.testBit 2=C
      generalize (i==1)=U
      generalize (i==2)=V
      cases A <;> cases B <;> cases C <;> cases U <;> cases V <;> decide
    have := ih (w/8) (move m (w % 8)).1
    have := two m (w % 8)
    omega

end PEqualNP.Outside.L_meta_25545_aux.Scan

namespace PEqualNP.Outside.L_meta_25545_aux.Word
open PEqualNP.Outside.L_meta_25545_aux.Line
def rawBit {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (w s p : Nat) :=
  (stateAt k u c s w).testBit (p % k)
def inj {k : Nat} (c : Nat → Fin (2^k)) (w s p : Nat) :=
  xor ((rot k (2*(s-1)) w).testBit (p % k)) ((c s).val.testBit (p % k))
def par {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (w t p : Nat) :=
  xor (xor (rawBit u c w t (p-2)) (rawBit u c w t (p-1))) (rawBit u c w t p)

def src {k : Nat} (u : Fin (2^k)) (w : Nat) := rot k 1 w ^^^ u.val
def word39 {k : Nat} (u w : Fin (2^k)) (j : Nat) := (src u w.val).testBit (j % k)

namespace Layout
variable {k : Nat}
def inputWord (u x : Fin (2^k)) : Fin (2^k) :=
  ⟨rot k (k-1) (x.val ^^^ u.val),Nat.mod_lt _ (by positivity)⟩
end Layout

end PEqualNP.Outside.L_meta_25545_aux.Word

namespace PEqualNP.Outside.L_meta_25545_aux.Word
namespace Solver

abbrev W (k : Nat) := Fin (2^k)
def flip {k : Nat} (x : W k) (p : Fin k) : W k :=
  ⟨x.val ^^^ (1 <<< p.val), Nat.xor_lt_two_pow x.isLt (by
    rw [Nat.one_shiftLeft]; exact Nat.pow_lt_pow_right (by decide) p.isLt)⟩
lemma flipBit {k : Nat} (x : W k) (p : Fin k) (j : Nat) :
    (flip x p).val.testBit j=xor (x.val.testBit j) (decide (p.val=j)) := by
  simp [flip,Nat.testBit_xor,Nat.one_shiftLeft,Nat.testBit_two_pow]

def put {k : Nat} (p : Nat → Fin k) (F : Nat → W k → Bool) (j : Nat) (x : W k) :=
  if F j x then flip x (p j) else x
def run {k : Nat} (p : Nat → Fin k) (F : Nat → W k → Bool) (seed : W k) : Nat → W k
  | 0 => seed
  | n+1 => put p F n (run p F seed n)
def Good {k : Nat} (F : Nat → W k → Bool) (n : Nat) (v : W k) := ∀ j<n, F j v=false
def Future {k : Nat} (p : Nat → Fin k) (n len : Nat) (j : Nat) := ∃ z, n≤z ∧ z<len ∧ (p z).val=j

theorem certified {k l : Nat} (p : Nat → Fin k) (F : Nat → W k → Bool) (seed : W k)
    (distinct : ∀ j<l, ∀ t<l, p j=p t → j=t)
    (tri : ∀ j<l, ∀ x y, Good F j x → Good F j y →
      (∀ b : Fin k, ¬Future p j l b.val → x.val.testBit b.val=y.val.testBit b.val) →
      xor (F j x) (x.val.testBit (p j).val)=xor (F j y) (y.val.testBit (p j).val)) :
    ∀ target, target=run p F seed l ↔ Good F l target ∧
      ∀ b:Fin k, ¬Future p 0 l b.val → target.val.testBit b.val=seed.val.testBit b.val := by
  have invariant (n : Nat) (hn : n≤l) : Good F n (run p F seed n) ∧
      (∀ b:Fin k, ¬Future p 0 n b.val →
        (run p F seed n).val.testBit b.val=seed.val.testBit b.val) ∧
      (∀ y, Good F n y →
        (∀ b:Fin k, ¬Future p 0 l b.val → y.val.testBit b.val=seed.val.testBit b.val) →
        ∀ b:Fin k, ¬Future p n l b.val →
          y.val.testBit b.val=(run p F seed n).val.testBit b.val) := by
    have stable (n : Nat) (hn : n≤l) (x y : W k) (gx : Good F n x)
        (same : ∀ b : Fin k, ¬Future p n l b.val → x.val.testBit b.val = y.val.testBit b.val) :
        Good F n y := by
      intro j hj
      induction j using Nat.strong_induction_on with
      | ind j ih =>
        have eq := tri j (by omega) x y (fun t ht => gx t (by omega)) (fun t ht => ih t ht (by omega))
          (fun b hb => same b (fun ⟨t,hl,hr,eq⟩ => hb ⟨t,by omega,hr,eq⟩))
        have thisBit := same (p j) (by
          rintro ⟨t,hl,hr,eq⟩
          have e := distinct t hr j (by omega) (Fin.ext eq)
          omega)
        rw [thisBit,gx j hj] at eq
        exact (Bool.xor_left_inj.mp eq).symm
    induction n with
    | zero =>
      refine ⟨fun _ h => by omega, fun _ _ => rfl, fun _ _ right => right⟩
    | succ n ih =>
      obtain ⟨hG,hOff,hUnique⟩ := ih (by omega)
      let x := run p F seed n
      let y := put p F n x
      have changed (j : Nat) : y.val.testBit j = xor (x.val.testBit j) (F n x && decide ((p n).val=j)) := by
        dsimp only [y,put]
        cases F n x <;> simp [flipBit]
      have keep (b:Fin k) (e:b≠p n) : y.val.testBit b.val=x.val.testBit b.val := by
        rw [changed];simp [show (p n).val≠b.val by intro h;exact e (Fin.ext h.symm)]
      have old := stable n (by omega) x y hG (fun b h => (keep b (by
        rintro rfl;exact h ⟨n,by omega,by omega,rfl⟩)).symm)
      have fix := tri n (by omega) y x old hG (fun b h => keep b (by
        rintro rfl;exact h ⟨n,by omega,by omega,rfl⟩))
      rw [changed] at fix
      have fixed : F n y=false := by
        simpa only [decide_true, Bool.and_true] using
          (show ∀ z c d : Bool, xor z (xor c d) = xor d c → z=false by decide) _ _ _ (by simpa using fix)
      refine ⟨?_,?_,?_⟩
      · intro j hj
        by_cases e:j=n
        · subst j;exact fixed
        · exact old j (by omega)
      · intro b h
        have off : ¬Future p 0 n b.val := fun ⟨j,hl,hr,eq⟩ => h ⟨j,hl,by omega,eq⟩
        have ne : b≠p n := by rintro rfl; exact h ⟨n,by omega,by omega,rfl⟩
        exact (keep b ne).trans (hOff b off)
      · intro z hz right b ho
        have upto := hUnique z (fun j hj => hz j (by omega)) right
        by_cases pe : b=p n
        · subst b
          have eq := tri n (by omega) z y (fun j hj => hz j (by omega)) old (fun j off =>
            (upto j off).trans (keep j (by rintro rfl;exact off ⟨n,by omega,by omega,rfl⟩)).symm)
          change z.val.testBit (p n).val=y.val.testBit (p n).val;simpa only [hz n (by omega),fixed,Bool.false_xor] using eq
        · have off : ¬Future p n l b.val := by
            rintro ⟨t,tl,tr,eq⟩
            by_cases tt:t=n
            · subst t;exact pe (Fin.ext eq.symm)
            · exact ho ⟨t,by omega,tr,eq⟩
          exact (upto b off).trans (keep b pe).symm
  intro target
  obtain ⟨ok,off,unique⟩:=invariant l (by omega)
  constructor
  · rintro rfl;exact ⟨ok,off⟩
  · rintro ⟨gt,h⟩
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases e:j<k
    · exact unique _ gt h ⟨j,e⟩ (fun ⟨t,hl,hr,_⟩ => by omega)
    · have mono : 2^k ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le target.isLt mono),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (run p F seed l).isLt mono)]

end Solver
end PEqualNP.Outside.L_meta_25545_aux.Word

namespace PEqualNP.Outside.L_meta_25545_aux.Encoding
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

end PEqualNP.Outside.L_meta_25545_aux.Encoding

namespace PEqualNP.Outside.L_meta_25545_aux
open PEqualNP.Outside.L_meta_25545_aux.Line (rot stateAt lineStep lInj lGuard cut)
open PEqualNP.Outside.L_meta_25545_aux.Word (src rawBit par inj word39)
open PEqualNP.Outside.L_meta_25545_aux.Scan (move summary)

def digit (v j : Nat) := (v >>> (3*j)) % 8
def tick (j : Nat) := 5+j
def edge (q v j : Nat) := q-13-3*j+(summary v j).2
def left (q v j : Nat) := edge q v j+3-2*tick j
def rawOne {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (w mode t e : Nat) :=
  let v:=inj c w (t-1) (e+2)
  let old:=par u c w (t-2) (e+2)
  let b:=xor old (inj c w (t-1) (e+1))
  if mode==1 then rawBit u c w (t-1) e == !(xor b v)
  else (src u w).testBit ((e+3-2*t+2) % k)
def rawTwo {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (w mode t e : Nat) :=
  if mode==0 then (src u w).testBit ((e+3-2*t+1) % k)
  else rawBit u c w (t-1) (e-1) == inj c w (t-1) (e+2)
def rawDigit {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (w mode t e : Nat) :=
  (rawOne u c w mode t e).toNat+2*(rawTwo u c w mode t e).toNat+4*(par u c w (t-1) e).toNat
def lineOne {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (f : Nat→Bool) (mode t e : Nat) :=
  let v:=lInj u c f (t-1) (e+2)
  let old:=lGuard u c f (t-2) (e+2)
  let b:=xor old (lInj u c f (t-1) (e+1))
  if mode==1 then lineStep k u c f (t-1) e == !(xor b v)
  else f (e+3-2*t+2)
def lineTwo {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (f : Nat→Bool) (mode t e : Nat) :=
  if mode==0 then f (e+3-2*t+1) else lineStep k u c f (t-1) (e-1) == lInj u c f (t-1) (e+2)
def trace {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (q w n : Nat) :=
  (List.range n).foldl (fun (st : Nat×Nat×Nat) j =>
    let d:=rawDigit u c w st.1 (tick j) (q-13-3*j+st.2.1)
    let res:=move st.1 d
    (res.1,st.2.1+res.2,st.2.2 ||| (d <<< (3*j)))) (0,0,0)

def prefixOK {k : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (q v w n : Nat) :=
  ∀ j<n,rawDigit u c w (summary v j).1 (tick j) (edge q v j)=digit v j

lemma summarySucc (v j : Nat) : summary v (j+1) =
    let stateNext:=move (summary v j).1 (digit v j)
    (stateNext.1,(summary v j).2+stateNext.2) := by
  simp only [PEqualNP.Outside.L_meta_25545_aux.Scan.scan,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rfl

lemma moveBound (s v : Nat) : (move s v).2 ≤ 2 :=
  (show ∀ a b:Bool,a.toNat + (b && a).toNat≤2 by decide) _ _
lemma summaryMono (v : Nat) {i j : Nat} (h:i≤j) :
    (summary v i).2 ≤ (summary v j).2 ∧ (summary v j).2 ≤ (summary v i).2+2*(j-i) := by
  induction j with
  | zero => have :i=0 := by omega
            subst i;simp
  | succ j ih =>
    by_cases z:i=j+1
    · subst i;simp
    · obtain ⟨a,b⟩:=ih (by omega)
      rw [summarySucc];dsimp only
      have:=moveBound (summary v j).1 (digit v j);omega

end PEqualNP.Outside.L_meta_25545_aux

namespace PEqualNP.Outside.L_meta_25545_aux
open PEqualNP.Outside.L_meta_25545_aux.Scan (move summary scan)

lemma orPack {v j d : Nat} (hv : v < 8^j) :
    v ||| (d <<< (3*j)) = v + d*(8^j) := by
  rw [Nat.shiftLeft_eq]
  have power : 2^(3*j)=8^j := by rw [pow_mul]; rfl
  rw [power,Nat.add_comm,Nat.mul_comm d]
  rw [show 8^j=2^(3*j) by exact power.symm]
  rw [Nat.two_pow_add_eq_or_of_lt (by simpa only [power] using hv) d,Nat.or_comm]
lemma digDiv (v j : Nat) : digit v j = (v / 8^j) % 8 := by
  rw [digit,Nat.shiftRight_eq_div_pow, pow_mul];rfl
lemma digAddSmall {v j n : Nat} (h : j<n) (z : Nat) :
    digit (v+z*8^n) j=digit v j := by
  rw [digDiv,digDiv]
  obtain ⟨d,rfl⟩ : ∃ d, n=(j+1)+d := ⟨n-(j+1),by omega⟩
  rw [pow_add,pow_succ]
  have eq : z*(8^j*8*8^d)=8^j*(8*(z*8^d)) := by ring
  rw [eq,Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
lemma digLast {v j : Nat} (hv : v<8^j) (z : Nat) (hz:z<8) :
    digit (v+z*8^j) j=z := by
  rw [digDiv,Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hv,Nat.zero_add,Nat.mod_eq_of_lt hz]
lemma rawDigitLt {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (w m t e : Nat) :
    rawDigit u c w m t e < 8 :=
  (show ∀ a b c : Bool,a.toNat+2*b.toNat+4*c.toNat<8 by decide) _ _ _
lemma traceSucc {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (q w n : Nat) :
    trace u c q w (n+1) =
      let x:=trace u c q w n
      let d:=rawDigit u c w x.1 (tick n) (q-13-3*n+x.2.1)
      let res:=move x.1 d
      (res.1,x.2.1+res.2,x.2.2 ||| (d <<< (3*n))) := by
  simp only [trace,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
lemma sumAgree {v z n : Nat} (ag : ∀ j<n, digit v j=digit z j) : summary v n=summary z n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [summarySucc,summarySucc,ih (fun j hj=>ag _ (by omega)),ag n (by omega)]

lemma normalized {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (q w a : Nat) :
    let t:=trace u c q w a
    t.2.2 < 8^a ∧ (t.1,t.2.1)=summary t.2.2 a ∧ prefixOK u c q t.2.2 w a := by
  induction a with
  | zero => simp [trace,scan,prefixOK]
  | succ n ih =>
    let z:=trace u c q w n
    let val:=rawDigit u c w z.1 (tick n) (q-13-3*n+z.2.1)
    let v:=z.2.2+val*8^n
    have hi : z.2.2<8^n := ih.1
    have hd : val<8 := rawDigitLt ..
    have hsum (j : Nat) (hj:j≤n) : summary v j=summary z.2.2 j :=
      sumAgree (fun i h=>digAddSmall (by omega) val)
    have last : digit v n=val := digLast hi val hd
    have first : z.1=(summary z.2.2 n).1 := congrArg Prod.fst ih.2.1
    have second : z.2.1=(summary z.2.2 n).2 := congrArg Prod.snd ih.2.1
    rw [traceSucc]
    change z.2.2 ||| val <<< (3*n) < 8^(n+1) ∧
      ((move z.1 val).1,z.2.1+(move z.1 val).2)=summary (z.2.2 ||| val <<< (3*n)) (n+1) ∧
      prefixOK u c q (z.2.2 ||| val <<< (3*n)) w (n+1)
    rw [orPack hi]
    refine ⟨?_,?_,?_⟩
    · have h:= Nat.mul_le_mul_right (8^n) (show val+1≤8 by omega)
      rw [pow_succ];simp only [Nat.add_mul,Nat.one_mul] at h;omega
    · change _=summary v (n+1)
      rw [summarySucc,hsum n (by omega),last,←first,←second]
    · intro j hj
      change rawDigit u c w (summary v j).1 (tick j) (q-13-3*j+(summary v j).2)=digit v j
      rw [hsum j (by omega)]
      by_cases e : j=n
      · subst j;rw [last,←first,←second]
      · rw [show digit v j=digit z.2.2 j by exact digAddSmall (by omega) val];exact ih.2.2 j (by omega)

lemma traceIff {k v a : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (q w : Nat) (hv:v<8^a) :
    (trace u c q w a).2.2=v ↔ prefixOK u c q v w a := by
  constructor
  · intro e;simpa only [e] using (normalized u c q w a).2.2
  · intro h
    have aux (j : Nat) (hj:j≤a) : trace u c q w j=((summary v j).1,(summary v j).2,v % 8^j) := by
      induction j with
      | zero => simp [trace,scan,Nat.mod_one]
      | succ j ih =>
        rw [traceSucc,ih (by omega)]
        dsimp only
        change (_,_,v % 8^j ||| (rawDigit u c w (summary v j).1 (tick j) (edge q v j) <<< (3*j)))=_
        rw [h j (by omega),orPack (Nat.mod_lt _ (by positivity)),summarySucc,pow_succ,Nat.mod_mul]
        simp only [edge] at *
        rw [show rawDigit u c w (summary v j).1 (tick j) (q-13-3*j+(summary v j).2)=digit v j by exact h j (by omega)]
        rw [digDiv v j,Nat.mul_comm (v / 8^j % 8)]
    rw [aux a (by omega),Nat.mod_eq_of_lt hv]
end PEqualNP.Outside.L_meta_25545_aux

namespace PEqualNP.Outside.L_meta_25545_aux
open PEqualNP.Outside.L_meta_25545_aux.Line.Right
open PEqualNP.Outside.L_meta_25545_aux.Scan (move)
namespace Front
def one (P J : Src) (e : Nat) := cell P J e == !(xor (xor (grd P (e+2)) (J (e+1))) (J (e+2)))
def two (P J : Src) (e : Nat) := cell P J (e-1) == J (e+2)
def term (Y : Src) (e : Nat) :=
  !(tri (Y (e-1)) (Y e) (Y (e+1))) && tri (Y e) (Y (e+1)) (Y (e+2))
lemma algebra (A X Y Z j v : Bool) :
  let mid := !(xor (xor A j) v)
  let n := xor (xor A (!X && Y)) j
  let m := xor (xor X (!Y && Z)) v
  (!(tri v mid n) && tri mid n m)=false := by
  cases A <;> cases X <;> cases Y <;> cases Z <;> cases j <;> cases v <;> decide

lemma alignOne (P J : Src) (e : Nat) (ho : one P J e=true) (ht : two P J e=true) :
    term (cell P J) e=false := by
  unfold one at ho;unfold two at ht
  rw [beq_iff_eq] at ho ht
  unfold term
  rw [ht,ho]
  let a := tri (P e) (P (e+1)) (P (e+2))
  have old : grd P (e+2)=a := by simp only [grd,a,show e+2-2=e by omega,show e+2-1=e+1 by omega]
  rw [old]
  simp only [cell,show e+1-1=e by omega,show e+2-1=e+1 by omega,show e+1+1=e+2 by omega,
    show e+1+2=e+3 by omega,show e+1+3=e+4 by omega,show e+2+1=e+3 by omega,show e+2+2=e+4 by omega,show e+2+3=e+5 by omega]
  exact algebra ..

lemma alignTwo (Y : Src) (e : Nat) (ht : Y (e-1)=Y (e+2)) : term Y e=false := by
  unfold term;rw [ht]
  cases Y e <;> cases Y (e+1) <;> cases Y (e+2) <;> decide

lemma extra (Y A : Src) {e : Nat} (he : 3≤e) (bz : term Y e=false) :
    cell Y A (e-1)=xor (grd Y e) (A (e-1)) := by
  unfold cell
  unfold term at bz
  simp only [show e-1-1=e-2 by omega,show e-1+1=e by omega,show e-1+2=e+1 by omega,show e-1+3=e+2 by omega,
    bz,Bool.xor_false,grd]

def dig (a b h : Bool) := a.toNat+2*b.toNat+4*h.toNat
def align (mode : Nat) (a b : Bool) := ((mode==1) && a && b) || ((mode==2) && b)
lemma moveDig (mode : Nat) (a b h : Bool) :
    PEqualNP.Outside.L_meta_25545_aux.Scan.move mode (dig a b h) =
      (if align mode a b then (if h then 0 else 2) else 1,h.toNat+(align mode a b && h).toNat) := by
  unfold PEqualNP.Outside.L_meta_25545_aux.Scan.move dig align
  by_cases m1 : mode=1 <;> by_cases m2 : mode=2 <;> simp only [beq_iff_eq,show ∀ n m : Nat, (n==m)=decide (n=m) by intros; rfl,m1,m2] <;> cases a <;> cases b <;> cases h <;> simp [m1,m2] <;> decide

def inv (mode e : Nat) (P P' J J' : Src) : Prop :=
  PrefixEq (cell P J) (cell P' J') e ∧
  (mode=1 → grd P (e+2)=grd P' (e+2)) ∧
  (mode=2 → cell P J (e+2)=J (e+2) ∧ cell P' J' (e+2)=J' (e+2))

lemma next {e mode : Nat} {P P' J J' A A' : Src} {ob tb : Bool}
    (he : 8≤e) (h : inv mode e P P' J J') (ja : PrefixEq J J' (e+2)) (aa : PrefixEq A A' (e+2))
    (o : mode=1 → ob=one P J e) (b : mode≠0 → tb=two P J e) :
    let H := grd (cell P J) e
    let res := PEqualNP.Outside.L_meta_25545_aux.Scan.move mode (dig ob tb H)
    inv res.1 (e-3+res.2) (cell P J) (cell P' J') A A' := by
  let Y := cell P J
  let Z := cell P' J'
  let H := grd Y e
  let m := align mode ob tb
  have agree : PrefixEq Y Z e := h.1
  have hg : grd Y e=grd Z e := guardEq agree
  have adv := PEqualNP.Outside.L_meta_25545_aux.Line.Right.move (e:=e) (by omega) agree (show PrefixEq A A' e from fun n hn=>aa n (by omega))
  have aligned (yes : m=true) : term Y e=false ∧ term Z e=false := by
    have cases' : (mode=1 ∧ ob=true ∧ tb=true) ∨ (mode=2 ∧ tb=true) := by
      simpa [m,align,and_assoc] using yes
    rcases cases' with ⟨md,ox,tx⟩|⟨md,tx⟩
    · have ofst := (o md).symm.trans ox
      have tsnd := (b (by omega)).symm.trans tx
      have oo : one P J e=one P' J' e := by
        change (Y e == _) = (Z e == _)
        rw [agree _ (by omega),h.2.1 md,ja (e+1) (by omega),ja (e+2) (by omega)]
      have tt : two P J e=two P' J' e := by
        change (Y (e-1) == J (e+2)) = (Z (e-1) == J' (e+2))
        rw [agree _ (by omega),ja _ (by omega)]
      exact ⟨alignOne P J e ofst tsnd,alignOne P' J' e (oo.symm.trans ofst) (tt.symm.trans tsnd)⟩
    · have tsnd := (b (by omega)).symm.trans tx
      change (Y (e-1)==J (e+2))=true at tsnd
      have past := h.2.2 md
      exact ⟨alignTwo Y e ((beq_iff_eq.mp tsnd).trans past.1.symm),
        alignTwo Z e ((agree _ (by omega)).symm.trans ((beq_iff_eq.mp tsnd).trans ((ja _ (by omega)).trans past.2.symm)))⟩
  dsimp only
  rw [moveDig]
  change inv (if m then (if H then 0 else 2) else 1) (e-3+(H.toNat+(m && H).toNat)) Y Z A A'
  cases am : m <;> cases hh : H <;> simp only [am,hh,Bool.toNat_true,Bool.toNat_false,
    Bool.false_and,Bool.true_and,Bool.false_eq_true,ite_true,ite_false,Nat.add_zero,Nat.zero_add] <;>
    constructor
  all_goals try (simpa [H,hh] using adv)
  all_goals try (constructor; intro h; exact guardEq (e:=_) (fun n hn => agree n (by omega)); intro nope;omega)
  all_goals try (constructor;intro nope;omega;intro nope;omega)
  all_goals try change PrefixEq (cell Y A) (cell Z A') _ at adv
  all_goals try (intro p hp; by_cases hp' : p≤e-3+(grd Y e).toNat
                 · exact adv p hp'
                 · change grd Y e=true at hh
                   simp [hh] at hp'
                   have ep : p=e-1 := by omega
                   subst p
                   rw [extra Y A (by omega) (aligned am).1,extra Z A' (by omega) (aligned am).2,hg,aa _ (by omega)])
  all_goals try (constructor
                 · intro nope;omega
                 · intro _
                   have ep : e-3+2=e-1 := by omega
                   change grd Y e=false at hh
                   rw [ep,extra Y A (by omega) (aligned am).1,extra Z A' (by omega) (aligned am).2,←hg,hh]
                   simp)
end Front
end PEqualNP.Outside.L_meta_25545_aux

namespace PEqualNP.Outside.L_meta_25545_aux
open PEqualNP.Outside.L_meta_25545_aux.Line (lineStep lInj lGuard cut)
open PEqualNP.Outside.L_meta_25545_aux.Line.Right (cell grd PrefixEq)
open PEqualNP.Outside.L_meta_25545_aux.Word (word39)
open PEqualNP.Outside.L_meta_25545_aux.Scan (move summary)
namespace Bridge
variable {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k))
abbrev S := Nat → Bool
def prev (f : S) (j : Nat) := lineStep k u c f (3+j)
def add (f : S) (j : Nat) := lInj u c f (4+j)
def cur (f : S) (j : Nat) := cell (prev u c f j) (add u c f j)

lemma curEq (f : S) (j : Nat) : lineStep k u c f (4+j)=cur u c f j := by
  funext p
  rw [show 4+j=(3+j)+1 by omega,PEqualNP.Outside.L_meta_25545_aux.Line.Right.stepEq]
  rw [show 3+j+1=4+j by omega]
  rfl

lemma obsOne (f : S) (m j e : Nat) : lineOne u c f m (tick j) e =
  if m=1 then Front.one (prev u c f j) (add u c f j) e else f (e+3-2*tick j+2) := by
  simp only [lineOne,tick,show ∀ j : Nat,5+j-1=4+j by omega,show ∀ j : Nat,5+j-2=3+j by omega,
    curEq,Front.one,prev,add,cur,lGuard,grd,PEqualNP.Outside.L_meta_25545_aux.Line.Right.tri,beq_iff_eq]

lemma obsTwo (f : S) (m j e : Nat) : lineTwo u c f m (tick j) e =
  if m=0 then f (e+3-2*tick j+1) else Front.two (prev u c f j) (add u c f j) e := by
  simp only [lineTwo,tick,show ∀ j : Nat,5+j-1=4+j by omega,curEq,Front.two,cur,add,beq_iff_eq]

lemma obsHit (f : S) (j e : Nat) : lGuard u c f (tick j-1) e = grd (cur u c f j) e := by
  simp only [lGuard,grd,PEqualNP.Outside.L_meta_25545_aux.Line.Right.tri,tick,show ∀ j : Nat,5+j-1=4+j by omega,curEq]

lemma rawQueries {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (w : Fin (2^k))
    (hk : 6≤k) (m t e : Nat) (ht : 5≤t) (he : 2*t+5≤e) :
    rawOne u c w.val m t e=lineOne u c (word39 u w) m t e ∧
    rawTwo u c w.val m t e=lineTwo u c (word39 u w) m t e ∧
    PEqualNP.Outside.L_meta_25545_aux.Word.par u c w.val (t-1) e=lGuard u c (word39 u w) (t-1) e := by
  have bit (s p : Nat) (hp : 2*s≤p) :
      lineStep k u c (word39 u w) s p = PEqualNP.Outside.L_meta_25545_aux.Word.rawBit u c w.val s p :=
    PEqualNP.Outside.L_meta_25545_aux.Line.lineStep_eq_stateAt (by omega) u c w s p hp
  have inp (s p : Nat) (hs : 1≤s) (hp : 2*s≤p) :
      lInj u c (word39 u w) s p = PEqualNP.Outside.L_meta_25545_aux.Word.inj c w.val s p :=
    PEqualNP.Outside.L_meta_25545_aux.Line.injRaw hk hs hp w.isLt u c
  simp (disch := omega) only [lineOne,lineTwo,lGuard,rawOne,rawTwo,PEqualNP.Outside.L_meta_25545_aux.Word.par,bit,inp,word39,true_and]

lemma bounds (q v j : Nat) (big : 5*j+35≤q) : 2*tick j+5≤edge q v j ∧ edge q v j+13≤q := by
  have gg := summaryMono v (i:=0) (j:=j) (Nat.zero_le j)
  have zero : (summary v 0).2=0 := rfl
  rw [zero] at gg;unfold edge tick;omega

lemma eqObs {f g : S} (m j e q : Nat) (top : e+13≤q) (same : ∀ n, n<q → f n=g n)
    (h : Front.inv m e (prev u c f j) (prev u c g j) (add u c f j) (add u c g j)) :
    lineOne u c f m (tick j) e=lineOne u c g m (tick j) e ∧
    lineTwo u c f m (tick j) e=lineTwo u c g m (tick j) e ∧
    lGuard u c f (tick j-1) e=lGuard u c g (tick j-1) e := by
  have input (p : Nat) (hp : p≤e+2) : add u c f j p=add u c g j p := by
    unfold add lInj;rw [same _ (by omega)]
  rw [obsOne,obsOne,obsTwo,obsTwo,obsHit,obsHit]
  constructor
  · split
    · next hm => unfold Front.one;rw [h.1 e (by omega),h.2.1 hm,input _ (by omega),input _ (by omega)]
    · exact same _ (by omega)
  constructor
  · split
    · exact same _ (by omega)
    · unfold Front.two;rw [h.1 (e-1) (by omega),input _ (by omega)]
  · exact PEqualNP.Outside.L_meta_25545_aux.Line.Right.guardEq h.1
end Bridge
end PEqualNP.Outside.L_meta_25545_aux

namespace PEqualNP.Outside.L_meta_25545_aux
open PEqualNP.Outside.L_meta_25545_aux.Line (lineStep lInj lGuard cut)
open PEqualNP.Outside.L_meta_25545_aux.Line.Right (PrefixEq grd)
open PEqualNP.Outside.L_meta_25545_aux.Word (word39 par)
open PEqualNP.Outside.L_meta_25545_aux.Scan (move summary)
open Bridge
private lemma initial45 {k q : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) {f g : S}
    (same : ∀ p, p<q → f p=g p) (s p : Nat) (h : p+3*s<q) :
    lineStep k u c f s p=lineStep k u c g s p := by
  induction s generalizing p with
  | zero => exact same p (by omega)
  | succ s ih =>
    rw [PEqualNP.Outside.L_meta_25545_aux.Line.Right.stepEq,PEqualNP.Outside.L_meta_25545_aux.Line.Right.stepEq]
    unfold PEqualNP.Outside.L_meta_25545_aux.Line.Right.cell lInj
    rw [ih _ (by omega),ih _ (by omega),ih _ (by omega),ih _ (by omega),ih _ (by omega),same _ (by omega)]

lemma cutInv45 {k q v j : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (w : Fin (2^k))
    (hk : 6≤k) (big : 5*j+35≤q) (pre : prefixOK u c q v w.val j) :
    let f := word39 u w
    let g := cut q f
    Front.inv (summary v j).1 (edge q v j) (prev u c f j) (prev u c g j) (add u c f j) (add u c g j) := by
  let f := word39 u w
  let g := cut q f
  have same (n : Nat) (lt : n<q) : f n=g n := by simp [g,cut,lt]
  induction j with
  | zero =>
    change Front.inv 0 (q-13) (prev u c f 0) (prev u c g 0) (add u c f 0) (add u c g 0)
    constructor
    · intro n hn
      change cur u c f 0 n=cur u c g 0 n
      rw [←curEq,←curEq]
      exact initial45 u c same 4 n (by omega)
    · exact ⟨by omega,by omega⟩
  | succ j ih =>
    let e := edge q v j
    let m := (summary v j).1
    let t := tick j
    have last := ih (by omega) (fun i hi => pre i (by omega))
    have bd := bounds q v j (by omega)
    have eLo : 2*t+5≤e := bd.1
    have eHi : e+13≤q := bd.2
    have he : 8≤e := by dsimp [t,tick] at eLo;omega
    have injEq (s : Nat) : PrefixEq (lInj u c f s) (lInj u c g s) (e+2) := by
      intro n hn;unfold lInj;rw [same _ (by omega)]
    let ob := lineOne u c f m t e
    let tb := lineTwo u c f m t e
    have o (h:m=1) : ob=Front.one (prev u c f j) (add u c f j) e := by
      dsimp [ob,t];rw [obsOne,if_pos h]
    have b (h:m≠0) : tb=Front.two (prev u c f j) (add u c f j) e := by
      dsimp [tb,t];rw [obsTwo,if_neg h]
    have hnew := Front.next (mode:=m) (e:=e) he last (injEq (4+j)) (injEq (4+(j+1))) o b
    have raw := rawQueries u c w hk m t e (by dsimp [t,tick];omega) eLo
    have digEq : Front.dig ob tb (grd (cur u c f j) e)=digit v j := by
      specialize pre j (by omega)
      change rawDigit u c w.val m t e = digit v j at pre
      unfold Front.dig
      change ob.toNat+2*tb.toNat+4*(grd (cur u c f j) e).toNat=_
      rw [←obsHit,←raw.2.2]
      change (lineOne u c (word39 u w) m t e).toNat+2*(lineTwo u c (word39 u w) m t e).toNat+_=_
      rw [←raw.1,←raw.2.1];exact pre
    let res := move m (digit v j)
    have sm : summary v (j+1)=(res.1,(summary v j).2+res.2) := summarySucc v j
    have ed : edge q v (j+1)=e-3+res.2 := by
      unfold edge;rw [sm];dsimp only
      dsimp [e,edge]
      omega
    have shift (z : S) : prev u c z (j+1)=cur u c z j := by
      change lineStep k u c z (3+(j+1))=_
      rw [show 3+(j+1)=4+j by omega,curEq]
    change Front.inv (summary v (j+1)).1 (edge q v (j+1)) (prev u c f (j+1)) (prev u c g (j+1)) _ _
    rw [ed,sm,shift,shift]
    dsimp only at hnew
    change Front.inv (move m (Front.dig ob tb (grd (cur u c f j) e))).1
      (e-3+(move m (Front.dig ob tb (grd (cur u c f j) e))).2) _ _ _ _ at hnew
    rw [digEq] at hnew
    exact hnew

lemma cutPrefix45 {k q v j : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (w : Fin (2^k))
    (hk : 6≤k) (big : 5*j+35≤q) (pre : prefixOK u c q v w.val j) :
    PrefixEq (lineStep k u c (word39 u w) (4+j)) (lineStep k u c (cut q (word39 u w)) (4+j)) (edge q v j) := by
  rw [curEq,curEq]
  exact (cutInv45 u c w hk big pre).1

lemma cutQueries45 {k q v j : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (w : Fin (2^k))
    (hk : 6≤k) (big : 5*j+35≤q) (pre : prefixOK u c q v w.val j) :
    let t:=tick j
    let e:=edge q v j
    let mode:=(summary v j).1
    let f:=cut q (word39 u w)
    rawOne u c w.val mode t e=lineOne u c f mode t e ∧ rawTwo u c w.val mode t e=lineTwo u c f mode t e ∧
      par u c w.val (t-1) e=lGuard u c f (t-1) e := by
  dsimp only
  let mode := (summary v j).1
  have bd := bounds q v j big
  have raw := rawQueries u c w hk mode (tick j) (edge q v j) (by unfold tick;omega) bd.1
  have eqs := eqObs u c mode j (edge q v j) q bd.2
    (f:=word39 u w) (g:=cut q (word39 u w)) (fun n lt => by simp [cut,lt]) (cutInv45 u c w hk big pre)
  exact ⟨raw.1.trans eqs.1,raw.2.1.trans eqs.2.1,raw.2.2.trans eqs.2.2⟩
end PEqualNP.Outside.L_meta_25545_aux

namespace PEqualNP.Outside.L_meta_25545_aux
open PEqualNP.Outside.L_meta_25545_aux.Scan (move summary scan_gain_le)
open PEqualNP.Outside.L_meta_25545_aux.Word (src par word39)
open PEqualNP.Outside.L_meta_25545_aux.Word.Layout (inputWord)
open PEqualNP.Outside.L_meta_25545_aux.Recovery.Col97 (recover1Init initRecover1)
structure Params (k : Nat) where
  r : Nat
  d : Nat
  i : Nat
  a : Nat
  v : Nat
  hr : 6≤r
  hkd : k+3+d=5*r
  hd : d≤r-5
  hi : i<k
  him : i+(2*(r-5)-d)≤k
  ha : a≤r-5
  hv : v<8^a
  eligible : a=0 ∨ d<(summary v (a-1)).2+2*(r-5+1-a)
namespace Params
variable {k : Nat} (P : Params k)
abbrev q := k+P.i+3*P.r-P.d
abbrev N := 3*P.a
include P in
lemma kLarge : 16≤k := by have:=P.hr;have:=P.hd;have:=P.hkd;omega
include P in
lemma srcRecover (u x : Fin (2^k)) : src u (inputWord u x).val=x.val :=
  initRecover1 P.kLarge x.isLt u.isLt
include P in
lemma keyRecover (u w : Fin (2^k)) : (inputWord u ⟨src u w.val,
    Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) u.isLt⟩).val=w.val :=
  recover1Init P.kLarge w.isLt
def pp (n : Nat) := left P.q P.v (n/3)+2-n % 3
def pv (n : Nat) : Fin k := ⟨P.pp n % k,Nat.mod_lt _ (by have:=P.kLarge;omega)⟩
lemma big {j : Nat} (hj : j≤P.a) : 5*j+35≤P.q := by
  have:=P.hr;have:=P.hd;have:=P.hkd;have:=P.ha;dsimp [q];omega
lemma interval {n : Nat} (hn:n<P.N) : P.q-k ≤ P.pp n ∧ P.pp n < P.q := by
  have:=P.hr;have:=P.hd;have:=P.hkd;have:=P.ha;have he:=P.eligible
  have lt : n/3<P.a := by dsimp [N] at hn; omega
  have b:=P.big (j:=n/3) (by omega)
  have mono:=summaryMono P.v (i:=n/3) (j:=P.a-1) (by omega)
  have ub:=scan_gain_le P.v (n/3) 0
  dsimp only [pp,left,edge,tick,q,PEqualNP.Outside.L_meta_25545_aux.Scan.summary] at *
  omega
lemma pointwise {n : Nat} (hn:n+1<P.N) : P.pp (n+1)<P.pp n := by
  have h:P.q≥5*(n/3)+35 := P.big (by dsimp [N] at hn;omega)
  by_cases e:n % 3=2
  · have j : (n+1)/3=n/3+1 := by omega
    have g:=moveBound (summary P.v (n/3)).1 (digit P.v (n/3))
    simp only [pp,j,left,edge,tick,summarySucc,show (n+1) % 3=0 by omega,e,Nat.sub_zero];omega
  · simp only [pp,show (n+1)/3=n/3 by omega];omega
lemma decreasing {j t : Nat} (h:j<t) (ht:t<P.N) : P.pp t<P.pp j := by
  induction t with
  | zero => omega
  | succ t ih =>
    have one:=P.pointwise ht
    by_cases e:j=t
    · simpa [e] using one
    · exact lt_trans one (ih (by omega) (by omega))
lemma sameMod {x y : Nat} (xl:P.q-k≤x) (xr:x<P.q) (yl:P.q-k≤y) (yr:y<P.q) (eq:x % k=y % k) : x=y := by
  have qm:k≤P.q := by have:=P.hr;have:=P.hd;dsimp [q];omega
  have f (a b:Nat) (lt:a<b) (bt:b<a+k) (eq:a % k=b % k) : False := by
    have vd:k ∣ b-a := (Nat.modEq_iff_dvd' (Nat.le_of_lt lt)).mp eq
    have := Nat.le_of_dvd (by omega : 0<b-a) vd;omega
  rcases lt_trichotomy x y with h|h|h
  · exact False.elim (f x y h (by omega) eq)
  · exact h
  · exact False.elim (f y x h (by omega) eq.symm)
lemma distinct : ∀ j<P.N, ∀ t<P.N, P.pv j=P.pv t → j=t := by
  intro j hj t ht h
  have same := P.sameMod (P.interval hj).1 (P.interval hj).2 (P.interval ht).1 (P.interval ht).2 (congrArg Fin.val h)
  rcases lt_trichotomy j t with e|e|e
  · have := P.decreasing e ht;omega
  · exact e
  · have := P.decreasing e hj;omega
lemma past {t : Nat} (ht:t<P.N) {x y : Fin (2^k)}
    (same:∀ b:Fin k, ¬PEqualNP.Outside.L_meta_25545_aux.Word.Solver.Future P.pv t P.N b.val →
        x.val.testBit b.val=y.val.testBit b.val)
    (j : Nat) (lo:P.pp t<j) (hr:j<P.q) : x.val.testBit (j % k)=y.val.testBit (j % k) := by
  apply same ⟨j % k,Nat.mod_lt _ (by have:=P.kLarge;omega)⟩
  rintro ⟨z,hz,hl,eq⟩
  have low: P.q-k ≤ j := by have := (P.interval ht).1;omega
  have e:=P.sameMod (P.interval hl).1 (P.interval hl).2 low hr eq
  by_cases ez:t=z
  · subst z;omega
  · have := P.decreasing (by omega : t<z) hl;omega
def obs (u : Fin (2^k)) (c : Nat→Fin (2^k)) (w n : Nat) :=
  let j:=n/3
  let e:=edge P.q P.v j
  let t:=tick j
  let mode:=(summary P.v j).1
  if n % 3=0 then rawOne u c w mode t e else if n % 3=1 then rawTwo u c w mode t e else par u c w (t-1) e
def err (u : Fin (2^k)) (c : Nat→Fin (2^k)) (n : Nat) (x : Fin (2^k)) :=
  xor (P.obs u c (inputWord u x).val n) (P.v.testBit n)

lemma digitBit (v j b : Nat) (h:b<3) : (digit v j).testBit b=v.testBit (3*j+b) := by
  change ((v >>> (3*j)) % 2^3).testBit b = v.testBit (3*j+b)
  rw [Nat.testBit_mod_two_pow];simp only [h,decide_true,Bool.true_and,Nat.testBit_shiftRight]

lemma group (u : Fin (2^k)) (c : Nat→Fin (2^k)) (w j : Nat) :
    (∀ b : Fin 3, P.obs u c w (3*j+b.val)=P.v.testBit (3*j+b.val)) ↔
      rawDigit u c w (summary P.v j).1 (tick j) (edge P.q P.v j)=digit P.v j := by
  let mode := (summary P.v j).1
  let t:=tick j
  let e:=edge P.q P.v j
  let one:=rawOne u c w mode t e
  let two:=rawTwo u c w mode t e
  let g:=par u c w (t-1) e
  have h (v : Fin 8) : ∀ a b c:Bool,a.toNat+2*b.toNat+4*c.toNat=v.val ↔
      a=v.val.testBit 0 ∧ b=v.val.testBit 1 ∧ c=v.val.testBit 2 :=
    (show ∀ v : Fin 8, ∀ a b c : Bool, a.toNat+2*b.toNat+4*c.toNat=v.val ↔
      a=v.val.testBit 0 ∧ b=v.val.testBit 1 ∧ c=v.val.testBit 2 by decide) v
  have eq:=h ⟨digit P.v j,Nat.mod_lt _ (by decide)⟩ one two g
  simp only [digitBit _ _ 0 (by decide),digitBit _ _ 1 (by decide),digitBit _ _ 2 (by decide),Nat.add_zero] at eq
  change _ ↔ one.toNat+2*two.toNat+4*g.toNat=_
  rw [eq]
  have each (b : Fin 3) : P.obs u c w (3*j+b.val)=if b.val=0 then one else if b.val=1 then two else g := by
    have hb:=b.isLt
    simp only [obs,show (3*j+b.val)/3=j by omega,show (3*j+b.val) % 3=b.val by omega]
    rfl
  constructor
  · intro all
    have z:=all 0;have o:=all 1;have b:=all 2
    rw [each] at z o b
    exact ⟨z,o,b⟩
  · rintro ⟨z,o,b⟩ j
    rw [each];fin_cases j <;> first | exact z | exact o | exact b
lemma xorFalse (a b : Bool) : xor a b=false ↔ a=b := by cases a <;>cases b <;>decide
lemma earlierPrefix {u x : Fin (2^k)} {c : Nat→Fin (2^k)} {t j : Nat} (h:3*j≤t)
    (g : PEqualNP.Outside.L_meta_25545_aux.Word.Solver.Good (P.err u c) t x) :
    prefixOK u c P.q P.v (inputWord u x).val j := by
  intro z hz
  apply (P.group u c (inputWord u x).val z).mp
  intro b
  have := b.isLt
  exact (xorFalse ..).mp (g _ (by omega : 3*z+b.val<t))
lemma goodIff (u : Fin (2^k)) (c : Nat→Fin (2^k)) (x : Fin (2^k)) :
    PEqualNP.Outside.L_meta_25545_aux.Word.Solver.Good (P.err u c) P.N x ↔ (trace u c P.q (inputWord u x).val P.a).2.2=P.v := by
  rw [traceIff _ _ _ _ P.hv]
  constructor
  · exact fun g=>P.earlierPrefix (t:=P.N) (by rfl) g
  · intro good n hn
    let b : Fin 3 := ⟨n % 3,Nat.mod_lt _ (by decide)⟩
    have h: n/3<P.a := by dsimp [N] at hn;omega
    have eq:= (P.group u c (inputWord u x).val (n/3)).mpr (good _ h) b
    rw [show 3*(n/3)+b.val=n by dsimp [b];omega] at eq
    exact (xorFalse ..).mpr eq
end Params
end PEqualNP.Outside.L_meta_25545_aux

namespace PEqualNP.Outside.L_meta_25545_aux
theorem length_filter_range_eq_card_fin (N : Nat) (p : Nat → Bool) :
    ((List.range N).filter p).length =
      ((Finset.univ : Finset (Fin N)).filter (fun x => p x.val = true)).card := by
  have h1 : ((List.range N).filter p).length =
      ((Finset.range N).filter (fun n => p n = true)).card := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [List.range_succ, List.filter_append, List.length_append, Finset.range_add_one,
          Finset.filter_insert]
      by_cases h : p N = true
      · simp [h, ih, Finset.card_insert_of_notMem]
      · have hf : p N = false := Bool.eq_false_iff.2 h
        simp [h, hf, ih]
  rw [h1]
  refine Finset.card_bij (fun n hn => ⟨n, Finset.mem_range.1 (Finset.mem_filter.1 hn).1⟩) ?_ ?_ ?_
  · intro n hn
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hn).2⟩
  · intro n1 _ n2 _ heq
    exact congrArg Fin.val heq
  · intro x hx
    exact ⟨x.val, Finset.mem_filter.2 ⟨Finset.mem_range.2 x.isLt, (Finset.mem_filter.1 hx).2⟩, rfl⟩

open PEqualNP.Outside.L_meta_25545_aux.Word (src)
open PEqualNP.Outside.L_meta_25545_aux.Word.Layout (inputWord)
open PEqualNP.Outside.L_meta_25545_aux.Encoding (encodeBits encBit)
namespace Params
open PEqualNP.Outside.L_meta_25545_aux.Word.Solver
variable {k : Nat} (P : Params k)

lemma count (u : Fin (2^k)) (c : Nat → Fin (2^k))
    (tri : ∀ n<P.N, ∀ x y, Good (P.err u c) n x → Good (P.err u c) n y →
      (∀ b:Fin k, ¬Future P.pv n P.N b.val → x.val.testBit b.val=y.val.testBit b.val) →
      xor (P.err u c n x) (x.val.testBit (P.pv n).val)=
        xor (P.err u c n y) (y.val.testBit (P.pv n).val)) :
    ((List.range (2^k)).filter (fun w => (trace u c P.q w P.a).2.2 == P.v)).length=2^(k-P.N) := by
  classical
  let f : Fin P.N → Fin k := fun n => P.pv n.val
  let M := (Finset.univ : Finset (Fin P.N)).image f
  have cm : M.card=P.N := by
    have hi : Function.Injective f := fun a b eq => Fin.ext (P.distinct a.val a.isLt b.val b.isLt eq)
    simp [M,Finset.card_image_of_injective _ hi]
  have mem (j : Fin k) : j∈M ↔ Future P.pv 0 P.N j.val := by
    simp only [M,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨n,rfl⟩;exact ⟨n.val,by omega,n.isLt,rfl⟩
    · rintro ⟨n,_,hn,eq⟩;exact ⟨⟨n,hn⟩,Fin.ext eq⟩
  let B := {j:Fin k // j∉M}
  let K := (Finset.univ : Finset (Fin (2^k))).filter (fun w => (trace u c P.q w.val P.a).2.2=P.v)
  let bits := fun (w : ↥K) (b : B) => (src u w.val.val).testBit b.val.val
  have good (w:↥K) : (trace u c P.q w.val.val P.a).2.2=P.v := (Finset.mem_filter.mp w.property).2
  let start := fun (w : Fin (2^k)) => (⟨src u w.val,Nat.xor_lt_two_pow (Nat.mod_lt _ (by positivity)) u.isLt⟩ : Fin (2^k))
  have invKey (w:Fin (2^k)) : inputWord u (start w)=w := Fin.ext (P.keyRecover u w)
  have goodStart (w : ↥K) : Good (P.err u c) P.N (start w.val) := (P.goodIff ..).mpr (by rw [invKey];exact good w)
  have hi : Function.Injective bits := by
    intro w z eq
    have cert:=certified P.pv (P.err u c) (start w.val) P.distinct tri
    have w':start w.val=run P.pv (P.err u c) (start w.val) P.N :=
      (cert _).mpr ⟨goodStart w,fun _ _=>rfl⟩
    have z':start z.val=run P.pv (P.err u c) (start w.val) P.N := by
      apply (cert _).mpr
      refine ⟨goodStart z,fun j hj=>?_⟩
      exact (congrFun eq (⟨j,fun hm => hj ((mem j).mp hm)⟩:B)).symm
    apply Subtype.ext
    exact (invKey w.val).symm.trans ((congrArg (inputWord u) (w'.trans z'.symm)).trans (invKey z.val))
  have hs : Function.Surjective bits := by
    intro g
    let seed:=encodeBits k (fun n => if h:n<k then
      (if m:(⟨n,h⟩:Fin k)∈M then false else g ⟨⟨n,h⟩,m⟩) else false)
    let x := run P.pv (P.err u c) seed P.N
    obtain ⟨gx,off⟩ := (certified P.pv (P.err u c) seed P.distinct tri x).mp rfl
    have wk : inputWord u x ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(P.goodIff ..).mp gx⟩
    refine ⟨⟨inputWord u x,wk⟩,?_⟩
    funext b
    change (src u (inputWord u x).val).testBit b.val.val=g b
    rw [P.srcRecover,off b.val (fun hf => b.property ((mem _).mpr hf))]
    simp [seed,encBit b.val.isLt,b.val.isLt,b.property]
  have hcard := Fintype.card_congr (Equiv.ofBijective bits ⟨hi,hs⟩)
  have cb : Fintype.card B=k-P.N := by
    change Fintype.card {j:Fin k // ¬j∈M} = _
    rw [Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_coe,cm]
  rw [length_filter_range_eq_card_fin]
  simp only [beq_iff_eq]
  change K.card=_
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_bool,cb] using hcard
end Params
end PEqualNP.Outside.L_meta_25545_aux

namespace PEqualNP.Outside.L_meta_25545_aux
open PEqualNP.Outside.L_meta_25545_aux.Line (lineStep stateAt cut lineStep_eq_stateAt lineStep_xor_pivot lInj)
open PEqualNP.Outside.L_meta_25545_aux.Word (word39 src)
open PEqualNP.Outside.L_meta_25545_aux.Scan (summary scan_gain_le)
namespace Params
variable {k : Nat} (P : Params k)
lemma terminal (u : Fin (2^k)) (c : Nat → Fin (2^k))
    (bridgeCut : ∀ w:Fin (2^k), prefixOK u c P.q P.v w.val P.a →
      PEqualNP.Outside.L_meta_25545_aux.Line.Right.PrefixEq
        (lineStep k u c (word39 u w) (4+P.a)) (lineStep k u c (cut P.q (word39 u w)) (4+P.a)) (edge P.q P.v P.a))
    (done : P.a=P.r-5) (x y : Fin (2^k)) (j : Fin ((summary P.v P.a).2-P.d))
    (hx : (trace u c P.q x.val P.a).2.2=P.v) (hy : (trace u c P.q y.val P.a).2.2=P.v)
    (same : ∀ p : Fin k, (∀ b : Nat,b≤j.val → (P.q+b) % k≠p.val) →
      (src u x.val).testBit p.val=(src u y.val).testBit p.val) :
    xor ((stateAt k u c P.r x.val).testBit (P.i+j.val)) ((stateAt k u c P.r y.val).testBit (P.i+j.val)) =
      xor ((src u x.val).testBit ((P.q+j.val) % k)) ((src u y.val).testBit ((P.q+j.val) % k)) := by
  let p:=k+P.i+j.val
  let a:=4+P.a
  have hr:=P.hr; have hk:=P.hkd;have hd:=P.hd;have hl:=P.him
  have hpos : 2*P.r≤p := by dsimp [p];omega
  have gl := scan_gain_le P.v P.a 0
  have js:=j.isLt
  have hi:P.i+j.val<k := by change (summary P.v P.a).2≤2*P.a at gl; omega
  have hm : p % k=P.i+j.val := by dsimp [p];rw [show k+P.i+j.val=(P.i+j.val)+k by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hi]
  have ep : p+3≤edge P.q P.v P.a := by dsimp [p,edge,q];omega
  have eb : edge P.q P.v P.a+4≤P.q := by
    change (summary P.v P.a).2≤2*P.a at gl
    have big:=P.big (j:=P.a) (by omega)
    dsimp [edge];omega
  have pivot : p+3-2*P.r=P.q+j.val-k := by dsimp [p,q];omega
  have pk : P.q+j.val-k<P.q := by have := P.big (j:=0) (by omega);dsimp only [q] at *;omega
  have pm : (P.q+j.val-k) % k=(P.q+j.val) % k := by
    conv_rhs => rw [show P.q+j.val=(P.q+j.val-k)+k by dsimp [q];omega,Nat.add_mod_right]
  have bridge (w : Fin (2^k)) (pre : (trace u c P.q w.val P.a).2.2=P.v) :
      (stateAt k u c P.r w.val).testBit (P.i+j.val)=lineStep k u c (cut P.q (word39 u w)) P.r p := by
    have base := bridgeCut w ((traceIff u c _ _ P.hv).mp pre)
    have right : lineStep k u c (word39 u w) P.r p=lineStep k u c (cut P.q (word39 u w)) P.r p := by
      rw [show P.r=(4+P.a)+1 by omega,PEqualNP.Outside.L_meta_25545_aux.Line.Right.stepEq,
        PEqualNP.Outside.L_meta_25545_aux.Line.Right.stepEq]
      unfold PEqualNP.Outside.L_meta_25545_aux.Line.Right.cell lInj
      rw [base _ (by omega),base _ (by omega),base _ (by omega),base _ (by omega),base _ (by omega)]
      simp [cut,show p+3-2*(4+P.a+1)<P.q by omega]
    have fromRaw:=lineStep_eq_stateAt (by have:=P.kLarge;omega : 2≤k) u c w P.r p hpos
    rw [hm] at fromRaw
    exact fromRaw.symm.trans right
  rw [bridge x hx,bridge y hy]
  have delta := lineStep_xor_pivot k u c (cut P.q (word39 u x)) (cut P.q (word39 u y)) P.r p (by omega) hpos (fun n lo _ => by
    by_cases hn:n<P.q
    · simp only [cut,ite_eq_left hn]
      apply same ⟨n % k,Nat.mod_lt _ (by have:=P.kLarge;omega)⟩
      intro b hb eq
      have small : 0 < P.q+b-n := by omega
      have dvd : k ∣ P.q+b-n := (Nat.modEq_iff_dvd' (by omega : n≤P.q+b)).mp eq.symm
      have := Nat.le_of_dvd small dvd
      omega
    · simp [cut,hn])
  rw [pivot] at delta
  simpa only [cut,ite_eq_left pk,word39,pm] using delta

end Params
end PEqualNP.Outside.L_meta_25545_aux

namespace PEqualNP.Outside.L_meta_25545_aux
open PEqualNP.Outside.L_meta_25545_aux.Line (lineStep lInj lGuard cut gPivot lineStep_agree_interval lineStep_xor_pivot)
open PEqualNP.Outside.L_meta_25545_aux.Word (par src word39)
open PEqualNP.Outside.L_meta_25545_aux.Word.Layout (inputWord)
open PEqualNP.Outside.L_meta_25545_aux.Scan (summary)

private theorem alignXor (f g c d : Bool) (h : xor f g=c) :
    xor (f==d) (g==d)=c := by subst c; cases f <;> cases g <;> cases d <;> rfl

lemma onePivot {k : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (f g : Nat→Bool) (m t e : Nat)
    (ht:5≤t) (he:2*t+5≤e) (ag:∀ n,e+3-2*t+2<n → f n=g n) :
    xor (lineOne u c f m t e) (lineOne u c g m t e) = xor (f (e+3-2*t+2)) (g (e+3-2*t+2)) := by
  unfold lineOne
  by_cases hm : (m==1)=true
  · simp only [hm,ite_true]
    let L:= e+3-2*t+3
    have old (p : Nat) (pl:e≤p) : lineStep k u c f (t-2) p=lineStep k u c g (t-2) p :=
      lineStep_agree_interval k u c f g L (p+3*(t-2)) (fun n hn _ => ag n (by dsimp [L] at hn;omega))
        _ p (by dsimp [L];omega) (by omega)
    have oldGuard : lGuard u c f (t-2) (e+2)=lGuard u c g (t-2) (e+2) := by
      unfold lGuard
      rw [old _ (by omega),old _ (by omega),old _ (by omega)]
    have injs (p : Nat) (hp:e+1≤p) : lInj u c f (t-1) p=lInj u c g (t-1) p := by
      unfold lInj;rw [ag _ (by omega)]
    rw [oldGuard,injs _ (by omega),injs _ (by omega)]
    apply alignXor
    have eq:=lineStep_xor_pivot k u c f g (t-1) e (by omega) (by omega) (fun n hn _ => ag _ (by omega))
    rwa [show e+3-2*(t-1)=e+3-2*t+2 by omega] at eq
  · simp only [hm,Bool.false_eq_true,ite_false]

lemma twoPivot {k : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (f g : Nat→Bool) (m t e : Nat)
    (ht:5≤t) (he:2*t+5≤e) (ag:∀ n,e+3-2*t+1<n → f n=g n) :
    xor (lineTwo u c f m t e) (lineTwo u c g m t e) = xor (f (e+3-2*t+1)) (g (e+3-2*t+1)) := by
  unfold lineTwo
  by_cases hm : (m==0)=true
  · simp only [hm,ite_true]
  · simp only [hm,Bool.false_eq_true,ite_false]
    have ins : lInj u c f (t-1) (e+2)=lInj u c g (t-1) (e+2) := by unfold lInj;rw [ag _ (by omega)]
    rw [ins]
    apply alignXor
    have eq:=lineStep_xor_pivot k u c f g (t-1) (e-1) (by omega) (by omega) (fun n hn _ => ag _ (by omega))
    rwa [show e-1+3-2*(t-1)=e+3-2*t+1 by omega] at eq

namespace Params
open PEqualNP.Outside.L_meta_25545_aux.Word.Solver
variable {k : Nat} (P : Params k)
theorem mainTri (u : Fin (2^k)) (c : Nat→Fin (2^k)) :
    ∀ n<P.N, ∀ x y, Good (P.err u c) n x → Good (P.err u c) n y →
      (∀ b:Fin k, ¬Future P.pv n P.N b.val → x.val.testBit b.val=y.val.testBit b.val) →
      xor (P.err u c n x) (x.val.testBit (P.pv n).val)=xor (P.err u c n y) (y.val.testBit (P.pv n).val) := by
  intro n hn x y gx gy same
  let j:=n/3
  let t:=tick j
  let e:=edge P.q P.v j
  let mode:=(summary P.v j).1
  let f:=cut P.q (word39 u (inputWord u x))
  let g:=cut P.q (word39 u (inputWord u y))
  have jl:j<P.a := by dsimp [j];dsimp [N] at hn;omega
  have big:=P.big (j:=j) (by omega)
  have ht:5≤t := by dsimp [t,tick];omega
  have he:2*t+5≤e := by dsimp [e,edge,t,tick];omega
  have rawX:=cutQueries45 u c (inputWord u x) (by have:=P.kLarge;omega) big
    (P.earlierPrefix (j:=j) (by dsimp [j];omega) gx)
  have rawY:=cutQueries45 u c (inputWord u y) (by have:=P.kLarge;omega) big
    (P.earlierPrefix (j:=j) (by dsimp [j];omega) gy)
  have a (n' : Nat) (h:P.pp n<n') : f n'=g n' := by
    by_cases hr:n'<P.q
    · simpa only [f,g,cut,ite_eq_left hr,word39,P.srcRecover] using P.past hn same n' h hr
    · simp [f,g,cut,hr]
  have right : xor (f (P.pp n)) (g (P.pp n))=xor (x.val.testBit (P.pv n).val) (y.val.testBit (P.pv n).val) := by
    simp only [f,g,cut,ite_eq_left (P.interval hn).2,word39,P.srcRecover,pv]
  suffices h : xor (P.obs u c (inputWord u x).val n) (P.obs u c (inputWord u y).val n) =
      xor (f (P.pp n)) (g (P.pp n)) by
    exact (show ∀ a b c d e:Bool, xor a b=xor c d → xor (xor a e) c=xor (xor b e) d by decide) _ _ _ _ _ (h.trans right)
  by_cases z:n % 3=0
  · have which : P.pp n=e+3-2*t+2 := by simp only [pp,z,Nat.sub_zero];rfl
    simp only [obs,z,ite_true,which]
    rw [rawX.1,rawY.1]
    exact onePivot u c f g mode t e ht he (fun n' hh=>a n' (by rwa [which]))
  · by_cases o:n % 3=1
    · have which : P.pp n=e+3-2*t+1 := by unfold pp;rw [o];change e+3-2*t+2-1=_;omega
      simp only [obs,z,o,ite_false,ite_true,which]
      rw [rawX.2.1,rawY.2.1]
      exact twoPivot u c f g mode t e ht he (fun n' hh=>a n' (by rwa [which]))
    · have r:n % 3=2 := by omega
      have which :P.pp n=e+1-2*(t-1) := by unfold pp;rw [r];change e+3-2*t+2-2=_;omega
      simp only [obs,z,o,ite_false,which]
      rw [rawX.2.2,rawY.2.2]
      exact gPivot u c f g (s:=t-1) (e:=e) (by omega) (by omega) (fun n' hh=>a n' (by rwa [which]))
end Params
end PEqualNP.Outside.L_meta_25545_aux

open PEqualNP.Outside.L_meta_25545_aux in
theorem PEqualNP.Outside.L_meta_25545 :
∀ (k r d i : Nat), 6 ≤ r → k + 3 + d = 5 * r →
  let attempts := r - 5
  d ≤ attempts → i < k → i + (2 * attempts - d) ≤ k →
  ∀ constant : Nat → Fin (2 ^ k),
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
  let guard := fun (row round key stop : Nat) =>
    xor (xor (bit row round key (stop - 2)) (bit row round key (stop - 1))) (bit row round key stop)
  let move := fun (mode letter : Nat) =>
    let aligned := ((mode == 1) && letter.testBit 0 && letter.testBit 1) ||
      ((mode == 2) && letter.testBit 1)
    let hit := letter.testBit 2
    (if aligned then (if hit then 0 else 2) else 1,
      hit.toNat + (aligned && hit).toNat)
  let summary := fun (code length : Nat) =>
    (List.range length).foldl (fun (st : Nat × Nat) digitPos =>
      let result := move st.1 ((code >>> (3 * digitPos)) % 8)
      (result.1, st.2 + result.2)) (0, 0)
  let q := k + i + 3 * r - d
  let trace := fun (row key length : Nat) =>
    ((List.range length).foldl (fun (st : Nat × Nat × Nat) idx =>
      let t := 5 + idx
      let edge := q - 13 - 3 * idx + st.2.1
      let left := edge + 3 - 2 * t
      let x := rot 1 key ^^^ row
      let v := injected (t - 1) key (edge + 2)
      let oldMix := guard row (t - 2) key (edge + 2)
      let uBit := xor oldMix (injected (t - 1) key (edge + 1))
      let one := if st.1 == 1 then
        bit row (t - 1) key edge == !(xor uBit v)
        else x.testBit ((left + 2) % k)
      let two := if st.1 == 0 then x.testBit ((left + 1) % k)
        else bit row (t - 1) key (edge - 1) == v
      let hit := guard row (t - 1) key edge
      let digit := one.toNat + 2 * two.toNat + 4 * hit.toNat
      let outcome := move st.1 digit
      (outcome.1, st.2.1 + outcome.2, st.2.2 ||| (digit <<< (3 * idx)))) (0, 0, 0)).2.2
  ∀ (a : Nat) (code : Fin (8 ^ a)), a ≤ attempts →
    (a = 0 ∨ d < (summary code.val (a - 1)).2 + 2 * (attempts + 1 - a)) →
    ∀ rowName : Fin (2 ^ k),
    let keys := (List.range (2 ^ k)).filter (fun raw => trace rowName.val raw a == code.val)
    keys.length = 2 ^ (k - 3 * a) ∧
      (a = attempts →
        let m := (summary code.val a).2 - d
        ∀ (key₁ key₂ : Fin (2 ^ k)) (j : Fin m),
          trace rowName.val key₁.val a = code.val → trace rowName.val key₂.val a = code.val →
          let x₁ := rot 1 key₁.val ^^^ rowName.val
          let x₂ := rot 1 key₂.val ^^^ rowName.val
          (∀ p : Fin k, (∀ b : Nat, b ≤ j.val → (q + b) % k ≠ p.val) →
            x₁.testBit p.val = x₂.testBit p.val) →
          xor ((state rowName.val r key₁.val).testBit (i + j.val))
              ((state rowName.val r key₂.val).testBit (i + j.val)) =
            xor (x₁.testBit ((q + j.val) % k)) (x₂.testBit ((q + j.val) % k))) := by
  intro k r d i hr hkd attempts hd hi him c rot step state injected bit guard move summary q trace a code ha hv u keys
  let P : Params k := ⟨r,d,i,a,code.val,hr,hkd,hd,hi,him,ha,code.isLt,hv⟩
  refine ⟨P.count u c (P.mainTri u c),?_⟩
  intro done m x y j hx hy firstSource secondSource same
  exact P.terminal u c (fun w pre => cutPrefix45 u c w (by have := P.kLarge;omega) (P.big le_rfl) pre)
    done x y j hx hy same
