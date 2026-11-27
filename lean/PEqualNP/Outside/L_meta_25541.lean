import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25541_aux

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
end PEqualNP.Outside.L_meta_25541_aux

namespace PEqualNP.Outside.L_meta_25541_aux

def src {k : Nat} (u : Fin (2^k)) (key n : Nat) := (rot k 1 key ^^^ u.val).testBit (n % k)
def vary {k : Nat} (base : Fin (2^k)) (lo m : Nat) := base.val ^^^ rot k (lo+k-1) m
def cut (q : Nat) (f : Nat → Bool) (n : Nat) := if n<q then f n else false

theorem vary_lt {k : Nat} (base : Fin (2^k)) (lo m : Nat) : vary base lo m < 2^k :=
  xor_lt base.isLt (rot_lt _ _ _)

theorem src_vary {k q lo n : Nat} (hk : 6≤k) (hl : 0<lo) (hn : lo≤n) (hnq : n<q) (hq : q≤lo+k)
    (u base : Fin (2^k)) (m : Fin 64) :
    src u (vary base lo m.val) n = xor (src u base.val n) (m.val.testBit (n-lo)) := by
  have hpos : 0<k := by omega
  have hm : m.val < 2^k := m.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hk)
  have hone : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have hdiff : (n % k+k-1 % k) % k=(n-1) % k := mod_sub_eq hpos (by omega)
  have hshift : ((n-1) % k+k-(lo+k-1) % k) % k=n-lo := by
    have hc := mod_sub_eq (k:=k) (p:=n-1+k) (s:=lo+k-1) hpos (by omega)
    rw [Nat.add_mod_right, show n-1+k-(lo+k-1)=n-lo by omega, Nat.mod_eq_of_lt (by omega : n-lo<k)] at hc
    exact hc
  simp only [src,Nat.testBit_xor]
  rw [testBit_rot (vary_lt base lo m.val) (Nat.mod_lt _ hpos),testBit_rot base.isLt (Nat.mod_lt _ hpos),hdiff]
  simp only [vary,Nat.testBit_xor,testBit_rot hm (Nat.mod_lt _ hpos),hshift]
  generalize base.val.testBit ((n-1) % k) = a
  generalize m.val.testBit (n-lo) = b
  generalize u.val.testBit (n % k) = z
  cases a <;> cases b <;> cases z <;> rfl

theorem cut_tri {k q lo d : Nat} (hk : 6≤k) (hl : 0<lo) (hdq : lo+d<q) (hq : q≤lo+k)
    (u base : Fin (2^k)) (m n : Fin 64)
    (ag : ∀ j, d<j → j<6 → m.val.testBit j=n.val.testBit j) :
    let f := cut q (src u (vary base lo m.val))
    let g := cut q (src u (vary base lo n.val))
    (∀ p, lo+d<p → f p=g p) ∧ xor (f (lo+d)) (g (lo+d)) = xor (m.val.testBit d) (n.val.testBit d) := by
  dsimp only
  constructor
  · intro p hp
    by_cases h : p<q
    · simp only [cut,ite_eq_left h,src_vary hk hl (by omega : lo≤p) h hq]
      by_cases hj : p-lo<6
      · rw [ag _ (by omega) hj]
      · have hm : ∀ a : Fin 64, a.val.testBit (p-lo)=false := fun a =>
          Nat.testBit_lt_two_pow (a.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega : 6≤p-lo)))
        rw [hm m,hm n]
    · simp [cut,h]
  · simp only [cut,ite_eq_left hdq,src_vary hk hl (by omega : lo≤lo+d) hdq hq, Nat.add_sub_cancel_left]
    generalize src u base.val (lo+d)=x
    cases x <;> cases m.val.testBit d <;> cases n.val.testBit d <;> rfl

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

theorem alignPivot {k t e : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k)) (f g : Nat → Bool)
    (ht : 5≤t) (he : 2*t+3≤e) (b : Bool) :
    let d := if b then 2 else 3
    let V := if b then lNear u c else lFar u c
    (∀j, e+3-d-2*t<j → f j=g j) →
    xor (V f t e) (V g t e) = xor (f (e+3-d-2*t)) (g (e+3-d-2*t)) := by
  dsimp only
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> intro ag
  · have h := lineStep_xor_pivot k u c f g t (e-3) (by omega) (by omega) (fun j hj _ => ag _ (by omega))
    rw [show e-3+3-2*t=e+3-3-2*t by omega] at h
    unfold lFar lInj
    rw [ag (e+3-2*t) (by omega),←h]
    generalize lineStep k u c f t (e-3)=a
    generalize lineStep k u c g t (e-3)=b
    generalize xor (xor (g (e+3-2*t)) (u.val.testBit ((e+3-2*t) % k))) ((c t).val.testBit (e % k))=z
    cases a <;> cases b <;> cases z <;> rfl
  · have h := lineStep_xor_pivot k u c f g t (e-2) (by omega) (by omega) (fun j hj _ => ag _ (by omega))
    rw [show e-2+3-2*t=e+3-2-2*t by omega] at h
    unfold lNear lInj
    rw [ag (e+3-2*t) (by omega),ag (e-1+3-2*t) (by omega),←h]
    generalize lineStep k u c f t (e-2)=a
    generalize lineStep k u c g t (e-2)=b
    generalize xor (xor (xor (g (e-1+3-2*t)) (u.val.testBit ((e-1+3-2*t) % k))) ((c t).val.testBit ((e-1) % k))) (xor (xor (g (e+3-2*t)) (u.val.testBit ((e+3-2*t) % k))) ((c t).val.testBit (e % k)))=z
    cases a <;> cases b <;> cases z <;> rfl

end PEqualNP.Outside.L_meta_25541_aux

namespace PEqualNP.Outside.L_meta_25541_aux

theorem lTrace_succ {k : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (f : Nat→Bool) (q j : Nat) :
  lTrace u c f q (j+1) =
    let z := lTrace u c f q j
    let v := lBranch u c f (5+2*j) z.1
    (z.1-6+gain v,z.2+v*10^j) := by simp [lTrace,List.range_succ]

theorem branch_gain {k : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (f : Nat→Bool) (t e : Nat) :
    gain (lBranch u c f t e) ≤ 3 := by
  have h : ∀ b n f y : Bool, gain (if b then 2+n.toNat+2*f.toNat+4*y.toNat else y.toNat)≤3 := by decide
  exact h ..
theorem trace_bounds {k : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (f : Nat→Bool) (q j : Nat)
    (big : 10*j+35≤q) : q-13-6*j ≤ (lTrace u c f q j).1 ∧ (lTrace u c f q j).1 ≤ q-13 := by
  induction j with
  | zero => simp [lTrace]
  | succ j ih =>
    obtain ⟨lb,ub⟩ := ih (by omega)
    have gd := branch_gain u c f (5+2*j) (lTrace u c f q j).1
    rw [lTrace_succ]
    dsimp only
    omega

theorem branchLeft {k t e : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (f g : Nat→Bool)
    (ht : 5≤t) (he : 2*t+6≤e) (ag : ∀n, e-(2*t+2)≤n → f n=g n) :
    lBranch u c f t e=lBranch u c g t e := by
  have bitEq (s j : Nat) (hs : 4≤s) (hj : e-(2*t+2)+2*s-3≤j) :
      lineStep k u c f s j = lineStep k u c g s j :=
    lineStep_agree_interval k u c f g (e-(2*t+2)) (j+3*s) (fun n hn _ => ag _ hn) s j (by omega) (by omega)
  have guardEq (s j : Nat) (hs : 4≤s) (hj : e-(2*t+2)+2*s-1≤j) :
      lGuard u c f s j=lGuard u c g s j := by
    unfold lGuard
    rw [bitEq _ _ hs (by omega),bitEq _ _ hs (by omega),bitEq _ _ hs (by omega)]
  have injEq (j : Nat) (hj : e-1≤j) : lInj u c f t j=lInj u c g t j := by
    unfold lInj
    rw [ag _ (by omega)]
  have nearEq : lNear u c f t e=lNear u c g t e := by
    unfold lNear
    rw [bitEq _ _ (by omega) (by omega),injEq (e-1) (by omega),injEq e (by omega)]
  have farEq : lFar u c f t e=lFar u c g t e := by
    unfold lFar
    rw [bitEq _ _ (by omega) (by omega),injEq e (by omega)]
  unfold lBranch
  rw [guardEq (t-1) e (by omega) (by omega),nearEq,farEq]
  cases lGuard u c g (t-1) e <;> simp only [Bool.toNat_false,Bool.toNat_true] <;> rw [guardEq t _ (by omega) (by omega)]

theorem histLeft {k : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (f g : Nat→Bool) (q p : Nat)
    (big : 10*p+35≤q) (ag : ∀n, (lTrace u c f q p).1-(2*(5+2*p)+2)+6≤n → f n=g n) :
    lTrace u c f q p=lTrace u c g q p := by
  induction p with
  | zero => rfl
  | succ p ih =>
    have lb := (trace_bounds u c f q p (by omega)).1
    have gd := branch_gain u c f (5+2*p) (lTrace u c f q p).1
    rw [lTrace_succ] at ag ⊢
    dsimp only at ag ⊢
    have old := ih (by omega) (fun n hn => ag n (by omega))
    have bb := branchLeft u c f g (t:=5+2*p) (e:=(lTrace u c f q p).1) (by omega) (by omega)
      (fun n hn => ag n (by omega))
    rw [lTrace_succ u c g,←old,bb]

end PEqualNP.Outside.L_meta_25541_aux

namespace PEqualNP.Outside.L_meta_25541_aux

def invPack41 (v a : Nat) :=
  ((a % 2) <<< 5) ||| (if v < 2 then (a / 2) % 2 else
    (((a / 2) % 2) <<< 3) ||| (((a / 4) % 2) <<< 2) ||| (((a / 8) % 2) <<< 1))

def invEval41 (h n f m y : Bool) : Nat :=
  if h then 2 + n.toNat + 2 * f.toNat + 4 * y.toNat else m.toNat

def invTri41 (idx : Nat) (F : Nat → Bool) : Prop :=
  ∀ m n : Fin 64, (∀ j : Nat, idx < j → j < 6 → m.val.testBit j = n.val.testBit j) →
    xor (F m.val) (F n.val) = xor (m.val.testBit idx) (n.val.testBit idx)

private theorem sameInv41 {idx : Nat} {F : Nat → Bool} (hf : invTri41 idx F)
    (a b : Fin 64) (hh : ∀ j : Fin 6, idx < j.val → a.val.testBit j.val = b.val.testBit j.val)
    (he : F a.val = F b.val) : a.val.testBit idx = b.val.testBit idx := by
  have hh' := hf a b (fun j h hj => hh ⟨j,hj⟩ h)
  rw [he] at hh'
  cases F b.val <;> cases h : a.val.testBit idx <;> cases h' : b.val.testBit idx <;>
    simp_all

def maskInv4 (a : Fin 4) : Fin 64 :=
  ⟨invPack41 0 a.val,(by
    have h : ∀ a : Fin 4, invPack41 0 a.val < 64 := by decide +kernel
    exact h a)⟩

private def bitsInv4 (h m : Bool) := h.toNat + 2*m.toNat
private theorem bitsInv4Bound (h m : Bool) : bitsInv4 h m < 4 := by
  revert h m
  decide +kernel
private def sigInv4 (H M : Nat → Bool) (a : Fin 4) : Fin 4 :=
  ⟨bitsInv4 (H (maskInv4 a).val) (M (maskInv4 a).val),bitsInv4Bound ..⟩
private theorem injInv4 (H M : Nat → Bool) (tH : invTri41 5 H) (tM : invTri41 0 M) : Function.Injective (sigInv4 H M) := by
  intro a b e
  have eqn := congrArg Fin.val e
  change bitsInv4 (H (maskInv4 a).val) (M (maskInv4 a).val) = bitsInv4 (H (maskInv4 b).val) (M (maskInv4 b).val) at eqn
  have digitEq : ∀ ha ma hb mb : Bool, bitsInv4 ha ma = bitsInv4 hb mb → ha = hb ∧ ma = mb := by decide +kernel
  obtain ⟨eH,eM⟩ := digitEq  _ _ _ _ eqn
  have highH : ∀ a b : Fin 4, ∀ j : Fin 6, 5 < j.val → (maskInv4 a).val.testBit j.val = (maskInv4 b).val.testBit j.val := by decide +kernel
  have bitH := sameInv41 tH (maskInv4 a) (maskInv4 b) (highH a b ) eH
  have highM : ∀ a b : Fin 4, (maskInv4 a).val.testBit 5 = (maskInv4 b).val.testBit 5 → ∀ j : Fin 6, 0 < j.val → (maskInv4 a).val.testBit j.val = (maskInv4 b).val.testBit j.val := by decide +kernel
  have bitM := sameInv41 tM (maskInv4 a) (maskInv4 b) (highM a b bitH) eM
  have inj : ∀ a b : Fin 4, (maskInv4 a).val.testBit 5 = (maskInv4 b).val.testBit 5 → (maskInv4 a).val.testBit 0 = (maskInv4 b).val.testBit 0 → a = b := by decide +kernel
  exact inj a b bitH bitM

private theorem evalInv4 : ∀ v : Fin 10, v.val < 2 → ∀ h n f m y : Bool, (bitsInv4 h m = v.val * 2) ↔ (invEval41 h n f m y = v.val) := by decide +kernel

def maskInv16 (a : Fin 16) : Fin 64 :=
  ⟨invPack41 2 a.val,(by
    have h : ∀ a : Fin 16, invPack41 2 a.val < 64 := by decide +kernel
    exact h a)⟩

private def bitsInv16 (h n f y : Bool) := h.toNat + 2*n.toNat + 4*f.toNat + 8*y.toNat
private theorem bitsInv16Bound (h n f y : Bool) : bitsInv16 h n f y < 16 := by
  revert h n f y
  decide +kernel
private def sigInv16 (H N F Y : Nat → Bool) (a : Fin 16) : Fin 16 :=
  ⟨bitsInv16 (H (maskInv16 a).val) (N (maskInv16 a).val) (F (maskInv16 a).val) (Y (maskInv16 a).val),bitsInv16Bound ..⟩
private theorem injInv16 (H N F Y : Nat → Bool) (tH : invTri41 5 H) (tN : invTri41 3 N) (tF : invTri41 2 F) (tY : invTri41 1 Y) : Function.Injective (sigInv16 H N F Y) := by
  intro a b e
  have eqn := congrArg Fin.val e
  change bitsInv16 (H (maskInv16 a).val) (N (maskInv16 a).val) (F (maskInv16 a).val) (Y (maskInv16 a).val) = bitsInv16 (H (maskInv16 b).val) (N (maskInv16 b).val) (F (maskInv16 b).val) (Y (maskInv16 b).val) at eqn
  have digitEq : ∀ ha na fa ya hb nb fb yb : Bool, bitsInv16 ha na fa ya = bitsInv16 hb nb fb yb → ha = hb ∧ na = nb ∧ fa = fb ∧ ya = yb := by decide +kernel
  obtain ⟨eH,eN,eF,eY⟩ := digitEq  _ _ _ _ _ _ _ _ eqn
  have highH : ∀ a b : Fin 16, ∀ j : Fin 6, 5 < j.val → (maskInv16 a).val.testBit j.val = (maskInv16 b).val.testBit j.val := by decide +kernel
  have bitH := sameInv41 tH (maskInv16 a) (maskInv16 b) (highH a b ) eH
  have highN : ∀ a b : Fin 16, (maskInv16 a).val.testBit 5 = (maskInv16 b).val.testBit 5 → ∀ j : Fin 6, 3 < j.val → (maskInv16 a).val.testBit j.val = (maskInv16 b).val.testBit j.val := by decide +kernel
  have bitN := sameInv41 tN (maskInv16 a) (maskInv16 b) (highN a b bitH) eN
  have highF : ∀ a b : Fin 16, (maskInv16 a).val.testBit 5 = (maskInv16 b).val.testBit 5 → (maskInv16 a).val.testBit 3 = (maskInv16 b).val.testBit 3 → ∀ j : Fin 6, 2 < j.val → (maskInv16 a).val.testBit j.val = (maskInv16 b).val.testBit j.val := by decide +kernel
  have bitF := sameInv41 tF (maskInv16 a) (maskInv16 b) (highF a b bitH bitN) eF
  have highY : ∀ a b : Fin 16, (maskInv16 a).val.testBit 5 = (maskInv16 b).val.testBit 5 → (maskInv16 a).val.testBit 3 = (maskInv16 b).val.testBit 3 → (maskInv16 a).val.testBit 2 = (maskInv16 b).val.testBit 2 → ∀ j : Fin 6, 1 < j.val → (maskInv16 a).val.testBit j.val = (maskInv16 b).val.testBit j.val := by decide +kernel
  have bitY := sameInv41 tY (maskInv16 a) (maskInv16 b) (highY a b bitH bitN bitF) eY
  have inj : ∀ a b : Fin 16, (maskInv16 a).val.testBit 5 = (maskInv16 b).val.testBit 5 → (maskInv16 a).val.testBit 3 = (maskInv16 b).val.testBit 3 → (maskInv16 a).val.testBit 2 = (maskInv16 b).val.testBit 2 → (maskInv16 a).val.testBit 1 = (maskInv16 b).val.testBit 1 → a = b := by decide +kernel
  exact inj a b bitH bitN bitF bitY

private theorem evalInv16 : ∀ v : Fin 10, ¬ v.val < 2 → ∀ h n f m y : Bool, (bitsInv16 h n f y = 1 + 2*(v.val - 2)) ↔ (invEval41 h n f m y = v.val) := by decide +kernel


theorem invert41 (H N F M Y : Nat → Bool)
    (hH : invTri41 5 H) (hN : invTri41 3 N) (hF : invTri41 2 F)
    (hM : invTri41 0 M) (hY : invTri41 1 Y) (v : Fin 10) :
    ∃! a : Fin (2 ^ (if v.val < 2 then 2 else 4)),
      (let m := invPack41 v.val a.val
       invEval41 (H m) (N m) (F m) (M m) (Y m)) = v.val := by
  by_cases hv : v.val < 2
  · rw [if_pos hv]
    let target : Fin 4 := ⟨v.val * 2,by omega⟩
    have inj := injInv4 H M hH hM
    obtain ⟨a,ha⟩ := Finite.surjective_of_injective inj target
    have hm (b : Fin 4) : invPack41 v.val b.val = (maskInv4 b).val := by simp [invPack41,maskInv4, hv]
    have eqv (b : Fin 4) : sigInv4 H M b = target ↔ (let m := invPack41 v.val b.val; invEval41 (H m) (N m) (F m) (M m) (Y m)) = v.val := by
      rw [hm]
      exact Fin.ext_iff.trans (evalInv4 v hv ..)
    exact ⟨a,(eqv a).mp ha,fun b hb => inj ((eqv b).mpr hb |>.trans ha.symm)⟩
  · rw [if_neg hv]
    let target : Fin 16 := ⟨1 + 2*(v.val - 2),by omega⟩
    have inj := injInv16 H N F Y hH hN hF hY
    obtain ⟨a,ha⟩ := Finite.surjective_of_injective inj target
    have hm (b : Fin 16) : invPack41 v.val b.val = (maskInv16 b).val := by simp [invPack41,maskInv16, hv]
    have eqv (b : Fin 16) : sigInv16 H N F Y b = target ↔ (let m := invPack41 v.val b.val; invEval41 (H m) (N m) (F m) (M m) (Y m)) = v.val := by
      rw [hm]
      exact Fin.ext_iff.trans (evalInv16 v hv ..)
    exact ⟨a,(eqv a).mp ha,fun b hb => inj ((eqv b).mpr hb |>.trans ha.symm)⟩

end PEqualNP.Outside.L_meta_25541_aux

namespace PEqualNP.Outside.L_meta_25541_aux

def rawBit {k : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (t key n : Nat) :=
  (stateAt k u c t key).testBit (n % k)
def rawInj {k : Nat} (c : Nat→Fin (2^k)) (t key n : Nat) :=
  xor ((rot k (2*(t-1)) key).testBit (n % k)) ((c t).val.testBit (n % k))
def rawGuard {k : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (t key e : Nat) :=
  xor (xor (rawBit u c t key (e-2)) (rawBit u c t key (e-1))) (rawBit u c t key e)
def rawB {k : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (t e key : Nat) :=
  let h := rawGuard u c (t-1) key e
  let close := rawGuard u c t key (e-3+h.toNat)
  if h then
    let near := rawBit u c t key (e-2) == xor (rawInj c t key (e-1)) (rawInj c t key e)
    let far := rawBit u c t key (e-3) == rawInj c t key e
    2+near.toNat+2*far.toNat+4*close.toNat
  else close.toNat
def rawT {k : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (q len key : Nat) :=
  (List.range len).foldl (fun (acc : Nat × Nat) j =>
    let v := rawB u c (5+2*j) acc.1 key
    (acc.1-6+gain v,acc.2+v*10^j)) (q-13,0)

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

theorem branchRaw {k t e key : Nat} (hk : 6≤k) (ht : 5≤t) (he : 2*t+6≤e) (hw : key<2^k)
    (u : Fin (2^k)) (c : Nat→Fin (2^k)) :
    lBranch u c (src u key) t e=rawB u c t e key := by
  have bitEq (s j : Nat) (h : 2*s≤j) :
      lineStep k u c (src u key) s j=rawBit u c s key j :=
    lineStep_eq_stateAt (by omega) u c ⟨key,hw⟩ s j h
  have geq (s j : Nat) (h : 2*s+2≤j) : lGuard u c (src u key) s j=rawGuard u c s key j := by
    unfold lGuard rawGuard
    rw [bitEq _ _ (by omega),bitEq _ _ (by omega),bitEq _ _ (by omega)]
  unfold lBranch rawB lNear lFar
  rw [geq (t-1) e (by omega),bitEq t (e-2) (by omega),bitEq t (e-3) (by omega),
    injRaw hk (by omega) (by omega) hw,injRaw hk (by omega) (by omega) hw]
  cases rawGuard u c (t-1) key e <;> simp only [Bool.toNat_false,Bool.toNat_true] <;>
    rw [geq _ _ (by omega)]

theorem traceRaw {k q key : Nat} (hk : 6≤k) (hw : key<2^k) (u : Fin (2^k)) (c : Nat→Fin (2^k))
    (p : Nat) (hbig : 10*p+35≤q) : lTrace u c (src u key) q p=rawT u c q p key := by
  induction p with
  | zero => rfl
  | succ j ih =>
    have bound := (trace_bounds u c (src u key) q j (by omega)).1
    have h := ih (by omega)
    have hs : rawT u c q (j+1) key =
      let z := rawT u c q j key
      let v := rawB u c (5+2*j) z.1 key
      (z.1-6+gain v,z.2+v*10^j) := by simp [rawT,List.range_succ]
    rw [lTrace_succ,hs,←h]
    dsimp only
    rw [branchRaw hk (by omega) (by omega) hw]

end PEqualNP.Outside.L_meta_25541_aux

namespace PEqualNP.Outside.L_meta_25541_aux

theorem solveLeft {k q e t : Nat} (hk : 6≤k) (ht : 5≤t) (he : 2*t+6≤e) (upper : e≤q-13)
    (hq0 : 13≤q) (u base : Fin (2^k)) (c : Nat→Fin (2^k)) :
    let lo := e-(2*t+2)
    let f := fun m => cut q (src u (vary base lo m))
    q≤lo+k → ∀ v : Fin 10, ∃! a : Fin (2^(if v.val<2 then 2 else 4)),
      lBranch u c (f (invPack41 v.val a.val)) t e = v.val := by
  intro lo f wit v
  have hl : 0<lo := by dsimp [lo];omega
  have maxLt : lo+5<q := by dsimp [lo];omega
  have gTri (d s j : Nat) (hd : d≤5) (hs : 4≤s) (hj : 2*s+2≤j) (hi : j+1-2*s=lo+d) :
      invTri41 d (fun m => lGuard u c (f m) s j) := by
    intro m n ag
    obtain ⟨same,del⟩ := cut_tri (d:=d) hk hl (by omega) wit u base m n ag
    rw [gPivot u c (f m.val) (f n.val) hs hj (fun x hx => same _ (by omega)),hi]
    exact del
  have aTri (d : Nat) (b : Bool) (hd : d≤5) (hi : e+3-(if b then 2 else 3)-2*t=lo+d) :
      invTri41 d (fun m => (if b then lNear u c else lFar u c) (f m) t e) := by
    intro m n ag
    obtain ⟨same,del⟩ := cut_tri (d:=d) hk hl (by omega) wit u base m n ag
    have piv := alignPivot u c (f m.val) (f n.val) ht (by omega : 2*t+3≤e) b
      (fun x hx => same _ (by simpa only [←hi] using hx))
    rw [hi] at piv
    exact piv.trans del
  have hH := gTri 5 (t-1) e (by omega) (by omega) (by omega) (by dsimp [lo];omega)
  have hN := aTri 3 true (by omega) (by dsimp [lo];omega)
  have hF := aTri 2 false (by omega) (by dsimp [lo];omega)
  have hM := gTri 0 t (e-3) (by omega) (by omega) (by omega) (by dsimp [lo];omega)
  have hY := gTri 1 t (e-2) (by omega) (by omega) (by omega) (by dsimp [lo];omega)
  let H := fun m => lGuard u c (f m) (t-1) e
  let N := fun m => lNear u c (f m) t e
  let F := fun m => lFar u c (f m) t e
  let M := fun m => lGuard u c (f m) t (e-3)
  let Y := fun m => lGuard u c (f m) t (e-2)
  have eval (m : Nat) : lBranch u c (f m) t e = invEval41 (H m) (N m) (F m) (M m) (Y m) := by
    change (let b := H m; let y := lGuard u c (f m) t (e-3+b.toNat)
            if b then 2+(N m).toNat+2*(F m).toNat+4*y.toNat else y.toNat) = _
    unfold invEval41
    cases H m <;> simp [M,Y,show e-3+1=e-2 by omega]
  simpa only [eval] using (invert41 H N F M Y hH hN hF hM hY v)

end PEqualNP.Outside.L_meta_25541_aux

namespace PEqualNP.Outside.L_meta_25541_aux

def RightLaw41 {k : Nat} (u : Fin (2^k)) (c : Nat→Fin (2^k)) (q p : Nat) :=
  ∀ f g : Nat→Bool, (∀ n, n<q → f n=g n) →
    lTrace u c f q p=lTrace u c g q p ∧
      lBranch u c f (5+2*p) (lTrace u c f q p).1 =
        lBranch u c g (5+2*p) (lTrace u c f q p).1

theorem package41 {k p : Nat} (hk : 6≤k) (a : Fin k) (u base : Fin (2^k)) (c : Nat→Fin (2^k))
    (q : Nat) (hq0 : q=a.val+(10*p+30)*k) (rightLaw : RightLaw41 u c q p) :
    let e := (rawT u c q p base.val).1
    let t := 5+2*p
    let lo := e-(2*t+2)
    q≤lo+k →
      (∀m : Fin 64, rawT u c q p (vary base lo m.val) = rawT u c q p base.val) ∧
      ∀v : Fin 10, ∃! z : Fin (2^(if v.val<2 then 2 else 4)),
        rawB u c t e (vary base lo (invPack41 v.val z.val)) = v.val := by
  intro e t lo w
  have big : 10*p+35≤q := by nlinarith [Nat.zero_le a.val, Nat.mul_le_mul_left (10*p+30) hk]
  have hbase := traceRaw hk base.isLt u c p big
  have bounds := trace_bounds u c (src u base.val) q p big
  rw [hbase] at bounds
  change q-13-6*p ≤ e ∧ e≤q-13 at bounds
  have he : 2*t+6≤e := by dsimp [t];omega
  have hl : 0<lo := by dsimp [lo];omega
  have ht : 5≤t := by dsimp [t];omega
  have maxLt : lo+5<q := by dsimp [lo];omega
  let G := fun key => cut q (src u key)
  have rlaw (key : Nat) := rightLaw (src u key) (G key) (fun n hn => by simp [G,cut,hn])
  have cb : lTrace u c (G base.val) q p=rawT u c q p base.val := (rlaw base.val).1.symm.trans hbase
  have cl (m : Fin 64) : lTrace u c (G base.val) q p = lTrace u c (G (vary base lo m.val)) q p := by
    apply histLeft u c _ _ q p big
    rw [cb]
    change ∀n, lo+6≤n → _
    intro n hn
    have z : vary base lo 0=base.val := by simp [vary,rot]
    have ht0 := cut_tri (d:=5) hk hl maxLt w u base (0 : Fin 64) m (fun j hj hj' => by omega)
    have := ht0.1 n (by omega)
    simpa only [Fin.val_zero,z,G] using this
  have traces (m : Fin 64) : rawT u c q p (vary base lo m.val) = rawT u c q p base.val :=
    (traceRaw hk (vary_lt base lo m.val) u c p big).symm.trans
      ((rlaw _).1.trans ((cl m).symm.trans cb))
  refine ⟨traces,?_⟩
  intro v
  have tr (m : Fin 64) : rawB u c t e (vary base lo m.val) = lBranch u c (G (vary base lo m.val)) t e := by
    have r := (rlaw (vary base lo m.val)).2
    rw [traceRaw hk (vary_lt base lo m.val) u c p big,traces m] at r
    exact (branchRaw hk ht he (vary_lt base lo m.val) u c).symm.trans r
  have pp (z : Fin (2^(if v.val<2 then 2 else 4))) : invPack41 v.val z.val<64 := by
    have allz : ∀ x : Fin 10, ∀ y : Fin (2^(if x.val<2 then 2 else 4)), invPack41 x.val y.val < 64 := by decide +kernel
    exact allz v z
  have solved := solveLeft hk ht he bounds.2 (by omega : 13≤q) u base c w v
  have ident (z : Fin (2^(if v.val<2 then 2 else 4))) := tr ⟨invPack41 v.val z.val,pp z⟩
  simpa only [ident] using solved

end PEqualNP.Outside.L_meta_25541_aux

namespace PEqualNP.Outside.L_meta_25541_aux
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
lemma special (x y z a b : Bool) :
    let q := xor (xor true (!x && y)) a
    let r := xor (xor x (!y && z)) b
    (!(tri b (xor a b) q) && tri (xor a b) q r) = false := by
  cases x <;> cases y <;> cases z <;> cases a <;> cases b <;> decide

lemma bonus (f j : Src) {e : Nat} (he : 6≤e) (hit : grd f e=true)
    (near : cell f j (e-2) = xor (j (e-1)) (j e)) (far : cell f j (e-3)=j e) :
    (!(tri (cell f j (e-3)) (cell f j (e-2)) (cell f j (e-1))) &&
      tri (cell f j (e-2)) (cell f j (e-1)) (cell f j e)) = false := by
  rw [near,far]
  simp only [cell,show e-1-1=e-2 by omega,show e-1+1=e by omega,
    show e-1+2=e+1 by omega,show e-1+3=e+2 by omega]
  change tri (f (e-2)) (f (e-1)) (f e)=true at hit
  rw [hit]
  exact special ..

end Right
end PEqualNP.Outside.L_meta_25541_aux

namespace PEqualNP.Outside.L_meta_25541_aux
namespace Right
def letter (f a : Src) (e : Nat) :=
  let y := cell f a
  let h := grd f e
  let extra := grd y (e-3+h.toNat)
  if h then 2+(y (e-2)==xor (a (e-1)) (a e)).toNat+2*(y (e-3)==a e).toNat+4*extra.toNat
  else extra.toNat

lemma grow {f g a b j l : Src} {e : Nat} (he : 12≤e)
    (h : PrefixEq f g e) (ha : PrefixEq a b e) (hj : PrefixEq j l e) :
    letter f a e=letter g b e ∧
    PrefixEq (cell (cell f a) j) (cell (cell g b) l) (e-6+gain (letter f a e)) := by
  let y := cell f a
  let z := cell g b
  let mid := e-3+(grd f e).toNat
  have ma : PrefixEq y z mid := move (by omega) h ha
  have hmid : 6≤mid ∧ mid≤e := by dsimp [mid];cases grd f e <;> simp <;> omega
  have step2 := move hmid.1 ma (show PrefixEq j l mid from fun n hn => hj n (by omega))
  have eq0 := guardEq h
  have eq1 := guardEq ma
  cases hit : grd f e with
  | false =>
    have eqm : mid=e-3 := by simp [mid,hit]
    simp only [letter,hit,←eq0,Bool.false_eq_true,ite_false,Bool.toNat_false,Nat.add_zero]
    change (grd y (e-3)).toNat = (grd z (e-3)).toNat ∧ _
    have e1 : grd y (e-3)=grd z (e-3) := by simpa [eqm] using eq1
    refine ⟨congrArg Bool.toNat e1,?_⟩
    change PrefixEq _ _ (e-6+gain (grd y (e-3)).toNat)
    rw [eqm] at step2
    cases eh : grd y (e-3) <;> simpa [gain,eh,Nat.sub_sub] using step2
  | true =>
    have eqm : mid=e-2 := by simp [mid,hit];omega
    have nearEq : (y (e-2)==xor (a (e-1)) (a e)) = (z (e-2)==xor (b (e-1)) (b e)) := by
      rw [ma _ (by omega),ha _ (by omega),ha _ (by omega)]
    have farEq : (y (e-3)==a e)=(z (e-3)==b e) := by rw [ma _ (by omega),ha _ (by omega)]
    have e1 : grd y mid=grd z mid := eq1
    have letterA : letter f a e=2+(y (e-2)==xor (a (e-1)) (a e)).toNat+2*(y (e-3)==a e).toNat+4*(grd y mid).toNat := by simp [letter,hit,mid,y]
    have letterB : letter g b e=2+(z (e-2)==xor (b (e-1)) (b e)).toNat+2*(z (e-3)==b e).toNat+4*(grd z mid).toNat := by simp [letter,←eq0,hit,mid,z]
    refine ⟨by rw [letterA,letterB,nearEq,farEq,e1],?_⟩
    intro p hp
    by_cases sub : p≤mid-3+(grd y mid).toNat
    · exact step2 p sub
    · rw [letterA] at hp
      cases ne : (y (e-2)==xor (a (e-1)) (a e)) <;>
        cases fe : (y (e-3)==a e) <;> cases en : grd y mid <;>
        simp [ne,fe,en,gain] at hp sub <;> try omega
      have ep : p=e-3 := by omega
      subst p
      have fA := bonus f a (e:=e) (by omega) hit (beq_iff_eq.mp ne) (beq_iff_eq.mp fe)
      have fB := bonus g b (e:=e) (by omega) (eq0.symm.trans hit)
        (beq_iff_eq.mp (nearEq.symm.trans ne)) (beq_iff_eq.mp (farEq.symm.trans fe))
      change cell y j (e-3)=cell z l (e-3)
      unfold cell
      simp only [show e-3+1=e-2 by omega,show e-3+2=e-1 by omega,show e-3+3=e by omega]
      change (!tri (y (e-3)) (y (e-2)) (y (e-1)) && tri (y (e-2)) (y (e-1)) (y e))=false at fA
      change (!tri (z (e-3)) (z (e-2)) (z (e-1)) && tri (z (e-2)) (z (e-1)) (z e))=false at fB
      rw [fA,fB,ma (e-3-1) (by omega), ma (e-3) (by omega),ma (e-2) (by omega),hj _ (by omega)]
end Right
end PEqualNP.Outside.L_meta_25541_aux

namespace PEqualNP.Outside.L_meta_25541_aux
namespace Right
variable {k : Nat} (u : Fin (2^k)) (c : Nat → Fin (2^k))
lemma initial {f g : Src} {q : Nat} (same : ∀ n, n<q → f n=g n) (s p : Nat) (h : p+3*s<q) :
    lineStep k u c f s p=lineStep k u c g s p := by
  induction s generalizing p with
  | zero => exact same p (by omega)
  | succ s ih =>
    rw [stepEq,stepEq]
    unfold cell lInj
    rw [ih _ (by omega),ih _ (by omega),ih _ (by omega),ih _ (by omega),ih _ (by omega),same _ (by omega)]

lemma asLetter (f : Src) (s e : Nat) :
    lBranch u c f (s+1) e = letter (lineStep k u c f s) (lInj u c f (s+1)) e := by
  simp only [lBranch,lGuard,lNear,lFar,letter,grd,tri,Nat.add_sub_cancel,Nat.add_one_sub_one,stepEq] <;> rfl

lemma gainLe (y a : Src) (e : Nat) : gain (letter y a e) ≤ 3 := by
  have small (h n f g : Bool) : gain (if h then 2+n.toNat+2*f.toNat+4*g.toNat else g.toNat) ≤ 3 := by
    cases h <;> cases n <;> cases f <;> cases g <;> decide
  exact small ..

lemma traceSucc (f : Src) (q j : Nat) :
    lTrace u c f q (j+1) =
      let a := lTrace u c f q j
      let v := lBranch u c f (5+2*j) a.1
      (a.1-6+gain v,a.2+v*10^j) := by simp [lTrace,List.range_succ,List.foldl_append]

lemma rightTrace {f g : Src} {p q : Nat} (hq : 6*p+26 ≤ q)
    (same : ∀ n, n<q → f n=g n) :
    lTrace u c f q p=lTrace u c g q p ∧
    lBranch u c f (5+2*p) (lTrace u c f q p).1=lBranch u c g (5+2*p) (lTrace u c f q p).1 := by
  let E := fun j => (lTrace u c f q j).1
  have iter (j : Nat) (hj : j≤p) : lTrace u c f q j=lTrace u c g q j ∧
      E j+6*j+13≥q ∧ E j+13≤q ∧ PrefixEq (lineStep k u c f (4+2*j)) (lineStep k u c g (4+2*j)) (E j) := by
    induction j with
    | zero =>
      have te (a : Src) : lTrace u c a q 0=(q-13,0) := rfl
      refine ⟨rfl,?_,?_,?_⟩
      · change q-13+6*0+13≥q;omega
      · change q-13+13≤q;omega
      · intro n hn
        change n≤q-13 at hn
        exact initial u c same 4 n (by omega)
    | succ j ih =>
      obtain ⟨hist,bot,top,agree⟩ := ih (by omega)
      let e := E j
      have he : 12≤e := by dsimp [e];omega
      have inj (t : Nat) : PrefixEq (lInj u c f t) (lInj u c g t) e := by
        intro n hn; unfold lInj;rw [same _ (by dsimp [e] at hn;omega)]
      have out := grow he agree (inj (4+2*j+1)) (inj (4+2*j+2))
      have va := asLetter u c f (4+2*j) e
      have vb := asLetter u c g (4+2*j) e
      have ar : 4+2*j+1=5+2*j := by omega
      have eq : lBranch u c f (5+2*j) e=lBranch u c g (5+2*j) e := by
        rw [←ar,va,vb];exact out.1
      let v := lBranch u c f (5+2*j) e
      have gl : gain v≤3 := by dsimp [v];rw [←ar,va];exact gainLe ..
      have ne : E (j+1)=e-6+gain v := congrArg Prod.fst (traceSucc u c f q j)
      refine ⟨?_,by rw [ne];dsimp [e];omega,by rw [ne];dsimp [e];omega,?_⟩
      · rw [traceSucc,traceSucc,←hist]; dsimp only
        change (_, _ + lBranch u c f _ e * _) = (_, _ + lBranch u c g _ e * _)
        rw [eq]
      · rw [ne]
        intro n hn
        rw [show 4+2*(j+1)=(4+2*j+1)+1 by omega,stepEq,stepEq]
        have aa (s : Src) : lineStep k u c s (4+2*j+1)=cell (lineStep k u c s (4+2*j)) (lInj u c s (4+2*j+1)) :=
          funext (stepEq u c s (4+2*j))
        rw [aa,aa]
        apply out.2 n
        simpa only [v,←ar,va] using hn
  obtain ⟨hist,bot,top,agree⟩ := iter p (Nat.le_refl _)
  let e := E p
  have inj (t : Nat) : PrefixEq (lInj u c f t) (lInj u c g t) e := by
    intro n hn;unfold lInj;rw [same _ (by dsimp [e] at hn;omega)]
  have out := grow (e:=e) (by dsimp [e];omega) agree (inj (4+2*p+1)) (inj (4+2*p+2))
  refine ⟨hist,?_⟩
  rw [show 5+2*p=4+2*p+1 by omega,asLetter,asLetter];exact out.1
end Right
end PEqualNP.Outside.L_meta_25541_aux

theorem PEqualNP.Outside.L_meta_25541 :
∀ (k p : Nat), 6 ≤ k → ∀ (anchor : Fin k) (u base : Fin (2 ^ k))
    (constant : Nat → Fin (2 ^ k)),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc j =>
      acc ||| ((xor (word.testBit j)
        (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0
  let state := fun (rounds key : Nat) =>
    (List.range rounds).foldl (fun prev tick =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * tick) key ^^^
        (constant (tick + 1)).val) (rot 1 key ^^^ u.val)
  let injected := fun (round key pos : Nat) =>
    xor ((rot (2 * (round - 1)) key).testBit (pos % k))
      ((constant round).val.testBit (pos % k))
  let bit := fun (round key pos : Nat) => (state round key).testBit (pos % k)
  let guard := fun (round key stop : Nat) =>
    xor (xor (bit round key (stop - 2)) (bit round key (stop - 1))) (bit round key stop)
  let branch := fun (t edge subject : Nat) =>
    let hit := guard (t - 1) subject edge
    let mid := edge - 3 + hit.toNat
    let next := guard t subject mid
    if hit then
      let near := bit t subject (edge - 2) ==
        xor (injected t subject (edge - 1)) (injected t subject edge)
      let far := bit t subject (edge - 3) == injected t subject edge
      2 + near.toNat + 2 * far.toNat + 4 * next.toNat
    else next.toNat
  let gain := fun (v : Nat) =>
    if v < 2 then v else 1 + (v - 2) / 4 + (if v = 9 then 1 else 0)
  let q := anchor.val + (10 * p + 30) * k
  let trace := fun (len keyWord : Nat) =>
    (List.range len).foldl (fun (acc : Nat × Nat) j =>
      let v := branch (5 + 2 * j) acc.1 keyWord
      (acc.1 - 6 + gain v, acc.2 + v * 10 ^ j)) (q - 13, 0)
  let prev := trace p base.val
  let t := 5 + 2 * p
  let lo := prev.1 - (2 * t + 2)
  let vary := fun (mask : Nat) => base.val ^^^ rot (lo + k - 1) mask
  let pack := fun (v bits : Nat) =>
    ((bits % 2) <<< 5) ||| (if v < 2 then (bits / 2) % 2 else
      (((bits / 2) % 2) <<< 3) ||| (((bits / 4) % 2) <<< 2) ||| (((bits / 8) % 2) <<< 1))
  q ≤ lo + k →
    (∀ mask : Fin 64, trace p (vary mask.val) = prev) ∧
    ∀ label : Fin 10, ∃! assignment : Fin (2 ^ (if label.val < 2 then 2 else 4)),
      branch t prev.1 (vary (pack label.val assignment.val)) = label.val := by
  intro k p hk a u base c
  apply PEqualNP.Outside.L_meta_25541_aux.package41 hk a u base c _ rfl
  intro f g ag
  apply PEqualNP.Outside.L_meta_25541_aux.Right.rightTrace u c _ ag
  nlinarith [Nat.zero_le a.val, Nat.mul_le_mul_left (10*p+30) hk]
