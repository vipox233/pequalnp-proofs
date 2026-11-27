import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25567_aux

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

abbrev Word (k : Nat) := Fin (2^k)
def per {k : Nat} (w : Word k) (n : Nat) := w.val.testBit (n % k)
def flipWord {k : Nat} (hk : 0<k) (p : Nat) (w : Word k) : Word k :=
  ⟨w.val ^^^ 2^(p % k),xor_lt w.isLt (Nat.pow_lt_pow_right (by decide) (Nat.mod_lt _ hk))⟩
theorem per_flip {k : Nat} (hk : 0<k) (p : Nat) (w : Word k) (n : Nat) :
    per (flipWord hk p w) n = xor (per w n) (decide (p % k=n % k)) := by
  simp [per,flipWord,Nat.testBit_xor,Nat.testBit_two_pow]
theorem flip_flip {k : Nat} (hk : 0<k) (p : Nat) (w : Word k) :
    flipWord hk p (flipWord hk p w)=w := by
  apply Fin.ext
  simp [flipWord,Nat.xor_assoc]
def badGuard {k : Nat} (u : Word k) (c : Nat→Word k) (Q t : Nat) (w : Word k) :=
  lGuard u c (per w) t (Q-3*t-1)
def bad67 {k : Nat} (u : Word k) (c : Nat→Word k) (Q r : Nat) (w : Word k) : Prop :=
  ∀t, t<r-1 → t≠3 → badGuard u c Q t w=false
end PEqualNP.Outside.L_meta_25567_aux

namespace PEqualNP.Outside.L_meta_25567_aux

theorem modNe_up {k p n : Nat} (hp : p<n) (hn : n<p+k) : p % k ≠ n % k := by
  intro eqn
  have m : 0+p ≡ (n-p)+p [MOD k] := by rw [Nat.zero_add,Nat.sub_add_cancel hp.le];exact eqn
  have h := Nat.ModEq.add_right_cancel' p m
  change 0 % k=(n-p) % k at h
  rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega : n-p<k)] at h
  omega

theorem per_same {k p n : Nat} (hk : 0<k) (w : Word k)
    (br : n<p+k) (bl : p<n+k) (dif : p≠n) : per (flipWord hk p w) n=per w n := by
  by_cases h : p<n
  · simp [per_flip,modNe_up h br]
  · simp [per_flip,Ne.symm (modNe_up (by omega : n<p) bl)]

theorem per_toggle {k : Nat} (hk : 0<k) (p : Nat) (w : Word k) :
  per (flipWord hk p w) p=!(per w p) := by simp [per_flip]

theorem valSame {k s p t : Nat} (hk : 0<k) (hs : 4≤s) (hp : 2*s≤p)
    (u : Word k) (c : Nat→Word k) (w : Word k)
    (br : p+3*s<t+k) (bl : t<p+3-2*s+k) (dif : t<p+3-2*s ∨ p+3*s<t) :
    lineStep k u c (per (flipWord hk t w)) s p=lineStep k u c (per w) s p :=
  lineStep_agree_interval k u c _ _ (p+3-2*s) (p+3*s)
    (fun n nl nr => per_same hk w (by omega) (by omega) (by omega)) s p (by omega) (by omega)

theorem valToggle {k s p t : Nat} (hk : 0<k) (hs : 4≤s) (hp : 2*s≤p)
    (u : Word k) (c : Nat→Word k) (w : Word k)
    (ht : p+3-2*s=t) (br : p+3*s<t+k) :
    lineStep k u c (per (flipWord hk t w)) s p=!(lineStep k u c (per w) s p) := by
  have h := lineStep_xor_pivot k u c (per (flipWord hk t w)) (per w) s p hs hp
    (fun n nl nr => per_same hk w (by omega) (by omega) (by omega))
  rw [ht,per_toggle] at h
  revert h
  generalize lineStep k u c (per (flipWord hk t w)) s p = x
  generalize lineStep k u c (per w) s p = y
  cases x <;> cases y <;> cases per w t <;> decide

def cell67 (a b d e f inj : Bool) := xor (xor (xor b a) d) (!(xor (xor d b) e) && xor (xor e d) f) ^^ inj
theorem step67 {k : Nat} (u : Word k) (c : Nat→Word k) (s j : Nat) (w : Word k) :
  lineStep k u c (per w) (s+1) j =
    cell67 (lineStep k u c (per w) s (j-1)) (lineStep k u c (per w) s j)
      (lineStep k u c (per w) s (j+1)) (lineStep k u c (per w) s (j+2)) (lineStep k u c (per w) s (j+3))
      (lInj u c (per w) (s+1) j) := by
  rw [lineStep_succ]
  unfold cell67 lInj
  rw [show j+3-2*(s+1)=j+1-2*s by omega]
  simp only [Bool.xor_assoc]

theorem valNext {k s p t : Nat} (hk : 0<k) (hs : 5≤s) (hp : 2*s+1≤p)
    (u : Word k) (c : Nat→Word k) (w : Word k)
    (ht : p+4-2*s=t) (br : p+3*s<t+k) :
    lineStep k u c (per (flipWord hk t w)) s p=!(lineStep k u c (per w) s p) := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s≠0)
  have d := valToggle (p:=p-1) hk (by omega : 4≤s) (by omega) u c w (by omega : p-1+3-2*s=t) (by omega)
  have same (j : Nat) (hl : p≤j) (hr : j≤p+3) := valSame (s:=s) (p:=j) (t:=t) hk (by omega) (by omega) u c w
      (by omega) (by omega) (Or.inl (by omega))
  have inj : lInj u c (per (flipWord hk t w)) (s+1) p=lInj u c (per w) (s+1) p := by
    unfold lInj; rw [per_same hk w (by omega) (by omega) (by omega)]
  rw [step67,step67,d,same p (by omega) (by omega),same (p+1) (by omega) (by omega),
    same (p+2) (by omega) (by omega),same (p+3) (by omega) (by omega),inj]
  exact (by decide : ∀ a b d e f j : Bool, cell67 (!a) b d e f j = !(cell67 a b d e f j)) _ _ _ _ _ _

end PEqualNP.Outside.L_meta_25567_aux

namespace PEqualNP.Outside.L_meta_25567_aux
theorem edgeBad {k r N : Nat} (hk : 0<k) (hr : 6≤r) (hw : k+3=5*r) (hN : k≤N)
    (u : Word k) (c : Nat→Word k) (w : Word k) :
    let Q := N+3*r
    let A := N+3-2*r
    lineStep k u c (per (flipWord hk A w)) (r-1) (N+3) ≠ lineStep k u c (per w) (r-1) (N+3) →
    bad67 u c Q r w := by
  intro Q A
  let z := flipWord hk A w
  have span : Q=A+k := by dsimp [Q,A];omega
  have run (s : Nat) (hs : s<r) (dif : lineStep k u c (per z) s (Q-3*s) ≠ lineStep k u c (per w) s (Q-3*s)) :
      ∀ t, t<s → badGuard u c Q t w=false := by
    induction s with
    | zero => omega
    | succ s ih =>
      let j := Q-3*(s+1)
      have jl : j+2=Q-3*s-1 := by dsimp [j,Q];omega
      have jm : j+3=Q-3*s := by dsimp [j,Q];omega
      have lower : max (A+1+s) (A+1+2*s-3) ≤ j-1 := by dsimp [j,A,Q];omega
      have upper : j+2+3*s≤Q-1 := by dsimp [j,Q];omega
      have same (n : Nat) (nl : j-1≤n) (nu : n≤j+2) :
          lineStep k u c (per z) s n=lineStep k u c (per w) s n :=
        lineStep_agree_interval k u c _ _ (A+1) (Q-1)
          (fun i li ri => per_same hk w (by omega) (by omega) (by omega)) s n (by omega) (by omega)
      have inj : lInj u c (per z) (s+1) j=lInj u c (per w) (s+1) j := by
        unfold lInj
        rw [show per z (j+3-2*(s+1))=per w (j+3-2*(s+1)) from
          per_same hk w (by dsimp [j,A,Q] at *;omega) (by dsimp [j,A,Q] at *;omega) (by dsimp [j,A,Q] at *;omega)]
      change lineStep k u c (per z) (s+1) j ≠ lineStep k u c (per w) (s+1) j at dif
      rw [step67,step67,same _ (by omega) (by omega),same _ (by omega) (by omega),same _ (by omega) (by omega),
        same _ (by omega) (by omega),inj] at dif
      have test (a b d e f g h : Bool) : cell67 a b d e f h≠cell67 a b d e g h →
        f≠g ∧ xor (xor b d) e=false := by revert a b d e f g h;decide
      obtain ⟨old,gate⟩ := test _ _ _ _ _ _ _ dif
      rw [jm] at old
      intro t ht
      by_cases eqn : t=s
      · subst t
        unfold badGuard lGuard
        rw [←jl,show j+2-2=j by omega,show j+2-1=j+1 by omega]
        exact gate
      · exact ih (by omega) old t (by omega)
  have idx : Q-3*(r-1)=N+3 := by dsimp [Q];omega
  intro dif t ht _
  exact run (r-1) (by omega) (by simpa only [idx] using dif) t ht
end PEqualNP.Outside.L_meta_25567_aux

namespace PEqualNP.Outside.L_meta_25567_aux

def result67 {k : Nat} (u : Word k) (c : Nat→Word k) (r N : Nat) (w : Word k) : Bool×Bool :=
  (lineStep k u c (per w) r N, lineStep k u c (per w) r (N+1))
def h67 {k : Nat} (u : Word k) (c : Nat→Word k) (r N : Nat) (w : Word k) :=
  lGuard u c (per w) (r-1) (N+3)
def t67 {k : Nat} (u : Word k) (c : Nat→Word k) (r N : Nat) (w : Word k) :=
  !(xor (xor (lGuard u c (per w) (r-1) (N+1)) (lInj u c (per w) r N)) (lInj u c (per w) r (N+1)))
def par67 (b : Bool×Bool) := xor b.1 b.2

theorem laws67 {k r N : Nat} (hk : 0<k) (hr : 6≤r) (hw : k+3=5*r) (hN : k≤N)
    (u : Word k) (c : Nat→Word k) (w : Word k) :
    let P := N+3-2*r
    let A := flipWord hk P
    let B := flipWord hk (P+1)
    let C := flipWord hk (P+2)
    let F := result67 u c r N
    let H := h67 u c r N
    let T := t67 u c r N
    (F (B w)).1 = !((F w).1) ∧ (F (C w)).2 = !((F w).2) ∧ H (C w)=H w ∧
    (H w=false → par67 (F (C w))=!(par67 (F w))) ∧
    T (A w)=!(T w) ∧ (H w=true → par67 (F w)=T w) ∧
    (H (A w)≠H w → bad67 u c (N+3*r) r w) := by
  intro P A B C F H T
  let s := r-1
  have sr : s+1=r := by dsimp [s];omega
  have pdef : P=N+3-2*r := rfl
  have sd : s=r-1 := rfl
  have b0 : (F (B w)).1 = !((F w).1) :=
    valNext hk (by omega) (by omega) u c w (by omega) (by omega)
  have c1 : (F (C w)).2 = !((F w).2) :=
    valNext hk (by omega) (by omega) u c w (by omega) (by omega)
  let y := fun (z : Word k) (n : Nat) => lineStep k u c (per z) s n
  have cs (j : Nat) (lo : N+1≤j) (hi : j≤N+4) : y (C w) j=y w j :=
    valSame hk (by omega) (by omega) u c w (by omega) (by omega) (Or.inl (by omega))
  have aSame (j : Nat) (lo : N-1≤j) (hi : j≤N+2) : y (A w) j=y w j :=
    valSame hk (by omega) (by omega) u c w (by omega) (by omega) (Or.inl (by omega))
  have cn : y (C w) (N-1)=!(y w (N-1)) :=
    valNext hk (by omega) (by omega) u c w (by omega) (by omega)
  have cz : y (C w) N=!(y w N) :=
    valToggle hk (by omega) (by omega) u c w (by omega) (by omega)
  have h1 (z : Word k) : H z=xor (xor (y z (N+1)) (y z (N+2))) (y z (N+3)) := by
    dsimp only [H,h67,lGuard,y,s]
    rw [show N+3-2=N+1 by omega,show N+3-1=N+2 by omega]
  have t1 (z : Word k) : T z=!(xor (xor (xor (xor (y z (N-1)) (y z N)) (y z (N+1)))
      (lInj u c (per z) r N)) (lInj u c (per z) r (N+1))) := by
    dsimp only [T,t67,lGuard,y,s]
    rw [show N+1-2=N-1 by omega,show N+1-1=N by omega]
  have cH : H (C w)=H w := by
    rw [h1,h1,cs _ (by omega) (by omega),cs _ (by omega) (by omega),cs _ (by omega) (by omega)]
  have step0 (z : Word k) : (F z).1=cell67 (y z (N-1)) (y z N) (y z (N+1)) (y z (N+2)) (y z (N+3)) (lInj u c (per z) r N) := by
    change lineStep k u c (per z) r N=_
    conv_lhs => rw [←sr,step67];rw [sr]
  have step1 (z : Word k) : (F z).2=cell67 (y z N) (y z (N+1)) (y z (N+2)) (y z (N+3)) (y z (N+4)) (lInj u c (per z) r (N+1)) := by
    change lineStep k u c (per z) r (N+1)=_
    conv_lhs => rw [←sr,step67];rw [sr]
    simp only [show N+1-1=N by omega,show N+1+1=N+2 by omega,show N+1+2=N+3 by omega,show N+1+3=N+4 by omega,y]
  have iC : lInj u c (per (C w)) r N=lInj u c (per w) r N := by
    unfold lInj
    rw [show per (C w) (N+3-2*r)=per w (N+3-2*r) from per_same hk w (by omega) (by omega) (by omega)]
  have iA : lInj u c (per (A w)) r N=!(lInj u c (per w) r N) := by
    unfold lInj
    rw [show per (A w) (N+3-2*r)=!(per w (N+3-2*r)) from per_toggle hk _ w]
    exact (by decide : ∀ a b c : Bool, xor (xor (!a) b) c = !(xor (xor a b) c)) _ _ _ 
  have iA1 : lInj u c (per (A w)) r (N+1)=lInj u c (per w) r (N+1) := by
    unfold lInj
    rw [show per (A w) (N+1+3-2*r)=per w (N+1+3-2*r) from per_same hk w (by omega) (by omega) (by omega)]
  refine ⟨b0,c1,cH,?_,?_,?_,?_⟩
  · intro h
    rw [h1] at h
    have fst : (F (C w)).1=(F w).1 := by
      rw [step0,step0,cn,cz,cs _ (by omega) (by omega),cs _ (by omega) (by omega),cs _ (by omega) (by omega),iC]
      exact (by decide : ∀ a b d e f j : Bool, xor (xor d e) f=false → cell67 (!a) (!b) d e f j=cell67 a b d e f j) _ _ _ _ _ _ h
    unfold par67
    rw [fst,c1]
    exact (by decide : ∀ a b : Bool, xor a (!b)=!(xor a b)) _ _
  · rw [t1,t1,aSame _ (by omega) (by omega),aSame _ (by omega) (by omega),aSame _ (by omega) (by omega),iA,iA1]
    exact (by decide : ∀ a b c : Bool, (!(xor (xor a (!b)) c))=!!(xor (xor a b) c)) _ _ _
  · intro h
    rw [h1] at h
    unfold par67
    rw [step0,step1,t1]
    exact (by decide : ∀ a b d e f g x y : Bool, xor (xor d e) f=true →
      xor (cell67 a b d e f x) (cell67 b d e f g y)=!(xor (xor (xor (xor a b) d) x) y)) _ _ _ _ _ _ _ _ h
  · intro diff
    apply edgeBad hk hr hw hN u c w
    intro eqn
    apply diff
    rw [h1,h1,aSame _ (by omega) (by omega),aSame _ (by omega) (by omega)]
    exact congrArg _ eqn

end PEqualNP.Outside.L_meta_25567_aux

namespace PEqualNP.Outside.L_meta_25567_aux

def startW {k : Nat} (u w : Word k) : Word k :=
  ⟨rot k 1 w.val ^^^ u.val, xor_lt (rot_lt k 1 w.val) u.isLt⟩

theorem startInj {k : Nat} (hk : 2≤k) (u : Word k) : Function.Injective (startW u) := by
  intro a b ab
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<k
  · have pos : 0<k := by omega
    have A := congrArg (fun w : Word k => per w (j+1)) ab
    have hmod := mod_sub_eq (k:=k) (s:=1) (p:=j+1) pos (by omega)
    rw [show j+1-1=j by omega,Nat.mod_eq_of_lt hj] at hmod
    simp only [per,startW,Nat.testBit_xor,testBit_rot a.isLt (Nat.mod_lt _ pos),
      testBit_rot b.isLt (Nat.mod_lt _ pos),hmod] at A
    revert A
    cases a.val.testBit j <;> cases b.val.testBit j <;> cases u.val.testBit ((j+1) % k) <;> decide
  · have zero (w : Word k) : w.val.testBit j=false :=
      Nat.testBit_lt_two_pow (w.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega : k≤j)))
    rw [zero a,zero b]

theorem rangeCard (N : Nat) (p : Nat→Bool) :
    ((List.range N).filter p).length=(Finset.univ.filter (fun x : Fin N => p x.val=true)).card := by
  have h1 : ((List.range N).filter p).length=((Finset.range N).filter (fun n => p n=true)).card := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [List.range_succ,List.filter_append,List.length_append,Finset.range_add_one,Finset.filter_insert]
      by_cases h : p N=true
      · simp [h,ih,Finset.card_insert_of_notMem]
      · have hf : p N=false := Bool.eq_false_iff.2 h
        simp [h,hf,ih]
  rw [h1]
  apply Finset.card_bij (fun n hn => (⟨n,Finset.mem_range.1 (Finset.mem_filter.1 hn).1⟩ : Fin N))
  · intro n hn
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _,(Finset.mem_filter.1 hn).2⟩
  · intro a _ b _ eqn; exact congrArg Fin.val eqn
  · intro w hw
    refine ⟨w.val,Finset.mem_filter.2 ⟨Finset.mem_range.2 w.isLt,(Finset.mem_filter.1 hw).2⟩,?_⟩
    exact Fin.ext rfl

def rawPair {k : Nat} (u : Word k) (c : Nat→Word k) (r i w : Nat) :=
  ((stateAt k u c r w).testBit i,(stateAt k u c r w).testBit ((i+1) % k))

theorem transport {k r i : Nat} (hk : 6≤r) (hw : k+3=5*r) (hi : i<k)
    (u : Word k) (c : Nat→Word k) (target : Bool×Bool) :
    ((List.range (2^k)).filter (fun w=>rawPair u c r i w == target)).length =
      (Finset.univ.filter (fun w => result67 u c r (k+i) w=target)).card := by
  classical
  have ev (w : Word k) : result67 u c r (k+i) (startW u w) = rawPair u c r i w.val := by
    have bit (j : Nat) : lineStep k u c (per (startW u w)) r (k+j) = (stateAt k u c r w.val).testBit (j % k) := by
      have eqn := lineStep_eq_stateAt (by omega : 2≤k) u c w r (k+j) (by omega)
      change lineStep k u c (fun n=>(rot k 1 w.val ^^^ u.val).testBit (n % k)) r (k+j)=_
      simpa only [Nat.add_mod_left] using eqn
    apply Prod.ext
    · simpa only [result67,rawPair,Nat.mod_eq_of_lt hi] using bit i
    · simpa only [result67,rawPair,Nat.add_assoc] using bit (i+1)
  rw [rangeCard]
  apply Finset.card_bij (fun w _ => startW u w)
  · intro w hw
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rw [ev]
    exact beq_iff_eq.mp (Finset.mem_filter.mp hw).2
  · exact fun _ _ _ _ h => startInj (by omega) u h
  · intro z hz
    obtain ⟨w,rfl⟩ := Finite.surjective_of_injective (startInj (by omega) u) z
    refine ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,beq_iff_eq.mpr ?_⟩,rfl⟩
    rw [←ev]
    exact (Finset.mem_filter.mp hz).2
end PEqualNP.Outside.L_meta_25567_aux

namespace PEqualNP.Outside.L_meta_25567_aux
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
end PEqualNP.Outside.L_meta_25567_aux

namespace PEqualNP.Outside.L_meta_25567_aux

private theorem earlyToggle67 {k s p t : Nat} (hk : 0<k) (hs : s≤2) (hp : s+2≤p)
    (u : Word k) (c : Nat→Word k) (w : Word k) (ht : p-s=t) (br : p+3*s<t+k) :
    lineStep k u c (per (flipWord hk t w)) s p=!(lineStep k u c (per w) s p) := by
  induction s generalizing p with
  | zero =>
    have eq : p=t := by omega
    subst p
    exact per_toggle hk t w
  | succ s ih =>
    have left := ih (by omega) (p:=p-1) (by omega) (by omega) (by omega)
    have same (j : Nat) (jl : p≤j) (jr : j≤p+3) :
        lineStep k u c (per (flipWord hk t w)) s j=lineStep k u c (per w) s j := by
      apply lineStep_agree_interval k u c _ _ (t+1) (p+3*(s+1))
      · intro z lo hi
        exact per_same hk w (by omega) (by omega) (by omega)
      · omega
      · omega
    have inj : lInj u c (per (flipWord hk t w)) (s+1) p=lInj u c (per w) (s+1) p := by
      unfold lInj
      rw [per_same hk w (by omega) (by omega) (by omega)]
    rw [step67,step67,left,same p (by omega) (by omega),same (p+1) (by omega) (by omega),
      same (p+2) (by omega) (by omega),same (p+3) (by omega) (by omega),inj]
    exact (by decide : ∀ a b d e f j : Bool, cell67 (!a) b d e f j = !(cell67 a b d e f j)) _ _ _ _ _ _

private def fresh67 (Q s : Nat) := if s≤2 then Q-4*s-3 else Q-5*s

private theorem law67 {k r N : Nat} (hr : 6≤r) (hw : k+3=5*r) (hN : k≤N)
    (u : Word k) (c : Nat→Word k) (t : Nat) (ht : t<r-1) (nt : t≠3) :
    let Q := N+3*r
    let p := fresh67 Q t
    let F := flipWord (show 0<k by omega) p
    (∀ w,badGuard u c Q t (F w)=!(badGuard u c Q t w)) ∧
      ∀ w j,j<t → j≠3 → badGuard u c Q j (F w)=badGuard u c Q j w := by
  intro Q p F
  have kp : 0<k := by omega
  have top : Q<p+k := by dsimp [p,fresh67,Q]; split <;> omega
  have past {j : Nat} (h : j<t) : p<fresh67 Q j := by
    dsimp [p,fresh67,Q];split <;> split <;> omega
  have left (s : Nat) (w : Word k) (pos : Nat) (zlo : Q-3*s-3≤pos) (zhi : pos≤Q-3*s-1)
      (sr : s<r-1) (lower : p+1+s≤pos) (lower2 : p+1+2*s-3≤pos) :
      lineStep k u c (per (F w)) s pos=lineStep k u c (per w) s pos := by
    apply lineStep_agree_interval k u c _ _ (p+1) Q
    · intro z hl hr'
      exact per_same kp w (by omega) (by omega) (by omega)
    · omega
    · dsimp [Q] at *; omega
  constructor
  · intro w
    let d := Q-3*t-1
    have tog : lineStep k u c (per (F w)) t (d-2)=!(lineStep k u c (per w) t (d-2)) := by
      by_cases small : t≤2
      · apply earlyToggle67 kp small (by dsimp [d,Q]; omega) u c w
        · simp only [p,fresh67,ite_eq_left small];dsimp [d,Q];omega
        · dsimp [d,Q] at *;omega
      · apply valToggle kp (by omega) (by dsimp [d,Q]; omega) u c w
        · simp only [p,fresh67,ite_eq_right small];dsimp [d,Q];omega
        · dsimp [d,Q] at *;omega
    have eq (j : Nat) (lj : d-1≤j) (rj : j≤d) :
        lineStep k u c (per (F w)) t j=lineStep k u c (per w) t j := by
      apply left t w j (by dsimp [d,Q] at *;omega) rj ht
      · dsimp [p,d,Q,fresh67] at *; split <;> omega
      · dsimp [p,d,Q,fresh67] at *; split <;> omega
    change xor (xor (lineStep k u c (per (F w)) t (d-2)) (lineStep k u c (per (F w)) t (d-1)))
      (lineStep k u c (per (F w)) t d) = !(xor (xor (lineStep k u c (per w) t (d-2))
      (lineStep k u c (per w) t (d-1))) (lineStep k u c (per w) t d))
    rw [tog,eq (d-1) (by omega) (by omega),eq d (by omega) (by omega)]
    exact (by decide : ∀ a b c : Bool, xor (xor (!a) b) c=!(xor (xor a b) c)) _ _ _
  · intro w j jt nj
    let d := Q-3*j-1
    have pe := past jt
    have eq (pos : Nat) (lo : d-2≤pos) (hi : pos≤d) :
        lineStep k u c (per (F w)) j pos=lineStep k u c (per w) j pos := by
      apply left j w pos (by dsimp [d,Q] at *;omega) hi (by omega)
      · dsimp only [fresh67] at pe
        split at pe <;> dsimp [d,Q] at * <;> omega
      · dsimp only [fresh67] at pe
        split at pe <;> dsimp [d,Q] at * <;> omega
    change xor (xor (lineStep k u c (per (F w)) j (d-2)) (lineStep k u c (per (F w)) j (d-1)))
      (lineStep k u c (per (F w)) j d)=_
    rw [eq (d-2) (by omega) (by omega),eq (d-1) (by omega) (by omega),eq d (by omega) (by omega)]
    rfl

noncomputable def badSet67 {k : Nat} (u : Word k) (c : Nat→Word k) (Q r : Nat) :
    Finset (Word k) := by classical exact Finset.univ.filter (bad67 u c Q r)

theorem badCount67 {k r N : Nat} (hr : 6≤r) (hw : k+3=5*r) (hN : k≤N)
    (u : Word k) (c : Nat→Word k) :
    (badSet67 u c (N+3*r) r).card=2^(k-r+2) := by
  classical
  let Q := N+3*r
  let slot := fun j : Nat => if j<3 then j else j+1
  let G := fun w j => badGuard u c Q (slot j) w
  have bound (j : Nat) (hj : j<r-2) : slot j<r-1 ∧ slot j≠3 := by dsimp [slot];split <;> omega
  have same : badSet67 u c Q r =
      Finset.univ.filter (fun w : Word k=>decide (∀t:Fin (r-2),G w t.val=false)) := by
    ext w
    simp only [badSet67,Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq]
    constructor
    · intro a j
      exact a _ (bound j j.isLt).1 (bound j j.isLt).2
    · intro a t ht ne
      by_cases sm : t<3
      · simpa [G,slot,sm] using a ⟨t,by omega⟩
      · have prev : ¬t-1<3 := by omega
        simpa [G,slot,prev,show t-1+1=t by omega] using a ⟨t-1,by omega⟩
  change (badSet67 u c Q r).card=_
  rw [same,show k-r+2=k-(r-2) by omega]
  apply halves k (r-2) (by omega) G (by simp [Word])
  intro j hj
  obtain ⟨now,prior⟩ := law67 hr hw hN u c (slot j) (bound j hj).1 (bound j hj).2
  refine ⟨flipWord (show 0<k by omega) (fresh67 Q (slot j)),flip_flip _ _,now,?_⟩
  intro w t ht
  exact prior w (slot t) (by dsimp [slot];split <;> split <;> omega) (bound t (by omega)).2

end PEqualNP.Outside.L_meta_25567_aux

namespace PEqualNP.Outside.L_meta_25567_aux

def sg (reference b : Bool) : Int := if b=reference then 1 else -1
theorem sg_not (ref b : Bool) : sg ref (!b) = -sg ref b := by cases ref <;> cases b <;> decide
theorem sumInv {α : Type} [Fintype α] (f : α→α) (hf : ∀a,f (f a)=a) (g : α→Int) :
  (∑a,g (f a))=∑a,g a := (Equiv.sum_comp (⟨f,f,hf,hf⟩ : α≃α) g)
theorem sumZero {α : Type} [Fintype α] (f : α→α) (hf : ∀a,f (f a)=a) (g : α→Int)
    (flip : ∀a,g (f a)=-(g a)) : ∑a,g a=0 := by
  have z := sumInv f hf g
  simp only [flip,Finset.sum_neg_distrib] at z
  omega

theorem quarterCount {α : Type} [Fintype α] (A B C : α→α) (F : α→Bool×Bool) (H T : α→Bool)
    (Bad : α→Prop) [DecidablePred Bad] (ai : ∀w,A (A w)=w) (bi : ∀w,B (B w)=w) (ci : ∀w,C (C w)=w)
    (laws : ∀ w,
      (F (B w)).1 = !((F w).1) ∧ (F (C w)).2 = !((F w).2) ∧ H (C w)=H w ∧
      (H w=false → par67 (F (C w))=!(par67 (F w))) ∧
      T (A w)=!(T w) ∧ (H w=true → par67 (F w)=T w) ∧ (H (A w)≠H w → Bad w))
    (target : Bool×Bool) :
    let N := Fintype.card α
    let n := (Finset.univ.filter (fun w=> F w=target)).card
    let b := (Finset.univ.filter Bad).card
    2*N≤8*n+b ∧ 8*n≤2*N+b := by
  intro N n b
  let X := fun w=>sg target.1 (F w).1
  let Y := fun w=>sg target.2 (F w).2
  let Z := fun w=>sg (par67 target) (par67 (F w))
  let U := fun w=>if H w then sg (par67 target) (T w) else 0
  let V := fun w=>if H w then 0 else Z w
  have zx : ∑w,X w=0 := sumZero B bi X (fun w => by simp only [X,(laws w).1,sg_not])
  have zy : ∑w,Y w=0 := sumZero C ci Y (fun w => by simp only [Y,(laws w).2.1,sg_not])
  have zv : ∑w,V w=0 := by
    apply sumZero C ci
    intro w
    simp only [V,(laws w).2.2.1]
    cases h : H w
    · simp [Z,(laws w).2.2.2.1 h,sg_not]
    · simp
  have uv (w : α) : Z w=U w+V w := by
    cases h : H w
    · simp [U,V,h]
    · simp [U,V,Z,h,(laws w).2.2.2.2.2.1 h]
  have uni : ∑w,Z w=∑w,U w := by simp only [uv,Finset.sum_add_distrib,zv,add_zero]
  have per (w : α) :  -(if Bad w then 1 else 0 : Int)≤U w+U (A w) ∧
                        U w+U (A w)≤(if Bad w then 1 else 0 : Int) := by
    have diff := (laws w).2.2.2.2.2.2
    rcases Bool.eq_false_or_eq_true (H w) with h|h <;>
      rcases Bool.eq_false_or_eq_true (H (A w)) with ha|ha
    all_goals simp only [U,h,ha,Bool.false_eq_true,ite_false,ite_true,(laws w).2.2.2.2.1,sg_not]
    all_goals first | (have hb : Bad w := diff (by rw [h,ha];decide); rw [ite_eq_left hb];cases T w <;> cases par67 target <;> decide) |
      (split <;> omega)
  have ub := Finset.sum_le_sum (s:=Finset.univ) (fun w _ => (per w).2)
  have lb := Finset.sum_le_sum (s:=Finset.univ) (fun w _ => (per w).1)
  simp only [Finset.sum_add_distrib,sumInv A ai U,Finset.sum_boole,Finset.sum_neg_distrib] at lb ub
  have ident (w : α) : 4*(if F w=target then 1 else 0 : Int)=1+X w+Y w+Z w := by
    rcases h : F w with ⟨a,d⟩
    rcases target with ⟨e,f⟩
    simp only [X,Y,Z,h]
    cases a <;> cases d <;> cases e <;> cases f <;> decide
  have sums := Finset.sum_congr (s₁:=Finset.univ) rfl (fun w _ => ident w)
  simp only [←Finset.mul_sum,Finset.sum_boole,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,mul_one,zx,zy,add_zero,uni] at sums
  change -((b : Nat) : Int) ≤ _ at lb
  change _ ≤ ((b : Nat) : Int) at ub
  change 4*(n:Int)=(N:Int)+_ at sums

  omega

end PEqualNP.Outside.L_meta_25567_aux

namespace PEqualNP.Outside.L_meta_25567_aux
open Classical in
theorem package67 {k r i : Nat} (hr : 6≤r) (hw : k+3=5*r) (hi : i<k)
    (u : Word k) (c : Nat→Word k)
    (target : Bool×Bool) :
    let n := ((List.range (2^k)).filter (fun w=>rawPair u c r i w == target)).length
    2^(k-2) ≤ n+2^(k-r-1) ∧ n≤2^(k-2)+2^(k-r-1) := by
  classical
  intro n
  have hk : 0<k := by omega
  let N := k+i
  let P := N+3-2*r
  let F := result67 u c r N
  have hbad : (badSet67 u c (N+3*r) r).card ≤ 2^(k-r+2) := (badCount67 hr hw (by dsimp [N];omega : k≤N) u c).le
  have b := quarterCount (flipWord hk P) (flipWord hk (P+1)) (flipWord hk (P+2)) F (h67 u c r N) (t67 u c r N)
    (bad67 u c (N+3*r) r) (flip_flip hk P) (flip_flip hk (P+1)) (flip_flip hk (P+2))
    (laws67 hk hr hw (by dsimp [N];omega : k≤N) u c) target
  dsimp only at b
  have card : Fintype.card (Word k) = 2^k := Fintype.card_fin _
  have tran : (Finset.univ.filter (fun w => F w = target)).card=n := (transport hr hw hi u c target).symm
  rw [tran,card] at b
  change (Finset.univ.filter (bad67 u c (N+3*r) r)).card≤_ at hbad
  have exp : 2^k=4*2^(k-2) := by
    calc 2^k = 2^((k-2)+2) := by congr 1;omega
         _ = 4*2^(k-2) := by rw [pow_add];omega
  have errexp : 2^(k-r+2)=8*2^(k-r-1) := by
    calc 2^(k-r+2) = 2^((k-r-1)+3) := by congr 1;omega
         _ = 8*2^(k-r-1) := by rw [pow_add];omega


  omega
end PEqualNP.Outside.L_meta_25567_aux

theorem PEqualNP.Outside.L_meta_25567 :
∀ (k r : Nat), 6 ≤ r → k + 3 = 5 * r →
  ∀ (c : Nat → Fin (2 ^ k)) (u i : Nat), u < 2 ^ k → i < k →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc b =>
      acc ||| ((xor (word.testBit b)
        (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0
  let state := fun (key : Nat) =>
    (List.range r).foldl (fun prev t =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * t) key ^^^
        (c (t + 1)).val) (rot 1 key ^^^ u)
  let out := fun (key : Nat) =>
    let word := state key
    (word.testBit i, word.testBit ((i + 1) % k))
  ∀ target : Bool × Bool,
    let countTarget := ((List.range (2 ^ k)).filter (fun candidate => out candidate == target)).length
    let quarter := 2 ^ (k - 2)
    let error := 2 ^ (k - r - 1)
    quarter ≤ countTarget + error ∧ countTarget ≤ quarter + error := by
  intro k r hr hw c u i hu hi
  exact PEqualNP.Outside.L_meta_25567_aux.package67 hr hw hi ⟨u,hu⟩ c
