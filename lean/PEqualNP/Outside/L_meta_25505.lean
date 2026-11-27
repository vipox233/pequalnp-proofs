import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25505_aux

def rot (k s w : Nat) : Nat :=
  ((w <<< (s % k)) ||| (w >>> (k - s % k))) % 2 ^ k

def step (k x : Nat) : Nat :=
  (List.range k).foldl (fun acc b =>
    acc ||| ((xor (x.testBit b)
      (!(x.testBit ((b + 1) % k)) && x.testBit ((b + 2) % k))).toNat <<< b)) 0

def stateAux (k : Nat) (constants : Nat → Fin (2 ^ k)) (u key rounds : Nat) : Nat :=
  (List.range rounds).foldl (fun prev t =>
    step k (prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev) ^^^ rot k (2 * t) key ^^^
      (constants (t + 1)).val) (rot k 1 key ^^^ u)

lemma rot_lt (k s w : Nat) : rot k s w < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma testBit_rot (k s w i : Nat) (hw : w < 2 ^ k) (hi : i < k) :
    (rot k s w).testBit i = w.testBit ((i + k - s % k) % k) := by
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have hs : s % k < k := Nat.mod_lt s hk
  unfold rot
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and,
      Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases hle : s % k ≤ i
  · have hge : k ≤ k - s % k + i := by omega
    have hfalse : w.testBit (k - s % k + i) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) hge))
    have hmod : (i + k - s % k) % k = i - s % k := by
      have h1 : i + k - s % k = (i - s % k) + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [decide_eq_true hle, Bool.true_and, hfalse, Bool.or_false, hmod]
  · have hlt : i + k - s % k < k := by omega
    have hmod : (i + k - s % k) % k = k - s % k + i := by
      rw [Nat.mod_eq_of_lt hlt]
      omega
    rw [decide_eq_false hle, Bool.false_and, Bool.false_or, hmod]

lemma foldl_step_props (k x : Nat) (n : Nat) (hn : n ≤ k) :
    let f := fun (acc b : Nat) =>
      acc ||| ((xor (x.testBit b)
        (!(x.testBit ((b + 1) % k)) && x.testBit ((b + 2) % k))).toNat <<< b)
    (List.range n).foldl f 0 < 2 ^ n ∧
    ∀ b < n, ((List.range n).foldl f 0).testBit b =
      xor (x.testBit b) (!(x.testBit ((b + 1) % k)) && x.testBit ((b + 2) % k)) := by
  induction n with
  | zero =>
    refine ⟨by simp, ?_⟩
    intro b hb
    omega
  | succ m ih =>
    obtain ⟨hlt, hbit⟩ := ih (by omega)
    have hr : List.range (m + 1) = List.range m ++ [m] := List.range_succ
    dsimp only
    rw [hr, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set acc := (List.range m).foldl (fun acc b =>
      acc ||| ((xor (x.testBit b)
        (!(x.testBit ((b + 1) % k)) && x.testBit ((b + 2) % k))).toNat <<< b)) 0
    set bit := xor (x.testBit m) (!(x.testBit ((m + 1) % k)) && x.testBit ((m + 2) % k))
    have hlt_b : bit.toNat <<< m < 2 ^ (m + 1) := by
      rw [Nat.shiftLeft_eq, Nat.pow_succ']
      cases bit <;> simp
    have hlt_acc : acc < 2 ^ (m + 1) :=
      Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega))
    refine ⟨Nat.or_lt_two_pow hlt_acc hlt_b, ?_⟩
    intro b hb
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hbm : b < m
    · rw [decide_eq_false (by omega), Bool.false_and, Bool.or_false]
      exact hbit b hbm
    · have heq : b = m := by omega
      subst heq
      have hacc_false : acc.testBit b = false := Nat.testBit_lt_two_pow hlt
      rw [hacc_false, Bool.false_or, decide_eq_true (Nat.le_refl b), Bool.true_and, Nat.sub_self]
      show bit.toNat.testBit 0 = bit
      cases bit <;> rfl

lemma step_lt (k x : Nat) : step k x < 2 ^ k :=
  (foldl_step_props k x k (Nat.le_refl k)).1

lemma testBit_step (k x b : Nat) (hb : b < k) :
    (step k x).testBit b =
      xor (x.testBit b) (!(x.testBit ((b + 1) % k)) && x.testBit ((b + 2) % k)) :=
  (foldl_step_props k x k (Nat.le_refl k)).2 b hb

lemma stateAux_zero (k : Nat) (constants : Nat → Fin (2 ^ k)) (u key : Nat) :
    stateAux k constants u key 0 = rot k 1 key ^^^ u := rfl

lemma stateAux_succ (k : Nat) (constants : Nat → Fin (2 ^ k)) (u key t : Nat) :
    stateAux k constants u key (t + 1) =
      step k (stateAux k constants u key t ^^^ rot k 1 (stateAux k constants u key t) ^^^
        rot k (k - 1) (stateAux k constants u key t)) ^^^
      rot k (2 * t) key ^^^ (constants (t + 1)).val := by
  unfold stateAux
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma stateAux_lt (k : Nat) (constants : Nat → Fin (2 ^ k)) (u key t : Nat) (hu : u < 2 ^ k) :
    stateAux k constants u key t < 2 ^ k := by
  induction t with
  | zero =>
    rw [stateAux_zero]
    exact Nat.xor_lt_two_pow (rot_lt k 1 key) hu
  | succ m _ =>
    rw [stateAux_succ]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (step_lt k _) (rot_lt k (2 * m) key)) (constants (m + 1)).isLt

lemma flip_lt (k w a : Nat) (hw : w < 2 ^ k) (ha : a < k) :
    w ^^^ (1 <<< a) < 2 ^ k := by
  have h1 : 1 <<< a < 2 ^ k := by
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.pow_lt_pow_right (by omega) ha
  exact Nat.xor_lt_two_pow hw h1

lemma testBit_one_shiftLeft (a x : Nat) :
    (1 <<< a).testBit x = decide (x = a) := by
  rw [Nat.testBit_shiftLeft]
  by_cases hax : a ≤ x
  · rw [decide_eq_true hax, Bool.true_and]
    by_cases heq : x = a
    · subst heq; simp
    · have hpos : 0 < x - a := by omega
      have hgt : 1 < 2 ^ (x - a) := by
        calc 1 = 2 ^ 0 := rfl
          _ < 2 ^ (x - a) := Nat.pow_lt_pow_right (by omega) hpos
      rw [Nat.testBit_lt_two_pow hgt, decide_eq_false heq]
  · rw [decide_eq_false hax, Bool.false_and, decide_eq_false (by omega)]

lemma testBit_rot_flip_xor (k s w a q : Nat) (hw : w < 2 ^ k) (ha : a < k) (hq : q < k) :
    xor ((rot k s w).testBit q) ((rot k s (w ^^^ (1 <<< a))).testBit q) =
      decide (q = (a + s) % k) := by
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le q) hq
  rw [testBit_rot k s w q hw hq, testBit_rot k s (w ^^^ (1 <<< a)) q (flip_lt k w a hw ha) hq,
      Nat.testBit_xor, testBit_one_shiftLeft]
  have hcancel : ∀ x y : Bool, xor x (xor x y) = y := by intro x y; cases x <;> cases y <;> rfl
  rw [hcancel]
  have hiff : (q + k - s % k) % k = a ↔ q = (a + s) % k := by
    have hs : s % k < k := Nat.mod_lt s hk
    have hdiv := Nat.div_add_mod s k
    constructor
    · intro h
      have h1 : (q + k - s % k + s) % k = (a + s) % k := by
        rw [Nat.add_mod, h, Nat.add_mod_mod]
      have h2 : q + k - s % k + s = q + k * (s / k + 1) := by
        rw [Nat.mul_add, Nat.mul_one]; omega
      rw [h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq] at h1
      exact h1
    · intro h
      subst h
      have h2 : (((a + s) % k + k - s % k) + s % k) % k = (a + s % k) % k := by
        have h3 : ((a + s) % k + k - s % k) + s % k + k * ((a + s) / k) = (a + s % k) + k * (s / k + 1) := by
          have has := Nat.div_add_mod (a + s) k
          have has_lt : (a + s) % k < k := Nat.mod_lt _ hk
          rw [Nat.mul_add, Nat.mul_one]; omega
        have h4 := congrArg (· % k) h3
        simp only [Nat.add_mul_mod_self_left] at h4
        exact h4
      have hcancel_mod : ∀ x y z : Nat, (x + z) % k = (y + z) % k → x % k = y % k := by
        intro x y z hxy
        have hxz : ((x + z) + (k - z % k)) % k = ((y + z) + (k - z % k)) % k := by
          rw [Nat.add_mod, hxy, ← Nat.add_mod]
        have hzlt : z % k < k := Nat.mod_lt z hk
        have hzs : (z + (k - z % k)) % k = 0 := by
          have := Nat.div_add_mod z k
          have h' : z + (k - z % k) = k * (z / k + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
          rw [h', Nat.mul_mod_right]
        have hl' : ((x + z) + (k - z % k)) % k = x % k := by
          rw [Nat.add_assoc, Nat.add_mod, hzs, Nat.add_zero, Nat.mod_mod]
        have hr' : ((y + z) + (k - z % k)) % k = y % k := by
          rw [Nat.add_assoc, Nat.add_mod, hzs, Nat.add_zero, Nat.mod_mod]
        rw [hl', hr'] at hxz
        exact hxz
      have h5 := hcancel_mod _ _ (s % k) h2
      rw [Nat.mod_eq_of_lt ha] at h5
      exact h5
  exact Bool.eq_iff_iff.mpr (by simpa [decide_eq_true_eq] using hiff)

lemma testBit_rot_k_sub_1 (k prev q : Nat) (hk : 2 ≤ k) (hprev : prev < 2 ^ k) (hq : q < k) :
    (rot k (k - 1) prev).testBit q = prev.testBit ((q + 1) % k) := by
  rw [testBit_rot k (k - 1) prev q hprev hq]
  have h1 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  have h2 : q + k - (k - 1) = q + 1 := by omega
  rw [h2]

lemma testBit_lin (k prev q : Nat) (hk : 2 ≤ k) (hprev : prev < 2 ^ k) (hq : q < k) :
    (prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev).testBit q =
      xor (xor (prev.testBit q) (prev.testBit ((q + k - 1 % k) % k))) (prev.testBit ((q + 1) % k)) := by
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rot k 1 prev q hprev hq,
      testBit_rot_k_sub_1 k prev q hk hprev hq]

lemma mod_add_sub_cancel (k base x : Nat) (hk : 2 ≤ k) (hx : 1 ≤ x) :
    ((base + x) % k + k - 1 % k) % k = (base + (x - 1)) % k := by
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  have hlt : (base + x) % k < k := Nat.mod_lt _ (by omega)
  have hdiv := Nat.div_add_mod (base + x) k
  have h3 : ((base + x) % k + k - 1) + k * ((base + x) / k) = (base + (x - 1)) + k := by omega
  have h4 := congrArg (· % k) h3
  simp only [Nat.add_mul_mod_self_left, Nat.add_mod_right] at h4
  exact h4

lemma mod_add_n (k base x n : Nat) :
    ((base + x) % k + n) % k = (base + (x + n)) % k := by
  rw [Nat.mod_add_mod, Nat.add_assoc]

lemma step_right_endpoint_xor (k prev1 prev2 base x : Nat) (hk : 2 ≤ k)
    (hp1 : prev1 < 2 ^ k) (hp2 : prev2 < 2 ^ k) (hx : 1 ≤ x)
    (hm1 : prev1.testBit ((base + (x - 1)) % k) = prev2.testBit ((base + (x - 1)) % k))
    (h0 : prev1.testBit ((base + x) % k) = prev2.testBit ((base + x) % k))
    (h1 : prev1.testBit ((base + (x + 1)) % k) = prev2.testBit ((base + (x + 1)) % k))
    (h2 : prev1.testBit ((base + (x + 2)) % k) = prev2.testBit ((base + (x + 2)) % k)) :
    let l1 := prev1 ^^^ rot k 1 prev1 ^^^ rot k (k - 1) prev1
    let l2 := prev2 ^^^ rot k 1 prev2 ^^^ rot k (k - 1) prev2
    xor ((step k l1).testBit ((base + x) % k)) ((step k l2).testBit ((base + x) % k)) =
      (!(xor (xor (prev1.testBit ((base + x) % k)) (prev1.testBit ((base + (x + 1)) % k)))
             (prev1.testBit ((base + (x + 2)) % k))) &&
       xor (prev1.testBit ((base + (x + 3)) % k)) (prev2.testBit ((base + (x + 3)) % k))) := by
  dsimp only
  have hq0 : (base + x) % k < k := Nat.mod_lt _ (by omega)
  have hq1 : (base + (x + 1)) % k < k := Nat.mod_lt _ (by omega)
  have hq2 : (base + (x + 2)) % k < k := Nat.mod_lt _ (by omega)
  rw [testBit_step k _ _ hq0, testBit_step k _ _ hq0]
  rw [mod_add_n k base x 1, mod_add_n k base x 2]
  rw [testBit_lin k prev1 _ hk hp1 hq0, testBit_lin k prev2 _ hk hp2 hq0]
  rw [testBit_lin k prev1 _ hk hp1 hq1, testBit_lin k prev2 _ hk hp2 hq1]
  rw [testBit_lin k prev1 _ hk hp1 hq2, testBit_lin k prev2 _ hk hp2 hq2]
  rw [mod_add_sub_cancel k base x hk hx,
      mod_add_sub_cancel k base (x + 1) hk (by omega),
      mod_add_sub_cancel k base (x + 2) hk (by omega)]
  rw [mod_add_n k base x 1, mod_add_n k base (x + 1) 1, mod_add_n k base (x + 2) 1]
  have ha1 : x + 1 - 1 = x := by omega
  have ha2 : x + 2 - 1 = x + 1 := by omega
  have hb2 : x + 1 + 1 = x + 2 := by omega
  have hb3 : x + 2 + 1 = x + 3 := by omega
  rw [ha1, ha2, hb2, hb3, hm1, h0, h1, h2]
  cases prev2.testBit ((base + (x - 1)) % k) <;>
  cases prev2.testBit ((base + x) % k) <;>
  cases prev2.testBit ((base + (x + 1)) % k) <;>
  cases prev2.testBit ((base + (x + 2)) % k) <;>
  cases prev1.testBit ((base + (x + 3)) % k) <;>
  cases prev2.testBit ((base + (x + 3)) % k) <;> rfl

lemma xor_eq_false_iff (a b : Bool) : xor a b = false ↔ a = b := by
  cases a <;> cases b <;> decide

lemma xor_eq_true_iff (a b : Bool) : xor a b = true ↔ a ≠ b := by
  cases a <;> cases b <;> decide

lemma mod_ne_of_lt (k base x y : Nat) (hx : x < k) (hy : y < k) (hne : x ≠ y) :
    (base + x) % k ≠ (base + y) % k := by
  intro heq
  have hk : 0 < k := by omega
  have hxz : ((base + x) + (k - base % k)) % k = ((base + y) + (k - base % k)) % k := by
    rw [Nat.add_mod, heq, ← Nat.add_mod]
  have hblt : base % k < k := Nat.mod_lt base hk
  have hbs : (base + (k - base % k)) % k = 0 := by
    have := Nat.div_add_mod base k
    have h' : base + (k - base % k) = k * (base / k + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    rw [h', Nat.mul_mod_right]
  have hl : ((base + x) + (k - base % k)) % k = x := by
    rw [Nat.add_right_comm, Nat.add_mod, hbs, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hx]
  have hr : ((base + y) + (k - base % k)) % k = y := by
    rw [Nat.add_right_comm, Nat.add_mod, hbs, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hy]
  rw [hl, hr] at hxz
  exact hne hxz

lemma key_pos_eq (k r i t : Nat) (hr : 4 ≤ r) (hkr : k + 3 = 5 * r) :
    ((i + 3 * r - 1) % k + 2 * t) % k = (i + k - r + (4 * r - 1 + 2 * t)) % k := by
  rw [Nat.mod_add_mod]
  have h1 : (i + 3 * r - 1) + 2 * t + k = i + k - r + (4 * r - 1 + 2 * t) := by omega
  rw [← h1, Nat.add_mod_right]

lemma key_no_hit_interior (k r i t x : Nat) (hr : 4 ≤ r) (hkr : k + 3 = 5 * r)
    (ht : t + 1 < r) (hx1 : t + 1 ≤ x) (hx2 : x ≤ 4 * r - 3 * (t + 1)) :
    (i + k - r + x) % k ≠ ((i + 3 * r - 1) % k + 2 * t) % k := by
  rw [key_pos_eq k r i t hr hkr]
  by_cases hlt : 4 * r - 1 + 2 * t < k
  · exact mod_ne_of_lt k (i + k - r) x (4 * r - 1 + 2 * t) (by omega) hlt (by omega)
  · have hwrap : (i + k - r + (4 * r - 1 + 2 * t)) % k = (i + k - r + (4 * r - 1 + 2 * t - k)) % k := by
      have h1 : i + k - r + (4 * r - 1 + 2 * t) = (i + k - r + (4 * r - 1 + 2 * t - k)) + k := by omega
      rw [h1, Nat.add_mod_right]
    rw [hwrap]
    exact mod_ne_of_lt k (i + k - r) x (4 * r - 1 + 2 * t - k) (by omega) (by omega) (by omega)

lemma state_agree_interior (k r : Nat) (constants : Nat → Fin (2 ^ k)) (u i : Nat)
    (w : Fin (2 ^ k)) (hr : 4 ≤ r) (hkr : k + 3 = 5 * r) (hu : u < 2 ^ k) :
    let flip := w.val ^^^ (1 <<< ((i + 3 * r - 1) % k))
    ∀ t : Nat, t < r → ∀ x : Nat, t ≤ x → x < 4 * r - 3 * t →
      (stateAux k constants u w.val t).testBit ((i + k - r + x) % k) =
      (stateAux k constants u flip t).testBit ((i + k - r + x) % k) := by
  intro flip t
  induction t with
  | zero =>
    intro _ x _ hx2
    rw [stateAux_zero, stateAux_zero]
    have ha : (i + 3 * r - 1) % k < k := Nat.mod_lt _ (by omega)
    have hq : (i + k - r + x) % k < k := Nat.mod_lt _ (by omega)
    have hrot := testBit_rot_flip_xor k 1 w.val ((i + 3 * r - 1) % k) ((i + k - r + x) % k) w.isLt ha hq
    have hne : (i + k - r + x) % k ≠ ((i + 3 * r - 1) % k + 1) % k := by
      have h1 : ((i + 3 * r - 1) % k + 1) % k = (i + k - r + 4 * r) % k := by
        rw [Nat.mod_add_mod]
        have : (i + 3 * r - 1) + 1 + k = i + k - r + 4 * r := by omega
        rw [← this, Nat.add_mod_right]
      rw [h1]
      exact mod_ne_of_lt k (i + k - r) x (4 * r) (by omega) (by omega) (by omega)
    rw [decide_eq_false hne] at hrot
    have heq := (xor_eq_false_iff _ _).mp hrot
    rw [Nat.testBit_xor, Nat.testBit_xor, heq]
  | succ m ih =>
    intro hm x hx1 hx2
    have h1 := ih (by omega) (x - 1) (by omega) (by omega)
    have h2 := ih (by omega) x (by omega) (by omega)
    have h3 := ih (by omega) (x + 1) (by omega) (by omega)
    have h4 := ih (by omega) (x + 2) (by omega) (by omega)
    have h5 := ih (by omega) (x + 3) (by omega) (by omega)
    have hst := step_right_endpoint_xor k (stateAux k constants u w.val m) (stateAux k constants u flip m)
      (i + k - r) x (by omega) (stateAux_lt k constants u w.val m hu)
      (stateAux_lt k constants u flip m hu) (by omega) h1 h2 h3 h4
    rw [h5, Bool.xor_self, Bool.and_false] at hst
    have hst_eq := (xor_eq_false_iff _ _).mp hst
    have ha : (i + 3 * r - 1) % k < k := Nat.mod_lt _ (by omega)
    have hq : (i + k - r + x) % k < k := Nat.mod_lt _ (by omega)
    have hrot := testBit_rot_flip_xor k (2 * m) w.val ((i + 3 * r - 1) % k) ((i + k - r + x) % k) w.isLt ha hq
    have hne := key_no_hit_interior k r i m x hr hkr hm hx1 (by omega)
    rw [decide_eq_false hne] at hrot
    have hkey_eq := (xor_eq_false_iff _ _).mp hrot
    rw [stateAux_succ, stateAux_succ, Nat.testBit_xor, Nat.testBit_xor,
        Nat.testBit_xor, Nat.testBit_xor, hst_eq, hkey_eq]

lemma endpoint_xor_step (k r : Nat) (constants : Nat → Fin (2 ^ k)) (u i : Nat)
    (w : Fin (2 ^ k)) (hr : 4 ≤ r) (hkr : k + 3 = 5 * r) (hu : u < 2 ^ k)
    (t : Nat) (ht : t < r) :
    let flip := w.val ^^^ (1 <<< ((i + 3 * r - 1) % k))
    let z := stateAux k constants u w.val t
    let b := i + 3 * (r - (t + 1))
    let parity := xor (xor (z.testBit (b % k)) (z.testBit ((b + 1) % k))) (z.testBit ((b + 2) % k))
    let curDiff := xor ((stateAux k constants u w.val t).testBit ((i + 3 * (r - t)) % k))
                       ((stateAux k constants u flip t).testBit ((i + 3 * (r - t)) % k))
    xor ((stateAux k constants u w.val (t + 1)).testBit ((i + 3 * (r - (t + 1))) % k))
        ((stateAux k constants u flip (t + 1)).testBit ((i + 3 * (r - (t + 1))) % k)) =
      xor (!parity && curDiff) (decide (t + 1 = r)) := by
  intro flip z b parity curDiff
  have hpos_b : ∀ d : Nat, (i + k - r + (4 * r - 3 * (t + 1) + d)) % k = (b + d) % k := by
    intro d
    have h1 : i + k - r + (4 * r - 3 * (t + 1) + d) = (b + d) + k := by omega
    rw [h1, Nat.add_mod_right]
  have hpos0 : (i + k - r + (4 * r - 3 * (t + 1))) % k = b % k := by
    simpa using hpos_b 0
  have hpos3 : (i + k - r + (4 * r - 3 * (t + 1) + 3)) % k = (i + 3 * (r - t)) % k := by
    have h1 : i + k - r + (4 * r - 3 * (t + 1) + 3) = (i + 3 * (r - t)) + k := by omega
    rw [h1, Nat.add_mod_right]
  have x := 4 * r - 3 * (t + 1)
  have hm1 := state_agree_interior k r constants u i w hr hkr hu t ht (4 * r - 3 * (t + 1) - 1) (by omega) (by omega)
  have h0 := state_agree_interior k r constants u i w hr hkr hu t ht (4 * r - 3 * (t + 1)) (by omega) (by omega)
  have h1 := state_agree_interior k r constants u i w hr hkr hu t ht (4 * r - 3 * (t + 1) + 1) (by omega) (by omega)
  have h2 := state_agree_interior k r constants u i w hr hkr hu t ht (4 * r - 3 * (t + 1) + 2) (by omega) (by omega)
  have hst := step_right_endpoint_xor k (stateAux k constants u w.val t) (stateAux k constants u flip t)
    (i + k - r) (4 * r - 3 * (t + 1)) (by omega) (stateAux_lt k constants u w.val t hu)
    (stateAux_lt k constants u flip t hu) (by omega) hm1 h0 h1 h2
  rw [hpos0, hpos_b 1, hpos_b 2, hpos3] at hst
  have ha : (i + 3 * r - 1) % k < k := Nat.mod_lt _ (by omega)
  have hq : b % k < k := Nat.mod_lt _ (by omega)
  have hrot := testBit_rot_flip_xor k (2 * t) w.val ((i + 3 * r - 1) % k) (b % k) w.isLt ha hq
  have hkey_dec : decide (b % k = ((i + 3 * r - 1) % k + 2 * t) % k) = decide (t + 1 = r) := by
    by_cases hlast : t + 1 = r
    · rw [decide_eq_true hlast, decide_eq_true]
      rw [← hpos0, key_pos_eq k r i t hr hkr]
      have h1 : i + k - r + (4 * r - 1 + 2 * t) = (i + k - r + (4 * r - 3 * (t + 1))) + k := by omega
      rw [h1, Nat.add_mod_right]
    · rw [decide_eq_false hlast, decide_eq_false]
      rw [← hpos0]
      exact key_no_hit_interior k r i t (4 * r - 3 * (t + 1)) hr hkr (by omega) (by omega) (Nat.le_refl _)
  rw [hkey_dec] at hrot
  have hre : ∀ s1 s2 k1 k2 cc : Bool,
      xor (xor (xor s1 k1) cc) (xor (xor s2 k2) cc) = xor (xor s1 s2) (xor k1 k2) := by
    intro s1 s2 k1 k2 cc; cases s1 <;> cases s2 <;> cases k1 <;> cases k2 <;> cases cc <;> rfl
  change xor ((stateAux k constants u w.val (t + 1)).testBit (b % k))
             ((stateAux k constants u flip (t + 1)).testBit (b % k)) = _
  rw [stateAux_succ, stateAux_succ, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor,
      hre, hst, hrot]

lemma endpoint_diff_prefix (k r : Nat) (constants : Nat → Fin (2 ^ k)) (u i : Nat)
    (w : Fin (2 ^ k)) (hr : 4 ≤ r) (hkr : k + 3 = 5 * r) (hu : u < 2 ^ k) :
    let flip := w.val ^^^ (1 <<< ((i + 3 * r - 1) % k))
    ∀ m : Nat, m < r →
      ((xor ((stateAux k constants u w.val m).testBit ((i + 3 * (r - m)) % k))
            ((stateAux k constants u flip m).testBit ((i + 3 * (r - m)) % k)) = true) ↔
       (∀ s : Nat, s < m →
         let z := stateAux k constants u w.val s
         let b := i + 3 * (r - (s + 1))
         xor (xor (z.testBit (b % k)) (z.testBit ((b + 1) % k))) (z.testBit ((b + 2) % k)) = false)) := by
  intro flip m
  induction m with
  | zero =>
    intro _
    rw [stateAux_zero, stateAux_zero]
    have ha : (i + 3 * r - 1) % k < k := Nat.mod_lt _ (by omega)
    have hq : (i + 3 * (r - 0)) % k < k := Nat.mod_lt _ (by omega)
    have hrot := testBit_rot_flip_xor k 1 w.val ((i + 3 * r - 1) % k) ((i + 3 * (r - 0)) % k) w.isLt ha hq
    have heq : (i + 3 * (r - 0)) % k = ((i + 3 * r - 1) % k + 1) % k := by
      rw [Nat.mod_add_mod]
      congr 1; omega
    rw [decide_eq_true heq] at hrot
    have hcancel : ∀ a b cc : Bool, xor (xor a cc) (xor b cc) = xor a b := by
      intro a b cc; cases a <;> cases b <;> cases cc <;> rfl
    rw [Nat.testBit_xor, Nat.testBit_xor, hcancel, hrot]
    simp
  | succ t ih =>
    intro ht
    have hstep := endpoint_xor_step k r constants u i w hr hkr hu t (by omega)
    dsimp only at hstep
    rw [decide_eq_false (by omega), Bool.xor_false] at hstep
    rw [hstep, Bool.and_eq_true, Bool.not_eq_true', ih (by omega)]
    constructor
    · rintro ⟨hp, hall⟩ s hs
      by_cases hst : s < t
      · exact hall s hst
      · have hseq : s = t := by omega
        subst hseq
        exact hp
    · intro hall
      exact ⟨hall t (by omega), fun s hs => hall s (by omega)⟩

end PEqualNP.Outside.L_meta_25505_aux

open PEqualNP.Outside.L_meta_25505_aux in
theorem PEqualNP.Outside.L_meta_25505 : (∀ (k r : ℕ) (constants : ℕ → Fin (2 ^ k)) (u i : ℕ),
  4 ≤ r → k + 3 = 5 * r → u < 2 ^ k → i < k →
  let rot := fun (s word : ℕ) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : ℕ) =>
    (List.range k).foldl (fun acc b =>
      acc ||| ((xor (word.testBit b)
        (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0
  let state := fun (key rounds : ℕ) =>
    (List.range rounds).foldl (fun prev t =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * t) key ^^^
        (constants (t + 1)).val) (rot 1 key ^^^ u)
  let flip := fun w : ℕ => w ^^^ (1 <<< ((i + 3 * r - 1) % k))
  ∀ w : Fin (2 ^ k),
    ((state w.val r).testBit i = (state (flip w.val) r).testBit i) ↔
      ∀ s : Fin r,
        let z := state w.val s.val
        let b := i + 3 * (r - (s.val + 1))
        xor (xor (z.testBit (b % k)) (z.testBit ((b + 1) % k)))
          (z.testBit ((b + 2) % k)) = false) := by
  intro k r constants u i hr hkr hu hik rotF stepF stateF flipF w
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hstep := endpoint_xor_step k (m + 1) constants u i w hr hkr hu m (by omega)
  dsimp only at hstep
  have hmod_i : (i + 3 * (m + 1 - (m + 1))) % k = i := by
    simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
    exact Nat.mod_eq_of_lt hik
  rw [hmod_i, decide_eq_true rfl] at hstep
  have hpref := endpoint_diff_prefix k (m + 1) constants u i w hr hkr hu m (by omega)
  change ((stateAux k constants u w.val (m + 1)).testBit i =
          (stateAux k constants u (flipF w.val) (m + 1)).testBit i) ↔ _
  rw [← xor_eq_false_iff, hstep]
  have hxt : ∀ a : Bool, xor a true = false ↔ a = true := by intro a; cases a <;> decide
  rw [hxt, Bool.and_eq_true, Bool.not_eq_true', hpref]
  constructor
  · rintro ⟨hp, hall⟩ s
    by_cases hsm : s.val < m
    · exact hall s.val hsm
    · have hseq : s.val = m := by omega
      change xor (xor ((stateAux k constants u w.val s.val).testBit ((i + 3 * (m + 1 - (s.val + 1))) % k))
                      ((stateAux k constants u w.val s.val).testBit ((i + 3 * (m + 1 - (s.val + 1)) + 1) % k)))
                 ((stateAux k constants u w.val s.val).testBit ((i + 3 * (m + 1 - (s.val + 1)) + 2) % k)) = false
      rw [hseq, hmod_i]
      exact hp
  · intro hall
    refine ⟨?_, fun s hs => hall ⟨s, by omega⟩⟩
    have hm := hall ⟨m, by omega⟩
    change xor (xor ((stateAux k constants u w.val m).testBit ((i + 3 * (m + 1 - (m + 1))) % k))
                    ((stateAux k constants u w.val m).testBit ((i + 3 * (m + 1 - (m + 1)) + 1) % k)))
               ((stateAux k constants u w.val m).testBit ((i + 3 * (m + 1 - (m + 1)) + 2) % k)) = false at hm
    rwa [hmod_i] at hm
