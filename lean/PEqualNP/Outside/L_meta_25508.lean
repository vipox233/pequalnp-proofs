import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25508_aux

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

def guardAt (k r : Nat) (constants : Nat → Fin (2 ^ k)) (u i key s : Nat) : Bool :=
  let z := stateAux k constants u key s
  let b := i + 3 * (r - (s + 1))
  xor (xor (z.testBit (b % k)) (z.testBit ((b + 1) % k))) (z.testBit ((b + 2) % k))

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

lemma nat_eq_of_testBit_lt (k a b : Nat) (ha : a < 2 ^ k) (hb : b < 2 ^ k)
    (h : ∀ j < k, a.testBit j = b.testBit j) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < k
  · exact h j hj
  · have ha' : a < 2 ^ j := Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega))
    have hb' : b < 2 ^ j := Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow ha', Nat.testBit_lt_two_pow hb']

lemma cancel_mod_add (k x y z : Nat) (hk : 0 < k) (hxy : (x + z) % k = (y + z) % k) :
    x % k = y % k := by
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

lemma rot_comp_inv (k s x : Nat) (hk : 0 < k) (hx : x < 2 ^ k) :
    rot k s (rot k (k - s % k) x) = x := by
  apply nat_eq_of_testBit_lt k _ _ (rot_lt k s _) hx
  intro j hj
  have hs : s % k < k := Nat.mod_lt s hk
  rw [testBit_rot k s _ j (rot_lt k _ x) hj,
      testBit_rot k (k - s % k) x _ hx (Nat.mod_lt _ hk)]
  congr 1
  by_cases hs0 : s % k = 0
  · simp [hs0, Nat.mod_eq_of_lt hj]
  · have hks : (k - s % k) % k = k - s % k := Nat.mod_eq_of_lt (by omega)
    rw [hks]
    have h1 : (j + k - s % k) % k + k - (k - s % k) = (j + k - s % k) % k + s % k := by omega
    rw [h1, Nat.mod_add_mod]
    have h2 : j + k - s % k + s % k = j + k := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hj]

lemma rot_inv_comp (k s x : Nat) (hk : 0 < k) (hx : x < 2 ^ k) :
    rot k (k - s % k) (rot k s x) = x := by
  have hs : s % k < k := Nat.mod_lt s hk
  by_cases hs0 : s % k = 0
  · apply nat_eq_of_testBit_lt k _ _ (rot_lt k _ _) hx
    intro j hj
    rw [testBit_rot k _ _ j (rot_lt k _ x) hj, testBit_rot k s x _ hx (Nat.mod_lt _ hk)]
    simp [hs0, Nat.mod_eq_of_lt hj]
  · have hks : (k - s % k) % k = k - s % k := Nat.mod_eq_of_lt (by omega)
    have hback : k - (k - s % k) % k = s % k := by rw [hks]; omega
    have hrot_eq : rot k s x = rot k (k - (k - s % k) % k) x := by
      unfold rot; rw [hback, Nat.mod_eq_of_lt hs]
    rw [hrot_eq]
    exact rot_comp_inv k (k - s % k) x hk hx

lemma rot_1_inv (k x : Nat) (hk : 2 ≤ k) (hx : x < 2 ^ k) :
    rot k 1 (rot k (k - 1) x) = x := by
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have := rot_comp_inv k 1 x (by omega) hx
  rwa [h1] at this

lemma rot_inv_1 (k x : Nat) (hk : 2 ≤ k) (hx : x < 2 ^ k) :
    rot k (k - 1) (rot k 1 x) = x := by
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have := rot_inv_comp k 1 x (by omega) hx
  rwa [h1] at this

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
      have h5 := cancel_mod_add k _ _ (s % k) hk h2
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

lemma step_left_lin_xor (k prev1 prev2 base x : Nat) (hk : 2 ≤ k)
    (hp1 : prev1 < 2 ^ k) (hp2 : prev2 < 2 ^ k) (hx : 1 ≤ x)
    (h0 : prev1.testBit ((base + x) % k) = prev2.testBit ((base + x) % k))
    (h1 : prev1.testBit ((base + (x + 1)) % k) = prev2.testBit ((base + (x + 1)) % k))
    (h2 : prev1.testBit ((base + (x + 2)) % k) = prev2.testBit ((base + (x + 2)) % k))
    (h3 : prev1.testBit ((base + (x + 3)) % k) = prev2.testBit ((base + (x + 3)) % k)) :
    let l1 := prev1 ^^^ rot k 1 prev1 ^^^ rot k (k - 1) prev1
    let l2 := prev2 ^^^ rot k 1 prev2 ^^^ rot k (k - 1) prev2
    xor ((step k l1).testBit ((base + x) % k)) ((step k l2).testBit ((base + x) % k)) =
      xor (prev1.testBit ((base + (x - 1)) % k)) (prev2.testBit ((base + (x - 1)) % k)) := by
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
  rw [ha1, ha2, hb2, hb3, h0, h1, h2, h3]
  cases prev1.testBit ((base + (x - 1)) % k) <;>
  cases prev2.testBit ((base + (x - 1)) % k) <;>
  cases prev2.testBit ((base + x) % k) <;>
  cases prev2.testBit ((base + (x + 1)) % k) <;>
  cases prev2.testBit ((base + (x + 2)) % k) <;>
  cases prev2.testBit ((base + (x + 3)) % k) <;> rfl

lemma xor_eq_false_iff (a b : Bool) : xor a b = false ↔ a = b := by
  cases a <;> cases b <;> decide

lemma mod_ne_of_lt (k base x y : Nat) (hx : x < k) (hy : y < k) (hne : x ≠ y) :
    (base + x) % k ≠ (base + y) % k := by
  intro heq
  have hk : 0 < k := by omega
  have h1 : (x + base) % k = (y + base) % k := by
    rw [Nat.add_comm x base, Nat.add_comm y base]; exact heq
  have h2 := cancel_mod_add k x y base hk h1
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h2
  exact hne h2

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
    xor ((stateAux k constants u w.val (t + 1)).testBit ((i + 3 * (r - (t + 1))) % k))
        ((stateAux k constants u flip (t + 1)).testBit ((i + 3 * (r - (t + 1))) % k)) =
      xor (!(guardAt k r constants u i w.val t) &&
           xor ((stateAux k constants u w.val t).testBit ((i + 3 * (r - t)) % k))
               ((stateAux k constants u flip t).testBit ((i + 3 * (r - t)) % k)))
          (decide (t + 1 = r)) := by
  intro flip
  let b := i + 3 * (r - (t + 1))
  have hpos_b : ∀ d : Nat, (i + k - r + (4 * r - 3 * (t + 1) + d)) % k = (b + d) % k := by
    intro d
    have h1 : i + k - r + (4 * r - 3 * (t + 1) + d) = (b + d) + k := by omega
    rw [h1, Nat.add_mod_right]
  have hpos0 : (i + k - r + (4 * r - 3 * (t + 1))) % k = b % k := by
    simpa using hpos_b 0
  have hpos3 : (i + k - r + (4 * r - 3 * (t + 1) + 3)) % k = (i + 3 * (r - t)) % k := by
    have h1 : i + k - r + (4 * r - 3 * (t + 1) + 3) = (i + 3 * (r - t)) + k := by omega
    rw [h1, Nat.add_mod_right]
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
  rfl

lemma endpoint_diff_prefix (k r : Nat) (constants : Nat → Fin (2 ^ k)) (u i : Nat)
    (w : Fin (2 ^ k)) (hr : 4 ≤ r) (hkr : k + 3 = 5 * r) (hu : u < 2 ^ k) :
    let flip := w.val ^^^ (1 <<< ((i + 3 * r - 1) % k))
    ∀ m : Nat, m < r →
      ((xor ((stateAux k constants u w.val m).testBit ((i + 3 * (r - m)) % k))
            ((stateAux k constants u flip m).testBit ((i + 3 * (r - m)) % k)) = true) ↔
       (∀ s : Nat, s < m → guardAt k r constants u i w.val s = false)) := by
  intro flip m
  induction m with
  | zero =>
    intro _
    rw [stateAux_zero, stateAux_zero]
    have ha : (i + 3 * r - 1) % k < k := Nat.mod_lt _ (by omega)
    have hq : (i + 3 * (r - 0)) % k < k := Nat.mod_lt _ (by omega)
    have hrot := testBit_rot_flip_xor k 1 w.val ((i + 3 * r - 1) % k) ((i + 3 * (r - 0)) % k) w.isLt ha hq
    have heq : (i + 3 * (r - 0)) % k = ((i + 3 * r - 1) % k + 1) % k := by
      rw [Nat.mod_add_mod]; congr 1; omega
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
        subst hseq; exact hp
    · intro hall
      exact ⟨hall t (by omega), fun s hs => hall s (by omega)⟩

lemma flip_iff_all_guards (k r : Nat) (constants : Nat → Fin (2 ^ k)) (u i : Nat)
    (hr : 4 ≤ r) (hkr : k + 3 = 5 * r) (hu : u < 2 ^ k) (hik : i < k) (w : Fin (2 ^ k)) :
    let flip := w.val ^^^ (1 <<< ((i + 3 * r - 1) % k))
    ((stateAux k constants u w.val r).testBit i = (stateAux k constants u flip r).testBit i) ↔
      (∀ s < r, guardAt k r constants u i w.val s = false) := by
  intro flip
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hstep := endpoint_xor_step k (m + 1) constants u i w hr hkr hu m (by omega)
  dsimp only at hstep
  have hmod_i : (i + 3 * (m + 1 - (m + 1))) % k = i := by
    simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
    exact Nat.mod_eq_of_lt hik
  rw [hmod_i, decide_eq_true rfl] at hstep
  have hpref := endpoint_diff_prefix k (m + 1) constants u i w hr hkr hu m (by omega)
  rw [← xor_eq_false_iff, hstep]
  have hxt : ∀ a : Bool, xor a true = false ↔ a = true := by intro a; cases a <;> decide
  rw [hxt, Bool.and_eq_true, Bool.not_eq_true', hpref]
  constructor
  · rintro ⟨hp, hall⟩ s hs
    by_cases hsm : s < m
    · exact hall s hsm
    · have hseq : s = m := by omega
      subst hseq; exact hp
  · intro hall
    exact ⟨hall m (by omega), fun s hs => hall s (by omega)⟩

def keyOfStart (k u st : Nat) : Nat := rot k (k - 1) (st ^^^ u)

lemma keyOfStart_lt (k u st : Nat) : keyOfStart k u st < 2 ^ k := rot_lt k _ _

lemma stateAux_keyOfStart_zero (k : Nat) (constants : Nat → Fin (2 ^ k)) (u st : Nat)
    (hk : 2 ≤ k) (hu : u < 2 ^ k) (hst : st < 2 ^ k) :
    stateAux k constants u (keyOfStart k u st) 0 = st := by
  rw [stateAux_zero, keyOfStart, rot_1_inv k (st ^^^ u) hk (Nat.xor_lt_two_pow hst hu)]
  apply nat_eq_of_testBit_lt k _ _ (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hst hu) hu) hst
  intro j _
  rw [Nat.testBit_xor, Nat.testBit_xor]
  cases st.testBit j <;> cases u.testBit j <;> rfl

lemma key_rot_testBit_from_start (k u st1 st2 j base x : Nat)
    (hk : 2 ≤ k) (hu : u < 2 ^ k) (hs1 : st1 < 2 ^ k) (hs2 : st2 < 2 ^ k) (hge : 2 * j ≤ x + 1) :
    xor ((rot k (2 * j) (keyOfStart k u st1)).testBit ((base + x) % k))
        ((rot k (2 * j) (keyOfStart k u st2)).testBit ((base + x) % k)) =
      xor (st1.testBit ((base + (x + 1 - 2 * j)) % k))
          (st2.testBit ((base + (x + 1 - 2 * j)) % k)) := by
  have hq : (base + x) % k < k := Nat.mod_lt _ (by omega)
  have hlt1 := Nat.xor_lt_two_pow hs1 hu
  have hlt2 := Nat.xor_lt_two_pow hs2 hu
  rw [testBit_rot k (2 * j) _ _ (keyOfStart_lt k u st1) hq,
      testBit_rot k (2 * j) _ _ (keyOfStart_lt k u st2) hq,
      keyOfStart, keyOfStart,
      testBit_rot_k_sub_1 k _ _ hk hlt1 (Nat.mod_lt _ (by omega)),
      testBit_rot_k_sub_1 k _ _ hk hlt2 (Nat.mod_lt _ (by omega)),
      Nat.testBit_xor, Nat.testBit_xor]
  have hidx : (((base + x) % k + k - (2 * j) % k) % k + 1) % k = (base + (x + 1 - 2 * j)) % k := by
    rw [Nat.mod_add_mod]
    have ha := Nat.div_add_mod (base + x) k
    have hb := Nat.div_add_mod (2 * j) k
    have hm1 : (base + x) % k < k := Nat.mod_lt _ (by omega)
    have hm2 : (2 * j) % k < k := Nat.mod_lt _ (by omega)
    have hsum : (((base + x) % k + k - (2 * j) % k + 1) + (2 * j) % k) + k * ((base + x) / k) =
        ((base + (x + 1 - 2 * j)) + (2 * j) % k) + k * ((2 * j) / k + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    have hmod := congrArg (· % k) hsum
    simp only [Nat.add_mul_mod_self_left] at hmod
    exact cancel_mod_add k _ _ ((2 * j) % k) (by omega) hmod
  rw [hidx]
  cases st1.testBit ((base + (x + 1 - 2 * j)) % k) <;>
  cases st2.testBit ((base + (x + 1 - 2 * j)) % k) <;>
  cases u.testBit ((base + (x + 1 - 2 * j)) % k) <;> rfl

lemma state_agree_start_window (k : Nat) (constants : Nat → Fin (2 ^ k)) (u base : Nat)
    (st1 st2 : Nat) (lo hi : Nat) (hk : 2 ≤ k) (hu : u < 2 ^ k)
    (hs1 : st1 < 2 ^ k) (hs2 : st2 < 2 ^ k)
    (hwin : ∀ x, lo ≤ x → x ≤ hi → st1.testBit ((base + x) % k) = st2.testBit ((base + x) % k)) :
    ∀ t x, lo + max t (2 * t - 3) ≤ x → x + 3 * t ≤ hi →
      (stateAux k constants u (keyOfStart k u st1) t).testBit ((base + x) % k) =
      (stateAux k constants u (keyOfStart k u st2) t).testBit ((base + x) % k) := by
  intro t
  induction t with
  | zero =>
    intro x hx1 hx2
    rw [stateAux_keyOfStart_zero k constants u st1 hk hu hs1,
        stateAux_keyOfStart_zero k constants u st2 hk hu hs2]
    exact hwin x (by omega) (by omega)
  | succ m ih =>
    intro x hx1 hx2
    have h1 := ih (x - 1) (by omega) (by omega)
    have h2 := ih x (by omega) (by omega)
    have h3 := ih (x + 1) (by omega) (by omega)
    have h4 := ih (x + 2) (by omega) (by omega)
    have h5 := ih (x + 3) (by omega) (by omega)
    have hst := step_left_lin_xor k
      (stateAux k constants u (keyOfStart k u st1) m)
      (stateAux k constants u (keyOfStart k u st2) m)
      base x hk (stateAux_lt k constants u _ m hu) (stateAux_lt k constants u _ m hu) (by omega)
      h2 h3 h4 h5
    rw [h1, Bool.xor_self] at hst
    have hst_eq := (xor_eq_false_iff _ _).mp hst
    have hky := key_rot_testBit_from_start k u st1 st2 m base x hk hu hs1 hs2 (by omega)
    have hkw := hwin (x + 1 - 2 * m) (by omega) (by omega)
    rw [hkw, Bool.xor_self] at hky
    have hky_eq := (xor_eq_false_iff _ _).mp hky
    rw [stateAux_succ, stateAux_succ, Nat.testBit_xor, Nat.testBit_xor,
        Nat.testBit_xor, Nat.testBit_xor, hst_eq, hky_eq]

lemma state3_cancel_15 (k : Nat) (constants : Nat → Fin (2 ^ k)) (u base st1 st2 : Nat)
    (hk : 17 ≤ k) (hu : u < 2 ^ k) (hs1 : st1 < 2 ^ k) (hs2 : st2 < 2 ^ k)
    (h14 : ∀ x, k - 14 ≤ x → x ≤ k - 1 → st1.testBit ((base + x) % k) = st2.testBit ((base + x) % k)) :
    (stateAux k constants u (keyOfStart k u st1) 3).testBit ((base + (k - 12)) % k) =
    (stateAux k constants u (keyOfStart k u st2) 3).testBit ((base + (k - 12)) % k) := by
  have hk2 : 2 ≤ k := by omega
  have hre : ∀ s1 s2 k1 k2 cc : Bool,
      xor (xor (xor s1 k1) cc) (xor (xor s2 k2) cc) = xor (xor s1 s2) (xor k1 k2) := by
    intro s1 s2 k1 k2 cc; cases s1 <;> cases s2 <;> cases k1 <;> cases k2 <;> cases cc <;> rfl

  have hd1 : xor ((stateAux k constants u (keyOfStart k u st1) 1).testBit ((base + (k - 14)) % k))
                 ((stateAux k constants u (keyOfStart k u st2) 1).testBit ((base + (k - 14)) % k)) =
             xor (st1.testBit ((base + (k - 15)) % k)) (st2.testBit ((base + (k - 15)) % k)) := by
    have a0 := state_agree_start_window k constants u base st1 st2 (k - 14) (k - 1) hk2 hu hs1 hs2 h14 0 (k - 14) (by omega) (by omega)
    have a1 := state_agree_start_window k constants u base st1 st2 (k - 14) (k - 1) hk2 hu hs1 hs2 h14 0 (k - 13) (by omega) (by omega)
    have a2 := state_agree_start_window k constants u base st1 st2 (k - 14) (k - 1) hk2 hu hs1 hs2 h14 0 (k - 12) (by omega) (by omega)
    have a3 := state_agree_start_window k constants u base st1 st2 (k - 14) (k - 1) hk2 hu hs1 hs2 h14 0 (k - 11) (by omega) (by omega)
    have hst := step_left_lin_xor k (stateAux k constants u (keyOfStart k u st1) 0)
      (stateAux k constants u (keyOfStart k u st2) 0) base (k - 14) hk2
      (stateAux_lt k constants u _ 0 hu) (stateAux_lt k constants u _ 0 hu) (by omega)
      a0 (by simpa [show k - 14 + 1 = k - 13 by omega] using a1)
      (by simpa [show k - 14 + 2 = k - 12 by omega] using a2)
      (by simpa [show k - 14 + 3 = k - 11 by omega] using a3)
    have hky := key_rot_testBit_from_start k u st1 st2 0 base (k - 14) hk2 hu hs1 hs2 (by omega)
    have hk0 := h14 (k - 13) (by omega) (by omega)
    rw [show k - 14 + 1 - 2 * 0 = k - 13 by omega, hk0, Bool.xor_self] at hky
    rw [stateAux_succ, stateAux_succ, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor,
        hre, hst, hky, Bool.xor_false,
        stateAux_keyOfStart_zero k constants u st1 hk2 hu hs1,
        stateAux_keyOfStart_zero k constants u st2 hk2 hu hs2,
        show k - 14 - 1 = k - 15 by omega]

  have hd2 : xor ((stateAux k constants u (keyOfStart k u st1) 2).testBit ((base + (k - 13)) % k))
                 ((stateAux k constants u (keyOfStart k u st2) 2).testBit ((base + (k - 13)) % k)) =
             xor (st1.testBit ((base + (k - 15)) % k)) (st2.testBit ((base + (k - 15)) % k)) := by
    have a0 := state_agree_start_window k constants u base st1 st2 (k - 14) (k - 1) hk2 hu hs1 hs2 h14 1 (k - 13) (by omega) (by omega)
    have a1 := state_agree_start_window k constants u base st1 st2 (k - 14) (k - 1) hk2 hu hs1 hs2 h14 1 (k - 12) (by omega) (by omega)
    have a2 := state_agree_start_window k constants u base st1 st2 (k - 14) (k - 1) hk2 hu hs1 hs2 h14 1 (k - 11) (by omega) (by omega)
    have a3 := state_agree_start_window k constants u base st1 st2 (k - 14) (k - 1) hk2 hu hs1 hs2 h14 1 (k - 10) (by omega) (by omega)
    have hst := step_left_lin_xor k (stateAux k constants u (keyOfStart k u st1) 1)
      (stateAux k constants u (keyOfStart k u st2) 1) base (k - 13) hk2
      (stateAux_lt k constants u _ 1 hu) (stateAux_lt k constants u _ 1 hu) (by omega)
      a0 (by simpa [show k - 13 + 1 = k - 12 by omega] using a1)
      (by simpa [show k - 13 + 2 = k - 11 by omega] using a2)
      (by simpa [show k - 13 + 3 = k - 10 by omega] using a3)
    have hky := key_rot_testBit_from_start k u st1 st2 1 base (k - 13) hk2 hu hs1 hs2 (by omega)
    have hk1 := h14 (k - 14) (by omega) (by omega)
    rw [show k - 13 + 1 - 2 * 1 = k - 14 by omega, hk1, Bool.xor_self] at hky
    rw [stateAux_succ k constants u (keyOfStart k u st1) 1,
        stateAux_succ k constants u (keyOfStart k u st2) 1,
        Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor,
        hre, hst, hky, Bool.xor_false, show k - 13 - 1 = k - 14 by omega, hd1]

  have a0 := state_agree_start_window k constants u base st1 st2 (k - 14) (k - 1) hk2 hu hs1 hs2 h14 2 (k - 12) (by omega) (by omega)
  have a1 := state_agree_start_window k constants u base st1 st2 (k - 14) (k - 1) hk2 hu hs1 hs2 h14 2 (k - 11) (by omega) (by omega)
  have a2 := state_agree_start_window k constants u base st1 st2 (k - 14) (k - 1) hk2 hu hs1 hs2 h14 2 (k - 10) (by omega) (by omega)
  have a3 := state_agree_start_window k constants u base st1 st2 (k - 14) (k - 1) hk2 hu hs1 hs2 h14 2 (k - 9) (by omega) (by omega)
  have hst := step_left_lin_xor k (stateAux k constants u (keyOfStart k u st1) 2)
    (stateAux k constants u (keyOfStart k u st2) 2) base (k - 12) hk2
    (stateAux_lt k constants u _ 2 hu) (stateAux_lt k constants u _ 2 hu) (by omega)
    a0 (by simpa [show k - 12 + 1 = k - 11 by omega] using a1)
    (by simpa [show k - 12 + 2 = k - 10 by omega] using a2)
    (by simpa [show k - 12 + 3 = k - 9 by omega] using a3)
  have hky := key_rot_testBit_from_start k u st1 st2 2 base (k - 12) hk2 hu hs1 hs2 (by omega)
  have hxor3 : xor ((stateAux k constants u (keyOfStart k u st1) 3).testBit ((base + (k - 12)) % k))
                   ((stateAux k constants u (keyOfStart k u st2) 3).testBit ((base + (k - 12)) % k)) = false := by
    rw [stateAux_succ k constants u (keyOfStart k u st1) 2,
        stateAux_succ k constants u (keyOfStart k u st2) 2,
        Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor,
        hre, hst, hky, show k - 12 - 1 = k - 13 by omega, show k - 12 + 1 - 2 * 2 = k - 15 by omega,
        hd2, Bool.xor_self]
  exact (xor_eq_false_iff _ _).mp hxor3

lemma guards_lt4_congr (k r : Nat) (constants : Nat → Fin (2 ^ k)) (u i st1 st2 : Nat)
    (hr : 4 ≤ r) (hkr : k + 3 = 5 * r) (hu : u < 2 ^ k) (hs1 : st1 < 2 ^ k) (hs2 : st2 < 2 ^ k)
    (h14 : ∀ x, k - 14 ≤ x → x ≤ k - 1 →
      st1.testBit ((i + 3 * r + x) % k) = st2.testBit ((i + 3 * r + x) % k)) :
    ∀ s < 4, guardAt k r constants u i (keyOfStart k u st1) s =
             guardAt k r constants u i (keyOfStart k u st2) s := by
  intro s hs
  unfold guardAt
  dsimp only
  have hconv : ∀ d : Nat, d < k → (i + 3 * (r - (s + 1)) + d) % k =
      (i + 3 * r + (k - 3 * (s + 1) + d)) % k := by
    intro d hd
    have h1 : i + 3 * r + (k - 3 * (s + 1) + d) = (i + 3 * (r - (s + 1)) + d) + k := by omega
    rw [h1, Nat.add_mod_right]
  have hk2 : 2 ≤ k := by omega
  have h0 : (i + 3 * (r - (s + 1))) % k = (i + 3 * r + (k - 3 * (s + 1))) % k := by
    simpa using hconv 0 (by omega)
  have h1 := hconv 1 (by omega)
  have h2 := hconv 2 (by omega)
  rw [h0, h1, h2]
  have hst1 : (stateAux k constants u (keyOfStart k u st1) s).testBit ((i + 3 * r + (k - 3 * (s + 1) + 1)) % k) =
              (stateAux k constants u (keyOfStart k u st2) s).testBit ((i + 3 * r + (k - 3 * (s + 1) + 1)) % k) :=
    state_agree_start_window k constants u (i + 3 * r) st1 st2 (k - 14) (k - 1) hk2 hu hs1 hs2 h14 s _ (by omega) (by omega)
  have hst2 : (stateAux k constants u (keyOfStart k u st1) s).testBit ((i + 3 * r + (k - 3 * (s + 1) + 2)) % k) =
              (stateAux k constants u (keyOfStart k u st2) s).testBit ((i + 3 * r + (k - 3 * (s + 1) + 2)) % k) :=
    state_agree_start_window k constants u (i + 3 * r) st1 st2 (k - 14) (k - 1) hk2 hu hs1 hs2 h14 s _ (by omega) (by omega)
  have hst0 : (stateAux k constants u (keyOfStart k u st1) s).testBit ((i + 3 * r + (k - 3 * (s + 1))) % k) =
              (stateAux k constants u (keyOfStart k u st2) s).testBit ((i + 3 * r + (k - 3 * (s + 1))) % k) := by
    by_cases hs3 : s = 3
    · subst hs3
      exact state3_cancel_15 k constants u (i + 3 * r) st1 st2 (by omega) hu hs1 hs2 h14
    · exact state_agree_start_window k constants u (i + 3 * r) st1 st2 (k - 14) (k - 1) hk2 hu hs1 hs2 h14 s _ (by omega) (by omega)
  rw [hst0, hst1, hst2]

lemma pivot_toggle_props (k r : Nat) (constants : Nat → Fin (2 ^ k)) (u i st m : Nat)
    (hr : 4 ≤ r) (hkr : k + 3 = 5 * r) (hu : u < 2 ^ k) (hst : st < 2 ^ k)
    (hm4 : 4 ≤ m) (hmr : m < r) :
    let piv := (i + 3 * r + (k - 5 * m)) % k
    let st' := st ^^^ (1 <<< piv)
    (∀ s < m, guardAt k r constants u i (keyOfStart k u st') s =
              guardAt k r constants u i (keyOfStart k u st) s) ∧
    guardAt k r constants u i (keyOfStart k u st') m =
      !(guardAt k r constants u i (keyOfStart k u st) m) := by
  intro piv st'
  have hk2 : 2 ≤ k := by omega
  have hpiv_lt : piv < k := Nat.mod_lt _ (by omega)
  have hst'_lt : st' < 2 ^ k := flip_lt k st piv hst hpiv_lt
  have hwin_big : ∀ x, k - 5 * m + 1 ≤ x → x ≤ k - 1 →
      st.testBit ((i + 3 * r + x) % k) = st'.testBit ((i + 3 * r + x) % k) := by
    intro x hx1 hx2
    have hne : (i + 3 * r + x) % k ≠ piv :=
      mod_ne_of_lt k (i + 3 * r) x (k - 5 * m) (by omega) (by omega) (by omega)
    dsimp only [st']
    rw [Nat.testBit_xor, testBit_one_shiftLeft, decide_eq_false hne, Bool.xor_false]
  constructor
  · intro s hsm
    by_cases hs4 : s < 4
    · exact (guards_lt4_congr k r constants u i st st' hr hkr hu hst hst'_lt
        (fun x hx1 hx2 => hwin_big x (by omega) hx2) s hs4).symm
    · unfold guardAt
      dsimp only
      have hconv : ∀ d : Nat, d < k → (i + 3 * (r - (s + 1)) + d) % k =
          (i + 3 * r + (k - 3 * (s + 1) + d)) % k := by
        intro d hd
        have h1 : i + 3 * r + (k - 3 * (s + 1) + d) = (i + 3 * (r - (s + 1)) + d) + k := by omega
        rw [h1, Nat.add_mod_right]
      have h0 : (i + 3 * (r - (s + 1))) % k = (i + 3 * r + (k - 3 * (s + 1))) % k := by
        simpa using hconv 0 (by omega)
      rw [h0, hconv 1 (by omega), hconv 2 (by omega)]
      have a0 := state_agree_start_window k constants u (i + 3 * r) st st' (k - 5 * m + 1) (k - 1) hk2 hu hst hst'_lt hwin_big s (k - 3 * (s + 1)) (by omega) (by omega)
      have a1 := state_agree_start_window k constants u (i + 3 * r) st st' (k - 5 * m + 1) (k - 1) hk2 hu hst hst'_lt hwin_big s (k - 3 * (s + 1) + 1) (by omega) (by omega)
      have a2 := state_agree_start_window k constants u (i + 3 * r) st st' (k - 5 * m + 1) (k - 1) hk2 hu hst hst'_lt hwin_big s (k - 3 * (s + 1) + 2) (by omega) (by omega)
      rw [a0, a1, a2]
  · unfold guardAt
    dsimp only
    have hconv : ∀ d : Nat, d < k → (i + 3 * (r - (m + 1)) + d) % k =
        (i + 3 * r + (k - 3 * (m + 1) + d)) % k := by
      intro d hd
      have h1 : i + 3 * r + (k - 3 * (m + 1) + d) = (i + 3 * (r - (m + 1)) + d) + k := by omega
      rw [h1, Nat.add_mod_right]
    have h0 : (i + 3 * (r - (m + 1))) % k = (i + 3 * r + (k - 3 * (m + 1))) % k := by
      simpa using hconv 0 (by omega)
    rw [h0, hconv 1 (by omega), hconv 2 (by omega)]
    have a1 := state_agree_start_window k constants u (i + 3 * r) st st' (k - 5 * m + 1) (k - 1) hk2 hu hst hst'_lt hwin_big m (k - 3 * (m + 1) + 1) (by omega) (by omega)
    have a2 := state_agree_start_window k constants u (i + 3 * r) st st' (k - 5 * m + 1) (k - 1) hk2 hu hst hst'_lt hwin_big m (k - 3 * (m + 1) + 2) (by omega) (by omega)

    obtain ⟨m0, rfl⟩ : ∃ m0, m = m0 + 1 := ⟨m - 1, by omega⟩
    have b_m1 := state_agree_start_window k constants u (i + 3 * r) st st' (k - 5 * (m0 + 1) + 1) (k - 1) hk2 hu hst hst'_lt hwin_big m0 (k - 3 * (m0 + 1 + 1) - 1) (by omega) (by omega)
    have b0 := state_agree_start_window k constants u (i + 3 * r) st st' (k - 5 * (m0 + 1) + 1) (k - 1) hk2 hu hst hst'_lt hwin_big m0 (k - 3 * (m0 + 1 + 1)) (by omega) (by omega)
    have b1 := state_agree_start_window k constants u (i + 3 * r) st st' (k - 5 * (m0 + 1) + 1) (k - 1) hk2 hu hst hst'_lt hwin_big m0 (k - 3 * (m0 + 1 + 1) + 1) (by omega) (by omega)
    have b2 := state_agree_start_window k constants u (i + 3 * r) st st' (k - 5 * (m0 + 1) + 1) (k - 1) hk2 hu hst hst'_lt hwin_big m0 (k - 3 * (m0 + 1 + 1) + 2) (by omega) (by omega)
    have b3 := state_agree_start_window k constants u (i + 3 * r) st st' (k - 5 * (m0 + 1) + 1) (k - 1) hk2 hu hst hst'_lt hwin_big m0 (k - 3 * (m0 + 1 + 1) + 3) (by omega) (by omega)
    have hstep_eq : xor ((step k (stateAux k constants u (keyOfStart k u st) m0 ^^^
                                   rot k 1 (stateAux k constants u (keyOfStart k u st) m0) ^^^
                                   rot k (k - 1) (stateAux k constants u (keyOfStart k u st) m0))).testBit
                          ((i + 3 * r + (k - 3 * (m0 + 1 + 1))) % k))
                        ((step k (stateAux k constants u (keyOfStart k u st') m0 ^^^
                                   rot k 1 (stateAux k constants u (keyOfStart k u st') m0) ^^^
                                   rot k (k - 1) (stateAux k constants u (keyOfStart k u st') m0))).testBit
                          ((i + 3 * r + (k - 3 * (m0 + 1 + 1))) % k)) = false := by
      have hst := step_left_lin_xor k (stateAux k constants u (keyOfStart k u st) m0)
        (stateAux k constants u (keyOfStart k u st') m0) (i + 3 * r) (k - 3 * (m0 + 1 + 1)) hk2
        (stateAux_lt k constants u _ m0 hu) (stateAux_lt k constants u _ m0 hu) (by omega)
        b0 b1 b2 b3
      rw [b_m1, Bool.xor_self] at hst
      exact hst
    have hky := key_rot_testBit_from_start k u st st' m0 (i + 3 * r) (k - 3 * (m0 + 1 + 1)) hk2 hu hst hst'_lt (by omega)
    have hpiv_idx : k - 3 * (m0 + 1 + 1) + 1 - 2 * m0 = k - 5 * (m0 + 1) := by omega
    rw [hpiv_idx] at hky
    have hst_flip : xor (st.testBit piv) (st'.testBit piv) = true := by
      dsimp only [st']
      rw [Nat.testBit_xor, testBit_one_shiftLeft, decide_eq_true rfl]
      cases st.testBit piv <;> rfl
    change xor ((rot k (2 * m0) (keyOfStart k u st)).testBit ((i + 3 * r + (k - 3 * (m0 + 1 + 1))) % k))
               ((rot k (2 * m0) (keyOfStart k u st')).testBit ((i + 3 * r + (k - 3 * (m0 + 1 + 1))) % k)) =
           xor (st.testBit piv) (st'.testBit piv) at hky
    rw [hst_flip] at hky
    have hre : ∀ s1 s2 k1 k2 cc : Bool,
        xor (xor (xor s1 k1) cc) (xor (xor s2 k2) cc) = xor (xor s1 s2) (xor k1 k2) := by
      intro s1 s2 k1 k2 cc; cases s1 <;> cases s2 <;> cases k1 <;> cases k2 <;> cases cc <;> rfl
    have hflip0 : (stateAux k constants u (keyOfStart k u st') (m0 + 1)).testBit ((i + 3 * r + (k - 3 * (m0 + 1 + 1))) % k) =
                  !((stateAux k constants u (keyOfStart k u st) (m0 + 1)).testBit ((i + 3 * r + (k - 3 * (m0 + 1 + 1))) % k)) := by
      have hxor : xor ((stateAux k constants u (keyOfStart k u st) (m0 + 1)).testBit ((i + 3 * r + (k - 3 * (m0 + 1 + 1))) % k))
                      ((stateAux k constants u (keyOfStart k u st') (m0 + 1)).testBit ((i + 3 * r + (k - 3 * (m0 + 1 + 1))) % k)) = true := by
        rw [stateAux_succ, stateAux_succ, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor,
            hre, hstep_eq, hky, Bool.false_xor]
      cases hL : (stateAux k constants u (keyOfStart k u st) (m0 + 1)).testBit ((i + 3 * r + (k - 3 * (m0 + 1 + 1))) % k) <;>
      cases hR : (stateAux k constants u (keyOfStart k u st') (m0 + 1)).testBit ((i + 3 * r + (k - 3 * (m0 + 1 + 1))) % k) <;>
      simp [hL, hR] at hxor ⊢
    rw [hflip0, ← a1, ← a2]
    cases (stateAux k constants u (keyOfStart k u st) (m0 + 1)).testBit ((i + 3 * r + (k - 3 * (m0 + 1 + 1))) % k) <;>
    cases (stateAux k constants u (keyOfStart k u st) (m0 + 1)).testBit ((i + 3 * r + (k - 3 * (m0 + 1 + 1) + 1)) % k) <;>
    cases (stateAux k constants u (keyOfStart k u st) (m0 + 1)).testBit ((i + 3 * r + (k - 3 * (m0 + 1 + 1) + 2)) % k) <;> rfl

lemma card_filter_half {α : Type*} [DecidableEq α] (S : Finset α) (f : α → α) (p : α → Bool)
    (hmem : ∀ x ∈ S, f x ∈ S)
    (hinv : ∀ x ∈ S, f (f x) = x)
    (hflip : ∀ x ∈ S, p (f x) = !(p x)) :
    2 * (S.filter (fun x => p x = false)).card = S.card := by
  have hpart : (S.filter (fun x => p x = false)).card + (S.filter (fun x => p x = true)).card = S.card := by
    have hdisj : Disjoint (S.filter (fun x => p x = false)) (S.filter (fun x => p x = true)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_filter] at hx1 hx2
      rw [hx1.2] at hx2; cases hx2.2
    have hunion : S.filter (fun x => p x = false) ∪ S.filter (fun x => p x = true) = S := by
      ext x; simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro hx; cases hp : p x
        · left; exact ⟨hx, rfl⟩
        · right; exact ⟨hx, rfl⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have heq_card : (S.filter (fun x => p x = false)).card = (S.filter (fun x => p x = true)).card := by
    apply Finset.card_bij (fun x _ => f x)
    · intro x hx
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨hmem x hx.1, by rw [hflip x hx.1, hx.2]; rfl⟩
    · intro x hx y hy hxy
      simp only [Finset.mem_filter] at hx hy
      have := congrArg f hxy
      rwa [hinv x hx.1, hinv y hy.1] at this
    · intro y hy
      simp only [Finset.mem_filter] at hy
      refine ⟨f y, ?_, hinv y hy.1⟩
      simp only [Finset.mem_filter]
      exact ⟨hmem y hy.1, by rw [hflip y hy.1, hy.2]; rfl⟩
  omega

lemma card_pass_step (k r : Nat) (constants : Nat → Fin (2 ^ k)) (u i : Nat)
    (hr : 4 ≤ r) (hkr : k + 3 = 5 * r) (hu : u < 2 ^ k) :
    ∀ m, 4 ≤ m → m ≤ r →
      ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun st =>
        (List.range m).all (fun s => !(guardAt k r constants u i (keyOfStart k u st.val) s)))).card *
      2 ^ (m - 4) =
      ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun st =>
        (List.range 4).all (fun s => !(guardAt k r constants u i (keyOfStart k u st.val) s)))).card := by
  intro m hm4
  induction m with
  | zero => omega
  | succ m ih =>
    intro hmr
    by_cases hm4' : m = 3
    · subst hm4'; simp
    · have h4m : 4 ≤ m := by omega
      let S := (Finset.univ : Finset (Fin (2 ^ k))).filter (fun st =>
        (List.range m).all (fun s => !(guardAt k r constants u i (keyOfStart k u st.val) s)))
      let piv := (i + 3 * r + (k - 5 * m)) % k
      have hpiv : piv < k := Nat.mod_lt _ (by omega)
      let f : Fin (2 ^ k) → Fin (2 ^ k) := fun st => ⟨st.val ^^^ (1 <<< piv), flip_lt k st.val piv st.isLt hpiv⟩
      let p : Fin (2 ^ k) → Bool := fun st => guardAt k r constants u i (keyOfStart k u st.val) m
      have hhalf : 2 * (S.filter (fun x => p x = false)).card = S.card := by
        apply card_filter_half S f p
        · intro st hst
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, List.all_eq_true, List.mem_range] at hst ⊢
          intro s hs
          have hpr := (pivot_toggle_props k r constants u i st.val m hr hkr hu st.isLt h4m (by omega)).1 s hs
          rw [hpr]; exact hst s hs
        · intro st _
          ext
          dsimp only [f]
          apply nat_eq_of_testBit_lt k _ _ (flip_lt k _ piv (flip_lt k st.val piv st.isLt hpiv) hpiv) st.isLt
          intro j _
          rw [Nat.testBit_xor, Nat.testBit_xor]
          cases st.val.testBit j <;> cases (1 <<< piv).testBit j <;> rfl
        · intro st _
          exact (pivot_toggle_props k r constants u i st.val m hr hkr hu st.isLt h4m (by omega)).2
      have hfilt : S.filter (fun x => p x = false) =
          (Finset.univ : Finset (Fin (2 ^ k))).filter (fun st =>
            (List.range (m + 1)).all (fun s => !(guardAt k r constants u i (keyOfStart k u st.val) s))) := by
        ext st
        simp only [S, p, Finset.mem_filter, Finset.mem_univ, true_and, List.all_eq_true, List.mem_range,
                   Bool.not_eq_true']
        constructor
        · rintro ⟨hall, hm_f⟩ s hs
          by_cases hsm : s < m
          · exact hall s hsm
          · have : s = m := by omega
            subst this; exact hm_f
        · intro hall
          exact ⟨fun s hs => hall s (by omega), hall m (by omega)⟩
      rw [hfilt] at hhalf
      have hih := ih h4m (by omega)
      have hexp : m + 1 - 4 = (m - 4) + 1 := by omega
      rw [hexp, Nat.pow_succ, Nat.mul_comm (2 ^ (m - 4)) 2, ← Nat.mul_assoc,
          Nat.mul_comm _ 2, hhalf]
      exact hih

lemma pack_w_lt (k w : Nat) (hwk : w ≤ k) (seed : Fin (2 ^ w)) (hi : Fin (2 ^ (k - w))) :
    seed.val + hi.val * 2 ^ w < 2 ^ k := by
  have hpow : 2 ^ w * 2 ^ (k - w) = 2 ^ k := by
    rw [← Nat.pow_add]; congr 1; omega
  have h1 : hi.val + 1 ≤ 2 ^ (k - w) := hi.isLt
  calc seed.val + hi.val * 2 ^ w < 2 ^ w + hi.val * 2 ^ w := Nat.add_lt_add_right seed.isLt _
    _ = (hi.val + 1) * 2 ^ w := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    _ ≤ 2 ^ (k - w) * 2 ^ w := Nat.mul_le_mul_right _ h1
    _ = 2 ^ k := by rw [Nat.mul_comm, hpow]

lemma rot_pack_w_testBit_agree (k r i w : Nat) (hk : w + 3 ≤ k)
    (seed : Fin (2 ^ w)) (hi : Fin (2 ^ (k - w))) (x : Nat)
    (hx1 : k - w ≤ x) (hx2 : x ≤ k - 1) :
    (rot k (i + 3 * r + k - w) (seed.val + hi.val * 2 ^ w)).testBit ((i + 3 * r + x) % k) =
    (rot k (i + 3 * r + k - w) seed.val).testBit ((i + 3 * r + x) % k) := by
  let shift := i + 3 * r + k - w
  have hq : (i + 3 * r + x) % k < k := Nat.mod_lt _ (by omega)
  have hseed_lt : seed.val < 2 ^ k := Nat.lt_of_lt_of_le seed.isLt (Nat.pow_le_pow_right (by omega) (by omega))
  rw [testBit_rot k shift _ _ (pack_w_lt k w (by omega) seed hi) hq, testBit_rot k shift _ _ hseed_lt hq]
  have hidx : ((i + 3 * r + x) % k + k - shift % k) % k = x - (k - w) := by
    have ha := Nat.div_add_mod (i + 3 * r + x) k
    have hb := Nat.div_add_mod shift k
    have hm1 : (i + 3 * r + x) % k < k := Nat.mod_lt _ (by omega)
    have hm2 : shift % k < k := Nat.mod_lt _ (by omega)
    have hshift : shift = i + 3 * r + k - w := rfl
    have hsum : (((i + 3 * r + x) % k + k - shift % k) + shift % k) + k * ((i + 3 * r + x) / k) =
        ((x - (k - w)) + shift % k) + k * (shift / k + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    have hmod := congrArg (· % k) hsum
    simp only [Nat.add_mul_mod_self_left] at hmod
    have hc := cancel_mod_add k _ _ (shift % k) (by omega) hmod
    exact hc.trans (Nat.mod_eq_of_lt (by omega))
  rw [hidx]
  have hltw : x - (k - w) < w := by omega
  have h1 : (seed.val + hi.val * 2 ^ w) % 2 ^ w = seed.val := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt seed.isLt]
  have h2 := congrArg (fun n => n.testBit (x - (k - w))) h1
  rw [Nat.testBit_mod_two_pow, decide_eq_true hltw, Bool.true_and] at h2
  exact h2

lemma card_pass_base4_gen (k r w : Nat) (constants : Nat → Fin (2 ^ k)) (u i : Nat)
    (hr : 4 ≤ r) (hkr : k + 3 = 5 * r) (hu : u < 2 ^ k) (hw : w = 14) :
    let shift := i + 3 * r + k - w
    let prefixOK := fun (seed : Fin (2 ^ w)) =>
      (List.range 4).all (fun s => !(guardAt k r constants u i (keyOfStart k u (rot k shift seed.val)) s))
    ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun st =>
      (List.range 4).all (fun s => !(guardAt k r constants u i (keyOfStart k u st.val) s)))).card =
    ((Finset.univ : Finset (Fin (2 ^ w))).filter (fun seed => prefixOK seed)).card * 2 ^ (k - w) := by
  intro shift prefixOK
  have hkw : w + 3 ≤ k := by omega
  have hpow : 2 ^ w * 2 ^ (k - w) = 2 ^ k := by
    rw [← Nat.pow_add]; congr 1; omega
  let prodSet := ((Finset.univ : Finset (Fin (2 ^ w))).filter (fun seed => prefixOK seed)) ×ˢ
                 (Finset.univ : Finset (Fin (2 ^ (k - w))))
  have hprod_card : prodSet.card =
      ((Finset.univ : Finset (Fin (2 ^ w))).filter (fun seed => prefixOK seed)).card * 2 ^ (k - w) := by
    simp [prodSet, Finset.card_product, Fintype.card_fin]
  rw [← hprod_card]
  symm
  apply Finset.card_bij (fun p _ => ⟨rot k shift (p.1.val + p.2.val * 2 ^ w), rot_lt k shift _⟩)
  · intro p hp
    simp only [prodSet, prefixOK, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true,
               List.all_eq_true, List.mem_range] at hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.all_eq_true, List.mem_range]
    intro s hs
    have hcg := guards_lt4_congr k r constants u i
      (rot k shift (p.1.val + p.2.val * 2 ^ w)) (rot k shift p.1.val)
      hr hkr hu (rot_lt k shift _) (rot_lt k shift _)
      (fun x hx1 hx2 => rot_pack_w_testBit_agree k r i w hkw p.1 p.2 x (by omega) hx2) s hs
    rw [hcg]
    exact hp s hs
  · intro p1 _ p2 _ heq
    have hval : rot k shift (p1.1.val + p1.2.val * 2 ^ w) = rot k shift (p2.1.val + p2.2.val * 2 ^ w) :=
      congrArg Fin.val heq
    have hrot := congrArg (rot k (k - shift % k)) hval
    rw [rot_inv_comp k shift _ (by omega) (pack_w_lt k w (by omega) p1.1 p1.2),
        rot_inv_comp k shift _ (by omega) (pack_w_lt k w (by omega) p2.1 p2.2)] at hrot
    have h1 : p1.1.val = p2.1.val := by
      have hm := congrArg (· % 2 ^ w) hrot
      rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt p1.1.isLt, Nat.mod_eq_of_lt p2.1.isLt] at hm
      exact hm
    have h2 : p1.2.val = p2.2.val := by
      have hd := congrArg (· / 2 ^ w) hrot
      rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos w),
          Nat.add_mul_div_right _ _ (Nat.two_pow_pos w),
          Nat.div_eq_of_lt p1.1.isLt, Nat.div_eq_of_lt p2.1.isLt, Nat.zero_add, Nat.zero_add] at hd
      exact hd
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)
  · intro st hst
    let z := rot k (k - shift % k) st.val
    have hz : z < 2 ^ k := rot_lt k _ _
    let seed : Fin (2 ^ w) := ⟨z % 2 ^ w, Nat.mod_lt z (Nat.two_pow_pos w)⟩
    let hi : Fin (2 ^ (k - w)) := ⟨z / 2 ^ w, by
      exact Nat.div_lt_of_lt_mul (by rw [hpow]; exact hz)⟩
    have hre : seed.val + hi.val * 2 ^ w = z := by
      have := Nat.div_add_mod z (2 ^ w)
      dsimp only [seed, hi]
      rw [Nat.mul_comm]; omega
    have hst_eq : rot k shift (seed.val + hi.val * 2 ^ w) = st.val := by
      rw [hre]; exact rot_comp_inv k shift st.val (by omega) st.isLt
    refine ⟨(seed, hi), ?_, Fin.ext hst_eq⟩
    simp only [prodSet, prefixOK, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true,
               List.all_eq_true, List.mem_range]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.all_eq_true, List.mem_range] at hst
    intro s hs
    have hcg := guards_lt4_congr k r constants u i
      (rot k shift (seed.val + hi.val * 2 ^ w)) (rot k shift seed.val)
      hr hkr hu (rot_lt k shift _) (rot_lt k shift _)
      (fun x hx1 hx2 => rot_pack_w_testBit_agree k r i w hkw seed hi x (by omega) hx2) s hs
    rw [hst_eq] at hcg
    rw [← hcg]
    exact hst s hs

lemma card_pass_base4 (k r : Nat) (constants : Nat → Fin (2 ^ k)) (u i : Nat)
    (hr : 4 ≤ r) (hkr : k + 3 = 5 * r) (hu : u < 2 ^ k) :
    let shift := i + 3 * r + k - 14
    let prefixOK := fun (seed : Fin (2 ^ 14)) =>
      (List.range 4).all (fun s => !(guardAt k r constants u i (keyOfStart k u (rot k shift seed.val)) s))
    ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun st =>
      (List.range 4).all (fun s => !(guardAt k r constants u i (keyOfStart k u st.val) s)))).card =
    ((Finset.univ : Finset (Fin (2 ^ 14))).filter (fun seed => prefixOK seed)).card * 2 ^ (k - 14) :=
  card_pass_base4_gen k r 14 constants u i hr hkr hu rfl

end PEqualNP.Outside.L_meta_25508_aux

open PEqualNP.Outside.L_meta_25508_aux in
theorem PEqualNP.Outside.L_meta_25508 : (∀ (k r : ℕ) (constants : ℕ → Fin (2 ^ k)) (u i : ℕ),
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
  let prefixOK := fun (seed : Fin (2 ^ 14)) =>
    let start := rot (i + 3 * r + k - 14) seed.val
    let key := rot (k - 1) (start ^^^ u)
    (List.range 4).all (fun roundIndex =>
      let stateBefore := state key roundIndex
      let a := i + 3 * (r - (roundIndex + 1))
      !(xor (xor (stateBefore.testBit (a % k)) (stateBefore.testBit ((a + 1) % k)))
        (stateBefore.testBit ((a + 2) % k))))
  ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun keyWord =>
    (state keyWord.val r).testBit i = (state (flip keyWord.val) r).testBit i)).card =
    ((Finset.univ : Finset (Fin (2 ^ 14))).filter (fun shortWord => prefixOK shortWord)).card *
      2 ^ (k - (14 + (r - 4)))) := by
  intro k r constants u i hr hkr hu hik rotF stepF stateF flipF prefixOK
  have hk2 : 2 ≤ k := by omega

  have hkey_to_start :
      ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun keyWord =>
        (stateF keyWord.val r).testBit i = (stateF (flipF keyWord.val) r).testBit i)).card =
      ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun st =>
        (List.range r).all (fun s => !(guardAt k r constants u i (keyOfStart k u st.val) s)))).card := by
    apply Finset.card_bij (fun kw _ => ⟨PEqualNP.Outside.L_meta_25508_aux.rot k 1 kw.val ^^^ u,
      Nat.xor_lt_two_pow (rot_lt k 1 kw.val) hu⟩)
    · intro kw hkw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.all_eq_true, List.mem_range,
                 Bool.not_eq_true'] at hkw ⊢
      have hback : keyOfStart k u (PEqualNP.Outside.L_meta_25508_aux.rot k 1 kw.val ^^^ u) = kw.val := by
        unfold keyOfStart
        have hxu : (PEqualNP.Outside.L_meta_25508_aux.rot k 1 kw.val ^^^ u) ^^^ u =
            PEqualNP.Outside.L_meta_25508_aux.rot k 1 kw.val := by
          apply nat_eq_of_testBit_lt k _ _
            (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (rot_lt k 1 kw.val) hu) hu) (rot_lt k 1 kw.val)
          intro j _
          rw [Nat.testBit_xor, Nat.testBit_xor]
          cases (PEqualNP.Outside.L_meta_25508_aux.rot k 1 kw.val).testBit j <;> cases u.testBit j <;> rfl
        rw [hxu]
        exact rot_inv_1 k kw.val hk2 kw.isLt
      rw [hback]
      exact (flip_iff_all_guards k r constants u i hr hkr hu hik kw).mp hkw
    · intro k1 _ k2 _ heq
      have hval : PEqualNP.Outside.L_meta_25508_aux.rot k 1 k1.val ^^^ u =
          PEqualNP.Outside.L_meta_25508_aux.rot k 1 k2.val ^^^ u := congrArg Fin.val heq
      have h1 : PEqualNP.Outside.L_meta_25508_aux.rot k 1 k1.val =
          PEqualNP.Outside.L_meta_25508_aux.rot k 1 k2.val := by
        apply nat_eq_of_testBit_lt k _ _ (rot_lt k 1 k1.val) (rot_lt k 1 k2.val)
        intro j _
        have hj := congrArg (fun n => n.testBit j) hval
        rw [Nat.testBit_xor, Nat.testBit_xor] at hj
        cases h1b : (PEqualNP.Outside.L_meta_25508_aux.rot k 1 k1.val).testBit j <;>
        cases h2b : (PEqualNP.Outside.L_meta_25508_aux.rot k 1 k2.val).testBit j <;>
        cases hub : u.testBit j <;> simp [h1b, h2b, hub] at hj ⊢
      have h2 := congrArg (PEqualNP.Outside.L_meta_25508_aux.rot k (k - 1)) h1
      rw [rot_inv_1 k k1.val hk2 k1.isLt, rot_inv_1 k k2.val hk2 k2.isLt] at h2
      exact Fin.ext h2
    · intro st hst
      let kw : Fin (2 ^ k) := ⟨keyOfStart k u st.val, keyOfStart_lt k u st.val⟩
      have hst_back : PEqualNP.Outside.L_meta_25508_aux.rot k 1 kw.val ^^^ u = st.val :=
        stateAux_keyOfStart_zero k constants u st.val hk2 hu st.isLt
      refine ⟨kw, ?_, Fin.ext hst_back⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.all_eq_true, List.mem_range,
                 Bool.not_eq_true'] at hst ⊢
      exact (flip_iff_all_guards k r constants u i hr hkr hu hik kw).mpr hst
  rw [hkey_to_start]
  have hstep_r := card_pass_step k r constants u i hr hkr hu r hr (Nat.le_refl r)
  have hbase := card_pass_base4 k r constants u i hr hkr hu
  dsimp only at hbase
  rw [hbase] at hstep_r
  have hpow_split : 2 ^ (k - 14) = 2 ^ (k - (14 + (r - 4))) * 2 ^ (r - 4) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hpow_split, ← Nat.mul_assoc] at hstep_r
  have hpos : 0 < 2 ^ (r - 4) := Nat.two_pow_pos (r - 4)
  exact Nat.eq_of_mul_eq_mul_right hpos hstep_r
