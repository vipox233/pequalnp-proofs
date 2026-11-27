import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25504_aux

def rot (k s word : Nat) : Nat :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def step (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc j =>
    acc ||| ((xor (word.testBit j)
      (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0

def rnd (k cc key prev t : Nat) : Nat :=
  step k (prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev) ^^^ rot k (2 * t) key ^^^ cc

def first (k : Nat) (c : Nat → Fin (2 ^ k)) (row key : Nat) : Nat :=
  (List.range 3).foldl (fun prev roundIndex =>
    rnd k (c (roundIndex + 1)).val key prev roundIndex) (rot k 1 key ^^^ row)

def D (a b m : Nat) : Bool := xor (a.testBit m) (b.testBit m)

def P (k x d : Nat) : Nat := (x + d) % k

lemma xor_false_eq (a b : Bool) (h : xor a b = false) : a = b := by
  revert h
  cases a <;> cases b <;> decide

lemma rot_lt (k s x : Nat) : rot k s x < 2 ^ k := Nat.mod_lt _ (by positivity)

lemma rot_testBit (k s x j : Nat) (hx : x < 2 ^ k) (hj : j < k) :
    (rot k s x).testBit j = x.testBit ((j + k - s % k) % k) := by
  unfold rot
  have hs : s % k < k := Nat.mod_lt _ (by omega)
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : s % k ≤ j
  · have e : (j + k - s % k) % k = j - s % k := by
      have e' : j + k - s % k = (j - s % k) + k := by omega
      rw [e', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have f : x.testBit (k - s % k + j) = false := by
      apply Nat.testBit_lt_two_pow
      exact lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [e, f]
    simp [h, hj]
  · have e : (j + k - s % k) % k = k - s % k + j := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [e]
    simp [h, hj]

lemma fold_testBit (f : Nat → Bool) (m j : Nat) :
    ((List.range m).foldl (fun acc i => acc ||| ((f i).toNat <<< i)) 0).testBit j =
      (decide (j < m) && f j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.testBit_or, ih,
      Nat.testBit_shiftLeft]
    by_cases h1 : j < m
    · have h2 : ¬ (j ≥ m) := by omega
      have h3 : j < m + 1 := by omega
      simp [h1, h2, h3]
    · by_cases h2 : j = m
      · subst h2
        cases hf : f j <;> simp
      · have h3 : ¬ (j < m + 1) := by omega
        have h4 : j - m ≠ 0 := by omega
        have h5 : Nat.testBit 1 (j - m) = false := by
          obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h4
          rw [hn, Nat.testBit_succ]
          simp
        cases hf : f m <;> simp [h1, h3, h5]

lemma step_testBit (k x j : Nat) :
    (step k x).testBit j = (decide (j < k) && xor (x.testBit j)
      (!(x.testBit ((j + 1) % k)) && x.testBit ((j + 2) % k))) :=
  fold_testBit (fun j => xor (x.testBit j)
    (!(x.testBit ((j + 1) % k)) && x.testBit ((j + 2) % k))) k j

lemma step_lt (k x : Nat) : step k x < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [step_testBit]
  have h : ¬ (j < k) := by omega
  simp [h]

lemma rnd_lt (k cc key prev t : Nat) (hc : cc < 2 ^ k) : rnd k cc key prev t < 2 ^ k := by
  unfold rnd
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (step_lt _ _) (rot_lt _ _ _)) hc

lemma theta_testBit (k p m : Nat) (hk : 13 ≤ k) (hp : p < 2 ^ k) (hm : m < k) :
    (p ^^^ rot k 1 p ^^^ rot k (k - 1) p).testBit m =
      xor (xor (p.testBit m) (p.testBit ((m + k - 1) % k))) (p.testBit ((m + 1) % k)) := by
  have e1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have e2 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
  have e3 : m + k - (k - 1) = m + 1 := by omega
  rw [Nat.testBit_xor, Nat.testBit_xor, rot_testBit k 1 p m hp hm,
    rot_testBit k (k - 1) p m hp hm, e1, e2, e3]

lemma rnd_testBit (k cc key p t j : Nat) (hk : 13 ≤ k) (hp : p < 2 ^ k) (hkey : key < 2 ^ k)
    (hj : j < k) :
    (rnd k cc key p t).testBit j =
      xor (xor (xor (xor (xor (p.testBit j) (p.testBit ((j + k - 1) % k)))
          (p.testBit ((j + 1) % k)))
        (!(xor (xor (p.testBit ((j + 1) % k)) (p.testBit j)) (p.testBit ((j + 2) % k))) &&
          xor (xor (p.testBit ((j + 2) % k)) (p.testBit ((j + 1) % k)))
            (p.testBit ((j + 3) % k))))
        (key.testBit ((j + k - (2 * t) % k) % k))) (cc.testBit j) := by
  have hk0 : 0 < k := by omega
  have e1 : ((j + 1) % k + k - 1) % k = j := by
    rw [show (j + 1) % k + k - 1 = (j + 1) % k + (k - 1) by omega, Nat.mod_add_mod,
      show j + 1 + (k - 1) = j + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  have e2 : ((j + 1) % k + 1) % k = (j + 2) % k := by rw [Nat.mod_add_mod]
  have e3 : ((j + 2) % k + k - 1) % k = (j + 1) % k := by
    rw [show (j + 2) % k + k - 1 = (j + 2) % k + (k - 1) by omega, Nat.mod_add_mod,
      show j + 2 + (k - 1) = j + 1 + k by omega, Nat.add_mod_right]
  have e4 : ((j + 2) % k + 1) % k = (j + 3) % k := by rw [Nat.mod_add_mod]
  unfold rnd
  rw [Nat.testBit_xor, Nat.testBit_xor, step_testBit, rot_testBit k (2 * t) key j hkey hj,
    theta_testBit k p j hk hp hj, theta_testBit k p ((j + 1) % k) hk hp (Nat.mod_lt _ hk0),
    theta_testBit k p ((j + 2) % k) hk hp (Nat.mod_lt _ hk0), e1, e2, e3, e4]
  simp only [hj, decide_true, Bool.true_and]

lemma rnd_diff (k cc key key' p p' t j : Nat) (hk : 13 ≤ k) (hp : p < 2 ^ k) (hp' : p' < 2 ^ k)
    (hkey : key < 2 ^ k) (hkey' : key' < 2 ^ k) (hj : j < k)
    (h : ∀ e, e < 4 → D p p' ((j + e) % k) = false) :
    D (rnd k cc key p t) (rnd k cc key' p' t) j =
      xor (D p p' ((j + k - 1) % k)) (D key key' ((j + k - (2 * t) % k) % k)) := by
  have g0 : p.testBit j = p'.testBit j := by
    have h0 := h 0 (by omega)
    rw [Nat.add_zero, Nat.mod_eq_of_lt hj] at h0
    exact xor_false_eq _ _ h0
  have g1 : p.testBit ((j + 1) % k) = p'.testBit ((j + 1) % k) :=
    xor_false_eq _ _ (h 1 (by omega))
  have g2 : p.testBit ((j + 2) % k) = p'.testBit ((j + 2) % k) :=
    xor_false_eq _ _ (h 2 (by omega))
  have g3 : p.testBit ((j + 3) % k) = p'.testBit ((j + 3) % k) :=
    xor_false_eq _ _ (h 3 (by omega))
  unfold D
  rw [rnd_testBit k cc key p t j hk hp hkey hj, rnd_testBit k cc key' p' t j hk hp' hkey' hj,
    g0, g1, g2, g3]
  generalize p'.testBit j = b0
  generalize p'.testBit ((j + 1) % k) = b1
  generalize p'.testBit ((j + 2) % k) = b2
  generalize p'.testBit ((j + 3) % k) = b3
  generalize p.testBit ((j + k - 1) % k) = a
  generalize p'.testBit ((j + k - 1) % k) = a'
  generalize key.testBit ((j + k - (2 * t) % k) % k) = q
  generalize key'.testBit ((j + k - (2 * t) % k) % k) = q'
  generalize cc.testBit j = cb
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases a <;> cases a' <;> cases q <;>
    cases q' <;> cases cb <;> rfl

lemma P_lt (k x d : Nat) (hk : 0 < k) : P k x d < k := Nat.mod_lt _ hk

lemma P_add (k x d e : Nat) : (P k x d + e) % k = P k x (d + e) := by
  unfold P
  rw [Nat.mod_add_mod, Nat.add_assoc]

lemma P_sub (k x d a : Nat) (ha : a ≤ k) : (P k x (d + a) + k - a) % k = P k x d := by
  unfold P
  rw [show (x + (d + a)) % k + k - a = (x + (d + a)) % k + (k - a) by omega, Nat.mod_add_mod,
    show x + (d + a) + (k - a) = x + d + k by omega, Nat.add_mod_right]

lemma rnd_diffP (k cc key key' p p' t x d dm dk a : Nat) (hk : 13 ≤ k)
    (hp : p < 2 ^ k) (hp' : p' < 2 ^ k) (hkey : key < 2 ^ k) (hkey' : key' < 2 ^ k)
    (ha : (2 * t) % k = a) (hak : a ≤ k) (hdm : dm + 1 = d) (hdk : dk + a = d)
    (h : ∀ e, e < 4 → D p p' (P k x (d + e)) = false) :
    D (rnd k cc key p t) (rnd k cc key' p' t) (P k x d) =
      xor (D p p' (P k x dm)) (D key key' (P k x dk)) := by
  have e1 : (P k x d + k - 1) % k = P k x dm := by
    rw [← hdm]
    exact P_sub k x dm 1 (by omega)
  have e2 : (P k x d + k - a) % k = P k x dk := by
    rw [← hdk]
    exact P_sub k x dk a hak
  rw [rnd_diff k cc key key' p p' t (P k x d) hk hp hp' hkey hkey' (P_lt k x _ (by omega))
    (by intro e he; rw [P_add]; exact h e he), ha, e1, e2]

lemma three (k c1 c2 c3 w z s0 s0' x : Nat) (hk : 13 ≤ k)
    (hc1 : c1 < 2 ^ k) (hc2 : c2 < 2 ^ k) (hw : w < 2 ^ k) (hz : z < 2 ^ k)
    (hs0 : s0 < 2 ^ k) (hs0' : s0' < 2 ^ k)
    (hS0 : ∀ d, 2 ≤ d → d ≤ 13 → D s0 s0' (P k x d) = false)
    (hKz : ∀ d, 1 ≤ d → d ≤ 10 → D w z (P k x d) = false)
    (hK0 : D w z (P k x 0) = D s0 s0' (P k x 1)) :
    D (rnd k c3 w (rnd k c2 w (rnd k c1 w s0 0) 1) 2)
      (rnd k c3 z (rnd k c2 z (rnd k c1 z s0' 0) 1) 2) (P k x 4) = false := by
  have hs1 : rnd k c1 w s0 0 < 2 ^ k := rnd_lt _ _ _ _ _ hc1
  have hs1' : rnd k c1 z s0' 0 < 2 ^ k := rnd_lt _ _ _ _ _ hc1
  have hs2 : rnd k c2 w (rnd k c1 w s0 0) 1 < 2 ^ k := rnd_lt _ _ _ _ _ hc2
  have hs2' : rnd k c2 z (rnd k c1 z s0' 0) 1 < 2 ^ k := rnd_lt _ _ _ _ _ hc2
  have a0 : (2 * 0) % k = 0 := by simp
  have a1 : (2 * 1) % k = 2 := by rw [Nat.mod_eq_of_lt (by omega)]
  have a2 : (2 * 2) % k = 4 := by rw [Nat.mod_eq_of_lt (by omega)]
  have h1a : ∀ d, 3 ≤ d → d ≤ 10 →
      D (rnd k c1 w s0 0) (rnd k c1 z s0' 0) (P k x d) = false := by
    intro d hd1 hd2
    rw [rnd_diffP k c1 w z s0 s0' 0 x d (d - 1) d 0 hk hs0 hs0' hw hz a0 (by omega)
      (by omega) (by omega) (fun e he => hS0 (d + e) (by omega) (by omega)),
      hS0 (d - 1) (by omega) (by omega), hKz d (by omega) (by omega)]
    rfl
  have h1b : D (rnd k c1 w s0 0) (rnd k c1 z s0' 0) (P k x 2) = D s0 s0' (P k x 1) := by
    rw [rnd_diffP k c1 w z s0 s0' 0 x 2 1 2 0 hk hs0 hs0' hw hz a0 (by omega)
      (by omega) (by omega) (fun e he => hS0 (2 + e) (by omega) (by omega)),
      hKz 2 (by omega) (by omega), Bool.xor_false]
  have h2a : ∀ d, 4 ≤ d → d ≤ 7 →
      D (rnd k c2 w (rnd k c1 w s0 0) 1) (rnd k c2 z (rnd k c1 z s0' 0) 1) (P k x d) = false := by
    intro d hd1 hd2
    rw [rnd_diffP k c2 w z (rnd k c1 w s0 0) (rnd k c1 z s0' 0) 1 x d (d - 1) (d - 2) 2 hk
      hs1 hs1' hw hz a1 (by omega) (by omega) (by omega)
      (fun e he => h1a (d + e) (by omega) (by omega)),
      h1a (d - 1) (by omega) (by omega), hKz (d - 2) (by omega) (by omega)]
    rfl
  have h2b : D (rnd k c2 w (rnd k c1 w s0 0) 1) (rnd k c2 z (rnd k c1 z s0' 0) 1) (P k x 3) =
      D s0 s0' (P k x 1) := by
    rw [rnd_diffP k c2 w z (rnd k c1 w s0 0) (rnd k c1 z s0' 0) 1 x 3 2 1 2 hk
      hs1 hs1' hw hz a1 (by omega) (by omega) (by omega)
      (fun e he => h1a (3 + e) (by omega) (by omega)),
      h1b, hKz 1 (by omega) (by omega), Bool.xor_false]
  rw [rnd_diffP k c3 w z (rnd k c2 w (rnd k c1 w s0 0) 1) (rnd k c2 z (rnd k c1 z s0' 0) 1) 2 x
    4 3 0 4 hk hs2 hs2' hw hz a2 (by omega) (by omega) (by omega)
    (fun e he => h2a (4 + e) (by omega) (by omega)), h2b, hK0]
  exact Bool.xor_self _

lemma main_nat (k c1 c2 c3 i u w v z : Nat) (hk : 13 ≤ k)
    (hc1 : c1 < 2 ^ k) (hc2 : c2 < 2 ^ k) (hi : i < k)
    (hu : u < 2 ^ k) (hw : w < 2 ^ k) (hv : v < 2 ^ k) (hz : z < 2 ^ k)
    (hS : ∀ t, t < 12 → (rot k 1 w ^^^ u).testBit ((i + k - 2 + t) % k) =
      (rot k 1 z ^^^ v).testBit ((i + k - 2 + t) % k))
    (hR : ∀ t, t < 11 → u.testBit ((i + k - 3 + t) % k) = v.testBit ((i + k - 3 + t) % k)) :
    (rnd k c3 w (rnd k c2 w (rnd k c1 w (rot k 1 w ^^^ u) 0) 1) 2).testBit i =
      (rnd k c3 z (rnd k c2 z (rnd k c1 z (rot k 1 z ^^^ v) 0) 1) 2).testBit i := by
  have hk0 : 0 < k := by omega
  have hs0 : rot k 1 w ^^^ u < 2 ^ k := Nat.xor_lt_two_pow (rot_lt _ _ _) hu
  have hs0' : rot k 1 z ^^^ v < 2 ^ k := Nat.xor_lt_two_pow (rot_lt _ _ _) hv
  have hS0 : ∀ d, 2 ≤ d → d ≤ 13 →
      D (rot k 1 w ^^^ u) (rot k 1 z ^^^ v) (P k (i + k - 4) d) = false := by
    intro d hd1 hd2
    have h := hS (d - 2) (by omega)
    have e : i + k - 2 + (d - 2) = i + k - 4 + d := by omega
    rw [e] at h
    unfold D P
    rw [h]
    exact Bool.xor_self _
  have hR0 : ∀ d, 1 ≤ d → d ≤ 11 → D u v (P k (i + k - 4) d) = false := by
    intro d hd1 hd2
    have h := hR (d - 1) (by omega)
    have e : i + k - 3 + (d - 1) = i + k - 4 + d := by omega
    rw [e] at h
    unfold D P
    rw [h]
    exact Bool.xor_self _
  have hK : ∀ d, D w z (P k (i + k - 4) d) =
      xor (D (rot k 1 w ^^^ u) (rot k 1 z ^^^ v) (P k (i + k - 4) (d + 1)))
        (D u v (P k (i + k - 4) (d + 1))) := by
    intro d
    unfold D
    rw [Nat.testBit_xor, Nat.testBit_xor, rot_testBit k 1 w _ hw (P_lt k _ _ hk0),
      rot_testBit k 1 z _ hz (P_lt k _ _ hk0), Nat.mod_eq_of_lt (show 1 < k by omega),
      P_sub k (i + k - 4) d 1 (by omega)]
    generalize w.testBit (P k (i + k - 4) d) = a
    generalize z.testBit (P k (i + k - 4) d) = b
    generalize u.testBit (P k (i + k - 4) (d + 1)) = e
    generalize v.testBit (P k (i + k - 4) (d + 1)) = f
    cases a <;> cases b <;> cases e <;> cases f <;> rfl
  have hKz : ∀ d, 1 ≤ d → d ≤ 10 → D w z (P k (i + k - 4) d) = false := by
    intro d hd1 hd2
    rw [hK, hS0 (d + 1) (by omega) (by omega), hR0 (d + 1) (by omega) (by omega)]
    rfl
  have hK0 : D w z (P k (i + k - 4) 0) =
      D (rot k 1 w ^^^ u) (rot k 1 z ^^^ v) (P k (i + k - 4) 1) := by
    rw [hK, hR0 (0 + 1) (by omega) (by omega), Bool.xor_false]
  have h3 := three k c1 c2 c3 w z (rot k 1 w ^^^ u) (rot k 1 z ^^^ v) (i + k - 4) hk hc1 hc2
    hw hz hs0 hs0' hS0 hKz hK0
  have e : P k (i + k - 4) 4 = i := by
    unfold P
    rw [show i + k - 4 + 4 = i + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  rw [e] at h3
  exact xor_false_eq _ _ h3

lemma main (k : Nat) (hk : 13 ≤ k) (c : Nat → Fin (2 ^ k)) (i : Fin k) (u w v z : Fin (2 ^ k)) :
    (∀ t : Fin 12, (rot k 1 w.val ^^^ u.val).testBit ((i.val + k - 2 + t.val) % k) =
      (rot k 1 z.val ^^^ v.val).testBit ((i.val + k - 2 + t.val) % k)) →
    (∀ t : Fin 11, u.val.testBit ((i.val + k - 3 + t.val) % k) =
      v.val.testBit ((i.val + k - 3 + t.val) % k)) →
    (first k c u.val w.val).testBit i.val = (first k c v.val z.val).testBit i.val := by
  intro hS hR
  exact main_nat k (c 1).val (c 2).val (c 3).val i.val u.val w.val v.val z.val hk
    (c 1).isLt (c 2).isLt i.isLt u.isLt w.isLt v.isLt z.isLt
    (fun t ht => hS ⟨t, ht⟩) (fun t ht => hR ⟨t, ht⟩)

end PEqualNP.Outside.L_meta_25504_aux

theorem PEqualNP.Outside.L_meta_25504 : (∀ (k : Nat), 13 ≤ k → ∀ (c : Nat → Fin (2 ^ k))
    (i : Fin k) (u w v z : Fin (2 ^ k)),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc j =>
      acc ||| ((xor (word.testBit j)
        (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0
  let start := fun (row key : Nat) => rot 1 key ^^^ row
  let first := fun (row key : Nat) =>
    (List.range 3).foldl (fun prev roundIndex =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * roundIndex) key ^^^ (c (roundIndex + 1)).val)
      (start row key)
  (∀ t : Fin 12, (start u.val w.val).testBit ((i.val + k - 2 + t.val) % k) =
    (start v.val z.val).testBit ((i.val + k - 2 + t.val) % k)) →
  (∀ t : Fin 11, u.val.testBit ((i.val + k - 3 + t.val) % k) =
    v.val.testBit ((i.val + k - 3 + t.val) % k)) →
  (first u.val w.val).testBit i.val = (first v.val z.val).testBit i.val) := by
  intro k hk c i u w v z
  exact PEqualNP.Outside.L_meta_25504_aux.main k hk c i u w v z
