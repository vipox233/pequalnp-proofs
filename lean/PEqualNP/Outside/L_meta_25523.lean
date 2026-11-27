import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25504
import PEqualNP.Outside.L_meta_25522

namespace PEqualNP.Outside.L_meta_25523_aux

def rot (k s word : Nat) : Nat :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def step (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc j =>
    acc ||| ((xor (word.testBit j)
      (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0

def first (k : Nat) (c : Nat → Fin (2 ^ k)) (row key : Nat) : Nat :=
  (List.range 3).foldl (fun prev roundIndex =>
    step k (prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev) ^^^ rot k (2 * roundIndex) key ^^^
      (c (roundIndex + 1)).val) (rot k 1 key ^^^ row)

def okBit (k h : Nat) (c : Nat → Fin (2 ^ k)) (u : Fin (2 ^ k)) (target : Fin (2 ^ h))
    (w s : Nat) : Bool :=
  (first k c u.val w).testBit (k - 1 - s) == target.val.testBit (h - 1 - s)

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

lemma xor_two_pow_lt (k p w : Nat) (hp : p < k) (hw : w < 2 ^ k) :
    w ^^^ 2 ^ p < 2 ^ k :=
  Nat.xor_lt_two_pow hw (Nat.pow_lt_pow_right (by norm_num) hp)

lemma locality_of_low_bits (k h q : Nat) (c : Nat → Fin (2 ^ k)) (u : Fin (2 ^ k))
    (target : Fin (2 ^ h)) (hk : 13 ≤ k) (hq : q ≤ k - 11) (s : Nat) (hs : s < q)
    (w z : Nat) (hw : w < 2 ^ k) (hz : z < 2 ^ k)
    (hagree : ∀ j, j < k → (j < k - 3 - q ∨ k - 4 - s ≤ j) → w.testBit j = z.testBit j) :
    okBit k h c u target w s = okBit k h c u target z s := by
  unfold okBit
  congr 1
  have hi : k - 1 - s < k := by omega
  have h504 := PEqualNP.Outside.L_meta_25504 k hk c ⟨k - 1 - s, hi⟩ u ⟨w, hw⟩ u ⟨z, hz⟩
  apply h504
  · intro t
    have hidx : (k - 1 - s + k - 2 + t.val) % k < k := Nat.mod_lt _ (by omega)
    rw [Nat.testBit_xor, Nat.testBit_xor]
    congr 1
    change (rot k 1 w).testBit ((k - 1 - s + k - 2 + t.val) % k) =
      (rot k 1 z).testBit ((k - 1 - s + k - 2 + t.val) % k)
    rw [rot_testBit k 1 w _ hw hidx, rot_testBit k 1 z _ hz hidx]
    have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have hpos_eq : ((k - 1 - s + k - 2 + t.val) % k + k - 1) % k =
        (k - 4 - s + t.val) % k := by
      have e1 : (k - 1 - s + k - 2 + t.val) % k + k - 1 =
          (k - 1 - s + k - 2 + t.val) % k + (k - 1) := by omega
      rw [e1, Nat.mod_add_mod,
        show k - 1 - s + k - 2 + t.val + (k - 1) = (k - 4 - s + t.val) + 2 * k by omega,
        Nat.add_mul_mod_self_right]
    rw [hpos_eq]
    have hlt : (k - 4 - s + t.val) % k < k := Nat.mod_lt _ (by omega)
    apply hagree _ hlt
    by_cases hwrap : k - 4 - s + t.val < k
    · right
      rw [Nat.mod_eq_of_lt hwrap]
      omega
    · left
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      have ht := t.isLt
      omega
  · intro _
    rfl

lemma not_all_four_ok (k h q : Nat) (c : Nat → Fin (2 ^ k)) (u : Fin (2 ^ k))
    (target : Fin (2 ^ h)) (hk : 13 ≤ k) (hq : q ≤ k - 11) (s : Nat) (hs : s < q)
    (w : Nat) (hw : w < 2 ^ k) :
    let a := 2 ^ (k - 4 - s)
    let b := 2 ^ (k - 3 - s)
    ¬(okBit k h c u target w s = true ∧
      okBit k h c u target (w ^^^ a) s = true ∧
      okBit k h c u target (w ^^^ b) s = true ∧
      okBit k h c u target (w ^^^ b ^^^ a) s = true) := by
  intro a b h4
  obtain ⟨h00, h10, h01, h11⟩ := h4
  have hi : k - 1 - s < k := by omega
  have h522 := PEqualNP.Outside.L_meta_25522 k hk c u ⟨w, hw⟩ ⟨k - 1 - s, hi⟩
  have ha_eq : (k - 1 - s + k - 3) % k = k - 4 - s := by
    rw [show k - 1 - s + k - 3 = (k - 4 - s) + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  have hb_eq : (k - 1 - s + k - 2) % k = k - 3 - s := by
    rw [show k - 1 - s + k - 2 = (k - 3 - s) + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  have hab : w ^^^ a ^^^ b = w ^^^ b ^^^ a := by
    rw [Nat.xor_assoc, Nat.xor_comm a b, ← Nat.xor_assoc]
  have e00 : (first k c u.val w).testBit (k - 1 - s) = target.val.testBit (h - 1 - s) := by
    simpa [okBit] using h00
  have e10 : (first k c u.val (w ^^^ a)).testBit (k - 1 - s) = target.val.testBit (h - 1 - s) := by
    simpa [okBit] using h10
  have e01 : (first k c u.val (w ^^^ b)).testBit (k - 1 - s) = target.val.testBit (h - 1 - s) := by
    simpa [okBit] using h01
  have e11 : (first k c u.val (w ^^^ a ^^^ b)).testBit (k - 1 - s) =
      target.val.testBit (h - 1 - s) := by
    rw [hab]
    simpa [okBit] using h11
  change xor (xor ((first k c u.val w).testBit (k - 1 - s))
      ((first k c u.val (w ^^^ 2 ^ ((k - 1 - s + k - 3) % k))).testBit (k - 1 - s)))
    (xor ((first k c u.val (w ^^^ 2 ^ ((k - 1 - s + k - 2) % k))).testBit (k - 1 - s))
      ((first k c u.val (w ^^^ 2 ^ ((k - 1 - s + k - 3) % k) ^^^
        2 ^ ((k - 1 - s + k - 2) % k))).testBit (k - 1 - s))) = true at h522
  rw [ha_eq, hb_eq] at h522
  change xor (xor ((first k c u.val w).testBit (k - 1 - s))
      ((first k c u.val (w ^^^ a)).testBit (k - 1 - s)))
    (xor ((first k c u.val (w ^^^ b)).testBit (k - 1 - s))
      ((first k c u.val (w ^^^ a ^^^ b)).testBit (k - 1 - s))) = true at h522
  rw [e00, e10, e01, e11] at h522
  cases h : target.val.testBit (h - 1 - s) <;> simp [h] at h522

def G (k q : Nat) (ok : Nat → Nat → Bool) : Nat → Nat → Nat
  | 0, _ => 1
  | t + 1, w =>
    let s := q - (t + 1)
    let a := 2 ^ (k - 4 - s)
    (if ok w s then G k q ok t w else 0) +
    (if ok (w ^^^ a) s then G k q ok t (w ^^^ a) else 0)

lemma G_fib_bound (k h q : Nat) (c : Nat → Fin (2 ^ k)) (u : Fin (2 ^ k))
    (target : Fin (2 ^ h)) (hk : 13 ≤ k) (hq : q ≤ k - 11) :
    ∀ t, t ≤ q → ∀ w, w < 2 ^ k →
      G k q (okBit k h c u target) t w ≤ Nat.fib (t + 2) ∧
      G k q (okBit k h c u target) t w +
        G k q (okBit k h c u target) t (w ^^^ 2 ^ (k - 3 - (q - t))) ≤ Nat.fib (t + 3) := by
  intro t
  induction t with
  | zero =>
    intro _ w _
    simp [G, Nat.fib_add_two]
  | succ t ih =>
    intro ht w hw
    have hs : q - (t + 1) < q := by omega
    have hqt : q - t = q - (t + 1) + 1 := by omega
    have ha_pos : k - 4 - (q - (t + 1)) < k := by omega
    have hb_pos : k - 3 - (q - (t + 1)) < k := by omega
    have ha_eq : k - 3 - (q - t) = k - 4 - (q - (t + 1)) := by omega
    have h1 : ∀ z, z < 2 ^ k → G k q (okBit k h c u target) (t + 1) z ≤ Nat.fib (t + 3) := by
      intro z hz
      dsimp only [G]
      have hpair := (ih (by omega) z hz).2
      rw [ha_eq] at hpair
      have hle1 : (if okBit k h c u target z (q - (t + 1)) then
          G k q (okBit k h c u target) t z else 0) ≤ G k q (okBit k h c u target) t z := by
        split_ifs <;> omega
      have hle2 : (if okBit k h c u target (z ^^^ 2 ^ (k - 4 - (q - (t + 1)))) (q - (t + 1)) then
          G k q (okBit k h c u target) t (z ^^^ 2 ^ (k - 4 - (q - (t + 1)))) else 0) ≤
          G k q (okBit k h c u target) t (z ^^^ 2 ^ (k - 4 - (q - (t + 1)))) := by
        split_ifs <;> omega
      omega
    refine ⟨h1 w hw, ?_⟩
    set s := q - (t + 1)
    set a := 2 ^ (k - 4 - s)
    set b := 2 ^ (k - 3 - s)
    change G k q (okBit k h c u target) (t + 1) w +
      G k q (okBit k h c u target) (t + 1) (w ^^^ b) ≤ Nat.fib (t + 4)
    have hwa : w ^^^ a < 2 ^ k := xor_two_pow_lt k _ w ha_pos hw
    have hwb : w ^^^ b < 2 ^ k := xor_two_pow_lt k _ w hb_pos hw
    have hwba : w ^^^ b ^^^ a < 2 ^ k := xor_two_pow_lt k _ (w ^^^ b) ha_pos hwb
    have hnot4 := not_all_four_ok k h q c u target hk hq s hs w hw
    have hfib : Nat.fib (t + 4) = Nat.fib (t + 2) + Nat.fib (t + 3) := by
      rw [show t + 4 = (t + 2) + 2 by omega, Nat.fib_add_two]
    have hGw_le : G k q (okBit k h c u target) (t + 1) w ≤ Nat.fib (t + 3) := h1 w hw
    have hGwb_le : G k q (okBit k h c u target) (t + 1) (w ^^^ b) ≤ Nat.fib (t + 3) := h1 _ hwb
    have hsingle : ∀ z, z < 2 ^ k →
        (okBit k h c u target z s = false ∨ okBit k h c u target (z ^^^ a) s = false) →
        G k q (okBit k h c u target) (t + 1) z ≤ Nat.fib (t + 2) := by
      intro z hz hfalse
      have hza : z ^^^ a < 2 ^ k := xor_two_pow_lt k _ z ha_pos hz
      have hGz := (ih (by omega) z hz).1
      have hGza := (ih (by omega) (z ^^^ a) hza).1
      change (if okBit k h c u target z s then G k q (okBit k h c u target) t z else 0) +
        (if okBit k h c u target (z ^^^ a) s then
          G k q (okBit k h c u target) t (z ^^^ a) else 0) ≤ Nat.fib (t + 2)
      rcases hfalse with hf1 | hf2
      · rw [hf1]; simp; split_ifs <;> omega
      · rw [hf2]; simp; split_ifs <;> omega
    by_cases c00 : okBit k h c u target w s = true
    · by_cases c10 : okBit k h c u target (w ^^^ a) s = true
      · by_cases c01 : okBit k h c u target (w ^^^ b) s = true
        · have c11 : okBit k h c u target (w ^^^ b ^^^ a) s = false := by
            cases hc : okBit k h c u target (w ^^^ b ^^^ a) s
            · rfl
            · exact absurd ⟨c00, c10, c01, hc⟩ hnot4
          have := hsingle (w ^^^ b) hwb (Or.inr c11)
          omega
        · have c01f : okBit k h c u target (w ^^^ b) s = false := by
            cases hc : okBit k h c u target (w ^^^ b) s <;> simp_all
          have := hsingle (w ^^^ b) hwb (Or.inl c01f)
          omega
      · have c10f : okBit k h c u target (w ^^^ a) s = false := by
          cases hc : okBit k h c u target (w ^^^ a) s <;> simp_all
        have := hsingle w hw (Or.inr c10f)
        omega
    · have c00f : okBit k h c u target w s = false := by
        cases hc : okBit k h c u target w s <;> simp_all
      have := hsingle w hw (Or.inl c00f)
      omega

lemma disjoint_xor_eq_add : ∀ a b : Nat,
    (∀ j, (a.testBit j && b.testBit j) = false) → a + b = a ^^^ b := by
  intro a
  induction a using Nat.strong_induction_on with
  | ind a ih =>
    intro b hdisj
    by_cases ha0 : a = 0
    · subst ha0; simp
    · have h0 := hdisj 0
      rw [Nat.testBit_zero, Nat.testBit_zero] at h0
      have hdiv : ∀ j, ((a / 2).testBit j && (b / 2).testBit j) = false := by
        intro j
        have := hdisj (j + 1)
        rwa [Nat.testBit_succ, Nat.testBit_succ] at this
      have ih' := ih (a / 2) (Nat.div_lt_self (by omega) (by omega)) (b / 2) hdiv
      have hmod : a % 2 = 0 ∨ b % 2 = 0 := by
        have ha2 : a % 2 < 2 := Nat.mod_lt _ (by omega)
        have hb2 : b % 2 < 2 := Nat.mod_lt _ (by omega)
        by_cases h1 : a % 2 = 1
        · right
          have hf : decide (b % 2 = 1) = false := by simpa [h1] using h0
          have hne : b % 2 ≠ 1 := of_decide_eq_false hf
          omega
        · left; omega
      have hxor_div : (a ^^^ b) / 2 = (a / 2) ^^^ (b / 2) := by
        apply Nat.eq_of_testBit_eq; intro j
        rw [← Nat.testBit_succ, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ]
      have hxor_mod : (a ^^^ b) % 2 = a % 2 + b % 2 := by
        have hbit0 : (a ^^^ b).testBit 0 = xor (a.testBit 0) (b.testBit 0) := Nat.testBit_xor a b 0
        rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero] at hbit0
        have hxb : (a ^^^ b) % 2 = 0 ∨ (a ^^^ b) % 2 = 1 := by omega
        have ha2 : a % 2 = 0 ∨ a % 2 = 1 := by omega
        have hb2 : b % 2 = 0 ∨ b % 2 = 1 := by omega
        rcases hxb with hx | hx <;> rcases ha2 with ha | ha <;> rcases hb2 with hb | hb <;>
          simp [hx, ha, hb] at hbit0 hmod ⊢ <;> omega
      have h1 := Nat.div_add_mod a 2
      have h2 := Nat.div_add_mod b 2
      have h3 := Nat.div_add_mod (a ^^^ b) 2
      omega

lemma G_eq_card (k h q : Nat) (c : Nat → Fin (2 ^ k)) (u : Fin (2 ^ k))
    (target : Fin (2 ^ h)) (hk : 13 ≤ k) (hq : q ≤ k - 11) :
    ∀ t, t ≤ q → ∀ w, w < 2 ^ k →
      (∀ j, k - 3 - q ≤ j → j < k - 3 - q + t → w.testBit j = false) →
      G k q (okBit k h c u target) t w =
        ((Finset.univ : Finset (Fin (2 ^ t))).filter (fun v =>
          (List.range t).all (fun r =>
            okBit k h c u target (w ^^^ (v.val <<< (k - 3 - q))) (q - t + r)))).card := by
  intro t
  induction t with
  | zero =>
    intro _ w _ _
    simp [G]
  | succ t ih =>
    intro ht w hw hzero
    set s := q - (t + 1)
    set a := 2 ^ (k - 4 - s)
    have hpos_eq : k - 4 - s = k - 3 - q + t := by omega
    have ha_pos : k - 4 - s < k := by omega
    have hwa : w ^^^ a < 2 ^ k := xor_two_pow_lt k _ w ha_pos hw
    have hzero_lo : ∀ j, k - 3 - q ≤ j → j < k - 3 - q + t → w.testBit j = false :=
      fun j h1 h2 => hzero j h1 (by omega)
    have hzero_wa : ∀ j, k - 3 - q ≤ j → j < k - 3 - q + t → (w ^^^ a).testBit j = false := by
      intro j h1 h2
      rw [Nat.testBit_xor, hzero j h1 (by omega)]
      dsimp [a]
      rw [Nat.testBit_two_pow]
      have hne : k - 4 - s ≠ j := by omega
      simp [hne]
    have ih0 := ih (by omega) w hw hzero_lo
    have ih1 := ih (by omega) (w ^^^ a) hwa hzero_wa
    have hsplit : ∀ v : Fin (2 ^ (t + 1)),
        let b := decide (2 ^ t ≤ v.val)
        let v' : Fin (2 ^ t) := ⟨v.val % 2 ^ t, Nat.mod_lt _ (Nat.two_pow_pos t)⟩
        w ^^^ (v.val <<< (k - 3 - q)) =
          (if b then w ^^^ a else w) ^^^ (v'.val <<< (k - 3 - q)) := by
      intro v b v'
      have hv_split : v.val = (if b then 2 ^ t else 0) + v'.val := by
        dsimp [b, v']
        split_ifs with hge
        · have hge' : 2 ^ t ≤ v.val := of_decide_eq_true hge
          have hlt : v.val < 2 ^ t + 2 ^ t := by
            calc
              v.val < 2 ^ (t + 1) := v.isLt
              _ = 2 ^ t + 2 ^ t := by rw [pow_succ, mul_two]
          have hmod : v.val % 2 ^ t = v.val - 2 ^ t := by
            rw [Nat.mod_eq_sub_mod hge', Nat.mod_eq_of_lt (by omega)]
          omega
        · have hlt' : v.val < 2 ^ t := by
            have hn : ¬(2 ^ t ≤ v.val) := by
              intro h; exact hge (decide_eq_true h)
            omega
          rw [Nat.mod_eq_of_lt hlt']; omega
      have hxor_v : v.val = (if b then 2 ^ t else 0) ^^^ v'.val := by
        rw [hv_split]
        apply disjoint_xor_eq_add
        intro j
        split_ifs
        · rw [Nat.testBit_two_pow]
          by_cases hjt : t = j
          · subst hjt
            rw [Nat.testBit_lt_two_pow v'.isLt]; simp
          · simp [hjt]
        · simp
      have hshift : (v.val <<< (k - 3 - q)) =
          ((if b then a else 0) ^^^ (v'.val <<< (k - 3 - q))) := by
        rw [hxor_v]
        apply Nat.eq_of_testBit_eq
        intro j
        rw [Nat.testBit_shiftLeft, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft]
        by_cases hj : k - 3 - q ≤ j
        · simp only [hj, decide_true, Bool.true_and]
          split_ifs
          · dsimp [a]
            rw [Nat.testBit_two_pow, Nat.testBit_two_pow]
            have hiff : (t = j - (k - 3 - q)) ↔ (k - 4 - s = j) := by omega
            simp [hiff]
          · simp
        · simp only [hj, decide_false, Bool.false_and]
          split_ifs
          · dsimp [a]
            rw [Nat.testBit_two_pow]
            have hne : k - 4 - s ≠ j := by omega
            simp [hne]
          · simp
      rw [hshift, ← Nat.xor_assoc]
      split_ifs <;> simp
    have hok_indep : ∀ (base : Nat) (v' : Fin (2 ^ t)), base < 2 ^ k →
        okBit k h c u target (base ^^^ (v'.val <<< (k - 3 - q))) s =
          okBit k h c u target base s := by
      intro base v' hbase
      have hv_lt : (v'.val <<< (k - 3 - q)) < 2 ^ k := by
        rw [Nat.shiftLeft_eq]
        calc
          v'.val * 2 ^ (k - 3 - q) < 2 ^ t * 2 ^ (k - 3 - q) :=
            Nat.mul_lt_mul_of_pos_right v'.isLt (Nat.two_pow_pos _)
          _ = 2 ^ (t + (k - 3 - q)) := (pow_add 2 t (k - 3 - q)).symm
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      apply locality_of_low_bits k h q c u target hk hq s (by omega) _ base
        (Nat.xor_lt_two_pow hbase hv_lt) hbase
      intro j hj hrange
      rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
      rcases hrange with hlo | hhi
      · have hnot : ¬(k - 3 - q ≤ j) := by omega
        simp [hnot]
      · have hv_false : v'.val.testBit (j - (k - 3 - q)) = false := by
          apply Nat.testBit_lt_two_pow
          exact lt_of_lt_of_le v'.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
        simp [hv_false]
    have hrange_split : ∀ (z : Nat),
        (List.range (t + 1)).all (fun r => okBit k h c u target z (s + r)) =
          (okBit k h c u target z s &&
            (List.range t).all (fun r => okBit k h c u target z ((q - t) + r))) := by
      intro z
      rw [List.range_succ_eq_map, List.all_cons, List.all_map, Nat.add_zero]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, List.mem_range, Function.comp_apply]
      constructor <;> intro hh r hr
      · have := hh r hr; rwa [show s + (r + 1) = q - t + r by omega] at this
      · have := hh r hr; rwa [show q - t + r = s + (r + 1) by omega] at this
    set S := (Finset.univ : Finset (Fin (2 ^ (t + 1)))).filter (fun v =>
      (List.range (t + 1)).all (fun r =>
        okBit k h c u target (w ^^^ (v.val <<< (k - 3 - q))) (s + r)))
    set S0 := S.filter (fun v => v.val < 2 ^ t)
    set S1 := S.filter (fun v => 2 ^ t ≤ v.val)
    have hdisj : Disjoint S0 S1 := by
      rw [Finset.disjoint_left]
      intro v hv0 hv1
      rw [Finset.mem_filter] at hv0 hv1
      omega
    have hunion : S0 ∪ S1 = S := by
      ext v
      simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h
        by_cases hlt : v.val < 2 ^ t
        · exact Or.inl ⟨h, hlt⟩
        · exact Or.inr ⟨h, by omega⟩
    have hScard : S.card = S0.card + S1.card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hS0 : S0.card = (if okBit k h c u target w s then
        ((Finset.univ : Finset (Fin (2 ^ t))).filter (fun v' =>
          (List.range t).all (fun r =>
            okBit k h c u target (w ^^^ (v'.val <<< (k - 3 - q))) (q - t + r)))).card else 0) := by
      split_ifs with hok0
      · refine Finset.card_bij (fun v hv => ⟨v.val, (Finset.mem_filter.mp hv).2⟩) ?_ ?_ ?_
        · intro v hv
          rw [Finset.mem_filter] at hv
          obtain ⟨hvS, hvlt⟩ := hv
          rw [Finset.mem_filter] at hvS ⊢
          refine ⟨Finset.mem_univ _, ?_⟩
          have hall := hvS.2
          rw [hrange_split, Bool.and_eq_true] at hall
          exact hall.2
        · intro v1 _ v2 _ hEq
          exact Fin.ext (Fin.mk.inj hEq)
        · intro v' hv'
          rw [Finset.mem_filter] at hv'
          have hvlt : v'.val < 2 ^ (t + 1) :=
            lt_trans v'.isLt (Nat.pow_lt_pow_right (by norm_num) (by omega))
          refine ⟨⟨v'.val, hvlt⟩, ?_, Fin.ext rfl⟩
          rw [Finset.mem_filter]
          refine ⟨?_, v'.isLt⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [hrange_split, Bool.and_eq_true]
          exact ⟨by rw [hok_indep w v' hw]; exact hok0, hv'.2⟩
      · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro v hv
        rw [Finset.mem_filter] at hv
        obtain ⟨hvS, hvlt⟩ := hv
        rw [Finset.mem_filter] at hvS
        have hall := hvS.2
        rw [hrange_split, Bool.and_eq_true] at hall
        have hokv := hall.1
        rw [hok_indep w ⟨v.val, hvlt⟩ hw] at hokv
        exact hok0 hokv
    have hS1 : S1.card = (if okBit k h c u target (w ^^^ a) s then
        ((Finset.univ : Finset (Fin (2 ^ t))).filter (fun v' =>
          (List.range t).all (fun r =>
            okBit k h c u target ((w ^^^ a) ^^^ (v'.val <<< (k - 3 - q))) (q - t + r)))).card
        else 0) := by
      split_ifs with hok1
      · refine Finset.card_bij (fun v _ => ⟨v.val % 2 ^ t, Nat.mod_lt _ (Nat.two_pow_pos t)⟩)
          ?_ ?_ ?_
        · intro v hv
          rw [Finset.mem_filter] at hv
          obtain ⟨hvS, hvge⟩ := hv
          rw [Finset.mem_filter] at hvS ⊢
          refine ⟨Finset.mem_univ _, ?_⟩
          have hall := hvS.2
          have hsp := hsplit v
          simp only [hvge, decide_true, ↓reduceIte] at hsp
          rw [hrange_split, Bool.and_eq_true, hsp] at hall
          exact hall.2
        · intro v1 hv1 v2 hv2 hEq
          rw [Finset.mem_filter] at hv1 hv2
          have h1lt : v1.val < 2 ^ t + 2 ^ t := by
            calc
              v1.val < 2 ^ (t + 1) := v1.isLt
              _ = 2 ^ t + 2 ^ t := by rw [pow_succ, mul_two]
          have h2lt : v2.val < 2 ^ t + 2 ^ t := by
            calc
              v2.val < 2 ^ (t + 1) := v2.isLt
              _ = 2 ^ t + 2 ^ t := by rw [pow_succ, mul_two]
          have h1m : v1.val % 2 ^ t = v1.val - 2 ^ t := by
            rw [Nat.mod_eq_sub_mod hv1.2, Nat.mod_eq_of_lt (by omega)]
          have h2m : v2.val % 2 ^ t = v2.val - 2 ^ t := by
            rw [Nat.mod_eq_sub_mod hv2.2, Nat.mod_eq_of_lt (by omega)]
          have hval : v1.val % 2 ^ t = v2.val % 2 ^ t := congrArg Fin.val hEq
          apply Fin.ext
          omega
        · intro v' hv'
          rw [Finset.mem_filter] at hv'
          have hvlt : 2 ^ t + v'.val < 2 ^ (t + 1) := by
            rw [pow_succ, mul_two]; exact Nat.add_lt_add_left v'.isLt (2 ^ t)
          let v : Fin (2 ^ (t + 1)) := ⟨2 ^ t + v'.val, hvlt⟩
          have hvmod : v.val % 2 ^ t = v'.val := by
            dsimp [v]
            rw [Nat.add_mod_left, Nat.mod_eq_of_lt v'.isLt]
          have hvge : 2 ^ t ≤ v.val := by dsimp [v]; omega
          refine ⟨v, ?_, Fin.ext hvmod⟩
          rw [Finset.mem_filter]
          refine ⟨?_, hvge⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hsp := hsplit v
          simp only [hvge, decide_true, ↓reduceIte, hvmod] at hsp
          rw [hrange_split, Bool.and_eq_true, hsp]
          exact ⟨by rw [hok_indep (w ^^^ a) v' hwa]; exact hok1, hv'.2⟩
      · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro v hv
        rw [Finset.mem_filter] at hv
        obtain ⟨hvS, hvge⟩ := hv
        rw [Finset.mem_filter] at hvS
        have hall := hvS.2
        have hsp := hsplit v
        simp only [hvge, decide_true, ↓reduceIte] at hsp
        rw [hrange_split, Bool.and_eq_true, hsp] at hall
        have hokv := hall.1
        rw [hok_indep (w ^^^ a) ⟨v.val % 2 ^ t, Nat.mod_lt _ (Nat.two_pow_pos t)⟩ hwa] at hokv
        exact hok1 hokv
    change (if okBit k h c u target w s then G k q (okBit k h c u target) t w else 0) +
      (if okBit k h c u target (w ^^^ a) s then
        G k q (okBit k h c u target) t (w ^^^ a) else 0) = S.card
    rw [ih0, ih1, hScard, hS0, hS1]

lemma main (k h : Nat) (hk : 13 ≤ k) (hh0 : 0 < h) (hhk : h ≤ k)
    (c : Nat → Fin (2 ^ k)) (u : Fin (2 ^ k)) (target : Fin (2 ^ h)) :
    let q := min h (k - 11)
    ((List.range (2 ^ k)).filter (fun w =>
      decide ((first k c u.val w >>> (k - h)) = target.val))).length ≤
      2 ^ (k - (q + 1)) * Nat.fib (q + 3) := by
  intro q
  have hq_le_h : q ≤ h := Nat.min_le_left _ _
  have hq_le_k11 : q ≤ k - 11 := Nat.min_le_right _ _
  have hq_pos : 1 ≤ q := by omega
  have hlist_to_fin :
      ((List.range (2 ^ k)).filter (fun w =>
        decide ((first k c u.val w >>> (k - h)) = target.val))).length ≤
      ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
        (List.range q).all (fun s => okBit k h c u target w.val s))).card := by
    have h1 :
        ((List.range (2 ^ k)).filter (fun w =>
          decide ((first k c u.val w >>> (k - h)) = target.val))).length =
        ((Finset.range (2 ^ k)).filter (fun w =>
          (first k c u.val w >>> (k - h)) = target.val)).card := by
      rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
      congr 1
      ext x
      simp [Finset.mem_filter, Finset.mem_range]
    rw [h1]
    have h2 :
        ((Finset.range (2 ^ k)).filter (fun w =>
          (first k c u.val w >>> (k - h)) = target.val)).card =
        ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
          (first k c u.val w.val >>> (k - h)) = target.val)).card := by
      refine Finset.card_bij (fun w hw => ⟨w, (Finset.mem_range.mp (Finset.mem_filter.mp hw).1)⟩)
        ?_ ?_ ?_
      · intro w hw
        rw [Finset.mem_filter] at hw ⊢
        exact ⟨Finset.mem_univ _, hw.2⟩
      · intro w1 _ w2 _ hEq
        exact congrArg Fin.val hEq
      · intro w hw
        rw [Finset.mem_filter] at hw
        refine ⟨w.val, ?_, Fin.ext rfl⟩
        rw [Finset.mem_filter, Finset.mem_range]
        exact ⟨w.isLt, hw.2⟩
    rw [h2]
    apply Finset.card_le_card
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [List.all_eq_true]
    intro s hs
    rw [List.mem_range] at hs
    unfold okBit
    simp only [beq_iff_eq]
    have hbit := congrArg (fun n => n.testBit (h - 1 - s)) hw.2
    rw [Nat.testBit_shiftRight, show k - h + (h - 1 - s) = k - 1 - s by omega] at hbit
    exact hbit
  apply le_trans hlist_to_fin
  let loBits := k - 3 - q
  let extWord : Fin (2 ^ loBits) × Fin (2 ^ 2) → Nat :=
    fun p => p.1.val + p.2.val * 2 ^ (k - 2)
  have hext_lt : ∀ p : Fin (2 ^ loBits) × Fin (2 ^ 2), extWord p < 2 ^ k := by
    intro p
    dsimp [extWord]
    have hlo : p.1.val < 2 ^ (k - 2) :=
      lt_of_lt_of_le p.1.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hhi : p.2.val + 1 ≤ 4 := by have := p.2.isLt; omega
    calc
      p.1.val + p.2.val * 2 ^ (k - 2) < (p.2.val + 1) * 2 ^ (k - 2) := by
        rw [add_mul, one_mul]; omega
      _ ≤ 4 * 2 ^ (k - 2) := Nat.mul_le_mul_right _ hhi
      _ = 2 ^ 2 * 2 ^ (k - 2) := by norm_num
      _ = 2 ^ k := by rw [← pow_add, show 2 + (k - 2) = k by omega]
  have hext_zero : ∀ (p : Fin (2 ^ loBits) × Fin (2 ^ 2)) (j : Nat),
      loBits ≤ j → j < k - 2 → (extWord p).testBit j = false := by
    intro p j hj1 hj2
    have hdisj : ∀ m, (p.1.val.testBit m && (p.2.val * 2 ^ (k - 2)).testBit m) = false := by
      intro m
      by_cases hm : m < k - 2
      · rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
        have : ¬(k - 2 ≤ m) := by omega
        simp [this]
      · have : p.1.val.testBit m = false := by
          apply Nat.testBit_lt_two_pow
          exact lt_of_lt_of_le p.1.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
        simp [this]
    dsimp [extWord]
    rw [disjoint_xor_eq_add _ _ hdisj, Nat.testBit_xor, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
    have hp1 : p.1.val.testBit j = false := by
      apply Nat.testBit_lt_two_pow
      exact lt_of_lt_of_le p.1.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hnot : ¬(k - 2 ≤ j) := by omega
    simp [hp1, hnot]
  let mkWord : (Fin (2 ^ loBits) × Fin (2 ^ 2)) × (Bool × Fin (2 ^ q)) → Fin (2 ^ k) :=
    fun ⟨p, b, v⟩ =>
      ⟨(if b then extWord p ^^^ 2 ^ (k - 3) else extWord p) ^^^ (v.val <<< loBits), by
        have hbase : (if b then extWord p ^^^ 2 ^ (k - 3) else extWord p) < 2 ^ k := by
          split_ifs
          · exact xor_two_pow_lt k (k - 3) (extWord p) (by omega) (hext_lt p)
          · exact hext_lt p
        have hvlt : (v.val <<< loBits) < 2 ^ k := by
          rw [Nat.shiftLeft_eq]
          calc
            v.val * 2 ^ loBits < 2 ^ q * 2 ^ loBits :=
              Nat.mul_lt_mul_of_pos_right v.isLt (Nat.two_pow_pos _)
            _ = 2 ^ (q + loBits) := (pow_add 2 q loBits).symm
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact Nat.xor_lt_two_pow hbase hvlt⟩
  have hmk_val : ∀ p b v,
      (mkWord (p, b, v)).val =
        p.1.val + (v.val + (if b then 2 ^ q else 0)) * 2 ^ loBits + p.2.val * 2 ^ (k - 2) := by
    intro p b v
    dsimp [mkWord, extWord]
    have hdisj1 : ∀ m, (p.1.val.testBit m && (p.2.val * 2 ^ (k - 2)).testBit m) = false := by
      intro m
      by_cases hm : m < k - 2
      · rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
        have : ¬(k - 2 ≤ m) := by omega
        simp [this]
      · have : p.1.val.testBit m = false := by
          apply Nat.testBit_lt_two_pow
          exact lt_of_lt_of_le p.1.isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
        simp [this]
    have hv_b : (v.val + (if b then 2 ^ q else 0)) * 2 ^ loBits =
        (if b then 2 ^ (k - 3) else 0) ^^^ (v.val <<< loBits) := by
      have hdisj_vb : ∀ m, (v.val.testBit m && (if b then 2 ^ q else 0).testBit m) = false := by
        intro m
        split_ifs
        · rw [Nat.testBit_two_pow]
          by_cases hmq : q = m
          · subst hmq
            rw [Nat.testBit_lt_two_pow v.isLt]; simp
          · simp [hmq]
        · simp
      rw [disjoint_xor_eq_add _ _ hdisj_vb, ← Nat.shiftLeft_eq]
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_shiftLeft, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_shiftLeft]
      by_cases hj : loBits ≤ j
      · simp only [hj, decide_true, Bool.true_and]
        split_ifs
        · rw [Nat.testBit_two_pow, Nat.testBit_two_pow]
          have hiff : (q = j - loBits) ↔ (k - 3 = j) := by omega
          simp [hiff, Bool.xor_comm]
        · simp
      · simp only [hj, decide_false, Bool.false_and]
        split_ifs
        · rw [Nat.testBit_two_pow]
          have hne : k - 3 ≠ j := by omega
          simp [hne]
        · simp
    have hdisj_all : ∀ m,
        ((p.1.val + p.2.val * 2 ^ (k - 2)).testBit m &&
          ((v.val + (if b then 2 ^ q else 0)) * 2 ^ loBits).testBit m) = false := by
      intro m
      by_cases hm1 : loBits ≤ m
      · by_cases hm2 : m < k - 2
        · rw [hext_zero p m hm1 hm2]; simp
        · have hlt : (v.val + (if b then 2 ^ q else 0)) * 2 ^ loBits < 2 ^ (k - 2) := by
            have h1 : v.val + (if b then 2 ^ q else 0) < 2 ^ (q + 1) := by
              rw [pow_succ, mul_two]
              split_ifs <;> have := v.isLt <;> omega
            calc
              (v.val + (if b then 2 ^ q else 0)) * 2 ^ loBits < 2 ^ (q + 1) * 2 ^ loBits :=
                Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
              _ = 2 ^ (k - 2) := by rw [← pow_add, show q + 1 + loBits = k - 2 by omega]
          have hf : ((v.val + (if b then 2 ^ q else 0)) * 2 ^ loBits).testBit m = false :=
            Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)))
          simp [hf]
      · have hzero2 : ((v.val + (if b then 2 ^ q else 0)) * 2 ^ loBits).testBit m = false := by
          rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
          simp [hm1]
        simp [hzero2]
    have hrearr :
        p.1.val + (v.val + (if b then 2 ^ q else 0)) * 2 ^ loBits + p.2.val * 2 ^ (k - 2) =
        (p.1.val + p.2.val * 2 ^ (k - 2)) + (v.val + (if b then 2 ^ q else 0)) * 2 ^ loBits := by
      omega
    rw [hrearr, disjoint_xor_eq_add _ _ hdisj_all, hv_b, ← Nat.xor_assoc]
    split_ifs <;> simp
  have hmk_bij : Function.Bijective mkWord := by
    constructor
    · intro x1 x2 hEq
      rcases x1 with ⟨⟨lo1, hi1⟩, b1, v1⟩
      rcases x2 with ⟨⟨lo2, hi2⟩, b2, v2⟩
      have hv := congrArg Fin.val hEq
      rw [hmk_val, hmk_val] at hv
      have hmid1 : v1.val + (if b1 then 2 ^ q else 0) < 2 ^ (q + 1) := by
        rw [pow_succ, mul_two]; split_ifs <;> have := v1.isLt <;> omega
      have hmid2 : v2.val + (if b2 then 2 ^ q else 0) < 2 ^ (q + 1) := by
        rw [pow_succ, mul_two]; split_ifs <;> have := v2.isLt <;> omega
      have hlow1 : lo1.val + (v1.val + (if b1 then 2 ^ q else 0)) * 2 ^ loBits < 2 ^ (k - 2) := by
        have hlt1 : (v1.val + (if b1 then 2 ^ q else 0) + 1) ≤ 2 ^ (q + 1) := by omega
        calc
          lo1.val + (v1.val + (if b1 then 2 ^ q else 0)) * 2 ^ loBits
            < (v1.val + (if b1 then 2 ^ q else 0) + 1) * 2 ^ loBits := by
              have hmul : (v1.val + (if b1 then 2 ^ q else 0) + 1) * 2 ^ loBits =
                  (v1.val + (if b1 then 2 ^ q else 0)) * 2 ^ loBits + 2 ^ loBits := by ring
              linarith [lo1.isLt]
          _ ≤ 2 ^ (q + 1) * 2 ^ loBits := Nat.mul_le_mul_right _ hlt1
          _ = 2 ^ (k - 2) := by rw [← pow_add, show q + 1 + loBits = k - 2 by omega]
      have hlow2 : lo2.val + (v2.val + (if b2 then 2 ^ q else 0)) * 2 ^ loBits < 2 ^ (k - 2) := by
        have hlt2 : (v2.val + (if b2 then 2 ^ q else 0) + 1) ≤ 2 ^ (q + 1) := by omega
        calc
          lo2.val + (v2.val + (if b2 then 2 ^ q else 0)) * 2 ^ loBits
            < (v2.val + (if b2 then 2 ^ q else 0) + 1) * 2 ^ loBits := by
              have hmul : (v2.val + (if b2 then 2 ^ q else 0) + 1) * 2 ^ loBits =
                  (v2.val + (if b2 then 2 ^ q else 0)) * 2 ^ loBits + 2 ^ loBits := by ring
              linarith [lo2.isLt]
          _ ≤ 2 ^ (q + 1) * 2 ^ loBits := Nat.mul_le_mul_right _ hlt2
          _ = 2 ^ (k - 2) := by rw [← pow_add, show q + 1 + loBits = k - 2 by omega]
      have hhi : hi1.val = hi2.val := by
        have h1 := congrArg (fun n => n / 2 ^ (k - 2)) hv
        rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
          Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
          Nat.div_eq_of_lt hlow1, Nat.div_eq_of_lt hlow2, zero_add, zero_add] at h1
        exact h1
      have hlow_eq : lo1.val + (v1.val + (if b1 then 2 ^ q else 0)) * 2 ^ loBits =
          lo2.val + (v2.val + (if b2 then 2 ^ q else 0)) * 2 ^ loBits := by
        dsimp only at hv
        rw [hhi] at hv; omega
      have hlo : lo1.val = lo2.val := by
        have h1 := congrArg (fun n => n % 2 ^ loBits) hlow_eq
        rw [Nat.add_mul_mod_self_right, Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt lo1.isLt, Nat.mod_eq_of_lt lo2.isLt] at h1
        exact h1
      have hmid_eq : v1.val + (if b1 then 2 ^ q else 0) = v2.val + (if b2 then 2 ^ q else 0) := by
        have h1 := congrArg (fun n => n / 2 ^ loBits) hlow_eq
        rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
          Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
          Nat.div_eq_of_lt lo1.isLt, Nat.div_eq_of_lt lo2.isLt, zero_add, zero_add] at h1
        exact h1
      have hb : b1 = b2 := by
        cases b1 <;> cases b2
        · rfl
        · have := v1.isLt; simp at hmid_eq; omega
        · have := v2.isLt; simp at hmid_eq; omega
        · rfl
      subst hb
      have hv_eq : v1.val = v2.val := by omega
      exact Prod.ext (Prod.ext (Fin.ext hlo) (Fin.ext hhi)) (Prod.ext rfl (Fin.ext hv_eq))
    · intro w
      let hi : Fin (2 ^ 2) := ⟨w.val / 2 ^ (k - 2), by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, show 2 + (k - 2) = k by omega]
        exact w.isLt⟩
      let rem := w.val % 2 ^ (k - 2)
      have hrem : rem < 2 ^ (k - 2) := Nat.mod_lt _ (Nat.two_pow_pos _)
      let lo : Fin (2 ^ loBits) := ⟨rem % 2 ^ loBits, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
      let mid := rem / 2 ^ loBits
      have hmid : mid < 2 ^ (q + 1) := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add,
          show q + 1 + loBits = k - 2 by omega]
        exact hrem
      let b : Bool := decide (2 ^ q ≤ mid)
      let v : Fin (2 ^ q) := ⟨mid % 2 ^ q, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
      refine ⟨((lo, hi), b, v), ?_⟩
      apply Fin.ext
      rw [hmk_val]
      have hmv : v.val + (if b then 2 ^ q else 0) = mid := by
        dsimp [v, b]
        split_ifs with hge
        · have hge' : 2 ^ q ≤ mid := of_decide_eq_true hge
          have h2 : mid < 2 ^ q + 2 ^ q := by rw [pow_succ, mul_two] at hmid; exact hmid
          rw [Nat.mod_eq_sub_mod hge', Nat.mod_eq_of_lt (by omega)]; omega
        · have hlt' : mid < 2 ^ q := by
            have hn : ¬(2 ^ q ≤ mid) := by intro h; exact hge (decide_eq_true h)
            omega
          rw [Nat.mod_eq_of_lt hlt']; omega
      dsimp only
      rw [hmv]
      have h1 : lo.val + mid * 2 ^ loBits = rem := by
        dsimp [lo, mid]
        have := Nat.div_add_mod rem (2 ^ loBits)
        linarith
      have h2 : rem + hi.val * 2 ^ (k - 2) = w.val := by
        dsimp [rem, hi]
        have := Nat.div_add_mod w.val (2 ^ (k - 2))
        linarith
      omega
  have hcard_eq :
      ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
        (List.range q).all (fun s => okBit k h c u target w.val s))).card =
      ∑ p : Fin (2 ^ loBits) × Fin (2 ^ 2),
        (G k q (okBit k h c u target) q (extWord p) +
          G k q (okBit k h c u target) q (extWord p ^^^ 2 ^ (k - 3))) := by
    have hbij_card :
        ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
          (List.range q).all (fun s => okBit k h c u target w.val s))).card =
        ((Finset.univ : Finset ((Fin (2 ^ loBits) × Fin (2 ^ 2)) × (Bool × Fin (2 ^ q)))).filter
          (fun x => (List.range q).all (fun s => okBit k h c u target (mkWord x).val s))).card := by
      symm
      refine Finset.card_bij (fun x _ => mkWord x) ?_ ?_ ?_
      · intro x hx
        rw [Finset.mem_filter] at hx ⊢
        exact ⟨Finset.mem_univ _, hx.2⟩
      · intro x1 _ x2 _ hEq
        exact hmk_bij.1 hEq
      · intro w hw
        rw [Finset.mem_filter] at hw
        obtain ⟨x, hx⟩ := hmk_bij.2 w
        refine ⟨x, ?_, hx⟩
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [hx]; exact hw.2⟩
    rw [hbij_card, Finset.card_filter, Fintype.sum_prod_type]
    congr 1
    ext p
    rw [Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
    have hG0 := G_eq_card k h q c u target hk hq_le_k11 q (le_refl _) (extWord p) (hext_lt p)
      (fun j hj1 hj2 => hext_zero p j hj1 (by omega))
    have hG1 := G_eq_card k h q c u target hk hq_le_k11 q (le_refl _)
      (extWord p ^^^ 2 ^ (k - 3)) (xor_two_pow_lt k (k - 3) (extWord p) (by omega) (hext_lt p))
      (fun j hj1 hj2 => by
        rw [Nat.testBit_xor, hext_zero p j hj1 (by omega), Nat.testBit_two_pow]
        have hne : k - 3 ≠ j := by omega
        simp [hne])
    simp only [Nat.sub_self, zero_add] at hG0 hG1
    rw [hG0, hG1, Finset.card_filter, Finset.card_filter]
    rfl
  rw [hcard_eq]
  calc
    ∑ p : Fin (2 ^ loBits) × Fin (2 ^ 2),
        (G k q (okBit k h c u target) q (extWord p) +
          G k q (okBit k h c u target) q (extWord p ^^^ 2 ^ (k - 3)))
      ≤ ∑ _p : Fin (2 ^ loBits) × Fin (2 ^ 2), Nat.fib (q + 3) := by
        apply Finset.sum_le_sum
        intro p _
        have hb := (G_fib_bound k h q c u target hk hq_le_k11 q (le_refl _) (extWord p)
          (hext_lt p)).2
        simpa using hb
    _ = (Finset.univ : Finset (Fin (2 ^ loBits) × Fin (2 ^ 2))).card * Nat.fib (q + 3) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = 2 ^ (k - (q + 1)) * Nat.fib (q + 3) := by
        congr 1
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, ← pow_add]
        congr 1
        omega

end PEqualNP.Outside.L_meta_25523_aux

theorem PEqualNP.Outside.L_meta_25523 : (∀ (k h : Nat), 13 ≤ k → 0 < h → h ≤ k →
  ∀ (c : Nat → Fin (2 ^ k)) (u : Fin (2 ^ k)) (target : Fin (2 ^ h)),
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
  let q := min h (k - 11)
  ((List.range (2 ^ k)).filter (fun w =>
    decide ((first u.val w >>> (k - h)) = target.val))).length ≤
    2 ^ (k - (q + 1)) * Nat.fib (q + 3)) := by
  intro k h hk hh0 hhk c u target
  exact PEqualNP.Outside.L_meta_25523_aux.main k h hk hh0 hhk c u target
