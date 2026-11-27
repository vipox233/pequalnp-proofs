import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25530

def rot (k s w : Nat) : Nat :=
  ((w <<< (s % k)) ||| (w >>> (k - s % k))) % 2 ^ k

def chi (a b c : Bool) : Bool :=
  xor a (!b && c)

def step (k w : Nat) : Nat :=
  (List.range k).foldl (fun acc j =>
    acc ||| ((chi (w.testBit j) (w.testBit ((j + 1) % k)) (w.testBit ((j + 2) % k))).toNat <<< j)) 0

def mix (k w : Nat) : Nat :=
  w ^^^ rot k 1 w ^^^ rot k (k - 1) w

def bit (k w n : Nat) : Bool :=
  w.testBit (n % k)

def stateAux (k : Nat) (c : Nat → Fin (2 ^ k)) (u key rounds : Nat) : Nat :=
  (List.range rounds).foldl (fun prev t =>
    step k (mix k prev) ^^^ rot k (2 * t) key ^^^ (c (t + 1)).val) (rot k 1 key ^^^ u)

def preWord (k : Nat) (c : Nat → Fin (2 ^ k)) (u key t : Nat) : Nat :=
  step k (mix k (stateAux k c u key (t - 1)))

def wave (k r : Nat) (c : Nat → Fin (2 ^ k)) (u key t : Nat) : Nat :=
  if t < r then stateAux k c u key t else preWord k c u key r

def leftOff (s : Nat) : Nat :=
  max (s + 1) (2 * s - 2)

def guard (k r : Nat) (c : Nat → Fin (2 ^ k)) (u i key t g : Nat) : Bool :=
  let z := stateAux k c u key (t - 1)
  let b := i + 3 * (r - t) + k - g
  xor (xor (bit k z b) (bit k z (b + 1))) (bit k z (b + 2))

def flipBit (k p : Nat) (hk : 0 < k) (key : Fin (2 ^ k)) : Fin (2 ^ k) :=
  ⟨key.val ^^^ 2 ^ (p % k),
    Nat.xor_lt_two_pow key.isLt (Nat.pow_lt_pow_right (by omega) (Nat.mod_lt p hk))⟩

def flipOff (k i r x : Nat) (hk : 0 < k) (key : Fin (2 ^ k)) : Fin (2 ^ k) :=
  flipBit k (i + 3 * r + k - x) hk key

def maxSat (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => if p (n + 1) then n + 1 else maxSat p n

def binomTail (n d : Nat) : Nat :=
  ∑ j ∈ Finset.range (d + 1), Nat.choose n j

def accepts (k r e q : Nat) (consts : Nat → Fin (2 ^ k)) (u i : Nat) :
    Nat → Nat → Nat → Nat → Bool
  | n, t, j, key =>
    let cut := e + q + 3
    let D := e + q - 1
    let N := (r - e) - cut
    let m := N - D
    if m + 1 ≤ j then true
    else match n with
      | 0 => false
      | n' + 1 =>
        if t ≤ cut + D + j ∧ cut + D + j - t ≤ D ∧ cut + D + j - t ≤ 4 * (r - t) then
          if guard k r consts u i key t (cut + D + j - t) then
            accepts k r e q consts u i n' (t + 1) j key
          else
            accepts k r e q consts u i n' (t + 1) (j + 1) key
        else false

lemma rot_lt (k s w : Nat) : rot k s w < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma testBit_pack (f : Nat → Bool) (n j : Nat) :
    ((List.range n).foldl (fun acc m => acc ||| ((f m).toNat <<< m)) 0).testBit j =
      (decide (j < n) && f j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Nat.testBit_or, ih, Nat.shiftLeft_eq]
    by_cases h : n = j
    · subst h; cases f n <;> simp
    · have hcmp : j < n + 1 ↔ j < n := by omega
      cases f n <;> simp [h, hcmp]

lemma step_lt (k w : Nat) : step k w < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  unfold step
  rw [testBit_pack]
  simp [Nat.not_lt_of_ge hj]

lemma mix_lt {k w : Nat} (hw : w < 2 ^ k) : mix k w < 2 ^ k :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hw (rot_lt k 1 w)) (rot_lt k (k - 1) w)

lemma stateAux_zero (k : Nat) (c : Nat → Fin (2 ^ k)) (u key : Nat) :
    stateAux k c u key 0 = rot k 1 key ^^^ u := rfl

lemma stateAux_succ (k : Nat) (c : Nat → Fin (2 ^ k)) (u key t : Nat) :
    stateAux k c u key (t + 1) =
      step k (mix k (stateAux k c u key t)) ^^^ rot k (2 * t) key ^^^ (c (t + 1)).val := by
  unfold stateAux
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma stateAux_lt {k u : Nat} (c : Nat → Fin (2 ^ k)) (hu : u < 2 ^ k) (key t : Nat) :
    stateAux k c u key t < 2 ^ k := by
  cases t with
  | zero => exact Nat.xor_lt_two_pow (rot_lt k 1 key) hu
  | succ t =>
    rw [stateAux_succ]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (step_lt k _) (rot_lt k (2 * t) key)) (c (t + 1)).isLt

lemma bit_xor (k x y n : Nat) :
    bit k (x ^^^ y) n = xor (bit k x n) (bit k y n) :=
  Nat.testBit_xor _ _ _

lemma bit_add_k (k w n : Nat) :
    bit k w (n + k) = bit k w n := by
  unfold bit
  rw [Nat.add_mod_right]

lemma bit_rot {k s w : Nat} (hs : s < k) (hw : w < 2 ^ k) (n : Nat) :
    bit k (rot k s w) (n + s) = bit k w n := by
  have hk : 0 < k := by omega
  have hr : n % k < k := Nat.mod_lt n hk
  unfold bit rot
  rw [Nat.mod_eq_of_lt hs, Nat.testBit_mod_two_pow, Nat.testBit_or,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    decide_eq_true (Nat.mod_lt _ hk), Bool.true_and, ← Nat.mod_add_mod n k s]
  by_cases h : n % k + s < k
  · rw [Nat.mod_eq_of_lt h]
    have hhi : w.testBit (k - s + (n % k + s)) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [hhi]
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have heq : k - s + (n % k + s - k) = n % k := by omega
    simp [heq, show ¬ s ≤ n % k + s - k by omega]

lemma bit_rot_any {k w : Nat} (hk : 0 < k) (hw : w < 2 ^ k) (s n : Nat) :
    bit k (rot k s w) (n + s) = bit k w n := by
  have hrot : rot k s w = rot k (s % k) w := by
    unfold rot
    rw [Nat.mod_mod]
  have hmod : (n + s) % k = (n + s % k) % k := by
    rw [Nat.add_mod, Nat.add_mod n (s % k), Nat.mod_mod]
  unfold bit
  rw [hmod, hrot]
  exact bit_rot (Nat.mod_lt s hk) hw n

lemma bit_step {k : Nat} (hk : 0 < k) (w n : Nat) :
    bit k (step k w) n = chi (bit k w n) (bit k w (n + 1)) (bit k w (n + 2)) := by
  unfold bit step
  rw [testBit_pack, decide_eq_true (Nat.mod_lt n hk), Bool.true_and,
    Nat.mod_add_mod, Nat.mod_add_mod]

lemma bit_mix {k w : Nat} (hk : 2 ≤ k) (hw : w < 2 ^ k) (n : Nat) :
    bit k (mix k w) (n + 1) =
      xor (xor (bit k w (n + 1)) (bit k w n)) (bit k w (n + 2)) := by
  have h1 := bit_rot (k := k) (s := 1) (by omega) hw n
  have h2 := bit_rot (k := k) (s := k - 1) (by omega) hw (n + 2)
  have he : n + 2 + (k - 1) = (n + 1) + k := by omega
  rw [he] at h2
  simp only [bit, Nat.add_mod_right] at h2
  unfold mix
  rw [bit_xor, bit_xor, h1]
  exact congrArg (xor _) h2

lemma bit_step_mix_eq {k w1 w2 : Nat} (hk : 2 ≤ k) (hw1 : w1 < 2 ^ k) (hw2 : w2 < 2 ^ k)
    (n : Nat)
    (h0 : bit k w1 n = bit k w2 n)
    (h1 : bit k w1 (n + 1) = bit k w2 (n + 1))
    (h2 : bit k w1 (n + 2) = bit k w2 (n + 2))
    (h3 : bit k w1 (n + 3) = bit k w2 (n + 3))
    (h4 : bit k w1 (n + 4) = bit k w2 (n + 4)) :
    bit k (step k (mix k w1)) (n + 1) = bit k (step k (mix k w2)) (n + 1) := by
  rw [bit_step (by omega), bit_step (by omega)]
  have hm0 : bit k (mix k w1) (n + 1) = bit k (mix k w2) (n + 1) := by
    rw [bit_mix hk hw1 n, bit_mix hk hw2 n, h0, h1, h2]
  have hm1 : bit k (mix k w1) (n + 1 + 1) = bit k (mix k w2) (n + 1 + 1) := by
    rw [bit_mix hk hw1 (n + 1), bit_mix hk hw2 (n + 1), h1, h2, h3]
  have hm2 : bit k (mix k w1) (n + 1 + 2) = bit k (mix k w2) (n + 1 + 2) := by
    have he : n + 1 + 2 = (n + 2) + 1 := by omega
    rw [he, bit_mix hk hw1 (n + 2), bit_mix hk hw2 (n + 2), h2, h3, h4]
  rw [hm0, hm1, hm2]

lemma bit_step_mix_forced {k w1 w2 : Nat} (hk : 2 ≤ k) (hw1 : w1 < 2 ^ k) (hw2 : w2 < 2 ^ k)
    (n : Nat)
    (h0 : bit k w1 n = bit k w2 n)
    (h1 : bit k w1 (n + 1) = bit k w2 (n + 1))
    (h2 : bit k w1 (n + 2) = bit k w2 (n + 2))
    (h3 : bit k w1 (n + 3) = bit k w2 (n + 3))
    (hne : bit k (step k (mix k w1)) (n + 1) ≠ bit k (step k (mix k w2)) (n + 1)) :
    xor (xor (bit k w1 (n + 1)) (bit k w1 (n + 2))) (bit k w1 (n + 3)) = false := by
  rw [bit_step (by omega), bit_step (by omega)] at hne
  have hm0 : bit k (mix k w1) (n + 1) = bit k (mix k w2) (n + 1) := by
    rw [bit_mix hk hw1 n, bit_mix hk hw2 n, h0, h1, h2]
  have hm1 : bit k (mix k w1) (n + 1 + 1) = bit k (mix k w2) (n + 1 + 1) := by
    rw [bit_mix hk hw1 (n + 1), bit_mix hk hw2 (n + 1), h1, h2, h3]
  rw [hm0, hm1] at hne
  have hb : bit k (mix k w2) (n + 1 + 1) = false := by
    revert hne
    unfold chi
    cases bit k (mix k w2) (n + 1) <;>
      cases bit k (mix k w2) (n + 1 + 1) <;>
      cases bit k (mix k w1) (n + 1 + 2) <;>
      cases bit k (mix k w2) (n + 1 + 2) <;>
      decide
  rw [← hm1, bit_mix hk hw1 (n + 1)] at hb
  revert hb
  cases bit k w1 (n + 1) <;> cases bit k w1 (n + 2) <;> cases bit k w1 (n + 3) <;> decide

lemma mod_ne_of_diff {k a b : Nat} (h : a < b) (hd : b - a < k) (o : Nat) :
    (o + a) % k ≠ (o + b) % k := by
  have hk : 0 < k := by omega
  have hr : (o + a) % k < k := Nat.mod_lt _ hk
  have hb : (o + b) % k = ((o + a) % k + (b - a)) % k := by
    rw [Nat.mod_add_mod, show o + a + (b - a) = o + b by omega]
  rw [hb]
  by_cases hs : (o + a) % k + (b - a) < k
  · rw [Nat.mod_eq_of_lt hs]; omega
  · have hge : k ≤ (o + a) % k + (b - a) := by omega
    have hlt : (o + a) % k + (b - a) - k < k := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]; omega

lemma bit_flipBit (k p : Nat) (hk : 0 < k) (key : Fin (2 ^ k)) (n : Nat) :
    bit k (flipBit k p hk key).val n = xor (bit k key.val n) (decide (p % k = n % k)) := by
  unfold bit flipBit
  rw [Nat.testBit_xor, Nat.testBit_two_pow]

lemma flipBit_invol (k p : Nat) (hk : 0 < k) (key : Fin (2 ^ k)) :
    flipBit k p hk (flipBit k p hk key) = key := by
  apply Fin.ext
  dsimp only [flipBit]
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

lemma flipOff_invol (k i r x : Nat) (hk : 0 < k) (key : Fin (2 ^ k)) :
    flipOff k i r x hk (flipOff k i r x hk key) = key :=
  flipBit_invol k (i + 3 * r + k - x) hk key

lemma stateAux_cone {k u : Nat} (hk : 2 ≤ k) (consts : Nat → Fin (2 ^ k)) (hu : u < 2 ^ k)
    {key1 key2 : Nat} (hk1 : key1 < 2 ^ k) (hk2 : key2 < 2 ^ k) :
    ∀ s a, (∀ d < leftOff s + 3 * s, bit k key1 (a + d) = bit k key2 (a + d)) →
      bit k (stateAux k consts u key1 s) (a + leftOff s) =
        bit k (stateAux k consts u key2 s) (a + leftOff s) := by
  intro s
  induction s with
  | zero =>
    intro a h
    rw [stateAux_zero, stateAux_zero, bit_xor, bit_xor]
    have hlo : leftOff 0 = 1 := by unfold leftOff; omega
    rw [hlo, bit_rot (by omega) hk1 a, bit_rot (by omega) hk2 a]
    have h0 := h 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [h0]
  | succ s ih =>
    intro a h
    rw [stateAux_succ, stateAux_succ, bit_xor, bit_xor, bit_xor, bit_xor]
    have hrot_eq : bit k (rot k (2 * s) key1) (a + leftOff (s + 1)) =
        bit k (rot k (2 * s) key2) (a + leftOff (s + 1)) := by
      have hge : 2 * s ≤ leftOff (s + 1) := by unfold leftOff; omega
      have he : a + leftOff (s + 1) = (a + (leftOff (s + 1) - 2 * s)) + 2 * s := by omega
      rw [he, bit_rot_any (by omega) hk1, bit_rot_any (by omega) hk2]
      exact h (leftOff (s + 1) - 2 * s) (by omega)
    have hge1 : leftOff s + 1 ≤ leftOff (s + 1) := by unfold leftOff; omega
    let δ := leftOff (s + 1) - (leftOff s + 1)
    have hpos : a + leftOff (s + 1) = (a + δ + leftOff s) + 1 := by omega
    have hprev : ∀ j ≤ 4,
        bit k (stateAux k consts u key1 s) (a + δ + leftOff s + j) =
          bit k (stateAux k consts u key2 s) (a + δ + leftOff s + j) := by
      intro j hj
      have he : a + δ + leftOff s + j = (a + δ + j) + leftOff s := by omega
      rw [he]
      apply ih (a + δ + j)
      intro d hd
      have he2 : a + δ + j + d = a + (δ + j + d) := by omega
      rw [he2]
      exact h (δ + j + d) (by omega)
    have hstep_eq : bit k (step k (mix k (stateAux k consts u key1 s))) (a + leftOff (s + 1)) =
        bit k (step k (mix k (stateAux k consts u key2 s))) (a + leftOff (s + 1)) := by
      rw [hpos]
      exact bit_step_mix_eq hk (stateAux_lt consts hu key1 s) (stateAux_lt consts hu key2 s)
        (a + δ + leftOff s)
        (by simpa using hprev 0 (by omega))
        (hprev 1 (by omega))
        (hprev 2 (by omega))
        (hprev 3 (by omega))
        (hprev 4 (by omega))
    rw [hstep_eq, hrot_eq]

lemma stateAux_pivot {k u : Nat} (hk : 2 ≤ k) (consts : Nat → Fin (2 ^ k)) (hu : u < 2 ^ k)
    {key1 key2 : Nat} (hk1 : key1 < 2 ^ k) (hk2 : key2 < 2 ^ k)
    {s : Nat} (hs : 3 ≤ s) (a : Nat)
    (hagree : ∀ d, 1 ≤ d → d ≤ 5 * s + 2 → bit k key1 (a + d) = bit k key2 (a + d))
    (hflip : bit k key1 a = !(bit k key2 a)) :
    bit k (stateAux k consts u key1 (s + 1)) (a + 2 * s) =
      !(bit k (stateAux k consts u key2 (s + 1)) (a + 2 * s)) := by
  rw [stateAux_succ, stateAux_succ, bit_xor, bit_xor, bit_xor, bit_xor]
  have hlo : leftOff s = 2 * s - 2 := by unfold leftOff; omega
  have hpos : a + 2 * s = (a + 1 + leftOff s) + 1 := by omega
  have hprev : ∀ j ≤ 4,
      bit k (stateAux k consts u key1 s) (a + 1 + leftOff s + j) =
        bit k (stateAux k consts u key2 s) (a + 1 + leftOff s + j) := by
    intro j hj
    have he : a + 1 + leftOff s + j = (a + 1 + j) + leftOff s := by omega
    rw [he]
    apply stateAux_cone hk consts hu hk1 hk2 s (a + 1 + j)
    intro d hd
    have he2 : a + 1 + j + d = a + (1 + j + d) := by omega
    rw [he2]
    exact hagree (1 + j + d) (by omega) (by omega)
  have hstep_eq : bit k (step k (mix k (stateAux k consts u key1 s))) (a + 2 * s) =
      bit k (step k (mix k (stateAux k consts u key2 s))) (a + 2 * s) := by
    rw [hpos]
    exact bit_step_mix_eq hk (stateAux_lt consts hu key1 s) (stateAux_lt consts hu key2 s)
      (a + 1 + leftOff s)
      (by simpa using hprev 0 (by omega))
      (hprev 1 (by omega))
      (hprev 2 (by omega))
      (hprev 3 (by omega))
      (hprev 4 (by omega))
  have hrot : bit k (rot k (2 * s) key1) (a + 2 * s) = !(bit k (rot k (2 * s) key2) (a + 2 * s)) := by
    rw [bit_rot_any (by omega) hk1, bit_rot_any (by omega) hk2, hflip]
  rw [hstep_eq, hrot]
  cases bit k (step k (mix k (stateAux k consts u key2 s))) (a + 2 * s) <;>
    cases bit k (rot k (2 * s) key2) (a + 2 * s) <;>
    cases bit k (consts (s + 1)).val (a + 2 * s) <;>
    decide

lemma guard_flip_pivot {k r e q u i : Nat} (consts : Nat → Fin (2 ^ k))
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r) (hu : u < 2 ^ k)
    (hkpos : 0 < k)
    {t g : Nat} (ht1 : e + q + 4 ≤ t) (ht2 : t ≤ r - e) (hg : g ≤ 4 * (r - t))
    (key : Fin (2 ^ k)) :
    let off := 5 * t - 4 + g
    guard k r consts u i (flipOff k i r off hkpos key).val t g =
      !(guard k r consts u i key.val t g) := by
  dsimp only
  set off := 5 * t - 4 + g
  set a := i + 3 * r + k - off
  set s := t - 2
  have hs3 : 3 ≤ s := by omega
  have ht_eq : t - 1 = s + 1 := by omega
  have hoff_lt : off < k := by omega
  have h5t_lt : 5 * t - 6 < k := by omega
  have hkey1 := (flipOff k i r off hkpos key).isLt
  have hkey2 := key.isLt
  have hagree : ∀ d, 1 ≤ d → d ≤ 5 * t - 6 →
      bit k (flipOff k i r off hkpos key).val (a + d) = bit k key.val (a + d) := by
    intro d hd1 hd2
    unfold flipOff
    rw [show i + 3 * r + k - off = a from rfl, bit_flipBit]
    have hne : a % k ≠ (a + d) % k := by
      have h0 : a % k = (a + 0) % k := by simp
      rw [h0]
      exact mod_ne_of_diff (by omega) (by omega) a
    simp [hne]
  have hflip : bit k (flipOff k i r off hkpos key).val a = !(bit k key.val a) := by
    unfold flipOff
    rw [show i + 3 * r + k - off = a from rfl, bit_flipBit]
    simp
  have hb_eq : i + 3 * (r - t) + k - g = a + 2 * s := by omega
  have hz0 : bit k (stateAux k consts u (flipOff k i r off hkpos key).val (t - 1)) (a + 2 * s) =
      !(bit k (stateAux k consts u key.val (t - 1)) (a + 2 * s)) := by
    rw [ht_eq]
    exact stateAux_pivot (by omega) consts hu hkey1 hkey2 hs3 a
      (fun d hd1 hd2 => hagree d hd1 (by omega)) hflip
  have hlo1 : leftOff (s + 1) = 2 * s := by unfold leftOff; omega
  have hz1 : bit k (stateAux k consts u (flipOff k i r off hkpos key).val (t - 1)) (a + 2 * s + 1) =
      bit k (stateAux k consts u key.val (t - 1)) (a + 2 * s + 1) := by
    rw [ht_eq, show a + 2 * s + 1 = (a + 1) + leftOff (s + 1) by omega]
    apply stateAux_cone (by omega) consts hu hkey1 hkey2 (s + 1) (a + 1)
    intro d hd
    rw [show a + 1 + d = a + (1 + d) by omega]
    exact hagree (1 + d) (by omega) (by omega)
  have hz2 : bit k (stateAux k consts u (flipOff k i r off hkpos key).val (t - 1)) (a + 2 * s + 2) =
      bit k (stateAux k consts u key.val (t - 1)) (a + 2 * s + 2) := by
    rw [ht_eq, show a + 2 * s + 2 = (a + 2) + leftOff (s + 1) by omega]
    apply stateAux_cone (by omega) consts hu hkey1 hkey2 (s + 1) (a + 2)
    intro d hd
    rw [show a + 2 + d = a + (2 + d) by omega]
    exact hagree (2 + d) (by omega) (by omega)
  unfold guard
  dsimp only
  rw [hb_eq, hz0, hz1, hz2]
  cases bit k (stateAux k consts u key.val (t - 1)) (a + 2 * s) <;>
    cases bit k (stateAux k consts u key.val (t - 1)) (a + 2 * s + 1) <;>
    cases bit k (stateAux k consts u key.val (t - 1)) (a + 2 * s + 2) <;>
    decide

lemma guard_flip_above {k r e q u i : Nat} (consts : Nat → Fin (2 ^ k))
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r) (hu : u < 2 ^ k)
    (hkpos : 0 < k)
    {t g x : Nat} (ht1 : e + q + 4 ≤ t) (ht2 : t ≤ r - e) (hg : g ≤ 4 * (r - t))
    (hx1 : 5 * t - 4 + g + 1 ≤ x) (hx2 : x < k)
    (key : Fin (2 ^ k)) :
    guard k r consts u i (flipOff k i r x hkpos key).val t g =
      guard k r consts u i key.val t g := by
  set off := 5 * t - 4 + g
  set a := i + 3 * r + k - off
  set p := i + 3 * r + k - x
  set s := t - 2
  have ht_eq : t - 1 = s + 1 := by omega
  have hlo1 : leftOff (s + 1) = 2 * s := by unfold leftOff; omega
  have hkey1 := (flipOff k i r x hkpos key).isLt
  have hkey2 := key.isLt
  have hagree : ∀ d ≤ 5 * t - 6,
      bit k (flipOff k i r x hkpos key).val (a + d) = bit k key.val (a + d) := by
    intro d hd
    unfold flipOff
    rw [show i + 3 * r + k - x = p from rfl, bit_flipBit]
    have hne : p % k ≠ (a + d) % k := by
      have h0 : p % k = (p + 0) % k := by simp
      have ha : a + d = p + (x - off + d) := by omega
      rw [h0, ha]
      exact mod_ne_of_diff (by omega) (by omega) p
    simp [hne]
  have hb_eq : i + 3 * (r - t) + k - g = a + 2 * s := by omega
  have hz : ∀ j ≤ 2,
      bit k (stateAux k consts u (flipOff k i r x hkpos key).val (t - 1)) (a + 2 * s + j) =
        bit k (stateAux k consts u key.val (t - 1)) (a + 2 * s + j) := by
    intro j hj
    rw [ht_eq, show a + 2 * s + j = (a + j) + leftOff (s + 1) by omega]
    apply stateAux_cone (by omega) consts hu hkey1 hkey2 (s + 1) (a + j)
    intro d hd
    rw [show a + j + d = a + (j + d) by omega]
    exact hagree (j + d) (by omega)
  unfold guard
  dsimp only
  rw [hb_eq, show a + 2 * s = a + 2 * s + 0 by omega, hz 0 (by omega),
    show a + 2 * s + 0 + 1 = a + 2 * s + 1 by omega, hz 1 (by omega),
    show a + 2 * s + 0 + 2 = a + 2 * s + 2 by omega, hz 2 (by omega)]

lemma maxSat_le (p : Nat → Bool) (m : Nat) : maxSat p m ≤ m := by
  induction m with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
    simp only [maxSat]
    split
    · exact Nat.le_refl _
    · exact Nat.le_trans ih (Nat.le_succ m)

lemma maxSat_spec (p : Nat → Bool) (m : Nat) :
    (∃ x ≤ m, p x = true) →
      p (maxSat p m) = true ∧
      (∀ x ≤ m, p x = true → x ≤ maxSat p m) := by
  induction m with
  | zero =>
    rintro ⟨x, hx, hpx⟩
    have hx0 : x = 0 := by omega
    subst hx0
    exact ⟨hpx, fun y hy _ => by omega⟩
  | succ m ih =>
    rintro ⟨x, hx, hpx⟩
    simp only [maxSat]
    by_cases htop : p (m + 1) = true
    · simp only [htop, ↓reduceIte]
      exact ⟨trivial, fun y hy _ => hy⟩
    · simp only [htop, ↓reduceIte]
      have hxm : x ≤ m := by
        by_contra h
        have hxe : x = m + 1 := by omega
        subst hxe
        exact htop hpx
      rcases ih ⟨x, hxm, hpx⟩ with ⟨hp, hmax⟩
      refine ⟨hp, fun y hy hpy => ?_⟩
      have hym : y ≤ m := by
        by_contra h
        have hye : y = m + 1 := by omega
        subst hye
        exact htop hpy
      exact hmax y hym hpy

lemma wave_history {k r e q u i : Nat} (consts : Nat → Fin (2 ^ k))
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r)
    (hu : u < 2 ^ k) (hi : i < k)
    (base : Fin (2 ^ k)) (mask : Fin (2 ^ q))
    (hdiff : (preWord k consts u base.val r).testBit i ≠
      (preWord k consts u (base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val) r).testBit i) :
    let cut := e + q + 3
    ∃ d : Nat → Nat,
      (∀ t, cut ≤ t → t ≤ r → d t < e + q ∧ d t ≤ 4 * (r - t)) ∧
      (∀ t, cut < t → t ≤ r → d t ≤ d (t - 1)) ∧
      ∀ t, cut < t → t ≤ r - e →
        (∀ s, cut ≤ s → s < t → s + d s < t + d t) →
        guard k r consts u i base.val t (d t) = false := by
  dsimp only
  set cut := e + q + 3
  set smask := i + 3 * r + k - e - q
  set key1 := base.val
  set key2 := base.val ^^^ rot k smask mask.val
  have hk1 : key1 < 2 ^ k := base.isLt
  have hk2 : key2 < 2 ^ k := Nat.xor_lt_two_pow base.isLt (rot_lt k smask mask.val)
  have hmask_lt : mask.val < 2 ^ k :=
    Nat.lt_of_lt_of_le mask.isLt (Nat.pow_le_pow_right (by omega) (by omega))
  have hkey_agree_window : ∀ Δ, q ≤ Δ → Δ < k →
      bit k key1 (smask + Δ) = bit k key2 (smask + Δ) := by
    intro Δ hqΔ hΔk
    dsimp only [key2]
    rw [bit_xor, Nat.add_comm smask Δ, bit_rot_any (by omega) hmask_lt]
    have hmb : bit k mask.val Δ = false := by
      unfold bit
      rw [Nat.mod_eq_of_lt hΔk]
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le mask.isLt (Nat.pow_le_pow_right (by omega) hqΔ))
    rw [hmb, Bool.xor_false, Nat.add_comm Δ smask]
  let wpos := fun t δ => i + 3 * (r - t) + k - δ
  let diffBit := fun t δ =>
    decide (bit k (wave k r consts u key1 t) (wpos t δ) ≠
      bit k (wave k r consts u key2 t) (wpos t δ))
  have hkey_inj : ∀ t δ, cut ≤ t → t < r → δ ≤ 4 * (r - t) →
      bit k (rot k (2 * (t - 1)) key1) (wpos t δ) =
        bit k (rot k (2 * (t - 1)) key2) (wpos t δ) := by
    intro t δ hct htr hδ
    let Δ := k + e + q - (5 * t - 2 + δ)
    have hqΔ : q ≤ Δ := by omega
    have hΔk : Δ < k := by omega
    have hsum : (smask + Δ) + 2 * (t - 1) = wpos t δ + k := by
      dsimp only [smask, Δ, wpos]; omega
    rw [← bit_add_k k _ (wpos t δ), ← bit_add_k k _ (wpos t δ), ← hsum,
      bit_rot_any (by omega) hk1, bit_rot_any (by omega) hk2]
    exact hkey_agree_window Δ hqΔ hΔk
  have hpre_of_wave : ∀ t δ, cut ≤ t → t ≤ r → δ ≤ 4 * (r - t) →
      diffBit t δ = true →
      bit k (preWord k consts u key1 t) (wpos t δ) ≠
        bit k (preWord k consts u key2 t) (wpos t δ) := by
    intro t δ hct htr hδ hdb
    have hne : bit k (wave k r consts u key1 t) (wpos t δ) ≠
        bit k (wave k r consts u key2 t) (wpos t δ) := of_decide_eq_true hdb
    by_cases hlt : t < r
    · simp only [wave, hlt, ↓reduceIte] at hne
      have ht_eq : t = (t - 1) + 1 := by omega
      have hst1 : stateAux k consts u key1 t =
          step k (mix k (stateAux k consts u key1 (t - 1))) ^^^
            rot k (2 * (t - 1)) key1 ^^^ (consts ((t - 1) + 1)).val := by
        conv_lhs => rw [ht_eq]
        exact stateAux_succ k consts u key1 (t - 1)
      have hst2 : stateAux k consts u key2 t =
          step k (mix k (stateAux k consts u key2 (t - 1))) ^^^
            rot k (2 * (t - 1)) key2 ^^^ (consts ((t - 1) + 1)).val := by
        conv_lhs => rw [ht_eq]
        exact stateAux_succ k consts u key2 (t - 1)
      rw [hst1, hst2, bit_xor, bit_xor, bit_xor, bit_xor] at hne
      have hki := hkey_inj t δ hct hlt hδ
      intro hpeq
      apply hne
      unfold preWord at hpeq
      rw [hpeq, hki]
    · have hte : t = r := by omega
      subst hte
      simp only [wave, Nat.lt_irrefl, ↓reduceIte] at hne
      exact hne
  have hupper : ∀ t δ, cut ≤ t → t < r → e + q ≤ δ → δ ≤ 4 * (r - t) →
      diffBit t δ = false := by
    intro t δ hct htr hδ1 hδ2
    apply decide_eq_false
    intro hne
    apply hne
    simp only [wave, htr, ↓reduceIte]
    let Δ := k + e + q - (5 * t - 2 + δ)
    have hlo : leftOff t = 2 * t - 2 := by unfold leftOff; omega
    have hpos : (smask + Δ) + leftOff t = wpos t δ + k := by
      dsimp only [smask, Δ, wpos]; omega
    rw [← bit_add_k k _ (wpos t δ), ← bit_add_k k _ (wpos t δ), ← hpos]
    apply stateAux_cone (by omega) consts hu hk1 hk2 t (smask + Δ)
    intro d hd
    rw [show smask + Δ + d = smask + (Δ + d) by omega]
    exact hkey_agree_window (Δ + d) (by omega) (by omega)
  have hstep_back : ∀ t δ, cut < t → t ≤ r → δ ≤ 4 * (r - t) → diffBit t δ = true →
      ∃ δ', δ ≤ δ' ∧ δ' ≤ δ + 4 ∧ diffBit (t - 1) δ' = true := by
    intro t δ hct htr hδ hdb
    have hpre := hpre_of_wave t δ (by omega) htr hδ hdb
    unfold preWord at hpre
    let n := wpos (t - 1) (δ + 4)
    have hn : wpos t δ = n + 1 := by dsimp only [n, wpos]; omega
    rw [hn] at hpre
    have htm1 : t - 1 < r := by omega
    by_contra hnone
    have hall : ∀ j ≤ 4,
        bit k (stateAux k consts u key1 (t - 1)) (n + j) =
          bit k (stateAux k consts u key2 (t - 1)) (n + j) := by
      intro j hj
      have hnj : n + j = wpos (t - 1) (δ + 4 - j) := by dsimp only [n, wpos]; omega
      rw [hnj]
      by_contra hneq
      apply hnone
      refine ⟨δ + 4 - j, by omega, by omega, ?_⟩
      dsimp only [diffBit]
      simp only [wave, htm1, ↓reduceIte]
      exact decide_eq_true hneq
    exact hpre (bit_step_mix_eq (by omega)
      (stateAux_lt consts hu key1 (t - 1)) (stateAux_lt consts hu key2 (t - 1)) n
      (by simpa using hall 0 (by omega))
      (hall 1 (by omega))
      (hall 2 (by omega))
      (hall 3 (by omega))
      (hall 4 (by omega)))
  have hex : ∀ j ≤ r - cut, ∃ δ ≤ 4 * (r - (r - j)), diffBit (r - j) δ = true := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨0, by omega, ?_⟩
      dsimp only [diffBit, wpos]
      simp only [Nat.sub_self, Nat.sub_zero, wave, Nat.lt_irrefl, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
      apply decide_eq_true
      unfold bit
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hi]
      exact hdiff
    | succ j ih =>
      intro hj
      rcases ih (by omega) with ⟨δ, hδ, hdb⟩
      have hgt : cut < r - j := by omega
      rcases hstep_back (r - j) δ hgt (by omega) hδ hdb with ⟨δ', _, hδ2, hdb'⟩
      have heq : r - j - 1 = r - (j + 1) := by omega
      rw [heq] at hdb'
      exact ⟨δ', by omega, hdb'⟩
  let d := fun t => maxSat (diffBit t) (4 * (r - t))
  have hd_spec : ∀ t, cut ≤ t → t ≤ r →
      diffBit t (d t) = true ∧ (∀ x ≤ 4 * (r - t), diffBit t x = true → x ≤ d t) := by
    intro t hct htr
    have hj : r - (r - t) = t := by omega
    have h1 := hex (r - t) (by omega)
    rw [hj] at h1
    exact maxSat_spec (diffBit t) (4 * (r - t)) h1
  refine ⟨d, ?_, ?_, ?_⟩
  · intro t hct htr
    have hle : d t ≤ 4 * (r - t) := maxSat_le _ _
    refine ⟨?_, hle⟩
    by_cases hlt : t < r
    · by_contra hge
      have hfalse := hupper t (d t) hct hlt (by omega) hle
      have htrue := (hd_spec t hct htr).1
      rw [hfalse] at htrue
      exact Bool.noConfusion htrue
    · omega
  · intro t hct htr
    have hle : d t ≤ 4 * (r - t) := maxSat_le _ _
    have htrue := (hd_spec t (by omega) htr).1
    rcases hstep_back t (d t) hct htr hle htrue with ⟨δ', hδ1, hδ2, hdb'⟩
    have hmax := (hd_spec (t - 1) (by omega) (by omega)).2 δ' (by omega) hdb'
    omega
  · intro t hct htre hrec
    have htr : t ≤ r := by omega
    have hle : d t ≤ 4 * (r - t) := maxSat_le _ _
    have hrec1 : (t - 1) + d (t - 1) < t + d t := hrec (t - 1) (by omega) (by omega)
    have hpre := hpre_of_wave t (d t) (by omega) htr hle (hd_spec t (by omega) htr).1
    unfold preWord at hpre
    let n := wpos (t - 1) (d t + 4)
    have hn : wpos t (d t) = n + 1 := by dsimp only [n, wpos]; omega
    rw [hn] at hpre
    have htm1 : t - 1 < r := by omega
    have hagree : ∀ j ≤ 3,
        bit k (stateAux k consts u key1 (t - 1)) (n + j) =
          bit k (stateAux k consts u key2 (t - 1)) (n + j) := by
      intro j hj
      have hnj : n + j = wpos (t - 1) (d t + 4 - j) := by dsimp only [n, wpos]; omega
      rw [hnj]
      by_contra hneq
      have hdb' : diffBit (t - 1) (d t + 4 - j) = true := by
        dsimp only [diffBit]
        simp only [wave, htm1, ↓reduceIte]
        exact decide_eq_true hneq
      have hmax := (hd_spec (t - 1) (by omega) (by omega)).2 (d t + 4 - j) (by omega) hdb'
      omega
    have hforced := bit_step_mix_forced (by omega)
      (stateAux_lt consts hu key1 (t - 1)) (stateAux_lt consts hu key2 (t - 1)) n
      (by simpa using hagree 0 (by omega))
      (hagree 1 (by omega))
      (hagree 2 (by omega))
      (hagree 3 (by omega))
      hpre
    unfold guard
    dsimp only
    rw [show i + 3 * (r - t) + k - d t = n + 1 by exact hn]
    exact hforced

lemma crossing_exists {cut tEnd : Nat} (d : Nat → Nat)
    (hdec : ∀ t, cut < t → t ≤ tEnd → d t ≤ d (t - 1))
    {L : Nat} (hlo : cut + d cut < L) (hhi : L ≤ tEnd + d tEnd) (hct : cut ≤ tEnd) :
    ∃ t, cut < t ∧ t ≤ tEnd ∧ t + d t = L ∧ (∀ s, cut ≤ s → s < t → s + d s < L) := by
  have hex : ∃ t, cut ≤ t ∧ t ≤ tEnd ∧ L ≤ t + d t := ⟨tEnd, hct, Nat.le_refl _, hhi⟩
  set t0 := Nat.find hex
  have ht0_spec : cut ≤ t0 ∧ t0 ≤ tEnd ∧ L ≤ t0 + d t0 := Nat.find_spec hex
  have ht0_min : ∀ s < t0, ¬ (cut ≤ s ∧ s ≤ tEnd ∧ L ≤ s + d s) :=
    fun s hs => Nat.find_min hex hs
  have hgt : cut < t0 := by
    by_contra h
    have heq : t0 = cut := by omega
    rw [heq] at ht0_spec
    omega
  have hall : ∀ s, cut ≤ s → s < t0 → s + d s < L := by
    intro s hs1 hs2
    have hnot := ht0_min s hs2
    omega
  have hprev := hall (t0 - 1) (by omega) (by omega)
  have hd_step := hdec t0 hgt ht0_spec.2.1
  have hlt1 : cut ≤ t0 := ht0_spec.1
  have hlt2 : t0 ≤ tEnd := ht0_spec.2.1
  have hlt3 : L ≤ t0 + d t0 := ht0_spec.2.2
  refine ⟨t0, hgt, hlt2, ?_, hall⟩
  omega

lemma accepts_done (k r e q : Nat) (consts : Nat → Fin (2 ^ k)) (u i n t j key : Nat)
    (hdone : (r - e) - (e + q + 3) - (e + q - 1) + 1 ≤ j) :
    accepts k r e q consts u i n t j key = true := by
  unfold accepts
  dsimp only
  rw [if_pos hdone]

lemma accepts_zero_not_done (k r e q : Nat) (consts : Nat → Fin (2 ^ k)) (u i t j key : Nat)
    (hdone : ¬ ((r - e) - (e + q + 3) - (e + q - 1) + 1 ≤ j)) :
    accepts k r e q consts u i 0 t j key = false := by
  unfold accepts
  dsimp only
  rw [if_neg hdone]

lemma accepts_succ_legal (k r e q : Nat) (consts : Nat → Fin (2 ^ k)) (u i n t j key : Nat)
    (hdone : ¬ ((r - e) - (e + q + 3) - (e + q - 1) + 1 ≤ j))
    (hcond : t ≤ (e + q + 3) + (e + q - 1) + j ∧
      (e + q + 3) + (e + q - 1) + j - t ≤ e + q - 1 ∧
      (e + q + 3) + (e + q - 1) + j - t ≤ 4 * (r - t)) :
    accepts k r e q consts u i (n + 1) t j key =
      if guard k r consts u i key t ((e + q + 3) + (e + q - 1) + j - t) then
        accepts k r e q consts u i n (t + 1) j key
      else
        accepts k r e q consts u i n (t + 1) (j + 1) key := by
  conv_lhs => unfold accepts; dsimp only
  rw [if_neg hdone, if_pos hcond]

lemma accepts_succ_illegal (k r e q : Nat) (consts : Nat → Fin (2 ^ k)) (u i n t j key : Nat)
    (hdone : ¬ ((r - e) - (e + q + 3) - (e + q - 1) + 1 ≤ j))
    (hcond : ¬ (t ≤ (e + q + 3) + (e + q - 1) + j ∧
      (e + q + 3) + (e + q - 1) + j - t ≤ e + q - 1 ∧
      (e + q + 3) + (e + q - 1) + j - t ≤ 4 * (r - t))) :
    accepts k r e q consts u i (n + 1) t j key = false := by
  unfold accepts
  dsimp only
  rw [if_neg hdone, if_neg hcond]

lemma accepts_of_history {k r e q u i : Nat} (consts : Nat → Fin (2 ^ k))
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r)
    (key : Nat) (d : Nat → Nat)
    (h1 : ∀ t, e + q + 3 ≤ t → t ≤ r → d t < e + q ∧ d t ≤ 4 * (r - t))
    (h2 : ∀ t, e + q + 3 < t → t ≤ r → d t ≤ d (t - 1))
    (h3 : ∀ t, e + q + 3 < t → t ≤ r - e →
      (∀ s, e + q + 3 ≤ s → s < t → s + d s < t + d t) →
      guard k r consts u i key t (d t) = false) :
    let cut := e + q + 3
    let N := (r - e) - cut
    accepts k r e q consts u i N (cut + 1) 1 key = true := by
  dsimp only
  set cut := e + q + 3
  set D := e + q - 1
  set N := (r - e) - cut
  set m := N - D
  have hcross : ∀ j, 1 ≤ j → j ≤ m →
      ∃ tj, cut < tj ∧ tj ≤ r - e ∧ tj + d tj = cut + D + j ∧
        guard k r consts u i key tj (d tj) = false ∧
        d tj ≤ 4 * (r - tj) ∧
        (∀ s, cut ≤ s → s < tj → s + d s < cut + D + j) := by
    intro j hj1 hjm
    have hcut_d := (h1 cut (Nat.le_refl _) (by omega)).1
    rcases crossing_exists (tEnd := r - e) d (fun t h1t h2t => h2 t h1t (by omega))
      (L := cut + D + j) (by omega) (by omega) (by omega) with ⟨tj, hgt, hle, heq, hall⟩
    refine ⟨tj, hgt, hle, heq, ?_, (h1 tj (by omega) (by omega)).2, hall⟩
    apply h3 tj hgt hle
    intro s hs1 hs2
    rw [heq]
    exact hall s hs1 hs2
  have hstep : ∀ n t j,
      t + n = r - e + 1 → 1 ≤ j → j ≤ m + 1 → cut + j ≤ t →
      (∀ tj, cut < tj → tj ≤ r - e → tj + d tj = cut + D + j →
        (∀ s, cut ≤ s → s < tj → s + d s < cut + D + j) → t ≤ tj) →
      accepts k r e q consts u i n t j key = true := by
    intro n
    induction n with
    | zero =>
      intro t j htn hj1 hjm htj hinv
      by_cases hdone : m + 1 ≤ j
      · exact accepts_done k r e q consts u i 0 t j key hdone
      · rcases hcross j hj1 (by omega) with ⟨tj, hgt, hle, heq, _, _, hall⟩
        have htle := hinv tj hgt hle heq hall
        omega
    | succ n ih =>
      intro t j htn hj1 hjm htj hinv
      by_cases hdone : m + 1 ≤ j
      · exact accepts_done k r e q consts u i (n + 1) t j key hdone
      · rcases hcross j hj1 (by omega) with ⟨tj, hgt, hle, heq, hg0, hd4, hall⟩
        have htle := hinv tj hgt hle heq hall
        have hcond : t ≤ cut + D + j ∧ cut + D + j - t ≤ D ∧ cut + D + j - t ≤ 4 * (r - t) := by
          omega
        rw [accepts_succ_legal k r e q consts u i n t j key hdone hcond]
        by_cases hgv : guard k r consts u i key t (cut + D + j - t) = true
        · rw [if_pos hgv]
          apply ih (t + 1) j (by omega) hj1 hjm (by omega)
          intro tj' hgt' hle' heq' hall'
          have htjeq : tj' = tj := by
            by_contra hne
            rcases Nat.lt_or_gt_of_ne hne with hlt | hgt2
            · have := hall tj' (by omega) hlt; omega
            · have := hall' tj (by omega) hgt2; omega
          by_contra hnot
          have ht_eq : t = tj' := by omega
          have hdg : cut + D + j - tj' = d tj' := by omega
          rw [ht_eq, hdg, htjeq, hg0] at hgv
          exact Bool.noConfusion hgv
        · rw [if_neg hgv]
          apply ih (t + 1) (j + 1) (by omega) (by omega) (by omega) (by omega)
          intro tj' hgt' hle' heq' hall'
          have hlt : tj < tj' := by
            by_contra hge
            have hle2 : tj' ≤ tj := by omega
            by_cases he : tj' = tj
            · subst he; omega
            · have := hall tj' (by omega) (by omega); omega
          omega
  apply hstep N (cut + 1) 1 (by omega) (by omega) (by omega) (by omega)
  intro tj hgt _ _ _
  omega

lemma binomTail_zero (n : Nat) : binomTail n 0 = 1 := by
  unfold binomTail
  simp

lemma binomTail_self (n : Nat) : binomTail n n = 2 ^ n :=
  Nat.sum_range_choose n

lemma binomTail_succ_succ (n d : Nat) :
    binomTail (n + 1) (d + 1) = binomTail n (d + 1) + binomTail n d := by
  unfold binomTail
  rw [Finset.sum_range_succ' (fun j => Nat.choose (n + 1) j) (d + 1)]
  simp only [Nat.choose_zero_right]
  have hsplit : ∑ j ∈ Finset.range (d + 1), Nat.choose (n + 1) (j + 1) =
      ∑ j ∈ Finset.range (d + 1), (Nat.choose n j + Nat.choose n (j + 1)) := by
    apply Finset.sum_congr rfl
    intro j _
    exact Nat.choose_succ_succ n j
  rw [hsplit, Finset.sum_add_distrib,
    Finset.sum_range_succ' (fun j => Nat.choose n j) (d + 1)]
  simp only [Nat.choose_zero_right]
  omega

lemma filter_half {k : Nat} (S : Finset (Fin (2 ^ k))) (f : Fin (2 ^ k) → Bool)
    (inv : Fin (2 ^ k) → Fin (2 ^ k))
    (hinvol : ∀ x, inv (inv x) = x)
    (hmem : ∀ x, inv x ∈ S ↔ x ∈ S)
    (hflip : ∀ x, f (inv x) = !(f x)) :
    (S.filter (fun x => f x = false)).card = (S.filter (fun x => f x = true)).card ∧
    2 * (S.filter (fun x => f x = false)).card = S.card := by
  have heq : (S.filter (fun x => f x = false)).card = (S.filter (fun x => f x = true)).card := by
    refine Finset.card_bij (fun x _ => inv x) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨(hmem x).mpr hx.1, by rw [hflip x, hx.2]; rfl⟩
    · intro x1 _ x2 _ h
      have h2 := congrArg inv h
      rw [hinvol, hinvol] at h2
      exact h2
    · intro y hy
      rw [Finset.mem_filter] at hy
      refine ⟨inv y, ?_, hinvol y⟩
      rw [Finset.mem_filter]
      exact ⟨(hmem y).mpr hy.1, by rw [hflip y, hy.2]; rfl⟩
  have hsum := Finset.card_filter_add_card_filter_not (s := S) (p := fun x => f x = false)
  have hnot : {a ∈ S | ¬ f a = false} = S.filter (fun x => f x = true) := by
    ext x
    simp only [Finset.mem_filter]
    cases f x <;> simp
  rw [hnot, ← heq] at hsum
  exact ⟨heq, by omega⟩

lemma card_accepts_le {k r e q u i : Nat} (consts : Nat → Fin (2 ^ k))
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r) (hu : u < 2 ^ k)
    (hkpos : 0 < k) :
    let cut := e + q + 3
    let D := e + q - 1
    let N := (r - e) - cut
    let m := N - D
    ∀ n t j M (S : Finset (Fin (2 ^ k))),
      n ≤ N →
      t + n = r - e + 1 →
      1 ≤ j →
      j ≤ m + 1 →
      cut + j ≤ t →
      M ≤ 4 * t + cut + D + j - 4 →
      S.card = 2 ^ (k - (N - n)) →
      (∀ x, M ≤ x → x < k → ∀ key : Fin (2 ^ k), flipOff k i r x hkpos key ∈ S ↔ key ∈ S) →
      (S.filter (fun key => accepts k r e q consts u i n t j key.val = true)).card ≤
        binomTail n (cut + D + j - t) * 2 ^ (k - N) := by
  dsimp only
  set cut := e + q + 3
  set D := e + q - 1
  set N := (r - e) - cut
  set m := N - D
  intro n
  induction n with
  | zero =>
    intro t j M S hn htn hj1 hjm htj hM hcard hinv
    by_cases hdone : m + 1 ≤ j
    · have hsub : S.filter (fun key => accepts k r e q consts u i 0 t j key.val = true) = S := by
        ext key
        simp only [Finset.mem_filter, accepts_done k r e q consts u i 0 t j key.val hdone, and_true]
      rw [hsub, hcard, show cut + D + j - t = 0 by omega, binomTail_zero]
      simp
    · have hemp : S.filter (fun key => accepts k r e q consts u i 0 t j key.val = true) = ∅ := by
        ext key
        simp only [Finset.mem_filter, Finset.notMem_empty,
          accepts_zero_not_done k r e q consts u i t j key.val hdone, Bool.false_eq_true, and_false]
      rw [hemp, Finset.card_empty]
      exact Nat.zero_le _
  | succ n ih =>
    intro t j M S hn htn hj1 hjm htj hM hcard hinv
    by_cases hdone : m + 1 ≤ j
    · have hsub : S.filter (fun key => accepts k r e q consts u i (n + 1) t j key.val = true) = S := by
        ext key
        simp only [Finset.mem_filter, accepts_done k r e q consts u i (n + 1) t j key.val hdone, and_true]
      rw [hsub, hcard, show cut + D + j - t = n + 1 by omega, binomTail_self]
      rw [← Nat.pow_add, show (n + 1) + (k - N) = k - (N - (n + 1)) by omega]
    · by_cases hcond : t ≤ cut + D + j ∧ cut + D + j - t ≤ D ∧ cut + D + j - t ≤ 4 * (r - t)
      · set g := cut + D + j - t
        set off := 5 * t - 4 + g
        have hoff_eq : off = 4 * t + cut + D + j - 4 := by omega
        have hoff_ge : M ≤ off := by omega
        have hoff_lt : off < k := by omega
        have ht1 : e + q + 4 ≤ t := by omega
        have ht2 : t ≤ r - e := by omega
        let f := fun key : Fin (2 ^ k) => guard k r consts u i key.val t g
        have hhalf := filter_half S f (flipOff k i r off hkpos)
          (flipOff_invol k i r off hkpos)
          (hinv off hoff_ge hoff_lt)
          (fun key => guard_flip_pivot consts hq hr hk hu hkpos ht1 ht2 hcond.2.2 key)
        set Sf := S.filter (fun key => f key = false)
        set St := S.filter (fun key => f key = true)
        have hpow : 2 ^ (k - (N - (n + 1))) = 2 * 2 ^ (k - (N - n)) := by
          have hexp : k - (N - (n + 1)) = (k - (N - n)) + 1 := by omega
          rw [hexp, Nat.pow_succ, Nat.mul_comm]
        have hSf_card : Sf.card = 2 ^ (k - (N - n)) := by omega
        have hSt_card : St.card = 2 ^ (k - (N - n)) := by omega
        have hSf_inv : ∀ x, off + 1 ≤ x → x < k →
            ∀ key : Fin (2 ^ k), flipOff k i r x hkpos key ∈ Sf ↔ key ∈ Sf := by
          intro x hx1 hx2 key
          simp only [Sf, Finset.mem_filter, f]
          rw [hinv x (by omega) hx2 key,
            guard_flip_above consts hq hr hk hu hkpos ht1 ht2 hcond.2.2 (by omega) hx2 key]
        have hSt_inv : ∀ x, off + 1 ≤ x → x < k →
            ∀ key : Fin (2 ^ k), flipOff k i r x hkpos key ∈ St ↔ key ∈ St := by
          intro x hx1 hx2 key
          simp only [St, Finset.mem_filter, f]
          rw [hinv x (by omega) hx2 key,
            guard_flip_above consts hq hr hk hu hkpos ht1 ht2 hcond.2.2 (by omega) hx2 key]
        have hunion :
            S.filter (fun key => accepts k r e q consts u i (n + 1) t j key.val = true) =
              Sf.filter (fun key => accepts k r e q consts u i n (t + 1) (j + 1) key.val = true) ∪
              St.filter (fun key => accepts k r e q consts u i n (t + 1) j key.val = true) := by
          ext key
          simp only [Finset.mem_union, Finset.mem_filter, Sf, St, f]
          constructor
          · rintro ⟨hkS, hacc⟩
            rw [accepts_succ_legal k r e q consts u i n t j key.val hdone hcond] at hacc
            cases hgv : guard k r consts u i key.val t g
            · left
              rw [show cut + D + j - t = g from rfl, hgv] at hacc
              exact ⟨⟨hkS, rfl⟩, hacc⟩
            · right
              rw [show cut + D + j - t = g from rfl, hgv] at hacc
              exact ⟨⟨hkS, rfl⟩, hacc⟩
          · rintro (⟨⟨hkS, hgv⟩, hacc⟩ | ⟨⟨hkS, hgv⟩, hacc⟩)
            · refine ⟨hkS, ?_⟩
              rw [accepts_succ_legal k r e q consts u i n t j key.val hdone hcond,
                show cut + D + j - t = g from rfl, hgv]
              exact hacc
            · refine ⟨hkS, ?_⟩
              rw [accepts_succ_legal k r e q consts u i n t j key.val hdone hcond,
                show cut + D + j - t = g from rfl, hgv]
              exact hacc
        have hle_sum :
            (S.filter (fun key => accepts k r e q consts u i (n + 1) t j key.val = true)).card ≤
              (Sf.filter (fun key => accepts k r e q consts u i n (t + 1) (j + 1) key.val = true)).card +
              (St.filter (fun key => accepts k r e q consts u i n (t + 1) j key.val = true)).card := by
          rw [hunion]
          exact Finset.card_union_le _ _
        have hbf := ih (t + 1) (j + 1) (off + 1) Sf (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) hSf_card hSf_inv
        rw [show cut + D + (j + 1) - (t + 1) = g by omega] at hbf
        by_cases hg0 : g = 0
        · have hSt_emp :
              St.filter (fun key => accepts k r e q consts u i n (t + 1) j key.val = true) = ∅ := by
            ext key
            simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
            intro _
            cases n with
            | zero =>
              rw [accepts_zero_not_done k r e q consts u i (t + 1) j key.val hdone]
              exact Bool.false_ne_true
            | succ n' =>
              have hnotc : ¬ (t + 1 ≤ cut + D + j ∧ cut + D + j - (t + 1) ≤ D ∧
                  cut + D + j - (t + 1) ≤ 4 * (r - (t + 1))) := by omega
              rw [accepts_succ_illegal k r e q consts u i n' (t + 1) j key.val hdone hnotc]
              exact Bool.false_ne_true
          rw [hSt_emp, Finset.card_empty, Nat.add_zero] at hle_sum
          rw [hg0, binomTail_zero] at hbf ⊢
          exact Nat.le_trans hle_sum hbf
        · have hbt := ih (t + 1) j (off + 1) St (by omega) (by omega) hj1 hjm
            (by omega) (by omega) hSt_card hSt_inv
          have hgm1 : cut + D + j - (t + 1) = g - 1 := by omega
          rw [hgm1] at hbt
          have hgsucc : g = (g - 1) + 1 := by omega
          calc
            (S.filter (fun key => accepts k r e q consts u i (n + 1) t j key.val = true)).card
                ≤ binomTail n g * 2 ^ (k - N) + binomTail n (g - 1) * 2 ^ (k - N) :=
              Nat.le_trans hle_sum (Nat.add_le_add hbf hbt)
            _ = (binomTail n g + binomTail n (g - 1)) * 2 ^ (k - N) :=
              (Nat.add_mul _ _ _).symm
            _ = binomTail (n + 1) g * 2 ^ (k - N) := by
              rw [hgsucc, binomTail_succ_succ, ← hgsucc]
      · have hemp : S.filter (fun key => accepts k r e q consts u i (n + 1) t j key.val = true) = ∅ := by
          ext key
          simp only [Finset.mem_filter, Finset.notMem_empty,
            accepts_succ_illegal k r e q consts u i n t j key.val hdone hcond,
            Bool.false_eq_true, and_false]
        rw [hemp, Finset.card_empty]
        exact Nat.zero_le _

end PEqualNP.Outside.L_meta_25530

theorem PEqualNP.Outside.L_meta_25530 : ∀ (k r e q : ℕ) (constants : ℕ → Fin (2 ^ k)) (u i : ℕ),
  0 < q → 3 * e + 2 * q + 3 ≤ r → k + e + 3 = 5 * r → u < 2 ^ k → i < k →
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
  let before := fun subject : ℕ =>
    let prev := state subject (r - 1)
    (step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev)).testBit i
  let N := (r - e) - (e + q + 3)
  let D := e + q - 1
  ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun base =>
    ∃ mask : Fin (2 ^ q),
      before base.val ≠ before (base.val ^^^ rot (i + 3 * r + k - e - q) mask.val))).card ≤
    (∑ j ∈ Finset.range (D + 1), Nat.choose N j) * 2 ^ (k - N) := by
  intro k r e q constants u i hq hr hk hu hi rot step state before N D
  have hsub :
      (Finset.univ : Finset (Fin (2 ^ k))).filter (fun base =>
        ∃ mask : Fin (2 ^ q),
          before base.val ≠ before (base.val ^^^ rot (i + 3 * r + k - e - q) mask.val)) ⊆
      (Finset.univ : Finset (Fin (2 ^ k))).filter (fun base =>
        PEqualNP.Outside.L_meta_25530.accepts k r e q constants u i N (e + q + 3 + 1) 1 base.val = true) := by
    intro base hmem
    rw [Finset.mem_filter] at hmem ⊢
    refine ⟨hmem.1, ?_⟩
    rcases hmem.2 with ⟨mask, hdiff⟩
    rcases PEqualNP.Outside.L_meta_25530.wave_history constants hq hr hk hu hi base mask hdiff with
      ⟨d, h1, h2, h3⟩
    exact PEqualNP.Outside.L_meta_25530.accepts_of_history constants hq hr base.val d h1 h2 h3
  have hbound := PEqualNP.Outside.L_meta_25530.card_accepts_le (i := i) constants hq hr hk hu
    (by omega) N (e + q + 3 + 1) 1 2 Finset.univ
    (Nat.le_refl N) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp [Finset.card_univ, Fintype.card_fin, N])
    (fun _ _ _ _ => by simp)
  rw [show e + q + 3 + D + 1 - (e + q + 3 + 1) = D by omega] at hbound
  exact Nat.le_trans (Finset.card_le_card hsub) hbound
