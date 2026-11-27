import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Card

namespace PEqualNP.Outside.L_meta_25519

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

def wpos (k r i t δ : Nat) : Nat :=
  i + 3 * (r - t) + k - δ

def leftOff (s : Nat) : Nat :=
  max (s + 1) (2 * s - 2)

def guard (k r : Nat) (c : Nat → Fin (2 ^ k)) (u i key t g : Nat) : Bool :=
  let z := stateAux k c u key (t - 1)
  let b := wpos k r i t g
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

def accepts {k : Nat} (G : Nat → Nat → Fin (2 ^ k) → Bool) :
    Nat → Nat → Nat → Fin (2 ^ k) → Bool
  | 0, _, _, _ => true
  | n + 1, t, g, key =>
    if n + 1 ≤ g then true
    else if G t g key then
      match g with
      | 0 => false
      | g' + 1 => accepts G n (t + 1) g' key
    else
      accepts G n (t + 1) g key

lemma xor_not_l (a b : Bool) : xor (!a) b = !(xor a b) := by cases a <;> cases b <;> rfl
lemma xor_not_r (a b : Bool) : xor a (!b) = !(xor a b) := by cases a <;> cases b <;> rfl

lemma xor_xor_cancel {a b c d : Bool} (h : xor (xor a b) d = xor (xor a c) d) : b = c := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

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

lemma bit_add_k (k w n : Nat) : bit k w (n + k) = bit k w n := by
  unfold bit; rw [Nat.add_mod_right]

lemma bit_rot {k s w : Nat} (hs : s < k) (hw : w < 2 ^ k) (n : Nat) :
    bit k (rot k s w) (n + s) = bit k w n := by
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) hs
  have hr : n % k < k := Nat.mod_lt n hk
  unfold bit rot
  rw [Nat.mod_eq_of_lt hs, Nat.testBit_mod_two_pow, Nat.testBit_or,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    decide_eq_true (Nat.mod_lt _ hk), Bool.true_and, ← Nat.mod_add_mod n k s]
  by_cases h : n % k + s < k
  · rw [Nat.mod_eq_of_lt h]
    have hhi : w.testBit (k - s + (n % k + s)) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hhi]
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have heq : k - s + (n % k + s - k) = n % k := by omega
    simp [heq, show ¬ s ≤ n % k + s - k by omega]

lemma bit_rot_any {k w : Nat} (hk : 0 < k) (hw : w < 2 ^ k) (s n : Nat) :
    bit k (rot k s w) (n + s) = bit k w n := by
  have hrot : rot k s w = rot k (s % k) w := by unfold rot; rw [Nat.mod_mod]
  have hmod : (n + s) % k = (n + s % k) % k := by
    rw [Nat.add_mod, Nat.add_mod n (s % k), Nat.mod_mod]
  unfold bit
  rw [hmod, hrot]
  exact bit_rot (Nat.mod_lt s hk) hw n

lemma bit_rotInv {k w : Nat} (hk : 0 < k) (hw : w < 2 ^ k) (s m : Nat) :
    bit k (rot k (k - s % k) w) m = bit k w (s + m) := by
  have hms : s % k < k := Nat.mod_lt s hk
  have hmod : (s + m + (k - s % k)) % k = m % k := by
    have h1 : s = k * (s / k) + s % k := (Nat.div_add_mod s k).symm
    have h2 : s + m + (k - s % k) = m + k * (s / k + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    rw [h2, Nat.add_mul_mod_self_left]
  have h := bit_rot_any hk hw (k - s % k) (s + m)
  unfold bit at h ⊢
  rw [hmod] at h
  exact h

lemma rot_rotInv {k w : Nat} (hk : 0 < k) (hw : w < 2 ^ k) (s : Nat) :
    rot k s (rot k (k - s % k) w) = w := by
  apply Nat.eq_of_testBit_eq
  intro n
  by_cases hn : n < k
  · have h1 : (rot k s (rot k (k - s % k) w)).testBit n =
        bit k (rot k s (rot k (k - s % k) w)) n := by
      unfold bit; rw [Nat.mod_eq_of_lt hn]
    have h2 : w.testBit n = bit k w n := by
      unfold bit; rw [Nat.mod_eq_of_lt hn]
    rw [h1, h2]
    have hms : s % k < k := Nat.mod_lt s hk
    have hmod : (n + (k - s % k) + s) % k = n % k := by
      have hdiv : s = k * (s / k) + s % k := (Nat.div_add_mod s k).symm
      have heq : n + (k - s % k) + s = n + k * (s / k + 1) := by
        rw [Nat.mul_add, Nat.mul_one]; omega
      rw [heq, Nat.add_mul_mod_self_left]
    have hrot := bit_rot_any hk (rot_lt k (k - s % k) w) s (n + (k - s % k))
    have hinv := bit_rotInv hk hw s (n + (k - s % k))
    have hmod2 : (s + (n + (k - s % k))) % k = n % k := by
      rw [show s + (n + (k - s % k)) = n + (k - s % k) + s by omega]; exact hmod
    unfold bit at hrot hinv ⊢
    rw [hmod] at hrot
    rw [hmod2] at hinv
    rw [hrot, hinv]
  · have hlt1 : rot k s (rot k (k - s % k) w) < 2 ^ n :=
      Nat.lt_of_lt_of_le (rot_lt k _ _) (Nat.pow_le_pow_right (by decide) (by omega))
    have hlt2 : w < 2 ^ n :=
      Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_lt_two_pow hlt1, Nat.testBit_lt_two_pow hlt2]

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
    (n : Nat) (h : ∀ j ≤ 4, bit k w1 (n + j) = bit k w2 (n + j)) :
    bit k (step k (mix k w1)) (n + 1) = bit k (step k (mix k w2)) (n + 1) := by
  have hk0 : 0 < k := Nat.lt_of_lt_of_le (by decide) hk
  rw [bit_step hk0, bit_step hk0]
  have h0 : bit k w1 n = bit k w2 n := by simpa using h 0 (by decide)
  have hm0 : bit k (mix k w1) (n + 1) = bit k (mix k w2) (n + 1) := by
    rw [bit_mix hk hw1 n, bit_mix hk hw2 n, h0, h 1 (by decide), h 2 (by decide)]
  have hm1 : bit k (mix k w1) (n + 1 + 1) = bit k (mix k w2) (n + 1 + 1) := by
    rw [bit_mix hk hw1 (n + 1), bit_mix hk hw2 (n + 1), h 1 (by decide), h 2 (by decide), h 3 (by decide)]
  have hm2 : bit k (mix k w1) (n + 1 + 2) = bit k (mix k w2) (n + 1 + 2) := by
    change bit k (mix k w1) ((n + 2) + 1) = bit k (mix k w2) ((n + 2) + 1)
    rw [bit_mix hk hw1 (n + 2), bit_mix hk hw2 (n + 2), h 2 (by decide), h 3 (by decide), h 4 (by decide)]
  rw [hm0, hm1, hm2]

lemma bit_step_mix_forced {k w1 w2 : Nat} (hk : 2 ≤ k) (hw1 : w1 < 2 ^ k) (hw2 : w2 < 2 ^ k)
    (n : Nat) (h : ∀ j ≤ 3, bit k w1 (n + j) = bit k w2 (n + j))
    (hne : bit k (step k (mix k w1)) (n + 1) ≠ bit k (step k (mix k w2)) (n + 1)) :
    xor (xor (bit k w1 (n + 1)) (bit k w1 (n + 2))) (bit k w1 (n + 3)) = false := by
  have hk0 : 0 < k := Nat.lt_of_lt_of_le (by decide) hk
  rw [bit_step hk0, bit_step hk0] at hne
  have h0 : bit k w1 n = bit k w2 n := by simpa using h 0 (by decide)
  have hm0 : bit k (mix k w1) (n + 1) = bit k (mix k w2) (n + 1) := by
    rw [bit_mix hk hw1 n, bit_mix hk hw2 n, h0, h 1 (by decide), h 2 (by decide)]
  have hm1 : bit k (mix k w1) (n + 1 + 1) = bit k (mix k w2) (n + 1 + 1) := by
    rw [bit_mix hk hw1 (n + 1), bit_mix hk hw2 (n + 1), h 1 (by decide), h 2 (by decide), h 3 (by decide)]
  have hb : bit k (mix k w1) (n + 1 + 1) = false := by
    cases hval : bit k (mix k w1) (n + 1 + 1) with
    | false => rfl
    | true =>
      exfalso; apply hne
      rw [← hm0, ← hm1, hval]; simp [chi]
  rw [bit_mix hk hw1 (n + 1), Bool.xor_comm (bit k w1 (n + 2)) (bit k w1 (n + 1))] at hb
  exact hb

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

lemma leftOff_zero : leftOff 0 = 1 := rfl
lemma leftOff_ge3 {s : Nat} (hs : 3 ≤ s) : leftOff s = 2 * s - 2 := by unfold leftOff; omega
lemma leftOff_step_rot (s : Nat) : 2 * s ≤ leftOff (s + 1) := by unfold leftOff; omega
lemma leftOff_step_prev (s : Nat) : leftOff s + 1 ≤ leftOff (s + 1) := by unfold leftOff; omega

lemma stateAux_cone {k u : Nat} (hk : 2 ≤ k) (consts : Nat → Fin (2 ^ k)) (hu : u < 2 ^ k)
    {key1 key2 : Nat} (hk1 : key1 < 2 ^ k) (hk2 : key2 < 2 ^ k) :
    ∀ s a, (∀ d < leftOff s + 3 * s, bit k key1 (a + d) = bit k key2 (a + d)) →
      bit k (stateAux k consts u key1 s) (a + leftOff s) =
        bit k (stateAux k consts u key2 s) (a + leftOff s) := by
  have hk0 : 0 < k := Nat.lt_of_lt_of_le (by decide) hk
  intro s
  induction s with
  | zero =>
    intro a h
    rw [stateAux_zero, stateAux_zero, bit_xor, bit_xor, leftOff_zero,
      bit_rot (by omega) hk1 a, bit_rot (by omega) hk2 a]
    simpa using congrArg (xor · (bit k u (a + 1))) (h 0 (by decide))
  | succ s ih =>
    intro a h
    rw [stateAux_succ, stateAux_succ, bit_xor, bit_xor, bit_xor, bit_xor]
    have hge : 2 * s ≤ leftOff (s + 1) := leftOff_step_rot s
    have hge1 : leftOff s + 1 ≤ leftOff (s + 1) := leftOff_step_prev s
    obtain ⟨dr, hdr⟩ : ∃ dr, leftOff (s + 1) = dr + 2 * s := ⟨leftOff (s + 1) - 2 * s, by omega⟩
    obtain ⟨δ, hδ⟩ : ∃ δ, leftOff (s + 1) = δ + leftOff s + 1 :=
      ⟨leftOff (s + 1) - (leftOff s + 1), by omega⟩
    have hrot_eq : bit k (rot k (2 * s) key1) (a + leftOff (s + 1)) =
        bit k (rot k (2 * s) key2) (a + leftOff (s + 1)) := by
      rw [hdr, ← Nat.add_assoc, bit_rot_any hk0 hk1, bit_rot_any hk0 hk2]
      exact h dr (by omega)
    have hstep_eq : bit k (step k (mix k (stateAux k consts u key1 s))) (a + leftOff (s + 1)) =
        bit k (step k (mix k (stateAux k consts u key2 s))) (a + leftOff (s + 1)) := by
      rw [hδ, show a + (δ + leftOff s + 1) = (a + δ + leftOff s) + 1 by omega]
      apply bit_step_mix_eq hk (stateAux_lt consts hu key1 s) (stateAux_lt consts hu key2 s)
      intro j hj
      rw [show a + δ + leftOff s + j = (a + δ + j) + leftOff s by omega]
      apply ih (a + δ + j)
      intro d hd
      rw [show a + δ + j + d = a + (δ + j + d) by omega]
      exact h (δ + j + d) (by omega)
    rw [hstep_eq, hrot_eq]

lemma stateAux_pivot {k u : Nat} (hk : 2 ≤ k) (consts : Nat → Fin (2 ^ k)) (hu : u < 2 ^ k)
    {key1 key2 : Nat} (hk1 : key1 < 2 ^ k) (hk2 : key2 < 2 ^ k)
    {s : Nat} (hs : 3 ≤ s) (a : Nat)
    (hagree : ∀ d, 1 ≤ d → d ≤ 5 * s + 2 → bit k key1 (a + d) = bit k key2 (a + d))
    (hflip : bit k key1 a = !(bit k key2 a)) :
    bit k (stateAux k consts u key1 (s + 1)) (a + 2 * s) =
      !(bit k (stateAux k consts u key2 (s + 1)) (a + 2 * s)) := by
  have hk0 : 0 < k := Nat.lt_of_lt_of_le (by decide) hk
  rw [stateAux_succ, stateAux_succ, bit_xor, bit_xor, bit_xor, bit_xor]
  have hlo : leftOff s = 2 * s - 2 := leftOff_ge3 hs
  have hstep_eq : bit k (step k (mix k (stateAux k consts u key1 s))) (a + 2 * s) =
      bit k (step k (mix k (stateAux k consts u key2 s))) (a + 2 * s) := by
    rw [show a + 2 * s = (a + 1 + leftOff s) + 1 by omega]
    apply bit_step_mix_eq hk (stateAux_lt consts hu key1 s) (stateAux_lt consts hu key2 s)
    intro j hj
    rw [show a + 1 + leftOff s + j = (a + 1 + j) + leftOff s by omega]
    apply stateAux_cone hk consts hu hk1 hk2 s (a + 1 + j)
    intro d hd
    rw [show a + 1 + j + d = a + (1 + j + d) by omega]
    exact hagree (1 + j + d) (by omega) (by omega)
  have hrot : bit k (rot k (2 * s) key1) (a + 2 * s) = !(bit k (rot k (2 * s) key2) (a + 2 * s)) := by
    rw [bit_rot_any hk0 hk1, bit_rot_any hk0 hk2, hflip]
  rw [hstep_eq, hrot, xor_not_r, xor_not_l]

lemma flipOff_bit_ne {k i r x n : Nat} (hkpos : 0 < k)
    (h1 : i + 3 * r + k - x < n) (h2 : n - (i + 3 * r + k - x) < k) (key : Fin (2 ^ k)) :
    bit k (flipOff k i r x hkpos key).val n = bit k key.val n := by
  unfold flipOff
  rw [bit_flipBit]
  generalize hp : i + 3 * r + k - x = p at h1 h2 ⊢
  have hne : p % k ≠ n % k := by
    have h0 : p % k = (p + 0) % k := by simp
    rw [h0, show n = p + (n - p) by omega]
    exact mod_ne_of_diff (by omega) (by omega) p
  simp [hne]

lemma wpos_eq_pivot {k r i s g : Nat} (htr : s + 2 ≤ r) (hoff : 5 * s + 6 + g < k) :
    wpos k r i (s + 2) g = (i + 3 * r + k - (5 * s + 6 + g)) + 2 * s := by
  obtain ⟨rm, rfl⟩ : ∃ rm, r = s + 2 + rm := ⟨r - (s + 2), by omega⟩
  unfold wpos; omega

lemma guard_flip_pivot {k r u i : Nat} (consts : Nat → Fin (2 ^ k))
    (hk2 : 2 ≤ k) (hu : u < 2 ^ k) (hkpos : 0 < k)
    {t g : Nat} (ht5 : 5 ≤ t) (htr : t ≤ r) (hoff_lt : 5 * t - 4 + g < k)
    (key : Fin (2 ^ k)) :
    guard k r consts u i (flipOff k i r (5 * t - 4 + g) hkpos key).val t g =
      !(guard k r consts u i key.val t g) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  have hs3 : 3 ≤ s := by omega
  have hoff_eq : 5 * (s + 2) - 4 + g = 5 * s + 6 + g := by omega
  rw [hoff_eq] at hoff_lt ⊢
  have hba : wpos k r i (s + 2) g = (i + 3 * r + k - (5 * s + 6 + g)) + 2 * s :=
    wpos_eq_pivot htr hoff_lt
  have hlo1 : leftOff (s + 1) = 2 * s := leftOff_ge3 (by omega)
  have hkey1 := (flipOff k i r (5 * s + 6 + g) hkpos key).isLt
  have hkey2 := key.isLt
  generalize ha : i + 3 * r + k - (5 * s + 6 + g) = a at hba
  have hagree : ∀ d, 1 ≤ d → d ≤ 5 * s + 4 →
      bit k (flipOff k i r (5 * s + 6 + g) hkpos key).val (a + d) = bit k key.val (a + d) :=
    fun d hd1 hd2 => flipOff_bit_ne hkpos (by omega) (by omega) key
  have hflip : bit k (flipOff k i r (5 * s + 6 + g) hkpos key).val a = !(bit k key.val a) := by
    unfold flipOff; rw [bit_flipBit, ha]; simp
  have hz0 : bit k (stateAux k consts u (flipOff k i r (5 * s + 6 + g) hkpos key).val (s + 1)) (a + 2 * s) =
      !(bit k (stateAux k consts u key.val (s + 1)) (a + 2 * s)) :=
    stateAux_pivot hk2 consts hu hkey1 hkey2 hs3 a (fun d h1 h2 => hagree d h1 (by omega)) hflip
  have hz12 : ∀ j, 1 ≤ j → j ≤ 2 →
      bit k (stateAux k consts u (flipOff k i r (5 * s + 6 + g) hkpos key).val (s + 1)) (a + 2 * s + j) =
        bit k (stateAux k consts u key.val (s + 1)) (a + 2 * s + j) := by
    intro j hj1 hj2
    rw [show a + 2 * s + j = (a + j) + leftOff (s + 1) by omega]
    apply stateAux_cone hk2 consts hu hkey1 hkey2 (s + 1) (a + j)
    intro d hd
    rw [show a + j + d = a + (j + d) by omega]
    exact hagree (j + d) (by omega) (by omega)
  unfold guard; dsimp only
  rw [show s + 2 - 1 = s + 1 by omega, hba, hz0, hz12 1 (by decide) (by decide),
    hz12 2 (by decide) (by decide), xor_not_l, xor_not_l]

lemma guard_flip_above {k r u i : Nat} (consts : Nat → Fin (2 ^ k))
    (hk2 : 2 ≤ k) (hu : u < 2 ^ k) (hkpos : 0 < k)
    {t g x : Nat} (ht5 : 5 ≤ t) (htr : t ≤ r)
    (hx1 : 5 * t - 4 + g + 1 ≤ x) (hx2 : x < k)
    (key : Fin (2 ^ k)) :
    guard k r consts u i (flipOff k i r x hkpos key).val t g =
      guard k r consts u i key.val t g := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
  have hs3 : 3 ≤ s := by omega
  have hx1' : 5 * s + 6 + g + 1 ≤ x := by omega
  have hba : wpos k r i (s + 2) g = (i + 3 * r + k - (5 * s + 6 + g)) + 2 * s :=
    wpos_eq_pivot htr (by omega)
  have hlo1 : leftOff (s + 1) = 2 * s := leftOff_ge3 (by omega)
  have hkey1 := (flipOff k i r x hkpos key).isLt
  have hkey2 := key.isLt
  generalize ha : i + 3 * r + k - (5 * s + 6 + g) = a at hba
  have hgap : i + 3 * r + k - x + (x - (5 * s + 6 + g)) = a := by omega
  have hz : ∀ j ≤ 2,
      bit k (stateAux k consts u (flipOff k i r x hkpos key).val (s + 1)) (a + 2 * s + j) =
        bit k (stateAux k consts u key.val (s + 1)) (a + 2 * s + j) := by
    intro j hj
    rw [show a + 2 * s + j = (a + j) + leftOff (s + 1) by omega]
    apply stateAux_cone hk2 consts hu hkey1 hkey2 (s + 1) (a + j)
    intro d hd
    rw [show a + j + d = a + (j + d) by omega]
    exact flipOff_bit_ne hkpos (by omega) (by omega) key
  unfold guard; dsimp only
  have hz0 : bit k (stateAux k consts u (flipOff k i r x hkpos key).val (s + 1)) (a + 2 * s) =
      bit k (stateAux k consts u key.val (s + 1)) (a + 2 * s) := by
    simpa using hz 0 (by decide)
  rw [show s + 2 - 1 = s + 1 by omega, hba, hz0, hz 1 (by decide), hz 2 (by decide)]

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
      p (maxSat p m) = true ∧ (∀ x ≤ m, p x = true → x ≤ maxSat p m) := by
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
    · simp only [htop]
      have hxm : x ≤ m := by
        by_contra h
        have hxe : x = m + 1 := by omega
        subst hxe; exact htop hpx
      rcases ih ⟨x, hxm, hpx⟩ with ⟨hp, hmax⟩
      refine ⟨hp, fun y hy hpy => ?_⟩
      have hym : y ≤ m := by
        by_contra h
        have hye : y = m + 1 := by omega
        subst hye; exact htop hpy
      exact hmax y hym hpy

lemma key_agree_window {k q : Nat} (hqk : q ≤ k) (smask : Nat)
    (base : Fin (2 ^ k)) (mask : Fin (2 ^ q)) {Δ : Nat} (hqΔ : q ≤ Δ) (hΔk : Δ < k) :
    bit k base.val (smask + Δ) = bit k (base.val ^^^ rot k smask mask.val) (smask + Δ) := by
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) hΔk
  have hmask_lt : mask.val < 2 ^ k :=
    Nat.lt_of_lt_of_le mask.isLt (Nat.pow_le_pow_right (by decide) hqk)
  rw [bit_xor, Nat.add_comm smask Δ, bit_rot_any hk hmask_lt]
  have hmb : bit k mask.val Δ = false := by
    unfold bit; rw [Nat.mod_eq_of_lt hΔk]
    exact Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le mask.isLt (Nat.pow_le_pow_right (by decide) hqΔ))
  rw [hmb, Bool.xor_false, Nat.add_comm Δ smask]

lemma arith_wave_Δ {k r e q i t δ : Nat}
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r)
    (hct : e + q + 3 ≤ t) (htr : t < r) (hδ : δ ≤ 4 * (r - t)) :
    let Δ := k + e + q - (5 * t - 2 + δ)
    q ≤ Δ ∧ Δ < k ∧
    ((i + 3 * r + k - e - q) + Δ) + 2 * (t - 1) = wpos k r i t δ + k := by
  obtain ⟨rm, rfl⟩ : ∃ rm, r = t + rm := ⟨r - t, by omega⟩
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have h5 : 5 * (t' + 1) - 2 = 5 * t' + 3 := by omega
  have hle1 : 5 * t' + 3 + δ + q ≤ k + e + q := by omega
  have hle2 : e + q ≤ i + 3 * (t' + 1 + rm) + k := by omega
  have hle3 : δ ≤ i + 3 * rm + k := by omega
  have hrm : t' + 1 + rm - (t' + 1) = rm := Nat.add_sub_cancel_left _ _
  dsimp only [wpos]
  rw [h5, hrm, Nat.add_sub_cancel]
  have hsub1 : i + 3 * (t' + 1 + rm) + k - e - q = i + 3 * (t' + 1 + rm) + k - (e + q) :=
    Nat.sub_sub _ _ _
  rw [hsub1]
  have hΔ : k + e + q - (5 * t' + 3 + δ) + (5 * t' + 3 + δ) = k + e + q :=
    Nat.sub_add_cancel (by omega)
  have hsm : i + 3 * (t' + 1 + rm) + k - (e + q) + (e + q) = i + 3 * (t' + 1 + rm) + k :=
    Nat.sub_add_cancel hle2
  have hwp : i + 3 * rm + k - δ + δ = i + 3 * rm + k := Nat.sub_add_cancel hle3
  refine ⟨by omega, by omega, by omega⟩

lemma arith_wave_upper {k r e q i t δ d : Nat}
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r)
    (hct : e + q + 3 ≤ t) (htr : t < r) (hδ1 : e + q ≤ δ) (hδ2 : δ ≤ 4 * (r - t))
    (hd : d < 5 * t - 2) :
    let Δ := k + e + q - (5 * t - 2 + δ)
    q ≤ Δ + d ∧ Δ + d < k ∧
    ((i + 3 * r + k - e - q) + Δ) + (2 * t - 2) = wpos k r i t δ + k := by
  obtain ⟨rm, rfl⟩ : ∃ rm, r = t + rm := ⟨r - t, by omega⟩
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have h5 : 5 * (t' + 1) - 2 = 5 * t' + 3 := by omega
  have h2 : 2 * (t' + 1) - 2 = 2 * t' := by omega
  have hle1 : 5 * t' + 3 + δ + q ≤ k + e + q := by omega
  have hle2 : e + q ≤ i + 3 * (t' + 1 + rm) + k := by omega
  have hle3 : δ ≤ i + 3 * rm + k := by omega
  have hrm : t' + 1 + rm - (t' + 1) = rm := Nat.add_sub_cancel_left _ _
  dsimp only [wpos]
  rw [h5, h2, hrm]
  rw [Nat.sub_sub (i + 3 * (t' + 1 + rm) + k) e q]
  have hΔ : k + e + q - (5 * t' + 3 + δ) + (5 * t' + 3 + δ) = k + e + q :=
    Nat.sub_add_cancel (by omega)
  have hsm : i + 3 * (t' + 1 + rm) + k - (e + q) + (e + q) = i + 3 * (t' + 1 + rm) + k :=
    Nat.sub_add_cancel hle2
  have hwp : i + 3 * rm + k - δ + δ = i + 3 * rm + k := Nat.sub_add_cancel hle3
  refine ⟨by omega, by omega, by omega⟩

lemma wpos_step_back {k r i t δ : Nat} (ht1 : 1 ≤ t) (htr : t ≤ r) (hδ : δ + 4 ≤ k) :
    wpos k r i t δ = wpos k r i (t - 1) (δ + 4) + 1 ∧
    ∀ j ≤ 4, wpos k r i (t - 1) (δ + 4) + j = wpos k r i (t - 1) (δ + 4 - j) := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  obtain ⟨rm, rfl⟩ : ∃ rm, r = t' + 1 + rm := ⟨r - (t' + 1), by omega⟩
  unfold wpos
  exact ⟨by omega, fun j hj => by omega⟩

lemma wave_pre_of_diff {k r e q u i : Nat} (consts : Nat → Fin (2 ^ k))
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r)
    (base : Fin (2 ^ k)) (mask : Fin (2 ^ q))
    {t δ : Nat} (hct : e + q + 3 ≤ t) (htr : t ≤ r) (hδ : δ ≤ 4 * (r - t))
    (hne : bit k (wave k r consts u base.val t) (wpos k r i t δ) ≠
      bit k (wave k r consts u (base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val) t)
        (wpos k r i t δ)) :
    bit k (preWord k consts u base.val t) (wpos k r i t δ) ≠
      bit k (preWord k consts u (base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val) t)
        (wpos k r i t δ) := by
  by_cases hlt : t < r
  · simp only [wave, hlt, ↓reduceIte] at hne
    have hkey2 : base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val < 2 ^ k :=
      Nat.xor_lt_two_pow base.isLt (rot_lt k _ _)
    rcases arith_wave_Δ (i := i) hq hr hk hct hlt hδ with ⟨hqΔ, hΔk, hsum⟩
    have hki : bit k (rot k (2 * (t - 1)) base.val) (wpos k r i t δ) =
        bit k (rot k (2 * (t - 1)) (base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val))
          (wpos k r i t δ) := by
      rw [← bit_add_k k _ (wpos k r i t δ), ← bit_add_k k _ (wpos k r i t δ),
        ← hsum, bit_rot_any (by omega) base.isLt, bit_rot_any (by omega) hkey2]
      exact key_agree_window (by omega) _ base mask hqΔ hΔk
    intro hpeq
    apply hne
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [stateAux_succ, stateAux_succ]
    simp only [bit_xor]
    unfold preWord at hpeq
    simp only [Nat.add_sub_cancel] at hpeq hki ⊢
    rw [hpeq, hki]
  · have hte : t = r := by omega
    subst hte
    simp only [wave, Nat.lt_irrefl, ↓reduceIte] at hne
    exact hne

lemma wave_upper_eq {k r e q u i : Nat} (consts : Nat → Fin (2 ^ k))
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r) (hu : u < 2 ^ k)
    (base : Fin (2 ^ k)) (mask : Fin (2 ^ q))
    {t δ : Nat} (hct : e + q + 3 ≤ t) (htr : t < r) (hδ1 : e + q ≤ δ) (hδ2 : δ ≤ 4 * (r - t)) :
    bit k (wave k r consts u base.val t) (wpos k r i t δ) =
      bit k (wave k r consts u (base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val) t)
        (wpos k r i t δ) := by
  simp only [wave, htr, ↓reduceIte]
  have hkey2 : base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val < 2 ^ k :=
    Nat.xor_lt_two_pow base.isLt (rot_lt k _ _)
  have hlo : leftOff t = 2 * t - 2 := leftOff_ge3 (by omega)
  have hpos := (arith_wave_upper (i := i) (d := 0) hq hr hk hct htr hδ1 hδ2 (by omega)).2.2
  rw [← bit_add_k k _ (wpos k r i t δ), ← bit_add_k k _ (wpos k r i t δ), ← hpos, ← hlo]
  apply stateAux_cone (by omega) consts hu base.isLt hkey2 t _
  intro d hd
  have hup := arith_wave_upper (i := i) (d := d) hq hr hk hct htr hδ1 hδ2 (by omega)
  rw [Nat.add_assoc]
  exact key_agree_window (by omega) _ base mask hup.1 hup.2.1

lemma wave_step_back {k r e q u i : Nat} (consts : Nat → Fin (2 ^ k))
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r) (hu : u < 2 ^ k)
    (base : Fin (2 ^ k)) (mask : Fin (2 ^ q))
    {t δ : Nat} (hct : e + q + 3 < t) (htr : t ≤ r) (hδ : δ ≤ 4 * (r - t))
    (hne : bit k (wave k r consts u base.val t) (wpos k r i t δ) ≠
      bit k (wave k r consts u (base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val) t)
        (wpos k r i t δ)) :
    ∃ δ', δ ≤ δ' ∧ δ' ≤ δ + 4 ∧
      bit k (wave k r consts u base.val (t - 1)) (wpos k r i (t - 1) δ') ≠
        bit k (wave k r consts u (base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val) (t - 1))
          (wpos k r i (t - 1) δ') := by
  have hpre := wave_pre_of_diff consts hq hr hk base mask (by omega) htr hδ hne
  rcases wpos_step_back (k := k) (i := i) (δ := δ) (by omega) htr (by omega) with ⟨hn, hnj⟩
  unfold preWord at hpre
  rw [hn] at hpre
  have htm1 : t - 1 < r := by omega
  by_contra hnone
  apply hpre
  apply bit_step_mix_eq (by omega) (stateAux_lt consts hu _ _) (stateAux_lt consts hu _ _)
  intro j hj
  rw [hnj j hj]
  by_contra hneq
  apply hnone
  refine ⟨δ + 4 - j, by omega, by omega, ?_⟩
  simp only [wave, htm1, ↓reduceIte]
  exact hneq

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
  let key2 := base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val
  let diffBit := fun t δ =>
    decide (bit k (wave k r consts u base.val t) (wpos k r i t δ) ≠
      bit k (wave k r consts u key2 t) (wpos k r i t δ))
  have hex : ∀ j ≤ r - (e + q + 3), ∃ δ ≤ 4 * j, diffBit (r - j) δ = true := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨0, Nat.le_refl _, ?_⟩
      dsimp only [diffBit, wpos]
      simp only [Nat.sub_zero, Nat.sub_self, Nat.mul_zero, Nat.add_zero, wave, Nat.lt_irrefl, ↓reduceIte]
      apply decide_eq_true
      unfold bit
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hi]
      exact hdiff
    | succ j ih =>
      intro hj
      rcases ih (by omega) with ⟨δ, hδ, hdb⟩
      rcases wave_step_back consts hq hr hk hu base mask (t := r - j) (δ := δ)
          (by omega) (by omega) (by omega) (of_decide_eq_true hdb) with ⟨δ', _, hδ2, hne'⟩
      rw [show r - j - 1 = r - (j + 1) by omega] at hne'
      exact ⟨δ', by omega, decide_eq_true hne'⟩
  let d := fun t => maxSat (diffBit t) (4 * (r - t))
  have hd_spec : ∀ t, e + q + 3 ≤ t → t ≤ r →
      diffBit t (d t) = true ∧ (∀ x ≤ 4 * (r - t), diffBit t x = true → x ≤ d t) := by
    intro t hct htr
    have h1 := hex (r - t) (by omega)
    rw [show r - (r - t) = t by omega] at h1
    exact maxSat_spec (diffBit t) (4 * (r - t)) h1
  refine ⟨d, ?_, ?_, ?_⟩
  · intro t hct htr
    have hle : d t ≤ 4 * (r - t) := maxSat_le _ _
    refine ⟨?_, hle⟩
    by_cases hlt : t < r
    · by_contra hge
      exact of_decide_eq_true (hd_spec t hct htr).1
        (wave_upper_eq consts hq hr hk hu base mask hct hlt (by omega) hle)
    · omega
  · intro t hct htr
    have hle : d t ≤ 4 * (r - t) := maxSat_le _ _
    rcases wave_step_back consts hq hr hk hu base mask hct htr hle
        (of_decide_eq_true (hd_spec t (by omega) htr).1) with ⟨δ', hδ1, hδ2, hne'⟩
    have hmax := (hd_spec (t - 1) (by omega) (by omega)).2 δ' (by omega) (decide_eq_true hne')
    omega
  · intro t hct htre hrec
    have htr : t ≤ r := by omega
    have hle : d t ≤ 4 * (r - t) := maxSat_le _ _
    have hrec1 : (t - 1) + d (t - 1) < t + d t := hrec (t - 1) (by omega) (by omega)
    have hpre := wave_pre_of_diff consts hq hr hk base mask (by omega) htr hle
      (of_decide_eq_true (hd_spec t (by omega) htr).1)
    rcases wpos_step_back (k := k) (i := i) (δ := d t) (by omega) htr (by omega) with ⟨hn, hnj⟩
    unfold preWord at hpre
    rw [hn] at hpre
    have htm1 : t - 1 < r := by omega
    have hforced := bit_step_mix_forced (by omega)
      (stateAux_lt consts hu base.val (t - 1)) (stateAux_lt consts hu key2 (t - 1)) _
      (fun j hj => by
        rw [hnj j (by omega)]
        by_contra hneq
        have hdb' : diffBit (t - 1) (d t + 4 - j) = true := by
          dsimp only [diffBit]; simp only [wave, htm1, ↓reduceIte]; exact decide_eq_true hneq
        have hmax := (hd_spec (t - 1) (by omega) (by omega)).2 (d t + 4 - j) (by omega) hdb'
        omega)
      hpre
    unfold guard; dsimp only
    rw [hn]
    exact hforced

lemma accepts_of_history {k : Nat} (G : Nat → Nat → Fin (2 ^ k) → Bool)
    {cut tEnd : Nat} (key : Fin (2 ^ k)) (d : Nat → Nat)
    (h2 : ∀ t, cut < t → t ≤ tEnd → d t ≤ d (t - 1))
    (h3 : ∀ t, cut < t → t ≤ tEnd →
      (∀ s, cut ≤ s → s < t → s + d s < t + d t) → G t (d t) key = false) :
    ∀ n t g, t + n = tEnd + 1 → cut < t →
      (∀ s, cut ≤ s → s < t → s + d s < t + g) →
      accepts G n t g key = true := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _; rfl
  | succ n ih =>
    intro t g htn hct hinv
    unfold accepts
    by_cases hdone : n + 1 ≤ g
    · simp only [hdone, ↓reduceIte]
    · simp only [hdone, ↓reduceIte]
      have hprev : (t - 1) + d (t - 1) < t + g := hinv (t - 1) (by omega) (by omega)
      have hdt_le : d t ≤ g := Nat.le_trans (h2 t hct (by omega)) (by omega)
      cases hgv : G t g key
      · simp only [Bool.false_eq_true, ↓reduceIte]
        apply ih (t + 1) g (by omega) (by omega)
        intro s hs1 hs2
        by_cases hst : s < t
        · have := hinv s hs1 hst; omega
        · have heq : s = t := by omega
          subst heq; omega
      · simp only [↓reduceIte]
        have hdt_lt : d t < g := by
          by_contra hge
          have hdeq : d t = g := by omega
          have h0 := h3 t hct (by omega) (fun s hs1 hs2 => by rw [hdeq]; exact hinv s hs1 hs2)
          rw [hdeq, hgv] at h0
          exact Bool.noConfusion h0
        cases g with
        | zero => omega
        | succ g' =>
          apply ih (t + 1) g' (by omega) (by omega)
          intro s hs1 hs2
          by_cases hst : s < t
          · have := hinv s hs1 hst; omega
          · have heq : s = t := by omega
            subst heq; omega

lemma binomTail_zero (n : Nat) : binomTail n 0 = 1 := by
  unfold binomTail; simp

lemma binomTail_of_le {n g : Nat} (h : n ≤ g) : binomTail n g = 2 ^ n := by
  induction g with
  | zero =>
    have : n = 0 := by omega
    subst this; exact Nat.sum_range_choose 0
  | succ g ih =>
    by_cases hle : n ≤ g
    · unfold binomTail
      rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (by omega), Nat.add_zero]
      exact ih hle
    · have : n = g + 1 := by omega
      subst this; exact Nat.sum_range_choose (g + 1)

lemma binomTail_succ_succ (n d : Nat) :
    binomTail (n + 1) (d + 1) = binomTail n (d + 1) + binomTail n d := by
  unfold binomTail
  rw [Finset.sum_range_succ' (fun j => Nat.choose (n + 1) j) (d + 1)]
  simp only [Nat.choose_zero_right]
  have hsplit : ∑ j ∈ Finset.range (d + 1), Nat.choose (n + 1) (j + 1) =
      ∑ j ∈ Finset.range (d + 1), (Nat.choose n j + Nat.choose n (j + 1)) :=
    Finset.sum_congr rfl fun j _ => Nat.choose_succ_succ n j
  rw [hsplit, Finset.sum_add_distrib,
    Finset.sum_range_succ' (fun j => Nat.choose n j) (d + 1)]
  simp only [Nat.choose_zero_right]
  omega

lemma sum_choose_add_eq (r d : Nat) :
    ∑ j ∈ Finset.range (d + 1), Nat.choose (r + j) j = Nat.choose (r + d + 1) d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih, show r + (d + 1) = r + d + 1 by omega]
    exact (Nat.choose_succ_succ (r + d + 1) d).symm

lemma binomTail_le_choose {r e q : Nat} (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) :
    binomTail ((r - e) - (e + q + 3)) (e + q - 1) ≤ Nat.choose (r + (e + q) + 1) (e + q) := by
  unfold binomTail
  rw [show e + q - 1 + 1 = e + q by omega]
  have h1 : ∑ j ∈ Finset.range (e + q), Nat.choose ((r - e) - (e + q + 3)) j ≤
      ∑ j ∈ Finset.range (e + q + 1), Nat.choose ((r - e) - (e + q + 3)) j := by
    rw [Finset.sum_range_succ]
    exact Nat.le_add_right _ _
  have h2 : ∑ j ∈ Finset.range (e + q + 1), Nat.choose ((r - e) - (e + q + 3)) j ≤
      ∑ j ∈ Finset.range (e + q + 1), Nat.choose (r + j) j :=
    Finset.sum_le_sum fun j _ => Nat.choose_le_choose j (by omega)
  exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_of_eq (sum_choose_add_eq r (e + q))))

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
    ext x; simp only [Finset.mem_filter]; cases f x <;> simp
  rw [hnot, ← heq] at hsum
  exact ⟨heq, by omega⟩

lemma card_accepts_le {k t0 tEnd c : Nat}
    (G : Nat → Nat → Fin (2 ^ k) → Bool)
    (inv : Nat → Fin (2 ^ k) → Fin (2 ^ k))
    (hinvol : ∀ x key, inv x (inv x key) = key)
    (piv : Nat → Nat → Nat)
    (hpiv_f : ∀ t g, t0 ≤ t → piv t g + 1 ≤ piv (t + 1) g)
    (hpiv_t : ∀ t g, t0 ≤ t → piv t (g + 1) + 1 ≤ piv (t + 1) g)
    (hbound : ∀ t g, t0 ≤ t → t + g ≤ tEnd → piv t g < k)
    (hflip : ∀ t g key, t0 ≤ t → t + g ≤ tEnd → G t g (inv (piv t g) key) = !(G t g key))
    (habove : ∀ t g x key, t0 ≤ t → t + g ≤ tEnd → piv t g < x → x < k →
      G t g (inv x key) = G t g key) :
    ∀ n t g M (S : Finset (Fin (2 ^ k))),
      t0 ≤ t → t + n = tEnd + 1 → M ≤ piv t g → S.card = 2 ^ (c + n) →
      (∀ x, M ≤ x → x < k → ∀ key, inv x key ∈ S ↔ key ∈ S) →
      (S.filter (fun key => accepts G n t g key = true)).card ≤ binomTail n g * 2 ^ c := by
  intro n
  induction n with
  | zero =>
    intro t g M S _ _ _ hcard _
    have hsub : S.filter (fun key => accepts G 0 t g key = true) = S := by
      ext key; simp [accepts]
    rw [hsub, hcard, Nat.add_zero, binomTail_of_le (Nat.zero_le g), Nat.pow_zero, Nat.one_mul]
  | succ n ih =>
    intro t g M S ht htn hM hcard hinv
    by_cases hdone : n + 1 ≤ g
    · have hsub : S.filter (fun key => accepts G (n + 1) t g key = true) = S := by
        ext key; simp [accepts, hdone]
      rw [hsub, hcard, binomTail_of_le hdone, ← Nat.pow_add, Nat.add_comm (n + 1) c]
    · have htg : t + g ≤ tEnd := by omega
      have hoff_lt : piv t g < k := hbound t g ht htg
      have hhalf := filter_half S (G t g) (inv (piv t g)) (hinvol _)
        (hinv _ hM hoff_lt) (fun key => hflip t g key ht htg)
      set Sf := S.filter (fun key => G t g key = false)
      set St := S.filter (fun key => G t g key = true)
      have hpow : 2 ^ (c + (n + 1)) = 2 * 2 ^ (c + n) := by
        rw [← Nat.add_assoc, Nat.pow_succ, Nat.mul_comm]
      have hSf_card : Sf.card = 2 ^ (c + n) := by omega
      have hSt_card : St.card = 2 ^ (c + n) := by omega
      have hSf_inv : ∀ x, piv t g + 1 ≤ x → x < k → ∀ key, inv x key ∈ Sf ↔ key ∈ Sf := by
        intro x hx1 hx2 key
        simp only [Sf, Finset.mem_filter]
        rw [hinv x (Nat.le_trans hM (Nat.le_of_lt hx1)) hx2 key, habove t g x key ht htg hx1 hx2]
      have hSt_inv : ∀ x, piv t g + 1 ≤ x → x < k → ∀ key, inv x key ∈ St ↔ key ∈ St := by
        intro x hx1 hx2 key
        simp only [St, Finset.mem_filter]
        rw [hinv x (Nat.le_trans hM (Nat.le_of_lt hx1)) hx2 key, habove t g x key ht htg hx1 hx2]
      have hbf := ih (t + 1) g (piv t g + 1) Sf (Nat.le_succ_of_le ht) (by omega) (hpiv_f t g ht) hSf_card hSf_inv
      cases g with
      | zero =>
        have hsub : S.filter (fun key => accepts G (n + 1) t 0 key = true) ⊆
            Sf.filter (fun key => accepts G n (t + 1) 0 key = true) := by
          intro key hk
          simp only [Sf, Finset.mem_filter] at hk ⊢
          rcases hk with ⟨hkS, hacc⟩
          unfold accepts at hacc
          simp only [hdone, ↓reduceIte] at hacc
          cases hgv : G t 0 key
          · simp only [hgv, Bool.false_eq_true, ↓reduceIte] at hacc
            exact ⟨⟨hkS, rfl⟩, hacc⟩
          · simp only [hgv, ↓reduceIte] at hacc
            exact Bool.noConfusion hacc
        rw [binomTail_zero] at hbf ⊢
        exact Nat.le_trans (Finset.card_le_card hsub) hbf
      | succ g' =>
        have hsub : S.filter (fun key => accepts G (n + 1) t (g' + 1) key = true) ⊆
            Sf.filter (fun key => accepts G n (t + 1) (g' + 1) key = true) ∪
            St.filter (fun key => accepts G n (t + 1) g' key = true) := by
          intro key hk
          simp only [Sf, St, Finset.mem_union, Finset.mem_filter] at hk ⊢
          rcases hk with ⟨hkS, hacc⟩
          unfold accepts at hacc
          simp only [hdone, ↓reduceIte] at hacc
          cases hgv : G t (g' + 1) key
          · simp only [hgv, Bool.false_eq_true, ↓reduceIte] at hacc
            exact Or.inl ⟨⟨hkS, rfl⟩, hacc⟩
          · simp only [hgv, ↓reduceIte] at hacc
            exact Or.inr ⟨⟨hkS, rfl⟩, hacc⟩
        have hbt := ih (t + 1) g' (piv t (g' + 1) + 1) St (Nat.le_succ_of_le ht) (by omega) (hpiv_t t g' ht) hSt_card hSt_inv
        calc
          (S.filter (fun key => accepts G (n + 1) t (g' + 1) key = true)).card
              ≤ (Sf.filter (fun key => accepts G n (t + 1) (g' + 1) key = true) ∪
                  St.filter (fun key => accepts G n (t + 1) g' key = true)).card :=
            Finset.card_le_card hsub
          _ ≤ (Sf.filter (fun key => accepts G n (t + 1) (g' + 1) key = true)).card +
              (St.filter (fun key => accepts G n (t + 1) g' key = true)).card :=
            Finset.card_union_le _ _
          _ ≤ binomTail n (g' + 1) * 2 ^ c + binomTail n g' * 2 ^ c :=
            Nat.add_le_add hbf hbt
          _ = (binomTail n (g' + 1) + binomTail n g') * 2 ^ c := (Nat.add_mul _ _ _).symm
          _ = binomTail (n + 1) (g' + 1) * 2 ^ c := by rw [binomTail_succ_succ]

lemma card_exc_le (k r e q : Nat) (constants : Nat → Fin (2 ^ k)) (u i : Nat)
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r)
    (hu : u < 2 ^ k) (hi : i < k) :
    ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun base =>
      ∃ mask : Fin (2 ^ q),
        (preWord k constants u base.val r).testBit i ≠
          (preWord k constants u
            (base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val) r).testBit i)).card ≤
      Nat.choose (r + (e + q) + 1) (e + q) * 2 ^ (k - (r - (3 * e + 2 * q + 2))) := by
  let N := (r - e) - (e + q + 3)
  let D := e + q - 1
  let G : Nat → Nat → Fin (2 ^ k) → Bool := fun t g key =>
    guard k r constants u i key.val t g
  have hsub :
      (Finset.univ : Finset (Fin (2 ^ k))).filter (fun base =>
        ∃ mask : Fin (2 ^ q),
          (preWord k constants u base.val r).testBit i ≠
            (preWord k constants u
              (base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val) r).testBit i) ⊆
      (Finset.univ : Finset (Fin (2 ^ k))).filter (fun base =>
        accepts G N (e + q + 3 + 1) D base = true) := by
    intro base hmem
    rw [Finset.mem_filter] at hmem ⊢
    refine ⟨hmem.1, ?_⟩
    rcases hmem.2 with ⟨mask, hdiff⟩
    rcases wave_history constants hq hr hk hu hi base mask hdiff with ⟨d, h1, h2, h3⟩
    apply accepts_of_history G base d (fun t ht1 ht2 => h2 t ht1 (by omega)) h3
      N (e + q + 3 + 1) D (by omega) (by omega)
    intro s hs1 hs2
    have hse : s = e + q + 3 := by omega
    subst hse
    have hd0 := (h1 (e + q + 3) (Nat.le_refl _) (by omega)).1
    omega
  have hkpos : 0 < k := by omega
  have hbound := card_accepts_le (t0 := e + q + 4) (tEnd := r - e) (c := k - N)
    G (fun x key => flipOff k i r x hkpos key)
    (fun x key => flipOff_invol k i r x hkpos key)
    (fun t g => 5 * t - 4 + g) (fun _ _ _ => by omega) (fun _ _ _ => by omega)
    (fun t g ht htg => by omega)
    (fun t g key ht htg =>
      guard_flip_pivot constants (by omega) hu hkpos (by omega) (by omega) (by omega) key)
    (fun t g x key ht htg hx1 hx2 =>
      guard_flip_above constants (by omega) hu hkpos (by omega) (by omega) (by omega) hx2 key)
    N (e + q + 3 + 1) D 0 Finset.univ (by omega) (by omega) (Nat.zero_le _)
    (by simp [Finset.card_univ, Fintype.card_fin, show k - N + N = k by omega])
    (fun _ _ _ _ => by simp)
  have hbt : binomTail N D ≤ Nat.choose (r + (e + q) + 1) (e + q) :=
    binomTail_le_choose hq hr
  have hpow : 2 ^ (k - N) ≤ 2 ^ (k - (r - (3 * e + 2 * q + 2))) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.le_trans (Finset.card_le_card hsub)
    (Nat.le_trans hbound (Nat.mul_le_mul hbt hpow))

def proj (k q baseOff : Nat) (hqk : q ≤ k) (key : Fin (2 ^ k)) : Fin (2 ^ (k - q)) :=
  ⟨(rot k (k - baseOff % k) key.val) >>> q, by
    rw [Nat.shiftRight_eq_div_pow]
    have hlt : rot k (k - baseOff % k) key.val < 2 ^ q * 2 ^ (k - q) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hqk]
      exact rot_lt k _ _
    exact Nat.div_lt_of_lt_mul hlt⟩

lemma bit_eq_of_proj_eq {k q baseOff : Nat} (hk : 0 < k) (hqk : q ≤ k)
    {key1 key2 : Fin (2 ^ k)}
    (hproj : proj k q baseOff hqk key1 = proj k q baseOff hqk key2)
    {m : Nat} (hm1 : q ≤ m) (hm2 : m < k) :
    bit k key1.val (baseOff + m) = bit k key2.val (baseOff + m) := by
  rw [← bit_rotInv hk key1.isLt baseOff m, ← bit_rotInv hk key2.isLt baseOff m]
  unfold bit
  rw [Nat.mod_eq_of_lt hm2]
  have hval : (rot k (k - baseOff % k) key1.val) >>> q =
      (rot k (k - baseOff % k) key2.val) >>> q := congrArg Fin.val hproj
  have htb := congrArg (fun x => x.testBit (m - q)) hval
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight,
    show q + (m - q) = m by omega] at htb
  exact htb

lemma exists_diff_of_ne {k q baseOff : Nat} (hk : 0 < k) (hqk : q ≤ k)
    {key1 key2 : Fin (2 ^ k)}
    (hproj : proj k q baseOff hqk key1 = proj k q baseOff hqk key2)
    (hne : key1 ≠ key2) :
    ∃ j < q, bit k key1.val (baseOff + j) ≠ bit k key2.val (baseOff + j) := by
  by_contra hnone
  apply hne
  apply Fin.ext
  have hrot_eq : rot k (k - baseOff % k) key1.val = rot k (k - baseOff % k) key2.val := by
    apply Nat.eq_of_testBit_eq
    intro m
    by_cases hm : m < k
    · have h1 : (rot k (k - baseOff % k) key1.val).testBit m = bit k key1.val (baseOff + m) := by
        rw [← bit_rotInv hk key1.isLt baseOff m]; unfold bit; rw [Nat.mod_eq_of_lt hm]
      have h2 : (rot k (k - baseOff % k) key2.val).testBit m = bit k key2.val (baseOff + m) := by
        rw [← bit_rotInv hk key2.isLt baseOff m]; unfold bit; rw [Nat.mod_eq_of_lt hm]
      rw [h1, h2]
      by_cases hmq : m < q
      · by_contra hdiff
        exact hnone ⟨m, hmq, hdiff⟩
      · exact bit_eq_of_proj_eq hk hqk hproj (by omega) hm
    · have hlt1 : rot k (k - baseOff % k) key1.val < 2 ^ m :=
        Nat.lt_of_lt_of_le (rot_lt k _ _) (Nat.pow_le_pow_right (by decide) (by omega))
      have hlt2 : rot k (k - baseOff % k) key2.val < 2 ^ m :=
        Nat.lt_of_lt_of_le (rot_lt k _ _) (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.testBit_lt_two_pow hlt1, Nat.testBit_lt_two_pow hlt2]
  have hback := congrArg (rot k baseOff) hrot_eq
  rw [rot_rotInv hk key1.isLt baseOff, rot_rotInv hk key2.isLt baseOff] at hback
  exact hback

lemma pair_in_exc {k r e q u : Nat} (constants : Nat → Fin (2 ^ k))
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r)
    (hqk : q ≤ k)
    (key1 key2 : Fin (2 ^ k))
    (hp1 : stateAux k constants u key1.val r < 2 ^ (k - (k + 1) / 2))
    (hp2 : stateAux k constants u key2.val r < 2 ^ (k - (k + 1) / 2))
    (hproj : proj k q ((k - q) + 3 * r + k - e - 1) hqk key1 =
      proj k q ((k - q) + 3 * r + k - e - 1) hqk key2)
    (hne : key1 ≠ key2) :
    ∃ j : Fin q, ∃ mask : Fin (2 ^ q),
      (preWord k constants u key1.val r).testBit (k - q + j.val) ≠
        (preWord k constants u
          (key1.val ^^^ rot k ((k - q + j.val) + 3 * r + k - e - q) mask.val) r).testBit
          (k - q + j.val) := by
  have hkpos : 0 < k := by omega
  let baseOff := (k - q) + 3 * r + k - e - 1
  rcases exists_diff_of_ne hkpos hqk hproj hne with ⟨j0, hj0, hdiff0⟩
  let p : Nat → Bool := fun j =>
    decide (bit k key1.val (baseOff + j) ≠ bit k key2.val (baseOff + j))
  have hspec := maxSat_spec p (q - 1) ⟨j0, by omega, decide_eq_true hdiff0⟩
  let jm := maxSat p (q - 1)
  have hjm_le : jm ≤ q - 1 := maxSat_le p (q - 1)
  have hjm_lt : jm < q := by omega
  have hjm_ne : bit k key1.val (baseOff + jm) ≠ bit k key2.val (baseOff + jm) :=
    of_decide_eq_true hspec.1
  have hagree : ∀ m, jm < m → m < k →
      bit k key1.val (baseOff + m) = bit k key2.val (baseOff + m) := by
    intro m hm1 hm2
    by_cases hmq : m < q
    · by_contra hdm
      have hle := hspec.2 m (by omega) (decide_eq_true hdm)
      omega
    · exact bit_eq_of_proj_eq hkpos hqk hproj (by omega) hm2
  let i := k - q + jm
  let Si := i + 3 * r + k - e - q
  let diff := key1.val ^^^ key2.val
  have hdiff_lt : diff < 2 ^ k := Nat.xor_lt_two_pow key1.isLt key2.isLt
  let maskVal := rot k (k - Si % k) diff
  have hmask_lt : maskVal < 2 ^ q := by
    apply Nat.lt_pow_two_of_testBit
    intro d hd
    by_cases hdk : d < k
    · have h1 : maskVal.testBit d = bit k maskVal d := by
        unfold bit; rw [Nat.mod_eq_of_lt hdk]
      rw [h1, bit_rotInv hkpos hdiff_lt Si d, bit_xor]
      have hpos : Si + d = baseOff + (jm + 1 + (d - q)) := by
        dsimp only [Si, i, baseOff]; omega
      rw [hpos, hagree (jm + 1 + (d - q)) (by omega) (by omega)]
      simp
    · exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le (rot_lt k _ _) (Nat.pow_le_pow_right (by decide) (by omega)))
  have hkey2_eq : key1.val ^^^ rot k Si maskVal = key2.val := by
    dsimp only [maskVal]
    rw [rot_rotInv hkpos hdiff_lt Si]
    dsimp only [diff]
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have hi_lt : i < k := by dsimp only [i]; omega
  have hi_ge : k - (k + 1) / 2 ≤ i := by dsimp only [i]; omega
  have hout1 : (stateAux k constants u key1.val r).testBit i = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hp1 (Nat.pow_le_pow_right (by decide) hi_ge))
  have hout2 : (stateAux k constants u key2.val r).testBit i = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hp2 (Nat.pow_le_pow_right (by decide) hi_ge))
  have hr_eq : r = (r - 1) + 1 := by omega
  have hstate_bit : ∀ key : Fin (2 ^ k),
      (stateAux k constants u key.val r).testBit i =
        xor (xor ((preWord k constants u key.val r).testBit i)
          (bit k key.val (baseOff + jm))) ((constants r).val.testBit i) := by
    intro key
    conv_lhs => rw [hr_eq, stateAux_succ]
    rw [Nat.testBit_xor, Nat.testBit_xor, ← hr_eq]
    have hpre_eq : step k (mix k (stateAux k constants u key.val (r - 1))) =
        preWord k constants u key.val r := rfl
    rw [hpre_eq]
    have hrot_bit : (rot k (2 * (r - 1)) key.val).testBit i = bit k key.val (baseOff + jm) := by
      have hb : (rot k (2 * (r - 1)) key.val).testBit i =
          bit k (rot k (2 * (r - 1)) key.val) i := by
        unfold bit; rw [Nat.mod_eq_of_lt hi_lt]
      rw [hb, ← bit_add_k k _ i, ← bit_add_k k _ (i + k)]
      have hsum : i + k + k = (baseOff + jm) + 2 * (r - 1) := by
        dsimp only [i, baseOff]; omega
      rw [hsum, bit_rot_any hkpos key.isLt]
    rw [hrot_bit]
  have hpre_ne : (preWord k constants u key1.val r).testBit i ≠
      (preWord k constants u key2.val r).testBit i := by
    intro hpeq
    have he1 := hstate_bit key1
    have he2 := hstate_bit key2
    rw [hout1] at he1
    rw [hout2] at he2
    have hEq : xor (xor ((preWord k constants u key1.val r).testBit i)
        (bit k key1.val (baseOff + jm))) ((constants r).val.testBit i) =
      xor (xor ((preWord k constants u key1.val r).testBit i)
        (bit k key2.val (baseOff + jm))) ((constants r).val.testBit i) := by
      rw [← he1, hpeq, ← he2]
    exact hjm_ne (xor_xor_cancel hEq)
  refine ⟨⟨jm, hjm_lt⟩, ⟨maskVal, hmask_lt⟩, ?_⟩
  change (preWord k constants u key1.val r).testBit i ≠
    (preWord k constants u (key1.val ^^^ rot k Si maskVal) r).testBit i
  rw [hkey2_eq]
  exact hpre_ne

end PEqualNP.Outside.L_meta_25519

theorem PEqualNP.Outside.L_meta_25519 : ∀ (k r e q : ℕ) (constants : ℕ → Fin (2 ^ k)) (u : ℕ),
  0 < q → 3 * e + 2 * q + 3 ≤ r → k + e + 3 = 5 * r → u < 2 ^ k →
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
  ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun subject =>
    state subject.val r < 2 ^ (k - (k + 1) / 2))).card ≤
    2 ^ (k - q) + q * Nat.choose (r + (e + q) + 1) (e + q) * 2 ^ (k - (r - (3 * e + 2 * q + 2))) := by
  intro k r e q constants u hq hr hk hu rot step state
  have hqk : q ≤ k := by omega
  let baseOff := (k - q) + 3 * r + k - e - 1
  let Pass : Finset (Fin (2 ^ k)) :=
    Finset.univ.filter (fun subject =>
      PEqualNP.Outside.L_meta_25519.stateAux k constants u subject.val r < 2 ^ (k - (k + 1) / 2))
  let Exc : Fin q → Finset (Fin (2 ^ k)) := fun j =>
    Finset.univ.filter (fun base =>
      ∃ mask : Fin (2 ^ q),
        (PEqualNP.Outside.L_meta_25519.preWord k constants u base.val r).testBit (k - q + j.val) ≠
          (PEqualNP.Outside.L_meta_25519.preWord k constants u
            (base.val ^^^ PEqualNP.Outside.L_meta_25519.rot k
              ((k - q + j.val) + 3 * r + k - e - q) mask.val) r).testBit (k - q + j.val))
  let Bad : Finset (Fin (2 ^ k)) := Finset.univ.biUnion Exc
  let Good : Finset (Fin (2 ^ k)) := Pass \ Bad
  have hsub : Pass ⊆ Good ∪ Bad := by
    intro x hx
    by_cases hxb : x ∈ Bad
    · exact Finset.mem_union_right _ hxb
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxb⟩)
  have hgood : Good.card ≤ 2 ^ (k - q) := by
    have hinj : Set.InjOn (PEqualNP.Outside.L_meta_25519.proj k q baseOff hqk) Good := by
      intro x hx y hy hxy
      by_contra hne
      have hxP : x ∈ Pass := (Finset.mem_sdiff.mp hx).1
      have hxNB : x ∉ Bad := (Finset.mem_sdiff.mp hx).2
      have hyP : y ∈ Pass := (Finset.mem_sdiff.mp hy).1
      rcases PEqualNP.Outside.L_meta_25519.pair_in_exc constants hq hr hk hqk x y
        (Finset.mem_filter.mp hxP).2 (Finset.mem_filter.mp hyP).2 hxy hne with ⟨j, mask, hdiff⟩
      exact hxNB (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j,
        Finset.mem_filter.mpr ⟨Finset.mem_univ x, ⟨mask, hdiff⟩⟩⟩)
    have hcard := Finset.card_le_card_of_injOn
      (PEqualNP.Outside.L_meta_25519.proj k q baseOff hqk)
      (fun _ _ => Finset.mem_univ _) hinj
    simpa [Finset.card_univ, Fintype.card_fin] using hcard
  have hbad : Bad.card ≤
      q * Nat.choose (r + (e + q) + 1) (e + q) * 2 ^ (k - (r - (3 * e + 2 * q + 2))) := by
    calc
      Bad.card ≤ ∑ j : Fin q, (Exc j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j : Fin q,
            Nat.choose (r + (e + q) + 1) (e + q) * 2 ^ (k - (r - (3 * e + 2 * q + 2))) :=
        Finset.sum_le_sum fun j _ =>
          PEqualNP.Outside.L_meta_25519.card_exc_le k r e q constants u (k - q + j.val)
            hq hr hk hu (by omega)
      _ = q * (Nat.choose (r + (e + q) + 1) (e + q) * 2 ^ (k - (r - (3 * e + 2 * q + 2)))) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      _ = q * Nat.choose (r + (e + q) + 1) (e + q) * 2 ^ (k - (r - (3 * e + 2 * q + 2))) :=
        (Nat.mul_assoc _ _ _).symm
  change Pass.card ≤ _
  calc
    Pass.card ≤ (Good ∪ Bad).card := Finset.card_le_card hsub
    _ ≤ Good.card + Bad.card := Finset.card_union_le _ _
    _ ≤ 2 ^ (k - q) +
        q * Nat.choose (r + (e + q) + 1) (e + q) * 2 ^ (k - (r - (3 * e + 2 * q + 2))) :=
      Nat.add_le_add hgood hbad
