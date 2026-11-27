import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25510

abbrev Tape := ℤ → Bool

def mix (s : Tape) (d : ℤ) := xor (xor (s (d - 1)) (s (d - 2))) (s d)

def box (a b c : Bool) := xor a (!b && c)

def layer (s : Tape) (d : ℤ) := box (mix s (d - 2)) (mix s (d - 1)) (mix s d)

def run (x key : Tape) (c : ℕ → Tape) : ℕ → Tape
  | 0 => x
  | t + 1 => fun d => xor (xor (layer (run x key c t) d) (key (d - 5 * t - 3))) (c t d)

lemma mix_congr {s u : Tape} {d : ℤ} (h : ∀ j, d - 2 ≤ j → j ≤ d → s j = u j) :
    mix s d = mix u d := by
  unfold mix
  rw [h (d - 1) (by omega) (by omega), h (d - 2) (by omega) (by omega), h d (by omega) (by omega)]

lemma layer_congr {s u : Tape} {d : ℤ} (h : ∀ j, d - 4 ≤ j → j ≤ d → s j = u j) :
    layer s d = layer u d := by
  unfold layer
  congr 1 <;> apply mix_congr <;> intro j hj hj' <;> apply h <;> omega

lemma run_congr {x y a b : Tape} {c : ℕ → Tape} (t : ℕ) (d : ℤ)
    (hx : ∀ j, d - 4 * t ≤ j → j ≤ d → x j = y j)
    (hk : ∀ j, d - 5 * t + 2 ≤ j → j ≤ d - 3 → a j = b j) :
    run x a c t d = run y b c t d := by
  induction t generalizing d with
  | zero => exact hx d (by simp) le_rfl
  | succ t ih =>
    unfold run
    have hc : layer (run x a c t) d = layer (run y b c t) d := by
      apply layer_congr
      intro e he he'
      apply ih <;> intro j hj hj'
      · apply hx <;> omega
      · apply hk <;> omega
    rw [hc, hk (d - 5 * t - 3) (by omega) (by omega)]

def advance (p : Bool × Bool) (a b c : Bool) : Bool × Bool :=
  ((!a && p.1), xor (!b && c) (!(xor b p.1) && xor c (xor p.1 p.2)))

def track (v : ℕ → Tape) : ℕ → Bool × Bool
  | 0 => (true, false)
  | t + 1 => advance (track v t) (v t (-1)) (v t 0) (v t 1)

lemma track_congr {v w : ℕ → Tape} (t : ℕ)
    (h : ∀ j, j < t → ∀ d, -1 ≤ d → d ≤ 1 → v j d = w j d) :
    track v t = track w t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [track]
    rw [ih (fun j hj => h j (by omega)), h t (by omega) (-1) (by decide) (by decide),
      h t (by omega) 0 (by decide) (by decide), h t (by omega) 1 (by decide) (by decide)]

def idx (k : ℕ) (o z : ℤ) : ℕ := ((o + z) % (k : ℤ)).toNat

lemma idx_val {k : ℕ} (hk : 0 < k) (o z : ℤ) :
    (idx k o z : ℤ) = (o + z) % (k : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

lemma idx_lt {k : ℕ} (hk : 0 < k) (o z : ℤ) : idx k o z < k := by
  have h := idx_val hk o z
  have := Int.emod_lt_of_pos (o + z) (show 0 < (k : ℤ) by omega)
  omega

lemma idx_dvd {k : ℕ} (hk : 0 < k) (o p q : ℤ) :
    idx k o p = idx k o q ↔ (k : ℤ) ∣ q - p := by
  have hm : (o + p) ≡ (o + q) [ZMOD (k : ℤ)] ↔ (k : ℤ) ∣ q - p := by
    rw [Int.modEq_iff_dvd, show o + q - (o + p) = q - p by omega]
  rw [← hm]
  change _ ↔ (o + p) % (k : ℤ) = (o + q) % (k : ℤ)
  rw [← idx_val hk, ← idx_val hk]
  omega

lemma idx_ne {k : ℕ} (hk : 0 < k) {p q : ℤ} (o : ℤ)
    (ha : p < q) (hb : q - p < k) : idx k o p ≠ idx k o q := by
  intro h
  have hd := (idx_dvd hk o p q).mp h
  have := Int.le_of_dvd (show 0 < q - p by omega) hd
  omega

def bits (k : ℕ) (o : ℤ) (w : ℕ) : Tape := fun d => w.testBit (idx k o d)

def twist (k : ℕ) (o p : ℤ) (s : Tape) : Tape :=
  fun d => xor (s d) (decide (idx k o p = idx k o d))

lemma twist_eq {k : ℕ} {o p d : ℤ} {s : Tape} (h : idx k o p = idx k o d) :
    twist k o p s d = !(s d) := by simp [twist, h]

lemma twist_ne {k : ℕ} {o p d : ℤ} {s : Tape} (h : idx k o p ≠ idx k o d) :
    twist k o p s d = s d := by simp [twist, h]

lemma unchanged {k : ℕ} (hk : 0 < k) (o : ℤ) (x a : Tape) (c : ℕ → Tape) (t : ℕ) (d : ℤ)
    (hu : d < 0) (hx : -(k : ℤ) < d - 4 * t) (ha : -(k : ℤ) - 1 < d - 5 * t + 2) :
    run (twist k o 0 x) (twist k o (-1) a) c t d = run x a c t d := by
  apply run_congr <;> intro j hj hj'
  · exact twist_ne (idx_ne hk o (by omega : j < 0) (by omega)).symm
  · exact twist_ne (idx_ne hk o (by omega : j < -1) (by omega)).symm

lemma mix_diff (s u : Tape) (d : ℤ) (a b c : Bool)
    (h₁ : u (d - 1) = xor (s (d - 1)) a)
    (h₂ : u (d - 2) = xor (s (d - 2)) b)
    (h₃ : u d = xor (s d) c) :
    mix u d = xor (mix s d) (xor (xor a b) c) := by
  unfold mix
  rw [h₁, h₂, h₃]
  simp only [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

lemma box_low : ∀ a b c l : Bool,
    box a b (xor c l) = xor (box a b c) (!b && l) := by decide

lemma box_high : ∀ a b c l u : Bool,
    box a (xor b l) (xor c (xor l u)) =
      xor (box a b c) (advance (l,u) false b c).2 := by decide

lemma mix_front {s v : Tape} {p : Bool × Bool}
    (h : ∀ d, -3 ≤ d → d < 0 → v d = s d)
    (hl : v 0 = xor (s 0) p.1) (hu : v 1 = xor (s 1) p.2) :
    mix v (-1) = mix s (-1) ∧ mix v 0 = xor (mix s 0) p.1 ∧
    mix v 1 = xor (mix s 1) (xor p.1 p.2) := by
  refine ⟨mix_congr (fun j hj hj' => h j (by omega) (by omega)), ?_, ?_⟩
  · simpa using mix_diff s v 0 false false p.1
      (by simpa using h (-1) (by decide) (by decide))
      (by simpa using h (-2) (by decide) (by decide)) hl
  · simpa using mix_diff s v 1 p.1 false p.2 (by simpa using hl)
      (by simpa using h (-1) (by decide) (by decide)) hu

lemma layer_low {s v : Tape} {p : Bool × Bool}
    (h : ∀ d, -4 ≤ d → d < 0 → v d = s d)
    (hl : v 0 = xor (s 0) p.1) (hu : v 1 = xor (s 1) p.2) :
    layer v 0 = xor (layer s 0) (advance p (mix s (-1)) (mix s 0) (mix s 1)).1 := by
  obtain ⟨h₁, h₂, _⟩ := mix_front (fun j h₁ h₂ => h j (by omega) h₂) hl hu
  have hm : mix v (-2) = mix s (-2) := mix_congr (fun j hj hj' => h j (by omega) (by omega))
  change box (mix v (-2)) (mix v (-1)) (mix v 0) = _
  rw [hm, h₁, h₂]
  exact box_low _ _ _ _

lemma layer_high {s v : Tape} {p : Bool × Bool}
    (h : ∀ d, -3 ≤ d → d < 0 → v d = s d)
    (hl : v 0 = xor (s 0) p.1) (hu : v 1 = xor (s 1) p.2) :
    layer v 1 = xor (layer s 1) (advance p (mix s (-1)) (mix s 0) (mix s 1)).2 := by
  obtain ⟨h₁, h₂, h₃⟩ := mix_front h hl hu
  change box (mix v (-1)) (mix v 0) (mix v 1) = _
  rw [h₁, h₂, h₃]
  exact box_high _ _ _ _ _

def controls (x a : Tape) (c : ℕ → Tape) (t : ℕ) := mix (run x a c t)

lemma before_last {k r : ℕ} (hr : 5 ≤ r) (hw : k + 4 = 5 * r) (o : ℤ)
    (x a : Tape) (c : ℕ → Tape) (t : ℕ) (ht : t < r) :
    let s := run x a c t
    let v := run (twist k o 0 x) (twist k o (-1) a) c t
    let p := track (controls x a c) t
    v 0 = xor (s 0) p.1 ∧ v 1 = xor (s 1) p.2 := by
  have hk : 0 < k := by omega
  induction t with
  | zero =>
    change twist k o 0 x 0 = xor (x 0) true ∧ twist k o 0 x 1 = xor (x 1) false
    exact ⟨by simp [twist], by simpa using twist_ne (s := x) (idx_ne hk o (by decide : (0:ℤ) < 1) (by omega))⟩
  | succ t ih =>
    obtain ⟨hl, hu⟩ := ih (by omega)
    have h := fun d (hd : -4 ≤ d) (hd' : d < 0) =>
      unchanged hk o x a c t d hd' (by omega) (by omega)
    have hkey (d : ℤ) (hd : 0 ≤ d) (hd' : d ≤ 1) :
        twist k o (-1) a (d - 5 * t - 3) = a (d - 5 * t - 3) := by
      apply twist_ne
      exact (idx_ne hk o (by omega : d - 5 * t - 3 < -1) (by omega)).symm
    dsimp only
    constructor
    · simp only [run, track]
      rw [layer_low h hl hu, hkey 0 (by decide) (by decide)]
      unfold controls
      simp only [Bool.xor_assoc, Bool.xor_comm]
    · simp only [run, track]
      rw [layer_high (fun d hd hd' => h d (by omega) hd') hl hu, hkey 1 (by decide) (by decide)]
      unfold controls
      simp only [Bool.xor_assoc, Bool.xor_comm]

lemma last_bit {k r : ℕ} (hr : 5 ≤ r) (hw : k + 4 = 5 * r) (o : ℤ)
    (x a : Tape) (c : ℕ → Tape) :
    run x a c r 1 = run (twist k o 0 x) (twist k o (-1) a) c r 1 ↔
      (track (controls x a c) r).2 = true := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega)
  have hk : 0 < k := by omega
  obtain ⟨hl, hu⟩ := before_last hr hw o x a c t (by omega)
  have h := fun d (hd : -3 ≤ d) (hd' : d < 0) =>
    unchanged hk o x a c t d hd' (by omega) (by omega)
  have hi : idx k o (-1) = idx k o (1 - 5 * (t : ℤ) - 3) := by
    apply (idx_dvd hk _ _ _).mpr
    use -1
    omega
  simp only [run, track, layer_high h hl hu, twist_eq hi, controls]
  generalize layer (run x a c t) 1 = b
  generalize a (1 - 5 * (t : ℤ) - 3) = e
  generalize c t 1 = f
  generalize (advance (track (controls x a c) t) (mix (run x a c t) (-1))
    (mix (run x a c t) 0) (mix (run x a c t) 1)).2 = g
  cases b <;> cases e <;> cases f <;> cases g <;> decide


def rot (k s w : ℕ) := ((w <<< (s % k)) ||| (w >>> (k - s % k))) % 2 ^ k

def pack (n : ℕ) (f : ℕ → Bool) :=
  (List.range n).foldl (fun a j => a ||| ((f j).toNat <<< j)) 0

def step (k w : ℕ) :=
  pack k (fun b => box (w.testBit b) (w.testBit ((b + 1) % k)) (w.testBit ((b + 2) % k)))

def mixed (k w : ℕ) := w ^^^ rot k 1 w ^^^ rot k (k - 1) w

def rounds (k : ℕ) (c : ℕ → Fin (2 ^ k)) (start key t : ℕ) :=
  (List.range t).foldl (fun w j => step k (mixed k w) ^^^ rot k (2*j) key ^^^ (c (j+1)).val) start

lemma pack_succ (n : ℕ) (f : ℕ → Bool) :
    pack (n+1) f = pack n f ||| ((f n).toNat <<< n) := by
  simp [pack, List.range_succ]

lemma pack_bit (n : ℕ) (f : ℕ → Bool) (j : ℕ) :
    (pack n f).testBit j = (decide (j < n) && f j) := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    rw [pack_succ, Nat.testBit_or, ih, Nat.shiftLeft_eq]
    by_cases he : n = j
    · subst j
      cases f n <;> simp
    · have hcmp : j < n + 1 ↔ j < n := by omega
      cases f n
      · simp [hcmp]
      · simp [he, hcmp]

lemma pack_lt (n : ℕ) (f : ℕ → Bool) : pack n f < 2^n := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    rw [pack_succ]
    have h : 2^n < (2:ℕ)^(n+1) := Nat.pow_lt_pow_right (by decide) (by omega)
    apply Nat.or_lt_two_pow (ih.trans h)
    cases hf : f n <;> simp [Nat.shiftLeft_eq, h]

lemma rot_lt (k s w : ℕ) : rot k s w < 2^k := Nat.mod_lt _ (by positivity)

lemma rounds_succ (k : ℕ) (c : ℕ → Fin (2 ^ k)) (x a t : ℕ) :
    rounds k c x a (t+1) =
    step k (mixed k (rounds k c x a t)) ^^^ rot k (2*t) a ^^^ (c (t+1)).val := by
  simp [rounds, List.range_succ]

lemma rounds_lt {k : ℕ} (c : ℕ → Fin (2 ^ k)) {x : ℕ} (hx : x < 2^k) (a t : ℕ) :
    rounds k c x a t < 2^k := by
  cases t with
  | zero => exact hx
  | succ t =>
    rw [rounds_succ]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (pack_lt _ _) (rot_lt _ _ _)) (c _).isLt

lemma idx_spec {k : ℕ} (hk : 0 < k) (o z : ℤ) :
    (o+z) ≡ (idx k o z : ℤ) [ZMOD (k : ℤ)] := by
  rw [idx_val hk]
  exact (Int.mod_modEq _ _).symm

lemma idx_rep {k b : ℕ} (hk : 0 < k) (hb : b < k) {o z : ℤ}
    (hm : o+z ≡ (b : ℤ) [ZMOD (k : ℤ)]) : idx k o z = b := by
  change (o+z) % (k:ℤ) = (b:ℤ) % k at hm
  rw [Int.emod_eq_of_lt (by omega : 0 ≤ (b:ℤ)) (by omega : (b:ℤ) < k), ← idx_val hk] at hm
  omega

lemma idx_add {k : ℕ} (hk : 0 < k) (o z : ℤ) (s : ℕ) :
    idx k o (z+s) = (idx k o z + s) % k := by
  apply idx_rep hk (Nat.mod_lt _ hk)
  rw [← add_assoc]
  exact ((idx_spec hk o z).add_right (s:ℤ)).trans
    (Int.natCast_modEq_iff.mpr (Nat.mod_modEq (idx k o z+s) k).symm)

lemma bits_rot {k w : ℕ} (hk : 0 < k) (hw : w < 2^k) (o z : ℤ) (s : ℕ) :
    bits k o (rot k s w) z = bits k o w (z - s) := by
  let j := idx k o z
  let v := s % k
  have hj : j < k := idx_lt hk o z
  have hv : v < k := Nat.mod_lt _ hk
  have hs : (s:ℤ) ≡ (v:ℤ) [ZMOD (k:ℤ)] :=
    Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _).symm
  have hm := (idx_spec hk o z).sub hs
  have hb : o + (z - s) ≡ (j:ℤ) - v [ZMOD (k:ℤ)] := by
    simpa only [add_sub_assoc] using hm
  change (rot k s w).testBit j = w.testBit (idx k o (z - s))
  simp only [rot, Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  change (decide (j < k) && ((decide (v ≤ j) && w.testBit (j-v)) || w.testBit (k-v+j))) = _
  by_cases h : v ≤ j
  · have hi : idx k o (z - s) = j - v := idx_rep hk (by omega)
        (by simpa only [Nat.cast_sub h] using hb)
    have hf := Nat.testBit_lt_two_pow (i := k-v+j) (hw.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h, hj, hi, hf]
  · have hi : idx k o (z - s) = k - v + j := by
      apply idx_rep hk (by omega)
      apply hb.trans
      apply Int.modEq_iff_dvd.mpr
      use 1
      omega
    simp [h, hj, hi]

lemma bits_xor (k : ℕ) (o : ℤ) (x a : ℕ) (z : ℤ) :
    bits k o (x ^^^ a) z = xor (bits k o x z) (bits k o a z) := by
  exact Nat.testBit_xor _ _ _

lemma bits_step {k : ℕ} (hk : 0 < k) (o z : ℤ) (w : ℕ) :
    bits k o (step k w) z = box (bits k o w z) (bits k o w (z+1)) (bits k o w (z+2)) := by
  unfold bits step
  rw [pack_bit, ← idx_add hk o z 1, ← idx_add hk o z 2]
  simp [idx_lt hk]

lemma bits_mixed {k w : ℕ} (hk : 0 < k) (hw : w < 2^k) (o z : ℤ) :
    bits k o (mixed k w) z =
      xor (xor (bits k o w z) (bits k o w (z-1))) (bits k o w (z+1)) := by
  simp only [mixed, bits_xor, bits_rot hk hw, Nat.cast_one]
  have h : idx k o (z - ((k-1:ℕ):ℤ)) = idx k o (z+1) := by
    apply (idx_dvd hk ..).mpr
    use 1
    omega
  unfold bits
  rw [h]

def masks (k : ℕ) (o : ℤ) (c : ℕ → Fin (2 ^ k)) (t : ℕ) : Tape :=
  fun d => bits k o (c (t+1)).val (d - 3*(t+1:ℕ))

lemma rounds_bit {k x a : ℕ} (hk : 0 < k) (hx : x < 2^k) (ha : a < 2^k)
    (o : ℤ) (c : ℕ → Fin (2 ^ k)) (t : ℕ) (d : ℤ) :
    bits k o (rounds k c x a t) (d - 3*t) =
    run (bits k o x) (bits k o a) (masks k o c) t d := by
  induction t generalizing d with
  | zero => simp [rounds, run]
  | succ t ih =>
    let w := rounds k c x a t
    let s := run (bits k o x) (bits k o a) (masks k o c) t
    have hmix (e : ℤ) : bits k o (mixed k w) (e-1-3*t) = mix s e := by
      rw [bits_mixed hk (rounds_lt c hx a t)]
      unfold mix
      have h₁ : e - 1 - 3*t - 1 = (e-2) - 3*t := by omega
      have h₂ : e - 1 - 3*t + 1 = e - 3*t := by omega
      rw [h₁, h₂, ih, ih, ih]
    rw [rounds_succ, bits_xor, bits_xor, bits_step hk, bits_rot hk ha]
    change xor (xor (box _ _ _) _) _ = xor (xor (layer s d) _) _
    have h₀ : d - 3 * ((t+1:ℕ):ℤ) = (d-2)-1-3*t := by omega
    have h₁ : d - 3 * ((t+1:ℕ):ℤ) + 1 = (d-1)-1-3*t := by omega
    have h₂ : d - 3 * ((t+1:ℕ):ℤ) + 2 = d-1-3*t := by omega
    have ha' : d - 3 * ((t+1:ℕ):ℤ) - ((2*t:ℕ):ℤ) = d-5*t-3 := by omega
    unfold masks
    rw [h₁, h₂, ha', h₀, hmix, hmix, hmix]
    rfl


abbrev Pair (k : ℕ) := Fin (2 ^ k) × Fin (2 ^ k)

def byWord {k : ℕ} (w : Fin (2 ^ k)) : Equiv.Perm (Fin (2 ^ k)) where
  toFun x := ⟨x.val ^^^ w.val, Nat.xor_lt_two_pow x.isLt w.isLt⟩
  invFun x := ⟨x.val ^^^ w.val, Nat.xor_lt_two_pow x.isLt w.isLt⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

def single {k : ℕ} (hk : 0 < k) (o d : ℤ) : Fin (2 ^ k) :=
  ⟨2 ^ (idx k o d), Nat.pow_lt_pow_right (by decide) (idx_lt hk o d)⟩

lemma bits_flip {k : ℕ} (hk : 0 < k) (o d : ℤ) (w : Fin (2 ^ k)) :
    bits k o (byWord (single hk o d) w).val = twist k o d (bits k o w.val) := by
  funext j
  simp [byWord, single, bits, twist, Nat.testBit_two_pow]

def obs {k : ℕ} (o : ℤ) (c : ℕ → Tape) (w : Pair k) :=
  controls (bits k o w.1.val) (bits k o w.2.val) c

def border {k : ℕ} (o : ℤ) (c : ℕ → Tape) (t : ℕ) (w : Pair k) := track (obs o c w) t

lemma key_safe {k : ℕ} (hk : 0 < k) (o : ℤ) (x a : Tape) (c : ℕ → Tape)
    {p d : ℤ} (hp : -(k:ℤ) ≤ p) (t : ℕ) (hl : p < d - 5*t + 2) (hu : d ≤ 1) :
    run x (twist k o p a) c t d = run x a c t d := by
  apply run_congr
  · intros; rfl
  · intro j hj hj'
    exact twist_ne (idx_ne hk o (by omega : p < j) (by omega))

lemma obs_safe {k : ℕ} (hk : 0 < k) (o : ℤ) (x a : Tape) (c : ℕ → Tape)
    {p e : ℤ} (hp : -(k:ℤ) ≤ p) (t : ℕ) (hl : p < e - 5*t) (hu : e ≤ 1) :
    controls x (twist k o p a) c t e = controls x a c t e := by
  apply mix_congr
  intro j hj hj'
  apply key_safe hk o x a c hp t <;> omega

lemma obs_toggle {k : ℕ} (hk : 0 < k) (o : ℤ) (x a : Tape) (c : ℕ → Tape)
    (t : ℕ) (d : ℤ) (hu : d ≤ 1) (hp : -(k:ℤ) ≤ d-5*(t+1:ℕ)) :
    let p := d-5*(t+1:ℕ)
    controls x (twist k o p a) c (t+1) d = !(controls x a c (t+1) d) := by
  let p := d-5*(t+1:ℕ)
  let s := run x a c (t+1)
  let v := run x (twist k o p a) c (t+1)
  have hn : v (d-2) = !(s (d-2)) := by
    have h : layer (run x (twist k o p a) c t) (d-2) = layer (run x a c t) (d-2) := by
      apply layer_congr
      intro e he he'
      apply key_safe hk o x a c hp t <;> omega
    have hp' : d-2-5*t-3 = p := by dsimp [p]; omega
    dsimp only [v, s, run]
    rw [h, hp', twist_eq (s := a) (rfl : idx k o p = idx k o p)]
    generalize layer (run x a c t) (d-2) = y
    cases y <;> cases a p <;> cases c t (d-2) <;> decide
  have h₁ : v (d-1) = s (d-1) := key_safe hk o x a c hp (t+1) (by omega) (by omega)
  have h₂ : v d = s d := key_safe hk o x a c hp (t+1) (by omega) hu
  change mix v d = !(mix s d)
  simpa using mix_diff s v d false true false (by simpa using h₁) (by simpa using hn) (by simpa using h₂)

lemma first_toggle {k : ℕ} (hk : 5 ≤ k) (o d : ℤ) (x : Tape) :
    mix (twist k o (d-2) x) d = !(mix x d) := by
  have hk' : 0 < k := by omega
  apply Eq.trans (mix_diff x _ d false true false ?_ ?_ ?_) <;> simp only [Bool.xor_false, Bool.xor_true]
  · rfl
  · exact twist_ne (idx_ne hk' o (by omega : d-2 < d-1) (by omega))
  · exact twist_eq rfl
  · exact twist_ne (idx_ne hk' o (by omega : d-2 < d) (by omega))

lemma shuffle {k r : ℕ} (hr : 5 ≤ r) (hw : k + 4 = 5*r) (o : ℤ) (c : ℕ → Tape)
    (t : ℕ) (ht : t < r) (d : ℤ) (hd : -1 ≤ d) (hd' : d ≤ 1) :
    ∃ E : Equiv.Perm (Pair k), ∀ w,
      border o c t (E w) = border o c t w ∧ obs o c (E w) t d = !(obs o c w t d) ∧
      ∀ e, d < e → e ≤ 1 → obs o c (E w) t e = obs o c w t e := by
  have hk : 0 < k := by omega
  cases t with
  | zero =>
    refine ⟨(byWord (single hk o (d-2))).prodCongr (Equiv.refl _), ?_⟩
    intro w
    change _ ∧ mix (bits k o (byWord (single hk o (d-2)) w.1).val) d = _ ∧
      ∀ e, d < e → e ≤ 1 → mix (bits k o (byWord (single hk o (d-2)) w.1).val) e = _
    rw [bits_flip]
    refine ⟨rfl, first_toggle (by omega) o d _, ?_⟩
    intro e he he'
    apply mix_congr
    intro j hj hj'
    exact twist_ne (idx_ne hk o (by omega : d-2 < j) (by omega))
  | succ t =>
    let p := d-5*(t+1:ℕ)
    have hp : -(k:ℤ) ≤ p := by dsimp [p]; omega
    refine ⟨(Equiv.refl _).prodCongr (byWord (single hk o p)), ?_⟩
    intro w
    let x := bits k o w.1.val
    let a := bits k o w.2.val
    change track (controls x (bits k o (byWord (single hk o p) w.2).val) c) (t+1) = _ ∧
      controls x (bits k o (byWord (single hk o p) w.2).val) c (t+1) d = _ ∧
      ∀ e, d < e → e ≤ 1 → controls x (bits k o (byWord (single hk o p) w.2).val) c (t+1) e = _
    rw [bits_flip]
    refine ⟨?_, obs_toggle hk o x a c t d hd' hp, ?_⟩
    · apply track_congr
      intro j hj e he he'
      apply obs_safe hk o x a c hp j _ he'
      dsimp [p]
      omega
    · intro e he he'
      apply obs_safe hk o x a c hp (t+1) _ he'
      dsimp [p]
      omega


def both (f : Bool → ℕ) := f false + f true

lemma average {X : Type} [Fintype X] (E : Equiv.Perm X) (v : X → Bool) (f : X → Bool → ℕ)
    (hv : ∀ x, v (E x) = !(v x)) (hf : ∀ x b, f (E x) b = f x b) :
    2 * (∑ x, f x (v x)) = ∑ x, both (f x) := by
  calc
    _ = (∑ x, f x (v x)) + ∑ x, f (E x) (v (E x)) := by
      rw [Equiv.sum_comp E (fun x => f x (v x)), two_mul]
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      rw [hv, hf]
      cases v x <;> simp [both, add_comm]

def weight (f : Bool × Bool → ℕ) (p : Bool × Bool) :=
  both fun c => both fun b => both fun a => f (advance p a b c)

lemma count_round {k r : ℕ} (hr : 5 ≤ r) (hw : k + 4 = 5*r) (o : ℤ) (c : ℕ → Tape)
    (t : ℕ) (ht : t < r) (f : Bool × Bool → ℕ) :
    8 * (∑ w : Pair k, f (border o c (t+1) w)) = ∑ w : Pair k, weight f (border o c t w) := by
  let p := border (k := k) o c t
  let v (d : ℤ) (w : Pair k) := obs o c w t d
  obtain ⟨ea, ha⟩ := shuffle hr hw o c t ht (-1) (by decide) (by decide)
  obtain ⟨eb, hb⟩ := shuffle hr hw o c t ht 0 (by decide) (by decide)
  obtain ⟨ec, hc⟩ := shuffle hr hw o c t ht 1 (by decide) (by decide)
  let fa (w : Pair k) (a : Bool) := f (advance (p w) a (v 0 w) (v 1 w))
  let fb (w : Pair k) (b : Bool) := both fun a => f (advance (p w) a b (v 1 w))
  let fc (w : Pair k) (c' : Bool) := both fun b => both fun a => f (advance (p w) a b c')
  have h₁ := average ea (v (-1)) fa (fun w => (ha w).2.1) (by
    intro w a
    dsimp only [fa, p, v]
    rw [(ha w).1, (ha w).2.2 0 (by decide) (by decide), (ha w).2.2 1 (by decide) (by decide)])
  have h₂ := average eb (v 0) fb (fun w => (hb w).2.1) (by
    intro w b
    dsimp only [fb, p, v]
    rw [(hb w).1, (hb w).2.2 1 (by decide) (by decide)])
  have h₃ := average ec (v 1) fc (fun w => (hc w).2.1) (by
    intro w c'
    dsimp only [fc, p]
    rw [(hc w).1])
  change 2 * (∑ w : Pair k, f (border o c (t+1) w)) = ∑ w, fb w (v 0 w) at h₁
  change 2 * (∑ w, fb w (v 0 w)) = ∑ w, fc w (v 1 w) at h₂
  change 2 * (∑ w, fc w (v 1 w)) = ∑ w : Pair k, weight f (border o c t w) at h₃
  omega

def low (p : Bool × Bool) := p.1.toNat

def onlyHigh (p : Bool × Bool) := (!p.1 && p.2).toNat

def high (p : Bool × Bool) := p.2.toNat

lemma weight_low : ∀ p, weight low p = 4 * low p := by decide

lemma weight_only : ∀ p, weight onlyHigh p = 2 * low p + 4 * onlyHigh p := by decide

lemma weight_high : ∀ p, weight high p = 4 * low p + 4 * onlyHigh p := by decide

def total {k : ℕ} (o : ℤ) (c : ℕ → Tape) (t : ℕ) (f : Bool × Bool → ℕ) :=
  ∑ w : Pair k, f (border o c t w)

lemma powers {n t : ℕ} (ht : t+2 ≤ n) :
    2^(n-t) = 4 * (2:ℕ)^(n-(t+2)) ∧ 2^(n-(t+1)) = 2 * (2:ℕ)^(n-(t+2)) := by
  constructor
  · rw [show n-t = 2 + (n-(t+2)) by omega, pow_add]
    rfl
  · rw [show n-(t+1) = 1 + (n-(t+2)) by omega, pow_add, pow_one]

lemma totals {k r : ℕ} (hr : 5 ≤ r) (hw : k + 4 = 5*r) (o : ℤ) (c : ℕ → Tape)
    (t : ℕ) (ht : t ≤ r) :
    total (k := k) o c t low = 2^(2*k-t) ∧
    total (k := k) o c t onlyHigh = t * 2^(2*k-(t+1)) := by
  induction t with
  | zero =>
    simp [total, border, track, low, onlyHigh, Pair, two_mul, pow_add]
  | succ t ih =>
    obtain ⟨hl, ho⟩ := ih (by omega)
    obtain ⟨ha, hb⟩ := powers (n := 2*k) (t := t) (by omega)
    have h₁ := count_round hr hw o c t (by omega) low
    have h₂ := count_round hr hw o c t (by omega) onlyHigh
    simp only [weight_low, weight_only, Finset.sum_add_distrib, ← Finset.mul_sum] at h₁ h₂
    unfold total at hl ho ⊢
    rw [hl, ha] at h₁
    rw [hl, ho, ha, hb] at h₂
    rw [hb]
    constructor <;> nlinarith only [h₁, h₂]

lemma total_high {k r : ℕ} (hr : 5 ≤ r) (hw : k + 4 = 5*r) (o : ℤ) (c : ℕ → Tape) :
    total (k := k) o c r high = (r+1)*2^(2*k-(r+1)) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega)
  obtain ⟨hl, ho⟩ := totals hr hw o c t (by omega)
  obtain ⟨ha, hb⟩ := powers (n := 2*k) (t := t) (by omega)
  have h := count_round hr hw o c t (by omega) high
  simp only [weight_high, Finset.sum_add_distrib, ← Finset.mul_sum] at h
  unfold total at hl ho ⊢
  rw [hl, ho, ha, hb] at h
  nlinarith only [h]


def start {k : ℕ} (w : Pair k) : Fin (2 ^ k) :=
  ⟨rot k 1 w.2.val ^^^ w.1.val, Nat.xor_lt_two_pow (rot_lt _ _ _) w.1.isLt⟩

lemma start_inv {k : ℕ} (w : Pair k) : (start (start w, w.2), w.2) = w := by
  apply Prod.ext
  · apply Fin.ext
    simp [start]
  · rfl

def prepare (k : ℕ) : Equiv.Perm (Pair k) where
  toFun w := (start w, w.2)
  invFun w := (start w, w.2)
  left_inv := start_inv
  right_inv := start_inv

def changed {k : ℕ} (hk : 0 < k) (o : ℤ) (w : Pair k) : Pair k :=
  (w.1, byWord (single hk o (-1)) w.2)

lemma start_change {k : ℕ} (hk : 0 < k) (o : ℤ) (w : Pair k) :
    bits k o (start (changed hk o w)).val = twist k o 0 (bits k o (start w).val) := by
  funext d
  have hi : idx k o (-1) = idx k o (d-1) ↔ idx k o 0 = idx k o d := by
    rw [idx_dvd hk, idx_dvd hk]
    simp
  change bits k o (rot k 1 (byWord (single hk o (-1)) w.2).val ^^^ w.1.val) d =
    xor (bits k o (rot k 1 w.2.val ^^^ w.1.val) d) _
  rw [bits_xor, bits_xor, bits_rot hk (byWord _ w.2).isLt, bits_rot hk w.2.isLt, bits_flip]
  simp only [Nat.cast_one, twist, hi, Bool.xor_assoc, Bool.xor_comm]

lemma event {k r : ℕ} (hr : 5 ≤ r) (hw : k+4 = 5*r) (o : ℤ)
    (c : ℕ → Fin (2 ^ k)) (w : Pair k) :
    let hk : 0 < k := by omega
    let q := changed hk o w
    let j := idx k o (1-3*r)
    (rounds k c (start w).val w.2.val r).testBit j =
        (rounds k c (start q).val q.2.val r).testBit j ↔
      (border o (masks k o c) r (prepare k w)).2 = true := by
  dsimp only
  have hk : 0 < k := by omega
  have hread (v : Pair k) :
      (rounds k c (start v).val v.2.val r).testBit (idx k o (1-3*r)) =
        run (bits k o (start v).val) (bits k o v.2.val) (masks k o c) r 1 :=
    rounds_bit hk (start v).isLt v.2.isLt o c r 1
  rw [hread, hread, start_change]
  change _ = run _ (bits k o (byWord (single hk o (-1)) w.2).val) _ _ _ ↔ _
  rw [bits_flip]
  exact last_bit hr hw o _ _ _


end PEqualNP.Outside.L_meta_25510

open PEqualNP.Outside.L_meta_25510

theorem PEqualNP.Outside.L_meta_25510 : (∀ (k r : ℕ) (constants : ℕ → Fin (2 ^ k)) (i : Fin k),
  5 ≤ r → k + 4 = 5 * r →
  let rot := fun (s word : ℕ) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : ℕ) =>
    (List.range k).foldl (fun acc b =>
      acc ||| ((xor (word.testBit b)
        (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0
  let state := fun (row key : ℕ) =>
    (List.range r).foldl (fun prev t =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * t) key ^^^
        (constants (t + 1)).val) (rot 1 key ^^^ row)
  let flip := fun key : ℕ => key ^^^ (1 <<< ((i.val + 3 * r - 2) % k))
  ((Finset.univ : Finset (Fin (2 ^ k) × Fin (2 ^ k))).filter (fun pair =>
    (state pair.1.val pair.2.val).testBit i.val =
      (state pair.1.val (flip pair.2.val)).testBit i.val)).card =
    (r + 1) * 2 ^ (2 * k - (r + 1))) := by
  intro k r constants i hr hw
  have hk : 0 < k := by omega
  let o : ℤ := (i.val : ℤ) + 3*r - 1
  have hi : idx k o (1-3*r) = i.val := by
    apply idx_rep hk i.isLt
    have h : o + (1-3*r) = i.val := by dsimp [o]; omega
    rw [h]
  have hj : idx k o (-1) = (i.val+3*r-2) % k := by
    have h : o + (-1) = ((i.val+3*r-2 : ℕ):ℤ) := by dsimp [o]; omega
    simp only [idx, h, ← Int.natCast_emod, Int.toNat_natCast]
  dsimp only
  rw [Finset.card_filter]
  calc
    _ = ∑ w : Pair k, high (border o (masks k o constants) r (prepare k w)) := by
      apply Finset.sum_congr rfl
      intro w _
      have h := event hr hw o constants w
      dsimp only at h
      rw [hi] at h
      have hf : (changed hk o w).2.val = w.2.val ^^^ (1 <<< ((i.val+3*r-2)%k)) := by
        simp [changed, byWord, single, hj, Nat.shiftLeft_eq]
      change (if (rounds k constants (start w).val w.2.val r).testBit i.val =
          (rounds k constants (rot k 1 (w.2.val ^^^ (1 <<< ((i.val+3*r-2)%k))) ^^^ w.1.val)
            (w.2.val ^^^ (1 <<< ((i.val+3*r-2)%k))) r).testBit i.val then 1 else 0) = _
      rw [← hf]
      change (if (rounds k constants (start w).val w.2.val r).testBit i.val =
        (rounds k constants (start (changed hk o w)).val (changed hk o w).2.val r).testBit i.val
        then 1 else 0) = _
      simp only [h]
      unfold high
      cases (border o (masks k o constants) r (prepare k w)).2 <;> decide
    _ = total (k := k) o (masks k o constants) r high :=
      Equiv.sum_comp (prepare k) (fun w => high (border o (masks k o constants) r w))
    _ = _ := total_high hr hw o (masks k o constants)
