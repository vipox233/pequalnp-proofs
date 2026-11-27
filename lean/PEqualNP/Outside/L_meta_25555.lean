import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Find
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Data.Finset.Lattice.Fold

namespace PEqualNP.Outside.L_meta_25555_aux

namespace Guard25555Bits

def rot (k s word : ℕ) : ℕ :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def step (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc b =>
    acc ||| ((xor (word.testBit b)
      (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0

def mix (k prev : ℕ) : ℕ := prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev

theorem rot_lt (k s word : ℕ) : rot k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

theorem testBit_rot {k word b : ℕ} (s : ℕ) (hword : word < 2 ^ k) (hb : b < k) :
    (rot k s word).testBit b = word.testBit ((b + (k - s % k)) % k) := by
  have hs : s % k < k := Nat.mod_lt _ (by omega)
  simp only [rot, Nat.testBit_mod_two_pow, hb, decide_true, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : s % k ≤ b
  · have hshift : k ≤ k - s % k + b := by omega
    have hzero : word.testBit (k - s % k + b) = false :=
      Nat.testBit_lt_two_pow (hword.trans_le (Nat.pow_le_pow_right (by decide) hshift))
    have hindex : b + (k - s % k) = (b - s % k) + k := by omega
    simp [h, hzero, hindex, Nat.mod_eq_of_lt (show b - s % k < k by omega)]
  · have hshift : b + (k - s % k) < k := by omega
    simp [h, Nat.mod_eq_of_lt hshift, Nat.add_comm]

private theorem testBit_foldRange (f : ℕ → Bool) (n b : ℕ) :
    ((List.range n).foldl (fun acc j => acc ||| (f j).toNat <<< j) 0).testBit b =
      if b < n then f b else false := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_bool_toNat, ih, Nat.lt_succ_iff]
    rcases lt_trichotomy b n with h | rfl | h
    · simp [h, h.le, Nat.not_le_of_gt h]
    · simp
    · simp [Nat.not_lt_of_ge h.le, Nat.not_le_of_gt h,
        Nat.ne_of_gt (Nat.sub_pos_of_lt h)]

theorem step_lt (k word : ℕ) : step k word < 2 ^ k := by
  by_contra! h
  obtain ⟨b, hb, hbit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow h
  simp [step, testBit_foldRange, Nat.not_lt.mpr hb] at hbit

theorem testBit_step {k b : ℕ} (word : ℕ) (hb : b < k) :
    (step k word).testBit b = xor (word.testBit b)
      (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k)) := by
  unfold step
  rw [testBit_foldRange, ite_eq_left hb]

theorem testBit_step_mod {k : ℕ} (word b : ℕ) (hk : 0 < k) :
    (step k word).testBit (b % k) = xor (word.testBit (b % k))
      (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k)) := by
  simpa only [Nat.mod_add_mod] using testBit_step word (Nat.mod_lt b hk)

theorem testBit_mix {k prev : ℕ} (b : ℕ) (hk : 1 < k) (hprev : prev < 2 ^ k) :
    (mix k prev).testBit (b % k) = xor
      (xor (prev.testBit (b % k)) (prev.testBit ((b + (k - 1)) % k)))
      (prev.testBit ((b + 1) % k)) := by
  have hb := Nat.mod_lt b (show 0 < k by omega)
  have hlast : k - 1 < k := by omega
  have hsub : k - (k - 1) = 1 := by omega
  simp only [mix, Nat.testBit_xor, testBit_rot _ hprev hb, Nat.mod_eq_of_lt hk,
    Nat.mod_eq_of_lt hlast, hsub, Nat.mod_add_mod]

theorem testBit_mix_succ {k prev : ℕ} (b : ℕ) (hk : 1 < k) (hprev : prev < 2 ^ k) :
    (mix k prev).testBit ((b + 1) % k) = xor
      (xor (prev.testBit (b % k)) (prev.testBit ((b + 1) % k)))
      (prev.testBit ((b + 2) % k)) := by
  rw [testBit_mix (b + 1) hk hprev]
  have hindex : b + 1 + (k - 1) = b + k := by omega
  rw [hindex, Nat.add_mod_right]
  exact congrArg (fun bit => xor bit _) (Bool.xor_comm _ _)

def stepLocal (a b c d e : Bool) : Bool :=
  let x := xor (xor a b) c
  let y := xor (xor b c) d
  let z := xor (xor c d) e
  xor x (!y && z)

theorem testBit_stepLocal {k prev : ℕ} (n : ℕ) (hk : 1 < k) (hprev : prev < 2 ^ k) :
    (step k (prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev)).testBit ((n + 1) % k) =
      stepLocal (prev.testBit (n % k)) (prev.testBit ((n + 1) % k))
        (prev.testBit ((n + 2) % k)) (prev.testBit ((n + 3) % k))
        (prev.testBit ((n + 4) % k)) := by
  change (step k (mix k prev)).testBit ((n + 1) % k) = _
  unfold stepLocal
  rw [testBit_step_mod _ _ (show 0 < k by omega), testBit_mix_succ n hk hprev,
    testBit_mix_succ (n + 1) hk hprev, testBit_mix_succ (n + 2) hk hprev]

end Guard25555Bits

namespace Guard25555Inject

def coneIndex (k r i t d : ℕ) : ℕ := i + 3 * (r - t) + k - d

def maskShift (k r e q i : ℕ) : ℕ := i + 3 * r + k - e - q

private theorem offsetEq_of_support {k r e q i t d s a : ℕ}
    (hk : 4 * r + 1 ≤ k) (hbudget : e + q + 4 ≤ r)
    (ht : t ≤ r) (hd : d ≤ 4 * (r - t))
    (hnear : 3 * t + d + s + a < e + q + k)
    (hsupport : coneIndex k r i t d % k = (maskShift k r e q i + s + a) % k) :
    3 * t + d + s + a = e + q := by
  have hbase : coneIndex k r i t d + (3 * t + d) = maskShift k r e q i + (e + q) := by
    unfold coneIndex maskShift
    omega
  have hreorder : maskShift k r e q i + s + a + (3 * t + d) =
      maskShift k r e q i + (3 * t + d + s + a) := by omega
  have hmod : coneIndex k r i t d ≡ maskShift k r e q i + s + a [MOD k] := hsupport
  have hshifted : maskShift k r e q i + (e + q) ≡
      maskShift k r e q i + (3 * t + d + s + a) [MOD k] := by
    simpa only [hbase, hreorder] using hmod.add_right (3 * t + d)
  have hoffset := (Nat.ModEq.add_left_cancel' _ hshifted).symm
  exact le_antisymm (hoffset.le_of_lt_add hnear) (hoffset.symm.le_of_lt_add (by omega))

theorem initial_of_support {k r e q i d a : ℕ}
    (hk : 4 * r + 1 ≤ k) (hbudget : e + q + 4 ≤ r)
    (hd : d ≤ 4 * r) (ha : a < q)
    (hsupport : coneIndex k r i 0 d % k = (maskShift k r e q i + 1 + a) % k) :
    d ≤ e + q - 1 := by
  have hoffset := offsetEq_of_support hk hbudget (Nat.zero_le r)
    (by simpa using hd) (by omega) hsupport
  omega

theorem injection_of_support {k r e q i t d a : ℕ}
    (hk : 4 * r + 1 ≤ k) (hsize : k + e + 3 = 5 * r) (hbudget : e + q + 4 ≤ r)
    (ht : 0 < t) (htr : t < r) (hd : d ≤ 4 * (r - t)) (ha : a < q)
    (hsupport : coneIndex k r i t d % k =
      (maskShift k r e q i + 2 * (t - 1) + a) % k) :
    d ≤ e + q - 1 ∧ t + d ≤ 4 + (e + q - 1) := by

  have hnear : 3 * t + d + 2 * (t - 1) + a < e + q + k := by omega
  have hoffset := offsetEq_of_support hk hbudget htr.le hd hnear hsupport
  omega

def RotBit (k : ℕ) (rot : ℕ → ℕ → ℕ) : Prop :=
  ∀ (s : ℕ) {word b : ℕ}, word < 2 ^ k → b < k →
    (rot s word).testBit b = word.testBit ((b + (k - s % k)) % k)

theorem rotated_key_bit_changes_iff {k key mask shift s b : ℕ} {rot : ℕ → ℕ → ℕ}
    (rotBit : RotBit k rot) (hkey : key < 2 ^ k) (hmaskRot : rot shift mask < 2 ^ k)
    (hb : b < k) :
    ((rot s key).testBit b ≠ (rot s (key ^^^ rot shift mask)).testBit b) ↔
      (rot s (rot shift mask)).testBit b = true := by
  rw [rotBit s hkey hb, rotBit s (Nat.xor_lt_two_pow hkey hmaskRot) hb,
    rotBit s hmaskRot hb, Nat.testBit_xor]
  cases key.testBit ((b + (k - s % k)) % k) <;> simp

private theorem rotation_index_add_mod {k : ℕ} (hk : 0 < k) (s b : ℕ) :
    (((b + (k - s % k)) % k) + s) % k = b % k := by
  have hs := Nat.mod_lt s hk
  have hsum : k - s % k + s % k = k := by omega
  calc
    _ = (b + (k - s % k) + s % k) % k := by
      simp only [Nat.mod_add_mod, Nat.add_mod_mod]
    _ = b % k := by rw [Nat.add_assoc, hsum, Nat.add_mod_right]

theorem rotated_key_bit_support {k q key mask shift s b : ℕ} {rot : ℕ → ℕ → ℕ}
    (rotBit : RotBit k rot) (hkey : key < 2 ^ k) (hmask : mask < 2 ^ q)
    (hqk : q ≤ k) (hmaskRot : rot shift mask < 2 ^ k) (hb : b < k)
    (hchanged : (rot s key).testBit b ≠ (rot s (key ^^^ rot shift mask)).testBit b) :
    ∃ a < q, b = (shift + s + a) % k := by
  have hk : 0 < k := by omega
  let c := (b + (k - s % k)) % k
  let a := (c + (k - shift % k)) % k
  have hc : c < k := Nat.mod_lt _ hk
  have hmaskWidth : mask < 2 ^ k :=
    hmask.trans_le (Nat.pow_le_pow_right (by decide) hqk)
  have hbit := (rotated_key_bit_changes_iff rotBit hkey hmaskRot hb).mp hchanged
  rw [rotBit s hmaskRot hb, rotBit shift hmaskWidth hc] at hbit
  change mask.testBit a = true at hbit
  have ha : a < q := by
    by_contra! hqa
    have hzero := Nat.testBit_lt_two_pow
      (hmask.trans_le (Nat.pow_le_pow_right (by decide) hqa))
    rw [hzero] at hbit
    contradiction
  have hc' : (a + shift) % k = c := by
    simpa only [a, Nat.mod_eq_of_lt hc] using rotation_index_add_mod hk shift c
  have hb' : (c + s) % k = b := by
    simpa only [c, Nat.mod_eq_of_lt hb] using rotation_index_add_mod hk s b
  refine ⟨a, ha, ?_⟩
  calc
    b = (c + s) % k := hb'.symm
    _ = ((a + shift) % k + s) % k := by rw [hc']
    _ = (shift + s + a) % k := by rw [Nat.mod_add_mod]; congr 1; omega

theorem initial_of_bit_change {k r e q i d key mask u : ℕ} {rot : ℕ → ℕ → ℕ}
    (rotBit : RotBit k rot) (hk : 4 * r + 1 ≤ k) (hbudget : e + q + 4 ≤ r)
    (hkey : key < 2 ^ k) (hmask : mask < 2 ^ q) (hmaskRot : rot (maskShift k r e q i) mask < 2 ^ k)
    (hd : d ≤ 4 * r)
    (hchanged : (rot 1 key ^^^ u).testBit (coneIndex k r i 0 d % k) ≠
      (rot 1 (key ^^^ rot (maskShift k r e q i) mask) ^^^ u).testBit (coneIndex k r i 0 d % k)) :
    d ≤ e + q - 1 := by
  rw [Nat.testBit_xor, Nat.testBit_xor] at hchanged
  have hrotChanged := fun h => hchanged (Bool.xor_left_inj.mpr h)
  obtain ⟨a, ha, hpos⟩ := rotated_key_bit_support rotBit hkey hmask (by omega) hmaskRot
    (Nat.mod_lt _ (by omega)) hrotChanged
  exact initial_of_support hk hbudget hd ha hpos

theorem injection_of_bit_change {k r e q i t d key mask : ℕ} {rot : ℕ → ℕ → ℕ}
    (rotBit : RotBit k rot) (hk : 4 * r + 1 ≤ k) (hsize : k + e + 3 = 5 * r)
    (hbudget : e + q + 4 ≤ r) (hkey : key < 2 ^ k) (hmask : mask < 2 ^ q)
    (hmaskRot : rot (maskShift k r e q i) mask < 2 ^ k)
    (ht : 0 < t) (htr : t < r) (hd : d ≤ 4 * (r - t))
    (hchanged : (rot (2 * (t - 1)) key).testBit (coneIndex k r i t d % k) ≠
      (rot (2 * (t - 1)) (key ^^^ rot (maskShift k r e q i) mask)).testBit
        (coneIndex k r i t d % k)) :
    d ≤ e + q - 1 ∧ t + d ≤ 4 + (e + q - 1) := by
  obtain ⟨a, ha, hpos⟩ := rotated_key_bit_support rotBit hkey hmask (by omega) hmaskRot
    (Nat.mod_lt _ (by omega)) hchanged
  exact injection_of_support hk hsize hbudget ht htr hd ha hpos

end Guard25555Inject

private theorem earliestHeightCrossings (r D : ℕ) (H : ℕ → ℕ)
    (h4 : H 4 = 4 + D) (hend : r ≤ H r) (hr : 4 ≤ r)
    (hstep : ∀ t, 4 < t → t ≤ r → H t ≤ H (t - 1) + 1) :
    ∃ times : Fin (r - (4 + D)) → ℕ, StrictMono times ∧
      ∀ j, 5 + j.val ≤ times j ∧ times j ≤ 5 + D + j.val ∧
        times j ≤ r ∧ 4 < times j ∧ H (times j) = 5 + D + j.val ∧
        H (times j - 1) < 5 + D + j.val := by
  have growth (s t : ℕ) (hs : 4 ≤ s) (hst : s ≤ t) (ht : t ≤ r) :
      H t ≤ H s + (t - s) := by
    induction t, hst using Nat.le_induction with
    | base => simp
    | succ t hst ih =>
      have step := hstep (t + 1) (by omega) ht
      simp at step
      have bound := ih (by omega)
      omega
  let count := r - (4 + D)
  let height (j : Fin count) := 5 + D + j.val
  have heightLe (j : Fin count) : height j ≤ r := by
    have hj := j.isLt
    dsimp [count] at hj
    dsimp [height]
    omega
  have existsHit (j : Fin count) : ∃ t, 4 ≤ t ∧ height j ≤ H t :=
    ⟨r, hr, (heightLe j).trans hend⟩
  let times (j : Fin count) := Nat.find (existsHit j)
  have first (j : Fin count) {t : ℕ} (hit : 4 ≤ t ∧ height j ≤ H t) :
      times j ≤ t := Nat.find_min' (existsHit j) hit
  have crossing (j : Fin count) :
      5 + j.val ≤ times j ∧ times j ≤ height j ∧ times j ≤ r ∧ 4 < times j ∧
        H (times j) = height j ∧ H (times j - 1) < height j := by
    have hit : 4 ≤ times j ∧ height j ≤ H (times j) := Nat.find_spec (existsHit j)
    obtain ⟨hstart, hhit⟩ := hit
    have hheight : 4 ≤ height j := by dsimp [height]; omega
    have hlevel := heightLe j
    have toEnd := growth (height j) r hheight hlevel (le_refl r)
    have hupper := first j ⟨hheight, by omega⟩
    have hlast := hupper.trans hlevel
    have fromStart := growth 4 (times j) (le_refl 4) hstart hlast
    rw [h4] at fromStart
    have hlower : 5 + j.val ≤ times j := by
      dsimp [height] at hhit
      omega
    have hpos : 4 < times j := by omega
    have hprev : H (times j - 1) < height j := by
      by_contra! h
      have hle := first j (t := times j - 1) ⟨by omega, h⟩
      omega
    have step := hstep (times j) hpos hlast
    exact ⟨hlower, hupper, hlast, hpos, by omega, hprev⟩
  refine ⟨times, ?_, crossing⟩
  intro i j hij
  have hlevels : height i < height j :=
    Nat.add_lt_add_left (show i.val < j.val from hij) _
  obtain ⟨_, _, _, _, hi, _⟩ := crossing i
  obtain ⟨_, _, _, hj, hjhit, _⟩ := crossing j
  have hle := first i (t := times j) ⟨hj.le, by omega⟩
  apply lt_of_le_of_ne hle
  intro heq
  rw [heq, hjhit] at hi
  omega

private theorem cone (r D : ℕ) (changed guard : ℕ → ℕ → Prop)
    (hr : 4 ≤ r) (hfinal : changed r 0)
    (hinitial : ∀ d, d ≤ 4 * r → changed 0 d → d ≤ D)
    (hparent : ∀ t d, 0 < t → t ≤ r → d ≤ 4 * (r - t) → changed t d →
      (d ≤ D ∧ t + d ≤ 4 + D) ∨ ∃ a ≤ 4, changed (t - 1) (d + a))
    (heven : ∀ t d, 4 < t → t ≤ r → d ≤ 4 * (r - t) → 4 + D < t + d →
      changed t d → (∀ a, 0 < a → a ≤ 4 → ¬ changed (t - 1) (d + a)) → guard t d)
    (hcross : ∀ H : ℕ → ℕ, H 4 = 4 + D → r ≤ H r →
      (∀ t, 4 < t → t ≤ r → H t ≤ H (t - 1) + 1) →
      ∃ times : Fin (r - (4 + D)) → ℕ, StrictMono times ∧ ∀ j,
        5 + j.val ≤ times j ∧ times j ≤ 5 + D + j.val ∧ times j ≤ r ∧
        4 < times j ∧ H (times j) = 5 + D + j.val ∧ H (times j - 1) < 5 + D + j.val) :
    ∃ times : Fin (r - (4 + D)) → ℕ, StrictMono times ∧ ∀ j,
      let t := times j
      let level := 5 + D + j.val
      let g := level - t
      5 + j.val ≤ t ∧ t ≤ level ∧ t ≤ r ∧ g ≤ 4 * (r - t) ∧ guard t g := by
  classical
  let weight t d := if changed t d then t + d else 0
  let H t := max (4 + D) ((Finset.range (4 * (r - t) + 1)).sup (weight t))
  have lower (t d : ℕ) (hd : d ≤ 4 * (r - t)) (hc : changed t d) : t + d ≤ H t := by
    have hmem : d ∈ Finset.range (4 * (r - t) + 1) := Finset.mem_range.mpr (by omega)
    have hb := Finset.le_sup (f := weight t) hmem
    exact le_max_of_le_right (by simpa [weight, hc] using hb)
  have early (t : ℕ) (ht : t ≤ r) (d : ℕ) (hd : d ≤ 4 * (r - t))
      (hc : changed t d) : d ≤ D := by
    induction t generalizing d with
    | zero => exact hinitial d (by simpa using hd) hc
    | succ t ih =>
      rcases hparent (t + 1) d (by omega) ht hd hc with ⟨hD, _⟩ | ⟨a, ha, hp⟩
      · exact hD
      · have bound := ih (by omega) (d + a) (by omega) (by simpa using hp)
        omega
  have hstart : H 4 = 4 + D := by
    apply max_eq_left
    apply Finset.sup_le
    intro d hd
    have hbound : d ≤ 4 * (r - 4) := by have := Finset.mem_range.mp hd; omega
    by_cases hc : changed 4 d
    · have hD := early 4 hr d hbound hc
      simpa [weight, hc] using hD
    · simp [weight, hc]
  have hstep (t : ℕ) (ht : 4 < t) (htr : t ≤ r) : H t ≤ H (t - 1) + 1 := by
    have floor : 4 + D ≤ H (t - 1) := le_max_left _ _
    apply max_le (by omega)
    apply Finset.sup_le
    intro d hd
    have hbound : d ≤ 4 * (r - t) := by have := Finset.mem_range.mp hd; omega
    by_cases hc : changed t d
    · simp only [weight, ite_eq_left hc]
      rcases hparent t d (by omega) htr hbound hc with ⟨_, hi⟩ | ⟨a, ha, hp⟩
      · omega
      · have hp' := lower (t - 1) (d + a) (by omega) hp
        omega
    · simp [weight, hc]
  have hlast : r ≤ H r := by simpa using lower r 0 (by omega) hfinal
  obtain ⟨times, hmono, htimes⟩ := hcross H hstart hlast hstep
  refine ⟨times, hmono, fun j => ?_⟩
  dsimp only
  obtain ⟨hlo, hhi, hr', h4, heq, hprev⟩ := htimes j
  have hs : 5 + D + j.val - 1 < (Finset.range (4 * (r - times j) + 1)).sup (weight (times j)) := by
    change max (4 + D) _ = _ at heq
    omega
  obtain ⟨d, hd, hw⟩ := Finset.lt_sup_iff.mp hs
  have hbound : d ≤ 4 * (r - times j) := by have := Finset.mem_range.mp hd; omega
  have hc : changed (times j) d := by
    by_contra hn
    simp [weight, hn] at hw
  have hw' : 5 + D + j.val ≤ times j + d := by simp [weight, hc] at hw; omega
  have hlower := lower (times j) d hbound hc
  have hdEq : 5 + D + j.val - times j = d := by omega
  refine ⟨hlo, hhi, hr', ?_⟩
  rw [hdEq]
  refine ⟨hbound, heven (times j) d h4 hr' hbound (by omega) hc ?_⟩
  intro a ha h4a hpa
  have hph := lower (times j - 1) (d + a) (by omega) hpa
  omega

private def localBit (a b c d e : Bool) : Bool :=
  Guard25555Bits.stepLocal a b c d e

private theorem localGuard (a b c d e e' : Bool)
    (hne : localBit a b c d e ≠ localBit a b c d e') :
    xor (xor b c) d = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases e' <;>
    simp_all [localBit, Guard25555Bits.stepLocal]

private theorem dynamics (r D : ℕ) (bit injection : Bool → ℕ → ℕ → Bool)
    (step : ∀ side t d, 0 < t → t ≤ r → d ≤ 4 * (r - t) →
      bit side t d = xor (localBit (bit side (t - 1) (d + 4))
        (bit side (t - 1) (d + 3)) (bit side (t - 1) (d + 2))
        (bit side (t - 1) (d + 1)) (bit side (t - 1) d)) (injection side t d))
    (support : ∀ t d, 0 < t → t ≤ r → d ≤ 4 * (r - t) →
      injection false t d ≠ injection true t d → d ≤ D ∧ t + d ≤ 4 + D) :
    (∀ t d, 0 < t → t ≤ r → d ≤ 4 * (r - t) → bit false t d ≠ bit true t d →
      (d ≤ D ∧ t + d ≤ 4 + D) ∨ ∃ a ≤ 4, bit false (t - 1) (d + a) ≠ bit true (t - 1) (d + a)) ∧
    (∀ t d, 4 < t → t ≤ r → d ≤ 4 * (r - t) → 4 + D < t + d →
      bit false t d ≠ bit true t d →
      (∀ a, 0 < a → a ≤ 4 → ¬ bit false (t - 1) (d + a) ≠ bit true (t - 1) (d + a)) →
        xor (xor (bit false (t - 1) (d + 3)) (bit false (t - 1) (d + 2)))
          (bit false (t - 1) (d + 1)) = false) := by
  constructor
  · intro t d ht htr hd hc
    by_cases hi : injection false t d = injection true t d
    · right
      by_contra hn
      have same (a : ℕ) (ha : a ≤ 4) : bit false (t - 1) (d + a) = bit true (t - 1) (d + a) := by
        by_contra h
        exact hn ⟨a, ha, h⟩
      apply hc
      rw [step false t d ht htr hd, step true t d ht htr hd, hi,
        same 4 (by omega), same 3 (by omega), same 2 (by omega), same 1 (by omega),
        show bit false (t - 1) d = bit true (t - 1) d from same 0 (by omega)]
    · exact Or.inl (support t d ht htr hd hi)
  · intro t d ht htr hd hheight hc heq
    have hi : injection true t d = injection false t d := by
      by_contra h
      have hh := support t d (by omega) htr hd (Ne.symm h)
      omega
    have same (a : ℕ) (ha : 0 < a) (ha4 : a ≤ 4) :
        bit true (t - 1) (d + a) = bit false (t - 1) (d + a) :=
      (not_ne_iff.mp (heq a ha ha4)).symm
    rw [step false t d (by omega) htr hd, step true t d (by omega) htr hd, hi,
      same 4 (by omega) (by omega), same 3 (by omega) (by omega),
      same 2 (by omega) (by omega), same 1 (by omega) (by omega)] at hc
    apply localGuard _ _ _ _ (bit false (t - 1) d) (bit true (t - 1) d)
    intro h
    exact hc (congrArg (fun x => xor x (injection false t d)) h)

private def state (k : ℕ) (constants : ℕ → Fin (2 ^ k)) (u key rounds : ℕ) : ℕ :=
  (List.range rounds).foldl (fun prev t =>
    Guard25555Bits.step k (Guard25555Bits.mix k prev) ^^^ Guard25555Bits.rot k (2 * t) key ^^^
      (constants (t + 1)).val) (Guard25555Bits.rot k 1 key ^^^ u)

private theorem state_zero (k : ℕ) (constants : ℕ → Fin (2 ^ k)) (u key : ℕ) :
    state k constants u key 0 = Guard25555Bits.rot k 1 key ^^^ u := rfl

private theorem state_succ (k : ℕ) (constants : ℕ → Fin (2 ^ k)) (u key n : ℕ) :
    state k constants u key (n + 1) =
      Guard25555Bits.step k (Guard25555Bits.mix k (state k constants u key n)) ^^^
        Guard25555Bits.rot k (2 * n) key ^^^ (constants (n + 1)).val := by
  simp only [state, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem state_lt {k u key : ℕ} (constants : ℕ → Fin (2 ^ k)) (hu : u < 2 ^ k)
    (t : ℕ) : state k constants u key t < 2 ^ k := by
  cases t with
  | zero => exact Nat.xor_lt_two_pow (Guard25555Bits.rot_lt _ _ _) hu
  | succ n =>
    rw [state_succ]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Guard25555Bits.step_lt _ _) (Guard25555Bits.rot_lt _ _ _))
      (constants (n + 1)).isLt

private def coord (k r i t d : ℕ) : ℕ := i + 3 * (r - t) + k - d

private theorem coord_prev {k r i t d a : ℕ} (hk : 4 * r + 1 ≤ k) (ht : 0 < t)
    (htr : t ≤ r) (hd : d ≤ 4 * (r - t)) (ha : a ≤ 4) :
    coord k r i (t - 1) (d + a) = coord k r i t d - 1 + (4 - a) := by
  unfold coord
  omega

open Guard25555Bits Guard25555Inject in
private theorem proveGuard (k r e q : ℕ) (constants : ℕ → Fin (2 ^ k)) (u i : ℕ)
    (hq : 0 < q) (hk : 4 * r + 1 ≤ k) (hsize : k + e + 3 = 5 * r)
    (hbudget : e + q + 4 ≤ r) (hu : u < 2 ^ k) (hi : i < k)
    (base : Fin (2 ^ k)) (mask : Fin (2 ^ q))
    (hfinal : let before := fun key =>
      (step k (mix k (state k constants u key (r - 1)))).testBit i
      before base.val ≠ before (base.val ^^^ rot k (maskShift k r e q i) mask.val)) :
    let D := e + q - 1
    ∃ times : Fin (r - (4 + D)) → ℕ, StrictMono times ∧ ∀ j,
      let t := times j
      let level := 5 + D + j.val
      let g := level - t
      let b := coord k r i t g
      let z := state k constants u base.val (t - 1)
      5 + j.val ≤ t ∧ t ≤ level ∧ t ≤ r ∧ g ≤ 4 * (r - t) ∧
        xor (xor (z.testBit (b % k)) (z.testBit ((b + 1) % k)))
          (z.testBit ((b + 2) % k)) = false := by
  dsimp only
  have hr : 4 ≤ r := by omega
  have hk' : 1 < k := by omega
  let key (side : Bool) := if side then base.val ^^^ rot k (maskShift k r e q i) mask.val else base.val
  let z (side : Bool) (t : ℕ) := state k constants u (key side) t
  let bit (side : Bool) (t d : ℕ) :=
    (if t = r then step k (mix k (z side (t - 1))) else z side t).testBit (coord k r i t d % k)
  let inj (side : Bool) (t d : ℕ) :=
    if t = r then false else
      (rot k (2 * (t - 1)) (key side) ^^^ (constants t).val).testBit (coord k r i t d % k)
  let changed t d := bit false t d ≠ bit true t d
  let guard t d := xor (xor (bit false (t - 1) (d + 3)) (bit false (t - 1) (d + 2)))
    (bit false (t - 1) (d + 1)) = false
  have hlast : changed r 0 := by
    simpa [changed, bit, key, z, coord, Nat.mod_eq_of_lt hi] using hfinal
  have hinit (d : ℕ) (hd : d ≤ 4 * r) (hc : changed 0 d) : d ≤ e + q - 1 := by
    have hn : 0 ≠ r := by omega
    apply initial_of_bit_change (rot := rot k) (i := i) (u := u)
      (fun s {word b} hw hb => testBit_rot s hw hb) hk hbudget base.isLt mask.isLt (rot_lt _ _ _) hd
    simpa [changed, bit, z, key, hn, state_zero, coneIndex, coord] using hc
  have hsupport (t d : ℕ) (ht : 0 < t) (htr : t ≤ r) (hd : d ≤ 4 * (r - t))
      (hc : inj false t d ≠ inj true t d) : d ≤ e + q - 1 ∧ t + d ≤ 4 + (e + q - 1) := by
    have hne : t ≠ r := by intro he; simp [inj, he] at hc
    have hc' : (rot k (2 * (t - 1)) base.val).testBit (coneIndex k r i t d % k) ≠
        (rot k (2 * (t - 1)) (base.val ^^^ rot k (maskShift k r e q i) mask.val)).testBit
          (coneIndex k r i t d % k) := by
      intro he
      apply hc
      have he' : (rot k (2 * (t - 1)) base.val).testBit (coord k r i t d % k) =
          (rot k (2 * (t - 1)) (base.val ^^^ rot k (maskShift k r e q i) mask.val)).testBit
            (coord k r i t d % k) := he
      simp [inj, key, hne, Nat.testBit_xor, he']
    exact injection_of_bit_change (rot := rot k) (i := i)
      (fun s {word b} hw hb => testBit_rot s hw hb) hk hsize hbudget base.isLt mask.isLt
      (rot_lt _ _ _) ht (by omega) hd hc'
  have hstep (side : Bool) (t d : ℕ) (ht : 0 < t) (htr : t ≤ r) (hd : d ≤ 4 * (r - t)) :
      bit side t d = xor (localBit (bit side (t - 1) (d + 4))
        (bit side (t - 1) (d + 3)) (bit side (t - 1) (d + 2))
        (bit side (t - 1) (d + 1)) (bit side (t - 1) d)) (inj side t d) := by
    let b := coord k r i t d
    have hb : 0 < b := by dsimp [b, coord]; omega
    have hbp : b - 1 + 1 = b := by omega
    have hp (a : ℕ) (ha : a ≤ 4) :
        bit side (t - 1) (d + a) = (z side (t - 1)).testBit ((b - 1 + (4 - a)) % k) := by
      have hne : t - 1 ≠ r := by omega
      simp only [bit, ite_eq_right hne, coord_prev hk ht htr hd ha, b]
    have hlocal := testBit_stepLocal (b - 1) hk' (state_lt constants hu (t - 1) (key := key side))
    rw [hbp] at hlocal
    change (step k (mix k (z side (t - 1)))).testBit (b % k) = _ at hlocal
    rw [hp 4 (by decide), hp 3 (by decide), hp 2 (by decide), hp 1 (by decide),
      show bit side (t - 1) d = (z side (t - 1)).testBit ((b - 1 + 4) % k) by
        simpa using hp 0 (by decide)]
    have hlocal' : (step k (mix k (z side (t - 1)))).testBit (b % k) =
        localBit ((z side (t - 1)).testBit ((b - 1 + (4 - 4)) % k))
          ((z side (t - 1)).testBit ((b - 1 + (4 - 3)) % k))
          ((z side (t - 1)).testBit ((b - 1 + (4 - 2)) % k))
          ((z side (t - 1)).testBit ((b - 1 + (4 - 1)) % k))
          ((z side (t - 1)).testBit ((b - 1 + 4) % k)) := by
      rw [hlocal]
      simp only [show 4 - 4 = 0 by decide, Nat.add_zero, show 4 - 3 = 1 by decide,
        show 4 - 2 = 2 by decide, show 4 - 1 = 3 by decide, hbp, localBit, stepLocal, z]
    rw [← hlocal']
    by_cases he : t = r
    · simp [bit, inj, he, b]
    · have hz : z side t = step k (mix k (z side (t - 1))) ^^^
          rot k (2 * (t - 1)) (key side) ^^^ (constants t).val := by
        have hh := state_succ k constants u (key side) (t - 1)
        rwa [show t - 1 + 1 = t by omega] at hh
      simp [bit, inj, he, hz, Nat.testBit_xor, b]
  obtain ⟨hparent, heven⟩ := dynamics r (e + q - 1) bit inj hstep hsupport
  obtain ⟨times, hmono, htimes⟩ := cone r (e + q - 1) changed guard hr hlast hinit
    hparent heven (fun H h4 hend hstep => earliestHeightCrossings r (e + q - 1) H h4 hend hr hstep)
  refine ⟨times, hmono, fun j => ?_⟩
  obtain ⟨ht, hlevel, htr, hd, hg⟩ := htimes j
  let t := times j
  let d := 5 + (e + q - 1) + j.val - t
  have hne : t - 1 ≠ r := by dsimp [t]; omega
  have hcoord (a : ℕ) (ha : a ≤ 3) :
      coord k r i (t - 1) (d + (3 - a)) = coord k r i t d + a := by
    unfold coord
    dsimp only [t, d] at *
    omega
  change xor (xor (bit false (t - 1) (d + (3 - 0))) (bit false (t - 1) (d + (3 - 1))))
    (bit false (t - 1) (d + (3 - 2))) = false at hg
  simp only [bit, ite_eq_right hne, hcoord 0 (by decide), hcoord 1 (by decide), hcoord 2 (by decide),
    Nat.add_zero, z, key, Bool.false_eq_true, ite_false] at hg
  exact ⟨ht, hlevel, htr, hd, hg⟩

end PEqualNP.Outside.L_meta_25555_aux

theorem PEqualNP.Outside.L_meta_25555 : (∀ (k r e q : ℕ) (constants : ℕ → Fin (2 ^ k)) (u i : ℕ),
  0 < q → 4 * r + 1 ≤ k → k + e + 3 = 5 * r → e + q + 4 ≤ r → u < 2 ^ k → i < k →
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
  let D := e + q - 1
  ∀ (base : Fin (2 ^ k)) (mask : Fin (2 ^ q)),
    before base.val ≠ before (base.val ^^^ rot (i + 3 * r + k - e - q) mask.val) →
    ∃ times : Fin (r - (4 + D)) → ℕ, StrictMono times ∧
      ∀ j, let t := times j
           let level := 5 + D + j.val
           let g := level - t
           let b := i + 3 * (r - t) + k - g
           let z := state base.val (t - 1)
           5 + j.val ≤ t ∧ t ≤ level ∧ t ≤ r ∧ g ≤ 4 * (r - t) ∧
             xor (xor (z.testBit (b % k)) (z.testBit ((b + 1) % k)))
               (z.testBit ((b + 2) % k)) = false) := by
  intro k r e q constants u i hq hk hsize hbudget hu hi
  dsimp only
  intro base mask hfinal
  exact PEqualNP.Outside.L_meta_25555_aux.proveGuard k r e q constants u i hq hk hsize hbudget hu hi base mask hfinal
