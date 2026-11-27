import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_meta_29762

abbrev B := ZMod 2
abbrev W (k : ℕ) := ZMod k → B

variable {k : ℕ} [NeZero k]

lemma add_bit (a : B) : a + a = 0 := by
  have h : (2 : B) = 0 := by decide
  rw [← two_mul, h, zero_mul]

lemma add_word (a : W k) : a + a = 0 := funext fun i => add_bit (a i)

lemma bit_zero {a b : B} : a + b = 0 ↔ a = b := by
  have h : -b = b := neg_eq_of_add_eq_zero_right (add_bit b)
  rw [add_eq_zero_iff_eq_neg, h]

def rot (s : ℕ) (x : W k) (i : ZMod k) : B := x (i - s)

def mix (s : ℕ) : W k →ₗ[B] W k where
  toFun x i := x (i - s) + x i + x (i + s)
  map_add' x y := by
    funext i
    change (x _ + y _) + (x i + y i) + (x _ + y _) = _
    simp only [Pi.add_apply]
    ring
  map_smul' a x := by
    funext i
    change a * x _ + a * x i + a * x _ = _
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

lemma mix_at (s : ℕ) (x : W k) (i : ZMod k) :
    mix s x i = x (i - s) + x i + x (i + s) := rfl

lemma ker_period (s : ℕ) {x : W k} (hx : mix s x = 0) (i : ZMod k) :
    x (i + 3 * s) = x i := by
  have a := congrFun hx (i + s)
  have b := congrFun hx (i + 2 * s)
  rw [mix_at, add_sub_cancel_right, show i + s + s = i + 2 * s by ring] at a
  rw [mix_at, show i + 2 * s - s = i + s by ring,
    show i + 2 * s + s = i + 3 * s by ring] at b
  change x i + x (i + s) + x (i + 2 * s) = 0 at a
  change x (i + s) + x (i + 2 * s) + x (i + 3 * s) = 0 at b
  linear_combination b - a

lemma mix_bij (hk3 : k % 3 ≠ 0) (s : ℕ) : Function.Bijective (mix (k := k) s) := by
  apply Finite.injective_iff_bijective.mp
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro x hx
  change mix s x = 0 at hx
  have hp (m : ℕ) (i : ZMod k) : x (i + (m : ZMod k) * (3 * s)) = x i := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.cast_succ, show i + ((m : ZMod k) + 1) * (3 * s) =
        (i + (m : ZMod k) * (3 * s)) + 3 * s by ring, ker_period s hx, ih]
  have hk0 : (k : ZMod k) = 0 := ZMod.natCast_self k
  have hstep (i : ZMod k) : x (i + s) = x i := by
    have hk12 : k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hk12 with h1 | h2
    · have e := hp (k / 3) (i + s)
      have ec := congrArg (fun n : ℕ => (n : ZMod k)) (show 3 * (k / 3) + 1 = k by omega)
      push_cast at ec
      rw [hk0] at ec
      rw [show i + s + (↑(k / 3) : ZMod k) * (3 * s) = i by
        linear_combination (s : ZMod k) * ec] at e
      exact e.symm
    · have e := hp (k / 3 + 1) i
      have ec := congrArg (fun n : ℕ => (n : ZMod k)) (show 3 * (k / 3 + 1) = k + 1 by omega)
      push_cast at ec e
      rw [hk0, zero_add] at ec
      rw [show i + ((↑(k / 3) : ZMod k) + 1) * (3 * s) = i + s by
        linear_combination (s : ZMod k) * ec] at e
      exact e
  funext i
  have hn : x (i - s) = x i := by
    simpa only [sub_add_cancel] using (hstep (i - s)).symm
  have e := congrFun hx i
  rwa [mix_at, hn, hstep, add_bit, zero_add] at e

def chi (z : W k) (i : ZMod k) : B :=
  z i + (1 + z (i + 1)) * z (i + 2)

def chiDiff (d z : W k) (i : ZMod k) : B :=
  chi d i + z (i + 1) * d (i + 2) + z (i + 2) * d (i + 1)

lemma chi_diff (d z : W k) :
    chi (z + d) = chi z + chiDiff d z := by
  funext i
  simp only [chi, chiDiff, Pi.add_apply]
  ring

lemma intCast_index_inj (hk : 7 ≤ k) (i : ZMod k) {a b : ℤ}
    (hl : a - b < 7) (hr : b - a < 7) :
    i + (a : ZMod k) = i + (b : ZMod k) ↔ a = b := by
  refine ⟨fun he => ?_, fun he => by rw [he]⟩
  have hc := add_left_cancel he
  have hz : ((a - b : ℤ) : ZMod k) = 0 := by rw [Int.cast_sub, hc, sub_self]
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - b) k).mp hz
  have hpos : (7 : ℤ) ≤ k := by exact_mod_cast hk
  by_cases h0 : m = 0
  · simp [h0] at hm
    omega
  · rcases lt_or_gt_of_ne h0 with hneg | hposm
    · have hle := mul_le_mul_of_nonneg_left (show m ≤ -1 by omega) (show (0 : ℤ) ≤ k by omega)
      push_cast at hle hm
      simp only [mul_neg, mul_one] at hle
      omega
    · have hle := mul_le_mul_of_nonneg_left (show 1 ≤ m by omega) (show (0 : ℤ) ≤ k by omega)
      push_cast at hle hm
      simp only [mul_one] at hle
      omega

def spike (i : ZMod k) (z : B) : W k := fun j => if j = i then z else 0

lemma outer_diff (hk : 7 ≤ k) (i : ZMod k) (d : W k) (u : B) :
    (∀ y : W k, chiDiff d y i = u) ↔
      d (i + 1) = 0 ∧ d (i + 2) = 0 ∧ d i = u := by
  have hi : i + 1 ≠ i + 2 := by
    intro eq
    have e := (intCast_index_inj hk i (a := 1) (b := 2) (by decide) (by decide)).mp (by simpa using eq)
    omega
  constructor
  · intro eq
    have e0 := eq 0
    have e1 := eq (spike (i + 1) 1)
    have e2 := eq (spike (i + 2) 1)
    simp [chiDiff, spike, hi, Ne.symm hi] at e0 e1 e2
    have h1 : d (i + 1) = 0 := by simpa [e0] using e2
    have h2 : d (i + 2) = 0 := by simpa [e0] using e1
    exact ⟨h1, h2, by simpa [chi, h2] using e0⟩
  · rintro ⟨h1, h2, h0⟩ y
    simp [chiDiff, chi, h1, h2, h0]

def atOffset (i : ZMod k) (n : ℤ) : ZMod k := i + n

lemma offset_add (i : ZMod k) (a b : ℤ) :
    atOffset (atOffset i a) b = atOffset i (a + b) := by
  simp [atOffset, add_assoc]

lemma affine_coeff {n : ℕ} (idx : Fin n → ZMod k) (hi : Function.Injective idx)
    (c : Fin n → B) (b u : B) :
    (∀ z : W k, b + ∑ j, z (idx j) * c j = u) ↔ b = u ∧ c = 0 := by
  classical
  constructor
  · intro h
    have hb : b = u := by simpa using h 0
    refine ⟨hb, funext fun j => ?_⟩
    have e := h (spike (idx j) 1)
    rw [Finset.sum_eq_single j] at e
    · simpa [spike, hb] using e
    · intro a _ ha
      have hn : idx a ≠ idx j := fun e => ha (hi e)
      simp [spike, hn]
    · simp
  · rintro ⟨rfl, rfl⟩ z
    simp

def rowIdx (i : ZMod k) (j : Fin 4) : ZMod k := atOffset i (j.val : ℤ)

def colIdx (i : ZMod k) (j : Fin 6) : ZMod k := atOffset i ((j.val : ℤ) - 1)

lemma row_diff (hk : 7 ≤ k) (i : ZMod k) (d : W k) (u : B) :
    (∀ z, mix 1 (chiDiff d z) i = u) ↔
      (∀ j : Fin 4, d (rowIdx i j) = 0) ∧
      d (i - 1) + d i + d (i + 1) = u := by
  let c : Fin 4 → B := ![d (i+1), d i + d (i+2), d (i+1) + d (i+3), d (i+2)]
  have hi : Function.Injective (rowIdx i) := by
    intro a b e
    have h := (intCast_index_inj hk i (a := a.val) (b := b.val)
      (by have := a.isLt; omega) (by have := b.isLt; omega)).mp e
    exact Fin.ext (by omega)
  have e (z : W k) : mix 1 (chiDiff d z) i =
      mix 1 (chi d) i + ∑ j : Fin 4, z (rowIdx i j) * c j := by
    simp [mix_at, chiDiff, Fin.sum_univ_succ, rowIdx, atOffset, c]
    ring_nf
  have eq := affine_coeff (rowIdx i) hi c (mix 1 (chi d) i) u
  simp_rw [e]
  rw [eq]
  have hc : c = 0 ↔ ∀ j : Fin 4, d (rowIdx i j) = 0 := by
    have he : (∀ j : Fin 4, d (rowIdx i j) = 0) ↔
        d i = 0 ∧ d (i+1) = 0 ∧ d (i+2) = 0 ∧ d (i+3) = 0 := by
      constructor
      · intro h
        exact ⟨by simpa [rowIdx, atOffset] using h 0, by simpa [rowIdx, atOffset] using h 1,
          by simpa [rowIdx, atOffset] using h 2, by simpa [rowIdx, atOffset] using h 3⟩
      · rintro ⟨a, b, c, d₃⟩ j
        fin_cases j <;> simpa [rowIdx, atOffset] using ‹_›
    rw [he]
    simp [c, funext_iff, Fin.forall_fin_succ]
    aesop
  rw [hc]
  constructor
  · rintro ⟨hu, hz⟩
    have a := hz 0
    have b := hz 1
    have c := hz 2
    have d₃ := hz 3
    simp [rowIdx, atOffset] at a b c d₃
    refine ⟨hz, ?_⟩
    simpa [mix_at, chi, a, b, c, d₃, show i - 1 + 2 = i + 1 by ring,
      show i + 1 + 2 = i + 3 by ring] using hu
  · rintro ⟨hz, hu⟩
    have b := hz 1
    have c := hz 2
    have d₃ := hz 3
    simp [rowIdx, atOffset] at b c d₃
    refine ⟨?_, hz⟩
    simpa [mix_at, chi, b, c, d₃, show i - 1 + 2 = i + 1 by ring,
      show i + 1 + 2 = i + 3 by ring] using hu

lemma col_diff (hk : 7 ≤ k) (i : ZMod k) (d : W k) (u : B) :
    (∀ z, mix 2 (chiDiff d z) i = u) ↔
      (∀ j : Fin 6, d (colIdx i j) = 0) ∧
      d (i - 2) + d i + d (i + 2) = u := by
  let c : Fin 6 → B := ![d i, d (i-1), d (i+2), d (i+1), d (i+4), d (i+3)]
  have hi : Function.Injective (colIdx i) := by
    intro a b e
    have h := (intCast_index_inj hk i (a := (a.val : ℤ) - 1) (b := (b.val : ℤ) - 1)
      (by have := a.isLt; omega) (by have := b.isLt; omega)).mp e
    exact Fin.ext (by omega)
  have e (z : W k) : mix 2 (chiDiff d z) i =
      mix 2 (chi d) i + ∑ j : Fin 6, z (colIdx i j) * c j := by
    simp [mix_at, chiDiff, Fin.sum_univ_succ, colIdx, atOffset, c]
    ring_nf
  have eq := affine_coeff (colIdx i) hi c (mix 2 (chi d) i) u
  simp_rw [e]
  rw [eq]
  have hc : c = 0 ↔ ∀ j : Fin 6, d (colIdx i j) = 0 := by
    simp [c, funext_iff, Fin.forall_fin_succ, colIdx, atOffset]
    norm_num [sub_eq_add_neg]
    simp [and_assoc, and_left_comm, and_comm]
  rw [hc]
  constructor
  · rintro ⟨hu, hz⟩
    have a := hz 1
    have b := hz 3
    have c := hz 5
    simp [colIdx, atOffset] at a b c
    refine ⟨hz, ?_⟩
    simpa [mix_at, chi, a, b, c, show i - 2 + 2 = i by ring,
      show i + 2 + 2 = i + 4 by ring] using hu
  · rintro ⟨hz, hu⟩
    have a := hz 1
    have b := hz 3
    have c := hz 5
    simp [colIdx, atOffset] at a b c
    refine ⟨?_, hz⟩
    simpa [mix_at, chi, a, b, c, show i - 2 + 2 = i by ring,
      show i + 2 + 2 = i + 4 by ring] using hu

def run (s a b c : ℕ) (key name c₁ c₂ : W k) : W k :=
  chi (mix s (chi (mix s (rot a key + name)) + rot b key + c₁)) + rot c key + c₂

def lane (s a b c h : ℕ) (start : ZMod k) (c₁ c₂ dn dk : W k) : Prop :=
  ∀ (name key : W k) (q : Fin h),
    run s a b c (key + dk) (name + dn) c₁ c₂ (atOffset start q.val) =
      run s a b c key name c₁ c₂ (atOffset start q.val)

lemma rot_add (s : ℕ) (x y : W k) : rot s (x + y) = rot s x + rot s y := rfl

lemma rot_surj (s : ℕ) : Function.Surjective (rot (k := k) s) := by
  intro x
  refine ⟨fun i => x (i + s), ?_⟩
  ext i
  simp [rot]

lemma run_diff (s a b c : ℕ) (key name c₁ c₂ dn dk : W k) :
    let z := mix s (rot a key + name)
    let y := mix s (chi z + rot b key + c₁)
    let d := mix s (rot a dk + dn)
    let δ := mix s (chiDiff d z + rot b dk)
    run s a b c (key + dk) (name + dn) c₁ c₂ =
      run s a b c key name c₁ c₂ + (chiDiff δ y + rot c dk) := by
  dsimp only [run]
  rw [rot_add a, show rot a key + rot a dk + (name + dn) =
    (rot a key + name) + (rot a dk + dn) by abel,
    map_add (mix s) (rot a key + name), chi_diff (mix s (rot a dk + dn)),
    rot_add b, show chi (mix s (rot a key + name)) +
        chiDiff (mix s (rot a dk + dn)) (mix s (rot a key + name)) +
        (rot b key + rot b dk) + c₁ =
      (chi (mix s (rot a key + name)) + rot b key + c₁) +
        (chiDiff (mix s (rot a dk + dn)) (mix s (rot a key + name)) + rot b dk) by abel,
    map_add, chi_diff, rot_add c]
  abel

lemma run_inputs (hk3 : k % 3 ≠ 0) (s a b : ℕ) (c₁ z y : W k) :
    ∃ (name key : W k), mix s (rot a key + name) = z ∧
      mix s (chi z + rot b key + c₁) = y := by
  obtain ⟨Y, hY⟩ := (mix_bij hk3 s).2 y
  obtain ⟨key, hkey⟩ := rot_surj b (Y - chi z - c₁)
  obtain ⟨Z, hZ⟩ := (mix_bij hk3 s).2 z
  refine ⟨Z - rot a key, key, ?_, ?_⟩
  · rwa [show rot a key + (Z - rot a key) = Z by abel]
  · rwa [hkey, show chi z + (Y - chi z - c₁) + c₁ = Y by abel]

lemma lane_iff (hk : 7 ≤ k) (hk3 : k % 3 ≠ 0) (s a b c h : ℕ)
    (start : ZMod k) (c₁ c₂ dn dk : W k) :
    lane s a b c h start c₁ c₂ dn dk ↔
      ∀ (z : W k) (q : Fin h),
        let δ := mix s (chiDiff (mix s (rot a dk + dn)) z + rot b dk)
        let i := atOffset start q.val
        δ (i + 1) = 0 ∧ δ (i + 2) = 0 ∧ δ i = rot c dk i := by
  constructor
  · intro hp z q
    apply (outer_diff hk _ _ _).mp
    intro y
    obtain ⟨name, key, ez, ey⟩ := run_inputs hk3 s a b c₁ z y
    have eq := hp name key q
    rw [run_diff, ez, ey] at eq
    exact bit_zero.mp (add_left_cancel (eq.trans (add_zero _).symm))
  · intro hp name key q
    have hd := (outer_diff hk _ _ _).mpr (hp (mix s (rot a key + name)) q)
      (mix s (chi (mix s (rot a key + name)) + rot b key + c₁))
    simp only [run_diff, Pi.add_apply, hd, add_bit, add_zero]

lemma offset_step (i : ZMod k) (a b : ℤ) :
    atOffset i a + (b : ZMod k) = atOffset i (a + b) := by
  simp [atOffset, add_assoc]

lemma lane_window (s a b c h : ℕ) (hh : 2 ≤ h) (start : ZMod k) (dn dk : W k) :
    (∀ (z : W k) (q : Fin h),
      let δ := mix s (chiDiff (mix s (rot a dk + dn)) z + rot b dk)
      let i := atOffset start q.val
      δ (i + 1) = 0 ∧ δ (i + 2) = 0 ∧ δ i = rot c dk i) ↔
    ((∀ (z : W k),
      mix s (chiDiff (mix s (rot a dk + dn)) z + rot b dk) start = rot c dk start) ∧
     (∀ (z : W k) (j : ℤ), 1 ≤ j → j ≤ (h : ℤ) + 1 →
      mix s (chiDiff (mix s (rot a dk + dn)) z + rot b dk) (atOffset start j) = 0) ∧
     (∀ j : ℤ, 1 ≤ j → j < (h : ℤ) → rot c dk (atOffset start j) = 0)) := by
  constructor
  · intro hp
    have hz (z : W k) (j : ℤ) (hj : 1 ≤ j) (hj' : j ≤ (h : ℤ) + 1) :
        mix s (chiDiff (mix s (rot a dk + dn)) z + rot b dk) (atOffset start j) = 0 := by
      by_cases he : j = (h : ℤ) + 1
      · let q : Fin h := ⟨h - 1, by omega⟩
        have e := (hp z q).2.1
        rw [show (2 : ZMod k) = ((2 : ℤ) : ZMod k) by norm_num, offset_step] at e
        exact (show (q.val : ℤ) + 2 = j by dsimp [q]; omega) ▸ e
      · let q : Fin h := ⟨(j - 1).toNat, by omega⟩
        have e := (hp z q).1
        rw [show (1 : ZMod k) = ((1 : ℤ) : ZMod k) by norm_num, offset_step] at e
        exact (show (q.val : ℤ) + 1 = j by dsimp [q]; omega) ▸ e
    refine ⟨fun z => ?_, hz, fun j hj hj' => ?_⟩
    · simpa [atOffset] using (hp z ⟨0, by omega⟩).2.2
    · let q : Fin h := ⟨j.toNat, by omega⟩
      have e : (q.val : ℤ) = j := by dsimp [q]; omega
      have hq := (hp 0 q).2.2
      rw [e, hz 0 j hj (by omega)] at hq
      exact hq.symm
  · rintro ⟨head, hz, tail⟩ z q
    have bq := q.isLt
    refine ⟨?_, ?_, ?_⟩
    · rw [show (1 : ZMod k) = ((1 : ℤ) : ZMod k) by norm_num, offset_step]
      exact hz z _ (by omega) (by omega)
    · rw [show (2 : ZMod k) = ((2 : ℤ) : ZMod k) by norm_num, offset_step]
      exact hz z _ (by omega) (by omega)
    · by_cases eq : q.val = 0
      · simpa [eq, atOffset] using head z
      · rw [hz z _ (by omega) (by omega), tail _ (by omega) (by omega)]

def zeros (start : ZMod k) (x : W k) (lo hi : ℤ) : Prop :=
  ∀ j : ℤ, lo ≤ j → j ≤ hi → x (atOffset start j) = 0

lemma diff_at (hk : 7 ≤ k) (s : ℕ) (hs : s = 1 ∨ s = 2)
    (i : ZMod k) (d : W k) (u : B) :
    (∀ z, mix s (chiDiff d z) i = u) ↔
      zeros i d (1 - (s : ℤ)) (2 + (s : ℤ)) ∧ d (i - s) = u := by
  rcases hs with rfl | rfl
  · rw [row_diff hk]
    have he : (∀ j : Fin 4, d (rowIdx i j) = 0) ↔ zeros i d 0 3 := by
      constructor
      · intro h j hl hr
        let m : Fin 4 := ⟨j.toNat, by omega⟩
        have hm : (m.val : ℤ) = j := by dsimp [m]; omega
        simpa only [rowIdx, hm] using h m
      · intro h j
        exact h j.val (by positivity) (by have := j.isLt; omega)
    norm_num
    rw [he]
    constructor <;> rintro ⟨hz, eq⟩ <;> refine ⟨hz, ?_⟩
    all_goals
      have h0 : d i = 0 := by simpa [atOffset] using hz 0 (by decide) (by decide)
      have h1 : d (i+1) = 0 := by simpa [atOffset] using hz 1 (by decide) (by decide)
      simpa [h0, h1] using eq
  · rw [col_diff hk]
    have he : (∀ j : Fin 6, d (colIdx i j) = 0) ↔ zeros i d (-1) 4 := by
      constructor
      · intro h j hl hr
        let m : Fin 6 := ⟨(j+1).toNat, by omega⟩
        have hm : (m.val : ℤ) - 1 = j := by dsimp [m]; omega
        simpa only [colIdx, hm] using h m
      · intro h j
        exact h (j.val - 1 : ℤ) (by have := j.isLt; omega) (by have := j.isLt; omega)
    norm_num
    rw [he]
    constructor <;> rintro ⟨hz, eq⟩ <;> refine ⟨hz, ?_⟩
    all_goals
      have h0 : d i = 0 := by simpa [atOffset] using hz 0 (by decide) (by decide)
      have h2 : d (i+2) = 0 := by simpa [atOffset] using hz 2 (by decide) (by decide)
      simpa [h0, h2] using eq

lemma diff_window (hk : 7 ≤ k) (s : ℕ) (hs : s = 1 ∨ s = 2) (h : ℕ)
    (start : ZMod k) (d : W k) (f : ℤ → B) :
    (∀ (j : ℤ), 0 ≤ j → j ≤ (h : ℤ) + 1 → ∀ z,
      mix s (chiDiff d z) (atOffset start j) = f j) ↔
    zeros start d (1 - (s : ℤ)) ((h : ℤ) + 3 + s) ∧
      d (atOffset start (-(s : ℤ))) = f 0 ∧
      ∀ j : ℤ, 1 ≤ j → j ≤ (h : ℤ) + 1 → f j = 0 := by
  have hs₁ : 1 ≤ s := by omega
  have hs₂ : s ≤ 2 := by omega
  have he (j : ℤ) : atOffset start j - (s : ZMod k) = atOffset start (j - s) := by
    simp [atOffset, sub_eq_add_neg, add_assoc]
  constructor
  · intro H
    have localZero (j : ℤ) (hj : 0 ≤ j) (hj' : j ≤ (h : ℤ) + 1) :=
      (diff_at hk s hs (atOffset start j) d (f j)).mp (H j hj hj')
    have hz : zeros start d (1 - (s : ℤ)) ((h : ℤ) + 3 + s) := by
      intro j hj hj'
      let q : ℤ := max 0 (j - (2 + s))
      have hq := (localZero q (by dsimp [q]; omega) (by dsimp [q]; omega)).1 (j-q)
        (by dsimp [q]; omega) (by dsimp [q]; omega)
      rwa [offset_add, show q + (j-q) = j by omega] at hq
    refine ⟨hz, ?_, ?_⟩
    · simpa only [he, zero_sub] using (localZero 0 (by omega) (by omega)).2
    · intro j hj hj'
      rw [← (localZero j (by omega) hj').2, he]
      exact hz _ (by omega) (by omega)
  · rintro ⟨hz, head, tail⟩ j hj hj'
    apply (diff_at hk s hs _ _ _).mpr
    refine ⟨?_, ?_⟩
    · intro l hl hl'
      rw [offset_add]
      exact hz _ (by omega) (by omega)
    · rw [he]
      by_cases eq : j = 0
      · simpa [eq] using head
      · rw [tail j (by omega) hj']
        exact hz _ (by omega) (by omega)

set_option maxHeartbeats 1500000 in
lemma lane_linear (hk : 7 ≤ k) (hk3 : k % 3 ≠ 0) (s : ℕ) (hs : s = 1 ∨ s = 2)
    (a b c h : ℕ) (hh : 2 ≤ h) (start : ZMod k) (c₁ c₂ dn dk : W k) :
    lane s a b c h start c₁ c₂ dn dk ↔
      let d := mix s (rot a dk + dn)
      let m := mix s (rot b dk)
      zeros start d (1 - (s : ℤ)) ((h : ℤ) + 3 + s) ∧
      d (atOffset start (-(s : ℤ))) + m start = rot c dk start ∧
      zeros start m 1 ((h : ℤ) + 1) ∧
      zeros start (rot c dk) 1 ((h : ℤ) - 1) := by
  classical
  rw [lane_iff hk hk3, lane_window s a b c h hh]
  let d := mix s (rot a dk + dn)
  let m := mix s (rot b dk)
  let f : ℤ → B := fun j => (if j = 0 then rot c dk start else 0) - m (atOffset start j)
  have head : atOffset start 0 = start := by simp [atOffset]
  have H : (∀ j : ℤ, 0 ≤ j → j ≤ (h : ℤ) + 1 → ∀ z,
      mix s (chiDiff d z) (atOffset start j) = f j) ↔
      ((∀ z, mix s (chiDiff d z + rot b dk) start = rot c dk start) ∧
       (∀ z j, 1 ≤ j → j ≤ (h : ℤ) + 1 →
         mix s (chiDiff d z + rot b dk) (atOffset start j) = 0)) := by
    constructor
    · intro eq
      refine ⟨fun z => ?_, fun z j hj hj' => ?_⟩
      · have e := eq 0 (by decide) (by omega) z
        simpa [f, head, ← eq_sub_iff_add_eq, m, map_add, Pi.add_apply] using e
      · have e := eq j (by omega) hj' z
        simpa [f, show j ≠ 0 by omega, ← eq_sub_iff_add_eq, m, map_add, Pi.add_apply] using e
    · rintro ⟨h₀, h₁⟩ j hj hj' z
      by_cases eq : j = 0
      · simpa [eq, f, head, ← eq_sub_iff_add_eq, m, map_add, Pi.add_apply] using h₀ z
      · simpa [eq, f, ← eq_sub_iff_add_eq, m, map_add, Pi.add_apply] using h₁ z j (by omega) hj'
  have H' := diff_window hk s hs h start d f
  rw [H] at H'
  have h₀ : d (atOffset start (-(s : ℤ))) = f 0 ↔
      d (atOffset start (-(s : ℤ))) + m start = rot c dk start := by
    simp [f, head, eq_sub_iff_add_eq]
  have h₁ : (∀ j : ℤ, 1 ≤ j → j ≤ (h : ℤ) + 1 → f j = 0) ↔
      zeros start m 1 ((h : ℤ) + 1) := by
    simp only [zeros, f]
    constructor <;> intro e j hj hj' <;>
      simpa [show j ≠ 0 by omega] using e j hj hj'
  rw [h₀, h₁] at H'
  have tail : (∀ j : ℤ, 1 ≤ j → j < (h : ℤ) → rot c dk (atOffset start j) = 0) ↔
      zeros start (rot c dk) 1 ((h : ℤ) - 1) := by
    unfold zeros
    constructor <;> intro e j hj hj' <;> exact e j hj (by omega)
  constructor
  · rintro ⟨A, C, T⟩
    obtain ⟨z, a, c⟩ := H'.mp ⟨A, C⟩
    exact ⟨z, a, c, tail.mp T⟩
  · rintro ⟨z, a, c, t⟩
    obtain ⟨A, C⟩ := H'.mpr ⟨z, a, c⟩
    exact ⟨A, C, tail.mpr t⟩

lemma rot_offset (a : ℕ) (x : W k) (i : ZMod k) (j : ℤ) :
    rot a x (atOffset i j) = x (atOffset i (j - a)) := by
  simp [rot, atOffset, sub_eq_add_neg, add_assoc]

lemma mix_rot_offset (s a : ℕ) (x : W k) (i : ZMod k) (j : ℤ) :
    mix s (rot a x) (atOffset i j) =
      x (atOffset i (j - a - s)) + x (atOffset i (j - a)) + x (atOffset i (j - a + s)) := by
  rw [mix_at, show (s : ZMod k) = ((s : ℤ) : ZMod k) by simp, sub_eq_add_neg, ← Int.cast_neg,
    offset_step, offset_step, rot_offset, rot_offset, rot_offset]
  rw [show j + -(s : ℤ) - a = j - a - s by omega,
    show j + (s : ℤ) - a = j - a + s by omega]

lemma key_window (h : ℕ) (hh : 6 ≤ h) (start : ZMod k) (dk : W k)
    (row : zeros start (rot 2 dk) 1 ((h : ℤ) - 1))
    (col : zeros start (rot 7 dk) 1 ((h : ℤ) - 1))
    (tap : zeros start (mix 1 (rot 0 dk)) 1 ((h : ℤ) + 1)) :
    zeros start dk (-6) ((h : ℤ) + 2) := by
  have init (j : ℤ) (hl : -6 ≤ j) (hr : j ≤ (h : ℤ) - 3) :
      dk (atOffset start j) = 0 := by
    by_cases a : -1 ≤ j
    · have e := row (j+2) (by omega) (by omega)
      rw [rot_offset, show j + 2 - (2 : ℕ) = j by omega] at e
      exact e
    · have e := col (j+7) (by omega) (by omega)
      rw [rot_offset, show j + 7 - (7 : ℕ) = j by omega] at e
      exact e
  have extend (n : ℕ) : (n : ℤ) ≤ (h : ℤ) + 8 →
      dk (atOffset start ((n : ℤ)-6)) = 0 := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro hn
      by_cases a : (n : ℤ) - 6 ≤ (h : ℤ) - 3
      · exact init _ (by omega) a
      · have e := tap ((n : ℤ)-7) (by omega) (by omega)
        have e₁ := ih (n-2) (by omega) (by omega)
        have e₂ := ih (n-1) (by omega) (by omega)
        rw [mix_rot_offset,
          show (n : ℤ)-7-(0 : ℕ)+(1 : ℕ) = (n : ℤ)-6 by omega,
          show (n : ℤ)-7-(0 : ℕ)-(1 : ℕ) = ((n-2 : ℕ) : ℤ)-6 by omega,
          show (n : ℤ)-7-(0 : ℕ) = ((n-1 : ℕ) : ℤ)-6 by omega,
          e₁, e₂, zero_add, zero_add] at e
        exact e
  intro j hj hj'
  have e := extend (j+6).toNat (by omega)
  rwa [show (((j+6).toNat : ℕ) : ℤ) - 6 = j by omega] at e

def rowPattern (h : ℕ) (p q : B) (j : ℤ) : B :=
  if j = (h : ℤ) + 3 then p else if j = (h : ℤ) + 4 then p + q else 0

def colPattern (h : ℕ) (p q : B) (j : ℤ) : B :=
  if j = (h : ℤ) + 4 then p else if j = (h : ℤ) + 5 then q else 0

lemma row_taps (h : ℕ) (start : ZMod k) (dk : W k)
    (Z : zeros start dk (-6) ((h : ℤ) + 2))
    (j : ℤ) (hj : -1 ≤ j) (hj' : j ≤ (h : ℤ) + 4) :
    mix 1 (rot 1 dk) (atOffset start j) =
      rowPattern h (dk (atOffset start ((h : ℤ)+3))) (dk (atOffset start ((h : ℤ)+4))) j := by
  rw [mix_rot_offset]
  by_cases a : j = (h : ℤ) + 3
  · subst j
    simp [rowPattern, show (h : ℤ) + 3 - (1 : ℕ) + (1 : ℕ) = (h : ℤ)+3 by omega,
      Z ((h : ℤ) + 3 - 1 - 1) (by omega) (by omega),
      Z ((h : ℤ) + 3 - 1) (by omega) (by omega)]
  by_cases b : j = (h : ℤ) + 4
  · subst j
    rw [show (h : ℤ) + 4 - (1 : ℕ) + (1 : ℕ) = (h : ℤ)+4 by omega,
      Z _ (by omega) (by omega), show (h : ℤ) + 4 - (1 : ℕ) = (h : ℤ)+3 by omega]
    simp [rowPattern, a]
  · rw [Z _ (by omega) (by omega), Z _ (by omega) (by omega), Z _ (by omega) (by omega)]
    simp [rowPattern, a, b]

lemma col_taps (h : ℕ) (start : ZMod k) (dk : W k)
    (Z : zeros start dk (-6) ((h : ℤ) + 2))
    (j : ℤ) (hj : -1 ≤ j) (hj' : j ≤ (h : ℤ) + 5) :
    mix 2 (rot 3 dk) (atOffset start j) =
      colPattern h (dk (atOffset start ((h : ℤ)+3))) (dk (atOffset start ((h : ℤ)+4))) j := by
  rw [mix_rot_offset, Z _ (by omega) (by omega), Z _ (by omega) (by omega), zero_add, zero_add]
  by_cases a : j = (h : ℤ) + 4
  · rw [show j - (3 : ℕ) + (2 : ℕ) = (h : ℤ) + 3 by omega]
    simp [colPattern, a]
  by_cases b : j = (h : ℤ) + 5
  · rw [show j - (3 : ℕ) + (2 : ℕ) = (h : ℤ) + 4 by omega]
    simp [colPattern, a, b]
  · rw [Z _ (by omega) (by omega)]
    simp [colPattern, a, b]

lemma row_schedule (h : ℕ) (start : ZMod k) (dk : W k)
    (z : zeros start dk (-6) ((h : ℤ) + 2)) :
    zeros start (mix 1 (rot 0 dk)) 1 ((h : ℤ)+1) ∧
    zeros start (rot 2 dk) 1 ((h : ℤ)-1) ∧
    mix 1 (rot 0 dk) start = 0 ∧ rot 2 dk start = 0 := by
  have hm (j : ℤ) (hl : 0 ≤ j) (hr : j ≤ (h : ℤ)+1) :
      mix 1 (rot 0 dk) (atOffset start j) = 0 := by
    rw [mix_rot_offset, z _ (by omega) (by omega), z _ (by omega) (by omega),
      z _ (by omega) (by omega), zero_add, zero_add]
  have hr (j : ℤ) (hl : 0 ≤ j) (hr : j ≤ (h : ℤ)-1) :
      rot 2 dk (atOffset start j) = 0 := by
    rw [rot_offset]
    exact z _ (by omega) (by omega)
  refine ⟨fun j a b => hm j (by omega) b, fun j a b => hr j (by omega) b, ?_, ?_⟩
  · simpa [atOffset] using hm 0 (by omega) (by omega)
  · have e := z (-2) (by omega) (by omega)
    simpa [atOffset, rot, sub_eq_add_neg] using e

lemma col_schedule (h : ℕ) (start : ZMod k) (dk : W k)
    (z : zeros start dk (-6) ((h : ℤ) + 2)) :
    zeros start (mix 2 (rot 4 dk)) 1 ((h : ℤ)+1) ∧
    zeros start (rot 7 dk) 1 ((h : ℤ)-1) ∧
    mix 2 (rot 4 dk) start = 0 ∧ rot 7 dk start = dk (atOffset start (-7)) := by
  have hm (j : ℤ) (hl : 0 ≤ j) (hr : j ≤ (h : ℤ)+1) :
      mix 2 (rot 4 dk) (atOffset start j) = 0 := by
    rw [mix_rot_offset, z _ (by omega) (by omega), z _ (by omega) (by omega),
      z _ (by omega) (by omega), zero_add, zero_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j a b
    exact hm j (by omega) b
  · intro j a b
    rw [rot_offset]
    exact z _ (by omega) (by omega)
  · simpa [atOffset] using hm 0 (by omega) (by omega)
  · simp [rot, atOffset, sub_eq_add_neg]

def colKey (start : ZMod k) (dk : W k) : W k :=
  mix 2 (rot 3 dk) + spike (atOffset start (-2)) (dk (atOffset start (-7)))

lemma col_key_head (h : ℕ) (start : ZMod k) (dk : W k)
    (z : zeros start dk (-6) ((h : ℤ) + 2)) :
    colKey start dk (atOffset start (-2)) = 0 := by
  simp only [colKey, Pi.add_apply, spike, if_pos rfl, mix_rot_offset]
  norm_num
  simp [z (-5) (by omega) (by omega), z (-3) (by omega) (by omega), add_bit]

lemma col_spike_tail (h : ℕ) (start : ZMod k) (dk : W k)
    (z : zeros start dk (-6) ((h : ℤ) + 2)) (j : ℤ)
    (hj : -1 ≤ j) (hj' : j ≤ (h : ℤ)+5) :
    spike (atOffset start (-2)) (dk (atOffset start (-7))) (atOffset start j) = 0 := by
  by_cases a : atOffset start j = atOffset start (-2)
  · have he : atOffset start (j-5) = atOffset start (-7) := by
      simpa only [offset_add, ← sub_eq_add_neg, show (-2 : ℤ) + -5 = -7 by decide] using
        congrArg (fun i => atOffset i (-5)) a
    have hz := z (j - 5) (by omega) (by omega)
    rw [he] at hz
    simp [spike, hz]
  · simp [spike, a]

lemma row_name (h : ℕ) (start : ZMod k) (dn dk : W k) :
    (zeros start (mix 1 (rot 1 dk + dn)) 0 ((h : ℤ)+4) ∧
      mix 1 (rot 1 dk + dn) (atOffset start (-1)) = 0) ↔
    ∀ j : ℤ, -1 ≤ j → j ≤ (h : ℤ)+4 →
      mix 1 dn (atOffset start j) = mix 1 (rot 1 dk) (atOffset start j) := by
  simp only [zeros, map_add, Pi.add_apply, bit_zero]
  constructor
  · rintro ⟨tail, head⟩ j hj hj'
    by_cases eq : j = -1
    · simpa only [eq] using head.symm
    · exact (tail j (by omega) hj').symm
  · intro hyp
    exact ⟨fun j hj hj' => (hyp j (by omega) hj').symm, (hyp (-1) (by omega) (by omega)).symm⟩

lemma col_name (h : ℕ) (start : ZMod k) (dn dk : W k)
    (z : zeros start dk (-6) ((h : ℤ) + 2)) :
    (zeros start (mix 2 (rot 3 dk + dn)) (-1) ((h : ℤ)+5) ∧
      mix 2 (rot 3 dk + dn) (atOffset start (-2)) = dk (atOffset start (-7))) ↔
    ∀ j : ℤ, -2 ≤ j → j ≤ (h : ℤ)+5 →
      mix 2 dn (atOffset start j) = colKey start dk (atOffset start j) := by
  have head (j : ℤ) :
      mix 2 (rot 3 dk + dn) (atOffset start j) =
        spike (atOffset start (-2)) (dk (atOffset start (-7))) (atOffset start j) ↔
      mix 2 dn (atOffset start j) = colKey start dk (atOffset start j) := by
    simp only [colKey, map_add, Pi.add_apply]
    generalize mix 2 (rot 3 dk) (atOffset start j) = a
    generalize mix 2 dn (atOffset start j) = b
    generalize spike (atOffset start (-2)) (dk (atOffset start (-7))) (atOffset start j) = c
    constructor <;> intro e
    · rw [← e, ← add_assoc, add_bit, zero_add]
    · rw [e, ← add_assoc, add_bit, zero_add]
  constructor
  · rintro ⟨tail, e⟩ j hj hj'
    apply (head j).mp
    by_cases a : atOffset start j = atOffset start (-2)
    · simpa [a, spike] using e
    · simpa only [spike, if_neg a] using tail j (by
        have hn : j ≠ -2 := fun eq => a (congrArg (atOffset start) eq)
        omega) hj'
  · intro hyp
    have e := (head (-2)).mpr (hyp (-2) (by omega) (by omega))
    refine ⟨?_, by simpa [spike] using e⟩
    intro j hj hj'
    have eq := (head j).mpr (hyp j (by omega) hj')
    rwa [col_spike_tail h start dk z j hj hj'] at eq

set_option maxHeartbeats 2000000 in
lemma shared_linear (hk : 7 ≤ k) (hk3 : k % 3 ≠ 0) (h : ℕ) (hh : 6 ≤ h)
    (start : ZMod k) (r₁ r₂ c₁ c₂ : W k) (dn : W k × W k) (dk : W k) :
    (lane 1 1 0 2 h start r₁ r₂ dn.1 dk ∧ lane 2 3 4 7 h start c₁ c₂ dn.2 dk) ↔
      zeros start dk (-6) ((h : ℤ)+2) ∧
      (∀ j : ℤ, -1 ≤ j → j ≤ (h : ℤ)+4 →
        mix 1 dn.1 (atOffset start j) = mix 1 (rot 1 dk) (atOffset start j)) ∧
      (∀ j : ℤ, -2 ≤ j → j ≤ (h : ℤ)+5 →
        mix 2 dn.2 (atOffset start j) = colKey start dk (atOffset start j)) := by
  rw [lane_linear hk hk3 1 (Or.inl rfl) 1 0 2 h (by omega),
      lane_linear hk hk3 2 (Or.inr rfl) 3 4 7 h (by omega)]
  norm_num
  simp only [show (h : ℤ)+3+1 = (h : ℤ)+4 by omega,
    show (h : ℤ)+3+2 = (h : ℤ)+5 by omega]
  constructor
  · rintro ⟨⟨rz, rh, rt, rr⟩, ⟨cz, ch, ct, cr⟩⟩
    have z := key_window h hh start dk rr cr rt
    obtain ⟨_, _, a, b⟩ := row_schedule h start dk z
    obtain ⟨_, _, c, d⟩ := col_schedule h start dk z
    rw [a, b, add_zero] at rh
    rw [c, d, add_zero] at ch
    exact ⟨z, (row_name h start dn.1 dk).mp (by simpa only [map_add, Pi.add_apply] using And.intro rz rh),
      (col_name h start dn.2 dk z).mp (by simpa only [map_add, Pi.add_apply] using And.intro cz ch)⟩
  · rintro ⟨z, row, col⟩
    obtain ⟨rt, rr, a, b⟩ := row_schedule h start dk z
    obtain ⟨ct, cr, c, d⟩ := col_schedule h start dk z
    obtain ⟨rz, rh⟩ := (row_name h start dn.1 dk).mpr row
    obtain ⟨cz, ch⟩ := (col_name h start dn.2 dk z).mpr col
    exact ⟨⟨by simpa only [map_add] using rz, by simpa [a, b] using rh, rt, rr⟩,
      ⟨by simpa only [map_add] using cz, by simpa [c, d] using ch, ct, cr⟩⟩

def window (start : ZMod k) (lo : ℤ) (n : ℕ) : W k →ₗ[B] (Fin n → B) where
  toFun w j := w (atOffset start (lo + (j.val : ℤ)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma window_surj (start : ZMod k) (lo : ℤ) (n : ℕ) (hn : n ≤ k) :
    Function.Surjective (window start lo n) := by
  classical
  let idx : Fin n → ZMod k := fun j => atOffset start (lo + (j.val : ℤ))
  have hi : Function.Injective idx := by
    intro i j he
    have eq : (i.val : ZMod k) = (j.val : ZMod k) := by
      dsimp [idx, atOffset] at he
      push_cast at he
      exact add_left_cancel (by simpa only [← add_assoc] using he)
    exact Fin.ext (by simpa only [ZMod.val_natCast_of_lt (lt_of_lt_of_le i.isLt hn),
      ZMod.val_natCast_of_lt (lt_of_lt_of_le j.isLt hn)] using congrArg ZMod.val eq)
  intro y
  refine ⟨Function.extend idx y 0, ?_⟩
  funext j
  exact hi.extend_apply y 0 j

lemma window_eq (start : ZMod k) (lo : ℤ) (n : ℕ) (v w : W k) :
    window start lo (min k n) v = window start lo (min k n) w ↔
      ∀ j : ℤ, lo ≤ j → j < lo + n → v (atOffset start j) = w (atOffset start j) := by
  constructor
  · intro eq j jl jr
    let a := (j-lo).toNat
    have ha : lo + (a : ℤ) = j := by dsimp [a]; omega
    have hn : a < n := by omega
    let i : Fin (min k n) := ⟨a % k, lt_min (Nat.mod_lt _ (NeZero.pos k))
      (lt_of_le_of_lt (Nat.mod_le _ _) hn)⟩
    have e := congrFun eq i
    change v (atOffset start (lo + ((a % k : ℕ) : ℤ))) =
      w (atOffset start (lo + ((a % k : ℕ) : ℤ))) at e
    have he : atOffset start (lo + ((a % k : ℕ) : ℤ)) = atOffset start j := by
      rw [← ha]
      simp [atOffset, ZMod.natCast_mod]
    rwa [he] at e
  · intro e
    funext i
    exact e (lo + (i.val : ℤ)) (by omega)
      (by have := lt_of_lt_of_le i.isLt (min_le_right k n); omega)

lemma window_ker (start : ZMod k) (lo : ℤ) (n : ℕ) (x : W k) :
    x ∈ (window start lo (min k n)).ker ↔ zeros start x lo (lo + n - 1) := by
  rw [LinearMap.mem_ker, ← map_zero (window start lo (min k n)), window_eq]
  unfold zeros
  constructor <;> intro e j jl jr <;> exact e j jl (by omega)

lemma word_finrank : Module.finrank B (W k) = k := by
  simp [W, Module.finrank_pi_fintype, ZMod.card]

lemma window_ker_dim (start : ZMod k) (lo : ℤ) (n : ℕ) :
    Module.finrank B (window start lo (min k n)).ker = k - n := by
  have e := (window start lo (min k n)).finrank_range_add_finrank_ker
  have d : Module.finrank B (Fin (min k n) → B) = min k n := by
    simp [Module.finrank_pi_fintype]
  rw [LinearMap.range_eq_top.mpr (window_surj start lo _ (min_le_left k n)),
    finrank_top, d, word_finrank] at e
  omega

def rotLin (s : ℕ) : W k →ₗ[B] W k where
  toFun := rot s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def colKeyLin (start : ZMod k) : W k →ₗ[B] W k where
  toFun := colKey start
  map_add' x y := by
    funext j
    by_cases h : j = atOffset start (-2) <;> simp [colKey, rot_add, spike, h] <;> abel
  map_smul' a x := by
    have H : rot 3 (a • x) = a • rot 3 x := rfl
    funext j
    by_cases h : j = atOffset start (-2) <;> simp [colKey, H, spike, h, mul_add]

abbrev Space (k h : ℕ) := (Fin (min k (h+6)) → B) × (Fin (min k (h+8)) → B)

def nameProj (start : ZMod k) (h : ℕ) : (W k × W k) →ₗ[B] Space k h :=
  ((window start (-1) _).comp (mix 1)).prodMap ((window start (-2) _).comp (mix 2))

noncomputable def keyProj (start : ZMod k) (h : ℕ) :
    (window start (-6) (min k (h+9))).ker →ₗ[B] Space k h :=
  ((((window start (-1) _).comp ((mix 1).comp (rotLin 1))).prod
    ((window start (-2) _).comp (colKeyLin start)))).domRestrict _

lemma nameProj_surj (hk3 : k % 3 ≠ 0) (start : ZMod k) (h : ℕ) :
    Function.Surjective (nameProj start h) := by
  intro y
  obtain ⟨r, er⟩ := ((window_surj start (-1) _ (min_le_left k (h+6))).comp (mix_bij hk3 1).2) y.1
  obtain ⟨c, ec⟩ := ((window_surj start (-2) _ (min_le_left k (h+8))).comp (mix_bij hk3 2).2) y.2
  exact ⟨(r,c), Prod.ext er ec⟩

lemma keyProj_eq (start : ZMod k) (h : ℕ)
    (u : (window start (-6) (min k (h+9))).ker) (dn : W k × W k) :
    nameProj start h dn = keyProj start h u ↔
      (∀ j : ℤ, -1 ≤ j → j ≤ (h : ℤ)+4 →
        mix 1 dn.1 (atOffset start j) = mix 1 (rot 1 (u : W k)) (atOffset start j)) ∧
      (∀ j : ℤ, -2 ≤ j → j ≤ (h : ℤ)+5 →
        mix 2 dn.2 (atOffset start j) = colKey start (u : W k) (atOffset start j)) := by
  rw [Prod.ext_iff]
  change ((window start (-1) (min k (h+6)) (mix 1 dn.1) =
    window start (-1) (min k (h+6)) (mix 1 (rot 1 (u : W k)))) ∧
    (window start (-2) (min k (h+8)) (mix 2 dn.2) =
    window start (-2) (min k (h+8)) (colKey start (u : W k)))) ↔ _
  rw [window_eq, window_eq]
  have rb (j : ℤ) : j < -1 + ((h+6 : ℕ) : ℤ) ↔ j ≤ (h : ℤ)+4 := by push_cast; omega
  have cb (j : ℤ) : j < -2 + ((h+8 : ℕ) : ℤ) ↔ j ≤ (h : ℤ)+5 := by push_cast; omega
  simp only [rb, cb]

lemma key_mem (start : ZMod k) (h : ℕ) (dk : W k) :
    dk ∈ (window start (-6) (min k (h+9))).ker ↔
      zeros start dk (-6) ((h : ℤ) + 2) := by
  rw [window_ker, show (-6 : ℤ) + ((h+9 : ℕ) : ℤ) - 1 = (h : ℤ)+2 by push_cast; omega]

lemma keyProj_kernel (start : ZMod k) (h : ℕ)
    (u : (window start (-6) (min k (h+9))).ker) :
    u ∈ (keyProj start h).ker ↔
      (u : W k) ∈ (window start (-6) (min k (h+11))).ker := by
  have z := (key_mem start h u).mp u.property
  rw [LinearMap.mem_ker, ← map_zero (nameProj start h), eq_comm, keyProj_eq, window_ker]
  have el : (-6 : ℤ) + ((h + 11 : ℕ) : ℤ) - 1 = (h : ℤ) + 4 := by push_cast; omega
  rw [el]
  simp only [Prod.fst_zero, Prod.snd_zero, map_zero, Pi.zero_apply]
  constructor
  · rintro ⟨r, c⟩
    have p := (r ((h : ℤ)+3) (by omega) (by omega)).symm
    have q := (r ((h : ℤ)+4) (by omega) (by omega)).symm
    rw [row_taps h start _ z _ (by omega) (by omega), rowPattern, if_pos rfl] at p
    rw [row_taps h start _ z _ (by omega) (by omega), rowPattern, if_neg (by omega), if_pos rfl,
      p, zero_add] at q
    intro j hj hj'
    by_cases a : j = (h : ℤ)+3
    · simpa only [a] using p
    by_cases b : j = (h : ℤ)+4
    · simpa only [b] using q
    exact z j hj (by omega)
  · intro zz
    have p := zz ((h : ℤ)+3) (by omega) (by omega)
    have q := zz ((h : ℤ)+4) (by omega) (by omega)
    refine ⟨fun j a b => ?_, fun j a b => ?_⟩
    · simp [row_taps h start _ z j a b, rowPattern, p, q]
    · by_cases c : j = -2
      · simpa [c] using (col_key_head h start _ z).symm
      have hl : -1 ≤ j := by omega
      simp [colKey, col_spike_tail h start _ z j hl b, col_taps h start _ z j hl b,
        colPattern, p, q]

lemma long_to_short (start : ZMod k) (h : ℕ) (dk : W k)
    (e : dk ∈ (window start (-6) (min k (h+11))).ker) :
    dk ∈ (window start (-6) (min k (h+9))).ker := by
  rw [window_ker] at e
  apply (key_mem start h dk).mpr
  intro j hj hj'
  exact e j hj (by push_cast; omega)

noncomputable def keyKerEquiv (start : ZMod k) (h : ℕ) :
    (keyProj start h).ker ≃ₗ[B] (window start (-6) (min k (h+11))).ker where
  toFun u := ⟨(u.val : W k), (keyProj_kernel start h u.val).mp u.property⟩
  invFun u :=
    let v := ⟨u.val, long_to_short start h u.val u.property⟩
    ⟨v, (keyProj_kernel start h v).mpr u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma keyKer_dim (start : ZMod k) (h : ℕ) :
    Module.finrank B (keyProj start h).ker = k - (h+11) := by
  rw [(keyKerEquiv start h).finrank_eq, window_ker_dim]

lemma keyRange_dim (start : ZMod k) (h : ℕ) :
    Module.finrank B (keyProj start h).range = min 2 (k-(h+9)) := by
  have e := (keyProj start h).finrank_range_add_finrank_ker
  rw [keyKer_dim, window_ker_dim] at e
  omega

lemma space_dim (h : ℕ) : Module.finrank B (Space k h) =
    min k (h+6) + min k (h+8) := by
  simp [Space, Module.finrank_prod, Module.finrank_pi_fintype]

lemma fiber_card {V U : Type*} [AddCommGroup V] [Module B V] [AddCommGroup U] [Module B U]
    (f : V →ₗ[B] U) {y : U} (hy : y ∈ f.range) :
    Nat.card { v : V // f v = y } = Nat.card f.ker := by
  obtain ⟨a, rfl⟩ := hy
  refine Nat.card_congr
    { toFun := fun v => ⟨v.val - a, by simp [LinearMap.mem_ker, v.property]⟩
      invFun := fun u => ⟨u.val + a, by simp [LinearMap.mem_ker.mp u.property]⟩
      left_inv := fun v => Subtype.ext (sub_add_cancel _ _)
      right_inv := fun u => Subtype.ext (add_sub_cancel_right _ _) }

def bothOut (h : ℕ) (start : ZMod k) (r₁ r₂ c₁ c₂ : W k)
    (nm : W k × W k) (key : W k) (q : Fin h) : B × B :=
  (run 1 1 0 2 key nm.1 r₁ r₂ (atOffset start q.val),
    run 2 3 4 7 key nm.2 c₁ c₂ (atOffset start q.val))

lemma preserves_iff (hk : 7 ≤ k) (hk3 : k % 3 ≠ 0) (h : ℕ) (hh : 6 ≤ h)
    (start : ZMod k) (r₁ r₂ c₁ c₂ : W k) (dn : W k × W k) (dk : W k) :
    (∀ base key q, bothOut h start r₁ r₂ c₁ c₂ (base + dn) (key + dk) q =
      bothOut h start r₁ r₂ c₁ c₂ base key q) ↔
    ∃ u : (window start (-6) (min k (h+9))).ker,
      (u : W k) = dk ∧ keyProj start h u = nameProj start h dn := by
  have e :
      (∀ base key q, bothOut h start r₁ r₂ c₁ c₂ (base + dn) (key + dk) q =
        bothOut h start r₁ r₂ c₁ c₂ base key q) ↔
      lane 1 1 0 2 h start r₁ r₂ dn.1 dk ∧ lane 2 3 4 7 h start c₁ c₂ dn.2 dk := by
    constructor
    · intro f
      exact ⟨fun row key q => congrArg Prod.fst (f (row, 0) key q),
        fun col key q => congrArg Prod.snd (f (0, col) key q)⟩
    · rintro ⟨r, c⟩ base key q
      exact Prod.ext (r base.1 key q) (c base.2 key q)
  rw [e, shared_linear hk hk3 h hh]
  constructor
  · rintro ⟨z, r, c⟩
    let u : (window start (-6) (min k (h+9))).ker := ⟨dk, (key_mem start h dk).mpr z⟩
    exact ⟨u, rfl, ((keyProj_eq start h u dn).mpr ⟨r,c⟩).symm⟩
  · rintro ⟨u, rfl, eu⟩
    exact ⟨(key_mem start h u).mp u.property, (keyProj_eq start h u dn).mp eu.symm⟩

noncomputable def fiberEquiv (hk : 7 ≤ k) (hk3 : k % 3 ≠ 0) (h : ℕ) (hh : 6 ≤ h)
    (start : ZMod k) (r₁ r₂ c₁ c₂ : W k) (dn : W k × W k) :
    { dk : W k // ∀ base key q, bothOut h start r₁ r₂ c₁ c₂ (base + dn) (key + dk) q =
      bothOut h start r₁ r₂ c₁ c₂ base key q } ≃
    { u : (window start (-6) (min k (h+9))).ker // keyProj start h u = nameProj start h dn } := by
  let e := preserves_iff hk hk3 h hh start r₁ r₂ c₁ c₂ dn
  apply Equiv.symm
  refine Equiv.ofBijective (fun u => ⟨u.val.val, (e u.val.val).mpr ⟨u.val, rfl, u.property⟩⟩)
    ⟨?_, ?_⟩
  · intro u v he
    have he' : u.val.val = v.val.val := congrArg (fun t => (t.val : W k)) he
    apply Subtype.ext
    apply Subtype.ext
    exact he'
  · intro dk
    obtain ⟨u, he, hu⟩ := (e dk.val).mp dk.property
    exact ⟨⟨u, hu⟩, Subtype.ext he⟩

lemma target_card (h : ℕ) (start : ZMod k) (r₁ r₂ c₁ c₂ : W k)
    (x y : W k × W k) (dk : W k)
    (p : ∀ base key q, bothOut h start r₁ r₂ c₁ c₂ (base + (x+y)) (key + dk) q =
      bothOut h start r₁ r₂ c₁ c₂ base key q)
    (target : Fin h → B × B) :
    Nat.card { key : W k // ∀ q, bothOut h start r₁ r₂ c₁ c₂ x key q = target q } =
    Nat.card { key : W k // ∀ q, bothOut h start r₁ r₂ c₁ c₂ y key q = target q } := by
  have addPair (z : W k × W k) : z + z = 0 := Prod.ext (add_word _) (add_word _)
  have hx : x + (x+y) = y := by rw [← add_assoc, addPair, zero_add]
  have hy : y + (x+y) = x := by rw [add_comm x y, ← add_assoc, addPair, zero_add]
  have eqx (key : W k) (q : Fin h) :
      bothOut h start r₁ r₂ c₁ c₂ y (key + dk) q =
      bothOut h start r₁ r₂ c₁ c₂ x key q := by simpa only [hx] using p x key q
  have eqy (key : W k) (q : Fin h) :
      bothOut h start r₁ r₂ c₁ c₂ x (key + dk) q =
      bothOut h start r₁ r₂ c₁ c₂ y key q := by simpa only [hy] using p y key q
  refine Nat.card_congr
    { toFun := fun v => ⟨v.val + dk, fun q => (eqx v.val q).trans (v.property q)⟩
      invFun := fun v => ⟨v.val + dk, fun q => (eqy v.val q).trans (v.property q)⟩
      left_inv := fun v => Subtype.ext (by change v.val + dk + dk = v.val; rw [add_assoc, add_word, add_zero])
      right_inv := fun v => Subtype.ext (by change v.val + dk + dk = v.val; rw [add_assoc, add_word, add_zero]) }

set_option maxHeartbeats 2500000 in
lemma solve (hk : 7 ≤ k) (hk3 : k % 3 ≠ 0) (h : ℕ) (hh : 6 ≤ h)
    (start : ZMod k) (r₁ r₂ c₁ c₂ : W k) :
    let out := bothOut h start r₁ r₂ c₁ c₂
    let preserves := fun (dn : W k × W k) (dk : W k) =>
      ∀ base key q, out (base+dn) (key+dk) q = out base key q
    let num := fun (nm : W k × W k) (target : Fin h → (B × B)) =>
      Nat.card { key : W k // ∀ q : Fin h, out nm key q = target q }
    let bits := min k (h+6) + min k (h+8) - min 2 (k-(h+9))
    ∃ sig : (W k × W k) →ₗ[B] (Fin bits → B), Function.Surjective sig ∧
      ∀ x y : W k × W k,
        (Nat.card { dk : W k // preserves (x+y) dk } =
          (if sig x = sig y then 2^(k-(h+11)) else 0)) ∧
        (sig x = sig y → ∀ target, num x target = num y target) := by
  classical
  dsimp only
  let R := (keyProj start h).range
  let bits := min k (h+6) + min k (h+8) - min 2 (k-(h+9))
  have dim : Module.finrank B (Space k h ⧸ R) = bits := by
    have e := R.finrank_quotient_add_finrank
    rw [space_dim, keyRange_dim] at e
    dsimp [bits]
    omega
  let iso := (Module.finBasisOfFinrankEq B (Space k h ⧸ R) dim).equivFun
  let sig := iso.toLinearMap.comp (R.mkQ.comp (nameProj start h))
  refine ⟨sig, iso.surjective.comp (R.mkQ_surjective.comp (nameProj_surj hk3 start h)), ?_⟩
  intro x y
  have hm : sig x = sig y ↔ nameProj start h (x+y) ∈ R := by
    change iso (R.mkQ (nameProj start h x)) = iso (R.mkQ (nameProj start h y)) ↔ _
    have hmem (z : Space k h) : z ∈ R ↔ R.mkQ z = 0 := by
      change z ∈ R ↔ z ∈ R.mkQ.ker
      rw [R.ker_mkQ]
    rw [iso.injective.eq_iff, hmem, map_add, map_add]
    have hyy : R.mkQ (nameProj start h y) + R.mkQ (nameProj start h y) = 0 := by
      rw [← map_add, ← map_add, show y + y = 0 from Prod.ext (add_word _) (add_word _),
        map_zero, map_zero]
    constructor
    · intro e
      rwa [e]
    · intro e
      calc
        R.mkQ (nameProj start h x) = R.mkQ (nameProj start h x) + 0 := (add_zero _).symm
        _ = (R.mkQ (nameProj start h x) + R.mkQ (nameProj start h y)) +
            R.mkQ (nameProj start h y) := by rw [add_assoc, hyy]
        _ = R.mkQ (nameProj start h y) := by rw [e, zero_add]
  constructor
  · rw [Nat.card_congr (fiberEquiv hk hk3 h hh start r₁ r₂ c₁ c₂ (x+y))]
    by_cases eq : sig x = sig y
    · rw [if_pos eq, fiber_card (keyProj start h) (hm.mp eq)]
      letI := Fintype.ofFinite (keyProj start h).ker
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := B), keyKer_dim, ZMod.card]
    · rw [if_neg eq]
      exact Nat.card_eq_zero.mpr (Or.inl ⟨fun u => eq (hm.mpr ⟨u.val, u.property⟩)⟩)
  · intro eq target
    obtain ⟨u, hu⟩ := hm.mp eq
    exact target_card h start r₁ r₂ c₁ c₂ x y u
      ((preserves_iff hk hk3 h hh start r₁ r₂ c₁ c₂ (x+y) u).mpr ⟨u, rfl, hu⟩) target

end PEqualNP.Outside.L_meta_29762

open PEqualNP.Outside.L_meta_29762

set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.L_meta_29762 : ∀ (k : ℕ) [NeZero k], 7 ≤ k → k % 3 ≠ 0 →
  let I := ZMod k
  let W := I → ZMod 2
  let rot := fun (s : ℕ) (x : W) (i : I) => x (i-(s : I))
  let mix := fun (s : ℕ) (x : W) (i : I) => x (i-(s : I)) + x i + x (i+(s : I))
  let update := fun (s : ℕ) (x : W) (i : I) =>
    let z := mix s x
    z i + (1+z (i+1))*z (i+2)
  let run := fun (col : Bool) (key name c1 c2 : W) =>
    let s : ℕ := if col then 2 else 1
    let first := update s (rot (if col then 3 else 1) key + name) +
      rot (if col then 4 else 0) key + c1
    update s first + rot (if col then 7 else 2) key + c2
  ∀ (h : ℕ), 6 ≤ h → h ≤ k → ∀ (start : I) (r1 r2 c1 c2 : W),
    let out := fun (name : W × W) (key : W) (q : Fin h) =>
      let i := start+(q.val : I)
      (run false key name.1 r1 r2 i, run true key name.2 c1 c2 i)
    let preserves := fun (dn : W × W) (dk : W) =>
      ∀ (base : W × W) (key : W) (q : Fin h), out (base+dn) (key+dk) q = out base key q
    let num := fun (nm : W × W) (target : Fin h → (ZMod 2 × ZMod 2)) =>
      Nat.card { key : W // ∀ q : Fin h, out nm key q = target q }
    let bits := min k (h+6) + min k (h+8) - min 2 (k-(h+9))
    ∃ sig : (W × W) →ₗ[ZMod 2] (Fin bits → ZMod 2), Function.Surjective sig ∧
      ∀ x y : W × W,
        (Nat.card { dk : W // preserves (x+y) dk } =
          (if sig x = sig y then 2^(k-(h+11)) else 0)) ∧
        (sig x = sig y → ∀ target, num x target = num y target) := by
  intro k inst hk hk3
  intro I U rotate mixing updateF runF h hh hle start r1 r2 c1 c2 out preserves num bits
  have erot : rotate = rot (k := k) := rfl
  have eupdate : updateF = (fun (s : ℕ) (x : W k) => chi (mix s x)) := rfl
  have erun (col : Bool) (key name c₁ c₂ : W k) :
      runF col key name c₁ c₂ =
        run (if col then 2 else 1) (if col then 3 else 1) (if col then 4 else 0)
          (if col then 7 else 2) key name c₁ c₂ := by
    dsimp only [runF, run]
    rw [erot, eupdate]
  have eout : out = bothOut h start r1 r2 c1 c2 := by
    funext name key q
    dsimp only [out, bothOut]
    simp only [erun, atOffset, Int.cast_natCast, Bool.false_eq_true, if_false, if_true, if_pos rfl]
  simpa only [preserves, num, bits, eout] using solve hk hk3 h hh start r1 r2 c1 c2
