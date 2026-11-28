import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32015

variable {k : ℕ} [NeZero k]

abbrev V (k : ℕ) := ZMod k → ZMod 2

def R (s : ℕ) (x : V k) : V k := fun i => x (i - (s : ZMod k))
def M (g : ℕ) (x : V k) : V k := fun i => x i + x (i + (g : ZMod k)) + x (i - (g : ZMod k))
def st (x : V k) : V k := fun i => x i + (1 + x (i + 1)) * x (i + 2)
def ind (q : ZMod k) : V k := fun t => if t = q then 1 else 0
def Ld (e Y : V k) : V k := fun i => Y (i + 1) * e (i + 2) + e (i + 1) * Y (i + 2)
def Ce (e : V k) : V k := fun i => e i + e (i + 2) + e (i + 1) * e (i + 2)
def T (a : ZMod k) (x : V k) : V k := fun s => x (a + s)

def S (g a : ℕ) (inj : ℕ → ℕ) (w : V k) (c : ℕ → V k) : ℕ → V k
  | 0 => R a w + c 0
  | j + 1 => st (M g (S g a inj w c j)) + R (inj (j + 1)) w + c (j + 1)

theorem z2 (a : ZMod 2) : a + a = 0 := by revert a; decide

theorem vz2 (x : V k) : x + x = 0 := by funext i; exact z2 _

theorem vsub (x y : V k) : x - y = x + y := by
  funext i; simp only [Pi.sub_apply, Pi.add_apply]
  linear_combination (-1 : ZMod 2) * z2 (y i)

theorem M_add (g : ℕ) (x y : V k) : M g (x + y) = M g x + M g y := by
  funext i; simp only [M, Pi.add_apply]; ring

theorem M_zero (g : ℕ) : M g (0 : V k) = 0 := by
  funext i; simp [M]

theorem R_add (s : ℕ) (x y : V k) : R s (x + y) = R s x + R s y := by
  funext i; simp only [R, Pi.add_apply]

theorem M_R (g s : ℕ) (x : V k) : M g (R s x) = R s (M g x) := by
  funext i; simp only [M, R]
  rw [show i + (g : ZMod k) - s = i - s + g by ring, show i - (g : ZMod k) - s = i - s - g by ring]

theorem R_eq_zero (s : ℕ) (x : V k) (h : R s x = 0) : x = 0 := by
  funext i
  have := congrFun h (i + s)
  simpa [R] using this

theorem st_diff (Y e : V k) : st (Y + e) = st Y + (Ce e + Ld e Y) := by
  funext i
  simp only [st, Ce, Ld, Pi.add_apply]
  generalize Y i = a0
  generalize Y (i + 1) = a1
  generalize Y (i + 2) = a2
  generalize e i = b0
  generalize e (i + 1) = b1
  generalize e (i + 2) = b2
  revert a0 a1 a2 b0 b1 b2; decide

theorem Ld_add (e Y Y' : V k) : Ld e (Y + Y') = Ld e Y + Ld e Y' := by
  funext i; simp only [Ld, Pi.add_apply]; ring

theorem Ld_zero (e : V k) : Ld e 0 = 0 := by
  funext i; simp [Ld]

theorem M_T (g : ℕ) (a : ZMod k) (x : V k) : M g (T a x) = T a (M g x) := by
  funext i; simp only [M, T]
  rw [show a + (i + (g : ZMod k)) = a + i + g by ring, show a + (i - (g : ZMod k)) = a + i - g by ring]

theorem Ld_T (a : ZMod k) (e Y : V k) : Ld (T a e) (T a Y) = T a (Ld e Y) := by
  funext i; simp only [Ld, T]
  rw [show a + (i + 1) = a + i + 1 by ring, show a + (i + 2) = a + i + 2 by ring]

theorem TT (a : ZMod k) (y : V k) : T a (T (-a) y) = y := by
  funext i; simp only [T]; congr 1; ring

/-- the translated condition -/
theorem cond_T (g : ℕ) (e : V k) (h : ∀ y : V k, M g (Ld e (M g y)) = 0) (a : ZMod k) :
    ∀ y : V k, M g (Ld (T a e) (M g y)) = 0 := by
  intro y
  have := h (T (-a) y)
  rw [← TT a y, M_T, Ld_T, M_T, this]
  funext i; rfl

theorem S_local (g a : ℕ) (inj : ℕ → ℕ) (w : V k) (c c' : ℕ → V k) :
    ∀ j, (∀ i ≤ j, c i = c' i) → S g a inj w c j = S g a inj w c' j := by
  intro j
  induction j with
  | zero => intro h; simp only [S, h 0 le_rfl]
  | succ j ih =>
    intro h
    simp only [S]
    rw [ih (fun i hi => h i (by omega)), h (j + 1) le_rfl]

theorem S_upd (g a : ℕ) (inj : ℕ → ℕ) (w : V k) (c : ℕ → V k) (j : ℕ) (t : V k) :
    S g a inj w (Function.update c j (c j + t)) j = S g a inj w c j + t := by
  cases j with
  | zero => simp only [S, Function.update_self]; abel
  | succ m =>
    have hl := S_local g a inj w (Function.update c (m + 1) (c (m + 1) + t)) c m
      (fun i hi => by rw [Function.update_of_ne (by omega)])
    simp only [S, hl, Function.update_self]; abel


theorem lit_ne (n : ℕ) (h0 : 0 < n) (h : n < k) : (n : ZMod k) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd; have := Nat.le_of_dvd h0 hd; omega

theorem lit_eq (n : ℕ) (h : k ∣ n) : (n : ZMod k) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]; exact h

theorem ker_triv (g : ℕ) (hk : ¬ 3 ∣ k) (x : V k) (hx : M g x = 0) : x = 0 := by
  have e : ∀ i, x i + x (i + g) + x (i - g) = 0 := fun i => congrFun hx i
  have p3 : ∀ i, x (i + 3 * g) = x i := by
    intro i
    have e1 := e (i + g)
    have e2 := e (i + 2 * g)
    rw [show i + (g : ZMod k) - g = i by ring, show i + (g : ZMod k) + g = i + 2 * g by ring]
      at e1
    rw [show i + 2 * (g : ZMod k) - g = i + g by ring,
      show i + 2 * (g : ZMod k) + g = i + 3 * g by ring] at e2
    linear_combination e2 - e1
  have pn : ∀ n : ℕ, ∀ i, x (i + (n : ZMod k) * (3 * g)) = x i := by
    intro n
    induction n with
    | zero => intro i; simp
    | succ n ih =>
      intro i
      rw [show i + ((n + 1 : ℕ) : ZMod k) * (3 * g) = (i + (n : ZMod k) * (3 * g)) + 3 * g by
        push_cast; ring, p3, ih]
  have hcop : Nat.Coprime 3 k := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]; exact hk
  set u := ZMod.unitOfCoprime 3 hcop
  have hu : (u : ZMod k) = 3 := by simp [u, ZMod.coe_unitOfCoprime]
  have hn : (((u⁻¹ : (ZMod k)ˣ) : ZMod k).val : ZMod k) * (3 * g) = g := by
    rw [ZMod.natCast_zmod_val, ← mul_assoc, ← hu, Units.inv_mul, one_mul]
  have ps : ∀ i, x (i + g) = x i := by
    intro i; have := pn (((u⁻¹ : (ZMod k)ˣ) : ZMod k).val) i; rwa [hn] at this
  funext i
  have ei := e i
  have hm := ps (i - g)
  rw [sub_add_cancel] at hm
  rw [ps i, ← hm] at ei
  simp only [Pi.zero_apply]
  linear_combination ei - z2 (x i)

theorem M_inj (g : ℕ) (hk : ¬ 3 ∣ k) : Function.Injective (M g : V k → V k) := by
  intro x y hxy
  have h0 : M g (x + y) = 0 := by rw [M_add, hxy, vz2]
  have h1 := ker_triv g hk _ h0
  funext i
  have := congrFun h1 i
  simp only [Pi.add_apply, Pi.zero_apply] at this
  linear_combination this - z2 (y i)

theorem KL_inv (g : ℕ) (hk : ¬ 3 ∣ k) (hk1 : k ≠ 1) (e : V k)
    (h : ∀ y : V k, M g (Ld e (M g y)) = 0) : e = 0 := by
  have hs := Finite.surjective_of_injective (M_inj (k := k) g hk)
  have hL : ∀ Y : V k, Ld e Y = 0 := by
    intro Y
    obtain ⟨y, rfl⟩ := hs Y
    exact ker_triv g hk _ (h y)
  have h1 : (1 : ZMod k) ≠ 0 := by
    have := lit_ne (k := k) 1 (by omega) (by have := NeZero.pos k; omega)
    simpa using this
  funext j
  have := congrFun (hL (ind (j - 2 + 1))) (j - 2)
  have hne : j - 2 + 2 ≠ j - 2 + 1 := by
    intro hh; apply h1; linear_combination hh
  simp only [Ld, ind, hne, ite_true, ite_false, one_mul, mul_zero, add_zero, Pi.zero_apply] at this
  rw [show j - 2 + 2 = j by ring] at this
  simpa using this

theorem window (x : V k) (L : ℕ) (hL : 0 < L) (i : ZMod k)
    (hrec : ∀ t : ZMod k, (∀ n < L, x (t + n) = 0) → x (t + L) = 0)
    (hz : ∀ n < L, x (i + n) = 0) : x = 0 := by
  have key : ∀ m n : ℕ, n < L → x (i + ((m + n : ℕ) : ZMod k)) = 0 := by
    intro m
    induction m with
    | zero => intro n hn; simpa using hz n hn
    | succ m ih =>
      intro n hn
      by_cases hn1 : n + 1 < L
      · have := ih (n + 1) hn1
        rwa [show m + (n + 1) = m + 1 + n by omega] at this
      · have hnL : n = L - 1 := by omega
        have := hrec (i + m) (fun n' hn' => by
          have := ih n' hn'; push_cast at this; rwa [add_assoc])
        rw [show m + 1 + n = m + L by omega]; push_cast
        rwa [← add_assoc]
  funext j
  have := key (j - i).val 0 hL
  simpa [ZMod.natCast_zmod_val] using this

theorem lits (K : ℕ) (hk : K ≤ k) :
    ∀ n : ℕ, 0 < n → n < K → (n : ZMod k) ≠ 0 := fun n h0 h => lit_ne n h0 (by omega)

theorem KL1_0 (hk : 6 ≤ k) (e : V k) (h : ∀ y : V k, M 1 (Ld e (M 1 y)) = 0) : e 2 = 0 := by
  have l := lits 6 hk
  have h1 : (1 : ZMod k) ≠ 0 := by simpa using l 1 (by omega) (by omega)
  have h2 : (2 : ZMod k) ≠ 0 := by simpa using l 2 (by omega) (by omega)
  have h3 : (3 : ZMod k) ≠ 0 := by simpa using l 3 (by omega) (by omega)
  have h4 : (4 : ZMod k) ≠ 0 := by simpa using l 4 (by omega) (by omega)
  have h5 : (5 : ZMod k) ≠ 0 := by simpa using l 5 (by omega) (by omega)
  set Z := Ld e (M 1 (ind (0 : ZMod k))) with hZ
  have hM := h (ind 0)
  have hz : Z = 0 := by
    apply window Z 2 (by omega) 1
    · intro t ht
      have e0 := ht 0 (by omega)
      have e1 := ht 1 (by omega)
      have := congrFun hM (t + 1)
      simp only [M, Nat.cast_one, Pi.zero_apply, ← hZ] at this e0 e1
      rw [show t + 1 + 1 = t + ((2 : ℕ) : ZMod k) by push_cast; ring,
        show t + 1 - 1 = t by ring] at this
      simp only [Nat.cast_zero, add_zero] at e0 e1
      rw [e0, e1] at this; simpa using this
    · intro n hn
      interval_cases n <;> norm_num [hZ, Ld, M, ind, h1, h2, h3, h4, h5]
  have := congrFun hz 0
  norm_num [hZ, Ld, M, ind, h1, h2, h3, h4, h5] at this
  exact this

theorem lit_ne' (n : ℕ) (h : ¬ k ∣ n) : (n : ZMod k) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]; exact h

theorem KL2_0 (hk : 10 ≤ k) (e : V k) (h : ∀ y : V k, M 2 (Ld e (M 2 y)) = 0) : e (-1) = 0 := by
  have l := lits 10 hk
  have h1 : (1 : ZMod k) ≠ 0 := by simpa using l 1 (by omega) (by omega)
  have h2 : (2 : ZMod k) ≠ 0 := by simpa using l 2 (by omega) (by omega)
  have h3 : (3 : ZMod k) ≠ 0 := by simpa using l 3 (by omega) (by omega)
  have h4 : (4 : ZMod k) ≠ 0 := by simpa using l 4 (by omega) (by omega)
  have h5 : (5 : ZMod k) ≠ 0 := by simpa using l 5 (by omega) (by omega)
  have h6 : (6 : ZMod k) ≠ 0 := by simpa using l 6 (by omega) (by omega)
  have h7 : (7 : ZMod k) ≠ 0 := by simpa using l 7 (by omega) (by omega)
  have h8 : (8 : ZMod k) ≠ 0 := by simpa using l 8 (by omega) (by omega)
  have h9 : (9 : ZMod k) ≠ 0 := by simpa using l 9 (by omega) (by omega)
  set Z := Ld e (M 2 (ind (0 : ZMod k))) with hZ
  have hM := h (ind 0)
  have hz : Z = 0 := by
    apply window Z 4 (by omega) 2
    · intro t ht
      have e0 := ht 0 (by omega)
      have e2 := ht 2 (by omega)
      have := congrFun hM (t + 2)
      simp only [M, Nat.cast_ofNat, Pi.zero_apply, ← hZ] at this e0 e2
      rw [show t + 2 + 2 = t + ((4 : ℕ) : ZMod k) by push_cast; ring,
        show t + 2 - 2 = t by ring] at this
      simp only [Nat.cast_zero, add_zero] at e0 e2
      rw [e0, e2] at this; simpa using this
    · intro n hn
      interval_cases n <;> norm_num [hZ, Ld, M, ind, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  have := congrFun hz (-3)
  norm_num [hZ, Ld, M, ind, h1, h2, h3, h4, h5, h6, h7, h8, h9] at this
  exact this

theorem KL9_0 (hk : k = 9) (e : V k) (h : ∀ y : V k, M 2 (Ld e (M 2 y)) = 0) : e (-1) = 0 := by
  have l := lits (k := k) 9 (by omega)
  have h1 : (1 : ZMod k) ≠ 0 := by simpa using l 1 (by omega) (by omega)
  have h2 : (2 : ZMod k) ≠ 0 := by simpa using l 2 (by omega) (by omega)
  have h3 : (3 : ZMod k) ≠ 0 := by simpa using l 3 (by omega) (by omega)
  have h4 : (4 : ZMod k) ≠ 0 := by simpa using l 4 (by omega) (by omega)
  have h5 : (5 : ZMod k) ≠ 0 := by simpa using l 5 (by omega) (by omega)
  have h6 : (6 : ZMod k) ≠ 0 := by simpa using l 6 (by omega) (by omega)
  have h7 : (7 : ZMod k) ≠ 0 := by simpa using l 7 (by omega) (by omega)
  have h8 : (8 : ZMod k) ≠ 0 := by simpa using l 8 (by omega) (by omega)
  have h9 : (9 : ZMod k) = 0 := by simpa using lit_eq (k := k) 9 (by rw [hk])
  set Z := Ld e (M 2 (ind (0 : ZMod k))) with hZ
  have hM := h (ind 0)
  have hE : ∀ t, Z t + Z (t + 2) + Z (t - 2) = 0 := by
    intro t; have := congrFun hM t; simpa [M] using this
  have p6 : ∀ t, Z (t + 6) = Z t := by
    intro t
    have a1 := hE (t + 2)
    have a2 := hE (t + 4)
    rw [show t + 2 + 2 = t + 4 by ring, show t + 2 - 2 = t by ring] at a1
    rw [show t + 4 + 2 = t + 6 by ring, show t + 4 - 2 = t + 2 by ring] at a2
    linear_combination a2 - a1
  have p3 : ∀ t, Z (t + 3) = Z t := by
    intro t
    rw [← p6 (t + 3), show t + 3 + 6 = t + 9 by ring, h9, add_zero]
  have hz : Z = 0 := by
    apply window Z 3 (by omega) 2
    · intro t ht
      have e0 := ht 0 (by omega)
      simp only [Nat.cast_zero, add_zero] at e0
      rw [show ((3 : ℕ) : ZMod k) = 3 by norm_num, p3, e0]
    · intro n hn
      interval_cases n <;> norm_num [hZ, Ld, M, ind, h1, h2, h3, h4, h5, h6, h7, h8]
  have := congrFun hz (-3)
  norm_num [hZ, Ld, M, ind, h1, h2, h3, h4, h5, h6, h7, h8] at this
  exact this

theorem KL6_0 (hk : k = 6) (d : V k) (h : ∀ y : V k, M 2 (Ld (M 2 d) (M 2 y)) = 0) :
    M 2 d 1 = 0 := by
  have l := lits (k := k) 6 (by omega)
  have h1 : (1 : ZMod k) ≠ 0 := by simpa using l 1 (by omega) (by omega)
  have h2 : (2 : ZMod k) ≠ 0 := by simpa using l 2 (by omega) (by omega)
  have h3 : (3 : ZMod k) ≠ 0 := by simpa using l 3 (by omega) (by omega)
  have h4 : (4 : ZMod k) ≠ 0 := by simpa using l 4 (by omega) (by omega)
  have h5 : (5 : ZMod k) ≠ 0 := by simpa using l 5 (by omega) (by omega)
  have h6 : (6 : ZMod k) = 0 := by simpa using lit_eq (k := k) 6 (by rw [hk])
  have h7 : (7 : ZMod k) ≠ 0 := by simpa using lit_ne' (k := k) 7 (by rw [hk]; decide)
  have := congrFun (h (ind 0)) 1
  norm_num [Ld, M, ind, h1, h2, h3, h4, h5, h6, h7] at this
  simp only [h6, ite_true] at this
  have i7 : (7 : ZMod k) = 1 := by linear_combination h6
  have i5 : (5 : ZMod k) = -1 := by linear_combination h6
  rw [i7, i5] at this
  simp only [M, Nat.cast_ofNat]
  rw [show (1 : ZMod k) - 2 = -1 by ring, show (1 : ZMod k) + 2 = 3 by norm_num]
  generalize d 1 = a at *
  generalize d 3 = b at *
  generalize d (-1) = c at *
  revert a b c; decide

theorem KL (g : ℕ) (hg : g = 1 ∨ g = 2) (hk1 : k ≠ 1) (hk3 : k ≠ 3) (d : V k)
    (h : ∀ y : V k, M g (Ld (M g d) (M g y)) = 0) : M g d = 0 := by
  by_cases h3 : 3 ∣ k
  · have hk0 := NeZero.pos k
    have k6 : 6 ≤ k := by omega
    rcases hg with rfl | rfl
    · funext j
      have := KL1_0 k6 (T (j - 2) (M 1 d)) (cond_T 1 _ h (j - 2))
      simp only [T] at this
      rwa [show j - 2 + 2 = j by ring] at this
    · by_cases k6' : k = 6
      · funext j
        have h' := cond_T 2 _ h (j - 1)
        rw [← M_T] at h'
        have := KL6_0 k6' (T (j - 1) d) h'
        rw [M_T] at this
        simp only [T] at this
        rwa [show j - 1 + 1 = j by ring] at this
      · funext j
        have h' := cond_T 2 _ h (j + 1)
        by_cases k9 : k = 9
        · have := KL9_0 k9 _ h'
          simp only [T] at this
          rwa [show j + 1 + -1 = j by ring] at this
        · have := KL2_0 (by omega) _ h'
          simp only [T] at this
          rwa [show j + 1 + -1 = j by ring] at this
  · exact KL_inv g h3 hk1 _ h

section run
variable (g a : ℕ) (inj : ℕ → ℕ)

def D (w d : V k) (c : ℕ → V k) (j : ℕ) : V k := S g a inj (w + d) c j + S g a inj w c j

theorem split_sum (x y : V k) : y = x + (y + x) := by
  rw [add_comm y x, ← add_assoc, vz2, zero_add]

theorem D_zero (w d : V k) (c : ℕ → V k) : D g a inj w d c 0 = R a d := by
  funext i
  simp only [D, S, R_add, Pi.add_apply]
  linear_combination z2 (R a w i) + z2 (c 0 i)

theorem D_succ (w d : V k) (c : ℕ → V k) (j : ℕ) :
    D g a inj w d c (j + 1) = Ce (M g (D g a inj w d c j)) +
      Ld (M g (D g a inj w d c j)) (M g (S g a inj w c j)) + R (inj (j + 1)) d := by
  have hs := split_sum (S g a inj w c j) (S g a inj (w + d) c j)
  have : D g a inj w d c (j + 1) = st (M g (S g a inj (w + d) c j)) +
      st (M g (S g a inj w c j)) + R (inj (j + 1)) d := by
    funext i
    simp only [D, S, R_add, Pi.add_apply]
    linear_combination z2 (R (inj (j + 1)) w i) + z2 (c (j + 1) i)
  rw [this]
  rw [hs, M_add, st_diff]
  funext i
  simp only [D, Pi.add_apply]
  linear_combination z2 (st (M g (S g a inj w c j)) i)

theorem D_upd (w d : V k) (c : ℕ → V k) (j : ℕ) (t : V k) :
    D g a inj w d (Function.update c j (c j + t)) j = D g a inj w d c j := by
  simp only [D, S_upd]
  funext i
  simp only [Pi.add_apply]
  linear_combination z2 (t i)

theorem step_lemma (hg : g = 1 ∨ g = 2) (hk1 : k ≠ 1) (hk3 : k ≠ 3) (w d : V k) (j : ℕ)
    (v : V k) (hv : ∀ c, M g (D g a inj w d c (j + 1)) = v) (c : ℕ → V k) :
    M g (D g a inj w d c j) = 0 := by
  apply KL g hg hk1 hk3
  intro y
  have key : ∀ y : V k, M g (D g a inj w d
      (Function.update c j (c j + (y + S g a inj w c j))) (j + 1)) =
      M g (Ce (M g (D g a inj w d c j))) + M g (Ld (M g (D g a inj w d c j)) (M g y)) +
        M g (R (inj (j + 1)) d) := by
    intro y
    rw [D_succ, D_upd, S_upd, M_add, M_add]
    congr 4
    rw [add_comm y, ← add_assoc, vz2, zero_add]
  have e1 := key y
  have e0 := key 0
  rw [hv, M_zero, Ld_zero, M_zero, add_zero] at e0
  rw [hv, e0] at e1
  funext i
  have := congrFun e1 i
  simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
  linear_combination (-1 : ZMod 2) * this

theorem descent (hg : g = 1 ∨ g = 2) (hk1 : k ≠ 1) (hk3 : k ≠ 3) (w d : V k) :
    ∀ j, (∀ c, M g (D g a inj w d c j) = 0) → M g d = 0 := by
  intro j
  induction j with
  | zero =>
    intro h
    have := h (fun _ => 0)
    rw [D_zero, M_R] at this
    exact R_eq_zero _ _ this
  | succ j ih =>
    intro h
    exact ih (step_lemma g a inj hg hk1 hk3 w d j 0 h)

theorem Ce_zero : Ce (0 : V k) = 0 := by funext i; simp [Ce]

theorem Ld_zero_left (Y : V k) : Ld 0 Y = 0 := by funext i; simp [Ld]

theorem forward (w d : V k) (hd : M g d = 0) (c : ℕ → V k) :
    ∀ j, M g (D g a inj w d c j) = 0 ∧ D g a inj w d c (j + 1) = R (inj (j + 1)) d := by
  have hj : ∀ j, M g (D g a inj w d c j) = 0 := by
    intro j
    cases j with
    | zero => rw [D_zero, M_R, hd]; funext i; rfl
    | succ j =>
      induction j with
      | zero =>
        rw [D_succ, D_zero, M_R, hd]
        have : R a (0 : V k) = 0 := by funext i; rfl
        rw [this, Ce_zero, Ld_zero_left, zero_add, zero_add, M_R, hd]; funext i; rfl
      | succ j ih =>
        rw [D_succ, ih, Ce_zero, Ld_zero_left, zero_add, zero_add, M_R, hd]; funext i; rfl
  intro j
  refine ⟨hj j, ?_⟩
  rw [D_succ, hj j, Ce_zero, Ld_zero_left, zero_add, zero_add]

end run

section small
variable (g a : ℕ) (inj : ℕ → ℕ)

theorem D_succ_small (hF1 : ∀ x : V k, st (M g x) = M g x) (w d : V k) (c : ℕ → V k)
    (j : ℕ) : D g a inj w d c (j + 1) = M g (D g a inj w d c j) + R (inj (j + 1)) d := by
  funext i
  simp only [D, S, R_add, hF1, M_add, Pi.add_apply]
  linear_combination z2 (R (inj (j + 1)) w i) + z2 (c (j + 1) i)

theorem small_formula (hF1 : ∀ x : V k, st (M g x) = M g x)
    (hF2 : ∀ x : V k, M g (M g x) = M g x) (hF3 : ∀ s (x : V k), M g (R s x) = M g x)
    (w d : V k) (c : ℕ → V k) : ∀ j, D g a inj w d c (j + 1) =
      R (inj (j + 1)) d + (if (j + 1) % 2 = 1 then M g d else 0) := by
  intro j
  induction j with
  | zero =>
    rw [D_succ_small g a inj hF1, D_zero, hF3, if_pos (by norm_num), add_comm]
  | succ j ih =>
    rw [D_succ_small g a inj hF1, ih, M_add, hF3]
    by_cases hp : (j + 1) % 2 = 1
    · rw [if_pos hp, if_neg (by omega), hF2, vz2, zero_add, add_zero]
    · rw [if_neg hp, if_pos (by omega), M_zero, add_zero, add_comm]

theorem F_one (hk : k = 1) :
    (∀ x : V k, st (M g x) = M g x) ∧ (∀ x : V k, M g (M g x) = M g x) ∧
      (∀ s (x : V k), M g (R s x) = M g x) := by
  subst hk
  have hs : ∀ a b : ZMod 1, a = b := fun a b => Subsingleton.elim a b
  refine ⟨?_, ?_, ?_⟩
  · intro x; funext i
    simp only [st, M]
    rw [hs (i + 1 + g) i, hs (i + 1 - g) i, hs (i + 2 + g) i, hs (i + 2 - g) i, hs (i + 1) i,
      hs (i + 2) i, hs (i + g) i, hs (i - g) i]
    generalize x i = u; revert u; decide
  · intro x; funext i
    simp only [M]
    rw [hs (i + g + g) i, hs (i + g - g) i, hs (i - g + g) i, hs (i - g - g) i, hs (i + g) i,
      hs (i - g) i]
    generalize x i = u; revert u; decide
  · intro s x; funext i
    simp only [M, R]
    rw [hs (i - s) i, hs (i + g - s) i, hs (i - g - s) i, hs (i + g) i, hs (i - g) i]

theorem M_three (hg : g = 1 ∨ g = 2) (x : V 3) (i : ZMod 3) : M g x i = x 0 + x 1 + x 2 := by
  have hs : ∀ x : ZMod 3 → ZMod 2, ∀ i a : ZMod 3, a ≠ 0 →
      x i + x (i + a) + x (i - a) = x 0 + x 1 + x 2 := by decide
  have hg' : (g : ZMod 3) ≠ 0 := by rcases hg with rfl | rfl <;> decide
  exact hs x i g hg'

theorem F_three (hg : g = 1 ∨ g = 2) (hk : k = 3) :
    (∀ x : V k, st (M g x) = M g x) ∧ (∀ x : V k, M g (M g x) = M g x) ∧
      (∀ s (x : V k), M g (R s x) = M g x) := by
  subst hk
  refine ⟨?_, ?_, ?_⟩
  · intro x; funext i
    simp only [st, M_three g hg]
    generalize x 0 + x 1 + x 2 = u; revert u; decide
  · intro x; funext i
    simp only [M_three g hg]
    generalize x 0 + x 1 + x 2 = u; revert u; decide
  · intro s x; funext i
    simp only [M_three g hg, R]
    have hs : ∀ x : ZMod 3 → ZMod 2, ∀ b : ZMod 3,
        x (0 - b) + x (1 - b) + x (2 - b) = x 0 + x 1 + x 2 := by decide
    exact hs x s

end small

section card

theorem per3 (g : ℕ) (x : V k) (hx : M g x = 0) : ∀ i, x (i + 3 * g) = x i := by
  have e : ∀ i, x i + x (i + g) + x (i - g) = 0 := fun i => congrFun hx i
  intro i
  have e1 := e (i + g)
  have e2 := e (i + 2 * g)
  rw [show i + (g : ZMod k) - g = i by ring, show i + (g : ZMod k) + g = i + 2 * g by ring] at e1
  rw [show i + 2 * (g : ZMod k) - g = i + g by ring,
    show i + 2 * (g : ZMod k) + g = i + 3 * g by ring] at e2
  linear_combination e2 - e1

theorem card_triv (g : ℕ) (hk : ¬ 3 ∣ k) : Nat.card {d : V k // M g d = 0} = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  exact ⟨⟨0, M_zero g⟩, fun y => Subtype.ext (ker_triv g hk y.1 y.2)⟩

theorem wd (P : ℕ) (hP : P ∣ k) (i : ZMod k) (c : ℕ) : (i + c).val % P = (i.val + c) % P := by
  rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_mod_of_dvd _ hP, Nat.add_mod,
    Nat.mod_mod_of_dvd _ hP, ← Nat.add_mod]

theorem negc (g : ℕ) (hg : g ≤ k) : -((g : ℕ) : ZMod k) = ((k - g : ℕ) : ZMod k) := by
  rw [Nat.cast_sub hg, ZMod.natCast_self, zero_sub]

def f3 (a b : ZMod 2) (r : ℕ) : ZMod 2 := if r = 0 then a else if r = 1 then b else a + b
def w3 (a b : ZMod 2) : V k := fun i => f3 a b (i.val % 3)

def f6 (a b c d : ZMod 2) (r : ℕ) : ZMod 2 :=
  if r = 0 then a else if r = 1 then b else if r = 2 then c else if r = 3 then d
  else if r = 4 then a + c else b + d
def w6 (a b c d : ZMod 2) : V k := fun i => f6 a b c d (i.val % 6)

theorem w3_mem (h3 : 3 ∣ k) (hk6 : 6 ≤ k) (a b : ZMod 2) : M 1 (w3 (k := k) a b) = 0 := by
  funext i
  simp only [M, Pi.zero_apply]
  rw [sub_eq_add_neg, negc 1 (by omega)]
  simp only [w3]
  rw [wd 3 h3, wd 3 h3]
  obtain ⟨m, hm⟩ := h3
  have hr : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
  rw [show (i.val + 1) % 3 = (i.val % 3 + 1) % 3 by omega,
    show (i.val + (k - 1)) % 3 = (i.val % 3 + 2) % 3 by omega]
  rcases hr with hr | hr | hr <;> rw [hr] <;> (revert a b; decide)

theorem w6_mem (h6 : 6 ∣ k) (a b c d : ZMod 2) : M 2 (w6 (k := k) a b c d) = 0 := by
  have hk := NeZero.pos k
  funext i
  simp only [M, Pi.zero_apply]
  rw [sub_eq_add_neg, negc 2 (by omega)]
  simp only [w6]
  rw [wd 6 h6, wd 6 h6]
  obtain ⟨m, hm⟩ := h6
  have hr : i.val % 6 = 0 ∨ i.val % 6 = 1 ∨ i.val % 6 = 2 ∨ i.val % 6 = 3 ∨ i.val % 6 = 4 ∨
    i.val % 6 = 5 := by omega
  rw [show (i.val + 2) % 6 = (i.val % 6 + 2) % 6 by omega,
    show (i.val + (k - 2)) % 6 = (i.val % 6 + 4) % 6 by omega]
  rcases hr with hr | hr | hr | hr | hr | hr <;> rw [hr] <;> (revert a b c d; decide)

theorem inj1 (hk6 : 6 ≤ k) (z : V k) (hz : M 1 z = 0) (h0 : z 0 = 0) (h1 : z 1 = 0) :
    z = 0 := by
  apply window z 2 (by omega) 0
  · intro t ht
    have e0 := ht 0 (by omega)
    have e1 := ht 1 (by omega)
    have := congrFun hz (t + 1)
    simp only [M, Nat.cast_one, Pi.zero_apply] at this e0 e1
    rw [show t + 1 + 1 = t + ((2 : ℕ) : ZMod k) by push_cast; ring,
      show t + 1 - 1 = t by ring] at this
    simp only [Nat.cast_zero, add_zero] at e0 e1
    rw [e0, e1] at this; simpa using this
  · intro n hn
    interval_cases n <;> simpa using ‹_›

theorem inj2 (z : V k) (hz : M 2 z = 0) (h0 : z 0 = 0) (h1 : z 1 = 0) (h2 : z 2 = 0)
    (h3 : z 3 = 0) : z = 0 := by
  apply window z 4 (by omega) 0
  · intro t ht
    have e0 := ht 0 (by omega)
    have e2 := ht 2 (by omega)
    have := congrFun hz (t + 2)
    simp only [M, Nat.cast_ofNat, Pi.zero_apply] at this e0 e2
    rw [show t + 2 + 2 = t + ((4 : ℕ) : ZMod k) by push_cast; ring,
      show t + 2 - 2 = t by ring] at this
    simp only [Nat.cast_zero, add_zero] at e0 e2
    rw [e0, e2] at this; simpa using this
  · intro n hn
    interval_cases n
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3

theorem valn (n : ℕ) (hn : n < k) : ((n : ℕ) : ZMod k).val = n := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn]

theorem val1 (hk : 2 ≤ k) : (1 : ZMod k).val = 1 := by
  rw [← Nat.cast_one, valn 1 (by omega)]

theorem card1 (h3 : 3 ∣ k) (hk6 : 6 ≤ k) : Nat.card {d : V k // M 1 d = 0} = 4 := by
  have v1 := val1 (k := k) (by omega)
  have e : {d : V k // M 1 d = 0} ≃ ZMod 2 × ZMod 2 :=
    { toFun := fun x => (x.1 0, x.1 1)
      invFun := fun p => ⟨w3 p.1 p.2, w3_mem h3 hk6 p.1 p.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        show w3 (x.1 0) (x.1 1) = x.1
        have hz := inj1 hk6 (w3 (x.1 0) (x.1 1) + x.1)
          (by rw [M_add, w3_mem h3 hk6, x.2, add_zero])
          (by simp only [Pi.add_apply, w3, ZMod.val_zero, Nat.zero_mod, f3]; exact z2 _)
          (by simp only [Pi.add_apply, w3, v1, f3]; norm_num; exact z2 _)
        have := split_sum x.1 (w3 (k := k) (x.1 0) (x.1 1))
        rwa [hz, add_zero] at this
      right_inv := by
        intro p
        simp only [w3, v1, ZMod.val_zero]
        simp [f3] }
  rw [Nat.card_congr e]; simp

theorem card6 (h6 : 6 ∣ k) : Nat.card {d : V k // M 2 d = 0} = 16 := by
  have hk := NeZero.pos k
  have hk6 : 6 ≤ k := Nat.le_of_dvd hk h6
  have v1 := val1 (k := k) (by omega)
  have v2 : (2 : ZMod k).val = 2 := by
    have := valn (k := k) 2 (by omega); simpa using this
  have v3 : (3 : ZMod k).val = 3 := by
    have := valn (k := k) 3 (by omega); simpa using this
  have e : {d : V k // M 2 d = 0} ≃ ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 :=
    { toFun := fun x => (x.1 0, x.1 1, x.1 2, x.1 3)
      invFun := fun p => ⟨w6 p.1 p.2.1 p.2.2.1 p.2.2.2, w6_mem h6 _ _ _ _⟩
      left_inv := by
        intro x
        apply Subtype.ext
        show w6 (x.1 0) (x.1 1) (x.1 2) (x.1 3) = x.1
        have hz := inj2 (w6 (x.1 0) (x.1 1) (x.1 2) (x.1 3) + x.1)
          (by rw [M_add, w6_mem h6, x.2, add_zero])
          (by simp only [Pi.add_apply, w6, ZMod.val_zero, Nat.zero_mod, f6]; exact z2 _)
          (by simp only [Pi.add_apply, w6, v1, f6]; norm_num; exact z2 _)
          (by simp only [Pi.add_apply, w6, v2, f6]; norm_num; exact z2 _)
          (by simp only [Pi.add_apply, w6, v3, f6]; norm_num; exact z2 _)
        have := split_sum x.1 (w6 (k := k) (x.1 0) (x.1 1) (x.1 2) (x.1 3))
        rwa [hz, add_zero] at this
      right_inv := by
        intro p
        simp only [w6, v1, v2, v3, ZMod.val_zero]
        simp [f6] }
  rw [Nat.card_congr e]; simp

theorem K21 (h3 : 3 ∣ k) (hodd : ¬ 2 ∣ k) (z : V k) : M 2 z = 0 ↔ M 1 z = 0 := by
  have eqM : (∀ i, z (i + 3) = z i) → M 2 z = M 1 z := by
    intro hp
    funext i
    simp only [M, Nat.cast_ofNat, Nat.cast_one]
    rw [← hp (i - 1), show i - 1 + 3 = i + 2 by ring, ← hp (i - 2),
      show i - 2 + 3 = i + 1 by ring]
    ring
  constructor
  · intro hz
    have p6 := per3 2 z hz
    have pl : ∀ l : ℕ, ∀ t, z (t + 6 * (l : ZMod k)) = z t := by
      intro l
      induction l with
      | zero => intro t; simp
      | succ l ih =>
        intro t
        have := p6 (t + 6 * (l : ZMod k))
        push_cast at this ⊢
        rw [show t + 6 * ((l : ZMod k) + 1) = t + 6 * l + 3 * 2 by ring, this, ih]
    have hp : ∀ i, z (i + 3) = z i := by
      intro i
      obtain ⟨l, hl⟩ : ∃ l, k = 6 * l + 3 := ⟨k / 6, by omega⟩
      have := pl l (i + 3)
      rw [show i + 3 + 6 * (l : ZMod k) = i + ((6 * l + 3 : ℕ) : ZMod k) by push_cast; ring,
        ← hl, ZMod.natCast_self, add_zero] at this
      exact this.symm
    rw [← eqM hp]; exact hz
  · intro hz
    have hp : ∀ i, z (i + 3) = z i := by
      intro i; have := per3 1 z hz i; simpa using this
    rw [eqM hp]; exact hz

theorem card_odd (h3 : 3 ∣ k) (hodd : ¬ 2 ∣ k) (hk6 : 6 ≤ k) :
    Nat.card {d : V k // M 2 d = 0} = 4 := by
  rw [← card1 h3 hk6]
  exact Nat.card_congr (Equiv.subtypeEquivRight (K21 h3 hodd))

end card

def cc (name : V k) (c : ℕ → V k) : ℕ → V k
  | 0 => name
  | j + 1 => c (j + 1)

theorem cc_self (c : ℕ → V k) : cc (c 0) c = c := by
  funext j; cases j <;> rfl

theorem foldl_S (g a : ℕ) (inj : ℕ → ℕ) (w name : V k) (c : ℕ → V k) (r : ℕ) :
    (List.range r).foldl (fun (x : V k) (j : ℕ) => st (M g x) + R (inj (j + 1)) w + c (j + 1))
      (R a w + name) = S g a inj w (cc name c) r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [List.range_succ, List.foldl_append, ih]
    rfl

theorem ix_eq (n m : ℕ) (i : ZMod (n + 1)) :
    @Eq (ZMod (n + 1))
      (⟨((i : Fin (n + 1)).val + m) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ : Fin (n + 1))
      (i + (m : ZMod (n + 1))) := by
  refine ZMod.val_injective (n + 1) ?_
  rw [ZMod.val_add, ZMod.val_natCast]
  show ((i : Fin (n + 1)).val + m) % (n + 1) = (ZMod.val i + m % (n + 1)) % (n + 1)
  rw [Nat.add_mod_mod]

theorem ix_sub (n s : ℕ) (i : ZMod (n + 1)) :
    @Eq (ZMod (n + 1)) (⟨((i : Fin (n + 1)).val + (n + 1) - s % (n + 1)) % (n + 1),
      Nat.mod_lt _ (Nat.succ_pos n)⟩ : Fin (n + 1)) (i - (s : ZMod (n + 1))) := by
  have hs : s % (n + 1) ≤ n + 1 := (Nat.mod_lt _ (Nat.succ_pos n)).le
  have := ix_eq n (n + 1 - s % (n + 1)) i
  rw [Nat.add_sub_assoc hs, this, Nat.cast_sub hs, ZMod.natCast_mod, ZMod.natCast_self]
  ring

end PEqualNP.Outside.L_meta_32015

namespace PEqualNP.Outside.L_meta_32015

theorem ix_one (n : ℕ) (i : ZMod (n + 1)) :
    @Eq (ZMod (n + 1))
      (⟨((i : Fin (n + 1)).val + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ : Fin (n + 1))
      (i + 1) := by
  rw [ix_eq n 1 i, Nat.cast_one]

theorem ix_two (n : ℕ) (i : ZMod (n + 1)) :
    @Eq (ZMod (n + 1))
      (⟨((i : Fin (n + 1)).val + 2) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ : Fin (n + 1))
      (i + 2) := by
  rw [ix_eq n 2 i, Nat.cast_ofNat]

end PEqualNP.Outside.L_meta_32015

namespace PEqualNP.Outside.L_meta_32015

theorem mainV (n : ℕ) (col : Bool) (j g a : ℕ) (injection : ℕ → ℕ)
    (hcg : (col = false ∧ g = 1) ∨ (col = true ∧ g = 2)) (w : V (n + 1)) :
    (∀ d : V (n + 1), (∃ v, ∀ c' : ℕ → V (n + 1), M g (D g a injection w d c' (j + 1)) = v) ↔
      (n + 1 = 1 ∨ n + 1 = 3) ∨ M g d = 0) ∧
    (∀ d : V (n + 1), (∃ v, ∀ c' : ℕ → V (n + 1), M g (D g a injection w d c' (j + 1)) = v) →
      ∀ c' : ℕ → V (n + 1), D g a injection w d c' (j + 1) = R (injection (j + 1)) d +
        (if (n + 1 = 1 ∨ n + 1 = 3) ∧ (j + 1) % 2 = 1 then M g d else 0)) ∧
    Nat.card {d : V (n + 1) //
      ∃ v, ∀ c' : ℕ → V (n + 1), M g (D g a injection w d c' (j + 1)) = v} =
      2 ^ (if (n + 1 = 1 ∨ n + 1 = 3) then n + 1 else if 3 ∣ n + 1 then
        (if col = true ∧ 2 ∣ n + 1 then 4 else 2) else 0) := by
  have hg : g = 1 ∨ g = 2 := by rcases hcg with h | h; exacts [Or.inl h.2, Or.inr h.2]
  have hk : 0 < n + 1 := Nat.succ_pos n
  by_cases hs : (n + 1 = 1 ∨ n + 1 = 3)
  · obtain ⟨F1, F2, F3⟩ : (∀ x : V (n + 1), st (M g x) = M g x) ∧
        (∀ x : V (n + 1), M g (M g x) = M g x) ∧
        (∀ s (x : V (n + 1)), M g (R s x) = M g x) := by
      rcases hs with h | h
      · exact F_one g h
      · exact F_three g hg h
    have hf := small_formula g a injection F1 F2 F3 w
    have hall : ∀ d : V (n + 1),
        ∃ v, ∀ c' : ℕ → V (n + 1), M g (D g a injection w d c' (j + 1)) = v := by
      intro d
      exact ⟨M g (R (injection (j + 1)) d + if (j + 1) % 2 = 1 then M g d else 0),
        fun c' => by rw [hf]⟩
    refine ⟨fun d => ⟨fun _ => Or.inl hs, fun _ => hall d⟩, fun d _ c' => ?_, ?_⟩
    · rw [hf]
      by_cases hp : (j + 1) % 2 = 1
      · rw [if_pos hp, if_pos ⟨hs, hp⟩]
      · rw [if_neg hp, if_neg (fun h => hp h.2)]
    · rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), if_pos hs]
      simp
  · have hk1 : n + 1 ≠ 1 := fun h => hs (Or.inl h)
    have hk3 : n + 1 ≠ 3 := fun h => hs (Or.inr h)
    have hiff : ∀ d : V (n + 1),
        (∃ v, ∀ c' : ℕ → V (n + 1), M g (D g a injection w d c' (j + 1)) = v) ↔ M g d = 0 := by
      intro d
      constructor
      · rintro ⟨v, h⟩
        exact descent g a injection hg hk1 hk3 w d j
          (step_lemma g a injection hg hk1 hk3 w d j v h)
      · intro hd
        refine ⟨0, fun c' => ?_⟩
        rw [(forward g a injection w d hd c' j).2, M_R, hd]
        rfl
    refine ⟨fun d => ?_, fun d hd c' => ?_, ?_⟩
    · rw [hiff d]
      exact ⟨Or.inr, fun h => h.resolve_left hs⟩
    · rw [(forward g a injection w d ((hiff d).1 hd) _ j).2, if_neg (fun h => hs h.1), add_zero]
    · rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), if_neg hs]
      by_cases h3 : 3 ∣ n + 1
      · have hk6 : 6 ≤ n + 1 := by omega
        rw [if_pos h3]
        rcases hcg with ⟨hc, hg1⟩ | ⟨hc, hg2⟩
        · rw [if_neg (by rw [hc]; simp), hg1, card1 h3 hk6]; norm_num
        · by_cases h2 : 2 ∣ n + 1
          · rw [if_pos ⟨hc, h2⟩, hg2, card6 (by omega)]; norm_num
          · rw [if_neg (fun h => h2 h.2), hg2, card_odd h3 h2 hk6]; norm_num
      · rw [if_neg h3, card_triv g h3]; rfl

end PEqualNP.Outside.L_meta_32015

open PEqualNP.Outside.L_meta_32015 in
theorem PEqualNP.Outside.L_meta_32015 : ∀ (k : ℕ) (hk : 0 < k), ∀ (col : Bool) (r : ℕ), 0 < r →
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val + k - s % k))
  let g := if col then 2 else (1 : ℕ)
  let mix := fun (x : W) (i : Fin k) => x i + x (ix (i.val + g)) + x (ix (i.val + k - g % k))
  let step := fun (x : W) (i : Fin k) =>
    x i + (1 + x (ix (i.val+1))) * x (ix (i.val+2))
  let injection := fun (t : ℕ) => if col then 3*t+1 else 2*(t-1)
  let state := fun (w name : W) (c : ℕ → W) =>
    (List.range r).foldl (fun (x : W) (j : ℕ) =>
      step (mix x) + rot (injection (j+1)) w + c (j+1))
      (rot (if col then 3 else 1) w + name)
  let small := k = 1 ∨ k = 3
  let dim := if small then k else if 3 ∣ k then (if col = true ∧ 2 ∣ k then 4 else 2) else 0
  ∀ w : W,
    let predictable := fun (d : W) => ∃ v : W, ∀ (name : W) (c : ℕ → W),
      mix (state (w+d) name c - state w name c) = v
    (∀ d : W, predictable d ↔ small ∨ mix d = 0) ∧
    (∀ d : W, predictable d → ∀ (name : W) (c : ℕ → W),
      state (w+d) name c - state w name c = rot (injection r) d +
        (if small ∧ r % 2 = 1 then mix d else 0)) ∧
    Nat.card {d : W // predictable d} = 2 ^ dim := by
  intro k hk
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  intro col r hr F W ix rot g mix step injection state small dim w predictable
  have hrot : ∀ s, rot s = R (k := n + 1) s := by
    intro s; funext x i
    exact congrArg x (ix_sub n s i)
  have hmix : mix = M (k := n + 1) g := by
    funext x i
    exact congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl (congrArg x (ix_eq n g i)))
      (congrArg x (ix_sub n g i))
  have hstep : step = st (k := n + 1) := by
    funext x i
    exact congrArg₂ (· + ·) rfl (congrArg₂ (· * ·) (congrArg₂ (· + ·) rfl
      (congrArg x (ix_one n i))) (congrArg x (ix_two n i)))
  have hstate : ∀ w name c, state w name c =
      S (k := n + 1) g (if col then 3 else 1) injection w (cc name c) r := by
    intro w name c
    show (List.range r).foldl _ _ = _
    simp only [hmix, hstep, hrot]
    exact foldl_S (k := n + 1) g _ injection w name c r
  generalize ha : (if col = true then 3 else 1) = a at hstate
  have hD : ∀ d name c, state (w + d) name c - state w name c =
      D (k := n + 1) g a injection w d (cc name c) r := by
    intro d name c; rw [hstate, hstate]; exact vsub (k := n + 1) _ _
  have hcg : (col = false ∧ g = 1) ∨ (col = true ∧ g = 2) := by
    cases col
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have hpc : ∀ d, predictable d ↔
      ∃ v, ∀ c' : ℕ → V (n + 1), M g (D g a injection w d c' r) = v := by
    intro d
    show (∃ v, ∀ name c, mix (state (w + d) name c - state w name c) = v) ↔ _
    simp only [hD, hmix]
    constructor
    · rintro ⟨v, h⟩
      exact ⟨v, fun c' => by have := h (c' 0) c'; rwa [cc_self] at this⟩
    · rintro ⟨v, h⟩
      exact ⟨v, fun name c => h _⟩
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  have hm := mainV n col j g a injection hcg w
  refine ⟨fun d => ?_, fun d hd name c => ?_, ?_⟩
  · rw [hpc, hmix]; exact hm.1 d
  · rw [hD, hrot, hmix]; exact hm.2.1 d ((hpc d).1 hd) (cc name c)
  · rw [Nat.card_congr (Equiv.subtypeEquivRight hpc)]; exact hm.2.2
