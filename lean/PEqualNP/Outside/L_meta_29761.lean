import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29761

variable {k : ℕ} [NeZero k]

abbrev W (k : ℕ) := ZMod k → ZMod 2

def rot (s : ℕ) (x : W k) : W k := fun i => x (i - (s : ZMod k))
def mix (s : ℕ) (x : W k) : W k := fun i => x (i - (s : ZMod k)) + x i + x (i + (s : ZMod k))
def upd (s : ℕ) (x : W k) : W k := fun i =>
  mix s x i + (1 + mix s x (i + 1)) * mix s x (i + 2)
def Dc (A : W k) (i : ZMod k) : ZMod 2 := A i + A (i + 2) + A (i + 1) * A (i + 2)
def Ud (a Y : W k) : W k := fun i => Dc a i + a (i + 1) * Y (i + 2) + a (i + 2) * Y (i + 1)
def EE (s : ℕ) (a b Y : W k) : W k := mix s (Ud a Y) + b
def G (s : ℕ) (a b f : W k) (site : ZMod k) (Y Z : W k) : ZMod 2 :=
  Dc (EE s a b Y) site + EE s a b Y (site + 1) * Z (site + 2) +
    EE s a b Y (site + 2) * Z (site + 1) + f site
def run' (s r1 r2 r3 : ℕ) (key name c1 c2 : W k) : W k :=
  upd s (upd s (rot r1 key + name) + rot r2 key + c1) + rot r3 key + c2
def ind (p : ZMod k) : W k := fun j => if j = p then 1 else 0

theorem z2_self (a : ZMod 2) : a + a = 0 := by revert a; decide

theorem mix_add (s : ℕ) (x y : W k) : mix s (x + y) = mix s x + mix s y := by
  funext i; simp only [mix, Pi.add_apply]; ring

theorem rot_add (s : ℕ) (x y : W k) : rot s (x + y) = rot s x + rot s y := by
  funext i; simp only [rot, Pi.add_apply]

theorem upd_diff (s : ℕ) (x d : W k) (i : ZMod k) :
    upd s (x + d) i + upd s x i =
      Dc (mix s d) i + mix s d (i + 1) * mix s x (i + 2) + mix s d (i + 2) * mix s x (i + 1) := by
  simp only [upd, Dc, mix_add, Pi.add_apply]
  generalize mix s x i = a0
  generalize mix s x (i + 1) = a1
  generalize mix s x (i + 2) = a2
  generalize mix s d i = b0
  generalize mix s d (i + 1) = b1
  generalize mix s d (i + 2) = b2
  revert a0 a1 a2 b0 b1 b2; decide

theorem run_diff (s r1 r2 r3 : ℕ) (key name dk dn c1 c2 : W k) (site : ZMod k) :
    run' s r1 r2 r3 (key + dk) (name + dn) c1 c2 site + run' s r1 r2 r3 key name c1 c2 site =
      G s (mix s (rot r1 dk + dn)) (mix s (rot r2 dk)) (rot r3 dk) site
        (mix s (rot r1 key + name)) (mix s (upd s (rot r1 key + name) + rot r2 key + c1)) := by
  set y := rot r1 key + name with hy
  set X := upd s y + rot r2 key + c1 with hX
  have h1 : rot r1 (key + dk) + (name + dn) = y + (rot r1 dk + dn) := by
    rw [rot_add, hy]; abel
  have hU : upd s (y + (rot r1 dk + dn)) + upd s y = Ud (mix s (rot r1 dk + dn)) (mix s y) := by
    funext i; rw [Pi.add_apply, upd_diff]; rfl
  have h2 : upd s (y + (rot r1 dk + dn)) + rot r2 (key + dk) + c1 =
      X + (Ud (mix s (rot r1 dk + dn)) (mix s y) + rot r2 dk) := by
    rw [← hU, hX, rot_add]
    funext i
    simp only [Pi.add_apply]
    linear_combination (-1 : ZMod 2) * z2_self (upd s y i)
  have hE : mix s (Ud (mix s (rot r1 dk + dn)) (mix s y) + rot r2 dk) =
      EE s (mix s (rot r1 dk + dn)) (mix s (rot r2 dk)) (mix s y) := by
    rw [mix_add]; rfl
  simp only [run']
  rw [h1, h2, rot_add]
  simp only [Pi.add_apply]
  have h3 := upd_diff s X (Ud (mix s (rot r1 dk + dn)) (mix s y) + rot r2 dk) site
  rw [hE] at h3
  simp only [G]
  linear_combination h3 + z2_self (rot r3 key site) + z2_self (c2 site)

theorem mix_surj (s : ℕ) (hk : k % 3 ≠ 0) : Function.Surjective (mix s : W k → W k) := by
  have ker : ∀ x : W k, mix s x = 0 → x = 0 := by
    intro x hx
    have e : ∀ i, x (i - s) + x i + x (i + s) = 0 := fun i => congrFun hx i
    have p3 : ∀ i, x (i + 3 * s) = x i := by
      intro i
      have e1 := e (i + s)
      have e2 := e (i + 2 * s)
      rw [show i + (s : ZMod k) - s = i by ring, show i + (s : ZMod k) + s = i + 2 * s by ring]
        at e1
      rw [show i + 2 * (s : ZMod k) - s = i + s by ring,
        show i + 2 * (s : ZMod k) + s = i + 3 * s by ring] at e2
      linear_combination e2 - e1
    have pn : ∀ n : ℕ, ∀ i, x (i + (n : ZMod k) * (3 * s)) = x i := by
      intro n
      induction n with
      | zero => intro i; simp
      | succ n ih =>
        intro i
        rw [show i + ((n + 1 : ℕ) : ZMod k) * (3 * s) = (i + (n : ZMod k) * (3 * s)) + 3 * s by
          push_cast; ring, p3, ih]
    have hcop : Nat.Coprime 3 k := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      intro hd; exact hk (Nat.mod_eq_zero_of_dvd hd)
    set u := ZMod.unitOfCoprime 3 hcop
    have hu : (u : ZMod k) = 3 := by simp [u, ZMod.coe_unitOfCoprime]
    have hn : (((u⁻¹ : (ZMod k)ˣ) : ZMod k).val : ZMod k) * (3 * s) = s := by
      rw [ZMod.natCast_zmod_val, ← mul_assoc, ← hu, Units.inv_mul, one_mul]
    have ps : ∀ i, x (i + s) = x i := by
      intro i; have := pn (((u⁻¹ : (ZMod k)ˣ) : ZMod k).val) i; rwa [hn] at this
    funext i
    have ei := e i
    have hm := ps (i - s)
    rw [sub_add_cancel] at hm
    rw [ps i, ← hm] at ei
    simp only [Pi.zero_apply]
    linear_combination ei - z2_self (x i)
  have inj : Function.Injective (mix s : W k → W k) := by
    intro x y hxy
    have h0 : mix s (x + y) = 0 := by
      rw [mix_add, hxy]; funext i; exact z2_self _
    have h1 := ker _ h0
    funext i
    have := congrFun h1 i
    simp only [Pi.add_apply, Pi.zero_apply] at this
    linear_combination this - z2_self (y i)
  exact Finite.surjective_of_injective inj


theorem eqA (s r1 r2 r3 : ℕ) (hs : Function.Surjective (mix s : W k → W k))
    (dk dn c1 c2 : W k) (site : ZMod k) (value : ZMod 2) :
    (∀ key name : W k, run' s r1 r2 r3 (key + dk) (name + dn) c1 c2 site +
        run' s r1 r2 r3 key name c1 c2 site = value) ↔
      ∀ Y Z : W k,
        G s (mix s (rot r1 dk + dn)) (mix s (rot r2 dk)) (rot r3 dk) site Y Z = value := by
  constructor
  · intro h Y Z
    obtain ⟨y, rfl⟩ := hs Y
    obtain ⟨X, rfl⟩ := hs Z
    let key : W k := fun i => (X + upd s y + c1) (i + (r2 : ZMod k))
    have hk : rot r2 key = X + upd s y + c1 := by
      funext i; simp only [rot, key, sub_add_cancel]
    have hyy : rot r1 key + (y + rot r1 key) = y := by
      funext i; simp only [Pi.add_apply]; linear_combination z2_self (rot r1 key i)
    have hXX : upd s y + rot r2 key + c1 = X := by
      rw [hk]; funext i; simp only [Pi.add_apply]
      linear_combination z2_self (upd s y i) + z2_self (c1 i)
    have := h key (y + rot r1 key)
    rw [run_diff, hyy, hXX] at this
    exact this
  · intro h key name; rw [run_diff]; exact h _ _

theorem eqB (s : ℕ) (a b f : W k) (site : ZMod k) (value : ZMod 2)
    (h12 : site + 1 ≠ site + 2) :
    (∀ Y Z : W k, G s a b f site Y Z = value) ↔
      ∀ Y : W k, EE s a b Y (site + 1) = 0 ∧ EE s a b Y (site + 2) = 0 ∧
        EE s a b Y site = value + f site := by
  constructor
  · intro h Y
    have g0 := h Y 0
    have g1 := h Y (ind (site + 1))
    have g2 := h Y (ind (site + 2))
    simp only [G, Dc, ind, Pi.zero_apply, h12, Ne.symm h12, ite_true, ite_false,
      mul_zero, mul_one, add_zero] at g0 g1 g2
    clear h
    generalize EE s a b Y site = e0 at *
    generalize EE s a b Y (site + 1) = e1 at *
    generalize EE s a b Y (site + 2) = e2 at *
    generalize f site = fs at *
    revert e0 e1 e2 fs value
    decide
  · intro h Y Z
    obtain ⟨h1, h2, h3⟩ := h Y
    simp only [G, Dc]
    rw [h1, h2, h3]
    linear_combination z2_self (f site)

theorem off_ne (x : ZMod k) (u v : ℕ) (huv : u < v) (hv : v < k) :
    x + (u : ZMod k) ≠ x + (v : ZMod k) := by
  intro h
  have h' := add_left_cancel h
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hv] at h'
  omega

theorem ne_of_off (p x y : ZMod k) (u v : ℕ) (huv : u < v) (hv : v < k)
    (hx : x = p + u) (hy : y = p + v) : x ≠ y := by
  rw [hx, hy]; exact off_ne p u v huv hv

def K1 (a b : W k) (m : ZMod k) : ZMod 2 := Dc a (m - 1) + Dc a m + Dc a (m + 1) + b m
def K2 (a b : W k) (m : ZMod k) : ZMod 2 := Dc a (m - 2) + Dc a m + Dc a (m + 2) + b m

theorem EE1 (a b Y : W k) (m : ZMod k) : EE 1 a b Y m = K1 a b m + a m * Y (m + 1) +
    a (m + 1) * Y m + a (m + 1) * Y (m + 2) + a (m + 2) * Y (m + 1) +
    a (m + 2) * Y (m + 3) + a (m + 3) * Y (m + 2) := by
  simp only [EE, mix, Ud, K1, Pi.add_apply, Nat.cast_one]
  rw [show m - 1 + 1 = m by ring, show m - 1 + 2 = m + 1 by ring,
    show m + 1 + 1 = m + 2 by ring, show m + 1 + 2 = m + 3 by ring]
  ring

theorem EE2 (a b Y : W k) (m : ZMod k) : EE 2 a b Y m = K2 a b m + a m * Y (m - 1) +
    a (m - 1) * Y m + a (m + 2) * Y (m + 1) + a (m + 1) * Y (m + 2) +
    a (m + 4) * Y (m + 3) + a (m + 3) * Y (m + 4) := by
  simp only [EE, mix, Ud, K2, Pi.add_apply, Nat.cast_ofNat]
  rw [show m - 2 + 1 = m - 1 by ring, show m - 2 + 2 = m by ring,
    show m + 2 + 1 = m + 3 by ring, show m + 2 + 2 = m + 4 by ring]
  ring

theorem C1 (hk : 7 ≤ k) (a b : W k) (m : ZMod k) (c : ZMod 2) :
    (∀ Y : W k, EE 1 a b Y m = c) ↔
      (a m = 0 ∧ a (m + 1) = 0 ∧ a (m + 2) = 0 ∧ a (m + 3) = 0 ∧ K1 a b m = c) := by
  have n01 : m ≠ m + 1 := ne_of_off m _ _ 0 1 (by omega) (by omega) (by simp) (by simp)
  have n02 : m ≠ m + 2 := ne_of_off m _ _ 0 2 (by omega) (by omega) (by simp) (by simp)
  have n03 : m ≠ m + 3 := ne_of_off m _ _ 0 3 (by omega) (by omega) (by simp) (by simp)
  have n12 : m + 1 ≠ m + 2 := ne_of_off m _ _ 1 2 (by omega) (by omega) (by simp) (by simp)
  have n13 : m + 1 ≠ m + 3 := ne_of_off m _ _ 1 3 (by omega) (by omega) (by simp) (by simp)
  have n23 : m + 2 ≠ m + 3 := ne_of_off m _ _ 2 3 (by omega) (by omega) (by simp) (by simp)
  constructor
  · intro h
    have g0 := h 0
    have g1 := h (ind m)
    have g2 := h (ind (m + 1))
    have g3 := h (ind (m + 2))
    have g4 := h (ind (m + 3))
    simp only [EE1, ind, Pi.zero_apply, n01, n02, n03, n12, n13, n23, Ne.symm n01,
      Ne.symm n02, Ne.symm n03, Ne.symm n12, Ne.symm n13, Ne.symm n23, ite_true, ite_false,
      mul_zero, mul_one, add_zero] at g0 g1 g2 g3 g4
    clear h
    generalize a m = A0 at *
    generalize a (m + 1) = A1 at *
    generalize a (m + 2) = A2 at *
    generalize a (m + 3) = A3 at *
    generalize K1 a b m = K at *
    revert A0 A1 A2 A3 K c
    decide
  · rintro ⟨h0, h1, h2, h3, hK⟩ Y
    rw [EE1, h0, h1, h2, h3]
    simpa using hK

theorem C2 (hk : 7 ≤ k) (a b : W k) (m : ZMod k) (c : ZMod 2) :
    (∀ Y : W k, EE 2 a b Y m = c) ↔
      (a (m - 1) = 0 ∧ a m = 0 ∧ a (m + 1) = 0 ∧ a (m + 2) = 0 ∧ a (m + 3) = 0 ∧
        a (m + 4) = 0 ∧ K2 a b m = c) := by
  have e : ∀ u v : ℕ, u < v → v < 6 → ∀ x y : ZMod k, x = m - 1 + u → y = m - 1 + v → x ≠ y :=
    fun u v huv hv x y hx hy => ne_of_off (m - 1) x y u v huv (by omega) hx hy
  have n01 : m - 1 ≠ m := e 0 1 (by omega) (by omega) _ _ (by simp) (by simp)
  have n02 : m - 1 ≠ m + 1 := e 0 2 (by omega) (by omega) _ _ (by simp) (by push_cast; ring)
  have n03 : m - 1 ≠ m + 2 := e 0 3 (by omega) (by omega) _ _ (by simp) (by push_cast; ring)
  have n04 : m - 1 ≠ m + 3 := e 0 4 (by omega) (by omega) _ _ (by simp) (by push_cast; ring)
  have n05 : m - 1 ≠ m + 4 := e 0 5 (by omega) (by omega) _ _ (by simp) (by push_cast; ring)
  have n12 : m ≠ m + 1 := e 1 2 (by omega) (by omega) _ _ (by simp) (by push_cast; ring)
  have n13 : m ≠ m + 2 := e 1 3 (by omega) (by omega) _ _ (by simp) (by push_cast; ring)
  have n14 : m ≠ m + 3 := e 1 4 (by omega) (by omega) _ _ (by simp) (by push_cast; ring)
  have n15 : m ≠ m + 4 := e 1 5 (by omega) (by omega) _ _ (by simp) (by push_cast; ring)
  have n23 : m + 1 ≠ m + 2 := e 2 3 (by omega) (by omega) _ _ (by push_cast; ring)
    (by push_cast; ring)
  have n24 : m + 1 ≠ m + 3 := e 2 4 (by omega) (by omega) _ _ (by push_cast; ring)
    (by push_cast; ring)
  have n25 : m + 1 ≠ m + 4 := e 2 5 (by omega) (by omega) _ _ (by push_cast; ring)
    (by push_cast; ring)
  have n34 : m + 2 ≠ m + 3 := e 3 4 (by omega) (by omega) _ _ (by push_cast; ring)
    (by push_cast; ring)
  have n35 : m + 2 ≠ m + 4 := e 3 5 (by omega) (by omega) _ _ (by push_cast; ring)
    (by push_cast; ring)
  have n45 : m + 3 ≠ m + 4 := e 4 5 (by omega) (by omega) _ _ (by push_cast; ring)
    (by push_cast; ring)
  constructor
  · intro h
    have g0 := h 0
    have g1 := h (ind (m - 1))
    have g2 := h (ind m)
    have g3 := h (ind (m + 1))
    have g4 := h (ind (m + 2))
    have g5 := h (ind (m + 3))
    have g6 := h (ind (m + 4))
    simp only [EE2, ind, Pi.zero_apply, n01, n02, n03, n04, n05, n12, n13, n14, n15, n23,
      n24, n25, n34, n35, n45, Ne.symm n01, Ne.symm n02, Ne.symm n03, Ne.symm n04,
      Ne.symm n05, Ne.symm n12, Ne.symm n13, Ne.symm n14, Ne.symm n15, Ne.symm n23,
      Ne.symm n24, Ne.symm n25, Ne.symm n34, Ne.symm n35, Ne.symm n45, ite_true, ite_false,
      mul_zero, mul_one, add_zero] at g0 g1 g2 g3 g4 g5 g6
    clear h
    exact ⟨by linear_combination g2 - g0, by linear_combination g1 - g0,
      by linear_combination g4 - g0, by linear_combination g3 - g0,
      by linear_combination g6 - g0, by linear_combination g5 - g0, g0⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, hK⟩ Y
    rw [EE2, h0, h1, h2, h3, h4, h5]
    simpa using hK

theorem idx (site : ZMod k) :
    site + 1 + 1 = site + 2 ∧ site + 1 + 2 = site + 3 ∧ site + 1 + 3 = site + 4 ∧
    site + 1 + 4 = site + 5 ∧ site + 2 + 1 = site + 3 ∧ site + 2 + 2 = site + 4 ∧
    site + 2 + 3 = site + 5 ∧ site + 2 + 4 = site + 6 ∧ site + 3 + 1 = site + 4 ∧
    site + 3 + 2 = site + 5 ∧ site + 4 + 1 = site + 5 ∧ site + 4 + 2 = site + 6 ∧
    site + 1 - 1 = site ∧ site + 2 - 1 = site + 1 ∧ site + 1 - 2 = site - 1 ∧
    site + 2 - 2 = site ∧ site - 1 + 1 = site ∧ site - 1 + 2 = site + 1 ∧
    site - 2 + 1 = site - 1 ∧ site - 2 + 2 = site := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem finQ (a : W k) (base : ZMod k) (N : ℕ) (h : ∀ q : Fin N, a (base + (q.val : ZMod k)) = 0)
    (c : ℕ) (hc : c < N) (x : ZMod k) (hx : x = base + c) : a x = 0 := by
  rw [hx]; exact h ⟨c, hc⟩

theorem atx (a : W k) (base : ZMod k) (c : ℕ) (x : ZMod k) (hx : x = base + c) (h : a x = 0) :
    a (base + c) = 0 := by
  rw [← hx]; exact h

theorem main_row (hk7 : 7 ≤ k) (hk3 : k % 3 ≠ 0) (c1 c2 dn dk : W k) (site : ZMod k)
    (value : ZMod 2) :
    (∀ key name : W k, run' 1 1 0 2 (key + dk) (name + dn) c1 c2 site +
        run' 1 1 0 2 key name c1 c2 site = value) ↔
      ((∀ q : Fin 6, mix 1 (rot 1 dk + dn) (site - 0 + (q.val : ZMod k)) = 0) ∧
        mix 1 (rot 0 dk) (site + 1) = 0 ∧ mix 1 (rot 0 dk) (site + 2) = 0 ∧
        value = mix 1 (rot 1 dk + dn) (site - 1) + mix 1 (rot 0 dk) site + rot 2 dk site) := by
  have h12 : site + 1 ≠ site + 2 :=
    ne_of_off site _ _ 1 2 (by omega) (by omega) (by simp) (by simp)
  rw [eqA 1 1 0 2 (mix_surj 1 hk3), eqB 1 _ _ _ site value h12]
  set a := mix 1 (rot 1 dk + dn)
  set b := mix 1 (rot 0 dk)
  set f := rot 2 dk
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19,
    i20⟩ := idx site
  simp only [forall_and]
  rw [C1 hk7 a b (site + 1) 0, C1 hk7 a b (site + 2) 0, C1 hk7 a b site (value + f site)]
  simp only [K1, Dc, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17,
    i18, i19, i20]
  constructor
  · rintro ⟨⟨-, -, -, z4, hK1⟩, ⟨-, -, -, z5, hK2⟩, ⟨z0, z1, z2, z3, hK0⟩⟩
    simp only [z0, z1, z2, z3, z4, z5, mul_zero, zero_mul, add_zero, zero_add] at hK0 hK1 hK2
    refine ⟨?_, hK1, hK2, ?_⟩
    · intro q
      have hq := q.isLt
      generalize q.val = c at hq ⊢
      interval_cases c
      · exact atx a _ 0 site (by push_cast; ring) z0
      · exact atx a _ 1 (site + 1) (by push_cast; ring) z1
      · exact atx a _ 2 (site + 2) (by push_cast; ring) z2
      · exact atx a _ 3 (site + 3) (by push_cast; ring) z3
      · exact atx a _ 4 (site + 4) (by push_cast; ring) z4
      · exact atx a _ 5 (site + 5) (by push_cast; ring) z5
    · linear_combination (-1 : ZMod 2) * hK0 - z2_self (f site)
  · rintro ⟨hq, hb1, hb2, hv⟩
    have z0 := finQ a _ 6 hq 0 (by omega) site (by push_cast; ring)
    have z1 := finQ a _ 6 hq 1 (by omega) (site + 1) (by push_cast; ring)
    have z2 := finQ a _ 6 hq 2 (by omega) (site + 2) (by push_cast; ring)
    have z3 := finQ a _ 6 hq 3 (by omega) (site + 3) (by push_cast; ring)
    have z4 := finQ a _ 6 hq 4 (by omega) (site + 4) (by push_cast; ring)
    have z5 := finQ a _ 6 hq 5 (by omega) (site + 5) (by push_cast; ring)
    refine ⟨⟨z1, z2, z3, z4, ?_⟩, ⟨z2, z3, z4, z5, ?_⟩, ⟨z0, z1, z2, z3, ?_⟩⟩ <;>
      simp only [z0, z1, z2, z3, z4, z5, mul_zero, zero_mul, add_zero, zero_add]
    · exact hb1
    · exact hb2
    · linear_combination (-1 : ZMod 2) * hv - z2_self (f site)

theorem main_col (hk7 : 7 ≤ k) (hk3 : k % 3 ≠ 0) (c1 c2 dn dk : W k) (site : ZMod k)
    (value : ZMod 2) :
    (∀ key name : W k, run' 2 3 4 7 (key + dk) (name + dn) c1 c2 site +
        run' 2 3 4 7 key name c1 c2 site = value) ↔
      ((∀ q : Fin 8, mix 2 (rot 3 dk + dn) (site - 1 + (q.val : ZMod k)) = 0) ∧
        mix 2 (rot 4 dk) (site + 1) = 0 ∧ mix 2 (rot 4 dk) (site + 2) = 0 ∧
        value = mix 2 (rot 3 dk + dn) (site - 2) + mix 2 (rot 4 dk) site + rot 7 dk site) := by
  have h12 : site + 1 ≠ site + 2 :=
    ne_of_off site _ _ 1 2 (by omega) (by omega) (by simp) (by simp)
  rw [eqA 2 3 4 7 (mix_surj 2 hk3), eqB 2 _ _ _ site value h12]
  set a := mix 2 (rot 3 dk + dn)
  set b := mix 2 (rot 4 dk)
  set f := rot 7 dk
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19,
    i20⟩ := idx site
  simp only [forall_and]
  rw [C2 hk7 a b (site + 1) 0, C2 hk7 a b (site + 2) 0, C2 hk7 a b site (value + f site)]
  simp only [K2, Dc, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17,
    i18, i19, i20]
  constructor
  · rintro ⟨⟨-, -, -, -, -, z5, hK1⟩, ⟨-, -, -, -, -, z6, hK2⟩, ⟨zm, z0, z1, z2, z3, z4, hK0⟩⟩
    simp only [zm, z0, z1, z2, z3, z4, z5, z6, mul_zero, zero_mul, add_zero, zero_add]
      at hK0 hK1 hK2
    refine ⟨?_, hK1, hK2, ?_⟩
    · intro q
      have hq := q.isLt
      generalize q.val = c at hq ⊢
      interval_cases c
      · exact atx a _ 0 (site - 1) (by push_cast; ring) zm
      · exact atx a _ 1 site (by push_cast; ring) z0
      · exact atx a _ 2 (site + 1) (by push_cast; ring) z1
      · exact atx a _ 3 (site + 2) (by push_cast; ring) z2
      · exact atx a _ 4 (site + 3) (by push_cast; ring) z3
      · exact atx a _ 5 (site + 4) (by push_cast; ring) z4
      · exact atx a _ 6 (site + 5) (by push_cast; ring) z5
      · exact atx a _ 7 (site + 6) (by push_cast; ring) z6
    · linear_combination (-1 : ZMod 2) * hK0 - z2_self (f site)
  · rintro ⟨hq, hb1, hb2, hv⟩
    have zm := finQ a _ 8 hq 0 (by omega) (site - 1) (by push_cast; ring)
    have z0 := finQ a _ 8 hq 1 (by omega) site (by push_cast; ring)
    have z1 := finQ a _ 8 hq 2 (by omega) (site + 1) (by push_cast; ring)
    have z2 := finQ a _ 8 hq 3 (by omega) (site + 2) (by push_cast; ring)
    have z3 := finQ a _ 8 hq 4 (by omega) (site + 3) (by push_cast; ring)
    have z4 := finQ a _ 8 hq 5 (by omega) (site + 4) (by push_cast; ring)
    have z5 := finQ a _ 8 hq 6 (by omega) (site + 5) (by push_cast; ring)
    have z6 := finQ a _ 8 hq 7 (by omega) (site + 6) (by push_cast; ring)
    refine ⟨⟨z0, z1, z2, z3, z4, z5, ?_⟩, ⟨z1, z2, z3, z4, z5, z6, ?_⟩,
      ⟨zm, z0, z1, z2, z3, z4, ?_⟩⟩ <;>
      simp only [zm, z0, z1, z2, z3, z4, z5, z6, mul_zero, zero_mul, add_zero, zero_add]
    · exact hb1
    · exact hb2
    · linear_combination (-1 : ZMod 2) * hv - z2_self (f site)

end PEqualNP.Outside.L_meta_29761

open PEqualNP.Outside.L_meta_29761 in
theorem PEqualNP.Outside.L_meta_29761 : ∀ (k : ℕ) [NeZero k], 7 ≤ k → k % 3 ≠ 0 →
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
  ∀ (col : Bool) (c1 c2 dn dk : W) (site : I) (value : ZMod 2),
    let s : ℕ := if col then 2 else 1
    let a := mix s (rot (if col then 3 else 1) dk + dn)
    let b := mix s (rot (if col then 4 else 0) dk)
    let f := rot (if col then 7 else 2) dk
    Iff (∀ key name : W,
      run col (key+dk) (name+dn) c1 c2 site + run col key name c1 c2 site = value)
      ((∀ q : Fin (if col then 8 else 6),
        a (site - (if col then 1 else 0) + (q.val : I)) = 0) ∧
       b (site+1) = 0 ∧ b (site+2) = 0 ∧
       value = a (site-(if col then 2 else 1)) + b site + f site) := by
  intro k _ hk7 hk3 I W rot mix update run col c1 c2 dn dk site value s a b f
  cases col
  · exact main_row hk7 hk3 c1 c2 dn dk site value
  · exact main_col hk7 hk3 c1 c2 dn dk site value
