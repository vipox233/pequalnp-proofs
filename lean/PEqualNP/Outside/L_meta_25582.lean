import Mathlib
import PEqualNP.Defs

-- L-meta-25582: on the integer line, the state after s rounds at z reads starting bits z-2s+3 .. z+3s, and for
-- s >= 4 the lowest one enters only through the last injection. So the guard read at round 5+j has lead starting
-- bit H+5-5(5+j)+f; the leads fall by at least 4 and stay within k-1 positions, so flipping a lead toggles its own
-- guard and keeps all earlier ones. Halving inside the cube of words fixed off the pivots leaves one word.
-- Agreement: below the moving boundary (cut minus 3 per round) both runs agree; an odd guard keeps one more bit.

namespace PEqualNP.Outside.L_meta_25582_aux

/-! ## Toolkit: cyclic bit view of k-bit words, rotation / step bit lemmas, dependency windows,
triangular injectivity and the counting endgame. -/

def pz (k x : ℕ) (n : ℤ) : Bool := x.testBit (n % (k : ℤ)).toNat

def rotF (k s word : ℕ) : ℕ := ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def stepF (k x : ℕ) : ℕ :=
  (List.range k).foldl (fun acc i =>
    acc ||| ((xor (x.testBit i) (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))).toNat <<< i)) 0

theorem pz_nat (k x a : ℕ) : pz k x (a : ℤ) = x.testBit (a % k) := by
  unfold pz; rw [← Int.natCast_mod, Int.toNat_natCast]

theorem pz_lt (k x i : ℕ) (hi : i < k) : pz k x (i : ℤ) = x.testBit i := by
  rw [pz_nat, Nat.mod_eq_of_lt hi]

theorem pz_modEq {k x : ℕ} {n n' : ℤ} (h : n ≡ n' [ZMOD k]) : pz k x n = pz k x n' := by
  unfold pz; rw [show n % (k : ℤ) = n' % (k : ℤ) from h]

theorem pz_add_k (k x : ℕ) (n : ℤ) : pz k x (n + k) = pz k x n :=
  pz_modEq (by simp [Int.ModEq])

theorem pz_sub_k (k x : ℕ) (n : ℤ) : pz k x (n - k) = pz k x n := by
  rw [← pz_add_k k x (n - k), sub_add_cancel]

theorem pz_xor (k a b : ℕ) (n : ℤ) : pz k (a ^^^ b) n = xor (pz k a n) (pz k b n) := by
  unfold pz; rw [Nat.testBit_xor]

theorem toNat_lt {k : ℕ} (hk : 0 < k) (n : ℤ) : (n % (k : ℤ)).toNat < k := by
  have h0 := Int.emod_nonneg n (by omega : (k : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos n (by omega : (0 : ℤ) < k)
  omega

theorem toNat_cast {k : ℕ} (hk : 0 < k) (n : ℤ) : (((n % (k : ℤ)).toNat : ℕ) : ℤ) = n % k :=
  Int.toNat_of_nonneg (Int.emod_nonneg n (by omega))

theorem big_false {k x j : ℕ} (hx : x < 2 ^ k) (hj : k ≤ j) : x.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hj))

theorem lt_pow_iff_bits (x m : ℕ) : x < 2 ^ m ↔ ∀ i, m ≤ i → x.testBit i = false :=
  ⟨fun h _ hi => big_false h hi, fun h => Nat.lt_pow_two_of_testBit x h⟩

theorem rotF_lt (k s x : ℕ) : rotF k s x < 2 ^ k := Nat.mod_lt _ (by positivity)

theorem testBit_rotF {k s x i : ℕ} (hx : x < 2 ^ k) (hi : i < k) :
    (rotF k s x).testBit i = x.testBit ((i + k - s % k) % k) := by
  have hk : 0 < k := by omega
  have hs : s % k < k := Nat.mod_lt _ hk
  unfold rotF
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  simp only [hi, decide_true, Bool.true_and]
  by_cases h : s % k ≤ i
  · rw [big_false hx (by omega : k ≤ k - s % k + i)]
    have : (i + k - s % k) % k = i - s % k := by
      rw [show i + k - s % k = (i - s % k) + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    simp [h, this]
  · have : (i + k - s % k) % k = k - s % k + i := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    simp [show ¬ (i ≥ s % k) by omega, this]

theorem pz_rotF {k s x : ℕ} (hk : 0 < k) (hx : x < 2 ^ k) (n : ℤ) :
    pz k (rotF k s x) n = pz k x (n - s) := by
  have hi : (n % (k : ℤ)).toNat < k := toNat_lt hk n
  have hin := toNat_cast hk n
  have hs : s % k < k := Nat.mod_lt _ hk
  calc pz k (rotF k s x) n = (rotF k s x).testBit (n % (k : ℤ)).toNat := rfl
    _ = x.testBit (((n % (k : ℤ)).toNat + k - s % k) % k) := testBit_rotF hx hi
    _ = pz k x (((n % (k : ℤ)).toNat + k - s % k : ℕ) : ℤ) := (pz_nat _ _ _).symm
    _ = pz k x (n - s) := by
      apply pz_modEq
      rw [Nat.cast_sub (by omega), Nat.cast_add, hin, Int.natCast_mod]
      have h1 : n % (k : ℤ) ≡ n [ZMOD k] := Int.mod_modEq n k
      have h2 : (s : ℤ) % k ≡ s [ZMOD k] := Int.mod_modEq s k
      have h3 : (k : ℤ) ≡ 0 [ZMOD k] := by simp [Int.ModEq]
      simpa using (h1.add h3).sub h2

theorem testBit_foldl_or (g : ℕ → Bool) (n j : ℕ) :
    ((List.range n).foldl (fun acc i => acc ||| ((g i).toNat <<< i)) 0).testBit j =
      (decide (j < n) && g j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.testBit_or, ih]
    rcases lt_trichotomy j n with h | h | h
    · cases g n <;> simp [h, Nat.shiftLeft_eq, show j < n + 1 by omega,
        show n ≠ j by omega]
    · subst h; cases g j <;> simp [Nat.shiftLeft_eq]
    · cases g n <;> simp [Nat.shiftLeft_eq, show ¬ j < n by omega,
        show ¬ j < n + 1 by omega, show n ≠ j by omega]

theorem testBit_stepF (k x i : ℕ) : (stepF k x).testBit i =
    (decide (i < k) && xor (x.testBit i) (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))) :=
  testBit_foldl_or (fun i => xor (x.testBit i) (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))) k i

theorem stepF_lt (k x : ℕ) : stepF k x < 2 ^ k :=
  Nat.lt_pow_two_of_testBit _ (fun i hi => by rw [testBit_stepF]; simp [show ¬ i < k by omega])

theorem pz_stepF {k : ℕ} (hk : 0 < k) (x : ℕ) (n : ℤ) :
    pz k (stepF k x) n = xor (pz k x n) (!(pz k x (n + 1)) && pz k x (n + 2)) := by
  have hi : (n % (k : ℤ)).toNat < k := toNat_lt hk n
  have hin := toNat_cast hk n
  have e : ∀ a : ℕ, pz k x (n + a) = x.testBit (((n % (k : ℤ)).toNat + a) % k) := by
    intro a; rw [← pz_nat]; apply pz_modEq; push_cast; rw [hin]
    exact ((Int.mod_modEq n k).add_right _).symm
  have e0 : pz k x n = x.testBit (n % (k : ℤ)).toNat := by
    have := e 0; simpa [Nat.mod_eq_of_lt hi] using this
  have e1 := e 1
  have e2 := e 2
  push_cast at e1 e2
  rw [e0, e1, e2]
  show (stepF k x).testBit (n % (k : ℤ)).toNat = _
  rw [testBit_stepF]; simp [hi]

/-! ### dependency windows -/

/-- bit `n` of `F w` depends only on key bits `n+lo .. n+hi` (cyclic). -/
def Dep (k : ℕ) (F : ℕ → ℕ) (lo hi : ℤ) : Prop :=
  ∀ w w' : ℕ, w < 2 ^ k → w' < 2 ^ k → ∀ n : ℤ,
    (∀ t : ℤ, lo ≤ t → t ≤ hi → pz k w (n + t) = pz k w' (n + t)) → pz k (F w) n = pz k (F w') n

/-- bit `n` of `F w` is key bit `n+e` XOR a function of key bits `n+lo .. n+hi`. -/
def DepL (k : ℕ) (F : ℕ → ℕ) (e lo hi : ℤ) : Prop :=
  ∀ w w' : ℕ, w < 2 ^ k → w' < 2 ^ k → ∀ n : ℤ,
    (∀ t : ℤ, lo ≤ t → t ≤ hi → pz k w (n + t) = pz k w' (n + t)) →
      xor (pz k (F w) n) (pz k w (n + e)) = xor (pz k (F w') n) (pz k w' (n + e))

def Bd (k : ℕ) (F : ℕ → ℕ) : Prop := ∀ w, w < 2 ^ k → F w < 2 ^ k

theorem xor_cancel_left {a b c : Bool} (h : xor a b = xor a c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem xor_cancel_right {a b c : Bool} (h : xor a b = xor c b) : a = c := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem Dep_mono {k F lo hi lo' hi'} (h : Dep k F lo hi) (h1 : lo' ≤ lo) (h2 : hi ≤ hi') :
    Dep k F lo' hi' :=
  fun w w' hw hw' n hag => h w w' hw hw' n (fun t a b => hag t (by omega) (by omega))

theorem DepL_mono {k F e lo hi lo' hi'} (h : DepL k F e lo hi) (h1 : lo' ≤ lo) (h2 : hi ≤ hi') :
    DepL k F e lo' hi' :=
  fun w w' hw hw' n hag => h w w' hw hw' n (fun t a b => hag t (by omega) (by omega))

theorem Dep_const (k c : ℕ) (lo hi : ℤ) : Dep k (fun _ => c) lo hi :=
  fun _ _ _ _ _ _ => rfl

theorem DepL_key {k : ℕ} (hk : 0 < k) (s : ℕ) (lo hi : ℤ) :
    DepL k (fun w => rotF k s w) (-(s : ℤ)) lo hi := by
  intro w w' hw hw' n _
  simp only [pz_rotF hk hw, pz_rotF hk hw', ← sub_eq_add_neg, Bool.xor_self]

theorem Dep_key {k : ℕ} (hk : 0 < k) (s : ℕ) : Dep k (fun w => rotF k s w) (-(s : ℤ)) (-(s : ℤ)) := by
  intro w w' hw hw' n hag
  simp only [pz_rotF hk hw, pz_rotF hk hw', sub_eq_add_neg]
  exact hag _ le_rfl le_rfl

theorem Dep_xor {k F G lo hi} (hF : Dep k F lo hi) (hG : Dep k G lo hi) :
    Dep k (fun w => F w ^^^ G w) lo hi := by
  intro w w' hw hw' n hag
  simp only [pz_xor, hF w w' hw hw' n hag, hG w w' hw hw' n hag]

theorem DepL_xor {k F G e lo hi} (hF : DepL k F e lo hi) (hG : Dep k G lo hi) :
    DepL k (fun w => F w ^^^ G w) e lo hi := by
  intro w w' hw hw' n hag
  simp only [pz_xor, hG w w' hw hw' n hag, Bool.xor_right_comm _ (pz k (G w') n)]
  rw [hF w w' hw hw' n hag]

theorem DepL_xor_left {k F G e lo hi} (hF : Dep k F lo hi) (hG : DepL k G e lo hi) :
    DepL k (fun w => F w ^^^ G w) e lo hi := by
  intro w w' hw hw' n hag
  simp only [pz_xor, hF w w' hw hw' n hag, Bool.xor_assoc]
  rw [hG w w' hw hw' n hag]

theorem Dep_of_DepL {k F e lo hi lo' hi'} (h : DepL k F e lo hi) (h1 : lo' ≤ lo) (h2 : hi ≤ hi')
    (h3 : lo' ≤ e) (h4 : e ≤ hi') : Dep k F lo' hi' := by
  intro w w' hw hw' n hag
  have a := h w w' hw hw' n (fun t a b => hag t (by omega) (by omega))
  rw [hag e h3 h4] at a
  exact xor_cancel_right a

theorem Dep_rot {k F lo hi} (hk : 0 < k) (hB : Bd k F) (hF : Dep k F lo hi) (s : ℕ) :
    Dep k (fun w => rotF k s (F w)) (lo - s) (hi - s) := by
  intro w w' hw hw' n hag
  simp only [pz_rotF hk (hB w hw), pz_rotF hk (hB w' hw')]
  apply hF w w' hw hw' (n - s)
  intro t h1 h2
  have := hag (t - s) (by omega) (by omega)
  rwa [show n + (t - s) = n - s + t by ring] at this

theorem DepL_rot {k F e lo hi} (hk : 0 < k) (hB : Bd k F) (hF : DepL k F e lo hi) (s : ℕ) :
    DepL k (fun w => rotF k s (F w)) (e - s) (lo - s) (hi - s) := by
  intro w w' hw hw' n hag
  simp only [pz_rotF hk (hB w hw), pz_rotF hk (hB w' hw'), show n + (e - s) = n - s + e by ring]
  apply hF w w' hw hw' (n - s)
  intro t h1 h2
  have := hag (t - s) (by omega) (by omega)
  rwa [show n + (t - s) = n - s + t by ring] at this

theorem Dep_addk {k F lo hi} (hF : Dep k F lo hi) : Dep k F (lo + k) (hi + k) := by
  intro w w' hw hw' n hag
  apply hF w w' hw hw' n
  intro t h1 h2
  have := hag (t + k) (by omega) (by omega)
  rwa [show n + (t + k) = (n + t) + k by ring, pz_add_k, pz_add_k] at this

theorem Dep_step {k F lo hi} (hk : 0 < k) (hF : Dep k F lo hi) :
    Dep k (fun w => stepF k (F w)) lo (hi + 2) := by
  intro w w' hw hw' n hag
  simp only [pz_stepF hk]
  have a0 := hF w w' hw hw' n (fun t h1 h2 => hag t h1 (by omega))
  have a1 := hF w w' hw hw' (n + 1) (fun t h1 h2 => by
    have := hag (t + 1) (by omega) (by omega); rwa [show n + (t + 1) = n + 1 + t by ring] at this)
  have a2 := hF w w' hw hw' (n + 2) (fun t h1 h2 => by
    have := hag (t + 2) (by omega) (by omega); rwa [show n + (t + 2) = n + 2 + t by ring] at this)
  rw [a0, a1, a2]

theorem DepL_step {k F e lo hi} (hk : 0 < k) (hF : DepL k F e lo hi) (h1 : e + 1 ≤ lo) (h2 : e ≤ hi) :
    DepL k (fun w => stepF k (F w)) e (e + 1) (hi + 2) := by
  intro w w' hw hw' n hag
  simp only [pz_stepF hk]
  have a0 := hF w w' hw hw' n (fun t h1 h2 => hag t (by omega) (by omega))
  have a1 := hF w w' hw hw' (n + 1) (fun t h1 h2 => by
    have := hag (t + 1) (by omega) (by omega); rwa [show n + (t + 1) = n + 1 + t by ring] at this)
  have a2 := hF w w' hw hw' (n + 2) (fun t h1 h2 => by
    have := hag (t + 2) (by omega) (by omega); rwa [show n + (t + 2) = n + 2 + t by ring] at this)
  have b1 := hag (e + 1) le_rfl (by omega)
  have b2 := hag (e + 2) (by omega) (by omega)
  rw [show n + 1 + e = n + (e + 1) by ring, b1] at a1
  rw [show n + 2 + e = n + (e + 2) by ring, b2] at a2
  rw [xor_cancel_right a1, xor_cancel_right a2, Bool.xor_right_comm, a0, Bool.xor_right_comm]

/-! ### triangular injectivity and counting -/

theorem tri {k M L : ℕ} {e : ℤ} {S : ℕ → ℕ} (hS : DepL k S e (e + 1) (e + L)) (hLM : L ≤ M)
    (hMk : M ≤ k) {w w' : ℕ} (hw : w < 2 ^ k) (hw' : w' < 2 ^ k)
    (hcon : ∀ i : ℕ, M ≤ i → i < k → pz k (S w) i = pz k (S w') i)
    (hfree : ∀ i : ℕ, i < M → pz k w (i + e) = pz k w' (i + e)) : w = w' := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp at hw hw'; omega
  have key : ∀ d i : ℕ, k ≤ i + d → i < k → pz k w (i + e) = pz k w' (i + e) := by
    intro d
    induction d with
    | zero => intro i h1 h2; omega
    | succ d ih =>
      intro i h1 h2
      by_cases hd : k ≤ i + d
      · exact ih i hd h2
      by_cases hiM : i < M
      · exact hfree i hiM
      have hx := hS w w' hw hw' (i : ℤ) (fun t ht1 ht2 => by
        obtain ⟨s, rfl⟩ : ∃ s : ℕ, t = e + s := ⟨(t - e).toNat, by omega⟩
        by_cases hwrap : i + s < k
        · have := ih (i + s) (by omega) hwrap
          rw [show (i : ℤ) + (e + s) = ((i + s : ℕ) : ℤ) + e by push_cast; ring]; exact this
        · have := hfree (i + s - k) (by omega)
          rw [show ((i + s - k : ℕ) : ℤ) + e = (i : ℤ) + (e + s) - k by
            rw [Nat.cast_sub (by omega)]; push_cast; ring, pz_sub_k, pz_sub_k] at this
          exact this)
      rw [hcon i (by omega) h2] at hx
      exact xor_cancel_left hx
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < k
  · rw [← pz_lt k w j hj, ← pz_lt k w' j hj]
    have hi := toNat_lt hk ((j : ℤ) - e)
    have := key k _ (by omega) hi
    have hc : ((((j : ℤ) - e) % (k : ℤ)).toNat : ℤ) + e ≡ (j : ℤ) [ZMOD k] := by
      rw [toNat_cast hk]
      simpa using (Int.mod_modEq ((j : ℤ) - e) k).add_right e
    rwa [pz_modEq hc, pz_modEq hc] at this
  · rw [big_false hw (by omega), big_false hw' (by omega)]

theorem count_le_count (P Q : ℕ → Bool) (N : ℕ) (T : ℕ → ℕ)
    (hT : ∀ x, x < N → P x = true → T x < N ∧ Q (T x) = true)
    (hinj : ∀ x y, x < N → y < N → P x = true → P y = true → T x = T y → x = y) :
    ((List.range N).filter P).length ≤ ((List.range N).filter Q).length := by
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter P),
    ← List.toFinset_card_of_nodup (List.nodup_range.filter Q)]
  apply Finset.card_le_card_of_injOn T
  · intro x hx
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range] at hx ⊢
    exact hT x hx.1 hx.2
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range] at hx hy
    exact hinj x y hx.1 hy.1 hx.2 hy.2 hxy

theorem count_le_inj (P : ℕ → Bool) (N M : ℕ) (T : ℕ → ℕ)
    (hT : ∀ x, x < N → P x = true → T x < M)
    (hinj : ∀ x y, x < N → y < N → P x = true → P y = true → T x = T y → x = y) :
    ((List.range N).filter P).length ≤ M := by
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter P)]
  calc _ ≤ (Finset.range M).card := by
        apply Finset.card_le_card_of_injOn T
        · intro x hx
          simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range,
            Finset.mem_range] at hx ⊢
          exact hT x hx.1 hx.2
        · intro x hx y hy hxy
          simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range] at hx hy
          exact hinj x y hx.1 hy.1 hx.2 hy.2 hxy
    _ = M := Finset.card_range M

theorem count_eq_of_inj (Q : ℕ → Bool) (N : ℕ) (T : ℕ → ℕ) (hT : ∀ x, x < N → T x < N)
    (hinj : ∀ x y, x < N → y < N → T x = T y → x = y) :
    ((List.range N).filter (fun x => Q (T x))).length = ((List.range N).filter Q).length := by
  have h1 := count_le_count (fun x => Q (T x)) Q N T (fun x hx h => ⟨hT x hx, h⟩)
    (fun x y hx hy _ _ => hinj x y hx hy)
  have h2 := count_le_count (fun x => !Q (T x)) (fun x => !Q x) N T
    (fun x hx h => ⟨hT x hx, h⟩) (fun x y hx hy _ _ => hinj x y hx hy)
  have e1 := List.length_eq_length_filter_add (fun x => Q (T x)) (l := List.range N)
  have e2 := List.length_eq_length_filter_add Q (l := List.range N)
  simp only [List.length_range] at e1 e2
  omega

theorem count_lt (m N : ℕ) :
    ((List.range N).filter (fun t => decide (t < m))).length = min N m := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    by_cases h : N < m <;> simp [h] <;> omega

/-- exact count: a DepL triangular state with window `L ≤ m` leaves exactly `2^m` keys
with the top `k - m` bits zero. -/
theorem exact_count {k m L s : ℕ} {e : ℤ} (S : ℕ → ℕ) (hk : 0 < k)
    (hS : DepL k S e (e + 1) (e + L)) (hB : Bd k S) (hLm : L ≤ m) (hmk : m ≤ k)
    (hse : e = -(s : ℤ)) :
    ((List.range (2 ^ k)).filter (fun w => decide (S w < 2 ^ m))).length = 2 ^ m := by
  let T : ℕ → ℕ := fun w => ((S w >>> m) <<< m) ||| (rotF k s w % 2 ^ m)
  have hTb : ∀ w i, (T w).testBit i =
      ((decide (i ≥ m) && (S w).testBit i) || (decide (i < m) && (rotF k s w).testBit i)) := by
    intro w i
    simp only [T, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
      Nat.testBit_mod_two_pow]
    by_cases h : m ≤ i
    · simp [h, show m + (i - m) = i by omega]
    · simp [h, show i < m by omega]
  have hTlt : ∀ w, w < 2 ^ k → T w < 2 ^ k := fun w hw =>
    Nat.lt_pow_two_of_testBit _ (fun i hi => by
      rw [hTb, big_false (hB w hw) hi]; simp [show ¬ i < m by omega])
  have hiff : ∀ w, decide (S w < 2 ^ m) = decide (T w < 2 ^ m) := by
    intro w
    congr 1
    rw [lt_pow_iff_bits, lt_pow_iff_bits, eq_iff_iff]
    refine forall_congr' (fun i => imp_congr_right (fun hi => ?_))
    rw [hTb]; simp [hi, show ¬ i < m by omega]
  rw [List.filter_congr (fun w _ => hiff w),
    count_eq_of_inj (fun t => decide (t < 2 ^ m)) (2 ^ k) T hTlt, count_lt,
    min_eq_right (Nat.pow_le_pow_right (by norm_num) hmk)]
  intro w w' hw hw' hT
  apply tri hS hLm hmk hw hw'
  · intro i hi1 hi2
    rw [pz_lt _ _ _ hi2, pz_lt _ _ _ hi2]
    have := congrArg (fun x => x.testBit i) hT
    simp only [hTb] at this
    simpa [show i ≥ m from hi1, show ¬ i < m by omega] using this
  · intro i hi
    have := congrArg (fun x => x.testBit i) hT
    simp only [hTb] at this
    have h2 : (rotF k s w).testBit i = (rotF k s w').testBit i := by
      simpa [show ¬ i ≥ m by omega, hi] using this
    rw [← pz_lt k _ _ (by omega), ← pz_lt k _ _ (by omega), pz_rotF hk hw, pz_rotF hk hw'] at h2
    rwa [hse, ← sub_eq_add_neg]

/-- upper bound: with window `L ≤ M` and `m ≤ M ≤ k`, at most `2^M` keys have the top `k - m`
bits zero. -/
theorem upper_count {k m M L s : ℕ} {e : ℤ} (S : ℕ → ℕ) (hk : 0 < k)
    (hS : DepL k S e (e + 1) (e + L)) (hB : Bd k S) (hLM : L ≤ M) (hmM : m ≤ M) (hMk : M ≤ k)
    (hse : e = -(s : ℤ)) :
    ((List.range (2 ^ k)).filter (fun w => decide (S w < 2 ^ m))).length ≤ 2 ^ M := by
  apply count_le_inj _ _ _ (fun w => rotF k s w % 2 ^ M)
  · intro x _ _; exact Nat.mod_lt _ (by positivity)
  intro w w' hw hw' hPw hPw' hT
  simp only [decide_eq_true_eq] at hPw hPw'
  apply tri hS hLM hMk hw hw'
  · intro i hi1 hi2
    rw [pz_lt _ _ _ hi2, pz_lt _ _ _ hi2, big_false hPw (by omega), big_false hPw' (by omega)]
  · intro i hi
    have := congrArg (fun x => x.testBit i) hT
    simp only [Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and] at this
    rw [← pz_lt k _ _ (by omega), ← pz_lt k _ _ (by omega), pz_rotF hk hw, pz_rotF hk hw'] at this
    rwa [hse, ← sub_eq_add_neg]


/-! ### generic round: mix by rotations a and k-a, step, XOR rotated key and a constant -/

def rndG (k a : ℕ) (b c : ℕ → ℕ) (w prev j : ℕ) : ℕ :=
  stepF k (prev ^^^ rotF k a prev ^^^ rotF k (k - a) prev) ^^^ rotF k (b j) w ^^^ c (j + 1)

def cst (k j : ℕ) : ℕ := 3 ^ (k + j) % 2 ^ k

theorem cst_lt (k j : ℕ) : cst k j < 2 ^ k := Nat.mod_lt _ (by positivity)

theorem fold_succ {β : Type} (f : β → ℕ → β) (x : β) (n : ℕ) :
    (List.range (n + 1)).foldl f x = f ((List.range n).foldl f x) n := by
  rw [List.range_succ, List.foldl_append]; rfl

theorem Bd_rndG {k a : ℕ} (b c : ℕ → ℕ) (hc : ∀ j, c j < 2 ^ k) (F : ℕ → ℕ) (j : ℕ) :
    Bd k (fun w => rndG k a b c w (F w) j) := fun _ _ =>
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepF_lt _ _) (rotF_lt _ _ _)) (hc _)

theorem Dep_mixstep {k a : ℕ} (hk : 0 < k) (ha : a ≤ k) {F : ℕ → ℕ} {lo hi : ℤ}
    (hF : Dep k F lo hi) (hB : Bd k F) :
    Dep k (fun w => stepF k (F w ^^^ rotF k a (F w) ^^^ rotF k (k - a) (F w)))
      (lo - a) (hi + a + 2) := by
  have h1 : Dep k (fun w => rotF k a (F w)) (lo - a) (hi + a) :=
    Dep_mono (Dep_rot hk hB hF a) le_rfl (by omega)
  have h2 : Dep k (fun w => rotF k (k - a) (F w)) (lo - a) (hi + a) := by
    have := Dep_addk (Dep_rot hk hB hF (k - a))
    rw [Nat.cast_sub ha] at this
    exact Dep_mono this (by omega) (by omega)
  have h0 : Dep k F (lo - a) (hi + a) := Dep_mono hF (by omega) (by omega)
  exact Dep_step hk (Dep_xor (Dep_xor h0 h1) h2)

theorem Dep_rndG {k a : ℕ} (hk : 0 < k) (ha : a ≤ k) (b c : ℕ → ℕ) {F : ℕ → ℕ} {lo hi : ℤ}
    (hF : Dep k F lo hi) (hB : Bd k F) (j : ℕ) {lo' hi' : ℤ} (h1 : lo' ≤ lo - a)
    (h2 : hi + a + 2 ≤ hi') (h3 : lo' ≤ -((b j : ℕ) : ℤ)) (h4 : -((b j : ℕ) : ℤ) ≤ hi') :
    Dep k (fun w => rndG k a b c w (F w) j) lo' hi' :=
  Dep_xor (Dep_xor (Dep_mono (Dep_mixstep hk ha hF hB) h1 h2) (Dep_mono (Dep_key hk (b j)) h3 h4))
    (Dep_const k _ lo' hi')

theorem DepL_rndG_last {k a : ℕ} (hk : 0 < k) (ha : a ≤ k) (b c : ℕ → ℕ) {F : ℕ → ℕ}
    {lo hi : ℤ} (hF : Dep k F lo hi) (hB : Bd k F) (j : ℕ) {lo' hi' : ℤ} (h1 : lo' ≤ lo - a)
    (h2 : hi + a + 2 ≤ hi') :
    DepL k (fun w => rndG k a b c w (F w) j) (-((b j : ℕ) : ℤ)) lo' hi' :=
  DepL_xor (DepL_xor_left (Dep_mono (Dep_mixstep hk ha hF hB) h1 h2) (DepL_key hk (b j) lo' hi'))
    (Dep_const k _ lo' hi')

/-- windows of the keyed test after `n` rounds, as a function of the key. -/
theorem round_inv {k a s0 u : ℕ} (hk : 0 < k) (ha : a ≤ k) (hu : u < 2 ^ k) (b c : ℕ → ℕ)
    (hc : ∀ j, c j < 2 ^ k) (lo hi : ℕ → ℤ) (h0lo : lo 0 ≤ -(s0 : ℤ)) (h0hi : -(s0 : ℤ) ≤ hi 0)
    (hstep : ∀ n, lo (n + 1) ≤ lo n - a ∧ hi n + a + 2 ≤ hi (n + 1) ∧
      lo (n + 1) ≤ -((b n : ℕ) : ℤ) ∧ -((b n : ℕ) : ℤ) ≤ hi (n + 1)) (n : ℕ) :
    Dep k (fun w => (List.range n).foldl (rndG k a b c w) (rotF k s0 w ^^^ u)) (lo n) (hi n) ∧
      Bd k (fun w => (List.range n).foldl (rndG k a b c w) (rotF k s0 w ^^^ u)) := by
  induction n with
  | zero =>
    exact ⟨Dep_mono (Dep_xor (Dep_key hk s0) (Dep_const k u _ _)) h0lo h0hi,
      fun _ _ => Nat.xor_lt_two_pow (rotF_lt _ _ _) hu⟩
  | succ n ih =>
    obtain ⟨hD, hB⟩ := ih
    obtain ⟨s1, s2, s3, s4⟩ := hstep n
    simp only [fold_succ]
    exact ⟨Dep_rndG hk ha b c hD hB n s1 s2 s3 s4, Bd_rndG b c hc _ n⟩

/-- final-round structure: bit i of the state is key bit i - b(n) XOR a window function. -/
theorem final_DepL {k a s0 u : ℕ} (hk : 0 < k) (ha : a ≤ k) (hu : u < 2 ^ k) (b c : ℕ → ℕ)
    (hc : ∀ j, c j < 2 ^ k) (lo hi : ℕ → ℤ) (h0lo : lo 0 ≤ -(s0 : ℤ)) (h0hi : -(s0 : ℤ) ≤ hi 0)
    (hstep : ∀ n, lo (n + 1) ≤ lo n - a ∧ hi n + a + 2 ≤ hi (n + 1) ∧
      lo (n + 1) ≤ -((b n : ℕ) : ℤ) ∧ -((b n : ℕ) : ℤ) ≤ hi (n + 1)) (n : ℕ) {lo' hi' : ℤ}
    (h1 : lo' ≤ lo n - a) (h2 : hi n + a + 2 ≤ hi') :
    DepL k (fun w => (List.range (n + 1)).foldl (rndG k a b c w) (rotF k s0 w ^^^ u))
      (-((b n : ℕ) : ℤ)) lo' hi' ∧
      Bd k (fun w => (List.range (n + 1)).foldl (rndG k a b c w) (rotF k s0 w ^^^ u)) := by
  obtain ⟨hD, hB⟩ := round_inv hk ha hu b c hc lo hi h0lo h0hi hstep n
  simp only [fold_succ]
  exact ⟨DepL_rndG_last hk ha b c hD hB n h1 h2, Bd_rndG b c hc _ n⟩
theorem pz_rot1 {k : ℕ} (hk : 0 < k) : ∀ z, z < 2 ^ k → ∀ n, pz k (rotF k 1 z) n = pz k z (n + -1) :=
  fun z hz n => by rw [pz_rotF hk hz]; norm_num [sub_eq_add_neg]

theorem pz_rotkm1 {k : ℕ} (hk : 0 < k) :
    ∀ z, z < 2 ^ k → ∀ n, pz k (rotF k (k - 1) z) n = pz k z (n + 1) := fun z hz n => by
  rw [pz_rotF hk hz, Nat.cast_sub (by omega), Nat.cast_one,
    show n - ((k : ℤ) - 1) = n + 1 - k by ring, pz_sub_k]


/-! ### one-round propagation (mix by rotations 1 and k-1, then step) -/

def mixF (k x : ℕ) : ℕ := x ^^^ rotF k 1 x ^^^ rotF k (k - 1) x

def preF (k x : ℕ) : ℕ := stepF k (mixF k x)

theorem pz_mixF {k : ℕ} (hk : 0 < k) {x : ℕ} (hx : x < 2 ^ k) (n : ℤ) :
    pz k (mixF k x) n = xor (xor (pz k x n) (pz k x (n - 1))) (pz k x (n + 1)) := by
  unfold mixF
  rw [pz_xor, pz_xor, pz_rot1 hk x hx, pz_rotkm1 hk x hx, ← sub_eq_add_neg]

theorem pz_preF {k : ℕ} (hk : 0 < k) {x : ℕ} (hx : x < 2 ^ k) (n : ℤ) :
    pz k (preF k x) n =
      xor (xor (xor (pz k x (n - 1)) (pz k x n)) (pz k x (n + 1)))
        (!(xor (xor (pz k x n) (pz k x (n + 1))) (pz k x (n + 2))) &&
          xor (xor (pz k x (n + 1)) (pz k x (n + 2))) (pz k x (n + 3))) := by
  unfold preF
  rw [pz_stepF hk, pz_mixF hk hx, pz_mixF hk hx, pz_mixF hk hx,
    show n + 1 - 1 = n by ring, show n + 2 - 1 = n + 1 by ring, show n + 1 + 1 = n + 2 by ring,
    show n + 2 + 1 = n + 3 by ring]
  cases pz k x (n - 1) <;> cases pz k x n <;> cases pz k x (n + 1) <;> cases pz k x (n + 2) <;>
    cases pz k x (n + 3) <;> rfl

/-- propagation: bit `n` after one round only sees bits `n-1 .. n+3`. -/
theorem pre_agree {k : ℕ} (hk : 0 < k) {x x' : ℕ} (hx : x < 2 ^ k) (hx' : x' < 2 ^ k) (n : ℤ)
    (h : ∀ j : ℤ, -1 ≤ j → j ≤ 3 → pz k x (n + j) = pz k x' (n + j)) :
    pz k (preF k x) n = pz k (preF k x') n := by
  have h0 := h 0 (by norm_num) (by norm_num)
  have h1 := h 1 (by norm_num) (by norm_num)
  have h2 := h 2 (by norm_num) (by norm_num)
  have h3 := h 3 (by norm_num) (by norm_num)
  have hm := h (-1) (by norm_num) (by norm_num)
  rw [add_zero] at h0
  rw [← sub_eq_add_neg] at hm
  rw [pz_preF hk hx, pz_preF hk hx', h0, h1, h2, h3, hm]

/-- tight round: if bits `n-1 .. n+2` agree but bit `n` after a round differs, then the
three-bit parity at `n, n+1, n+2` is zero (the step's `!w(b+1) && w(b+2)` term fired). -/
theorem pre_tight {k : ℕ} (hk : 0 < k) {x x' : ℕ} (hx : x < 2 ^ k) (hx' : x' < 2 ^ k) (n : ℤ)
    (h : ∀ j : ℤ, -1 ≤ j → j ≤ 2 → pz k x (n + j) = pz k x' (n + j))
    (hne : pz k (preF k x) n ≠ pz k (preF k x') n) :
    xor (xor (pz k x n) (pz k x (n + 1))) (pz k x (n + 2)) = false := by
  have h0 := h 0 (by norm_num) (by norm_num)
  have h1 := h 1 (by norm_num) (by norm_num)
  have h2 := h 2 (by norm_num) (by norm_num)
  have hm := h (-1) (by norm_num) (by norm_num)
  rw [add_zero] at h0
  rw [← sub_eq_add_neg] at hm
  rw [pz_preF hk hx, pz_preF hk hx', h0, h1, h2, hm] at hne
  rw [h0, h1, h2]
  revert hne
  cases pz k x' (n - 1) <;> cases pz k x' n <;> cases pz k x' (n + 1) <;> cases pz k x' (n + 2) <;>
    cases pz k x (n + 3) <;> cases pz k x' (n + 3) <;> simp

/-! ### the keyed state, the two keys `w` and `w' = w XOR (rotated mask)` -/

def st (k u : ℕ) (cs : ℕ → ℕ) (w t : ℕ) : ℕ :=
  (List.range t).foldl (rndG k 1 (fun j => 2 * j) cs w) (rotF k 1 w ^^^ u)

theorem st_zero (k u : ℕ) (cs : ℕ → ℕ) (w : ℕ) : st k u cs w 0 = rotF k 1 w ^^^ u := rfl

theorem st_succ (k u : ℕ) (cs : ℕ → ℕ) (w t : ℕ) :
    st k u cs w (t + 1) = preF k (st k u cs w t) ^^^ rotF k (2 * t) w ^^^ cs (t + 1) := by
  unfold st; rw [fold_succ]; rfl

theorem st_lt {k u : ℕ} {cs : ℕ → ℕ} (hu : u < 2 ^ k) (hc : ∀ j, cs j < 2 ^ k) (w t : ℕ) :
    st k u cs w t < 2 ^ k := by
  induction t with
  | zero => exact Nat.xor_lt_two_pow (rotF_lt _ _ _) hu
  | succ t ih =>
    rw [st_succ]; exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepF_lt _ _) (rotF_lt _ _ _)) (hc _)

theorem pz_st_succ {k u : ℕ} {cs : ℕ → ℕ} (hk : 0 < k) {w : ℕ} (hw : w < 2 ^ k) (t : ℕ) (n : ℤ) :
    pz k (st k u cs w (t + 1)) n =
      xor (pz k (preF k (st k u cs w t)) n) (xor (pz k w (n - ((2 * t : ℕ) : ℤ))) (pz k (cs (t + 1)) n)) := by
  rw [st_succ, pz_xor, pz_xor, pz_rotF hk hw, Bool.xor_assoc]

theorem maskfree {k q x : ℕ} (hx : x < 2 ^ q) (m c : ℤ) (h1 : (q : ℤ) ≤ m + c * k)
    (h2 : m + c * k < k) : pz k x m = false := by
  have e1 : pz k x m = pz k x (m + c * k) := pz_modEq (by
    show m % (k : ℤ) = (m + c * k) % (k : ℤ); simp)
  obtain ⟨a, ha⟩ : ∃ a : ℕ, m + c * k = a := ⟨(m + c * k).toNat, by omega⟩
  rw [e1, ha, pz_nat, Nat.mod_eq_of_lt (by omega)]
  exact big_false hx (by omega)

/-- a difference in bit `n` of the round-`t` pre-injection word (cone top `i+3r-3t`, depth `j`). -/
def Dl (k u : ℕ) (cs : ℕ → ℕ) (w w' i r t j : ℕ) : Prop :=
  pz k (preF k (st k u cs w' (t - 1))) ((i : ℤ) + 3 * r - 3 * t - j) ≠
    pz k (preF k (st k u cs w (t - 1))) ((i : ℤ) + 3 * r - 3 * t - j)

theorem core14 (k r e q : ℕ) (cs : ℕ → ℕ) (hc : ∀ j, cs j < 2 ^ k) (u i : ℕ)
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r) (hu : u < 2 ^ k) (hi : i < k)
    (w m : ℕ) (hw : w < 2 ^ k) (hm : m < 2 ^ q)
    (hne : (preF k (st k u cs w (r - 1))).testBit i ≠
      (preF k (st k u cs (w ^^^ rotF k (i + 3 * r + k - e - q) m) (r - 1))).testBit i) :
    ∃ d : ℕ → ℕ,
      (∀ t, e + q + 3 ≤ t → t ≤ r → d t < e + q ∧ d t ≤ 4 * (r - t)) ∧
      (∀ t, e + q + 3 < t → t ≤ r → d t ≤ d (t - 1)) ∧
      ∀ t, e + q + 3 < t → t ≤ r - e →
        (∀ s, e + q + 3 ≤ s → s < t → s + d s < t + d t) →
        xor (xor ((st k u cs w (t - 1)).testBit ((i + 3 * (r - t) + k - d t) % k))
          ((st k u cs w (t - 1)).testBit ((i + 3 * (r - t) + k - d t + 1) % k)))
          ((st k u cs w (t - 1)).testBit ((i + 3 * (r - t) + k - d t + 2) % k)) = false := by
  classical
  have hk0 : 0 < k := by omega
  set S := i + 3 * r + k - e - q with hSdef
  set w' := w ^^^ rotF k S m with hw'def
  have hw' : w' < 2 ^ k := Nat.xor_lt_two_pow hw (rotF_lt _ _ _)
  have hqk : q ≤ k := by omega
  have hmk : m < 2 ^ k := lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) hqk)
  have mfree : ∀ n : ℤ, (q : ℤ) ≤ n - S + 2 * k → n - S + 2 * k < k → pz k w' n = pz k w n := by
    intro n h1 h2
    rw [hw'def, pz_xor, pz_rotF hk0 hmk, maskfree hm (n - S) 2 h1 h2, Bool.xor_false]
  have stl : ∀ x t, st k u cs x t < 2 ^ k := fun x t => st_lt hu hc x t
  have inj : ∀ t : ℕ, ∀ n : ℤ, (q : ℤ) ≤ n - ((2 * t : ℕ) : ℤ) - S + 2 * k →
      n - ((2 * t : ℕ) : ℤ) - S + 2 * k < k →
      (pz k (st k u cs w' (t + 1)) n = pz k (st k u cs w (t + 1)) n ↔
        pz k (preF k (st k u cs w' t)) n = pz k (preF k (st k u cs w t)) n) := by
    intro t n h1 h2
    rw [pz_st_succ hk0 hw', pz_st_succ hk0 hw, mfree _ h1 h2]
    cases pz k (preF k (st k u cs w' t)) n <;> cases pz k (preF k (st k u cs w t)) n <;> simp
  -- low region: no difference at depth `≥ e + q` below the cone top
  have low : ∀ t, t + 1 ≤ r → ∀ n : ℤ, (i : ℤ) - r + t ≤ n → n ≤ (i : ℤ) + 3 * r - 3 * t - (e + q) →
      pz k (st k u cs w' t) n = pz k (st k u cs w t) n := by
    intro t
    induction t with
    | zero =>
      intro _ n h1 h2
      simp only [st_zero, pz_xor, pz_rotF hk0 hw', pz_rotF hk0 hw]
      rw [mfree _ (by omega) (by omega)]
    | succ t ih =>
      intro ht n h1 h2
      rw [inj t n (by omega) (by omega)]
      apply pre_agree hk0 (stl _ _) (stl _ _) n
      intro j hj1 hj2
      exact ih (by omega) _ (by omega) (by omega)
  have prelow : ∀ t, 1 ≤ t → t ≤ r → ∀ j, e + q ≤ j → j ≤ 4 * (r - t) → ¬ Dl k u cs w w' i r t j := by
    intro t ht1 ht2 j hj1 hj2 hD
    apply hD
    apply pre_agree hk0 (stl _ _) (stl _ _)
    intro j' hj1' hj2'
    exact low (t - 1) (by omega) _ (by omega) (by omega)
  -- window transfer: past the early injections, a state difference in the cone is a pre-word difference
  have wt : ∀ t, e + q + 3 ≤ t → t + 1 ≤ r → ∀ j, j ≤ 4 * (r - t) →
      pz k (st k u cs w' t) ((i : ℤ) + 3 * r - 3 * t - j) ≠ pz k (st k u cs w t) ((i : ℤ) + 3 * r - 3 * t - j) →
      Dl k u cs w w' i r t j := by
    intro t ht1 ht2 j hj hd
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    unfold Dl
    rw [Nat.add_sub_cancel]
    intro heq
    exact hd ((inj s _ (by omega) (by omega)).2 heq)
  -- one round back: a pre-word difference at depth j comes from a state difference at depth j .. j+4
  have back : ∀ t, 1 ≤ t → ∀ j, Dl k u cs w w' i r (t + 1) j → ∃ J : ℕ, j ≤ J ∧ J ≤ j + 4 ∧
      pz k (st k u cs w' t) ((i : ℤ) + 3 * r - 3 * t - J) ≠ pz k (st k u cs w t) ((i : ℤ) + 3 * r - 3 * t - J) := by
    intro t _ j hD
    unfold Dl at hD
    rw [Nat.add_sub_cancel] at hD
    have : ∃ j' : ℤ, -1 ≤ j' ∧ j' ≤ 3 ∧
        pz k (st k u cs w' t) ((i : ℤ) + 3 * r - 3 * ((t + 1 : ℕ) : ℤ) - j + j') ≠
          pz k (st k u cs w t) ((i : ℤ) + 3 * r - 3 * ((t + 1 : ℕ) : ℤ) - j + j') := by
      by_contra hno
      push_neg at hno
      exact hD (pre_agree hk0 (stl _ _) (stl _ _) _ hno)
    obtain ⟨j', h1, h2, h3⟩ := this
    obtain ⟨J, hJ⟩ : ∃ J : ℕ, (J : ℤ) = j + 3 - j' := ⟨((j : ℤ) + 3 - j').toNat, by omega⟩
    refine ⟨J, by omega, by omega, ?_⟩
    rwa [show (i : ℤ) + 3 * r - 3 * t - J = (i : ℤ) + 3 * r - 3 * ((t + 1 : ℕ) : ℤ) - j + j' by
      push_cast; omega]
  let d : ℕ → ℕ := fun t => Nat.findGreatest (Dl k u cs w w' i r t) (4 * (r - t))
  have dle : ∀ t, d t ≤ 4 * (r - t) := fun t => Nat.findGreatest_le _
  have dlt : ∀ t, 1 ≤ t → t ≤ r → d t < e + q := by
    intro t h1 h2
    by_contra hge
    push_neg at hge
    exact prelow t h1 h2 (d t) hge (dle t) (Nat.findGreatest_of_ne_zero rfl (by omega))
  -- nonempty cone differences from the changed bit backwards
  have ne : ∀ a t, t + a = r → e + q + 3 ≤ t → ∃ j, j ≤ 4 * (r - t) ∧ Dl k u cs w w' i r t j := by
    intro a
    induction a with
    | zero =>
      intro t ht _
      refine ⟨0, by omega, ?_⟩
      have htr : t = r := by omega
      subst htr
      unfold Dl
      rw [show (i : ℤ) + 3 * t - 3 * t - ((0 : ℕ) : ℤ) = ((i : ℕ) : ℤ) by push_cast; ring,
        pz_lt _ _ _ hi, pz_lt _ _ _ hi]
      exact fun h => hne h.symm
    | succ a ih =>
      intro t ht hcut
      obtain ⟨j, hj, hD⟩ := ih (t + 1) (by omega) (by omega)
      obtain ⟨J, hJ1, hJ2, hJ3⟩ := back t (by omega) j hD
      exact ⟨J, by omega, wt t hcut (by omega) J (by omega) hJ3⟩
  refine ⟨d, fun t h1 h2 => ⟨dlt t (by omega) h2, dle t⟩, ?_, ?_⟩
  · intro t h1 h2
    by_contra hlt
    push_neg at hlt
    have hD : Dl k u cs w w' i r t (d t) := Nat.findGreatest_of_ne_zero rfl (by omega)
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    obtain ⟨J, hJ1, hJ2, hJ3⟩ := back s (by omega) (d (s + 1)) hD
    have hW := wt s (by omega) (by omega) J (by have := dle (s + 1); omega) hJ3
    exact Nat.findGreatest_is_greatest (show d s < J by simp only [Nat.add_sub_cancel] at hlt; omega)
      (by have := dle (s + 1); omega) hW
  · intro t h1 h2 hrec
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hs := hrec s (by omega) (by omega)
    have hdec : d (s + 1) ≤ d s := by
      by_contra hlt
      push_neg at hlt
      have hD : Dl k u cs w w' i r (s + 1) (d (s + 1)) := Nat.findGreatest_of_ne_zero rfl (by omega)
      obtain ⟨J, hJ1, hJ2, hJ3⟩ := back s (by omega) (d (s + 1)) hD
      have hW := wt s (by omega) (by omega) J (by have := dle (s + 1); omega) hJ3
      exact Nat.findGreatest_is_greatest (show d s < J by omega) (by have := dle (s + 1); omega) hW
    have heqd : d s = d (s + 1) := by omega
    obtain ⟨j0, hj0, hD0⟩ := ne (r - (s + 1)) (s + 1) (by omega) (by omega)
    have hD : Dl k u cs w w' i r (s + 1) (d (s + 1)) := Nat.findGreatest_spec hj0 hD0
    unfold Dl at hD
    rw [Nat.add_sub_cancel] at hD
    set D := d (s + 1) with hDdef
    set n : ℤ := (i : ℤ) + 3 * r - 3 * ((s + 1 : ℕ) : ℤ) - D with hn
    have hag : ∀ j' : ℤ, -1 ≤ j' → j' ≤ 2 →
        pz k (st k u cs w s) (n + j') = pz k (st k u cs w' s) (n + j') := by
      intro j' h1' h2'
      by_contra hd
      obtain ⟨J, hJ⟩ : ∃ J : ℕ, (J : ℤ) = D + 3 - j' := ⟨((D : ℤ) + 3 - j').toNat, by omega⟩
      have hd' : pz k (st k u cs w' s) ((i : ℤ) + 3 * r - 3 * s - J) ≠
          pz k (st k u cs w s) ((i : ℤ) + 3 * r - 3 * s - J) := by
        rw [show (i : ℤ) + 3 * r - 3 * s - J = n + j' by rw [hn]; push_cast; omega]
        exact fun h => hd h.symm
      have hW := wt s (by omega) (by omega) J (by have := dle (s + 1); omega) hd'
      exact Nat.findGreatest_is_greatest (show d s < J by omega) (by have := dle (s + 1); omega) hW
    have tight := pre_tight hk0 (stl w s) (stl w' s) n hag (fun h => hD h.symm)
    have conv : ∀ (a : ℕ) (c : ℤ), (a : ℤ) = n + c + k →
        (st k u cs w s).testBit (a % k) = pz k (st k u cs w s) (n + c) := by
      intro a c hac
      rw [← pz_nat, hac, pz_add_k]
    have hD4 := dle (s + 1)
    rw [conv _ 0 (by rw [hn]; push_cast; omega), conv _ 1 (by rw [hn]; push_cast; omega),
      conv _ 2 (by rw [hn]; push_cast; omega), add_zero]
    exact tight

/-! ### halving: conditions with flips that keep the earlier conditions and toggle the current one -/

theorem halve_one {α : Type} [DecidableEq α] (s : Finset α) (p : α → Bool) (F : α → α)
    (hinv : ∀ x, F (F x) = x) (hs : ∀ x, x ∈ s → F x ∈ s) (hp : ∀ x, p (F x) = !p x) (b : Bool) :
    2 * (s.filter (fun x => p x = b)).card = s.card := by
  have e1 : (s.filter (fun x => p x = b)).card = (s.filter (fun x => ¬ p x = b)).card := by
    apply Finset.card_nbij' F F
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx ⊢
      refine ⟨hs x hx.1, ?_⟩
      rw [hp, hx.2]; cases b <;> simp
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx ⊢
      refine ⟨hs x hx.1, ?_⟩
      rw [hp]; revert hx; cases b <;> cases p x <;> simp
    · intro x _; exact hinv x
    · intro x _; exact hinv x
  have e2 := Finset.card_filter_add_card_filter_not (s := s) (fun x => p x = b)
  omega

theorem halving {α : Type} [Fintype α] [DecidableEq α] (N : ℕ) (C : ℕ → α → Bool) (σ : ℕ → Bool)
    (F : ℕ → α → α) (hinv : ∀ j, j < N → ∀ x, F j (F j x) = x)
    (hkeep : ∀ j, j < N → ∀ j', j' < j → ∀ x, C j' (F j x) = C j' x)
    (hflip : ∀ j, j < N → ∀ x, C j (F j x) = !C j x) :
    ∀ M, M ≤ N → ((Finset.univ : Finset α).filter (fun x => ∀ j, j < M → C j x = σ j)).card * 2 ^ M =
      Fintype.card α := by
  intro M
  induction M with
  | zero =>
    intro _
    simp
  | succ M ih =>
    intro hM
    have h1 := ih (by omega)
    set s := (Finset.univ : Finset α).filter (fun x => ∀ j, j < M → C j x = σ j) with hsdef
    have hsplit : (Finset.univ : Finset α).filter (fun x => ∀ j, j < M + 1 → C j x = σ j) =
        s.filter (fun x => C M x = σ M) := by
      ext x
      simp only [hsdef, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; exact ⟨fun j hj => h j (by omega), h M (by omega)⟩
      · intro h j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · exact h.1 j hj
        · rw [hj]; exact h.2
    have h2 := halve_one s (C M) (F M) (hinv M (by omega))
      (fun x hx => by
        simp only [hsdef, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        intro j hj; rw [hkeep M (by omega) j hj]; exact hx j hj)
      (hflip M (by omega)) (σ M)
    rw [hsplit, pow_succ, ← h1, ← h2]
    ring

/-! ### one-bit flips -/

def flipK (k : ℕ) (l : ℤ) (w : ℕ) : ℕ := w ^^^ rotF k ((l % (k : ℤ)).toNat) 1

theorem flipK_lt {k : ℕ} (hk : 0 < k) (l : ℤ) {w : ℕ} (hw : w < 2 ^ k) : flipK k l w < 2 ^ k :=
  Nat.xor_lt_two_pow hw (rotF_lt _ _ _)

theorem flipK_flipK (k : ℕ) (l : ℤ) (w : ℕ) : flipK k l (flipK k l w) = w := by
  unfold flipK; rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem pz_flipK {k : ℕ} (hk : 0 < k) (l : ℤ) (w : ℕ) (m : ℤ) :
    pz k (flipK k l w) m = xor (pz k w m) (pz k 1 (m - l)) := by
  have h1 : (1 : ℕ) < 2 ^ k := Nat.one_lt_two_pow (by omega)
  unfold flipK
  rw [pz_xor, pz_rotF hk h1]
  congr 1
  apply pz_modEq
  rw [toNat_cast hk]
  exact ((Int.mod_modEq l k).neg.add_left m)

theorem pz_one_zero (k : ℕ) (hk : 0 < k) : pz k 1 0 = true := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl, pz_nat, Nat.zero_mod]; rfl

theorem pz_flipK_off {k : ℕ} (hk : 0 < k) (l : ℤ) (w : ℕ) (m : ℤ) (h1 : 1 ≤ m - l) (h2 : m - l < k) :
    pz k (flipK k l w) m = pz k w m := by
  have h1' : (1 : ℕ) < 2 ^ 1 := by norm_num
  rw [pz_flipK hk, maskfree h1' (m - l) 0 (by simpa using h1) (by simpa using h2), Bool.xor_false]

theorem pz_flipK_on {k : ℕ} (hk : 0 < k) (l : ℤ) (w : ℕ) :
    pz k (flipK k l w) l = !pz k w l := by
  rw [pz_flipK hk, sub_self, pz_one_zero k hk]; cases pz k w l <;> rfl

/-! ### the state after `n+1` rounds as a function of the key -/

theorem st_DepL {k u : ℕ} {cs : ℕ → ℕ} (hk : 0 < k) (hu : u < 2 ^ k) (hc : ∀ j, cs j < 2 ^ k)
    (n : ℕ) (hn : 3 ≤ n) :
    DepL k (fun w => st k u cs w (n + 1)) (-((2 * n : ℕ) : ℤ)) (-2 * (n : ℤ) + 1) (3 * (n : ℤ) + 2) := by
  have := (final_DepL (k := k) (a := 1) (s0 := 1) (u := u) hk (by omega) hu (fun j => 2 * j) cs hc
    (fun n => min (-(n : ℤ) - 1) (-2 * (n : ℤ) + 2)) (fun n => 3 * (n : ℤ) - 1)
    (by simp) (by simp)
    (fun n => by push_cast; refine ⟨by omega, by omega, by omega, by omega⟩) n
    (lo' := -2 * (n : ℤ) + 1) (hi' := 3 * (n : ℤ) + 2) (by push_cast; omega) (by push_cast; omega)).1
  exact this

/-! ### integer-indexed words: the lifted row rule -/

def mixZ (w : ℤ → Bool) (z : ℤ) : Bool := xor (xor (w z) (w (z - 1))) (w (z + 1))

def befZ (w : ℤ → Bool) (z : ℤ) : Bool := xor (mixZ w z) (!(mixZ w (z + 1)) && mixZ w (z + 2))

def stZ (pub : ℕ → ℤ → Bool) (start : ℤ → Bool) (n : ℕ) : ℤ → Bool :=
  (List.range n).foldl (fun (prev : ℤ → Bool) (tick : ℕ) (z : ℤ) =>
    xor (xor (befZ prev z) (start (z + 1 - 2 * (tick : ℤ)))) (pub (tick + 1) z)) start

theorem stZ_zero (pub : ℕ → ℤ → Bool) (s : ℤ → Bool) : stZ pub s 0 = s := rfl

theorem stZ_succ (pub : ℕ → ℤ → Bool) (s : ℤ → Bool) (t : ℕ) (z : ℤ) :
    stZ pub s (t + 1) z = xor (xor (befZ (stZ pub s t) z) (s (z + 1 - 2 * (t : ℤ)))) (pub (t + 1) z) := by
  unfold stZ; rw [List.range_succ, List.foldl_append]; rfl

theorem befZ_eq (x : ℤ → Bool) (n : ℤ) : befZ x n =
    xor (xor (xor (x (n - 1)) (x n)) (x (n + 1)))
      (!(xor (xor (x n) (x (n + 1))) (x (n + 2))) && xor (xor (x (n + 1)) (x (n + 2))) (x (n + 3))) := by
  unfold befZ mixZ
  rw [show n + 1 - 1 = n by ring, show n + 2 - 1 = n + 1 by ring, show n + 1 + 1 = n + 2 by ring,
    show n + 2 + 1 = n + 3 by ring]
  cases x (n - 1) <;> cases x n <;> cases x (n + 1) <;> cases x (n + 2) <;> cases x (n + 3) <;> rfl

theorem befZ_agree {x x' : ℤ → Bool} (n : ℤ)
    (h : ∀ j : ℤ, -1 ≤ j → j ≤ 3 → x (n + j) = x' (n + j)) : befZ x n = befZ x' n := by
  have h0 := h 0 (by norm_num) (by norm_num)
  have h1 := h 1 (by norm_num) (by norm_num)
  have h2 := h 2 (by norm_num) (by norm_num)
  have h3 := h 3 (by norm_num) (by norm_num)
  have hm := h (-1) (by norm_num) (by norm_num)
  rw [add_zero] at h0
  rw [← sub_eq_add_neg] at hm
  rw [befZ_eq, befZ_eq, h0, h1, h2, h3, hm]

theorem befZ_tight {x x' : ℤ → Bool} (n : ℤ)
    (h : ∀ j : ℤ, -1 ≤ j → j ≤ 2 → x (n + j) = x' (n + j)) (hne : befZ x n ≠ befZ x' n) :
    xor (xor (x n) (x (n + 1))) (x (n + 2)) = false := by
  have h0 := h 0 (by norm_num) (by norm_num)
  have h1 := h 1 (by norm_num) (by norm_num)
  have h2 := h 2 (by norm_num) (by norm_num)
  have hm := h (-1) (by norm_num) (by norm_num)
  rw [add_zero] at h0
  rw [← sub_eq_add_neg] at hm
  rw [befZ_eq, befZ_eq, h0, h1, h2, hm] at hne
  rw [h0, h1, h2]
  revert hne
  cases x' (n - 1) <;> cases x' n <;> cases x' (n + 1) <;> cases x' (n + 2) <;>
    cases x (n + 3) <;> cases x' (n + 3) <;> simp

/-- a pre-injection difference at round `t`, depth `j` below the cone top `P - 3t`. -/
def DZ (pub : ℕ → ℤ → Bool) (base other : ℤ → Bool) (P : ℤ) (t j : ℕ) : Prop :=
  befZ (stZ pub other (t - 1)) (P - 3 * (t : ℤ) - (j : ℤ)) ≠
    befZ (stZ pub base (t - 1)) (P - 3 * (t : ℤ) - (j : ℤ))

def HZ (pub : ℕ → ℤ → Bool) (base other : ℤ → Bool) (P : ℤ) (r h t : ℕ) : Prop :=
  1 ≤ t ∧ t ≤ r ∧ t ≤ h ∧ h - t ≤ 4 * (r - t) ∧ DZ pub base other P t (h - t)

theorem core68 (r D : ℕ) (i P : ℤ) (hP : P = i + 3 * (r : ℤ)) (h5 : 5 + D ≤ r) (base other : ℤ → Bool) (pub : ℕ → ℤ → Bool)
    (hag : ∀ z < P - (D : ℤ), base z = other z)
    (hne : befZ (stZ pub base (r - 1)) i ≠ befZ (stZ pub other (r - 1)) i) :
    ∃ times : Fin (r - (4 + D)) → ℕ, StrictMono times ∧
      ∀ j : Fin (r - (4 + D)),
        5 + j.val ≤ times j ∧ times j ≤ 5 + D + j.val ∧ times j ≤ r ∧
        5 + D + j.val - times j ≤ 4 * (r - times j) ∧
        xor (xor (stZ pub base (times j - 1) (P - 3 * (times j : ℤ) - ((5 + D + j.val - times j : ℕ) : ℤ)))
          (stZ pub base (times j - 1) (P - 3 * (times j : ℤ) - ((5 + D + j.val - times j : ℕ) : ℤ) + 1)))
          (stZ pub base (times j - 1) (P - 3 * (times j : ℤ) - ((5 + D + j.val - times j : ℕ) : ℤ) + 2))
          = false := by
  classical
  -- low region: no difference at depth beyond D
  have low : ∀ t : ℕ, ∀ z : ℤ, z < P - 3 * (t : ℤ) - D → stZ pub other t z = stZ pub base t z := by
    intro t
    induction t with
    | zero => intro z hz; exact (hag z (by push_cast at hz; omega)).symm
    | succ t ih =>
      intro z hz
      rw [stZ_succ, stZ_succ, hag (z + 1 - 2 * (t : ℤ)) (by push_cast at hz; omega)]
      rw [befZ_agree z (fun j h1 h2 => ih _ (by push_cast at hz; omega))]
  have prelow : ∀ t, 1 ≤ t → ∀ j, D + 1 ≤ j → ¬ DZ pub base other P t j := by
    intro t ht j hj hD
    apply hD
    apply befZ_agree
    intro j' h1 h2
    exact low (t - 1) _ (by push_cast [Nat.cast_sub ht]; omega)
  have wt : ∀ t, 1 ≤ t → ∀ j, D ≤ t + j →
      stZ pub other t (P - 3 * (t : ℤ) - j) ≠ stZ pub base t (P - 3 * (t : ℤ) - j) →
      DZ pub base other P t j := by
    intro t ht j hlev hd
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    unfold DZ
    rw [Nat.add_sub_cancel]
    intro heq
    apply hd
    rw [stZ_succ, stZ_succ, heq, hag _ (by push_cast; omega)]
  have back : ∀ t j, DZ pub base other P (t + 1) j → ∃ J : ℕ, j ≤ J ∧ J ≤ j + 4 ∧
      stZ pub other t (P - 3 * (t : ℤ) - J) ≠ stZ pub base t (P - 3 * (t : ℤ) - J) := by
    intro t j hD
    unfold DZ at hD
    rw [Nat.add_sub_cancel] at hD
    have : ∃ j' : ℤ, -1 ≤ j' ∧ j' ≤ 3 ∧
        stZ pub other t (P - 3 * ((t + 1 : ℕ) : ℤ) - j + j') ≠
          stZ pub base t (P - 3 * ((t + 1 : ℕ) : ℤ) - j + j') := by
      by_contra hno
      push_neg at hno
      exact hD (befZ_agree _ hno)
    obtain ⟨j', h1, h2, h3⟩ := this
    obtain ⟨J, hJ⟩ : ∃ J : ℕ, (J : ℤ) = j + 3 - j' := ⟨((j : ℤ) + 3 - j').toNat, by omega⟩
    refine ⟨J, by omega, by omega, ?_⟩
    rwa [show P - 3 * (t : ℤ) - J = P - 3 * ((t + 1 : ℕ) : ℤ) - j + j' by push_cast; omega]
  have stdiff : ∀ t J, D + 1 ≤ t + J →
      stZ pub other t (P - 3 * (t : ℤ) - J) ≠ stZ pub base t (P - 3 * (t : ℤ) - J) →
      1 ≤ t ∧ DZ pub base other P t J := by
    intro t J hlev hd
    by_cases ht0 : t = 0
    · subst ht0
      exact absurd (low 0 _ (by push_cast; omega)) hd
    · exact ⟨by omega, wt t (by omega) J (by omega) hd⟩
  have desc : ∀ h, D + 1 ≤ h → ∀ s J, 1 ≤ s → s ≤ r → J ≤ 4 * (r - s) → DZ pub base other P s J →
      h ≤ s + J → ∃ t, t ≤ s ∧ (h < s + J → t < s) ∧ HZ pub base other P r h t := by
    intro h hh s
    induction s with
    | zero => intro J h1; omega
    | succ s ih =>
      intro J h1 h2 h3 hD hle
      by_cases heq : h = s + 1 + J
      · refine ⟨s + 1, le_rfl, fun h' => by omega, by omega, h2, by omega, by omega, ?_⟩
        rwa [show h - (s + 1) = J by omega]
      · obtain ⟨J', hJ1, hJ2, hJ3⟩ := back s J hD
        have hJ'r : J' ≤ 4 * (r - s) := by omega
        obtain ⟨hs1, hD'⟩ := stdiff s J' (by omega) hJ3
        obtain ⟨t, ht1, -, ht3⟩ := ih J' hs1 (by omega) hJ'r hD' (by omega)
        exact ⟨t, by omega, fun _ => by omega, ht3⟩
  have hr0 : DZ pub base other P r 0 := by
    unfold DZ
    rw [show P - 3 * (r : ℤ) - ((0 : ℕ) : ℤ) = i by rw [hP]; push_cast; ring]
    exact fun h => hne h.symm
  have hex : ∀ h, D + 1 ≤ h → h ≤ r → ∃ t, HZ pub base other P r h t := by
    intro h h1 h2
    obtain ⟨t, -, -, ht⟩ := desc h h1 r 0 (by omega) le_rfl (by omega) hr0 (by omega)
    exact ⟨t, ht⟩
  let tau : ℕ → ℕ := fun h => if hh : D + 1 ≤ h ∧ h ≤ r then Nat.find (hex h hh.1 hh.2) else 0
  have tau_hit : ∀ h, D + 1 ≤ h → h ≤ r → HZ pub base other P r h (tau h) := by
    intro h h1 h2
    simp only [tau, dif_pos (And.intro h1 h2)]
    exact Nat.find_spec (hex h h1 h2)
  have tau_min : ∀ h, D + 1 ≤ h → h ≤ r → ∀ t, HZ pub base other P r h t → tau h ≤ t := by
    intro h h1 h2 t ht
    simp only [tau, dif_pos (And.intro h1 h2)]
    exact Nat.find_min' _ ht
  have tau_mono : ∀ h1 h2, D + 1 ≤ h1 → h1 < h2 → h2 ≤ r → tau h1 < tau h2 := by
    intro h1 h2 a1 a2 a3
    obtain ⟨b1, b2, b3, b4, b5⟩ := tau_hit h2 (by omega) a3
    obtain ⟨t, -, ht2, ht3⟩ := desc h1 a1 (tau h2) (h2 - tau h2) b1 b2 b4 b5 (by omega)
    have := tau_min h1 a1 (by omega) t ht3
    have := ht2 (by omega)
    omega
  have guard : ∀ h, D + 5 ≤ h → h ≤ r →
      xor (xor (stZ pub base (tau h - 1) (P - 3 * (tau h : ℤ) - ((h - tau h : ℕ) : ℤ)))
        (stZ pub base (tau h - 1) (P - 3 * (tau h : ℤ) - ((h - tau h : ℕ) : ℤ) + 1)))
        (stZ pub base (tau h - 1) (P - 3 * (tau h : ℤ) - ((h - tau h : ℕ) : ℤ) + 2)) = false := by
    intro h h1 h2
    obtain ⟨b1, b2, b3, b4, b5⟩ := tau_hit h (by omega) h2
    set t := tau h with htdef
    obtain ⟨s, hs⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [hs, Nat.add_sub_cancel]
    have hD := b5
    rw [hs] at hD
    unfold DZ at hD
    rw [Nat.add_sub_cancel] at hD
    set g := h - (s + 1) with hg
    set n : ℤ := P - 3 * ((s + 1 : ℕ) : ℤ) - (g : ℕ) with hn
    have hagr : ∀ j' : ℤ, -1 ≤ j' → j' ≤ 2 →
        stZ pub base s (n + j') = stZ pub other s (n + j') := by
      intro j' h1' h2'
      by_contra hd
      obtain ⟨J, hJ⟩ : ∃ J : ℕ, (J : ℤ) = g + 3 - j' := ⟨((g : ℤ) + 3 - j').toNat, by omega⟩
      have hd' : stZ pub other s (P - 3 * (s : ℤ) - J) ≠ stZ pub base s (P - 3 * (s : ℤ) - J) := by
        rw [show P - 3 * (s : ℤ) - J = n + j' by rw [hn]; push_cast; omega]
        exact fun h => hd h.symm
      have hJr : J ≤ 4 * (r - s) := by omega
      obtain ⟨hs1, hD'⟩ := stdiff s J (by omega) hd'
      obtain ⟨t', ht1, ht2, ht3⟩ := desc h (by omega) s J hs1 (by omega) hJr hD' (by omega)
      have := tau_min h (by omega) h2 t' ht3
      omega
    exact befZ_tight n hagr (fun h => hD h.symm)
  refine ⟨fun j => tau (5 + D + j.val), ?_, ?_⟩
  · intro a b hab
    exact tau_mono _ _ (by omega) (by simp only [Fin.lt_def] at hab; omega) (by have := b.isLt; omega)
  · intro j
    beta_reduce
    have hj := j.isLt
    set h := 5 + D + j.val with hh
    obtain ⟨b1, b2, b3, b4, b5⟩ := tau_hit h (by omega) (by omega)
    have hgE : h - tau h < D + 1 := by
      by_contra hge
      exact prelow (tau h) b1 (h - tau h) (by omega) b5
    exact ⟨by omega, b3, b2, b4, guard h (by omega) (by omega)⟩

/-! ### integer-line runs from a periodic starting word: windows, leads, pivot flips -/

def loZ (s : ℕ) : ℤ := if s ≤ 3 then -(s : ℤ) else -2 * (s : ℤ) + 3

theorem loZ_succ (s : ℕ) : loZ (s + 1) ≤ loZ s - 1 ∧ loZ (s + 1) ≤ 1 - 2 * (s : ℤ) := by
  unfold loZ; split_ifs <;> push_cast <;> omega

theorem zdep (pub : ℕ → ℤ → Bool) (a b : ℤ → Bool) : ∀ s : ℕ, ∀ z : ℤ,
    (∀ y, z + loZ s ≤ y → y ≤ z + 3 * (s : ℤ) → a y = b y) → stZ pub a s z = stZ pub b s z := by
  intro s
  induction s with
  | zero => intro z h; exact h z (by simp [loZ]) (by simp)
  | succ s ih =>
    intro z h
    have hl := loZ_succ s
    rw [stZ_succ, stZ_succ, h _ (by omega) (by push_cast; omega)]
    rw [befZ_agree z (fun j h1 h2 => ih _ (fun y hy1 hy2 => h y (by omega) (by push_cast at hy2 ⊢; omega)))]

theorem zlead (pub : ℕ → ℤ → Bool) (a b : ℤ → Bool) (s : ℕ) (hs : 3 ≤ s) (z : ℤ)
    (h : ∀ y, z + loZ (s + 1) + 1 ≤ y → y ≤ z + 3 * ((s + 1 : ℕ) : ℤ) → a y = b y) :
    xor (stZ pub a (s + 1) z) (a (z + loZ (s + 1))) = xor (stZ pub b (s + 1) z) (b (z + loZ (s + 1))) := by
  have hl : loZ (s + 1) = 1 - 2 * (s : ℤ) := by unfold loZ; split_ifs <;> push_cast <;> omega
  have hl0 : -2 * (s : ℤ) + 3 ≤ loZ s := by unfold loZ; split_ifs <;> omega
  rw [stZ_succ, stZ_succ, hl, show z + 1 - 2 * (s : ℤ) = z + (1 - 2 * (s : ℤ)) by ring]
  rw [befZ_agree z (fun j h1 h2 => zdep pub _ _ s _ (fun y hy1 hy2 => h y (by rw [hl]; omega)
    (by push_cast at hy2 ⊢; omega)))]
  cases befZ (stZ pub b s) z <;> cases a (z + (1 - 2 * (s : ℤ))) <;> cases b (z + (1 - 2 * (s : ℤ))) <;>
    cases pub (s + 1) z <;> rfl

/-- halving inside a set that every flip preserves. -/
theorem halvingS {α : Type} [DecidableEq α] (s : Finset α) (N : ℕ) (C : ℕ → α → Bool) (σ : ℕ → Bool)
    (F : ℕ → α → α) (hinv : ∀ j, j < N → ∀ x, F j (F j x) = x)
    (hs : ∀ j, j < N → ∀ x, x ∈ s → F j x ∈ s)
    (hkeep : ∀ j, j < N → ∀ j', j' < j → ∀ x, C j' (F j x) = C j' x)
    (hflip : ∀ j, j < N → ∀ x, C j (F j x) = !C j x) :
    ∀ M, M ≤ N → (s.filter (fun x => ∀ j, j < M → C j x = σ j)).card * 2 ^ M = s.card := by
  intro M
  induction M with
  | zero =>
    intro _
    simp
  | succ M ih =>
    intro hM
    have h1 := ih (by omega)
    set t := s.filter (fun x => ∀ j, j < M → C j x = σ j) with htdef
    have hsplit : s.filter (fun x => ∀ j, j < M + 1 → C j x = σ j) = t.filter (fun x => C M x = σ M) := by
      ext x
      simp only [htdef, Finset.mem_filter]
      constructor
      · intro h; exact ⟨⟨h.1, fun j hj => h.2 j (by omega)⟩, h.2 M (by omega)⟩
      · intro h
        refine ⟨h.1.1, fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
        · exact h.1.2 j hj
        · rw [hj]; exact h.2
    have h2 := halve_one t (C M) (F M) (hinv M (by omega))
      (fun x hx => by
        simp only [htdef, Finset.mem_filter] at hx ⊢
        refine ⟨hs M (by omega) x hx.1, fun j hj => ?_⟩
        rw [hkeep M (by omega) j hj]; exact hx.2 j hj)
      (hflip M (by omega)) (σ M)
    rw [hsplit, pow_succ, ← h1, ← h2]
    ring

theorem pz_one_iff {k : ℕ} (hk : 0 < k) (x : ℤ) : pz k 1 x = decide (x % (k : ℤ) = 0) := by
  unfold pz
  have h0 := Int.emod_nonneg x (by omega : (k : ℤ) ≠ 0)
  by_cases h : x % (k : ℤ) = 0
  · rw [h]; rfl
  · rw [big_false (show 1 < 2 ^ 1 by norm_num) (show 1 ≤ (x % (k : ℤ)).toNat by omega)]
    simp [h]

theorem testBit_flipK {k : ℕ} (hk : 0 < k) (l : ℤ) (w b : ℕ) (hb : b < k) :
    (flipK k l w).testBit b = xor (w.testBit b) (decide (b = (l % (k : ℤ)).toNat)) := by
  rw [← pz_lt k _ b hb, pz_flipK hk, pz_lt k _ b hb, pz_one_iff hk]
  congr 1
  have h0 := Int.emod_nonneg l (by omega : (k : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos l (by omega : (0 : ℤ) < k)
  rw [decide_eq_decide, ← Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.emod_eq_of_lt (by omega) (by omega)]
  omega

theorem int_mod_ne {k : ℤ} {a b : ℤ} (hk : 0 < k) (hab : a < b) (hb : b < a + k) : a % k ≠ b % k := by
  intro h
  have h2 : (b - a) % k = 0 := by rw [Int.sub_emod, h, sub_self, Int.zero_emod]
  have h3 := Int.emod_emod_of_dvd (b - a) (dvd_refl k)
  rw [Int.emod_eq_of_lt (by omega) (by omega)] at h2
  omega

def cntC (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | j + 1 => cntC b j + (if b j then 1 else 0)

theorem cntC_mono (b : ℕ → Bool) : ∀ j j', j ≤ j' → cntC b j ≤ cntC b j' ∧ cntC b j' - cntC b j ≤ j' - j := by
  intro j j' h
  induction j' with
  | zero => obtain rfl : j = 0 := by omega
            simp
  | succ j' ih =>
    rcases Nat.lt_or_ge j (j' + 1) with h' | h'
    · have := ih (by omega)
      simp only [cntC]; split_ifs <;> omega
    · obtain rfl : j = j' + 1 := by omega
      simp

theorem cntC_le (b : ℕ → Bool) : ∀ j, cntC b j ≤ j := by
  intro j; induction j with
  | zero => simp [cntC]
  | succ j ih => simp only [cntC]; split_ifs <;> omega

theorem cntC_list (b : ℕ → Bool) : ∀ j, ((List.range j).filter (fun h => b h)).length = cntC b j := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih]
    simp only [cntC]
    cases hb : b j <;> simp [List.filter_cons, hb]

/-! ### guards of a cut trace: flips at the leads, unique completion, moving boundary -/

def plZ (cut : ℤ) (o : ℕ → ℕ) (j : ℕ) : ℤ := cut - 3 * (5 + (j : ℤ)) + (o j : ℤ)

def ldZ (cut : ℤ) (o : ℕ → ℕ) (j : ℕ) : ℤ := cut + 5 - 5 * (5 + (j : ℤ)) + (o j : ℤ)

def grd (k : ℕ) (pub : ℕ → ℤ → Bool) (cut : ℤ) (o : ℕ → ℕ) (j w : ℕ) : Bool :=
  xor (xor (stZ pub (pz k w) (4 + j) (plZ cut o j)) (stZ pub (pz k w) (4 + j) (plZ cut o j + 1)))
    (stZ pub (pz k w) (4 + j) (plZ cut o j + 2))

theorem loZ4 (j : ℕ) : loZ (4 + j) = -5 - 2 * (j : ℤ) := by
  unfold loZ; split_ifs <;> push_cast <;> omega

theorem grd_keep {k : ℕ} (hk : 0 < k) (pub : ℕ → ℤ → Bool) (cut : ℤ) (o : ℕ → ℕ)
    (hmono : ∀ j j', j ≤ j' → o j ≤ o j' ∧ o j' - o j ≤ j' - j)
    {j j' : ℕ} (hj' : j' < j) (hjk : 5 * j + 19 < k) (w : ℕ) :
    grd k pub cut o j' (flipK k (ldZ cut o j) w) = grd k pub cut o j' w := by
  have hm := hmono j' j hj'.le
  have hl := loZ4 j'
  have e : ∀ c : ℤ, 0 ≤ c → c ≤ 2 →
      stZ pub (pz k (flipK k (ldZ cut o j) w)) (4 + j') (plZ cut o j' + c) =
        stZ pub (pz k w) (4 + j') (plZ cut o j' + c) := by
    intro c h0 h2
    apply zdep
    intro y hy1 hy2
    apply pz_flipK_off hk
    · unfold ldZ; unfold plZ at hy1; omega
    · unfold ldZ; unfold plZ at hy2; push_cast at hy2; omega
  have e0 := e 0 le_rfl (by norm_num)
  rw [add_zero] at e0
  unfold grd
  rw [e0, e 1 (by norm_num) (by norm_num), e 2 (by norm_num) (by norm_num)]

theorem grd_toggle {k : ℕ} (hk : 0 < k) (pub : ℕ → ℤ → Bool) (cut : ℤ) (o : ℕ → ℕ)
    {j : ℕ} (hjk : 5 * j + 19 < k) (w : ℕ) :
    grd k pub cut o j (flipK k (ldZ cut o j) w) = !grd k pub cut o j w := by
  have hl := loZ4 j
  have e : ∀ c : ℤ, 1 ≤ c → c ≤ 2 →
      stZ pub (pz k (flipK k (ldZ cut o j) w)) (4 + j) (plZ cut o j + c) =
        stZ pub (pz k w) (4 + j) (plZ cut o j + c) := by
    intro c h0 h2
    apply zdep
    intro y hy1 hy2
    apply pz_flipK_off hk
    · unfold ldZ; unfold plZ at hy1; omega
    · unfold ldZ; unfold plZ at hy2; push_cast at hy2; omega
  have e0 := zlead pub (pz k (flipK k (ldZ cut o j) w)) (pz k w) (3 + j) (by omega) (plZ cut o j)
    (fun y hy1 hy2 => by
      apply pz_flipK_off hk
      · unfold ldZ; rw [show 3 + j + 1 = 4 + j by omega, hl] at hy1; unfold plZ at hy1; omega
      · unfold ldZ; unfold plZ at hy2; push_cast at hy2; omega)
  have hpos : plZ cut o j + loZ (3 + j + 1) = ldZ cut o j := by
    rw [show 3 + j + 1 = 4 + j by omega, hl]; unfold plZ ldZ; push_cast; ring
  rw [hpos, pz_flipK_on hk, show 3 + j + 1 = 4 + j by omega] at e0
  have e0' : stZ pub (pz k (flipK k (ldZ cut o j) w)) (4 + j) (plZ cut o j) =
      !stZ pub (pz k w) (4 + j) (plZ cut o j) := by
    revert e0
    cases stZ pub (pz k (flipK k (ldZ cut o j) w)) (4 + j) (plZ cut o j) <;>
      cases stZ pub (pz k w) (4 + j) (plZ cut o j) <;> cases pz k w (ldZ cut o j) <;> simp
  unfold grd
  rw [e0', e 1 (by norm_num) (by norm_num), e 2 (by norm_num) (by norm_num)]
  cases stZ pub (pz k w) (4 + j) (plZ cut o j) <;> simp

/-- unique completion off the pivots with a prescribed trace. -/
theorem complete82 (k n : ℕ) (hk : 5 * n + 15 ≤ k) (pub : ℕ → ℤ → Bool) (cut : ℤ) (o : ℕ → ℕ)
    (hmono : ∀ j j', j ≤ j' → o j ≤ o j' ∧ o j' - o j ≤ j' - j) (cb : ℕ → Bool) (seed : Fin (2 ^ k)) :
    ∃! w : Fin (2 ^ k), (∀ j < n, grd k pub cut o j w.val = cb j) ∧
      ∀ b < k, (∀ j < n, ((ldZ cut o j) % (k : ℤ)).toNat ≠ b) → w.val.testBit b = seed.val.testBit b := by
  classical
  have hk0 : 0 < k := by omega
  set pv : ℕ → ℕ := fun j => ((ldZ cut o j) % (k : ℤ)).toNat with hpv
  have pvlt : ∀ j, pv j < k := fun j => by
    have := Int.emod_lt_of_pos (ldZ cut o j) (by omega : (0 : ℤ) < k)
    have := Int.emod_nonneg (ldZ cut o j) (by omega : (k : ℤ) ≠ 0)
    simp only [hpv]; omega
  have pvinj : ∀ j j', j < n → j' < n → j ≠ j' → pv j ≠ pv j' := by
    intro j j' hj hj' hne heq
    have h0 := Int.emod_nonneg (ldZ cut o j) (by omega : (k : ℤ) ≠ 0)
    have h0' := Int.emod_nonneg (ldZ cut o j') (by omega : (k : ℤ) ≠ 0)
    have hmod : ldZ cut o j % (k : ℤ) = ldZ cut o j' % (k : ℤ) := by simp only [hpv] at heq; omega
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := hmono j j' h.le
      exact int_mod_ne (k := (k : ℤ)) (a := ldZ cut o j') (b := ldZ cut o j) (by omega)
        (by unfold ldZ; omega) (by unfold ldZ; omega) hmod.symm
    · have := hmono j' j h.le
      exact int_mod_ne (k := (k : ℤ)) (a := ldZ cut o j) (b := ldZ cut o j') (by omega)
        (by unfold ldZ; omega) (by unfold ldZ; omega) hmod
  let F : ℕ → Fin (2 ^ k) → Fin (2 ^ k) := fun j x => ⟨flipK k (ldZ cut o j) x.val, flipK_lt hk0 _ x.isLt⟩
  have Finv : ∀ j, j < n → ∀ x, F j (F j x) = x := fun j _ x => Fin.ext (flipK_flipK k _ _)
  have Fbit : ∀ j x b, b < k → (F j x).val.testBit b = xor (x.val.testBit b) (decide (b = pv j)) :=
    fun j x b hb => testBit_flipK hk0 _ _ b hb
  set s0 := (Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
    ∀ b < k, (∀ j < n, pv j ≠ b) → w.val.testBit b = seed.val.testBit b) with hs0
  have Fs : ∀ j, j < n → ∀ x, x ∈ s0 → F j x ∈ s0 := by
    intro j hj x hx
    simp only [hs0, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro b hb hnp
    rw [Fbit j x b hb, hx b hb hnp]
    simp [Ne.symm (hnp j hj)]
  -- the pivot cube has 2^n words
  have hcube := halvingS s0 n (fun j (x : Fin (2 ^ k)) => x.val.testBit (pv j)) (fun j => seed.val.testBit (pv j))
    F Finv Fs
    (fun j hj j' hj' x => by
      rw [Fbit j x (pv j') (pvlt j')]
      simp [pvinj j' j (by omega) hj (by omega)])
    (fun j hj x => by rw [Fbit j x (pv j) (pvlt j)]; simp) n le_rfl
  have hsing : s0.filter (fun x => ∀ j, j < n → x.val.testBit (pv j) = seed.val.testBit (pv j)) = {seed} := by
    ext x
    simp only [hs0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro ⟨h1, h2⟩
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro b
      by_cases hb : b < k
      · by_cases hp : ∃ j < n, pv j = b
        · obtain ⟨j, hj, rfl⟩ := hp
          exact h2 j hj
        · push_neg at hp
          exact h1 b hb hp
      · rw [big_false x.isLt (by omega), big_false seed.isLt (by omega)]
    · rintro rfl; exact ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
  rw [hsing, Finset.card_singleton, one_mul] at hcube
  -- the trace cuts the cube to one word
  have htr := halvingS s0 n (fun j (x : Fin (2 ^ k)) => grd k pub cut o j x.val) cb F Finv Fs
    (fun j hj j' hj' x => grd_keep hk0 pub cut o hmono hj' (by omega) x.val)
    (fun j hj x => grd_toggle hk0 pub cut o (by omega) x.val) n le_rfl
  rw [← hcube] at htr
  have hone := Nat.eq_of_mul_eq_mul_right (by positivity) (htr.trans (one_mul _).symm)
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hone
  have hmem : ∀ y : Fin (2 ^ k), ((∀ j < n, grd k pub cut o j y.val = cb j) ∧
      ∀ b < k, (∀ j < n, pv j ≠ b) → y.val.testBit b = seed.val.testBit b) ↔ y = a := by
    intro y
    rw [← Finset.mem_singleton, ← ha]
    simp only [hs0, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  exact ⟨a, (hmem a).2 rfl, fun y hy => (hmem y).1 hy⟩

/-- the moving boundary: agreement below `front t`. -/
def front (cut : ℤ) (n : ℕ) (cb : ℕ → Bool) : ℕ → ℤ
  | 0 => cut
  | t + 1 => front cut n cb t - 3 + (if 4 ≤ t ∧ t - 4 < n ∧ cb (t - 4) = true then 1 else 0)

theorem front_val (cut : ℤ) (n : ℕ) (cb : ℕ → Bool) :
    ∀ t, front cut n cb t = cut - 3 * (t : ℤ) + (cntC cb (min n (t - 4)) : ℤ) := by
  intro t
  induction t with
  | zero => simp [front, cntC]
  | succ t ih =>
    simp only [front, ih]
    by_cases h4 : 4 ≤ t
    · by_cases hn : t - 4 < n
      · rw [show min n (t + 1 - 4) = (t - 4) + 1 by omega, show min n (t - 4) = t - 4 by omega]
        simp only [cntC]
        by_cases hc : cb (t - 4) = true
        · simp [h4, hn, hc]; push_cast; ring
        · simp [h4, hn, hc]; push_cast; ring
      · rw [show min n (t + 1 - 4) = n by omega, show min n (t - 4) = n by omega]
        simp [hn]; push_cast; ring
    · rw [show min n (t + 1 - 4) = min n (t - 4) by omega]
      simp [h4]; push_cast; ring

theorem front82 (k n : ℕ) (pub : ℕ → ℤ → Bool) (cut : ℤ) (cb : ℕ → Bool) (w : ℕ)
    (htr : ∀ j < n, grd k pub cut (cntC cb) j w = cb j) (other : ℤ → Bool)
    (hag : ∀ z < cut, pz k w z = other z) :
    ∀ t, (∀ z < front cut n cb t, stZ pub (pz k w) t z = stZ pub other t z) ∧
      (∀ z < front cut n cb (t + 1), befZ (stZ pub (pz k w) t) z = befZ (stZ pub other t) z) := by
  have pre : ∀ t, (∀ z < front cut n cb t, stZ pub (pz k w) t z = stZ pub other t z) →
      ∀ z < front cut n cb (t + 1), befZ (stZ pub (pz k w) t) z = befZ (stZ pub other t) z := by
    intro t ht z hz
    simp only [front] at hz
    by_cases hlow : z < front cut n cb t - 3
    · exact befZ_agree z (fun j h1 h2 => ht _ (by omega))
    · -- the boundary bit: an odd guard keeps it equal
      have hb : 4 ≤ t ∧ t - 4 < n ∧ cb (t - 4) = true := by
        by_contra hb; rw [if_neg hb] at hz; omega
      rw [if_pos hb] at hz
      have hz' : z = front cut n cb t - 3 := by omega
      obtain ⟨j, rfl⟩ : ∃ j, t = 4 + j := ⟨t - 4, by omega⟩
      have hj : j < n := by omega
      have hg := htr j hj
      rw [show 4 + j - 4 = j by omega] at hb
      rw [hb.2.2] at hg
      have hfv := front_val cut n cb (4 + j)
      rw [show min n (4 + j - 4) = j by omega] at hfv
      have hpl : plZ cut (cntC cb) j = z := by unfold plZ; rw [hz', hfv]; push_cast; ring
      unfold grd at hg
      rw [hpl] at hg
      have a0 := ht z (by omega)
      have a1 := ht (z + 1) (by omega)
      have a2 := ht (z + 2) (by omega)
      have am := ht (z - 1) (by omega)
      rw [befZ_eq, befZ_eq, ← a0, ← a1, ← a2, ← am, hg]
      simp
  intro t
  induction t with
  | zero =>
    have h0 : ∀ z < front cut n cb 0, stZ pub (pz k w) 0 z = stZ pub other 0 z := fun z hz => hag z hz
    exact ⟨h0, pre 0 h0⟩
  | succ t ih =>
    have h1 : ∀ z < front cut n cb (t + 1), stZ pub (pz k w) (t + 1) z = stZ pub other (t + 1) z := by
      intro z hz
      have hfv := front_val cut n cb (t + 1)
      have hc := cntC_le cb (min n (t + 1 - 4))
      rw [stZ_succ, stZ_succ, ih.2 z hz, hag _ (by omega)]
    exact ⟨h1, pre (t + 1) h1⟩

end PEqualNP.Outside.L_meta_25582_aux

open PEqualNP.Outside.L_meta_25582_aux in
theorem PEqualNP.Outside.L_meta_25582 :
    ∀ (k n : ℕ), 0 < n → 5 * n + 15 ≤ k →
      ∀ (cut : ℤ) (publicBit : ℕ → ℤ → Bool) (code : Fin (2 ^ n)),
      let mix := fun (word : ℤ → Bool) (z : ℤ) =>
        xor (xor (word z) (word (z - 1))) (word (z + 1))
      let before := fun (word : ℤ → Bool) (z : ℤ) =>
        xor (mix word z) (!(mix word (z + 1)) && mix word (z + 2))
      let state := fun (start : ℤ → Bool) (rounds : ℕ) =>
        (List.range rounds).foldl (fun (prev : ℤ → Bool) (tick : ℕ) (z : ℤ) =>
          xor (xor (before prev z) (start (z + 1 - 2 * (tick : ℤ)))) (publicBit (tick + 1) z)) start
      let residue := fun (z : ℤ) => (z % (k : ℤ)).toNat
      let periodic := fun (w : Fin (2 ^ k)) (p : ℤ) => w.val.testBit (residue p)
      let ones := fun (j : ℕ) => ((List.range j).filter (fun h => code.val.testBit h)).length
      let place := fun (j : ℕ) => cut - 3 * (5 + (j : ℤ)) + (ones j : ℤ)
      let pivot := fun (j : ℕ) => residue (cut + 5 - 5 * (5 + (j : ℤ)) + (ones j : ℤ))
      let realizesTrace := fun (w : Fin (2 ^ k)) => ∀ j < n,
        let z := state (periodic w) (4 + j)
        let a := place j
        xor (xor (z a) (z (a + 1))) (z (a + 2)) = code.val.testBit j
      (∀ seed : Fin (2 ^ k), ∃! w : Fin (2 ^ k), realizesTrace w ∧
        ∀ b < k, (∀ j < n, pivot j ≠ b) → w.val.testBit b = seed.val.testBit b) ∧
      ∀ w : Fin (2 ^ k), realizesTrace w → ∀ other : ℤ → Bool,
        (∀ z < cut, periodic w z = other z) →
        ∀ s : ℕ, n + 4 ≤ s → ∀ z : ℤ, z + 3 * (s : ℤ) < cut + (ones n : ℤ) →
          before (state (periodic w) (s - 1)) z = before (state other (s - 1)) z
    := by
  intro k n hn hk cut publicBit code mix before state residue periodic ones place pivot realizesTrace
  have hones : ones = cntC (fun h => code.val.testBit h) := funext fun j => cntC_list _ j
  have hmono : ∀ j j', j ≤ j' → ones j ≤ ones j' ∧ ones j' - ones j ≤ j' - j := by
    intro j j' h; rw [hones]; exact cntC_mono _ j j' h
  refine ⟨fun seed => complete82 k n hk publicBit cut ones hmono (fun j => code.val.testBit j) seed, ?_⟩
  intro w hw other hag s hs z hz
  have hw' : ∀ j < n, grd k publicBit cut ones j w.val = code.val.testBit j := hw
  rw [hones] at hw' hz
  have hf := (front82 k n publicBit cut (fun h => code.val.testBit h) w.val hw' other hag (s - 1)).2
  have hfv := front_val cut n (fun h => code.val.testBit h) (s - 1 + 1)
  rw [show min n (s - 1 + 1 - 4) = n by omega] at hfv
  exact hf z (by rw [hfv]; push_cast; omega)
