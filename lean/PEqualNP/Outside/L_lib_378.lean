import Mathlib
import PEqualNP.Defs

-- L-lib-378: dependency windows of the row test. For r = 1, 2 and r >= 4 (not 3, where leads cancel), bit i
-- of the state is key bit i-left-1 XOR a function of key bits i-left..i-left-1+width (Dep/DepL combinators).
-- Key bit m is start bit m+1 XOR row bit m+1, so equal start windows after p = i-left give equal window
-- functions, and the XOR of the two outputs at i equals the XOR of the start bits at p.

namespace PEqualNP.Outside.L_lib_378_aux

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


/-! ### the rotated-name round (first-test shape) -/

def rnd (k : ℕ) (c : ℕ → ℕ) (w prev j : ℕ) : ℕ :=
  stepF k (prev ^^^ rotF k 1 prev ^^^ rotF k (k - 1) prev) ^^^ rotF k (2 * j) w ^^^ c (j + 1)

theorem Bd_rnd {k : ℕ} (c : ℕ → ℕ) (hc : ∀ j, c j < 2 ^ k) (F : ℕ → ℕ) (j : ℕ) :
    Bd k (fun w => rnd k c w (F w) j) := fun w _ =>
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepF_lt _ _) (rotF_lt _ _ _)) (hc _)

theorem DepL_rnd {k : ℕ} (hk : 0 < k) (c : ℕ → ℕ) {F : ℕ → ℕ} {e lo hi : ℤ}
    (hF : DepL k F e lo hi) (hB : Bd k F) (h1 : e + 1 ≤ lo) (h2 : e ≤ hi) (j : ℕ)
    {e' lo' hi' : ℤ} (he : e' = e - 1) (hlo : lo' ≤ e) (hhi : hi + 3 ≤ hi')
    (hj1 : lo' ≤ -((2 * j : ℕ) : ℤ)) (hj2 : -((2 * j : ℕ) : ℤ) ≤ hi') :
    DepL k (fun w => rnd k c w (F w) j) e' lo' hi' := by
  subst he
  have hF0 : Dep k F e hi := Dep_of_DepL hF (by omega) le_rfl le_rfl h2
  have hR1 : DepL k (fun w => rotF k 1 (F w)) (e - 1) e (hi + 1) := by
    have := DepL_rot hk hB hF 1
    simp only [Nat.cast_one] at this
    exact DepL_mono this (by omega) (by omega)
  have hR2 : Dep k (fun w => rotF k (k - 1) (F w)) e (hi + 1) := by
    have := Dep_addk (Dep_rot hk hB hF0 (k - 1))
    rw [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one] at this
    exact Dep_mono this (by omega) (by omega)
  have hM : DepL k (fun w => F w ^^^ rotF k 1 (F w) ^^^ rotF k (k - 1) (F w)) (e - 1) e (hi + 1) :=
    DepL_xor (DepL_xor_left (Dep_mono hF0 le_rfl (by omega)) hR1) hR2
  have hMB : Bd k (fun w => F w ^^^ rotF k 1 (F w) ^^^ rotF k (k - 1) (F w)) := fun w hw =>
    Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (hB w hw) (rotF_lt _ _ _)) (rotF_lt _ _ _)
  have hS := DepL_step hk hM (by omega) (by omega)
  have hS' := DepL_mono (lo' := lo') hS (by omega) (by omega : hi + 1 + 2 ≤ hi')
  have hK := Dep_mono (Dep_key hk (2 * j)) hj1 hj2
  exact DepL_xor (DepL_xor hS' hK) (Dep_const k (c (j + 1)) lo' hi')

theorem DepL_seed {k : ℕ} (hk : 0 < k) (u : ℕ) :
    DepL k (fun w => rotF k 1 w ^^^ u) (-1) 0 (-1) := by
  have := DepL_xor (DepL_key hk 1 0 (-1)) (Dep_const k u 0 (-1))
  simpa using this

theorem Bd_seed {k u : ℕ} (hu : u < 2 ^ k) : Bd k (fun w => rotF k 1 w ^^^ u) := fun _ _ =>
  Nat.xor_lt_two_pow (rotF_lt _ _ _) hu


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

theorem xor_swap4 {a b c d : Bool} (h : xor a b = xor c d) : xor a c = xor b d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

theorem finish_lib {k : ℕ} (hk : 0 < k) {S : ℕ → ℕ} {l L : ℕ}
    (hS : DepL k S (-((l : ℤ) + 1)) (-((l : ℤ) + 1) + 1) (-((l : ℤ) + 1) + L)) (hl : l ≤ k)
    {u w v : ℕ} (hu : u < 2 ^ k) (hw : w < 2 ^ k) (hv : v < 2 ^ k) {i : ℕ} (hi : i < k)
    (hag : ∀ j : Fin L, (rotF k 1 w ^^^ u).testBit (((i + k - l) % k + 1 + j.val) % k) =
      (rotF k 1 v ^^^ u).testBit (((i + k - l) % k + 1 + j.val) % k)) :
    xor ((S w).testBit i) ((S v).testBit i) =
      xor ((rotF k 1 w ^^^ u).testBit ((i + k - l) % k))
        ((rotF k 1 v ^^^ u).testBit ((i + k - l) % k)) := by
  have kb : ∀ x, x < 2 ^ k → ∀ m : ℤ,
      pz k x m = xor (pz k (rotF k 1 x ^^^ u) (m + 1)) (pz k u (m + 1)) := by
    intro x hx m
    rw [pz_xor, pz_rotF hk hx, Nat.cast_one, add_sub_cancel_right, Bool.xor_assoc, Bool.xor_self,
      Bool.xor_false]
  have h0 : (((i + k - l) % k : ℕ) : ℤ) ≡ (i : ℤ) - l [ZMOD k] := by
    rw [Int.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add]
    refine (Int.mod_modEq _ _).trans ?_
    show _ % _ = _ % _
    rw [show (i : ℤ) + k - l = ((i : ℤ) - l) + k * 1 by ring, Int.add_mul_emod_self_left]
  have hp : ∀ j : ℕ, (((i + k - l) % k + j : ℕ) : ℤ) ≡ (i : ℤ) - l + j [ZMOD k] := by
    intro j; rw [Nat.cast_add]; exact h0.add_right _
  have hD := hS w v hw hv (i : ℤ) (by
    intro t t1 t2
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, t = -(l : ℤ) + j := ⟨(t + l).toNat, by omega⟩
    rw [kb w hw, kb v hv]
    have := hag ⟨j, by omega⟩
    simp only at this
    rw [← pz_nat, ← pz_nat] at this
    have hc : (((i + k - l) % k + 1 + j : ℕ) : ℤ) ≡ (i : ℤ) + (-(l : ℤ) + j) + 1 [ZMOD k] := by
      rw [Nat.add_assoc, show (i : ℤ) + (-(l : ℤ) + j) + 1 = (i : ℤ) - l + ((1 + j : ℕ) : ℤ) by
        push_cast; ring]
      exact hp (1 + j)
    rw [pz_modEq hc, pz_modEq hc] at this
    rw [this])
  have eP : ∀ X, pz k X ((i : ℤ) + -((l : ℤ) + 1) + 1) = X.testBit ((i + k - l) % k) := by
    intro X
    rw [show X.testBit ((i + k - l) % k) = X.testBit ((i + k - l) % k % k) by rw [Nat.mod_mod],
      ← pz_nat]
    apply pz_modEq
    rw [show (i : ℤ) + -((l : ℤ) + 1) + 1 = (i : ℤ) - l + ((0 : ℕ) : ℤ) by push_cast; ring]
    exact (hp 0).symm
  rw [kb w hw, kb v hv, eP (rotF k 1 w ^^^ u), eP (rotF k 1 v ^^^ u), eP u] at hD
  rw [← pz_lt k (S w) i hi, ← pz_lt k (S v) i hi]
  revert hD
  cases pz k (S w) i <;> cases pz k (S v) i <;>
    cases (rotF k 1 w ^^^ u).testBit ((i + k - l) % k) <;>
    cases (rotF k 1 v ^^^ u).testBit ((i + k - l) % k) <;>
    cases u.testBit ((i + k - l) % k) <;> simp

theorem DepL_congr {k F e lo hi e' lo' hi'} (h : DepL k F e lo hi) (h1 : e = e') (h2 : lo = lo')
    (h3 : hi = hi') : DepL k F e' lo' hi' := by subst h1 h2 h3; exact h

theorem mainLib378 (k r : ℕ) (u : Fin (2 ^ k)) (c : ℕ → Fin (2 ^ k)) (hr1 : 1 ≤ r) (hr3 : r ≠ 3)
    (hwid : max r (2 * r - 3) + 3 * r < k) (i : Fin k) (w v : Fin (2 ^ k))
    (hag : ∀ j : Fin (max r (2 * r - 3) + 3 * r),
      (rotF k 1 w.val ^^^ u.val).testBit (((i.val + k - max r (2 * r - 3)) % k + 1 + j.val) % k) =
      (rotF k 1 v.val ^^^ u.val).testBit (((i.val + k - max r (2 * r - 3)) % k + 1 + j.val) % k)) :
    xor (((List.range r).foldl (rnd k (fun j => (c j).val) w.val) (rotF k 1 w.val ^^^ u.val)).testBit i.val)
      (((List.range r).foldl (rnd k (fun j => (c j).val) v.val) (rotF k 1 v.val ^^^ u.val)).testBit i.val) =
    xor ((rotF k 1 w.val ^^^ u.val).testBit ((i.val + k - max r (2 * r - 3)) % k))
      ((rotF k 1 v.val ^^^ u.val).testBit ((i.val + k - max r (2 * r - 3)) % k)) := by
  have hk : 0 < k := by omega
  have hc : ∀ j, (fun j => (c j).val) j < 2 ^ k := fun j => (c j).isLt
  have hlv : (r = 1 ∧ max r (2 * r - 3) = 1) ∨ (r = 2 ∧ max r (2 * r - 3) = 2) ∨
      (4 ≤ r ∧ max r (2 * r - 3) = 2 * r - 3) := by
    rw [Nat.max_def]; split_ifs <;> omega
  generalize hl : max r (2 * r - 3) = l at hag hwid hlv ⊢
  have h0 := DepL_seed hk u.val
  have hB0 := Bd_seed (k := k) u.isLt
  rcases hlv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hr4, rfl⟩
  · have h1 := DepL_rnd hk (fun j => (c j).val) h0 hB0 (by norm_num) (by norm_num) 0
      (e' := -(((1 : ℕ) : ℤ) + 1)) (lo' := -(((1 : ℕ) : ℤ) + 1) + 1)
      (hi' := -(((1 : ℕ) : ℤ) + 1) + ((1 + 3 * 1 : ℕ) : ℤ)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    exact finish_lib hk h1 (by omega) u.isLt w.isLt v.isLt i.isLt hag
  · have h1 := DepL_rnd hk (fun j => (c j).val) h0 hB0 (by norm_num) (by norm_num) 0
      (e' := -2) (lo' := -1) (hi' := 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    have h2 := DepL_rnd hk (fun j => (c j).val) h1 (Bd_rnd _ hc _ 0) (by norm_num) (by norm_num) 1
      (e' := -(((2 : ℕ) : ℤ) + 1)) (lo' := -(((2 : ℕ) : ℤ) + 1) + 1)
      (hi' := -(((2 : ℕ) : ℤ) + 1) + ((2 + 3 * 2 : ℕ) : ℤ)) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
    exact finish_lib hk h2 (by omega) u.isLt w.isLt v.isLt i.isLt hag
  · obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
    obtain ⟨hL, _⟩ := final_DepL (a := 1) (s0 := 1) hk (by omega) u.isLt (fun j => 2 * j)
      (fun j => (c j).val) hc (fun n => -(max ((n : ℤ) + 1) (2 * n - 2))) (fun n => 3 * n - 1)
      (by norm_num) (by norm_num) (fun n => by push_cast; omega) j
      (lo' := -((2 * j : ℕ) : ℤ) + 1) (hi' := -((2 * j : ℕ) : ℤ) + ((5 * (j + 1) - 3 : ℕ) : ℤ))
      (by push_cast; omega) (by push_cast; omega)
    have hL' := DepL_congr hL (e' := -(((2 * (j + 1) - 3 : ℕ) : ℤ) + 1))
      (lo' := -(((2 * (j + 1) - 3 : ℕ) : ℤ) + 1) + 1)
      (hi' := -(((2 * (j + 1) - 3 : ℕ) : ℤ) + 1) + ((2 * (j + 1) - 3 + 3 * (j + 1) : ℕ) : ℤ))
      (by push_cast [Nat.cast_sub (show 3 ≤ 2 * (j + 1) by omega)]; ring)
      (by push_cast [Nat.cast_sub (show 3 ≤ 2 * (j + 1) by omega)]; ring)
      (by push_cast [Nat.cast_sub (show 3 ≤ 2 * (j + 1) by omega),
        Nat.cast_sub (show 3 ≤ 5 * (j + 1) by omega)]; ring)
    exact finish_lib (S := fun x => (List.range (j + 1)).foldl (rnd k (fun j => (c j).val) x)
      (rotF k 1 x ^^^ u.val)) hk hL' (by omega) u.isLt w.isLt v.isLt i.isLt hag

end PEqualNP.Outside.L_lib_378_aux

theorem PEqualNP.Outside.L_lib_378 :
    ∀ (k r : Nat) (u : Fin (2 ^ k)) (c : Nat → Fin (2 ^ k)),
      1 ≤ r → r ≠ 3 →
      let left := max r (2 * r - 3)
      let width := left + 3 * r
      width < k →
      let rot := fun (s w : Nat) =>
        ((w <<< (s % k)) ||| (w >>> (k - s % k))) % 2 ^ k
      let step := fun (x : Nat) =>
        (List.range k).foldl (fun acc i =>
          acc ||| ((xor (x.testBit i)
            (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))).toNat <<< i)) 0
      let start := fun (w : Fin (2 ^ k)) => rot 1 w.val ^^^ u.val
      let state := fun (w : Fin (2 ^ k)) =>
        (List.range r).foldl (fun prev j =>
          step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * j) w.val ^^^ (c (j + 1)).val)
          (start w)
      ∀ (i : Fin k) (w v : Fin (2 ^ k)),
        let p := (i.val + k - left) % k
        (∀ j : Fin width,
          (start w).testBit ((p + 1 + j.val) % k) =
          (start v).testBit ((p + 1 + j.val) % k)) →
        xor ((state w).testBit i.val) ((state v).testBit i.val) =
          xor ((start w).testBit p) ((start v).testBit p)
      := by
  intro k r u c hr1 hr3 left width hwid rot step start state i w v p hag
  exact PEqualNP.Outside.L_lib_378_aux.mainLib378 k r u c hr1 hr3 hwid i w v hag
