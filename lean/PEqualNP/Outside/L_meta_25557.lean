import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25557_aux

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

def rndG (k a : ℕ) (b c : ℕ → ℕ) (w prev j : ℕ) : ℕ :=
  stepF k (prev ^^^ rotF k a prev ^^^ rotF k (k - a) prev) ^^^ rotF k (b j) w ^^^ c (j + 1)

theorem fold_succ {β : Type} (f : β → ℕ → β) (x : β) (n : ℕ) :
    (List.range (n + 1)).foldl f x = f ((List.range n).foldl f x) n := by
  rw [List.range_succ, List.foldl_append]; rfl

theorem pz_rot1 {k : ℕ} (hk : 0 < k) : ∀ z, z < 2 ^ k → ∀ n, pz k (rotF k 1 z) n = pz k z (n + -1) :=
  fun z hz n => by rw [pz_rotF hk hz]; norm_num [sub_eq_add_neg]

theorem pz_rotkm1 {k : ℕ} (hk : 0 < k) :
    ∀ z, z < 2 ^ k → ∀ n, pz k (rotF k (k - 1) z) n = pz k z (n + 1) := fun z hz n => by
  rw [pz_rotF hk hz, Nat.cast_sub (by omega), Nat.cast_one,
    show n - ((k : ℤ) - 1) = n + 1 - k by ring, pz_sub_k]

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

def st (k u : ℕ) (cs : ℕ → ℕ) (w t : ℕ) : ℕ :=
  (List.range t).foldl (rndG k 1 (fun j => 2 * j) cs w) (rotF k 1 w ^^^ u)

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

theorem halve_one {α : Type} [DecidableEq α] (s : Finset α) (p : α → Bool) (F : α → α)
    (hinv : ∀ x, F (F x) = x) (hs : ∀ x, x ∈ s → F x ∈ s) (hp : ∀ x, p (F x) = !p x) (b : Bool) :
    2 * (s.filter (fun x => p x = b)).card = s.card := by
  have e1 : (s.filter (fun x => p x = b)).card = (s.filter (fun x => ¬ p x = b)).card := by
    apply Finset.card_nbij' F F
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx ⊢
      refine ⟨hs x hx.1, ?_⟩
      rw [hp, hx.2]; cases b <;> simp
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx ⊢
      refine ⟨hs x hx.1, ?_⟩
      rw [hp]; revert hx; cases b <;> cases p x <;> simp
    · intro x _; exact hinv x
    · intro x _; exact hinv x
  have e2 := Finset.card_filter_add_card_filter_not (s := s) (fun x => p x = b)
  omega

def flipK (k : ℕ) (l : ℤ) (w : ℕ) : ℕ := w ^^^ rotF k ((l % (k : ℤ)).toNat) 1

theorem flipK_lt {k : ℕ} (l : ℤ) {w : ℕ} (hw : w < 2 ^ k) : flipK k l w < 2 ^ k :=
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

theorem pz_one_zero (k : ℕ) : pz k 1 0 = true := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl, pz_nat, Nat.zero_mod]; rfl

theorem pz_flipK_off {k : ℕ} (hk : 0 < k) (l : ℤ) (w : ℕ) (m : ℤ) (h1 : 1 ≤ m - l) (h2 : m - l < k) :
    pz k (flipK k l w) m = pz k w m := by
  have h1' : (1 : ℕ) < 2 ^ 1 := by norm_num
  rw [pz_flipK hk, maskfree h1' (m - l) 0 (by simpa using h1) (by simpa using h2), Bool.xor_false]

theorem pz_flipK_on {k : ℕ} (hk : 0 < k) (l : ℤ) (w : ℕ) :
    pz k (flipK k l w) l = !pz k w l := by
  rw [pz_flipK hk, sub_self, pz_one_zero k]; cases pz k w l <;> rfl

def mixZ (w : ℤ → Bool) (z : ℤ) : Bool := xor (xor (w z) (w (z - 1))) (w (z + 1))

def befZ (w : ℤ → Bool) (z : ℤ) : Bool := xor (mixZ w z) (!(mixZ w (z + 1)) && mixZ w (z + 2))

def stZ (pub : ℕ → ℤ → Bool) (start : ℤ → Bool) (n : ℕ) : ℤ → Bool :=
  (List.range n).foldl (fun (prev : ℤ → Bool) (tick : ℕ) (z : ℤ) =>
    xor (xor (befZ prev z) (start (z + 1 - 2 * (tick : ℤ)))) (pub (tick + 1) z)) start

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
    rw [show 3 + j + 1 = 4 + j by omega, hl]; unfold plZ ldZ; ring
  rw [hpos, pz_flipK_on hk, show 3 + j + 1 = 4 + j by omega] at e0
  have e0' : stZ pub (pz k (flipK k (ldZ cut o j) w)) (4 + j) (plZ cut o j) =
      !stZ pub (pz k w) (4 + j) (plZ cut o j) := by
    revert e0
    cases stZ pub (pz k (flipK k (ldZ cut o j) w)) (4 + j) (plZ cut o j) <;>
      cases stZ pub (pz k w) (4 + j) (plZ cut o j) <;> cases pz k w (ldZ cut o j) <;> simp
  unfold grd
  rw [e0', e 1 (by norm_num) (by norm_num), e 2 (by norm_num) (by norm_num)]
  cases stZ pub (pz k w) (4 + j) (plZ cut o j) <;> simp

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
        · simp [h4, hn, hc]; ring
        · simp [h4, hn, hc]; ring
      · rw [show min n (t + 1 - 4) = n by omega, show min n (t - 4) = n by omega]
        simp [hn]; ring
    · rw [show min n (t + 1 - 4) = min n (t - 4) by omega]
      simp [h4]; ring

theorem boundaryAgreement (k n : ℕ) (pub : ℕ → ℤ → Bool) (cut : ℤ) (cb : ℕ → Bool) (w : ℕ)
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
    ·
      have hb : 4 ≤ t ∧ t - 4 < n ∧ cb (t - 4) = true := by
        by_contra hb; rw [ite_eq_right hb] at hz; omega
      rw [ite_eq_left hb] at hz
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

def publicBit (k u : ℕ) (cs : ℕ → ℕ) (t : ℕ) (z : ℤ) : Bool :=
  xor (pz k u (z + 3 - 2 * (t : ℤ))) (pz k (cs t) z)

theorem liftState {k u w : ℕ} (hk : 0 < k) (hu : u < 2 ^ k)
    (hw : w < 2 ^ k) (cs : ℕ → ℕ) (hc : ∀ j, cs j < 2 ^ k) (t : ℕ) :
    pz k (st k u cs w t) = stZ (publicBit k u cs) (pz k (rotF k 1 w ^^^ u)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext z
    rw [pz_st_succ hk hw, pz_preF hk (st_lt hu hc w t), ← befZ_eq, ih, stZ_succ]
    unfold publicBit
    rw [pz_xor, pz_rotF hk hw]
    rw [show z + 1 - 2 * (t : ℤ) - (1 : ℕ) = z - ((2 * t : ℕ) : ℤ) by push_cast; ring,
      show z + 3 - 2 * ((t + 1 : ℕ) : ℤ) = z + 1 - 2 * (t : ℤ) by push_cast; ring]
    generalize befZ (stZ (fun t z => pz k u (z + 3 - 2 * (t : ℤ)) ^^ pz k (cs t) z)
      (pz k (rotF k 1 w ^^^ u)) t) z = prev
    cases prev <;> cases pz k w (z - ((2 * t : ℕ) : ℤ)) <;>
      cases pz k u (z + 1 - 2 * (t : ℤ)) <;> cases pz k (cs (t + 1)) z <;> rfl

theorem liftOutput {k u w i : ℕ} (hk : 0 < k) (hu : u < 2 ^ k)
    (hw : w < 2 ^ k) (hi : i < k) (cs : ℕ → ℕ) (hc : ∀ j, cs j < 2 ^ k) (t : ℕ) :
    (preF k (st k u cs w t)).testBit i =
    befZ (stZ (publicBit k u cs) (pz k (rotF k 1 w ^^^ u)) t) i := by
  rw [← pz_lt _ _ _ hi, pz_preF hk (st_lt hu hc w t), ← befZ_eq, liftState hk hu hw cs hc]

def initial (k u : ℕ) (hu : u < 2 ^ k) (w : Fin (2 ^ k)) : Fin (2 ^ k) :=
  ⟨rotF k 1 w.val ^^^ u, Nat.xor_lt_two_pow (rotF_lt _ _ _) hu⟩

theorem initial_injective {k u : ℕ} (hk : 0 < k) (hu : u < 2 ^ k) :
    Function.Injective (initial k u hu) := by
  intro w w' h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < k
  · have h' := congrArg (fun x : Fin (2 ^ k) => pz k x.val ((b : ℤ) + 1)) h
    simp only [initial, pz_xor, pz_rotF hk w.isLt, pz_rotF hk w'.isLt,
      Nat.cast_one, add_sub_cancel_right, pz_lt _ _ _ hb] at h'
    cases pz k u ((b : ℤ) + 1) <;> simpa using h'
  · rw [big_false w.isLt (by omega), big_false w'.isLt (by omega)]

theorem unchangedBeforeCut {k r e q i u w m : ℕ}
    (hk : 0 < k) (hsize : k + e + 3 = 5 * r) (hq : 0 < q) (hr : e + q + 4 ≤ r)
    (hw : w < 2 ^ k) (hm : m < 2 ^ q) (z : ℤ)
    (hlo : (i : ℤ) - 2 * r + 4 ≤ z)
    (hhi : z < (i : ℤ) + 3 * r - ((e + q - 1 : ℕ) : ℤ)) :
    pz k (rotF k 1 w ^^^ u) z =
    pz k (rotF k 1 (w ^^^ rotF k (i + 3 * r + k - e - q) m) ^^^ u) z := by
  have hqk : q ≤ k := by omega
  have hmk : m < 2 ^ k := lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hqk)
  have hwm := Nat.xor_lt_two_pow hw (rotF_lt k (i + 3 * r + k - e - q) m)
  simp only [pz_xor, pz_rotF hk hw, pz_rotF hk hwm, pz_rotF hk hmk, Nat.cast_one]
  rw [maskfree hm (z - 1 - ((i + 3 * r + k - e - q : ℕ) : ℤ)) 2 (by omega) (by omega)]
  simp

def roll (guard : ℕ → ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | j + 1 => roll guard j + (if guard j (roll guard j) then 1 else 0)

def traceBit (k : ℕ) (pub : ℕ → ℤ → Bool) (cut : ℤ) (w j : ℕ) : Bool :=
  let guard := fun j o => grd k pub cut (fun _ => o) j w
  guard j (roll guard j)

theorem tracePrefix (k : ℕ) (pub : ℕ → ℤ → Bool) (cut : ℤ) (w j : ℕ) :
    cntC (traceBit k pub cut w) j = roll (fun j o => grd k pub cut (fun _ => o) j w) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [cntC, roll, ih, traceBit]
    rfl

theorem cntC_congr {a b : ℕ → Bool} (n : ℕ) (h : ∀ j < n, a j = b j) :
    cntC a n = cntC b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cntC, cntC, ih (fun j hj => h j (by omega)), h n (by omega)]

def traceSet (k n : ℕ) (pub : ℕ → ℤ → Bool) (cut : ℤ) (w : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun j => traceBit k pub cut w j)

def setBit (s : Finset ℕ) (j : ℕ) : Bool := decide (j ∈ s)

theorem traceSet_bit (k n : ℕ) (pub : ℕ → ℤ → Bool) (cut : ℤ) (w j : ℕ) (hj : j < n) :
    setBit (traceSet k n pub cut w) j = traceBit k pub cut w j := by
  simp [setBit, traceSet, hj]

theorem realizedTrace (k n : ℕ) (pub : ℕ → ℤ → Bool) (cut : ℤ) (w : ℕ) :
    ∀ j < n, grd k pub cut (cntC (setBit (traceSet k n pub cut w))) j w =
      setBit (traceSet k n pub cut w) j := by
  intro j hj
  have hc : cntC (setBit (traceSet k n pub cut w)) j = cntC (traceBit k pub cut w) j :=
    cntC_congr j (fun h hh => traceSet_bit k n pub cut w h (by omega))
  rw [traceSet_bit k n pub cut w j hj]
  unfold grd plZ
  rw [hc, tracePrefix]
  rfl

theorem cntC_card_filter (b : ℕ → Bool) (n : ℕ) :
    cntC b n = ((Finset.range n).filter (fun j => b j)).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cntC, ih, Finset.range_add_one, Finset.filter_insert]
    cases h : b n <;> simp [h]

theorem traceFiber (k n : ℕ) (hwidth : 5 * n + 15 ≤ k) (pub : ℕ → ℤ → Bool)
    (cut : ℤ) (cb : ℕ → Bool) :
    ((Finset.univ : Finset (Fin (2 ^ k))).filter
      (fun w => ∀ j < n, grd k pub cut (cntC cb) j w.val = cb j)).card = 2 ^ (k - n) := by
  classical
  have hk : 0 < k := by omega
  let toggle (j : ℕ) (w : Fin (2 ^ k)) : Fin (2 ^ k) :=
    ⟨flipK k (ldZ cut (cntC cb) j) w.val, flipK_lt _ w.isLt⟩
  have h := halvingS Finset.univ n (fun j (w : Fin (2 ^ k)) => grd k pub cut (cntC cb) j w.val)
    cb toggle (fun j _ w => Fin.ext (flipK_flipK k (ldZ cut (cntC cb) j) w.val))
    (fun _ _ _ _ => Finset.mem_univ _)
    (fun j hj j' hj' w => grd_keep hk pub cut _ (cntC_mono cb) hj' (by omega) w.val)
    (fun j hj w => grd_toggle hk pub cut (cntC cb) (by omega) w.val) n (le_refl _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have hp : (2 : ℕ) ^ k = 2 ^ (k - n) * 2 ^ n := by
    rw [← pow_add, show k - n + n = k by omega]
  exact Nat.eq_of_mul_eq_mul_right (by positivity) (h.trans hp)

theorem countSmallTraces (k n d : ℕ) (hwidth : 5 * n + 15 ≤ k)
    (pub : ℕ → ℤ → Bool) (cut : ℤ) {A : Finset (Fin (2 ^ k))}
    (f : Fin (2 ^ k) → Fin (2 ^ k)) (hf : Function.Injective f)
    (hsmall : ∀ w ∈ A, (traceSet k n pub cut (f w).val).card ≤ d) :
    A.card ≤ (∑ j ∈ Finset.range (d + 1), Nat.choose n j) * 2 ^ (k - n) := by
  classical
  let t (w : Fin (2 ^ k)) := traceSet k n pub cut (f w).val
  let allowed := (Finset.range (d + 1)).biUnion (fun j => (Finset.range n).powersetCard j)
  have hm : (A : Set (Fin (2 ^ k))).MapsTo t allowed := by
    intro w hw
    have hwA : w ∈ A := hw
    apply Finset.mem_biUnion.2
    refine ⟨(t w).card, Finset.mem_range.2 (Nat.lt_succ_of_le (hsmall w hwA)),
      Finset.mem_powersetCard.2 ⟨?_, rfl⟩⟩
    exact Finset.filter_subset _ _
  have hallowed : allowed.card ≤ ∑ j ∈ Finset.range (d + 1), Nat.choose n j := by
    unfold allowed
    calc
      _ ≤ ∑ j ∈ Finset.range (d + 1), ((Finset.range n).powersetCard j).card :=
        Finset.card_biUnion_le
      _ = _ := by simp [Finset.card_powersetCard]
  calc
    A.card = ∑ s ∈ allowed, (A.filter (fun w => t w = s)).card :=
      Finset.card_eq_sum_card_fiberwise hm
    _ ≤ ∑ _s ∈ allowed, 2 ^ (k - n) := by
      apply Finset.sum_le_sum
      intro s _
      let B := (Finset.univ : Finset (Fin (2 ^ k))).filter
        (fun w => ∀ j < n, grd k pub cut (cntC (setBit s)) j w.val = setBit s j)
      have hB : B.card = 2 ^ (k - n) := traceFiber k n hwidth pub cut (setBit s)
      rw [← hB, ← Finset.card_image_of_injective _ hf]
      apply Finset.card_le_card
      intro x hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hx
      have ht : t w = s := (Finset.mem_filter.1 hw).2
      have hz := realizedTrace k n pub cut (f w).val
      change ∀ j < n, grd k pub cut (cntC (setBit (t w))) j (f w).val = setBit (t w) j at hz
      rw [ht] at hz
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hz⟩
    _ = allowed.card * 2 ^ (k - n) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hallowed

theorem outputEqOfLargeTrace {k r e q n u i w m : ℕ}
    (hk : 0 < k) (hsize : k + e + 3 = 5 * r) (hq : 0 < q) (hr : e + q + 4 ≤ r)
    (hn : n + 4 ≤ r) (hu : u < 2 ^ k) (hi : i < k) (hw : w < 2 ^ k) (hm : m < 2 ^ q)
    (cs : ℕ → ℕ) (hc : ∀ j, cs j < 2 ^ k)
    (hlarge : e + q - 1 <
      (traceSet k n (publicBit k u cs) ((i : ℤ) + 3 * r - ((e + q - 1 : ℕ) : ℤ))
        (rotF k 1 w ^^^ u)).card) :
    (preF k (st k u cs w (r - 1))).testBit i =
      (preF k (st k u cs (w ^^^ rotF k (i + 3 * r + k - e - q) m) (r - 1))).testBit i := by
  let changed := w ^^^ rotF k (i + 3 * r + k - e - q) m
  change _ = (preF k (st k u cs changed (r - 1))).testBit i
  have hchanged : changed < 2 ^ k := Nat.xor_lt_two_pow hw (rotF_lt _ _ _)
  rw [liftOutput hk hu hw hi cs hc, liftOutput hk hu hchanged hi cs hc]
  let cut : ℤ := (i : ℤ) + 3 * r - ((e + q - 1 : ℕ) : ℤ)
  let pub := publicBit k u cs
  let base := rotF k 1 w ^^^ u
  let alter := rotF k 1 changed ^^^ u
  let cb := setBit (traceSet k n pub cut base)
  let patched (z : ℤ) := if z < cut then pz k base z else pz k alter z
  change befZ (stZ pub (pz k base) (r - 1)) i = befZ (stZ pub (pz k alter) (r - 1)) i
  have hcnt : cntC cb n = (traceSet k n pub cut base).card := by
    rw [cntC_card_filter]
    congr 1
    ext j
    simp [cb, setBit, traceSet]
  have hfront := (boundaryAgreement k n pub cut cb base (realizedTrace k n pub cut base)
    patched (fun z hz => (ite_eq_left hz).symm) (r - 1)).2
  have hbelow : (i : ℤ) < front cut n cb (r - 1 + 1) := by
    rw [show r - 1 + 1 = r by omega, front_val, min_eq_left (by omega : n ≤ r - 4), hcnt]
    change (i : ℤ) < (i : ℤ) + 3 * r - ((e + q - 1 : ℕ) : ℤ) - 3 * r +
      ((traceSet k n pub cut base).card : ℤ)
    change e + q - 1 < (traceSet k n pub cut base).card at hlarge
    omega
  refine (hfront i hbelow).trans ?_
  apply befZ_agree
  intro j hj hj'
  apply zdep
  intro z hz _
  have hlocal : (i : ℤ) - 2 * r + 4 ≤ z := by
    simp only [loZ, ite_eq_right (by omega : ¬ r - 1 ≤ 3)] at hz
    omega
  by_cases hzcut : z < cut
  · simp only [patched, ite_eq_left hzcut]
    exact unchangedBeforeCut hk hsize hq hr hw hm z hlocal hzcut
  · simp [patched, hzcut]

end PEqualNP.Outside.L_meta_25557_aux

open PEqualNP.Outside.L_meta_25557_aux in
theorem PEqualNP.Outside.L_meta_25557 : (∀ (k r e q : ℕ) (constants : ℕ → Fin (2 ^ k)) (u i : ℕ),
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
  let T := min r ((k + 5) / 5)
  let N := T - 4
  let D := e + q - 1
  D < N →
  ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun base =>
    ∃ mask : Fin (2 ^ q),
      before base.val ≠ before (base.val ^^^ rot (i + 3 * r + k - e - q) mask.val))).card ≤
    (∑ j ∈ Finset.range (D + 1), Nat.choose N j) * 2 ^ (k - N)) := by
  classical
  intro k r e q constants u i hq hk4 hsize hr hu hi
  dsimp only
  intro hDN
  let T := min r ((k + 5) / 5)
  let N := T - 4
  let D := e + q - 1
  change D < N at hDN
  have hk : 0 < k := by omega
  have hTr : T ≤ r := min_le_left _ _
  have hTk : T ≤ (k + 5) / 5 := min_le_right _ _
  have hdiv := Nat.div_mul_le_self (k + 5) 5
  have hNT : N + 4 = T := by dsimp only [N] at hDN ⊢; omega
  have hwidth : 5 * N + 15 ≤ k := by omega
  have hN : N + 4 ≤ r := hNT.trans_le hTr
  let cs := fun j => (constants j).val
  let pub := publicBit k u cs
  let cut : ℤ := (i : ℤ) + 3 * r - (D : ℤ)
  let before (w : ℕ) := (preF k (st k u cs w (r - 1))).testBit i
  let affected := (Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
    ∃ m : Fin (2 ^ q), before w.val ≠ before (w.val ^^^ rotF k (i + 3 * r + k - e - q) m.val))
  change affected.card ≤ (∑ j ∈ Finset.range (D + 1), Nat.choose N j) * 2 ^ (k - N)
  apply countSmallTraces k N D hwidth pub cut (initial k u hu) (initial_injective hk hu)
  intro w hw
  obtain ⟨m, hm⟩ := (Finset.mem_filter.1 hw).2
  by_contra! hlarge
  exact hm (outputEqOfLargeTrace hk hsize hq hr hN hu hi w.isLt m.isLt cs
    (fun j => (constants j).isLt) hlarge)
