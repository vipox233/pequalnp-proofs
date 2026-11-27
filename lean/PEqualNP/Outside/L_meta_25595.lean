import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25594

namespace PEqualNP.Outside.L_meta_25595_aux

private def idx (k : ℕ) (hk : 0 < k) (n : ℕ) : Fin k :=
  ⟨n % k, Nat.mod_lt _ hk⟩

private def wadd {k : ℕ} (x y : Fin k → Bool) (i : Fin k) : Bool :=
  xor (x i) (y i)

private def wzero {k : ℕ} : Fin k → Bool :=
  fun _ => false

private def wunit {k : ℕ} (p i : Fin k) : Bool :=
  decide (i = p)

private def rot (k : ℕ) (hk : 0 < k) (s : ℕ) (x : Fin k → Bool) (i : Fin k) : Bool :=
  x (idx k hk (i.val + k - s % k))

private def rotInv (k : ℕ) (hk : 0 < k) (s : ℕ) (x : Fin k → Bool) (i : Fin k) : Bool :=
  x (idx k hk (i.val + s % k))

private def mix (k d : ℕ) (hk : 0 < k) (x : Fin k → Bool) (i : Fin k) : Bool :=
  xor (xor (x i) (x (idx k hk (i.val + d)))) (x (idx k hk (i.val + k - d)))

private def delta {k : ℕ} (f : (Fin k → Bool) → Bool) (h x : Fin k → Bool) : Bool :=
  xor (f x) (f (wadd x h))

private def delta4 {k : ℕ} (f : (Fin k → Bool) → Bool) (h1 h2 h3 h4 x : Fin k → Bool) : Bool :=
  delta (delta (delta (delta f h1) h2) h3) h4 x

private lemma wadd_comm {k : ℕ} (x y : Fin k → Bool) : wadd x y = wadd y x := by
  funext i
  simp [wadd, Bool.xor_comm]

private lemma wadd_assoc {k : ℕ} (x y z : Fin k → Bool) : wadd (wadd x y) z = wadd x (wadd y z) := by
  funext i
  simp [wadd]

private lemma wadd_self {k : ℕ} (x : Fin k → Bool) : wadd x x = wzero := by
  funext i
  simp [wadd, wzero]

private lemma wadd_zero {k : ℕ} (x : Fin k → Bool) : wadd x wzero = x := by
  funext i
  simp [wadd, wzero]

private lemma zero_wadd {k : ℕ} (x : Fin k → Bool) : wadd wzero x = x := by
  funext i
  simp [wadd, wzero]

private lemma wadd_cancel_right {k : ℕ} (x y : Fin k → Bool) : wadd (wadd x y) y = x := by
  rw [wadd_assoc, wadd_self, wadd_zero]

private lemma wadd_eq_zero_iff {k : ℕ} (x y : Fin k → Bool) : wadd x y = wzero ↔ x = y := by
  constructor
  · intro h
    have h1 : wadd (wadd x y) y = wadd wzero y := congrArg (fun z => wadd z y) h
    rw [wadd_cancel_right, zero_wadd] at h1
    exact h1
  · rintro rfl
    exact wadd_self x

private lemma idx_eq_iff (k : ℕ) (hk : 0 < k) (a b : ℕ) :
    idx k hk a = idx k hk b ↔ a % k = b % k := by
  simp [idx, Fin.ext_iff]

private lemma idx_val_add (k : ℕ) (hk : 0 < k) (n m : ℕ) :
    idx k hk ((idx k hk n).val + m) = idx k hk (n + m) := by
  rw [idx_eq_iff]
  simp [idx, Nat.add_mod]

private lemma idx_val_add_sub (k d : ℕ) (hk : 0 < k) (hdk : d ≤ k) (n : ℕ) :
    idx k hk ((idx k hk n).val + k - d) = idx k hk (n + (k - d)) := by
  rw [idx_eq_iff]
  have h1 : (idx k hk n).val + k - d = (idx k hk n).val + (k - d) := by omega
  rw [h1]
  simp [idx, Nat.add_mod]

private lemma idx_add_k (k : ℕ) (hk : 0 < k) (n : ℕ) :
    idx k hk (n + k) = idx k hk n := by
  rw [idx_eq_iff, Nat.add_mod_right]

private lemma idx_self (k : ℕ) (hk : 0 < k) (i : Fin k) :
    idx k hk i.val = i := by
  ext
  exact Nat.mod_eq_of_lt i.isLt

private lemma mod_eq_of_lt_two_mul {x k : ℕ} (hx : x < 2 * k) :
    x % k = if x < k then x else x - k := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have h1 : x = (x - k) + k := by omega
    conv_lhs => rw [h1]
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private lemma mod_cancel_add (k a b c : ℕ) (hk : 0 < k) (h : (a + c) % k = (b + c) % k) :
    a % k = b % k := by
  have ha : a % k < k := Nat.mod_lt a hk
  have hb : b % k < k := Nat.mod_lt b hk
  have hc : c % k < k := Nat.mod_lt c hk
  rw [Nat.add_mod, Nat.add_mod b c] at h
  rw [mod_eq_of_lt_two_mul (x := a % k + c % k) (by omega),
    mod_eq_of_lt_two_mul (x := b % k + c % k) (by omega)] at h
  split_ifs at h <;> omega

private lemma rot_add (k : ℕ) (hk : 0 < k) (s : ℕ) (x y : Fin k → Bool) :
    rot k hk s (wadd x y) = wadd (rot k hk s x) (rot k hk s y) := rfl

private def eRot (k : ℕ) (hk : 0 < k) (s : ℕ) : Equiv.Perm (Fin k → Bool) where
  toFun := rot k hk s
  invFun := rotInv k hk s
  left_inv x := by
    funext i
    dsimp only [rot, rotInv]
    have hlt : s % k < k := Nat.mod_lt s hk
    rw [idx_val_add_sub k (s % k) hk (by omega)]
    have heq : i.val + s % k + (k - s % k) = i.val + k := by omega
    rw [heq, idx_add_k, idx_self]
  right_inv x := by
    funext i
    dsimp only [rot, rotInv]
    have hlt : s % k < k := Nat.mod_lt s hk
    rw [idx_val_add]
    have heq : i.val + k - s % k + s % k = i.val + k := by omega
    rw [heq, idx_add_k, idx_self]

private lemma mix_add (k d : ℕ) (hk : 0 < k) (x y : Fin k → Bool) :
    mix k d hk (wadd x y) = wadd (mix k d hk x) (mix k d hk y) := by
  funext i
  simp only [mix, wadd]
  cases x i <;> cases y i <;>
    cases x (idx k hk (i.val + d)) <;> cases y (idx k hk (i.val + d)) <;>
    cases x (idx k hk (i.val + k - d)) <;> cases y (idx k hk (i.val + k - d)) <;> rfl

private lemma mix_zero (k d : ℕ) (hk : 0 < k) :
    mix k d hk wzero = wzero := by
  funext i
  simp [mix, wzero]

private lemma mix_eq_zero_imp (k d : ℕ) (hk : 0 < k) (hk3 : k % 3 ≠ 0) (hdk : d < k)
    (hk1 : 1 < k) (x : Fin k → Bool) (hx : mix k d hk x = wzero) : x = wzero := by
  have hmix : ∀ i : Fin k,
      xor (xor (x i) (x (idx k hk (i.val + d)))) (x (idx k hk (i.val + k - d))) = false :=
    fun i => congrFun hx i
  have hstep2 : ∀ i : Fin k, x (idx k hk (i.val + 2 * d)) = x (idx k hk (i.val + k - d)) := by
    intro i
    have h0 := hmix i
    have h1 := hmix (idx k hk (i.val + d))
    have h1a : idx k hk ((idx k hk (i.val + d)).val + d) = idx k hk (i.val + 2 * d) := by
      rw [idx_val_add]; congr 1; omega
    have h1b : idx k hk ((idx k hk (i.val + d)).val + k - d) = i := by
      rw [idx_val_add_sub k d hk (by omega)]
      have heq : i.val + d + (k - d) = i.val + k := by omega
      rw [heq, idx_add_k, idx_self]
    rw [h1a, h1b] at h1
    generalize x i = v0 at h0 h1
    generalize x (idx k hk (i.val + d)) = v1 at h0 h1
    generalize x (idx k hk (i.val + 2 * d)) = v2 at h1 ⊢
    generalize x (idx k hk (i.val + k - d)) = vm at h0 ⊢
    cases v0 <;> cases v1 <;> cases v2 <;> cases vm <;> simp_all
  have hstep3 : ∀ i : Fin k, x (idx k hk (i.val + 3 * d)) = x i := by
    intro i
    have h1 := hstep2 (idx k hk (i.val + d))
    have h1a : idx k hk ((idx k hk (i.val + d)).val + 2 * d) = idx k hk (i.val + 3 * d) := by
      rw [idx_val_add]; congr 1; omega
    have h1b : idx k hk ((idx k hk (i.val + d)).val + k - d) = i := by
      rw [idx_val_add_sub k d hk (by omega)]
      have heq : i.val + d + (k - d) = i.val + k := by omega
      rw [heq, idx_add_k, idx_self]
    rw [h1a, h1b] at h1
    exact h1
  have hiter : ∀ (m : ℕ) (i : Fin k), x (idx k hk (i.val + m * (3 * d))) = x i := by
    intro m
    induction m with
    | zero =>
      intro i
      simpa using congrArg x (idx_self k hk i)
    | succ m ih =>
      intro i
      have hrew : idx k hk (i.val + (m + 1) * (3 * d)) =
          idx k hk ((idx k hk (i.val + m * (3 * d))).val + 3 * d) := by
        rw [idx_val_add]; congr 1; ring
      rw [hrew, hstep3, ih]
  have hinv3 : ∃ m : ℕ, (3 * m) % k = 1 := by
    by_cases h1 : k % 3 = 1
    · refine ⟨(2 * k + 1) / 3, ?_⟩
      have heq : 3 * ((2 * k + 1) / 3) = 1 + 2 * k := by omega
      rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk1]
    · refine ⟨(k + 1) / 3, ?_⟩
      have heq : 3 * ((k + 1) / 3) = 1 + 1 * k := by omega
      rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk1]
  rcases hinv3 with ⟨m, hm⟩
  have hstep1 : ∀ i : Fin k, x (idx k hk (i.val + d)) = x i := by
    intro i
    have h1 := hiter m i
    have hidx : idx k hk (i.val + m * (3 * d)) = idx k hk (i.val + d) := by
      rw [idx_eq_iff, Nat.add_mod, Nat.add_mod i.val d]
      have hmul : (m * (3 * d)) % k = d % k := by
        rw [show m * (3 * d) = (3 * m) * d by ring, Nat.mul_mod, hm, one_mul, Nat.mod_mod]
      rw [hmul]
    rw [hidx] at h1
    exact h1
  funext i
  have hp := hstep1 i
  have hm0 : x (idx k hk (i.val + k - d)) = x i := by
    have h1 := hstep1 (idx k hk (i.val + k - d))
    have heq : idx k hk ((idx k hk (i.val + k - d)).val + d) = i := by
      rw [idx_val_add, show i.val + k - d + d = i.val + k by omega, idx_add_k, idx_self]
    rw [heq] at h1
    exact h1.symm
  have h0 := hmix i
  rw [hp, hm0] at h0
  dsimp only [wzero]
  cases hx0 : x i <;> simp_all

private lemma mix_bijective (k d : ℕ) (hk : 0 < k) (hk3 : k % 3 ≠ 0) (hdk : d < k) (hk1 : 1 < k) :
    Function.Bijective (mix k d hk) := by
  apply Finite.injective_iff_bijective.mp
  intro x y hxy
  have hsub : mix k d hk (wadd x y) = wzero := by
    rw [mix_add, hxy, wadd_self]
  exact (wadd_eq_zero_iff x y).mp (mix_eq_zero_imp k d hk hk3 hdk hk1 (wadd x y) hsub)

private lemma delta_xor {k : ℕ} (f g : (Fin k → Bool) → Bool) (h z : Fin k → Bool) :
    delta (fun w => xor (f w) (g w)) h z = xor (delta f h z) (delta g h z) := by
  simp only [delta]
  cases f z <;> cases g z <;> cases f (wadd z h) <;> cases g (wadd z h) <;> rfl

private lemma delta_xor_fn {k : ℕ} (f g : (Fin k → Bool) → Bool) (h : Fin k → Bool) :
    delta (fun w => xor (f w) (g w)) h = fun w => xor (delta f h w) (delta g h w) := by
  funext w
  exact delta_xor f g h w

private lemma delta4_xor {k : ℕ} (f g : (Fin k → Bool) → Bool) (h1 h2 h3 h4 z : Fin k → Bool) :
    delta4 (fun w => xor (f w) (g w)) h1 h2 h3 h4 z =
      xor (delta4 f h1 h2 h3 h4 z) (delta4 g h1 h2 h3 h4 z) := by
  simp only [delta4, delta_xor_fn]

private lemma delta_comm {k : ℕ} (f : (Fin k → Bool) → Bool) (h1 h2 : Fin k → Bool) :
    delta (delta f h1) h2 = delta (delta f h2) h1 := by
  funext z
  simp only [delta]
  have h12 : wadd (wadd z h2) h1 = wadd (wadd z h1) h2 := by
    rw [wadd_assoc, wadd_comm h2 h1, ← wadd_assoc]
  rw [h12]
  cases f z <;> cases f (wadd z h1) <;> cases f (wadd z h2) <;>
    cases f (wadd (wadd z h1) h2) <;> rfl

private lemma delta4_swap_pairs {k : ℕ} (f : (Fin k → Bool) → Bool) (h1 h2 h3 h4 z : Fin k → Bool) :
    delta4 f h1 h2 h3 h4 z = delta4 f h3 h4 h1 h2 z := by
  unfold delta4
  rw [delta_comm (delta f h1) h2 h3]
  rw [delta_comm f h1 h3]
  rw [delta_comm (delta (delta f h3) h1) h2 h4]
  rw [delta_comm (delta f h3) h1 h4]

private lemma foldl_xor_init (l : List Bool) (a : Bool) :
    l.foldl xor a = xor a (l.foldl xor false) := by
  induction l generalizing a with
  | nil => simp
  | cons b bs ih =>
    simp only [List.foldl_cons, Bool.false_xor]
    rw [ih (xor a b), ih b, Bool.xor_assoc]

private lemma foldl_xor_ofFn_xor :
    ∀ {k : ℕ} (f g : Fin k → Bool),
      (List.ofFn (fun i => xor (f i) (g i))).foldl xor false =
        xor ((List.ofFn f).foldl xor false) ((List.ofFn g).foldl xor false)
  | 0, _, _ => by simp
  | k + 1, f, g => by
    simp only [List.ofFn_succ, List.foldl_cons, Bool.false_xor]
    rw [foldl_xor_init (List.ofFn (fun i : Fin k => xor (f i.succ) (g i.succ))),
      foldl_xor_init (List.ofFn (fun i : Fin k => f i.succ)),
      foldl_xor_init (List.ofFn (fun i : Fin k => g i.succ)),
      foldl_xor_ofFn_xor]
    cases f 0 <;> cases g 0 <;>
      cases (List.ofFn (fun i : Fin k => f i.succ)).foldl xor false <;>
      cases (List.ofFn (fun i : Fin k => g i.succ)).foldl xor false <;> rfl

private lemma step_2d_reach (k d : ℕ) (hk : 0 < k) (hk2 : k % 2 = 1) (hd : d = 1 ∨ d = 2)
    (hk1 : 1 < k) (Q : Fin k → Prop)
    (hstep : ∀ i : Fin k, Q i → Q (idx k hk (i.val + 2 * d)))
    (h0 : Q ⟨0, hk⟩) : ∀ i : Fin k, Q i := by
  have hiter : ∀ (m : ℕ) (i : Fin k), Q i → Q (idx k hk (i.val + m * (2 * d))) := by
    intro m
    induction m with
    | zero =>
      intro i hi
      simpa [idx_self] using hi
    | succ m ih =>
      intro i hi
      have hrew : idx k hk (i.val + (m + 1) * (2 * d)) =
          idx k hk ((idx k hk (i.val + m * (2 * d))).val + 2 * d) := by
        rw [idx_val_add]; congr 1; ring
      rw [hrew]
      exact hstep _ (ih i hi)
  have hinv : ∃ r : ℕ, (r * (2 * d)) % k = 1 := by
    let h2 := (k + 1) / 2
    have hh2 : 2 * h2 = k + 1 := by omega
    rcases hd with rfl | rfl
    · refine ⟨h2, ?_⟩
      have heq : h2 * (2 * 1) = 1 + 1 * k := by omega
      rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk1]
    · refine ⟨h2 * h2, ?_⟩
      have heq : h2 * h2 * (2 * 2) = 1 + (k + 2) * k := by
        calc h2 * h2 * (2 * 2) = (2 * h2) * (2 * h2) := by ring
          _ = (k + 1) * (k + 1) := by rw [hh2]
          _ = 1 + (k + 2) * k := by ring
      rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk1]
  rcases hinv with ⟨r, hr⟩
  intro i
  have h1 := hiter (i.val * r) ⟨0, hk⟩ h0
  have heq : idx k hk (0 + i.val * r * (2 * d)) = i := by
    rw [zero_add]
    ext
    dsimp only [idx]
    rw [show i.val * r * (2 * d) = i.val * (r * (2 * d)) by ring,
      Nat.mul_mod, hr, mul_one, Nat.mod_mod, Nat.mod_eq_of_lt i.isLt]
  rw [heq] at h1
  exact h1

private theorem main_aux : ∀ (k d : ℕ) (hk : 0 < k), k % 3 ≠ 0 → (d = 1 ∨ d = 2) → 4 * d + 4 < k →
    let W := Fin k → Bool
    let idx' := fun (n : ℕ) => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
    let add' := fun (x y : W) (i : Fin k) => xor (x i) (y i)
    let rot' := fun (s : ℕ) (x : W) (i : Fin k) => x (idx' (i.val + k - s % k))
    let mix' := fun (x : W) (i : Fin k) =>
      xor (xor (x i) (x (idx' (i.val + d)))) (x (idx' (i.val + k - d)))
    let step' := fun (x : W) (i : Fin k) =>
      xor (x i) (!(x (idx' (i.val + 1))) && x (idx' (i.val + 2)))
    ∀ (s t h : ℕ) (name c₁ c₂ mask : W) (P : W → W),
      (∀ x y, P (add' x y) = add' (P x) (P y)) → (∀ z, P (P z) = P z) →
      let keyMix := fun (w : W) => mix' (rot' s w)
      let observed := fun (w : W) =>
        let initial := mix' (add' (rot' s w) name)
        let middle := add' (step' initial) (add' (rot' t w) c₁)
        let out := add' (step' (mix' middle)) (add' (rot' h w) c₂)
        (List.ofFn (fun bit : Fin k => mask bit && out bit)).foldl xor false
      (∃ left right : W → Bool, ∀ x y : W,
        observed (add' (P x) (add' y (P y))) = xor (left x) (right y)) →
      (∀ j : Fin k, mask j = true →
        let a := idx' (j.val + k + 3 - d)
        let b := idx' (j.val + 3 + d)
        (∀ w : W, keyMix (P w) a = false ∧ keyMix (P w) b = false) ∨
        (∀ w : W, keyMix (add' w (P w)) a = false ∧ keyMix (add' w (P w)) b = false)) ∧
      (k % 2 = 1 → mask = (fun _maskPos => true) →
        (∀ w : W, P w = (fun _zeroPos => false)) ∨ (∀ w : W, P w = w)) := by
  intro k d hk hk3 hd hdk W idx' add' rot' mix' step' s t h name c₁ c₂ mask P hPadd hPidem
    keyMix observed hsplit
  have hd_pos : 0 < d := by omega
  have hdk_lt : d < k := by omega
  have hk1 : 1 < k := by omega
  let eMix : Equiv.Perm W := Equiv.ofBijective (mix k d hk) (mix_bijective k d hk hk3 hdk_lt hk1)
  let eKey : Equiv.Perm W := (eRot k hk s).trans eMix
  have heKey_eq : ∀ w : W, eKey w = keyMix w := fun _ => rfl
  have heKey_add : ∀ x y : W, eKey (wadd x y) = wadd (eKey x) (eKey y) := by
    intro x y
    exact mix_add k d hk (rot k hk s x) (rot k hk s y)
  have heKey_zero : eKey wzero = wzero := by
    change mix k d hk (rot k hk s wzero) = wzero
    have hrz : rot k hk s wzero = wzero := rfl
    rw [hrz, mix_zero]
  have heKey_symm_add : ∀ x y : W, eKey.symm (wadd x y) = wadd (eKey.symm x) (eKey.symm y) := by
    intro x y
    apply eKey.injective
    rw [eKey.apply_symm_apply, heKey_add, eKey.apply_symm_apply, eKey.apply_symm_apply]
  let wOf : W → W := fun z => eKey.symm (wadd z (mix k d hk name))
  have hwOf_add : ∀ z dh : W, wOf (wadd z dh) = wadd (wOf z) (eKey.symm dh) := by
    intro z dh
    dsimp only [wOf]
    rw [← heKey_symm_add]
    congr 1
    rw [wadd_assoc, wadd_comm dh (mix k d hk name), ← wadd_assoc]
  have hinit : ∀ z : W, mix' (add' (rot' s (wOf z)) name) = z := by
    intro z
    change mix k d hk (wadd (rot k hk s (wOf z)) name) = z
    rw [mix_add]
    change wadd (eKey (eKey.symm (wadd z (mix k d hk name)))) (mix k d hk name) = z
    rw [eKey.apply_symm_apply, wadd_cancel_right]
  let feedback : W → W := fun z => rot k hk t (eKey.symm z)
  have hfb : ∀ x y : W, feedback (wadd x y) = wadd (feedback x) (feedback y) := by
    intro x y
    dsimp only [feedback]
    rw [heKey_symm_add, rot_add]
  let offset : W := wadd (rot k hk t (eKey.symm (mix k d hk name))) c₁
  let obs94 : W → Bool := fun z =>
    let middle := wadd (step' z) (wadd (feedback z) offset)
    let out := step' (mix' middle)
    (List.ofFn (fun bit : Fin k => mask bit && out bit)).foldl xor false
  let linTail : W → Bool := fun z =>
    (List.ofFn (fun bit : Fin k =>
      mask bit && xor (rot k hk h (wOf z) bit) (c₂ bit))).foldl xor false
  have hobs_decomp : ∀ z : W, observed (wOf z) = xor (obs94 z) (linTail z) := by
    intro z
    dsimp only [observed, obs94, linTail]
    have hmid_eq : add' (step' (mix' (add' (rot' s (wOf z)) name))) (add' (rot' t (wOf z)) c₁) =
        wadd (step' z) (wadd (feedback z) offset) := by
      rw [hinit z]
      change wadd (step' z) (wadd (rot k hk t (eKey.symm (wadd z (mix k d hk name)))) c₁) =
        wadd (step' z) (wadd (rot k hk t (eKey.symm z))
          (wadd (rot k hk t (eKey.symm (mix k d hk name))) c₁))
      rw [heKey_symm_add, rot_add, wadd_assoc]
    rw [hmid_eq]
    rw [← foldl_xor_ofFn_xor]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp only [List.getElem_ofFn]
      change (mask ⟨i, _⟩ &&
        xor (step' (mix' (wadd (step' z) (wadd (feedback z) offset))) ⟨i, _⟩)
          (xor (rot k hk h (wOf z) ⟨i, _⟩) (c₂ ⟨i, _⟩))) =
        xor (mask ⟨i, _⟩ && step' (mix' (wadd (step' z) (wadd (feedback z) offset))) ⟨i, _⟩)
          (mask ⟨i, _⟩ && xor (rot k hk h (wOf z) ⟨i, _⟩) (c₂ ⟨i, _⟩))
      cases mask ⟨i, _⟩ <;>
        cases step' (mix' (wadd (step' z) (wadd (feedback z) offset))) ⟨i, _⟩ <;>
        cases rot k hk h (wOf z) ⟨i, _⟩ <;> cases c₂ ⟨i, _⟩ <;> rfl
  have hlin_delta2 : ∀ h1 h2 z : W, delta (delta linTail h1) h2 z = false := by
    intro h1 h2 z
    have hd1 : ∀ w : W, delta linTail h1 w =
        (List.ofFn (fun bit : Fin k => mask bit && rot k hk h (eKey.symm h1) bit)).foldl xor false := by
      intro w
      dsimp only [delta, linTail]
      rw [← foldl_xor_ofFn_xor]
      congr 1
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp only [List.getElem_ofFn, hwOf_add, rot_add]
        change xor (mask ⟨i, _⟩ && xor (rot k hk h (wOf w) ⟨i, _⟩) (c₂ ⟨i, _⟩))
          (mask ⟨i, _⟩ && xor (xor (rot k hk h (wOf w) ⟨i, _⟩) (rot k hk h (eKey.symm h1) ⟨i, _⟩))
            (c₂ ⟨i, _⟩)) =
          (mask ⟨i, _⟩ && rot k hk h (eKey.symm h1) ⟨i, _⟩)
        cases mask ⟨i, _⟩ <;> cases rot k hk h (wOf w) ⟨i, _⟩ <;>
          cases rot k hk h (eKey.symm h1) ⟨i, _⟩ <;> cases c₂ ⟨i, _⟩ <;> rfl
    change xor (delta linTail h1 z) (delta linTail h1 (wadd z h2)) = false
    rw [hd1 z, hd1 (wadd z h2), Bool.xor_self]
  have hlin_delta4 : ∀ h1 h2 h3 h4 z : W, delta4 linTail h1 h2 h3 h4 z = false := by
    intro h1 h2 h3 h4 z
    have hfn : delta (delta linTail h1) h2 = fun _ => false := funext (hlin_delta2 h1 h2)
    unfold delta4
    rw [hfn]
    simp [delta]
  have hdelta4_obs : ∀ (j : Fin k) (u v base : W),
      let lo := idx k hk (j.val + k + 2 - d)
      let hi := idx k hk (j.val + 4 + d)
      let a := idx k hk (j.val + k + 3 - d)
      let b := idx k hk (j.val + 3 + d)
      delta4 (fun z => observed (wOf z)) (wunit lo) (wunit hi) u v base =
        (mask j && xor (u a && v b) (u b && v a)) := by
    intro j u v base lo hi a b
    have hfun : (fun z => observed (wOf z)) = fun z => xor (obs94 z) (linTail z) :=
      funext hobs_decomp
    rw [hfun, delta4_xor, hlin_delta4, Bool.xor_false]
    exact PEqualNP.Outside.L_meta_25594 k d hk hd_pos hdk feedback hfb offset mask j u v base
  have hmixed_zero : ∀ w1 w2 base_w : W,
      delta (delta observed (P w1)) (wadd w2 (P w2)) base_w = false := by
    rcases hsplit with ⟨left, right, hlr⟩
    have hP0 : P wzero = wzero := by
      have h1 := hPadd wzero wzero
      change P (wadd wzero wzero) = wadd (P wzero) (P wzero) at h1
      rw [wadd_self, wadd_self] at h1
      exact h1
    have hform : ∀ bw a b : W,
        wadd bw (wadd (P a) (wadd b (P b))) =
          wadd (P (wadd bw a)) (wadd (wadd bw b) (P (wadd bw b))) := by
      intro bw a b
      have hpa : P (wadd bw a) = wadd (P bw) (P a) := hPadd bw a
      have hpb : P (wadd bw b) = wadd (P bw) (P b) := hPadd bw b
      rw [hpa, hpb]
      funext i
      simp only [wadd]
      cases bw i <;> cases P bw i <;> cases P a i <;> cases b i <;> cases P b i <;> rfl
    intro w1 w2 base_w
    have h00 : observed base_w = xor (left base_w) (right base_w) := by
      have h1 : observed (wadd (P base_w) (wadd base_w (P base_w))) =
          xor (left base_w) (right base_w) := hlr base_w base_w
      have harg : wadd (P base_w) (wadd base_w (P base_w)) = base_w := by
        funext i; simp only [wadd]; cases base_w i <;> cases P base_w i <;> rfl
      rw [harg] at h1
      exact h1
    have h10 : observed (wadd base_w (P w1)) = xor (left (wadd base_w w1)) (right base_w) := by
      have h1 := hform base_w w1 wzero
      rw [hP0, wadd_zero, wadd_zero, wadd_zero] at h1
      have h2 : observed (wadd (P (wadd base_w w1)) (wadd base_w (P base_w))) =
          xor (left (wadd base_w w1)) (right base_w) := hlr (wadd base_w w1) base_w
      rw [h1]
      exact h2
    have h01 : observed (wadd base_w (wadd w2 (P w2))) =
        xor (left base_w) (right (wadd base_w w2)) := by
      have h1 := hform base_w wzero w2
      rw [hP0, zero_wadd, wadd_zero] at h1
      have h2 : observed (wadd (P base_w) (wadd (wadd base_w w2) (P (wadd base_w w2)))) =
          xor (left base_w) (right (wadd base_w w2)) := hlr base_w (wadd base_w w2)
      rw [h1]
      exact h2
    have h11 : observed (wadd (wadd base_w (P w1)) (wadd w2 (P w2))) =
        xor (left (wadd base_w w1)) (right (wadd base_w w2)) := by
      have h1 := hform base_w w1 w2
      rw [← wadd_assoc] at h1
      have h2 : observed (wadd (P (wadd base_w w1)) (wadd (wadd base_w w2) (P (wadd base_w w2)))) =
          xor (left (wadd base_w w1)) (right (wadd base_w w2)) := hlr (wadd base_w w1) (wadd base_w w2)
      rw [h1]
      exact h2
    simp only [delta]
    have hcomm : wadd (wadd base_w (wadd w2 (P w2))) (P w1) =
        wadd (wadd base_w (P w1)) (wadd w2 (P w2)) := by
      rw [wadd_assoc, wadd_comm (wadd w2 (P w2)) (P w1), ← wadd_assoc]
    rw [hcomm, h00, h10, h01, h11]
    cases left base_w <;> cases right base_w <;>
      cases left (wadd base_w w1) <;> cases right (wadd base_w w2) <;> rfl
  have hdet_zero : ∀ (j : Fin k), mask j = true → ∀ (w1 w2 : W),
      let a := idx k hk (j.val + k + 3 - d)
      let b := idx k hk (j.val + 3 + d)
      xor (keyMix (P w1) a && keyMix (wadd w2 (P w2)) b)
          (keyMix (P w1) b && keyMix (wadd w2 (P w2)) a) = false := by
    intro j hmj w1 w2 a b
    let lo := idx k hk (j.val + k + 2 - d)
    let hi := idx k hk (j.val + 4 + d)
    have h1 := hdelta4_obs j (eKey (P w1)) (eKey (wadd w2 (P w2))) wzero
    dsimp only at h1
    rw [hmj, Bool.true_and, heKey_eq, heKey_eq] at h1
    have h2 : delta (delta (fun z => observed (wOf z)) (eKey (P w1))) (eKey (wadd w2 (P w2))) =
        fun _ => false := by
      funext z
      have hshift : ∀ dh x : W, wOf (wadd x (eKey dh)) = wadd (wOf x) dh := by
        intro dh x
        rw [hwOf_add, eKey.symm_apply_apply]
      simp only [delta, hshift]
      exact hmixed_zero w1 w2 (wOf z)
    have h3 : delta4 (fun z => observed (wOf z)) (wunit lo) (wunit hi)
        (eKey (P w1)) (eKey (wadd w2 (P w2))) wzero = false := by
      rw [delta4_swap_pairs]
      unfold delta4
      rw [h2]
      simp [delta]
    rw [← h1]
    exact h3
  have hpart1 : ∀ j : Fin k, mask j = true →
      let a := idx' (j.val + k + 3 - d)
      let b := idx' (j.val + 3 + d)
      (∀ w : W, keyMix (P w) a = false ∧ keyMix (P w) b = false) ∨
      (∀ w : W, keyMix (add' w (P w)) a = false ∧ keyMix (add' w (P w)) b = false) := by
    intro j hmj a b
    have hab : a ≠ b := by
      intro heq
      have hmod : (j.val + k + 3 - d) % k = (j.val + 3 + d) % k := congrArg Fin.val heq
      have h1 : (0 + (j.val + (k - d + 3))) % k = (2 * d + (j.val + (k - d + 3))) % k := by
        have hl : 0 + (j.val + (k - d + 3)) = j.val + k + 3 - d := by omega
        have hr : 2 * d + (j.val + (k - d + 3)) = (j.val + 3 + d) + k := by omega
        rw [hl, hr, Nat.add_mod_right, hmod]
      have h2 := mod_cancel_add k 0 (2 * d) (j.val + (k - d + 3)) hk h1
      rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)] at h2
      omega
    have hsplit_all : ∀ x : W, keyMix x = wadd (keyMix (P x)) (keyMix (wadd x (P x))) := by
      intro x
      rw [← heKey_eq, ← heKey_eq, ← heKey_eq, ← heKey_add]
      congr 1
      funext i; simp only [wadd]; cases x i <;> cases P x i <;> rfl
    by_contra hboth
    push Not at hboth
    rcases hboth with ⟨⟨w1, hw1⟩, ⟨w2, hw2⟩⟩
    have hw1' : keyMix (P w1) a = true ∨ keyMix (P w1) b = true := by
      cases ha1 : keyMix (P w1) a <;> cases hb1 : keyMix (P w1) b
      · exact False.elim (hw1 ha1 hb1)
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
    have hw2' : keyMix (wadd w2 (P w2)) a = true ∨ keyMix (wadd w2 (P w2)) b = true := by
      cases ha2 : keyMix (wadd w2 (P w2)) a <;> cases hb2 : keyMix (wadd w2 (P w2)) b
      · exact False.elim (hw2 ha2 hb2)
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
    let p1 := keyMix (P w1) a
    let q1 := keyMix (P w1) b
    let p2 := keyMix (wadd w2 (P w2)) a
    let q2 := keyMix (wadd w2 (P w2)) b
    have hd12 : xor (p1 && q2) (q1 && p2) = false := hdet_zero j hmj w1 w2
    let ta : Bool := if p1 then false else true
    let tb : Bool := if p1 then true else false
    let target : W := fun i => if i = a then ta else if i = b then tb else false
    let w := eKey.symm target
    have hkw : keyMix w = target := by
      rw [← heKey_eq, eKey.apply_symm_apply]
    have hka : keyMix w a = ta := by simp [hkw, target]
    have hkb : keyMix w b = tb := by simp [hkw, target, hab.symm]
    have hsplit_w : keyMix w = wadd (keyMix (P w)) (keyMix (wadd w (P w))) := hsplit_all w
    have hxa : ta = xor (keyMix (P w) a) (keyMix (wadd w (P w)) a) := by
      rw [← hka, hsplit_w]; rfl
    have hxb : tb = xor (keyMix (P w) b) (keyMix (wadd w (P w)) b) := by
      rw [← hkb, hsplit_w]; rfl
    have hdw2 : xor (keyMix (P w) a && q2) (keyMix (P w) b && p2) = false :=
      hdet_zero j hmj w w2
    have hd1w : xor (p1 && keyMix (wadd w (P w)) b) (q1 && keyMix (wadd w (P w)) a) = false :=
      hdet_zero j hmj w1 w
    change p1 = true ∨ q1 = true at hw1'
    change p2 = true ∨ q2 = true at hw2'
    dsimp only [ta, tb] at hxa hxb
    generalize keyMix (P w) a = ua at hxa hdw2
    generalize keyMix (P w) b = ub at hxb hdw2
    generalize keyMix (wadd w (P w)) a = va at hxa hd1w
    generalize keyMix (wadd w (P w)) b = vb at hxb hd1w
    revert hw1' hw2' hd12 hxa hxb hdw2 hd1w
    cases p1 <;> cases q1 <;> cases p2 <;> cases q2 <;>
      cases ua <;> cases ub <;> cases va <;> cases vb <;> decide
  refine ⟨hpart1, ?_⟩
  intro hk2 hmask
  let zeroU : Fin k → Prop := fun i => ∀ w : W, keyMix (P w) i = false
  let zeroV : Fin k → Prop := fun i => ∀ w : W, keyMix (wadd w (P w)) i = false
  have hdisj : ∀ i : Fin k, ¬ (zeroU i ∧ zeroV i) := by
    intro i ⟨hu, hv⟩
    let w := eKey.symm (wunit i)
    have hkw : keyMix w = wunit i := by rw [← heKey_eq, eKey.apply_symm_apply]
    have hsplit_w : keyMix w = wadd (keyMix (P w)) (keyMix (wadd w (P w))) := by
      rw [← heKey_eq, ← heKey_eq, ← heKey_eq, ← heKey_add]
      congr 1
      rw [wadd_comm (P w) (wadd w (P w)), wadd_cancel_right]
    have h1 := congrFun hsplit_w i
    rw [hkw] at h1
    simp [wunit, wadd, hu w, hv w] at h1
  have hpair : ∀ i : Fin k,
      (zeroU i ∧ zeroU (idx k hk (i.val + 2 * d))) ∨
      (zeroV i ∧ zeroV (idx k hk (i.val + 2 * d))) := by
    intro i
    let j : Fin k := idx k hk (i.val + k + d - 3)
    have hmj : mask j = true := by rw [hmask]
    have hp := hpart1 j hmj
    have haj : idx' (j.val + k + 3 - d) = i := by
      change idx k hk ((idx k hk (i.val + k + d - 3)).val + k + 3 - d) = i
      have h1 : (idx k hk (i.val + k + d - 3)).val + k + 3 - d =
          (idx k hk (i.val + k + d - 3)).val + (k + 3 - d) := by omega
      rw [h1, idx_val_add]
      have h2 : i.val + k + d - 3 + (k + 3 - d) = i.val + k + k := by omega
      rw [h2, idx_add_k, idx_add_k, idx_self]
    have hbj : idx' (j.val + 3 + d) = idx k hk (i.val + 2 * d) := by
      change idx k hk ((idx k hk (i.val + k + d - 3)).val + 3 + d) = idx k hk (i.val + 2 * d)
      have h1 : (idx k hk (i.val + k + d - 3)).val + 3 + d =
          (idx k hk (i.val + k + d - 3)).val + (3 + d) := by omega
      rw [h1, idx_val_add]
      have h2 : i.val + k + d - 3 + (3 + d) = (i.val + 2 * d) + k := by omega
      rw [h2, idx_add_k]
    dsimp only at hp
    rw [haj, hbj] at hp
    rcases hp with hU | hV
    · exact Or.inl ⟨fun w => (hU w).1, fun w => (hU w).2⟩
    · exact Or.inr ⟨fun w => (hV w).1, fun w => (hV w).2⟩
  rcases hpair ⟨0, hk⟩ with ⟨hU0, _⟩ | ⟨hV0, _⟩
  · left
    have hUall : ∀ i : Fin k, zeroU i :=
      step_2d_reach k d hk hk2 hd hk1 zeroU (fun i hi => by
        rcases hpair i with ⟨_, hnext⟩ | ⟨hv, _⟩
        · exact hnext
        · exact False.elim (hdisj i ⟨hi, hv⟩)) hU0
    intro w
    apply eKey.injective
    change keyMix (P w) = eKey wzero
    rw [heKey_zero]
    funext i
    exact hUall i w
  · right
    have hVall : ∀ i : Fin k, zeroV i :=
      step_2d_reach k d hk hk2 hd hk1 zeroV (fun i hi => by
        rcases hpair i with ⟨hu, _⟩ | ⟨_, hnext⟩
        · exact False.elim (hdisj i ⟨hu, hi⟩)
        · exact hnext) hV0
    intro w
    have hsub : wadd w (P w) = wzero := by
      apply eKey.injective
      rw [heKey_eq, heKey_zero]
      funext i
      exact hVall i w
    exact ((wadd_eq_zero_iff w (P w)).mp hsub).symm

end PEqualNP.Outside.L_meta_25595_aux

theorem PEqualNP.Outside.L_meta_25595 : (∀ (k d : ℕ) (hk : 0 < k), k % 3 ≠ 0 → (d = 1 ∨ d = 2) → 4 * d + 4 < k →
  let W := Fin k → Bool
  let idx := fun (n : ℕ) => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let add := fun (x y : W) (i : Fin k) => xor (x i) (y i)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (idx (i.val + k - s % k))
  let mix := fun (x : W) (i : Fin k) =>
    xor (xor (x i) (x (idx (i.val + d)))) (x (idx (i.val + k - d)))
  let step := fun (x : W) (i : Fin k) =>
    xor (x i) (!(x (idx (i.val + 1))) && x (idx (i.val + 2)))
  ∀ (s t h : ℕ) (name c₁ c₂ mask : W) (P : W → W),
    (∀ x y, P (add x y) = add (P x) (P y)) → (∀ z, P (P z) = P z) →
    let keyMix := fun (w : W) => mix (rot s w)
    let observed := fun (w : W) =>
      let initial := mix (add (rot s w) name)
      let middle := add (step initial) (add (rot t w) c₁)
      let out := add (step (mix middle)) (add (rot h w) c₂)
      (List.ofFn (fun bit : Fin k => mask bit && out bit)).foldl xor false
    (∃ left right : W → Bool, ∀ x y : W,
      observed (add (P x) (add y (P y))) = xor (left x) (right y)) →
    (∀ j : Fin k, mask j = true →
      let a := idx (j.val + k + 3 - d)
      let b := idx (j.val + 3 + d)
      (∀ w : W, keyMix (P w) a = false ∧ keyMix (P w) b = false) ∨
      (∀ w : W, keyMix (add w (P w)) a = false ∧ keyMix (add w (P w)) b = false)) ∧
    (k % 2 = 1 → mask = (fun _maskPos => true) →
      (∀ w : W, P w = (fun _zeroPos => false)) ∨ (∀ w : W, P w = w))) :=
  PEqualNP.Outside.L_meta_25595_aux.main_aux
