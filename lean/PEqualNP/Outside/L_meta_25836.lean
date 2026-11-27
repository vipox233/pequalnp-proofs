import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25836_aux

theorem z2_add_one_add_one : ∀ a : ZMod 2, a + 1 + 1 = a := by decide

theorem z2_flip_zero : ∀ a : ZMod 2, ¬ a = 0 → a + 1 = 0 := by decide

theorem z2_flip_ne : ∀ a : ZMod 2, a = 0 → ¬ a + 1 = 0 := by decide

theorem pow_cancel (N h k : ℕ) (hh : h ≤ k) (H : 2 ^ h * N = 2 ^ k) : N = 2 ^ (k - h) := by
  have e : 2 ^ k = 2 ^ h * 2 ^ (k - h) := by
    rw [← pow_add]
    congr 1
    omega
  exact Nat.eq_of_mul_eq_mul_left (by positivity) (H.trans e)

theorem cap_arith (N a b m L : ℕ) (hL : L = a + b + m) (H : 2 ^ m * N ≤ 2 ^ L) :
    N ≤ 2 ^ a * 2 ^ b := by
  subst hL
  have e : 2 ^ (a + b + m) = 2 ^ m * (2 ^ a * 2 ^ b) := by
    rw [pow_add, pow_add]
    ring
  rw [e] at H
  exact Nat.le_of_mul_le_mul_left H (by positivity)

variable {S : Type} [DecidableEq S]

def flp (p : S) (x : S → ZMod 2) : S → ZMod 2 := Function.update x p (x p + 1)

theorem flp_self (p : S) (x : S → ZMod 2) : flp p x p = x p + 1 := by
  simp [flp]

theorem flp_ne (p q : S) (x : S → ZMod 2) (h : q ≠ p) : flp p x q = x q := by
  simp [flp, h]

theorem flp_flp (p : S) (x : S → ZMod 2) : flp p (flp p x) = x := by
  funext q
  by_cases h : q = p
  · subst h
    rw [flp_self, flp_self, z2_add_one_add_one]
  · rw [flp_ne _ _ _ h, flp_ne _ _ _ h]

variable [Fintype S]

theorem halve (B : (S → ZMod 2) → Prop) (p : S) (F : (S → ZMod 2) → ZMod 2)
    (hB : ∀ x, B x → B (flp p x)) (hF : ∀ x, F (flp p x) = F x + 1) :
    Nat.card {x // B x} = 2 * Nat.card {x // B x ∧ F x = 0} := by
  classical
  have e1 : Nat.card {x // B x} = (Finset.univ.filter B).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have e2 : Nat.card {x // B x ∧ F x = 0}
      = ((Finset.univ.filter B).filter (fun x => F x = 0)).card := by
    rw [Finset.filter_filter, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have e3 : ((Finset.univ.filter B).filter (fun x => ¬ F x = 0)).card
      = ((Finset.univ.filter B).filter (fun x => F x = 0)).card := by
    refine Finset.card_bij' (fun x _ => flp p x) (fun x _ => flp p x) ?_ ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter, Finset.mem_filter] at hx ⊢
      refine ⟨⟨Finset.mem_univ _, hB x hx.1.2⟩, ?_⟩
      rw [hF]
      exact z2_flip_zero _ hx.2
    · intro x hx
      rw [Finset.mem_filter, Finset.mem_filter] at hx ⊢
      refine ⟨⟨Finset.mem_univ _, hB x hx.1.2⟩, ?_⟩
      rw [hF]
      exact z2_flip_ne _ hx.2
    · intro x _
      exact flp_flp p x
    · intro x _
      exact flp_flp p x
  have e4 := Finset.card_filter_add_card_filter_not (s := Finset.univ.filter B) (fun x => F x = 0)
  rw [e1, e2]
  omega

theorem tri (A : (S → ZMod 2) → Prop) (n : ℕ) :
    ∀ (π : ℕ → S) (E : ℕ → (S → ZMod 2) → ZMod 2),
    (∀ j, j < n → ∀ x, A x → A (flp (π j) x)) →
    (∀ j, j < n → ∀ x, E j (flp (π j) x) = E j x + 1) →
    (∀ j j', j < j' → j' < n → ∀ x, E j' (flp (π j) x) = E j' x) →
    2 ^ n * Nat.card {x // A x ∧ ∀ j, j < n → E j x = 0} = Nat.card {x // A x} := by
  induction n with
  | zero =>
    intro π E _ _ _
    rw [pow_zero, one_mul]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => by simp))
  | succ n ih =>
    intro π E hA hF hI
    have h1 := ih (fun j => π (j + 1)) (fun j => E (j + 1)) (fun j hj => hA (j + 1) (by omega))
      (fun j hj => hF (j + 1) (by omega))
      (fun j j' hjj hj' => hI (j + 1) (j' + 1) (by omega) (by omega))
    have h2 := halve (fun x => A x ∧ ∀ j, j < n → E (j + 1) x = 0) (π 0) (E 0)
      (fun x hx => ⟨hA 0 (by omega) x hx.1,
        fun j hj => (hI 0 (j + 1) (by omega) (by omega) x).trans (hx.2 j hj)⟩)
      (hF 0 (by omega))
    have h3 : Nat.card {x // A x ∧ ∀ j, j < n + 1 → E j x = 0}
        = Nat.card {x // (A x ∧ ∀ j, j < n → E (j + 1) x = 0) ∧ E 0 x = 0} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight (fun x => ?_))
      constructor
      · intro hx
        exact ⟨⟨hx.1, fun j hj => hx.2 (j + 1) (by omega)⟩, hx.2 0 (by omega)⟩
      · intro hx
        refine ⟨hx.1.1, fun j hj => ?_⟩
        rcases j with _ | j
        · exact hx.2
        · exact hx.1.2 j (by omega)
    rw [h3, pow_succ, mul_assoc, ← h2]
    exact h1

theorem card_imp {X : Type} [Finite X] (P Q : X → Prop) (hPQ : ∀ x, P x → Q x) :
    Nat.card {x // P x} ≤ Nat.card {x // Q x} :=
  Nat.card_le_card_of_injective (Subtype.map id hPQ) (Subtype.map_injective hPQ Function.injective_id)

theorem margin {V X : Type} [Fintype V] [Fintype X] (R : X → Prop) (C : V → X → Prop) (N : ℕ)
    (hC : ∀ x, Nat.card {v // C v x} = N) :
    ∑ v : V, Nat.card {x // R x ∧ C v x} = Nat.card {x // R x} * N := by
  classical
  have e1 : ∀ v, Nat.card {x // R x ∧ C v x} = ∑ x : X, if R x ∧ C v x then 1 else 0 := by
    intro v
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  have e2 : ∀ x, (∑ v : V, if R x ∧ C v x then 1 else 0) = if R x then N else 0 := by
    intro x
    by_cases hx : R x
    · simp only [hx, true_and, ite_true]
      rw [← Finset.card_filter, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, hC]
    · simp [hx]
  rw [Finset.sum_congr rfl (fun v _ => e1 v), Finset.sum_comm, Finset.sum_congr rfl (fun x _ => e2 x),
    Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  split_ifs <;> simp

theorem margin' {V X : Type} [Fintype V] [Fintype X] (R : X → Prop) (C : V → X → Prop) (N : ℕ)
    (hC : ∀ x, Nat.card {v // C v x} = N) :
    ∑ v : V, Nat.card {x // C v x ∧ R x} = Nat.card {x // R x} * N := by
  rw [← margin R C N hC]
  exact Finset.sum_congr rfl
    (fun v _ => Nat.card_congr (Equiv.subtypeEquivRight (fun x => and_comm)))

variable {k : ℕ}

def turn (d : ℕ) (w : ZMod k → ZMod 2) : ZMod k → ZMod 2 := fun i => w (i - (d : ZMod k))

def mix (d : ℕ) (w : ZMod k → ZMod 2) : ZMod k → ZMod 2 :=
  fun i => w (i - (d : ZMod k)) + w i + w (i + (d : ZMod k))

def chi (w : ZMod k → ZMod 2) : ZMod k → ZMod 2 := fun i => w i + (1 + w (i + 1)) * w (i + 2)

def Win (h : ℕ) (G : ZMod k → ZMod 2) : Prop := ∀ i : ZMod k, k - h ≤ i.val → G i = 0

def rowOut (r : ℕ) (cr : ℕ → ZMod k → ZMod 2) (u key : ZMod k → ZMod 2) : ZMod k → ZMod 2 :=
  (List.range r).foldl (fun acc t => chi (mix 1 acc) + turn (2 * t) key + cr (t + 1)) (turn 1 key + u)

def colOut (r : ℕ) (cc : ℕ → ZMod k → ZMod 2) (v key : ZMod k → ZMod 2) : ZMod k → ZMod 2 :=
  (List.range r).foldl (fun acc t => chi (mix 2 acc) + turn (3 * (t + 1) + 1) key + cc (t + 1))
    (turn 3 key + v)

def rowSt (cr : ℕ → ZMod k → ZMod 2) (u key : ZMod k → ZMod 2) : ℕ → ZMod k → ZMod 2
  | 0 => turn 1 key + u
  | t + 1 => chi (mix 1 (rowSt cr u key t)) + turn (2 * t) key + cr (t + 1)

def colSt (cc : ℕ → ZMod k → ZMod 2) (v key : ZMod k → ZMod 2) : ℕ → ZMod k → ZMod 2
  | 0 => turn 3 key + v
  | t + 1 => chi (mix 2 (colSt cc v key t)) + turn (3 * (t + 1) + 1) key + cc (t + 1)

theorem rowOut_eq (r : ℕ) (cr : ℕ → ZMod k → ZMod 2) (u key : ZMod k → ZMod 2) :
    rowOut r cr u key = rowSt cr u key r := by
  induction r with
  | zero => rfl
  | succ t ih =>
    rw [rowOut] at ih ⊢
    rw [List.range_succ, List.foldl_append, ih]
    rfl

theorem colOut_eq (r : ℕ) (cc : ℕ → ZMod k → ZMod 2) (v key : ZMod k → ZMod 2) :
    colOut r cc v key = colSt cc v key r := by
  induction r with
  | zero => rfl
  | succ t ih =>
    rw [colOut] at ih ⊢
    rw [List.range_succ, List.foldl_append, ih]
    rfl

theorem natCast_ne (a b : ℕ) (h1 : a < b) (h2 : b < a + k) : ((a : ℕ) : ZMod k) ≠ ((b : ℕ) : ZMod k) := by
  intro h
  rw [ZMod.natCast_eq_natCast_iff] at h
  have h3 := (Nat.modEq_iff_dvd' h1.le).mp h
  have h4 := Nat.le_of_dvd (by omega) h3
  omega

theorem nat_ne_zero (n : ℕ) (h1 : 0 < n) (h2 : n < k) : ((n : ℕ) : ZMod k) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have h4 := Nat.le_of_dvd h1 h
  omega

def Dep (F : (ZMod k → ZMod 2) → ZMod k → ZMod 2) (a w : ℕ) : Prop :=
  ∀ (i p : ZMod k), (∀ δ : ℕ, δ < w → p ≠ i - (a : ZMod k) + (δ : ZMod k)) →
    ∀ x, F (flp p x) i = F x i

def Piv (F : (ZMod k → ZMod 2) → ZMod k → ZMod 2) (a : ℕ) : Prop :=
  ∀ (i : ZMod k) (x : ZMod k → ZMod 2), F (flp (i - (a : ZMod k)) x) i = F x i + 1

theorem dep_const (c : ZMod k → ZMod 2) (a w : ℕ) : Dep (fun _ => c) a w := fun _ _ _ _ => rfl

theorem dep_weaken {F : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {a w : ℕ} (hF : Dep F a w)
    (a' w' : ℕ) (h1 : a ≤ a') (h2 : w + (a' - a) ≤ w') : Dep F a' w' := by
  intro i p hp x
  refine hF i p ?_ x
  intro δ hδ
  have h3 := hp (δ + (a' - a)) (by omega)
  have e : i - (a' : ZMod k) + ((δ + (a' - a) : ℕ) : ZMod k) = i - (a : ZMod k) + (δ : ZMod k) := by
    rw [Nat.cast_add, Nat.cast_sub h1]
    ring
  rwa [e] at h3

theorem dep_add {F G : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {a w : ℕ} (hF : Dep F a w)
    (hG : Dep G a w) : Dep (fun x => F x + G x) a w := by
  intro i p hp x
  show F (flp p x) i + G (flp p x) i = F x i + G x i
  rw [hF i p hp x, hG i p hp x]

theorem dep_turn (d : ℕ) : Dep (fun x : ZMod k → ZMod 2 => turn d x) d 1 := by
  intro i p hp x
  have h := hp 0 (by omega)
  rw [Nat.cast_zero, add_zero] at h
  exact flp_ne p _ x (Ne.symm h)

theorem piv_turn (d : ℕ) : Piv (fun x : ZMod k → ZMod 2 => turn d x) d :=
  fun _ x => flp_self _ x

theorem dep_id : Dep (fun x : ZMod k → ZMod 2 => x) 0 1 := by
  intro i p hp x
  have h := hp 0 (by omega)
  rw [Nat.cast_zero, sub_zero, add_zero] at h
  exact flp_ne p _ x (Ne.symm h)

theorem piv_id : Piv (fun x : ZMod k → ZMod 2 => x) 0 := by
  intro i x
  rw [Nat.cast_zero, sub_zero]
  exact flp_self i x

theorem phi_congr (d : ℕ) (s s' : ZMod k → ZMod 2) (i : ZMod k)
    (hs : ∀ ε : ℕ, ε ≤ 2 * d + 2 → s (i - (d : ZMod k) + (ε : ZMod k)) = s' (i - (d : ZMod k) + (ε : ZMod k))) :
    chi (mix d s) i = chi (mix d s') i := by
  have e0 : s (i - (d : ZMod k)) = s' (i - (d : ZMod k)) := by
    have h := hs 0 (by omega)
    rwa [Nat.cast_zero, add_zero] at h
  have e1 : s i = s' i := by
    have h := hs d (by omega)
    rwa [sub_add_cancel] at h
  have e2 : s (i + (d : ZMod k)) = s' (i + (d : ZMod k)) := by
    have h := hs (2 * d) (by omega)
    have e : i - (d : ZMod k) + ((2 * d : ℕ) : ZMod k) = i + (d : ZMod k) := by push_cast; ring
    rwa [e] at h
  have e3 : s (i + 1 - (d : ZMod k)) = s' (i + 1 - (d : ZMod k)) := by
    have h := hs 1 (by omega)
    have e : i - (d : ZMod k) + ((1 : ℕ) : ZMod k) = i + 1 - (d : ZMod k) := by push_cast; ring
    rwa [e] at h
  have e4 : s (i + 1) = s' (i + 1) := by
    have h := hs (d + 1) (by omega)
    have e : i - (d : ZMod k) + ((d + 1 : ℕ) : ZMod k) = i + 1 := by push_cast; ring
    rwa [e] at h
  have e5 : s (i + 1 + (d : ZMod k)) = s' (i + 1 + (d : ZMod k)) := by
    have h := hs (2 * d + 1) (by omega)
    have e : i - (d : ZMod k) + ((2 * d + 1 : ℕ) : ZMod k) = i + 1 + (d : ZMod k) := by push_cast; ring
    rwa [e] at h
  have e6 : s (i + 2 - (d : ZMod k)) = s' (i + 2 - (d : ZMod k)) := by
    have h := hs 2 (by omega)
    have e : i - (d : ZMod k) + ((2 : ℕ) : ZMod k) = i + 2 - (d : ZMod k) := by push_cast; ring
    rwa [e] at h
  have e7 : s (i + 2) = s' (i + 2) := by
    have h := hs (d + 2) (by omega)
    have e : i - (d : ZMod k) + ((d + 2 : ℕ) : ZMod k) = i + 2 := by push_cast; ring
    rwa [e] at h
  have e8 : s (i + 2 + (d : ZMod k)) = s' (i + 2 + (d : ZMod k)) := by
    have h := hs (2 * d + 2) (by omega)
    have e : i - (d : ZMod k) + ((2 * d + 2 : ℕ) : ZMod k) = i + 2 + (d : ZMod k) := by push_cast; ring
    rwa [e] at h
  show s (i - (d : ZMod k)) + s i + s (i + (d : ZMod k))
      + (1 + (s (i + 1 - (d : ZMod k)) + s (i + 1) + s (i + 1 + (d : ZMod k))))
        * (s (i + 2 - (d : ZMod k)) + s (i + 2) + s (i + 2 + (d : ZMod k)))
    = s' (i - (d : ZMod k)) + s' i + s' (i + (d : ZMod k))
      + (1 + (s' (i + 1 - (d : ZMod k)) + s' (i + 1) + s' (i + 1 + (d : ZMod k))))
        * (s' (i + 2 - (d : ZMod k)) + s' (i + 2) + s' (i + 2 + (d : ZMod k)))
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8]

theorem phi_flip (d : ℕ) (hd : 1 ≤ d) (s s' : ZMod k → ZMod 2) (i : ZMod k)
    (h0 : s (i - (d : ZMod k)) = s' (i - (d : ZMod k)) + 1)
    (hs : ∀ ε : ℕ, 1 ≤ ε → ε ≤ 2 * d + 2 →
      s (i - (d : ZMod k) + (ε : ZMod k)) = s' (i - (d : ZMod k) + (ε : ZMod k))) :
    chi (mix d s) i = chi (mix d s') i + 1 := by
  have e1 : s i = s' i := by
    have h := hs d hd (by omega)
    rwa [sub_add_cancel] at h
  have e2 : s (i + (d : ZMod k)) = s' (i + (d : ZMod k)) := by
    have h := hs (2 * d) (by omega) (by omega)
    have e : i - (d : ZMod k) + ((2 * d : ℕ) : ZMod k) = i + (d : ZMod k) := by push_cast; ring
    rwa [e] at h
  have e3 : s (i + 1 - (d : ZMod k)) = s' (i + 1 - (d : ZMod k)) := by
    have h := hs 1 (by omega) (by omega)
    have e : i - (d : ZMod k) + ((1 : ℕ) : ZMod k) = i + 1 - (d : ZMod k) := by push_cast; ring
    rwa [e] at h
  have e4 : s (i + 1) = s' (i + 1) := by
    have h := hs (d + 1) (by omega) (by omega)
    have e : i - (d : ZMod k) + ((d + 1 : ℕ) : ZMod k) = i + 1 := by push_cast; ring
    rwa [e] at h
  have e5 : s (i + 1 + (d : ZMod k)) = s' (i + 1 + (d : ZMod k)) := by
    have h := hs (2 * d + 1) (by omega) (by omega)
    have e : i - (d : ZMod k) + ((2 * d + 1 : ℕ) : ZMod k) = i + 1 + (d : ZMod k) := by push_cast; ring
    rwa [e] at h
  have e6 : s (i + 2 - (d : ZMod k)) = s' (i + 2 - (d : ZMod k)) := by
    have h := hs 2 (by omega) (by omega)
    have e : i - (d : ZMod k) + ((2 : ℕ) : ZMod k) = i + 2 - (d : ZMod k) := by push_cast; ring
    rwa [e] at h
  have e7 : s (i + 2) = s' (i + 2) := by
    have h := hs (d + 2) (by omega) (by omega)
    have e : i - (d : ZMod k) + ((d + 2 : ℕ) : ZMod k) = i + 2 := by push_cast; ring
    rwa [e] at h
  have e8 : s (i + 2 + (d : ZMod k)) = s' (i + 2 + (d : ZMod k)) := by
    have h := hs (2 * d + 2) (by omega) (by omega)
    have e : i - (d : ZMod k) + ((2 * d + 2 : ℕ) : ZMod k) = i + 2 + (d : ZMod k) := by push_cast; ring
    rwa [e] at h
  show s (i - (d : ZMod k)) + s i + s (i + (d : ZMod k))
      + (1 + (s (i + 1 - (d : ZMod k)) + s (i + 1) + s (i + 1 + (d : ZMod k))))
        * (s (i + 2 - (d : ZMod k)) + s (i + 2) + s (i + 2 + (d : ZMod k)))
    = s' (i - (d : ZMod k)) + s' i + s' (i + (d : ZMod k))
      + (1 + (s' (i + 1 - (d : ZMod k)) + s' (i + 1) + s' (i + 1 + (d : ZMod k))))
        * (s' (i + 2 - (d : ZMod k)) + s' (i + 2) + s' (i + 2 + (d : ZMod k))) + 1
  rw [h0, e1, e2, e3, e4, e5, e6, e7, e8]
  ring

theorem dep_phi (d : ℕ) {F : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {a w : ℕ} (hF : Dep F a w) :
    Dep (fun x => chi (mix d (F x))) (a + d) (w + 2 * d + 2) := by
  intro i p hp x
  refine phi_congr d _ _ i (fun ε hε => hF _ p (fun δ hδ heq => hp (ε + δ) (by omega) ?_) x)
  rw [heq]
  push_cast
  ring

theorem piv_phi (d : ℕ) (hd : 1 ≤ d) {F : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {a w : ℕ}
    (hk : w + 2 * d + 1 < k) (hF : Dep F a w) (hP : Piv F a) :
    Piv (fun x => chi (mix d (F x))) (a + d) := by
  intro i x
  refine phi_flip d hd _ _ i ?_ ?_
  · have h := hP (i - (d : ZMod k)) x
    have e : i - ((a + d : ℕ) : ZMod k) = i - (d : ZMod k) - (a : ZMod k) := by push_cast; ring
    rw [e]
    exact h
  · intro ε h1 h2
    refine hF _ _ (fun δ hδ heq => ?_) x
    have h0 : ((ε + δ : ℕ) : ZMod k) = 0 := by
      push_cast at heq ⊢
      linear_combination -heq
    exact nat_ne_zero (ε + δ) (by omega) (by omega) h0

theorem piv_add_left {F G : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {a : ℕ} (hF : Piv F a)
    (hG : ∀ (i : ZMod k) (x : ZMod k → ZMod 2), G (flp (i - (a : ZMod k)) x) i = G x i) :
    Piv (fun x => F x + G x) a := by
  intro i x
  show F (flp (i - (a : ZMod k)) x) i + G (flp (i - (a : ZMod k)) x) i = F x i + G x i + 1
  rw [hF i x, hG i x]
  ring

theorem piv_add_right {F G : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {a : ℕ}
    (hF : ∀ (i : ZMod k) (x : ZMod k → ZMod 2), F (flp (i - (a : ZMod k)) x) i = F x i)
    (hG : Piv G a) : Piv (fun x => F x + G x) a := by
  intro i x
  show F (flp (i - (a : ZMod k)) x) i + G (flp (i - (a : ZMod k)) x) i = F x i + G x i + 1
  rw [hF i x, hG i x]
  ring

theorem dep_left {G : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {a' w' : ℕ} (hG : Dep G a' w')
    (a : ℕ) (h1 : a' < a) (h2 : w' + a - a' ≤ k) (i : ZMod k) (x : ZMod k → ZMod 2) :
    G (flp (i - (a : ZMod k)) x) i = G x i := by
  refine hG _ _ (fun δ hδ heq => ?_) x
  have h0 : ((δ + (a - a') : ℕ) : ZMod k) = 0 := by
    rw [Nat.cast_add, Nat.cast_sub h1.le]
    linear_combination -heq
  exact nat_ne_zero _ (by omega) (by omega) h0

theorem row_name_dep (cr : ℕ → ZMod k → ZMod 2) (key : ZMod k → ZMod 2) (t : ℕ) :
    Dep (fun u => rowSt cr u key t) t (4 * t + 1) := by
  induction t with
  | zero => exact dep_add (dep_const (turn 1 key) 0 1) dep_id
  | succ t ih =>
    exact dep_weaken (dep_add (dep_add (dep_phi 1 ih) (dep_const (turn (2 * t) key) _ _))
      (dep_const (cr (t + 1)) _ _)) _ _ (by omega) (by omega)

theorem row_name_piv (cr : ℕ → ZMod k → ZMod 2) (key : ZMod k → ZMod 2) (t : ℕ) (hk : 4 * t < k) :
    Piv (fun u => rowSt cr u key t) t := by
  induction t with
  | zero => exact piv_add_right (fun _ _ => rfl) piv_id
  | succ t ih =>
    exact piv_add_left (piv_add_left
      (piv_phi 1 le_rfl (by omega) (row_name_dep cr key t) (ih (by omega))) (fun _ _ => rfl))
      (fun _ _ => rfl)

theorem col_name_dep (cc : ℕ → ZMod k → ZMod 2) (key : ZMod k → ZMod 2) (t : ℕ) :
    Dep (fun v => colSt cc v key t) (2 * t) (6 * t + 1) := by
  induction t with
  | zero => exact dep_add (dep_const (turn 3 key) 0 1) dep_id
  | succ t ih =>
    exact dep_weaken (dep_add (dep_add (dep_phi 2 ih)
      (dep_const (turn (3 * (t + 1) + 1) key) _ _)) (dep_const (cc (t + 1)) _ _)) _ _
      (by omega) (by omega)

theorem col_name_piv (cc : ℕ → ZMod k → ZMod 2) (key : ZMod k → ZMod 2) (t : ℕ) (hk : 6 * t < k) :
    Piv (fun v => colSt cc v key t) (2 * t) := by
  induction t with
  | zero => exact piv_add_right (fun _ _ => rfl) piv_id
  | succ t ih =>
    exact piv_add_left (piv_add_left
      (piv_phi 2 (by omega) (by omega) (col_name_dep cc key t) (ih (by omega))) (fun _ _ => rfl))
      (fun _ _ => rfl)

theorem row_key_dep (cr : ℕ → ZMod k → ZMod 2) (u : ZMod k → ZMod 2) (t : ℕ) :
    Dep (fun key => rowSt cr u key t) (max (t + 1) (2 * t - 2)) (max (t + 1) (2 * t - 2) + 3 * t) := by
  induction t with
  | zero =>
    exact dep_weaken (dep_add (dep_turn 1) (dep_const u 1 1)) _ _ (by omega) (by omega)
  | succ t ih =>
    have hA := dep_weaken (dep_phi 1 ih) (max (t + 1 + 1) (2 * (t + 1) - 2))
      (max (t + 1 + 1) (2 * (t + 1) - 2) + 3 * (t + 1)) (by omega) (by omega)
    have hB := dep_weaken (dep_turn (k := k) (2 * t)) (max (t + 1 + 1) (2 * (t + 1) - 2))
      (max (t + 1 + 1) (2 * (t + 1) - 2) + 3 * (t + 1)) (by omega) (by omega)
    exact dep_add (dep_add hA hB) (dep_const (cr (t + 1)) _ _)

theorem col_key_dep (cc : ℕ → ZMod k → ZMod 2) (v : ZMod k → ZMod 2) (t : ℕ) :
    Dep (fun key => colSt cc v key t) (max (2 * t + 3) (3 * t + 1))
      (max (2 * t + 3) (3 * t + 1) + 4 * t - 2) := by
  induction t with
  | zero =>
    exact dep_weaken (dep_add (dep_turn 3) (dep_const v 3 1)) _ _ (by omega) (by omega)
  | succ t ih =>
    have hA := dep_weaken (dep_phi 2 ih) (max (2 * (t + 1) + 3) (3 * (t + 1) + 1))
      (max (2 * (t + 1) + 3) (3 * (t + 1) + 1) + 4 * (t + 1) - 2) (by omega) (by omega)
    have hB := dep_weaken (dep_turn (k := k) (3 * (t + 1) + 1)) (max (2 * (t + 1) + 3) (3 * (t + 1) + 1))
      (max (2 * (t + 1) + 3) (3 * (t + 1) + 1) + 4 * (t + 1) - 2) (by omega) (by omega)
    exact dep_add (dep_add hA hB) (dep_const (cc (t + 1)) _ _)

theorem row_key_piv_big (cr : ℕ → ZMod k → ZMod 2) (u : ZMod k → ZMod 2) (t : ℕ) (ht : 3 ≤ t)
    (hk : 5 * t + 3 ≤ k) : Piv (fun key => rowSt cr u key (t + 1)) (2 * t) := by
  have hD := dep_phi 1 (row_key_dep cr u t)
  have hL := dep_left hD (2 * t) (by omega) (by omega)
  exact piv_add_left (piv_add_right hL (piv_turn (2 * t))) (fun _ _ => rfl)

theorem col_key_piv_big (cc : ℕ → ZMod k → ZMod 2) (v : ZMod k → ZMod 2) (t : ℕ) (ht : 2 ≤ t)
    (hk : 7 * t + 6 ≤ k) : Piv (fun key => colSt cc v key (t + 1)) (3 * (t + 1) + 1) := by
  have hD := dep_phi 2 (col_key_dep cc v t)
  have hL := dep_left hD (3 * (t + 1) + 1) (by omega) (by omega)
  exact piv_add_left (piv_add_right hL (piv_turn (3 * (t + 1) + 1))) (fun _ _ => rfl)

theorem row_key_piv_one (cr : ℕ → ZMod k → ZMod 2) (u : ZMod k → ZMod 2) (hk : 4 < k) :
    Piv (fun key => rowSt cr u key 1) 2 := by
  have hP0 : Piv (fun key : ZMod k → ZMod 2 => turn 1 key + u) 1 :=
    piv_add_left (piv_turn 1) (fun _ _ => rfl)
  have hD0 : Dep (fun key : ZMod k → ZMod 2 => turn 1 key + u) 1 1 :=
    dep_add (dep_turn 1) (dep_const u 1 1)
  have hP := piv_phi 1 le_rfl (by omega) hD0 hP0
  have hL := dep_left (dep_turn (k := k) (2 * 0)) 2 (by omega) (by omega)
  exact piv_add_left (piv_add_left hP hL) (fun _ _ => rfl)

theorem col_key_piv_one (cc : ℕ → ZMod k → ZMod 2) (v : ZMod k → ZMod 2) (hk : 6 < k) :
    Piv (fun key => colSt cc v key 1) 5 := by
  have hP0 : Piv (fun key : ZMod k → ZMod 2 => turn 3 key + v) 3 :=
    piv_add_left (piv_turn 3) (fun _ _ => rfl)
  have hD0 : Dep (fun key : ZMod k → ZMod 2 => turn 3 key + v) 3 1 :=
    dep_add (dep_turn 3) (dep_const v 3 1)
  have hP := piv_phi 2 (by omega) (by omega) hD0 hP0
  have hL := dep_left (dep_turn (k := k) (3 * (0 + 1) + 1)) 5 (by omega) (by omega)
  exact piv_add_left (piv_add_left hP hL) (fun _ _ => rfl)

variable [NeZero k]

theorem win_iff (h : ℕ) (hh : h ≤ k) (G : ZMod k → ZMod 2) :
    Win h G ↔ ∀ c, c < h → G ((k - h + c : ℕ) : ZMod k) = 0 := by
  constructor
  · intro H c hc
    refine H _ ?_
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro H i hi
    have h1 := H (i.val - (k - h)) (by have := ZMod.val_lt i; omega)
    have e : k - h + (i.val - (k - h)) = i.val := by omega
    rwa [e, ZMod.natCast_zmod_val] at h1

theorem win_indep {F : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {a w : ℕ} (hF : Dep F a w) (h q : ℕ)
    (h1 : q + a < k - h) (h2 : w ≤ q + a + 1) (x : ZMod k → ZMod 2) (hx : Win h (F x)) :
    Win h (F (flp ((q : ℕ) : ZMod k) x)) := by
  intro i hi
  refine (hF i _ (fun δ hδ heq => ?_) x).trans (hx i hi)
  have hv : ((i.val : ℕ) : ZMod k) = i := ZMod.natCast_zmod_val i
  have e : ((q + a : ℕ) : ZMod k) = ((i.val + δ : ℕ) : ZMod k) := by
    rw [Nat.cast_add, Nat.cast_add, hv, heq]
    ring
  have h3 := ZMod.val_lt i
  exact natCast_ne (q + a) (i.val + δ) (by omega) (by omega) e

theorem win_tri {F : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {a w : ℕ} (hF : Dep F a w) (hP : Piv F a)
    (A : (ZMod k → ZMod 2) → Prop) (h m : ℕ) (ha : a ≤ k - h)
    (hw : w + m ≤ k + 1)
    (hA : ∀ c, c < m → ∀ x, A x → A (flp ((k - h + c - a : ℕ) : ZMod k) x)) :
    2 ^ m * Nat.card {x // A x ∧ ∀ c, c < m → F x ((k - h + c : ℕ) : ZMod k) = 0}
      = Nat.card {x // A x} := by
  refine tri A m (fun c => ((k - h + c - a : ℕ) : ZMod k))
    (fun c x => F x ((k - h + c : ℕ) : ZMod k)) hA ?_ ?_
  · intro c _ x
    have h1 := hP ((k - h + c : ℕ) : ZMod k) x
    have e : ((k - h + c : ℕ) : ZMod k) - (a : ZMod k) = ((k - h + c - a : ℕ) : ZMod k) := by
      rw [Nat.cast_sub (by omega)]
    rw [e] at h1
    exact h1
  · intro c c' hcc hc' x
    refine hF _ _ (fun δ hδ heq => ?_) x
    have e : ((k - h + c : ℕ) : ZMod k) = ((k - h + c' + δ : ℕ) : ZMod k) := by
      have e1 : ((k - h + c - a : ℕ) : ZMod k) = ((k - h + c : ℕ) : ZMod k) - (a : ZMod k) := by
        rw [Nat.cast_sub (by omega)]
      rw [e1] at heq
      rw [Nat.cast_add (k - h + c') δ]
      linear_combination heq
    exact natCast_ne _ _ (by omega) (by omega) e

theorem card_all : Nat.card {_x : ZMod k → ZMod 2 // True} = 2 ^ k := by
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun _ => trivial)), Nat.card_eq_fintype_card]
  simp [ZMod.card]

theorem win_card {F : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {a w : ℕ} (hF : Dep F a w) (hP : Piv F a)
    (h : ℕ) (hh : h ≤ k) (ha : a ≤ k - h) (hw : w + h ≤ k + 1) :
    Nat.card {x // Win h (F x)} = 2 ^ (k - h) := by
  have h1 := win_tri hF hP (fun _ => True) h h ha hw (fun _ _ _ _ => trivial)
  have e : Nat.card {x // Win h (F x)}
      = Nat.card {x : ZMod k → ZMod 2 // True ∧ ∀ c, c < h → F x ((k - h + c : ℕ) : ZMod k) = 0} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [win_iff h hh, true_and]))
  rw [card_all] at h1
  rw [e]
  exact pow_cancel _ h k hh h1

theorem cap {Fr Fc : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {ar wr ac wc : ℕ}
    (hRd : Dep Fr ar wr) (hRp : Piv Fr ar) (hCd : Dep Fc ac wc) (hCp : Piv Fc ac)
    (h m : ℕ) (hm : m ≤ h) (hh : h ≤ k) (har : ar ≤ k - h) (hac : ac ≤ k - h)
    (hwr : wr + h ≤ k + 1) (hwc : wc + h ≤ k + 1) (h1 : ar + m ≤ ac)
    (h2 : ac + wr ≤ k - h + ar + 1) :
    2 ^ m * Nat.card {x // Win h (Fr x) ∧ Win h (Fc x)} ≤ 2 ^ (k - h) := by
  have h3 := win_tri hCd hCp (fun x => Win h (Fr x)) h m hac (by omega)
    (fun c hc x hx => win_indep hRd h (k - h + c - ac) (by omega) (by omega) x hx)
  rw [win_card hRd hRp h hh har hwr] at h3
  rw [← h3]
  refine Nat.mul_le_mul_left _ (card_imp _ _ (fun x hx => ⟨hx.1, fun c hc => ?_⟩))
  exact (win_iff h hh _).mp hx.2 c (by omega)

theorem passive {Fr Fc : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {ar wr ac wc : ℕ}
    (hRd : Dep Fr ar wr) (hCd : Dep Fc ac wc) (h s : ℕ) (hs : s ≤ k - h) (hac : ac ≤ s)
    (har : ar ≤ ac) (h1 : wr + ac ≤ s + ar + 1) (h2 : wc ≤ s + 1) :
    2 ^ (k - h - s) ∣ Nat.card {x // Win h (Fr x) ∧ Win h (Fc x)} := by
  have h3 := tri (fun x => Win h (Fr x) ∧ Win h (Fc x)) (k - h - s)
    (fun j => ((s - ac + j : ℕ) : ZMod k)) (fun j x => x ((s - ac + j : ℕ) : ZMod k))
    (fun j hj x hx => ⟨win_indep hRd h (s - ac + j) (by omega) (by omega) x hx.1,
      win_indep hCd h (s - ac + j) (by omega) (by omega) x hx.2⟩)
    (fun j _ x => flp_self _ x)
    (fun j j' hjj hj' x => flp_ne _ _ x (natCast_ne _ _ (by omega) (by omega)).symm)
  exact Dvd.intro _ h3

theorem core (R C : (ZMod k → ZMod 2) → (ZMod k → ZMod 2) → ZMod k → ZMod 2)
    (an wn bn wb ar wr ac wc h m s sd : ℕ)
    (hRn : ∀ key, Dep (fun u => R u key) an wn) (hRnP : ∀ key, Piv (fun u => R u key) an)
    (hCn : ∀ key, Dep (fun v => C v key) bn wb) (hCnP : ∀ key, Piv (fun v => C v key) bn)
    (hRk : ∀ u, Dep (fun key => R u key) ar wr) (hRkP : ∀ u, Piv (fun key => R u key) ar)
    (hCk : ∀ v, Dep (fun key => C v key) ac wc) (hCkP : ∀ v, Piv (fun key => C v key) ac)
    (hh : h ≤ k) (han : an ≤ k - h) (hwn : wn + h ≤ k + 1) (hbn : bn ≤ k - h)
    (hwb : wb + h ≤ k + 1) (har : ar ≤ k - h) (hwr : wr + h ≤ k + 1) (hac : ac ≤ k - h)
    (hwc : wc + h ≤ k + 1) (hm : m ≤ h) (h1 : ar + m ≤ ac) (h2 : ac + wr ≤ k - h + ar + 1)
    (hs : s ≤ k - h) (hacs : ac ≤ s) (h3 : wr + ac ≤ s + ar + 1) (h4 : wc ≤ s + 1)
    (h5 : k - h = k - h - s + sd + m) :
    (∀ u v : ZMod k → ZMod 2,
      2 ^ (k - h - s) ∣ Nat.card {x : ZMod k → ZMod 2 // Win h (R u x) ∧ Win h (C v x)} ∧
        Nat.card {x : ZMod k → ZMod 2 // Win h (R u x) ∧ Win h (C v x)}
          ≤ 2 ^ (k - h - s) * 2 ^ sd) ∧
      (∀ u : ZMod k → ZMod 2, (∑ v : ZMod k → ZMod 2,
        Nat.card {x : ZMod k → ZMod 2 // Win h (R u x) ∧ Win h (C v x)}) = 2 ^ (2 * (k - h))) ∧
      (∀ v : ZMod k → ZMod 2, (∑ u : ZMod k → ZMod 2,
        Nat.card {x : ZMod k → ZMod 2 // Win h (R u x) ∧ Win h (C v x)}) = 2 ^ (2 * (k - h))) := by
  have e : 2 ^ (2 * (k - h)) = 2 ^ (k - h) * 2 ^ (k - h) := by rw [← pow_add, two_mul]
  refine ⟨fun u v => ⟨?_, ?_⟩, fun u => ?_, fun v => ?_⟩
  · exact passive (hRk u) (hCk v) h s hs hacs (by omega) h3 h4
  · exact cap_arith _ _ _ m _ h5
      (cap (hRk u) (hRkP u) (hCk v) (hCkP v) h m hm hh har hac hwr hwc h1 h2)
  · rw [margin (fun x => Win h (R u x)) (fun v x => Win h (C v x)) (2 ^ (k - h))
      (fun x => win_card (hCn x) (hCnP x) h hh hbn hwb), win_card (hRk u) (hRkP u) h hh har hwr, e]
  · rw [margin' (fun x => Win h (C v x)) (fun u x => Win h (R u x)) (2 ^ (k - h))
      (fun x => win_card (hRn x) (hRnP x) h hh han hwn), win_card (hCk v) (hCkP v) h hh hac hwc, e]

theorem main1 (h : ℕ) (hh : 5 ≤ h) (hk : h + 7 ≤ k) (cr cc : ℕ → ZMod k → ZMod 2) :
    (∀ u v : ZMod k → ZMod 2,
      2 ^ (k - h - 7) ∣
          Nat.card {x : ZMod k → ZMod 2 // Win h (rowSt cr u x 1) ∧ Win h (colSt cc v x 1)} ∧
        Nat.card {x : ZMod k → ZMod 2 // Win h (rowSt cr u x 1) ∧ Win h (colSt cc v x 1)}
          ≤ 2 ^ (k - h - 7) * 2 ^ 4) ∧
      (∀ u : ZMod k → ZMod 2, (∑ v : ZMod k → ZMod 2,
        Nat.card {x : ZMod k → ZMod 2 // Win h (rowSt cr u x 1) ∧ Win h (colSt cc v x 1)})
          = 2 ^ (2 * (k - h))) ∧
      (∀ v : ZMod k → ZMod 2, (∑ u : ZMod k → ZMod 2,
        Nat.card {x : ZMod k → ZMod 2 // Win h (rowSt cr u x 1) ∧ Win h (colSt cc v x 1)})
          = 2 ^ (2 * (k - h))) :=
  core (fun u key => rowSt cr u key 1) (fun v key => colSt cc v key 1)
    1 5 2 7 2 5 5 7 h 3 7 4
    (fun key => row_name_dep cr key 1) (fun key => row_name_piv cr key 1 (by omega))
    (fun key => col_name_dep cc key 1) (fun key => col_name_piv cc key 1 (by omega))
    (fun u => dep_weaken (row_key_dep cr u 1) 2 5 (by omega) (by omega))
    (fun u => row_key_piv_one cr u (by omega))
    (fun v => dep_weaken (col_key_dep cc v 1) 5 7 (by omega) (by omega))
    (fun v => col_key_piv_one cc v (by omega))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)

theorem main4 (h t : ℕ) (ht : 3 ≤ t) (hh : t + 4 ≤ h) (hk : h + (7 * (t + 1) - 2) ≤ k)
    (cr cc : ℕ → ZMod k → ZMod 2) :
    (∀ u v : ZMod k → ZMod 2,
      2 ^ (k - h - (7 * (t + 1) - 2)) ∣
          Nat.card {x : ZMod k → ZMod 2 //
            Win h (rowSt cr u x (t + 1)) ∧ Win h (colSt cc v x (t + 1))} ∧
        Nat.card {x : ZMod k → ZMod 2 //
            Win h (rowSt cr u x (t + 1)) ∧ Win h (colSt cc v x (t + 1))}
          ≤ 2 ^ (k - h - (7 * (t + 1) - 2)) * 2 ^ (6 * (t + 1) - 5)) ∧
      (∀ u : ZMod k → ZMod 2, (∑ v : ZMod k → ZMod 2,
        Nat.card {x : ZMod k → ZMod 2 //
            Win h (rowSt cr u x (t + 1)) ∧ Win h (colSt cc v x (t + 1))})
          = 2 ^ (2 * (k - h))) ∧
      (∀ v : ZMod k → ZMod 2, (∑ u : ZMod k → ZMod 2,
        Nat.card {x : ZMod k → ZMod 2 //
            Win h (rowSt cr u x (t + 1)) ∧ Win h (colSt cc v x (t + 1))})
          = 2 ^ (2 * (k - h))) :=
  core (fun u key => rowSt cr u key (t + 1)) (fun v key => colSt cc v key (t + 1))
    (t + 1) (4 * (t + 1) + 1) (2 * (t + 1)) (6 * (t + 1) + 1) (2 * t) (5 * t + 3)
    (3 * (t + 1) + 1) (7 * t + 6) h (t + 4) (7 * (t + 1) - 2) (6 * (t + 1) - 5)
    (fun key => row_name_dep cr key (t + 1)) (fun key => row_name_piv cr key (t + 1) (by omega))
    (fun key => col_name_dep cc key (t + 1)) (fun key => col_name_piv cc key (t + 1) (by omega))
    (fun u => dep_weaken (row_key_dep cr u (t + 1)) _ _ (by omega) (by omega))
    (fun u => row_key_piv_big cr u t ht (by omega))
    (fun v => dep_weaken (col_key_dep cc v (t + 1)) _ _ (by omega) (by omega))
    (fun v => col_key_piv_big cc v t (by omega) (by omega))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)

theorem main (k : ℕ) [NeZero k] (h r : ℕ) (hr : r = 1 ∨ 4 ≤ r) (hh : max 5 (r + 3) ≤ h)
    (hk : h + (if r = 1 then 7 else 7 * r - 2) ≤ k) (cr cc : ℕ → ZMod k → ZMod 2) :
    (∀ u v : ZMod k → ZMod 2,
      2 ^ (k - h - (if r = 1 then 7 else 7 * r - 2)) ∣
          Nat.card {x : ZMod k → ZMod 2 // Win h (rowOut r cr u x) ∧ Win h (colOut r cc v x)} ∧
        Nat.card {x : ZMod k → ZMod 2 // Win h (rowOut r cr u x) ∧ Win h (colOut r cc v x)}
          ≤ 2 ^ (k - h - (if r = 1 then 7 else 7 * r - 2)) * 2 ^ (if r = 1 then 4 else 6 * r - 5)) ∧
      (∀ u : ZMod k → ZMod 2, (∑ v : ZMod k → ZMod 2,
        Nat.card {x : ZMod k → ZMod 2 // Win h (rowOut r cr u x) ∧ Win h (colOut r cc v x)})
          = 2 ^ (2 * (k - h))) ∧
      (∀ v : ZMod k → ZMod 2, (∑ u : ZMod k → ZMod 2,
        Nat.card {x : ZMod k → ZMod 2 // Win h (rowOut r cr u x) ∧ Win h (colOut r cc v x)})
          = 2 ^ (2 * (k - h))) := by
  simp only [rowOut_eq, colOut_eq]
  rcases hr with rfl | hr
  · exact main1 h (by omega) hk cr cc
  · obtain ⟨t, rfl⟩ : ∃ t, r = t + 1 := ⟨r - 1, by omega⟩
    have e1 : ¬ t + 1 = 1 := by omega
    rw [ite_eq_right e1] at hk ⊢
    rw [ite_eq_right e1]
    exact main4 h t (by omega) (by omega) hk cr cc

end PEqualNP.Outside.L_meta_25836_aux

theorem PEqualNP.Outside.L_meta_25836 : (∀ (k : ℕ) [NeZero k] (h r : ℕ),
  let span := if r = 1 then 7 else 7*r-2
  let seed := if r = 1 then 4 else 6*r-5
  (r = 1 ∨ 4 ≤ r) → max 5 (r+3) ≤ h → h+span ≤ k →
  let I := ZMod k
  let W := I → ZMod 2
  let lo := k-h
  let turn := fun (dist : ℕ) (word : W) (site : I) => word (site - (dist : I))
  let mix := fun (dist : ℕ) (word : W) (site : I) =>
    word (site - (dist : I)) + word site + word (site + (dist : I))
  let chi := fun (word : W) (site : I) =>
    word site + (1 + word (site+1)) * word (site+2)
  ∀ cr cc : ℕ → W,
    let rowTest := fun (u key : W) =>
      let out := (List.range r).foldl (fun acc t =>
        chi (mix 1 acc) + turn (2*t) key + cr (t+1)) (turn 1 key + u)
      ∀ i : I, lo ≤ i.val → out i = 0
    let colTest := fun (v key : W) =>
      let out := (List.range r).foldl (fun acc t =>
        chi (mix 2 acc) + turn (3*(t+1)+1) key + cc (t+1)) (turn 3 key + v)
      ∀ i : I, lo ≤ i.val → out i = 0
    let wt := fun (u v : W) => Nat.card {x : W // rowTest u x ∧ colTest v x}
    let f := 2^(lo-span)
    (∀ u v, f ∣ wt u v ∧ wt u v ≤ f * 2^seed) ∧
      (∀ u, (∑ v : W, wt u v) = 2^(2*lo)) ∧
      (∀ v, (∑ u : W, wt u v) = 2^(2*lo))) := by
  intro k _ h r
  dsimp only
  intro hr hh hk cr cc
  exact PEqualNP.Outside.L_meta_25836_aux.main k h r hr hh hk cr cc
