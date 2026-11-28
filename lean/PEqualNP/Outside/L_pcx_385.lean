import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_pcx_385

def lawDef (n : ℕ) (σ : Fin n → Fin n) (p : Bool × Fin n → Option Bool)
    (r b : Fin (n + 1)) : ℚ :=
  (((Finset.univ : Finset (Bool × Fin n → Bool)).filter (fun x =>
    (∀ v, p v = none ∨ p v = some (x v)) ∧
    (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card = r.val ∧
    (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card = b.val)).card : ℚ) /
    (2 : ℚ) ^ ((Finset.univ.filter (fun v : Bool × Fin n => p v = none)).card)

def polyDef (n : ℕ) (σ : Fin n → Fin n) (p : Bool × Fin n → Option Bool) (u v : ℚ) : ℚ :=
  ∑ r : Fin (n + 1), ∑ b : Fin (n + 1), lawDef n σ p r b *
    (1 - u) ^ r.val * (1 + u) ^ (n - r.val) *
    (1 - v) ^ b.val * (1 + v) ^ (n - b.val)

def sgn (b : Bool) : ℚ := if b then -1 else 1

lemma sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> norm_num [sgn]

lemma sgn_mul_eq (a b : Bool) : sgn a * sgn b = if a ≠ b then -1 else 1 := by
  cases a <;> cases b <;> norm_num [sgn]

lemma one_add_sgn_mul (a b : Bool) (u : ℚ) :
    1 + u * sgn a * sgn b = if a ≠ b then 1 - u else 1 + u := by
  cases a <;> cases b <;> simp [sgn] <;> ring

def nextE {n : ℕ} (σ : Equiv.Perm (Fin n)) : Bool × Fin n ≃ Bool × Fin n where
  toFun e := match e.1 with
    | false => (true, e.2)
    | true => (false, σ e.2)
  invFun e := match e.1 with
    | true => (false, e.2)
    | false => (true, σ.symm e.2)
  left_inv e := by
    rcases e with ⟨b, i⟩
    cases b <;> simp
  right_inv e := by
    rcases e with ⟨b, i⟩
    cases b <;> simp

def headV {n : ℕ} (σ : Equiv.Perm (Fin n)) : Bool × Fin n ≃ Bool × Fin n where
  toFun e := match e.1 with
    | false => (false, e.2)
    | true => (true, σ e.2)
  invFun v := match v.1 with
    | false => (false, v.2)
    | true => (true, σ.symm v.2)
  left_inv e := by
    rcases e with ⟨b, i⟩
    cases b <;> simp
  right_inv v := by
    rcases v with ⟨b, i⟩
    cases b <;> simp

def epsV {n : ℕ} (p : Bool × Fin n → Option Bool) (v : Bool × Fin n) : ℚ :=
  match p v with
  | none => 1
  | some b => sgn b

lemma epsV_sq {n : ℕ} (p : Bool × Fin n → Option Bool) (v : Bool × Fin n) :
    epsV p v = 1 ∨ epsV p v = -1 := by
  unfold epsV
  cases p v with
  | none => left; rfl
  | some b => cases b <;> simp [sgn]

def qE {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (e : Bool × Fin n) : Option Bool :=
  p (headV σ e)

def epsE {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (e : Bool × Fin n) : ℚ :=
  epsV p (headV σ e)

def edgeW {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (u v : ℚ) (e : Bool × Fin n) : ℚ :=
  (if e.1 then v else u) * epsE σ p e * epsE σ p ((nextE σ).symm e)

lemma prod_bool_ite (u : ℚ) {n : ℕ} (P : Fin n → Prop) [DecidablePred P] :
    (∏ i : Fin n, if P i then 1 - u else 1 + u) =
      (1 - u) ^ (Finset.univ.filter P).card *
      (1 + u) ^ (n - (Finset.univ.filter P).card) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 2
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) P
  simp only [Finset.card_univ, Fintype.card_fin] at h
  omega

lemma term_eq_prod_edges {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Bool × Fin n → Bool) (u v : ℚ) :
    (1 - u) ^ (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card *
    (1 + u) ^ (n - (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card) *
    ((1 - v) ^ (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card *
    (1 + v) ^ (n - (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card)) =
    ∏ e : Bool × Fin n,
      (1 + (if e.1 then v else u) * sgn (x (headV σ e)) * sgn (x (headV σ ((nextE σ).symm e)))) := by
  rw [Fintype.prod_prod_type, Fintype.prod_bool]
  have hfalse :
      ∏ i : Fin n, (1 + (if false then v else u) *
        sgn (x (headV σ (false, i))) * sgn (x (headV σ ((nextE σ).symm (false, i))))) =
      (1 - u) ^ (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card *
      (1 + u) ^ (n - (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card) := by
    rw [← prod_bool_ite]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte, headV, nextE, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
      Equiv.apply_symm_apply]
    exact one_add_sgn_mul (x (false, i)) (x (true, i)) u
  have htrue :
      ∏ i : Fin n, (1 + (if true then v else u) *
        sgn (x (headV σ (true, i))) * sgn (x (headV σ ((nextE σ).symm (true, i))))) =
      (1 - v) ^ (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card *
      (1 + v) ^ (n - (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card) := by
    rw [← prod_bool_ite]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [↓reduceIte, headV, nextE, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
    rw [one_add_sgn_mul (x (true, σ i)) (x (false, i)) v]
    have hne : (x (true, σ i) ≠ x (false, i)) ↔ (x (false, i) ≠ x (true, σ i)) := ne_comm
    simp only [hne]
  rw [htrue, hfalse, mul_comm]

lemma polyDef_eq_avg_compat {n : ℕ} (σ : Fin n → Fin n) (p : Bool × Fin n → Option Bool) (u v : ℚ) :
    polyDef n σ p u v =
      (∑ x ∈ Finset.univ.filter (fun x : Bool × Fin n → Bool =>
          ∀ w, p w = none ∨ p w = some (x w)),
        (1 - u) ^ (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card *
        (1 + u) ^ (n - (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card) *
        ((1 - v) ^ (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card *
        (1 + v) ^ (n - (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card))) /
      (2 : ℚ) ^ ((Finset.univ.filter (fun w : Bool × Fin n => p w = none)).card) := by
  unfold polyDef lawDef
  set D : ℚ := (2 : ℚ) ^ ((Finset.univ.filter (fun w : Bool × Fin n => p w = none)).card)
  have hrew : ∀ r b : Fin (n + 1),
      (((Finset.univ : Finset (Bool × Fin n → Bool)).filter (fun x =>
        (∀ w, p w = none ∨ p w = some (x w)) ∧
        (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card = r.val ∧
        (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card = b.val)).card : ℚ) / D *
      (1 - u) ^ r.val * (1 + u) ^ (n - r.val) *
      (1 - v) ^ b.val * (1 + v) ^ (n - b.val) =
      (((Finset.univ : Finset (Bool × Fin n → Bool)).filter (fun x =>
        (∀ w, p w = none ∨ p w = some (x w)) ∧
        (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card = r.val ∧
        (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card = b.val)).card : ℚ) *
      ((1 - u) ^ r.val * (1 + u) ^ (n - r.val) *
       ((1 - v) ^ b.val * (1 + v) ^ (n - b.val))) / D := by
    intro r b; ring
  simp_rw [hrew, div_eq_mul_inv, ← Finset.sum_mul]
  congr 1
  have hstep : ∀ r b : Fin (n + 1),
      (((Finset.univ : Finset (Bool × Fin n → Bool)).filter (fun x =>
        (∀ w, p w = none ∨ p w = some (x w)) ∧
        (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card = r.val ∧
        (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card = b.val)).card : ℚ) *
      ((1 - u) ^ r.val * (1 + u) ^ (n - r.val) *
       ((1 - v) ^ b.val * (1 + v) ^ (n - b.val))) =
      ∑ x ∈ Finset.univ.filter (fun x : Bool × Fin n → Bool =>
          ∀ w, p w = none ∨ p w = some (x w)),
        if (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card = r.val ∧
           (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card = b.val
        then (1 - u) ^ r.val * (1 + u) ^ (n - r.val) *
             ((1 - v) ^ b.val * (1 + v) ^ (n - b.val))
        else 0 := by
    intro r b
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      Finset.filter_filter]
  simp_rw [hstep]
  rw [Finset.sum_comm]
  have hswap : ∀ r : Fin (n + 1),
      ∑ b : Fin (n + 1), ∑ x ∈ Finset.univ.filter (fun x : Bool × Fin n → Bool =>
          ∀ w, p w = none ∨ p w = some (x w)),
        (if (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card = r.val ∧
            (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card = b.val
         then (1 - u) ^ r.val * (1 + u) ^ (n - r.val) *
              ((1 - v) ^ b.val * (1 + v) ^ (n - b.val))
         else 0) =
      ∑ x ∈ Finset.univ.filter (fun x : Bool × Fin n → Bool =>
          ∀ w, p w = none ∨ p w = some (x w)),
        ∑ b : Fin (n + 1),
          (if (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card = r.val ∧
              (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card = b.val
           then (1 - u) ^ r.val * (1 + u) ^ (n - r.val) *
                ((1 - v) ^ b.val * (1 + v) ^ (n - b.val))
           else 0) := by
    intro r
    exact Finset.sum_comm
  rw [Finset.sum_comm]
  simp_rw [hswap]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  set rx := (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card
  set bx := (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card
  have hrx : rx < n + 1 := Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))
  have hbx : bx < n + 1 := Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))
  have hinner : ∀ r : Fin (n + 1),
      ∑ b : Fin (n + 1),
        (if rx = r.val ∧ bx = b.val
         then (1 - u) ^ r.val * (1 + u) ^ (n - r.val) *
              ((1 - v) ^ b.val * (1 + v) ^ (n - b.val))
         else 0) =
      if rx = r.val then
        (1 - u) ^ r.val * (1 + u) ^ (n - r.val) *
        ((1 - v) ^ bx * (1 + v) ^ (n - bx))
      else 0 := by
    intro r
    by_cases hr : rx = r.val
    · simp only [hr, true_and, ↓reduceIte]
      rw [Finset.sum_eq_single ⟨bx, hbx⟩]
      · simp
      · intro b _ hne
        have : bx ≠ b.val := fun h => hne (Fin.ext h.symm)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp [hr]
  simp_rw [hinner]
  rw [Finset.sum_eq_single ⟨rx, hrx⟩]
  · simp
  · intro r _ hne
    have : rx ≠ r.val := fun h => hne (Fin.ext h.symm)
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma prod_one_add_eq_sum_bool {α : Type*} [Fintype α] [DecidableEq α] (f : α → ℚ) :
    (∏ a : α, (1 + f a)) = ∑ S : α → Bool, ∏ a : α, if S a then f a else 1 := by
  have h : (∏ a : α, (1 + f a)) = ∏ a : α, ∑ b : Bool, if b then f a else 1 := by
    refine Finset.prod_congr rfl (fun a _ => ?_)
    rw [Fintype.sum_bool]
    simp [add_comm]
  rw [h, Fintype.prod_sum]

lemma prod_ite_sgn_mul {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Bool × Fin n → Bool)
    (x : Bool × Fin n → Bool) :
    (∏ e : Bool × Fin n, if S e then sgn (x (headV σ e)) * sgn (x (headV σ ((nextE σ).symm e))) else 1) =
    ∏ e : Bool × Fin n, if S e ≠ S (nextE σ e) then sgn (x (headV σ e)) else 1 := by
  have h1 :
      (∏ e : Bool × Fin n, if S e then sgn (x (headV σ e)) * sgn (x (headV σ ((nextE σ).symm e))) else 1) =
      (∏ e : Bool × Fin n, if S e then sgn (x (headV σ e)) else 1) *
      (∏ e : Bool × Fin n, if S e then sgn (x (headV σ ((nextE σ).symm e))) else 1) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun e _ => ?_)
    cases S e <;> simp
  have h2 :
      (∏ e : Bool × Fin n, if S e then sgn (x (headV σ ((nextE σ).symm e))) else 1) =
      ∏ e : Bool × Fin n, if S (nextE σ e) then sgn (x (headV σ e)) else 1 := by
    refine Fintype.prod_equiv (nextE σ).symm _ _ (fun e => ?_)
    simp
  rw [h1, h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  cases S e <;> cases S (nextE σ e) <;> simp [sgn_mul_self]

lemma prod_ite_eps_mul {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (S : Bool × Fin n → Bool) :
    (∏ e : Bool × Fin n, if S e ≠ S (nextE σ e) then epsE σ p e else 1) =
    ∏ e : Bool × Fin n, if S e then epsE σ p e * epsE σ p ((nextE σ).symm e) else 1 := by
  have h1 :
      (∏ e : Bool × Fin n, if S e ≠ S (nextE σ e) then epsE σ p e else 1) =
      (∏ e : Bool × Fin n, if S e then epsE σ p e else 1) *
      (∏ e : Bool × Fin n, if S (nextE σ e) then epsE σ p e else 1) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun e _ => ?_)
    have hsq : epsE σ p e * epsE σ p e = 1 := by
      rcases epsV_sq p (headV σ e) with h | h <;> simp [epsE, h]
    cases S e <;> cases S (nextE σ e) <;> simp [hsq]
  have h2 :
      (∏ e : Bool × Fin n, if S (nextE σ e) then epsE σ p e else 1) =
      ∏ e : Bool × Fin n, if S e then epsE σ p ((nextE σ).symm e) else 1 := by
    refine Fintype.prod_equiv (nextE σ) _ _ (fun e => ?_)
    simp
  rw [h1, h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  cases S e <;> simp

lemma compat_filter_eq_piFinset {n : ℕ} (p : Bool × Fin n → Option Bool) :
    Finset.univ.filter (fun x : Bool × Fin n → Bool => ∀ w, p w = none ∨ p w = some (x w)) =
    Fintype.piFinset (fun w : Bool × Fin n => match p w with | none => Finset.univ | some b => {b}) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  constructor
  · intro hx w
    cases hw : p w with
    | none => exact Finset.mem_univ _
    | some b =>
      rcases hx w with h | h
      · rw [hw] at h; cases h
      · rw [hw] at h
        have hbx : b = x w := Option.some.inj h
        simp [hbx]
  · intro hx w
    have hw := hx w
    cases hp : p w with
    | none => left; rfl
    | some b =>
      rw [hp] at hw
      right
      simp only [Finset.mem_singleton] at hw
      rw [hw]

lemma sum_compat_prod_sgn {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (S : Bool × Fin n → Bool) :
    (∑ x ∈ Finset.univ.filter (fun x : Bool × Fin n → Bool =>
        ∀ w, p w = none ∨ p w = some (x w)),
      ∏ e : Bool × Fin n, if S e ≠ S (nextE σ e) then sgn (x (headV σ e)) else 1) =
    if ∀ e : Bool × Fin n, qE σ p e = none → S (nextE σ e) = S e then
      (2 : ℚ) ^ ((Finset.univ.filter (fun w : Bool × Fin n => p w = none)).card) *
      (∏ e : Bool × Fin n, if S e ≠ S (nextE σ e) then epsE σ p e else 1)
    else 0 := by
  rw [compat_filter_eq_piFinset]
  have hreidx : ∀ x : Bool × Fin n → Bool,
      (∏ e : Bool × Fin n, if S e ≠ S (nextE σ e) then sgn (x (headV σ e)) else 1) =
      ∏ w : Bool × Fin n,
        if S ((headV σ).symm w) ≠ S (nextE σ ((headV σ).symm w)) then sgn (x w) else 1 := by
    intro x
    exact Fintype.prod_equiv (headV σ) _ _ (fun e => by simp)
  simp_rw [hreidx]
  have hpi := (Finset.prod_univ_sum
    (fun w : Bool × Fin n => match p w with | none => Finset.univ | some b => {b})
    (fun w b => if S ((headV σ).symm w) ≠ S (nextE σ ((headV σ).symm w)) then sgn b else 1)).symm
  rw [hpi]
  have hback :
      (∏ w : Bool × Fin n, ∑ b ∈ (match p w with | none => Finset.univ | some c => {c}),
        if S ((headV σ).symm w) ≠ S (nextE σ ((headV σ).symm w)) then sgn b else 1) =
      ∏ e : Bool × Fin n, ∑ b ∈ (match qE σ p e with | none => Finset.univ | some c => {c}),
        if S e ≠ S (nextE σ e) then sgn b else 1 := by
    exact Fintype.prod_equiv (headV σ).symm _ _ (fun w => by simp [qE])
  rw [hback]
  by_cases hval : ∀ e : Bool × Fin n, qE σ p e = none → S (nextE σ e) = S e
  · rw [if_pos hval]
    have hfactor : ∀ e : Bool × Fin n,
        (∑ b ∈ (match qE σ p e with | none => Finset.univ | some c => {c}),
          if S e ≠ S (nextE σ e) then sgn b else 1) =
        (if qE σ p e = none then (2 : ℚ) else 1) *
        (if S e ≠ S (nextE σ e) then epsE σ p e else 1) := by
      intro e
      cases hq : qE σ p e with
      | none =>
        have heq : S (nextE σ e) = S e := hval e hq
        have hne : ¬ (S e ≠ S (nextE σ e)) := by simp [heq]
        simp only [hne, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
          nsmul_eq_mul, mul_one, Nat.cast_ofNat]
      | some c =>
        simp only [Finset.sum_singleton, reduceCtorEq, ↓reduceIte, one_mul, epsE, epsV]
        change (if S e ≠ S (nextE σ e) then sgn c else 1) =
          if S e ≠ S (nextE σ e) then (match qE σ p e with | none => 1 | some b => sgn b) else 1
        rw [hq]
    simp_rw [hfactor]
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    congr 1
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_of_bijective (f := fun x : {e : Bool × Fin n // qE σ p e = none} =>
        (⟨headV σ x.1, x.2⟩ : {w : Bool × Fin n // p w = none}))
      ⟨fun a b hab => Subtype.ext ((headV σ).injective (congrArg Subtype.val hab)),
       fun y => ⟨⟨(headV σ).symm y.1, by simp [qE, y.2]⟩, Subtype.ext (by simp)⟩⟩
  · rw [if_neg hval]
    have hex : ∃ e0 : Bool × Fin n, qE σ p e0 = none ∧ S (nextE σ e0) ≠ S e0 := by
      by_contra hall
      apply hval
      intro e hq
      by_contra hne
      exact hall ⟨e, hq, hne⟩
    obtain ⟨e0, hq0, hne0⟩ := hex
    refine Finset.prod_eq_zero (Finset.mem_univ e0) ?_
    rw [hq0]
    have hne' : S e0 ≠ S (nextE σ e0) := Ne.symm hne0
    rw [Fintype.sum_bool, if_pos hne', if_pos hne']
    norm_num [sgn]

lemma polyDef_eq_edgeSum {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (u v : ℚ) :
    polyDef n σ p u v =
      ∑ S ∈ Finset.univ.filter (fun S : Bool × Fin n → Bool =>
        ∀ e : Bool × Fin n, qE σ p e = none → S (nextE σ e) = S e),
        ∏ e : Bool × Fin n, if S e then edgeW σ p u v e else 1 := by
  rw [polyDef_eq_avg_compat]
  simp_rw [term_eq_prod_edges, prod_one_add_eq_sum_bool]
  rw [Finset.sum_comm]
  have hpull : ∀ S : Bool × Fin n → Bool,
      (∑ x ∈ Finset.univ.filter (fun x : Bool × Fin n → Bool =>
          ∀ w, p w = none ∨ p w = some (x w)),
        ∏ e : Bool × Fin n,
          if S e then (if e.1 then v else u) * sgn (x (headV σ e)) *
            sgn (x (headV σ ((nextE σ).symm e)))
          else 1) =
      (∏ e : Bool × Fin n, if S e then (if e.1 then v else u) else 1) *
      (∑ x ∈ Finset.univ.filter (fun x : Bool × Fin n → Bool =>
          ∀ w, p w = none ∨ p w = some (x w)),
        ∏ e : Bool × Fin n, if S e ≠ S (nextE σ e) then sgn (x (headV σ e)) else 1) := by
    intro S
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← prod_ite_sgn_mul, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun e _ => ?_)
    cases S e <;> simp [mul_assoc]
  simp_rw [hpull, sum_compat_prod_sgn]
  set D : ℚ := (2 : ℚ) ^ ((Finset.univ.filter (fun w : Bool × Fin n => p w = none)).card)
  have hD : D ≠ 0 := by positivity
  rw [div_eq_mul_inv, Finset.sum_mul]
  simp_rw [← div_eq_mul_inv]
  have hterm : ∀ S : Bool × Fin n → Bool,
      ((∏ e : Bool × Fin n, if S e then (if e.1 then v else u) else 1) *
        (if ∀ e : Bool × Fin n, qE σ p e = none → S (nextE σ e) = S e then
          D * (∏ e : Bool × Fin n, if S e ≠ S (nextE σ e) then epsE σ p e else 1)
         else 0)) / D =
      if ∀ e : Bool × Fin n, qE σ p e = none → S (nextE σ e) = S e then
        ∏ e : Bool × Fin n, if S e then edgeW σ p u v e else 1
      else 0 := by
    intro S
    by_cases hval : ∀ e : Bool × Fin n, qE σ p e = none → S (nextE σ e) = S e
    · simp only [eq_true hval, ↓reduceIte]
      rw [prod_ite_eps_mul]
      have hmul :
          (∏ e : Bool × Fin n, if S e then (if e.1 then v else u) else 1) *
          (D * (∏ e : Bool × Fin n, if S e then epsE σ p e * epsE σ p ((nextE σ).symm e) else 1)) / D =
          (∏ e : Bool × Fin n, if S e then (if e.1 then v else u) else 1) *
          (∏ e : Bool × Fin n, if S e then epsE σ p e * epsE σ p ((nextE σ).symm e) else 1) := by
        rw [← mul_assoc, mul_comm _ D, mul_assoc, mul_div_cancel_left₀ _ hD]
      rw [hmul, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun e _ => ?_)
      cases S e <;> simp [edgeW, mul_assoc]
    · simp only [eq_false hval, ↓reduceIte, mul_zero, zero_div]
  simp_rw [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]

lemma sum_valid_eq_prod {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (cls : α → β) (hsurj : Function.Surjective cls) (W : α → ℚ)
    (P : (α → Bool) → Prop) [DecidablePred P]
    (hP : ∀ S : α → Bool, P S ↔ ∀ x y, cls x = cls y → S x = S y) :
    (∑ S ∈ Finset.univ.filter P, ∏ x : α, if S x then W x else 1) =
    ∏ b : β, (1 + ∏ x ∈ Finset.univ.filter (fun x => cls x = b), W x) := by
  rw [prod_one_add_eq_sum_bool]
  symm
  refine Finset.sum_bij (fun T _ => fun x => T (cls x)) ?_ ?_ ?_ ?_
  · intro T _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hP]
    intro x y hxy
    rw [hxy]
  · intro T₁ _ T₂ _ h
    funext b
    obtain ⟨x, rfl⟩ := hsurj b
    exact congrFun h x
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hP] at hS
    refine ⟨fun b => S (hsurj b).choose, Finset.mem_univ _, ?_⟩
    funext x
    exact hS _ _ (hsurj (cls x)).choose_spec
  · intro T _
    have hfib : (∏ x : α, if T (cls x) then W x else 1) =
        ∏ b : β, ∏ x ∈ Finset.univ.filter (fun x : α => cls x = b),
          if T (cls x) then W x else 1 := by
      exact (Finset.prod_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _).symm
    rw [hfib]
    refine Finset.prod_congr rfl (fun b _ => ?_)
    cases hTb : T b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine (Finset.prod_eq_one (fun x hx => ?_)).symm
      rw [Finset.mem_filter] at hx
      simp [hx.2, hTb]
    · simp only [↓reduceIte]
      refine (Finset.prod_congr rfl (fun x hx => ?_)).symm
      rw [Finset.mem_filter] at hx
      simp [hx.2, hTb]

def ArcStep {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (e₁ e₂ : Bool × Fin n) : Prop :=
  qE σ p e₁ = none ∧ e₂ = nextE σ e₁

lemma arcStep_right_unique {n : ℕ} {σ : Equiv.Perm (Fin n)} {p : Bool × Fin n → Option Bool}
    {x y₁ y₂ : Bool × Fin n} (h₁ : ArcStep σ p x y₁) (h₂ : ArcStep σ p x y₂) : y₁ = y₂ :=
  h₁.2.trans h₂.2.symm

lemma arcStep_left_unique {n : ℕ} {σ : Equiv.Perm (Fin n)} {p : Bool × Fin n → Option Bool}
    {x₁ x₂ y : Bool × Fin n} (h₁ : ArcStep σ p x₁ y) (h₂ : ArcStep σ p x₂ y) : x₁ = x₂ :=
  (nextE σ).injective (h₁.2.symm.trans h₂.2)

lemma reach_linear_out {n : ℕ} {σ : Equiv.Perm (Fin n)} {p : Bool × Fin n → Option Bool}
    {a x y : Bool × Fin n}
    (hx : Relation.ReflTransGen (ArcStep σ p) a x)
    (hy : Relation.ReflTransGen (ArcStep σ p) a y) :
    Relation.ReflTransGen (ArcStep σ p) x y ∨ Relation.ReflTransGen (ArcStep σ p) y x := by
  induction hx using Relation.ReflTransGen.head_induction_on generalizing y with
  | refl => left; exact hy
  | @head a' b hab hbx ih =>
    rcases Relation.ReflTransGen.cases_head hy with rfl | ⟨c, hac, hcy⟩
    · right; exact Relation.ReflTransGen.head hab hbx
    · have hbc : b = c := arcStep_right_unique hab hac
      subst hbc
      exact ih hcy

lemma reach_linear_in {n : ℕ} {σ : Equiv.Perm (Fin n)} {p : Bool × Fin n → Option Bool}
    {a x y : Bool × Fin n}
    (hx : Relation.ReflTransGen (ArcStep σ p) x a)
    (hy : Relation.ReflTransGen (ArcStep σ p) y a) :
    Relation.ReflTransGen (ArcStep σ p) x y ∨ Relation.ReflTransGen (ArcStep σ p) y x := by
  induction hx generalizing y with
  | refl => right; exact hy
  | @tail b a' hxb hba ih =>
    rcases Relation.ReflTransGen.cases_tail hy with rfl | ⟨c, hyc, hca⟩
    · left; exact Relation.ReflTransGen.tail hxb hba
    · have hbc : b = c := arcStep_left_unique hba hca
      subst hbc
      exact ih hyc

lemma eqv_imp_reach_or {n : ℕ} {σ : Equiv.Perm (Fin n)} {p : Bool × Fin n → Option Bool}
    {x y : Bool × Fin n} (h : Relation.EqvGen (ArcStep σ p) x y) :
    Relation.ReflTransGen (ArcStep σ p) x y ∨ Relation.ReflTransGen (ArcStep σ p) y x := by
  induction h with
  | rel a b hab => left; exact Relation.ReflTransGen.single hab
  | refl a => left; exact Relation.ReflTransGen.refl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 =>
    rcases ih1 with h1 | h1 <;> rcases ih2 with h2 | h2
    · left; exact h1.trans h2
    · exact reach_linear_in h1 h2
    · exact reach_linear_out h1 h2
    · right; exact h2.trans h1

lemma stop_unique {n : ℕ} {σ : Equiv.Perm (Fin n)} {p : Bool × Fin n → Option Bool}
    {x y : Bool × Fin n} (heqv : Relation.EqvGen (ArcStep σ p) x y)
    (hx : qE σ p x ≠ none) (hy : qE σ p y ≠ none) : x = y := by
  rcases eqv_imp_reach_or heqv with h | h
  · rcases Relation.ReflTransGen.cases_head h with rfl | ⟨b, hxb, _⟩
    · rfl
    · exact absurd hxb.1 hx
  · rcases Relation.ReflTransGen.cases_head h with rfl | ⟨b, hyb, _⟩
    · rfl
    · exact absurd hyb.1 hy

lemma valid_iff_eqv_const {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (S : Bool × Fin n → Bool) :
    (∀ e : Bool × Fin n, qE σ p e = none → S (nextE σ e) = S e) ↔
    (∀ x y : Bool × Fin n, Relation.EqvGen (ArcStep σ p) x y → S x = S y) := by
  constructor
  · intro h x y hxy
    induction hxy with
    | rel a b hab => rw [hab.2]; exact (h a hab.1).symm
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h e hq
    exact (h e (nextE σ e) (Relation.EqvGen.rel e (nextE σ e) ⟨hq, rfl⟩)).symm

lemma prod_pm_one {α : Type*} (s : Finset α) (f : α → ℚ)
    (hf : ∀ a ∈ s, f a = 1 ∨ f a = -1) :
    (∏ a ∈ s, f a) = 1 ∨ (∏ a ∈ s, f a) = -1 := by
  classical
  induction s using Finset.induction_on with
  | empty => left; simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun x hx => hf x (Finset.mem_insert_of_mem hx))
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2]

lemma arc_class_props {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (e0 : Bool × Fin n) :
    let c : Finset (Bool × Fin n) :=
      @Finset.filter _ (fun e' => Relation.EqvGen (ArcStep σ p) e0 e')
        (Classical.decPred _) Finset.univ
    let r := (c.filter (fun e => e.1 = false)).card
    let b := (c.filter (fun e => e.1 = true)).card
    0 < r + b ∧ r ≤ b + 1 ∧ b ≤ r + 1 := by
  classical
  intro c r b
  have hmem0 : e0 ∈ c := by
    simp [c, Relation.EqvGen.refl]
  have hrb_sum : r + b = c.card := by
    have h := Finset.card_filter_add_card_filter_not (s := c) (fun e : Bool × Fin n => e.1 = false)
    have heq : c.filter (fun e => ¬ e.1 = false) = c.filter (fun e => e.1 = true) := by
      ext e; cases e.1 <;> simp
    rw [heq] at h
    exact h
  have hpos : 0 < r + b := by
    rw [hrb_sum]
    exact Finset.card_pos.mpr ⟨e0, hmem0⟩
  have hstop_le : (c.filter (fun e => qE σ p e ≠ none)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [Finset.mem_filter, c, Finset.mem_univ, true_and] at hx hy
    exact stop_unique (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hx.1) hy.1) hx.2 hy.2
  have hbound : ∀ col : Bool,
      (c.filter (fun e => e.1 = col)).card ≤ (c.filter (fun e => e.1 = !col)).card + 1 := by
    intro col
    set s := c.filter (fun e => e.1 = col)
    have hsplit := Finset.card_filter_add_card_filter_not (s := s) (fun e => qE σ p e = none)
    have hneg_le : (s.filter (fun e => ¬ qE σ p e = none)).card ≤ 1 := by
      refine le_trans (Finset.card_le_card ?_) hstop_le
      intro e he
      simp only [Finset.mem_filter, s] at he ⊢
      exact ⟨he.1.1, he.2⟩
    have hgo_le : (s.filter (fun e => qE σ p e = none)).card ≤
        (c.filter (fun e => e.1 = !col)).card := by
      have hinj : ((s.filter (fun e => qE σ p e = none)).image (nextE σ)).card =
          (s.filter (fun e => qE σ p e = none)).card :=
        Finset.card_image_of_injective _ (nextE σ).injective
      rw [← hinj]
      refine Finset.card_le_card ?_
      intro e' he'
      rw [Finset.mem_image] at he'
      obtain ⟨e, he, rfl⟩ := he'
      simp only [Finset.mem_filter, s, c, Finset.mem_univ, true_and] at he ⊢
      refine ⟨Relation.EqvGen.trans _ _ _ he.1.1 (Relation.EqvGen.rel e (nextE σ e) ⟨he.2, rfl⟩), ?_⟩
      rcases e with ⟨eb, ei⟩
      cases eb <;> simp [nextE] at he ⊢ <;> simp [he.1.2]
    omega
  refine ⟨hpos, ?_, ?_⟩
  · simpa using hbound false
  · simpa using hbound true

lemma exists_arc_factors {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    ∃ L : List (ℕ × ℕ × Bool),
      (∀ a ∈ L, 0 < a.1 + a.2.1 ∧ a.1 ≤ a.2.1 + 1 ∧ a.2.1 ≤ a.1 + 1) ∧
      ∀ u v : ℚ, polyDef n σ p u v =
        (L.map (fun a => 1 + (if a.2.2 then (1 : ℚ) else -1) * u ^ a.1 * v ^ a.2.1)).prod := by
  classical
  let cls : Bool × Fin n → Finset (Bool × Fin n) :=
    fun e => Finset.univ.filter (fun e' => Relation.EqvGen (ArcStep σ p) e e')
  let C : Finset (Finset (Bool × Fin n)) := Finset.univ.image cls
  let clsSub : Bool × Fin n → {c : Finset (Bool × Fin n) // c ∈ C} :=
    fun e => ⟨cls e, Finset.mem_image_of_mem cls (Finset.mem_univ e)⟩
  have hsurj : Function.Surjective clsSub := by
    rintro ⟨c, hc⟩
    rw [Finset.mem_image] at hc
    obtain ⟨e, _, rfl⟩ := hc
    exact ⟨e, rfl⟩
  have hcls_iff : ∀ x y, clsSub x = clsSub y ↔ Relation.EqvGen (ArcStep σ p) x y := by
    intro x y
    constructor
    · intro h
      have hx : y ∈ cls y := by simp [cls, Relation.EqvGen.refl]
      have h' : cls x = cls y := congrArg Subtype.val h
      rw [← h'] at hx
      simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx
    · intro h
      apply Subtype.ext
      ext z
      dsimp only [clsSub, cls]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hxz => Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) hxz,
        fun hyz => Relation.EqvGen.trans _ _ _ h hyz⟩
  have hfib : ∀ c : {c : Finset (Bool × Fin n) // c ∈ C},
      Finset.univ.filter (fun x => clsSub x = c) = c.1 := by
    rintro ⟨c, hc⟩
    rw [Finset.mem_image] at hc
    obtain ⟨e0, _, rfl⟩ := hc
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hsub : (clsSub x = ⟨cls e0, Finset.mem_image_of_mem cls (Finset.mem_univ e0)⟩) ↔
        clsSub x = clsSub e0 := Iff.rfl
    rw [hsub, hcls_iff]
    simp only [cls, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => Relation.EqvGen.symm _ _ h, fun h => Relation.EqvGen.symm _ _ h⟩
  let toTriple : {c : Finset (Bool × Fin n) // c ∈ C} → ℕ × ℕ × Bool := fun c =>
    let r := (c.1.filter (fun e => e.1 = false)).card
    let b := (c.1.filter (fun e => e.1 = true)).card
    let sg := ∏ e ∈ c.1, (epsE σ p e * epsE σ p ((nextE σ).symm e))
    (r, b, decide (sg = 1))
  refine ⟨(Finset.univ.toList).map toTriple, ?_, ?_⟩
  · intro a ha
    rw [List.mem_map] at ha
    obtain ⟨c, _, rfl⟩ := ha
    rcases c with ⟨c, hc⟩
    rw [Finset.mem_image] at hc
    obtain ⟨e0, _, rfl⟩ := hc
    exact arc_class_props σ p e0
  · intro u v
    rw [polyDef_eq_edgeSum]
    rw [sum_valid_eq_prod clsSub hsurj (edgeW σ p u v) _ (fun S => by
      simp only [hcls_iff]
      exact valid_iff_eqv_const σ p S)]
    rw [List.map_map]
    have hlist :
        ((Finset.univ : Finset {c : Finset (Bool × Fin n) // c ∈ C}).toList.map
          ((fun a : ℕ × ℕ × Bool => 1 + (if a.2.2 then (1 : ℚ) else -1) * u ^ a.1 * v ^ a.2.1) ∘
            toTriple)).prod =
        ∏ c : {c : Finset (Bool × Fin n) // c ∈ C},
          (fun a : ℕ × ℕ × Bool => 1 + (if a.2.2 then (1 : ℚ) else -1) * u ^ a.1 * v ^ a.2.1)
            (toTriple c) := by
      exact Finset.prod_map_toList _ _
    rw [hlist]
    refine Finset.prod_congr rfl (fun c _ => ?_)
    rw [hfib c]
    congr 1
    dsimp only [toTriple]
    have hsg : (∏ e ∈ c.1, (epsE σ p e * epsE σ p ((nextE σ).symm e))) = 1 ∨
        (∏ e ∈ c.1, (epsE σ p e * epsE σ p ((nextE σ).symm e))) = -1 := by
      refine prod_pm_one c.1 _ (fun e _ => ?_)
      rcases epsV_sq p (headV σ e) with h1 | h1 <;>
        rcases epsV_sq p (headV σ ((nextE σ).symm e)) with h2 | h2 <;>
        simp [epsE, h1, h2]
    have hsg_eq :
        (if decide ((∏ e ∈ c.1, (epsE σ p e * epsE σ p ((nextE σ).symm e))) = 1) then (1 : ℚ) else -1) =
        ∏ e ∈ c.1, (epsE σ p e * epsE σ p ((nextE σ).symm e)) := by
      rcases hsg with h | h <;> rw [h] <;> norm_num
    rw [hsg_eq]
    have hsplit : (∏ e ∈ c.1, edgeW σ p u v e) =
        (∏ e ∈ c.1, if e.1 then v else u) *
        (∏ e ∈ c.1, (epsE σ p e * epsE σ p ((nextE σ).symm e))) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun e _ => ?_)
      simp [edgeW, mul_assoc]
    have huv : (∏ e ∈ c.1, if e.1 then v else u) =
        u ^ (c.1.filter (fun e => e.1 = false)).card *
        v ^ (c.1.filter (fun e => e.1 = true)).card := by
      have hf : c.1.filter (fun e => ¬ e.1 = true) = c.1.filter (fun e => e.1 = false) := by
        ext e; cases e.1 <;> simp
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, mul_comm, hf]
    rw [hsplit, huv]
    ring

def GoodPair (ab : ℕ × ℕ) : Prop :=
  0 < ab.1 + ab.2 ∧
  (ab.1 = ab.2 ∨
   ab.1 = ab.2 + 1 ∨
   ab.2 = ab.1 + 1 ∨
   (ab.1 = ab.2 + 2 ∧ Even ab.2) ∨
   (ab.2 = ab.1 + 2 ∧ Even ab.1))

lemma goodPair_of_arc {r b : ℕ} (hpos : 0 < r + b) (h1 : r ≤ b + 1) (h2 : b ≤ r + 1) :
    GoodPair (r, b) := by
  refine ⟨hpos, ?_⟩
  omega

lemma goodPair_double_of_arc {r b : ℕ} (hpos : 0 < r + b) (h1 : r ≤ b + 1) (h2 : b ≤ r + 1) :
    GoodPair (2 * r, 2 * b) := by
  refine ⟨by omega, ?_⟩
  have hcas : r = b ∨ r = b + 1 ∨ b = r + 1 := by omega
  rcases hcas with rfl | rfl | rfl
  · left; rfl
  · right; right; right; left
    exact ⟨by omega, ⟨b, by omega⟩⟩
  · right; right; right; right
    exact ⟨by omega, ⟨r, by omega⟩⟩

lemma goodPair_inj {k : ℕ} (hk : 3 ≤ k) {p₁ p₂ : ℕ × ℕ}
    (h₁ : GoodPair p₁) (h₂ : GoodPair p₂) (heq : p₁.1 + k * p₁.2 = p₂.1 + k * p₂.2) :
    p₁ = p₂ := by
  rcases p₁ with ⟨r₁, b₁⟩
  rcases p₂ with ⟨r₂, b₂⟩
  rcases h₁ with ⟨_, hc₁⟩
  rcases h₂ with ⟨_, hc₂⟩
  by_cases hk3 : k = 3
  · subst hk3
    rcases hc₁ with h1 | h1 | h1 | ⟨h1, ⟨m1, hm1⟩⟩ | ⟨h1, ⟨m1, hm1⟩⟩ <;>
    rcases hc₂ with h2 | h2 | h2 | ⟨h2, ⟨m2, hm2⟩⟩ | ⟨h2, ⟨m2, hm2⟩⟩ <;>
    exact Prod.ext (by omega) (by omega)
  · have hk4 : 4 ≤ k := by omega
    have hdiff1 : (r₁ : ℤ) - b₁ ≤ 2 ∧ -2 ≤ (r₁ : ℤ) - b₁ := by
      rcases hc₁ with h1 | h1 | h1 | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    have hdiff2 : (r₂ : ℤ) - b₂ ≤ 2 ∧ -2 ≤ (r₂ : ℤ) - b₂ := by
      rcases hc₂ with h2 | h2 | h2 | ⟨h2, _⟩ | ⟨h2, _⟩ <;> omega
    have hz : ((b₁ : ℤ) - b₂) * (k + 1 : ℤ) = ((r₂ : ℤ) - b₂) - ((r₁ : ℤ) - b₁) := by
      have heqz : (r₁ : ℤ) + (k : ℤ) * b₁ = (r₂ : ℤ) + (k : ℤ) * b₂ := by exact_mod_cast heq
      linarith
    have hb : (b₁ : ℤ) = b₂ := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : (b₁ : ℤ) - b₂ ≤ -1 := by omega
        have hmul : ((b₁ : ℤ) - b₂) * (k + 1 : ℤ) ≤ -(k + 1 : ℤ) := by nlinarith
        omega
      · have hge : 1 ≤ (b₁ : ℤ) - b₂ := by omega
        have hmul : (k + 1 : ℤ) ≤ ((b₁ : ℤ) - b₂) * (k + 1 : ℤ) := by nlinarith
        omega
    have hb_nat : b₁ = b₂ := by exact_mod_cast hb
    subst hb_nat
    exact Prod.ext (by omega) rfl

def numPairs : List (ℕ × ℕ × Bool) → Multiset (ℕ × ℕ)
  | [] => 0
  | (r, b, true) :: L => (2 * r, 2 * b) ::ₘ numPairs L
  | (r, b, false) :: L => (r, b) ::ₘ numPairs L

def denPairs : List (ℕ × ℕ × Bool) → Multiset (ℕ × ℕ)
  | [] => 0
  | (r, b, true) :: L => (r, b) ::ₘ denPairs L
  | (_, _, false) :: L => denPairs L

def prodOneMinus (M : Multiset (ℕ × ℕ)) (u v : ℚ) : ℚ :=
  (M.map (fun ab => 1 - u ^ ab.1 * v ^ ab.2)).prod

noncomputable def prodOneMinusPoly (M : Multiset ℕ) : Polynomial ℚ :=
  (M.map (fun e => 1 - Polynomial.X ^ e)).prod

lemma prodOneMinus_add (M₁ M₂ : Multiset (ℕ × ℕ)) (u v : ℚ) :
    prodOneMinus (M₁ + M₂) u v = prodOneMinus M₁ u v * prodOneMinus M₂ u v := by
  simp [prodOneMinus, Multiset.map_add, Multiset.prod_add]

lemma prodOneMinusPoly_add (M₁ M₂ : Multiset ℕ) :
    prodOneMinusPoly (M₁ + M₂) = prodOneMinusPoly M₁ * prodOneMinusPoly M₂ := by
  simp [prodOneMinusPoly, Multiset.map_add, Multiset.prod_add]

lemma eval_prodOneMinusPoly (k : ℕ) (M : Multiset (ℕ × ℕ)) (z : ℚ) :
    (prodOneMinusPoly (M.map (fun ab => ab.1 + k * ab.2))).eval z = prodOneMinus M z (z ^ k) := by
  induction M using Multiset.induction_on with
  | empty => simp [prodOneMinusPoly, prodOneMinus]
  | @cons ab M ih =>
    simp only [prodOneMinusPoly, prodOneMinus, Multiset.map_cons, Multiset.prod_cons,
      Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow,
      Polynomial.eval_X] at ih ⊢
    rw [ih, pow_add, pow_mul]

lemma numPairs_good (L : List (ℕ × ℕ × Bool))
    (hL : ∀ a ∈ L, 0 < a.1 + a.2.1 ∧ a.1 ≤ a.2.1 + 1 ∧ a.2.1 ≤ a.1 + 1) :
    ∀ ab ∈ numPairs L, GoodPair ab := by
  induction L with
  | nil => intro ab h; simp [numPairs] at h
  | cons a L ih =>
    rcases a with ⟨r, b, sg⟩
    have ha := hL (r, b, sg) (List.mem_cons_self ..)
    have hL' : ∀ x ∈ L, 0 < x.1 + x.2.1 ∧ x.1 ≤ x.2.1 + 1 ∧ x.2.1 ≤ x.1 + 1 :=
      fun x hx => hL x (List.mem_cons_of_mem _ hx)
    cases sg
    · intro ab hab
      simp only [numPairs, Multiset.mem_cons] at hab
      rcases hab with rfl | hmem
      · exact goodPair_of_arc ha.1 ha.2.1 ha.2.2
      · exact ih hL' ab hmem
    · intro ab hab
      simp only [numPairs, Multiset.mem_cons] at hab
      rcases hab with rfl | hmem
      · exact goodPair_double_of_arc ha.1 ha.2.1 ha.2.2
      · exact ih hL' ab hmem

lemma denPairs_good (L : List (ℕ × ℕ × Bool))
    (hL : ∀ a ∈ L, 0 < a.1 + a.2.1 ∧ a.1 ≤ a.2.1 + 1 ∧ a.2.1 ≤ a.1 + 1) :
    ∀ ab ∈ denPairs L, GoodPair ab := by
  induction L with
  | nil => intro ab h; simp [denPairs] at h
  | cons a L ih =>
    rcases a with ⟨r, b, sg⟩
    have ha := hL (r, b, sg) (List.mem_cons_self ..)
    have hL' : ∀ x ∈ L, 0 < x.1 + x.2.1 ∧ x.1 ≤ x.2.1 + 1 ∧ x.2.1 ≤ x.1 + 1 :=
      fun x hx => hL x (List.mem_cons_of_mem _ hx)
    cases sg
    · exact ih hL'
    · intro ab hab
      simp only [denPairs, Multiset.mem_cons] at hab
      rcases hab with rfl | hmem
      · exact goodPair_of_arc ha.1 ha.2.1 ha.2.2
      · exact ih hL' ab hmem

lemma list_arc_mul_den (L : List (ℕ × ℕ × Bool)) (u v : ℚ) :
    (L.map (fun a => 1 + (if a.2.2 then (1 : ℚ) else -1) * u ^ a.1 * v ^ a.2.1)).prod *
      prodOneMinus (denPairs L) u v =
    prodOneMinus (numPairs L) u v := by
  induction L with
  | nil => simp [denPairs, numPairs, prodOneMinus]
  | cons a L ih =>
    rcases a with ⟨r, b, sg⟩
    cases sg
    · simp only [List.map_cons, List.prod_cons, Bool.false_eq_true, ↓reduceIte, denPairs, numPairs,
        prodOneMinus, Multiset.map_cons, Multiset.prod_cons] at ih ⊢
      rw [mul_assoc, ih]
      ring
    · simp only [List.map_cons, List.prod_cons, ↓reduceIte, denPairs, numPairs,
        prodOneMinus, Multiset.map_cons, Multiset.prod_cons] at ih ⊢
      have h1 : (1 + 1 * u ^ r * v ^ b) * (1 - u ^ r * v ^ b) =
          1 - u ^ (2 * r) * v ^ (2 * b) := by
        rw [two_mul, two_mul, pow_add, pow_add]
        ring
      calc
        ((1 + 1 * u ^ r * v ^ b) *
          (L.map (fun a => 1 + (if a.2.2 then (1 : ℚ) else -1) * u ^ a.1 * v ^ a.2.1)).prod) *
          ((1 - u ^ r * v ^ b) * ((denPairs L).map (fun ab => 1 - u ^ ab.1 * v ^ ab.2)).prod)
          = ((1 + 1 * u ^ r * v ^ b) * (1 - u ^ r * v ^ b)) *
            ((L.map (fun a => 1 + (if a.2.2 then (1 : ℚ) else -1) * u ^ a.1 * v ^ a.2.1)).prod *
              ((denPairs L).map (fun ab => 1 - u ^ ab.1 * v ^ ab.2)).prod) := by ring
        _ = (1 - u ^ (2 * r) * v ^ (2 * b)) *
            ((numPairs L).map (fun ab => 1 - u ^ ab.1 * v ^ ab.2)).prod := by rw [h1, ih]

lemma eval_zero_prodOneMinusPoly (M : Multiset ℕ) (hM : ∀ e ∈ M, 0 < e) :
    (prodOneMinusPoly M).eval 0 = 1 := by
  induction M using Multiset.induction_on with
  | empty => simp [prodOneMinusPoly]
  | @cons e M ih =>
    simp only [prodOneMinusPoly, Multiset.map_cons, Multiset.prod_cons, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X]
    have he : 0 < e := hM e (Multiset.mem_cons_self e M)
    have hM' : ∀ x ∈ M, 0 < x := fun x hx => hM x (Multiset.mem_cons_of_mem hx)
    rw [zero_pow (Nat.ne_of_gt he), sub_zero, one_mul]
    exact ih hM'

lemma coeff_prodOneMinusPoly {d : ℕ} (hd : 0 < d) (M : Multiset ℕ) (hM : ∀ e ∈ M, d ≤ e) :
    (prodOneMinusPoly M).coeff 0 = 1 ∧
    (∀ j, 0 < j → j < d → (prodOneMinusPoly M).coeff j = 0) ∧
    (prodOneMinusPoly M).coeff d = -(M.count d : ℚ) := by
  induction M using Multiset.induction_on with
  | empty =>
    simp only [prodOneMinusPoly, Multiset.map_zero, Multiset.prod_zero, Polynomial.coeff_one,
      ↓reduceIte, Multiset.count_zero, Nat.cast_zero, neg_zero, true_and]
    exact ⟨fun j hj _ => by simp [Nat.ne_of_gt hj], by simp [Nat.ne_of_gt hd]⟩
  | @cons e M ih =>
    have he : d ≤ e := hM e (Multiset.mem_cons_self e M)
    have hM' : ∀ x ∈ M, d ≤ x := fun x hx => hM x (Multiset.mem_cons_of_mem hx)
    obtain ⟨h0, hlt, hcd⟩ := ih hM'
    set P := prodOneMinusPoly M
    have hmul : prodOneMinusPoly (e ::ₘ M) = P - Polynomial.X ^ e * P := by
      simp only [prodOneMinusPoly, Multiset.map_cons, Multiset.prod_cons, P]
      ring
    rw [hmul]
    have hcoeff_sub : ∀ m, (P - Polynomial.X ^ e * P).coeff m =
        P.coeff m - (if e ≤ m then P.coeff (m - e) else 0) := by
      intro m
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul']
    refine ⟨?_, ?_, ?_⟩
    · rw [hcoeff_sub 0, h0]
      have : ¬ (e ≤ 0) := by omega
      simp [this]
    · intro j hj hjd
      rw [hcoeff_sub j, hlt j hj hjd]
      have : ¬ (e ≤ j) := by omega
      simp [this]
    · rw [hcoeff_sub d, hcd]
      by_cases hed : e = d
      · subst hed
        simp only [le_refl, ↓reduceIte, Nat.sub_self, h0, Multiset.count_cons_self, Nat.cast_add,
          Nat.cast_one]
        ring
      · have hne : ¬ (e ≤ d) := by omega
        have hne' : d ≠ e := Ne.symm hed
        simp [hne, Multiset.count_cons_of_ne hne']

lemma multiset_eq_of_prodOneMinusPoly_eq (M₁ M₂ : Multiset ℕ)
    (h₁ : ∀ e ∈ M₁, 0 < e) (h₂ : ∀ e ∈ M₂, 0 < e)
    (heq : prodOneMinusPoly M₁ = prodOneMinusPoly M₂) : M₁ = M₂ := by
  let C := M₁ ∩ M₂
  let A := M₁ - C
  let B := M₂ - C
  have hCA : A + C = M₁ := Multiset.sub_add_cancel Multiset.inter_le_left
  have hCB : B + C = M₂ := Multiset.sub_add_cancel Multiset.inter_le_right
  have hApos : ∀ e ∈ A, 0 < e := fun e he => h₁ e (hCA ▸ Multiset.mem_add.mpr (Or.inl he))
  have hBpos : ∀ e ∈ B, 0 < e := fun e he => h₂ e (hCB ▸ Multiset.mem_add.mpr (Or.inl he))
  have hCpos : ∀ e ∈ C, 0 < e := fun e he => h₁ e (hCA ▸ Multiset.mem_add.mpr (Or.inr he))
  have hCnz : prodOneMinusPoly C ≠ 0 := by
    intro h0
    have := eval_zero_prodOneMinusPoly C hCpos
    rw [h0, Polynomial.eval_zero] at this
    norm_num at this
  have hABeq : prodOneMinusPoly A = prodOneMinusPoly B := by
    apply mul_right_cancel₀ hCnz
    rw [← prodOneMinusPoly_add, ← prodOneMinusPoly_add, hCA, hCB, heq]
  have hdisj : ∀ e, ¬ (e ∈ A ∧ e ∈ B) := by
    intro e ⟨heA, heB⟩
    have hcA : 0 < A.count e := Multiset.count_pos.mpr heA
    have hcB : 0 < B.count e := Multiset.count_pos.mpr heB
    simp only [A, B, C, Multiset.count_sub, Multiset.count_inter] at hcA hcB
    omega
  have hAB : A = B := by
    by_contra hne
    have hne_sum : (A + B).toFinset.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hA0 : A = 0 := by
        rw [Multiset.eq_zero_iff_forall_notMem]
        intro e he
        have : e ∈ (A + B).toFinset := Multiset.mem_toFinset.mpr (Multiset.mem_add.mpr (Or.inl he))
        rw [hempty] at this
        exact Finset.notMem_empty e this
      have hB0 : B = 0 := by
        rw [Multiset.eq_zero_iff_forall_notMem]
        intro e he
        have : e ∈ (A + B).toFinset := Multiset.mem_toFinset.mpr (Multiset.mem_add.mpr (Or.inr he))
        rw [hempty] at this
        exact Finset.notMem_empty e this
      exact hne (hA0.trans hB0.symm)
    set d := (A + B).toFinset.min' hne_sum
    have hd_mem : d ∈ A + B := Multiset.mem_toFinset.mp (Finset.min'_mem _ hne_sum)
    have hd_pos : 0 < d := by
      rcases Multiset.mem_add.mp hd_mem with h | h
      · exact hApos d h
      · exact hBpos d h
    have hd_le_A : ∀ e ∈ A, d ≤ e := fun e he =>
      Finset.min'_le _ e (Multiset.mem_toFinset.mpr (Multiset.mem_add.mpr (Or.inl he)))
    have hd_le_B : ∀ e ∈ B, d ≤ e := fun e he =>
      Finset.min'_le _ e (Multiset.mem_toFinset.mpr (Multiset.mem_add.mpr (Or.inr he)))
    have hcA := (coeff_prodOneMinusPoly hd_pos A hd_le_A).2.2
    have hcB := (coeff_prodOneMinusPoly hd_pos B hd_le_B).2.2
    rw [hABeq] at hcA
    have hcnt : A.count d = B.count d := by
      have : -(A.count d : ℚ) = -(B.count d : ℚ) := hcA.symm.trans hcB
      exact_mod_cast neg_inj.mp this
    rcases Multiset.mem_add.mp hd_mem with hdA | hdB
    · have hposA : 0 < A.count d := Multiset.count_pos.mpr hdA
      have hdB : d ∈ B := Multiset.count_pos.mp (hcnt ▸ hposA)
      exact hdisj d ⟨hdA, hdB⟩
    · have hposB : 0 < B.count d := Multiset.count_pos.mpr hdB
      have hdA : d ∈ A := Multiset.count_pos.mp (hcnt.symm ▸ hposB)
      exact hdisj d ⟨hdA, hdB⟩
  rw [← hCA, ← hCB, hAB]

lemma multiset_eq_of_map_inj {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : α → Prop) (f : α → β)
    (hinj : ∀ x y, P x → P y → f x = f y → x = y)
    (M₁ M₂ : Multiset α) (h₁ : ∀ x ∈ M₁, P x) (h₂ : ∀ y ∈ M₂, P y)
    (hmap : M₁.map f = M₂.map f) : M₁ = M₂ := by
  induction M₁ using Multiset.induction_on generalizing M₂ with
  | empty =>
    simp only [Multiset.map_zero] at hmap
    exact (Multiset.map_eq_zero.mp hmap.symm).symm
  | @cons a M₁ ih =>
    have haP : P a := h₁ a (Multiset.mem_cons_self a M₁)
    have hfa : f a ∈ M₂.map f := by
      rw [← hmap]; exact Multiset.mem_map_of_mem f (Multiset.mem_cons_self a M₁)
    rw [Multiset.mem_map] at hfa
    obtain ⟨b, hbM₂, hfb⟩ := hfa
    have hab : a = b := hinj a b haP (h₂ b hbM₂) hfb.symm
    subst hab
    have hcons : M₂ = a ::ₘ (M₂.erase a) := (Multiset.cons_erase hbM₂).symm
    rw [hcons] at hmap ⊢
    congr 1
    apply ih (M₂.erase a) (fun x hx => h₁ x (Multiset.mem_cons_of_mem hx))
      (fun y hy => h₂ y (Multiset.mem_of_mem_erase hy))
    simp only [Multiset.map_cons] at hmap
    exact Multiset.ext.mpr (fun x => by
      have hc := congrArg (Multiset.count x) hmap
      simp only [Multiset.count_cons] at hc
      split_ifs at hc <;> omega)

lemma eval_sum_poly {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℚ) (z : ℚ) :
    (∑ i ∈ s, f i).eval z = ∑ i ∈ s, (f i).eval z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.eval_add, ih]

lemma coeff_sum_poly {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℚ) (m : ℕ) :
    (∑ i ∈ s, f i).coeff m = ∑ i ∈ s, (f i).coeff m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.coeff_add, ih]

lemma rat_div_lt_one {a b : ℚ} (hb : 0 < b) (hab : a < b) : a / b < 1 := by
  have h1 : a * b⁻¹ < b * b⁻¹ := mul_lt_mul_of_pos_right hab (inv_pos.mpr hb)
  rwa [mul_inv_cancel₀ hb.ne', ← div_eq_mul_inv] at h1

lemma natDegree_poly_term_le {n k : ℕ} (c : ℚ) (r b : Fin (n + 1)) :
    (Polynomial.C c *
      (1 - Polynomial.X) ^ r.val * (1 + Polynomial.X) ^ (n - r.val) *
      (1 - Polynomial.X ^ k) ^ b.val * (1 + Polynomial.X ^ k) ^ (n - b.val)).natDegree ≤
    (k + 1) * n := by
  have hd1 : (1 - (Polynomial.X : Polynomial ℚ)).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    simp
  have hd2 : (1 + (Polynomial.X : Polynomial ℚ)).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    simp
  have hd3 : (1 - (Polynomial.X : Polynomial ℚ) ^ k).natDegree ≤ k := by
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    simp
  have hd4 : (1 + (Polynomial.X : Polynomial ℚ) ^ k).natDegree ≤ k := by
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    simp
  have hp1 : ((1 - (Polynomial.X : Polynomial ℚ)) ^ r.val).natDegree ≤ r.val :=
    (Polynomial.natDegree_pow_le).trans (by nlinarith)
  have hp2 : ((1 + (Polynomial.X : Polynomial ℚ)) ^ (n - r.val)).natDegree ≤ n - r.val :=
    (Polynomial.natDegree_pow_le).trans (by nlinarith)
  have hp3 : ((1 - (Polynomial.X : Polynomial ℚ) ^ k) ^ b.val).natDegree ≤ k * b.val :=
    (Polynomial.natDegree_pow_le).trans (by nlinarith)
  have hp4 : ((1 + (Polynomial.X : Polynomial ℚ) ^ k) ^ (n - b.val)).natDegree ≤ k * (n - b.val) :=
    (Polynomial.natDegree_pow_le).trans (by nlinarith)
  have hle1 := Polynomial.natDegree_mul_le (p := Polynomial.C c *
      (1 - Polynomial.X) ^ r.val * (1 + Polynomial.X) ^ (n - r.val) *
      (1 - Polynomial.X ^ k) ^ b.val) (q := (1 + Polynomial.X ^ k) ^ (n - b.val))
  have hle2 := Polynomial.natDegree_mul_le (p := Polynomial.C c *
      (1 - Polynomial.X) ^ r.val * (1 + Polynomial.X) ^ (n - r.val))
      (q := (1 - Polynomial.X ^ k) ^ b.val)
  have hle3 := Polynomial.natDegree_mul_le (p := Polynomial.C c *
      (1 - Polynomial.X) ^ r.val) (q := (1 + Polynomial.X) ^ (n - r.val))
  have hle4 := Polynomial.natDegree_mul_le (p := Polynomial.C c) (q := (1 - Polynomial.X) ^ r.val)
  have hC : (Polynomial.C c).natDegree = 0 := Polynomial.natDegree_C c
  have hr : r.val ≤ n := Nat.le_of_lt_succ r.isLt
  have hb : b.val ≤ n := Nat.le_of_lt_succ b.isLt
  have hsum : r.val + (n - r.val) + (k * b.val + k * (n - b.val)) = (k + 1) * n := by
    have h1 : r.val + (n - r.val) = n := Nat.add_sub_of_le hr
    have h2 : k * b.val + k * (n - b.val) = k * n := by
      rw [← mul_add, Nat.add_sub_of_le hb]
    rw [h1, h2]; ring
  omega

noncomputable def polyZ (n k : ℕ) (σ : Fin n → Fin n) (p : Bool × Fin n → Option Bool) : Polynomial ℚ :=
  ∑ r : Fin (n + 1), ∑ b : Fin (n + 1),
    Polynomial.C (lawDef n σ p r b) *
    (1 - Polynomial.X) ^ r.val * (1 + Polynomial.X) ^ (n - r.val) *
    (1 - Polynomial.X ^ k) ^ b.val * (1 + Polynomial.X ^ k) ^ (n - b.val)

lemma eval_polyZ (n k : ℕ) (σ : Fin n → Fin n) (p : Bool × Fin n → Option Bool) (z : ℚ) :
    (polyZ n k σ p).eval z = polyDef n σ p z (z ^ k) := by
  unfold polyZ polyDef
  rw [eval_sum_poly]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [eval_sum_poly]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]

lemma natDegree_polyZ_le (n k : ℕ) (σ : Fin n → Fin n) (p : Bool × Fin n → Option Bool) :
    (polyZ n k σ p).natDegree ≤ (k + 1) * n := by
  unfold polyZ
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun r _ => ?_)
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun b _ => ?_)
  exact natDegree_poly_term_le _ r b

lemma polyZ_eq_of_samples_eq {n k : ℕ} {σ τ : Fin n → Fin n}
    {p q : Bool × Fin n → Option Bool}
    (h : ∀ i : Fin ((k + 1) * n + 1),
      polyDef n σ p (i.val : ℚ) ((i.val : ℚ) ^ k) =
      polyDef n τ q (i.val : ℚ) ((i.val : ℚ) ^ k)) :
    polyZ n k σ p = polyZ n k τ q := by
  set d := polyZ n k σ p - polyZ n k τ q
  have hdeg : d.natDegree ≤ (k + 1) * n :=
    (Polynomial.natDegree_sub_le _ _).trans
      (max_le (natDegree_polyZ_le n k σ p) (natDegree_polyZ_le n k τ q))
  set pts : Finset ℚ := (Finset.univ : Finset (Fin ((k + 1) * n + 1))).image (fun i => (i.val : ℚ))
  have hcard : pts.card = (k + 1) * n + 1 := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      exact Fin.ext (Nat.cast_injective hab)
  have hzero : d = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' d pts ?_ (by omega)
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨i, _, rfl⟩ := hz
    simp only [d, Polynomial.eval_sub, eval_polyZ, h i, sub_self]
  exact sub_eq_zero.mp hzero

lemma prodOneMinus_pos {M : Multiset (ℕ × ℕ)} (hM : ∀ ab ∈ M, 0 < ab.1 + ab.2)
    {u v : ℚ} (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) :
    0 < prodOneMinus M u v := by
  induction M using Multiset.induction_on with
  | empty => simp [prodOneMinus]
  | @cons ab M ih =>
    simp only [prodOneMinus, Multiset.map_cons, Multiset.prod_cons]
    have hab : 0 < ab.1 + ab.2 := hM ab (Multiset.mem_cons_self ab M)
    have hM' : ∀ x ∈ M, 0 < x.1 + x.2 := fun x hx => hM x (Multiset.mem_cons_of_mem hx)
    have hlt1 : u ^ ab.1 * v ^ ab.2 < 1 := by
      have hu_le : u ^ ab.1 ≤ 1 := pow_le_one₀ hu0.le hu1.le
      have hv_le : v ^ ab.2 ≤ 1 := pow_le_one₀ hv0.le hv1.le
      have hu_pos : 0 < u ^ ab.1 := pow_pos hu0 _
      have hv_pos : 0 < v ^ ab.2 := pow_pos hv0 _
      by_cases ha : 0 < ab.1
      · have hult : u ^ ab.1 < 1 := pow_lt_one₀ hu0.le hu1 (Nat.ne_of_gt ha)
        nlinarith
      · have hb : 0 < ab.2 := by omega
        have hvlt : v ^ ab.2 < 1 := pow_lt_one₀ hv0.le hv1 (Nat.ne_of_gt hb)
        nlinarith
    exact mul_pos (sub_pos.mpr hlt1) (ih hM')

lemma coeff_eq_zero_of_poly_eval_unit {n : ℕ} (c : Fin (n + 1) → ℚ)
    (heval : ∀ a : Fin (n + 1), ∑ r : Fin (n + 1), c r * ((1 : ℚ) / (a.val + 2 : ℚ)) ^ r.val = 0) :
    ∀ r : Fin (n + 1), c r = 0 := by
  let P : Polynomial ℚ := ∑ r : Fin (n + 1), Polynomial.C (c r) * Polynomial.X ^ r.val
  have hdeg : P.natDegree ≤ n := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun r _ => ?_)
    refine (Polynomial.natDegree_mul_le).trans ?_
    simp only [Polynomial.natDegree_C, zero_add, Polynomial.natDegree_X_pow]
    exact Nat.le_of_lt_succ r.isLt
  set pts : Finset ℚ := (Finset.univ : Finset (Fin (n + 1))).image
    (fun a => (1 : ℚ) / (a.val + 2 : ℚ))
  have hcard : pts.card = n + 1 := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      have ha0 : (a.val + 2 : ℚ) ≠ 0 := by positivity
      have hb0 : (b.val + 2 : ℚ) ≠ 0 := by positivity
      have heq : (a.val + 2 : ℚ) = (b.val + 2 : ℚ) := by
        have := (div_eq_div_iff ha0 hb0).mp hab
        linarith
      exact Fin.ext (by exact_mod_cast (show (a.val : ℚ) = (b.val : ℚ) by linarith))
  have hP0 : P = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P pts ?_ (by omega)
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨a, _, rfl⟩ := hx
    dsimp only [P]
    rw [eval_sum_poly]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact heval a
  intro r
  have hcoeff := congrArg (fun f : Polynomial ℚ => f.coeff r.val) hP0
  dsimp only [P] at hcoeff
  rw [coeff_sum_poly, Polynomial.coeff_zero] at hcoeff
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero] at hcoeff
  rw [Finset.sum_eq_single r] at hcoeff
  · simpa using hcoeff
  · intro s _ hsr
    have hne : r.val ≠ s.val := fun h => hsr (Fin.ext h.symm)
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ r) h

lemma law_eq_of_polyDef_eq_open {n : ℕ} {σ τ : Fin n → Fin n}
    {p q : Bool × Fin n → Option Bool}
    (h : ∀ u v : ℚ, 0 < u → u < 1 → 0 < v → v < 1 → polyDef n σ p u v = polyDef n τ q u v) :
    lawDef n σ p = lawDef n τ q := by
  have hxy : ∀ a c : Fin (n + 1),
      ∑ r : Fin (n + 1), ∑ b : Fin (n + 1),
        (lawDef n σ p r b - lawDef n τ q r b) *
        ((1 : ℚ) / (a.val + 2 : ℚ)) ^ r.val *
        ((1 : ℚ) / (c.val + 2 : ℚ)) ^ b.val = 0 := by
    intro a c
    have ha_nn : (0 : ℚ) ≤ a.val := Nat.cast_nonneg _
    have hc_nn : (0 : ℚ) ≤ c.val := Nat.cast_nonneg _
    have ha2 : (0 : ℚ) < (a.val : ℚ) + 2 := by linarith
    have hc2 : (0 : ℚ) < (c.val : ℚ) + 2 := by linarith
    set x : ℚ := 1 / (a.val + 2 : ℚ)
    set y : ℚ := 1 / (c.val + 2 : ℚ)
    have hx0 : 0 < x := div_pos one_pos ha2
    have hx1 : x < 1 := rat_div_lt_one ha2 (by linarith)
    have hy0 : 0 < y := div_pos one_pos hc2
    have hy1 : y < 1 := rat_div_lt_one hc2 (by linarith)
    set u : ℚ := (1 - x) / (1 + x)
    set v : ℚ := (1 - y) / (1 + y)
    have h1px : (0 : ℚ) < 1 + x := by linarith
    have h1py : (0 : ℚ) < 1 + y := by linarith
    have hu0 : 0 < u := div_pos (by linarith) h1px
    have hu1 : u < 1 := rat_div_lt_one h1px (by linarith)
    have hv0 : 0 < v := div_pos (by linarith) h1py
    have hv1 : v < 1 := rat_div_lt_one h1py (by linarith)
    have h1mu : 1 - u = (2 / (1 + x)) * x := by
      dsimp only [u]
      rw [one_sub_div h1px.ne']
      ring
    have h1pu : 1 + u = 2 / (1 + x) := by
      dsimp only [u]
      rw [one_add_div h1px.ne']
      ring
    have h1mv : 1 - v = (2 / (1 + y)) * y := by
      dsimp only [v]
      rw [one_sub_div h1py.ne']
      ring
    have h1pv : 1 + v = 2 / (1 + y) := by
      dsimp only [v]
      rw [one_add_div h1py.ne']
      ring
    have hpow : ∀ (t s : ℚ) (m : Fin (n + 1)),
        (t * s) ^ m.val * t ^ (n - m.val) = t ^ n * s ^ m.val := by
      intro t s m
      rw [mul_pow, mul_comm (t ^ m.val) (s ^ m.val), mul_assoc, ← pow_add,
        Nat.add_sub_of_le (Nat.le_of_lt_succ m.isLt), mul_comm]
    have huv := h u v hu0 hu1 hv0 hv1
    have hrew : ∀ (ρ : Fin n → Fin n) (w : Bool × Fin n → Option Bool),
        polyDef n ρ w u v =
        (2 / (1 + x)) ^ n * (2 / (1 + y)) ^ n *
        ∑ r : Fin (n + 1), ∑ b : Fin (n + 1), lawDef n ρ w r b * x ^ r.val * y ^ b.val := by
      intro ρ w
      unfold polyDef
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [h1mu, h1pu, h1mv, h1pv]
      have hpr := hpow (2 / (1 + x)) x r
      have hpb := hpow (2 / (1 + y)) y b
      calc
        lawDef n ρ w r b * ((2 / (1 + x)) * x) ^ r.val * (2 / (1 + x)) ^ (n - r.val) *
          ((2 / (1 + y)) * y) ^ b.val * (2 / (1 + y)) ^ (n - b.val)
          = lawDef n ρ w r b *
            (((2 / (1 + x)) * x) ^ r.val * (2 / (1 + x)) ^ (n - r.val)) *
            (((2 / (1 + y)) * y) ^ b.val * (2 / (1 + y)) ^ (n - b.val)) := by ring
        _ = lawDef n ρ w r b * ((2 / (1 + x)) ^ n * x ^ r.val) *
            ((2 / (1 + y)) ^ n * y ^ b.val) := by rw [hpr, hpb]
        _ = (2 / (1 + x)) ^ n * (2 / (1 + y)) ^ n * (lawDef n ρ w r b * x ^ r.val * y ^ b.val) := by
            ring
    rw [hrew σ p, hrew τ q] at huv
    have hfac : (2 / (1 + x)) ^ n * (2 / (1 + y)) ^ n ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (div_ne_zero two_ne_zero h1px.ne'))
        (pow_ne_zero _ (div_ne_zero two_ne_zero h1py.ne'))
    have hsum_eq := mul_left_cancel₀ hfac huv
    have hsub :
        (∑ r : Fin (n + 1), ∑ b : Fin (n + 1),
          (lawDef n σ p r b - lawDef n τ q r b) * x ^ r.val * y ^ b.val) =
        (∑ r : Fin (n + 1), ∑ b : Fin (n + 1), lawDef n σ p r b * x ^ r.val * y ^ b.val) -
        (∑ r : Fin (n + 1), ∑ b : Fin (n + 1), lawDef n τ q r b * x ^ r.val * y ^ b.val) := by
      simp_rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun b _ => ?_))
      ring
    rw [hsub, hsum_eq, sub_self]
  have hinner : ∀ (a b : Fin (n + 1)),
      ∑ r : Fin (n + 1), (lawDef n σ p r b - lawDef n τ q r b) *
        ((1 : ℚ) / (a.val + 2 : ℚ)) ^ r.val = 0 := by
    intro a
    apply coeff_eq_zero_of_poly_eval_unit
    intro c
    have hc := hxy a c
    rw [Finset.sum_comm] at hc
    simpa [Finset.sum_mul] using hc
  funext r b
  have hr : lawDef n σ p r b - lawDef n τ q r b = 0 :=
    coeff_eq_zero_of_poly_eval_unit (fun r => lawDef n σ p r b - lawDef n τ q r b)
      (fun a => hinner a b) r
  exact sub_eq_zero.mp hr

lemma part1 {n k : ℕ} (hk : 3 ≤ k) (σ τ : Equiv.Perm (Fin n))
    (p q : Bool × Fin n → Option Bool)
    (hsamp : ∀ i : Fin ((k + 1) * n + 1),
      polyDef n σ p (i.val : ℚ) ((i.val : ℚ) ^ k) =
      polyDef n τ q (i.val : ℚ) ((i.val : ℚ) ^ k)) :
    lawDef n σ p = lawDef n τ q := by
  have hpolyZ : polyZ n k σ p = polyZ n k τ q := polyZ_eq_of_samples_eq hsamp
  obtain ⟨L₁, hL₁, hP₁⟩ := exists_arc_factors σ p
  obtain ⟨L₂, hL₂, hP₂⟩ := exists_arc_factors τ q
  set N₁ := numPairs L₁
  set D₁ := denPairs L₁
  set N₂ := numPairs L₂
  set D₂ := denPairs L₂
  have hN₁g : ∀ ab ∈ N₁, GoodPair ab := numPairs_good L₁ hL₁
  have hD₁g : ∀ ab ∈ D₁, GoodPair ab := denPairs_good L₁ hL₁
  have hN₂g : ∀ ab ∈ N₂, GoodPair ab := numPairs_good L₂ hL₂
  have hD₂g : ∀ ab ∈ D₂, GoodPair ab := denPairs_good L₂ hL₂
  have hmul₁ : ∀ u v : ℚ, polyDef n σ p u v * prodOneMinus D₁ u v = prodOneMinus N₁ u v := by
    intro u v; rw [hP₁]; exact list_arc_mul_den L₁ u v
  have hmul₂ : ∀ u v : ℚ, polyDef n τ q u v * prodOneMinus D₂ u v = prodOneMinus N₂ u v := by
    intro u v; rw [hP₂]; exact list_arc_mul_den L₂ u v
  let φ : ℕ × ℕ → ℕ := fun ab => ab.1 + k * ab.2
  have hpoly_cross :
      prodOneMinusPoly ((N₁ + D₂).map φ) = prodOneMinusPoly ((N₂ + D₁).map φ) := by
    set A := prodOneMinusPoly ((N₁ + D₂).map φ)
    set B := prodOneMinusPoly ((N₂ + D₁).map φ)
    have hval : ∀ z : ℚ, A.eval z = B.eval z := by
      intro z
      simp only [A, B, φ, eval_prodOneMinusPoly, prodOneMinus_add]
      have hz := congrArg (fun f : Polynomial ℚ => f.eval z) hpolyZ
      simp only [eval_polyZ] at hz
      calc
        prodOneMinus N₁ z (z ^ k) * prodOneMinus D₂ z (z ^ k)
          = polyDef n σ p z (z ^ k) * prodOneMinus D₁ z (z ^ k) * prodOneMinus D₂ z (z ^ k) := by
            rw [hmul₁]
        _ = polyDef n τ q z (z ^ k) * prodOneMinus D₂ z (z ^ k) * prodOneMinus D₁ z (z ^ k) := by
            rw [hz]; ring
        _ = prodOneMinus N₂ z (z ^ k) * prodOneMinus D₁ z (z ^ k) := by rw [hmul₂]
    set diff := A - B
    set m := diff.natDegree + 1
    set pts : Finset ℚ := (Finset.univ : Finset (Fin m)).image (fun i => (i.val : ℚ))
    have hcard : pts.card = m := by
      rw [Finset.card_image_of_injective]
      · simp
      · intro a b hab; exact Fin.ext (Nat.cast_injective hab)
    have hdiff0 : diff = 0 := by
      refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' diff pts ?_ (by omega)
      intro z _
      simp only [diff, Polynomial.eval_sub, hval z, sub_self]
    exact sub_eq_zero.mp hdiff0
  have hpos_φ : ∀ ab, GoodPair ab → 0 < φ ab := by
    intro ab hab
    have := hab.1
    dsimp only [φ]
    nlinarith
  have hmap_eq : (N₁ + D₂).map φ = (N₂ + D₁).map φ := by
    refine multiset_eq_of_prodOneMinusPoly_eq _ _ ?_ ?_ hpoly_cross
    · intro e he
      rw [Multiset.mem_map] at he
      obtain ⟨ab, hab, rfl⟩ := he
      rcases Multiset.mem_add.mp hab with h | h
      · exact hpos_φ ab (hN₁g ab h)
      · exact hpos_φ ab (hD₂g ab h)
    · intro e he
      rw [Multiset.mem_map] at he
      obtain ⟨ab, hab, rfl⟩ := he
      rcases Multiset.mem_add.mp hab with h | h
      · exact hpos_φ ab (hN₂g ab h)
      · exact hpos_φ ab (hD₁g ab h)
  have hmulti_eq : N₁ + D₂ = N₂ + D₁ := by
    refine multiset_eq_of_map_inj GoodPair φ (fun x y hx hy => goodPair_inj hk hx hy)
      (N₁ + D₂) (N₂ + D₁) ?_ ?_ hmap_eq
    · intro ab hab
      rcases Multiset.mem_add.mp hab with h | h
      · exact hN₁g ab h
      · exact hD₂g ab h
    · intro ab hab
      rcases Multiset.mem_add.mp hab with h | h
      · exact hN₂g ab h
      · exact hD₁g ab h
  apply law_eq_of_polyDef_eq_open
  intro u v hu0 hu1 hv0 hv1
  have hD₁pos : 0 < prodOneMinus D₁ u v :=
    prodOneMinus_pos (fun ab hab => (hD₁g ab hab).1) hu0 hu1 hv0 hv1
  have hD₂pos : 0 < prodOneMinus D₂ u v :=
    prodOneMinus_pos (fun ab hab => (hD₂g ab hab).1) hu0 hu1 hv0 hv1
  have hprod : prodOneMinus (N₁ + D₂) u v = prodOneMinus (N₂ + D₁) u v := by
    rw [hmulti_eq]
  rw [prodOneMinus_add, prodOneMinus_add, ← hmul₁, ← hmul₂] at hprod
  have hcancel : (polyDef n σ p u v) * (prodOneMinus D₁ u v * prodOneMinus D₂ u v) =
      (polyDef n τ q u v) * (prodOneMinus D₁ u v * prodOneMinus D₂ u v) := by
    linarith
  exact mul_right_cancel₀ (mul_pos hD₁pos hD₂pos).ne' hcancel

def ringPerm (t : ℕ) : Equiv.Perm (Fin (t + 1)) where
  toFun i := i + 1
  invFun i := i - 1
  left_inv i := add_sub_cancel_right i 1
  right_inv i := sub_add_cancel i 1

def posEquiv (t : ℕ) : Fin (2 * (t + 1)) ≃ Bool × Fin (t + 1) where
  toFun j := (decide (j.val % 2 = 1), ⟨j.val / 2, by omega⟩)
  invFun e := ⟨2 * e.2.val + if e.1 then 1 else 0, by cases e.1 <;> simp <;> omega⟩
  left_inv j := by
    apply Fin.ext
    dsimp only
    by_cases h : j.val % 2 = 1
    · simp only [h, decide_true, ↓reduceIte]; omega
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]; omega
  right_inv e := by
    rcases e with ⟨b, ⟨i, hi⟩⟩
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      apply Prod.ext
      · simp
      · apply Fin.ext; dsimp only; omega
    · simp only [↓reduceIte]
      apply Prod.ext
      · simp
      · apply Fin.ext; dsimp only; omega

lemma nextE_posEquiv (t : ℕ) (j : Fin (2 * (t + 1))) :
    nextE (ringPerm t) (posEquiv t j) = posEquiv t (j + 1) := by
  have hj1 : (j + 1 : Fin (2 * (t + 1))).val = (j.val + 1) % (2 * (t + 1)) := by
    change (j.val + (1 : Fin (2 * (t + 1))).val) % (2 * (t + 1)) = _
    have h1 : (1 : Fin (2 * (t + 1))).val = 1 :=
      Nat.mod_eq_of_lt (show (1 : ℕ) < 2 * (t + 1) by omega)
    rw [h1]
  apply Prod.ext
  · dsimp only [nextE, posEquiv, Equiv.coe_fn_mk]
    by_cases h : j.val % 2 = 1
    · simp only [h, decide_true]
      symm
      rw [decide_eq_false_iff_not, hj1]
      by_cases hlast : j.val + 1 = 2 * (t + 1)
      · rw [hlast, Nat.mod_self]; omega
      · have hlt : j.val + 1 < 2 * (t + 1) := by omega
        rw [Nat.mod_eq_of_lt hlt]; omega
    · simp only [h, decide_false]
      symm
      rw [decide_eq_true_iff, hj1]
      have hlt : j.val + 1 < 2 * (t + 1) := by omega
      rw [Nat.mod_eq_of_lt hlt]; omega
  · dsimp only [nextE, posEquiv, ringPerm, Equiv.coe_fn_mk]
    by_cases h : j.val % 2 = 1
    · simp only [h, decide_true]
      apply Fin.ext
      dsimp only
      have hfin1 : ((⟨j.val / 2, by omega⟩ : Fin (t + 1)) + 1).val = (j.val / 2 + 1) % (t + 1) := by
        change (j.val / 2 + (1 : Fin (t + 1)).val) % (t + 1) = _
        by_cases ht0 : t = 0
        · subst ht0; simp
        · have : (1 : Fin (t + 1)).val = 1 :=
            Nat.mod_eq_of_lt (show (1 : ℕ) < t + 1 by omega)
          rw [this]
      rw [hfin1, hj1]
      by_cases hlast : j.val + 1 = 2 * (t + 1)
      · rw [hlast, Nat.mod_self]
        have hdiv : j.val / 2 = t := by omega
        rw [hdiv, Nat.mod_self]
      · have hlt : j.val + 1 < 2 * (t + 1) := by omega
        rw [Nat.mod_eq_of_lt hlt]
        have hlt2 : j.val / 2 + 1 < t + 1 := by omega
        rw [Nat.mod_eq_of_lt hlt2]; omega
    · simp only [h, decide_false]
      apply Fin.ext
      dsimp only
      rw [hj1]
      have hlt : j.val + 1 < 2 * (t + 1) := by omega
      rw [Nat.mod_eq_of_lt hlt]; omega

lemma symm_nextE_posEquiv (t : ℕ) (j : Fin (2 * (t + 1))) :
    (nextE (ringPerm t)).symm (posEquiv t j) = posEquiv t (j - 1) := by
  apply (nextE (ringPerm t)).injective
  rw [Equiv.apply_symm_apply, nextE_posEquiv, sub_add_cancel]

def pOf {t : ℕ} (q0 : Fin (2 * (t + 1)) → Option Bool) : Bool × Fin (t + 1) → Option Bool :=
  fun v => q0 ((posEquiv t).symm ((headV (ringPerm t)).symm v))

def eps0 {t : ℕ} (q0 : Fin (2 * (t + 1)) → Option Bool) (j : Fin (2 * (t + 1))) : ℚ :=
  match q0 j with
  | none => 1
  | some b => sgn b

def ringW {t : ℕ} (q0 : Fin (2 * (t + 1)) → Option Bool) (u v : ℚ) (j : Fin (2 * (t + 1))) : ℚ :=
  (if j.val % 2 = 1 then v else u) * eps0 q0 j * eps0 q0 (j - 1)

lemma polyDef_ring_pOf {t : ℕ} (q0 : Fin (2 * (t + 1)) → Option Bool) (u v : ℚ) :
    polyDef (t + 1) (fun i => i + 1) (pOf q0) u v =
      ∑ S ∈ Finset.univ.filter (fun S : Fin (2 * (t + 1)) → Bool =>
        ∀ j : Fin (2 * (t + 1)), q0 j = none → S (j + 1) = S j),
        ∏ j : Fin (2 * (t + 1)), if S j then ringW q0 u v j else 1 := by
  have hring : (fun i : Fin (t + 1) => i + 1) = (ringPerm t : Fin (t + 1) → Fin (t + 1)) := rfl
  rw [hring, polyDef_eq_edgeSum]
  refine Finset.sum_bij (fun S _ => fun j => S (posEquiv t j)) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    intro j hj
    have hq : qE (ringPerm t) (pOf q0) (posEquiv t j) = none := by
      simp [qE, pOf, hj]
    have h1 := hS (posEquiv t j) hq
    rwa [nextE_posEquiv] at h1
  · intro S₁ _ S₂ _ h
    funext e
    have := congrFun h ((posEquiv t).symm e)
    simpa using this
  · intro S' hS'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS'
    refine ⟨fun e => S' ((posEquiv t).symm e), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro e he
      set j := (posEquiv t).symm e
      have hej : e = posEquiv t j := (Equiv.apply_symm_apply _ _).symm
      rw [hej] at he ⊢
      rw [nextE_posEquiv, Equiv.symm_apply_apply]
      apply hS' j
      simpa [qE, pOf] using he
    · funext j; simp
  · intro S _
    symm
    refine Fintype.prod_equiv (posEquiv t) _ _ (fun j => ?_)
    have hw : ringW q0 u v j = edgeW (ringPerm t) (pOf q0) u v (posEquiv t j) := by
      dsimp only [ringW, edgeW, epsE, epsV, eps0]
      rw [symm_nextE_posEquiv]
      simp only [pOf, Equiv.symm_apply_apply]
      dsimp only [posEquiv, Equiv.coe_fn_mk]
      simp only [decide_eq_true_eq]
    rw [hw]

lemma fin_sub_one_val {m : ℕ} [NeZero m] (hm : 2 ≤ m) (j : Fin m) :
    (j - 1 : Fin m).val = if j.val = 0 then m - 1 else j.val - 1 := by
  have h1 : (1 : Fin m).val = 1 := Nat.mod_eq_of_lt (show (1 : ℕ) < m by omega)
  have hsub : (j - 1 : Fin m).val = (j.val + (m - 1)) % m := by
    rw [Fin.val_sub, h1, add_comm]
  rw [hsub]
  by_cases hj : j.val = 0
  · simp only [hj, ↓reduceIte, zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  · simp only [hj, ↓reduceIte]
    have hsplit : j.val + (m - 1) = m + (j.val - 1) := by omega
    rw [hsplit, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

lemma fin_add_one_val {m : ℕ} [NeZero m] (hm : 2 ≤ m) (j : Fin m) :
    (j + 1 : Fin m).val = if j.val + 1 = m then 0 else j.val + 1 := by
  have h1 : (1 : Fin m).val = 1 := Nat.mod_eq_of_lt (show (1 : ℕ) < m by omega)
  have hadd : (j + 1 : Fin m).val = (j.val + 1) % m := by
    rw [Fin.val_add, h1]
  rw [hadd]
  by_cases hj : j.val + 1 = m
  · simp only [hj, ↓reduceIte, Nat.mod_self]
  · simp only [hj, ↓reduceIte]
    exact Nat.mod_eq_of_lt (by omega)

lemma prod_even_odd_tail {t : ℕ} (a : ℕ) (ha : a ≤ t + 1) (u v : ℚ) :
    (∏ j ∈ Finset.univ.filter (fun j : Fin (2 * (t + 1)) => 2 * a ≤ j.val),
      if j.val % 2 = 1 then v else u) =
    u ^ (t + 1 - a) * v ^ (t + 1 - a) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, mul_comm]
  have heven :
      ((Finset.univ.filter (fun j : Fin (2 * (t + 1)) => 2 * a ≤ j.val)).filter
        (fun j => ¬ j.val % 2 = 1)).card = t + 1 - a := by
    have hbij :
        ((Finset.univ.filter (fun j : Fin (2 * (t + 1)) => 2 * a ≤ j.val)).filter
          (fun j => ¬ j.val % 2 = 1)).card = (Finset.Ico a (t + 1)).card := by
      refine Finset.card_nbij (fun j => j.val / 2) ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [Finset.mem_coe, Finset.mem_Ico]
        omega
      · intro x hx y hy hxy
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
        dsimp only at hxy
        exact Fin.ext (by omega)
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_Ico] at hi
        refine ⟨⟨2 * i, by omega⟩, ?_, by dsimp only; omega⟩
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
    rw [hbij, Nat.card_Ico]
  have hodd :
      ((Finset.univ.filter (fun j : Fin (2 * (t + 1)) => 2 * a ≤ j.val)).filter
        (fun j => j.val % 2 = 1)).card = t + 1 - a := by
    have hbij :
        ((Finset.univ.filter (fun j : Fin (2 * (t + 1)) => 2 * a ≤ j.val)).filter
          (fun j => j.val % 2 = 1)).card = (Finset.Ico a (t + 1)).card := by
      refine Finset.card_nbij (fun j => j.val / 2) ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [Finset.mem_coe, Finset.mem_Ico]
        omega
      · intro x hx y hy hxy
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
        dsimp only at hxy
        exact Fin.ext (by omega)
      · intro i hi
        simp only [Finset.mem_coe, Finset.mem_Ico] at hi
        refine ⟨⟨2 * i + 1, by omega⟩, ?_, by dsimp only; omega⟩
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
    rw [hbij, Nat.card_Ico]
  rw [heven, hodd]

lemma part2_k1 {t : ℕ} (ht : 2 ≤ t + 1) :
    ∃ p q : Bool × Fin (t + 1) → Option Bool,
      (∀ u : ℚ, polyDef (t + 1) (fun i => i + 1) p u u =
        polyDef (t + 1) (fun i => i + 1) q u u) ∧
      lawDef (t + 1) (fun i => i + 1) p ≠ lawDef (t + 1) (fun i => i + 1) q := by
  let q1 : Fin (2 * (t + 1)) → Option Bool := fun j =>
    if j.val = 0 then some false
    else if j.val = 2 * (t + 1) - 1 then some true
    else none
  let q2 : Fin (2 * (t + 1)) → Option Bool := fun j =>
    if j.val = 0 then some true
    else if j.val = 1 then some false
    else none
  have h2m : 2 ≤ 2 * (t + 1) := by omega
  have hW1 : ∀ u v j, ringW q1 u v j =
      (if j.val % 2 = 1 then v else u) *
      (if j.val = 0 ∨ j.val = 2 * (t + 1) - 1 then -1 else 1) := by
    intro u v j
    have he1 : ∀ x : Fin (2 * (t + 1)),
        eps0 q1 x = if x.val = 2 * (t + 1) - 1 then -1 else 1 := by
      intro x
      dsimp only [eps0, q1]
      by_cases h0 : x.val = 0
      · have hne : x.val ≠ 2 * (t + 1) - 1 := by omega
        rw [if_pos h0, if_neg hne]
        simp [sgn]
      · by_cases hlast : x.val = 2 * (t + 1) - 1
        · rw [if_neg h0, if_pos hlast, if_pos hlast]
          simp [sgn]
        · rw [if_neg h0, if_neg hlast, if_neg hlast]
    dsimp only [ringW]
    rw [he1 j, he1 (j - 1), fin_sub_one_val h2m j]
    by_cases h0 : j.val = 0
    · have hne : j.val ≠ 2 * (t + 1) - 1 := by omega
      rw [if_neg hne, if_pos h0, if_pos rfl, if_pos (Or.inl h0)]
      ring
    · by_cases hlast : j.val = 2 * (t + 1) - 1
      · have hne : j.val - 1 ≠ 2 * (t + 1) - 1 := by omega
        rw [if_pos hlast, if_neg h0, if_neg hne, if_pos (Or.inr hlast)]
        ring
      · have hne : j.val - 1 ≠ 2 * (t + 1) - 1 := by omega
        have hnor : ¬ (j.val = 0 ∨ j.val = 2 * (t + 1) - 1) := by omega
        rw [if_neg hlast, if_neg h0, if_neg hne, if_neg hnor]
        ring
  have hW2 : ∀ u v j, ringW q2 u v j =
      (if j.val % 2 = 1 then v else u) *
      (if j.val = 0 ∨ j.val = 1 then -1 else 1) := by
    intro u v j
    have he2 : ∀ x : Fin (2 * (t + 1)), eps0 q2 x = if x.val = 0 then -1 else 1 := by
      intro x
      dsimp only [eps0, q2]
      by_cases h0 : x.val = 0
      · rw [if_pos h0, if_pos h0]; simp [sgn]
      · by_cases h1 : x.val = 1
        · rw [if_neg h0, if_pos h1, if_neg h0]; simp [sgn]
        · rw [if_neg h0, if_neg h1, if_neg h0]
    dsimp only [ringW]
    rw [he2 j, he2 (j - 1), fin_sub_one_val h2m j]
    by_cases h0 : j.val = 0
    · have hne : 2 * (t + 1) - 1 ≠ 0 := by omega
      rw [if_pos h0, if_pos h0, if_neg hne, if_pos (Or.inl h0)]
      ring
    · by_cases h1 : j.val = 1
      · have hsub0 : j.val - 1 = 0 := by omega
        rw [if_neg h0, if_neg h0, if_pos hsub0, if_pos (Or.inr h1)]
        ring
      · have hne : j.val - 1 ≠ 0 := by omega
        have hnor : ¬ (j.val = 0 ∨ j.val = 1) := by omega
        rw [if_neg h0, if_neg h0, if_neg hne, if_neg hnor]
        ring
  have hP1 : ∀ u v : ℚ,
      polyDef (t + 1) (fun i => i + 1) (pOf q1) u v = (1 - u) * (1 - u ^ t * v ^ (t + 1)) := by
    intro u v
    rw [polyDef_ring_pOf]
    let cls1 : Fin (2 * (t + 1)) → Bool := fun j => decide (j.val ≠ 0)
    have hsurj1 : Function.Surjective cls1 := by
      intro b
      cases b
      · exact ⟨⟨0, by omega⟩, by simp [cls1]⟩
      · exact ⟨⟨1, by omega⟩, by simp [cls1]⟩
    have hiff1 : ∀ S : Fin (2 * (t + 1)) → Bool,
        (∀ j : Fin (2 * (t + 1)), q1 j = none → S (j + 1) = S j) ↔
        (∀ x y, cls1 x = cls1 y → S x = S y) := by
      intro S
      constructor
      · intro hS
        have hstep : ∀ m : ℕ, 1 ≤ m → (hm : m < 2 * (t + 1)) →
            S ⟨m, hm⟩ = S ⟨1, by omega⟩ := by
          intro m hm1 hm
          induction m with
          | zero => omega
          | succ m ih =>
            by_cases hm0 : m = 0
            · subst hm0; rfl
            · have hm1' : 1 ≤ m := by omega
              have hm' : m < 2 * (t + 1) := by omega
              have hq : q1 ⟨m, hm'⟩ = none := by
                dsimp only [q1]
                rw [if_neg (show m ≠ 0 by omega), if_neg (show m ≠ 2 * (t + 1) - 1 by omega)]
              have hnext : (⟨m, hm'⟩ + 1 : Fin (2 * (t + 1))) = ⟨m + 1, hm⟩ := by
                apply Fin.ext
                rw [fin_add_one_val h2m]
                rw [if_neg (show m + 1 ≠ 2 * (t + 1) by omega)]
              have hs := hS ⟨m, hm'⟩ hq
              rw [hnext] at hs
              exact hs.trans (ih hm1' hm')
        intro x y hxy
        by_cases hx0 : x.val = 0
        · have hy0 : y.val = 0 := by
            by_contra hyne
            have hx_f : cls1 x = false := by simp only [cls1, hx0, ne_eq, not_true_eq_false, decide_false]
            have hy_t : cls1 y = true := by simp only [cls1, ne_eq, hyne, not_false_eq_true, decide_true]
            rw [hx_f, hy_t] at hxy
            exact Bool.false_ne_true hxy
          rw [Fin.ext (hx0.trans hy0.symm)]
        · have hy0 : y.val ≠ 0 := by
            intro hyeq
            have hx_t : cls1 x = true := by simp only [cls1, ne_eq, hx0, not_false_eq_true, decide_true]
            have hy_f : cls1 y = false := by simp only [cls1, hyeq, ne_eq, not_true_eq_false, decide_false]
            rw [hx_t, hy_f] at hxy
            exact Bool.false_ne_true hxy.symm
          exact (hstep x.val (by omega) x.isLt).trans (hstep y.val (by omega) y.isLt).symm
      · intro hS j hj
        have hj0 : j.val ≠ 0 := by
          intro h; dsimp only [q1] at hj; rw [if_pos h] at hj; cases hj
        have hjl : j.val ≠ 2 * (t + 1) - 1 := by
          intro h; dsimp only [q1] at hj; rw [if_neg hj0, if_pos h] at hj; cases hj
        apply hS
        have hj1 : (j + 1 : Fin (2 * (t + 1))).val ≠ 0 := by
          have := j.isLt
          rw [fin_add_one_val h2m]; split_ifs <;> omega
        simp only [cls1, ne_eq, hj0, hj1]
    rw [sum_valid_eq_prod cls1 hsurj1 (ringW q1 u v) _ hiff1, Fintype.prod_bool, mul_comm]
    have h0 : (∏ j ∈ Finset.univ.filter (fun j : Fin (2 * (t + 1)) => cls1 j = false),
        ringW q1 u v j) = -u := by
      have hf : Finset.univ.filter (fun j : Fin (2 * (t + 1)) => cls1 j = false) =
          {⟨0, by omega⟩} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, cls1,
          ne_eq, decide_eq_false_iff_not, not_not, Fin.ext_iff]
      rw [hf, Finset.prod_singleton, hW1]
      simp
    have h1 : (∏ j ∈ Finset.univ.filter (fun j : Fin (2 * (t + 1)) => cls1 j = true),
        ringW q1 u v j) = -(u ^ t * v ^ (t + 1)) := by
      simp_rw [hW1]
      rw [Finset.prod_mul_distrib]
      have hsign : (∏ j ∈ Finset.univ.filter (fun j : Fin (2 * (t + 1)) => cls1 j = true),
          if j.val = 0 ∨ j.val = 2 * (t + 1) - 1 then (-1 : ℚ) else 1) = -1 := by
        rw [Finset.prod_eq_single ⟨2 * (t + 1) - 1, by omega⟩]
        · simp
        · intro j hj hne
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, cls1, ne_eq,
            decide_eq_true_eq] at hj
          have hne' : j.val ≠ 2 * (t + 1) - 1 := fun h => hne (Fin.ext h)
          simp [hj, hne']
        · intro hmem
          exfalso; apply hmem
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, cls1, ne_eq,
            decide_eq_true_eq]
          omega
      have huv_tail :
          (∏ j ∈ Finset.univ.filter (fun j : Fin (2 * (t + 1)) => cls1 j = true),
            if j.val % 2 = 1 then v else u) = u ^ t * v ^ (t + 1) := by
        have hge1 : (Finset.univ.filter (fun j : Fin (2 * (t + 1)) => cls1 j = true)) =
            insert ⟨1, by omega⟩ (Finset.univ.filter (fun j : Fin (2 * (t + 1)) => 2 * 1 ≤ j.val)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, cls1,
            ne_eq, decide_eq_true_eq, Fin.ext_iff]
          omega
        have hnotmem1 : (⟨1, by omega⟩ : Fin (2 * (t + 1))) ∉
            Finset.univ.filter (fun j : Fin (2 * (t + 1)) => 2 * 1 ≤ j.val) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        rw [hge1, Finset.prod_insert hnotmem1, prod_even_odd_tail (t := t) 1 (by omega) u v]
        simp only [Nat.add_sub_cancel]
        norm_num
        rw [pow_succ']
        ring
      rw [hsign, huv_tail]
      ring
    rw [h0, h1]
    ring
  have hP2 : ∀ u v : ℚ,
      polyDef (t + 1) (fun i => i + 1) (pOf q2) u v = (1 - v) * (1 - u ^ (t + 1) * v ^ t) := by
    intro u v
    rw [polyDef_ring_pOf]
    let cls2 : Fin (2 * (t + 1)) → Bool := fun j => decide (j.val ≠ 1)
    have hsurj2 : Function.Surjective cls2 := by
      intro b
      cases b
      · exact ⟨⟨1, by omega⟩, by simp only [cls2, ne_eq, not_true_eq_false, decide_false]⟩
      · exact ⟨⟨0, by omega⟩, by simp only [cls2, ne_eq, zero_ne_one, not_false_eq_true, decide_true]⟩
    have hiff2 : ∀ S : Fin (2 * (t + 1)) → Bool,
        (∀ j : Fin (2 * (t + 1)), q2 j = none → S (j + 1) = S j) ↔
        (∀ x y, cls2 x = cls2 y → S x = S y) := by
      intro S
      constructor
      · intro hS
        have hstep : ∀ m : ℕ, 2 ≤ m → (hm : m < 2 * (t + 1)) →
            S ⟨m, hm⟩ = S ⟨2, by omega⟩ := by
          intro m hm2 hm
          induction m with
          | zero => omega
          | succ m ih =>
            by_cases hm1 : m = 1
            · subst hm1; rfl
            · have hm2' : 2 ≤ m := by omega
              have hm' : m < 2 * (t + 1) := by omega
              have hq : q2 ⟨m, hm'⟩ = none := by
                dsimp only [q2]
                rw [if_neg (show m ≠ 0 by omega), if_neg (show m ≠ 1 by omega)]
              have hnext : (⟨m, hm'⟩ + 1 : Fin (2 * (t + 1))) = ⟨m + 1, hm⟩ := by
                apply Fin.ext
                rw [fin_add_one_val h2m]
                rw [if_neg (show m + 1 ≠ 2 * (t + 1) by omega)]
              have hs := hS ⟨m, hm'⟩ hq
              rw [hnext] at hs
              exact hs.trans (ih hm2' hm')
        have hwrap : S ⟨0, by omega⟩ = S ⟨2, by omega⟩ := by
          have hlast : q2 ⟨2 * (t + 1) - 1, by omega⟩ = none := by
            dsimp only [q2]
            rw [if_neg (show 2 * (t + 1) - 1 ≠ 0 by omega),
              if_neg (show 2 * (t + 1) - 1 ≠ 1 by omega)]
          have hnext : (⟨2 * (t + 1) - 1, by omega⟩ + 1 : Fin (2 * (t + 1))) = ⟨0, by omega⟩ := by
            apply Fin.ext
            rw [fin_add_one_val h2m]
            rw [if_pos (show 2 * (t + 1) - 1 + 1 = 2 * (t + 1) by omega)]
          have hs := hS ⟨2 * (t + 1) - 1, by omega⟩ hlast
          rw [hnext] at hs
          exact hs.trans (hstep (2 * (t + 1) - 1) (by omega) (by omega))
        have hall : ∀ x : Fin (2 * (t + 1)), x.val ≠ 1 → S x = S ⟨2, by omega⟩ := by
          intro x hx
          by_cases hx0 : x.val = 0
          · rw [show x = ⟨0, by omega⟩ from Fin.ext hx0]; exact hwrap
          · exact hstep x.val (by omega) x.isLt
        intro x y hxy
        by_cases hx1 : x.val = 1
        · have hy1 : y.val = 1 := by
            by_contra hyne
            have hx_f : cls2 x = false := by simp only [cls2, hx1, ne_eq, not_true_eq_false, decide_false]
            have hy_t : cls2 y = true := by simp only [cls2, ne_eq, hyne, not_false_eq_true, decide_true]
            rw [hx_f, hy_t] at hxy
            exact Bool.false_ne_true hxy
          rw [Fin.ext (hx1.trans hy1.symm)]
        · have hy1 : y.val ≠ 1 := by
            intro hyeq
            have hx_t : cls2 x = true := by simp only [cls2, ne_eq, hx1, not_false_eq_true, decide_true]
            have hy_f : cls2 y = false := by simp only [cls2, hyeq, ne_eq, not_true_eq_false, decide_false]
            rw [hx_t, hy_f] at hxy
            exact Bool.false_ne_true hxy.symm
          exact (hall x hx1).trans (hall y hy1).symm
      · intro hS j hj
        have hj0 : j.val ≠ 0 := by
          intro h; dsimp only [q2] at hj; rw [if_pos h] at hj; cases hj
        have hj1 : j.val ≠ 1 := by
          intro h; dsimp only [q2] at hj; rw [if_neg hj0, if_pos h] at hj; cases hj
        apply hS
        have hj1' : (j + 1 : Fin (2 * (t + 1))).val ≠ 1 := by
          have := j.isLt
          rw [fin_add_one_val h2m]; split_ifs <;> omega
        simp only [cls2, ne_eq, hj1, hj1']
    rw [sum_valid_eq_prod cls2 hsurj2 (ringW q2 u v) _ hiff2, Fintype.prod_bool, mul_comm]
    have h0 : (∏ j ∈ Finset.univ.filter (fun j : Fin (2 * (t + 1)) => cls2 j = false),
        ringW q2 u v j) = -v := by
      have hf : Finset.univ.filter (fun j : Fin (2 * (t + 1)) => cls2 j = false) =
          {⟨1, by omega⟩} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, cls2,
          ne_eq, decide_eq_false_iff_not, not_not, Fin.ext_iff]
      rw [hf, Finset.prod_singleton, hW2]
      simp
    have h1 : (∏ j ∈ Finset.univ.filter (fun j : Fin (2 * (t + 1)) => cls2 j = true),
        ringW q2 u v j) = -(u ^ (t + 1) * v ^ t) := by
      simp_rw [hW2]
      rw [Finset.prod_mul_distrib]
      have hsign : (∏ j ∈ Finset.univ.filter (fun j : Fin (2 * (t + 1)) => cls2 j = true),
          if j.val = 0 ∨ j.val = 1 then (-1 : ℚ) else 1) = -1 := by
        rw [Finset.prod_eq_single ⟨0, by omega⟩]
        · simp
        · intro j hj hne
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, cls2, ne_eq,
            decide_eq_true_eq] at hj
          have hne' : j.val ≠ 0 := fun h => hne (Fin.ext h)
          simp [hj, hne']
        · intro hmem
          exfalso; apply hmem
          simp [cls2]
      have huv_tail :
          (∏ j ∈ Finset.univ.filter (fun j : Fin (2 * (t + 1)) => cls2 j = true),
            if j.val % 2 = 1 then v else u) = u ^ (t + 1) * v ^ t := by
        have hge1 : (Finset.univ.filter (fun j : Fin (2 * (t + 1)) => cls2 j = true)) =
            insert ⟨0, by omega⟩ (Finset.univ.filter (fun j : Fin (2 * (t + 1)) => 2 * 1 ≤ j.val)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, cls2,
            ne_eq, decide_eq_true_eq, Fin.ext_iff]
          omega
        have hnotmem0 : (⟨0, by omega⟩ : Fin (2 * (t + 1))) ∉
            Finset.univ.filter (fun j : Fin (2 * (t + 1)) => 2 * 1 ≤ j.val) := by
          simp
        rw [hge1, Finset.prod_insert hnotmem0, prod_even_odd_tail (t := t) 1 (by omega) u v]
        simp only [Nat.add_sub_cancel]
        norm_num
        rw [pow_succ']
        ring
      rw [hsign, huv_tail]
      ring
    rw [h0, h1]
    ring
  refine ⟨pOf q1, pOf q2, ?_, ?_⟩
  · intro u
    rw [hP1, hP2]
    ring
  · intro hlaw
    have hev : polyDef (t + 1) (fun i => i + 1) (pOf q1) 1 0 =
        polyDef (t + 1) (fun i => i + 1) (pOf q2) 1 0 := by
      simp [polyDef, hlaw]
    rw [hP1, hP2] at hev
    have ht0 : t ≠ 0 := by omega
    rw [zero_pow ht0] at hev
    norm_num at hev

lemma part2_k2 {t : ℕ} (ht : 2 ≤ t + 1) :
    ∃ p q : Bool × Fin (t + 1) → Option Bool,
      (∀ u : ℚ, polyDef (t + 1) (fun i => i + 1) p u (u ^ 2) =
        polyDef (t + 1) (fun i => i + 1) q u (u ^ 2)) ∧
      lawDef (t + 1) (fun i => i + 1) p ≠ lawDef (t + 1) (fun i => i + 1) q := by
  let q1 : Fin (2 * (t + 1)) → Option Bool := fun j =>
    if j.val = 0 then some false
    else if j.val = 1 then some false
    else if j.val = 2 then some true
    else if j.val = 3 then some false
    else if j.val = 2 * (t + 1) - 1 then some false
    else none
  let q2 : Fin (2 * (t + 1)) → Option Bool := fun j =>
    if j.val = 2 then some true
    else if j.val = 3 then some false
    else if j.val = 2 * (t + 1) - 1 then some false
    else none
  have h2m : 2 ≤ 2 * (t + 1) := by omega
  have heps : ∀ (x : Fin (2 * (t + 1))),
      eps0 q1 x = (if x.val = 2 then -1 else 1) ∧
      eps0 q2 x = (if x.val = 2 then -1 else 1) := by
    intro x
    constructor
    · dsimp only [eps0, q1]
      by_cases h0 : x.val = 0
      · rw [if_pos h0, if_neg (show x.val ≠ 2 by omega)]; simp [sgn]
      · by_cases h1 : x.val = 1
        · rw [if_neg h0, if_pos h1, if_neg (show x.val ≠ 2 by omega)]; simp [sgn]
        · by_cases h2 : x.val = 2
          · rw [if_neg h0, if_neg h1, if_pos h2, if_pos h2]; simp [sgn]
          · by_cases h3 : x.val = 3
            · rw [if_neg h0, if_neg h1, if_neg h2, if_pos h3, if_neg h2]; simp [sgn]
            · by_cases hl : x.val = 2 * (t + 1) - 1
              · rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos hl, if_neg h2]; simp [sgn]
              · rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg hl, if_neg h2]
    · dsimp only [eps0, q2]
      by_cases h2 : x.val = 2
      · rw [if_pos h2, if_pos h2]; simp [sgn]
      · by_cases h3 : x.val = 3
        · rw [if_neg h2, if_pos h3, if_neg h2]; simp [sgn]
        · by_cases hl : x.val = 2 * (t + 1) - 1
          · rw [if_neg h2, if_neg h3, if_pos hl, if_neg h2]; simp [sgn]
          · rw [if_neg h2, if_neg h3, if_neg hl, if_neg h2]
  have hW : ∀ u v j,
      ringW q1 u v j = (if j.val % 2 = 1 then v else u) * (if j.val = 2 ∨ j.val = 3 then -1 else 1) ∧
      ringW q2 u v j = (if j.val % 2 = 1 then v else u) * (if j.val = 2 ∨ j.val = 3 then -1 else 1) := by
    intro u v j
    have hcommon :
        (if j.val = 2 then (-1 : ℚ) else 1) * (if (j - 1 : Fin (2 * (t + 1))).val = 2 then -1 else 1) =
        if j.val = 2 ∨ j.val = 3 then -1 else 1 := by
      rw [fin_sub_one_val h2m j]
      by_cases h0 : j.val = 0
      · have hne : 2 * (t + 1) - 1 ≠ 2 := by omega
        have hnor : ¬ (j.val = 2 ∨ j.val = 3) := by omega
        rw [if_neg (show j.val ≠ 2 by omega), if_pos h0, if_neg hne, if_neg hnor]; ring
      · by_cases h2 : j.val = 2
        · have hne : j.val - 1 ≠ 2 := by omega
          rw [if_pos h2, if_neg h0, if_neg hne, if_pos (Or.inl h2)]; ring
        · by_cases h3 : j.val = 3
          · have heq2 : j.val - 1 = 2 := by omega
            rw [if_neg h2, if_neg h0, if_pos heq2, if_pos (Or.inr h3)]; ring
          · have hne : j.val - 1 ≠ 2 := by omega
            have hnor : ¬ (j.val = 2 ∨ j.val = 3) := by omega
            rw [if_neg h2, if_neg h0, if_neg hne, if_neg hnor]; ring
    constructor
    · dsimp only [ringW]
      rw [(heps j).1, (heps (j - 1)).1, mul_assoc, hcommon]
    · dsimp only [ringW]
      rw [(heps j).2, (heps (j - 1)).2, mul_assoc, hcommon]
  by_cases ht1 : t = 1
  · subst ht1
    have hP1 : ∀ u v : ℚ,
        polyDef 2 (fun i => i + 1) (pOf q1) u v = (1 - u ^ 2) * (1 - v ^ 2) := by
      intro u v
      rw [polyDef_ring_pOf]
      have hiff : ∀ S : Fin (2 * (1 + 1)) → Bool,
          (∀ j : Fin (2 * (1 + 1)), q1 j = none → S (j + 1) = S j) ↔
          (∀ x y : Fin (2 * (1 + 1)), id x = id y → S x = S y) := by
        intro S
        constructor
        · intro _ x y h; exact congrArg S h
        · intro _ j hj
          have h0 : j.val ≠ 0 := by intro h; dsimp only [q1] at hj; rw [if_pos h] at hj; cases hj
          have h1 : j.val ≠ 1 := by intro h; dsimp only [q1] at hj; rw [if_neg h0, if_pos h] at hj; cases hj
          have h2 : j.val ≠ 2 := by intro h; dsimp only [q1] at hj; rw [if_neg h0, if_neg h1, if_pos h] at hj; cases hj
          have h3 : j.val ≠ 3 := by intro h; dsimp only [q1] at hj; rw [if_neg h0, if_neg h1, if_neg h2, if_pos h] at hj; cases hj
          omega
      rw [sum_valid_eq_prod id Function.surjective_id (ringW q1 u v) _ hiff]
      have hfib : ∀ b : Fin 4, Finset.univ.filter (fun x : Fin 4 => x = b) = {b} := by
        intro b; ext x; simp
      simp_rw [id_eq, hfib, Finset.prod_singleton]
      rw [Fin.prod_univ_four]
      have w0 : ringW q1 u v ⟨0, by omega⟩ = u := by rw [(hW u v ⟨0, by omega⟩).1]; norm_num
      have w1 : ringW q1 u v ⟨1, by omega⟩ = v := by rw [(hW u v ⟨1, by omega⟩).1]; norm_num
      have w2 : ringW q1 u v ⟨2, by omega⟩ = -u := by rw [(hW u v ⟨2, by omega⟩).1]; norm_num
      have w3 : ringW q1 u v ⟨3, by omega⟩ = -v := by rw [(hW u v ⟨3, by omega⟩).1]; norm_num
      change (1 + ringW q1 u v ⟨0, by omega⟩) * (1 + ringW q1 u v ⟨1, by omega⟩) *
        (1 + ringW q1 u v ⟨2, by omega⟩) * (1 + ringW q1 u v ⟨3, by omega⟩) = _
      rw [w0, w1, w2, w3]
      ring
    have hP2 : ∀ u v : ℚ,
        polyDef 2 (fun i => i + 1) (pOf q2) u v = (1 - u ^ 2 * v) * (1 - v) := by
      intro u v
      rw [polyDef_ring_pOf]
      let cls2 : Fin 4 → Bool := fun j => decide (j.val = 3)
      have hsurj2 : Function.Surjective cls2 := by
        intro b; cases b
        · exact ⟨⟨0, by omega⟩, by simp [cls2]⟩
        · exact ⟨⟨3, by omega⟩, by simp [cls2]⟩
      have hiff : ∀ S : Fin 4 → Bool,
          (∀ j : Fin 4, q2 j = none → S (j + 1) = S j) ↔
          (∀ x y : Fin 4, cls2 x = cls2 y → S x = S y) := by
        intro S
        constructor
        · intro hS
          have h01 : S 1 = S 0 := hS 0 (by simp [q2])
          have h12 : S 2 = S 1 := hS 1 (by simp [q2])
          intro x y hxy
          fin_cases x <;> fin_cases y <;> simp [cls2] at hxy ⊢ <;>
            first | rfl | exact h01 | exact h01.symm | exact h12 | exact h12.symm |
              exact h12.trans h01 | exact (h12.trans h01).symm
        · intro hS j hj
          fin_cases j <;> simp [q2] at hj
          · exact hS 1 0 (by simp [cls2])
          · exact hS 2 1 (by simp [cls2])
      rw [sum_valid_eq_prod cls2 hsurj2 (ringW q2 u v) _ hiff, Fintype.prod_bool, mul_comm]
      have hf0 : Finset.univ.filter (fun j : Fin 4 => cls2 j = false) = {0, 1, 2} := by
        ext j; fin_cases j <;> simp [cls2]
      have hf1 : Finset.univ.filter (fun j : Fin 4 => cls2 j = true) = {3} := by
        ext j; fin_cases j <;> simp [cls2]
      rw [hf0, hf1, Finset.prod_singleton, Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_singleton]
      have w0 := (hW u v 0).2
      have w1 := (hW u v 1).2
      have w2 := (hW u v 2).2
      have w3 := (hW u v 3).2
      norm_num at w0 w1 w2 w3
      rw [w0, w1, w2, w3]
      ring
    refine ⟨pOf q1, pOf q2, ?_, ?_⟩
    · intro u; rw [hP1, hP2]; ring
    · intro hlaw
      have hev : polyDef 2 (fun i => i + 1) (pOf q1) 0 2 =
          polyDef 2 (fun i => i + 1) (pOf q2) 0 2 := by
        simp [polyDef, hlaw]
      rw [hP1, hP2] at hev
      norm_num at hev
  · have ht2 : 2 ≤ t := by omega
    have htail_step : ∀ (S : Fin (2 * (t + 1)) → Bool),
        (∀ j : Fin (2 * (t + 1)), 4 ≤ j.val → j.val < 2 * (t + 1) - 1 → S (j + 1) = S j) →
        ∀ m : ℕ, 4 ≤ m → (hm : m < 2 * (t + 1)) → S ⟨m, hm⟩ = S ⟨4, by omega⟩ := by
      intro S hS m hm4 hm
      induction m with
      | zero => omega
      | succ m ih =>
        by_cases hm3 : m = 3
        · subst hm3; rfl
        · have hm4' : 4 ≤ m := by omega
          have hm' : m < 2 * (t + 1) := by omega
          have hnext : (⟨m, hm'⟩ + 1 : Fin (2 * (t + 1))) = ⟨m + 1, hm⟩ := by
            apply Fin.ext
            rw [fin_add_one_val h2m]
            have : m + 1 ≠ 2 * (t + 1) := by omega
            simp [this]
          have hs := hS ⟨m, hm'⟩ hm4' (show (⟨m, hm'⟩ : Fin (2 * (t + 1))).val < 2 * (t + 1) - 1 by dsimp only; omega)
          rw [hnext] at hs
          exact hs.trans (ih hm4' hm')
    have htail_prod : ∀ u v : ℚ,
        (∏ j ∈ Finset.univ.filter (fun j : Fin (2 * (t + 1)) => 4 ≤ j.val),
          ringW q1 u v j) = u ^ (t - 1) * v ^ (t - 1) ∧
        (∏ j ∈ Finset.univ.filter (fun j : Fin (2 * (t + 1)) => 4 ≤ j.val),
          ringW q2 u v j) = u ^ (t - 1) * v ^ (t - 1) := by
      intro u v
      have hsame : ∀ j ∈ Finset.univ.filter (fun j : Fin (2 * (t + 1)) => 4 ≤ j.val),
          ringW q1 u v j = (if j.val % 2 = 1 then v else u) ∧
          ringW q2 u v j = (if j.val % 2 = 1 then v else u) := by
        intro j hj
        rw [Finset.mem_filter] at hj
        have hne2 : j.val ≠ 2 := by omega
        have hne3 : j.val ≠ 3 := by omega
        have hw := hW u v j
        simp only [hne2, hne3, or_self, ↓reduceIte, mul_one] at hw
        exact hw
      have hbase := prod_even_odd_tail (t := t) 2 (by omega) u v
      have hsub : t + 1 - 2 = t - 1 := by omega
      rw [hsub] at hbase
      constructor
      · rw [Finset.prod_congr rfl (fun j hj => (hsame j hj).1)]
        exact hbase
      · rw [Finset.prod_congr rfl (fun j hj => (hsame j hj).2)]
        exact hbase
    have hP1 : ∀ u v : ℚ,
        polyDef (t + 1) (fun i => i + 1) (pOf q1) u v =
        (1 - u ^ 2) * (1 - v ^ 2) * (1 + u ^ (t - 1) * v ^ (t - 1)) := by
      intro u v
      rw [polyDef_ring_pOf]
      let cls1 : Fin (2 * (t + 1)) → Fin 5 := fun j => ⟨min j.val 4, by omega⟩
      have hsurj1 : Function.Surjective cls1 := by
        intro b
        refine ⟨⟨b.val, by omega⟩, Fin.ext (by dsimp [cls1]; omega)⟩
      have hiff1 : ∀ S : Fin (2 * (t + 1)) → Bool,
          (∀ j : Fin (2 * (t + 1)), q1 j = none → S (j + 1) = S j) ↔
          (∀ x y, cls1 x = cls1 y → S x = S y) := by
        intro S
        constructor
        · intro hS
          have htail := htail_step S (fun j hj4 hjl => by
            apply hS j
            dsimp only [q1]
            rw [if_neg (show j.val ≠ 0 by omega), if_neg (show j.val ≠ 1 by omega),
              if_neg (show j.val ≠ 2 by omega), if_neg (show j.val ≠ 3 by omega),
              if_neg (show j.val ≠ 2 * (t + 1) - 1 by omega)])
          intro x y hxy
          have hm : min x.val 4 = min y.val 4 := congrArg Fin.val hxy
          by_cases hx4 : x.val < 4
          · have hxy_eq : x.val = y.val := by omega
            rw [Fin.ext hxy_eq]
          · have hy4 : 4 ≤ y.val := by omega
            exact (htail x.val (by omega) x.isLt).trans (htail y.val hy4 y.isLt).symm
        · intro hS j hj
          have h0 : j.val ≠ 0 := by
            intro h; dsimp only [q1] at hj; rw [if_pos h] at hj; cases hj
          have h1 : j.val ≠ 1 := by
            intro h; dsimp only [q1] at hj; rw [if_neg h0, if_pos h] at hj; cases hj
          have h2 : j.val ≠ 2 := by
            intro h; dsimp only [q1] at hj; rw [if_neg h0, if_neg h1, if_pos h] at hj; cases hj
          have h3 : j.val ≠ 3 := by
            intro h; dsimp only [q1] at hj; rw [if_neg h0, if_neg h1, if_neg h2, if_pos h] at hj; cases hj
          have hl : j.val ≠ 2 * (t + 1) - 1 := by
            intro h; dsimp only [q1] at hj; rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_pos h] at hj; cases hj
          apply hS
          apply Fin.ext
          dsimp only [cls1]
          rw [fin_add_one_val h2m]
          rw [if_neg (show j.val + 1 ≠ 2 * (t + 1) by omega)]
          omega
      rw [sum_valid_eq_prod cls1 hsurj1 (ringW q1 u v) _ hiff1, Fin.prod_univ_five]
      have hf0 : Finset.univ.filter (fun j : Fin (2 * (t + 1)) => cls1 j = 0) = {⟨0, by omega⟩} := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Fin.ext_iff, cls1]; omega
      have hf1 : Finset.univ.filter (fun j : Fin (2 * (t + 1)) => cls1 j = 1) = {⟨1, by omega⟩} := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Fin.ext_iff, cls1]; omega
      have hf2 : Finset.univ.filter (fun j : Fin (2 * (t + 1)) => cls1 j = 2) = {⟨2, by omega⟩} := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Fin.ext_iff, cls1]; omega
      have hf3 : Finset.univ.filter (fun j : Fin (2 * (t + 1)) => cls1 j = 3) = {⟨3, by omega⟩} := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Fin.ext_iff, cls1]; omega
      have hf4 : Finset.univ.filter (fun j : Fin (2 * (t + 1)) => cls1 j = 4) =
          Finset.univ.filter (fun j : Fin (2 * (t + 1)) => 4 ≤ j.val) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff, cls1]; omega
      rw [hf0, hf1, hf2, hf3, hf4, Finset.prod_singleton, Finset.prod_singleton,
        Finset.prod_singleton, Finset.prod_singleton, (htail_prod u v).1]
      have w0 : ringW q1 u v ⟨0, by omega⟩ = u := by rw [(hW u v ⟨0, by omega⟩).1]; norm_num
      have w1 : ringW q1 u v ⟨1, by omega⟩ = v := by rw [(hW u v ⟨1, by omega⟩).1]; norm_num
      have w2 : ringW q1 u v ⟨2, by omega⟩ = -u := by rw [(hW u v ⟨2, by omega⟩).1]; norm_num
      have w3 : ringW q1 u v ⟨3, by omega⟩ = -v := by rw [(hW u v ⟨3, by omega⟩).1]; norm_num
      rw [w0, w1, w2, w3]
      ring
    have hP2 : ∀ u v : ℚ,
        polyDef (t + 1) (fun i => i + 1) (pOf q2) u v =
        (1 - u ^ 2 * v) * (1 - v) * (1 + u ^ (t - 1) * v ^ (t - 1)) := by
      intro u v
      rw [polyDef_ring_pOf]
      let cls2 : Fin (2 * (t + 1)) → Fin 3 := fun j =>
        if j.val ≤ 2 then 0 else if j.val = 3 then 1 else 2
      have hsurj2 : Function.Surjective cls2 := by
        intro b
        fin_cases b
        · exact ⟨⟨0, by omega⟩, by simp [cls2]⟩
        · exact ⟨⟨3, by omega⟩, by simp [cls2]⟩
        · exact ⟨⟨4, by omega⟩, by simp [cls2]⟩
      have hiff2 : ∀ S : Fin (2 * (t + 1)) → Bool,
          (∀ j : Fin (2 * (t + 1)), q2 j = none → S (j + 1) = S j) ↔
          (∀ x y, cls2 x = cls2 y → S x = S y) := by
        intro S
        constructor
        · intro hS
          have h01 : S ⟨1, by omega⟩ = S ⟨0, by omega⟩ := by
            have hq : q2 ⟨0, by omega⟩ = none := by
              dsimp only [q2]
              rw [if_neg (by omega), if_neg (by omega), if_neg (show 0 ≠ 2 * (t + 1) - 1 by omega)]
            have hnext : (⟨0, by omega⟩ + 1 : Fin (2 * (t + 1))) = ⟨1, by omega⟩ := by
              apply Fin.ext; rw [fin_add_one_val h2m]
              rw [if_neg (show 0 + 1 ≠ 2 * (t + 1) by omega)]
            have hs := hS ⟨0, by omega⟩ hq
            rwa [hnext] at hs
          have h12 : S ⟨2, by omega⟩ = S ⟨1, by omega⟩ := by
            have hq : q2 ⟨1, by omega⟩ = none := by
              dsimp only [q2]
              rw [if_neg (by omega), if_neg (by omega), if_neg (show 1 ≠ 2 * (t + 1) - 1 by omega)]
            have hnext : (⟨1, by omega⟩ + 1 : Fin (2 * (t + 1))) = ⟨2, by omega⟩ := by
              apply Fin.ext; rw [fin_add_one_val h2m]
              rw [if_neg (show 1 + 1 ≠ 2 * (t + 1) by omega)]
            have hs := hS ⟨1, by omega⟩ hq
            rwa [hnext] at hs
          have hhead : ∀ x : Fin (2 * (t + 1)), x.val ≤ 2 → S x = S ⟨0, by omega⟩ := by
            intro x hx
            have hx_cases : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by omega
            rcases hx_cases with h | h | h
            · rw [show x = ⟨0, by omega⟩ from Fin.ext h]
            · rw [show x = ⟨1, by omega⟩ from Fin.ext h]; exact h01
            · rw [show x = ⟨2, by omega⟩ from Fin.ext h]; exact h12.trans h01
          have htail := htail_step S (fun j hj4 hjl => by
            apply hS j
            dsimp only [q2]
            rw [if_neg (show j.val ≠ 2 by omega), if_neg (show j.val ≠ 3 by omega),
              if_neg (show j.val ≠ 2 * (t + 1) - 1 by omega)])
          intro x y hxy
          by_cases hx2 : x.val ≤ 2
          · have hy2 : y.val ≤ 2 := by
              by_contra hy2
              dsimp only [cls2] at hxy
              rw [if_pos hx2, if_neg hy2] at hxy
              split_ifs at hxy <;> simp at hxy
            exact (hhead x hx2).trans (hhead y hy2).symm
          · by_cases hx3 : x.val = 3
            · have hy3 : y.val = 3 := by
                by_contra hy3
                dsimp only [cls2] at hxy
                rw [if_neg hx2, if_pos hx3] at hxy
                split_ifs at hxy <;> simp at hxy
              rw [Fin.ext (hx3.trans hy3.symm)]
            · have hy4 : 4 ≤ y.val := by
                by_contra hy4
                dsimp only [cls2] at hxy
                rw [if_neg hx2, if_neg hx3] at hxy
                by_cases hy2 : y.val ≤ 2
                · rw [if_pos hy2] at hxy; simp at hxy
                · have hy3 : y.val = 3 := by omega
                  rw [if_neg hy2, if_pos hy3] at hxy; simp at hxy
              exact (htail x.val (by omega) x.isLt).trans (htail y.val hy4 y.isLt).symm
        · intro hS j hj
          have h2 : j.val ≠ 2 := by
            intro h; dsimp only [q2] at hj; rw [if_pos h] at hj; cases hj
          have h3 : j.val ≠ 3 := by
            intro h; dsimp only [q2] at hj; rw [if_neg h2, if_pos h] at hj; cases hj
          have hl : j.val ≠ 2 * (t + 1) - 1 := by
            intro h; dsimp only [q2] at hj; rw [if_neg h2, if_neg h3, if_pos h] at hj; cases hj
          apply hS
          dsimp only [cls2]
          rw [fin_add_one_val h2m]
          rw [if_neg (show j.val + 1 ≠ 2 * (t + 1) by omega)]
          by_cases hj1 : j.val ≤ 1
          · rw [if_pos (show j.val + 1 ≤ 2 by omega), if_pos (show j.val ≤ 2 by omega)]
          · have hj4 : 4 ≤ j.val := by omega
            rw [if_neg (show ¬ (j.val + 1 ≤ 2) by omega), if_neg (show j.val + 1 ≠ 3 by omega),
              if_neg (show ¬ (j.val ≤ 2) by omega), if_neg h3]
      rw [sum_valid_eq_prod cls2 hsurj2 (ringW q2 u v) _ hiff2, Fin.prod_univ_three]
      have hf0 : Finset.univ.filter (fun j : Fin (2 * (t + 1)) => cls2 j = 0) =
          {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Fin.ext_iff, cls2]
        constructor
        · intro h; by_cases hle : j.val ≤ 2
          · omega
          · rw [if_neg hle] at h; split_ifs at h <;> simp at h
        · rintro (h | h | h) <;> simp [h]
      have hf1 : Finset.univ.filter (fun j : Fin (2 * (t + 1)) => cls2 j = 1) =
          {⟨3, by omega⟩} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Fin.ext_iff, cls2]
        constructor
        · intro h; by_cases hle : j.val ≤ 2
          · rw [if_pos hle] at h; simp at h
          · rw [if_neg hle] at h; by_cases h3 : j.val = 3
            · exact h3
            · rw [if_neg h3] at h; simp at h
        · intro h; simp [h]
      have hf2 : Finset.univ.filter (fun j : Fin (2 * (t + 1)) => cls2 j = 2) =
          Finset.univ.filter (fun j : Fin (2 * (t + 1)) => 4 ≤ j.val) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, cls2]
        constructor
        · intro h; by_cases hle : j.val ≤ 2
          · rw [if_pos hle] at h; simp at h
          · rw [if_neg hle] at h; by_cases h3 : j.val = 3
            · rw [if_pos h3] at h; simp at h
            · omega
        · intro h4
          simp [show ¬ (j.val ≤ 2) by omega, show j.val ≠ 3 by omega]
      rw [hf0, hf1, hf2, Finset.prod_singleton, (htail_prod u v).2]
      have hne01 : (⟨0, by omega⟩ : Fin (2 * (t + 1))) ∉
          ({⟨1, by omega⟩, ⟨2, by omega⟩} : Finset (Fin (2 * (t + 1)))) := by
        simp [Fin.ext_iff]
      have hne12 : (⟨1, by omega⟩ : Fin (2 * (t + 1))) ∉
          ({⟨2, by omega⟩} : Finset (Fin (2 * (t + 1)))) := by
        simp [Fin.ext_iff]
      rw [Finset.prod_insert hne01, Finset.prod_insert hne12, Finset.prod_singleton]
      have w0 : ringW q2 u v ⟨0, by omega⟩ = u := by rw [(hW u v ⟨0, by omega⟩).2]; norm_num
      have w1 : ringW q2 u v ⟨1, by omega⟩ = v := by rw [(hW u v ⟨1, by omega⟩).2]; norm_num
      have w2 : ringW q2 u v ⟨2, by omega⟩ = -u := by rw [(hW u v ⟨2, by omega⟩).2]; norm_num
      have w3 : ringW q2 u v ⟨3, by omega⟩ = -v := by rw [(hW u v ⟨3, by omega⟩).2]; norm_num
      rw [w0, w1, w2, w3]
      ring
    refine ⟨pOf q1, pOf q2, ?_, ?_⟩
    · intro u; rw [hP1, hP2]; ring
    · intro hlaw
      have hev : polyDef (t + 1) (fun i => i + 1) (pOf q1) 0 2 =
          polyDef (t + 1) (fun i => i + 1) (pOf q2) 0 2 := by
        simp [polyDef, hlaw]
      rw [hP1, hP2] at hev
      have ht1' : t - 1 ≠ 0 := by omega
      rw [zero_pow ht1'] at hev
      norm_num at hev

end PEqualNP.Outside.L_pcx_385

theorem PEqualNP.Outside.L_pcx_385 : ∀ (t k : ℕ), 0 < k →
  let n := t+1
  let I := Fin n
  let V := Bool × I
  let P := V → Option Bool
  let J := Fin (n+1)
  let law := fun (σ : I → I) (p : P) (r b : J) =>
    (((Finset.univ : Finset (V → Bool)).filter (fun x =>
      (∀ v, p v = none ∨ p v = some (x v)) ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,i))).card = r.val ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,σ i))).card = b.val)).card : ℚ) /
      (2 : ℚ)^((Finset.univ.filter (fun v : V => p v = none)).card)
  let samples := fun (σ : I → I) (p : P) (i : Fin ((k+1)*n+1)) =>
    let z : ℚ := i.val
    ∑ r : J, ∑ b : J, law σ p r b *
      (1-z)^r.val * (1+z)^(n-r.val) *
      (1-z^k)^b.val * (1+z^k)^(n-b.val)
  (3 ≤ k → ∀ (σ τ : Equiv.Perm I) (p q : P),
    samples σ p = samples τ q ↔ law σ p = law τ q) ∧
  (k ≤ 2 → 2 ≤ n →
    let ring := fun i : I => i+1
    ∃ p q : P, samples ring p = samples ring q ∧ law ring p ≠ law ring q) := by
  intro t k hk
  dsimp only
  refine ⟨?_, ?_⟩
  · intro hk3 σ τ p q
    constructor
    · intro hs
      exact PEqualNP.Outside.L_pcx_385.part1 hk3 σ τ p q (fun i => congrFun hs i)
    · intro hl
      funext i
      show PEqualNP.Outside.L_pcx_385.polyDef (t + 1) σ p (i.val : ℚ) ((i.val : ℚ) ^ k) =
        PEqualNP.Outside.L_pcx_385.polyDef (t + 1) τ q (i.val : ℚ) ((i.val : ℚ) ^ k)
      have hlaw : PEqualNP.Outside.L_pcx_385.lawDef (t + 1) σ p =
          PEqualNP.Outside.L_pcx_385.lawDef (t + 1) τ q := hl
      unfold PEqualNP.Outside.L_pcx_385.polyDef
      rw [hlaw]
  · intro hk2 hn2
    have hk12 : k = 1 ∨ k = 2 := by omega
    rcases hk12 with rfl | rfl
    · obtain ⟨p, q, hpoly, hlaw⟩ := PEqualNP.Outside.L_pcx_385.part2_k1 hn2
      refine ⟨p, q, ?_, hlaw⟩
      funext i
      change PEqualNP.Outside.L_pcx_385.polyDef (t + 1) (fun i => i + 1) p (i.val : ℚ) ((i.val : ℚ) ^ 1) =
        PEqualNP.Outside.L_pcx_385.polyDef (t + 1) (fun i => i + 1) q (i.val : ℚ) ((i.val : ℚ) ^ 1)
      rw [pow_one]
      exact hpoly (i.val : ℚ)
    · obtain ⟨p, q, hpoly, hlaw⟩ := PEqualNP.Outside.L_pcx_385.part2_k2 hn2
      refine ⟨p, q, ?_, hlaw⟩
      funext i
      exact hpoly (i.val : ℚ)
