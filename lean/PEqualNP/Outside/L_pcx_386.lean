import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_386.Core

section ArcBaseSection

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

noncomputable def arcList {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    List (ℕ × ℕ × Bool) := by
  classical
  let cls : Bool × Fin n → Finset (Bool × Fin n) :=
    fun e => Finset.univ.filter (fun e' => Relation.EqvGen (ArcStep σ p) e e')
  let C : Finset (Finset (Bool × Fin n)) := Finset.univ.image cls
  let toTriple : {c : Finset (Bool × Fin n) // c ∈ C} → ℕ × ℕ × Bool := fun c =>
    let r := (c.1.filter (fun e => e.1 = false)).card
    let b := (c.1.filter (fun e => e.1 = true)).card
    let sg := ∏ e ∈ c.1, (epsE σ p e * epsE σ p ((nextE σ).symm e))
    (r, b, decide (sg = 1))
  exact (Finset.univ.toList).map toTriple

lemma exists_arc_factors {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    ∃ L : List (ℕ × ℕ × Bool), L = arcList σ p ∧ L.length ≤ 2*n ∧
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
  refine ⟨(Finset.univ.toList).map toTriple, rfl, ?_, ?_, ?_⟩
  · simpa only [List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_prod,
      Fintype.card_bool, Fintype.card_fin] using Fintype.card_le_of_surjective clsSub hsurj
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

end ArcBaseSection

section EulerSection

open PowerSeries

noncomputable def euler (f : PowerSeries ℚ) : PowerSeries ℚ := -(X * derivative f)

noncomputable def logJet (f : PowerSeries ℚ) : PowerSeries ℚ := euler f * f⁻¹

noncomputable def oneDiv (j : ℕ) : PowerSeries ℚ := mk fun m =>
  if 0 < m ∧ j ∣ m then (j : ℚ) else 0

lemma euler_mul (f g : PowerSeries ℚ) : euler (f*g) = euler f * g + f * euler g := by
  simp [euler, Derivation.leibniz, smul_eq_mul]; ring

lemma coeff_euler (f : PowerSeries ℚ) (m : ℕ) : coeff m (euler f) = -(m : ℚ) * coeff m f := by
  cases m with
  | zero => simp [euler]
  | succ m =>
    rw [euler, map_neg, ← pow_one (X : PowerSeries ℚ), coeff_X_pow_mul, coeff_derivative]
    push_cast; ring

lemma logJet_mul_self (f : PowerSeries ℚ) (h : constantCoeff f ≠ 0) :
    logJet f * f = euler f := by
  rw [logJet, mul_assoc, PowerSeries.inv_mul_cancel _ h, mul_one]

lemma oneDiv_identity (j : ℕ) (hj : 0 < j) :
    ((1 : PowerSeries ℚ) - X ^ j) * oneDiv j = C (j : ℚ) * X^j := by
  ext m
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_C_mul, coeff_X_pow]
  simp only [oneDiv, coeff_mk]
  rcases lt_trichotomy m j with h | rfl | h
  · have hn : ¬(0 < m ∧ j ∣ m) := fun hc => (Nat.not_le_of_lt h) (Nat.le_of_dvd hc.1 hc.2)
    simp [hn, Nat.not_le_of_lt h, h.ne]
  · simp [hj]
  · have hd : j ∣ m-j ↔ j ∣ m := by
      constructor
      · intro hh
        simpa [Nat.sub_add_cancel h.le] using dvd_add hh (dvd_refl j)
      · intro hh; exact Nat.dvd_sub hh (dvd_refl j)
    simp [h.le, h.ne', (show 0 < m-j by omega), (show 0 < m by omega), hd]

lemma euler_one_sub (j : ℕ) (hj : 0 < j) :
    euler ((1 : PowerSeries ℚ) - X^j) = (1-X^j) * oneDiv j := by
  rw [oneDiv_identity _ hj]
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  rw [euler, map_sub, derivative_one, derivative_X_pow k.succ]
  simp only [Nat.succ_sub_one, zero_sub, mul_neg, neg_neg, pow_succ]
  ring

noncomputable def minusProd (M : Multiset ℕ) : PowerSeries ℚ :=
  (M.map fun j => (1 : PowerSeries ℚ) - X^j).prod

noncomputable def divSum (M : Multiset ℕ) : PowerSeries ℚ := (M.map oneDiv).sum

lemma minusProd_const (M : Multiset ℕ) (h : ∀ j ∈ M, 0 < j) :
    constantCoeff (minusProd M) = 1 := by
  induction M using Multiset.induction_on with
  | empty => simp [minusProd]
  | @cons j M ih =>
    have hj := h j (Multiset.mem_cons_self ..)
    have ht := ih (fun i hi => h i (Multiset.mem_cons_of_mem hi))
    simpa [minusProd, hj.ne'] using ht

lemma euler_minusProd (M : Multiset ℕ) (h : ∀ j ∈ M, 0 < j) :
    euler (minusProd M) = minusProd M * divSum M := by
  induction M using Multiset.induction_on with
  | empty => simp [minusProd, divSum, euler, derivative_one]
  | @cons j M ih =>
    have hj := h j (Multiset.mem_cons_self ..)
    have ht := ih (fun i hi => h i (Multiset.mem_cons_of_mem hi))
    simp only [minusProd, divSum, Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    change euler ((1-X^j) * minusProd M) = ((1-X^j)*minusProd M) * (oneDiv j + divSum M)
    rw [euler_mul, euler_one_sub j hj, ht]; ring

lemma logJet_divisor_identity (f : PowerSeries ℚ) (N D : Multiset ℕ)
    (hn : ∀ j ∈ N, 0 < j) (hd : ∀ j ∈ D, 0 < j)
    (h : f * minusProd D = minusProd N) : logJet f = divSum N - divSum D := by
  have hf : constantCoeff f = 1 := by
    have hv := congrArg constantCoeff h
    simpa only [map_mul, minusProd_const D hd, minusProd_const N hn, mul_one] using hv
  have hh := congrArg euler h
  rw [euler_mul, euler_minusProd D hd, euler_minusProd N hn, ← h] at hh
  have hD : minusProd D ≠ 0 := by
    intro h0; have hx := minusProd_const D hd; rw [h0, map_zero] at hx; exact zero_ne_one hx
  have he : euler f = f * (divSum N - divSum D) := by
    apply mul_right_cancel₀ hD
    linear_combination hh
  rw [logJet, he, mul_comm f, mul_assoc, PowerSeries.mul_inv_cancel _ (by simp [hf]), mul_one]

lemma coeff_divSum (M : Multiset ℕ) (m : ℕ) : coeff m (divSum M) =
    (M.map fun j => if 0 < m ∧ j ∣ m then (j : ℚ) else 0).sum := by
  induction M using Multiset.induction_on with
  | empty => simp [divSum]
  | @cons j M ih =>
    simp only [divSum, Multiset.map_cons, Multiset.sum_cons, map_add] at ih ⊢
    simpa [oneDiv, ih]

noncomputable def undiv (L : ℕ → ℚ) (m : ℕ) : ℚ :=
  L m - ∑ i : Fin m, if 0 < i.val ∧ i.val ∣ m then undiv L i.val else 0
termination_by m

lemma undiv_spec (L A : ℕ → ℚ) (m : ℕ)
    (h : ∀ k ≤ m, L k = A k + ∑ j : Fin k, if 0 < j.val ∧ j.val ∣ k then A j.val else 0) :
    undiv L m = A m := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    rw [undiv, h m le_rfl]
    have hs : (∑ i : Fin m, if 0 < i.val ∧ i.val ∣ m then undiv L i.val else 0) =
        ∑ i : Fin m, if 0 < i.val ∧ i.val ∣ m then A i.val else 0 := by
      apply Finset.sum_congr rfl; intro i _; rw [ih i.val i.isLt (fun k hk => h k (by omega))]
    rw [hs, add_sub_cancel_right]

def resums (A : ℕ → ℚ) (m : ℕ) : ℚ :=
  A m + ∑ i : Fin m, if 0 < i.val ∧ i.val ∣ m then A i.val else 0

lemma resums_add (A B : ℕ → ℚ) (m : ℕ) : resums (A+B) m = resums A m + resums B m := by
  have h (i : Fin m) : (if 0 < i.val ∧ i.val ∣ m then A i.val+B i.val else 0) =
      (if 0 < i.val ∧ i.val ∣ m then A i.val else 0) +
        (if 0 < i.val ∧ i.val ∣ m then B i.val else 0) := by split <;> simp_all
  simp only [resums, h, Finset.sum_add_distrib, Pi.add_apply]; ring

lemma resums_sub (A B : ℕ → ℚ) (m : ℕ) : resums (A-B) m = resums A m - resums B m := by
  have h := resums_add (A-B) B m
  rw [sub_add_cancel] at h; linarith

lemma resums_atom (j m : ℕ) : resums (fun i => if i = j then (i : ℚ) else 0) m =
    if 0 < m ∧ j ∣ m then (j : ℚ) else 0 := by
  unfold resums
  by_cases hj : j < m
  · rw [Finset.sum_eq_single (⟨j,hj⟩ : Fin m)]
    · by_cases h0 : j = 0
      · subst j; simp [show m ≠ 0 by omega]
      · simp [hj.ne', show 0 < m by omega, show 0 < j by omega]
    · intro i _ hne
      have hi : i.val ≠ j := fun hh => hne (Fin.ext hh)
      simp [hi]
    · simp
  · rw [Finset.sum_eq_zero (fun i _ => by
        have hi : i.val ≠ j := by have := i.isLt; omega
        simp [hi]), add_zero]
    by_cases he : j = m
    · subst j; by_cases h0 : m = 0
      · simp [h0]
      · simp [Nat.pos_of_ne_zero h0]
    · by_cases h0 : m = 0
      · subst m; simp [Ne.symm he]
      · have hn : ¬j ∣ m := fun hh => by have := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hh; omega
        simp [hn, Ne.symm he]

lemma divisor_peel (M : Multiset ℕ) (m : ℕ) :
    (M.map fun j => if 0 < m ∧ j ∣ m then (j : ℚ) else 0).sum =
    resums (fun i => (i : ℚ) * M.count i) m := by
  induction M using Multiset.induction_on with
  | empty => simp [resums]
  | @cons j M ih =>
    have he : (fun i : ℕ => (i : ℚ) * (j ::ₘ M).count i) =
        (fun i => if i = j then (i : ℚ) else 0) + (fun i : ℕ => (i : ℚ) * M.count i) := by
      funext i; by_cases hh : i = j <;> simp [Multiset.count_cons, hh] <;> ring
    rw [he, resums_add, resums_atom, Multiset.map_cons, Multiset.sum_cons, ih]

noncomputable def inventory (f : PowerSeries ℚ) (m : ℕ) : ℚ :=
  undiv (fun j => coeff j (logJet f)) m

lemma inventory_spec (f : PowerSeries ℚ) (N D : Multiset ℕ)
    (hn : ∀ j ∈ N, 0 < j) (hd : ∀ j ∈ D, 0 < j)
    (h : f * minusProd D = minusProd N) (m : ℕ) :
    inventory f m = (m : ℚ) * ((N.count m : ℚ) - D.count m) := by
  unfold inventory
  apply undiv_spec
  intro k hk
  rw [logJet_divisor_identity f N D hn hd h, map_sub, coeff_divSum, coeff_divSum,
    divisor_peel N, divisor_peel D]
  rw [← resums_sub]
  congr 1 <;> simp [resums, mul_sub, Pi.sub_apply]

lemma resums_inventory (f : PowerSeries ℚ) (m : ℕ) :
    resums (inventory f) m = coeff m (logJet f) := by
  unfold resums inventory
  rw [undiv]; ring

lemma logJet_zero (f : PowerSeries ℚ) : coeff 0 (logJet f) = 0 := by
  simp [logJet, euler]

lemma triangular_euler (f : PowerSeries ℚ) (hf : constantCoeff f ≠ 0) (m : ℕ) :
    -(m : ℚ)*coeff m f = ∑ i ∈ Finset.range m, coeff i f * coeff (m-i) (logJet f) := by
  have h := congrArg (coeff m) (logJet_mul_self f hf).symm
  rw [coeff_euler, mul_comm (logJet f) f, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ] at h
  simpa only [Nat.sub_self, logJet_zero, mul_zero, add_zero] using h

lemma jet_injective_through (f g : PowerSeries ℚ) (N : ℕ)
    (hf : constantCoeff f ≠ 0) (h0 : constantCoeff f = constantCoeff g)
    (h : ∀ i ≤ N, inventory f i = inventory g i) :
    ∀ m ≤ N, coeff m f = coeff m g := by
  have hL (i : ℕ) (hi : i ≤ N) : coeff i (logJet f) = coeff i (logJet g) := by
    rw [← resums_inventory, ← resums_inventory, resums, resums, h i hi]
    congr 1; apply Finset.sum_congr rfl; intro j _
    rw [h j.val (by have := j.isLt; omega)]
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro hm
    rcases Nat.eq_zero_or_pos m with rfl | hp
    · simpa only [coeff_zero_eq_constantCoeff] using h0
    · have hsum : (∑ i ∈ Finset.range m, coeff i f * coeff (m-i) (logJet f)) =
          ∑ i ∈ Finset.range m, coeff i g * coeff (m-i) (logJet g) := by
        apply Finset.sum_congr rfl; intro i hi; have hlt := Finset.mem_range.mp hi
        rw [ih i hlt (by omega), hL (m-i) (by omega)]
      rw [← triangular_euler f hf, ← triangular_euler g (h0 ▸ hf)] at hsum
      exact mul_left_cancel₀ (neg_ne_zero.mpr (by exact_mod_cast hp.ne')) hsum

lemma polynomial_jet_injective (f g : Polynomial ℚ) (N : ℕ) (df : f.natDegree ≤ N)
    (dg : g.natDegree ≤ N) (hf : f.coeff 0 ≠ 0) (h0 : f.coeff 0 = g.coeff 0)
    (h : ∀ i ≤ N, inventory (f : PowerSeries ℚ) i = inventory (g : PowerSeries ℚ) i) : f=g := by
  ext m
  by_cases hm : m ≤ N
  · have hh := jet_injective_through (f : PowerSeries ℚ) g N
      (by simpa only [← coeff_zero_eq_constantCoeff, Polynomial.coeff_coe] using hf)
      (by simpa only [← coeff_zero_eq_constantCoeff, Polynomial.coeff_coe] using h0) h m hm
    simpa only [Polynomial.coeff_coe] using hh
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < m),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : g.natDegree < m)]

end EulerSection

section TransformSection

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

abbrev Ix (n : ℕ) := Fin (n+1)
abbrev Tab (n : ℕ) := Ix n → Ix n → ℚ

noncomputable def binBasis (n : ℕ) (r : Ix n) : Polynomial ℚ :=
  (1-Polynomial.X)^r.val * (1+Polynomial.X)^(n-r.val)

noncomputable def sign1 {n : ℕ} (T : Ix n → ℚ) (a : Ix n) : ℚ :=
  ∑ r : Ix n, T r * (binBasis n r).coeff a.val

noncomputable def sign2 {n : ℕ} (T : Tab n) (a b : Ix n) : ℚ :=
  sign1 (fun s => sign1 (fun r => T r s) a) b

lemma basis_degree (n : ℕ) (r : Ix n) : (binBasis n r).natDegree ≤ n := by
  have h₁ : (1-(Polynomial.X : Polynomial ℚ)).natDegree ≤ 1 :=
    (Polynomial.natDegree_sub_le ..).trans (by simp)
  have h₂ : (1+(Polynomial.X : Polynomial ℚ)).natDegree ≤ 1 :=
    (Polynomial.natDegree_add_le ..).trans (by simp)
  have ha := Polynomial.natDegree_pow_le (p := (1-(Polynomial.X : Polynomial ℚ))) (n := r.val)
  have hb := Polynomial.natDegree_pow_le (p := (1+(Polynomial.X : Polynomial ℚ))) (n := n-r.val)
  unfold binBasis
  apply Polynomial.natDegree_mul_le.trans
  have hr := r.isLt; nlinarith [Nat.sub_add_cancel (by omega : r.val ≤ n),
    Nat.mul_le_mul_right r.val h₁, Nat.mul_le_mul_right (n-r.val) h₂]

lemma sign1_eval {n : ℕ} (T : Ix n → ℚ) (u : ℚ) :
    ∑ a : Ix n, sign1 T a * u^a.val = ∑ r : Ix n, T r * ((1-u)^r.val * (1+u)^(n-r.val)) := by
  simp only [sign1, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro r _
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun j => (binBasis n r).coeff j * u^j),
    ← Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (basis_degree n r))]
  simp [binBasis]

lemma sign1_injective (n : ℕ) : Function.Injective (@sign1 n) := by
  intro T U h
  have hz : ∀ a : Ix n, ∑ r : Ix n, (T r - U r) * ((1:ℚ)/(a.val+2))^r.val = 0 := by
    intro a
    let y : ℚ := 1/(a.val+2)
    let u : ℚ := (1-y)/(1+y)
    let c : ℚ := 2/(1+y)
    have hy : 0 < y := by dsimp [y]; positivity
    have hden : 1+y ≠ 0 := by linarith
    have h1 : 1-u = c*y := by dsimp [u,c]; field_simp; ring
    have h2 : 1+u = c := by dsimp [u,c]; field_simp; ring
    have hb (r : Ix n) : (1-u)^r.val * (1+u)^(n-r.val) = c^n*y^r.val := by
      rw [h1,h2,mul_pow, mul_comm (c^r.val), mul_assoc, ← pow_add,
        Nat.add_sub_of_le (Nat.le_of_lt_succ r.isLt), mul_comm]
    have he := (sign1_eval T u).symm.trans ((congrArg (fun f : Ix n → ℚ => ∑ a, f a*u^a.val) h).trans (sign1_eval U u))
    simp_rw [hb, ← mul_left_comm (c^n)] at he
    rw [← Finset.mul_sum, ← Finset.mul_sum] at he
    have hc : c^n ≠ 0 := pow_ne_zero _ (div_ne_zero (by norm_num) hden)
    have hsum := mul_left_cancel₀ hc he
    change ∑ r : Ix n, (T r-U r)*y^r.val = 0
    simp_rw [sub_mul, Finset.sum_sub_distrib, hsum, sub_self]
  funext r; exact sub_eq_zero.mp (coeff_eq_zero_of_poly_eval_unit _ hz r)

lemma sign2_injective (n : ℕ) : Function.Injective (@sign2 n) := by
  intro T U h
  have hh (a : Ix n) := sign1_injective n (congrFun h a)
  funext r b
  exact congrFun (sign1_injective n (funext fun a => congrFun (hh a) b)) r

noncomputable def pack {n : ℕ} (k : ℕ) (T : Tab n) : Polynomial ℚ :=
  ∑ z : Ix n × Ix n, Polynomial.C (T z.1 z.2) * Polynomial.X^(z.1.val+k*z.2.val)

lemma code_inj {n k : ℕ} (hk : n < k) : Function.Injective
    (fun z : Ix n × Ix n => z.1.val+k*z.2.val) := by
  intro x y he
  have hx : x.1.val < k := lt_of_le_of_lt (Nat.le_of_lt_succ x.1.isLt) hk
  have hy : y.1.val < k := lt_of_le_of_lt (Nat.le_of_lt_succ y.1.isLt) hk
  have ha := congrArg (· % k) he
  change (x.1.val+k*x.2.val) % k = (y.1.val+k*y.2.val) % k at ha
  simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at ha
  change x.1.val+k*x.2.val = y.1.val+k*y.2.val at he
  rw [ha] at he
  exact Prod.ext (Fin.ext ha) (Fin.ext (Nat.eq_of_mul_eq_mul_left (by omega : 0 < k) (Nat.add_left_cancel he)))

lemma coeff_pack {n k : ℕ} (hk : n < k) (T : Tab n) (a b : Ix n) :
    (pack k T).coeff (a.val+k*b.val) = T a b := by
  unfold pack; rw [coeff_sum_poly, Finset.sum_eq_single (a,b)]
  · simp
  · intro z _ hne
    have hn : a.val+k*b.val ≠ z.1.val+k*z.2.val := fun hh => hne (@code_inj n k hk z (a,b) hh.symm)
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hn]
  · simp

noncomputable def spectrum {n : ℕ} (k : ℕ) (T : Tab n) : Polynomial ℚ := pack k (sign2 T)

lemma spectrum_injective {n k : ℕ} (hk : n < k) : Function.Injective (@spectrum n k) := by
  intro T U he; apply sign2_injective n; funext a b
  simpa only [spectrum, coeff_pack hk] using congrArg (fun f : Polynomial ℚ => f.coeff (a.val+k*b.val)) he

lemma spectrum_degree {n : ℕ} (k : ℕ) (T : Tab n) : (spectrum k T).natDegree ≤ (k+1)*n := by
  apply Polynomial.natDegree_sum_le_of_forall_le; intro z _
  refine Polynomial.natDegree_mul_le.trans ?_
  simp only [Polynomial.natDegree_C, zero_add, Polynomial.natDegree_X_pow]
  have ha := z.1.isLt; have hb := z.2.isLt
  nlinarith [Nat.mul_le_mul_left k (by omega : z.2.val ≤ n)]

noncomputable def tensor {n : ℕ} (T : Tab n) (u v : ℚ) : ℚ :=
  ∑ r : Ix n, ∑ b : Ix n, T r b * (1-u)^r.val * (1+u)^(n-r.val) * (1-v)^b.val * (1+v)^(n-b.val)

lemma spectrum_eval {n : ℕ} (k : ℕ) (T : Tab n) (u : ℚ) : (spectrum k T).eval u = tensor T u (u^k) := by
  unfold spectrum pack tensor; rw [eval_sum_poly, Fintype.sum_prod_type]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    pow_add, pow_mul, sign2]
  let B := fun s : Ix n => (1-u^k)^s.val * (1+u^k)^(n-s.val)
  calc
    _ = ∑ a : Ix n, (∑ b : Ix n, sign1 (fun s => sign1 (fun r => T r s) a) b * (u^k)^b.val)*u^a.val := by
      apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro b _; ring
    _ = ∑ a : Ix n, (∑ s : Ix n, sign1 (fun r => T r s) a * B s)*u^a.val := by simp_rw [sign1_eval]; rfl
    _ = ∑ s : Ix n, (∑ a : Ix n, sign1 (fun r => T r s) a*u^a.val)*B s := by
      simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro a _; ring
    _ = _ := by
      simp_rw [sign1_eval, Finset.sum_mul]; rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro r _; apply Finset.sum_congr rfl; intro s _; dsimp [B]; ring

end TransformSection

section JoinSection

abbrev Pins (n : ℕ) := Bool × Fin n → Option Bool
abbrev Counts (n : ℕ) := Ix n → Ix n → ℕ

def physical {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pins n) (r b : Ix n) : ℕ :=
  ((Finset.univ : Finset (Bool × Fin n → Bool)).filter (fun x =>
    (∀ v, p v = none ∨ p v = some (x v)) ∧
    (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,i))).card = r.val ∧
    (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,σ i))).card = b.val)).card

def free {n : ℕ} (p : Pins n) : ℕ := (Finset.univ.filter fun v => p v = none).card

def normalize {n : ℕ} (q : ℕ) (T : Counts n) : Tab n := fun r b => (T r b : ℚ) / 2^q

lemma normalize_injective {n : ℕ} (q : ℕ) : Function.Injective (@normalize n q) := by
  intro U V h; funext r b
  have hh : (U r b : ℚ) / 2^q = (V r b : ℚ) / 2^q := congrFun (congrFun h r) b
  exact_mod_cast (div_left_inj' (by positivity : (2 : ℚ)^q ≠ 0)).mp hh

lemma normalize_physical {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pins n) :
    normalize (free p) (physical σ p) = lawDef n σ p := rfl

def arcCode (k : ℕ) (w : ℕ × ℕ) : ℕ := w.1+k*w.2

def numer (k : ℕ) (L : List (ℕ × ℕ × Bool)) : Multiset ℕ := (numPairs L).map (arcCode k)

def denom (k : ℕ) (L : List (ℕ × ℕ × Bool)) : Multiset ℕ := (denPairs L).map (arcCode k)

def charge (k : ℕ) (L : List (ℕ × ℕ × Bool)) (m : ℕ) : ℤ :=
  (m : ℤ) * (((numer k L).count m : ℤ) - (denom k L).count m)

lemma positive_codes (k : ℕ) (hk : 0 < k) (L : List (ℕ × ℕ × Bool))
    (hL : ∀ a ∈ L, 0 < a.1 + a.2.1 ∧ a.1 ≤ a.2.1 + 1 ∧ a.2.1 ≤ a.1 + 1) :
    (∀ j ∈ numer k L, 0 < j) ∧ (∀ j ∈ denom k L, 0 < j) := by
  have hw (w : ℕ × ℕ) (h : GoodPair w) : 0 < arcCode k w := by
    have hp := h.1; dsimp [arcCode]; nlinarith [Nat.mul_le_mul_right w.2 (by omega : 1 ≤ k)]
  constructor <;> intro j hj
  · obtain ⟨w,hm,rfl⟩ := Multiset.mem_map.mp hj; exact hw w (numPairs_good L hL w hm)
  · obtain ⟨w,hm,rfl⟩ := Multiset.mem_map.mp hj; exact hw w (denPairs_good L hL w hm)

lemma minus_coe (M : Multiset ℕ) : (prodOneMinusPoly M : PowerSeries ℚ) = minusProd M := by
  induction M using Multiset.induction_on with
  | empty => simp [prodOneMinusPoly, minusProd]
  | @cons j M ih =>
    simp only [prodOneMinusPoly, minusProd, Multiset.map_cons, Multiset.prod_cons,
      Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_pow, Polynomial.coe_X] at ih ⊢
    rw [ih]

lemma arc_spectrum {n : ℕ} (k : ℕ) (σ : Equiv.Perm (Fin n)) (p : Pins n)
    (L : List (ℕ × ℕ × Bool))
    (he : ∀ u v : ℚ, polyDef n σ p u v =
      (L.map (fun a => 1 + (if a.2.2 then (1:ℚ) else -1) * u^a.1 * v^a.2.1)).prod) :
    (spectrum k (lawDef n σ p) : PowerSeries ℚ) * minusProd (denom k L) = minusProd (numer k L) := by
  have hp : spectrum k (lawDef n σ p) * prodOneMinusPoly (denom k L) = prodOneMinusPoly (numer k L) := by
    apply Polynomial.funext; intro z
    rw [Polynomial.eval_mul, spectrum_eval]
    change polyDef n σ p z (z^k) * (prodOneMinusPoly ((denPairs L).map (fun ab => ab.1+k*ab.2))).eval z =
      (prodOneMinusPoly ((numPairs L).map (fun ab => ab.1+k*ab.2))).eval z
    rw [eval_prodOneMinusPoly, eval_prodOneMinusPoly, he, list_arc_mul_den]
  simpa only [Polynomial.coe_mul, minus_coe] using congrArg (fun F : Polynomial ℚ => (F : PowerSeries ℚ)) hp

lemma arc_semantics {n : ℕ} (k : ℕ) (hk : 0 < k) (σ : Equiv.Perm (Fin n)) (p : Pins n) :
    (arcList σ p).length ≤ 2*n ∧ (spectrum k (lawDef n σ p)).coeff 0 = 1 ∧
    ∀ m : ℕ, inventory (spectrum k (lawDef n σ p) : PowerSeries ℚ) m = charge k (arcList σ p) m := by
  obtain ⟨L, hL, hlen, hshape, hv⟩ := exists_arc_factors σ p
  subst L
  obtain ⟨hposN,hposD⟩ := positive_codes k hk _ hshape
  have h := arc_spectrum k σ p _ hv
  have hc := congrArg PowerSeries.constantCoeff h
  rw [map_mul, minusProd_const _ hposD, minusProd_const _ hposN, mul_one] at hc
  refine ⟨hlen, ?_, ?_⟩
  · simpa only [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe] using hc
  · intro j
    simpa [charge] using inventory_spec _ _ _ hposN hposD h j

def stride (n : ℕ) := 2*n+3

def radius (n : ℕ) := 2*(stride n+1)*n

noncomputable def certifiedProfile {n : ℕ} (T : Counts n) (q : ℕ)
    (L : List (ℕ × ℕ × Bool)) : Prop :=
  let F := spectrum (stride n) (normalize q T)
  F.coeff 0 = 1 ∧ ∀ m ≤ radius n, inventory (F : PowerSeries ℚ) m = charge (stride n) L m

lemma arbitrary_table_iff_arc_profile {n : ℕ} (T : Counts n) (σ : Equiv.Perm (Fin n)) (p : Pins n) :
    physical σ p = T ↔ certifiedProfile T (free p) (arcList σ p) := by
  let k := stride n
  have hk : n < k := by dsimp [k,stride]; omega
  obtain ⟨_,hc,he⟩ := arc_semantics k (by omega) σ p
  constructor
  · rintro rfl; exact ⟨hc, fun m _ => he m⟩
  · rintro ⟨h₀,hjet⟩
    apply normalize_injective (free p)
    rw [normalize_physical]
    apply spectrum_injective hk
    let N := (k+1)*n
    apply polynomial_jet_injective _ _ N (spectrum_degree ..) (spectrum_degree ..) (by simp [hc]) (hc.trans h₀.symm)
    intro i hi
    have hr : N ≤ radius n := by dsimp [N,radius,k]; nlinarith
    exact (he i).trans (hjet i (hi.trans hr)).symm

lemma physical_witness_iff_profile_witness {n : ℕ} (T : Counts n) (σ : Equiv.Perm (Fin n)) :
    (∃ p : Pins n, physical σ p = T) ↔ ∃ p : Pins n, certifiedProfile T (free p) (arcList σ p) :=
  exists_congr fun p => arbitrary_table_iff_arc_profile T σ p

end JoinSection

section PairedSection

lemma count_code_good (k : ℕ) (hk : 3≤k) (M : Multiset (ℕ × ℕ)) (hM : ∀ a ∈ M, GoodPair a)
    (w : ℕ × ℕ) (hw : GoodPair w) : (M.map (arcCode k)).count (arcCode k w) = M.count w := by
  induction M using Multiset.induction_on with
  | empty => simp
  | @cons a M ih =>
    have he : arcCode k w = arcCode k a ↔ w=a := ⟨goodPair_inj hk hw (hM a (Multiset.mem_cons_self ..)),congrArg (arcCode k)⟩
    simp only [Multiset.map_cons, Multiset.count_cons,he,ih (fun v hv => hM v (Multiset.mem_cons_of_mem hv))]

lemma bivariate_charge {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pins n) (w : ℕ × ℕ) (hw : GoodPair w) :
    charge (stride n) (arcList σ p) (arcCode (stride n) w) =
      (arcCode (stride n) w : ℤ)*(((numPairs (arcList σ p)).count w : ℤ) - (denPairs (arcList σ p)).count w) := by
  obtain ⟨_,rfl,_,hL,_⟩ := exists_arc_factors σ p
  have hk : 3 ≤ stride n := by unfold stride; omega
  unfold charge numer denom
  rw [count_code_good _ hk _ (numPairs_good _ hL) w hw,count_code_good _ hk _ (denPairs_good _ hL) w hw]

end PairedSection

section DyadicSection

def twicePair (w : ℕ × ℕ) : ℕ × ℕ := (2*w.1,2*w.2)

lemma twicePair_inj {v w : ℕ × ℕ} : twicePair v = twicePair w ↔ v=w := by
  obtain ⟨r,b⟩:=v; obtain ⟨a,c⟩:=w; simp [twicePair,Prod.ext_iff]

def perDirection (w : ℕ × ℕ) (s : Bool) : List (ℕ × ℕ × Bool) → ℕ
  | [] => 0
  | (r,b,f)::L => (if w=(r,b) ∧ s=f then 1 else 0)+perDirection w s L

def carried (w : ℕ × ℕ) : List (ℕ × ℕ × Bool) → ℕ
  | [] => 0
  | (r,b,f)::L => (if w=twicePair (r,b) ∧ f=true then 1 else 0)+carried w L

def imbalance (L : List (ℕ × ℕ × Bool)) (w : ℕ × ℕ) : ℤ :=
  ((numPairs L).count w : ℤ) - (denPairs L).count w

lemma imbalance_eq (L : List (ℕ × ℕ × Bool)) (w : ℕ × ℕ) : imbalance L w =
    perDirection w false L - (perDirection w true L : ℤ) + carried w L := by
  induction L with
  | nil => simp [imbalance,numPairs,denPairs,perDirection,carried]
  | cons a L ih =>
    obtain ⟨r,b,f⟩ := a
    unfold imbalance at ih ⊢
    cases f <;> by_cases hw : w=(r,b) <;> by_cases hd : w=twicePair (r,b) <;>
      simp [perDirection,carried,numPairs,denPairs,Multiset.count_cons,twicePair,hw,hd] at * <;> omega

lemma carried_twice (L : List (ℕ × ℕ × Bool)) (w : ℕ × ℕ) :
    carried (twicePair w) L = perDirection w true L := by
  induction L with
  | nil => rfl
  | cons a L ih => obtain ⟨r,b,f⟩ := a; cases f <;> simp [perDirection,carried,twicePair_inj,ih]

lemma carried_primitive (L : List (ℕ × ℕ × Bool)) {w : ℕ × ℕ} (h : ∀ a, w≠twicePair a) : carried w L=0 := by
  induction L with
  | nil => rfl
  | cons a L ih => obtain ⟨r,b,f⟩ := a; simp [carried,h,ih]

lemma perDirection_zero (L : List (ℕ × ℕ × Bool)) (w : ℕ × ℕ) (s : Bool)
    (h : ∀ a ∈ L, w ≠ (a.1,a.2.1)) : perDirection w s L = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih => obtain ⟨r,b,f⟩:=a; simp [perDirection,h _ List.mem_cons_self,ih (fun _ hm => h _ (List.mem_cons_of_mem _ hm))]

lemma imbalance_at_twice (L : List (ℕ × ℕ × Bool)) (w : ℕ × ℕ) : imbalance L (twicePair w) =
    perDirection (twicePair w) false L - (perDirection (twicePair w) true L : ℤ) + perDirection w true L := by
  rw [imbalance_eq,carried_twice]

lemma imbalance_primitive (L : List (ℕ × ℕ × Bool)) {w : ℕ × ℕ} (h : ∀ a, w≠twicePair a) :
    imbalance L w = perDirection w false L - (perDirection w true L : ℤ) := by
  rw [imbalance_eq,carried_primitive L h, Nat.cast_zero, add_zero]

lemma unit_skew_no_half (w : ℕ × ℕ) (h : w.1+1=w.2 ∨ w.2+1=w.1) : ∀ a, w≠twicePair a := by
  rintro ⟨r,b⟩ e; subst w; dsimp [twicePair] at h; omega

lemma physical_offdiag_counts {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pins n) (w : ℕ × ℕ)
    (h : w.1+1=w.2 ∨ w.2+1=w.1) :
    (perDirection w true (arcList σ p) : ℤ) = imbalance (arcList σ p) (twicePair w) ∧
    (perDirection w false (arcList σ p) : ℤ) = imbalance (arcList σ p) w + imbalance (arcList σ p) (twicePair w) := by
  obtain ⟨_,rfl,_,hl,_⟩ := exists_arc_factors σ p
  have bad (a : ℕ × ℕ × Bool) (ha : a ∈ arcList σ p) : twicePair w ≠ (a.1,a.2.1) := by
    obtain ⟨_,h1,h2⟩ := hl a ha
    intro he; have hr := congrArg Prod.fst he; have hb := congrArg Prod.snd he
    dsimp [twicePair] at hr hb; omega
  have he := imbalance_at_twice (arcList σ p) w
  rw [perDirection_zero _ _ false bad,perDirection_zero _ _ true bad] at he
  have he' := imbalance_primitive (arcList σ p) (unit_skew_no_half w h)
  exact ⟨by omega,by omega⟩

lemma physical_diagonal_counts {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pins n) (j : ℕ) :
    (perDirection (j,j) false (arcList σ p) : ℤ) = imbalance (arcList σ p) (j,j) + perDirection (j,j) true (arcList σ p) -
      (if 2 ∣ j then (perDirection (j/2,j/2) true (arcList σ p) : ℤ) else 0) := by
  by_cases h : 2 ∣ j
  · obtain ⟨k,rfl⟩:=h; have he := imbalance_at_twice (arcList σ p) (k,k)
    simp [twicePair] at he; simp; omega
  · have prim (w : ℕ × ℕ) : (j,j) ≠ twicePair w := by
      intro he; apply h; exact ⟨w.1,congrArg Prod.fst he⟩
    have he := imbalance_primitive (arcList σ p) prim
    rw [if_neg h]; omega

end DyadicSection

section MassGeomSection

noncomputable def arcCluster {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pins n) (e : Bool × Fin n) : Finset (Bool × Fin n) := by
  classical
  exact Finset.univ.filter (fun v => Relation.EqvGen (ArcStep σ p) e v)

noncomputable def components {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pins n) := Finset.univ.image (arcCluster σ p)

def cutEdges {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pins n) := Finset.univ.filter (fun e => qE σ p e ≠ none)

noncomputable def floating {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pins n) := components σ p \ (cutEdges σ p).image (arcCluster σ p)

lemma in_arcCluster {n : ℕ} {σ : Equiv.Perm (Fin n)} {p : Pins n} {u v : Bool × Fin n} :
    v ∈ arcCluster σ p u ↔ Relation.EqvGen (ArcStep σ p) u v := by classical simp [arcCluster]

lemma clusters_eq {n : ℕ} {σ : Equiv.Perm (Fin n)} {p : Pins n} {u v : Bool × Fin n} :
    arcCluster σ p u = arcCluster σ p v ↔ Relation.EqvGen (ArcStep σ p) u v := by
  constructor
  · intro h; apply in_arcCluster.mp; rw [h]; exact in_arcCluster.mpr (.refl _)
  · intro h; ext a; simp only [in_arcCluster]
    exact ⟨fun h' => .trans _ _ _ (.symm _ _ h) h',fun h' => .trans _ _ _ h h'⟩

lemma arcs_plus_free {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pins n) :
    (arcList σ p).length+free p = 2*n+(floating σ p).card := by
  classical
  have hlen : (arcList σ p).length=(components σ p).card := by
    simp [arcList,components]; apply congrArg Finset.card; apply Finset.image_congr; intro e _; ext v; simp only [in_arcCluster,Finset.mem_filter,Finset.mem_univ,true_and]
  have sub : (cutEdges σ p).image (arcCluster σ p) ⊆ components σ p := by
    rintro a ha; obtain ⟨e,_,rfl⟩:=Finset.mem_image.mp ha; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hcards := Finset.card_sdiff_add_card_eq_card sub
  have hcut : ((cutEdges σ p).image (arcCluster σ p)).card = (cutEdges σ p).card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb he
    exact stop_unique (clusters_eq.mp he) (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  have hm : (cutEdges σ p).image (headV σ) = Finset.univ.filter (fun v => p v ≠ none) := by
    ext v; constructor
    · intro hv; obtain ⟨e,he,rfl⟩:=Finset.mem_image.mp hv; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).2⟩
    · intro hv; refine Finset.mem_image.mpr ⟨(headV σ).symm v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,by simp⟩
      simpa only [qE,Equiv.apply_symm_apply] using (Finset.mem_filter.mp hv).2
  have hc := Finset.card_image_of_injective (cutEdges σ p) (headV σ).injective
  rw [hm] at hc
  have htot := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun v => p v = none)
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at htot
  have htot' : free p+(cutEdges σ p).card = 2*n := by
    rw [← hc]
    convert htot using 1 <;> congr 2 <;> ext x <;> simp only [free,Finset.mem_filter,Finset.mem_univ,true_and]
  unfold floating; omega

lemma floating_facts {n : ℕ} {σ : Equiv.Perm (Fin n)} {p : Pins n} {c : Finset (Bool × Fin n)} (hc : c ∈ floating σ p) :
    (∀ e ∈ c, c=arcCluster σ p e) ∧ (∀ e ∈ c, qE σ p e=none) ∧
    (∀ e, (nextE σ) e ∈ c ↔ e ∈ c) ∧ ∃ i : Fin n, (false,i) ∈ c := by
  classical
  obtain ⟨hc',hno⟩:=Finset.mem_sdiff.mp hc
  obtain ⟨e,_,rfl⟩:=Finset.mem_image.mp hc'
  have hm (u : Bool × Fin n) (hu : u ∈ arcCluster σ p e) := clusters_eq.mpr (in_arcCluster.mp hu)
  have hfree (u : Bool × Fin n) (hu : u ∈ arcCluster σ p e) : qE σ p u = none := by
    by_contra h
    apply hno; exact Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,(hm u hu).symm⟩
  have forward (u : Bool × Fin n) (hu : u ∈ arcCluster σ p e) : nextE σ u ∈ arcCluster σ p e :=
    in_arcCluster.mpr (.trans _ _ _ (in_arcCluster.mp hu) (.rel _ _ ⟨hfree u hu,rfl⟩))
  have hsub : (arcCluster σ p e).image (nextE σ) ⊆ arcCluster σ p e := by
    intro u hu; obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hu; exact forward v hv
  have him := Finset.eq_of_subset_of_card_le hsub (Finset.card_image_of_injective _ (nextE σ).injective).ge
  have hiff (u : Bool × Fin n) : nextE σ u ∈ arcCluster σ p e ↔ u ∈ arcCluster σ p e := by
    refine ⟨?_,forward u⟩; intro hx; rw [← him] at hx
    obtain ⟨v,hv,hvu⟩:=Finset.mem_image.mp hx; exact (nextE σ).injective hvu ▸ hv
  refine ⟨hm,hfree,hiff,?_⟩
  have hself : e ∈ arcCluster σ p e := in_arcCluster.mpr (.refl _)
  obtain ⟨b,i⟩:=e; cases b
  · exact ⟨i,hself⟩
  · exact ⟨σ i,forward _ hself⟩

lemma floating_bounded {n d : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pins n) (root : Fin d → Fin n)
    (cover : ∀ i, ∃ a : Fin d, ∃ h : Fin n, (σ^h.val) (root a)=i) : (floating σ p).card ≤ d := by
  classical
  let cls (a : Fin d) := arcCluster σ p (false,root a)
  have hsub : floating σ p ⊆ Finset.univ.image cls := by
    intro c hc
    obtain ⟨hc',_,hf,i,hi⟩:=floating_facts hc
    have twice (u : Fin n) : (false,σ u) ∈ c ↔ (false,u) ∈ c := (hf (true,u)).trans (hf (false,u))
    have power (u : Fin n) (k : ℕ) : (false,(σ^k) u) ∈ c ↔ (false,u) ∈ c := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ',Equiv.Perm.mul_apply,twice,ih]
    obtain ⟨a,h,he⟩:=cover i
    rw [← he] at hi
    exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,(hc' _ ((power (root a) h.val).mp hi)).symm⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (by simp))

lemma floating_positive_diagonal {n : ℕ} {σ : Equiv.Perm (Fin n)} {p : Pins n} {c : Finset (Bool × Fin n)} (hc : c ∈ floating σ p) :
    (c.filter (fun e => e.1=false)).card=(c.filter (fun e => e.1=true)).card ∧
      (∏ e ∈ c, (epsE σ p e * epsE σ p ((nextE σ).symm e)))=1 := by
  classical
  obtain ⟨_,hcut,hmem,_⟩:=floating_facts hc
  have flip (u : Bool × Fin n) : ((nextE σ) u).1 = !u.1 := by obtain ⟨b,i⟩:=u; cases b <;> rfl
  have hprev (e : Bool × Fin n) (he : e∈c) : (nextE σ).symm e ∈ c := (hmem _).mp (by simpa using he)
  have heps (e : Bool × Fin n) (he : e∈c) : epsE σ p e=1 := by
    have hz : p (headV σ e)=none := hcut e he; simp [epsE,epsV,hz]
  constructor
  · have eq : (c.filter (fun e => e.1=false)).image (nextE σ) = c.filter (fun e => e.1=true) := by
      ext u; constructor
      · intro h; obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp h; obtain ⟨hvc,hb⟩:=Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr ⟨(hmem _).mpr hvc,by simp [flip,hb]⟩
      · intro h; obtain ⟨hu,hcol⟩:=Finset.mem_filter.mp h
        refine Finset.mem_image.mpr ⟨(nextE σ).symm u,Finset.mem_filter.mpr ⟨hprev _ hu,?_⟩,by simp⟩
        have hflip := flip ((nextE σ).symm u); rw [Equiv.apply_symm_apply,hcol] at hflip
        cases h : ((nextE σ).symm u).1 <;> simp [h] at hflip ⊢
    rw [←eq,Finset.card_image_of_injective _ (nextE σ).injective]
  · apply Finset.prod_eq_one; intro e he; rw [heps e he,heps _ (hprev e he),mul_one]

end MassGeomSection

section IntegralSection

noncomputable def termI {n : ℕ} (k : ℕ) (r b : Ix n) : Polynomial ℤ :=
  (1-Polynomial.X)^r.val*(1+Polynomial.X)^(n-r.val)*
    (1-Polynomial.X^k)^b.val*(1+Polynomial.X^k)^(n-b.val)

noncomputable def inputRow {n : ℕ} (k : ℕ) (T : Counts n) (m : ℕ) : ℤ :=
  ∑ r : Ix n, ∑ b : Ix n, (T r b : ℤ) * (termI k r b).coeff m

lemma spectrum_as_sum {n : ℕ} (k : ℕ) (T : Tab n) : spectrum k T =
    ∑ r : Ix n, ∑ b : Ix n, Polynomial.C (T r b) * (termI k r b).map (Int.castRingHom ℚ) := by
  apply Polynomial.funext; intro z
  rw [spectrum_eval,eval_sum_poly]; unfold tensor; apply Finset.sum_congr rfl; intro r _
  rw [eval_sum_poly]; apply Finset.sum_congr rfl; intro b _
  simp [termI, mul_assoc]

lemma inputRow_eq {n : ℕ} (k q : ℕ) (T : Counts n) (m : ℕ) :
    (inputRow k T m : ℚ) = 2^q * (spectrum k (normalize q T)).coeff m := by
  rw [spectrum_as_sum, coeff_sum_poly, Finset.mul_sum]
  unfold inputRow; push_cast; apply Finset.sum_congr rfl; intro r _
  rw [coeff_sum_poly, Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_map]; change _ = 2^q * (((T r b : ℚ)/2^q)*_)
  field_simp; rfl

def logRec {R : Type} [Ring R] (a : ℕ → R) (m : ℕ) : R :=
  -(m : R)*a m - ∑ i : Fin m, logRec a i.val * a (m-i.val)
termination_by m

def chargeRec {R : Type} [Ring R] (ρ : R) (L : ℕ → R) (m : ℕ) : R :=
  L m - ∑ i : Fin m, if 0 < i.val ∧ i.val ∣ m then ρ^(m-i.val) * chargeRec ρ L i.val else 0
termination_by m

def dilated {R : Type} [Ring R] (ρ : R) (a : ℕ → R) (m : ℕ) : R :=
  if m = 0 then 1 else ρ^(m-1)*a m

def decode {R : Type} [Ring R] (ρ : R) (a : ℕ → R) (m : ℕ) : R :=
  chargeRec ρ (logRec (dilated ρ a)) m

lemma log_step {R : Type} [Ring R] (a : ℕ → R) (m : ℕ) :
    logRec a m = -(m : R)*a m - ∑ i : Fin m, logRec a i.val * a (m-i.val) := by rw [logRec]

lemma charge_step {R : Type} [Ring R] (ρ : R) (L : ℕ → R) (m : ℕ) :
    chargeRec ρ L m = L m - ∑ i : Fin m, if 0 < i.val ∧ i.val ∣ m then ρ^(m-i.val) * chargeRec ρ L i.val else 0 := by rw [chargeRec]

lemma logRec_map {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (a : ℕ → R) (m : ℕ) :
    φ (logRec a m) = logRec (φ ∘ a) m := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    rw [log_step a m, log_step (φ ∘ a) m]; simp [map_sum, ih]

lemma chargeRec_map {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (ρ : R) (L : ℕ → R) (m : ℕ) :
    φ (chargeRec ρ L m) = chargeRec (φ ρ) (φ ∘ L) m := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    rw [charge_step ρ L m, charge_step (φ ρ) (φ ∘ L) m]; simp [map_sum, apply_ite φ, ih]

lemma decode_map {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (ρ : R) (a : ℕ → R) (m : ℕ) :
    φ (decode ρ a m) = decode (φ ρ) (φ ∘ a) m := by
  have h : φ ∘ dilated ρ a = dilated (φ ρ) (φ ∘ a) := by
    funext j; by_cases hj : j = 0 <;> simp [dilated,hj]
  have he : φ ∘ logRec (dilated ρ a) = logRec (dilated (φ ρ) (φ ∘ a)) := by
    funext j; simpa only [Function.comp_apply, logRec_map, h]
  rw [decode, decode, chargeRec_map, he]

lemma logRec_dilate {R : Type} [CommRing R] (ρ : R) (a : ℕ → R) (m : ℕ) :
    logRec (fun j => ρ^j*a j) m = ρ^m * logRec a m := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    rw [log_step (fun j => ρ^j*a j) m, log_step a m, mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl; intro i _; rw [ih i.val i.isLt]
      have hp : ρ^i.val * ρ^(m-i.val) = ρ^m := by rw [← pow_add]; congr 1; omega
      linear_combination logRec a i.val * a (m-i.val) * hp

lemma logRec_euler (f : PowerSeries ℚ) (hf : PowerSeries.constantCoeff f = 1) (m : ℕ) :
    logRec (fun i => PowerSeries.coeff i f) m = PowerSeries.coeff m (logJet f) := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    have he := congrArg (PowerSeries.coeff m) (logJet_mul_self f (by simp [hf]))
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ,
      Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff,hf,mul_one,coeff_euler] at he
    rw [logRec, Fin.sum_univ_eq_sum_range (fun j => logRec (fun i => PowerSeries.coeff i f) j * PowerSeries.coeff (m-j) f)]
    have hs : (∑ i ∈ Finset.range m, logRec (fun j => PowerSeries.coeff j f) i * PowerSeries.coeff (m-i) f) =
        ∑ i ∈ Finset.range m, PowerSeries.coeff i (logJet f) * PowerSeries.coeff (m-i) f := by
      apply Finset.sum_congr rfl; intro i hi; rw [ih i (Finset.mem_range.mp hi)]
    rw [hs]; linarith

lemma chargeRec_dilated (ρ : ℚ) (s : ℕ → ℚ) (m : ℕ) :
    chargeRec ρ (fun j => ρ^j*s j) m = ρ^m * undiv s m := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    rw [chargeRec, undiv, mul_sub, Finset.mul_sum]; congr 1
    apply Finset.sum_congr rfl; intro i _
    split_ifs
    · rw [ih i.val i.isLt, ← mul_assoc, ← pow_add, Nat.sub_add_cancel i.isLt.le]
    · simp

lemma decode_fraction_free {n : ℕ} (k q : ℕ) (T : Counts n)
    (h0 : (spectrum k (normalize q T)).coeff 0 = 1) (m : ℕ) :
    (decode (R := ℤ) ((2:ℤ)^q) (inputRow k T) m : ℚ) =
      ((2:ℚ)^q)^m * inventory (spectrum k (normalize q T) : PowerSeries ℚ) m := by
  let F : PowerSeries ℚ := spectrum k (normalize q T)
  have hf : PowerSeries.constantCoeff F = 1 := by
    simpa only [F, ← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe] using h0
  let ρ := (2:ℚ)^q
  have ha : dilated ρ ((Int.castRingHom ℚ) ∘ inputRow k T) = fun j => ρ^j * PowerSeries.coeff j F := by
    funext j; cases j with
    | zero => simp [dilated,hf]
    | succ j =>
      simp only [dilated, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one, Function.comp_apply, F, Polynomial.coeff_coe]
      change ρ^j*(inputRow k T (j+1) : ℚ) = ρ^(j+1)*(spectrum k (normalize q T)).coeff (j+1)
      rw [inputRow_eq k q T (j+1), pow_succ]; dsimp [ρ]; ring
  have hmap := decode_map (Int.castRingHom ℚ) ((2:ℤ)^q) (inputRow k T) m
  change (Int.castRingHom ℚ) (decode ((2:ℤ)^q) (inputRow k T) m) = _
  rw [hmap]; simp only [map_pow, map_ofNat]
  change chargeRec ρ (logRec (dilated ρ ((Int.castRingHom ℚ) ∘ inputRow k T))) m = ρ^m * inventory F m
  rw [ha]
  have hL : logRec (fun j => ρ^j * PowerSeries.coeff j F) = fun j => ρ^j * PowerSeries.coeff j (logJet F) := by
    funext j; rw [logRec_dilate, logRec_euler F hf]
  rw [hL, chargeRec_dilated]; rfl

lemma arbitrary_table_integral_test {n : ℕ} (T : Counts n) (σ : Equiv.Perm (Fin n)) (p : Pins n) :
    physical σ p = T ↔
    inputRow (stride n) T 0 = (2:ℤ)^(free p) ∧
      ∀ m ≤ radius n, decode ((2:ℤ)^(free p)) (inputRow (stride n) T) m =
        ((2:ℤ)^(free p))^m * charge (stride n) (arcList σ p) m := by
  rw [arbitrary_table_iff_arc_profile]
  have hc := inputRow_eq (stride n) (free p) T 0
  have h0 : (spectrum (stride n) (normalize (free p) T)).coeff 0 = 1 ↔
      inputRow (stride n) T 0 = (2:ℤ)^(free p) := by
    constructor
    · intro he; rw [he,mul_one] at hc; exact_mod_cast hc
    · intro he; rw [he, Int.cast_pow,Int.cast_ofNat] at hc
      exact mul_left_cancel₀ (by positivity : (2:ℚ)^free p ≠ 0) (by simpa using hc.symm :
        (2:ℚ)^free p*(spectrum (stride n) (normalize (free p) T)).coeff 0=(2:ℚ)^free p*1)
  constructor
  · rintro ⟨hb,hj⟩; refine ⟨h0.mp hb,?_⟩; intro m hm
    have he := decode_fraction_free (stride n) (free p) T hb m
    rw [hj m hm] at he; exact_mod_cast he
  · rintro ⟨hb,hj⟩; refine ⟨h0.mpr hb,?_⟩; intro m hm
    have he := decode_fraction_free (stride n) (free p) T (h0.mpr hb) m
    rw [hj m hm,Int.cast_mul,Int.cast_pow,Int.cast_pow,Int.cast_ofNat] at he
    exact mul_left_cancel₀ (by positivity) he.symm

end IntegralSection

section GateBaseSection

namespace Compiler

namespace GateBridge

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

def Legal (op : GateOp) (arity : ℕ) : Prop :=
  ((op = .and ∨ op = .or) ∧ arity = 2) ∨ (op = .not ∧ arity = 1)

variable {α : Type*}

def Scheduled (n : ℕ) (F : α → (Fin n → Bool) → Bool) (k : ℕ) (S : Set α) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack n ⟨gs, 0⟩ ∧ (∀ g ∈ gs, Legal g.op g.inputs.length) ∧
    ∀ a ∈ S, ∃ i : ℕ, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x

theorem wireLength (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length + C.gates.length := by
  rcases C with ⟨gs, out⟩
  change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    w).length = w.length + gs.length
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem start {n : ℕ} {F : α → (Fin n → Bool) → Bool}
    (input : Fin n → α) (h : ∀ i x, F (input i) x = x i) :
    Scheduled n F 0 (Set.range input) := by
  refine ⟨[], rfl, ?_, ?_, ?_⟩
  · simp [ReadsBack]
  · simp
  · intro a ha
    obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
    refine ⟨i.val, by simpa using i.isLt, fun x => ?_⟩
    change (List.ofFn x).getD i.val false = F (input i) x
    rw [List.getD_eq_getElem _ _ (by simpa using i.isLt), List.getElem_ofFn, h i x]

theorem restrict {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S T : Set α}
    (h : Scheduled n F k S) (hsub : T ⊆ S) : Scheduled n F k T := by
  obtain ⟨gs, hs, hr, hf, hw⟩ := h
  exact ⟨gs, hs, hr, hf, fun a ha => hw a (hsub ha)⟩

theorem realizeDeps {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : ℕ, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x)
    (deps : List α) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List ℕ, is.length = deps.length ∧ (∀ i ∈ is, i < n + k) ∧
      ∀ x : Fin n → Bool,
        is.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) =
          deps.map (fun a => F a x) := by
  induction deps with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons a deps ih =>
    obtain ⟨i, hi, hval⟩ := hw a (hdeps a List.mem_cons_self)
    obtain ⟨is, hlen, hbound, hvals⟩ := ih (fun b hb => hdeps b (List.mem_cons_of_mem a hb))
    refine ⟨i :: is, by simp [hlen], ?_, fun x => ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hbound j hj
    · simp only [List.map_cons, hval x, hvals x]

theorem push {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    (h : Scheduled n F k S) (op : GateOp) (deps : List α) (out : α)
    (hop : Legal op deps.length) (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, F out x = op.eval (deps.map fun a => F a x)) :
    Scheduled n F (k + 1) (insert out S) := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨is, his, hbound, hvalues⟩ := realizeDeps hw deps hdeps
  let g : Gate := ⟨op, is⟩
  have hlength (x : Fin n → Bool) :
      ((Circuit.mk gs 0).wires (List.ofFn x)).length = n + k := by
    rw [wireLength]
    simpa using congrArg (n + ·) hgs
  have hsnoc (x : Fin n → Bool) :
      (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [F out x] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (Circuit.mk gs 0).wires (List.ofFn x) ++
      [op.eval (is.map fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)] =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [F out x]
    rw [hvalues x, hval x]
  refine ⟨gs ++ [g], by simp [hgs], ?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (gs ++ [g]).length at hj
    change i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hr j hj' i hi
    · have heq : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      have hi' : i ∈ is := by simpa [g] using hi
      simpa [hgs] using hbound i hi'
  · intro g' hg'
    change g' ∈ gs ++ [g] at hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hf g' hg'
    · have heq : g' = g := List.mem_singleton.mp hg'
      subst g'
      change Legal op is.length
      simpa only [his] using hop
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · refine ⟨n + k, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append_right _ _ _ _ (by simp [hlength x])]
      simp [hlength x]
    · obtain ⟨i, hi, hval'⟩ := hw a ha
      refine ⟨i, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by simpa [hlength x] using hi), hval' x]

end GateBridge

namespace Build

open PEqualNP.CircuitLowerBounds

variable {n : Nat}
abbrev Sig (n : Nat) := (Fin n → Bool) → Bool
def Build (A B : Set (Sig n)) (b : Nat) : Prop :=
  True ∧ (∀ {m S}, GateBridge.Scheduled n id m S → A ⊆ S →
    ∃ c ≤ b, GateBridge.Scheduled n id (m+c) (S ∪ B))

theorem Build.run {A B : Set (Sig n)} {b m S} (H : Build A B b)
    (HS : GateBridge.Scheduled n id m S) (hA : A ⊆ S) :
    ∃ c ≤ b, GateBridge.Scheduled n id (m+c) (S ∪ B) := H.2 HS hA

theorem idle {A B : Set (Sig n)} (h : B ⊆ A) : Build A B 0 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨0, Nat.le_refl _, ?_⟩
  simpa [Set.union_eq_left.mpr (h.trans hA)] using HS

theorem relax {A B C D : Set (Sig n)} {b d : Nat}
    (H : Build A B b) (hA : A ⊆ C) (hB : D ⊆ B) (h : b ≤ d) : Build C D d := by
  refine ⟨trivial, ?_⟩
  intro m S HS hC
  obtain ⟨c,hc,HS'⟩ := H.run HS (hA.trans hC)
  exact ⟨c,hc.trans h,GateBridge.restrict HS' (Set.union_subset_union le_rfl hB)⟩

theorem seq {A B C : Set (Sig n)} {b c : Nat}
    (H : Build A B b) (J : Build (A ∪ B) C c) : Build A (B ∪ C) (b+c) := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  obtain ⟨d,hd,K⟩ := H.run HS hA
  obtain ⟨e,he,K'⟩ := J.run K (Set.union_subset_union hA le_rfl)
  exact ⟨d+e,Nat.add_le_add hd he,by simpa [Nat.add_assoc,Set.union_assoc] using K'⟩

theorem one {A : Set (Sig n)} (op : GateOp) (deps : List (Sig n))
    (hop : GateBridge.Legal op deps.length)
    (hd : ∀ g ∈ deps, g ∈ A) (f : Sig n)
    (hv : ∀ x, f x = op.eval (deps.map fun g => g x)) : Build A {f} 1 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨1,le_rfl,?_⟩
  have h := GateBridge.push HS op deps f hop (fun g hg => hA (hd g hg)) hv
  rw [Set.insert_eq] at h
  exact GateBridge.restrict h (by intro g hg; exact hg.elim Or.inr Or.inl)

def an (f g : Sig n) : Sig n := fun x => f x && g x
def or (f g : Sig n) : Sig n := fun x => f x || g x
def nt (f : Sig n) : Sig n := fun x => !f x
def xo (f g : Sig n) : Sig n := fun x => xor (f x) (g x)

theorem andG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {an f g} 1 :=
  one .and [f,g] (by simp [GateBridge.Legal]) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, an])

theorem orG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {or f g} 1 :=
  one .or [f,g] (by simp [GateBridge.Legal]) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, or])

theorem notG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) : Build A {nt f} 1 :=
  one .not [f] (by simp [GateBridge.Legal]) (by simpa using hf) _ (by simp [GateOp.eval, nt])

theorem xorG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {xo f g} 4 := by
  have he : xo f g = an (or f g) (nt (an f g)) := by
    funext x
    change xor (f x) (g x) = ((f x || g x) && !(f x && g x))
    cases f x <;> cases g x <;> rfl
  rw [he]
  have h₁ := andG hf hg
  have h₂ := orG (A := A ∪ {an f g}) (Or.inl hf) (Or.inl hg)
  have h₃ := notG (A := A ∪ ({an f g} ∪ {or f g})) (f := an f g) (by simp)
  have h₄ := andG (A := A ∪ (({an f g} ∪ {or f g}) ∪ {nt (an f g)}))
    (f := or f g) (g := nt (an f g)) (by simp) (by simp)
  exact relax (seq (seq (seq h₁ h₂) h₃) h₄) le_rfl (by simp) le_rfl

theorem topological {α : Type*} [DecidableEq α] {A : Set (Sig n)}
    (F : α → Sig n) (rank cost : α → Nat) (s : Finset α)
    (H : ∀ i ∈ s, Build (A ∪ {f | ∃ j ∈ s, rank j < rank i ∧ f = F j}) {F i} (cost i)) :
    Build A {f | ∃ i ∈ s, f = F i} (∑ i ∈ s, cost i) := by
  classical
  induction s using Finset.strongInduction with
  | H s IH =>
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi, himax⟩ := Finset.exists_max_image s rank hs
      have Hsub : s.erase i ⊂ s := Finset.erase_ssubset hi
      have hstep (j : α) (hj : j ∈ s.erase i) (l : α) (hl : l ∈ s)
          (hlt : rank l < rank j) : l ∈ s.erase i := by
        refine Finset.mem_erase.mpr ⟨?_,hl⟩
        intro heq
        subst l
        exact (Nat.not_lt_of_ge (himax j (Finset.mem_of_mem_erase hj))) hlt
      have Hs := IH (s.erase i) Hsub fun j hj =>
        relax (H j (Finset.mem_of_mem_erase hj))
          (by rintro f (hf | ⟨l,hl,hlt,rfl⟩)
              · exact Or.inl hf
              · exact Or.inr ⟨l,hstep j hj l hl hlt,hlt,rfl⟩) le_rfl le_rfl
      have Hi := relax (H i hi) (C := A ∪ {f | ∃ j ∈ s.erase i, f = F j})
        (by rintro f (hf | ⟨j,hj,hlt,rfl⟩)
            · exact Or.inl hf
            · exact Or.inr ⟨j,Finset.mem_erase.mpr ⟨by aesop, hj⟩,rfl⟩) le_rfl le_rfl
      refine relax (seq Hs Hi) le_rfl ?_ ?_
      · rintro f ⟨j,hj,rfl⟩
        by_cases he : j = i
        · exact Or.inr (by simp [he])
        · exact Or.inl ⟨j,Finset.mem_erase.mpr ⟨he,hj⟩,rfl⟩
      · rw [Finset.sum_erase_add _ _ hi]
    · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      exact relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by simp) (by simp)
theorem anyG {A : Set (Sig n)} (xs : List (Sig n))
    (hs : ∀ f ∈ xs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => xs.any (fun f => f x)} xs.length := by
  induction xs with
  | nil =>
    exact idle (Set.singleton_subset_iff.mpr hfalse)
  | cons f xs IH =>
    have H := IH (fun g hg => hs g (List.mem_cons_of_mem f hg))
    have K := orG (A := A ∪ {fun x => xs.any (fun g => g x)})
      (Or.inl (hs f List.mem_cons_self)) (Or.inr rfl)
    exact relax (seq H K) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by simp)

theorem allG {α : Type*} [Fintype α] {A : Set (Sig n)}
    (F : α → Sig n) (c : Nat) (H : ∀ i, Build A {F i} c) :
    Build A (Set.range F) (Fintype.card α*c) := by
  classical
  have K := topological F (fun _ => 0) (fun _ => c) Finset.univ
    (fun i _ => relax (H i) Set.subset_union_left le_rfl le_rfl)
  refine relax (by simpa only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul] using K) le_rfl ?_ le_rfl
  rintro _ ⟨i,rfl⟩
  exact ⟨i,Finset.mem_univ _,rfl⟩

theorem finG {k : Nat} {A : Set (Sig n)} (F : Fin k → Sig n) (c : Nat)
    (H : ∀ i, Build A {F i} c) : Build A (Set.range F) (k*c) := by
  simpa only [Fintype.card_fin] using allG F c H

def inputs (n : Nat) : Set (Sig n) := Set.range (fun i : Fin n => fun v => v i)

def base (n : Nat) : Set (Sig n) := inputs n ∪ {fun _ => false, fun _ => true}

theorem thenG {A B C : Set (Sig n)} {b c : Nat}
    (h : Build A B b) (j : Build (A ∪ B) C c) : Build A C (b+c) :=
  relax (seq h j) le_rfl Set.subset_union_right le_rfl

theorem bothG {A B C : Set (Sig n)} {b c : Nat}
    (h : Build A B b) (j : Build A C c) : Build A (B ∪ C) (b+c) :=
  seq h (relax j Set.subset_union_left le_rfl le_rfl)

def mx (s f g : Sig n) : Sig n := fun x => if s x then g x else f x

theorem muxG {A : Set (Sig n)} {s f g : Sig n} (hs : s ∈ A) (hf : f ∈ A) (hg : g ∈ A) :
    Build A {mx s f g} 4 := by
  have he : mx s f g = or (an (nt s) f) (an s g) := by
    funext x
    change (if s x then g x else f x) = ((!(s x) && f x) || (s x && g x))
    cases s x <;> cases f x <;> cases g x <;> rfl
  rw [he]
  have h₁ := notG hs
  have h₂ := andG (A := A ∪ {nt s}) (f := nt s) (by simp) (Or.inl hf)
  have h₃ := andG (A := A ∪ ({nt s} ∪ {an (nt s) f}))
    (Or.inl hs) (Or.inl hg)
  have h₄ := orG (A := A ∪ (({nt s} ∪ {an (nt s) f}) ∪ {an s g}))
    (f := an (nt s) f) (g := an s g) (by simp) (by simp)
  exact relax (seq (seq (seq h₁ h₂) h₃) h₄) le_rfl (by simp) le_rfl
theorem everyG {A : Set (Sig n)} (xs : List (Sig n))
    (hs : ∀ f ∈ xs, f ∈ A) (htrue : (fun _ => true) ∈ A) :
    Build A {fun x => xs.all (fun f => f x)} xs.length := by
  induction xs with
  | nil => exact idle (Set.singleton_subset_iff.mpr htrue)
  | cons f xs ih =>
    have H := ih (fun g hg => hs g (List.mem_cons_of_mem f hg))
    have K := andG (A := A ∪ {fun x => xs.all (fun g => g x)})
      (Or.inl (hs f List.mem_cons_self)) (Or.inr rfl)
    exact relax (seq H K) le_rfl Set.subset_union_right (by simp)

def familyOut {ι : Type*} (s : Finset ι) (B : ι → Set (Sig n)) : Set (Sig n) :=
  {f | ∃ i ∈ s, f ∈ B i}

lemma familyG {ι : Type*} [Fintype ι] {A : Set (Sig n)} (B : ι → Set (Sig n)) (c : Nat)
    (h : ∀ i, Build A (B i) c) : Build A (familyOut Finset.univ B) (Fintype.card ι * c) := by
  classical
  suffices ∀ s, Build A (familyOut s B) (s.card * c) by simpa [Finset.card_univ] using this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa [familyOut] using (idle (A := A) (B := ∅) (by simp))
  | @insert i s hi ih =>
    have hnew := bothG ih (h i)
    refine relax hnew le_rfl ?_ (by rw [Finset.card_insert_of_notMem hi, Nat.succ_mul])
    rintro v ⟨j, hj, hv⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Or.inr hv
    · exact Or.inl ⟨j, hj, hv⟩

lemma family_mem {ι : Type*} [Fintype ι] {B : ι → Set (Sig n)} {i : ι} {f : Sig n}
    (h : f ∈ B i) : f ∈ familyOut Finset.univ B := ⟨i, Finset.mem_univ i, h⟩

end Build
end Compiler

end GateBaseSection

section DecoderSection

open Compiler.Build

abbrev Input (N : ℕ) := Fin N → Bool

def eqBit {N : ℕ} {R : Type} [DecidableEq R] (f : Input N → R) (r : R) : Sig N :=
  fun x => decide (f x = r)

def codes {N : ℕ} {R : Type} [DecidableEq R] (f : Input N → R) : Set (Sig N) := Set.range (eqBit f)

lemma const_available {N : ℕ} {R : Type} [DecidableEq R] {A : Set (Sig N)}
    (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A) (r : R) :
    codes (N := N) (fun _ => r) ⊆ A := by
  rintro _ ⟨j,rfl⟩; change (fun _ : Input N => decide (r=j)) ∈ A; by_cases h : r = j
  · simpa [eqBit,h] using ht
  · simpa [eqBit,h] using hf

lemma bigOR {N : ℕ} {ι : Type} [Fintype ι] {A : Set (Sig N)} (f : ι → Sig N) (c : ℕ)
    (hf : ∀ i, Build A {f i} c) (h0 : (fun _ => false) ∈ A) :
    Build A {fun x => decide (∃ i, f i x = true)} (Fintype.card ι * (c+1)) := by
  classical
  let l := (Finset.univ : Finset ι).toList.map f
  have h1 := allG f c hf
  have h2 := anyG (A := A ∪ Set.range f) l (by
    intro g hg; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hg; exact Or.inr ⟨i,rfl⟩) (Or.inl h0)
  have he : (fun x => l.any (fun g => g x)) = (fun x => decide (∃ i, f i x = true)) := by
    funext x; apply Bool.eq_iff_iff.mpr; simp [l]
  rw [he] at h2
  exact relax (thenG h1 h2) le_rfl le_rfl (by simp [l, Nat.mul_add])

lemma binary_codes {N : ℕ} {S T R : Type} [Fintype S] [Fintype T] [Fintype R]
    [DecidableEq S] [DecidableEq T] [DecidableEq R] {A : Set (Sig N)}
    (h0 : (fun _ => false) ∈ A) (f : Input N → S) (g : Input N → T) (φ : S → T → R)
    (hf : codes f ⊆ A) (hg : codes g ⊆ A) :
    Build A (codes fun x => φ (f x) (g x)) (Fintype.card R * ((Fintype.card S * Fintype.card T)*2)) := by
  classical
  apply allG; intro r
  let F : S × T → Sig N := fun v => if φ v.1 v.2 = r then an (eqBit f v.1) (eqBit g v.2) else fun _ => false
  have H (v) : Build A {F v} 1 := by
    by_cases h : φ v.1 v.2 = r
    · simpa only [F,h,ite_true] using andG (hf ⟨v.1,rfl⟩) (hg ⟨v.2,rfl⟩)
    · simp only [F,h,ite_false]; exact relax (idle (Set.singleton_subset_iff.mpr h0)) le_rfl le_rfl (by omega)
  have he : (fun x => decide (∃ v, F v x = true)) = eqBit (fun x => φ (f x) (g x)) r := by
    funext x; apply Bool.eq_iff_iff.mpr; simp only [eqBit, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨a,b⟩,hv⟩; by_cases h : φ a b = r
      · have hh : f x = a ∧ g x = b := by simpa [F,h,an,eqBit] using hv
        simpa [hh.1,hh.2] using h
      · simp [F,h] at hv
    · intro h; exact ⟨⟨f x,g x⟩, by simp [F,h,an,eqBit]⟩
  simpa only [he, Fintype.card_prod] using bigOR F 1 H h0

lemma unary_codes {N : ℕ} {S R : Type} [Fintype S] [Fintype R] [DecidableEq S] [DecidableEq R]
    {A : Set (Sig N)} (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A)
    (f : Input N → S) (φ : S → R) (hf : codes f ⊆ A) :
    Build A (codes fun x => φ (f x)) (Fintype.card R * (Fintype.card S*2)) := by
  simpa using binary_codes h0 f (fun _ => ()) (fun s _ => φ s) hf (const_available h0 h1 ())

def opCost (p : ℕ) := p * ((p*p)*2)

lemma sum_codes {N : ℕ} {ι R : Type} [Fintype ι] [Fintype R] [DecidableEq R] [AddCommMonoid R]
    {A : Set (Sig N)} (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A)
    (F : ι → Input N → R) (hf : ∀ i, codes (F i) ⊆ A) :
    Build A (codes fun x => ∑ i, F i x) (Fintype.card ι * opCost (Fintype.card R)) := by
  classical
  suffices hh : ∀ s : Finset ι, Build A (codes fun x => ∑ i ∈ s, F i x) (s.card * opCost (Fintype.card R)) by
    simpa using hh Finset.univ
  intro s; induction s using Finset.induction_on with
  | empty => simpa using idle (const_available h0 h1 (0:R))
  | @insert i s hi ih =>
    have st := binary_codes (A := A ∪ codes (fun x => ∑ j ∈ s, F j x)) (Or.inl h0)
      (F i) (fun x => ∑ j ∈ s, F j x) (· + ·) ((hf i).trans Set.subset_union_left) Set.subset_union_right
    simpa only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.succ_mul, opCost] using thenG ih st

lemma sum_built_codes {N : ℕ} {ι R : Type} [Fintype ι] [Fintype R] [DecidableEq R] [AddCommMonoid R]
    {A : Set (Sig N)} (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A)
    (F : ι → Input N → R) (b : ℕ) (hf : ∀ i, Build A (codes (F i)) b) :
    Build A (codes fun x => ∑ i, F i x) (Fintype.card ι * (b + opCost (Fintype.card R))) := by
  have H := familyG (fun i => codes (F i)) b hf
  have K := sum_codes (A := A ∪ familyOut Finset.univ (fun i => codes (F i))) (Or.inl h0) (Or.inl h1) F
    (fun i _ h => Or.inr (family_mem (i := i) h))
  simpa only [Nat.mul_add] using thenG H K

lemma weighted_input_codes {N : ℕ} {ι R : Type} [Fintype ι] [Fintype R] [DecidableEq R] [AddCommMonoid R]
    {A : Set (Sig N)} (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A)
    (F : ι → Sig N) (w : ι → R) (hf : ∀ i, F i ∈ A) :
    Build A (codes fun x => ∑ i, if F i x then w i else 0) (Fintype.card ι * (Fintype.card R + opCost (Fintype.card R))) := by
  apply sum_built_codes h0 h1; intro i
  simpa only [Nat.mul_one, codes] using allG (eqBit (fun x => if F i x then w i else 0)) 1 (fun r => by
    by_cases hw : w i = r <;> by_cases hz : (0:R) = r
    · have he : eqBit (fun x => if F i x then w i else 0) r = fun _ => true := by
        funext x; cases hb : F i x <;> simp [eqBit, hw,hz,hb]
      rw [he]; exact relax (idle (Set.singleton_subset_iff.mpr h1)) le_rfl le_rfl (by omega)
    · have he : eqBit (fun x => if F i x then w i else 0) r = F i := by
        funext x; cases hb : F i x <;> simp [eqBit,hw,hz,hb]
      rw [he]; exact relax (idle (Set.singleton_subset_iff.mpr (hf i))) le_rfl le_rfl (by omega)
    · have he : eqBit (fun x => if F i x then w i else 0) r = nt (F i) := by
        funext x; cases hb : F i x <;> simp [eqBit,nt,hw,hz,hb]
      rw [he]; exact notG (hf i)
    · have he : eqBit (fun x => if F i x then w i else 0) r = fun _ => false := by
        funext x; cases hb : F i x <;> simp [eqBit,hw,hz,hb]
      rw [he]; exact relax (idle (Set.singleton_subset_iff.mpr h0)) le_rfl le_rfl (by omega))

end DecoderSection

section RegistersSection

open Compiler.Build

def registers {N : ℕ} {R : Type} [DecidableEq R] (F : ℕ → Input N → R) (t : ℕ) : Set (Sig N) :=
  {g | ∃ i < t, g ∈ codes (F i)}

lemma registers_build {N : ℕ} {R : Type} [DecidableEq R] {A : Set (Sig N)}
    (F : ℕ → Input N → R) (t b : ℕ)
    (h : ∀ i < t, Build (A ∪ registers F i) (codes (F i)) b) : Build A (registers F t) (t*b) := by
  induction t with
  | zero => rw [Nat.zero_mul]; apply idle; rintro _ ⟨i,hi,_⟩; omega
  | succ t ih =>
    have hp := ih (fun i hi => h i (by omega))
    have hw := seq hp (h t (by omega))
    apply relax hw le_rfl _ (by rw [Nat.succ_mul]); rintro f ⟨i,hi,hf⟩
    by_cases he : i=t
    · exact Or.inr (he ▸ hf)
    · exact Or.inl ⟨i,by omega,hf⟩

def unCost (p : ℕ) := p*(p*2)

def logCost (t p : ℕ) := unCost p + t*(opCost p + opCost p) + opCost p

def multCost (t p : ℕ) := t*(unCost p + opCost p) + opCost p

lemma circuit_log_rows {N : ℕ} {R : Type} [Fintype R] [DecidableEq R] [Ring R]
    {A : Set (Sig N)} (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A)
    (a : ℕ → Input N → R) (t : ℕ) (ha : registers a t ⊆ A) :
    Build A (registers (fun m x => logRec (fun j => a j x) m) t) (t * logCost t (Fintype.card R)) := by
  let p := Fintype.card R
  let L : ℕ → Input N → R := fun m x => logRec (fun j => a j x) m
  apply registers_build L; intro m hm
  let B := A ∪ registers L m
  have hB0 : (fun _ => false) ∈ B := Or.inl h0
  have hB1 : (fun _ => true) ∈ B := Or.inl h1
  have hA (j) (hj : j < t) : codes (a j) ⊆ B := fun _ hz => Or.inl (ha ⟨j,hj,hz⟩)
  let U : Input N → R := fun x => -(m:R)*a m x
  let V : Input N → R := fun x => ∑ i : Fin m, L i.val x * a (m-i.val) x
  have hu : Build B (codes U) (unCost p) := unary_codes hB0 hB1 (a m) (fun z => -(m:R)*z) (hA m hm)
  have hv : Build B (codes V) (m*(opCost p+opCost p)) := by
    simpa only [Fintype.card_fin] using sum_built_codes hB0 hB1
      (fun (i : Fin m) x => L i.val x*a (m-i.val) x) (opCost p) (fun i =>
        binary_codes hB0 (L i.val) (a (m-i.val)) (· * ·) (fun _ hy => Or.inr ⟨i.val,i.isLt,hy⟩)
          (hA (m-i.val) (by omega)))
  have hvu := bothG hu hv
  have hw := binary_codes (A := B ∪ (codes U ∪ codes V)) (Or.inl hB0) U V (· - ·)
    (fun _ hz => Or.inr (Or.inl hz)) (fun _ hz => Or.inr (Or.inr hz))
  have he : L m = fun x => U x - V x := funext fun _ => log_step ..
  rw [he]; apply relax (thenG hvu hw) le_rfl le_rfl
  change unCost p + m*(opCost p+opCost p) + opCost p ≤ _
  dsimp only [logCost]; gcongr

lemma circuit_charge_rows {N : ℕ} {R : Type} [Fintype R] [DecidableEq R] [Ring R]
    {A : Set (Sig N)} (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A) (ρ : R)
    (L : ℕ → Input N → R) (t : ℕ) (hL : registers L t ⊆ A) :
    Build A (registers (fun m x => chargeRec ρ (fun j => L j x) m) t) (t * multCost t (Fintype.card R)) := by
  let p := Fintype.card R
  let C : ℕ → Input N → R := fun m x => chargeRec ρ (fun j => L j x) m
  apply registers_build C; intro m hm
  let B := A ∪ registers C m
  have hB0 : (fun _ => false) ∈ B := Or.inl h0
  have hB1 : (fun _ => true) ∈ B := Or.inl h1
  let part : Fin m → Input N → R := fun i x => if 0 < i.val ∧ i.val ∣ m then ρ^(m-i.val)*C i.val x else 0
  have aux (i : Fin m) : Build B (codes (part i)) (unCost p) := by
    by_cases hh : 0 < i.val ∧ i.val ∣ m
    · simpa [part,hh,unCost,p] using unary_codes hB0 hB1 (C i.val) (fun z => ρ^(m-i.val)*z)
        (fun _ hy => Or.inr ⟨i.val,i.isLt,hy⟩)
    · simp only [part,hh,ite_false]; exact relax (idle (const_available hB0 hB1 0)) le_rfl le_rfl (Nat.zero_le _)
  let V : Input N → R := fun x => ∑ i : Fin m, part i x
  have hv : Build B (codes V) (m*(unCost p+opCost p)) := by
    simpa only [Fintype.card_fin] using sum_built_codes hB0 hB1 part (unCost p) aux
  have hw := binary_codes (A := B ∪ codes V) (Or.inl hB0) (L m) V (· - ·)
    (fun _ hz => Or.inl (Or.inl (hL ⟨m,hm,hz⟩))) Set.subset_union_right
  have he : C m = fun x => L m x - V x := funext fun _ => charge_step ..
  rw [he]; apply relax (thenG hv hw) le_rfl le_rfl; change m*(unCost p+opCost p)+opCost p ≤ _
  dsimp only [multCost]; gcongr

noncomputable def linearRow {N : ℕ} {ι R : Type} [Fintype ι] [AddCommMonoid R]
    (bits : ι → Sig N) (w : ℕ → ι → R) (m : ℕ) (x : Input N) := ∑ i, if bits i x then w m i else 0

def decoderCost (b t p : ℕ) := t*(b*(p+opCost p)) + t*unCost p + t*logCost t p + t*multCost t p

lemma circuit_decode {N : ℕ} {ι R : Type} [Fintype ι] [Fintype R] [DecidableEq R] [Ring R]
    {A : Set (Sig N)} (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A)
    (bits : ι → Sig N) (w : ℕ → ι → R) (ρ : R) (t : ℕ) (hb : ∀ i, bits i ∈ A) :
    Build A (registers (fun m x => decode ρ (fun j => linearRow bits w j x) m) t)
      (decoderCost (Fintype.card ι) t (Fintype.card R)) := by
  let p := Fintype.card R
  let a := linearRow bits w
  let B := A ∪ registers a t
  have hrows : Build A (registers a t) (t*(Fintype.card ι * (p+opCost p))) := by
    apply registers_build; intro m _
    exact relax (weighted_input_codes h0 h1 bits (w m) hb) Set.subset_union_left le_rfl le_rfl
  let d : ℕ → Input N → R := fun m x => dilated ρ (fun j => a j x) m
  have hd : Build B (registers d t) (t*unCost p) := by
    apply registers_build; intro m hm
    let φ := fun z : R => if m=0 then 1 else ρ^(m-1)*z
    exact unary_codes (Or.inl (Or.inl h0)) (Or.inl (Or.inl h1)) (a m) φ
      (fun _ hz => Or.inl (Or.inr ⟨m,hm,hz⟩))
  have hD := thenG hrows hd
  let l : ℕ → Input N → R := fun m x => logRec (fun i => d i x) m
  have hlog := circuit_log_rows (A := A ∪ registers d t) (Or.inl h0) (Or.inl h1) d t Set.subset_union_right
  have hL := thenG hD hlog
  have hcharge := circuit_charge_rows (A := A ∪ registers l t) (Or.inl h0) (Or.inl h1) ρ l t Set.subset_union_right
  exact thenG hL hcharge

end RegistersSection

section OutputSection

open Compiler.Build PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

lemma make_constants {N : ℕ} (i : Fin N) : Build (inputs N) ({fun _ => false, fun _ => true} : Set (Sig N)) 3 := by
  let f : Sig N := fun x => x i
  have hf : f ∈ inputs N := ⟨i,rfl⟩
  have h1 := notG hf
  have h2 := andG (A := inputs N ∪ {nt f}) (Or.inl hf) (Or.inr rfl)
  have hf₀ : an f (nt f) = fun _ => false := by funext x; cases hb : f x <;> simp [an,nt,hb]
  rw [hf₀] at h2
  have h3 := notG (A := inputs N ∪ {(fun _ => false)}) (f := fun _ => false) (Or.inr rfl)
  change Build _ {(fun _ => true)} 1 at h3
  exact relax (seq (thenG h1 h2) h3) le_rfl (by intro z hz; rcases hz with hh | hh; exact Or.inl (Set.mem_singleton_iff.mpr hh); exact Or.inr hh) le_rfl

theorem literal_decode {N : ℕ} {ι R : Type} [Fintype ι] [Fintype R] [DecidableEq R] [Ring R]
    (i0 : Fin N) (src : ι → Fin N) (w : ℕ → ι → R) (ρ : R) (t : ℕ) :
    ∃ (g : Circuit) (out : Fin t → R → Fin (N+g.size)),
      ReadsBack N g ∧ g.size ≤ 3+decoderCost (Fintype.card ι) t (Fintype.card R) ∧
      (∀ a ∈ g.gates, ((a.op = .and ∨ a.op = .or) ∧ a.inputs.length = 2) ∨ (a.op = .not ∧ a.inputs.length = 1)) ∧
      ∀ (x : Input N) (m : Fin t) (z : R), (g.wires (List.ofFn x)).getD (out m z).val false =
        decide (decode ρ (fun j => ∑ i, if x (src i) then w j i else 0) m.val = z) := by
  classical
  let B := inputs N ∪ ({fun _ => false, fun _ => true} : Set (Sig N))
  let bits : ι → Sig N := fun i x => x (src i)
  have H := circuit_decode (A := B) (Or.inr (by simp)) (Or.inr (by simp)) bits w ρ t
    (fun i => Or.inl ⟨src i,rfl⟩)
  have K := thenG (make_constants i0) H
  have hstart : Compiler.GateBridge.Scheduled N id 0 (inputs N) :=
    Compiler.GateBridge.start (F := id) (fun (i : Fin N) (x : Input N) => x i) (fun _ _ => rfl)
  obtain ⟨c,hc,gs,hgs,hr,hg,hw⟩ := K.run hstart le_rfl
  let g : Circuit := ⟨gs,0⟩
  have hsize : g.size = c := by simpa [g,Circuit.size] using hgs
  have output (m : Fin t) (z : R) : ∃ u : Fin (N+g.size), ∀ x : Input N,
      (g.wires (List.ofFn x)).getD u.val false =
        decide (decode ρ (fun j => ∑ i, if x (src i) then w j i else 0) m.val = z) := by
    obtain ⟨u,hu,he⟩ := hw _ (Or.inr ⟨m.val,m.isLt,⟨z,rfl⟩⟩)
    exact ⟨⟨u,by simpa [hsize] using hu⟩,he⟩
  choose out he using output
  exact ⟨g,out,hr,hsize ▸ hc,hg,fun x m z => he m z x⟩

abbrev Width (n : ℕ) := Fin (2*n+1)
abbrev BitIx (n : ℕ) := Ix n × Ix n × Width n
abbrev Histogram (n : ℕ) := Ix n → Ix n → Width n → Bool

def tableOf {n : ℕ} (H : Histogram n) (r b : Ix n) := ∑ k : Width n, (H r b k).toNat * 2^k.val

noncomputable def matrixEntry {n : ℕ} (k m : ℕ) (u : BitIx n) : ℤ :=
  2^u.2.2.val * (termI k u.1 u.2.1).coeff m

lemma row_binary {n : ℕ} (k m : ℕ) (H : Histogram n) :
    inputRow k (tableOf H) m = ∑ u : BitIx n, if H u.1 u.2.1 u.2.2 then matrixEntry k m u else 0 := by
  unfold inputRow tableOf matrixEntry
  rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro r _
  rw [Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro b _
  push_cast; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _
  cases hh : H r b j <;> simp [hh]

def countLen (n : ℕ) := 2+n*n+(n+1)*(n+1)*(2*n+1)

def blockIx {l w : ℕ} (e : Fin l) (j : Fin w) : Fin (l*w) :=
  ⟨e.val*w+j.val, by
    calc e.val*w+j.val < e.val*w+w := Nat.add_lt_add_left j.isLt _
      _ = (e.val+1)*w := by ring
      _ ≤ l*w := Nat.mul_le_mul_right _ e.isLt⟩

def blockRead {l w : ℕ} (h : 0 < w) (F : Fin l → Fin w → Bool) : Fin (l*w) → Bool := fun u =>
  F ⟨u.val / w, Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using u.isLt)⟩ ⟨u.val % w,Nat.mod_lt _ h⟩

lemma blockRead_ix {l w : ℕ} (hw : 0 < w) (F : Fin l → Fin w → Bool) (e : Fin l) (j : Fin w) :
    blockRead hw F (blockIx e j) = F e j := by
  have hq : (e.val*w+j.val)/w=e.val := Nat.div_eq_of_lt_le (by omega) (by rw [Nat.add_mul,one_mul]; omega)
  have hm : (e.val*w+j.val) % w=j.val := by simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  unfold blockRead blockIx; congr 1 <;> apply Fin.ext
  · exact hq
  · exact hm

lemma blockRead_list {l w : ℕ} (hw : 0 < w) (F : Fin l → Fin w → Bool) :
    List.ofFn (blockRead hw F) = (List.ofFn (fun e => List.ofFn (F e))).flatten := by
  rw [List.ofFn_mul]; congr 1; congr 1; funext e; congr 1; funext j
  exact blockRead_ix hw F e j

def countSrc {n : ℕ} (u : BitIx n) : Fin (countLen n) :=
  (Fin.natAdd (2+n*n) (blockIx u.1 (blockIx u.2.1 u.2.2))).cast (by unfold countLen; ring)

def countWord {n : ℕ} (σ : Equiv.Perm (Fin n)) (H : Histogram n) : List Bool :=
  [false,true] ++ (List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin n => decide (σ i = j)))).flatten ++
    (List.ofFn (fun r : Ix n => (List.ofFn (fun b : Ix n => List.ofFn (H r b))).flatten)).flatten

lemma countWord_input {n : ℕ} (hn : 0<n) (σ : Equiv.Perm (Fin n)) (H : Histogram n) :
    ∃ x : Input (countLen n), List.ofFn x = countWord σ H ∧ ∀ u : BitIx n, x (countSrc u) = H u.1 u.2.1 u.2.2 := by
  let P := blockRead hn (fun i j => decide (σ i = j))
  let V := fun r : Ix n => blockRead (by omega : 0<2*n+1) (H r)
  let T := blockRead (by positivity : 0<(n+1)*(2*n+1)) V
  let c : Fin 2 → Bool := fun i => decide (i.val=1)
  let pre := Fin.append c P
  let X := Fin.append pre T
  have hlen : 2+n*n+(n+1)*((n+1)*(2*n+1))=countLen n := by unfold countLen; ring
  refine ⟨fun i => X (i.cast hlen.symm), ?_,?_⟩
  · have eq : List.ofFn (fun i : Fin (countLen n) => X (i.cast hlen.symm)) = List.ofFn X := by
      exact List.ofFn_congr hlen.symm _
    rw [eq]; simp only [X,pre,List.ofFn_fin_append,T,V,P,blockRead_list,countWord]
    rfl
  · intro u; change Fin.append pre T (Fin.natAdd (2+n*n) (blockIx u.1 (blockIx u.2.1 u.2.2))) = _
    rw [Fin.append_right]; dsimp only [T,V]; rw [blockRead_ix, blockRead_ix]

theorem modular_arc_wires (n f M t : ℕ) (hn : 0<n) :
    ∃ (g : Circuit) (out : Fin t → ZMod (M+1) → Fin (countLen n+g.size)),
      ReadsBack (countLen n) g ∧ g.size ≤ 3+decoderCost ((n+1)*((n+1)*(2*n+1))) t (M+1) ∧
      (∀ a ∈ g.gates, ((a.op = .and ∨ a.op = .or) ∧ a.inputs.length = 2) ∨ (a.op = .not ∧ a.inputs.length = 1)) ∧
      ∀ (σ : Equiv.Perm (Fin n)) (H : Histogram n) (m : Fin t) (z : ZMod (M+1)),
      (g.wires (countWord σ H)).getD (out m z).val false =
        decide (((decode ((2:ℤ)^f) (inputRow (stride n) (tableOf H)) m.val : ℤ) : ZMod (M+1)) = z) := by
  let φ := Int.castRingHom (ZMod (M+1))
  let wt := fun j (u : BitIx n) => φ (matrixEntry (stride n) j u)
  obtain ⟨g,out,hr,hb,hl,he⟩ := literal_decode (R := ZMod (M+1)) (N := countLen n)
    ⟨0,by unfold countLen; omega⟩ countSrc wt (φ ((2:ℤ)^f)) t
  refine ⟨g,out,hr,?_,hl,?_⟩
  · simpa only [BitIx,Ix,Width,Fintype.card_prod,Fintype.card_fin,ZMod.card] using hb
  · intro σ H m z; obtain ⟨x,hx,hs⟩ := countWord_input hn σ H
    rw [← hx, he]
    have heq : (fun j => ∑ u : BitIx n, if x (countSrc u) then wt j u else 0) = φ ∘ inputRow (stride n) (tableOf H) := by
      funext j; rw [Function.comp_apply,row_binary, map_sum]; apply Finset.sum_congr rfl; intro u _
      rw [hs]; cases H u.1 u.2.1 u.2.2 <;> simp [wt]
    rw [heq, ← decode_map]; rfl

end OutputSection

section BoundsSection

lemma sum_abs_bound {ι : Type} [Fintype ι] (f : ι → ℤ) (b : ℤ) (h : ∀ i, |f i| ≤ b) :
    |∑ i, f i| ≤ (Fintype.card ι : ℤ)*b := by
  calc |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _ : ι, b := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

noncomputable def bump (j : ℕ) (s : Bool) : Polynomial ℤ :=
  if s then 1+Polynomial.X^j else 1-Polynomial.X^j

lemma bump_bound (P : Polynomial ℤ) (B : ℤ) (hP : ∀ m, |P.coeff m| ≤ B) (j : ℕ) (s : Bool) (m : ℕ) :
    |(P*bump j s).coeff m| ≤ 2*B := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hP 0)
  cases s
  · simp only [bump, Bool.false_eq_true, ite_false, mul_sub, mul_one, Polynomial.coeff_sub, Polynomial.coeff_mul_X_pow']
    split_ifs with hh
    · exact (abs_sub ..).trans (by linarith [hP m, hP (m-j)])
    · simp; linarith [hP m]
  · simp only [bump, ite_true, mul_add, mul_one, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow']
    split_ifs with hh
    · exact (abs_add_le ..).trans (by linarith [hP m, hP (m-j)])
    · simp; linarith [hP m]

lemma bump_pow_bound (P : Polynomial ℤ) (B : ℤ) (hP : ∀ m, |P.coeff m| ≤ B) (j : ℕ) (s : Bool) (l : ℕ) :
    ∀ m, |(P*(bump j s)^l).coeff m| ≤ 2^l*B := by
  induction l with
  | zero => simpa using hP
  | succ l ih =>
    intro m; rw [pow_succ,← mul_assoc]
    exact (bump_bound _ _ ih j s m).trans (by rw [pow_succ]; ring_nf; exact le_rfl)

lemma term_bound {n : ℕ} (k : ℕ) (r b : Ix n) (m : ℕ) : |(termI k r b).coeff m| ≤ (2:ℤ)^(2*n) := by
  have h1 : ∀ m : ℕ, |(1 : Polynomial ℤ).coeff m| ≤ 1 := by intro m; by_cases h : m=0 <;> simp [Polynomial.coeff_one, h]
  have h2 := bump_pow_bound _ _ h1 1 false r.val
  have h3 := bump_pow_bound _ _ h2 1 true (n-r.val)
  have h4 := bump_pow_bound _ _ h3 k false b.val
  have h5 := bump_pow_bound _ _ h4 k true (n-b.val) m
  have hr := r.isLt; have hb := b.isLt
  simpa only [termI,bump,Bool.false_eq_true,ite_true,ite_false,pow_one,one_mul,mul_one,← pow_add,
    show n-b.val+(b.val+(n-r.val+r.val))=2*n by omega] using h5

def rowBudget (n : ℕ) := 8*n+6

lemma row_bound {n : ℕ} (k : ℕ) (T : Counts n) (hT : ∀ r b, T r b ≤ (2*n+1)*2^(2*n+1)) (m : ℕ) :
    |inputRow k T m| ≤ (2:ℤ)^rowBudget n := by
  let A := (2:ℤ)^(2*n+1)*(2:ℤ)^(2*n)
  have hb (r b : Ix n) : |(T r b : ℤ)*(termI k r b).coeff m| ≤ (2*n+1 : ℤ)*A := by
    rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
    have ht : (T r b : ℤ) ≤ (2*n+1 : ℤ)*2^(2*n+1) := by exact_mod_cast hT r b
    exact (mul_le_mul ht (term_bound k r b m) (abs_nonneg _) (by positivity)).trans (by dsimp [A]; ring_nf; exact le_rfl)
  have h : |inputRow k T m| ≤ (n+1 : ℤ)*((n+1 : ℤ)*((2*n+1 : ℤ)*A)) := by
    unfold inputRow
    simpa [Ix] using sum_abs_bound (fun r : Ix n => ∑ b : Ix n, (T r b : ℤ)*(termI k r b).coeff m)
      ((n+1 : ℤ)*((2*n+1 : ℤ)*A)) (fun r => by simpa [Ix] using sum_abs_bound _ _ (hb r))
  have hj : (n+1 : ℤ) ≤ (2:ℤ)^(n+1) := by exact_mod_cast (Nat.lt_two_pow_self (n := n+1)).le
  have hw : (2*n+1 : ℤ) ≤ (2:ℤ)^(2*n+1) := by exact_mod_cast (Nat.lt_two_pow_self (n := 2*n+1)).le
  apply h.trans
  calc (n+1 : ℤ)*((n+1 : ℤ)*((2*n+1 : ℤ)*A)) ≤ 2^(n+1)*(2^(n+1)*(2^(2*n+1)*A)) := by dsimp [A]; gcongr
    _ ≤ _ := by dsimp [A]; simp only [← pow_add]; apply pow_le_pow_right₀ (by decide); unfold rowBudget; omega

lemma table_bound {n : ℕ} (H : Histogram n) (r b : Ix n) : tableOf H r b ≤ (2*n+1)*2^(2*n+1) := by
  unfold tableOf
  calc ∑ k : Width n, (H r b k).toNat * 2^k.val ≤ ∑ _ : Width n, 2^(2*n+1) := by
         apply Finset.sum_le_sum; intro k _; cases H r b k <;> simp
         exact Nat.pow_le_pow_right (by decide) k.isLt.le
    _ = _ := by simp [Width]

lemma physical_bound {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pins n) (r b : Ix n) :
    physical σ p r b ≤ (2*n+1)*2^(2*n+1) := by
  have h : physical σ p r b ≤ 2^(2*n) := by
    simpa [physical, Fintype.card_fun, Fintype.card_prod] using
      (Finset.card_filter_le (Finset.univ : Finset (Bool × Fin n → Bool)) (fun x =>
        (∀ v, p v = none ∨ p v = some (x v)) ∧
        (Finset.univ.filter (fun i => x (false,i) ≠ x (true,i))).card = r.val ∧
        (Finset.univ.filter (fun i => x (false,i) ≠ x (true,σ i))).card = b.val))
  exact h.trans (by rw [pow_succ]; nlinarith [Nat.zero_le (2^(2*n))])

lemma free_bound {n : ℕ} (p : Pins n) : free p ≤ 2*n := by
  simpa [free,Fintype.card_prod] using Finset.card_filter_le (Finset.univ : Finset (Bool × Fin n)) (fun v => p v = none)

lemma amount_bound (L : List (ℕ × ℕ × Bool)) (k m : ℕ) : |charge k L m| ≤ (m : ℤ)*L.length := by
  have hcard : (numPairs L).card ≤ L.length ∧ (denPairs L).card ≤ L.length := by
    induction L with
    | nil => simp [numPairs,denPairs]
    | cons a L ih => rcases a with ⟨r,b,s⟩; rcases ih with ⟨h1,h2⟩; cases s <;> simp [numPairs,denPairs] <;> omega
  have hn := (Multiset.count_le_card m (numer k L)).trans (by simpa [numer] using hcard.1)
  have hd := (Multiset.count_le_card m (denom k L)).trans (by simpa [denom] using hcard.2)
  rw [charge,abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (Int.natCast_nonneg _); apply abs_le.mpr; omega

end BoundsSection

section CrtSection

lemma logRec_ext {a b : ℕ → ℤ} (m : ℕ) (h : ∀ i ≤ m, a i = b i) : logRec a m = logRec b m := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    rw [log_step a m,log_step b m,h m le_rfl]; congr 1; apply Finset.sum_congr rfl; intro i _
    rw [ih i.val i.isLt (fun j hj => h j (by omega)), h (m-i.val) (by omega)]

lemma chargeRec_ext {a b : ℕ → ℤ} (ρ : ℤ) (m : ℕ) (h : ∀ i ≤ m, a i = b i) :
    chargeRec ρ a m = chargeRec ρ b m := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    rw [charge_step ρ a m,charge_step ρ b m,h m le_rfl]; congr 1; apply Finset.sum_congr rfl; intro i _
    rw [ih i.val i.isLt (fun j hj => h j (by omega))]

lemma logRec_leading {a b : ℕ → ℤ} (m : ℕ) (h : ∀ i < m, a i = b i) :
    logRec a m-logRec b m = -(m:ℤ)*(a m-b m) := by
  have hs : (∑ i : Fin m, logRec a i.val * a (m-i.val)) = ∑ i : Fin m, logRec b i.val * b (m-i.val) := by
    apply Finset.sum_congr rfl; intro i _
    rw [logRec_ext i.val (fun j hj => h j (by have := i.isLt; omega))]
    by_cases hz : i.val = 0
    · simp [hz,log_step b 0]
    · rw [h (m-i.val) (by have := i.isLt; omega)]
  rw [log_step a m,log_step b m,hs]; ring

lemma decode_leading (a b : ℕ → ℤ) (ρ : ℤ) (m : ℕ) (hm : 0 < m) (h : ∀ j < m, a j = b j) :
    decode ρ a m - decode ρ b m = -(m:ℤ) * ρ^(m-1) * (a m-b m) := by
  let A := dilated ρ a
  let B := dilated ρ b
  have hd (j : ℕ) (hj : j < m) : A j = B j := by simp [A,B,dilated,h j hj]
  have he (j : ℕ) (hj : j < m) : logRec A j = logRec B j := logRec_ext j (fun l hl => hd l (by omega))
  have hs : (∑ i : Fin m, if 0 < i.val ∧ i.val ∣ m then ρ^(m-i.val)*chargeRec ρ (logRec A) i.val else 0) =
      ∑ i : Fin m, if 0 < i.val ∧ i.val ∣ m then ρ^(m-i.val)*chargeRec ρ (logRec B) i.val else 0 := by
    apply Finset.sum_congr rfl; intro i _; rw [chargeRec_ext ρ i.val (fun j hj => he j (by have := i.isLt; omega))]
  change chargeRec ρ (logRec A) m - chargeRec ρ (logRec B) m = _
  rw [charge_step ρ (logRec A) m, charge_step ρ (logRec B) m, hs, sub_sub_sub_cancel_right,
    logRec_leading m hd]
  simp [A,B,dilated,hm.ne']; ring

def modBudget (n : ℕ) := rowBudget n + (2*n+2)*(radius n+1) + radius n + 10

lemma residues_separate (a b : ℤ) (B : ℕ) (hB : 7 ≤ B) (hab : |a-b| < (2:ℤ)^B)
    (h : ∀ i : Fin B, (a : ZMod (i.val+1)) = (b : ZMod (i.val+1))) : a=b := by
  have hd : Nat.lcmUpto B ∣ (a-b).natAbs := by
    apply Finset.lcm_dvd; intro j hj; have hj' := Finset.mem_Icc.mp hj
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j≠0 by omega)
    have he := h ⟨i,by omega⟩
    have hh : ((a-b : ℤ) : ZMod (i+1)) = 0 := by simpa only [Int.cast_sub, sub_eq_zero] using he
    exact Int.natCast_dvd.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp hh)
  by_contra hn
  have hpos : 0 < (a-b).natAbs := Int.natAbs_pos.mpr (sub_ne_zero.mpr hn)
  have hu := (Chebyshev.two_pow_le_lcmUpto hB).trans (Nat.le_of_dvd hpos hd)
  have h₁ : ((a-b).natAbs : ℤ) < 2^B := by simpa using hab
  exact Nat.not_lt_of_ge hu (by exact_mod_cast h₁)

lemma budget_margin (n q m : ℕ) (hq : q ≤ 2*n) (hm : m ≤ radius n) :
    m + q*(m-1) + (rowBudget n+1) < modBudget n := by
  unfold modBudget
  have hprod := Nat.mul_le_mul hq (by omega : m-1 ≤ radius n)
  nlinarith

lemma residue_rows_equal {n q : ℕ} (a b : ℕ → ℤ) (hq : q ≤ 2*n)
    (ha : ∀ m, |a m| ≤ (2:ℤ)^rowBudget n) (hb : ∀ m, |b m| ≤ (2:ℤ)^rowBudget n)
    (h0 : ∀ u : Fin (modBudget n), (a 0 : ZMod (u.val+1)) = (b 0 : ZMod (u.val+1)))
    (h : ∀ m ≤ radius n, ∀ u : Fin (modBudget n),
      ((decode ((2:ℤ)^q) a m : ℤ) : ZMod (u.val+1)) = ((decode ((2:ℤ)^q) b m : ℤ) : ZMod (u.val+1))) :
    ∀ m ≤ radius n, a m = b m := by
  have hB : 7 ≤ modBudget n := by unfold modBudget; omega
  have hd (i : ℕ) : |a i-b i| ≤ (2:ℤ)^(rowBudget n+1) := (abs_sub ..).trans (by rw [pow_succ]; linarith [ha i, hb i])
  intro m; induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro hm
    rcases Nat.eq_zero_or_pos m with rfl | hp
    · exact residues_separate _ _ _ hB ((hd 0).trans_lt (pow_lt_pow_right₀ (by decide) (by unfold modBudget; omega))) h0
    · let ρ := (2:ℤ)^q
      have he := decode_leading a b ρ m hp (fun j hj => ih j hj (by omega))
      have hab : |decode ρ a m - decode ρ b m| < (2:ℤ)^modBudget n := by
        rw [he, abs_mul, abs_mul, abs_neg, abs_of_nonneg (Int.natCast_nonneg _), abs_of_nonneg (by dsimp [ρ]; positivity : 0 ≤ ρ^(m-1))]
        calc (m:ℤ)*ρ^(m-1)*|a m-b m| ≤ 2^m*((2:ℤ)^q)^(m-1)*2^(rowBudget n+1) := by
               dsimp [ρ]; gcongr; exact_mod_cast (Nat.lt_two_pow_self (n := m)).le; exact hd m
          _ < _ := by rw [← pow_mul, ← pow_add, ← pow_add]; apply pow_lt_pow_right₀ (by decide) (budget_margin n q m hq hm)
      have heq := residues_separate _ _ _ hB hab (h m hm)
      rw [heq,sub_self] at he
      have hnon : -(m:ℤ)*ρ^(m-1) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast hp.ne')) (by dsimp [ρ]; positivity)
      exact sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_left hnon)

noncomputable def fits {n : ℕ} (H : Histogram n) (q : ℕ) (L : List (ℕ × ℕ × Bool)) : Prop :=
  (∀ a : Fin (modBudget n), (inputRow (stride n) (tableOf H) 0 : ZMod (a.val+1)) = 2^q) ∧
  ∀ m ≤ radius n, ∀ a : Fin (modBudget n),
    ((decode ((2:ℤ)^q) (inputRow (stride n) (tableOf H)) m : ℤ) : ZMod (a.val+1)) =
      ((2:ZMod (a.val+1))^q)^m * (charge (stride n) L m : ZMod (a.val+1))

lemma arbitrary_table_residue_test {n : ℕ} (H : Histogram n) (σ : Equiv.Perm (Fin n)) (p : Pins n) :
    physical σ p = tableOf H ↔ fits H (free p) (arcList σ p) := by
  constructor
  · intro he; obtain ⟨h0,hC⟩ := (arbitrary_table_integral_test _ σ p).mp he
    exact ⟨fun u => by rw [h0]; push_cast; rfl, fun m hm u => by rw [hC m hm]; push_cast; rfl⟩
  · intro ht; obtain ⟨hp0,hpC⟩ := (arbitrary_table_integral_test (physical σ p) σ p).mp rfl
    let k := stride n; let T := tableOf H; let P := physical σ p
    have hrow := residue_rows_equal (inputRow k T) (inputRow k P) (free_bound p)
      (row_bound k T (table_bound H)) (row_bound k P (physical_bound σ p))
      (fun a => by change _ = (inputRow (stride n) (physical σ p) 0 : ZMod (a.val+1)); rw [hp0]; simpa using ht.1 a)
      (fun m hm a => by
        change _ = ((decode ((2:ℤ)^free p) (inputRow (stride n) (physical σ p)) m : ℤ) : ZMod (a.val+1))
        rw [hpC m hm]; simpa using ht.2 m hm a)
    apply normalize_injective 0; apply spectrum_injective (k := k) (by dsimp [k,stride]; omega)
    ext m; by_cases h : m ≤ radius n
    · have he := congrArg (fun z : ℤ => (z:ℚ)) (hrow m h).symm
      simpa only [inputRow_eq k 0, pow_zero,one_mul,T,P] using he
    · have hd (Y : Tab n) : (spectrum k Y).natDegree < m := (spectrum_degree k Y).trans_lt (by dsimp [k,radius] at *; nlinarith)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hd _), Polynomial.coeff_eq_zero_of_natDegree_lt (hd _)]

end CrtSection

section SimulSection

open Compiler.Build PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

def Bcap (n : ℕ) := 2*n*radius n
abbrev Zslot (n : ℕ) := Fin (2*Bcap n+1)
abbrev Order (n : ℕ) := Fin (radius n+1)
abbrev ChargeIx (n : ℕ) := Width n × Order n × Zslot n

def signed {n : ℕ} (z : Zslot n) : ℤ := (z.val : ℤ)-Bcap n

def readHist {n : ℕ} (x : Input (countLen n)) : Histogram n := fun r b j => x (countSrc (r,b,j))

noncomputable def massMod {n : ℕ} (q : Width n) (u : Fin (modBudget n)) : Sig (countLen n) := fun x =>
  decide ((inputRow (stride n) (tableOf (readHist x)) 0 : ZMod (u.val+1)) = 2^q.val)

noncomputable def itemMod {n : ℕ} (v : ChargeIx n) (u : Fin (modBudget n)) : Sig (countLen n) := fun x =>
  decide (((decode ((2:ℤ)^v.1.val) (inputRow (stride n) (tableOf (readHist x))) v.2.1.val : ℤ) : ZMod (u.val+1)) =
    ((2 : ZMod (u.val+1))^v.1.val)^v.2.1.val * (signed v.2.2 : ZMod (u.val+1)))

noncomputable def massOK {n : ℕ} (q : Width n) : Sig (countLen n) := fun x => decide (∀ u, massMod q u x = true)
noncomputable def itemOK {n : ℕ} (v : ChargeIx n) : Sig (countLen n) := fun x => decide (∀ u, itemMod v u x = true)

def bitCard (n : ℕ) := (n+1)*((n+1)*(2*n+1))
def unitCost (n : ℕ) := let p := modBudget n
  bitCard n * (p+opCost p) + decoderCost (bitCard n) (radius n+1) p

def checkCost (n : ℕ) := modBudget n*(unitCost n+1)
def preCost (n : ℕ) := (2*n+1)*checkCost n + ((2*n+1)*((radius n+1)*(2*Bcap n+1)))*checkCost n

lemma bigAND {N : ℕ} {ι : Type} [Fintype ι] {A : Set (Sig N)} (f : ι → Sig N) (c : ℕ)
    (hf : ∀ i, Build A {f i} c) (h1 : (fun _ => true) ∈ A)
    (dec : ∀ x : Input N, Decidable (∀ i, f i x = true)) :
    Build A {fun x => @decide (∀ i, f i x = true) (dec x)} (Fintype.card ι * (c+1)) := by
  classical
  let l := (Finset.univ : Finset ι).toList.map f
  have hB := allG f c hf
  have hC := everyG (A := A ∪ Set.range f) l (by
    intro g hg; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hg; exact Or.inr ⟨i,rfl⟩) (Or.inl h1)
  have he : (fun x => l.all (fun g => g x)) = (fun x => @decide (∀ i, f i x = true) (dec x)) := by
    funext x; apply Bool.eq_iff_iff.mpr; simp [l]
  rw [he] at hC
  exact relax (thenG hB hC) le_rfl le_rfl (by simp [l,Nat.mul_add])

lemma row_function {n : ℕ} (u : ℕ) (j : ℕ) :
    (fun x : Input (countLen n) => ∑ i : BitIx n,
      if x (countSrc i) then (matrixEntry (stride n) j i : ZMod (u+1)) else 0) =
      fun x => ((inputRow (stride n) (tableOf (readHist x)) j : ℤ) : ZMod (u+1)) := by
  funext x; rw [row_binary,Int.cast_sum]; apply Finset.sum_congr rfl; intro v _
  change (if x (countSrc v) then _ else _) = ((if x (countSrc v) then _ else _ : ℤ) : ZMod (u+1))
  cases x (countSrc v) <;> simp

lemma mass_mod_gate {n : ℕ} (q : Width n) (u : Fin (modBudget n)) :
    Build (base (countLen n)) {massMod q u} (unitCost n) := by
  let A := base (countLen n)
  let bits := fun (i : BitIx n) (x : Input (countLen n)) => x (countSrc i)
  let w := fun i : BitIx n => (matrixEntry (stride n) 0 i : ZMod (u.val+1))
  have h := weighted_input_codes (A := A) (Or.inr (by simp)) (Or.inr (by simp)) bits w (fun i => Or.inl ⟨countSrc i,rfl⟩)
  apply relax h le_rfl (Set.singleton_subset_iff.mpr ⟨2^q.val,?_⟩)
  · simp only [BitIx,Ix,Width,Fintype.card_prod,Fintype.card_fin,ZMod.card]; unfold unitCost bitCard
    apply le_trans _ (Nat.le_add_right ..); unfold opCost; gcongr <;> omega
  · funext x; apply Bool.eq_iff_iff.mpr
    change decide (_ = _) = true ↔ decide (_=_) = true
    simp only [decide_eq_true_eq]; exact (congrFun (row_function (n:=n) u.val 0) x).congr_left

lemma item_mod_gate {n : ℕ} (v : ChargeIx n) (u : Fin (modBudget n)) :
    Build (base (countLen n)) {itemMod v u} (unitCost n) := by
  let A := base (countLen n)
  let φ := Int.castRingHom (ZMod (u.val+1))
  let w := fun j (i : BitIx n) => φ (matrixEntry (stride n) j i)
  let bits := fun (i : BitIx n) (x : Input (countLen n)) => x (countSrc i)
  have h := circuit_decode (A := A) (Or.inr (by simp)) (Or.inr (by simp)) bits w
    (φ ((2:ℤ)^v.1.val)) (radius n+1) (fun i => Or.inl ⟨countSrc i,rfl⟩)
  apply relax h le_rfl (Set.singleton_subset_iff.mpr ⟨v.2.1.val,v.2.1.isLt,⟨((2:ZMod (u.val+1))^v.1.val)^v.2.1.val * (signed v.2.2 : ZMod (u.val+1)),?_⟩⟩)
  · simp only [BitIx,Ix,Width,Fintype.card_prod,Fintype.card_fin,ZMod.card]
    apply le_trans _ (Nat.le_add_left ..); unfold decoderCost logCost multCost unCost opCost bitCard; gcongr <;> omega
  · funext x
    have hl : (fun j => linearRow bits w j x) = φ ∘ inputRow (stride n) (tableOf (readHist x)) := by
      funext j; exact congrFun (row_function (n:=n) u.val j) x
    change decide (decode (φ ((2:ℤ)^v.1.val)) (fun j => linearRow bits w j x) _ = _) = _
    rw [hl,← decode_map]; rfl

lemma query_bank (n : ℕ) :
    Build (base (countLen n)) (Set.range (@massOK n) ∪ Set.range (@itemOK n)) (preCost n) := by
  have ht : (fun _ => true) ∈ base (countLen n) := Or.inr (by simp)
  have hm (q : Width n) : Build (base (countLen n)) {massOK q} (checkCost n) := by
    change Build _ {fun x => decide (∀ i, massMod q i x = true)} _
    simpa only [checkCost,Fintype.card_fin] using bigAND (massMod q) (unitCost n) (mass_mod_gate q) ht (fun _ => inferInstance)
  have hc (v : ChargeIx n) : Build (base (countLen n)) {itemOK v} (checkCost n) := by
    change Build _ {fun x => decide (∀ i, itemMod v i x = true)} _
    simpa only [checkCost,Fintype.card_fin] using bigAND (itemMod v) (unitCost n) (item_mod_gate v) ht (fun _ => inferInstance)
  simpa only [ChargeIx,Width,Order,Zslot,Fintype.card_prod,Fintype.card_fin,preCost] using
    bothG (allG massOK _ hm) (allG itemOK _ hc)

def qIndex {n : ℕ} (p : Pins n) : Width n := ⟨free p,Nat.lt_succ_of_le (free_bound p)⟩

lemma arc_mag {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pins n) (m : Order n) :
    |charge (stride n) (arcList σ p) m.val| ≤ (Bcap n : ℤ) := by
  obtain ⟨_,rfl,hL,_,_⟩ := exists_arc_factors σ p
  have hh := amount_bound (arcList σ p) (stride n) m.val
  apply hh.trans; unfold Bcap; push_cast; rw [mul_comm (2*(n:ℤ))]; gcongr
  · exact_mod_cast Nat.le_of_lt_succ m.isLt
  · exact_mod_cast hL

noncomputable def arcSlot {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pins n) (m : Order n) : Zslot n :=
  ⟨(charge (stride n) (arcList σ p) m.val+Bcap n).toNat, by
    have hh := abs_le.mp (arc_mag σ p m); omega⟩

lemma signed_arcSlot {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pins n) (m : Order n) :
    signed (arcSlot σ p m) = charge (stride n) (arcList σ p) m.val := by
  change (((charge (stride n) (arcList σ p) m.val+Bcap n).toNat : ℤ)-Bcap n) = _
  have hh := abs_le.mp (arc_mag σ p m); omega

noncomputable def fitsSignals {n : ℕ} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (x : Input (countLen n)) (σ : Equiv.Perm (Fin n)) (p : Pins n) : Prop :=
  a (qIndex p) x = true ∧ ∀ m : Order n, b (qIndex p,m,arcSlot σ p m) x = true

lemma massOK_iff {n : ℕ} (q : Width n) (x : Input (countLen n)) :
    massOK q x = true ↔ ∀ u : Fin (modBudget n), (inputRow (stride n) (tableOf (readHist x)) 0 : ZMod (u.val+1)) = 2^q.val := by
  constructor
  · intro h u; exact of_decide_eq_true ((of_decide_eq_true h : ∀ u, massMod q u x = true) u)
  · intro h; exact decide_eq_true (show ∀ u, massMod q u x = true from fun u => decide_eq_true (h u))

lemma itemOK_iff {n : ℕ} (v : ChargeIx n) (x : Input (countLen n)) :
    itemOK v x = true ↔ ∀ u : Fin (modBudget n),
      ((decode ((2:ℤ)^v.1.val) (inputRow (stride n) (tableOf (readHist x))) v.2.1.val : ℤ) : ZMod (u.val+1)) =
        ((2:ZMod (u.val+1))^v.1.val)^v.2.1.val*(signed v.2.2 : ZMod (u.val+1)) := by
  constructor
  · intro h u; exact of_decide_eq_true ((of_decide_eq_true h : ∀ u, itemMod v u x = true) u)
  · intro h; exact decide_eq_true (show ∀ u, itemMod v u x = true from fun u => decide_eq_true (h u))

lemma query_bank_spec {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Input (countLen n)) (p : Pins n) :
    fitsSignals massOK itemOK x σ p ↔ physical σ p = tableOf (readHist x) := by
  rw [arbitrary_table_residue_test]; unfold fitsSignals fits
  rw [massOK_iff]; simp_rw [itemOK_iff]; simp only [qIndex, signed_arcSlot]
  constructor
  · rintro ⟨ha,hb⟩; exact ⟨ha,fun m hm => hb ⟨m,Nat.lt_succ_of_le hm⟩⟩
  · rintro ⟨ha,hb⟩; exact ⟨ha,fun m => hb m.val (Nat.le_of_lt_succ m.isLt)⟩

end SimulSection

section TraceSection

open Compiler.Build

structure TraceCell (N : ℕ) (ι : Type*) where
  ok : Sig N
  bits : ι → Sig N

namespace TraceCell

variable {N : ℕ} {ι κ : Type*}

def outputs (p : TraceCell N ι) : Set (Sig N) := {p.ok} ∪ Set.range p.bits

def blank : TraceCell N ι := ⟨fun _ => false, fun _ _ => false⟩

def prior (a b : TraceCell N ι) : TraceCell N ι :=
  ⟨or a.ok b.ok,fun w => mx a.ok (b.bits w) (a.bits w)⟩

def select (f : κ → TraceCell N ι) : List κ → TraceCell N ι
  | [] => blank
  | i::is => prior (f i) (select f is)

lemma select_ok (f : κ → TraceCell N ι) (xs : List κ) (x : Input N) :
    (select f xs).ok x = true ↔ ∃ i ∈ xs, (f i).ok x = true := by
  induction xs with
  | nil => simp [select,blank]
  | cons i xs ih => simp [select,prior,Compiler.Build.or,ih]

lemma select_data (f : κ → TraceCell N ι) (xs : List κ) (x : Input N) (h : (select f xs).ok x=true) :
    ∃ i ∈ xs, (f i).ok x=true ∧ ∀ w, (select f xs).bits w x=(f i).bits w x := by
  induction xs with
  | nil => simp [select,blank] at h
  | cons i xs ih =>
    by_cases hi : (f i).ok x=true
    · exact ⟨i,List.mem_cons_self,hi,fun w => by simp [select,prior,mx,hi]⟩
    · have h' : (select f xs).ok x=true := by simpa [select,prior,Compiler.Build.or,hi] using h
      obtain ⟨j,hj,hk,hw⟩ := ih h'
      exact ⟨j,List.mem_cons_of_mem _ hj,hk,fun w => by simpa [select,prior,mx,hi] using hw w⟩

lemma compile_prior [Fintype ι] {A : Set (Sig N)} (a b : TraceCell N ι)
    (ha : a.outputs ⊆ A) (hb : b.outputs ⊆ A) : Build A (prior a b).outputs (1+Fintype.card ι*4) := by
  have hy := orG (ha (Or.inl rfl)) (hb (Or.inl rfl))
  have hw := allG (fun w => mx a.ok (b.bits w) (a.bits w)) 4 (fun w =>
    muxG (ha (Or.inl rfl)) (hb (Or.inr ⟨w,rfl⟩)) (ha (Or.inr ⟨w,rfl⟩)))
  exact bothG hy hw

lemma compile_select [Fintype ι] {A : Set (Sig N)} (f : κ → TraceCell N ι) (xs : List κ)
    (hfalse : (fun _ => false) ∈ A) (hmem : ∀ i ∈ xs, (f i).outputs ⊆ A) :
    Build A (select f xs).outputs (xs.length*(1+Fintype.card ι*4)) := by
  induction xs with
  | nil => simp only [List.length_nil,Nat.zero_mul]; apply idle; rintro _ (h | ⟨w,rfl⟩); exact h ▸ hfalse; exact hfalse
  | cons i xs ih =>
    have hp := ih (fun j hj => hmem j (List.mem_cons_of_mem _ hj))
    have hs := compile_prior (A:=A ∪ (select f xs).outputs) (f i) (select f xs)
      ((hmem i List.mem_cons_self).trans Set.subset_union_left) Set.subset_union_right
    exact relax (thenG hp hs) le_rfl le_rfl (by simp [Nat.succ_mul])

def extend (p : TraceCell N ι) (edge : Sig N) (mark : ι → Sig N) : TraceCell N ι :=
  ⟨an p.ok edge,fun w => or (p.bits w) (mark w)⟩

lemma compile_extend [Fintype ι] {A : Set (Sig N)} (p : TraceCell N ι) (edge : Sig N) (mark : ι → Sig N)
    (hp : p.outputs ⊆ A) (he : edge ∈ A) (hm : ∀ w, mark w ∈ A) :
    Build A (extend p edge mark).outputs (1+Fintype.card ι*1) := by
  exact bothG (andG (hp (Or.inl rfl)) he) (allG _ 1 (fun w => orG (hp (Or.inr ⟨w,rfl⟩)) (hm w)))

end TraceCell

section WalkCompiler

variable {N M : ℕ} {ι : Type*}

def startCells (s : Fin M → Sig N) (i : Fin M) : TraceCell N ι := ⟨s i,fun _ _ => false⟩

def nextCells (row : Fin M → TraceCell N ι) (edge : Fin M → Fin M → Sig N)
    (mark : Fin M → Fin M → ι → Sig N) (j : Fin M) : TraceCell N ι :=
  TraceCell.select (fun i => (row i).extend (edge i j) (mark i j)) (List.finRange M)

def walkCells (s : Fin M → Sig N) (e : ℕ → Fin M → Fin M → Sig N)
    (v : ℕ → Fin M → Fin M → ι → Sig N) : ℕ → Fin M → TraceCell N ι
  | 0 => startCells s
  | k+1 => nextCells (walkCells s e v k) (e k) (v k)

def TracePath (s : Fin M → Sig N) (e : ℕ → Fin M → Fin M → Sig N)
    (v : ℕ → Fin M → Fin M → ι → Sig N) (x : Input N) : ℕ → Fin M → (ι → Bool) → Prop
  | 0, j, b => s j x=true ∧ ∀ w, b w=false
  | k+1, j, b => ∃ i old, TracePath s e v x k i old ∧ e k i j x=true ∧ ∀ w, b w=(old w || v k i j w x)

lemma walk_semantics (s : Fin M → Sig N) (e : ℕ → Fin M → Fin M → Sig N)
    (v : ℕ → Fin M → Fin M → ι → Sig N) (x : Input N) (k : ℕ) (j : Fin M) :
    ((walkCells s e v k j).ok x=true ↔ ∃ b, TracePath s e v x k j b) ∧
      ((walkCells s e v k j).ok x=true → TracePath s e v x k j (fun w => (walkCells s e v k j).bits w x)) := by
  induction k generalizing j with
  | zero =>
    change (s j x=true ↔ ∃ b : ι → Bool, s j x=true ∧ ∀ w, b w=false) ∧ _
    exact ⟨⟨fun h => ⟨fun _ => false,h,fun _ => rfl⟩,fun ⟨_,h,_⟩ => h⟩,fun h => ⟨h,fun _ => rfl⟩⟩
  | succ k ih =>
    let f (i : Fin M) := (walkCells s e v k i).extend (e k i j) (v k i j)
    have sel (h : (walkCells s e v (k+1) j).ok x=true) : TracePath s e v x (k+1) j (fun w => (walkCells s e v (k+1) j).bits w x) := by
      obtain ⟨i,_,hi,hw⟩ := TraceCell.select_data f (List.finRange M) x h
      have hh := Bool.and_eq_true_iff.mp hi
      exact ⟨i,_,(ih i).2 hh.1,hh.2,hw⟩
    refine ⟨⟨fun h => ⟨_,sel h⟩,?_⟩,sel⟩
    rintro ⟨b,i,old,hp,he,_⟩
    exact (TraceCell.select_ok f (List.finRange M) x).mpr ⟨i,List.mem_finRange i,Bool.and_eq_true_iff.mpr ⟨(ih i).1.mpr ⟨old,hp⟩,he⟩⟩

def traceCost (M W : ℕ) := M*(M*(1+W*1)+M*(1+W*4))

def cellRow (rows : Fin M → TraceCell N ι) : Set (Sig N) := familyOut Finset.univ (fun j => (rows j).outputs)

lemma compile_layer [Fintype ι] {A : Set (Sig N)} (row : Fin M → TraceCell N ι) (edge : Fin M → Fin M → Sig N)
    (mark : Fin M → Fin M → ι → Sig N) (hf : (fun _ => false)∈A)
    (he : ∀ i j, edge i j∈A) (hm : ∀ i j w, mark i j w∈A) :
    Build (A ∪ cellRow row) (cellRow (nextCells row edge mark)) (traceCost M (Fintype.card ι)) := by
  let B:=A ∪ cellRow row; let W:=Fintype.card ι
  have per (j : Fin M) : Build B (nextCells row edge mark j).outputs (M*(1+W*1)+M*(1+W*4)) := by
    let f (i : Fin M) := (row i).extend (edge i j) (mark i j)
    have hv (i : Fin M) : Build B (f i).outputs (1+W*1) := TraceCell.compile_extend (row i) _ _
      (fun _ h => Or.inr (family_mem (i:=i) h)) (Or.inl (he i j)) (fun w => Or.inl (hm i j w))
    have g := familyG (fun i => (f i).outputs) (1+W*1) hv
    have g' := TraceCell.compile_select (A:=B ∪ cellRow f) f (List.finRange M) (Or.inl (Or.inl hf))
      (fun i _ _ h => Or.inr (family_mem (i:=i) h))
    simpa only [Fintype.card_fin,List.length_finRange,nextCells,B,W,f,cellRow] using thenG g g'
  simpa only [Fintype.card_fin,B,W,cellRow,traceCost] using familyG (fun j => (nextCells row edge mark j).outputs) _ per

lemma compile_walk [Fintype ι] {A : Set (Sig N)} (s : Fin M → Sig N) (e : ℕ → Fin M → Fin M → Sig N)
    (v : ℕ → Fin M → Fin M → ι → Sig N) (t : ℕ) (hf : (fun _ => false)∈A)
    (hs : ∀ i, s i∈A) (he : ∀ k<t, ∀ i j, e k i j∈A) (hv : ∀ k<t, ∀ i j w, v k i j w∈A) :
    Build A (cellRow (walkCells s e v t)) (t*traceCost M (Fintype.card ι)) := by
  induction t with
  | zero =>
    simp only [Nat.zero_mul]; apply idle
    rintro g ⟨j,_,hj⟩; rcases hj with h | ⟨w,rfl⟩
    · exact h ▸ hs j
    · exact hf
  | succ t ih =>
    have h := ih (fun k hk => he k (by omega)) (fun k hk => hv k (by omega))
    have h' := compile_layer (walkCells s e v t) (e t) (v t) hf (he t (by omega)) (hv t (by omega))
    simpa only [Nat.succ_mul,walkCells] using thenG h h'

end WalkCompiler

end TraceSection

section ReduceSection

open Compiler.Build PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

def uniqueRows {n : ℕ} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (x : Input (countLen n)) : Prop :=
  (∀ q q', a q x = true → a q' x = true → q=q') ∧
  (∀ q m z z', b (q,m,z) x = true → b (q,m,z') x = true → z=z')

lemma signed_abs_bound {n : ℕ} (z : Zslot n) : |signed z| ≤ (Bcap n : ℤ) := by
  have hz := z.isLt; unfold signed; apply abs_le.mpr; omega

lemma bank_unique {n : ℕ} (x : Input (countLen n)) : uniqueRows massOK itemOK x := by
  have hB : 7 ≤ modBudget n := by unfold modBudget; omega
  constructor
  · intro q s hq hs; rw [massOK_iff] at hq hs
    have hb (i : Width n) : (2:ℤ)^i.val ≤ 2^(2*n) := pow_le_pow_right₀ (by decide) (Nat.le_of_lt_succ i.isLt)
    have he := residues_separate ((2:ℤ)^q.val) (2^s.val) (modBudget n) hB (by
      calc |(2:ℤ)^q.val-2^s.val| ≤ |(2:ℤ)^q.val|+|(2:ℤ)^s.val| := abs_sub ..
        _ ≤ 2^(2*n+1) := by simp only [abs_of_nonneg (by positivity : 0 ≤ (2:ℤ)^q.val),abs_of_nonneg (by positivity : 0 ≤ (2:ℤ)^s.val), pow_succ]; linarith [hb q,hb s]
        _ < _ := pow_lt_pow_right₀ (by decide) (by unfold modBudget rowBudget; omega))
      (fun u => by simpa using (hq u).symm.trans (hs u))
    exact Fin.ext ((pow_right_strictMono₀ (by norm_num : (1:ℤ)<2)).injective he)
  · intro q m z w hz hw; rw [itemOK_iff] at hz hw
    let c := ((2:ℤ)^q.val)^m.val
    have he : c*signed z = c*signed w := by
      apply residues_separate _ _ _ hB
      · have hb : |signed z-signed w| ≤ 2*(Bcap n : ℤ) := (abs_sub ..).trans (by linarith [signed_abs_bound z,signed_abs_bound w])
        have h1 : (2*n : ℤ) ≤ 2^(2*n) := by exact_mod_cast (Nat.lt_two_pow_self (n := 2*n)).le
        have h2 : (radius n : ℤ) ≤ 2^(radius n) := by exact_mod_cast (Nat.lt_two_pow_self (n := radius n)).le
        have hqm : q.val*m.val ≤ (2*n)*radius n := Nat.mul_le_mul (Nat.le_of_lt_succ q.isLt) (Nat.le_of_lt_succ m.isLt)
        rw [← mul_sub, abs_mul, abs_of_nonneg (by dsimp [c]; positivity : 0≤c)]
        calc c*|signed z-signed w| ≤ c*(2*Bcap n) := by gcongr
          _ ≤ 2^(q.val*m.val)*(2*(2^(2*n)*2^(radius n))) := by
            dsimp [c,Bcap]; push_cast; rw [pow_mul]; gcongr
          _ < _ := by
            rw [show (2:ℤ)*(2^(2*n)*2^(radius n)) = 2^(2*n+radius n+1) by rw [pow_succ,pow_add]; ring, ← pow_add]
            apply pow_lt_pow_right₀ (by decide); unfold modBudget rowBudget; nlinarith
      · intro u; simpa [c] using (hz u).symm.trans (hw u)
    have hzw := mul_left_cancel₀ (by dsimp [c]; positivity : c≠0) he
    apply Fin.ext; unfold signed at hzw; omega

def polySize (F : ℕ → ℕ) : Prop := ∃ k : ℕ, ∀ n, F n ≤ (n+2)^k

lemma poly_id : polySize id := ⟨1,by intro n; simp⟩
lemma poly_const (c : ℕ) : polySize (fun _ => c) := by
  exact ⟨c,fun n => (Nat.lt_two_pow_self (n := c)).le.trans (Nat.pow_le_pow_left (by omega) _)⟩
lemma poly_add {f g : ℕ → ℕ} (h : polySize f) (j : polySize g) : polySize (fun n => f n+g n) := by
  obtain ⟨a,ha⟩ := h; obtain ⟨b,hb⟩ := j
  refine ⟨max a b+1, fun n => ?_⟩
  have hf := (ha n).trans (Nat.pow_le_pow_right (by omega) (le_max_left a b))
  have hg := (hb n).trans (Nat.pow_le_pow_right (by omega) (le_max_right a b))
  rw [pow_succ]; nlinarith
lemma poly_mul {f g : ℕ → ℕ} (h : polySize f) (j : polySize g) : polySize (fun n => f n*g n) := by
  obtain ⟨a,ha⟩ := h; obtain ⟨b,hb⟩ := j
  exact ⟨a+b, fun n => (pow_add (n+2) a b).symm ▸ Nat.mul_le_mul (ha n) (hb n)⟩

set_option maxHeartbeats 2400000 in
lemma bank_poly : polySize (fun n => 3+preCost n) := by
  unfold preCost checkCost unitCost bitCard decoderCost logCost multCost unCost opCost modBudget rowBudget Bcap radius stride
  repeat first | apply poly_add | apply poly_mul | apply poly_const | exact poly_id

def layoutBasis {n : ℕ} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n)) : Set (Sig (countLen n)) :=
  (Set.range (fun i : Fin (2+n*n) => fun x : Input (countLen n) => x (Fin.castAdd ((n+1)*(n+1)*(2*n+1)) i)) ∪
    {fun _ => false, fun _ => true}) ∪ (Set.range a ∪ Set.range b)

def permPrefix {n : ℕ} (σ : Equiv.Perm (Fin n)) :=
  [false,true] ++ (List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin n => decide (σ i=j)))).flatten

def pinOutputs {n : ℕ} (ok : Sig (countLen n)) (pw : Bool → Bool × Fin n → Sig (countLen n)) : Set (Sig (countLen n)) :=
  {ok} ∪ Set.range (fun w : Bool × (Bool × Fin n) => pw w.1 w.2)

def readPins {n : ℕ} (pw : Bool → Bool × Fin n → Sig (countLen n)) (x : Input (countLen n)) : Pins n :=
  fun v => if pw false v x then some (pw true v x) else none

def LayoutCore : Prop := ∃ K : ℕ, ∀ (t : ℕ) (budget : Fin (t+1)),
  let n := t+1
  let d := budget.val+1
  ∀ (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n)),
  ∃ (ok : Sig (countLen n)) (pw : Bool → Bool × Fin n → Sig (countLen n)),
    Build (layoutBasis a b) (pinOutputs ok pw) ((n+2)^(K*(d+1))) ∧
    ∀ σ : Equiv.Perm (Fin n), (∃ roots : Fin d → Fin n, ∀ i, ∃ j : Fin d, ∃ h : Fin n, (σ^h.val) (roots j) = i) →
    ∀ x : Input (countLen n), (List.ofFn x).take (2+n*n) = permPrefix σ → uniqueRows a b x →
    (ok x = true ↔ ∃ p : Pins n, fitsSignals a b x σ p) ∧
      (ok x = true → fitsSignals a b x σ (readPins pw x))

lemma prefix_length {n : ℕ} (σ : Equiv.Perm (Fin n)) : (permPrefix σ).length = 2+n*n := by
  simp [permPrefix,List.length_flatten,List.map_ofFn,List.sum_ofFn]; omega

lemma prefix_take {n : ℕ} (σ : Equiv.Perm (Fin n)) (H : Histogram n) :
    (countWord σ H).take (2+n*n) = permPrefix σ := by
  change (permPrefix σ ++ _).take _ = _; rw [← prefix_length σ]; simp

lemma total_budget {E K n d : ℕ} (hp : 3+preCost n ≤ (n+2)^E) :
    3+(preCost n+(n+2)^(K*(d+1))) ≤ (n+2)^((E+K+2)*(d+1)) := by
  let B:=n+2; let r:=(E+K+1)*(d+1)
  have h1 : E≤r := by unfold r; nlinarith
  have h2 : K*(d+1)≤r := by unfold r; nlinarith
  have h3 : r+1 ≤ (E+K+2)*(d+1) := by unfold r; nlinarith
  calc 3+(preCost n+(n+2)^(K*(d+1))) ≤ B^r+B^r := by
         rw [← Nat.add_assoc]; gcongr; exact hp.trans (Nat.pow_le_pow_right (by omega) h1)
       _ ≤ B^(r+1) := by rw [pow_succ,← Nat.mul_two]; exact Nat.mul_le_mul_left _ (by dsimp [B]; omega)
       _ ≤ _ := Nat.pow_le_pow_right (by omega) h3

open Compiler.Build

abbrev PinMarks (n : ℕ) := Bool × (Bool × Fin n)

lemma trace_cost_explicit (n M : ℕ) : traceCost M (Fintype.card (PinMarks n)) = M^2*(2+20*n) := by
  simp [traceCost,PinMarks]; ring

def traceGivens {N M : ℕ} {ι : Type*} (s : Fin M → Sig N) (e : ℕ → Fin M → Fin M → Sig N)
    (v : ℕ → Fin M → Fin M → ι → Sig N) (T : ℕ) : Set (Sig N) :=
  Set.range s ∪ ({g | ∃ k<T, ∃ i j, g=e k i j} ∪ {g | ∃ k<T, ∃ i j w, g=v k i j w})

def marksPin {n : ℕ} (u : PinMarks n → Bool) : Pins n :=
  fun v => if u (false,v) then some (u (true,v)) else none

def LayoutTrace : Prop := ∃ K : ℕ, ∀ (t : ℕ) (budget : Fin (t+1)),
  let n:=t+1
  let d:=budget.val+1
  let N:=countLen n
  ∀ (a : Width n → Sig N) (b : ChargeIx n → Sig N),
  ∃ (M T B : ℕ) (j : Fin M) (s : Fin M → Sig N) (e : ℕ → Fin M → Fin M → Sig N)
    (v : ℕ → Fin M → Fin M → PinMarks n → Sig N),
    Build (layoutBasis a b) (traceGivens s e v T) B ∧ B+T*(M^2*(2+20*n)) ≤ (n+2)^(K*(d+1)) ∧
    ∀ σ : Equiv.Perm (Fin n), (∃ roots : Fin d → Fin n, ∀ i, ∃ j : Fin d, ∃ h : Fin n, (σ^h.val) (roots j)=i) →
    ∀ x : Input N, (List.ofFn x).take (2+n*n)=permPrefix σ → uniqueRows a b x →
      ((∃ u, TracePath s e v x T j u) ↔ ∃ p : Pins n, fitsSignals a b x σ p) ∧
      (∀ u, TracePath s e v x T j u → fitsSignals a b x σ (marksPin u))

lemma layout_core_of_trace (H : LayoutTrace) : LayoutCore := by
  obtain ⟨K,hK⟩ := H
  refine ⟨K,?_⟩; intro t budget; dsimp only; intro a b
  let n:=t+1; let d:=budget.val+1; let N:=countLen n
  obtain ⟨M,T,B,j,s,e,v,hgiven,hsize,hsem⟩ := hK t budget a b
  let A:=layoutBasis a b ∪ traceGivens s e v T
  have hf : (fun _ => false) ∈ A := Or.inl (Or.inl (Or.inr (Or.inl rfl)))
  have hs (i : Fin M) : s i∈A := Or.inr (Or.inl ⟨i,rfl⟩)
  have he (k : ℕ) (hk : k<T) (i j : Fin M) : e k i j∈A := Or.inr (Or.inr (Or.inl ⟨k,hk,i,j,rfl⟩))
  have hv (k : ℕ) (hk : k<T) (i j : Fin M) (w : PinMarks n) : v k i j w∈A := Or.inr (Or.inr (Or.inr ⟨k,hk,i,j,w,rfl⟩))
  let row:=walkCells s e v T
  let pw (k : Bool) (u : Bool × Fin n) := (row j).bits (k,u)
  refine ⟨(row j).ok,pw,?_,?_⟩
  · apply relax (thenG hgiven (compile_walk s e v T hf hs he hv)) le_rfl _ (by simpa only [trace_cost_explicit] using hsize)
    rintro g (hh | ⟨⟨k,w⟩,rfl⟩)
    · exact family_mem (i:=j) (Or.inl hh : g ∈ (row j).outputs)
    · exact family_mem (i:=j) (Or.inr ⟨(k,w),rfl⟩ : pw k w ∈ (row j).outputs)
  · intro σ hroot x hx hu
    obtain ⟨hyes,hwit⟩ := hsem σ hroot x hx hu
    have hc:=walk_semantics s e v x T j
    exact ⟨hc.1.trans hyes,fun hh => hwit _ (hc.2 hh)⟩

lemma literal_profile_frontend : ∃ C : ℕ, 0<C ∧ ∀ t : ℕ,
  let n:=t+1
  ∃ (g : Circuit) (mw : Width n → Fin (countLen n+g.size))
    (cw : ChargeIx n → Fin (countLen n+g.size)),
    ReadsBack (countLen n) g ∧ g.size ≤ (n+2)^C ∧
    (∀ a ∈ g.gates, ((a.op = .and ∨ a.op = .or) ∧ a.inputs.length = 2) ∨ (a.op = .not ∧ a.inputs.length = 1)) ∧
    ∀ (σ : Equiv.Perm (Fin n)) (H : Histogram n),
      let ws:=g.wires (countWord σ H)
      ∀ p : Pins n, physical σ p = tableOf H ↔ ws.getD (mw (qIndex p)).val false = true ∧
        ∀ m : Order n, ws.getD (cw (qIndex p,m,arcSlot σ p m)).val false = true := by
  classical
  obtain ⟨E,hE⟩ := bank_poly
  refine ⟨E+1,by omega,?_⟩; intro t
  let n:=t+1; let N:=countLen n
  have i0 : Fin N := ⟨0,by dsimp [N,countLen]; omega⟩
  have big := thenG (make_constants i0) (query_bank n)
  have start : Compiler.GateBridge.Scheduled N id 0 (inputs N) :=
    Compiler.GateBridge.start (F:=id) (fun (i : Fin N) (x : Input N) => x i) (fun _ _ => rfl)
  obtain ⟨k,hk,gs,hgs,hr,hg,hw⟩ := big.run start le_rfl
  let g : Circuit := ⟨gs,0⟩
  have hsize : g.size=k := by simpa [g,Circuit.size] using hgs
  have w (s : Sig N) (hs : s ∈ Set.range (@massOK n) ∪ Set.range (@itemOK n)) :
      ∃ v : Fin (N+g.size), ∀ x : Input N, (g.wires (List.ofFn x)).getD v.val false = s x := by
    obtain ⟨i,hi,hy⟩ := hw _ (Or.inr hs); exact ⟨⟨i,by simpa [hsize] using hi⟩,hy⟩
  choose mw hm using fun q : Width n => w _ (Or.inl ⟨q,rfl⟩)
  choose cw hc using fun z : ChargeIx n => w _ (Or.inr ⟨z,rfl⟩)
  refine ⟨g,mw,cw,hr,hsize ▸ (hk.trans ((hE n).trans (Nat.pow_le_pow_right (by omega) (by omega)))),hg,?_⟩
  intro σ H; obtain ⟨x,hx,hs⟩ := countWord_input (n:=n) (by dsimp [n]; omega) σ H
  have hH : readHist x = H := by funext r b j; exact hs (r,b,j)
  dsimp only
  intro p
  change physical σ p = tableOf H ↔ (g.wires (countWord σ H)).getD (mw (qIndex p)).val false = true ∧ _
  rw [← hx,hm]; simp_rw [hc]
  change physical σ p = tableOf H ↔ fitsSignals massOK itemOK x σ p
  rw [query_bank_spec,hH]

lemma reduction_from_layout_core (hcore : LayoutCore) : (∃ C : ℕ, 0 < C ∧ ∀ t : ℕ,
  let n := t+1
  let I := Fin n
  let J := Fin (n+1)
  let V := Bool × I
  let P := V → Option Bool
  let W := Fin (2*n+1)
  let inputs := 2+n*n+(n+1)*(n+1)*(2*n+1)
  let hist := fun (σ : Equiv.Perm I) (p : P) (r b : J) =>
    ((Finset.univ : Finset (V → Bool)).filter (fun x =>
      (∀ v, p v = none ∨ p v = some (x v)) ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,i))).card = r.val ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,σ i))).card = b.val)).card
  ∀ budget : I,
    let d := budget.val+1
    ∃ (g : PEqualNP.CircuitLowerBounds.Circuit) (flag : Fin (inputs+g.size))
      (pinWire : Bool → V → Fin (inputs+g.size)),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs g ∧ g.size ≤ (n+2)^(C*(d+1)) ∧
      (∀ gate ∈ g.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
        (gate.op = .not ∧ gate.inputs.length = 1)) ∧
      ∀ (σ : Equiv.Perm I), (∃ root : Fin d → I, ∀ i : I,
        ∃ a : Fin d, ∃ h : I, (σ ^ h.val) (root a) = i) →
      ∀ H : J → J → W → Bool,
        let table := fun (r b : J) => ∑ k : W, (H r b k).toNat * 2^k.val
        let permBits := (List.ofFn (fun i : I => List.ofFn (fun j : I => decide (σ i = j)))).flatten
        let countBits := (List.ofFn (fun r : J => (List.ofFn (fun b : J => List.ofFn (H r b))).flatten)).flatten
        let ws := g.wires ([false,true] ++ permBits ++ countBits)
        let q : P := fun v => if ws.getD (pinWire false v).val false then some (ws.getD (pinWire true v).val false) else none
        (ws.getD flag.val false = true ↔ ∃ p : P, hist σ p = table) ∧
          (ws.getD flag.val false = true → hist σ q = table)) := by
  classical
  obtain ⟨K,HK⟩ := hcore
  obtain ⟨E,HE⟩ := bank_poly
  refine ⟨E+K+2,by omega,?_⟩
  intro t; dsimp only; intro budget
  let n := t+1
  let d := budget.val+1
  let N := countLen n
  obtain ⟨ok,pw,hbuild,hsem⟩ := HK t budget massOK itemOK
  have sub : layoutBasis (@massOK n) (@itemOK n) ⊆ base N ∪ (Set.range massOK ∪ Set.range itemOK) := by
    rintro g ((⟨i,rfl⟩ | h) | h)
    · exact Or.inl (Or.inl ⟨_,rfl⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hb := thenG (query_bank n) (relax hbuild sub le_rfl le_rfl)
  have i0 : Fin N := ⟨0,by dsimp [N,countLen]; omega⟩
  have whole := thenG (make_constants i0) hb
  have start : Compiler.GateBridge.Scheduled N id 0 (inputs N) :=
    Compiler.GateBridge.start (F:=id) (fun (i : Fin N) (x : Input N) => x i) (fun _ _ => rfl)
  obtain ⟨k,hk,gs,hgs,hr,hg,hw⟩ := whole.run start le_rfl
  let g : Circuit := ⟨gs,0⟩
  have hsize : g.size = k := by simpa [g,Circuit.size] using hgs
  have wire (s : Sig N) (hs : s ∈ pinOutputs ok pw) : ∃ w : Fin (N+g.size),
      ∀ x, (g.wires (List.ofFn x)).getD w.val false = s x := by
    obtain ⟨w,hh,hy⟩ := hw _ (Or.inr hs); exact ⟨⟨w,by simpa [hsize] using hh⟩,hy⟩
  obtain ⟨flag,hflag⟩ := wire ok (Or.inl rfl)
  have hwires (b : Bool) (v : Bool × Fin n) := wire (pw b v) (Or.inr ⟨(b,v),rfl⟩)
  choose pinWire hpins using hwires
  refine ⟨g,flag,pinWire,hr,hsize ▸ (hk.trans (total_budget (d:=d) (HE n))),hg,?_⟩
  intro σ roots H
  obtain ⟨x,hx,hdata⟩ := countWord_input (n:=n) (by dsimp [n]; omega) σ H
  have hH : readHist x = H := by funext r b j; exact hdata (r,b,j)
  have hpre : (List.ofFn x).take (2+n*n) = permPrefix σ := hx ▸ prefix_take σ H
  obtain ⟨hyes,hwit⟩ := hsem σ roots x hpre (bank_unique x)
  have hmatch (p : Pins n) : fitsSignals massOK itemOK x σ p ↔ physical σ p = tableOf H := by
    simpa only [hH] using query_bank_spec σ x p
  change ((g.wires (countWord σ H)).getD flag.val false = true ↔ ∃ p : Pins n, physical σ p = tableOf H) ∧
    ((g.wires (countWord σ H)).getD flag.val false = true → physical σ (fun v =>
      if (g.wires (countWord σ H)).getD (pinWire false v).val false then
        some ((g.wires (countWord σ H)).getD (pinWire true v).val false) else none) = tableOf H)
  rw [← hx,hflag]
  constructor
  · exact hyes.trans (exists_congr hmatch)
  · intro h
    have he : (fun v => if (g.wires (List.ofFn x)).getD (pinWire false v).val false then
        some ((g.wires (List.ofFn x)).getD (pinWire true v).val false) else none) = readPins pw x := by
      funext v; rw [hpins false v x, hpins true v x]; rfl
    rw [he]; exact (hmatch (readPins pw x)).mp (hwit h)

lemma reduction_from_layout_trace (h : LayoutTrace) : (∃ C : ℕ, 0 < C ∧ ∀ t : ℕ,
  let n := t+1
  let I := Fin n
  let J := Fin (n+1)
  let V := Bool × I
  let P := V → Option Bool
  let W := Fin (2*n+1)
  let inputs := 2+n*n+(n+1)*(n+1)*(2*n+1)
  let hist := fun (σ : Equiv.Perm I) (p : P) (r b : J) =>
    ((Finset.univ : Finset (V → Bool)).filter (fun x =>
      (∀ v, p v = none ∨ p v = some (x v)) ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,i))).card = r.val ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,σ i))).card = b.val)).card
  ∀ budget : I,
    let d := budget.val+1
    ∃ (g : PEqualNP.CircuitLowerBounds.Circuit) (flag : Fin (inputs+g.size))
      (pinWire : Bool → V → Fin (inputs+g.size)),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs g ∧ g.size ≤ (n+2)^(C*(d+1)) ∧
      (∀ gate ∈ g.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
        (gate.op = .not ∧ gate.inputs.length = 1)) ∧
      ∀ (σ : Equiv.Perm I), (∃ root : Fin d → I, ∀ i : I,
        ∃ a : Fin d, ∃ h : I, (σ ^ h.val) (root a) = i) →
      ∀ H : J → J → W → Bool,
        let table := fun (r b : J) => ∑ k : W, (H r b k).toNat * 2^k.val
        let permBits := (List.ofFn (fun i : I => List.ofFn (fun j : I => decide (σ i = j)))).flatten
        let countBits := (List.ofFn (fun r : J => (List.ofFn (fun b : J => List.ofFn (H r b))).flatten)).flatten
        let ws := g.wires ([false,true] ++ permBits ++ countBits)
        let q : P := fun v => if ws.getD (pinWire false v).val false then some (ws.getD (pinWire true v).val false) else none
        (ws.getD flag.val false = true ↔ ∃ p : P, hist σ p = table) ∧
          (ws.getD flag.val false = true → hist σ q = table)) :=
  reduction_from_layout_core (layout_core_of_trace h)

end ReduceSection

end PEqualNP.Outside.L_pcx_386.Core

namespace PEqualNP.Outside.L_pcx_386.Allocation

open PEqualNP.Outside.L_pcx_386.Core

abbrev Arc := ℕ × ℕ × Bool
abbrev Count (n : ℕ) := Fin (2*n+1)
abbrev Choice (n d : ℕ) := Fin d → Count n × Count n
abbrev Box (n d : ℕ) := Fin d → Fin 4 → Count n
abbrev State (n d : ℕ) := Count n × Box n d

inductive Row where
  | diag (j : ℕ) (charge : ℤ)
  | close (charge : ℤ)
  | skew (r b : ℕ) (single double : ℤ)
deriving DecidableEq

def pos {n d} (c : Choice n d) := ∑ i, (c i).1.val
def neg {n d} (c : Choice n d) := ∑ i, (c i).2.val

def Credit {n d} (row : Row) (old next : Count n) (c : Choice n d) : Prop :=
  match row with
  | .diag _ z => next.val = pos c ∧ (neg c : ℤ) - pos c + old.val = z
  | .close z => (old.val : ℤ) = z ∧ next.val = 0
  | .skew _ _ u v => old.val = 0 ∧ next.val = 0 ∧ (pos c : ℤ) = v ∧ (neg c : ℤ) = u+v

instance {n d} (row : Row) (old next : Count n) (c : Choice n d) :
    Decidable (Credit row old next c) := by cases row <;> unfold Credit <;> infer_instance

def bundle (r b p m : ℕ) : List Arc :=
  List.replicate p (r,b,true) ++ List.replicate m (r,b,false)

def packet {n d} (row : Row) (c : Choice n d) (i : Fin d) : List Arc :=
  match row with
  | .diag j _ => bundle j j (c i).1.val (c i).2.val
  | .skew r b _ _ => bundle r b (c i).1.val (c i).2.val
  | .close _ => []

def tally : List Arc → Fin 4 → ℕ
  | [] => 0
  | (r,b,s)::rest => ![r,b,1,(!s).toNat] + tally rest

theorem tally_append (a b : List Arc) : tally (a ++ b) = tally a + tally b := by
  induction a with
  | nil => simp [tally]
  | cons a rest ih =>
    obtain ⟨r,b',s⟩ := a
    simp [tally,ih,add_assoc]

def step {n d} (r : Row) (a b : State n d) : Bool :=
  decide (∃ c : Choice n d, Credit r a.1 b.1 c ∧
    ∀ i j, (b.2 i j).val = (a.2 i j).val + tally (packet r c i) j)

def scan {n d} : List Row → State n d → State n d → Bool
  | [], a, b => decide (a=b)
  | r::rs, a, b => decide (∃ m : State n d, step r a m = true ∧ scan rs m b = true)

def Emits {n d} : List Row → Count n → Count n → (Fin d → List Arc) → Prop
  | [], a, b, bags => a=b ∧ ∀ i, bags i = []
  | r::rs, a, b, bags => ∃ (next : Count n) (c : Choice n d) (tail : Fin d → List Arc),
    Credit r a next c ∧ Emits rs next b tail ∧ ∀ i, bags i = packet r c i ++ tail i

theorem scan_iff {n d} (rs : List Row) (a b : State n d) :
    scan rs a b = true ↔ ∃ bags : Fin d → List Arc, Emits rs a.1 b.1 bags ∧
      ∀ i j, (b.2 i j).val = (a.2 i j).val + tally (bags i) j := by
  induction rs generalizing a b with
  | nil =>
    simp only [scan,decide_eq_true_eq,Emits]
    constructor
    · rintro rfl
      exact ⟨fun _ => [],⟨rfl,fun _ => rfl⟩,by simp [tally]⟩
    · rintro ⟨bags,⟨hab,hbags⟩,h⟩
      refine Prod.ext hab (funext fun i => funext fun j => Fin.ext ?_)
      simpa [hbags,tally] using (h i j).symm
  | cons r rs ih =>
    simp only [scan,decide_eq_true_eq,step,Emits]
    constructor
    · rintro ⟨m,⟨c,hc,hm⟩,hs⟩
      obtain ⟨tail,ht,hb⟩ := (ih m b).mp hs
      exact ⟨fun i => packet r c i ++ tail i,⟨m.1,c,tail,hc,ht,fun _ => rfl⟩,
        fun i j => by simp [hb i j,hm i j,tally_append,add_assoc]⟩
    · rintro ⟨bags,⟨next,c,tail,hc,ht,he⟩,hb⟩
      have fit (i : Fin d) (j : Fin 4) :
          (a.2 i j).val + tally (packet r c i) j < 2*n+1 := by
        have bound := (b.2 i j).isLt
        have h := hb i j
        rw [he i,tally_append,Pi.add_apply] at h
        omega
      let m : State n d := (next,fun i j => ⟨_,fit i j⟩)
      refine ⟨m,⟨c,hc,fun _ _ => rfl⟩,(ih m b).mpr ⟨tail,ht,?_⟩⟩
      intro i j
      simpa [m,he i,tally_append,add_assoc] using hb i j

theorem state_card (n d : ℕ) : Fintype.card (State n d) = (2*n+1)^(4*d+1) := by
  simp [State,Box,Count,pow_succ,pow_mul,mul_pow,Nat.mul_comm]

theorem choice_card (n d : ℕ) : Fintype.card (Choice n d) = (2*n+1)^(2*d) := by
  simp [Choice,Count,pow_mul,pow_two]

theorem state_budget (n d : ℕ) : Fintype.card (State n d) ≤ (n+2)^(8*(d+1)) := by
  rw [state_card]
  calc _ ≤ ((n+2)^2)^(4*d+1) := Nat.pow_le_pow_left (by nlinarith) _
       _ = (n+2)^(2*(4*d+1)) := (pow_mul ..).symm
       _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem choose_floating {d : ℕ} (singletons : Finset (Fin d)) (arcs free n : ℕ) :
    (∃ U ⊆ singletons, arcs+free = 2*n + U.card) ↔
      2*n ≤ arcs+free ∧ arcs+free ≤ 2*n+singletons.card := by
  constructor
  · rintro ⟨u,hu,eq⟩
    have := Finset.card_le_card hu
    omega
  · rintro ⟨low,high⟩
    obtain ⟨u,hu,sz⟩ := Finset.exists_subset_card_eq (s:=singletons)
      (show arcs+free-2*n ≤ singletons.card by omega)
    exact ⟨u,hu,by omega⟩

theorem dyadic_cover {n j : ℕ} (hj : 0<j) (bound : j≤n) :
    ∃ o ≤ n, Odd o ∧ ∃ k ≤ n, j=2^k*o := by
  obtain ⟨k,o,odd,eq⟩ := Nat.exists_eq_two_pow_mul_odd hj.ne'
  have ho : 0<o := by obtain ⟨v,hv⟩ := odd; omega
  have h1 : o ≤ 2^k*o := Nat.le_mul_of_pos_left _ (by positivity)
  have h2 : 2^k ≤ 2^k*o := Nat.le_mul_of_pos_right _ ho
  have hk := Nat.lt_two_pow_self (n:=k)
  exact ⟨o,by omega,odd,k,by omega,eq⟩

theorem odd_ne_succ {o : ℕ} (odd : Odd o) (a v : ℕ) : o ≠ 2^(a+1)*v := by
  obtain ⟨q,hq⟩ := odd
  rw [pow_succ',Nat.mul_assoc]
  omega

theorem dyadic_unique {u v : ℕ} (hu : Odd u) (hv : Odd v) (a b : ℕ)
    (eq : 2^a*u=2^b*v) : a=b ∧ u=v := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simpa using eq
    | succ b => exact False.elim (odd_ne_succ hu b v (by simpa using eq))
  | succ a ih =>
    cases b with
    | zero => exact False.elim (odd_ne_succ hv a u (by simpa using eq.symm))
    | succ b =>
      simp only [pow_succ',Nat.mul_assoc] at eq
      obtain ⟨ab,uv⟩ := ih b (Nat.eq_of_mul_eq_mul_left (by decide : 0<2) eq)
      exact ⟨congrArg Nat.succ ab,uv⟩

theorem real_diag {n d} (σ : Equiv.Perm (Fin n)) (p : Pins n) (j : ℕ)
    (old next : Count n) (c : Choice n d)
    (ho : (old.val : ℤ) = if 2 ∣ j then (perDirection (j/2,j/2) true (arcList σ p) : ℤ) else 0)
    (hn : next.val = pos c)
    (hp : pos c = perDirection (j,j) true (arcList σ p))
    (hm : neg c = perDirection (j,j) false (arcList σ p)) :
    Credit (.diag j (imbalance (arcList σ p) (j,j))) old next c := by
  refine ⟨hn,?_⟩
  have h := physical_diagonal_counts σ p j
  rw [hp,hm,ho]
  omega

theorem real_skew {n d} (σ : Equiv.Perm (Fin n)) (p : Pins n) (r b : ℕ)
    (h : r+1=b ∨ b+1=r) (old next : Count n) (c : Choice n d)
    (ho : old.val=0) (hn : next.val=0)
    (hp : pos c = perDirection (r,b) true (arcList σ p))
    (hm : neg c = perDirection (r,b) false (arcList σ p)) :
    Credit (.skew r b (imbalance (arcList σ p) (r,b)) (imbalance (arcList σ p) (twicePair (r,b)))) old next c := by
  obtain ⟨pos',neg'⟩ := physical_offdiag_counts σ p (r,b) h
  exact ⟨ho,hn,hp ▸ pos',hm ▸ neg'⟩

theorem real_terminal {n d} (σ : Equiv.Perm (Fin n)) (p : Pins n) (j : ℕ)
    (old next : Count n) (c : Choice n d) (hn : next.val=0)
    (hp : old.val = perDirection (j,j) true (arcList σ p))
    (absent : ∀ a ∈ arcList σ p, twicePair (j,j) ≠ (a.1,a.2.1)) :
    Credit (.close (imbalance (arcList σ p) (twicePair (j,j)))) old next c := by
  refine ⟨?_,hn⟩
  rw [imbalance_at_twice,perDirection_zero _ _ true absent,perDirection_zero _ _ false absent,hp]
  simp

end PEqualNP.Outside.L_pcx_386.Allocation

namespace PEqualNP.Outside.L_pcx_386.Allocation

open PEqualNP.Outside.L_pcx_386.Core
open PEqualNP.Outside.L_pcx_386.Core.Compiler.Build

def Moves {n d} (r : Row) (a b : State n d) (c : Choice n d) : Prop :=
  ∀ i j, (b.2 i j).val = (a.2 i j).val + tally (packet r c i) j

instance {n d} (r : Row) (a b : State n d) (c : Choice n d) : Decidable (Moves r a b c) := by
  unfold Moves; infer_instance

theorem bundle_sizes (r b plus minus : ℕ) :
    tally (bundle r b plus minus) 2 = plus+minus ∧
      tally (bundle r b plus minus) 3 = minus := by
  have rep (s : Bool) (k : ℕ) : tally (List.replicate k (r,b,s)) 2 = k ∧
      tally (List.replicate k (r,b,s)) 3 = if s then 0 else k := by
    induction k with
    | zero => simp [tally]
    | succ k ih => cases s <;> simp [List.replicate_succ,tally,ih.1,ih.2,Nat.add_comm]
  simp [bundle,tally_append,(rep true plus).1,(rep false minus).1,
    (rep true plus).2,(rep false minus).2]

theorem packet_unique {n d} (r : Row) {a b : State n d} {c f : Choice n d}
    (hc : Moves r a b c) (hf : Moves r a b f) (i : Fin d) : packet r c i = packet r f i := by
  have h2 := Nat.add_left_cancel ((hc i 2).symm.trans (hf i 2))
  have h3 := Nat.add_left_cancel ((hc i 3).symm.trans (hf i 3))
  have eq (R B : ℕ)
      (x : tally (bundle R B (c i).1.val (c i).2.val) 2 = tally (bundle R B (f i).1.val (f i).2.val) 2)
      (y : tally (bundle R B (c i).1.val (c i).2.val) 3 = tally (bundle R B (f i).1.val (f i).2.val) 3) :
      bundle R B (c i).1.val (c i).2.val = bundle R B (f i).1.val (f i).2.val := by
    rw [(bundle_sizes ..).1,(bundle_sizes ..).1] at x
    rw [(bundle_sizes ..).2,(bundle_sizes ..).2] at y
    rw [y] at x ⊢
    rw [Nat.add_right_cancel x]
  cases r with
  | diag j z => exact eq j j h2 h3
  | skew r b z w => exact eq r b h2 h3
  | close _ => rfl

noncomputable def marking {n d} (r : Row) (a b : State n d) (i : Fin d) : List Arc :=
  if h : ∃ c : Choice n d, Moves r a b c then packet r h.choose i else []

theorem marking_correct {n d} (r : Row) (a b : State n d) {c : Choice n d}
    (hc : Moves r a b c) (i : Fin d) : marking r a b i = packet r c i := by
  have h : ∃ c : Choice n d, Moves r a b c := ⟨c,hc⟩
  rw [marking,dite_eq_left h]
  exact packet_unique r h.choose_spec hc i

def testDose {N n d} (u v : ℤ → Sig N) (r : Row) (a b : State n d) (c : Choice n d) : Sig N :=
  if Moves r a b c then
    match r with
    | .diag _ _ => if b.1.val = pos c then u ((neg c : ℤ)-pos c+a.1.val) else fun _ => false
    | .close _ => if b.1.val = 0 then u a.1.val else fun _ => false
    | .skew _ _ _ _ => if a.1.val = 0 ∧ b.1.val = 0 then an (u ((neg c : ℤ)-pos c)) (v (pos c))
        else fun _ => false
  else fun _ => false

def edgeSignal {N n d} (u v : ℤ → Sig N) (r : Row) (a b : State n d) : Sig N :=
  fun x => decide (∃ c : Choice n d, testDose u v r a b c x = true)

theorem build_dose {N n d} {A : Set (Sig N)} (u v : ℤ → Sig N) (r : Row) (a b : State n d)
    (hf : (fun _ => false) ∈ A) (hu : ∀ i, u i ∈ A) (hv : ∀ i, v i ∈ A) (c : Choice n d) :
    Build A {testDose u v r a b c} 1 := by
  have reuse {g : Sig N} (h : g∈A) : Build A {g} 1 :=
    relax (idle (Set.singleton_subset_iff.mpr h)) le_rfl le_rfl (by decide)
  by_cases hm : Moves r a b c
  · cases r with
    | diag j z =>
      by_cases h : b.1.val = pos c
      · simpa [testDose,hm,h] using reuse (hu ((neg c : ℤ)-pos c+a.1.val))
      · simpa [testDose,hm,h] using reuse hf
    | close z =>
      by_cases h : b.1.val = 0
      · simpa [testDose,hm,h] using reuse (hu a.1.val)
      · simpa [testDose,hm,h] using reuse hf
    | skew rr bb z w =>
      by_cases h : a.1.val = 0 ∧ b.1.val = 0
      · simpa only [testDose,ite_eq_left hm,ite_eq_left h] using andG (hu ((neg c : ℤ)-pos c)) (hv (pos c))
      · simpa only [testDose,ite_eq_left hm,ite_eq_right h] using reuse hf
  · simpa [testDose,hm] using reuse hf

theorem build_edge {N n d} {A : Set (Sig N)} (u v : ℤ → Sig N) (r : Row) (a b : State n d)
    (hf : (fun _ => false) ∈ A) (hu : ∀ i, u i ∈ A) (hv : ∀ i, v i ∈ A) :
    Build A {edgeSignal u v r a b} ((2*n+1)^(2*d)*2) := by
  apply relax (bigOR (testDose u v r a b) 1 (build_dose u v r a b hf hu hv) hf) le_rfl _ (by rw [choice_card])
  rintro g (hg : g = edgeSignal u v r a b)
  rw [hg]
  apply Set.mem_singleton_iff.mpr
  funext x
  apply Bool.eq_iff_iff.mpr
  simp [edgeSignal]

theorem testDose_spec {N n d} (u v : ℤ → Sig N) (r : Row) (a b : State n d)
    (c : Choice n d) (x : Input N)
    (hu : ∀ j, u j x = true ↔ j = (match r with | .diag _ k | .close k | .skew _ _ k _ => k))
    (hv : ∀ j, v j x = true ↔ j = (match r with | .skew _ _ _ k => k | _ => 0)) :
    testDose u v r a b c x = true ↔ Credit r a.1 b.1 c ∧ Moves r a b c := by
  by_cases hm : Moves r a b c
  · cases r with
    | diag j z =>
      have ui (i : ℤ) : u i x = true ↔ i=z := hu i
      by_cases h : b.1.val=pos c <;> simp [testDose,hm,Credit,h,ui]
    | close z =>
      have ui (i : ℤ) : u i x = true ↔ i=z := hu i
      by_cases h : b.1.val=0 <;> simp [testDose,hm,Credit,h,ui]
    | skew rr bb k l =>
      have ui (i : ℤ) : u i x = true ↔ i=k := hu i
      have vi (i : ℤ) : v i x = true ↔ i=l := hv i
      by_cases h : a.1.val=0 <;> by_cases h' : b.1.val=0 <;>
        simp [testDose,hm,Credit,h,h',an,ui,vi] <;> omega
  · simp [testDose,hm]

theorem edge_exact {N n d} (u v : ℤ → Sig N) (r : Row) (a b : State n d) (x : Input N)
    (hu : ∀ j, u j x = true ↔ j = (match r with | .diag _ k | .close k | .skew _ _ k _ => k))
    (hv : ∀ j, v j x = true ↔ j = (match r with | .skew _ _ _ k => k | _ => 0)) :
    edgeSignal u v r a b x = step r a b := by
  apply Bool.eq_iff_iff.mpr
  simp only [edgeSignal,step,decide_eq_true_eq]
  exact exists_congr fun c => testDose_spec u v r a b c x hu hv

def lookup {n} (b : ChargeIx n → Sig (countLen n)) (q : Width n) (atOrder : Order n)
    (amount : ℤ) : Sig (countLen n) :=
  let k := (atOrder.val : ℤ)*amount
  if h : -(Bcap n : ℤ) ≤ k ∧ k ≤ Bcap n then
    b (q,atOrder,⟨(k+Bcap n).toNat,by omega⟩)
  else fun _ => false

theorem lookup_mem {n} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (q : Width n) (m : Order n) (z : ℤ) : lookup b q m z ∈ layoutBasis a b := by
  dsimp only [lookup]; split
  · exact Or.inr (Or.inr ⟨_,rfl⟩)
  · exact Or.inl (Or.inr (Or.inl rfl))

theorem lookup_physical {n} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (x : Input (countLen n)) (σ : Equiv.Perm (Fin n)) (p : Pins n) (m : Order n)
    (hu : uniqueRows a b x) (hfit : fitsSignals a b x σ p)
    (w : ℕ × ℕ) (hw : GoodPair w) (hm : m.val = arcCode (stride n) w)
    (hm0 : 0 < m.val) (z : ℤ) :
    lookup b (qIndex p) m z x = true ↔ z = imbalance (arcList σ p) w := by
  have actual : charge (stride n) (arcList σ p) m.val = (m.val : ℤ)*imbalance (arcList σ p) w := by
    rw [hm]; exact bivariate_charge σ p w hw
  have bound := abs_le.mp (arc_mag σ p m)
  have hz := signed_arcSlot σ p m
  have nz : (m.val : ℤ) ≠ 0 := by exact_mod_cast hm0.ne'
  dsimp only [lookup]
  split
  · rename_i h
    let slot : Zslot n := ⟨((m.val : ℤ)*z+Bcap n).toNat,by omega⟩
    have sv : signed slot = (m.val : ℤ)*z := by dsimp [signed,slot]; omega
    change b (qIndex p,m,slot) x = true ↔ _
    constructor
    · intro yes
      have eq := hu.2 (qIndex p) m slot (arcSlot σ p m) yes (hfit.2 m)
      exact mul_left_cancel₀ nz (sv.symm.trans ((congrArg (signed (n:=n)) eq).trans (hz.trans actual)))
    · intro eq
      have ids : slot = arcSlot σ p m := by
        apply Fin.ext
        unfold signed at sv hz
        rw [eq,← actual] at sv
        omega
      rw [ids]; exact hfit.2 m
  · rename_i bad
    constructor
    · intro h; cases h
    · rintro rfl; exact (bad (actual ▸ bound)).elim

theorem bundle_inj {r b p m q l : ℕ} (h : bundle r b p m = bundle r b q l) : p=q ∧ m=l := by
  have h2 := congrArg (fun L => tally L 2) h
  have h3 := congrArg (fun L => tally L 3) h
  change tally (bundle r b p m) 2 = tally (bundle r b q l) 2 at h2
  change tally (bundle r b p m) 3 = tally (bundle r b q l) 3 at h3
  rw [(bundle_sizes ..).1,(bundle_sizes ..).1] at h2
  rw [(bundle_sizes ..).2,(bundle_sizes ..).2] at h3
  omega

theorem guard_unique {N n d} (u v : ℤ → Sig N) (r : Row) (a b : State n d) (c f : Choice n d)
    (hc : Moves r a b c) (hf : Moves r a b f) : testDose u v r a b c = testDose u v r a b f := by
  have h := packet_unique r hc hf
  have same (R B : ℕ) (e : ∀ i, bundle R B (c i).1.val (c i).2.val = bundle R B (f i).1.val (f i).2.val) :
      c=f := by
    funext i
    obtain ⟨hp,hm⟩ := bundle_inj (e i)
    exact Prod.ext (Fin.ext hp) (Fin.ext hm)
  cases r with
  | diag j z => rw [same j j h]
  | skew r b z w => rw [same r b h]
  | close z => simp [testDose,hc,hf]

theorem one_gate_edge {N n d} {A : Set (Sig N)} (u v : ℤ → Sig N) (r : Row) (a b : State n d)
    (hf : (fun _ => false) ∈ A) (hu : ∀ i, u i ∈ A) (hv : ∀ i, v i ∈ A) :
    Build A {edgeSignal u v r a b} 1 := by
  by_cases h : ∃ c : Choice n d, Moves r a b c
  · obtain ⟨c,hc⟩ := h
    have eq : edgeSignal u v r a b = testDose u v r a b c := by
      funext x
      apply Bool.eq_iff_iff.mpr
      simp only [edgeSignal,decide_eq_true_eq]
      constructor
      · rintro ⟨f,yes⟩
        by_cases hm : Moves r a b f
        · rwa [guard_unique u v r a b f c hm hc] at yes
        · simp [testDose,hm] at yes
      · exact fun yes => ⟨c,yes⟩
    rw [eq]
    exact build_dose u v r a b hf hu hv c
  · have eq : edgeSignal u v r a b = fun _ => false := by
      funext x
      apply Bool.eq_false_iff.mpr
      intro yes'
      change decide (∃ c : Choice n d, testDose u v r a b c x = true) = true at yes'
      obtain ⟨c,yes⟩ := of_decide_eq_true yes'
      have hm : ¬Moves r a b c := fun hc => h ⟨c,hc⟩
      simp [testDose,hm] at yes
    rw [eq]
    exact relax (idle (Set.singleton_subset_iff.mpr hf)) le_rfl le_rfl (by decide)

set_option maxHeartbeats 600000 in
theorem all_edge_budget {n d N T : ℕ} {A : Set (Sig N)} (rows : Fin T → Row)
    (u v : Fin T → ℤ → Sig N) (hf : (fun _ => false)∈A)
    (hu : ∀ t z, u t z ∈ A) (hv : ∀ t z, v t z ∈ A) (ht : T≤(n+2)^4) :
    Build A (Set.range (fun k : Fin T × State n d × State n d =>
      edgeSignal (u k.1) (v k.1) (rows k.1) k.2.1 k.2.2)) ((n+2)^(20*(d+1))) := by
  let F (k : Fin T × State n d × State n d) := edgeSignal (u k.1) (v k.1) (rows k.1) k.2.1 k.2.2
  have each (k) : Build A {F k} 1 := one_gate_edge _ _ _ _ _ hf (hu _) (hv _)
  apply relax (allG F 1 each) le_rfl le_rfl
  change Fintype.card (Fin T × State n d × State n d)*1 ≤ (n+2)^(20*(d+1))
  rw [Nat.mul_one,Fintype.card_prod,Fintype.card_fin,Fintype.card_prod]
  calc T*(Fintype.card (State n d)*Fintype.card (State n d)) ≤ (n+2)^4*((n+2)^(8*(d+1))*(n+2)^(8*(d+1))) :=
         Nat.mul_le_mul ht (Nat.mul_le_mul (state_budget n d) (state_budget n d))
       _ = (n+2)^(4+(8*(d+1)+8*(d+1))) := by rw [pow_add,pow_add]
       _ ≤ (n+2)^(20*(d+1)) := Nat.pow_le_pow_right (by omega) (by omega)

end PEqualNP.Outside.L_pcx_386.Allocation

namespace PEqualNP.Outside.L_pcx_386.Allocation

open PEqualNP.Outside.L_pcx_386.Core
open PEqualNP.Outside.L_pcx_386.Core.Compiler.Build

theorem lookup_literal {n} (b : ChargeIx n → Sig (countLen n)) (q : Width n)
    (σ : Equiv.Perm (Fin n)) (p : Pins n) (m : Order n) (z : ℤ)
    (he : charge (stride n) (arcList σ p) m.val = (m.val : ℤ)*z) :
    lookup b q m z = b (q,m,arcSlot σ p m) := by
  have hz := signed_arcSlot σ p m
  have bound := abs_le.mp (arc_mag σ p m)
  have h : -(Bcap n : ℤ) ≤ (m.val : ℤ)*z ∧ (m.val : ℤ)*z ≤ Bcap n := he ▸ bound
  simp only [lookup,dite_eq_left h]
  congr 3
  apply Fin.ext
  change ((m.val : ℤ)*z + Bcap n).toNat = (arcSlot σ p m).val
  unfold signed at hz
  rw [he] at hz
  omega

def Supported (n k : ℕ) := ∃ w, GoodPair w ∧ k = arcCode (stride n) w

theorem off_charge {n} (σ : Equiv.Perm (Fin n)) (p : Pins n) (m : ℕ) (h : ¬Supported n m) :
    charge (stride n) (arcList σ p) m = 0 := by
  obtain ⟨_,rfl,_,ok,_⟩ := exists_arc_factors σ p
  have miss (bag : Multiset (ℕ × ℕ)) (good : ∀ w ∈ bag, GoodPair w) :
      (bag.map (arcCode (stride n))).count m = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro hm
    obtain ⟨w,hw,eq⟩ := Multiset.mem_map.mp hm
    exact h ⟨w,good w hw,eq.symm⟩
  unfold charge numer denom
  rw [miss _ (numPairs_good _ ok),miss _ (denPairs_good _ ok)]
  simp

noncomputable def zeroMask {n} (P : Order n → Prop) (b : ChargeIx n → Sig (countLen n)) (q : Width n) : Sig (countLen n) := by
  classical
  exact fun x => decide (∀ m : Order n, ¬P m → lookup b q m 0 x = true)

theorem zero_mask_build {n} (P : Order n → Prop) (a : Width n → Sig (countLen n))
    (b : ChargeIx n → Sig (countLen n)) (q : Width n) :
    Build (layoutBasis a b) {zeroMask P b q} (radius n+1) := by
  classical
  let g (m : Order n) : Sig (countLen n) := if P m then fun _ => true else lookup b q m 0
  have ht : (fun _ => true) ∈ layoutBasis a b := Or.inl (Or.inr (Or.inr rfl))
  have h (m) : Build (layoutBasis a b) {g m} 0 := by
    apply idle
    apply Set.singleton_subset_iff.mpr
    by_cases hm : P m
    · simpa [g,hm] using ht
    · simpa [g,hm] using lookup_mem a b q m 0
  have eq : zeroMask P b q = fun x => decide (∀ m : Order n, g m x = true) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [zeroMask,decide_eq_true_eq]
    constructor
    · intro yes m
      by_cases hm : P m
      · simp [g,hm]
      · simpa only [g,ite_eq_right hm] using yes m hm
    · intro yes m hm
      simpa [g,hm] using yes m
  rw [eq]
  simpa only [Order,Fintype.card_fin,Nat.zero_add,Nat.mul_one] using bigAND g 0 h ht (fun _ => inferInstance)

noncomputable def ZeroTail {n} (b : ChargeIx n → Sig (countLen n)) (q : Width n) : Sig (countLen n) :=
  zeroMask (fun m => Supported n m.val) b q

theorem zero_tail_build {n} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n)) (q : Width n) :
    Build (layoutBasis a b) {ZeroTail b q} (radius n+1) := zero_mask_build _ a b q

theorem arbitrary_rows {n} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (x : Input (countLen n)) (σ : Equiv.Perm (Fin n)) (p : Pins n) :
    fitsSignals a b x σ p ↔ a (qIndex p) x = true ∧ ZeroTail b (qIndex p) x = true ∧
      ∀ (m : Order n) (w : ℕ × ℕ), GoodPair w → m.val = arcCode (stride n) w →
        lookup b (qIndex p) m (imbalance (arcList σ p) w) x = true := by
  classical
  simp only [ZeroTail,zeroMask,decide_eq_true_eq]
  have constant (m : Order n) (h : ¬Supported n m.val) :=
    lookup_literal b (qIndex p) σ p m 0 (by rw [off_charge σ p m h,mul_zero])
  have covered (m : Order n) (w : ℕ × ℕ) (hw : GoodPair w) (hm : m.val = arcCode (stride n) w) :=
    lookup_literal b (qIndex p) σ p m (imbalance (arcList σ p) w) (by rw [hm]; exact bivariate_charge σ p w hw)
  constructor
  · intro yes
    exact ⟨yes.1,fun m h => by rw [constant m h]; exact yes.2 m,
      fun m w hw hm => by rw [covered m w hw hm]; exact yes.2 m⟩
  · rintro ⟨mass,absent,good⟩
    refine ⟨mass,fun m => ?_⟩
    by_cases hm : Supported n m.val
    · obtain ⟨w,hw,eq⟩ := hm
      simpa only [covered m w hw eq] using good m w hw eq
    · simpa only [constant m hm] using absent m hm

end PEqualNP.Outside.L_pcx_386.Allocation

namespace PEqualNP.Outside.L_pcx_386.Allocation

open PEqualNP.Outside.L_pcx_386.Core
open PEqualNP.Outside.L_pcx_386.Core.Compiler.Build

inductive StageKey where
  | diag (j : ℕ)
  | finishChain (j : ℕ)
  | skew (r b : ℕ)
deriving DecidableEq

def samples : StageKey → List (ℕ × ℕ)
  | .diag j | .finishChain j => [(j,j)]
  | .skew r b => [(r,b),twicePair (r,b)]

def chain (n : ℕ) : ℕ → ℕ → List StageKey
  | 0,j => [.finishChain j]
  | t+1,j => if j≤n then .diag j :: chain n t (2*j) else [.finishChain j]

def catalog (n : ℕ) : List StageKey :=
  ((List.range n).flatMap fun i => [.skew i (i+1),.skew (i+1) i]) ++
  ((List.range (n+1)).flatMap fun o => if Odd o then chain n (n+1) o else [])

def Touch (L : List StageKey) (w : ℕ × ℕ) : Prop := ∃ k ∈ L, w ∈ samples k

theorem first_touch (n t j : ℕ) : Touch (chain n t j) (j,j) := by
  cases t with
  | zero => exact ⟨.finishChain j,by simp [chain],by simp [samples]⟩
  | succ t =>
    by_cases h : j≤n
    · exact ⟨.diag j,by simp [chain,h],by simp [samples]⟩
    · exact ⟨.finishChain j,by simp [chain,h],by simp [samples]⟩

theorem chain_hits (n a t j : ℕ) (ht : a<t) (hj : 2^a*j≤n) :
    .diag (2^a*j) ∈ chain n t j ∧ Touch (chain n t j) (2*(2^a*j),2*(2^a*j)) := by
  induction a generalizing t j with
  | zero =>
    cases t with
    | zero => omega
    | succ t =>
      simp only [pow_zero,one_mul] at hj ⊢
      obtain ⟨k,hk,hw⟩ := first_touch n t (2*j)
      exact ⟨by simp [chain,hj],k,by simp [chain,hj,hk],hw⟩
  | succ a ih =>
    cases t with
    | zero => omega
    | succ t =>
      have eq : 2^(a+1)*j = 2^a*(2*j) := by rw [pow_succ,Nat.mul_assoc]
      have hj' : j≤n := (Nat.le_mul_of_pos_left _ (by positivity : 0<2^(a+1))).trans hj
      rw [eq] at hj ⊢
      obtain ⟨hm,k,hk,hw⟩ := ih t (2*j) (by omega) hj
      exact ⟨by simp [chain,hj',hm],k,by simp [chain,hj',hk],hw⟩

def Raw (n : ℕ) (w : ℕ × ℕ) : Prop :=
  0<w.1+w.2 ∧ w.1≤n ∧ w.2≤n ∧ w.1≤w.2+1 ∧ w.2≤w.1+1

theorem catalog_hits {n : ℕ} {w : ℕ × ℕ} (h : Raw n w) :
    Touch (catalog n) w ∧ Touch (catalog n) (twicePair w) := by
  obtain ⟨r,b⟩ := w
  obtain ⟨hp,hr,hb,hrb,hbr⟩ := h
  dsimp at hp hr hb hrb hbr
  have skew {j : ℕ} (hj : j<n) (t : StageKey) (ht : t∈[.skew j (j+1),.skew (j+1) j]) :
      t ∈ catalog n := List.mem_append_left _ (List.mem_flatMap.mpr ⟨j,List.mem_range.mpr hj,ht⟩)
  rcases (show r=b ∨ b=r+1 ∨ r=b+1 by omega) with rfl | rfl | rfl
  · obtain ⟨o,ho,odd,k,hk,e⟩ := dyadic_cover (by omega : 0<r) hr
    obtain ⟨hm,l,hl,hpair⟩ := chain_hits n k (n+1) o (by omega) (e ▸ hr)
    have lift {l : StageKey} (hl : l ∈ chain n (n+1) o) : l∈catalog n := by
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      exact ⟨o,List.mem_range.mpr (by omega),by simpa [odd] using hl⟩
    rw [e]
    exact ⟨⟨_,lift hm,by simp [samples]⟩,l,lift hl,hpair⟩
  · have hm := skew (j:=r) (by omega) (.skew r (r+1)) (by simp)
    exact ⟨⟨_,hm,by simp [samples]⟩,_,hm,by simp [samples]⟩
  · have hm := skew (j:=b) (by omega) (.skew (b+1) b) (by simp)
    exact ⟨⟨_,hm,by simp [samples]⟩,_,hm,by simp [samples]⟩

theorem physical_raw {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pins n) (v : Arc) (hv : v∈arcList σ p) :
    Raw n (v.1,v.2.1) := by
  classical
  obtain ⟨_,rfl,_,hshape,_⟩ := exists_arc_factors σ p
  obtain ⟨hp,h1,h2⟩ := hshape v hv
  have perColor (c : Finset (Bool × Fin n)) (b : Bool) : (c.filter (fun v => v.1=b)).card ≤ n := by
    let s := c.filter (fun v => v.1=b)
    have inj : Set.InjOn Prod.snd (↑s : Set (Bool × Fin n)) := by
      intro a ha f hf eq
      exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hf).2.symm) eq
    calc s.card = (s.image Prod.snd).card := (Finset.card_image_of_injOn inj).symm
         _ ≤ Fintype.card (Fin n) := Finset.card_le_univ _
         _ = n := Fintype.card_fin n
  refine ⟨hp,?_,?_,h1,h2⟩ <;> (unfold arcList at hv; obtain ⟨c,_,rfl⟩ := List.mem_map.mp hv)
  · exact perColor c.1 false
  · exact perColor c.1 true

theorem sampled_factors {n} (L : List Arc) (h : ∀ a ∈ L, Raw n (a.1,a.2.1)) :
    (∀ w ∈ numPairs L, Touch (catalog n) w) ∧ (∀ w ∈ denPairs L, Touch (catalog n) w) := by
  induction L with
  | nil => simp [numPairs,denPairs]
  | cons a L ih =>
    obtain ⟨r,b,s⟩ := a
    obtain ⟨u,v⟩ := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    obtain ⟨hs,hd⟩ := catalog_hits (h (r,b,s) List.mem_cons_self)
    cases s <;> simp only [numPairs,denPairs,Multiset.mem_cons] <;> grind [twicePair]

def Scheduled (n m : ℕ) : Prop := ∃ w, Touch (catalog n) w ∧ m=arcCode (stride n) w

theorem unseen_zero {n} (σ : Equiv.Perm (Fin n)) (p : Pins n) (m : ℕ) (h : ¬Scheduled n m) :
    charge (stride n) (arcList σ p) m = 0 := by
  have pair := sampled_factors _ (physical_raw σ p)
  have miss (bag : Multiset (ℕ × ℕ)) (ok : ∀ w∈bag, Touch (catalog n) w) :
      (bag.map (arcCode (stride n))).count m = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro hm
    obtain ⟨w,hw,eq⟩ := Multiset.mem_map.mp hm
    exact h ⟨w,ok w hw,eq.symm⟩
  unfold charge numer denom
  rw [miss _ pair.1,miss _ pair.2]
  simp

theorem chain_length (n t j : ℕ) : (chain n t j).length ≤ t+1 := by
  induction t generalizing j with
  | zero => simp [chain]
  | succ t ih => by_cases h : j≤n <;> simp [chain,h,ih]

theorem flat_bound {α β} (L : List α) (f : α → List β) (k : ℕ) (h : ∀ a, (f a).length ≤ k) :
    (L.flatMap f).length ≤ L.length*k := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]; grind

theorem catalog_length (n : ℕ) : (catalog n).length ≤ (n+2)^4 := by
  have sk := flat_bound (List.range n) (fun i => [StageKey.skew i (i+1),.skew (i+1) i]) 2 (by simp)
  have dg := flat_bound (List.range (n+1)) (fun o => if Odd o then chain n (n+1) o else []) (n+2)
    (by intro o; split <;> first | exact chain_length .. | simp)
  simp only [catalog,List.length_append,List.length_range] at *
  nlinarith [Nat.zero_le (n^3),Nat.zero_le (n^4)]

def KeyOK (n : ℕ) : StageKey → Prop
  | .diag j => 0<j ∧ j≤n
  | .finishChain j => n<j ∧ j≤2*n ∧ Even j
  | .skew r b => r≤n ∧ b≤n ∧ (r+1=b ∨ b+1=r)

theorem chain_ok (n t j : ℕ) (hj : 0<j) (hw : j≤2*n) (ht : n<j+t) (hdiv : n<j → Even j) :
    ∀ k ∈ chain n t j, KeyOK n k := by
  induction t generalizing j with
  | zero =>
    intro k hk
    have eq : k=.finishChain j := by simpa [chain] using hk
    exact eq ▸ ⟨by omega,hw,hdiv (by omega)⟩
  | succ t ih =>
    intro k hk
    by_cases h : j≤n
    · simp only [chain,ite_eq_left h,List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact ⟨hj,h⟩
      · exact ih (2*j) (by omega) (by omega) (by omega) (fun _ => ⟨j,by omega⟩) k hk
    · have eq : k=.finishChain j := by simpa [chain,h] using hk
      exact eq ▸ ⟨by omega,hw,hdiv (by omega)⟩

theorem catalog_ok {n k} (h : k∈catalog n) : KeyOK n k := by
  rcases List.mem_append.mp h with hs | hd
  · obtain ⟨j,hj,hk⟩ := List.mem_flatMap.mp hs
    have hj' := List.mem_range.mp hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl <;> exact ⟨by omega,by omega,by omega⟩
  · obtain ⟨o,ho,hk⟩ := List.mem_flatMap.mp hd
    have ho' := List.mem_range.mp ho
    by_cases hodd : Odd o
    · obtain ⟨l,hl⟩ := hodd
      exact chain_ok n (n+1) o (by omega) (by omega) (by omega) (by omega) k (by simpa [show Odd o from ⟨l,hl⟩] using hk)
    · simp [hodd] at hk

theorem key_sample {n k w} (hk : KeyOK n k) (hw : w∈samples k) :
    GoodPair w ∧ w.1≤2*n ∧ w.2≤2*n := by
  cases k with
  | diag j =>
    obtain ⟨_,_⟩ := hk
    obtain rfl : w=(j,j) := by simpa [samples] using hw
    exact ⟨goodPair_of_arc (by omega) (by omega) (by omega),by omega,by omega⟩
  | finishChain j =>
    obtain ⟨_,_,_⟩ := hk
    obtain rfl : w=(j,j) := by simpa [samples] using hw
    exact ⟨goodPair_of_arc (by omega) (by omega) (by omega),by omega,by omega⟩
  | skew r b =>
    obtain ⟨_,_,_⟩ := hk
    simp only [samples,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨goodPair_of_arc (by omega) (by omega) (by omega),by omega,by omega⟩
    · exact ⟨goodPair_double_of_arc (by omega) (by omega) (by omega),by dsimp [twicePair]; omega,by dsimp [twicePair]; omega⟩

def sampleOrder (n : ℕ) (w : ℕ × ℕ) : Order n :=
  ⟨min (arcCode (stride n) w) (radius n),Nat.lt_succ_of_le (min_le_right ..)⟩

theorem sample_order {n k w} (hk : k∈catalog n) (hw : w∈samples k) :
    (sampleOrder n w).val=arcCode (stride n) w := by
  obtain ⟨_,hr,hb⟩ := key_sample (catalog_ok hk) hw
  apply min_eq_left
  unfold arcCode radius
  nlinarith [Nat.mul_le_mul_left (stride n) hb]

def Asked {n} (b : ChargeIx n → Sig (countLen n)) (q : Width n) (x : Input (countLen n))
    (z : ℕ × ℕ → ℤ) := ∀ k ∈ catalog n, ∀ w ∈ samples k, lookup b q (sampleOrder n w) (z w) x = true

theorem arbitrary_scheduled {n} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (x : Input (countLen n)) (σ : Equiv.Perm (Fin n)) (p : Pins n) :
    fitsSignals a b x σ p ↔ a (qIndex p) x = true ∧
      zeroMask (fun m => Scheduled n m.val) b (qIndex p) x = true ∧
      Asked b (qIndex p) x (imbalance (arcList σ p)) := by
  classical
  simp only [zeroMask,decide_eq_true_eq]
  have gone (m : Order n) (h : ¬Scheduled n m.val) :=
    lookup_literal b (qIndex p) σ p m 0 (by rw [unseen_zero σ p m h,mul_zero])
  have seen (k) (hk : k∈catalog n) (w) (hw : w∈samples k) :=
    lookup_literal b (qIndex p) σ p (sampleOrder n w) (imbalance (arcList σ p) w)
      (by rw [sample_order hk hw]; exact bivariate_charge σ p w (key_sample (catalog_ok hk) hw).1)
  constructor
  · intro yes
    exact ⟨yes.1,fun m h => by rw [gone m h]; exact yes.2 m,
      fun k hk w hw => by rw [seen k hk w hw]; exact yes.2 _⟩
  · rintro ⟨mass,absent,yes⟩
    refine ⟨mass,fun m => ?_⟩
    by_cases h : Scheduled n m.val
    · obtain ⟨w,⟨k,hk,hw⟩,eq⟩ := h
      obtain rfl : m=sampleOrder n w := Fin.ext (eq.trans (sample_order hk hw).symm)
      simpa only [seen k hk w hw] using yes k hk w hw
    · simpa only [gone m h] using absent m h

end PEqualNP.Outside.L_pcx_386.Allocation

namespace PEqualNP.Outside.L_pcx_386_aux

namespace Compiler

namespace GateBridge

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

def Legal (op : GateOp) (arity : ℕ) : Prop :=
  ((op = .and ∨ op = .or) ∧ arity = 2) ∨ (op = .not ∧ arity = 1)

variable {α : Type*}

def Scheduled (n : ℕ) (F : α → (Fin n → Bool) → Bool) (k : ℕ) (S : Set α) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack n ⟨gs, 0⟩ ∧ (∀ g ∈ gs, Legal g.op g.inputs.length) ∧
    ∀ a ∈ S, ∃ i : ℕ, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x

theorem wireLength (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length + C.gates.length := by
  rcases C with ⟨gs, out⟩
  change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    w).length = w.length + gs.length
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem start {n : ℕ} {F : α → (Fin n → Bool) → Bool}
    (input : Fin n → α) (h : ∀ i x, F (input i) x = x i) :
    Scheduled n F 0 (Set.range input) := by
  refine ⟨[], rfl, ?_, ?_, ?_⟩
  · simp [ReadsBack]
  · simp
  · intro a ha
    obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
    refine ⟨i.val, by simpa using i.isLt, fun x => ?_⟩
    change (List.ofFn x).getD i.val false = F (input i) x
    rw [List.getD_eq_getElem _ _ (by simpa using i.isLt), List.getElem_ofFn, h i x]

theorem restrict {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S T : Set α}
    (h : Scheduled n F k S) (hsub : T ⊆ S) : Scheduled n F k T := by
  obtain ⟨gs, hs, hr, hf, hw⟩ := h
  exact ⟨gs, hs, hr, hf, fun a ha => hw a (hsub ha)⟩

theorem realizeDeps {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : ℕ, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x)
    (deps : List α) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List ℕ, is.length = deps.length ∧ (∀ i ∈ is, i < n + k) ∧
      ∀ x : Fin n → Bool,
        is.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) =
          deps.map (fun a => F a x) := by
  induction deps with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons a deps ih =>
    obtain ⟨i, hi, hval⟩ := hw a (hdeps a List.mem_cons_self)
    obtain ⟨is, hlen, hbound, hvals⟩ := ih (fun b hb => hdeps b (List.mem_cons_of_mem a hb))
    refine ⟨i :: is, by simp [hlen], ?_, fun x => ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hbound j hj
    · simp only [List.map_cons, hval x, hvals x]

theorem push {n k : ℕ} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    (h : Scheduled n F k S) (op : GateOp) (deps : List α) (out : α)
    (hop : Legal op deps.length) (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, F out x = op.eval (deps.map fun a => F a x)) :
    Scheduled n F (k + 1) (insert out S) := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨is, his, hbound, hvalues⟩ := realizeDeps hw deps hdeps
  let g : Gate := ⟨op, is⟩
  have hlength (x : Fin n → Bool) :
      ((Circuit.mk gs 0).wires (List.ofFn x)).length = n + k := by
    rw [wireLength]
    simpa using congrArg (n + ·) hgs
  have hsnoc (x : Fin n → Bool) :
      (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [F out x] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (Circuit.mk gs 0).wires (List.ofFn x) ++
      [op.eval (is.map fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)] =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [F out x]
    rw [hvalues x, hval x]
  refine ⟨gs ++ [g], by simp [hgs], ?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (gs ++ [g]).length at hj
    change i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hr j hj' i hi
    · have heq : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      have hi' : i ∈ is := by simpa [g] using hi
      simpa [hgs] using hbound i hi'
  · intro g' hg'
    change g' ∈ gs ++ [g] at hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hf g' hg'
    · have heq : g' = g := List.mem_singleton.mp hg'
      subst g'
      change Legal op is.length
      simpa only [his] using hop
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · refine ⟨n + k, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append_right _ _ _ _ (by simp [hlength x])]
      simp [hlength x]
    · obtain ⟨i, hi, hval'⟩ := hw a ha
      refine ⟨i, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by simpa [hlength x] using hi), hval' x]

end GateBridge

namespace Build

open PEqualNP.CircuitLowerBounds

variable {n : Nat}
abbrev Sig (n : Nat) := (Fin n → Bool) → Bool
def Build (A B : Set (Sig n)) (b : Nat) : Prop :=
  True ∧ (∀ {m S}, GateBridge.Scheduled n id m S → A ⊆ S →
    ∃ c ≤ b, GateBridge.Scheduled n id (m+c) (S ∪ B))

theorem Build.run {A B : Set (Sig n)} {b m S} (H : Build A B b)
    (HS : GateBridge.Scheduled n id m S) (hA : A ⊆ S) :
    ∃ c ≤ b, GateBridge.Scheduled n id (m+c) (S ∪ B) := H.2 HS hA

theorem idle {A B : Set (Sig n)} (h : B ⊆ A) : Build A B 0 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨0, Nat.le_refl _, ?_⟩
  simpa [Set.union_eq_left.mpr (h.trans hA)] using HS

theorem relax {A B C D : Set (Sig n)} {b d : Nat}
    (H : Build A B b) (hA : A ⊆ C) (hB : D ⊆ B) (h : b ≤ d) : Build C D d := by
  refine ⟨trivial, ?_⟩
  intro m S HS hC
  obtain ⟨c,hc,HS'⟩ := H.run HS (hA.trans hC)
  exact ⟨c,hc.trans h,GateBridge.restrict HS' (Set.union_subset_union le_rfl hB)⟩

theorem seq {A B C : Set (Sig n)} {b c : Nat}
    (H : Build A B b) (J : Build (A ∪ B) C c) : Build A (B ∪ C) (b+c) := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  obtain ⟨d,hd,K⟩ := H.run HS hA
  obtain ⟨e,he,K'⟩ := J.run K (Set.union_subset_union hA le_rfl)
  exact ⟨d+e,Nat.add_le_add hd he,by simpa [Nat.add_assoc,Set.union_assoc] using K'⟩

theorem one {A : Set (Sig n)} (op : GateOp) (deps : List (Sig n))
    (hop : GateBridge.Legal op deps.length)
    (hd : ∀ g ∈ deps, g ∈ A) (f : Sig n)
    (hv : ∀ x, f x = op.eval (deps.map fun g => g x)) : Build A {f} 1 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨1,le_rfl,?_⟩
  have h := GateBridge.push HS op deps f hop (fun g hg => hA (hd g hg)) hv
  rw [Set.insert_eq] at h
  exact GateBridge.restrict h (by intro g hg; exact hg.elim Or.inr Or.inl)

def an (f g : Sig n) : Sig n := fun x => f x && g x
def or (f g : Sig n) : Sig n := fun x => f x || g x
def nt (f : Sig n) : Sig n := fun x => !f x
def xo (f g : Sig n) : Sig n := fun x => xor (f x) (g x)

theorem andG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {an f g} 1 :=
  one .and [f,g] (by simp [GateBridge.Legal]) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, an])

theorem orG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {or f g} 1 :=
  one .or [f,g] (by simp [GateBridge.Legal]) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, or])

theorem notG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) : Build A {nt f} 1 :=
  one .not [f] (by simp [GateBridge.Legal]) (by simpa using hf) _ (by simp [GateOp.eval, nt])

theorem xorG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {xo f g} 4 := by
  have he : xo f g = an (or f g) (nt (an f g)) := by
    funext x
    change xor (f x) (g x) = ((f x || g x) && !(f x && g x))
    cases f x <;> cases g x <;> rfl
  rw [he]
  have h₁ := andG hf hg
  have h₂ := orG (A := A ∪ {an f g}) (Or.inl hf) (Or.inl hg)
  have h₃ := notG (A := A ∪ ({an f g} ∪ {or f g})) (f := an f g) (by simp)
  have h₄ := andG (A := A ∪ (({an f g} ∪ {or f g}) ∪ {nt (an f g)}))
    (f := or f g) (g := nt (an f g)) (by simp) (by simp)
  exact relax (seq (seq (seq h₁ h₂) h₃) h₄) le_rfl (by simp) le_rfl

theorem topological {α : Type*} [DecidableEq α] {A : Set (Sig n)}
    (F : α → Sig n) (rank cost : α → Nat) (s : Finset α)
    (H : ∀ i ∈ s, Build (A ∪ {f | ∃ j ∈ s, rank j < rank i ∧ f = F j}) {F i} (cost i)) :
    Build A {f | ∃ i ∈ s, f = F i} (∑ i ∈ s, cost i) := by
  classical
  induction s using Finset.strongInduction with
  | H s IH =>
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi, himax⟩ := Finset.exists_max_image s rank hs
      have Hsub : s.erase i ⊂ s := Finset.erase_ssubset hi
      have hstep (j : α) (hj : j ∈ s.erase i) (l : α) (hl : l ∈ s)
          (hlt : rank l < rank j) : l ∈ s.erase i := by
        refine Finset.mem_erase.mpr ⟨?_,hl⟩
        intro heq
        subst l
        exact (Nat.not_lt_of_ge (himax j (Finset.mem_of_mem_erase hj))) hlt
      have Hs := IH (s.erase i) Hsub fun j hj =>
        relax (H j (Finset.mem_of_mem_erase hj))
          (by rintro f (hf | ⟨l,hl,hlt,rfl⟩)
              · exact Or.inl hf
              · exact Or.inr ⟨l,hstep j hj l hl hlt,hlt,rfl⟩) le_rfl le_rfl
      have Hi := relax (H i hi) (C := A ∪ {f | ∃ j ∈ s.erase i, f = F j})
        (by rintro f (hf | ⟨j,hj,hlt,rfl⟩)
            · exact Or.inl hf
            · exact Or.inr ⟨j,Finset.mem_erase.mpr ⟨by aesop, hj⟩,rfl⟩) le_rfl le_rfl
      refine relax (seq Hs Hi) le_rfl ?_ ?_
      · rintro f ⟨j,hj,rfl⟩
        by_cases he : j = i
        · exact Or.inr (by simp [he])
        · exact Or.inl ⟨j,Finset.mem_erase.mpr ⟨he,hj⟩,rfl⟩
      · rw [Finset.sum_erase_add _ _ hi]
    · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      exact relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by simp) (by simp)
theorem anyG {A : Set (Sig n)} (xs : List (Sig n))
    (hs : ∀ f ∈ xs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => xs.any (fun f => f x)} xs.length := by
  induction xs with
  | nil =>
    exact idle (Set.singleton_subset_iff.mpr hfalse)
  | cons f xs IH =>
    have H := IH (fun g hg => hs g (List.mem_cons_of_mem f hg))
    have K := orG (A := A ∪ {fun x => xs.any (fun g => g x)})
      (Or.inl (hs f List.mem_cons_self)) (Or.inr rfl)
    exact relax (seq H K) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by simp)

theorem allG {α : Type*} [Fintype α] {A : Set (Sig n)}
    (F : α → Sig n) (c : Nat) (H : ∀ i, Build A {F i} c) :
    Build A (Set.range F) (Fintype.card α*c) := by
  classical
  have K := topological F (fun _ => 0) (fun _ => c) Finset.univ
    (fun i _ => relax (H i) Set.subset_union_left le_rfl le_rfl)
  refine relax (by simpa only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul] using K) le_rfl ?_ le_rfl
  rintro _ ⟨i,rfl⟩
  exact ⟨i,Finset.mem_univ _,rfl⟩

theorem finG {k : Nat} {A : Set (Sig n)} (F : Fin k → Sig n) (c : Nat)
    (H : ∀ i, Build A {F i} c) : Build A (Set.range F) (k*c) := by
  simpa only [Fintype.card_fin] using allG F c H

def inputs (n : Nat) : Set (Sig n) := Set.range (fun i : Fin n => fun v => v i)

def base (n : Nat) : Set (Sig n) := inputs n ∪ {fun _ => false, fun _ => true}

theorem thenG {A B C : Set (Sig n)} {b c : Nat}
    (h : Build A B b) (j : Build (A ∪ B) C c) : Build A C (b+c) :=
  relax (seq h j) le_rfl Set.subset_union_right le_rfl

theorem bothG {A B C : Set (Sig n)} {b c : Nat}
    (h : Build A B b) (j : Build A C c) : Build A (B ∪ C) (b+c) :=
  seq h (relax j Set.subset_union_left le_rfl le_rfl)

theorem loopG {A : Set (Sig n)} (F : Nat → Set (Sig n)) {b c t : Nat}
    (hbase : Build A (F 0) b)
    (hstep : ∀ j, j < t → Build (A ∪ F j) (F (j+1)) c) :
    Build A (F t) (b + t*c) := by
  induction t with
  | zero => simpa only [Nat.zero_mul, Nat.add_zero] using hbase
  | succ t ih =>
    have hprev := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
    refine relax (seq hprev (hstep t (Nat.lt_succ_self t))) le_rfl Set.subset_union_right ?_
    rw [Nat.succ_mul, Nat.add_assoc]

def mx (s f g : Sig n) : Sig n := fun x => if s x then g x else f x

theorem muxG {A : Set (Sig n)} {s f g : Sig n} (hs : s ∈ A) (hf : f ∈ A) (hg : g ∈ A) :
    Build A {mx s f g} 4 := by
  have he : mx s f g = or (an (nt s) f) (an s g) := by
    funext x
    change (if s x then g x else f x) = ((!(s x) && f x) || (s x && g x))
    cases s x <;> cases f x <;> cases g x <;> rfl
  rw [he]
  have h₁ := notG hs
  have h₂ := andG (A := A ∪ {nt s}) (f := nt s) (by simp) (Or.inl hf)
  have h₃ := andG (A := A ∪ ({nt s} ∪ {an (nt s) f}))
    (Or.inl hs) (Or.inl hg)
  have h₄ := orG (A := A ∪ (({nt s} ∪ {an (nt s) f}) ∪ {an s g}))
    (f := an (nt s) f) (g := an s g) (by simp) (by simp)
  exact relax (seq (seq (seq h₁ h₂) h₃) h₄) le_rfl (by simp) le_rfl
theorem everyG {A : Set (Sig n)} (xs : List (Sig n))
    (hs : ∀ f ∈ xs, f ∈ A) (htrue : (fun _ => true) ∈ A) :
    Build A {fun x => xs.all (fun f => f x)} xs.length := by
  induction xs with
  | nil => exact idle (Set.singleton_subset_iff.mpr htrue)
  | cons f xs ih =>
    have H := ih (fun g hg => hs g (List.mem_cons_of_mem f hg))
    have K := andG (A := A ∪ {fun x => xs.all (fun g => g x)})
      (Or.inl (hs f List.mem_cons_self)) (Or.inr rfl)
    exact relax (seq H K) le_rfl Set.subset_union_right (by simp)

abbrev Word (n w : Nat) := Fin w → Sig n

def Available {w : Nat} (A : Set (Sig n)) (v : Word n w) : Prop := ∀ i, v i ∈ A

theorem wordConstG {w : Nat} {A : Set (Sig n)} (v : Fin w → Bool)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A) :
    Build A (Set.range (fun (i : Fin w) (_ : Fin n → Bool) => v i)) 0 := by
  apply idle
  rintro _ ⟨i, rfl⟩
  cases hi : v i
  · simpa only [hi] using hfalse
  · simpa only [hi] using htrue

theorem wordNotG {w : Nat} {A : Set (Sig n)} {v : Word n w} (hv : Available A v) :
    Build A (Set.range (fun i => nt (v i))) w := by
  simpa only [Nat.mul_one] using finG (fun i => nt (v i)) 1 (fun i => notG (hv i))

theorem wordAndG {w : Nat} {A : Set (Sig n)} {v u : Word n w}
    (hv : Available A v) (hu : Available A u) :
    Build A (Set.range (fun i => an (v i) (u i))) w := by
  simpa only [Nat.mul_one] using finG (fun i => an (v i) (u i)) 1 (fun i => andG (hv i) (hu i))

theorem wordOrG {w : Nat} {A : Set (Sig n)} {v u : Word n w}
    (hv : Available A v) (hu : Available A u) :
    Build A (Set.range (fun i => or (v i) (u i))) w := by
  simpa only [Nat.mul_one] using finG (fun i => or (v i) (u i)) 1 (fun i => orG (hv i) (hu i))
theorem wordMuxG {w : Nat} {A : Set (Sig n)} {s : Sig n} {v u : Word n w}
    (hs : s ∈ A) (hv : Available A v) (hu : Available A u) :
    Build A (Set.range (fun i => mx s (v i) (u i))) (w*4) :=
  finG _ 4 (fun i => muxG hs (hv i) (hu i))
def listInput (x : List Bool) (hx : x.length = n) : Fin n → Bool :=
  fun i => x.get (i.cast hx.symm)

theorem ofFn_listInput (x : List Bool) (hx : x.length = n) :
    List.ofFn (listInput x hx) = x := by
  subst n
  exact List.ofFn_get x

theorem listInput_getD (x : List Bool) (hx : x.length = n) (i : Fin n) :
    listInput x hx i = x.getD i.val false := by
  rw [List.getD_eq_getElem _ _ (by simpa only [hx] using i.isLt)]
  rfl
theorem relaxKeep {A B C D : Set (Sig n)} {b d : Nat}
    (H : Build A B b) (hA : A ⊆ C) (hB : D ⊆ C ∪ B) (h : b ≤ d) : Build C D d := by
  refine ⟨trivial, ?_⟩
  intro m S HS hC
  obtain ⟨c, hc, HS'⟩ := H.run HS (hA.trans hC)
  refine ⟨c, hc.trans h, GateBridge.restrict HS' ?_⟩
  intro f hf
  rcases hf with hs | hd
  · exact Or.inl hs
  · rcases hB hd with hc | hb
    · exact Or.inl (hC hc)
    · exact Or.inr hb

theorem xor_eq_or_and_not_and (a b : Bool) :
    xor a b = ((a || b) && !(a && b)) := by
  cases a <;> cases b <;> rfl

def faSum (a b c : Bool) : Bool := xor (xor a b) c

def faCarry (a b c : Bool) : Bool := (a && b) || (xor a b && c)

theorem fullAdderB {N : ℕ} {A : Set (Sig N)} {fa fb fc : Sig N}
    (ha : fa ∈ A) (hb : fb ∈ A) (hc : fc ∈ A) :
    Build A ({fun x => faSum (fa x) (fb x) (fc x), fun x => faCarry (fa x) (fb x) (fc x)}) 9 := by
  let abOr : Sig N := fun x => fa x || fb x
  let abAnd : Sig N := fun x => fa x && fb x
  let abNand : Sig N := fun x => !(abAnd x)
  let t1 : Sig N := fun x => abOr x && abNand x
  let tcOr : Sig N := fun x => t1 x || fc x
  let tcAnd : Sig N := fun x => t1 x && fc x
  let tcNand : Sig N := fun x => !(tcAnd x)
  let sOut : Sig N := fun x => tcOr x && tcNand x
  let cOut : Sig N := fun x => abAnd x || tcAnd x
  have h1 : Build A {abOr} 1 := orG ha hb
  have h2 : Build (A ∪ {abOr}) {abAnd} 1 := andG (Or.inl ha) (Or.inl hb)
  have h3 : Build (A ∪ ({abOr} ∪ {abAnd})) {abNand} 1 := notG (Or.inr (Or.inr rfl))
  have h4 : Build (A ∪ (({abOr} ∪ {abAnd}) ∪ {abNand})) {t1} 1 :=
    andG (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
  have h5 : Build (A ∪ ((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1})) {tcOr} 1 :=
    orG (Or.inr (Or.inr rfl)) (Or.inl hc)
  have h6 : Build (A ∪ (((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr})) {tcAnd} 1 :=
    andG (Or.inr (Or.inl (Or.inr rfl))) (Or.inl hc)
  have h7 : Build (A ∪ ((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd})) {tcNand} 1 :=
    notG (Or.inr (Or.inr rfl))
  have h8 : Build (A ∪ (((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd}) ∪ {tcNand})) {sOut} 1 :=
    andG (Or.inr (Or.inl (Or.inl (Or.inr rfl)))) (Or.inr (Or.inr rfl))
  have h9 : Build (A ∪ ((((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1}) ∪ {tcOr}) ∪ {tcAnd}) ∪ {tcNand}) ∪ {sOut})) {cOut} 1 :=
    orG (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr rfl))))))))
        (Or.inr (Or.inl (Or.inl (Or.inr rfl))))
  have hall := seq (seq (seq (seq (seq (seq (seq (seq h1 h2) h3) h4) h5) h6) h7) h8) h9
  have hsEq : sOut = fun x => faSum (fa x) (fb x) (fc x) := by
    funext x
    simp only [sOut, tcOr, tcNand, tcAnd, t1, abOr, abNand, abAnd, faSum]
    rw [xor_eq_or_and_not_and (fa x) (fb x), xor_eq_or_and_not_and _ (fc x)]
  have hcEq : cOut = fun x => faCarry (fa x) (fb x) (fc x) := by
    funext x
    simp only [cOut, tcAnd, t1, abOr, abNand, abAnd, faCarry]
    rw [xor_eq_or_and_not_and (fa x) (fb x)]
  refine relaxKeep hall le_rfl ?_ (by omega)
  intro f hf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl
  · rw [← hsEq]
    exact Or.inr (Or.inl (Or.inr rfl))
  · rw [← hcEq]
    exact Or.inr (Or.inr rfl)

def rippleCarry (a b : ℕ) : ℕ → Bool
  | 0 => false
  | j + 1 => faCarry (a.testBit j) (b.testBit j) (rippleCarry a b j)

theorem testBit_eq_decide_div_mod (x j : ℕ) :
    x.testBit j = decide ((x / 2 ^ j) % 2 = 1) := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  have hlt : (x / 2 ^ j) % 2 < 2 := Nat.mod_lt _ (by omega)
  have hcases : (x / 2 ^ j) % 2 = 0 ∨ (x / 2 ^ j) % 2 = 1 := by omega
  rcases hcases with h | h <;> simp [h]

theorem mod_two_pow_succ_eq (a j : ℕ) :
    a % 2 ^ (j + 1) = a % 2 ^ j + (if a.testBit j then 2 ^ j else 0) := by
  have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
  have hdiv1 := Nat.div_add_mod a (2 ^ j)
  have hdiv2 := Nat.div_add_mod (a / 2 ^ j) 2
  have ha_eq : a = (a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2)) + 2 ^ (j + 1) * (a / 2 ^ j / 2) := by
    rw [Nat.pow_succ]
    have h1 : 2 ^ j * (a / 2 ^ j) = 2 ^ j * (2 * (a / 2 ^ j / 2) + (a / 2 ^ j) % 2) := by
      rw [hdiv2]
    rw [Nat.mul_add] at h1
    have h2 : 2 ^ j * (2 * (a / 2 ^ j / 2)) = 2 ^ j * 2 * (a / 2 ^ j / 2) := by ring
    omega
  have hlt_rem : a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2) < 2 ^ (j + 1) := by
    have h1 : a % 2 ^ j < 2 ^ j := Nat.mod_lt _ hpos
    have h2 : (a / 2 ^ j) % 2 ≤ 1 := by have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
    have h3 : 2 ^ j * ((a / 2 ^ j) % 2) ≤ 2 ^ j := by
      calc 2 ^ j * ((a / 2 ^ j) % 2) ≤ 2 ^ j * 1 := Nat.mul_le_mul_left _ h2
        _ = 2 ^ j := Nat.mul_one _
    rw [Nat.pow_succ]; omega
  have h1 : a % 2 ^ (j + 1) = a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2) := by
    conv_lhs => rw [ha_eq]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_rem]
  rw [h1, testBit_eq_decide_div_mod a j]
  have hcases : (a / 2 ^ j) % 2 = 0 ∨ (a / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
  rcases hcases with h | h <;> simp [h]

theorem rippleCarry_spec (a b : ℕ) :
    ∀ j : ℕ,
      rippleCarry a b j = decide (2 ^ j ≤ a % 2 ^ j + b % 2 ^ j) ∧
      (a + b).testBit j = faSum (a.testBit j) (b.testBit j) (rippleCarry a b j) := by
  intro j
  have hcarry : ∀ k : ℕ, rippleCarry a b k = decide (2 ^ k ≤ a % 2 ^ k + b % 2 ^ k) := by
    intro k
    induction k with
    | zero => simp [rippleCarry, Nat.mod_one]
    | succ k ih =>
      unfold rippleCarry
      rw [ih, mod_two_pow_succ_eq a k, mod_two_pow_succ_eq b k]
      have ha_lt : a % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      have hb_lt : b % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
      cases h1 : a.testBit k <;> cases h2 : b.testBit k <;>
        by_cases h3 : 2 ^ k ≤ a % 2 ^ k + b % 2 ^ k <;>
        simp [faCarry, h3, hp] <;> omega
  refine ⟨hcarry j, ?_⟩
  rw [hcarry j]
  have hdiv : (a + b) / 2 ^ j =
      a / 2 ^ j + b / 2 ^ j + (a % 2 ^ j + b % 2 ^ j) / 2 ^ j := by
    have ha := Nat.div_add_mod a (2 ^ j)
    have hb := Nat.div_add_mod b (2 ^ j)
    have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
    have hsum : a + b = (a % 2 ^ j + b % 2 ^ j) + (a / 2 ^ j + b / 2 ^ j) * 2 ^ j := by
      have : 2 ^ j * (a / 2 ^ j) = (a / 2 ^ j) * 2 ^ j := Nat.mul_comm _ _
      have : 2 ^ j * (b / 2 ^ j) = (b / 2 ^ j) * 2 ^ j := Nat.mul_comm _ _
      rw [Nat.add_mul]; omega
    rw [hsum, Nat.add_mul_div_right _ _ hpos]
    omega
  have hcdiv : (a % 2 ^ j + b % 2 ^ j) / 2 ^ j = if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0 := by
    have ha_lt : a % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    have hb_lt : b % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    by_cases hle : 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j
    · simp only [hle, ↓reduceIte]
      have hsub : a % 2 ^ j + b % 2 ^ j = (a % 2 ^ j + b % 2 ^ j - 2 ^ j) + 1 * 2 ^ j := by omega
      rw [hsub, Nat.add_mul_div_right _ _ (Nat.two_pow_pos j), Nat.div_eq_of_lt (by omega)]
    · simp only [hle, ↓reduceIte]
      exact Nat.div_eq_of_lt (by omega)
  rw [testBit_eq_decide_div_mod (a + b) j, testBit_eq_decide_div_mod a j,
    testBit_eq_decide_div_mod b j, hdiv, hcdiv]
  have ha2 : (a / 2 ^ j) % 2 = 0 ∨ (a / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
  have hb2 : (b / 2 ^ j) % 2 = 0 ∨ (b / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (b / 2 ^ j) (by omega : 0 < 2); omega
  have hmod : (a / 2 ^ j + b / 2 ^ j + if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0) % 2 =
      ((a / 2 ^ j) % 2 + (b / 2 ^ j) % 2 + if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0) % 2 := by
    omega
  rw [hmod]
  by_cases hc : 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j <;>
  rcases ha2 with ha | ha <;>
  rcases hb2 with hb | hb <;>
  simp [faSum, hc, ha, hb]

def bitsOf {N : ℕ} (L : ℕ) (F : (Fin N → Bool) → ℕ) : Fin L → Sig N :=
  fun j x => (F x).testBit j.val

theorem rippleB {N : ℕ} {A : Set (Sig N)} (F G : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A) :
    ∀ L : ℕ,
      (∀ j : Fin L, (fun x => (F x).testBit j.val) ∈ A) →
      (∀ j : Fin L, (fun x => (G x).testBit j.val) ∈ A) →
      Build A
        ((Set.range (bitsOf L (fun x => F x + G x))) ∪ {fun x => rippleCarry (F x) (G x) L})
        (9 * L) := by
  intro L
  induction L with
  | zero =>
    intro _ _
    simp only [Nat.mul_zero]
    apply idle
    intro f hf
    rcases hf with ⟨j, _⟩ | rfl
    · exact Fin.elim0 j
    · exact hfalse
  | succ L ih =>
    intro hF hG
    have hprev := ih (fun j => hF j.castSucc) (fun j => hG j.castSucc)
    have hstep : Build
        (A ∪ (Set.range (bitsOf L (fun x => F x + G x)) ∪ {fun x => rippleCarry (F x) (G x) L}))
        ({fun x => faSum ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L),
          fun x => faCarry ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L)}) 9 :=
      fullAdderB (Or.inl (hF (Fin.last L))) (Or.inl (hG (Fin.last L))) (Or.inr (Or.inr rfl))
    have hseq := seq hprev hstep
    refine relaxKeep hseq le_rfl ?_ (by omega)
    intro f hf
    rcases hf with ⟨j, rfl⟩ | rfl
    · by_cases hj : j.val < L
      · have hjeq : bitsOf (L + 1) (fun x => F x + G x) j =
            bitsOf L (fun x => F x + G x) ⟨j.val, hj⟩ := rfl
        rw [hjeq]
        exact Or.inr (Or.inl (Or.inl ⟨⟨j.val, hj⟩, rfl⟩))
      · have hjeq : j.val = L := by omega
        have hfeq : bitsOf (L + 1) (fun x => F x + G x) j =
            fun x => faSum ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L) := by
          funext x
          unfold bitsOf
          rw [hjeq]
          exact (rippleCarry_spec (F x) (G x) L).2
        rw [hfeq]
        exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

theorem sumTwoB {N : ℕ} {A : Set (Sig N)} (L : ℕ) (F G : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A)
    (hF : ∀ j : Fin L, bitsOf L F j ∈ A)
    (hG : ∀ j : Fin L, bitsOf L G j ∈ A) :
    Build A (Set.range (bitsOf L (fun x => F x + G x))) (9 * L) :=
  relaxKeep (rippleB F G hfalse L hF hG) le_rfl
    (fun _ hf => Or.inr (Or.inl hf)) le_rfl
def familyOut {ι : Type*} (s : Finset ι) (B : ι → Set (Sig n)) : Set (Sig n) :=
  {f | ∃ i ∈ s, f ∈ B i}

lemma familyG {ι : Type*} [Fintype ι] {A : Set (Sig n)} (B : ι → Set (Sig n)) (c : Nat)
    (h : ∀ i, Build A (B i) c) : Build A (familyOut Finset.univ B) (Fintype.card ι * c) := by
  classical
  suffices ∀ s, Build A (familyOut s B) (s.card * c) by simpa [Finset.card_univ] using this Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty => simpa [familyOut] using (idle (A := A) (B := ∅) (by simp))
  | @insert i s hi ih =>
    have hnew := bothG ih (h i)
    refine relax hnew le_rfl ?_ (by rw [Finset.card_insert_of_notMem hi, Nat.succ_mul])
    rintro v ⟨j, hj, hv⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Or.inr hv
    · exact Or.inl ⟨j, hj, hv⟩

lemma family_mem {ι : Type*} [Fintype ι] {B : ι → Set (Sig n)} {i : ι} {f : Sig n}
    (h : f ∈ B i) : f ∈ familyOut Finset.univ B := ⟨i, Finset.mem_univ i, h⟩

end Build
end Compiler

namespace Compiler
namespace Build

theorem bitConst {A : Set (Sig N)} (c : ℕ) (hf : (fun _ => false) ∈ A)
    (ht : (fun _ => true) ∈ A) : Build A (Set.range (bitsOf m (fun _ => c))) 0 :=
  wordConstG (fun j => c.testBit j.val) hf ht

theorem bitGate {A : Set (Sig N)} {p : Sig N} {F : (Fin N → Bool) → ℕ}
    (hp : p ∈ A) (hF : Available A (bitsOf m F)) :
    Build A (Set.range (bitsOf m (fun x => if p x then F x else 0))) m := by
  apply relax (wordAndG (v := fun _ => p) (u := bitsOf m F) (fun _ => hp) hF) le_rfl ?_ le_rfl
  rintro _ ⟨j, rfl⟩
  refine ⟨j, ?_⟩
  funext x
  cases hp' : p x <;> simp [bitsOf, an, hp']

private theorem bit_twice_add_one_zero (a : ℕ) : (2 * a + 1).testBit 0 = true := by
  rw [show 2 * a + 1 = 2 ^ 1 * a + 1 by rfl]
  rw [Nat.testBit_two_pow_mul_add a (b := 1) (i := 1) (by decide)]
  rfl

private theorem bit_twice_add_one_succ (a j : ℕ) :
    (2 * a + 1).testBit (j + 1) = a.testBit j := by
  rw [show 2 * a + 1 = 2 ^ 1 * a + 1 by rfl]
  rw [Nat.testBit_two_pow_mul_add a (b := 1) (i := 1) (by decide)]
  simp

private theorem bit_twice_succ (a j : ℕ) : (2 * a).testBit (j + 1) = a.testBit j := by
  rw [show 2 * a = 2 ^ 1 * a + 0 by rfl]
  rw [Nat.testBit_two_pow_mul_add a (b := 0) (i := 1) (by decide)]
  simp

theorem subSumB {N w : ℕ} {A : Set (Sig N)} (F T : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (hF : Available A (bitsOf w F)) (hT : Available A (bitsOf w T))
    (hFb : ∀ x, F x < 2 ^ w) (hTb : ∀ x, T x < 2 ^ w) :
    Build A (Set.range (bitsOf w (fun x => F x + (2 ^ w - (T x + 1)) + 1)) ∪
      {fun x => decide (F x < T x)}) (10 * w + 10) := by
  let C : (Fin N → Bool) → ℕ := fun x => 2 ^ w - (T x + 1)
  have hC (x) : T x + C x + 1 = 2 ^ w := by
    have := hTb x
    dsimp [C]
    omega
  have hCb (x) : C x < 2 ^ w := by have := hC x; omega
  have hcbit (j : Fin w) : bitsOf w C j = nt (bitsOf w T j) := by
    funext x
    simpa [bitsOf, C, nt, j.isLt] using Nat.testBit_two_pow_sub_succ (hTb x) j.val
  have Hc : Build A (Set.range (bitsOf w C)) w := by
    rw [show bitsOf w C = _ from funext hcbit]
    exact wordNotG hT
  let B := A ∪ Set.range (bitsOf w C)

  let U : (Fin N → Bool) → ℕ := fun x => 2 * F x + 1
  let V : (Fin N → Bool) → ℕ := fun x => 2 * C x + 1
  have liftBits {G : (Fin N → Bool) → ℕ} (hG : Available B (bitsOf w G)) :
      Available B (bitsOf (w + 1) (fun x => 2 * G x + 1)) := by
    intro j
    by_cases hj : j.val = 0
    · have he : bitsOf (w + 1) (fun x => 2 * G x + 1) j = fun _ => true := by
        funext x
        change (2 * G x + 1).testBit j.val = true
        rw [hj, bit_twice_add_one_zero]
      rw [he]
      exact Or.inl htrue
    · let i : Fin w := ⟨j.val - 1, by omega⟩
      have hi : j.val = i.val + 1 := by dsimp [i]; omega
      have he : bitsOf (w + 1) (fun x => 2 * G x + 1) j = bitsOf w G i := by
        funext x
        change (2 * G x + 1).testBit j.val = (G x).testBit i.val
        rw [hi, bit_twice_add_one_succ]
      rw [he]
      exact hG i
  have Hsum := rippleB U V (A := B) (Or.inl hfalse) (w + 1)
    (liftBits (fun j => Or.inl (hF j))) (liftBits (fun j => Or.inr ⟨j, rfl⟩))
  let Carry : Sig N := fun x => rippleCarry (U x) (V x) (w + 1)
  have hflag : nt Carry = fun x => decide (F x < T x) := by
    funext x
    have hu : U x < 2 ^ (w + 1) := by
      have := hFb x
      rw [Nat.pow_succ]
      dsimp [U]
      omega
    have hv : V x < 2 ^ (w + 1) := by
      have := hCb x
      rw [Nat.pow_succ]
      dsimp [V]
      omega
    have he : 2 ^ (w + 1) ≤ U x + V x ↔ T x ≤ F x := by
      rw [Nat.pow_succ]
      have := hC x
      dsimp [U, V]
      omega
    simp only [nt, Carry, (rippleCarry_spec (U x) (V x) (w + 1)).1,
      Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv, he]
    by_cases h : T x ≤ F x
    · simp [h, Nat.not_lt_of_ge h]
    · simp [h, Nat.lt_of_not_ge h]
  have Hnot := notG
    (A := A ∪ (Set.range (bitsOf w C) ∪
      (Set.range (bitsOf (w + 1) (fun x => U x + V x)) ∪ {Carry})))
    (f := Carry) (Or.inr (Or.inr (Or.inr rfl)))
  refine relax (seq (seq Hc Hsum) Hnot) le_rfl ?_ (by omega)
  intro f hf
  rcases hf with ⟨j, rfl⟩ | rfl
  · let i : Fin (w + 1) := ⟨j.val + 1, by omega⟩
    have he : bitsOf w (fun x => F x + C x + 1) j =
        bitsOf (w + 1) (fun x => U x + V x) i := by
      funext x
      change (F x + C x + 1).testBit j.val = (U x + V x).testBit (j.val + 1)
      rw [show U x + V x = 2 * (F x + C x + 1) by dsimp [U, V]; omega, bit_twice_succ]
    change bitsOf w (fun x => F x + C x + 1) j ∈ _
    rw [he]
    exact Or.inl (Or.inr (Or.inl ⟨i, rfl⟩))
  · rw [← hflag]
    exact Or.inr rfl

theorem wordLtB {N w : ℕ} {A : Set (Sig N)} (F T : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (hF : Available A (bitsOf w F)) (hT : Available A (bitsOf w T))
    (hFb : ∀ x, F x < 2 ^ w) (hTb : ∀ x, T x < 2 ^ w) :
    Build A {fun x => decide (F x < T x)} (10 * w + 10) :=
  relax (subSumB F T hfalse htrue hF hT hFb hTb) le_rfl Set.subset_union_right le_rfl

theorem guardedSubB {N w : ℕ} {A : Set (Sig N)} (F T : (Fin N → Bool) → ℕ)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (hF : Available A (bitsOf w F)) (hT : Available A (bitsOf w T))
    (hFb : ∀ x, F x < 2 ^ w) (hTb : ∀ x, T x < 2 ^ w) :
    Build A (Set.range (bitsOf w (fun x => if T x ≤ F x then F x - T x else F x)) ∪
      {fun x => decide (F x < T x)}) (14 * w + 10) := by
  let D := bitsOf w (fun x => F x + (2 ^ w - (T x + 1)) + 1)
  let L : Sig N := fun x => decide (F x < T x)
  have H := subSumB F T hfalse htrue hF hT hFb hTb
  have Hmux := wordMuxG (A := A ∪ (Set.range D ∪ {L})) (s := L) (v := D) (u := bitsOf w F)
    (Or.inr (Or.inr rfl)) (fun j => Or.inr (Or.inl ⟨j, rfl⟩)) (fun j => Or.inl (hF j))
  refine relax (seq H Hmux) le_rfl ?_ (by omega)
  intro f hf
  rcases hf with ⟨j, rfl⟩ | rfl
  · refine Or.inr ⟨j, ?_⟩
    funext x
    by_cases h : T x ≤ F x
    · have ht := hTb x
      have he : F x + (2 ^ w - (T x + 1)) + 1 = 2 ^ w + (F x - T x) := by omega
      simp [mx, D, L, bitsOf, h, Nat.not_lt_of_ge h, he, Nat.testBit_two_pow_add_gt j.isLt]
    · simp [mx, D, L, bitsOf, h, Nat.lt_of_not_ge h]
  · exact Or.inl (Or.inr rfl)

theorem sumFinsetB {N w : ℕ} {A : Set (Sig N)} {ι : Type*}
    (s : Finset ι) (F : ι → (Fin N → Bool) → ℕ)
    (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A)
    (hF : ∀ i ∈ s, Available A (bitsOf w (F i))) :
    Build A (Set.range (bitsOf w (fun x => ∑ i ∈ s, F i x))) (s.card * (9 * w)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (bitConst (m := w) 0 hf ht)
  | @insert i s hi ih =>
    have H := ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))
    have H' := sumTwoB (A := A ∪ Set.range (bitsOf w (fun x => ∑ j ∈ s, F j x)))
      w (F i) (fun x => ∑ j ∈ s, F j x) (Or.inl hf)
      (fun j => Or.inl (hF i (Finset.mem_insert_self _ _) j))
      (fun j => Or.inr ⟨j, rfl⟩)
    simpa only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.add_mul, Nat.one_mul]
      using thenG H H'

theorem sumGatedB {N w : ℕ} {A : Set (Sig N)} {ι : Type*} [Fintype ι]
    (on : ι → Sig N) (F : ι → (Fin N → Bool) → ℕ)
    (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A)
    (ho : ∀ i, on i ∈ A) (hF : ∀ i, Available A (bitsOf w (F i))) :
    Build A (Set.range (bitsOf w (fun x => ∑ i, if on i x then F i x else 0)))
      (Fintype.card ι * (10 * w)) := by
  classical
  let G (i : ι) (x : Fin N → Bool) := if on i x then F i x else 0
  have H := familyG (fun i => Set.range (bitsOf w (G i))) w
    (fun i => bitGate (ho i) (hF i))
  have H' := sumFinsetB (A := A ∪ familyOut Finset.univ (fun i => Set.range (bitsOf w (G i))))
    Finset.univ G (Or.inl hf) (Or.inl ht)
    (fun i _ j => Or.inr (family_mem (B := fun i => Set.range (bitsOf w (G i))) (i := i) ⟨j, rfl⟩))
  simpa only [Finset.card_univ, ← Nat.mul_add, show w + 9 * w = 10 * w by omega]
    using thenG H H'

noncomputable def pathCounts {N : ℕ} {S E : Type*} [Fintype S] [Fintype E] [DecidableEq S]
    (init : S) (step : ℕ → S → E → S) (permit : ℕ → E → Sig N) :
    ℕ → S → (Fin N → Bool) → ℕ
  | 0, s, _ => if s = init then 1 else 0
  | j+1, s, x => ∑ a : S × E, if step j a.1 a.2 = s ∧ permit j a.2 x = true
      then pathCounts init step permit j a.1 x else 0

def countOut {N : ℕ} {S : Type*} [Fintype S]
    (w : ℕ) (F : S → (Fin N → Bool) → ℕ) : Set (Sig N) :=
  familyOut Finset.univ (fun i => Set.range (bitsOf w (F i)))

theorem countOut_mem {N w : ℕ} {S : Type*} [Fintype S]
    {F : S → (Fin N → Bool) → ℕ} (s : S) (i : Fin w) :
    bitsOf w (F s) i ∈ countOut w F := family_mem (i := s) ⟨i, rfl⟩

theorem pathCountsB {N w L : ℕ} {A : Set (Sig N)} {S E : Type*}
    [Fintype S] [Fintype E] [DecidableEq S]
    (init : S) (step : ℕ → S → E → S) (permit : ℕ → E → Sig N)
    (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A)
    (hp : ∀ j < L, ∀ e, permit j e ∈ A) :
    Build A (countOut w (pathCounts init step permit L))
      (L * (Fintype.card S * (Fintype.card (S × E) * (10 * w)))) := by
  let O j := countOut w (pathCounts init step permit j)
  have hb : Build A (O 0) 0 := by
    exact relax (familyG _ 0 (fun s => bitConst (m := w) (if s = init then 1 else 0) hf ht))
      le_rfl le_rfl (by simp)
  suffices H : Build A (O L) (0 + L * (Fintype.card S * (Fintype.card (S × E) * (10 * w)))) by
    simpa only [Nat.zero_add] using H
  refine loopG O hb fun j hj => ?_
  apply familyG
  intro s
  let on : S × E → Sig N := fun a => if step j a.1 a.2 = s then permit j a.2 else fun _ => false
  have hon (a) : on a ∈ A ∪ O j := by
    by_cases h : step j a.1 a.2 = s
    · rw [show on a = permit j a.2 from if_pos h]
      exact Or.inl (hp j hj a.2)
    · rw [show on a = (fun _ => false) from if_neg h]
      exact Or.inl hf
  have H := sumGatedB (w := w) on (fun (a : S × E) => pathCounts init step permit j a.1)
    (Or.inl hf) (Or.inl ht) hon (fun a i => Or.inr (countOut_mem a.1 i))
  refine relax H le_rfl ?_ le_rfl
  rintro _ ⟨i, rfl⟩
  refine ⟨i, ?_⟩
  congr 1
  funext x
  rw [pathCounts]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : step j a.1 a.2 = s <;> simp [on, h]

def runPath {S E : Type*} (init : S) (step : ℕ → S → E → S) :
    (j : ℕ) → (Fin j → E) → S
  | 0, _ => init
  | j+1, y => step j (runPath init step j (Fin.init y)) (y (Fin.last j))

def livePath {N : ℕ} {E : Type*} (permit : ℕ → E → Sig N) :
    (j : ℕ) → (Fin j → E) → (Fin N → Bool) → Bool
  | 0, _, _ => true
  | j+1, y, x => livePath permit j (Fin.init y) x && permit j (y (Fin.last j)) x

theorem pathCounts_spec {N : ℕ} {S E : Type*} [Fintype S] [Fintype E] [DecidableEq S]
    (init : S) (step : ℕ → S → E → S) (permit : ℕ → E → Sig N)
    (j : ℕ) (s : S) (x : Fin N → Bool) :
    pathCounts init step permit j s x =
      ∑ y : Fin j → E, if livePath permit j y x = true ∧ runPath init step j y = s then 1 else 0 := by
  classical
  induction j generalizing s with
  | zero => simp [pathCounts, livePath, runPath, eq_comm]
  | succ j ih =>
    rw [pathCounts]
    simp_rw [Fintype.sum_prod_type, ih]
    rw [Finset.sum_comm]
    let equiv := Fin.snocEquiv (fun _ : Fin (j + 1) => E)
    rw [← Fintype.sum_equiv equiv _ _ (fun _ => rfl), Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro e _
    have he (a : S) :
        (if step j a e = s ∧ permit j e x = true then
          ∑ y : Fin j → E, if livePath permit j y x = true ∧ runPath init step j y = a then 1 else 0 else 0) =
        ∑ y : Fin j → E, if runPath init step j y = a then
          (if (livePath permit j y x = true ∧ permit j e x = true) ∧ step j a e = s then 1 else 0) else 0 := by
      split_ifs with h
      · apply Finset.sum_congr rfl
        intro y _
        by_cases hy : runPath init step j y = a <;> simp [hy, h.1, h.2]
      · rw [Finset.sum_eq_zero]
        intro y _
        by_cases hy : runPath init step j y = a
        · simp only [hy, if_true]
          split_ifs with hh
          · exact (h ⟨hh.2, hh.1.2⟩).elim
          · rfl
        · simp [hy]
    simp_rw [he, Finset.sum_comm (s := (Finset.univ : Finset S))]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_eq_single (runPath init step j y)]
    · simp [equiv, Fin.snocEquiv_apply, livePath, runPath]
    · intro a _ ha
      simp [Ne.symm ha]
    · simp

theorem livePath_spec {N : ℕ} {E : Type*} (permit : ℕ → E → Sig N)
    (j : ℕ) (y : Fin j → E) (x : Fin N → Bool) :
    livePath permit j y x = true ↔ ∀ i : Fin j, permit i.val (y i) x = true := by
  induction j with
  | zero => simp [livePath]
  | succ j ih =>
    simp only [livePath, Bool.and_eq_true, ih, Fin.init, Fin.forall_fin_succ_pi]
    constructor
    · intro h i
      exact Fin.lastCases (motive := fun i => permit i.val (y i) x = true) h.2 h.1 i
    · intro H
      exact ⟨fun i => H i.castSucc, H (Fin.last j)⟩

theorem runPath_fold {S E : Type*} (init : S) (next : S → E → S)
    (j : ℕ) (y : Fin j → E) :
    runPath init (fun _ => next) j y = (List.ofFn y).foldl next init := by
  induction j with
  | zero => simp [runPath]
  | succ j ih =>
    rw [List.ofFn_succ_last, List.foldl_append, runPath, ih]
    rfl

noncomputable def acceptingCount {N : ℕ} {S E : Type*} [Fintype S] [Fintype E] [DecidableEq S]
    (init : S) (step : ℕ → S → E → S) (permit : ℕ → E → Sig N) (accept : S → Sig N)
    (L : ℕ) (x : Fin N → Bool) : ℕ :=
  ∑ s, if accept s x then pathCounts init step permit L s x else 0

theorem acceptingCount_spec {N : ℕ} {S E : Type*} [Fintype S] [Fintype E] [DecidableEq S]
    (init : S) (step : ℕ → S → E → S) (permit : ℕ → E → Sig N) (accept : S → Sig N)
    (L : ℕ) (x : Fin N → Bool) :
    acceptingCount init step permit accept L x =
      ∑ y : Fin L → E, if livePath permit L y x = true ∧ accept (runPath init step L y) x = true
        then 1 else 0 := by
  unfold acceptingCount
  simp_rw [pathCounts_spec]
  have h (s : S) :
      (if accept s x = true then
        ∑ y : Fin L → E, if livePath permit L y x = true ∧ runPath init step L y = s then 1 else 0
        else 0) =
      ∑ y : Fin L → E, if runPath init step L y = s then
        if livePath permit L y x = true ∧ accept s x = true then 1 else 0
        else 0 := by
    by_cases hs : accept s x = true
    · simp only [hs, ite_true, and_true]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : runPath init step L y = s <;> simp [hy]
    · have hfalse : accept s x = false := Bool.eq_false_of_not_eq_true hs
      simp [hfalse]
  simp_rw [h]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_eq_single (runPath init step L y)]
  · simp
  · intro s _ hs
    simp [Ne.symm hs]
  · simp

theorem acceptingCountB {N w L : ℕ} {A : Set (Sig N)} {S E : Type*}
    [Fintype S] [Fintype E] [DecidableEq S]
    (init : S) (step : ℕ → S → E → S) (permit : ℕ → E → Sig N) (accept : S → Sig N)
    (hf : (fun _ => false) ∈ A) (ht : (fun _ => true) ∈ A)
    (hp : ∀ j < L, ∀ e, permit j e ∈ A) (ha : ∀ s, accept s ∈ A) :
    Build A (Set.range (bitsOf w (acceptingCount init step permit accept L)))
      (L * (Fintype.card S * (Fintype.card (S × E) * (10 * w))) + Fintype.card S * (10 * w)) := by
  have H := pathCountsB (w := w) init step permit hf ht hp
  have H' := sumGatedB (A := A ∪ countOut w (pathCounts init step permit L))
    (w := w) accept (pathCounts init step permit L) (Or.inl hf) (Or.inl ht)
    (fun s => Or.inl (ha s)) (fun s i => Or.inr (countOut_mem s i))
  exact thenG H H'

end Build
end Compiler

namespace Front

open Compiler.Build Compiler.GateBridge
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

private theorem addConstants {N : ℕ} (hN : 0 < N) :
    Build (inputs N) ({fun _ => false, fun _ => true} : Set (Sig N)) 3 := by
  let p : Sig N := fun x => x ⟨0,hN⟩
  have hp : p ∈ inputs N := ⟨⟨0,hN⟩, rfl⟩
  have h₁ := notG hp
  have h₂ := andG (A := inputs N ∪ {nt p}) (f := p) (g := nt p) (Or.inl hp) (Or.inr rfl)
  have he : an p (nt p) = fun _ => false := by
    funext x
    cases h : p x <;> simp [an, nt, h]
  rw [he] at h₂
  have h₃ := notG (A := inputs N ∪ ({nt p} ∪ {fun _ => false})) (f := fun _ => false) (Or.inr (Or.inr rfl))
  have ht : nt (fun _ : Fin N → Bool => false) = fun _ => true := rfl
  rw [ht] at h₃
  refine relax (seq (seq h₁ h₂) h₃) le_rfl ?_ le_rfl
  rintro f (rfl | rfl)
  · exact Or.inl (Or.inr rfl)
  · exact Or.inr rfl

theorem realize {N b : ℕ} {O : Set (Sig N)} (hN : 0 < N) (H : Build (base N) O b) :
    ∃ (g : Circuit) (whereAt : O → Fin (N+g.size)),
      ReadsBack N g ∧ g.size ≤ 3+b ∧ (∀ a ∈ g.gates, Legal a.op a.inputs.length) ∧
      ∀ (f : O) (x : Fin N → Bool), (g.wires (List.ofFn x)).getD (whereAt f).val false = f.val x := by
  classical
  have H' : Build (inputs N) O (3+b) := thenG (addConstants hN) H
  have hs : Scheduled N id 0 (inputs N) := start (F := id) (fun (i : Fin N) x => x i) (fun _ _ => rfl)
  obtain ⟨k, hk, hks⟩ := H'.run hs le_rfl
  rw [Nat.zero_add] at hks
  obtain ⟨gs, e, back, legal, hw⟩ := hks
  have hh (f : O) := hw f.val (Or.inr f.property)
  choose i hi hs using hh
  refine ⟨⟨gs, 0⟩, fun f => ⟨i f, ?_⟩, back, ?_, legal, ?_⟩
  · simpa only [Circuit.size, e] using hi f
  · simpa only [Circuit.size, e] using hk
  · intro f x
    exact hs f x

end Front

namespace Layout

open Function Equiv.Perm

variable {n : ℕ}

abbrev Label := Fin n

abbrev Root (τ : Equiv.Perm (Fin n)) := {r : Fin n // ∀ s, τ.SameCycle r s → r ≤ s}

abbrev Active (τ : Equiv.Perm (Fin n)) := Σ r : Root τ, Fin (minimalPeriod τ r.val)

lemma periodic (τ : Equiv.Perm (Fin n)) (i : Fin n) : i ∈ periodicPts τ := by
  have hlt : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by simp
  obtain ⟨a, b, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun t : Fin (n + 1) => (τ^[t.val]) i) hlt
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
  · refine ⟨b.val - a.val, by omega, ?_⟩
    apply (τ.injective.iterate a.val)
    rw [← Function.iterate_add_apply, show a.val + (b.val - a.val) = b.val by omega, heq]
  · refine ⟨a.val - b.val, by omega, ?_⟩
    apply (τ.injective.iterate b.val)
    rw [← Function.iterate_add_apply, show b.val + (a.val - b.val) = a.val by omega, heq]

lemma periodPos (τ : Equiv.Perm (Fin n)) (i : Fin n) : 0 < minimalPeriod τ i :=
  minimalPeriod_pos_of_mem_periodicPts (periodic τ i)

lemma periodLe (τ : Equiv.Perm (Fin n)) (i : Fin n) : minimalPeriod τ i ≤ n := by
  simpa only [Fintype.card_fin] using minimalPeriod_le_card (f := τ) (x := i)

lemma cycleIff (τ : Equiv.Perm (Fin n)) (r s : Fin n) :
    τ.SameCycle r s ↔ ∃ j < minimalPeriod τ r, (τ^[j]) r = s := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    rw [Equiv.Perm.coe_pow] at hk
    exact ⟨k % minimalPeriod τ r, Nat.mod_lt _ (periodPos τ r), iterate_mod_minimalPeriod_eq.trans hk⟩
  · rintro ⟨j, -, rfl⟩
    rw [← Equiv.Perm.coe_pow]
    exact (SameCycle.refl τ r).pow_right

lemma existsRoot (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    ∃ r : Root τ, τ.SameCycle r.val i := by
  classical
  let O := Finset.univ.filter (fun r => τ.SameCycle r i)
  have hO : O.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, SameCycle.refl τ i⟩⟩
  let r := O.min' hO
  have hr : τ.SameCycle r i := (Finset.mem_filter.mp (O.min'_mem hO)).2
  refine ⟨⟨r, ?_⟩, hr⟩
  intro s hs
  exact O.min'_le s (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.symm.trans hr⟩)

def atSlot (τ : Equiv.Perm (Fin n)) (a : Active τ) : Fin n :=
  (τ^[a.2.val]) a.1.val

lemma atSlot_bij (τ : Equiv.Perm (Fin n)) : Function.Bijective (atSlot τ) := by
  constructor
  · rintro ⟨r, j⟩ ⟨s, k⟩ h
    have h1 : τ.SameCycle r.val (atSlot τ ⟨r, j⟩) := (cycleIff τ _ _).2 ⟨_, j.isLt, rfl⟩
    have h2 : τ.SameCycle s.val (atSlot τ ⟨s, k⟩) := (cycleIff τ _ _).2 ⟨_, k.isLt, rfl⟩
    rw [h] at h1
    have hrs := h1.trans h2.symm
    have hroot : r = s := Subtype.ext ((r.property _ hrs).antisymm (s.property _ hrs.symm))
    subst s
    have hjk : j = k := Fin.ext
      ((iterate_eq_iterate_iff_of_lt_minimalPeriod j.isLt k.isLt).mp h)
    subst k
    rfl
  · intro i
    obtain ⟨r, hr⟩ := existsRoot τ i
    obtain ⟨j, hj, h⟩ := (cycleIff τ _ _).mp hr
    exact ⟨⟨r, ⟨j, hj⟩⟩, h⟩

noncomputable def slotsEquiv (τ : Equiv.Perm (Fin n)) : Active τ ≃ Fin n :=
  Equiv.ofBijective (atSlot τ) (atSlot_bij τ)

lemma activeIff (τ : Equiv.Perm (Fin n)) (r : Fin n) (j : ℕ) :
    j < minimalPeriod τ r ↔ ∀ k ≤ j, 0 < k → (τ^[k]) r ≠ r := by
  constructor
  · intro h k hk hk0 hfix
    exact (not_lt_of_ge ((show IsPeriodicPt τ k r from hfix).minimalPeriod_le hk0)) (hk.trans_lt h)
  · intro h
    by_contra! hj
    exact h _ hj (periodPos τ r) iterate_minimalPeriod

lemma rootIff (τ : Equiv.Perm (Fin n)) (r : Fin n) :
    (∀ s, τ.SameCycle r s → r ≤ s) ↔ ∀ j : Fin n, r ≤ (τ^[j.val]) r := by
  constructor
  · intro h j
    rw [← Equiv.Perm.coe_pow]
    exact h _ (SameCycle.refl τ r).pow_right
  · intro h s hs
    obtain ⟨j, hj, rfl⟩ := (cycleIff τ _ _).mp hs
    exact h ⟨j, hj.trans_le (periodLe τ r)⟩

lemma nextSlot (τ : Equiv.Perm (Fin n)) (r : Root τ) (j : Fin (minimalPeriod τ r.val)) :
    τ (atSlot τ ⟨r, j⟩) =
      atSlot τ ⟨r, ⟨(j.val + 1) % minimalPeriod τ r.val, Nat.mod_lt _ (periodPos τ r.val)⟩⟩ := by
  simp only [atSlot, iterate_mod_minimalPeriod_eq, Function.iterate_succ_apply']

end Layout

namespace LayoutCircuit

open Compiler.Build

variable {N n : ℕ}

def anyFin {m : ℕ} (f : Fin m → Sig N) : Sig N :=
  fun x => (List.ofFn f).any (fun g => g x)

def allFin {m : ℕ} (f : Fin m → Sig N) : Sig N :=
  fun x => (List.ofFn f).all (fun g => g x)

lemma anyFin_true {m : ℕ} (f : Fin m → Sig N) (x : Fin N → Bool) :
    anyFin f x = true ↔ ∃ j, f j x = true := by
  simp [anyFin, List.any_eq_true, List.mem_ofFn]

lemma allFin_true {m : ℕ} (f : Fin m → Sig N) (x : Fin N → Bool) :
    allFin f x = true ↔ ∀ j, f j x = true := by
  simp [allFin, List.all_eq_true, List.mem_ofFn]

theorem anyFinB {m : ℕ} {A : Set (Sig N)} (f : Fin m → Sig N)
    (hf : ∀ j, f j ∈ A) (hz : (fun _ => false) ∈ A) :
    Build A {anyFin f} m := by
  unfold anyFin
  simpa only [List.length_ofFn] using
    anyG (List.ofFn f) (fun g hg => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
      exact hf j) hz

theorem allFinB {m : ℕ} {A : Set (Sig N)} (f : Fin m → Sig N)
    (hf : ∀ j, f j ∈ A) (ho : (fun _ => true) ∈ A) :
    Build A {allFin f} m := by
  unfold allFin
  simpa only [List.length_ofFn] using
    everyG (List.ofFn f) (fun g hg => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
      exact hf j) ho

abbrev Mat (n N : ℕ) := Fin n → Fin n → Sig N

def matPow (edge : Mat n N) : ℕ → Mat n N
  | 0, r, t => fun _ => decide (r = t)
  | j+1, r, t => anyFin (fun k => an (matPow edge j r k) (edge k t))

lemma matPow_spec (edge : Mat n N) (τ : Equiv.Perm (Fin n)) (x : Fin N → Bool)
    (he : ∀ r t, edge r t x = decide (τ r = t)) (j : ℕ) (r t : Fin n) :
    matPow edge j r t x = decide ((τ^[j]) r = t) := by
  induction j generalizing t with
  | zero => rfl
  | succ j ih =>
    apply Bool.eq_iff_iff.mpr
    simp only [matPow, anyFin_true, an, Bool.and_eq_true, ih, he, decide_eq_true_eq,
      Function.iterate_succ_apply']
    constructor
    · rintro ⟨k, rfl, h⟩
      exact h
    · intro h
      exact ⟨_, rfl, h⟩

def matOut (edge : Mat n N) (j : ℕ) : Set (Sig N) :=
  {f | ∃ k ≤ j, ∃ r t, f = matPow edge k r t}

theorem matPowB {A : Set (Sig N)} (edge : Mat n N) (L : ℕ)
    (he : ∀ r t, edge r t ∈ A) (hz : (fun _ => false) ∈ A) (ho : (fun _ => true) ∈ A) :
    Build A (matOut edge L) (L * (n * n * (2 * n))) := by
  have hb : Build A (matOut edge 0) 0 := by
    apply idle
    rintro _ ⟨j, hj, r, t, rfl⟩
    have hj0 : j = 0 := by omega
    subst j
    by_cases h : r = t
    · simpa [matPow, h] using ho
    · simpa [matPow, h] using hz
  suffices HB : Build A (matOut edge L) (0 + L * (n * n * (2 * n))) by
    simpa only [Nat.zero_add] using HB
  refine loopG (matOut edge) hb fun j _ => ?_
  let B := A ∪ matOut edge j
  have each (r t : Fin n) : Build B {matPow edge (j+1) r t} (2*n) := by
    let f := fun k : Fin n => an (matPow edge j r k) (edge k t)
    have H := finG (A := B) f 1
      (fun k => andG (Or.inr ⟨j, le_rfl, r, k, rfl⟩) (Or.inl (he k t)))
    have H' := anyFinB (A := B ∪ Set.range f) f (fun k => Or.inr ⟨k, rfl⟩) (Or.inl (Or.inl hz))
    exact relax (thenG H H') le_rfl le_rfl (by omega)
  have H := allG (A := B) (α := Fin n × Fin n) (fun a => matPow edge (j+1) a.1 a.2)
    (2*n) (fun a => each a.1 a.2)
  refine relaxKeep H le_rfl ?_ (by simp)
  rintro _ ⟨k, hk, r, t, rfl⟩
  by_cases h : k = j+1
  · subst k
    exact Or.inr ⟨(r,t), rfl⟩
  · exact Or.inl (Or.inr ⟨k, by omega, r, t, rfl⟩)

def literal (f : Sig N) (b : Bool) : Sig N := if b then f else nt f

lemma literal_true (f : Sig N) (b : Bool) (x : Fin N → Bool) :
    literal f b x = true ↔ f x = b := by
  cases b <;> cases h : f x <;> simp [literal, nt, h]

lemma literalB {A : Set (Sig N)} (f : Sig N) (b : Bool) (hf : f ∈ A) :
    Build A {literal f b} 1 := by
  cases b
  · exact notG hf
  · exact relax (idle (Set.singleton_subset_iff.mpr hf)) le_rfl le_rfl (by omega)

def rootSignal (edge : Mat n N) (r : Fin n) : Sig N :=
  allFin (fun j : Fin n => allFin (fun t : Fin n =>
    if t < r then nt (matPow edge j.val r t) else fun _ => true))

def liveSignal (edge : Mat n N) (r j : Fin n) : Sig N :=
  an (rootSignal edge r)
    (allFin fun k : Fin n => if k.val < j.val then nt (matPow edge (k.val+1) r r) else fun _ => true)

lemma rootSignal_spec (edge : Mat n N) (τ : Equiv.Perm (Fin n)) (x : Fin N → Bool)
    (he : ∀ r t, edge r t x = decide (τ r = t)) (r : Fin n) :
    rootSignal edge r x = true ↔ ∀ s, τ.SameCycle r s → r ≤ s := by
  rw [Layout.rootIff]
  simp only [rootSignal, allFin_true]
  constructor
  · intro H j
    by_contra! h
    have hbad := H j ((τ^[j.val]) r)
    simp [h, nt, matPow_spec edge τ x he] at hbad
  · intro H j t
    by_cases h : t < r
    · have hne : (τ^[j.val]) r ≠ t := fun e => (not_lt_of_ge (e ▸ H j)) h
      simp [h, nt, matPow_spec edge τ x he, hne]
    · simp [h]

lemma liveSignal_spec (edge : Mat n N) (τ : Equiv.Perm (Fin n)) (x : Fin N → Bool)
    (he : ∀ r t, edge r t x = decide (τ r = t)) (r j : Fin n) :
    liveSignal edge r j x = true ↔
      (∀ s, τ.SameCycle r s → r ≤ s) ∧ j.val < Function.minimalPeriod τ r := by
  simp only [liveSignal, an, Bool.and_eq_true, rootSignal_spec edge τ x he, allFin_true,
    Layout.activeIff]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · intro H k hkj hk
    let l : Fin n := ⟨k-1, by have := j.isLt; omega⟩
    have hl : l.val < j.val := by dsimp [l]; omega
    have heq : l.val + 1 = k := by dsimp [l]; omega
    simpa [hl, nt, matPow_spec edge τ x he, heq] using H l
  · intro H l
    by_cases hl : l.val < j.val
    · have hbad := H (l.val+1) (by omega) (by omega)
      rw [Function.iterate_succ_apply] at hbad
      simp [hl, nt, matPow_spec edge τ x he, hbad]
    · simp [hl]

theorem testAllB {m : ℕ} {A : Set (Sig N)} (f : Fin m → Sig N)
    (mask : Fin m → Prop) [DecidablePred mask] (hf : ∀ j, f j ∈ A)
    (ho : (fun _ => true) ∈ A) :
    Build A {allFin (fun j => if mask j then nt (f j) else fun _ => true)} (2*m) := by
  let F : Fin m → Sig N := fun j => if mask j then nt (f j) else fun _ => true
  have H := finG (A := A) F 1 (fun j => by
    by_cases h : mask j
    · rw [show F j = nt (f j) from if_pos h]
      exact notG (hf j)
    · rw [show F j = (fun _ => true) from if_neg h]
      exact relax (idle (Set.singleton_subset_iff.mpr ho)) le_rfl le_rfl (by omega))
  have H' := allFinB (A := A ∪ Set.range F) F (fun j => Or.inr ⟨j, rfl⟩) (Or.inl ho)
  exact relax (thenG H H') le_rfl le_rfl (by omega)

theorem rootSignalB {A : Set (Sig N)} (edge : Mat n N) (r : Fin n)
    (hM : matOut edge n ⊆ A) (ho : (fun _ => true) ∈ A) :
    Build A {rootSignal edge r} (n*(2*n)+n) := by
  let F (j : Fin n) := allFin (fun t : Fin n =>
    if t < r then nt (matPow edge j.val r t) else fun _ => true)
  have H := finG (A := A) F (2*n) (fun j => testAllB _ _
    (fun t => hM ⟨j.val,j.isLt.le,r,t,rfl⟩) ho)
  have H' := allFinB (A := A ∪ Set.range F) F (fun j => Or.inr ⟨j, rfl⟩) (Or.inl ho)
  exact thenG H H'

theorem liveSignalB {A : Set (Sig N)} (edge : Mat n N) (r j : Fin n)
    (hM : matOut edge n ⊆ A) (ho : (fun _ => true) ∈ A) :
    Build A {liveSignal edge r j} (n*(2*n)+n+2*n+1) := by
  let y := allFin fun k : Fin n => if k.val < j.val then nt (matPow edge (k.val+1) r r) else fun _ => true
  have H := bothG (rootSignalB edge r hM ho) (testAllB (A := A)
    (fun k : Fin n => matPow edge (k.val+1) r r) (fun k => k.val < j.val)
    (fun k => hM ⟨k.val+1,k.isLt,r,r,rfl⟩) ho)
  have H' := andG (A := A ∪ ({rootSignal edge r} ∪ {y}))
    (f := rootSignal edge r) (g := y) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  exact thenG H H'

abbrev Permit (n N : ℕ) := (Bool × Fin n) → Fin 3 → Sig N
abbrev Symbol := Option (Bool × Fin 3 × Fin 3)

def allowAt (edge : Mat n N) (permit : Permit n N) (r j : Fin n) (d0 d1 : Fin 3) : Sig N :=
  anyFin fun i : Fin n => an (matPow edge j.val r i) (an (permit (false,i) d0) (permit (true,i) d1))

lemma allowAt_spec (edge : Mat n N) (permit : Permit n N) (τ : Equiv.Perm (Fin n))
    (x : Fin N → Bool) (he : ∀ r t, edge r t x = decide (τ r = t))
    (r j : Fin n) (d0 d1 : Fin 3) :
    allowAt edge permit r j d0 d1 x =
      (permit (false,(τ^[j.val]) r) d0 x && permit (true,(τ^[j.val]) r) d1 x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [allowAt, anyFin_true, an, Bool.and_eq_true, matPow_spec edge τ x he, decide_eq_true_eq]
  constructor
  · rintro ⟨i, rfl, h⟩
    exact h
  · intro h
    exact ⟨_, rfl, h⟩

theorem allowAtB {A : Set (Sig N)} (edge : Mat n N) (permit : Permit n N)
    (r j : Fin n) (d0 d1 : Fin 3)
    (hm : matOut edge n ⊆ A) (hp : ∀ v d, permit v d ∈ A) (hz : (fun _ => false) ∈ A) :
    Build A {allowAt edge permit r j d0 d1} (3*n) := by
  let f (i : Fin n) := an (matPow edge j.val r i) (an (permit (false,i) d0) (permit (true,i) d1))
  have H := finG (A := A) f 2 (fun i =>
    thenG (andG (hp (false,i) d0) (hp (true,i) d1))
      (andG (Or.inl (hm ⟨j.val,j.isLt.le,r,i,rfl⟩)) (Or.inr rfl)))
  have H' := anyFinB (A := A ∪ Set.range f) f (fun j => Or.inr ⟨j, rfl⟩) (Or.inl hz)
  exact relax (thenG H H') le_rfl le_rfl (by omega)

def symbolSignal (edge : Mat n N) (permit : Permit n N) (r j : Fin n) : Symbol → Sig N
  | none => nt (liveSignal edge r j)
  | some (b,d0,d1) => an (liveSignal edge r j)
      (an (literal (matPow edge (j.val+1) r r) b) (allowAt edge permit r j d0 d1))

theorem symbolSignalB {A : Set (Sig N)} (edge : Mat n N) (permit : Permit n N)
    (r j : Fin n) (e : Symbol) (hm : matOut edge n ⊆ A)
    (hp : ∀ v d, permit v d ∈ A)
    (hz : (fun _ => false) ∈ A) (ho : (fun _ => true) ∈ A) :
    Build A {symbolSignal edge permit r j e} (n*(2*n)+n+2*n+1+3*n+3) := by
  have hl := liveSignalB edge r j hm ho
  cases e with
  | none =>
    exact relax (thenG hl (notG (Or.inr rfl))) le_rfl le_rfl (by omega)
  | some e =>
    obtain ⟨b,d0,d1⟩ := e
    let lit := literal (matPow edge (j.val+1) r r) b
    let al := allowAt edge permit r j d0 d1
    have H := bothG hl (bothG (literalB (matPow edge (j.val+1) r r) b (hm ⟨_,j.isLt,r,r,rfl⟩))
      (allowAtB edge permit r j d0 d1 hm hp hz))
    have H' := andG (A := A ∪ ({liveSignal edge r j} ∪ ({lit} ∪ {al}))) (f := lit) (g := al)
      (Or.inr (Or.inr (Or.inl rfl))) (Or.inr (Or.inr (Or.inr rfl)))
    have H'' := andG (A := A ∪ (({liveSignal edge r j} ∪ ({lit} ∪ {al})) ∪ {an lit al}))
      (f := liveSignal edge r j) (g := an lit al) (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
    exact relax (thenG (seq H H') H'') le_rfl le_rfl (by omega)

def eqBits {m : ℕ} (F : Fin m → Sig N) (bits : Fin m → Bool) : Sig N :=
  allFin (fun j => literal (F j) (bits j))

lemma eqBits_spec {m : ℕ} (F : Fin m → Sig N) (bits : Fin m → Bool) (x : Fin N → Bool) :
    eqBits F bits x = true ↔ ∀ j, F j x = bits j := by simp [eqBits, allFin_true, literal_true]

theorem eqBitsB {m : ℕ} {A : Set (Sig N)} (F : Fin m → Sig N) (bits : Fin m → Bool)
    (hF : ∀ j, F j ∈ A) (ht : (fun _ => true) ∈ A) :
    Build A {eqBits F bits} (2*m) := by
  let G (j : Fin m) := literal (F j) (bits j)
  have H := finG (A := A) G 1 (fun j => literalB _ _ (hF j))
  have H' := allFinB (A := A ∪ Set.range G) G (fun j => Or.inr ⟨j, rfl⟩) (Or.inl ht)
  exact relax (thenG H H') le_rfl le_rfl (by omega)

end LayoutCircuit

namespace ProfileFactor

abbrev Arc := ℕ × Bool × Bool
abbrev Ports (R : Type*) := Bool → Bool → R

variable {R : Type*} [CommSemiring R]

open scoped BigOperators

def colorAt (c : Bool) (k : ℕ) : Bool := if k % 2 = 0 then c else !c

lemma colorAt_zero (c : Bool) : colorAt c 0 = c := by simp [colorAt]

lemma colorAt_succ (c : Bool) (k : ℕ) : colorAt c (k + 1) = !colorAt c k := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · have h' : (k + 1) % 2 = 1 := by omega
    simp [colorAt, h, h']
  · have h' : (k + 1) % 2 = 0 := by omega
    simp [colorAt, h, h']

lemma colorAt_flip (c : Bool) (k : ℕ) : colorAt (!c) k = !colorAt c k := by
  by_cases h : k % 2 = 0 <;> simp [colorAt, h]

lemma colorAt_add (c : Bool) (m k : ℕ) :
    colorAt c (m + k) = colorAt (colorAt c m) k := by
  induction k with
  | zero => simp [colorAt_zero]
  | succ k ih => rw [← Nat.add_assoc, colorAt_succ, colorAt_succ, ih]

lemma colorAt_even (c : Bool) {k : ℕ} (he : k % 2 = 0) : colorAt c k = c := by
  simp [colorAt, he]

def portId : Ports R := fun a b => if a = b then 1 else 0

def portComp (A B : Ports R) : Ports R := fun a b => ∑ v : Bool, A a v * B v b

lemma portComp_left_id (A : Ports R) : portComp portId A = A := by
  funext a b
  simp [portComp, portId, ite_mul]

lemma portComp_right_id (A : Ports R) : portComp A portId = A := by
  funext a b
  simp [portComp, portId, mul_ite, eq_comm]

lemma portComp_assoc (A B C : Ports R) :
    portComp (portComp A B) C = portComp A (portComp B C) := by
  funext a b
  simp only [portComp, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

def portTrace (A : Ports R) : R := ∑ a : Bool, A a a

def edgePort (w : Bool → R) (c : Bool) : Ports R :=
  fun a b => if a = b then 1 else w c

def letter (w : Bool → R) (c : Bool) (p : Option Bool) : Ports R :=
  fun a b => if p = none ∨ p = some a then edgePort w c a b else 0

lemma letter_none (w : Bool → R) (c : Bool) : letter w c none = edgePort w c := by
  funext a b
  simp [letter]

lemma portComp_letter_some (A : Ports R) (w : Bool → R) (c p a b : Bool) :
    portComp A (letter w c (some p)) a b = A a p * edgePort w c p b := by
  cases p <;> simp [portComp, letter, Fintype.sum_bool]

lemma portComp_rank_one (u v : Bool → R) (A : Ports R) (a b : Bool) :
    portComp (fun i j => u i * v j) A a b = u a * portComp (fun _ j => v j) A a b := by
  simp only [portComp, Finset.mul_sum, mul_assoc]

def freePath (w : Bool → R) : Bool → ℕ → Ports R
  | _, 0 => portId
  | c, k + 1 => portComp (edgePort w c) (freePath w (!c) k)

lemma freePath_one (w : Bool → R) (c : Bool) : freePath w c 1 = edgePort w c := by
  simpa only [freePath] using portComp_right_id (edgePort w c)

lemma freePath_add (w : Bool → R) (c : Bool) (m k : ℕ) :
    freePath w c (m + k) = portComp (freePath w c m) (freePath w (colorAt c m) k) := by
  induction m generalizing c with
  | zero => simp [freePath, colorAt_zero, portComp_left_id]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [freePath, colorAt_succ, ← colorAt_flip, portComp_assoc]
    rw [ih]

lemma freePath_appendEdge (w : Bool → R) (c : Bool) (k : ℕ) :
    portComp (freePath w c k) (edgePort w (colorAt c k)) = freePath w c (k + 1) := by
  rw [freePath_add, freePath_one]

lemma freePath_flip (w : Bool → R) (c : Bool) (k : ℕ) (a b : Bool) :
    freePath w c k (!a) (!b) = freePath w c k a b := by
  induction k generalizing c a b with
  | zero => cases a <;> cases b <;> rfl
  | succ k ih =>
    have h₀ := ih (!c) false b
    have h₁ := ih (!c) true b
    cases a <;> cases b <;>
      simp [freePath, portComp, Fintype.sum_bool, edgePort] at h₀ h₁ ⊢ <;>
      rw [h₀, h₁] <;> ac_rfl

def arcFactor (w : Bool → R) (q : Arc) : R := freePath w q.2.1 q.1 false q.2.2

lemma freePath_eq_arcFactor (w : Bool → R) (c : Bool) (k : ℕ) (a b : Bool) :
    freePath w c k a b = arcFactor w (k, c, Bool.xor a b) := by
  cases a <;> cases b
  · rfl
  · rfl
  · exact freePath_flip w c k false true
  · exact freePath_flip w c k false false

lemma arcFactor_zero (w : Bool → R) (c p : Bool) :
    arcFactor w (0, c, p) = if p = false then 1 else 0 := by
  cases p <;> simp [arcFactor, freePath, portId]

lemma arcFactor_succ (w : Bool → R) (c p : Bool) (k : ℕ) :
    arcFactor w (k + 1, c, p) =
      arcFactor w (k, !c, p) + w c * arcFactor w (k, !c, !p) := by
  have h : freePath w (!c) k true p = arcFactor w (k, !c, !p) := by
    cases p <;> exact freePath_eq_arcFactor w (!c) k true _
  calc
    _ = w c * freePath w (!c) k true p + arcFactor w (k, !c, p) := by
      simp [arcFactor, freePath, portComp, Fintype.sum_bool, edgePort]
    _ = _ := by rw [h, add_comm]

def wordPorts (w : Bool → R) : Bool → List (Option Bool) → Ports R
  | _, [] => portId
  | c, p :: ps => portComp (letter w c p) (wordPorts w (!c) ps)

lemma wordPorts_append (w : Bool → R) (c : Bool) (L M : List (Option Bool)) :
    wordPorts w c (L ++ M) = portComp (wordPorts w c L) (wordPorts w (colorAt c L.length) M) := by
  induction L generalizing c with
  | nil => simp [wordPorts, colorAt_zero, portComp_left_id]
  | cons p L ih =>
    simp only [List.cons_append, List.length_cons, wordPorts, colorAt_succ, ← colorAt_flip,
      portComp_assoc]
    rw [ih]

abbrev OpenData := ℕ × Bool × ℕ × Bool × Bool

abbrev Scan := ℕ × Option OpenData × List Arc

def scanStep (c : Bool) : Scan → Option Bool → Scan
  | (k, none, A), none => (k + 1, none, A)
  | (k, none, A), some a => (k + 1, some (k, a, 1, a, colorAt c k), A)
  | (k, some (f, a, l, b, d), A), none => (k + 1, some (f, a, l + 1, b, d), A)
  | (k, some (f, a, l, b, d), A), some p =>
    (k + 1, some (f, a, 1, p, colorAt c k), (l, d, Bool.xor b p) :: A)

def scanWord (c : Bool) (L : List (Option Bool)) : Scan :=
  L.foldl (scanStep c) (0, none, [])

def arcLength (A : List Arc) : ℕ := (A.map Prod.fst).sum

def arcProduct (w : Bool → R) (A : List Arc) : R := (A.map (arcFactor w)).prod

def scanGood (c : Bool) : Scan → Prop
  | (k, o, A) => (∀ q ∈ A, 0 < q.1) ∧
    match o with
    | none => A = []
    | some (f, _, l, _, d) => 0 < l ∧ f + l + arcLength A = k ∧ colorAt d l = colorAt c k

def scanPorts (w : Bool → R) (c : Bool) : Scan → Ports R
  | (k, none, _) => freePath w c k
  | (_, some (f, a, l, b, d), A) => fun u v =>
    (arcProduct w A * freePath w c f u a) * freePath w d l b v

lemma scanStep_pos (c : Bool) (s : Scan) (p : Option Bool) :
    (scanStep c s p).1 = s.1 + 1 := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩ <;> cases p <;> rfl

lemma scanStep_good (c : Bool) (s : Scan) (p : Option Bool) (h : scanGood c s) :
    scanGood c (scanStep c s p) := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩
  · obtain ⟨hpos, he⟩ := h
    cases p with
    | none => exact ⟨hpos, he⟩
    | some a =>
      subst A
      exact ⟨hpos, by simp [scanGood, arcLength, colorAt_succ, colorAt_zero]⟩
  · obtain ⟨hpos, hl, hk, hd⟩ := h
    cases p with
    | none =>
      exact ⟨hpos, by
        refine ⟨by omega, by omega, ?_⟩
        rw [colorAt_succ, colorAt_succ, hd]⟩
    | some p =>
      refine ⟨?_, ?_⟩
      · intro q hq
        rcases List.mem_cons.mp hq with hq | hq
        · subst q; exact hl
        · exact hpos q hq
      · refine ⟨by decide, ?_, ?_⟩
        · simp [arcLength] at hk ⊢
          omega
        · simp [colorAt_succ, colorAt_zero]

lemma scanStep_ports (w : Bool → R) (c : Bool) (s : Scan) (p : Option Bool)
    (h : scanGood c s) :
    scanPorts w c (scanStep c s p) = portComp (scanPorts w c s) (letter w (colorAt c s.1) p) := by
  funext u v
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩
  · cases p with
    | none =>
      change freePath w c (k + 1) u v = portComp (freePath w c k) (letter w (colorAt c k) none) u v
      rw [letter_none, freePath_appendEdge]
    | some a =>
      have he : A = [] := h.2
      subst A
      change ((1 : R) * freePath w c k u a) * freePath w (colorAt c k) 1 a v =
        portComp (freePath w c k) (letter w (colorAt c k) (some a)) u v
      rw [portComp_letter_some, freePath_one, one_mul]
  · obtain ⟨_, _, _, hd⟩ := h
    cases p with
    | none =>
      change (arcProduct w A * freePath w c f u a) * freePath w d (l + 1) b v =
        portComp (fun i j => (arcProduct w A * freePath w c f i a) * freePath w d l b j)
          (letter w (colorAt c k) none) u v
      rw [letter_none, portComp_rank_one, ← hd, ← freePath_appendEdge] <;> rfl
    | some p =>
      change ((arcFactor w (l, d, Bool.xor b p) * arcProduct w A) * freePath w c f u a) *
          freePath w (colorAt c k) 1 p v =
        portComp (fun i j => (arcProduct w A * freePath w c f i a) * freePath w d l b j)
          (letter w (colorAt c k) (some p)) u v
      rw [portComp_letter_some, freePath_one, freePath_eq_arcFactor w d l b p]
      ac_rfl

lemma scanWord_spec (w : Bool → R) (c : Bool) (L : List (Option Bool)) :
    (scanWord c L).1 = L.length ∧ scanGood c (scanWord c L) ∧
    scanPorts w c (scanWord c L) = wordPorts w c L := by
  induction L using List.reverseRecOn with
  | nil => simp [scanWord, scanGood, scanPorts, wordPorts, freePath]
  | append_singleton L p ih =>
    obtain ⟨hk, hg, hp⟩ := ih
    have hs : scanWord c (L ++ [p]) = scanStep c (scanWord c L) p := by
      simp [scanWord, List.foldl_append]
    refine ⟨by simp [hs, scanStep_pos, hk], ?_, ?_⟩
    · rw [hs]
      exact scanStep_good c _ p hg
    · rw [hs, scanStep_ports _ _ _ _ hg, hp, hk, wordPorts_append]
      simp [wordPorts, portComp_right_id]

def closeScan (c : Bool) : Scan → ℕ × List Arc
  | (k, none, _) => (1, [(k, c, false)])
  | (_, some (f, a, l, b, d), A) => (0, (l + f, d, Bool.xor b a) :: A)

lemma closeScan_length (c : Bool) (s : Scan) (hg : scanGood c s) :
    arcLength (closeScan c s).2 = s.1 := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩
  · simp [closeScan, arcLength]
  · obtain ⟨_, _, hk, _⟩ := hg
    simp [closeScan, arcLength] at hk ⊢
    omega

lemma closeScan_positive (c : Bool) (s : Scan) (hg : scanGood c s) (hk : 0 < s.1) :
    ∀ q ∈ (closeScan c s).2, 0 < q.1 := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩
  · simpa [closeScan] using hk
  · obtain ⟨hA, hl, _, _⟩ := hg
    intro q hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst q
      change 0 < l + f
      omega
    · exact hA q hq

lemma closeScan_factor (w : Bool → R) (c : Bool) (s : Scan)
    (hg : scanGood c s) (he : s.1 % 2 = 0) :
    portTrace (scanPorts w c s) = (2 : R) ^ (closeScan c s).1 * arcProduct w (closeScan c s).2 := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩
  · change (∑ x : Bool, freePath w c k x x) = (2 : R) ^ 1 * (arcFactor w (k, c, false) * 1)
    have h : freePath w c k true true = freePath w c k false false :=
      freePath_flip w c k false false
    rw [Fintype.sum_bool, pow_one, mul_one, two_mul, h] <;> rfl
  · obtain ⟨_, _, _, hd⟩ := hg
    change k % 2 = 0 at he
    have hc : colorAt d l = c := hd.trans (colorAt_even c he)
    have H : (∑ x : Bool, (arcProduct w A * freePath w c f x a) * freePath w d l b x) =
        arcProduct w A * portComp (freePath w d l) (freePath w c f) b a := by
      simp only [portComp, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ac_rfl
    change (∑ x : Bool, (arcProduct w A * freePath w c f x a) * freePath w d l b x) =
        (2 : R) ^ 0 * (arcFactor w (l + f, d, Bool.xor b a) * arcProduct w A)
    rw [H, ← hc, ← freePath_add, freePath_eq_arcFactor w d (l + f) b a, pow_zero, one_mul, mul_comm]

lemma cycle_factor (w : Bool → R) (c : Bool) (L : List (Option Bool)) (he : L.length % 2 = 0) :
    portTrace (wordPorts w c L) =
      (2 : R) ^ (closeScan c (scanWord c L)).1 * arcProduct w (closeScan c (scanWord c L)).2 := by
  obtain ⟨hk, hg, hp⟩ := scanWord_spec w c L
  rw [← hp]
  apply closeScan_factor w c _ hg
  rw [hk]
  exact he

lemma scanWord_valid (c : Bool) (L : List (Option Bool)) :
    (scanWord c L).1 = L.length ∧ scanGood c (scanWord c L) :=
  let h := scanWord_spec (fun _ => (0 : ℕ)) c L
  ⟨h.1, h.2.1⟩

lemma scanPartial_length (c : Bool) (s : Scan) (hg : scanGood c s) :
    arcLength s.2.2 ≤ s.1 := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩
  · have h : A = [] := hg.2
    simp [h, arcLength]
  · obtain ⟨_, _, hk, _⟩ := hg
    change arcLength A ≤ k
    omega

lemma scanPartial_positive (c : Bool) (s : Scan) (hg : scanGood c s) :
    ∀ q ∈ s.2.2, 0 < q.1 := by
  rcases s with ⟨k, o, A⟩
  exact hg.1

lemma scanWord_partial (c : Bool) (L : List (Option Bool)) :
    arcLength (scanWord c L).2.2 ≤ L.length ∧ ∀ q ∈ (scanWord c L).2.2, 0 < q.1 := by
  obtain ⟨hk, hg⟩ := scanWord_valid c L
  exact ⟨(scanPartial_length c _ hg).trans_eq hk, scanPartial_positive c _ hg⟩

lemma cycle_inventory_bounds (c : Bool) (L : List (Option Bool)) (hn : 0 < L.length) :
    arcLength (closeScan c (scanWord c L)).2 = L.length ∧
      ∀ q ∈ (closeScan c (scanWord c L)).2, 0 < q.1 := by
  obtain ⟨hk, hg⟩ := scanWord_valid c L
  refine ⟨(closeScan_length c _ hg).trans hk, closeScan_positive c _ hg ?_⟩
  rwa [hk]

lemma tailColor_eq_lastOffset (c : Bool) (k : ℕ) (f : ℕ) (a : Bool)
    (l : ℕ) (b d : Bool) (A : List Arc)
    (hg : scanGood c (k, some (f, a, l, b, d), A)) :
    l ≤ k ∧ d = colorAt c (k - l) := by
  obtain ⟨_, _, hk, hd⟩ := hg
  have hle : l ≤ k := by omega
  refine ⟨hle, ?_⟩
  have h := calc
    colorAt d l = colorAt c k := hd
    _ = colorAt c (k - l + l) := by rw [Nat.sub_add_cancel hle]
    _ = colorAt (colorAt c (k - l)) l := colorAt_add _ _ _
  by_cases hl : l % 2 = 0
  · simpa [colorAt, hl] using h
  · exact Bool.not_injective (by simpa only [colorAt, if_neg hl] using h)

abbrev OffsetScan := ℕ × Option (ℕ × Bool × ℕ × Bool) × List Arc

def offsetView : Scan → OffsetScan
  | (k, none, A) => (k, none, A)
  | (k, some (f, a, l, b, _), A) => (k, some (f, a, k - l, b), A)

def offsetStep (c : Bool) : OffsetScan → Option Bool → OffsetScan
  | (k, o, A), none => (k + 1, o, A)
  | (k, none, A), some a => (k + 1, some (k, a, k, a), A)
  | (k, some (f, a, l, b), A), some p =>
    (k + 1, some (f, a, k, p), (k - l, colorAt c l, Bool.xor b p) :: A)

def offsetClose (c : Bool) : OffsetScan → ℕ × List Arc
  | (k, none, _) => (1, [(k, c, false)])
  | (k, some (f, a, l, b), A) => (0, (k - l + f, colorAt c l, Bool.xor b a) :: A)

lemma offsetView_step (c : Bool) (s : Scan) (p : Option Bool) (h : scanGood c s) :
    offsetView (scanStep c s p) = offsetStep c (offsetView s) p := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩
  · cases p <;> simp [offsetView, scanStep, offsetStep]
  · obtain ⟨hle, hc⟩ := tailColor_eq_lastOffset c k f a l b d A h
    cases p with
    | none =>
      have hs : k + 1 - (l + 1) = k - l := by omega
      simp [offsetView, scanStep, offsetStep, hs]
    | some p =>
      have hs : k - (k - l) = l := by omega
      simp [offsetView, scanStep, offsetStep, hs, hc]

lemma offsetView_close (c : Bool) (s : Scan) (h : scanGood c s) :
    offsetClose c (offsetView s) = closeScan c s := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩
  · rfl
  · obtain ⟨hle, hc⟩ := tailColor_eq_lastOffset c k f a l b d A h
    have hs : k - (k - l) = l := by omega
    simp [offsetClose, offsetView, closeScan, hs, hc]

def offsetWord (c : Bool) (L : List (Option Bool)) : OffsetScan :=
  L.foldl (offsetStep c) (0, none, [])

lemma offsetWord_eq (c : Bool) (L : List (Option Bool)) :
    offsetWord c L = offsetView (scanWord c L) := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L p ih =>
    unfold offsetWord scanWord
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change offsetStep c (offsetWord c L) p = offsetView (scanStep c (scanWord c L) p)
    rw [ih, offsetView_step c _ p (scanWord_valid c L).2]

lemma offsetWord_close (c : Bool) (L : List (Option Bool)) :
    offsetClose c (offsetWord c L) = closeScan c (scanWord c L) := by
  rw [offsetWord_eq, offsetView_close c _ (scanWord_valid c L).2]

lemma offsetView_fields (c : Bool) (s : Scan) (hg : scanGood c s) :
    (offsetView s).1 = s.1 ∧ (offsetView s).2.2 = s.2.2 ∧
      (match (offsetView s).2.1 with
       | none => s.2.2 = []
       | some (f, _, l, _) => f ≤ l ∧ l < s.1 ∧ f + (s.1 - l) + arcLength s.2.2 = s.1) := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩
  · exact ⟨rfl, rfl, hg.2⟩
  · obtain ⟨_, hl, hk, _⟩ := hg
    refine ⟨rfl, rfl, ?_⟩
    change f ≤ k - l ∧ k - l < k ∧ f + (k - (k - l)) + arcLength A = k
    omega

lemma offsetWord_fields (c : Bool) (L : List (Option Bool)) :
    (offsetWord c L).1 = L.length ∧
      arcLength (offsetWord c L).2.2 ≤ L.length ∧
      (∀ q ∈ (offsetWord c L).2.2, 0 < q.1) ∧
      (match (offsetWord c L).2.1 with
       | none => (offsetWord c L).2.2 = []
       | some (f, _, l, _) =>
          f ≤ l ∧ l < L.length ∧ f + (L.length - l) + arcLength (offsetWord c L).2.2 = L.length) := by
  obtain ⟨hk, hg⟩ := scanWord_valid c L
  obtain ⟨hp, ha, hb⟩ := offsetView_fields c _ hg
  obtain ⟨hl, hpos⟩ := scanWord_partial c L
  rw [offsetWord_eq, ha]
  rw [hk] at hb
  exact ⟨hp.trans hk, hl, hpos, hb⟩

lemma offset_inventory_bounds (c : Bool) (L : List (Option Bool)) (hn : 0 < L.length) :
    arcLength (offsetClose c (offsetWord c L)).2 = L.length ∧
      ∀ q ∈ (offsetClose c (offsetWord c L)).2, 0 < q.1 := by
  rw [offsetWord_close]
  exact cycle_inventory_bounds c L hn

lemma offset_cycle_factor (w : Bool → R) (c : Bool) (L : List (Option Bool)) (he : L.length % 2 = 0) :
    portTrace (wordPorts w c L) =
      (2 : R) ^ (offsetClose c (offsetWord c L)).1 * arcProduct w (offsetClose c (offsetWord c L)).2 := by
  rw [offsetWord_close]
  exact cycle_factor w c L he

lemma offsetStep_no_pin (c : Bool) (s : OffsetScan) (p : Option Bool) :
    (offsetStep c s p).2.1 = none ↔ s.2.1 = none ∧ p = none := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b⟩ <;> cases p <;> simp [offsetStep]

lemma offsetWord_no_pin (c : Bool) (L : List (Option Bool)) :
    (offsetWord c L).2.1 = none ↔ ∀ p ∈ L, p = none := by
  induction L using List.reverseRecOn with
  | nil => simp [offsetWord]
  | append_singleton L p ih =>
    have h : offsetWord c (L ++ [p]) = offsetStep c (offsetWord c L) p := by
      simp [offsetWord, List.foldl_append]
    rw [h, offsetStep_no_pin, ih]
    constructor
    · rintro ⟨hL, rfl⟩ q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hL q hq
      · simpa using hq
    · intro hh
      exact ⟨fun q hq => hh q (List.mem_append_left _ hq), hh p (by simp)⟩

lemma offsetClose_one_iff (c : Bool) (s : OffsetScan) :
    (offsetClose c s).1 = 1 ↔ s.2.1 = none := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b⟩ <;> simp [offsetClose]

lemma offsetCycle_free (c : Bool) (L : List (Option Bool)) :
    (offsetClose c (offsetWord c L)).1 = 1 ↔ ∀ p ∈ L, p = none := by
  rw [offsetClose_one_iff, offsetWord_no_pin]

lemma arcProduct_append (w : Bool → R) (A B : List Arc) :
    arcProduct w (A ++ B) = arcProduct w A * arcProduct w B := by
  simp [arcProduct, List.prod_append]

lemma arcLength_append (A B : List Arc) :
    arcLength (A ++ B) = arcLength A + arcLength B := by
  simp [arcLength, List.sum_append]

lemma arcLength_ge (A : List Arc) (q : Arc) (hq : q ∈ A) : q.1 ≤ arcLength A := by
  induction A with
  | nil => simp at hq
  | cons a A ih =>
    simp only [arcLength, List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hq with hq | hq
    · subst a; omega
    · have hh := ih hq
      unfold arcLength at hh
      omega

def arcUniverse (M : ℕ) : Finset Arc :=
  (Finset.Icc 1 M).product (Finset.univ : Finset (Bool × Bool))

lemma arcProduct_inventory (w : Bool → R) (A : List Arc) (M : ℕ)
    (hp : ∀ q ∈ A, 0 < q.1) (hM : arcLength A ≤ M) :
    arcProduct w A = ∏ q ∈ arcUniverse M, arcFactor w q ^ A.count q := by
  rw [arcProduct, Finset.prod_list_map_count]
  refine Finset.prod_subset ?_ ?_
  · intro q hq
    have hq' := List.mem_toFinset.mp hq
    simp [arcUniverse, Nat.succ_le_of_lt (hp q hq'), le_trans (arcLength_ge A q hq') hM]
  · intro q _ hq
    rw [List.count_eq_zero_of_not_mem (fun h => hq (List.mem_toFinset.mpr h)), pow_zero]

abbrev CycleWord := Bool × List (Option Bool)

def layoutArcs (W : List CycleWord) : List Arc :=
  (W.map fun (c, L) => (offsetClose c (offsetWord c L)).2).flatten

def layoutFree (W : List CycleWord) : ℕ :=
  (W.map fun (c, L) => (offsetClose c (offsetWord c L)).1).sum

lemma layout_factor (w : Bool → R) (W : List CycleWord)
    (he : ∀ q ∈ W, q.2.length % 2 = 0) :
    (W.map fun (c, L) => portTrace (wordPorts w c L)).prod =
      (2 : R) ^ layoutFree W * arcProduct w (layoutArcs W) := by
  induction W with
  | nil => simp [layoutFree, layoutArcs, arcProduct]
  | cons q W ih =>
    obtain ⟨c, L⟩ := q
    have hq := offset_cycle_factor w c L (he (c, L) (List.mem_cons_self ..))
    have ht := ih (fun q hq => he q (List.mem_cons_of_mem _ hq))
    simp only [layoutFree, layoutArcs, List.map_cons, List.sum_cons, List.flatten_cons,
      List.prod_cons, pow_add, arcProduct_append]
    rw [hq, ht]
    unfold layoutArcs layoutFree
    ac_rfl

lemma layout_inventory_bounds (W : List CycleWord) (hn : ∀ q ∈ W, 0 < q.2.length) :
    arcLength (layoutArcs W) = (W.map fun q => q.2.length).sum ∧
      ∀ q ∈ layoutArcs W, 0 < q.1 := by
  induction W with
  | nil => simp [layoutArcs, arcLength]
  | cons q W ih =>
    obtain ⟨c, L⟩ := q
    obtain ⟨hl, hp⟩ := offset_inventory_bounds c L (hn (c, L) (List.mem_cons_self ..))
    obtain ⟨ht, htp⟩ := ih (fun q hq => hn q (List.mem_cons_of_mem _ hq))
    change arcLength ((offsetClose c (offsetWord c L)).2 ++ layoutArcs W) =
      L.length + (W.map fun q => q.2.length).sum ∧
      ∀ q ∈ (offsetClose c (offsetWord c L)).2 ++ layoutArcs W, 0 < q.1
    refine ⟨by rw [arcLength_append, hl, ht], ?_⟩
    intro q hq
    exact (List.mem_append.mp hq).elim (hp q) (htp q)

lemma layout_factor_inventory (w : Bool → R) (W : List CycleWord) (M : ℕ)
    (he : ∀ q ∈ W, q.2.length % 2 = 0) (hn : ∀ q ∈ W, 0 < q.2.length)
    (hM : (W.map fun q => q.2.length).sum ≤ M) :
    (W.map fun (c, L) => portTrace (wordPorts w c L)).prod =
      (2 : R) ^ layoutFree W * ∏ q ∈ arcUniverse M, arcFactor w q ^ (layoutArcs W).count q := by
  obtain ⟨hl, hp⟩ := layout_inventory_bounds W hn
  rw [layout_factor w W he, arcProduct_inventory w _ M hp (hl.le.trans hM)]

def headBit {m : ℕ} (x : Fin m → Bool) (b : Bool) : Bool :=
  if h : 0 < m then x ⟨0, h⟩ else b

def nextBit {m : ℕ} (x : Fin m → Bool) (b : Bool) (i : Fin m) : Bool :=
  if h : i.val + 1 < m then x ⟨i.val + 1, h⟩ else b

lemma headBit_cons {m : ℕ} (a : Bool) (x : Fin m → Bool) (b : Bool) :
    headBit (Fin.cons a x) b = a := by
  simp [headBit]

lemma nextBit_cons_zero {m : ℕ} (a : Bool) (x : Fin m → Bool) (b : Bool) :
    nextBit (Fin.cons a x) b 0 = headBit x b := by
  by_cases hm : 0 < m
  · have h : 1 < m + 1 := by omega
    rw [nextBit, dif_pos (show (0 : Fin (m + 1)).val + 1 < m + 1 from h), headBit, dif_pos hm]
    exact Fin.cons_succ (α := fun _ : Fin (m + 1) => Bool) a x ⟨0, hm⟩
  · have h : ¬1 < m + 1 := by omega
    simp [nextBit, headBit, h, hm]

lemma nextBit_cons_succ {m : ℕ} (a : Bool) (x : Fin m → Bool) (b : Bool) (i : Fin m) :
    nextBit (Fin.cons a x) b i.succ = nextBit x b i := by
  by_cases hm : i.val + 1 < m
  · have h : i.val + 1 + 1 < m + 1 := by omega
    rw [nextBit, dif_pos (show i.succ.val + 1 < m + 1 from h), nextBit, dif_pos hm]
    exact Fin.cons_succ (α := fun _ : Fin (m + 1) => Bool) a x ⟨i.val + 1, hm⟩
  · have h : ¬i.val + 1 + 1 < m + 1 := by omega
    simp [nextBit, h, hm]

lemma nextBit_cyclic {m : ℕ} (hm : 0 < m) (x : Fin m → Bool) (i : Fin m) :
    nextBit x (x ⟨0, hm⟩) i = x ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩ := by
  by_cases h : i.val + 1 < m
  · simp [nextBit, h, Nat.mod_eq_of_lt h]
  · have he : i.val + 1 = m := by have := i.isLt; omega
    simp [nextBit, h, he]

def wordWeight (w : Bool → R) (c : Bool) (L : List (Option Bool))
    (x : Fin L.length → Bool) (b : Bool) : R :=
  ∏ i : Fin L.length, letter w (colorAt c i.val) L[i.val] (x i) (nextBit x b i)

lemma wordWeight_cons (w : Bool → R) (c : Bool) (p : Option Bool) (L : List (Option Bool))
    (a : Bool) (x : Fin L.length → Bool) (b : Bool) :
    wordWeight w c (p :: L) (Fin.cons a x) b =
      letter w c p a (headBit x b) * wordWeight w (!c) L x b := by
  simp only [wordWeight, List.length_cons, Fin.prod_univ_succ, Fin.val_zero, List.getElem_cons_zero,
    Fin.cons_zero, nextBit_cons_zero, colorAt_zero, Fin.val_succ, List.getElem_cons_succ,
    Fin.cons_succ, nextBit_cons_succ, colorAt_succ, colorAt_flip]

lemma wordPorts_eq_sum (w : Bool → R) (c : Bool) (L : List (Option Bool)) (a b : Bool) :
    wordPorts w c L a b = ∑ x : Fin L.length → Bool,
      if headBit x b = a then wordWeight w c L x b else 0 := by
  induction L generalizing c a b with
  | nil => simp [wordPorts, portId, headBit, wordWeight, eq_comm]
  | cons p L ih =>
    let F (x : Fin (L.length + 1) → Bool) : R :=
      if headBit x b = a then wordWeight w c (p :: L) x b else 0
    change _ = ∑ x, F x
    have hr : (∑ q : Bool × (Fin L.length → Bool), F (Fin.cons q.1 q.2)) = ∑ x, F x :=
      Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (L.length + 1) => Bool)) F
    rw [← hr, Fintype.sum_prod_type]
    simp only [F, headBit_cons, wordWeight_cons, wordPorts, portComp]
    have H : (∑ u : Bool, ∑ x : Fin L.length → Bool,
        if u = a then letter w c p u (headBit x b) * wordWeight w (!c) L x b else 0) =
        ∑ x : Fin L.length → Bool, letter w c p a (headBit x b) * wordWeight w (!c) L x b := by
      cases a <;> simp [Fintype.sum_bool]
    rw [H]
    simp_rw [ih, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    cases h : headBit x b <;> simp [Fintype.sum_bool, h]

lemma trace_eq_sum (w : Bool → R) (c : Bool) (L : List (Option Bool)) (hn : 0 < L.length) :
    portTrace (wordPorts w c L) =
      ∑ x : Fin L.length → Bool, wordWeight w c L x (x ⟨0, hn⟩) := by
  unfold portTrace
  simp_rw [wordPorts_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  cases h : x ⟨0, hn⟩ <;> simp [headBit, hn, Fintype.sum_bool, h]

def colorCount (c : Bool) (L : List (Option Bool)) (x : Fin L.length → Bool)
    (b d : Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin L.length => colorAt c i.val = d ∧ x i ≠ nextBit x b i).card

def wordFits (L : List (Option Bool)) (x : Fin L.length → Bool) : Prop :=
  ∀ i : Fin L.length, L[i.val] = none ∨ L[i.val] = some (x i)

def wordFits_decidable (L : List (Option Bool)) (x : Fin L.length → Bool) : Decidable (wordFits L x) :=
  inferInstanceAs (Decidable (∀ i : Fin L.length, L[i.val] = none ∨ L[i.val] = some (x i)))

lemma wordWeight_eq_powers (w : Bool → R) (c : Bool) (L : List (Option Bool))
    (x : Fin L.length → Bool) (b : Bool) :
    wordWeight w c L x b = @ite R (wordFits L x) (wordFits_decidable L x)
      (w false ^ colorCount c L x b false * w true ^ colorCount c L x b true) 0 := by
  classical
  by_cases hp : wordFits L x
  · rw [if_pos hp]
    have h (i : Fin L.length) :
        letter w (colorAt c i.val) L[i.val] (x i) (nextBit x b i) =
          (if colorAt c i.val = false ∧ x i ≠ nextBit x b i then w false else 1) *
          (if colorAt c i.val = true ∧ x i ≠ nextBit x b i then w true else 1) := by
      rw [letter, if_pos (hp i)]
      cases hc : colorAt c i.val <;> by_cases hx : x i = nextBit x b i <;> simp [edgePort, hc, hx]
    simp_rw [wordWeight, h]
    rw [Finset.prod_mul_distrib]
    simp only [← Finset.prod_filter, Finset.prod_const, colorCount]
  · rw [if_neg hp]
    change ¬ (∀ i : Fin L.length, L[i.val] = none ∨ L[i.val] = some (x i)) at hp
    obtain ⟨i, hi⟩ := not_forall.mp hp
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [letter, hi])

open MvPolynomial

noncomputable def biDegree (r b : ℕ) : Bool →₀ ℕ := Finsupp.single false r + Finsupp.single true b

lemma biDegree_eq_iff (r b r' b' : ℕ) : biDegree r b = biDegree r' b' ↔ r = r' ∧ b = b' := by
  constructor
  · intro h
    exact ⟨by simpa [biDegree] using congrArg (fun d : Bool →₀ ℕ => d false) h,
      by simpa [biDegree] using congrArg (fun d : Bool →₀ ℕ => d true) h⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma X_pow_mul_X_pow (r b : ℕ) :
    (X false : MvPolynomial Bool ℕ) ^ r * X true ^ b = monomial (biDegree r b) 1 := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial]
  simp [biDegree]

lemma coeff_weighted_hist {A : Type*} [Fintype A] (p : A → Prop) [DecidablePred p]
    (r b : A → ℕ) (rr bb : ℕ) :
    (∑ x : A, if p x then
      (X false : MvPolynomial Bool ℕ) ^ (r x) * X true ^ (b x) else 0).coeff (biDegree rr bb) =
        (Finset.univ.filter fun x => p x ∧ r x = rr ∧ b x = bb).card := by
  rw [MvPolynomial.coeff_sum, Finset.card_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hp : p x <;>
    simp [hp, X_pow_mul_X_pow, MvPolynomial.coeff_monomial, biDegree_eq_iff]

def wrapNext {m : ℕ} (hm : 0 < m) (i : Fin m) : Fin m :=
  ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩

lemma trace_ofFn (w : Bool → R) (c : Bool) {m : ℕ}
    (p : Fin m → Option Bool) (hm : 0 < m) :
    portTrace (wordPorts w c (List.ofFn p)) =
      ∑ x : Fin m → Bool, ∏ i : Fin m, letter w (colorAt c i.val) (p i) (x i) (x (wrapNext hm i)) := by
  have hn : 0 < (List.ofFn p).length := by simpa using hm
  let e : Fin m ≃ Fin (List.ofFn p).length := finCongr List.length_ofFn.symm
  let f := Equiv.arrowCongr e (Equiv.refl Bool)
  have hv (i : Fin m) : (e i).val = i.val := rfl
  have he (i : Fin m) : e (wrapNext hm i) = wrapNext hn (e i) := by
    apply Fin.ext
    simp [wrapNext, hv]
  rw [trace_eq_sum w c _ hn, ← f.sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold wordWeight
  rw [← e.prod_comp]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [nextBit_cyclic, List.getElem_ofFn]
  have hi : (⟨(e i).val, by simpa using (e i).isLt⟩ : Fin m) = i := Fin.ext (hv i)
  change letter w (colorAt c (e i).val) (p ⟨(e i).val, _⟩) ((f x) (e i))
    ((f x) (wrapNext hn (e i))) = _
  have hf (j : Fin m) : f x (e j) = x j := by
    change x (e.symm (e j)) = x j
    rw [Equiv.symm_apply_apply]
  rw [← he, hf, hf, hi, hv]

variable {n : ℕ}

open Function

def pairPos (m : ℕ) : Bool × Fin m ≃ Fin (2 * m) where
  toFun q := ⟨2 * q.2.val + q.1.toNat, by
    obtain ⟨b, j⟩ := q
    have h := j.isLt
    cases b <;> simp [Bool.toNat] <;> omega⟩
  invFun i := (decide (i.val % 2 = 1), ⟨i.val / 2, by have := i.isLt; omega⟩)
  left_inv := by
    rintro ⟨b, j⟩
    apply Prod.ext
    · change decide ((2 * j.val + b.toNat) % 2 = 1) = b
      cases b
      · exact decide_eq_false (show ¬ (2 * j.val + 0) % 2 = 1 by omega)
      · exact decide_eq_true (show (2 * j.val + 1) % 2 = 1 by omega)
    · apply Fin.ext
      change (2 * j.val + b.toNat) / 2 = j.val
      cases b <;> simp [Bool.toNat] <;> omega
  right_inv := by
    intro i
    apply Fin.ext
    change 2 * (i.val / 2) + (decide (i.val % 2 = 1)).toNat = i.val
    rcases Nat.mod_two_eq_zero_or_one i.val with h | h <;> simp [h, Bool.toNat] <;> omega

lemma wrapNext_pair_false {m : ℕ} (hm : 0 < m) (j : Fin m) :
    wrapNext (by omega : 0 < 2 * m) (pairPos m (false, j)) = pairPos m (true, j) := by
  apply Fin.ext
  change (2 * j.val + 1) % (2 * m) = 2 * j.val + 1
  exact Nat.mod_eq_of_lt (by have := j.isLt; omega)

lemma wrapNext_pair_true {m : ℕ} (hm : 0 < m) (j : Fin m) :
    wrapNext (by omega : 0 < 2 * m) (pairPos m (true, j)) = pairPos m (false, wrapNext hm j) := by
  apply Fin.ext
  change (2 * j.val + 1 + 1) % (2 * m) = 2 * ((j.val + 1) % m)
  rw [show 2 * j.val + 1 + 1 = 2 * (j.val + 1) by omega, Nat.mul_mod_mul_left]

abbrev CyclePos (τ : Equiv.Perm (Fin n)) (r : Layout.Root τ) := Fin (2 * minimalPeriod τ r.val)

lemma cyclePos_positive (τ : Equiv.Perm (Fin n)) (r : Layout.Root τ) :
    0 < 2 * minimalPeriod τ r.val := by
  have := Layout.periodPos τ r.val
  omega

noncomputable def slotVertex (τ : Equiv.Perm (Fin n)) (r : Layout.Root τ) (i : CyclePos τ r) : Bool × Fin n :=
  let q := (pairPos (minimalPeriod τ r.val)).symm i
  (q.1, Layout.atSlot τ ⟨r, q.2⟩)

lemma slotVertex_pair (τ : Equiv.Perm (Fin n)) (r : Layout.Root τ)
    (q : Bool × Fin (minimalPeriod τ r.val)) :
    slotVertex τ r (pairPos _ q) = (q.1, Layout.atSlot τ ⟨r, q.2⟩) := by
  simp [slotVertex]

noncomputable def vertexEquiv (τ : Equiv.Perm (Fin n)) :
    (Σ r : Layout.Root τ, CyclePos τ r) ≃ Bool × Fin n :=
  (Equiv.sigmaCongrRight fun (r : Layout.Root τ) =>
    (pairPos (minimalPeriod τ r.val)).symm.trans (Equiv.prodComm _ _)).trans
    ((Equiv.sigmaProdDistrib (fun r : Layout.Root τ => Fin (minimalPeriod τ r.val)) Bool).symm.trans
      ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl Bool) (Layout.slotsEquiv τ))))

lemma vertexEquiv_apply (τ : Equiv.Perm (Fin n)) (r : Layout.Root τ) (i : CyclePos τ r) :
    vertexEquiv τ ⟨r, i⟩ = slotVertex τ r i := rfl

noncomputable def cycleWord (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r : Layout.Root τ) :
    List (Option Bool) := List.ofFn (fun i : CyclePos τ r => p (slotVertex τ r i))

lemma cycleWord_length (τ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r : Layout.Root τ) :
    (cycleWord τ p r).length = 2 * minimalPeriod τ r.val := by
  simp [cycleWord]

lemma slotVertex_color (τ : Equiv.Perm (Fin n)) (r : Layout.Root τ) (i : CyclePos τ r) :
    colorAt false i.val = (slotVertex τ r i).1 := by
  obtain ⟨⟨b, j⟩, rfl⟩ := (pairPos (minimalPeriod τ r.val)).surjective i
  rw [slotVertex_pair]
  change (if (2 * j.val + b.toNat) % 2 = 0 then false else !false) = b
  cases b <;> simp

def nextVertex (σ : Equiv.Perm (Fin n)) : Bool × Fin n → Bool × Fin n
  | (false, i) => (true, i)
  | (true, i) => (false, σ.symm i)

lemma slotVertex_next (σ : Equiv.Perm (Fin n)) (r : Layout.Root σ.symm) (i : CyclePos σ.symm r) :
    slotVertex σ.symm r (wrapNext (cyclePos_positive σ.symm r) i) =
      nextVertex σ (slotVertex σ.symm r i) := by
  obtain ⟨⟨b, j⟩, rfl⟩ := (pairPos (minimalPeriod σ.symm r.val)).surjective i
  have hm := Layout.periodPos σ.symm r.val
  cases b with
  | false => rw [wrapNext_pair_false hm, slotVertex_pair, slotVertex_pair] <;> rfl
  | true =>
    rw [wrapNext_pair_true hm, slotVertex_pair, slotVertex_pair]
    change (false, Layout.atSlot σ.symm ⟨r, wrapNext hm j⟩) =
      (false, σ.symm (Layout.atSlot σ.symm ⟨r, j⟩))
    rw [Layout.nextSlot σ.symm r j] <;> rfl

def compatible (p : Bool × Fin n → Option Bool) (x : Bool × Fin n → Bool) : Prop :=
  ∀ v, p v = none ∨ p v = some (x v)

def postedCount (σ : Equiv.Perm (Fin n)) (x : Bool × Fin n → Bool) (c : Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, if c then σ i else i))).card

def edgeCount (σ : Equiv.Perm (Fin n)) (x : Bool × Fin n → Bool) (c : Bool) : ℕ :=
  (Finset.univ.filter (fun v : Bool × Fin n => v.1 = c ∧ x v ≠ x (nextVertex σ v))).card

lemma edgeCount_eq_posted (σ : Equiv.Perm (Fin n)) (x : Bool × Fin n → Bool) (c : Bool) :
    edgeCount σ x c = postedCount σ x c := by
  classical
  unfold edgeCount postedCount
  rw [Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_bool, Finset.card_filter]
  cases c with
  | false => simp [nextVertex]
  | true =>
    simpa [nextVertex, ne_comm] using
      (Equiv.sum_comp σ (fun i => if x (true, i) ≠ x (false, σ.symm i) then (1 : ℕ) else 0)).symm

noncomputable def assignmentWeight (w : Bool → R) (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) (x : Bool × Fin n → Bool) : R := by
  classical
  exact if compatible p x then w false ^ postedCount σ x false * w true ^ postedCount σ x true else 0

lemma assignment_weight_eq (w : Bool → R) (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) (x : Bool × Fin n → Bool) :
    (∏ v : Bool × Fin n, letter w v.1 (p v) (x v) (x (nextVertex σ v))) = assignmentWeight w σ p x := by
  classical
  unfold assignmentWeight
  by_cases hp : compatible p x
  · rw [if_pos hp, ← edgeCount_eq_posted σ x false, ← edgeCount_eq_posted σ x true]
    have h (v : Bool × Fin n) :
        letter w v.1 (p v) (x v) (x (nextVertex σ v)) =
          (if v.1 = false ∧ x v ≠ x (nextVertex σ v) then w false else 1) *
          (if v.1 = true ∧ x v ≠ x (nextVertex σ v) then w true else 1) := by
      rw [letter, if_pos (hp v)]
      cases hc : v.1 <;> by_cases hx : x v = x (nextVertex σ v) <;> simp [edgePort, hc, hx]
    simp_rw [h]
    rw [Finset.prod_mul_distrib]
    simp only [← Finset.prod_filter, Finset.prod_const, edgeCount]
  · rw [if_neg hp]
    obtain ⟨v, hv⟩ := not_forall.mp (show ¬∀ v, p v = none ∨ p v = some (x v) from hp)
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [letter, hv])

noncomputable def cycleTraceProduct (w : Bool → R) (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) : R := by
  classical
  exact ∏ r : Layout.Root σ.symm, portTrace (wordPorts w false (cycleWord σ.symm p r))

lemma cycleTrace_eq_assignments (w : Bool → R) (τ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) (r : Layout.Root τ) :
    portTrace (wordPorts w false (cycleWord τ p r)) =
      ∑ x : CyclePos τ r → Bool, ∏ i : CyclePos τ r,
        letter w (colorAt false i.val) (p (slotVertex τ r i)) (x i)
          (x (wrapNext (cyclePos_positive τ r) i)) :=
  trace_ofFn w false _ (cyclePos_positive τ r)

set_option maxHeartbeats 1600000 in
lemma cycleTraceProduct_eq_weighted (w : Bool → R) (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) :
    cycleTraceProduct w σ p = ∑ x : Bool × Fin n → Bool, assignmentWeight w σ p x := by
  classical
  let e : (Bool × Fin n → Bool) ≃ ((r : Layout.Root σ.symm) → CyclePos σ.symm r → Bool) :=
    (Equiv.arrowCongr (vertexEquiv σ.symm).symm (Equiv.refl Bool)).trans
      (Equiv.piCurry (fun (_ : Layout.Root σ.symm) _ => Bool))
  have he (x : Bool × Fin n → Bool) (r : Layout.Root σ.symm) (i : CyclePos σ.symm r) :
      e x r i = x (slotVertex σ.symm r i) := by
    change x (vertexEquiv σ.symm ⟨r, i⟩) = x (slotVertex σ.symm r i)
    rw [vertexEquiv_apply]
  unfold cycleTraceProduct
  simp_rw [cycleTrace_eq_assignments w σ.symm p]
  rw [Fintype.prod_sum, ← e.sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← assignment_weight_eq]
  calc
    _ = ∏ r : Layout.Root σ.symm, ∏ i : CyclePos σ.symm r,
        letter w (slotVertex σ.symm r i).1 (p (slotVertex σ.symm r i))
          (x (slotVertex σ.symm r i)) (x (nextVertex σ (slotVertex σ.symm r i))) := by
      refine Finset.prod_congr rfl fun r _ => Finset.prod_congr rfl fun i _ => ?_
      rw [he, he, slotVertex_color, slotVertex_next]
    _ = ∏ q : (Σ r : Layout.Root σ.symm, CyclePos σ.symm r),
        letter w (vertexEquiv σ.symm q).1 (p (vertexEquiv σ.symm q))
          (x (vertexEquiv σ.symm q)) (x (nextVertex σ (vertexEquiv σ.symm q))) :=
      (Fintype.prod_sigma (fun q : (Σ r : Layout.Root σ.symm, CyclePos σ.symm r) =>
        letter w (vertexEquiv σ.symm q).1 (p (vertexEquiv σ.symm q))
          (x (vertexEquiv σ.symm q)) (x (nextVertex σ (vertexEquiv σ.symm q))))).symm
    _ = _ := (vertexEquiv σ.symm).prod_comp
      (fun v : Bool × Fin n => letter w v.1 (p v) (x v) (x (nextVertex σ v)))

noncomputable def histogram (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r b : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun x => compatible p x ∧ postedCount σ x false = r ∧ postedCount σ x true = b).card

lemma coeff_cycleTraceProduct (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r b : ℕ) :
    (cycleTraceProduct (fun c => X c : Bool → MvPolynomial Bool ℕ) σ p).coeff (biDegree r b) =
      histogram σ p r b := by
  classical
  rw [cycleTraceProduct_eq_weighted]
  exact coeff_weighted_hist (compatible p) (fun x => postedCount σ x false)
    (fun x => postedCount σ x true) r b

noncomputable def cycleWords (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    List CycleWord := by
  classical
  exact (Finset.univ : Finset (Layout.Root σ.symm)).toList.map
    (fun r => (false, cycleWord σ.symm p r))

lemma cycleWords_length (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    ((cycleWords σ p).map fun q => q.2.length).sum = 2 * n := by
  classical
  have h := Fintype.card_congr (Layout.slotsEquiv σ.symm)
  simp only [Layout.Active, Fintype.card_sigma, Fintype.card_fin] at h
  simp only [cycleWords, List.map_map, Function.comp_apply, cycleWord_length, Finset.sum_map_toList,
    ← Finset.mul_sum, h]

lemma cycleWords_member (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (q : CycleWord) (hq : q ∈ cycleWords σ p) :
    ∃ r : Layout.Root σ.symm, q = (false, cycleWord σ.symm p r) := by
  unfold cycleWords at hq
  obtain ⟨r, _, hr⟩ := List.mem_map.mp hq
  exact ⟨r, hr.symm⟩

lemma cycleTraceProduct_eq_inventory (w : Bool → R) (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) :
    cycleTraceProduct w σ p =
      (2 : R) ^ layoutFree (cycleWords σ p) *
        ∏ q ∈ arcUniverse (2 * n), arcFactor w q ^ (layoutArcs (cycleWords σ p)).count q := by
  classical
  have he (q : CycleWord) (hq : q ∈ cycleWords σ p) : q.2.length % 2 = 0 := by
    obtain ⟨r, rfl⟩ := cycleWords_member σ p q hq
    change (cycleWord σ.symm p r).length % 2 = 0
    rw [cycleWord_length]
    omega
  have hp (q : CycleWord) (hq : q ∈ cycleWords σ p) : 0 < q.2.length := by
    obtain ⟨r, rfl⟩ := cycleWords_member σ p q hq
    change 0 < (cycleWord σ.symm p r).length
    rw [cycleWord_length]
    exact cyclePos_positive _ _
  have h := layout_factor_inventory w (cycleWords σ p) (2 * n) he hp (cycleWords_length σ p).le
  simpa [cycleWords, cycleTraceProduct, List.map_map, Function.comp_apply] using h

lemma coeff_cycle_inventory (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r b : ℕ) :
    ((2 : MvPolynomial Bool ℕ) ^ layoutFree (cycleWords σ p) *
      ∏ q ∈ arcUniverse (2 * n), arcFactor (fun c => X c) q ^ (layoutArcs (cycleWords σ p)).count q).coeff
      (biDegree r b) =
        histogram σ p r b := by
  rw [← cycleTraceProduct_eq_inventory]
  exact coeff_cycleTraceProduct σ p r b

lemma coeff_posted_hist (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (r b : Fin (n + 1)) :
    ((2 : MvPolynomial Bool ℕ) ^ layoutFree (cycleWords σ p) *
      ∏ q ∈ arcUniverse (2 * n), arcFactor (fun c => X c) q ^ (layoutArcs (cycleWords σ p)).count q).coeff
      (biDegree r.val b.val) =
      ((Finset.univ : Finset (Bool × Fin n → Bool)).filter (fun x =>
        (∀ v, p v = none ∨ p v = some (x v)) ∧
        (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card = r.val ∧
        (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card = b.val)).card := by
  classical
  rw [coeff_cycle_inventory σ p r.val b.val]
  unfold histogram
  congr 1
  ext x
  simp [postedCount, compatible]

end ProfileFactor

namespace Scatter

open Compiler.Build LayoutCircuit

variable {n N : ℕ}

def offset {τ : Equiv.Perm (Fin n)} (a : Layout.Active τ) : Fin n :=
  ⟨a.2.val,a.2.isLt.trans_le (Layout.periodLe τ a.1.val)⟩

def route (edge : Mat n N) (field : Fin n → Fin n → Sig N) (i : Fin n) : Sig N :=
  anyFin fun r => anyFin fun j =>
    an (liveSignal edge r j) (an (matPow edge j.val r i) (field r j))

theorem route_slot (edge : Mat n N) (field : Fin n → Fin n → Sig N) (τ : Equiv.Perm (Fin n))
    (x : Fin N → Bool) (he : ∀ r t, edge r t x = decide (τ r = t)) (a : Layout.Active τ) :
    route edge field (Layout.atSlot τ a) x = field a.1.val (offset a) x := by
  apply Bool.eq_iff_iff.mpr
  simp only [route,anyFin_true,an,Bool.and_eq_true,liveSignal_spec edge τ x he,
    matPow_spec edge τ x he,decide_eq_true_eq]
  constructor
  · rintro ⟨r,j,⟨hr,hj⟩,heq,hbit⟩
    let b : Layout.Active τ := ⟨⟨r,hr⟩,⟨j.val,hj⟩⟩
    have hab : b = a := (Layout.atSlot_bij τ).1 heq
    change field b.1.val (offset b) x = true at hbit
    rwa [hab] at hbit
  · intro h
    exact ⟨a.1.val,offset a,⟨a.1.property,a.2.isLt⟩,rfl,h⟩

private def termCost (n : ℕ) := n*(2*n)+n+2*n+3
private def oneCost (n : ℕ) := n*(n*termCost n+n)+n
def cost (n : ℕ) := n*(n*n*(2*n))+4*n*oneCost n

private theorem single {A : Set (Sig N)} (edge : Mat n N) (field : Fin n → Fin n → Sig N) (i : Fin n)
    (hm : matOut edge n ⊆ A) (hf : ∀ r j, field r j ∈ A)
    (hz : (fun _ => false) ∈ A) (ho : (fun _ => true) ∈ A) :
    Build A {route edge field i} (oneCost n) := by
  let term (r j : Fin n) := an (liveSignal edge r j) (an (matPow edge j.val r i) (field r j))
  have ht (r j : Fin n) : Build A {term r j} (termCost n) := by
    let f := liveSignal edge r j
    let g := an (matPow edge j.val r i) (field r j)
    have H : Build A ({f} ∪ {g}) (n*(2*n)+n+2*n+1+1) :=
      bothG (liveSignalB edge r j hm ho) (andG (hm ⟨j.val,j.isLt.le,r,i,rfl⟩) (hf r j))
    exact relax (thenG H (andG (A := A ∪ ({f} ∪ {g})) (f := f) (g := g)
      (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)))) le_rfl le_rfl (by unfold termCost; omega)
  let row (r : Fin n) := anyFin (term r)
  have hr (r : Fin n) : Build A {row r} (n*termCost n+n) :=
    thenG (finG (term r) _ (ht r)) (anyFinB _ (fun j => Or.inr ⟨j,rfl⟩) (Or.inl hz))
  exact thenG (finG row _ hr) (anyFinB row (fun r => Or.inr ⟨r,rfl⟩) (Or.inl hz))

abbrev Marks (n N : ℕ) := Bool → Bool → Fin n → Fin n → Sig N

def out (edge : Mat n N) (mark : Marks n N) (i : Bool × Bool × Fin n) :=
  route edge (mark i.1 i.2.1) i.2.2

theorem build {A : Set (Sig N)} (edge : Mat n N) (mark : Marks n N)
    (he : ∀ r s, edge r s ∈ A) (hm : ∀ z b r j, mark z b r j ∈ A)
    (hz : (fun _ => false) ∈ A) (ho : (fun _ => true) ∈ A) :
    Build A (Set.range (out edge mark)) (cost n) := by
  have H := allG (A := A ∪ matOut edge n) (out edge mark) (oneCost n)
    (fun z => single edge (mark z.1 z.2.1) z.2.2 Set.subset_union_right (fun r j => Or.inl (hm _ _ r j))
      (Or.inl hz) (Or.inl ho))
  have hc : Fintype.card (Bool × Bool × Fin n) = 4*n := by simp; omega
  rw [hc] at H
  exact thenG (matPowB edge n he hz ho) H

theorem cost_bound (n : ℕ) : cost n ≤ (n+2)^6 := by
  unfold cost oneCost termCost
  ring_nf
  omega

abbrev Guess (n d : ℕ) := Fin d → Fin n × Fin n

def hasSlot {d : ℕ} (g : Guess n d) (r j : Fin n) : Bool :=
  decide (∃ a, (g a).1 = r ∧ j ≤ (g a).2)

def guardSig {d : ℕ} (edge : Mat n N) (g : Guess n d) : Sig N :=
  allFin fun r => allFin fun j => literal (liveSignal edge r j) (hasSlot g r j)

theorem matches_spec {d : ℕ} (edge : Mat n N) (g : Guess n d) (τ : Equiv.Perm (Fin n))
    (x : Fin N → Bool) (he : ∀ r t, edge r t x = decide (τ r = t)) :
    guardSig edge g x = true ↔ ∀ r j,
      ((∀ s, τ.SameCycle r s → r ≤ s) ∧ j.val < Function.minimalPeriod τ r ↔
        ∃ a, (g a).1 = r ∧ j ≤ (g a).2) := by
  simp only [guardSig,allFin_true,literal_true,hasSlot]
  apply forall_congr' fun r => forall_congr' fun j => ?_
  exact Bool.eq_iff_iff.trans (by rw [liveSignal_spec edge τ x he,decide_eq_true_eq])

private noncomputable def rootOf (τ : Equiv.Perm (Fin n)) (i : Fin n) : Layout.Root τ :=
  ((Layout.slotsEquiv τ).symm i).1

private theorem rootRelated (τ : Equiv.Perm (Fin n)) (i : Fin n) : τ.SameCycle (rootOf τ i).val i :=
  (Layout.cycleIff τ _ _).mpr ⟨_,((Layout.slotsEquiv τ).symm i).2.isLt,(Layout.slotsEquiv τ).apply_symm_apply i⟩

private noncomputable def lastSlot (τ : Equiv.Perm (Fin n)) (r : Fin n) : Fin n :=
  ⟨Function.minimalPeriod τ r-1,by
    have := Layout.periodPos τ r
    have := Layout.periodLe τ r
    omega⟩

def Coherent {d : ℕ} (g : Guess n d) := ∀ a b, (g a).1 = (g b).1 → (g a).2 = (g b).2

theorem matches_cover {d : ℕ} (edge : Mat n N) (σ : Equiv.Perm (Fin n)) (x : Fin N → Bool)
    (he : ∀ r t, edge r t x = decide (σ.symm r = t))
    (cover : ∃ seed : Fin d → Fin n, ∀ i, ∃ a : Fin d, ∃ k : Fin n, (σ^k.val) (seed a) = i) :
    ∃ g : Guess n d, Coherent g ∧ guardSig edge g x = true := by
  obtain ⟨seed,hs⟩ := cover
  let R (a : Fin d) := rootOf σ.symm (seed a)
  let g : Guess n d := fun a => ((R a).val,lastSlot σ.symm (R a).val)
  refine ⟨g,fun _ _ h => congrArg (lastSlot σ.symm) h,(matches_spec _ _ _ _ he).mpr ?_⟩
  intro r j
  constructor
  · rintro ⟨hr,hj⟩
    obtain ⟨a,k,hk⟩ := hs r
    have same : σ.SameCycle (seed a) r := by
      rw [←hk]
      exact (Equiv.Perm.SameCycle.refl σ _).pow_right
    have rel := (rootRelated σ.symm (seed a)).trans same.inv
    have eq : (R a).val = r := ((R a).property _ rel).antisymm (hr _ rel.symm)
    refine ⟨a,eq,?_⟩
    change j.val ≤ Function.minimalPeriod σ.symm (R a).val - 1
    rw [eq]
    omega
  · rintro ⟨a,ha,hj⟩
    change (R a).val = r at ha
    subst r
    refine ⟨(R a).property,?_⟩
    change j.val ≤ Function.minimalPeriod σ.symm (R a).val - 1 at hj
    have := Layout.periodPos σ.symm (R a).val
    omega

theorem matched_length {d : ℕ} (edge : Mat n N) (g : Guess n d) (τ : Equiv.Perm (Fin n))
    (x : Fin N → Bool) (he : ∀ r t, edge r t x = decide (τ r = t))
    (hc : Coherent g) (hg : guardSig edge g x = true) (a : Fin d) :
    (∀ s, τ.SameCycle (g a).1 s → (g a).1 ≤ s) ∧ (g a).2.val+1 = Function.minimalPeriod τ (g a).1 := by
  have H := (matches_spec edge g τ x he).mp hg
  have e := (H (g a).1 (g a).2).mpr ⟨a,rfl,le_rfl⟩
  have hp := Layout.periodPos τ (g a).1
  have hj : (lastSlot τ (g a).1).val < Function.minimalPeriod τ (g a).1 := by unfold lastSlot; dsimp; omega
  obtain ⟨b,hb,hl⟩ := (H _ (lastSlot τ (g a).1)).mp ⟨e.1,hj⟩
  rw [hc b a hb] at hl
  change Function.minimalPeriod τ (g a).1-1 ≤ (g a).2.val at hl
  exact ⟨e.1,by omega⟩

def guessCost (n d : ℕ) := n*(n*n*(2*n))+(n*n)^d*(n*(n*(n*(2*n)+n+2*n+2)+n)+n)

theorem build_guesses {A : Set (Sig N)} (edge : Mat n N) (d : ℕ)
    (he : ∀ r t, edge r t ∈ A) (hz : (fun _ => false) ∈ A) (ho : (fun _ => true) ∈ A) :
    Build A (Set.range (guardSig (d := d) edge)) (guessCost n d) := by
  let B := A ∪ matOut edge n
  have ho' : (fun _ => true) ∈ B := Or.inl ho
  have each (g : Guess n d) (r j : Fin n) : Build B {literal (liveSignal edge r j) (hasSlot g r j)}
      (n*(2*n)+n+2*n+2) := by
    have H := liveSignalB (A := B) edge r j Set.subset_union_right ho'
    have G := thenG H (literalB (liveSignal edge r j) (hasSlot g r j) (Or.inr rfl))
    exact relax G le_rfl le_rfl (by omega)
  have row (g : Guess n d) (r : Fin n) : Build B {allFin (fun j => literal (liveSignal edge r j) (hasSlot g r j))}
      (n*(n*(2*n)+n+2*n+2)+n) :=
    thenG (finG _ _ (each g r)) (allFinB _ (fun j => Or.inr ⟨j,rfl⟩) (Or.inl ho'))
  have one (g : Guess n d) : Build B {guardSig edge g} (n*(n*(n*(2*n)+n+2*n+2)+n)+n) :=
    thenG (finG _ _ (row g)) (allFinB _ (fun j => Or.inr ⟨j,rfl⟩) (Or.inl ho'))
  have h := allG _ _ one
  have card : Fintype.card (Guess n d) = (n*n)^d := by simp [Guess]
  rw [card] at h
  exact thenG (matPowB edge n he hz ho) h

theorem guessCost_bound (n d : ℕ) : guessCost n d ≤ (n+2)^(6*(d+1)) := by
  let B := n+2
  have h₁ : n*(n*n*(2*n)) ≤ B^5 := by dsimp [B]; ring_nf; omega
  have h₂ : n*(n*(n*(2*n)+n+2*n+2)+n)+n ≤ B^5 := by dsimp [B]; ring_nf; omega
  have h₃ : (n*n)^d ≤ B^(2*d) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by dsimp [B]; nlinarith : n*n ≤ B^2) d
  have h₄ : B^5 ≤ B^(2*d+5) := Nat.pow_le_pow_right (by dsimp [B]; omega) (by omega)
  calc
    guessCost n d ≤ B^(2*d+5) + B^(2*d)*B^5 := Nat.add_le_add (h₁.trans h₄) (Nat.mul_le_mul h₃ h₂)
    _ = B^(2*d+5)*2 := by rw [← pow_add]; omega
    _ ≤ B^(2*d+5)*B := Nat.mul_le_mul_left _ (by dsimp [B]; omega)
    _ = B^(2*d+5+1) := (pow_succ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by dsimp [B]; omega) (by omega)

def physical (edge : Mat n N) (mark : Marks n N) (x : Fin N → Bool) : Bool × Fin n → Option Bool :=
  fun v => if out edge mark (false,v) x then some (out edge mark (true,v) x) else none

def assigned (mark : Marks n N) (x : Fin N → Bool) (b : Bool) (r j : Fin n) : Option Bool :=
  if mark false b r j x then some (mark true b r j x) else none

theorem physical_slot (edge : Mat n N) (mark : Marks n N) (τ : Equiv.Perm (Fin n))
    (x : Fin N → Bool) (he : ∀ r t, edge r t x = decide (τ r = t)) (a : Layout.Active τ) (b : Bool) :
    physical edge mark x (b,Layout.atSlot τ a) = assigned mark x b a.1.val (offset a) := by
  unfold physical out assigned
  simp only [route_slot edge _ τ x he]

open ProfileFactor

noncomputable def assignedWord (mark : Marks n N) (x : Fin N → Bool)
    (τ : Equiv.Perm (Fin n)) (r : Layout.Root τ) : List (Option Bool) :=
  List.ofFn fun i : CyclePos τ r =>
    let q := (pairPos (Function.minimalPeriod τ r.val)).symm i
    assigned mark x q.1 r.val (offset (τ := τ) ⟨r,q.2⟩)

theorem word_correct (edge : Mat n N) (mark : Marks n N) (τ : Equiv.Perm (Fin n))
    (x : Fin N → Bool) (he : ∀ r t, edge r t x = decide (τ r = t)) (r : Layout.Root τ) :
    cycleWord τ (physical edge mark x) r = assignedWord mark x τ r := by
  unfold cycleWord assignedWord
  apply congrArg List.ofFn
  funext i
  obtain ⟨⟨b,j⟩,rfl⟩ := (pairPos (Function.minimalPeriod τ r.val)).surjective i
  rw [slotVertex_pair,Equiv.symm_apply_apply]
  exact physical_slot edge mark τ x he ⟨r,j⟩ b

noncomputable def assignedWords (mark : Marks n N) (x : Fin N → Bool)
    (σ : Equiv.Perm (Fin n)) : List CycleWord := by
  classical
  exact (Finset.univ : Finset (Layout.Root σ.symm)).toList.map
    (fun r => (false,assignedWord mark x σ.symm r))

theorem assigned_hist (edge : Mat n N) (mark : Marks n N) (σ : Equiv.Perm (Fin n))
    (x : Fin N → Bool) (he : ∀ r t, edge r t x = decide (σ.symm r = t)) (r b : Fin (n+1)) :
    let rows := assignedWords mark x σ
    ((2 : MvPolynomial Bool ℕ)^layoutFree rows *
      ∏ q ∈ arcUniverse (2*n), arcFactor (fun c => MvPolynomial.X c) q ^ (layoutArcs rows).count q).coeff
      (biDegree r.val b.val) =
      ((Finset.univ : Finset ((Bool × Fin n) → Bool)).filter (fun y =>
        (∀ v, physical edge mark x v = none ∨ physical edge mark x v = some (y v)) ∧
        (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,i))).card = r.val ∧
        (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,σ i))).card = b.val)).card := by
  have eqn : cycleWords σ (physical edge mark x) = assignedWords mark x σ := by
    simp only [cycleWords,assignedWords,word_correct edge mark σ.symm x he]
  dsimp only
  rw [←eqn]
  exact coeff_posted_hist σ (physical edge mark x) r b

end Scatter
end PEqualNP.Outside.L_pcx_386_aux

namespace PEqualNP.Outside.L_pcx_386.Placement

open PEqualNP.Outside.L_pcx_386.Core
open PEqualNP.Outside.L_pcx_386.Core.Compiler.Build

variable {N : ℕ}

def enabled {α : Type} (events : List (Sig N × α)) (x : Input N) : List α :=
  events.filterMap (fun e => if e.1 x then some e.2 else none)

theorem enabled_append {α : Type} (u v : List (Sig N × α)) (x : Input N) :
    enabled (u++v) x = enabled u x ++ enabled v x := List.filterMap_append ..

def scan {α S : Type} (f : S → α → S) (s : S) (events : List (Sig N × α)) (x : Input N) : S :=
  (enabled events x).foldl f s

private theorem signalCodes {A : Set (Sig N)} (b : Sig N) (hb : b ∈ A) :
    Build A (codes b) 1 := by
  apply relax (bothG (idle (A:=A) (B:=A) le_rfl) (notG hb)) le_rfl _ (by decide)
  rintro _ ⟨i,rfl⟩
  cases i
  · right
    change (eqBit b false) = nt b
    funext x; cases h : b x <;> simp [eqBit,nt,h]
  · left
    have eq : eqBit b true = b := by funext x; cases h : b x <;> simp [eqBit,h]
    exact eq ▸ hb

def stepCost (s : ℕ) := 1+s*((s*2)*2)

theorem scan_build {α S : Type} [Fintype S] [DecidableEq S] {A : Set (Sig N)}
    (f : S → α → S) (s : S) (L : List (Sig N × α))
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A) (hl : ∀ a ∈ L, a.1 ∈ A) :
    Build A (codes (scan f s L)) (L.length * stepCost (Fintype.card S)) := by
  induction L using List.reverseRecOn with
  | nil =>
    rw [show (scan (N:=N) f s []) = (fun _ => s) by funext x; rfl]
    simpa using idle (const_available h0 h1 s)
  | append_singleton L e ih =>
    have H := ih (fun a ha => hl a (List.mem_append_left _ ha))
    have G := signalCodes e.1 (hl e (by simp))
    let up (s : S) (on : Bool) := if on then f s e.2 else s
    have K := binary_codes (A := A ∪ (codes (scan f s L) ∪ codes e.1)) (Or.inl h0) (scan f s L) e.1 up
      (fun _ hf => Or.inr (Or.inl hf)) (fun _ hf => Or.inr (Or.inr hf))
    have eq : (fun x => up (scan f s L x) (e.1 x)) = scan f s (L++[e]) := by
      funext x; cases hx : e.1 x <;> simp [scan,enabled_append,enabled,hx,up,List.foldl_append]
    rw [eq] at K
    exact relax (thenG (bothG H G) K) le_rfl le_rfl (by simp [stepCost,Nat.succ_mul]; omega)

abbrev Picker (T : ℕ) (α : Type) := Fin (T+1) ⊕ α

def pickStep {T : ℕ} {α : Type} : Picker T α → α → Picker T α
  | .inr a, _ => .inr a
  | .inl r, a => if r.val = 0 then .inr a else .inl ⟨r.val-1,by omega⟩

def picked {T : ℕ} {α : Type} : Picker T α → Option α
  | .inl _ => none
  | .inr a => some a

lemma pick_fixed {T : ℕ} {α : Type} (a : α) (L : List α) :
    L.foldl (pickStep (T := T)) (.inr a) = .inr a := by
  induction L with
  | nil => rfl
  | cons h t ih => exact ih

lemma pick_correct {T : ℕ} {α : Type} (L : List α) (r : Fin (T+1)) :
    picked (L.foldl pickStep (.inl r)) = L[r.val]? := by
  induction L generalizing r with
  | nil => simp [picked]
  | cons a L ih =>
    simp only [List.foldl_cons,pickStep]
    split_ifs with h
    · rw [pick_fixed,h]; rfl
    · rw [ih]
      change L[r.val-1]? = (a::L)[r.val]?
      have e : r.val = (r.val-1)+1 := by omega
      conv_rhs => rw [e,List.getElem?_cons_succ]

def selectCost (T m len : ℕ) := len*stepCost ((T+1)+m)+(m+1)*(((T+1)+m)*2)

theorem kth_build {T : ℕ} {α : Type} [Fintype α] [DecidableEq α] {A : Set (Sig N)}
    (L : List (Sig N × α)) (k : Fin (T+1))
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A) (hl : ∀ a ∈ L, a.1 ∈ A) :
    Build A (codes fun x => (enabled L x)[k.val]?) (selectCost T (Fintype.card α) L.length) := by
  let init : Picker T α := .inl k
  have H := scan_build pickStep init L h0 h1 hl
  have G := unary_codes (A := A ∪ codes (scan pickStep init L)) (Or.inl h0) (Or.inl h1)
    (scan pickStep init L) picked Set.subset_union_right
  have e : (fun x => picked (scan pickStep init L x)) = (fun x => (enabled L x)[k.val]?) := by
    funext x; exact pick_correct _ _
  rw [e] at G
  simpa only [selectCost,Picker,Fintype.card_sum,Fintype.card_option,Fintype.card_fin] using thenG H G

abbrev Arc := ℕ × ℕ × Bool
def span (a : Arc) := a.1+a.2.1
def flip (a : Arc) := !a.2.2
def chunk (b : Bool) (a : Arc) : List (Option Bool) :=
  (some b :: List.replicate (span a) none).take (span a)

theorem chunk_length (b : Bool) (a : Arc) : (chunk b a).length = span a := by simp [chunk]

def render (b : Bool) : List Arc → List (Option Bool)
  | [] => []
  | a::L => chunk b a ++ render (xor b (flip a)) L

theorem render_length (b : Bool) (L : List Arc) : (render b L).length = (L.map span).sum := by
  induction L generalizing b with
  | nil => rfl
  | cons a L ih => simp [render,chunk_length,ih]

abbrev Seek (B : ℕ) := (Fin (B+1) × Bool) ⊕ Option Bool

def seekStep {B : ℕ} : Seek B → Arc → Seek B
  | .inr pin, _ => .inr pin
  | .inl (k,b), a =>
      if k.val < span a then .inr (if k.val=0 then some b else none)
      else .inl (⟨k.val-span a,by have := k.isLt; omega⟩,xor b (flip a))

def sought {B : ℕ} : Seek B → Option Bool
  | .inl _ => none
  | .inr pin => pin

private theorem seek_fixed {B : ℕ} (p : Option Bool) (L : List Arc) :
    L.foldl (seekStep (B:=B)) (.inr p) = .inr p := by
  induction L with
  | nil => rfl
  | cons a L ih => exact ih

theorem seek_render {B : ℕ} (L : List Arc) (k : Fin (B+1)) (b : Bool) :
    sought (L.foldl seekStep (.inl (k,b))) = (render b L).getD k.val none := by
  induction L generalizing k b with
  | nil => simp [sought,render]
  | cons a L ih =>
    simp only [List.foldl_cons,seekStep,render]
    split_ifs with hk hz
    · rw [seek_fixed,List.getD_append _ _ _ _ (by simpa [chunk_length] using hk),hz]
      simp [sought,chunk,List.getD_eq_getElem?_getD,List.getElem?_take,show 0<span a by omega]
    · rw [seek_fixed,List.getD_append _ _ _ _ (by simpa [chunk_length] using hk)]
      have e : k.val=k.val-1+1 := by omega
      change none = _
      rw [List.getD_eq_getElem?_getD,show (chunk b a)[k.val]? =
          (some b :: List.replicate (span a) none)[k.val]? from List.getElem?_take_of_lt hk]
      conv_rhs => rw [e,List.getElem?_cons_succ]
      simp [show k.val-1<span a by omega]
    · rw [List.getD_append_right _ _ _ _ (by rw [chunk_length];omega),chunk_length,ih]

abbrev Stage := Fin 3 × ℕ

def stages (T : ℕ) : List Stage :=
  (List.range T).map (fun i => (0,i)) ++ (List.range T).flatMap (fun i => [(1,i),(2,i)])

lemma stages_length (T : ℕ) : (stages T).length = 3*T := by
  simp [stages,List.length_flatMap,List.map_const']; omega

lemma stages_bound {T : ℕ} {a : Stage} (h : a ∈ stages T) : a.2 < T := by
  rcases List.mem_append.mp h with h | h
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    exact List.mem_range.mp hi
  · obtain ⟨i,hi,ha⟩ := List.mem_flatMap.mp h
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at ha
    rcases ha with rfl | rfl <;> exact List.mem_range.mp hi

abbrev Bank (N : ℕ) (α : Type) := Fin 3 → List (Sig N × α)

def ordinal {α : Type} (bank : Bank N α) (a : Stage) (x : Input N) : Option α :=
  (enabled (bank a.1) x)[a.2]?

def sequence {α : Type} (T : ℕ) (bank : Bank N α) (x : Input N) : List α :=
  (stages T).filterMap (fun a => ordinal bank a x)

def weave {α : Type} : List α → List α → List α
  | [], ys => ys
  | a::as, [] => a::as
  | a::as, b::bs => a::b::weave as bs

lemma ordinals_all {α : Type} (T : ℕ) (L : List α) (h : L.length ≤ T) :
    (List.range T).filterMap (fun i => L[i]?) = L := by
  induction T generalizing L with
  | zero => have he : L = [] := List.eq_nil_of_length_eq_zero (by omega); simp [he]
  | succ T ih =>
    cases L with
    | nil => simp
    | cons a xs =>
      rw [List.range_succ_eq_map]
      simp [List.filterMap_map,Function.comp_def,ih xs (by simpa using h)]

lemma ordinals_weave {α : Type} (T : ℕ) (L R : List α) (h : L.length ≤ T) (eq : L.length = R.length) :
    ((List.range T).flatMap fun i => L[i]?.toList ++ R[i]?.toList) = weave L R := by
  induction T generalizing L R with
  | zero =>
    have a : L = [] := List.eq_nil_of_length_eq_zero (by omega)
    have b : R = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [a,b,weave]
  | succ T ih =>
    cases L with
    | nil => have hr : R = [] := List.eq_nil_of_length_eq_zero eq.symm; simp [hr,weave]
    | cons a xs =>
      cases R with
      | nil => simp at eq
      | cons b ys =>
        rw [List.range_succ_eq_map]
        simp [List.flatMap_map,Function.comp_def,weave,ih xs ys (by simpa using h) (by simpa using eq)]

theorem sequence_exact {α : Type} (T : ℕ) (bank : Bank N α) (x : Input N)
    (h : ∀ c, (enabled (bank c) x).length ≤ T)
    (eq : (enabled (bank 1) x).length = (enabled (bank 2) x).length) :
    sequence T bank x = enabled (bank 0) x ++ weave (enabled (bank 1) x) (enabled (bank 2) x) := by
  simp only [sequence,stages,List.filterMap_append,List.filterMap_map,List.filterMap_flatMap,
    Function.comp_def,ordinal]
  rw [ordinals_all T _ (h 0),← ordinals_weave T _ _ (h 1) eq]
  congr 1
  apply List.flatMap_congr
  intro i _
  cases a : (enabled (bank 1) x)[i]? <;> cases b : (enabled (bank 2) x)[i]? <;> simp [a,b]

def codedRun {S α : Type} (f : S → α → S) (s : S) (L : List Stage)
    (read : Stage → Input N → Option α) (x : Input N) : S :=
  (L.filterMap (fun a => read a x)).foldl f s

theorem codedRun_build {S α : Type} [Fintype S] [DecidableEq S] [Fintype α] [DecidableEq α]
    {A : Set (Sig N)} (f : S → α → S) (s : S) (L : List Stage) (read : Stage → Input N → Option α) (cost : ℕ)
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A)
    (hc : ∀ a ∈ L, Build A (codes (read a)) cost) :
    Build A (codes (codedRun f s L read))
      (L.length*(cost + Fintype.card S*((Fintype.card S*(Fintype.card α+1))*2))) := by
  induction L using List.reverseRecOn with
  | nil =>
    rw [show codedRun f s [] read = fun _ => s by funext x; rfl]
    simpa using idle (const_available h0 h1 s)
  | append_singleton L e ih =>
    have H := ih (fun a ha => hc a (List.mem_append_left _ ha))
    have G := hc e (by simp)
    let up (s : S) (a : Option α) := a.elim s (f s)
    let prior := codedRun f s L read
    have K := binary_codes (A := A ∪ (codes prior ∪ codes (read e))) (Or.inl h0) prior (read e) up
      (fun _ hf => Or.inr (Or.inl hf)) (fun _ hf => Or.inr (Or.inr hf))
    have eq : (fun x => up (prior x) (read e x)) = codedRun f s (L++[e]) read := by
      funext x; cases hv : read e x <;> simp [prior,codedRun,List.foldl_append,hv,up]
    rw [eq] at K
    exact relax (thenG (bothG H G) K) le_rfl le_rfl (by simp [Nat.succ_mul];omega)

def stateSize (B : ℕ) := (B+1)*2+3
def positionCost (B T m L : ℕ) :=
  3*T*(selectCost T m L + stateSize B*((stateSize B*(m+1))*2))+3*(stateSize B*2)

def atPosition {α : Type} (T : ℕ) (desc : α → Arc) (bank : Bank N α) (k : ℕ) (x : Input N) :=
  (render false ((sequence T bank x).map desc)).getD k none

theorem position_build {T B : ℕ} {α : Type} [Fintype α] [DecidableEq α] {A : Set (Sig N)}
    (desc : α → Arc) (bank : Bank N α) (k : Fin (B+1)) (L : ℕ)
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A)
    (hl : ∀ c, (bank c).length ≤ L) (hf : ∀ c, ∀ e ∈ bank c, e.1 ∈ A) :
    Build A (codes (atPosition T desc bank k.val)) (positionCost B T (Fintype.card α) L) := by
  let init : Seek B := .inl (k,false)
  let f (z : Seek B) (a : α) := seekStep z (desc a)
  let q := codedRun f init (stages T) (ordinal bank)
  have ho (a : Stage) (ha : a ∈ stages T) : Build A (codes (ordinal bank a)) (selectCost T (Fintype.card α) L) := by
    let j : Fin (T+1) := ⟨a.2,(stages_bound ha).trans (Nat.lt_succ_self _)⟩
    exact relax (kth_build (bank a.1) j h0 h1 (hf a.1)) le_rfl le_rfl (by unfold selectCost;gcongr; exact hl _)
  have H := codedRun_build f init (stages T) (ordinal bank) _ h0 h1 ho
  have G := unary_codes (A := A ∪ codes q) (Or.inl h0) (Or.inl h1) q sought Set.subset_union_right
  have eq : (fun x => sought (q x)) = atPosition T desc bank k.val := by
    funext x
    rw [show q x = ((sequence T bank x).map desc).foldl seekStep init by simp [q,codedRun,sequence,List.foldl_map,f]]
    exact seek_render _ k false
  rw [eq] at G
  have st : Fintype.card (Seek B) = stateSize B := by simp [Seek,stateSize]
  simpa only [positionCost,st,stages_length,Fintype.card_option,Fintype.card_bool] using thenG H G

def maskedPin {α : Type} (T : ℕ) (desc : α → Arc) (bank : Bank N α) (skip : Sig N) (k : ℕ) (x : Input N) :=
  if skip x then none else atPosition T desc bank k x

def pinField (v : Input N → Option Bool) (p : Bool) : Sig N :=
  if p then eqBit v (some true) else nt (eqBit v none)

theorem read_field (v : Input N → Option Bool) (x : Input N) :
    (if pinField v false x then some (pinField v true x) else none) = v x := by
  cases h : v x with
  | none => simp [pinField,nt,eqBit,h]
  | some b => cases b <;> simp [pinField,nt,eqBit,h]

theorem pinField_build {T B : ℕ} {α : Type} [Fintype α] [DecidableEq α] {A : Set (Sig N)}
    (desc : α → Arc) (bank : Bank N α) (skip : Sig N) (k : Fin (B+1)) (p : Bool) (L : ℕ)
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A) (hs : skip ∈ A)
    (hl : ∀ c, (bank c).length ≤ L) (hf : ∀ c, ∀ e ∈ bank c, e.1 ∈ A) :
    Build A {pinField (maskedPin T desc bank skip k.val) p} (positionCost B T (Fintype.card α) L+38) := by
  let v := atPosition T desc bank k.val
  let z := maskedPin T desc bank skip k.val
  have H := bothG (position_build (T:=T) desc bank k L h0 h1 hl hf) (signalCodes skip hs)
  let A' := A ∪ (codes v ∪ codes skip)
  have G := binary_codes (A:=A') (Or.inl h0) v skip (fun b off => if off then none else b)
    (fun _ h => Or.inr (Or.inl h)) (fun _ h => Or.inr (Or.inr h))
  have ez : (fun x => if skip x then none else v x) = z := by funext x; rfl
  rw [ez] at G
  have H' : Build A (codes z) (positionCost B T (Fintype.card α) L+1+36) := by
    convert (thenG H G) using 1
    simp
  cases p
  · exact relax (thenG H' (notG (A:=A ∪ codes z) (Or.inr ⟨none,rfl⟩))) le_rfl le_rfl (by omega)
  · exact relax H' le_rfl (Set.singleton_subset_iff.mpr ⟨some true,rfl⟩) (by omega)

def allCost (d B T m L : ℕ) := d*(2*(B+1))*(positionCost B T m L+38)

theorem physicalFields {d T B : ℕ} {α : Type} [Fintype α] [DecidableEq α] {A : Set (Sig N)}
    (desc : α → Arc) (banks : Fin d → Bank N α) (skip : Fin d → Sig N) (L : ℕ)
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A) (hs : ∀ i, skip i ∈ A)
    (hl : ∀ i c, ((banks i) c).length ≤ L) (hf : ∀ i c, ∀ e ∈ (banks i) c, e.1 ∈ A) :
    Build A (Set.range (fun u : Fin d × Bool × Fin (B+1) =>
      pinField (maskedPin T desc (banks u.1) (skip u.1) u.2.2.val) u.2.1))
      (allCost d B T (Fintype.card α) L) := by
  simpa only [allCost,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] using
    (allG (A:=A) (fun u : Fin d × Bool × Fin (B+1) =>
      pinField (maskedPin T desc (banks u.1) (skip u.1) u.2.2.val) u.2.1) _
      (fun u => pinField_build (T:=T) desc (banks u.1) (skip u.1) u.2.2 u.2.1 L h0 h1 (hs u.1) (hl u.1) (hf u.1)))

theorem allCost_bound {d B T m L s : ℕ} (a : d ≤ s) (b : B ≤ s) (c : T ≤ s) (h : m ≤ s) (l : L ≤ s) :
    allCost d B T m L ≤ (s+2)^12 := by
  calc
    allCost d B T m L ≤ allCost s s s s s := by unfold allCost positionCost selectCost stateSize stepCost; gcongr
    _ ≤ _ := by unfold allCost positionCost selectCost stateSize stepCost; ring_nf; omega

abbrev Receipt (S d U : ℕ) := Fin S × Fin d × Bool × Fin U
abbrev Item (S : ℕ) := Fin S × Bool
def category (q : ℕ × ℕ) : Fin 3 := if q.1=q.2 then 0 else if q.2<q.1 then 1 else 2
def description {S : ℕ} (dims : Fin S → ℕ × ℕ) (u : Item S) : Arc :=
  ((dims u.1).1,(dims u.1).2,u.2)

def units {S d U : ℕ} (load : Receipt S d U → Sig N) (i : Fin d) (j : Fin S) (b : Bool) :=
  (List.finRange U).map (fun h => (load (j,i,b,h),(j,b)))

def bankOf {S d U : ℕ} (dims : Fin S → ℕ × ℕ) (load : Receipt S d U → Sig N) (i : Fin d) : Bank N (Item S) :=
  fun c => (List.finRange S).flatMap (fun j => if category (dims j)=c then units load i j true ++ units load i j false else [])

lemma bank_length {S d U : ℕ} (dims : Fin S → ℕ × ℕ) (load : Receipt S d U → Sig N) (i : Fin d) (c : Fin 3) :
    ((bankOf dims load i) c).length ≤ S*(2*U) := by
  have hl (l : List (Fin S)) : (l.flatMap (fun j => if category (dims j)=c then
      units load i j true ++ units load i j false else [])).length ≤ l.length*(2*U) := by
    induction l with
    | nil => simp
    | cons j l ih =>
      by_cases h : category (dims j)=c <;> simp [h,units,Nat.succ_mul] at ih ⊢ <;> omega
  simpa only [bankOf,List.length_finRange] using hl (List.finRange S)

lemma bank_mem {S d U : ℕ} {A : Set (Sig N)} (dims : Fin S → ℕ × ℕ) (load : Receipt S d U → Sig N)
    (hh : ∀ w, load w ∈ A) (i : Fin d) (c : Fin 3) {e} (he : e ∈ bankOf dims load i c) : e.1 ∈ A := by
  obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp he
  split_ifs at hj with h
  · rcases List.mem_append.mp hj with hu | hu <;> obtain ⟨k,_,rfl⟩ := List.mem_map.mp hu <;> exact hh _
  · simp at hj

private theorem units_prefix {α : Type} (a : α) (m U : ℕ) (h : m≤U) :
    (List.finRange U).filterMap (fun k => if k.val < m then some a else none) = List.replicate m a := by
  induction U generalizing m with
  | zero =>
    have hm : m=0 := by omega
    simp [hm]
  | succ U ih =>
    rw [List.finRange_succ]
    cases m with
    | zero => simp
    | succ m =>
      simp [List.filterMap_map,Function.comp_def,ih m (by omega),List.replicate_succ]

def emitted {S d : ℕ} (dims : Fin S → ℕ × ℕ) (count : Fin S → Fin d → Bool → ℕ) (i : Fin d) (c : Fin 3) :=
  (List.finRange S).flatMap (fun j => if category (dims j)=c then
    List.replicate (count j i true) (j,true) ++ List.replicate (count j i false) (j,false) else [])

theorem bank_receipts {S d U : ℕ} (dims : Fin S → ℕ × ℕ) (load : Receipt S d U → Sig N)
    (x : Input N) (count : Fin S → Fin d → Bool → ℕ) (le : ∀ j i b, count j i b ≤ U)
    (hw : ∀ j i b k, load (j,i,b,k) x = decide (k.val<count j i b)) (i : Fin d) (c : Fin 3) :
    enabled (bankOf dims load i c) x = emitted dims count i c := by
  have hu (j : Fin S) (b : Bool) : enabled (units load i j b) x = List.replicate (count j i b) (j,b) := by
    simpa [enabled,units,List.filterMap_map,Function.comp_def,hw] using units_prefix (j,b) _ _ (le j i b)
  unfold bankOf emitted
  generalize List.finRange S = l
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [List.flatMap_cons,enabled_append,ih]
    by_cases h : category (dims j)=c
    · simp only [h,ite_true,enabled_append,hu]
    · simp [h,enabled]

def shipmentCost (S d U B T : ℕ) := allCost d B T (S*2) (S*(2*U))

theorem shipFields {S d U B T : ℕ} {A : Set (Sig N)} (dims : Fin S → ℕ × ℕ) (load : Receipt S d U → Sig N)
    (skip : Fin d → Sig N) (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A)
    (hm : ∀ w, load w ∈ A) (hs : ∀ i, skip i ∈ A) :
    Build A (Set.range (fun u : Fin d × Bool × Fin (B+1) =>
      pinField (maskedPin T (description dims) (bankOf dims load u.1) (skip u.1) u.2.2.val) u.2.1))
      (shipmentCost S d U B T) := by
  simpa only [shipmentCost,Item,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] using
    physicalFields (B:=B) (T:=T) (description dims) (bankOf dims load) skip (S*(2*U)) h0 h1 hs
      (bank_length _ _) (fun i c _ h => bank_mem dims load hm i c h)

theorem postcompose_walk {S d U B T M : ℕ} {A : Set (Sig N)}
    (start : Fin M → Sig N) (edge : ℕ → Fin M → Fin M → Sig N)
    (label : ℕ → Fin M → Fin M → Receipt S d U → Sig N) (stagesN : ℕ) (last : Fin M)
    (dims : Fin S → ℕ × ℕ) (skip : Fin d → Sig N)
    (h0 : (fun _ => false) ∈ A) (h1 : (fun _ => true) ∈ A) (hs : ∀ i, skip i ∈ A)
    (hstart : ∀ i, start i ∈ A) (hedge : ∀ k<stagesN, ∀ i j, edge k i j ∈ A)
    (hlabel : ∀ k<stagesN, ∀ i j w, label k i j w ∈ A) :
    let row := walkCells start edge label stagesN
    let wire := fun u : Fin d × Bool × Fin (B+1) =>
      pinField (maskedPin T (description dims) (bankOf dims (row last).bits u.1) (skip u.1) u.2.2.val) u.2.1
    Build A ({(row last).ok} ∪ Set.range wire)
      (stagesN*traceCost M (S*(d*(2*U)))+shipmentCost S d U B T) ∧
      ∀ x, ((row last).ok x=true ↔ ∃ bits,TracePath start edge label x stagesN last bits) ∧
      ((row last).ok x=true → ∃ bits, TracePath start edge label x stagesN last bits ∧
        ∀ i k, (if wire (i,false,k) x then some (wire (i,true,k) x) else none) =
          maskedPin T (description dims) (bankOf dims (fun u _ => bits u) i) (skip i) k.val x) := by
  dsimp only
  let r := walkCells start edge label stagesN
  let E := A ∪ cellRow r
  have H := compile_walk start edge label stagesN h0 hstart hedge hlabel
  have G := shipFields (B:=B) (T:=T) dims (r last).bits skip (A:=E) (Or.inl h0) (Or.inl h1)
    (fun w => Or.inr (family_mem (i:=last) (Or.inr ⟨w,rfl⟩ : _ ∈ (r last).outputs))) (fun i => Or.inl (hs i))
  constructor
  · apply relax (seq H G) le_rfl _ (by simp [Receipt])
    rintro g (hg|hg)
    · exact Or.inl (family_mem (i:=last) (Or.inl hg : g ∈ (r last).outputs))
    · exact Or.inr hg
  · intro x
    have hc := walk_semantics start edge label x stagesN last
    refine ⟨hc.1,fun ok => ⟨fun u => (r last).bits u x,hc.2 ok,?_⟩⟩
    intro i k
    rw [read_field]
    have h (c : Fin 3) : enabled (bankOf dims (r last).bits i c) x =
        enabled (bankOf dims (fun u _ => (r last).bits u x) i c) x := by
      unfold bankOf
      generalize List.finRange S = l
      induction l with
      | nil => rfl
      | cons j l ih =>
        simp only [List.flatMap_cons,enabled_append,ih]
        split_ifs <;> simp [enabled_append,enabled,units,List.filterMap_map]
    change maskedPin T (description dims) (bankOf dims (r last).bits i) _ _ _ = _
    simp only [maskedPin,atPosition,sequence,ordinal,h]

end PEqualNP.Outside.L_pcx_386.Placement

namespace PEqualNP.Outside.L_pcx_386.Placement

open PEqualNP.Outside.L_pcx_386_aux.ProfileFactor hiding Arc
open PEqualNP.Outside.L_pcx_386.Core PEqualNP.Outside.L_pcx_386.Core.Compiler.Build

abbrev Tag := PEqualNP.Outside.L_pcx_386_aux.ProfileFactor.Arc

def exitSpin (b : Bool) : List Arc → Bool
  | [] => b
  | a::L => exitSpin (xor b (flip a)) L

def tags (c : Bool) : List Arc → List Tag
  | [] => []
  | a::L => (span a,c,flip a)::tags (colorAt c (span a)) L

def decodeTag (q : Tag) : Arc :=
  ((q.1 + (!q.2.1).toNat)/2,(q.1+q.2.1.toNat)/2,!q.2.2)

lemma chunk_succ {a : Arc} {k : ℕ} (h : span a = k+1) (b : Bool) :
    chunk b a = some b :: List.replicate k none := by simp [chunk,h]

private lemma none_pending (c : Bool) (k l p : ℕ) (s b d : Bool) (A : List Tag) (t : ℕ) :
    (List.replicate t none).foldl (scanStep c) (k,some (p,s,l,b,d),A) =
      (k+t,some (p,s,l+t,b,d),A) := by
  induction t generalizing k l with
  | zero => simp
  | succ t ih =>
    rw [List.replicate_succ,List.foldl_cons]
    change (List.replicate t none).foldl _ (k+1,some (p,s,l+1,b,d),A) = _
    rw [ih]
    rw [show k+1+t=k+(t+1) by omega,show l+1+t=l+(t+1) by omega]

private lemma none_empty (c : Bool) (k t : ℕ) :
    (List.replicate t none).foldl (scanStep c) (k,none,[]) = (k+t,none,[]) := by
  induction t generalizing k with
  | zero => simp
  | succ t ih =>
    rw [List.replicate_succ,List.foldl_cons]
    change (List.replicate t none).foldl _ (k+1,none,[]) = _
    rw [ih]
    congr 1; omega

private lemma chunk_pending {a : Arc} (h : 0 < span a)
    (c : Bool) (k l : ℕ) (first prev d b : Bool) (A : List Tag) :
    (chunk b a).foldl (scanStep c) (k,some (0,first,l,prev,d),A) =
      (k+span a,some (0,first,span a,b,colorAt c k),(l,d,xor prev b)::A) := by
  obtain ⟨t,ht⟩ := Nat.exists_eq_add_one_of_ne_zero h.ne'
  rw [chunk_succ ht,List.foldl_cons]
  change (List.replicate t none).foldl _ (k+1,some (0,first,1,b,colorAt c k),(l,d,xor prev b)::A) = _
  rw [none_pending,ht]
  rw [show k+1+t=k+(t+1) by omega,show 1+t=t+1 by omega]

private lemma chunk_first {a : Arc} (h : 0 < span a) (c b : Bool) :
    (chunk b a).foldl (scanStep c) (0,none,[]) =
      (span a,some (0,b,span a,b,c),[]) := by
  obtain ⟨t,ht⟩ := Nat.exists_eq_add_one_of_ne_zero h.ne'
  rw [chunk_succ ht,List.foldl_cons]
  change (List.replicate t none).foldl _ (1,some (0,b,1,b,colorAt c 0),[]) = _
  rw [none_pending,ht,colorAt_zero,Nat.add_comm 1 t]

private theorem finish_tail (c first prev d b : Bool) (k l : ℕ) (A : List Tag) (L : List Arc)
    (hpos : ∀ a ∈ L, 0<span a) (hc : exitSpin b L = first) :
    closeScan c ((render b L).foldl (scanStep c) (k,some (0,first,l,prev,d),A)) =
      (0,(tags (colorAt c k) L).reverse ++ ((l,d,xor prev b)::A)) := by
  induction L generalizing prev d b k l A with
  | nil =>
    change b = first at hc
    subst first
    simp [render,closeScan,tags]
  | cons a rest ih =>
    simp only [render,List.foldl_append,chunk_pending (hpos a List.mem_cons_self)]
    rw [ih (b:=xor b (flip a)) (hpos:=fun q hq => hpos q (List.mem_cons_of_mem _ hq)) (hc:=hc)]
    simp [tags,List.reverse_cons,List.append_assoc,colorAt_add]

theorem rendered_inventory (c b : Bool) {L : List Arc} (hn : L ≠ [])
    (hpos : ∀ a ∈ L, 0<span a) (hc : exitSpin b L = b) :
    closeScan c (scanWord c (render b L)) = (0,(tags c L).reverse) := by
  cases L with
  | nil => contradiction
  | cons a rest =>
    simp only [scanWord,render,List.foldl_append,chunk_first (hpos a List.mem_cons_self)]
    rw [finish_tail (hc:=hc) (hpos:=fun q hq => hpos q (List.mem_cons_of_mem _ hq))]
    simp [tags,List.reverse_cons]

theorem floating_inventory (c : Bool) (k : ℕ) :
    closeScan c (scanWord c (List.replicate k none)) = (1,[(k,c,false)]) := by
  simp [scanWord,none_empty,closeScan]

private theorem weave_tags {R B : List Arc}
    (hr : ∀ a ∈ R, a.1=a.2.1+1) (hb : ∀ a ∈ B, a.2.1=a.1+1) (he : R.length=B.length) :
    (tags false (weave R B)).map decodeTag = weave R B := by
  induction R generalizing B with
  | nil => have eq := List.eq_nil_of_length_eq_zero he.symm; simp [eq,weave,tags]
  | cons r rs ih =>
    cases B with
    | nil => simp at he
    | cons b bs =>
      have er := hr r List.mem_cons_self
      have eb := hb b List.mem_cons_self
      have cr : colorAt false (span r) = true := by simp [colorAt,span,show (r.1+r.2.1) % 2=1 by omega]
      have cb : colorAt true (span b) = false := by simp [colorAt,span,show (b.1+b.2.1) % 2=1 by omega]
      have xr : decodeTag (span r,false,flip r) = r := by
        rcases r with ⟨r,z,s⟩
        simp [decodeTag,span,flip]
        dsimp only at er
        omega
      have xb : decodeTag (span b,true,flip b) = b := by
        rcases b with ⟨r,z,s⟩
        simp [decodeTag,span,flip]
        dsimp only at eb
        omega
      simp [weave,tags,cr,cb,xr,xb,ih (fun a h => hr a (List.mem_cons_of_mem _ h))
        (fun a h => hb a (List.mem_cons_of_mem _ h)) (by simpa using he)]

theorem ordered_tags {D R B : List Arc}
    (hd : ∀ a ∈ D, a.1=a.2.1) (hr : ∀ a ∈ R, a.1=a.2.1+1) (hb : ∀ a ∈ B, a.2.1=a.1+1)
    (he : R.length=B.length) :
    (tags false (D++weave R B)).map decodeTag = D++weave R B := by
  induction D with
  | nil => simpa using weave_tags hr hb he
  | cons a L ih =>
    have h := hd a List.mem_cons_self
    have hc : colorAt false (span a) = false := by simp [colorAt,span,show (a.1+a.2.1) % 2=0 by omega]
    have hx : decodeTag (span a,false,flip a) = a := by
      rcases a with ⟨r,b,s⟩
      simp [decodeTag,span,flip]
      dsimp only at h
      omega
    simp [tags,hc,hx,ih (fun q hq => hd q (List.mem_cons_of_mem _ hq))]

theorem weave_perm {α : Type} : ∀ L R : List α, (weave L R).Perm (L++R)
  | [], R => by simp [weave]
  | x::xs, [] => by simp [weave]
  | x::xs, y::ys => by
    simp only [weave,List.cons_append]
    exact (((weave_perm xs ys).cons y).trans List.perm_middle.symm).cons x

theorem weave_map {α β : Type} (f : α → β) : ∀ L R, (weave L R).map f = weave (L.map f) (R.map f)
  | [], R => by simp [weave]
  | x::xs, [] => by simp [weave]
  | x::xs, y::ys => by simp [weave,weave_map f xs ys]

theorem render_count (b : Bool) (L : List Arc) (hpos : ∀ a ∈ L, 0<span a) :
    (render b L).countP Option.isSome = L.length := by
  induction L generalizing b with
  | nil => rfl
  | cons a L ih =>
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_one_of_ne_zero (hpos a List.mem_cons_self).ne'
    simp [render,chunk_succ hk,List.countP_append,ih _ (fun q h => hpos q (List.mem_cons_of_mem _ h))]

def word (floating : Bool) (L : List Arc) : List (Option Bool) :=
  if floating then List.replicate ((L.map span).sum) none else render false L

theorem position_word {N T : ℕ} {α : Type} (desc : α → Arc) (bank : Bank N α) (skip : Sig N)
    (k : ℕ) (x : Input N) :
    maskedPin T desc bank skip k x = (word (skip x) ((sequence T bank x).map desc)).getD k none := by
  cases h : skip x <;> simp [maskedPin,word,atPosition,h,List.getD_eq_getElem?_getD,List.getElem?_replicate]
  split <;> rfl

theorem pack_inventory (D R B : List Arc) (floating : Bool)
    (hd : ∀ a ∈ D, a.1=a.2.1) (hr : ∀ a ∈ R, a.1=a.2.1+1) (hb : ∀ a ∈ B, a.2.1=a.1+1)
    (he : R.length=B.length) (hn : D++weave R B ≠ [])
    (hpos : ∀ a ∈ D++weave R B, 0<span a) (hc : exitSpin false (D++weave R B)=false)
    (hs : floating=true → ∃ k, D++weave R B=[(k,k,true)]) :
    let L := D++weave R B
    let w := word floating L
    let z := closeScan false (scanWord false w)
    z.1=floating.toNat ∧ (z.2.map decodeTag).Perm (D++R++B) ∧
      w.countP Option.isSome + floating.toNat = (D++R++B).length := by
  let L := D++weave R B
  have hp : L.Perm (D++R++B) := by
    rw [List.append_assoc]
    exact List.Perm.append_left D (weave_perm R B)
  cases floating
  · simp only [word,Bool.false_eq_true,ite_false,Bool.toNat_false,Nat.add_zero,
      rendered_inventory false false hn hpos hc,List.map_reverse,ordered_tags hd hr hb he]
    exact ⟨trivial,(List.reverse_perm _).trans hp,(render_count _ _ hpos).trans hp.length_eq⟩
  · obtain ⟨k,hk⟩ := hs rfl
    have ht : decodeTag (k+k,false,false) = (k,k,true) := by simp [decodeTag]; omega
    have hpp : [(k,k,true)].Perm (D++R++B) := hk ▸ hp
    simp only [word,Bool.true_eq,ite_true,hk,List.map_singleton,List.sum_singleton,span,
      floating_inventory,List.map_cons,List.map_nil,ht,Bool.toNat_true]
    refine ⟨trivial,hpp,?_⟩
    rw [← hpp.length_eq]
    simp

theorem receipt_sequence {N S d U T : ℕ} (dims : Fin S → ℕ × ℕ) (load : Receipt S d U → Sig N)
    (x : Input N) (count : Fin S → Fin d → Bool → ℕ) (le : ∀ j i b, count j i b ≤ U)
    (hw : ∀ j i b k, load (j,i,b,k) x = decide (k.val<count j i b)) (i : Fin d)
    (hl : ∀ c, (emitted dims count i c).length ≤ T)
    (he : (emitted dims count i 1).length = (emitted dims count i 2).length) :
    let bag := fun c => (emitted dims count i c).map (description dims)
    (sequence T (bankOf dims load i) x).map (description dims) = bag 0 ++ weave (bag 1) (bag 2) := by
  have h := bank_receipts dims load x count le hw i
  dsimp only
  rw [sequence_exact _ _ _ (by simpa only [h] using hl) (by simpa only [h] using he)]
  simp only [h,List.map_append,weave_map]

end PEqualNP.Outside.L_pcx_386.Placement

namespace PEqualNP.Outside.L_pcx_386.Homogeneous

open PEqualNP.Outside.L_pcx_386_aux
open PEqualNP.Outside.L_pcx_386_aux.ProfileFactor
open PEqualNP.Outside.L_pcx_386.Core
variable {R : Type*} [CommSemiring R] {n : ℕ}

def edgePort (w : Bool → Bool → R) (c : Bool) : Ports R :=
  fun a b => if a = b then w c false else w c true

def letter (w : Bool → Bool → R) (c : Bool) (p : Option Bool) : Ports R :=
  fun a b => if p = none ∨ p = some a then edgePort w c a b else 0

lemma letter_none (w : Bool → Bool → R) (c : Bool) : letter w c none = edgePort w c := by
  funext a b
  simp [letter]

lemma portComp_letter_some (A : Ports R) (w : Bool → Bool → R) (c p a b : Bool) :
    portComp A (letter w c (some p)) a b = A a p * edgePort w c p b := by
  cases p <;> simp [portComp, letter, Fintype.sum_bool]

lemma portComp_rank_one (u v : Bool → R) (A : Ports R) (a b : Bool) :
    portComp (fun i j => u i * v j) A a b = u a * portComp (fun _ j => v j) A a b := by
  simp only [portComp, Finset.mul_sum, mul_assoc]

def freePath (w : Bool → Bool → R) : Bool → ℕ → Ports R
  | _, 0 => portId
  | c, k + 1 => portComp (edgePort w c) (freePath w (!c) k)

lemma freePath_one (w : Bool → Bool → R) (c : Bool) : freePath w c 1 = edgePort w c := by
  simpa only [freePath] using portComp_right_id (edgePort w c)

lemma freePath_add (w : Bool → Bool → R) (c : Bool) (m k : ℕ) :
    freePath w c (m + k) = portComp (freePath w c m) (freePath w (colorAt c m) k) := by
  induction m generalizing c with
  | zero => simp [freePath, colorAt_zero, portComp_left_id]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [freePath, colorAt_succ, ← colorAt_flip, portComp_assoc]
    rw [ih]

lemma freePath_appendEdge (w : Bool → Bool → R) (c : Bool) (k : ℕ) :
    portComp (freePath w c k) (edgePort w (colorAt c k)) = freePath w c (k + 1) := by
  rw [freePath_add, freePath_one]

lemma freePath_flip (w : Bool → Bool → R) (c : Bool) (k : ℕ) (a b : Bool) :
    freePath w c k (!a) (!b) = freePath w c k a b := by
  induction k generalizing c a b with
  | zero => cases a <;> cases b <;> rfl
  | succ k ih =>
    have h₀ := ih (!c) false b
    have h₁ := ih (!c) true b
    cases a <;> cases b <;>
      simp [freePath, portComp, Fintype.sum_bool, edgePort] at h₀ h₁ ⊢ <;>
      rw [h₀, h₁] <;> ac_rfl

def arcFactor (w : Bool → Bool → R) (q : Arc) : R := freePath w q.2.1 q.1 false q.2.2

lemma freePath_eq_arcFactor (w : Bool → Bool → R) (c : Bool) (k : ℕ) (a b : Bool) :
    freePath w c k a b = arcFactor w (k, c, Bool.xor a b) := by
  cases a <;> cases b
  · rfl
  · rfl
  · exact freePath_flip w c k false true
  · exact freePath_flip w c k false false

lemma arcFactor_zero (w : Bool → Bool → R) (c p : Bool) :
    arcFactor w (0, c, p) = if p = false then 1 else 0 := by
  cases p <;> simp [arcFactor, freePath, portId]

def wordPorts (w : Bool → Bool → R) : Bool → List (Option Bool) → Ports R
  | _, [] => portId
  | c, p :: ps => portComp (letter w c p) (wordPorts w (!c) ps)

lemma wordPorts_append (w : Bool → Bool → R) (c : Bool) (L M : List (Option Bool)) :
    wordPorts w c (L ++ M) = portComp (wordPorts w c L) (wordPorts w (colorAt c L.length) M) := by
  induction L generalizing c with
  | nil => simp [wordPorts, colorAt_zero, portComp_left_id]
  | cons p L ih =>
    simp only [List.cons_append, List.length_cons, wordPorts, colorAt_succ, ← colorAt_flip,
      portComp_assoc]
    rw [ih]

def arcProduct (w : Bool → Bool → R) (A : List Arc) : R := (A.map (arcFactor w)).prod

def scanPorts (w : Bool → Bool → R) (c : Bool) : Scan → Ports R
  | (k, none, _) => freePath w c k
  | (_, some (f, a, l, b, d), A) => fun u v =>
    (arcProduct w A * freePath w c f u a) * freePath w d l b v

lemma scanStep_ports (w : Bool → Bool → R) (c : Bool) (s : Scan) (p : Option Bool)
    (h : scanGood c s) :
    scanPorts w c (scanStep c s p) = portComp (scanPorts w c s) (letter w (colorAt c s.1) p) := by
  funext u v
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩
  · cases p with
    | none =>
      change freePath w c (k + 1) u v = portComp (freePath w c k) (letter w (colorAt c k) none) u v
      rw [letter_none, freePath_appendEdge]
    | some a =>
      have he : A = [] := h.2
      subst A
      change ((1 : R) * freePath w c k u a) * freePath w (colorAt c k) 1 a v =
        portComp (freePath w c k) (letter w (colorAt c k) (some a)) u v
      rw [portComp_letter_some, freePath_one, one_mul]
  · obtain ⟨_, _, _, hd⟩ := h
    cases p with
    | none =>
      change (arcProduct w A * freePath w c f u a) * freePath w d (l + 1) b v =
        portComp (fun i j => (arcProduct w A * freePath w c f i a) * freePath w d l b j)
          (letter w (colorAt c k) none) u v
      rw [letter_none, portComp_rank_one, ← hd, ← freePath_appendEdge] <;> rfl
    | some p =>
      change ((arcFactor w (l, d, Bool.xor b p) * arcProduct w A) * freePath w c f u a) *
          freePath w (colorAt c k) 1 p v =
        portComp (fun i j => (arcProduct w A * freePath w c f i a) * freePath w d l b j)
          (letter w (colorAt c k) (some p)) u v
      rw [portComp_letter_some, freePath_one, freePath_eq_arcFactor w d l b p]
      ac_rfl

lemma scanWord_spec (w : Bool → Bool → R) (c : Bool) (L : List (Option Bool)) :
    (scanWord c L).1 = L.length ∧ scanGood c (scanWord c L) ∧
    scanPorts w c (scanWord c L) = wordPorts w c L := by
  induction L using List.reverseRecOn with
  | nil => simp [scanWord, scanGood, scanPorts, wordPorts, freePath]
  | append_singleton L p ih =>
    obtain ⟨hk, hg, hp⟩ := ih
    have hs : scanWord c (L ++ [p]) = scanStep c (scanWord c L) p := by
      simp [scanWord, List.foldl_append]
    refine ⟨by simp [hs, scanStep_pos, hk], ?_, ?_⟩
    · rw [hs]
      exact scanStep_good c _ p hg
    · rw [hs, scanStep_ports _ _ _ _ hg, hp, hk, wordPorts_append]
      simp [wordPorts, portComp_right_id]

lemma closeScan_factor (w : Bool → Bool → R) (c : Bool) (s : Scan)
    (hg : scanGood c s) (he : s.1 % 2 = 0) :
    portTrace (scanPorts w c s) = (2 : R) ^ (closeScan c s).1 * arcProduct w (closeScan c s).2 := by
  rcases s with ⟨k, o, A⟩
  rcases o with _ | ⟨f, a, l, b, d⟩
  · change (∑ x : Bool, freePath w c k x x) = (2 : R) ^ 1 * (arcFactor w (k, c, false) * 1)
    have h : freePath w c k true true = freePath w c k false false :=
      freePath_flip w c k false false
    rw [Fintype.sum_bool, pow_one, mul_one, two_mul, h] <;> rfl
  · obtain ⟨_, _, _, hd⟩ := hg
    change k % 2 = 0 at he
    have hc : colorAt d l = c := hd.trans (colorAt_even c he)
    have H : (∑ x : Bool, (arcProduct w A * freePath w c f x a) * freePath w d l b x) =
        arcProduct w A * portComp (freePath w d l) (freePath w c f) b a := by
      simp only [portComp, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ac_rfl
    change (∑ x : Bool, (arcProduct w A * freePath w c f x a) * freePath w d l b x) =
        (2 : R) ^ 0 * (arcFactor w (l + f, d, Bool.xor b a) * arcProduct w A)
    rw [H, ← hc, ← freePath_add, freePath_eq_arcFactor w d (l + f) b a, pow_zero, one_mul, mul_comm]

lemma cycle_factor (w : Bool → Bool → R) (c : Bool) (L : List (Option Bool)) (he : L.length % 2 = 0) :
    portTrace (wordPorts w c L) =
      (2 : R) ^ (closeScan c (scanWord c L)).1 * arcProduct w (closeScan c (scanWord c L)).2 := by
  obtain ⟨hk, hg, hp⟩ := scanWord_spec w c L
  rw [← hp]
  apply closeScan_factor w c _ hg
  rw [hk]
  exact he

def wordWeight (w : Bool → Bool → R) (c : Bool) (L : List (Option Bool))
    (x : Fin L.length → Bool) (b : Bool) : R :=
  ∏ i : Fin L.length, letter w (colorAt c i.val) L[i.val] (x i) (nextBit x b i)

lemma wordWeight_cons (w : Bool → Bool → R) (c : Bool) (p : Option Bool) (L : List (Option Bool))
    (a : Bool) (x : Fin L.length → Bool) (b : Bool) :
    wordWeight w c (p :: L) (Fin.cons a x) b =
      letter w c p a (headBit x b) * wordWeight w (!c) L x b := by
  simp only [wordWeight, List.length_cons, Fin.prod_univ_succ, Fin.val_zero, List.getElem_cons_zero,
    Fin.cons_zero, nextBit_cons_zero, colorAt_zero, Fin.val_succ, List.getElem_cons_succ,
    Fin.cons_succ, nextBit_cons_succ, colorAt_succ, colorAt_flip]

lemma wordPorts_eq_sum (w : Bool → Bool → R) (c : Bool) (L : List (Option Bool)) (a b : Bool) :
    wordPorts w c L a b = ∑ x : Fin L.length → Bool,
      if headBit x b = a then wordWeight w c L x b else 0 := by
  induction L generalizing c a b with
  | nil => simp [wordPorts, portId, headBit, wordWeight, eq_comm]
  | cons p L ih =>
    let F (x : Fin (L.length + 1) → Bool) : R :=
      if headBit x b = a then wordWeight w c (p :: L) x b else 0
    change _ = ∑ x, F x
    have hr : (∑ q : Bool × (Fin L.length → Bool), F (Fin.cons q.1 q.2)) = ∑ x, F x :=
      Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (L.length + 1) => Bool)) F
    rw [← hr, Fintype.sum_prod_type]
    simp only [F, headBit_cons, wordWeight_cons, wordPorts, portComp]
    have H : (∑ u : Bool, ∑ x : Fin L.length → Bool,
        if u = a then letter w c p u (headBit x b) * wordWeight w (!c) L x b else 0) =
        ∑ x : Fin L.length → Bool, letter w c p a (headBit x b) * wordWeight w (!c) L x b := by
      cases a <;> simp [Fintype.sum_bool]
    rw [H]
    simp_rw [ih, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    cases h : headBit x b <;> simp [Fintype.sum_bool, h]

lemma trace_eq_sum (w : Bool → Bool → R) (c : Bool) (L : List (Option Bool)) (hn : 0 < L.length) :
    portTrace (wordPorts w c L) =
      ∑ x : Fin L.length → Bool, wordWeight w c L x (x ⟨0, hn⟩) := by
  unfold portTrace
  simp_rw [wordPorts_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  cases h : x ⟨0, hn⟩ <;> simp [headBit, hn, Fintype.sum_bool, h]

lemma trace_ofFn (w : Bool → Bool → R) (c : Bool) {m : ℕ}
    (p : Fin m → Option Bool) (hm : 0 < m) :
    portTrace (wordPorts w c (List.ofFn p)) =
      ∑ x : Fin m → Bool, ∏ i : Fin m, letter w (colorAt c i.val) (p i) (x i) (x (wrapNext hm i)) := by
  have hn : 0 < (List.ofFn p).length := by simpa using hm
  let e : Fin m ≃ Fin (List.ofFn p).length := finCongr List.length_ofFn.symm
  let f := Equiv.arrowCongr e (Equiv.refl Bool)
  have hv (i : Fin m) : (e i).val = i.val := rfl
  have he (i : Fin m) : e (wrapNext hm i) = wrapNext hn (e i) := by
    apply Fin.ext
    simp [wrapNext, hv]
  rw [trace_eq_sum w c _ hn, ← f.sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold wordWeight
  rw [← e.prod_comp]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [nextBit_cyclic, List.getElem_ofFn]
  have hi : (⟨(e i).val, by simpa using (e i).isLt⟩ : Fin m) = i := Fin.ext (hv i)
  change letter w (colorAt c (e i).val) (p ⟨(e i).val, _⟩) ((f x) (e i))
    ((f x) (wrapNext hn (e i))) = _
  have hf (j : Fin m) : f x (e j) = x j := by
    change x (e.symm (e j)) = x j
    rw [Equiv.symm_apply_apply]
  rw [← he, hf, hf, hi, hv]

noncomputable def assignmentWeight (w : Bool → Bool → R) (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) (x : Bool × Fin n → Bool) : R := by
  classical
  exact if compatible p x then ∏ i : Bool × Fin n, edgePort w i.1 (x i) (x (nextVertex σ i)) else 0

lemma assignment_weight_eq (w : Bool → Bool → R) (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) (x : Bool × Fin n → Bool) :
    (∏ i : Bool × Fin n, letter w i.1 (p i) (x i) (x (nextVertex σ i))) = assignmentWeight w σ p x := by
  classical
  by_cases h : compatible p x
  · rw [assignmentWeight,if_pos h]
    exact Finset.prod_congr rfl (fun i _ => if_pos (h i))
  · obtain ⟨i,hi⟩ := not_forall.mp (show ¬ ∀ i, p i = none ∨ p i = some (x i) from h)
    simp only [assignmentWeight,if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [letter,hi])

noncomputable def cycleTraceProduct (w : Bool → Bool → R) (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) : R := by
  classical
  exact ∏ r : Layout.Root σ.symm, portTrace (wordPorts w false (cycleWord σ.symm p r))

lemma cycleTrace_eq_assignments (w : Bool → Bool → R) (τ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) (r : Layout.Root τ) :
    portTrace (wordPorts w false (cycleWord τ p r)) =
      ∑ x : CyclePos τ r → Bool, ∏ i : CyclePos τ r,
        letter w (colorAt false i.val) (p (slotVertex τ r i)) (x i)
          (x (wrapNext (cyclePos_positive τ r) i)) :=
  trace_ofFn w false _ (cyclePos_positive τ r)

set_option maxHeartbeats 1600000 in
lemma cycleTraceProduct_eq_weighted (w : Bool → Bool → R) (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) :
    cycleTraceProduct w σ p = ∑ x : Bool × Fin n → Bool, assignmentWeight w σ p x := by
  classical
  let e : (Bool × Fin n → Bool) ≃ ((r : Layout.Root σ.symm) → CyclePos σ.symm r → Bool) :=
    (Equiv.arrowCongr (vertexEquiv σ.symm).symm (Equiv.refl Bool)).trans
      (Equiv.piCurry (fun (_ : Layout.Root σ.symm) _ => Bool))
  have he (x : Bool × Fin n → Bool) (r : Layout.Root σ.symm) (i : CyclePos σ.symm r) :
      e x r i = x (slotVertex σ.symm r i) := by
    change x (vertexEquiv σ.symm ⟨r, i⟩) = x (slotVertex σ.symm r i)
    rw [vertexEquiv_apply]
  unfold cycleTraceProduct
  simp_rw [cycleTrace_eq_assignments w σ.symm p]
  rw [Fintype.prod_sum, ← e.sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← assignment_weight_eq]
  calc
    _ = ∏ r : Layout.Root σ.symm, ∏ i : CyclePos σ.symm r,
        letter w (slotVertex σ.symm r i).1 (p (slotVertex σ.symm r i))
          (x (slotVertex σ.symm r i)) (x (nextVertex σ (slotVertex σ.symm r i))) := by
      refine Finset.prod_congr rfl fun r _ => Finset.prod_congr rfl fun i _ => ?_
      rw [he, he, slotVertex_color, slotVertex_next]
    _ = ∏ q : (Σ r : Layout.Root σ.symm, CyclePos σ.symm r),
        letter w (vertexEquiv σ.symm q).1 (p (vertexEquiv σ.symm q))
          (x (vertexEquiv σ.symm q)) (x (nextVertex σ (vertexEquiv σ.symm q))) :=
      (Fintype.prod_sigma (fun q : (Σ r : Layout.Root σ.symm, CyclePos σ.symm r) =>
        letter w (vertexEquiv σ.symm q).1 (p (vertexEquiv σ.symm q))
          (x (vertexEquiv σ.symm q)) (x (nextVertex σ (vertexEquiv σ.symm q))))).symm
    _ = _ := (vertexEquiv σ.symm).prod_comp
      (fun v : Bool × Fin n => letter w v.1 (p v) (x v) (x (nextVertex σ v)))

def axis (u v : ℚ) (c : Bool) := if c then v else u
def weights (u v : ℚ) (c sameFlip : Bool) : ℚ :=
  if sameFlip then 1 - axis u v c else 1 + axis u v c
def mon (u v : ℚ) (c : Bool) (k : ℕ) :=
  u^((k+(!c).toNat)/2) * v^((k+c.toNat)/2)
def elem (u v : ℚ) (a : Placement.Arc) :=
  1 + (if a.2.2 then (1:ℚ) else -1)*u^a.1*v^a.2.1

theorem mon_succ (u v : ℚ) (c : Bool) (k : ℕ) :
    mon u v c (k+1) = axis u v c * mon u v (!c) k := by
  have hr : (k+1+1)/2=k/2+1 := by omega
  cases c <;> simp [mon,axis,hr,pow_succ] <;> ring

theorem arc_succ (w : Bool → Bool → R) (c p : Bool) (k : ℕ) :
    arcFactor w (k+1,c,p) =
      w c false*arcFactor w (k,!c,p) + w c true*arcFactor w (k,!c,!p) := by
  have h : freePath w (!c) k true p = arcFactor w (k,!c,!p) := by
    cases p <;> exact freePath_eq_arcFactor w (!c) k true _
  calc
    _ = w c true * freePath w (!c) k true p + w c false * arcFactor w (k,!c,p) := by
      simp [arcFactor,freePath,portComp,Fintype.sum_bool,edgePort]
    _ = _ := by rw [h,add_comm]

theorem arc_eigen (u v : ℚ) (c p : Bool) (k : ℕ) :
    arcFactor (weights u v) (k,c,p) =
      ((2:ℚ)^k/2)*(1+(if p then (-1:ℚ) else 1)*mon u v c k) := by
  induction k generalizing c p with
  | zero => cases c <;> cases p <;> norm_num [arcFactor_zero,mon]
  | succ k ih => rw [arc_succ,ih,ih,mon_succ]; cases p <;> simp [weights,pow_succ] <;> ring

theorem arc_eval (u v : ℚ) (q : ProfileFactor.Arc) :
    arcFactor (weights u v) q = ((2:ℚ)^q.1/2)*elem u v (Placement.decodeTag q) := by
  obtain ⟨k,c,p⟩ := q
  rw [arc_eigen]
  cases p <;> simp [elem,Placement.decodeTag,mon] <;> ring

theorem assignments_eval (σ : Equiv.Perm (Fin n)) (p : Pins n) (u v : ℚ) :
    polyDef n σ p u v = cycleTraceProduct (weights u v) σ p / (2:ℚ)^(free p) := by
  classical
  rw [polyDef_eq_avg_compat,cycleTraceProduct_eq_weighted]
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  unfold assignmentWeight compatible
  split_ifs with h
  · rw [term_eq_prod_edges,← (headV σ).prod_comp (fun i : Bool × Fin n =>
      edgePort (weights u v) i.1 (x i) (x (nextVertex σ i)))]
    apply Finset.prod_congr rfl
    rintro ⟨c,i⟩ _
    cases c <;> simp [headV,nextE,nextVertex,one_add_sgn_mul,edgePort,weights,axis,eq_comm]
  · rfl

abbrev Tag := ProfileFactor.Arc
def closed (L : List (Option Bool)) := closeScan false (scanWord false L)
noncomputable def roots (σ : Equiv.Perm (Fin n)) : List (Layout.Root σ.symm) := by
  classical exact Finset.univ.toList
noncomputable def rowTags (σ : Equiv.Perm (Fin n)) (p : Pins n) (r : Layout.Root σ.symm) :=
  (closed (cycleWord σ.symm p r)).2
noncomputable def allTags (σ : Equiv.Perm (Fin n)) (p : Pins n) :=
  (roots σ).flatMap (rowTags σ p)
noncomputable def allArcs (σ : Equiv.Perm (Fin n)) (p : Pins n) :=
  (allTags σ p).map Placement.decodeTag

private theorem product_rows {α : Type} (t : α → List Tag) (f : Tag → ℚ) (rs : List α) :
    (rs.map fun r => ((t r).map f).prod).prod = ((rs.flatMap t).map f).prod := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [ih]

private theorem product_weights (u v : ℚ) (t : List Tag) :
    (t.map (arcFactor (weights u v))).prod =
      (t.map (fun q => (2:ℚ)^q.1/2)).prod * ((t.map Placement.decodeTag).map (elem u v)).prod := by
  induction t with
  | nil => simp
  | cons q t ih => simp [arc_eval,ih]; ring

theorem trace_factor (σ : Equiv.Perm (Fin n)) (p : Pins n) :
    ∃ c : ℚ, ∀ u v, polyDef n σ p u v = c*((allArcs σ p).map (elem u v)).prod := by
  classical
  let float : Layout.Root σ.symm → ℚ := fun r => 2^(closed (cycleWord σ.symm p r)).1
  let scalar : ℚ := ((roots σ).map float).prod * ((allTags σ p).map (fun q => (2:ℚ)^q.1/2)).prod / 2^(free p)
  refine ⟨scalar,fun u v => ?_⟩
  have hw (r : Layout.Root σ.symm) :
      portTrace (wordPorts (weights u v) false (cycleWord σ.symm p r)) =
        float r * ((rowTags σ p r).map (arcFactor (weights u v))).prod := by
    exact cycle_factor _ _ _ (by rw [cycleWord_length]; omega)
  have f : cycleTraceProduct (weights u v) σ p =
      ((roots σ).map fun r => float r * ((rowTags σ p r).map (arcFactor (weights u v))).prod).prod := by
    simpa only [cycleTraceProduct,roots,Finset.prod_map_toList] using
      Finset.prod_congr (s₁:=Finset.univ) rfl (fun r _ => hw r)
  rw [assignments_eval,f,List.prod_map_mul,product_rows,← allTags,product_weights]
  unfold scalar allArcs
  ring

theorem tag_shape (q : Tag) (h : 0<q.1) :
    let a := Placement.decodeTag q
    0<a.1+a.2.1 ∧ a.1≤a.2.1+1 ∧ a.2.1≤a.1+1 := by
  rcases q with ⟨k,c,s⟩
  cases c <;> simp [Placement.decodeTag] at h ⊢ <;> omega

theorem all_shape (σ : Equiv.Perm (Fin n)) (p : Pins n) :
    ∀ a ∈ allArcs σ p, 0<a.1+a.2.1 ∧ a.1≤a.2.1+1 ∧ a.2.1≤a.1+1 := by
  intro a ha
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
  obtain ⟨r,_,hq⟩ := List.mem_flatMap.mp hq
  have H := scanWord_valid false (cycleWord σ.symm p r)
  exact tag_shape q (closeScan_positive _ _ H.2 (by rw [H.1,cycleWord_length]; exact cyclePos_positive ..) q hq)

theorem zero_prod (L : List Placement.Arc) (h : ∀ a ∈ L, 0<a.1+a.2.1) :
    (L.map (elem 0 0)).prod=1 := by
  induction L with
  | nil => rfl
  | cons a t ih =>
    have hp := h a List.mem_cons_self
    have ht := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hz : a.1 ≠ 0 ∨ a.2.1 ≠ 0 := by omega
    rcases hz with hr|hb
    · simp [elem,ht,zero_pow hr]
    · simp [elem,ht,zero_pow hb]

theorem physical_factor (σ : Equiv.Perm (Fin n)) (p : Pins n) (u v : ℚ) :
    polyDef n σ p u v = ((allArcs σ p).map (elem u v)).prod := by
  obtain ⟨c,hc⟩ := trace_factor σ p
  have h0 := hc 0 0
  rw [zero_prod _ (fun a h => (all_shape σ p a h).1),mul_one] at h0
  obtain ⟨L,_,_,hs,hv⟩ := exists_arc_factors σ p
  have h1 : polyDef n σ p 0 0 = 1 := (hv 0 0).trans (zero_prod L (fun a h => (hs a h).1))
  rw [hc,← h0,h1,one_mul]

theorem physical_charge (σ : Equiv.Perm (Fin n)) (p : Pins n) (k : ℕ) (hk : 0<k) (m : ℕ) :
    charge k (allArcs σ p) m = charge k (arcList σ p) m := by
  obtain ⟨hn,hd⟩ := positive_codes k hk _ (all_shape σ p)
  have e := arc_spectrum k σ p _ (physical_factor σ p)
  have a := inventory_spec _ _ _ hn hd e m
  have eqQ : ((charge k (allArcs σ p) m : ℤ) : ℚ) = charge k (arcList σ p) m := by
    simpa [charge] using a.symm.trans ((arc_semantics k hk σ p).2.2 m)
  exact_mod_cast eqQ

end PEqualNP.Outside.L_pcx_386.Homogeneous

namespace PEqualNP.Outside.L_pcx_386.RowShape

open PEqualNP.Outside.L_pcx_386_aux
open PEqualNP.Outside.L_pcx_386_aux.ProfileFactor
open PEqualNP.Outside.L_pcx_386.Core
open PEqualNP.Outside.L_pcx_386.Homogeneous (allArcs allTags rowTags roots closed)

def lane (c e : Bool) (k : ℕ) := (k+(decide (c=e)).toNat)/2
def packetLane (e : Bool) (q : ProfileFactor.Arc) := lane q.2.1 e q.1
def laneSum (A : List ProfileFactor.Arc) (e : Bool) := (A.map (packetLane e)).sum
def openLane (c e : Bool) : Scan → ℕ
  | (k,none,_) => lane c e k
  | (_,some (f,_,l,_,d),A) => lane c e f + lane d e l + laneSum A e
def negSum (A : List ProfileFactor.Arc) := (A.map (fun q => q.2.2.toNat)).sum
def evenInv : Scan → Prop
  | (_,none,A) => A=[]
  | (_,some (_,a,_,b,_),A) => negSum A % 2 = (xor b a).toNat
def marks : Scan → ℕ
  | (_,none,_) => 0
  | (_,some _,A) => A.length+1

theorem lane_succ (c e : Bool) (k : ℕ) :
    lane c e (k+1) = lane c e k + (decide (colorAt c k=e)).toNat := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> cases c <;> cases e <;> simp [lane,colorAt,h] <;> omega

theorem lane_add (c e : Bool) (k j : ℕ) :
    lane c e (k+j) = lane c e k + lane (colorAt c k) e j := by
  induction j with
  | zero =>
    have h : lane (colorAt c k) e 0 = 0 := by unfold lane; cases decide (colorAt c k=e) <;> decide
    rw [h,Nat.add_zero,Nat.add_zero]
  | succ j ih => rw [← Nat.add_assoc,lane_succ,lane_succ,ih,colorAt_add]; omega

private theorem lane_step (c e : Bool) (s : Scan) (p : Option Bool) (hg : scanGood c s) :
    openLane c e (scanStep c s p) = openLane c e s + (decide (colorAt c s.1=e)).toNat := by
  rcases s with ⟨k, o, A⟩
  rcases o with _|⟨f,a,l,b,d⟩
  · have hn : A=[] := hg.2
    subst A
    cases p with
    | none => exact lane_succ ..
    | some b =>
      change lane c e k + lane (colorAt c k) e 1 + 0 = _
      rw [lane_succ,show lane (colorAt c k) e 0=0 by unfold lane; cases decide (colorAt c k=e) <;> decide]
      simp [colorAt_zero,openLane]
  · obtain ⟨_,_,_,ha⟩ := hg
    cases p with
    | none =>
      change lane c e f + lane d e (l+1) + laneSum A e = _
      rw [lane_succ,ha]; simp [openLane]; omega
    | some z =>
      change lane c e f + lane (colorAt c k) e 1 + laneSum ((l,d,xor b z)::A) e = _
      rw [lane_succ,show lane (colorAt c k) e 0=0 by unfold lane; cases decide (colorAt c k=e) <;> decide]
      simp [colorAt_zero,openLane,laneSum,packetLane]; omega

private theorem parity_step (c : Bool) (s : Scan) (p : Option Bool) (h : evenInv s) :
    evenInv (scanStep c s p) := by
  rcases s with ⟨k,o,A⟩
  rcases o with _|⟨f,a,l,b,d⟩
  · change A=[] at h
    subst A
    cases p <;> simp [scanStep,evenInv,negSum]
  · change negSum A % 2=(xor b a).toNat at h
    cases p with
    | none => exact h
    | some z =>
      change negSum ((l,d,xor b z)::A) % 2=(xor z a).toNat
      cases a <;> cases b <;> cases z <;> simp [negSum] at h ⊢ <;> omega

private theorem marks_step (c : Bool) (s : Scan) (p : Option Bool) :
    marks (scanStep c s p) = marks s + p.isSome.toNat ∨ s.2.1 = none := by
  rcases s with ⟨k,o,A⟩
  rcases o with _|⟨f,a,l,b,d⟩
  · exact Or.inr rfl
  · left; cases p <;> simp [marks,scanStep]

private theorem marks_step_good (c : Bool) (s : Scan) (p : Option Bool) (h : scanGood c s) :
    marks (scanStep c s p) = marks s + p.isSome.toNat := by
  rcases marks_step c s p with H|H
  · exact H
  · rcases s with ⟨k,o,A⟩
    change o=none at H
    subst o
    have hn : A=[] := h.2
    subst A
    cases p <;> rfl

theorem scan_invariants (c : Bool) (W : List (Option Bool)) :
    (∀ e, openLane c e (scanWord c W)=lane c e W.length) ∧
      evenInv (scanWord c W) ∧ marks (scanWord c W)=W.countP Option.isSome := by
  induction W using List.reverseRecOn with
  | nil => exact ⟨fun _ => rfl,rfl,rfl⟩
  | append_singleton W p ih =>
    have hs : scanWord c (W++[p]) = scanStep c (scanWord c W) p := by simp [scanWord,List.foldl_append]
    have g := scanWord_valid c W
    rw [hs]
    refine ⟨fun e => ?_,parity_step _ _ _ ih.2.1,?_⟩
    · rw [lane_step _ _ _ _ g.2,ih.1,g.1]
      simp [lane_succ]
    · rw [marks_step_good _ _ _ g.2,ih.2.2,List.countP_append]
      cases p <;> simp

private theorem closed_lane (c e : Bool) (s : Scan) (h : scanGood c s) (he : s.1 % 2=0) :
    laneSum (closeScan c s).2 e = openLane c e s := by
  rcases s with ⟨k,o,A⟩
  rcases o with _|⟨f,a,l,b,d⟩
  · simp [openLane,laneSum,packetLane,closeScan]
  · obtain ⟨_,_,_,hd⟩ := h
    have H := hd.trans (colorAt_even c he)
    simp [laneSum,packetLane,closeScan,openLane,lane_add,H]
    omega

private theorem closed_parity (c : Bool) (s : Scan) (h : evenInv s) :
    negSum (closeScan c s).2 % 2 = 0 := by
  rcases s with ⟨k,o,A⟩
  rcases o with _|⟨f,a,l,b,d⟩
  · simp [closeScan,negSum]
  · change negSum A % 2=(xor b a).toNat at h
    cases b <;> cases a <;> simp [negSum,closeScan] at h ⊢ <;> omega

private theorem closed_marks (c : Bool) (s : Scan) :
    (closeScan c s).2.length = marks s + (closeScan c s).1 := by
  rcases s with ⟨k,o,A⟩
  rcases o with _|⟨f,a,l,b,d⟩ <;> rfl

def packets (W : List (Option Bool)) := (closed W).2.map Placement.decodeTag

theorem local_packets (W : List (Option Bool)) (m : ℕ) (hW : W.length=2*m) :
    ((packets W).map Prod.fst).sum=m ∧ ((packets W).map (fun a => a.2.1)).sum=m ∧
    ((packets W).map (fun a => (!a.2.2).toNat)).sum % 2=0 ∧
    (packets W).length = W.countP Option.isSome + (closed W).1 ∧
    (closed W).1 ≤ 1 ∧ ((closed W).1=1 → packets W=[(m,m,true)]) := by
  let s := scanWord false W
  obtain ⟨hk,hg⟩ := scanWord_valid false W
  have hn : s.1=2*m := hk.trans hW
  obtain ⟨lc,even,hm⟩ := scan_invariants false W
  have hl (c : Bool) := (closed_lane false c s hg (by omega)).trans (lc c)
  have red (q : ProfileFactor.Arc) : (Placement.decodeTag q).1 = packetLane false q := by
    rcases q with ⟨k,c,b⟩; cases c <;> rfl
  have blue (q : ProfileFactor.Arc) : (Placement.decodeTag q).2.1 = packetLane true q := by
    rcases q with ⟨k,c,b⟩; cases c <;> rfl
  have minus (q : ProfileFactor.Arc) : (!(Placement.decodeTag q).2.2).toNat=q.2.2.toNat := by simp [Placement.decodeTag]
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa [packets,List.map_map,Function.comp_def,red,laneSum,lane,hW,closed,s,show (2*m+1)/2=m by omega] using hl false
  · simpa [packets,List.map_map,Function.comp_def,blue,laneSum,lane,hW,closed,s] using hl true
  · simpa [packets,List.map_map,Function.comp_def,minus,closed,s,negSum] using closed_parity false s even
  · simpa [packets,closed,s,hm] using closed_marks false s
  · change (closeScan false s).1 ≤ 1 ∧ ((closeScan false s).1=1 → (closeScan false s).2.map Placement.decodeTag=[(m,m,true)])
    rcases s with ⟨k,o,A⟩
    rcases o with _|⟨f,a,l,b,d⟩
    · change k=2*m at hn
      simp [closeScan,hn,Placement.decodeTag,show (2*m+1)/2=m by omega]
    · simp [closeScan]

theorem physical_imbalance (σ : Equiv.Perm (Fin n)) (p : Pins n) (w : ℕ × ℕ) (hw : GoodPair w) :
    imbalance (allArcs σ p) w = imbalance (arcList σ p) w := by
  let k := stride n
  have hk : 3≤k := by unfold k stride; omega
  have ht := Homogeneous.all_shape σ p
  have E := Homogeneous.physical_charge σ p k (by omega) (arcCode k w)
  unfold charge numer denom at E
  rw [count_code_good k hk _ (numPairs_good _ ht) w hw,count_code_good k hk _ (denPairs_good _ ht) w hw] at E
  obtain ⟨_,rfl,_,hf,_⟩ := exists_arc_factors σ p
  rw [count_code_good k hk _ (numPairs_good _ hf) w hw,count_code_good k hk _ (denPairs_good _ hf) w hw] at E
  have hp := hw.1
  have pos : 0<arcCode k w := by unfold arcCode; nlinarith [Nat.mul_le_mul_right w.2 (by omega : 1≤k)]
  exact mul_left_cancel₀ (by exact_mod_cast pos.ne' : (arcCode k w : ℤ) ≠ 0) E

private theorem count_to_sum {α : Type} (P : α → Bool) (L : List α) :
    L.countP P = (L.map (fun x => (P x).toNat)).sum := by
  induction L with
  | nil => rfl
  | cons a t ih => cases h : P a <;> simp [List.countP_cons,h,ih,Nat.add_comm]

noncomputable def floats (σ : Equiv.Perm (Fin n)) (p : Pins n) : ℕ := by
  classical exact ∑ r : Layout.Root σ.symm, (closed (cycleWord σ.symm p r)).1

theorem physical_mass (σ : Equiv.Perm (Fin n)) (p : Pins n) :
    (allArcs σ p).length + free p = 2*n + floats σ p := by
  classical
  let W := cycleWord σ.symm p
  have hr (r : Layout.Root σ.symm) : (rowTags σ p r).length =
      (W r).countP Option.isSome + (closed (W r)).1 := by
    have h := (local_packets (W r) _ (cycleWord_length ..)).2.2.2.1
    simpa [W,packets,rowTags] using h
  have hl : (allArcs σ p).length = (∑ r, (W r).countP Option.isSome)+floats σ p := by
    simp only [allArcs,allTags,List.length_map,List.length_flatMap,roots,Finset.sum_map_toList,hr,
      Finset.sum_add_distrib,floats,W]
  let pinned := fun v : Bool × Fin n => (p v).isSome.toNat
  have hw (r : Layout.Root σ.symm) : (W r).countP Option.isSome = ∑ i : CyclePos σ.symm r, pinned (slotVertex σ.symm r i) := by
    simp [W,cycleWord,count_to_sum,List.map_ofFn,List.sum_ofFn,Function.comp_def,pinned]
  have hp : (∑ r, (W r).countP Option.isSome) = ∑ v, pinned v := by
    simp_rw [hw]
    rw [← (vertexEquiv σ.symm).sum_comp pinned,Fintype.sum_sigma]
    rfl
  have pt (v : Bool × Fin n) : pinned v + (if p v=none then 1 else 0)=1 := by
    cases h : p v <;> simp [pinned,h]
  have hh : (∑ v, pinned v)+free p=2*n := by
    rw [free,Finset.card_filter,← Finset.sum_add_distrib]
    simp [pt]
  rw [hl,hp]
  omega

def primary {d : ℕ} {α : Type} (f : Fin d → α) (a : Fin d) : Prop :=
  ∀ b, b<a → f b ≠ f a

noncomputable def representatives {d : ℕ} {α : Type} (f : Fin d → α) (surj : Function.Surjective f) :
    {a : Fin d // primary f a} ≃ α := by
  classical
  apply Equiv.ofBijective (fun a => f a.val)
  constructor
  · rintro ⟨a,ha⟩ ⟨b,hb⟩ e
    apply Subtype.ext
    rcases lt_trichotomy a b with h|h|h
    · exact False.elim (hb a h e)
    · exact h
    · exact False.elim (ha b h e.symm)
  · intro r
    obtain ⟨i,hi⟩ := surj r
    let F := Finset.univ.filter (fun a => f a=r)
    have ne : F.Nonempty := ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
    let a := F.min' ne
    have ha : f a=r := (Finset.mem_filter.mp (F.min'_mem ne)).2
    refine ⟨⟨a,fun b hb e => ?_⟩,ha⟩
    exact hb.not_ge (F.min'_le b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.trans ha⟩))

theorem representatives_apply {d : ℕ} {α : Type} (f : Fin d → α) (su : Function.Surjective f)
    (a : {a : Fin d // primary f a}) : representatives f su a = f a.val := rfl

theorem primary_roots {d : ℕ} (τ : Equiv.Perm (Fin n)) (g : Fin d → Fin n × Fin n)
    (real : ∀ a, (∀ s, τ.SameCycle (g a).1 s → (g a).1 ≤ s) ∧ (g a).2.val+1=Function.minimalPeriod τ (g a).1)
    (cover : ∀ r : Layout.Root τ, ∃ a : Fin d, (g a).1=r.val) :
    ∃ e : {a : Fin d // primary (fun i => (g i).1) a} ≃ Layout.Root τ,
      ∀ a, (e a).val=(g a.val).1 ∧ Function.minimalPeriod τ (e a).val=(g a.val).2.val+1 := by
  let f : Fin d → Layout.Root τ := fun a => ⟨(g a).1,(real a).1⟩
  have hs : Function.Surjective f := fun r => by
    obtain ⟨a,h⟩ := cover r
    exact ⟨a,Subtype.ext h⟩
  let q : {a : Fin d // primary (fun i => (g i).1) a} ≃ {a : Fin d // primary f a} :=
    Equiv.subtypeEquivRight fun i => by
      exact ⟨fun h j hj e => h j hj (congrArg Subtype.val e),fun h j hj e => h j hj (Subtype.ext e)⟩
  exact ⟨q.trans (representatives f hs),fun a => ⟨rfl,(real a.val).2.symm⟩⟩

end PEqualNP.Outside.L_pcx_386.RowShape

namespace PEqualNP.Outside.L_pcx_386.Assembly

open PEqualNP.Outside.L_pcx_386_aux
open PEqualNP.Outside.L_pcx_386_aux.ProfileFactor hiding Arc
open PEqualNP.Outside.L_pcx_386.Core
open PEqualNP.Outside.L_pcx_386.Core.Compiler.Build
open PEqualNP.Outside.L_pcx_386.Placement
open PEqualNP.Outside.L_pcx_386.RowShape
open PEqualNP.Outside.L_pcx_386.Homogeneous (allArcs allTags rowTags roots closed)

def red (L : List Arc) := (L.map Prod.fst).sum
def blue (L : List Arc) := (L.map (fun q => q.2.1)).sum
def minus (L : List Arc) := (L.map (fun q => (flip q).toNat)).sum

lemma total_span (L : List Arc) : (L.map span).sum=red L+blue L := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [span,red,blue] at ih ⊢; omega

lemma tip_eq (s : Bool) (L : List Arc) :
    (exitSpin s L).toNat = (s.toNat+minus L) % 2 := by
  induction L generalizing s with
  | nil => cases s <;> rfl
  | cons a L ih =>
    change (exitSpin (xor s (flip a)) L).toNat = _
    rw [ih]
    cases s <;> cases h : flip a <;> simp [minus,h] <;> omega

private theorem mono_sum {L : List Arc} (t : ℕ) (h : ∀ a ∈ L, a.1=a.2.1+t) :
    red L = blue L + t*L.length := by
  induction L with
  | nil => simp [red,blue]
  | cons a L ih =>
    have x := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have y := h a List.mem_cons_self
    simp [red,blue,Nat.mul_succ] at x ⊢
    omega

private theorem anti_sum {L : List Arc} (h : ∀ a ∈ L, a.2.1=a.1+1) :
    blue L = red L + L.length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have x := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have y := h a List.mem_cons_self
    simp [red,blue] at x ⊢
    omega

theorem render_packets {D R B : List Arc} {m : ℕ} (hm : 0 < m) (float : Bool)
    (hd : ∀ a ∈ D, a.1=a.2.1) (hr : ∀ a ∈ R, a.1=a.2.1+1) (hb : ∀ a ∈ B, a.2.1=a.1+1)
    (hp : ∀ a ∈ D++R++B, 0<span a) (rr : red (D++R++B)=m) (bb : blue (D++R++B)=m)
    (par : minus (D++R++B) % 2=0) (single : float=true → ∃ k, (D++R++B).Perm [(k,k,true)]) :
    R.length=B.length ∧
      let w := word float (D++weave R B)
      w.length=2*m ∧ (packets w).Perm (D++R++B) ∧ (closed w).1=float.toNat := by
  have hrb : red D=blue D := by simpa using mono_sum 0 (L:=D) (by simpa using hd)
  have hr' := mono_sum 1 hr
  have hb' := anti_sum hb
  have eq : R.length=B.length := by
    simp [red,blue] at hrb hr' hb' rr bb
    omega
  let L := D++weave R B
  have pe : L.Perm (D++R++B) := by
    rw [List.append_assoc]; exact List.Perm.append_left _ (weave_perm _ _)
  have gross : (L.map span).sum=2*m := (pe.map span).sum_eq.trans (by rw [total_span,rr,bb];omega)
  have ne : L≠[] := by intro nil; simp [nil] at gross; omega
  have even : minus L % 2=0 := by
    have h : minus L=minus (D++R++B) := (pe.map _).sum_eq
    rw [h,par]
  have hc : exitSpin false L=false := by
    have H := tip_eq false L
    cases ht : exitSpin false L <;> simp [ht,even] at H ⊢
  have hh (f : float=true) : ∃ k, L=[(k,k,true)] := by
    obtain ⟨k,hk⟩ := single f
    exact ⟨k,List.perm_singleton.mp (pe.trans hk)⟩
  have H := pack_inventory D R B float hd hr hb eq ne (fun q h => hp q (pe.mem_iff.mp h)) hc hh
  refine ⟨eq,?_,H.2.1,H.1⟩
  change (word float L).length=2*m
  cases float <;> simp [word,render_length,gross]

private theorem first_unique {d : ℕ} {α : Type} (f : Fin d → α) {a b : Fin d}
    (ha : primary f a) (hb : primary f b) (h : f a=f b) : a=b := by
  rcases lt_trichotomy a b with l|e|l
  · exact False.elim (hb a l h)
  · exact e
  · exact False.elim (ha b l h.symm)

noncomputable def selected {n d : ℕ} (g : Scatter.Guess n d) (r : Fin n) : Option (Fin d) := by
  classical exact if h : ∃ a : Fin d, (g a).1=r ∧ primary (fun i => (g i).1) a then some h.choose else none

theorem selected_first {n d : ℕ} (g : Scatter.Guess n d) {r : Fin n} {a : Fin d}
    (hr : (g a).1=r) (ha : primary (fun i => (g i).1) a) : selected g r=some a := by
  classical
  have h : ∃ b : Fin d, (g b).1=r ∧ primary (fun i => (g i).1) b := ⟨a,hr,ha⟩
  rw [selected,dite_eq_left h]
  exact congrArg some (first_unique (fun i => (g i).1) h.choose_spec.2 ha (h.choose_spec.1.trans hr.symm))

def bankPos {n : ℕ} (b : Bool) (j : Fin n) : Fin (2*n+1) :=
  ⟨2*j.val+b.toNat,by have := j.isLt;cases b <;> simp <;> omega⟩

def slotPos {n : ℕ} {τ : Equiv.Perm (Fin n)} {r : Layout.Root τ} (j : CyclePos τ r) : Fin (2*n+1) :=
  ⟨j.val,by have := j.isLt; have := Layout.periodLe τ r.val; omega⟩

noncomputable def fanMarks {n d N : ℕ} (g : Scatter.Guess n d)
    (wire : Fin d × Bool × Fin (2*n+1) → Sig N) : Scatter.Marks n N :=
  fun z b r j => match selected g r with
    | none => fun _ => false
    | some a => wire (a,z,bankPos b j)

theorem fan_build {n d N : ℕ} {A : Set (Sig N)} {b : ℕ} (edge : LayoutCircuit.Mat n N)
    (g : Scatter.Guess n d) (wire : Fin d × Bool × Fin (2*n+1) → Sig N) (ok : Sig N)
    (hc : Build A ({ok} ∪ Set.range wire) b) (he : ∀ r t, edge r t∈A)
    (hz : (fun _ => false)∈A) (ho : (fun _ => true)∈A) :
    Build A ({ok} ∪ Set.range (Scatter.out edge (fanMarks g wire))) (b+Scatter.cost n) := by
  let E := A ∪ ({ok} ∪ Set.range wire)
  have hm (z b r j) : fanMarks g wire z b r j ∈ E := by
    cases hs : selected g r with
    | none => rw [fanMarks,hs]; exact Or.inl hz
    | some a => rw [fanMarks,hs]; exact Or.inr (Or.inr ⟨_,rfl⟩)
  have hs : Build E (Set.range (Scatter.out edge (fanMarks g wire))) (Scatter.cost n) :=
    Scatter.build edge (fanMarks g wire) (fun r t => Or.inl (he r t)) hm (Or.inl hz) (Or.inl ho)
  exact relax (seq hc hs) le_rfl (fun _ h => h.elim (fun h => Or.inl (Or.inl h)) Or.inr) le_rfl

theorem physical_word {n d N : ℕ} (edge : LayoutCircuit.Mat n N) (g : Scatter.Guess n d)
    (wire : Fin d × Bool × Fin (2*n+1) → Sig N) (x : Fin N → Bool)
    (τ : Equiv.Perm (Fin n)) (he : ∀ r t, edge r t x=decide (τ r=t))
    (r : Layout.Root τ) (a : Fin d) (hr : (g a).1=r.val) (ha : primary (fun i => (g i).1) a) :
    cycleWord τ (Scatter.physical edge (fanMarks g wire) x) r =
      List.ofFn fun i : CyclePos τ r =>
        if wire (a,false,slotPos i) x then some (wire (a,true,slotPos i) x) else none := by
  rw [Scatter.word_correct edge _ τ x he]
  unfold Scatter.assignedWord
  apply congrArg List.ofFn
  funext i
  obtain ⟨⟨b,j⟩,rfl⟩ := (pairPos (Function.minimalPeriod τ r.val)).surjective i
  simp only [Equiv.symm_apply_apply,Scatter.assigned,fanMarks,selected_first g hr ha]
  rfl

theorem physical_recovers {n d N : ℕ} (edge : LayoutCircuit.Mat n N) (g : Scatter.Guess n d)
    (wire : Fin d × Bool × Fin (2*n+1) → Sig N) (x : Fin N → Bool)
    (τ : Equiv.Perm (Fin n)) (he : ∀ r t, edge r t x=decide (τ r=t))
    (r : Layout.Root τ) (a : Fin d) (hr : (g a).1=r.val) (ha : primary (fun i => (g i).1) a)
    (w : List (Option Bool)) (len : w.length=2*Function.minimalPeriod τ r.val)
    (h : ∀ k : Fin (2*n+1), (if wire (a,false,k) x then some (wire (a,true,k) x) else none)=w.getD k.val none) :
    cycleWord τ (Scatter.physical edge (fanMarks g wire) x) r=w := by
  rw [physical_word edge g wire x τ he r a hr ha]
  apply List.ext_getElem
  · simpa using len.symm
  · intro j hj hw
    simp only [List.getElem_ofFn,h]
    exact List.getD_eq_getElem w none hw

theorem matched_rep {n d N : ℕ} (edge : LayoutCircuit.Mat n N) (g : Scatter.Guess n d)
    (x : Fin N → Bool) (τ : Equiv.Perm (Fin n)) (he : ∀ r t, edge r t x=decide (τ r=t))
    (hc : Scatter.Coherent g) (hg : Scatter.guardSig edge g x=true) :
    ∃ e : {a : Fin d // primary (fun i => (g i).1) a} ≃ Layout.Root τ,
      ∀ a, (e a).val=(g a.val).1 ∧ Function.minimalPeriod τ (e a).val=(g a.val).2.val+1 := by
  apply primary_roots τ g (Scatter.matched_length edge g τ x he hc hg)
  intro r
  let j : Fin n := ⟨0,by have := r.val.isLt;omega⟩
  have hu := (Scatter.matches_spec edge g τ x he).mp hg r.val j
  obtain ⟨a,eq,_⟩ := hu.mp ⟨r.property,Layout.periodPos τ r.val⟩
  exact ⟨a,eq⟩

private theorem flat_sum {α β : Type} (L : List α) (bag : α → List β) :
    ((L.flatMap bag : List β) : Multiset β) = (L.map (fun a => (bag a : Multiset β))).sum := by
  induction L with
  | nil => rfl
  | cons a t ih => simp only [List.flatMap_cons,← Multiset.coe_add,List.map_cons,List.sum_cons,ih]

noncomputable def catRows {d : ℕ} (bag : Fin d → List Arc) : List Arc :=
  Finset.univ.toList.flatMap bag

theorem cat_sum {d : ℕ} (bag : Fin d → List Arc) :
    ((catRows bag : List Arc) : Multiset Arc) = ∑ i, (bag i : Multiset Arc) := by
  rw [catRows,flat_sum,Finset.sum_map_toList]

theorem arcs_sum {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pins n) :
    ((allArcs σ p : List Arc) : Multiset Arc) =
      ∑ r : Layout.Root σ.symm, (packets (cycleWord σ.symm p r) : Multiset Arc) := by
  classical
  simp only [allArcs,allTags,List.map_flatMap,roots,flat_sum,Finset.sum_map_toList,rowTags,packets]

private theorem sum_nonempty {d : ℕ} {M : Type} [AddCommMonoid M] (P : Fin d → Prop)
    [Fintype (Subtype P)] (f : Fin d → M) (off : ∀ i, ¬P i → f i=0) :
    ∑ i : Subtype P, f i.val = ∑ i, f i := by
  classical
  let F := Finset.univ.filter P
  have he (i : Fin d) : i∈F ↔ P i := by simp [F]
  rw [← Finset.sum_subtype F he f]
  exact Finset.sum_subset (Finset.subset_univ _) (fun i _ h => off i (fun hi => h ((he _).mpr hi)))

theorem pair_congr {L K : List Arc} (h : L.Perm K) :
    numPairs L=numPairs K ∧ denPairs L=denPairs K := by
  induction h with
  | nil => exact ⟨rfl,rfl⟩
  | cons a _ ih => rcases a with ⟨r,b,s⟩; cases s <;> simp [numPairs,denPairs,ih.1,ih.2]
  | swap a q t =>
    rcases a with ⟨r,b,s⟩; rcases q with ⟨r',b',s'⟩
    cases s <;> cases s' <;> simp [numPairs,denPairs,Multiset.cons_swap]
  | trans _ _ h1 h2 => exact ⟨h1.1.trans h2.1,h1.2.trans h2.2⟩

theorem padded_bridge {n d : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pins n) (g : Scatter.Guess n d)
    (e : {a : Fin d // primary (fun i => (g i).1) a} ≃ Layout.Root σ.symm)
    (bag : Fin d → List Arc) (float : Fin d → ℕ)
    (row : ∀ a, (packets (cycleWord σ.symm p (e a))).Perm (bag a.val))
    (hf : ∀ a, (closed (cycleWord σ.symm p (e a))).1=float a.val)
    (pad : ∀ i, ¬primary (fun j => (g j).1) i → bag i=[] ∧ float i=0) :
    (allArcs σ p).Perm (catRows bag) ∧ (catRows bag).length+free p=2*n+∑ i, float i ∧
      ∀ w, GoodPair w → imbalance (catRows bag) w = imbalance (arcList σ p) w := by
  classical
  have perm : (allArcs σ p).Perm (catRows bag) := by
    apply Multiset.coe_eq_coe.mp
    rw [arcs_sum,cat_sum,← e.sum_comp (fun r => (packets (cycleWord σ.symm p r) : Multiset Arc))]
    calc
      _ = ∑ a : {a : Fin d // primary (fun i => (g i).1) a}, (bag a.val : Multiset Arc) :=
        Finset.sum_congr rfl fun a _ => Multiset.coe_eq_coe.mpr (row a)
      _ = _ := sum_nonempty _ (fun i => (bag i : Multiset Arc)) (fun i hi => by rw [(pad i hi).1]; rfl)
  have f : floats σ p = ∑ i, float i := by
    rw [floats,← e.sum_comp (fun r => (closed (cycleWord σ.symm p r)).1)]
    simp_rw [hf]
    exact sum_nonempty _ _ (fun i hi => (pad i hi).2)
  have m := physical_mass σ p
  rw [perm.length_eq,f] at m
  have pair := pair_congr perm
  refine ⟨perm,m,fun w hw => ?_⟩
  rw [← physical_imbalance σ p w hw]
  simp [imbalance,pair.1,pair.2]

noncomputable def capacity {n d : ℕ} (g : Scatter.Guess n d) (i : Fin d) : ℕ := by
  classical exact if primary (fun j => (g j).1) i then (g i).2.val+1 else 0

theorem witness_packets {n d : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pins n) (g : Scatter.Guess n d)
    (e : {a : Fin d // primary (fun i => (g i).1) a} ≃ Layout.Root σ.symm)
    (period : ∀ a, Function.minimalPeriod σ.symm (e a).val=(g a.val).2.val+1) :
    ∃ (bag : Fin d → List Arc) (float : Fin d → ℕ),
      (∀ i, red (bag i)=capacity g i ∧ blue (bag i)=capacity g i ∧ minus (bag i) % 2=0 ∧
        float i ≤ 1 ∧ (float i=1 → bag i=[(capacity g i,capacity g i,true)])) ∧
      (∀ i, ¬primary (fun j => (g j).1) i → bag i=[] ∧ float i=0) ∧
      (∀ i a, a∈bag i → 0<span a ∧ a.1≤a.2.1+1 ∧ a.2.1≤a.1+1) ∧
      (catRows bag).length+free p=2*n+∑ i,float i ∧
      ∀ w, GoodPair w → imbalance (catRows bag) w=imbalance (arcList σ p) w := by
  classical
  let P := primary (fun j => (g j).1)
  let W := cycleWord σ.symm p
  let bag (i : Fin d) : List Arc := if h : P i then packets (W (e ⟨i,h⟩)) else []
  let float (i : Fin d) : ℕ := if h : P i then (closed (W (e ⟨i,h⟩))).1 else 0
  have off (i) (hi : ¬P i) : bag i=[] ∧ float i=0 := by simp [bag,float,hi]
  have b (a : Subtype P) : bag a.val=packets (W (e a)) := by simp [bag,a.property]
  have f (a : Subtype P) : float a.val=(closed (W (e a))).1 := by simp [float,a.property]
  have H := padded_bridge σ p g e bag float (fun a => (b a) ▸ List.Perm.refl _) (fun a => (f a).symm) off
  refine ⟨bag,float,?_,off,?_,H.2⟩
  · intro i
    by_cases h : P i
    · let a : Subtype P := ⟨i,h⟩
      have cg : capacity g i=(g i).2.val+1 := if_pos h
      have lp : (W (e a)).length=2*((g i).2.val+1) := (cycleWord_length ..).trans (congrArg (2*·) (period a))
      obtain ⟨rr,bb,neg,_,ff,ss⟩ := local_packets _ _ lp
      rw [cg,b a,f a]
      exact ⟨rr,bb,neg,ff,ss⟩
    · have hp : ¬primary (fun j => (g j).1) i := h
      simp [capacity,hp,(off i h).1,(off i h).2,red,blue,minus]
  · intro i a ha
    have hm : a∈allArcs σ p := H.1.mem_iff.mpr (List.mem_flatMap.mpr ⟨i,by simp,ha⟩)
    exact Homogeneous.all_shape σ p a hm

theorem length_le_mass (L : List Arc) (h : ∀ a ∈ L, 0<span a) : L.length≤red L+blue L := by
  rw [← total_span]
  induction L with
  | nil => simp
  | cons a t ih =>
    have x := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have y := h a List.mem_cons_self
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    omega

theorem receipt_word {N S d U T : ℕ} (dims : Fin S → ℕ × ℕ) (load : Receipt S d U → Sig N)
    (skip : Fin d → Sig N) (x : Input N) (count : Fin S → Fin d → Bool → ℕ)
    (le : ∀ j i b, count j i b ≤ U) (hw : ∀ j i b k, load (j,i,b,k) x=decide (k.val<count j i b))
    (i : Fin d) (hl : ∀ c, (emitted dims count i c).length ≤ T)
    (he : (emitted dims count i 1).length = (emitted dims count i 2).length) (k : ℕ) :
    let b := fun c => (emitted dims count i c).map (description dims)
    maskedPin T (description dims) (bankOf dims load i) (skip i) k x =
      (word (skip i x) (b 0 ++ weave (b 1) (b 2))).getD k none := by
  rw [position_word,receipt_sequence dims load x count le hw i hl he]

theorem output_sound {n d N : ℕ} (edge : LayoutCircuit.Mat n N) (g : Scatter.Guess n d)
    (wire : Fin d × Bool × Fin (2*n+1) → Sig N) (x : Fin N → Bool)
    (σ : Equiv.Perm (Fin n)) (he : ∀ r t, edge r t x=decide (σ.symm r=t))
    (coh : Scatter.Coherent g) (pass : Scatter.guardSig edge g x=true)
    (Ds Rs Bs : Fin d → List Arc) (chosen : Fin d → Bool)
    (hd : ∀ i a, a∈Ds i → a.1=a.2.1) (hr : ∀ i a, a∈Rs i → a.1=a.2.1+1)
    (hb : ∀ i a, a∈Bs i → a.2.1=a.1+1)
    (hp : ∀ i a, a∈Ds i++Rs i++Bs i → 0<span a)
    (rr : ∀ i, red (Ds i++Rs i++Bs i)=capacity g i)
    (bb : ∀ i, blue (Ds i++Rs i++Bs i)=capacity g i)
    (par : ∀ i, minus (Ds i++Rs i++Bs i) % 2=0)
    (single : ∀ i, chosen i=true → ∃ k, (Ds i++Rs i++Bs i).Perm [(k,k,true)])
    (read : ∀ i k, (if wire (i,false,k) x then some (wire (i,true,k) x) else none) =
        (word (chosen i) (Ds i++weave (Rs i) (Bs i))).getD k.val none) :
    let bag := fun i => Ds i++Rs i++Bs i
    let p := Scatter.physical edge (fanMarks g wire) x
    (allArcs σ p).Perm (catRows bag) ∧ (catRows bag).length+free p=2*n+∑ i,(chosen i).toNat ∧
      ∀ w, GoodPair w → imbalance (catRows bag) w=imbalance (arcList σ p) w := by
  classical
  let bag (i : Fin d) := Ds i++Rs i++Bs i
  let p := Scatter.physical edge (fanMarks g wire) x
  obtain ⟨e,good⟩ := matched_rep edge g x σ.symm he coh pass
  have localRow (a : {i : Fin d // primary (fun j => (g j).1) i}) :
      (packets (cycleWord σ.symm p (e a))).Perm (bag a.val) ∧
      (closed (cycleWord σ.symm p (e a))).1=(chosen a.val).toNat := by
    let i := a.val
    have m : capacity g i=(g i).2.val+1 := if_pos a.property
    have ck := render_packets (m:=capacity g i) (by rw [m];omega) (chosen i) (hd i) (hr i) (hb i)
      (hp i) (rr i) (bb i) (par i) (single i)
    have len : (word (chosen i) (Ds i++weave (Rs i) (Bs i))).length=2*Function.minimalPeriod σ.symm (e a).val := by
      rw [ck.2.1,m,(good a).2]
    have hw := physical_recovers edge g wire x σ.symm he (e a) i (good a).1.symm a.property _ len (read i)
    change (packets (cycleWord σ.symm (Scatter.physical edge (fanMarks g wire) x) (e a))).Perm _ ∧ _
    change cycleWord σ.symm p (e a)=_ at hw
    change (packets (cycleWord σ.symm p (e a))).Perm _ ∧ _
    rw [hw]
    exact ck.2.2
  apply padded_bridge σ p g e bag (fun i => (chosen i).toNat) (fun a => (localRow a).1) (fun a => (localRow a).2)
  intro i hi
  have sz := length_le_mass (bag i) (hp i)
  have zero : capacity g i=0 := if_neg hi
  change (bag i).length ≤ red (Ds i++Rs i++Bs i)+blue (Ds i++Rs i++Bs i) at sz
  rw [rr,bb,zero] at sz
  have hn := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp sz)
  refine ⟨hn,?_⟩
  cases h : chosen i with
  | false => rfl
  | true =>
    obtain ⟨k,hk⟩ := single i h
    change (bag i).Perm _ at hk
    rw [hn] at hk
    simp at hk

theorem shipment_bound {S n d : ℕ} (st : S ≤ (n+2)^4) (hd : d≤n) :
    shipmentCost S d (2*n) (2*n) (2*n) ≤ (n+2)^84 := by
  let X := n+2
  have hx : 2≤X := by unfold X;omega
  have twoN : 2*n ≤ X^2 := by dsimp [X];nlinarith
  have fourN : 2*(2*n) ≤ X^2 := by dsimp [X];nlinarith
  have sm : 2 ≤ X^2 := by nlinarith
  have m : S*2 ≤ X^6 := (Nat.mul_le_mul st sm).trans_eq (pow_add X 4 2).symm
  have l : S*(2*(2*n)) ≤ X^6 := (Nat.mul_le_mul st fourN).trans_eq (pow_add X 4 2).symm
  have r := twoN.trans (Nat.pow_le_pow_right (by omega : X>0) (by decide : 2≤6))
  have k : 2≤X^6 := sm.trans (Nat.pow_le_pow_right (by omega) (by decide : 2≤6))
  have e : X^6+2 ≤ X^7 := by
    calc X^6+2 ≤ X^6+X^6 := Nat.add_le_add_left k _
         _ = X^6*2 := (Nat.mul_two _).symm
         _ ≤ X^6*X := Nat.mul_le_mul_left _ hx
         _ = X^7 := (pow_succ X 6).symm
  calc
    _ ≤ (X^6+2)^12 := allCost_bound (hd.trans (show n≤X^6 by omega)) r r m l
    _ ≤ (X^7)^12 := Nat.pow_le_pow_left e _
    _ = _ := (pow_mul X 7 12).symm

end PEqualNP.Outside.L_pcx_386.Assembly

namespace PEqualNP.Outside.L_pcx_386.PhysicalBank

open PEqualNP.Outside.L_pcx_386_aux
open PEqualNP.Outside.L_pcx_386.Core PEqualNP.Outside.L_pcx_386.Core.Compiler.Build
open PEqualNP.Outside.L_pcx_386.Placement (span flip)
open PEqualNP.Outside.L_pcx_386.RowShape
open PEqualNP.Outside.L_pcx_386.Assembly
open PEqualNP.Outside.L_pcx_386.Allocation

private lemma flatten_ofFn_eq_getD {α : Type*} (d : α) :
    ∀ (A B : ℕ) (L : Fin A → List α), (∀ a, (L a).length = B) →
      ∀ (a : Fin A) {b : ℕ}, b < B →
        (List.ofFn L).flatten.getD (a.val * B + b) d = (L a).getD b d
  | 0, _, _, _, a, _, _ => Fin.elim0 a
  | A + 1, B, L, hL, a, b, hb => by
    rw [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ ?_ a
    · simp only [Fin.val_zero, zero_mul, zero_add]
      have hlen : b < (L 0).length := by rw [hL 0]; exact hb
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]
    · intro a'
      have hge : (L 0).length ≤ a'.succ.val * B + b := by
        rw [hL 0, Fin.val_succ, Nat.succ_mul]; omega
      have hsub : a'.succ.val * B + b - (L 0).length = a'.val * B + b := by
        rw [hL 0, Fin.val_succ, Nat.succ_mul]; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, hsub]
      simpa only [List.getD_eq_getElem?_getD] using
        flatten_ofFn_eq_getD d A B (fun x => L x.succ) (fun x => hL x.succ) a' hb

def matrixIx (i j : Fin n) : Fin (2+n*n) :=
  ⟨2+(i.val*n+j.val),by
    have h := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
    rw [Nat.succ_mul] at h
    have := j.isLt
    omega⟩

def inverseMatrix (n : ℕ) : LayoutCircuit.Mat n (countLen n) :=
  fun r t x => x (Fin.castAdd ((n+1)*(n+1)*(2*n+1)) (matrixIx t r))

theorem matrix_given {n} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (r t : Fin n) : inverseMatrix n r t ∈ layoutBasis a b := Or.inl (Or.inl ⟨matrixIx t r,rfl⟩)

theorem matrix_correct {n} (σ : Equiv.Perm (Fin n)) (x : Input (countLen n))
    (hp : (List.ofFn x).take (2+n*n)=permPrefix σ) (r t : Fin n) :
    inverseMatrix n r t x=decide (σ.symm r=t) := by
  let j := matrixIx t r
  have hl : j.val<(List.ofFn x).length := j.isLt.trans_le (by rw [List.length_ofFn]; unfold countLen; omega)
  have hs : (List.ofFn x).getD j.val false = (permPrefix σ).getD j.val false := by
    rw [←hp]
    simp [List.getD_eq_getElem?_getD,List.getElem?_take,j.isLt]
  have val : inverseMatrix n r t x=(List.ofFn x).getD j.val false := by
    rw [List.getD_eq_getElem _ _ hl,List.getElem_ofFn];rfl
  rw [val,hs]
  unfold permPrefix
  change (([false,true] : List Bool) ++ (List.ofFn (fun i : Fin n => List.ofFn (fun h : Fin n => decide (σ i=h)))).flatten).getD
    (2+(t.val*n+r.val)) false=_
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_cons,List.length_nil,show 2+(t.val*n+r.val)-(0+1+1)=t.val*n+r.val by omega]
  rw [flatten_ofFn_eq_getD false n n _ (fun _ => by simp) t r.isLt,List.getD_eq_getElem _ _ (by simpa using r.isLt),
    List.getElem_ofFn]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  change σ t=r ↔ σ.symm r=t
  exact ⟨fun h => by rw [← h,Equiv.symm_apply_apply],fun h => by rw [← h,Equiv.apply_symm_apply]⟩

theorem literal_election {n d} (σ : Equiv.Perm (Fin n)) (x : Input (countLen n))
    (hp : (List.ofFn x).take (2+n*n)=permPrefix σ)
    (cover : ∃ seed : Fin d → Fin n, ∀ i, ∃ j : Fin d, ∃ h : Fin n, (σ^h.val) (seed j)=i) :
    ∃ g : Scatter.Guess n d, Scatter.Coherent g ∧ Scatter.guardSig (inverseMatrix n) g x=true ∧
      ∃ e : {a : Fin d // primary (fun i => (g i).1) a} ≃ Layout.Root σ.symm,
        ∀ a, (e a).val=(g a.val).1 ∧ Function.minimalPeriod σ.symm (e a).val=(g a.val).2.val+1 := by
  obtain ⟨g,coh,pass⟩ := Scatter.matches_cover (inverseMatrix n) σ x (matrix_correct σ x hp) cover
  exact ⟨g,coh,pass,matched_rep (inverseMatrix n) g x σ.symm (matrix_correct σ x hp) coh pass⟩

theorem tally_fields (L : List Arc) :
    tally L 0=red L ∧ tally L 1=blue L ∧ tally L 2=L.length ∧ tally L 3=minus L := by
  induction L with
  | nil => decide
  | cons a t ih =>
    rcases a with ⟨r,b,s⟩
    obtain ⟨r₁,b₁,c₁,m₁⟩ := ih
    simp [tally,red,blue,minus,Placement.flip] at r₁ b₁ c₁ m₁ ⊢
    omega

theorem part_bound {a : Arc} {L : List Arc} (h : a∈L) : a.1≤red L ∧ a.2.1≤blue L := by
  induction L with
  | nil => contradiction
  | cons q L ih =>
    rcases List.mem_cons.mp h with rfl|h
    · simp [red,blue]
    · obtain ⟨h1,h2⟩ := ih h
      simp [red,blue] at h1 h2 ⊢
      omega

theorem capacity_bound {n d} (g : Scatter.Guess n d) (i : Fin d) : capacity g i ≤ n := by
  classical
  have := (g i).2.isLt
  unfold capacity
  split <;> omega

theorem asked_congr {n} (b : ChargeIx n → Sig (countLen n)) (q : Width n) (x : Input (countLen n))
    {f h : ℕ × ℕ → ℤ} (e : ∀ w, GoodPair w → f w=h w) : Asked b q x f ↔ Asked b q x h := by
  constructor
  · intro test k hk w hw
    rw [← e w (key_sample (catalog_ok hk) hw).1]
    exact test k hk w hw
  · intro test k hk w hw
    rw [e w (key_sample (catalog_ok hk) hw).1]
    exact test k hk w hw

theorem fits_by_cargo {n} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (σ : Equiv.Perm (Fin n)) (p : Pins n) (x : Input (countLen n)) (q : Width n) (L : List Arc) (floats : ℕ)
    (mass : L.length+q.val=2*n+floats) (trueMass : L.length+free p=2*n+floats)
    (eq : ∀ w, GoodPair w → imbalance L w=imbalance (arcList σ p) w) :
    fitsSignals a b x σ p ↔
      a q x=true ∧ zeroMask (fun m => Scheduled n m.val) b q x=true ∧ Asked b q x (imbalance L) := by
  have E : qIndex p=q := Fin.ext (by change free p=q.val;omega)
  rw [arbitrary_scheduled,E,(asked_congr b q x eq)]

theorem actual_witness {n d} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (σ : Equiv.Perm (Fin n)) (p : Pins n) (x : Input (countLen n)) (g : Scatter.Guess n d)
    (hp : (List.ofFn x).take (2+n*n)=permPrefix σ) (hc : Scatter.Coherent g)
    (pass : Scatter.guardSig (inverseMatrix n) g x=true) (ok : fitsSignals a b x σ p) :
    ∃ (q : Width n) (bag : Fin d → List Arc) (float : Fin d → ℕ),
      (∀ i, tally (bag i) 0=capacity g i ∧ tally (bag i) 1=capacity g i ∧
        tally (bag i) 2≤2*n ∧ tally (bag i) 3 % 2=0 ∧ float i ≤ 1 ∧
        (float i=1 → bag i=[(capacity g i,capacity g i,true)])) ∧
      (∀ i, ¬primary (fun j => (g j).1) i → bag i=[] ∧ float i=0) ∧
      (∀ i a, a∈bag i → Raw n (a.1,a.2.1)) ∧
      (catRows bag).length+q.val=2*n+∑ i,float i ∧ a q x=true ∧
      zeroMask (fun m => Scheduled n m.val) b q x=true ∧ Asked b q x (imbalance (catRows bag)) := by
  classical
  obtain ⟨e,good⟩ := matched_rep (inverseMatrix n) g x σ.symm (matrix_correct σ x hp) hc pass
  obtain ⟨bag,float,loc,pad,shape,mass,equal⟩ := witness_packets σ p g e (fun x => (good x).2)
  refine ⟨qIndex p,bag,float,?_,pad,?_,mass,(fits_by_cargo a b σ p x (qIndex p) (catRows bag) _ mass mass equal).mp ok⟩
  · intro i
    obtain ⟨r,b,c,m⟩ := tally_fields (bag i)
    obtain ⟨rr,bb,neg,one,single⟩ := loc i
    have bl := length_le_mass (bag i) (fun u hu => (shape i u hu).1)
    have cap := capacity_bound g i
    exact ⟨r.trans rr,b.trans bb,by omega,m ▸ neg,one,single⟩
  · intro i u hu
    obtain ⟨sp,e1,e2⟩ := shape i u hu
    obtain ⟨r,b⟩ := part_bound hu
    obtain ⟨rr,bb,_,_,_⟩ := loc i
    exact ⟨sp,r.trans (rr ▸ capacity_bound g i),b.trans (bb ▸ capacity_bound g i),e1,e2⟩

theorem cat_length {d} (bags : Fin d → List Arc) : (catRows bags).length=∑ i,(bags i).length := by
  simp [catRows,List.length_flatMap,Finset.sum_map_toList]

theorem minus_le_length (L : List Arc) : minus L ≤ L.length := by
  induction L with
  | nil => rfl
  | cons a t ih => cases h : Placement.flip a <;> simp [minus,h] at ih ⊢ <;> omega

theorem singleton_fields {L : List Arc} {r : ℕ} (hr : red L=r) (hb : blue L=r)
    (hl : L.length=1) (hm : minus L=0) : L=[(r,r,true)] := by
  cases L with
  | nil => contradiction
  | cons a t =>
    have ht : t=[] := List.eq_nil_of_length_eq_zero (by change t.length+1=1 at hl; omega)
    subst t
    rcases a with ⟨R,B,s⟩
    cases s <;> simp [red,blue,minus,Placement.flip] at hr hb hm ⊢ <;> exact ⟨hr,hb⟩

def Terminal {n d} (g : Scatter.Guess n d) (q : Width n) (t : State n d) (mask : Fin d → Bool) : Prop :=
  t.1.val=0 ∧
  (∀ i, (t.2 i 0).val=capacity g i ∧ (t.2 i 1).val=capacity g i ∧ (t.2 i 3).val % 2=0 ∧
    (mask i=true → (t.2 i 2).val=1 ∧ (t.2 i 3).val=0)) ∧
    ((∑ i, (t.2 i 2).val)+q.val=2*n+∑ i, (mask i).toNat)

theorem capacity_total {n d} (σ : Equiv.Perm (Fin n)) (x : Input (countLen n)) (g : Scatter.Guess n d)
    (hp : (List.ofFn x).take (2+n*n)=permPrefix σ) (hc : Scatter.Coherent g)
    (pass : Scatter.guardSig (inverseMatrix n) g x=true) : ∑ i,capacity g i=n := by
  classical
  obtain ⟨e,good⟩ := matched_rep (inverseMatrix n) g x σ.symm (matrix_correct σ x hp) hc pass
  have hr := Fintype.card_congr (Layout.slotsEquiv σ.symm)
  simp only [Layout.Active,Fintype.card_sigma,Fintype.card_fin] at hr
  let F := Finset.univ.filter (fun i => RowShape.primary (fun j => (g j).1) i)
  have iff (i : Fin d) : i∈F ↔ RowShape.primary (fun j => (g j).1) i := by simp [F]
  calc
    _ = ∑ i ∈ F,capacity g i := (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by
      rw [capacity,if_neg (fun h => hi ((iff i).mpr h))])).symm
    _ = ∑ r : {i // RowShape.primary (fun j => (g j).1) i},capacity g r.val := Finset.sum_subtype F iff _
    _ = ∑ r,Function.minimalPeriod σ.symm (e r).val := Finset.sum_congr rfl fun r _ =>
      (show capacity g r.val=(g r.val).2.val+1 from if_pos r.property).trans (good r).2.symm
    _ = n := (e.sum_comp (fun r : Layout.Root σ.symm => Function.minimalPeriod σ.symm r.val)).trans hr

theorem total_length {n d} (g : Scatter.Guess n d) (bags : Fin d → List Arc)
    (cap : ∑ i, capacity g i=n) (rr : ∀ i, tally (bags i) 0=capacity g i) (bb : ∀ i, tally (bags i) 1=capacity g i)
    (sh : ∀ i a, a∈bags i → Raw n (a.1,a.2.1)) : (List.ofFn bags).flatten.length ≤ 2*n := by
  simp only [List.length_flatten,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  calc
    _ ≤ ∑ i, (capacity g i+capacity g i) := Finset.sum_le_sum (fun i _ => by
      have h := length_le_mass (bags i) (fun u hu => (sh i u hu).1)
      rw [← (tally_fields _).1,← (tally_fields _).2.1,rr,bb] at h
      exact h)
    _ = _ := by rw [Finset.sum_add_distrib,cap]; omega

theorem endpoint_witness {n d} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (σ : Equiv.Perm (Fin n)) (p : Pins n) (x : Input (countLen n)) (g : Scatter.Guess n d)
    (hp : (List.ofFn x).take (2+n*n)=permPrefix σ) (hc : Scatter.Coherent g)
    (pass : Scatter.guardSig (inverseMatrix n) g x=true) (ok : fitsSignals a b x σ p) :
    ∃ (q : Width n) (t : State n d) (mask : Fin d → Bool) (bags : Fin d → List Arc),
      Terminal g q t mask ∧ (∀ i j, (t.2 i j).val=tally (bags i) j) ∧
      (∀ i u, u∈bags i → Raw n (u.1,u.2.1)) ∧ (List.ofFn bags).flatten.length≤2*n ∧ a q x=true ∧
      zeroMask (fun m => Scheduled n m.val) b q x=true ∧ Asked b q x (imbalance (catRows bags)) := by
  classical
  obtain ⟨q,bags,float,localH,_,shape,mass,check,missing,ask⟩ := actual_witness a b σ p x g hp hc pass ok
  have fits (i : Fin d) (j : Fin 4) : tally (bags i) j < 2*n+1 := by
    obtain ⟨r,b,c,neg,one,single⟩ := localH i
    obtain ⟨_,_,len,mi⟩ := tally_fields (bags i)
    have h := capacity_bound g i
    have m := minus_le_length (bags i)
    rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 by fin_cases j <;> decide) with rfl|rfl|rfl|rfl <;> omega
  let t : State n d := (0,fun i j => ⟨tally (bags i) j,fits i j⟩)
  let mask : Fin d → Bool := fun i => decide (float i=1)
  have val (i : Fin d) : (mask i).toNat = float i := by
    have H := (localH i).2.2.2.2.1
    by_cases h : float i=1 <;> simp [mask,h] <;> omega
  have total := total_length g bags (capacity_total σ x g hp hc pass) (fun i => (localH i).1) (fun i => (localH i).2.1) shape
  refine ⟨q,t,mask,bags,⟨rfl,?_,?_⟩,fun _ _ => rfl,shape,total,check,missing,ask⟩
  · intro i
    obtain ⟨r,b,_,neg,_,single⟩ := localH i
    refine ⟨r,b,neg,fun yes => ?_⟩
    have eq := single (of_decide_eq_true yes)
    change tally (bags i) 2=1 ∧ tally (bags i) 3=0
    simp [eq,tally]
  · change (∑ i, tally (bags i) 2)+q.val = 2*n+∑ i,(mask i).toNat
    simp_rw [val,fun i => (tally_fields (bags i)).2.2.1]
    rwa [cat_length] at mass

theorem endpoint_sound {n d} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (σ : Equiv.Perm (Fin n)) (x : Input (countLen n)) (g : Scatter.Guess n d)
    (q : Width n) (t : State n d) (mask : Fin d → Bool) (term : Terminal g q t mask)
    (hp : (List.ofFn x).take (2+n*n)=permPrefix σ) (hc : Scatter.Coherent g)
    (pass : Scatter.guardSig (inverseMatrix n) g x=true)
    (D R B : Fin d → List Arc) (wire : Fin d × Bool × Fin (2*n+1) → Sig (countLen n))
    (hd : ∀ i u, u∈D i → u.1=u.2.1) (hr : ∀ i u, u∈R i → u.1=u.2.1+1)
    (hb : ∀ i u, u∈B i → u.2.1=u.1+1)
    (positive : ∀ i u, u∈D i++R i++B i → 0<span u)
    (tallies : ∀ i j, (t.2 i j).val=tally (D i++R i++B i) j)
    (read : ∀ i k, (if wire (i,false,k) x then some (wire (i,true,k) x) else none) =
        (Placement.word (mask i) (D i++Placement.weave (R i) (B i))).getD k.val none)
    (width : a q x=true) (tail : zeroMask (fun m => Scheduled n m.val) b q x=true)
    (ask : Asked b q x (imbalance (catRows (fun i => D i++R i++B i)))) :
    let pins := fun z (v : Bool × Fin n) => Scatter.out (inverseMatrix n) (fanMarks g wire) (z,v)
    fitsSignals a b x σ (readPins pins x) := by
  classical
  let bags (i : Fin d) := D i++R i++B i
  let pins := Scatter.physical (inverseMatrix n) (fanMarks g wire) x
  have rr (i) : red (bags i)=capacity g i := (tally_fields _).1.symm.trans ((tallies i 0).symm.trans (term.2.1 i).1)
  have bb (i) : blue (bags i)=capacity g i := (tally_fields _).2.1.symm.trans ((tallies i 1).symm.trans (term.2.1 i).2.1)
  have mm (i) : minus (bags i)=(t.2 i 3).val := (tally_fields _).2.2.2.symm.trans (tallies i 3).symm
  have nn (i) : (bags i).length=(t.2 i 2).val := (tally_fields _).2.2.1.symm.trans (tallies i 2).symm
  have ss (i) (yes : mask i=true) : ∃ k, (bags i).Perm [(k,k,true)] := by
    obtain ⟨len,neg⟩ := (term.2.1 i).2.2.2 yes
    exact ⟨capacity g i,List.perm_singleton.mpr (singleton_fields (rr i) (bb i) ((nn i).trans len) ((mm i).trans neg))⟩
  obtain ⟨_,real,eq⟩ := output_sound (inverseMatrix n) g wire x σ (matrix_correct σ x hp) hc pass D R B mask hd hr hb
    positive rr bb (fun i => (mm i) ▸ (term.2.1 i).2.2.1) ss read
  have mass : (catRows bags).length+q.val=2*n+∑ i,(mask i).toNat := by
    rw [cat_length]; simp_rw [nn]; exact term.2.2
  exact (fits_by_cargo a b σ pins x q (catRows bags) _ mass real eq).mpr ⟨width,tail,ask⟩

end PEqualNP.Outside.L_pcx_386.PhysicalBank

namespace PEqualNP.Outside.L_pcx_386.Allocation

open PEqualNP.Outside.L_pcx_386.Core
open PEqualNP.Outside.L_pcx_386.Core.Compiler.Build

def height : StageKey → ℕ
  | .diag j | .finishChain j => j
  | .skew _ _ => 0

theorem chain_origin (n t j : ℕ) {k : StageKey} (hk : k∈chain n t j) :
    ∃ a : ℕ, k=.diag (2^a*j) ∨ k=.finishChain (2^a*j) := by
  induction t generalizing j with
  | zero =>
    have eq : k=.finishChain j := by simpa [chain] using hk
    exact ⟨0,Or.inr (by simpa using eq)⟩
  | succ t ih =>
    by_cases h : j≤n
    · simp only [chain,ite_eq_left h,List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact ⟨0,Or.inl (by simp)⟩
      · obtain ⟨a,ha⟩ := ih (2*j) hk
        exact ⟨a+1,by simpa only [pow_succ,Nat.mul_assoc] using ha⟩
    · have eq : k=.finishChain j := by simpa [chain,h] using hk
      exact ⟨0,Or.inr (by simpa using eq)⟩

theorem chain_nodup (n t j : ℕ) (hj : 0<j) : (chain n t j).Nodup := by
  induction t generalizing j with
  | zero => simp [chain]
  | succ t ih =>
    by_cases h : j≤n
    · simp only [chain,ite_eq_left h,List.nodup_cons]
      refine ⟨?_,ih (2*j) (by omega)⟩
      intro hm
      obtain ⟨a,he | he⟩ := chain_origin n t (2*j) hm
      · have := StageKey.diag.inj he
        have := Nat.le_mul_of_pos_left (2*j) (by positivity : 0<2^a)
        omega
      · cases he
    · simp [chain,h]

theorem catalog_nodup (n : ℕ) : (catalog n).Nodup := by
  let F (i : ℕ) := [StageKey.skew i (i+1),.skew (i+1) i]
  let G (o : ℕ) := if Odd o then chain n (n+1) o else []
  have fdisj {i j} (h : i≠j) : (F i).Disjoint (F j) := by
    intro k hi hj
    simp only [F,List.mem_cons,List.not_mem_nil,or_false] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with e | e <;> (injection e; omega)
  have gdisj {i j} (h : i≠j) : (G i).Disjoint (G j) := by
    intro k hi hj
    by_cases oi : Odd i
    · by_cases oj : Odd j
      · obtain ⟨a,ha⟩ := chain_origin n (n+1) i (by simpa [G,oi] using hi)
        obtain ⟨b,hb⟩ := chain_origin n (n+1) j (by simpa [G,oj] using hj)
        have ha' : height k=2^a*i := by rcases ha with e|e <;> rw [e] <;> rfl
        have hb' : height k=2^b*j := by rcases hb with e|e <;> rw [e] <;> rfl
        exact h (dyadic_unique oi oj a b (ha'.symm.trans hb')).2
      · simp [G,oj] at hj
    · simp [G,oi] at hi
  have fseen : ((List.range n).flatMap F).Nodup :=
    List.nodup_flatMap.mpr ⟨fun j _ => by simp [F],List.Pairwise.imp (fun h => fdisj h) List.nodup_range⟩
  have gseen : ((List.range (n+1)).flatMap G).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨?_,List.Pairwise.imp (fun h => gdisj h) List.nodup_range⟩
    intro o _
    by_cases odd : Odd o
    · have hp : 0<o := by obtain ⟨q,hq⟩ := odd; omega
      simpa [G,odd] using chain_nodup n (n+1) o hp
    · simp [G,odd]
  change (((List.range n).flatMap F) ++ ((List.range (n+1)).flatMap G)).Nodup
  apply List.pairwise_append.mpr
  refine ⟨fseen,gseen,?_⟩
  rintro k hk _ hl rfl
  obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp hk
  obtain ⟨o,_,ho⟩ := List.mem_flatMap.mp hl
  by_cases odd : Odd o
  · obtain ⟨z,hz⟩ := chain_origin n (n+1) o (by simpa [G,odd] using ho)
    simp only [F,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl <;> rcases hz with h|h <;> cases h
  · simp [G,odd] at ho

def firstPair : StageKey → ℕ × ℕ
  | .diag j | .finishChain j => (j,j)
  | .skew r b => (r,b)

def blank : StageKey → Row
  | .diag j => .diag j 0
  | .finishChain _ => .close 0
  | .skew r b => .skew r b 0 0

def measure {n} (b : ChargeIx n → Sig (countLen n)) (q : Width n) (w : ℕ × ℕ) :=
  lookup b q (sampleOrder n w)

def liveEdge {n d} (b : ChargeIx n → Sig (countLen n)) (q : Width n) (k : StageKey) (s t : State n d) :=
  edgeSignal (measure b q (firstPair k)) (measure b q (twicePair (firstPair k))) (blank k) s t

def NextCarry {n d} (k : StageKey) (s t : State n d) (c : Choice n d) : Prop :=
  match k with
  | .diag _ => t.1.val=pos c
  | .finishChain _ => t.1.val=0
  | .skew _ _ => s.1.val=0 ∧ t.1.val=0

def reads {n d} (k : StageKey) (s : State n d) (c : Choice n d) (w : ℕ × ℕ) : ℤ :=
  match k with
  | .diag _ => (neg c : ℤ)-pos c+s.1.val
  | .finishChain _ => s.1.val
  | .skew r b => if w=(r,b) then (neg c : ℤ)-pos c else pos c

theorem stage_exact {n d} (b : ChargeIx n → Sig (countLen n)) (q : Width n) (k : StageKey)
    (hk : KeyOK n k) (s t : State n d) (x : Input (countLen n)) :
    liveEdge b q k s t x = true ↔ ∃ c : Choice n d, Moves (blank k) s t c ∧ NextCarry k s t c ∧
      ∀ w ∈ samples k, measure b q w (reads k s c w) x = true := by
  simp only [liveEdge,edgeSignal,decide_eq_true_eq]
  apply exists_congr
  intro c
  by_cases hm : Moves (blank k) s t c
  · simp only [testDose,hm,ite_true,true_and]
    cases k with
    | diag j =>
      by_cases good : t.1.val=pos c <;> simp [blank,NextCarry,firstPair,good,samples,reads]
    | finishChain j =>
      by_cases good : t.1.val=0 <;> simp only [blank,NextCarry,firstPair,good,ite_true,ite_false,true_and,false_and] <;> simp [samples,reads]
    | skew r l =>
      obtain ⟨_,_,hd⟩ := hk
      have ne : twicePair (r,l) ≠ (r,l) := by simp [twicePair,Prod.ext_iff]; omega
      by_cases good : s.1.val=0 ∧ t.1.val=0
      · simp only [blank,NextCarry,firstPair,good,ite_true,true_and]
        simp [samples,reads,ne,an]
      · simp only [blank,NextCarry,firstPair,good,ite_false,false_and,Bool.false_eq_true]
  · simp [testDose,hm]

theorem live_edge_bank {n d} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n)) (q : Width n) :
    Build (layoutBasis a b) (Set.range (fun ix : Fin (catalog n).length × State n d × State n d =>
      liveEdge b q ((catalog n).get ix.1) ix.2.1 ix.2.2)) ((n+2)^(20*(d+1))) :=
  all_edge_budget (fun i => blank ((catalog n).get i))
    (fun i => measure b q (firstPair ((catalog n).get i)))
    (fun i => measure b q (twicePair (firstPair ((catalog n).get i))))
    (Or.inl (Or.inr (Or.inl rfl))) (fun _ _ => lookup_mem ..) (fun _ _ => lookup_mem ..) (catalog_length n)

end PEqualNP.Outside.L_pcx_386.Allocation

namespace PEqualNP.Outside.L_pcx_386.Allocation

open PEqualNP.Outside.L_pcx_386.Core
open PEqualNP.Outside.L_pcx_386.Core.Compiler.Build

instance {n w} : Decidable (Raw n w) := by unfold Raw; infer_instance

def keyOf (w : ℕ × ℕ) := if w.1=w.2 then StageKey.diag w.1 else .skew w.1 w.2

def units {n d} (D : StageKey → Choice n d) (s : Bool) (w : ℕ × ℕ) : ℕ :=
  if Raw n w then if s then pos (D (keyOf w)) else neg (D (keyOf w)) else 0

def halfValue (P : ℕ × ℕ → ℕ) (w : ℕ × ℕ) : ℕ :=
  if 2∣w.1 ∧ 2∣w.2 then P (w.1/2,w.2/2) else 0

def pulse (P M : ℕ × ℕ → ℕ) (w : ℕ × ℕ) : ℤ := (M w : ℤ)-P w+halfValue P w

theorem pulse_inventory (L : List Arc) (w : ℕ × ℕ) :
    pulse (fun v => perDirection v true L) (fun v => perDirection v false L) w = imbalance L w := by
  obtain ⟨r,b⟩ := w
  by_cases h : 2∣r ∧ 2∣b
  · obtain ⟨i,hi⟩ := h.1
    obtain ⟨j,hj⟩ := h.2
    subst r; subst b
    simpa [pulse,halfValue,twicePair] using (imbalance_at_twice L (i,j)).symm
  · have bad (a : ℕ × ℕ) : (r,b)≠twicePair a := by
      intro eq
      apply h
      exact ⟨⟨a.1,congrArg Prod.fst eq⟩,⟨a.2,congrArg Prod.snd eq⟩⟩
    simpa [pulse,halfValue,h] using (imbalance_primitive L bad).symm

def before (P : ℕ × ℕ → ℕ) : StageKey → ℕ
  | .diag j | .finishChain j => halfValue P (j,j)
  | .skew _ _ => 0

def after (P : ℕ × ℕ → ℕ) : StageKey → ℕ
  | .diag j => P (j,j)
  | _ => 0

def Links (P : ℕ × ℕ → ℕ) : ℕ → List StageKey → ℕ → Prop
  | i,[],j => i=j
  | i,k::ks,j => i=before P k ∧ Links P (after P k) ks j

theorem link_join {P a b c} {L R : List StageKey} (u : Links P a L b) (v : Links P b R c) :
    Links P a (L++R) c := by
  induction L generalizing a with
  | nil => exact (show a=b from u) ▸ v
  | cons k ks ih => exact ⟨u.1,ih u.2⟩

theorem link_blocks {α} (P) (f : α → List StageKey) (L : List α) (h : ∀ i, Links P 0 (f i) 0) :
    Links P 0 (L.flatMap f) 0 := by
  induction L with
  | nil => rfl
  | cons a t ih => exact link_join (h a) ih

theorem link_chain (P) (n t j : ℕ) : Links P (halfValue P (j,j)) (chain n t j) 0 := by
  induction t generalizing j with
  | zero => exact ⟨rfl,rfl⟩
  | succ t ih =>
    by_cases h : j≤n
    · rw [chain,ite_eq_left h]
      refine ⟨rfl,?_⟩
      simpa only [after,halfValue,Nat.dvd_mul_right,true_and,ite_true,Nat.mul_div_cancel_left,
        show 0<2 by decide] using ih (2*j)
    · rw [chain,ite_eq_right h]; exact ⟨rfl,rfl⟩

theorem link_catalog (P) (n : ℕ) : Links P 0 (catalog n) 0 := by
  apply link_join
  · apply link_blocks
    intro i; exact ⟨rfl,rfl,rfl⟩
  · apply link_blocks
    intro o
    by_cases odd : Odd o
    · have h : ¬2∣o := by obtain ⟨q,hq⟩ := odd; omega
      simpa [odd,halfValue,h] using link_chain P n (n+1) o
    · simp [odd,Links]

theorem read_pulse {n d} (D : StageKey → Choice n d) (k) (hk : KeyOK n k) (s : State n d)
    (hs : s.1.val=before (units D true) k) {w} (hw : w∈samples k) :
    reads k s (D k) w = pulse (units D true) (units D false) w := by
  cases k with
  | diag j =>
    obtain ⟨hj,hbound⟩ := hk
    have raw : Raw n (j,j) := ⟨by omega,hbound,hbound,by omega,by omega⟩
    obtain rfl : w=(j,j) := by simpa [samples] using hw
    simp [reads,pulse,hs,before,units,raw,keyOf]
  | finishChain j =>
    obtain ⟨hj,_,_⟩ := hk
    have raw : ¬Raw n (j,j) := fun h => Nat.not_le_of_lt hj h.2.1
    obtain rfl : w=(j,j) := by simpa [samples] using hw
    simp [reads,pulse,hs,before,units,raw]
  | skew r b =>
    obtain ⟨hr,hb,hd⟩ := hk
    have raw : Raw n (r,b) := ⟨by omega,hr,hb,by omega,by omega⟩
    have rd : r≠b := by omega
    have nh : ¬(2∣r ∧ 2∣b) := by omega
    have nd : twicePair (r,b)≠(r,b) := by simp [twicePair,Prod.ext_iff]; omega
    have bad : ¬Raw n (twicePair (r,b)) := by
      rintro ⟨_,_,_,h1,h2⟩; dsimp [twicePair] at h1 h2; omega
    have dbl : halfValue (units D true) (twicePair (r,b)) = units D true (r,b) := by simp [halfValue,twicePair]
    simp only [samples,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl | rfl
    · simp [reads,pulse,halfValue,nh,units,raw,keyOf,rd]
    · simp [reads,pulse,nd,dbl,units,raw,bad,keyOf,rd]

theorem next_after {n d} (D : StageKey → Choice n d) (k) (hk : KeyOK n k) (s t : State n d)
    (h : NextCarry k s t (D k)) : t.1.val=after (units D true) k := by
  cases k with
  | diag j =>
    obtain ⟨hj,hbound⟩ := hk
    have raw : Raw n (j,j) := ⟨by omega,hbound,hbound,by omega,by omega⟩
    simpa [NextCarry,after,units,raw,keyOf] using h
  | finishChain _ => exact h
  | skew _ _ => exact h.2

def Walk {K V : Type} (e : K → V → V → Prop) : List K → V → V → Prop
  | [],s,t => s=t
  | k::ks,s,t => ∃ m, e k s m ∧ Walk e ks m t

theorem walk_local {K V : Type} {e f : K → V → V → Prop} (L : List K) (s t : V)
    (h : ∀ k∈L, ∀ u v, e k u v ↔ f k u v) : Walk e L s t ↔ Walk f L s t := by
  induction L generalizing s with
  | nil => rfl
  | cons k ks ih =>
    exact exists_congr fun m => and_congr (h k List.mem_cons_self s m)
      (ih m (fun j hj => h j (List.mem_cons_of_mem k hj)))

theorem section_walk {K V C : Type} [DecidableEq K] [Nonempty C] (e : K → V → V → C → Prop)
    (L : List K) (hn : L.Nodup) (s t : V) :
    Walk (fun k u v => ∃ c,e k u v c) L s t ↔ ∃ D : K → C, Walk (fun k u v => e k u v (D k)) L s t := by
  classical
  induction L generalizing s with
  | nil => exact ⟨fun h => ⟨fun _ => Classical.choice inferInstance,h⟩,fun ⟨_,h⟩ => h⟩
  | cons k ks ih =>
    obtain ⟨miss,uniq⟩ := List.nodup_cons.mp hn
    constructor
    · rintro ⟨m,⟨c,hc⟩,tail⟩
      obtain ⟨D,he⟩ := (ih uniq m).mp tail
      let E := Function.update D k c
      refine ⟨E,m,by simpa [E] using hc,(walk_local ks m t ?_).mp he⟩
      intro j hj u v
      have ne : j≠k := fun eq => miss (eq ▸ hj)
      simp [E,Function.update_of_ne ne]
    · rintro ⟨D,m,h,tail⟩
      exact ⟨m,⟨D k,h⟩,(ih uniq m).mpr ⟨D,tail⟩⟩

def Motion {n d} (D : StageKey → Choice n d) (k) (s t : State n d) :=
  Moves (blank k) s t (D k) ∧ NextCarry k s t (D k)

def Tests {n d} (b : ChargeIx n → Sig (countLen n)) (q : Width n) (x : Input (countLen n))
    (k) (s : State n d) (c : Choice n d) :=
  ∀ w∈samples k, measure b q w (reads k s c w) x=true

theorem fixed_bank {n d} (b : ChargeIx n → Sig (countLen n)) (q : Width n) (x : Input (countLen n))
    (D : StageKey → Choice n d) (L : List StageKey) (s t : State n d) (endCarry : ℕ)
    (hk : ∀ k∈L, KeyOK n k) (links : Links (units D true) s.1.val L endCarry) :
    Walk (fun k u v => Motion D k u v ∧ Tests b q x k u (D k)) L s t ↔
      Walk (Motion D) L s t ∧ ∀ k∈L, ∀ w∈samples k,
        measure b q w (pulse (units D true) (units D false) w) x=true := by
  induction L generalizing s with
  | nil => simp [Walk]
  | cons k ks ih =>
    have ok := hk k List.mem_cons_self
    have suffix (m : State n d) (hm : Motion D k s m) :=
      ih m (fun j hj => hk j (List.mem_cons_of_mem _ hj))
        (show Links (units D true) m.1.val ks endCarry by rw [next_after D k ok s m hm.2]; exact links.2)
    have val := fun (w : ℕ × ℕ) (hw : w∈samples k) => read_pulse D k ok s links.1 hw
    constructor
    · rintro ⟨m,⟨move,tests⟩,trail⟩
      obtain ⟨path,qs⟩ := (suffix m move).mp trail
      refine ⟨⟨m,move,path⟩,?_⟩
      intro j hj w hw
      rcases List.mem_cons.mp hj with rfl | hj
      · simpa only [val w hw] using tests w hw
      · exact qs j hj w hw
    · rintro ⟨⟨m,move,trail⟩,qs⟩
      exact ⟨m,⟨move,fun w hw => by simpa only [val w hw] using qs k List.mem_cons_self w hw⟩,
        (suffix m move).mpr ⟨trail,fun j hj => qs j (List.mem_cons_of_mem k hj)⟩⟩

theorem accepting_catalog {n d} (b : ChargeIx n → Sig (countLen n)) (q : Width n) (x : Input (countLen n))
    (s t : State n d) (hs : s.1.val=0) :
    Walk (fun k u v => liveEdge b q k u v x=true) (catalog n) s t ↔
      ∃ D : StageKey → Choice n d, Walk (Motion D) (catalog n) s t ∧
        Asked b q x (pulse (units D true) (units D false)) := by
  let e (k) (u v : State n d) (c : Choice n d) := (Moves (blank k) u v c ∧ NextCarry k u v c) ∧ Tests b q x k u c
  have localEq (k) (hk : k∈catalog n) (u v : State n d) : liveEdge b q k u v x=true ↔ ∃ c,e k u v c := by
    rw [stage_exact b q k (catalog_ok hk)]
    exact exists_congr fun c => and_assoc.symm
  rw [walk_local (catalog n) s t localEq,section_walk e (catalog n) (catalog_nodup n)]
  exact exists_congr fun D => fixed_bank b q x D (catalog n) s t 0 (fun _ => catalog_ok)
    (by rw [hs]; exact link_catalog _ n)

end PEqualNP.Outside.L_pcx_386.Allocation

namespace PEqualNP.Outside.L_pcx_386.Allocation

open PEqualNP.Outside.L_pcx_386.Core
open PEqualNP.Outside.L_pcx_386.Core.Compiler.Build

def primary : StageKey → Option (ℕ × ℕ)
  | .diag j => some (j,j)
  | .finishChain _ => none
  | .skew r b => some (r,b)

theorem primary_spec {n k w} (hk : KeyOK n k) : primary k=some w ↔ Raw n w ∧ k=keyOf w := by
  cases k with
  | diag j =>
    obtain ⟨hj,hbound⟩ := hk
    change some (j,j)=some w ↔ _
    constructor
    · rintro ⟨⟩
      exact ⟨⟨by omega,hbound,hbound,by omega,by omega⟩,by simp [keyOf]⟩
    · rintro ⟨_,h⟩
      obtain ⟨r,b⟩ := w
      by_cases eq : r=b <;> simp [keyOf,eq] at h ⊢; grind
  | finishChain j => by_cases h : w.1=w.2 <;> simp [primary,keyOf,h]
  | skew r b =>
    obtain ⟨hr,hb,hd⟩ := hk
    have ne : r≠b := by omega
    change some (r,b)=some w ↔ _
    constructor
    · rintro ⟨⟩
      exact ⟨⟨by omega,hr,hb,by omega,by omega⟩,by simp [keyOf,ne]⟩
    · rintro ⟨_,h⟩
      obtain ⟨u,v⟩ := w
      by_cases eq : u=v <;> simp [keyOf,eq] at h ⊢; grind

theorem raw_key_mem {n w} (raw : Raw n w) : keyOf w ∈ catalog n := by
  obtain ⟨k,hk,hp⟩ := (catalog_hits raw).1
  have ok := catalog_ok hk
  have h : primary k=some w := by
    cases k with
    | diag j => simpa [samples,primary,eq_comm] using hp
    | finishChain j =>
      obtain rfl : w=(j,j) := by simpa [samples] using hp
      exact False.elim ((Nat.not_le_of_lt ok.1) raw.2.1)
    | skew r b =>
      simp only [samples,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl
      · rfl
      · obtain ⟨_,_,hd⟩ := ok
        obtain ⟨_,_,_,h1,h2⟩ := raw
        dsimp [twicePair] at h1 h2
        omega
  exact ((primary_spec ok).mp h).2 ▸ hk

def cargo {n d} (D : StageKey → Choice n d) (L : List StageKey) (i : Fin d) : List Arc :=
  L.flatMap fun k => packet (blank k) (D k) i

def aggregate {n d} (D : StageKey → Choice n d) : List Arc := (List.ofFn (cargo D (catalog n))).flatten

theorem dir_count (w : ℕ × ℕ) (s : Bool) (L : List Arc) : perDirection w s L = L.count (w.1,w.2,s) := by
  obtain ⟨r,b⟩ := w
  induction L with
  | nil => simp [perDirection]
  | cons a L ih =>
    obtain ⟨u,v,f⟩ := a
    have eq : ((u,v,f) : Arc)=(r,b,s) ↔ (r,b)=(u,v) ∧ s=f := by simp [Prod.ext_iff,eq_comm,and_assoc]
    simp only [perDirection,List.count_cons,beq_iff_eq,eq,ih,Nat.add_comm]

theorem dir_append (w : ℕ × ℕ) (s : Bool) (L R : List Arc) :
    perDirection w s (L++R) = perDirection w s L + perDirection w s R := by
  simp only [dir_count,List.count_append]

theorem dir_bundle (w : ℕ × ℕ) (s : Bool) (r b plus minus : ℕ) :
    perDirection w s (bundle r b plus minus) = if w=(r,b) then if s then plus else minus else 0 := by
  obtain ⟨x,y⟩ := w
  simp only [dir_count,bundle,List.count_append,List.count_replicate,beq_iff_eq,Prod.mk.injEq]
  cases s <;> split_ifs <;> grind

def weight {n d} (c : Choice n d) (i : Fin d) (s : Bool) := if s then (c i).1.val else (c i).2.val

theorem dir_packet {n d} (k) (c : Choice n d) (i : Fin d) (w) (s : Bool) :
    perDirection w s (packet (blank k) c i) = if primary k=some w then weight c i s else 0 := by
  cases k <;> simp [blank,packet,primary,dir_bundle,weight,eq_comm,perDirection]

theorem dir_cargo {n d} (D : StageKey → Choice n d) (L : List StageKey) (i : Fin d) (w) (s : Bool)
    (hn : L.Nodup) (ok : ∀ k∈L,KeyOK n k) :
    perDirection w s (cargo D L i) = if Raw n w ∧ keyOf w∈L then weight (D (keyOf w)) i s else 0 := by
  induction L with
  | nil => simp [cargo,perDirection]
  | cons k ks ih =>
    obtain ⟨miss,uniq⟩ := List.nodup_cons.mp hn
    change perDirection w s (packet (blank k) (D k) i ++ cargo D ks i) = _
    simp only [dir_append,dir_packet,primary_spec (ok k List.mem_cons_self),
      ih uniq (fun j hj => ok j (List.mem_cons_of_mem k hj))]
    by_cases raw : Raw n w
    · by_cases eq : k=keyOf w
      · subst k; simp [raw,miss]
      · simp [eq,Ne.symm eq,raw]
    · simp [raw]

theorem dir_flat (w) (s : Bool) (ls : List (List Arc)) :
    perDirection w s ls.flatten = (ls.map (perDirection w s)).sum := by
  induction ls with
  | nil => simp [perDirection]
  | cons l ls ih => simp [dir_append,ih]

theorem dir_aggregate {n d} (D : StageKey → Choice n d) (w) (s : Bool) :
    perDirection w s (aggregate D) = units D s w := by
  rw [aggregate,dir_flat,List.map_ofFn,List.sum_ofFn]
  by_cases raw : Raw n w
  · have key := raw_key_mem raw
    cases s <;> simp [dir_cargo D (catalog n) _ w _ (catalog_nodup n) (fun _ => catalog_ok),
      units,raw,key,weight,pos,neg]
  · simp [dir_cargo D (catalog n) _ w _ (catalog_nodup n) (fun _ => catalog_ok),units,raw]

theorem signed_cargo {n d} (D : StageKey → Choice n d) (w) :
    imbalance (aggregate D) w = pulse (units D true) (units D false) w := by
  rw [← pulse_inventory]
  simp only [dir_aggregate]

theorem motion_bounds {n d} (D : StageKey → Choice n d) (L) (s t : State n d) (ok : ∀ k∈L,KeyOK n k)
    (h : Walk (Motion D) L s t) :
    (∀ k∈L, after (units D true) k ≤ 2*n) ∧
      ∀ i j, (t.2 i j).val=(s.2 i j).val+tally (cargo D L i) j := by
  induction L generalizing s with
  | nil =>
    obtain rfl : s=t := h
    simp [cargo,tally]
  | cons k ks ih =>
    obtain ⟨m,move,trail⟩ := h
    obtain ⟨small,tot⟩ := ih m (fun j hj => ok j (List.mem_cons_of_mem k hj)) trail
    constructor
    · intro a ha
      rcases List.mem_cons.mp ha with rfl|ha
      · rw [← next_after D a (ok a List.mem_cons_self) s m move.2]
        exact Nat.le_of_lt_succ m.1.isLt
      · exact small a ha
    · intro i j
      rw [tot i j,move.1 i j]
      change _=(s.2 i j).val+tally (packet (blank k) (D k) i++cargo D ks i) j
      rw [tally_append,Pi.add_apply,Nat.add_assoc]

theorem next_of_positions {n d} (D : StageKey → Choice n d) (k) (hk : KeyOK n k) (s t : State n d)
    (hs : s.1.val=before (units D true) k) (ht : t.1.val=after (units D true) k) :
    NextCarry k s t (D k) := by
  cases k with
  | diag j =>
    obtain ⟨hj,hbound⟩ := hk
    have raw : Raw n (j,j) := ⟨by omega,hbound,hbound,by omega,by omega⟩
    simpa [after,units,raw,keyOf,NextCarry] using ht
  | finishChain _ => exact ht
  | skew _ _ => exact ⟨hs,ht⟩

theorem motion_of_bounds {n d} (D : StageKey → Choice n d) (L) (s t : State n d) (ok : ∀ k∈L,KeyOK n k)
    (links : Links (units D true) s.1.val L t.1.val) (bounds : ∀ k∈L,after (units D true) k≤2*n)
    (tot : ∀ i j, (t.2 i j).val=(s.2 i j).val+tally (cargo D L i) j) : Walk (Motion D) L s t := by
  induction L generalizing s with
  | nil =>
    refine Prod.ext (Fin.ext links) (funext fun i => funext fun j => Fin.ext ?_)
    simpa [cargo,tally] using (tot i j).symm
  | cons k ks ih =>
    have he (i j) : (t.2 i j).val=(s.2 i j).val + (tally (packet (blank k) (D k) i) j+tally (cargo D ks i) j) := by
      simpa only [cargo,List.flatMap_cons,tally_append,Pi.add_apply] using tot i j
    have fit (i j) : (s.2 i j).val+tally (packet (blank k) (D k) i) j < 2*n+1 := by
      have := he i j
      have := (t.2 i j).isLt
      omega
    let m : State n d := (⟨after (units D true) k,Nat.lt_succ_of_le (bounds k List.mem_cons_self)⟩,
      fun i j => ⟨_,fit i j⟩)
    refine ⟨m,⟨fun i j => rfl,next_of_positions D k (ok k List.mem_cons_self) s m links.1 rfl⟩,
      ih m (fun j hj => ok j (List.mem_cons_of_mem k hj)) links.2
        (fun j hj => bounds j (List.mem_cons_of_mem k hj)) ?_⟩
    intro i j
    simpa only [m,Nat.add_assoc] using he i j

theorem cargo_search {n d} (b : ChargeIx n → Sig (countLen n)) (q : Width n) (x : Input (countLen n))
    (s t : State n d) (hs : s.1.val=0) (ht : t.1.val=0) :
    Walk (fun k u v => liveEdge b q k u v x=true) (catalog n) s t ↔
      ∃ D : StageKey → Choice n d, (∀ k∈catalog n,after (units D true) k≤2*n) ∧
        (∀ i j, (t.2 i j).val=(s.2 i j).val+tally (cargo D (catalog n) i) j) ∧
        Asked b q x (imbalance (aggregate D)) := by
  rw [accepting_catalog b q x s t hs]
  apply exists_congr
  intro D
  have zeq : imbalance (aggregate D) = pulse (units D true) (units D false) := funext (signed_cargo D)
  rw [zeq]
  constructor
  · rintro ⟨motion,asks⟩
    obtain ⟨small,tot⟩ := motion_bounds D _ s t (fun _ => catalog_ok) motion
    exact ⟨small,tot,asks⟩
  · rintro ⟨small,tot,asks⟩
    exact ⟨motion_of_bounds D _ s t (fun _ => catalog_ok) (by rw [hs,ht]; exact link_catalog _ n) small tot,asks⟩

end PEqualNP.Outside.L_pcx_386.Allocation

namespace PEqualNP.Outside.L_pcx_386.Allocation

open PEqualNP.Outside.L_pcx_386.Core
open PEqualNP.Outside.L_pcx_386.Core.Compiler.Build

theorem tally_perm {L R : List Arc} (h : L.Perm R) : tally L=tally R := by
  induction h with
  | nil => rfl
  | cons a _ ih => obtain ⟨r,b,s⟩ := a; simp [tally,ih]
  | swap a b _ => obtain ⟨r,b',s⟩ := a; obtain ⟨v,u,f⟩ := b; simp [tally,add_left_comm]
  | trans _ _ i j => exact i.trans j

theorem dir_perm {L R : List Arc} (h : L.Perm R) (w) (s) :
    perDirection w s L=perDirection w s R := by simp only [dir_count,(List.perm_iff_count.mp h)]

theorem charge_perm {L R : List Arc} (h : L.Perm R) : imbalance L=imbalance R := by
  funext w
  rw [←pulse_inventory,←pulse_inventory]
  simp only [dir_perm h]

theorem flatten_fn {α β} (f : α → List β) (L : List α) : (L.map f).flatten=L.flatMap f := by
  induction L with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem merge_perm {d : ℕ} (L R : Fin d → List Arc) (h : ∀ i,(L i).Perm (R i)) :
    ((List.ofFn L).flatten).Perm ((Finset.univ.toList : List (Fin d)).flatMap R) := by
  have enumerated : (List.finRange d).Perm (Finset.univ.toList : List (Fin d)) :=
    (List.perm_ext_iff_of_nodup (List.nodup_finRange _) (Finset.nodup_toList _)).mpr (by simp)
  simpa only [List.ofFn_eq_map,flatten_fn] using enumerated.flatMap (fun i _ => h i)

theorem bag_length_at {d} (bags : Fin d → List Arc) (i : Fin d) : (bags i).length≤(List.ofFn bags).flatten.length := by
  rw [List.length_flatten,List.map_ofFn,List.sum_ofFn]
  exact Finset.single_le_sum (f:=fun i => (bags i).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

def planFor {n d} (bags : Fin d → List Arc) (small : (List.ofFn bags).flatten.length≤2*n) : StageKey → Choice n d :=
  fun k i =>
    let c (s : Bool) : Count n := ⟨perDirection (firstPair k) s (bags i),Nat.lt_succ_of_le
      ((by rw [dir_count]; exact List.count_le_length : perDirection (firstPair k) s (bags i) ≤ (bags i).length).trans
        ((bag_length_at bags i).trans small))⟩
    (c true,c false)

theorem of_bags {n d} (bags : Fin d → List Arc) (small : (List.ofFn bags).flatten.length≤2*n)
    (shaped : ∀ i a, a∈bags i → Raw n (a.1,a.2.1)) :
    ∃ D : StageKey → Choice n d, (∀ i, (cargo D (catalog n) i).Perm (bags i)) ∧
      (∀ k∈catalog n,after (units D true) k≤2*n) := by
  let D := planFor bags small
  have perm (i : Fin d) : (cargo D (catalog n) i).Perm (bags i) := by
    apply List.perm_iff_count.mpr
    rintro ⟨r,b,s⟩
    rw [←dir_count (r,b) s,←dir_count (r,b) s,dir_cargo D (catalog n) i (r,b) s (catalog_nodup n) (fun _ => catalog_ok)]
    by_cases raw : Raw n (r,b)
    · have eq : firstPair (keyOf (r,b))=(r,b) := by by_cases h : r=b <;> simp [keyOf,firstPair,h]
      have mem := raw_key_mem raw
      cases s <;> simp [raw,mem,D,planFor,weight,eq]
    · have miss (a : Arc) (ha : a∈bags i) : (r,b)≠(a.1,a.2.1) := fun eq => raw (eq ▸ shaped i a ha)
      simp [raw,perDirection_zero _ _ _ miss]
  have total : (aggregate D).Perm (List.ofFn bags).flatten := by
    simpa only [aggregate,List.ofFn_eq_map,flatten_fn] using
      (List.Perm.refl (List.finRange d)).flatMap (fun i _ => perm i)
  refine ⟨D,perm,?_⟩
  intro k _
  cases k with
  | diag j =>
    change units D true (j,j)≤2*n
    rw [←dir_aggregate,dir_count]
    exact List.count_le_length.trans (total.length_eq ▸ small)
  | finishChain _ => exact Nat.zero_le _
  | skew _ _ => exact Nat.zero_le _

def ordinalCount {n d} (k : StageKey) (c : Choice n d) (i : Fin d) (s : Bool) : ℕ :=
  match k with
  | .finishChain _ => 0
  | _ => weight c i s

noncomputable def receiptVal {n d} (k : StageKey) (s t : State n d) (i : Fin d) (f : Bool) :=
  perDirection (firstPair k) f (marking (blank k) s t i)

theorem receipt_move {n d} (k : StageKey) (s t : State n d) {c : Choice n d} (hm : Moves (blank k) s t c)
    (i : Fin d) (f : Bool) : receiptVal k s t i f = ordinalCount k c i f := by
  rw [receiptVal,marking_correct _ _ _ hm,dir_packet]
  cases k <;> simp [primary,firstPair,ordinalCount]

theorem receipt_small {n d} (k : StageKey) (c : Choice n d) (i : Fin d) (f : Bool) :
    ordinalCount k c i f ≤ 2*n := by
  cases k <;> cases f <;> simp only [ordinalCount,weight,Bool.false_eq_true,ite_true,ite_false] <;>
    first | exact Nat.zero_le _ | exact Nat.le_of_lt_succ (c i).1.isLt | exact Nat.le_of_lt_succ (c i).2.isLt

end PEqualNP.Outside.L_pcx_386.Allocation

namespace PEqualNP.Outside.L_pcx_386.Allocation

open PEqualNP.Outside.L_pcx_386.Core
open PEqualNP.Outside.L_pcx_386.Core.Compiler.Build

noncomputable def stateIso (n d : ℕ) := Fintype.equivFin (State n d)

abbrev Address (n d : ℕ) := Fin (catalog n).length × Fin d × Bool × Fin (2*n)

def keyAt (n k : ℕ) := (catalog n).getD k (.finishChain 0)

theorem key_at {n h} (hh : h<(catalog n).length) : keyAt n h=(catalog n)[h] := List.getD_eq_getElem _ _ hh

noncomputable def startNode {n d} (s : State n d) (i : Fin (Fintype.card (State n d))) : Sig (countLen n) :=
  fun _ => decide ((stateIso n d).symm i=s)

noncomputable def wireEdge {n d} (b : ChargeIx n → Sig (countLen n)) (q : Width n)
    (h : ℕ) (u v : Fin (Fintype.card (State n d))) : Sig (countLen n) :=
  liveEdge b q (keyAt n h) ((stateIso n d).symm u) ((stateIso n d).symm v)

noncomputable def wireLabels (n d h : ℕ) (u v : Fin (Fintype.card (State n d))) (w : Address n d) : Sig (countLen n) :=
  fun _ => decide (w.1.val=h ∧ w.2.2.2.val < receiptVal (keyAt n h) ((stateIso n d).symm u) ((stateIso n d).symm v) w.2.1 w.2.2.1)

def indexedCount {n d} (D : StageKey → Choice n d) (j : Fin (catalog n).length) :=
  ordinalCount ((catalog n).get j) (D ((catalog n).get j))

def answers {n d} (D : StageKey → Choice n d) (h : ℕ) (w : Address n d) :=
  decide (w.1.val<h ∧ w.2.2.2.val < indexedCount D w.1 w.2.1 w.2.2.1)

theorem walk_cat {K V : Type} (e : K → V → V → Prop) (L R) (u v : V) :
    Walk e (L++R) u v ↔ ∃ m, Walk e L u m ∧ Walk e R m v := by
  induction L generalizing u with
  | nil => simp [Walk]
  | cons k ks ih =>
    constructor
    · rintro ⟨j,hj,tail⟩
      obtain ⟨m,pre,suf⟩ := (ih j).mp tail
      exact ⟨m,⟨j,hj,pre⟩,suf⟩
    · rintro ⟨m,⟨j,hj,pre⟩,suf⟩
      exact ⟨j,hj,(ih j).mpr ⟨m,pre,suf⟩⟩

theorem walk_snoc {K V : Type} (e : K → V → V → Prop) (L k) (u v : V) :
    Walk e (L++[k]) u v ↔ ∃ m, Walk e L u m ∧ e k m v := by simp [walk_cat,Walk]

theorem mem_prefix {α} (L : List α) (j : Fin L.length) {h : ℕ} (hj : j.val<h) : L.get j ∈ L.take h := by
  have lt : j.val<(L.take h).length := by simp [List.length_take,hj,j.isLt]
  simpa only [List.get_eq_getElem,List.getElem_take] using List.getElem_mem lt

theorem key_new {n h} (hh : h<(catalog n).length) : keyAt n h ∉ (catalog n).take h := by
  have hn := (catalog_nodup n).sublist (List.take_sublist (h+1) (catalog n))
  rw [List.take_succ_eq_append_getElem hh] at hn
  intro hm
  rw [key_at hh] at hm
  exact (List.pairwise_append.mp hn).2.2 _ hm _ List.mem_cons_self rfl

theorem extend_answers {n d h} (hh : h<(catalog n).length) (D E : StageKey → Choice n d)
    (same : ∀ k∈(catalog n).take h,E k=D k) (u v : State n d)
    (hm : Moves (blank (keyAt n h)) u v (E (keyAt n h))) (x : Input (countLen n)) (w : Address n d) :
    answers E (h+1) w =
      (answers D h w || wireLabels n d h (stateIso n d u) (stateIso n d v) w x) := by
  obtain ⟨j,i,f,o⟩ := w
  simp only [answers,wireLabels,Equiv.symm_apply_apply,receipt_move _ _ _ hm]
  by_cases lt : j.val<h
  · have ne := Nat.ne_of_lt lt
    have eq := same _ (mem_prefix _ j lt)
    rw [List.get_eq_getElem] at eq
    simp [lt,ne,Nat.lt_succ_of_lt lt,indexedCount,eq]
  · by_cases eq : j.val=h
    · simp [eq,indexedCount,key_at hh]
    · have ge : ¬j.val<h+1 := by omega
      simp [lt,ge,eq]

def firing {n d} (b : ChargeIx n → Sig (countLen n)) (q : Width n) (x : Input (countLen n))
    (D : StageKey → Choice n d) (k) (u v : State n d) := Motion D k u v ∧ Tests b q x k u (D k)

theorem path_prefix {n d} (b : ChargeIx n → Sig (countLen n)) (q : Width n) (x : Input (countLen n))
    (origin : State n d) (h : ℕ) (hh : h≤(catalog n).length) (t : State n d) (bits : Address n d → Bool) :
    TracePath (startNode origin) (wireEdge b q) (wireLabels n d) x h (stateIso n d t) bits ↔
      ∃ D : StageKey → Choice n d, Walk (firing b q x D) ((catalog n).take h) origin t ∧ bits=answers D h := by
  classical
  induction h generalizing t bits with
  | zero =>
    simp only [TracePath,startNode,Equiv.symm_apply_apply,decide_eq_true_eq,List.take_zero,Walk]
    constructor
    · rintro ⟨rfl,z⟩
      exact ⟨fun _ _ => (0,0),rfl,funext fun w => by simpa [answers] using z w⟩
    · rintro ⟨_,rfl,rfl⟩; exact ⟨rfl,by simp [answers]⟩
  | succ h ih =>
    have lim : h<(catalog n).length := by omega
    let k := keyAt n h
    have hk : k ∈ catalog n := by rw [show k=(catalog n)[h] from key_at lim]; exact List.getElem_mem _
    have pre : (catalog n).take (h+1) = (catalog n).take h ++ [k] := by
      simpa only [k,key_at lim] using List.take_succ_eq_append_getElem lim
    constructor
    · rintro ⟨j,old,prior,edge,mark⟩
      let u := (stateIso n d).symm j
      have uj : stateIso n d u=j := (stateIso n d).apply_symm_apply _
      rw [←uj] at prior edge mark
      obtain ⟨D,path,hb⟩ := (ih lim.le u old).mp prior
      have on : liveEdge b q k u t x=true := by simpa only [wireEdge,Equiv.symm_apply_apply] using edge
      obtain ⟨c,moves,carry,check⟩ := (stage_exact b q k (catalog_ok hk) u t x).mp on
      let E := Function.update D k c
      have self : E k=c := Function.update_self ..
      have fresh : k∉(catalog n).take h := key_new lim
      have same (a : StageKey) (ha : a∈(catalog n).take h) : E a=D a :=
        Function.update_of_ne (show a≠k from fun eq => fresh (eq ▸ ha)) ..
      have path' : Walk (firing b q x E) ((catalog n).take h) origin u := by
        apply (walk_local _ _ _ ?_).mp path
        intro a ha r z
        simp only [firing,Motion,same a ha]
      have hm : Moves (blank k) u t (E k) := self ▸ moves
      refine ⟨E,?_,funext fun w => ?_⟩
      · rw [pre,walk_snoc]
        exact ⟨u,path',by simpa only [firing,Motion,Tests,self] using (show (Moves (blank k) u t c ∧ NextCarry k u t c) ∧ Tests b q x k u c from ⟨⟨moves,carry⟩,check⟩)⟩
      · rw [mark,hb,extend_answers lim D E same u t hm x w]
    · rintro ⟨D,path,rfl⟩
      rw [pre,walk_snoc] at path
      obtain ⟨u,prior,⟨⟨moves,carry⟩,check⟩⟩ := path
      have on := (stage_exact b q k (catalog_ok hk) u t x).mpr ⟨D k,moves,carry,check⟩
      exact ⟨stateIso n d u,answers D h,(ih lim.le u _).mpr ⟨D,prior,rfl⟩,
        by simpa only [wireEdge,Equiv.symm_apply_apply] using on,
        extend_answers lim D D (fun _ _ => rfl) u t moves x⟩

theorem trace_cargo {n d} (b : ChargeIx n → Sig (countLen n)) (q : Width n) (x : Input (countLen n))
    (s t : State n d) (hs : s.1.val=0) (ht : t.1.val=0) (bits : Address n d → Bool) :
    TracePath (startNode s) (wireEdge b q) (wireLabels n d) x (catalog n).length (stateIso n d t) bits ↔
      ∃ D : StageKey → Choice n d, (∀ k∈catalog n,after (units D true) k≤2*n) ∧
        (∀ i j, (t.2 i j).val=(s.2 i j).val+tally (cargo D (catalog n) i) j) ∧
        Asked b q x (imbalance (aggregate D)) ∧ ∀ j i f o, bits (j,i,f,o)=decide (o.val < indexedCount D j i f) := by
  rw [path_prefix b q x s _ le_rfl,List.take_length]
  apply exists_congr
  intro D
  have spec := fixed_bank b q x D (catalog n) s t 0 (fun _ => catalog_ok) (by rw [hs]; exact link_catalog _ n)
  have mass : imbalance (aggregate D)=pulse (units D true) (units D false) := funext (signed_cargo D)
  change (Walk (fun k u v => Motion D k u v ∧ Tests b q x k u (D k)) (catalog n) s t ∧ _) ↔ _
  rw [spec,mass]
  constructor
  · rintro ⟨⟨move,asks⟩,rfl⟩
    obtain ⟨low,tot⟩ := motion_bounds D _ s t (fun _ => catalog_ok) move
    exact ⟨low,tot,asks,fun j i f o => by simp [answers,j.isLt]⟩
  · rintro ⟨low,tot,asks,receipt⟩
    refine ⟨⟨motion_of_bounds D _ s t (fun _ => catalog_ok) (by rw [hs,ht]; exact link_catalog _ n) low tot,asks⟩,?_⟩
    funext w
    obtain ⟨j,i,f,o⟩ := w
    simpa [answers,j.isLt] using receipt j i f o

theorem constant_signal {N : ℕ} {A : Set (Sig N)} (h0 : (fun _ => false)∈A) (h1 : (fun _ => true)∈A)
    (v : Bool) : (fun _ => v)∈A := by cases v <;> assumption

theorem start_given {n d} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (s : State n d) (i) : startNode s i ∈ layoutBasis a b :=
  constant_signal (Or.inl (Or.inr (Or.inl rfl))) (Or.inl (Or.inr (Or.inr rfl))) _

theorem label_given {n d} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (h) (u v) (w) : wireLabels n d h u v w ∈ layoutBasis a b :=
  constant_signal (Or.inl (Or.inr (Or.inl rfl))) (Or.inl (Or.inr (Or.inr rfl))) _

theorem edge_given {n d} (b : ChargeIx n → Sig (countLen n)) (q : Width n) (h) (hh : h<(catalog n).length)
    (u v : Fin (Fintype.card (State n d))) : wireEdge b q h u v ∈
      Set.range (fun ix : Fin (catalog n).length × State n d × State n d =>
        liveEdge b q ((catalog n).get ix.1) ix.2.1 ix.2.2) := by
  refine ⟨(⟨h,hh⟩,(stateIso n d).symm u,(stateIso n d).symm v),?_⟩
  simp [wireEdge,key_at hh]

end PEqualNP.Outside.L_pcx_386.Allocation

namespace PEqualNP.Outside.L_pcx_386.PacketBank

open PEqualNP.Outside.L_pcx_386.Core
open PEqualNP.Outside.L_pcx_386.Core.Compiler.Build
open PEqualNP.Outside.L_pcx_386.Allocation
open PEqualNP.Outside.L_pcx_386.Assembly
open PEqualNP.Outside.L_pcx_386.PhysicalBank
open PEqualNP.Outside.L_pcx_386_aux

def dims (n : ℕ) (j : Fin (catalog n).length) := firstPair ((catalog n).get j)

def selectedColor (c : Fin 3) (a : Arc) := decide (Placement.category (a.1,a.2.1)=c)

def group {n d} (D : StageKey → Choice n d) (i : Fin d) (c : Fin 3) :=
  (Placement.emitted (dims n) (indexedCount D) i c).map (Placement.description (dims n))

theorem pack_filter {n d} (k : StageKey) (v : Choice n d) (i : Fin d) (c : Fin 3) :
    (packet (blank k) v i).filter (selectedColor c) =
      if Placement.category (firstPair k)=c then
        bundle (firstPair k).1 (firstPair k).2 (ordinalCount k v i true) (ordinalCount k v i false) else [] := by
  cases k <;>
    simp only [packet,blank,firstPair,ordinalCount,weight,bundle,List.filter_append,List.filter_replicate,
      selectedColor,decide_eq_true_eq,Bool.false_eq_true,ite_true,ite_false,List.filter_nil,List.replicate_zero,List.nil_append] <;>
    split_ifs <;> simp_all

theorem group_filter {n d} (D : StageKey → Choice n d) (i : Fin d) (c : Fin 3) :
    group D i c = (cargo D (catalog n) i).filter (selectedColor c) := by
  let g := (catalog n).get
  have listed : (List.finRange (catalog n).length).map g=catalog n := by
    rw [←List.ofFn_eq_map]; exact List.ofFn_get _
  simp only [group,Placement.emitted,List.map_flatMap,cargo,List.filter_flatMap]
  conv_rhs => rw [←listed,List.flatMap_map]
  apply List.flatMap_congr
  intro j _
  change _=(packet (blank (g j)) (D (g j)) i).filter (selectedColor c)
  rw [pack_filter]
  by_cases h : Placement.category (dims n j)=c
  · have hh : Placement.category (firstPair (g j))=c := h
    simp only [h,hh,ite_true,List.map_append,List.map_replicate]
    rfl
  · have hh : ¬Placement.category (firstPair (g j))=c := h
    simp [h,hh]

def allGroups {n d} (D : StageKey → Choice n d) (i : Fin d) :=
  group D i 0 ++ group D i 1 ++ group D i 2

theorem group_perm {n d} (D : StageKey → Choice n d) (i : Fin d) :
    (allGroups D i).Perm (cargo D (catalog n) i) := by
  simp only [allGroups,group_filter]
  let L := cargo D (catalog n) i
  apply List.perm_iff_count.mpr
  intro a
  have count (c) : (L.filter (selectedColor c)).count a = if Placement.category (a.1,a.2.1)=c then L.count a else 0 := by
    by_cases h : Placement.category (a.1,a.2.1)=c
    · simpa only [h,ite_true] using List.count_filter (p:=selectedColor c) (l:=L) (a:=a) (by simp [selectedColor,h])
    · have miss : a∉L.filter (selectedColor c) := by simp [selectedColor,h]
      simp [h,List.count_eq_zero.mpr miss]
  simp only [List.count_append]
  change (L.filter _).count a + (L.filter _).count a + (L.filter _).count a = L.count a
  simp only [count]
  generalize Placement.category (a.1,a.2.1)=col
  fin_cases col <;> simp

theorem member_raw {n d} (D : StageKey → Choice n d) (i : Fin d) {a} (h : a∈cargo D (catalog n) i) :
    Raw n (a.1,a.2.1) := by
  by_contra miss
  obtain ⟨r,b,f⟩ := a
  have yes := List.count_pos_iff.mpr h
  rw [←dir_count (r,b) f,dir_cargo D (catalog n) i _ _ (catalog_nodup n) (fun _ => catalog_ok)] at yes
  simp [miss] at yes

theorem group_shape {n d} (D : StageKey → Choice n d) (i : Fin d) :
    (∀ a∈group D i 0,a.1=a.2.1) ∧ (∀ a∈group D i 1,a.1=a.2.1+1) ∧
      (∀ a∈group D i 2,a.2.1=a.1+1) ∧ ∀ a∈allGroups D i,0<Placement.span a := by
  have classified (c) (a : Arc) (h : a∈group D i c) : Raw n (a.1,a.2.1) ∧ Placement.category (a.1,a.2.1)=c := by
    rw [group_filter] at h; obtain ⟨m,y⟩ := List.mem_filter.mp h
    exact ⟨member_raw D i m,of_decide_eq_true y⟩
  refine ⟨?_,?_,?_,fun a ha => (member_raw D i ((group_perm D i).mem_iff.mp ha)).1⟩ <;>
    intro a ha <;> obtain ⟨⟨_,_,_,hr,hb⟩,eq⟩ := classified _ a ha <;>
      dsimp [Placement.category] at eq hr hb <;> split_ifs at eq <;> omega

theorem tint_sum {L : List Arc} (z : ℤ) (h : ∀ a ∈ L, (a.1 : ℤ)-a.2.1=z) :
    (red L : ℤ)-blue L = z*L.length := by
  induction L with
  | nil => simp [red,blue]
  | cons a t ih =>
    have x := h a List.mem_cons_self
    have y := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp [red,blue] at y ⊢
    linarith

theorem split_length {n d} (D : StageKey → Choice n d) (i : Fin d) (t : State n d)
    (hc : ∀ j, (t.2 i j).val=tally (cargo D (catalog n) i) j) (eq : (t.2 i 0).val=(t.2 i 1).val) :
    (∀ c, (Placement.emitted (dims n) (indexedCount D) i c).length≤2*n) ∧
      (Placement.emitted (dims n) (indexedCount D) i 1).length=(Placement.emitted (dims n) (indexedCount D) i 2).length := by
  have gp := group_perm D i
  have tot (j : Fin 4) : (t.2 i j).val=tally (allGroups D i) j := (hc j).trans (congrFun (tally_perm gp).symm j)
  have rr := (tot 0).trans (tally_fields _).1
  have bb := (tot 1).trans (tally_fields _).2.1
  have ll := (tot 2).trans (tally_fields _).2.2.1
  have small := (t.2 i 2).isLt
  have lengths (c) : (Placement.emitted (dims n) (indexedCount D) i c).length=(group D i c).length := by simp [group]
  simp only [lengths]
  constructor
  · intro c
    simp only [allGroups,List.length_append] at ll
    rcases (show c=0 ∨ c=1 ∨ c=2 by fin_cases c <;> decide) with rfl|rfl|rfl <;> omega
  · obtain ⟨hd,hr,hb,_⟩ := group_shape D i
    have ez := tint_sum 0 (L:=group D i 0) (fun a ha => by rw [hd a ha]; simp)
    have er := tint_sum 1 (L:=group D i 1) (fun a ha => by rw [hr a ha]; push_cast; ring)
    have eb := tint_sum (-1) (L:=group D i 2) (fun a ha => by rw [hb a ha]; push_cast; ring)
    have whole : (red (allGroups D i) : ℤ)=blue (allGroups D i) := by exact_mod_cast rr.symm.trans (eq.trans bb)
    simp only [allGroups,red,blue,List.map_append,List.sum_append,Nat.cast_add] at whole ez er eb
    exact_mod_cast (show ((group D i 1).length : ℤ)=(group D i 2).length by linarith)

theorem all_fields {n d} (D : StageKey → Choice n d) (t : State n d)
    (c : ∀ i j, (t.2 i j).val=tally (cargo D (catalog n) i) j) :
    (∀ i j, (t.2 i j).val=tally (allGroups D i) j) ∧ imbalance (aggregate D)=imbalance (catRows (allGroups D)) := by
  refine ⟨fun i j => (c i j).trans (congrFun (tally_perm (group_perm D i)).symm j),?_⟩
  exact charge_perm (merge_perm _ _ (fun i => (group_perm D i).symm))

def fields {n d} (load : Address n d → Sig (countLen n)) (mask : Fin d → Bool) (u : Fin d × Bool × Fin (2*n+1)) :=
  Placement.pinField (Placement.maskedPin (2*n) (Placement.description (dims n)) (Placement.bankOf (dims n) load u.1)
    (fun _ => mask u.1) u.2.2.val) u.2.1

theorem selected_fit {n d} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (σ : Equiv.Perm (Fin n)) (x : Input (countLen n)) (g : Scatter.Guess n d)
    (q : Width n) (t : State n d) (mask : Fin d → Bool) (term : Terminal g q t mask)
    (hp : (List.ofFn x).take (2+n*n)=permPrefix σ) (coh : Scatter.Coherent g)
    (pass : Scatter.guardSig (inverseMatrix n) g x=true) (width : a q x=true)
    (tail : zeroMask (fun m => Scheduled n m.val) b q x=true) (load : Address n d → Sig (countLen n))
    (D : StageKey → Choice n d) (tallies : ∀ i j, (t.2 i j).val=tally (cargo D (catalog n) i) j)
    (asked : Asked b q x (imbalance (aggregate D)))
    (bits : ∀ j i f o, load (j,i,f,o) x=decide (o.val < indexedCount D j i f)) :
    let pins := fun z (v : Bool × Fin n) => Scatter.out (inverseMatrix n) (fanMarks g (fields load mask)) (z,v)
    fitsSignals a b x σ (readPins pins x) := by
  have base := all_fields D t tallies
  apply endpoint_sound a b σ x g q t mask term hp coh pass (fun i => group D i 0) (fun i => group D i 1)
    (fun i => group D i 2) (fields load mask) (fun i => (group_shape D i).1) (fun i => (group_shape D i).2.1)
    (fun i => (group_shape D i).2.2.1) (fun i => (group_shape D i).2.2.2) base.1 _ width tail
    (by change Asked b q x (imbalance (catRows (allGroups D))); rw [←base.2]; exact asked)
  intro i k
  have H := split_length D i t (tallies i) ((term.2.1 i).1.trans (term.2.1 i).2.1.symm)
  unfold fields
  exact (Placement.read_field _ _).trans (receipt_word (dims n) load (fun j _ => mask j) x (indexedCount D)
    (fun j a f => receipt_small _ _ a f) bits i H.1 H.2 k.val)

end PEqualNP.Outside.L_pcx_386.PacketBank

namespace PEqualNP.Outside.L_pcx_386.FinalJoin

open PEqualNP.Outside.L_pcx_386_aux
open PEqualNP.Outside.L_pcx_386.Core PEqualNP.Outside.L_pcx_386.Core.Compiler.Build
open PEqualNP.Outside.L_pcx_386.Allocation
open PEqualNP.Outside.L_pcx_386.Assembly PEqualNP.Outside.L_pcx_386.PhysicalBank

abbrev Blocks (n d : ℕ) := Scatter.Guess n d × Width n × State n d × (Fin d → Bool)
abbrev PinCode (n : ℕ) := Bool × (Bool × Fin n)
def Sealed {n d : ℕ} (u : Blocks n d) : Prop := Scatter.Coherent u.1 ∧ Terminal u.1 u.2.1 u.2.2.1 u.2.2.2
def pinsOf {n : ℕ} (C : TraceCell (countLen n) (PinCode n)) :=
  readPins (fun z v => C.bits (z,v))

noncomputable def guarded {n d} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (u : Blocks n d) (cell : TraceCell (countLen n) (PinCode n)) : TraceCell (countLen n) (PinCode n) :=
  ⟨fun x => [Scatter.guardSig (inverseMatrix n) u.1,a u.2.1,
       zeroMask (fun m => Scheduled n m.val) b u.2.1,cell.ok].all (fun f => f x),cell.bits⟩

theorem guarded_yes {n d} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (u : Blocks n d) (cell : TraceCell (countLen n) (PinCode n)) (x : Input (countLen n)) :
    (guarded a b u cell).ok x=true ↔ Scatter.guardSig (inverseMatrix n) u.1 x=true ∧ a u.2.1 x=true ∧
      zeroMask (fun m => Scheduled n m.val) b u.2.1 x=true ∧ cell.ok x=true := by simp [guarded]

theorem guarded_build {n d k} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (u : Blocks n d) (cell : TraceCell (countLen n) (PinCode n)) (h : Build (layoutBasis a b) cell.outputs k) :
    Build (layoutBasis a b) (guarded a b u cell).outputs (k+(Scatter.guessCost n d+(radius n+1))+4) := by
  let A := layoutBasis a b
  let g := Scatter.guardSig (inverseMatrix n) u.1
  let z := zeroMask (fun m => Scheduled n m.val) b u.2.1
  have zero : (fun _ => false)∈A := Or.inl (Or.inr (Or.inl rfl))
  have one : (fun _ => true)∈A := Or.inl (Or.inr (Or.inr rfl))
  have G : Build A {g} (Scatter.guessCost n d) :=
    relax (Scatter.build_guesses (inverseMatrix n) d (matrix_given a b) zero one) le_rfl (Set.singleton_subset_iff.mpr ⟨_,rfl⟩) le_rfl
  have Z : Build A {z} (radius n+1) := zero_mask_build _ a b u.2.1
  let Out := cell.outputs ∪ ({g} ∪ {z})
  have hs : Build A Out (k+(Scatter.guessCost n d+(radius n+1))) := bothG h (bothG G Z)
  let E := A∪Out
  have bits (w : PinCode n) : cell.bits w∈E := Or.inr (Or.inl (Or.inr ⟨w,rfl⟩))
  have ga : g∈E := Or.inr (Or.inr (Or.inl rfl))
  have za : z∈E := Or.inr (Or.inr (Or.inr rfl))
  have qa : a u.2.1∈E := Or.inl (Or.inr (Or.inl ⟨_,rfl⟩))
  have ca : cell.ok∈E := Or.inr (Or.inl (Or.inl rfl))
  have h4 : Build E {(guarded a b u cell).ok} 4 := everyG [g,a u.2.1,z,cell.ok]
    (fun f hf => by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hf
      rcases hf with rfl|rfl|rfl|rfl <;> assumption) (Or.inl one)
  apply relax (seq hs h4) le_rfl _ le_rfl
  rintro f (hh|⟨w,rfl⟩)
  · exact Or.inr hh
  · exact Or.inl (Or.inl (Or.inr ⟨w,rfl⟩))

def dExp (n d e : ℕ) := (n+2)^(e*(d+1))

theorem dBound_add {n d a b i j : ℕ} (h : a≤dExp n d i) (g : b≤dExp n d j) :
    a+b ≤ dExp n d (i+j+1) := by
  let X:=n+2
  have low : 2≤X := by unfold X;omega
  have L (m v : ℕ) (p : m≤dExp n d v) (q : v ≤ i+j) : m≤dExp n d (i+j) :=
    p.trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ q))
  have f := L _ i h (by omega)
  have g' := L _ j g (by omega)
  have v := Nat.mul_le_mul_left (dExp n d (i+j)) low
  calc a+b ≤ dExp n d (i+j)+dExp n d (i+j) := Nat.add_le_add f g'
       _ ≤ dExp n d (i+j)*X := (Nat.mul_two _).symm.le.trans v
       _ = X^((i+j)*(d+1)+1) := (pow_succ X _).symm
       _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

theorem dBound_mul {n d a b i j : ℕ} (h : a≤dExp n d i) (g : b≤dExp n d j) :
    a*b ≤ dExp n d (i+j) := by
  unfold dExp at *
  rw [Nat.add_mul,pow_add]
  exact Nat.mul_le_mul h g

theorem dBound_poly {n d a k : ℕ} (h : a≤(n+2)^k) : a≤dExp n d k :=
  h.trans (Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_right _ (by omega)))

theorem blocks_size (n d : ℕ) : Fintype.card (Blocks n d) ≤ dExp n d 13 := by
  let X:=n+2
  have g : (n*n)^d ≤ dExp n d 2 := by
    change (n*n)^d ≤ X^(2*(d+1))
    calc _ ≤ (X^2)^d := Nat.pow_le_pow_left (by dsimp [X];nlinarith) _
         _ = X^(2*d) := (pow_mul ..).symm
         _ ≤ _ := Nat.pow_le_pow_right (by dsimp [X];omega) (by omega)
  have w : 2*n+1≤dExp n d 2 := dBound_poly (by nlinarith)
  have s := state_budget n d
  have m : 2^d ≤ dExp n d 1 := by
    calc 2^d ≤ (n+2)^d := Nat.pow_le_pow_left (by omega) _
         _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  simpa only [Blocks,Scatter.Guess,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Width] using
    dBound_mul g (dBound_mul w (dBound_mul (show Fintype.card (State n d) ≤ dExp n d 8 from s) m))

theorem select_cost (n d : ℕ) : 1+Fintype.card (PinCode n)*4 ≤ dExp n d 5 := by
  apply dBound_poly
  simp [PinCode]
  ring_nf
  omega

noncomputable def sealedCell {n d} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (raw : Blocks n d → TraceCell (countLen n) (PinCode n)) (u : Blocks n d) : TraceCell (countLen n) (PinCode n) := by
  classical exact if Sealed u then guarded a b u (raw u) else TraceCell.blank

noncomputable def elected {n d} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (raw : Blocks n d → TraceCell (countLen n) (PinCode n)) :=
  TraceCell.select (sealedCell a b raw) Finset.univ.toList

theorem elected_ok {n d} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (raw : Blocks n d → TraceCell (countLen n) (PinCode n)) (x : Input (countLen n)) :
    (elected a b raw).ok x=true ↔ ∃ u, Sealed u ∧ Scatter.guardSig (inverseMatrix n) u.1 x=true ∧ a u.2.1 x=true ∧
      zeroMask (fun m => Scheduled n m.val) b u.2.1 x=true ∧ (raw u).ok x=true := by
  classical
  rw [elected,TraceCell.select_ok]
  simp only [Finset.mem_toList,Finset.mem_univ,true_and]
  apply exists_congr
  intro u
  by_cases h : Sealed u <;> simp [sealedCell,h,guarded_yes,TraceCell.blank]

theorem elected_wires {n d} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (raw : Blocks n d → TraceCell (countLen n) (PinCode n)) (x : Input (countLen n))
    (ok : (elected a b raw).ok x=true) :
    ∃ u, Sealed u ∧ Scatter.guardSig (inverseMatrix n) u.1 x=true ∧ a u.2.1 x=true ∧
      zeroMask (fun m => Scheduled n m.val) b u.2.1 x=true ∧ (raw u).ok x=true ∧
      pinsOf (elected a b raw) x = pinsOf (raw u) x := by
  classical
  obtain ⟨u,_,yes,wire⟩ := TraceCell.select_data (sealedCell a b raw) Finset.univ.toList x ok
  by_cases h : Sealed u
  · rw [sealedCell,if_pos h] at yes
    obtain ⟨g,q,t,r⟩ := (guarded_yes ..).mp yes
    refine ⟨u,h,g,q,t,r,?_⟩
    have ws (v) : (elected a b raw).bits v x=(raw u).bits v x := by
      change (TraceCell.select (sealedCell a b raw) Finset.univ.toList).bits v x = _
      exact (wire v).trans (by rw [sealedCell,if_pos h];rfl)
    funext v
    simp only [pinsOf,readPins,ws]
  · simp [sealedCell,h,TraceCell.blank] at yes

theorem elected_build {n d E} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (raw : Blocks n d → TraceCell (countLen n) (PinCode n))
    (hb : ∀ u, Sealed u → Build (layoutBasis a b) (raw u).outputs (dExp n d E)) :
    Build (layoutBasis a b) (elected a b raw).outputs (dExp n d (E+52)) := by
  classical
  let A:=layoutBasis a b
  let f:=sealedCell a b raw
  have zero : (fun _ => false)∈A := Or.inl (Or.inr (Or.inl rfl))
  let K := dExp n d E+(Scatter.guessCost n d+(radius n+1))+4
  have hk : K ≤ dExp n d (E+15) := by
    have z : radius n+1 ≤ dExp n d 4 := dBound_poly (by unfold radius stride;ring_nf;omega)
    have g : Scatter.guessCost n d ≤ dExp n d 6 := Scatter.guessCost_bound n d
    have four : 4 ≤ dExp n d 2 := dBound_poly (Nat.pow_le_pow_left (by omega : 2≤n+2) 2)
    have x := dBound_add (a:=dExp n d E) (i:=E) le_rfl (dBound_add g z)
    have y := dBound_add x four
    simpa only [K,Nat.add_assoc] using y
  have blocks (u : Blocks n d) : Build A (f u).outputs K := by
    by_cases h : Sealed u
    · simpa only [f,sealedCell,if_pos h,K,A] using guarded_build a b u (raw u) (hb u h)
    · rw [show f u = TraceCell.blank from if_neg h]
      apply relax (idle (A:=A) (B:=(TraceCell.blank (ι:=PinCode n)).outputs) ?_) le_rfl le_rfl (Nat.zero_le _)
      rintro s (rfl|⟨i,rfl⟩) <;> exact zero
  let F:=familyOut Finset.univ (fun u => (f u).outputs)
  have hAll := familyG (fun u => (f u).outputs) K blocks
  have hPick := TraceCell.compile_select (A:=A ∪ F) f Finset.univ.toList (Or.inl zero)
    (fun i _ s hs => Or.inr (family_mem (i:=i) hs))
  apply relax (thenG hAll hPick) le_rfl le_rfl
  rw [Finset.length_toList,Finset.card_univ]
  have hCost := dBound_mul (blocks_size n d) hk
  have sel := dBound_mul (blocks_size n d) (select_cost n d)
  apply (dBound_add hCost sel).trans
  unfold dExp
  exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by omega))

def zeroState (n d : ℕ) : State n d := (0,fun _ _ => 0)
noncomputable def lastCell {n d} (b : ChargeIx n → Sig (countLen n)) (q : Width n) (t : State n d) :
    TraceCell (countLen n) (Address n d) :=
  walkCells (startNode (zeroState n d)) (wireEdge b q) (wireLabels n d) (catalog n).length (stateIso n d t)
noncomputable def fields {n d} (b : ChargeIx n → Sig (countLen n)) (q : Width n) (t : State n d) (mask : Fin d → Bool)
    (u : Fin d × Bool × Fin (2*n+1)) : Sig (countLen n) :=
  Placement.pinField (Placement.maskedPin (2*n) (Placement.description (PacketBank.dims n))
    (Placement.bankOf (PacketBank.dims n) (lastCell b q t).bits u.1) (fun _ => mask u.1) u.2.2.val) u.2.1
noncomputable def rawBlock {n d} (b : ChargeIx n → Sig (countLen n)) (u : Blocks n d) :
    TraceCell (countLen n) (PinCode n) :=
  ⟨(lastCell b u.2.1 u.2.2.1).ok,
    fun w => Scatter.out (inverseMatrix n) (fanMarks u.1 (fields b u.2.1 u.2.2.1 u.2.2.2)) w⟩

theorem trace_bound {n d} (hd : d≤n) :
    (catalog n).length*traceCost (Fintype.card (State n d)) ((catalog n).length*(d*(2*(2*n)))) ≤ dExp n d 34 := by
  let S := (catalog n).length
  let M := Fintype.card (State n d)
  let B := n+2
  let W := S*(d*(2*(2*n)))
  have hs : S≤dExp n d 4 := dBound_poly (catalog_length n)
  have hm : M≤dExp n d 8 := state_budget n d
  have hD : d≤dExp n d 1 := dBound_poly (by simp;omega)
  have hN : 2*(2*n) ≤ dExp n d 2 := dBound_poly (by nlinarith)
  have hW : W≤dExp n d 7 := dBound_mul hs (dBound_mul hD hN)
  have two : 2≤dExp n d 1 := dBound_poly (by simp)
  have five : 5≤dExp n d 3 := dBound_poly (by ring_nf;omega)
  have ex : S*traceCost M W=S*(M*(M*(2+5*W))) := by unfold traceCost;ring
  change S*traceCost M W ≤ _
  rw [ex]
  have h := dBound_mul hs (dBound_mul hm (dBound_mul hm (dBound_add two (dBound_mul five hW))))
  exact h.trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by decide)))

theorem raw_build {n d} (hd : d≤n) (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (u : Blocks n d) : Build (layoutBasis a b) (rawBlock b u).outputs (dExp n d 150) := by
  obtain ⟨g,q,t,mask⟩ := u
  let A := layoutBasis a b
  let E := Set.range (fun ix : Fin (catalog n).length × State n d × State n d =>
    liveEdge b q ((catalog n).get ix.1) ix.2.1 ix.2.2)
  let V:= A∪E
  have zero : (fun _ => false)∈A := Or.inl (Or.inr (Or.inl rfl))
  have one : (fun _ => true)∈A := Or.inl (Or.inr (Or.inr rfl))
  have he : Build A E (dExp n d 20) := live_edge_bank a b q
  have place := (Placement.postcompose_walk (B:=2*n) (T:=2*n)
    (startNode (zeroState n d)) (wireEdge b q) (wireLabels n d) (catalog n).length (stateIso n d t)
    (PacketBank.dims n) (fun i _ => mask i) (A:=V) (Or.inl zero) (Or.inl one)
    (fun i => Or.inl (constant_signal zero one (mask i))) (fun i => Or.inl (start_given a b _ i))
    (fun k hk i j => Or.inr (edge_given b q _ hk i j)) (fun k _ i j w => Or.inl (label_given a b k i j w))).1
  let S:=(catalog n).length
  let K := S*traceCost (Fintype.card (State n d)) (S*(d*(2*(2*n)))) + Placement.shipmentCost S d (2*n) (2*n) (2*n)
  have built : Build V ({(lastCell b q t).ok} ∪ Set.range (fields b q t mask)) K := place
  have out := fan_build (inverseMatrix n) g (fields b q t mask) (lastCell b q t).ok built
    (fun r t => Or.inl (matrix_given a b r t)) (Or.inl zero) (Or.inl one)
  change Build A (rawBlock b (g,q,t,mask)).outputs _
  apply relax (thenG he out) le_rfl le_rfl
  have P : Placement.shipmentCost S d (2*n) (2*n) (2*n) ≤ dExp n d 84 :=
    dBound_poly (shipment_bound (catalog_length n) hd)
  have F : Scatter.cost n ≤ dExp n d 6 := dBound_poly (Scatter.cost_bound n)
  have all := dBound_add (a:=dExp n d 20) (i:=20) le_rfl (dBound_add (dBound_add (trace_bound hd) P) F)
  exact all.trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by decide)))

theorem exact_source {n d} (b : ChargeIx n → Sig (countLen n)) (q : Width n) (x : Input (countLen n)) (t : State n d)
    (ht : t.1.val=0) (bits : Address n d → Bool) :
    TracePath (startNode (zeroState n d)) (wireEdge b q) (wireLabels n d) x (catalog n).length (stateIso n d t) bits ↔
      ∃ D : StageKey → Choice n d, (∀ k∈catalog n,after (units D true) k≤2*n) ∧
        (∀ i j, (t.2 i j).val=tally (cargo D (catalog n) i) j) ∧
        Asked b q x (imbalance (aggregate D)) ∧ ∀ j i f o, bits (j,i,f,o)=decide (o.val < indexedCount D j i f) := by
  have h := trace_cargo b q x (zeroState n d) t rfl ht bits
  have z (i : Fin d) (j : Fin 4) : ((zeroState n d).2 i j).val=0 := rfl
  simp_rw [z,Nat.zero_add] at h
  exact h

theorem raw_complete {n d} (b : ChargeIx n → Sig (countLen n)) (x : Input (countLen n))
    (u : Blocks n d) (sealedH : Sealed u) (bags : Fin d → List Arc)
    (fields : ∀ i j, (u.2.2.1.2 i j).val=tally (bags i) j) (valid : ∀ i a, a∈bags i → Raw n (a.1,a.2.1))
    (le : (List.ofFn bags).flatten.length≤2*n) (ask : Asked b u.2.1 x (imbalance (catRows bags))) :
    (rawBlock b u).ok x=true := by
  obtain ⟨D,perm,bounds⟩ := of_bags bags le valid
  have ch : imbalance (aggregate D)=imbalance (catRows bags) := charge_perm (merge_perm _ _ perm)
  let bits (w : Address n d) := decide (w.2.2.2.val < indexedCount D w.1 w.2.1 w.2.2.1)
  apply (walk_semantics (startNode (zeroState n d)) (wireEdge b u.2.1) (wireLabels n d) x _ _).1.mpr
  refine ⟨bits,(exact_source b u.2.1 x u.2.2.1 sealedH.2.1 bits).mpr ⟨D,bounds,?_,ch ▸ ask,fun _ _ _ _ => rfl⟩⟩
  intro i j
  exact (fields i j).trans (congrFun (tally_perm (perm i)) j).symm

theorem raw_sound {n d} (a : Width n → Sig (countLen n)) (b : ChargeIx n → Sig (countLen n))
    (σ : Equiv.Perm (Fin n)) (x : Input (countLen n)) (pfx : (List.ofFn x).take (2+n*n)=permPrefix σ)
    (u : Blocks n d) (sealedH : Sealed u) (guard : Scatter.guardSig (inverseMatrix n) u.1 x=true)
    (w : a u.2.1 x=true) (z : zeroMask (fun m => Scheduled n m.val) b u.2.1 x=true)
    (yes : (rawBlock b u).ok x=true) : fitsSignals a b x σ (pinsOf (rawBlock b u) x) := by
  obtain ⟨g,q,t,mask⟩ := u
  let L:=lastCell b q t
  have path := (walk_semantics (startNode (zeroState n d)) (wireEdge b q) (wireLabels n d) x _ _).2 yes
  obtain ⟨D,_,tf,ask,hw⟩ := (exact_source b q x t sealedH.2.1 (fun j => L.bits j x)).mp path
  exact PacketBank.selected_fit a b σ x g q t mask sealedH.2 pfx sealedH.1 guard w z L.bits D tf ask hw

theorem uniform_layout : LayoutCore := by
  refine ⟨202,fun t budget => ?_⟩
  dsimp only
  let n:=t+1
  let d:=budget.val+1
  have hd : d≤n := budget.isLt
  intro a b
  let raw:=rawBlock (n:=n) (d:=d) b
  let sel:=elected a b raw
  let pw:=fun z v => sel.bits (z,v)
  refine ⟨sel.ok,pw,elected_build (E:=150) a b raw (fun u _ => raw_build hd a b u),?_⟩
  intro σ cover x pfx _
  have sound (yes : sel.ok x=true) : fitsSignals a b x σ (pinsOf sel x) := by
    obtain ⟨u,sealedH,guard,w,z,ok,eq⟩ := elected_wires a b raw x yes
    rw [eq]
    exact raw_sound a b σ x pfx u sealedH guard w z ok
  refine ⟨⟨fun yes => ⟨_,sound yes⟩,?_⟩,sound⟩
  rintro ⟨p,hp⟩
  obtain ⟨g,hg,pass,_,_⟩ := literal_election σ x pfx cover
  obtain ⟨q,t,mask,bags,term,tf,raws,len,width,tail,ask⟩ := endpoint_witness a b σ p x g pfx hg pass hp
  let u : Blocks n d := (g,q,t,mask)
  have sealedH : Sealed u := ⟨hg,term⟩
  exact (elected_ok a b raw x).mpr ⟨u,sealedH,pass,width,tail,raw_complete b x u sealedH bags tf raws len ask⟩

end PEqualNP.Outside.L_pcx_386.FinalJoin

theorem PEqualNP.Outside.L_pcx_386 : (∃ C : ℕ, 0 < C ∧ ∀ t : ℕ,
  let n := t+1
  let I := Fin n
  let J := Fin (n+1)
  let V := Bool × I
  let P := V → Option Bool
  let W := Fin (2*n+1)
  let inputs := 2+n*n+(n+1)*(n+1)*(2*n+1)
  let hist := fun (σ : Equiv.Perm I) (p : P) (r b : J) =>
    ((Finset.univ : Finset (V → Bool)).filter (fun x =>
      (∀ v, p v = none ∨ p v = some (x v)) ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,i))).card = r.val ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,σ i))).card = b.val)).card
  ∀ budget : I,
    let d := budget.val+1
    ∃ (g : PEqualNP.CircuitLowerBounds.Circuit) (flag : Fin (inputs+g.size))
      (pinWire : Bool → V → Fin (inputs+g.size)),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs g ∧ g.size ≤ (n+2)^(C*(d+1)) ∧
      (∀ gate ∈ g.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
        (gate.op = .not ∧ gate.inputs.length = 1)) ∧
      ∀ (σ : Equiv.Perm I), (∃ root : Fin d → I, ∀ i : I,
        ∃ a : Fin d, ∃ h : I, (σ ^ h.val) (root a) = i) →
      ∀ H : J → J → W → Bool,
        let table := fun (r b : J) => ∑ k : W, (H r b k).toNat * 2^k.val
        let permBits := (List.ofFn (fun i : I => List.ofFn (fun j : I => decide (σ i = j)))).flatten
        let countBits := (List.ofFn (fun r : J => (List.ofFn (fun b : J => List.ofFn (H r b))).flatten)).flatten
        let ws := g.wires ([false,true] ++ permBits ++ countBits)
        let q : P := fun v => if ws.getD (pinWire false v).val false then some (ws.getD (pinWire true v).val false) else none
        (ws.getD flag.val false = true ↔ ∃ p : P, hist σ p = table) ∧
          (ws.getD flag.val false = true → hist σ q = table)) := by
  exact PEqualNP.Outside.L_pcx_386.Core.reduction_from_layout_core PEqualNP.Outside.L_pcx_386.FinalJoin.uniform_layout
