import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_384

-- The cycle transform and its ring coordinates are adapted from L-pcx-385, PR 43575.
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


def ringPerm (t : ℕ) : Equiv.Perm (Fin (t + 1)) where
  toFun i := i + 1
  invFun i := i - 1
  left_inv i := add_sub_cancel_right i 1
  right_inv i := sub_add_cancel i 1


section Histogram

variable {α : Type*} [Fintype α]

def fits (p : α → Option Bool) (x : α → Bool) : Prop :=
  ∀ i, p i = none ∨ p i = some (x i)

noncomputable def completions (p : α → Option Bool) : Finset (α → Bool) := by
  classical
  exact Finset.univ.filter (fun x => fits p x)

def freeCount (p : α → Option Bool) : ℕ :=
  (Finset.univ.filter (fun i => p i = none)).card

lemma mem_completions (p : α → Option Bool) (x : α → Bool) :
    x ∈ completions p ↔ fits p x := by
  classical
  simp [completions]

lemma card_completions (p : α → Option Bool) :
    (completions p).card = 2 ^ freeCount p := by
  classical
  let opts : α → Finset Bool := fun i => match p i with
    | none => Finset.univ
    | some b => {b}
  have heq : completions p = Fintype.piFinset opts := by
    ext x
    rw [mem_completions, Fintype.mem_piFinset]
    unfold fits
    apply forall_congr'
    intro i
    cases h : p i <;> simp [opts, h]
    exact eq_comm
  have hsize : ∀ i, (opts i).card = if p i = none then 2 else 1 := by
    intro i
    cases h : p i <;> simp [opts, h]
  rw [heq, Fintype.card_piFinset]
  simp_rw [hsize]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, one_pow, mul_one]
  rfl

def diff (σ : α → α) (x : Bool × α → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x (false, i) ≠ x (true, σ i))).card

lemma diff_le (σ : α → α) (x : Bool × α → Bool) : diff σ x ≤ Fintype.card α := by
  exact (Finset.card_filter_le _ _).trans (by simp)

noncomputable def histG (n : ℕ) (σ : α → α) (p : Bool × α → Option Bool)
    (d : Fin (n+1) × Fin (n+1)) : ℕ := by
  classical
  exact (Finset.univ.filter (fun x => fits p x ∧ diff id x = d.1.val ∧ diff σ x = d.2.val)).card

noncomputable def lawG (n : ℕ) (σ : α → α) (p : Bool × α → Option Bool)
    (d : Fin (n+1) × Fin (n+1)) : ℚ :=
  (histG n σ p d : ℚ) / (2 : ℚ) ^ freeCount p

lemma sum_mul_histG {n : ℕ} (hn : Fintype.card α = n)
    (σ : α → α) (p : Bool × α → Option Bool)
    (F : Fin (n+1) × Fin (n+1) → ℚ) :
    (∑ d, (histG n σ p d : ℚ) * F d) =
    ∑ x ∈ completions p, F (⟨diff id x, by have := diff_le id x; omega⟩,
                              ⟨diff σ x, by have := diff_le σ x; omega⟩) := by
  classical
  let stat : (Bool × α → Bool) → Fin (n+1) × Fin (n+1) := fun x =>
    (⟨diff id x, by have := diff_le id x; omega⟩, ⟨diff σ x, by have := diff_le σ x; omega⟩)
  change _ = ∑ x ∈ completions p, F (stat x)
  rw [← Finset.sum_fiberwise (completions p) stat (fun x => F (stat x))]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hh : (completions p).filter (fun x => stat x = d) =
      Finset.univ.filter (fun x => fits p x ∧ diff id x = d.1.val ∧ diff σ x = d.2.val) := by
    ext x
    rw [Finset.mem_filter, mem_completions]
    rcases d with ⟨r,b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, stat, Prod.mk.injEq, Fin.ext_iff]
  have hw : ∀ x ∈ (completions p).filter (fun x => stat x = d), F (stat x) = F d :=
    fun x hx => congrArg F (Finset.mem_filter.mp hx).2
  rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul, hh]
  rfl

lemma sum_histG {n : ℕ} (hn : Fintype.card α = n) (σ : α → α) (p : Bool × α → Option Bool) :
    (∑ d, histG n σ p d) = 2 ^ freeCount p := by
  have h := sum_mul_histG hn σ p (fun _ => 1)
  simp [card_completions] at h
  exact_mod_cast h

lemma histG_eq_implies_lawG_eq {β : Type*} [Fintype β]
    {n : ℕ} (hn : Fintype.card α = n) (hm : Fintype.card β = n)
    (σ : α → α) (τ : β → β) (p : Bool × α → Option Bool) (q : Bool × β → Option Bool)
    (h : histG n σ p = histG n τ q) : lawG n σ p = lawG n τ q := by
  have hs := sum_histG hn σ p
  rw [h, sum_histG hm τ q] at hs
  have he : freeCount q = freeCount p := Nat.pow_right_injective (by decide : 2 ≤ 2) hs
  funext d
  simp [lawG, h, he]

def edgeValue (u : ℚ) (a b : Bool) : ℚ := if a ≠ b then 1 - u else 1 + u

lemma prod_edgeValue (σ : α → α) (x : Bool × α → Bool) (u : ℚ) :
    (∏ i : α, edgeValue u (x (false,i)) (x (true,σ i))) =
      (1-u) ^ diff σ x * (1+u) ^ (Fintype.card α - diff σ x) := by
  classical
  unfold edgeValue diff
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 2
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α))
    (fun i => x (false,i) ≠ x (true,σ i))
  rw [Finset.card_univ] at h
  omega

noncomputable def transform (n : ℕ) (f : Fin (n+1) × Fin (n+1) → ℚ) (u v : ℚ) : ℚ :=
  ∑ d, f d *
    ((1-u) ^ d.1.val * (1+u) ^ (n-d.1.val) *
     ((1-v) ^ d.2.val * (1+v) ^ (n-d.2.val)))

noncomputable def avg (σ : α → α) (p : Bool × α → Option Bool) (u v : ℚ) : ℚ :=
  (∑ x ∈ completions p, ∏ i : α,
    edgeValue u (x (false,i)) (x (true,i)) * edgeValue v (x (false,i)) (x (true,σ i))) /
    (2 : ℚ) ^ freeCount p

lemma transform_eq_avg {n : ℕ} (hn : Fintype.card α = n)
    (σ : α → α) (p : Bool × α → Option Bool) (u v : ℚ) :
    transform n (lawG n σ p) u v = avg σ p u v := by
  classical
  let F : Fin (n+1) × Fin (n+1) → ℚ := fun d =>
    (1-u) ^ d.1.val * (1+u) ^ (n-d.1.val) * ((1-v) ^ d.2.val * (1+v) ^ (n-d.2.val))
  unfold transform lawG avg
  change ∑ d, ((histG n σ p d : ℚ) / (2 : ℚ)^freeCount p) * F d = _
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [sum_mul_histG hn σ p F]
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hr := prod_edgeValue id x u
  simp only [id_eq] at hr
  rw [Finset.prod_mul_distrib, prod_edgeValue σ, hr]
  simp only [F, hn]

end Histogram

section Cycles

variable {C : Type*} [Fintype C] (k : C → ℕ)

def sigmaNext (i : Σ c, Fin (k c + 1)) : Σ c, Fin (k c + 1) :=
  ⟨i.1, i.2 + 1⟩

def atRing {A : Type*} (p : Bool × (Σ c, Fin (k c + 1)) → A)
    (c : C) (v : Bool × Fin (k c + 1)) : A := p (v.1, ⟨c, v.2⟩)

def ringAssemble {A : Type*} (p : ∀ c : C, Bool × Fin (k c + 1) → A)
    (v : Bool × (Σ c, Fin (k c + 1))) : A := p v.2.1 (v.1, v.2.2)

lemma fits_sigma (p : Bool × (Σ c, Fin (k c + 1)) → Option Bool)
    (x : Bool × (Σ c, Fin (k c + 1)) → Bool) :
    fits p x ↔ ∀ c, fits (atRing k p c) (atRing k x c) := by
  constructor
  · intro h c v
    exact h (v.1, ⟨c, v.2⟩)
  · rintro h ⟨b,c,i⟩
    exact h c (b,i)

lemma freeCount_sigma (p : Bool × (Σ c, Fin (k c + 1)) → Option Bool) :
    freeCount p = ∑ c, freeCount (atRing k p c) := by
  simp only [freeCount, Finset.card_filter, Fintype.sum_prod_type, Fintype.sum_sigma]
  rw [Finset.sum_comm]
  rfl

lemma avg_sigma (p : Bool × (Σ c, Fin (k c + 1)) → Option Bool) (u v : ℚ) :
    avg (sigmaNext k) p u v =
      ∏ c : C, avg (fun i : Fin (k c + 1) => i + 1) (atRing k p c) u v := by
  classical
  unfold avg
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, freeCount_sigma]
  congr 1
  rw [Finset.prod_univ_sum]
  refine Finset.sum_bij (fun x _ => fun c => atRing k x c) ?_ ?_ ?_ ?_
  · intro x hx
    simpa only [mem_completions, Fintype.mem_piFinset, fits_sigma] using hx
  · intro x _ y _ h
    funext v
    exact congrFun (congrFun h v.2.1) (v.1,v.2.2)
  · intro y hy
    refine ⟨ringAssemble k y, ?_, ?_⟩
    · rw [mem_completions, fits_sigma]
      intro c
      exact (mem_completions _ _).mp (Fintype.mem_piFinset.mp hy c)
    · funext c v
      rfl
  · intro x _
    rw [Fintype.prod_sigma]
    rfl

end Cycles


def paintRing {B : ℕ} (a bit : Bool) (Q : Finset (Fin B)) (v : Bool × Fin B) : Option Bool :=
  if v.1 = a ∧ v.2 ∈ Q then some bit else none

lemma avg_paint_bit {b : ℕ} (a bit : Bool) (Q : Finset (Fin (b+1))) (u v : ℚ) :
    avg (fun i => i + 1) (paintRing a bit Q) u v =
    avg (fun i => i + 1) (paintRing a false Q) u v := by
  classical
  cases bit
  · rfl
  · unfold avg
    have hfree : freeCount (paintRing a true Q) = freeCount (paintRing a false Q) := by
      simp only [freeCount, paintRing]
      congr 1
      ext z
      by_cases h : z.1 = a ∧ z.2 ∈ Q <;> simp [h]
    rw [hfree]
    congr 1
    let e : (Bool × Fin (b+1) → Bool) ≃ (Bool × Fin (b+1) → Bool) :=
      Function.Involutive.toPerm (fun f z => !f z) (fun f => funext fun z => Bool.not_not (f z))
    refine Finset.sum_equiv e (fun f => ?_) (fun f _ => ?_)
    · simp only [mem_completions, fits]
      apply forall_congr'
      intro z
      change (paintRing a true Q z = none ∨ paintRing a true Q z = some (f z)) ↔
        (paintRing a false Q z = none ∨ paintRing a false Q z = some (!f z))
      by_cases h : z.1 = a ∧ z.2 ∈ Q <;> cases hf : f z <;> simp [paintRing, h, hf]
    · refine Finset.prod_congr rfl (fun i _ => ?_)
      change edgeValue u (f (false,i)) (f (true,i)) * edgeValue v (f (false,i)) (f (true,i+1)) =
        edgeValue u (!f (false,i)) (!f (true,i)) * edgeValue v (!f (false,i)) (!f (true,i+1))
      cases f (false,i) <;> cases f (true,i) <;> cases f (true,i+1) <;> rfl

lemma avg_eq_polyDef {b : ℕ} (p : Bool × Fin (b+1) → Option Bool) (u v : ℚ) :
    avg (fun i => i + 1) p u v = polyDef (b+1) (fun i => i + 1) p u v := by
  rw [← transform_eq_avg (by simp : Fintype.card (Fin (b+1)) = b+1)]
  unfold transform polyDef
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => ?_))
  have h : lawG (b+1) (fun i => i+1) p (r,s) = lawDef (b+1) (fun i => i+1) p r s := by
    unfold lawG lawDef histG fits diff freeCount
    congr 2
    congr 1
    ext x
    simp
  rw [h]
  ring

def edgeLift {b : ℕ} (a : Bool) (S : Fin (b+1) → Bool) (e : Bool × Fin (b+1)) : Bool :=
  S (if a || e.1 then e.2 + 1 else e.2)

def cycleValid {b : ℕ} (Q : Finset (Fin (b+1))) (S : Fin (b+1) → Bool) : Prop :=
  ∀ j, j ∉ Q → S (j+1) = S j

noncomputable def cycleSum {b : ℕ} (Q : Finset (Fin (b+1))) (z : ℚ) : ℚ := by
  classical
  exact ∑ S ∈ Finset.univ.filter (cycleValid Q), ∏ j, if S j then z else 1

lemma edgeLift_valid {b : ℕ} (a : Bool) (Q : Finset (Fin (b+1))) (S : Fin (b+1) → Bool)
    (h : cycleValid Q S) :
    ∀ e : Bool × Fin (b+1), qE (ringPerm b) (paintRing a false Q) e = none →
      edgeLift a S (nextE (ringPerm b) e) = edgeLift a S e := by
  rintro ⟨e,j⟩ he
  cases a <;> cases e
  · exact h j (by simpa [qE, headV, paintRing] using he)
  · rfl
  · rfl
  · exact h (j+1) (by simpa [qE, headV, paintRing, ringPerm] using he)

lemma edgeLift_surj_valid {b : ℕ} (a : Bool) (Q : Finset (Fin (b+1)))
    (W : Bool × Fin (b+1) → Bool)
    (h : ∀ e, qE (ringPerm b) (paintRing a false Q) e = none →
      W (nextE (ringPerm b) e) = W e) :
    ∃ S, cycleValid Q S ∧ edgeLift a S = W := by
  cases a
  · let S : Fin (b+1) → Bool := fun j => W (false,j)
    have he (j : Fin (b+1)) : W (false,j+1) = W (true,j) :=
      h (true,j) (by simp [qE, headV, paintRing])
    refine ⟨S, ?_, ?_⟩
    · intro j hj
      exact (he j).trans (h (false,j) (by simp [qE, headV, paintRing, hj]))
    · funext e
      rcases e with ⟨e,j⟩
      cases e
      · rfl
      · exact he j
  · let S : Fin (b+1) → Bool := fun j => W (true,j-1)
    have he (j : Fin (b+1)) : W (true,j) = W (false,j) :=
      h (false,j) (by simp [qE, headV, paintRing])
    refine ⟨S, ?_, ?_⟩
    · intro j hj
      have hh := h (true,j-1) (by simp [qE, headV, paintRing, ringPerm, hj])
      change W (false,j-1+1) = W (true,j-1) at hh
      simpa [S] using (he j).trans (by simpa using hh)
    · funext e
      rcases e with ⟨e,j⟩
      cases e <;> simp [edgeLift, S, he]

lemma edgeLift_injective {b : ℕ} (a : Bool) :
    Function.Injective (edgeLift (b := b) a) := by
  intro S T h
  funext j
  cases a
  · exact congrFun h (false,j)
  · simpa [edgeLift] using congrFun h (true,j-1)

lemma edgeLift_prod {b : ℕ} (a : Bool) (Q : Finset (Fin (b+1))) (S : Fin (b+1) → Bool) (u v : ℚ) :
    (∏ e : Bool × Fin (b+1),
      if edgeLift a S e then edgeW (ringPerm b) (paintRing a false Q) u v e else 1) =
      ∏ j, if S j then u*v else 1 := by
  have he : ∀ w, epsV (paintRing a false Q) w = 1 := by
    intro w
    by_cases h : w.1 = a ∧ w.2 ∈ Q <;> simp [paintRing, h, epsV, sgn]
  rw [Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [edgeW, epsE, he, mul_one, ↓reduceIte, Bool.false_eq_true]
  have shift (w : ℚ) : (∏ j, if S (j+1) then w else 1) = ∏ j, if S j then w else 1 :=
    Equiv.prod_comp (ringPerm b) (fun j => if S j then w else 1)
  cases a <;> simp only [edgeLift, Bool.false_or, Bool.true_or, Bool.false_eq_true, ↓reduceIte] <;>
    simp_rw [shift] <;>
    rw [← Finset.prod_mul_distrib] <;>
    refine Finset.prod_congr rfl (fun j _ => ?_) <;> cases S j <;> simp [mul_comm]

lemma avg_paint_cycleSum {b : ℕ} (a bit : Bool) (Q : Finset (Fin (b+1))) (u v : ℚ) :
    avg (fun i => i + 1) (paintRing a bit Q) u v = cycleSum Q (u*v) := by
  classical
  rw [avg_paint_bit, avg_eq_polyDef]
  change polyDef (b+1) (ringPerm b) (paintRing a false Q) u v = _
  rw [polyDef_eq_edgeSum]
  unfold cycleSum
  symm
  refine Finset.sum_bij (fun S _ => edgeLift a S) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    exact edgeLift_valid a Q S hS
  · intro S _ T _ h
    exact edgeLift_injective a h
  · intro W hW
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hW
    obtain ⟨S, hS, rfl⟩ := edgeLift_surj_valid a Q W hW
    exact ⟨S, by simpa using hS, rfl⟩
  · intro S _
    exact (edgeLift_prod a Q S u v).symm

lemma cycleSum_translate {b : ℕ} (Q : Finset (Fin (b+1))) (a : Fin (b+1)) (z : ℚ) :
    cycleSum (Q.map (Equiv.addRight a).toEmbedding) z = cycleSum Q z := by
  classical
  unfold cycleSum
  let shift := Equiv.addRight a
  let e : (Fin (b+1) → Bool) ≃ (Fin (b+1) → Bool) :=
    Equiv.arrowCongr shift (Equiv.refl Bool)
  have he (S : Fin (b+1) → Bool) (j : Fin (b+1)) : e S (shift j) = S j := by
    simp [e, Equiv.arrowCongr]
  symm
  refine Finset.sum_equiv e (fun S => ?_) (fun S _ => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, cycleValid]
    have hs (j : Fin (b+1)) : shift (j+1) = shift j + 1 := by
      change j + 1 + a = j + a + 1
      ac_rfl
    have ht (j : Fin (b+1)) :
        shift j ∈ Q.map shift.toEmbedding ↔ j ∈ Q := by
      rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
    constructor
    · intro h j hj
      obtain ⟨i, rfl⟩ := shift.surjective j
      rw [← hs i]
      simpa only [he] using h i (fun hi => hj ((ht i).2 hi))
    · intro h j hj
      have h' := h (shift j) (fun hi => hj ((ht j).1 hi))
      rw [← hs j] at h'
      simpa only [he] using h'
  · refine Fintype.prod_equiv shift _ _ (fun j => ?_)
    simp [e, Equiv.arrowCongr]

noncomputable def nextStop {b : ℕ} (Q : Finset (Fin (b+1))) (hQ : Fin.last b ∈ Q)
    (i : Fin (b+1)) : {j : Fin (b+1) // j ∈ Q} := by
  classical
  let U := Q.filter (fun j => i ≤ j)
  have hU : U.Nonempty := ⟨Fin.last b, Finset.mem_filter.mpr ⟨hQ, Fin.le_last _⟩⟩
  exact ⟨U.min' hU, (Finset.mem_filter.mp (U.min'_mem hU)).1⟩

lemma le_nextStop {b : ℕ} (Q : Finset (Fin (b+1))) (hQ : Fin.last b ∈ Q) (i : Fin (b+1)) :
    i ≤ (nextStop Q hQ i).1 := by
  classical
  have hU : (Q.filter (fun j => i ≤ j)).Nonempty :=
    ⟨Fin.last b, Finset.mem_filter.mpr ⟨hQ, Fin.le_last _⟩⟩
  exact (Finset.mem_filter.mp (Finset.min'_mem _ hU)).2

lemma nextStop_le {b : ℕ} (Q : Finset (Fin (b+1))) (hQ : Fin.last b ∈ Q)
    {i j : Fin (b+1)} (hij : i ≤ j) (hj : j ∈ Q) : (nextStop Q hQ i).1 ≤ j := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hj,hij⟩)

lemma nextStop_of_mem {b : ℕ} (Q : Finset (Fin (b+1))) (hQ : Fin.last b ∈ Q)
    {j : Fin (b+1)} (hj : j ∈ Q) : nextStop Q hQ j = ⟨j,hj⟩ := by
  apply Subtype.ext
  exact le_antisymm (nextStop_le Q hQ le_rfl hj) (le_nextStop Q hQ j)

lemma add_one_val_of_lt_last {b : ℕ} {j : Fin (b+1)} (hj : j < Fin.last b) :
    (j+1).val = j.val + 1 := by
  have hv : j.val < b := hj
  have hb : 1 < b+1 := by omega
  rw [Fin.val_add, show (1 : Fin (b+1)).val = 1 from Nat.mod_eq_of_lt hb,
    Nat.mod_eq_of_lt (by omega)]

lemma nextStop_step {b : ℕ} (Q : Finset (Fin (b+1))) (hQ : Fin.last b ∈ Q)
    {j : Fin (b+1)} (hj : j ∉ Q) :
    nextStop Q hQ (j+1) = nextStop Q hQ j := by
  have hjlast : j < Fin.last b := lt_of_le_of_ne (Fin.le_last _) (fun h => hj (h ▸ hQ))
  have hinc := add_one_val_of_lt_last hjlast
  have hle := le_nextStop Q hQ j
  have hne : j ≠ (nextStop Q hQ j).1 := fun h => hj (h ▸ (nextStop Q hQ j).2)
  have hlt := lt_of_le_of_ne hle hne
  apply Subtype.ext
  refine le_antisymm (nextStop_le Q hQ ?_ (nextStop Q hQ j).2)
    (nextStop_le Q hQ ?_ (nextStop Q hQ (j+1)).2)
  · exact (show (j+1).val ≤ (nextStop Q hQ j).1.val by
      have := (show j.val < (nextStop Q hQ j).1.val from hlt)
      omega)
  · exact (show j ≤ j+1 from (show j.val ≤ (j+1).val by omega)).trans (le_nextStop Q hQ (j+1))

lemma cycleValid_eq_nextStop {b : ℕ} (Q : Finset (Fin (b+1))) (hQ : Fin.last b ∈ Q)
    (S : Fin (b+1) → Bool) :
    cycleValid Q S ↔ ∀ i, S i = S (nextStop Q hQ i).1 := by
  constructor
  · intro h
    have H : ∀ (n : ℕ) (i : Fin (b+1)), (nextStop Q hQ i).1.val - i.val ≤ n →
        S i = S (nextStop Q hQ i).1 := by
      intro n
      induction n with
      | zero =>
        intro i hi
        have hle : i.val ≤ (nextStop Q hQ i).1.val := le_nextStop Q hQ i
        congr 1
        exact Fin.ext (by omega)
      | succ n ih =>
        intro i hi
        by_cases hm : i ∈ Q
        · rw [nextStop_of_mem Q hQ hm]
        have hlast : i < Fin.last b := lt_of_le_of_ne (Fin.le_last _) (fun h => hm (h ▸ hQ))
        have hinc := add_one_val_of_lt_last hlast
        have hn := nextStop_step Q hQ hm
        have hbound : (nextStop Q hQ (i+1)).1.val - (i+1).val ≤ n := by
          rw [hn, hinc]
          omega
        have he := ih (i+1) hbound
        rw [hn] at he
        exact (h i hm).symm.trans he
    exact fun i => H _ i le_rfl
  · intro h j hj
    rw [h (j+1), h j, nextStop_step Q hQ hj]

noncomputable def gapSize {b : ℕ} (Q : Finset (Fin (b+1))) (hQ : Fin.last b ∈ Q)
    (a : {j : Fin (b+1) // j ∈ Q}) : ℕ :=
  (Finset.univ.filter (fun i => nextStop Q hQ i = a)).card

lemma gapSize_pos {b : ℕ} (Q : Finset (Fin (b+1))) (hQ : Fin.last b ∈ Q)
    (a : {j : Fin (b+1) // j ∈ Q}) : 0 < gapSize Q hQ a := by
  apply Finset.card_pos.mpr
  exact ⟨a.1, by simpa [nextStop_of_mem Q hQ a.2]⟩

lemma sum_gapSize {b : ℕ} (Q : Finset (Fin (b+1))) (hQ : Fin.last b ∈ Q) :
    (∑ a : {j : Fin (b+1) // j ∈ Q}, gapSize Q hQ a) = b+1 := by
  classical
  have h := Finset.sum_fiberwise (Finset.univ : Finset (Fin (b+1))) (nextStop Q hQ) (fun _ => (1 : ℕ))
  simpa [gapSize] using h

lemma cycleSum_product {b : ℕ} (Q : Finset (Fin (b+1))) (hQ : Fin.last b ∈ Q) (z : ℚ) :
    cycleSum Q z = ∏ a : {j : Fin (b+1) // j ∈ Q}, (1 + z ^ gapSize Q hQ a) := by
  classical
  have hsurj : Function.Surjective (nextStop Q hQ) :=
    fun a => ⟨a.1, nextStop_of_mem Q hQ a.2⟩
  have hc : ∀ S, cycleValid Q S ↔ ∀ x y, nextStop Q hQ x = nextStop Q hQ y → S x = S y := by
    intro S
    rw [cycleValid_eq_nextStop Q hQ S]
    constructor
    · intro h x y hxy
      have h' := congrArg (fun a => S a.1) hxy
      exact (h x).trans (h'.trans (h y).symm)
    · intro h i
      exact h _ _ (nextStop_of_mem Q hQ (nextStop Q hQ i).2).symm
  unfold cycleSum
  rw [sum_valid_eq_prod (nextStop Q hQ) hsurj (fun _ => z) _ hc]
  simp [gapSize]

lemma cycleSum_empty_eq_last {b : ℕ} (z : ℚ) :
    cycleSum (∅ : Finset (Fin (b+1))) z = cycleSum {Fin.last b} z := by
  classical
  unfold cycleSum
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h j _
    exact h j (by simp)
  · intro h
    have hstop : ∀ j, (nextStop {Fin.last b} (Finset.mem_singleton_self (Fin.last b)) j).1 = Fin.last b :=
      fun j => Finset.mem_singleton.mp (nextStop {Fin.last b} (Finset.mem_singleton_self (Fin.last b)) j).2
    have h' := (cycleValid_eq_nextStop _ (Finset.mem_singleton_self (Fin.last b)) S).1 h
    simp only [hstop] at h'
    intro j _
    exact (h' _).trans (h' _).symm

noncomputable def gapMultiset {b : ℕ} (Q : Finset (Fin (b+1))) (hQ : Fin.last b ∈ Q) :
    Multiset ℕ :=
  (Finset.univ : Finset {j : Fin (b+1) // j ∈ Q}).val.map (gapSize Q hQ)

lemma gapMultiset_spec {b : ℕ} (Q : Finset (Fin (b+1))) (hQ : Fin.last b ∈ Q) :
    (∀ e ∈ gapMultiset Q hQ, 0 < e) ∧ (gapMultiset Q hQ).sum = b+1 ∧
      (gapMultiset Q hQ).card = Q.card ∧
      ∀ z : ℚ, cycleSum Q z = ((gapMultiset Q hQ).map (fun e => 1 + z ^ e)).prod := by
  refine ⟨?_, sum_gapSize Q hQ, ?_, ?_⟩
  · intro e he
    obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp he
    exact gapSize_pos Q hQ a
  · simp [gapMultiset]
    exact Multiset.card_attach
  · intro z
    rw [cycleSum_product Q hQ]
    simp only [gapMultiset, Multiset.map_map, Finset.prod_eq_multiset_prod]
    rfl

lemma cycleSum_factors {b : ℕ} (Q : Finset (Fin (b+1))) :
    ∃ M : Multiset ℕ, (∀ e ∈ M, 0 < e) ∧ M.sum = b+1 ∧ M.card = max 1 Q.card ∧
      ∀ z : ℚ, cycleSum Q z = (M.map (fun e => 1 + z ^ e)).prod := by
  classical
  by_cases hn : Q.Nonempty
  · let a := Fin.last b - hn.choose
    let R := Q.map (Equiv.addRight a).toEmbedding
    have hR : Fin.last b ∈ R := by
      apply Finset.mem_map.mpr
      refine ⟨hn.choose, hn.choose_spec, ?_⟩
      change hn.choose + (Fin.last b - hn.choose) = Fin.last b
      abel
    obtain ⟨h₁,h₂,h₃,h₄⟩ := gapMultiset_spec R hR
    refine ⟨gapMultiset R hR, h₁, h₂, ?_, ?_⟩
    · rw [h₃, show R.card = Q.card by simp [R], max_eq_right (Finset.card_pos.mpr hn)]
    · intro z
      rw [← cycleSum_translate Q a z]
      exact h₄ z
  · have hQ := Finset.not_nonempty_iff_eq_empty.mp hn
    subst Q
    let R : Finset (Fin (b+1)) := {Fin.last b}
    obtain ⟨h₁,h₂,h₃,h₄⟩ := gapMultiset_spec R (Finset.mem_singleton_self _)
    refine ⟨gapMultiset R (Finset.mem_singleton_self _), h₁, h₂, by simpa [R] using h₃, ?_⟩
    intro z
    rw [cycleSum_empty_eq_last]
    exact h₄ z

lemma multiset_eq_singleton_of_card_sum {M : Multiset ℕ} (hcard : M.card = 1) :
    M = {M.sum} := by
  obtain ⟨a,rfl⟩ := Multiset.card_eq_one.mp hcard
  simp

lemma cycleSum_singleton {b : ℕ} (a : Fin (b+1)) (z : ℚ) :
    cycleSum {a} z = 1 + z ^ (b+1) := by
  obtain ⟨M,_,hs,hc,ht⟩ := cycleSum_factors ({a} : Finset (Fin (b+1)))
  have hm : M = {b+1} := by
    rw [← hs]
    exact multiset_eq_singleton_of_card_sum (by simpa using hc)
  simpa [hm] using ht z

lemma diff_eq_zero {α : Type*} [Fintype α] (σ : α → α) (x : Bool × α → Bool) :
    diff σ x = 0 ↔ ∀ i, x (false,i) = x (true,σ i) := by
  unfold diff
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  simp

lemma diff_eq_full {α : Type*} [Fintype α] (σ : α → α) (x : Bool × α → Bool) :
    diff σ x = Fintype.card α ↔ ∀ i, x (false,i) ≠ x (true,σ i) := by
  refine ⟨fun h i => Finset.filter_card_eq (p := fun i => x (false,i) ≠ x (true,σ i)) ?_ i (Finset.mem_univ i), fun h => ?_⟩
  · simpa [diff] using h
  · have he : (Finset.univ.filter (fun i => x (false,i) ≠ x (true,σ i))) = Finset.univ := by
      ext i
      simp [h i]
    rw [diff, he, Finset.card_univ]

lemma histG_pos {α : Type*} [Fintype α] (n : ℕ) (σ : α → α) (p : Bool × α → Option Bool)
    (d : Fin (n+1) × Fin (n+1)) :
    0 < histG n σ p d ↔ ∃ x, fits p x ∧ diff id x = d.1.val ∧ diff σ x = d.2.val := by
  classical
  simp [histG, Finset.card_pos, Finset.Nonempty]

lemma lawG_pos {α : Type*} [Fintype α] (n : ℕ) (σ : α → α) (p : Bool × α → Option Bool)
    (d : Fin (n+1) × Fin (n+1)) :
    0 < lawG n σ p d ↔ 0 < histG n σ p d := by
  unfold lawG
  rw [div_pos_iff_of_pos_right (by positivity)]
  exact Nat.cast_pos

lemma const_of_succ {b : ℕ} (f : Fin (b+1) → Bool) (h : ∀ i, f (i+1) = f i) :
    ∀ i, f i = f 0 := by
  have H : ∀ k (hk : k < b+1), f ⟨k,hk⟩ = f 0 := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have hstep : (⟨k, by omega⟩ : Fin (b+1)) + 1 = ⟨k+1,hk⟩ :=
        Fin.ext (add_one_val_of_lt_last (show (⟨k, by omega⟩ : Fin (b+1)) < Fin.last b from (show k < b by omega)))
      rw [← hstep, h, ih]
  exact fun i => H i.val i.isLt

lemma bool_eq_of_ne_ne {a b c : Bool} (h₁ : a ≠ c) (h₂ : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

lemma paint_of_extrema {b : ℕ} (p : Bool × Fin (b+1) → Option Bool)
    (x y : Bool × Fin (b+1) → Bool) (hx : fits p x) (hy : fits p y)
    (hx₁ : ∀ j, x (false,j) = x (true,j)) (hx₂ : ∀ j, x (false,j) = x (true,j+1))
    (hy₁ : ∀ j, y (false,j) ≠ y (true,j)) (hy₂ : ∀ j, y (false,j) ≠ y (true,j+1)) :
    ∃ a bit Q, p = paintRing a bit Q := by
  have hxstep (j : Fin (b+1)) : x (false,j+1) = x (false,j) :=
    (hx₁ (j+1)).trans (hx₂ j).symm
  have hxs (w : Bool × Fin (b+1)) : x w = x (false,0) := by
    rcases w with ⟨a,j⟩
    cases a
    · exact const_of_succ (fun j => x (false,j)) hxstep j
    · exact (hx₁ j).symm.trans (const_of_succ (fun j => x (false,j)) hxstep j)
  have hystep (j : Fin (b+1)) : y (false,j+1) = y (false,j) :=
    bool_eq_of_ne_ne (hy₁ (j+1)) (hy₂ j)
  have hyfalse (i j : Fin (b+1)) : y (false,i) = y (false,j) :=
    (const_of_succ (fun j => y (false,j)) hystep i).trans (const_of_succ (fun j => y (false,j)) hystep j).symm
  have hys (v w : Bool × Fin (b+1)) : y v = y w → v.1 = w.1 := by
    rcases v with ⟨c,i⟩
    rcases w with ⟨d,j⟩
    intro hh
    cases c <;> cases d
    · rfl
    · exact (hy₁ j ((hyfalse j i).trans hh)).elim
    · exact (hy₁ i ((hyfalse i j).trans hh.symm)).elim
    · rfl
  by_cases hp : ∀ w, p w = none
  · refine ⟨false, false, ∅, ?_⟩
    funext w
    simp [hp, paintRing]
  · push_neg at hp
    obtain ⟨w, hw⟩ := hp
    let Q := Finset.univ.filter (fun j => p (w.1,j) ≠ none)
    refine ⟨w.1, x (false,0), Q, ?_⟩
    have hpval (v : Bool × Fin (b+1)) (hv : p v ≠ none) : p v = some (x (false,0)) :=
      ((hx v).resolve_left hv).trans (congrArg some (hxs v))
    have hsame (v : Bool × Fin (b+1)) (hv : p v ≠ none) : v.1 = w.1 := by
      apply hys
      have e₁ := (hy v).resolve_left hv
      have e₂ := (hy w).resolve_left hw
      exact Option.some.inj (e₁.symm.trans ((hpval v hv).trans ((hpval w hw).symm.trans e₂)))
    funext v
    rcases v with ⟨a,j⟩
    by_cases hz : p (a,j) = none
    · have hh : ¬(a = w.1 ∧ j ∈ Q) := by
        rintro ⟨rfl,hj⟩
        exact (Finset.mem_filter.mp hj).2 hz
      simp [paintRing, hh, hz]
    · have ha : a = w.1 := hsame (a,j) hz
      subst a
      have hj : j ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
      simpa [paintRing, hj] using hpval (w.1,j) hz

lemma freeCount_paint {B : ℕ} (a bit : Bool) (Q : Finset (Fin B)) :
    freeCount (paintRing a bit Q) + Q.card = 2 * B := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Bool × Fin B)))
    (fun v => paintRing a bit Q v = none)
  have he (v : Bool × Fin B) : paintRing a bit Q v ≠ none ↔ v.1 = a ∧ v.2 ∈ Q := by
    unfold paintRing
    split <;> simp_all
  have hq : ∑ j : Fin B, (if j ∈ Q then 1 else 0 : ℕ) = Q.card := by
    rw [← Finset.card_filter]
    simp
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] at h
  rw [Finset.card_filter (fun v => ¬ paintRing a bit Q v = none)] at h
  simp only [he, Fintype.sum_prod_type, Fintype.sum_bool] at h
  cases a <;> simp [hq] at h <;> exact h

section RingFamilies

variable {C : Type*} [Fintype C]

lemma card_shiftSigma (k : C → ℕ) :
    Fintype.card (Σ c, Fin (k c + 1)) = ∑ c, (k c + 1) := by
  simp [Fintype.card_sigma]

def sourcePins (s : C → ℕ) : Bool × (Σ c, Fin (s c + 1)) → Option Bool :=
  ringAssemble s (fun _ => paintRing false false {0})

lemma fits_sourcePins (s : C → ℕ) (x : Bool × (Σ c, Fin (s c + 1)) → Bool) :
    fits (sourcePins s) x ↔ ∀ c, x (false, ⟨c,0⟩) = false := by
  constructor
  · intro h c
    have hc := h (false, ⟨c,0⟩)
    simpa [sourcePins, ringAssemble, paintRing, eq_comm (a := false)] using hc
  · rintro h ⟨a,c,j⟩
    by_cases hj : a = false ∧ j = 0
    · rcases hj with ⟨rfl,rfl⟩
      simp [sourcePins, ringAssemble, paintRing, h c]
    · have hf : sourcePins s (a,⟨c,j⟩) = none := by
        simpa [sourcePins, ringAssemble, paintRing, hj]
      exact Or.inl hf

lemma source_hist_extrema (s : C → ℕ) {n : ℕ} (hn : ∑ c, (s c+1) = n) :
    0 < histG n (sigmaNext s) (sourcePins s) (0,0) ∧
      0 < histG n (sigmaNext s) (sourcePins s) (Fin.last n,Fin.last n) := by
  have hc : Fintype.card (Σ c, Fin (s c + 1)) = n := (card_shiftSigma s).trans hn
  rw [histG_pos, histG_pos]
  constructor
  · refine ⟨fun _ => false, (fits_sourcePins _ _).2 (fun _ => rfl), ?_, ?_⟩
    · exact (diff_eq_zero _ _).mpr (fun _ => rfl)
    · exact (diff_eq_zero _ _).mpr (fun _ => rfl)
  · refine ⟨Prod.fst, (fits_sourcePins _ _).2 (fun _ => rfl), ?_, ?_⟩
    · exact ((diff_eq_full _ _).mpr (fun _ => Bool.false_ne_true)).trans hc
    · exact ((diff_eq_full _ _).mpr (fun _ => Bool.false_ne_true)).trans hc

lemma freeCount_family (k : C → ℕ) (a bit : C → Bool) (Q : ∀ c, Finset (Fin (k c+1))) :
    freeCount (ringAssemble k (fun c => paintRing (a c) (bit c) (Q c))) +
      ∑ c, (Q c).card = 2 * ∑ c, (k c+1) := by
  rw [freeCount_sigma, ← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun c _ => freeCount_paint (a c) (bit c) (Q c))

lemma source_freeCount (s : C → ℕ) {n : ℕ} (hn : ∑ c, (s c+1) = n) :
    freeCount (sourcePins s) + Fintype.card C = 2*n := by
  simpa [sourcePins, hn] using freeCount_family s (fun _ => false) (fun _ => false) (fun _ => {0})

lemma source_transform (s : C → ℕ) {n : ℕ} (hn : ∑ c, (s c+1) = n) (u v : ℚ) :
    transform n (lawG n (sigmaNext s) (sourcePins s)) u v =
    ∏ c : C, (1 + (u*v) ^ (s c+1)) := by
  rw [transform_eq_avg ((card_shiftSigma s).trans hn), avg_sigma]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  change avg (fun j => j+1) (paintRing false false {0}) u v = _
  rw [avg_paint_cycleSum, cycleSum_singleton]

lemma paints_of_extrema (k : C → ℕ) (p : Bool × (Σ c, Fin (k c+1)) → Option Bool)
    {n : ℕ} (hn : ∑ c, (k c+1) = n)
    (h₀ : 0 < histG n (sigmaNext k) p (0,0))
    (h₁ : 0 < histG n (sigmaNext k) p (Fin.last n, Fin.last n)) :
    ∃ (a bit : C → Bool) (Q : ∀ c, Finset (Fin (k c+1))),
      p = ringAssemble k (fun c => paintRing (a c) (bit c) (Q c)) := by
  classical
  have hc : Fintype.card (Σ c, Fin (k c + 1)) = n := (card_shiftSigma k).trans hn
  obtain ⟨x,hx,hx₁,hx₂⟩ := (histG_pos _ _ _ _).1 h₀
  obtain ⟨y,hy,hy₁,hy₂⟩ := (histG_pos _ _ _ _).1 h₁
  have hx₁' := (diff_eq_zero id x).1 hx₁
  have hx₂' := (diff_eq_zero (sigmaNext k) x).1 hx₂
  have hy₁' := (diff_eq_full id y).1 (hy₁.trans hc.symm)
  have hy₂' := (diff_eq_full (sigmaNext k) y).1 (hy₂.trans hc.symm)
  have hpaint (c : C) :
      ∃ a bit Q, atRing k p c = paintRing a bit Q :=
    paint_of_extrema (atRing k p c) (atRing k x c) (atRing k y c)
      ((fits_sigma k _ _).1 hx c) ((fits_sigma k _ _).1 hy c)
      (fun j => hx₁' ⟨c,j⟩) (fun j => hx₂' ⟨c,j⟩) (fun j => hy₁' ⟨c,j⟩) (fun j => hy₂' ⟨c,j⟩)
  choose a bit Q hQ using hpaint
  refine ⟨a,bit,Q,?_⟩
  funext v
  rcases v with ⟨d,c,j⟩
  exact congrFun (hQ c) (d,j)

lemma paints_of_lawEq {K : Type*} [Fintype K] (s : K → ℕ) (k : C → ℕ)
    (p : Bool × (Σ c, Fin (k c+1)) → Option Bool) {n : ℕ}
    (hs : ∑ i, (s i+1) = n) (hk : ∑ c, (k c+1) = n)
    (h : lawG n (sigmaNext k) p = lawG n (sigmaNext s) (sourcePins s)) :
    ∃ (a bit : C → Bool) (Q : ∀ c, Finset (Fin (k c+1))),
      p = ringAssemble k (fun c => paintRing (a c) (bit c) (Q c)) := by
  have hpos d (hh : 0 < histG n (sigmaNext s) (sourcePins s) d) :
      0 < histG n (sigmaNext k) p d := by
    apply (lawG_pos _ _ _ _).1
    rw [h]
    exact (lawG_pos _ _ _ _).2 hh
  obtain ⟨h₀,h₁⟩ := source_hist_extrema s hs
  exact paints_of_extrema k p hk (hpos _ h₀) (hpos _ h₁)

lemma transform_paints (k : C → ℕ) {n : ℕ} (hn : ∑ c, (k c+1) = n)
    (a bit : C → Bool) (Q : ∀ c, Finset (Fin (k c+1))) (u v : ℚ) :
    transform n (lawG n (sigmaNext k) (ringAssemble k (fun c => paintRing (a c) (bit c) (Q c)))) u v =
    ∏ c : C, cycleSum (Q c) (u*v) := by
  rw [transform_eq_avg ((card_shiftSigma k).trans hn), avg_sigma]
  exact Finset.prod_congr rfl (fun c _ => avg_paint_cycleSum (a c) (bit c) (Q c) u v)

end RingFamilies


-- The least-exponent argument is adapted from L-pcx-385, PR 43575.
noncomputable def prodOnePlusPoly (M : Multiset ℕ) : Polynomial ℚ :=
  (M.map (fun e => 1 + Polynomial.X ^ e)).prod

lemma prodOnePlusPoly_add (M₁ M₂ : Multiset ℕ) :
    prodOnePlusPoly (M₁ + M₂) = prodOnePlusPoly M₁ * prodOnePlusPoly M₂ := by
  simp [prodOnePlusPoly, Multiset.map_add, Multiset.prod_add]

lemma eval_zero_prodOnePlusPoly (M : Multiset ℕ) (hM : ∀ e ∈ M, 0 < e) :
    (prodOnePlusPoly M).eval 0 = 1 := by
  induction M using Multiset.induction_on with
  | empty => simp [prodOnePlusPoly]
  | @cons e M ih =>
    simp only [prodOnePlusPoly, Multiset.map_cons, Multiset.prod_cons, Polynomial.eval_mul,
      Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X]
    have he : 0 < e := hM e (Multiset.mem_cons_self e M)
    have hM' : ∀ x ∈ M, 0 < x := fun x hx => hM x (Multiset.mem_cons_of_mem hx)
    rw [zero_pow (Nat.ne_of_gt he), add_zero, one_mul]
    exact ih hM'

lemma coeff_prodOnePlusPoly {d : ℕ} (hd : 0 < d) (M : Multiset ℕ) (hM : ∀ e ∈ M, d ≤ e) :
    (prodOnePlusPoly M).coeff 0 = 1 ∧
    (∀ j, 0 < j → j < d → (prodOnePlusPoly M).coeff j = 0) ∧
    (prodOnePlusPoly M).coeff d = (M.count d : ℚ) := by
  induction M using Multiset.induction_on with
  | empty =>
    simp only [prodOnePlusPoly, Multiset.map_zero, Multiset.prod_zero, Polynomial.coeff_one,
      ↓reduceIte, Multiset.count_zero, Nat.cast_zero, true_and]
    exact ⟨fun j hj _ => by simp [Nat.ne_of_gt hj], by simp [Nat.ne_of_gt hd]⟩
  | @cons e M ih =>
    have he : d ≤ e := hM e (Multiset.mem_cons_self e M)
    have hM' : ∀ x ∈ M, d ≤ x := fun x hx => hM x (Multiset.mem_cons_of_mem hx)
    obtain ⟨h0, hlt, hcd⟩ := ih hM'
    set P := prodOnePlusPoly M
    have hmul : prodOnePlusPoly (e ::ₘ M) = P + Polynomial.X ^ e * P := by
      simp only [prodOnePlusPoly, Multiset.map_cons, Multiset.prod_cons, P]
      ring
    rw [hmul]
    have hcoeff_add : ∀ m, (P + Polynomial.X ^ e * P).coeff m =
        P.coeff m + (if e ≤ m then P.coeff (m - e) else 0) := by
      intro m
      rw [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul']
    refine ⟨?_, ?_, ?_⟩
    · rw [hcoeff_add 0, h0]
      have : ¬ (e ≤ 0) := by omega
      simp [this]
    · intro j hj hjd
      rw [hcoeff_add j, hlt j hj hjd]
      have : ¬ (e ≤ j) := by omega
      simp [this]
    · rw [hcoeff_add d, hcd]
      by_cases hed : e = d
      · subst hed
        simp only [le_refl, ↓reduceIte, Nat.sub_self, h0, Multiset.count_cons_self, Nat.cast_add,
          Nat.cast_one]
      · have hne : ¬ (e ≤ d) := by omega
        have hne' : d ≠ e := Ne.symm hed
        simp [hne, Multiset.count_cons_of_ne hne']

lemma multiset_eq_of_prodOnePlusPoly_eq (M₁ M₂ : Multiset ℕ)
    (h₁ : ∀ e ∈ M₁, 0 < e) (h₂ : ∀ e ∈ M₂, 0 < e)
    (heq : prodOnePlusPoly M₁ = prodOnePlusPoly M₂) : M₁ = M₂ := by
  let C := M₁ ∩ M₂
  let A := M₁ - C
  let B := M₂ - C
  have hCA : A + C = M₁ := Multiset.sub_add_cancel Multiset.inter_le_left
  have hCB : B + C = M₂ := Multiset.sub_add_cancel Multiset.inter_le_right
  have hApos : ∀ e ∈ A, 0 < e := fun e he => h₁ e (hCA ▸ Multiset.mem_add.mpr (Or.inl he))
  have hBpos : ∀ e ∈ B, 0 < e := fun e he => h₂ e (hCB ▸ Multiset.mem_add.mpr (Or.inl he))
  have hCpos : ∀ e ∈ C, 0 < e := fun e he => h₁ e (hCA ▸ Multiset.mem_add.mpr (Or.inr he))
  have hCnz : prodOnePlusPoly C ≠ 0 := by
    intro h0
    have := eval_zero_prodOnePlusPoly C hCpos
    rw [h0, Polynomial.eval_zero] at this
    norm_num at this
  have hABeq : prodOnePlusPoly A = prodOnePlusPoly B := by
    apply mul_right_cancel₀ hCnz
    rw [← prodOnePlusPoly_add, ← prodOnePlusPoly_add, hCA, hCB, heq]
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
    have hcA := (coeff_prodOnePlusPoly hd_pos A hd_le_A).2.2
    have hcB := (coeff_prodOnePlusPoly hd_pos B hd_le_B).2.2
    rw [hABeq] at hcA
    have hcnt : A.count d = B.count d := by
      exact_mod_cast (show (A.count d : ℚ) = (B.count d : ℚ) from hcA.symm.trans hcB)
    rcases Multiset.mem_add.mp hd_mem with hdA | hdB
    · have hposA : 0 < A.count d := Multiset.count_pos.mpr hdA
      have hdB : d ∈ B := Multiset.count_pos.mp (hcnt ▸ hposA)
      exact hdisj d ⟨hdA, hdB⟩
    · have hposB : 0 < B.count d := Multiset.count_pos.mpr hdB
      have hdA : d ∈ A := Multiset.count_pos.mp (hcnt.symm ▸ hposB)
      exact hdisj d ⟨hdA, hdB⟩
  rw [← hCA, ← hCB, hAB]


lemma eq_of_plus_factors (M N : Multiset ℕ) (hM : ∀ e ∈ M, 0 < e) (hN : ∀ e ∈ N, 0 < e)
    (h : ∀ z : ℚ, (M.map (fun e => 1 + z ^ e)).prod = (N.map (fun e => 1 + z ^ e)).prod) :
    M = N := by
  apply multiset_eq_of_prodOnePlusPoly_eq M N hM hN
  apply Polynomial.funext
  intro z
  simpa only [prodOnePlusPoly, Polynomial.eval_multiset_prod, Multiset.map_map,
    Function.comp_apply, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_pow,
    Polynomial.eval_X] using h z


def spectrum {K : Type*} [Fintype K] (len : K → ℕ) : Multiset ℕ :=
  (Finset.univ : Finset K).val.map len

lemma mem_spectrum {K : Type*} [Fintype K] (len : K → ℕ) (e : ℕ) :
    e ∈ spectrum len ↔ ∃ k, len k = e := by
  simp [spectrum, Multiset.mem_map]

lemma spectrum_prod {K : Type*} [Fintype K] (len : K → ℕ) (z : ℚ) :
    ((spectrum len).map (fun e => 1 + z ^ e)).prod = ∏ k, (1 + z ^ len k) := by
  simp only [spectrum, Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

lemma spectrum_count {K : Type*} [Fintype K] (len : K → ℕ) (e : ℕ) :
    (spectrum len).count e = (Finset.univ.filter (fun k => len k = e)).card := by
  rw [spectrum, Multiset.count_map, ← Finset.filter_val]
  change (Finset.univ.filter (fun k => e = len k)).card = _
  congr 1
  exact Finset.filter_congr (fun _ _ => eq_comm)

lemma prod_factors_summed {C : Type*} [Fintype C] (M : C → Multiset ℕ) (z : ℚ) :
    (((∑ c, M c) : Multiset ℕ).map (fun e => 1 + z ^ e)).prod =
      ∏ c, ((M c).map (fun e => 1 + z ^ e)).prod := by
  classical
  induction (Finset.univ : Finset C) using Finset.induction_on with
  | empty => simp
  | @insert c s hc ih =>
    rw [Finset.sum_insert hc, Finset.prod_insert hc, Multiset.map_add, Multiset.prod_add, ih]

lemma narrow_sum_card {B : ℕ} (M : Multiset ℕ)
    (hs : M.sum = B) (hB : 0 < B) (h : ∀ e ∈ M, B < 4*e ∧ 2*e < B) :
    M.card = 3 := by
  have hm : 0 < M.card := by
    by_contra! hn
    have hz : M = 0 := Multiset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hn)
    simp [hz] at hs
    omega
  have H : ∀ N : Multiset ℕ,
      (∀ e ∈ N, B < 4*e ∧ 2*e < B) →
        (B+1)*N.card ≤ 4*N.sum ∧ 2*N.sum+N.card ≤ B*N.card := by
    intro N
    induction N using Multiset.induction_on with
    | empty => simp
    | @cons e N ih =>
      intro hh
      have he := hh e (Multiset.mem_cons_self e N)
      obtain ⟨h₁,h₂⟩ := ih (fun x hx => hh x (Multiset.mem_cons_of_mem hx))
      simp only [Multiset.card_cons, Multiset.sum_cons, Nat.mul_add, mul_one, Nat.add_mul, one_mul] at *
      exact ⟨by omega, by omega⟩
  obtain ⟨hl,hu⟩ := H M h
  rw [hs, Nat.add_mul, one_mul] at hl
  rw [hs] at hu
  have h₁ : B*2 < B*M.card := by omega
  have h₂ : B*M.card < B*4 := by omega
  exact (show M.card = 3 by
    have ht := Nat.lt_of_mul_lt_mul_left h₁
    have hl := Nat.lt_of_mul_lt_mul_left h₂
    omega)

lemma targets_have_three_pins {m b : ℕ} (s : Fin m × Fin 3 → ℕ)
    (hs : ∑ i, (s i+1) = m*(b+1))
    (hsize : ∀ i, b+1 < 4*(s i+1) ∧ 2*(s i+1) < b+1)
    (p : Bool × (Σ _ : Fin m, Fin (b+1)) → Option Bool)
    (h : lawG (m*(b+1)) (sigmaNext (fun _ => b)) p =
      lawG (m*(b+1)) (sigmaNext s) (sourcePins s)) :
    ∃ (a bit : Fin m → Bool) (Q : Fin m → Finset (Fin (b+1))),
      (∀ c, (Q c).card = 3) ∧
      p = ringAssemble (fun _ => b) (fun c => paintRing (a c) (bit c) (Q c)) := by
  classical
  have hk : ∑ _ : Fin m, (b+1) = m*(b+1) := by simp
  obtain ⟨a,bit,Q,hp⟩ := paints_of_lawEq s (fun _ => b) p hs hk h
  refine ⟨a,bit,Q,?_,hp⟩
  choose M hpos hsum hcard hprod using fun c => cycleSum_factors (Q c)
  have heq : (∑ c, M c) = spectrum (fun i => s i+1) := by
    apply eq_of_plus_factors
    · intro e he
      obtain ⟨c,_,hec⟩ := Multiset.mem_sum.mp he
      exact hpos c e hec
    · intro e he
      obtain ⟨i,rfl⟩ := (mem_spectrum _ _).mp he
      omega
    · intro z
      rw [prod_factors_summed, spectrum_prod]
      have hz := congrFun (congrFun (congrArg (transform (m*(b+1))) h) z) 1
      rw [hp, transform_paints (fun _ => b) hk, source_transform s hs, mul_one] at hz
      simpa only [hprod] using hz
  intro c
  have hm := narrow_sum_card (M c) (hsum c) (Nat.succ_pos b) (fun e he => by
    have hmem : e ∈ ∑ c, M c := Multiset.mem_sum.mpr ⟨c,Finset.mem_univ _,he⟩
    rw [heq] at hmem
    obtain ⟨i,rfl⟩ := (mem_spectrum _ _).mp hmem
    exact hsize i)
  have hh := hcard c
  omega

lemma lawEq_to_histEq {α β : Type*} [Fintype α] [Fintype β] {n : ℕ}
    (σ : α → α) (τ : β → β) (p : Bool × α → Option Bool) (q : Bool × β → Option Bool)
    (hf : freeCount p = freeCount q) (he : lawG n σ p = lawG n τ q) :
    histG n σ p = histG n τ q := by
  funext d
  have hh := congrFun he d
  unfold lawG at hh
  rw [hf] at hh
  exact_mod_cast (div_left_inj' (by positivity : (2 : ℚ) ^ freeCount q ≠ 0)).mp hh

lemma norm_implies_hist {m b : ℕ} (s : Fin m × Fin 3 → ℕ)
    (hs : ∑ i, (s i+1) = m*(b+1))
    (hsize : ∀ i, b+1 < 4*(s i+1) ∧ 2*(s i+1) < b+1)
    (p : Bool × (Σ _ : Fin m, Fin (b+1)) → Option Bool)
    (h : lawG (m*(b+1)) (sigmaNext (fun _ => b)) p =
      lawG (m*(b+1)) (sigmaNext s) (sourcePins s)) :
    histG (m*(b+1)) (sigmaNext (fun _ => b)) p =
      histG (m*(b+1)) (sigmaNext s) (sourcePins s) := by
  obtain ⟨a,bit,Q,hc,hp⟩ := targets_have_three_pins s hs hsize p h
  have hfree := freeCount_family (fun _ => b) a bit Q
  have hsource := source_freeCount s hs
  rw [← hp] at hfree
  have hfree' : freeCount p + m*3 = 2*(m*(b+1)) := by
    simpa [hc, nsmul_eq_mul] using hfree
  have hsource' : freeCount (sourcePins s) + m*3 = 2*(m*(b+1)) := by simpa using hsource
  exact lawEq_to_histEq _ _ _ _ (Nat.add_right_cancel (hfree'.trans hsource'.symm)) h

section Transport

variable {α β : Type*} [Fintype α] [Fintype β]

lemma card_filter_equiv (e : α ≃ β) (P : α → Prop) (Q : β → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ i, P i ↔ Q (e i)) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
  rw [Finset.card_filter, Finset.card_filter]
  exact Fintype.sum_equiv e _ _ (fun i => by simp only [h i])

def pullback (e : α ≃ β) {A : Type*} (p : Bool × β → A) : Bool × α → A :=
  fun v => p (v.1,e v.2)

lemma freeCount_pullback (e : α ≃ β) (p : Bool × β → Option Bool) :
    freeCount (pullback e p) = freeCount p :=
  card_filter_equiv (Equiv.prodCongr (Equiv.refl Bool) e) _ _ (fun _ => Iff.rfl)

lemma fits_pullback (e : α ≃ β) (p : Bool × β → Option Bool) (x : Bool × β → Bool) :
    fits (pullback e p) (pullback e x) ↔ fits p x := by
  constructor
  · rintro h ⟨d,j⟩
    obtain ⟨i,rfl⟩ := e.surjective j
    exact h (d,i)
  · rintro h ⟨d,i⟩
    exact h (d,e i)

lemma diff_pullback (e : α ≃ β) (σ : α → α) (τ : β → β)
    (h : ∀ i, e (σ i) = τ (e i)) (x : Bool × β → Bool) :
    diff σ (pullback e x) = diff τ x := by
  apply card_filter_equiv e
  intro i
  simp [pullback, h i]

lemma histG_pullback (e : α ≃ β) (σ : α → α) (τ : β → β)
    (h : ∀ i, e (σ i) = τ (e i)) (n : ℕ) (p : Bool × β → Option Bool) :
    histG n σ (pullback e p) = histG n τ p := by
  classical
  let E : (Bool × β → Bool) ≃ (Bool × α → Bool) :=
    { toFun := pullback e
      invFun := pullback e.symm
      left_inv := fun f => funext (fun v => by simp [pullback])
      right_inv := fun f => funext (fun v => by simp [pullback]) }
  funext d
  unfold histG
  symm
  refine card_filter_equiv E _ _ (fun x => ?_)
  change (fits p x ∧ diff id x = d.1.val ∧ diff τ x = d.2.val) ↔
    fits (pullback e p) (pullback e x) ∧ diff id (pullback e x) = d.1.val ∧
    diff σ (pullback e x) = d.2.val
  rw [fits_pullback, diff_pullback e id id (fun _ => rfl), diff_pullback e σ τ h]

lemma lawG_pullback (e : α ≃ β) (σ : α → α) (τ : β → β)
    (h : ∀ i, e (σ i) = τ (e i)) (n : ℕ) (p : Bool × β → Option Bool) :
    lawG n σ (pullback e p) = lawG n τ p := by
  funext d
  simp only [lawG, histG_pullback e σ τ h, freeCount_pullback]

lemma law_eq_iff_cross {n : ℕ} (σ : α → α) (τ : β → β)
    (p : Bool × α → Option Bool) (q : Bool × β → Option Bool) :
    lawG n σ p = lawG n τ q ↔
      ∀ d, histG n σ p d * 2 ^ freeCount q = histG n τ q d * 2 ^ freeCount p := by
  have hp : (2 : ℚ)^freeCount p ≠ 0 := by positivity
  have hq : (2 : ℚ)^freeCount q ≠ 0 := by positivity
  constructor
  · intro h d
    have hh := (div_eq_div_iff hp hq).1 (congrFun h d)
    exact_mod_cast hh
  · intro h
    funext d
    apply (div_eq_div_iff hp hq).2
    exact_mod_cast h d

end Transport

def targetNext {m b : ℕ} (i : Fin m × Fin (b+1)) : Fin m × Fin (b+1) :=
  (i.1,i.2+1)

def targetEquiv (m b : ℕ) :
    (Σ _ : Fin m, Fin (b+1)) ≃ (Fin m × Fin (b+1)) :=
  Equiv.sigmaEquivProd (Fin m) (Fin (b+1))

lemma target_hist_pullback {m b : ℕ} (p : Bool × (Fin m × Fin (b+1)) → Option Bool) :
    histG (m*(b+1)) (sigmaNext (fun _ => b)) (pullback (targetEquiv m b) p) =
    histG (m*(b+1)) targetNext p :=
  histG_pullback (targetEquiv m b) _ _ (fun _ => rfl) _ p

lemma target_law_pullback {m b : ℕ} (p : Bool × (Fin m × Fin (b+1)) → Option Bool) :
    lawG (m*(b+1)) (sigmaNext (fun _ => b)) (pullback (targetEquiv m b) p) =
    lawG (m*(b+1)) targetNext p :=
  lawG_pullback (targetEquiv m b) _ _ (fun _ => rfl) _ p

lemma source_freeCount_closed {m b : ℕ} (s : Fin m × Fin 3 → ℕ)
    (hs : ∑ i, (s i+1) = m*(b+1)) :
    freeCount (sourcePins s) = 2*m*(b+1) - 3*m := by
  have h := source_freeCount s hs
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  rw [Nat.mul_assoc]
  omega

lemma target_norm_iff_hist {m b : ℕ} (s : Fin m × Fin 3 → ℕ)
    (hs : ∑ i, (s i+1) = m*(b+1))
    (hsize : ∀ i, b+1 < 4*(s i+1) ∧ 2*(s i+1) < b+1)
    (p : Bool × (Fin m × Fin (b+1)) → Option Bool) :
    lawG (m*(b+1)) targetNext p = lawG (m*(b+1)) (sigmaNext s) (sourcePins s) ↔
    histG (m*(b+1)) targetNext p = histG (m*(b+1)) (sigmaNext s) (sourcePins s) := by
  constructor
  · intro h
    rw [← target_law_pullback] at h
    rw [← target_hist_pullback]
    exact norm_implies_hist s hs hsize _ h
  · exact histG_eq_implies_lawG_eq (by simp) ((card_shiftSigma s).trans hs) _ _ _ _

-- The interpolation proof is adapted from L-pcx-385, PR 43575.
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

lemma transform_injective {n : ℕ} {f g : Fin (n+1) × Fin (n+1) → ℚ}
    (h : ∀ u v : ℚ, 0 < u → u < 1 → 0 < v → v < 1 → transform n f u v = transform n g u v) :
    f = g := by
  have hxy : ∀ a c : Fin (n + 1),
      ∑ r : Fin (n + 1), ∑ b : Fin (n + 1),
        (f (r,b) - g (r,b)) *
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
    have hrew : ∀ (F : Fin (n+1) × Fin (n+1) → ℚ),
        transform n F u v =
        (2 / (1 + x)) ^ n * (2 / (1 + y)) ^ n *
        ∑ r : Fin (n + 1), ∑ b : Fin (n + 1), F (r,b) * x ^ r.val * y ^ b.val := by
      intro F
      unfold transform
      rw [Fintype.sum_prod_type]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [h1mu, h1pu, h1mv, h1pv]
      have hpr := hpow (2 / (1 + x)) x r
      have hpb := hpow (2 / (1 + y)) y b
      calc
        F (r,b) * (((2 / (1 + x)) * x) ^ r.val * (2 / (1 + x)) ^ (n - r.val) *
          (((2 / (1 + y)) * y) ^ b.val * (2 / (1 + y)) ^ (n - b.val)))
          = F (r,b) *
            (((2 / (1 + x)) * x) ^ r.val * (2 / (1 + x)) ^ (n - r.val)) *
            (((2 / (1 + y)) * y) ^ b.val * (2 / (1 + y)) ^ (n - b.val)) := by ring
        _ = F (r,b) * ((2 / (1 + x)) ^ n * x ^ r.val) *
            ((2 / (1 + y)) ^ n * y ^ b.val) := by rw [hpr, hpb]
        _ = (2 / (1 + x)) ^ n * (2 / (1 + y)) ^ n * (F (r,b) * x ^ r.val * y ^ b.val) := by
            ring
    rw [hrew f, hrew g] at huv
    have hfac : (2 / (1 + x)) ^ n * (2 / (1 + y)) ^ n ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (div_ne_zero two_ne_zero h1px.ne'))
        (pow_ne_zero _ (div_ne_zero two_ne_zero h1py.ne'))
    have hsum_eq := mul_left_cancel₀ hfac huv
    have hsub :
        (∑ r : Fin (n + 1), ∑ b : Fin (n + 1),
          (f (r,b) - g (r,b)) * x ^ r.val * y ^ b.val) =
        (∑ r : Fin (n + 1), ∑ b : Fin (n + 1), f (r,b) * x ^ r.val * y ^ b.val) -
        (∑ r : Fin (n + 1), ∑ b : Fin (n + 1), g (r,b) * x ^ r.val * y ^ b.val) := by
      simp_rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun b _ => ?_))
      ring
    rw [hsub, hsum_eq, sub_self]
  have hinner : ∀ (a b : Fin (n + 1)),
      ∑ r : Fin (n + 1), (f (r,b) - g (r,b)) *
        ((1 : ℚ) / (a.val + 2 : ℚ)) ^ r.val = 0 := by
    intro a
    apply coeff_eq_zero_of_poly_eval_unit
    intro c
    have hc := hxy a c
    rw [Finset.sum_comm] at hc
    simpa [Finset.sum_mul] using hc
  funext d
  rcases d with ⟨r,b⟩
  have hr : f (r,b) - g (r,b) = 0 :=
    coeff_eq_zero_of_poly_eval_unit (fun r => f (r,b) - g (r,b))
      (fun a => hinner a b) r
  exact sub_eq_zero.mp hr



-- The fiber-preserving permutation count is from L-lib-667, PR 39612.
private lemma card_perm_fiber_map {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (f g : α → β) :
    (Finset.univ.filter (fun p : Equiv.Perm α => ∀ x : α, g (p x) = f x)).card =
      if ∀ b : β, (Finset.univ.filter (fun x => f x = b)).card =
                  (Finset.univ.filter (fun x => g x = b)).card
      then ∏ b : β, ((Finset.univ.filter (fun x => f x = b)).card).factorial
      else 0 := by
  by_cases heq : ∀ b : β, (Finset.univ.filter (fun x => f x = b)).card =
      (Finset.univ.filter (fun x => g x = b)).card
  · simp only [heq, implies_true, ↓reduceIte]
    let Dom := { p : Equiv.Perm α // ∀ x : α, g (p x) = f x }
    let Cod := ∀ b : β, { x : α // f x = b } ≃ { y : α // g y = b }
    let toCod : Dom → Cod := fun p b =>
      { toFun := fun x => ⟨p.1 x.1, (p.2 x.1).trans x.2⟩
        invFun := fun y => ⟨p.1.symm y.1, by
          have h := p.2 (p.1.symm y.1)
          simp only [Equiv.apply_symm_apply] at h
          exact h.symm.trans y.2⟩
        left_inv := fun x => Subtype.ext (p.1.symm_apply_apply x.1)
        right_inv := fun y => Subtype.ext (p.1.apply_symm_apply y.1) }
    let fromCod : Cod → Dom := fun φ =>
      ⟨{ toFun := fun x => (φ (f x) ⟨x, rfl⟩).1
         invFun := fun y => ((φ (g y)).symm ⟨y, rfl⟩).1
         left_inv := fun x => by
           dsimp only
           have hg : g (φ (f x) ⟨x, rfl⟩).1 = f x := (φ (f x) ⟨x, rfl⟩).2
           have hcast : ∀ (b1 b2 : β) (hb : b1 = b2) (z : { y : α // g y = b1 }),
               ((φ b1).symm z).1 = ((φ b2).symm ⟨z.1, z.2.trans hb⟩).1 := by
             intro b1 b2 hb z; subst hb; rfl
           rw [hcast (g (φ (f x) ⟨x, rfl⟩).1) (f x) hg ⟨(φ (f x) ⟨x, rfl⟩).1, rfl⟩]
           change ((φ (f x)).symm (φ (f x) ⟨x, rfl⟩)).1 = x
           rw [Equiv.symm_apply_apply]
         right_inv := fun y => by
           dsimp only
           have hf : f ((φ (g y)).symm ⟨y, rfl⟩).1 = g y := ((φ (g y)).symm ⟨y, rfl⟩).2
           have hcast : ∀ (b1 b2 : β) (hb : b1 = b2) (z : { x : α // f x = b1 }),
               (φ b1 z).1 = (φ b2 ⟨z.1, z.2.trans hb⟩).1 := by
             intro b1 b2 hb z; subst hb; rfl
           rw [hcast (f ((φ (g y)).symm ⟨y, rfl⟩).1) (g y) hf ⟨((φ (g y)).symm ⟨y, rfl⟩).1, rfl⟩]
           change (φ (g y) ((φ (g y)).symm ⟨y, rfl⟩)).1 = y
           rw [Equiv.apply_symm_apply] },
       fun x => (φ (f x) ⟨x, rfl⟩).2⟩
    let eqv : Dom ≃ Cod :=
      { toFun := toCod
        invFun := fromCod
        left_inv := fun p => by
          apply Subtype.ext
          ext x
          rfl
        right_inv := fun φ => by
          funext b
          ext x
          rcases x with ⟨x, hx⟩
          subst hx
          rfl }
    have hcard_dom : (Finset.univ.filter (fun p : Equiv.Perm α => ∀ x : α, g (p x) = f x)).card =
        Fintype.card Dom := (Fintype.card_subtype _).symm
    rw [hcard_dom, Fintype.card_congr eqv, Fintype.card_pi]
    apply Finset.prod_congr rfl
    intro b _
    have hc1 : Fintype.card { x : α // f x = b } = (Finset.univ.filter (fun x => f x = b)).card :=
      Fintype.card_subtype _
    have hc2 : Fintype.card { y : α // g y = b } = (Finset.univ.filter (fun x => g x = b)).card :=
      Fintype.card_subtype _
    have hce : Fintype.card { x : α // f x = b } = Fintype.card { y : α // g y = b } := by
      rw [hc1, hc2, heq b]
    let efg : { x : α // f x = b } ≃ { y : α // g y = b } := Fintype.equivOfCardEq hce
    have hperm : Fintype.card ({ x : α // f x = b } ≃ { y : α // g y = b }) =
        Fintype.card (Equiv.Perm { x : α // f x = b }) :=
      Fintype.card_congr (Equiv.equivCongr (Equiv.refl _) efg.symm)
    rw [hperm, Fintype.card_perm, hc1, heq b]
  · simp only [heq, ↓reduceIte]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    apply heq
    intro b
    apply Finset.card_bij (fun x _ => p x)
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ _, (hp x).trans hx.2⟩
    · intro x _ y _ hxy
      exact p.injective hxy
    · intro y hy
      rw [Finset.mem_filter] at hy
      refine ⟨p.symm y, ?_, p.apply_symm_apply y⟩
      rw [Finset.mem_filter]
      have h := hp (p.symm y)
      simp only [Equiv.apply_symm_apply] at h
      exact ⟨Finset.mem_univ _, h.symm.trans hy.2⟩

lemma card_length_labels {K : Type} [Fintype K] [DecidableEq K]
    (B : ℕ) (arc len : K → ℕ)
    (ha : ∀ i, arc i ≤ B) (hl : ∀ i, len i ≤ B)
    (hf : ∀ j : Fin (B+1), (Finset.univ.filter (fun i => arc i = j.val)).card =
      (Finset.univ.filter (fun i => len i = j.val)).card) :
    (Finset.univ.filter (fun π : Equiv.Perm K => ∀ i, len (π i) = arc i)).card =
      ∏ j : Fin (B+1), ((Finset.univ.filter (fun i => len i = j.val)).card).factorial := by
  let f (i : K) : Fin (B+1) := ⟨arc i, Nat.lt_succ_of_le (ha i)⟩
  let g (i : K) : Fin (B+1) := ⟨len i, Nat.lt_succ_of_le (hl i)⟩
  have heq : ∀ j : Fin (B+1),
      (Finset.univ.filter (fun i => f i = j)).card =
      (Finset.univ.filter (fun i => g i = j)).card := by
    simpa only [Fin.ext_iff, f, g] using hf
  have h := card_perm_fiber_map f g
  simp only [heq, implies_true, ↓reduceIte] at h
  simpa only [Fin.ext_iff, f, g, hf] using h



abbrev SlotAssignment (m B : ℕ) (len : Fin m × Fin 3 → ℕ) :=
  { π : Equiv.Perm (Fin m × Fin 3) // ∀ c : Fin m, (∑ u : Fin 3, len (π (c, u))) = B }

abbrev LengthProfile (m B : ℕ) (len : Fin m × Fin 3 → ℕ) :=
  { arc : (Fin m × Fin 3) → Fin (B+1) //
    (∀ i, 0 < (arc i).val) ∧
    (∀ c : Fin m, (∑ u : Fin 3, (arc (c, u)).val) = B) ∧
    (∀ j : Fin (B+1), (Finset.univ.filter (fun i => (arc i).val = j.val)).card =
      (Finset.univ.filter (fun i => len i = j.val)).card) }

def lengthProfileOfSlots {m B : ℕ} {len : Fin m × Fin 3 → ℕ}
    (hpos : ∀ i, 0 < len i) (hle : ∀ i, len i ≤ B) (π : SlotAssignment m B len) :
    LengthProfile m B len := by
  refine ⟨fun i => ⟨len (π.1 i), Nat.lt_succ_of_le (hle (π.1 i))⟩,
      fun i => hpos (π.1 i), π.2, ?_⟩
  intro j
  apply Finset.card_bij (fun i _ => π.1 i)
  · intro i hi
    simpa using hi
  · intro i _ k _ h
    exact π.1.injective h
  · intro i hi
    refine ⟨π.1.symm i, ?_, π.1.apply_symm_apply i⟩
    simpa using hi

def lengthProfileFiberEquiv {m B : ℕ} {len : Fin m × Fin 3 → ℕ}
    (hpos : ∀ i, 0 < len i) (hle : ∀ i, len i ≤ B) (arc : LengthProfile m B len) :
    { π : SlotAssignment m B len // lengthProfileOfSlots hpos hle π = arc } ≃
      { π : Equiv.Perm (Fin m × Fin 3) // ∀ i, len (π i) = (arc.1 i).val } where
  toFun π := ⟨π.1.1, fun i =>
    congrArg (fun p : LengthProfile m B len => (p.1 i).val) π.2⟩
  invFun π := by
    have h : ∀ c : Fin m, (∑ u : Fin 3, len (π.1 (c, u))) = B := by
      intro c
      simpa only [π.2] using arc.2.2.1 c
    refine ⟨⟨π.1, h⟩, ?_⟩
    apply Subtype.ext
    funext i
    exact Fin.ext (π.2 i)
  left_inv π := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv π := by
    apply Subtype.ext
    rfl

lemma card_slots_profiles {m B : ℕ} (len : Fin m × Fin 3 → ℕ)
    (hpos : ∀ i, 0 < len i) (hle : ∀ i, len i ≤ B) :
    Nat.card (SlotAssignment m B len) =
      (∏ j : Fin (B+1), ((Finset.univ.filter (fun i => len i = j.val)).card).factorial) *
        Nat.card (LengthProfile m B len) := by
  classical
  let copies := ∏ j : Fin (B+1), ((Finset.univ.filter (fun i => len i = j.val)).card).factorial
  have hcard (arc : LengthProfile m B len) :
      Nat.card { π : SlotAssignment m B len // lengthProfileOfSlots hpos hle π = arc } =
        copies := by
    rw [Nat.card_congr (lengthProfileFiberEquiv hpos hle arc), Nat.card_eq_fintype_card,
      Fintype.card_subtype]
    exact card_length_labels B (fun i => (arc.1 i).val) len
      (fun i => Nat.le_of_lt_succ (arc.1 i).isLt) hle arc.2.2.2
  calc
    Nat.card (SlotAssignment m B len) =
        Nat.card (Σ arc : LengthProfile m B len,
          { π : SlotAssignment m B len // lengthProfileOfSlots hpos hle π = arc }) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv (lengthProfileOfSlots hpos hle)).symm
    _ = copies * Nat.card (LengthProfile m B len) := by
      rw [Nat.card_sigma]
      simp only [hcard]
      simp [Nat.card_eq_fintype_card, mul_comm]

lemma card_slots_profiles_finset {m B : ℕ} (len : Fin m × Fin 3 → ℕ)
    (hpos : ∀ i, 0 < len i) (hle : ∀ i, len i ≤ B) :
    (Finset.univ.filter (fun π : Equiv.Perm (Fin m × Fin 3) =>
      ∀ c : Fin m, (∑ u : Fin 3, len (π (c, u))) = B)).card =
      (∏ j : Fin (B+1), ((Finset.univ.filter (fun i => len i = j.val)).card).factorial) *
        Nat.card (LengthProfile m B len) := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact card_slots_profiles len hpos hle



abbrev RingGaps (B : ℕ) :=
  { l : Fin 3 → ℕ // (∀ u, 0 < l u) ∧ ∑ u : Fin 3, l u = B }

abbrev RingOffsets (B : ℕ) [NeZero B] :=
  { q : Fin B × Fin B // 0 < q.1 ∧ q.1 < q.2 }

abbrev ZeroMarkedTriple (B : ℕ) [NeZero B] :=
  { S : Finset (Fin B) // S.card = 3 ∧ 0 ∈ S }

abbrev MarkedTriple (B : ℕ) :=
  { p : Fin B × Finset (Fin B) // p.2.card = 3 ∧ p.1 ∈ p.2 }

def gapOffsetsEquiv (B : ℕ) [NeZero B] : RingGaps B ≃ RingOffsets B where
  toFun l := by
    have h := l.2.2
    rw [Fin.sum_univ_three] at h
    have h0 := l.2.1 0
    have h1 := l.2.1 1
    have h2 := l.2.1 2
    refine ⟨(⟨l.1 0, by omega⟩, ⟨l.1 0 + l.1 1, by omega⟩), ?_⟩
    simpa only [Fin.lt_def, Fin.val_zero, Nat.lt_add_right_iff_pos] using And.intro h0 h1
  invFun q := by
    have h0 : 0 < q.1.1.val := by simpa only [Fin.lt_def, Fin.val_zero] using q.2.1
    have h1 : q.1.1.val < q.1.2.val := q.2.2
    have h2 := q.1.2.isLt
    refine ⟨![q.1.1.val, q.1.2.val - q.1.1.val, B - q.1.2.val], ?_, ?_⟩
    · intro u
      fin_cases u <;> simp <;> omega
    · rw [Fin.sum_univ_three]
      change q.1.1.val + (q.1.2.val - q.1.1.val) + (B - q.1.2.val) = B
      omega
  left_inv l := by
    have h := l.2.2
    rw [Fin.sum_univ_three] at h
    apply Subtype.ext
    change ![l.1 0, l.1 0 + l.1 1 - l.1 0, B - (l.1 0 + l.1 1)] = l.1
    funext u
    fin_cases u
    · rfl
    · simp
    · simp
      omega
  right_inv q := by
    have h := q.2.2
    change q.1.1.val < q.1.2.val at h
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change q.1.1.val + (q.1.2.val - q.1.1.val) = q.1.2.val
      omega

def zeroTripleOfOffsets {B : ℕ} [NeZero B] (q : RingOffsets B) : ZeroMarkedTriple B := by
  have h01 : (0 : Fin B) < q.1.1 := q.2.1
  have h12 : q.1.1 < q.1.2 := q.2.2
  refine ⟨{0, q.1.1, q.1.2}, ?_, by simp⟩
  exact Finset.card_eq_three.2 ⟨0, q.1.1, q.1.2, h01.ne, (h01.trans h12).ne, h12.ne, rfl⟩

private lemma zeroTripleErase_card {B : ℕ} [NeZero B] (S : ZeroMarkedTriple B) :
    (S.1.erase 0).card = 2 := by
  rw [Finset.card_erase_of_mem S.2.2, S.2.1]

private lemma zeroTripleErase_nonempty {B : ℕ} [NeZero B] (S : ZeroMarkedTriple B) :
    (S.1.erase 0).Nonempty :=
  Finset.card_pos.mp (by rw [zeroTripleErase_card S]; decide)

def offsetsOfZeroTriple {B : ℕ} [NeZero B] (S : ZeroMarkedTriple B) : RingOffsets B := by
  let U := S.1.erase 0
  have hn : U.Nonempty := zeroTripleErase_nonempty S
  refine ⟨(U.min' hn, U.max' hn), ?_, ?_⟩
  · exact bot_lt_iff_ne_bot.mpr (Finset.mem_erase.mp (U.min'_mem hn)).1
  · exact U.min'_lt_max'_of_card (by rw [zeroTripleErase_card S]; decide)

lemma zeroTriple_erase_eq_offsets {B : ℕ} [NeZero B] (S : ZeroMarkedTriple B) :
    S.1.erase 0 = {(offsetsOfZeroTriple S).1.1, (offsetsOfZeroTriple S).1.2} := by
  have hn := zeroTripleErase_nonempty S
  change S.1.erase 0 = {(S.1.erase 0).min' hn, (S.1.erase 0).max' hn}
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.min'_mem _ _
    · exact Finset.max'_mem _ _
  · have hne : (S.1.erase 0).min' hn ≠ (S.1.erase 0).max' hn :=
      (offsetsOfZeroTriple S).2.2.ne
    rw [zeroTripleErase_card S, Finset.card_eq_two.mpr ⟨_, _, hne, rfl⟩]

def offsetsZeroTripleEquiv (B : ℕ) [NeZero B] : RingOffsets B ≃ ZeroMarkedTriple B where
  toFun := zeroTripleOfOffsets
  invFun := offsetsOfZeroTriple
  left_inv q := by
    have ha := q.2.1
    have hab := q.2.2
    have hb := ha.trans hab
    have he :
        ({0, q.1.1, q.1.2} : Finset (Fin B)).erase 0 = {q.1.1, q.1.2} := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hx, h | h⟩
        · exact (hx h).elim
        · exact h
      · rintro (rfl | rfl)
        · exact ⟨ha.ne', Or.inr (Or.inl rfl)⟩
        · exact ⟨hb.ne', Or.inr (Or.inr rfl)⟩
    have hr := zeroTripleErase_nonempty (zeroTripleOfOffsets q)
    have he' : (zeroTripleOfOffsets q).1.erase 0 = {q.1.1, q.1.2} := he
    apply Subtype.ext
    apply Prod.ext
    · change ((zeroTripleOfOffsets q).1.erase 0).min' hr = q.1.1
      rw [Finset.min'_eq_iff]
      rw [he']
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, true_and]
      rintro x (rfl | rfl)
      · exact le_rfl
      · exact hab.le
    · change ((zeroTripleOfOffsets q).1.erase 0).max' hr = q.1.2
      rw [Finset.max'_eq_iff]
      rw [he']
      simp only [Finset.mem_insert, Finset.mem_singleton, or_true, true_and]
      rintro x (rfl | rfl)
      · exact hab.le
      · exact le_rfl
  right_inv S := by
    apply Subtype.ext
    change insert 0 {(offsetsOfZeroTriple S).1.1, (offsetsOfZeroTriple S).1.2} = S.1
    rw [← zeroTriple_erase_eq_offsets, Finset.insert_erase S.2.2]

def translateTripleEquiv (B : ℕ) [NeZero B] :
    (Fin B × ZeroMarkedTriple B) ≃ MarkedTriple B where
  toFun q := by
    refine ⟨(q.1, q.2.1.map (Equiv.addRight q.1).toEmbedding), ?_, ?_⟩
    · rw [Finset.card_map]
      exact q.2.2.1
    · apply Finset.mem_map.mpr
      exact ⟨0, q.2.2.2, by simp⟩
  invFun q := by
    refine ⟨q.1.1, q.1.2.map (Equiv.addRight q.1.1).symm.toEmbedding, ?_, ?_⟩
    · rw [Finset.card_map]
      exact q.2.1
    · apply Finset.mem_map.mpr
      exact ⟨q.1.1, q.2.2, by simp⟩
  left_inv q := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change (q.2.1.map (Equiv.addRight q.1).toEmbedding).map
        (Equiv.addRight q.1).symm.toEmbedding = q.2.1
      rw [Finset.map_map]
      have h : (Equiv.addRight q.1).toEmbedding.trans
          (Equiv.addRight q.1).symm.toEmbedding = Function.Embedding.refl (Fin B) := by
        apply Function.Embedding.ext
        intro x
        exact (Equiv.addRight q.1).symm_apply_apply x
      rw [h, Finset.map_refl]
  right_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (q.1.2.map (Equiv.addRight q.1.1).symm.toEmbedding).map
        (Equiv.addRight q.1.1).toEmbedding = q.1.2
      rw [Finset.map_map]
      have h : (Equiv.addRight q.1.1).symm.toEmbedding.trans
          (Equiv.addRight q.1.1).toEmbedding = Function.Embedding.refl (Fin B) := by
        apply Function.Embedding.ext
        intro x
        exact (Equiv.addRight q.1.1).apply_symm_apply x
      rw [h, Finset.map_refl]

def markedTripleEquiv (B : ℕ) [NeZero B] : (Fin B × RingGaps B) ≃ MarkedTriple B :=
  (Equiv.prodCongr (Equiv.refl _) ((gapOffsetsEquiv B).trans (offsetsZeroTripleEquiv B))).trans
    (translateTripleEquiv B)

lemma markedTripleEquiv_apply_anchor (B : ℕ) [NeZero B] (a : Fin B) (l : RingGaps B) :
    (markedTripleEquiv B (a, l)).1.1 = a := rfl

lemma markedTripleEquiv_apply_set (B : ℕ) [NeZero B] (a : Fin B) (l : RingGaps B) :
    (markedTripleEquiv B (a, l)).1.2 =
      {a, ((gapOffsetsEquiv B l).1.1 + a), ((gapOffsetsEquiv B l).1.2 + a)} := by
  change ({0, (gapOffsetsEquiv B l).1.1, (gapOffsetsEquiv B l).1.2} : Finset (Fin B)).map
    (Equiv.addRight a).toEmbedding = _
  simp

lemma markedTripleEquiv_symm_anchor (B : ℕ) [NeZero B] (p : MarkedTriple B) :
    ((markedTripleEquiv B).symm p).1 = p.1.1 := rfl

def ringSideEmbedding (B : ℕ) (side : Bool) : Fin B ↪ Fin (2*B) where
  toFun i := ⟨2*i.val + side.toNat, by
    have := i.isLt
    cases side <;> simp <;> omega⟩
  inj' := by
    intro i j h
    have h' := congrArg Fin.val h
    dsimp only at h'
    apply Fin.ext
    omega

lemma ringSideEmbedding_sub (B : ℕ) (side : Bool) (a x : Fin B) :
    ((ringSideEmbedding B side x) - (ringSideEmbedding B side a)).val = 2 * (x - a).val := by
  rw [Fin.val_sub, Fin.val_sub]
  change (2 * B - (2 * a.val + side.toNat) + (2 * x.val + side.toNat)) % (2*B) = _
  have he : 2 * B - (2 * a.val + side.toNat) + (2 * x.val + side.toNat) =
      2 * (B - a.val + x.val) := by
    have h := a.isLt
    cases side <;> simp <;> omega
  rw [he, Nat.mul_mod_mul_left]

lemma ring_sub_even_iff (B : ℕ) (a x : Fin (2*B)) :
    (x - a).val % 2 = 0 ↔ x.val % 2 = a.val % 2 := by
  rw [Fin.val_sub, Nat.mod_mod_of_dvd _ (dvd_mul_right 2 B)]
  have h := a.isLt
  omega



abbrev RingShape (B : ℕ) := Bool × Bool × { S : Finset (Fin B) // S.card = 3 }

abbrev RingShapes (m B : ℕ) := Fin m → RingShape B

abbrev RingAnchor {B : ℕ} (q : RingShape B) := { i : Fin B // i ∈ q.2.2.1 }

abbrev ShapeAnchors {m B : ℕ} (q : RingShapes m B) := ∀ c : Fin m, RingAnchor (q c)

def paintRings {m B : ℕ} (q : RingShapes m B) : Bool × (Fin m × Fin B) → Option Bool :=
  fun (a, c, i) => if a = (q c).1 ∧ i ∈ (q c).2.2.1 then some (q c).2.1 else none

lemma paintRings_eq_some {m B : ℕ} (q : RingShapes m B)
    (a b : Bool) (c : Fin m) (i : Fin B) :
    paintRings q (a, c, i) = some b ↔
      a = (q c).1 ∧ i ∈ (q c).2.2.1 ∧ (q c).2.1 = b := by
  by_cases h : a = (q c).1 ∧ i ∈ (q c).2.2.1
  · simp [paintRings, h]
  · simp only [paintRings, h, ↓reduceIte, reduceCtorEq, false_iff]
    exact fun hp => h ⟨hp.1, hp.2.1⟩

lemma paintRings_injective {m B : ℕ} :
    Function.Injective (paintRings (m := m) (B := B)) := by
  intro q r h
  funext c
  have hn : ((q c).2.2.1).Nonempty := by
    rw [← Finset.card_pos, (q c).2.2.2]
    decide
  obtain ⟨i, hi⟩ := hn
  have pins (j : Fin B) (hj : j ∈ (q c).2.2.1) :
      (q c).1 = (r c).1 ∧ j ∈ (r c).2.2.1 ∧ (r c).2.1 = (q c).2.1 := by
    apply (paintRings_eq_some r (q c).1 (q c).2.1 c j).mp
    rw [← h]
    exact (paintRings_eq_some q (q c).1 (q c).2.1 c j).mpr ⟨rfl, hj, rfl⟩
  apply Prod.ext (pins i hi).1
  apply Prod.ext (pins i hi).2.2.symm
  apply Subtype.ext
  exact Finset.eq_of_subset_of_card_le (fun j hj => (pins j hj).2.1)
    (by rw [(q c).2.2.2, (r c).2.2.2])

def shapeMarkedTriple {B : ℕ} (q : RingShape B) (a : RingAnchor q) : MarkedTriple B :=
  ⟨(a.1, q.2.2.1), q.2.2.2, a.2⟩

def shapeGaps {m B : ℕ} [NeZero B] (q : RingShapes m B) (a : ShapeAnchors q) :
    Fin m × Fin 3 → ℕ :=
  fun (c, u) => ((markedTripleEquiv B).symm (shapeMarkedTriple (q c) (a c))).2.1 u

def shapeLengthMatch {m B : ℕ} (len : Fin m × Fin 3 → ℕ) (arc : Fin m × Fin 3 → ℕ) : Prop :=
  ∀ j : Fin (B+1), (Finset.univ.filter (fun i => arc i = j.val)).card =
    (Finset.univ.filter (fun i => len i = j.val)).card

private abbrev RingPlacements (m B : ℕ) := Fin m → (Bool × Bool) × Fin B
private abbrev GapFamilies (m B : ℕ) := Fin m → RingGaps B

private def decorateTripleEquiv (B : ℕ) :
    ((Bool × Bool) × MarkedTriple B) ≃ (Σ q : RingShape B, RingAnchor q) where
  toFun z :=
    ⟨(z.1.1, z.1.2, ⟨z.2.1.2, z.2.2.1⟩), ⟨z.2.1.1, z.2.2.2⟩⟩
  invFun z := ((z.1.1, z.1.2.1), shapeMarkedTriple z.1 z.2)
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

private def oneRingShapeEquiv (B : ℕ) [NeZero B] :
    (((Bool × Bool) × Fin B) × RingGaps B) ≃ (Σ q : RingShape B, RingAnchor q) :=
  (Equiv.prodAssoc (Bool × Bool) (Fin B) (RingGaps B)).trans
    ((Equiv.prodCongr (Equiv.refl _) (markedTripleEquiv B)).trans (decorateTripleEquiv B))

private def splitPiPairEquiv (ι A C : Type) : ((ι → A) × (ι → C)) ≃ (ι → A × C) where
  toFun z c := (z.1 c, z.2 c)
  invFun z := (fun c => (z c).1, fun c => (z c).2)
  left_inv _ := rfl
  right_inv _ := rfl

private def markRingsEquiv (m B : ℕ) :
    (Fin m → Σ q : RingShape B, RingAnchor q) ≃ (Σ q : RingShapes m B, ShapeAnchors q) where
  toFun z := ⟨fun c => (z c).1, fun c => (z c).2⟩
  invFun z c := ⟨z.1 c, z.2 c⟩
  left_inv z := by
    funext c
    change Sigma.mk (z c).1 (z c).2 = z c
    cases z c
    rfl
  right_inv z := by cases z; rfl

private def shapeAssemblyEquiv (m B : ℕ) [NeZero B] :
    (RingPlacements m B × GapFamilies m B) ≃ (Σ q : RingShapes m B, ShapeAnchors q) :=
  (splitPiPairEquiv _ _ _).trans
    ((Equiv.piCongrRight (fun _ => oneRingShapeEquiv B)).trans (markRingsEquiv m B))

private lemma shapeAssembly_gap (m B : ℕ) [NeZero B]
    (z : RingPlacements m B × GapFamilies m B) :
    shapeGaps (shapeAssemblyEquiv m B z).1 (shapeAssemblyEquiv m B z).2 =
      fun (c, u) => (z.2 c).1 u := by
  funext i
  rcases i with ⟨c, u⟩
  change ((markedTripleEquiv B).symm
    (markedTripleEquiv B ((z.1 c).2, z.2 c))).2.1 u = (z.2 c).1 u
  rw [Equiv.symm_apply_apply]

private lemma ringGaps_le {B : ℕ} (g : RingGaps B) (u : Fin 3) : g.1 u ≤ B := by
  calc
    g.1 u ≤ ∑ j : Fin 3, g.1 j :=
      Finset.single_le_sum (f := g.1) (fun j _ => Nat.zero_le (g.1 j)) (Finset.mem_univ u)
    _ = B := g.2.2

private def profileGapsEquiv {m B : ℕ} (len : Fin m × Fin 3 → ℕ) :
    LengthProfile m B len ≃
      { g : GapFamilies m B // shapeLengthMatch (B := B) len
        (fun (c, u) => (g c).1 u) } where
  toFun l := ⟨fun c => ⟨fun u => (l.1 (c, u)).val, fun u => l.2.1 (c, u), l.2.2.1 c⟩, l.2.2.2⟩
  invFun g :=
    ⟨fun (c, u) => ⟨(g.1 c).1 u, Nat.lt_succ_of_le (ringGaps_le (g.1 c) u)⟩,
      fun (c, u) => (g.1 c).2.1 u, fun c => (g.1 c).2.2, g.2⟩
  left_inv l := by
    apply Subtype.ext
    funext i
    rcases i with ⟨c, u⟩
    exact Fin.ext rfl
  right_inv g := by
    apply Subtype.ext
    funext c
    apply Subtype.ext
    rfl

private def prodAttachRightEquiv (P A : Type) (q : A → Prop) :
    P × { a // q a } ≃ { z : P × A // q z.2 } where
  toFun z := ⟨(z.1, z.2.1), z.2.2⟩
  invFun z := (z.1.1, ⟨z.1.2, z.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

private def markedGoodShapeEquiv {m B : ℕ} [NeZero B] (len : Fin m × Fin 3 → ℕ)
    (good : Finset (Bool × (Fin m × Fin B) → Option Bool))
    (hchar : ∀ (q : RingShapes m B) (a : ShapeAnchors q),
      paintRings q ∈ good ↔ shapeLengthMatch (B := B) len (shapeGaps q a)) :
    (RingPlacements m B × LengthProfile m B len) ≃
      (Σ q : { q : RingShapes m B // paintRings q ∈ good }, ShapeAnchors q.1) := by
  let C (g : GapFamilies m B) := shapeLengthMatch (B := B) len (fun (c, u) => (g c).1 u)
  let e := shapeAssemblyEquiv m B
  have h (z : RingPlacements m B × GapFamilies m B) :
      C z.2 ↔ paintRings (e z).1 ∈ good := by
    rw [hchar (e z).1 (e z).2]
    change C z.2 ↔ shapeLengthMatch (B := B) len
      (shapeGaps (shapeAssemblyEquiv m B z).1 (shapeAssemblyEquiv m B z).2)
    rw [shapeAssembly_gap]
  exact (Equiv.prodCongr (Equiv.refl _) (profileGapsEquiv len)).trans
    ((prodAttachRightEquiv _ _ C).trans ((e.subtypeEquiv h).trans
      (Equiv.subtypeSigmaEquiv ShapeAnchors (fun q => paintRings q ∈ good))))

private lemma card_shapeAnchors {m B : ℕ} (q : RingShapes m B) :
    Nat.card (ShapeAnchors q) = 3^m := by
  rw [Nat.card_pi]
  have h (c : Fin m) : Nat.card (RingAnchor (q c)) = 3 := by
    change Nat.card ↥((q c).2.2.1) = 3
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, (q c).2.2.2]
  simp only [h]
  simp

private lemma card_physical_good_shapes {m B : ℕ}
    (good : Finset (Bool × (Fin m × Fin B) → Option Bool))
    (hshape : ∀ p ∈ good, ∃ q : RingShapes m B, paintRings q = p) :
    Nat.card { q : RingShapes m B // paintRings q ∈ good } = good.card := by
  let f : { q : RingShapes m B // paintRings q ∈ good } → ↥good :=
    fun q => ⟨paintRings q.1, q.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro q r hqr
      exact Subtype.ext (paintRings_injective (congrArg Subtype.val hqr))
    · intro p
      obtain ⟨q, hq⟩ := hshape p.1 p.2
      have hqg : paintRings q ∈ good := by rw [hq]; exact p.2
      exact ⟨⟨q, hqg⟩, Subtype.ext hq⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_coe]

private lemma card_ringPlacements (m B : ℕ) :
    Nat.card (RingPlacements m B) = (4*B)^m := by
  rw [Nat.card_fun]
  norm_num [Nat.card_prod, Nat.card_eq_fintype_card]

private lemma card_marked_good_shapes {m B : ℕ} [NeZero B]
    (len : Fin m × Fin 3 → ℕ)
    (good : Finset (Bool × (Fin m × Fin B) → Option Bool))
    (hshape : ∀ p ∈ good, ∃ q : RingShapes m B, paintRings q = p)
    (hchar : ∀ (q : RingShapes m B) (a : ShapeAnchors q),
      paintRings q ∈ good ↔ shapeLengthMatch (B := B) len (shapeGaps q a)) :
    3^m * good.card = (4*B)^m * Nat.card (LengthProfile m B len) := by
  classical
  calc
    3^m * good.card =
        Nat.card (Σ q : { q : RingShapes m B // paintRings q ∈ good }, ShapeAnchors q.1) := by
      rw [Nat.card_sigma]
      simp only [card_shapeAnchors]
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
        card_physical_good_shapes good hshape, Nat.mul_comm]
    _ = Nat.card (RingPlacements m B × LengthProfile m B len) :=
      Nat.card_congr (markedGoodShapeEquiv len good hchar).symm
    _ = (4*B)^m * Nat.card (LengthProfile m B len) := by
      rw [Nat.card_prod, card_ringPlacements]

lemma count_physical_patterns_from_gaps {m B : ℕ} [NeZero B]
    (len : Fin m × Fin 3 → ℕ) (hpos : ∀ i, 0 < len i) (hle : ∀ i, len i ≤ B)
    (good : Finset (Bool × (Fin m × Fin B) → Option Bool))
    (hshape : ∀ p ∈ good, ∃ q : RingShapes m B, paintRings q = p)
    (hchar : ∀ (q : RingShapes m B) (a : ShapeAnchors q),
      paintRings q ∈ good ↔ shapeLengthMatch (B := B) len (shapeGaps q a)) :
    let slots := (Finset.univ : Finset (Equiv.Perm (Fin m × Fin 3))).filter (fun π =>
      ∀ c : Fin m, (∑ u : Fin 3, len (π (c, u))) = B)
    let copies := ∏ j : Fin (B+1), ((Finset.univ.filter (fun i => len i = j.val)).card).factorial
    (good.Nonempty ↔ slots.Nonempty) ∧ 3^m * copies * good.card = (4*B)^m * slots.card := by
  intro slots copies
  have hs : slots.card = copies * Nat.card (LengthProfile m B len) :=
    card_slots_profiles_finset len hpos hle
  have hm := card_marked_good_shapes len good hshape hchar
  have h3 : 0 < 3^m := by positivity
  have h4 : 0 < (4*B)^m := by have := NeZero.pos B; positivity
  have hc : 0 < copies := by
    apply Finset.prod_pos
    intro j _
    exact Nat.factorial_pos _
  constructor
  · calc
      good.Nonempty ↔ 0 < good.card := Finset.card_pos.symm
      _ ↔ 0 < 3^m * good.card := (Nat.mul_pos_iff_of_pos_left h3).symm
      _ ↔ 0 < slots.card := by rw [hm, hs, Nat.mul_pos_iff_of_pos_left h4, Nat.mul_pos_iff_of_pos_left hc]
      _ ↔ slots.Nonempty := Finset.card_pos
  · calc
      3^m * copies * good.card = copies * (3^m * good.card) := by ring
      _ = (4*B)^m * slots.card := by rw [hm, hs]; ring



private theorem cycleSum_triple_last {b : ℕ} (d e : Fin (b+1))
    (hde : d < e) (he : e < Fin.last b) (z : ℚ) :
    cycleSum {d, e, Fin.last b} z =
      (1 + z ^ (d.val+1)) * (1 + z ^ (e.val - d.val)) * (1 + z ^ (b - e.val)) := by
  classical
  let Q : Finset (Fin (b+1)) := {d, e, Fin.last b}
  have hdQ : d ∈ Q := by simp [Q]
  have heQ : e ∈ Q := by simp [Q]
  have hlQ : Fin.last b ∈ Q := by simp [Q]
  let sd : ↥Q := ⟨d, hdQ⟩
  let se : ↥Q := ⟨e, heQ⟩
  let sl : ↥Q := ⟨Fin.last b, hlQ⟩
  have hstop (i : Fin (b+1)) :
      (nextStop Q hlQ i).1 = if i ≤ d then d else if i ≤ e then e else Fin.last b := by
    have hlo := le_nextStop Q hlQ i
    have hmem := (nextStop Q hlQ i).2
    change (nextStop Q hlQ i).1 ∈ ({d, e, Fin.last b} : Finset (Fin (b+1))) at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    split_ifs with hd hi
    · have hhi := nextStop_le Q hlQ hd hdQ
      simp only [Fin.le_def, Fin.lt_def, Fin.ext_iff] at *
      omega
    · have hhi := nextStop_le Q hlQ hi heQ
      simp only [Fin.le_def, Fin.lt_def, Fin.ext_iff] at *
      omega
    · simp only [Fin.le_def, Fin.lt_def, Fin.ext_iff] at *
      omega
  have hf₀ : Finset.univ.filter (fun i => nextStop Q hlQ i = sd) = Finset.Iic d := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic, Subtype.ext_iff, hstop]
    change ((if i ≤ d then d else if i ≤ e then e else Fin.last b) = d) ↔ i ≤ d
    split_ifs <;> constructor <;> intro hh <;>
      simp only [Fin.le_def, Fin.lt_def, Fin.ext_iff, Fin.val_last] at * <;> omega
  have hf₁ : Finset.univ.filter (fun i => nextStop Q hlQ i = se) = Finset.Ioc d e := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioc, Subtype.ext_iff, hstop]
    change ((if i ≤ d then d else if i ≤ e then e else Fin.last b) = e) ↔ d < i ∧ i ≤ e
    split_ifs <;> constructor <;> intro hh <;>
      simp only [Fin.le_def, Fin.lt_def, Fin.ext_iff, Fin.val_last] at * <;> omega
  have hf₂ : Finset.univ.filter (fun i => nextStop Q hlQ i = sl) = Finset.Ioc e (Fin.last b) := by
    ext i
    have hil := Fin.le_last i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioc, Subtype.ext_iff, hstop]
    change ((if i ≤ d then d else if i ≤ e then e else Fin.last b) = Fin.last b) ↔ e < i ∧ i ≤ Fin.last b
    split_ifs <;> constructor <;> intro hh <;>
      simp only [Fin.le_def, Fin.lt_def, Fin.ext_iff, Fin.val_last] at * <;> omega
  have hg₀ : gapSize Q hlQ sd = d.val + 1 := by rw [gapSize, hf₀, Fin.card_Iic]
  have hg₁ : gapSize Q hlQ se = e.val - d.val := by rw [gapSize, hf₁, Fin.card_Ioc]
  have hg₂ : gapSize Q hlQ sl = b - e.val := by rw [gapSize, hf₂, Fin.card_Ioc]; rfl
  let f : Fin 3 → ↥Q := ![sd, se, sl]
  have hinj : Function.Injective f := by
    intro i j h
    have hval := congrArg Subtype.val h
    have hdl : d < Fin.last b := hde.trans he
    fin_cases i <;> fin_cases j <;>
      simp_all [f, sd, se, sl, hde.ne, hde.ne', hdl.ne, hdl.ne', he.ne, he.ne']
  have hsurj : Function.Surjective f := by
    intro j
    have h := j.2
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · exact ⟨0, Subtype.ext h.symm⟩
    · exact ⟨1, Subtype.ext h.symm⟩
    · exact ⟨2, Subtype.ext h.symm⟩
  let eqv : Fin 3 ≃ ↥Q := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hp := (Equiv.prod_comp eqv (fun a => 1 + z ^ gapSize Q hlQ a)).symm
  change cycleSum Q z = _
  rw [cycleSum_product Q hlQ, hp, Fin.prod_univ_three]
  change (1 + z ^ gapSize Q hlQ sd) * (1 + z ^ gapSize Q hlQ se) *
    (1 + z ^ gapSize Q hlQ sl) = _
  rw [hg₀, hg₁, hg₂]

lemma cycleSum_markedTriple {b : ℕ} (p : MarkedTriple (b+1)) (z : ℚ) :
    cycleSum p.1.2 z = ∏ u : Fin 3, (1 + z ^ ((markedTripleEquiv (b+1)).symm p).2.1 u) := by
  obtain ⟨⟨a, g⟩, rfl⟩ := (markedTripleEquiv (b+1)).surjective p
  rw [Equiv.symm_apply_apply]
  let d := (gapOffsetsEquiv (b+1) g).1.1
  let e := (gapOffsetsEquiv (b+1) g).1.2
  have hd : 0 < d := (gapOffsetsEquiv (b+1) g).2.1
  have hde : d < e := (gapOffsetsEquiv (b+1) g).2.2
  have he : 0 < e := hd.trans hde
  have hlast : Fin.last b = -(1 : Fin (b+1)) := by rw [← Fin.neg_last b, neg_neg]
  let k := Fin.last b - a
  have hk : a + k = Fin.last b := by dsimp [k]; abel
  have hshift (i : Fin (b+1)) : i + a + k = i - 1 := by rw [add_assoc, hk, hlast, sub_eq_add_neg]
  have hdv : (d - 1).val = d.val - 1 := Fin.val_sub_one_of_ne_zero hd.ne'
  have hev : (e - 1).val = e.val - 1 := Fin.val_sub_one_of_ne_zero he.ne'
  have hda : d.val = g.1 0 := rfl
  have hea : e.val = g.1 0 + g.1 1 := rfl
  have hsum := g.2.2
  rw [Fin.sum_univ_three] at hsum
  have ht : ((markedTripleEquiv (b+1) (a,g)).1.2.map (Equiv.addRight k).toEmbedding) =
      {d-1, e-1, Fin.last b} := by
    rw [markedTripleEquiv_apply_set]
    change ({a, d+a, e+a} : Finset (Fin (b+1))).map (Equiv.addRight k).toEmbedding = _
    simp only [Finset.map_insert, Finset.map_singleton, Equiv.toEmbedding_apply]
    change ({a+k, d+a+k, e+a+k} : Finset (Fin (b+1))) = _
    rw [hk, hshift d, hshift e]
    ext i
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  have h' : d - 1 < e - 1 := by
    simp only [Fin.lt_def, Fin.val_zero] at hd hde ⊢
    omega
  have h'' : e - 1 < Fin.last b := by
    simp only [Fin.lt_def, Fin.val_last]
    rw [hev]
    have h := e.isLt
    simp only [Fin.lt_def, Fin.val_zero] at he
    omega
  rw [← cycleSum_translate _ k z, ht, cycleSum_triple_last _ _ h' h'', Fin.prod_univ_three]
  have heq₀ : (d-1).val + 1 = g.1 0 := by
    rw [hdv, hda]
    have h := g.2.1 0
    omega
  have heq₁ : (e-1).val - (d-1).val = g.1 1 := by
    rw [hev, hdv, hea, hda]
    have h := g.2.1 0
    omega
  have heq₂ : b - (e-1).val = g.1 2 := by
    rw [hev, hea]
    have h := g.2.1 0
    omega
  rw [heq₀, heq₁, heq₂]

lemma cycleSum_shapeGaps {m b : ℕ} (q : RingShapes m (b+1))
    (a : ShapeAnchors q) (c : Fin m) (z : ℚ) :
    cycleSum (q c).2.2.1 z = ∏ u : Fin 3, (1 + z ^ shapeGaps q a (c,u)) :=
  cycleSum_markedTriple (shapeMarkedTriple (q c) (a c)) z


lemma shapeLengthMatch_iff_spectrum {m B : ℕ} (len arc : Fin m × Fin 3 → ℕ)
    (hl : ∀ i, len i ≤ B) (ha : ∀ i, arc i ≤ B) :
    shapeLengthMatch (B := B) len arc ↔ spectrum arc = spectrum len := by
  rw [Multiset.ext]
  simp only [spectrum_count]
  constructor
  · intro h j
    by_cases hj : j ≤ B
    · exact h ⟨j, Nat.lt_succ_of_le hj⟩
    · have hz (f : Fin m × Fin 3 → ℕ) (hf : ∀ i, f i ≤ B) :
          (Finset.univ.filter (fun i => f i = j)).card = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.filter_eq_empty_iff.mpr
        exact fun i _ he => hj (he ▸ hf i)
      rw [hz arc ha, hz len hl]
  · exact fun h j => h j.val

lemma shapeGaps_pos_le {m B : ℕ} [NeZero B] (q : RingShapes m B) (a : ShapeAnchors q) :
    ∀ i, 0 < shapeGaps q a i ∧ shapeGaps q a i ≤ B := by
  rintro ⟨c,u⟩
  let g := ((markedTripleEquiv B).symm (shapeMarkedTriple (q c) (a c))).2
  change 0 < g.1 u ∧ g.1 u ≤ B
  refine ⟨g.2.1 u, ?_⟩
  calc
    g.1 u ≤ ∑ j : Fin 3, g.1 j :=
      Finset.single_le_sum (f := g.1) (fun j _ => Nat.zero_le (g.1 j)) (Finset.mem_univ u)
    _ = B := g.2.2

lemma pullback_paintRings {m b : ℕ} (q : RingShapes m (b+1)) :
    pullback (targetEquiv m b) (paintRings q) =
      ringAssemble (fun _ => b) (fun c => paintRing (q c).1 (q c).2.1 (q c).2.2.1) := by
  rfl

lemma transform_paintRings {m b : ℕ} (q : RingShapes m (b+1)) (a : ShapeAnchors q) (u v : ℚ) :
    transform (m*(b+1)) (lawG (m*(b+1)) targetNext (paintRings q)) u v =
      ∏ i : Fin m × Fin 3, (1 + (u*v) ^ shapeGaps q a i) := by
  have hk : ∑ _ : Fin m, (b+1) = m*(b+1) := by simp
  rw [← target_law_pullback, pullback_paintRings, transform_paints (fun _ => b) hk,
    Fintype.prod_prod_type]
  exact Finset.prod_congr rfl (fun c _ => cycleSum_shapeGaps q a c (u*v))

lemma norm_painted_iff_lengths {m b : ℕ} (s : Fin m × Fin 3 → ℕ)
    (hs : ∑ i, (s i+1) = m*(b+1)) (hle : ∀ i, s i+1 ≤ b+1)
    (q : RingShapes m (b+1)) (a : ShapeAnchors q) :
    lawG (m*(b+1)) targetNext (paintRings q) =
      lawG (m*(b+1)) (sigmaNext s) (sourcePins s) ↔
    shapeLengthMatch (B := b+1) (fun i => s i+1) (shapeGaps q a) := by
  rw [shapeLengthMatch_iff_spectrum _ _ hle (fun i => (shapeGaps_pos_le q a i).2)]
  constructor
  · intro h
    apply eq_of_plus_factors
    · intro e he
      obtain ⟨i,rfl⟩ := (mem_spectrum _ _).1 he
      exact (shapeGaps_pos_le q a i).1
    · intro e he
      obtain ⟨i,rfl⟩ := (mem_spectrum _ _).1 he
      omega
    · intro z
      rw [spectrum_prod, spectrum_prod]
      have hz := congrFun (congrFun (congrArg (transform (m*(b+1))) h) z) 1
      rw [transform_paintRings q a, source_transform s hs, mul_one] at hz
      exact hz
  · intro h
    apply transform_injective
    intro u v _ _ _ _
    rw [transform_paintRings q a, source_transform s hs, ← spectrum_prod, ← spectrum_prod, h]

lemma shape_of_histEq {m b : ℕ} (s : Fin m × Fin 3 → ℕ)
    (hs : ∑ i, (s i+1) = m*(b+1))
    (hsize : ∀ i, b+1 < 4*(s i+1) ∧ 2*(s i+1) < b+1)
    (p : Bool × (Fin m × Fin (b+1)) → Option Bool)
    (hp : histG (m*(b+1)) targetNext p = histG (m*(b+1)) (sigmaNext s) (sourcePins s)) :
    ∃ q : RingShapes m (b+1), paintRings q = p := by
  have h := (target_law_pullback p).trans ((target_norm_iff_hist s hs hsize p).2 hp)
  obtain ⟨a,bit,Q,hc,hp'⟩ := targets_have_three_pins s hs hsize _ h
  let q : RingShapes m (b+1) := fun c => (a c,bit c,⟨Q c,hc c⟩)
  refine ⟨q, ?_⟩
  funext v
  rcases v with ⟨d,c,j⟩
  exact (congrFun hp' (d,⟨c,j⟩)).symm

def recordedSource {m b : ℕ} (s : Fin m × Fin 3 → ℕ)
    (d : Fin (m*(b+1)+1) × Fin (m*(b+1)+1)) : ℕ :=
  let K := Fin m × Fin 3
  let I := (i : K) × Fin (s i+1)
  ((Finset.univ : Finset ((Bool × I) → Bool)).filter (fun x =>
    (∀ i : K, x (false,(⟨i,0⟩ : I)) = false) ∧
    (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,i))).card = d.1.val ∧
    (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,(⟨i.1,i.2+1⟩ : I)))).card = d.2.val)).card

def recordedTarget {m b : ℕ} (p : Bool × (Fin m × Fin (b+1)) → Option Bool)
    (d : Fin (m*(b+1)+1) × Fin (m*(b+1)+1)) : ℕ :=
  let T := Fin m × Fin (b+1)
  ((Finset.univ : Finset ((Bool × T) → Bool)).filter (fun x =>
    (∀ v, p v = none ∨ p v = some (x v)) ∧
    (Finset.univ.filter (fun i : T => x (false,i) ≠ x (true,i))).card = d.1.val ∧
    (Finset.univ.filter (fun i : T => x (false,i) ≠ x (true,(i.1,i.2+1)))).card = d.2.val)).card

lemma recordedSource_eq {m b : ℕ} (s : Fin m × Fin 3 → ℕ) :
    recordedSource (b := b) s = histG (m*(b+1)) (sigmaNext s) (sourcePins s) := by
  funext d
  unfold recordedSource histG
  dsimp only
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, fits_sourcePins, diff, sigmaNext, id_eq]
  rfl

lemma recordedTarget_eq {m b : ℕ} (p : Bool × (Fin m × Fin (b+1)) → Option Bool) :
    recordedTarget p = histG (m*(b+1)) targetNext p := by
  funext d
  unfold recordedTarget histG
  dsimp only
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, fits, diff, targetNext, id_eq]
  rfl

lemma result {m b : ℕ} (s : Fin m × Fin 3 → ℕ)
    (hs : ∑ i, (s i+1) = m*(b+1))
    (hsize : ∀ i, b+1 < 4*(s i+1) ∧ 2*(s i+1) < b+1) :
    let K := Fin m × Fin 3
    let len := fun i : K => s i+1
    let source := recordedSource (b := b) s
    let hist := recordedTarget (m := m) (b := b)
    let good := Finset.univ.filter (fun p => hist p = source)
    let slots := (Finset.univ : Finset (Equiv.Perm K)).filter (fun π =>
      ∀ c : Fin m, (∑ u : Fin 3, len (π (c,u))) = b+1)
    let copies := ∏ j : Fin ((b+1)+1), ((Finset.univ : Finset K).filter (fun i => len i = j.val)).card.factorial
    (∀ p, (∀ d, hist p d * 2^(2*m*(b+1)-3*m) = source d * 2^((Finset.univ.filter (fun v => p v = none)).card)) ↔ p ∈ good) ∧
      (good.Nonempty ↔ slots.Nonempty) ∧
      3^m * copies * good.card = (4*(b+1))^m * slots.card := by
  intro K len source hist good slots copies
  have good_iff (p : Bool × (Fin m × Fin (b+1)) → Option Bool) :
      p ∈ good ↔ histG (m*(b+1)) targetNext p = histG (m*(b+1)) (sigmaNext s) (sourcePins s) := by
    exact (show p ∈ Finset.univ.filter (fun p => recordedTarget p = recordedSource (b := b) s) ↔ _ by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, recordedTarget_eq, recordedSource_eq])
  constructor
  · intro p
    rw [good_iff, ← target_norm_iff_hist s hs hsize p, law_eq_iff_cross, source_freeCount_closed s hs]
    change (∀ d, recordedTarget p d * _ = recordedSource (b := b) s d * _) ↔ _
    simp only [recordedTarget_eq, recordedSource_eq, freeCount]
  · have hpos (i : K) : 0 < len i := by dsimp [len]; omega
    have hle (i : K) : len i ≤ b+1 := by have := (hsize i).2; dsimp [len]; omega
    have hshape (p : Bool × (Fin m × Fin (b+1)) → Option Bool) (hp : p ∈ good) :
        ∃ q : RingShapes m (b+1), paintRings q = p :=
      shape_of_histEq s hs hsize p ((good_iff p).1 hp)
    have hchar (q : RingShapes m (b+1)) (a : ShapeAnchors q) :
        paintRings q ∈ good ↔ shapeLengthMatch (B := b+1) len (shapeGaps q a) := by
      rw [good_iff, ← target_norm_iff_hist s hs hsize (paintRings q)]
      exact norm_painted_iff_lengths s hs hle q a
    exact count_physical_patterns_from_gaps len hpos hle good hshape hchar

end PEqualNP.Outside.L_pcx_384

theorem PEqualNP.Outside.L_pcx_384 : ∀ (t b : ℕ) (s : (Fin (t+1) × Fin 3) → ℕ),
  let m := t+1
  let B := b+1
  let K := Fin m × Fin 3
  let len := fun i : K => s i + 1
  (∑ i : K, len i) = m*B → (∀ i, B < 4*len i ∧ 2*len i < B) →
  let I := (i : K) × Fin (s i+1)
  let T := Fin m × Fin B
  let J := Fin (m*B+1)
  let source := fun (d : J × J) =>
    ((Finset.univ : Finset ((Bool × I) → Bool)).filter (fun x =>
      (∀ i : K, x (false,(⟨i,0⟩ : I)) = false) ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,i))).card = d.1.val ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,(⟨i.1,i.2+1⟩ : I)))).card = d.2.val)).card
  let hist := fun (p : Bool × T → Option Bool) (d : J × J) =>
    ((Finset.univ : Finset ((Bool × T) → Bool)).filter (fun x =>
      (∀ v, p v = none ∨ p v = some (x v)) ∧
      (Finset.univ.filter (fun i : T => x (false,i) ≠ x (true,i))).card = d.1.val ∧
      (Finset.univ.filter (fun i : T => x (false,i) ≠ x (true,(i.1,i.2+1)))).card = d.2.val)).card
  let good := Finset.univ.filter (fun p => hist p = source)
  let slots := (Finset.univ : Finset (Equiv.Perm K)).filter (fun π =>
    ∀ c : Fin m, (∑ u : Fin 3, len (π (c,u))) = B)
  let copies := ∏ j : Fin (B+1), ((Finset.univ : Finset K).filter (fun i => len i = j.val)).card.factorial
  (∀ p, (∀ d, hist p d * 2^(2*m*B-3*m) =
    source d * 2^((Finset.univ.filter (fun v => p v = none)).card)) ↔ p ∈ good) ∧
    (good.Nonempty ↔ slots.Nonempty) ∧
    3^m * copies * good.card = (4*B)^m * slots.card := by
  intro t b s m B K len hs hsize
  exact PEqualNP.Outside.L_pcx_384.result (b := b) s hs hsize
