import Mathlib

namespace PEqualNP.Outside.L_pcx_378_aux

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


-- Section 2: Fin (2 * (t + 1)) coordinates and arc decomposition

instance instNeZeroTwoMulSucc (t : ℕ) : NeZero (2 * (t + 1)) := ⟨by omega⟩

lemma fin_one_val (t : ℕ) : (1 : Fin (2 * (t + 1))).val = 1 := by
  change 1 % (2 * (t + 1)) = 1
  exact Nat.mod_eq_of_lt (by omega)

lemma ofNat_fin_eq {t : ℕ} (r : ℕ) (hr : r < 2 * (t + 1)) :
    Fin.ofNat (2 * (t + 1)) r = ⟨r, hr⟩ :=
  Fin.ext (Nat.mod_eq_of_lt hr)

lemma ofNat_fin_add {t : ℕ} (a b : ℕ) :
    Fin.ofNat (2 * (t + 1)) (a + b) = Fin.ofNat (2 * (t + 1)) a + Fin.ofNat (2 * (t + 1)) b := by
  apply Fin.ext
  change (a + b) % (2 * (t + 1)) = (a % (2 * (t + 1)) + b % (2 * (t + 1))) % (2 * (t + 1))
  exact Nat.add_mod a b (2 * (t + 1))

lemma ofNat_fin_one {t : ℕ} : Fin.ofNat (2 * (t + 1)) 1 = (1 : Fin (2 * (t + 1))) := rfl

lemma ofNat_fin_val_self {t : ℕ} (x : Fin (2 * (t + 1))) :
    Fin.ofNat (2 * (t + 1)) x.val = x :=
  ofNat_fin_eq x.val x.isLt

lemma fin_add_three_eq {t : ℕ} (a b c d : Fin (2 * (t + 1)))
    (h : a.val + b.val + c.val = d.val) : a + b + c = d := by
  have hd : d.val < 2 * (t + 1) := d.isLt
  have h1 : (a + b).val = a.val + b.val := by
    rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
  apply Fin.ext
  rw [Fin.val_add, h1, Nat.mod_eq_of_lt (by omega)]
  exact h

def edgeEquiv (t : ℕ) : Fin (2 * (t + 1)) ≃ Bool × Fin (t + 1) where
  toFun k := (decide (k.val % 2 = 1), ⟨k.val / 2, by omega⟩)
  invFun e := ⟨2 * e.2.val + if e.1 then 1 else 0, by cases e.1 <;> simp <;> omega⟩
  left_inv k := by
    apply Fin.ext
    dsimp only
    by_cases h : k.val % 2 = 1
    · simp [h]; omega
    · simp [h]; omega
  right_inv e := by
    rcases e with ⟨b, i⟩
    cases b <;> ext <;> simp <;> omega

lemma edgeEquiv_add_one (t : ℕ) (k : Fin (2 * (t + 1))) :
    edgeEquiv t (k + 1) = nextE (ringPerm t) (edgeEquiv t k) := by
  have h1 : (1 : Fin (2 * (t + 1))).val = 1 := fin_one_val t
  have hval : (k + 1).val = (k.val + 1) % (2 * (t + 1)) := by
    rw [Fin.val_add, h1]
  have hlt : k.val < 2 * (t + 1) := k.isLt
  by_cases hlast : k.val + 1 = 2 * (t + 1)
  · have hmod : (k + 1).val = 0 := by rw [hval, hlast, Nat.mod_self]
    have hodd : k.val % 2 = 1 := by omega
    have hdiv : k.val / 2 = t := by omega
    apply Prod.ext
    · simp [edgeEquiv, nextE, hmod, hodd]
    · apply Fin.ext
      simp only [edgeEquiv, nextE, ringPerm, Equiv.coe_fn_mk, hmod, hodd, ↓reduceIte, decide_true]
      have : (⟨k.val / 2, by omega⟩ + 1 : Fin (t + 1)).val = (t + 1) % (t + 1) := by
        rw [Fin.val_add]
        simp only [hdiv]
        by_cases ht : t = 0
        · subst ht; simp
        · have h1' : (1 : Fin (t + 1)).val = 1 := by
            change 1 % (t + 1) = 1; exact Nat.mod_eq_of_lt (by omega)
          rw [h1']
      rw [this, Nat.mod_self]
  · have hmod : (k + 1).val = k.val + 1 := by
      rw [hval, Nat.mod_eq_of_lt (by omega)]
    by_cases hodd : k.val % 2 = 1
    · have hev : (k + 1).val % 2 = 0 := by omega
      have hdiv : (k + 1).val / 2 = k.val / 2 + 1 := by omega
      apply Prod.ext
      · simp [edgeEquiv, nextE, hodd, hev]
      · apply Fin.ext
        simp only [edgeEquiv, nextE, ringPerm, Equiv.coe_fn_mk, hodd, ↓reduceIte, decide_true]
        rw [hdiv, Fin.val_add]
        have hlt2 : k.val / 2 + 1 < t + 1 := by omega
        have h1' : (1 : Fin (t + 1)).val = 1 := by
          change 1 % (t + 1) = 1; exact Nat.mod_eq_of_lt (by omega)
        simp only [h1', Nat.mod_eq_of_lt hlt2]
    · have hodd2 : (k + 1).val % 2 = 1 := by omega
      have hdiv : (k + 1).val / 2 = k.val / 2 := by omega
      apply Prod.ext
      · simp [edgeEquiv, nextE, hodd, hodd2]
      · apply Fin.ext
        simp [edgeEquiv, nextE, hodd, hdiv]

lemma edgeEquiv_sub_one (t : ℕ) (k : Fin (2 * (t + 1))) :
    edgeEquiv t (k - 1) = (nextE (ringPerm t)).symm (edgeEquiv t k) := by
  apply (nextE (ringPerm t)).injective
  rw [Equiv.apply_symm_apply, ← edgeEquiv_add_one, sub_add_cancel]

def pinEquiv (t : ℕ) : (Bool × Fin (t + 1) → Option Bool) ≃ (Fin (2 * (t + 1)) → Option Bool) where
  toFun p k := qE (ringPerm t) p (edgeEquiv t k)
  invFun q v := q ((edgeEquiv t).symm ((headV (ringPerm t)).symm v))
  left_inv p := by
    funext v
    simp [qE]
  right_inv q := by
    funext k
    simp [qE]

def epsQ {N : ℕ} (q : Fin N → Option Bool) (k : Fin N) : ℚ :=
  match q k with
  | none => 1
  | some b => sgn b

lemma epsQ_sq {N : ℕ} (q : Fin N → Option Bool) (k : Fin N) :
    epsQ q k * epsQ q k = 1 := by
  unfold epsQ
  cases q k with
  | none => simp
  | some b => exact sgn_mul_self b

def edgeWQ (t : ℕ) (q : Fin (2 * (t + 1)) → Option Bool) (u v : ℚ)
    (k : Fin (2 * (t + 1))) : ℚ :=
  (if k.val % 2 = 1 then v else u) * epsQ q k * epsQ q (k - 1)

def polyQ (t : ℕ) (q : Fin (2 * (t + 1)) → Option Bool) (u v : ℚ) : ℚ :=
  ∑ S ∈ Finset.univ.filter (fun S : Fin (2 * (t + 1)) → Bool =>
      ∀ k, q k = none → S (k + 1) = S k),
    ∏ k : Fin (2 * (t + 1)), if S k then edgeWQ t q u v k else 1

lemma polyDef_eq_polyQ (t : ℕ) (p : Bool × Fin (t + 1) → Option Bool) (u v : ℚ) :
    polyDef (t + 1) (ringPerm t) p u v = polyQ t (pinEquiv t p) u v := by
  rw [polyDef_eq_edgeSum]
  unfold polyQ
  refine Finset.sum_bij (fun S _ => fun k => S (edgeEquiv t k)) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    intro k hk
    rw [edgeEquiv_add_one]
    exact hS (edgeEquiv t k) hk
  · intro S₁ _ S₂ _ h
    funext e
    have := congrFun h ((edgeEquiv t).symm e)
    simpa using this
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    refine ⟨fun e => T ((edgeEquiv t).symm e), ?_, by funext k; simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro e he
    have hk : pinEquiv t p ((edgeEquiv t).symm e) = none := by simpa [pinEquiv] using he
    have h1 := hT ((edgeEquiv t).symm e) hk
    have h2 : (edgeEquiv t).symm (nextE (ringPerm t) e) = (edgeEquiv t).symm e + 1 := by
      apply (edgeEquiv t).injective
      rw [Equiv.apply_symm_apply, edgeEquiv_add_one, Equiv.apply_symm_apply]
    rw [h2, h1]
  · intro S _
    symm
    refine Fintype.prod_equiv (edgeEquiv t) _ _ (fun k => ?_)
    cases hS : S (edgeEquiv t k)
    · simp [hS]
    · simp only [hS, ↓reduceIte, edgeWQ, edgeW, epsQ, epsE, epsV, pinEquiv, qE,
        Equiv.coe_fn_mk, ← edgeEquiv_sub_one]
      have hb : (edgeEquiv t k).1 = decide (k.val % 2 = 1) := rfl
      by_cases h : k.val % 2 = 1 <;> simp [hb, h]

def pinCount (t : ℕ) (q : Fin (2 * (t + 1)) → Option Bool) : ℕ :=
  (Finset.univ.filter (fun k => q k ≠ none)).card

lemma freeCount_pinEquiv (t : ℕ) (p : Bool × Fin (t + 1) → Option Bool) :
    freeCount p = (Finset.univ.filter (fun k : Fin (2 * (t + 1)) => pinEquiv t p k = none)).card := by
  unfold freeCount
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  let e : Fin (2 * (t + 1)) ≃ Bool × Fin (t + 1) := (edgeEquiv t).trans (headV (ringPerm t))
  exact (Fintype.card_of_bijective
    (f := fun x : {k : Fin (2 * (t + 1)) // pinEquiv t p k = none} => (⟨e x.1, x.2⟩ : {v // p v = none}))
    ⟨fun a b h => Subtype.ext (e.injective (congrArg Subtype.val h)),
     fun y => ⟨⟨e.symm y.1, by simp [pinEquiv, qE, e, y.2]⟩, Subtype.ext (by simp)⟩⟩).symm

lemma freeCount_add_pinCount (t : ℕ) (p : Bool × Fin (t + 1) → Option Bool) :
    freeCount p + pinCount t (pinEquiv t p) = 2 * (t + 1) := by
  rw [freeCount_pinEquiv, pinCount]
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (2 * (t + 1))))) (fun k => pinEquiv t p k = none)
  simpa using h

lemma polyQ_none (t : ℕ) (u v : ℚ) :
    polyQ t (fun _ => none) u v = 1 + (u * v) ^ (t + 1) := by
  unfold polyQ
  have hconst : ∀ S : Fin (2 * (t + 1)) → Bool,
      (∀ k, (fun _ : Fin (2 * (t + 1)) => (none : Option Bool)) k = none → S (k + 1) = S k) ↔
      (S = fun _ => false) ∨ (S = fun _ => true) := by
    intro S
    constructor
    · intro h
      have hall : ∀ m : ℕ, S ⟨m % (2 * (t + 1)), Nat.mod_lt _ (by omega)⟩ = S 0 := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih =>
          have hstep := h ⟨m % (2 * (t + 1)), Nat.mod_lt _ (by omega)⟩ rfl
          have hadd : (⟨m % (2 * (t + 1)), Nat.mod_lt _ (by omega)⟩ + 1 : Fin (2 * (t + 1))) =
              ⟨(m + 1) % (2 * (t + 1)), Nat.mod_lt _ (by omega)⟩ := by
            apply Fin.ext
            rw [Fin.val_add, fin_one_val t]
            simp [Nat.add_mod]
          rw [hadd] at hstep
          exact hstep.trans ih
      cases h0 : S 0
      · left; funext k
        have := hall k.val
        simp [Nat.mod_eq_of_lt k.isLt, h0] at this
        exact this
      · right; funext k
        have := hall k.val
        simp [Nat.mod_eq_of_lt k.isLt, h0] at this
        exact this
    · rintro (rfl | rfl) k _ <;> rfl
  have hfilt : Finset.univ.filter (fun S : Fin (2 * (t + 1)) → Bool =>
      ∀ k, (fun _ : Fin (2 * (t + 1)) => (none : Option Bool)) k = none → S (k + 1) = S k) =
      {fun _ => false, fun _ => true} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    simpa using hconst S
  rw [hfilt, Finset.sum_pair]
  · have hf : (∏ k : Fin (2 * (t + 1)), if false then edgeWQ t (fun _ => none) u v k else 1) = 1 := by
      simp
    have ht : (∏ k : Fin (2 * (t + 1)), if true then edgeWQ t (fun _ => none) u v k else 1) =
        (u * v) ^ (t + 1) := by
      simp only [↓reduceIte, edgeWQ, epsQ, mul_one]
      have heq := Fintype.prod_equiv (edgeEquiv t)
        (fun k : Fin (2 * (t + 1)) => if k.val % 2 = 1 then v else u)
        (fun e : Bool × Fin (t + 1) => if e.1 then v else u)
        (fun k => by
          have hb : (edgeEquiv t k).1 = decide (k.val % 2 = 1) := rfl
          by_cases h : k.val % 2 = 1 <;> simp [hb, h])
      rw [heq, Fintype.prod_prod_type, Fintype.prod_bool]
      simp [mul_pow, mul_comm]
    rw [hf, ht]
  · intro h
    have := congrFun h 0
    simp at this

-- Nonempty pin set arc decomposition

section NonemptyPins

variable {t : ℕ} (q : Fin (2 * (t + 1)) → Option Bool) (hq : ∃ k, q k ≠ none)
include hq

omit hq in
abbrev PinType (q : Fin (2 * (t + 1)) → Option Bool) :=
  {b : Fin (2 * (t + 1)) // q b ≠ none}

lemma nextPin_nonempty (k : Fin (2 * (t + 1))) :
    (Finset.univ.filter (fun m : Fin (2 * (t + 1)) => q (k + m) ≠ none)).Nonempty := by
  obtain ⟨k0, hk0⟩ := hq
  exact ⟨k0 - k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hk0⟩⟩

def nextPinDist (k : Fin (2 * (t + 1))) : Fin (2 * (t + 1)) :=
  (Finset.univ.filter (fun m : Fin (2 * (t + 1)) => q (k + m) ≠ none)).min'
    (nextPin_nonempty q hq k)

lemma nextPinDist_spec (k : Fin (2 * (t + 1))) :
    q (k + nextPinDist q hq k) ≠ none :=
  (Finset.mem_filter.mp (Finset.min'_mem _ (nextPin_nonempty q hq k))).2

lemma nextPinDist_minimal (k m : Fin (2 * (t + 1))) (hm : m < nextPinDist q hq k) :
    q (k + m) = none := by
  by_contra hne
  have hle : nextPinDist q hq k ≤ m :=
    Finset.min'_le _ m (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
  exact not_lt_of_ge hle hm

lemma nextPinDist_eq_zero_of_ne {k : Fin (2 * (t + 1))} (hk : q k ≠ none) :
    nextPinDist q hq k = 0 := by
  have hle : nextPinDist q hq k ≤ 0 :=
    Finset.min'_le _ 0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hk⟩)
  exact Fin.ext (Nat.eq_zero_of_le_zero hle)

def clsQ (k : Fin (2 * (t + 1))) : PinType q :=
  ⟨k + nextPinDist q hq k, nextPinDist_spec q hq k⟩

lemma clsQ_pin (b : PinType q) : clsQ q hq b.1 = b := by
  apply Subtype.ext
  simp [clsQ, nextPinDist_eq_zero_of_ne q hq b.2]

lemma clsQ_surj : Function.Surjective (clsQ q hq) :=
  fun b => ⟨b.1, clsQ_pin q hq b⟩

lemma nextPinDist_step {k : Fin (2 * (t + 1))} (hk : q k = none) :
    0 < (nextPinDist q hq k).val ∧
    (nextPinDist q hq (k + 1)).val + 1 = (nextPinDist q hq k).val ∧
    clsQ q hq (k + 1) = clsQ q hq k := by
  have hpos : 0 < (nextPinDist q hq k).val := by
    by_contra h0
    have hz : nextPinDist q hq k = 0 := Fin.ext (by change (nextPinDist q hq k).val = 0; omega)
    have hspec := nextPinDist_spec q hq k
    rw [hz, add_zero] at hspec
    exact hspec hk
  let d1 : Fin (2 * (t + 1)) := ⟨(nextPinDist q hq k).val - 1, by omega⟩
  have h1val : (1 : Fin (2 * (t + 1))).val = 1 := fin_one_val t
  have hd1_add : (1 : Fin (2 * (t + 1))) + d1 = nextPinDist q hq k := by
    apply Fin.ext
    rw [Fin.val_add, h1val]
    dsimp only [d1]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hd1_mem : q ((k + 1) + d1) ≠ none := by
    rw [add_assoc, hd1_add]
    exact nextPinDist_spec q hq k
  have hle : nextPinDist q hq (k + 1) ≤ d1 :=
    Finset.min'_le _ d1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd1_mem⟩)
  have hge : d1 ≤ nextPinDist q hq (k + 1) := by
    by_contra hlt
    push Not at hlt
    have hlt' : (nextPinDist q hq (k + 1)).val < d1.val := hlt
    let m2 : Fin (2 * (t + 1)) := ⟨(nextPinDist q hq (k + 1)).val + 1, by omega⟩
    have hm2_eq : (1 : Fin (2 * (t + 1))) + nextPinDist q hq (k + 1) = m2 := by
      apply Fin.ext
      rw [Fin.val_add, h1val]
      dsimp only [m2]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hm2_lt : m2 < nextPinDist q hq k := by
      show m2.val < (nextPinDist q hq k).val
      dsimp only [m2, d1] at hlt' ⊢
      omega
    have hnone := nextPinDist_minimal q hq k m2 hm2_lt
    have hne := nextPinDist_spec q hq (k + 1)
    rw [add_assoc, hm2_eq] at hne
    exact hne hnone
  have heq : nextPinDist q hq (k + 1) = d1 := le_antisymm hle hge
  refine ⟨hpos, ?_, ?_⟩
  · rw [heq]; dsimp only [d1]; omega
  · apply Subtype.ext
    change (k + 1) + nextPinDist q hq (k + 1) = k + nextPinDist q hq k
    rw [heq, add_assoc, hd1_add]

lemma valid_iff_clsQ (S : Fin (2 * (t + 1)) → Bool) :
    (∀ k, q k = none → S (k + 1) = S k) ↔ (∀ x y, clsQ q hq x = clsQ q hq y → S x = S y) := by
  constructor
  · intro hS
    have hto : ∀ m : ℕ, ∀ x : Fin (2 * (t + 1)), (nextPinDist q hq x).val = m → S x = S (clsQ q hq x).1 := by
      intro m
      induction m with
      | zero =>
        intro x hx
        have hz : nextPinDist q hq x = 0 := Fin.ext hx
        simp [clsQ, hz]
      | succ m ih =>
        intro x hx
        have hxnone : q x = none := by
          by_contra hne
          have hz := nextPinDist_eq_zero_of_ne q hq hne
          rw [hz] at hx; simp at hx
        obtain ⟨_, hstep, hcls⟩ := nextPinDist_step q hq hxnone
        have h1 : S x = S (x + 1) := (hS x hxnone).symm
        have h2 : S (x + 1) = S (clsQ q hq (x + 1)).1 := ih (x + 1) (by omega)
        rw [h1, h2, hcls]
    intro x y hxy
    rw [hto _ x rfl, hto _ y rfl, hxy]
  · intro hS k hk
    exact hS (k + 1) k (nextPinDist_step q hq hk).2.2

lemma prevPin_nonempty (b : Fin (2 * (t + 1))) :
    (Finset.univ.filter (fun m : Fin (2 * (t + 1)) => q (b - 1 - m) ≠ none)).Nonempty := by
  obtain ⟨k0, hk0⟩ := hq
  exact ⟨b - 1 - k0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [sub_sub_cancel] using hk0⟩⟩

def prevPinRaw (b : Fin (2 * (t + 1))) : Fin (2 * (t + 1)) :=
  (Finset.univ.filter (fun m : Fin (2 * (t + 1)) => q (b - 1 - m) ≠ none)).min'
    (prevPin_nonempty q hq b)

def prevPinDist (b : Fin (2 * (t + 1))) : ℕ := (prevPinRaw q hq b).val + 1

lemma prevPinDist_pos (b : Fin (2 * (t + 1))) : 1 ≤ prevPinDist q hq b := by
  unfold prevPinDist; omega

lemma prevPinDist_le (b : Fin (2 * (t + 1))) : prevPinDist q hq b ≤ 2 * (t + 1) := by
  unfold prevPinDist; omega

lemma prevPinRaw_spec (b : Fin (2 * (t + 1))) : q (b - 1 - prevPinRaw q hq b) ≠ none :=
  (Finset.mem_filter.mp (Finset.min'_mem _ (prevPin_nonempty q hq b))).2

lemma prevPinRaw_minimal (b m : Fin (2 * (t + 1))) (hm : m < prevPinRaw q hq b) :
    q (b - 1 - m) = none := by
  by_contra hne
  have hle : prevPinRaw q hq b ≤ m :=
    Finset.min'_le _ m (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
  exact not_lt_of_ge hle hm

def prevPin (b : PinType q) : PinType q :=
  ⟨b.1 - 1 - prevPinRaw q hq b.1, prevPinRaw_spec q hq b.1⟩

lemma prevPin_val_eq (b : PinType q) :
    (prevPin q hq b).1 = b.1 - Fin.ofNat (2 * (t + 1)) (prevPinDist q hq b.1) := by
  change b.1 - 1 - prevPinRaw q hq b.1 = b.1 - Fin.ofNat (2 * (t + 1)) ((prevPinRaw q hq b.1).val + 1)
  rw [ofNat_fin_add, ofNat_fin_one, ofNat_fin_val_self, sub_sub, add_comm (prevPinRaw q hq b.1) 1]

lemma prevPin_bijective : Function.Bijective (prevPin q hq) := by
  haveI : NeZero (2 * (t + 1)) := ⟨by omega⟩
  let inv : PinType q → PinType q := fun a => clsQ q hq (a.1 + 1)
  have hleft : ∀ b : PinType q, inv (prevPin q hq b) = b := by
    intro b
    apply Subtype.ext
    change (b.1 - 1 - prevPinRaw q hq b.1 + 1) + nextPinDist q hq (b.1 - 1 - prevPinRaw q hq b.1 + 1) = b.1
    set m := prevPinRaw q hq b.1
    have hbase : b.1 - 1 - m + 1 = b.1 - m := by abel
    rw [hbase]
    have hdist : nextPinDist q hq (b.1 - m) = m := by
      apply le_antisymm
      · exact Finset.min'_le _ m (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using b.2⟩)
      · by_contra hlt
        push Not at hlt
        set d := nextPinDist q hq (b.1 - m)
        have hdm : d.val < m.val := hlt
        let r : Fin (2 * (t + 1)) := ⟨m.val - d.val - 1, by omega⟩
        have hrlt : r < m := by show r.val < m.val; dsimp only [r]; omega
        have hreq : b.1 - 1 - r = (b.1 - m) + d := by
          have hr1 : (1 : Fin (2 * (t + 1))) + r + d = m :=
            fin_add_three_eq _ _ _ _ (by rw [fin_one_val t]; dsimp only [r]; omega)
          rw [← hr1]; abel
        have hnone := prevPinRaw_minimal q hq b.1 r hrlt
        rw [hreq] at hnone
        exact nextPinDist_spec q hq (b.1 - m) hnone
    rw [hdist, sub_add_cancel]
  have hright : ∀ a : PinType q, prevPin q hq (inv a) = a := by
    intro a
    apply Subtype.ext
    set d := nextPinDist q hq (a.1 + 1)
    change (a.1 + 1 + d) - 1 - prevPinRaw q hq (a.1 + 1 + d) = a.1
    have hraw : prevPinRaw q hq (a.1 + 1 + d) = d := by
      apply le_antisymm
      · exact Finset.min'_le _ d (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          have : a.1 + 1 + d - 1 - d = a.1 := by abel
          rw [this]; exact a.2⟩)
      · by_contra hlt
        push Not at hlt
        set r := prevPinRaw q hq (a.1 + 1 + d)
        have hrd : r.val < d.val := hlt
        let s : Fin (2 * (t + 1)) := ⟨d.val - r.val - 1, by omega⟩
        have hslt : s < d := by show s.val < d.val; dsimp only [s]; omega
        have hseq : (a.1 + 1) + s = (a.1 + 1 + d) - 1 - r := by
          have hs1 : (1 : Fin (2 * (t + 1))) + r + s = d :=
            fin_add_three_eq _ _ _ _ (by rw [fin_one_val t]; dsimp only [s]; omega)
          rw [← hs1]; abel
        have hnone := nextPinDist_minimal q hq (a.1 + 1) s hslt
        rw [hseq] at hnone
        exact prevPinRaw_spec q hq (a.1 + 1 + d) hnone
    rw [hraw]; abel
  exact Function.bijective_iff_has_inverse.mpr ⟨inv, hleft, hright⟩

lemma mem_arc_iff (b : PinType q) (k : Fin (2 * (t + 1))) :
    clsQ q hq k = b ↔ ∃ r : Fin (prevPinDist q hq b.1), k = b.1 - Fin.ofNat (2 * (t + 1)) r.val := by
  haveI : NeZero (2 * (t + 1)) := ⟨by omega⟩
  constructor
  · intro hcls
    have hk : k + nextPinDist q hq k = b.1 := congrArg Subtype.val hcls
    have hd_lt : (nextPinDist q hq k).val < prevPinDist q hq b.1 := by
      by_contra hge
      push Not at hge
      set d := nextPinDist q hq k
      set m := prevPinRaw q hq b.1
      have hdm : m.val + 1 ≤ d.val := by unfold prevPinDist at hge; omega
      let s : Fin (2 * (t + 1)) := ⟨d.val - (m.val + 1), by omega⟩
      have hslt : s < d := by show s.val < d.val; dsimp only [s]; omega
      have hseq : k + s = b.1 - 1 - m := by
        have hms : s + 1 + m = d :=
          fin_add_three_eq _ _ _ _ (by rw [fin_one_val t]; dsimp only [s]; omega)
        rw [← hk, ← hms]; abel
      have hnone := nextPinDist_minimal q hq k s hslt
      rw [hseq] at hnone
      exact prevPinRaw_spec q hq b.1 hnone
    refine ⟨⟨(nextPinDist q hq k).val, hd_lt⟩, ?_⟩
    rw [ofNat_fin_val_self, ← hk, add_sub_cancel_right]
  · rintro ⟨r, rfl⟩
    apply Subtype.ext
    change (b.1 - Fin.ofNat (2 * (t + 1)) r.val) + nextPinDist q hq (b.1 - Fin.ofNat (2 * (t + 1)) r.val) = b.1
    have hr_lt : r.val < 2 * (t + 1) := lt_of_lt_of_le r.isLt (prevPinDist_le q hq b.1)
    let rF : Fin (2 * (t + 1)) := ⟨r.val, hr_lt⟩
    have hrF : Fin.ofNat (2 * (t + 1)) r.val = rF := ofNat_fin_eq r.val hr_lt
    rw [hrF]
    have hdist : nextPinDist q hq (b.1 - rF) = rF := by
      apply le_antisymm
      · exact Finset.min'_le _ rF (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using b.2⟩)
      · by_contra hlt
        push Not at hlt
        set d := nextPinDist q hq (b.1 - rF)
        have hdr : d.val < rF.val := hlt
        let m : Fin (2 * (t + 1)) := ⟨rF.val - d.val - 1, by omega⟩
        have hmlt : m < prevPinRaw q hq b.1 := by
          show m.val < (prevPinRaw q hq b.1).val
          have hrp : r.val < (prevPinRaw q hq b.1).val + 1 := r.isLt
          dsimp only [m, rF] at hdr ⊢; omega
        have hmeq : b.1 - 1 - m = (b.1 - rF) + d := by
          have hmd : (1 : Fin (2 * (t + 1))) + m + d = rF :=
            fin_add_three_eq _ _ _ _ (by rw [fin_one_val t]; dsimp only [m, rF] at hdr ⊢; omega)
          rw [← hmd]; abel
        have hnone := prevPinRaw_minimal q hq b.1 m hmlt
        rw [hmeq] at hnone
        exact nextPinDist_spec q hq (b.1 - rF) hnone
    rw [hdist, sub_add_cancel]

omit q hq in
lemma telescope_eps (f : Fin (2 * (t + 1)) → ℚ) (hf : ∀ x, f x * f x = 1)
    (b : Fin (2 * (t + 1))) (L : ℕ) :
    (∏ r : Fin L, (f (b - Fin.ofNat (2 * (t + 1)) r.val) *
        f (b - Fin.ofNat (2 * (t + 1)) r.val - 1))) =
      f b * f (b - Fin.ofNat (2 * (t + 1)) L) := by
  induction L with
  | zero =>
    have h0 : Fin.ofNat (2 * (t + 1)) 0 = 0 := rfl
    simp [h0, hf]
  | succ L ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    have hstep : b - Fin.ofNat (2 * (t + 1)) L - 1 = b - Fin.ofNat (2 * (t + 1)) (L + 1) := by
      rw [ofNat_fin_add, ofNat_fin_one, sub_sub]
    rw [hstep]
    calc (f b * f (b - Fin.ofNat (2 * (t + 1)) L)) *
          (f (b - Fin.ofNat (2 * (t + 1)) L) * f (b - Fin.ofNat (2 * (t + 1)) (L + 1)))
        = f b * (f (b - Fin.ofNat (2 * (t + 1)) L) * f (b - Fin.ofNat (2 * (t + 1)) L)) *
          f (b - Fin.ofNat (2 * (t + 1)) (L + 1)) := by ring
      _ = f b * f (b - Fin.ofNat (2 * (t + 1)) (L + 1)) := by rw [hf, mul_one]

omit q hq in
lemma sub_nat_mod_two (b : Fin (2 * (t + 1))) (r : ℕ) :
    (b - Fin.ofNat (2 * (t + 1)) r).val % 2 = (b.val + r) % 2 := by
  haveI : NeZero (2 * (t + 1)) := ⟨by omega⟩
  rw [Fin.val_sub, Fin.val_ofNat]
  have h2 : 2 ∣ 2 * (t + 1) := dvd_mul_right 2 (t + 1)
  have h1 : (2 * (t + 1) - r % (2 * (t + 1)) + b.val) % (2 * (t + 1)) % 2 =
      (2 * (t + 1) - r % (2 * (t + 1)) + b.val) % 2 := Nat.mod_mod_of_dvd _ h2
  rw [h1]
  have hrlt : r % (2 * (t + 1)) < 2 * (t + 1) := Nat.mod_lt _ (by omega)
  have hr2 : (r % (2 * (t + 1))) % 2 = r % 2 := Nat.mod_mod_of_dvd _ h2
  omega

omit q hq in
lemma alt_prod_even (u v : ℚ) (b j : ℕ) :
    (∏ r : Fin (2 * j), if (b + r.val) % 2 = 1 then v else u) = (u * v) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h2 : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
    rw [Fin.prod_univ_eq_prod_range (fun r => if (b + r) % 2 = 1 then v else u),
        h2, Finset.prod_range_succ, Finset.prod_range_succ,
        ← Fin.prod_univ_eq_prod_range (fun r => if (b + r) % 2 = 1 then v else u), ih]
    by_cases hb : b % 2 = 1
    · have h1 : (b + 2 * j) % 2 = 1 := by omega
      have h2' : (b + (2 * j + 1)) % 2 = 0 := by omega
      simp [h1, h2', pow_succ]; ring
    · have h1 : (b + 2 * j) % 2 = 0 := by omega
      have h2' : (b + (2 * j + 1)) % 2 = 1 := by omega
      simp [h1, h2', pow_succ]; ring

omit q hq in
lemma alt_prod_odd (u v : ℚ) (b j : ℕ) :
    (∏ r : Fin (2 * j + 1), if (b + r.val) % 2 = 1 then v else u) =
      (if b % 2 = 1 then v else u) * (u * v) ^ j := by
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [alt_prod_even]
  have h : (b + 2 * j) % 2 = b % 2 := by omega
  simp only [h]
  rw [mul_comm]

omit q hq in
def factorOf (c : Fin 3) (s : Bool) (j : ℕ) (u v : ℚ) : ℚ :=
  1 + (if s then (-1 : ℚ) else 1) *
    match c with
    | 0 => (u * v) ^ j
    | 1 => u ^ (j + 1) * v ^ j
    | 2 => u ^ j * v ^ (j + 1)

def arcType (b : PinType q) : Fin 3 :=
  if prevPinDist q hq b.1 % 2 = 0 then 0
  else if b.1.val % 2 = 0 then 1 else 2

def arcSign (b : PinType q) : Bool :=
  decide (epsQ q b.1 * epsQ q (prevPin q hq b).1 = -1)

def arcJ (b : PinType q) : Fin ((t + 1) + 1) :=
  ⟨prevPinDist q hq b.1 / 2, by have := prevPinDist_le q hq b.1; omega⟩

lemma arcSign_val (b : PinType q) :
    (if arcSign q hq b then (-1 : ℚ) else 1) = epsQ q b.1 * epsQ q (prevPin q hq b).1 := by
  unfold arcSign
  have h1 : epsQ q b.1 = 1 ∨ epsQ q b.1 = -1 := by
    unfold epsQ; cases q b.1 with | none => left; rfl | some c => cases c <;> simp [sgn]
  have h2 : epsQ q (prevPin q hq b).1 = 1 ∨ epsQ q (prevPin q hq b).1 = -1 := by
    unfold epsQ; cases q (prevPin q hq b).1 with | none => left; rfl | some c => cases c <;> simp [sgn]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2] <;> norm_num

lemma arc_prod_eq_factor (b : PinType q) (u v : ℚ) :
    1 + (∏ k ∈ Finset.univ.filter (fun k => clsQ q hq k = b), edgeWQ t q u v k) =
      factorOf (arcType q hq b) (arcSign q hq b) (arcJ q hq b).val u v := by
  haveI : NeZero (2 * (t + 1)) := ⟨by omega⟩
  set L := prevPinDist q hq b.1
  have hLle : L ≤ 2 * (t + 1) := prevPinDist_le q hq b.1
  have hbij : (∏ k ∈ Finset.univ.filter (fun k => clsQ q hq k = b), edgeWQ t q u v k) =
      ∏ r : Fin L, edgeWQ t q u v (b.1 - Fin.ofNat (2 * (t + 1)) r.val) := by
    symm
    refine Finset.prod_bij (fun r _ => b.1 - Fin.ofNat (2 * (t + 1)) r.val) ?_ ?_ ?_ ?_
    · intro r _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_arc_iff q hq b _).mpr ⟨r, rfl⟩⟩
    · intro r1 _ r2 _ h
      have hsub : Fin.ofNat (2 * (t + 1)) r1.val = Fin.ofNat (2 * (t + 1)) r2.val := by
        have := congrArg (fun x => b.1 - x) h
        simpa using this
      rw [ofNat_fin_eq r1.val (lt_of_lt_of_le r1.isLt hLle),
          ofNat_fin_eq r2.val (lt_of_lt_of_le r2.isLt hLle)] at hsub
      exact Fin.ext (congrArg (Fin.val : Fin (2 * (t + 1)) → ℕ) hsub)
    · intro k hk
      obtain ⟨r, rfl⟩ := (mem_arc_iff q hq b k).mp (Finset.mem_filter.mp hk).2
      exact ⟨r, Finset.mem_univ _, rfl⟩
    · intro _ _; rfl
  rw [hbij]
  have hsplit : (∏ r : Fin L, edgeWQ t q u v (b.1 - Fin.ofNat (2 * (t + 1)) r.val)) =
      (∏ r : Fin L, if (b.1.val + r.val) % 2 = 1 then v else u) *
      (∏ r : Fin L, (epsQ q (b.1 - Fin.ofNat (2 * (t + 1)) r.val) *
        epsQ q (b.1 - Fin.ofNat (2 * (t + 1)) r.val - 1))) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun r _ => ?_)
    unfold edgeWQ
    rw [sub_nat_mod_two]
    ring
  rw [hsplit, telescope_eps (epsQ q) (epsQ_sq q) b.1 L, ← prevPin_val_eq q hq b,
      ← arcSign_val q hq b]
  unfold factorOf arcType arcJ
  have hLeq : prevPinDist q hq b.1 = L := rfl
  by_cases hev : L % 2 = 0
  · have hL : L = 2 * (L / 2) := by omega
    have hprod : (∏ r : Fin L, if (b.1.val + r.val) % 2 = 1 then v else u) = (u * v) ^ (L / 2) := by
      have hgen : ∀ m, m = 2 * (L / 2) → (∏ r : Fin m, if (b.1.val + r.val) % 2 = 1 then v else u) = (u * v) ^ (L / 2) := by
        rintro _ rfl; exact alt_prod_even u v b.1.val (L / 2)
      exact hgen L hL
    simp only [hLeq, hev, ↓reduceIte, hprod]
    ring
  · have hL : L = 2 * (L / 2) + 1 := by omega
    have hprod : (∏ r : Fin L, if (b.1.val + r.val) % 2 = 1 then v else u) =
        (if b.1.val % 2 = 1 then v else u) * (u * v) ^ (L / 2) := by
      have hgen : ∀ m, m = 2 * (L / 2) + 1 → (∏ r : Fin m, if (b.1.val + r.val) % 2 = 1 then v else u) =
          (if b.1.val % 2 = 1 then v else u) * (u * v) ^ (L / 2) := by
        rintro _ rfl; exact alt_prod_odd u v b.1.val (L / 2)
      exact hgen L hL
    by_cases hb : b.1.val % 2 = 0
    · simp only [hLeq, hev, hb, ↓reduceIte, hprod]
      simp only [show (0 : ℕ) ≠ 1 by decide, ↓reduceIte, mul_pow, pow_succ]
      ring
    · have hb1 : b.1.val % 2 = 1 := by omega
      simp only [hLeq, hev, hb, ↓reduceIte, hprod]
      simp only [hb1, ↓reduceIte, mul_pow, pow_succ]
      ring

lemma polyQ_eq_prod_pins (u v : ℚ) :
    polyQ t q u v = ∏ b : PinType q, factorOf (arcType q hq b) (arcSign q hq b) (arcJ q hq b).val u v := by
  unfold polyQ
  rw [sum_valid_eq_prod (clsQ q hq) (clsQ_surj q hq) (edgeWQ t q u v) _ (valid_iff_clsQ q hq)]
  refine Finset.prod_congr rfl (fun b _ => arc_prod_eq_factor q hq b u v)

end NonemptyPins

-- Section 3: RawInv, validRaw, reduceRaw, unfuseRaw

abbrev RawInv (n : ℕ) := Fin 3 → Bool → Fin (n + 1) → ℕ

def weightOf {n : ℕ} (c : Fin 3) (j : Fin (n + 1)) : ℕ :=
  2 * j.val + if c = 0 then 0 else 1

def totalLen {n : ℕ} (a : RawInv n) : ℕ :=
  ∑ c : Fin 3, ∑ s : Bool, ∑ j : Fin (n + 1), a c s j * weightOf c j

def totalCount {n : ℕ} (a : RawInv n) : ℕ :=
  ∑ c : Fin 3, ∑ s : Bool, ∑ j : Fin (n + 1), a c s j

def phi {n : ℕ} (a : RawInv n) : ℕ :=
  ∑ j : Fin (n + 1), a 0 true j * j.val.factorization 2

def validRaw {n : ℕ} (a : RawInv n) : Prop :=
  a 0 false 0 = 0 ∧ a 0 true 0 = 0 ∧
  totalLen a = 2 * n ∧
  (∑ s : Bool, ∑ j : Fin (n + 1), a 1 s j) = (∑ s : Bool, ∑ j : Fin (n + 1), a 2 s j) ∧
  (∑ c : Fin 3, ∑ j : Fin (n + 1), a c true j) % 2 = 0

def reducedRaw {n : ℕ} (a : RawInv n) : Prop :=
  validRaw a ∧ ∀ j : Fin (n + 1), a 0 false j = 0 ∨ a 0 true j = 0

def polyOfRaw {n : ℕ} (a : RawInv n) (u v : ℚ) : ℚ :=
  ∏ c : Fin 3, ∏ s : Bool, ∏ j : Fin (n + 1), (factorOf c s j.val u v) ^ (a c s j)

lemma totalCount_le_totalLen {n : ℕ} {a : RawInv n} (h0f : a 0 false 0 = 0) (h0t : a 0 true 0 = 0) :
    totalCount a ≤ totalLen a := by
  unfold totalCount totalLen
  refine Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun j _ => ?_)))
  by_cases h : c = 0 ∧ j = 0
  · rcases h with ⟨rfl, rfl⟩
    cases s <;> simp [h0f, h0t]
  · have hw : 1 ≤ weightOf c j := by
      unfold weightOf
      by_cases hc : c = 0
      · have hj : j.val ≠ 0 := fun hv => h ⟨hc, Fin.ext hv⟩
        simp [hc]; omega
      · simp [hc]
    exact Nat.le_mul_of_pos_right _ hw

lemma validRaw_entry_le {n : ℕ} {a : RawInv n} (ha : validRaw a) (c : Fin 3) (s : Bool) (j : Fin (n + 1)) :
    a c s j ≤ 2 * n := by
  have h1 : a c s j ≤ totalCount a := by
    unfold totalCount
    calc a c s j ≤ ∑ j' : Fin (n + 1), a c s j' := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      _ ≤ ∑ s' : Bool, ∑ j' : Fin (n + 1), a c s' j' :=
        Finset.single_le_sum (f := fun s' : Bool => ∑ j' : Fin (n + 1), a c s' j') (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
      _ ≤ ∑ c' : Fin 3, ∑ s' : Bool, ∑ j' : Fin (n + 1), a c' s' j' :=
        Finset.single_le_sum (f := fun c' => ∑ s' : Bool, ∑ j' : Fin (n + 1), a c' s' j') (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  exact h1.trans ((totalCount_le_totalLen ha.1 ha.2.1).trans ha.2.2.1.le)

lemma validRaw_pos_totalCount {t : ℕ} {a : RawInv (t + 1)} (ha : validRaw a) :
    1 ≤ totalCount a := by
  by_contra h0
  have hz : totalCount a = 0 := by omega
  have hall : ∀ c s j, a c s j = 0 := by
    intro c s j
    have h1 : a c s j ≤ totalCount a := by
      unfold totalCount
      calc a c s j ≤ ∑ j' : Fin (t + 2), a c s j' := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        _ ≤ ∑ s' : Bool, ∑ j' : Fin (t + 2), a c s' j' :=
          Finset.single_le_sum (f := fun s' : Bool => ∑ j' : Fin (t + 2), a c s' j') (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
        _ ≤ ∑ c' : Fin 3, ∑ s' : Bool, ∑ j' : Fin (t + 2), a c' s' j' :=
          Finset.single_le_sum (f := fun c' => ∑ s' : Bool, ∑ j' : Fin (t + 2), a c' s' j') (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    omega
  have hlen := ha.2.2.1
  unfold totalLen at hlen
  simp [hall] at hlen

def rawOfQ {t : ℕ} (q : Fin (2 * (t + 1)) → Option Bool) (hq : ∃ k, q k ≠ none) : RawInv (t + 1) :=
  fun c s j => (Finset.univ.filter (fun b : PinType q =>
    arcType q hq b = c ∧ arcSign q hq b = s ∧ arcJ q hq b = j)).card

lemma rawOfQ_totalCount {t : ℕ} (q : Fin (2 * (t + 1)) → Option Bool) (hq : ∃ k, q k ≠ none) :
    totalCount (rawOfQ q hq) = pinCount t q := by
  unfold totalCount rawOfQ pinCount
  let f : PinType q → Fin 3 × Bool × Fin (t + 2) := fun b => (arcType q hq b, arcSign q hq b, arcJ q hq b)
  have hsum : (∑ c : Fin 3, ∑ s : Bool, ∑ j : Fin (t + 2),
      (Finset.univ.filter (fun b : PinType q => arcType q hq b = c ∧ arcSign q hq b = s ∧ arcJ q hq b = j)).card) =
      ∑ x : Fin 3 × Bool × Fin (t + 2), (Finset.univ.filter (fun b : PinType q => f b = x)).card := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun j _ => ?_))
    rfl
  rw [hsum, ← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)]
  simp only [Finset.card_univ, Fintype.card_subtype]

lemma rawOfQ_poly {t : ℕ} (q : Fin (2 * (t + 1)) → Option Bool) (hq : ∃ k, q k ≠ none) (u v : ℚ) :
    polyQ t q u v = polyOfRaw (rawOfQ q hq) u v := by
  rw [polyQ_eq_prod_pins q hq u v]
  unfold polyOfRaw rawOfQ
  let f : PinType q → Fin 3 × Bool × Fin (t + 2) := fun b => (arcType q hq b, arcSign q hq b, arcJ q hq b)
  rw [← Finset.prod_fiberwise_of_maps_to (g := f) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl (fun c _ => ?_)
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl (fun s _ => Finset.prod_congr rfl (fun j _ => ?_))
  have hf : Finset.univ.filter (fun b : PinType q => f b = (c, s, j)) =
      Finset.univ.filter (fun b : PinType q => arcType q hq b = c ∧ arcSign q hq b = s ∧ arcJ q hq b = j) := by
    ext b; simp [f]
  rw [hf]
  trans (∏ _b ∈ Finset.univ.filter (fun b : PinType q =>
      arcType q hq b = c ∧ arcSign q hq b = s ∧ arcJ q hq b = j), factorOf c s j.val u v)
  · refine Finset.prod_congr rfl (fun b hb => ?_)
    obtain ⟨h1, h2, h3⟩ := (Finset.mem_filter.mp hb).2
    rw [h1, h2, h3]
  · rw [Finset.prod_const]

lemma rawOfQ_valid {t : ℕ} (q : Fin (2 * (t + 1)) → Option Bool) (hq : ∃ k, q k ≠ none) :
    validRaw (rawOfQ q hq) := by
  haveI : NeZero (2 * (t + 1)) := ⟨by omega⟩
  have hwt : ∀ b : PinType q, weightOf (arcType q hq b) (arcJ q hq b) = prevPinDist q hq b.1 := by
    intro b
    unfold weightOf arcType arcJ
    by_cases hev : prevPinDist q hq b.1 % 2 = 0
    · simp [hev]; omega
    · by_cases hb : b.1.val % 2 = 0 <;> simp [hev, hb] <;> omega
  have h0 : ∀ s : Bool, rawOfQ q hq 0 s 0 = 0 := by
    intro s
    unfold rawOfQ
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro b _ ⟨h1, _, h3⟩
    have hpos := prevPinDist_pos q hq b.1
    have hw := hwt b
    rw [h1, h3] at hw
    simp [weightOf] at hw
    omega
  refine ⟨h0 false, h0 true, ?_, ?_, ?_⟩
  · -- totalLen = 2 * (t + 1)
    let f : PinType q → Fin 3 × Bool × Fin (t + 2) := fun b => (arcType q hq b, arcSign q hq b, arcJ q hq b)
    have hsum : totalLen (rawOfQ q hq) = ∑ b : PinType q, prevPinDist q hq b.1 := by
      unfold totalLen rawOfQ
      rw [← Finset.sum_fiberwise_of_maps_to (g := f) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun j _ => ?_))
      have hf : Finset.univ.filter (fun b : PinType q => f b = (c, s, j)) =
          Finset.univ.filter (fun b : PinType q => arcType q hq b = c ∧ arcSign q hq b = s ∧ arcJ q hq b = j) := by
        ext b; simp [f]
      rw [hf]
      trans (∑ _b ∈ Finset.univ.filter (fun b : PinType q =>
          arcType q hq b = c ∧ arcSign q hq b = s ∧ arcJ q hq b = j), weightOf c j)
      · rw [Finset.sum_const, smul_eq_mul]
      · refine Finset.sum_congr rfl (fun b hb => ?_)
        obtain ⟨h1, _, h3⟩ := (Finset.mem_filter.mp hb).2
        rw [← hwt b, h1, h3]
    rw [hsum]
    have harc : ∀ b : PinType q, prevPinDist q hq b.1 =
        (Finset.univ.filter (fun k : Fin (2 * (t + 1)) => clsQ q hq k = b)).card := by
      intro b
      have hLle := prevPinDist_le q hq b.1
      trans (Finset.univ : Finset (Fin (prevPinDist q hq b.1))).card
      · simp
      · refine Finset.card_bij (fun r _ => b.1 - Fin.ofNat (2 * (t + 1)) r.val) ?_ ?_ ?_
        · intro r _
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_arc_iff q hq b _).mpr ⟨r, rfl⟩⟩
        · intro r1 _ r2 _ h
          have hsub : Fin.ofNat (2 * (t + 1)) r1.val = Fin.ofNat (2 * (t + 1)) r2.val := by
            have := congrArg (fun x => b.1 - x) h
            simpa using this
          rw [ofNat_fin_eq r1.val (lt_of_lt_of_le r1.isLt hLle),
              ofNat_fin_eq r2.val (lt_of_lt_of_le r2.isLt hLle)] at hsub
          exact Fin.ext (congrArg (Fin.val : Fin (2 * (t + 1)) → ℕ) hsub)
        · intro k hk
          obtain ⟨r, rfl⟩ := (mem_arc_iff q hq b k).mp (Finset.mem_filter.mp hk).2
          exact ⟨r, Finset.mem_univ _, rfl⟩
    simp_rw [harc]
    rw [← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)]
    simp
  · -- #(c = 1) = #(c = 2)
    have hcnt : ∀ c : Fin 3, (∑ s : Bool, ∑ j : Fin (t + 2), rawOfQ q hq c s j) =
        (Finset.univ.filter (fun b : PinType q => arcType q hq b = c)).card := by
      intro c
      unfold rawOfQ
      let g : PinType q → Bool × Fin (t + 2) := fun b => (arcSign q hq b, arcJ q hq b)
      have := (Finset.card_eq_sum_card_fiberwise
        (s := Finset.univ.filter (fun b : PinType q => arcType q hq b = c))
        (t := Finset.univ) (f := g) (fun _ _ => Finset.mem_univ _))
      rw [this, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun j _ => ?_))
      congr 1; ext b; simp [g, and_assoc]
    rw [hcnt 1, hcnt 2]
    have hbij := prevPin_bijective q hq
    have hsum_par : (∑ b : PinType q, ((b.1.val % 2 : ℕ) : ℤ)) =
        ∑ b : PinType q, (((prevPin q hq b).1.val % 2 : ℕ) : ℤ) :=
      (Fintype.sum_bijective (prevPin q hq) hbij _ _ (fun _ => rfl)).symm
    have hdiff : (∑ b : PinType q, (((b.1.val % 2 : ℕ) : ℤ) - (((prevPin q hq b).1.val % 2 : ℕ) : ℤ))) = 0 := by
      rw [Finset.sum_sub_distrib, hsum_par, sub_self]
    have hterm : ∀ b : PinType q,
        (((b.1.val % 2 : ℕ) : ℤ) - (((prevPin q hq b).1.val % 2 : ℕ) : ℤ)) =
        (if arcType q hq b = 2 then 1 else 0) - (if arcType q hq b = 1 then 1 else 0) := by
      intro b
      rw [prevPin_val_eq q hq b, sub_nat_mod_two]
      unfold arcType
      by_cases hev : prevPinDist q hq b.1 % 2 = 0
      · have hp : (b.1.val + prevPinDist q hq b.1) % 2 = b.1.val % 2 := by omega
        simp [hev, hp]
      · by_cases hb : b.1.val % 2 = 0
        · have hp : (b.1.val + prevPinDist q hq b.1) % 2 = 1 := by omega
          simp [hev, hb, hp]
        · have hb1 : b.1.val % 2 = 1 := by omega
          have hp : (b.1.val + prevPinDist q hq b.1) % 2 = 0 := by omega
          simp [hev, hb, hb1, hp]
    simp_rw [hterm] at hdiff
    rw [Finset.sum_sub_distrib] at hdiff
    simp only [Finset.sum_boole] at hdiff
    have h12 : ((Finset.univ.filter (fun b : PinType q => arcType q hq b = 2)).card : ℤ) =
        ((Finset.univ.filter (fun b : PinType q => arcType q hq b = 1)).card : ℤ) := sub_eq_zero.mp hdiff
    exact_mod_cast h12.symm
  · -- #(s = true) % 2 = 0
    have hcnt : (∑ c : Fin 3, ∑ j : Fin (t + 2), rawOfQ q hq c true j) =
        (Finset.univ.filter (fun b : PinType q => arcSign q hq b = true)).card := by
      unfold rawOfQ
      let g : PinType q → Fin 3 × Fin (t + 2) := fun b => (arcType q hq b, arcJ q hq b)
      have := (Finset.card_eq_sum_card_fiberwise
        (s := Finset.univ.filter (fun b : PinType q => arcSign q hq b = true))
        (t := Finset.univ) (f := g) (fun _ _ => Finset.mem_univ _))
      rw [this, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun j _ => ?_))
      congr 1; ext b; simp [g]; tauto
    rw [hcnt]
    have hprod : (∏ b : PinType q, if arcSign q hq b then (-1 : ℚ) else 1) = 1 := by
      simp_rw [arcSign_val q hq]
      rw [Finset.prod_mul_distrib]
      have hbij := Fintype.prod_bijective (prevPin q hq) (prevPin_bijective q hq)
        (fun b => epsQ q (prevPin q hq b).1) (fun b => epsQ q b.1) (fun _ => rfl)
      rw [hbij, ← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun b _ => epsQ_sq q b.1)
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one] at hprod
    have hmod : (Finset.univ.filter (fun b : PinType q => arcSign q hq b = true)).card % 2 = 0 := by
      by_contra hodd
      have h1 : (Finset.univ.filter (fun b : PinType q => arcSign q hq b = true)).card % 2 = 1 := by omega
      have hneg : (-1 : ℚ) ^ (Finset.univ.filter (fun b : PinType q => arcSign q hq b = true)).card = -1 := by
        rw [← Nat.div_add_mod (Finset.univ.filter (fun b : PinType q => arcSign q hq b = true)).card 2,
            h1, pow_add, pow_mul]
        norm_num
      rw [hneg] at hprod
      norm_num at hprod
    exact hmod

-- Fusion (reduceRaw) and Unfusion (unfuseRaw)

def fuseAt {n : ℕ} (k : ℕ) (a : RawInv n) : RawInv n :=
  if hk : 0 < k ∧ 2 * k ≤ n then
    let jk : Fin (n + 1) := ⟨k, by omega⟩
    let j2k : Fin (n + 1) := ⟨2 * k, by omega⟩
    let m := min (a 0 false jk) (a 0 true jk)
    fun c s j =>
      if c = 0 ∧ s = false ∧ j = jk then a 0 false jk - m
      else if c = 0 ∧ s = true ∧ j = jk then a 0 true jk - m
      else if c = 0 ∧ s = true ∧ j = j2k then a 0 true j2k + m
      else a c s j
  else a

lemma factorization_two_mul_two {k : ℕ} (hk : 0 < k) :
    (2 * k).factorization 2 = k.factorization 2 + 1 := by
  rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two, add_comm]

lemma fuseAt_props {n : ℕ} (k : ℕ) {a : RawInv n} (ha : validRaw a) :
    validRaw (fuseAt k a) ∧
    (∀ u v, polyOfRaw (fuseAt k a) u v = polyOfRaw a u v) ∧
    totalCount (fuseAt k a) + phi (fuseAt k a) = totalCount a + phi a ∧
    totalCount (fuseAt k a) ≤ totalCount a ∧
    (∀ j : Fin (n + 1), j.val < k →
      fuseAt k a 0 false j = a 0 false j ∧ fuseAt k a 0 true j = a 0 true j) ∧
    (∀ (_ : 0 < k) (hkn : k ≤ n), fuseAt k a 0 false ⟨k, by omega⟩ = 0 ∨ fuseAt k a 0 true ⟨k, by omega⟩ = 0) := by
  by_cases hk : 0 < k ∧ 2 * k ≤ n
  · set jk : Fin (n + 1) := ⟨k, by omega⟩
    set j2k : Fin (n + 1) := ⟨2 * k, by omega⟩
    set m := min (a 0 false jk) (a 0 true jk)
    have hne : jk ≠ j2k := fun h => by have := congrArg Fin.val h; dsimp only [jk, j2k] at this; omega
    have hjk0 : jk ≠ 0 := fun h => by have := congrArg Fin.val h; simp [jk] at this; omega
    have hj2k0 : j2k ≠ 0 := fun h => by have := congrArg Fin.val h; simp [j2k] at this; omega
    have hmf : m ≤ a 0 false jk := min_le_left _ _
    have hmt : m ≤ a 0 true jk := min_le_right _ _
    have hdef : ∀ c s j, fuseAt k a c s j =
        if c = 0 ∧ s = false ∧ j = jk then a 0 false jk - m
        else if c = 0 ∧ s = true ∧ j = jk then a 0 true jk - m
        else if c = 0 ∧ s = true ∧ j = j2k then a 0 true j2k + m
        else a c s j := fun c s j => by unfold fuseAt; rw [dif_pos hk]
    have h0f_sum : ∀ f : Fin (n + 1) → ℕ,
        (∑ j : Fin (n + 1), fuseAt k a 0 false j * f j) + m * f jk =
        ∑ j : Fin (n + 1), a 0 false j * f j := by
      intro f
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ jk),
          ← Finset.add_sum_erase _ (fun j => a 0 false j * f j) (Finset.mem_univ jk)]
      have hrest : ∑ j ∈ Finset.univ.erase jk, fuseAt k a 0 false j * f j =
          ∑ j ∈ Finset.univ.erase jk, a 0 false j * f j := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hjne : j ≠ jk := (Finset.mem_erase.mp hj).1
        simp [hdef, hjne]
      rw [hrest, hdef]
      simp only [true_and, ↓reduceIte]
      have hsub : (a 0 false jk - m) * f jk + m * f jk = a 0 false jk * f jk := by
        rw [← add_mul, Nat.sub_add_cancel hmf]
      linarith
    have h0t_sum : ∀ f : Fin (n + 1) → ℕ,
        (∑ j : Fin (n + 1), fuseAt k a 0 true j * f j) + m * f jk =
        (∑ j : Fin (n + 1), a 0 true j * f j) + m * f j2k := by
      intro f
      have h2mem : j2k ∈ Finset.univ.erase jk := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ jk),
          ← Finset.add_sum_erase _ _ h2mem,
          ← Finset.add_sum_erase _ (fun j => a 0 true j * f j) (Finset.mem_univ jk),
          ← Finset.add_sum_erase _ (fun j => a 0 true j * f j) h2mem]
      have hrest : ∑ j ∈ (Finset.univ.erase jk).erase j2k, fuseAt k a 0 true j * f j =
          ∑ j ∈ (Finset.univ.erase jk).erase j2k, a 0 true j * f j := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hj2 : j ≠ j2k := (Finset.mem_erase.mp hj).1
        have hj1 : j ≠ jk := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
        simp [hdef, hj1, hj2]
      rw [hrest, hdef, hdef]
      simp only [Bool.true_eq_false, false_and, ↓reduceIte, true_and, hne.symm, and_false]
      have hsub : (a 0 true jk - m) * f jk + m * f jk = a 0 true jk * f jk := by
        rw [← add_mul, Nat.sub_add_cancel hmt]
      have hadd : (a 0 true j2k + m) * f j2k = a 0 true j2k * f j2k + m * f j2k := add_mul _ _ _
      linarith
    have hother : ∀ c : Fin 3, c ≠ 0 → ∀ s j, fuseAt k a c s j = a c s j := by
      intro c hc s j; simp [hdef, hc]
    have hvalid : validRaw (fuseAt k a) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [hdef, hjk0.symm, ha.1]
      · simp [hdef, hjk0.symm, hj2k0.symm, ha.2.1]
      · unfold totalLen
        rw [Fin.sum_univ_three]
        have hc1 : (∑ s : Bool, ∑ j : Fin (n + 1), fuseAt k a 1 s j * weightOf 1 j) =
            ∑ s : Bool, ∑ j : Fin (n + 1), a 1 s j * weightOf 1 j := by
          simp [hother 1 (by decide)]
        have hc2 : (∑ s : Bool, ∑ j : Fin (n + 1), fuseAt k a 2 s j * weightOf 2 j) =
            ∑ s : Bool, ∑ j : Fin (n + 1), a 2 s j * weightOf 2 j := by
          simp [hother 2 (by decide)]
        rw [hc1, hc2, Fintype.sum_bool]
        have hf := h0f_sum (fun j => weightOf 0 j)
        have ht := h0t_sum (fun j => weightOf 0 j)
        have hw : weightOf 0 j2k = 2 * weightOf 0 jk := by
          simp [weightOf, jk, j2k]
        rw [hw, show m * (2 * weightOf 0 jk) = 2 * (m * weightOf 0 jk) by ring] at ht
        have hlen := ha.2.2.1
        unfold totalLen at hlen
        rw [Fin.sum_univ_three, Fintype.sum_bool] at hlen
        omega
      · simp only [hother 1 (by decide), hother 2 (by decide)]; exact ha.2.2.2.1
      · rw [Fin.sum_univ_three]
        have ht := h0t_sum (fun _ => 1)
        simp only [mul_one] at ht
        have h0eq : (∑ j : Fin (n + 1), fuseAt k a 0 true j) = ∑ j : Fin (n + 1), a 0 true j := by omega
        rw [h0eq]
        simp only [hother 1 (by decide), hother 2 (by decide)]
        have hpar := ha.2.2.2.2
        rw [Fin.sum_univ_three] at hpar
        exact hpar
    have hpoly : ∀ u v, polyOfRaw (fuseAt k a) u v = polyOfRaw a u v := by
      intro u v
      unfold polyOfRaw
      rw [Fin.prod_univ_three, Fin.prod_univ_three]
      simp only [hother 1 (by decide), hother 2 (by decide)]
      congr 2
      rw [Fintype.prod_bool, Fintype.prod_bool]
      have h2mem : j2k ∈ Finset.univ.erase jk := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
      have hpf : (∏ j : Fin (n + 1), factorOf 0 false j.val u v ^ fuseAt k a 0 false j) =
          factorOf 0 false jk.val u v ^ (a 0 false jk - m) *
          ∏ j ∈ Finset.univ.erase jk, factorOf 0 false j.val u v ^ a 0 false j := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ jk)]
        congr 1
        · simp [hdef]
        · refine Finset.prod_congr rfl (fun j hj => ?_)
          simp [hdef, (Finset.mem_erase.mp hj).1]
      have hpt : (∏ j : Fin (n + 1), factorOf 0 true j.val u v ^ fuseAt k a 0 true j) =
          factorOf 0 true jk.val u v ^ (a 0 true jk - m) *
          (factorOf 0 true j2k.val u v ^ (a 0 true j2k + m) *
          ∏ j ∈ (Finset.univ.erase jk).erase j2k, factorOf 0 true j.val u v ^ a 0 true j) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ jk),
            ← Finset.mul_prod_erase _ _ h2mem]
        congr 1
        · simp [hdef]
        · congr 1
          · simp [hdef, hne.symm]
          · refine Finset.prod_congr rfl (fun j hj => ?_)
            have hj2 := (Finset.mem_erase.mp hj).1
            have hj1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
            simp [hdef, hj1, hj2]
      have hpfA : (∏ j : Fin (n + 1), factorOf 0 false j.val u v ^ a 0 false j) =
          factorOf 0 false jk.val u v ^ a 0 false jk *
          ∏ j ∈ Finset.univ.erase jk, factorOf 0 false j.val u v ^ a 0 false j :=
        (Finset.mul_prod_erase _ _ (Finset.mem_univ jk)).symm
      have hptA : (∏ j : Fin (n + 1), factorOf 0 true j.val u v ^ a 0 true j) =
          factorOf 0 true jk.val u v ^ a 0 true jk *
          (factorOf 0 true j2k.val u v ^ a 0 true j2k *
          ∏ j ∈ (Finset.univ.erase jk).erase j2k, factorOf 0 true j.val u v ^ a 0 true j) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ jk),
            ← Finset.mul_prod_erase _ _ h2mem]
      rw [hpf, hpt, hpfA, hptA]
      have hfus : factorOf 0 true j2k.val u v =
          factorOf 0 false jk.val u v * factorOf 0 true jk.val u v := by
        simp only [factorOf, jk, j2k, Bool.false_eq_true, ↓reduceIte]
        have : (u * v) ^ (2 * k) = ((u * v) ^ k) ^ 2 := by rw [pow_mul', pow_two]
        rw [this]; ring
      have hsplit2 : factorOf 0 true j2k.val u v ^ (a 0 true j2k + m) =
          factorOf 0 true j2k.val u v ^ a 0 true j2k *
            (factorOf 0 false jk.val u v ^ m * factorOf 0 true jk.val u v ^ m) := by
        rw [pow_add]
        congr 1
        rw [hfus, mul_pow]
      rw [hsplit2]
      have h1 : factorOf 0 false jk.val u v ^ (a 0 false jk - m) * factorOf 0 false jk.val u v ^ m =
          factorOf 0 false jk.val u v ^ a 0 false jk := by
        rw [← pow_add, Nat.sub_add_cancel hmf]
      have h2 : factorOf 0 true jk.val u v ^ (a 0 true jk - m) * factorOf 0 true jk.val u v ^ m =
          factorOf 0 true jk.val u v ^ a 0 true jk := by
        rw [← pow_add, Nat.sub_add_cancel hmt]
      calc (factorOf 0 true jk.val u v ^ (a 0 true jk - m) *
              (factorOf 0 true j2k.val u v ^ a 0 true j2k *
                (factorOf 0 false jk.val u v ^ m * factorOf 0 true jk.val u v ^ m) *
              ∏ j ∈ (Finset.univ.erase jk).erase j2k, factorOf 0 true j.val u v ^ a 0 true j)) *
            (factorOf 0 false jk.val u v ^ (a 0 false jk - m) *
              ∏ j ∈ Finset.univ.erase jk, factorOf 0 false j.val u v ^ a 0 false j)
          = ((factorOf 0 true jk.val u v ^ (a 0 true jk - m) * factorOf 0 true jk.val u v ^ m) *
              (factorOf 0 true j2k.val u v ^ a 0 true j2k *
              ∏ j ∈ (Finset.univ.erase jk).erase j2k, factorOf 0 true j.val u v ^ a 0 true j)) *
            ((factorOf 0 false jk.val u v ^ (a 0 false jk - m) * factorOf 0 false jk.val u v ^ m) *
              ∏ j ∈ Finset.univ.erase jk, factorOf 0 false j.val u v ^ a 0 false j) := by ring
        _ = _ := by rw [h1, h2]
    have hcnt_rel : totalCount (fuseAt k a) + m = totalCount a := by
      unfold totalCount
      rw [Fin.sum_univ_three, Fin.sum_univ_three]
      simp only [hother 1 (by decide), hother 2 (by decide), Fintype.sum_bool]
      have hf := h0f_sum (fun _ => 1)
      have ht := h0t_sum (fun _ => 1)
      simp only [mul_one] at hf ht
      omega
    have hphi_rel : phi (fuseAt k a) = phi a + m := by
      unfold phi
      have ht := h0t_sum (fun j => j.val.factorization 2)
      have hfac : j2k.val.factorization 2 = jk.val.factorization 2 + 1 :=
        factorization_two_mul_two hk.1
      rw [hfac, mul_add, mul_one] at ht
      omega
    refine ⟨hvalid, hpoly, by omega, by omega, ?_, ?_⟩
    · intro j hj
      have hj1 : j ≠ jk := fun h => by have := congrArg Fin.val h; dsimp only [jk] at this; omega
      have hj2 : j ≠ j2k := fun h => by have := congrArg Fin.val h; dsimp only [j2k] at this; omega
      simp [hdef, hj1, hj2]
    · intro _ _
      change fuseAt k a 0 false jk = 0 ∨ fuseAt k a 0 true jk = 0
      rw [hdef, hdef]
      simp only [true_and, ↓reduceIte, Bool.true_eq_false, false_and]
      rcases le_total (a 0 false jk) (a 0 true jk) with h | h
      · left; simp [m, min_eq_left h]
      · right; simp [m, min_eq_right h]
  · have hdef : fuseAt k a = a := by unfold fuseAt; rw [dif_neg hk]
    rw [hdef]
    refine ⟨ha, fun _ _ => rfl, rfl, le_rfl, fun _ _ => ⟨rfl, rfl⟩, ?_⟩
    intro hkpos hkn
    have h2k : n < 2 * k := by omega
    by_contra hboth
    push Not at hboth
    have h1 : 1 ≤ a 0 false ⟨k, by omega⟩ := Nat.pos_of_ne_zero hboth.1
    have h2 : 1 ≤ a 0 true ⟨k, by omega⟩ := Nat.pos_of_ne_zero hboth.2
    have hle : a 0 false ⟨k, by omega⟩ * (2 * k) + a 0 true ⟨k, by omega⟩ * (2 * k) ≤ totalLen a := by
      unfold totalLen
      have hc0 : (∑ s : Bool, ∑ j : Fin (n + 1), a 0 s j * weightOf 0 j) ≤
          ∑ c : Fin 3, ∑ s : Bool, ∑ j : Fin (n + 1), a c s j * weightOf c j :=
        Finset.single_le_sum (f := fun c : Fin 3 => ∑ s : Bool, ∑ j : Fin (n + 1), a c s j * weightOf c j)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ (0 : Fin 3))
      rw [Fintype.sum_bool] at hc0
      have hf := Finset.single_le_sum (f := fun j : Fin (n + 1) => a 0 false j * weightOf 0 j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨k, by omega⟩)
      have ht := Finset.single_le_sum (f := fun j : Fin (n + 1) => a 0 true j * weightOf 0 j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨k, by omega⟩)
      have hw : weightOf 0 (⟨k, by omega⟩ : Fin (n + 1)) = 2 * k := by simp [weightOf]
      rw [hw] at hf ht
      omega
    have htot := ha.2.2.1
    nlinarith

def reduceUpTo {n : ℕ} : ℕ → RawInv n → RawInv n
  | 0, a => a
  | k + 1, a => fuseAt (k + 1) (reduceUpTo k a)

lemma reduceUpTo_props {n : ℕ} (k : ℕ) {a : RawInv n} (ha : validRaw a) :
    validRaw (reduceUpTo k a) ∧
    (∀ u v, polyOfRaw (reduceUpTo k a) u v = polyOfRaw a u v) ∧
    totalCount (reduceUpTo k a) + phi (reduceUpTo k a) = totalCount a + phi a ∧
    totalCount (reduceUpTo k a) ≤ totalCount a ∧
    (∀ j : Fin (n + 1), j.val ≤ k → reduceUpTo k a 0 false j = 0 ∨ reduceUpTo k a 0 true j = 0) := by
  induction k with
  | zero =>
    refine ⟨ha, fun _ _ => rfl, rfl, le_rfl, fun j hj => ?_⟩
    have hj0 : j = 0 := Fin.ext (Nat.eq_zero_of_le_zero hj)
    rw [hj0]; left; exact ha.1
  | succ k ih =>
    obtain ⟨hv, hp, hinv, hle, hred⟩ := ih
    obtain ⟨hv', hp', hinv', hle', hpres, hnew⟩ := fuseAt_props (k + 1) hv
    refine ⟨hv', fun u v => (hp' u v).trans (hp u v), hinv'.trans hinv, hle'.trans hle, ?_⟩
    intro j hj
    by_cases heq : j.val = k + 1
    · have hjeq : j = ⟨k + 1, by omega⟩ := Fin.ext heq
      rw [hjeq]
      exact hnew (by omega) (by omega)
    · have hlt : j.val < k + 1 := by omega
      obtain ⟨h1, h2⟩ := hpres j hlt
      change fuseAt (k + 1) (reduceUpTo k a) 0 false j = 0 ∨ fuseAt (k + 1) (reduceUpTo k a) 0 true j = 0
      rw [h1, h2]
      exact hred j (by omega)

def reduceRaw {n : ℕ} (a : RawInv n) : RawInv n := reduceUpTo n a

lemma reduceRaw_props {n : ℕ} {a : RawInv n} (ha : validRaw a) :
    reducedRaw (reduceRaw a) ∧
    (∀ u v, polyOfRaw (reduceRaw a) u v = polyOfRaw a u v) ∧
    totalCount (reduceRaw a) + phi (reduceRaw a) = totalCount a + phi a ∧
    totalCount (reduceRaw a) ≤ totalCount a := by
  obtain ⟨hv, hp, hinv, hle, hred⟩ := reduceUpTo_props n ha
  exact ⟨⟨hv, fun j => hred j (Nat.le_of_lt_succ j.isLt)⟩, hp, hinv, hle⟩

lemma exists_unfuse_step {n : ℕ} {a : RawInv n} (ha : validRaw a) (hphi : 0 < phi a) :
    ∃ b : RawInv n, validRaw b ∧
      (∀ u v, polyOfRaw b u v = polyOfRaw a u v) ∧
      totalCount b = totalCount a + 1 ∧
      phi b + 1 = phi a := by
  have hex : ∃ j : Fin (n + 1), 0 < a 0 true j * j.val.factorization 2 := by
    by_contra h
    push Not at h
    have hz : phi a = 0 := Finset.sum_eq_zero (fun j _ => Nat.eq_zero_of_le_zero (h j))
    omega
  obtain ⟨j2, hj2⟩ := hex
  have ha_pos : 0 < a 0 true j2 := Nat.pos_of_mul_pos_right hj2
  have hfac_pos : 0 < j2.val.factorization 2 := Nat.pos_of_mul_pos_left hj2
  have hj2_ne0 : j2.val ≠ 0 := by
    intro h0; rw [h0, Nat.factorization_zero, Finsupp.zero_apply] at hfac_pos; omega
  have hdvd : 2 ∣ j2.val := Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hj2_ne0 |>.mpr hfac_pos
  obtain ⟨k, hk_eq⟩ := hdvd
  have hk_pos : 0 < k := by omega
  let jk : Fin (n + 1) := ⟨k, by omega⟩
  have hne : jk ≠ j2 := fun h => by have := congrArg Fin.val h; dsimp only [jk] at this; omega
  have hjk0 : jk ≠ 0 := fun h => by have := congrArg Fin.val h; simp [jk] at this; omega
  let b : RawInv n := fun c s j =>
    if c = 0 ∧ s = false ∧ j = jk then a 0 false jk + 1
    else if c = 0 ∧ s = true ∧ j = jk then a 0 true jk + 1
    else if c = 0 ∧ s = true ∧ j = j2 then a 0 true j2 - 1
    else a c s j
  have h0f_sum : ∀ f : Fin (n + 1) → ℕ,
      (∑ j : Fin (n + 1), b 0 false j * f j) =
      (∑ j : Fin (n + 1), a 0 false j * f j) + f jk := by
    intro f
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ jk),
        ← Finset.add_sum_erase _ (fun j => a 0 false j * f j) (Finset.mem_univ jk)]
    have hrest : ∑ j ∈ Finset.univ.erase jk, b 0 false j * f j =
        ∑ j ∈ Finset.univ.erase jk, a 0 false j * f j := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      simp [b, (Finset.mem_erase.mp hj).1]
    rw [hrest]
    simp only [b, true_and, ↓reduceIte, add_mul, one_mul]
    ring
  have h0t_sum : ∀ f : Fin (n + 1) → ℕ,
      (∑ j : Fin (n + 1), b 0 true j * f j) + f j2 =
      (∑ j : Fin (n + 1), a 0 true j * f j) + f jk := by
    intro f
    have h2mem : j2 ∈ Finset.univ.erase jk := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ jk),
        ← Finset.add_sum_erase _ _ h2mem,
        ← Finset.add_sum_erase _ (fun j => a 0 true j * f j) (Finset.mem_univ jk),
        ← Finset.add_sum_erase _ (fun j => a 0 true j * f j) h2mem]
    have hrest : ∑ j ∈ (Finset.univ.erase jk).erase j2, b 0 true j * f j =
        ∑ j ∈ (Finset.univ.erase jk).erase j2, a 0 true j * f j := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hj2' := (Finset.mem_erase.mp hj).1
      have hj1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      simp [b, hj1, hj2']
    rw [hrest]
    simp only [b, Bool.true_eq_false, false_and, ↓reduceIte, true_and, hne.symm, and_false]
    have hsub : (a 0 true j2 - 1) * f j2 + f j2 = a 0 true j2 * f j2 := by
      calc (a 0 true j2 - 1) * f j2 + f j2 = (a 0 true j2 - 1) * f j2 + 1 * f j2 := by rw [one_mul]
        _ = (a 0 true j2 - 1 + 1) * f j2 := (add_mul _ _ _).symm
        _ = a 0 true j2 * f j2 := by rw [Nat.sub_add_cancel ha_pos]
    have hadd : (a 0 true jk + 1) * f jk = a 0 true jk * f jk + f jk := by rw [add_mul, one_mul]
    linarith
  have hother : ∀ c : Fin 3, c ≠ 0 → ∀ s j, b c s j = a c s j := by
    intro c hc s j; simp [b, hc]
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [b, hjk0.symm, ha.1]
    · have hj2_0 : j2 ≠ 0 := fun h => hj2_ne0 (congrArg Fin.val h)
      simp [b, hjk0.symm, hj2_0.symm, ha.2.1]
    · unfold totalLen
      rw [Fin.sum_univ_three]
      simp only [hother 1 (by decide), hother 2 (by decide)]
      rw [Fintype.sum_bool]
      have hf := h0f_sum (fun j => weightOf 0 j)
      have ht := h0t_sum (fun j => weightOf 0 j)
      have hw : weightOf 0 j2 = 2 * weightOf 0 jk := by simp [weightOf, jk, hk_eq]
      rw [hw] at ht
      have hlen := ha.2.2.1
      unfold totalLen at hlen
      rw [Fin.sum_univ_three, Fintype.sum_bool] at hlen
      omega
    · simp only [hother 1 (by decide), hother 2 (by decide)]; exact ha.2.2.2.1
    · rw [Fin.sum_univ_three]
      have ht := h0t_sum (fun _ => 1)
      simp only [mul_one] at ht
      have h0eq : (∑ j : Fin (n + 1), b 0 true j) = ∑ j : Fin (n + 1), a 0 true j := by omega
      rw [h0eq]
      simp only [hother 1 (by decide), hother 2 (by decide)]
      have hpar := ha.2.2.2.2
      rw [Fin.sum_univ_three] at hpar
      exact hpar
  · intro u v
    unfold polyOfRaw
    rw [Fin.prod_univ_three, Fin.prod_univ_three]
    simp only [hother 1 (by decide), hother 2 (by decide)]
    congr 2
    rw [Fintype.prod_bool, Fintype.prod_bool]
    have h2mem : j2 ∈ Finset.univ.erase jk := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
    have hpf : (∏ j : Fin (n + 1), factorOf 0 false j.val u v ^ b 0 false j) =
        factorOf 0 false jk.val u v ^ (a 0 false jk + 1) *
        ∏ j ∈ Finset.univ.erase jk, factorOf 0 false j.val u v ^ a 0 false j := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ jk)]
      congr 1
      · simp [b]
      · refine Finset.prod_congr rfl (fun j hj => ?_)
        simp [b, (Finset.mem_erase.mp hj).1]
    have hpt : (∏ j : Fin (n + 1), factorOf 0 true j.val u v ^ b 0 true j) =
        factorOf 0 true jk.val u v ^ (a 0 true jk + 1) *
        (factorOf 0 true j2.val u v ^ (a 0 true j2 - 1) *
        ∏ j ∈ (Finset.univ.erase jk).erase j2, factorOf 0 true j.val u v ^ a 0 true j) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ jk),
          ← Finset.mul_prod_erase _ _ h2mem]
      congr 1
      · simp [b]
      · congr 1
        · simp [b, hne.symm]
        · refine Finset.prod_congr rfl (fun j hj => ?_)
          have hj2' := (Finset.mem_erase.mp hj).1
          have hj1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
          simp [b, hj1, hj2']
    have hpfA : (∏ j : Fin (n + 1), factorOf 0 false j.val u v ^ a 0 false j) =
        factorOf 0 false jk.val u v ^ a 0 false jk *
        ∏ j ∈ Finset.univ.erase jk, factorOf 0 false j.val u v ^ a 0 false j :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ jk)).symm
    have hptA : (∏ j : Fin (n + 1), factorOf 0 true j.val u v ^ a 0 true j) =
        factorOf 0 true jk.val u v ^ a 0 true jk *
        (factorOf 0 true j2.val u v ^ a 0 true j2 *
        ∏ j ∈ (Finset.univ.erase jk).erase j2, factorOf 0 true j.val u v ^ a 0 true j) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ jk),
          ← Finset.mul_prod_erase _ _ h2mem]
    rw [hpf, hpt, hpfA, hptA]
    have hfus : factorOf 0 true j2.val u v =
        factorOf 0 false jk.val u v * factorOf 0 true jk.val u v := by
      simp only [factorOf, jk, hk_eq, Bool.false_eq_true, ↓reduceIte]
      have : (u * v) ^ (2 * k) = ((u * v) ^ k) ^ 2 := by rw [pow_mul', pow_two]
      rw [this]; ring
    have h2pow : factorOf 0 true j2.val u v ^ a 0 true j2 =
        factorOf 0 true j2.val u v ^ (a 0 true j2 - 1) * factorOf 0 true j2.val u v := by
      conv_lhs => rw [← Nat.sub_add_cancel ha_pos, pow_succ]
    rw [h2pow, hfus, pow_succ, pow_succ]
    ring
  · unfold totalCount
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [hother 1 (by decide), hother 2 (by decide), Fintype.sum_bool]
    have hf := h0f_sum (fun _ => 1)
    have ht := h0t_sum (fun _ => 1)
    simp only [mul_one] at hf ht
    omega
  · unfold phi
    have ht := h0t_sum (fun j => j.val.factorization 2)
    have hfac : j2.val.factorization 2 = jk.val.factorization 2 + 1 := by
      rw [hk_eq]; exact factorization_two_mul_two hk_pos
    rw [hfac] at ht
    omega

lemma exists_unfuse_any {n : ℕ} {a : RawInv n} (ha : validRaw a) :
    ∀ r ≤ phi a, ∃ b : RawInv n, validRaw b ∧
      (∀ u v, polyOfRaw b u v = polyOfRaw a u v) ∧
      totalCount b = totalCount a + r ∧
      phi b + r = phi a := by
  intro r
  induction r with
  | zero => intro _; exact ⟨a, ha, fun _ _ => rfl, by omega, by omega⟩
  | succ r ih =>
    intro hr
    obtain ⟨b, hb, hp, hcnt, hphi⟩ := ih (by omega)
    obtain ⟨b', hb', hp', hcnt', hphi'⟩ := exists_unfuse_step hb (by omega)
    exact ⟨b', hb', fun u v => (hp' u v).trans (hp u v), by omega, by omega⟩

-- Section 4: Constructing a concrete pinning q from any validRaw b

def zipInterleave {α : Type*} : List α → List α → List α
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => x :: y :: zipInterleave xs ys

lemma zipInterleave_length {α : Type*} : ∀ (xs ys : List α),
    (zipInterleave xs ys).length = xs.length + ys.length
  | [], ys => by simp [zipInterleave]
  | x :: xs, [] => by simp [zipInterleave]
  | x :: xs, y :: ys => by
    simp only [zipInterleave, List.length_cons, zipInterleave_length xs ys]
    omega

lemma zipInterleave_prod {α : Type*} (f : α → ℚ) : ∀ (xs ys : List α),
    ((zipInterleave xs ys).map f).prod = (xs.map f).prod * (ys.map f).prod
  | [], ys => by simp [zipInterleave]
  | x :: xs, [] => by simp [zipInterleave]
  | x :: xs, y :: ys => by
    simp only [zipInterleave, List.map_cons, List.prod_cons, zipInterleave_prod f xs ys]
    ring

lemma zipInterleave_sum {α : Type*} (f : α → ℕ) : ∀ (xs ys : List α),
    ((zipInterleave xs ys).map f).sum = (xs.map f).sum + (ys.map f).sum
  | [], ys => by simp [zipInterleave]
  | x :: xs, [] => by simp [zipInterleave]
  | x :: xs, y :: ys => by
    simp only [zipInterleave, List.map_cons, List.sum_cons, zipInterleave_sum f xs ys]
    omega

lemma zipInterleave_get_even {α : Type*} : ∀ (xs ys : List α), xs.length = ys.length →
    ∀ i (hi : i < (zipInterleave xs ys).length),
      (i % 2 = 0 → (zipInterleave xs ys)[i]'hi ∈ xs) ∧
      (i % 2 = 1 → (zipInterleave xs ys)[i]'hi ∈ ys)
  | [], [], _, i, hi => by simp [zipInterleave] at hi
  | x :: xs, y :: ys, hlen, i, hi => by
    simp only [List.length_cons] at hlen
    match i with
    | 0 => simp [zipInterleave]
    | 1 => simp [zipInterleave]
    | i + 2 =>
      have hi' : i < (zipInterleave xs ys).length := by
        simp only [zipInterleave, List.length_cons] at hi; omega
      obtain ⟨he, ho⟩ := zipInterleave_get_even xs ys (by omega) i hi'
      refine ⟨fun h => List.mem_cons_of_mem _ (he (by omega)),
              fun h => List.mem_cons_of_mem _ (ho (by omega))⟩

def listOfClass {n : ℕ} (a : RawInv n) (c : Fin 3) : List (Fin 3 × Bool × Fin (n + 1)) :=
  [false, true].flatMap (fun s =>
    (List.finRange (n + 1)).flatMap (fun j => List.replicate (a c s j) (c, s, j)))

lemma mem_listOfClass {n : ℕ} (a : RawInv n) (c : Fin 3) (x : Fin 3 × Bool × Fin (n + 1)) :
    x ∈ listOfClass a c → x.1 = c := by
  intro hx
  unfold listOfClass at hx
  simp only [List.mem_flatMap, List.mem_replicate] at hx
  rcases hx with ⟨s, _, j, _, _, rfl⟩
  rfl

lemma listOfClass_length {n : ℕ} (a : RawInv n) (c : Fin 3) :
    (listOfClass a c).length = ∑ s : Bool, ∑ j : Fin (n + 1), a c s j := by
  unfold listOfClass
  simp only [List.length_flatMap, List.length_replicate, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, Fintype.sum_bool]
  have hfin : ∀ s : Bool, ((List.finRange (n + 1)).map (fun j => a c s j)).sum =
      ∑ j : Fin (n + 1), a c s j := by
    intro s
    exact (Fin.sum_univ_def (fun j => a c s j)).symm
  rw [hfin false, hfin true, add_comm]

lemma list_sum_flatMap_nat {α : Type*} (l : List α) (g : α → List ℕ) :
    (l.flatMap g).sum = (l.map (fun x => (g x).sum)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, List.sum_append, ih]

lemma list_prod_flatMap_rat {α : Type*} (l : List α) (g : α → List ℚ) :
    (l.flatMap g).prod = (l.map (fun x => (g x).prod)).prod := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, List.prod_append, ih]

lemma listOfClass_sum {n : ℕ} (a : RawInv n) (c : Fin 3) (f : Fin 3 × Bool × Fin (n + 1) → ℕ) :
    ((listOfClass a c).map f).sum = ∑ s : Bool, ∑ j : Fin (n + 1), a c s j * f (c, s, j) := by
  unfold listOfClass
  simp only [List.map_flatMap, list_sum_flatMap_nat, List.map_replicate, List.sum_replicate,
    smul_eq_mul, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Fintype.sum_bool]
  have hfin : ∀ s : Bool, ((List.finRange (n + 1)).map (fun j => a c s j * f (c, s, j))).sum =
      ∑ j : Fin (n + 1), a c s j * f (c, s, j) := by
    intro s
    exact (Fin.sum_univ_def (fun j => a c s j * f (c, s, j))).symm
  rw [hfin false, hfin true, add_comm]

lemma listOfClass_prod {n : ℕ} (a : RawInv n) (c : Fin 3) (f : Fin 3 × Bool × Fin (n + 1) → ℚ) :
    ((listOfClass a c).map f).prod = ∏ s : Bool, ∏ j : Fin (n + 1), (f (c, s, j)) ^ (a c s j) := by
  unfold listOfClass
  simp only [List.map_flatMap, list_prod_flatMap_rat, List.map_replicate, List.prod_replicate,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Fintype.prod_bool]
  have hfin : ∀ s : Bool, ((List.finRange (n + 1)).map (fun j => (f (c, s, j)) ^ (a c s j))).prod =
      ∏ j : Fin (n + 1), (f (c, s, j)) ^ (a c s j) := by
    intro s
    exact (Fin.prod_univ_def (fun j => (f (c, s, j)) ^ (a c s j))).symm
  rw [hfin false, hfin true, mul_comm]

lemma list_prod_eq_fin_prod {α : Type*} (L : List α) (f : α → ℚ) :
    (L.map f).prod = ∏ r : Fin L.length, f (L[r.val]'r.isLt) := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.prod_cons, ih]
    symm
    exact Fin.prod_univ_succ (fun r : Fin (xs.length + 1) => f ((x :: xs)[r.val]'r.isLt))

set_option maxHeartbeats 800000 in
lemma exists_q_of_validRaw {t : ℕ} {a : RawInv (t + 1)} (ha : validRaw a) :
    ∃ q : Fin (2 * (t + 1)) → Option Bool,
      pinCount t q = totalCount a ∧
      ∀ u v, polyQ t q u v = polyOfRaw a u v := by
  haveI : NeZero (2 * (t + 1)) := ⟨by omega⟩
  let L0 := listOfClass a 0
  let L1 := listOfClass a 1
  let L2 := listOfClass a 2
  let L := L0 ++ zipInterleave L2 L1
  have hL12 : L2.length = L1.length := by
    simp only [L1, L2, listOfClass_length]
    exact ha.2.2.2.1.symm
  have hLlen : L.length = totalCount a := by
    simp only [L, List.length_append, zipInterleave_length, L0, L1, L2, listOfClass_length, totalCount]
    rw [Fin.sum_univ_three]
    omega
  have hLpos : 0 < L.length := by rw [hLlen]; exact validRaw_pos_totalCount ha
  let wfn : Fin 3 × Bool × Fin (t + 2) → ℕ := fun x => weightOf x.1 x.2.2
  have hLsum : (L.map wfn).sum = 2 * (t + 1) := by
    simp only [L, List.map_append, List.sum_append, zipInterleave_sum, L0, L1, L2, listOfClass_sum, wfn]
    have htot := ha.2.2.1
    unfold totalLen at htot
    rw [Fin.sum_univ_three] at htot
    omega
  have hLwt_pos : ∀ x ∈ L, 1 ≤ wfn x := by
    intro x hx
    simp only [L, List.mem_append] at hx
    rcases hx with h0 | h12
    · unfold L0 listOfClass at h0
      simp only [List.mem_flatMap, List.mem_replicate] at h0
      rcases h0 with ⟨s, _, j, _, hne, rfl⟩
      have hj0 : j.val ≠ 0 := by
        intro hv
        have hj : j = 0 := Fin.ext hv
        rw [hj] at hne
        cases s
        · exact hne ha.1
        · exact hne ha.2.1
      simp only [wfn, weightOf, ↓reduceIte]; omega
    · have h12' : x.1 = 1 ∨ x.1 = 2 := by
        have hmem := List.mem_iff_getElem.mp h12
        rcases hmem with ⟨i, hi, rfl⟩
        obtain ⟨he, ho⟩ := zipInterleave_get_even L2 L1 hL12 i hi
        by_cases hpar : i % 2 = 0
        · right; exact mem_listOfClass a 2 _ (he hpar)
        · left; exact mem_listOfClass a 1 _ (ho (by omega))
      rcases h12' with h | h <;> simp [wfn, weightOf, h]
  have hLsgn_even : (L.map (fun x => if x.2.1 then 1 else 0)).sum % 2 = 0 := by
    simp only [L, List.map_append, List.sum_append, zipInterleave_sum, L0, L1, L2, listOfClass_sum]
    have hpar := ha.2.2.2.2
    rw [Fin.sum_univ_three] at hpar
    simp only [Fintype.sum_bool, ↓reduceIte, mul_one, Bool.false_eq_true, mul_zero,
      Finset.sum_const_zero, add_zero]
    omega
  have hLprod : ∀ u v, (L.map (fun x => factorOf x.1 x.2.1 x.2.2.val u v)).prod = polyOfRaw a u v := by
    intro u v
    simp only [L, List.map_append, List.prod_append, zipInterleave_prod, L0, L1, L2, listOfClass_prod]
    unfold polyOfRaw
    rw [Fin.prod_univ_three]
    ring
  -- Running sums (positions) and running sign parities
  let pos : ℕ → ℕ := fun r => ((L.take r).map wfn).sum
  let par : ℕ → Bool := fun r => decide (((L.take r).map (fun x => if x.2.1 then 1 else 0)).sum % 2 = 1)
  have hpos_zero : pos 0 = 0 := by simp [pos]
  have hpos_end : pos L.length = 2 * (t + 1) := by simp only [pos, List.take_length, hLsum]
  have hpos_step : ∀ r (hr : r < L.length), pos (r + 1) = pos r + wfn (L[r]'hr) := by
    intro r hr
    simp only [pos, List.take_succ_eq_append_getElem hr, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton]
  have hpar_zero : par 0 = false := by simp [par]
  have hpar_end : par L.length = false := by
    simp only [par, List.take_length, hLsgn_even]
    decide
  have hpar_step : ∀ r (hr : r < L.length),
      sgn (par (r + 1)) * sgn (par r) = if (L[r]'hr).2.1 then -1 else 1 := by
    intro r hr
    simp only [par, List.take_succ_eq_append_getElem hr, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton]
    set S := ((L.take r).map (fun x => if x.2.1 then 1 else 0)).sum
    cases h : (L[r]'hr).2.1
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      exact sgn_mul_self _
    · simp only [↓reduceIte]
      by_cases hS : S % 2 = 1
      · have hS1 : (S + 1) % 2 ≠ 1 := by omega
        simp [hS, hS1, sgn]
      · have hS1 : (S + 1) % 2 = 1 := by omega
        simp [hS, hS1, sgn]
  have hpos_strict : ∀ r1 r2, r1 < r2 → r2 ≤ L.length → pos r1 < pos r2 := by
    intro r1 r2 h12 h2
    induction r2 with
    | zero => omega
    | succ r2 ih =>
      have hw : 1 ≤ wfn (L[r2]'(by omega)) := hLwt_pos _ (List.getElem_mem _)
      rw [hpos_step r2 (by omega)]
      by_cases heq : r1 = r2
      · subst heq; omega
      · have := ih (by omega) (by omega); omega
  have hpos_lt : ∀ r, r < L.length → pos r < 2 * (t + 1) := by
    intro r hr
    calc pos r < pos L.length := hpos_strict r L.length hr le_rfl
      _ = 2 * (t + 1) := hpos_end
  have hpos_parity : ∀ r (hr : r < L.length),
      ((L[r]'hr).1 = 0 → pos (r + 1) % 2 = 0) ∧
      ((L[r]'hr).1 = 1 → pos (r + 1) % 2 = 0) ∧
      ((L[r]'hr).1 = 2 → pos (r + 1) % 2 = 1) := by
    have hL0_even : ∀ k ≤ L0.length, pos k % 2 = 0 := by
      intro k
      induction k with
      | zero => intro _; simp [pos]
      | succ k ih =>
        intro hk
        have hkL : k < L.length := by simp only [L, List.length_append]; omega
        rw [hpos_step k hkL]
        have hmem : L[k]'hkL ∈ L0 := by
          simp only [L, List.getElem_append_left (by omega : k < L0.length)]
          exact List.getElem_mem _
        have hc0 : (L[k]'hkL).1 = 0 := mem_listOfClass a 0 _ hmem
        have hwev : wfn (L[k]'hkL) % 2 = 0 := by simp [wfn, weightOf, hc0]
        have := ih (by omega)
        omega
    have hzip_par : ∀ m ≤ (zipInterleave L2 L1).length,
        pos (L0.length + m) % 2 = m % 2 := by
      intro m
      induction m with
      | zero => intro _; simpa using hL0_even L0.length le_rfl
      | succ m ih =>
        intro hm
        have hkL : L0.length + m < L.length := by simp only [L, List.length_append]; omega
        rw [show L0.length + (m + 1) = (L0.length + m) + 1 by omega, hpos_step _ hkL]
        have hget : L[L0.length + m]'hkL = (zipInterleave L2 L1)[m]'(by omega) := by
          simp only [L, List.getElem_append_right (Nat.le_add_right L0.length m),
            Nat.add_sub_cancel_left]
        obtain ⟨he, ho⟩ := zipInterleave_get_even L2 L1 hL12 m (by omega)
        have hc : (L[L0.length + m]'hkL).1 ≠ 0 := by
          rw [hget]
          by_cases hmp : m % 2 = 0
          · rw [mem_listOfClass a 2 _ (he hmp)]; decide
          · rw [mem_listOfClass a 1 _ (ho (by omega))]; decide
        have hwodd : wfn (L[L0.length + m]'hkL) % 2 = 1 := by
          simp [wfn, weightOf, hc]
        have := ih (by omega)
        omega
    intro r hr
    by_cases hr0 : r < L0.length
    · have hmem : L[r]'hr ∈ L0 := by
        simp only [L, List.getElem_append_left hr0]; exact List.getElem_mem _
      have hc0 : (L[r]'hr).1 = 0 := mem_listOfClass a 0 _ hmem
      refine ⟨fun _ => hL0_even (r + 1) (by omega), (fun h => by rw [hc0] at h; cases h),
              (fun h => by rw [hc0] at h; cases h)⟩
    · set m := r - L0.length
      have hrm : r = L0.length + m := by omega
      have hm_lt : m < (zipInterleave L2 L1).length := by
        simp only [L, List.length_append] at hr; omega
      have hget : L[r]'hr = (zipInterleave L2 L1)[m]'hm_lt := by
        simp only [L, List.getElem_append_right (by omega : L0.length ≤ r)]
        rfl
      obtain ⟨he, ho⟩ := zipInterleave_get_even L2 L1 hL12 m hm_lt
      have hp1 : pos (r + 1) % 2 = (m + 1) % 2 := by
        rw [show r + 1 = L0.length + (m + 1) by omega]
        exact hzip_par (m + 1) (by omega)
      by_cases hmp : m % 2 = 0
      · have hc2 : (L[r]'hr).1 = 2 := by rw [hget]; exact mem_listOfClass a 2 _ (he hmp)
        refine ⟨(fun h => by rw [hc2] at h; cases h), (fun h => by rw [hc2] at h; cases h),
                (fun _ => by omega)⟩
      · have hc1 : (L[r]'hr).1 = 1 := by rw [hget]; exact mem_listOfClass a 1 _ (ho (by omega))
        refine ⟨(fun h => by rw [hc1] at h; cases h), (fun _ => by omega),
                (fun h => by rw [hc1] at h; cases h)⟩
  -- Define q by placing pins at pos r (for r : Fin L.length) with value par r
  let pinIdx : Fin L.length ↪ Fin (2 * (t + 1)) :=
    ⟨fun r => ⟨pos r.val, hpos_lt r.val r.isLt⟩, fun r1 r2 h => by
      have hv : pos r1.val = pos r2.val := congrArg Fin.val h
      apply Fin.ext
      rcases lt_trichotomy r1.val r2.val with hlt | heq | hgt
      · exact absurd hv (ne_of_lt (hpos_strict r1.val r2.val hlt (le_of_lt r2.isLt)))
      · exact heq
      · exact absurd hv.symm (ne_of_lt (hpos_strict r2.val r1.val hgt (le_of_lt r1.isLt)))⟩
  classical
  let q : Fin (2 * (t + 1)) → Option Bool := fun k =>
    if h : ∃ r : Fin L.length, pinIdx r = k then some (par h.choose.val) else none
  have hq_pin : ∀ r : Fin L.length, q (pinIdx r) = some (par r.val) := by
    intro r
    have hex : ∃ r' : Fin L.length, pinIdx r' = pinIdx r := ⟨r, rfl⟩
    simp only [q, dif_pos hex]
    congr 1
    exact congrArg (fun x : Fin L.length => par x.val) (pinIdx.injective hex.choose_spec)
  have hq_ne_iff : ∀ k : Fin (2 * (t + 1)), q k ≠ none ↔ ∃ r : Fin L.length, pinIdx r = k := by
    intro k
    by_cases h : ∃ r : Fin L.length, pinIdx r = k
    · simp [q, dif_pos h, h]
    · simp [q, dif_neg h, h]
  have hq_nonempty : ∃ k, q k ≠ none := ⟨pinIdx ⟨0, hLpos⟩, by rw [hq_pin]; simp⟩
  have hpinCount : pinCount t q = totalCount a := by
    rw [← hLlen]
    unfold pinCount
    have hfilt : Finset.univ.filter (fun k => q k ≠ none) = Finset.univ.image pinIdx := by
      ext k; simp [hq_ne_iff]
    rw [hfilt, Finset.card_image_of_injective _ pinIdx.injective, Finset.card_univ, Fintype.card_fin]
  refine ⟨q, hpinCount, fun u v => ?_⟩
  rw [polyQ_eq_prod_pins q hq_nonempty u v, ← hLprod u v, list_prod_eq_fin_prod]
  -- Biject r : Fin L.length to PinType q via endPin r = pinIdx ⟨(r.val + 1) % L.length, _⟩
  let endPin : Fin L.length → PinType q := fun r =>
    ⟨pinIdx ⟨(r.val + 1) % L.length, Nat.mod_lt _ hLpos⟩, by rw [hq_pin]; simp⟩
  have hendPin_bij : Function.Bijective endPin := by
    constructor
    · intro r1 r2 h
      have hidx := pinIdx.injective (congrArg Subtype.val h)
      have hmod : (r1.val + 1) % L.length = (r2.val + 1) % L.length := congrArg Fin.val hidx
      apply Fin.ext
      by_cases h1 : r1.val + 1 = L.length <;> by_cases h2 : r2.val + 1 = L.length
      · omega
      · rw [h1, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hmod; omega
      · rw [h2, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hmod; omega
      · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod; omega
    · intro b
      obtain ⟨r, hr⟩ := (hq_ne_iff b.1).mp b.2
      refine ⟨⟨(r.val + L.length - 1) % L.length, Nat.mod_lt _ hLpos⟩, ?_⟩
      apply Subtype.ext
      change pinIdx ⟨((r.val + L.length - 1) % L.length + 1) % L.length, _⟩ = b.1
      rw [← hr]
      congr 1; apply Fin.ext
      dsimp only
      by_cases hr0 : r.val = 0
      · rw [hr0, zero_add, Nat.mod_eq_of_lt (by omega : L.length - 1 < L.length),
            Nat.sub_add_cancel hLpos, Nat.mod_self]
      · have h1 : (r.val + L.length - 1) % L.length = r.val - 1 := by
          rw [show r.val + L.length - 1 = (r.val - 1) + L.length by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [h1, Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt r.isLt]
  rw [← Fintype.prod_bijective endPin hendPin_bij _ _ (fun _ => rfl)]
  refine Finset.prod_congr rfl (fun r _ => ?_)
  -- For each r : Fin L.length, show prevPinDist (endPin r) = wfn (L[r]), arcType, arcSign, arcJ match L[r]
  set w := wfn (L[r.val]'r.isLt)
  have hw_pos : 1 ≤ w := hLwt_pos _ (List.getElem_mem _)
  have hw_le : w ≤ 2 * (t + 1) := by
    have h1 := hpos_step r.val r.isLt
    have h2 : pos (r.val + 1) ≤ pos L.length := by
      by_cases he : r.val + 1 = L.length
      · rw [he]
      · exact le_of_lt (hpos_strict _ _ (by omega) le_rfl)
    omega
  have hend_val : (endPin r).1 = Fin.ofNat (2 * (t + 1)) (pos (r.val + 1)) := by
    by_cases hlast : r.val + 1 = L.length
    · apply Fin.ext
      change pos ((r.val + 1) % L.length) = pos (r.val + 1) % (2 * (t + 1))
      rw [hlast, Nat.mod_self, hpos_zero, hpos_end, Nat.mod_self]
    · apply Fin.ext
      change pos ((r.val + 1) % L.length) = pos (r.val + 1) % (2 * (t + 1))
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (hpos_lt _ (by omega))]
  have hprev_eq : (endPin r).1 - 1 - (⟨w - 1, by omega⟩ : Fin (2 * (t + 1))) = pinIdx r := by
    rw [hend_val]
    have hw1 : (1 : Fin (2 * (t + 1))) + ⟨w - 1, by omega⟩ = Fin.ofNat (2 * (t + 1)) w := by
      apply Fin.ext
      rw [Fin.val_add, fin_one_val t, Fin.val_ofNat]
      dsimp only
      rw [Nat.add_sub_cancel' hw_pos]
    rw [sub_sub, hw1, hpos_step r.val r.isLt, ofNat_fin_add, add_sub_cancel_right]
    exact ofNat_fin_eq (pos r.val) (hpos_lt r.val r.isLt)
  have hraw_eq : prevPinRaw q hq_nonempty (endPin r).1 = ⟨w - 1, by omega⟩ := by
    apply le_antisymm
    · refine Finset.min'_le _ (⟨w - 1, by omega⟩ : Fin (2 * (t + 1))) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
      rw [hprev_eq, hq_pin]; simp
    · by_contra hlt
      push Not at hlt
      set m := prevPinRaw q hq_nonempty (endPin r).1
      have hmw : m.val + 1 < w := by
        have : m.val < w - 1 := hlt
        omega
      have hne := prevPinRaw_spec q hq_nonempty (endPin r).1
      obtain ⟨r', hr'⟩ := (hq_ne_iff _).mp hne
      have hk_val : ((endPin r).1 - 1 - m).val = pos (r.val + 1) - (m.val + 1) := by
        have hpos_ge : m.val + 1 ≤ pos (r.val + 1) := by
          have := hpos_step r.val r.isLt; omega
        have hpos_le : pos (r.val + 1) ≤ 2 * (t + 1) := by
          by_cases he : r.val + 1 = L.length
          · rw [he, hpos_end]
          · exact le_of_lt (hpos_lt _ (by omega))
        have heq : (endPin r).1 - 1 - m = Fin.ofNat (2 * (t + 1)) (pos (r.val + 1) - (m.val + 1)) := by
          rw [hend_val, sub_sub]
          have hm1 : (1 : Fin (2 * (t + 1))) + m = Fin.ofNat (2 * (t + 1)) (m.val + 1) := by
            apply Fin.ext
            rw [Fin.val_add, fin_one_val t, Fin.val_ofNat, Nat.add_comm]
          rw [hm1]
          have hadd : Fin.ofNat (2 * (t + 1)) (pos (r.val + 1) - (m.val + 1)) +
              Fin.ofNat (2 * (t + 1)) (m.val + 1) = Fin.ofNat (2 * (t + 1)) (pos (r.val + 1)) := by
            rw [← ofNat_fin_add, Nat.sub_add_cancel hpos_ge]
          rw [← hadd, add_sub_cancel_right]
        rw [heq, Fin.val_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hpos_r' : pos r'.val = pos (r.val + 1) - (m.val + 1) := by
        have := congrArg Fin.val hr'
        change pos r'.val = ((endPin r).1 - 1 - m).val at this
        exact this.trans hk_val
      have hstep := hpos_step r.val r.isLt
      have hbetween : pos r.val < pos r'.val ∧ pos r'.val < pos (r.val + 1) := by omega
      rcases lt_or_ge r'.val r.val with hlt1 | hge1
      · have := hpos_strict r'.val r.val hlt1 (le_of_lt r.isLt); omega
      · by_cases heq1 : r'.val = r.val
        · rw [heq1] at hbetween; omega
        · have hge2 : r.val + 1 ≤ r'.val := by omega
          by_cases heq2 : r'.val = r.val + 1
          · rw [heq2] at hbetween; omega
          · have := hpos_strict (r.val + 1) r'.val (by omega) (le_of_lt r'.isLt); omega
  have hdist : prevPinDist q hq_nonempty (endPin r).1 = w := by
    unfold prevPinDist; rw [hraw_eq]; dsimp only; omega
  have hprevPin : (prevPin q hq_nonempty (endPin r)).1 = pinIdx r := by
    change (endPin r).1 - 1 - prevPinRaw q hq_nonempty (endPin r).1 = pinIdx r
    rw [hraw_eq, hprev_eq]
  have hend_par : (endPin r).1.val % 2 = pos (r.val + 1) % 2 := by
    rw [hend_val, Fin.val_ofNat]
    exact Nat.mod_mod_of_dvd _ (dvd_mul_right 2 (t + 1))
  have htype : arcType q hq_nonempty (endPin r) = (L[r.val]'r.isLt).1 := by
    unfold arcType
    rw [hdist, hend_par]
    obtain ⟨hp0, hp1, hp2⟩ := hpos_parity r.val r.isLt
    generalize hc : (L[r.val]'r.isLt).1 = c
    fin_cases c
    · have hw0 : w % 2 = 0 := by simp [w, wfn, weightOf, hc]
      simp [hw0]
    · have hw1 : w % 2 = 1 := by simp [w, wfn, weightOf, hc]
      have hpe := hp1 hc
      simp [hw1, hpe]
    · have hw1 : w % 2 = 1 := by simp [w, wfn, weightOf, hc]
      have hpo := hp2 hc
      simp [hw1, hpo]
  have hJ : (arcJ q hq_nonempty (endPin r)).val = (L[r.val]'r.isLt).2.2.val := by
    unfold arcJ
    dsimp only
    rw [hdist]
    dsimp only [w, wfn, weightOf]
    by_cases hc : (L[r.val]'r.isLt).1 = 0 <;> simp [hc] <;> omega
  have hsgn : arcSign q hq_nonempty (endPin r) = (L[r.val]'r.isLt).2.1 := by
    have he1 : epsQ q (endPin r).1 = sgn (par (r.val + 1)) := by
      by_cases hlast : r.val + 1 = L.length
      · have hpin0 : (endPin r).1 = pinIdx ⟨0, hLpos⟩ := by
          change pinIdx ⟨(r.val + 1) % L.length, _⟩ = pinIdx ⟨0, hLpos⟩
          congr 1; apply Fin.ext; simp [hlast]
        rw [hpin0, epsQ, hq_pin, hlast, hpar_end, hpar_zero]
      · have hpin1 : (endPin r).1 = pinIdx ⟨r.val + 1, by omega⟩ := by
          change pinIdx ⟨(r.val + 1) % L.length, _⟩ = pinIdx ⟨r.val + 1, by omega⟩
          congr 1; apply Fin.ext; simp [Nat.mod_eq_of_lt (by omega : r.val + 1 < L.length)]
        rw [hpin1, epsQ, hq_pin]
    have he2 : epsQ q (prevPin q hq_nonempty (endPin r)).1 = sgn (par r.val) := by
      rw [hprevPin, epsQ, hq_pin]
    unfold arcSign
    rw [he1, he2, hpar_step r.val r.isLt]
    cases (L[r.val]'r.isLt).2.1 <;> norm_num
  rw [htype, hsgn, hJ]

-- Section 5: Uniqueness of polyOfRaw on reducedRaw

noncomputable def factorPolyU (c : Fin 3) (s : Bool) (j : ℕ) : Polynomial ℚ :=
  1 + Polynomial.C (if s then (-1 : ℚ) else 1) *
    match c with
    | 0 => Polynomial.C ((1 / 2 : ℚ) ^ j) * Polynomial.X ^ j
    | 1 => Polynomial.C ((1 / 2 : ℚ) ^ j) * Polynomial.X ^ (j + 1)
    | 2 => Polynomial.C ((1 / 2 : ℚ) ^ (j + 1)) * Polynomial.X ^ j

lemma eval_factorPolyU (c : Fin 3) (s : Bool) (j : ℕ) (u : ℚ) :
    (factorPolyU c s j).eval u = factorOf c s j u (1 / 2) := by
  unfold factorPolyU factorOf
  fin_cases c <;> simp [mul_pow] <;> ring

noncomputable def polyRawU {n : ℕ} (a : RawInv n) : Polynomial ℚ :=
  ∏ c : Fin 3, ∏ s : Bool, ∏ j : Fin (n + 1), (factorPolyU c s j.val) ^ (a c s j)

lemma eval_polyRawU {n : ℕ} (a : RawInv n) (u : ℚ) :
    (polyRawU a).eval u = polyOfRaw a u (1 / 2) := by
  unfold polyRawU polyOfRaw
  simp only [Polynomial.eval_prod, Polynomial.eval_pow, eval_factorPolyU]

noncomputable def factorPolyV (c : Fin 3) (s : Bool) (j : ℕ) : Polynomial ℚ :=
  1 + Polynomial.C (if s then (-1 : ℚ) else 1) *
    match c with
    | 0 => Polynomial.C ((1 / 2 : ℚ) ^ j) * Polynomial.X ^ j
    | 1 => Polynomial.C ((1 / 2 : ℚ) ^ (j + 1)) * Polynomial.X ^ j
    | 2 => Polynomial.C ((1 / 2 : ℚ) ^ j) * Polynomial.X ^ (j + 1)

lemma eval_factorPolyV (c : Fin 3) (s : Bool) (j : ℕ) (v : ℚ) :
    (factorPolyV c s j).eval v = factorOf c s j (1 / 2) v := by
  unfold factorPolyV factorOf
  fin_cases c <;> simp [mul_pow] <;> ring

noncomputable def polyRawV {n : ℕ} (a : RawInv n) : Polynomial ℚ :=
  ∏ c : Fin 3, ∏ s : Bool, ∏ j : Fin (n + 1), (factorPolyV c s j.val) ^ (a c s j)

lemma eval_polyRawV {n : ℕ} (a : RawInv n) (v : ℚ) :
    (polyRawV a).eval v = polyOfRaw a (1 / 2) v := by
  unfold polyRawV polyOfRaw
  simp only [Polynomial.eval_prod, Polynomial.eval_pow, eval_factorPolyV]

lemma poly_eq_of_eq_on_unit {P Q : Polynomial ℚ}
    (h : ∀ u : ℚ, 0 < u → u < 1 → P.eval u = Q.eval u) : P = Q := by
  apply sub_eq_zero.mp
  set D := P - Q
  set pts : Finset ℚ := (Finset.range (D.natDegree + 1)).image (fun k : ℕ => (1 : ℚ) / ((k : ℚ) + 2))
  have hcard : pts.card = D.natDegree + 1 := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b hab
      have ha : (0 : ℚ) < (a : ℚ) + 2 := by positivity
      have hb : (0 : ℚ) < (b : ℚ) + 2 := by positivity
      have heq : (a : ℚ) + 2 = (b : ℚ) + 2 := by
        have := (div_eq_div_iff ha.ne' hb.ne').mp hab; linarith
      exact_mod_cast (show (a : ℚ) = (b : ℚ) by linarith)
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' D pts ?_ (by omega)
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨k, _, rfl⟩
  have hk : (0 : ℚ) < (k : ℚ) + 2 := by positivity
  have hx0 : 0 < (1 : ℚ) / (k + 2 : ℚ) := div_pos one_pos hk
  have hx1 : (1 : ℚ) / (k + 2 : ℚ) < 1 := rat_div_lt_one hk (by linarith [Nat.cast_nonneg (α := ℚ) k])
  simp only [D, Polynomial.eval_sub, h _ hx0 hx1, sub_self]

lemma factorPolyU_ne_zero (c : Fin 3) (s : Bool) (j : ℕ) (h0 : ¬ (c = 0 ∧ j = 0)) :
    factorPolyU c s j ≠ 0 := by
  intro h
  have hv := congrArg (Polynomial.eval (0 : ℚ)) h
  rw [Polynomial.eval_zero, eval_factorPolyU] at hv
  unfold factorOf at hv
  fin_cases c
  · have hj : j ≠ 0 := fun hj0 => h0 ⟨rfl, hj0⟩
    simp [zero_pow hj] at hv
  · simp [zero_pow (Nat.succ_ne_zero j)] at hv
  · by_cases hj : j = 0
    · subst hj; cases s <;> norm_num at hv
    · simp [zero_pow hj] at hv

lemma rootMultiplicity_one_of_deriv {p : Polynomial ℂ} {z : ℂ}
    (hp : p ≠ 0) (hz : p.eval z = 0) (hd : p.derivative.eval z ≠ 0) :
    p.rootMultiplicity z = 1 := by
  have h1 : 1 ≤ p.rootMultiplicity z := by
    rw [Polynomial.le_rootMultiplicity_iff hp, pow_one]
    exact Polynomial.dvd_iff_isRoot.mpr hz
  have h2 : ¬ 2 ≤ p.rootMultiplicity z := by
    rw [Polynomial.le_rootMultiplicity_iff hp]
    rintro ⟨q, hq⟩
    have hder := congrArg (fun f : Polynomial ℂ => f.derivative.eval z) hq
    simp only [Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_sub,
      Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, mul_one,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_pow (by decide : 2 ≠ 0),
      Nat.add_sub_cancel, pow_one, mul_zero, zero_mul, add_zero] at hder
    norm_num at hder
    exact hd hder
  omega

lemma rootMultiplicity_pow_eq (p : Polynomial ℂ) (k : ℕ) (z : ℂ) :
    (p ^ k).rootMultiplicity z = k * p.rootMultiplicity z := by
  classical
  have h1 : (1 : Polynomial ℂ).rootMultiplicity z = 0 :=
    Polynomial.rootMultiplicity_eq_zero_iff.mpr (fun h => by simp [Polynomial.IsRoot] at h)
  by_cases hp : p = 0
  · subst hp
    cases k with
    | zero => simp [h1]
    | succ k => simp [zero_pow (Nat.succ_ne_zero k)]
  · induction k with
    | zero => simp [h1]
    | succ k ih =>
      rw [pow_succ, Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero k hp) hp), ih]
      ring

lemma rootMultiplicity_prod_pow {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) (e : ι → ℕ)
    (z : ℂ) (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, (f i) ^ (e i)).rootMultiplicity z = ∑ i ∈ s, e i * (f i).rootMultiplicity z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hfa : (f a) ^ (e a) ≠ 0 := pow_ne_zero _ (hf a (Finset.mem_insert_self a s))
    have hfs : (∏ i ∈ s, (f i) ^ (e i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i hi => pow_ne_zero _ (hf i (Finset.mem_insert_of_mem hi)))
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hfa hfs),
        rootMultiplicity_pow_eq,
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

noncomputable def radC (j : ℕ) : ℝ := ((2 : ℝ) ^ j) ^ ((1 : ℝ) / (j + 1 : ℝ))

lemma radC_pos (j : ℕ) : 0 < radC j := by
  unfold radC; positivity

lemma radC_pow (j : ℕ) : (radC j) ^ (j + 1) = (2 : ℝ) ^ j := by
  unfold radC
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have h1 : (1 : ℝ) / ((j : ℝ) + 1) * ((j + 1 : ℕ) : ℝ) = 1 := by
    push_cast; field_simp
  rw [h1, Real.rpow_one]

lemma radC_lt_two (j : ℕ) : radC j < 2 := by
  have h : (radC j) ^ (j + 1) < (2 : ℝ) ^ (j + 1) := by
    rw [radC_pow, pow_succ]
    have : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    linarith
  exact lt_of_pow_lt_pow_left₀ (j + 1) (by positivity) h

lemma radC_pow_ne {j k : ℕ} (hjk : k ≠ j) : (radC j) ^ (k + 1) ≠ (2 : ℝ) ^ k := by
  intro heq
  have h1 : ((radC j) ^ (k + 1)) ^ (j + 1) = ((2 : ℝ) ^ k) ^ (j + 1) := congrArg (· ^ (j + 1)) heq
  rw [← pow_mul, mul_comm (k + 1) (j + 1), pow_mul, radC_pow, ← pow_mul, ← pow_mul] at h1
  have h2 : j * (k + 1) = k * (j + 1) := by simpa using h1
  have : j = k := by nlinarith
  exact hjk this.symm

lemma recover_c1_from_polyRawU {n : ℕ} {a a' : RawInv n}
    (ha : validRaw a) (ha' : validRaw a') (hpoly : polyRawU a = polyRawU a') :
    ∀ s : Bool, ∀ j : Fin (n + 1), a 1 s j = a' 1 s j := by
  intro s j
  let z : ℂ := if s then (radC j.val : ℂ)
    else (radC j.val : ℂ) * Complex.exp ((Real.pi : ℂ) * Complex.I / ((j.val + 1 : ℕ) : ℂ))
  have hnorm : ‖z‖ = radC j.val := by
    dsimp only [z]
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (radC_pos j.val).le]
      have hexp : (Real.pi : ℂ) * Complex.I / ((j.val + 1 : ℕ) : ℂ) =
          (((Real.pi / (j.val + 1 : ℝ)) : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [hexp, Complex.norm_exp_ofReal_mul_I, mul_one]
    · simp [Real.norm_of_nonneg (radC_pos j.val).le]
  have hzpow : z ^ (j.val + 1) = (if s then (1 : ℂ) else -1) * (2 : ℂ) ^ j.val := by
    dsimp only [z]
    cases s
    · simp only [Bool.false_eq_true, ↓reduceIte, mul_pow, ← Complex.exp_nat_mul]
      have harg : ((j.val + 1 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I / ((j.val + 1 : ℕ) : ℂ)) =
          (Real.pi : ℂ) * Complex.I := by
        have hne : ((j.val + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
        field_simp
      rw [harg, Complex.exp_pi_mul_I]
      have hr : ((radC j.val : ℂ)) ^ (j.val + 1) = (2 : ℂ) ^ j.val := by
        exact_mod_cast radC_pow j.val
      rw [hr]; ring
    · simp only [↓reduceIte, one_mul]
      exact_mod_cast radC_pow j.val
  have hrm_of : ∀ (b : RawInv n), validRaw b →
      ((polyRawU b).map (algebraMap ℚ ℂ)).rootMultiplicity z = b 1 s j := by
    intro b hb
    unfold polyRawU
    simp only [Polynomial.map_prod, Polynomial.map_pow]
    have hne : ∀ c : Fin 3, ∀ s' : Bool, ∀ k : Fin (n + 1),
        (b c s' k = 0 ∨ ¬ (c = 0 ∧ k = 0)) →
        ((factorPolyU c s' k.val).map (algebraMap ℚ ℂ)) ^ (b c s' k) ≠ 0 := by
      intro c s' k hok
      rcases hok with hz0 | hok
      · rw [hz0, pow_zero]; exact one_ne_zero
      · refine pow_ne_zero _ ?_
        have h0 := factorPolyU_ne_zero c s' k.val (fun ⟨hc, hk⟩ => hok ⟨hc, Fin.ext hk⟩)
        exact Polynomial.map_ne_zero h0
    -- Filter out (c=0, k=0) or just compute directly using rootMultiplicity_prod_pow
    -- Notice for (c=0, k=0), b 0 s' 0 = 0 so the power is 1!
    have h1 : ∀ (c : Fin 3) (s' : Bool) (k : Fin (n + 1)),
        (((factorPolyU c s' k.val).map (algebraMap ℚ ℂ)) ^ (b c s' k)).rootMultiplicity z =
        if c = 1 ∧ s' = s ∧ k = j then b 1 s j else 0 := by
      intro c s' k
      by_cases h00 : c = 0 ∧ k = 0
      · rcases h00 with ⟨rfl, rfl⟩
        have hbz : b 0 s' 0 = 0 := by cases s' <;> [exact hb.1; exact hb.2.1]
        simp [hbz]
      · have hfp_ne : (factorPolyU c s' k.val).map (algebraMap ℚ ℂ) ≠ 0 :=
          Polynomial.map_ne_zero (factorPolyU_ne_zero c s' k.val (fun ⟨h1, h2⟩ => h00 ⟨h1, Fin.ext h2⟩))
        rw [rootMultiplicity_pow_eq]
        by_cases hmatch : c = 1 ∧ s' = s ∧ k = j
        · rcases hmatch with ⟨hc, hs', hk'⟩
          rw [hc, hs', hk'] at hfp_ne ⊢
          simp only [true_and, ↓reduceIte]
          have heval : ((factorPolyU 1 s j.val).map (algebraMap ℚ ℂ)).eval z = 0 := by
            simp only [factorPolyU, Polynomial.map_add, Polynomial.map_one, Polynomial.map_mul,
              Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
              Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
              Polynomial.eval_pow, Polynomial.eval_X, hzpow]
            have h2ne : (2 : ℂ) ^ j.val ≠ 0 := pow_ne_zero _ (by norm_num)
            cases s <;> simp <;> field_simp <;> ring
          have hderiv : (((factorPolyU 1 s j.val).map (algebraMap ℚ ℂ)).derivative).eval z ≠ 0 := by
            simp only [factorPolyU, Polynomial.map_add, Polynomial.map_one, Polynomial.map_mul,
              Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
              Polynomial.derivative_add, Polynomial.derivative_one, Polynomial.derivative_mul,
              Polynomial.derivative_C, Polynomial.derivative_pow, Polynomial.derivative_X,
              zero_add, zero_mul, mul_one, Polynomial.eval_add, Polynomial.eval_mul,
              Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_natCast]
            rw [Nat.add_sub_cancel]
            have hz_ne : z ≠ 0 := by
              intro hz0; rw [hz0, norm_zero] at hnorm; linarith [radC_pos j.val]
            have h1 : (algebraMap ℚ ℂ) (if s then -1 else 1) ≠ 0 := by cases s <;> simp
            have h2 : (algebraMap ℚ ℂ) ((1 / 2 : ℚ) ^ j.val) ≠ 0 := by
              rw [map_pow]; exact pow_ne_zero _ (by norm_num)
            have h3 : ((j.val + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
            have h4 : z ^ j.val ≠ 0 := pow_ne_zero _ hz_ne
            exact mul_ne_zero h1 (mul_ne_zero h2 (mul_ne_zero h3 h4))
          rw [rootMultiplicity_one_of_deriv hfp_ne heval hderiv, mul_one]
        · simp only [hmatch, ↓reduceIte]
          have hne_ev : ((factorPolyU c s' k.val).map (algebraMap ℚ ℂ)).eval z ≠ 0 := by
            intro hev
            have hradlt : radC j.val / 2 < 1 := by linarith [radC_lt_two j.val]
            have hradnn : 0 ≤ radC j.val / 2 := by linarith [radC_pos j.val]
            fin_cases c <;>
              simp only [factorPolyU, Polynomial.map_add, Polynomial.map_one, Polynomial.map_mul,
                Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
                Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
                Polynomial.eval_pow, Polynomial.eval_X] at hev
            · have hk_pos : 0 < k.val := Nat.pos_of_ne_zero (fun hk0 => h00 ⟨rfl, Fin.ext hk0⟩)
              have hterm : ((1 / 2 : ℂ) ^ k.val) * z ^ k.val = (z / 2) ^ k.val := by
                rw [← mul_pow]; congr 1; ring
              have hnorm_lt : ‖(z / 2) ^ k.val‖ < 1 := by
                rw [norm_pow, norm_div, hnorm, Complex.norm_ofNat]
                exact pow_lt_one₀ hradnn hradlt (by omega)
              have hs_norm : ‖(algebraMap ℚ ℂ) (if s' then -1 else 1)‖ = 1 := by cases s' <;> simp
              have h1eq : (algebraMap ℚ ℂ) (if s' then -1 else 1) *
                  ((algebraMap ℚ ℂ) ((1 / 2) ^ k.val) * z ^ k.val) = -1 := by
                linear_combination hev
              have hnorm_eq := congrArg norm h1eq
              rw [norm_mul, hs_norm, one_mul, norm_neg, norm_one] at hnorm_eq
              have hmap : (algebraMap ℚ ℂ) ((1 / 2 : ℚ) ^ k.val) = (1 / 2 : ℂ) ^ k.val := by
                push_cast; rfl
              rw [hmap, hterm] at hnorm_eq
              linarith
            · by_cases hkj : k = j
              · subst hkj
                have hss' : s' ≠ s := fun hs' => hmatch ⟨rfl, hs', rfl⟩
                rw [hzpow] at hev
                have h2ne : (2 : ℂ) ^ k.val ≠ 0 := pow_ne_zero _ (by norm_num)
                cases s <;> cases s'
                · exact hss' rfl
                · simp at hev
                · simp at hev
                · exact hss' rfl
              · have hne_val : k.val ≠ j.val := fun h => hkj (Fin.ext h)
                have hs_norm : ‖(algebraMap ℚ ℂ) (if s' then -1 else 1)‖ = 1 := by cases s' <;> simp
                have h1eq : (algebraMap ℚ ℂ) (if s' then -1 else 1) *
                    ((algebraMap ℚ ℂ) ((1 / 2) ^ k.val) * z ^ (k.val + 1)) = -1 := by
                  linear_combination hev
                have hnorm_eq := congrArg norm h1eq
                rw [norm_mul, hs_norm, one_mul, norm_neg, norm_one, norm_mul, norm_pow, hnorm] at hnorm_eq
                have hmap : ‖(algebraMap ℚ ℂ) ((1 / 2 : ℚ) ^ k.val)‖ = ((2 : ℝ) ^ k.val)⁻¹ := by
                  simp [one_div_pow]
                rw [hmap] at hnorm_eq
                have hpow_eq : (radC j.val) ^ (k.val + 1) = (2 : ℝ) ^ k.val := by
                  have h2pos : (0 : ℝ) < (2 : ℝ) ^ k.val := by positivity
                  have := congrArg (fun x => (2 : ℝ) ^ k.val * x) hnorm_eq
                  field_simp at this
                  linarith
                exact radC_pow_ne hne_val hpow_eq
            · have hs_norm : ‖(algebraMap ℚ ℂ) (if s' then -1 else 1)‖ = 1 := by cases s' <;> simp
              have h1eq : (algebraMap ℚ ℂ) (if s' then -1 else 1) *
                  ((algebraMap ℚ ℂ) ((1 / 2) ^ (k.val + 1)) * z ^ k.val) = -1 := by
                linear_combination hev
              have hnorm_eq := congrArg norm h1eq
              rw [norm_mul, hs_norm, one_mul, norm_neg, norm_one, norm_mul, norm_pow, hnorm] at hnorm_eq
              have hmap : ‖(algebraMap ℚ ℂ) ((1 / 2 : ℚ) ^ (k.val + 1))‖ = (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ k.val) := by
                simp [pow_succ, mul_comm]
              rw [hmap, mul_assoc, ← mul_pow] at hnorm_eq
              have hle1 : (1 / 2 * radC j.val) ^ k.val ≤ 1 := by
                exact pow_le_one₀ (by linarith [radC_pos j.val]) (by linarith [radC_lt_two j.val])
              linarith
          have hrm0 : ((factorPolyU c s' k.val).map (algebraMap ℚ ℂ)).rootMultiplicity z = 0 :=
            Polynomial.rootMultiplicity_eq_zero_iff.mpr (fun hr => absurd hr hne_ev)
          rw [hrm0, mul_zero]
    -- Combine triple product using rootMultiplicity_prod_pow on Fin 3 × Bool × Fin (n + 1)
    have hprod_eq : (∏ c : Fin 3, ∏ s' : Bool, ∏ k : Fin (n + 1),
        ((factorPolyU c s' k.val).map (algebraMap ℚ ℂ)) ^ (b c s' k)) =
        ∏ x : Fin 3 × Bool × Fin (n + 1),
          ((factorPolyU x.1 x.2.1 x.2.2.val).map (algebraMap ℚ ℂ)) ^ (b x.1 x.2.1 x.2.2) := by
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl (fun c _ => ?_)
      rw [Fintype.prod_prod_type]
    rw [hprod_eq]
    have hrm_prod : ∀ S : Finset (Fin 3 × Bool × Fin (n + 1)),
        (∏ x ∈ S, ((factorPolyU x.1 x.2.1 x.2.2.val).map (algebraMap ℚ ℂ)) ^ (b x.1 x.2.1 x.2.2)).rootMultiplicity z =
        ∑ x ∈ S, (((factorPolyU x.1 x.2.1 x.2.2.val).map (algebraMap ℚ ℂ)) ^ (b x.1 x.2.1 x.2.2)).rootMultiplicity z := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | @insert x S hx ih =>
        rw [Finset.prod_insert hx, Finset.sum_insert hx]
        have hfx : ((factorPolyU x.1 x.2.1 x.2.2.val).map (algebraMap ℚ ℂ)) ^ (b x.1 x.2.1 x.2.2) ≠ 0 := by
          apply hne
          by_cases h00 : x.1 = 0 ∧ x.2.2 = 0
          · left; rcases h00 with ⟨h1, h2⟩; rw [h1, h2]; cases x.2.1 <;> [exact hb.1; exact hb.2.1]
          · right; exact h00
        have hfS : (∏ y ∈ S, ((factorPolyU y.1 y.2.1 y.2.2.val).map (algebraMap ℚ ℂ)) ^ (b y.1 y.2.1 y.2.2)) ≠ 0 := by
          refine Finset.prod_ne_zero_iff.mpr (fun y _ => hne y.1 y.2.1 y.2.2 ?_)
          by_cases h00 : y.1 = 0 ∧ y.2.2 = 0
          · left; rcases h00 with ⟨h1, h2⟩; rw [h1, h2]; cases y.2.1 <;> [exact hb.1; exact hb.2.1]
          · right; exact h00
        rw [Polynomial.rootMultiplicity_mul (mul_ne_zero hfx hfS), ih]
    rw [hrm_prod]
    simp_rw [h1]
    rw [Finset.sum_eq_single (1, s, j)]
    · simp
    · intro x _ hx
      have : ¬ (x.1 = 1 ∧ x.2.1 = s ∧ x.2.2 = j) := fun ⟨h1, h2, h3⟩ => hx (by rcases x with ⟨c, s', k⟩; simp_all)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h1 := hrm_of a ha
  have h2 := hrm_of a' ha'
  rw [hpoly] at h1
  exact h1.symm.trans h2

def swapRaw {n : ℕ} (a : RawInv n) : RawInv n :=
  fun c s j => a (match c with | 0 => 0 | 1 => 2 | 2 => 1) s j

lemma validRaw_swap {n : ℕ} {a : RawInv n} (ha : validRaw a) : validRaw (swapRaw a) := by
  refine ⟨ha.1, ha.2.1, ?_, ?_, ?_⟩
  · have hlen := ha.2.2.1
    unfold totalLen at hlen ⊢
    unfold swapRaw
    rw [Fin.sum_univ_three] at hlen ⊢
    have h12 : ∀ j : Fin (n + 1), weightOf (1 : Fin 3) j = weightOf (2 : Fin 3) j := fun j => by
      simp [weightOf]
    simp only [h12] at hlen ⊢
    linarith
  · simp only [swapRaw]
    exact ha.2.2.2.1.symm
  · have hpar := ha.2.2.2.2
    rw [Fin.sum_univ_three] at hpar ⊢
    simp only [swapRaw]
    omega

lemma polyRawU_swap {n : ℕ} (a : RawInv n) : polyRawU (swapRaw a) = polyRawV a := by
  unfold polyRawU polyRawV swapRaw
  rw [Fin.prod_univ_three, Fin.prod_univ_three]
  have h0 : ∀ s j, factorPolyU 0 s j = factorPolyV 0 s j := fun _ _ => rfl
  have h1 : ∀ s j, factorPolyU 1 s j = factorPolyV 2 s j := fun _ _ => rfl
  have h2 : ∀ s j, factorPolyU 2 s j = factorPolyV 1 s j := fun _ _ => rfl
  simp only [h0, h1, h2]
  ring

lemma coeff_mul_of_low_zero {k : ℕ} {P Q : Polynomial ℚ}
    (hP0 : P.coeff 0 = 1) (hQ0 : Q.coeff 0 = 1)
    (hP : ∀ m, 0 < m → m < k → P.coeff m = 0)
    (hQ : ∀ m, 0 < m → m < k → Q.coeff m = 0) :
    (P * Q).coeff 0 = 1 ∧
    (∀ m, 0 < m → m < k → (P * Q).coeff m = 0) ∧
    (0 < k → (P * Q).coeff k = P.coeff k + Q.coeff k) := by
  refine ⟨by rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => P.coeff i * Q.coeff j)]; simp [hP0, hQ0], ?_, ?_⟩
  · intro m hm0 hmk
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => P.coeff i * Q.coeff j)]
    refine Finset.sum_eq_zero (fun x hx => ?_)
    have hxle : x ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hx)
    by_cases hx0 : x = 0
    · rw [hx0, Nat.sub_zero, hQ m hm0 hmk, mul_zero]
    · by_cases hxm : x = m
      · rw [hxm, hP m hm0 hmk, zero_mul]
      · rw [hP x (by omega) (by omega), zero_mul]
  · intro hk
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => P.coeff i * Q.coeff j)]
    rw [Finset.sum_range_succ]
    have hk1 : k = (k - 1) + 1 := by omega
    have hsplit : ∑ x ∈ Finset.range k, P.coeff x * Q.coeff (k - x) =
        P.coeff 0 * Q.coeff k + ∑ x ∈ Finset.range (k - 1), P.coeff (x + 1) * Q.coeff (k - (x + 1)) := by
      conv_lhs => rw [hk1, Finset.sum_range_succ']
      simp only [← hk1, Nat.sub_zero, add_comm]
    rw [hsplit]
    have hmid : ∑ x ∈ Finset.range (k - 1), P.coeff (x + 1) * Q.coeff (k - (x + 1)) = 0 := by
      refine Finset.sum_eq_zero (fun x hx => ?_)
      have hxlt := Finset.mem_range.mp hx
      rw [hP (x + 1) (by omega) (by omega), zero_mul]
    rw [hmid, add_zero, Nat.sub_self, hP0, hQ0, one_mul, mul_one, add_comm]

lemma coeff_pow_of_low_zero {k : ℕ} {P : Polynomial ℚ}
    (hP0 : P.coeff 0 = 1) (hP : ∀ m, 0 < m → m < k → P.coeff m = 0) (e : ℕ) :
    (P ^ e).coeff 0 = 1 ∧
    (∀ m, 0 < m → m < k → (P ^ e).coeff m = 0) ∧
    (0 < k → (P ^ e).coeff k = (e : ℚ) * P.coeff k) := by
  induction e with
  | zero =>
    refine ⟨by simp, fun m hm _ => by simp [Polynomial.coeff_one, Nat.ne_of_gt hm],
      fun hk => by simp [Polynomial.coeff_one, Nat.ne_of_gt hk]⟩
  | succ e ih =>
    rw [pow_succ]
    obtain ⟨h0, hlow, htop⟩ := coeff_mul_of_low_zero ih.1 hP0 ih.2.1 hP
    refine ⟨h0, hlow, fun hk => ?_⟩
    rw [htop hk, ih.2.2 hk, Nat.cast_add, Nat.cast_one]
    ring

lemma coeff_prod_of_low_zero {ι : Type*} (s : Finset ι) (k : ℕ) (f : ι → Polynomial ℚ)
    (hf : ∀ i ∈ s, (f i).coeff 0 = 1 ∧ ∀ m, 0 < m → m < k → (f i).coeff m = 0) :
    (∏ i ∈ s, f i).coeff 0 = 1 ∧
    (∀ m, 0 < m → m < k → (∏ i ∈ s, f i).coeff m = 0) ∧
    (0 < k → (∏ i ∈ s, f i).coeff k = ∑ i ∈ s, (f i).coeff k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simp, fun m hm _ => by simp [Polynomial.coeff_one, Nat.ne_of_gt hm],
      fun hk => by simp [Polynomial.coeff_one, Nat.ne_of_gt hk]⟩
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hfa := hf a (Finset.mem_insert_self a s)
    have hih := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    obtain ⟨h0, hlow, htop⟩ := coeff_mul_of_low_zero hfa.1 hih.1 hfa.2 hih.2.1
    refine ⟨h0, hlow, fun hk => ?_⟩
    rw [htop hk, hih.2.2 hk, Finset.sum_insert ha]

lemma factorPolyU0_coeff (s : Bool) {j : ℕ} (hj : 0 < j) (m : ℕ) :
    (factorPolyU 0 s j).coeff m =
      (if m = 0 then 1 else 0) +
      (if m = j then (if s then (-1 : ℚ) else 1) * (1 / 2 : ℚ) ^ j else 0) := by
  unfold factorPolyU
  simp only [Polynomial.coeff_add, Polynomial.coeff_one, ← mul_assoc, ← Polynomial.C_mul,
    Polynomial.coeff_C_mul_X_pow]

lemma reducedRaw_unique {n : ℕ} {a a' : RawInv n}
    (ha : reducedRaw a) (ha' : reducedRaw a')
    (heq : ∀ u v : ℚ, 0 < u → u < 1 → 0 < v → v < 1 → polyOfRaw a u v = polyOfRaw a' u v) :
    a = a' := by
  have hU : polyRawU a = polyRawU a' := by
    apply poly_eq_of_eq_on_unit
    intro u hu0 hu1
    rw [eval_polyRawU, eval_polyRawU]
    exact heq u (1 / 2) hu0 hu1 (by norm_num) (by norm_num)
  have hV : polyRawV a = polyRawV a' := by
    apply poly_eq_of_eq_on_unit
    intro v hv0 hv1
    rw [eval_polyRawV, eval_polyRawV]
    exact heq (1 / 2) v (by norm_num) (by norm_num) hv0 hv1
  have hc1 : ∀ s j, a 1 s j = a' 1 s j := recover_c1_from_polyRawU ha.1 ha'.1 hU
  have hc2 : ∀ s j, a 2 s j = a' 2 s j := by
    have hUs : polyRawU (swapRaw a) = polyRawU (swapRaw a') := by
      rw [polyRawU_swap, polyRawU_swap, hV]
    have h1 := recover_c1_from_polyRawU (validRaw_swap ha.1) (validRaw_swap ha'.1) hUs
    intro s j
    exact h1 s j
  -- Cancel c = 1 and c = 2 factors from hU
  have h0prod : (∏ s : Bool, ∏ j : Fin (n + 1), (factorPolyU 0 s j.val) ^ (a 0 s j)) =
      ∏ s : Bool, ∏ j : Fin (n + 1), (factorPolyU 0 s j.val) ^ (a' 0 s j) := by
    unfold polyRawU at hU
    rw [Fin.prod_univ_three, Fin.prod_univ_three] at hU
    simp only [hc1, hc2] at hU
    have hne1 : (∏ s : Bool, ∏ j : Fin (n + 1), (factorPolyU 1 s j.val) ^ (a' 1 s j)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun s _ => Finset.prod_ne_zero_iff.mpr (fun j _ =>
        pow_ne_zero _ (factorPolyU_ne_zero 1 s j.val (by simp))))
    have hne2 : (∏ s : Bool, ∏ j : Fin (n + 1), (factorPolyU 2 s j.val) ^ (a' 2 s j)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun s _ => Finset.prod_ne_zero_iff.mpr (fun j _ =>
        pow_ne_zero _ (factorPolyU_ne_zero 2 s j.val (by simp))))
    exact mul_right_cancel₀ hne1 (mul_right_cancel₀ hne2 hU)
  -- Strong induction on k to recover a 0 s ⟨k, _⟩
  have hc0 : ∀ k (hk : k ≤ n), ∀ s : Bool, a 0 s ⟨k, by omega⟩ = a' 0 s ⟨k, by omega⟩ := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk
      by_cases hk0 : k = 0
      · subst hk0
        intro s
        cases s
        · change a 0 false 0 = a' 0 false 0; rw [ha.1.1, ha'.1.1]
        · change a 0 true 0 = a' 0 true 0; rw [ha.1.2.1, ha'.1.2.1]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        -- Split product over j < k and j ≥ k
        let Slt : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => j.val < k)
        let Sge : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => k ≤ j.val)
        have hsplit : ∀ b : RawInv n,
            (∏ s : Bool, ∏ j : Fin (n + 1), (factorPolyU 0 s j.val) ^ (b 0 s j)) =
            (∏ s : Bool, ∏ j ∈ Slt, (factorPolyU 0 s j.val) ^ (b 0 s j)) *
            (∏ s : Bool, ∏ j ∈ Sge, (factorPolyU 0 s j.val) ^ (b 0 s j)) := by
          intro b
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl (fun s _ => ?_)
          have hun : Slt ∪ Sge = Finset.univ := by
            ext j; simp only [Slt, Sge, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; omega
          have hdisj : Disjoint Slt Sge := Finset.disjoint_filter.mpr (fun j _ h1 h2 => by omega)
          rw [← Finset.prod_union hdisj, hun]
        rw [hsplit a, hsplit a'] at h0prod
        have hlt_eq : (∏ s : Bool, ∏ j ∈ Slt, (factorPolyU 0 s j.val) ^ (a 0 s j)) =
            ∏ s : Bool, ∏ j ∈ Slt, (factorPolyU 0 s j.val) ^ (a' 0 s j) := by
          refine Finset.prod_congr rfl (fun s _ => Finset.prod_congr rfl (fun j hj => ?_))
          have hjlt : j.val < k := (Finset.mem_filter.mp hj).2
          have := ih j.val hjlt (by omega) s
          exact congrArg (fun e => (factorPolyU 0 s j.val) ^ e) this
        have hlt_ne : (∏ s : Bool, ∏ j ∈ Slt, (factorPolyU 0 s j.val) ^ (a 0 s j)) ≠ 0 := by
          refine Finset.prod_ne_zero_iff.mpr (fun s _ => Finset.prod_ne_zero_iff.mpr (fun j _ => ?_))
          by_cases hj0 : j.val = 0
          · have hj : j = 0 := Fin.ext hj0
            rw [hj]; cases s <;> simp [ha.1.1, ha.1.2.1]
          · exact pow_ne_zero _ (factorPolyU_ne_zero 0 s j.val (fun ⟨_, h⟩ => hj0 h))
        rw [hlt_eq] at h0prod
        have hge_eq : (∏ s : Bool, ∏ j ∈ Sge, (factorPolyU 0 s j.val) ^ (a 0 s j)) =
            ∏ s : Bool, ∏ j ∈ Sge, (factorPolyU 0 s j.val) ^ (a' 0 s j) :=
          mul_left_cancel₀ (hlt_eq ▸ hlt_ne) h0prod
        have hcoeff_ge : ∀ b : RawInv n,
            (∏ s : Bool, ∏ j ∈ Sge, (factorPolyU 0 s j.val) ^ (b 0 s j)).coeff k =
            ((b 0 false ⟨k, by omega⟩ : ℚ) - (b 0 true ⟨k, by omega⟩ : ℚ)) * (1 / 2 : ℚ) ^ k := by
          intro b
          have hpair : (∏ s : Bool, ∏ j ∈ Sge, (factorPolyU 0 s j.val) ^ (b 0 s j)) =
              ∏ x ∈ (Finset.univ : Finset Bool) ×ˢ Sge, (factorPolyU 0 x.1 x.2.val) ^ (b 0 x.1 x.2) := by
            rw [Finset.prod_product]
          rw [hpair]
          have hlow : ∀ x ∈ (Finset.univ : Finset Bool) ×ˢ Sge,
              ((factorPolyU 0 x.1 x.2.val) ^ (b 0 x.1 x.2)).coeff 0 = 1 ∧
              ∀ m, 0 < m → m < k → ((factorPolyU 0 x.1 x.2.val) ^ (b 0 x.1 x.2)).coeff m = 0 := by
            intro x hx
            have hxk : k ≤ x.2.val := (Finset.mem_filter.mp (Finset.mem_product.mp hx).2).2
            have h := coeff_pow_of_low_zero (k := k) (P := factorPolyU 0 x.1 x.2.val)
              (by rw [factorPolyU0_coeff _ (by omega)]; simp [show (0 : ℕ) ≠ x.2.val by omega])
              (fun m hm0 hmk => by rw [factorPolyU0_coeff _ (by omega)]; simp [Nat.ne_of_gt hm0, show m ≠ x.2.val by omega])
              (b 0 x.1 x.2)
            exact ⟨h.1, h.2.1⟩
          rw [(coeff_prod_of_low_zero _ k _ hlow).2.2 hkpos, Finset.sum_product]
          have hterm : ∀ s : Bool, ∀ j ∈ Sge,
              ((factorPolyU 0 s j.val) ^ (b 0 s j)).coeff k =
              if j = ⟨k, by omega⟩ then (b 0 s j : ℚ) * ((if s then (-1 : ℚ) else 1) * (1 / 2 : ℚ) ^ k) else 0 := by
            intro s j hj
            have hjk : k ≤ j.val := (Finset.mem_filter.mp hj).2
            have h := coeff_pow_of_low_zero (k := k) (P := factorPolyU 0 s j.val)
              (by rw [factorPolyU0_coeff _ (by omega)]; simp [show (0 : ℕ) ≠ j.val by omega])
              (fun m hm0 hmk => by rw [factorPolyU0_coeff _ (by omega)]; simp [Nat.ne_of_gt hm0, show m ≠ j.val by omega])
              (b 0 s j)
            rw [h.2.2 hkpos, factorPolyU0_coeff _ (by omega)]
            by_cases hjeq : j = ⟨k, by omega⟩
            · rw [hjeq]; simp [Nat.ne_of_gt hkpos]
            · have hne : k ≠ j.val := fun hv => hjeq (Fin.ext hv.symm)
              simp [hjeq, hne, Nat.ne_of_gt hkpos]
          have hsum_s : ∀ s : Bool, ∑ j ∈ Sge, ((factorPolyU 0 s j.val) ^ (b 0 s j)).coeff k =
              (b 0 s ⟨k, by omega⟩ : ℚ) * ((if s then (-1 : ℚ) else 1) * (1 / 2 : ℚ) ^ k) := by
            intro s
            rw [Finset.sum_congr rfl (hterm s)]
            rw [Finset.sum_ite_eq' Sge ⟨k, by omega⟩]
            have hmem : (⟨k, by omega⟩ : Fin (n + 1)) ∈ Sge :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
            simp [hmem]
          simp_rw [hsum_s]
          rw [Fintype.sum_bool]
          simp only [↓reduceIte, Bool.false_eq_true]
          ring
        have hck := congrArg (fun P : Polynomial ℚ => P.coeff k) hge_eq
        rw [hcoeff_ge a, hcoeff_ge a'] at hck
        have h2k : ((1 / 2 : ℚ) ^ k) ≠ 0 := by positivity
        have hdiff : (a 0 false ⟨k, by omega⟩ : ℚ) - (a 0 true ⟨k, by omega⟩ : ℚ) =
            (a' 0 false ⟨k, by omega⟩ : ℚ) - (a' 0 true ⟨k, by omega⟩ : ℚ) :=
          mul_right_cancel₀ h2k hck
        have hdiffZ : (a 0 false ⟨k, by omega⟩ : ℤ) - (a 0 true ⟨k, by omega⟩ : ℤ) =
            (a' 0 false ⟨k, by omega⟩ : ℤ) - (a' 0 true ⟨k, by omega⟩ : ℤ) := by
          exact_mod_cast hdiff
        have hr1 := ha.2 ⟨k, by omega⟩
        have hr2 := ha'.2 ⟨k, by omega⟩
        intro s
        rcases hr1 with h1 | h1 <;> rcases hr2 with h2 | h2 <;> cases s <;> omega
  funext c s j
  fin_cases c
  · exact hc0 j.val (Nat.le_of_lt_succ j.isLt) s
  · exact hc1 s j
  · exact hc2 s j

-- Section 6: Final counting assembly

def toRaw {n : ℕ} (a : Fin 3 → Bool → Fin (n + 1) → Fin (2 * n + 1)) : RawInv n :=
  fun c s j => (a c s j).val

def ofValidRaw {n : ℕ} (a : RawInv n) (ha : validRaw a) :
    Fin 3 → Bool → Fin (n + 1) → Fin (2 * n + 1) :=
  fun c s j => ⟨a c s j, Nat.lt_succ_of_le (validRaw_entry_le ha c s j)⟩

lemma toRaw_ofValidRaw {n : ℕ} (a : RawInv n) (ha : validRaw a) :
    toRaw (ofValidRaw a ha) = a := by
  funext c s j; rfl

lemma toRaw_injective {n : ℕ} : Function.Injective (@toRaw n) := by
  intro a b h
  funext c s j
  exact Fin.ext (congrFun (congrFun (congrFun h c) s) j)

def a0Inv (t : ℕ) : Fin 3 → Bool → Fin ((t + 1) + 1) → Fin (2 * (t + 1) + 1) :=
  fun c s j => if c = 0 ∧ s = false ∧ j = Fin.last (t + 1) then ⟨1, by omega⟩ else ⟨0, by omega⟩

lemma a0Inv_reduced (t : ℕ) : reducedRaw (toRaw (a0Inv t)) := by
  have hlast_ne0 : Fin.last (t + 1) ≠ 0 := fun h => by
    have := congrArg Fin.val h; simp at this
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [toRaw, a0Inv, hlast_ne0.symm]
  · simp [toRaw, a0Inv]
  · unfold totalLen toRaw a0Inv
    rw [Fin.sum_univ_three, Fintype.sum_bool]
    have h0t : ∑ j : Fin (t + 2),
        (if (0 : Fin 3) = 0 ∧ true = false ∧ j = Fin.last (t + 1) then (⟨1, by omega⟩ : Fin (2 * (t + 1) + 1)) else ⟨0, by omega⟩).val *
        weightOf 0 j = 0 := by simp
    have h1 : ∑ s : Bool, ∑ j : Fin (t + 2),
        (if (1 : Fin 3) = 0 ∧ s = false ∧ j = Fin.last (t + 1) then (⟨1, by omega⟩ : Fin (2 * (t + 1) + 1)) else ⟨0, by omega⟩).val *
        weightOf 1 j = 0 := by simp
    have h2 : ∑ s : Bool, ∑ j : Fin (t + 2),
        (if (2 : Fin 3) = 0 ∧ s = false ∧ j = Fin.last (t + 1) then (⟨1, by omega⟩ : Fin (2 * (t + 1) + 1)) else ⟨0, by omega⟩).val *
        weightOf 2 j = 0 := by simp
    rw [h0t, h1, h2, zero_add, add_zero, add_zero]
    rw [Finset.sum_eq_single (Fin.last (t + 1))]
    · simp [weightOf]
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp [toRaw, a0Inv]
  · simp [toRaw, a0Inv]
  · intro j; right; simp [toRaw, a0Inv]

lemma a0Inv_poly (t : ℕ) (u v : ℚ) :
    polyOfRaw (toRaw (a0Inv t)) u v = 1 + (u * v) ^ (t + 1) := by
  unfold polyOfRaw toRaw a0Inv
  rw [Fin.prod_univ_three, Fintype.prod_bool]
  have h1 : ∏ s : Bool, ∏ j : Fin (t + 2),
      factorOf 1 s j.val u v ^ (if (1 : Fin 3) = 0 ∧ s = false ∧ j = Fin.last (t + 1) then (⟨1, by omega⟩ : Fin (2 * (t + 1) + 1)) else ⟨0, by omega⟩).val = 1 := by simp
  have h2 : ∏ s : Bool, ∏ j : Fin (t + 2),
      factorOf 2 s j.val u v ^ (if (2 : Fin 3) = 0 ∧ s = false ∧ j = Fin.last (t + 1) then (⟨1, by omega⟩ : Fin (2 * (t + 1) + 1)) else ⟨0, by omega⟩).val = 1 := by simp
  have h0t : ∏ j : Fin (t + 2),
      factorOf 0 true j.val u v ^ (if (0 : Fin 3) = 0 ∧ true = false ∧ j = Fin.last (t + 1) then (⟨1, by omega⟩ : Fin (2 * (t + 1) + 1)) else ⟨0, by omega⟩).val = 1 := by simp
  rw [h1, h2, h0t, one_mul, mul_one, mul_one]
  rw [Finset.prod_eq_single (Fin.last (t + 1))]
  · simp [factorOf, Nat.mod_eq_of_lt (by omega : 1 < 2 * (t + 1) + 1)]
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ _) h

set_option maxHeartbeats 800000 in
lemma main_result (t : ℕ) :
  let n := t+1
  let I := Fin n
  let J := Fin (n+1)
  let V := Bool × I
  let P := V → Option Bool
  let hist := fun (p : P) (d : J × J) =>
    ((Finset.univ : Finset (V → Bool)).filter (fun x =>
      (∀ u, p u = none ∨ p u = some (x u)) ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,i))).card = d.1.val ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,i+1))).card = d.2.val)).card
  let prob := fun (p : P) (d : J × J) =>
    (hist p d : ℚ) / (2 : ℚ)^((Finset.univ.filter (fun u : V => p u = none)).card)
  let Inv := Fin 3 → Bool → J → Fin (2*n+1)
  let legal := (Finset.univ : Finset Inv).filter (fun a =>
    (a 0 false 0).val = 0 ∧ (a 0 true 0).val = 0 ∧
    (∀ j, (a 0 false j).val = 0 ∨ (a 0 true j).val = 0) ∧
    (∑ c : Fin 3, ∑ s : Bool, ∑ j : J,
      (a c s j).val * (2*j.val + (if c = 0 then 0 else 1))) = 2*n ∧
    (∑ s : Bool, ∑ j : J, (a 1 s j).val) = (∑ s : Bool, ∑ j : J, (a 2 s j).val) ∧
    (∑ c : Fin 3, ∑ j : J, (a c true j).val) % 2 = 0)
  ((Finset.univ : Finset P).image prob).card = legal.card ∧
    ((Finset.univ : Finset P).image hist).card =
      1 + ∑ a ∈ legal, (1 + ∑ j : J, (a 0 true j).val * j.val.factorization 2) := by
  classical
  intro n I J V P hist prob Inv legal
  -- Relate hist, prob, transform, polyDef, polyQ
  have hhist_eq : ∀ p : P, hist p = histG n (ringPerm t) p := by
    intro p; funext d
    unfold histG fits diff
    dsimp only [hist]
    apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine and_congr Iff.rfl (and_congr ?_ ?_)
    · refine iff_of_eq (congrArg (· = d.1.val) (congrArg Finset.card (Finset.ext fun i => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, id_eq])))
    · refine iff_of_eq (congrArg (· = d.2.val) (congrArg Finset.card (Finset.ext fun i => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simp only [ringPerm, Equiv.coe_fn_mk])))
  have hprob_eq : ∀ p : P, prob p = lawG n (ringPerm t) p := by
    intro p; funext d
    unfold lawG freeCount
    simp only [prob, hhist_eq]
    congr 2
  have htrans_eq : ∀ (p : P) (u v : ℚ),
      transform n (prob p) u v = polyQ t (pinEquiv t p) u v := by
    intro p u v
    rw [← polyDef_eq_polyQ]
    unfold transform polyDef lawDef
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun b _ => ?_))
    have hl : prob p (r, b) = (((Finset.univ : Finset (Bool × Fin n → Bool)).filter (fun x =>
        (∀ w, p w = none ∨ p w = some (x w)) ∧
        (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card = r.val ∧
        (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, ringPerm t i))).card = b.val)).card : ℚ) /
        (2 : ℚ) ^ ((Finset.univ.filter (fun w : Bool × Fin n => p w = none)).card) := by
      simp only [prob, hist, ringPerm, Equiv.coe_fn_mk]
      congr 2
    rw [hl]; ring
  have hprob_iff : ∀ p1 p2 : P,
      prob p1 = prob p2 ↔
      ∀ u v : ℚ, 0 < u → u < 1 → 0 < v → v < 1 →
        polyQ t (pinEquiv t p1) u v = polyQ t (pinEquiv t p2) u v := by
    intro p1 p2
    constructor
    · intro h u v _ _ _ _
      rw [← htrans_eq p1, ← htrans_eq p2, h]
    · intro h
      apply transform_injective
      intro u v hu0 hu1 hv0 hv1
      rw [htrans_eq, htrans_eq]
      exact h u v hu0 hu1 hv0 hv1
  have hmem_legal : ∀ a : Inv, a ∈ legal ↔ reducedRaw (toRaw a) := by
    intro a
    simp only [legal, Finset.mem_filter, Finset.mem_univ, true_and, reducedRaw, validRaw, totalLen,
      toRaw, weightOf]
    tauto
  -- Witness pinning for each validRaw
  have hwit_raw : ∀ b : RawInv n, validRaw b →
      ∃ p : P, pinCount t (pinEquiv t p) = totalCount b ∧
        ∀ u v, polyQ t (pinEquiv t p) u v = polyOfRaw b u v := by
    intro b hb
    obtain ⟨q, hcnt, hpoly⟩ := exists_q_of_validRaw hb
    refine ⟨(pinEquiv t).symm q, ?_, ?_⟩
    · simpa using hcnt
    · intro u v; simpa using hpoly u v
  -- Canonical representative prob for each a ∈ legal
  have hex_rep : ∀ a : Inv, ∃ f : J × J → ℚ,
      (a ∈ legal → ∃ p : P, prob p = f ∧ ∀ u v, polyQ t (pinEquiv t p) u v = polyOfRaw (toRaw a) u v) := by
    intro a
    by_cases ha : a ∈ legal
    · obtain ⟨p, _, hp⟩ := hwit_raw (toRaw a) ((hmem_legal a).mp ha).1
      exact ⟨prob p, fun _ => ⟨p, rfl, hp⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h ha⟩
  choose rep hrep using hex_rep
  have hrep_inj : Set.InjOn rep (legal : Set Inv) := by
    intro a ha b hb hab
    obtain ⟨pa, hpa, hpa_poly⟩ := hrep a ha
    obtain ⟨pb, hpb, hpb_poly⟩ := hrep b hb
    have hpeq : prob pa = prob pb := hpa.trans (hab.trans hpb.symm)
    have hpoly : ∀ u v : ℚ, 0 < u → u < 1 → 0 < v → v < 1 →
        polyOfRaw (toRaw a) u v = polyOfRaw (toRaw b) u v := by
      intro u v hu0 hu1 hv0 hv1
      rw [← hpa_poly, ← hpb_poly]
      exact (hprob_iff pa pb).mp hpeq u v hu0 hu1 hv0 hv1
    exact toRaw_injective (reducedRaw_unique ((hmem_legal a).mp ha) ((hmem_legal b).mp hb) hpoly)
  have hrep_surj : (Finset.univ : Finset P).image prob = legal.image rep := by
    ext f
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨p, rfl⟩
      by_cases hne : ∃ k, pinEquiv t p k ≠ none
      · set b := rawOfQ (pinEquiv t p) hne
        have hb : validRaw b := rawOfQ_valid (pinEquiv t p) hne
        obtain ⟨hred, hred_poly, _, _⟩ := reduceRaw_props hb
        let a : Inv := ofValidRaw (reduceRaw b) hred.1
        have ha : a ∈ legal := (hmem_legal a).mpr (by rw [toRaw_ofValidRaw]; exact hred)
        refine ⟨a, ha, ?_⟩
        obtain ⟨pa, hpa, hpa_poly⟩ := hrep a ha
        rw [← hpa]
        apply (hprob_iff pa p).mpr
        intro u v _ _ _ _
        rw [hpa_poly, toRaw_ofValidRaw, hred_poly, ← rawOfQ_poly (pinEquiv t p) hne]
      · push Not at hne
        have hqnone : pinEquiv t p = fun _ => none := funext hne
        have ha0 : a0Inv t ∈ legal := (hmem_legal _).mpr (a0Inv_reduced t)
        refine ⟨a0Inv t, ha0, ?_⟩
        obtain ⟨pa, hpa, hpa_poly⟩ := hrep (a0Inv t) ha0
        rw [← hpa]
        apply (hprob_iff pa p).mpr
        intro u v _ _ _ _
        rw [hpa_poly, a0Inv_poly, hqnone, polyQ_none]
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨pa, hpa, _⟩ := hrep a ha
      exact ⟨pa, hpa⟩
  have hpart1 : ((Finset.univ : Finset P).image prob).card = legal.card := by
    rw [hrep_surj, Finset.card_image_of_injOn hrep_inj]
  -- Part 2: hist count
  have hhist_iff : ∀ p1 p2 : P,
      hist p1 = hist p2 ↔ prob p1 = prob p2 ∧ pinCount t (pinEquiv t p1) = pinCount t (pinEquiv t p2) := by
    intro p1 p2
    constructor
    · intro h
      have hG : histG n (ringPerm t) p1 = histG n (ringPerm t) p2 := by
        rw [← hhist_eq, ← hhist_eq, h]
      have hcardI : Fintype.card I = n := Fintype.card_fin n
      have hlaw : prob p1 = prob p2 := by
        rw [hprob_eq, hprob_eq]
        exact histG_eq_implies_lawG_eq hcardI hcardI _ _ _ _ hG
      have hsum1 := sum_histG hcardI (ringPerm t) p1
      have hsum2 := sum_histG hcardI (ringPerm t) p2
      rw [hG] at hsum1
      have hfree : freeCount p1 = freeCount p2 :=
        Nat.pow_right_injective (by decide : 2 ≤ 2) (hsum1.symm.trans hsum2)
      have h1 := freeCount_add_pinCount t p1
      have h2 := freeCount_add_pinCount t p2
      exact ⟨hlaw, by omega⟩
    · rintro ⟨hpr, hpc⟩
      have h1 := freeCount_add_pinCount t p1
      have h2 := freeCount_add_pinCount t p2
      have hfree : freeCount p1 = freeCount p2 := by omega
      funext d
      have hd := congrFun hpr d
      have hpow : (2 : ℚ) ^ freeCount p1 ≠ 0 := by positivity
      change (hist p1 d : ℚ) / (2 : ℚ) ^ freeCount p1 = (hist p2 d : ℚ) / (2 : ℚ) ^ freeCount p2 at hd
      rw [← hfree] at hd
      have hqeq : (hist p1 d : ℚ) = (hist p2 d : ℚ) := by
        have := congrArg (· * (2 : ℚ) ^ freeCount p1) hd
        rwa [div_mul_cancel₀ _ hpow, div_mul_cancel₀ _ hpow] at this
      exact_mod_cast hqeq
  let pairFn : P → (J × J → ℚ) × ℕ := fun p => (prob p, pinCount t (pinEquiv t p))
  have hhist_pair : ((Finset.univ : Finset P).image hist).card =
      ((Finset.univ : Finset P).image pairFn).card := by
    refine Finset.card_bij
      (fun H hH => pairFn (Finset.mem_image.mp hH).choose) ?_ ?_ ?_
    · intro H hH
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    · intro H1 hH1 H2 hH2 heq
      have h1 := (Finset.mem_image.mp hH1).choose_spec.2
      have h2 := (Finset.mem_image.mp hH2).choose_spec.2
      rw [← h1, ← h2]
      exact (hhist_iff _ _).mpr (Prod.ext_iff.mp heq)
    · intro y hy
      rcases Finset.mem_image.mp hy with ⟨p, _, rfl⟩
      refine ⟨hist p, Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩, ?_⟩
      have hch := (Finset.mem_image.mp (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩ :
        hist p ∈ Finset.univ.image hist)).choose_spec.2
      exact Prod.ext_iff.mpr ((hhist_iff _ _).mp hch)
  -- Group pairFn image by first coordinate = rep a for a ∈ legal
  let S : Inv → Finset ℕ := fun a =>
    (Finset.univ.filter (fun p : P => prob p = rep a)).image (fun p => pinCount t (pinEquiv t p))
  have hpair_sum : ((Finset.univ : Finset P).image pairFn).card = ∑ a ∈ legal, (S a).card := by
    rw [Finset.card_eq_sum_card_fiberwise (t := legal.image rep) (f := Prod.fst)]
    · rw [Finset.sum_image (fun a ha b hb hab => hrep_inj ha hb hab)]
      refine Finset.sum_congr rfl (fun a ha => ?_)
      refine Finset.card_bij (fun y _ => y.2) ?_ ?_ ?_
      · intro y hy
        obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
        rcases Finset.mem_image.mp hy1 with ⟨p, _, rfl⟩
        exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy2⟩, rfl⟩
      · intro y1 hy1 y2 hy2 h2
        exact Prod.ext ((Finset.mem_filter.mp hy1).2.trans (Finset.mem_filter.mp hy2).2.symm) h2
      · intro c hc
        rcases Finset.mem_image.mp hc with ⟨p, hp, rfl⟩
        have hpr := (Finset.mem_filter.mp hp).2
        exact ⟨pairFn p, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩, hpr⟩, rfl⟩
    · intro y hy
      rcases Finset.mem_image.mp hy with ⟨p, _, rfl⟩
      have : prob p ∈ (Finset.univ : Finset P).image prob := Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩
      rwa [hrep_surj] at this
  -- Characterize S a for each a ∈ legal
  have hS_card : ∀ a ∈ legal, (S a).card =
      (if a = a0Inv t then 1 else 0) + (1 + phi (toRaw a)) := by
    intro a ha
    have hredA : reducedRaw (toRaw a) := (hmem_legal a).mp ha
    obtain ⟨pa, hpa, hpa_poly⟩ := hrep a ha
    let IccA := Finset.Icc (totalCount (toRaw a)) (totalCount (toRaw a) + phi (toRaw a))
    have hsub_icc : IccA ⊆ S a := by
      intro m hm
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hm
      set r := m - totalCount (toRaw a)
      have hr : r ≤ phi (toRaw a) := by omega
      obtain ⟨b, hb, hb_poly, hbcnt, _⟩ := exists_unfuse_any hredA.1 r hr
      obtain ⟨p, hpcnt, hppoly⟩ := hwit_raw b hb
      refine Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by omega⟩
      rw [← hpa]
      exact (hprob_iff p pa).mpr (fun u v _ _ _ _ => by rw [hppoly, hb_poly, ← hpa_poly])
    have hmem_S : ∀ m ∈ S a, m ∈ IccA ∨ (m = 0 ∧ a = a0Inv t) := by
      intro m hm
      rcases Finset.mem_image.mp hm with ⟨p, hp, rfl⟩
      have hpr : prob p = prob pa := (Finset.mem_filter.mp hp).2.trans hpa.symm
      by_cases hne : ∃ k, pinEquiv t p k ≠ none
      · left
        set b := rawOfQ (pinEquiv t p) hne
        have hb : validRaw b := rawOfQ_valid (pinEquiv t p) hne
        obtain ⟨hredB, hredB_poly, hinv, hle⟩ := reduceRaw_props hb
        have hpoly_eq : ∀ u v : ℚ, 0 < u → u < 1 → 0 < v → v < 1 →
            polyOfRaw (reduceRaw b) u v = polyOfRaw (toRaw a) u v := by
          intro u v hu0 hu1 hv0 hv1
          rw [hredB_poly, ← rawOfQ_poly (pinEquiv t p) hne, ← hpa_poly]
          exact (hprob_iff p pa).mp hpr u v hu0 hu1 hv0 hv1
        have heq_red : reduceRaw b = toRaw a := reducedRaw_unique hredB hredA hpoly_eq
        rw [heq_red] at hinv hle
        rw [← rawOfQ_totalCount (pinEquiv t p) hne]
        change totalCount b ∈ IccA
        exact Finset.mem_Icc.mpr ⟨hle, by omega⟩
      · right
        push Not at hne
        have hqnone : pinEquiv t p = fun _ => none := funext hne
        have hpc0 : pinCount t (pinEquiv t p) = 0 := by
          unfold pinCount; rw [hqnone]; simp
        have hpoly_eq : ∀ u v : ℚ, 0 < u → u < 1 → 0 < v → v < 1 →
            polyOfRaw (toRaw a) u v = polyOfRaw (toRaw (a0Inv t)) u v := by
          intro u v hu0 hu1 hv0 hv1
          rw [a0Inv_poly, ← polyQ_none t, ← hqnone, ← hpa_poly]
          exact ((hprob_iff p pa).mp hpr u v hu0 hu1 hv0 hv1).symm
        exact ⟨hpc0, toRaw_injective (reducedRaw_unique hredA (a0Inv_reduced t) hpoly_eq)⟩
    have h0_not_mem : 0 ∉ IccA := by
      intro h0
      have hlo := (Finset.mem_Icc.mp h0).1
      have hpos := validRaw_pos_totalCount hredA.1
      omega
    have hicc_card : IccA.card = 1 + phi (toRaw a) := by
      simp [IccA]; omega
    by_cases ha0 : a = a0Inv t
    · have h0_mem : 0 ∈ S a := by
        let p0 : P := (pinEquiv t).symm (fun _ => none)
        have hp0_eq : pinEquiv t p0 = fun _ => none := Equiv.apply_symm_apply _ _
        refine Finset.mem_image.mpr ⟨p0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · rw [← hpa]
          apply (hprob_iff p0 pa).mpr
          intro u v _ _ _ _
          rw [hp0_eq, polyQ_none, hpa_poly, ha0, a0Inv_poly]
        · unfold pinCount; rw [hp0_eq]; simp
      have hSeq : S a = insert 0 IccA := by
        ext m
        simp only [Finset.mem_insert]
        constructor
        · intro hm
          rcases hmem_S m hm with h | ⟨rfl, _⟩
          · exact Or.inr h
          · exact Or.inl rfl
        · rintro (rfl | h)
          · exact h0_mem
          · exact hsub_icc h
      rw [hSeq, Finset.card_insert_of_notMem h0_not_mem, hicc_card, if_pos ha0]
      omega
    · have hSeq : S a = IccA := by
        ext m
        constructor
        · intro hm
          rcases hmem_S m hm with h | ⟨_, hEq⟩
          · exact h
          · exact absurd hEq ha0
        · intro hm; exact hsub_icc hm
      rw [hSeq, hicc_card, if_neg ha0, zero_add]
  have ha0_mem : a0Inv t ∈ legal := (hmem_legal _).mpr (a0Inv_reduced t)
  have hpart2 : ((Finset.univ : Finset P).image hist).card =
      1 + ∑ a ∈ legal, (1 + ∑ j : J, (a 0 true j).val * j.val.factorization 2) := by
    rw [hhist_pair, hpair_sum, Finset.sum_congr rfl hS_card, Finset.sum_add_distrib,
        Finset.sum_ite_eq' legal (a0Inv t), if_pos ha0_mem]
    rfl
  exact ⟨hpart1, hpart2⟩

end PEqualNP.Outside.L_pcx_378_aux

theorem PEqualNP.Outside.L_pcx_378 : ∀ t : ℕ,
  let n := t+1
  let I := Fin n
  let J := Fin (n+1)
  let V := Bool × I
  let P := V → Option Bool
  let hist := fun (p : P) (d : J × J) =>
    ((Finset.univ : Finset (V → Bool)).filter (fun x =>
      (∀ u, p u = none ∨ p u = some (x u)) ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,i))).card = d.1.val ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,i+1))).card = d.2.val)).card
  let prob := fun (p : P) (d : J × J) =>
    (hist p d : ℚ) / (2 : ℚ)^((Finset.univ.filter (fun u : V => p u = none)).card)
  let Inv := Fin 3 → Bool → J → Fin (2*n+1)
  let legal := (Finset.univ : Finset Inv).filter (fun a =>
    (a 0 false 0).val = 0 ∧ (a 0 true 0).val = 0 ∧
    (∀ j, (a 0 false j).val = 0 ∨ (a 0 true j).val = 0) ∧
    (∑ c : Fin 3, ∑ s : Bool, ∑ j : J,
      (a c s j).val * (2*j.val + (if c = 0 then 0 else 1))) = 2*n ∧
    (∑ s : Bool, ∑ j : J, (a 1 s j).val) = (∑ s : Bool, ∑ j : J, (a 2 s j).val) ∧
    (∑ c : Fin 3, ∑ j : J, (a c true j).val) % 2 = 0)
  ((Finset.univ : Finset P).image prob).card = legal.card ∧
    ((Finset.univ : Finset P).image hist).card =
      1 + ∑ a ∈ legal, (1 + ∑ j : J, (a 0 true j).val * j.val.factorization 2) :=
  PEqualNP.Outside.L_pcx_378_aux.main_result
