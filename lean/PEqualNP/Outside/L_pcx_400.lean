import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_400
open Polynomial Finset
abbrev R2 := Polynomial (Polynomial ℚ)
noncomputable def redW : R2 := C X * (1 + X)
noncomputable def bluW : R2 := C X
noncomputable def wq (q : ℕ) : R2 := if q % 2 = 0 then redW else bluW
def posOf (c : Bool) (i : ℕ) : ℕ := if c then 2 * i else 2 * i + 1
def pinsOf : List (ℕ × Bool) → Bool → ℕ → ℕ → Option Bool
  | [], v, Q, q => if q = Q then some v else none
  | s :: rest, v, Q, q => if q = Q then some v else pinsOf rest (Bool.xor v s.2) (Q + s.1) q
def lenSum : List (ℕ × Bool) → ℕ
  | [] => 0
  | s :: rest => s.1 + lenSum rest
def parSum : List (ℕ × Bool) → Bool
  | [] => false
  | s :: rest => Bool.xor s.2 (parSum rest)
noncomputable def stepV (w : R2) (pin : Option Bool) (φ : Bool → R2) : Bool → R2 :=
  fun c => if pin = none ∨ pin = some c then φ c + w * φ (!c) else 0
noncomputable def runV (pin : ℕ → Option Bool) (Q : ℕ) : ℕ → (Bool → R2) → (Bool → R2)
  | 0, φ => φ
  | L + 1, φ => stepV (wq (Q + L)) (pin (Q + L + 1)) (runV pin Q L φ)
noncomputable def eV (v : Bool) : Bool → R2 := fun c => if c = v then 1 else 0
def redCnt (Q L : ℕ) : ℕ := (L + 1 - Q % 2) / 2
noncomputable def segT (a b : ℕ) (π : Bool) : R2 :=
  C (C (1 / 2 : ℚ)) * ((1 + redW) ^ a * (1 + bluW) ^ b +
    (if π then -1 else 1) * ((1 - redW) ^ a * (1 - bluW) ^ b))
noncomputable def segProd : List (ℕ × Bool) → ℕ → R2
  | [], _ => 1
  | s :: rest, Q => segT (redCnt Q s.1) (s.1 - redCnt Q s.1) s.2 * segProd rest (Q + s.1)
def rrD (t : ℕ) (x : Bool × Fin (t+1) → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin (t+1) => x (false,i) ≠ x (true,i))).card
def bbD (t : ℕ) (x : Bool × Fin (t+1) → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin (t+1) => x (false,i) ≠ x (true,i+1))).card
noncomputable def profGF (t : ℕ) (p : Bool × Fin (t+1) → Option Bool) : R2 :=
  ∑ x ∈ (Finset.univ : Finset (Bool × Fin (t+1) → Bool)).filter
      (fun x => ∀ v, p v = none ∨ p v = some (x v)),
    (C X : R2) ^ (rrD t x + bbD t x) * (1 + X) ^ (rrD t x)
noncomputable def cycSum (M : ℕ) (pin : ℕ → Option Bool) : R2 :=
  ∑ y ∈ (Finset.univ : Finset (Fin (M+1) → Bool)).filter
      (fun y => ∀ q : Fin (M+1), pin q.val = none ∨ pin q.val = some (y q)),
    ∏ q : Fin (M+1), (if y q = y (q + 1) then 1 else wq q.val)
def histD (t : ℕ) (p : Bool × Fin (t+1) → Option Bool) (r b : Fin (t+1+1)) : ℕ :=
  ((Finset.univ : Finset (Bool × Fin (t+1) → Bool)).filter (fun x =>
      (∀ v, p v = none ∨ p v = some (x v)) ∧
      (Finset.univ.filter (fun i : Fin (t+1) => x (false,i) ≠ x (true,i))).card = r.val ∧
      (Finset.univ.filter (fun i : Fin (t+1) => x (false,i) ≠ x (true,i+1))).card = b.val)).card
def profileD (t : ℕ) (H : Fin (t+1+1) → Fin (t+1+1) → ℕ) (h : ℕ) (s : Fin (2*(t+1)+1)) : ℕ :=
  ∑ r : Fin (t+1+1), ∑ b : Fin (t+1+1),
    if r.val + b.val = s.val then Nat.choose r.val h * H r b else 0
def needOf (mode : Bool) (u : ℕ) : ℕ :=
  if mode then 2*(u+1)*(u+1)+4*(u+1) else (u+1)*((u+1)+1)
def kk (mode : Bool) : ℕ := if mode then 1 else 0
def dd (mode : Bool) : ℕ := if mode then 4 else 2
def gadSegs (mode : Bool) (j : ℕ) (b : Bool) : List (ℕ × Bool) :=
  if mode then
    (if b then [(4*j+2, true), (4*j+2, true), (2, true), (2, false), (2, true), (2, false)]
     else [(2*j+1, false), (2*j+1, true), (2*j+1, true), (2*j+1, false), (4, true), (4, true)])
  else [(2*j+1, b), (2*j+1, !b), (2, true)]
def gadList (mode : Bool) (y : ℕ → Bool) : ℕ → List (ℕ × Bool)
  | 0 => []
  | j + 1 => gadList mode y j ++ gadSegs mode j (y j)
def xN (u : ℕ) (x : Fin (u+1) → Bool) (j : ℕ) : Bool :=
  if h : j < u + 1 then x ⟨j, h⟩ else false
def segsFull (mode : Bool) (u t : ℕ) (x : Fin (u+1) → Bool) : List (ℕ × Bool) :=
  gadList mode (xN u x) (u+1) ++
    (if needOf mode u < t+1 then [(2*(t+1-needOf mode u), false)] else [])
def encD (mode : Bool) (u t : ℕ) (x : Fin (u+1) → Bool) : Bool × Fin (t+1) → Option Bool :=
  fun v => pinsOf (segsFull mode u t x) false 0 (posOf v.1 v.2.val)
noncomputable def gadF (j : ℕ) (b : Bool) : R2 :=
  segT (j+1) j b * segT j (j+1) (!b) * segT 1 1 true
noncomputable def gadT (j : ℕ) (b : Bool) : R2 :=
  if b then
    segT (2*j+1) (2*j+1) true * segT (2*j+1) (2*j+1) true * segT 1 1 true * segT 1 1 false *
      segT 1 1 true * segT 1 1 false
  else
    segT (j+1) j false * segT j (j+1) true * segT (j+1) j true * segT j (j+1) false *
      segT 2 2 true * segT 2 2 true
noncomputable def gad (mode : Bool) (j : ℕ) (b : Bool) : R2 := if mode then gadT j b else gadF j b
noncomputable def extraF (mode : Bool) (u t : ℕ) : R2 :=
  if needOf mode u < t+1 then segT (t+1-needOf mode u) (t+1-needOf mode u) false else 1
noncomputable def APp : R2 := (1 + redW) * (1 + bluW)
noncomputable def AMm : R2 := (1 - redW) * (1 - bluW)
noncomputable def gE (mode : Bool) (j : ℕ) : R2 :=
  if mode then gadT j true
  else C (C (1 / 4 : ℚ)) * (APp ^ (2*j+1) - AMm ^ (2*j+1)) * segT 1 1 true
noncomputable def gF (mode : Bool) (j : ℕ) : R2 :=
  if mode then C (C (-1 / 16 : ℚ)) * (C X) ^ 2 * (APp * AMm) ^ (2*j) * (APp ^ 2 - AMm ^ 2) ^ 2
  else C (C (-1 / 2 : ℚ)) * C X * (APp * AMm) ^ j * segT 1 1 true
def gc (mode : Bool) (b : Bool) : ℚ :=
  if mode then (if b then 0 else 1) else (if b then -1 else 1)
theorem Br_term (n r h s : ℕ) :
    ((((C X : R2) ^ n * (1 + X) ^ r).coeff h).coeff s) = if s = n then (r.choose h : ℚ) else 0 := by
  rw [← C_pow, coeff_C_mul, coeff_one_add_X_pow, ← C_eq_natCast, mul_comm, coeff_C_mul_X_pow]
theorem Br_rr_le (t : ℕ) (x : Bool × Fin (t+1) → Bool) : rrD t x ≤ t + 1 := by
  unfold rrD
  calc _ ≤ (Finset.univ : Finset (Fin (t+1))).card := Finset.card_filter_le _ _
    _ = t + 1 := by simp
theorem Br_bb_le (t : ℕ) (x : Bool × Fin (t+1) → Bool) : bbD t x ≤ t + 1 := by
  unfold bbD
  calc _ ≤ (Finset.univ : Finset (Fin (t+1))).card := Finset.card_filter_le _ _
    _ = t + 1 := by simp
theorem Br_coeff (t : ℕ) (p : Bool × Fin (t+1) → Option Bool) (h s : ℕ) :
    ((profGF t p).coeff h).coeff s =
      ∑ x ∈ (Finset.univ : Finset (Bool × Fin (t+1) → Bool)).filter
        (fun x => ∀ v, p v = none ∨ p v = some (x v)),
        (if s = rrD t x + bbD t x then ((rrD t x).choose h : ℚ) else 0) := by
  unfold profGF
  rw [finsetSum_coeff, finsetSum_coeff]
  exact Finset.sum_congr rfl (fun x _ => Br_term _ _ _ _)
theorem Br_hist (t : ℕ) (p : Bool × Fin (t+1) → Option Bool) (r b : Fin (t+1+1)) :
    histD t p r b = ∑ x ∈ (Finset.univ : Finset (Bool × Fin (t+1) → Bool)).filter
        (fun x => ∀ v, p v = none ∨ p v = some (x v)),
        (if rrD t x = r.val ∧ bbD t x = b.val then 1 else 0) := by
  rw [← Finset.card_filter, Finset.filter_filter]
  rfl
theorem Br_single (t a c : ℕ) (ha : a ≤ t+1) (hc : c ≤ t+1) (sv h : ℕ) :
    ∑ r : Fin (t+1+1), ∑ b : Fin (t+1+1),
      (if r.val + b.val = sv then r.val.choose h else 0) * (if a = r.val ∧ c = b.val then 1 else 0) =
    (if sv = a + c then a.choose h else 0) := by
  rw [Finset.sum_eq_single (⟨a, by omega⟩ : Fin (t+1+1))]
  · rw [Finset.sum_eq_single (⟨c, by omega⟩ : Fin (t+1+1))]
    · simp only [and_self, ite_true, mul_one]
      by_cases hs : a + c = sv
      · rw [ite_eq_left hs, ite_eq_left hs.symm]
      · rw [ite_eq_right hs, ite_eq_right (fun e => hs e.symm)]
    · intro b _ hb
      have : c ≠ b.val := fun e => hb (Fin.ext e.symm)
      simp [this]
    · simp
  · intro r _ hr
    apply Finset.sum_eq_zero
    intro b _
    have : a ≠ r.val := fun e => hr (Fin.ext e.symm)
    simp [this]
  · simp
theorem Br_prof (t : ℕ) (p : Bool × Fin (t+1) → Option Bool) (h : ℕ) (s : Fin (2*(t+1)+1)) :
    profileD t (histD t p) h s =
      ∑ x ∈ (Finset.univ : Finset (Bool × Fin (t+1) → Bool)).filter
        (fun x => ∀ v, p v = none ∨ p v = some (x v)),
        (if s.val = rrD t x + bbD t x then (rrD t x).choose h else 0) := by
  unfold profileD
  have e1 : ∀ r b : Fin (t+1+1),
      (if r.val + b.val = s.val then r.val.choose h * histD t p r b else 0) =
      ∑ x ∈ (Finset.univ : Finset (Bool × Fin (t+1) → Bool)).filter
        (fun x => ∀ v, p v = none ∨ p v = some (x v)),
        (if r.val + b.val = s.val then r.val.choose h else 0) *
          (if rrD t x = r.val ∧ bbD t x = b.val then 1 else 0) := by
    intro r b
    rw [← Finset.mul_sum, ← Br_hist]
    split_ifs <;> simp
  simp only [e1]
  rw [Finset.sum_congr rfl (fun r _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  exact Br_single t (rrD t x) (bbD t x) (Br_rr_le t x) (Br_bb_le t x) s.val h
theorem gap_bridge (t : ℕ) (p : Bool × Fin (t+1) → Option Bool) :
    (∀ (h : ℕ) (s : Fin (2*(t+1)+1)),
      ((profileD t (histD t p) h s : ℕ) : ℚ) = ((profGF t p).coeff h).coeff s.val) ∧
    (∀ (h s : ℕ), 2*(t+1) < s → ((profGF t p).coeff h).coeff s = 0) := by
  refine ⟨fun h s => ?_, fun h s hs => ?_⟩
  · rw [Br_prof, Br_coeff, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Nat.cast_ite, Nat.cast_zero]
  · rw [Br_coeff]
    refine Finset.sum_eq_zero (fun x _ => ?_)
    have h1 := Br_rr_le t x
    have h2 := Br_bb_le t x
    rw [ite_eq_right (by omega)]
def Rg1_enc (t : ℕ) (v : Bool × Fin (t+1)) : Fin (2*t+1+1) :=
  ⟨posOf v.1 v.2.val, by
    have h := v.2.isLt
    unfold posOf
    split <;> omega⟩
def Rg1_dec (t : ℕ) (q : Fin (2*t+1+1)) : Bool × Fin (t+1) :=
  (decide (q.val % 2 = 0), ⟨q.val / 2, by have h := q.isLt; omega⟩)
theorem Rg1_val_true (t : ℕ) (i : Fin (t+1)) : (Rg1_enc t (true, i)).val = 2 * i.val := rfl
theorem Rg1_val_false (t : ℕ) (i : Fin (t+1)) : (Rg1_enc t (false, i)).val = 2 * i.val + 1 := rfl
theorem Rg1_dec_enc (t : ℕ) (v : Bool × Fin (t+1)) : Rg1_dec t (Rg1_enc t v) = v := by
  obtain ⟨c, i⟩ := v
  cases c
  · refine Prod.ext ?_ (Fin.ext ?_)
    · show decide ((2 * i.val + 1) % 2 = 0) = false
      exact decide_eq_false (by omega)
    · show (2 * i.val + 1) / 2 = i.val
      omega
  · refine Prod.ext ?_ (Fin.ext ?_)
    · show decide ((2 * i.val) % 2 = 0) = true
      exact decide_eq_true (by omega)
    · show (2 * i.val) / 2 = i.val
      omega
theorem Rg1_enc_dec (t : ℕ) (q : Fin (2*t+1+1)) : Rg1_enc t (Rg1_dec t q) = q := by
  apply Fin.ext
  show posOf (decide (q.val % 2 = 0)) (q.val / 2) = q.val
  unfold posOf
  by_cases h : q.val % 2 = 0
  · rw [ite_eq_left (decide_eq_true h)]
    omega
  · rw [ite_eq_right (fun e => h (of_decide_eq_true e))]
    omega
theorem Rg1_pos_dec (t : ℕ) (q : Fin (2*t+1+1)) :
    posOf (Rg1_dec t q).1 (Rg1_dec t q).2.val = q.val :=
  congrArg Fin.val (Rg1_enc_dec t q)
theorem Rg1_bij (t : ℕ) : Function.Bijective (Rg1_enc t) :=
  Function.bijective_iff_has_inverse.mpr ⟨Rg1_dec t, Rg1_dec_enc t, Rg1_enc_dec t⟩
theorem Rg1_succ_true (t : ℕ) (i : Fin (t+1)) :
    Rg1_enc t (true, i) + 1 = Rg1_enc t (false, i) := by
  have hi := i.isLt
  apply Fin.ext
  rw [Fin.val_add_one, Rg1_val_false]
  have hne : Rg1_enc t (true, i) ≠ Fin.last (2*t+1) := by
    intro h
    have h2 := congrArg Fin.val h
    rw [Rg1_val_true, Fin.val_last] at h2
    omega
  rw [ite_eq_right hne, Rg1_val_true]
theorem Rg1_succ_false (t : ℕ) (i : Fin (t+1)) :
    Rg1_enc t (false, i) + 1 = Rg1_enc t (true, i + 1) := by
  have hi := i.isLt
  apply Fin.ext
  rw [Fin.val_add_one, Rg1_val_true, Fin.val_add_one]
  by_cases h : i = Fin.last t
  · have h1 : Rg1_enc t (false, i) = Fin.last (2*t+1) := by
      apply Fin.ext
      rw [Rg1_val_false, Fin.val_last, h, Fin.val_last]
    rw [ite_eq_left h1, ite_eq_left h]
  · have hlt : i.val < t := by
      have : i.val ≠ t := fun e => h (Fin.ext (by rw [e, Fin.val_last]))
      omega
    have h1 : Rg1_enc t (false, i) ≠ Fin.last (2*t+1) := by
      intro e
      have h2 := congrArg Fin.val e
      rw [Rg1_val_false, Fin.val_last] at h2
      omega
    rw [ite_eq_right h1, ite_eq_right h, Rg1_val_false]
    omega
theorem Rg1_wq_even (n : ℕ) : wq (2 * n) = redW := by
  unfold wq
  rw [ite_eq_left (by omega)]
theorem Rg1_wq_odd (n : ℕ) : wq (2 * n + 1) = bluW := by
  unfold wq
  rw [ite_eq_right (by omega)]
theorem Rg1_pow_card {n : ℕ} (P : Fin n → Prop) [DecidablePred P] (w : R2) :
    (∏ i : Fin n, (if P i then 1 else w)) = w ^ (Finset.univ.filter (fun i => ¬ P i)).card := by
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
theorem Rg1_prod (t : ℕ) (x : Bool × Fin (t+1) → Bool) :
    (∏ q : Fin (2*t+1+1), (if x (Rg1_dec t q) = x (Rg1_dec t (q + 1)) then (1:R2) else wq q.val)) =
      (C X : R2) ^ (rrD t x + bbD t x) * (1 + X) ^ (rrD t x) := by
  rw [← (Rg1_bij t).prod_comp, Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [Rg1_succ_true, Rg1_succ_false, Rg1_dec_enc, Rg1_val_true, Rg1_val_false,
    Rg1_wq_even, Rg1_wq_odd]
  rw [Rg1_pow_card, Rg1_pow_card]
  have hr : (Finset.univ.filter (fun i : Fin (t+1) => ¬ (x (true,i) = x (false,i)))).card =
      rrD t x := by
    unfold rrD
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h e => h e.symm, fun h e => h e.symm⟩
  have hb : (Finset.univ.filter (fun i : Fin (t+1) => ¬ (x (false,i) = x (true,i+1)))).card =
      bbD t x := rfl
  rw [hr, hb]
  unfold redW bluW
  rw [mul_pow, pow_add]
  ring
theorem gap_ring1 (t : ℕ) (pin : ℕ → Option Bool) :
    profGF t (fun v => pin (posOf v.1 v.2.val)) = cycSum (2*t+1) pin := by
  unfold profGF cycSum
  refine Finset.sum_nbij' (fun x q => x (Rg1_dec t q)) (fun y v => y (Rg1_enc t v))
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro q
    have h := hx (Rg1_dec t q)
    rw [Rg1_pos_dec] at h
    exact h
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    intro v
    exact hy (Rg1_enc t v)
  · intro x _
    funext v
    simp only [Rg1_dec_enc]
  · intro y _
    funext q
    simp only [Rg1_enc_dec]
  · intro x _
    exact (Rg1_prod t x).symm
noncomputable def Rg2_pf (o : Option Bool) (b : Bool) : R2 := if o = none ∨ o = some b then 1 else 0
noncomputable def Rg2_W (pin : ℕ → Option Bool) (L : ℕ) (y : Fin (L+1) → Bool) : R2 :=
  ∏ q : Fin L, (Rg2_pf (pin (q.val + 1)) (y q.succ) *
    (if y q.castSucc = y q.succ then 1 else wq q.val))
noncomputable def Rg2_P (pin : ℕ → Option Bool) (φ : Bool → R2) (L : ℕ) (c : Bool) : R2 :=
  ∑ y : Fin (L+1) → Bool, (if y (Fin.last L) = c then φ (y 0) * Rg2_W pin L y else 0)
theorem Rg2_sum_snoc (n : ℕ) (F : (Fin (n+1) → Bool) → R2) :
    ∑ y : Fin (n+1) → Bool, F y = ∑ b : Bool, ∑ z : Fin n → Bool, F (Fin.snoc z b) := by
  rw [← Fintype.sum_prod_type' (fun (b : Bool) (z : Fin n → Bool) => F (Fin.snoc z b))]
  exact (Fintype.sum_bijective _ (Fin.snocEquiv (fun _ => Bool)).bijective _ _
    (fun _ => rfl)).symm
theorem Rg2_snoc_zero (L : ℕ) (z : Fin (L+1) → Bool) (b : Bool) :
    (Fin.snoc z b : Fin (L+1+1) → Bool) 0 = z 0 := by
  have h : (0 : Fin (L+1+1)) = Fin.castSucc (0 : Fin (L+1)) := rfl
  rw [h, Fin.snoc_castSucc]
theorem Rg2_W_snoc (pin : ℕ → Option Bool) (L : ℕ) (z : Fin (L+1) → Bool) (b : Bool) :
    Rg2_W pin (L+1) (Fin.snoc z b) = Rg2_W pin L z *
      (Rg2_pf (pin (L+1)) b * (if z (Fin.last L) = b then 1 else wq L)) := by
  unfold Rg2_W
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun q _ => ?_)
    simp only [Fin.val_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc]
  · simp only [Fin.val_last, Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc]
theorem Rg2_P_succ (pin : ℕ → Option Bool) (φ : Bool → R2) (L : ℕ) (c : Bool) :
    Rg2_P pin φ (L+1) c = ∑ z : Fin (L+1) → Bool, φ (z 0) * (Rg2_W pin L z *
      (Rg2_pf (pin (L+1)) c * (if z (Fin.last L) = c then 1 else wq L))) := by
  unfold Rg2_P
  rw [Rg2_sum_snoc]
  simp only [Fin.snoc_last, Rg2_snoc_zero, Rg2_W_snoc]
  rw [Fintype.sum_bool]
  cases c <;> simp
theorem Rg2_run (pin : ℕ → Option Bool) (φ : Bool → R2) :
    ∀ L c, runV pin 0 L φ c = Rg2_P pin φ L c := by
  intro L
  induction L with
  | zero =>
    intro c
    rw [Rg2_P, Rg2_sum_snoc, Fintype.sum_bool]
    cases c <;> simp [Fin.snoc_zero, Rg2_W, runV]
  | succ L ih =>
    intro c
    rw [Rg2_P_succ]
    simp only [runV, stepV, zero_add]
    rw [ih c, ih (!c)]
    have key : ∀ z : Fin (L+1) → Bool, φ (z 0) * (Rg2_W pin L z * (Rg2_pf (pin (L+1)) c *
        (if z (Fin.last L) = c then 1 else wq L))) = Rg2_pf (pin (L+1)) c *
        ((if z (Fin.last L) = c then φ (z 0) * Rg2_W pin L z else 0) +
          wq L * (if z (Fin.last L) = !c then φ (z 0) * Rg2_W pin L z else 0)) := by
      intro z
      cases hz : z (Fin.last L) <;> cases c <;> simp <;> ring
    rw [Finset.sum_congr rfl (fun z _ => key z), ← Finset.mul_sum, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    unfold Rg2_pf Rg2_P
    split_ifs <;> simp
theorem gap_ring2 (M : ℕ) (pin : ℕ → Option Bool) (h0 : pin 0 = some false)
    (h1 : pin (M+1) = some false) :
    cycSum M pin = runV pin 0 (M+1) (eV false) false := by
  rw [Rg2_run, Rg2_P_succ, cycSum, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have hp1 : Rg2_pf (pin (M+1)) false = 1 := by simp [Rg2_pf, h1]
  rw [hp1, one_mul]
  cases hy0 : y 0 with
  | true =>
    have hn : ¬ (∀ q : Fin (M+1), pin q.val = none ∨ pin q.val = some (y q)) := by
      intro h
      have h' := h 0
      simp [h0, hy0] at h'
    rw [ite_eq_right hn]
    simp [eV]
  | false =>
    have he : eV false false = 1 := by simp [eV]
    rw [he, one_mul]
    by_cases hc : ∀ q : Fin M, pin (q.val + 1) = none ∨ pin (q.val + 1) = some (y q.succ)
    · have hall : ∀ q : Fin (M+1), pin q.val = none ∨ pin q.val = some (y q) := by
        refine Fin.forall_fin_succ.mpr ⟨?_, fun i => ?_⟩
        · simp [h0, hy0]
        · exact hc i
      rw [ite_eq_left hall, Fin.prod_univ_castSucc]
      unfold Rg2_W
      rw [Finset.prod_mul_distrib]
      have hpf : ∏ q : Fin M, Rg2_pf (pin (q.val+1)) (y q.succ) = 1 :=
        Finset.prod_eq_one (fun q _ => by simp [Rg2_pf, hc q])
      rw [hpf, one_mul]
      congr 1
      · refine Finset.prod_congr rfl (fun q _ => ?_)
        rw [Fin.coeSucc_eq_succ, Fin.val_castSucc]
      · rw [Fin.last_add_one, hy0, Fin.val_last]
    · obtain ⟨q, hq0⟩ := not_forall.mp hc
      have hq := not_or.mp hq0
      have hn : ¬ (∀ q : Fin (M+1), pin q.val = none ∨ pin q.val = some (y q)) := by
        intro h
        rcases h q.succ with h' | h'
        · exact hq.1 h'
        · exact hq.2 h'
      rw [ite_eq_right hn]
      unfold Rg2_W
      rw [Finset.prod_eq_zero (Finset.mem_univ q) (by simp [Rg2_pf, hq])]
      simp
theorem Sg_lt (segs : List (ℕ × Bool)) : ∀ (v : Bool) (Q q : ℕ), q < Q → pinsOf segs v Q q = none := by
  induction segs with
  | nil =>
    intro v Q q h
    simp only [pinsOf]
    rw [ite_eq_right (show q ≠ Q by omega)]
  | cons s rest ih =>
    intro v Q q h
    simp only [pinsOf]
    rw [ite_eq_right (show q ≠ Q by omega)]
    exact ih _ _ _ (by omega)
theorem Sg_start (segs : List (ℕ × Bool)) (v : Bool) (Q : ℕ) : pinsOf segs v Q Q = some v := by
  cases segs with
  | nil => simp [pinsOf]
  | cons s rest => simp [pinsOf]
theorem Sg_tail (L : ℕ) (π : Bool) (rest : List (ℕ × Bool)) (v : Bool) (Q q : ℕ) (h : q ≠ Q) :
    pinsOf ((L, π) :: rest) v Q q = pinsOf rest (Bool.xor v π) (Q + L) q := by
  simp only [pinsOf]
  rw [ite_eq_right h]
theorem Sg_loc (p1 p2 : ℕ → Option Bool) (Q : ℕ) (φ : Bool → R2) : ∀ L : ℕ,
    (∀ i, i < L → p1 (Q + i + 1) = p2 (Q + i + 1)) → runV p1 Q L φ = runV p2 Q L φ
  | 0, _ => rfl
  | L + 1, h => by
    simp only [runV]
    rw [Sg_loc p1 p2 Q φ L (fun i hi => h i (by omega)), h L (by omega)]
theorem Sg_lin (pin : ℕ → Option Bool) (Q : ℕ) (a : R2) (φ : Bool → R2) : ∀ L : ℕ,
    runV pin Q L (fun c => a * φ c) = fun c => a * runV pin Q L φ c
  | 0 => rfl
  | L + 1 => by
    simp only [runV]
    rw [Sg_lin pin Q a φ L]
    funext c
    simp only [stepV]
    split_ifs <;> ring
theorem Sg_lin2 (pin : ℕ → Option Bool) (Q : ℕ) (a : R2) (φ : Bool → R2) (L : ℕ) (c : Bool) :
    runV pin Q L (fun c => a * φ c) c = a * runV pin Q L φ c := by
  rw [Sg_lin]
theorem Sg_comp (pin : ℕ → Option Bool) (Q L1 : ℕ) (φ : Bool → R2) : ∀ L2 : ℕ,
    runV pin Q (L1 + L2) φ = runV pin (Q + L1) L2 (runV pin Q L1 φ)
  | 0 => rfl
  | L2 + 1 => by
    show stepV (wq (Q + (L1 + L2))) (pin (Q + (L1 + L2) + 1)) (runV pin Q (L1 + L2) φ) =
      stepV (wq (Q + L1 + L2)) (pin (Q + L1 + L2 + 1)) (runV pin (Q + L1) L2 (runV pin Q L1 φ))
    rw [Sg_comp pin Q L1 φ L2, Nat.add_assoc Q L1 L2]
theorem Sg_step_none (w : R2) (φ : Bool → R2) (c : Bool) :
    stepV w none φ c = φ c + w * φ (!c) := by
  simp [stepV]
theorem Sg_step_some (w : R2) (d : Bool) (φ : Bool → R2) (c : Bool) :
    stepV w (some d) φ c = if c = d then φ c + w * φ (!c) else 0 := by
  unfold stepV
  by_cases h : c = d
  · subst h
    simp
  · have h' : ¬ (d = c) := fun e => h e.symm
    simp [h, h']
theorem Sg_eV_self (v : Bool) : eV v v = 1 := by
  simp [eV]
theorem Sg_eV_ne (v c : Bool) (h : ¬ c = v) : eV v c = 0 := by
  simp [eV, h]
noncomputable def Sg_A (Q l : ℕ) : R2 := (1 + redW) ^ (redCnt Q l) * (1 + bluW) ^ (l - redCnt Q l)
noncomputable def Sg_B (Q l : ℕ) : R2 := (1 - redW) ^ (redCnt Q l) * (1 - bluW) ^ (l - redCnt Q l)
theorem Sg_AB_succ (Q l : ℕ) :
    Sg_A Q (l+1) = (1 + wq (Q + l)) * Sg_A Q l ∧ Sg_B Q (l+1) = (1 - wq (Q + l)) * Sg_B Q l := by
  unfold Sg_A Sg_B wq
  by_cases h : (Q + l) % 2 = 0
  · have h1 : redCnt Q (l+1) = redCnt Q l + 1 := by unfold redCnt; omega
    have h2 : l + 1 - redCnt Q (l+1) = l - redCnt Q l := by unfold redCnt; omega
    rw [ite_eq_left h, h2, h1]
    constructor <;> ring
  · have h1 : redCnt Q (l+1) = redCnt Q l := by unfold redCnt; omega
    have h2 : l + 1 - redCnt Q (l+1) = l - redCnt Q l + 1 := by unfold redCnt; omega
    rw [ite_eq_right h, h2, h1]
    constructor <;> ring
theorem Sg_AB_zero (Q : ℕ) : Sg_A Q 0 = 1 ∧ Sg_B Q 0 = 1 := by
  have h : redCnt Q 0 = 0 := by unfold redCnt; omega
  unfold Sg_A Sg_B
  rw [h]
  simp
theorem Sg_half : (C (C (1/2 : ℚ)) : R2) + C (C (1/2 : ℚ)) = 1 := by
  rw [← C_add, ← C_add]
  norm_num
theorem Sg_sgn (c v : Bool) : (if (!c) = v then (1:R2) else -1) = -(if c = v then 1 else -1) := by
  cases c <;> cases v <;> simp
theorem Sg_sgn2 (v π : Bool) :
    (if (Bool.xor v π) = v then (1:R2) else -1) = if π then -1 else 1 := by
  cases v <;> cases π <;> simp
theorem Sg_free (pin : ℕ → Option Bool) (Q : ℕ) (v : Bool) : ∀ l : ℕ,
    (∀ i, i < l → pin (Q + i + 1) = none) → ∀ c : Bool,
    runV pin Q l (eV v) c = C (C (1/2 : ℚ)) * (Sg_A Q l + (if c = v then 1 else -1) * Sg_B Q l)
  | 0, _, c => by
    obtain ⟨hA, hB⟩ := Sg_AB_zero Q
    rw [hA, hB]
    show eV v c = _
    unfold eV
    have h2 := Sg_half
    split_ifs with hc
    · linear_combination (-1 : R2) * h2
    · ring
  | l + 1, hf, c => by
    have hp : pin (Q + l + 1) = none := hf l (by omega)
    have ih := Sg_free pin Q v l (fun i hi => hf i (by omega))
    obtain ⟨hA, hB⟩ := Sg_AB_succ Q l
    show stepV (wq (Q + l)) (pin (Q + l + 1)) (runV pin Q l (eV v)) c = _
    rw [hp, Sg_step_none, ih c, ih (!c), hA, hB, Sg_sgn]
    ring
theorem Sg_one (pin : ℕ → Option Bool) (Q n : ℕ) (v π : Bool)
    (hfree : ∀ i, i < n → pin (Q + i + 1) = none) (hend : pin (Q + n + 1) = some (Bool.xor v π))
    (c : Bool) :
    runV pin Q (n + 1) (eV v) c =
      segT (redCnt Q (n+1)) (n + 1 - redCnt Q (n+1)) π * eV (Bool.xor v π) c := by
  have ih := Sg_free pin Q v n hfree
  obtain ⟨hA, hB⟩ := Sg_AB_succ Q n
  have hT : segT (redCnt Q (n+1)) (n + 1 - redCnt Q (n+1)) π =
      C (C (1/2 : ℚ)) * (Sg_A Q (n+1) + (if π then -1 else 1) * Sg_B Q (n+1)) := rfl
  show stepV (wq (Q + n)) (pin (Q + n + 1)) (runV pin Q n (eV v)) c = _
  rw [hend, Sg_step_some, hT]
  by_cases hc : c = Bool.xor v π
  · subst hc
    rw [ite_eq_left (rfl : Bool.xor v π = Bool.xor v π), Sg_eV_self, ih, ih, hA, hB, Sg_sgn, Sg_sgn2]
    ring
  · rw [ite_eq_right hc, Sg_eV_ne _ _ hc, mul_zero]
theorem gap_seg (segs : List (ℕ × Bool)) (hL : ∀ s ∈ segs, 1 ≤ s.1) (v : Bool) (Q : ℕ)
    (c : Bool) :
    runV (pinsOf segs v Q) Q (lenSum segs) (eV v) c =
      segProd segs Q * eV (Bool.xor v (parSum segs)) c := by
  induction segs generalizing v Q c with
  | nil =>
    simp only [lenSum, parSum, segProd, runV, Bool.xor_false, one_mul]
  | cons s rest ih =>
    obtain ⟨L, π⟩ := s
    have hL1 : 1 ≤ L := hL (L, π) (by simp)
    have hr : ∀ s' ∈ rest, 1 ≤ s'.1 := fun s' hs' => hL s' (by simp [hs'])
    obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
    have hfree : ∀ i, i < n → pinsOf ((n+1, π) :: rest) v Q (Q + i + 1) = none := by
      intro i hi
      rw [Sg_tail (n+1) π rest v Q (Q + i + 1) (by omega)]
      exact Sg_lt _ _ _ _ (by omega)
    have hend : pinsOf ((n+1, π) :: rest) v Q (Q + n + 1) = some (Bool.xor v π) := by
      rw [Sg_tail (n+1) π rest v Q (Q + n + 1) (by omega), show Q + n + 1 = Q + (n + 1) by ring]
      exact Sg_start _ _ _
    have h1 : runV (pinsOf ((n+1, π) :: rest) v Q) Q (n + 1) (eV v) =
        fun c => segT (redCnt Q (n+1)) (n + 1 - redCnt Q (n+1)) π * eV (Bool.xor v π) c := by
      funext c
      exact Sg_one _ Q n v π hfree hend c
    have hloc : runV (pinsOf ((n+1, π) :: rest) v Q) (Q + (n+1)) (lenSum rest)
        (eV (Bool.xor v π)) =
        runV (pinsOf rest (Bool.xor v π) (Q + (n+1))) (Q + (n+1)) (lenSum rest)
          (eV (Bool.xor v π)) := by
      apply Sg_loc
      intro i hi
      exact Sg_tail (n+1) π rest v Q _ (by omega)
    simp only [lenSum, parSum, segProd]
    rw [Sg_comp, h1, Sg_lin2, hloc, ih hr, Bool.xor_assoc, mul_assoc]
theorem Ct_none_lt (segs : List (ℕ × Bool)) (v : Bool) (Q q : ℕ) (h : q < Q) :
    pinsOf segs v Q q = none := by
  induction segs generalizing v Q with
  | nil =>
    simp only [pinsOf]
    rw [ite_eq_right (by omega)]
  | cons s rest ih =>
    simp only [pinsOf]
    rw [ite_eq_right (by omega)]
    exact ih _ _ (by omega)
theorem Ct_cons_eq (s : ℕ × Bool) (rest : List (ℕ × Bool)) (v : Bool) (Q q : ℕ) :
    pinsOf (s :: rest) v Q q =
      if q = Q then some v else pinsOf rest (Bool.xor v s.2) (Q + s.1) q := rfl
theorem Ct_card_Ico (segs : List (ℕ × Bool)) (hL : ∀ s ∈ segs, 1 ≤ s.1) (v : Bool) (Q : ℕ) :
    ((Finset.Ico Q (Q + lenSum segs)).filter
      (fun q => (pinsOf segs v Q q).isSome)).card = segs.length := by
  induction segs generalizing v Q with
  | nil => simp [lenSum]
  | cons s rest ih =>
    have h1 : 1 ≤ s.1 := hL s (by simp)
    have hr : ∀ s' ∈ rest, 1 ≤ s'.1 := fun s' hs' => hL s' (by simp [hs'])
    have hsplit : (Finset.Ico Q (Q + lenSum (s :: rest))).filter
        (fun q => (pinsOf (s :: rest) v Q q).isSome) =
      insert Q ((Finset.Ico (Q + s.1) (Q + s.1 + lenSum rest)).filter
        (fun q => (pinsOf rest (Bool.xor v s.2) (Q + s.1) q).isSome)) := by
      ext q
      rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter, Finset.mem_Ico,
        Finset.mem_Ico, Ct_cons_eq]
      have e : lenSum (s :: rest) = s.1 + lenSum rest := rfl
      rw [e]
      constructor
      · rintro ⟨⟨hq1, hq2⟩, hs⟩
        by_cases hqQ : q = Q
        · exact Or.inl hqQ
        · right
          rw [ite_eq_right hqQ] at hs
          have hge : Q + s.1 ≤ q := by
            by_contra hc
            rw [Ct_none_lt _ _ _ _ (by omega)] at hs
            simp at hs
          exact ⟨⟨hge, by omega⟩, hs⟩
      · rintro (hq | ⟨⟨hq1, hq2⟩, hs⟩)
        · refine ⟨⟨by omega, by omega⟩, ?_⟩
          rw [ite_eq_left hq]
          rfl
        · rw [ite_eq_right (by omega)]
          exact ⟨⟨by omega, by omega⟩, hs⟩
    rw [hsplit, Finset.card_insert_of_notMem, ih hr, List.length_cons]
    rw [Finset.mem_filter, Finset.mem_Ico]
    intro h
    omega
theorem Ct_posOf_lt (t : ℕ) (w : Bool × Fin (t+1)) : posOf w.1 w.2.val < 2*(t+1) := by
  have := w.2.isLt
  unfold posOf
  split_ifs <;> omega
theorem Ct_posOf_inj (t : ℕ) (a b : Bool × Fin (t+1))
    (h : posOf a.1 a.2.val = posOf b.1 b.2.val) : a = b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  have e1 : a1 = b1 := by
    cases a1 <;> cases b1 <;> simp [posOf] at h ⊢ <;> omega
  subst e1
  have e2 : a2.val = b2.val := by
    cases a1 <;> simp [posOf] at h <;> omega
  rw [Fin.ext e2]
theorem gap_count (t : ℕ) (segs : List (ℕ × Bool)) (hL : ∀ s ∈ segs, 1 ≤ s.1)
    (hsum : lenSum segs = 2*(t+1)) (v : Bool) :
    (Finset.univ.filter (fun w : Bool × Fin (t+1) =>
      (pinsOf segs v 0 (posOf w.1 w.2.val)).isSome)).card = segs.length := by
  have key := Ct_card_Ico segs hL v 0
  rw [zero_add, hsum] at key
  rw [← key]
  apply Finset.card_bij (fun w _ => posOf w.1 w.2.val)
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨Nat.zero_le _, Ct_posOf_lt t w⟩, hw⟩
  · intro a _ b _ hab
    exact Ct_posOf_inj t a b hab
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_Ico] at hq
    obtain ⟨⟨-, hq2⟩, hs⟩ := hq
    have hlt : q / 2 < t + 1 := by omega
    have hp : posOf (decide (q % 2 = 0)) (q / 2) = q := by
      unfold posOf
      split_ifs with h2
      · have : q % 2 = 0 := by simpa using h2
        omega
      · have : q % 2 ≠ 0 := by simpa using h2
        omega
    refine ⟨(decide (q % 2 = 0), ⟨q / 2, hlt⟩), ?_, hp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show (pinsOf segs v 0 (posOf (decide (q % 2 = 0)) (q / 2))).isSome = true
    rw [hp]
    exact hs
theorem Ly_lenSum_append (l1 l2 : List (ℕ × Bool)) :
    lenSum (l1 ++ l2) = lenSum l1 + lenSum l2 := by
  induction l1 with
  | nil => simp [lenSum]
  | cons s rest ih =>
    simp only [List.cons_append, lenSum, ih]
    omega
theorem Ly_parSum_append (l1 l2 : List (ℕ × Bool)) :
    parSum (l1 ++ l2) = Bool.xor (parSum l1) (parSum l2) := by
  induction l1 with
  | nil => simp [parSum]
  | cons s rest ih => simp only [List.cons_append, parSum, ih, Bool.xor_assoc]
theorem Ly_gadSegs_pos (mode : Bool) (j : ℕ) (b : Bool) : ∀ s ∈ gadSegs mode j b, 1 ≤ s.1 := by
  cases mode <;> cases b <;> simp [gadSegs]
theorem Ly_gadSegs_len (mode : Bool) (j : ℕ) (b : Bool) :
    lenSum (gadSegs mode j b) = if mode then 8*j+12 else 4*j+4 := by
  cases mode <;> cases b <;> simp [gadSegs, lenSum] <;> omega
theorem Ly_gadSegs_par (mode : Bool) (j : ℕ) (b : Bool) : parSum (gadSegs mode j b) = false := by
  cases mode <;> cases b <;> rfl
theorem Ly_gadSegs_length (mode : Bool) (j : ℕ) (b : Bool) :
    (gadSegs mode j b).length = if mode then 6 else 3 := by
  cases mode <;> cases b <;> rfl
theorem Ly_gadSegs_map (j : ℕ) (b b' : Bool) :
    (gadSegs false j b).map Prod.fst = (gadSegs false j b').map Prod.fst := by
  cases b <;> cases b' <;> rfl
theorem Ly_gadList_pos (mode : Bool) (y : ℕ → Bool) (J : ℕ) :
    ∀ s ∈ gadList mode y J, 1 ≤ s.1 := by
  induction J with
  | zero => simp [gadList]
  | succ J ih =>
    intro s hs
    simp only [gadList, List.mem_append] at hs
    rcases hs with hs | hs
    · exact ih s hs
    · exact Ly_gadSegs_pos mode J (y J) s hs
theorem Ly_gadList_len (mode : Bool) (y : ℕ → Bool) (J : ℕ) :
    lenSum (gadList mode y J) = if mode then 4*J*(J+2) else 2*J*(J+1) := by
  induction J with
  | zero => simp [gadList, lenSum]
  | succ J ih =>
    simp only [gadList, Ly_lenSum_append, ih, Ly_gadSegs_len]
    cases mode <;> simp <;> ring
theorem Ly_gadList_par (mode : Bool) (y : ℕ → Bool) (J : ℕ) :
    parSum (gadList mode y J) = false := by
  induction J with
  | zero => rfl
  | succ J ih => simp only [gadList, Ly_parSum_append, ih, Ly_gadSegs_par, Bool.xor_false]
theorem Ly_gadList_length (mode : Bool) (y : ℕ → Bool) (J : ℕ) :
    (gadList mode y J).length = if mode then 6*J else 3*J := by
  induction J with
  | zero => simp [gadList]
  | succ J ih =>
    simp only [gadList, List.length_append, ih, Ly_gadSegs_length]
    cases mode <;> simp <;> ring
theorem Ly_gadList_map (y y' : ℕ → Bool) (J : ℕ) :
    (gadList false y J).map Prod.fst = (gadList false y' J).map Prod.fst := by
  induction J with
  | zero => rfl
  | succ J ih =>
    simp only [gadList, List.map_append]
    rw [ih, Ly_gadSegs_map J (y J) (y' J)]
theorem Ly_gad_need (mode : Bool) (y : ℕ → Bool) (u : ℕ) :
    lenSum (gadList mode y (u+1)) = 2 * needOf mode u := by
  rw [Ly_gadList_len]
  cases mode <;> simp [needOf] <;> ring
theorem gap_layout (mode : Bool) (u t : ℕ) (x : Fin (u+1) → Bool) (hn : needOf mode u ≤ t+1) :
    (∀ s ∈ segsFull mode u t x, 1 ≤ s.1) ∧
    lenSum (segsFull mode u t x) = 2*(t+1) ∧
    parSum (segsFull mode u t x) = false ∧
    (segsFull mode u t x).length =
      (if mode then 6*(u+1) else 3*(u+1)) + (if needOf mode u < t+1 then 1 else 0) ∧
    (mode = false → ∀ y : Fin (u+1) → Bool,
      (segsFull mode u t x).map Prod.fst = (segsFull mode u t y).map Prod.fst) := by
  have hpos := Ly_gadList_pos mode (xN u x) (u+1)
  have hlen := Ly_gad_need mode (xN u x) u
  have hpar := Ly_gadList_par mode (xN u x) (u+1)
  have hlg := Ly_gadList_length mode (xN u x) (u+1)
  unfold segsFull
  by_cases hlt : needOf mode u < t+1
  · simp only [ite_eq_left hlt]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro s hs
      rw [List.mem_append] at hs
      rcases hs with hs | hs
      · exact hpos s hs
      · rw [List.mem_singleton] at hs
        rw [hs]
        show 1 ≤ 2 * (t + 1 - needOf mode u)
        omega
    · rw [Ly_lenSum_append, hlen]
      simp only [lenSum]
      omega
    · rw [Ly_parSum_append, hpar]
      rfl
    · rw [List.length_append, hlg]
      rfl
    · intro hm y
      rw [List.map_append, List.map_append]
      subst hm
      rw [Ly_gadList_map (xN u x) (xN u y)]
  · simp only [ite_eq_right hlt, List.append_nil]
    refine ⟨hpos, ?_, hpar, ?_, ?_⟩
    · rw [hlen]
      omega
    · rw [hlg]
      rfl
    · intro hm y
      subst hm
      exact Ly_gadList_map _ _ _
theorem Pd_app (l1 l2 : List (ℕ × Bool)) (Q : ℕ) :
    segProd (l1 ++ l2) Q = segProd l1 Q * segProd l2 (Q + lenSum l1) := by
  induction l1 generalizing Q with
  | nil => simp only [List.nil_append, segProd, lenSum, one_mul, Nat.add_zero]
  | cons s rest ih =>
    simp only [List.cons_append, segProd, lenSum]
    rw [ih (Q + s.1), mul_assoc, Nat.add_assoc]
theorem Pd_lenApp (l1 l2 : List (ℕ × Bool)) :
    lenSum (l1 ++ l2) = lenSum l1 + lenSum l2 := by
  induction l1 with
  | nil => simp only [List.nil_append, lenSum, Nat.zero_add]
  | cons s rest ih =>
    simp only [List.cons_append, lenSum]
    rw [ih, Nat.add_assoc]
theorem Pd_lenGad (mode : Bool) (j : ℕ) (b : Bool) :
    lenSum (gadSegs mode j b) % 2 = 0 := by
  cases mode <;> cases b <;>
    simp only [gadSegs, lenSum, Bool.false_eq_true, ↓reduceIte, Bool.not_true, Bool.not_false] <;>
    omega
theorem Pd_lenList (mode : Bool) (y : ℕ → Bool) (J : ℕ) :
    lenSum (gadList mode y J) % 2 = 0 := by
  induction J with
  | zero => simp only [gadList, lenSum, Nat.zero_mod]
  | succ J ih =>
    simp only [gadList]
    rw [Pd_lenApp]
    have := Pd_lenGad mode J (y J)
    omega
theorem Pd_cons (L : ℕ) (π : Bool) (rest : List (ℕ × Bool)) (Q a b : ℕ)
    (h : (L + 1 - Q % 2) / 2 = a) (h2 : L - a = b) :
    segProd ((L, π) :: rest) Q = segT a b π * segProd rest (Q + L) := by
  subst h h2
  rfl
theorem Pd_nil (Q : ℕ) : segProd [] Q = 1 := rfl
theorem Pd_gadSegs (mode : Bool) (j : ℕ) (b : Bool) (Q : ℕ) (hQ : Q % 2 = 0) :
    segProd (gadSegs mode j b) Q = gad mode j b := by
  cases mode
  · simp only [gadSegs, gad, gadF, Bool.false_eq_true, ite_false]
    rw [Pd_cons (2*j+1) b _ Q (j+1) j (by omega) (by omega),
      Pd_cons (2*j+1) (!b) _ (Q + (2*j+1)) j (j+1) (by omega) (by omega),
      Pd_cons 2 true _ (Q + (2*j+1) + (2*j+1)) 1 1 (by omega) (by omega), Pd_nil]
    ring
  · cases b
    · simp only [gadSegs, gad, gadT, Bool.false_eq_true, ite_false, ite_true]
      rw [Pd_cons (2*j+1) false _ Q (j+1) j (by omega) (by omega),
        Pd_cons (2*j+1) true _ (Q + (2*j+1)) j (j+1) (by omega) (by omega),
        Pd_cons (2*j+1) true _ (Q + (2*j+1) + (2*j+1)) (j+1) j (by omega) (by omega),
        Pd_cons (2*j+1) false _ (Q + (2*j+1) + (2*j+1) + (2*j+1)) j (j+1) (by omega) (by omega),
        Pd_cons 4 true _ (Q + (2*j+1) + (2*j+1) + (2*j+1) + (2*j+1)) 2 2 (by omega) (by omega),
        Pd_cons 4 true _ (Q + (2*j+1) + (2*j+1) + (2*j+1) + (2*j+1) + 4) 2 2 (by omega)
          (by omega), Pd_nil]
      ring
    · simp only [gadSegs, gad, gadT, ite_true]
      rw [Pd_cons (4*j+2) true _ Q (2*j+1) (2*j+1) (by omega) (by omega),
        Pd_cons (4*j+2) true _ (Q + (4*j+2)) (2*j+1) (2*j+1) (by omega) (by omega),
        Pd_cons 2 true _ (Q + (4*j+2) + (4*j+2)) 1 1 (by omega) (by omega),
        Pd_cons 2 false _ (Q + (4*j+2) + (4*j+2) + 2) 1 1 (by omega) (by omega),
        Pd_cons 2 true _ (Q + (4*j+2) + (4*j+2) + 2 + 2) 1 1 (by omega) (by omega),
        Pd_cons 2 false _ (Q + (4*j+2) + (4*j+2) + 2 + 2 + 2) 1 1 (by omega) (by omega),
        Pd_nil]
      ring
theorem Pd_gadList (mode : Bool) (y : ℕ → Bool) (J Q : ℕ) (hQ : Q % 2 = 0) :
    segProd (gadList mode y J) Q = ∏ j ∈ range J, gad mode j (y j) := by
  induction J with
  | zero => simp only [gadList, segProd, Finset.range_zero, Finset.prod_empty]
  | succ J ih =>
    simp only [gadList]
    rw [Pd_app, ih, Pd_gadSegs mode J (y J) _ (by have := Pd_lenList mode y J; omega),
      Finset.prod_range_succ]
theorem Pd_extra (mode : Bool) (u t Q : ℕ) (hQ : Q % 2 = 0) :
    segProd (if needOf mode u < t+1 then [(2*(t+1-needOf mode u), false)] else []) Q =
      extraF mode u t := by
  unfold extraF
  split_ifs with h
  · rw [Pd_cons (2*(t+1-needOf mode u)) false _ Q (t+1-needOf mode u) (t+1-needOf mode u)
      (by omega) (by omega), Pd_nil, mul_one]
  · exact Pd_nil Q
theorem gap_prod (mode : Bool) (u t : ℕ) (x : Fin (u+1) → Bool) :
    segProd (segsFull mode u t x) 0 = (∏ j : Fin (u+1), gad mode j.val (x j)) * extraF mode u t := by
  unfold segsFull
  rw [Pd_app, Pd_gadList mode _ _ 0 (Nat.zero_mod 2),
    Pd_extra mode u t _ (by have := Pd_lenList mode (xN u x) (u+1); omega)]
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (fun j => gad mode j (xN u x j))]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  have e : xN u x j.val = x j := by
    simp only [xN, j.isLt, ↓reduceDIte]
  rw [e]
theorem gap_affine {ι : Type*} [DecidableEq ι] {R : Type*} [CommRing R] (k : ℕ) (s : Finset ι)
    (E F : ι → R[X]) :
    ∃ Rem : R[X], ∏ j ∈ s, (E j + X ^ (k+1) * F j) =
      (∏ j ∈ s, E j) + X ^ (k+1) * (∑ j ∈ s, F j * ∏ j' ∈ s.erase j, E j') +
        X ^ (2*k+2) * Rem := by
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨0, by simp only [Finset.prod_empty, Finset.sum_empty, mul_zero, add_zero]⟩
  | insert a s ha ih =>
    obtain ⟨Rem, hR⟩ := ih
    refine ⟨E a * Rem + F a * (∑ j ∈ s, F j * ∏ j' ∈ s.erase j, E j') +
      X ^ (k+1) * F a * Rem, ?_⟩
    have h2 : ∀ j ∈ s, F j * ∏ j' ∈ (insert a s).erase j, E j' =
        E a * (F j * ∏ j' ∈ s.erase j, E j') := by
      intro j hj
      have hne : a ≠ j := fun h => ha (h ▸ hj)
      rw [Finset.erase_insert_of_ne hne,
        Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
      ring
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha, hR,
      Finset.erase_insert ha, Finset.sum_congr rfl h2, ← Finset.mul_sum]
    ring
theorem Al_cc (a b : ℚ) : (C (C a) : R2) * C (C b) = C (C (a * b)) := by
  simp only [C_mul]
theorem Al_hh : (2 : R2) * C (C (1/2 : ℚ)) = 1 := by
  rw [two_mul, ← C_add, ← C_add]
  norm_num
theorem Al_h4 : (C (C (1/4 : ℚ)) : R2) = C (C (1/2 : ℚ)) * C (C (1/2 : ℚ)) := by
  rw [Al_cc]
  norm_num
theorem Al_hm2 : (C (C (-1/2 : ℚ)) : R2) = - C (C (1/2 : ℚ)) := by
  rw [← C_neg, ← C_neg]
  norm_num
theorem Al_hm16 : (C (C (-1/16 : ℚ)) : R2) =
    -(C (C (1/2 : ℚ)) * C (C (1/2 : ℚ)) * C (C (1/2 : ℚ)) * C (C (1/2 : ℚ))) := by
  rw [Al_cc, Al_cc, Al_cc, ← C_neg, ← C_neg]
  norm_num
theorem Al_hd : (1 - redW) * (1 + bluW) - (1 + redW) * (1 - bluW) = -2 * ((C X : R2) * X) := by
  simp only [redW, bluW]
  ring
theorem Al_p1F (j : ℕ) (b : Bool) :
    gad false j b = gE false j + C (C (gc false b)) * X ^ (kk false + 1) * gF false j := by
  have hh := Al_hh
  have hd := Al_hd
  cases b
  · simp only [gad, gadF, gE, gF, gc, kk, segT, APp, AMm, Al_h4, Al_hm2, Bool.false_eq_true,
      Bool.not_false, ↓reduceIte, map_one]
    generalize C (C (1/2 : ℚ)) = h at hh ⊢
    generalize (1 + redW : R2) = A at hd ⊢
    generalize (1 - redW : R2) = A' at hd ⊢
    generalize (1 + bluW : R2) = P at hd ⊢
    generalize (1 - bluW : R2) = M at hd ⊢
    linear_combination ((A*A'*P*M)^j * (h * (A*P - A'*M)) * h^2) * hd -
      ((A*A'*P*M)^j * (h * (A*P - A'*M)) * h * (C X : R2) * (X : R2)) * hh
  · simp only [gad, gadF, gE, gF, gc, kk, segT, APp, AMm, Al_h4, Al_hm2, Bool.false_eq_true,
      Bool.not_true, ↓reduceIte, map_one, map_neg]
    generalize C (C (1/2 : ℚ)) = h at hh ⊢
    generalize (1 + redW : R2) = A at hd ⊢
    generalize (1 - redW : R2) = A' at hd ⊢
    generalize (1 + bluW : R2) = P at hd ⊢
    generalize (1 - bluW : R2) = M at hd ⊢
    linear_combination (-(A*A'*P*M)^j * (h * (A*P - A'*M)) * h^2) * hd +
      ((A*A'*P*M)^j * (h * (A*P - A'*M)) * h * (C X : R2) * (X : R2)) * hh
theorem Al_p1T (j : ℕ) (b : Bool) :
    gad true j b = gE true j + C (C (gc true b)) * X ^ (kk true + 1) * gF true j := by
  have hh := Al_hh
  have hd := Al_hd
  cases b
  · simp only [gad, gadT, gE, gF, gc, kk, segT, APp, AMm, Al_hm16, Bool.false_eq_true,
      ↓reduceIte, map_one]
    generalize C (C (1/2 : ℚ)) = h at hh ⊢
    generalize (1 + redW : R2) = A at hd ⊢
    generalize (1 - redW : R2) = A' at hd ⊢
    generalize (1 + bluW : R2) = P at hd ⊢
    generalize (1 - bluW : R2) = M at hd ⊢
    linear_combination (-(A*A'*P*M)^(2*j) * ((A*P)^2 - (A'*M)^2)^2 * h^6 *
        (A'*P - A*M - 2*((C X : R2)*(X : R2)))) * hd +
      (-(A*A'*P*M)^(2*j) * ((A*P)^2 - (A'*M)^2)^2 * h^4 * (2*h+1) * (C X : R2)^2 * (X : R2)^2) * hh
  · simp [gad, gE, gc]
theorem Al_c_red : Polynomial.constantCoeff redW = (X : ℚ[X]) := by
  simp [constantCoeff_apply, redW]
theorem Al_c_blu : Polynomial.constantCoeff bluW = (X : ℚ[X]) := by
  simp [constantCoeff_apply, bluW]
theorem Al_c_CC (q : ℚ) : Polynomial.constantCoeff (C (C q) : R2) = C q := by
  simp [constantCoeff_apply]
theorem Al_c_CX : Polynomial.constantCoeff (C X : R2) = X := by
  simp [constantCoeff_apply]
theorem Al_p2F (j : ℕ) :
    ∃ K : ℚ[X], (gF false j).coeff 0 = (X - C 1) ^ (dd false * j) * K ∧ K.eval 1 ≠ 0 := by
  refine ⟨C (-1/2 : ℚ) * X * ((1 + X) * (1 + X)) ^ j * (C (1/2 : ℚ) * ((1 + X) ^ 1 * (1 + X) ^ 1 +
    (-1) * ((1 - X) ^ 1 * (1 - X) ^ 1))), ?_, ?_⟩
  · rw [← constantCoeff_apply]
    simp only [gF, dd, segT, APp, AMm, Bool.false_eq_true, ↓reduceIte, map_mul, map_add, map_sub,
      map_pow, map_one, map_neg, Al_c_red, Al_c_blu, Al_c_CC, Al_c_CX]
    have e : ((1 : ℚ[X]) - X) * (1 - X) = (X - 1) * (X - 1) := by ring
    rw [e]
    generalize (X - 1 : ℚ[X]) = y
    generalize (1 + X : ℚ[X]) = a
    ring
  · simp only [eval_mul, eval_add, eval_sub, eval_pow, eval_one, eval_neg, eval_C, eval_X]
    norm_num
theorem Al_p2T (j : ℕ) :
    ∃ K : ℚ[X], (gF true j).coeff 0 = (X - C 1) ^ (dd true * j) * K ∧ K.eval 1 ≠ 0 := by
  refine ⟨C (-1/16 : ℚ) * X ^ 2 * ((1 + X) * (1 + X)) ^ (2 * j) *
    (((1 + X) * (1 + X)) ^ 2 - ((1 - X) * (1 - X)) ^ 2) ^ 2, ?_, ?_⟩
  · rw [← constantCoeff_apply]
    simp only [gF, dd, APp, AMm, ↓reduceIte, map_mul, map_add, map_sub,
      map_pow, map_one, Al_c_red, Al_c_blu, Al_c_CC, Al_c_CX]
    have e : ((1 : ℚ[X]) - X) * (1 - X) = (X - 1) * (X - 1) := by ring
    rw [e]
    generalize (X - 1 : ℚ[X]) = y
    generalize (1 + X : ℚ[X]) = a
    ring
  · simp only [eval_mul, eval_add, eval_sub, eval_pow, eval_one, eval_C, eval_X]
    norm_num
noncomputable def Al_ev : R2 →+* ℚ := (evalRingHom (1 : ℚ)).comp Polynomial.constantCoeff
theorem Al_ev_apply (p : R2) : Al_ev p = (p.coeff 0).eval 1 := rfl
theorem Al_ev_red : Al_ev redW = 1 := by
  simp [Al_ev_apply, redW]
theorem Al_ev_blu : Al_ev bluW = 1 := by
  simp [Al_ev_apply, bluW]
theorem Al_ev_CC (q : ℚ) : Al_ev (C (C q)) = q := by
  simp [Al_ev_apply]
theorem Al_ev_seg (a b : ℕ) (π : Bool) (ha : a ≠ 0) : Al_ev (segT a b π) ≠ 0 := by
  have h0 : (0 : ℚ) ^ a = 0 := zero_pow ha
  cases π <;> simp only [segT, map_mul, map_add, map_sub, map_pow, map_one, map_neg, Al_ev_red,
    Al_ev_blu, Al_ev_CC, sub_self, h0, Bool.false_eq_true, ↓reduceIte] <;> norm_num
theorem Al_p3 (mode : Bool) (j : ℕ) : ((gE mode j).coeff 0).eval 1 ≠ 0 := by
  rw [← Al_ev_apply]
  cases mode
  · simp only [gE, Bool.false_eq_true, ↓reduceIte, map_mul, map_sub, map_pow, APp, AMm, map_add,
      map_one, Al_ev_red, Al_ev_blu, Al_ev_CC]
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) (Al_ev_seg 1 1 true one_ne_zero)
    norm_num
  · simp only [gE, gadT, ↓reduceIte, map_mul]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_) ?_ <;>
      exact Al_ev_seg _ _ _ (by omega)
theorem Al_p4 (mode : Bool) (u t : ℕ) : ((extraF mode u t).coeff 0).eval 1 ≠ 0 := by
  rw [← Al_ev_apply]
  unfold extraF
  split_ifs with hlt
  · exact Al_ev_seg _ _ _ (by omega)
  · simp
theorem gap_alg (mode : Bool) (u t : ℕ) :
    (∀ (j : ℕ) (b : Bool),
      gad mode j b = gE mode j + C (C (gc mode b)) * X ^ (kk mode + 1) * gF mode j) ∧
    (∀ j : ℕ, ∃ K : ℚ[X], (gF mode j).coeff 0 = (X - C 1) ^ (dd mode * j) * K ∧ K.eval 1 ≠ 0) ∧
    (∀ j : ℕ, ((gE mode j).coeff 0).eval 1 ≠ 0) ∧
    ((extraF mode u t).coeff 0).eval 1 ≠ 0 := by
  refine ⟨?_, ?_, fun j => Al_p3 mode j, Al_p4 mode u t⟩
  · cases mode
    · exact Al_p1F
    · exact Al_p1T
  · cases mode
    · exact Al_p2F
    · exact Al_p2T
theorem Ln_indep (m d : ℕ) (hd : 1 ≤ d) (Z : Fin m → ℚ[X])
    (hZ : ∀ j : Fin m, ∃ K : ℚ[X], Z j = (X - C 1) ^ (d * j.val) * K ∧ K.eval 1 ≠ 0)
    (a : Fin m → ℚ) (ha : ∑ j : Fin m, C (a j) * Z j = 0) : a = 0 := by
  choose K hK hK1 using hZ
  have key : ∀ n : ℕ, ∀ j : Fin m, j.val = n → a j = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro j hj
      have hlow : ∀ j' : Fin m, j'.val < j.val → a j' = 0 :=
        fun j' h' => ih j'.val (hj ▸ h') j' rfl
      have hfac : (X - C 1) ^ (d * j.val) *
          (∑ j' : Fin m, C (a j') * (X - C 1) ^ (d * j'.val - d * j.val) * K j') =
          ∑ j' : Fin m, C (a j') * Z j' := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j' _ => ?_)
        by_cases h : j'.val < j.val
        · rw [hlow j' h]
          simp
        · have hle : d * j.val ≤ d * j'.val := Nat.mul_le_mul_left _ (by omega)
          rw [hK j', show (X - C 1 : ℚ[X]) ^ (d * j'.val) =
            (X - C 1) ^ (d * j.val) * (X - C 1) ^ (d * j'.val - d * j.val) by
              rw [← pow_add]
              congr 1
              omega]
          ring
      have hQ0 : (∑ j' : Fin m, C (a j') * (X - C 1) ^ (d * j'.val - d * j.val) * K j') = 0 := by
        have h1 : (X - C 1) ^ (d * j.val) *
            (∑ j' : Fin m, C (a j') * (X - C 1) ^ (d * j'.val - d * j.val) * K j') = 0 := by
          rw [hfac, ha]
        have h2 : (X - C (1:ℚ)) ^ (d * j.val) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero 1)
        exact (mul_eq_zero.mp h1).resolve_left h2
      have hev : (∑ j' : Fin m, C (a j') * (X - C 1) ^ (d * j'.val - d * j.val) * K j').eval 1 =
          a j * (K j).eval 1 := by
        rw [eval_finsetSum, Finset.sum_eq_single j]
        · simp
        · intro j' _ hne
          by_cases h : j'.val < j.val
          · rw [hlow j' h]
            simp
          · have hlt : j.val < j'.val := by
              rcases lt_or_eq_of_le (not_lt.mp h) with h' | h'
              · exact h'
              · exact absurd (Fin.ext h'.symm) hne
            have hle : d * (j.val + 1) ≤ d * j'.val := Nat.mul_le_mul_left _ hlt
            rw [mul_add, mul_one] at hle
            have hpos : d * j'.val - d * j.val ≠ 0 := by omega
            simp [eval_mul, eval_pow, hpos]
        · intro h
          exact absurd (Finset.mem_univ j) h
      have h3 : a j * (K j).eval 1 = 0 := by
        rw [← hev, hQ0]
        simp
      exact (mul_eq_zero.mp h3).resolve_right (hK1 j)
  funext j
  exact key j.val j rfl
theorem Ln_main (m N d : ℕ) (hd : 1 ≤ d) (vec : (Fin m → Bool) → ℚ[X]) (B : ℚ[X])
    (Z : Fin m → ℚ[X])
    (hvec : ∀ x, vec x = B + ∑ j : Fin m, (if x j then Z j else 0))
    (hdeg : ∀ x s, N < s → (vec x).coeff s = 0)
    (hZ : ∀ j : Fin m, ∃ K : ℚ[X], Z j = (X - C 1) ^ (d * j.val) * K ∧ K.eval 1 ≠ 0) :
    ∃ (base : Fin m → ℚ) (readout : Fin m → Fin (N+1) → ℚ),
      ∀ x i, base i + ∑ s : Fin (N+1), readout i s * (vec x).coeff s.val = ((x i).toNat : ℚ) := by
  have hZdeg : ∀ j : Fin m, ∀ s, N < s → (Z j).coeff s = 0 := by
    intro j s hs
    have h1 := hvec (fun k => decide (k = j))
    have h0 := hvec (fun _ => false)
    simp only [decide_eq_true_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Bool.false_eq_true, ite_false, Finset.sum_const_zero, add_zero] at h1 h0
    have e : Z j = vec (fun k => decide (k = j)) - vec (fun _ => false) := by
      rw [h1, h0]
      ring
    rw [e, coeff_sub, hdeg _ s hs, hdeg _ s hs, sub_zero]
  let W : (Fin m → ℚ) →ₗ[ℚ] (Fin (N+1) → ℚ) :=
    { toFun := fun a s => ∑ j : Fin m, a j * (Z j).coeff s.val
      map_add' := by
        intro a b
        funext s
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        funext s
        simp [Finset.mul_sum, mul_assoc] }
  have hW : LinearMap.ker W = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro a ha
    apply Ln_indep m d hd Z hZ a
    ext n
    rw [finsetSum_coeff, coeff_zero]
    by_cases hn : n ≤ N
    · have := congrFun ha ⟨n, Nat.lt_succ_of_le hn⟩
      simpa [W, coeff_C_mul] using this
    · replace hn : N < n := by omega
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [coeff_C_mul, hZdeg j n hn, mul_zero]
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective W hW
  have key : ∀ (x : Fin m → Bool) (i : Fin m),
      -L (fun s : Fin (N+1) => B.coeff s.val) i +
        ∑ s : Fin (N+1), L (fun s' => if s = s' then 1 else 0) i * (vec x).coeff s.val =
        ((x i).toNat : ℚ) := by
    intro x i
    have hv : (fun s : Fin (N+1) => (vec x).coeff s.val) =
        (fun s : Fin (N+1) => B.coeff s.val) + W (fun j => ((x j).toNat : ℚ)) := by
      funext s
      simp only [Pi.add_apply, W, LinearMap.coe_mk, AddHom.coe_mk]
      rw [hvec x, coeff_add, finsetSum_coeff]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      cases x j <;> simp
    have hLv : L (fun s : Fin (N+1) => (vec x).coeff s.val) i =
        ∑ s : Fin (N+1), L (fun s' => if s = s' then 1 else 0) i * (vec x).coeff s.val := by
      rw [LinearMap.pi_apply_eq_sum_univ L (fun s : Fin (N+1) => (vec x).coeff s.val)]
      simp [Finset.sum_apply, mul_comm]
    have hLW : L (W (fun j => ((x j).toNat : ℚ))) = (fun j => ((x j).toNat : ℚ)) := by
      have := congrArg (fun g => g (fun j => ((x j).toNat : ℚ))) hL
      simpa using this
    rw [← hLv, hv, map_add, Pi.add_apply, hLW]
    ring
  exact ⟨fun i => -L (fun s : Fin (N+1) => B.coeff s.val) i,
    fun i s => L (fun s' => if s = s' then 1 else 0) i, key⟩
theorem gap_lin (m N d : ℕ) (hd : 1 ≤ d) (vec : (Fin m → Bool) → ℚ[X]) (B : ℚ[X])
    (Y : Fin m → ℚ[X]) (γ : ℚ) (hγ : γ ≠ 0)
    (hvec : ∀ x, vec x = B + ∑ j : Fin m, (if x j then C γ * Y j else 0))
    (hdeg : ∀ x s, N < s → (vec x).coeff s = 0)
    (hY : ∀ j : Fin m, ∃ K : ℚ[X], Y j = (X - C 1) ^ (d * j.val) * K ∧ K.eval 1 ≠ 0) :
    ∃ (base : Fin m → ℚ) (readout : Fin m → Fin (N+1) → ℚ),
      ∀ x i, base i + ∑ s : Fin (N+1), readout i s * (vec x).coeff s.val = ((x i).toNat : ℚ) := by
  refine Ln_main m N d hd vec B (fun j => C γ * Y j) hvec hdeg ?_
  intro j
  obtain ⟨K, hK, hK1⟩ := hY j
  refine ⟨C γ * K, ?_, ?_⟩
  · rw [hK]
    ring
  · rw [eval_mul, eval_C]
    exact mul_ne_zero hγ hK1
theorem pinsOf_start (segs : List (ℕ × Bool)) (v : Bool) (Q : ℕ) :
    pinsOf segs v Q Q = some v := by
  cases segs with
  | nil => simp [pinsOf]
  | cons s rest => simp [pinsOf]
theorem pinsOf_end (segs : List (ℕ × Bool)) (hL : ∀ s ∈ segs, 1 ≤ s.1) (v : Bool) (Q : ℕ) :
    pinsOf segs v Q (Q + lenSum segs) = some (Bool.xor v (parSum segs)) := by
  induction segs generalizing v Q with
  | nil => simp [pinsOf, lenSum, parSum]
  | cons s rest ih =>
    have h1 : 1 ≤ s.1 := hL s (by simp)
    have hr : ∀ s' ∈ rest, 1 ≤ s'.1 := fun s' hs' => hL s' (by simp [hs'])
    have hne : Q + lenSum (s :: rest) ≠ Q := by
      simp only [lenSum]
      omega
    have e : Q + lenSum (s :: rest) = Q + s.1 + lenSum rest := by
      simp only [lenSum]
      ring
    simp only [pinsOf, hne, ite_false]
    rw [e, ih hr (Bool.xor v s.2) (Q + s.1)]
    simp [parSum]
theorem pinsOf_isSome_congr (s1 s2 : List (ℕ × Bool)) (h : s1.map Prod.fst = s2.map Prod.fst)
    (v1 v2 : Bool) (Q q : ℕ) :
    (pinsOf s1 v1 Q q).isSome = (pinsOf s2 v2 Q q).isSome := by
  induction s1 generalizing s2 v1 v2 Q with
  | nil =>
    cases s2 with
    | nil =>
      simp only [pinsOf]
      split_ifs <;> rfl
    | cons a l => simp at h
  | cons a l ih =>
    cases s2 with
    | nil => simp at h
    | cons b l2 =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨hab, hl⟩ := h
      simp only [pinsOf]
      split_ifs with hq
      · rfl
      · rw [hab]
        exact ih l2 hl _ _ _
theorem coeff_low (A S Rem E : R2) (k h : ℕ) (hh : h ≤ k) :
    ((A + X ^ (k+1) * S + X ^ (2*k+2) * Rem) * E).coeff h = (A * E).coeff h := by
  have e : (A + X ^ (k+1) * S + X ^ (2*k+2) * Rem) * E =
      A * E + X ^ (k+1) * (S * E) + X ^ (2*k+2) * (Rem * E) := by ring
  rw [e, coeff_add, coeff_add, coeff_X_pow_mul', coeff_X_pow_mul']
  have h1 : ¬ (k + 1 ≤ h) := by omega
  have h2 : ¬ (2*k+2 ≤ h) := by omega
  simp [h1, h2]
theorem coeff_mid (A S Rem E : R2) (k : ℕ) :
    ((A + X ^ (k+1) * S + X ^ (2*k+2) * Rem) * E).coeff (k+1) =
      (A * E).coeff (k+1) + (S * E).coeff 0 := by
  have e : (A + X ^ (k+1) * S + X ^ (2*k+2) * Rem) * E =
      A * E + X ^ (k+1) * (S * E) + X ^ (2*k+2) * (Rem * E) := by ring
  rw [e, coeff_add, coeff_add, coeff_X_pow_mul', coeff_X_pow_mul']
  have h2 : ¬ (2*k+2 ≤ k+1) := by omega
  simp [h2]
theorem profGF_enc (mode : Bool) (u t : ℕ) (x : Fin (u+1) → Bool) (hn : needOf mode u ≤ t+1) :
    profGF t (encD mode u t x) = (∏ j : Fin (u+1), gad mode j.val (x j)) * extraF mode u t := by
  obtain ⟨hL, hsum, hpar, -, -⟩ := gap_layout mode u t x hn
  have e2 : 2*(t+1) = 2*t+1+1 := by ring
  have h0 : pinsOf (segsFull mode u t x) false 0 0 = some false := pinsOf_start _ _ _
  have hend : pinsOf (segsFull mode u t x) false 0 (2*t+1+1) = some false := by
    have e := pinsOf_end (segsFull mode u t x) hL false 0
    rw [hpar, zero_add, hsum, e2] at e
    simpa using e
  have h1 : profGF t (encD mode u t x) = cycSum (2*t+1) (pinsOf (segsFull mode u t x) false 0) :=
    gap_ring1 t (pinsOf (segsFull mode u t x) false 0)
  have h2 := gap_ring2 (2*t+1) (pinsOf (segsFull mode u t x) false 0) h0 hend
  have h3 := gap_seg (segsFull mode u t x) hL false 0 false
  rw [hsum, hpar, e2] at h3
  rw [h1, h2, h3, gap_prod mode u t x]
  simp [eV]
theorem main_lemma (u t : ℕ) (mode : Bool) (hn : needOf mode u ≤ t+1) :
    ∃ (enc : (Fin (u+1) → Bool) → (Bool × Fin (t+1) → Option Bool)) (base : Fin (u+1) → ℚ)
      (readout : Fin (u+1) → Fin (2*(t+1)+1) → ℚ),
      (∀ x, (Finset.univ.filter (fun v => (enc x v).isSome)).card =
        (if mode then 6*(u+1) else 3*(u+1)) + (if needOf mode u < t+1 then 1 else 0)) ∧
      (mode = false → ∀ x y v, (enc x v).isSome = (enc y v).isSome) ∧
      (∀ x y, ∀ h, h ≤ kk mode → ∀ s,
        profileD t (histD t (enc x)) h s = profileD t (histD t (enc y)) h s) ∧
      ∀ x i, base i + (∑ s : Fin (2*(t+1)+1),
        readout i s * (profileD t (histD t (enc x)) (kk mode + 1) s : ℚ)) = ((x i).toNat : ℚ) := by
  obtain ⟨hgad, hevF, hevE, hevX⟩ := gap_alg mode u t
  have hexp : ∀ x : Fin (u+1) → Bool, ∃ Rem : R2, profGF t (encD mode u t x) =
      ((∏ j : Fin (u+1), gE mode j.val) +
        X ^ (kk mode + 1) * (∑ j : Fin (u+1), (C (C (gc mode (x j))) * gF mode j.val) *
          ∏ j' ∈ Finset.univ.erase j, gE mode j'.val) + X ^ (2 * kk mode + 2) * Rem) *
        extraF mode u t := by
    intro x
    obtain ⟨Rem, hR⟩ := gap_affine (kk mode) (Finset.univ : Finset (Fin (u+1)))
      (fun j => gE mode j.val) (fun j => C (C (gc mode (x j))) * gF mode j.val)
    refine ⟨Rem, ?_⟩
    rw [profGF_enc mode u t x hn, ← hR]
    congr 1
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [hgad]
    ring
  have hlow : ∀ x y : Fin (u+1) → Bool, ∀ h, h ≤ kk mode →
      (profGF t (encD mode u t x)).coeff h = (profGF t (encD mode u t y)).coeff h := by
    intro x y h hh
    obtain ⟨R1, e1⟩ := hexp x
    obtain ⟨R3, e3⟩ := hexp y
    rw [e1, e3, coeff_low _ _ _ _ _ _ hh, coeff_low _ _ _ _ _ _ hh]
  let Y : Fin (u+1) → ℚ[X] := fun j =>
    (gF mode j.val * (∏ j' ∈ Finset.univ.erase j, gE mode j'.val) * extraF mode u t).coeff 0
  let Bc : ℚ[X] := ((∏ j : Fin (u+1), gE mode j.val) * extraF mode u t).coeff (kk mode + 1)
  have hmid : ∀ x : Fin (u+1) → Bool, (profGF t (encD mode u t x)).coeff (kk mode + 1) =
      Bc + ∑ j : Fin (u+1), C (gc mode (x j)) * Y j := by
    intro x
    obtain ⟨R1, e1⟩ := hexp x
    rw [e1, coeff_mid]
    congr 1
    rw [Finset.sum_mul, finsetSum_coeff]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have e : C (C (gc mode (x j))) * gF mode j.val * (∏ j' ∈ Finset.univ.erase j, gE mode j'.val) *
        extraF mode u t = C (C (gc mode (x j))) *
          (gF mode j.val * (∏ j' ∈ Finset.univ.erase j, gE mode j'.val) * extraF mode u t) := by
      ring
    rw [e, coeff_C_mul]
  have hd : 1 ≤ dd mode := by cases mode <;> simp [dd]
  have hγ : gc mode true - gc mode false ≠ 0 := by cases mode <;> norm_num [gc]
  have hY : ∀ j : Fin (u+1), ∃ K : ℚ[X], Y j = (X - C 1) ^ (dd mode * j.val) * K ∧ K.eval 1 ≠ 0 := by
    intro j
    obtain ⟨K, hK, hK1⟩ := hevF j.val
    refine ⟨K * (∏ j' ∈ Finset.univ.erase j, (gE mode j'.val).coeff 0) * (extraF mode u t).coeff 0,
      ?_, ?_⟩
    · show (gF mode j.val * (∏ j' ∈ Finset.univ.erase j, gE mode j'.val) * extraF mode u t).coeff 0 = _
      rw [mul_coeff_zero, mul_coeff_zero, coeff_zero_prod, hK]
      ring
    · rw [eval_mul, eval_mul, eval_prod]
      refine mul_ne_zero (mul_ne_zero hK1 ?_) hevX
      exact Finset.prod_ne_zero_iff.mpr (fun j' _ => hevE j'.val)
  have hvec : ∀ x : Fin (u+1) → Bool, (profGF t (encD mode u t x)).coeff (kk mode + 1) =
      (Bc + ∑ j : Fin (u+1), C (gc mode false) * Y j) +
        ∑ j : Fin (u+1), (if x j then C (gc mode true - gc mode false) * Y j else 0) := by
    intro x
    rw [hmid x, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hx : x j = true
    · simp only [hx, ite_true, C_sub]
      ring
    · have hx' : x j = false := by simpa using hx
      simp only [hx', Bool.false_eq_true, ite_false]
      ring
  have hdeg : ∀ (x : Fin (u+1) → Bool) (s : ℕ), 2*(t+1) < s →
      ((profGF t (encD mode u t x)).coeff (kk mode + 1)).coeff s = 0 :=
    fun x s hs => (gap_bridge t (encD mode u t x)).2 _ s hs
  obtain ⟨base, readout, hread⟩ := gap_lin (u+1) (2*(t+1)) (dd mode) hd
    (fun x => (profGF t (encD mode u t x)).coeff (kk mode + 1))
    (Bc + ∑ j : Fin (u+1), C (gc mode false) * Y j) Y (gc mode true - gc mode false) hγ
    hvec hdeg hY
  refine ⟨encD mode u t, base, readout, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨hL, hsum, -, hlen, -⟩ := gap_layout mode u t x hn
    rw [← hlen]
    exact gap_count t _ hL hsum false
  · intro hm x y v
    obtain ⟨-, -, -, -, hmap⟩ := gap_layout mode u t x hn
    exact pinsOf_isSome_congr _ _ (hmap hm y) _ _ _ _
  · intro x y h hh s
    have e1 := (gap_bridge t (encD mode u t x)).1 h s
    have e3 := (gap_bridge t (encD mode u t y)).1 h s
    have hq : ((profileD t (histD t (encD mode u t x)) h s : ℕ) : ℚ) =
        ((profileD t (histD t (encD mode u t y)) h s : ℕ) : ℚ) := by
      rw [e1, e3, hlow x y h hh]
    exact_mod_cast hq
  · intro x i
    rw [← hread x i]
    congr 1
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [(gap_bridge t (encD mode u t x)).1]
end PEqualNP.Outside.L_pcx_400
theorem PEqualNP.Outside.L_pcx_400 : ∀ u t : ℕ,
  let n := t+1
  let m := u+1
  let I := Fin n
  let J := Fin (n+1)
  let V := Bool × I
  let P := V → Option Bool
  let S := Fin (2*n+1)
  let hist := fun (p : P) (r b : J) =>
    ((Finset.univ : Finset (V → Bool)).filter (fun x =>
      (∀ v, p v = none ∨ p v = some (x v)) ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,i))).card = r.val ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,i+1))).card = b.val)).card
  let profile := fun (H : J → J → ℕ) (h : ℕ) (s : S) =>
    ∑ r : J, ∑ b : J, if r.val+b.val = s.val then Nat.choose r.val h * H r b else 0
  ∀ mode : Bool,
    let k : ℕ := if mode then 1 else 0
    let need := if mode then 2*m*m+4*m else m*(m+1)
    need ≤ n →
    ∃ (enc : (Fin m → Bool) → P) (base : Fin m → ℚ) (readout : Fin m → S → ℚ),
      (∀ x, (Finset.univ.filter (fun v => (enc x v).isSome)).card =
        (if mode then 6*m else 3*m) + (if need < n then 1 else 0)) ∧
      (mode = false → ∀ x y v, (enc x v).isSome = (enc y v).isSome) ∧
      (∀ x y, ∀ h, h ≤ k → ∀ s, profile (hist (enc x)) h s = profile (hist (enc y)) h s) ∧
      ∀ x i, base i + (∑ s : S, readout i s * (profile (hist (enc x)) (k+1) s : ℚ)) =
        ((x i).toNat : ℚ) := by
  intro u t n m I J V P S hist profile mode k need hle
  exact PEqualNP.Outside.L_pcx_400.main_lemma u t mode hle
