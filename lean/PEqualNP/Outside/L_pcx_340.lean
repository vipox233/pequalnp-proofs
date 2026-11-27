import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_340
open scoped BigOperators

open scoped BigOperators

abbrev Cube (q : ℕ) := Fin q → Bool

def isDisj {q : ℕ} (a z : Cube q) : Prop := ∀ j, ¬ (a j = true ∧ z j = true)

instance {q : ℕ} (a z : Cube q) : Decidable (isDisj a z) := by
  unfold isDisj
  infer_instance

def leftBit {q : ℕ} (d u : Cube q) : Cube q := fun j => d j && u j

def rightBit {q : ℕ} (d u : Cube q) : Cube q := fun j => !d j && u j

def probe {q : ℕ} {T : Type} (τ : Cube q → Cube q → T)
    (d : Cube q) (i : Fin q) (a z : Bool) (u : Cube q) : T :=
  τ (Function.update (leftBit d u) i a) (Function.update (rightBit d u) i z)

def rect {q : ℕ} {T : Type} (τ : Cube q → Cube q → T) : Prop :=
  ∀ a z a' z', τ a z = τ a' z' → τ a z' = τ a z

noncomputable def mass {q : ℕ} {T : Type} (φ : Cube q → T) (t : T) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun u => φ u = t)).card : ℝ) / (2 : ℝ)^q

noncomputable def halfMass {q : ℕ} {T : Type} (φ : Cube q → T) (i : Fin q) (b : Bool) (t : T) : ℝ := by
  classical
  exact 2 * ((Finset.univ.filter (fun u => φ u = t ∧ u i = b)).card : ℝ) / (2 : ℝ)^q

noncomputable def ell {T : Type} [Fintype T] (P Q : T → ℝ) : ℝ :=
  ∑ t, (Real.sqrt (P t) - Real.sqrt (Q t))^2

open scoped BigOperators

noncomputable def selectSwap {q : ℕ} (i : Fin q) : Cube q ≃ Cube q where
  toFun d := Function.update d i (!d i)
  invFun d := Function.update d i (!d i)
  left_inv d := by
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [Function.update_of_ne h]
  right_inv d := by
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [Function.update_of_ne h]

theorem sumAvgBound {q e : ℕ} {S : Type} [Fintype S] (c : S → ℕ)
    (K : Cube q → Fin q → S → ℝ)
    (hpoint : ∀ d i, ((Fintype.card S : ℝ) - 2 * (e : ℝ))^2 ≤
      2 * (Fintype.card S : ℝ) * (∑ s, (K d i s + K (selectSwap i d) i s)))
    (henergy : ∀ d s, (∑ i, K d i s) ≤ 4 * (c s : ℝ)) :
    (q : ℝ) * ((Fintype.card S : ℝ) - 2 * (e : ℝ))^2 ≤
      16 * (Fintype.card S : ℝ) * (∑ s, (c s : ℝ)) := by
  let h : ℝ := Fintype.card S
  let δ : ℝ := (h - 2 * (e : ℝ))^2
  let N : ℝ := Fintype.card (Cube q)
  have hN : 0 < N := by
    have : Nonempty (Cube q) := ⟨fun _ => false⟩
    change 0 < (Fintype.card (Cube q) : ℝ)
    exact_mod_cast (Fintype.card_pos (α := Cube q))
  have hh : 0 ≤ h := by positivity
  have hsum (i : Fin q) : N * δ ≤ 4 * h * ∑ d, ∑ s, K d i s := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Cube q)))
      (fun d _ => hpoint d i)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum] at h
    have hswap : (∑ d, ∑ s, K (selectSwap i d) i s) = ∑ d, ∑ s, K d i s :=
      (selectSwap i).sum_comp (fun d => ∑ s, K d i s)
    rw [hswap] at h
    change N * δ ≤ _ at h
    change _ ≤ 4 * (Fintype.card S : ℝ) * _
    linarith only [h]
  have ha := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin q))) (fun i _ => hsum i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum] at ha
  have hb : (∑ i, ∑ d, ∑ s, K d i s) ≤ N * (4 * ∑ s, (c s : ℝ)) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ d, ∑ s, ∑ i, K d i s := by
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.sum_comm]
      _ ≤ ∑ _d : Cube q, (4 * ∑ s, (c s : ℝ)) := by
        apply Finset.sum_le_sum
        intro d _
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun s _ => henergy d s)
      _ = _ := by simp [N, nsmul_eq_mul]
  have H : (q : ℝ) * (N * δ) ≤ 4 * h * (N * (4 * ∑ s, (c s : ℝ))) :=
    ha.trans (mul_le_mul_of_nonneg_left hb (by positivity))
  apply le_of_mul_le_mul_left _ hN
  change N * ((q : ℝ) * δ) ≤ N * (16 * h * ∑ s, (c s : ℝ))
  nlinarith only [H]

theorem weightedMass {q : ℕ} {T : Type} [Fintype T] (f : Cube q → T) (w : T → ℝ) :
    (∑ t, w t * mass f t) = (∑ x, w (f x)) / (2 : ℝ)^q := by
  classical
  simp only [mass, ← mul_div_assoc, ← Finset.sum_div]
  congr 1
  conv_lhs =>
    arg 2
    intro t
    rw [← nsmul_eq_mul', ← Finset.sum_const]
  exact Finset.sum_fiberwise' Finset.univ f w

open scoped BigOperators

noncomputable def asRealBool (b : Bool) : ℝ := if b then 1 else 0

noncomputable def acceptance {T : Type} [Fintype T] (out : T → Bool) (P : T → ℝ) : ℝ :=
  ∑ t, asRealBool (out t) * P t

theorem acceptance_eq_event {T : Type} [Fintype T] (out : T → Bool) (P : T → ℝ) :
    acceptance out P = ∑ t ∈ Finset.univ.filter (fun t => out t = true), P t := by
  classical
  rw [Finset.sum_filter]
  unfold acceptance
  apply Finset.sum_congr rfl
  intro t _
  cases out t <;> simp [asRealBool]

theorem realVotes {S : Type} [Fintype S] (f : S → Bool) :
    (∑ s, asRealBool (f s)) = ((Finset.univ.filter (fun s => f s = true)).card : ℝ) := by
  classical
  calc
    _ = ∑ s ∈ Finset.univ.filter (fun s => f s = true), (1 : ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro s _
      cases f s <;> simp [asRealBool]
    _ = _ := by simp

theorem votesLo {S : Type} [Fintype S] (f : S → Bool) (e : ℕ)
    (h : (Finset.univ.filter (fun s => f s ≠ true)).card ≤ e) :
    (Fintype.card S : ℝ) - e ≤ ∑ s, asRealBool (f s) := by
  classical
  rw [realVotes]
  have hpart := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset S)) (fun s => f s = true)
  rw [Finset.card_univ] at hpart
  have hn : (Finset.univ.filter (fun s => f s = true)).card +
      (Finset.univ.filter (fun s => f s ≠ true)).card = Fintype.card S := hpart
  apply sub_le_iff_le_add.mpr
  exact_mod_cast (hn.symm.le.trans (Nat.add_le_add_left h _))

theorem votesHi {S : Type} [Fintype S] (f : S → Bool) (e : ℕ)
    (h : (Finset.univ.filter (fun s => f s ≠ false)).card ≤ e) :
    (∑ s, asRealBool (f s)) ≤ (e : ℝ) := by
  classical
  rw [realVotes]
  have heq : (Finset.univ.filter (fun s => f s = true)) = Finset.univ.filter (fun s => f s ≠ false) := by
    ext s; cases hh : f s <;> simp [hh]
  rw [heq]
  exact_mod_cast h

theorem plantedGood {q : ℕ} (d u : Cube q) (i : Fin q) :
    isDisj (Function.update (leftBit d u) i false) (Function.update (rightBit d u) i false) := by
  intro j
  by_cases hj : j = i
  · subst j; simp
  · cases hd : d j <;> simp [Function.update_of_ne hj, leftBit, rightBit, hd]

theorem plantedBad {q : ℕ} (d u : Cube q) (i : Fin q) :
    ¬ isDisj (Function.update (leftBit d u) i true) (Function.update (rightBit d u) i true) := by
  intro h
  exact h i (by simp)

theorem gap_all {q e : ℕ} {S : Type} [Fintype S] {T : S → Type} [∀ s, Fintype (T s)]
    (τ : ∀ s, Cube q → Cube q → T s) (out : ∀ s, T s → Bool)
    (herr : ∀ a z : Cube q, (Finset.univ.filter (fun s : S => out s (τ s a z) ≠ decide (isDisj a z))).card ≤ e)
    (d : Cube q) (i : Fin q) : (Fintype.card S : ℝ) - 2 * (e : ℝ) ≤
      ∑ s, (acceptance (out s) (mass (probe (τ s) d i false false)) -
        acceptance (out s) (mass (probe (τ s) d i true true))) := by
  classical
  let h : ℝ := Fintype.card S
  let N : ℝ := (2 : ℝ)^q
  let A : Bool → S → Cube q → ℝ := fun b s u => asRealBool (out s (probe (τ s) d i b b u))
  have hN : 0 < N := by positivity
  have hcard : (Fintype.card (Cube q) : ℝ) = N := by simp [Cube, N]
  have hlo (u : Cube q) : h - e ≤ ∑ s, A false s u := by
    apply votesLo
    simpa [probe, plantedGood d u i] using herr
      (Function.update (leftBit d u) i false) (Function.update (rightBit d u) i false)
  have hhi (u : Cube q) : (∑ s, A true s u) ≤ e := by
    apply votesHi
    simpa [probe, plantedBad d u i] using herr
      (Function.update (leftBit d u) i true) (Function.update (rightBit d u) i true)
  have hh (u : Cube q) : h - 2 * e ≤ ∑ s, (A false s u - A true s u) := by
    rw [Finset.sum_sub_distrib]
    linarith [hlo u, hhi u]
  unfold acceptance
  simp_rw [weightedMass]
  change h - 2 * e ≤ ∑ s, ((∑ u, A false s u) / N - (∑ u, A true s u) / N)
  simp_rw [← sub_div, ← Finset.sum_sub_distrib]
  rw [← Finset.sum_div, Finset.sum_comm, le_div_iff₀ hN]
  calc
    _ = ∑ _u : Cube q, (h - 2 * (e : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; ring
    _ ≤ _ := Finset.sum_le_sum (fun u _ => hh u)

theorem mass_nonneg {q : ℕ} {T : Type} (φ : Cube q → T) (t : T) :
    0 ≤ mass φ t := by
  unfold mass
  exact div_nonneg (Nat.cast_nonneg _) (by positivity)

theorem mass_sum {q : ℕ} {T : Type} [Fintype T] (φ : Cube q → T) :
    (∑ t, mass φ t) = 1 := by
  classical
  have hcount : (∑ t, (Finset.univ.filter (fun u : Cube q => φ u = t)).card) = 2 ^ q := by
    simpa [Cube, Fintype.card_fun] using
      Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Cube q))
        (Finset.univ : Finset T) φ
  unfold mass
  rw [← Finset.sum_div, ← Nat.cast_sum, hcount, Nat.cast_pow]
  exact div_self (by positivity : (2 : ℝ) ^ q ≠ 0)

theorem ell_event {T : Type} [Fintype T] (P Q : T → ℝ) (E : Finset T)
    (hP : ∀ t, 0 ≤ P t) (hQ : ∀ t, 0 ≤ Q t)
    (hPsum : (∑ t, P t) = 1) (hQsum : (∑ t, Q t) = 1) :
    ((∑ t ∈ E, P t) - (∑ t ∈ E, Q t)) ^ 2 ≤ ell P Q := by
  classical
  let a : T → ℝ := fun t => Real.sqrt (P t) - Real.sqrt (Q t)
  let b : T → ℝ := fun t =>
    if t ∈ E then Real.sqrt (P t) + Real.sqrt (Q t)
    else -(Real.sqrt (P t) + Real.sqrt (Q t))

  have hprod (t : T) :
      a t * b t = 2 * (if t ∈ E then P t - Q t else 0) - (P t - Q t) := by
    by_cases ht : t ∈ E <;> simp only [a, b, ht, if_true, if_false] <;>
      nlinarith only [Real.sq_sqrt (hP t), Real.sq_sqrt (hQ t)]
  have hsigned : (∑ t, a t * b t) = 2 * ((∑ t ∈ E, P t) - (∑ t ∈ E, Q t)) := by
    simp only [hprod, Finset.sum_sub_distrib, ← Finset.mul_sum, Fintype.sum_ite_mem,
      hPsum, hQsum, sub_self, sub_zero]
  have hb : (∑ t, b t ^ 2) ≤ 4 := by
    calc
      (∑ t, b t ^ 2) ≤ ∑ t, 2 * (P t + Q t) := by
        refine Finset.sum_le_sum fun t _ => ?_
        by_cases ht : t ∈ E <;> simp only [b, ht, if_true, if_false] <;>
          nlinarith only [Real.sq_sqrt (hP t), Real.sq_sqrt (hQ t),
            sq_nonneg (Real.sqrt (P t) - Real.sqrt (Q t))]
      _ = 4 := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, hPsum, hQsum] <;> norm_num
  have hell : 0 ≤ ell P Q := by
    unfold ell
    exact Finset.sum_nonneg fun t _ => sq_nonneg _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset T) a b
  rw [hsigned] at hcs
  change (2 * ((∑ t ∈ E, P t) - (∑ t ∈ E, Q t))) ^ 2 ≤
    ell P Q * (∑ t, b t ^ 2) at hcs
  have hbound := hcs.trans (mul_le_mul_of_nonneg_left hb hell)
  nlinarith only [hbound]

private theorem ell_of_normalized {T : Type} [Fintype T] (P Q : T → ℝ)
    (hP : ∀ t, 0 ≤ P t) (hQ : ∀ t, 0 ≤ Q t)
    (hPsum : (∑ t, P t) = 1) (hQsum : (∑ t, Q t) = 1) :
    ell P Q = 2 - 2 * (∑ t, Real.sqrt (P t) * Real.sqrt (Q t)) := by
  calc
    ell P Q = ∑ t, (P t + Q t - 2 * (Real.sqrt (P t) * Real.sqrt (Q t))) := by
      unfold ell
      refine Finset.sum_congr rfl fun t _ => ?_
      nlinarith only [Real.sq_sqrt (hP t), Real.sq_sqrt (hQ t)]
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hPsum, hQsum] <;>
        norm_num

theorem ell_paste {T : Type} [Fintype T] (P00 P01 P10 P11 : T → ℝ)
    (h00 : ∀ t, 0 ≤ P00 t) (h01 : ∀ t, 0 ≤ P01 t)
    (h10 : ∀ t, 0 ≤ P10 t) (h11 : ∀ t, 0 ≤ P11 t)
    (s00 : (∑ t, P00 t) = 1) (s01 : (∑ t, P01 t) = 1)
    (s10 : (∑ t, P10 t) = 1) (s11 : (∑ t, P11 t) = 1)
    (hpaste : ∀ t, P00 t * P11 t = P10 t * P01 t) :
    ell P00 P11 = ell P10 P01 := by
  have haff : (∑ t, Real.sqrt (P00 t) * Real.sqrt (P11 t)) =
      (∑ t, Real.sqrt (P10 t) * Real.sqrt (P01 t)) := by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Real.sqrt_mul (h00 t), ← Real.sqrt_mul (h10 t), hpaste t]
  rw [ell_of_normalized P00 P11 h00 h11 s00 s11,
    ell_of_normalized P10 P01 h10 h01 s10 s01, haff]

theorem ell_triangle_sq {T : Type} [Fintype T] (P Q R : T → ℝ) :
    ell P Q ≤ 2 * (ell P R + ell R Q) := by
  unfold ell
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  nlinarith only [sq_nonneg (Real.sqrt (P t) - 2 * Real.sqrt (R t) + Real.sqrt (Q t))]

theorem ell_symm {T : Type} [Fintype T] (P Q : T → ℝ) : ell P Q = ell Q P := by
  unfold ell
  exact Finset.sum_congr rfl fun t _ => by ring

private theorem cross_update_congr {q : ℕ} (i : Fin q) (b : Bool) (u v : Cube q)
    (h : ∀ j, j ≠ i → u j = v j) :
    Function.update u i b = Function.update v i b := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Function.update_self]
  · simpa only [Function.update_of_ne hj] using h j hj

private def crossMix {q : ℕ} (d : Cube q) (i : Fin q) (u v : Cube q) : Cube q :=
  fun j => if j ≠ i ∧ d j = true then v j else u j

private def crossSwap {q : ℕ} (d : Cube q) (i : Fin q)
    (p : Cube q × Cube q) : Cube q × Cube q :=
  (crossMix d i p.1 p.2, crossMix d i p.2 p.1)

private theorem crossSwap_involutive {q : ℕ} (d : Cube q) (i : Fin q) :
    Function.Involutive (crossSwap d i) := by
  intro p
  apply Prod.ext <;> funext j <;> by_cases h : j ≠ i ∧ d j = true <;>
    simp [crossSwap, crossMix, h]

private theorem probe_crossMix {q : ℕ} {T : Type} (τ : Cube q → Cube q → T)
    (d : Cube q) (i : Fin q) (a z : Bool) (u v : Cube q) :
    probe τ d i a z (crossMix d i u v) =
      τ (Function.update (leftBit d v) i a) (Function.update (rightBit d u) i z) := by
  have hl : Function.update (leftBit d (crossMix d i u v)) i a =
      Function.update (leftBit d v) i a := by
    apply cross_update_congr
    intro j hj
    cases h : d j <;> simp [leftBit, crossMix, hj, h]
  have hz : Function.update (rightBit d (crossMix d i u v)) i z =
      Function.update (rightBit d u) i z := by
    apply cross_update_congr
    intro j hj
    cases h : d j <;> simp [rightBit, crossMix, hj, h]
  unfold probe
  rw [hl, hz]

private theorem crossSwap_fiber {q : ℕ} {T : Type} (τ : Cube q → Cube q → T)
    (hr : rect τ) (d : Cube q) (i : Fin q) (t : T) (a z a' z' : Bool) (p : Cube q × Cube q)
    (h : probe τ d i a z p.1 = t ∧ probe τ d i a' z' p.2 = t) :
    probe τ d i a' z (crossSwap d i p).1 = t ∧
      probe τ d i a z' (crossSwap d i p).2 = t := by
  unfold rect at hr
  unfold probe at h
  have he := h.1.trans h.2.symm
  constructor
  · change probe τ d i a' z (crossMix d i p.1 p.2) = t
    rw [probe_crossMix]

    exact (hr _ _ _ _ he.symm).trans h.2
  · change probe τ d i a z' (crossMix d i p.2 p.1) = t
    rw [probe_crossMix]
    exact (hr _ _ _ _ he).trans h.1

theorem mass_paste {q : ℕ} {T : Type} (τ : Cube q → Cube q → T)
    (hr : rect τ) (d : Cube q) (i : Fin q) (t : T) :
    mass (probe τ d i false false) t * mass (probe τ d i true true) t =
      mass (probe τ d i true false) t * mass (probe τ d i false true) t := by
  classical
  let F (a z : Bool) : Finset (Cube q) := Finset.univ.filter (fun u => probe τ d i a z u = t)
  have mem_pair (a z a' z' : Bool) (p : Cube q × Cube q) :
      p ∈ F a z ×ˢ F a' z' ↔ probe τ d i a z p.1 = t ∧ probe τ d i a' z' p.2 = t := by
    simp [F]
  have hCard : (F false false ×ˢ F true true).card = (F true false ×ˢ F false true).card := by
    refine Finset.card_bij' (fun p _ => crossSwap d i p) (fun p _ => crossSwap d i p)
      ?_ ?_ ?_ ?_
    · intro p hp
      exact (mem_pair true false false true _).2
        (crossSwap_fiber τ hr d i t false false true true p ((mem_pair false false true true p).1 hp))
    · intro p hp
      exact (mem_pair false false true true _).2
        (crossSwap_fiber τ hr d i t true false false true p ((mem_pair true false false true p).1 hp))
    · intro p _
      exact crossSwap_involutive d i p
    · intro p _
      exact crossSwap_involutive d i p
  have hCount : (F false false).card * (F true true).card =
      (F true false).card * (F false true).card := by
    simpa only [Finset.card_product] using hCard
  have hReal : ((F false false).card : ℝ) * ((F true true).card : ℝ) =
      ((F true false).card : ℝ) * ((F false true).card : ℝ) := by
    exact_mod_cast hCount
  change (((F false false).card : ℝ) / (2 : ℝ)^q) * (((F true true).card : ℝ) / (2 : ℝ)^q) =
    (((F true false).card : ℝ) / (2 : ℝ)^q) * (((F false true).card : ℝ) / (2 : ℝ)^q)
  simp only [div_mul_div_comm, hReal]

private theorem probe_active_update {q : ℕ} {T : Type} (τ : Cube q → Cube q → T)
    (d : Cube q) (i : Fin q) (b : Bool) (u : Cube q) :
    τ (leftBit d (Function.update u i b)) (rightBit d (Function.update u i b)) =
      probe τ d i (d i && b) (!d i && b) u := by
  have hl : leftBit d (Function.update u i b) =
      Function.update (leftBit d u) i (d i && b) := by
    funext j
    exact Function.apply_update (fun (k : Fin q) (x : Bool) => d k && x) u i b j
  have hz : rightBit d (Function.update u i b) =
      Function.update (rightBit d u) i (!d i && b) := by
    funext j
    exact Function.apply_update (fun (k : Fin q) (x : Bool) => !d k && x) u i b j
  unfold probe
  rw [hl, hz]

theorem probe_active {q : ℕ} {T : Type} (τ : Cube q → Cube q → T)
    (d : Cube q) (i : Fin q) (b : Bool) (t : T) :
    mass (probe τ d i (d i && b) (!d i && b)) t =
      halfMass (fun u => τ (leftBit d u) (rightBit d u)) i b t := by
  classical
  let F : Finset (Cube q) :=
    Finset.univ.filter (fun u => probe τ d i (d i && b) (!d i && b) u = t)
  let H : Finset (Cube q) :=
    Finset.univ.filter (fun u => τ (leftBit d u) (rightBit d u) = t ∧ u i = b)
  have memF (u : Cube q) : u ∈ F ↔ probe τ d i (d i && b) (!d i && b) u = t := by
    simp [F]
  have memH (u : Cube q) : u ∈ H ↔ τ (leftBit d u) (rightBit d u) = t ∧ u i = b := by
    simp [H]

  have hCard : F.card = (H ×ˢ (Finset.univ : Finset Bool)).card := by
    refine Finset.card_bij' (fun u _ => (Function.update u i b, u i))
      (fun p _ => Function.update p.1 i p.2) ?_ ?_ ?_ ?_
    · intro u hu
      exact Finset.mem_product.2
        ⟨(memH _).2 ⟨(probe_active_update τ d i b u).trans ((memF u).1 hu),
          Function.update_self i b u⟩, Finset.mem_univ _⟩
    · intro p hp
      have hp' := (memH p.1).1 (Finset.mem_product.1 hp).1
      have hu : Function.update p.1 i b = p.1 := Function.update_eq_self_iff.mpr hp'.2.symm
      apply (memF _).2
      rw [← probe_active_update, Function.update_idem, hu]
      exact hp'.1
    · intro u _
      change Function.update (Function.update u i b) i (u i) = u
      rw [Function.update_idem]
      exact Function.update_eq_self_iff.mpr rfl
    · intro p hp
      have hi := ((memH p.1).1 (Finset.mem_product.1 hp).1).2
      have hu : Function.update p.1 i b = p.1 := Function.update_eq_self_iff.mpr hi.symm
      apply Prod.ext
      · change Function.update (Function.update p.1 i p.2) i b = p.1
        rw [Function.update_idem, hu]
      · exact Function.update_self i p.2 p.1
  have hCount : F.card = H.card * 2 := by
    simpa only [Finset.card_product, Finset.card_univ, Fintype.card_bool] using hCard
  have hReal : (F.card : ℝ) = (H.card : ℝ) * 2 := by
    exact_mod_cast hCount
  change (F.card : ℝ) / (2 : ℝ)^q = 2 * (H.card : ℝ) / (2 : ℝ)^q
  rw [hReal, mul_comm (H.card : ℝ) 2]

theorem probe_toggle_fun {q : ℕ} {T : Type} (τ : Cube q → Cube q → T)
    (d : Cube q) (i : Fin q) (a z : Bool) :
    probe τ (Function.update d i (!d i)) i a z = probe τ d i a z := by
  funext u
  have hl : Function.update (leftBit (Function.update d i (!d i)) u) i a =
      Function.update (leftBit d u) i a := by
    apply cross_update_congr
    intro j hj
    simp only [leftBit, Function.update_of_ne hj]
  have hz : Function.update (rightBit (Function.update d i (!d i)) u) i z =
      Function.update (rightBit d u) i z := by
    apply cross_update_congr
    intro j hj
    simp only [rightBit, Function.update_of_ne hj]
  unfold probe
  rw [hl, hz]

theorem probe_toggle {q : ℕ} {T : Type} (τ : Cube q → Cube q → T)
    (d : Cube q) (i : Fin q) (a z : Bool) (t : T) :
    mass (probe τ (Function.update d i (!d i)) i a z) t = mass (probe τ d i a z) t := by
  rw [probe_toggle_fun]

open scoped BigOperators

private noncomputable def energyFiber {q : ℕ} {T : Type} (φ : Cube q → T) (t : T) :
    Finset (Cube q) := by
  classical
  exact Finset.univ.filter (fun u => φ u = t)

private noncomputable def energySign (b : Bool) : ℝ := if b = true then 1 else -1

private noncomputable def energyBias {q : ℕ} {T : Type} (φ : Cube q → T) (t : T)
    (i : Fin q) : ℝ :=
  (∑ u ∈ energyFiber φ t, energySign (u i)) / ((energyFiber φ t).card : ℝ)

private theorem energy_card_mul_bias {q : ℕ} {T : Type} (φ : Cube q → T) (t : T)
    (i : Fin q) :
    ((energyFiber φ t).card : ℝ) * energyBias φ t i =
      ∑ u ∈ energyFiber φ t, energySign (u i) := by
  unfold energyBias
  by_cases h : (energyFiber φ t).card = 0
  · simp [Finset.card_eq_zero.mp h]
  · have hn : ((energyFiber φ t).card : ℝ) ≠ 0 := by exact_mod_cast h
    calc
      _ = ((∑ u ∈ energyFiber φ t, energySign (u i)) / ((energyFiber φ t).card : ℝ)) *
          ((energyFiber φ t).card : ℝ) := mul_comm _ _
      _ = _ := div_mul_cancel₀ _ hn

private theorem energy_sum_mass {q : ℕ} {T : Type} [Fintype T] (φ : Cube q → T) :
    (∑ t, mass φ t) = 1 := by
  classical
  have h : (∑ t, (energyFiber φ t).card) = 2 ^ q := by
    simpa [energyFiber, Cube, Fintype.card_fun] using
      (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Cube q))
        (Finset.univ : Finset T) φ)
  have hr : (∑ t, ((energyFiber φ t).card : ℝ)) = (2 : ℝ)^q := by exact_mod_cast h
  change (∑ t, ((energyFiber φ t).card : ℝ) / (2 : ℝ)^q) = 1
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, hr]
  exact mul_inv_cancel₀ (by positivity)

private theorem energy_mass_nonneg {q : ℕ} {T : Type} (φ : Cube q → T) (t : T) :
    0 ≤ mass φ t := by
  unfold mass
  positivity

private theorem energy_half_nonneg {q : ℕ} {T : Type} (φ : Cube q → T) (i : Fin q)
    (b : Bool) (t : T) : 0 ≤ halfMass φ i b t := by
  unfold halfMass
  positivity

private theorem energy_halves {q : ℕ} {T : Type} (φ : Cube q → T) (t : T)
    (i : Fin q) :
    halfMass φ i false t + halfMass φ i true t = 2 * mass φ t ∧
      halfMass φ i true t - halfMass φ i false t = 2 * mass φ t * energyBias φ t i := by
  classical
  let s := energyFiber φ t
  let p : Cube q → Prop := fun u => u i = true
  have hnot (u : Cube q) : (¬ p u) = (u i = false) := by
    apply propext
    cases h : u i <;> simp [p, h]
  have ht : halfMass φ i true t = 2 * ((s.filter p).card : ℝ) / (2 : ℝ)^q := by
    simp only [halfMass, s, energyFiber, p, Finset.filter_filter]
  have hf : halfMass φ i false t =
      2 * ((s.filter (fun u => ¬ p u)).card : ℝ) / (2 : ℝ)^q := by
    simp only [halfMass, s, energyFiber, Finset.filter_filter, hnot]
  have hcard : ((s.filter p).card : ℝ) + ((s.filter (fun u => ¬ p u)).card : ℝ) = s.card := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := s) p)
  have hsum : (∑ u ∈ s, energySign (u i)) =
      ((s.filter p).card : ℝ) - ((s.filter (fun u => ¬ p u)).card : ℝ) := by
    have h₁ : (∑ u ∈ s.filter p, energySign (u i)) = ((s.filter p).card : ℝ) := calc
      _ = ∑ _u ∈ s.filter p, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro u hu
        have hp : u i = true := (Finset.mem_filter.mp hu).2
        simp [energySign, hp]
      _ = _ := by simp
    have h₂ : (∑ u ∈ s.filter (fun u => ¬ p u), energySign (u i)) =
        -((s.filter (fun u => ¬ p u)).card : ℝ) := calc
      _ = ∑ _u ∈ s.filter (fun u => ¬ p u), -(1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro u hu
        have hp : ¬ (u i = true) := (Finset.mem_filter.mp hu).2
        simp [energySign, hp]
      _ = _ := by simp [Finset.sum_neg_distrib]
    rw [← Finset.sum_filter_add_sum_filter_not s p (fun u => energySign (u i)), h₁, h₂,
      sub_eq_add_neg]
  have hb : (s.card : ℝ) * energyBias φ t i = ∑ u ∈ s, energySign (u i) :=
    energy_card_mul_bias φ t i
  have hm : mass φ t = (s.card : ℝ) / (2 : ℝ)^q := rfl
  constructor
  · rw [hf, ht, hm, ← add_div, ← mul_add, add_comm, hcard] <;> ring
  · rw [ht, hf, hm, ← sub_div, ← mul_sub, ← hsum, ← hb] <;> ring

private theorem energy_sqrt_bound {a b m d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : a + b = 2 * m) (hd : b - a = 2 * m * d) :
    (Real.sqrt a - Real.sqrt b)^2 ≤ 2 * m * d^2 := by
  by_cases hm : m = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [hm, ha0, hb0]
  · have hm' : 0 < 2 * m := by
      have hp : 0 < m := lt_of_le_of_ne (by linarith) (Ne.symm hm)
      positivity
    apply le_of_mul_le_mul_left _ hm'
    calc
      2 * m * (Real.sqrt a - Real.sqrt b)^2 ≤
          (Real.sqrt a + Real.sqrt b)^2 * (Real.sqrt a - Real.sqrt b)^2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have h := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
        nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]
      _ = ((Real.sqrt b)^2 - (Real.sqrt a)^2)^2 := by ring
      _ = (b - a)^2 := by rw [Real.sq_sqrt hb, Real.sq_sqrt ha]
      _ = 2 * m * (2 * m * d^2) := by rw [hd]; ring

private theorem energy_cube_mgf {q : ℕ} (a : Fin q → ℝ) :
    (∑ u : Cube q, Real.exp (∑ i, a i * energySign (u i))) ≤
      (2 : ℝ)^q * Real.exp ((∑ i, (a i)^2) / 2) := by
  classical
  calc
    _ = ∑ u : Cube q, ∏ i, Real.exp (a i * energySign (u i)) := by
      simp_rw [Real.exp_sum]
    _ = ∏ i, ∑ b : Bool, Real.exp (a i * energySign b) :=
      (Fintype.prod_sum (fun i (b : Bool) => Real.exp (a i * energySign b))).symm
    _ = ∏ i, 2 * Real.cosh (a i) := by
      apply Finset.prod_congr rfl
      intro i _
      simp [Fintype.sum_bool, energySign, Real.cosh_eq] <;> ring
    _ = (2 : ℝ)^q * (∏ i, Real.cosh (a i)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ (2 : ℝ)^q * (∏ i, Real.exp ((a i)^2 / 2)) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod₀ (fun i _ => (Real.cosh_pos (a i)).le)
          (fun i _ => Real.cosh_le_exp_half_sq (a i))) (by positivity)
    _ = (2 : ℝ)^q * Real.exp ((∑ i, (a i)^2) / 2) := by
      have h : (∑ i, (a i)^2 / 2) = (∑ i, (a i)^2) / 2 := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
      rw [← Real.exp_sum, h]

private theorem energy_fiber_mgf {q : ℕ} {T : Type} (φ : Cube q → T) (t : T) :
    mass φ t * Real.exp ((∑ i, (energyBias φ t i)^2) / 2) ≤ 1 := by
  classical
  let s := energyFiber φ t
  let n : ℝ := s.card
  let a : Fin q → ℝ := energyBias φ t
  let g : Cube q → ℝ := fun u => ∑ i, a i * energySign (u i)
  let E : ℝ := ∑ i, (a i)^2
  have hmass : mass φ t = n / (2 : ℝ)^q := rfl
  change mass φ t * Real.exp (E / 2) ≤ 1
  by_cases he : s.card = 0
  · simp [hmass, n, he]
  have hn : 0 < n := by
    change (0 : ℝ) < (s.card : ℝ)
    exact_mod_cast (Nat.pos_of_ne_zero he)
  have hw : (∑ _u ∈ s, n⁻¹) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hn.ne'
  have hj : Real.exp (∑ u ∈ s, n⁻¹ * g u) ≤ ∑ u ∈ s, n⁻¹ * Real.exp (g u) := by
    simpa only [smul_eq_mul] using
      (convexOn_exp.map_sum_le (t := s) (w := fun _ => n⁻¹) (p := g)
        (fun _ _ => inv_nonneg.mpr hn.le) hw (fun _ _ => Set.mem_univ _))
  have hg : (∑ u ∈ s, n⁻¹ * g u) = E := by
    calc
      _ = ∑ i : Fin q, ∑ u ∈ s, n⁻¹ * (a i * energySign (u i)) := by
        simp only [g, Finset.mul_sum]
        exact Finset.sum_comm
      _ = ∑ i : Fin q, (a i)^2 := by
        apply Finset.sum_congr rfl
        intro i _
        have hi : n * a i = ∑ u ∈ s, energySign (u i) := energy_card_mul_bias φ t i
        calc
          _ = (n⁻¹ * a i) * (∑ u ∈ s, energySign (u i)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun u _ => (mul_assoc _ _ _).symm)
          _ = (n * n⁻¹) * (a i)^2 := by rw [← hi]; ring
          _ = (a i)^2 := by rw [mul_inv_cancel₀ hn.ne', one_mul]
  rw [hg, ← Finset.mul_sum] at hj
  have hbound : n * Real.exp E ≤ (2 : ℝ)^q * Real.exp (E / 2) := calc
    _ ≤ n * (n⁻¹ * (∑ u ∈ s, Real.exp (g u))) := mul_le_mul_of_nonneg_left hj hn.le
    _ = ∑ u ∈ s, Real.exp (g u) := by rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
    _ ≤ ∑ u : Cube q, Real.exp (g u) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun u _ _ => (Real.exp_pos (g u)).le)
    _ ≤ _ := energy_cube_mgf a
  have hsplit : Real.exp E = Real.exp (E / 2) * Real.exp (E / 2) := by
    have hE : E / 2 + E / 2 = E := by ring
    rw [← Real.exp_add, hE]
  rw [hsplit, ← mul_assoc] at hbound
  have hfinal : n * Real.exp (E / 2) ≤ (2 : ℝ)^q :=
    le_of_mul_le_mul_right hbound (Real.exp_pos _)
  rw [hmass, div_mul_eq_mul_div₀]
  exact (div_le_iff₀ (by positivity)).2 (by simpa only [one_mul] using hfinal)

theorem cube_energy {q c : ℕ} {T : Type} [Fintype T] (φ : Cube q → T)
    (hc : Fintype.card T ≤ 2^c) :
    (∑ i, ell (halfMass φ i false) (halfMass φ i true)) ≤ 4 * (c : ℝ) := by
  classical
  let E : T → ℝ := fun t => (∑ i, (energyBias φ t i)^2) / 2
  have hj : Real.exp (∑ t, mass φ t * E t) ≤ ∑ t, mass φ t * Real.exp (E t) := by
    simpa only [smul_eq_mul] using
      (convexOn_exp.map_sum_le (t := Finset.univ) (w := mass φ) (p := E)
        (fun t _ => energy_mass_nonneg φ t) (energy_sum_mass φ) (fun _ _ => Set.mem_univ _))
  have hcard : (∑ t, mass φ t * Real.exp (E t)) ≤ (Fintype.card T : ℝ) := calc
    _ ≤ ∑ _t : T, (1 : ℝ) := Finset.sum_le_sum (fun t _ => energy_fiber_mgf φ t)
    _ = _ := by simp
  have hc' : (Fintype.card T : ℝ) ≤ (2 : ℝ)^c := by exact_mod_cast hc
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hexp : (2 : ℝ)^c ≤ Real.exp (c : ℝ) := calc
    _ ≤ (Real.exp 1)^c := pow_le_pow_left₀ (by norm_num) htwo c
    _ = _ := by rw [← Real.exp_nat_mul, mul_one]
  have hE : (∑ t, mass φ t * E t) ≤ (c : ℝ) :=
    Real.exp_le_exp.mp (hj.trans (hcard.trans (hc'.trans hexp)))
  calc
    (∑ i, ell (halfMass φ i false) (halfMass φ i true)) =
        ∑ t, ∑ i, (Real.sqrt (halfMass φ i false t) - Real.sqrt (halfMass φ i true t))^2 := by
      unfold ell
      exact Finset.sum_comm
    _ ≤ ∑ t, ∑ i, 2 * mass φ t * (energyBias φ t i)^2 := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum
      intro i _
      obtain ⟨hs, hd⟩ := energy_halves φ t i
      exact energy_sqrt_bound (energy_half_nonneg φ i false t)
        (energy_half_nonneg φ i true t) hs hd
    _ = 4 * ∑ t, mass φ t * E t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [← Finset.mul_sum]
      dsimp only [E]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hE (by norm_num)

open scoped BigOperators

noncomputable def bitEnergy {q : ℕ} {T : Type} [Fintype T]
    (τ : Cube q → Cube q → T) (d : Cube q) (i : Fin q) : ℝ :=
  let φ := fun u => τ (leftBit d u) (rightBit d u)
  ell (halfMass φ i false) (halfMass φ i true)

theorem energyEdge {q : ℕ} {T : Type} [Fintype T]
    (τ : Cube q → Cube q → T) (d : Cube q) (i : Fin q) :
    bitEnergy τ d i + bitEnergy τ (selectSwap i d) i =
      ell (mass (probe τ d i true false)) (mass (probe τ d i false false)) +
      ell (mass (probe τ d i false false)) (mass (probe τ d i false true)) := by
  let d' := selectSwap i d
  have ht : d' i = !d i := by simp [d', selectSwap]
  have edge (D : Cube q) (b : Bool) :
      halfMass (fun u => τ (leftBit D u) (rightBit D u)) i b =
      mass (probe τ D i (D i && b) (!D i && b)) :=
    funext (fun t => (probe_active τ D i b t).symm)
  have toggled (a z : Bool) : probe τ d' i a z = probe τ d i a z :=
    probe_toggle_fun τ d i a z
  change bitEnergy τ d i + bitEnergy τ d' i = _
  simp only [bitEnergy, edge, toggled, ht]
  cases h : d i <;> simp [h] <;> rw [ell_symm (mass (probe τ d i true false)) (mass (probe τ d i false false))] <;> ac_rfl

theorem protocolBound {q e : ℕ} {S : Type} [Fintype S] {T : S → Type} [∀ s, Fintype (T s)]
    (c : S → ℕ) (τ : ∀ s, Cube q → Cube q → T s) (out : ∀ s, T s → Bool)
    (hcap : ∀ s, Fintype.card (T s) ≤ 2^(c s)) (hr : ∀ s, rect (τ s))
    (herr : ∀ a z : Cube q, (Finset.univ.filter (fun s : S => out s (τ s a z) ≠ decide (isDisj a z))).card ≤ e) :
    q*(Fintype.card S-2*e)^2 ≤ 16*Fintype.card S*(∑ s, c s) := by
  classical
  by_cases he : Fintype.card S ≤ 2*e
  · simp [Nat.sub_eq_zero_of_le he]
  have he' : 2*e ≤ Fintype.card S := by omega
  have hδ : 0 ≤ (Fintype.card S : ℝ) - 2 * (e : ℝ) := sub_nonneg.mpr (by exact_mod_cast he')
  have hh : (0 : ℝ) ≤ Fintype.card S := by positivity
  have hmain := sumAvgBound (e := e) c (fun d i s => bitEnergy (τ s) d i) (by
    intro d i
    let P (s : S) (a z : Bool) := mass (probe (τ s) d i a z)
    let gap (s : S) := acceptance (out s) (P s false false) - acceptance (out s) (P s true true)
    have hg : (Fintype.card S : ℝ) - 2 * (e : ℝ) ≤ ∑ s, gap s := gap_all τ out herr d i
    have hg0 : 0 ≤ ∑ s, gap s := hδ.trans hg
    have hsq := (sq_le_sq₀ hδ hg0).2 hg
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset S) (fun _ => (1:ℝ)) gap
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
    refine hsq.trans (hcs.trans ?_)
    have hsum : (∑ s, (gap s)^2) ≤ 2 * ∑ s, (bitEnergy (τ s) d i + bitEnergy (τ s) (selectSwap i d) i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro s _
      have hb : (gap s)^2 ≤ ell (P s false false) (P s true true) := by
        unfold gap
        rw [acceptance_eq_event, acceptance_eq_event]
        exact ell_event _ _ _ (mass_nonneg _) (mass_nonneg _) (mass_sum _) (mass_sum _)
      have hc : ell (P s false false) (P s true true) = ell (P s true false) (P s false true) :=
        ell_paste _ _ _ _ (mass_nonneg _) (mass_nonneg _) (mass_nonneg _) (mass_nonneg _)
          (mass_sum _) (mass_sum _) (mass_sum _) (mass_sum _) (mass_paste (τ s) (hr s) d i)
      rw [energyEdge]
      exact hb.trans (hc.le.trans (ell_triangle_sq (P s true false) (P s false true) (P s false false)))
    convert mul_le_mul_of_nonneg_left hsum hh using 1 <;> ring) (by
    intro d s
    exact cube_energy _ (hcap s))
  have hcast : ((Fintype.card S - 2*e : ℕ) : ℝ) = (Fintype.card S : ℝ) - 2*(e : ℝ) := by
    rw [Nat.cast_sub he']; norm_num
  exact_mod_cast (show (q : ℝ) * ((Fintype.card S - 2*e : ℕ) : ℝ)^2 ≤
      16*(Fintype.card S : ℝ)*(∑ s, (c s : ℝ)) by rwa [hcast])

abbrev BitVec (n : ℕ) := Fin n → Bool
abbrev WireStep (n : ℕ) (Q : Type) := Fin n × (Q → Bool → Q)
abbrev Segment (n : ℕ) (Q : Type) := Bool × List (WireStep n Q)

def segmentEval {n : ℕ} {Q : Type} (x : BitVec n) (segment : Segment n Q) (st : Q) : Q :=
  segment.2.foldl (fun s k => k.2 s (x k.1)) st

def segmentsEval {n : ℕ} {Q : Type} (x : BitVec n) (segments : List (Segment n Q)) (st : Q) : Q :=
  segments.foldl (fun s seg => segmentEval x seg s) st

def segmentStates {n : ℕ} {Q : Type} (x : BitVec n) (segments : List (Segment n Q)) (st : Q) : List Q :=
  segments.scanl (fun s seg => segmentEval x seg s) st

def mix {n : ℕ} (S : Finset (Fin n)) (x y : BitVec n) : BitVec n :=
  fun i => if i ∈ S then x i else y i

def good {n : ℕ} (S : Finset (Fin n)) (owner : Bool) (i : Fin n) : Prop :=
  if owner then i ∈ S else i ∉ S

theorem segmentCongr {n : ℕ} {Q : Type} (seg : Segment n Q) (x y : BitVec n)
    (h : ∀ k ∈ seg.2, x k.1 = y k.1) (s : Q) : segmentEval x seg s = segmentEval y seg s := by
  rcases seg with ⟨owner, ks⟩
  unfold segmentEval
  induction ks generalizing s with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.foldl_cons]
    rw [h k (by simp)]
    exact ih _ (fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem scanRectangle {n : ℕ} {Q : Type} (S E : Finset (Fin n))
    (segments : List (Segment n Q))
    (hc : ∀ seg ∈ segments, ∀ k ∈ seg.2, ¬ good S seg.1 k.1 → k.1 ∈ E)
    (x y u v : BitVec n) (st : Q)
    (hm : ∀ i ∈ E, mix S x y i = mix S u v i)
    (hs : segmentStates (mix S x y) segments st = segmentStates (mix S u v) segments st) :
    segmentStates (mix S x v) segments st = segmentStates (mix S x y) segments st := by
  induction segments generalizing st with
  | nil => rfl
  | cons seg segments ih =>
    let l := segmentEval (mix S x y) seg st
    let r := segmentEval (mix S u v) seg st
    let m := segmentEval (mix S x v) seg st
    have hf : segmentStates (mix S x y) (seg :: segments) st =
        st :: segmentStates (mix S x y) segments l := by simp [segmentStates, l]
    have hg : segmentStates (mix S u v) (seg :: segments) st =
        st :: segmentStates (mix S u v) segments r := by simp [segmentStates, r]
    have hf' : segmentStates (mix S x v) (seg :: segments) st =
        st :: segmentStates (mix S x v) segments m := by simp [segmentStates, m]
    rw [hf, hg, List.cons.injEq] at hs
    have hlr : l = r := by
      have eq := congrArg List.head? hs.2
      simpa [segmentStates] using eq
    have hm' : m = l := by
      cases h : seg.1
      · have hmR : m = r := by
          apply segmentCongr
          intro k hk
          by_cases hi : k.1 ∈ S
          · exact by simpa [mix, hi] using hm k.1 (hc seg (by simp) k hk (by simp [good, h, hi]))
          · simp [mix, hi]
        exact hmR.trans hlr.symm
      · apply segmentCongr
        intro k hk
        by_cases hi : k.1 ∈ S
        · simp [mix, hi]
        · exact by simpa [mix, hi] using (hm k.1 (hc seg (by simp) k hk (by simp [good, h, hi]))).symm
    rw [hf, hf', hm']
    congr 1
    exact ih (fun sg hsg j hj => hc sg (List.mem_cons_of_mem _ hsg) j hj) l (by
      simpa only [← hlr] using hs.2)

theorem editsRectangle {n : ℕ} (S E : Finset (Fin n)) (x y u v : BitVec n)
    (h : ∀ i ∈ E, mix S x y i = mix S u v i) :
    ∀ i ∈ E, mix S x v i = mix S x y i := by
  intro i hi
  by_cases hs : i ∈ S
  · simp [mix, hs]
  · simpa [mix, hs] using (h i hi).symm

abbrev Transcript {n : ℕ} (E : Finset (Fin n)) (m : ℕ) (Q : Type) :=
  (↥E → Bool) × (Fin m → Q)

def transcript {n : ℕ} {Q : Type} (E : Finset (Fin n))
    (segs : List (Segment n Q)) (st : Q) (x : BitVec n) : Transcript E segs.length Q :=
  (fun i => x i.val, fun j => (segmentStates x segs st).getD (j.val + 1) st)

theorem eqStates {n : ℕ} {Q : Type} (E : Finset (Fin n))
    (segs : List (Segment n Q)) (st : Q) {x y : BitVec n}
    (h : transcript E segs st x = transcript E segs st y) :
    segmentStates x segs st = segmentStates y segs st := by
  apply List.ext_getElem (by simp [segmentStates])
  intro j hx hy
  cases j with
  | zero => simp [segmentStates]
  | succ j =>
    have hj : j < segs.length := by simp [segmentStates] at hx; omega
    have e := congrFun (congrArg Prod.snd h) ⟨j, hj⟩
    change (segmentStates x segs st).getD (j + 1) st =
      (segmentStates y segs st).getD (j + 1) st at e
    rwa [List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hy] at e

theorem transcriptRectangle {n : ℕ} {Q : Type} (S E : Finset (Fin n))
    (segs : List (Segment n Q)) (st : Q)
    (hc : ∀ seg ∈ segs, ∀ k ∈ seg.2, ¬ good S seg.1 k.1 → k.1 ∈ E)
    {x y u v : BitVec n}
    (h : transcript E segs st (mix S x y) = transcript E segs st (mix S u v)) :
    transcript E segs st (mix S x v) = transcript E segs st (mix S x y) := by
  have hm : ∀ i ∈ E, mix S x y i = mix S u v i :=
    fun i hi => congrFun (congrArg Prod.fst h) ⟨i, hi⟩
  have he := editsRectangle S E x y u v hm
  have hs := scanRectangle S E segs hc x y u v st hm (eqStates E segs st h)
  apply Prod.ext
  · funext i; exact he i.val i.property
  · funext j
    exact congrArg (fun l : List Q => l.getD (j.val + 1) st) hs

theorem transcriptEval {n : ℕ} {Q : Type} (E : Finset (Fin n))
    (segs : List (Segment n Q)) (st : Q) {x y : BitVec n}
    (h : transcript E segs st x = transcript E segs st y) :
    segmentsEval x segs st = segmentsEval y segs st := by
  simpa [segmentStates, segmentsEval, List.getLast?_scanl] using
    congrArg List.getLast? (eqStates E segs st h)

theorem transcriptCard {n b : ℕ} (E : Finset (Fin n)) (m : ℕ) :
    Fintype.card (Transcript E m (Fin (2^b))) = 2^(E.card + m*b) := by
  simp [Transcript, pow_add, pow_mul]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm b m]

def mismatches {n p : ℕ} (S : Finset (Fin n)) (order : Fin p → (Fin n ≃ Fin n))
    (stop : Fin p → Fin (n+1)) (flip : Fin p → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun a => ∃ pass : Fin p,
    let target : Finset (Fin n) := if flip pass then Finset.univ \ S else S
    ¬ (a ∈ target ↔ ((order pass).symm a).val < (stop pass).val))

def splitPass {n : ℕ} {Q : Type} (order : Fin n ≃ Fin n)
    (step : Fin n → Q → Bool → Q) (stop : Fin (n+1)) (flip : Bool) : List (Segment n Q) :=
  let entry := fun k => (order k, step k)
  [(!flip, ((List.finRange n).take stop.val).map entry),
    (flip, ((List.finRange n).drop stop.val).map entry)]

theorem splitPassEval {n : ℕ} {Q : Type} (order : Fin n ≃ Fin n)
    (step : Fin n → Q → Bool → Q) (stop : Fin (n+1)) (flip : Bool)
    (x : BitVec n) (st : Q) : segmentsEval x (splitPass order step stop flip) st =
      (List.finRange n).foldl (fun s k => step k s (x (order k))) st := by
  simp only [segmentsEval, splitPass, List.foldl_cons, List.foldl_nil, segmentEval, List.foldl_map]
  rw [← List.foldl_append, List.take_append_drop]

theorem takeFin {n m : ℕ} {k : Fin n} (h : k ∈ (List.finRange n).take m) : k.val < m := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hj' := j.isLt
  simp only [List.length_take, List.length_finRange] at hj'
  have hval : j.val = k.val := by
    simpa [List.get_eq_getElem, List.getElem_take] using congrArg Fin.val hj
  omega

theorem dropFin {n m : ℕ} {k : Fin n} (h : k ∈ (List.finRange n).drop m) : m ≤ k.val := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hval : m + j.val = k.val := by
    simpa [List.get_eq_getElem, List.getElem_drop] using congrArg Fin.val hj
  omega

theorem splitPassCovers {n p : ℕ} {Q : Type} (S : Finset (Fin n))
    (order : Fin p → (Fin n ≃ Fin n)) (step : Fin p → Fin n → Q → Bool → Q)
    (stop : Fin p → Fin (n+1)) (flip : Fin p → Bool) (pass : Fin p)
    (seg : Segment n Q) (hg : seg ∈ splitPass (order pass) (step pass) (stop pass) (flip pass))
    (k : WireStep n Q) (hk : k ∈ seg.2) (hm : ¬ good S seg.1 k.1) :
    k.1 ∈ mismatches S order stop flip := by
  simp only [splitPass, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
    have he := takeFin hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, pass, ?_⟩
    cases hf : flip pass <;>
      simpa [good, hf, he, Finset.mem_sdiff] using hm
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
    have he : ¬ i.val < (stop pass).val := Nat.not_lt_of_ge (dropFin hi)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, pass, ?_⟩
    cases hf : flip pass <;>
      simpa [good, hf, he, Finset.mem_sdiff] using hm

theorem flattenEval {n A : ℕ} {Q : Type} (ps : List (Fin A))
    (order : Fin A → (Fin n ≃ Fin n)) (step : Fin A → Fin n → Q → Bool → Q)
    (stop : Fin A → Fin (n+1)) (flip : Fin A → Bool) (x : BitVec n) (st : Q) :
    segmentsEval x (ps.flatMap fun pass => splitPass (order pass) (step pass) (stop pass) (flip pass)) st =
      ps.foldl (fun s pass => (List.finRange n).foldl (fun z k => step pass k z (x (order pass k))) s) st := by
  induction ps generalizing st with
  | nil => rfl
  | cons pass ps ih =>
    simp only [List.flatMap_cons, List.foldl_cons]
    unfold segmentsEval
    rw [List.foldl_append]
    change segmentsEval x (ps.flatMap _) (segmentsEval x (splitPass _ _ _ _) st) = _
    rw [ih, splitPassEval]

theorem flattenLength {n A : ℕ} {Q : Type} (ps : List (Fin A))
    (order : Fin A → (Fin n ≃ Fin n)) (step : Fin A → Fin n → Q → Bool → Q)
    (stop : Fin A → Fin (n+1)) (flip : Fin A → Bool) :
    (ps.flatMap fun pass => splitPass (order pass) (step pass) (stop pass) (flip pass)).length = 2 * ps.length := by
  induction ps with
  | nil => simp
  | cons pass ps ih => simp [splitPass, Nat.mul_succ, Nat.add_comm]; omega

open scoped BigOperators

noncomputable def chooseOut {A T : Type} (f : A → T) (ans : A → Bool) (t : T) : Bool := by
  classical
  exact decide (∃ a, f a = t ∧ ans a = true)

theorem chooseOut_ok {A T : Type} (f : A → T) (ans : A → Bool)
    (h : ∀ a b, f a = f b → ans a = ans b) (a : A) :
    chooseOut f ans (f a) = ans a := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [chooseOut, decide_eq_true_eq]
  exact ⟨fun ⟨b, hb, hy⟩ => h a b hb.symm ▸ hy, fun he => ⟨a, rfl, he⟩⟩

theorem readerBound {n q R p b e : ℕ} (f : BitVec n → Bool) (S : Finset (Fin n))
    (left right : Cube q → BitVec n)
    (hf : ∀ a z, f (mix S (left a) (right z)) = true ↔ isDisj a z)
    (order : Fin R → Fin p → (Fin n ≃ Fin n)) (init : Fin R → Fin (2^b))
    (step : Fin R → Fin p → Fin n → Fin (2^b) → Bool → Fin (2^b))
    (out : Fin R → Fin (2^b) → Bool)
    (hbad : ∀ x : BitVec n, (Finset.univ.filter (fun seed : Fin R =>
      out seed ((List.finRange p).foldl (fun st pass => (List.finRange n).foldl
        (fun z k => step seed pass k z (x (order seed pass k))) st) (init seed)) ≠ f x)).card ≤ e)
    (G : Finset (Fin R)) (stop : Fin R → Fin p → Fin (n+1)) (flip : Fin R → Fin p → Bool) :
    q*(G.card-2*e)^2 ≤ 32*G.card*(G.card*(p*b+1) + ∑ s ∈ G, (mismatches S (order s) (stop s) (flip s)).card) := by
  classical
  let E (s : Fin R) := mismatches S (order s) (stop s) (flip s)
  let segs (s : Fin R) := (List.finRange p).flatMap
    (fun pass => splitPass (order s pass) (step s pass) (stop s pass) (flip s pass))
  let T (s : ↥G) := Transcript (E s.val) (segs s.val).length (Fin (2^b))
  let τ (s : ↥G) (a z : Cube q) : T s := transcript (E s.val) (segs s.val) (init s.val) (mix S (left a) (right z))
  let c (s : ↥G) := (E s.val).card + (2*p)*b
  let v (s : Fin R) (x : BitVec n) := out s (segmentsEval x (segs s) (init s))
  let ans (s : ↥G) : T s → Bool := chooseOut (fun u : Cube q × Cube q => τ s u.1 u.2)
    (fun u : Cube q × Cube q => v s.val (mix S (left u.1) (right u.2)))
  have hcover (s : Fin R) (seg : Segment n (Fin (2^b))) (hg : seg ∈ segs s)
      (k : WireStep n (Fin (2^b))) (hk : k ∈ seg.2) (hm : ¬ good S seg.1 k.1) : k.1 ∈ E s := by
    obtain ⟨pass, _, hp⟩ := List.mem_flatMap.mp hg
    exact splitPassCovers S (order s) (step s) (stop s) (flip s) pass seg hp k hk hm
  have hc (s : ↥G) : Fintype.card (T s) ≤ 2^(c s) := by
    dsimp only [T, c]
    rw [transcriptCard, flattenLength, List.length_finRange]
  have hr (s : ↥G) : rect (τ s) := by
    intro a z a' z' eq
    exact transcriptRectangle S (E s.val) (segs s.val) (init s.val) (hcover s.val)
      (x := left a) (u := left a') (y := right z) (v := right z') eq
  have hdec (a z : Cube q) : f (mix S (left a) (right z)) = decide (isDisj a z) := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    exact hf a z
  have hdecoded (s : ↥G) (a z : Cube q) : ans s (τ s a z) = v s.val (mix S (left a) (right z)) := by
    apply chooseOut_ok (a := (a,z))
    intro x y h
    unfold v
    congr 1
    exact transcriptEval (E s.val) (segs s.val) (init s.val) h
  have hv (s : Fin R) (x : BitVec n) : v s x = out s ((List.finRange p).foldl
      (fun st pass => (List.finRange n).foldl (fun z k => step s pass k z (x (order s pass k))) st) (init s)) := by
    unfold v segs
    rw [flattenEval]
  have herr (a z : Cube q) : (Finset.univ.filter (fun s : ↥G => ans s (τ s a z) ≠ decide (isDisj a z))).card ≤ e := by
    simp_rw [hdecoded, ← hdec a z]
    apply le_trans (Finset.card_le_card_of_injOn (fun s : ↥G => s.val) ?_ (fun _ _ _ _ h => Subtype.ext h))
      (hbad (mix S (left a) (right z)))
    intro s hs
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [← hv]
    exact (Finset.mem_filter.mp hs).2
  have bd := protocolBound c τ ans hc hr herr
  have hs' : (∑ s : ↥G, c s) = (∑ s ∈ G, (E s).card) + G.card*((2*p)*b) := by
    simp only [c, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    congr 1
    exact Finset.sum_attach G (fun s => (E s).card)
  rw [Fintype.card_coe, hs'] at bd
  refine bd.trans ?_
  change 16 * G.card * ((∑ s ∈ G, (E s).card) + G.card * (2*p*b)) ≤
    32 * G.card * (G.card * (p*b+1) + ∑ s ∈ G, (E s).card)
  nlinarith only [Nat.zero_le (G.card * (∑ s ∈ G, (E s).card)), Nat.zero_le (G.card*G.card)]

end PEqualNP.Outside.L_pcx_340

theorem PEqualNP.Outside.L_pcx_340 : (∃ C : ℕ, 0 < C ∧ ∀ (n q : ℕ) (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)),
  let V := Fin n
  let X := V → Bool
  let A := Fin q → Bool
  (∃ left right : A → X, ∀ a z : A,
    (f (fun i => if i ∈ S then left a i else right z i) = true ↔
      ∀ j : Fin q, ¬ (a j = true ∧ z j = true))) →
    ∀ (R p b e : ℕ), 0 < R → 0 < p →
      ∀ (order : Fin R → Fin p → (Fin n ≃ V)) (init : Fin R → Fin (2^b))
        (step : Fin R → Fin p → Fin n → Fin (2^b) → Bool → Fin (2^b))
        (out : Fin R → Fin (2^b) → Bool),
        let answer := fun (seed : Fin R) (x : X) => out seed
          ((List.finRange p).foldl (fun st pass => (List.finRange n).foldl
            (fun z k => step seed pass k z (x (order seed pass k))) st) (init seed))
        (∀ x : X, (Finset.univ.filter (fun seed : Fin R =>
          ¬ (answer seed x = f x))).card ≤ e) →
          ∀ (G : Finset (Fin R)) (stop : Fin R → Fin p → Fin (n+1))
            (flip : Fin R → Fin p → Bool),
            let edits := fun (seed : Fin R) =>
              (Finset.univ.filter (fun a : V => ∃ pass : Fin p,
                let target : Finset V := if flip seed pass then Finset.univ \ S else S
                ¬ (a ∈ target ↔ ((order seed pass).symm a).val < (stop seed pass).val))).card
            q*(G.card-2*e)^2 ≤ C*G.card*
              (G.card*(p*b+1) + ∑ seed ∈ G, edits seed)) := by
  refine ⟨32, by omega, ?_⟩
  intro n q f S
  dsimp only
  rintro ⟨left, right, henc⟩ R p b e _ _ order init step out hbad G stop flip
  exact L_pcx_340.readerBound f S left right henc order init step out hbad G stop flip
