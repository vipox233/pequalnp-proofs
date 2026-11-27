import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_575_aux

noncomputable def H {T : ℕ} (P : Fin T → ℝ) : ℝ := ∑ t, Real.negMulLog (P t)

lemma js_key (x m : ℝ) (hx : 0 ≤ x) (hm : 0 ≤ m) (hxm : x ≤ 2 * m) :
    2 * x - 2 * (Real.sqrt x * Real.sqrt m) ≤ x * Real.log x - x * Real.log m := by
  rcases hx.eq_or_lt with h0 | hpos
  · subst h0; simp
  · have hmpos : 0 < m := by linarith
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hpos
    have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
    have h1 := Real.log_le_sub_one_of_pos (div_pos hsm hsx)
    rw [Real.log_div hsm.ne' hsx.ne', Real.log_sqrt hm, Real.log_sqrt hx] at h1
    have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx
    have h2 : x * (Real.sqrt m / Real.sqrt x) = Real.sqrt x * Real.sqrt m := by
      calc x * (Real.sqrt m / Real.sqrt x)
          = (Real.sqrt x * Real.sqrt x) * (Real.sqrt m / Real.sqrt x) := by rw [hxx]
        _ = Real.sqrt x * Real.sqrt m := by field_simp
    have h3 := mul_le_mul_of_nonneg_left h1 hx
    have h4 : x * (Real.log m / 2 - Real.log x / 2) = (x * Real.log m - x * Real.log x) / 2 := by
      ring
    have h5 : x * (Real.sqrt m / Real.sqrt x - 1) = Real.sqrt x * Real.sqrt m - x := by
      rw [mul_sub, h2]; ring
    rw [h4, h5] at h3
    linarith

lemma js_term (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (1/4) * (Real.sqrt p - Real.sqrt q)^2 ≤
      Real.negMulLog ((p+q)/2) - (Real.negMulLog p + Real.negMulLog q)/2 := by
  obtain ⟨m, hm⟩ : ∃ m, m = (p+q)/2 := ⟨_, rfl⟩
  rw [← hm]
  have hm0 : 0 ≤ m := by rw [hm]; linarith
  have k1 := js_key p m hp hm0 (by rw [hm]; linarith)
  have k2 := js_key q m hq hm0 (by rw [hm]; linarith)
  have ea := Real.sq_sqrt hp
  have eb := Real.sq_sqrt hq
  have ec := Real.sq_sqrt hm0
  have hml : m * Real.log m = p/2 * Real.log m + q/2 * Real.log m := by
    have h : m * Real.log m = (p+q)/2 * Real.log m := congrArg (fun y => y * Real.log m) hm
    rw [h]; ring
  unfold Real.negMulLog
  nlinarith [sq_nonneg (Real.sqrt p + Real.sqrt q - 2 * Real.sqrt m)]

lemma H_le {T : ℕ} (hT : 0 < T) (P : Fin T → ℝ) (h0 : ∀ t, 0 ≤ P t) (h1 : ∑ t, P t = 1) :
    H P ≤ Real.log T := by
  have hTpos : (0:ℝ) < T := by exact_mod_cast hT
  have key : ∀ t, Real.negMulLog (P t) ≤ P t * Real.log T + (1/(T:ℝ) - P t) := by
    intro t
    rcases (h0 t).eq_or_lt with h | h
    · rw [← h]; simp
    · have h6 := Real.log_le_sub_one_of_pos (show 0 < 1/(P t * T) by positivity)
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one,
        Real.log_mul h.ne' hTpos.ne'] at h6
      have h2 := mul_le_mul_of_nonneg_left h6 h.le
      have h3 : P t * (1/(P t * T) - 1) = 1/T - P t := by field_simp
      rw [h3] at h2
      unfold Real.negMulLog; nlinarith
  calc H P ≤ ∑ t, (P t * Real.log T + (1/(T:ℝ) - P t)) :=
        Finset.sum_le_sum (fun t _ => key t)
    _ = Real.log T := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, h1, Finset.sum_sub_distrib, h1]
      simp [hTpos.ne']

lemma H_nonneg {T : ℕ} (P : Fin T → ℝ) (h0 : ∀ t, 0 ≤ P t) (h1 : ∑ t, P t = 1) :
    0 ≤ H P :=
  Finset.sum_nonneg (fun t _ => Real.negMulLog_nonneg (h0 t)
    (by rw [← h1]; exact Finset.single_le_sum (fun i _ => h0 i) (Finset.mem_univ t)))

lemma local_ineq {T : ℕ} (P00 P10 P01 P11 : Fin T → ℝ)
    (h00 : ∀ t, 0 ≤ P00 t) (h10 : ∀ t, 0 ≤ P10 t) (h01 : ∀ t, 0 ≤ P01 t) (h11 : ∀ t, 0 ≤ P11 t)
    (s00 : ∑ t, P00 t = 1) (s10 : ∑ t, P10 t = 1) (s01 : ∑ t, P01 t = 1) (s11 : ∑ t, P11 t = 1)
    (hprod : ∀ t, P10 t * P01 t = P00 t * P11 t) (acc : Fin T → Bool) (δ : ℝ) :
    (1/2) * (2 * δ * (∑ t, if acc t = true then P11 t - P00 t else 0) - δ^2) ≤
      ∑ t, ((Real.sqrt (P00 t) - Real.sqrt (P10 t))^2
        + (Real.sqrt (P00 t) - Real.sqrt (P01 t))^2) := by
  have e1 : ∑ t, (Real.sqrt (P10 t) - Real.sqrt (P01 t))^2
      = ∑ t, (Real.sqrt (P00 t) - Real.sqrt (P11 t))^2 := by
    have a1 : ∀ t, (Real.sqrt (P10 t) - Real.sqrt (P01 t))^2
        = P10 t + P01 t - 2 * (Real.sqrt (P00 t) * Real.sqrt (P11 t)) := by
      intro t
      have h := congrArg Real.sqrt (hprod t)
      rw [Real.sqrt_mul (h10 t), Real.sqrt_mul (h00 t)] at h
      linear_combination (Real.sq_sqrt (h10 t)) + (Real.sq_sqrt (h01 t)) - 2 * h
    have a2 : ∀ t, (Real.sqrt (P00 t) - Real.sqrt (P11 t))^2
        = P00 t + P11 t - 2 * (Real.sqrt (P00 t) * Real.sqrt (P11 t)) := by
      intro t
      linear_combination (Real.sq_sqrt (h00 t)) + (Real.sq_sqrt (h11 t))
    simp only [a1, a2, Finset.sum_sub_distrib, Finset.sum_add_distrib, s00, s10, s01, s11]
  have e2 : ∑ t, (1/2) * (Real.sqrt (P10 t) - Real.sqrt (P01 t))^2
      ≤ ∑ t, ((Real.sqrt (P00 t) - Real.sqrt (P10 t))^2
        + (Real.sqrt (P00 t) - Real.sqrt (P01 t))^2) :=
    Finset.sum_le_sum (fun t _ => by
      nlinarith [sq_nonneg (2 * Real.sqrt (P00 t) - Real.sqrt (P10 t) - Real.sqrt (P01 t))])
  have e3 : 2 * δ * (∑ t, if acc t = true then P11 t - P00 t else 0) - δ^2
      ≤ ∑ t, (Real.sqrt (P00 t) - Real.sqrt (P11 t))^2 := by
    have t1 : ∀ t, δ * ((if acc t = true then (2:ℝ) else 0) - 1) * (P11 t - P00 t)
        ≤ (Real.sqrt (P00 t) - Real.sqrt (P11 t))^2 + δ^2/2 * (P11 t + P00 t) := by
      intro t
      have ea := Real.sq_sqrt (h00 t)
      have eb := Real.sq_sqrt (h11 t)
      obtain ⟨x, hx⟩ : ∃ x, x = Real.sqrt (P00 t) := ⟨_, rfl⟩
      obtain ⟨y, hy⟩ : ∃ y, y = Real.sqrt (P11 t) := ⟨_, rfl⟩
      rw [← hx] at ea
      rw [← hy] at eb
      rw [← hx, ← hy, ← ea, ← eb]
      cases acc t
      · simp only [Bool.false_eq_true, ite_false]
        nlinarith [sq_nonneg ((x - y) - δ/2*(x+y)), sq_nonneg ((x-y) + δ/2*(x+y)),
          mul_nonneg (sq_nonneg δ) (sq_nonneg (x-y))]
      · simp only [ite_true]
        nlinarith [sq_nonneg ((x - y) - δ/2*(x+y)), sq_nonneg ((x-y) + δ/2*(x+y)),
          mul_nonneg (sq_nonneg δ) (sq_nonneg (x-y))]
    have t2 := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => t1 t)
    have t3 : ∑ t, δ * ((if acc t = true then (2:ℝ) else 0) - 1) * (P11 t - P00 t)
        = 2 * δ * (∑ t, if acc t = true then P11 t - P00 t else 0) := by
      have t5 : ∀ t, δ * ((if acc t = true then (2:ℝ) else 0) - 1) * (P11 t - P00 t)
          = 2 * δ * (if acc t = true then P11 t - P00 t else 0) - δ * (P11 t - P00 t) := by
        intro t; split_ifs <;> ring
      simp only [t5, Finset.sum_sub_distrib, ← Finset.mul_sum, s11, s00]; ring
    have t4 : ∑ t, ((Real.sqrt (P00 t) - Real.sqrt (P11 t))^2 + δ^2/2 * (P11 t + P00 t))
        = ∑ t, (Real.sqrt (P00 t) - Real.sqrt (P11 t))^2 + δ^2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, s11, s00]; ring
    linarith
  rw [← Finset.mul_sum] at e2
  linarith

lemma avgB {m : ℕ} (G : (Fin m → Bool) → ℝ) (k : Fin m) :
    ∑ w, G w = ∑ w, (G (Function.update w k false) + G (Function.update w k true)) / 2 := by
  have h1 : ∀ w : Fin m → Bool, G (Function.update w k false) + G (Function.update w k true)
      = G w + G (Function.update w k (!w k)) := by
    intro w
    cases h : w k
    · have e : Function.update w k false = w := by rw [← h]; exact Function.update_eq_self k w
      rw [e]; simp
    · have e : Function.update w k true = w := by rw [← h]; exact Function.update_eq_self k w
      rw [e]; simp [add_comm]
  have h2 : ∑ w : Fin m → Bool, G (Function.update w k (!w k)) = ∑ w, G w := by
    apply Fintype.sum_bijective (fun w : Fin m → Bool => Function.update w k (!w k))
    · apply Function.Involutive.bijective
      intro w
      simp
    · intro w; rfl
  simp only [h1]
  rw [← Finset.sum_div, Finset.sum_add_distrib, h2]; ring

lemma pw_insert {m : ℕ} (S : Finset (Fin m)) (k : Fin m) (hk : k ∉ S) (z w : Fin m → Bool)
    (c : Bool) :
    S.piecewise z (Function.update w k c) = (insert k S).piecewise (Function.update z k c) w := by
  funext i
  by_cases hi : i = k
  · rw [hi]; simp [Finset.piecewise, hk]
  · by_cases hS : i ∈ S <;> simp [Finset.piecewise, hS, hi]

noncomputable def Lg {m T : ℕ} (g : (Fin m → Bool) → Fin T) (S : Finset (Fin m))
    (z : Fin m → Bool) (t : Fin T) : ℝ :=
  (∑ w : Fin m → Bool, if g (S.piecewise z w) = t then (1:ℝ) else 0) / 2^m

lemma Lg_nonneg {m T : ℕ} (g : (Fin m → Bool) → Fin T) (S : Finset (Fin m))
    (z : Fin m → Bool) (t : Fin T) : 0 ≤ Lg g S z t := by
  unfold Lg
  apply div_nonneg
  · exact Finset.sum_nonneg (fun w _ => by split_ifs <;> norm_num)
  · positivity

lemma Lg_sum {m T : ℕ} (g : (Fin m → Bool) → Fin T) (S : Finset (Fin m))
    (z : Fin m → Bool) : ∑ t, Lg g S z t = 1 := by
  unfold Lg
  rw [← Finset.sum_div, Finset.sum_comm]
  simp

lemma Lg_split {m T : ℕ} (g : (Fin m → Bool) → Fin T) (S : Finset (Fin m)) (k : Fin m)
    (hk : k ∉ S) (z : Fin m → Bool) (t : Fin T) :
    Lg g S z t = (Lg g (insert k S) (Function.update z k false) t
      + Lg g (insert k S) (Function.update z k true) t) / 2 := by
  unfold Lg
  rw [avgB (fun w => if g (S.piecewise z w) = t then (1:ℝ) else 0) k]
  simp only [pw_insert S k hk]
  rw [← Finset.sum_div, Finset.sum_add_distrib]; ring

noncomputable def SqD {m T : ℕ} (g : (Fin m → Bool) → Fin T) (S' : Finset (Fin m))
    (k : Fin m) : ℝ :=
  ∑ z : Fin m → Bool, ∑ t, (Real.sqrt (Lg g S' (Function.update z k false) t)
    - Real.sqrt (Lg g S' (Function.update z k true) t))^2

lemma cube_step {m T : ℕ} (g : (Fin m → Bool) → Fin T) (S : Finset (Fin m)) (k : Fin m)
    (hk : k ∉ S) :
    (1/4) * SqD g (insert k S) k ≤ ∑ z, H (Lg g S z) - ∑ z, H (Lg g (insert k S) z) := by
  unfold SqD
  rw [avgB (fun z => H (Lg g (insert k S) z)) k, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  have ht : ∀ t, 1/4 * (Real.sqrt (Lg g (insert k S) (Function.update z k false) t)
      - Real.sqrt (Lg g (insert k S) (Function.update z k true) t))^2
      ≤ Real.negMulLog (Lg g S z t)
        - (Real.negMulLog (Lg g (insert k S) (Function.update z k false) t)
          + Real.negMulLog (Lg g (insert k S) (Function.update z k true) t)) / 2 := by
    intro t
    rw [Lg_split g S k hk z t]
    exact js_term _ _ (Lg_nonneg _ _ _ _) (Lg_nonneg _ _ _ _)
  have h := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => ht t)
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum] at h
  simp only [H]
  exact h

def X {m : ℕ} (d u : Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter (fun i => d i = true ∧ u i = true)

def Y {m : ℕ} (d u : Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter (fun i => d i = false ∧ u i = true)

def mix {m : ℕ} (d w w' : Fin m → Bool) : Fin m → Bool :=
  fun i => if d i = true then w i else w' i

lemma mem_X {m : ℕ} (d u : Fin m → Bool) (i : Fin m) :
    i ∈ X d u ↔ (d i = true ∧ u i = true) := by simp [X]

lemma mem_Y {m : ℕ} (d u : Fin m → Bool) (i : Fin m) :
    i ∈ Y d u ↔ (d i = false ∧ u i = true) := by simp [Y]

lemma XY_disj {m : ℕ} (d u : Fin m → Bool) : Disjoint (X d u) (Y d u) := by
  rw [Finset.disjoint_left]
  intro i h1 h2
  rw [mem_X] at h1
  rw [mem_Y] at h2
  simp_all

lemma pw_k {m : ℕ} (S : Finset (Fin m)) (k : Fin m) (z w : Fin m → Bool) (c : Bool) :
    (insert k S).piecewise (Function.update z k c) w k = c := by simp [Finset.piecewise]

lemma pw_ne {m : ℕ} {i k : Fin m} (hi : i ≠ k) (S : Finset (Fin m)) (z w : Fin m → Bool)
    (c : Bool) :
    (insert k S).piecewise (Function.update z k c) w i = S.piecewise z w i := by
  by_cases hS : i ∈ S <;> simp [Finset.piecewise, hS, hi]

def X0 {m : ℕ} (S : Finset (Fin m)) (k : Fin m) (d z w : Fin m → Bool) : Finset (Fin m) :=
  X (Function.update d k false) ((insert k S).piecewise (Function.update z k false) w)

def Y0 {m : ℕ} (S : Finset (Fin m)) (k : Fin m) (d z w : Fin m → Bool) : Finset (Fin m) :=
  Y (Function.update d k false) ((insert k S).piecewise (Function.update z k false) w)

lemma sX1 {m : ℕ} (S : Finset (Fin m)) (k : Fin m) (d z w : Fin m → Bool) :
    X (Function.update d k true) ((insert k S).piecewise (Function.update z k false) w)
      = X0 S k d z w := by
  unfold X0; ext i; rw [mem_X, mem_X]
  by_cases hi : i = k
  · rw [hi]; simp
  · simp [pw_ne hi, hi]

lemma sY1 {m : ℕ} (S : Finset (Fin m)) (k : Fin m) (d z w : Fin m → Bool) :
    Y (Function.update d k true) ((insert k S).piecewise (Function.update z k false) w)
      = Y0 S k d z w := by
  unfold Y0; ext i; rw [mem_Y, mem_Y]
  by_cases hi : i = k
  · rw [hi]; simp
  · simp [pw_ne hi, hi]

lemma sX2 {m : ℕ} (S : Finset (Fin m)) (k : Fin m) (d z w : Fin m → Bool) :
    X (Function.update d k true) ((insert k S).piecewise (Function.update z k true) w)
      = insert k (X0 S k d z w) := by
  unfold X0; ext i; rw [Finset.mem_insert, mem_X, mem_X]
  by_cases hi : i = k
  · rw [hi]; simp
  · simp [pw_ne hi, hi]

lemma sY2 {m : ℕ} (S : Finset (Fin m)) (k : Fin m) (d z w : Fin m → Bool) :
    Y (Function.update d k true) ((insert k S).piecewise (Function.update z k true) w)
      = Y0 S k d z w := by
  unfold Y0; ext i; rw [mem_Y, mem_Y]
  by_cases hi : i = k
  · rw [hi]; simp
  · simp [pw_ne hi, hi]

lemma sX3 {m : ℕ} (S : Finset (Fin m)) (k : Fin m) (d z w : Fin m → Bool) :
    X (Function.update d k false) ((insert k S).piecewise (Function.update z k true) w)
      = X0 S k d z w := by
  unfold X0; ext i; rw [mem_X, mem_X]
  by_cases hi : i = k
  · rw [hi]; simp
  · simp [pw_ne hi, hi]

lemma sY3 {m : ℕ} (S : Finset (Fin m)) (k : Fin m) (d z w : Fin m → Bool) :
    Y (Function.update d k false) ((insert k S).piecewise (Function.update z k true) w)
      = insert k (Y0 S k d z w) := by
  unfold Y0; ext i; rw [Finset.mem_insert, mem_Y, mem_Y]
  by_cases hi : i = k
  · rw [hi]; simp
  · simp [pw_ne hi, hi]

lemma X_mix {m : ℕ} (d z w w' : Fin m → Bool) (S' : Finset (Fin m)) :
    X d (S'.piecewise z (mix d w w')) = X d (S'.piecewise z w) := by
  ext i; rw [mem_X, mem_X]
  by_cases hd : d i = true
  · have e : S'.piecewise z (mix d w w') i = S'.piecewise z w i := by
      by_cases hS : i ∈ S' <;> simp [Finset.piecewise, hS, mix, hd]
    rw [e]
  · simp [hd]

lemma Y_mix {m : ℕ} (d z w w' : Fin m → Bool) (S' : Finset (Fin m)) :
    Y d (S'.piecewise z (mix d w w')) = Y d (S'.piecewise z w') := by
  ext i; rw [mem_Y, mem_Y]
  by_cases hd : d i = true
  · simp [hd]
  · have e : S'.piecewise z (mix d w w') i = S'.piecewise z w' i := by
      by_cases hS : i ∈ S' <;> simp [Finset.piecewise, hS, mix, hd]
    rw [e]

lemma ins_inter {m : ℕ} (S : Finset (Fin m)) (k : Fin m) (d z w : Fin m → Bool) :
    insert k (X0 S k d z w) ∩ insert k (Y0 S k d z w) = {k} := by
  have h : X0 S k d z w ∩ Y0 S k d z w = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp (XY_disj _ _)
  rw [← Finset.insert_inter_distrib, h]
  simp

noncomputable def Dist {m T : ℕ} (ℓ : Finset (Fin m) → Finset (Fin m) → Fin T)
    (A B : (Fin m → Bool) → Finset (Fin m)) (t : Fin T) : ℝ :=
  (∑ w : Fin m → Bool, if ℓ (A w) (B w) = t then (1:ℝ) else 0) / 2^m

lemma Dist_nonneg {m T : ℕ} (ℓ : Finset (Fin m) → Finset (Fin m) → Fin T)
    (A B : (Fin m → Bool) → Finset (Fin m)) (t : Fin T) : 0 ≤ Dist ℓ A B t := by
  unfold Dist
  apply div_nonneg
  · exact Finset.sum_nonneg (fun w _ => by split_ifs <;> norm_num)
  · positivity

lemma Dist_sum {m T : ℕ} (ℓ : Finset (Fin m) → Finset (Fin m) → Fin T)
    (A B : (Fin m → Bool) → Finset (Fin m)) : ∑ t, Dist ℓ A B t = 1 := by
  unfold Dist
  rw [← Finset.sum_div, Finset.sum_comm]
  simp

lemma Dist_acc {m T : ℕ} (ℓ : Finset (Fin m) → Finset (Fin m) → Fin T)
    (A B : (Fin m → Bool) → Finset (Fin m)) (acc : Fin T → Bool) :
    ∑ t, (if acc t = true then Dist ℓ A B t else 0)
      = (∑ w : Fin m → Bool, if acc (ℓ (A w) (B w)) = true then (1:ℝ) else 0) / 2^m := by
  unfold Dist
  have h : ∀ t, (if acc t = true then
      (∑ w : Fin m → Bool, if ℓ (A w) (B w) = t then (1:ℝ) else 0) / 2^m else 0)
      = (∑ w : Fin m → Bool, if ℓ (A w) (B w) = t then
          (if acc t = true then (1:ℝ) else 0) else 0) / 2^m := by
    intro t; cases acc t <;> simp
  simp only [h]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp

lemma Dist_prod {m T : ℕ} (ℓ : Finset (Fin m) → Finset (Fin m) → Fin T)
    (hrect : ∀ x y x' y', ℓ x y = ℓ x' y' → ℓ x y' = ℓ x y)
    (d : Fin m → Bool) (A0 B0 A1 B1 : (Fin m → Bool) → Finset (Fin m))
    (hA0 : ∀ w w', A0 (mix d w w') = A0 w) (hB0 : ∀ w w', B0 (mix d w w') = B0 w')
    (hA1 : ∀ w w', A1 (mix d w w') = A1 w) (hB1 : ∀ w w', B1 (mix d w w') = B1 w')
    (t : Fin T) :
    Dist ℓ A1 B0 t * Dist ℓ A0 B1 t = Dist ℓ A0 B0 t * Dist ℓ A1 B1 t := by
  unfold Dist
  rw [div_mul_div_comm, div_mul_div_comm]
  congr 1
  rw [Fintype.sum_mul_sum, Fintype.sum_mul_sum, ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  apply Fintype.sum_bijective
    (fun p : (Fin m → Bool) × (Fin m → Bool) => (mix d p.2 p.1, mix d p.1 p.2))
  · apply Function.Involutive.bijective
    rintro ⟨w, w'⟩
    apply Prod.ext <;> funext i <;> by_cases h : d i = true <;> simp [mix, h]
  · rintro ⟨w, w'⟩
    simp only [hA0, hB0, hA1, hB1]
    have hiff : (ℓ (A1 w) (B0 w) = t ∧ ℓ (A0 w') (B1 w') = t)
        ↔ (ℓ (A0 w') (B0 w) = t ∧ ℓ (A1 w) (B1 w') = t) := by
      constructor
      · rintro ⟨h1, h2⟩
        have e : ℓ (A1 w) (B0 w) = ℓ (A0 w') (B1 w') := h1.trans h2.symm
        exact ⟨(hrect _ _ _ _ e.symm).trans h2, (hrect _ _ _ _ e).trans h1⟩
      · rintro ⟨h1, h2⟩
        have e : ℓ (A0 w') (B0 w) = ℓ (A1 w) (B1 w') := h1.trans h2.symm
        exact ⟨(hrect _ _ _ _ e.symm).trans h2, (hrect _ _ _ _ e).trans h1⟩
    by_cases a1 : ℓ (A1 w) (B0 w) = t <;> by_cases a2 : ℓ (A0 w') (B1 w') = t <;>
      by_cases a3 : ℓ (A0 w') (B0 w) = t <;> by_cases a4 : ℓ (A1 w) (B1 w') = t <;>
      simp_all

noncomputable def Gap {m T : ℕ} (ℓ : Finset (Fin m) → Finset (Fin m) → Fin T)
    (acc : Fin T → Bool) (S : Finset (Fin m)) (k : Fin m) (d z : Fin m → Bool) : ℝ :=
  (∑ w : Fin m → Bool,
      if acc (ℓ (insert k (X0 S k d z w)) (insert k (Y0 S k d z w))) = true then (1:ℝ) else 0) / 2^m
    - (∑ w : Fin m → Bool,
      if acc (ℓ (X0 S k d z w) (Y0 S k d z w)) = true then (1:ℝ) else 0) / 2^m

lemma d_step {m T : ℕ} (ℓ : Finset (Fin m) → Finset (Fin m) → Fin T)
    (hrect : ∀ x y x' y', ℓ x y = ℓ x' y' → ℓ x y' = ℓ x y) (acc : Fin T → Bool)
    (S : Finset (Fin m)) (k : Fin m) (hk : k ∉ S) (δ : ℝ) :
    (1/16) * ∑ d : Fin m → Bool, ∑ z : Fin m → Bool, (2 * δ * Gap ℓ acc S k d z - δ^2)
    ≤ ∑ d : Fin m → Bool, (∑ z, H (Lg (fun u => ℓ (X d u) (Y d u)) S z)
        - ∑ z, H (Lg (fun u => ℓ (X d u) (Y d u)) (insert k S) z)) := by
  have hz : ∀ d z : Fin m → Bool,
      (1/2) * (2 * δ * Gap ℓ acc S k d z - δ^2)
      ≤ ∑ t, (Real.sqrt (Lg (fun u => ℓ (X (Function.update d k false) u)
                (Y (Function.update d k false) u)) (insert k S) (Function.update z k false) t)
            - Real.sqrt (Lg (fun u => ℓ (X (Function.update d k false) u)
                (Y (Function.update d k false) u)) (insert k S) (Function.update z k true) t))^2
        + ∑ t, (Real.sqrt (Lg (fun u => ℓ (X (Function.update d k true) u)
                (Y (Function.update d k true) u)) (insert k S) (Function.update z k false) t)
            - Real.sqrt (Lg (fun u => ℓ (X (Function.update d k true) u)
                (Y (Function.update d k true) u)) (insert k S) (Function.update z k true) t))^2 := by
    intro d z
    have f0 : Lg (fun u => ℓ (X (Function.update d k false) u)
        (Y (Function.update d k false) u)) (insert k S) (Function.update z k false)
        = Dist ℓ (fun w => X0 S k d z w) (fun w => Y0 S k d z w) := rfl
    have f1 : Lg (fun u => ℓ (X (Function.update d k true) u)
        (Y (Function.update d k true) u)) (insert k S) (Function.update z k false)
        = Dist ℓ (fun w => X0 S k d z w) (fun w => Y0 S k d z w) := by
      funext t; simp only [Lg, Dist, sX1, sY1]
    have f2 : Lg (fun u => ℓ (X (Function.update d k true) u)
        (Y (Function.update d k true) u)) (insert k S) (Function.update z k true)
        = Dist ℓ (fun w => insert k (X0 S k d z w)) (fun w => Y0 S k d z w) := by
      funext t; simp only [Lg, Dist, sX2, sY2]
    have f3 : Lg (fun u => ℓ (X (Function.update d k false) u)
        (Y (Function.update d k false) u)) (insert k S) (Function.update z k true)
        = Dist ℓ (fun w => X0 S k d z w) (fun w => insert k (Y0 S k d z w)) := by
      funext t; simp only [Lg, Dist, sX3, sY3]
    rw [f0, f1, f2, f3, ← Finset.sum_add_distrib]
    have key := local_ineq
      (Dist ℓ (fun w => X0 S k d z w) (fun w => Y0 S k d z w))
      (Dist ℓ (fun w => X0 S k d z w) (fun w => insert k (Y0 S k d z w)))
      (Dist ℓ (fun w => insert k (X0 S k d z w)) (fun w => Y0 S k d z w))
      (Dist ℓ (fun w => insert k (X0 S k d z w)) (fun w => insert k (Y0 S k d z w)))
      (Dist_nonneg _ _ _) (Dist_nonneg _ _ _) (Dist_nonneg _ _ _) (Dist_nonneg _ _ _)
      (Dist_sum _ _ _) (Dist_sum _ _ _) (Dist_sum _ _ _) (Dist_sum _ _ _)
      (fun t => by
        rw [mul_comm]
        exact Dist_prod ℓ hrect (Function.update d k false)
          (fun w => X0 S k d z w) (fun w => Y0 S k d z w)
          (fun w => insert k (X0 S k d z w)) (fun w => insert k (Y0 S k d z w))
          (fun w w' => X_mix _ _ _ _ _) (fun w w' => Y_mix _ _ _ _ _)
          (fun w w' => congrArg (insert k) (X_mix _ _ _ _ _))
          (fun w w' => congrArg (insert k) (Y_mix _ _ _ _ _)) t)
      acc δ
    have hg : (∑ t, if acc t = true then
          Dist ℓ (fun w => insert k (X0 S k d z w)) (fun w => insert k (Y0 S k d z w)) t
            - Dist ℓ (fun w => X0 S k d z w) (fun w => Y0 S k d z w) t else 0)
        = Gap ℓ acc S k d z := by
      have h : ∀ t, (if acc t = true then
          Dist ℓ (fun w => insert k (X0 S k d z w)) (fun w => insert k (Y0 S k d z w)) t
            - Dist ℓ (fun w => X0 S k d z w) (fun w => Y0 S k d z w) t else 0)
          = (if acc t = true then
              Dist ℓ (fun w => insert k (X0 S k d z w)) (fun w => insert k (Y0 S k d z w)) t
              else 0)
            - (if acc t = true then
              Dist ℓ (fun w => X0 S k d z w) (fun w => Y0 S k d z w) t else 0) := by
        intro t; split_ifs <;> simp
      simp only [h, Finset.sum_sub_distrib, Dist_acc]
      rfl
    rw [hg] at key
    exact key
  have h2 : ∑ d : Fin m → Bool, (1/4) * SqD (fun u => ℓ (X d u) (Y d u)) (insert k S) k
      ≤ ∑ d : Fin m → Bool, (∑ z, H (Lg (fun u => ℓ (X d u) (Y d u)) S z)
        - ∑ z, H (Lg (fun u => ℓ (X d u) (Y d u)) (insert k S) z)) :=
    Finset.sum_le_sum (fun d _ => cube_step _ S k hk)
  have h3 := avgB (fun d => (1/4) * SqD (fun u => ℓ (X d u) (Y d u)) (insert k S) k) k
  have h4 : (1/16) * ∑ d : Fin m → Bool, ∑ z : Fin m → Bool, (2 * δ * Gap ℓ acc S k d z - δ^2)
      ≤ ∑ d : Fin m → Bool,
        ((1/4) * SqD (fun u => ℓ (X (Function.update d k false) u)
            (Y (Function.update d k false) u)) (insert k S) k
          + (1/4) * SqD (fun u => ℓ (X (Function.update d k true) u)
            (Y (Function.update d k true) u)) (insert k S) k) / 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d _
    have h5 := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => hz d z)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h5
    unfold SqD
    linarith
  linarith

noncomputable def Psi {m T R : ℕ}
    (label : Fin R → Finset (Fin m) → Finset (Fin m) → Fin T) (S : Finset (Fin m)) : ℝ :=
  ∑ r : Fin R, ∑ d : Fin m → Bool, ∑ z : Fin m → Bool,
    H (Lg (fun u => label r (X d u) (Y d u)) S z)

lemma main {m T R Q a : ℕ} (hT : 0 < T) (hR : 0 < R) (hQ : 0 < Q) (b : Fin m → ℕ)
    (label : Fin R → Finset (Fin m) → Finset (Fin m) → Fin T) (out : Fin R → Fin T → Bool)
    (hrect : ∀ r x y x' y', label r x y = label r x' y' → label r x y' = label r x y)
    (hdis : ∀ x y : Finset (Fin m), Disjoint x y →
      (Q:ℝ) * (∑ r : Fin R, if out r (label r x y) = true then (1:ℝ) else 0) ≤ a * R)
    (hint : ∀ (i : Fin m) (x y : Finset (Fin m)), x ∩ y = {i} →
      (b i : ℝ) * R ≤ Q * ∑ r : Fin R, if out r (label r x y) = true then (1:ℝ) else 0) :
    2^(∑ i : Fin m, (b i - a)^2) ≤ T^(16*Q^2) := by
  have hQ' : (0:ℝ) < Q := by exact_mod_cast hQ
  have hR' : (0:ℝ) < R := by exact_mod_cast hR
  have hT' : (0:ℝ) < T := by exact_mod_cast hT
  have hN : (0:ℝ) < 2^m := by positivity
  have hcard : ((Fintype.card (Fin m → Bool) : ℕ) : ℝ) = 2^m := by simp
  have step : ∀ S : Finset (Fin m), ∀ k, k ∉ S →
      (1/16) * ((2:ℝ)^m * (2^m * ((R:ℝ) * (((b k - a : ℕ) : ℝ) / Q)^2)))
        ≤ Psi label S - Psi label (insert k S) := by
    intro S k hk
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ((b k - a : ℕ) : ℝ) / Q := ⟨_, rfl⟩
    rw [← hδ]
    have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
    have hA : ∀ d z : Fin m → Bool,
        (R:ℝ) * (((b k : ℝ) - a) / Q) ≤ ∑ r : Fin R, Gap (label r) (out r) S k d z := by
      intro d z
      unfold Gap
      rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]
      have h11 : (2:ℝ)^m * ((b k : ℝ) * R / Q) ≤ ∑ r : Fin R, ∑ w : Fin m → Bool,
          (if out r (label r (insert k (X0 S k d z w)) (insert k (Y0 S k d z w))) = true
            then (1:ℝ) else 0) := by
        rw [Finset.sum_comm]
        calc (2:ℝ)^m * ((b k : ℝ) * R / Q)
            = ∑ w : Fin m → Bool, ((b k : ℝ) * R / Q) := by
              simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
          _ ≤ _ := Finset.sum_le_sum (fun w _ => by
              rw [div_le_iff₀ hQ']
              have h := hint k _ _ (ins_inter S k d z w)
              linarith)
      have h00 : ∑ r : Fin R, ∑ w : Fin m → Bool,
          (if out r (label r (X0 S k d z w) (Y0 S k d z w)) = true then (1:ℝ) else 0)
          ≤ (2:ℝ)^m * ((a : ℝ) * R / Q) := by
        rw [Finset.sum_comm]
        calc _ ≤ ∑ w : Fin m → Bool, ((a : ℝ) * R / Q) := Finset.sum_le_sum (fun w _ => by
              rw [le_div_iff₀ hQ']
              have h := hdis (X0 S k d z w) (Y0 S k d z w) (XY_disj _ _)
              linarith)
          _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
      rw [← sub_div, le_div_iff₀ hN]
      have e : (R:ℝ) * (((b k : ℝ) - a) / Q) * 2^m
          = (2:ℝ)^m * ((b k : ℝ) * R / Q) - (2:ℝ)^m * ((a : ℝ) * R / Q) := by ring
      linarith
    have hG : ∀ d z : Fin m → Bool, (R:ℝ) * δ^2
        ≤ ∑ r : Fin R, (2 * δ * Gap (label r) (out r) S k d z - δ^2) := by
      intro d z
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      have h := hA d z
      rcases le_or_gt (b k) a with hba | hba
      · have e : δ = 0 := by rw [hδ, Nat.sub_eq_zero_of_le hba]; simp
        rw [e]; simp
      · have e : δ = ((b k : ℝ) - a) / Q := by rw [hδ, Nat.cast_sub hba.le]
        rw [← e] at h
        nlinarith [mul_le_mul_of_nonneg_left h hδ0]
    calc (1/16) * ((2:ℝ)^m * (2^m * ((R:ℝ) * δ^2)))
        = (1/16) * ∑ d : Fin m → Bool, ∑ z : Fin m → Bool, ((R:ℝ) * δ^2) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
      _ ≤ (1/16) * ∑ d : Fin m → Bool, ∑ z : Fin m → Bool, ∑ r : Fin R,
            (2 * δ * Gap (label r) (out r) S k d z - δ^2) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun z _ => hG d z))
      _ = ∑ r : Fin R, (1/16) * ∑ d : Fin m → Bool, ∑ z : Fin m → Bool,
            (2 * δ * Gap (label r) (out r) S k d z - δ^2) := by
          rw [← Finset.mul_sum]
          congr 1
          exact (Finset.sum_congr rfl (fun d _ => Finset.sum_comm)).trans Finset.sum_comm
      _ ≤ Psi label S - Psi label (insert k S) := by
          unfold Psi
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_le_sum (fun r _ => by
            rw [← Finset.sum_sub_distrib]
            exact d_step (label r) (hrect r) (out r) S k hk δ)
  have ind : ∀ S : Finset (Fin m),
      (1/16) * ((2:ℝ)^m * (2^m * ((R:ℝ) * ∑ k ∈ S, (((b k - a : ℕ) : ℝ) / Q)^2)))
        ≤ Psi label ∅ - Psi label S := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert k S hk ih =>
      rw [Finset.sum_insert hk]
      have h := step S k hk
      nlinarith
  have hU : Psi label ∅ ≤ (R:ℝ) * ((2:ℝ)^m * ((2:ℝ)^m * Real.log T)) := by
    unfold Psi
    calc _ ≤ ∑ r : Fin R, ∑ d : Fin m → Bool, ∑ z : Fin m → Bool, Real.log T :=
          Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun d _ =>
            Finset.sum_le_sum (fun z _ =>
              H_le hT _ (fun t => Lg_nonneg _ _ _ t) (Lg_sum _ _ _))))
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, Fintype.card_fin]
  have hL : 0 ≤ Psi label Finset.univ := by
    unfold Psi
    exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun d _ =>
      Finset.sum_nonneg (fun z _ =>
        H_nonneg _ (fun t => Lg_nonneg _ _ _ t) (Lg_sum _ _ _))))
  have h3 := ind Finset.univ
  have h4 : ∑ k : Fin m, (((b k - a : ℕ) : ℝ) / Q)^2 ≤ 16 * Real.log T := by
    have hc : 0 < (2:ℝ)^m * (2^m * (R:ℝ)) := by positivity
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [mul_lt_mul_of_pos_left hcon hc]
  have h5 : ((∑ i : Fin m, (b i - a)^2 : ℕ) : ℝ) ≤ 16 * (Q:ℝ)^2 * Real.log T := by
    push_cast
    have e : ∀ i : Fin m, (((b i - a : ℕ) : ℝ))^2
        = (Q:ℝ)^2 * (((b i - a : ℕ) : ℝ) / Q)^2 := by
      intro i; field_simp
    simp only [e]
    rw [← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left h4 (sq_nonneg (Q:ℝ))]
  have h6 : ((2:ℝ))^(∑ i : Fin m, (b i - a)^2) ≤ (T:ℝ)^(16*Q^2) := by
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    have hl0 : 0 ≤ Real.log T := Real.log_nonneg (by exact_mod_cast hT)
    have hS0 : (0:ℝ) ≤ ((∑ i : Fin m, (b i - a)^2 : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast at h5 hS0 ⊢
    nlinarith [Real.log_pos (show (1:ℝ) < 2 by norm_num)]
  exact_mod_cast h6

end PEqualNP.Outside.L_lib_575_aux

theorem PEqualNP.Outside.L_lib_575 : (∀ (m T R Q a : Nat), 0 < T → 0 < R → 0 < Q → a ≤ Q →
  ∀ (b : Fin m → Nat), (∀ i, b i ≤ Q) →
  let W := Finset (Fin m)
  ∀ (label : Fin R → W → W → Fin T) (out : Fin R → Fin T → Bool),
    (∀ r x y x' y', label r x y = label r x' y' → label r x y' = label r x y) →
    let ones := fun x y : W => ((List.finRange R).filter (fun r => out r (label r x y))).length
    (∀ x y : W, Disjoint x y → Q*ones x y ≤ a*R) →
    (∀ (i : Fin m) (x y : W), x ∩ y = {i} → b i*R ≤ Q*ones x y) →
    2^(∑ i : Fin m, (b i-a)^2) ≤ T^(16*Q^2)) := by
  intro m T R Q a hT hR hQ _ b _ W label out hrect ones hdis hint
  have hones : ∀ x y : Finset (Fin m), ((ones x y : ℕ) : ℝ)
      = ∑ r : Fin R, if out r (label r x y) = true then (1:ℝ) else 0 := by
    intro x y
    have e : ((List.finRange R).filter (fun r => out r (label r x y))).toFinset
        = Finset.univ.filter (fun r => out r (label r x y) = true) := by
      ext r; simp
    show ((((List.finRange R).filter (fun r => out r (label r x y))).length : ℕ) : ℝ) = _
    rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ (List.nodup_finRange R)), e,
      Finset.card_filter]
    push_cast
    rfl
  exact PEqualNP.Outside.L_lib_575_aux.main hT hR hQ b label out hrect
    (fun x y h => by rw [← hones x y]; exact_mod_cast hdis x y h)
    (fun i x y h => by rw [← hones x y]; exact_mod_cast hint i x y h)
