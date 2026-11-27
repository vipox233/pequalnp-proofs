import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25579

private abbrev Word (k : ℕ) := Fin k → ZMod 2

private def atPos {k : ℕ} (hk : 0 < k) (i : ℕ) : Fin k := ⟨i % k, Nat.mod_lt _ hk⟩

private def proj {k : ℕ} (hk : 0 < k) (p v : Word k) (i : Fin k) : ZMod 2 :=
  ∑ t : Fin k, p t * v (atPos hk (i.val + k - t.val))

private def mixOp {k : ℕ} (hk : 0 < k) (s : ℕ) (v : Word k) (i : Fin k) : ZMod 2 :=
  v i + v (atPos hk (i.val + s)) + v (atPos hk (i.val + k - s % k))

private def shiftW {k : ℕ} (hk : 0 < k) (r : ℕ) (v : Word k) (i : Fin k) : ZMod 2 :=
  v (atPos hk (i.val + r))

private def mdot {k : ℕ} (mask u v : Word k) : ZMod 2 :=
  ∑ j : Fin k, mask j * u j * v j

private def stdE {k : ℕ} (a : Fin k) : Word k :=
  fun i => if i = a then 1 else 0

private def slotVec {k : ℕ} (hk : 0 < k) (L : List ℕ) : Word k :=
  fun i => (L.map (fun site => if atPos hk site = i then (1 : ZMod 2) else 0)).sum

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  calc a = a + 0 := (add_zero a).symm
    _ = a + (a + b) := by rw [h]
    _ = (a + a) + b := (add_assoc a a b).symm
    _ = 0 + b := by rw [zmod2_add_self]
    _ = b := zero_add b

private lemma atPos_val_of_lt {k : ℕ} (hk : 0 < k) {a : ℕ} (ha : a < k) :
    (atPos hk a).val = a := Nat.mod_eq_of_lt ha

private lemma atPos_eq_iff {k : ℕ} (hk : 0 < k) (i : Fin k) {a : ℕ} (ha : a < k) :
    atPos hk a = i ↔ i.val = a := by
  constructor
  · intro h; rw [← h]; exact Nat.mod_eq_of_lt ha
  · intro h; apply Fin.ext; simp only [atPos, Nat.mod_eq_of_lt ha, h]

private lemma eq_atPos_iff {k : ℕ} (hk : 0 < k) (i : Fin k) {a : ℕ} (ha : a < k) :
    i = atPos hk a ↔ i.val = a := by
  rw [eq_comm, atPos_eq_iff hk i ha]

private lemma atPos_val_add {k : ℕ} (hk : 0 < k) (a b : ℕ) :
    atPos hk ((atPos hk a).val + b) = atPos hk (a + b) := by
  apply Fin.ext
  simp only [atPos, Nat.mod_add_mod]

private lemma atPos_add_mod {k : ℕ} (hk : 0 < k) (a b : ℕ) :
    atPos hk (a + b % k) = atPos hk (a + b) := by
  apply Fin.ext
  simp only [atPos, Nat.add_mod_mod]

private lemma atPos_val_sub_add {k : ℕ} (hk : 0 < k) (i : Fin k) (r : ℕ) :
    atPos hk ((atPos hk (i.val + r)).val + k - r % k) = i := by
  apply Fin.ext
  have hi : i.val < k := i.isLt
  have h1 : (i.val + r) % k = (i.val + r % k) % k := (Nat.add_mod_mod i.val r k).symm
  have hrm : r % k < k := Nat.mod_lt r hk
  simp only [atPos]
  rw [h1]
  by_cases hlt : i.val + r % k < k
  · rw [Nat.mod_eq_of_lt hlt]
    have h2 : i.val + r % k + k - r % k = i.val + k := by omega
    rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · have h2 : (i.val + r % k) % k = i.val + r % k - k := by
      have hsplit : i.val + r % k = (i.val + r % k - k) + k := by omega
      conv_lhs => rw [hsplit]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [h2]
    have h3 : i.val + r % k - k + k - r % k = i.val := by omega
    rw [h3, Nat.mod_eq_of_lt hi]

private lemma atPos_sub_shift {k : ℕ} (hk : 0 < k) (i : Fin k) (r t : ℕ) (ht : t < k) :
    atPos hk ((atPos hk (i.val + r)).val + k - t) = atPos hk ((atPos hk (i.val + k - t)).val + r) := by
  apply Fin.ext
  have hi : i.val < k := i.isLt
  have h1 : (i.val + r) % k + k - t = (i.val + r) % k + (k - t) := by omega
  simp only [atPos]
  rw [h1, Nat.mod_add_mod]
  have h2 : (i.val + k - t) % k + r = (i.val + (k - t)) % k + r := by
    have : i.val + k - t = i.val + (k - t) := by omega
    rw [this]
  rw [h2, Nat.mod_add_mod]
  congr 1
  omega

private lemma atPos_sub_comm {k : ℕ} (hk : 0 < k) (i : Fin k) (a b : ℕ) (ha : a < k) (hb : b < k) :
    atPos hk ((atPos hk (i.val + k - a)).val + k - b) =
    atPos hk ((atPos hk (i.val + k - b)).val + k - a) := by
  have h1 : (atPos hk (i.val + k - a)).val + k - b = (atPos hk (i.val + k - a)).val + (k - b) := by omega
  have h2 : (atPos hk (i.val + k - b)).val + k - a = (atPos hk (i.val + k - b)).val + (k - a) := by omega
  have h3 : i.val + k - a = i.val + (k - a) := by omega
  have h4 : i.val + k - b = i.val + (k - b) := by omega
  rw [h1, h2, h3, h4, atPos_val_add, atPos_val_add]
  congr 1; omega

private lemma shiftW_add {k : ℕ} (hk : 0 < k) (r1 r2 : ℕ) (v : Word k) :
    shiftW hk r1 (shiftW hk r2 v) = shiftW hk (r1 + r2) v := by
  funext i
  simp only [shiftW]
  rw [atPos_val_add]
  congr 1; apply Fin.ext; simp only [atPos]; congr 1; omega

private lemma shiftW_zero {k : ℕ} (hk : 0 < k) (v : Word k) :
    shiftW hk 0 v = v := by
  funext i
  simp only [shiftW, Nat.add_zero, atPos, Nat.mod_eq_of_lt i.isLt, Fin.eta]

private lemma shiftW_k {k : ℕ} (hk : 0 < k) (v : Word k) :
    shiftW hk k v = v := by
  funext i
  simp only [shiftW, atPos, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt, Fin.eta]

private lemma shiftW_proj {k : ℕ} (hk : 0 < k) (p v : Word k) (r : ℕ) :
    shiftW hk r (proj hk p v) = proj hk p (shiftW hk r v) := by
  funext i
  simp only [shiftW, proj]
  apply Finset.sum_congr rfl
  intro t _
  rw [atPos_sub_shift hk i r t.val t.isLt]

private lemma shiftW_mixOp {k : ℕ} (hk : 0 < k) (s r : ℕ) (v : Word k) :
    shiftW hk r (mixOp hk s v) = mixOp hk s (shiftW hk r v) := by
  funext i
  simp only [shiftW, mixOp]
  rw [atPos_val_add, atPos_val_add]
  have h1 : atPos hk (i.val + r + s) = atPos hk (i.val + s + r) := by
    apply Fin.ext; simp only [atPos]; congr 1; omega
  rw [h1, atPos_sub_shift hk i r (s % k) (Nat.mod_lt s hk)]

private lemma proj_add {k : ℕ} (hk : 0 < k) (p u v : Word k) :
    proj hk p (u + v) = proj hk p u + proj hk p v := by
  funext i
  simp only [proj, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma proj_zero {k : ℕ} (hk : 0 < k) (p : Word k) :
    proj hk p 0 = 0 := by
  funext i
  simp only [proj, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

private lemma mixOp_add {k : ℕ} (hk : 0 < k) (s : ℕ) (u v : Word k) :
    mixOp hk s (u + v) = mixOp hk s u + mixOp hk s v := by
  funext i
  simp only [mixOp, Pi.add_apply]
  ring

private lemma mixOp_zero {k : ℕ} (hk : 0 < k) (s : ℕ) :
    mixOp hk s 0 = 0 := by
  funext i
  simp only [mixOp, Pi.zero_apply, add_zero]

private lemma proj_mixOp {k : ℕ} (hk : 0 < k) (p : Word k) (s : ℕ) (v : Word k) :
    proj hk p (mixOp hk s v) = mixOp hk s (proj hk p v) := by
  funext i
  simp only [proj, mixOp, mul_add, Finset.sum_add_distrib]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro t _
    congr 1
    exact congrArg v (atPos_sub_shift hk i s t.val t.isLt).symm
  · apply Finset.sum_congr rfl
    intro t _
    congr 1
    exact congrArg v (atPos_sub_comm hk i t.val (s % k) t.isLt (Nat.mod_lt s hk))

private lemma mdot_comm {k : ℕ} (mask u v : Word k) :
    mdot mask u v = mdot mask v u := by
  simp only [mdot]
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma mdot_zero_right {k : ℕ} (mask u : Word k) :
    mdot mask u 0 = 0 := by
  simp only [mdot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

private lemma mdot_add_left {k : ℕ} (mask u1 u2 v : Word k) :
    mdot mask (u1 + u2) v = mdot mask u1 v + mdot mask u2 v := by
  simp only [mdot, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma mdot_add_right {k : ℕ} (mask u v1 v2 : Word k) :
    mdot mask u (v1 + v2) = mdot mask u v1 + mdot mask u v2 := by
  rw [mdot_comm, mdot_add_left, mdot_comm mask v1, mdot_comm mask v2]

private lemma polarize_output {k : ℕ} (hk : 0 < k) (s : ℕ) (x u v : Word k) (j : Fin k) :
    let out := fun w i =>
      let y := mixOp hk s w
      y i + (1 + y (atPos hk (i.val + 1))) * y (atPos hk (i.val + 2))
    out x j + out (x + u) j + out (x + v) j + out (x + u + v) j =
      mixOp hk s u (atPos hk (j.val + 1)) * mixOp hk s v (atPos hk (j.val + 2)) +
      mixOp hk s v (atPos hk (j.val + 1)) * mixOp hk s u (atPos hk (j.val + 2)) := by
  dsimp only
  rw [mixOp_add, mixOp_add, mixOp_add, mixOp_add]
  simp only [Pi.add_apply]
  generalize mixOp hk s x j = x0
  generalize mixOp hk s x (atPos hk (j.val + 1)) = x1
  generalize mixOp hk s x (atPos hk (j.val + 2)) = x2
  generalize mixOp hk s u j = u0
  generalize mixOp hk s u (atPos hk (j.val + 1)) = u1
  generalize mixOp hk s u (atPos hk (j.val + 2)) = u2
  generalize mixOp hk s v j = v0
  generalize mixOp hk s v (atPos hk (j.val + 1)) = v1
  generalize mixOp hk s v (atPos hk (j.val + 2)) = v2
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h4 : (4 : ZMod 2) = 0 := by decide
  calc
    x0 + (1 + x1) * x2 + (x0 + u0 + (1 + (x1 + u1)) * (x2 + u2)) +
      (x0 + v0 + (1 + (x1 + v1)) * (x2 + v2)) +
      (x0 + u0 + v0 + (1 + (x1 + u1 + v1)) * (x2 + u2 + v2))
      = 4 * x0 + 2 * u0 + 2 * v0 + 4 * x2 + 2 * u2 + 2 * v2 +
        4 * x1 * x2 + 2 * x1 * u2 + 2 * x1 * v2 + 2 * u1 * x2 + 2 * u1 * u2 +
        2 * v1 * x2 + 2 * v1 * v2 + (u1 * v2 + v1 * u2) := by ring
    _ = u1 * v2 + v1 * u2 := by simp [h2, h4]

private lemma mdot_shift_pow {k : ℕ} (hk : 0 < k) (p mask : Word k) (s : ℕ)
    (hstep : ∀ a b : Word k,
      let U := mixOp hk s (proj hk p a)
      let V := mixOp hk s (b + proj hk p b)
      mdot mask (shiftW hk 1 U) V = mdot mask U (shiftW hk 1 V)) :
    ∀ t : ℕ, ∀ a b : Word k,
      let U := mixOp hk s (proj hk p a)
      let V := mixOp hk s (b + proj hk p b)
      mdot mask (shiftW hk t U) V = mdot mask U (shiftW hk t V) := by
  intro t
  induction t with
  | zero =>
    intro a b
    simp only [shiftW_zero]
  | succ t ih =>
    intro a b
    have ha : shiftW hk 1 (mixOp hk s (proj hk p a)) = mixOp hk s (proj hk p (shiftW hk 1 a)) := by
      rw [shiftW_mixOp, shiftW_proj]
    have hb : shiftW hk t (mixOp hk s (b + proj hk p b)) =
        mixOp hk s (shiftW hk t b + proj hk p (shiftW hk t b)) := by
      rw [shiftW_mixOp]
      congr 1
      funext i
      simp only [shiftW, Pi.add_apply]
      congr 1
      exact congrFun (shiftW_proj hk p b t) i
    calc
      mdot mask (shiftW hk (t + 1) (mixOp hk s (proj hk p a))) (mixOp hk s (b + proj hk p b))
          = mdot mask (shiftW hk t (shiftW hk 1 (mixOp hk s (proj hk p a)))) (mixOp hk s (b + proj hk p b)) := by
              rw [shiftW_add]
      _ = mdot mask (shiftW hk t (mixOp hk s (proj hk p (shiftW hk 1 a)))) (mixOp hk s (b + proj hk p b)) := by
              rw [ha]
      _ = mdot mask (mixOp hk s (proj hk p (shiftW hk 1 a))) (shiftW hk t (mixOp hk s (b + proj hk p b))) :=
              ih (shiftW hk 1 a) b
      _ = mdot mask (shiftW hk 1 (mixOp hk s (proj hk p a))) (mixOp hk s (shiftW hk t b + proj hk p (shiftW hk t b))) := by
              rw [← ha, hb]
      _ = mdot mask (mixOp hk s (proj hk p a)) (shiftW hk 1 (mixOp hk s (shiftW hk t b + proj hk p (shiftW hk t b)))) :=
              hstep a (shiftW hk t b)
      _ = mdot mask (mixOp hk s (proj hk p a)) (shiftW hk (t + 1) (mixOp hk s (b + proj hk p b))) := by
              rw [← hb, shiftW_add]
              have h1t : 1 + t = t + 1 := Nat.add_comm 1 t
              rw [h1t]

private lemma mdot_proj_eq {k : ℕ} (hk : 0 < k) (p mask : Word k) (u v : Word k)
    (hpow : ∀ t : ℕ, mdot mask (shiftW hk t u) v = mdot mask u (shiftW hk t v)) :
    mdot mask (proj hk p u) v = mdot mask u (proj hk p v) := by
  have h1 : mdot mask (proj hk p u) v =
      ∑ t : Fin k, p t * mdot mask (shiftW hk (k - t.val) u) v := by
    simp only [mdot, proj, shiftW]
    have hl : (∑ j : Fin k, mask j * (∑ t : Fin k, p t * u (atPos hk (j.val + k - t.val))) * v j) =
        ∑ j : Fin k, ∑ t : Fin k, p t * (mask j * u (atPos hk (j.val + (k - t.val))) * v j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t _
      have hidx : j.val + k - t.val = j.val + (k - t.val) := by have := t.isLt; omega
      rw [hidx]; ring
    rw [hl, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.mul_sum]
  have h2 : mdot mask u (proj hk p v) =
      ∑ t : Fin k, p t * mdot mask u (shiftW hk (k - t.val) v) := by
    simp only [mdot, proj, shiftW]
    have hl : (∑ j : Fin k, mask j * u j * (∑ t : Fin k, p t * v (atPos hk (j.val + k - t.val)))) =
        ∑ j : Fin k, ∑ t : Fin k, p t * (mask j * u j * v (atPos hk (j.val + (k - t.val)))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      have hidx : j.val + k - t.val = j.val + (k - t.val) := by have := t.isLt; omega
      rw [hidx]; ring
    rw [hl, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.mul_sum]
  rw [h1, h2]
  apply Finset.sum_congr rfl
  intro t _
  rw [hpow (k - t.val)]

private lemma polarized_iff_orth {k : ℕ} (hk : 0 < k) (p : Word k)
    (hp : ∀ v : Word k, proj hk p (proj hk p v) = proj hk p v)
    (s : ℕ) (mask : Word k) :
    (∀ a b : Word k,
      let U := mixOp hk s (proj hk p a)
      let V := mixOp hk s (b + proj hk p b)
      (∑ j : Fin k, mask j *
        (U (atPos hk (j.val + 1)) * V (atPos hk (j.val + 2)) +
         V (atPos hk (j.val + 1)) * U (atPos hk (j.val + 2)))) = 0) ↔
    (∀ a b : Word k,
      mdot mask (mixOp hk s (proj hk p a)) (mixOp hk s (b + proj hk p b)) = 0) := by
  constructor
  · intro hpol
    have hstep : ∀ a b : Word k,
        let U := mixOp hk s (proj hk p a)
        let V := mixOp hk s (b + proj hk p b)
        mdot mask (shiftW hk 1 U) V = mdot mask U (shiftW hk 1 V) := by
      intro a b
      let a' := shiftW hk (k - 1) a
      let b' := shiftW hk (k - 1) b
      have ha1 : shiftW hk 1 a' = a := by
        simp only [a', shiftW_add]
        have : 1 + (k - 1) = k := by omega
        rw [this, shiftW_k]
      have hb1 : shiftW hk 1 b' = b := by
        simp only [b', shiftW_add]
        have : 1 + (k - 1) = k := by omega
        rw [this, shiftW_k]
      have h0 := hpol a' b'
      dsimp only at h0
      have hU1 : shiftW hk 1 (mixOp hk s (proj hk p a')) = mixOp hk s (proj hk p a) := by
        rw [shiftW_mixOp, shiftW_proj, ha1]
      have hV1 : shiftW hk 1 (mixOp hk s (b' + proj hk p b')) = mixOp hk s (b + proj hk p b) := by
        rw [shiftW_mixOp]
        congr 1
        funext i
        simp only [shiftW, Pi.add_apply]
        have hba : b' (atPos hk (i.val + 1)) = b i := congrFun hb1 i
        have hpb : proj hk p b' (atPos hk (i.val + 1)) = proj hk p b i := by
          have := congrFun (shiftW_proj hk p b' 1) i
          simp only [shiftW] at this
          rw [this, hb1]
        rw [hba, hpb]
      have hU2 : shiftW hk 2 (mixOp hk s (proj hk p a')) = shiftW hk 1 (mixOp hk s (proj hk p a)) := by
        rw [← hU1, shiftW_add]
      have hV2 : shiftW hk 2 (mixOp hk s (b' + proj hk p b')) = shiftW hk 1 (mixOp hk s (b + proj hk p b)) := by
        rw [← hV1, shiftW_add]
      have hrew : (∑ j : Fin k, mask j *
          (mixOp hk s (proj hk p a') (atPos hk (j.val + 1)) * mixOp hk s (b' + proj hk p b') (atPos hk (j.val + 2)) +
           mixOp hk s (b' + proj hk p b') (atPos hk (j.val + 1)) * mixOp hk s (proj hk p a') (atPos hk (j.val + 2)))) =
          mdot mask (mixOp hk s (proj hk p a)) (shiftW hk 1 (mixOp hk s (b + proj hk p b))) +
          mdot mask (shiftW hk 1 (mixOp hk s (proj hk p a))) (mixOp hk s (b + proj hk p b)) := by
        simp only [mdot, shiftW, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        have hu1 := congrFun hU1 j
        have hv1 := congrFun hV1 j
        have hu2 := congrFun hU2 j
        have hv2 := congrFun hV2 j
        simp only [shiftW] at hu1 hv1 hu2 hv2
        rw [hu1, hv1, hu2, hv2]
        ring
      rw [hrew] at h0
      exact (zmod2_eq_of_add_eq_zero h0).symm
    have hpow := mdot_shift_pow hk p mask s hstep
    intro a b
    have hself := mdot_proj_eq hk p mask (mixOp hk s (proj hk p a)) (mixOp hk s (b + proj hk p b))
      (fun t => hpow t a b)
    have hpu : proj hk p (mixOp hk s (proj hk p a)) = mixOp hk s (proj hk p a) := by
      rw [proj_mixOp, hp]
    have hpv : proj hk p (mixOp hk s (b + proj hk p b)) = 0 := by
      rw [proj_mixOp, proj_add, hp]
      have h0 : proj hk p b + proj hk p b = 0 := by
        funext i; simp only [Pi.add_apply, Pi.zero_apply]; exact zmod2_add_self _
      rw [h0, mixOp_zero]
    rw [hpu, hpv, mdot_zero_right] at hself
    exact hself
  · intro horth a b
    dsimp only
    have h1 := horth (shiftW hk 1 a) (shiftW hk 2 b)
    have h2 := horth (shiftW hk 2 a) (shiftW hk 1 b)
    have hrew : (∑ j : Fin k, mask j *
        (mixOp hk s (proj hk p a) (atPos hk (j.val + 1)) * mixOp hk s (b + proj hk p b) (atPos hk (j.val + 2)) +
         mixOp hk s (b + proj hk p b) (atPos hk (j.val + 1)) * mixOp hk s (proj hk p a) (atPos hk (j.val + 2)))) =
        mdot mask (mixOp hk s (proj hk p (shiftW hk 1 a))) (mixOp hk s (shiftW hk 2 b + proj hk p (shiftW hk 2 b))) +
        mdot mask (mixOp hk s (proj hk p (shiftW hk 2 a))) (mixOp hk s (shiftW hk 1 b + proj hk p (shiftW hk 1 b))) := by
      simp only [mdot, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      have hu1 : mixOp hk s (proj hk p (shiftW hk 1 a)) j = mixOp hk s (proj hk p a) (atPos hk (j.val + 1)) := by
        rw [← shiftW_proj, ← shiftW_mixOp]; rfl
      have hu2 : mixOp hk s (proj hk p (shiftW hk 2 a)) j = mixOp hk s (proj hk p a) (atPos hk (j.val + 2)) := by
        rw [← shiftW_proj, ← shiftW_mixOp]; rfl
      have hv1 : mixOp hk s (shiftW hk 1 b + proj hk p (shiftW hk 1 b)) j =
          mixOp hk s (b + proj hk p b) (atPos hk (j.val + 1)) := by
        have : shiftW hk 1 b + proj hk p (shiftW hk 1 b) = shiftW hk 1 (b + proj hk p b) := by
          funext i; simp only [shiftW, Pi.add_apply]; congr 1
          exact (congrFun (shiftW_proj hk p b 1) i).symm
        rw [this, ← shiftW_mixOp]; rfl
      have hv2 : mixOp hk s (shiftW hk 2 b + proj hk p (shiftW hk 2 b)) j =
          mixOp hk s (b + proj hk p b) (atPos hk (j.val + 2)) := by
        have : shiftW hk 2 b + proj hk p (shiftW hk 2 b) = shiftW hk 2 (b + proj hk p b) := by
          funext i; simp only [shiftW, Pi.add_apply]; congr 1
          exact (congrFun (shiftW_proj hk p b 2) i).symm
        rw [this, ← shiftW_mixOp]; rfl
      rw [hu1, hu2, hv1, hv2]
      ring
    rw [hrew, h1, h2, add_zero]

private def symForm {k : ℕ} (hk : 0 < k) (p mask y z : Word k) : ZMod 2 :=
  mdot mask y (proj hk p z) + mdot mask z (proj hk p y)

private lemma symForm_comm {k : ℕ} (hk : 0 < k) (p mask y z : Word k) :
    symForm hk p mask y z = symForm hk p mask z y := by
  simp only [symForm, add_comm]

private lemma symForm_self {k : ℕ} (hk : 0 < k) (p mask y : Word k) :
    symForm hk p mask y y = 0 := zmod2_add_self _

private lemma symForm_zero_left {k : ℕ} (hk : 0 < k) (p mask z : Word k) :
    symForm hk p mask 0 z = 0 := by
  simp only [symForm, mdot, proj_zero, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]

private lemma symForm_zero_right {k : ℕ} (hk : 0 < k) (p mask y : Word k) :
    symForm hk p mask y 0 = 0 := by
  rw [symForm_comm, symForm_zero_left]

private lemma symForm_add_left {k : ℕ} (hk : 0 < k) (p mask y1 y2 z : Word k) :
    symForm hk p mask (y1 + y2) z = symForm hk p mask y1 z + symForm hk p mask y2 z := by
  simp only [symForm, mdot_add_left, proj_add, mdot_add_right]
  ring

private lemma symForm_add_right {k : ℕ} (hk : 0 < k) (p mask y z1 z2 : Word k) :
    symForm hk p mask y (z1 + z2) = symForm hk p mask y z1 + symForm hk p mask y z2 := by
  rw [symForm_comm, symForm_add_left, symForm_comm hk p mask z1, symForm_comm hk p mask z2]

private lemma symForm_smul_left {k : ℕ} (hk : 0 < k) (p mask : Word k) (c : ZMod 2) (y z : Word k) :
    symForm hk p mask (fun i => c * y i) z = c * symForm hk p mask y z := by
  fin_cases c
  · change symForm hk p mask (fun i => (0 : ZMod 2) * y i) z = (0 : ZMod 2) * symForm hk p mask y z
    have h0 : (fun i : Fin k => (0 : ZMod 2) * y i) = 0 := by funext i; simp
    rw [h0, symForm_zero_left, zero_mul]
  · change symForm hk p mask (fun i => (1 : ZMod 2) * y i) z = (1 : ZMod 2) * symForm hk p mask y z
    have h1 : (fun i : Fin k => (1 : ZMod 2) * y i) = y := by funext i; simp
    rw [h1, one_mul]

private lemma symForm_sum_left {k : ℕ} (hk : 0 < k) (p mask : Word k) {ι : Type*}
    (S : Finset ι) (f : ι → Word k) (z : Word k) :
    symForm hk p mask (fun i => ∑ a ∈ S, f a i) z = ∑ a ∈ S, symForm hk p mask (f a) z := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact symForm_zero_left hk p mask z
  | insert a s ha ih =>
    have hfun : (fun i => ∑ x ∈ insert a s, f x i) = f a + (fun i => ∑ x ∈ s, f x i) := by
      funext i; simp only [Pi.add_apply, Finset.sum_insert ha]
    rw [hfun, symForm_add_left, ih, Finset.sum_insert ha]

private lemma symForm_sum_right {k : ℕ} (hk : 0 < k) (p mask : Word k) {ι : Type*}
    (S : Finset ι) (y : Word k) (f : ι → Word k) :
    symForm hk p mask y (fun i => ∑ a ∈ S, f a i) = ∑ a ∈ S, symForm hk p mask y (f a) := by
  rw [symForm_comm, symForm_sum_left]
  apply Finset.sum_congr rfl
  intro a _
  rw [symForm_comm]

private lemma orth_iff_symForm {k : ℕ} (hk : 0 < k) (p : Word k)
    (hp : ∀ v : Word k, proj hk p (proj hk p v) = proj hk p v)
    (s : ℕ) (mask : Word k) :
    (∀ a b : Word k, mdot mask (mixOp hk s (proj hk p a)) (mixOp hk s (b + proj hk p b)) = 0) ↔
    (∀ a b : Word k, symForm hk p mask (mixOp hk s a) (mixOp hk s b) = 0) := by
  constructor
  · intro horth a b
    let y := mixOp hk s a
    let z := mixOp hk s b
    have hy : y = proj hk p y + (y + proj hk p y) := by
      funext i; simp only [Pi.add_apply]
      calc y i = y i + 0 := (add_zero _).symm
        _ = y i + (proj hk p y i + proj hk p y i) := by rw [zmod2_add_self]
        _ = proj hk p y i + (y i + proj hk p y i) := by ring
    have hz : z = proj hk p z + (z + proj hk p z) := by
      funext i; simp only [Pi.add_apply]
      calc z i = z i + 0 := (add_zero _).symm
        _ = z i + (proj hk p z i + proj hk p z i) := by rw [zmod2_add_self]
        _ = proj hk p z i + (z i + proj hk p z i) := by ring
    have h1 : mdot mask (y + proj hk p y) (proj hk p z) = 0 := by
      have hya : y + proj hk p y = mixOp hk s (a + proj hk p a) := by
        simp only [y, mixOp_add, proj_mixOp]
      have hzb : proj hk p z = mixOp hk s (proj hk p b) := by
        simp only [z, proj_mixOp]
      rw [hya, hzb, mdot_comm]
      exact horth b a
    have h2 : mdot mask (z + proj hk p z) (proj hk p y) = 0 := by
      have hzb : z + proj hk p z = mixOp hk s (b + proj hk p b) := by
        simp only [z, mixOp_add, proj_mixOp]
      have hya : proj hk p y = mixOp hk s (proj hk p a) := by
        simp only [y, proj_mixOp]
      rw [hzb, hya, mdot_comm]
      exact horth a b
    change mdot mask y (proj hk p z) + mdot mask z (proj hk p y) = 0
    have hl : mdot mask y (proj hk p z) = mdot mask (proj hk p y) (proj hk p z) := by
      conv_lhs => rw [hy]
      rw [mdot_add_left, h1, add_zero]
    have hr : mdot mask z (proj hk p y) = mdot mask (proj hk p z) (proj hk p y) := by
      conv_lhs => rw [hz]
      rw [mdot_add_left, h2, add_zero]
    rw [hl, hr, mdot_comm mask (proj hk p z) (proj hk p y)]
    exact zmod2_add_self _
  · intro hsym a b
    have h0 := hsym (proj hk p a) (b + proj hk p b)
    simp only [symForm] at h0
    have hpa : proj hk p (mixOp hk s (proj hk p a)) = mixOp hk s (proj hk p a) := by
      rw [proj_mixOp, hp]
    have hpb : proj hk p (mixOp hk s (b + proj hk p b)) = 0 := by
      rw [proj_mixOp, proj_add, hp]
      have hz : proj hk p b + proj hk p b = 0 := by
        funext i; simp only [Pi.add_apply, Pi.zero_apply]; exact zmod2_add_self _
      rw [hz, mixOp_zero]
    rw [hpa, hpb, mdot_zero_right, zero_add, mdot_comm] at h0
    exact h0

private lemma symForm_stdE {k : ℕ} (hk : 0 < k) (p mask : Word k) (r c : ℕ) (hr : r < k) (hc : c < k) :
    symForm hk p mask (stdE (atPos hk r)) (stdE (atPos hk c)) =
      mask (atPos hk r) * p (atPos hk (r + k - c)) +
      mask (atPos hk c) * p (atPos hk (c + k - r)) := by
  have hterm : ∀ (a b : ℕ) (ha : a < k) (hb : b < k),
      mdot mask (stdE (atPos hk a)) (proj hk p (stdE (atPos hk b))) =
        mask (atPos hk a) * p (atPos hk (a + k - b)) := by
    intro a b ha hb
    simp only [mdot]
    rw [Finset.sum_eq_single (atPos hk a)]
    · simp only [stdE, ite_true, mul_one, proj]
      rw [Finset.sum_eq_single (atPos hk (a + k - b))]
      · have hpos : atPos hk ((atPos hk a).val + k - (atPos hk (a + k - b)).val) = atPos hk b := by
          apply Fin.ext
          simp only [atPos, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
          by_cases hle : b ≤ a
          · have h1 : (a + k - b) % k = a - b := by
              have hsp : a + k - b = (a - b) + k := by omega
              conv_lhs => rw [hsp]
              rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [h1]
            have hsp2 : a + k - (a - b) = b + k := by omega
            rw [hsp2, Nat.add_mod_right, Nat.mod_eq_of_lt hb]
          · have h1 : (a + k - b) % k = a + k - b := Nat.mod_eq_of_lt (by omega)
            rw [h1]
            have hsp2 : a + k - (a + k - b) = b := by omega
            rw [hsp2, Nat.mod_eq_of_lt hb]
        rw [hpos]
        simp
      · intro t _ hne
        have hne2 : atPos hk ((atPos hk a).val + k - t.val) ≠ atPos hk b := by
          intro heq
          apply hne
          apply Fin.ext
          have hv := congrArg Fin.val heq
          simp only [atPos, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hv
          simp only [atPos]
          have ht := t.isLt
          by_cases hle1 : t.val ≤ a
          · have h1 : (a + k - t.val) % k = a - t.val := by
              have hsp : a + k - t.val = (a - t.val) + k := by omega
              conv_lhs => rw [hsp]
              rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [h1] at hv
            have hsp2 : a + k - b = t.val + k := by omega
            rw [hsp2, Nat.add_mod_right, Nat.mod_eq_of_lt ht]
          · have h1 : (a + k - t.val) % k = a + k - t.val := Nat.mod_eq_of_lt (by omega)
            rw [h1] at hv
            have hsp2 : a + k - b = t.val := by omega
            rw [hsp2, Nat.mod_eq_of_lt ht]
        simp [hne2]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro j _ hne; simp [stdE, hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [symForm]
  rw [hterm r c hr hc, hterm c r hc hr]

private lemma slotVec_nil {k : ℕ} (hk : 0 < k) : slotVec hk [] = 0 := by
  funext i; simp [slotVec]

private lemma symForm_stdE_slotVec {k : ℕ} (hk : 0 < k) (p mask : Word k) (r : ℕ) (hr : r < k)
    (L2 : List ℕ) (hL2 : ∀ c ∈ L2, c < k) :
    symForm hk p mask (stdE (atPos hk r)) (slotVec hk L2) =
      (L2.map (fun c =>
        mask (atPos hk r) * p (atPos hk (r + k - c)) +
        mask (atPos hk c) * p (atPos hk (c + k - r)))).sum := by
  induction L2 with
  | nil =>
    rw [slotVec_nil, symForm_zero_right]
    simp
  | cons c cs ih =>
    have hc : c < k := hL2 c List.mem_cons_self
    have hcs : ∀ x ∈ cs, x < k := fun x hx => hL2 x (List.mem_cons_of_mem c hx)
    have hsplit : slotVec hk (c :: cs) = stdE (atPos hk c) + slotVec hk cs := by
      funext i
      simp only [slotVec, stdE, Pi.add_apply, List.map_cons, List.sum_cons]
      by_cases h : atPos hk c = i
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [hsplit, symForm_add_right, ih hcs, symForm_stdE hk p mask r c hr hc, List.map_cons, List.sum_cons]

private lemma symForm_slotVec {k : ℕ} (hk : 0 < k) (p mask : Word k) (L1 L2 : List ℕ)
    (hL1 : ∀ r ∈ L1, r < k) (hL2 : ∀ c ∈ L2, c < k) :
    symForm hk p mask (slotVec hk L1) (slotVec hk L2) =
      (L1.map (fun r => (L2.map (fun c =>
        mask (atPos hk r) * p (atPos hk (r + k - c)) +
        mask (atPos hk c) * p (atPos hk (c + k - r)))).sum)).sum := by
  induction L1 with
  | nil =>
    rw [slotVec_nil, symForm_zero_left]
    simp
  | cons r rs ih =>
    have hr : r < k := hL1 r List.mem_cons_self
    have hrs : ∀ x ∈ rs, x < k := fun x hx => hL1 x (List.mem_cons_of_mem r hx)
    have hsplit : slotVec hk (r :: rs) = stdE (atPos hk r) + slotVec hk rs := by
      funext i
      simp only [slotVec, stdE, Pi.add_apply, List.map_cons, List.sum_cons]
      by_cases h : atPos hk r = i
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [hsplit, symForm_add_left, ih hrs, symForm_stdE_slotVec hk p mask r hr L2 hL2, List.map_cons, List.sum_cons]

private lemma mix1_pair {k : ℕ} (hk : 0 < k) (a b : ℕ) (ha : a < b) (hb : b < k)
    (h3 : (b - a) % 3 = 0) :
    ∃ v : Word k, mixOp hk 1 v = stdE (atPos hk a) + stdE (atPos hk b) := by
  let v : Word k := fun t =>
    if a < t.val ∧ t.val < b ∧ (t.val - a) % 3 ≠ 0 then 1 else 0
  refine ⟨v, ?_⟩
  funext i
  have hi : i.val < k := i.isLt
  have hk3 : 3 ≤ k := by omega
  have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  simp only [mixOp, stdE, Pi.add_apply, h1m]
  have hp1 : (atPos hk (i.val + 1)).val = if i.val + 1 < k then i.val + 1 else 0 := by
    simp only [atPos]
    split_ifs with hlt
    · exact Nat.mod_eq_of_lt hlt
    · have : i.val + 1 = k := by omega
      rw [this, Nat.mod_self]
  have hm1 : (atPos hk (i.val + k - 1)).val = if i.val = 0 then k - 1 else i.val - 1 := by
    simp only [atPos]
    split_ifs with h0
    · rw [h0, Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
    · have hsp : i.val + k - 1 = (i.val - 1) + k := by omega
      rw [hsp, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hea : (i = atPos hk a) ↔ i.val = a := eq_atPos_iff hk i (by omega)
  have heb : (i = atPos hk b) ↔ i.val = b := eq_atPos_iff hk i hb
  simp only [v, hp1, hm1, hea, heb]
  split_ifs <;> first | rfl | omega

private lemma mix1_triple {k : ℕ} (hk : 0 < k) (h3 : 3 ≤ k) :
    ∃ v : Word k, mixOp hk 1 v = stdE (atPos hk 0) + stdE (atPos hk 1) + stdE (atPos hk 2) := by
  refine ⟨stdE (atPos hk 1), ?_⟩
  funext i
  have hi : i.val < k := i.isLt
  have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  simp only [mixOp, stdE, Pi.add_apply, h1m]
  have h0 : (i = atPos hk 0) ↔ i.val = 0 := eq_atPos_iff hk i (by omega)
  have h1 : (i = atPos hk 1) ↔ i.val = 1 := eq_atPos_iff hk i (by omega)
  have h2 : (i = atPos hk 2) ↔ i.val = 2 := eq_atPos_iff hk i (by omega)
  have hp1 : (atPos hk (i.val + 1) = atPos hk 1) ↔ i.val = 0 := by
    rw [eq_atPos_iff hk _ (by omega)]
    simp only [atPos]
    by_cases hlt : i.val + 1 < k
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · have : i.val + 1 = k := by omega
      rw [this, Nat.mod_self]; omega
  have hm1 : (atPos hk (i.val + k - 1) = atPos hk 1) ↔ i.val = 2 := by
    rw [eq_atPos_iff hk _ (by omega)]
    simp only [atPos]
    by_cases h0' : i.val = 0
    · rw [h0', Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; omega
    · have hsp : i.val + k - 1 = (i.val - 1) + k := by omega
      rw [hsp, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  simp only [h0, h1, h2, hp1, hm1]
  split_ifs <;> rfl

private lemma mix2_even_pair {k : ℕ} (hk : 0 < k) (a b : ℕ) (ha : a < b) (hb : b < k)
    (h6 : (b - a) % 6 = 0) :
    ∃ v : Word k, mixOp hk 2 v = stdE (atPos hk a) + stdE (atPos hk b) := by
  have hk6 : 6 ≤ k := by omega
  have h2m : 2 % k = 2 := Nat.mod_eq_of_lt (by omega)
  let v : Word k := fun t =>
    if a < t.val ∧ t.val < b ∧ (t.val - a) % 2 = 0 ∧ (t.val - a) % 6 ≠ 0 then 1 else 0
  refine ⟨v, ?_⟩
  funext i
  have hi : i.val < k := i.isLt
  simp only [mixOp, stdE, Pi.add_apply, h2m]
  have hp2 : (atPos hk (i.val + 2)).val = if i.val + 2 < k then i.val + 2 else i.val + 2 - k := by
    simp only [atPos]
    split_ifs with hlt
    · exact Nat.mod_eq_of_lt hlt
    · have hsp : i.val + 2 = (i.val + 2 - k) + k := by omega
      conv_lhs => rw [hsp]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hm2 : (atPos hk (i.val + k - 2)).val = if i.val < 2 then i.val + k - 2 else i.val - 2 := by
    simp only [atPos]
    split_ifs with hlt
    · exact Nat.mod_eq_of_lt (by omega)
    · have hsp : i.val + k - 2 = (i.val - 2) + k := by omega
      rw [hsp, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hea : (i = atPos hk a) ↔ i.val = a := eq_atPos_iff hk i (by omega)
  have heb : (i = atPos hk b) ↔ i.val = b := eq_atPos_iff hk i hb
  simp only [v, hp2, hm2, hea, heb]
  split_ifs <;> first | rfl | omega

private lemma mix2_even_triple {k : ℕ} (hk : 0 < k) (hk6 : 6 ≤ k) (r : ℕ) (hr : r < 2) :
    ∃ v : Word k, mixOp hk 2 v = stdE (atPos hk r) + stdE (atPos hk (r + 2)) + stdE (atPos hk (r + 4)) := by
  refine ⟨stdE (atPos hk (r + 2)), ?_⟩
  funext i
  have hi : i.val < k := i.isLt
  have h2m : 2 % k = 2 := Nat.mod_eq_of_lt (by omega)
  simp only [mixOp, stdE, Pi.add_apply, h2m]
  have h0 : (i = atPos hk r) ↔ i.val = r := eq_atPos_iff hk i (by omega)
  have h1 : (i = atPos hk (r + 2)) ↔ i.val = r + 2 := eq_atPos_iff hk i (by omega)
  have h2 : (i = atPos hk (r + 4)) ↔ i.val = r + 4 := eq_atPos_iff hk i (by omega)
  have hp2 : (atPos hk (i.val + 2) = atPos hk (r + 2)) ↔ i.val = r := by
    rw [eq_atPos_iff hk _ (by omega)]
    simp only [atPos]
    by_cases hlt : i.val + 2 < k
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · have hsp : i.val + 2 = (i.val + 2 - k) + k := by omega
      conv_lhs => rw [hsp]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  have hm2 : (atPos hk (i.val + k - 2) = atPos hk (r + 2)) ↔ i.val = r + 4 := by
    rw [eq_atPos_iff hk _ (by omega)]
    simp only [atPos]
    by_cases hlt : i.val < 2
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · have hsp : i.val + k - 2 = (i.val - 2) + k := by omega
      rw [hsp, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  simp only [h0, h1, h2, hp2, hm2]
  split_ifs <;> rfl

private lemma mix2_odd_pullback {k : ℕ} (hk : 0 < k) (hodd : k % 2 = 1) (w : Word k) :
    let half := (k + 1) / 2
    let pull := fun (v : Word k) (i : Fin k) => v (atPos hk (half * i.val))
    ∀ v : Word k, mixOp hk 1 v = w → mixOp hk 2 (pull v) = pull w := by
  intro half pull v hv
  have h2half : 2 * half = k + 1 := by omega
  funext i
  simp only [pull, mixOp, ← hv]
  by_cases hk1 : k = 1
  · subst hk1
    have hi0 : i = ⟨0, by omega⟩ := Fin.ext (by omega)
    subst hi0
    simp [atPos]
  · have hk3 : 3 ≤ k := by omega
    have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    have h2m : 2 % k = 2 := Nat.mod_eq_of_lt (by omega)
    rw [h1m, h2m]
    have hplus : atPos hk (half * (atPos hk (i.val + 2)).val) = atPos hk ((atPos hk (half * i.val)).val + 1) := by
      apply Fin.ext
      simp only [atPos]
      calc
        (half * ((i.val + 2) % k)) % k = (half * (i.val + 2)) % k := Nat.mul_mod_mod half (i.val + 2) k
        _ = (half * i.val + 2 * half) % k := by congr 1; ring
        _ = (half * i.val + 1 + k) % k := by rw [h2half]; congr 1; omega
        _ = (half * i.val + 1) % k := Nat.add_mod_right _ k
        _ = ((half * i.val) % k + 1) % k := (Nat.mod_add_mod _ _ _).symm
    have hminus : atPos hk (half * (atPos hk (i.val + k - 2)).val) = atPos hk ((atPos hk (half * i.val)).val + k - 1) := by
      apply Fin.ext
      simp only [atPos]
      have h1 : (half * ((i.val + k - 2) % k)) % k = (half * (i.val + k - 2)) % k :=
        Nat.mul_mod_mod half (i.val + k - 2) k
      rw [h1]
      have h2 : half * (i.val + k - 2) + 1 = half * i.val + (half - 1) * k := by
        have hsub : i.val + k - 2 + 2 = i.val + k := by omega
        have hmul : half * (i.val + k - 2) + half * 2 = half * i.val + half * k := by
          calc half * (i.val + k - 2) + half * 2 = half * (i.val + k - 2 + 2) := by ring
            _ = half * (i.val + k) := by rw [hsub]
            _ = half * i.val + half * k := by ring
        have h2h : half * 2 = k + 1 := by omega
        have hhk : half * k = (half - 1) * k + k := by
          have : half = (half - 1) + 1 := by omega
          conv_lhs => rw [this]
          ring
        omega
      have hmod1 : (half * (i.val + k - 2) + 1) % k = (half * i.val) % k := by
        rw [h2, Nat.add_mul_mod_self_right]
      have hm := Nat.mod_lt (half * i.val) hk
      have hm2 := Nat.mod_lt (half * (i.val + k - 2)) hk
      have hstep : ((half * (i.val + k - 2)) % k + 1) % k = (half * i.val) % k := by
        rw [← hmod1, Nat.mod_add_mod]
      by_cases hzero : (half * i.val) % k = 0
      · rw [hzero] at hstep ⊢
        have hval : (half * (i.val + k - 2)) % k = k - 1 := by
          by_cases hlt : (half * (i.val + k - 2)) % k + 1 < k
          · rw [Nat.mod_eq_of_lt hlt] at hstep; omega
          · omega
        rw [hval, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      · have hval : (half * (i.val + k - 2)) % k + 1 = (half * i.val) % k := by
          by_cases hlt : (half * (i.val + k - 2)) % k + 1 < k
          · rw [Nat.mod_eq_of_lt hlt] at hstep; exact hstep
          · have heq : (half * (i.val + k - 2)) % k + 1 = k := by omega
            rw [heq, Nat.mod_self] at hstep; exact absurd hstep.symm hzero
        have hpos : 1 ≤ (half * i.val) % k := Nat.pos_of_ne_zero hzero
        have hsub2 : (half * i.val) % k + k - 1 = ((half * i.val) % k - 1) + k := by omega
        have hlt2 : (half * i.val) % k - 1 < k := by omega
        rw [hsub2, Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
        omega
    rw [hplus, hminus]

private lemma gcd_s_info {k s : ℕ} (hk : 0 < k) (h3 : 3 ∣ k) (hs : s = 1 ∨ s = 2) :
    (Nat.gcd k s = 1 ∧ 3 ≤ k ∧ 3 * Nat.gcd k s ∣ k) ∨
    (s = 2 ∧ Nat.gcd k s = 2 ∧ 2 ∣ k ∧ 6 ≤ k ∧ 3 * Nat.gcd k s ∣ k) := by
  obtain ⟨m, rfl⟩ := h3
  rcases hs with rfl | rfl
  · left
    have hg : Nat.gcd (3 * m) 1 = 1 := Nat.gcd_one_right _
    exact ⟨hg, by omega, by rw [hg]; exact ⟨m, by ring⟩⟩
  · by_cases hev : m % 2 = 0
    · right
      have h2m : 2 ∣ 3 * m := ⟨3 * (m / 2), by omega⟩
      have hg : Nat.gcd (3 * m) 2 = 2 := Nat.gcd_eq_right h2m
      exact ⟨rfl, hg, h2m, by omega, by rw [hg]; exact ⟨m / 2, by omega⟩⟩
    · left
      have hnot2 : ¬ (2 ∣ 3 * m) := by intro ⟨q, hq⟩; omega
      have hg : Nat.gcd (3 * m) 2 = 1 := by
        rw [Nat.gcd_comm]
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnot2
      exact ⟨hg, by omega, by rw [hg]; exact ⟨m, by ring⟩⟩

private lemma basis_in_image_aux {k s g : ℕ} (hk : 0 < k) (h3 : 3 ∣ k) (hs : s = 1 ∨ s = 2)
    (hg_def : g = Nat.gcd k s) (n : ℕ) (hn : n < k - 2 * g) :
    ∃ v : Word k,
      mixOp hk s v = slotVec hk
        (if n < g then [n, n + g, n + 2 * g]
         else [n + 2 * g, (n + 2 * g) % (3 * g)]) := by
  have hslot2 : ∀ a b : ℕ, slotVec hk [a, b] = stdE (atPos hk a) + stdE (atPos hk b) := by
    intro a b; funext i
    simp only [slotVec, stdE, Pi.add_apply, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    by_cases ha : atPos hk a = i <;> by_cases hb : atPos hk b = i <;> simp_all [eq_comm]
  have hslot3 : ∀ a b c : ℕ, slotVec hk [a, b, c] = stdE (atPos hk a) + stdE (atPos hk b) + stdE (atPos hk c) := by
    intro a b c; funext i
    simp only [slotVec, stdE, Pi.add_apply, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    by_cases ha : atPos hk a = i <;> by_cases hb : atPos hk b = i <;> by_cases hc : atPos hk c = i <;> simp_all [eq_comm]; ring
  have hinfo := gcd_s_info hk h3 hs
  rw [← hg_def] at hinfo
  rcases hs with rfl | rfl
  · have hg1 : g = 1 := by rw [hg_def]; exact Nat.gcd_one_right k
    subst hg1
    have hk3 : 3 ≤ k := by obtain ⟨m, rfl⟩ := h3; omega
    split_ifs with hlt
    · have hn0 : n = 0 := by omega
      subst hn0
      rw [hslot3]
      exact mix1_triple hk hk3
    · rw [hslot2]
      have ha : (n + 2 * 1) % (3 * 1) < n + 2 * 1 := by omega
      have hb : n + 2 * 1 < k := by omega
      have hm3 : (n + 2 * 1 - (n + 2 * 1) % (3 * 1)) % 3 = 0 := by omega
      obtain ⟨v, hv⟩ := mix1_pair hk _ _ ha hb hm3
      exact ⟨v, by rw [hv, add_comm]⟩
  · rcases hinfo with ⟨rfl, hk3, _⟩ | ⟨_, rfl, _, hk6, _⟩
    · have hodd : k % 2 = 1 := by
        by_contra hne
        have h2k : 2 ∣ k := Nat.dvd_of_mod_eq_zero (by omega)
        have : Nat.gcd k 2 = 2 := Nat.gcd_eq_right h2k
        omega
      let half := (k + 1) / 2
      have h2half : 2 * half = k + 1 := by omega
      have hpull_e : ∀ (c : ℕ) (hc : c < k),
          (fun i : Fin k => stdE (atPos hk ((half * c) % k)) (atPos hk (half * i.val))) = stdE (atPos hk c) := by
        intro c hc
        funext i
        simp only [stdE]
        have hiff : atPos hk (half * i.val) = atPos hk ((half * c) % k) ↔ i = atPos hk c := by
          constructor
          · intro h
            have hv := congrArg Fin.val h
            simp only [atPos, Nat.mod_mod] at hv
            have hmul : (2 * (half * i.val)) % k = (2 * (half * c)) % k := by
              calc (2 * (half * i.val)) % k = (2 * ((half * i.val) % k)) % k := (Nat.mul_mod_mod 2 _ k).symm
                _ = (2 * ((half * c) % k)) % k := by rw [hv]
                _ = (2 * (half * c)) % k := Nat.mul_mod_mod 2 _ k
            have hl : (2 * (half * i.val)) % k = i.val := by
              have hsp : 2 * (half * i.val) = i.val + i.val * k := by
                calc 2 * (half * i.val) = (2 * half) * i.val := by ring
                  _ = (k + 1) * i.val := by rw [h2half]
                  _ = i.val + i.val * k := by ring
              rw [hsp, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]
            have hr' : (2 * (half * c)) % k = c := by
              have hsp : 2 * (half * c) = c + c * k := by
                calc 2 * (half * c) = (2 * half) * c := by ring
                  _ = (k + 1) * c := by rw [h2half]
                  _ = c + c * k := by ring
              rw [hsp, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
            rw [hl, hr'] at hmul
            exact (eq_atPos_iff hk i hc).mpr hmul
          · intro h; rw [h]; apply Fin.ext; simp only [atPos, Nat.mod_eq_of_lt hc, Nat.mod_mod]
        by_cases h : atPos hk (half * i.val) = atPos hk ((half * c) % k)
        · simp only [ite_eq_left_iff.mpr (fun hn => absurd h hn), ite_eq_left_iff.mpr (fun hn => absurd (hiff.mp h) hn)]
        · have h' : ¬ i = atPos hk c := fun h1 => h (hiff.mpr h1)
          simp only [ite_eq_right_iff.mpr (fun hp => absurd hp h), ite_eq_right_iff.mpr (fun hp => absurd hp h')]
      split_ifs with hlt
      · have hn0 : n = 0 := by omega
        subst hn0
        rw [hslot3]
        have hhalf0 : (half * 0) % k = 0 := by simp
        have hhalf2 : (half * 2) % k = 1 := by
          have hsp : half * 2 = 1 + k := by omega
          rw [hsp, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have hhalf1 : (half * 1) % k = half := by
          simp only [mul_one]; exact Nat.mod_eq_of_lt (by omega)
        obtain ⟨v0, hv0⟩ := mix1_triple hk hk3
        have hhalf_mod3 : (half - 2) % 3 = 0 := by
          obtain ⟨m, rfl⟩ := h3
          omega
        by_cases hk3eq : k = 3
        · have hhalf_eq : half = 2 := by omega
          refine ⟨fun i => v0 (atPos hk (half * i.val)), ?_⟩
          have hp := mix2_odd_pullback hk hodd _ v0 hv0
          rw [hp]
          funext i
          simp only [Pi.add_apply]
          have h0 : stdE (atPos hk 0) (atPos hk (half * i.val)) = stdE (atPos hk 0) i := by
            rw [← hhalf0]; exact congrFun (hpull_e 0 (by omega)) i
          have h1m : (half * 1) % k = 2 := by rw [hhalf1, hhalf_eq]
          have h1 : stdE (atPos hk 2) (atPos hk (half * i.val)) = stdE (atPos hk 1) i := by
            have hraw := congrFun (hpull_e 1 (by omega)) i
            rw [h1m] at hraw
            exact hraw
          have h2 : stdE (atPos hk 1) (atPos hk (half * i.val)) = stdE (atPos hk 2) i := by
            rw [← hhalf2]; exact congrFun (hpull_e 2 (by omega)) i
          change stdE (atPos hk 0) (atPos hk (half * i.val)) + stdE (atPos hk 1) (atPos hk (half * i.val)) +
            stdE (atPos hk 2) (atPos hk (half * i.val)) =
            stdE (atPos hk 0) i + stdE (atPos hk 1) i + stdE (atPos hk 2) i
          rw [h0, h1, h2]
          ring
        · have h2lt : 2 < half := by omega
          have hhalt : half < k := by omega
          obtain ⟨v1, hv1⟩ := mix1_pair hk 2 half h2lt hhalt hhalf_mod3
          have hsum : mixOp hk 1 (v0 + v1) =
              stdE (atPos hk 0) + stdE (atPos hk 1) + stdE (atPos hk half) := by
            rw [mixOp_add, hv0, hv1]
            funext i; simp only [Pi.add_apply]
            calc
              stdE (atPos hk 0) i + stdE (atPos hk 1) i + stdE (atPos hk 2) i +
                (stdE (atPos hk 2) i + stdE (atPos hk half) i)
                = stdE (atPos hk 0) i + stdE (atPos hk 1) i +
                  (stdE (atPos hk 2) i + stdE (atPos hk 2) i) + stdE (atPos hk half) i := by ring
              _ = stdE (atPos hk 0) i + stdE (atPos hk 1) i + stdE (atPos hk half) i := by
                  rw [zmod2_add_self, add_zero]
          refine ⟨fun i => (v0 + v1) (atPos hk (half * i.val)), ?_⟩
          have hp := mix2_odd_pullback hk hodd _ (v0 + v1) hsum
          rw [hp]
          funext i
          simp only [Pi.add_apply]
          have h0 := congrFun (hpull_e 0 (by omega)) i
          have h1 := congrFun (hpull_e 1 (by omega)) i
          have h2 := congrFun (hpull_e 2 (by omega)) i
          rw [hhalf0] at h0; rw [hhalf1] at h1; rw [hhalf2] at h2
          rw [h0, h1, h2]
          ring
      · rw [hslot2]
        let a := n + 2 * 1
        let b := (n + 2 * 1) % (3 * 1)
        have ha_lt : a < k := by omega
        have hb_lt : b < k := by omega
        have hab_ne : a ≠ b := by omega
        have hab_mod3 : a % 3 = b % 3 := by dsimp only [a, b]; omega
        let a' := (half * a) % k
        let b' := (half * b) % k
        have ha'_lt : a' < k := Nat.mod_lt _ hk
        have hb'_lt : b' < k := Nat.mod_lt _ hk
        have hne' : a' ≠ b' := by
          intro heq
          apply hab_ne
          have hmul : (2 * (half * a)) % k = (2 * (half * b)) % k := by
            calc (2 * (half * a)) % k = (2 * a') % k := (Nat.mul_mod_mod 2 _ k).symm
              _ = (2 * b') % k := by rw [heq]
              _ = (2 * (half * b)) % k := Nat.mul_mod_mod 2 _ k
          have hl : (2 * (half * a)) % k = a := by
            have hsp : 2 * (half * a) = a + a * k := by
              calc 2 * (half * a) = (2 * half) * a := by ring
                _ = (k + 1) * a := by rw [h2half]
                _ = a + a * k := by ring
            rw [hsp, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha_lt]
          have hr' : (2 * (half * b)) % k = b := by
            have hsp : 2 * (half * b) = b + b * k := by
              calc 2 * (half * b) = (2 * half) * b := by ring
                _ = (k + 1) * b := by rw [h2half]
                _ = b + b * k := by ring
            rw [hsp, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb_lt]
          omega
        have hmod3' : a' % 3 = b' % 3 := by
          obtain ⟨m, rfl⟩ := h3
          have h1 : a' % 3 = (half * a) % 3 := Nat.mod_mod_of_dvd (half * a) ⟨m, rfl⟩
          have h2 : b' % 3 = (half * b) % 3 := Nat.mod_mod_of_dvd (half * b) ⟨m, rfl⟩
          rw [h1, h2, Nat.mul_mod half a 3, Nat.mul_mod half b 3, hab_mod3]
        have hex1 : ∃ v : Word k, mixOp hk 1 v = stdE (atPos hk a') + stdE (atPos hk b') := by
          rcases lt_or_gt_of_ne hne' with hlt' | hgt'
          · exact mix1_pair hk a' b' hlt' hb'_lt (by omega)
          · obtain ⟨v, hv⟩ := mix1_pair hk b' a' hgt' ha'_lt (by omega)
            exact ⟨v, by rw [hv, add_comm]⟩
        obtain ⟨v, hv⟩ := hex1
        refine ⟨fun i => v (atPos hk (half * i.val)), ?_⟩
        have hp := mix2_odd_pullback hk hodd _ v hv
        rw [hp]
        funext i
        simp only [Pi.add_apply]
        rw [congrFun (hpull_e a ha_lt) i, congrFun (hpull_e b hb_lt) i]
    · split_ifs with hlt
      · rw [hslot3]
        exact mix2_even_triple hk hk6 n hlt
      · rw [hslot2]
        have ha : (n + 2 * 2) % (3 * 2) < n + 2 * 2 := by omega
        have hb : n + 2 * 2 < k := by omega
        have hm6 : (n + 2 * 2 - (n + 2 * 2) % (3 * 2)) % 6 = 0 := by omega
        obtain ⟨v, hv⟩ := mix2_even_pair hk _ _ ha hb hm6
        exact ⟨v, by rw [hv, add_comm]⟩

private lemma mix_class_sum_eq_aux {k s g : ℕ} (hk : 0 < k) (h3 : 3 ∣ k) (hs : s = 1 ∨ s = 2)
    (hg_def : g = Nat.gcd k s) (v : Word k) (r : ℕ) (hr : r < g) (c : ℕ) (hc : c < 3) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val % (3 * g) = r + c * g), mixOp hk s v i) =
    (∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val % g = r), v i) := by
  have hinfo := gcd_s_info hk h3 hs
  rw [← hg_def] at hinfo
  have h3g_dvd : 3 * g ∣ k := by rcases hinfo with ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ <;> exact h
  have hg12 : g = 1 ∨ g = 2 := by
    rcases hinfo with ⟨h, _, _⟩ | ⟨_, h, _, _, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have h3g_pos : 0 < 3 * g := by omega
  have hshift_sum : ∀ (d : ℕ) (hd : d < k),
      (∑ i ∈ Finset.univ.filter (fun i : Fin k => i.val % (3 * g) = r + c * g), v (atPos hk (i.val + d))) =
      (∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val % (3 * g) = (r + c * g + d) % (3 * g)), v j) := by
    intro d hd
    apply Finset.sum_bij (fun i _ => atPos hk (i.val + d))
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      have hmod : (atPos hk (i.val + d)).val % (3 * g) = (i.val + d) % (3 * g) :=
        Nat.mod_mod_of_dvd (i.val + d) h3g_dvd
      rw [hmod, Nat.add_mod, hi, Nat.add_mod_mod]
    · intro i1 _ i2 _ heq
      have h1 := atPos_val_sub_add hk i1 d
      have h2 := atPos_val_sub_add hk i2 d
      rw [heq] at h1
      rw [← h1, h2]
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      refine ⟨atPos hk (j.val + k - d), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hmod : (atPos hk (j.val + k - d)).val % (3 * g) = (j.val + k - d) % (3 * g) :=
          Nat.mod_mod_of_dvd _ h3g_dvd
        rw [hmod]
        have hsub : (j.val + k - d) + d = j.val + k := by omega
        have hmod2 : ((j.val + k - d) + d) % (3 * g) = j.val % (3 * g) := by
          rw [hsub, Nat.add_mod, Nat.mod_eq_zero_of_dvd h3g_dvd, add_zero, Nat.mod_mod]
        rw [hj] at hmod2
        have hlt : r + c * g < 3 * g := by rcases hg12 with rfl | rfl <;> omega
        have hdm : ((j.val + k - d) % (3 * g) + d % (3 * g)) % (3 * g) =
            ((r + c * g) + d % (3 * g)) % (3 * g) := by
          calc ((j.val + k - d) % (3 * g) + d % (3 * g)) % (3 * g)
              = ((j.val + k - d) + d) % (3 * g) := (Nat.add_mod _ _ _).symm
            _ = (r + c * g + d) % (3 * g) := hmod2
            _ = (r + c * g + d % (3 * g)) % (3 * g) := (Nat.add_mod_mod _ _ _).symm
        rcases hg12 with rfl | rfl <;> omega
      · apply Fin.ext
        simp only [atPos]
        have hsub : j.val + k - d = j.val + (k - d) := by omega
        rw [hsub, Nat.mod_add_mod]
        have hadd : j.val + (k - d) + d = j.val + k := by omega
        rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
    · intro i _; rfl
  simp only [mixOp, Finset.sum_add_distrib]
  have hs_mod : s % k = s := by
    have hk3 : 3 ≤ k := by rcases hinfo with ⟨_, h, _⟩ | ⟨_, _, _, h, _⟩ <;> omega
    exact Nat.mod_eq_of_lt (by omega)
  have hs_lt : s % k < k := Nat.mod_lt s hk
  have hs_eq : ∀ i : Fin k, atPos hk (i.val + s) = atPos hk (i.val + s % k) := fun i => (atPos_add_mod hk i.val s).symm
  simp only [hs_eq]
  have hterm1 := hshift_sum (s % k) hs_lt
  have hsub_lt : k - s % k < k := by rw [hs_mod]; rcases hs with rfl | rfl <;> omega
  have hsub_rw : ∀ i : Fin k, atPos hk (i.val + k - s % k) = atPos hk (i.val + (k - s % k)) := by
    intro i; congr 1; omega
  simp only [hsub_rw]
  have hterm2 := hshift_sum (k - s % k) hsub_lt
  rw [hterm1, hterm2, hs_mod]
  have hpart : ∀ (r0 r1 r2 : ℕ),
      r0 < 3 * g → r1 < 3 * g → r2 < 3 * g →
      r0 % g = r → r1 % g = r → r2 % g = r →
      r0 ≠ r1 → r0 ≠ r2 → r1 ≠ r2 →
      (∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val % (3 * g) = r0), v j) +
      (∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val % (3 * g) = r1), v j) +
      (∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val % (3 * g) = r2), v j) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val % g = r), v j := by
    intro r0 r1 r2 hr0 hr1 hr2 hm0 hm1 hm2 h01 h02 h12
    have hd01 : Disjoint (Finset.univ.filter (fun j : Fin k => j.val % (3 * g) = r0))
        (Finset.univ.filter (fun j : Fin k => j.val % (3 * g) = r1)) := by
      rw [Finset.disjoint_filter]; intro j _ h1 h2; omega
    have hd012 : Disjoint
        (Finset.univ.filter (fun j : Fin k => j.val % (3 * g) = r0) ∪
         Finset.univ.filter (fun j : Fin k => j.val % (3 * g) = r1))
        (Finset.univ.filter (fun j : Fin k => j.val % (3 * g) = r2)) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
      omega
    rw [← Finset.sum_union hd01, ← Finset.sum_union hd012]
    congr 1
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · have hd3 : g ∣ 3 * g := ⟨3, by ring⟩
      rintro ((h | h) | h)
      · rw [← Nat.mod_mod_of_dvd j.val hd3, h, hm0]
      · rw [← Nat.mod_mod_of_dvd j.val hd3, h, hm1]
      · rw [← Nat.mod_mod_of_dvd j.val hd3, h, hm2]
    · intro hj
      have hd3 : g ∣ 3 * g := ⟨3, by ring⟩
      have hm : (j.val % (3 * g)) % g = r := by rw [Nat.mod_mod_of_dvd j.val hd3]; exact hj
      have hdiv : ∀ x : ℕ, x < 3 * g → x % g = r → x = r ∨ x = r + g ∨ x = r + 2 * g := by
        intro x hx hxm
        rcases hg12 with hg1 | hg2
        · rw [hg1] at hx hxm hr ⊢; omega
        · rw [hg2] at hx hxm hr ⊢; omega
      have hpigeon : ∀ a b c x y0 y1 y2 : ℕ,
          (a = y0 ∨ a = y1 ∨ a = y2) → (b = y0 ∨ b = y1 ∨ b = y2) →
          (c = y0 ∨ c = y1 ∨ c = y2) → (x = y0 ∨ x = y1 ∨ x = y2) →
          a ≠ b → a ≠ c → b ≠ c → (x = a ∨ x = b) ∨ x = c := by omega
      exact hpigeon r0 r1 r2 (j.val % (3 * g)) r (r + g) (r + 2 * g)
        (hdiv r0 hr0 hm0) (hdiv r1 hr1 hm1) (hdiv r2 hr2 hm2)
        (hdiv (j.val % (3 * g)) (Nat.mod_lt _ h3g_pos) hm) h01 h02 h12
  obtain ⟨q, hq⟩ := h3g_dvd
  apply hpart (r + c * g) ((r + c * g + s) % (3 * g)) ((r + c * g + (k - s)) % (3 * g))
  · rcases hinfo with ⟨hg, _, _⟩ | ⟨_, hg, _, _, _⟩ <;> subst hg <;> omega
  · exact Nat.mod_lt _ h3g_pos
  · exact Nat.mod_lt _ h3g_pos
  · rcases hinfo with ⟨hg, _, _⟩ | ⟨_, hg, _, _, _⟩ <;> subst hg <;> omega
  · rcases hinfo with ⟨hg, _, _⟩ | ⟨hs2, hg, _, _, _⟩ <;> rcases hs with rfl | rfl <;> subst hg <;> omega
  · rcases hinfo with ⟨hg, _, _⟩ | ⟨hs2, hg, _, _, _⟩ <;> rcases hs with rfl | rfl <;> subst hg <;> omega
  · rcases hinfo with ⟨hg, _, _⟩ | ⟨hs2, hg, _, _, _⟩ <;> rcases hs with rfl | rfl <;> subst hg <;> omega
  · rcases hinfo with ⟨hg, _, _⟩ | ⟨hs2, hg, _, _, _⟩ <;> rcases hs with rfl | rfl <;> subst hg <;> omega
  · rcases hinfo with ⟨hg, _, _⟩ | ⟨hs2, hg, _, _, _⟩ <;> rcases hs with rfl | rfl <;> subst hg <;> omega

private lemma expand_in_basis_aux {k s g : ℕ} (hk : 0 < k) (h3 : 3 ∣ k) (hs : s = 1 ∨ s = 2)
    (hg_def : g = Nat.gcd k s) (v : Word k) :
    ∃ coeff : Fin (k - 2 * g) → ZMod 2,
      mixOp hk s v = fun i => ∑ n : Fin (k - 2 * g), coeff n * slotVec hk
        (if n.val < g then [n.val, n.val + g, n.val + 2 * g]
         else [n.val + 2 * g, (n.val + 2 * g) % (3 * g)]) i := by
  have hinfo := gcd_s_info hk h3 hs
  rw [← hg_def] at hinfo
  have hg12 : g = 1 ∨ g = 2 := by
    rcases hinfo with ⟨h, _, _⟩ | ⟨_, h, _, _, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have h3g_le : 3 * g ≤ k := by
    rcases hinfo with ⟨rfl, hk3, _⟩ | ⟨_, rfl, _, hk6, _⟩ <;> omega
  have hg_pos : 0 < g := by omega
  let basisSlots : Fin (k - 2 * g) → List ℕ := fun n =>
    if n.val < g then [n.val, n.val + g, n.val + 2 * g]
    else [n.val + 2 * g, (n.val + 2 * g) % (3 * g)]
  let y := mixOp hk s v
  let coeff : Fin (k - 2 * g) → ZMod 2 := fun n =>
    if n.val < g then
      ∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val % (3 * g) = n.val), y j
    else
      y (atPos hk (n.val + 2 * g))
  refine ⟨coeff, ?_⟩
  funext i
  have hi : i.val < k := i.isLt
  by_cases hge : 3 * g ≤ i.val
  · let n0 : Fin (k - 2 * g) := ⟨i.val - 2 * g, by omega⟩
    rw [Finset.sum_eq_single n0]
    · have hn0_ge : ¬ n0.val < g := by dsimp only [n0]; omega
      have hpos : atPos hk (n0.val + 2 * g) = i :=
        (atPos_eq_iff hk i (by dsimp only [n0]; omega)).mpr (by dsimp only [n0]; omega)
      have hne : atPos hk ((n0.val + 2 * g) % (3 * g)) ≠ i := by
        have hml := Nat.mod_lt (n0.val + 2 * g) (show 0 < 3 * g by omega)
        rw [ne_eq, atPos_eq_iff hk i (by omega)]
        omega
      dsimp only [coeff]
      rw [ite_eq_right_iff.mpr (fun h => absurd h hn0_ge)]
      rw [ite_eq_right_iff.mpr (fun h => absurd h hn0_ge)]
      simp only [slotVec, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hpos, ite_true]
      simp [hne]; rfl
    · intro n _ hne
      have hnlt : n.val < k - 2 * g := n.isLt
      split_ifs with hlt
      · simp only [slotVec, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        have h1 : atPos hk n.val ≠ i := by rw [ne_eq, atPos_eq_iff hk i (by omega)]; omega
        have h2 : atPos hk (n.val + g) ≠ i := by rw [ne_eq, atPos_eq_iff hk i (by omega)]; omega
        have h3' : atPos hk (n.val + 2 * g) ≠ i := by rw [ne_eq, atPos_eq_iff hk i (by omega)]; omega
        simp [h1, h2, h3']
      · simp only [slotVec, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        have h1 : atPos hk (n.val + 2 * g) ≠ i := by
          rw [ne_eq, atPos_eq_iff hk i (by omega)]
          intro h; apply hne; apply Fin.ext; dsimp only [n0]; omega
        have h2 : atPos hk ((n.val + 2 * g) % (3 * g)) ≠ i := by
          have hml := Nat.mod_lt (n.val + 2 * g) (show 0 < 3 * g by omega)
          rw [ne_eq, atPos_eq_iff hk i (by omega)]; omega
        simp [h1, h2]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hilt : i.val < 3 * g := by omega
    let r := i.val % g
    let c := i.val / g
    have hr : r < g := Nat.mod_lt i.val hg_pos
    have hc : c < 3 := by dsimp only [c]; rcases hg12 with rfl | rfl <;> omega
    have hi_eq : i.val = r + c * g := by
      have hdiv := Nat.mod_add_div i.val g
      dsimp only [r, c]
      rw [Nat.mul_comm] at hdiv
      omega
    let nr : Fin (k - 2 * g) := ⟨r, by omega⟩
    let Sbig : Finset (Fin (k - 2 * g)) :=
      Finset.univ.filter (fun n : Fin (k - 2 * g) => g ≤ n.val ∧ (n.val + 2 * g) % (3 * g) = i.val)
    have hsplit_sum :
        (∑ n : Fin (k - 2 * g), coeff n * slotVec hk (basisSlots n) i) =
        coeff nr * slotVec hk (basisSlots nr) i +
        ∑ n ∈ Sbig, coeff n * slotVec hk (basisSlots n) i := by
      have hdisj : nr ∉ Sbig := by
        simp only [Sbig, Finset.mem_filter, Finset.mem_univ, true_and, nr]
        omega
      rw [← Finset.sum_insert (f := fun n => coeff n * slotVec hk (basisSlots n) i) hdisj]
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro n _ hnot
      have hnlt : n.val < k - 2 * g := n.isLt
      simp only [Finset.mem_insert, Sbig, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hnot
      dsimp only [basisSlots]
      split_ifs with hlt
      · have hnr : n.val ≠ r := fun h => hnot.1 (Fin.ext h)
        simp only [slotVec, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        have h1 : atPos hk n.val ≠ i := by
          rw [ne_eq, atPos_eq_iff hk i (by omega)]; rcases hg12 with rfl | rfl <;> omega
        have h2 : atPos hk (n.val + g) ≠ i := by
          rw [ne_eq, atPos_eq_iff hk i (by omega)]; rcases hg12 with rfl | rfl <;> omega
        have h3' : atPos hk (n.val + 2 * g) ≠ i := by
          rw [ne_eq, atPos_eq_iff hk i (by omega)]; rcases hg12 with rfl | rfl <;> omega
        simp [h1, h2, h3']
      · have hnm : (n.val + 2 * g) % (3 * g) ≠ i.val := fun h => hnot.2 ⟨by omega, h⟩
        simp only [slotVec, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        have h1 : atPos hk (n.val + 2 * g) ≠ i := by rw [ne_eq, atPos_eq_iff hk i (by omega)]; omega
        have h2 : atPos hk ((n.val + 2 * g) % (3 * g)) ≠ i := by
          have := Nat.mod_lt (n.val + 2 * g) (show 0 < 3 * g by omega)
          rw [ne_eq, atPos_eq_iff hk i (by omega)]; omega
        simp [h1, h2]
    change y i = ∑ n : Fin (k - 2 * g), coeff n * slotVec hk (basisSlots n) i
    rw [hsplit_sum]
    have hnr_slot : slotVec hk (basisSlots nr) i = 1 := by
      dsimp only [basisSlots, nr]
      rw [ite_eq_left_iff.mpr (fun h => absurd hr h)]
      simp only [slotVec, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have hc_cases : c = 0 ∨ c = 1 ∨ c = 2 := by generalize hc_var : c = c0 at hc ⊢; omega
      rcases hc_cases with hc0 | hc1 | hc2
      · have hi0 : i.val = r := by rw [hi_eq, hc0]; ring
        have h1 : atPos hk r = i := (atPos_eq_iff hk i (by omega)).mpr hi0
        have h2 : atPos hk (r + g) ≠ i := by rw [ne_eq, atPos_eq_iff hk i (by omega)]; omega
        have h3' : atPos hk (r + 2 * g) ≠ i := by rw [ne_eq, atPos_eq_iff hk i (by omega)]; omega
        simp [h1, h2, h3']
      · have hi1 : i.val = r + g := by rw [hi_eq, hc1]; ring
        have h1 : atPos hk r ≠ i := by rw [ne_eq, atPos_eq_iff hk i (by omega)]; omega
        have h2 : atPos hk (r + g) = i := (atPos_eq_iff hk i (by omega)).mpr hi1
        have h3' : atPos hk (r + 2 * g) ≠ i := by rw [ne_eq, atPos_eq_iff hk i (by omega)]; omega
        simp [h1, h2, h3']
      · have hi2 : i.val = r + 2 * g := by rw [hi_eq, hc2]
        have h1 : atPos hk r ≠ i := by rw [ne_eq, atPos_eq_iff hk i (by omega)]; omega
        have h2 : atPos hk (r + g) ≠ i := by rw [ne_eq, atPos_eq_iff hk i (by omega)]; omega
        have h3' : atPos hk (r + 2 * g) = i := (atPos_eq_iff hk i (by omega)).mpr hi2
        simp [h1, h2, h3']
    have hnr_coeff : coeff nr = ∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val % (3 * g) = i.val), y j := by
      dsimp only [coeff, nr]
      rw [ite_eq_left_iff.mpr (fun h => absurd hr h)]
      have h0 := mix_class_sum_eq_aux hk h3 hs hg_def v r hr 0 (by omega)
      have hc' := mix_class_sum_eq_aux hk h3 hs hg_def v r hr c hc
      simp only [zero_mul, add_zero] at h0
      rw [← hi_eq] at hc'
      exact h0.trans hc'.symm
    have hbig_sum : (∑ n ∈ Sbig, coeff n * slotVec hk (basisSlots n) i) =
        ∑ j ∈ (Finset.univ.filter (fun j : Fin k => j.val % (3 * g) = i.val)).erase i, y j := by
      apply Finset.sum_bij (fun n _ => atPos hk (n.val + 2 * g))
      · intro n hn
        simp only [Sbig, Finset.mem_filter, Finset.mem_univ, true_and] at hn
        simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
        have hnlt := n.isLt
        have hval : (atPos hk (n.val + 2 * g)).val = n.val + 2 * g := atPos_val_of_lt hk (by omega)
        refine ⟨?_, ?_⟩
        · intro heq; have := congrArg Fin.val heq; omega
        · rw [hval]; exact hn.2
      · intro n1 _ n2 _ heq
        have hv := congrArg Fin.val heq
        have h1 := n1.isLt; have h2 := n2.isLt
        rw [atPos_val_of_lt hk (by omega), atPos_val_of_lt hk (by omega)] at hv
        exact Fin.ext (by omega)
      · intro j hj
        simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have hjge : 3 * g ≤ j.val := by
          by_contra hlt'
          have : j.val = i.val := by rw [← hj.2, Nat.mod_eq_of_lt (by omega)]
          exact hj.1 (Fin.ext this)
        refine ⟨⟨j.val - 2 * g, by omega⟩, ?_, ?_⟩
        · simp only [Sbig, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨by omega, ?_⟩
          have : j.val - 2 * g + 2 * g = j.val := by omega
          rw [this]; exact hj.2
        · exact (atPos_eq_iff hk j (by dsimp only; omega)).mpr (by dsimp only; omega)
      · intro n hn
        simp only [Sbig, Finset.mem_filter, Finset.mem_univ, true_and] at hn
        have hnge : ¬ n.val < g := by omega
        dsimp only [coeff, basisSlots]
        rw [ite_eq_right_iff.mpr (fun h => absurd h hnge)]
        rw [ite_eq_right_iff.mpr (fun h => absurd h hnge)]
        simp only [slotVec, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        have hnlt := n.isLt
        have h1 : atPos hk (n.val + 2 * g) ≠ i := by rw [ne_eq, atPos_eq_iff hk i (by omega)]; omega
        have h2 : atPos hk ((n.val + 2 * g) % (3 * g)) = i :=
          (atPos_eq_iff hk i (by omega)).mpr hn.2.symm
        simp [h1, h2]
    rw [hnr_slot, mul_one, hnr_coeff, hbig_sum]
    have hi_mem : i ∈ Finset.univ.filter (fun j : Fin k => j.val % (3 * g) = i.val) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.mod_eq_of_lt hilt]
    rw [← Finset.add_sum_erase _ y hi_mem, add_assoc, zmod2_add_self, add_zero]

end PEqualNP.Outside.L_meta_25579

theorem PEqualNP.Outside.L_meta_25579 : ∀ (k : Nat) (hk : 0 < k), 3 ∣ k →
  let atPos := fun (i : Nat) => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
  let word := Fin k → ZMod 2
  ∀ (p : word),
    let project := fun (v : word) (i : Fin k) =>
      ∑ t : Fin k, p t * v (atPos (i.val + k - t.val))
    (∀ v : word, project (project v) = project v) →
    ∀ (s : Nat), (s = 1 ∨ s = 2) →
    let mix := fun (v : word) (i : Fin k) =>
      v i + v (atPos (i.val + s)) + v (atPos (i.val + k - s % k))
    let output := fun (v : word) (i : Fin k) =>
      let y := mix v
      y i + (1 + y (atPos (i.val + 1))) * y (atPos (i.val + 2))
    let g := Nat.gcd k s
    let basisSlots := fun (n : Fin (k - 2 * g)) =>
      if n.val < g then [n.val, n.val + g, n.val + 2 * g]
      else [n.val + 2 * g, (n.val + 2 * g) % (3 * g)]
    ∀ x mask : word,
      (∀ a b : word,
        let u := project a
        let v := b + project b
        (∑ j : Fin k, mask j *
          (output x j + output (x + u) j + output (x + v) j +
            output (x + u + v) j)) = 0) ↔
      let entry := fun (rowSite colSite : Nat) =>
        mask (atPos rowSite) * p (atPos (rowSite + k - colSite)) +
          mask (atPos colSite) * p (atPos (colSite + k - rowSite))
      ∀ a b : Fin (k - 2 * g), a.val < b.val →
        ((basisSlots a).map (fun site => ((basisSlots b).map (entry site)).sum)).sum = 0 := by
  intro k hk h3 atPos word p project hp s hs mix output g basisSlots x mask
  have hpol_eq :
      (∀ a b : word,
        let u := project a
        let v := b + project b
        (∑ j : Fin k, mask j *
          (output x j + output (x + u) j + output (x + v) j +
            output (x + u + v) j)) = 0) ↔
      (∀ a b : word,
        let U := PEqualNP.Outside.L_meta_25579.mixOp hk s (PEqualNP.Outside.L_meta_25579.proj hk p a)
        let V := PEqualNP.Outside.L_meta_25579.mixOp hk s (b + PEqualNP.Outside.L_meta_25579.proj hk p b)
        (∑ j : Fin k, mask j *
          (U (PEqualNP.Outside.L_meta_25579.atPos hk (j.val + 1)) * V (PEqualNP.Outside.L_meta_25579.atPos hk (j.val + 2)) +
           V (PEqualNP.Outside.L_meta_25579.atPos hk (j.val + 1)) * U (PEqualNP.Outside.L_meta_25579.atPos hk (j.val + 2)))) = 0) := by
    constructor <;> intro h a b <;>
    · have h0 := h a b
      have hcongr : ∀ j : Fin k,
          output x j + output (x + project a) j + output (x + (b + project b)) j +
            output (x + project a + (b + project b)) j =
          PEqualNP.Outside.L_meta_25579.mixOp hk s (PEqualNP.Outside.L_meta_25579.proj hk p a)
            (PEqualNP.Outside.L_meta_25579.atPos hk (j.val + 1)) *
          PEqualNP.Outside.L_meta_25579.mixOp hk s (b + PEqualNP.Outside.L_meta_25579.proj hk p b)
            (PEqualNP.Outside.L_meta_25579.atPos hk (j.val + 2)) +
          PEqualNP.Outside.L_meta_25579.mixOp hk s (b + PEqualNP.Outside.L_meta_25579.proj hk p b)
            (PEqualNP.Outside.L_meta_25579.atPos hk (j.val + 1)) *
          PEqualNP.Outside.L_meta_25579.mixOp hk s (PEqualNP.Outside.L_meta_25579.proj hk p a)
            (PEqualNP.Outside.L_meta_25579.atPos hk (j.val + 2)) :=
        fun j => PEqualNP.Outside.L_meta_25579.polarize_output hk s x (project a) (b + project b) j
      simpa only [hcongr] using h0
  rw [hpol_eq,
      PEqualNP.Outside.L_meta_25579.polarized_iff_orth hk p hp s mask,
      PEqualNP.Outside.L_meta_25579.orth_iff_symForm hk p hp s mask]
  have hinfo := PEqualNP.Outside.L_meta_25579.gcd_s_info hk h3 hs
  have h3g_le : 3 * g ≤ k := by
    rcases hinfo with ⟨hg, hk3, _⟩ | ⟨_, hg, _, hk6, _⟩ <;> dsimp only [g] <;> omega
  have hlt_slots : ∀ n : Fin (k - 2 * g), ∀ site ∈ basisSlots n, site < k := by
    intro n site hs'
    dsimp only [basisSlots] at hs'
    split_ifs at hs' with hlt
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs'
      rcases hs' with rfl | rfl | rfl <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs'
      rcases hs' with rfl | rfl
      · have := n.isLt; omega
      · have := Nat.mod_lt (n.val + 2 * g) (show 0 < 3 * g by have := Nat.gcd_pos_of_pos_left s hk; omega)
        omega
  have hbasis_eval : ∀ a b : Fin (k - 2 * g),
      PEqualNP.Outside.L_meta_25579.symForm hk p mask
        (PEqualNP.Outside.L_meta_25579.slotVec hk (basisSlots a))
        (PEqualNP.Outside.L_meta_25579.slotVec hk (basisSlots b)) =
      ((basisSlots a).map (fun site => ((basisSlots b).map (fun colSite =>
        mask (atPos site) * p (atPos (site + k - colSite)) +
        mask (atPos colSite) * p (atPos (colSite + k - site)))).sum)).sum := by
    intro a b
    exact PEqualNP.Outside.L_meta_25579.symForm_slotVec hk p mask (basisSlots a) (basisSlots b)
      (hlt_slots a) (hlt_slots b)
  constructor
  · intro hsym entry a b _
    rw [← hbasis_eval a b]
    obtain ⟨va, hva⟩ := PEqualNP.Outside.L_meta_25579.basis_in_image_aux hk h3 hs rfl a.val a.isLt
    obtain ⟨vb, hvb⟩ := PEqualNP.Outside.L_meta_25579.basis_in_image_aux hk h3 hs rfl b.val b.isLt
    rw [← hva, ← hvb]
    exact hsym va vb
  · intro htri a b
    dsimp only at htri
    have hall : ∀ i j : Fin (k - 2 * g),
        PEqualNP.Outside.L_meta_25579.symForm hk p mask
          (PEqualNP.Outside.L_meta_25579.slotVec hk (basisSlots i))
          (PEqualNP.Outside.L_meta_25579.slotVec hk (basisSlots j)) = 0 := by
      intro i j
      rcases lt_trichotomy i.val j.val with hlt | heq | hgt
      · rw [hbasis_eval]; exact htri i j hlt
      · have : i = j := Fin.ext heq
        subst this
        exact PEqualNP.Outside.L_meta_25579.symForm_self hk p mask _
      · rw [PEqualNP.Outside.L_meta_25579.symForm_comm, hbasis_eval]
        exact htri j i hgt
    obtain ⟨ca, hca⟩ := PEqualNP.Outside.L_meta_25579.expand_in_basis_aux hk h3 hs rfl a
    obtain ⟨cb, hcb⟩ := PEqualNP.Outside.L_meta_25579.expand_in_basis_aux hk h3 hs rfl b
    rw [hca, hcb, PEqualNP.Outside.L_meta_25579.symForm_sum_left]
    apply Finset.sum_eq_zero
    intro i _
    rw [PEqualNP.Outside.L_meta_25579.symForm_smul_left, PEqualNP.Outside.L_meta_25579.symForm_sum_right]
    have hinner : (∑ j : Fin (k - 2 * g),
        PEqualNP.Outside.L_meta_25579.symForm hk p mask
          (PEqualNP.Outside.L_meta_25579.slotVec hk (basisSlots i))
          (fun t => cb j * PEqualNP.Outside.L_meta_25579.slotVec hk (basisSlots j) t)) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [PEqualNP.Outside.L_meta_25579.symForm_comm, PEqualNP.Outside.L_meta_25579.symForm_smul_left,
          PEqualNP.Outside.L_meta_25579.symForm_comm, hall i j, mul_zero]
    rw [hinner, mul_zero]
