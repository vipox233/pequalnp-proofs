import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25897

open Finset

def st {k r : ℕ} (L : (Fin k → ZMod 2) → (Fin k → ZMod 2)) (K0 : (Fin k → ZMod 2) → (Fin k → ZMod 2))
    (K : ℕ → (Fin k → ZMod 2) → (Fin k → ZMod 2))
    (data : (Fin k → ZMod 2) × (Fin r → (Fin k → ZMod 2))) (key : Fin k → ZMod 2) (time : Fin (r+1)) :
    Fin k → ZMod 2 :=
  ((List.finRange r).take time.val).foldl (fun v tick =>
    L v + K tick.val key + data.2 tick) (K0 key + data.1)

lemma st_zero {k r : ℕ} (L K0 : (Fin k → ZMod 2) → (Fin k → ZMod 2))
    (K : ℕ → (Fin k → ZMod 2) → (Fin k → ZMod 2))
    (data : (Fin k → ZMod 2) × (Fin r → (Fin k → ZMod 2))) (key : Fin k → ZMod 2) :
    st L K0 K data key 0 = K0 key + data.1 := by
  simp [st]

lemma st_succ {k r : ℕ} (L K0 : (Fin k → ZMod 2) → (Fin k → ZMod 2))
    (K : ℕ → (Fin k → ZMod 2) → (Fin k → ZMod 2))
    (data : (Fin k → ZMod 2) × (Fin r → (Fin k → ZMod 2))) (key : Fin k → ZMod 2) (t : Fin r) :
    st L K0 K data key t.succ = L (st L K0 K data key t.castSucc) + K t.val key + data.2 t := by
  simp only [st, Fin.val_succ, Fin.val_castSucc]
  rw [List.take_add_one, List.foldl_append]
  have h : (List.finRange r)[t.val]? = some t := by
    rw [List.getElem?_eq_getElem (by simp)]
    simp
  rw [h]
  rfl

lemma card_test (k : ℕ) (test : Finset (Fin k)) (target : Fin k → ZMod 2) :
    ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun w => ∀ j ∈ test, w j = target j)).card
      = 2 ^ (k - test.card) := by
  classical
  have h : ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun w => ∀ j ∈ test, w j = target j)) =
      Fintype.piFinset (fun j => if j ∈ test then {target j} else Finset.univ) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hw j
      split_ifs with hj
      · simp [hw j hj]
      · simp
    · intro hw j hj
      have := hw j
      simp only [hj, ↓reduceIte, Finset.mem_singleton] at this
      exact this
  rw [h, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, Finset.card_singleton, Finset.card_univ, ZMod.card]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  have : (Finset.univ.filter (fun j : Fin k => j ∉ test)) = testᶜ := by ext j; simp
  rw [this, Finset.card_compl, Fintype.card_fin]

theorem main (k r s : ℕ) (L K0 : (Fin k → ZMod 2) → (Fin k → ZMod 2))
    (K : ℕ → (Fin k → ZMod 2) → (Fin k → ZMod 2))
    (hK0 : ∀ x y, K0 (x + y) = K0 x + K0 y) (hK : ∀ t x y, K t (x + y) = K t x + K t y)
    (raw : Fin k → ZMod 2) (delta : Fin s → (Fin k → ZMod 2))
    (path : Fin (r+1) → Fin s → (Fin k → ZMod 2)) (test : Finset (Fin k)) (target : Fin k → ZMod 2) :
    ((Finset.univ : Finset ((Fin k → ZMod 2) × (Fin r → (Fin k → ZMod 2)))).filter (fun data =>
      (∀ t p, st L K0 K data (raw + delta p) t - st L K0 K data raw t = path t p) ∧
      (∀ j ∈ test, st L K0 K data raw (Fin.last r) j = target j))).card =
      (if (∀ p, path 0 p = K0 (delta p)) then
        2 ^ (k - test.card) * ∏ t : Fin r,
          ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun v => ∀ p : Fin s,
            L (v + path t.castSucc p) - L v + K t.val (delta p) = path t.succ p)).card else 0) := by
  classical
  -- differences
  have hD0 : ∀ (data : (Fin k → ZMod 2) × (Fin r → (Fin k → ZMod 2))) p, st L K0 K data (raw + delta p) 0 - st L K0 K data raw 0 = K0 (delta p) := by
    intro data p; rw [st_zero, st_zero, hK0]; abel
  have hDs : ∀ (data : (Fin k → ZMod 2) × (Fin r → (Fin k → ZMod 2))) p (t : Fin r), st L K0 K data (raw + delta p) t.succ - st L K0 K data raw t.succ
      = L (st L K0 K data (raw + delta p) t.castSucc) - L (st L K0 K data raw t.castSucc)
        + K t.val (delta p) := by
    intro data p t; rw [st_succ, st_succ, hK]; abel
  -- condition rewrite
  have hcond : ∀ (data : (Fin k → ZMod 2) × (Fin r → (Fin k → ZMod 2))), (∀ t p, st L K0 K data (raw + delta p) t - st L K0 K data raw t = path t p) ↔
      ((∀ p, path 0 p = K0 (delta p)) ∧ ∀ t : Fin r, ∀ p,
        L (st L K0 K data raw t.castSucc + path t.castSucc p) - L (st L K0 K data raw t.castSucc)
          + K t.val (delta p) = path t.succ p) := by
    intro data
    constructor
    · intro h
      refine ⟨fun p => by rw [← h 0 p, hD0], fun t p => ?_⟩
      rw [← h t.succ p, hDs, ← h t.castSucc p, add_sub_cancel]
    · rintro ⟨h0, hs⟩ t
      induction t using Fin.induction with
      | zero => intro p; rw [hD0, h0]
      | succ t ih =>
        intro p
        have e : st L K0 K data (raw + delta p) t.castSucc =
            st L K0 K data raw t.castSucc + path t.castSucc p := by
          rw [← ih p, add_sub_cancel]
        rw [hDs, e, hs]
  -- the bijection to state sequences
  let Φ := fun data : (Fin k → ZMod 2) × (Fin r → (Fin k → ZMod 2)) =>
    fun t : Fin (r+1) => st L K0 K data raw t
  have hinj : Function.Injective Φ := by
    intro d d' h
    have h0 := congrFun h 0
    simp only [Φ, st_zero] at h0
    have h1 : d.1 = d'.1 := add_left_cancel h0
    have h2 : d.2 = d'.2 := by
      funext t
      have hs := congrFun h t.succ
      have hc := congrFun h t.castSucc
      simp only [Φ] at hs hc
      rw [st_succ, st_succ, hc] at hs
      exact add_left_cancel hs
    exact Prod.ext h1 h2
  have hbij : Function.Bijective Φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    simp [Fintype.card_prod, pow_succ, mul_comm]
  let T := fun i : Fin (r+1) => if h : i = Fin.last r then
      (Finset.univ : Finset (Fin k → ZMod 2)).filter (fun w => ∀ j ∈ test, w j = target j)
    else (Finset.univ : Finset (Fin k → ZMod 2)).filter (fun v => ∀ p : Fin s,
      L (v + path (i.castPred h).castSucc p) - L v + K (i.castPred h).val (delta p) = path (i.castPred h).succ p)
  split_ifs with hinit
  · have hcard : ((Finset.univ : Finset ((Fin k → ZMod 2) × (Fin r → (Fin k → ZMod 2)))).filter (fun data =>
        (∀ t p, st L K0 K data (raw + delta p) t - st L K0 K data raw t = path t p) ∧
        (∀ j ∈ test, st L K0 K data raw (Fin.last r) j = target j))).card = (Fintype.piFinset T).card := by
      apply Finset.card_bij (fun d _ => Φ d)
      · intro d hd
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
        rw [hcond] at hd
        rw [Fintype.mem_piFinset]
        intro i
        by_cases hi : i = Fin.last r
        · simp only [T, hi, dite_true, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hd.2
        · simp only [T, hi, dite_false, Finset.mem_filter, Finset.mem_univ, true_and, Φ]
          intro p
          have := hd.1.2 (i.castPred hi) p
          rwa [Fin.castSucc_castPred] at this
      · intro x _ y _ h
        exact hinj h
      · intro v hv
        obtain ⟨d, hd⟩ := hbij.2 v
        refine ⟨d, ?_, hd⟩
        rw [Fintype.mem_piFinset] at hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hcond]
        refine ⟨⟨hinit, fun t p => ?_⟩, ?_⟩
        · have := hv t.castSucc
          simp only [T, Fin.castSucc_ne_last, dite_false] at this
          have h2 := (Finset.mem_filter.mp this).2 p
          simp only [Fin.castPred_castSucc] at h2
          rw [← hd] at h2
          exact h2
        · have := hv (Fin.last r)
          simp only [T, dite_true, Finset.mem_filter, Finset.mem_univ, true_and] at this
          rw [← hd] at this
          exact this
    rw [hcard, Fintype.card_piFinset, Fin.prod_univ_castSucc, mul_comm]
    congr 1
    · simp only [T, dite_true]
      exact card_test k test target
    · apply Finset.prod_congr rfl
      intro t _
      simp only [T, Fin.castSucc_ne_last, dite_false, Fin.castPred_castSucc]
      congr 1
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro d _ hd
    exact hinit ((hcond d).mp hd.1).1

end PEqualNP.Outside.L_meta_25897

theorem PEqualNP.Outside.L_meta_25897 : ∀ (k r s : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun t : Nat => (⟨t % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (amount : Nat) (x : W) (j : Fin k) => x (ix (j.val+k-amount % k))
  let layer := fun (gap : Nat) (x : W) =>
    let m := fun (j : Fin k) => x j + x (ix (j.val+gap)) + x (ix (j.val+k-gap % k))
    fun (j : Fin k) => m j + (1+m (ix (j.val+1))) * m (ix (j.val+2))
  ∀ (col : Bool) (raw : W) (delta : Fin s → W)
    (path : Fin (r+1) → Fin s → W) (test : Finset (Fin k)) (target : W),
    let initial := if col then 3 else 1
    let gap := if col then 2 else 1
    let inject := fun t : Nat => if col then 3*(t+1)+1 else 2*t
    let state := fun (data : W × (Fin r → W)) (key : W) (time : Fin (r+1)) =>
      ((List.finRange r).take time.val).foldl (fun v tick =>
        layer gap v + rot (inject tick.val) key + data.2 tick) (rot initial key + data.1)
    let weight := fun (t : Fin r) =>
      ((Finset.univ : Finset W).filter (fun v => ∀ p : Fin s,
        layer gap (v+path t.castSucc p) - layer gap v + rot (inject t.val) (delta p)
          = path t.succ p)).card
    ((Finset.univ : Finset (W × (Fin r → W))).filter (fun data =>
      (∀ t p, state data (raw+delta p) t - state data raw t = path t p) ∧
      (∀ j ∈ test, state data raw (Fin.last r) j = target j))).card =
      (if (∀ p, path 0 p = rot initial (delta p)) then
        2^(k-test.card) * ∏ t : Fin r, weight t else 0) := by
  intro k r s hk F W ix rot layer col raw delta path test target initial gap inject state weight
  exact PEqualNP.Outside.L_meta_25897.main k r s (layer gap) (rot initial)
    (fun t key => rot (inject t) key) (fun _ _ => rfl) (fun _ _ _ => rfl) raw delta path test target
