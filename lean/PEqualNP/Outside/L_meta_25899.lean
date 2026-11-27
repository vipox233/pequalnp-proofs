import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25899

def sg (f : ZMod 2) : ℤ := if f = 0 then 1 else -1

theorem sg_add (a b : ZMod 2) : sg (a + b) = sg a * sg b := by
  revert a b; decide

theorem sg_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    sg (∑ i ∈ s, f i) = ∏ i ∈ s, sg (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sg]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sg_add, ih]

theorem char_sum (k : ℕ) (a target : Fin k → ZMod 2) (test : Finset (Fin k)) :
    ∑ x : Fin k → ZMod 2, (if ∀ j ∈ test, x j = target j then sg (a ⬝ᵥ x) else 0) =
      if ∀ j, j ∉ test → a j = 0 then (2 : ℤ) ^ (k - test.card) * sg (a ⬝ᵥ target) else 0 := by
  classical
  have h1 : ∀ x : Fin k → ZMod 2, (if ∀ j ∈ test, x j = target j then sg (a ⬝ᵥ x) else 0) =
      ∏ j, (if (j ∈ test → x j = target j) then sg (a j * x j) else 0) := by
    intro x
    rw [Fintype.prod_ite_zero, dotProduct, sg_sum]
    congr
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun j (y : ZMod 2) => if (j ∈ test → y = target j) then sg (a j * y) else 0)]
  by_cases h : ∀ j, j ∉ test → a j = 0
  · rw [if_pos h]
    have h2 : ∀ j, (∑ y : ZMod 2, if (j ∈ test → y = target j) then sg (a j * y) else 0) =
        (if j ∈ test then 1 else 2) * sg (a j * target j) := by
      intro j
      by_cases hj : j ∈ test
      · simp [hj]
      · simp [hj, h j hj, sg]
    simp_rw [h2]
    rw [Finset.prod_mul_distrib, dotProduct, sg_sum, Finset.prod_ite, Finset.prod_const_one,
      Finset.prod_const, one_mul]
    congr 2
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (by simp)]
    simp
  · rw [if_neg h]
    push_neg at h
    obtain ⟨j, hj, haj⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    have : a j = 1 := by
      revert haj; generalize a j = z; revert z; decide
    simp only [hj, this, one_mul, false_imp_iff, if_true]
    decide

theorem char_sum_S (k r : ℕ) (x : Fin r → Fin k → ZMod 2) :
    ∑ b : Fin r → Fin k → ZMod 2, sg (∑ t, b t ⬝ᵥ x t) =
      if x = 0 then (2 : ℤ) ^ (k * r) else 0 := by
  classical
  simp_rw [sg_sum]
  rw [← Fintype.prod_sum (fun t (y : Fin k → ZMod 2) => sg (y ⬝ᵥ x t))]
  have h : ∀ t, ∑ y : Fin k → ZMod 2, sg (y ⬝ᵥ x t) = if x t = 0 then (2 : ℤ) ^ k else 0 := by
    intro t
    have := char_sum k (x t) 0 ∅
    simp only [Finset.notMem_empty, false_imp_iff, implies_true, if_true, Finset.card_empty,
      Nat.sub_zero, dotProduct_zero, forall_true_left] at this
    simp_rw [dotProduct_comm _ (x t)]
    rw [this]
    simp [sg, funext_iff]
  simp_rw [h]
  rw [Fintype.prod_ite_zero]
  simp [funext_iff, pow_mul]

theorem inversion (k r : ℕ) (hits score : (Fin r → Fin k → ZMod 2) → ℤ)
    (h1 : ∀ b, ∑ c, hits c * sg (∑ t, b t ⬝ᵥ c t) = score b) (c : Fin r → Fin k → ZMod 2) :
    (2 : ℤ) ^ (k * r) * hits c = ∑ b, score b * sg (∑ t, b t ⬝ᵥ c t) := by
  classical
  simp_rw [← h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h2 : ∀ c', ∑ b : Fin r → Fin k → ZMod 2,
      hits c' * sg (∑ t, b t ⬝ᵥ c' t) * sg (∑ t, b t ⬝ᵥ c t) =
      hits c' * if c' + c = 0 then (2 : ℤ) ^ (k * r) else 0 := by
    intro c'
    rw [← char_sum_S, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_assoc, ← sg_add, ← Finset.sum_add_distrib]
    simp [dotProduct_add]
  have h3 : ∀ c' : Fin r → Fin k → ZMod 2, c' + c = 0 ↔ c' = c := by
    intro c'
    constructor
    · intro h
      funext t j
      have := congrFun (congrFun h t) j
      exact CharTwo.add_eq_zero.mp this
    · rintro rfl
      funext t j
      exact CharTwo.add_self_eq_zero _
  simp_rw [h2, h3]
  simp [mul_comm]

theorem foldl_take_succ {α : Type*} (r : ℕ) (f : α → Fin r → α) (a : α) (t : Fin r) :
    ((List.finRange r).take (t.val + 1)).foldl f a =
      f (((List.finRange r).take t.val).foldl f a) t := by
  rw [List.take_succ]
  simp

theorem core (k r s : ℕ) (L ρ0 : (Fin k → ZMod 2) → (Fin k → ZMod 2))
    (ρ : ℕ → (Fin k → ZMod 2) → (Fin k → ZMod 2))
    (hρ0 : ∀ a b, ρ0 (a + b) = ρ0 a + ρ0 b) (hρ : ∀ n a b, ρ n (a + b) = ρ n a + ρ n b)
    (raw : Fin k → ZMod 2) (delta : Fin s → Fin k → ZMod 2)
    (path : Fin (r + 1) → Fin s → Fin k → ZMod 2) (test : Finset (Fin k))
    (target : Fin k → ZMod 2)
    (st : (Fin k → ZMod 2) × (Fin r → Fin k → ZMod 2) → (Fin k → ZMod 2) → Fin (r + 1) →
      (Fin k → ZMod 2))
    (h0 : ∀ d key, st d key 0 = ρ0 key + d.1)
    (hs : ∀ d key (t : Fin r),
      st d key t.succ = L (st d key t.castSucc) + ρ t.val key + d.2 t)
    (b : Fin r → Fin k → ZMod 2) :
    ∑ c : Fin r → Fin k → ZMod 2,
      (((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun name =>
        (∀ t p, st (name, c) (raw + delta p) t - st (name, c) raw t = path t p) ∧
        (∀ j ∈ test, st (name, c) raw (Fin.last r) j = target j))).card : ℤ) *
        sg (∑ t : Fin r, b t ⬝ᵥ c t) =
    if (∀ p, path 0 p = ρ0 (delta p)) ∧
        (∀ j : Fin k, j ∉ test → (∑ t : Fin r, (if t.val + 1 = r then b t else 0)) j = 0) then
      (2 : ℤ) ^ (k - test.card) *
        sg ((∑ t : Fin r, (if t.val + 1 = r then b t else 0)) ⬝ᵥ target) *
        (∏ t : Fin r, (∑ v ∈ (Finset.univ : Finset (Fin k → ZMod 2)).filter (fun v => ∀ p : Fin s,
          L (v + path t.castSucc p) - L v + ρ t.val (delta p) = path t.succ p),
          sg ((∑ t' : Fin r, (if t'.val + 1 = t.val then b t' else 0)) ⬝ᵥ v +
            b t ⬝ᵥ (L v + ρ t.val raw))))
    else 0 := by
  classical
  have sub_add : ∀ x y : Fin k → ZMod 2, x - y = x + y := by
    intro x y; funext j; exact CharTwo.sub_eq_add _ _
  have hD : ∀ d, (∀ t p, st d (raw + delta p) t - st d raw t = path t p) ↔
      (∀ p, path 0 p = ρ0 (delta p)) ∧ ∀ t : Fin r, ∀ p,
        L (st d raw t.castSucc + path t.castSucc p) - L (st d raw t.castSucc) +
          ρ t.val (delta p) = path t.succ p := by
    intro d
    constructor
    · intro h
      refine ⟨fun p => ?_, fun t p => ?_⟩
      · have := h 0 p
        rw [h0, h0, hρ0] at this
        rw [← this]; abel
      · have h1 := h t.succ p
        have h2 := h t.castSucc p
        rw [hs, hs, hρ] at h1
        have h3 : st d (raw + delta p) t.castSucc = st d raw t.castSucc + path t.castSucc p := by
          rw [← h2]; abel
        rw [h3] at h1
        rw [← h1]; abel
    · rintro ⟨hv, hl⟩ t p
      induction t using Fin.induction with
      | zero => rw [h0, h0, hρ0, hv p]; abel
      | succ t ih =>
        have h3 : st d (raw + delta p) t.castSucc = st d raw t.castSucc + path t.castSucc p := by
          rw [← ih]; abel
        rw [hs, hs, hρ, h3, ← hl t p]; abel
  have hc : ∀ (d : (Fin k → ZMod 2) × (Fin r → Fin k → ZMod 2)) (t : Fin r),
      d.2 t = st d raw t.succ - L (st d raw t.castSucc) - ρ t.val raw := by
    intro d t; rw [hs]; abel
  let e : (Fin k → ZMod 2) × (Fin r → Fin k → ZMod 2) ≃ (Fin (r + 1) → Fin k → ZMod 2) :=
    { toFun := fun d t => st d raw t
      invFun := fun v => (v 0 - ρ0 raw, fun t => v t.succ - L (v t.castSucc) - ρ t.val raw)
      left_inv := by
        rintro ⟨name, c⟩
        refine Prod.ext ?_ ?_
        · show st (name, c) raw 0 - ρ0 raw = name
          rw [h0]; abel
        · funext t
          show st (name, c) raw t.succ - L (st (name, c) raw t.castSucc) - ρ t.val raw = c t
          rw [hs]; abel
      right_inv := by
        intro v
        funext t
        induction t using Fin.induction with
        | zero => show st _ raw 0 = v 0; rw [h0]; dsimp only; abel
        | succ t ih =>
          show st _ raw t.succ = v t.succ
          rw [hs]
          have ih' : st (v 0 - ρ0 raw, fun t => v t.succ - L (v t.castSucc) - ρ t.val raw) raw
              t.castSucc = v t.castSucc := ih
          rw [ih']; dsimp only; abel }
  let pv : ℕ → Fin k → ZMod 2 := fun j => ∑ t' : Fin r, if t'.val + 1 = j then b t' else 0
  have pv0 : pv 0 = 0 := by simp [pv]
  have pvs : ∀ t : Fin r, pv (t.val + 1) = b t := by
    intro t; simp [pv, Fin.val_inj]
  let Gf : (Fin (r + 1) → Fin k → ZMod 2) → ℤ := fun v =>
    if (∀ p, path 0 p = ρ0 (delta p)) ∧ (∀ t : Fin r, ∀ p,
        L (v t.castSucc + path t.castSucc p) - L (v t.castSucc) + ρ t.val (delta p) =
          path t.succ p) ∧ (∀ j ∈ test, v (Fin.last r) j = target j) then
      sg (∑ t : Fin r, b t ⬝ᵥ (v t.succ - L (v t.castSucc) - ρ t.val raw)) else 0
  have step1 : ∑ c : Fin r → Fin k → ZMod 2,
      (((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun name =>
        (∀ t p, st (name, c) (raw + delta p) t - st (name, c) raw t = path t p) ∧
        (∀ j ∈ test, st (name, c) raw (Fin.last r) j = target j))).card : ℤ) *
        sg (∑ t : Fin r, b t ⬝ᵥ c t) = ∑ v, Gf v := by
    rw [← Equiv.sum_comp e Gf]
    simp only [Finset.natCast_card_filter, Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun name _ => Finset.sum_congr rfl fun c _ => ?_
    show _ = if _ ∧ (∀ t : Fin r, ∀ p,
        L (st (name, c) raw t.castSucc + path t.castSucc p) - L (st (name, c) raw t.castSucc) +
          ρ t.val (delta p) = path t.succ p) ∧ (∀ j ∈ test, st (name, c) raw (Fin.last r) j = target j) then
      sg (∑ t : Fin r, b t ⬝ᵥ (st (name, c) raw t.succ - L (st (name, c) raw t.castSucc) - ρ t.val raw)) else 0
    simp only [hD (name, c), and_assoc]
    refine if_congr Iff.rfl (congrArg sg (Finset.sum_congr rfl fun t _ => ?_)) rfl
    rw [← hc (name, c) t]
  rw [step1]
  by_cases hV : ∀ p, path 0 p = ρ0 (delta p)
  swap
  · simp [Gf, hV]
  let G : Fin (r + 1) → (Fin k → ZMod 2) → ℤ := fun u =>
    Fin.lastCases (motive := fun _ => (Fin k → ZMod 2) → ℤ)
      (fun x => if ∀ j ∈ test, x j = target j then sg (pv r ⬝ᵥ x) else 0)
      (fun t x => if (∀ p, L (x + path t.castSucc p) - L x + ρ t.val (delta p) = path t.succ p)
        then sg (pv t.val ⬝ᵥ x + b t ⬝ᵥ (L x + ρ t.val raw)) else 0) u
  have hG : ∀ v, Gf v = ∏ u, G u (v u) := by
    intro v
    rw [Fin.prod_univ_castSucc]
    simp only [G, Gf, Fin.lastCases_last, Fin.lastCases_castSucc]
    rw [Fintype.prod_ite_zero]
    by_cases hQ : ∀ t : Fin r, ∀ p, L (v t.castSucc + path t.castSucc p) - L (v t.castSucc) +
        ρ t.val (delta p) = path t.succ p
    swap
    · simp [hQ]
    by_cases hT : ∀ j ∈ test, v (Fin.last r) j = target j
    swap
    · simp [hT]
    rw [if_pos ⟨hV, hQ, hT⟩, if_pos hQ, if_pos hT]
    have hH : ∏ u : Fin (r + 1), sg (pv u.val ⬝ᵥ v u) = ∏ t : Fin r, sg (b t ⬝ᵥ v t.succ) := by
      rw [Fin.prod_univ_succ]
      simp [pv0, pvs, sg]
    have hH2 := Fin.prod_univ_castSucc (fun u : Fin (r + 1) => sg (pv u.val ⬝ᵥ v u))
    simp only [Fin.val_castSucc, Fin.val_last] at hH2
    rw [sg_sum]
    simp only [sub_add, dotProduct_add, sg_add, Finset.prod_mul_distrib]
    rw [← hH, hH2]
    ring
  simp_rw [hG]
  rw [← Fintype.prod_sum G, Fin.prod_univ_castSucc]
  simp only [G, Fin.lastCases_last, Fin.lastCases_castSucc]
  rw [char_sum]
  simp only [Finset.sum_filter, pv]
  by_cases hC : ∀ j, j ∉ test → (∑ t : Fin r, if t.val + 1 = r then b t else 0) j = 0
  · rw [if_pos hC, if_pos ⟨hV, hC⟩]; ring
  · rw [if_neg hC, if_neg (fun h => hC h.2)]; ring

end PEqualNP.Outside.L_meta_25899

theorem PEqualNP.Outside.L_meta_25899 : ∀ (k r s : Nat) (hk : 0 < k),
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
    let S := Fin r → W
    let valid := ∀ p, path 0 p = rot initial (delta p)
    let localSet := fun (t : Fin r) => (Finset.univ : Finset W).filter (fun v => ∀ p : Fin s,
      layer gap (v+path t.castSucc p) - layer gap v + rot (inject t.val) (delta p) = path t.succ p)
    let hits := fun (c : S) => ((Finset.univ : Finset W).filter (fun name =>
      (∀ t p, state (name,c) (raw+delta p) t - state (name,c) raw t = path t p) ∧
      (∀ j ∈ test, state (name,c) raw (Fin.last r) j = target j))).card
    let prev := fun (b : S) (j : Nat) => ∑ t : Fin r, (if t.val+1 = j then b t else 0)
    let pairing := fun (b c : S) => ∑ t : Fin r, dotProduct (b t) (c t)
    let phase := fun (b : S) (t : Fin r) (v : W) => dotProduct (prev b t.val) v +
      dotProduct (b t) (layer gap v + rot (inject t.val) raw)
    let sign := fun f : F => if f = 0 then (1 : ℤ) else -1
    let score := fun b : S =>
      if valid ∧ (∀ j : Fin k, j ∉ test → prev b r j = 0) then
        (2 : ℤ)^(k-test.card) * sign (dotProduct (prev b r) target) *
          (∏ t : Fin r, (∑ v ∈ localSet t, sign (phase b t v)))
      else 0
    (∀ b : S, (∑ c : S, (hits c : ℤ) * sign (pairing b c)) = score b) ∧
    (∀ c : S, (2 : ℤ)^(k*r) * (hits c : ℤ) = ∑ b : S, score b * sign (pairing b c)) := by
  intro k r s hk F W ix rot layer col raw delta path test target initial gap inject state S
    valid localSet hits prev pairing phase sign score
  have h1 : ∀ b : S, (∑ c : S, (hits c : ℤ) * sign (pairing b c)) = score b := by
    intro b
    exact PEqualNP.Outside.L_meta_25899.core k r s (layer gap) (rot initial)
      (fun n => rot (inject n)) (fun _ _ => rfl) (fun _ _ _ => rfl) raw delta path test target
      (fun d key t => state d key t) (fun _ _ => rfl)
      (fun d key t => PEqualNP.Outside.L_meta_25899.foldl_take_succ r _ _ t) b
  exact ⟨h1, fun c => PEqualNP.Outside.L_meta_25899.inversion k r (fun c => (hits c : ℤ)) score h1 c⟩
