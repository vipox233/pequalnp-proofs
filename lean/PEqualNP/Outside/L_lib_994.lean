import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_994_aux

def par {a : ℕ} (S : Finset (Fin a)) (x : Fin a → Bool) : Bool :=
  decide ((S.filter (fun i => x i)).card % 2 = 1)

def sg (b : Bool) : ℤ := if b then -1 else 1

def outT {n : ℕ} (f : Fin n → Fin n) (T : Fin n → Bool → Bool) (x : Fin n → Bool) (i : Fin n) : Bool :=
  xor (x i) (T i (x (f i)))

def coef {n : ℕ} (T : Fin n → Bool → Bool) (i : Fin n) : ℤ :=
  if T i false = T i true then 0 else sg (T i false)

lemma cs_sg_xor (a b : Bool) : sg (xor a b) = sg a * sg b := by
  cases a <;> cases b <;> simp [sg]

lemma cs_sg_parity (k : ℕ) : sg (decide (k % 2 = 1)) = (-1 : ℤ) ^ k := by
  rcases Nat.even_or_odd k with h | h
  · rw [h.neg_one_pow]
    simp [sg, Nat.even_iff.mp h]
  · rw [h.neg_one_pow]
    simp [sg, Nat.odd_iff.mp h]

theorem sg_par {a : ℕ} (S : Finset (Fin a)) (x : Fin a → Bool) :
    sg (par S x) = ∏ i ∈ S, sg (x i) := by
  unfold par
  rw [cs_sg_parity]
  simp [sg, Finset.prod_ite]

lemma cs_exists_out {n : ℕ} (f : Fin n → Fin n) (S : Finset (Fin n)) (h : S.image f ≠ S) :
    ∃ s ∈ S, s ∉ S.image f := by
  by_contra hc
  push Not at hc
  exact h (Finset.eq_of_subset_of_card_le (fun s hs => hc s hs) Finset.card_image_le).symm

def cs_flip {n : ℕ} (s : Fin n) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun x j := xor (x j) (decide (j = s))
  invFun x j := xor (x j) (decide (j = s))
  left_inv x := by funext j; simp
  right_inv x := by funext j; simp

lemma cs_term_flip {n : ℕ} (f : Fin n → Fin n) (T : Fin n → Bool → Bool) (S : Finset (Fin n))
    (s : Fin n) (hs : s ∈ S) (hns : s ∉ S.image f) (x : Fin n → Bool) :
    ∏ i ∈ S, sg (outT f T (cs_flip s x) i) = - ∏ i ∈ S, sg (outT f T x i) := by
  have h1 : ∀ i ∈ S, sg (outT f T (cs_flip s x) i) =
      sg (decide (i = s)) * sg (outT f T x i) := by
    intro i hi
    have hfi : f i ≠ s := fun h => hns (Finset.mem_image.mpr ⟨i, hi, h⟩)
    have e : cs_flip s x (f i) = x (f i) := by simp [cs_flip, hfi]
    unfold outT
    rw [e]
    have e2 : cs_flip s x i = xor (x i) (decide (i = s)) := rfl
    rw [e2]
    simp only [cs_sg_xor]
    ring
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib]
  have h2 : ∏ i ∈ S, sg (decide (i = s)) = -1 := by
    simp [sg, Finset.prod_ite_eq', hs]
  rw [h2, neg_one_mul]

lemma cs_sum_zero {n : ℕ} (f : Fin n → Fin n) (T : Fin n → Bool → Bool) (S : Finset (Fin n))
    (h : S.image f ≠ S) : (∑ x : Fin n → Bool, ∏ i ∈ S, sg (outT f T x i)) = 0 := by
  obtain ⟨s, hs, hns⟩ := cs_exists_out f S h
  have := Fintype.sum_equiv (cs_flip s)
    (fun x => ∏ i ∈ S, sg (outT f T (cs_flip s x) i))
    (fun x => ∏ i ∈ S, sg (outT f T x i)) (fun x => rfl)
  simp only [cs_term_flip f T S s hs hns, Finset.sum_neg_distrib] at this
  linarith

lemma cs_reindex {n : ℕ} (f : Fin n → Fin n) (S : Finset (Fin n)) (h : S.image f = S)
    (hinj : Set.InjOn f S) (P : Fin n → ℤ) :
    ∏ i ∈ S, P (f i) = ∏ j ∈ S, P j := by
  rw [← Finset.prod_image hinj, h]

lemma cs_G (u v : Bool) :
    sg true * sg v + sg false * sg u = 2 * (if u = v then 0 else sg u) := by
  cases u <;> cases v <;> norm_num [sg]

lemma cs_term_image {n : ℕ} (f g : Fin n → Fin n) (T : Fin n → Bool → Bool) (S : Finset (Fin n))
    (h : S.image f = S) (hinj : Set.InjOn f S) (hgf : ∀ i ∈ S, g (f i) = i)
    (x : Fin n → Bool) :
    ∏ i ∈ S, sg (outT f T x i) =
      ∏ j, (if j ∈ S then sg (x j) * sg (T (g j) (x j)) else 1) := by
  rw [Finset.prod_ite_mem, Finset.univ_inter,
    ← cs_reindex f S h hinj (fun j => sg (x j) * sg (T (g j) (x j)))]
  simp only [outT, cs_sg_xor]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    cs_reindex f S h hinj (fun j => sg (x j))]
  congr 1
  exact Finset.prod_congr rfl (fun i hi => by rw [hgf i hi])

lemma cs_left_inv {n : ℕ} (f : Fin n → Fin n) (S : Finset (Fin n)) (hinj : Set.InjOn f S) :
    ∃ g : Fin n → Fin n, ∀ i ∈ S, g (f i) = i := by
  classical
  refine ⟨fun j => if hj : ∃ i ∈ S, f i = j then hj.choose else j, fun i hi => ?_⟩
  have hj : ∃ i' ∈ S, f i' = f i := ⟨i, hi, rfl⟩
  simp only [hj, dite_true]
  exact hinj hj.choose_spec.1 hi hj.choose_spec.2

lemma cs_sum_image {n : ℕ} (f : Fin n → Fin n) (T : Fin n → Bool → Bool) (S : Finset (Fin n))
    (h : S.image f = S) :
    (∑ x : Fin n → Bool, ∏ i ∈ S, sg (outT f T x i)) = (2 : ℤ)^n * ∏ i ∈ S, coef T i := by
  have hinj : Set.InjOn f S := Finset.card_image_iff.mp (by rw [h])
  obtain ⟨g, hgf⟩ := cs_left_inv f S hinj
  rw [Finset.sum_congr rfl (fun x _ => cs_term_image f _ T S h hinj hgf x)]
  rw [← Fintype.prod_sum (fun j b => if j ∈ S then
    sg b * sg (T (g j) b) else (1 : ℤ))]
  rw [Finset.prod_congr rfl (fun j _ => (show (∑ b : Bool, (if j ∈ S then
    sg b * sg (T (g j) b) else (1 : ℤ))) =
      2 * (if j ∈ S then coef T (g j) else 1) by
    split_ifs
    · rw [Fintype.sum_bool, cs_G]
      rfl
    · simp))]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.prod_ite_mem, Finset.univ_inter,
    ← cs_reindex f S h hinj (fun j => coef T (g j))]
  congr 1
  exact Finset.prod_congr rfl (fun i hi => by rw [hgf i hi])

theorem charsum {n : ℕ} (f : Fin n → Fin n) (T : Fin n → Bool → Bool) (S : Finset (Fin n)) :
    (∑ x : Fin n → Bool, ∏ i ∈ S, sg (outT f T x i)) =
      if S.image f = S then (2 : ℤ)^n * ∏ i ∈ S, coef T i else 0 := by
  split_ifs with h
  · exact cs_sum_image f T S h
  · exact cs_sum_zero f T S h

lemma m1_prod_ite {m : ℕ} (J : Finset (Fin m)) (c : Fin m → Bool) (b : Bool) :
    ∏ j ∈ J, (if c j = true then sg b else 1) = if par J c = true then sg b else 1 := by
  cases b
  · simp [sg]
  · have h := sg_par J c
    simp only [sg] at h ⊢
    simpa using h.symm

lemma m1_mask {n m : ℕ} (A : Fin m → Finset (Fin n)) (J : Finset (Fin m)) (o : Fin n → Bool) :
    ∏ j ∈ J, sg (par (A j) o) =
      ∏ i ∈ (Finset.univ : Finset (Fin n)).filter (fun i => par J (fun j => decide (i ∈ A j))),
        sg (o i) := by
  calc ∏ j ∈ J, sg (par (A j) o)
      = ∏ j ∈ J, ∏ i, (if decide (i ∈ A j) = true then sg (o i) else 1) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [sg_par, ← Finset.prod_filter]
        congr 1
        ext i
        simp
    _ = ∏ i, ∏ j ∈ J, (if decide (i ∈ A j) = true then sg (o i) else 1) := Finset.prod_comm
    _ = ∏ i, (if par J (fun j => decide (i ∈ A j)) = true then sg (o i) else 1) :=
        Finset.prod_congr rfl fun i _ => m1_prod_ite J (fun j => decide (i ∈ A j)) (o i)
    _ = _ := (Finset.prod_filter _ _).symm

lemma m1_ind {m : ℕ} (p y : Fin m → Bool) :
    (2 : ℤ)^m * (if ∀ j, p j = y j then 1 else 0) =
      ∑ J ∈ (Finset.univ : Finset (Fin m)).powerset, ∏ j ∈ J, (sg (p j) * sg (y j)) := by
  rw [← Finset.prod_one_add]
  split_ifs with h
  · rw [mul_one, Finset.prod_congr rfl (g := fun _ => (2 : ℤ))]
    · simp
    · intro j _
      rw [h j]
      cases y j <;> simp [sg]
  · obtain ⟨j, hj⟩ := not_forall.mp h
    rw [mul_zero]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    cases hp : p j <;> cases hy : y j <;> simp_all [sg]

lemma m1_card {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] :
    ((Nat.card {z : α // P z} : ℕ) : ℤ) = ∑ z : α, if P z then 1 else 0 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  push_cast
  rfl

theorem main1 {n : ℕ} (f : Fin n → Fin n) (m N : ℕ) (T : Fin N → Fin n → Bool → Bool)
    (A : Fin m → Finset (Fin n)) (y : Fin m → Bool) :
    (2 : ℤ)^m * ((Nat.card {z : Fin N × (Fin n → Bool) //
      ∀ j, par (A j) (outT f (T z.1) z.2) = y j} : ℕ) : ℤ) =
      (2 : ℤ)^n * ∑ J ∈ (Finset.univ : Finset (Fin m)).powerset,
        if ((Finset.univ : Finset (Fin n)).filter (fun i => par J (fun j => decide (i ∈ A j)))).image f =
            (Finset.univ : Finset (Fin n)).filter (fun i => par J (fun j => decide (i ∈ A j))) then
          sg (par J y) * (∑ e : Fin N, ∏ i ∈ (Finset.univ : Finset (Fin n)).filter
            (fun i => par J (fun j => decide (i ∈ A j))), coef (T e) i)
        else 0 := by
  rw [m1_card, Finset.mul_sum]
  simp_rw [m1_ind]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  simp_rw [Finset.prod_mul_distrib, m1_mask, ← sg_par J y]
  rw [← Finset.sum_mul, Fintype.sum_prod_type]
  simp_rw [charsum]
  split_ifs with h
  · rw [← Finset.mul_sum]
    ring
  · simp

theorem m2_par_single {n : ℕ} (j : Fin n) (x : Fin n → Bool) : par {j} x = x j := by
  unfold par
  cases h : x j <;> simp [Finset.filter_singleton, h]

theorem m2_mask {n : ℕ} (J : Finset (Fin n)) :
    (Finset.univ : Finset (Fin n)).filter
      (fun i => par J (fun j => decide (i ∈ ({j} : Finset (Fin n))))) = J := by
  ext i
  by_cases hi : i ∈ J <;> simp [par, Finset.filter_eq, hi, eq_comm]

theorem m2_hits {n : ℕ} (f : Fin n → Fin n) (T : Fin n → Bool → Bool) (v : Fin n → Bool) :
    Nat.card {z : Fin 1 × (Fin n → Bool) //
      ∀ j, par ({j} : Finset (Fin n)) (outT f ((fun _ => T) z.1) z.2) = v j} =
      Nat.card {x : Fin n → Bool // outT f T x = v} :=
  Nat.card_congr
    { toFun := fun z => ⟨z.1.2, funext fun j => by simpa [m2_par_single] using z.2 j⟩
      invFun := fun x => ⟨(0, x.1), fun j => by simp [m2_par_single, x.2]⟩
      left_inv := fun z => Subtype.ext (Prod.ext (Subsingleton.elim _ _) rfl)
      right_inv := fun x => rfl }

theorem m2_fiber {n : ℕ} (f : Fin n → Fin n) (T : Fin n → Bool → Bool) (v : Fin n → Bool) :
    ((Nat.card {x : Fin n → Bool // outT f T x = v} : ℕ) : ℤ) =
      ∑ J ∈ (Finset.univ : Finset (Fin n)).powerset,
        if J.image f = J then sg (par J v) * ∏ i ∈ J, coef T i else 0 := by
  have h := main1 f n 1 (fun _ => T) (fun j => {j}) v
  simp only [m2_mask, m2_hits, Fin.sum_univ_one] at h
  exact mul_left_cancel₀ (pow_ne_zero n two_ne_zero) h

theorem m2_coef {n : ℕ} (c : Fin n → Bool) (i : Fin n) :
    coef (fun i b => xor b (c i)) i = sg (c i) := by
  unfold coef
  cases h : c i <;> simp [h]

theorem m2_bool (p q : Prop) [Decidable p] [Decidable q] :
    ∑ b : Bool, (if p then sg b else 1) * (if q then sg b else 1) =
      if (p ↔ q) then 2 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, sg]

theorem m2_ind {n : ℕ} (J : Finset (Fin n)) (c : Fin n → Bool) :
    sg (par J c) = ∏ i, if i ∈ J then sg (c i) else 1 := by
  rw [sg_par, Finset.prod_ite_mem_eq]

theorem m2_orth {n : ℕ} (J S : Finset (Fin n)) :
    ∑ c : Fin n → Bool, sg (par J c) * sg (par S c) = if J = S then (2 : ℤ)^n else 0 := by
  simp only [m2_ind, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) => (if i ∈ J then sg b else 1) * (if i ∈ S then sg b else 1))]
  simp only [m2_bool]
  split_ifs with h
  · subst h
    simp
  · obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ J ↔ i ∈ S) := not_forall.mp fun hc => h (Finset.ext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem m2_term {n : ℕ} (f : Fin n → Fin n) (S J : Finset (Fin n)) (hS : S.image f = S)
    (u : Fin n → Bool) :
    ∑ c : Fin n → Bool, sg (par S c) *
      (if J.image f = J then sg (par J u) * sg (par J c) else 0) =
      if J = S then (2 : ℤ)^n * sg (par S u) else 0 := by
  by_cases hinv : J.image f = J
  · simp only [hinv, ite_true]
    have e : ∀ c : Fin n → Bool, sg (par S c) * (sg (par J u) * sg (par J c)) =
        sg (par J u) * (sg (par J c) * sg (par S c)) := fun c => by ring
    rw [Finset.sum_congr rfl (fun c _ => e c), ← Finset.mul_sum, m2_orth]
    split_ifs with h
    · subst h
      ring
    · simp
  · have hne : J ≠ S := fun h => hinv (h ▸ hS)
    simp [hinv, hne]

theorem m2_key {n : ℕ} (f : Fin n → Fin n) (S : Finset (Fin n)) (hS : S.image f = S)
    (u : Fin n → Bool) :
    ∑ c : Fin n → Bool, sg (par S c) * ∑ J ∈ (Finset.univ : Finset (Fin n)).powerset,
      (if J.image f = J then sg (par J u) * ∏ i ∈ J, coef (fun i b => xor b (c i)) i else 0) =
      (2 : ℤ)^n * sg (par S u) := by
  simp only [m2_coef, ← sg_par, Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun J _ => m2_term f S J hS u)]
  simp

theorem main2 {n : ℕ} (f : Fin n → Fin n) (v w : Fin n → Bool) :
    (∀ T : Fin n → Bool → Bool, Nat.card {x : Fin n → Bool // outT f T x = v} =
        Nat.card {x : Fin n → Bool // outT f T x = w}) ↔
      ∀ S : Finset (Fin n), S.image f = S → par S v = par S w := by
  constructor
  · intro h S hS
    have e : ∀ c : Fin n → Bool,
        (∑ J ∈ (Finset.univ : Finset (Fin n)).powerset,
          (if J.image f = J then sg (par J v) * ∏ i ∈ J, coef (fun i b => xor b (c i)) i else 0)) =
        ∑ J ∈ (Finset.univ : Finset (Fin n)).powerset,
          (if J.image f = J then sg (par J w) * ∏ i ∈ J, coef (fun i b => xor b (c i)) i else 0) :=
      fun c => by rw [← m2_fiber, ← m2_fiber, h]
    have hv := m2_key f S hS v
    have hw := m2_key f S hS w
    simp only [e] at hv
    have h3 := mul_left_cancel₀ (pow_ne_zero n two_ne_zero) (hv.symm.trans hw)
    revert h3
    cases par S v <;> cases par S w <;> simp [sg]
  · intro h T
    have hz : ((Nat.card {x : Fin n → Bool // outT f T x = v} : ℕ) : ℤ) =
        ((Nat.card {x : Fin n → Bool // outT f T x = w} : ℕ) : ℤ) := by
      rw [m2_fiber, m2_fiber]
      refine Finset.sum_congr rfl fun J _ => ?_
      by_cases hJ : J.image f = J
      · simp [hJ, h J hJ]
      · simp [hJ]
    exact_mod_cast hz

end PEqualNP.Outside.L_lib_994_aux

theorem PEqualNP.Outside.L_lib_994 : (∀ (n : Nat) (f : Fin n → Fin n),
  let parity := fun {a : Nat} (S : Finset (Fin a)) (x : Fin a → Bool) =>
    decide ((S.filter (fun i => x i)).card % 2 = 1)
  let sign := fun (b : Bool) => if b then (-1 : ℤ) else 1
  let out := fun (T : Fin n → Bool → Bool) (x : Fin n → Bool) (i : Fin n) =>
    xor (x i) (T i (x (f i)))
  let fiber := fun (T : Fin n → Bool → Bool) (v : Fin n → Bool) =>
    Nat.card {x : Fin n → Bool // out T x = v}
  (∀ (m N : Nat) (T : Fin N → Fin n → Bool → Bool)
    (A : Fin m → Finset (Fin n)) (y : Fin m → Bool),
    let mask := fun (J : Finset (Fin m)) =>
      (Finset.univ : Finset (Fin n)).filter
        (fun i => parity J (fun j => decide (i ∈ A j)))
    let coeff := fun (e : Fin N) (i : Fin n) =>
      if T e i false = T e i true then (0 : ℤ) else sign (T e i false)
    let hits := Nat.card {z : Fin N × (Fin n → Bool) //
      ∀ j, parity (A j) (out (T z.1) z.2) = y j}
    (2 : ℤ)^m * (hits : ℤ) =
      (2 : ℤ)^n * ∑ J ∈ (Finset.univ : Finset (Fin m)).powerset,
        if (mask J).image f = mask J then sign (parity J y) *
          (∑ e : Fin N, ∏ i ∈ mask J, coeff e i) else 0) ∧
  (∀ (v w : Fin n → Bool),
    (∀ T : Fin n → Bool → Bool, fiber T v = fiber T w) ↔
    ∀ S : Finset (Fin n), S.image f = S → parity S v = parity S w)) := by
  intro n f
  exact ⟨fun m N T A y => PEqualNP.Outside.L_lib_994_aux.main1 f m N T A y,
    fun v w => PEqualNP.Outside.L_lib_994_aux.main2 f v w⟩
