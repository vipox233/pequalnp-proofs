import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_975

open scoped BigOperators

lemma avg_prod {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℚ) :
    (𝔼 p, f p) = 𝔼 a, 𝔼 b, f (a,b) := by
  simpa only [Finset.univ_product_univ] using Finset.expect_product Finset.univ Finset.univ f

lemma avg_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (f : A → ℚ) :
    (𝔼 a, f a) = 𝔼 b, f (e.symm b) := by
  apply Finset.expect_equiv e <;> simp

lemma avg_insert {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] (i : I)
    (f : (I → A) → ℚ) :
    (𝔼 r, f r) = 𝔼 a, 𝔼 t, f ((Equiv.piSplitAt i (fun _ => A)).symm (a,t)) := by
  rw [avg_equiv (Equiv.piSplitAt i (fun _ => A)) f, avg_prod]

lemma avg_sum_indep {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
    (s : Finset I) (v : I → A → ℚ) (i : I) (hi : i ∉ s) (g h : ℚ → ℚ) :
    (𝔼 r : I → A, g (v i (r i)) * h (∑ j ∈ s, v j (r j))) =
      (𝔼 a : A, g (v i a)) * (𝔼 r : I → A, h (∑ j ∈ s, v j (r j))) := by
  classical
  let e := Equiv.piSplitAt i (fun _ => A)
  have hj (a : A) (t : {j : I // j ≠ i} → A) :
      (∑ j ∈ s, v j (e.symm (a,t) j)) = ∑ j ∈ s.attach, v j.1 (t ⟨j.1, fun he => hi (he ▸ j.2)⟩) := by
    rw [← Finset.sum_attach s]
    apply Finset.sum_congr rfl
    intro j _
    have hji : j.1 ≠ i := fun he => hi (he ▸ j.2)
    simp [e, Equiv.piSplitAt, hji]
  rw [avg_insert i, avg_insert i (fun r => h _)]
  change (𝔼 a, 𝔼 t, g (v i (e.symm (a,t) i)) * h (∑ j ∈ s, v j (e.symm (a,t) j))) =
    (𝔼 a, g (v i a)) * (𝔼 a, 𝔼 t, h (∑ j ∈ s, v j (e.symm (a,t) j)))
  simp_rw [show ∀ (a : A) t, e.symm (a,t) i = a by simp [e, Equiv.piSplitAt], hj]
  simp_rw [← Finset.mul_expect]
  simp [← Finset.expect_mul]

lemma sum_moments {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
    (s : Finset I) (v : I → A → ℚ) (hm : ∀ i, (𝔼 a, v i a) = 0)
    (hb : ∀ i a, |v i a| ≤ 1) :
    (𝔼 r : I → A, ∑ j ∈ s, v j (r j)) = 0 ∧
    (𝔼 r : I → A, (∑ j ∈ s, v j (r j))^2) ≤ s.card ∧
    (𝔼 r : I → A, (∑ j ∈ s, v j (r j))^4) ≤ 3*(s.card : ℚ)^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    let V := fun (r : I → A) => ∑ j ∈ s, v j (r j)
    let X := fun (r : I → A) => v i (r i)
    have hf (g h : ℚ → ℚ) : (𝔼 r, g (X r) * h (V r)) =
        (𝔼 a, g (v i a)) * (𝔼 r, h (V r)) := avg_sum_indep s v i hi g h
    have hx (g : ℚ → ℚ) : (𝔼 r, g (X r)) = 𝔼 a, g (v i a) := by
      simpa using hf g (fun _ => 1)
    have h2 : (𝔼 r, X r ^ 2) ≤ 1 := by
      rw [hx (fun z => z^2), ← Finset.expect_const (Finset.univ_nonempty (α := A)) (1 : ℚ)]
      apply Finset.expect_le_expect
      intro a _
      simpa only [sq_abs] using pow_le_one₀ (abs_nonneg _) (hb i a) (n := 2)
    have h4 : (𝔼 r, X r ^ 4) ≤ 1 := by
      rw [hx (fun z => z^4), ← Finset.expect_const (Finset.univ_nonempty (α := A)) (1 : ℚ)]
      exact Finset.expect_le_expect fun a _ => by simpa only [Even.pow_abs (by decide : Even 4)] using pow_le_one₀ (abs_nonneg _) (hb i a) (n := 4)
    rcases ih with ⟨hV, hV2, hV4⟩
    change (𝔼 r, V r) = 0 at hV
    change (𝔼 r, V r^2) ≤ _ at hV2
    change (𝔼 r, V r^4) ≤ _ at hV4
    have hx0 := hx id
    change (𝔼 r, X r) = 𝔼 a, v i a at hx0
    rw [hm] at hx0
    have h10 (h : ℚ → ℚ) : (𝔼 r, X r * h (V r)) = 0 := by simpa [hm] using hf id h
    have h31 : (𝔼 r, X r^3 * V r) = 0 := by simpa [hV] using hf (fun z => z^3) id
    have h22 : (𝔼 r, X r^2 * V r^2) ≤ s.card := by
      rw [hf (fun z => z^2) (fun z => z^2), ← hx (fun z => z^2)]
      exact (mul_le_mul_of_nonneg_right h2 (Finset.expect_nonneg fun _ _ => sq_nonneg _)).trans (by simpa using hV2)
    simp_rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
    change (𝔼 r, (X r + V r)) = 0 ∧ (𝔼 r, (X r + V r)^2) ≤ _ ∧ (𝔼 r, (X r + V r)^4) ≤ _
    constructor
    · rw [Finset.expect_add_distrib, hx0, hV, add_zero]
    constructor
    · have h11 : (𝔼 r, X r * V r) = 0 := h10 id
      simp only [show ∀ a b : ℚ, (a+b)^2 = a^2+2*(a*b)+b^2 by intros; ring,
        Finset.expect_add_distrib, ← Finset.mul_expect, h11]
      linarith
    · have h13 : (𝔼 r, X r * V r^3) = 0 := h10 (fun z => z^3)
      simp only [show ∀ a b : ℚ, (a+b)^4 = a^4+4*(a^3*b)+6*(a^2*b^2)+4*(a*b^3)+b^4 by intros; ring,
        Finset.expect_add_distrib, ← Finset.mul_expect, h31, h13]
      linarith

lemma variance_sum {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
    (s : Finset I) (v : I → A → ℚ) (hm : ∀ i, (𝔼 a, v i a) = 0) :
    (𝔼 r : I → A, (∑ j ∈ s, v j (r j))^2) = ∑ j ∈ s, 𝔼 a, v j a ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have h1 := avg_sum_indep s v i hi id id
    simp only [id_eq, hm, zero_mul] at h1
    have h2 := avg_sum_indep s v i hi (fun z => z^2) (fun _ => 1)
    simp only [Finset.expect_const Finset.univ_nonempty, mul_one] at h2
    simp only [Finset.sum_insert hi, show ∀ a b : ℚ, (a+b)^2 = a^2+2*(a*b)+b^2 by intros; ring,
      Finset.expect_add_distrib, ← Finset.mul_expect, h1, h2, ih, mul_zero, add_zero]

def sign (b : Bool) : ℚ := if b then -1 else 1

def clip (s : ℚ) : ℚ := max (-1) (min 1 s)

def resp (w s : ℚ) : ℚ := (clip (s+w) - clip (s-w))/2

lemma clip_mono : Monotone clip := fun _ _ h => max_le_max_left _ (min_le_min_left _ h)

lemma resp_nonneg {w : ℚ} (hw : 0 ≤ w) (s : ℚ) : 0 ≤ resp w s := by
  exact div_nonneg (sub_nonneg.2 (clip_mono (by linarith))) (by norm_num)

lemma resp_lo {u w s : ℚ} (hu : 0 ≤ u) (huw : u ≤ w) (hu' : u ≤ 1/2) :
    u * (1-4*s^2) ≤ resp w s := by
  by_cases h : |s| ≤ 1/2
  · obtain ⟨hs, ht⟩ := abs_le.mp h
    have h1 : clip (s+u) = s+u := by simp [clip, min_eq_right (by linarith : s+u ≤ 1), max_eq_right (by linarith : -1 ≤ s+u)]
    have h2 : clip (s-u) = s-u := by simp [clip, min_eq_right (by linarith : s-u ≤ 1), max_eq_right (by linarith : -1 ≤ s-u)]
    have h3 := clip_mono (show s+u ≤ s+w by linarith)
    have h4 := clip_mono (show s-w ≤ s-u by linarith)
    rw [h1] at h3
    rw [h2] at h4
    unfold resp
    nlinarith [mul_nonneg hu (sq_nonneg s)]
  · apply le_trans _ (resp_nonneg (hu.trans huw) s)
    apply mul_nonpos_of_nonneg_of_nonpos hu
    rw [not_le] at h
    nlinarith [sq_abs s]

lemma resp_hi {w s d : ℚ} (hd : 0 < d) (hdw : d+1 ≤ w) :
    1 - s^2/d^2 ≤ resp w s := by
  by_cases h : |s| ≤ d
  · obtain ⟨h1,h2⟩ := abs_le.mp h
    simp [resp, clip, min_eq_left (by linarith : 1 ≤ s+w),
      min_eq_right (by linarith : s-w ≤ 1), max_eq_left (by linarith : s-w ≤ -1)]
    positivity
  · apply le_trans _ (resp_nonneg (by linarith) s)
    have hs : d ≤ |s| := le_of_lt (lt_of_not_ge h)
    have hl := pow_le_pow_left₀ hd.le hs 2
    rw [sq_abs] at hl
    have : 1 ≤ s^2/d^2 := (one_le_div₀ (by positivity)).2 hl
    linarith

lemma avg_bool (f : Bool → ℚ) : (𝔼 b, f b) = (f false + f true)/2 := by
  have h := Fintype.card_mul_expect f
  simp only [Fintype.card_bool, Nat.cast_ofNat, Fintype.sum_bool] at h
  linarith

def score {I B : Type*} [Fintype I] [DecidableEq B] (w : I → ℚ) (v : I → Bool)
    (r : I → B × Bool) (b : B) : ℚ :=
  ∑ j, if (r j).1 = b then sign (r j).2 * sign (v j) * w j else 0

set_option maxHeartbeats 1200000 in
lemma hash_bias {I B : Type*} [Fintype I] [DecidableEq I] [Fintype B] [Nonempty B]
    [DecidableEq B] (x : I) (w : I → ℚ) (v : I → Bool) (a c : ℚ)
    (hc : 0 ≤ c) (hw : ∀ t, a - c*t^2 ≤ resp (w x) t) :
    a - c * ((∑ j, w j ^ 2) / Fintype.card B) ≤
    𝔼 r : I → B × Bool, sign (r x).2 * sign (v x) * clip (score w v r (r x).1) := by
  classical
  let J := {j : I // j ≠ x}
  let N (b : B) (j : J) (p : B × Bool) := if p.1 = b then sign p.2 * sign (v j) * w j else 0
  let S (b : B) (t : J → B × Bool) := ∑ j, N b j (t j)
  have hn (b : B) (j : J) : (𝔼 p, N b j p) = 0 := by
    rw [avg_prod]
    simp_rw [avg_bool]
    apply Finset.expect_eq_zero
    intro k _
    cases h : v j <;> by_cases hk : k = b <;> simp [hk, N, sign, h]
  have h2 (b : B) (j : J) : (𝔼 p, N b j p ^ 2) = (w j)^2 / Fintype.card B := by
    rw [avg_prod]
    simp_rw [avg_bool]
    have h (k : B) : (N b j (k,false)^2 + N b j (k,true)^2)/2 =
        if k = b then (w j)^2 else 0 := by
      cases h : v j <;> by_cases hk : k = b <;> simp [N, sign, hk, h]
    simp_rw [h]
    simp [Finset.expect, NNRat.smul_def, div_eq_inv_mul]
  have hb (b : B) : (𝔼 t, S b t ^ 2) ≤ (∑ j, w j ^ 2) / Fintype.card B := by
    unfold S
    rw [variance_sum Finset.univ (N b) (hn b)]
    simp_rw [h2, ← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    change (∑ j : {j : I // j ≠ x}, w j.1^2) ≤ _
    rw [← Finset.sum_subtype (p := fun j => j ≠ x) (Finset.univ.erase x) (by simp) (fun j => w j ^ 2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (by intros; positivity)
  let e := Equiv.piSplitAt x (fun _ => B × Bool)
  have hscore (p : B × Bool) (t : J → B × Bool) :
      score w v (e.symm (p,t)) p.1 = sign p.2 * sign (v x) * w x + S p.1 t := by
    unfold score
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
    congr 1
    · simp [e, Equiv.piSplitAt]
    · unfold S
      rw [Finset.sum_subtype (p := fun j => j ≠ x) (Finset.univ.erase x) (by simp)]
      apply Finset.sum_congr rfl
      intro j _
      simp [N, e, Equiv.piSplitAt, j.property]
  rw [avg_insert x]
  change _ ≤ 𝔼 p, 𝔼 t, sign (e.symm (p,t) x).2 * sign (v x) * clip (score w v (e.symm (p,t)) (e.symm (p,t) x).1)
  simp only [show ∀ (p : B × Bool) t, e.symm (p,t) x = p by simp [e, Equiv.piSplitAt], hscore]
  rw [avg_prod]
  rw [← Finset.expect_const (Finset.univ_nonempty (α := B)) (a - _)]
  apply Finset.expect_le_expect
  intro b _
  rw [Finset.expect_comm]
  simp_rw [avg_bool]
  have hh (t : J → B × Bool) :
      (sign false * sign (v x) * clip (sign false * sign (v x) * w x + S b t) +
       sign true * sign (v x) * clip (sign true * sign (v x) * w x + S b t))/2 =
        resp (w x) (S b t) := by
    cases hv : v x <;> simp [sign, resp, sub_eq_add_neg, add_comm]
  simp only [hh]
  calc
    _ ≤ a - c * (𝔼 t, S b t ^ 2) := by gcongr; exact hb b
    _ = 𝔼 t, (a - c * S b t ^ 2) := by rw [Finset.expect_sub_distrib, ← Finset.mul_expect, Finset.expect_const Finset.univ_nonempty]
    _ ≤ _ := Finset.expect_le_expect fun t _ => hw _

abbrev Word (m q : ℕ) := Fin m → Fin q

def count {m q : ℕ} (x y : Word m q) :=
  ((Finset.univ : Finset (Fin m)).filter (fun i => x i = y i)).card

def delta {m q : ℕ} (x y : Word m q) : ℚ := (count x y : ℚ)/m - 1/q

lemma count_sum {m q : ℕ} (x y : Word m q) :
    (count x y : ℚ) = ∑ i, if x i = y i then (1 : ℚ) else 0 := by simp [count]

lemma delta_moments {m q : ℕ} (hm : 0 < m) (hq : 0 < q) (y : Word m q) :
    (𝔼 x, delta x y ^ 2) ≤ 1/m ∧ (𝔼 x, delta x y ^ 4) ≤ 3/(m : ℚ)^2 := by
  classical
  let _ : NeZero q := ⟨hq.ne'⟩
  let v (i : Fin m) (a : Fin q) : ℚ := (if a = y i then 1 else 0) - 1/q
  have hq' : 1 ≤ (q : ℚ) := by exact_mod_cast hq
  have hp : (1 : ℚ)/q ≤ 1 := (div_le_one (by positivity)).2 hq'
  have h0 (i : Fin m) : (𝔼 a, v i a) = 0 := by
    simp [v, Finset.expect, hq.ne', div_eq_inv_mul]
  have hb (i : Fin m) (a : Fin q) : |v i a| ≤ 1 := by
    have : (0 : ℚ) ≤ 1/q := by positivity
    rw [abs_le]
    by_cases h : a = y i <;> simp only [v, h, ite_true, ite_false] <;> constructor <;> linarith
  have hh := sum_moments Finset.univ v h0 hb
  have hd (x : Word m q) : delta x y = (∑ j, v j (x j)) / m := by
    simp only [delta, count_sum, v, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simp only [Finset.card_univ, Fintype.card_fin] at hh
  simp only [hd, div_pow]
  simp only [div_eq_mul_inv, ← Finset.expect_mul]
  constructor
  · calc
      _ ≤ (m : ℚ) * ((m : ℚ)^2)⁻¹ := by gcongr; exact hh.2.1
      _ = _ := by field_simp
  · calc
      _ ≤ (3 * (m : ℚ)^2) * ((m : ℚ)^4)⁻¹ := by gcongr; exact hh.2.2
      _ = _ := by field_simp

def weight {m q : ℕ} (A s : ℚ) (x y : Word m q) := A*(1/s+s*(delta x y)^2)

lemma weight_sum {m q : ℕ} (hm : 0 < m) (hq : 0 < q) (y : Word m q)
    (A s : ℚ) (hs : 0 < s) (hs1 : (m : ℚ) ≤ s^2) (hs2 : s^2 ≤ 4*m) :
    (∑ x, weight A s x y ^ 2) ≤ (q^m : ℕ) * (18*A^2/m) := by
  have ⟨h2,h4⟩ := delta_moments hm hq y
  have he : (𝔼 x, weight A s x y ^ 2) ≤ 18*A^2/m := by
    have h1 : (1/s)^2 ≤ 1/(m : ℚ) := by rw [div_pow, one_pow]; gcongr
    have h3 : s^2 * (3/(m : ℚ)^2) ≤ 12/(m : ℚ) := by
      calc
        _ ≤ (4*m : ℚ)*(3/(m : ℚ)^2) := by gcongr
        _ = _ := by field_simp; norm_num
    calc
      _ = 𝔼 x : Word m q, (A^2 * ((1/s)^2+2*delta x y^2+s^2*delta x y^4)) := by
        apply Finset.expect_congr rfl
        intro x _
        unfold weight
        field_simp
        ring
      _ = A^2 * ((1/s)^2 + 2*(𝔼 x, delta x y^2) + s^2*(𝔼 x, delta x y^4)) := by
        let _ : NeZero q := ⟨hq.ne'⟩
        simp only [← Finset.mul_expect, Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty]
      _ ≤ A^2 * (1/m+2*(1/m)+12/m) := by
        have h5 := (mul_le_mul_of_nonneg_left h4 (sq_nonneg s)).trans h3
        gcongr
      _ ≤ _ := by ring_nf; gcongr; norm_num
  rw [← Fintype.card_mul_expect]
  simp only [Word, Fintype.card_pi_const, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_left he (by positivity)

def parity {m q : ℕ} (x y : Word m q) : Bool := count x y % 2 == 1

def adj {m q : ℕ} (x : Word m q) :
    (Σ i : Fin m, {a : Fin q // a ≠ x i}) ↪ Word m q where
  toFun u := Function.update x u.1 u.2.1
  inj' := by
    intro ⟨i,a⟩ ⟨j,b⟩ h
    change Function.update x i a.val = Function.update x j b.val at h
    have h' := congrFun h i
    by_cases hij : i = j
    · subst j
      simp only [Function.update_self] at h'
      congr 1
      exact Subtype.ext h'
    · simp [Function.update_of_ne hij] at h'
      exact (a.property h').elim

def neigh {m q : ℕ} (x : Word m q) := Finset.univ.map (adj x)

lemma card_alts {q : ℕ} (a : Fin q) : Fintype.card {b : Fin q // b ≠ a} = q-1 := by
  simp [Fintype.card_subtype_compl]

lemma card_neigh {m q : ℕ} (x : Word m q) : (neigh x).card = m*(q-1) := by
  simp [neigh, Fintype.card_sigma]

lemma count_edit {m q : ℕ} (x y : Word m q) (i : Fin m) (b : Fin q) :
    count (Function.update x i b) y + (if x i = y i then 1 else 0) =
      count x y + (if b = y i then 1 else 0) := by
  have he (z : Word m q) : count z y =
      (if z i = y i then 1 else 0) + ∑ j ∈ Finset.univ.erase i, if z j = y j then 1 else 0 := by
    rw [Finset.add_sum_erase _ (fun j => if z j = y j then 1 else 0) (Finset.mem_univ i)]
    simp [count]
  rw [he, he x, Function.update_self]
  have h : (∑ j ∈ Finset.univ.erase i, if Function.update x i b j = y j then 1 else 0) =
      ∑ j ∈ Finset.univ.erase i, if x j = y j then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [h]
  omega

lemma one_edit {m q : ℕ} (x y : Word m q) (i : Fin m) (b : Fin q) (hb : b ≠ x i) :
    sign (parity x y) * sign (parity (Function.update x i b) y) =
      1 - 2*((if x i = y i then 1 else 0) + (if b = y i then 1 else 0) : ℚ) := by
  have h := count_edit x y i b
  unfold sign parity
  simp only [beq_iff_eq]
  by_cases h1 : x i = y i <;> by_cases h2 : b = y i <;>
    simp only [h1,h2,ite_true,ite_false] at h ⊢ <;>
    split_ifs <;> norm_num <;> omega

lemma edit_bias {m q : ℕ} (x y : Word m q) :
    (∑ z ∈ neigh x, sign (parity x y) * sign (parity z y)) =
      (m*(q-1 : ℕ) : ℕ) - 2*((q-1 : ℕ)*(count x y : ℚ) + (m-count x y : ℚ)) := by
  classical
  simp only [neigh, Finset.sum_map, Fintype.sum_sigma]
  change (∑ i, ∑ b : {a : Fin q // a ≠ x i}, sign (parity x y) * sign (parity (Function.update x i b.val) y)) = _
  have ha (i : Fin m) : (∑ b : {a : Fin q // a ≠ x i}, if b.val = y i then (1 : ℚ) else 0) =
      if x i = y i then 0 else 1 := by
    rw [← Finset.sum_subtype (p := fun a => a ≠ x i) (Finset.univ.erase (x i)) (by simp) (fun a => if a = y i then 1 else 0)]
    simp [eq_comm]
  simp_rw [fun (i : Fin m) (b : {a : Fin q // a ≠ x i}) => one_edit x y i b.val b.property]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, card_alts, nsmul_eq_mul, ha, Fintype.card_fin, mul_one]
  simp_rw [show ∀ i, (if x i = y i then 0 else 1 : ℚ) = 1-(if x i = y i then 1 else 0) by intro i; split <;> norm_num]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, ← count_sum, Nat.cast_mul]

def amp (d : ℚ) := max 0 (1-20*|d|)

lemma amp_bounds (d : ℚ) : 0 ≤ amp d ∧ amp d ≤ 1 := by
  exact ⟨le_max_left _ _, max_le (by norm_num) (by linarith [abs_nonneg d])⟩

lemma amp_lip (d e : ℚ) : |amp d - amp e| ≤ 20 * |d-e| := by
  have h := abs_abs_sub_abs_le_abs_sub d e
  obtain ⟨h1,h2⟩ := abs_le.mp h
  have h3 := abs_nonneg (d-e)
  unfold amp
  rw [abs_le]
  rcases le_total 0 (1-20*|d|) with hd|hd <;> rcases le_total 0 (1-20*|e|) with he|he <;>
    simp only [max_eq_left, max_eq_right, hd, he] <;> constructor <;> linarith

lemma edit_delta {m q : ℕ} (hm : 0 < m) (x y z : Word m q) (hz : z ∈ neigh x) :
    |delta z y - delta x y| ≤ 1/m := by
  obtain ⟨⟨i,b⟩,_,rfl⟩ := Finset.mem_map.mp hz
  have h := count_edit x y i b.1
  change |delta (Function.update x i b.val) y - delta x y| ≤ _
  simp only [delta, sub_sub_sub_cancel_right, ← sub_div, abs_div, abs_of_nonneg (show 0 ≤ (m : ℚ) by positivity)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [abs_le]
  split_ifs at h <;> have h' := congrArg (fun n : ℕ => (n : ℚ)) h <;> push_cast at h' <;> constructor <;> linarith

def center {m q : ℕ} (x y z : Word m q) := sign (parity x y) * sign (parity z y) * amp (delta z y)

lemma center_bounds {m q : ℕ} (hm : 0 < m) (hq : 5 ≤ q) (x y : Word m q) :
    -(20/(m : ℚ)) ≤ (𝔼 z ∈ neigh x, center x y z) ∧
    1-4/(q : ℚ)-22*|delta x y|-20/m ≤ (𝔼 z ∈ neigh x, center x y z) := by
  let d := delta x y
  let ρ : ℚ := 1-4/(q : ℚ)
  let k : ℚ := 2*(q-2 : ℚ)/(q-1)
  have hq' : (5 : ℚ) ≤ q := by exact_mod_cast hq
  have hq1 : 0 < (q : ℚ)-1 := by linarith
  have hq0 : (0 : ℚ) < q := by linarith
  have hm0 : (0 : ℚ) < m := by positivity
  have hk : 0 ≤ k := div_nonneg (by linarith) hq1.le
  have hk2 : k ≤ 2 := (div_le_iff₀ hq1).2 (by linarith)
  have hr1 : ρ ≤ 1 := by dsimp [ρ]; linarith [div_nonneg (by norm_num : (0 : ℚ) ≤ 4) hq0.le]
  have hr0 : 1/5 ≤ ρ := by
    dsimp [ρ]
    have : 4/(q : ℚ) ≤ 4/5 := by gcongr
    linarith
  have hc : 0 < (neigh x).card := by rw [card_neigh]; exact Nat.mul_pos hm (by omega)
  have hn := Finset.card_pos.mp hc
  have hmean : (𝔼 z ∈ neigh x, sign (parity x y) * sign (parity z y)) = ρ-k*d := by
    apply mul_left_cancel₀ (show ((neigh x).card : ℚ) ≠ 0 by positivity)
    rw [Finset.card_mul_expect, edit_bias, card_neigh]
    simp only [Nat.cast_mul, Nat.cast_sub (show 1 ≤ q by omega), Nat.cast_one, ρ,k,d,delta]
    field_simp
    ring
  have hmain : (ρ-k*d)*amp d - 20/m ≤ (𝔼 z ∈ neigh x, center x y z) := by
    rw [← hmean, Finset.expect_mul, ← Finset.expect_const hn (20/(m : ℚ)), ← Finset.expect_sub_distrib]
    apply Finset.expect_le_expect
    intro z hz
    have h := (amp_lip (delta z y) d).trans (mul_le_mul_of_nonneg_left (edit_delta hm x y z hz) (by norm_num : (0 : ℚ) ≤ 20))
    rw [mul_one_div] at h
    obtain ⟨h1,h2⟩ := abs_le.mp h
    unfold center
    cases h3 : parity x y <;> cases h4 : parity z y <;> simp only [sign, Bool.false_eq_true, ite_false, ite_true, one_mul, neg_one_mul, neg_neg] <;> linarith
  have hd1 : k*d ≤ 2*|d| := (mul_le_mul_of_nonneg_left (le_abs_self _) hk).trans (mul_le_mul_of_nonneg_right hk2 (abs_nonneg _))
  have ⟨ha,ha1⟩ := amp_bounds d
  have hpos : 0 ≤ (ρ-k*d)*amp d := by
    by_cases hh : 0 ≤ 1-20*|d|
    · apply mul_nonneg _ ha
      linarith
    · simp [amp, max_eq_left (le_of_not_ge hh)]
  have hl : ρ-22*|d| ≤ (ρ-k*d)*amp d := by
    have hh : 1-20*|d| ≤ amp d := le_max_right _ _
    have h1 := mul_le_mul_of_nonneg_left hh (show 0 ≤ ρ by linarith)
    have h2 := mul_le_mul_of_nonneg_right hr1 (abs_nonneg d)
    have h3 := mul_le_mul_of_nonneg_right hd1 ha
    have h4 := mul_le_mul_of_nonneg_left ha1 (abs_nonneg d)
    nlinarith
  change _ ≤ _ ∧ ρ-22*|d|-20/m ≤ _
  constructor <;> linarith

lemma coin (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ (D : ℕ) (_ : 0 < D) (f : Fin D → Bool), ∀ a b : ℚ,
      (𝔼 k, (if f k then a else b)) = p*a+(1-p)*b := by
  let n := p.num.toNat
  let D := p.den
  have hd : 0 < D := p.den_pos
  have hd' : (0 : ℚ) < D := by positivity
  have hn : (n : ℚ) / D = p := by
    have h : 0 ≤ p.num := Rat.num_nonneg.mpr hp
    have he : (n : ℤ) = p.num := Int.toNat_of_nonneg h
    rw [← p.num_div_den]
    exact congrArg (· / (D : ℚ)) (by exact_mod_cast he : (n : ℚ) = (p.num : ℚ))
  have hle : n ≤ D := by
    exact_mod_cast (div_le_one hd').mp (hn.trans_le hp1)
  let f (k : Fin D) := decide (k.val < n)
  have hc : (Finset.univ.filter (fun k : Fin D => k.val < n)).card = n := by
    rcases hle.eq_or_lt with h|h
    · simp [h]
    · let a : Fin D := ⟨n,h⟩
      have he : (Finset.univ.filter (fun k : Fin D => k.val < n)) = Finset.Iio a := by ext; simp [a,Fin.lt_def]
      rw [he, Fin.card_Iio]
  refine ⟨D,hd,f,?_⟩
  intro a b
  apply mul_left_cancel₀ hd'.ne'
  conv_lhs => lhs; rw [← Fintype.card_fin D]
  rw [Fintype.card_mul_expect]
  have hh := Finset.univ.card_filter_add_card_filter_not (fun k : Fin D => k.val < n)
  simp only [hc, Finset.card_univ, Fintype.card_fin] at hh
  have hh' : (Finset.univ.filter fun k : Fin D => ¬k.val < n).card = D-n := by omega
  simp only [f, decide_eq_true_eq, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, hc, hh', Nat.cast_sub hle]
  rw [← hn]
  field_simp

def pick {W : Type*} [DecidableEq W] (T : Finset W) :
    (k : ℕ) → (Fin k → W) → Option (Fin k)
  | 0, _ => none
  | k+1, r => if r 0 ∈ T then some 0 else (pick T k (Fin.tail r)).map Fin.succ

lemma avg_select {W : Type*} [Fintype W] [Nonempty W] [DecidableEq W] (T : Finset W) (k : ℕ) (f : W → ℚ) (b : ℚ) :
    (𝔼 r : Fin k → W, (pick T k r).elim b (fun j => f (r j))) =
      (1-(1-(T.card : ℚ)/Fintype.card W)^k) * (𝔼 w ∈ T, f w) + (1-(T.card : ℚ)/Fintype.card W)^k*b := by
  classical
  have hw : (0 : ℚ) < Fintype.card W := by exact_mod_cast Fintype.card_pos
  have he (c : ℚ) : (𝔼 w, if w ∈ T then f w else c) =
      ((T.card : ℚ)/Fintype.card W)*(𝔼 w ∈ T, f w)+(1-(T.card : ℚ)/Fintype.card W)*c := by
    apply mul_left_cancel₀ hw.ne'
    rw [Fintype.card_mul_expect, Finset.sum_ite]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    have hs : (Finset.univ.filter fun w => w ∉ T) = Tᶜ := by ext; simp
    rw [hs, Finset.card_compl, Nat.cast_sub T.card_le_univ, ← Finset.card_mul_expect]
    field_simp
  induction k with
  | zero => simp [pick]
  | succ k ih =>
    rw [avg_equiv (Fin.consEquiv (fun _ : Fin (k+1) => W)).symm, avg_prod]
    simp only [Equiv.symm_symm, Fin.consEquiv_apply, pick, Fin.cons_zero, Fin.tail_cons]
    have hp (a : W) (t : Fin k → W) :
        ((if a ∈ T then some 0 else (pick T k t).map Fin.succ).elim b (fun j => f (Fin.cons (α := fun _ => W) a t j))) =
          if a ∈ T then f a else (pick T k t).elim b (fun j => f (t j)) := by
      by_cases h : a ∈ T <;> cases h0 : pick T k t <;> simp [h]
    simp_rw [hp]
    have hinner (a : W) : (𝔼 t : Fin k → W, if a ∈ T then f a else (pick T k t).elim b (fun j => f (t j))) =
        if a ∈ T then f a else (𝔼 t : Fin k → W, (pick T k t).elim b (fun j => f (t j))) := by
      by_cases h : a ∈ T <;> simp [h]
    simp_rw [hinner]
    rw [he, ih, pow_succ]
    ring

lemma round_table {U : Type} [Fintype U] (g : U → ℚ) (hg : ∀ u, |g u| ≤ 1) :
    ∃ (T : Type) (_ : Fintype T) (_ : Nonempty T) (out : T → U → Bool),
      ∀ u, (𝔼 t, sign (out t u)) = g u := by
  classical
  have h (u : U) := abs_le.mp (hg u)
  have hc (u : U) := coin ((1-g u)/2) (by linarith [(h u).2]) (by linarith [(h u).1])
  choose D hd f hf using hc
  let A := fun u => Fin (D u)
  let _ (u : U) : Nonempty (A u) := ⟨⟨0,hd u⟩⟩
  refine ⟨∀ u, A u, inferInstance, inferInstance, fun t u => f u (t u), ?_⟩
  intro u
  rw [avg_equiv (Equiv.piSplitAt u A), avg_prod]
  simp only [Equiv.piSplitAt_symm_apply, dite_eq_left, Finset.expect_const Finset.univ_nonempty]
  change (𝔼 k, (if f u k then (-1 : ℚ) else 1)) = _
  rw [hf]
  ring

lemma compile_protocol {S M X Y : Type} [Fintype S] [Nonempty S] [Fintype M] [Fintype Y]
    (truth : X → Y → Bool) (send : S → X → M) (val : S → M → Y → ℚ) (β : ℚ)
    (hv : ∀ s j y, |val s j y| ≤ 1)
    (h : ∀ x y, β ≤ 𝔼 s, sign (truth x y) * val s (send s x) y) :
    ∃ (z : ℕ) (send' : Fin z → X → Fin (Fintype.card M)) (read' : Fin z → Fin (Fintype.card M) → Y → Bool),
      0 < z ∧ ∀ x y, (1+β)*(z : ℚ) ≤ 2*(((Finset.univ : Finset (Fin z)).filter
        (fun seed => read' seed (send' seed x) y = truth x y)).card : ℚ) := by
  classical
  obtain ⟨T,instT,ht,R,hR⟩ := round_table (fun u : S × M × Y => val u.1 u.2.1 u.2.2) (fun u => hv _ _ _)
  let e := Fintype.equivFin (S × T)
  let a := Fintype.equivFin M
  let F (i : Fin (Fintype.card (S × T))) (x : X) := a (send (e.symm i).1 x)
  let G (i : Fin (Fintype.card (S × T))) (j : Fin (Fintype.card M)) (y : Y) :=
    R (e.symm i).2 ((e.symm i).1,a.symm j,y)
  refine ⟨_,F,G,Fintype.card_pos,?_⟩
  intro x y
  let z := Fintype.card (S × T)
  have he : (𝔼 i : Fin z, sign (truth x y) * sign (G i (F i x) y)) = 𝔼 s, sign (truth x y) * val s (send s x) y := by
    rw [avg_equiv e.symm, avg_prod]
    simp only [Equiv.symm_symm,F,G,Equiv.symm_apply_apply,← Finset.mul_expect,hR]
  have ha := (h x y).trans_eq he.symm
  have hh (i : Fin z) : sign (truth x y) * sign (G i (F i x) y) =
      2*(if G i (F i x) y = truth x y then (1 : ℚ) else 0) - 1 := by
    cases truth x y <;> cases G i (F i x) y <;> norm_num [sign]
  have hpos : 0 ≤ (z : ℚ) := by positivity
  have hb := mul_le_mul_of_nonneg_left ha hpos
  conv at hb => rhs; lhs; rw [← Fintype.card_fin z]
  rw [Fintype.card_mul_expect] at hb
  simp only [hh,Finset.sum_sub_distrib,← Finset.mul_sum, Finset.sum_boole, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one] at hb
  change (1+β)*(z : ℚ) ≤ _
  linarith

def gain : ℚ := 64000000

def bucketFactor : ℕ := 288*64000000^2

def buckets (m q : ℕ) := bucketFactor*(q^m/m+1)

lemma bucket_bounds {m q : ℕ} (hm : 0 < m) (hq : 5 ≤ q) :
    0 < buckets m q ∧ bucketFactor*q^m ≤ buckets m q * m ∧
    buckets m q * m ≤ 2*bucketFactor*q^m := by
  have h1 := Nat.lt_mul_div_succ (q^m) hm
  have h2 := Nat.div_mul_le_self (q^m) m
  have h3 : m ≤ q^m := (Nat.lt_pow_self (a := q) (by omega) (n := m)).le
  unfold buckets
  constructor
  · exact Nat.mul_pos (by decide) (Nat.succ_pos _)
  constructor
  · rw [Nat.mul_assoc, Nat.mul_comm (_ + 1) m]
    exact Nat.mul_le_mul_left _ h1.le
  · calc
      _ = bucketFactor * (q^m/m*m+m) := by ring
      _ ≤ bucketFactor * (q^m+q^m) := Nat.mul_le_mul_left _ (Nat.add_le_add h2 h3)
      _ = _ := by ring

def hashed {m q H : ℕ} (s : ℚ) (x y : Word m q) (v : Word m q → Bool)
    (r : Word m q → Fin H × Bool) :=
  sign (r x).2 * sign (v x) * clip (score (fun j => weight gain s j y) v r (r x).1)

lemma hash_bounds {m q : ℕ} (hm : 0 < m) (hq : 5 ≤ q) (s : ℚ) (hs : 8000 ≤ s)
    (hs1 : (m : ℚ) ≤ s^2) (hs2 : s^2 ≤ 4*m) (x y : Word m q) (v : Word m q → Bool) :
    let H := buckets m q
    let b := 𝔼 r : Word m q → Fin H × Bool, hashed s x y v r
    (|delta x y| ≤ 1/4000 → 200*(1/s+|delta x y|) ≤ b) ∧
    (1/4000 ≤ |delta x y| → 1-1/(m : ℚ) ≤ b) := by
  let H := buckets m q
  have ⟨hH,hB,_⟩ := bucket_bounds hm hq
  let _ : NeZero H := ⟨hH.ne'⟩
  let d := delta x y
  let w := fun j => weight gain s j y
  let V := (∑ j, w j^2)/(H : ℚ)
  have hs0 : 0 < s := by linarith
  have hm0 : (0 : ℚ) < m := by positivity
  have hH0 : (0 : ℚ) < H := by exact_mod_cast hH
  have hV : V ≤ 1/16 := by
    apply (div_le_iff₀ hH0).2
    refine (weight_sum hm (by omega) y gain s hs0 hs1 hs2).trans ?_
    have h' : (bucketFactor : ℚ)*(q^m : ℕ) ≤ (H : ℚ)*m := by exact_mod_cast hB
    norm_num [bucketFactor] at h'
    norm_num [gain]
    field_simp
    linarith
  let b := 𝔼 r : Word m q → Fin H × Bool, hashed s x y v r
  have hh (a c : ℚ) (hc : 0 ≤ c) (hh : ∀ t, a-c*t^2 ≤ resp (w x) t) : a-c*V ≤ b := by
    simpa only [V,b,hashed,w,Fintype.card_fin] using hash_bias (B := Fin H) x w v a c hc hh
  change (|d| ≤ _ → _ ≤ b) ∧ (_ ≤ |d| → _ ≤ b)
  constructor
  · intro hd
    let u := 300*(1/s+|d|)
    have hu : 0 ≤ u := by dsimp [u]; positivity
    have hu1 : u ≤ 1/2 := by
      have : 1/s ≤ 1/8000 := by gcongr
      dsimp [u]; linarith
    have hun : u ≤ w x := by
      change 300*(1/s+|d|) ≤ 64000000*(1/s+s*d^2)
      apply (mul_le_mul_iff_of_pos_left hs0).mp
      have he : s*(1/s) = 1 := by field_simp
      nlinarith [sq_nonneg (s*|d|-1), sq_abs d, sq_nonneg (s*d), mul_nonneg (sq_nonneg s) (sq_nonneg d),
        show (s*|d|)^2 = s^2*d^2 by rw [mul_pow,sq_abs]]
    have h := hh u (4*u) (by positivity) fun t => by
      simpa only [mul_sub, mul_one, mul_left_comm, mul_assoc] using resp_lo (s := t) hu hun hu1
    have hv := mul_le_mul_of_nonneg_left hV (show 0 ≤ 4*u by positivity)
    dsimp [u] at h hv hu
    nlinarith
  · intro hd
    have hw : s+1 ≤ w x := by
      change s+1 ≤ 64000000*(1/s+s*d^2)
      have hl := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 1/4000) hd 2
      rw [sq_abs] at hl
      have hh := mul_le_mul_of_nonneg_left hl hs0.le
      nlinarith [one_div_pos.mpr hs0]
    have h := hh 1 (1/s^2) (by positivity) fun t => by
      simpa only [div_eq_inv_mul, mul_one] using resp_hi (s := t) hs0 hw
    have hv := mul_le_mul_of_nonneg_left hV (show 0 ≤ 1/s^2 by positivity)
    have hv' : 1/s^2 ≤ 1/(m : ℚ) := by gcongr
    have hpos : 0 ≤ 1/s^2 := by positivity
    linarith

def rho (q : ℕ) : ℚ := 1-4/(q : ℚ)

def beta (q : ℕ) := rho q/(1+rho q)

def tau (m q : ℕ) := beta q+32/(m : ℚ)

lemma beta_bounds {q : ℕ} (hq : 5 ≤ q) :
    1/5 ≤ rho q ∧ rho q ≤ 1 ∧ 1/6 ≤ beta q ∧ beta q ≤ 1/2 ∧ (1-beta q)*rho q = beta q := by
  have hq' : (5 : ℚ) ≤ q := by exact_mod_cast hq
  have hr : 1/5 ≤ rho q := by
    have : 4/(q : ℚ) ≤ 4/5 := by gcongr
    unfold rho
    linarith
  have hr1 : rho q ≤ 1 := by unfold rho; linarith [show (0 : ℚ) ≤ 4/q by positivity]
  have h : 0 < 1+rho q := by linarith
  refine ⟨hr,hr1,(le_div_iff₀ h).2 (by linarith),(div_le_iff₀ h).2 (by linarith),?_⟩
  unfold beta
  field_simp
  ring

lemma mix_bound {m q : ℕ} (hm : 64000000 ≤ m) (hq : 5 ≤ q)
    (s : ℚ) (hs : 8000 ≤ s) (hs1 : (m : ℚ) ≤ s^2) (hs2 : s^2 ≤ 4*m)
    (x y : Word m q) (v : Word m q → Bool) :
    beta q ≤ (1-tau m q)*(𝔼 z ∈ neigh x, center x y z) + tau m q *
      (𝔼 r : Word m q → Fin (buckets m q) × Bool, hashed s x y v r) := by
  let d := |delta x y|
  let C := 𝔼 z ∈ neigh x, center x y z
  let B := 𝔼 r : Word m q → Fin (buckets m q) × Bool, hashed s x y v r
  have hm' : (64000000 : ℚ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℚ) < m := by linarith
  have hs0 : 0 < s := by linarith
  have ⟨hr,hr1,hb,hb1,he⟩ := beta_bounds hq
  have ht0 : 1/6 ≤ tau m q := by unfold tau; linarith [show (0 : ℚ) ≤ 32/m by positivity]
  have ht1 : tau m q ≤ 1 := by
    have : 32/(m : ℚ) ≤ 1/2 := (div_le_iff₀ hm0).2 (by linarith)
    unfold tau
    linarith
  have ⟨hc1,hc2⟩ := center_bounds (by omega : 0 < m) hq x y
  change -(20/(m : ℚ)) ≤ C at hc1
  change rho q-22*d-20/m ≤ C at hc2
  have ⟨hn,hf⟩ := hash_bounds (by omega : 0 < m) hq s hs hs1 hs2 x y v
  change beta q ≤ (1-tau m q)*C+tau m q*B
  rcases le_total d (1/4000) with hd|hd
  · have hh : 200*(1/s+d) ≤ B := hn hd
    have hd0 : 0 ≤ d := abs_nonneg _
    have hscale : 2*s ≤ m := by nlinarith
    have hi : 2/(m : ℚ) ≤ 1/s := (div_le_div_iff₀ hm0 hs0).2 (by linarith)
    have h1 := mul_le_mul_of_nonneg_left hc2 (sub_nonneg.mpr ht1)
    have h2 := mul_le_mul_of_nonneg_left hh (show 0 ≤ tau m q by linarith)
    have h3 := mul_le_mul_of_nonneg_right ht0 (show 0 ≤ 200*(1/s+d) by positivity)
    have h4 := mul_le_mul_of_nonneg_right (show 1-tau m q ≤ 1 by linarith) (show (0 : ℚ) ≤ 22*d+20/m by positivity)
    have h5 := mul_le_mul_of_nonneg_left hr1 (show (0 : ℚ) ≤ 32/m by positivity)
    unfold tau at *
    simp only [div_eq_mul_inv] at *
    nlinarith only [h1,h2,h3,h4,h5,he,hi,hd0,inv_nonneg.mpr hm0.le]
  · have hh : 1-1/(m : ℚ) ≤ B := hf hd
    have h1 := mul_le_mul_of_nonneg_left hc1 (sub_nonneg.mpr ht1)
    have h2 := mul_le_mul_of_nonneg_left hh (show 0 ≤ tau m q by linarith)
    have h3 := mul_le_mul_of_nonneg_right ht1 (show (0 : ℚ) ≤ 1/m by positivity)
    have h4 := mul_nonneg (show 0 ≤ tau m q by linarith) (show (0 : ℚ) ≤ 20/m by positivity)
    unfold tau at *
    simp only [div_eq_mul_inv] at *
    nlinarith only [h1,h2,h3,h4,inv_nonneg.mpr hm0.le]

def miss (m q : ℕ) : ℚ := (1-(m*(q-1) : ℕ)/(q^m : ℕ))^(buckets m q)

lemma miss_bounds {m q : ℕ} (hm : 0 < m) (hq : 5 ≤ q) (x : Word m q) :
    0 ≤ miss m q ∧ miss m q ≤ 1/6 := by
  let p : ℚ := (m*(q-1) : ℕ)/(q^m : ℕ)
  let K := buckets m q
  have hq0 : 0 < q := by omega
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hn : (0 : ℚ) < (q^m : ℕ) := by positivity
  have hp1 : p ≤ 1 := by
    apply (div_le_one hn).2
    have h := (neigh x).card_le_univ
    rw [card_neigh] at h
    exact_mod_cast (by simpa [Word,Fintype.card_pi_const] using h : m*(q-1) ≤ q^m)
  have hKp : 6 ≤ (K : ℚ)*p := by
    have hk := (bucket_bounds hm hq).2.1
    have h : 6*q^m ≤ K*m*(q-1) := calc
      _ ≤ bucketFactor*q^m := Nat.mul_le_mul_right _ (by decide)
      _ ≤ K*m := hk
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
    dsimp [p]
    rw [← mul_div_assoc, le_div_iff₀ hn]
    exact_mod_cast (by simpa [Nat.mul_assoc] using h : 6*q^m ≤ K*(m*(q-1)))
  change 0 ≤ (1-p)^K ∧ (1-p)^K ≤ 1/6
  have h0 := sub_nonneg.mpr hp1
  refine ⟨pow_nonneg h0 _,?_⟩
  have h1 : (1-p)^K*(1+p)^K ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (mul_nonneg h0 (by linarith)) (by nlinarith [sq_nonneg p])
  have h2 := one_add_mul_le_pow (show -2 ≤ p by linarith) K
  nlinarith [mul_le_mul_of_nonneg_left (show 6 ≤ (1+p)^K by linarith) (pow_nonneg h0 K)]

abbrev Msg (k : ℕ) := (Fin k ⊕ Fin k) × Bool

lemma sign_xor (a b : Bool) : sign (xor a b) = sign a * sign b := by
  cases a <;> cases b <;> norm_num [sign]

lemma abs_sign (a : Bool) : |sign a| = 1 := by cases a <;> norm_num [sign]

lemma large_protocol {m q : ℕ} (hm : 64000000 ≤ m) (hq : 5 ≤ q) (left right : Word m q → Bool) :
    let k := buckets m q
    let truth := fun x y => xor (xor (left x) (right y)) (parity x y)
    ∃ (z : ℕ) (send : Fin z → Word m q → Fin (Fintype.card (Msg k)))
      (read : Fin z → Fin (Fintype.card (Msg k)) → Word m q → Bool), 0 < z ∧
      ∀ x y, (1+beta q)*(z : ℚ) ≤ 2*(((Finset.univ : Finset (Fin z)).filter
        (fun seed => read seed (send seed x) y = truth x y)).card : ℚ) := by
  classical
  let k := buckets m q
  let W := Word m q
  let truth (x y : W) := xor (xor (left x) (right y)) (parity x y)
  let _ : NeZero q := ⟨by omega⟩
  let _ : NeZero k := ⟨(bucket_bounds (by omega : 0 < m) hq).1.ne'⟩
  let s : ℚ := (m.sqrt : ℚ)+1
  have hm' : (64000000 : ℚ) ≤ m := by exact_mod_cast hm
  have hs1 : (m : ℚ) ≤ s^2 := by dsimp [s]; exact_mod_cast (Nat.lt_succ_sqrt' m).le
  have hs2 : s^2 ≤ 4*m := by
    have hl : (m.sqrt : ℚ)^2 ≤ m := by exact_mod_cast Nat.sqrt_le' m
    have hle : (m.sqrt : ℚ) ≤ m := by exact_mod_cast Nat.sqrt_le_self m
    dsimp [s]; nlinarith
  have hs : 8000 ≤ s := by
    have hh : 0 ≤ s := by dsimp [s]; positivity
    nlinarith
  have hms := miss_bounds (by omega : 0 < m) hq (fun _ => (0 : Fin q))
  have hhit : 0 < 1-miss m q := by linarith [hms.2]
  have ht1 : tau m q ≤ 1 := by
    have hh : 32/(m : ℚ) ≤ 1/2 := (div_le_iff₀ (by positivity)).2 (by linarith)
    unfold tau
    linarith [(beta_bounds hq).2.2.2.1]
  have ht0 : miss m q ≤ tau m q := by
    unfold tau
    linarith [hms.2,(beta_bounds hq).2.2.1,show (0 : ℚ) ≤ 32/m by positivity]
  let p := (1-tau m q)/(1-miss m q)
  have hp : 0 ≤ p := div_nonneg (sub_nonneg.mpr ht1) hhit.le
  have hp1 : p ≤ 1 := (div_le_one hhit).2 (by linarith)
  obtain ⟨D,hD,coinF,coinH⟩ := coin p hp hp1
  let _ : NeZero D := ⟨hD.ne'⟩
  let R := W → Fin k × Bool
  let L := Fin k → W
  let S := R × Fin D × L
  let F (u : S) (x : W) : Msg k :=
    let fallback : Msg k := (Sum.inr (u.1 x).1,(u.1 x).2)
    if coinF u.2.1 then (pick (neigh x) k u.2.2).elim fallback (fun j => (Sum.inl j,left x))
    else fallback
  let G (u : S) (msg : Msg k) (y : W) : ℚ :=
    Sum.elim (fun j => sign (xor (xor msg.2 (right y)) (parity (u.2.2 j) y)) * amp (delta (u.2.2 j) y))
      (fun j => sign msg.2 * clip (score (fun a => weight gain s a y) (fun a => truth a y) u.1 j)) msg.1
  have hG (u : S) (msg : Msg k) (y : W) : |G u msg y| ≤ 1 := by
    rcases msg with ⟨j,b⟩
    cases j with
    | inl j => simpa [G,abs_mul,abs_sign,abs_of_nonneg (amp_bounds _).1] using (amp_bounds (delta (u.2.2 j) y)).2
    | inr j =>
      simp only [G,Sum.elim_inr,abs_mul,abs_sign,one_mul,abs_le,clip]
      constructor
      · exact le_max_left _ _
      · exact max_le (by norm_num) (min_le_left _ _)
  apply compile_protocol truth F G (beta q) hG
  intro x y
  let B (r : R) := hashed s x y (fun a => truth a y) r
  let C := 𝔼 a ∈ neigh x, center x y a
  have hval (r : R) (i : Fin D) (t : L) :
      sign (truth x y)*G (r,i,t) (F (r,i,t) x) y =
      if coinF i then (pick (neigh x) k t).elim (B r) (fun j => center x y (t j)) else B r := by
    cases hcoin : coinF i <;> cases hj : pick (neigh x) k t <;>
      simp only [F,G,hcoin,hj,Bool.false_eq_true,ite_false,ite_true,Option.elim_none,Option.elim_some,Sum.elim_inr,Sum.elim_inl,B,hashed,center,truth]
    all_goals try ac_rfl
    simp only [sign_xor]
    cases left x <;> cases right y <;> norm_num only [sign,ite_true,Bool.false_eq_true,ite_false,one_mul,neg_one_mul,mul_neg,neg_mul,neg_neg] <;> ring
  have hsel (r : R) : (𝔼 t : L, (pick (neigh x) k t).elim (B r) (fun j => center x y (t j))) =
      (1-miss m q)*C + miss m q*B r := by
    simpa only [C,Word,miss,card_neigh,Fintype.card_pi_const,Fintype.card_fin] using avg_select (neigh x) k (center x y) (B r)
  have hinner (r : R) (i : Fin D) : (𝔼 t : L, sign (truth x y)*G (r,i,t) (F (r,i,t) x) y) =
      if coinF i then (1-miss m q)*C + miss m q*B r else B r := by
    simp_rw [hval]
    cases h : coinF i <;> simp [hsel]
  have he (r : R) : (𝔼 it : Fin D × L, sign (truth x y)*G (r,it) (F (r,it) x) y) =
      (1-tau m q)*C+tau m q*B r := by
    rw [avg_prod]
    simp_rw [hinner]
    rw [coinH]
    have hp' : p*(1-miss m q) = 1-tau m q := div_mul_cancel₀ _ hhit.ne'
    linear_combination (C-B r)*hp'
  change _ ≤ 𝔼 u : R × Fin D × L, sign (truth x y)*G u (F u x) y
  rw [avg_prod]
  simp_rw [he]
  rw [Finset.expect_add_distrib,Finset.expect_const Finset.univ_nonempty,← Finset.mul_expect]
  exact mix_bound hm hq s hs hs1 hs2 x y (fun a => truth a y)

end PEqualNP.Outside.L_lib_975

theorem PEqualNP.Outside.L_lib_975 : ∀ (q : Nat), 5 ≤ q →
  let ρ : ℚ := 1-4/(q : ℚ)
  let β := ρ/(1+ρ)
  ∃ C : Nat, 0 < C ∧ ∀ m : Nat, 0 < m →
    let W := Fin m → Fin q
    ∀ left right : W → Bool,
      let truth := fun (x y : W) => xor (xor (left x) (right y))
        (((Finset.univ : Finset (Fin m)).filter (fun i => x i = y i)).card % 2 == 1)
      ∃ (M z : Nat) (send : Fin z → W → Fin M) (read : Fin z → Fin M → W → Bool),
        0 < z ∧ M*m ≤ C*q^m ∧ ∀ x y, (1+β)*(z : ℚ) ≤
          2*(((Finset.univ : Finset (Fin z)).filter
            (fun seed => read seed (send seed x) y = truth x y)).card : ℚ) := by
  classical
  intro q hq
  let C := 8*PEqualNP.Outside.L_lib_975.bucketFactor+64000000
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro m hm W left right
  by_cases h : 64000000 ≤ m
  · obtain ⟨z,send,read,hz,hgood⟩ := PEqualNP.Outside.L_lib_975.large_protocol h hq left right
    refine ⟨_,z,send,read,hz,?_,hgood⟩
    have hcard : Fintype.card (PEqualNP.Outside.L_lib_975.Msg (PEqualNP.Outside.L_lib_975.buckets m q)) = 4*PEqualNP.Outside.L_lib_975.buckets m q := by
      simp [PEqualNP.Outside.L_lib_975.Msg,Fintype.card_sum,Fintype.card_prod]; ring
    rw [hcard, Nat.mul_assoc]
    calc
      _ ≤ 4*(2*PEqualNP.Outside.L_lib_975.bucketFactor*q^m) := Nat.mul_le_mul_left _ (PEqualNP.Outside.L_lib_975.bucket_bounds hm hq).2.2
      _ ≤ C*q^m := by dsimp [C]; ring_nf; omega
  · let e := Fintype.equivFin W
    let truth (x y : W) := xor (xor (left x) (right y)) (PEqualNP.Outside.L_lib_975.parity x y)
    refine ⟨_,1,fun _ x => e x,fun _ j y => truth (e.symm j) y,by decide,?_,?_⟩
    · have hcard : Fintype.card W = q^m := by simp [W]
      rw [hcard, Nat.mul_comm]
      exact Nat.mul_le_mul_right _ (by dsimp [C]; omega)
    · intro x y
      change (1+PEqualNP.Outside.L_lib_975.beta q)*(1 : ℕ) ≤ 2*(((Finset.univ : Finset (Fin 1)).filter (fun _ => truth (e.symm (e x)) y = truth x y)).card : ℚ)
      simp
      linarith [(PEqualNP.Outside.L_lib_975.beta_bounds hq).2.2.2.1]
