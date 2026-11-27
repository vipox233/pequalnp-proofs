import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_523_aux

/-- Big-endian binary word of `n` on `k` bits. -/
def bits : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, n => bits k (n / 2) ++ [decide (n % 2 = 1)]

lemma bits_length (k n : ℕ) : (bits k n).length = k := by
  induction k generalizing n with
  | zero => simp [bits]
  | succ k ih => simp [bits, ih]

lemma bits_add (k r b : ℕ) : bits (k + r) b = bits k (b / 2 ^ r) ++ bits r b := by
  induction r generalizing b with
  | zero => simp [bits]
  | succ r ih =>
    rw [show k + (r + 1) = (k + r) + 1 from rfl]
    simp only [bits]
    rw [ih (b / 2), Nat.div_div_eq_div_mul, ← pow_succ', List.append_assoc]

lemma bits_inj (k a b : ℕ) (h : bits k a = bits k b) : a % 2 ^ k = b % 2 ^ k := by
  induction k generalizing a b with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    simp only [bits] at h
    have hl : (bits k (a / 2)).length = (bits k (b / 2)).length := by
      simp [bits_length]
    have h1 := List.append_inj_left h hl
    have h2 := List.append_inj_right h hl
    have e1 := ih _ _ h1
    have e2 : a % 2 = b % 2 := by
      simp only [List.cons.injEq, and_true, decide_eq_decide] at h2
      omega
    rw [pow_succ', Nat.mod_mul, Nat.mod_mul, e1, e2]

/-- Converse of the Kraft inequality, binary alphabet. -/
lemma kraft_converse {m : ℕ} (l : Fin m → ℕ) (hk : ∑ i, ((1 : ℝ) / 2) ^ (l i) ≤ 1) :
    ∃ c : Fin m → List Bool, (∀ i, (c i).length = l i) ∧
      ∀ i j, (∃ t : List Bool, c j = c i ++ t) → i = j := by
  classical
  set L := ∑ i, l i with hLdef
  have hlL : ∀ i, l i ≤ L := fun i =>
    Finset.single_le_sum (f := l) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hkN : ∑ i, 2 ^ (L - l i) ≤ 2 ^ L := by
    have hR : ((∑ i, 2 ^ (L - l i) : ℕ) : ℝ) = (2 : ℝ) ^ L * ∑ i, ((1 : ℝ) / 2) ^ (l i) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have := hlL i
      rw [div_pow, one_pow, mul_one_div, eq_div_iff (by positivity), ← pow_add,
        Nat.sub_add_cancel this]
    have : ((∑ i, 2 ^ (L - l i) : ℕ) : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := by
      rw [hR]; push_cast
      calc (2 : ℝ) ^ L * ∑ i, ((1 : ℝ) / 2) ^ (l i) ≤ (2 : ℝ) ^ L * 1 :=
            mul_le_mul_of_nonneg_left hk (by positivity)
        _ = 2 ^ L := mul_one _
    exact_mod_cast this
  let prec : Fin m → Fin m → Prop := fun j i => l j < l i ∨ (l j = l i ∧ j.val < i.val)
  let a : Fin m → ℕ := fun i => ∑ j ∈ Finset.univ.filter (fun j => prec j i), 2 ^ (L - l j)
  have key1 : ∀ i j, prec j i → a j + 2 ^ (L - l j) ≤ a i := by
    intro i j hji
    have hnot : j ∉ Finset.univ.filter (fun k => prec k j) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, prec]; omega
    have hsub : insert j (Finset.univ.filter (fun k => prec k j)) ⊆
        Finset.univ.filter (fun k => prec k i) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, prec] at hk ⊢
      rcases hk with rfl | hk
      · exact hji
      · simp only [prec] at hji; omega
    have := Finset.sum_le_sum_of_subset (f := fun k => 2 ^ (L - l k)) hsub
    rw [Finset.sum_insert hnot] at this
    simp only [a]; omega
  have key2 : ∀ i, a i + 2 ^ (L - l i) ≤ 2 ^ L := by
    intro i
    have hnot : i ∉ Finset.univ.filter (fun k => prec k i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, prec]; omega
    have := Finset.sum_le_sum_of_subset (f := fun k => 2 ^ (L - l k))
      (Finset.subset_univ (insert i (Finset.univ.filter (fun k => prec k i))))
    rw [Finset.sum_insert hnot] at this
    simp only [a]; omega
  have key3 : ∀ i, 2 ^ (L - l i) ∣ a i := by
    intro i
    apply Finset.dvd_sum
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, prec] at hj
    exact pow_dvd_pow 2 (by omega)
  let A : Fin m → ℕ := fun i => a i / 2 ^ (L - l i)
  have hA : ∀ i, a i = A i * 2 ^ (L - l i) := fun i => (Nat.div_mul_cancel (key3 i)).symm
  have hAlt : ∀ i, A i < 2 ^ (l i) := by
    intro i
    have h1 : a i < 2 ^ L := by
      have := key2 i; have : 0 < 2 ^ (L - l i) := by positivity
      omega
    have h2 : 2 ^ L = 2 ^ (l i) * 2 ^ (L - l i) := by
      rw [← pow_add, Nat.add_sub_cancel' (hlL i)]
    rw [hA i, h2] at h1
    exact Nat.lt_of_mul_lt_mul_right h1
  refine ⟨fun i => bits (l i) (A i), fun i => bits_length _ _, ?_⟩
  intro i j ⟨t, ht⟩
  simp only at ht
  have hlen : l j = l i + t.length := by
    have := congrArg List.length ht
    simpa [bits_length] using this
  set r := t.length with hr
  rw [hlen, bits_add] at ht
  have hlen2 : (bits (l i) (A j / 2 ^ r)).length = (bits (l i) (A i)).length := by
    simp [bits_length]
  have h1 := List.append_inj_left ht hlen2
  have e := bits_inj _ _ _ h1
  have hAj : A j / 2 ^ r < 2 ^ (l i) := by
    have := hAlt j
    rw [hlen, pow_add] at this
    exact Nat.div_lt_of_lt_mul (by rwa [mul_comm] at this)
  rw [Nat.mod_eq_of_lt hAj, Nat.mod_eq_of_lt (hAlt i)] at e
  -- e : A j / 2 ^ r = A i
  set P := 2 ^ (L - l j) with hP
  set Q := 2 ^ r with hQ
  have hPpos : 0 < P := by positivity
  have hQpos : 0 < Q := by positivity
  have hQP : 2 ^ (L - l i) = Q * P := by
    rw [hQ, hP, ← pow_add]; congr 1; have := hlL j; omega
  have hai : a i = A i * (Q * P) := by rw [hA i, hQP]
  have haj : a j = A j * P := hA j
  have hdm := Nat.div_add_mod (A j) Q
  have hmod := Nat.mod_lt (A j) hQpos
  rw [e] at hdm
  have hle : a i ≤ a j := by
    rw [hai, haj, ← hdm, ← mul_assoc, mul_comm (A i) Q]
    exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
  have hlt : a j < a i + 2 ^ (L - l i) := by
    rw [hQP, hai, haj, ← hdm, ← mul_assoc, mul_comm (A i) Q, ← add_mul]
    exact Nat.mul_lt_mul_of_pos_right (by omega) hPpos
  by_contra hne
  have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
  have : prec i j ∨ prec j i := by simp only [prec]; omega
  rcases this with h | h
  · have := key1 j i h; omega
  · have := key1 i j h
    have : 0 < 2 ^ (L - l j) := by positivity
    omega

lemma lower {m : ℕ} (p : Fin m → ℝ) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1)
    (c : Fin m → List Bool) (hc : ∀ i j, (∃ t : List Bool, c j = c i ++ t) → i = j) :
    ∑ i, p i * (-Real.log (p i) / Real.log 2) ≤ ∑ i, p i * ((c i).length : ℝ) := by
  classical
  have hinj : Function.Injective c := fun i j h => (hc i j ⟨[], by simp [h]⟩)
  have hpf : InformationTheory.IsPrefixFree
      ((Finset.univ.image c : Finset (List Bool)) : Set (List Bool)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    obtain ⟨t, ht⟩ := hxy
    rw [hc i j ⟨t, ht.symm⟩]
  have hk := InformationTheory.IsPrefixFree.finsetSum_one_div_card_pow_length_le_one hpf
  rw [Finset.sum_image (fun i _ j _ h => hinj h)] at hk
  simp only [Fintype.card_bool, Nat.cast_ofNat] at hk
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpt : ∀ i, p i * (-Real.log (p i)) - p i * ((c i).length * Real.log 2) ≤
      ((1 : ℝ) / 2) ^ (c i).length - p i := by
    intro i
    have hpi := hp i
    have hq : 0 < ((1 : ℝ) / 2) ^ (c i).length := by positivity
    have h1 := Real.log_le_sub_one_of_pos (div_pos hq hpi)
    have hl12 : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    rw [Real.log_div hq.ne' hpi.ne', Real.log_pow, hl12] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hpi.le
    have h3 : p i * (((1 : ℝ) / 2) ^ (c i).length / p i - 1) =
        ((1 : ℝ) / 2) ^ (c i).length - p i := by
      field_simp
    rw [h3] at h2
    linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hs] at hsum
  have hE : ∑ i, p i * (-Real.log (p i)) ≤ Real.log 2 * ∑ i, p i * ((c i).length : ℝ) := by
    have : ∑ i, p i * (((c i).length : ℝ) * Real.log 2) =
        Real.log 2 * ∑ i, p i * ((c i).length : ℝ) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _ => by ring)
    linarith
  have : ∑ i, p i * (-Real.log (p i) / Real.log 2) =
      (∑ i, p i * (-Real.log (p i))) / Real.log 2 := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun i _ => by ring)
  rw [this, div_le_iff₀ hl2]
  linarith

lemma upper {m : ℕ} (p : Fin m → ℝ) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1) :
    ∃ c : Fin m → List Bool, (∀ i j, (∃ t : List Bool, c j = c i ++ t) → i = j) ∧
      ∑ i, p i * ((c i).length : ℝ) < ∑ i, p i * (-Real.log (p i) / Real.log 2) + 1 := by
  classical
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp1 : ∀ i, p i ≤ 1 := by
    intro i; rw [← hs]
    exact Finset.single_le_sum (fun j _ => (hp j).le) (Finset.mem_univ i)
  set x : Fin m → ℝ := fun i => -Real.log (p i) / Real.log 2 with hx
  have hx0 : ∀ i, 0 ≤ x i := by
    intro i
    simp only [hx]
    apply div_nonneg _ hl2.le
    have := Real.log_nonpos (hp i).le (hp1 i)
    linarith
  let l : Fin m → ℕ := fun i => Nat.ceil (x i)
  have hlx : ∀ i, x i ≤ (l i : ℝ) := fun i => Nat.le_ceil _
  have hlx1 : ∀ i, (l i : ℝ) < x i + 1 := fun i => Nat.ceil_lt_add_one (hx0 i)
  have hq : ∀ i, ((1 : ℝ) / 2) ^ (l i) ≤ p i := by
    intro i
    have hpi := hp i
    have h1 : -Real.log (p i) ≤ (l i : ℝ) * Real.log 2 := by
      have := hlx i
      simp only [hx] at this
      rwa [div_le_iff₀ hl2] at this
    have h2 : 0 ≤ Real.log (p i * 2 ^ (l i)) := by
      rw [Real.log_mul hpi.ne' (by positivity), Real.log_pow]
      linarith
    rw [Real.log_nonneg_iff (by positivity)] at h2
    rw [div_pow, one_pow, div_le_iff₀ (by positivity)]
    exact h2
  have hk : ∑ i, ((1 : ℝ) / 2) ^ (l i) ≤ 1 := by
    calc ∑ i, ((1 : ℝ) / 2) ^ (l i) ≤ ∑ i, p i := Finset.sum_le_sum (fun i _ => hq i)
      _ = 1 := hs
  obtain ⟨c, hcl, hc⟩ := kraft_converse l hk
  refine ⟨c, hc, ?_⟩
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hs
    · exact ⟨⟨0, h⟩, Finset.mem_univ _⟩
  calc ∑ i, p i * ((c i).length : ℝ) < ∑ i, p i * (x i + 1) := by
        apply Finset.sum_lt_sum_of_nonempty hne
        intro i _
        rw [hcl i]
        exact mul_lt_mul_of_pos_left (hlx1 i) (hp i)
    _ = ∑ i, p i * x i + 1 := by
        simp only [mul_add, mul_one, Finset.sum_add_distrib, hs]

end PEqualNP.Outside.L_lib_523_aux

open PEqualNP.Outside.L_lib_523_aux in
theorem PEqualNP.Outside.L_lib_523 : ∀ (m h : ℕ) (w : Fin h → ℝ) (p : Fin h → Fin m → ℝ),
  (∀ y, 0 < w y) → (∑ y, w y) = 1 →
  (∀ y i, 0 < p y i) → (∀ y, (∑ i, p y i) = 1) →
  let prefixCode := fun (code : Fin m → List Bool) =>
    ∀ i j, (∃ tail : List Bool, code j = code i ++ tail) → i = j
  let H := ∑ y, w y * (∑ i, p y i * (-Real.log (p y i) / Real.log 2))
  let cost := fun (code : Fin h → Fin m → List Bool) =>
    ∑ y, w y * (∑ i, p y i * ((code y i).length : ℝ))
  (∀ code, (∀ y, prefixCode (code y)) → H ≤ cost code) ∧
    ∃ code, (∀ y, prefixCode (code y)) ∧ cost code < H+1 := by
  intro m h w p hw hws hp hps prefixCode H cost
  refine ⟨?_, ?_⟩
  · intro code hcode
    exact Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left
      (lower (p y) (hp y) (hps y) (code y) (hcode y)) (hw y).le)
  · choose code hcode hlt using fun y => upper (p y) (hp y) (hps y)
    refine ⟨code, hcode, ?_⟩
    have hne : (Finset.univ : Finset (Fin h)).Nonempty := by
      rcases Nat.eq_zero_or_pos h with h0 | h0
      · subst h0; simp at hws
      · exact ⟨⟨0, h0⟩, Finset.mem_univ _⟩
    calc cost code < ∑ y, w y * (∑ i, p y i * (-Real.log (p y i) / Real.log 2) + 1) :=
          Finset.sum_lt_sum_of_nonempty hne (fun y _ => mul_lt_mul_of_pos_left (hlt y) (hw y))
      _ = H + 1 := by
          simp only [H, mul_add, mul_one, Finset.sum_add_distrib, hws]
