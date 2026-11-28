import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_982_aux

open scoped BigOperators

abbrev PG (q : ℕ) := (ZMod q × ZMod q) ⊕ ZMod q ⊕ Unit

def vec {q : ℕ} : PG q → ZMod q × ZMod q × ZMod q
  | Sum.inl (x, y) => (x, y, 1)
  | Sum.inr (Sum.inl x) => (x, 1, 0)
  | Sum.inr (Sum.inr ()) => (1, 0, 0)

def dot3 {q : ℕ} (u v : ZMod q × ZMod q × ZMod q) : ZMod q :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

def cross3 {q : ℕ} (u v : ZMod q × ZMod q × ZMod q) : ZMod q × ZMod q × ZMod q :=
  (u.2.1 * v.2.2 - u.2.2 * v.2.1,
   u.2.2 * v.1 - u.1 * v.2.2,
   u.1 * v.2.1 - u.2.1 * v.1)

def inc {q : ℕ} (p l : PG q) : Prop :=
  dot3 (vec p) (vec l) = 0

instance instDecidableInc {q : ℕ} : DecidableRel (@inc q) := by
  intro p l
  unfold inc
  infer_instance

lemma card_PG (q : ℕ) [NeZero q] : Fintype.card (PG q) = q ^ 2 + q + 1 := by
  simp only [PG, Fintype.card_sum, Fintype.card_prod, ZMod.card, Fintype.card_unit]
  ring

lemma inc_symm {q : ℕ} (p l : PG q) : inc p l ↔ inc l p := by
  unfold inc dot3
  have h : (vec p).1 * (vec l).1 + (vec p).2.1 * (vec l).2.1 + (vec p).2.2 * (vec l).2.2 =
      (vec l).1 * (vec p).1 + (vec l).2.1 * (vec p).2.1 + (vec l).2.2 * (vec p).2.2 := by ring
  rw [h]

lemma dot3_cross3_left {q : ℕ} (u v : ZMod q × ZMod q × ZMod q) :
    dot3 u (cross3 u v) = 0 := by
  unfold dot3 cross3
  ring

lemma dot3_cross3_right {q : ℕ} (u v : ZMod q × ZMod q × ZMod q) :
    dot3 v (cross3 u v) = 0 := by
  unfold dot3 cross3
  ring

lemma cross3_bac_cab {q : ℕ} (x u v : ZMod q × ZMod q × ZMod q)
    (hu : dot3 u x = 0) (hv : dot3 v x = 0) :
    cross3 x (cross3 u v) = (0, 0, 0) := by
  have h1 : (cross3 x (cross3 u v)).1 = (dot3 v x) * u.1 - (dot3 u x) * v.1 := by
    unfold cross3 dot3; ring
  have h2 : (cross3 x (cross3 u v)).2.1 = (dot3 v x) * u.2.1 - (dot3 u x) * v.2.1 := by
    unfold cross3 dot3; ring
  have h3 : (cross3 x (cross3 u v)).2.2 = (dot3 v x) * u.2.2 - (dot3 u x) * v.2.2 := by
    unfold cross3 dot3; ring
  rw [hu, hv] at h1 h2 h3
  ext
  · simpa using h1
  · simpa using h2
  · simpa using h3

lemma eq_of_cross3_vec_eq_zero {q : ℕ} [Fact q.Prime] {p₁ p₂ : PG q}
    (h : cross3 (vec p₁) (vec p₂) = (0, 0, 0)) : p₁ = p₂ := by
  have h1 : (cross3 (vec p₁) (vec p₂)).1 = 0 := congrArg Prod.fst h
  have h2 : (cross3 (vec p₁) (vec p₂)).2.1 = 0 := congrArg (fun z => z.2.1) h
  have h3 : (cross3 (vec p₁) (vec p₂)).2.2 = 0 := congrArg (fun z => z.2.2) h
  rcases p₁ with ⟨x₁, y₁⟩ | x₁ | ⟨⟩ <;> rcases p₂ with ⟨x₂, y₂⟩ | x₂ | ⟨⟩
  · simp only [vec, cross3, mul_one, one_mul] at h1 h2
    have hy : y₁ = y₂ := sub_eq_zero.mp h1
    have hx : x₁ = x₂ := (sub_eq_zero.mp h2).symm
    subst hx; subst hy; rfl
  · simp [vec, cross3] at h1
  · simp [vec, cross3] at h2
  · simp [vec, cross3] at h1
  · simp [vec, cross3] at h3
    have hx : x₁ = x₂ := sub_eq_zero.mp h3
    subst hx; rfl
  · simp [vec, cross3] at h3
  · simp [vec, cross3] at h2
  · simp [vec, cross3] at h3
  · rfl

def normalize3 {q : ℕ} [Fact q.Prime] (w : ZMod q × ZMod q × ZMod q) : PG q :=
  if w.2.2 ≠ 0 then Sum.inl (w.1 / w.2.2, w.2.1 / w.2.2)
  else if w.2.1 ≠ 0 then Sum.inr (Sum.inl (w.1 / w.2.1))
  else Sum.inr (Sum.inr ())

lemma normalize3_spec {q : ℕ} [Fact q.Prime] {w : ZMod q × ZMod q × ZMod q}
    (hw : w ≠ (0, 0, 0)) :
    ∃ c : ZMod q, c ≠ 0 ∧ vec (normalize3 w) = (c * w.1, c * w.2.1, c * w.2.2) := by
  by_cases h3 : w.2.2 ≠ 0
  · refine ⟨w.2.2⁻¹, inv_ne_zero h3, ?_⟩
    simp [normalize3, h3, vec, div_eq_inv_mul, inv_mul_cancel₀ h3]
  · push Not at h3
    by_cases h2 : w.2.1 ≠ 0
    · refine ⟨w.2.1⁻¹, inv_ne_zero h2, ?_⟩
      simp [normalize3, h3, h2, vec, div_eq_inv_mul, inv_mul_cancel₀ h2]
    · push Not at h2
      have h1 : w.1 ≠ 0 := by
        intro h1
        apply hw
        ext
        · exact h1
        · exact h2
        · exact h3
      refine ⟨w.1⁻¹, inv_ne_zero h1, ?_⟩
      simp only [normalize3, h3, h2, ne_eq, not_true_eq_false, ↓reduceIte, vec,
        inv_mul_cancel₀ h1, mul_zero]

lemma card_common_inc {q : ℕ} [Fact q.Prime] {p₁ p₂ : PG q} (hne : p₁ ≠ p₂) :
    ((Finset.univ : Finset (PG q)).filter (fun l => inc p₁ l ∧ inc p₂ l)).card = 1 := by
  let w := cross3 (vec p₁) (vec p₂)
  have hw : w ≠ (0, 0, 0) := fun h0 => hne (eq_of_cross3_vec_eq_zero h0)
  let l₀ := normalize3 w
  obtain ⟨c, hc, hl₀⟩ := normalize3_spec hw
  have hmem : inc p₁ l₀ ∧ inc p₂ l₀ := by
    constructor
    · unfold inc dot3
      rw [hl₀]
      have : (vec p₁).1 * (c * w.1) + (vec p₁).2.1 * (c * w.2.1) + (vec p₁).2.2 * (c * w.2.2) =
          c * dot3 (vec p₁) w := by unfold dot3; ring
      rw [this, dot3_cross3_left, mul_zero]
    · unfold inc dot3
      rw [hl₀]
      have : (vec p₂).1 * (c * w.1) + (vec p₂).2.1 * (c * w.2.1) + (vec p₂).2.2 * (c * w.2.2) =
          c * dot3 (vec p₂) w := by unfold dot3; ring
      rw [this, dot3_cross3_right, mul_zero]
  have heq : (Finset.univ : Finset (PG q)).filter (fun l => inc p₁ l ∧ inc p₂ l) = {l₀} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro ⟨h1, h2⟩
      have hbc := cross3_bac_cab (vec l) (vec p₁) (vec p₂) h1 h2
      have hcl : cross3 (vec l) (vec l₀) = (0, 0, 0) := by
        rw [hl₀]
        have h1' : (cross3 (vec l) (c * w.1, c * w.2.1, c * w.2.2)).1 =
            c * (cross3 (vec l) w).1 := by unfold cross3; ring
        have h2' : (cross3 (vec l) (c * w.1, c * w.2.1, c * w.2.2)).2.1 =
            c * (cross3 (vec l) w).2.1 := by unfold cross3; ring
        have h3' : (cross3 (vec l) (c * w.1, c * w.2.1, c * w.2.2)).2.2 =
            c * (cross3 (vec l) w).2.2 := by unfold cross3; ring
        rw [hbc] at h1' h2' h3'
        ext
        · simpa using h1'
        · simpa using h2'
        · simpa using h3'
      exact eq_of_cross3_vec_eq_zero hcl
    · rintro rfl
      exact hmem
  rw [heq, Finset.card_singleton]

lemma card_filter_PG {q : ℕ} [NeZero q] (P : PG q → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (PG q)).filter P).card =
      ((Finset.univ : Finset (ZMod q × ZMod q)).filter (fun xy => P (Sum.inl xy))).card +
      ((Finset.univ : Finset (ZMod q)).filter (fun x => P (Sum.inr (Sum.inl x)))).card +
      (if P (Sum.inr (Sum.inr ())) then 1 else 0) := by
  have h1 : (Finset.univ : Finset (PG q)).filter P =
      ((Finset.univ : Finset (ZMod q × ZMod q)).filter (fun xy => P (Sum.inl xy))).map
        ⟨Sum.inl, Sum.inl_injective⟩ ∪
      (((Finset.univ : Finset (ZMod q)).filter (fun x => P (Sum.inr (Sum.inl x)))).map
        ⟨fun x => Sum.inr (Sum.inl x), fun _ _ h => Sum.inl.inj (Sum.inr.inj h)⟩ ∪
      ((Finset.univ : Finset Unit).filter (fun u => P (Sum.inr (Sum.inr u)))).map
        ⟨fun u => Sum.inr (Sum.inr u), fun _ _ h => Sum.inr.inj (Sum.inr.inj h)⟩) := by
    ext p
    rcases p with ⟨x, y⟩ | x | ⟨⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      constructor
      · intro h; exact Or.inl ⟨(x, y), h, rfl⟩
      · rintro (⟨⟨x', y'⟩, h, heq⟩ | ⟨a, _, heq⟩ | ⟨u, _, heq⟩)
        · cases heq; exact h
        · cases heq
        · cases heq
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      constructor
      · intro h; exact Or.inr (Or.inl ⟨x, h, rfl⟩)
      · rintro (⟨⟨x', y'⟩, _, heq⟩ | ⟨a, h, heq⟩ | ⟨u, _, heq⟩)
        · cases heq
        · cases heq; exact h
        · cases heq
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      constructor
      · intro h; exact Or.inr (Or.inr ⟨(), h, rfl⟩)
      · rintro (⟨⟨x', y'⟩, _, heq⟩ | ⟨a, _, heq⟩ | ⟨u, h, heq⟩)
        · cases heq
        · cases heq
        · cases u; exact h
  rw [h1, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
  · simp only [Finset.card_map]
    have hu : ((Finset.univ : Finset Unit).filter (fun u => P (Sum.inr (Sum.inr u)))).card =
        if P (Sum.inr (Sum.inr ())) then 1 else 0 := by
      by_cases hP : P (Sum.inr (Sum.inr ()))
      · simp [hP]
      · simp [hP]
    rw [hu]
    omega
  · rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at ha hb
    rcases ha with ⟨_, _, rfl⟩
    rcases hb with ⟨_, _, h⟩
    cases h
  · rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_map, Finset.mem_union, Function.Embedding.coeFn_mk] at ha hb
    rcases ha with ⟨_, _, rfl⟩
    rcases hb with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h

lemma card_linear_pair {q : ℕ} [Fact q.Prime] (a b c : ZMod q) (h : a ≠ 0 ∨ b ≠ 0) :
    ((Finset.univ : Finset (ZMod q × ZMod q)).filter (fun xy => a * xy.1 + b * xy.2 + c = 0)).card = q := by
  conv_rhs => rw [← ZMod.card q, ← Finset.card_univ]
  rcases h with ha | hb
  · refine Finset.card_bij (fun xy _ => xy.2) ?_ ?_ ?_
    · intro xy _; exact Finset.mem_univ _
    · intro xy₁ h₁ xy₂ h₂ heq
      have h1' : a * xy₁.1 + b * xy₁.2 + c = 0 := (Finset.mem_filter.mp h₁).2
      have h2' : a * xy₂.1 + b * xy₂.2 + c = 0 := (Finset.mem_filter.mp h₂).2
      have hx : xy₁.1 = xy₂.1 := by
        apply mul_left_cancel₀ ha
        rw [heq] at h1'
        linear_combination h1' - h2'
      exact Prod.ext hx heq
    · intro y _
      refine ⟨(-(b * y + c) / a, y), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      field_simp [ha]
      ring
  · refine Finset.card_bij (fun xy _ => xy.1) ?_ ?_ ?_
    · intro xy _; exact Finset.mem_univ _
    · intro xy₁ h₁ xy₂ h₂ heq
      have h1' : a * xy₁.1 + b * xy₁.2 + c = 0 := (Finset.mem_filter.mp h₁).2
      have h2' : a * xy₂.1 + b * xy₂.2 + c = 0 := (Finset.mem_filter.mp h₂).2
      have hy : xy₁.2 = xy₂.2 := by
        apply mul_left_cancel₀ hb
        rw [heq] at h1'
        linear_combination h1' - h2'
      exact Prod.ext heq hy
    · intro x _
      refine ⟨(x, -(a * x + c) / b), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      field_simp [hb]
      ring

lemma card_linear_single {q : ℕ} [Fact q.Prime] (a c : ZMod q) (ha : a ≠ 0) :
    ((Finset.univ : Finset (ZMod q)).filter (fun x => a * x + c = 0)).card = 1 := by
  have heq : (Finset.univ : Finset (ZMod q)).filter (fun x => a * x + c = 0) = {-c / a} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      have h1 : a * x = -c := by linear_combination h
      rw [eq_div_iff ha, mul_comm]
      exact h1
    · intro h
      rw [h]
      field_simp [ha]
      ring
  rw [heq, Finset.card_singleton]

lemma card_inc {q : ℕ} [Fact q.Prime] (p : PG q) :
    ((Finset.univ : Finset (PG q)).filter (fun l => inc p l)).card = q + 1 := by
  rw [card_filter_PG]
  rcases p with ⟨a, b⟩ | a | ⟨⟩
  · by_cases h : a ≠ 0 ∨ b ≠ 0
    · have h1 : ((Finset.univ : Finset (ZMod q × ZMod q)).filter
          (fun xy => inc (Sum.inl (a, b)) (Sum.inl xy))).card = q := by
        simpa [inc, dot3, vec] using card_linear_pair a b 1 h
      rw [h1]
      by_cases ha : a = 0
      · have hb : b ≠ 0 := h.resolve_left (not_not.mpr ha)
        have h2 : ((Finset.univ : Finset (ZMod q)).filter
            (fun x => inc (Sum.inl (a, b)) (Sum.inr (Sum.inl x)))).card = 0 := by
          simp [inc, dot3, vec, ha, hb]
        have h3 : inc (Sum.inl (a, b)) (Sum.inr (Sum.inr ())) := by
          simp [inc, dot3, vec, ha]
        simp [h2, h3]
      · have h2 : ((Finset.univ : Finset (ZMod q)).filter
            (fun x => inc (Sum.inl (a, b)) (Sum.inr (Sum.inl x)))).card = 1 := by
          simpa [inc, dot3, vec] using card_linear_single a b ha
        have h3 : ¬ inc (Sum.inl (a, b)) (Sum.inr (Sum.inr ())) := by
          simp [inc, dot3, vec, ha]
        simp [h2, h3]
    · push Not at h
      rcases h with ⟨ha, hb⟩
      have h1 : ((Finset.univ : Finset (ZMod q × ZMod q)).filter
          (fun xy => inc (Sum.inl (a, b)) (Sum.inl xy))).card = 0 := by
        simp [inc, dot3, vec, ha, hb]
      have h2 : ((Finset.univ : Finset (ZMod q)).filter
          (fun x => inc (Sum.inl (a, b)) (Sum.inr (Sum.inl x)))).card = q := by
        simp [inc, dot3, vec, ha, hb, ZMod.card]
      have h3 : inc (Sum.inl (a, b)) (Sum.inr (Sum.inr ())) := by
        simp [inc, dot3, vec, ha, hb]
      simp [h1, h2, h3]
  · have h1 : ((Finset.univ : Finset (ZMod q × ZMod q)).filter
        (fun xy => inc (Sum.inr (Sum.inl a)) (Sum.inl xy))).card = q := by
      simpa [inc, dot3, vec] using card_linear_pair a 1 0 (Or.inr one_ne_zero)
    rw [h1]
    by_cases ha : a = 0
    · have h2 : ((Finset.univ : Finset (ZMod q)).filter
          (fun x => inc (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl x)))).card = 0 := by
        simp [inc, dot3, vec, ha]
      have h3 : inc (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr ())) := by
        simp [inc, dot3, vec, ha]
      simp [h2, h3]
    · have h2 : ((Finset.univ : Finset (ZMod q)).filter
          (fun x => inc (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl x)))).card = 1 := by
        simpa [inc, dot3, vec] using card_linear_single a 1 ha
      have h3 : ¬ inc (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr ())) := by
        simp [inc, dot3, vec, ha]
      simp [h2, h3]
  · have h1 : ((Finset.univ : Finset (ZMod q × ZMod q)).filter
        (fun xy => inc (Sum.inr (Sum.inr ())) (Sum.inl xy))).card = q := by
      have hc := card_linear_pair (1 : ZMod q) 0 0 (Or.inl one_ne_zero)
      simpa [inc, dot3, vec] using hc
    have h2 : ((Finset.univ : Finset (ZMod q)).filter
        (fun x => inc (Sum.inr (Sum.inr ())) (Sum.inr (Sum.inl x)))).card = 1 := by
      have hc := card_linear_single (1 : ZMod q) 0 one_ne_zero
      simpa [inc, dot3, vec] using hc
    have h3 : ¬ inc (Sum.inr (Sum.inr ()) : PG q) (Sum.inr (Sum.inr ()) : PG q) := by
      simp [inc, dot3, vec]
    simp [h1, h2, h3]

lemma det_qI_add_J (m : ℕ) (hm : 0 < m) (q : ℝ) :
    Matrix.det (fun i j : Fin m => (if i = j then q else 0) + 1) =
      (q + (m : ℝ)) * q ^ (m - 1) := by
  let z : Fin m := ⟨0, hm⟩
  let M : Matrix (Fin m) (Fin m) ℝ := fun i j => (if i = j then q else 0) + 1
  let L : Matrix (Fin m) (Fin m) ℝ := fun i j => if i = j then 1 else if j = z then -1 else 0
  let R : Matrix (Fin m) (Fin m) ℝ := fun i j => if i = j then 1 else if j = z then 1 else 0
  have hL_tri : L.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hne : i ≠ j := ne_of_lt hij
    have hj : j ≠ z := by
      intro h0
      rw [h0] at hij
      exact Nat.not_lt_zero i.val hij
    simp [L, hne, hj]
  have hR_tri : R.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hne : i ≠ j := ne_of_lt hij
    have hj : j ≠ z := by
      intro h0
      rw [h0] at hij
      exact Nat.not_lt_zero i.val hij
    simp [R, hne, hj]
  have hL_det : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular L hL_tri]
    simp [L]
  have hR_det : R.det = 1 := by
    rw [Matrix.det_of_lowerTriangular R hR_tri]
    simp [R]
  have hLM : ∀ i k : Fin m, (L * M) i k =
      if i = z then (if z = k then q else 0) + 1
      else (if i = k then q else 0) - (if z = k then q else 0) := by
    intro i k
    rw [Matrix.mul_apply]
    by_cases hi : i = z
    · subst hi
      rw [Finset.sum_eq_single z]
      · simp [L, M]
      · intro b _ hbz
        simp [L, hbz.symm, hbz]
      · intro h; exact absurd (Finset.mem_univ z) h
    · have hsplit : ∑ b : Fin m, L i b * M b k = L i i * M i k + L i z * M z k := by
        rw [← Finset.sum_subset (s₁ := {i, z}) (Finset.subset_univ _)]
        · rw [Finset.sum_pair hi]
        · intro b _ hb
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
          simp [L, Ne.symm hb.1, hb.2]
      rw [hsplit]
      simp [L, M, hi, Ne.symm hi]
      ring
  have hU_entry : ∀ i j : Fin m, (L * M * R) i j =
      if j = z then (if i = z then q + (m : ℝ) else 0)
      else if i = z then 1
      else if i = j then q else 0 := by
    intro i j
    rw [Matrix.mul_apply]
    by_cases hj : j = z
    · subst hj
      have hRcol : ∀ k : Fin m, R k z = 1 := by
        intro k
        by_cases hk : k = z <;> simp [R, hk]
      simp only [hRcol, mul_one, ↓reduceIte]
      by_cases hi : i = z
      · subst hi
        simp only [hLM, ↓reduceIte, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      · simp only [hLM, hi, ↓reduceIte, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
          sub_self]
    · rw [Finset.sum_eq_single j]
      · simp only [R, ↓reduceIte, mul_one, hLM, hj]
        by_cases hi : i = z
        · subst hi
          simp [Ne.symm hj]
        · simp [hi, Ne.symm hj]
      · intro k _ hkj
        simp [R, hkj, hj]
      · intro h; exact absurd (Finset.mem_univ j) h
  have hU_tri : (L * M * R).BlockTriangular id := by
    intro i j hij
    have hne : i ≠ j := ne_of_gt hij
    have hi : i ≠ z := by
      intro h0
      rw [h0] at hij
      exact Nat.not_lt_zero j.val hij
    rw [hU_entry]
    split_ifs <;> simp_all
  have hU_det : (L * M * R).det = (q + (m : ℝ)) * q ^ (m - 1) := by
    rw [Matrix.det_of_upperTriangular hU_tri]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ z)]
    have hz : (L * M * R) z z = q + (m : ℝ) := by simp [hU_entry]
    have hrest : ∏ i ∈ Finset.univ.erase z, (L * M * R) i i = q ^ (m - 1) := by
      have hcongr : ∏ i ∈ Finset.univ.erase z, (L * M * R) i i =
          ∏ _i ∈ Finset.univ.erase z, q := by
        apply Finset.prod_congr rfl
        intro i hi
        have hne : i ≠ z := (Finset.mem_erase.mp hi).1
        simp [hU_entry, hne]
      rw [hcongr, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ z),
        Finset.card_univ, Fintype.card_fin]
    rw [hz, hrest]
  have hdet_eq : (L * M * R).det = M.det := by
    rw [Matrix.det_mul, Matrix.det_mul, hL_det, hR_det, one_mul, mul_one]
  rw [← hdet_eq, hU_det]

lemma am_gm_finset {α : Type*} [DecidableEq α] :
    ∀ (n : ℕ) (s : Finset α) (f : α → ℝ),
      s.card = n → (∀ x ∈ s, 0 ≤ f x) →
      ∏ x ∈ s, f x ≤ ((∑ x ∈ s, f x) / (n : ℝ)) ^ n := by
  intro n
  induction n with
  | zero =>
    intro s f hs _
    rw [Finset.card_eq_zero.mp hs]
    simp
  | succ k ih =>
    intro s f hs hf
    rcases k with _ | k'
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
      simp
    · set n := k' + 2 with hn_def
      have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
      let M : ℝ := (∑ x ∈ s, f x) / (n : ℝ)
      have hsum : ∑ x ∈ s, f x = (n : ℝ) * M := by
        dsimp only [M]
        field_simp [hn_pos.ne']
      have hM_nonneg : 0 ≤ M := div_nonneg (Finset.sum_nonneg hf) hn_pos.le
      have hex_le : ∃ a ∈ s, f a ≤ M := by
        by_contra hall
        push Not at hall
        have hgt : ∑ x ∈ s, M < ∑ x ∈ s, f x :=
          Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp (by omega)) hall
        simp only [Finset.sum_const, hs, nsmul_eq_mul] at hgt
        linarith
      have hex_ge : ∃ b ∈ s, M ≤ f b := by
        by_contra hall
        push Not at hall
        have hlt : ∑ x ∈ s, f x < ∑ x ∈ s, M :=
          Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp (by omega)) hall
        simp only [Finset.sum_const, hs, nsmul_eq_mul] at hlt
        linarith
      obtain ⟨a, ha, hfa⟩ := hex_le
      obtain ⟨b, hb, hfb⟩ := hex_ge
      have hcard_erase : (s.erase a).card = k' + 1 := by
        rw [Finset.card_erase_of_mem ha, hs]
        omega
      by_cases hab : a = b
      · subst hab
        have hfaM : f a = M := le_antisymm hfa hfb
        rw [← Finset.mul_prod_erase s f ha, hfaM]
        have hsum_er : ∑ x ∈ s.erase a, f x = ((k' + 1 : ℕ) : ℝ) * M := by
          have := Finset.add_sum_erase s f ha
          rw [hfaM, hsum] at this
          push_cast [hn_def] at this ⊢
          linarith
        have hih := ih (s.erase a) f hcard_erase (fun x hx => hf x (Finset.mem_of_mem_erase hx))
        rw [hsum_er] at hih
        have hdiv : ((k' + 1 : ℕ) : ℝ) * M / ((k' + 1 : ℕ) : ℝ) = M := by
          have hpos' : ((k' + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          field_simp [hpos']
        rw [hdiv] at hih
        rw [pow_succ']
        exact mul_le_mul_of_nonneg_left hih hM_nonneg
      · have hb_er : b ∈ s.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
        let g : α → ℝ := fun x => if x = b then f a + f b - M else f x
        have hg_nonneg : ∀ x ∈ s.erase a, 0 ≤ g x := by
          intro x hx
          dsimp only [g]
          split_ifs with hxb
          · have := hf a ha; linarith
          · exact hf x (Finset.mem_of_mem_erase hx)
        have hsum_g : ∑ x ∈ s.erase a, g x = ((k' + 1 : ℕ) : ℝ) * M := by
          rw [← Finset.add_sum_erase (s.erase a) g hb_er]
          have hgb : g b = f a + f b - M := by simp [g]
          have hrest : ∑ x ∈ (s.erase a).erase b, g x = ∑ x ∈ (s.erase a).erase b, f x := by
            apply Finset.sum_congr rfl
            intro x hx
            have hne : x ≠ b := (Finset.mem_erase.mp hx).1
            simp [g, hne]
          have htot : f a + (f b + ∑ x ∈ (s.erase a).erase b, f x) = ∑ x ∈ s, f x := by
            rw [Finset.add_sum_erase (s.erase a) f hb_er, Finset.add_sum_erase s f ha]
          rw [hgb, hrest]
          push_cast [hn_def] at hsum ⊢
          linarith
        have hprod_le : ∏ x ∈ s, f x ≤ M * ∏ x ∈ s.erase a, g x := by
          rw [← Finset.mul_prod_erase s f ha, ← Finset.mul_prod_erase (s.erase a) f hb_er,
              ← Finset.mul_prod_erase (s.erase a) g hb_er]
          have hgb : g b = f a + f b - M := by simp [g]
          have hrest : ∏ x ∈ (s.erase a).erase b, g x = ∏ x ∈ (s.erase a).erase b, f x := by
            apply Finset.prod_congr rfl
            intro x hx
            have hne : x ≠ b := (Finset.mem_erase.mp hx).1
            simp [g, hne]
          rw [hgb, hrest]
          have hprod_nn : 0 ≤ ∏ x ∈ (s.erase a).erase b, f x :=
            Finset.prod_nonneg (fun x hx => hf x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)))
          have hpair : f a * f b ≤ M * (f a + f b - M) := by
            nlinarith
          calc f a * (f b * ∏ x ∈ (s.erase a).erase b, f x)
              = (f a * f b) * ∏ x ∈ (s.erase a).erase b, f x := by ring
            _ ≤ (M * (f a + f b - M)) * ∏ x ∈ (s.erase a).erase b, f x :=
                mul_le_mul_of_nonneg_right hpair hprod_nn
            _ = M * ((f a + f b - M) * ∏ x ∈ (s.erase a).erase b, f x) := by ring
        have hih := ih (s.erase a) g hcard_erase hg_nonneg
        rw [hsum_g] at hih
        have hdiv : ((k' + 1 : ℕ) : ℝ) * M / ((k' + 1 : ℕ) : ℝ) = M := by
          have hpos' : ((k' + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          field_simp [hpos']
        rw [hdiv] at hih
        calc ∏ x ∈ s, f x ≤ M * ∏ x ∈ s.erase a, g x := hprod_le
          _ ≤ M * M ^ (k' + 1) := mul_le_mul_of_nonneg_left hih hM_nonneg
          _ = M ^ n := by rw [← pow_succ']

lemma pow_sum_le_card_mul_prod {β : Type*} [DecidableEq β] (K : Finset β) (a : β → ℕ) :
    let S := ∑ j ∈ K, a j
    (S : ℝ) ^ S ≤ (K.card : ℝ) ^ S * ∏ j ∈ K, (a j : ℝ) ^ (a j) := by
  intro S
  by_cases hS : S = 0
  · rw [hS]
    simp only [Nat.cast_zero, pow_zero, one_mul]
    have h1 : ∀ j ∈ K, (a j : ℝ) ^ (a j) = 1 := by
      intro j hj
      have h0 : a j = 0 := (Finset.sum_eq_zero_iff.mp hS) j hj
      simp [h0]
    rw [Finset.prod_eq_one h1]
  · have hS_pos : 0 < S := Nat.pos_of_ne_zero hS
    let Kpos := K.filter (fun j => 0 < a j)
    let T := Σ j : {j // j ∈ Kpos}, Fin (a j.1)
    have hcardT : (Finset.univ : Finset T).card = S := by
      simp only [T, Finset.card_univ, Fintype.card_sigma, Fintype.card_fin]
      rw [Finset.sum_coe_sort Kpos a]
      dsimp only [S]
      apply Finset.sum_subset (Finset.filter_subset _ K)
      intro j hj hnot
      have h0 : ¬ 0 < a j := by simpa [Kpos, hj] using hnot
      omega
    let f : T → ℝ := fun t => (S : ℝ) / (a t.1.1 : ℝ)
    have hf_nn : ∀ t ∈ (Finset.univ : Finset T), 0 ≤ f t := by
      intro t _
      dsimp only [f]
      positivity
    have ham := am_gm_finset S Finset.univ f hcardT hf_nn
    have hsum_f : ∑ t : T, f t = (Kpos.card : ℝ) * (S : ℝ) := by
      rw [Fintype.sum_sigma]
      have hinner : ∀ j : {j // j ∈ Kpos}, ∑ _x : Fin (a j.1), f ⟨j, _x⟩ = (S : ℝ) := by
        intro j
        have haj : 0 < a j.1 := (Finset.mem_filter.mp j.2).2
        have haj_r : (a j.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr haj.ne'
        simp only [f, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp [haj_r]
      simp only [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    have hprod_f : ∏ t : T, f t = (S : ℝ) ^ S / ∏ j ∈ K, (a j : ℝ) ^ (a j) := by
      rw [Fintype.prod_sigma]
      have hinner : ∀ j : {j // j ∈ Kpos},
          ∏ _x : Fin (a j.1), f ⟨j, _x⟩ = (S : ℝ) ^ (a j.1) / (a j.1 : ℝ) ^ (a j.1) := by
        intro j
        simp only [f, Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow]
      simp only [hinner]
      rw [Finset.prod_coe_sort Kpos (fun j => (S : ℝ) ^ (a j) / (a j : ℝ) ^ (a j)),
          Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
      have hsumKpos : ∑ j ∈ Kpos, a j = S := by
        dsimp only [S]
        apply Finset.sum_subset (Finset.filter_subset _ K)
        intro j hj hnot
        have h0 : ¬ 0 < a j := by simpa [Kpos, hj] using hnot
        omega
      have hprodKpos : ∏ j ∈ Kpos, (a j : ℝ) ^ (a j) = ∏ j ∈ K, (a j : ℝ) ^ (a j) := by
        apply Finset.prod_subset (Finset.filter_subset _ K)
        intro j hj hnot
        have h0 : a j = 0 := by
          have : ¬ 0 < a j := by simpa [Kpos, hj] using hnot
          omega
        simp [h0]
      rw [hsumKpos, hprodKpos]
    have hprod_pos : 0 < ∏ j ∈ K, (a j : ℝ) ^ (a j) := by
      apply Finset.prod_pos
      intro j _
      by_cases h0 : a j = 0
      · simp [h0]
      · have : (0 : ℝ) < (a j : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
        positivity
    rw [hprod_f, hsum_f] at ham
    have hS_r : (S : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hS
    have hdiv : (Kpos.card : ℝ) * (S : ℝ) / (S : ℝ) = (Kpos.card : ℝ) := by
      field_simp [hS_r]
    rw [hdiv] at ham
    have hKle : (Kpos.card : ℝ) ≤ (K.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ K)
    have hpow_le : (Kpos.card : ℝ) ^ S ≤ (K.card : ℝ) ^ S :=
      pow_le_pow_left₀ (by positivity) hKle S
    have hle : (S : ℝ) ^ S / ∏ j ∈ K, (a j : ℝ) ^ (a j) ≤ (K.card : ℝ) ^ S :=
      le_trans ham hpow_le
    exact (div_le_iff₀ hprod_pos).mp hle

lemma prod_le_prod_nonneg {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact mul_le_mul (hfg a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => hfg i (Finset.mem_insert_of_mem hi)))
      (Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
      (le_trans (hf a (Finset.mem_insert_self a s)) (hfg a (Finset.mem_insert_self a s)))

noncomputable def avail {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (σ π : Equiv.Perm (Fin m)) (k : Fin m) : ℕ :=
  ((Finset.univ : Finset (Fin m)).filter
    (fun r => H r (σ k) = 1 ∧ ∀ t : Fin m, t < k → π (σ t) ≠ r)).card

lemma prefix_telescope {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ)
    (P : Finset (Equiv.Perm (Fin m))) (hP : ∀ π ∈ P, ∀ i : Fin m, H (π i) i = 1)
    (σ : Equiv.Perm (Fin m)) :
    ∀ (r : ℕ) (hr : r ≤ m),
      let k := m - r
      ∀ (pref : Fin k → Fin m),
        let Q := P.filter (fun π => ∀ t : Fin k, π (σ ⟨t.val, by omega⟩) = pref t)
        (Q.card : ℝ) ^ Q.card ≤
          ∏ π ∈ Q, ∏ t ∈ (Finset.univ : Finset (Fin m)).filter (fun t => k ≤ t.val),
            (avail H σ π t : ℝ) := by
  intro r
  induction r with
  | zero =>
    intro _ k pref Q
    have hfilt : (Finset.univ : Finset (Fin m)).filter (fun t : Fin m => k ≤ t.val) = ∅ := by
      ext t
      simp only [k, Nat.sub_zero, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_le]
      exact t.isLt
    rw [hfilt]
    simp only [Finset.prod_empty, Finset.prod_const_one]
    have hcard : Q.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro π₁ h₁ π₂ h₂
      have hp1 := (Finset.mem_filter.mp h₁).2
      have hp2 := (Finset.mem_filter.mp h₂).2
      ext i
      have hσ : σ (σ.symm i) = i := σ.apply_symm_apply i
      rw [← hσ]
      let t : Fin k := ⟨(σ.symm i).val, by omega⟩
      have h1' := hp1 t
      have h2' := hp2 t
      have hfin : (⟨t.val, by omega⟩ : Fin m) = σ.symm i := Fin.ext rfl
      rw [hfin] at h1' h2'
      exact congrArg Fin.val (h1'.trans h2'.symm)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with h0 | h1
    · simp [h0]
    · simp [h1]
  | succ r ih =>
    intro hr k pref Q
    have hk_lt : k < m := by omega
    have hk_succ : m - r = k + 1 := by omega
    let kFin : Fin m := ⟨k, hk_lt⟩
    let K : Finset (Fin m) :=
      Finset.univ.filter (fun c => H c (σ kFin) = 1 ∧ ∀ t : Fin k, pref t ≠ c)
    let Qsub : Fin m → Finset (Equiv.Perm (Fin m)) :=
      fun c => Q.filter (fun π => π (σ kFin) = c)
    have hQ_mem_K : ∀ π ∈ Q, π (σ kFin) ∈ K := by
      intro π hπ
      have hπP : π ∈ P := (Finset.mem_filter.mp hπ).1
      have hπpref := (Finset.mem_filter.mp hπ).2
      simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hP π hπP (σ kFin), ?_⟩
      intro t heq
      rw [← hπpref t] at heq
      have hσeq : (⟨t.val, by omega⟩ : Fin m) = kFin := σ.injective (π.injective heq)
      have : t.val = k := congrArg Fin.val hσeq
      omega
    have hQ_avail : ∀ π ∈ Q, avail H σ π kFin = K.card := by
      intro π hπ
      have hπpref := (Finset.mem_filter.mp hπ).2
      unfold avail
      congr 1
      ext c
      simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ⟨hH, hall⟩
        refine ⟨hH, ?_⟩
        intro t
        rw [← hπpref t]
        exact hall ⟨t.val, by omega⟩ t.isLt
      · intro ⟨hH, hall⟩
        refine ⟨hH, ?_⟩
        intro t ht
        have hlt : t.val < k := ht
        have := hall ⟨t.val, hlt⟩
        rwa [← hπpref ⟨t.val, hlt⟩] at this
    have hQ_part : Q = K.biUnion Qsub := by
      ext π
      simp only [Finset.mem_biUnion, Qsub, Finset.mem_filter]
      constructor
      · intro hπ
        exact ⟨π (σ kFin), hQ_mem_K π hπ, hπ, rfl⟩
      · rintro ⟨_, _, hπ, _⟩
        exact hπ
    have hQ_disj : Set.PairwiseDisjoint (K : Set (Fin m)) Qsub := by
      intro c₁ _ c₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro π h1 h2
      have e1 := (Finset.mem_filter.mp h1).2
      have e2 := (Finset.mem_filter.mp h2).2
      exact hne (e1.symm.trans e2)
    have hQ_card : Q.card = ∑ c ∈ K, (Qsub c).card := by
      conv_lhs => rw [hQ_part]
      exact Finset.card_biUnion hQ_disj
    have hstep := pow_sum_le_card_mul_prod K (fun c => (Qsub c).card)
    dsimp only at hstep
    rw [← hQ_card] at hstep
    have hsub_ih : ∀ c ∈ K, ((Qsub c).card : ℝ) ^ (Qsub c).card ≤
        (∏ π ∈ Qsub c, ∏ t ∈ (Finset.univ : Finset (Fin m)).filter (fun t => k + 1 ≤ t.val),
          (avail H σ π t : ℝ)) := by
      intro c _
      let pref' : Fin (m - r) → Fin m := fun t =>
        if ht : t.val < k then pref ⟨t.val, ht⟩ else c
      have hih_c := ih (by omega) pref'
      have hQeq : Qsub c = P.filter (fun π => ∀ t : Fin (m - r),
          π (σ ⟨t.val, by omega⟩) = pref' t) := by
        ext π
        simp only [Qsub, Q, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hπP, hpref⟩, hc⟩
          refine ⟨hπP, ?_⟩
          intro t
          dsimp only [pref']
          split_ifs with ht
          · exact hpref ⟨t.val, ht⟩
          · have hteq : t.val = k := by omega
            have hfin : (⟨t.val, by omega⟩ : Fin m) = kFin := Fin.ext hteq
            rw [hfin]
            exact hc
        · rintro ⟨hπP, hpref'⟩
          refine ⟨⟨hπP, ?_⟩, ?_⟩
          · intro t
            have := hpref' ⟨t.val, by omega⟩
            simpa [pref', t.isLt] using this
          · have := hpref' ⟨k, by omega⟩
            have hnot : ¬ k < k := Nat.lt_irrefl k
            simpa [pref', hnot, kFin] using this
      dsimp only at hih_c
      rw [← hQeq] at hih_c
      have hfilt_eq : (Finset.univ : Finset (Fin m)).filter (fun t => m - r ≤ t.val) =
          (Finset.univ : Finset (Fin m)).filter (fun t => k + 1 ≤ t.val) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rwa [hfilt_eq] at hih_c
    have hprod_ih : ∏ c ∈ K, ((Qsub c).card : ℝ) ^ (Qsub c).card ≤
        ∏ c ∈ K, ∏ π ∈ Qsub c,
          ∏ t ∈ (Finset.univ : Finset (Fin m)).filter (fun t => k + 1 ≤ t.val),
            (avail H σ π t : ℝ) := by
      apply prod_le_prod_nonneg
      · intro c _; exact pow_nonneg (Nat.cast_nonneg _) _
      · intro c hc; exact hsub_ih c hc
    have hKpow : (K.card : ℝ) ^ Q.card = ∏ π ∈ Q, (avail H σ π kFin : ℝ) := by
      rw [← Finset.prod_const]
      apply Finset.prod_congr rfl
      intro π hπ
      rw [hQ_avail π hπ]
    have hmerge_Q : ∏ c ∈ K, ∏ π ∈ Qsub c,
        ∏ t ∈ (Finset.univ : Finset (Fin m)).filter (fun t => k + 1 ≤ t.val),
          (avail H σ π t : ℝ) =
        ∏ π ∈ Q, ∏ t ∈ (Finset.univ : Finset (Fin m)).filter (fun t => k + 1 ≤ t.val),
          (avail H σ π t : ℝ) := by
      conv_rhs => rw [hQ_part]
      rw [Finset.prod_biUnion hQ_disj]
    have hmerge_t : ∀ π ∈ Q,
        (avail H σ π kFin : ℝ) *
          ∏ t ∈ (Finset.univ : Finset (Fin m)).filter (fun t => k + 1 ≤ t.val),
            (avail H σ π t : ℝ) =
        ∏ t ∈ (Finset.univ : Finset (Fin m)).filter (fun t => k ≤ t.val),
          (avail H σ π t : ℝ) := by
      intro π _
      have hset : (Finset.univ : Finset (Fin m)).filter (fun t => k ≤ t.val) =
          insert kFin ((Finset.univ : Finset (Fin m)).filter (fun t => k + 1 ≤ t.val)) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Fin.ext_iff, kFin]
        omega
      have hnotmem : kFin ∉ (Finset.univ : Finset (Fin m)).filter (fun t => k + 1 ≤ t.val) := by
        intro hmem
        have := (Finset.mem_filter.mp hmem).2
        dsimp only [kFin] at this
        omega
      rw [hset, Finset.prod_insert hnotmem]
    calc (Q.card : ℝ) ^ Q.card
        ≤ (K.card : ℝ) ^ Q.card * ∏ c ∈ K, ((Qsub c).card : ℝ) ^ (Qsub c).card := hstep
      _ ≤ (K.card : ℝ) ^ Q.card *
            ∏ c ∈ K, ∏ π ∈ Qsub c,
              ∏ t ∈ (Finset.univ : Finset (Fin m)).filter (fun t => k + 1 ≤ t.val),
                (avail H σ π t : ℝ) :=
          mul_le_mul_of_nonneg_left hprod_ih (pow_nonneg (Nat.cast_nonneg _) _)
      _ = (∏ π ∈ Q, (avail H σ π kFin : ℝ)) *
            ∏ π ∈ Q, ∏ t ∈ (Finset.univ : Finset (Fin m)).filter (fun t => k + 1 ≤ t.val),
              (avail H σ π t : ℝ) := by
          rw [hKpow, hmerge_Q]
      _ = ∏ π ∈ Q, ((avail H σ π kFin : ℝ) *
            ∏ t ∈ (Finset.univ : Finset (Fin m)).filter (fun t => k + 1 ≤ t.val),
              (avail H σ π t : ℝ)) := by
          rw [← Finset.prod_mul_distrib]
      _ = ∏ π ∈ Q, ∏ t ∈ (Finset.univ : Finset (Fin m)).filter (fun t => k ≤ t.val),
            (avail H σ π t : ℝ) := by
          apply Finset.prod_congr rfl
          exact hmerge_t

lemma prod_Icc_eq_factorial (d : ℕ) : ∏ k ∈ Finset.Icc 1 d, (k : ℝ) = (d.factorial : ℝ) := by
  induction d with
  | zero => simp
  | succ k ih =>
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hIcc, Finset.prod_insert (by simp), ih, Nat.factorial_succ]
    push_cast
    ring

lemma prod_rank_pow_eq {m d : ℕ} (S : Finset (Fin m)) (i : Fin m) (hi : i ∈ S)
    (hS : S.card = d) :
    (∏ τ : Equiv.Perm (Fin m), ((S.filter (fun j => τ i ≤ τ j)).card : ℝ)) ^ d =
      (d.factorial : ℝ) ^ (Fintype.card (Equiv.Perm (Fin m))) := by
  let rankFn : Equiv.Perm (Fin m) → Fin m → ℕ :=
    fun τ a => (S.filter (fun j => τ a ≤ τ j)).card
  have hrank_mem : ∀ τ : Equiv.Perm (Fin m), ∀ a ∈ S, rankFn τ a ∈ Finset.Icc 1 d := by
    intro τ a ha
    rw [Finset.mem_Icc]
    constructor
    · exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, le_rfl⟩⟩
    · rw [← hS]
      exact Finset.card_le_card (Finset.filter_subset _ S)
  have hrank_inj : ∀ τ : Equiv.Perm (Fin m),
      Set.InjOn (rankFn τ) (S : Set (Fin m)) := by
    intro τ a ha b hb heq
    rcases lt_trichotomy (τ a) (τ b) with hlt | hEq | hgt
    · have hsub : S.filter (fun j => τ b ≤ τ j) ⊂ S.filter (fun j => τ a ≤ τ j) := by
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨a, Finset.mem_filter.mpr ⟨ha, le_rfl⟩,
            by simp only [Finset.mem_filter, not_and, not_le]; intro _; exact hlt⟩
        · intro j hj
          simp only [Finset.mem_filter] at hj ⊢
          exact ⟨hj.1, le_trans hlt.le hj.2⟩
      have := Finset.card_lt_card hsub
      dsimp only [rankFn] at heq
      omega
    · exact τ.injective hEq
    · have hsub : S.filter (fun j => τ a ≤ τ j) ⊂ S.filter (fun j => τ b ≤ τ j) := by
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨b, Finset.mem_filter.mpr ⟨hb, le_rfl⟩,
            by simp only [Finset.mem_filter, not_and, not_le]; intro _; exact hgt⟩
        · intro j hj
          simp only [Finset.mem_filter] at hj ⊢
          exact ⟨hj.1, le_trans hgt.le hj.2⟩
      have := Finset.card_lt_card hsub
      dsimp only [rankFn] at heq
      omega
  have hrank_bij : ∀ τ : Equiv.Perm (Fin m), ∀ k ∈ Finset.Icc 1 d,
      (S.filter (fun a => rankFn τ a = k)).card = 1 := by
    intro τ k hk
    have himg : S.image (rankFn τ) = Finset.Icc 1 d := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
        exact hrank_mem τ a ha
      · rw [Finset.card_image_of_injOn (hrank_inj τ), hS, Nat.card_Icc]
        omega
    have hk_img : k ∈ S.image (rankFn τ) := by rw [himg]; exact hk
    rcases Finset.mem_image.mp hk_img with ⟨a₀, ha₀, hr₀⟩
    have heq : S.filter (fun a => rankFn τ a = k) = {a₀} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro ⟨ha, hr⟩
        exact hrank_inj τ ha ha₀ (hr.trans hr₀.symm)
      · rintro rfl
        exact ⟨ha₀, hr₀⟩
    rw [heq, Finset.card_singleton]
  have hswap_card : ∀ a ∈ S, ∀ k : ℕ,
      ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter (fun τ => rankFn τ a = k)).card =
      ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter (fun τ => rankFn τ i = k)).card := by
    intro a ha k
    refine Finset.card_bij (fun τ _ => τ * Equiv.swap i a) ?_ ?_ ?_
    · intro τ hτ
      have hτk : rankFn τ a = k := (Finset.mem_filter.mp hτ).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hτk]
      dsimp only [rankFn]
      refine Finset.card_bij (fun j _ => Equiv.swap i a j) ?_ ?_ ?_
      · intro j hj
        rcases Finset.mem_filter.mp hj with ⟨hjS, hle⟩
        rw [Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · by_cases h1 : j = i
          · subst h1; simpa using ha
          · by_cases h2 : j = a
            · subst h2; simpa using hi
            · simpa [Equiv.swap_apply_of_ne_of_ne h1 h2] using hjS
        · simpa [Equiv.Perm.mul_apply] using hle
      · intro j₁ _ j₂ _ h; exact (Equiv.swap i a).injective h
      · intro j hj
        rcases Finset.mem_filter.mp hj with ⟨hjS, hle⟩
        refine ⟨Equiv.swap i a j, ?_, by simp⟩
        rw [Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · by_cases h1 : j = i
          · subst h1; simpa using ha
          · by_cases h2 : j = a
            · subst h2; simpa using hi
            · simpa [Equiv.swap_apply_of_ne_of_ne h1 h2] using hjS
        · simpa [Equiv.Perm.mul_apply] using hle
    · intro τ₁ _ τ₂ _ h
      exact mul_right_cancel h
    · intro τ hτ
      refine ⟨τ * Equiv.swap i a, ?_, by simp [mul_assoc]⟩
      have hτk : rankFn τ i = k := (Finset.mem_filter.mp hτ).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hτk]
      dsimp only [rankFn]
      refine Finset.card_bij (fun j _ => Equiv.swap i a j) ?_ ?_ ?_
      · intro j hj
        rcases Finset.mem_filter.mp hj with ⟨hjS, hle⟩
        rw [Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · by_cases h1 : j = i
          · subst h1; simpa using ha
          · by_cases h2 : j = a
            · subst h2; simpa using hi
            · simpa [Equiv.swap_apply_of_ne_of_ne h1 h2] using hjS
        · simpa [Equiv.Perm.mul_apply] using hle
      · intro j₁ _ j₂ _ h; exact (Equiv.swap i a).injective h
      · intro j hj
        rcases Finset.mem_filter.mp hj with ⟨hjS, hle⟩
        refine ⟨Equiv.swap i a j, ?_, by simp⟩
        rw [Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · by_cases h1 : j = i
          · subst h1; simpa using ha
          · by_cases h2 : j = a
            · subst h2; simpa using hi
            · simpa [Equiv.swap_apply_of_ne_of_ne h1 h2] using hjS
        · simpa [Equiv.Perm.mul_apply] using hle
  have hfiber_card : ∀ k ∈ Finset.Icc 1 d,
      d * ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter (fun τ => rankFn τ i = k)).card =
        Fintype.card (Equiv.Perm (Fin m)) := by
    intro k hk
    have h1 : ∑ a ∈ S,
        ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter (fun τ => rankFn τ a = k)).card =
        d * ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter (fun τ => rankFn τ i = k)).card := by
      rw [Finset.sum_congr rfl (fun a ha => hswap_card a ha k), Finset.sum_const, hS, smul_eq_mul]
    have h2 : ∑ a ∈ S,
        ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter (fun τ => rankFn τ a = k)).card =
        ∑ τ : Equiv.Perm (Fin m), (S.filter (fun a => rankFn τ a = k)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    rw [← h1, h2]
    simp only [Finset.sum_congr rfl (fun τ _ => hrank_bij τ k hk), Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one]
  have hprod_fib : ∏ τ : Equiv.Perm (Fin m), (rankFn τ i : ℝ) =
      ∏ k ∈ Finset.Icc 1 d,
        (k : ℝ) ^ ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter (fun τ => rankFn τ i = k)).card := by
    rw [← Finset.prod_fiberwise_of_maps_to (g := fun τ => rankFn τ i)
      (fun τ _ => hrank_mem τ i hi)]
    apply Finset.prod_congr rfl
    intro k _
    have hconst : ∏ τ ∈ (Finset.univ : Finset (Equiv.Perm (Fin m))).filter (fun τ => rankFn τ i = k),
        (rankFn τ i : ℝ) =
        ∏ _τ ∈ (Finset.univ : Finset (Equiv.Perm (Fin m))).filter (fun τ => rankFn τ i = k),
          (k : ℝ) := by
      apply Finset.prod_congr rfl
      intro τ hτ
      rw [(Finset.mem_filter.mp hτ).2]
    rw [hconst, Finset.prod_const]
  have hfact : ∏ k ∈ Finset.Icc 1 d, (k : ℝ) = (d.factorial : ℝ) := prod_Icc_eq_factorial d
  change (∏ τ : Equiv.Perm (Fin m), (rankFn τ i : ℝ)) ^ d = _
  rw [hprod_fib, ← Finset.prod_pow]
  have hcongr : ∏ k ∈ Finset.Icc 1 d,
      ((k : ℝ) ^ ((Finset.univ : Finset (Equiv.Perm (Fin m))).filter (fun τ => rankFn τ i = k)).card) ^ d =
      ∏ k ∈ Finset.Icc 1 d, (k : ℝ) ^ (Fintype.card (Equiv.Perm (Fin m))) := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [← pow_mul, mul_comm, hfiber_card k hk]
  rw [hcongr, Finset.prod_pow, hfact]

lemma bregman_regular {m d : ℕ} (H : Matrix (Fin m) (Fin m) ℝ)
    (h01 : ∀ i j, H i j = 0 ∨ H i j = 1)
    (hcol : ∀ j, ((Finset.univ : Finset (Fin m)).filter (fun i => H i j = 1)).card = d)
    (hpos : 0 < H.permanent) :
    H.permanent ^ d ≤ (d.factorial : ℝ) ^ m := by
  let P : Finset (Equiv.Perm (Fin m)) := Finset.univ.filter (fun π => ∀ i : Fin m, H (π i) i = 1)
  have hperm_eq : H.permanent = (P.card : ℝ) := by
    rw [Matrix.permanent]
    have hterm : ∀ π : Equiv.Perm (Fin m), (∏ i : Fin m, H (π i) i) = if π ∈ P then 1 else 0 := by
      intro π
      by_cases hπ : π ∈ P
      · simp only [hπ, ↓reduceIte]
        exact Finset.prod_eq_one (fun i _ => (Finset.mem_filter.mp hπ).2 i)
      · simp only [hπ, ↓reduceIte]
        have hex : ∃ i : Fin m, H (π i) i ≠ 1 := by
          by_contra hall
          push Not at hall
          exact hπ (Finset.mem_filter.mpr ⟨Finset.mem_univ π, hall⟩)
        rcases hex with ⟨i, hi⟩
        have h0 : H (π i) i = 0 := (h01 (π i) i).resolve_right hi
        exact Finset.prod_eq_zero (Finset.mem_univ i) h0
    simp [hterm]
  have hP_pos : 0 < P.card := by
    rw [hperm_eq] at hpos
    exact_mod_cast hpos
  have hP_valid : ∀ π ∈ P, ∀ i : Fin m, H (π i) i = 1 := fun π hπ => (Finset.mem_filter.mp hπ).2
  have htele : ∀ σ : Equiv.Perm (Fin m),
      (P.card : ℝ) ^ P.card ≤ ∏ π ∈ P, ∏ t : Fin m, (avail H σ π t : ℝ) := by
    intro σ
    have h0 := prefix_telescope H P hP_valid σ m le_rfl (fun t => Fin.elim0 (by simpa using t))
    have hsub : m - m = 0 := Nat.sub_self m
    have hQ : P.filter (fun π => ∀ t : Fin (m - m), π (σ ⟨t.val, by omega⟩) =
        (fun t : Fin (m - m) => Fin.elim0 (by simpa using t)) t) = P := by
      ext π
      simp only [Finset.mem_filter, and_iff_left_iff_imp]
      intro _ t
      exact absurd t.isLt (by omega)
    have hfilt : (Finset.univ : Finset (Fin m)).filter (fun t : Fin m => m - m ≤ t.val) =
        Finset.univ := by
      ext t
      simp
    simpa [hQ, hfilt] using h0
  have hprod_σ : ((P.card : ℝ) ^ P.card) ^ Fintype.card (Equiv.Perm (Fin m)) ≤
      ∏ π ∈ P, ∏ i : Fin m, ∏ σ : Equiv.Perm (Fin m), (avail H σ π (σ.symm i) : ℝ) := by
    have h1 : ((P.card : ℝ) ^ P.card) ^ Fintype.card (Equiv.Perm (Fin m)) ≤
        ∏ σ : Equiv.Perm (Fin m), ∏ π ∈ P, ∏ t : Fin m, (avail H σ π t : ℝ) := by
      rw [← Finset.card_univ, ← Finset.prod_const]
      apply prod_le_prod_nonneg
      · intro _ _; exact pow_nonneg (Nat.cast_nonneg _) _
      · intro σ _; exact htele σ
    have h2 : ∀ σ : Equiv.Perm (Fin m), ∀ π ∈ P,
        (∏ t : Fin m, (avail H σ π t : ℝ)) = ∏ i : Fin m, (avail H σ π (σ.symm i) : ℝ) := by
      intro σ π _
      exact (Equiv.prod_comp σ.symm (fun t => (avail H σ π t : ℝ))).symm
    have h3 : (∏ σ : Equiv.Perm (Fin m), ∏ π ∈ P, ∏ t : Fin m, (avail H σ π t : ℝ)) =
        ∏ π ∈ P, ∏ i : Fin m, ∏ σ : Equiv.Perm (Fin m), (avail H σ π (σ.symm i) : ℝ) := by
      calc ∏ σ : Equiv.Perm (Fin m), ∏ π ∈ P, ∏ t : Fin m, (avail H σ π t : ℝ)
          = ∏ σ : Equiv.Perm (Fin m), ∏ π ∈ P, ∏ i : Fin m, (avail H σ π (σ.symm i) : ℝ) := by
            apply Finset.prod_congr rfl
            intro σ _
            apply Finset.prod_congr rfl
            exact h2 σ
        _ = ∏ π ∈ P, ∏ σ : Equiv.Perm (Fin m), ∏ i : Fin m, (avail H σ π (σ.symm i) : ℝ) :=
            Finset.prod_comm
        _ = ∏ π ∈ P, ∏ i : Fin m, ∏ σ : Equiv.Perm (Fin m), (avail H σ π (σ.symm i) : ℝ) := by
            apply Finset.prod_congr rfl
            intro π _
            exact Finset.prod_comm
    linarith
  have hinner_eval : ∀ π ∈ P, ∀ i : Fin m,
      (∏ σ : Equiv.Perm (Fin m), (avail H σ π (σ.symm i) : ℝ)) ^ d =
        (d.factorial : ℝ) ^ Fintype.card (Equiv.Perm (Fin m)) := by
    intro π hπ i
    let S : Finset (Fin m) := Finset.univ.filter (fun j => H (π j) i = 1)
    have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hP_valid π hπ i⟩
    have hScard : S.card = d := by
      rw [← hcol i]
      refine Finset.card_bij (fun j _ => π j) ?_ ?_ ?_
      · intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
      · intro j₁ _ j₂ _ h; exact π.injective h
      · intro r hr
        refine ⟨π.symm r, ?_, π.apply_symm_apply r⟩
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp hr).2⟩
    have havail_eq : ∀ σ : Equiv.Perm (Fin m),
        avail H σ π (σ.symm i) = (S.filter (fun j => σ.symm i ≤ σ.symm j)).card := by
      intro σ
      unfold avail
      refine Finset.card_bij (fun r _ => π.symm r) ?_ ?_ ?_
      · intro r hr
        rcases Finset.mem_filter.mp hr with ⟨_, hH, hall⟩
        simp only [Equiv.apply_symm_apply] at hH
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hH⟩, ?_⟩
        by_contra hlt
        push Not at hlt
        have := hall (σ.symm (π.symm r)) hlt
        simp at this
      · intro r₁ _ r₂ _ h; exact π.symm.injective h
      · intro j hj
        rcases Finset.mem_filter.mp hj with ⟨hjS, hle⟩
        refine ⟨π j, ?_, π.symm_apply_apply j⟩
        simp only [Finset.mem_filter, Finset.mem_univ, Equiv.apply_symm_apply, true_and]
        refine ⟨(Finset.mem_filter.mp hjS).2, ?_⟩
        intro t ht heq
        have hj' : σ t = j := π.injective heq
        rw [← hj', Equiv.symm_apply_apply] at hle
        exact not_lt.mpr hle ht
    have hrew : (∏ σ : Equiv.Perm (Fin m), (avail H σ π (σ.symm i) : ℝ)) =
        ∏ τ : Equiv.Perm (Fin m), ((S.filter (fun j => τ i ≤ τ j)).card : ℝ) := by
      simp only [havail_eq]
      exact Equiv.prod_comp (Equiv.inv (Equiv.Perm (Fin m)))
        (fun τ => ((S.filter (fun j => τ i ≤ τ j)).card : ℝ))
    rw [hrew]
    exact prod_rank_pow_eq S i hiS hScard
  have hpow_d : (((P.card : ℝ) ^ d) ^ (P.card * Fintype.card (Equiv.Perm (Fin m)))) ≤
      (((d.factorial : ℝ) ^ m) ^ (P.card * Fintype.card (Equiv.Perm (Fin m)))) := by
    have h1 := pow_le_pow_left₀ (by positivity) hprod_σ d
    have hlhs : (((P.card : ℝ) ^ P.card) ^ Fintype.card (Equiv.Perm (Fin m))) ^ d =
        ((P.card : ℝ) ^ d) ^ (P.card * Fintype.card (Equiv.Perm (Fin m))) := by
      rw [← pow_mul, ← pow_mul, ← pow_mul]
      congr 1
      ring
    have hrhs : (∏ π ∈ P, ∏ i : Fin m, ∏ σ : Equiv.Perm (Fin m),
          (avail H σ π (σ.symm i) : ℝ)) ^ d =
        ((d.factorial : ℝ) ^ m) ^ (P.card * Fintype.card (Equiv.Perm (Fin m))) := by
      rw [← Finset.prod_pow]
      have hcongr : ∏ π ∈ P, (∏ i : Fin m, ∏ σ : Equiv.Perm (Fin m),
            (avail H σ π (σ.symm i) : ℝ)) ^ d =
          ∏ _π ∈ P, ((d.factorial : ℝ) ^ Fintype.card (Equiv.Perm (Fin m))) ^ m := by
        apply Finset.prod_congr rfl
        intro π hπ
        rw [← Finset.prod_pow]
        have hcongr2 : ∏ i : Fin m, (∏ σ : Equiv.Perm (Fin m),
              (avail H σ π (σ.symm i) : ℝ)) ^ d =
            ∏ _i : Fin m, (d.factorial : ℝ) ^ Fintype.card (Equiv.Perm (Fin m)) := by
          apply Finset.prod_congr rfl
          intro i _
          exact hinner_eval π hπ i
        rw [hcongr2, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [hcongr, Finset.prod_const, ← pow_mul, ← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [hlhs, hrhs] at h1
    exact h1
  have hexp_ne : P.card * Fintype.card (Equiv.Perm (Fin m)) ≠ 0 :=
    mul_ne_zero hP_pos.ne' (Fintype.card_pos.ne')
  rw [hperm_eq]
  exact le_of_pow_le_pow_left₀ hexp_ne (by positivity) hpow_d

end PEqualNP.Outside.L_lib_982_aux

theorem PEqualNP.Outside.L_lib_982 :
  ∀ q : ℕ, Nat.Prime q →
  let m : ℕ := q^2+q+1
  let d : ℕ := q+1
  let I := Fin m
  ∃ H : Matrix I I ℝ, (∀ i j, H i j = 0 ∨ H i j = 1) ∧
    (∀ i, ((Finset.univ : Finset I).filter (fun j => H i j = 1)).card = d) ∧
    (∀ j, ((Finset.univ : Finset I).filter (fun i => H i j = 1)).card = d) ∧
    H.det^2 = (d : ℝ)^2*(q : ℝ)^(m-1) ∧
    0 < H.permanent ∧ H.permanent^d ≤ (d.factorial : ℝ)^m := by
  intro q hq
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  dsimp only
  let m : ℕ := q ^ 2 + q + 1
  let d : ℕ := q + 1
  let e : Fin m ≃ PEqualNP.Outside.L_lib_982_aux.PG q :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, PEqualNP.Outside.L_lib_982_aux.card_PG])
  let H : Matrix (Fin m) (Fin m) ℝ :=
    fun i j => if PEqualNP.Outside.L_lib_982_aux.inc (e i) (e j) then 1 else 0
  have h01 : ∀ i j, H i j = 0 ∨ H i j = 1 := by
    intro i j
    dsimp only [H]
    split_ifs <;> simp
  have hrow : ∀ i : Fin m, ((Finset.univ : Finset (Fin m)).filter (fun j => H i j = 1)).card = d := by
    intro i
    have hcard := PEqualNP.Outside.L_lib_982_aux.card_inc (e i)
    dsimp only [d]
    rw [← hcard]
    refine Finset.card_bij (fun j _ => e j) ?_ ?_ ?_
    · intro j hj
      have h1 : H i j = 1 := (Finset.mem_filter.mp hj).2
      have hinc : PEqualNP.Outside.L_lib_982_aux.inc (e i) (e j) := by
        by_contra hn
        simp [H, hn] at h1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinc⟩
    · intro j₁ _ j₂ _ h; exact e.injective h
    · intro l hl
      refine ⟨e.symm l, ?_, e.apply_symm_apply l⟩
      have hinc : PEqualNP.Outside.L_lib_982_aux.inc (e i) l := (Finset.mem_filter.mp hl).2
      simp [H, hinc]
  have hcol : ∀ j : Fin m, ((Finset.univ : Finset (Fin m)).filter (fun i => H i j = 1)).card = d := by
    intro j
    have hsymm : ∀ i : Fin m, H i j = H j i := by
      intro i
      simp only [H, PEqualNP.Outside.L_lib_982_aux.inc_symm (e i) (e j)]
    simp only [hsymm]
    exact hrow j
  have hGram : H * H.transpose = fun i j : Fin m => (if i = j then (q : ℝ) else 0) + 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have hterm : ∀ k : Fin m, H i k * H.transpose k j =
        if PEqualNP.Outside.L_lib_982_aux.inc (e i) (e k) ∧
           PEqualNP.Outside.L_lib_982_aux.inc (e j) (e k) then 1 else 0 := by
      intro k
      rw [Matrix.transpose_apply]
      dsimp only [H]
      split_ifs <;> simp_all
    simp only [hterm, Finset.sum_boole]
    by_cases hij : i = j
    · subst hij
      have hfilt : ((Finset.univ : Finset (Fin m)).filter
          (fun k => PEqualNP.Outside.L_lib_982_aux.inc (e i) (e k) ∧
                    PEqualNP.Outside.L_lib_982_aux.inc (e i) (e k))).card = d := by
        have h1 : ((Finset.univ : Finset (Fin m)).filter
            (fun k => PEqualNP.Outside.L_lib_982_aux.inc (e i) (e k) ∧
                      PEqualNP.Outside.L_lib_982_aux.inc (e i) (e k))) =
            (Finset.univ : Finset (Fin m)).filter (fun k => H i k = 1) := by
          ext k
          simp [H]
        rw [h1, hrow i]
      rw [hfilt]
      simp [d]
    · have hne : e i ≠ e j := fun h => hij (e.injective h)
      have hcard := PEqualNP.Outside.L_lib_982_aux.card_common_inc hne
      have hfilt : ((Finset.univ : Finset (Fin m)).filter
          (fun k => PEqualNP.Outside.L_lib_982_aux.inc (e i) (e k) ∧
                    PEqualNP.Outside.L_lib_982_aux.inc (e j) (e k))).card = 1 := by
        rw [← hcard]
        refine Finset.card_bij (fun k _ => e k) ?_ ?_ ?_
        · intro k hk
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hk).2⟩
        · intro k₁ _ k₂ _ h; exact e.injective h
        · intro l hl
          refine ⟨e.symm l, ?_, e.apply_symm_apply l⟩
          simpa using (Finset.mem_filter.mp hl).2
      rw [hfilt]
      simp [hij]
  have hdet_sq : H.det ^ 2 = (d : ℝ) ^ 2 * (q : ℝ) ^ (m - 1) := by
    have h1 : H.det ^ 2 = (H * H.transpose).det := by
      rw [Matrix.det_mul, Matrix.det_transpose, sq]
    rw [h1, hGram, PEqualNP.Outside.L_lib_982_aux.det_qI_add_J m (by omega) (q : ℝ)]
    have hqm : (q : ℝ) + (m : ℝ) = (d : ℝ) ^ 2 := by
      dsimp only [m, d]
      push_cast
      ring
    rw [hqm]
  have hperm_pos : 0 < H.permanent := by
    have hdet_ne : H.det ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by norm_num : 2 ≠ 0)] at hdet_sq
      have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq.pos
      have hd_pos : (0 : ℝ) < (d : ℝ) := by dsimp only [d]; positivity
      have hrhs_pos : (0 : ℝ) < (d : ℝ) ^ 2 * (q : ℝ) ^ (m - 1) := by positivity
      linarith
    have hex : ∃ π : Equiv.Perm (Fin m), ∏ i : Fin m, H (π i) i ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hdet_ne
      rw [Matrix.det_apply']
      apply Finset.sum_eq_zero
      intro π _
      rw [hall π, mul_zero]
    rcases hex with ⟨π, hπ⟩
    have hterm_nn : ∀ σ : Equiv.Perm (Fin m), 0 ≤ ∏ i : Fin m, H (σ i) i := by
      intro σ
      apply Finset.prod_nonneg
      intro i _
      rcases h01 (σ i) i with h0 | h1 <;> linarith
    have hπ_pos : 0 < ∏ i : Fin m, H (π i) i :=
      lt_of_le_of_ne (hterm_nn π) (Ne.symm hπ)
    have hle : (∏ i : Fin m, H (π i) i) ≤ H.permanent := by
      rw [Matrix.permanent]
      exact Finset.single_le_sum (fun σ _ => hterm_nn σ) (Finset.mem_univ π)
    linarith
  have hbreg : H.permanent ^ d ≤ (d.factorial : ℝ) ^ m :=
    PEqualNP.Outside.L_lib_982_aux.bregman_regular H h01 hcol hperm_pos
  exact ⟨H, h01, hrow, hcol, hdet_sq, hperm_pos, hbreg⟩
