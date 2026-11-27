import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_801_aux

open scoped BigOperators

abbrev Vec (r : ℕ) := Fin r → ZMod 2

def fVal {r : ℕ} (z : ℚ) (a : Vec r) : ℚ :=
  if a = 0 then z - 1 else -1

def TMat {r : ℕ} (z : ℚ) (h : Vec r) : Matrix (Option (Vec r)) (Option (Vec r)) ℚ :=
  fun before after =>
    before.elim (after.elim 1 (fun b => if b = h then 1 else 0))
      (fun a => after.elim (fVal z a) (fun b => if b = a + h then 1 else 0))

def cycleVal {r : ℕ} (z : ℚ) (w : List (Vec r)) : ℚ :=
  Matrix.trace (w.map (TMat z)).prod + fVal z w.sum - (if w.sum = 0 then ((2 ^ r : ℕ) : ℚ) else 0)

def Realizes {r : ℕ} (g : List (Vec r) → ℚ) (k : ℕ) (test : List (Vec r) → Prop) : Prop :=
  ∃ (u v : Fin k → ℚ) (M : Vec r → Matrix (Fin k) (Fin k) ℚ),
    ∀ w : List (Vec r), test w →
      (∑ i : Fin k, ∑ j : Fin k, u i * (w.map M).prod i j * v j) = g w

def Fits (r : ℕ) (z : ℚ) (k : ℕ) (test : List (Vec r) → Prop) : Prop :=
  Realizes (cycleVal z) k test

lemma zmod2_add_eq_zero_iff (x y : ZMod 2) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_add, ZMod.val_zero] at hv
    have hx := ZMod.val_lt x
    have hy := ZMod.val_lt y
    exact ZMod.val_injective 2 (by omega)
  · rintro rfl
    apply ZMod.val_injective 2
    rw [ZMod.val_add, ZMod.val_zero]
    omega

lemma vec_add_eq_zero_iff {r : ℕ} (a b : Vec r) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    funext i
    exact (zmod2_add_eq_zero_iff (a i) (b i)).mp (congrFun h i)
  · rintro rfl
    funext i
    exact (zmod2_add_eq_zero_iff (a i) (a i)).mpr rfl

lemma vec_add_self {r : ℕ} (a : Vec r) : a + a = 0 :=
  (vec_add_eq_zero_iff a a).mpr rfl

lemma card_vec (r : ℕ) : Fintype.card (Vec r) = 2 ^ r := by
  simp [Vec]

lemma sum_fVal {r : ℕ} (z : ℚ) : ∑ a : Vec r, fVal z a = z - (2 ^ r : ℚ) := by
  have h0 : (0 : Vec r) ∈ (Finset.univ : Finset (Vec r)) := Finset.mem_univ 0
  rw [← Finset.add_sum_erase _ _ h0]
  have h1 : fVal z (0 : Vec r) = z - 1 := by simp [fVal]
  have h2 : ∑ a ∈ Finset.univ.erase (0 : Vec r), fVal z a = ((2 ^ r : ℕ) - 1 : ℕ) * (-1 : ℚ) := by
    have heq : ∀ a ∈ Finset.univ.erase (0 : Vec r), fVal z a = (-1 : ℚ) := by
      intro a ha
      have hne : a ≠ 0 := (Finset.mem_erase.mp ha).1
      simp [fVal, hne]
    rw [Finset.sum_congr rfl heq, Finset.sum_const, Finset.card_erase_of_mem h0,
      Finset.card_univ, card_vec, nsmul_eq_mul]
  rw [h1, h2]
  have hpos : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  rw [Nat.cast_sub hpos]
  push_cast
  ring

lemma cycleVal_nil {r : ℕ} (z : ℚ) : cycleVal (r := r) z [] = z := by
  unfold cycleVal fVal
  simp [Matrix.trace_one, card_vec]

lemma realizes_mono {r k1 k2 : ℕ} {g : List (Vec r) → ℚ} {test : List (Vec r) → Prop}
    (hk : k1 ≤ k2) (h : Realizes g k1 test) : Realizes g k2 test := by
  rcases h with ⟨u, v, M, hM⟩
  let u' : Fin k2 → ℚ := fun i => if hi : i.val < k1 then u ⟨i.val, hi⟩ else 0
  let v' : Fin k2 → ℚ := fun j => if hj : j.val < k1 then v ⟨j.val, hj⟩ else 0
  let M' : Vec r → Matrix (Fin k2) (Fin k2) ℚ := fun a i j =>
    if hi : i.val < k1 then if hj : j.val < k1 then M a ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0 else 0
  let emb : Fin k1 ↪ Fin k2 := ⟨Fin.castLE hk, Fin.castLE_injective hk⟩
  have hprod : ∀ (w : List (Vec r)) (i j : Fin k1),
      (w.map M').prod (emb i) (emb j) = (w.map M).prod i j := by
    intro w
    induction w with
    | nil =>
      intro i j
      simp [emb, Matrix.one_apply, Fin.ext_iff]
    | cons a ws ih =>
      intro i j
      simp only [List.map_cons, List.prod_cons]
      rw [Matrix.mul_apply, Matrix.mul_apply]
      calc ∑ x : Fin k2, M' a (emb i) x * (ws.map M').prod x (emb j)
          = ∑ x ∈ Finset.univ.map emb, M' a (emb i) x * (ws.map M').prod x (emb j) := by
            symm
            apply Finset.sum_subset (Finset.subset_univ _)
            intro x _ hx
            have hxge : ¬ x.val < k1 := fun hlt =>
              hx (Finset.mem_map.mpr ⟨⟨x.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
            simp [M', emb, i.isLt, hxge]
        _ = ∑ x : Fin k1, M a i x * (ws.map M).prod x j := by
            rw [Finset.sum_map]
            apply Finset.sum_congr rfl
            intro x _
            have hMe : M' a (emb i) (emb x) = M a i x := by simp [M', emb, i.isLt, x.isLt]
            rw [hMe, ih x j]
  refine ⟨u', v', M', ?_⟩
  intro w hw
  have hsum :
      ∑ i : Fin k2, ∑ j : Fin k2, u' i * (w.map M').prod i j * v' j =
      ∑ i : Fin k1, ∑ j : Fin k1, u i * (w.map M).prod i j * v j := by
    calc ∑ i : Fin k2, ∑ j : Fin k2, u' i * (w.map M').prod i j * v' j
        = ∑ i ∈ Finset.univ.map emb, ∑ j : Fin k2, u' i * (w.map M').prod i j * v' j := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro i _ hi
          have hige : ¬ i.val < k1 := fun hlt =>
            hi (Finset.mem_map.mpr ⟨⟨i.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
          simp [u', hige]
      _ = ∑ i : Fin k1, ∑ j : Fin k2, u' (emb i) * (w.map M').prod (emb i) j * v' j := by
          rw [Finset.sum_map]
      _ = ∑ i : Fin k1, ∑ j ∈ Finset.univ.map emb, u' (emb i) * (w.map M').prod (emb i) j * v' j := by
          apply Finset.sum_congr rfl
          intro i _
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro j _ hj
          have hjge : ¬ j.val < k1 := fun hlt =>
            hj (Finset.mem_map.mpr ⟨⟨j.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
          simp [v', hjge]
      _ = ∑ i : Fin k1, ∑ j : Fin k1, u i * (w.map M).prod i j * v j := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_map]
          apply Finset.sum_congr rfl
          intro j _
          have hu' : u' (emb i) = u i := by simp [u', emb, i.isLt]
          have hv' : v' (emb j) = v j := by simp [v', emb, j.isLt]
          rw [hu', hv', hprod w i j]
  rw [hsum]
  exact hM w hw

lemma realizes_of_equiv {r k : ℕ} {g : List (Vec r) → ℚ} {test : List (Vec r) → Prop}
    {γ : Type*} [Fintype γ] [DecidableEq γ] (e : Fin k ≃ γ)
    (u v : γ → ℚ) (M : Vec r → Matrix γ γ ℚ)
    (hM : ∀ w : List (Vec r), test w → (∑ i : γ, ∑ j : γ, u i * (w.map M).prod i j * v j) = g w) :
    Realizes g k test := by
  let M' : Vec r → Matrix (Fin k) (Fin k) ℚ := fun a => (M a).submatrix e e
  have hprod : ∀ w : List (Vec r), (w.map M').prod = ((w.map M).prod).submatrix e e := by
    intro w
    induction w with
    | nil =>
      ext i j
      simp [Matrix.submatrix_apply, Matrix.one_apply, e.injective.eq_iff]
    | cons a ws ih =>
      simp only [List.map_cons, List.prod_cons, ih, M']
      ext i j
      rw [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.mul_apply]
      simp only [Matrix.submatrix_apply]
      exact e.sum_comp (fun x => M a (e i) x * (ws.map M).prod x (e j))
  refine ⟨fun i => u (e i), fun j => v (e j), M', ?_⟩
  intro w hw
  rw [hprod w]
  have h1 :
      ∑ i : Fin k, ∑ j : Fin k, u (e i) * (w.map M).prod (e i) (e j) * v (e j) =
      ∑ i : γ, ∑ j : γ, u i * (w.map M).prod i j * v j := by
    rw [e.sum_comp (fun i => ∑ j : Fin k, u i * (w.map M).prod i (e j) * v (e j))]
    apply Finset.sum_congr rfl
    intro i _
    exact e.sum_comp (fun j => u i * (w.map M).prod i j * v j)
  simpa [Matrix.submatrix_apply] using h1.trans (hM w hw)

lemma realizes_of_sum {r k1 k2 : ℕ} {g1 g2 : List (Vec r) → ℚ} {test : List (Vec r) → Prop}
    (h1 : Realizes g1 k1 test) (h2 : Realizes g2 k2 test) :
    Realizes (fun w => g1 w + g2 w) (k1 + k2) test := by
  rcases h1 with ⟨u1, v1, M1, hM1⟩
  rcases h2 with ⟨u2, v2, M2, hM2⟩
  let e : Fin (k1 + k2) ≃ Fin k1 ⊕ Fin k2 := finSumFinEquiv.symm
  let u : Fin k1 ⊕ Fin k2 → ℚ := Sum.elim u1 u2
  let v : Fin k1 ⊕ Fin k2 → ℚ := Sum.elim v1 v2
  let M : Vec r → Matrix (Fin k1 ⊕ Fin k2) (Fin k1 ⊕ Fin k2) ℚ := fun a =>
    Matrix.fromBlocks (M1 a) 0 0 (M2 a)
  have hprod : ∀ w : List (Vec r),
      (w.map M).prod = Matrix.fromBlocks ((w.map M1).prod) 0 0 ((w.map M2).prod) := by
    intro w
    induction w with
    | nil =>
      simp [Matrix.fromBlocks_one]
    | cons a ws ih =>
      simp only [List.map_cons, List.prod_cons, ih, M, Matrix.fromBlocks_multiply,
        Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  apply realizes_of_equiv e u v M
  intro w hw
  rw [hprod w, Fintype.sum_sum_type]
  simp only [u, v, Sum.elim_inl, Sum.elim_inr, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  rw [hM1 w hw, hM2 w hw]

lemma realizes_of_trace {r d : ℕ} {γ : Type*} [Fintype γ] [DecidableEq γ]
    (hcard : Fintype.card γ = d) (M : Vec r → Matrix γ γ ℚ) :
    Realizes (fun w => Matrix.trace (w.map M).prod) (d ^ 2) (fun _ => True) := by
  have hcard2 : Fintype.card (γ × γ) = d ^ 2 := by
    simp [hcard, sq]
  let e : Fin (d ^ 2) ≃ γ × γ := (Fintype.equivFinOfCardEq hcard2).symm
  let u : γ × γ → ℚ := fun p => if p.1 = p.2 then 1 else 0
  let v : γ × γ → ℚ := fun p => if p.1 = p.2 then 1 else 0
  let M2 : Vec r → Matrix (γ × γ) (γ × γ) ℚ := fun a p q =>
    if p.1 = q.1 then M a p.2 q.2 else 0
  have hM2_apply : ∀ a p q, M2 a p q = if p.1 = q.1 then M a p.2 q.2 else 0 := fun _ _ _ => rfl
  have hprod : ∀ (w : List (Vec r)) (p q : γ × γ),
      (w.map M2).prod p q = if p.1 = q.1 then (w.map M).prod p.2 q.2 else 0 := by
    intro w
    induction w with
    | nil =>
      intro p q
      simp only [List.map_nil, List.prod_nil, Matrix.one_apply, Prod.ext_iff]
      by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [h1, h2]
    | cons a ws ih =>
      intro p q
      simp only [List.map_cons, List.prod_cons]
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      simp_rw [hM2_apply, ih]
      rw [Finset.sum_eq_single p.1]
      · by_cases h1 : p.1 = q.1
        · simp only [h1, ↓reduceIte, Matrix.mul_apply]
        · simp [h1]
      · intro x _ hx
        simp [Ne.symm hx]
      · intro h; exact False.elim (h (Finset.mem_univ _))
  apply realizes_of_equiv e u v M2
  intro w _
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, hprod w]
  have hsum : ∑ i : γ, ∑ j : γ, ∑ i' : γ, ∑ j' : γ,
      u (i, j) * (if i = i' then (w.map M).prod j j' else 0) * v (i', j') =
      ∑ i : γ, (w.map M).prod i i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single i]
        · simp [u, v]
        · intro j' _ hj'; simp [v, Ne.symm hj']
        · intro h; exact False.elim (h (Finset.mem_univ _))
      · intro i' _ hi'; simp [Ne.symm hi']
      · intro h; exact False.elim (h (Finset.mem_univ _))
    · intro j _ hj; simp [u, Ne.symm hj]
    · intro h; exact False.elim (h (Finset.mem_univ _))
  rw [hsum]
  rfl

lemma fits_all_of_fits_pos {r k : ℕ} (z : ℚ) (hpos : Fits r z k (fun w => 0 < w.length)) :
    Fits r z (k + 1) (fun _ => True) := by
  rcases hpos with ⟨u, v, M, hM⟩
  let d : ℚ := cycleVal (r := r) z [] - ∑ i : Fin k, u i * v i
  have hdead : Realizes (r := r) (fun w : List (Vec r) => if w = [] then d else 0) 1 (fun _ => True) := by
    refine ⟨fun _ => d, fun _ => 1, fun _ => 0, ?_⟩
    intro w _
    cases w with
    | nil => simp
    | cons a ws => simp
  have hmain : Realizes (r := r) (fun w : List (Vec r) => if w = [] then ∑ i : Fin k, u i * v i else cycleVal z w) k (fun _ => True) := by
    refine ⟨u, v, M, ?_⟩
    intro w _
    cases w with
    | nil =>
      simp only [List.map_nil, List.prod_nil, ↓reduceIte]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Matrix.one_apply, Ne.symm hj]
      · intro h; exact False.elim (h (Finset.mem_univ _))
    | cons a ws =>
      simp only [reduceCtorEq, ↓reduceIte]
      exact hM (a :: ws) (by simp)
  rcases realizes_of_sum hmain hdead with ⟨u', v', M', hM'⟩
  refine ⟨u', v', M', ?_⟩
  intro w _
  rw [hM' w trivial]
  cases w with
  | nil => simp [d]
  | cons a ws => simp

lemma hankel_rank_le_of_fits {r k : ℕ} {z : ℚ} {test : List (Vec r) → Prop}
    {I J : Type*} [Fintype I] [Fintype J]
    (pref : I → List (Vec r)) (suff : J → List (Vec r))
    (htest : ∀ i j, test (pref i ++ suff j))
    (hfit : Fits r z k test) :
    (Matrix.of (fun i j => cycleVal z (pref i ++ suff j))).rank ≤ k := by
  rcases hfit with ⟨left, right, M, hM⟩
  let U : Matrix I (Fin k) ℚ := fun i a => ∑ b : Fin k, left b * ((pref i).map M).prod b a
  let V : Matrix (Fin k) J ℚ := fun a j => ∑ c : Fin k, ((suff j).map M).prod a c * right c
  have hfac : Matrix.of (fun i j => cycleVal z (pref i ++ suff j)) = U * V := by
    ext i j
    rw [Matrix.of_apply, Matrix.mul_apply]
    dsimp only [U, V]
    rw [← hM (pref i ++ suff j) (htest i j)]
    simp only [List.map_append, List.prod_append]
    calc ∑ b : Fin k, ∑ c : Fin k,
            left b * (((pref i).map M).prod * ((suff j).map M).prod) b c * right c
        = ∑ b : Fin k, ∑ c : Fin k, ∑ a : Fin k,
            (left b * ((pref i).map M).prod b a) * (((suff j).map M).prod a c * right c) := by
          apply Finset.sum_congr rfl; intro b _
          apply Finset.sum_congr rfl; intro c _
          rw [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl; intro a _; ring
      _ = ∑ b : Fin k, ∑ a : Fin k, ∑ c : Fin k,
            (left b * ((pref i).map M).prod b a) * (((suff j).map M).prod a c * right c) := by
          apply Finset.sum_congr rfl; intro b _; exact Finset.sum_comm
      _ = ∑ a : Fin k, ∑ b : Fin k, ∑ c : Fin k,
            (left b * ((pref i).map M).prod b a) * (((suff j).map M).prod a c * right c) :=
          Finset.sum_comm
      _ = ∑ a : Fin k,
            (∑ b : Fin k, left b * ((pref i).map M).prod b a) *
            (∑ c : Fin k, ((suff j).map M).prod a c * right c) := by
          apply Finset.sum_congr rfl; intro a _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl; intro b _
          rw [Finset.mul_sum]
  rw [hfac]
  exact (Matrix.rank_mul_le_left U V).trans ((Matrix.rank_le_card_width U).trans (Fintype.card_fin k).le)

lemma exists_finset_span_eq_top {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    {α : Type*} (φ : α → V) (P : α → Prop)
    (hspan : Submodule.span ℚ {v : V | ∃ a : α, P a ∧ φ a = v} = ⊤) :
    ∃ W : Finset α, (∀ a ∈ W, P a) ∧
      Submodule.span ℚ (Set.range (fun a : W => φ a.1)) = ⊤ := by
  classical
  let b := Module.finBasis ℚ V
  have hmem : ∀ i : Fin (Module.finrank ℚ V),
      ∃ F : Finset α, (∀ a ∈ F, P a) ∧ b i ∈ Submodule.span ℚ (Set.range (fun a : F => φ a.1)) := by
    intro i
    have hi : b i ∈ Submodule.span ℚ {v : V | ∃ a : α, P a ∧ φ a = v} := by
      rw [hspan]; exact Submodule.mem_top
    rw [Finsupp.mem_span_iff_linearCombination] at hi
    rcases hi with ⟨l, hl⟩
    let S := l.support
    let chooseA : {v : V // ∃ a : α, P a ∧ φ a = v} → α := fun v => Classical.choose v.2
    let F : Finset α := S.image chooseA
    refine ⟨F, ?_, ?_⟩
    · intro a ha
      rcases Finset.mem_image.mp ha with ⟨v, _, rfl⟩
      exact (Classical.choose_spec v.2).1
    · rw [← hl, Finsupp.linearCombination_apply, Finsupp.sum]
      apply Submodule.sum_mem
      intro v hv
      apply Submodule.smul_mem
      apply Submodule.subset_span
      have hmemF : chooseA v ∈ F := Finset.mem_image.mpr ⟨v, hv, rfl⟩
      exact ⟨⟨chooseA v, hmemF⟩, (Classical.choose_spec v.2).2⟩
  let Fset : Fin (Module.finrank ℚ V) → Finset α := fun i => Classical.choose (hmem i)
  let W : Finset α := Finset.univ.biUnion Fset
  refine ⟨W, ?_, ?_⟩
  · intro a ha
    rcases Finset.mem_biUnion.mp ha with ⟨i, _, hi⟩
    exact (Classical.choose_spec (hmem i)).1 a hi
  · rw [eq_top_iff]
    intro v _
    have hv : v ∈ Submodule.span ℚ (Set.range b) := by
      rw [b.span_eq]; exact Submodule.mem_top
    refine Submodule.span_le.mpr ?_ hv
    rintro _ ⟨i, rfl⟩
    have hbi := (Classical.choose_spec (hmem i)).2
    have hsub : Set.range (fun a : Fset i => φ a.1) ⊆ Set.range (fun a : W => φ a.1) := by
      rintro _ ⟨a, rfl⟩
      exact ⟨⟨a.1, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, a.2⟩⟩, rfl⟩
    exact Submodule.span_mono hsub hbi

lemma lower_bound_of_nondeg_pairing {r k : ℕ} {z : ℚ}
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (φ : List (Vec r) → V)
    (B : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hnondeg : ∀ y : V, (∀ x : V, B x y = 0) → y = 0)
    (hmatch : ∀ w1 w2 : List (Vec r), 0 < w1.length → 0 < w2.length →
      cycleVal z (w1 ++ w2) = B (φ w1) (φ w2))
    (hspan : Submodule.span ℚ {v : V | ∃ w : List (Vec r), 0 < w.length ∧ φ w = v} = ⊤)
    (hfit : Fits r z k (fun w => 0 < w.length)) :
    Module.finrank ℚ V ≤ k := by
  classical
  obtain ⟨W, hWpos, hWspan⟩ := exists_finset_span_eq_top φ (fun w => 0 < w.length) hspan
  let pref : W → List (Vec r) := fun w => w.1
  have htest : ∀ w1 w2 : W, 0 < (pref w1 ++ pref w2).length := by
    intro w1 w2
    have h1 := hWpos w1.1 w1.2
    simp only [pref, List.length_append]
    omega
  let H : Matrix W W ℚ := Matrix.of (fun w1 w2 => cycleVal z (pref w1 ++ pref w2))
  have hHle : H.rank ≤ k := hankel_rank_le_of_fits pref pref htest hfit
  let Ψ : (W → ℚ) →ₗ[ℚ] V :=
    { toFun := fun c => ∑ w : W, c w • φ w.1
      map_add' := fun c1 c2 => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun s c => by simp [Finset.smul_sum, mul_smul] }
  have hΨ_surj : LinearMap.range Ψ = ⊤ := by
    rw [eq_top_iff, ← hWspan, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    refine ⟨fun x => if x = w then 1 else 0, ?_⟩
    change ∑ x : W, (if x = w then (1 : ℚ) else 0) • φ x.1 = φ w.1
    rw [Finset.sum_eq_single w]
    · simp
    · intro x _ hx; simp [hx]
    · intro h; exact False.elim (h (Finset.mem_univ w))
  have hker_le : LinearMap.ker H.mulVecLin ≤ LinearMap.ker Ψ := by
    intro c hc
    change Ψ c = 0
    apply hnondeg
    have hallW : ∀ w1 : W, B (φ w1.1) (Ψ c) = 0 := by
      intro w1
      have hr : (H.mulVec c) w1 = 0 := congrFun hc w1
      have h1 : B (φ w1.1) (Ψ c) = (H.mulVec c) w1 := by
        change B (φ w1.1) (∑ w : W, c w • φ w.1) = (H.mulVec c) w1
        rw [map_sum, Matrix.mulVec, dotProduct]
        apply Finset.sum_congr rfl
        intro w2 _
        rw [map_smul, smul_eq_mul]
        change c w2 * B (φ w1.1) (φ w2.1) = cycleVal z (w1.1 ++ w2.1) * c w2
        rw [hmatch w1.1 w2.1 (hWpos w1.1 w1.2) (hWpos w2.1 w2.2), mul_comm]
      rw [h1, hr]
    intro x
    have hx : x ∈ Submodule.span ℚ (Set.range (fun a : W => φ a.1)) := by
      rw [hWspan]; exact Submodule.mem_top
    have hkerB : Submodule.span ℚ (Set.range (fun a : W => φ a.1)) ≤ LinearMap.ker (B.flip (Ψ c)) := by
      rw [Submodule.span_le]
      rintro _ ⟨w1, rfl⟩
      exact hallW w1
    exact hkerB hx
  have hrnH := H.mulVecLin.finrank_range_add_finrank_ker
  have hrnΨ := Ψ.finrank_range_add_finrank_ker
  rw [hΨ_surj, finrank_top] at hrnΨ
  have hker_fin : Module.finrank ℚ (LinearMap.ker H.mulVecLin) ≤ Module.finrank ℚ (LinearMap.ker Ψ) :=
    Submodule.finrank_mono hker_le
  change H.rank + Module.finrank ℚ (LinearMap.ker H.mulVecLin) = Module.finrank ℚ (W → ℚ) at hrnH
  omega

lemma lower_bound_all_of_nondeg_pairing {r k : ℕ} {z : ℚ}
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (φ : List (Vec r) → V) (v0 : V)
    (B : V →ₗ[ℚ] V →ₗ[ℚ] ℚ)
    (hnondeg : ∀ y : V, (∀ x : V, B x y = 0) → y = 0)
    (hmatch : ∀ w1 w2 : List (Vec r), 0 < w1.length → 0 < w2.length →
      cycleVal z (w1 ++ w2) = B (φ w1) (φ w2))
    (hleft0 : ∀ w2 : List (Vec r), 0 < w2.length → cycleVal z w2 = B v0 (φ w2))
    (hright0 : ∀ w1 : List (Vec r), 0 < w1.length → cycleVal z w1 = B (φ w1) v0)
    (hjump : cycleVal (r := r) z [] ≠ B v0 v0)
    (hspan : Submodule.span ℚ {v : V | ∃ w : List (Vec r), 0 < w.length ∧ φ w = v} = ⊤)
    (hfit : Fits r z k (fun _ => True)) :
    Module.finrank ℚ V + 1 ≤ k := by
  classical
  obtain ⟨W, hWpos, hWspan⟩ := exists_finset_span_eq_top φ (fun w => 0 < w.length) hspan
  let pref : Option W → List (Vec r) := fun o => o.elim [] (fun w => w.1)
  let H : Matrix (Option W) (Option W) ℚ := Matrix.of (fun o1 o2 => cycleVal z (pref o1 ++ pref o2))
  have hHle : H.rank ≤ k := hankel_rank_le_of_fits pref pref (fun _ _ => trivial) hfit
  let Ψ : (Option W → ℚ) →ₗ[ℚ] (V × ℚ) :=
    { toFun := fun c => (c none • v0 + ∑ w : W, c (some w) • φ w.1, c none)
      map_add' := fun c1 c2 => by
        ext
        · simp [add_smul, Finset.sum_add_distrib]; abel
        · rfl
      map_smul' := fun s c => by
        ext
        · simp [Finset.smul_sum, mul_smul, smul_add]
        · rfl }
  have hΨ_surj : LinearMap.range Ψ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, t⟩ _
    have hx' : x - t • v0 ∈ Submodule.span ℚ (Set.range (fun a : W => φ a.1)) := by
      rw [hWspan]; exact Submodule.mem_top
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hx'
    rcases hx' with ⟨cW, hcW⟩
    refine ⟨fun o => o.elim t (fun w => cW w), ?_⟩
    ext
    · change t • v0 + ∑ w : W, cW w • φ w.1 = x
      have hsum : ∑ w : W, cW w • φ w.1 = x - t • v0 := by
        rw [← hcW, Finsupp.sum_fintype]
        intro w; simp
      rw [hsum]; abel
    · rfl
  have hker_le : LinearMap.ker H.mulVecLin ≤ LinearMap.ker Ψ := by
    intro c hc
    have hV0 : (Ψ c).1 = 0 := by
      apply hnondeg
      have hallW : ∀ w1 : W, B (φ w1.1) (Ψ c).1 = 0 := by
        intro w1
        have hr : (H.mulVec c) (some w1) = 0 := congrFun hc (some w1)
        have h1 : B (φ w1.1) (Ψ c).1 = (H.mulVec c) (some w1) := by
          simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_sum, map_smul, smul_eq_mul,
            Matrix.mulVec, dotProduct, Fintype.sum_option, H, Matrix.of_apply, pref,
            Option.elim_some, Option.elim_none, List.append_nil]
          rw [hright0 w1.1 (hWpos w1.1 w1.2), mul_comm (c none)]
          congr 1
          apply Finset.sum_congr rfl
          intro w2 _
          rw [hmatch w1.1 w2.1 (hWpos w1.1 w1.2) (hWpos w2.1 w2.2), mul_comm]
        rw [h1, hr]
      intro x
      have hx : x ∈ Submodule.span ℚ (Set.range (fun a : W => φ a.1)) := by
        rw [hWspan]; exact Submodule.mem_top
      have hkerB : Submodule.span ℚ (Set.range (fun a : W => φ a.1)) ≤ LinearMap.ker (B.flip (Ψ c).1) := by
        rw [Submodule.span_le]
        rintro _ ⟨w1, rfl⟩
        exact hallW w1
      exact hkerB hx
    have hnone0 : c none = 0 := by
      have hr : (H.mulVec c) none = 0 := congrFun hc none
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, H, Matrix.of_apply, pref,
        Option.elim_none, Option.elim_some, List.nil_append] at hr
      have hBv : B v0 (Ψ c).1 = 0 := by rw [hV0, map_zero]
      simp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_sum, map_smul, smul_eq_mul] at hBv
      have hsum_eq : ∑ w : W, cycleVal z w.1 * c (some w) = ∑ w : W, c (some w) * B v0 (φ w.1) := by
        apply Finset.sum_congr rfl
        intro w _
        rw [hleft0 w.1 (hWpos w.1 w.2), mul_comm]
      rw [hsum_eq] at hr
      have hdiff : (cycleVal (r := r) z [] - B v0 v0) * c none = 0 := by linarith
      exact (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hjump)
    change Ψ c = 0
    ext
    · exact hV0
    · exact hnone0
  have hrnH := H.mulVecLin.finrank_range_add_finrank_ker
  have hrnΨ := Ψ.finrank_range_add_finrank_ker
  rw [hΨ_surj, finrank_top, Module.finrank_prod, Module.finrank_self] at hrnΨ
  have hker_fin : Module.finrank ℚ (LinearMap.ker H.mulVecLin) ≤ Module.finrank ℚ (LinearMap.ker Ψ) :=
    Submodule.finrank_mono hker_le
  change H.rank + Module.finrank ℚ (LinearMap.ker H.mulVecLin) = Module.finrank ℚ (Option W → ℚ) at hrnH
  omega

def seqRec (z : ℚ) : ℕ → ℚ
  | 0 => 2
  | 1 => 2
  | m + 2 => 2 * seqRec z (m + 1) + (z - 2) * seqRec z m

lemma r0_mat_pow_trace (z : ℚ) :
    ∀ w : List (Vec 0), Matrix.trace (w.map (TMat z)).prod = seqRec z w.length := by
  let e : Option (Vec 0) ≃ Fin 2 :=
    { toFun := fun s => s.elim 0 (fun _ => 1)
      invFun := fun i => if i = 0 then none else some 0
      left_inv := fun s => by
        cases s with
        | none => rfl
        | some a =>
          have ha : a = 0 := funext (fun i => Fin.elim0 i)
          simp [ha]
      right_inv := fun i => by fin_cases i <;> simp }
  let B : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; z - 1, 1]
  have hT_eq : ∀ h : Vec 0, (TMat z h).submatrix e.symm e.symm = B := by
    intro h
    have hh : h = 0 := funext (fun i => Fin.elim0 i)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e, TMat, B, fVal, hh]
  have hpow : ∀ w : List (Vec 0), ((w.map (TMat z)).prod).submatrix e.symm e.symm = B ^ w.length := by
    intro w
    induction w with
    | nil =>
      ext i j
      simp [Matrix.submatrix_apply, Matrix.one_apply, e.symm.injective.eq_iff]
    | cons a ws ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
      rw [← ih, ← hT_eq a]
      ext i j
      rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply]
      simp only [Matrix.submatrix_apply]
      exact (e.symm.sum_comp (fun x => TMat z a (e.symm i) x * (ws.map (TMat z)).prod x (e.symm j))).symm
  have htr_eq : ∀ w : List (Vec 0), Matrix.trace (w.map (TMat z)).prod = Matrix.trace (B ^ w.length) := by
    intro w
    rw [← hpow w]
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
    exact (e.symm.sum_comp (fun x => (w.map (TMat z)).prod x x)).symm
  have hB2 : B * B = (2 : ℚ) • B + (z - 2) • (1 : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [B, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have htr_rec : ∀ m : ℕ, Matrix.trace (B ^ m) = seqRec z m := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      match m with
      | 0 => simp [seqRec, Matrix.trace_one]
      | 1 => simp [seqRec, Matrix.trace, Matrix.diag, Fin.sum_univ_two, B]; ring
      | k + 2 =>
        have hpow2 : B ^ (k + 2) = (B * B) * B ^ k := by
          rw [Nat.add_comm k 2, pow_add, pow_two]
        rw [hpow2, hB2, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
          Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
        have h1 : B * B ^ k = B ^ (k + 1) := by rw [pow_succ']
        rw [h1, ih (k + 1) (by omega), ih k (by omega), seqRec]
  intro w
  rw [htr_eq w, htr_rec w.length]

lemma r0_cycleVal (z : ℚ) (w : List (Vec 0)) :
    cycleVal z w = seqRec z w.length + (z - 2) := by
  have hsum0 : w.sum = (0 : Vec 0) := funext (fun i => Fin.elim0 i)
  unfold cycleVal
  rw [r0_mat_pow_trace z w, hsum0]
  simp [fVal]
  ring

lemma seqRec_three_realizes (r : ℕ) (z : ℚ) :
    Realizes (fun w : List (Vec r) => seqRec z w.length + (z - 2)) 3 (fun _ => True) := by
  let M : Vec r → Matrix (Fin 3) (Fin 3) ℚ := fun _ =>
    !![0, 1, 0; z - 2, 2, 0; 0, 0, 1]
  let u : Fin 3 → ℚ := ![1, 0, 1]
  let v : Fin 3 → ℚ := ![2, 2, z - 2]
  have hmv : ∀ w : List (Vec r),
      ((w.map M).prod).mulVec v = ![seqRec z w.length, seqRec z (w.length + 1), z - 2] := by
    intro w
    induction w with
    | nil =>
      ext i
      fin_cases i <;> simp [v, seqRec]
    | cons a ws ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, ← Matrix.mulVec_mulVec, ih]
      ext i
      fin_cases i <;>
        simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three, seqRec] <;> ring
  refine ⟨u, v, M, ?_⟩
  intro w _
  have hsum : ∑ i : Fin 3, ∑ j : Fin 3, u i * (w.map M).prod i j * v j =
      dotProduct u (((w.map M).prod).mulVec v) := by
    simp only [dotProduct, Matrix.mulVec]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum, hmv w]
  simp [dotProduct, Fin.sum_univ_three, u]

lemma seqRec_hankel3_lb {r k : ℕ} {z : ℚ} (hz1 : z ≠ 1) (hz2 : z ≠ 2)
    (hcyc : ∀ w : List (Vec r), cycleVal z w = seqRec z w.length + (z - 2))
    (hfit : Fits r z k (fun w => 0 < w.length)) :
    3 ≤ k := by
  let pref : Fin 3 → List (Vec r) := ![ [0], [0, 0], [0, 0, 0] ]
  let suff : Fin 3 → List (Vec r) := ![ [], [0], [0, 0] ]
  have htest : ∀ i j : Fin 3, 0 < (pref i ++ suff j).length := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [pref, suff]
  let H : Matrix (Fin 3) (Fin 3) ℚ := Matrix.of (fun i j => cycleVal z (pref i ++ suff j))
  have hHle : H.rank ≤ k := hankel_rank_le_of_fits pref suff htest hfit
  have hs0 : seqRec z 0 = 2 := rfl
  have hs1 : seqRec z 1 = 2 := rfl
  have hs2 : seqRec z 2 = 2 * z := by simp [seqRec]; ring
  have hs3 : seqRec z 3 = 6 * z - 4 := by simp [seqRec, hs2]; ring
  have hs4 : seqRec z 4 = 2 * z ^ 2 + 8 * z - 8 := by simp [seqRec, hs3, hs2]; ring
  have hs5 : seqRec z 5 = 10 * z ^ 2 - 8 := by simp [seqRec, hs4, hs3]; ring
  have hH : ∀ i j : Fin 3, H i j = seqRec z (i.val + j.val + 1) + (z - 2) := by
    intro i j
    simp only [H, Matrix.of_apply, hcyc, List.length_append]
    fin_cases i <;> fin_cases j <;> simp [pref, suff]
  have hinj : Function.Injective H.mulVecLin := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hr0 : (H.mulVec v) 0 = 0 := congrFun hv 0
    have hr1 : (H.mulVec v) 1 = 0 := congrFun hv 1
    have hr2 : (H.mulVec v) 2 = 0 := congrFun hv 2
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hH] at hr0 hr1 hr2
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, hs1, hs2, hs3, hs4, hs5] at hr0 hr1 hr2
    have hneq1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hneq2 : z - 2 ≠ 0 := sub_ne_zero.mpr hz2
    have hcoef : (-4 : ℚ) * (z - 1) ^ 3 * (z - 2) ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hneq1)) (pow_ne_zero 2 hneq2)
    have hdet_v0 : (-4 * (z - 1) ^ 3 * (z - 2) ^ 2) * v 0 = 0 := by
      have hcomb :
          ((6 * z - 4 + (z - 2)) * (10 * z ^ 2 - 8 + (z - 2)) - (2 * z ^ 2 + 8 * z - 8 + (z - 2)) ^ 2) *
            ((2 + (z - 2)) * v 0 + (2 * z + (z - 2)) * v 1 + (6 * z - 4 + (z - 2)) * v 2) +
          ((6 * z - 4 + (z - 2)) * (2 * z ^ 2 + 8 * z - 8 + (z - 2)) - (2 * z + (z - 2)) * (10 * z ^ 2 - 8 + (z - 2))) *
            ((2 * z + (z - 2)) * v 0 + (6 * z - 4 + (z - 2)) * v 1 + (2 * z ^ 2 + 8 * z - 8 + (z - 2)) * v 2) +
          ((2 * z + (z - 2)) * (2 * z ^ 2 + 8 * z - 8 + (z - 2)) - (6 * z - 4 + (z - 2)) ^ 2) *
            ((6 * z - 4 + (z - 2)) * v 0 + (2 * z ^ 2 + 8 * z - 8 + (z - 2)) * v 1 + (10 * z ^ 2 - 8 + (z - 2)) * v 2) =
          (-4 * (z - 1) ^ 3 * (z - 2) ^ 2) * v 0 := by ring
      rw [← hcomb, hr0, hr1, hr2]; ring
    have hdet_v1 : (-4 * (z - 1) ^ 3 * (z - 2) ^ 2) * v 1 = 0 := by
      have hcomb :
          ((6 * z - 4 + (z - 2)) * (2 * z ^ 2 + 8 * z - 8 + (z - 2)) - (2 * z + (z - 2)) * (10 * z ^ 2 - 8 + (z - 2))) *
            ((2 + (z - 2)) * v 0 + (2 * z + (z - 2)) * v 1 + (6 * z - 4 + (z - 2)) * v 2) +
          ((2 + (z - 2)) * (10 * z ^ 2 - 8 + (z - 2)) - (6 * z - 4 + (z - 2)) ^ 2) *
            ((2 * z + (z - 2)) * v 0 + (6 * z - 4 + (z - 2)) * v 1 + (2 * z ^ 2 + 8 * z - 8 + (z - 2)) * v 2) +
          ((2 * z + (z - 2)) * (6 * z - 4 + (z - 2)) - (2 + (z - 2)) * (2 * z ^ 2 + 8 * z - 8 + (z - 2))) *
            ((6 * z - 4 + (z - 2)) * v 0 + (2 * z ^ 2 + 8 * z - 8 + (z - 2)) * v 1 + (10 * z ^ 2 - 8 + (z - 2)) * v 2) =
          (-4 * (z - 1) ^ 3 * (z - 2) ^ 2) * v 1 := by ring
      rw [← hcomb, hr0, hr1, hr2]; ring
    have hdet_v2 : (-4 * (z - 1) ^ 3 * (z - 2) ^ 2) * v 2 = 0 := by
      have hcomb :
          ((2 * z + (z - 2)) * (2 * z ^ 2 + 8 * z - 8 + (z - 2)) - (6 * z - 4 + (z - 2)) ^ 2) *
            ((2 + (z - 2)) * v 0 + (2 * z + (z - 2)) * v 1 + (6 * z - 4 + (z - 2)) * v 2) +
          ((2 * z + (z - 2)) * (6 * z - 4 + (z - 2)) - (2 + (z - 2)) * (2 * z ^ 2 + 8 * z - 8 + (z - 2))) *
            ((2 * z + (z - 2)) * v 0 + (6 * z - 4 + (z - 2)) * v 1 + (2 * z ^ 2 + 8 * z - 8 + (z - 2)) * v 2) +
          ((2 + (z - 2)) * (6 * z - 4 + (z - 2)) - (2 * z + (z - 2)) ^ 2) *
            ((6 * z - 4 + (z - 2)) * v 0 + (2 * z ^ 2 + 8 * z - 8 + (z - 2)) * v 1 + (10 * z ^ 2 - 8 + (z - 2)) * v 2) =
          (-4 * (z - 1) ^ 3 * (z - 2) ^ 2) * v 2 := by ring
      rw [← hcomb, hr0, hr1, hr2]; ring
    have hv0 : v 0 = 0 := (mul_eq_zero.mp hdet_v0).resolve_left hcoef
    have hv1 : v 1 = 0 := (mul_eq_zero.mp hdet_v1).resolve_left hcoef
    have hv2 : v 2 = 0 := (mul_eq_zero.mp hdet_v2).resolve_left hcoef
    funext i
    fin_cases i
    · exact hv0
    · exact hv1
    · exact hv2
  have hrank3 : H.rank = 3 := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
  omega

lemma solve_r0 (z : ℚ) (k : ℕ) :
    let least : ℕ := if z = 1 then 1 else if z = 2 then 2 else 3
    (Fits 0 z k (fun _ => True) ↔ least ≤ k) ∧
    (Fits 0 z k (fun w => 0 < w.length) ↔ (if z = 2 then least - 1 else least) ≤ k) := by
  dsimp only
  by_cases hz1 : z = 1
  · subst hz1
    have h12 : (1 : ℚ) ≠ 2 := by norm_num
    simp only [↓reduceIte, h12]
    have hcyc : ∀ w : List (Vec 0), cycleVal 1 w = 1 := by
      intro w
      rw [r0_cycleVal 1 w]
      have hseq : ∀ m : ℕ, seqRec 1 m = 2 := by
        intro m
        induction m using Nat.strong_induction_on with
        | ind m ih =>
          match m with
          | 0 => rfl
          | 1 => rfl
          | t + 2 =>
            rw [seqRec, ih (t + 1) (by omega), ih t (by omega)]
            ring
      rw [hseq w.length]
      ring
    have hup1 : Fits 0 1 1 (fun _ => True) := by
      refine ⟨fun _ => 1, fun _ => 1, fun _ => 1, ?_⟩
      intro w _
      have hprod : (w.map (fun _ : Vec 0 => (1 : Matrix (Fin 1) (Fin 1) ℚ))).prod = 1 := by
        induction w with
        | nil => rfl
        | cons _ ws ih => simp [ih]
      simp [hprod, hcyc w]
    have hlb : Fits 0 1 k (fun w => 0 < w.length) → 1 ≤ k := by
      intro hfit
      by_contra h0
      have hk0 : k = 0 := by omega
      subst hk0
      rcases hfit with ⟨u, v, M, hM⟩
      have h1 := hM [0] (by simp)
      rw [hcyc [0]] at h1
      simp at h1
    have hweak : Fits 0 1 k (fun _ => True) → Fits 0 1 k (fun w => 0 < w.length) := by
      rintro ⟨u, v, M, hM⟩; exact ⟨u, v, M, fun w _ => hM w trivial⟩
    exact ⟨⟨fun h => hlb (hweak h), fun hk => realizes_mono hk hup1⟩,
      ⟨hlb, fun hk => hweak (realizes_mono hk hup1)⟩⟩
  · by_cases hz2 : z = 2
    · subst hz2
      simp only [hz1, ↓reduceIte]
      have hseq : ∀ m : ℕ, 0 < m → seqRec 2 m = 2 ^ m := by
        intro m hm
        induction m using Nat.strong_induction_on with
        | ind m ih =>
          match m with
          | 0 => omega
          | 1 => simp [seqRec]
          | t + 2 =>
            rw [seqRec, ih (t + 1) (by omega) (by omega)]
            ring
      have hcyc_pos : ∀ w : List (Vec 0), 0 < w.length → cycleVal 2 w = (2 : ℚ) ^ w.length := by
        intro w hw
        rw [r0_cycleVal 2 w, hseq w.length hw]
        ring
      have hup_pos : Fits 0 2 1 (fun w => 0 < w.length) := by
        refine ⟨fun _ => 1, fun _ => 1, fun _ => !![2], ?_⟩
        intro w hw
        have hprod : ∀ l : List (Vec 0), (l.map (fun _ : Vec 0 => !![(2 : ℚ)])).prod 0 0 = 2 ^ l.length := by
          intro l
          induction l with
          | nil => simp
          | cons _ ls ih =>
            simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
            rw [Matrix.mul_apply, Fin.sum_univ_one, ih]
            simp
        rw [Fin.sum_univ_one, Fin.sum_univ_one]
        simp only [one_mul, mul_one]
        rw [hprod w, hcyc_pos w hw]
      have hup_all : Fits 0 2 2 (fun _ => True) := fits_all_of_fits_pos 2 hup_pos
      have hlb_pos : Fits 0 2 k (fun w => 0 < w.length) → 1 ≤ k := by
        intro hfit
        by_contra h0
        have hk0 : k = 0 := by omega
        subst hk0
        rcases hfit with ⟨u, v, M, hM⟩
        have h1 := hM [0] (by simp)
        rw [hcyc_pos [0] (by simp)] at h1
        simp at h1
      have hlb_all : Fits 0 2 k (fun _ => True) → 2 ≤ k := by
        intro hfit
        let pref : Fin 2 → List (Vec 0) := ![ [], [0] ]
        let H : Matrix (Fin 2) (Fin 2) ℚ := Matrix.of (fun i j => cycleVal 2 (pref i ++ pref j))
        have hHle : H.rank ≤ k := hankel_rank_le_of_fits pref pref (fun _ _ => trivial) hfit
        have h00 : H 0 0 = 2 := by simp [H, pref, cycleVal_nil]
        have h01 : H 0 1 = 2 := by
          change cycleVal 2 ([] ++ [0]) = 2
          rw [List.nil_append, hcyc_pos [0] (by simp)]
          norm_num
        have h10 : H 1 0 = 2 := by
          change cycleVal 2 ([0] ++ []) = 2
          rw [List.append_nil, hcyc_pos [0] (by simp)]
          norm_num
        have h11 : H 1 1 = 4 := by
          change cycleVal 2 ([0] ++ [0]) = 4
          rw [hcyc_pos ([0] ++ [0]) (by simp)]
          norm_num
        have hinj : Function.Injective H.mulVecLin := by
          rw [injective_iff_map_eq_zero]
          intro v hv
          have hr0 : (H.mulVec v) 0 = 0 := congrFun hv 0
          have hr1 : (H.mulVec v) 1 = 0 := congrFun hv 1
          simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h00, h01, h10, h11] at hr0 hr1
          funext i; fin_cases i
          · change v 0 = 0; linarith
          · change v 1 = 0; linarith
        have hrank : H.rank = 2 := by
          rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card,
            Fintype.card_fin]
        omega
      exact ⟨⟨hlb_all, fun hk => realizes_mono hk hup_all⟩,
        ⟨hlb_pos, fun hk => realizes_mono hk hup_pos⟩⟩
    · simp only [hz1, hz2, ↓reduceIte]
      have hup3 : Fits 0 z 3 (fun _ => True) := by
        rcases seqRec_three_realizes 0 z with ⟨u, v, M, hM⟩
        exact ⟨u, v, M, fun w _ => (hM w trivial).trans (r0_cycleVal z w).symm⟩
      have hweak : Fits 0 z k (fun _ => True) → Fits 0 z k (fun w => 0 < w.length) := by
        rintro ⟨u, v, M, hM⟩; exact ⟨u, v, M, fun w _ => hM w trivial⟩
      have hlb : Fits 0 z k (fun w => 0 < w.length) → 3 ≤ k :=
        seqRec_hankel3_lb hz1 hz2 (r0_cycleVal z)
      exact ⟨⟨fun h => hlb (hweak h), fun hk => realizes_mono hk hup3⟩,
        ⟨hlb, fun hk => hweak (realizes_mono hk hup3)⟩⟩

lemma zero_cycleVal (r : ℕ) (w : List (Vec r)) :
    cycleVal (r := r) 0 w = seqRec 0 w.length - 2 := by
  let B : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; -1, 1]
  have hB_pow : ∀ m : ℕ, Matrix.trace (B ^ m) = seqRec 0 m := by
    have hB2 : B * B = (2 : ℚ) • B + (-2 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [B, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      match m with
      | 0 => simp [seqRec, Matrix.trace_one]
      | 1 => simp [seqRec, Matrix.trace, Matrix.diag, Fin.sum_univ_two, B]; norm_num
      | t + 2 =>
        have hpow2 : B ^ (t + 2) = (B * B) * B ^ t := by rw [Nat.add_comm t 2, pow_add, pow_two]
        rw [hpow2, hB2, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
          Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
        have h1 : B * B ^ t = B ^ (t + 1) := by rw [pow_succ']
        rw [h1, ih (t + 1) (by omega), ih t (by omega), seqRec]
        ring
  have hf0 : ∀ a : Vec r, fVal 0 a = -1 := by
    intro a; unfold fVal; by_cases ha : a = 0 <;> simp [ha]
  have hstruct : ∀ l : List (Vec r),
      let P := (l.map (TMat 0)).prod
      let Bm := B ^ l.length
      P none none = Bm 0 0 ∧
      (∀ a : Vec r, P (some a) none = Bm 1 0) ∧
      (∑ b : Vec r, P none (some b) = Bm 0 1) ∧
      ∃ g : Vec r → ℚ, (∑ b : Vec r, g b = Bm 1 1 - 1) ∧
        ∀ a b : Vec r, P (some a) (some b) = (if b = a + l.sum then 1 else 0) + g b := by
    intro l
    induction l with
    | nil =>
      refine ⟨by simp, fun a => by simp [Matrix.one_apply], by simp [Matrix.one_apply], fun _ => 0,
        by simp, fun a b => by simp [Matrix.one_apply, eq_comm]⟩
    | cons h ws ih =>
      dsimp only at ih ⊢
      rcases ih with ⟨h00, h10, h01, g, hg_sum, hg_eq⟩
      simp only [List.map_cons, List.prod_cons, List.length_cons, List.sum_cons, pow_succ']
      have hB00 : (B * B ^ ws.length) 0 0 = (B ^ ws.length) 0 0 + (B ^ ws.length) 1 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [B]
      have hB10 : (B * B ^ ws.length) 1 0 = - (B ^ ws.length) 0 0 + (B ^ ws.length) 1 0 := by
        rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [B]
      have hB01 : (B * B ^ ws.length) 0 1 = (B ^ ws.length) 0 1 + (B ^ ws.length) 1 1 := by
        rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [B]
      have hB11 : (B * B ^ ws.length) 1 1 = - (B ^ ws.length) 0 1 + (B ^ ws.length) 1 1 := by
        rw [Matrix.mul_apply, Fin.sum_univ_two]; simp [B]
      refine ⟨?_, ?_, ?_, fun b => g b - (ws.map (TMat 0)).prod none (some b), ?_, ?_⟩
      · rw [Matrix.mul_apply, Fintype.sum_option, hB00]
        simp only [TMat, Option.elim_none, Option.elim_some, one_mul, h00]
        congr 1
        rw [Finset.sum_eq_single h]
        · simp [h10]
        · intro b _ hb; simp [hb]
        · intro h'; exact False.elim (h' (Finset.mem_univ _))
      · intro a
        rw [Matrix.mul_apply, Fintype.sum_option, hB10]
        simp only [TMat, Option.elim_some, Option.elim_none, hf0, h00]
        have hs : ∑ x : Vec r, (if x = a + h then (1 : ℚ) else 0) * (ws.map (TMat 0)).prod (some x) none =
            (B ^ ws.length) 1 0 := by
          rw [Finset.sum_eq_single (a + h)]
          · simp [h10]
          · intro x _ hx; simp [hx]
          · intro h'; exact False.elim (h' (Finset.mem_univ _))
        rw [hs]; ring
      · have hent : ∀ b : Vec r, (TMat 0 h * (ws.map (TMat 0)).prod) none (some b) =
            (ws.map (TMat 0)).prod none (some b) + (if b = h + ws.sum then 1 else 0) + g b := by
          intro b
          rw [Matrix.mul_apply, Fintype.sum_option]
          simp only [TMat, Option.elim_none, Option.elim_some, one_mul]
          have hs : ∑ x : Vec r, (if x = h then (1 : ℚ) else 0) * (ws.map (TMat 0)).prod (some x) (some b) =
              (if b = h + ws.sum then 1 else 0) + g b := by
            rw [Finset.sum_eq_single h]
            · simp [hg_eq h b]
            · intro x _ hx; simp [hx]
            · intro h'; exact False.elim (h' (Finset.mem_univ _))
          rw [hs]; ring
        simp_rw [hent, Finset.sum_add_distrib, h01, hg_sum, hB01]
        have h1 : ∑ b : Vec r, (if b = h + ws.sum then (1 : ℚ) else 0) = 1 := by
          rw [Finset.sum_eq_single (h + ws.sum)]
          · simp
          · intro b _ hb; simp [hb]
          · intro h'; exact False.elim (h' (Finset.mem_univ _))
        rw [h1]; ring
      · rw [Finset.sum_sub_distrib, hg_sum, h01, hB11]; ring
      · intro a b
        rw [Matrix.mul_apply, Fintype.sum_option]
        simp only [TMat, Option.elim_some, Option.elim_none, hf0]
        have hs : ∑ x : Vec r, (if x = a + h then (1 : ℚ) else 0) * (ws.map (TMat 0)).prod (some x) (some b) =
            (if b = a + (h + ws.sum) then 1 else 0) + g b := by
          rw [Finset.sum_eq_single (a + h)]
          · simp [hg_eq (a + h) b, add_assoc]
          · intro x _ hx; simp [hx]
          · intro h'; exact False.elim (h' (Finset.mem_univ _))
        rw [hs]; ring
  rcases hstruct w with ⟨h00, _, _, g, hg_sum, hg_eq⟩
  unfold cycleVal
  rw [Matrix.trace, Fintype.sum_option]
  simp only [Matrix.diag_apply, h00]
  simp_rw [hg_eq, Finset.sum_add_distrib, hg_sum, hf0]
  have hdiag : ∑ a : Vec r, (if a = a + w.sum then (1 : ℚ) else 0) =
      if w.sum = 0 then ((2 ^ r : ℕ) : ℚ) else 0 := by
    by_cases h0 : w.sum = 0
    · simp [h0, card_vec]
    · simp only [h0, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro a _
      have hne' : a ≠ a + w.sum := by
        intro h
        have h1 : a + a = a + (a + w.sum) := congrArg (a + ·) h
        rw [vec_add_self, ← add_assoc, vec_add_self, zero_add] at h1
        exact h0 h1.symm
      simp [hne']
  rw [hdiag]
  have htrB : (B ^ w.length) 0 0 + (B ^ w.length) 1 1 = seqRec 0 w.length := by
    have := hB_pow w.length
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using this
  linarith

lemma solve_z0 (r : ℕ) (_hr : r ≠ 0) (k : ℕ) :
    (Fits r 0 k (fun _ => True) ↔ 3 ≤ k) ∧
    (Fits r 0 k (fun w => 0 < w.length) ↔ 3 ≤ k) := by
  have hcyc : ∀ w : List (Vec r), cycleVal 0 w = seqRec 0 w.length + (0 - 2) := by
    intro w; rw [zero_cycleVal r w]; ring
  have hup3 : Fits r 0 3 (fun _ => True) := by
    rcases seqRec_three_realizes r 0 with ⟨u, v, M, hM⟩
    exact ⟨u, v, M, fun w _ => (hM w trivial).trans (hcyc w).symm⟩
  have hweak : Fits r 0 k (fun _ => True) → Fits r 0 k (fun w => 0 < w.length) := by
    rintro ⟨u, v, M, hM⟩; exact ⟨u, v, M, fun w _ => hM w trivial⟩
  have hlb : Fits r 0 k (fun w => 0 < w.length) → 3 ≤ k :=
    seqRec_hankel3_lb (by norm_num) (by norm_num) hcyc
  exact ⟨⟨fun h => hlb (hweak h), fun hk => realizes_mono hk hup3⟩,
    ⟨hlb, fun hk => hweak (realizes_mono hk hup3)⟩⟩

abbrev kerE (r : ℕ) : Matrix (Option (Vec r)) (Vec r) ℚ := fun s c =>
  s.elim (if c = 0 then 1 else 0)
    (fun a => if c = 0 then 0 else if a = c then 1 else if a = 0 then -1 else 0)

abbrev kerP (r : ℕ) : Matrix (Vec r) (Option (Vec r)) ℚ := fun c s =>
  s.elim (if c = 0 then 1 else 0)
    (fun a => if c = 0 then 0 else if a = c then 1 else 0)

abbrev kerM (r : ℕ) : Vec r → Matrix (Vec r) (Vec r) ℚ :=
  fun h => kerP r * TMat ((2 ^ r : ℕ) : ℚ) h * kerE r

lemma ker_trace_zq (r : ℕ) :
    ∀ w : List (Vec r), cycleVal ((2 ^ r : ℕ) : ℚ) w = Matrix.trace (w.map (kerM r)).prod := by
  let z : ℚ := ((2 ^ r : ℕ) : ℚ)
  let E : Matrix (Option (Vec r)) (Vec r) ℚ := kerE r
  let P : Matrix (Vec r) (Option (Vec r)) ℚ := kerP r
  let M : Vec r → Matrix (Vec r) (Vec r) ℚ := kerM r
  change ∀ w : List (Vec r), cycleVal z w = Matrix.trace (w.map M).prod
  have hPE : P * E = 1 := by
    ext c1 c2
    rw [Matrix.mul_apply, Fintype.sum_option, Matrix.one_apply]
    by_cases h1 : c1 = 0
    · subst h1
      simp [P, E, eq_comm]
    · simp only [P, E, Option.elim_none, Option.elim_some, h1, ↓reduceIte, zero_mul, zero_add]
      rw [Finset.sum_eq_single c1]
      · by_cases h2 : c2 = 0
        · subst h2; simp [h1]
        · by_cases h12 : c1 = c2 <;> simp [h1, h2, h12]
      · intro a _ ha; simp [ha]
      · intro h'; exact False.elim (h' (Finset.mem_univ _))
  have hEP_ker : ∀ v : Option (Vec r) → ℚ, (∑ a : Vec r, v (some a)) = 0 →
      (E * P).mulVec v = v := by
    intro v hv
    rw [← Matrix.mulVec_mulVec]
    have hPv0 : P.mulVec v 0 = v none := by
      rw [Matrix.mulVec, dotProduct, Fintype.sum_option]; simp [P]
    have hPvc : ∀ c : Vec r, c ≠ 0 → P.mulVec v c = v (some c) := by
      intro c hc
      rw [Matrix.mulVec, dotProduct, Fintype.sum_option]
      simp only [P, Option.elim_none, Option.elim_some, hc, ↓reduceIte, zero_mul, zero_add]
      rw [Finset.sum_eq_single c]
      · simp
      · intro a _ ha; simp [ha]
      · intro h'; exact False.elim (h' (Finset.mem_univ _))
    funext s
    rw [Matrix.mulVec, dotProduct]
    cases s with
    | none =>
      rw [Finset.sum_eq_single (0 : Vec r)]
      · simp [E, hPv0]
      · intro c _ hc; simp [E, hc]
      · intro h'; exact False.elim (h' (Finset.mem_univ _))
    | some a =>
      by_cases ha0 : a = 0
      · subst ha0
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Vec r))]
        have h0 : E (some 0) 0 * P.mulVec v 0 = 0 := by simp [E]
        rw [h0, zero_add]
        have her : ∑ c ∈ Finset.univ.erase (0 : Vec r), E (some 0) c * P.mulVec v c =
            ∑ c ∈ Finset.univ.erase (0 : Vec r), (-1 : ℚ) * v (some c) := by
          apply Finset.sum_congr rfl
          intro c hc
          have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
          have hEc : E (some 0) c = -1 := by simp [E, hc0, Ne.symm hc0]
          rw [hEc, hPvc c hc0]
        rw [her, ← Finset.mul_sum]
        have htot := Finset.add_sum_erase Finset.univ (fun c : Vec r => v (some c)) (Finset.mem_univ 0)
        linarith
      · rw [Finset.sum_eq_single a]
        · have hEa : E (some a) a = 1 := by simp [E, ha0]
          rw [hEa, one_mul, hPvc a ha0]
        · intro c _ hca
          have hEc : E (some a) c = 0 := by
            by_cases hc0 : c = 0
            · simp [E, hc0]
            · simp [E, hc0, Ne.symm hca, ha0]
          rw [hEc, zero_mul]
        · intro h'; exact False.elim (h' (Finset.mem_univ _))
  have huT : ∀ (h : Vec r) (s : Option (Vec r)),
      ∑ a : Vec r, TMat z h (some a) s = s.elim 0 (fun _ => 1) := by
    intro h s
    cases s with
    | none =>
      simp only [TMat, Option.elim_some, Option.elim_none, sum_fVal, z, Nat.cast_pow, Nat.cast_ofNat,
        sub_self]
    | some b =>
      simp only [TMat, Option.elim_some]
      rw [Finset.sum_eq_single (b + h)]
      · have h1 : b + h + h = b := by rw [add_assoc, vec_add_self, add_zero]
        simp [h1]
      · intro a _ ha
        have hne : b ≠ a + h := by
          intro heq
          apply ha
          have : b + h = a + h + h := congrArg (· + h) heq
          rw [add_assoc, vec_add_self, add_zero] at this
          exact this.symm
        simp [hne]
      · intro h'; exact False.elim (h' (Finset.mem_univ _))
  have huProd : ∀ (w : List (Vec r)) (s : Option (Vec r)),
      ∑ a : Vec r, (w.map (TMat z)).prod (some a) s = s.elim 0 (fun _ => 1) := by
    intro w
    induction w with
    | nil =>
      intro s
      cases s with
      | none => simp [Matrix.one_apply]
      | some b =>
        simp only [List.map_nil, List.prod_nil, Option.elim_some]
        rw [Finset.sum_eq_single b]
        · simp [Matrix.one_apply]
        · intro a _ ha; simp [Matrix.one_apply, ha]
        · intro h'; exact False.elim (h' (Finset.mem_univ _))
    | cons h ws ih =>
      intro s
      simp only [List.map_cons, List.prod_cons]
      simp_rw [Matrix.mul_apply]
      rw [Finset.sum_comm]
      have h1 : ∑ x : Option (Vec r), ∑ a : Vec r, TMat z h (some a) x * (ws.map (TMat z)).prod x s =
          ∑ x : Option (Vec r), (∑ a : Vec r, TMat z h (some a) x) * (ws.map (TMat z)).prod x s := by
        apply Finset.sum_congr rfl; intro x _; rw [Finset.sum_mul]
      rw [h1]
      simp_rw [huT h]
      rw [Fintype.sum_option]
      simp [ih s]
  have hcol_ker : ∀ (h : Vec r) (c : Vec r), ∑ a : Vec r, (TMat z h * E) (some a) c = 0 := by
    intro h c
    simp_rw [Matrix.mul_apply]
    rw [Finset.sum_comm]
    have h1 : ∑ x : Option (Vec r), ∑ a : Vec r, TMat z h (some a) x * E x c =
        ∑ x : Option (Vec r), (∑ a : Vec r, TMat z h (some a) x) * E x c := by
      apply Finset.sum_congr rfl; intro x _; rw [Finset.sum_mul]
    rw [h1]
    simp_rw [huT h]
    rw [Fintype.sum_option]
    simp only [Option.elim_none, zero_mul, Option.elim_some, one_mul, zero_add]
    by_cases hc0 : c = 0
    · simp [E, hc0]
    · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c)]
      have h0mem : (0 : Vec r) ∈ Finset.univ.erase c := Finset.mem_erase.mpr ⟨Ne.symm hc0, Finset.mem_univ 0⟩
      rw [← Finset.add_sum_erase _ _ h0mem]
      have hrest : ∑ b ∈ (Finset.univ.erase c).erase 0, E (some b) c = 0 := by
        apply Finset.sum_eq_zero
        intro b hb
        have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
        have hbc : b ≠ c := (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1
        simp [E, hc0, hbc, hb0]
      rw [hrest, add_zero]
      have hEc : E (some c) c = 1 := by simp [E, hc0]
      have hE0 : E (some 0) c = -1 := by simp [E, hc0, Ne.symm hc0]
      rw [hEc, hE0]; ring
  have hinter : ∀ h : Vec r, TMat z h * E = E * M h := by
    intro h
    change TMat z h * E = E * (P * TMat z h * E)
    rw [Matrix.mul_assoc P (TMat z h) E, ← Matrix.mul_assoc E P]
    ext s c
    have hv := congrFun (hEP_ker (fun u => (TMat z h * E) u c) (hcol_ker h c)) s
    have hlhs : ((E * P).mulVec (fun u => (TMat z h * E) u c)) s = ((E * P) * (TMat z h * E)) s c := by
      rw [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    rw [hlhs] at hv
    exact hv.symm
  have hprod_inter : ∀ w : List (Vec r), (w.map (TMat z)).prod * E = E * (w.map M).prod := by
    intro w
    induction w with
    | nil => simp
    | cons h ws ih =>
      simp only [List.map_cons, List.prod_cons, Matrix.mul_assoc, ih, ← Matrix.mul_assoc (TMat z h) E, hinter h]
  intro w
  let W := (w.map (TMat z)).prod
  have hEP_plus : ∀ s t : Option (Vec r),
      (E * P) s t = (1 : Matrix (Option (Vec r)) (Option (Vec r)) ℚ) s t -
        (if s = some 0 then t.elim 0 (fun _ => 1) else 0) := by
    intro s t
    rw [Matrix.mul_apply, Matrix.one_apply]
    cases s with
    | none =>
      rw [Finset.sum_eq_single (0 : Vec r)]
      · cases t <;> simp [E, P]
      · intro c _ hc; simp [E, hc]
      · intro h'; exact False.elim (h' (Finset.mem_univ _))
    | some a =>
      by_cases ha0 : a = 0
      · subst ha0
        cases t with
        | none =>
          simp only [Option.elim_none, ↓reduceIte, sub_zero, reduceCtorEq]
          rw [Finset.sum_eq_single (0 : Vec r)]
          · simp [E, P]
          · intro c _ hc; simp [P, hc]
          · intro h'; exact False.elim (h' (Finset.mem_univ _))
        | some b =>
          by_cases hb0 : b = 0
          · subst hb0
            simp only [Option.elim_some, ↓reduceIte, sub_self]
            apply Finset.sum_eq_zero
            intro c _
            by_cases hc0 : c = 0 <;> simp [E, P, hc0, Ne.symm]
          · simp only [Option.elim_some, ↓reduceIte, Option.some.injEq, Ne.symm hb0, zero_sub]
            rw [Finset.sum_eq_single b]
            · simp [E, P, hb0, Ne.symm hb0]
            · intro c _ hcb
              by_cases hc0 : c = 0 <;> simp [E, P, hc0, hcb, Ne.symm hcb]
            · intro h'; exact False.elim (h' (Finset.mem_univ _))
      · simp only [Option.some.injEq, ha0, ↓reduceIte, sub_zero]
        rw [Finset.sum_eq_single a]
        · cases t with
          | none => simp [E, P, ha0]
          | some b =>
            by_cases hab : a = b
            · subst hab; simp [E, P, ha0]
            · simp [E, P, ha0, hab, Ne.symm hab]
        · intro c _ hca
          by_cases hc0 : c = 0 <;> simp [E, hc0, Ne.symm hca, ha0]
        · intro h'; exact False.elim (h' (Finset.mem_univ _))
  have htr_M : Matrix.trace (w.map M).prod = Matrix.trace (W * (E * P)) := by
    have h1 : (w.map M).prod = P * W * E := by
      calc (w.map M).prod = (P * E) * (w.map M).prod := by rw [hPE, Matrix.one_mul]
        _ = P * (E * (w.map M).prod) := Matrix.mul_assoc _ _ _
        _ = P * (W * E) := by rw [← hprod_inter w]
        _ = P * W * E := (Matrix.mul_assoc _ _ _).symm
    rw [h1, Matrix.mul_assoc P W E, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have htr_W : Matrix.trace W = Matrix.trace (w.map M).prod + 1 := by
    rw [htr_M]
    have hdiff : Matrix.trace W - Matrix.trace (W * (E * P)) = 1 := by
      rw [Matrix.trace, Matrix.trace, ← Finset.sum_sub_distrib]
      have hterm : ∀ s : Option (Vec r),
          Matrix.diag W s - Matrix.diag (W * (E * P)) s =
          W s (some 0) * s.elim 0 (fun _ => 1) := by
        intro s
        change W s s - (W * (E * P)) s s = _
        rw [Matrix.mul_apply]
        simp_rw [hEP_plus, mul_sub, Finset.sum_sub_distrib]
        have h1 : ∑ t : Option (Vec r), W s t * (1 : Matrix (Option (Vec r)) (Option (Vec r)) ℚ) t s = W s s := by
          rw [Finset.sum_eq_single s]
          · simp
          · intro t _ ht; simp [ht]
          · intro h'; exact False.elim (h' (Finset.mem_univ _))
        have h2 : ∑ t : Option (Vec r), W s t * (if t = some 0 then s.elim 0 (fun _ => 1) else 0) =
            W s (some 0) * s.elim 0 (fun _ => 1) := by
          rw [Finset.sum_eq_single (some 0)]
          · simp
          · intro t _ ht; simp [ht]
          · intro h'; exact False.elim (h' (Finset.mem_univ _))
        rw [h1, h2]; ring
      have hsum : ∑ s : Option (Vec r), (Matrix.diag W s - Matrix.diag (W * (E * P)) s) =
          ∑ s : Option (Vec r), W s (some 0) * s.elim 0 (fun _ => 1) :=
        Finset.sum_congr rfl (fun s _ => hterm s)
      rw [hsum, Fintype.sum_option]
      simp only [Option.elim_none, mul_zero, zero_add, Option.elim_some, mul_one]
      exact huProd w (some 0)
    linarith
  unfold cycleVal fVal
  rw [htr_W]
  by_cases hs0 : w.sum = 0 <;> simp [hs0, z]

lemma solve_r1_z2 (k : ℕ) :
    (Fits 1 2 k (fun _ => True) ↔ 2 ≤ k) ∧
    (Fits 1 2 k (fun w => 0 < w.length) ↔ 1 ≤ k) := by
  have hcyc_pos : ∀ w : List (Vec 1), 0 < w.length →
      cycleVal (r := 1) 2 w = (w.map (fun h : Vec 1 => if h = 0 then (2 : ℚ) else 0)).prod := by
    let e : Option (Vec 1) ≃ Fin 3 :=
      { toFun := fun s => s.elim 0 (fun a => if a = 0 then 1 else 2)
        invFun := fun i => if i = 0 then none else if i = 1 then some 0 else some (fun _ => 1)
        left_inv := fun s => by
          cases s with
          | none => rfl
          | some a =>
            by_cases ha : a = 0
            · simp [ha]
            · have ha1 : a = (fun _ => 1) := by
                funext i
                have hi : i = 0 := Subsingleton.elim i 0
                subst hi
                have hne : a 0 ≠ 0 := fun h => ha (funext fun j => by rw [Subsingleton.elim j 0]; exact h)
                have hlt := ZMod.val_lt (a 0)
                have hne_val : (a 0).val ≠ 0 := fun hv => hne (ZMod.val_injective 2 (by simpa using hv))
                have h1v : (1 : ZMod 2).val = 1 := rfl
                exact ZMod.val_injective 2 (by omega)
              have h10 : (fun _ : Fin 1 => (1 : ZMod 2)) ≠ 0 := fun h => by
                have := congrFun h 0; exact absurd this (by decide)
              simp [ha1, h10]
        right_inv := fun i => by
          fin_cases i
          · rfl
          · simp
          · have h10 : (fun _ : Fin 1 => (1 : ZMod 2)) ≠ 0 := fun h => by
              have := congrFun h 0; exact absurd this (by decide)
            simp [h10] }
    let Q0 : Matrix (Fin 3) (Fin 3) ℚ := !![1, 1, 0; 1, 1, 0; -1, 0, 1]
    let Q1 : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 1; 1, 0, 1; -1, 1, 0]
    let Q : Vec 1 → Matrix (Fin 3) (Fin 3) ℚ := fun h => if h = 0 then Q0 else Q1
    have hT_sub : ∀ h : Vec 1, (TMat (r := 1) 2 h).submatrix e.symm e.symm = Q h := by
      intro h
      have h10 : (fun _ : Fin 1 => (1 : ZMod 2)) ≠ 0 := fun heq => by
        have := congrFun heq 0; exact absurd this (by decide)
      by_cases hh : h = 0
      · subst hh
        ext i j
        fin_cases i <;> fin_cases j <;> simp [e, TMat, Q, Q0, fVal, h10, Ne.symm h10] <;> norm_num
      · have hh1 : h = (fun _ => 1) := by
          funext i
          rw [Subsingleton.elim i 0]
          have hne : h 0 ≠ 0 := fun h' => hh (funext fun j => by rw [Subsingleton.elim j 0]; exact h')
          have hlt := ZMod.val_lt (h 0)
          have hne_val : (h 0).val ≠ 0 := fun hv => hne (ZMod.val_injective 2 (by simpa using hv))
          have h1v : (1 : ZMod 2).val = 1 := rfl
          exact ZMod.val_injective 2 (by omega)
        subst hh1
        have h11 : (fun _ : Fin 1 => (1 : ZMod 2)) + (fun _ : Fin 1 => (1 : ZMod 2)) = 0 := vec_add_self _
        ext i j
        fin_cases i <;> fin_cases j <;> simp [e, TMat, Q, Q1, fVal, h10, Ne.symm h10, h11] <;> norm_num
    have htr_Q : ∀ w : List (Vec 1), Matrix.trace (w.map (TMat (r := 1) 2)).prod = Matrix.trace (w.map Q).prod := by
      intro w
      have hprod : ((w.map (TMat (r := 1) 2)).prod).submatrix e.symm e.symm = (w.map Q).prod := by
        induction w with
        | nil =>
          ext i j; simp [Matrix.submatrix_apply, Matrix.one_apply, e.symm.injective.eq_iff]
        | cons a ws ih =>
          simp only [List.map_cons, List.prod_cons, ← ih, ← hT_sub a]
          ext i j
          rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply]
          simp only [Matrix.submatrix_apply]
          exact (e.symm.sum_comp (fun x => TMat 2 a (e.symm i) x * (ws.map (TMat 2)).prod x (e.symm j))).symm
      rw [← hprod]
      simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
      exact (e.symm.sum_comp (fun x => (w.map (TMat 2)).prod x x)).symm
    let B : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 0; 1, -1, 1; -1, 1, 0]
    let Binv : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 0; 1, 0, 1; 0, 1, 1]
    have hBB : Binv * B = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [B, Binv, Matrix.mul_apply, Fin.sum_univ_three]
    have hQ0_conj : Binv * Q0 * B = !![2, -1, 1; 0, 0, 1; 0, 0, 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [B, Binv, Q0, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
    have hQ1_conj : Binv * Q1 * B = !![0, 1, 0; 0, 0, 1; 0, 0, 1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [B, Binv, Q1, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
    have hconj_prod : ∀ w : List (Vec 1), 0 < w.length →
        ∃ c1 c2 : ℚ, Binv * (w.map Q).prod * B =
          !![(w.map (fun h : Vec 1 => if h = 0 then (2 : ℚ) else 0)).prod, c1, c2;
             0, 0, 1;
             0, 0, 1] := by
      intro w hw
      induction w with
      | nil => simp at hw
      | cons h ws ih =>
        cases ws with
        | nil =>
          by_cases hh : h = 0
          · refine ⟨-1, 1, ?_⟩
            simpa [Q, hh] using hQ0_conj
          · refine ⟨1, 0, ?_⟩
            simpa [Q, hh] using hQ1_conj
        | cons h2 ws2 =>
          obtain ⟨c1, c2, hih⟩ := ih (by simp)
          have hmul : Binv * ((h :: h2 :: ws2).map Q).prod * B =
              (Binv * Q h * B) * (Binv * ((h2 :: ws2).map Q).prod * B) := by
            simp only [List.map_cons, List.prod_cons]
            calc Binv * (Q h * ((h2 :: ws2).map Q).prod) * B
                = (Binv * Q h) * (1 * ((h2 :: ws2).map Q).prod * B) := by simp [Matrix.mul_assoc]
              _ = (Binv * Q h) * ((B * Binv) * ((h2 :: ws2).map Q).prod * B) := by
                    have hBB' : B * Binv = 1 := by
                      ext i j; fin_cases i <;> fin_cases j <;> simp [B, Binv, Matrix.mul_apply, Fin.sum_univ_three]
                    rw [hBB']
              _ = (Binv * Q h * B) * (Binv * ((h2 :: ws2).map Q).prod * B) := by simp [Matrix.mul_assoc]
          rw [hmul, hih]
          by_cases hh : h = 0
          · simp only [Q, hh, ↓reduceIte, hQ0_conj, List.map_cons, List.prod_cons]
            refine ⟨2 * c1, 2 * c2, ?_⟩
            ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;> ring
          · simp only [Q, hh, ↓reduceIte, hQ1_conj, List.map_cons, List.prod_cons, zero_mul]
            refine ⟨0, 1, ?_⟩
            ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    intro w hw
    obtain ⟨c1, c2, hc⟩ := hconj_prod w hw
    have htr_eq : Matrix.trace (w.map Q).prod =
        (w.map (fun h : Vec 1 => if h = 0 then (2 : ℚ) else 0)).prod + 1 := by
      have h1 : Matrix.trace (Binv * (w.map Q).prod * B) = Matrix.trace (w.map Q).prod := by
        have hBB' : B * Binv = 1 := by
          ext i j; fin_cases i <;> fin_cases j <;> simp [B, Binv, Matrix.mul_apply, Fin.sum_univ_three]
        rw [Matrix.trace_mul_cycle, hBB', Matrix.one_mul]
      rw [← h1, hc]
      simp [Matrix.trace, Matrix.diag, Fin.sum_univ_three]
    unfold cycleVal fVal
    rw [htr_Q w, htr_eq]
    by_cases hs : w.sum = 0 <;> simp [hs] <;> ring
  have hup_pos : Fits 1 2 1 (fun w => 0 < w.length) := by
    refine ⟨fun _ => 1, fun _ => 1, fun h => !![if h = 0 then 2 else 0], ?_⟩
    intro w hw
    have hprod : ∀ l : List (Vec 1),
        (l.map (fun h : Vec 1 => !![if h = 0 then (2 : ℚ) else 0])).prod 0 0 =
        (l.map (fun h : Vec 1 => if h = 0 then (2 : ℚ) else 0)).prod := by
      intro l
      induction l with
      | nil => simp
      | cons a ls ih =>
        simp only [List.map_cons, List.prod_cons]
        rw [Matrix.mul_apply, Fin.sum_univ_one, ih]
        simp
    simp [hprod w, hcyc_pos w hw]
  have hup_all : Fits 1 2 2 (fun _ => True) := fits_all_of_fits_pos 2 hup_pos
  have hlb_pos : Fits 1 2 k (fun w => 0 < w.length) → 1 ≤ k := by
    intro hfit
    by_contra h0
    have hk0 : k = 0 := by omega
    subst hk0
    rcases hfit with ⟨u, v, M', hM'⟩
    have h1 := hM' [0] (by simp)
    rw [hcyc_pos [0] (by simp)] at h1
    simp at h1
  have hlb_all : Fits 1 2 k (fun _ => True) → 2 ≤ k := by
    intro hfit
    let pref : Fin 2 → List (Vec 1) := ![ [], [0] ]
    let H : Matrix (Fin 2) (Fin 2) ℚ := Matrix.of (fun i j => cycleVal 2 (pref i ++ pref j))
    have hHle : H.rank ≤ k := hankel_rank_le_of_fits pref pref (fun _ _ => trivial) hfit
    have h00 : H 0 0 = 2 := by simp [H, pref, cycleVal_nil]
    have h01 : H 0 1 = 2 := by simp [H, pref, hcyc_pos [0] (by simp)]
    have h10 : H 1 0 = 2 := by simp [H, pref, hcyc_pos [0] (by simp)]
    have h11 : H 1 1 = 4 := by simp [H, pref, hcyc_pos [0, 0] (by simp)]; norm_num
    have hinj : Function.Injective H.mulVecLin := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      have hr0 : (H.mulVec v) 0 = 0 := congrFun hv 0
      have hr1 : (H.mulVec v) 1 = 0 := congrFun hv 1
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h00, h01, h10, h11] at hr0 hr1
      funext i; fin_cases i
      · change v 0 = 0; linarith
      · change v 1 = 0; linarith
    have hrank : H.rank = 2 := by
      rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card,
        Fintype.card_fin]
    omega
  exact ⟨⟨hlb_all, fun hk => realizes_mono hk hup_all⟩,
    ⟨hlb_pos, fun hk => realizes_mono hk hup_pos⟩⟩

lemma solve_zq_ge4 (r : ℕ) (hr2 : 2 ≤ r) (k : ℕ) :
    let q : ℕ := 2 ^ r
    (Fits r (q : ℚ) k (fun _ => True) ↔ q ^ 2 ≤ k) ∧
    (Fits r (q : ℚ) k (fun w => 0 < w.length) ↔ q ^ 2 ≤ k) := by
  dsimp only
  let q : ℕ := 2 ^ r
  let z : ℚ := (q : ℚ)
  have hq4 : 4 ≤ q := by
    have : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hr2
    simpa [q] using this
  have hq_ne0 : (q : ℚ) ≠ 0 := by positivity
  have hq2_ne0 : (q : ℚ) - 2 ≠ 0 := by
    have : (4 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq4
    linarith
  let E : Matrix (Option (Vec r)) (Vec r) ℚ := kerE r
  let P : Matrix (Vec r) (Option (Vec r)) ℚ := kerP r
  let M : Vec r → Matrix (Vec r) (Vec r) ℚ := kerM r
  have hcyc_M : ∀ w : List (Vec r), cycleVal z w = Matrix.trace (w.map M).prod :=
    ker_trace_zq r
  have hup : Fits r z (q ^ 2) (fun _ => True) := by
    rcases realizes_of_trace (card_vec r) M with ⟨u, v, M2, hM2⟩
    exact ⟨u, v, M2, fun w _ => (hM2 w trivial).trans (hcyc_M w).symm⟩
  have hspan : Submodule.span ℚ
      {X : Matrix (Vec r) (Vec r) ℚ | ∃ w : List (Vec r), 0 < w.length ∧ (w.map M).prod = X} = ⊤ := by
    let 𝒜 := Submodule.span ℚ
      {X : Matrix (Vec r) (Vec r) ℚ | ∃ w : List (Vec r), 0 < w.length ∧ (w.map M).prod = X}
    have hM_mem : ∀ h : Vec r, M h ∈ 𝒜 := fun h =>
      Submodule.subset_span ⟨[h], by simp, by simp⟩
    have h𝒜_mul : ∀ X ∈ 𝒜, ∀ Y ∈ 𝒜, X * Y ∈ 𝒜 := by
      intro X hX
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hX
      · rintro _ ⟨w1, hw1, rfl⟩ Y hY
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hY
        · rintro _ ⟨w2, hw2, rfl⟩
          exact Submodule.subset_span ⟨w1 ++ w2, by simp; omega, by simp⟩
        · simp
        · intro A B _ _ hA hB; rw [Matrix.mul_add]; exact Submodule.add_mem _ hA hB
        · intro c A _ hA; rw [Matrix.mul_smul]; exact Submodule.smul_mem _ c hA
      · intro Y _; simp
      · intro A B _ _ hA hB Y hY; rw [Matrix.add_mul]; exact Submodule.add_mem _ (hA Y hY) (hB Y hY)
      · intro c A _ hA Y hY; rw [Matrix.smul_mul]; exact Submodule.smul_mem _ c (hA Y hY)
    let wf : Vec r → ℚ := fun c => if c = 0 then 1 else -1
    let e0 : Vec r → ℚ := fun c => if c = 0 then 1 else 0
    have hAvg_mem : ((1 / (q : ℚ)) • ∑ h : Vec r, M h) ∈ 𝒜 :=
      Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun h _ => hM_mem h))
    have hM_col0 : ∀ (h c : Vec r), M h c 0 = if c = 0 then 1 else fVal z c := by
      intro h c
      change (P * TMat z h * E) c 0 = _
      rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_option]
      have hTE0 : ∀ s : Option (Vec r), (TMat z h * E) s 0 = s.elim 1 (fun a => fVal z a) := by
        intro s
        rw [Matrix.mul_apply, Fintype.sum_option]
        cases s <;> simp [TMat, E]
      simp_rw [hTE0]
      by_cases hc0 : c = 0
      · subst hc0; simp [P]
      · simp only [P, Option.elim_none, Option.elim_some, hc0, ↓reduceIte, zero_mul, zero_add]
        rw [Finset.sum_eq_single c]
        · simp
        · intro a _ ha; simp [ha]
        · intro h'; exact False.elim (h' (Finset.mem_univ _))
    have hM_row0 : ∀ (h c : Vec r), M h 0 c =
        if c = 0 then 1 else if h = c then 1 else if h = 0 then -1 else 0 := by
      intro h c
      change (P * TMat z h * E) 0 c = _
      rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_option]
      simp only [P, Option.elim_none, Option.elim_some, ↓reduceIte, one_mul, zero_mul,
        Finset.sum_const_zero, add_zero]
      rw [Matrix.mul_apply, Fintype.sum_option]
      simp only [TMat, Option.elim_none, Option.elim_some, one_mul]
      have hs : ∑ x : Vec r, (if x = h then (1 : ℚ) else 0) * E (some x) c = E (some h) c := by
        rw [Finset.sum_eq_single h]
        · simp
        · intro x _ hx; simp [hx]
        · intro h'; exact False.elim (h' (Finset.mem_univ _))
      rw [hs]
      by_cases hc0 : c = 0 <;> simp [E, hc0]
    have hAvg_eq : ((1 / (q : ℚ)) • ∑ h : Vec r, M h) = Matrix.vecMulVec wf e0 := by
      ext c1 c2
      simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Matrix.vecMulVec_apply, wf, e0]
      by_cases hc2 : c2 = 0
      · subst hc2
        simp only [↓reduceIte, mul_one]
        simp_rw [hM_col0]
        rw [Finset.sum_const, Finset.card_univ, card_vec, nsmul_eq_mul]
        by_cases hc1 : c1 = 0
        · simp only [hc1, ↓reduceIte, q]; field_simp [hq_ne0]
        · simp only [hc1, ↓reduceIte, fVal, q]; field_simp [hq_ne0]
      · simp only [hc2, ↓reduceIte, mul_zero]
        have hsum_zero : ∑ h : Vec r, M h c1 c2 = 0 := by
          have h1 : ∀ h : Vec r, M h c1 c2 =
              P c1 none * (TMat z h * E) none c2 + ∑ a : Vec r, P c1 (some a) * (TMat z h * E) (some a) c2 := by
            intro h
            change (P * TMat z h * E) c1 c2 = _
            rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_option]
          have hsum_TE : ∀ s : Option (Vec r), ∑ h : Vec r, (TMat z h * E) s c2 = 0 := by
            intro s
            have hE0 : E none c2 = 0 := by simp [E, hc2]
            have hsumE : ∑ b : Vec r, E (some b) c2 = 0 := by
              rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c2)]
              have h0m : (0 : Vec r) ∈ Finset.univ.erase c2 := Finset.mem_erase.mpr ⟨Ne.symm hc2, Finset.mem_univ 0⟩
              rw [← Finset.add_sum_erase _ _ h0m]
              have hr : ∑ b ∈ (Finset.univ.erase c2).erase 0, E (some b) c2 = 0 := by
                apply Finset.sum_eq_zero; intro b hb
                have hb0 := (Finset.mem_erase.mp hb).1
                have hbc := (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1
                simp [E, hc2, hbc, hb0]
              rw [hr, add_zero]
              have hEc : E (some c2) c2 = 1 := by simp [E, hc2]
              have hE0' : E (some 0) c2 = -1 := by simp [E, hc2, Ne.symm hc2]
              rw [hEc, hE0']; ring
            cases s with
            | none =>
              have hte : ∀ h : Vec r, (TMat z h * E) none c2 = E (some h) c2 := by
                intro h
                rw [Matrix.mul_apply, Fintype.sum_option]
                simp only [TMat, Option.elim_none, Option.elim_some, hE0, mul_zero, zero_add]
                rw [Finset.sum_eq_single h]
                · simp
                · intro b _ hb; simp [hb]
                · intro h'; exact False.elim (h' (Finset.mem_univ _))
              simp_rw [hte]; exact hsumE
            | some a =>
              have hte : ∀ h : Vec r, (TMat z h * E) (some a) c2 = E (some (a + h)) c2 := by
                intro h
                rw [Matrix.mul_apply, Fintype.sum_option]
                simp only [TMat, Option.elim_some, Option.elim_none, hE0, mul_zero, zero_add]
                rw [Finset.sum_eq_single (a + h)]
                · simp
                · intro b _ hb; simp [hb]
                · intro h'; exact False.elim (h' (Finset.mem_univ _))
              simp_rw [hte]
              have hsh : ∑ h : Vec r, E (some (a + h)) c2 = ∑ b : Vec r, E (some b) c2 :=
                Fintype.sum_equiv (Equiv.addLeft a) _ _ (fun _ => rfl)
              rw [hsh]; exact hsumE
          simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, hsum_TE, mul_zero, zero_add]
          rw [Finset.sum_comm]
          apply Finset.sum_eq_zero
          intro a _
          rw [← Finset.mul_sum, hsum_TE, mul_zero]
        rw [hsum_zero, mul_zero]
    have hAvg_vmv : Matrix.vecMulVec wf e0 ∈ 𝒜 := by rw [← hAvg_eq]; exact hAvg_mem
    have hvec_mul_M : ∀ (h : Vec r), (M h * Matrix.vecMulVec wf e0) = Matrix.vecMulVec ((M h).mulVec wf) e0 := by
      intro h
      ext c1 c2
      rw [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct]
      simp_rw [Matrix.vecMulVec_apply, ← mul_assoc, ← Finset.sum_mul]
    have hM_wf : ∀ (h c : Vec r), (M h).mulVec wf c =
        if c = 0 then (if h = 0 then (q : ℚ) else 0)
        else (if c = h then (q : ℚ) - 2 else -2) := by
      intro h c
      have hEw : E.mulVec wf = fun s => s.elim 1 (fun a => fVal z a) := by
        funext s
        rw [Matrix.mulVec, dotProduct]
        cases s with
        | none =>
          rw [Finset.sum_eq_single (0 : Vec r)]
          · simp [E, wf]
          · intro x _ hx; simp [E, hx]
          · intro h'; exact False.elim (h' (Finset.mem_univ _))
        | some a =>
          by_cases ha0 : a = 0
          · subst ha0
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Vec r))]
            have h0 : E (some 0) 0 * wf 0 = 0 := by simp [E]
            rw [h0, zero_add]
            have her : ∑ x ∈ Finset.univ.erase (0 : Vec r), E (some 0) x * wf x =
                ∑ _x ∈ Finset.univ.erase (0 : Vec r), (1 : ℚ) := by
              apply Finset.sum_congr rfl; intro x hx
              have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
              simp [E, wf, hx0, Ne.symm hx0]
            rw [her, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
              Finset.card_univ, card_vec, nsmul_eq_mul, mul_one]
            simp only [Option.elim_some, fVal, ↓reduceIte, z]
            have hpos : 1 ≤ q := by omega
            rw [Nat.cast_sub hpos]; push_cast; ring
          · rw [Finset.sum_eq_single a]
            · simp [E, wf, ha0, fVal]
            · intro x _ hxa
              by_cases hx0 : x = 0 <;> simp [E, hx0, Ne.symm hxa, ha0]
            · intro h'; exact False.elim (h' (Finset.mem_univ _))
      have hTEw : ∀ s : Option (Vec r), (TMat z h).mulVec (E.mulVec wf) s =
          s.elim (1 + fVal z h) (fun a => fVal z a + fVal z (a + h)) := by
        intro s
        rw [Matrix.mulVec, dotProduct, Fintype.sum_option, hEw]
        cases s with
        | none =>
          simp only [TMat, Option.elim_none, Option.elim_some, one_mul]
          congr 1
          rw [Finset.sum_eq_single h]
          · simp
          · intro b _ hb; simp [hb]
          · intro h'; exact False.elim (h' (Finset.mem_univ _))
        | some a =>
          simp only [TMat, Option.elim_some, Option.elim_none, mul_one]
          congr 1
          rw [Finset.sum_eq_single (a + h)]
          · simp
          · intro b _ hb; simp [hb]
          · intro h'; exact False.elim (h' (Finset.mem_univ _))
      have hMw : (M h).mulVec wf = P.mulVec ((TMat z h).mulVec (E.mulVec wf)) := by
        change (P * TMat z h * E).mulVec wf = _
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rw [hMw, Matrix.mulVec, dotProduct, Fintype.sum_option]
      simp_rw [hTEw]
      by_cases hc0 : c = 0
      · subst hc0
        simp only [P, Option.elim_none, Option.elim_some, ↓reduceIte, one_mul, zero_mul,
          Finset.sum_const_zero, add_zero]
        by_cases hh0 : h = 0 <;> simp [fVal, hh0, z]
      · simp only [P, Option.elim_none, Option.elim_some, hc0, ↓reduceIte, zero_mul, zero_add]
        rw [Finset.sum_eq_single c]
        · simp only [↓reduceIte, one_mul]
          by_cases hch : c = h
          · subst hch; simp [fVal, hc0, vec_add_self, z]; ring
          · have hne : c + h ≠ 0 := fun heq => hch ((vec_add_eq_zero_iff c h).mp heq)
            simp [fVal, hc0, hne, hch]; ring
        · intro a _ ha; simp [ha]
        · intro h'; exact False.elim (h' (Finset.mem_univ _))
    have hLeft_e0 : Matrix.vecMulVec e0 e0 ∈ 𝒜 := by
      have hM0_wf : Matrix.vecMulVec ((M 0).mulVec wf) e0 ∈ 𝒜 := by
        rw [← hvec_mul_M 0]; exact h𝒜_mul _ (hM_mem 0) _ hAvg_vmv
      have hcomb : ((1 / ((q : ℚ) - 2)) • (Matrix.vecMulVec ((M 0).mulVec wf) e0 - (2 : ℚ) • Matrix.vecMulVec wf e0)) =
          Matrix.vecMulVec e0 e0 := by
        ext c1 c2
        simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, smul_eq_mul,
          hM_wf 0 c1, wf, e0]
        by_cases hc1 : c1 = 0
        · subst hc1; simp only [↓reduceIte]; field_simp [hq2_ne0]
        · simp only [hc1, ↓reduceIte]; ring
      rw [← hcomb]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hM0_wf (Submodule.smul_mem _ _ hAvg_vmv))
    have hLeft_ec : ∀ c : Vec r, Matrix.vecMulVec (fun x => if x = c then (1 : ℚ) else 0) e0 ∈ 𝒜 := by
      intro c
      by_cases hc0 : c = 0
      · subst hc0; exact hLeft_e0
      · have hMc_wf : Matrix.vecMulVec ((M c).mulVec wf) e0 ∈ 𝒜 := by
          rw [← hvec_mul_M c]; exact h𝒜_mul _ (hM_mem c) _ hAvg_vmv
        have hcomb :
            ((1 / (q : ℚ)) • (Matrix.vecMulVec ((M c).mulVec wf) e0 - (2 : ℚ) • Matrix.vecMulVec wf e0 + (2 : ℚ) • Matrix.vecMulVec e0 e0)) =
            Matrix.vecMulVec (fun x => if x = c then (1 : ℚ) else 0) e0 := by
          ext c1 c2
          simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.vecMulVec_apply,
            smul_eq_mul, hM_wf c c1, wf, e0]
          by_cases hc10 : c1 = 0
          · subst hc10; simp only [hc0, Ne.symm hc0, ↓reduceIte]; ring
          · by_cases hc1c : c1 = c
            · subst hc1c; simp only [hc0, ↓reduceIte]; field_simp [hq_ne0]; ring
            · simp only [hc10, hc1c, ↓reduceIte]; ring
        rw [← hcomb]
        exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.sub_mem _ hMc_wf
          (Submodule.smul_mem _ _ hAvg_vmv)) (Submodule.smul_mem _ _ hLeft_e0))
    have hUnit : ∀ c1 c2 : Vec r,
        Matrix.vecMulVec (fun x => if x = c1 then (1 : ℚ) else 0)
          (fun y => if y = c2 then (1 : ℚ) else 0) ∈ 𝒜 := by
      intro c1 c2
      have hleft := hLeft_ec c1
      by_cases hc20 : c2 = 0
      · subst hc20; exact hleft
      · have hright : (Matrix.vecMulVec (fun x => if x = c1 then (1 : ℚ) else 0) e0 * M c2) -
            Matrix.vecMulVec (fun x => if x = c1 then (1 : ℚ) else 0) e0 =
            Matrix.vecMulVec (fun x => if x = c1 then (1 : ℚ) else 0)
              (fun y => if y = c2 then (1 : ℚ) else 0) := by
          ext a b
          simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.vecMulVec_apply, e0]
          have hs : ∑ x : Vec r, (if a = c1 then (1 : ℚ) else 0) * (if x = 0 then 1 else 0) * M c2 x b =
              (if a = c1 then (1 : ℚ) else 0) * M c2 0 b := by
            rw [Finset.sum_eq_single (0 : Vec r)]
            · simp
            · intro x _ hx; simp [hx]
            · intro h'; exact False.elim (h' (Finset.mem_univ _))
          rw [hs, hM_row0 c2 b]
          by_cases hb0 : b = 0
          · subst hb0; simp [hc20, Ne.symm hc20]
          · by_cases hbc : b = c2
            · subst hbc; simp [hb0]
            · simp [hb0, hbc, Ne.symm hbc, hc20]
        rw [← hright]
        exact Submodule.sub_mem _ (h𝒜_mul _ hleft _ (hM_mem c2)) hleft
    rw [eq_top_iff]
    intro X _
    have hdecomp : X = ∑ c1 : Vec r, ∑ c2 : Vec r,
        X c1 c2 • Matrix.vecMulVec (fun x => if x = c1 then (1 : ℚ) else 0)
          (fun y => if y = c2 then (1 : ℚ) else 0) := by
      ext a b
      simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
      rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single b]
        · simp
        · intro c2 _ hc2; simp [Ne.symm hc2]
        · intro h'; exact False.elim (h' (Finset.mem_univ _))
      · intro c1 _ hc1; simp [Ne.symm hc1]
      · intro h'; exact False.elim (h' (Finset.mem_univ _))
    rw [hdecomp]
    exact Submodule.sum_mem _ (fun c1 _ => Submodule.sum_mem _ (fun c2 _ =>
      Submodule.smul_mem _ _ (hUnit c1 c2)))
  let B : Matrix (Vec r) (Vec r) ℚ →ₗ[ℚ] Matrix (Vec r) (Vec r) ℚ →ₗ[ℚ] ℚ :=
    { toFun := fun X =>
        { toFun := fun Y => Matrix.trace (X * Y)
          map_add' := fun Y1 Y2 => by rw [Matrix.mul_add, Matrix.trace_add]
          map_smul' := fun s Y => by rw [Matrix.mul_smul, Matrix.trace_smul]; rfl }
      map_add' := fun X1 X2 => by ext Y; simp [Matrix.add_mul, Matrix.trace_add]
      map_smul' := fun s X => by ext Y; simp [Matrix.smul_mul, Matrix.trace_smul] }
  have hnondeg : ∀ Y : Matrix (Vec r) (Vec r) ℚ, (∀ X, B X Y = 0) → Y = 0 := by
    intro Y hY
    have h0 := hY Y.transpose
    change Matrix.trace (Y.transpose * Y) = 0 at h0
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply] at h0
    have hsq0 : ∀ a : Vec r, ∑ b : Vec r, Y b a * Y b a = 0 := fun a =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
        Finset.sum_nonneg (fun b _ => mul_self_nonneg (Y b x)))).mp h0 a (Finset.mem_univ a)
    ext b a
    have hba := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => mul_self_nonneg (Y x a))).mp (hsq0 a) b (Finset.mem_univ b)
    exact mul_self_eq_zero.mp hba
  have hfin : Module.finrank ℚ (Matrix (Vec r) (Vec r) ℚ) = q ^ 2 := by
    rw [Module.finrank_matrix, card_vec, Module.finrank_self, mul_one, sq]
  have hlb : Fits r z k (fun w => 0 < w.length) → q ^ 2 ≤ k := by
    intro hfit
    rw [← hfin]
    exact lower_bound_of_nondeg_pairing (fun w => (w.map M).prod) B hnondeg
      (fun w1 w2 _ _ => by rw [hcyc_M, List.map_append, List.prod_append]; rfl) hspan hfit
  have hweak : Fits r z k (fun _ => True) → Fits r z k (fun w => 0 < w.length) := by
    rintro ⟨u, v, M2, hM2⟩; exact ⟨u, v, M2, fun w _ => hM2 w trivial⟩
  exact ⟨⟨fun h => hlb (hweak h), fun hk => realizes_mono hk hup⟩,
    ⟨hlb, fun hk => hweak (realizes_mono hk hup)⟩⟩

def z2Corr (r : ℕ) (a : Vec r) : ℚ :=
  fVal (r := r) 2 a - (if a = 0 then ((2 ^ r : ℕ) : ℚ) else 0)

def z2Pairing (r : ℕ) :
    (Matrix (Vec r) (Vec r) ℚ × (Vec r → ℚ)) →ₗ[ℚ]
    (Matrix (Vec r) (Vec r) ℚ × (Vec r → ℚ)) →ₗ[ℚ] ℚ :=
  { toFun := fun p1 =>
      { toFun := fun p2 =>
          Matrix.trace (p1.1 * p2.1) + ∑ a : Vec r, ∑ b : Vec r, p1.2 a * z2Corr r (a + b) * p2.2 b
        map_add' := fun p2 p3 => by
          simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Matrix.mul_add, Matrix.trace_add,
            mul_add, Finset.sum_add_distrib]
          ring
        map_smul' := fun s p2 => by
          change Matrix.trace (p1.1 * (s • p2.1)) +
              ∑ a : Vec r, ∑ b : Vec r, p1.2 a * z2Corr r (a + b) * (s * p2.2 b) =
              s * (Matrix.trace (p1.1 * p2.1) +
                ∑ a : Vec r, ∑ b : Vec r, p1.2 a * z2Corr r (a + b) * p2.2 b)
          rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_add]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro b _; ring }
    map_add' := fun p1 p2 => by
      apply LinearMap.ext
      intro p3
      change Matrix.trace ((p1.1 + p2.1) * p3.1) +
          ∑ a : Vec r, ∑ b : Vec r, (p1.2 a + p2.2 a) * z2Corr r (a + b) * p3.2 b =
        (Matrix.trace (p1.1 * p3.1) + ∑ a : Vec r, ∑ b : Vec r, p1.2 a * z2Corr r (a + b) * p3.2 b) +
        (Matrix.trace (p2.1 * p3.1) + ∑ a : Vec r, ∑ b : Vec r, p2.2 a * z2Corr r (a + b) * p3.2 b)
      simp only [Matrix.add_mul, Matrix.trace_add, add_mul, Finset.sum_add_distrib]
      ring
    map_smul' := fun s p1 => by
      apply LinearMap.ext
      intro p3
      change Matrix.trace ((s • p1.1) * p3.1) +
          ∑ a : Vec r, ∑ b : Vec r, (s * p1.2 a) * z2Corr r (a + b) * p3.2 b =
        s * (Matrix.trace (p1.1 * p3.1) +
          ∑ a : Vec r, ∑ b : Vec r, p1.2 a * z2Corr r (a + b) * p3.2 b)
      rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, mul_add]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro b _; ring }

lemma z2Pairing_nondeg (r : ℕ) (hr2 : 2 ≤ r) :
    ∀ p2 : Matrix (Vec r) (Vec r) ℚ × (Vec r → ℚ),
      (∀ p1, z2Pairing r p1 p2 = 0) → p2 = 0 := by
  have hq4 : 4 ≤ 2 ^ r := by
    have : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hr2
    omega
  have h2q_ne0 : (2 : ℚ) - ((2 ^ r : ℕ) : ℚ) ≠ 0 := by
    have : (4 : ℚ) ≤ ((2 ^ r : ℕ) : ℚ) := by exact_mod_cast hq4
    linarith
  have h22q_ne0 : (2 : ℚ) - 2 * ((2 ^ r : ℕ) : ℚ) ≠ 0 := by
    have : (4 : ℚ) ≤ ((2 ^ r : ℕ) : ℚ) := by exact_mod_cast hq4
    linarith
  rintro ⟨Y, y⟩ hY
  have hY0 : Y = 0 := by
    have h0 := hY (Y.transpose, 0)
    change Matrix.trace (Y.transpose * Y) +
        ∑ a : Vec r, ∑ b : Vec r, (0 : ℚ) * z2Corr r (a + b) * y b = 0 at h0
    simp only [zero_mul, Finset.sum_const_zero, add_zero] at h0
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply] at h0
    have hsq0 : ∀ a : Vec r, ∑ b : Vec r, Y b a * Y b a = 0 := fun a =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
        Finset.sum_nonneg (fun b _ => mul_self_nonneg (Y b x)))).mp h0 a (Finset.mem_univ a)
    ext b a
    have hba := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => mul_self_nonneg (Y x a))).mp (hsq0 a) b (Finset.mem_univ b)
    exact mul_self_eq_zero.mp hba
  have hy0 : y = 0 := by
    have hrow : ∀ a : Vec r, ((2 : ℚ) - ((2 ^ r : ℕ) : ℚ)) * y a - (∑ b : Vec r, y b) = 0 := by
      intro a
      have h0 := hY (0, fun x => if x = a then 1 else 0)
      change Matrix.trace ((0 : Matrix (Vec r) (Vec r) ℚ) * Y) +
        ∑ x : Vec r, ∑ b : Vec r, (if x = a then (1 : ℚ) else 0) * z2Corr r (x + b) * y b = 0 at h0
      simp only [Matrix.zero_mul, Matrix.trace_zero, zero_add] at h0
      rw [Finset.sum_eq_single a] at h0
      · simp only [↓reduceIte, one_mul] at h0
        have hcb : ∀ b : Vec r, z2Corr r (a + b) = (if a = b then (2 : ℚ) - ((2 ^ r : ℕ) : ℚ) else 0) - 1 := by
          intro b
          simp only [z2Corr, fVal, vec_add_eq_zero_iff]
          by_cases hab : a = b <;> simp [hab] <;> ring
        simp_rw [hcb, sub_mul, Finset.sum_sub_distrib, one_mul] at h0
        have hs : ∑ b : Vec r, (if a = b then (2 : ℚ) - ((2 ^ r : ℕ) : ℚ) else 0) * y b =
            ((2 : ℚ) - ((2 ^ r : ℕ) : ℚ)) * y a := by
          rw [Finset.sum_eq_single a]
          · simp
          · intro b _ hb; simp [Ne.symm hb]
          · intro h'; exact False.elim (h' (Finset.mem_univ _))
        rw [hs] at h0
        exact h0
      · intro x _ hx; simp [hx]
      · intro h'; exact False.elim (h' (Finset.mem_univ _))
    have hS0 : ∑ b : Vec r, y b = 0 := by
      have hsum : ∑ a : Vec r, (((2 : ℚ) - ((2 ^ r : ℕ) : ℚ)) * y a - (∑ b : Vec r, y b)) = 0 :=
        Finset.sum_eq_zero (fun a _ => hrow a)
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        card_vec, nsmul_eq_mul] at hsum
      have hfac : ((2 : ℚ) - 2 * ((2 ^ r : ℕ) : ℚ)) * (∑ b : Vec r, y b) = 0 := by
        linarith
      exact (mul_eq_zero.mp hfac).resolve_left h22q_ne0
    funext a
    have ha := hrow a
    rw [hS0, sub_zero] at ha
    exact (mul_eq_zero.mp ha).resolve_left h2q_ne0
  exact Prod.ext hY0 hy0

lemma solve_z2_ge4 (r : ℕ) (hr2 : 2 ≤ r) (k : ℕ) :
    let q : ℕ := 2 ^ r
    (Fits r 2 k (fun _ => True) ↔ q ^ 2 + q + 1 ≤ k) ∧
    (Fits r 2 k (fun w => 0 < w.length) ↔ q ^ 2 + q ≤ k) := by
  dsimp only
  let q : ℕ := 2 ^ r
  have hq4 : 4 ≤ q := by
    have : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hr2
    simpa [q] using this
  have hq_ne0 : (q : ℚ) ≠ 0 := by positivity
  have h2q_ne0 : (2 : ℚ) - (q : ℚ) ≠ 0 := by
    have : (4 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq4
    linarith
  have h22q_ne0 : (2 : ℚ) - 2 * (q : ℚ) ≠ 0 := by
    have : (4 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq4
    linarith
  let E : Matrix (Option (Vec r)) (Vec r) ℚ := fun s b =>
    s.elim (if b = 0 then 1 else 0) (fun a => if a = b then 1 else 0)
  let R : Vec r → Matrix (Vec r) (Option (Vec r)) ℚ := fun h a s => TMat (r := r) 2 h (some a) s
  let S : Vec r → Matrix (Vec r) (Vec r) ℚ := fun h a b =>
    fVal (r := r) 2 a * (if b = 0 then 1 else 0) + (if b = a + h then 1 else 0)
  have hT_fac : ∀ h : Vec r, TMat (r := r) 2 h = E * R h := by
    intro h
    ext s t
    rw [Matrix.mul_apply]
    cases s with
    | none =>
      rw [Finset.sum_eq_single (0 : Vec r)]
      · cases t <;> simp [E, R, TMat, fVal] <;> norm_num
      · intro b _ hb; simp [E, hb]
      · intro h'; exact False.elim (h' (Finset.mem_univ _))
    | some a =>
      rw [Finset.sum_eq_single a]
      · simp [E, R]
      · intro b _ hb; simp [E, Ne.symm hb]
      · intro h'; exact False.elim (h' (Finset.mem_univ _))
  have hRE : ∀ h : Vec r, R h * E = S h := by
    intro h
    ext a b
    rw [Matrix.mul_apply, Fintype.sum_option]
    simp only [R, E, TMat, Option.elim_some, Option.elim_none, S]
    congr 1
    rw [Finset.sum_eq_single (a + h)]
    · by_cases hb : b = a + h <;> simp [hb, eq_comm]
    · intro x _ hx; simp [hx]
    · intro h'; exact False.elim (h' (Finset.mem_univ _))
  have hprod_S : ∀ w : List (Vec r), 0 < w.length →
      Matrix.trace (w.map (TMat (r := r) 2)).prod = Matrix.trace (w.map S).prod := by
    intro w hw
    have haux : ∀ (h0 : Vec r) (ws : List (Vec r)),
        ((h0 :: ws).map (TMat (r := r) 2)).prod =
        E * (((ws.map (fun h => S h)).prod) * R h0) ∨ True := fun _ _ => Or.inr trivial
    have hchain : ∀ (ws : List (Vec r)) (h0 : Vec r),
        (ws.map (TMat (r := r) 2)).prod * E = E * (ws.map S).prod := by
      intro ws
      induction ws with
      | nil => intro _; simp
      | cons h tl ih =>
        intro h0
        simp only [List.map_cons, List.prod_cons]
        calc TMat 2 h * (tl.map (TMat 2)).prod * E
            = TMat 2 h * ((tl.map (TMat 2)).prod * E) := Matrix.mul_assoc _ _ _
          _ = (E * R h) * (E * (tl.map S).prod) := by rw [ih h0, hT_fac h]
          _ = E * ((R h * E) * (tl.map S).prod) := by simp [Matrix.mul_assoc]
          _ = E * (S h * (tl.map S).prod) := by rw [hRE h]
    cases w with
    | nil => simp at hw
    | cons h ws =>
      simp only [List.map_cons, List.prod_cons]
      rw [hT_fac h, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hchain ws h,
        ← Matrix.mul_assoc, hRE h, Matrix.trace_mul_comm]
  let corr : Vec r → ℚ := z2Corr r
  have hcyc_pos : ∀ w : List (Vec r), 0 < w.length →
      cycleVal (r := r) 2 w = Matrix.trace (w.map S).prod + corr w.sum := by
    intro w hw
    unfold cycleVal
    rw [hprod_S w hw]
    simp only [corr, z2Corr]
    ring
  let Reg : Vec r → Matrix (Vec r) (Vec r) ℚ := fun h a b => if b = a + h then 1 else 0
  have hReg_apply : ∀ h a b : Vec r, Reg h a b = if b = a + h then 1 else 0 := fun _ _ _ => rfl
  have hReg_prod : ∀ (w : List (Vec r)) (a b : Vec r),
      (w.map Reg).prod a b = if b = a + w.sum then 1 else 0 := by
    intro w
    induction w with
    | nil =>
      intro a b
      simp [Matrix.one_apply, eq_comm]
    | cons h ws ih =>
      intro a b
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [Matrix.mul_apply]
      simp_rw [hReg_apply, ih]
      rw [Finset.sum_eq_single (a + h)]
      · simp only [↓reduceIte, one_mul, add_assoc]
        rfl
      · intro x _ hx; simp [hx]
      · intro h'; exact False.elim (h' (Finset.mem_univ _))
  have hreal_corr : Realizes (fun w : List (Vec r) => corr w.sum) q (fun _ => True) := by
    let e : Fin q ≃ Vec r := (Fintype.equivFinOfCardEq (card_vec r)).symm
    apply realizes_of_equiv e (fun a => if a = 0 then 1 else 0) corr Reg
    intro w _
    rw [Finset.sum_eq_single (0 : Vec r)]
    · rw [Finset.sum_eq_single w.sum]
      · simp [hReg_prod w 0 w.sum]
      · intro b _ hb; simp [hReg_prod w 0 b, hb]
      · intro h'; exact False.elim (h' (Finset.mem_univ _))
    · intro a _ ha; simp [ha]
    · intro h'; exact False.elim (h' (Finset.mem_univ _))
  have hup_pos : Fits r 2 (q ^ 2 + q) (fun w => 0 < w.length) := by
    have h1 := realizes_of_trace (card_vec r) S
    have h1' : Realizes (fun w => Matrix.trace (w.map S).prod) (q ^ 2) (fun w => 0 < w.length) := by
      rcases h1 with ⟨u, v, M, hM⟩; exact ⟨u, v, M, fun w _ => hM w trivial⟩
    have h2' : Realizes (fun w => corr w.sum) q (fun w => 0 < w.length) := by
      rcases hreal_corr with ⟨u, v, M, hM⟩; exact ⟨u, v, M, fun w _ => hM w trivial⟩
    rcases realizes_of_sum h1' h2' with ⟨u, v, M, hM⟩
    exact ⟨u, v, M, fun w hw => (hM w hw).trans (hcyc_pos w hw).symm⟩
  have hup_all : Fits r 2 (q ^ 2 + q + 1) (fun _ => True) := fits_all_of_fits_pos 2 hup_pos
  let V := Matrix (Vec r) (Vec r) ℚ × (Vec r → ℚ)
  let conv : (Vec r → ℚ) → (Vec r → ℚ) → (Vec r → ℚ) :=
    fun y1 y2 c => ∑ a : Vec r, y1 a * y2 (a + c)
  let delta : Vec r → (Vec r → ℚ) := fun a x => if x = a then 1 else 0
  have hconv_delta : ∀ a b : Vec r, conv (delta a) (delta b) = delta (a + b) := by
    intro a b
    funext c
    simp only [conv, delta]
    rw [Finset.sum_eq_single a]
    · by_cases hcb : c = a + b
      · subst hcb
        have h1 : a + (a + b) = b := by rw [← add_assoc, vec_add_self, zero_add]
        simp [h1]
      · have h1 : a + c ≠ b := by
          intro heq
          apply hcb
          have := congrArg (a + ·) heq
          rw [← add_assoc, vec_add_self, zero_add] at this
          exact this
        simp [hcb, h1]
    · intro x _ hx; simp [hx]
    · intro h'; exact False.elim (h' (Finset.mem_univ _))
  let φ : List (Vec r) → V := fun w => ((w.map S).prod, delta w.sum)
  let 𝒦 : Submodule ℚ V :=
    Submodule.span ℚ {v : V | ∃ w : List (Vec r), 0 < w.length ∧ φ w = v}
  have hS_mem : ∀ h : Vec r, (S h, delta h) ∈ 𝒦 := fun h =>
    Submodule.subset_span ⟨[h], by simp, by simp [φ]⟩
  have h𝒦_mul : ∀ p ∈ 𝒦, ∀ p' ∈ 𝒦, (p.1 * p'.1, conv p.2 p'.2) ∈ 𝒦 := by
    intro p hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨w1, hw1, rfl⟩ p' hp'
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hp'
      · rintro _ ⟨w2, hw2, rfl⟩
        refine Submodule.subset_span ⟨w1 ++ w2, by simp; omega, ?_⟩
        simp [φ, hconv_delta]
      · simp only [φ, Prod.fst_zero, Prod.snd_zero]
        have h0 : ((w1.map S).prod * 0, conv (delta w1.sum) 0) = (0 : V) := by
          ext a b
          · simp
          · simp [conv]
        rw [h0]; exact Submodule.zero_mem _
      · rintro ⟨A1, A2⟩ ⟨B1, B2⟩ _ _ hA hB
        change ((w1.map S).prod * (A1 + B1), conv (delta w1.sum) (A2 + B2)) ∈ 𝒦
        have hadd : ((w1.map S).prod * (A1 + B1), conv (delta w1.sum) (A2 + B2)) =
            ((w1.map S).prod * A1, conv (delta w1.sum) A2) +
            ((w1.map S).prod * B1, conv (delta w1.sum) B2) := by
          ext a b
          · simp [Matrix.mul_add]
          · simp [conv, mul_add, Finset.sum_add_distrib]
        rw [hadd]; exact Submodule.add_mem _ hA hB
      · rintro s ⟨A1, A2⟩ _ hA
        change ((w1.map S).prod * (s • A1), conv (delta w1.sum) (s • A2)) ∈ 𝒦
        have hsm : ((w1.map S).prod * (s • A1), conv (delta w1.sum) (s • A2)) =
            s • ((w1.map S).prod * A1, conv (delta w1.sum) A2) := by
          ext a b
          · simp
          · simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, conv, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro x _; ring
        rw [hsm]; exact Submodule.smul_mem _ s hA
    · intro p' _
      change ((0 : Matrix (Vec r) (Vec r) ℚ) * p'.1, conv 0 p'.2) ∈ 𝒦
      have h0 : ((0 : Matrix (Vec r) (Vec r) ℚ) * p'.1, conv 0 p'.2) = (0 : V) := by
        ext a b
        · simp
        · simp [conv]
      rw [h0]; exact Submodule.zero_mem _
    · rintro ⟨A1, A2⟩ ⟨B1, B2⟩ _ _ hA hB p' hp'
      change ((A1 + B1) * p'.1, conv (A2 + B2) p'.2) ∈ 𝒦
      have hadd : ((A1 + B1) * p'.1, conv (A2 + B2) p'.2) =
          (A1 * p'.1, conv A2 p'.2) + (B1 * p'.1, conv B2 p'.2) := by
        ext a b
        · simp [Matrix.add_mul]
        · simp [conv, add_mul, Finset.sum_add_distrib]
      rw [hadd]; exact Submodule.add_mem _ (hA p' hp') (hB p' hp')
    · rintro s ⟨A1, A2⟩ _ hA p' hp'
      change ((s • A1) * p'.1, conv (s • A2) p'.2) ∈ 𝒦
      have hsm : ((s • A1) * p'.1, conv (s • A2) p'.2) =
          s • (A1 * p'.1, conv A2 p'.2) := by
        ext a b
        · simp
        · simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, conv, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro x _; ring
      rw [hsm]; exact Submodule.smul_mem _ s (hA p' hp')
  have h𝒦_top : 𝒦 = ⊤ := by
    let U : V := ((1 / (q : ℚ)) • ∑ h : Vec r, (S h, delta h))
    have hU_mem : U ∈ 𝒦 := Submodule.smul_mem _ _ (Submodule.sum_mem _ (fun h _ => hS_mem h))
    have hU2 : U.2 = fun _ => 1 / (q : ℚ) := by
      funext c
      simp only [U, Prod.smul_snd, Prod.snd_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, delta]
      rw [Finset.sum_eq_single c]
      · simp
      · intro h _ hh; simp [Ne.symm hh]
      · intro h'; exact False.elim (h' (Finset.mem_univ _))
    have hS_apply : ∀ h a b : Vec r,
        S h a b = fVal (r := r) 2 a * (if b = 0 then 1 else 0) + (if b = a + h then 1 else 0) :=
      fun _ _ _ => rfl
    have hU1 : ∀ a b : Vec r, U.1 a b = fVal (r := r) 2 a * (if b = 0 then 1 else 0) + 1 / (q : ℚ) := by
      intro a b
      simp only [U, Prod.smul_fst, Prod.fst_sum, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
      simp_rw [hS_apply, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, card_vec,
        nsmul_eq_mul]
      have hs : ∑ h : Vec r, (if b = a + h then (1 : ℚ) else 0) = 1 := by
        rw [Finset.sum_eq_single (a + b)]
        · have h1 : a + (a + b) = b := by rw [← add_assoc, vec_add_self, zero_add]
          simp [h1]
        · intro h _ hh
          have hne : b ≠ a + h := by
            intro heq
            apply hh
            have := congrArg (a + ·) heq
            rw [← add_assoc, vec_add_self, zero_add] at this
            exact this.symm
          simp [hne]
        · intro h'; exact False.elim (h' (Finset.mem_univ _))
      rw [hs]
      simp only [q]
      field_simp [hq_ne0]
    have hdiff_0 : ∀ h : Vec r,
        (Matrix.vecMulVec (fun a => (if a = h then 1 else 0) - (if a = 0 then 1 else 0)) (delta 0), 0) ∈ 𝒦 := by
      intro h
      have hD : (S h, delta h) - (S 0, delta 0) ∈ 𝒦 := Submodule.sub_mem _ (hS_mem h) (hS_mem 0)
      have hP := h𝒦_mul _ hD _ hU_mem
      have heq : (((S h, delta h) - (S 0, delta 0)).1 * U.1, conv ((S h, delta h) - (S 0, delta 0)).2 U.2) =
          (2 : ℚ) • (Matrix.vecMulVec (fun a => (if a = h then 1 else 0) - (if a = 0 then 1 else 0)) (delta 0), 0) := by
        ext a b
        · simp only [Prod.fst_sub, Matrix.mul_apply, Matrix.sub_apply, hU1, Prod.smul_fst,
            Matrix.smul_apply, Matrix.vecMulVec_apply, delta, smul_eq_mul]
          have hSdiff : ∀ x : Vec r, S h a x - S 0 a x =
              (if x = a + h then 1 else 0) - (if x = a then 1 else 0) := by
            intro x; simp [S]
          simp_rw [hSdiff, sub_mul, Finset.sum_sub_distrib]
          have hs1 : ∑ x : Vec r, (if x = a + h then (1 : ℚ) else 0) * (fVal 2 x * (if b = 0 then 1 else 0) + 1 / (q : ℚ)) =
              fVal 2 (a + h) * (if b = 0 then 1 else 0) + 1 / (q : ℚ) := by
            rw [Finset.sum_eq_single (a + h)]
            · simp
            · intro x _ hx; simp [hx]
            · intro h'; exact False.elim (h' (Finset.mem_univ _))
          have hs2 : ∑ x : Vec r, (if x = a then (1 : ℚ) else 0) * (fVal 2 x * (if b = 0 then 1 else 0) + 1 / (q : ℚ)) =
              fVal 2 a * (if b = 0 then 1 else 0) + 1 / (q : ℚ) := by
            rw [Finset.sum_eq_single a]
            · simp
            · intro x _ hx; simp [hx]
            · intro h'; exact False.elim (h' (Finset.mem_univ _))
          rw [hs1, hs2]
          have hfah : fVal (r := r) 2 (a + h) = 2 * (if a = h then 1 else 0) - 1 := by
            simp only [fVal, vec_add_eq_zero_iff]; by_cases hah : a = h <;> simp [hah] <;> ring
          have hfa : fVal (r := r) 2 a = 2 * (if a = 0 then 1 else 0) - 1 := by
            simp only [fVal]; by_cases ha0 : a = 0 <;> simp [ha0] <;> ring
          rw [hfah, hfa]
          ring
        · simp only [Prod.snd_sub, conv, hU2, Pi.sub_apply, delta, Prod.smul_snd, Pi.smul_apply,
            Pi.zero_apply, smul_eq_mul, mul_zero, sub_mul, Finset.sum_sub_distrib]
          have hs1 : ∑ x : Vec r, (if x = h then (1 : ℚ) else 0) * (1 / (q : ℚ)) = 1 / (q : ℚ) := by
            rw [Finset.sum_eq_single h]
            · simp
            · intro x _ hx; simp [hx]
            · intro h'; exact False.elim (h' (Finset.mem_univ _))
          have hs2 : ∑ x : Vec r, (if x = 0 then (1 : ℚ) else 0) * (1 / (q : ℚ)) = 1 / (q : ℚ) := by
            rw [Finset.sum_eq_single (0 : Vec r)]
            · simp
            · intro x _ hx; simp [hx]
            · intro h'; exact False.elim (h' (Finset.mem_univ _))
          rw [hs1, hs2, sub_self]
      rw [heq] at hP
      have hhalf := Submodule.smul_mem 𝒦 (1 / 2 : ℚ) hP
      rw [smul_smul] at hhalf
      have h12 : (1 / 2 : ℚ) * 2 = 1 := by norm_num
      rwa [h12, one_smul] at hhalf
    have hF_mem : (Matrix.vecMulVec (fVal (r := r) 2) (delta 0), 0) ∈ 𝒦 := by
      have hex_h : ∃ h : Vec r, h ≠ 0 := by
        have hlt : 1 < Fintype.card (Vec r) := by rw [card_vec]; omega
        obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hlt
        by_cases ha0 : a = 0
        · exact ⟨b, fun hb0 => hab (ha0.trans hb0.symm)⟩
        · exact ⟨a, ha0⟩
      obtain ⟨h, hh0⟩ := hex_h
      have h1 := hdiff_0 h
      have h2 := h𝒦_mul _ (hS_mem 0) _ h1
      have hprod_eq :
          (S 0 * Matrix.vecMulVec (fun a => (if a = h then 1 else 0) - (if a = 0 then 1 else 0)) (delta 0),
            conv (delta 0) 0) =
          (Matrix.vecMulVec (fun a => (if a = h then 1 else 0) - (if a = 0 then 1 else 0)) (delta 0), (0 : Vec r → ℚ)) -
          (Matrix.vecMulVec (fVal (r := r) 2) (delta 0), (0 : Vec r → ℚ)) := by
        ext a b
        · simp only [Prod.fst_sub, Matrix.sub_apply]
          rw [Matrix.mul_apply]
          simp only [hS_apply, Matrix.vecMulVec_apply, delta, add_zero]
          simp_rw [add_mul, Finset.sum_add_distrib]
          have hs1 : ∑ x : Vec r, fVal 2 a * (if x = 0 then (1 : ℚ) else 0) *
              (((if x = h then 1 else 0) - (if x = 0 then 1 else 0)) * (if b = 0 then 1 else 0)) =
              - (fVal 2 a * (if b = 0 then 1 else 0)) := by
            rw [Finset.sum_eq_single (0 : Vec r)]
            · by_cases hb0 : b = 0 <;> simp [hb0, Ne.symm hh0]
            · intro x _ hx; simp [hx]
            · intro h'; exact False.elim (h' (Finset.mem_univ _))
          have hs2 : ∑ x : Vec r, (if x = a then (1 : ℚ) else 0) *
              (((if x = h then 1 else 0) - (if x = 0 then 1 else 0)) * (if b = 0 then 1 else 0)) =
              ((if a = h then 1 else 0) - (if a = 0 then 1 else 0)) * (if b = 0 then 1 else 0) := by
            rw [Finset.sum_eq_single a]
            · simp
            · intro x _ hx; simp [hx]
            · intro h'; exact False.elim (h' (Finset.mem_univ _))
          rw [hs1, hs2]; ring
        · simp [conv]
      rw [hprod_eq] at h2
      have hsub := Submodule.sub_mem 𝒦 h1 h2
      have hsub_eq :
          (Matrix.vecMulVec (fun a => (if a = h then 1 else 0) - (if a = 0 then 1 else 0)) (delta 0), (0 : Vec r → ℚ)) -
          ((Matrix.vecMulVec (fun a => (if a = h then 1 else 0) - (if a = 0 then 1 else 0)) (delta 0), (0 : Vec r → ℚ)) -
           (Matrix.vecMulVec (fVal (r := r) 2) (delta 0), (0 : Vec r → ℚ))) =
          (Matrix.vecMulVec (fVal (r := r) 2) (delta 0), (0 : Vec r → ℚ)) := by abel
      rwa [hsub_eq] at hsub
    have he0_mem : (Matrix.vecMulVec (delta 0) (delta 0), 0) ∈ 𝒦 := by
      have hsum_diff : (Matrix.vecMulVec (fVal (r := r) 2) (delta 0), (0 : Vec r → ℚ)) +
          ∑ h : Vec r, (Matrix.vecMulVec (fun a => (if a = h then 1 else 0) - (if a = 0 then 1 else 0)) (delta 0), (0 : Vec r → ℚ)) ∈ 𝒦 :=
        Submodule.add_mem _ hF_mem (Submodule.sum_mem _ (fun h _ => hdiff_0 h))
      have heq : (Matrix.vecMulVec (fVal (r := r) 2) (delta 0), (0 : Vec r → ℚ)) +
          ∑ h : Vec r, (Matrix.vecMulVec (fun a => (if a = h then 1 else 0) - (if a = 0 then 1 else 0)) (delta 0), (0 : Vec r → ℚ)) =
          ((2 : ℚ) - (q : ℚ)) • (Matrix.vecMulVec (delta 0) (delta 0), (0 : Vec r → ℚ)) := by
        ext a b
        · simp only [Prod.fst_add, Prod.fst_sum, Matrix.add_apply, Matrix.sum_apply,
            Matrix.vecMulVec_apply, Prod.smul_fst, Matrix.smul_apply, smul_eq_mul, delta]
          simp_rw [sub_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, card_vec,
            nsmul_eq_mul]
          have hs1 : ∑ h : Vec r, (if a = h then (1 : ℚ) else 0) * (if b = 0 then 1 else 0) =
              if b = 0 then 1 else 0 := by
            rw [Finset.sum_eq_single a]
            · simp
            · intro h _ hh; simp [Ne.symm hh]
            · intro h'; exact False.elim (h' (Finset.mem_univ _))
          rw [hs1]
          by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0 <;> simp [fVal, ha0, hb0, q] <;> ring
        · simp [Prod.snd_sum]
      rw [heq] at hsum_diff
      have hsc := Submodule.smul_mem 𝒦 (1 / ((2 : ℚ) - (q : ℚ))) hsum_diff
      have h1 : (1 / ((2 : ℚ) - (q : ℚ))) * ((2 : ℚ) - (q : ℚ)) = 1 := one_div_mul_cancel h2q_ne0
      rw [smul_smul, h1, one_smul] at hsc
      exact hsc
    have hleft_any : ∀ a : Vec r, (Matrix.vecMulVec (delta a) (delta 0), 0) ∈ 𝒦 := by
      intro a
      have hadd := Submodule.add_mem 𝒦 (hdiff_0 a) he0_mem
      have heq : (Matrix.vecMulVec (fun x => (if x = a then 1 else 0) - (if x = 0 then 1 else 0)) (delta 0), (0 : Vec r → ℚ)) +
          (Matrix.vecMulVec (delta 0) (delta 0), (0 : Vec r → ℚ)) = (Matrix.vecMulVec (delta a) (delta 0), (0 : Vec r → ℚ)) := by
        ext x y
        · by_cases hy : y = 0 <;> simp [Matrix.vecMulVec_apply, delta, hy]
        · simp
      convert hadd using 1
      exact heq.symm
    have hunit : ∀ a b : Vec r, (Matrix.vecMulVec (delta a) (delta b), 0) ∈ 𝒦 := by
      intro a b
      have hl := hleft_any a
      have hm := h𝒦_mul _ hl _ (hS_mem b)
      have hsub := Submodule.sub_mem 𝒦 hm hl
      have heq : (Matrix.vecMulVec (delta a) (delta 0) * S b, conv 0 (delta b)) -
          (Matrix.vecMulVec (delta a) (delta 0), (0 : Vec r → ℚ)) =
          (Matrix.vecMulVec (delta a) (delta b), (0 : Vec r → ℚ)) := by
        ext x y
        · simp only [Prod.fst_sub, Matrix.sub_apply, Matrix.mul_apply, Matrix.vecMulVec_apply, delta]
          rw [Finset.sum_eq_single (0 : Vec r)]
          · simp only [↓reduceIte, mul_one, hS_apply, fVal, zero_add]
            ring
          · intro c _ hc; simp [hc]
          · intro h'; exact False.elim (h' (Finset.mem_univ _))
        · simp [conv]
      rwa [heq] at hsub
    have hmat_all : ∀ X : Matrix (Vec r) (Vec r) ℚ, (X, 0) ∈ 𝒦 := by
      intro X
      have hdec : (X, (0 : Vec r → ℚ)) = ∑ a : Vec r, ∑ b : Vec r,
          X a b • (Matrix.vecMulVec (delta a) (delta b), (0 : Vec r → ℚ)) := by
        ext x y
        · simp only [Prod.fst_sum, Matrix.sum_apply, Prod.smul_fst, Matrix.smul_apply,
            Matrix.vecMulVec_apply, delta, smul_eq_mul]
          rw [Finset.sum_eq_single x]
          · rw [Finset.sum_eq_single y]
            · simp
            · intro b _ hb; simp [Ne.symm hb]
            · intro h'; exact False.elim (h' (Finset.mem_univ _))
          · intro a _ ha; simp [Ne.symm ha]
          · intro h'; exact False.elim (h' (Finset.mem_univ _))
        · simp [Prod.snd_sum]
      rw [hdec]
      exact Submodule.sum_mem _ (fun a _ => Submodule.sum_mem _ (fun b _ =>
        Submodule.smul_mem _ _ (hunit a b)))
    have hvec_all : ∀ y : Vec r → ℚ, (0, y) ∈ 𝒦 := by
      intro y
      have hdelta_mem : ∀ h : Vec r, (0, delta h) ∈ 𝒦 := by
        intro h
        have hsub := Submodule.sub_mem 𝒦 (hS_mem h) (hmat_all (S h))
        have h0 : (S h, delta h) - (S h, (0 : Vec r → ℚ)) = (0, delta h) := by
          ext <;> simp
        rwa [h0] at hsub
      have hdec : ((0 : Matrix (Vec r) (Vec r) ℚ), y) = ∑ h : Vec r, y h • ((0 : Matrix (Vec r) (Vec r) ℚ), delta h) := by
        ext a b
        · simp [Prod.fst_sum]
        · simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply, delta, smul_eq_mul]
          rw [Finset.sum_eq_single a]
          · simp
          · intro h _ hh; simp [Ne.symm hh]
          · intro h'; exact False.elim (h' (Finset.mem_univ _))
      rw [hdec]
      exact Submodule.sum_mem _ (fun h _ => Submodule.smul_mem _ _ (hdelta_mem h))
    rw [eq_top_iff]
    rintro ⟨X, y⟩ _
    have hsplit : (X, y) = (X, 0) + (0, y) := by simp
    rw [hsplit]
    exact Submodule.add_mem _ (hmat_all X) (hvec_all y)
  let B : V →ₗ[ℚ] V →ₗ[ℚ] ℚ := z2Pairing r
  have hnondeg : ∀ p2 : V, (∀ p1 : V, B p1 p2 = 0) → p2 = 0 := z2Pairing_nondeg r hr2
  have hB_delta : ∀ (X1 X2 : Matrix (Vec r) (Vec r) ℚ) (s1 s2 : Vec r),
      B (X1, delta s1) (X2, delta s2) = Matrix.trace (X1 * X2) + corr (s1 + s2) := by
    intro X1 X2 s1 s2
    change Matrix.trace (X1 * X2) + ∑ a : Vec r, ∑ b : Vec r, delta s1 a * z2Corr r (a + b) * delta s2 b = _
    congr 1
    rw [Finset.sum_eq_single s1]
    · rw [Finset.sum_eq_single s2]
      · simp [delta, corr]
      · intro b _ hb; simp [delta, hb]
      · intro h'; exact False.elim (h' (Finset.mem_univ _))
    · intro a _ ha; simp [delta, ha]
    · intro h'; exact False.elim (h' (Finset.mem_univ _))
  have hfinV : Module.finrank ℚ V = q ^ 2 + q := by
    rw [Module.finrank_prod, Module.finrank_matrix, Module.finrank_fintype_fun_eq_card, card_vec,
      Module.finrank_self, mul_one, sq]
  have hlb_pos : Fits r 2 k (fun w => 0 < w.length) → q ^ 2 + q ≤ k := by
    intro hfit
    rw [← hfinV]
    exact lower_bound_of_nondeg_pairing φ B hnondeg
      (fun w1 w2 hw1 hw2 => by
        rw [hcyc_pos (w1 ++ w2) (by simp; omega), List.map_append, List.prod_append, List.sum_append,
          hB_delta])
      h𝒦_top hfit
  have hlb_all : Fits r 2 k (fun _ => True) → q ^ 2 + q + 1 ≤ k := by
    intro hfit
    rw [← hfinV]
    let v0 : V := (1, delta 0)
    have hjump : cycleVal (r := r) 2 [] ≠ B v0 v0 := by
      rw [cycleVal_nil, hB_delta, Matrix.one_mul, Matrix.trace_one, card_vec, add_zero]
      simp only [corr, z2Corr, fVal, ↓reduceIte]
      norm_num
    exact lower_bound_all_of_nondeg_pairing φ v0 B hnondeg
      (fun w1 w2 hw1 hw2 => by
        rw [hcyc_pos (w1 ++ w2) (by simp; omega), List.map_append, List.prod_append, List.sum_append,
          hB_delta])
      (fun w2 hw2 => by
        rw [hcyc_pos w2 hw2, hB_delta, Matrix.one_mul, zero_add])
      (fun w1 hw1 => by
        rw [hcyc_pos w1 hw1, hB_delta, Matrix.mul_one, add_zero])
      hjump h𝒦_top hfit
  exact ⟨⟨hlb_all, fun hk => realizes_mono hk hup_all⟩,
    ⟨hlb_pos, fun hk => realizes_mono hk hup_pos⟩⟩

lemma main_proof (r : ℕ) (z : ℚ)
    (hsing : r = 0 ∨ z = 0 ∨ z = 2 ∨ z = ((2 ^ r : ℕ) : ℚ)) :
    let q : ℕ := 2 ^ r
    let least : ℕ := if r = 0 then (if z = 1 then 1 else if z = 2 then 2 else 3)
      else if z = 0 then 3
      else if z = 2 then (if q = 2 then 2 else q ^ 2 + q + 1)
      else q ^ 2
    ∀ k : ℕ, (Fits r z k (fun _ => True) ↔ least ≤ k) ∧
      (Fits r z k (fun w => 0 < w.length) ↔ (if z = 2 then least - 1 else least) ≤ k) := by
  dsimp only
  intro k
  by_cases hr0 : r = 0
  · subst hr0
    simp only [↓reduceIte]
    exact solve_r0 z k
  · simp only [hr0, ↓reduceIte]
    by_cases hz0 : z = 0
    · subst hz0
      simp only [↓reduceIte, OfNat.zero_ne_ofNat]
      exact solve_z0 r hr0 k
    · simp only [hz0, ↓reduceIte]
      by_cases hz2 : z = 2
      · subst hz2
        simp only [↓reduceIte]
        by_cases hr1 : r = 1
        · subst hr1
          simp only [pow_one, ↓reduceIte]
          exact solve_r1_z2 k
        · have hr2 : 2 ≤ r := by omega
          have hqne2 : 2 ^ r ≠ 2 := by
            have : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hr2
            omega
          simp only [hqne2, ↓reduceIte, Nat.add_sub_cancel]
          exact solve_z2_ge4 r hr2 k
      · simp only [hz2, ↓reduceIte]
        have hzq : z = ((2 ^ r : ℕ) : ℚ) := by
          rcases hsing with h | h | h | h
          · exact absurd h hr0
          · exact absurd h hz0
          · exact absurd h hz2
          · exact h
        have hr1_ne : r ≠ 1 := by
          intro hr1
          subst hr1
          simp at hzq
          exact hz2 hzq
        have hr2 : 2 ≤ r := by omega
        subst hzq
        exact solve_zq_ge4 r hr2 k

end PEqualNP.Outside.L_lib_801_aux

theorem PEqualNP.Outside.L_lib_801 :
∀ (r : ℕ) (z : ℚ),
  let A := Fin r → ZMod 2
  let q : ℕ := 2^r
  let f := fun a : A => if a = 0 then z-1 else -1
  let T : A → Matrix (Option A) (Option A) ℚ := fun h before after =>
    before.elim (after.elim 1 (fun b => if b = h then 1 else 0))
      (fun a => after.elim (f a) (fun b => if b = a+h then 1 else 0))
  let cycle := fun w : List A =>
    Matrix.trace (w.map T).prod + f w.sum - (if w.sum = 0 then (q : ℚ) else 0)
  let fits := fun (k : ℕ) (test : List A → Prop) =>
    ∃ (u v : Fin k → ℚ) (M : A → Matrix (Fin k) (Fin k) ℚ),
      ∀ w : List A, test w → (∑ i : Fin k, ∑ j : Fin k, u i * (w.map M).prod i j * v j) = cycle w
  (r = 0 ∨ z = 0 ∨ z = 2 ∨ z = (q : ℚ)) →
    let least : ℕ := if r = 0 then (if z = 1 then 1 else if z = 2 then 2 else 3)
      else if z = 0 then 3
      else if z = 2 then (if q = 2 then 2 else q^2+q+1)
      else q^2
    ∀ k : ℕ, (fits k (fun _ => True) ↔ least ≤ k) ∧
      (fits k (fun w => 0 < w.length) ↔ (if z = 2 then least-1 else least) ≤ k) := by
  intro r z
  dsimp only
  intro hsing k
  exact PEqualNP.Outside.L_lib_801_aux.main_proof r z hsing k
