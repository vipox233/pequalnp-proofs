import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_987_aux

open scoped Matrix

abbrev F := ZMod 2

lemma z2_add_self (a : F) : a + a = 0 := by fin_cases a <;> rfl
lemma z2_sq (a : F) : a * a = a := by fin_cases a <;> rfl
lemma z2_eq_zero_or_one (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl
lemma z2_add_eq_zero_iff (a b : F) : a + b = 0 ↔ a = b := by
  revert a b; decide

lemma finrank_sup_le' {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (U W : Submodule F V) :
    Module.finrank F (U ⊔ W : Submodule F V) ≤ Module.finrank F U + Module.finrank F W := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq U W
  omega

lemma eq_of_le_of_finrank_ge' {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {U W : Submodule F V} (hle : U ≤ W) (hge : Module.finrank F W ≤ Module.finrank F U) :
    U = W :=
  Submodule.eq_of_le_of_finrank_eq hle (le_antisymm (Submodule.finrank_mono hle) hge)

lemma mat_add_self {α β : Type*} (A : Matrix α β F) : A + A = 0 := by
  ext i j; exact z2_add_self (A i j)

lemma mat_add_eq_zero_iff {α β : Type*} (A B : Matrix α β F) : A + B = 0 ↔ A = B := by
  constructor
  · intro h; ext i j
    exact (z2_add_eq_zero_iff _ _).mp (congrFun (congrFun h i) j)
  · rintro rfl; exact mat_add_self A

lemma vec_add_self {α : Type*} (v : α → F) : v + v = 0 := by
  ext i; exact z2_add_self (v i)

lemma vec_add_eq_zero_iff {α : Type*} (u v : α → F) : u + v = 0 ↔ u = v := by
  constructor
  · intro h; ext i; exact (z2_add_eq_zero_iff _ _).mp (congrFun h i)
  · rintro rfl; exact vec_add_self u

def Alt {n : ℕ} (A : Matrix (Fin n) (Fin n) F) : Prop :=
  A.transpose = A ∧ ∀ i, A i i = 0

lemma Alt.zero {n : ℕ} : Alt (0 : Matrix (Fin n) (Fin n) F) :=
  ⟨by ext i j; rfl, fun _ => rfl⟩

lemma Alt.add {n : ℕ} {A B : Matrix (Fin n) (Fin n) F} (hA : Alt A) (hB : Alt B) :
    Alt (A + B) := by
  refine ⟨?_, fun i => ?_⟩
  · rw [Matrix.transpose_add, hA.1, hB.1]
  · change A i i + B i i = 0; rw [hA.2 i, hB.2 i, add_zero]

lemma Alt.smul {n : ℕ} (c : F) {A : Matrix (Fin n) (Fin n) F} (hA : Alt A) :
    Alt (c • A) := by
  refine ⟨?_, fun i => ?_⟩
  · rw [Matrix.transpose_smul, hA.1]
  · change c * A i i = 0; rw [hA.2 i, mul_zero]

def WSub {n : ℕ} (P : Submodule F (Matrix (Fin n) (Fin n) F)) :
    Submodule F (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :=
  { carrier := {X | ∃ A K : Matrix (Fin n) (Fin n) F,
      Alt A ∧ K ∈ P ∧ X = Matrix.fromBlocks A K K (0 : Matrix (Fin n) (Fin n) F)}
    zero_mem' := ⟨0, 0, Alt.zero, P.zero_mem, by ext i j; cases i <;> cases j <;> rfl⟩
    smul_mem' := by
      rintro c _ ⟨A, K, hA, hK, rfl⟩
      refine ⟨c • A, c • K, hA.smul c, P.smul_mem c hK, ?_⟩
      rw [Matrix.fromBlocks_smul, smul_zero]
    , add_mem' := by
      rintro _ _ ⟨A₁, K₁, hA₁, hK₁, rfl⟩ ⟨A₂, K₂, hA₂, hK₂, rfl⟩
      refine ⟨A₁ + A₂, K₁ + K₂, hA₁.add hA₂, P.add_mem hK₁ hK₂, ?_⟩
      rw [Matrix.fromBlocks_add, add_zero] }

lemma WSub_eq_span {n : ℕ} (P : Submodule F (Matrix (Fin n) (Fin n) F)) :
    Submodule.span F {X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F |
      ∃ A K : Matrix (Fin n) (Fin n) F,
        Alt A ∧ K ∈ P ∧ X = Matrix.fromBlocks A K K (0 : Matrix (Fin n) (Fin n) F)} = WSub P :=
  le_antisymm (Submodule.span_le.mpr fun _ h => h) (fun _ h => Submodule.subset_span h)

def crossLin (n : ℕ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F →ₗ[F] Matrix (Fin n) (Fin n) F where
  toFun X i j := X (Sum.inl i) (Sum.inr j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma crossLin_fromBlocks {n : ℕ} (A K : Matrix (Fin n) (Fin n) F) :
    crossLin n (Matrix.fromBlocks A K K (0 : Matrix (Fin n) (Fin n) F)) = K := by
  ext i j; rfl

noncomputable def colSp {α β : Type*} [Fintype β] (A : Matrix α β F) : Submodule F (α → F) :=
  LinearMap.range A.mulVecLin

lemma rank_eq_finrank_colSp {α β : Type*} [Fintype β] (A : Matrix α β F) :
    A.rank = Module.finrank F (colSp A) := rfl

lemma colSp_add_le {α β : Type*} [Fintype β] (A B : Matrix α β F) :
    colSp (A + B) ≤ colSp A ⊔ colSp B := by
  rintro y ⟨x, rfl⟩
  change (A + B) *ᵥ x ∈ colSp A ⊔ colSp B
  rw [Matrix.add_mulVec]
  exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩

lemma rank_add_le {α β : Type*} [Fintype α] [Fintype β] (A B : Matrix α β F) :
    (A + B).rank ≤ A.rank + B.rank := by
  rw [rank_eq_finrank_colSp, rank_eq_finrank_colSp, rank_eq_finrank_colSp]
  exact (Submodule.finrank_mono (colSp_add_le A B)).trans (finrank_sup_le' _ _)

lemma colSp_add_eq_sup_of_rank_eq {α β : Type*} [Fintype α] [Fintype β] (A B : Matrix α β F)
    (h : (A + B).rank = A.rank + B.rank) :
    colSp (A + B) = colSp A ⊔ colSp B := by
  apply eq_of_le_of_finrank_ge' (colSp_add_le A B)
  have h1 : Module.finrank F (colSp A ⊔ colSp B : Submodule F (α → F)) ≤ A.rank + B.rank :=
    finrank_sup_le' (colSp A) (colSp B)
  rw [rank_eq_finrank_colSp] at h
  omega

def piBot (n : ℕ) : (Fin n ⊕ Fin n → F) →ₗ[F] (Fin n → F) where
  toFun v := v ∘ Sum.inr
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def injTop (n : ℕ) : (Fin n → F) →ₗ[F] (Fin n ⊕ Fin n → F) where
  toFun u := Sum.elim u 0
  map_add' u v := by ext i; cases i <;> simp
  map_smul' c u := by ext i; cases i <;> simp

lemma injTop_injective (n : ℕ) : Function.Injective (injTop n) := by
  intro u v h
  ext i
  exact congrFun h (Sum.inl i)

lemma fromBlocks_mulVec_inl {n : ℕ} (A K : Matrix (Fin n) (Fin n) F) (v : Fin n ⊕ Fin n → F)
    (i : Fin n) :
    (Matrix.fromBlocks A K K (0 : Matrix (Fin n) (Fin n) F) *ᵥ v) (Sum.inl i) =
      (A *ᵥ (v ∘ Sum.inl)) i + (K *ᵥ (v ∘ Sum.inr)) i := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

lemma fromBlocks_mulVec_inr {n : ℕ} (A K : Matrix (Fin n) (Fin n) F) (v : Fin n ⊕ Fin n → F)
    (i : Fin n) :
    (Matrix.fromBlocks A K K (0 : Matrix (Fin n) (Fin n) F) *ᵥ v) (Sum.inr i) =
      (K *ᵥ (v ∘ Sum.inl)) i := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

lemma map_piBot_colSp_fromBlocks {n : ℕ} (A K : Matrix (Fin n) (Fin n) F) :
    (colSp (Matrix.fromBlocks A K K (0 : Matrix (Fin n) (Fin n) F))).map (piBot n) = colSp K := by
  ext y
  simp only [Submodule.mem_map, colSp, LinearMap.mem_range, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨v ∘ Sum.inl, ?_⟩
    ext i
    exact (fromBlocks_mulVec_inr A K v i).symm
  · rintro ⟨u, rfl⟩
    refine ⟨Matrix.fromBlocks A K K 0 *ᵥ Sum.elim u 0, ⟨Sum.elim u 0, rfl⟩, ?_⟩
    ext i
    exact fromBlocks_mulVec_inr A K (Sum.elim u 0) i

lemma two_mul_rank_le_rank_fromBlocks {n : ℕ} (A K : Matrix (Fin n) (Fin n) F) :
    2 * K.rank ≤ (Matrix.fromBlocks A K K (0 : Matrix (Fin n) (Fin n) F)).rank := by
  set X := Matrix.fromBlocks A K K (0 : Matrix (Fin n) (Fin n) F)
  let φ : colSp X →ₗ[F] (Fin n → F) := (piBot n).domRestrict (colSp X)
  have hrm := LinearMap.finrank_range_add_finrank_ker φ
  have hrange : LinearMap.range φ = colSp K := by
    rw [← map_piBot_colSp_fromBlocks A K]
    ext y
    simp only [φ, LinearMap.mem_range, LinearMap.domRestrict_apply, Subtype.exists, exists_prop,
      Submodule.mem_map]
    rfl
  have hr : Module.finrank F (LinearMap.range φ) = K.rank := by
    rw [hrange, rank_eq_finrank_colSp]
  have hmem : ∀ y ∈ colSp K, injTop n y ∈ colSp X := by
    rintro y ⟨u, rfl⟩
    refine ⟨Sum.elim 0 u, ?_⟩
    ext i
    cases i with
    | inl i =>
      change (X *ᵥ Sum.elim 0 u) (Sum.inl i) = (K *ᵥ u) i
      rw [fromBlocks_mulVec_inl]
      have h0 : Sum.elim (0 : Fin n → F) u ∘ Sum.inl = 0 := rfl
      have h1 : Sum.elim (0 : Fin n → F) u ∘ Sum.inr = u := rfl
      rw [h0, h1, Matrix.mulVec_zero, Pi.zero_apply, zero_add]
    | inr i =>
      change (X *ᵥ Sum.elim 0 u) (Sum.inr i) = 0
      rw [fromBlocks_mulVec_inr]
      have h0 : Sum.elim (0 : Fin n → F) u ∘ Sum.inl = 0 := rfl
      rw [h0, Matrix.mulVec_zero, Pi.zero_apply]
  let ψ : colSp K →ₗ[F] LinearMap.ker φ :=
    { toFun := fun y => ⟨⟨injTop n y.1, hmem y.1 y.2⟩, by
        change piBot n (injTop n y.1) = 0
        ext i; rfl⟩
      map_add' := fun x y => by ext i; cases i <;> simp [injTop]
      map_smul' := fun c x => by ext i; cases i <;> simp [injTop] }
  have hψinj : Function.Injective ψ := by
    intro x y h
    apply Subtype.ext
    apply injTop_injective n
    exact congrArg (fun z => z.1.1) h
  have hk : K.rank ≤ Module.finrank F (LinearMap.ker φ) := by
    rw [rank_eq_finrank_colSp]
    exact LinearMap.finrank_le_finrank_of_injective hψinj
  change 2 * K.rank ≤ Module.finrank F (colSp X)
  omega

lemma rank_ne_zero_of_ne_zero {n : ℕ} {K : Matrix (Fin n) (Fin n) F} (hK : K ≠ 0) :
    K.rank ≠ 0 := by
  intro hr
  apply hK
  have hbot : colSp K = ⊥ := Submodule.finrank_eq_zero.mp hr
  ext i j
  have hcol : K *ᵥ Pi.single j (1 : F) ∈ colSp K := ⟨Pi.single j 1, rfl⟩
  rw [hbot, Submodule.mem_bot] at hcol
  have hi := congrFun hcol i
  simpa [Matrix.mulVec_single] using hi

lemma rank_ne_one_of_alt {n : ℕ} {K : Matrix (Fin n) (Fin n) F} (hK : Alt K) :
    K.rank ≠ 1 := by
  intro hr
  have hne : colSp K ≠ ⊥ := by
    intro hb
    rw [rank_eq_finrank_colSp, hb, finrank_bot] at hr
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hsp : Submodule.span F {u} = colSp K := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr (by simpa using hu)
    · rw [finrank_span_singleton hu0, ← rank_eq_finrank_colSp, hr]
  have hcol : ∀ j : Fin n, ∃ c : F, ∀ i : Fin n, K i j = c * u i := by
    intro j
    have hm : K *ᵥ Pi.single j (1 : F) ∈ Submodule.span F {u} := by
      rw [hsp]; exact ⟨Pi.single j 1, rfl⟩
    rw [Submodule.mem_span_singleton] at hm
    obtain ⟨c, hc⟩ := hm
    refine ⟨c, fun i => ?_⟩
    have hi := congrFun hc i
    simpa [Matrix.mulVec_single, mul_comm] using hi.symm
  choose c hc using hcol
  have hK0 : K ≠ 0 := by
    intro h0; rw [h0, Matrix.rank_zero] at hr; omega
  have hex : ∃ i₀ j₀ : Fin n, K i₀ j₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hK0 (Matrix.ext hall)
  obtain ⟨i₀, j₀, hij⟩ := hex
  have h1 : c j₀ * u i₀ ≠ 0 := by rwa [← hc j₀ i₀]
  have hui : u i₀ = 1 := by
    rcases z2_eq_zero_or_one (u i₀) with h | h
    · exfalso; apply h1; simp [h]
    · exact h
  have hsym : K j₀ i₀ = K i₀ j₀ := congrFun (congrFun hK.1 i₀) j₀
  have h2 : c i₀ * u j₀ ≠ 0 := by rwa [← hc i₀ j₀, hsym]
  have hci : c i₀ = 1 := by
    rcases z2_eq_zero_or_one (c i₀) with h | h
    · exfalso; apply h2; simp [h]
    · exact h
  have hdiag : K i₀ i₀ = 0 := hK.2 i₀
  rw [hc i₀ i₀, hci, hui, mul_one] at hdiag
  exact one_ne_zero hdiag

lemma two_le_rank_of_alt_ne_zero {n : ℕ} {K : Matrix (Fin n) (Fin n) F}
    (hK : Alt K) (hne : K ≠ 0) : 2 ≤ K.rank := by
  have h0 := rank_ne_zero_of_ne_zero hne
  have h1 := rank_ne_one_of_alt hK
  omega

lemma cross_eq_zero_of_mem_W_rank_le_two {n : ℕ}
    {P : Submodule F (Matrix (Fin n) (Fin n) F)}
    (hP : ∀ K ∈ P, Alt K)
    {X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hXW : X ∈ WSub P) (hXr : X.rank ≤ 2) :
    crossLin n X = 0 := by
  obtain ⟨A, K, _, hKP, rfl⟩ := hXW
  rw [crossLin_fromBlocks]
  by_contra hKne
  have h1 := two_le_rank_of_alt_ne_zero (hP K hKP) hKne
  have h2 := two_mul_rank_le_rank_fromBlocks A K
  omega

def wedge {n : ℕ} (u v : Fin n → F) : Matrix (Fin n) (Fin n) F :=
  fun i j => u i * v j + v i * u j

lemma wedge_mulVec {n : ℕ} (u v x : Fin n → F) :
    wedge u v *ᵥ x = (dotProduct v x) • u + (dotProduct u x) • v := by
  ext i
  simp only [Matrix.mulVec, dotProduct, wedge, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma wedge_add_right {n : ℕ} (w a b : Fin n → F) :
    wedge w a + wedge w b = wedge w (a + b) := by
  ext i j
  simp only [Matrix.add_apply, wedge, Pi.add_apply]
  ring

lemma exists_det_one_of_pair {n : ℕ} {u v : Fin n → F}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    ∃ i₁ i₂ : Fin n, u i₁ * v i₂ + v i₁ * u i₂ = 1 := by
  have hexu : ∃ i₁, u i₁ ≠ 0 := by
    by_contra h; push Not at h; exact hu (funext h)
  obtain ⟨i₁, hi₁⟩ := hexu
  have hui₁ : u i₁ = 1 := (z2_eq_zero_or_one (u i₁)).resolve_left hi₁
  rcases z2_eq_zero_or_one (v i₁) with hvi₁ | hvi₁
  · have hexv : ∃ i₂, v i₂ ≠ 0 := by
      by_contra h; push Not at h; exact hv (funext h)
    obtain ⟨i₂, hi₂⟩ := hexv
    have hvi₂ : v i₂ = 1 := (z2_eq_zero_or_one (v i₂)).resolve_left hi₂
    exact ⟨i₁, i₂, by rw [hui₁, hvi₂, hvi₁]; simp⟩
  · have hexne : ∃ i₂, u i₂ ≠ v i₂ := by
      by_contra h; push Not at h; exact huv (funext h)
    obtain ⟨i₂, hi₂⟩ := hexne
    refine ⟨i₁, i₂, ?_⟩
    rw [hui₁, hvi₁, one_mul, one_mul]
    rcases z2_eq_zero_or_one (u i₂) with h1 | h1 <;>
    rcases z2_eq_zero_or_one (v i₂) with h2 | h2 <;>
    simp_all

lemma colSp_wedge {n : ℕ} {u v : Fin n → F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    colSp (wedge u v) = Submodule.span F ({u, v} : Set (Fin n → F)) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    change wedge u v *ᵥ x ∈ _
    rw [wedge_mulVec]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · obtain ⟨i₁, i₂, hdet⟩ := exists_det_one_of_pair hu hv huv
    rw [Submodule.span_le]
    intro y hy
    rcases Set.mem_insert_iff.mp hy with hyu | hyv
    · rw [hyu]
      refine ⟨u i₂ • Pi.single i₁ 1 + u i₁ • Pi.single i₂ 1, ?_⟩
      change wedge u v *ᵥ _ = u
      rw [wedge_mulVec]
      have hdu : dotProduct u (u i₂ • Pi.single i₁ (1 : F) + u i₁ • Pi.single i₂ 1) = 0 := by
        simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_single, mul_one]
        rw [mul_comm (u i₂) (u i₁)]
        exact z2_add_self _
      have hdv : dotProduct v (u i₂ • Pi.single i₁ (1 : F) + u i₁ • Pi.single i₂ 1) = 1 := by
        simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_single, mul_one]
        calc u i₂ * v i₁ + u i₁ * v i₂ = u i₁ * v i₂ + v i₁ * u i₂ := by ring
          _ = 1 := hdet
      rw [hdu, hdv, zero_smul, one_smul, add_zero]
    · rw [Set.mem_singleton_iff.mp hyv]
      refine ⟨v i₂ • Pi.single i₁ 1 + v i₁ • Pi.single i₂ 1, ?_⟩
      change wedge u v *ᵥ _ = v
      rw [wedge_mulVec]
      have hdv : dotProduct v (v i₂ • Pi.single i₁ (1 : F) + v i₁ • Pi.single i₂ 1) = 0 := by
        simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_single, mul_one]
        rw [mul_comm (v i₂) (v i₁)]
        exact z2_add_self _
      have hdu : dotProduct u (v i₂ • Pi.single i₁ (1 : F) + v i₁ • Pi.single i₂ 1) = 1 := by
        simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_single, mul_one]
        calc v i₂ * u i₁ + v i₁ * u i₂ = u i₁ * v i₂ + v i₁ * u i₂ := by ring
          _ = 1 := hdet
      rw [hdu, hdv, zero_smul, one_smul, zero_add]

lemma eq_wedge_of_alt_colSp {n : ℕ} {K : Matrix (Fin n) (Fin n) F}
    (hK : Alt K) (hKne : K ≠ 0) {u v : Fin n → F}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (hsp : colSp K = Submodule.span F ({u, v} : Set (Fin n → F))) :
    K = wedge u v := by
  obtain ⟨i₁, i₂, hdet⟩ := exists_det_one_of_pair hu hv huv
  have hcol : ∀ j : Fin n, ∃ a b : F, ∀ i : Fin n, K i j = u i * a + v i * b := by
    intro j
    have hm : K *ᵥ Pi.single j (1 : F) ∈ Submodule.span F ({u, v} : Set (Fin n → F)) := by
      rw [← hsp]; exact ⟨Pi.single j 1, rfl⟩
    rw [Submodule.mem_span_pair] at hm
    obtain ⟨a, b, hab⟩ := hm
    refine ⟨a, b, fun i => ?_⟩
    have hi := congrFun hab i
    simpa [Matrix.mulVec_single, mul_comm] using hi.symm
  choose a b hab using hcol
  have ha_eq : ∀ j : Fin n, a j = v i₂ * K i₁ j + v i₁ * K i₂ j := by
    intro j
    rw [hab j i₁, hab j i₂]
    calc a j = (u i₁ * v i₂ + v i₁ * u i₂) * a j + (v i₂ * v i₁ + v i₁ * v i₂) * b j := by
          rw [hdet, one_mul, mul_comm (v i₂) (v i₁), z2_add_self, zero_mul, add_zero]
      _ = v i₂ * (u i₁ * a j + v i₁ * b j) + v i₁ * (u i₂ * a j + v i₂ * b j) := by ring
  have hb_eq : ∀ j : Fin n, b j = u i₂ * K i₁ j + u i₁ * K i₂ j := by
    intro j
    rw [hab j i₁, hab j i₂]
    calc b j = (u i₂ * u i₁ + u i₁ * u i₂) * a j + (u i₁ * v i₂ + v i₁ * u i₂) * b j := by
          rw [hdet, one_mul, mul_comm (u i₂) (u i₁), z2_add_self, zero_mul, zero_add]
      _ = u i₂ * (u i₁ * a j + v i₁ * b j) + u i₁ * (u i₂ * a j + v i₂ * b j) := by ring
  have hsym : ∀ i j : Fin n, K i j = K j i := fun i j =>
    congrFun (congrFun hK.1 j) i
  let α : F := v i₂ * a i₁ + v i₁ * a i₂
  let β : F := v i₂ * b i₁ + v i₁ * b i₂
  let γ : F := u i₂ * a i₁ + u i₁ * a i₂
  let δ : F := u i₂ * b i₁ + u i₁ * b i₂
  have ha_lin : ∀ j, a j = α * u j + β * v j := by
    intro j
    rw [ha_eq j, hsym i₁ j, hsym i₂ j, hab i₁ j, hab i₂ j]
    dsimp [α, β]; ring
  have hb_lin : ∀ j, b j = γ * u j + δ * v j := by
    intro j
    rw [hb_eq j, hsym i₁ j, hsym i₂ j, hab i₁ j, hab i₂ j]
    dsimp [γ, δ]; ring
  have hKform : ∀ i j, K i j = α * (u i * u j) + β * (u i * v j) +
      γ * (v i * u j) + δ * (v i * v j) := by
    intro i j
    rw [hab j i, ha_lin j, hb_lin j]
    ring
  have hβγ : β = γ := by
    have hs := hsym i₁ i₂
    rw [hKform i₁ i₂, hKform i₂ i₁] at hs
    have h0 : (β + γ) * (u i₁ * v i₂ + v i₁ * u i₂) = 0 := by
      have hz := (z2_add_eq_zero_iff _ _).mpr hs
      calc (β + γ) * (u i₁ * v i₂ + v i₁ * u i₂)
          = (α * (u i₁ * u i₂) + β * (u i₁ * v i₂) + γ * (v i₁ * u i₂) + δ * (v i₁ * v i₂)) +
            (α * (u i₂ * u i₁) + β * (u i₂ * v i₁) + γ * (v i₂ * u i₁) + δ * (v i₂ * v i₁)) := by
              have h1 : α * (u i₁ * u i₂) + α * (u i₂ * u i₁) = 0 := by
                rw [mul_comm (u i₂) (u i₁)]; exact z2_add_self _
              have h2 : δ * (v i₁ * v i₂) + δ * (v i₂ * v i₁) = 0 := by
                rw [mul_comm (v i₂) (v i₁)]; exact z2_add_self _
              calc (β + γ) * (u i₁ * v i₂ + v i₁ * u i₂)
                  = (β + γ) * (u i₁ * v i₂ + v i₁ * u i₂) + 0 + 0 := by simp
                _ = (β + γ) * (u i₁ * v i₂ + v i₁ * u i₂) +
                    (α * (u i₁ * u i₂) + α * (u i₂ * u i₁)) +
                    (δ * (v i₁ * v i₂) + δ * (v i₂ * v i₁)) := by rw [h1, h2]
                _ = _ := by ring
        _ = 0 := hz
    rw [hdet, mul_one] at h0
    exact (z2_add_eq_zero_iff β γ).mp h0
  have hdiag : ∀ i, α * u i + δ * v i = 0 := by
    intro i
    have hd := hK.2 i
    rw [hKform i i, hβγ, z2_sq (u i), z2_sq (v i)] at hd
    have hmid : γ * (u i * v i) + γ * (v i * u i) = 0 := by
      rw [mul_comm (v i) (u i)]; exact z2_add_self _
    calc α * u i + δ * v i
        = α * u i + (γ * (u i * v i) + γ * (v i * u i)) + δ * v i := by rw [hmid, add_zero]
      _ = α * u i + γ * (u i * v i) + γ * (v i * u i) + δ * v i := by ring
      _ = 0 := hd
  have hα : α = 0 := by
    calc α = α * (u i₁ * v i₂ + v i₁ * u i₂) + δ * 0 := by
          rw [hdet, mul_one, mul_zero, add_zero]
      _ = α * (u i₁ * v i₂ + v i₁ * u i₂) + δ * (v i₂ * v i₁ + v i₁ * v i₂) := by
          rw [mul_comm (v i₂) (v i₁), z2_add_self]
      _ = v i₂ * (α * u i₁ + δ * v i₁) + v i₁ * (α * u i₂ + δ * v i₂) := by ring
      _ = 0 := by rw [hdiag i₁, hdiag i₂]; simp
  have hδ : δ = 0 := by
    calc δ = δ * (u i₁ * v i₂ + v i₁ * u i₂) + α * 0 := by
          rw [hdet, mul_one, mul_zero, add_zero]
      _ = δ * (u i₁ * v i₂ + v i₁ * u i₂) + α * (u i₂ * u i₁ + u i₁ * u i₂) := by
          rw [mul_comm (u i₂) (u i₁), z2_add_self]
      _ = u i₂ * (α * u i₁ + δ * v i₁) + u i₁ * (α * u i₂ + δ * v i₂) := by ring
      _ = 0 := by rw [hdiag i₁, hdiag i₂]; simp
  have hKβ : ∀ i j, K i j = β * (u i * v j + v i * u j) := by
    intro i j
    rw [hKform i j, hα, hδ, ← hβγ]
    ring
  have hβ : β = 1 := by
    rcases z2_eq_zero_or_one β with h0 | h1
    · exfalso; apply hKne
      ext i j; rw [hKβ i j, h0, zero_mul]; rfl
    · exact h1
  ext i j
  rw [hKβ i j, hβ, one_mul]
  rfl

lemma rank_wedge_add_of_disjoint {n : ℕ} {u₁ v₁ u₂ v₂ : Fin n → F}
    (hu₁ : u₁ ≠ 0) (hv₁ : v₁ ≠ 0) (huv₁ : u₁ ≠ v₁)
    (hu₂ : u₂ ≠ 0) (hv₂ : v₂ ≠ 0) (huv₂ : u₂ ≠ v₂)
    (hdisj : Submodule.span F ({u₁, v₁} : Set (Fin n → F)) ⊓
      Submodule.span F ({u₂, v₂} : Set (Fin n → F)) = ⊥) :
    (wedge u₁ v₁ + wedge u₂ v₂).rank = 4 := by
  let vecs : Fin 4 → (Fin n → F) := ![u₁, v₁, u₂, v₂]
  have hli : LinearIndependent F vecs := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : (g 0 • u₁ + g 1 • v₁) + (g 2 • u₂ + g 3 • v₂) = 0 := by
      have h4 : ∑ i : Fin 4, g i • vecs i =
          g 0 • u₁ + g 1 • v₁ + (g 2 • u₂ + g 3 • v₂) := by
        rw [Fin.sum_univ_four]
        simp only [vecs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
        abel
      rwa [← h4]
    have hmem1 : g 0 • u₁ + g 1 • v₁ ∈ Submodule.span F ({u₁, v₁} : Set (Fin n → F)) :=
      Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hmem2 : g 2 • u₂ + g 3 • v₂ ∈ Submodule.span F ({u₂, v₂} : Set (Fin n → F)) :=
      Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have heq : g 0 • u₁ + g 1 • v₁ = g 2 • u₂ + g 3 • v₂ :=
      (vec_add_eq_zero_iff _ _).mp hsum
    have hbot : g 0 • u₁ + g 1 • v₁ ∈ (⊥ : Submodule F (Fin n → F)) := by
      rw [← hdisj]
      exact ⟨hmem1, heq ▸ hmem2⟩
    rw [Submodule.mem_bot] at hbot
    have hbot2 : g 2 • u₂ + g 3 • v₂ = 0 := heq ▸ hbot
    have h01 : g 0 = 0 ∧ g 1 = 0 := by
      rcases z2_eq_zero_or_one (g 0) with h0 | h0 <;>
      rcases z2_eq_zero_or_one (g 1) with h1 | h1
      · exact ⟨h0, h1⟩
      · rw [h0, h1, zero_smul, one_smul, zero_add] at hbot; exact absurd hbot hv₁
      · rw [h0, h1, one_smul, zero_smul, add_zero] at hbot; exact absurd hbot hu₁
      · rw [h0, h1, one_smul, one_smul] at hbot
        exact absurd ((vec_add_eq_zero_iff u₁ v₁).mp hbot) huv₁
    have h23 : g 2 = 0 ∧ g 3 = 0 := by
      rcases z2_eq_zero_or_one (g 2) with h2 | h2 <;>
      rcases z2_eq_zero_or_one (g 3) with h3 | h3
      · exact ⟨h2, h3⟩
      · rw [h2, h3, zero_smul, one_smul, zero_add] at hbot2; exact absurd hbot2 hv₂
      · rw [h2, h3, one_smul, zero_smul, add_zero] at hbot2; exact absurd hbot2 hu₂
      · rw [h2, h3, one_smul, one_smul] at hbot2
        exact absurd ((vec_add_eq_zero_iff u₂ v₂).mp hbot2) huv₂
    intro i
    fin_cases i
    · exact h01.1
    · exact h01.2
    · exact h23.1
    · exact h23.2
  let B : Matrix (Fin 4) (Fin n) F := fun k j => vecs k j
  have hBT : Bᵀ.rank = 4 := by
    rw [rank_eq_finrank_colSp]
    have hrg : colSp Bᵀ = Submodule.span F (Set.range vecs) := by
      ext y
      simp only [colSp, LinearMap.mem_range, Matrix.mulVecLin_apply,
        ← Fintype.range_linearCombination]
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨x, ?_⟩
        ext i
        simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Matrix.mulVec, dotProduct, B]
        apply Finset.sum_congr rfl
        intro k _
        exact mul_comm _ _
      · rintro ⟨x, rfl⟩
        refine ⟨x, ?_⟩
        ext i
        simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Matrix.mulVec, dotProduct, B]
        apply Finset.sum_congr rfl
        intro k _
        exact mul_comm _ _
    rw [hrg, finrank_span_eq_card hli, Fintype.card_fin]
  have hBr : B.rank = 4 := by
    rw [← Matrix.rank_transpose, hBT]
  have hker : LinearMap.ker (wedge u₁ v₁ + wedge u₂ v₂).mulVecLin = LinearMap.ker B.mulVecLin := by
    ext x
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.add_mulVec, wedge_mulVec]
    constructor
    · intro hx
      let c : Fin 4 → F := ![dotProduct v₁ x, dotProduct u₁ x, dotProduct v₂ x, dotProduct u₂ x]
      have hsum : ∑ i : Fin 4, c i • vecs i = 0 := by
        rw [Fin.sum_univ_four]
        simp only [c, vecs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
        simpa [add_assoc] using hx
      have hc0 := (Fintype.linearIndependent_iff.mp hli) c hsum
      ext k
      change dotProduct (vecs k) x = 0
      fin_cases k
      · exact hc0 1
      · exact hc0 0
      · exact hc0 3
      · exact hc0 2
    · intro hx
      have h0 : dotProduct u₁ x = 0 := congrFun hx 0
      have h1 : dotProduct v₁ x = 0 := congrFun hx 1
      have h2 : dotProduct u₂ x = 0 := congrFun hx 2
      have h3 : dotProduct v₂ x = 0 := congrFun hx 3
      rw [h0, h1, h2, h3]
      simp
  have h1 := LinearMap.finrank_range_add_finrank_ker (wedge u₁ v₁ + wedge u₂ v₂).mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  rw [hker] at h1
  change (wedge u₁ v₁ + wedge u₂ v₂).rank + _ = _ at h1
  change B.rank + _ = _ at h2
  omega

lemma exists_pair_of_finrank_two {n : ℕ} {V : Submodule F (Fin n → F)}
    (hV : Module.finrank F V = 2) :
    ∃ u v : Fin n → F, u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧
      V = Submodule.span F ({u, v} : Set (Fin n → F)) := by
  have hne : V ≠ ⊥ := by
    intro hb; rw [hb, finrank_bot] at hV; omega
  obtain ⟨u, huV, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hlt : Submodule.span F {u} < V := by
    refine lt_of_le_of_ne (Submodule.span_le.mpr (by simpa using huV)) ?_
    intro heq
    have h1 : Module.finrank F (Submodule.span F {u}) = 1 := finrank_span_singleton hu0
    rw [heq, hV] at h1
    omega
  obtain ⟨v, hvV, hvnot⟩ := IsConcreteLE.exists_of_lt hlt
  have hv0 : v ≠ 0 := fun h => hvnot (h ▸ Submodule.zero_mem _)
  have huv : u ≠ v := fun h => hvnot (h ▸ Submodule.subset_span (Set.mem_singleton u))
  have hsub : Submodule.span F ({u, v} : Set (Fin n → F)) ≤ V :=
    Submodule.span_le.mpr (by intro x hx; rcases hx with rfl | rfl <;> assumption)
  have hlt2 : Submodule.span F {u} < Submodule.span F ({u, v} : Set (Fin n → F)) := by
    refine lt_of_le_of_ne (Submodule.span_mono (Set.singleton_subset_iff.mpr (by simp))) ?_
    intro heq
    exact hvnot (heq ▸ Submodule.subset_span (by simp))
  have hfr1 : Module.finrank F (Submodule.span F {u}) <
      Module.finrank F (Submodule.span F ({u, v} : Set (Fin n → F))) :=
    Submodule.finrank_lt_finrank_of_lt hlt2
  have hfr2 : Module.finrank F (Submodule.span F ({u, v} : Set (Fin n → F))) ≤
      Module.finrank F V :=
    Submodule.finrank_mono hsub
  have hfr_eq : Module.finrank F (Submodule.span F ({u, v} : Set (Fin n → F))) = 2 := by
    rw [finrank_span_singleton hu0] at hfr1; omega
  exact ⟨u, v, hu0, hv0, huv, (Submodule.eq_of_le_of_finrank_eq hsub (by rw [hfr_eq, hV])).symm⟩

lemma exists_extend_of_finrank_two {n : ℕ} {V : Submodule F (Fin n → F)}
    (hV : Module.finrank F V = 2) {w : Fin n → F} (hwV : w ∈ V) (hw0 : w ≠ 0) :
    ∃ a : Fin n → F, a ∈ V ∧ a ∉ Submodule.span F {w} ∧ a ≠ 0 ∧ w ≠ a ∧
      V = Submodule.span F ({w, a} : Set (Fin n → F)) := by
  have hlt : Submodule.span F {w} < V := by
    refine lt_of_le_of_ne (Submodule.span_le.mpr (by simpa using hwV)) ?_
    intro heq
    have h1 : Module.finrank F (Submodule.span F {w}) = 1 := finrank_span_singleton hw0
    rw [heq, hV] at h1
    omega
  obtain ⟨a, haV, hanot⟩ := IsConcreteLE.exists_of_lt hlt
  have ha0 : a ≠ 0 := fun h => hanot (h ▸ Submodule.zero_mem _)
  have hwa : w ≠ a := fun h => hanot (h ▸ Submodule.subset_span (Set.mem_singleton w))
  have hsub : Submodule.span F ({w, a} : Set (Fin n → F)) ≤ V :=
    Submodule.span_le.mpr (by intro x hx; rcases hx with rfl | rfl <;> assumption)
  have hlt2 : Submodule.span F {w} < Submodule.span F ({w, a} : Set (Fin n → F)) := by
    refine lt_of_le_of_ne (Submodule.span_mono (Set.singleton_subset_iff.mpr (by simp))) ?_
    intro heq
    exact hanot (heq ▸ Submodule.subset_span (by simp))
  have hfr1 : Module.finrank F (Submodule.span F {w}) <
      Module.finrank F (Submodule.span F ({w, a} : Set (Fin n → F))) :=
    Submodule.finrank_lt_finrank_of_lt hlt2
  have hfr2 : Module.finrank F (Submodule.span F ({w, a} : Set (Fin n → F))) ≤
      Module.finrank F V :=
    Submodule.finrank_mono hsub
  have hfr_eq : Module.finrank F (Submodule.span F ({w, a} : Set (Fin n → F))) = 2 := by
    rw [finrank_span_singleton hw0] at hfr1; omega
  exact ⟨a, haV, hanot, ha0, hwa, (Submodule.eq_of_le_of_finrank_eq hsub (by rw [hfr_eq, hV])).symm⟩

lemma part1 {n : ℕ} (P : Submodule F (Matrix (Fin n) (Fin n) F))
    (hP : ∀ K ∈ P, Alt K)
    (R : Fin 3 → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (hRk : ∀ i, (R i).rank ≤ 2)
    (hRW : ∀ i j, R i + R j ∈ WSub P) :
    ∃ i j : Fin 3, i ≠ j ∧ crossLin n (R i) = crossLin n (R j) := by
  by_contra hcontra
  push Not at hcontra
  have hpair : ∀ i j : Fin 3, i ≠ j →
      let K := crossLin n (R i) + crossLin n (R j)
      Alt K ∧ K ≠ 0 ∧ K.rank = 2 ∧
        colSp K = (colSp (R i)).map (piBot n) ⊔ (colSp (R j)).map (piBot n) := by
    intro i j hij
    obtain ⟨A, K, hA, hKP, hEq⟩ := hRW i j
    have hKeq : K = crossLin n (R i) + crossLin n (R j) := by
      have hc := congrArg (crossLin n) hEq
      rw [map_add, crossLin_fromBlocks] at hc
      exact hc.symm
    subst hKeq
    have hKne : crossLin n (R i) + crossLin n (R j) ≠ 0 := by
      intro h0
      exact hcontra i j hij ((mat_add_eq_zero_iff _ _).mp h0)
    have hKalt : Alt (crossLin n (R i) + crossLin n (R j)) := hP _ hKP
    have hKge : 2 ≤ (crossLin n (R i) + crossLin n (R j)).rank :=
      two_le_rank_of_alt_ne_zero hKalt hKne
    have hblk : 2 * (crossLin n (R i) + crossLin n (R j)).rank ≤ (R i + R j).rank := by
      rw [hEq]; exact two_mul_rank_le_rank_fromBlocks A _
    have hadd : (R i + R j).rank ≤ (R i).rank + (R j).rank := rank_add_le (R i) (R j)
    have hri := hRk i
    have hrj := hRk j
    have hKr : (crossLin n (R i) + crossLin n (R j)).rank = 2 := by omega
    have hsumr : (R i + R j).rank = (R i).rank + (R j).rank := by omega
    have hsup := colSp_add_eq_sup_of_rank_eq (R i) (R j) hsumr
    have hmap : colSp (crossLin n (R i) + crossLin n (R j)) =
        (colSp (R i)).map (piBot n) ⊔ (colSp (R j)).map (piBot n) := by
      rw [← map_piBot_colSp_fromBlocks A (crossLin n (R i) + crossLin n (R j)),
        ← hEq, hsup, Submodule.map_sup]
    exact ⟨hKalt, hKne, hKr, hmap⟩
  obtain ⟨hAlt01, hNe01, hRk01, hMap01⟩ := hpair 0 1 (by decide)
  obtain ⟨hAlt02, hNe02, hRk02, hMap02⟩ := hpair 0 2 (by decide)
  obtain ⟨hAlt12, hNe12, hRk12, hMap12⟩ := hpair 1 2 (by decide)
  set K01 := crossLin n (R 0) + crossLin n (R 1)
  set K02 := crossLin n (R 0) + crossLin n (R 2)
  set K12 := crossLin n (R 1) + crossLin n (R 2)
  have hK12eq : K12 = K01 + K02 := by
    ext i j
    change crossLin n (R 1) i j + crossLin n (R 2) i j =
      (crossLin n (R 0) i j + crossLin n (R 1) i j) +
      (crossLin n (R 0) i j + crossLin n (R 2) i j)
    have h00 := z2_add_self (crossLin n (R 0) i j)
    calc crossLin n (R 1) i j + crossLin n (R 2) i j
        = 0 + crossLin n (R 1) i j + crossLin n (R 2) i j := by rw [zero_add]
      _ = (crossLin n (R 0) i j + crossLin n (R 0) i j) +
          crossLin n (R 1) i j + crossLin n (R 2) i j := by rw [h00]
      _ = _ := by ring
  let V01 := colSp K01
  let V02 := colSp K02
  let V12 := colSp K12
  have hfr01 : Module.finrank F V01 = 2 := hRk01
  have hfr02 : Module.finrank F V02 = 2 := hRk02
  have hVne : V01 ≠ V02 := by
    intro heq
    obtain ⟨u, v, hu, hv, huv, hsp⟩ := exists_pair_of_finrank_two hfr01
    have h1 : K01 = wedge u v := eq_wedge_of_alt_colSp hAlt01 hNe01 hu hv huv hsp
    have h2 : K02 = wedge u v := eq_wedge_of_alt_colSp hAlt02 hNe02 hu hv huv (heq.symm.trans hsp)
    have h0 : K12 = 0 := by rw [hK12eq, h1, h2, mat_add_self]
    exact hNe12 h0
  have hVinf : V01 ⊓ V02 ≠ ⊥ := by
    intro hdisj
    obtain ⟨u₁, v₁, hu₁, hv₁, huv₁, hsp₁⟩ := exists_pair_of_finrank_two hfr01
    obtain ⟨u₂, v₂, hu₂, hv₂, huv₂, hsp₂⟩ := exists_pair_of_finrank_two hfr02
    have h1 : K01 = wedge u₁ v₁ := eq_wedge_of_alt_colSp hAlt01 hNe01 hu₁ hv₁ huv₁ hsp₁
    have h2 : K02 = wedge u₂ v₂ := eq_wedge_of_alt_colSp hAlt02 hNe02 hu₂ hv₂ huv₂ hsp₂
    have hr4 : K12.rank = 4 := by
      rw [hK12eq, h1, h2]
      exact rank_wedge_add_of_disjoint hu₁ hv₁ huv₁ hu₂ hv₂ huv₂
        (by rw [← hsp₁, ← hsp₂]; exact hdisj)
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVinf
  obtain ⟨a, haV01, hanot, ha0, hwa, hsp01⟩ := exists_extend_of_finrank_two hfr01 hw.1 hw0
  obtain ⟨b, hbV02, hbnot, hb0, hwb, hsp02⟩ := exists_extend_of_finrank_two hfr02 hw.2 hw0
  have hbnot01 : b ∉ V01 := by
    intro hb1
    have hsub : V02 ≤ V01 := by
      rw [hsp02, Submodule.span_le]
      intro x hx; rcases hx with rfl | rfl
      · exact hw.1
      · exact hb1
    exact hVne (Submodule.eq_of_le_of_finrank_eq hsub (by rw [hfr02, hfr01])).symm
  have hK01w : K01 = wedge w a := eq_wedge_of_alt_colSp hAlt01 hNe01 hw0 ha0 hwa hsp01
  have hK02w : K02 = wedge w b := eq_wedge_of_alt_colSp hAlt02 hNe02 hw0 hb0 hwb hsp02
  have hK12w : K12 = wedge w (a + b) := by rw [hK12eq, hK01w, hK02w, wedge_add_right]
  have hab0 : a + b ≠ 0 := by
    intro h0
    have heq : a = b := (vec_add_eq_zero_iff a b).mp h0
    exact hbnot01 (heq ▸ haV01)
  have hwab : w ≠ a + b := by
    intro h0
    have hb_eq : b = w + a := by
      ext i
      have hi : w i = a i + b i := congrFun h0 i
      have h1 := z2_add_self (a i)
      calc b i = 0 + b i := by rw [zero_add]
        _ = (a i + a i) + b i := by rw [h1]
        _ = (a i + b i) + a i := by ring
        _ = w i + a i := by rw [← hi]
    exact hbnot01 (hb_eq ▸ V01.add_mem hw.1 haV01)
  have hsp12 : V12 = Submodule.span F ({w, a + b} : Set (Fin n → F)) := by
    change colSp K12 = _
    rw [hK12w]
    exact colSp_wedge hw0 hab0 hwab
  have hinf01_02 : V01 ⊓ V02 ≤ Submodule.span F {w} := by
    intro z hz
    have hz2 : z ∈ Submodule.span F ({w, b} : Set (Fin n → F)) := hsp02 ▸ hz.2
    rw [Submodule.mem_span_pair] at hz2
    obtain ⟨c₁, c₂, hcz⟩ := hz2
    rcases z2_eq_zero_or_one c₂ with hc2 | hc2
    · rw [hc2, zero_smul, add_zero] at hcz
      rw [← hcz]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton w))
    · exfalso; apply hbnot01
      rw [hc2, one_smul] at hcz
      have hbeq : b = z + c₁ • w := by
        ext i
        have hi : c₁ * w i + b i = z i := congrFun hcz i
        have hs := z2_add_self (c₁ * w i)
        calc b i = 0 + b i := by rw [zero_add]
          _ = (c₁ * w i + c₁ * w i) + b i := by rw [hs]
          _ = (c₁ * w i + b i) + c₁ * w i := by ring
          _ = z i + c₁ * w i := by rw [hi]
      rw [hbeq]
      exact V01.add_mem hz.1 (V01.smul_mem c₁ hw.1)
  have hinf01_12 : V01 ⊓ V12 ≤ Submodule.span F {w} := by
    intro z hz
    have hz2 : z ∈ Submodule.span F ({w, a + b} : Set (Fin n → F)) := hsp12 ▸ hz.2
    rw [Submodule.mem_span_pair] at hz2
    obtain ⟨c₁, c₂, hcz⟩ := hz2
    rcases z2_eq_zero_or_one c₂ with hc2 | hc2
    · rw [hc2, zero_smul, add_zero] at hcz
      rw [← hcz]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton w))
    · exfalso; apply hbnot01
      rw [hc2, one_smul] at hcz
      have hbeq : b = z + c₁ • w + a := by
        ext i
        have hi : c₁ * w i + (a i + b i) = z i := congrFun hcz i
        have hs1 := z2_add_self (c₁ * w i)
        have hs2 := z2_add_self (a i)
        calc b i = 0 + 0 + b i := by simp
          _ = (c₁ * w i + c₁ * w i) + (a i + a i) + b i := by rw [hs1, hs2]
          _ = (c₁ * w i + (a i + b i)) + c₁ * w i + a i := by ring
          _ = z i + c₁ * w i + a i := by rw [hi]
      rw [hbeq]
      exact V01.add_mem (V01.add_mem hz.1 (V01.smul_mem c₁ hw.1)) haV01
  set U0 := (colSp (R 0)).map (piBot n)
  set U1 := (colSp (R 1)).map (piBot n)
  have hU0 : U0 ≤ Submodule.span F {w} := by
    refine le_trans ?_ hinf01_02
    exact le_inf
      (by rw [show V01 = U0 ⊔ U1 from hMap01]; exact le_sup_left)
      (by rw [show V02 = U0 ⊔ (colSp (R 2)).map (piBot n) from hMap02]; exact le_sup_left)
  have hU1 : U1 ≤ Submodule.span F {w} := by
    refine le_trans ?_ hinf01_12
    exact le_inf
      (by rw [show V01 = U0 ⊔ U1 from hMap01]; exact le_sup_right)
      (by rw [show V12 = U1 ⊔ (colSp (R 2)).map (piBot n) from hMap12]; exact le_sup_left)
  have hV01_le : V01 ≤ Submodule.span F {w} := by
    rw [show V01 = U0 ⊔ U1 from hMap01]
    exact sup_le hU0 hU1
  have hfr := Submodule.finrank_mono hV01_le
  rw [finrank_span_singleton hw0] at hfr
  change K01.rank ≤ 1 at hfr
  omega

lemma pow_mono_sub {a b : ℕ} (h : a ≤ b) : b - a + 2 ^ (a + 1) ≤ 2 ^ (b + 1) := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
    have hpow : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
    omega

lemma finrank_fun_F {ι : Type*} [Fintype ι] :
    Module.finrank F (ι → F) = Fintype.card ι := by
  simp

lemma part2 {n : ℕ} (P : Submodule F (Matrix (Fin n) (Fin n) F))
    (hP : ∀ K ∈ P, Alt K)
    (t : ℕ) (R : Fin t → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (hRk : ∀ i, (R i).rank ≤ 2)
    (hWS : WSub P ≤ Submodule.span F (Set.range R)) :
    let D := Module.finrank F (WSub P)
    let p := Module.finrank F P
    let h := t - D
    D ≤ t ∧ p + h + 2 ≤ 2 ^ (h + 1) := by
  classical
  set W := WSub P
  set S := Submodule.span F (Set.range R)
  set D := Module.finrank F W
  set p := Module.finrank F P
  have hS_le : Module.finrank F S ≤ t := by
    have hrg : LinearMap.range (Fintype.linearCombination F R) = S :=
      Fintype.range_linearCombination F R
    rw [← hrg]
    have h1 := LinearMap.finrank_range_le (Fintype.linearCombination F R)
    rw [finrank_fun_F, Fintype.card_fin] at h1
    exact h1
  have hDt : D ≤ t := (Submodule.finrank_mono hWS).trans hS_le
  refine ⟨hDt, ?_⟩
  set Q := S.map W.mkQ
  set s := Module.finrank F Q
  have hs_le : s ≤ t - D := by
    let qS : S →ₗ[F] (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F ⧸ W) := W.mkQ.domRestrict S
    have hrm := LinearMap.finrank_range_add_finrank_ker qS
    have hrg : LinearMap.range qS = Q := by
      ext y; simp [qS, Q, Submodule.mem_map]
    have hker : Module.finrank F (LinearMap.ker qS) = D := by
      let e : W →ₗ[F] LinearMap.ker qS :=
        { toFun := fun x => ⟨⟨x.1, hWS x.2⟩, by
            change W.mkQ x.1 = 0
            exact (Submodule.Quotient.mk_eq_zero W).mpr x.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have he_bij : Function.Bijective e := by
        constructor
        · intro x y h; exact Subtype.ext (congrArg (fun z => z.1.1) h)
        · rintro ⟨⟨x, hxS⟩, hxk⟩
          have hxW : x ∈ W := (Submodule.Quotient.mk_eq_zero W).mp hxk
          exact ⟨⟨x, hxW⟩, rfl⟩
      exact (LinearEquiv.ofBijective e he_bij).finrank_eq.symm
    rw [hrg, hker] at hrm
    omega
  let qR : Fin t → (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F ⧸ W) := fun i => W.mkQ (R i)
  have hqR_mem : ∀ i, qR i ∈ Q := fun i =>
    ⟨R i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  let Cplus : Finset (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F ⧸ W) :=
    (Finset.univ.image qR).erase 0
  set m := Cplus.card
  have hm_bound : m + 1 ≤ 2 ^ s := by
    have h0not : (0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F ⧸ W) ∉ Cplus :=
      Finset.notMem_erase _ _
    let C0 := insert (0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F ⧸ W) Cplus
    have hC0_card : C0.card = m + 1 := Finset.card_insert_of_notMem h0not
    have hC0_mem : ∀ c ∈ C0, c ∈ Q := by
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc'
      · exact Q.zero_mem
      · have hci := Finset.mem_of_mem_erase hc'
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hci
        exact hqR_mem i
    have hcard_le : C0.card ≤ Fintype.card Q := by
      let f : C0 → Q := fun c => ⟨c.1, hC0_mem c.1 c.2⟩
      have hfinj : Function.Injective f := fun a b h =>
        Subtype.ext (congrArg (fun z : Q => z.1) h)
      simpa [Fintype.card_coe] using Fintype.card_le_of_injective f hfinj
    have hQcard : Fintype.card Q = 2 ^ s := by
      have h := Module.card_eq_pow_finrank (K := F) (V := Q)
      rw [ZMod.card] at h
      exact h
    omega
  have hrep_ex : ∀ c : Cplus, ∃ i : Fin t, qR i = c.1 := by
    intro c
    have hc := Finset.mem_of_mem_erase c.2
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hc
    exact ⟨i, hi⟩
  choose rep hrep using hrep_ex
  have hd_ex : ∀ c : Cplus, ∃ d : Matrix (Fin n) (Fin n) F,
      ∀ i : Fin t, qR i = c.1 →
        crossLin n (R i) + crossLin n (R (rep c)) ∈ Submodule.span F {d} := by
    intro c
    by_cases hall : ∀ i : Fin t, qR i = c.1 → crossLin n (R i) = crossLin n (R (rep c))
    · refine ⟨0, fun i hi => ?_⟩
      rw [hall i hi, mat_add_self]
      exact Submodule.zero_mem _
    · push Not at hall
      obtain ⟨i₁, hi₁, hne₁⟩ := hall
      refine ⟨crossLin n (R i₁) + crossLin n (R (rep c)), fun i hi => ?_⟩
      let R3 : Fin 3 → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := ![R (rep c), R i₁, R i]
      have hR3k : ∀ a : Fin 3, (R3 a).rank ≤ 2 := by
        intro a; fin_cases a <;> exact hRk _
      have hR3q : ∀ a : Fin 3, W.mkQ (R3 a) = c.1 := by
        intro a; fin_cases a
        · exact hrep c
        · exact hi₁
        · exact hi
      have hR3W : ∀ a b : Fin 3, R3 a + R3 b ∈ W := by
        intro a b
        rw [← Submodule.Quotient.mk_eq_zero W]
        change W.mkQ (R3 a + R3 b) = 0
        rw [map_add, hR3q a, hR3q b]
        have : c.1 + c.1 = (1 + 1 : F) • c.1 := by rw [add_smul, one_smul]
        rw [this]
        have h11 : (1 + 1 : F) = 0 := rfl
        rw [h11, zero_smul]
      obtain ⟨a, b, hab, hceq⟩ := part1 P hP R3 hR3k hR3W
      have hcases : crossLin n (R i) = crossLin n (R (rep c)) ∨
          crossLin n (R i) = crossLin n (R i₁) := by
        fin_cases a <;> fin_cases b <;> simp_all [R3]
      rcases hcases with heq | heq
      · rw [heq, mat_add_self]; exact Submodule.zero_mem _
      · rw [heq]; exact Submodule.subset_span (Set.mem_singleton _)
  choose d hd using hd_ex
  let Φ : (Cplus → F) →ₗ[F] Q :=
    { toFun := fun lam => ⟨∑ c : Cplus, lam c • c.1, by
        apply Q.sum_mem
        intro c _
        have hc := Finset.mem_of_mem_erase c.2
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hc
        exact Q.smul_mem _ (hi ▸ hqR_mem i)⟩
      map_add' := fun x y => by
        apply Subtype.ext
        change ∑ c : Cplus, (x c + y c) • c.1 =
          (∑ c : Cplus, x c • c.1) + ∑ c : Cplus, y c • c.1
        simp only [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        apply Subtype.ext
        change ∑ c : Cplus, (r * x c) • c.1 = r • ∑ c : Cplus, x c • c.1
        simp only [mul_smul, Finset.smul_sum] }
  let Ψ : (Cplus → F) →ₗ[F] Matrix (Fin n) (Fin n) F :=
    { toFun := fun lam => ∑ c : Cplus, lam c • crossLin n (R (rep c))
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r x => by simp [mul_smul, Finset.smul_sum] }
  have hΦ_surj : LinearMap.range Φ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hyQ⟩ _
    obtain ⟨x, hxS, rfl⟩ := hyQ
    have hxrg : x ∈ LinearMap.range (Fintype.linearCombination F R) := by
      rwa [Fintype.range_linearCombination]
    obtain ⟨α, rfl⟩ := hxrg
    let lam : Cplus → F := fun c => ∑ i ∈ Finset.univ.filter (fun i => qR i = c.1), α i
    refine ⟨lam, ?_⟩
    apply Subtype.ext
    change ∑ c : Cplus, lam c • c.1 = W.mkQ (∑ i : Fin t, α i • R i)
    rw [map_sum]
    simp only [map_smul]
    change ∑ c : Cplus, (∑ i ∈ Finset.univ.filter (fun i => qR i = c.1), α i) • c.1 =
      ∑ i : Fin t, α i • qR i
    have hfib := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (Fin t))) (t := Finset.univ.image qR) (g := qR)
      (f := fun i => α i • qR i) (fun i _ => Finset.mem_image_of_mem qR (Finset.mem_univ i))
    rw [← hfib]
    have hsum_er : ∑ c ∈ Finset.univ.image qR, ∑ i ∈ Finset.univ.filter (fun i => qR i = c), α i • qR i =
        ∑ c ∈ Cplus, ∑ i ∈ Finset.univ.filter (fun i => qR i = c), α i • qR i := by
      by_cases h0 : (0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F ⧸ W) ∈ Finset.univ.image qR
      · rw [← Finset.add_sum_erase _ _ h0]
        have hz : ∑ i ∈ Finset.univ.filter (fun i => qR i = 0), α i • qR i = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          rw [(Finset.mem_filter.mp hi).2, smul_zero]
        rw [hz, zero_add]
      · have hCeq : Cplus = Finset.univ.image qR := Finset.erase_eq_of_notMem h0
        rw [hCeq]
    rw [hsum_er, ← Finset.sum_coe_sort Cplus]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  have hkerΦ : Module.finrank F (LinearMap.ker Φ) + s = m := by
    have hrm := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hΦ_surj, finrank_top, finrank_fun_F, Fintype.card_coe] at hrm
    simpa [s, m, add_comm] using hrm
  let L₁ : Submodule F (Matrix (Fin n) (Fin n) F) := (LinearMap.ker Φ).map Ψ
  let L₂ : Submodule F (Matrix (Fin n) (Fin n) F) := Submodule.span F (Set.range d)
  have hP_le : P ≤ L₁ ⊔ L₂ := by
    intro K hKP
    let X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := Matrix.fromBlocks 0 K K 0
    have hXW : X ∈ W := ⟨0, K, Alt.zero, hKP, rfl⟩
    have hXS : X ∈ LinearMap.range (Fintype.linearCombination F R) := by
      rw [Fintype.range_linearCombination]; exact hWS hXW
    obtain ⟨α, hα⟩ := hXS
    have hXsum : X = ∑ i : Fin t, α i • R i := hα.symm
    let lam : Cplus → F := fun c => ∑ i ∈ Finset.univ.filter (fun i => qR i = c.1), α i
    have hlam_ker : lam ∈ LinearMap.ker Φ := by
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      change ∑ c : Cplus, lam c • c.1 = 0
      have hW0 : W.mkQ X = 0 := (Submodule.Quotient.mk_eq_zero W).mpr hXW
      rw [hXsum, map_sum] at hW0
      simp only [map_smul] at hW0
      change ∑ i : Fin t, α i • qR i = 0 at hW0
      rw [← hW0]
      have hfib := Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset (Fin t))) (t := Finset.univ.image qR) (g := qR)
        (f := fun i => α i • qR i) (fun i _ => Finset.mem_image_of_mem qR (Finset.mem_univ i))
      rw [← hfib]
      have hsum_er : ∑ c ∈ Finset.univ.image qR, ∑ i ∈ Finset.univ.filter (fun i => qR i = c), α i • qR i =
          ∑ c ∈ Cplus, ∑ i ∈ Finset.univ.filter (fun i => qR i = c), α i • qR i := by
        by_cases h0 : (0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F ⧸ W) ∈ Finset.univ.image qR
        · rw [← Finset.add_sum_erase _ _ h0]
          have hz : ∑ i ∈ Finset.univ.filter (fun i => qR i = 0), α i • qR i = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            rw [(Finset.mem_filter.mp hi).2, smul_zero]
          rw [hz, zero_add]
        · have hCeq : Cplus = Finset.univ.image qR := Finset.erase_eq_of_notMem h0
          rw [hCeq]
      rw [hsum_er, ← Finset.sum_coe_sort Cplus]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    have hK_eq : K = Ψ lam +
        ∑ c : Cplus, ∑ i ∈ Finset.univ.filter (fun i => qR i = c.1),
          α i • (crossLin n (R i) + crossLin n (R (rep c))) := by
      have hKc : K = ∑ i : Fin t, α i • crossLin n (R i) := by
        have hc := congrArg (crossLin n) hXsum
        rw [crossLin_fromBlocks, map_sum] at hc
        simpa only [map_smul] using hc
      rw [hKc]
      have hfib := Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset (Fin t))) (t := Finset.univ.image qR) (g := qR)
        (f := fun i => α i • crossLin n (R i))
        (fun i _ => Finset.mem_image_of_mem qR (Finset.mem_univ i))
      rw [← hfib]
      have hsum_er : ∑ c ∈ Finset.univ.image qR,
            ∑ i ∈ Finset.univ.filter (fun i => qR i = c), α i • crossLin n (R i) =
          ∑ c ∈ Cplus,
            ∑ i ∈ Finset.univ.filter (fun i => qR i = c), α i • crossLin n (R i) := by
        by_cases h0 : (0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F ⧸ W) ∈ Finset.univ.image qR
        · rw [← Finset.add_sum_erase _ _ h0]
          have hz : ∑ i ∈ Finset.univ.filter (fun i => qR i = 0), α i • crossLin n (R i) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have hi0 : W.mkQ (R i) = 0 := (Finset.mem_filter.mp hi).2
            have hiW : R i ∈ W := (Submodule.Quotient.mk_eq_zero W).mp hi0
            rw [cross_eq_zero_of_mem_W_rank_le_two hP hiW (hRk i), smul_zero]
          rw [hz, zero_add]
        · have hCeq : Cplus = Finset.univ.image qR := Finset.erase_eq_of_notMem h0
          rw [hCeq]
      rw [hsum_er, ← Finset.sum_coe_sort Cplus]
      change _ = (∑ c : Cplus, lam c • crossLin n (R (rep c))) + _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c _
      change ∑ i ∈ Finset.univ.filter (fun i => qR i = c.1), α i • crossLin n (R i) =
        (∑ i ∈ Finset.univ.filter (fun i => qR i = c.1), α i) • crossLin n (R (rep c)) +
        ∑ i ∈ Finset.univ.filter (fun i => qR i = c.1),
          α i • (crossLin n (R i) + crossLin n (R (rep c)))
      rw [Finset.sum_smul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ext a b
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      have hs := z2_add_self (α i * crossLin n (R (rep c)) a b)
      calc α i * crossLin n (R i) a b
          = 0 + α i * crossLin n (R i) a b := by rw [zero_add]
        _ = (α i * crossLin n (R (rep c)) a b + α i * crossLin n (R (rep c)) a b) +
            α i * crossLin n (R i) a b := by rw [hs]
        _ = _ := by ring
    rw [hK_eq]
    apply Submodule.add_mem_sup
    · exact ⟨lam, hlam_ker, rfl⟩
    · apply L₂.sum_mem
      intro c _
      apply L₂.sum_mem
      intro i hi
      apply L₂.smul_mem
      have hmem := hd c i (Finset.mem_filter.mp hi).2
      have hsub : Submodule.span F {d c} ≤ L₂ :=
        Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨c, rfl⟩)
      exact hsub hmem
  have hL1 : Module.finrank F L₁ ≤ Module.finrank F (LinearMap.ker Φ) :=
    Submodule.finrank_map_le Ψ (LinearMap.ker Φ)
  have hL2 : Module.finrank F L₂ ≤ m := by
    have hrg : LinearMap.range (Fintype.linearCombination F d) = L₂ :=
      Fintype.range_linearCombination F d
    rw [← hrg]
    have h1 := LinearMap.finrank_range_le (Fintype.linearCombination F d)
    rw [finrank_fun_F, Fintype.card_coe] at h1
    exact h1
  have hp_le : p ≤ Module.finrank F L₁ + Module.finrank F L₂ :=
    (Submodule.finrank_mono hP_le).trans (finrank_sup_le' L₁ L₂)
  have hpow_s : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
  have hps : p + s + 2 ≤ 2 ^ (s + 1) := by omega
  have hmono := pow_mono_sub hs_le
  omega

end PEqualNP.Outside.L_lib_987_aux

theorem PEqualNP.Outside.L_lib_987 : (let F := ZMod 2
∀ (n : ℕ) (P : Submodule F (Matrix (Fin n) (Fin n) F)),
  let M := Matrix (Fin n) (Fin n) F
  let J := Fin n ⊕ Fin n
  let Big := Matrix J J F
  let alt := fun (A : M) => A.transpose = A ∧ ∀ i, A i i = 0
  let W := Submodule.span F {X : Big | ∃ A K : M,
    alt A ∧ K ∈ P ∧ X = Matrix.fromBlocks A K K (0 : M)}
  let cross := fun (X : Big) => (fun (i j : Fin n) => X (Sum.inl i) (Sum.inr j) : M)
  let p := Module.finrank F P
  let D := Module.finrank F W
  (∀ K ∈ P, alt K) →
    (∀ R : Fin 3 → Big, (∀ i, (R i).rank ≤ 2) → (∀ i j, R i + R j ∈ W) →
      ∃ i j : Fin 3, i ≠ j ∧ cross (R i) = cross (R j)) ∧
    ∀ (t : ℕ) (R : Fin t → Big), (∀ i, (R i).rank ≤ 2) →
      W ≤ Submodule.span F (Set.range R) →
      let h := t-D
      D ≤ t ∧ p+h+2 ≤ 2^(h+1)) := by
  dsimp only
  intro n P hP
  have hWeq : Submodule.span (ZMod 2)
      {X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) |
        ∃ A K : Matrix (Fin n) (Fin n) (ZMod 2),
          (A.transpose = A ∧ ∀ i, A i i = 0) ∧ K ∈ P ∧ X = Matrix.fromBlocks A K K 0} =
      PEqualNP.Outside.L_lib_987_aux.WSub P :=
    PEqualNP.Outside.L_lib_987_aux.WSub_eq_span P
  rw [hWeq]
  exact ⟨fun R hRk hRW => PEqualNP.Outside.L_lib_987_aux.part1 P hP R hRk hRW,
    fun t R hRk hWS => PEqualNP.Outside.L_lib_987_aux.part2 P hP t R hRk hWS⟩
