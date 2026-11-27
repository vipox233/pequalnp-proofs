import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_559

noncomputable def dot {α : Type*} [Fintype α] (x y : α → ℝ) : ℝ :=
  ∑ i : α, x i * y i

lemma dot_comm {α : Type*} [Fintype α] (x y : α → ℝ) : dot x y = dot y x :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

lemma dot_zero_right {α : Type*} [Fintype α] (x : α → ℝ) : dot x 0 = 0 := by
  simp [dot]

lemma dot_sub_left {α : Type*} [Fintype α] (x y z : α → ℝ) :
    dot (x - y) z = dot x z - dot y z := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

lemma dot_smul_left {α : Type*} [Fintype α] (c : ℝ) (x y : α → ℝ) :
    dot (c • x) y = c * dot x y := by
  simp [dot, mul_assoc, Finset.mul_sum]

lemma dot_smul_right {α : Type*} [Fintype α] (c : ℝ) (x y : α → ℝ) :
    dot x (c • y) = c * dot x y := by
  rw [dot_comm, dot_smul_left, dot_comm]

lemma dot_sum_left {α ι : Type*} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) (y : α → ℝ) :
    dot (∑ a ∈ s, f a) y = ∑ a ∈ s, dot (f a) y := by
  simp only [dot, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

lemma dot_sum_right {α ι : Type*} [Fintype α] (s : Finset ι) (x : α → ℝ) (f : ι → α → ℝ) :
    dot x (∑ a ∈ s, f a) = ∑ a ∈ s, dot x (f a) := by
  rw [dot_comm, dot_sum_left]
  exact Finset.sum_congr rfl fun _ _ => dot_comm _ _

lemma dot_self_nonneg {α : Type*} [Fintype α] (x : α → ℝ) : 0 ≤ dot x x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

lemma eq_zero_of_dot_self_eq_zero {α : Type*} [Fintype α] {x : α → ℝ} (h : dot x x = 0) :
    x = 0 := by
  funext i
  have hterm : x i * x i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (x j))).mp h i (Finset.mem_univ i)
  exact mul_self_eq_zero.mp hterm

lemma gram_schmidt {α : Type*} [Fintype α] :
    ∀ (m : ℕ) (v : Fin m → α → ℝ),
      ∃ u : Fin m → α → ℝ,
        (∀ a b : Fin m, a ≠ b → dot (u a) (u b) = 0) ∧
        (∀ c : Fin m → ℝ, ∃ d : Fin m → ℝ, ∑ a, c a • v a = ∑ a, d a • u a)
  | 0, _ => ⟨Fin.elim0, fun a => a.elim0, fun _ => ⟨Fin.elim0, by simp⟩⟩
  | m + 1, v => by
    obtain ⟨u', hu'_orth, hu'_span⟩ := gram_schmidt m (fun a => v a.castSucc)
    let coeff : Fin m → ℝ := fun b => dot (v (Fin.last m)) (u' b) / dot (u' b) (u' b)
    let uLast : α → ℝ := v (Fin.last m) - ∑ b : Fin m, coeff b • u' b
    let u : Fin (m + 1) → α → ℝ := Fin.snoc u' uLast
    have horth_last : ∀ b : Fin m, dot uLast (u' b) = 0 := by
      intro b
      change dot (v (Fin.last m) - ∑ c : Fin m, coeff c • u' c) (u' b) = 0
      rw [dot_sub_left, dot_sum_left]
      simp_rw [dot_smul_left]
      rw [Finset.sum_eq_single b]
      · by_cases h0 : dot (u' b) (u' b) = 0
        · have hub : u' b = 0 := eq_zero_of_dot_self_eq_zero h0
          simp [hub, dot_zero_right]
        · simp only [coeff, div_mul_cancel₀ _ h0, sub_self]
      · intro c _ hcb
        rw [hu'_orth c b hcb, mul_zero]
      · intro hb
        exact absurd (Finset.mem_univ b) hb
    refine ⟨u, ?_, ?_⟩
    · intro a b
      refine Fin.lastCases ?_ (fun a' => ?_) a
      · refine Fin.lastCases ?_ (fun b' => ?_) b
        · intro hab
          exact absurd rfl hab
        · intro _
          simpa [u] using horth_last b'
      · refine Fin.lastCases ?_ (fun b' => ?_) b
        · intro _
          rw [dot_comm]
          simpa [u] using horth_last a'
        · intro hab
          have hne : a' ≠ b' := fun h => hab (congrArg Fin.castSucc h)
          simpa [u] using hu'_orth a' b' hne
    · intro c
      obtain ⟨d', hd'⟩ := hu'_span (fun a => c a.castSucc)
      refine ⟨Fin.snoc (fun b => d' b + c (Fin.last m) * coeff b) (c (Fin.last m)), ?_⟩
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [u, Fin.snoc_castSucc, Fin.snoc_last]
      rw [hd']
      have hvlast : v (Fin.last m) = uLast + ∑ b : Fin m, coeff b • u' b :=
        (sub_add_cancel _ _).symm
      rw [hvlast, smul_add, Finset.smul_sum]
      simp_rw [smul_smul, add_smul, Finset.sum_add_distrib]
      abel

lemma dot_self_eq_sum_proj {α : Type*} [Fintype α] {k : ℕ}
    (u : Fin k → α → ℝ) (horth : ∀ a b : Fin k, a ≠ b → dot (u a) (u b) = 0)
    (d : Fin k → ℝ) :
    let w := ∑ a, d a • u a
    dot w w = ∑ a : Fin k, (dot w (u a)) ^ 2 / dot (u a) (u a) := by
  intro w
  have hcoeff : ∀ b : Fin k, dot w (u b) = d b * dot (u b) (u b) := by
    intro b
    simp only [w, dot_sum_left, dot_smul_left]
    rw [Finset.sum_eq_single b]
    · intro a _ hab
      rw [horth a b hab, mul_zero]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  calc
    dot w w = dot w (∑ a, d a • u a) := rfl
    _ = ∑ a : Fin k, d a * dot w (u a) := by
      simp only [dot_sum_right, dot_smul_right]
    _ = ∑ a : Fin k, (dot w (u a)) ^ 2 / dot (u a) (u a) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hcoeff a]
      by_cases h0 : dot (u a) (u a) = 0
      · simp [h0]
      · rw [show (d a * dot (u a) (u a)) ^ 2 = (d a * (d a * dot (u a) (u a))) * dot (u a) (u a) by ring,
          mul_div_cancel_right₀ _ h0]

lemma hadamard_col_bound {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hH_orth : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0)
    (S T : Finset (Fin n)) (x : S → ℝ) :
    ∑ j : T, (∑ i : S, x i * H i.1 j.1) ^ 2 ≤ (n : ℝ) * dot x x := by
  have hsub : ∑ j : T, (∑ i : S, x i * H i.1 j.1) ^ 2 ≤
      ∑ j : Fin n, (∑ i : S, x i * H i.1 j) ^ 2 := by
    rw [Finset.sum_coe_sort T (fun j => (∑ i : S, x i * H i.1 j) ^ 2)]
    exact Finset.sum_le_univ_sum_of_nonneg fun j => sq_nonneg _
  have heq : ∑ j : Fin n, (∑ i : S, x i * H i.1 j) ^ 2 = (n : ℝ) * dot x x := by
    calc
      ∑ j : Fin n, (∑ i : S, x i * H i.1 j) ^ 2
          = ∑ j : Fin n, ∑ i₁ : S, ∑ i₂ : S, (x i₁ * x i₂) * (H i₁.1 j * H i₂.1 j) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [sq, Finset.sum_mul_sum]
            refine Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun i₂ _ => by ring
      _ = ∑ i₁ : S, ∑ j : Fin n, ∑ i₂ : S, (x i₁ * x i₂) * (H i₁.1 j * H i₂.1 j) :=
            Finset.sum_comm
      _ = ∑ i₁ : S, ∑ i₂ : S, ∑ j : Fin n, (x i₁ * x i₂) * (H i₁.1 j * H i₂.1 j) := by
            refine Finset.sum_congr rfl fun i₁ _ => Finset.sum_comm
      _ = ∑ i₁ : S, ∑ i₂ : S, (x i₁ * x i₂) * (∑ j : Fin n, H i₁.1 j * H i₂.1 j) := by
            refine Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun i₂ _ =>
              (Finset.mul_sum _ _ _).symm
      _ = ∑ i₁ : S, ∑ i₂ : S, (x i₁ * x i₂) * (if i₁ = i₂ then (n : ℝ) else 0) := by
            refine Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun i₂ _ => ?_
            rw [hH_orth i₁.1 i₂.1]
            by_cases h : i₁ = i₂ <;> simp [h]
      _ = ∑ i₁ : S, (x i₁ * x i₁) * (n : ℝ) := by
            refine Finset.sum_congr rfl fun i₁ _ => ?_
            simp
      _ = (n : ℝ) * dot x x := by
            rw [dot, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i₁ _ => by ring
  exact hsub.trans_eq heq

lemma submatrix_rank_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (S T : Finset (Fin n)) :
    Module.finrank ℝ
      (LinearMap.range (A.submatrix (Subtype.val : S → Fin n) (Subtype.val : T → Fin n)).mulVecLin) ≤
      A.rank := by
  let extT : (T → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun v j => if hj : j ∈ T then v ⟨j, hj⟩ else 0
      map_add' := fun v w => by ext j; by_cases hj : j ∈ T <;> simp [hj]
      map_smul' := fun c v => by ext j; by_cases hj : j ∈ T <;> simp [hj] }
  let resS : (Fin n → ℝ) →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun w i => w i.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hcomp :
      (A.submatrix (Subtype.val : S → Fin n) (Subtype.val : T → Fin n)).mulVecLin =
        resS.comp (A.mulVecLin.comp extT) := by
    apply LinearMap.ext
    intro v
    funext i
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Matrix.submatrix_apply, resS, extT, LinearMap.coe_mk, AddHom.coe_mk]
    have hsum :
        (∑ j : Fin n, A i.1 j * (if hj : j ∈ T then v ⟨j, hj⟩ else 0)) =
          ∑ j ∈ T, A i.1 j * (if hj : j ∈ T then v ⟨j, hj⟩ else 0) := by
      symm
      refine Finset.sum_subset (Finset.subset_univ T) fun j _ hj => ?_
      simp [hj]
    rw [hsum, ← Finset.sum_coe_sort T (fun j => A i.1 j * (if hj : j ∈ T then v ⟨j, hj⟩ else 0))]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [j.2]
  have hrange :
      LinearMap.range
          (A.submatrix (Subtype.val : S → Fin n) (Subtype.val : T → Fin n)).mulVecLin ≤
        Submodule.map resS (LinearMap.range A.mulVecLin) := by
    rw [hcomp]
    rintro y ⟨v, rfl⟩
    exact ⟨A.mulVecLin (extT v), ⟨extT v, rfl⟩, rfl⟩
  exact (Submodule.finrank_mono hrange).trans (Submodule.finrank_map_le resS _)

lemma hadamard_submatrix_rank_bound {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hH_pm : ∀ i j, H i j = 1 ∨ H i j = -1)
    (hH_orth : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0)
    (S T : Finset (Fin n)) :
    T.card * S.card ≤
      Module.finrank ℝ
        (LinearMap.range (H.submatrix (Subtype.val : S → Fin n) (Subtype.val : T → Fin n)).mulVecLin) * n := by
  let M : Matrix S T ℝ := H.submatrix Subtype.val Subtype.val
  let W : Submodule ℝ (S → ℝ) := LinearMap.range M.mulVecLin
  let k : ℕ := Module.finrank ℝ W
  let b : Module.Basis (Fin k) ℝ W := Module.finBasis ℝ W
  let v : Fin k → S → ℝ := fun a => (b a : S → ℝ)
  obtain ⟨u, hu_orth, hu_span⟩ := gram_schmidt k v
  let col : T → S → ℝ := fun j i => H i.1 j.1
  have hcol_mem : ∀ j : T, col j ∈ W := by
    intro j
    refine ⟨Pi.single j 1, ?_⟩
    funext i
    simp only [M, col, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      simp [Pi.single_eq_of_ne hj']
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hcol_norm : ∀ j : T, dot (col j) (col j) = (S.card : ℝ) := by
    intro j
    have hsq : ∀ i : S, H i.1 j.1 * H i.1 j.1 = 1 := fun i => by
      rcases hH_pm i.1 j.1 with h | h <;> simp [h]
    simp [dot, col, hsq]
  have hcol_proj : ∀ j : T,
      (S.card : ℝ) = ∑ a : Fin k, (dot (col j) (u a)) ^ 2 / dot (u a) (u a) := by
    intro j
    have hrepr : col j = ∑ a : Fin k, (b.repr ⟨col j, hcol_mem j⟩ a) • v a := by
      calc
        col j = W.subtype ⟨col j, hcol_mem j⟩ := rfl
        _ = W.subtype (∑ a : Fin k, (b.repr ⟨col j, hcol_mem j⟩ a) • b a) := by
              rw [b.sum_repr]
        _ = ∑ a : Fin k, (b.repr ⟨col j, hcol_mem j⟩ a) • v a := by
              simp only [map_sum, map_smul, Submodule.coe_subtype, v]
    obtain ⟨d, hd⟩ := hu_span (fun a => b.repr ⟨col j, hcol_mem j⟩ a)
    have hcol_eq : col j = ∑ a : Fin k, d a • u a := hrepr.trans hd
    rw [← hcol_norm j, hcol_eq]
    exact dot_self_eq_sum_proj u hu_orth d
  have hreal : (T.card : ℝ) * (S.card : ℝ) ≤ (k : ℝ) * (n : ℝ) := by
    calc
      (T.card : ℝ) * (S.card : ℝ)
          = ∑ _j : T, (S.card : ℝ) := by simp
      _ = ∑ j : T, ∑ a : Fin k, (dot (col j) (u a)) ^ 2 / dot (u a) (u a) :=
            Finset.sum_congr rfl fun j _ => hcol_proj j
      _ = ∑ a : Fin k, ∑ j : T, (dot (col j) (u a)) ^ 2 / dot (u a) (u a) :=
            Finset.sum_comm
      _ = ∑ a : Fin k, (∑ j : T, (dot (u a) (col j)) ^ 2) / dot (u a) (u a) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            simp_rw [div_eq_mul_inv, ← Finset.sum_mul, dot_comm]
      _ ≤ ∑ _a : Fin k, (n : ℝ) := by
            refine Finset.sum_le_sum fun a _ => ?_
            by_cases h0 : dot (u a) (u a) = 0
            · rw [h0, div_zero]
              exact Nat.cast_nonneg n
            · have hpos : 0 < dot (u a) (u a) :=
                lt_of_le_of_ne (dot_self_nonneg (u a)) (Ne.symm h0)
              rw [div_le_iff₀ hpos]
              exact hadamard_col_bound H hH_orth S T (u a)
      _ = (k : ℝ) * (n : ℝ) := by simp
  exact_mod_cast hreal

lemma exists_subset_sum_le {α : Type*} [DecidableEq α] (f : α → ℕ) :
    ∀ (d : ℕ) (U : Finset α) (m : ℕ), U.card = m + d →
      ∃ S ⊆ U, S.card = m ∧ U.card * ∑ i ∈ S, f i ≤ m * ∑ i ∈ U, f i
  | 0, U, m, hcard => ⟨U, Finset.Subset.refl U, by simpa using hcard, by simp [hcard]⟩
  | d + 1, U, m, hcard => by
    have hne : U.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hxU, hmax⟩ := Finset.exists_max_image U f hne
    let U' : Finset α := U.erase x
    have hU'card : U'.card = m + d := by
      have h1 : U'.card = U.card - 1 := Finset.card_erase_of_mem hxU
      omega
    obtain ⟨S, hSU', hScard, hSbound⟩ := exists_subset_sum_le f d U' m hU'card
    refine ⟨S, hSU'.trans (Finset.erase_subset x U), hScard, ?_⟩
    by_cases hm : m = 0
    · subst hm
      have hSempty : S = ∅ := Finset.card_eq_zero.mp hScard
      simp [hSempty]
    · have hU'pos : 0 < U'.card := by omega
      have hsumU : ∑ i ∈ U, f i = f x + ∑ i ∈ U', f i :=
        (Finset.add_sum_erase U f hxU).symm
      have hsumU'_le : ∑ i ∈ U', f i ≤ U'.card * f x := by
        calc
          ∑ i ∈ U', f i ≤ ∑ _i ∈ U', f x :=
            Finset.sum_le_sum fun y hy => hmax y (Finset.mem_of_mem_erase hy)
          _ = U'.card * f x := by simp
      have havg : U.card * ∑ i ∈ U', f i ≤ U'.card * ∑ i ∈ U, f i := by
        have hstep : U.card = U'.card + 1 := by omega
        rw [hstep, hsumU]
        calc
          (U'.card + 1) * ∑ i ∈ U', f i
              = U'.card * ∑ i ∈ U', f i + ∑ i ∈ U', f i := by ring
          _ ≤ U'.card * ∑ i ∈ U', f i + U'.card * f x := Nat.add_le_add_left hsumU'_le _
          _ = U'.card * (f x + ∑ i ∈ U', f i) := by ring
      have hmul : U'.card * (U.card * ∑ i ∈ S, f i) ≤ U'.card * (m * ∑ i ∈ U, f i) := by
        calc
          U'.card * (U.card * ∑ i ∈ S, f i)
              = U.card * (U'.card * ∑ i ∈ S, f i) := by ring
          _ ≤ U.card * (m * ∑ i ∈ U', f i) := Nat.mul_le_mul_left U.card hSbound
          _ = m * (U.card * ∑ i ∈ U', f i) := by ring
          _ ≤ m * (U'.card * ∑ i ∈ U, f i) := Nat.mul_le_mul_left m havg
          _ = U'.card * (m * ∑ i ∈ U, f i) := by ring
      exact Nat.le_of_mul_le_mul_left hmul hU'pos

end PEqualNP.Outside.L_lib_559

theorem PEqualNP.Outside.L_lib_559 : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ), 0 < n →
  (∀ i j, H i j = 1 ∨ H i j = -1) →
  (∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) →
  ∀ (r : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), 0 < r → 2*r ≤ n → A.rank ≤ r →
    let changes := (Finset.univ : Finset (Fin n × Fin n)).filter (fun p => H p.1 p.2 ≠ A p.1 p.2)
    n^2 ≤ 4*r*changes.card := by
  classical
  intro n H hn hH_pm hH_orth r A hr h2r hrank changes
  let rowChanges : Fin n → Finset (Fin n) :=
    fun i => (Finset.univ : Finset (Fin n)).filter (fun j => H i j ≠ A i j)
  have hsum_changes : ∑ i : Fin n, (rowChanges i).card = changes.card := by
    have h1 : changes.card =
        ∑ p : Fin n × Fin n, if H p.1 p.2 ≠ A p.1 p.2 then 1 else 0 := by
      simp [changes, Finset.card_filter]
    have h2 : ∀ i : Fin n, (rowChanges i).card =
        ∑ j : Fin n, if H i j ≠ A i j then 1 else 0 := fun i => by
      simp [rowChanges, Finset.card_filter]
    rw [h1, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => h2 i
  obtain ⟨S, _, hScard, hSbound⟩ :=
    PEqualNP.Outside.L_lib_559.exists_subset_sum_le
      (fun i => (rowChanges i).card) (n - 2 * r) (Finset.univ : Finset (Fin n)) (2 * r)
      (by simp; omega)
  have hSbound' : n * ∑ i ∈ S, (rowChanges i).card ≤ 2 * r * changes.card := by
    simpa [hsum_changes] using hSbound
  let badCols : Finset (Fin n) := S.biUnion rowChanges
  let T : Finset (Fin n) := badColsᶜ
  have hbad_le : badCols.card ≤ ∑ i ∈ S, (rowChanges i).card := Finset.card_biUnion_le
  have hnbad : n * badCols.card ≤ 2 * r * changes.card :=
    (Nat.mul_le_mul_left n hbad_le).trans hSbound'
  have hTadd : T.card + badCols.card = n := by
    have hle : badCols.card ≤ n := by simpa using Finset.card_le_univ badCols
    have hc : T.card = n - badCols.card := by simp [T, Finset.card_compl]
    omega
  have hsub_eq :
      H.submatrix (Subtype.val : S → Fin n) (Subtype.val : T → Fin n) =
        A.submatrix (Subtype.val : S → Fin n) (Subtype.val : T → Fin n) := by
    ext i j
    simp only [Matrix.submatrix_apply]
    by_contra hne
    have hj_row : j.1 ∈ rowChanges i.1 := by
      simp [rowChanges, hne]
    have hj_bad : j.1 ∈ badCols := Finset.mem_biUnion.mpr ⟨i.1, i.2, hj_row⟩
    have hj_not_bad : j.1 ∉ badCols := Finset.mem_compl.mp j.2
    exact hj_not_bad hj_bad
  have hsub_rank :
      Module.finrank ℝ
        (LinearMap.range (H.submatrix (Subtype.val : S → Fin n) (Subtype.val : T → Fin n)).mulVecLin) ≤
        r := by
    rw [hsub_eq]
    exact (PEqualNP.Outside.L_lib_559.submatrix_rank_le A S T).trans hrank
  have hhad :
      T.card * S.card ≤
        Module.finrank ℝ
          (LinearMap.range (H.submatrix (Subtype.val : S → Fin n) (Subtype.val : T → Fin n)).mulVecLin) * n :=
    PEqualNP.Outside.L_lib_559.hadamard_submatrix_rank_bound H hH_pm hH_orth S T
  have hTS : T.card * (2 * r) ≤ r * n := by
    rw [← hScard]
    exact hhad.trans (Nat.mul_le_mul_right n hsub_rank)
  have h2T : 2 * T.card ≤ n := by
    have hmul : r * (2 * T.card) ≤ r * n := by
      calc
        r * (2 * T.card) = T.card * (2 * r) := by ring
        _ ≤ r * n := hTS
    exact Nat.le_of_mul_le_mul_left hmul hr
  have hn_le_2bad : n ≤ 2 * badCols.card := by omega
  calc
    n ^ 2 = n * n := by ring
    _ ≤ n * (2 * badCols.card) := Nat.mul_le_mul_left n hn_le_2bad
    _ = 2 * (n * badCols.card) := by ring
    _ ≤ 2 * (2 * r * changes.card) := Nat.mul_le_mul_left 2 hnbad
    _ = 4 * r * changes.card := by ring
