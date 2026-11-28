import Mathlib.LinearAlgebra.Matrix.Rank

namespace PEqualNP.Outside.L_lib_1037

open Module Submodule Matrix

variable {K : Type} [Field K]

theorem projection_loss {V W : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (s t : Submodule K V) (hs : s ≤ t) :
    finrank K (t.map f) + finrank K s ≤ finrank K t + finrank K (s.map f) := by
  have dim (v : Submodule K V) : finrank K (v.map f) + finrank K (v ⊓ LinearMap.ker f : Submodule K V) = finrank K v := by
    have h := (f.domRestrict v).finrank_range_add_finrank_ker
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
      ← Submodule.finrank_map_subtype_eq v, Submodule.map_comap_subtype] at h
    exact h
  have hst := Submodule.finrank_mono (inf_le_inf_right (LinearMap.ker f) hs)
  have hs' := dim s
  have ht' := dim t
  omega

def pull {ι ι' : Type} (r : ι' → ι) : (ι → K) →ₗ[K] (ι' → K) where
  toFun x := x ∘ r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def cols {ι κ : Type} (A : Matrix ι κ K) (S : Finset κ) : Submodule K (ι → K) :=
  Submodule.span K (Set.range (fun j : S => A.col j.val))

theorem cols_mono {ι κ : Type} (A : Matrix ι κ K) {S J : Finset κ} (hs : S ⊆ J) :
    cols A S ≤ cols A J := by
  apply Submodule.span_mono
  rintro _ ⟨j,rfl⟩
  exact ⟨⟨j,hs j.property⟩,rfl⟩

theorem rank_pull {ι κ ι' : Type} [Fintype ι'] (A : Matrix ι κ K) (r : ι' → ι)
    (S : Finset κ) :
    (A.submatrix r (fun j : S => j.val)).rank = finrank K ((cols A S).map (pull r)) := by
  rw [Matrix.rank_eq_finrank_span_cols, cols, Submodule.map_span, ← Set.range_comp]
  rfl

theorem rank_id_cols {ι κ : Type} [Fintype ι] (A : Matrix ι κ K) (S : Finset κ) :
    (A.submatrix id (fun j : S => j.val)).rank = finrank K (cols A S) := by
  rw [Matrix.rank_eq_finrank_span_cols]
  rfl

set_option maxHeartbeats 900000 in
theorem submatrix_rank_loss {ι κ ι' : Type} [Fintype ι] [Fintype ι']
    (A : Matrix ι κ K) (r : ι' → ι) {S J : Finset κ} (hs : S ⊆ J) :
    (A.submatrix r (fun j : J => j.val)).rank + (A.submatrix id (fun j : S => j.val)).rank ≤
    (A.submatrix id (fun j : J => j.val)).rank + (A.submatrix r (fun j : S => j.val)).rank := by
  have hh := projection_loss (K := K) (V := ι → K) (W := ι' → K) (pull (K := K) r)
    (cols A S) (cols A J) (cols_mono A hs)
  exact (congrArg₂ (fun x y : ℕ => x ≤ y)
    (congrArg₂ Nat.add (rank_pull A r J) (rank_id_cols A S))
    (congrArg₂ Nat.add (rank_id_cols A J) (rank_pull A r S))).mpr
      hh

noncomputable def extend {m : ℕ} (S : Finset (Fin m)) : (S → K) →ₗ[K] (Fin m → K) where
  toFun z j := if h : j ∈ S then z ⟨j,h⟩ else 0
  map_add' x y := by funext j; by_cases h : j ∈ S <;> simp [h]
  map_smul' c x := by funext j; by_cases h : j ∈ S <;> simp [h]

theorem extend_injective {m : ℕ} (S : Finset (Fin m)) :
    Function.Injective (extend (K := K) S) := by
  intro z z' h
  funext j
  simpa [extend, j.property] using congrFun h j.val

theorem mulVec_extend {n m : ℕ} (G : Matrix (Fin n) (Fin m) K) (S : Finset (Fin m))
    (z : S → K) : G.mulVec (extend S z) = (G.submatrix id (fun j : S => j.val)).mulVec z := by
  classical
  funext x
  change (∑ j : Fin m, G x j * (extend S z) j) = ∑ j : S, G x j.val * z j
  calc
    _ = ∑ j ∈ S, G x j * (extend S z) j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro j _ hj
      simp [extend, hj]
    _ = ∑ j : S, G x j.val * z j := by
      rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro j _
      simp [extend, j.property]

noncomputable def cutKernel {n m : ℕ} (G : Matrix (Fin n) (Fin m) K) (S : Finset (Fin m)) :
    Submodule K (Fin m → K) :=
  (LinearMap.ker (G.submatrix id (fun j : S => j.val)).mulVecLin).map (extend S)

theorem mem_cutKernel {n m : ℕ} (G : Matrix (Fin n) (Fin m) K) (S : Finset (Fin m))
    (z : Fin m → K) :
    z ∈ cutKernel G S ↔ (∀ j ∉ S, z j = 0) ∧ G.mulVec z = 0 := by
  constructor
  · rintro ⟨v,hv,rfl⟩
    refine ⟨fun j hj => ?_, ?_⟩
    · simp [extend,hj]
    · rw [mulVec_extend]
      exact hv
  · rintro ⟨hs,hz⟩
    let v : S → K := fun j => z j.val
    have he : extend S v = z := by
      funext j
      by_cases hj : j ∈ S <;> simp [extend, v, hj, hs]
    refine ⟨v, ?_, he⟩
    change (G.submatrix id (fun j : S => j.val)).mulVec v = 0
    rw [← mulVec_extend, he, hz]

theorem dim_cutKernel {n m : ℕ} (G : Matrix (Fin n) (Fin m) K) (S : Finset (Fin m)) :
    (G.submatrix id (fun j : S => j.val)).rank + finrank K (cutKernel G S) = S.card := by
  let M := (G.submatrix id (fun j : S => j.val)).mulVecLin
  have he := (Submodule.equivMapOfInjective (extend S) (extend_injective S) (LinearMap.ker M)).finrank_eq
  change finrank K (LinearMap.ker M) = finrank K (cutKernel G S) at he
  change finrank K (LinearMap.range M) + finrank K (cutKernel G S) = S.card
  rw [← he, M.finrank_range_add_finrank_ker]
  simp

noncomputable def rankOn {n m : ℕ} (B : Matrix (Fin n) (Fin m) K)
    (I : Finset (Fin n)) (J : Finset (Fin m)) :=
  (B.submatrix (fun i : I => i.val) (fun j : J => j.val)).rank

theorem agree_rank {n m : ℕ} (G T : Matrix (Fin n) (Fin m) K)
    (I : Finset (Fin n)) (J : Finset (Fin m))
    (h : ∀ x ∈ I, ∀ y ∈ J, G x y = T x y) : rankOn G I J = rankOn T I J := by
  apply congrArg Matrix.rank
  ext i j
  exact h i.val i.property j.val j.property

theorem local_necessity {n m r : ℕ} {G T : Matrix (Fin n) (Fin m) K}
    (R I : Finset (Fin n)) (B S : Finset (Fin m)) (hS : S ⊆ B)
    (hR : ∀ x ∈ R, ∀ y, G x y = T x y)
    (hI : ∀ x ∈ I, ∀ y ∈ B, G x y = T x y)
    (hG : G.rank ≤ r) :
    (∀ z ∈ cutKernel G S, (∀ j ∉ S, z j = 0) ∧ ∀ x ∈ I, T.mulVec z x = 0) ∧
    rankOn T R Finset.univ + rankOn T I B + S.card ≤
      r + rankOn T R B + rankOn T I S + finrank K (cutKernel G S) := by
  constructor
  · intro z hz
    obtain ⟨hs,hk⟩ := (mem_cutKernel G S z).mp hz
    refine ⟨hs, fun x hx => ?_⟩
    calc
      T.mulVec z x = G.mulVec z x := by
        change (∑ j, T x j * z j) = ∑ j, G x j * z j
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j ∈ S
        · rw [hI x hx j (hS hj)]
        · simp [hs j hj]
      _ = 0 := congrFun hk x
  · have h₁ := submatrix_rank_loss G (fun i : R => i.val) (Finset.subset_univ B)
    have h₂ := submatrix_rank_loss G (fun i : I => i.val) hS
    have h₃ := dim_cutKernel G S
    have big := G.rank_submatrix_le id (fun j : (Finset.univ : Finset (Fin m)) => j.val)
    have hrj := agree_rank G T R Finset.univ (fun x hx y _ => hR x hx y)
    have hrb := agree_rank G T R B (fun x hx y _ => hR x hx y)
    have hib := agree_rank G T I B hI
    have his := agree_rank G T I S (fun x hx y hy => hI x hx y (hS hy))
    dsimp only [rankOn] at hrj hrb hib his ⊢
    omega

theorem necessity : (∀ (K : Type) [Field K] (n m a r : ℕ) (T : Matrix (Fin n) (Fin m) K)
  (row : Fin n → Option (Fin a)) (bags : ℕ → Finset (Fin m)),
  (∀ i j k : Fin a, i ≤ j → j ≤ k → bags i.val ∩ bags k.val ⊆ bags j.val) →
  let cut := fun j : ℕ => if 0 < j ∧ j < a then bags (j-1) ∩ bags j else ∅
  let R := (Finset.univ : Finset (Fin n)).filter (fun x => row x = none)
  let rows := fun i : Fin a => R ∪ Finset.univ.filter (fun x => row x = some i)
  let rk := fun (B : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) (J : Finset (Fin m)) =>
    Matrix.rank (B.submatrix (fun x : I => x.val) (fun y : J => y.val))
  let X := Fin m → K
  let State := Submodule K X
  let supported := fun (S : Finset (Fin m)) (z : X) => ∀ y ∉ S, z y = 0
  let agrees := fun (i : Fin a) (U V : State) =>
    ∀ z : X, supported (cut i.val ∩ cut (i.val+1)) z → (z ∈ U ↔ z ∈ V)
  let fits := fun (B : Matrix (Fin n) (Fin m) K) (i : Fin a) (j : ℕ) (U : State) =>
    (∀ z ∈ U, supported (cut j) z ∧ ∀ x ∈ rows i, B.mulVec z x = 0) ∧
    rk T R Finset.univ + rk B (rows i) (bags i.val) + (cut j).card ≤
      r + rk T R (bags i.val) + rk B (rows i) (cut j) + Module.finrank K U
  ((∃ G : Matrix (Fin n) (Fin m) K, Matrix.rank G ≤ r ∧ ∀ x y,
      (row x = none ∨ ∃ i : Fin a, row x = some i ∧ y ∈ bags i.val) → G x y = T x y) →
    rk T R Finset.univ ≤ r ∧ ∃ N : ℕ → State, ∀ i : Fin a,
      agrees i (N i.val) (N (i.val+1)) ∧
      fits T i i.val (N i.val) ∧ fits T i (i.val+1) (N (i.val+1)))) := by
  intro K k n m a r T row bags _interval cut R rows rk X State supported agrees fits
  rintro ⟨G,hgr,observed⟩
  have hr (x : Fin n) (hx : x ∈ R) (y : Fin m) : G x y = T x y :=
    observed x y (Or.inl (Finset.mem_filter.mp hx).2)
  have hi (i : Fin a) (x : Fin n) (hx : x ∈ rows i) (y : Fin m)
      (hy : y ∈ bags i.val) : G x y = T x y := by
    rcases Finset.mem_union.mp hx with h | h
    · exact hr x h y
    · exact observed x y (Or.inr ⟨i,(Finset.mem_filter.mp h).2,hy⟩)
  have left (i : Fin a) : cut i.val ⊆ bags i.val := by
    dsimp only [cut]
    split
    · exact Finset.inter_subset_right
    · exact Finset.empty_subset _
  have right (i : Fin a) : cut (i.val+1) ⊆ bags i.val := by
    dsimp only [cut]
    split
    · simp
    · exact Finset.empty_subset _
  refine ⟨?_, fun j => cutKernel G (cut j), fun i => ⟨?_,?_,?_⟩⟩
  · change rankOn T R Finset.univ ≤ r
    rw [← agree_rank G T R Finset.univ (fun x hx y _ => hr x hx y)]
    exact (G.rank_submatrix_le _ _).trans hgr
  · intro z hz
    rw [mem_cutKernel, mem_cutKernel]
    have hleft : ∀ j ∉ cut i.val, z j = 0 := fun j hj =>
      hz j (fun hm => hj (Finset.mem_inter.mp hm).1)
    have hright : ∀ j ∉ cut (i.val+1), z j = 0 := fun j hj =>
      hz j (fun hm => hj (Finset.mem_inter.mp hm).2)
    exact ⟨fun h => ⟨hright,h.2⟩, fun h => ⟨hleft,h.2⟩⟩
  · exact local_necessity R (rows i) (bags i.val) (cut i.val) (left i) hr (hi i) hgr
  · exact local_necessity R (rows i) (bags i.val) (cut (i.val+1)) (right i) hr (hi i) hgr

end PEqualNP.Outside.L_lib_1037

namespace PEqualNP.Outside.L_lib_1037

open Module Submodule
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem exists_outside_two (A B : Submodule K V) (hA : A ≠ ⊤) (hB : B ≠ ⊤) :
    ∃ x : V, x ∉ A ∧ x ∉ B := by
  obtain ⟨a,ha⟩ := SetLike.exists_notMem_of_ne_top A hA rfl
  obtain ⟨b,hb⟩ := SetLike.exists_notMem_of_ne_top B hB rfl
  by_cases hab : a ∈ B
  · by_cases hba : b ∈ A
    · refine ⟨a+b, fun hm => ha ?_, fun hm => hb ?_⟩
      · simpa using A.sub_mem hm hba
      · simpa using B.sub_mem hm hab
    · exact ⟨b,hba,hb⟩
  · exact ⟨a,ha,hab⟩

theorem common_kernel [FiniteDimensional K V] (S T : Submodule K V) (s : ℕ)
    (hs : finrank K S ≤ s) (ht : finrank K T ≤ s) :
    ∃ W : Submodule K V, Disjoint W S ∧ Disjoint W T ∧ finrank K (V ⧸ W) ≤ s := by
  classical
  let good (d : ℕ) := ∃ W : Submodule K V, Disjoint W S ∧ Disjoint W T ∧ finrank K W = d
  have hz : good 0 := ⟨⊥, disjoint_bot_left, disjoint_bot_left, by simp⟩
  obtain ⟨W,hWS,hWT,hmax⟩ := Nat.findGreatest_spec (P:=good) (Nat.zero_le (finrank K V)) hz
  refine ⟨W,hWS,hWT,?_⟩
  by_contra hi
  have dimW := W.finrank_quotient_add_finrank
  have proper (U : Submodule K V) (hu : finrank K U ≤ s) : W ⊔ U ≠ ⊤ := by
    intro he
    have hdu := Submodule.finrank_sup_add_finrank_inf_eq W U
    rw [he] at hdu
    simp only [finrank_top] at hdu
    omega
  obtain ⟨x,hxS,hxT⟩ := exists_outside_two (W ⊔ S) (W ⊔ T) (proper S hs) (proper T ht)
  let L := Submodule.span K {x}
  have hL (U : Submodule K V) (hu : x ∉ W ⊔ U) (hw : Disjoint W U) : Disjoint (L ⊔ W) U :=
    hw.disjoint_sup_left_of_disjoint_sup_right (Submodule.disjoint_span_singleton_of_notMem hu).symm
  have hlt : W < L ⊔ W := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro he
    have hx : x ∈ L ⊔ W := (show L ≤ L ⊔ W from le_sup_left) (Submodule.subset_span (by simp))
    have hxw : x ∈ W := he.symm ▸ hx
    exact hxS ((show W ≤ W ⊔ S from le_sup_left) hxw)
  have larger := Submodule.finrank_lt_finrank_of_lt hlt
  have admissible : good (finrank K (L ⊔ W : Submodule K V)) :=
    ⟨L ⊔ W, hL S hxS hWS, hL T hxT hWT, rfl⟩
  have bound := Nat.le_findGreatest (P:=good) (Submodule.finrank_le (L ⊔ W : Submodule K V)) admissible
  omega

def pad (d s : ℕ) : (Fin d → K) →ₗ[K] (Fin s → K) where
  toFun x j := if h : j.val < d then x ⟨j.val,h⟩ else 0
  map_add' x y := by funext j; by_cases h : j.val < d <;> simp [h]
  map_smul' c x := by funext j; by_cases h : j.val < d <;> simp [h]

theorem pad_injective {d s : ℕ} (h : d ≤ s) : Function.Injective (pad (K := K) d s) := by
  intro x y he
  funext j
  simpa [pad,j.isLt] using congrFun he (⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩ : Fin s)

theorem common_map [FiniteDimensional K V] (S T : Submodule K V) (s : ℕ)
    (hs : finrank K S ≤ s) (ht : finrank K T ≤ s) :
    ∃ f : V →ₗ[K] (Fin s → K),
      Function.Injective (f.domRestrict S) ∧ Function.Injective (f.domRestrict T) := by
  obtain ⟨W,hS,hT,hw⟩ := common_kernel S T s hs ht
  let b := (Module.finBasis K (V ⧸ W)).equivFun
  let e := (pad (K := K) (finrank K (V ⧸ W)) s).comp b.toLinearMap
  have he : Function.Injective e := (pad_injective hw).comp b.injective
  have inj (U : Submodule K V) (hd : Disjoint W U) :
      Function.Injective (W.mkQ.domRestrict U) := by
    apply LinearMap.injective_domRestrict_iff.mpr
    simpa only [Submodule.ker_mkQ] using hd.symm
  exact ⟨e.comp W.mkQ, he.comp (inj S hS), he.comp (inj T hT)⟩

theorem enlarge_kernels [FiniteDimensional K V]
    (L R P Q : Submodule K V) (s : ℕ) (hP : P ≤ L) (hQ : Q ≤ R)
    (hagree : P ⊓ R = Q ⊓ L)
    (hL : finrank K L ≤ s + finrank K P) (hR : finrank K R ≤ s + finrank K Q) :
    ∃ W : Submodule K V, W ⊓ L = P ∧ W ⊓ R = Q ∧ finrank K (V ⧸ W) ≤ s := by
  let A := P ⊔ Q
  have hl : A ⊓ L = P := by
    change (P ⊔ Q) ⊓ L = P
    rw [sup_inf_assoc_of_le Q hP, ← hagree, sup_inf_self]
  have hr : A ⊓ R = Q := by
    change (P ⊔ Q) ⊓ R = Q
    rw [sup_comm, sup_inf_assoc_of_le P hQ, hagree, sup_inf_self]
  have dim (Y : Submodule K V) :
      finrank K (Y.map A.mkQ) + finrank K (A ⊓ Y : Submodule K V) = finrank K Y := by
    have hd := (A.mkQ.domRestrict Y).finrank_range_add_finrank_ker
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ,
      ← Submodule.finrank_map_subtype_eq Y, Submodule.map_comap_subtype, inf_comm Y A] at hd
    exact hd
  have sl := dim L
  have sr := dim R
  rw [hl] at sl
  rw [hr] at sr
  obtain ⟨f,fl,fr⟩ := common_map (L.map A.mkQ) (R.map A.mkQ) s (by omega) (by omega)
  let F := f.comp A.mkQ
  have exactOn (Y : Submodule K V) (inj : Function.Injective (f.domRestrict (Y.map A.mkQ))) :
      LinearMap.ker F ⊓ Y = A ⊓ Y := by
    ext x
    constructor
    · rintro ⟨hk,hy⟩
      have hx : A.mkQ x ∈ Y.map A.mkQ := ⟨x,hy,rfl⟩
      have hh : (⟨A.mkQ x,hx⟩ : Y.map A.mkQ) = 0 := by
        apply inj
        change f (A.mkQ x) = f 0
        rw [map_zero]
        exact hk
      have hz : A.mkQ x = 0 := congrArg Subtype.val hh
      refine ⟨?_,hy⟩
      rw [← Submodule.ker_mkQ A]
      exact hz
    · rintro ⟨ha,hy⟩
      refine ⟨?_,hy⟩
      have hz : A.mkQ x = 0 := by
        change x ∈ LinearMap.ker A.mkQ
        rwa [Submodule.ker_mkQ]
      change f (A.mkQ x) = 0
      rw [hz,map_zero]
  refine ⟨LinearMap.ker F, (exactOn L fl).trans hl, (exactOn R fr).trans hr, ?_⟩
  rw [F.quotKerEquivRange.finrank_eq]
  simpa using (Submodule.finrank_le (LinearMap.range F))

theorem panel_kernel [FiniteDimensional K V] {Y : Type} [AddCommGroup Y] [Module K Y]
    (F : V →ₗ[K] Y) (L R P Q : Submodule K V) (budget : ℕ)
    (hP : P ≤ L) (hQ : Q ≤ R) (hp : P ≤ LinearMap.ker F) (hq : Q ≤ LinearMap.ker F)
    (hagree : P ⊓ R = Q ⊓ L)
    (hL : finrank K (LinearMap.range F) + finrank K L ≤
      budget + finrank K (L.map F) + finrank K P)
    (hR : finrank K (LinearMap.range F) + finrank K R ≤
      budget + finrank K (R.map F) + finrank K Q) :
    ∃ W : Submodule K V, W ≤ LinearMap.ker F ∧ W ⊓ L = P ∧ W ⊓ R = Q ∧
      finrank K (V ⧸ W) ≤ budget := by
  let A := LinearMap.ker F
  let lift := fun (U : Submodule K V) => U.comap A.subtype
  have dim_small (U : Submodule K V) (hu : U ≤ A) : finrank K (lift U) = finrank K U := by
    rw [← Submodule.finrank_map_subtype_eq A (lift U)]
    change finrank K ((U.comap A.subtype).map A.subtype) = _
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hu]
  have dim_restrict (U : Submodule K V) : finrank K (U.map F) + finrank K (lift U) = finrank K U := by
    have hd := (F.domRestrict U).finrank_range_add_finrank_ker
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
      ← Submodule.finrank_map_subtype_eq U, Submodule.map_comap_subtype] at hd
    rw [← Submodule.finrank_map_subtype_eq A (lift U)]
    change finrank K (U.map F) + finrank K ((U.comap A.subtype).map A.subtype) = finrank K U
    rw [Submodule.map_comap_subtype, inf_comm A U]
    exact hd
  have pl : lift P ≤ lift L := Submodule.comap_mono hP
  have qr : lift Q ≤ lift R := Submodule.comap_mono hQ
  have ag : lift P ⊓ lift R = lift Q ⊓ lift L := by
    change (P ⊓ R).comap A.subtype = (Q ⊓ L).comap A.subtype
    rw [hagree]
  have dl := dim_restrict L
  have dr := dim_restrict R
  have dp := dim_small P hp
  have dq := dim_small Q hq
  have lp := Submodule.finrank_mono pl
  let s := budget - finrank K (LinearMap.range F)
  obtain ⟨B,bl,br,bc⟩ := enlarge_kernels (lift L) (lift R) (lift P) (lift Q) s pl qr ag
    (by dsimp [s]; omega) (by dsimp [s]; omega)
  have exactOn (U N : Submodule K V) (hh : B ⊓ lift U = lift N) (hn : N ≤ A) :
      B.map A.subtype ⊓ U = N := by
    rw [Submodule.map_inf_eq_map_inf_comap]
    change (B ⊓ lift U).map A.subtype = N
    rw [hh]
    change (N.comap A.subtype).map A.subtype = N
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hn]
  refine ⟨B.map A.subtype, ?_, exactOn L P bl hp, exactOn R Q br hq, ?_⟩
  · rintro _ ⟨v,_,rfl⟩
    exact v.property
  · have e₁ := (B.map A.subtype).finrank_quotient_add_finrank
    have e₂ := B.finrank_quotient_add_finrank
    have e₃ := F.finrank_range_add_finrank_ker
    rw [Submodule.finrank_map_subtype_eq] at e₁
    change finrank K (LinearMap.range F) + finrank K A = finrank K V at e₃
    dsimp only [s] at bc
    omega

theorem encode_kernel [FiniteDimensional K V] {Y : Type} [AddCommGroup Y] [Module K Y]
    (c : V →ₗ[K] Y) (W : Submodule K V) (hw : W ≤ LinearMap.ker c) (s : ℕ)
    (hs : finrank K (V ⧸ W) ≤ finrank K (LinearMap.range c) + s) :
    ∃ f : V →ₗ[K] (Fin s → K), LinearMap.ker (c.prod f) = W := by
  let b := W.liftQ c hw
  let L := LinearMap.ker b
  have hb : LinearMap.range b = LinearMap.range c := Submodule.range_liftQ W c hw
  have hd := b.finrank_range_add_finrank_ker
  rw [hb] at hd
  have hL : finrank K L ≤ s := by dsimp only [L]; omega
  let coord := (Module.finBasis K L).equivFun
  let e := (pad (K := K) (finrank K L) s).comp coord.toLinearMap
  have he : Function.Injective e := (pad_injective hL).comp coord.injective
  obtain ⟨J,hJ⟩ := L.exists_isCompl
  let π := L.projectionOnto J hJ
  let f := e.comp (π.comp W.mkQ)
  refine ⟨f, ?_⟩
  ext x
  change (c x, f x) = (0,0) ↔ x ∈ W
  constructor
  · intro h
    have hc : c x = 0 := congrArg Prod.fst h
    have hf : f x = 0 := congrArg Prod.snd h
    have hx : W.mkQ x ∈ L := hc
    let y : L := ⟨W.mkQ x,hx⟩
    have hp : π (W.mkQ x) = y := L.projectionOnto_apply_left hJ y
    have hy : y = 0 := by
      apply he
      rw [← hp, map_zero]
      exact hf
    rw [← W.ker_mkQ]
    exact congrArg Subtype.val hy
  · intro hx
    have hc : c x = 0 := hw hx
    have hz : W.mkQ x = 0 := by
      change x ∈ LinearMap.ker W.mkQ
      rwa [Submodule.ker_mkQ]
    have hf : f x = 0 := by change e (π (W.mkQ x)) = 0; rw [hz,map_zero,map_zero]
    rw [hc,hf]

end PEqualNP.Outside.L_lib_1037

namespace PEqualNP.Outside.L_lib_1037

open Module Submodule
variable {K D A B : Type} [Field K] [AddCommGroup D] [Module K D]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]

theorem factor_on_image (f : D →ₗ[K] A) (g : D →ₗ[K] B)
    (hk : LinearMap.ker f ≤ LinearMap.ker g) :
    ∃ e : A →ₗ[K] B, ∀ x, e (f x) = g x := by
  obtain ⟨P,hP⟩ := (LinearMap.range f).exists_isCompl
  let π := (LinearMap.range f).projectionOnto P hP
  let onQuot := (LinearMap.ker f).liftQ g hk
  let e := (onQuot.comp f.quotKerEquivRange.symm.toLinearMap).comp π
  refine ⟨e,fun x => ?_⟩
  have hπ : π (f x) = f.rangeRestrict x := (LinearMap.range f).projectionOnto_apply_left hP (f.rangeRestrict x)
  have hf : f.quotKerEquivRange (Submodule.Quotient.mk x) = f.rangeRestrict x := rfl
  change onQuot (f.quotKerEquivRange.symm (π (f x))) = g x
  rw [hπ, ← hf, LinearEquiv.symm_apply_apply]
  rfl

theorem same_kernel_alignment [FiniteDimensional K B] (p q : D →ₗ[K] B)
    (hk : LinearMap.ker p = LinearMap.ker q) :
    ∃ e : B ≃ₗ[K] B, ∀ x, e (p x) = q x := by
  let i := Submodule.quotEquivOfEq _ _ hk
  let h := p.quotKerEquivRange.symm.trans (i.trans q.quotKerEquivRange)
  obtain ⟨e,he⟩ := Submodule.exists_linearEquiv_restrict_eq h
  refine ⟨e, fun x => ?_⟩
  have h₁ : p.quotKerEquivRange (Submodule.Quotient.mk x) = p.rangeRestrict x := rfl
  have h₂ : (h (p.rangeRestrict x) : B) = q x := by
    change (q.quotKerEquivRange (i (p.quotKerEquivRange.symm (p.rangeRestrict x))) : B) = q x
    rw [← h₁, LinearEquiv.symm_apply_apply]
    rfl
  exact (he (p.rangeRestrict x)).symm.trans h₂

theorem align_overlap [FiniteDimensional K B] (c : D →ₗ[K] A) (p q : D →ₗ[K] B)
    (hk : LinearMap.ker (c.prod p) = LinearMap.ker (c.prod q)) :
    ∃ (e : B ≃ₗ[K] B) (t : A →ₗ[K] B), ∀ x, e (p x) + t (c x) = q x := by
  let H := LinearMap.ker c
  have hloc : LinearMap.ker (p.domRestrict H) = LinearMap.ker (q.domRestrict H) := by
    ext y
    have hy : c y.val = 0 := y.property
    have hy' : y.val ∈ LinearMap.ker (c.prod p) ↔ y.val ∈ LinearMap.ker (c.prod q) := by rw [hk]
    change p y.val = 0 ↔ q y.val = 0
    change (c y.val,p y.val) = (0,0) ↔ (c y.val,q y.val) = (0,0) at hy'
    simpa [hy] using hy'
  obtain ⟨e,he⟩ := same_kernel_alignment (p.domRestrict H) (q.domRestrict H) hloc
  let δ := q - e.toLinearMap.comp p
  have hd : LinearMap.ker c ≤ LinearMap.ker δ := by
    intro x hx
    change q x - e (p x) = 0
    exact sub_eq_zero.mpr (he ⟨x,hx⟩).symm
  obtain ⟨t,ht⟩ := factor_on_image c δ hd
  refine ⟨e,t, fun x => ?_⟩
  rw [ht]
  change e (p x) + (q x - e (p x)) = q x
  abel

end PEqualNP.Outside.L_lib_1037

namespace PEqualNP.Outside.L_lib_1037

open Module Submodule Matrix
variable {K : Type} [Field K] {n m : ℕ}

noncomputable def coord (K : Type) [Field K] {m : ℕ} (S : Finset (Fin m)) : Submodule K (Fin m → K) :=
  LinearMap.range (extend S)

theorem coord_mem (S : Finset (Fin m)) (z : Fin m → K) :
    z ∈ coord K S ↔ ∀ j ∉ S, z j = 0 := by
  constructor
  · rintro ⟨v,rfl⟩ j hj
    simp [extend,hj]
  · intro h
    refine ⟨fun j => z j.val, ?_⟩
    funext j
    by_cases hj : j ∈ S <;> simp [extend,hj,h]

theorem coord_mono {S B : Finset (Fin m)} (h : S ⊆ B) : coord K S ≤ coord K B := by
  intro z hz
  rw [coord_mem] at hz ⊢
  exact fun j hj => hz j (fun h' => hj (h h'))

theorem coord_dim (S : Finset (Fin m)) : finrank K (coord K S) = S.card := by
  have h : finrank K (coord K S) = finrank K (S → K) :=
    (LinearEquiv.ofInjective (extend (K := K) S) (extend_injective (K := K) S)).finrank_eq.symm
  exact h.trans (by simp)

theorem coord_all : coord K (Finset.univ : Finset (Fin m)) = ⊤ := by
  apply top_unique
  intro z _
  rw [coord_mem]
  simp

noncomputable def rowMap (T : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) :
    (Fin m → K) →ₗ[K] (I → K) := (T.submatrix (fun x : I => x.val) id).mulVecLin

theorem rowMap_apply (T : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) (z : Fin m → K)
    (x : I) : rowMap T I z x = T.mulVec z x.val := rfl

theorem rank_image (T : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) (S : Finset (Fin m)) :
    finrank K ((coord K S).map (rowMap T I)) = rankOn T I S := by
  have hf : (rowMap T I).comp (extend S) =
      (T.submatrix (fun x : I => x.val) (fun j : S => j.val)).mulVecLin := by
    apply LinearMap.ext
    intro z
    funext j
    exact congrFun (mulVec_extend T S z) j.val
  change finrank K ((LinearMap.range (extend S)).map (rowMap T I)) = _
  rw [← LinearMap.range_comp, hf]
  rfl

theorem rank_common (T : Matrix (Fin n) (Fin m) K) (R : Finset (Fin n)) :
    finrank K (LinearMap.range (rowMap T R)) = rankOn T R Finset.univ := by
  have h := rank_image T R Finset.univ
  rwa [coord_all, Submodule.map_top] at h

theorem visible_rank (T : Matrix (Fin n) (Fin m) K) (R : Finset (Fin n)) (B : Finset (Fin m)) :
    finrank K (LinearMap.range ((rowMap T R).rangeRestrict.domRestrict (coord K B))) = rankOn T R B := by
  let f := rowMap T R
  rw [LinearMap.range_domRestrict]
  rw [← Submodule.finrank_map_subtype_eq (LinearMap.range f)]
  rw [← Submodule.map_comp]
  exact rank_image T R B

theorem observed_annihilation (T : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) (z : Fin m → K) :
    rowMap T I z = 0 ↔ ∀ x ∈ I, T.mulVec z x = 0 := by
  constructor
  · intro h x hx
    exact congrFun h ⟨x,hx⟩
  · intro h
    funext x
    exact h x.val x.property

end PEqualNP.Outside.L_lib_1037
namespace PEqualNP.Outside.L_lib_1037

open Module Submodule Matrix
variable {K : Type} [Field K] {n m : ℕ}

theorem local_panel_data (T : Matrix (Fin n) (Fin m) K)
    (R I : Finset (Fin n)) (B Sl Sr : Finset (Fin m)) (P Q : Submodule K (Fin m → K)) (r : ℕ)
    (ri : R ⊆ I) (lb : Sl ⊆ B) (rb : Sr ⊆ B) (budget : rankOn T R Finset.univ ≤ r)
    (agree : ∀ z : Fin m → K, (∀ j ∉ Sl ∩ Sr, z j = 0) → (z ∈ P ↔ z ∈ Q))
    (hp : ∀ z ∈ P, (∀ j ∉ Sl, z j = 0) ∧ ∀ x ∈ I, T.mulVec z x = 0)
    (hq : ∀ z ∈ Q, (∀ j ∉ Sr, z j = 0) ∧ ∀ x ∈ I, T.mulVec z x = 0)
    (dimL : rankOn T R Finset.univ + rankOn T I B + Sl.card ≤
      r + rankOn T R B + rankOn T I Sl + finrank K P)
    (dimR : rankOn T R Finset.univ + rankOn T I B + Sr.card ≤
      r + rankOn T R B + rankOn T I Sr + finrank K Q) :
    ∃ h : (Fin m → K) →ₗ[K] (Fin (r - rankOn T R Finset.univ) → K),
      (∀ z : Fin m → K, (∀ j ∉ Sl, z j = 0) →
        (((rowMap T R).rangeRestrict.prod h) z = 0 ↔ z ∈ P)) ∧
      (∀ z : Fin m → K, (∀ j ∉ Sr, z j = 0) →
        (((rowMap T R).rangeRestrict.prod h) z = 0 ↔ z ∈ Q)) ∧
      (∀ z : Fin m → K, (∀ j ∉ B, z j = 0) →
        ((rowMap T R).rangeRestrict.prod h) z = 0 → ∀ x ∈ I, T.mulVec z x = 0) := by
  let Bag := coord K B
  let lift := fun (U : Submodule K (Fin m → K)) => U.comap Bag.subtype
  let cl := coord K Sl
  let cr := coord K Sr
  let F := (rowMap T I).domRestrict Bag
  let c := (rowMap T R).rangeRestrict
  let d := rankOn T R Finset.univ
  let s := r - d
  have pcl : P ≤ cl := fun z hz => (coord_mem Sl z).mpr (hp z hz).1
  have qcr : Q ≤ cr := fun z hz => (coord_mem Sr z).mpr (hq z hz).1
  have cbl : cl ≤ Bag := coord_mono lb
  have cbr : cr ≤ Bag := coord_mono rb
  have ints (z : Fin m → K) (l : z ∈ cl) (rr : z ∈ cr) : ∀ j ∉ Sl ∩ Sr, z j = 0 := by
    intro j hj
    by_cases hl : j ∈ Sl
    · exact (coord_mem Sr z).mp rr j (fun hr => hj (Finset.mem_inter.mpr ⟨hl,hr⟩))
    · exact (coord_mem Sl z).mp l j hl
  have agreement : P ⊓ cr = Q ⊓ cl := by
    ext z
    constructor
    · rintro ⟨p,rr⟩
      exact ⟨(agree z (ints z (pcl p) rr)).mp p,pcl p⟩
    · rintro ⟨q,l⟩
      exact ⟨(agree z (ints z l (qcr q))).mpr q,qcr q⟩
  have dimLift (U : Submodule K (Fin m → K)) (hu : U ≤ Bag) : finrank K (lift U) = finrank K U := by
    rw [← Submodule.finrank_map_subtype_eq Bag (lift U)]
    change finrank K ((U.comap Bag.subtype).map Bag.subtype) = _
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hu]
  have image (U : Submodule K (Fin m → K)) (hu : U ≤ Bag) :
      (lift U).map F = U.map (rowMap T I) := by
    change (lift U).map ((rowMap T I).comp Bag.subtype) = _
    rw [Submodule.map_comp]
    change ((U.comap Bag.subtype).map Bag.subtype).map (rowMap T I) = _
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hu]
  have rangeF : finrank K (LinearMap.range F) = rankOn T I B := by
    rw [show LinearMap.range F = Bag.map (rowMap T I) from LinearMap.range_domRestrict ..]
    exact rank_image T I B
  have cutDim (S : Finset (Fin m)) (hS : coord K S ≤ Bag) :
      finrank K (lift (coord K S)) = S.card ∧
      finrank K ((lift (coord K S)).map F) = rankOn T I S :=
    ⟨(dimLift _ hS).trans (coord_dim S), by rw [image _ hS]; exact rank_image T I S⟩
  obtain ⟨dcl,irl⟩ := cutDim Sl cbl
  obtain ⟨dcr,irr⟩ := cutDim Sr cbr
  have dp := dimLift P (pcl.trans cbl)
  have dq := dimLift Q (qcr.trans cbr)
  have ap : lift P ≤ LinearMap.ker F := by
    intro z hz
    exact (observed_annihilation T I z).mpr (hp z.val hz).2
  have aq : lift Q ≤ LinearMap.ker F := by
    intro z hz
    exact (observed_annihilation T I z).mpr (hq z.val hz).2
  have ag : lift P ⊓ lift cr = lift Q ⊓ lift cl := by
    change (P ⊓ cr).comap Bag.subtype = (Q ⊓ cl).comap Bag.subtype
    rw [agreement]
  obtain ⟨W,wf,wl,wr,wd⟩ := panel_kernel F (lift cl) (lift cr) (lift P) (lift Q)
    (rankOn T R B + s) (Submodule.comap_mono pcl) (Submodule.comap_mono qcr) ap aq ag
    (by rw [rangeF,dp,show finrank K (lift cl) = Sl.card from dcl,show finrank K ((lift cl).map F) = rankOn T I Sl from irl]; dsimp [s,d]; omega)
    (by rw [rangeF,dq,show finrank K (lift cr) = Sr.card from dcr,show finrank K ((lift cr).map F) = rankOn T I Sr from irr]; dsimp [s,d]; omega)
  have wc : W ≤ LinearMap.ker (c.domRestrict Bag) := by
    intro z hz
    have ff : rowMap T I z.val = 0 := wf hz
    change (rowMap T R).rangeRestrict z.val = 0
    apply Subtype.ext
    funext j
    exact congrFun ff (⟨j.val,ri j.property⟩ : I)
  obtain ⟨v,hv⟩ := encode_kernel (c.domRestrict Bag) W wc s (by
    rw [show finrank K (LinearMap.range (c.domRestrict Bag)) = rankOn T R B from visible_rank T R B]
    exact wd)
  obtain ⟨J,hJ⟩ := Bag.exists_isCompl
  let π := Bag.projectionOnto J hJ
  let h := v.comp π
  have localEq (z : Bag) : (c.prod h) z.val = 0 ↔ z ∈ W := by
    change (c z.val, v (π z.val)) = 0 ↔ _
    rw [show π z.val = z from Bag.projectionOnto_apply_left hJ z]
    change z ∈ LinearMap.ker ((c.domRestrict Bag).prod v) ↔ z ∈ W
    rw [hv]
  have atCut (U N : Submodule K (Fin m → K)) (ub : U ≤ Bag) (wu : W ⊓ lift U = lift N)
      (z : Fin m → K) (zu : z ∈ U) : (c.prod h) z = 0 ↔ z ∈ N := by
    let zz : Bag := ⟨z,ub zu⟩
    constructor
    · intro hh
      have hm : zz ∈ W ⊓ lift U := ⟨(localEq zz).mp hh,zu⟩
      rw [wu] at hm
      exact hm
    · intro hn
      have hm : zz ∈ W ⊓ lift U := wu.symm ▸ (show zz ∈ lift N from hn)
      exact (localEq zz).mpr hm.1
  refine ⟨h, fun z hz => atCut cl P cbl wl z ((coord_mem Sl z).mpr hz),
    fun z hz => atCut cr Q cbr wr z ((coord_mem Sr z).mpr hz), ?_⟩
  intro z hz hh
  let zz : Bag := ⟨z,(coord_mem B z).mpr hz⟩
  exact (observed_annihilation T I z).mp (wf ((localEq zz).mp hh))

end PEqualNP.Outside.L_lib_1037

namespace PEqualNP.Outside.L_lib_1037

open Module Submodule
variable {K A H : Type} [Field K] [AddCommGroup A] [Module K A]
  [AddCommGroup H] [Module K H]

def bagSpace {m : ℕ} (S : Finset (Fin m)) : Submodule K (Fin m → K) :=
  { add_mem' := by intro x y hx hy j hj; simp [hx j hj, hy j hj]
    carrier := {z | ∀ y ∉ S, z y = 0}
    zero_mem' := by simp
    smul_mem' := by intro c x hx j hj; simp [hx j hj] }

theorem interval_overlap_subset {J : Type} [DecidableEq J] {a : ℕ}
    (bags : ℕ → Finset J)
    (interval : ∀ i j k : ℕ, i ≤ j → j ≤ k → k < a →
      bags i ∩ bags k ⊆ bags j)
    {i n : ℕ} (hin : i < n) (hna : n < a) :
    bags i ∩ bags n ⊆ bags (n-1) ∩ bags n := by
  intro x hx
  exact Finset.mem_inter.mpr
    ⟨interval i (n-1) n (by omega) (by omega) hna hx, (Finset.mem_inter.mp hx).2⟩

theorem linear_eq_on_bag {m : ℕ} (S : Finset (Fin m))
    (f g : (Fin m → K) →ₗ[K] H)
    (cols : ∀ j ∈ S, f (Pi.basisFun K (Fin m) j) = g (Pi.basisFun K (Fin m) j))
    (z : Fin m → K) (hz : ∀ j ∉ S, z j = 0) : f z = g z := by
  classical
  have expansion : z = ∑ j, z j • Pi.basisFun K (Fin m) j := by
    simpa using ((Pi.basisFun K (Fin m)).sum_repr z).symm
  rw [expansion]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ S
  · rw [cols j hj]
  · simp [hz j hj]

theorem basis_in_bag {m : ℕ} {S : Finset (Fin m)} {j : Fin m} (hj : j ∈ S) :
    Pi.basisFun K (Fin m) j ∈ bagSpace (K := K) S := by
  intro y hy
  have hne : y ≠ j := by intro h; exact hy (h ▸ hj)
  simp [Pi.basisFun_apply, hne]

theorem shear_kernel {m : ℕ} (c : (Fin m → K) →ₗ[K] A)
    (p : (Fin m → K) →ₗ[K] H) (e : H ≃ₗ[K] H) (t : A →ₗ[K] H)
    (z : Fin m → K) :
    (c.prod (e.toLinearMap.comp p + t.comp c)) z = 0 ↔ (c.prod p) z = 0 := by
  change (c z, e (p z) + t (c z)) = (0,0) ↔ (c z,p z) = (0,0)
  rw [Prod.mk.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨hc,hp⟩
    refine ⟨hc, e.injective ?_⟩
    simpa [hc] using hp
  · rintro ⟨hc,hp⟩
    simp [hc,hp]

theorem glue_interval_maps [FiniteDimensional K H] (a m : ℕ)
    (bags : ℕ → Finset (Fin m))
    (interval : ∀ i j k : ℕ, i ≤ j → j ≤ k → k < a →
      bags i ∩ bags k ⊆ bags j)
    (c : (Fin m → K) →ₗ[K] A) (hs : ℕ → (Fin m → K) →ₗ[K] H)
    (agree : ∀ i : ℕ, i+1 < a → ∀ z : Fin m → K,
      (∀ y ∉ bags i ∩ bags (i+1), z y = 0) →
      ((c.prod (hs i)) z = 0 ↔ (c.prod (hs (i+1))) z = 0)) :
    ∃ h : (Fin m → K) →ₗ[K] H, ∀ i : ℕ, i < a → ∀ z : Fin m → K,
      (∀ y ∉ bags i, z y = 0) →
      ((c.prod h) z = 0 ↔ (c.prod (hs i)) z = 0) := by
  classical
  have build : ∀ n : ℕ, n ≤ a → ∃ h : (Fin m → K) →ₗ[K] H,
      ∀ i : ℕ, i < n → ∀ z : Fin m → K,
      (∀ y ∉ bags i, z y = 0) →
      ((c.prod h) z = 0 ↔ (c.prod (hs i)) z = 0) := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨0, fun i hi => False.elim (by omega)⟩
    | succ n ih =>
      intro hn
      by_cases nz : n = 0
      · subst n
        refine ⟨hs 0, ?_⟩
        intro i hi z _
        have hiz : i = 0 := by omega
        subst i
        rfl
      obtain ⟨old, hold⟩ := ih (by omega)
      let S := bags (n-1) ∩ bags n
      let U := bagSpace (K := K) S
      have hker : LinearMap.ker ((c.domRestrict U).prod ((hs n).domRestrict U)) =
          LinearMap.ker ((c.domRestrict U).prod (old.domRestrict U)) := by
        ext z
        change (c.prod (hs n)) z.val = 0 ↔ (c.prod old) z.val = 0
        have zS : ∀ y ∉ S, z.val y = 0 := z.property
        have zprev : ∀ y ∉ bags (n-1), z.val y = 0 := by
          intro y hy
          exact zS y (fun h => hy (Finset.mem_inter.mp h).1)
        have ha := agree (n-1) (by omega) z.val (by simpa [S, Nat.sub_add_cancel (by omega : 1 ≤ n)] using zS)
        have hb := hold (n-1) (by omega) z.val zprev
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using ha.symm.trans hb.symm
      obtain ⟨e,t,he⟩ := align_overlap (c.domRestrict U) ((hs n).domRestrict U)
        (old.domRestrict U) hker
      let fresh := e.toLinearMap.comp (hs n) + t.comp c
      have onCut : ∀ z : Fin m → K, (∀ y ∉ S, z y = 0) → fresh z = old z := by
        intro z hz
        exact he ⟨z,hz⟩
      let h := (Pi.basisFun K (Fin m)).constr K
        (fun j => if j ∈ bags n then fresh (Pi.basisFun K (Fin m) j)
          else old (Pi.basisFun K (Fin m) j))
      have onNew : ∀ z : Fin m → K, (∀ y ∉ bags n, z y = 0) → h z = fresh z := by
        apply linear_eq_on_bag
        intro j hj
        simp only [h, Basis.constr_basis, ite_eq_left hj]
      have onOld : ∀ i : ℕ, i < n → ∀ z : Fin m → K,
          (∀ y ∉ bags i, z y = 0) → h z = old z := by
        intro i hi
        apply linear_eq_on_bag
        intro j hj
        by_cases jn : j ∈ bags n
        · have jS : j ∈ S := interval_overlap_subset bags interval hi (by omega)
              (Finset.mem_inter.mpr ⟨hj,jn⟩)
          have eq := onCut (Pi.basisFun K (Fin m) j) (basis_in_bag jS)
          simpa only [h, Basis.constr_basis, ite_eq_left jn] using eq
        · simp only [h, Basis.constr_basis, ite_eq_right jn]
      refine ⟨h, ?_⟩
      intro i hi z hz
      by_cases hin : i = n
      · subst i
        change (c z,h z) = (0,0) ↔ (c z,hs n z) = (0,0)
        rw [onNew z hz]
        exact shear_kernel c (hs n) e t z
      · have eq := onOld i (by omega) z hz
        have prev := hold i (by omega) z hz
        change (c z,h z) = (0,0) ↔ (c z,hs i z) = (0,0)
        rw [eq]
        exact prev
  exact build a le_rfl

end PEqualNP.Outside.L_lib_1037

namespace PEqualNP.Outside.L_lib_1037

open Module Submodule Matrix
variable {K Z : Type} [Field K] [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]

theorem complete_from_global_lift {n m r : ℕ} (T : Matrix (Fin n) (Fin m) K)
    (J : Fin n → Finset (Fin m)) (L : (Fin m → K) →ₗ[K] Z)
    (budget : finrank K Z ≤ r)
    (annihilates : ∀ x (v : Fin m → K), (∀ j ∉ J x, v j = 0) → L v = 0 →
      T.mulVec v x = 0) :
    ∃ G : Matrix (Fin n) (Fin m) K, G.rank ≤ r ∧ ∀ x j, j ∈ J x → G x j = T x j := by
  classical
  have rowFactor (x : Fin n) : ∃ e : Z →ₗ[K] K, ∀ (v : Fin m → K),
      (∀ j ∉ J x, v j = 0) → e (L v) = T.mulVec v x := by
    let P : Submodule K (Fin m → K) := bagSpace (J x)
    let b : (Fin m → K) →ₗ[K] K := (LinearMap.proj x).comp T.mulVecLin
    have inc : LinearMap.ker (L.comp P.subtype) ≤ LinearMap.ker (b.comp P.subtype) := by
      intro v hv
      exact annihilates x v v.property hv
    obtain ⟨e, he⟩ := factor_on_image (L.comp P.subtype) (b.comp P.subtype) inc
    exact ⟨e, fun v hv => he (⟨v,hv⟩ : P)⟩
  choose e he using rowFactor
  let out : Z →ₗ[K] (Fin n → K) := LinearMap.pi e
  refine ⟨LinearMap.toMatrix' (out.comp L), ?_, ?_⟩
  · change finrank K (LinearMap.range ((LinearMap.toMatrix' (out.comp L)).toLin')) ≤ r
    rw [Matrix.toLin'_toMatrix']
    exact (Submodule.finrank_mono (LinearMap.range_comp_le_range L out)).trans
      (LinearMap.finrank_range_le out |>.trans budget)
  · intro x j mem
    rw [LinearMap.toMatrix'_apply]
    change e x (L (Pi.single j 1)) = T x j
    have supp : ∀ k ∉ J x, (Pi.single j 1 : Fin m → K) k = 0 := by
      intro k hk
      exact Pi.single_eq_of_ne (fun h : k = j => hk (h ▸ mem)) _
    rw [he x _ supp, Matrix.mulVec_single_one]
    rfl

theorem finish_rows {n m a r d : ℕ} (T : Matrix (Fin n) (Fin m) K)
    (row : Fin n → Option (Fin a)) (bags : ℕ → Finset (Fin m)) (R : Finset (Fin n))
    (allrows : ∀ x, row x = none → x ∈ R) (dr : d ≤ r)
    (visible_dim : finrank K (LinearMap.range (T.submatrix (fun x : R => x.val) id).mulVecLin) = d)
    (h : (Fin m → K) →ₗ[K] (Fin (r-d) → K))
    (localRows : ∀ i : Fin a, ∀ v : Fin m → K, (∀ j ∉ bags i.val, v j = 0) →
      (((T.submatrix (fun x : R => x.val) id).mulVecLin.rangeRestrict).prod h) v = 0 →
      ∀ x, row x = some i → T.mulVec v x = 0) :
    ∃ G : Matrix (Fin n) (Fin m) K, G.rank ≤ r ∧ ∀ x y,
      (row x = none ∨ ∃ i : Fin a, row x = some i ∧ y ∈ bags i.val) → G x y = T x y := by
  classical
  let J := fun x => (row x).elim (Finset.univ : Finset (Fin m)) (fun i => bags i.val)
  let c := (T.submatrix (fun x : R => x.val) id).mulVecLin
  let L := c.rangeRestrict.prod h
  have budget : finrank K ((LinearMap.range c) × (Fin (r-d) → K)) ≤ r := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, visible_dim]
    omega
  have zeroRows (x : Fin n) (v : Fin m → K) (supp : ∀ j ∉ J x, v j = 0)
      (zero : L v = 0) : T.mulVec v x = 0 := by
    cases eq : row x with
    | none =>
      have h0 : c.rangeRestrict v = 0 := congrArg Prod.fst zero
      have h1 : c v = 0 := congrArg Subtype.val h0
      exact congrFun h1 (⟨x,allrows x eq⟩ : R)
    | some i =>
      exact localRows i v (by simpa [J,eq] using supp) zero x eq
  obtain ⟨G,rank,eq⟩ := complete_from_global_lift T J L budget zeroRows
  refine ⟨G,rank,?_⟩
  intro x y obs
  apply eq x y
  rcases obs with h0 | ⟨i,hi,mem⟩
  · simp [J,h0]
  · simpa [J,hi] using mem

end PEqualNP.Outside.L_lib_1037

open PEqualNP.Outside.L_lib_1037 in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.L_lib_1037 : ∀ (K : Type) [Field K] (n m a r : ℕ) (T : Matrix (Fin n) (Fin m) K)
  (row : Fin n → Option (Fin a)) (bags : ℕ → Finset (Fin m)),
  (∀ i j k : Fin a, i ≤ j → j ≤ k → bags i.val ∩ bags k.val ⊆ bags j.val) →
  let cut := fun j : ℕ => if 0 < j ∧ j < a then bags (j-1) ∩ bags j else ∅
  let R := (Finset.univ : Finset (Fin n)).filter (fun x => row x = none)
  let rows := fun i : Fin a => R ∪ Finset.univ.filter (fun x => row x = some i)
  let rk := fun (B : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) (J : Finset (Fin m)) =>
    Matrix.rank (B.submatrix (fun x : I => x.val) (fun y : J => y.val))
  let X := Fin m → K
  let State := Submodule K X
  let supported := fun (S : Finset (Fin m)) (z : X) => ∀ y ∉ S, z y = 0
  let agrees := fun (i : Fin a) (U V : State) =>
    ∀ z : X, supported (cut i.val ∩ cut (i.val+1)) z → (z ∈ U ↔ z ∈ V)
  let fits := fun (B : Matrix (Fin n) (Fin m) K) (i : Fin a) (j : ℕ) (U : State) =>
    (∀ z ∈ U, supported (cut j) z ∧ ∀ x ∈ rows i, B.mulVec z x = 0) ∧
    rk T R Finset.univ + rk B (rows i) (bags i.val) + (cut j).card ≤
      r + rk T R (bags i.val) + rk B (rows i) (cut j) + Module.finrank K U
  ((∃ G : Matrix (Fin n) (Fin m) K, Matrix.rank G ≤ r ∧ ∀ x y,
      (row x = none ∨ ∃ i : Fin a, row x = some i ∧ y ∈ bags i.val) → G x y = T x y) ↔
    rk T R Finset.univ ≤ r ∧ ∃ N : ℕ → State, ∀ i : Fin a,
      agrees i (N i.val) (N (i.val+1)) ∧
      fits T i i.val (N i.val) ∧ fits T i (i.val+1) (N (i.val+1))) := by
  intro K inst n m a r T row bags interval cut R rows rk X State supported agrees fits
  constructor
  · exact necessity K n m a r T row bags interval
  rintro ⟨budget, N, states⟩
  have left (i : Fin a) : cut i.val ⊆ bags i.val := by
    dsimp only [cut]
    split
    · exact Finset.inter_subset_right
    · exact Finset.empty_subset _
  have right (i : Fin a) : cut (i.val+1) ⊆ bags i.val := by
    dsimp only [cut]
    split
    · simp
    · exact Finset.empty_subset _
  let c := (rowMap T R).rangeRestrict
  let H := Fin (r-rankOn T R Finset.univ) → K
  have make (i : Fin a) := local_panel_data T R (rows i) (bags i.val)
    (cut i.val) (cut (i.val+1)) (N i.val) (N (i.val+1)) r
    Finset.subset_union_left (left i) (right i) budget (states i).1
    (states i).2.1.1 (states i).2.2.1 (states i).2.1.2 (states i).2.2.2
  choose h localProof using make
  let hs (i : ℕ) : (Fin m → K) →ₗ[K] H := if hi : i < a then h ⟨i,hi⟩ else 0
  have ordered (i j k : ℕ) (ij : i ≤ j) (jk : j ≤ k) (ka : k < a) :
      bags i ∩ bags k ⊆ bags j :=
    interval ⟨i,by omega⟩ ⟨j,by omega⟩ ⟨k,ka⟩ ij jk
  have neighboring (i : ℕ) (next : i+1 < a) (z : Fin m → K)
      (zs : ∀ j ∉ bags i ∩ bags (i+1), z j = 0) :
      (c.prod (hs i)) z = 0 ↔ (c.prod (hs (i+1))) z = 0 := by
    have ia : i < a := by omega
    have same : cut (i+1) = bags i ∩ bags (i+1) := by simp [cut, next]
    have onCut : ∀ j ∉ cut (i+1), z j = 0 := by simpa only [same] using zs
    have prev := (localProof ⟨i,ia⟩).2.1 z onCut
    have curr := (localProof ⟨i+1,next⟩).1 z onCut
    simpa only [hs, dite_eq_left ia, dite_eq_left next, c] using prev.trans curr.symm
  obtain ⟨globalH, glues⟩ := glue_interval_maps a m bags ordered c hs neighboring
  apply finish_rows T row bags R (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)
    budget (rank_common T R) globalH
  intro i z inBag ker x xi
  have same := (glues i.val i.isLt z inBag).mp ker
  have same' : (c.prod (h i)) z = 0 := by simpa [hs, i.isLt] using same
  exact (localProof i).2.2 z inBag same' x
    (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,xi⟩))
