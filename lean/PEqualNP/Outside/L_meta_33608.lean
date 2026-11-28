import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33608_aux.Pad

abbrev F := ZMod 2
abbrev J (n : ℕ) := Fin n ⊕ Fin n
abbrev M (n : ℕ) := Matrix (Fin n) (Fin n) F
abbrev BM (n f : ℕ) := Matrix (Fin n) (Fin f) F
abbrev Big (n : ℕ) := Matrix (J n) (J n) F
abbrev Larger (n f : ℕ) := Matrix (J n ⊕ Fin f) (J n ⊕ Fin f) F

def block {n f : ℕ} (A K : M n) (B : BM n f) : Larger n f :=
  let X := Matrix.fromBlocks A K K (0 : M n)
  let Y : Matrix (J n) (Fin f) F :=
    fun i j => Sum.elim (fun a => B a j) (fun _ => 0) i
  Matrix.fromBlocks X Y Y.transpose 0

def proj (n f : ℕ) : Larger n f →ₗ[F] Big n where
  toFun X := X.submatrix Sum.inl Sum.inl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def insertPad (n f : ℕ) : BM n f →ₗ[F] Larger n f where
  toFun B := block 0 0 B
  map_add' B C := by
    ext (a | a) (b | b)
    · cases a <;> cases b <;> exact (zero_add _).symm
    · cases a <;> first | rfl | exact (zero_add _).symm
    · cases b <;> first | rfl | exact (zero_add _).symm
    · exact (zero_add _).symm
  map_smul' c B := by
    ext (a | a) (b | b)
    · cases a <;> cases b <;> exact (smul_zero c).symm
    · cases a <;> first | rfl | exact (smul_zero c).symm
    · cases b <;> first | rfl | exact (smul_zero c).symm
    · exact (smul_zero c).symm

lemma insertPad_injective (n f : ℕ) : Function.Injective (insertPad n f) := by
  intro B C eq
  ext i j
  exact congrArg (fun X : Larger n f => X (Sum.inl (Sum.inl i)) (Sum.inr j)) eq

theorem reduce {n f t : ℕ} (P : Submodule F (M n)) (R : Fin t → Larger n f)
    (ranks : ∀ i, (R i).rank ≤ 2)
    (cov : ∀ (A K : M n) (B : BM n f), (A.transpose = A ∧ ∀ i, A i i = 0) →
      K ∈ P → block A K B ∈ Submodule.span F (Set.range R)) :
    ∃ (q : ℕ) (S : Fin q → Big n), q + n * f ≤ t ∧
      (∀ i, (S i).rank ≤ 2) ∧ ∀ A K : M n, (A.transpose = A ∧ ∀ i, A i i = 0) →
      K ∈ P → Matrix.fromBlocks A K K (0 : M n) ∈ Submodule.span F (Set.range S) := by
  classical
  let V := Submodule.span F (Set.range R)
  let pr := (proj n f).comp V.subtype
  let S := (proj n f) ∘ R
  have ran : LinearMap.range pr = Submodule.span F (Set.range S) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    change Submodule.map (proj n f) (Submodule.span F (Set.range R)) = _
    rw [Submodule.map_span, ← Set.range_comp]
  let inj := (insertPad n f).codRestrict V (fun B =>
    cov 0 0 B ⟨Matrix.transpose_zero, fun _ => rfl⟩ (Submodule.zero_mem P))
  let lift := inj.codRestrict (LinearMap.ker pr) (fun _ => by
    apply LinearMap.mem_ker.mpr
    ext (i | i) (j | j) <;> rfl)
  have li : Function.Injective lift := by
    intro b c e
    exact insertPad_injective n f (congrArg (fun x : LinearMap.ker pr => (x.val : Larger n f)) e)
  have kbound := LinearMap.finrank_le_finrank_of_injective li
  change Module.finrank F (BM n f) ≤ Module.finrank F (LinearMap.ker pr) at kbound
  rw [Module.finrank_matrix] at kbound
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at kbound
  have vb : Module.finrank F V ≤ t := by
    have h := finrank_range_le_card (R := F) R
    change Module.finrank F V ≤ Fintype.card (Fin t) at h
    simpa only [Fintype.card_fin] using h
  have dims := pr.finrank_range_add_finrank_ker
  rw [ran] at dims
  obtain ⟨ι, a, ai, span, lin⟩ := exists_linearIndependent' F S
  letI : Finite ι := Finite.of_injective a ai
  letI : Fintype ι := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  have dimS : Module.finrank F (Submodule.span F (Set.range S)) = Fintype.card ι := by
    rw [← span, finrank_span_eq_card lin]
  let T : Fin (Fintype.card ι) → Big n := (S ∘ a) ∘ e.symm
  have spT : Submodule.span F (Set.range T) = Submodule.span F (Set.range S) := by
    calc
      _ = Submodule.span F (Set.range (S ∘ a)) := by
        rw [show Set.range T = Set.range (S ∘ a) from e.symm.surjective.range_comp (S ∘ a)]
      _ = _ := span
  refine ⟨_, T, by omega, ?_, ?_⟩
  · intro i
    exact ((R (a (e.symm i))).rank_submatrix_le (Sum.inl : J n → J n ⊕ Fin f)
      (Sum.inl : J n → J n ⊕ Fin f)).trans (ranks _)
  · intro A K ha hk
    rw [spT, ← ran]
    exact ⟨⟨block A K 0, cov A K 0 ha hk⟩, rfl⟩

end PEqualNP.Outside.L_meta_33608_aux.Pad

namespace PEqualNP.Outside.L_meta_33608_aux.Graph

abbrev F := ZMod 2
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) F
abbrev Big (n : ℕ) := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F
variable {n : ℕ}

def Alt (A : Mat n) := A.transpose = A ∧ ∀ i, A i i = 0
def P (edges : Finset (Fin n × Fin n)) : Submodule F (Mat n) := {
  carrier := {K | Alt K ∧ ∀ i j, (i,j) ∉ edges → (j,i) ∉ edges → K i j = 0}
  zero_mem' := ⟨⟨rfl, fun _ => rfl⟩, fun _ _ _ _ => rfl⟩, add_mem' := by
    rintro A B ⟨⟨a, a'⟩, a''⟩ ⟨⟨b, b'⟩, b''⟩
    exact ⟨⟨by rw [Matrix.transpose_add, a, b], fun i => by simp [a', b']⟩,
      fun i j h k => by simp [a'' i j h k, b'' i j h k]⟩
  smul_mem' := by
    rintro c A ⟨⟨a, a'⟩, a''⟩
    exact ⟨⟨by rw [Matrix.transpose_smul, a], fun i => by simp [a']⟩,
      fun i j h k => by simp [a'' i j h k]⟩ }

def extend (e : Finset (Fin n × Fin n)) (x : e → F) : Mat n := fun i j =>
  if h : (i,j) ∈ e then x ⟨(i,j),h⟩ else if k : (j,i) ∈ e then x ⟨(j,i),k⟩ else 0

lemma extend_mem (e : Finset (Fin n × Fin n)) (he : ∀ p∈e, p.1 < p.2) (x : e → F) :
    extend e x ∈ P e := by
  refine ⟨⟨?_, ?_⟩, fun i j h k => by simp [extend, h, k]⟩
  · ext i j
    by_cases h : (i,j) ∈ e
    · have k : (j,i) ∉ e := fun k => (he _ h).not_gt (he _ k)
      simp [extend, h, k, Matrix.transpose_apply]
    · by_cases k : (j,i) ∈ e <;> simp [extend, h, k, Matrix.transpose_apply]
  · intro i
    have h : (i,i) ∉ e := fun k => lt_irrefl _ (he _ k)
    simp [extend, h]

def edgeEquiv (e : Finset (Fin n × Fin n)) (he : ∀ p∈e, p.1 < p.2) :
    P e ≃ₗ[F] (e → F) where
  toFun A p := A.val p.val.1 p.val.2
  invFun x := ⟨extend e x, extend_mem e he x⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := by
    intro A
    apply Subtype.ext
    ext i j
    change (extend e (fun p => A.val p.val.1 p.val.2)) i j = A.val i j
    by_cases h : (i,j) ∈ e
    · simp [extend,h]
    · by_cases k : (j,i) ∈ e
      · simpa [extend, h, k] using congrFun (congrFun A.property.1.1 i) j
      · simp [extend, h, k, A.property.2 i j h k]
  right_inv := by
    intro x
    funext p
    change extend e x p.val.1 p.val.2 = x p
    simp [extend,p.property]

theorem finrank_P (edges : Finset (Fin n × Fin n)) (hn : ∀ p∈edges, p.1 < p.2) :
    Module.finrank F (P edges) = edges.card := by
  simpa using (edgeEquiv edges hn).finrank_eq

def upper (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ ×ˢ Finset.univ).filter (fun p => p.1 < p.2)

lemma upper_mem (i j : Fin n) : (i,j) ∈ upper n ↔ i < j := by simp [upper]

lemma alt_iff_mem_upper (A : Mat n) : Alt A ↔ A ∈ P (upper n) := by
  refine ⟨fun h => ⟨h, ?_⟩, fun h => h.1⟩
  intro i j hij hji
  simp only [upper_mem] at hij hji
  obtain rfl : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
  exact h.2 _

lemma finrank_upper : Module.finrank F (P (upper n)) = n.choose 2 := by
  rw [finrank_P _ (fun p h => (upper_mem _ _).mp h)]
  simpa [upper] using (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n))))

def Wsp (S : Submodule F (Mat n)) : Submodule F (Big n) :=
  Submodule.span F {X : Big n | ∃ A K : Mat n, Alt A ∧ K ∈ S ∧
    X = Matrix.fromBlocks A K K (0 : Mat n)}

def blk (S : Submodule F (Mat n)) : (P (upper n) × S) →ₗ[F] Big n where
  toFun pair := Matrix.fromBlocks pair.1.val pair.2.val pair.2.val (0 : Mat n)
  map_add' := by
    intro x y
    ext i j
    cases i <;> cases j <;> rfl
  map_smul' := by
    intro c x
    ext i j
    cases i <;> cases j <;> rfl

lemma blk_inj (S : Submodule F (Mat n)) : Function.Injective (blk S) := by
  intro x y h
  apply Prod.ext <;> apply Subtype.ext <;> ext i j
  · exact congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
  · exact congrFun (congrFun h (Sum.inl i)) (Sum.inr j)

lemma Wsp_eq_range (S : Submodule F (Mat n)) : Wsp S = LinearMap.range (blk S) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨A, K, a, k, rfl⟩
    exact ⟨(⟨A, (alt_iff_mem_upper A).mp a⟩, ⟨K, k⟩), rfl⟩
  · rintro _ ⟨⟨A, K⟩, rfl⟩
    exact Submodule.subset_span ⟨_, _, A.property.1, K.property, rfl⟩

theorem finrank_Wsp (edges : Finset (Fin n × Fin n)) (hn : ∀ p∈edges, p.1 < p.2) :
    Module.finrank F (Wsp (P edges)) = n.choose 2 + edges.card := by
  rw [Wsp_eq_range, LinearMap.finrank_range_of_inj (blk_inj _), Module.finrank_prod,
    finrank_upper, finrank_P edges hn]

def Hsp (S : Submodule F (Mat n)) : Submodule F (Fin n → F) :=
  Submodule.span F {v | ∃ K ∈ S, ∃ j : Fin n, v = fun i => K i j}

def unitEdge (i j : Fin n) : Mat n := fun a b =>
  if (a = i ∧ b = j) ∨ (a = j ∧ b = i) then 1 else 0

lemma unitEdge_mem (edges : Finset (Fin n × Fin n)) (i j : Fin n)
    (h : (i,j) ∈ edges) (hne : i ≠ j) : unitEdge i j ∈ P edges := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · ext a b
    simp only [Matrix.transpose_apply, unitEdge]
    grind
  · intro a
    simp only [unitEdge]
    grind
  · intro a b h₁ h₂
    simp only [unitEdge]
    grind

lemma active_single_mem (e : Finset (Fin n × Fin n)) (he : ∀ p∈e, p.1 < p.2)
    (i : Fin n) (hi : i ∈ e.image Prod.fst ∪ e.image Prod.snd) :
    Pi.single i (1 : F) ∈ Hsp (P e) := by
  apply Submodule.subset_span
  rcases Finset.mem_union.mp hi with h | h
  · obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp h
    have hn : a ≠ b := (he _ hab).ne
    refine ⟨unitEdge a b, unitEdge_mem e a b hab hn, b, ?_⟩
    funext x
    by_cases hx : x = a <;> simp_all [unitEdge, Pi.single_apply, eq_comm]
  · obtain ⟨⟨a,b⟩, hab, rfl⟩ := Finset.mem_image.mp h
    have hn : a ≠ b := (he _ hab).ne
    refine ⟨unitEdge a b, unitEdge_mem e a b hab hn, a, ?_⟩
    funext x
    by_cases hx : x = b <;> simp_all [unitEdge, Pi.single_apply, eq_comm]

theorem active_le_finrank_Hsp (edges : Finset (Fin n × Fin n)) (hn : ∀ p∈edges, p.1 < p.2) :
    (edges.image Prod.fst ∪ edges.image Prod.snd).card ≤ Module.finrank F (Hsp (P edges)) := by
  let s := edges.image Prod.fst ∪ edges.image Prod.snd
  let v : s → Hsp (P edges) := fun i => ⟨Pi.single i.val 1, active_single_mem edges hn i i.property⟩
  have hi : LinearIndependent F v := by
    apply LinearIndependent.of_comp (Hsp (P edges)).subtype
    exact (Pi.linearIndependent_single_one (Fin n) F).comp (fun i : s => i.val) Subtype.val_injective
  change s.card ≤ _
  simpa only [Fintype.card_coe] using hi.fintype_card_le_finrank

end PEqualNP.Outside.L_meta_33608_aux.Graph

namespace PEqualNP.Outside.L_meta_33608_aux.Coset

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

lemma labelLine {n t : ℕ} (P : Submodule F (Matrix (Fin n) (Fin n) F))
    (hP : ∀ K ∈ P, Alt K)
    (R : Fin t → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (hRk : ∀ i, (R i).rank ≤ 2)
    (Cplus : Finset (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F ⧸ WSub P))
    (rep : Cplus → Fin t) (hrep : ∀ c, (WSub P).mkQ (R (rep c)) = c.1) :
    ∀ c : Cplus, ∃ d : Matrix (Fin n) (Fin n) F,
      ∀ i : Fin t, (WSub P).mkQ (R i) = c.1 →
        crossLin n (R i) + crossLin n (R (rep c)) ∈ Submodule.span F {d} := by
  classical
  let W := WSub P
  let qR := fun i => W.mkQ (R i)
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

lemma groupLabels {V : Type*} [AddCommGroup V] [Module F V] [DecidableEq V]
    {t : ℕ} (qR : Fin t → V) (α : Fin t → F) :
    let Cplus := (Finset.univ.image qR).erase 0
    ∑ c : Cplus, (∑ i ∈ Finset.univ.filter (fun i => qR i = c.1), α i) • c.1 =
      ∑ i : Fin t, α i • qR i := by
  classical
  intro Cplus
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin t))) (t := Finset.univ.image qR) (g := qR)
    (f := fun i => α i • qR i) (fun i _ => Finset.mem_image_of_mem qR (Finset.mem_univ i))
  rw [← hfib]
  have hsum_er : ∑ c ∈ Finset.univ.image qR, ∑ i ∈ Finset.univ.filter (fun i => qR i = c), α i • qR i =
      ∑ c ∈ Cplus, ∑ i ∈ Finset.univ.filter (fun i => qR i = c), α i • qR i := by
    by_cases h0 : (0 : V) ∈ Finset.univ.image qR
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

lemma dimBound {n : ℕ} (P : Submodule F (Matrix (Fin n) (Fin n) F))
    (hP : ∀ K ∈ P, Alt K)
    (t : ℕ) (R : Fin t → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (hRk : ∀ i, (R i).rank ≤ 2)
    (hWS : WSub P ≤ Submodule.span F (Set.range R)) (h : ℕ)
    (hsize : Module.finrank F (Submodule.span F (Set.range R)) ≤
      Module.finrank F (WSub P) + h) :
    Module.finrank F P + h + 2 ≤ 2 ^ (h+1) := by
  classical
  set W := WSub P
  set S := Submodule.span F (Set.range R)
  set D := Module.finrank F W
  set p := Module.finrank F P
  set Q := S.map W.mkQ
  set s := Module.finrank F Q
  have hs_le : s ≤ h := by
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
  have hd_ex := labelLine P hP R hRk Cplus rep hrep
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
    exact groupLabels qR α
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
      exact groupLabels qR α
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
  apply dimBound P hP t R hRk hWS
  change Module.finrank F S ≤ D + (t - D)
  omega

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) F
abbrev Big (n : ℕ) := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F
def Wsp {n : ℕ} (P : Submodule F (Mat n)) : Submodule F (Big n) :=
  Submodule.span F {X : Big n | ∃ A K : Mat n,
    Alt A ∧ K ∈ P ∧ X = Matrix.fromBlocks A K K (0 : Mat n)}

theorem main {n : ℕ} (P : Submodule F (Mat n)) (hP : ∀ K ∈ P, Alt K)
    (q : ℕ) (R : Fin q → Big n) (hR : ∀ i, (R i).rank ≤ 2)
    (hWS : Wsp P ≤ Submodule.span F (Set.range R)) :
    let D := Module.finrank F (Wsp P)
    let h := q - D
    D ≤ q ∧ Module.finrank F P + h + 2 ≤ 2 ^ (h + 1) := by
  have he : Wsp P = WSub P := WSub_eq_span P
  rw [he] at hWS ⊢
  exact part2 P hP q R hR hWS

end PEqualNP.Outside.L_meta_33608_aux.Coset

namespace PEqualNP.Outside.L_meta_33608_aux.Active

open scoped BigOperators
open Matrix

abbrev F := ZMod 2

variable {n : ℕ}

abbrev V (n : ℕ) := Fin n → F
abbrev JV (n : ℕ) := Fin n ⊕ Fin n → F
abbrev Big (n : ℕ) := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) F

def Alt (A : Mat n) : Prop := A.transpose = A ∧ ∀ i, A i i = 0

def Wsp (P : Submodule F (Mat n)) : Submodule F (Big n) :=
  Submodule.span F {X : Big n | ∃ A K : Mat n, Alt A ∧ K ∈ P ∧ X = Matrix.fromBlocks A K K (0 : Mat n)}

def Hsp (P : Submodule F (Mat n)) : Submodule F (V n) :=
  Submodule.span F {v : Fin n → F | ∃ K ∈ P, ∃ j : Fin n, v = fun i => K i j}

def Gset (E : Submodule F (JV n)) : Set (Big n) :=
  {X : Big n | (∀ j, (fun i => X i j) ∈ E) ∧ (∀ i, (fun j => X i j) ∈ E)}

def freeSp (E : Submodule F (JV n)) : Submodule F (Big n) := Submodule.span F (Gset E)

theorem two_zero (a : F) : a + a = 0 := CharTwo.add_self_eq_zero a

theorem se_dot (a b c d : V n) :
    (Sum.elim a b : JV n) ⬝ᵥ (Sum.elim c d : JV n) = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem fb_mulVec (A B C D : Mat n) (c d : V n) :
    Matrix.fromBlocks A B C D *ᵥ (Sum.elim c d : JV n) =
      Sum.elim (A *ᵥ c + B *ᵥ d) (C *ᵥ c + D *ᵥ d) := by
  rw [Matrix.fromBlocks_mulVec]
  rfl

theorem sym_swap (K : Mat n) (hK : K.transpose = K) (u w : V n) :
    u ⬝ᵥ (K *ᵥ w) = w ⬝ᵥ (K *ᵥ u) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hK, dotProduct_comm]

theorem alt_quad (A : Mat n) (hA : Alt A) (y : V n) : y ⬝ᵥ (A *ᵥ y) = 0 := by
  classical
  let B : Mat n := Matrix.of fun i j => if i < j then A i j else 0
  have hAB : A = B + B.transpose := by
    ext i j
    simp only [B, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply]
    rcases lt_trichotomy i j with h | h | h
    · rw [if_pos h, if_neg (not_lt.mpr h.le), add_zero]
    · subst h; simp [hA.2 i]
    · rw [if_neg (not_lt.mpr h.le), if_pos h, zero_add]
      have := congrFun (congrFun hA.1 i) j
      simpa [Matrix.transpose_apply] using this.symm
  have e : y ⬝ᵥ (B.transpose *ᵥ y) = y ⬝ᵥ (B *ᵥ y) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  rw [hAB, Matrix.add_mulVec, dotProduct_add, e, two_zero]

def bil (u w : JV n) : Big n →ₗ[F] F where
  toFun X := u ⬝ᵥ (X *ᵥ w)
  map_add' X Y := by simp [Matrix.add_mulVec, dotProduct_add]
  map_smul' c X := by simp [Matrix.smul_mulVec, dotProduct_smul]

theorem bil_apply (u w : JV n) (X : Big n) : bil u w X = u ⬝ᵥ (X *ᵥ w) := rfl

theorem Gset_right {E : Submodule F (JV n)} {X : Big n} (hX : X ∈ Gset E) (u w : JV n)
    (hw : ∀ e ∈ E, w ⬝ᵥ e = 0) : bil u w X = 0 := by
  have : X *ᵥ w = 0 := by
    funext i
    have h := hw _ (hX.2 i)
    simp only [Matrix.mulVec, Pi.zero_apply]
    rw [dotProduct_comm]
    exact h
  rw [bil_apply, this, dotProduct_zero]

theorem Gset_left {E : Submodule F (JV n)} {X : Big n} (hX : X ∈ Gset E) (u w : JV n)
    (hu : ∀ e ∈ E, u ⬝ᵥ e = 0) : bil u w X = 0 := by
  have : u ᵥ* X = 0 := by
    funext j
    have h := hu _ (hX.1 j)
    simp only [Matrix.vecMul, Pi.zero_apply]
    exact h
  rw [bil_apply, Matrix.dotProduct_mulVec, this, zero_dotProduct]

theorem vanish_L (P : Submodule F (Mat n)) (E : Submodule F (JV n)) (ℓ : Big n →ₗ[F] F)
    (hW : ∀ A K : Mat n, Alt A → K ∈ P → ℓ (Matrix.fromBlocks A K K 0) = 0)
    (hG : ∀ X ∈ Gset E, ℓ X = 0) : ∀ X ∈ Wsp P ⊔ freeSp E, ℓ X = 0 := by
  have h : Wsp P ⊔ freeSp E ≤ LinearMap.ker ℓ := by
    apply sup_le
    · apply Submodule.span_le.mpr
      rintro X ⟨A, K, hA, hK, rfl⟩
      exact hW A K hA hK
    · apply Submodule.span_le.mpr
      intro X hX
      exact hG X hX
  intro X hX
  exact h hX

theorem rank4_mat (a b c d e f : F) :
    (!![a, b, c, 1; d, e, 1, 0; f, 1, 0, 0; 1, 0, 0, 0] : Matrix (Fin 4) (Fin 4) F).rank = 4 := by
  have h2 : (2 : F) = 0 := by decide
  let M : Matrix (Fin 4) (Fin 4) F := !![a, b, c, 1; d, e, 1, 0; f, 1, 0, 0; 1, 0, 0, 0]
  let N : Matrix (Fin 4) (Fin 4) F := !![0, 0, 0, 1; 0, 0, 1, f; 0, 1, e, d + e * f;
    1, c, b + c * e, a + b * f + c * (d + e * f)]
  have hMN : M * N = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M, N, Matrix.mul_apply, Fin.sum_univ_four] <;>
      ring_nf <;> simp [h2]
  have hNM : N * M = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M, N, Matrix.mul_apply, Fin.sum_univ_four] <;>
      ring_nf <;> simp [h2]
  have hu : IsUnit M := ⟨⟨M, N, hMN, hNM⟩, rfl⟩
  show M.rank = 4
  rw [Matrix.rank_of_isUnit M hu]
  simp

theorem rank_four (X : Big n) (a0 a1 a2 a3 : JV n)
    (h03 : a0 ⬝ᵥ (X *ᵥ a3) = 1)
    (h30 : a3 ⬝ᵥ (X *ᵥ a0) = 1) (h12 : a1 ⬝ᵥ (X *ᵥ a2) = 1) (h21 : a2 ⬝ᵥ (X *ᵥ a1) = 1)
    (h13 : a1 ⬝ᵥ (X *ᵥ a3) = 0) (h31 : a3 ⬝ᵥ (X *ᵥ a1) = 0) (h22 : a2 ⬝ᵥ (X *ᵥ a2) = 0)
    (h23 : a2 ⬝ᵥ (X *ᵥ a3) = 0) (h32 : a3 ⬝ᵥ (X *ᵥ a2) = 0) (h33 : a3 ⬝ᵥ (X *ᵥ a3) = 0) :
    4 ≤ X.rank := by
  let vec : Fin 4 → JV n := ![a0, a1, a2, a3]
  let Vm : Matrix (Fin n ⊕ Fin n) (Fin 4) F := Matrix.of fun j a => vec a j
  let M : Matrix (Fin 4) (Fin 4) F := Vm.transpose * X * Vm
  have hM : ∀ a b, M a b = vec a ⬝ᵥ (X *ᵥ vec b) := by
    intro a b
    simp only [M, Vm, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, dotProduct,
      Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have Meq : M = !![M 0 0, M 0 1, M 0 2, 1; M 1 0, M 1 1, 1, 0; M 2 0, 1, 0, 0; 1, 0, 0, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [hM, vec, h03, h30, h12, h21, h13, h31, h22, h23, h32, h33]
  have hr : M.rank = 4 := by
    rw [Meq]
    exact rank4_mat _ _ _ _ _ _
  have le1 : M.rank ≤ X.rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  omega

theorem factor {E : Submodule F (JV n)} (ρ : E →ₗ[F] V n) (f : E →ₗ[F] F)
    (h : LinearMap.ker ρ ≤ LinearMap.ker f) : ∃ g : V n →ₗ[F] F, ∀ e, g (ρ e) = f e := by
  obtain ⟨ι, hι⟩ := LinearMap.exists_leftInverse_of_injective ((LinearMap.ker ρ).liftQ ρ le_rfl)
    (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
  refine ⟨((LinearMap.ker ρ).liftQ f h).comp ι, fun e => ?_⟩
  have e1 : ρ e = (LinearMap.ker ρ).liftQ ρ le_rfl (Submodule.Quotient.mk e) := rfl
  rw [LinearMap.comp_apply, e1, ← LinearMap.comp_apply ι, hι, LinearMap.id_apply]
  rfl

theorem dual_dot (φ : V n →ₗ[F] F) (v : V n) :
    φ v = v ⬝ᵥ (fun i => φ (fun j => if i = j then 1 else 0)) := by
  rw [LinearMap.pi_apply_eq_sum_univ φ v]
  simp [dotProduct, smul_eq_mul]

def itL : V n →ₗ[F] JV n where
  toFun t := Sum.elim t 0
  map_add' a b := by funext j; cases j <;> simp
  map_smul' c a := by funext j; cases j <;> simp

def pbL : JV n →ₗ[F] V n := LinearMap.funLeft F F Sum.inr

theorem pbL_apply (e : JV n) (i : Fin n) : pbL e i = e (Sum.inr i) := rfl

theorem split_vec (e : JV n) : e = Sum.elim (fun i => e (Sum.inl i)) (fun i => e (Sum.inr i)) := by
  funext j; cases j <;> rfl

theorem dir1 (P : Submodule F (Mat n)) (hP : ∀ K ∈ P, Alt K) (E : Submodule F (JV n))
    (hL : Wsp P ⊔ freeSp E =
      Submodule.span F {X : Big n | X ∈ Wsp P ⊔ freeSp E ∧ X.rank ≤ 2}) :
    Module.finrank F (Hsp P) ≤ Module.finrank F E := by
  classical
  let T0 : Submodule F (V n) := E.comap itL
  let B : Submodule F (V n) := E.map pbL
  let U : Submodule F (V n) := T0 ⊔ B

  let ρ : E →ₗ[F] V n := pbL.comp E.subtype
  have rn := LinearMap.finrank_range_add_finrank_ker ρ
  have hrange : LinearMap.range ρ = B := by
    ext v
    simp [B, ρ]
  have hB : Module.finrank F B ≤ Module.finrank F (LinearMap.range ρ) := by
    rw [hrange]
  have hT : Module.finrank F T0 ≤ Module.finrank F (LinearMap.ker ρ) := by
    let σ : T0 →ₗ[F] LinearMap.ker ρ :=
      LinearMap.codRestrict (LinearMap.ker ρ)
        (LinearMap.codRestrict E (itL.comp T0.subtype) (fun t => t.2))
        (fun t => by
          rw [LinearMap.mem_ker]
          funext i
          rfl)
    apply LinearMap.finrank_le_finrank_of_injective (f := σ)
    intro s t hst
    apply Subtype.ext
    have h1 := congrArg (fun z : LinearMap.ker ρ => ((z : E) : JV n)) hst
    funext i
    have := congrFun h1 (Sum.inl i)
    exact this
  have hU : Module.finrank F ↥(T0 ⊔ B) ≤ Module.finrank F E := by
    have := Submodule.finrank_add_le_finrank_add_finrank T0 B
    omega
  refine le_trans ?_ hU
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro v ⟨K, hK, j, rfl⟩
  show (fun i => K i j) ∈ U
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  set y : V n := fun i => φ (fun j => if i = j then 1 else 0) with hy
  have hφy : ∀ v, φ v = v ⬝ᵥ y := fun v => dual_dot φ v
  have perpB : ∀ e ∈ E, (fun i => e (Sum.inr i)) ⬝ᵥ y = 0 := by
    intro e he
    rw [← hφy]
    exact hφ _ (Submodule.mem_sup_right (Submodule.mem_map_of_mem he))
  have perpT : ∀ t : V n, itL t ∈ E → t ⬝ᵥ y = 0 := by
    intro t ht
    rw [← hφy]
    exact hφ _ (Submodule.mem_sup_left ht)

  let fL : E →ₗ[F] F :=
    { toFun := fun e => (fun i => (e : JV n) (Sum.inl i)) ⬝ᵥ y
      map_add' := fun a b => by
        show (fun i => a.1 (Sum.inl i) + b.1 (Sum.inl i)) ⬝ᵥ y = _
        rw [show (fun i => a.1 (Sum.inl i) + b.1 (Sum.inl i)) =
          (fun i => a.1 (Sum.inl i)) + (fun i => b.1 (Sum.inl i)) from rfl, add_dotProduct]
      map_smul' := fun c a => by
        show (fun i => c * a.1 (Sum.inl i)) ⬝ᵥ y = c • _
        rw [show (fun i => c * a.1 (Sum.inl i)) = c • (fun i => a.1 (Sum.inl i)) from rfl,
          smul_dotProduct] }
  have hker : LinearMap.ker ρ ≤ LinearMap.ker fL := by
    intro e he
    rw [LinearMap.mem_ker] at he ⊢
    have hb : ∀ i, (e : JV n) (Sum.inr i) = 0 := fun i => congrFun he i
    have hmem : itL (fun i => (e : JV n) (Sum.inl i)) ∈ E := by
      have : itL (fun i => (e : JV n) (Sum.inl i)) = (e : JV n) := by
        funext j
        cases j with
        | inl i => rfl
        | inr i => exact (hb i).symm
      rw [this]
      exact e.2
    exact perpT _ hmem
  obtain ⟨g, hg⟩ := factor ρ fL hker
  set z : V n := fun i => g (fun j => if i = j then 1 else 0) with hz
  have hgz : ∀ v, g v = v ⬝ᵥ z := fun v => dual_dot g v
  have zprop : ∀ e ∈ E, (fun i => e (Sum.inr i)) ⬝ᵥ z = (fun i => e (Sum.inl i)) ⬝ᵥ y := by
    intro e he
    rw [← hgz]
    exact hg ⟨e, he⟩
  let yt : JV n := Sum.elim y z
  let yb : JV n := Sum.elim 0 y
  have perp_yt : ∀ e ∈ E, yt ⬝ᵥ e = 0 := by
    intro e he
    rw [split_vec e, se_dot, dotProduct_comm y, dotProduct_comm z, zprop e he, two_zero]
  have perp_yb : ∀ e ∈ E, yb ⬝ᵥ e = 0 := by
    intro e he
    rw [split_vec e, se_dot, zero_dotProduct, zero_add, dotProduct_comm]
    exact perpB e he

  have keyx : ∀ x : V n, x ⬝ᵥ (K *ᵥ y) = 0 := by
    intro x
    let xt : JV n := Sum.elim x 0
    let xb : JV n := Sum.elim 0 x

    have gen : ∀ (u w u' w' : JV n),
        (∀ A K' : Mat n, Alt A → K' ∈ P →
          bil u w (Matrix.fromBlocks A K' K' 0) = bil u' w' (Matrix.fromBlocks A K' K' 0)) →
        (∀ X ∈ Gset E, bil u w X = bil u' w' X) →
        ∀ X ∈ Wsp P ⊔ freeSp E, bil u w X = bil u' w' X := by
      intro u w u' w' h1 h2 X hX
      have := vanish_L P E (bil u w - bil u' w')
        (fun A K' hA hK' => by rw [LinearMap.sub_apply, sub_eq_zero]; exact h1 A K' hA hK')
        (fun X hX => by rw [LinearMap.sub_apply, sub_eq_zero]; exact h2 X hX) X hX
      rwa [LinearMap.sub_apply, sub_eq_zero] at this
    have gen0 : ∀ (u w : JV n),
        (∀ A K' : Mat n, Alt A → K' ∈ P → bil u w (Matrix.fromBlocks A K' K' 0) = 0) →
        (∀ X ∈ Gset E, bil u w X = 0) →
        ∀ X ∈ Wsp P ⊔ freeSp E, bil u w X = 0 :=
      fun u w h1 h2 X hX => vanish_L P E (bil u w) h1 h2 X hX
    have Gyt_r : ∀ u, ∀ X ∈ Gset E, bil u yt X = 0 := fun u X hX => Gset_right hX u yt perp_yt
    have Gyb_r : ∀ u, ∀ X ∈ Gset E, bil u yb X = 0 := fun u X hX => Gset_right hX u yb perp_yb
    have Gyt_l : ∀ w, ∀ X ∈ Gset E, bil yt w X = 0 := fun w X hX => Gset_left hX yt w perp_yt
    have Gyb_l : ∀ w, ∀ X ∈ Gset E, bil yb w X = 0 := fun w X hX => Gset_left hX yb w perp_yb
    have F30 := gen yb xt xt yb
      (fun A K' hA hK' => by
        simp only [bil_apply, yb, xt, fb_mulVec, se_dot, Matrix.mulVec_zero, zero_dotProduct,
          dotProduct_zero, add_zero, zero_add]
        exact sym_swap K' (hP K' hK').1 y x)
      (fun X hX => by rw [Gyb_l _ X hX, Gyb_r _ X hX])
    have F12 := gen xb yt xt yb
      (fun A K' hA hK' => by
        simp only [bil_apply, yb, xt, xb, yt, fb_mulVec, se_dot, Matrix.mulVec_zero,
          zero_dotProduct, dotProduct_zero, add_zero, zero_add, Matrix.zero_mulVec])
      (fun X hX => by rw [Gyt_r _ X hX, Gyb_r _ X hX])
    have F21 := gen yt xb xt yb
      (fun A K' hA hK' => by
        simp only [bil_apply, yb, xt, xb, yt, fb_mulVec, se_dot, Matrix.mulVec_zero,
          zero_dotProduct, dotProduct_zero, add_zero, zero_add, Matrix.zero_mulVec]
        exact sym_swap K' (hP K' hK').1 y x)
      (fun X hX => by rw [Gyt_l _ X hX, Gyb_r _ X hX])
    have F13 := gen0 xb yb
      (fun A K' hA hK' => by
        simp [bil_apply, yb, xb, fb_mulVec, se_dot])
      (fun X hX => Gyb_r _ X hX)
    have F31 := gen0 yb xb
      (fun A K' hA hK' => by
        simp [bil_apply, yb, xb, fb_mulVec, se_dot])
      (fun X hX => Gyb_l _ X hX)
    have F22 := gen0 yt yt
      (fun A K' hA hK' => by
        simp only [bil_apply, yt, fb_mulVec, se_dot, Matrix.zero_mulVec, add_zero,
          dotProduct_add, alt_quad A hA y, zero_add]
        rw [sym_swap K' (hP K' hK').1 z y, two_zero])
      (fun X hX => Gyt_r _ X hX)
    have F23 := gen0 yt yb
      (fun A K' hA hK' => by
        simp only [bil_apply, yt, yb, fb_mulVec, se_dot, Matrix.zero_mulVec, Matrix.mulVec_zero, add_zero, zero_add, dotProduct_add, dotProduct_zero]
        exact alt_quad K' (hP K' hK') y)
      (fun X hX => Gyb_r _ X hX)
    have F32 := gen0 yb yt
      (fun A K' hA hK' => by
        simp only [bil_apply, yt, yb, fb_mulVec, se_dot, Matrix.zero_mulVec, Matrix.mulVec_zero, add_zero, zero_add, dotProduct_add, dotProduct_zero, zero_dotProduct]
        exact alt_quad K' (hP K' hK') y)
      (fun X hX => Gyb_l _ X hX)
    have F33 := gen0 yb yb
      (fun A K' hA hK' => by
        simp [bil_apply, yb, fb_mulVec, se_dot])
      (fun X hX => Gyb_r _ X hX)

    have hS : ∀ X ∈ {X : Big n | X ∈ Wsp P ⊔ freeSp E ∧ X.rank ≤ 2}, bil xt yb X = 0 := by
      rintro X ⟨hXL, hr⟩
      by_contra hne
      have h1 : bil xt yb X = 1 := by
        revert hne
        generalize bil xt yb X = c
        revert c; decide
      have := rank_four X xt xb yt yb h1
        (by rw [← bil_apply, F30 X hXL]; exact h1)
        (by rw [← bil_apply, F12 X hXL]; exact h1)
        (by rw [← bil_apply, F21 X hXL]; exact h1)
        (F13 X hXL) (F31 X hXL) (F22 X hXL) (F23 X hXL) (F32 X hXL) (F33 X hXL)
      omega
    have hspan : Submodule.span F {X : Big n | X ∈ Wsp P ⊔ freeSp E ∧ X.rank ≤ 2} ≤
        LinearMap.ker (bil xt yb) := Submodule.span_le.mpr hS
    have X0mem : Matrix.fromBlocks (0 : Mat n) K K 0 ∈ Wsp P ⊔ freeSp E := by
      apply Submodule.mem_sup_left
      apply Submodule.subset_span
      refine ⟨0, K, ⟨by simp, fun i => rfl⟩, hK, rfl⟩
    rw [hL] at X0mem
    have := hspan X0mem
    rw [LinearMap.mem_ker, bil_apply] at this
    simpa [xt, yb, fb_mulVec, se_dot] using this
  have Ky : K *ᵥ y = 0 := by
    funext i
    have := keyx (Pi.single i 1)
    rwa [single_dotProduct, one_mul] at this
  rw [hφy]
  have hsym := (hP K hK).1
  have : (fun i => K i j) ⬝ᵥ y = (K *ᵥ y) j := by
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    have := congrFun (congrFun hsym j) i
    simp only [Matrix.transpose_apply] at this
    rw [this]
  rw [this, Ky]
  rfl

end PEqualNP.Outside.L_meta_33608_aux.Active
namespace PEqualNP.Outside.L_meta_33608_aux.Active
open Matrix
variable {n : ℕ}
theorem free_le (P : Submodule F (Mat n)) (E : Submodule F (JV n)) : freeSp E ≤ Submodule.span F {X : Big n | X ∈ Wsp P ⊔ freeSp E ∧ X.rank ≤ 2} := by
  classical
  set L := Wsp P ⊔ freeSp E with hLdef
  set S := {X : Big n | X ∈ L ∧ X.rank ≤ 2} with hSdef
  have inS : ∀ X, X ∈ L → X.rank ≤ 2 → X ∈ Submodule.span F S :=
    fun X h r => Submodule.subset_span ⟨h, r⟩
  have hFle : freeSp E ≤ Submodule.span F S := by
    apply Submodule.span_le.mpr
    intro X hX
    obtain ⟨q, hq⟩ := E.exists_isCompl
    let π := E.projection q hq
    let ev : Fin n ⊕ Fin n → JV n := fun j k => if j = k then 1 else 0
    have hX_eq : X = ∑ j, Matrix.vecMulVec (fun i => X i j) (π (ev j)) := by
      ext i k
      have hrow : π (fun j => X i j) = (fun j => X i j) :=
        Submodule.projection_apply_left hq ⟨_, hX.2 i⟩
      have hsum : π (fun j => X i j) = ∑ j, X i j • π (ev j) := by
        conv_lhs => rw [pi_eq_sum_univ (fun j => X i j)]
        rw [map_sum]
        simp only [map_smul]
        rfl
      have := congrFun (hrow.symm.trans hsum) k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [Matrix.sum_apply]
      simp only [Matrix.vecMulVec_apply]
      exact this
    rw [hX_eq]
    apply Submodule.sum_mem
    intro j _
    have hu : (fun i => X i j) ∈ E := hX.1 j
    have hv : π (ev j) ∈ E := Submodule.projection_apply_mem hq _
    have hG : Matrix.vecMulVec (fun i => X i j) (π (ev j)) ∈ Gset E := by
      refine ⟨fun k => ?_, fun i => ?_⟩
      · have : (fun i => Matrix.vecMulVec (fun i => X i j) (π (ev j)) i k) =
            (π (ev j) k) • (fun i => X i j) := by
          funext i; simp [Matrix.vecMulVec_apply, mul_comm]
        rw [this]; exact E.smul_mem _ hu
      · have : (fun k => Matrix.vecMulVec (fun i => X i j) (π (ev j)) i k) =
            (X i j) • π (ev j) := by
          funext k; simp [Matrix.vecMulVec_apply]
        rw [this]; exact E.smul_mem _ hv
    exact inS _ (Submodule.mem_sup_right (Submodule.subset_span hG))
      ((Matrix.rank_vecMulVec_le _ _).trans (by norm_num))
  exact hFle

open Module

theorem quotient_bound (W : Submodule F (Big n)) {q : ℕ} (R : Fin q → Big n)
    (hWS : W ≤ Submodule.span F (Set.range R)) :
    finrank F ((Submodule.span F (Set.range R)).map W.mkQ) ≤ q - finrank F W := by
  classical
  set S := Submodule.span F (Set.range R)
  have hS : finrank F S ≤ q := by
    simpa only [S, Set.finrank, Fintype.card_fin] using (finrank_range_le_card (R := F) R)
  let π := W.mkQ.domRestrict S
  have h := LinearMap.finrank_range_add_finrank_ker π
  have hr : LinearMap.range π = S.map W.mkQ := by
    ext y; simp [π, Submodule.mem_map]
  have hk : finrank F (LinearMap.ker π) = finrank F W := by
    let e : W →ₗ[F] LinearMap.ker π :=
      { toFun := fun x => ⟨⟨x.1, hWS x.2⟩, (Submodule.Quotient.mk_eq_zero W).mpr x.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hb : Function.Bijective e := by
      constructor
      · intro x y h; exact Subtype.ext (congrArg (fun z => z.1.1) h)
      · rintro ⟨⟨x, hx⟩, hker⟩
        exact ⟨⟨x, (Submodule.Quotient.mk_eq_zero W).mp hker⟩, rfl⟩
    exact (LinearEquiv.ofBijective e hb).finrank_eq.symm
  rw [hr, hk] at h
  omega

theorem supplement (W : Submodule F (Big n)) {q : ℕ} (R : Fin q → Big n)
    (hWS : W ≤ Submodule.span F (Set.range R)) :
    ∃ (s : ℕ) (a : Fin s → Fin q), s ≤ q - finrank F W ∧
      Submodule.span F (Set.range R) ≤ W ⊔ Submodule.span F (Set.range (R ∘ a)) := by
  classical
  let U := Set.range (W.mkQ ∘ R)
  obtain ⟨b, hb, hsp, _⟩ := Submodule.exists_fun_fin_finrank_span_eq F U
  choose a ha using hb
  have eqU : Submodule.span F U = (Submodule.span F (Set.range R)).map W.mkQ := by
    rw [← Submodule.span_image, ← Set.range_comp]
  refine ⟨_, a, eqU ▸ quotient_bound W R hWS, ?_⟩
  have eqB : W.mkQ ∘ (R ∘ a) = b := funext ha
  rw [← Submodule.comap_map_mkQ, Submodule.map_le_iff_le_comap.symm]
  rw [← eqU, ← Submodule.span_image, ← Set.range_comp, eqB, hsp]

noncomputable def sides (X : Big n) : Submodule F (JV n) :=
  Submodule.span F (Set.range X.col) ⊔ Submodule.span F (Set.range X.row)

theorem dim_sides (X : Big n) : finrank F (sides X) ≤ 2 * X.rank := by
  unfold sides
  rw [two_mul]
  convert Submodule.finrank_add_le_finrank_add_finrank
    (Submodule.span F (Set.range X.col)) (Submodule.span F (Set.range X.row)) using 1
  rw [← Matrix.rank_eq_finrank_span_cols, ← Matrix.rank_eq_finrank_span_row]

theorem dim_sides_sup {s : ℕ} (B : Fin s → Big n) (h : ∀ i, (B i).rank ≤ 2) (I : Finset (Fin s)) :
    finrank F (I.sup (fun i => sides (B i)) : Submodule F (JV n)) ≤ 4 * I.card := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.sup_insert, Finset.card_insert_of_notMem hi]
    have e := Submodule.finrank_add_le_finrank_add_finrank (sides (B i)) (I.sup fun j => sides (B j))
    have := dim_sides (B i)
    have := h i
    omega

theorem main (P : Submodule F (Mat n)) (hP : ∀ K ∈ P, Alt K)
    (q : ℕ) (R : Fin q → Big n) (hR : ∀ i, (R i).rank ≤ 2)
    (hWS : Wsp P ≤ Submodule.span F (Set.range R)) :
    finrank F (Hsp P) ≤ 4 * (q - finrank F (Wsp P)) := by
  classical
  obtain ⟨s, a, hs, hsup⟩ := supplement (Wsp P) R hWS
  let E := Finset.univ.sup fun i => sides (R (a i))
  have hE : finrank F E ≤ 4 * s := by
    simpa using dim_sides_sup (R ∘ a) (fun i => hR (a i)) Finset.univ
  have hfree : Submodule.span F (Set.range (R ∘ a)) ≤ freeSp E := by
    apply Submodule.span_le.mpr
    rintro X ⟨i, rfl⟩
    have hle : sides (R (a i)) ≤ E := Finset.le_sup (f := fun j => sides (R (a j))) (Finset.mem_univ i)
    apply Submodule.subset_span
    exact ⟨fun j => hle (Submodule.mem_sup_left (Submodule.subset_span ⟨j, rfl⟩)),
      fun j => hle (Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩))⟩
  have hRL := hsup.trans (sup_le_sup_left hfree (Wsp P))
  apply (dir1 P hP E ?_).trans (hE.trans (Nat.mul_le_mul_left _ hs))
  apply le_antisymm
  · apply sup_le _ (free_le P E)
    apply hWS.trans
    apply Submodule.span_le.mpr
    rintro X ⟨i, rfl⟩
    exact Submodule.subset_span ⟨hRL (Submodule.subset_span ⟨i, rfl⟩), hR i⟩
  · exact Submodule.span_le.mpr (fun X hX => hX.1)

end PEqualNP.Outside.L_meta_33608_aux.Active

namespace PEqualNP.Outside.L_meta_33608_aux.Extract

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Matrix

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 :=
  match a with
  | ⟨0, _⟩ => Or.inl rfl
  | ⟨1, _⟩ => Or.inr rfl

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

lemma zmod2_sub_eq_add (a b : ZMod 2) : a - b = a + b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

lemma b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> simp [b2z] at h ⊢

lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_decide_ne_zero (a : ZMod 2) [Decidable (a ≠ 0)] : b2z (decide (a ≠ 0)) = a := by
  rcases zmod2_cases a with rfl | rfl <;> simp [b2z]

def nonlin (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depthsOf (width : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlin g).toNat])
    (List.replicate width 0)

def wiresOf (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma depthsOf_length (width : ℕ) (gs : List Gate) :
    (depthsOf width gs).length = width + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [depthsOf]
  | append_singleton gs g ih =>
    simp only [depthsOf, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton] at ih ⊢
    omega

lemma wiresOf_length (gs : List Gate) (x : List Bool) :
    (wiresOf gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wiresOf]
  | append_singleton gs g ih =>
    simp only [wiresOf, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_singleton] at ih ⊢
    omega

lemma getD_append_left {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_last {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_of_ge_length {α : Type*} (l : List α) (i : ℕ) (d : α) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma oneEach_length {n m : ℕ} (x : Fin n) (y : Fin m) :
    (oneEach x y).length = n + m := by
  simp [oneEach]

lemma wiresOf_append_prefix (gs₁ gs₂ : List Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + gs₁.length) :
    (wiresOf (gs₁ ++ gs₂) x).getD w false = (wiresOf gs₁ x).getD w false := by
  induction gs₂ using List.reverseRecOn with
  | nil => simp
  | append_singleton gs₂ g ih =>
    have h1 : gs₁ ++ (gs₂ ++ [g]) = (gs₁ ++ gs₂) ++ [g] := (List.append_assoc _ _ _).symm
    have hstep : wiresOf ((gs₁ ++ gs₂) ++ [g]) x =
        wiresOf (gs₁ ++ gs₂) x ++ [g.op.eval (g.inputs.map fun i => (wiresOf (gs₁ ++ gs₂) x).getD i false)] := by
      simp [wiresOf, List.foldl_append]
    rw [h1, hstep, getD_append_left _ _ _ _ (by rw [wiresOf_length, List.length_append]; omega)]
    exact ih

lemma depthsOf_append_prefix (width : ℕ) (gs₁ gs₂ : List Gate) (w : ℕ)
    (hw : w < width + gs₁.length) :
    (depthsOf width (gs₁ ++ gs₂)).getD w 0 = (depthsOf width gs₁).getD w 0 := by
  induction gs₂ using List.reverseRecOn with
  | nil => simp
  | append_singleton gs₂ g ih =>
    have h1 : gs₁ ++ (gs₂ ++ [g]) = (gs₁ ++ gs₂) ++ [g] := (List.append_assoc _ _ _).symm
    have hstep : depthsOf width ((gs₁ ++ gs₂) ++ [g]) =
        depthsOf width (gs₁ ++ gs₂) ++
          [(g.inputs.map (fun a => (depthsOf width (gs₁ ++ gs₂)).getD a 0)).foldr max 0 + (nonlin g).toNat] := by
      simp [depthsOf, List.foldl_append]
    rw [h1, hstep, getD_append_left _ _ _ _ (by rw [depthsOf_length, List.length_append]; omega)]
    exact ih

lemma b2z_unary_affine (f : Bool → Bool) :
    ∃ c0 c1 : ZMod 2, ∀ u : Bool, b2z (f u) = c0 + c1 * b2z u := by
  refine ⟨b2z (f false), b2z (f true) + b2z (f false), ?_⟩
  intro u
  cases h0 : f false <;> cases h1 : f true <;> cases u <;> simp only [h0, h1, b2z] <;> decide

lemma b2z_binary_poly (f : Bool → Bool → Bool) :
    ∃ c0 c1 c2 : ZMod 2, ∀ u v : Bool,
      b2z (f u v) = c0 + c1 * b2z u + c2 * b2z v +
        b2z (xor (xor (f false false) (f false true)) (xor (f true false) (f true true))) *
          (b2z u * b2z v) := by
  refine ⟨b2z (f false false),
    b2z (f true false) + b2z (f false false),
    b2z (f false true) + b2z (f false false), ?_⟩
  intro u v
  cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;>
    cases u <;> cases v <;> simp only [h00, h01, h10, h11, b2z] <;> decide

abbrev Quad (n m : ℕ) :=
  (Fin n → ZMod 2) × (Fin m → ZMod 2) × (Fin n → ZMod 2) × (Fin m → ZMod 2)

def evalQuad {n m : ℕ} (q : Quad n m) (x : Fin n) (y : Fin m) : ZMod 2 :=
  q.1 x * q.2.1 y + q.2.2.1 x * q.2.2.2 y

lemma circuit_depth1_decomp (n m : ℕ) (gs : List Gate)
    (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ qs : List (Quad n m),
      qs.length ≤ gs.countP nonlin ∧
      (∀ idx : ℕ, (depthsOf (n + m) gs).getD idx 0 = 0 →
        ∃ (α : Fin n → ZMod 2) (β : Fin m → ZMod 2),
          ∀ (x : Fin n) (y : Fin m), b2z ((wiresOf gs (oneEach x y)).getD idx false) = α x + β y) ∧
      (∀ idx : ℕ, (depthsOf (n + m) gs).getD idx 0 ≤ 1 →
        ∃ (mask : Fin qs.length → ZMod 2) (α : Fin n → ZMod 2) (β : Fin m → ZMod 2),
          ∀ (x : Fin n) (y : Fin m), b2z ((wiresOf gs (oneEach x y)).getD idx false) =
            α x + β y + ∑ p : Fin qs.length, mask p * evalQuad (qs.get p) x y) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨[], by simp, ?_, ?_⟩
    · intro idx _
      by_cases h1 : idx < n
      · refine ⟨fun x => b2z (decide (x.val = idx)), fun _ => 0, fun x y => ?_⟩
        simp only [wiresOf, List.foldl_nil, oneEach, add_zero]
        have hlen : (List.ofFn (fun i : Fin n => decide (i = x))).length = n := by simp
        rw [getD_append_left _ _ _ _ (by omega)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h1, Option.getD_some]
        have hiff : ((⟨idx, h1⟩ : Fin n) = x) ↔ x.val = idx :=
          ⟨fun h => by rw [← h], fun h => Fin.ext h.symm⟩
        simp [hiff]
      · by_cases h2 : idx < n + m
        · refine ⟨fun _ => 0, fun y => b2z (decide (y.val = idx - n)), fun x y => ?_⟩
          simp only [wiresOf, List.foldl_nil, oneEach, zero_add]
          have hlen1 : (List.ofFn (fun i : Fin n => decide (i = x))).length = n := by simp
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen1]; omega)]
          simp only [hlen1, List.getElem?_ofFn, dif_pos (by omega : idx - n < m), Option.getD_some]
          have hiff : ((⟨idx - n, by omega⟩ : Fin m) = y) ↔ y.val = idx - n :=
            ⟨fun h => by rw [← h], fun h => Fin.ext h.symm⟩
          simp [hiff]
        · refine ⟨fun _ => 0, fun _ => 0, fun x y => ?_⟩
          simp only [wiresOf, List.foldl_nil, add_zero]
          rw [getD_of_ge_length _ _ _ (by rw [oneEach_length]; omega)]
          rfl
    · intro idx _
      by_cases h1 : idx < n
      · refine ⟨Fin.elim0, fun x => b2z (decide (x.val = idx)), fun _ => 0, fun x y => ?_⟩
        simp only [wiresOf, List.foldl_nil, oneEach, Finset.sum_empty, add_zero]
        have hlen : (List.ofFn (fun i : Fin n => decide (i = x))).length = n := by simp
        rw [getD_append_left _ _ _ _ (by omega)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos h1, Option.getD_some]
        have hiff : ((⟨idx, h1⟩ : Fin n) = x) ↔ x.val = idx :=
          ⟨fun h => by rw [← h], fun h => Fin.ext h.symm⟩
        simp [hiff]
      · by_cases h2 : idx < n + m
        · refine ⟨Fin.elim0, fun _ => 0, fun y => b2z (decide (y.val = idx - n)), fun x y => ?_⟩
          simp only [wiresOf, List.foldl_nil, oneEach, Finset.sum_empty, zero_add, add_zero]
          have hlen1 : (List.ofFn (fun i : Fin n => decide (i = x))).length = n := by simp
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen1]; omega)]
          simp only [hlen1, List.getElem?_ofFn, dif_pos (by omega : idx - n < m), Option.getD_some]
          have hiff : ((⟨idx - n, by omega⟩ : Fin m) = y) ↔ y.val = idx - n :=
            ⟨fun h => by rw [← h], fun h => Fin.ext h.symm⟩
          simp [hiff]
        · refine ⟨Fin.elim0, fun _ => 0, fun _ => 0, fun x y => ?_⟩
          simp only [wiresOf, List.foldl_nil, Finset.sum_empty, add_zero]
          rw [getD_of_ge_length _ _ _ (by rw [oneEach_length]; omega)]
          rfl
  | append_singleton gs g ih =>
    have hfan_gs : ∀ g' ∈ gs, g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_append_left _ hg')
    have hfan_g : g.inputs.length ≤ 2 := hfan g (List.mem_append_right _ List.mem_cons_self)
    rcases ih hfan_gs with ⟨qs, hqs_len, ih0, ih1⟩
    set curLen := (n + m) + gs.length
    have hd_len : (depthsOf (n + m) gs).length = curLen := depthsOf_length (n + m) gs
    have hw_len : ∀ (x : Fin n) (y : Fin m), (wiresOf gs (oneEach x y)).length = curLen := fun x y => by
      rw [wiresOf_length, oneEach_length]
    have hd_step : depthsOf (n + m) (gs ++ [g]) =
        depthsOf (n + m) gs ++
          [(g.inputs.map (fun a => (depthsOf (n + m) gs).getD a 0)).foldr max 0 + (nonlin g).toNat] := by
      simp [depthsOf, List.foldl_append]
    have hw_step : ∀ (x : Fin n) (y : Fin m), wiresOf (gs ++ [g]) (oneEach x y) =
        wiresOf gs (oneEach x y) ++
          [g.op.eval (g.inputs.map fun i => (wiresOf gs (oneEach x y)).getD i false)] := by
      intro x y; simp [wiresOf, List.foldl_append]
    have hcount : (gs ++ [g]).countP nonlin = gs.countP nonlin + (nonlin g).toNat := by
      rw [List.countP_append, List.countP_cons, List.countP_nil]
      cases nonlin g <;> simp
    let d_in := (g.inputs.map (fun a => (depthsOf (n + m) gs).getD a 0)).foldr max 0
    have hd_new : (depthsOf (n + m) (gs ++ [g])).getD curLen 0 = d_in + (nonlin g).toNat := by
      rw [hd_step, ← hd_len, getD_append_last]
    have hw_new : ∀ (x : Fin n) (y : Fin m),
        (wiresOf (gs ++ [g]) (oneEach x y)).getD curLen false =
          g.op.eval (g.inputs.map fun i => (wiresOf gs (oneEach x y)).getD i false) := by
      intro x y
      rw [hw_step x y, ← hw_len x y, getD_append_last]
    have hd_old : ∀ idx < curLen,
        (depthsOf (n + m) (gs ++ [g])).getD idx 0 = (depthsOf (n + m) gs).getD idx 0 := by
      intro idx hlt
      rw [hd_step, getD_append_left _ _ _ _ (by omega)]
    have hw_old : ∀ idx < curLen, ∀ (x : Fin n) (y : Fin m),
        (wiresOf (gs ++ [g]) (oneEach x y)).getD idx false =
          (wiresOf gs (oneEach x y)).getD idx false := by
      intro idx hlt x y
      rw [hw_step x y, getD_append_left _ _ _ _ (by rw [hw_len x y]; omega)]
    have hw_hi : ∀ idx, curLen < idx → ∀ (x : Fin n) (y : Fin m),
        (wiresOf (gs ++ [g]) (oneEach x y)).getD idx false = false := by
      intro idx hgt x y
      rw [getD_of_ge_length _ _ _ (by rw [wiresOf_length, oneEach_length, List.length_append, List.length_singleton]; omega)]
    cases hnl : nonlin g
    · refine ⟨qs, by rw [hcount, hnl]; simp; exact hqs_len, ?_, ?_⟩
      · intro idx hdep0
        by_cases hlt : idx < curLen
        · rw [hd_old idx hlt] at hdep0
          rcases ih0 idx hdep0 with ⟨α, β, hαβ⟩
          exact ⟨α, β, fun x y => by rw [hw_old idx hlt x y, hαβ x y]⟩
        · by_cases hgt : curLen < idx
          · exact ⟨fun _ => 0, fun _ => 0, fun x y => by rw [hw_hi idx hgt x y]; simp [b2z]⟩
          · have heq : idx = curLen := by omega
            subst heq
            rw [hd_new, hnl] at hdep0
            simp only [Bool.toNat_false, add_zero] at hdep0
            rcases hgs_in : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
            · refine ⟨fun _ => b2z (g.op.eval []), fun _ => 0, fun x y => ?_⟩
              rw [hw_new x y, hgs_in]; simp
            · have ha0 : (depthsOf (n + m) gs).getD a 0 = 0 := by
                simp only [d_in, hgs_in, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdep0
                omega
              rcases ih0 a ha0 with ⟨α, β, hαβ⟩
              rcases b2z_unary_affine (fun u => g.op.eval [u]) with ⟨c0, c1, haff⟩
              refine ⟨fun x => c0 + c1 * α x, fun y => c1 * β y, fun x y => ?_⟩
              rw [hw_new x y, hgs_in, List.map_cons, List.map_nil, haff, hαβ x y]
              ring
            · have hab0 : max ((depthsOf (n + m) gs).getD a 0) ((depthsOf (n + m) gs).getD b 0) = 0 := by
                simp only [d_in, hgs_in, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdep0
                omega
              have ha0 : (depthsOf (n + m) gs).getD a 0 = 0 := by omega
              have hb0 : (depthsOf (n + m) gs).getD b 0 = 0 := by omega
              rcases ih0 a ha0 with ⟨α1, β1, h1⟩
              rcases ih0 b hb0 with ⟨α2, β2, h2⟩
              rcases b2z_binary_poly (fun u v => g.op.eval [u, v]) with ⟨c0, c1, c2, hpoly⟩
              have hnl0 : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                  (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
                cases h : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                    (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
                · rfl
                · simp [nonlin, hgs_in, h] at hnl
              refine ⟨fun x => c0 + c1 * α1 x + c2 * α2 x, fun y => c1 * β1 y + c2 * β2 y, fun x y => ?_⟩
              rw [hw_new x y, hgs_in, List.map_cons, List.map_cons, List.map_nil, hpoly, hnl0, h1 x y, h2 x y]
              simp only [b2z, Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero]
              ring
            · rw [hgs_in] at hfan_g; simp at hfan_g
      · intro idx hdep1
        by_cases hlt : idx < curLen
        · rw [hd_old idx hlt] at hdep1
          rcases ih1 idx hdep1 with ⟨mask, α, β, hαβ⟩
          exact ⟨mask, α, β, fun x y => by rw [hw_old idx hlt x y, hαβ x y]⟩
        · by_cases hgt : curLen < idx
          · exact ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun x y => by rw [hw_hi idx hgt x y]; simp [b2z]⟩
          · have heq : idx = curLen := by omega
            subst heq
            rw [hd_new, hnl] at hdep1
            simp only [Bool.toNat_false, add_zero] at hdep1
            rcases hgs_in : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
            · refine ⟨fun _ => 0, fun _ => b2z (g.op.eval []), fun _ => 0, fun x y => ?_⟩
              rw [hw_new x y, hgs_in]; simp
            · have ha1 : (depthsOf (n + m) gs).getD a 0 ≤ 1 := by
                simp only [d_in, hgs_in, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdep1
                omega
              rcases ih1 a ha1 with ⟨m1, α1, β1, h1⟩
              rcases b2z_unary_affine (fun u => g.op.eval [u]) with ⟨c0, c1, haff⟩
              refine ⟨fun p => c1 * m1 p, fun x => c0 + c1 * α1 x, fun y => c1 * β1 y, fun x y => ?_⟩
              rw [hw_new x y, hgs_in, List.map_cons, List.map_nil, haff, h1 x y]
              simp only [mul_assoc, ← Finset.mul_sum]
              ring
            · have hab1 : max ((depthsOf (n + m) gs).getD a 0) ((depthsOf (n + m) gs).getD b 0) ≤ 1 := by
                simp only [d_in, hgs_in, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdep1
                omega
              have ha1 : (depthsOf (n + m) gs).getD a 0 ≤ 1 := by omega
              have hb1 : (depthsOf (n + m) gs).getD b 0 ≤ 1 := by omega
              rcases ih1 a ha1 with ⟨m1, α1, β1, h1⟩
              rcases ih1 b hb1 with ⟨m2, α2, β2, h2⟩
              rcases b2z_binary_poly (fun u v => g.op.eval [u, v]) with ⟨c0, c1, c2, hpoly⟩
              have hnl0 : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                  (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
                cases h : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                    (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
                · rfl
                · simp [nonlin, hgs_in, h] at hnl
              refine ⟨fun p => c1 * m1 p + c2 * m2 p,
                fun x => c0 + c1 * α1 x + c2 * α2 x, fun y => c1 * β1 y + c2 * β2 y, fun x y => ?_⟩
              rw [hw_new x y, hgs_in, List.map_cons, List.map_cons, List.map_nil, hpoly, hnl0, h1 x y, h2 x y]
              simp only [b2z, Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero]
              have hsum_eq : ∑ p : Fin qs.length, (c1 * m1 p + c2 * m2 p) * evalQuad (qs.get p) x y =
                  c1 * (∑ p : Fin qs.length, m1 p * evalQuad (qs.get p) x y) +
                  c2 * (∑ p : Fin qs.length, m2 p * evalQuad (qs.get p) x y) := by
                simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
              rw [hsum_eq]
              ring
            · rw [hgs_in] at hfan_g; simp at hfan_g
    · have hlen2 : g.inputs.length = 2 := by
        simp only [nonlin, Bool.and_eq_true, beq_iff_eq] at hnl
        exact hnl.1
      have hnl1 : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
          (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = true := by
        simp only [nonlin, Bool.and_eq_true, beq_iff_eq] at hnl
        exact hnl.2
      by_cases hdin0 : d_in = 0
      · rcases hgs_in : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
        · simp [hgs_in] at hlen2
        · simp [hgs_in] at hlen2
        · have hab0 : max ((depthsOf (n + m) gs).getD a 0) ((depthsOf (n + m) gs).getD b 0) = 0 := by
            simp only [d_in, hgs_in, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdin0
            omega
          have ha0 : (depthsOf (n + m) gs).getD a 0 = 0 := by omega
          have hb0 : (depthsOf (n + m) gs).getD b 0 = 0 := by omega
          rcases ih0 a ha0 with ⟨α1, β1, h1⟩
          rcases ih0 b hb0 with ⟨α2, β2, h2⟩
          rcases b2z_binary_poly (fun u v => g.op.eval [u, v]) with ⟨c0, c1, c2, hpoly⟩
          let qNew : Quad n m := (α1, β2, α2, β1)
          let qs' := qs ++ [qNew]
          have hqs'_len : qs'.length = qs.length + 1 := by simp [qs']
          refine ⟨qs', by rw [hcount, hnl, hqs'_len]; simp; exact hqs_len, ?_, ?_⟩
          · intro idx hdep0
            by_cases hlt : idx < curLen
            · rw [hd_old idx hlt] at hdep0
              rcases ih0 idx hdep0 with ⟨α, β, hαβ⟩
              exact ⟨α, β, fun x y => by rw [hw_old idx hlt x y, hαβ x y]⟩
            · by_cases hgt : curLen < idx
              · exact ⟨fun _ => 0, fun _ => 0, fun x y => by rw [hw_hi idx hgt x y]; simp [b2z]⟩
              · have heq : idx = curLen := by omega
                subst heq
                rw [hd_new, hnl] at hdep0
                simp at hdep0
          · intro idx hdep1
            by_cases hlt : idx < curLen
            · rw [hd_old idx hlt] at hdep1
              rcases ih1 idx hdep1 with ⟨mask, α, β, hαβ⟩
              let mask' : Fin qs'.length → ZMod 2 := fun p =>
                if hp : p.val < qs.length then mask ⟨p.val, hp⟩ else 0
              refine ⟨mask', α, β, fun x y => ?_⟩
              rw [hw_old idx hlt x y, hαβ x y]
              congr 1
              have hsum_eq : ∑ p : Fin qs'.length, mask' p * evalQuad (qs'.get p) x y =
                  ∑ p : Fin qs.length, mask p * evalQuad (qs.get p) x y := by
                have hfin : ∑ p : Fin (qs.length + 1),
                    mask' ⟨p.val, by omega⟩ * evalQuad (qs'.get ⟨p.val, by omega⟩) x y =
                    ∑ p : Fin qs'.length, mask' p * evalQuad (qs'.get p) x y :=
                  Finset.sum_bij (fun p _ => ⟨p.val, by omega⟩) (fun _ _ => Finset.mem_univ _)
                    (fun _ _ _ _ h => Fin.ext (Fin.mk.inj h))
                    (fun p _ => ⟨⟨p.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
                    (fun _ _ => rfl)
                rw [← hfin, Fin.sum_univ_castSucc]
                have hlast : mask' ⟨(Fin.last qs.length).val, by omega⟩ = 0 := by simp [mask']
                rw [hlast, zero_mul, add_zero]
                refine Finset.sum_congr rfl fun p _ => ?_
                have hget : qs'.get ⟨p.val, by omega⟩ = qs.get p := by
                  simp [qs', List.get_eq_getElem, List.getElem_append_left p.isLt]
                change mask' ⟨p.val, by omega⟩ * evalQuad (qs'.get ⟨p.val, by omega⟩) x y =
                  mask p * evalQuad (qs.get p) x y
                rw [hget]
                simp [mask', p.isLt]
              exact hsum_eq.symm
            · by_cases hgt : curLen < idx
              · exact ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun x y => by rw [hw_hi idx hgt x y]; simp [b2z]⟩
              · have heq : idx = curLen := by omega
                subst heq
                let pLast : Fin qs'.length := ⟨qs.length, by omega⟩
                refine ⟨fun p => if p = pLast then 1 else 0,
                  fun x => c0 + c1 * α1 x + c2 * α2 x + α1 x * α2 x,
                  fun y => c1 * β1 y + c2 * β2 y + β1 y * β2 y, fun x y => ?_⟩
                rw [hw_new x y, hgs_in, List.map_cons, List.map_cons, List.map_nil, hpoly, hnl1, h1 x y, h2 x y]
                have hsum_single : ∑ p : Fin qs'.length,
                    (if p = pLast then (1 : ZMod 2) else 0) * evalQuad (qs'.get p) x y =
                    evalQuad qNew x y := by
                  rw [Finset.sum_eq_single pLast]
                  · simp only [↓reduceIte, one_mul]
                    have hget : qs'.get pLast = qNew := by
                      simp [qs', pLast, List.get_eq_getElem]
                    rw [hget]
                  · intro p _ hne
                    simp [hne]
                  · intro h; exact (h (Finset.mem_univ pLast)).elim
                rw [hsum_single]
                simp only [b2z, ↓reduceIte, one_mul, evalQuad, qNew]
                ring
        · simp [hgs_in] at hlen2
      · refine ⟨qs, by rw [hcount, hnl]; simp; omega, ?_, ?_⟩
        · intro idx hdep0
          by_cases hlt : idx < curLen
          · rw [hd_old idx hlt] at hdep0
            rcases ih0 idx hdep0 with ⟨α, β, hαβ⟩
            exact ⟨α, β, fun x y => by rw [hw_old idx hlt x y, hαβ x y]⟩
          · by_cases hgt : curLen < idx
            · exact ⟨fun _ => 0, fun _ => 0, fun x y => by rw [hw_hi idx hgt x y]; simp [b2z]⟩
            · have heq : idx = curLen := by omega
              subst heq
              rw [hd_new, hnl] at hdep0
              simp at hdep0
        · intro idx hdep1
          by_cases hlt : idx < curLen
          · rw [hd_old idx hlt] at hdep1
            rcases ih1 idx hdep1 with ⟨mask, α, β, hαβ⟩
            exact ⟨mask, α, β, fun x y => by rw [hw_old idx hlt x y, hαβ x y]⟩
          · by_cases hgt : curLen < idx
            · exact ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun x y => by rw [hw_hi idx hgt x y]; simp [b2z]⟩
            · have heq : idx = curLen := by omega
              subst heq
              rw [hd_new, hnl] at hdep1
              simp only [Bool.toNat_true] at hdep1
              omega

def deltaMat {n m : ℕ} (f : Fin (n + 1) → Fin (m + 1) → ZMod 2)
    (i : Fin n) (j : Fin m) : ZMod 2 :=
  f i.succ j.succ + f i.succ 0 + f 0 j.succ + f 0 0

lemma deltaMat_add {n m : ℕ} (f g : Fin (n + 1) → Fin (m + 1) → ZMod 2)
    (i : Fin n) (j : Fin m) :
    deltaMat (fun x y => f x y + g x y) i j = deltaMat f i j + deltaMat g i j := by
  simp only [deltaMat]; ring

lemma deltaMat_aff {n m : ℕ} (α : Fin (n + 1) → ZMod 2) (β : Fin (m + 1) → ZMod 2)
    (i : Fin n) (j : Fin m) :
    deltaMat (fun x y => α x + β y) i j = 0 := by
  simp only [deltaMat]
  have h1 : α i.succ + β j.succ + (α i.succ + β 0) + (α 0 + β j.succ) + (α 0 + β 0) =
      (α i.succ + α i.succ) + (α 0 + α 0) + (β j.succ + β j.succ) + (β 0 + β 0) := by ring
  rw [h1]
  simp only [zmod2_add_self, add_zero]

lemma deltaMat_outer {n m : ℕ} (u : Fin (n + 1) → ZMod 2) (v : Fin (m + 1) → ZMod 2)
    (i : Fin n) (j : Fin m) :
    deltaMat (fun x y => u x * v y) i j = (u i.succ + u 0) * (v j.succ + v 0) := by
  simp only [deltaMat]; ring

lemma deltaMat_quad {n m : ℕ} (q : Quad (n + 1) (m + 1)) (i : Fin n) (j : Fin m) :
    deltaMat (evalQuad q) i j =
      (q.1 i.succ + q.1 0) * (q.2.1 j.succ + q.2.1 0) +
      (q.2.2.1 i.succ + q.2.2.1 0) * (q.2.2.2 j.succ + q.2.2.2 0) := by
  unfold evalQuad
  rw [deltaMat_add, deltaMat_outer, deltaMat_outer]

lemma deltaMat_sum {n m : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Fin (n + 1) → Fin (m + 1) → ZMod 2) (i : Fin n) (j : Fin m) :
    deltaMat (fun x y => ∑ p ∈ s, f p x y) i j = ∑ p ∈ s, deltaMat (f p) i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [deltaMat]
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    rw [deltaMat_add, ih]

lemma deltaMat_smul {n m : ℕ} (c : ZMod 2)
    (f : Fin (n + 1) → Fin (m + 1) → ZMod 2) (i : Fin n) (j : Fin m) :
    deltaMat (fun x y => c * f x y) i j = c * deltaMat f i j := by
  simp only [deltaMat]; ring

def mkTable {d : ℕ} (H : Matrix (Fin d) (Fin d) (ZMod 2)) (x y : Fin (d + 1)) : Bool :=
  Fin.cases false (fun i => Fin.cases false (fun j => decide (H i j ≠ 0)) y) x

lemma b2z_mkTable_succ {d : ℕ} (H : Matrix (Fin d) (Fin d) (ZMod 2)) (i j : Fin d) :
    b2z (mkTable H i.succ j.succ) = H i j := by
  simp only [mkTable, Fin.cases_succ]
  exact b2z_decide_ne_zero (H i j)

lemma deltaMat_mkTable {d : ℕ} (H : Matrix (Fin d) (Fin d) (ZMod 2)) (i j : Fin d) :
    deltaMat (fun x y => b2z (mkTable H x y)) i j = H i j := by
  simp only [deltaMat, mkTable, Fin.cases_zero, Fin.cases_succ, b2z, Bool.false_eq_true, ↓reduceIte, add_zero]
  exact b2z_decide_ne_zero (H i j)

lemma rank_add_le {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (A B : Matrix m n (ZMod 2)) :
    (A + B).rank ≤ A.rank + B.rank := by
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    change (A + B) *ᵥ x ∈ _
    rw [Matrix.add_mulVec]
    exact Submodule.mem_sup.mpr ⟨A *ᵥ x, ⟨x, rfl⟩, B *ᵥ x, ⟨x, rfl⟩, rfl⟩
  have h1 : (A + B).rank ≤ Module.finrank (ZMod 2)
      ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  have hA : A.rank = Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) := rfl
  have hB : B.rank = Module.finrank (ZMod 2) (LinearMap.range B.mulVecLin) := rfl
  omega

abbrev F := ZMod 2
abbrev Idx (n f : ℕ) := (Fin n ⊕ Fin n) ⊕ Fin f
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) F
abbrev BMat (n f : ℕ) := Matrix (Fin n) (Fin f) F
abbrev Full (n f : ℕ) := Matrix (Idx n f) (Idx n f) F

def alt {n : ℕ} (A : Mat n) := A.transpose = A ∧ ∀ i, A i i = 0
def allowed {n : ℕ} (edges : Finset (Fin n × Fin n)) (K : Mat n) :=
  alt K ∧ ∀ i j, (i,j) ∉ edges → (j,i) ∉ edges → K i j = 0

def block {n f : ℕ} (A K : Mat n) (B : BMat n f) : Full n f :=
  let X := Matrix.fromBlocks A K K (0 : Mat n)
  let Y : Matrix (Fin n ⊕ Fin n) (Fin f) F :=
    fun i j => Sum.elim (fun a => B a j) (fun _ => 0) i
  Matrix.fromBlocks X Y Y.transpose (0 : Matrix (Fin f) (Fin f) F)

def coord {n f : ℕ} : Idx n f ≃ Fin (n+n+f) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin f))).trans finSumFinEquiv

def bank {n : ℕ} (edges : Finset (Fin n × Fin n)) (f t : ℕ) : Prop :=
  let d := n+n+f
  ∃ (C : Circuit) (tap : Mat n → Mat n → BMat n f → ℕ),
    ReadsBack ((d+1)+(d+1)) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlin ≤ t ∧
    ∀ A K B, alt A → allowed edges K →
      (depthsOf ((d+1)+(d+1)) C.gates).getD (tap A K B) 0 ≤ 1 ∧
      Represents (mkTable ((block A K B).submatrix coord.symm coord.symm))
        ⟨C.gates, tap A K B⟩

theorem main {n f t : ℕ} (edges : Finset (Fin n × Fin n)) (h : bank edges f t) :
    ∃ R : Fin t → Full n f, (∀ p, (R p).rank ≤ 2) ∧
      ∀ A K B, alt A → allowed edges K → block A K B ∈ Submodule.span F (Set.range R) := by
  classical
  obtain ⟨C,tap,_,hfan,hcnt,htap⟩ := h
  let d := n+n+f
  obtain ⟨qs,hlen,_,hdec⟩ := circuit_depth1_decomp (d+1) (d+1) C.gates hfan
  let U (u : Fin (d+1) → F) : Idx n f → F := fun i => u (coord i).succ + u 0
  let S (p : Fin qs.length) : Full n f :=
    Matrix.vecMulVec (U (qs.get p).1) (U (qs.get p).2.1) +
    Matrix.vecMulVec (U (qs.get p).2.2.1) (U (qs.get p).2.2.2)
  let R (p : Fin t) : Full n f := if h : p.val < qs.length then S ⟨p.val,h⟩ else 0
  have hlen' : qs.length ≤ t := hlen.trans hcnt
  have inc (p : Fin qs.length) : R (Fin.castLE hlen' p) = S p := by simp [R,p.isLt]
  refine ⟨R, ?_, ?_⟩
  · intro p
    dsimp only [R]
    split
    · exact (rank_add_le _ _).trans (Nat.add_le_add (Matrix.rank_vecMulVec_le _ _)
        (Matrix.rank_vecMulVec_le _ _))
    · simp
  · intro A K B hA hK
    obtain ⟨hd,hr⟩ := htap A K B hA hK
    obtain ⟨mask,α,β,hev⟩ := hdec (tap A K B) hd
    let N : Matrix (Fin d) (Fin d) F := (block A K B).submatrix coord.symm coord.symm
    have hfn : (fun x y => b2z (mkTable N x y)) =
        (fun x y => (α x + β y) + ∑ p : Fin qs.length, mask p * evalQuad (qs.get p) x y) := by
      funext x y
      have hr' : (wiresOf C.gates (oneEach x y)).getD (tap A K B) false = mkTable N x y := hr x y
      rw [← hr']
      exact hev x y
    have heq : block A K B = ∑ p : Fin qs.length, mask p • S p := by
      ext i j
      have hij : block A K B i j = N (coord i) (coord j) := by simp [N]
      rw [hij, ← deltaMat_mkTable N (coord i) (coord j), hfn,
        deltaMat_add, deltaMat_aff, zero_add, deltaMat_sum]
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro p _
      rw [deltaMat_smul, deltaMat_quad]
      rfl
    rw [heq]
    apply Submodule.sum_mem
    intro p _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨Fin.castLE hlen' p, inc p⟩

end PEqualNP.Outside.L_meta_33608_aux.Extract

namespace PEqualNP.Outside.L_meta_33608_aux.Upper.U33608Circuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Matrix

open PEqualNP.Outside.L_meta_33608_aux.Extract

private def goodGates (w : ℕ) (gs : List Gate) : Prop :=
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < w + j) ∧
  (∀ g ∈ gs, g.inputs.length ≤ 2)

private lemma append_gate_good (w : ℕ) (gs : List Gate) (g : Gate)
    (hgood : goodGates w gs) (hfan : g.inputs.length ≤ 2)
    (hback : ∀ i ∈ g.inputs, i < w + gs.length) :
    goodGates w (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [getD_append_left _ _ _ _ hlt] at hi
      exact hgood.1 j hlt i hi
    · have heq : j = gs.length := by omega
      subst heq
      rw [getD_append_last] at hi
      exact hback i hi
  · intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with h | rfl
    · exact hgood.2 g' h
    · exact hfan

private lemma append_constFalse (w : ℕ) (gs : List Gate) (hgood : goodGates w gs) :
    let gs' := gs ++ [⟨GateOp.or, []⟩]
    let out := w + gs.length
    gs.length ≤ gs'.length ∧ goodGates w gs' ∧
    gs'.countP nonlin = gs.countP nonlin ∧
    out < w + gs'.length ∧
    (depthsOf w gs').getD out 0 = 0 ∧
    (∀ u < w + gs.length, (depthsOf w gs').getD u 0 = (depthsOf w gs).getD u 0) ∧
    (∀ (x : List Bool), x.length = w →
      (∀ u < w + gs.length, (wiresOf gs' x).getD u false = (wiresOf gs x).getD u false) ∧
      (wiresOf gs' x).getD out false = false) := by
  intro gs' out
  have hnl : nonlin ⟨GateOp.or, []⟩ = false := by decide
  refine ⟨by simp [gs'], append_gate_good w gs _ hgood (by simp) (fun _ h => by cases h),
    by simp [gs', List.countP_append, hnl], by simp [gs', out], ?_, ?_, ?_⟩
  · simp only [gs', out, depthsOf, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (depthsOf w gs).length = w + gs.length := depthsOf_length w gs
    change ((depthsOf w gs) ++ [_]).getD (w + gs.length) 0 = 0
    rw [← hlen, getD_append_last]
    simp [hnl]
  · intro u hu
    exact depthsOf_append_prefix w gs _ u hu
  · intro x hx
    refine ⟨fun u hu => wiresOf_append_prefix gs _ x u (by omega), ?_⟩
    simp only [gs', out, wiresOf, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (wiresOf gs x).length = w + gs.length := by rw [wiresOf_length, hx]
    change ((wiresOf gs x) ++ [_]).getD (w + gs.length) false = false
    rw [← hlen, getD_append_last]
    rfl

private lemma append_xor2 (w : ℕ) (gs : List Gate) (u v : ℕ)
    (hgood : goodGates w gs) (hu : u < w + gs.length) (hv : v < w + gs.length) :
    let gs' := gs ++ [⟨GateOp.mod 2, [u, v]⟩, ⟨GateOp.not, [w + gs.length]⟩]
    let out := w + gs.length + 1
    gs.length ≤ gs'.length ∧ goodGates w gs' ∧
    gs'.countP nonlin = gs.countP nonlin ∧
    out < w + gs'.length ∧
    (depthsOf w gs').getD out 0 = max ((depthsOf w gs).getD u 0) ((depthsOf w gs).getD v 0) ∧
    (∀ k < w + gs.length, (depthsOf w gs').getD k 0 = (depthsOf w gs).getD k 0) ∧
    (∀ (x : List Bool), x.length = w →
      (∀ k < w + gs.length, (wiresOf gs' x).getD k false = (wiresOf gs x).getD k false) ∧
      (wiresOf gs' x).getD out false = xor ((wiresOf gs x).getD u false) ((wiresOf gs x).getD v false)) := by
  intro gs' out
  have hnl1 : nonlin ⟨GateOp.mod 2, [u, v]⟩ = false := by simp [nonlin]; decide
  have hnl2 : nonlin ⟨GateOp.not, [w + gs.length]⟩ = false := by simp [nonlin]
  have hgs'_eq : gs' = (gs ++ [⟨GateOp.mod 2, [u, v]⟩]) ++ [⟨GateOp.not, [w + gs.length]⟩] := by
    simp [gs']
  have hgood1 : goodGates w (gs ++ [⟨GateOp.mod 2, [u, v]⟩]) :=
    append_gate_good w gs _ hgood (by simp) (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega)
  have hgood2 : goodGates w gs' := by
    rw [hgs'_eq]
    exact append_gate_good w _ _ hgood1 (by simp) (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rw [hi, List.length_append, List.length_singleton]; omega)
  refine ⟨by simp [gs'], hgood2, by simp [gs', List.countP_append, hnl1, hnl2],
    by simp [gs', out]; omega, ?_, ?_, ?_⟩
  · rw [hgs'_eq]
    set gs1 := gs ++ [⟨GateOp.mod 2, [u, v]⟩]
    have hd1_len : (depthsOf w gs1).length = w + gs.length + 1 := by
      rw [depthsOf_length]; simp [gs1]; omega
    have hd0_len : (depthsOf w gs).length = w + gs.length := depthsOf_length w gs
    have hd_mid : (depthsOf w gs1).getD (w + gs.length) 0 =
        max ((depthsOf w gs).getD u 0) ((depthsOf w gs).getD v 0) := by
      have hstep : depthsOf w gs1 = depthsOf w gs ++
          [(([u, v]).map (fun a => (depthsOf w gs).getD a 0)).foldr max 0 + (nonlin ⟨GateOp.mod 2, [u, v]⟩).toNat] := by
        simp [gs1, depthsOf, List.foldl_append]
      rw [hstep, ← hd0_len, getD_append_last, hnl1]
      simp
    have hstep2 : depthsOf w (gs1 ++ [⟨GateOp.not, [w + gs.length]⟩]) = depthsOf w gs1 ++
        [(([w + gs.length]).map (fun a => (depthsOf w gs1).getD a 0)).foldr max 0 +
          (nonlin ⟨GateOp.not, [w + gs.length]⟩).toNat] := by
      simp [depthsOf, List.foldl_append]
    rw [hstep2]
    change (depthsOf w gs1 ++ _).getD (w + gs.length + 1) 0 = _
    rw [← hd1_len, getD_append_last, hnl2]
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_false, add_zero]
    rw [hd_mid]
    omega
  · intro k hk
    exact depthsOf_append_prefix w gs _ k hk
  · intro x hx
    refine ⟨fun k hk => wiresOf_append_prefix gs _ x k (by omega), ?_⟩
    rw [hgs'_eq]
    set gs1 := gs ++ [⟨GateOp.mod 2, [u, v]⟩]
    have hw0_len : (wiresOf gs x).length = w + gs.length := by rw [wiresOf_length, hx]
    have hw1_len : (wiresOf gs1 x).length = w + gs.length + 1 := by
      rw [wiresOf_length, hx]; simp [gs1]; omega
    have hmid : (wiresOf gs1 x).getD (w + gs.length) false =
        (GateOp.mod 2).eval [(wiresOf gs x).getD u false, (wiresOf gs x).getD v false] := by
      have hstep : wiresOf gs1 x = wiresOf gs x ++
          [(GateOp.mod 2).eval (([u, v]).map fun i => (wiresOf gs x).getD i false)] := by
        simp [gs1, wiresOf, List.foldl_append]
      rw [hstep, ← hw0_len, getD_append_last]
      rfl
    have hstep2 : wiresOf (gs1 ++ [⟨GateOp.not, [w + gs.length]⟩]) x = wiresOf gs1 x ++
        [GateOp.not.eval (([w + gs.length]).map fun i => (wiresOf gs1 x).getD i false)] := by
      simp [wiresOf, List.foldl_append]
    rw [hstep2]
    change (wiresOf gs1 x ++ _).getD (w + gs.length + 1) false = _
    rw [← hw1_len, getD_append_last]
    simp only [List.map_cons, List.map_nil]
    rw [hmid]
    generalize (wiresOf gs x).getD u false = bu
    generalize (wiresOf gs x).getD v false = bv
    cases bu <;> cases bv <;> decide

private lemma append_and2 (w : ℕ) (gs : List Gate) (u v : ℕ)
    (hgood : goodGates w gs) (hu : u < w + gs.length) (hv : v < w + gs.length) :
    let gs' := gs ++ [⟨GateOp.and, [u, v]⟩]
    let out := w + gs.length
    gs.length ≤ gs'.length ∧ goodGates w gs' ∧
    gs'.countP nonlin = gs.countP nonlin + 1 ∧
    out < w + gs'.length ∧
    (depthsOf w gs').getD out 0 = max ((depthsOf w gs).getD u 0) ((depthsOf w gs).getD v 0) + 1 ∧
    (∀ k < w + gs.length, (depthsOf w gs').getD k 0 = (depthsOf w gs).getD k 0) ∧
    (∀ (x : List Bool), x.length = w →
      (∀ k < w + gs.length, (wiresOf gs' x).getD k false = (wiresOf gs x).getD k false) ∧
      (wiresOf gs' x).getD out false = ((wiresOf gs x).getD u false && (wiresOf gs x).getD v false)) := by
  intro gs' out
  have hnl : nonlin ⟨GateOp.and, [u, v]⟩ = true := by simp [nonlin]; decide
  refine ⟨by simp [gs'], append_gate_good w gs _ hgood (by simp) (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega),
    by simp [gs', List.countP_append, hnl], by simp [gs', out], ?_, ?_, ?_⟩
  · have hstep : depthsOf w gs' = depthsOf w gs ++
        [(([u, v]).map (fun a => (depthsOf w gs).getD a 0)).foldr max 0 + (nonlin ⟨GateOp.and, [u, v]⟩).toNat] := by
      simp [gs', depthsOf, List.foldl_append]
    have hlen : (depthsOf w gs).length = w + gs.length := depthsOf_length w gs
    rw [hstep]
    change (depthsOf w gs ++ _).getD (w + gs.length) 0 = _
    rw [← hlen, getD_append_last, hnl]
    simp
  · intro k hk
    exact depthsOf_append_prefix w gs _ k hk
  · intro x hx
    refine ⟨fun k hk => wiresOf_append_prefix gs _ x k (by omega), ?_⟩
    have hstep : wiresOf gs' x = wiresOf gs x ++
        [GateOp.and.eval (([u, v]).map fun i => (wiresOf gs x).getD i false)] := by
      simp [gs', wiresOf, List.foldl_append]
    have hlen : (wiresOf gs x).length = w + gs.length := by rw [wiresOf_length, hx]
    rw [hstep]
    change (wiresOf gs x ++ _).getD (w + gs.length) false = _
    rw [← hlen, getD_append_last]
    simp only [List.map_cons, List.map_nil]
    generalize (wiresOf gs x).getD u false = bu
    generalize (wiresOf gs x).getD v false = bv
    cases bu <;> cases bv <;> decide

private lemma exists_xorList (w : ℕ) (gs : List Gate) (ws : List ℕ) (D : ℕ)
    (hgood : goodGates w gs) (hws : ∀ u ∈ ws, u < w + gs.length)
    (hdep : ∀ u ∈ ws, (depthsOf w gs).getD u 0 ≤ D) :
    ∃ (gs' : List Gate) (out : ℕ),
      gs.length ≤ gs'.length ∧ goodGates w gs' ∧
      gs'.countP nonlin = gs.countP nonlin ∧
      out < w + gs'.length ∧
      (depthsOf w gs').getD out 0 ≤ D ∧
      (∀ k < w + gs.length, (depthsOf w gs').getD k 0 = (depthsOf w gs).getD k 0) ∧
      (∀ (x : List Bool), x.length = w →
        (∀ k < w + gs.length, (wiresOf gs' x).getD k false = (wiresOf gs x).getD k false) ∧
        b2z ((wiresOf gs' x).getD out false) = (ws.map (fun u => b2z ((wiresOf gs x).getD u false))).sum) := by
  induction ws with
  | nil =>
    have h := append_constFalse w gs hgood
    refine ⟨_, _, h.1, h.2.1, h.2.2.1, h.2.2.2.1, by rw [h.2.2.2.2.1]; omega, h.2.2.2.2.2.1,
      fun x hx => ⟨(h.2.2.2.2.2.2 x hx).1, by rw [(h.2.2.2.2.2.2 x hx).2]; simp [b2z]⟩⟩
  | cons a t ih =>
    have ha : a < w + gs.length := hws a List.mem_cons_self
    have ha_dep : (depthsOf w gs).getD a 0 ≤ D := hdep a List.mem_cons_self
    rcases ih (fun u hu => hws u (List.mem_cons_of_mem a hu))
      (fun u hu => hdep u (List.mem_cons_of_mem a hu)) with
      ⟨gs1, out1, hlen1, hgood1, hcnt1, hout1, hdep1, hdpref1, hval1⟩
    have h2 := append_xor2 w gs1 a out1 hgood1 (by omega) hout1
    refine ⟨_, _, by omega, h2.2.1, by rw [h2.2.2.1, hcnt1], h2.2.2.2.1, ?_, ?_, ?_⟩
    · rw [h2.2.2.2.2.1, hdpref1 a ha]
      exact max_le ha_dep hdep1
    · intro k hk
      rw [h2.2.2.2.2.2.1 k (by omega), hdpref1 k hk]
    · intro x hx
      refine ⟨fun k hk => by rw [(h2.2.2.2.2.2.2 x hx).1 k (by omega), (hval1 x hx).1 k hk], ?_⟩
      rw [(h2.2.2.2.2.2.2 x hx).2, b2z_xor, (hval1 x hx).1 a ha, (hval1 x hx).2]
      simp

lemma synth_depth1_quads (n m q : ℕ) (qs : List (Quad n m))
    (mask : Fin q → Fin qs.length → ZMod 2)
    (α : Fin q → Fin n → ZMod 2) (β : Fin q → Fin m → ZMod 2) :
    ∃ (C : Circuit) (tap : Fin q → ℕ),
      ReadsBack (n + m) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      C.gates.countP nonlin ≤ qs.length ∧
      ∀ j : Fin q, (depthsOf (n + m) C.gates).getD (tap j) 0 ≤ 1 ∧
        ∀ (x : Fin n) (y : Fin m),
          b2z ((wiresOf C.gates (oneEach x y)).getD (tap j) false) =
            α j x + β j y + ∑ p : Fin qs.length, mask j p * evalQuad (qs.get p) x y := by
  classical
  have hbase_in : ∀ (gs : List Gate) (x : Fin n) (y : Fin m),
      (∀ i : Fin n, (wiresOf gs (oneEach x y)).getD i.val false = decide (i = x)) ∧
      (∀ j : Fin m, (wiresOf gs (oneEach x y)).getD (n + j.val) false = decide (j = y)) := by
    intro gs x y
    constructor
    · intro i
      have h1 := wiresOf_append_prefix [] gs (oneEach x y) i.val (by rw [oneEach_length]; simp; omega)
      change (wiresOf gs (oneEach x y)).getD i.val false = (oneEach x y).getD i.val false at h1
      rw [h1]
      simp only [oneEach]
      have hlen : (List.ofFn (fun i' : Fin n => decide (i' = x))).length = n := by simp
      rw [getD_append_left _ _ _ _ (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt]
    · intro j
      have h1 := wiresOf_append_prefix [] gs (oneEach x y) (n + j.val) (by rw [oneEach_length]; simp)
      change (wiresOf gs (oneEach x y)).getD (n + j.val) false = (oneEach x y).getD (n + j.val) false at h1
      rw [h1]
      simp only [oneEach]
      have hlen : (List.ofFn (fun i' : Fin n => decide (i' = x))).length = n := by simp
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen]; omega)]
      simp only [hlen, Nat.add_sub_cancel_left, List.getElem?_ofFn, dif_pos j.isLt, Option.getD_some]
  have hbase_dep : ∀ (gs : List Gate) (u : ℕ), u < n + m → (depthsOf (n + m) gs).getD u 0 = 0 := by
    intro gs u hu
    have h1 := depthsOf_append_prefix (n + m) [] gs u (by simp; omega)
    change (depthsOf (n + m) gs).getD u 0 = (List.replicate (n + m) 0).getD u 0 at h1
    rw [h1]
    simp [List.getD_eq_getElem?_getD, hu]
  have hbuild_aff : ∀ (gs : List Gate) (f : Fin n → ZMod 2) (h : Fin m → ZMod 2),
      goodGates (n + m) gs →
      ∃ (gs' : List Gate) (out : ℕ),
        gs.length ≤ gs'.length ∧ goodGates (n + m) gs' ∧
        gs'.countP nonlin = gs.countP nonlin ∧
        out < (n + m) + gs'.length ∧
        (depthsOf (n + m) gs').getD out 0 = 0 ∧
        (∀ k < (n + m) + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
        (∀ (x : Fin n) (y : Fin m),
          (∀ k < (n + m) + gs.length, (wiresOf gs' (oneEach x y)).getD k false = (wiresOf gs (oneEach x y)).getD k false) ∧
          b2z ((wiresOf gs' (oneEach x y)).getD out false) = f x + h y) := by
    intro gs f h hgood
    let wsX : List ℕ := ((List.finRange n).filter (fun i => decide (f i = 1))).map Fin.val
    let wsY : List ℕ := ((List.finRange m).filter (fun j => decide (h j = 1))).map (fun j => n + j.val)
    let ws := wsX ++ wsY
    have hws_lt : ∀ u ∈ ws, u < (n + m) + gs.length := by
      intro u hu
      simp only [ws, wsX, wsY, List.mem_append, List.mem_map, List.mem_filter] at hu
      rcases hu with ⟨i, _, rfl⟩ | ⟨j, _, rfl⟩ <;> omega
    have hws_dep : ∀ u ∈ ws, (depthsOf (n + m) gs).getD u 0 ≤ 0 := by
      intro u hu
      simp only [ws, wsX, wsY, List.mem_append, List.mem_map, List.mem_filter] at hu
      rcases hu with ⟨i, _, rfl⟩ | ⟨j, _, rfl⟩
      · rw [hbase_dep gs i.val (by omega)]
      · rw [hbase_dep gs (n + j.val) (by omega)]
    rcases exists_xorList (n + m) gs ws 0 hgood hws_lt hws_dep with
      ⟨gs', out, hlen, hgood', hcnt, hout, hdep, hdpref, hval⟩
    refine ⟨gs', out, hlen, hgood', hcnt, hout, by omega, hdpref, fun x y => ?_⟩
    have hv := hval (oneEach x y) (oneEach_length x y)
    refine ⟨hv.1, ?_⟩
    rw [hv.2]
    simp only [ws, List.map_append, List.sum_append]
    have hsumX : (wsX.map (fun u => b2z ((wiresOf gs (oneEach x y)).getD u false))).sum = f x := by
      have h1 : wsX.map (fun u => b2z ((wiresOf gs (oneEach x y)).getD u false)) =
          ((List.finRange n).filter (fun i => decide (f i = 1))).map (fun i => b2z (decide (i = x))) := by
        simp only [wsX, List.map_map]
        refine List.map_congr_left fun i _ => ?_
        dsimp only [Function.comp]
        rw [(hbase_in gs x y).1 i]
      rw [h1]
      have hnodup : ((List.finRange n).filter (fun i => decide (f i = 1))).Nodup :=
        (List.nodup_finRange n).filter _
      have htoF : ((List.finRange n).filter (fun i => decide (f i = 1))).toFinset =
          Finset.univ.filter (fun i : Fin n => f i = 1) := by ext i; simp
      rw [← List.sum_toFinset _ hnodup, htoF]
      by_cases hfx : f x = 1
      · rw [Finset.sum_eq_single x]
        · simp [hfx, b2z]
        · intro i _ hix; simp [hix, b2z]
        · intro h; exact (h (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hfx⟩)).elim
      · have hfx0 : f x = 0 := by rcases zmod2_cases (f x) with h0 | h1; exact h0; exact (hfx h1).elim
        rw [hfx0]
        apply Finset.sum_eq_zero
        intro i hi
        have hne : i ≠ x := fun heq => hfx (heq ▸ (Finset.mem_filter.mp hi).2)
        simp [hne, b2z]
    have hsumY : (wsY.map (fun u => b2z ((wiresOf gs (oneEach x y)).getD u false))).sum = h y := by
      have h1 : wsY.map (fun u => b2z ((wiresOf gs (oneEach x y)).getD u false)) =
          ((List.finRange m).filter (fun j => decide (h j = 1))).map (fun j => b2z (decide (j = y))) := by
        simp only [wsY, List.map_map]
        refine List.map_congr_left fun j _ => ?_
        dsimp only [Function.comp]
        rw [(hbase_in gs x y).2 j]
      rw [h1]
      have hnodup : ((List.finRange m).filter (fun j => decide (h j = 1))).Nodup :=
        (List.nodup_finRange m).filter _
      have htoF : ((List.finRange m).filter (fun j => decide (h j = 1))).toFinset =
          Finset.univ.filter (fun j : Fin m => h j = 1) := by ext j; simp
      rw [← List.sum_toFinset _ hnodup, htoF]
      by_cases hhy : h y = 1
      · rw [Finset.sum_eq_single y]
        · simp [hhy, b2z]
        · intro j _ hjy; simp [hjy, b2z]
        · intro hm; exact (hm (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hhy⟩)).elim
      · have hhy0 : h y = 0 := by rcases zmod2_cases (h y) with h0 | h1; exact h0; exact (hhy h1).elim
        rw [hhy0]
        apply Finset.sum_eq_zero
        intro j hj
        have hne : j ≠ y := fun heq => hhy (heq ▸ (Finset.mem_filter.mp hj).2)
        simp [hne, b2z]
    rw [hsumX, hsumY]
  have hstage1 : ∀ (k : ℕ) (hk : k ≤ qs.length),
      ∃ (gs : List Gate) (prodW : Fin k → ℕ),
        goodGates (n + m) gs ∧
        gs.countP nonlin = k ∧
        (∀ p : Fin k, prodW p < (n + m) + gs.length) ∧
        (∀ p : Fin k, (depthsOf (n + m) gs).getD (prodW p) 0 ≤ 1) ∧
        (∀ (p : Fin k) (x : Fin n) (y : Fin m),
          b2z ((wiresOf gs (oneEach x y)).getD (prodW p) false) =
            let qp := qs.get ⟨p.val, by omega⟩
            (qp.1 x + qp.2.2.2 y) * (qp.2.2.1 x + qp.2.1 y)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], Fin.elim0, ⟨fun j hj => by simp at hj, fun _ h => by cases h⟩, rfl,
        fun p => Fin.elim0 p, fun p => Fin.elim0 p, fun p => Fin.elim0 p⟩
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨gs, prodW, hgood, hcnt, hlt, hdep, heval⟩
      let qk := qs.get ⟨k, by omega⟩
      rcases hbuild_aff gs qk.1 qk.2.2.2 hgood with
        ⟨gs1, w1, hlen1, hgood1, hcnt1, hw1, hdep1, hdpref1, hval1⟩
      rcases hbuild_aff gs1 qk.2.2.1 qk.2.1 hgood1 with
        ⟨gs2, w2, hlen2, hgood2, hcnt2, hw2, hdep2, hdpref2, hval2⟩
      have h3 := append_and2 (n + m) gs2 w1 w2 hgood2 (by omega) hw2
      let gs3 := gs2 ++ [⟨GateOp.and, [w1, w2]⟩]
      let out := (n + m) + gs2.length
      let prodW' : Fin (k + 1) → ℕ := fun p => if hp : p.val < k then prodW ⟨p.val, hp⟩ else out
      refine ⟨gs3, prodW', h3.2.1, by rw [h3.2.2.1, hcnt2, hcnt1, hcnt], ?_, ?_, ?_⟩
      · intro p
        by_cases hp : p.val < k
        · simp only [prodW', dif_pos hp]
          have h1 := hlt ⟨p.val, hp⟩
          have hlen3 : gs3.length = gs2.length + 1 := by simp [gs3]
          omega
        · simp only [prodW', dif_neg hp]; exact h3.2.2.2.1
      · intro p
        by_cases hp : p.val < k
        · simp only [prodW', dif_pos hp]
          rw [h3.2.2.2.2.2.1 _ (by have := hlt ⟨p.val, hp⟩; omega),
            hdpref2 _ (by have := hlt ⟨p.val, hp⟩; omega),
            hdpref1 _ (hlt ⟨p.val, hp⟩)]
          exact hdep ⟨p.val, hp⟩
        · simp only [prodW', dif_neg hp]
          rw [h3.2.2.2.2.1, hdpref2 w1 hw1, hdep1, hdep2]
          decide
      · intro p x y
        by_cases hp : p.val < k
        · simp only [prodW', dif_pos hp]
          have hltp := hlt ⟨p.val, hp⟩
          rw [(h3.2.2.2.2.2.2 (oneEach x y) (oneEach_length x y)).1 _ (by omega),
            (hval2 x y).1 _ (by omega), (hval1 x y).1 _ hltp]
          exact heval ⟨p.val, hp⟩ x y
        · have hpk : p.val = k := by omega
          simp only [prodW', dif_neg hp]
          rw [(h3.2.2.2.2.2.2 (oneEach x y) (oneEach_length x y)).2, b2z_and,
            (hval2 x y).1 w1 hw1, (hval1 x y).2, (hval2 x y).2]
          have hqeq : qs.get ⟨p.val, by omega⟩ = qk := by
            dsimp only [qk]; congr 1; exact Fin.ext (by dsimp only; omega)
          rw [hqeq]
  rcases hstage1 qs.length le_rfl with ⟨gs1, prodW, hgood1, hcnt1, hplt1, hpdep1, hpeval1⟩
  have hstage2 : ∀ (k : ℕ) (hk : k ≤ q),
      ∃ (gs : List Gate) (tap : Fin k → ℕ),
        gs1.length ≤ gs.length ∧
        goodGates (n + m) gs ∧
        gs.countP nonlin = qs.length ∧
        (∀ p : Fin qs.length, (depthsOf (n + m) gs).getD (prodW p) 0 ≤ 1) ∧
        (∀ (p : Fin qs.length) (x : Fin n) (y : Fin m),
          b2z ((wiresOf gs (oneEach x y)).getD (prodW p) false) =
            let qp := qs.get p
            (qp.1 x + qp.2.2.2 y) * (qp.2.2.1 x + qp.2.1 y)) ∧
        (∀ j : Fin k, tap j < (n + m) + gs.length) ∧
        (∀ j : Fin k, (depthsOf (n + m) gs).getD (tap j) 0 ≤ 1) ∧
        (∀ (j : Fin k) (x : Fin n) (y : Fin m),
          b2z ((wiresOf gs (oneEach x y)).getD (tap j) false) =
            α ⟨j.val, by omega⟩ x + β ⟨j.val, by omega⟩ y +
              ∑ p : Fin qs.length, mask ⟨j.val, by omega⟩ p * evalQuad (qs.get p) x y) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨gs1, Fin.elim0, le_rfl, hgood1, hcnt1, hpdep1, hpeval1,
        fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨gs, tap, hlen, hgood, hcnt, hpdep, hpeval, htlt, htdep, hteval⟩
      let jk : Fin q := ⟨k, by omega⟩
      let α' : Fin n → ZMod 2 := fun x =>
        α jk x + ∑ p : Fin qs.length, mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x)
      let β' : Fin m → ZMod 2 := fun y =>
        β jk y + ∑ p : Fin qs.length, mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y)
      rcases hbuild_aff gs α' β' hgood with
        ⟨gsA, wA, hlenA, hgoodA, hcntA, hwA, hdepA, hdprefA, hvalA⟩
      let maskPs : List (Fin qs.length) := (List.finRange qs.length).filter (fun p => decide (mask jk p = 1))
      let inW : List ℕ := wA :: maskPs.map prodW
      have hinW_lt : ∀ u ∈ inW, u < (n + m) + gsA.length := by
        intro u hu
        simp only [inW, List.mem_cons, List.mem_map] at hu
        rcases hu with rfl | ⟨p, _, rfl⟩
        · exact hwA
        · have := hplt1 p; omega
      have hinW_dep : ∀ u ∈ inW, (depthsOf (n + m) gsA).getD u 0 ≤ 1 := by
        intro u hu
        simp only [inW, List.mem_cons, List.mem_map] at hu
        rcases hu with rfl | ⟨p, _, rfl⟩
        · omega
        · rw [hdprefA (prodW p) (by have := hplt1 p; omega)]
          exact hpdep p
      rcases exists_xorList (n + m) gsA inW 1 hgoodA hinW_lt hinW_dep with
        ⟨gsB, out, hlenB, hgoodB, hcntB, houtB, hdepB, hdprefB, hvalB⟩
      let tap' : Fin (k + 1) → ℕ := fun j => if hj : j.val < k then tap ⟨j.val, hj⟩ else out
      refine ⟨gsB, tap', by omega, hgoodB, by rw [hcntB, hcntA, hcnt], ?_, ?_, ?_, ?_, ?_⟩
      · intro p
        have hltp := hplt1 p
        rw [hdprefB (prodW p) (by omega), hdprefA (prodW p) (by omega)]
        exact hpdep p
      · intro p x y
        have hltp := hplt1 p
        rw [(hvalB (oneEach x y) (oneEach_length x y)).1 (prodW p) (by omega),
          (hvalA x y).1 (prodW p) (by omega)]
        exact hpeval p x y
      · intro j
        by_cases hj : j.val < k
        · simp only [tap', dif_pos hj]; have := htlt ⟨j.val, hj⟩; omega
        · simp only [tap', dif_neg hj]; exact houtB
      · intro j
        by_cases hj : j.val < k
        · simp only [tap', dif_pos hj]
          have hltj := htlt ⟨j.val, hj⟩
          rw [hdprefB _ (by omega), hdprefA _ hltj]
          exact htdep ⟨j.val, hj⟩
        · simp only [tap', dif_neg hj]; exact hdepB
      · intro j x y
        by_cases hj : j.val < k
        · simp only [tap', dif_pos hj]
          have hltj := htlt ⟨j.val, hj⟩
          rw [(hvalB (oneEach x y) (oneEach_length x y)).1 _ (by omega),
            (hvalA x y).1 _ hltj]
          exact hteval ⟨j.val, hj⟩ x y
        · have hjk_eq : (⟨j.val, by omega⟩ : Fin q) = jk := Fin.ext (by dsimp only [jk]; omega)
          simp only [tap', dif_neg hj, hjk_eq]
          rw [(hvalB (oneEach x y) (oneEach_length x y)).2]
          simp only [inW, List.map_cons, List.sum_cons, List.map_map]
          rw [(hvalA x y).2]
          have hmap_eq : maskPs.map ((fun u => b2z ((wiresOf gsA (oneEach x y)).getD u false)) ∘ prodW) =
              maskPs.map (fun p =>
                let qp := qs.get p
                (qp.1 x + qp.2.2.2 y) * (qp.2.2.1 x + qp.2.1 y)) := by
            refine List.map_congr_left fun p _ => ?_
            dsimp only [Function.comp]
            have hltp := hplt1 p
            rw [(hvalA x y).1 (prodW p) (by omega)]
            exact hpeval p x y
          rw [hmap_eq]
          have hnodup : maskPs.Nodup := (List.nodup_finRange qs.length).filter _
          have htoF : maskPs.toFinset = Finset.univ.filter (fun p : Fin qs.length => mask jk p = 1) := by
            ext p; simp [maskPs]
          rw [← List.sum_toFinset _ hnodup, htoF]
          have hfilt_sum : ∑ p ∈ Finset.univ.filter (fun p : Fin qs.length => mask jk p = 1),
              ((qs.get p).1 x + (qs.get p).2.2.2 y) * ((qs.get p).2.2.1 x + (qs.get p).2.1 y) =
              ∑ p : Fin qs.length, mask jk p *
                (((qs.get p).1 x + (qs.get p).2.2.2 y) * ((qs.get p).2.2.1 x + (qs.get p).2.1 y)) := by
            rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : Fin qs.length => mask jk p = 1)]
            have hleft : ∑ p ∈ Finset.univ.filter (fun p : Fin qs.length => mask jk p = 1),
                mask jk p * (((qs.get p).1 x + (qs.get p).2.2.2 y) * ((qs.get p).2.2.1 x + (qs.get p).2.1 y)) =
                ∑ p ∈ Finset.univ.filter (fun p : Fin qs.length => mask jk p = 1),
                  ((qs.get p).1 x + (qs.get p).2.2.2 y) * ((qs.get p).2.2.1 x + (qs.get p).2.1 y) := by
              refine Finset.sum_congr rfl fun p hp => ?_
              rw [(Finset.mem_filter.mp hp).2, one_mul]
            have hright : ∑ p ∈ Finset.univ.filter (fun p : Fin qs.length => ¬ mask jk p = 1),
                mask jk p * (((qs.get p).1 x + (qs.get p).2.2.2 y) * ((qs.get p).2.2.1 x + (qs.get p).2.1 y)) = 0 := by
              apply Finset.sum_eq_zero
              intro p hp
              have hne : mask jk p ≠ 1 := (Finset.mem_filter.mp hp).2
              have h0 : mask jk p = 0 := by rcases zmod2_cases (mask jk p) with h | h; exact h; exact (hne h).elim
              rw [h0, zero_mul]
            rw [hleft, hright, add_zero]
          rw [hfilt_sum]
          dsimp only [α', β']
          have hsum_eq : (∑ p : Fin qs.length, mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x)) +
              (∑ p : Fin qs.length, mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y)) +
              ∑ p : Fin qs.length, mask jk p *
                (((qs.get p).1 x + (qs.get p).2.2.2 y) * ((qs.get p).2.2.1 x + (qs.get p).2.1 y)) =
              ∑ p : Fin qs.length, mask jk p * evalQuad (qs.get p) x y := by
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun p _ => ?_
            dsimp only [evalQuad]
            have h1 := zmod2_add_self (mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x))
            have h2 := zmod2_add_self (mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y))
            calc mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x) +
                  mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y) +
                  mask jk p * (((qs.get p).1 x + (qs.get p).2.2.2 y) * ((qs.get p).2.2.1 x + (qs.get p).2.1 y))
                = (mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x) +
                    mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x)) +
                  (mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y) +
                    mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y)) +
                  mask jk p * ((qs.get p).1 x * (qs.get p).2.1 y + (qs.get p).2.2.1 x * (qs.get p).2.2.2 y) := by ring
              _ = mask jk p * ((qs.get p).1 x * (qs.get p).2.1 y + (qs.get p).2.2.1 x * (qs.get p).2.2.2 y) := by
                    rw [h1, h2, zero_add, zero_add]
          calc (α jk x + ∑ p : Fin qs.length, mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x)) +
                (β jk y + ∑ p : Fin qs.length, mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y)) +
                ∑ p : Fin qs.length, mask jk p *
                  (((qs.get p).1 x + (qs.get p).2.2.2 y) * ((qs.get p).2.2.1 x + (qs.get p).2.1 y))
              = α jk x + β jk y +
                  ((∑ p : Fin qs.length, mask jk p * ((qs.get p).1 x * (qs.get p).2.2.1 x)) +
                    (∑ p : Fin qs.length, mask jk p * ((qs.get p).2.2.2 y * (qs.get p).2.1 y)) +
                    ∑ p : Fin qs.length, mask jk p *
                      (((qs.get p).1 x + (qs.get p).2.2.2 y) * ((qs.get p).2.2.1 x + (qs.get p).2.1 y))) := by ring
            _ = α jk x + β jk y + ∑ p : Fin qs.length, mask jk p * evalQuad (qs.get p) x y := by rw [hsum_eq]
  rcases hstage2 q le_rfl with ⟨gs2, tap, _, hgood2, hcnt2, _, _, _, htdep2, hteval2⟩
  refine ⟨⟨gs2, 0⟩, tap, hgood2.1, hgood2.2, le_of_eq hcnt2, fun j => ⟨htdep2 j, hteval2 j⟩⟩

theorem matrix_rank_decomp {n m : ℕ} (B : Matrix (Fin n) (Fin m) (ZMod 2)) :
    ∃ (a : Fin B.rank → Fin n → ZMod 2) (b : Fin B.rank → Fin m → ZMod 2),
      B = ∑ k : Fin B.rank, Matrix.vecMulVec (a k) (b k) := by
  let bas := Module.finBasis (ZMod 2) (LinearMap.range B.mulVecLin)
  let a : Fin B.rank → Fin n → ZMod 2 := fun k => (bas k).1
  let b : Fin B.rank → Fin m → ZMod 2 := fun k j =>
    bas.repr ⟨B.mulVecLin (Pi.single j 1), ⟨Pi.single j 1, rfl⟩⟩ k
  refine ⟨a, b, ?_⟩
  ext i j
  have hcol : B.mulVecLin (Pi.single j 1) = ∑ k : Fin B.rank, (b k j) • (a k) := by
    have h1 := bas.sum_repr ⟨B.mulVecLin (Pi.single j 1), ⟨Pi.single j 1, rfl⟩⟩
    have h2 := congrArg Subtype.val h1
    rw [Submodule.coe_sum] at h2
    exact h2.symm
  have hi := congrFun hcol i
  have hlhs : B.mulVecLin (Pi.single j 1) i = B i j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hlhs] at hi
  rw [hi, Matrix.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.vecMulVec_apply, mul_comm]

private lemma twoTerms {d r : ℕ} (a b : Fin r → Fin d → ZMod 2) (hr : r ≤ 2) :
    ∃ u : Quad d d, ∀ i j, evalQuad u i j = ∑ p, a p i * b p j := by
  interval_cases r
  · exact ⟨(0,0,0,0), fun i j => by simp [evalQuad]⟩
  · exact ⟨(a 0,b 0,0,0), fun i j => by simp [evalQuad]⟩
  · exact ⟨(a 0,b 0,a 1,b 1), fun i j => by simp [evalQuad, Fin.sum_univ_two]⟩

private lemma toQuad {d : ℕ} (A : Matrix (Fin d) (Fin d) (ZMod 2)) (h : A.rank ≤ 2) :
    ∃ u : Quad d d, ∀ i j, evalQuad u i j = A i j := by
  obtain ⟨a,b,hab⟩ := matrix_rank_decomp A
  obtain ⟨u,hu⟩ := twoTerms a b h
  refine ⟨u,fun i j => ?_⟩
  simpa only [hu, Matrix.sum_apply, Matrix.vecMulVec_apply] using
    (congrArg (fun (M : Matrix (Fin d) (Fin d) (ZMod 2)) => M i j) hab.symm)

private def padQuad {d : ℕ} (u : Quad d d) : Quad (d+1) (d+1) :=
  (Fin.cases 0 u.1, Fin.cases 0 u.2.1, Fin.cases 0 u.2.2.1, Fin.cases 0 u.2.2.2)

theorem synth {d : ℕ} {α ι κ : Type} [Fintype α] [Fintype ι] [Fintype κ]
    (coord : α ≃ Fin d) (R : ι → Matrix α α (ZMod 2)) (T : κ → Matrix α α (ZMod 2))
    (hr : ∀ i, (R i).rank ≤ 2) (hT : ∀ k, T k ∈ Submodule.span (ZMod 2) (Set.range R)) :
    ∃ (C : Circuit) (tap : κ → ℕ), ReadsBack ((d+1)+(d+1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlin ≤ Fintype.card ι ∧
      ∀ k, (depthsOf ((d+1)+(d+1)) C.gates).getD (tap k) 0 ≤ 1 ∧
        Represents (fun x y : Fin (d+1) => Fin.cases false (fun i =>
          Fin.cases false (fun j => decide (T k (coord.symm i) (coord.symm j) ≠ 0)) y) x)
          ⟨C.gates, tap k⟩ := by
  classical
  have hcoef := fun k => (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp (hT k)
  choose c hc using hcoef
  have hq (p : ι) : ∃ u : Quad d d, ∀ i j, evalQuad u i j =
      R p (coord.symm i) (coord.symm j) := by
    apply toQuad ((R p).submatrix coord.symm coord.symm)
    simpa only [Matrix.rank_submatrix] using hr p
  choose u hu using hq
  let e := Fintype.equivFin ι
  let ek := Fintype.equivFin κ
  let qs := List.ofFn (fun p : Fin (Fintype.card ι) => padQuad (u (e.symm p)))
  have hlen : qs.length = Fintype.card ι := by simp [qs]
  let eqs : Fin qs.length ≃ ι := (finCongr hlen).trans e.symm
  have hget (p : Fin qs.length) : qs.get p = padQuad (u (eqs p)) := by
    simp [qs, eqs, List.get_eq_getElem, finCongr]
    rfl
  obtain ⟨C,tap,hrb,hfan,hcnt,hout⟩ := synth_depth1_quads (d+1) (d+1) (Fintype.card κ) qs
    (fun k p => c (ek.symm k) (eqs p)) (fun _ _ => 0) (fun _ _ => 0)
  refine ⟨C, fun k => tap (ek k), hrb, hfan, hcnt.trans hlen.le, fun k =>
    ⟨(hout (ek k)).1, fun x y => ?_⟩⟩
  apply b2z_inj
  change b2z ((wiresOf C.gates (oneEach x y)).getD (tap (ek k)) false) =
    b2z (mkTable ((T k).submatrix coord.symm coord.symm) x y)
  rw [(hout (ek k)).2 x y]
  simp only [zero_add, Equiv.symm_apply_apply, hget]
  rw [eqs.sum_comp (fun p => c k p * evalQuad (padQuad (u p)) x y)]
  cases x using Fin.cases with
  | zero => simp [padQuad, evalQuad, mkTable, b2z]
  | succ i =>
    cases y using Fin.cases with
    | zero => simp [padQuad, evalQuad, mkTable, b2z]
    | succ j =>
      rw [b2z_mkTable_succ]
      have huv (p : ι) : evalQuad (padQuad (u p)) i.succ j.succ =
          R p (coord.symm i) (coord.symm j) := by
        simpa only [padQuad, evalQuad, Fin.cases_succ] using hu p i j
      simpa only [huv, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.submatrix_apply]
        using congrArg (fun (M : Matrix α α (ZMod 2)) => M (coord.symm i) (coord.symm j)) (hc k)

end PEqualNP.Outside.L_meta_33608_aux.Upper.U33608Circuit

namespace PEqualNP.Outside.L_meta_33608_aux.Upper

open Matrix
abbrev F := ZMod 2
abbrev I (n f : ℕ) := (Fin n ⊕ Fin n) ⊕ Fin f
abbrev Mat (a b : Type) := Matrix a b F
abbrev Square (a : Type) := Mat a a

def sel {a b : Type} [DecidableEq b] (e : a → b) : Mat b a :=
  Matrix.of fun i j => if i = e j then 1 else 0

def layer {a b t : Type} [Fintype a] [Fintype b] [DecidableEq t]
    (e : a → t) (g : b → t) : Mat a b →ₗ[F] Square t where
  toFun X := sel e * X * (sel g).transpose
  map_add' X Y := by rw [Matrix.mul_add,Matrix.add_mul]
  map_smul' c X := by simp

theorem layer_rank {a b t : Type} [Fintype a] [Fintype b] [Fintype t] [DecidableEq t]
    (e : a → t) (g : b → t) (X : Mat a b) : (layer e g X).rank ≤ X.rank := by
  classical
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem rankPlus {a b : Type} [Fintype b] (A B : Mat a b) :
    (A+B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨v,rfl⟩
    rw [Matrix.mulVecLin_add,LinearMap.add_apply]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self A.mulVecLin v)
      (LinearMap.mem_range_self B.mulVecLin v)
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

def symLayer {a b t : Type} [Fintype a] [Fintype b] [DecidableEq t]
    (e : a → t) (g : b → t) : Mat a b →ₗ[F] Square t :=
  layer e g + (Matrix.transposeLinearEquiv t t F F).toLinearMap.comp (layer e g)

theorem symLayer_rank {a b t : Type} [Fintype a] [Fintype b] [Fintype t] [DecidableEq t]
    (e : a → t) (g : b → t) (X : Mat a b) (h : X.rank ≤ 1) :
    (symLayer e g X).rank ≤ 2 := by
  classical
  change (layer e g X + (layer e g X).transpose).rank ≤ 2
  refine (rankPlus _ _).trans ?_
  rw [Matrix.rank_transpose]
  have := (layer_rank e g X).trans h
  omega

def u {n f : ℕ} (i : Fin n) : I n f := .inl (.inl i)
def v {n f : ℕ} (i : Fin n) : I n f := .inl (.inr i)
def w {n f : ℕ} (i : Fin f) : I n f := .inr i

def panel {n f : ℕ} (A K : Square (Fin n)) (B : Mat (Fin n) (Fin f)) : Square (I n f) :=
  let X := Matrix.fromBlocks A K K (0 : Square (Fin n))
  let Y : Mat (Fin n ⊕ Fin n) (Fin f) := fun i j =>
    Sum.elim (fun a => B a j) (fun _ => 0) i
  Matrix.fromBlocks X Y Y.transpose (0 : Square (Fin f))

theorem panel_split {n f : ℕ} (A K : Square (Fin n)) (B : Mat (Fin n) (Fin f))
    (hK : K.transpose = K) :
    panel A K B = layer u u A + symLayer u v K + symLayer u w B := by
  have hs (i j : Fin n) : K j i = K i j := congrFun (congrFun hK i) j
  let U := sel (@u n f)
  let V := sel (@v n f)
  let W := sel (@w n f)
  change _ = (U * A * U.transpose + (U * K * V.transpose +
    (U * K * V.transpose).transpose)) + (U * B * W.transpose + (U * B * W.transpose).transpose)
  ext ((i | i) | i) ((j | j) | j) <;>
    simp [panel,U,V,W,sel,u,v,w,Matrix.mul_apply,Matrix.fromBlocks,Function.swap,
      Matrix.transpose_apply] <;> first | rfl | exact (hs _ _).symm

theorem rankSingle {a b : Type} [DecidableEq a] [DecidableEq b] [Fintype b]
    (i : a) (j : b) : (Matrix.single i j (1:F)).rank ≤ 1 := by
  rw [Matrix.single_eq_single_vecMulVec_single]
  exact Matrix.rank_vecMulVec_le _ _

theorem singles {a b : Type} [DecidableEq a] [DecidableEq b] [Fintype a] [Fintype b]
    (S : Submodule F (Mat a b)) (h : ∀ i j, Matrix.single i j (1:F) ∈ S) (B : Mat a b) :
    B ∈ S := by
  rw [Matrix.matrix_eq_sum_single B]
  apply S.sum_mem
  intro i _
  apply S.sum_mem
  intro j _
  simpa using S.smul_mem (B i j) (h i j)

end PEqualNP.Outside.L_meta_33608_aux.Upper

namespace PEqualNP.Outside.L_meta_33608_aux.UpperGraph

abbrev F := ZMod 2
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) F

def edgeMat {n : ℕ} (i j : Fin n) : Mat n :=
  Matrix.single i j 1 + Matrix.single j i 1

lemma edge_spans {n : ℕ} (edges : Finset (Fin n × Fin n)) (hn : ∀ p ∈ edges, p.1 < p.2)
    (P : Submodule F (Mat n)) (he : ∀ p ∈ edges, edgeMat p.1 p.2 ∈ P)
    (K : Mat n) (hs : K.transpose = K) (_hd : ∀ i, K i i = 0)
    (hk : ∀ i j, (i,j) ∉ edges → (j,i) ∉ edges → K i j = 0) : K ∈ P := by
  classical
  have hx : (∑ p ∈ edges, K p.1 p.2 • edgeMat p.1 p.2) = K := by
    ext i j
    have hterm (p : Fin n × Fin n) :
        (K p.1 p.2 • edgeMat p.1 p.2) i j =
          (if p = (i,j) then K i j else 0) + (if p = (j,i) then K j i else 0) := by
      rcases p with ⟨a,b⟩
      simp only [Matrix.smul_apply, smul_eq_mul, edgeMat, Matrix.add_apply, Matrix.single_apply,
        Prod.mk.injEq, mul_add]
      apply congrArg₂ (· + ·)
      · by_cases h : a = i ∧ b = j
        · rw [ite_eq_left h, ite_eq_left h, mul_one, h.1, h.2]
        · rw [ite_eq_right h, ite_eq_right h, mul_zero]
      · by_cases h : a = j ∧ b = i
        · rw [ite_eq_left h.symm, ite_eq_left h, mul_one, h.1, h.2]
        · rw [ite_eq_right (fun h' => h (And.symm h')), ite_eq_right h, mul_zero]
    simp only [Matrix.sum_apply, hterm, Finset.sum_add_distrib, Finset.sum_ite_eq']
    have hsym : K j i = K i j := congrArg (fun M : Mat n => M i j) hs
    by_cases hf : (i,j) ∈ edges
    · have hb : (j,i) ∉ edges := fun hr => (asymm (hn _ hf) (hn _ hr)).elim
      simp [hf,hb]
    · by_cases hb : (j,i) ∈ edges
      · simp [hf,hb,hsym]
      · simp [hf,hb,hk _ _ hf hb]
  rw [← hx]
  exact P.sum_mem fun p hp => P.smul_mem _ (he p hp)

lemma rank_single {n : ℕ} (i j : Fin n) : (Matrix.single i j (1 : F)).rank ≤ 1 := by
  rw [Matrix.single_eq_single_vecMulVec_single]
  exact Matrix.rank_vecMulVec_le _ _

def squareMat {n : ℕ} (i j : Fin n) : Mat n :=
  let v : Fin n → F := Pi.single i 1 + Pi.single j 1
  Matrix.vecMulVec v v

lemma edgeMat_eq {n : ℕ} (i j : Fin n) :
    edgeMat i j = squareMat i j - Matrix.single i i 1 - Matrix.single j j 1 := by
  simp only [squareMat, Matrix.add_vecMulVec, Matrix.vecMulVec_add,
    ← Matrix.single_eq_single_vecMulVec_single, edgeMat]
  abel

lemma main {n : ℕ} (edges : Finset (Fin n × Fin n)) (hn : ∀ p ∈ edges, p.1 < p.2) :
    ∃ (κ : Type) (_ : Fintype κ) (G : κ → Mat n),
      Fintype.card κ ≤ edges.card + min edges.card (edges.image Prod.fst ∪ edges.image Prod.snd).card ∧
      (∀ i, (G i).rank ≤ 1) ∧
      ∀ K : Mat n, K.transpose = K → (∀ i, K i i = 0) →
        (∀ i j, (i,j) ∉ edges → (j,i) ∉ edges → K i j = 0) →
        K ∈ Submodule.span F (Set.range G) := by
  classical
  let active := edges.image Prod.fst ∪ edges.image Prod.snd
  by_cases h : edges.card ≤ active.card
  · let G : (edges ⊕ edges) → Mat n := Sum.elim
        (fun e => Matrix.single e.1.1 e.1.2 1) (fun e => Matrix.single e.1.2 e.1.1 1)
    refine ⟨_, inferInstance, G, ?_, ?_, ?_⟩
    · simp [Fintype.card_sum, min_eq_left h, active] at *
    · rintro (e|e) <;> exact rank_single _ _
    · apply edge_spans edges hn
      intro p hp
      let e : edges := ⟨p,hp⟩
      exact Submodule.add_mem _
        (Submodule.subset_span (Set.mem_range_self (f := G) (Sum.inl e)))
        (Submodule.subset_span (Set.mem_range_self (f := G) (Sum.inr e)))
  · let G : (edges ⊕ active) → Mat n := Sum.elim
        (fun e => squareMat e.1.1 e.1.2) (fun i => Matrix.single i.1 i.1 1)
    refine ⟨_, inferInstance, G, ?_, ?_, ?_⟩
    · change Fintype.card (edges ⊕ active) ≤ edges.card + min edges.card active.card
      simp [min_eq_right (le_of_not_ge h)]
    · rintro (e|i)
      · exact Matrix.rank_vecMulVec_le _ _
      · exact rank_single _ _
    · apply edge_spans edges hn
      intro p hp
      let e : edges := ⟨p,hp⟩
      let i : active := ⟨p.1, Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)⟩
      let j : active := ⟨p.2, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)⟩
      rw [edgeMat_eq]
      exact Submodule.sub_mem _ (Submodule.sub_mem _
        (Submodule.subset_span (Set.mem_range_self (f := G) (Sum.inl e)))
        (Submodule.subset_span (Set.mem_range_self (f := G) (Sum.inr i))))
        (Submodule.subset_span (Set.mem_range_self (f := G) (Sum.inr j)))

end PEqualNP.Outside.L_meta_33608_aux.UpperGraph
namespace PEqualNP.Outside.L_meta_33608_aux.Upper

def tris (n : ℕ) : Finset (Fin n × Fin n) := Finset.univ.filter (fun z => z.1 < z.2)

theorem tri_card (n : ℕ) : (tris n).card = n.choose 2 := by
  simpa [tris] using (Fintype.card_product_filter_lt (α := Fin n))

theorem generators {n : ℕ} (edges : Finset (Fin n × Fin n)) (hn : ∀ p ∈ edges, p.1 < p.2)
    (f : ℕ) : ∃ (τ : Type) (_ : Fintype τ) (R : τ → Square (I n f)),
    Fintype.card τ ≤ n.choose 2 + edges.card + n*f +
      min edges.card (edges.image Prod.fst ∪ edges.image Prod.snd).card ∧
    (∀ i, (R i).rank ≤ 2) ∧ ∀ A K B, Extract.alt A → Extract.allowed edges K →
      panel A K B ∈ Submodule.span F (Set.range R) := by
  classical
  obtain ⟨κ, inst, G, hcard, hG, hspan⟩ := UpperGraph.main edges hn
  let τ := (tris n) ⊕ κ ⊕ (Fin n × Fin f)
  let U := @u n f
  let V := @v n f
  let W := @w n f
  let RA (p : tris n) := layer U U (UpperGraph.edgeMat p.1.1 p.1.2)
  let RK (i : κ) := symLayer U V (G i)
  let RB (p : Fin n × Fin f) := symLayer U W (Matrix.single p.1 p.2 (1:F))
  let R : τ → Square (I n f) := Sum.elim RA (Sum.elim RK RB)
  refine ⟨τ,inferInstance,R,?_,?_,?_⟩
  · simp only [τ,Fintype.card_sum,Fintype.card_coe,tri_card,Fintype.card_prod,Fintype.card_fin]
    omega
  · rintro (p | i | p)
    · refine (layer_rank U U _).trans ?_
      refine (rankPlus _ _).trans ?_
      have h₁ := rankSingle p.1.1 p.1.2
      have h₂ := rankSingle p.1.2 p.1.1
      omega
    · exact symLayer_rank U V _ (hG i)
    · exact symLayer_rank U W _ (rankSingle p.1 p.2)
  · intro A K B hA hK
    let S := Submodule.span F (Set.range R)
    have gen (i : τ) : R i ∈ S := Submodule.subset_span (Set.mem_range_self i)
    have a : A ∈ S.comap (layer U U) := by
      apply UpperGraph.edge_spans (tris n) (fun p hp => (Finset.mem_filter.mp hp).2)
        (S.comap (layer U U)) _ A hA.1 hA.2
      · intro i j hi hj
        have h₁ : ¬ i < j := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
        have h₂ : ¬ j < i := fun h => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
        have e : i = j := le_antisymm (le_of_not_gt h₂) (le_of_not_gt h₁)
        rw [e,hA.2]
      · intro p hp
        exact gen (Sum.inl ⟨p,hp⟩)
    have k : K ∈ S.comap (symLayer U V) := by
      apply (show Submodule.span F (Set.range G) ≤ S.comap (symLayer U V) from ?_)
        (hspan K hK.1.1 hK.1.2 hK.2)
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact gen (Sum.inr (Sum.inl i))
    have b : B ∈ S.comap (symLayer U W) := by
      apply singles
      exact fun i j => gen (Sum.inr (Sum.inr (i,j)))
    rw [panel_split A K B hK.1.1]
    exact S.add_mem (S.add_mem a k) b

theorem main {n : ℕ} (edges : Finset (Fin n × Fin n)) (hn : ∀ p ∈ edges, p.1 < p.2)
    (f : ℕ) : Extract.bank edges f (n.choose 2 + edges.card + n*f +
      min edges.card (edges.image Prod.fst ∪ edges.image Prod.snd).card) := by
  classical
  obtain ⟨τ, inst, R, hcard, hR, hspan⟩ := generators edges hn f
  let Kx := Extract.Mat n × Extract.Mat n × Extract.BMat n f
  let valid (z : Kx) := Extract.alt z.1 ∧ Extract.allowed edges z.2.1
  let T (z : Kx) := if valid z then panel z.1 z.2.1 z.2.2 else 0
  obtain ⟨C,tap,back,fan,count,reps⟩ := U33608Circuit.synth Extract.coord R T hR (by
    intro z
    by_cases h : valid z
    · simpa only [T,ite_eq_left h] using hspan _ _ _ h.1 h.2
    · simp only [T,ite_eq_right h,Submodule.zero_mem])
  refine ⟨C,fun A K B => tap (A,K,B),back,fan,count.trans hcard,?_⟩
  intro A K B ha hk
  have h := reps (A,K,B)
  have he : T (A,K,B) = panel A K B := ite_eq_left ⟨ha,hk⟩
  rw [he] at h
  exact h

end PEqualNP.Outside.L_meta_33608_aux.Upper

namespace PEqualNP.Outside.L_meta_33608_aux

private theorem lower {n f t : ℕ} (edges : Finset (Fin n × Fin n))
    (hord : ∀ p ∈ edges, p.1 < p.2) (hb : Extract.bank edges f t) :
    let a := (edges.image Prod.fst ∪ edges.image Prod.snd).card
    let D := n.choose 2 + edges.card + n*f
    let h := t-D
    D ≤ t ∧ a ≤ 4*h ∧ edges.card+h+2 ≤ 2^(h+1) := by
  obtain ⟨R, hr, hgen⟩ := Extract.main edges hb
  let P := Graph.P edges
  obtain ⟨q, S, hqt, hr', hg'⟩ := Pad.reduce P R hr
    (fun A K B hA hK => hgen A K B hA hK)
  have hW : Graph.Wsp P ≤ Submodule.span (ZMod 2) (Set.range S) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨A, K, hA, hK, rfl⟩
    exact hg' A K hA hK
  have hdim := Graph.finrank_Wsp edges hord
  have hp := Graph.finrank_P edges hord
  have hact := Graph.active_le_finrank_Hsp edges hord
  have ha := Active.main P (fun K hK => hK.1) q S hr' hW
  have hc := Coset.main P (fun K hK => hK.1) q S hr' hW
  change Module.finrank (ZMod 2) (Graph.Hsp P) ≤
      4 * (q - Module.finrank (ZMod 2) (Graph.Wsp P)) at ha
  change Module.finrank (ZMod 2) (Graph.Wsp P) ≤ q ∧
    Module.finrank (ZMod 2) P + (q - Module.finrank (ZMod 2) (Graph.Wsp P)) + 2 ≤
      2 ^ ((q - Module.finrank (ZMod 2) (Graph.Wsp P)) + 1) at hc
  dsimp only [P] at ha hc
  rw [hdim] at ha
  rw [hdim, hp] at hc
  have hsub : q - (n.choose 2 + edges.card) ≤ t - (n.choose 2 + edges.card + n*f) := by omega
  have grow := Coset.pow_mono_sub hsub
  dsimp only
  exact ⟨by omega, hact.trans (ha.trans (Nat.mul_le_mul_left 4 hsub)), by omega⟩

private theorem bank_mono {n f s t : ℕ} (edges : Finset (Fin n × Fin n))
    (hst : s ≤ t) (h : Extract.bank edges f s) : Extract.bank edges f t := by
  obtain ⟨C,tap,hb,hf,hn,ht⟩ := h
  exact ⟨C,tap,hb,hf,hn.trans hst,ht⟩

private theorem assembled {n : ℕ} (edges : Finset (Fin n × Fin n))
    (hord : ∀ p ∈ edges, p.1 < p.2) (f : ℕ) :
    let a := (edges.image Prod.fst ∪ edges.image Prod.snd).card
    let D := n.choose 2 + edges.card + n*f
    Extract.bank edges f (D + min edges.card a) →
    (∀ t, Extract.bank edges f t →
      D ≤ t ∧ a ≤ 4*(t-D) ∧ edges.card+(t-D)+2 ≤ 2^((t-D)+1)) ∧
    Extract.bank edges f (D + min edges.card a) ∧
    (Extract.bank edges f (D+1) ↔ edges.card ≤ 1) := by
  intro a D upper
  refine ⟨fun t h => lower edges hord h, upper, ?_, ?_⟩
  · intro h
    have cap := (lower edges hord h).2.2
    change edges.card + (D + 1 - D) + 2 ≤ 2 ^ ((D + 1 - D) + 1) at cap
    simp only [Nat.add_sub_cancel_left] at cap
    omega
  · intro h
    apply bank_mono edges _ upper
    omega

end PEqualNP.Outside.L_meta_33608_aux

theorem PEqualNP.Outside.L_meta_33608 :
(let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let F := ZMod 2
∀ (n : ℕ) (edges : Finset (Fin n × Fin n)), (∀ p ∈ edges, p.1 < p.2) →
  let active := edges.image Prod.fst ∪ edges.image Prod.snd
  let M := Matrix (Fin n) (Fin n) F
  let alt := fun (A : M) => A.transpose = A ∧ ∀ i, A i i = 0
  let allowed := fun (K : M) => alt K ∧
    ∀ i j, (i,j) ∉ edges → (j,i) ∉ edges → K i j = 0
  let D := fun f : ℕ => Nat.choose n 2 + edges.card + n*f
  let bank := fun (f t : ℕ) =>
    let J := Fin n ⊕ Fin n
    let d := n+n+f
    let BMat := Matrix (Fin n) (Fin f) F
    let coord : J ⊕ Fin f ≃ Fin d :=
      (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin f))).trans finSumFinEquiv
    let table := fun (A K : M) (B : BMat) (x y : Fin (d+1)) =>
      let X := Matrix.fromBlocks A K K (0 : M)
      let Y : Matrix J (Fin f) F := fun i j => Sum.elim (fun a => B a j) (fun _ => 0) i
      let Z := Matrix.fromBlocks X Y Y.transpose (0 : Matrix (Fin f) (Fin f) F)
      Fin.cases false (fun i => Fin.cases false (fun j =>
        decide (Z (coord.symm i) (coord.symm j) ≠ 0)) y) x
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : M → M → BMat → ℕ),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack ((d+1)+(d+1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
      ∀ A K B, alt A → allowed K →
        (depths ((d+1)+(d+1)) C).getD (tap A K B) 0 ≤ 1 ∧
        PEqualNP.Represents.Represents (table A K B) ⟨C.gates, tap A K B⟩
  ∀ f : ℕ,
    (∀ t : ℕ, bank f t →
      let h := t-D f
      D f ≤ t ∧ active.card ≤ 4*h ∧ edges.card+h+2 ≤ 2^(h+1)) ∧
    bank f (D f + min edges.card active.card) ∧
    (bank f (D f+1) ↔ edges.card ≤ 1)) := by
  intro nonlinear depths F n edges hord active M alt allowed D bank f
  exact PEqualNP.Outside.L_meta_33608_aux.assembled edges hord f
    (PEqualNP.Outside.L_meta_33608_aux.Upper.main edges hord f)
