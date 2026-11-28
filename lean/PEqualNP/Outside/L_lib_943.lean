import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_943

namespace Blocks

abbrev F := ZMod 2
abbrev ι (r c : ℕ) := Fin r ⊕ (Fin r ⊕ Fin c)
abbrev Mat (r c : ℕ) := Matrix (ι r c) (ι r c) F
abbrev Top {r c : ℕ} (i : Fin r) : ι r c := .inl i
abbrev Bot {r c : ℕ} (i : Fin r) : ι r c := .inr (.inl i)
abbrev Rest {r c : ℕ} (i : Fin c) : ι r c := .inr (.inr i)

def Alt (α : Type) : Submodule F (Matrix α α F) := by
  refine { carrier := {H | (∀ i j, H i j = H j i) ∧ ∀ i, H i i = 0},
           zero_mem' := ⟨fun _ _ => rfl, fun _ => rfl⟩, add_mem' := ?_, smul_mem' := ?_ }
  · rintro H G ⟨hs, hd⟩ ⟨gs, gd⟩
    refine ⟨fun i j => congrArg₂ (· + ·) (hs i j) (gs i j), ?_⟩
    intro i
    change H i i + G i i = 0
    rw [hd i, gd i, add_zero]
  · rintro a H ⟨hs, hd⟩
    refine ⟨fun i j => congrArg (fun b => a • b) (hs i j), ?_⟩
    intro i
    change a • H i i = 0
    rw [hd i, smul_zero]

theorem alt_symm {α : Type} {H : Matrix α α F} (h : H ∈ Alt α) (i j : α) :
    H i j = H j i := h.1 i j

theorem alt_diag {α : Type} {H : Matrix α α F} (h : H ∈ Alt α) (i : α) :
    H i i = 0 := h.2 i

theorem mem_Alt_iff {α : Type} {H : Matrix α α F} :
    H ∈ Alt α ↔ H.transpose = H ∧ ∀ i, H i i = 0 := by
  constructor
  · intro h
    exact ⟨Matrix.ext fun i j => alt_symm h j i, alt_diag h⟩
  · rintro ⟨hs, hd⟩
    exact ⟨fun i j => congrArg (fun A : Matrix α α F => A j i) hs, hd⟩

private def reflectUpper {α : Type} [LinearOrder α]
    (f : {p : α × α // p.1 < p.2} → F) : Matrix α α F :=
  Matrix.of fun i j =>
    if hij : i < j then f ⟨(i, j), hij⟩
    else if hji : j < i then f ⟨(j, i), hji⟩ else 0

def altCoordinates (α : Type) [LinearOrder α] :
    Alt α ≃ₗ[F] ({p : α × α // p.1 < p.2} → F) where
  toFun H p := (H : Matrix α α F) p.1.1 p.1.2
  invFun f := ⟨reflectUpper f, by
    refine ⟨?_, ?_⟩
    · intro i j
      rcases lt_trichotomy i j with h | rfl | h
      · simp [reflectUpper, h, not_lt_of_gt h]
      · rfl
      · simp [reflectUpper, h, not_lt_of_gt h]
    · intro i
      simp [reflectUpper]⟩
  left_inv H := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    change reflectUpper (fun p => (H : Matrix α α F) p.1.1 p.1.2) i j =
      (H : Matrix α α F) i j
    rcases lt_trichotomy i j with h | hij | h
    · simp [reflectUpper, h]
    · subst j
      simpa [reflectUpper] using (alt_diag H.property i).symm
    · simpa [reflectUpper, h, not_lt_of_gt h] using alt_symm H.property j i
  right_inv f := by
    funext p
    rcases p with ⟨⟨i, j⟩, h⟩
    change reflectUpper f i j = f ⟨(i, j), h⟩
    simp [reflectUpper, h]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_Alt (r : ℕ) : Module.finrank F (Alt (Fin r)) = Nat.choose r 2 := by
  rw [(altCoordinates (Fin r)).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_subtype]
  simpa using (Fintype.card_product_filter_lt (α := Fin r))

theorem finrank_altSpace (r : ℕ) (A : Submodule F (Matrix (Fin r) (Fin r) F))
    (hA : ∀ H : Matrix (Fin r) (Fin r) F, H ∈ A ↔ H.transpose = H ∧ ∀ i, H i i = 0) :
    Module.finrank F A = Nat.choose r 2 := by
  have h : A = Alt (Fin r) := Submodule.ext fun H => (hA H).trans mem_Alt_iff.symm
  rw [h, finrank_Alt]

def N (r c : ℕ) : Mat r c := Matrix.of fun
  | .inl i, .inr (.inl j) => if i = j then 1 else 0
  | _, _ => 0

def J (r c : ℕ) : Mat r c := 1 + N r c

def delta (r c : ℕ) : Mat r c →ₗ[F] Mat r c where
  toFun H := J r c * H * (J r c).transpose + H
  map_add' H G := by
    simp only [Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' a H := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add, RingHom.id_apply]

def imageMap (r c : ℕ) : Alt (ι r c) →ₗ[F] Mat r c :=
  (delta r c).comp (Alt (ι r c)).subtype

private theorem delta_expand {r c : ℕ} (H : Mat r c) :
    delta r c H = N r c * H + H * (N r c).transpose + N r c * H * (N r c).transpose := by
  have h : H + H = 0 := Matrix.ext fun i j => CharTwo.add_self_eq_zero (H i j)
  change (1 + N r c) * H * (1 + N r c).transpose + H = _
  calc
    _ = (H + H) + (N r c * H + H * (N r c).transpose + N r c * H * (N r c).transpose) := by
      simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.add_mul, Matrix.mul_add,
        one_mul, mul_one]
      abel
    _ = _ := by rw [h, zero_add]

private theorem N_mul_entry {r c : ℕ} (H : Mat r c) (i j : ι r c) :
    (N r c * H) i j = match i with
      | .inl a => H (Bot a) j
      | .inr _ => 0 := by
  rcases i with a | a <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, N, Bot, ite_mul, Finset.sum_ite_eq]

private theorem mul_Nt_entry {r c : ℕ} (H : Mat r c) (i j : ι r c) :
    (H * (N r c).transpose) i j = match j with
      | .inl b => H i (Bot b)
      | .inr _ => 0 := by
  rcases j with b | b <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, N, Bot, mul_ite,
      Finset.sum_ite_eq]

def blocks {r c : ℕ} (S K : Matrix (Fin r) (Fin r) F) (L : Matrix (Fin r) (Fin c) F) :
    Mat r c := Matrix.of fun
  | .inl i, .inl j => S i j
  | .inl i, .inr (.inl j) => K i j
  | .inl i, .inr (.inr j) => L i j
  | .inr (.inl i), .inl j => K j i
  | .inr (.inr i), .inl j => L j i
  | _, _ => 0

abbrev BlockData (r c : ℕ) := Alt (Fin r) × Alt (Fin r) × Matrix (Fin r) (Fin c) F

def assemble (r c : ℕ) : BlockData r c →ₗ[F] Mat r c where
  toFun x := blocks x.1 x.2.1 x.2.2
  map_add' x y := by
    apply Matrix.ext
    intro i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
      simp [blocks, Matrix.add_apply]
  map_smul' a x := by
    apply Matrix.ext
    intro i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
      simp [blocks, Matrix.smul_apply, Submodule.coe_smul]

theorem assemble_injective (r c : ℕ) : Function.Injective (assemble r c) := by
  intro x y h
  apply Prod.ext
  · apply Subtype.ext
    exact Matrix.ext fun i j => congrArg (fun M : Mat r c => M (Top i) (Top j)) h
  · apply Prod.ext
    · apply Subtype.ext
      exact Matrix.ext fun i j => congrArg (fun M : Mat r c => M (Top i) (Bot j)) h
    · exact Matrix.ext fun i j => congrArg (fun M : Mat r c => M (Top i) (Rest j)) h

def W (r c : ℕ) : Submodule F (Mat r c) := LinearMap.range (assemble r c)

theorem mem_W_iff {r c : ℕ} {M : Mat r c} :
    M ∈ W r c ↔ ∃ (S K : Alt (Fin r)) (L : Matrix (Fin r) (Fin c) F), blocks S K L = M := by
  constructor
  · rintro ⟨⟨S, K, L⟩, h⟩
    exact ⟨S, K, L, h⟩
  · rintro ⟨S, K, L, h⟩
    exact ⟨(S, K, L), h⟩

theorem delta_blocks {r c : ℕ} {H : Mat r c} (hH : H ∈ Alt (ι r c)) :
    delta r c H = blocks ((H.submatrix Top Bot).transpose + H.submatrix Top Bot +
      H.submatrix Bot Bot) (H.submatrix Bot Bot) (H.submatrix Bot Rest) := by
  rw [delta_expand]
  apply Matrix.ext
  intro i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp only [Matrix.add_apply, mul_Nt_entry, N_mul_entry, blocks, Matrix.of_apply,
      Matrix.submatrix_apply, Matrix.transpose_apply, Top, Bot, Rest, zero_add, add_zero]
  · exact congrArg (fun x => x + H (Top i) (Bot j) + H (Bot i) (Bot j))
      (alt_symm hH (Bot i) (Top j))
  · exact alt_symm hH (Bot i) (Bot j)
  · exact alt_symm hH (Rest i) (Bot j)

private theorem transpose_add_self_mem_Alt {α : Type} (X : Matrix α α F) :
    X.transpose + X ∈ Alt α :=
  ⟨fun i j => add_comm (X j i) (X i j), fun i => CharTwo.add_self_eq_zero (X i i)⟩

private def strictUpper {r : ℕ} (M : Matrix (Fin r) (Fin r) F) : Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i j => if i < j then M i j else 0

private theorem strictUpper_decompose {r : ℕ} {M : Matrix (Fin r) (Fin r) F}
    (h : M ∈ Alt (Fin r)) : (strictUpper M).transpose + strictUpper M = M := by
  apply Matrix.ext
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [strictUpper, hij, not_lt_of_gt hij]
  · simp [strictUpper, alt_diag h]
  · change (if j < i then M j i else 0) + (if i < j then M i j else 0) = M i j
    simp only [if_pos hji, if_neg (not_lt_of_gt hji), add_zero]
    exact alt_symm h j i

private def liftBlocks {r c : ℕ} (A K : Matrix (Fin r) (Fin r) F)
    (L : Matrix (Fin r) (Fin c) F) : Mat r c := Matrix.of fun
  | .inl i, .inr (.inl j) => A i j
  | .inr (.inl i), .inl j => A j i
  | .inr (.inl i), .inr (.inl j) => K i j
  | .inr (.inl i), .inr (.inr j) => L i j
  | .inr (.inr i), .inr (.inl j) => L j i
  | _, _ => 0

private theorem liftBlocks_mem_Alt {r c : ℕ} (A : Matrix (Fin r) (Fin r) F)
    (K : Alt (Fin r)) (L : Matrix (Fin r) (Fin c) F) : liftBlocks A K L ∈ Alt (ι r c) := by
  refine ⟨?_, ?_⟩
  · intro i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;> try rfl
    exact alt_symm K.property i j
  · intro i
    rcases i with i | (i | i) <;> try rfl
    exact alt_diag K.property i

theorem blocks_has_preimage {r c : ℕ} (S K : Alt (Fin r))
    (L : Matrix (Fin r) (Fin c) F) : ∃ H : Alt (ι r c), imageMap r c H = blocks S K L := by
  let A := strictUpper ((S : Matrix (Fin r) (Fin r) F) + (K : Matrix (Fin r) (Fin r) F))
  have hA : A.transpose + A = (S : Matrix (Fin r) (Fin r) F) + (K : Matrix (Fin r) (Fin r) F) :=
    strictUpper_decompose ((Alt (Fin r)).add_mem S.property K.property)
  have hH := liftBlocks_mem_Alt A K L
  refine ⟨⟨liftBlocks A K L, hH⟩, ?_⟩
  change delta r c (liftBlocks A K L) = blocks S K L
  rw [delta_blocks hH]
  change blocks (A.transpose + A + (K : Matrix (Fin r) (Fin r) F)) K L = blocks S K L
  have hS : (S : Matrix (Fin r) (Fin r) F) + (K : Matrix (Fin r) (Fin r) F) +
      (K : Matrix (Fin r) (Fin r) F) = S :=
    Matrix.ext fun i j => CharTwo.add_cancel_right _ _
  rw [hA, hS]

theorem W_eq_range (r c : ℕ) : W r c = LinearMap.range (imageMap r c) := by
  apply le_antisymm
  · intro M hM
    obtain ⟨S, K, L, rfl⟩ := mem_W_iff.mp hM
    exact LinearMap.mem_range.mpr (blocks_has_preimage S K L)
  · intro M hM
    obtain ⟨H, rfl⟩ := LinearMap.mem_range.mp hM
    change delta r c (H : Mat r c) ∈ W r c
    rw [delta_blocks H.property]
    let K : Alt (Fin r) := ⟨(H : Mat r c).submatrix Bot Bot,
      fun i j => alt_symm H.property (Bot i) (Bot j), fun i => alt_diag H.property (Bot i)⟩
    let X := (H : Mat r c).submatrix Top Bot
    exact mem_W_iff.mpr
      ⟨⟨X.transpose + X + K, (Alt (Fin r)).add_mem (transpose_add_self_mem_Alt X) K.property⟩,
        K, (H : Mat r c).submatrix Bot Rest, rfl⟩

theorem mem_W_iff_image {r c : ℕ} {M : Mat r c} :
    M ∈ W r c ↔ ∃ H : Mat r c, (H.transpose = H ∧ ∀ i, H i i = 0) ∧
      J r c * H * (J r c).transpose + H = M := by
  rw [W_eq_range, LinearMap.mem_range]
  constructor
  · rintro ⟨H, h⟩
    exact ⟨H, mem_Alt_iff.mp H.property, h⟩
  · rintro ⟨H, hAlt, h⟩
    exact ⟨⟨H, mem_Alt_iff.mpr hAlt⟩, h⟩

theorem finrank_W (r c : ℕ) : Module.finrank F (W r c) = 2 * Nat.choose r 2 + r * c := by
  change Module.finrank F (LinearMap.range (assemble r c)) = _
  rw [LinearMap.finrank_range_of_inj (assemble_injective r c)]
  simp only [Module.finrank_prod, finrank_Alt, Module.finrank_matrix, Fintype.card_fin,
    Module.finrank_self, mul_one]
  omega

def projK (r c : ℕ) : W r c →ₗ[F] Alt (Fin r) where
  toFun M := ⟨(M : Mat r c).submatrix Top Bot, by
    obtain ⟨S, K, L, h⟩ := mem_W_iff.mp M.property
    rw [← h]
    exact K.property⟩
  map_add' M M' := Subtype.ext (Matrix.ext fun _ _ => rfl)
  map_smul' a M := Subtype.ext (Matrix.ext fun _ _ => rfl)

theorem projK_apply (r c : ℕ) (M : W r c) :
    (projK r c M : Matrix (Fin r) (Fin r) F) = (M : Mat r c).submatrix Top Bot := rfl

theorem projK_surjective (r c : ℕ) : Function.Surjective (projK r c) := by
  intro K
  refine ⟨⟨blocks 0 K 0, mem_W_iff.mpr ⟨0, K, 0, rfl⟩⟩, ?_⟩
  exact Subtype.ext (Matrix.ext fun _ _ => rfl)

theorem W_BB {r c : ℕ} (M : W r c) : (M : Mat r c).submatrix (@Bot r c) (@Bot r c) = 0 := by
  obtain ⟨S, K, L, h⟩ := mem_W_iff.mp M.property
  rw [← h] <;> exact Matrix.ext fun _ _ => rfl

theorem W_BT {r c : ℕ} (M : W r c) :
    (M : Mat r c).submatrix Bot Top = (projK r c M : Matrix (Fin r) (Fin r) F).transpose := by
  rw [projK_apply]
  obtain ⟨S, K, L, h⟩ := mem_W_iff.mp M.property
  rw [← h] <;> exact Matrix.ext fun _ _ => rfl

end Blocks

namespace Normal

open Matrix

abbrev F := ZMod 2
abbrev ι (r c : ℕ) := Fin r ⊕ (Fin r ⊕ Fin c)
abbrev Top {r c : ℕ} (i : Fin r) : ι r c := Sum.inl i
abbrev Bot {r c : ℕ} (i : Fin r) : ι r c := Sum.inr (Sum.inl i)
abbrev Rest {r c : ℕ} (i : Fin c) : ι r c := Sum.inr (Sum.inr i)

def N (r c : ℕ) : Matrix (ι r c) (ι r c) F :=
  Matrix.fromBlocks 0 (Matrix.fromCols 1 0) 0 0

def J (r c : ℕ) : Matrix (ι r c) (ι r c) F := 1 + N r c

@[simp] theorem N_apply_top_bot {r c : ℕ} (i j : Fin r) :
    N r c (Top i) (Bot j) = (1 : Matrix (Fin r) (Fin r) F) i j := rfl

@[simp] theorem N_apply_top_top {r c : ℕ} (i j : Fin r) :
    N r c (Top i) (Top j) = 0 := rfl

@[simp] theorem N_apply_top_rest {r c : ℕ} (i : Fin r) (j : Fin c) :
    N r c (Top i) (Rest j) = 0 := rfl

@[simp] theorem N_apply_bot {r c : ℕ} (i : Fin r) (j : ι r c) :
    N r c (Bot i) j = 0 := by cases j <;> rfl

@[simp] theorem N_apply_rest {r c : ℕ} (i : Fin c) (j : ι r c) :
    N r c (Rest i) j = 0 := by cases j <;> rfl

@[simp] theorem N_mulVec_top {r c : ℕ} (x : ι r c → F) (i : Fin r) :
    (N r c *ᵥ x) (Top i) = x (Bot i) := by
  simp [N, Matrix.fromBlocks_mulVec, Matrix.fromCols_mulVec, Function.comp_apply]

@[simp] theorem N_mulVec_bot {r c : ℕ} (x : ι r c → F) (i : Fin r) :
    (N r c *ᵥ x) (Bot i) = 0 := by
  simp [N, Matrix.fromBlocks_mulVec]

@[simp] theorem N_mulVec_rest {r c : ℕ} (x : ι r c → F) (i : Fin c) :
    (N r c *ᵥ x) (Rest i) = 0 := by
  simp [N, Matrix.fromBlocks_mulVec]

theorem exists_normal_coordinates {d : ℕ} (U : Matrix (Fin d) (Fin d) F) (hU : U * U = 1) :
    ∃ c : ℕ, d = 2 * (U - 1).rank + c ∧
      ∃ e : (Fin d → F) ≃ₗ[F] (ι (U - 1).rank c → F),
        ∀ x, e (U *ᵥ x) = J (U - 1).rank c *ᵥ e x := by
  let V := Fin d → F
  let f : V →ₗ[F] V := (U - 1).mulVecLin
  let r := (U - 1).rank
  have hr : Module.finrank F f.range = r := rfl
  have hminus : U - 1 = U + 1 := by
    apply Matrix.ext
    intro i j
    exact CharTwo.sub_eq_add _ _
  have hadd (A : Matrix (Fin d) (Fin d) F) : A + A = 0 := by
    apply Matrix.ext
    intro i j
    exact CharTwo.add_self_eq_zero _
  have hN : (U - 1) * (U - 1) = 0 := by
    calc
      (U - 1) * (U - 1) = (U + 1) * (U + 1) := by rw [hminus]
      _ = (1 + U) + (U + 1) := by
        simp only [Matrix.add_mul, Matrix.mul_add, one_mul, mul_one, hU]
      _ = (1 + 1) + (U + U) := by abel
      _ = 0 := by rw [hadd 1, hadd U, zero_add]
  have hfk : f.range ≤ f.ker := by
    rintro _ ⟨x, rfl⟩
    change (U - 1) *ᵥ ((U - 1) *ᵥ x) = 0
    rw [Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec]

  let inc : f.range →ₗ[F] f.ker := Submodule.inclusion hfk
  let ei : f.range ≃ₗ[F] inc.range :=
    LinearEquiv.ofInjective inc (Submodule.inclusion_injective hfk)
  obtain ⟨P, hP⟩ := Submodule.exists_isCompl inc.range
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl f.ker
  let er : (f.range × P) ≃ₗ[F] f.ker :=
    (ei.prodCongr (LinearEquiv.refl F P)).trans (inc.range.prodEquivOfIsCompl P hP)
  let eq : Q ≃ₗ[F] f.range := (f.ker.quotientEquivOfIsCompl Q hQ).symm.trans f.quotKerEquivRange
  have her (a : f.range) : (er (a, 0) : V) = (a : V) := by
    simp [er, ei, inc]
  have heq (q : Q) : (eq q : V) = f (q : V) := rfl
  have hq (a : f.range) : f (eq.symm a : V) = (a : V) := by
    rw [← heq, eq.apply_symm_apply]

  let c := Module.finrank F P
  let br := (Module.finBasisOfFinrankEq F f.range hr).equivFun
  letI : Module.Free F P := Module.Free.of_divisionRing F P
  let bc := (Module.finBasis F P).equivFun
  let e₀ : (ι r c → F) ≃ₗ[F] (Fin r → F) × ((Fin r → F) × (Fin c → F)) :=
    (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin r ⊕ Fin c) F F).trans
      ((LinearEquiv.refl F (Fin r → F)).prodCongr
        (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin c) F F))
  let e₁ : (f.range × (f.range × P)) ≃ₗ[F] ((f.range × P) × f.range) :=
    ((LinearEquiv.refl F f.range).prodCongr (LinearEquiv.prodComm F f.range P)).trans
      (LinearEquiv.prodAssoc F f.range P f.range).symm
  let b : (ι r c → F) ≃ₗ[F] V :=
    (e₀.trans (br.symm.prodCongr (br.symm.prodCongr bc.symm))).trans
      (e₁.trans ((er.prodCongr eq.symm).trans (f.ker.prodEquivOfIsCompl Q hQ)))
  have hb (x : ι r c → F) :
      b x = (er (br.symm (fun i => x (Top i)), bc.symm (fun i => x (Rest i))) : V) +
        (eq.symm (br.symm (fun i => x (Bot i))) : V) := rfl
  have hfB (x : ι r c → F) : f (b x) = (br.symm (fun i => x (Bot i)) : V) := by
    simp only [hb, map_add, LinearMap.map_coe_ker, zero_add, hq]
  have hbN (x : ι r c → F) : b (N r c *ᵥ x) = (br.symm (fun i => x (Bot i)) : V) := by
    simp only [hb, N_mulVec_top, N_mulVec_bot, N_mulVec_rest]
    change (er (br.symm (fun i => x (Bot i)), bc.symm 0) : V) +
      (eq.symm (br.symm 0) : V) = (br.symm (fun i => x (Bot i)) : V)
    simp only [map_zero, her, Submodule.coe_zero, add_zero]
  have hUb (x : ι r c → F) : U *ᵥ b x = b (J r c *ᵥ x) := by
    rw [J, Matrix.add_mulVec, Matrix.one_mulVec, map_add, (hbN x).trans (hfB x).symm]
    change U *ᵥ b x = b x + (U - 1) *ᵥ b x
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  refine ⟨c, ?_, b.symm, ?_⟩
  · have hdim := b.finrank_eq
    simp only [Module.finrank_fintype_fun_eq_card, ι, V, Fintype.card_sum, Fintype.card_fin] at hdim
    change d = 2 * r + c
    omega
  · intro x
    have h := congrArg b.symm (hUb (b.symm x))
    simpa only [b.apply_symm_apply, b.symm_apply_apply] using h

theorem exists_normal_matrices {d : ℕ} (U : Matrix (Fin d) (Fin d) F) (hU : U * U = 1) :
    ∃ c : ℕ, d = 2 * (U - 1).rank + c ∧
      ∃ (S : Matrix (ι (U - 1).rank c) (Fin d) F) (T : Matrix (Fin d) (ι (U - 1).rank c) F),
        T * S = 1 ∧ S * T = 1 ∧ S * U * T = J (U - 1).rank c := by
  obtain ⟨c, hc, e, he⟩ := exists_normal_coordinates U hU
  let S := e.toLinearMap.toMatrix'
  let T := e.symm.toLinearMap.toMatrix'
  have hTS : T * S = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simpa only [S, T, Matrix.toLin'_mul, Matrix.toLin'_one, Matrix.toLin'_toMatrix',
      LinearMap.comp_apply, LinearMap.id_apply, LinearEquiv.coe_coe] using e.symm_apply_apply x
  have hST : S * T = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simpa only [S, T, Matrix.toLin'_mul, Matrix.toLin'_one, Matrix.toLin'_toMatrix',
      LinearMap.comp_apply, LinearMap.id_apply, LinearEquiv.coe_coe] using e.apply_symm_apply x
  have hSU : S * U = J (U - 1).rank c * S := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simpa only [S, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', LinearMap.comp_apply,
      LinearEquiv.coe_coe, Matrix.toLin'_apply] using he x
  exact ⟨c, hc, S, T, hTS, hST, by rw [hSU, Matrix.mul_assoc, hST, mul_one]⟩

section Transport

variable {m n : Type*} [Fintype m] [Fintype n]

def Alt (H : Matrix n n F) : Prop := Hᵀ = H ∧ ∀ i, H i i = 0

theorem alt_iff_toBilin' [DecidableEq n] (H : Matrix n n F) :
    Alt H ↔ (Matrix.toBilin' H).IsAlt := by
  constructor
  · intro h x
    rw [Matrix.toBilin'_apply, ← Fintype.sum_prod_type']
    apply Finset.sum_ninvolution Prod.swap
    · rintro ⟨i, j⟩
      change x i * H i j * x j + x j * H j i * x i = 0
      have hs : H j i = H i j := congrFun (congrFun h.1 i) j
      rw [hs, show x j * H i j * x i = x i * H i j * x j by ac_rfl]
      exact CharTwo.add_self_eq_zero _
    · rintro ⟨i, j⟩ hne heq
      have hij : j = i := congrArg Prod.fst heq
      subst j
      exact hne (by simp [h.2])
    · intro p
      exact Finset.mem_univ _
    · rintro ⟨i, j⟩
      rfl
  · intro h
    refine ⟨?_, fun i => by simpa only [Matrix.toBilin'_single] using h (Pi.single i 1)⟩
    apply Matrix.ext
    intro i j
    simpa only [Matrix.transpose_apply, Matrix.toBilin'_single, CharTwo.neg_eq] using
      (LinearMap.IsAlt.neg h (Pi.single i 1) (Pi.single j 1)).symm

def congruence (S : Matrix m n F) : Matrix n n F →ₗ[F] Matrix m m F where
  toFun H := S * H * Sᵀ
  map_add' A B := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' a A := by simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem congruence_apply (S : Matrix m n F) (H : Matrix n n F) :
    congruence S H = S * H * Sᵀ := rfl

theorem alt_congruence (S : Matrix m n F) {H : Matrix n n F} (h : Alt H) :
    Alt (congruence S H) := by
  classical
  apply (alt_iff_toBilin' _).2
  have hcomp := Matrix.toBilin'_comp H Sᵀ Sᵀ
  rw [Matrix.transpose_transpose] at hcomp
  rw [congruence_apply, ← hcomp]
  intro x
  exact (alt_iff_toBilin' H).1 h ((Sᵀ).toLin' x)

theorem congruence_cancel [DecidableEq n] {S : Matrix m n F} {T : Matrix n m F}
    (hTS : T * S = 1) (H : Matrix n n F) : congruence T (congruence S H) = H := by
  have ht : Sᵀ * Tᵀ = 1 := by rw [← Matrix.transpose_mul, hTS, Matrix.transpose_one]
  calc
    congruence T (congruence S H) = (T * S) * H * (Sᵀ * Tᵀ) := by
      simp only [congruence_apply, Matrix.mul_assoc]
    _ = H := by rw [hTS, ht, one_mul, mul_one]

theorem rank_congruence_le (S : Matrix m n F) (H : Matrix n n F) :
    (congruence S H).rank ≤ H.rank :=
  (Matrix.rank_mul_le_left (S * H) Sᵀ).trans (Matrix.rank_mul_le_right S H)

theorem rank_congruence [DecidableEq n] {S : Matrix m n F} {T : Matrix n m F}
    (hTS : T * S = 1) (H : Matrix n n F) : (congruence S H).rank = H.rank := by
  apply le_antisymm (rank_congruence_le S H)
  calc
    H.rank = (congruence T (congruence S H)).rank := by rw [congruence_cancel hTS]
    _ ≤ (congruence S H).rank := rank_congruence_le T _

theorem congruence_correction (S : Matrix m n F) (U : Matrix n n F) (V : Matrix m m F)
    (hSU : S * U = V * S) (H : Matrix n n F) :
    congruence S (U * H * Uᵀ + H) = V * congruence S H * Vᵀ + congruence S H := by
  have ht : Uᵀ * Sᵀ = Sᵀ * Vᵀ := by
    rw [← Matrix.transpose_mul, hSU, Matrix.transpose_mul]
  rw [map_add]
  have h₁ : congruence S (U * H * Uᵀ) = V * congruence S H * Vᵀ := by
    calc
      _ = (S * U) * H * (Uᵀ * Sᵀ) := by simp only [congruence_apply, Matrix.mul_assoc]
      _ = _ := by rw [hSU, ht]; simp only [congruence_apply, Matrix.mul_assoc]
  rw [h₁]

theorem transport_corrections [DecidableEq m] [DecidableEq n] {α : Type*}
    {S : Matrix m n F} {T : Matrix n m F} (hTS : T * S = 1) (hST : S * T = 1)
    {U : Matrix n n F} {V : Matrix m m F} (hSUV : S * U * T = V)
    (R : α → Matrix n n F)
    (hR : ∀ H : Matrix n n F, Alt H → U * H * Uᵀ + H ∈ Submodule.span F (Set.range R)) :
    (∀ i, (congruence S (R i)).rank = (R i).rank) ∧
      ∀ H : Matrix m m F, Alt H →
        V * H * Vᵀ + H ∈ Submodule.span F (Set.range (fun i => congruence S (R i))) := by
  have hSU : S * U = V * S := by rw [← hSUV, Matrix.mul_assoc, hTS, Matrix.mul_one]
  refine ⟨fun i => rank_congruence hTS (R i), ?_⟩
  intro H hH
  have hm : congruence S (U * congruence T H * Uᵀ + congruence T H) ∈
      (Submodule.span F (Set.range R)).map (congruence S) :=
    Submodule.mem_map_of_mem (hR _ (alt_congruence T hH))
  rw [Submodule.map_span, ← Set.range_comp' (congruence S) R, congruence_correction S U V hSU,
    congruence_cancel hST] at hm
  exact hm

end Transport

end Normal

open Matrix Module

namespace Cosets

section LinearAlgebra

variable {F a b k : Type*} [Field F]

abbrev colspace [Fintype b] (M : Matrix a b F) := LinearMap.range M.mulVecLin
abbrev rowspace [Fintype a] (M : Matrix a b F) := colspace Mᵀ

private theorem col_mem_colspace [Fintype b] (M : Matrix a b F) (j : b) :
    M.col j ∈ colspace M := by
  change M.col j ∈ M.mulVecLin.range
  rw [Matrix.range_mulVecLin]
  exact Submodule.subset_span (Set.mem_range_self j)

private theorem colspace_add_le_sup [Fintype b] (R T : Matrix a b F) :
    colspace (R + T) ≤ colspace R ⊔ colspace T := by
  rintro _ ⟨x, rfl⟩
  rw [Matrix.mulVecLin_add, LinearMap.add_apply]
  have hxR : R.mulVecLin x ∈ colspace R := ⟨x, rfl⟩
  have hxT : T.mulVecLin x ∈ colspace T := ⟨x, rfl⟩
  exact Submodule.add_mem _ ((show colspace R ≤ colspace R ⊔ colspace T from le_sup_left) hxR)
    ((show colspace T ≤ colspace R ⊔ colspace T from le_sup_right) hxT)

theorem colspace_add_eq_sup [Fintype a] [Fintype b] (R T : Matrix a b F)
    (h : R.rank + T.rank ≤ (R + T).rank) :
    colspace (R + T) = colspace R ⊔ colspace T := by
  apply Submodule.eq_of_le_of_finrank_le (colspace_add_le_sup R T)
  exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans h

private theorem rank_add_le [Fintype a] [Fintype b] (R T : Matrix a b F) :
    (R + T).rank ≤ R.rank + T.rank := by
  exact (Submodule.finrank_mono (colspace_add_le_sup R T)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem two_le_rank_of_cross_ne_zero [Fintype a] {K : Matrix a a F}
    (hs : K.IsSymm) (hd : ∀ i, K i i = 0) (hK : K ≠ 0) : 2 ≤ K.rank := by
  classical
  have hex : ∃ i j, K i j ≠ 0 := by
    by_contra! hn
    exact hK (Matrix.ext fun i j => hn i j)
  obtain ⟨i, j, hij⟩ := hex
  let e : Fin 2 → a := ![i, j]
  let A := K.submatrix e e
  have hdet : A.det ≠ 0 := by
    rw [Matrix.det_fin_two]
    change K i i * K j j - K i j * K j i ≠ 0
    rw [hd i, hd j, zero_mul, zero_sub, hs.apply i j]
    exact neg_ne_zero.mpr (mul_ne_zero hij hij)
  have hrank : A.rank = 2 := by
    have hinj : Function.Injective A.mulVecLin := Matrix.mulVec_injective_of_det_ne_zero hdet
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_pi, Fintype.card_fin]
  calc
    2 = A.rank := hrank.symm
    _ ≤ K.rank := K.rank_submatrix_le e e

def extendTop : (a → F) →ₗ[F] (a ⊕ b) → F where
  toFun x := Sum.elim x 0
  map_add' x y := by
    funext i
    rcases i with i | i
    · rfl
    · change (0 : F) = 0 + 0
      rw [zero_add]
  map_smul' t x := by
    funext i
    rcases i with i | i
    · rfl
    · change (0 : F) = t • (0 : F)
      rw [smul_zero]

abbrev restrictBot (e : k → b) : ((a ⊕ b) → F) →ₗ[F] k → F :=
  LinearMap.funLeft F F (Sum.inr ∘ e)

abbrev upper (M : Matrix (a ⊕ b) (a ⊕ b) F) (e : k → b) : Matrix a k F :=
  M.submatrix Sum.inl (Sum.inr ∘ e)

abbrev lower (M : Matrix (a ⊕ b) (a ⊕ b) F) (e : k → b) : Matrix k a F :=
  M.submatrix (Sum.inr ∘ e) Sum.inl

section Blocks

variable [Fintype a] [Fintype b] [Fintype k]
variable {M : Matrix (a ⊕ b) (a ⊕ b) F} {e : k → b}

theorem map_restrictBot_colspace (hrow : ∀ i j, M (.inr (e i)) (.inr j) = 0) :
    (colspace M).map (restrictBot e) = colspace (lower M e) := by
  change M.mulVecLin.range.map (restrictBot e) = (lower M e).mulVecLin.range
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin, Submodule.map_span]
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    rcases j with j | j
    · exact Submodule.subset_span (Set.mem_range_self j)
    · have hz : restrictBot e (M.col (.inr j)) = 0 := funext fun i => hrow i j
      rw [hz]
      exact Submodule.zero_mem _
  · rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨M.col (.inl j), Set.mem_range_self _, rfl⟩

theorem map_extendTop_le (hcol : ∀ i j, M (.inr i) (.inr (e j)) = 0) :
    (colspace (upper M e)).map extendTop ≤ colspace M ⊓ LinearMap.ker (restrictBot e) := by
  change (upper M e).mulVecLin.range.map extendTop ≤ colspace M ⊓ LinearMap.ker (restrictBot e)
  rw [Matrix.range_mulVecLin, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  refine ⟨?_, LinearMap.mem_ker.mpr rfl⟩
  have heq : extendTop ((upper M e).col j) = M.col (.inr (e j)) := by
    funext i
    rcases i with i | i
    · rfl
    · exact (hcol i j).symm
  rw [heq]
  exact col_mem_colspace M _

private theorem finrank_map_extendTop :
    finrank F ((colspace (upper M e)).map extendTop : Submodule F ((a ⊕ b) → F)) =
      (upper M e).rank := by
  have hinj : Function.Injective (extendTop : (a → F) →ₗ[F] (a ⊕ b) → F) := by
    intro x y h
    funext i
    exact congrFun h (.inl i)
  exact (Submodule.equivMapOfInjective extendTop hinj (colspace (upper M e))).finrank_eq.symm

private theorem bottom_rank_nullity (hrow : ∀ i j, M (.inr (e i)) (.inr j) = 0) :
    (lower M e).rank + finrank F (colspace M ⊓ LinearMap.ker (restrictBot e) :
      Submodule F ((a ⊕ b) → F)) = M.rank := by
  let Q : Submodule F ((a ⊕ b) → F) := colspace M ⊓ LinearMap.ker (restrictBot e)
  have hQ : Q ≤ colspace M := inf_le_left
  have hk : LinearMap.ker ((restrictBot e).domRestrict (colspace M)) =
      Q.comap (colspace M).subtype := by
    ext x
    change (restrictBot e (x : (a ⊕ b) → F) = 0) ↔ (x : (a ⊕ b) → F) ∈ Q
    exact ⟨fun h => ⟨x.property, LinearMap.mem_ker.mpr h⟩,
      fun h => LinearMap.mem_ker.mp h.2⟩
  have h := LinearMap.finrank_range_add_finrank_ker ((restrictBot e).domRestrict (colspace M))
  rw [LinearMap.range_domRestrict, map_restrictBot_colspace hrow, hk,
    (Submodule.comapSubtypeEquivOfLe hQ).finrank_eq] at h
  exact h

theorem rank_cross_le (hrow : ∀ i j, M (.inr (e i)) (.inr j) = 0)
    (hcol : ∀ i j, M (.inr i) (.inr (e j)) = 0) :
    (upper M e).rank + (lower M e).rank ≤ M.rank := by
  have h := Submodule.finrank_mono (map_extendTop_le hcol)
  rw [finrank_map_extendTop] at h
  have hnull := bottom_rank_nullity hrow
  omega

theorem map_extendTop_eq_of_rank (hrow : ∀ i j, M (.inr (e i)) (.inr j) = 0)
    (hcol : ∀ i j, M (.inr i) (.inr (e j)) = 0)
    (hr : M.rank ≤ (upper M e).rank + (lower M e).rank) :
    (colspace (upper M e)).map extendTop = colspace M ⊓ LinearMap.ker (restrictBot e) := by
  apply Submodule.eq_of_le_of_finrank_le (map_extendTop_le hcol)
  rw [finrank_map_extendTop]
  have hnull := bottom_rank_nullity hrow
  omega

theorem cross_eq_zero_of_rank_le_two_blocks {A : Matrix (a ⊕ a) (a ⊕ a) F}
    (hr : A.rank ≤ 2) (hBB : ∀ i j, A (.inr i) (.inr j) = 0)
    (hBA : lower A id = (upper A id)ᵀ)
    (hs : (upper A id).IsSymm) (hd : ∀ i, upper A id i i = 0) : upper A id = 0 := by
  by_contra hn
  have hlow := rank_cross_le (M := A) (e := id) hBB hBB
  rw [hBA, Matrix.rank_transpose] at hlow
  have htwo := two_le_rank_of_cross_ne_zero hs hd hn
  omega

end Blocks

theorem cross_eq_zero_of_rank_le_two [Fintype a] [Fintype b] {A : Matrix b b F}
    (top bot : a → b) (hr : A.rank ≤ 2) (hBB : ∀ i j, A (bot i) (bot j) = 0)
    (hBA : A.submatrix bot top = (A.submatrix top bot)ᵀ)
    (hs : (A.submatrix top bot).IsSymm) (hd : ∀ i, A (top i) (bot i) = 0) :
    A.submatrix top bot = 0 := by
  let e : a ⊕ a → b := Sum.elim top bot
  let B := A.submatrix e e
  have hB : B.rank ≤ 2 := (A.rank_submatrix_le e e).trans hr
  exact cross_eq_zero_of_rank_le_two_blocks (A := B) hB hBB hBA hs hd

end LinearAlgebra

abbrev F₂ := ZMod 2
abbrev Index (r c : ℕ) := Fin r ⊕ (Fin r ⊕ Fin c)
abbrev Mat (r c : ℕ) := Matrix (Index r c) (Index r c) F₂
abbrev Top {r c : ℕ} : Fin r → Index r c := Sum.inl
abbrev Bot {r c : ℕ} : Fin r → Index r c := Sum.inr ∘ Sum.inl
abbrev cross {r c : ℕ} (D : Mat r c) := upper D (Sum.inl : Fin r → Fin r ⊕ Fin c)

structure CrossShape {r c : ℕ} (D : Mat r c) : Prop where
  symm : D.IsSymm
  cross_symm : (cross D).IsSymm
  cross_diag : ∀ i, cross D i i = 0
  bot_zero : ∀ (i : Fin r) (j : Fin r ⊕ Fin c), D (Bot i) (.inr j) = 0

variable {r c : ℕ}

private theorem CrossShape.bot_col_zero {D : Mat r c} (h : CrossShape D) :
    ∀ (i : Fin r ⊕ Fin c) (j : Fin r), D (.inr i) (Bot j) = 0 :=
  fun i j => (h.symm.apply (Bot j) (.inr i)).trans (h.bot_zero j i)

private theorem CrossShape.lower_eq {D : Mat r c} (h : CrossShape D) :
    lower D (Sum.inl : Fin r → Fin r ⊕ Fin c) = cross D := by
  ext i j
  exact (h.symm.apply (Top j) (Bot i)).trans (h.cross_symm.apply i j)

theorem same_coset_rank_spaces {R T : Mat r c} (hR : R.rank ≤ 2) (hT : T.rank ≤ 2)
    (hD : CrossShape (R + T)) (hK : cross (R + T) ≠ 0) :
    (R + T).rank = 4 ∧ (cross (R + T)).rank = 2 ∧ R.rank = 2 ∧ T.rank = 2 ∧
    colspace (R + T) = colspace R ⊔ colspace T ∧
    rowspace (R + T) = rowspace R ⊔ rowspace T := by
  let e : Fin r → Fin r ⊕ Fin c := Sum.inl
  have hlo := rank_cross_le (M := R + T) (e := e) hD.bot_zero hD.bot_col_zero
  rw [hD.lower_eq] at hlo
  change (cross (R + T)).rank + (cross (R + T)).rank ≤ (R + T).rank at hlo
  have htwo := two_le_rank_of_cross_ne_zero hD.cross_symm hD.cross_diag hK
  have hhi := rank_add_le R T
  refine ⟨by omega, by omega, by omega, by omega, colspace_add_eq_sup R T (by omega), ?_⟩
  have hs : Rᵀ.rank + Tᵀ.rank ≤ (Rᵀ + Tᵀ).rank := by
    rw [← Matrix.transpose_add, Matrix.rank_transpose, Matrix.rank_transpose,
      Matrix.rank_transpose]
    omega
  simpa only [rowspace, Matrix.transpose_add] using colspace_add_eq_sup Rᵀ Tᵀ hs

theorem same_coset_spaces_le {R T : Mat r c} (hR : R.rank ≤ 2) (hT : T.rank ≤ 2)
    (hD : CrossShape (R + T)) (hK : cross (R + T) ≠ 0) :
    colspace T ≤ colspace (R + T) ∧ rowspace T ≤ rowspace (R + T) := by
  obtain ⟨_, _, _, _, hc, hr⟩ := same_coset_rank_spaces hR hT hD hK
  rw [hc, hr]
  exact ⟨le_sup_right, le_sup_right⟩

theorem same_coset_common_vector (T : Mat r c) (hT : T.rank ≤ 2) (S : Set (Mat r c))
    (hS : ∀ R ∈ S, cross (R + T) ≠ 0 → R.rank ≤ 2 ∧ CrossShape (R + T)) :
    ∃ v : Fin r → F₂, (v ≠ 0 ↔ ∃ R ∈ S, cross (R + T) ≠ 0) ∧
      ∀ R ∈ S, cross (R + T) ≠ 0 → v ∈ colspace (cross (R + T)) := by
  classical
  by_cases hex : ∃ R ∈ S, cross (R + T) ≠ 0
  · obtain ⟨R₀, hR₀, hK₀⟩ := hex
    obtain ⟨hR₀rank, hD₀⟩ := hS R₀ hR₀ hK₀
    have hTrank := (same_coset_rank_spaces hR₀rank hT hD₀ hK₀).2.2.2.1
    have hx : ∃ x ∈ colspace T, x ≠ 0 := by
      by_contra! hn
      have hz : colspace T = ⊥ := (Submodule.eq_bot_iff (colspace T)).mpr hn
      change finrank F₂ (colspace T) = 2 at hTrank
      have hh := congrArg (fun S : Submodule F₂ (Index r c → F₂) => finrank F₂ S) hz
      have he : finrank F₂ (colspace T) = 0 := hh.trans (by simp)
      omega
    obtain ⟨x, hxT, hxne⟩ := hx
    let e : Fin r → Fin r ⊕ Fin c := Sum.inl
    have hxD (R : Mat r c) (hR : R ∈ S) (hK : cross (R + T) ≠ 0) :
        x ∈ colspace (R + T) := by
      obtain ⟨hr, hd⟩ := hS R hR hK
      exact (same_coset_spaces_le hr hT hd hK).1 hxT
    have hex' : ∃ R ∈ S, cross (R + T) ≠ 0 := ⟨R₀, hR₀, hK₀⟩
    by_cases hb : restrictBot e x = 0
    · have hxmap (R : Mat r c) (hR : R ∈ S) (hK : cross (R + T) ≠ 0) :
          x ∈ (colspace (cross (R + T))).map extendTop := by
        obtain ⟨hr, hd⟩ := hS R hR hK
        have hranks := same_coset_rank_spaces hr hT hd hK
        have hsat : (R + T).rank ≤ (upper (R + T) e).rank + (lower (R + T) e).rank := by
          rw [hd.lower_eq]
          change (R + T).rank ≤ (cross (R + T)).rank + (cross (R + T)).rank
          rw [hranks.1, hranks.2.1] <;> omega
        rw [map_extendTop_eq_of_rank (M := R + T) (e := e) hd.bot_zero hd.bot_col_zero hsat]
        exact ⟨hxD R hR hK, LinearMap.mem_ker.mpr hb⟩
      let v : Fin r → F₂ := x ∘ Top
      have hv : v ≠ 0 := by
        obtain ⟨y, _, hy⟩ := hxmap R₀ hR₀ hK₀
        have hyv : y = v := funext fun i => congrFun hy (Top i)
        intro hz
        apply hxne
        rw [← hy, hyv, hz, map_zero]
      refine ⟨v, ⟨fun _ => hex', fun _ => hv⟩, ?_⟩
      intro R hR hK
      obtain ⟨y, hy, hyx⟩ := hxmap R hR hK
      have hyv : y = v := funext fun i => congrFun hyx (Top i)
      exact hyv ▸ hy
    · refine ⟨restrictBot e x, ⟨fun _ => hex', fun _ => hb⟩, ?_⟩
      intro R hR hK
      obtain ⟨_, hd⟩ := hS R hR hK
      rw [← hd.lower_eq, ← map_restrictBot_colspace (M := R + T) (e := e) hd.bot_zero]
      exact ⟨x, hxD R hR hK, rfl⟩
  · refine ⟨0, ⟨fun hn => (hn rfl).elim, fun hp => (hex hp).elim⟩, ?_⟩
    intro R hR hK
    exact Submodule.zero_mem _

section Compression

variable {a b : Type*} [Fintype a] [Fintype b]

private theorem alternating_dot {K : Matrix a a F₂} (hs : K.IsSymm)
    (hd : ∀ i, K i i = 0) (x : a → F₂) : x ⬝ᵥ K *ᵥ x = 0 := by
  classical
  have hsum (s : Finset a) : ∑ i ∈ s, ∑ j ∈ s, x i * K i j * x j = 0 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, hd, mul_zero, zero_mul, zero_add,
        Finset.sum_add_distrib, ih, add_zero]
      have heq : (∑ j ∈ s, x j * K j i * x i) = ∑ j ∈ s, x i * K i j * x j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hs.apply i j]
        ring
      rw [heq, CharTwo.add_self_eq_zero]
  simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using hsum Finset.univ

theorem compress_cross_eq_zero {K : Matrix a a F₂} (hs : K.IsSymm)
    (hd : ∀ i, K i i = 0) (hK : K.rank ≤ 2) {v : a → F₂} (hv : v ≠ 0)
    (hmem : v ∈ colspace K) (P : Matrix b a F₂) (hPv : P *ᵥ v = 0) : P * K * Pᵀ = 0 := by
  let f := P.mulVecLin.domRestrict (colspace K)
  have hk : LinearMap.ker f ≠ ⊥ := by
    intro hz
    have hm : (⟨v, hmem⟩ : colspace K) ∈ LinearMap.ker f := LinearMap.mem_ker.mpr hPv
    rw [hz] at hm
    exact hv (congrArg Subtype.val ((Submodule.mem_bot F₂).mp hm))
  have hkpos : 0 < finrank F₂ (LinearMap.ker f) := by
    exact Nat.pos_of_ne_zero (fun he => hk (Submodule.finrank_eq_zero.mp he))
  have hnull := LinearMap.finrank_range_add_finrank_ker f
  change finrank F₂ (LinearMap.range f) + finrank F₂ (LinearMap.ker f) = K.rank at hnull
  have hrange : LinearMap.range f = (colspace K).map P.mulVecLin :=
    LinearMap.range_domRestrict _ _
  have hrank : (P * K).rank ≤ 1 := by
    rw [Matrix.rank, Matrix.mulVecLin_mul, LinearMap.range_comp, ← hrange]
    omega
  have hsymm : (P * K * Pᵀ).IsSymm := by
    show (P * K * Pᵀ)ᵀ = P * K * Pᵀ
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hs.eq,
      Matrix.mul_assoc]
  have hdiag (i : b) : (P * K * Pᵀ) i i = 0 := by
    calc
      _ = (P i) ⬝ᵥ K *ᵥ (P i) := by rw [dotProduct_mulVec] <;> rfl
      _ = 0 := alternating_dot hs hd _
  by_contra hn
  have hlow := two_le_rank_of_cross_ne_zero hsymm hdiag hn
  have hhi := Matrix.rank_mul_le_left (P * K) Pᵀ
  omega

end Compression

end Cosets

open scoped Matrix BigOperators
namespace Support

abbrev F := ZMod 2
abbrev V (n : ℕ) := Fin n → F
abbrev Sq (ι : Type*) := Matrix ι ι F

def Alt {ι : Type*} (K : Sq ι) : Prop := K.transpose = K ∧ ∀ i, K i i = 0

lemma alt_symm {ι : Type*} {K : Sq ι} (hK : Alt K) (i j : ι) : K i j = K j i :=
  (congrFun (congrFun hK.1 i) j).symm

lemma alt_split {ι : Type*} [Fintype ι] {K : Sq ι} (hK : Alt K) : ∃ A : Sq ι, K = A + A.transpose := by
  classical
  let e := Fintype.equivFin ι
  let A : Sq ι := fun i j => if e i < e j then K i j else 0
  refine ⟨A, ?_⟩
  ext i j
  change K i j = A i j + A j i
  rcases lt_trichotomy (e i) (e j) with h | h | h
  · simp [A, h, not_lt_of_gt h]
  · have he := e.injective h
    subst j
    simp [A, hK.2]
  · simp [A, h, not_lt_of_gt h, alt_symm hK i j]

lemma alt_of_sum {ι : Type*} (A : Sq ι) : Alt (A + A.transpose) := by
  refine ⟨by rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm], fun i => ?_⟩
  change A i i + A i i = 0
  exact CharTwo.add_self_eq_zero _

lemma alt_congr {ι κ : Type*} [Fintype ι] {K : Sq ι} (hK : Alt K) (P : Matrix κ ι F) :
    Alt (P * K * P.transpose) := by
  obtain ⟨A, rfl⟩ := alt_split hK
  have he : P * (A + A.transpose) * P.transpose =
      (P * A * P.transpose) + (P * A * P.transpose).transpose := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  rw [he]
  exact alt_of_sum _

lemma congr_onto {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : Matrix κ ι F) (A : Matrix ι κ F) (hp : P * A = 1) {K : Sq κ} (hK : Alt K) :
    ∃ L : Sq ι, Alt L ∧ P * L * P.transpose = K := by
  refine ⟨A * K * A.transpose, alt_congr hK A, ?_⟩
  calc
    _ = (P*A) * K * (P*A).transpose := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = _ := by simp only [hp, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

lemma projectAway {r : ℕ} (T : Submodule F (V r)) :
    ∃ (k : ℕ) (P : Matrix (Fin k) (Fin r) F) (A : Matrix (Fin r) (Fin k) F),
      k + Module.finrank F T = r ∧ P * A = 1 ∧ ∀ x ∈ T, P *ᵥ x = 0 := by
  classical
  let k := Module.finrank F (V r ⧸ T)
  let e := (Module.finBasis F (V r ⧸ T)).equivFun
  let p : V r →ₗ[F] V k := e.toLinearMap.comp T.mkQ
  have hs : Function.Surjective p := e.surjective.comp T.mkQ_surjective
  obtain ⟨a, ha⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hs)
  refine ⟨k, p.toMatrix', a.toMatrix', ?_, ?_, ?_⟩
  · simpa [k] using T.finrank_quotient_add_finrank
  · rw [← LinearMap.toMatrix'_comp, ha, LinearMap.toMatrix'_id]
  · intro x hx
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix', LinearMap.comp_apply]
    rw [show T.mkQ x = 0 from (Submodule.Quotient.mk_eq_zero T).mpr hx, map_zero]

lemma finrank_sup_finset {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    {ι : Type*} (I : Finset ι) (T : ι → Submodule F V) :
    Module.finrank F ↥(I.sup T : Submodule F V) ≤ ∑ i ∈ I, Module.finrank F (T i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hi ih =>
    rw [Finset.sup_insert, Finset.sum_insert hi]
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)

lemma pick_rep {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W : Submodule F V) {t : ℕ} (R : Fin t → V) (hR : Submodule.span F (Set.range R) = ⊤) :
    ∃ I : Finset (Fin t), I.card ≤ Module.finrank F (V ⧸ W) ∧
      ∀ v : V, v ∈ W ⊔ Submodule.span F (R '' ↑I) := by
  classical
  let Q := V ⧸ W
  let f : Fin t → Q := fun i => W.mkQ (R i)
  have hs : ⊤ ≤ Submodule.span F (Set.range f) := by
    rw [show Set.range f = W.mkQ '' Set.range R from (Set.range_comp W.mkQ R),
      ← Submodule.map_span, hR, Submodule.map_top, LinearMap.range_eq_top.mpr W.mkQ_surjective]
  let ιb := ↥((linearIndepOn_empty F id).extend (Set.empty_subset (Set.range f)))
  let b : Module.Basis ιb F Q := Module.Basis.ofSpan hs
  have hb (i : _) : ∃ j, f j = b i := Module.Basis.ofSpan_subset hs (Set.mem_range_self i)
  choose sel hsel using hb
  letI : Finite ιb := Module.Finite.finite_basis b
  letI : Fintype ιb := Fintype.ofFinite ιb
  let I := Finset.univ.image sel
  refine ⟨I, ?_, fun v => ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, ← Module.finrank_eq_card_basis b]
  let T := Submodule.span F (R '' ↑I)
  have hq : T.map W.mkQ = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    exact Submodule.span_le.mpr (by
      rintro _ ⟨i, rfl⟩
      refine Submodule.mem_map.mpr ⟨R (sel i), ?_, hsel i⟩
      exact Submodule.subset_span ⟨sel i, Finset.mem_image_of_mem sel (Finset.mem_univ i), rfl⟩)
  have hv : W.mkQ v ∈ T.map W.mkQ := by rw [hq]; exact Submodule.mem_top
  obtain ⟨u, hu, huv⟩ := Submodule.mem_map.mp hv
  have hd : v-u ∈ W := by
    apply (Submodule.Quotient.mk_eq_zero W).mp
    change W.mkQ (v-u) = 0
    rw [map_sub, huv, sub_self]
  exact Submodule.mem_sup.mpr ⟨v-u, hd, u, hu, sub_add_cancel ..⟩

end Support

namespace QuotientCount
abbrev F := ZMod 2

noncomputable def occ {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) {t : ℕ} (R : Fin t → V) : Finset (V ⧸ W) := by
  classical
  exact (Finset.univ.image (fun i => W.mkQ (R i))).erase 0

lemma occ_le {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W : Submodule F V) {t : ℕ} (R : Fin t → V) :
    (occ W R).card ≤ 2 ^ Module.finrank F (V ⧸ W) - 1 := by
  classical
  let Q := V ⧸ W
  let e := (Module.finBasis F Q).equivFun
  letI : Fintype Q := Fintype.ofEquiv _ e.toEquiv.symm
  have hQ : Fintype.card Q = 2 ^ Module.finrank F Q := by
    rw [Fintype.card_congr e.toEquiv, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  calc
    _ ≤ ((Finset.univ : Finset Q).erase 0).card := by
      apply Finset.card_le_card
      exact Finset.erase_subset_erase _ (Finset.subset_univ _)
    _ = _ := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hQ]

lemma occ_rank {V Y : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    [AddCommGroup Y] [Module F Y] (W : Submodule F V) {t : ℕ} (R : Fin t → V)
    (hR : Submodule.span F (Set.range R) = ⊤) (L : V →ₗ[F] Y) (Z : Submodule F Y)
    (hz : ∀ z ∈ Z, ∃ w ∈ W, L w = z)
    (hzero : ∀ i, W.mkQ (R i) = 0 → L (R i) = 0)
    (hsame : ∀ i j, W.mkQ (R i) = W.mkQ (R j) → L (R i) = L (R j)) :
    Module.finrank F (V ⧸ W) + Module.finrank F Z ≤ (occ W R).card := by
  classical
  let Q := V ⧸ W
  let J : V →ₗ[F] Q × Y := W.mkQ.prod L
  let M := J.range
  let O := occ W R
  have hreps (x : O) : ∃ i : Fin t, W.mkQ (R i) = x.val := by
    have hm : x.val ∈ (Finset.univ.image (fun i => W.mkQ (R i))).erase 0 := x.property
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hm).2
    exact ⟨i, hi⟩
  choose rep hrep using hreps
  let f : O → Q × Y := fun x => J (R (rep x))
  have hM : M ≤ Submodule.span F (Set.range f) := by
    rw [LinearMap.range_le_iff_comap]
    apply top_unique
    rw [← hR]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change J (R i) ∈ Submodule.span F (Set.range f)
    by_cases h : W.mkQ (R i) = 0
    · have he : J (R i) = 0 := Prod.ext h (hzero i h)
      rw [he]
      exact Submodule.zero_mem _
    · have hm : W.mkQ (R i) ∈ O := Finset.mem_erase.mpr
        ⟨h, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
      let x : O := ⟨W.mkQ (R i), hm⟩
      have hq : W.mkQ (R (rep x)) = W.mkQ (R i) := hrep x
      have he : f x = J (R i) := Prod.ext hq (hsame (rep x) i hq)
      exact he ▸ Submodule.subset_span (Set.mem_range_self x)
  have hmCard : Module.finrank F M ≤ O.card := by
    haveI := Module.Finite.span_of_finite F (Set.finite_range f)
    have hcr : Module.finrank F (Submodule.span F (Set.range f)) ≤ Fintype.card O :=
      finrank_range_le_card f
    exact (Submodule.finrank_mono hM).trans (hcr.trans_eq (Fintype.card_coe O))
  let P : M →ₗ[F] Q := (LinearMap.fst F Q Y).domRestrict M
  have hp : Function.Surjective P := by
    intro q
    obtain ⟨v,hv⟩ := W.mkQ_surjective q
    exact ⟨⟨J v, LinearMap.mem_range_self J v⟩, hv⟩
  have hSum : Module.finrank F Q + Module.finrank F P.ker = Module.finrank F M := by
    have hh := P.ker.finrank_quotient_add_finrank
    rw [P.quotKerEquivRange.finrank_eq, LinearMap.range_eq_top.mpr hp, finrank_top] at hh
    exact hh
  let I : Z →ₗ[F] Q × Y := (LinearMap.inr F Q Y).comp Z.subtype
  have hI (z : Z) : I z ∈ M := by
    obtain ⟨w, hw, he⟩ := hz z.val z.property
    exact ⟨w, Prod.ext ((Submodule.Quotient.mk_eq_zero W).mpr hw) he⟩
  let I' := I.codRestrict M hI
  let I'' := I'.codRestrict P.ker (fun _ => LinearMap.mem_ker.mpr rfl)
  have hin : Function.Injective I'' := by
    intro z y hy
    exact Subtype.ext (congrArg (fun v : P.ker => (v.val.val).2) hy)
  exact (Nat.add_le_add_left (LinearMap.finrank_le_finrank_of_injective hin) _).trans
    (hSum.trans_le hmCard)

lemma pow_sub_sub_mono : Monotone (fun s : ℕ => 2^s - 1 - s) := by
  apply monotone_nat_of_le_succ
  intro s
  have hp (n : ℕ) : n+1 ≤ 2^n := by
    induction n with
    | zero => decide
    | succ k hk => rw [pow_succ]; omega
  have h := hp s
  rw [pow_succ]
  omega

lemma coset_bounds_arith {s h m r c : ℕ} (hsh : s ≤ h) (hm : m ≤ 2^s-1)
    (hrc : r-m ≤ c) (hc : s + Nat.choose c 2 ≤ m) :
    Nat.choose (r-(2^h-1)) 2 ≤ (2^h-1)-h := by
  have hmq : m ≤ 2^h-1 := hm.trans (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by decide) hsh) _)
  have hx : r-(2^h-1) ≤ c := (Nat.sub_le_sub_left hmq _).trans hrc
  have hy := Nat.choose_le_choose 2 hx
  have hz := pow_sub_sub_mono hsh
  change 2^s-1-s ≤ 2^h-1-h at hz
  omega

end QuotientCount

open scoped Matrix BigOperators
namespace Canonical
open Blocks
open Support (projectAway finrank_sup_finset pick_rep alt_congr congr_onto)
open Cosets (CrossShape cross_eq_zero_of_rank_le_two cross_eq_zero_of_rank_le_two_blocks same_coset_common_vector same_coset_rank_spaces compress_cross_eq_zero)

private def cut {a b a' b' : Type} (u : a' → a) (v : b' → b) : Matrix a b F →ₗ[F] Matrix a' b' F where
  toFun M := M.submatrix u v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def sandwich {a b : Type} [Fintype a] (P : Matrix b a F) : Matrix a a F →ₗ[F] Matrix b b F where
  toFun H := P * H * P.transpose
  map_add' _ _ := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' _ _ := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

private abbrev bitsel {r c : ℕ} : Fin r ⊕ Fin r → ι r c := Sum.elim Top Bot

private def packed {r c k : ℕ} (P : Matrix (Fin k) (Fin r) F) : Mat r c →ₗ[F] Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F :=
  (sandwich (Matrix.fromBlocks P 0 0 P)).comp (cut bitsel bitsel)

private lemma packed_blocks {r c k : ℕ} (P : Matrix (Fin k) (Fin r) F) (H : Mat r c) :
    packed P H = Matrix.fromBlocks
      (P * H.submatrix Top Top * P.transpose) (P * H.submatrix Top Bot * P.transpose)
      (P * H.submatrix Bot Top * P.transpose) (P * H.submatrix Bot Bot * P.transpose) := by
  have he : H.submatrix bitsel bitsel = Matrix.fromBlocks
      (H.submatrix Top Top) (H.submatrix Top Bot) (H.submatrix Bot Top) (H.submatrix Bot Bot) := by
    ext i j
    cases i <;> cases j <;> rfl
  let Q := Matrix.fromBlocks P 0 0 P
  change Q * H.submatrix bitsel bitsel * Q.transpose = _
  rw [he]
  simp [Q, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]

private lemma packed_rank {r c k : ℕ} (P : Matrix (Fin k) (Fin r) F) (H : Mat r c) :
    (packed P H).rank ≤ H.rank := by
  let Q := Matrix.fromBlocks P 0 0 P
  change (Q * H.submatrix bitsel bitsel * Q.transpose).rank ≤ H.rank
  exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans (Matrix.rank_submatrix_le _ _ _))

private lemma mul_killed {a b k : Type} [Fintype a] [Fintype b] [DecidableEq b]
    (P : Matrix k a F) (M : Matrix a b F) (h : ∀ x ∈ M.mulVecLin.range, P *ᵥ x = 0) : P*M = 0 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simp only [Matrix.toLin'_apply, Matrix.zero_mulVec]
  rw [← Matrix.mulVec_mulVec]
  exact h _ ⟨x,rfl⟩

private lemma cut_killed {r c k : ℕ} (P : Matrix (Fin k) (Fin r) F) (H : Mat r c)
    (hC : ∀ x ∈ (H.submatrix Bot id).mulVecLin.range, P *ᵥ x = 0)
    (hR : ∀ x ∈ (H.transpose.submatrix Bot id).mulVecLin.range, P *ᵥ x = 0) :
    P * H.submatrix Top Bot * P.transpose = 0 ∧
    P * H.submatrix Bot Top * P.transpose = 0 ∧
    P * H.submatrix Bot Bot * P.transpose = 0 := by
  have hc := mul_killed P _ hC
  have hr := mul_killed P _ hR
  have hit (f : Fin r → ι r c) : P * H.submatrix Bot f = 0 := by
    ext i j
    exact congrFun (congrFun hc i) (f j)
  have hit' (f : Fin r → ι r c) : P * H.transpose.submatrix Bot f = 0 := by
    ext i j
    exact congrFun (congrFun hr i) (f j)
  refine ⟨?_, by rw [hit, Matrix.zero_mul], by rw [hit, Matrix.zero_mul]⟩
  have he : H.submatrix Top Bot * P.transpose = 0 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_submatrix, Matrix.transpose_transpose,
      Matrix.transpose_zero] using congrArg Matrix.transpose (hit' Top)
  rw [Matrix.mul_assoc, he, Matrix.mul_zero]

private lemma canonical_shape {r c : ℕ} {H : Mat r c} (hH : H ∈ W r c) : CrossShape H := by
  obtain ⟨A,B,L,rfl⟩ := mem_W_iff.mp hH
  refine ⟨?_, (mem_Alt_iff.mp B.property).1, B.property.2, ?_⟩
  · apply Matrix.ext
    intro i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j)
    all_goals first | rfl | exact A.property.1 _ _
  · intro i j
    cases j <;> rfl

private lemma cross_zero {r c : ℕ} {H : Mat r c} (hh : H ∈ W r c) (hr : H.rank ≤ 2) :
    H.submatrix Top Bot = 0 := by
  let Z : W r c := ⟨H, hh⟩
  have h := canonical_shape hh
  exact cross_eq_zero_of_rank_le_two (@Blocks.Top r c) Bot hr
    (fun i j => h.bot_zero i (.inl j)) (W_BT Z)
    h.cross_symm h.cross_diag

set_option maxHeartbeats 500000 in
private lemma compression_vanish {r c t : ℕ} {M : Submodule F (Mat r c)}
    (Wle : W r c ≤ M) (R : Fin t → M) (hr : ∀ i, (R i : Mat r c).rank ≤ 2)
    (hgen : Submodule.span F (Set.range R) = ⊤) :
    r ≤ 4 * Module.finrank F (M ⧸ (W r c).comap M.subtype) + 1 := by
  classical
  let B := (W r c).comap M.subtype
  obtain ⟨I, hIs, hAll⟩ := pick_rep B R hgen
  let T₁ (i : Fin t) := ((R i : Mat r c).submatrix Bot id).mulVecLin.range
  let T₂ (i : Fin t) := ((R i : Mat r c).transpose.submatrix Bot id).mulVecLin.range
  let T := I.sup (fun i => T₁ i ⊔ T₂ i)
  have hT : Module.finrank F T ≤ 4 * I.card := by
    calc
      _ ≤ ∑ i ∈ I, Module.finrank F (T₁ i ⊔ T₂ i : Submodule F (Fin r → F)) := finrank_sup_finset I _
      _ ≤ ∑ _i ∈ I, 4 := Finset.sum_le_sum (fun i _ => by
        have hc : Module.finrank F (T₁ i) ≤ 2 := (Matrix.rank_submatrix_le _ _ _).trans (hr i)
        have ht : (R i : Mat r c).transpose.rank ≤ 2 := by rw [Matrix.rank_transpose]; exact hr i
        have hb : Module.finrank F (T₂ i) ≤ 2 := (Matrix.rank_submatrix_le _ _ _).trans ht
        have hd := Submodule.finrank_add_le_finrank_add_finrank (T₁ i) (T₂ i)
        omega)
      _ = _ := by simp [Nat.mul_comm]
  obtain ⟨k,P,A, hk, hPA, hPT⟩ := projectAway T
  let L₁ := ((sandwich P).comp (cut (@Top r c) (@Bot r c))).comp M.subtype
  let L₂ := ((sandwich P).comp (cut (@Bot r c) (@Top r c))).comp M.subtype
  let L₃ := ((sandwich P).comp (cut (@Bot r c) (@Bot r c))).comp M.subtype
  let L := L₁.prod (L₂.prod L₃)
  have hchosen : Submodule.span F (R '' ↑I) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    have hsub : T₁ i ⊔ T₂ i ≤ T := Finset.le_sup (f := fun j => T₁ j ⊔ T₂ j) hi
    have hs₁ : T₁ i ≤ T := (show T₁ i ≤ T₁ i ⊔ T₂ i from le_sup_left).trans hsub
    have hs₂ : T₂ i ≤ T := (show T₂ i ≤ T₁ i ⊔ T₂ i from le_sup_right).trans hsub
    have hc (x : Fin r → F) (hx : x ∈ T₁ i) : P *ᵥ x = 0 := hPT x (hs₁ hx)
    have hb (x : Fin r → F) (hx : x ∈ T₂ i) : P *ᵥ x = 0 := hPT x (hs₂ hx)
    obtain ⟨e₁,e₂,e₃⟩ := cut_killed P (R i : Mat r c) hc hb
    exact LinearMap.mem_ker.mpr (Prod.ext e₁ (Prod.ext e₂ e₃))
  have hkernel (i : Fin t) : L₁ (R i) = 0 := by
    obtain ⟨w, hw, v, hv, he⟩ := Submodule.mem_sup.mp (hAll (R i))
    have hz : L v = 0 := hchosen hv
    have heq : L (R i) = L w := by
      rw [← he, map_add, hz, add_zero]
    have h₁ : L₁ (R i) = L₁ w := congrArg Prod.fst heq
    have h₂ : L₂ (R i) = L₂ w := congrArg (fun x => x.2.1) heq
    have h₃ : L₃ (R i) = L₃ w := congrArg (fun x => x.2.2) heq
    let Z : W r c := ⟨w.val, hw⟩
    have hb : L₃ w = 0 := by
      change P * w.val.submatrix Bot Bot * P.transpose = 0
      rw [W_BB Z, Matrix.mul_zero, Matrix.zero_mul]
    have hbt : L₂ w = (L₁ w).transpose := by
      change P * w.val.submatrix Bot Top * P.transpose =
        (P * w.val.submatrix Top Bot * P.transpose).transpose
      rw [W_BT Z]
      simp only [projK_apply, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      rfl
    have hhAlt : (L₁ w).transpose = L₁ w ∧ ∀ i, L₁ w i i = 0 :=
      alt_congr (mem_Alt_iff.mp (projK r c Z).property) P
    let C := packed P (R i : Mat r c)
    have hp := packed_blocks P (R i : Mat r c)
    have hu : C.submatrix Sum.inl Sum.inr = L₁ (R i) := congrArg Matrix.toBlocks₁₂ hp
    have hd : C.submatrix Sum.inr Sum.inl = L₂ (R i) := congrArg Matrix.toBlocks₂₁ hp
    have hbb : C.submatrix Sum.inr Sum.inr = L₃ (R i) := congrArg Matrix.toBlocks₂₂ hp
    have hC := (packed_rank P (R i : Mat r c)).trans (hr i)
    have hz := cross_eq_zero_of_rank_le_two Sum.inl Sum.inr hC
      (fun a b => congrFun (congrFun (hbb.trans (h₃.trans hb)) a) b)
      (by rw [hd, h₂, hbt, hu, h₁]) (by rw [hu,h₁]; exact hhAlt.1)
      (fun a => congrFun (congrFun (hu.trans h₁) a) a |>.trans (hhAlt.2 a))
    exact hu.symm.trans hz
  have hVanAll : L₁ = 0 := by
    have htop : (⊤ : Submodule F M) ≤ L₁.ker := by
      rw [← hgen]
      exact Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hkernel i)
    exact LinearMap.ker_eq_top.mp (top_unique htop)
  have hkAlt (K : Alt (Fin k)) : K.val = 0 := by
    obtain ⟨N,hN,hEq⟩ := congr_onto P A hPA (mem_Alt_iff.mp K.property)
    let N' : Alt (Fin r) := ⟨N, mem_Alt_iff.mpr hN⟩
    let H : W r c := ⟨blocks 0 N' 0, mem_W_iff.mpr ⟨0, N', 0, rfl⟩⟩
    exact hEq.symm.trans (congrArg (fun f : M →ₗ[F] _ => f ⟨H.val, Wle H.property⟩) hVanAll)
  have hb : Module.finrank F (Alt (Fin k)) = 0 := by
    have hbot : Alt (Fin k) = ⊥ := (Submodule.eq_bot_iff _).mpr (fun x hx => hkAlt ⟨x,hx⟩)
    rw [hbot, finrank_bot]
  rw [finrank_Alt] at hb
  have hsmall := Nat.choose_eq_zero_iff.mp hb
  change _ ≤ 4 * Module.finrank F (M ⧸ B) + 1
  change k + Module.finrank F T = r at hk
  change I.card ≤ Module.finrank F (M ⧸ B) at hIs
  omega

private lemma coset_vanish {r c t : ℕ} {M : Submodule F (Mat r c)}
    (Wle : W r c ≤ M) (R : Fin t → M) (hr : ∀ i, (R i : Mat r c).rank ≤ 2)
    (hgen : Submodule.span F (Set.range R) = ⊤) (h : ℕ)
    (hsh : Module.finrank F (M ⧸ (W r c).comap M.subtype) ≤ h) :
    Nat.choose (r-(2^h-1)) 2 ≤ (2^h-1)-h := by
  classical
  let B := (W r c).comap M.subtype
  let Q := M ⧸ B
  let O := QuotientCount.occ B R
  have hrep (x : O) : ∃ i : Fin t, B.mkQ (R i) = x.val := by
    have hm : x.val ∈ (Finset.univ.image (fun i => B.mkQ (R i))).erase 0 := x.property
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hm).2
    exact ⟨i, hi⟩
  choose rep hrep using hrep
  have hdiff (i j : Fin t) (he : B.mkQ (R i) = B.mkQ (R j)) :
      (R i : Mat r c) + (R j : Mat r c) ∈ W r c := by
    change R i + R j ∈ B
    apply (Submodule.Quotient.mk_eq_zero B).mp
    change B.mkQ (R i + R j) = 0
    rw [map_add, he, ZModModule.add_self]
  let G (x : O) : Set (Mat r c) := {Y | ∃ i, B.mkQ (R i) = x.val ∧ (R i : Mat r c) = Y}
  have hvec (x : O) := same_coset_common_vector (R (rep x) : Mat r c) (hr (rep x)) (G x) (by
    rintro _ ⟨i, hix, rfl⟩ _
    exact ⟨hr i, canonical_shape (hdiff i (rep x) (hix.trans (hrep x).symm))⟩)
  choose v hv using hvec
  let T := Submodule.span F (Set.range v)
  have hT : Module.finrank F T ≤ O.card := (finrank_range_le_card v).trans_eq (Fintype.card_coe O)
  obtain ⟨k, P, A, hk, hPA, hPT⟩ := projectAway T
  let L : M →ₗ[F] Matrix (Fin k) (Fin k) F := ((sandwich P).comp (cut (@Top r c) (@Bot r c))).comp M.subtype
  have hz (i : Fin t) (hi : B.mkQ (R i) = 0) : L (R i) = 0 := by
    have he : (R i : Mat r c) ∈ W r c := (Submodule.Quotient.mk_eq_zero B).mp hi
    change P * (R i : Mat r c).submatrix Top Bot * P.transpose = 0
    rw [cross_zero he (hr i), Matrix.mul_zero, Matrix.zero_mul]
  have heq (i : Fin t) (x : O) (hi : B.mkQ (R i) = x.val) : L (R i) = L (R (rep x)) := by
    have hD := hdiff i (rep x) (hi.trans (hrep x).symm)
    have hs := canonical_shape hD
    let K := ((R i : Mat r c) + (R (rep x) : Mat r c)).submatrix Top Bot
    have h0 : P * K * P.transpose = 0 := by
      by_cases hK : K = 0
      · rw [hK, Matrix.mul_zero, Matrix.zero_mul]
      have hm : (R i : Mat r c) ∈ G x := ⟨i, hi, rfl⟩
      have hne := (hv x).1.mpr ⟨(R i : Mat r c), hm, hK⟩
      have hmem := (hv x).2 _ hm hK
      have hrk := (same_coset_rank_spaces (hr i) (hr (rep x)) hs hK).2.1.le
      exact compress_cross_eq_zero hs.cross_symm hs.cross_diag hrk hne hmem P
        (hPT _ (Submodule.subset_span (Set.mem_range_self x)))
    change L (R i + R (rep x)) = 0 at h0
    rw [map_add] at h0
    exact sub_eq_zero.mp ((ZModModule.sub_eq_add (L (R i)) (L (R (rep x)))).trans h0)
  have hall (i j : Fin t) (he : B.mkQ (R i) = B.mkQ (R j)) : L (R i) = L (R j) := by
    by_cases h0 : B.mkQ (R i) = 0
    · rw [hz i h0, hz j (he.symm.trans h0)]
    · let x : O := ⟨B.mkQ (R i), Finset.mem_erase.mpr ⟨h0, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩⟩
      exact (heq i x rfl).trans (heq j x he.symm).symm
  have honto (K : Matrix (Fin k) (Fin k) F) (hK : K ∈ Alt (Fin k)) :
      ∃ w ∈ B, L w = K := by
    obtain ⟨N, hN, he⟩ := congr_onto P A hPA (mem_Alt_iff.mp hK)
    let N' : Alt (Fin r) := ⟨N, mem_Alt_iff.mpr hN⟩
    have hw : blocks 0 N' (0 : Matrix (Fin r) (Fin c) F) ∈ W r c := mem_W_iff.mpr ⟨0,N',0,rfl⟩
    exact ⟨⟨_, Wle hw⟩, hw, he⟩
  have hcard := QuotientCount.occ_rank B R hgen L (Alt (Fin k)) honto hz hall
  rw [finrank_Alt] at hcard
  change k + Module.finrank F T = r at hk
  change Module.finrank F T ≤ (QuotientCount.occ B R).card at hT
  exact QuotientCount.coset_bounds_arith hsh (QuotientCount.occ_le B R) (by omega) hcard

private lemma twice_choose (n : ℕ) : 2 * Nat.choose n 2 = n * (n-1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.mul_add, ih]
    cases n with
    | zero => decide
    | succ q => simp only [Nat.succ_sub_one]; ring

lemma canonical {r c t d : ℕ} (hd : d = 2*r+c) (R : Fin t → Mat r c)
    (hr : ∀ i, (R i).rank ≤ 2)
    (hW : W r c ≤ Submodule.span F (Set.range R)) :
    let D := r*(d-r-1)
    let h := t-D
    let q := 2^h-1
    D ≤ t ∧ r ≤ 4*h+1 ∧ Nat.choose (r-q) 2 ≤ q-h := by
  classical
  let M := Submodule.span F (Set.range R)
  let B := (W r c).comap M.subtype
  let R' (i : Fin t) : M := ⟨R i, Submodule.subset_span (Set.mem_range_self i)⟩
  have hgen : Submodule.span F (Set.range R') = ⊤ := by
    have hinj : Function.Injective M.subtype := Subtype.val_injective
    apply (Submodule.map_injective_of_injective hinj)
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype,
      ← Set.range_comp M.subtype R']
    rfl
  let D := r*(d-r-1)
  have hD : Module.finrank F (W r c) = D := by
    rw [finrank_W, twice_choose]
    change r * (r-1) + r*c = r*(d-r-1)
    by_cases hz : r = 0
    · simp [hz]
    rw [← Nat.mul_add]
    congr 1
    omega
  have hB : Module.finrank F B = D := (Submodule.comapSubtypeEquivOfLe hW).finrank_eq.trans hD
  have hdim := B.finrank_quotient_add_finrank
  rw [hB] at hdim
  have hM : Module.finrank F M ≤ t := (finrank_range_le_card R).trans_eq (Fintype.card_fin t)
  have hsh : Module.finrank F (M ⧸ B) ≤ t - D := by omega
  have hrank := compression_vanish hW R' hr hgen
  change r ≤ 4 * Module.finrank F (M ⧸ B) + 1 at hrank
  change D ≤ t ∧ r ≤ 4*(t-D)+1 ∧ _
  exact ⟨by omega, by omega, coset_vanish hW R' hr hgen _ hsh⟩

end Canonical

end PEqualNP.Outside.L_lib_943

open PEqualNP.Outside.L_lib_943 in
theorem PEqualNP.Outside.L_lib_943 : (let F := ZMod 2
∀ (d : ℕ) (U : Matrix (Fin d) (Fin d) F), U*U = 1 →
  let Mat := Matrix (Fin d) (Fin d) F
  let alt := fun (H : Mat) => H.transpose = H ∧ ∀ i, H i i = 0
  let r := (U-1).rank
  let D := r*(d-r-1)
  ∀ (t : ℕ) (R : Fin t → Mat), (∀ i, (R i).rank ≤ 2) →
    (∀ H : Mat, alt H → U*H*U.transpose + H ∈ Submodule.span F (Set.range R)) →
    let h := t-D
    let q := 2^h-1
    D ≤ t ∧ r ≤ 4*h+1 ∧ Nat.choose (r-q) 2 ≤ q-h) := by
  dsimp only
  intro d U hU
  intro t R hr hspan
  obtain ⟨c, hc, S, T, hTS, hST, hJ⟩ := Normal.exists_normal_matrices U hU
  have hJJ : Normal.J (U-1).rank c = Blocks.J (U-1).rank c := by
    rw [Normal.J, Blocks.J]
    congr 1
    ext i j
    rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
      simp [Blocks.N, Normal.N, Matrix.one_apply, Matrix.fromCols]
  rw [hJJ] at hJ
  obtain ⟨hRank, hSpan⟩ := Normal.transport_corrections hTS hST hJ R hspan
  let R' := fun i => Normal.congruence S (R i)
  have hW : Blocks.W (U-1).rank c ≤ Submodule.span (ZMod 2) (Set.range R') := by
    intro M hM
    obtain ⟨H, hH, rfl⟩ := Blocks.mem_W_iff_image.mp hM
    exact hSpan H hH
  exact Canonical.canonical hc R' (fun i => (hRank i).trans_le (hr i)) hW
