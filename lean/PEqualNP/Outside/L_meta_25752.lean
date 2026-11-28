import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25752

open Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

abbrev F2 : Type := ZMod 2

def b2f (b : Bool) : F2 := if b then 1 else 0

lemma f2_cases (x : F2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩
  interval_cases v
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma f2_add_self (x : F2) : x + x = 0 := by
  rcases f2_cases x with rfl | rfl <;> decide

lemma f2_eq_of_add_eq_zero {x y : F2} (h : x + y = 0) : x = y := by
  rcases f2_cases x with rfl | rfl <;> rcases f2_cases y with rfl | rfl <;> first | rfl | exact absurd h (by decide)

lemma b2f_xor (a b : Bool) : b2f (xor a b) = b2f a + b2f b := by
  cases a <;> cases b <;> decide

lemma b2f_and (a b : Bool) : b2f (a && b) = b2f a * b2f b := by
  cases a <;> cases b <;> decide

lemma b2f_not (a : Bool) : b2f (!a) = b2f a + 1 := by
  cases a <;> decide

lemma b2f_inj {a b : Bool} (h : b2f a = b2f b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

def nlGate (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depthStep (ds : List ℕ) (g : Gate) : List ℕ :=
  ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat]

def wireStep (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map (fun a => ws.getD a false))]

def depthsOf (width : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl depthStep (List.replicate width 0)

def wiresOf (gs : List Gate) (inp : List Bool) : List Bool :=
  gs.foldl wireStep inp

lemma nat_max_zero (a : ℕ) : max a 0 = a := max_eq_left (Nat.zero_le a)

lemma foldl_depthStep_length (ds : List ℕ) (gs : List Gate) :
    (gs.foldl depthStep ds).length = ds.length + gs.length := by
  induction gs generalizing ds with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, depthStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma depthsOf_length (width : ℕ) (gs : List Gate) :
    (depthsOf width gs).length = width + gs.length := by
  simp [depthsOf, foldl_depthStep_length]

lemma foldl_wireStep_length (ws : List Bool) (gs : List Gate) :
    (gs.foldl wireStep ws).length = ws.length + gs.length := by
  induction gs generalizing ws with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma wiresOf_length (gs : List Gate) (inp : List Bool) :
    (wiresOf gs inp).length = inp.length + gs.length := by
  simp [wiresOf, foldl_wireStep_length]

lemma getD_append_left {α : Type} (l₁ l₂ : List α) (i : ℕ) (d : α) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl l.length),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

lemma foldl_depthStep_getD_old (ds : List ℕ) (gs : List Gate) (w : ℕ) (hw : w < ds.length) :
    (gs.foldl depthStep ds).getD w 0 = ds.getD w 0 := by
  induction gs generalizing ds with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hw' : w < (depthStep ds g).length := by simp [depthStep]; omega
    rw [ih (depthStep ds g) hw']
    exact getD_append_left ds _ w 0 hw

lemma foldl_wireStep_getD_old (ws : List Bool) (gs : List Gate) (w : ℕ) (hw : w < ws.length) :
    (gs.foldl wireStep ws).getD w false = ws.getD w false := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hw' : w < (wireStep ws g).length := by simp [wireStep]; omega
    rw [ih (wireStep ws g) hw']
    exact getD_append_left ws _ w false hw

lemma gate_eval_expand_two (op : GateOp) :
    ∃ c0 c1 c2 : F2, ∀ x y : Bool,
      b2f (op.eval [x, y]) =
        c0 + c1 * b2f x + c2 * b2f y +
        b2f (xor (xor (op.eval [false, false]) (op.eval [false, true]))
                 (xor (op.eval [true, false]) (op.eval [true, true]))) * (b2f x * b2f y) := by
  refine ⟨b2f (op.eval [false, false]),
    b2f (op.eval [true, false]) + b2f (op.eval [false, false]),
    b2f (op.eval [false, true]) + b2f (op.eval [false, false]), ?_⟩
  intro x y
  have hb0 : b2f false = 0 := rfl
  have hb1 : b2f true = 1 := rfl
  simp only [b2f_xor]
  cases x <;> cases y
  · simp only [hb0, mul_zero, add_zero]
  · simp only [hb0, hb1, mul_zero, mul_one, add_zero]
    have h := f2_add_self (b2f (op.eval [false, false]))
    linear_combination -h
  · simp only [hb0, hb1, mul_zero, mul_one, add_zero]
    have h := f2_add_self (b2f (op.eval [false, false]))
    linear_combination -h
  · simp only [hb1, mul_one]
    have h1 := f2_add_self (b2f (op.eval [false, false]))
    have h2 := f2_add_self (b2f (op.eval [false, true]))
    have h3 := f2_add_self (b2f (op.eval [true, false]))
    linear_combination -h1 - h1 - h2 - h3

lemma gate_eval_expand_one (op : GateOp) :
    ∃ c0 c1 : F2, ∀ x : Bool, b2f (op.eval [x]) = c0 + c1 * b2f x := by
  refine ⟨b2f (op.eval [false]), b2f (op.eval [true]) + b2f (op.eval [false]), ?_⟩
  intro x
  have hb0 : b2f false = 0 := rfl
  have hb1 : b2f true = 1 := rfl
  cases x <;> simp only [hb0, hb1, mul_zero, mul_one, add_zero]
  have h := f2_add_self (b2f (op.eval [false]))
  linear_combination -h

-- Section 1: Matrix rank lemmas over F2

lemma rank_vecMulVec_le {n m : ℕ} (p : Fin n → F2) (q : Fin m → F2) :
    (Matrix.of fun i j => p i * q j).rank ≤ 1 := by
  let A : Matrix (Fin n) (Fin m) F2 := Matrix.of fun i j => p i * q j
  have hsub : LinearMap.range A.mulVecLin ≤ Submodule.span F2 {p} := by
    rintro _ ⟨v, rfl⟩
    have heq : A.mulVecLin v = (∑ j : Fin m, q j * v j) • p := by
      ext i
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, A,
        Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton p))
  have hle1 : Module.finrank F2 (LinearMap.range A.mulVecLin) ≤ Module.finrank F2 (Submodule.span F2 {p}) :=
    Submodule.finrank_mono hsub
  have hle2 : Module.finrank F2 (Submodule.span F2 {p}) ≤ 1 := by
    have h := finrank_span_le_card (R := F2) ({p} : Set (Fin n → F2))
    simpa using h
  exact le_trans hle1 hle2

lemma rank_add_le {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A B : Matrix ι κ F2) :
    (A + B).rank ≤ A.rank + B.rank := by
  have hsub : LinearMap.range (A + B).mulVecLin ≤ LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    have heq : (A + B).mulVecLin v = A.mulVecLin v + B.mulVecLin v := by
      ext i; simp
    rw [heq]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  have h1 : Module.finrank F2 (LinearMap.range (A + B).mulVecLin) ≤
      Module.finrank F2 (↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin)) :=
    Submodule.finrank_mono hsub
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  change Module.finrank F2 (LinearMap.range (A + B).mulVecLin) ≤
    Module.finrank F2 (LinearMap.range A.mulVecLin) + Module.finrank F2 (LinearMap.range B.mulVecLin)
  omega

lemma rank_zero_eq {n m : ℕ} : (0 : Matrix (Fin n) (Fin m) F2).rank = 0 := by
  simp [Matrix.rank]

lemma rank_sum_le {ι : Type} {n m : ℕ} (s : Finset ι) (M : ι → Matrix (Fin n) (Fin m) F2) :
    (∑ i ∈ s, M i).rank ≤ ∑ i ∈ s, (M i).rank := by
  induction s using Finset.induction_on with
  | empty => simp [rank_zero_eq]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (rank_add_le _ _) (Nat.add_le_add_left ih _)

lemma range_fromCols_eq_sup {n m₁ m₂ : ℕ} (X : Matrix (Fin n) (Fin m₁) F2) (Y : Matrix (Fin n) (Fin m₂) F2) :
    LinearMap.range (Matrix.fromCols X Y).mulVecLin =
      LinearMap.range X.mulVecLin ⊔ LinearMap.range Y.mulVecLin := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    have heq : (Matrix.fromCols X Y).mulVecLin w =
        X.mulVecLin (fun j => w (Sum.inl j)) + Y.mulVecLin (fun j => w (Sum.inr j)) := by
      ext i
      simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    rw [heq]
    exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  · refine sup_le ?_ ?_
    · rintro _ ⟨v, rfl⟩
      refine ⟨Sum.elim v 0, ?_⟩
      ext i
      simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    · rintro _ ⟨v, rfl⟩
      refine ⟨Sum.elim 0 v, ?_⟩
      ext i
      simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

lemma rank_fromCols_dup {n m : ℕ} (Z : Matrix (Fin n) (Fin m) F2) :
    (Matrix.fromCols Z Z).rank = Z.rank := by
  change Module.finrank F2 (LinearMap.range (Matrix.fromCols Z Z).mulVecLin) =
    Module.finrank F2 (LinearMap.range Z.mulVecLin)
  rw [range_fromCols_eq_sup, sup_idem]

lemma rank_fromCols_left_zero {n m : ℕ} (Y : Matrix (Fin n) (Fin m) F2) :
    (Matrix.fromCols (0 : Matrix (Fin n) (Fin m) F2) Y).rank = Y.rank := by
  change Module.finrank F2 (LinearMap.range (Matrix.fromCols (0 : Matrix (Fin n) (Fin m) F2) Y).mulVecLin) =
    Module.finrank F2 (LinearMap.range Y.mulVecLin)
  rw [range_fromCols_eq_sup]
  have h0 : LinearMap.range (0 : Matrix (Fin n) (Fin m) F2).mulVecLin = ⊥ := by
    ext v; simp
  rw [h0, bot_sup_eq]

lemma rank_fromCols_right_zero {n m : ℕ} (X : Matrix (Fin n) (Fin m) F2) :
    (Matrix.fromCols X (0 : Matrix (Fin n) (Fin m) F2)).rank = X.rank := by
  change Module.finrank F2 (LinearMap.range (Matrix.fromCols X (0 : Matrix (Fin n) (Fin m) F2)).mulVecLin) =
    Module.finrank F2 (LinearMap.range X.mulVecLin)
  rw [range_fromCols_eq_sup]
  have h0 : LinearMap.range (0 : Matrix (Fin n) (Fin m) F2).mulVecLin = ⊥ := by
    ext v; simp
  rw [h0, sup_bot_eq]

lemma rank_fromCols_split_le {n m : ℕ} (Xp Yp Z : Matrix (Fin n) (Fin m) F2) :
    (Matrix.fromCols (Xp + Z) (Yp + Z)).rank ≤ Xp.rank + Yp.rank + Z.rank := by
  have hdecomp : Matrix.fromCols (Xp + Z) (Yp + Z) =
      Matrix.fromCols Xp (0 : Matrix (Fin n) (Fin m) F2) +
      Matrix.fromCols (0 : Matrix (Fin n) (Fin m) F2) Yp +
      Matrix.fromCols Z Z := by
    ext i j
    cases j <;> simp
  rw [hdecomp]
  have h1 := rank_add_le (Matrix.fromCols Xp 0 + Matrix.fromCols 0 Yp) (Matrix.fromCols Z Z)
  have h2 := rank_add_le (Matrix.fromCols Xp (0 : Matrix (Fin n) (Fin m) F2))
    (Matrix.fromCols (0 : Matrix (Fin n) (Fin m) F2) Yp)
  rw [rank_fromCols_right_zero, rank_fromCols_left_zero] at h2
  rw [rank_fromCols_dup] at h1
  omega

lemma rank_fromCols_eq_add_imp_disjoint {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) F2)
    (h : (Matrix.fromCols X Y).rank = X.rank + Y.rank) :
    LinearMap.range X.mulVecLin ⊓ LinearMap.range Y.mulVecLin = ⊥ := by
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range X.mulVecLin) (LinearMap.range Y.mulVecLin)
  change Module.finrank F2 (LinearMap.range (Matrix.fromCols X Y).mulVecLin) =
    Module.finrank F2 (LinearMap.range X.mulVecLin) + Module.finrank F2 (LinearMap.range Y.mulVecLin) at h
  rw [range_fromCols_eq_sup] at h
  have hinf0 : Module.finrank F2 (↥(LinearMap.range X.mulVecLin ⊓ LinearMap.range Y.mulVecLin)) = 0 := by omega
  exact Submodule.finrank_eq_zero.mp hinf0

lemma rank_fromRows_eq_rank_add {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) F2)
    (hdisj : LinearMap.range X.mulVecLin ⊓ LinearMap.range Y.mulVecLin = ⊥) :
    (Matrix.fromRows X Y).rank = (X + Y).rank := by
  have hker : LinearMap.ker (Matrix.fromRows X Y).mulVecLin = LinearMap.ker (X + Y).mulVecLin := by
    ext v
    simp only [LinearMap.mem_ker]
    constructor
    · intro hv
      have hX : X.mulVecLin v = 0 := by
        ext i; have := congrFun hv (Sum.inl i); simpa [Matrix.mulVecLin_apply, Matrix.mulVec] using this
      have hY : Y.mulVecLin v = 0 := by
        ext i; have := congrFun hv (Sum.inr i); simpa [Matrix.mulVecLin_apply, Matrix.mulVec] using this
      ext i
      have hi1 := congrFun hX i
      have hi2 := congrFun hY i
      simp only [Matrix.mulVecLin_apply, Matrix.add_mulVec, Pi.add_apply, Pi.zero_apply] at hi1 hi2 ⊢
      rw [hi1, hi2, add_zero]
    · intro hv
      have hsum : X.mulVecLin v + Y.mulVecLin v = 0 := by
        ext i
        have hi := congrFun hv i
        simpa [Matrix.mulVecLin_apply, Matrix.add_mulVec, Pi.add_apply] using hi
      have heq : X.mulVecLin v = Y.mulVecLin v := by
        ext i
        exact f2_eq_of_add_eq_zero (congrFun hsum i)
      have hmem : X.mulVecLin v ∈ LinearMap.range X.mulVecLin ⊓ LinearMap.range Y.mulVecLin :=
        ⟨⟨v, rfl⟩, ⟨v, heq.symm⟩⟩
      rw [hdisj, Submodule.mem_bot] at hmem
      have hY0 : Y.mulVecLin v = 0 := heq.symm.trans hmem
      ext i
      cases i with
      | inl i =>
        have hi := congrFun hmem i
        simpa [Matrix.mulVecLin_apply, Matrix.mulVec] using hi
      | inr i =>
        have hi := congrFun hY0 i
        simpa [Matrix.mulVecLin_apply, Matrix.mulVec] using hi
  have hr1 := LinearMap.finrank_range_add_finrank_ker (Matrix.fromRows X Y).mulVecLin
  have hr2 := LinearMap.finrank_range_add_finrank_ker (X + Y).mulVecLin
  rw [hker] at hr1
  change Module.finrank F2 (LinearMap.range (Matrix.fromRows X Y).mulVecLin) =
    Module.finrank F2 (LinearMap.range (X + Y).mulVecLin)
  omega

lemma rank_decomp {n m : ℕ} (M : Matrix (Fin n) (Fin m) F2) :
    ∃ (p : Fin M.rank → Fin n → F2) (q : Fin M.rank → Fin m → F2),
      ∀ x y, M x y = ∑ i : Fin M.rank, p i x * q i y := by
  let b := Module.finBasis F2 (LinearMap.range M.mulVecLin)
  refine ⟨fun i x => (b i).1 x,
    fun i y => b.repr ⟨M.mulVec (Pi.single y 1), ⟨Pi.single y 1, rfl⟩⟩ i, ?_⟩
  intro x y
  have hlin := b.sum_repr ⟨M.mulVec (Pi.single y 1), ⟨Pi.single y 1, rfl⟩⟩
  have hval := congrFun (congrArg Subtype.val hlin) x
  simp only [Submodule.coe_sum, SetLike.val_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hval
  have hcol : M.mulVec (Pi.single y 1) x = M x y := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hcol] at hval
  rw [← hval]
  refine Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma shared_rank2_decomp {n m : ℕ} (X Y : Matrix (Fin n) (Fin m) F2)
    (hrow : (Matrix.fromRows X Y).rank + 2 ≤ X.rank + Y.rank) :
    ∃ (p1 p2 : Fin n → F2) (q1 q2 : Fin m → F2),
      (X + Matrix.of (fun x y => p1 x * q1 y + p2 x * q2 y)).rank ≤ X.rank - 1 ∧
      (Y + Matrix.of (fun x y => p1 x * q1 y + p2 x * q2 y)).rank ≤ Y.rank - 1 := by
  let RX := LinearMap.range X.transpose.mulVecLin
  let RY := LinearMap.range Y.transpose.mulVecLin
  have hRX : Module.finrank F2 RX = X.rank := by
    simpa [RX, Matrix.rank] using Matrix.rank_transpose X
  have hRY : Module.finrank F2 RY = Y.rank := by
    simpa [RY, Matrix.rank] using Matrix.rank_transpose Y
  have hsup_eq : LinearMap.range (Matrix.fromRows X Y).transpose.mulVecLin = RX ⊔ RY := by
    have ht : (Matrix.fromRows X Y).transpose = Matrix.fromCols X.transpose Y.transpose := by
      ext i j; cases j <;> rfl
    rw [ht]
    exact range_fromCols_eq_sup X.transpose Y.transpose
  have hRXY : Module.finrank F2 (↥(RX ⊔ RY)) = (Matrix.fromRows X Y).rank := by
    rw [← hsup_eq]
    simpa [Matrix.rank] using Matrix.rank_transpose (Matrix.fromRows X Y)
  have hinf_dim : 2 ≤ Module.finrank F2 (↥(RX ⊓ RY)) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq RX RY
    omega
  have hXr2 : 2 ≤ X.rank := by
    have hle : Module.finrank F2 (↥(RX ⊓ RY)) ≤ Module.finrank F2 RX := Submodule.finrank_mono inf_le_left
    omega
  have hYr2 : 2 ≤ Y.rank := by
    have hle : Module.finrank F2 (↥(RX ⊓ RY)) ≤ Module.finrank F2 RY := Submodule.finrank_mono inf_le_right
    omega
  let bI := Module.finBasis F2 (↥(RX ⊓ RY))
  let w1 : Fin m → F2 := (bI ⟨0, by omega⟩).1
  let w2 : Fin m → F2 := (bI ⟨1, by omega⟩).1
  let W : Submodule F2 (Fin m → F2) := Submodule.span F2 ({w1, w2} : Set (Fin m → F2))
  have hw1_mem : w1 ∈ RX ⊓ RY := (bI ⟨0, by omega⟩).2
  have hw2_mem : w2 ∈ RX ⊓ RY := (bI ⟨1, by omega⟩).2
  have hWX : W ≤ RX := Submodule.span_le.mpr (by
    rintro z (rfl | rfl)
    · exact hw1_mem.1
    · exact hw2_mem.1)
  have hWY : W ≤ RY := Submodule.span_le.mpr (by
    rintro z (rfl | rfl)
    · exact hw1_mem.2
    · exact hw2_mem.2)
  have hlin12 : LinearIndependent F2 (fun i : Fin 2 => if i = 0 then w1 else w2) := by
    have hb := bI.linearIndependent
    rw [Fintype.linearIndependent_iff] at hb ⊢
    intro g hg i
    let g' : Fin (Module.finrank F2 (↥(RX ⊓ RY))) → F2 := fun k =>
      if h0 : k.val = 0 then g 0 else if h1 : k.val = 1 then g 1 else 0
    let i0 : Fin (Module.finrank F2 (↥(RX ⊓ RY))) := ⟨0, by omega⟩
    let i1 : Fin (Module.finrank F2 (↥(RX ⊓ RY))) := ⟨1, by omega⟩
    have hsum' : ∑ k, g' k • bI k = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, SetLike.val_smul, ZeroMemClass.coe_zero]
      have h01 : i0 ≠ i1 := by
        intro h; have hv := congrArg Fin.val h; simp [i0, i1] at hv
      have hfilt : ∑ k : Fin (Module.finrank F2 (↥(RX ⊓ RY))), g' k • (bI k).1 =
          g 0 • w1 + g 1 • w2 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)]
        have hmem1 : i1 ∈ Finset.univ.erase i0 :=
          Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ _⟩
        rw [← Finset.add_sum_erase _ _ hmem1]
        have hrest : ∑ k ∈ (Finset.univ.erase i0).erase i1,
            g' k • (bI k).1 = 0 := by
          refine Finset.sum_eq_zero fun k hk => ?_
          have hk1 : k ≠ i1 := (Finset.mem_erase.mp hk).1
          have hk0 : k ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
          have hv0 : k.val ≠ 0 := fun h => hk0 (Fin.ext h)
          have hv1 : k.val ≠ 1 := fun h => hk1 (Fin.ext h)
          simp [g', hv0, hv1]
        rw [hrest, add_zero]
        simp [g', w1, w2, i0, i1]
      rw [hfilt]
      simpa [Fin.sum_univ_two] using hg
    have h0 := hb g' hsum'
    fin_cases i
    · have := h0 i0; simpa [g', i0] using this
    · have := h0 i1; simpa [g', i1] using this
  have hW_dim : Module.finrank F2 W = 2 := by
    have hr : Set.range (fun i : Fin 2 => if i = 0 then w1 else w2) = ({w1, w2} : Set (Fin m → F2)) := by
      ext z; simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩; fin_cases i <;> simp
      · rintro (rfl | rfl)
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩
    change Module.finrank F2 (Submodule.span F2 ({w1, w2} : Set (Fin m → F2))) = 2
    rw [← hr, finrank_span_eq_card hlin12, Fintype.card_fin]
  -- Decompose any matrix M whose row space contains W into c1*w1 + c2*w2 + M_rest with rank(M_rest) <= rank(M) - 2
  have hsplit : ∀ (M : Matrix (Fin n) (Fin m) F2),
      W ≤ LinearMap.range M.transpose.mulVecLin →
      ∃ (c1 c2 : Fin n → F2) (Mrest : Matrix (Fin n) (Fin m) F2),
        Mrest.rank ≤ M.rank - 2 ∧
        ∀ x y, M x y = c1 x * w1 y + c2 x * w2 y + Mrest x y := by
    intro M hWM
    let RM := LinearMap.range M.transpose.mulVecLin
    let Wsub : Submodule F2 RM := W.comap RM.subtype
    obtain ⟨Usub, hcompl⟩ := Submodule.exists_isCompl Wsub
    let U : Submodule F2 (Fin m → F2) := Usub.map RM.subtype
    have hWsub_dim : Module.finrank F2 Wsub = 2 := by
      have he : Wsub.map RM.subtype = W :=
        Submodule.map_comap_eq_self (by rw [Submodule.range_subtype]; exact hWM)
      have hdim : Module.finrank F2 Wsub = Module.finrank F2 (Wsub.map RM.subtype) :=
        (Submodule.equivMapOfInjective RM.subtype Subtype.val_injective Wsub).finrank_eq
      rw [he] at hdim
      omega
    have hRM_dim : Module.finrank F2 RM = M.rank := by
      simpa [RM, Matrix.rank] using Matrix.rank_transpose M
    have hU_dim : Module.finrank F2 U = M.rank - 2 := by
      have hadd := Submodule.finrank_sup_add_finrank_inf_eq Wsub Usub
      rw [hcompl.sup_eq_top, hcompl.inf_eq_bot, finrank_top, finrank_bot, add_zero, hWsub_dim, hRM_dim] at hadd
      have hdim : Module.finrank F2 Usub = Module.finrank F2 (Usub.map RM.subtype) :=
        (Submodule.equivMapOfInjective RM.subtype Subtype.val_injective Usub).finrank_eq
      change Module.finrank F2 (Usub.map RM.subtype) = M.rank - 2
      omega
    have hrow_decomp : ∀ x : Fin n, ∃ (a b : F2) (u : Fin m → F2), u ∈ U ∧
        (fun y => M x y) = a • w1 + b • w2 + u := by
      intro x
      have hx : (fun y => M x y) ∈ RM := ⟨Pi.single x 1, by
        ext y; simp [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]⟩
      have htop : (⟨fun y => M x y, hx⟩ : RM) ∈ Wsub ⊔ Usub := by
        rw [hcompl.sup_eq_top]; trivial
      obtain ⟨⟨w, hw⟩, hwW, ⟨u, hu⟩, huU, hsum⟩ := Submodule.mem_sup.mp htop
      have hw_in_W : w ∈ W := hwW
      rw [Submodule.mem_span_pair] at hw_in_W
      obtain ⟨a, b, rfl⟩ := hw_in_W
      refine ⟨a, b, u, ⟨⟨u, hu⟩, huU, rfl⟩, ?_⟩
      have hval := congrArg Subtype.val hsum
      simpa [add_assoc] using hval.symm
    choose c1 c2 uvec huU hMeq using hrow_decomp
    let Mrest : Matrix (Fin n) (Fin m) F2 := Matrix.of fun x y => uvec x y
    have hMrest_rank : Mrest.rank ≤ M.rank - 2 := by
      have hsub : LinearMap.range Mrest.transpose.mulVecLin ≤ U := by
        rintro _ ⟨v, rfl⟩
        have heq : Mrest.transpose.mulVecLin v = ∑ x : Fin n, v x • uvec x := by
          ext y
          simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
            Matrix.of_apply, Mrest, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          refine Finset.sum_congr rfl fun x _ => mul_comm _ _
        rw [heq]
        exact Submodule.sum_mem U fun x _ => Submodule.smul_mem U (v x) (huU x)
      have h1 := Submodule.finrank_mono hsub
      rw [hU_dim] at h1
      have h2 : Mrest.transpose.rank ≤ M.rank - 2 := h1
      rw [Matrix.rank_transpose] at h2
      exact h2
    refine ⟨c1, c2, Mrest, hMrest_rank, fun x y => ?_⟩
    have hxy := congrFun (hMeq x) y
    simpa [Mrest, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hxy
  obtain ⟨c1, c2, Xrest, hXrest, hXeq⟩ := hsplit X hWX
  obtain ⟨d1, d2, Yrest, hYrest, hYeq⟩ := hsplit Y hWY
  refine ⟨c1, d2, w1, w2, ?_, ?_⟩
  · have hXZ : X + Matrix.of (fun x y => c1 x * w1 y + d2 x * w2 y) =
        Matrix.of (fun x y => (c2 x + d2 x) * w2 y) + Xrest := by
      ext x y
      simp only [Matrix.add_apply, Matrix.of_apply, hXeq x y]
      have hc1 := f2_add_self (c1 x * w1 y)
      linear_combination hc1
    rw [hXZ]
    have h1 := rank_add_le (Matrix.of fun x y => (c2 x + d2 x) * w2 y) Xrest
    have h2 := rank_vecMulVec_le (fun x => c2 x + d2 x) w2
    omega
  · have hYZ : Y + Matrix.of (fun x y => c1 x * w1 y + d2 x * w2 y) =
        Matrix.of (fun x y => (d1 x + c1 x) * w1 y) + Yrest := by
      ext x y
      simp only [Matrix.add_apply, Matrix.of_apply, hYeq x y]
      have hd2 := f2_add_self (d2 x * w2 y)
      linear_combination hd2
    rw [hYZ]
    have h1 := rank_add_le (Matrix.of fun x y => (d1 x + c1 x) * w1 y) Yrest
    have h2 := rank_vecMulVec_le (fun x => d1 x + c1 x) w1
    omega

-- Section 2: Lower bound from depth-<=1 circuits

lemma oneEach_getD {n m : ℕ} (x : Fin n) (y : Fin m) (w : ℕ) (hw : w < n + m) :
    (oneEach x y).getD w false =
      if h : w < n then decide (x.val = w) else decide (y.val = w - n) := by
  simp only [oneEach]
  by_cases h : w < n
  · rw [dif_pos h]
    have hlen : w < (List.ofFn (fun i : Fin n => decide (i = x))).length := by simp [h]
    rw [getD_append_left _ _ w false hlen]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h, ↓reduceDIte, Option.getD_some]
    by_cases hx : x.val = w
    · have : (⟨w, h⟩ : Fin n) = x := Fin.ext hx.symm
      simp [this, hx]
    · have : (⟨w, h⟩ : Fin n) ≠ x := fun he => hx (congrArg Fin.val he).symm
      simp [this, hx]
  · rw [dif_neg h]
    have hge : (List.ofFn (fun i : Fin n => decide (i = x))).length ≤ w := by simp; omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, List.length_ofFn,
      List.getElem?_ofFn]
    have hwn : w - n < m := by omega
    rw [dif_pos hwn, Option.getD_some]
    by_cases hy : y.val = w - n
    · have : (⟨w - n, hwn⟩ : Fin m) = y := Fin.ext hy.symm
      simp [this, hy]
    · have : (⟨w - n, hwn⟩ : Fin m) ≠ y := fun he => hy (congrArg Fin.val he).symm
      simp [this, hy]

lemma foldr_max_le_iff (l : List ℕ) (b : ℕ) :
    l.foldr max 0 ≤ b ↔ ∀ x ∈ l, x ≤ b := by
  induction l with
  | nil => simp
  | cons a t ih => simp [max_le_iff, ih]

lemma circuit_depth1_decomp (n m : ℕ) (gs : List Gate)
    (hrb : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + m + j)
    (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ M : Fin gs.length → Matrix (Fin n) (Fin m) F2,
      (∀ k, (M k).rank ≤ 2) ∧
      ∀ w < n + m + gs.length,
        ((depthsOf (n + m) gs).getD w 0 = 0 →
          ∃ (α : Fin n → F2) (β : Fin m → F2) (c : F2),
            ∀ x y, b2f ((wiresOf gs (oneEach x y)).getD w false) = α x + β y + c) ∧
        ((depthsOf (n + m) gs).getD w 0 ≤ 1 →
          ∃ (coeff : Fin gs.length → F2) (α : Fin n → F2) (β : Fin m → F2) (c : F2),
            (∀ k, coeff k ≠ 0 → nlGate (gs.get k) = true) ∧
            ∀ x y, b2f ((wiresOf gs (oneEach x y)).getD w false) =
              (∑ k : Fin gs.length, coeff k * M k x y) + α x + β y + c) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨fun k => Fin.elim0 k, fun k => Fin.elim0 k, ?_⟩
    intro w hw
    simp only [List.length_nil, add_zero] at hw
    have hw_rep : ∃ (α : Fin n → F2) (β : Fin m → F2) (c : F2),
        ∀ x y, b2f ((wiresOf [] (oneEach x y)).getD w false) = α x + β y + c := by
      by_cases h : w < n
      · refine ⟨fun x => b2f (decide (x.val = w)), fun _ => 0, 0, fun x y => ?_⟩
        simp only [wiresOf, List.foldl_nil, oneEach_getD x y w hw, h, ↓reduceDIte, add_zero]
      · refine ⟨fun _ => 0, fun y => b2f (decide (y.val = w - n)), 0, fun x y => ?_⟩
        simp only [wiresOf, List.foldl_nil, oneEach_getD x y w hw, h, ↓reduceDIte, zero_add, add_zero]
    refine ⟨fun _ => hw_rep, fun _ => ?_⟩
    obtain ⟨α, β, c, hxy⟩ := hw_rep
    exact ⟨fun k => Fin.elim0 k, α, β, c, fun k => Fin.elim0 k, fun x y => by
      rw [hxy x y]; simp⟩
  | append_singleton gs g ih =>
    have hrb_gs : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + m + j := by
      intro j hj i hi
      have h1 := hrb j (by simp; omega) i
      have hgd : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ :=
        getD_append_left gs [g] j _ hj
      rw [hgd] at h1
      exact h1 hi
    have hfan_gs : ∀ g' ∈ gs, g'.inputs.length ≤ 2 := fun g' hg' => hfan g' (by simp [hg'])
    have hfan_g : g.inputs.length ≤ 2 := hfan g (by simp)
    have hrb_g : ∀ i ∈ g.inputs, i < n + m + gs.length := by
      intro i hi
      have h1 := hrb gs.length (by simp) i
      rw [getD_append_self gs g _] at h1
      exact h1 hi
    obtain ⟨Mprev, hMrk, hWprev⟩ := ih hrb_gs hfan_gs
    let ds := depthsOf (n + m) gs
    have hds_len : ds.length = n + m + gs.length := depthsOf_length (n + m) gs
    have hds_new : depthsOf (n + m) (gs ++ [g]) = depthStep ds g := by
      simp [depthsOf, ds, List.foldl_append]
    have hws_new : ∀ inp, wiresOf (gs ++ [g]) inp = wireStep (wiresOf gs inp) g := fun inp => by
      simp [wiresOf, List.foldl_append]
    have hws_len : ∀ (x : Fin n) (y : Fin m), (wiresOf gs (oneEach x y)).length = n + m + gs.length :=
      fun x y => by simp only [wiresOf_length, oneEach, List.length_append, List.length_ofFn]
    have hd_last : (depthsOf (n + m) (gs ++ [g])).getD (n + m + gs.length) 0 =
        (g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat := by
      rw [hds_new, depthStep, ← hds_len, getD_append_self]
    have hw_last : ∀ (x : Fin n) (y : Fin m), (wiresOf (gs ++ [g]) (oneEach x y)).getD (n + m + gs.length) false =
        g.op.eval (g.inputs.map (fun a => (wiresOf gs (oneEach x y)).getD a false)) := by
      intro x y
      rw [hws_new, wireStep, ← hws_len x y, getD_append_self]
    -- Determine the new rank-<=2 matrix M_last for gate g
    have hlast_build :
        ∃ (Mlast : Matrix (Fin n) (Fin m) F2),
          Mlast.rank ≤ 2 ∧
          ((depthsOf (n + m) (gs ++ [g])).getD (n + m + gs.length) 0 = 0 →
            ∃ (α : Fin n → F2) (β : Fin m → F2) (c : F2),
              ∀ x y, b2f ((wiresOf (gs ++ [g]) (oneEach x y)).getD (n + m + gs.length) false) =
                α x + β y + c) ∧
          ((depthsOf (n + m) (gs ++ [g])).getD (n + m + gs.length) 0 ≤ 1 →
            ∃ (coeff : Fin (gs ++ [g]).length → F2) (α : Fin n → F2) (β : Fin m → F2) (c : F2),
              (∀ k, coeff k ≠ 0 → nlGate ((gs ++ [g]).get k) = true) ∧
              ∀ x y, b2f ((wiresOf (gs ++ [g]) (oneEach x y)).getD (n + m + gs.length) false) =
                (∑ k : Fin (gs ++ [g]).length,
                  coeff k * (if hk : k.val < gs.length then Mprev ⟨k.val, hk⟩ x y else Mlast x y)) +
                α x + β y + c) := by
      cases hgin : g.inputs with
      | nil =>
        refine ⟨0, by simp [rank_zero_eq], ?_, ?_⟩
        · intro _
          refine ⟨0, 0, b2f (g.op.eval []), fun x y => by rw [hw_last, hgin]; simp⟩
        · intro _
          refine ⟨0, 0, 0, b2f (g.op.eval []), fun k hk => absurd rfl hk, fun x y => by rw [hw_last, hgin]; simp⟩
      | cons a rest =>
        cases rest with
        | nil =>
          have ha_lt : a < n + m + gs.length := hrb_g a (by simp [hgin])
          have hnl_f : nlGate g = false := by simp [nlGate, hgin]
          obtain ⟨c0, c1, hexp⟩ := gate_eval_expand_one g.op
          refine ⟨0, by simp [rank_zero_eq], ?_, ?_⟩
          · intro hd0
            rw [hd_last, hgin, hnl_f] at hd0
            have hda0 : ds.getD a 0 = 0 := by
              simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
                Bool.toNat_false, add_zero, nat_max_zero] at hd0
              omega
            obtain ⟨αa, βa, ca, hxa⟩ := (hWprev a ha_lt).1 hda0
            refine ⟨fun x => c1 * αa x, fun y => c1 * βa y, c0 + c1 * ca, fun x y => ?_⟩
            rw [hw_last, hgin]
            simp only [List.map_cons, List.map_nil, hexp, hxa x y]
            ring
          · intro hd1
            rw [hd_last, hgin, hnl_f] at hd1
            have hda1 : ds.getD a 0 ≤ 1 := by
              simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
                Bool.toNat_false, add_zero, nat_max_zero] at hd1
              omega
            obtain ⟨cfa, αa, βa, ca, hsupp, hxa⟩ := (hWprev a ha_lt).2 hda1
            let cf : Fin (gs ++ [g]).length → F2 := fun k =>
              if hk : k.val < gs.length then c1 * cfa ⟨k.val, hk⟩ else 0
            refine ⟨cf, fun x => c1 * αa x, fun y => c1 * βa y, c0 + c1 * ca, ?_, ?_⟩
            · intro k hk
              by_cases hlt : k.val < gs.length
              · simp only [cf, dif_pos hlt] at hk
                have hne : cfa ⟨k.val, hlt⟩ ≠ 0 := fun h0 => hk (by simp [h0])
                have hget : (gs ++ [g]).get k = gs.get ⟨k.val, hlt⟩ := by
                  simp [List.getElem_append_left hlt]
                rw [hget]
                exact hsupp ⟨k.val, hlt⟩ hne
              · simp only [cf, dif_neg hlt] at hk; exact absurd rfl hk
            · intro x y
              rw [hw_last, hgin]
              simp only [List.map_cons, List.map_nil, hexp, hxa x y]
              have hsum : (∑ k : Fin (gs ++ [g]).length,
                  cf k * (if hk : k.val < gs.length then Mprev ⟨k.val, hk⟩ x y else (0 : Matrix _ _ F2) x y)) =
                  c1 * ∑ k : Fin gs.length, cfa k * Mprev k x y := by
                have hlen : (gs ++ [g]).length = gs.length + 1 := by simp
                rw [Finset.mul_sum]
                let e : Fin (gs.length + 1) ≃ Fin (gs ++ [g]).length := finCongr hlen.symm
                rw [← Equiv.sum_comp e, Fin.sum_univ_castSucc]
                have hlast0 : cf (e (Fin.last gs.length)) = 0 := by
                  simp [cf, e]
                rw [hlast0, zero_mul, add_zero]
                refine Finset.sum_congr rfl fun k _ => ?_
                simp only [cf, e, finCongr_apply, Fin.val_cast, Fin.val_castSucc, Fin.eta, k.isLt, ↓reduceDIte]
                ring
              rw [hsum]; ring
        | cons b rest2 =>
          cases rest2 with
          | cons _ _ =>
            simp [hgin] at hfan_g
          | nil =>
            have ha_lt : a < n + m + gs.length := hrb_g a (by simp [hgin])
            have hb_lt : b < n + m + gs.length := hrb_g b (by simp [hgin])
            obtain ⟨c0, c1, c2, hexp⟩ := gate_eval_expand_two g.op
            have hq_eq : b2f (xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                (xor (g.op.eval [true, false]) (g.op.eval [true, true]))) = b2f (nlGate g) := by
              simp [nlGate, hgin]
            by_cases hnl : nlGate g = true
            · -- Nonlinear gate: if depth <= 1 then both inputs have depth 0
              by_cases h0ab : ds.getD a 0 = 0 ∧ ds.getD b 0 = 0
              · obtain ⟨αa, βa, ca, hxa⟩ := (hWprev a ha_lt).1 h0ab.1
                obtain ⟨αb, βb, cb, hxb⟩ := (hWprev b hb_lt).1 h0ab.2
                let Mlast : Matrix (Fin n) (Fin m) F2 :=
                  Matrix.of fun x y => αa x * βb y + αb x * βa y
                have hMlast_rk : Mlast.rank ≤ 2 := by
                  have h1 : Mlast = Matrix.of (fun x y => αa x * βb y) +
                      Matrix.of (fun x y => αb x * βa y) := by ext x y; simp [Mlast]
                  rw [h1]
                  exact le_trans (rank_add_le _ _)
                    (Nat.add_le_add (rank_vecMulVec_le αa βb) (rank_vecMulVec_le αb βa))
                refine ⟨Mlast, hMlast_rk, ?_, ?_⟩
                · intro hd0
                  rw [hd_last, hnl] at hd0; simp at hd0
                · intro _
                  let cf : Fin (gs ++ [g]).length → F2 := fun k =>
                    if k.val = gs.length then 1 else 0
                  refine ⟨cf,
                    fun x => αa x * αb x + (c1 + cb) * αa x + (c2 + ca) * αb x,
                    fun y => βa y * βb y + (c1 + cb) * βa y + (c2 + ca) * βb y,
                    c0 + c1 * ca + c2 * cb + ca * cb, ?_, ?_⟩
                  · intro k hk
                    have hkeq : k.val = gs.length := by
                      by_contra hne; simp [cf, hne] at hk
                    have hget : (gs ++ [g]).get k = g := by
                      simp [List.getElem_append_right (le_of_eq hkeq.symm), hkeq]
                    rw [hget]; exact hnl
                  · intro x y
                    rw [hw_last, hgin]
                    simp only [List.map_cons, List.map_nil]
                    rw [hexp, hq_eq, hnl, hxa x y, hxb x y]
                    have hb1 : b2f true = 1 := rfl
                    rw [hb1, one_mul]
                    have hsum : (∑ k : Fin (gs ++ [g]).length,
                        cf k * (if hk : k.val < gs.length then Mprev ⟨k.val, hk⟩ x y else Mlast x y)) =
                        Mlast x y := by
                      have hlen : (gs ++ [g]).length = gs.length + 1 := by simp
                      let e : Fin (gs.length + 1) ≃ Fin (gs ++ [g]).length := finCongr hlen.symm
                      rw [← Equiv.sum_comp e, Fin.sum_univ_castSucc]
                      have hpref : ∑ k : Fin gs.length,
                          cf (e k.castSucc) * (if hk : (e k.castSucc).val < gs.length then
                            Mprev ⟨(e k.castSucc).val, hk⟩ x y else Mlast x y) = 0 := by
                        refine Finset.sum_eq_zero fun k _ => ?_
                        have hne : (e k.castSucc).val ≠ gs.length := by simp [e]; omega
                        simp [cf, hne]
                      rw [hpref, zero_add]
                      have hnotlt : ¬ (e (Fin.last gs.length)).val < gs.length := by simp [e]
                      have heq : (e (Fin.last gs.length)).val = gs.length := by simp [e]
                      simp [cf, heq, hnotlt]
                    rw [hsum]
                    dsimp only [Mlast, Matrix.of_apply]
                    ring
              · refine ⟨0, by simp [rank_zero_eq], ?_, ?_⟩
                · intro hd0; rw [hd_last, hnl] at hd0; simp at hd0
                · intro hd1
                  rw [hd_last, hgin, hnl] at hd1
                  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
                    Bool.toNat_true, nat_max_zero] at hd1
                  exfalso; apply h0ab; constructor <;> omega
            · -- Linear 2-input gate (`nlGate g = false`)
              have hnlf : nlGate g = false := Bool.eq_false_iff.mpr hnl
              refine ⟨0, by simp [rank_zero_eq], ?_, ?_⟩
              · intro hd0
                rw [hd_last, hgin, hnlf] at hd0
                simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
                  Bool.toNat_false, add_zero, nat_max_zero] at hd0
                have hda0 : ds.getD a 0 = 0 := by omega
                have hdb0 : ds.getD b 0 = 0 := by omega
                obtain ⟨αa, βa, ca, hxa⟩ := (hWprev a ha_lt).1 hda0
                obtain ⟨αb, βb, cb, hxb⟩ := (hWprev b hb_lt).1 hdb0
                refine ⟨fun x => c1 * αa x + c2 * αb x, fun y => c1 * βa y + c2 * βb y,
                  c0 + c1 * ca + c2 * cb, fun x y => ?_⟩
                rw [hw_last, hgin]
                simp only [List.map_cons, List.map_nil]
                rw [hexp, hq_eq, hnlf, hxa x y, hxb x y]
                have hb0 : b2f false = 0 := rfl
                rw [hb0, zero_mul, add_zero]
                ring
              · intro hd1
                rw [hd_last, hgin, hnlf] at hd1
                simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
                  Bool.toNat_false, add_zero, nat_max_zero] at hd1
                have hda1 : ds.getD a 0 ≤ 1 := by omega
                have hdb1 : ds.getD b 0 ≤ 1 := by omega
                obtain ⟨cfa, αa, βa, ca, hsuppa, hxa⟩ := (hWprev a ha_lt).2 hda1
                obtain ⟨cfb, αb, βb, cb, hsuppb, hxb⟩ := (hWprev b hb_lt).2 hdb1
                let cf : Fin (gs ++ [g]).length → F2 := fun k =>
                  if hk : k.val < gs.length then c1 * cfa ⟨k.val, hk⟩ + c2 * cfb ⟨k.val, hk⟩ else 0
                refine ⟨cf, fun x => c1 * αa x + c2 * αb x, fun y => c1 * βa y + c2 * βb y,
                  c0 + c1 * ca + c2 * cb, ?_, ?_⟩
                · intro k hk
                  by_cases hlt : k.val < gs.length
                  · simp only [cf, dif_pos hlt] at hk
                    have hget : (gs ++ [g]).get k = gs.get ⟨k.val, hlt⟩ := by
                      simp [List.getElem_append_left hlt]
                    rw [hget]
                    by_cases ha0 : cfa ⟨k.val, hlt⟩ ≠ 0
                    · exact hsuppa ⟨k.val, hlt⟩ ha0
                    · push_neg at ha0
                      have hb0 : cfb ⟨k.val, hlt⟩ ≠ 0 := fun h0 => hk (by simp [ha0, h0])
                      exact hsuppb ⟨k.val, hlt⟩ hb0
                  · simp only [cf, dif_neg hlt] at hk; exact absurd rfl hk
                · intro x y
                  rw [hw_last, hgin]
                  simp only [List.map_cons, List.map_nil]
                  rw [hexp, hq_eq, hnlf, hxa x y, hxb x y]
                  have hb0 : b2f false = 0 := rfl
                  rw [hb0, zero_mul, add_zero]
                  have hsum : (∑ k : Fin (gs ++ [g]).length,
                      cf k * (if hk : k.val < gs.length then Mprev ⟨k.val, hk⟩ x y else (0 : Matrix _ _ F2) x y)) =
                      c1 * (∑ k : Fin gs.length, cfa k * Mprev k x y) +
                      c2 * (∑ k : Fin gs.length, cfb k * Mprev k x y) := by
                    have hlen : (gs ++ [g]).length = gs.length + 1 := by simp
                    let e : Fin (gs.length + 1) ≃ Fin (gs ++ [g]).length := finCongr hlen.symm
                    rw [← Equiv.sum_comp e, Fin.sum_univ_castSucc]
                    have hlast0 : cf (e (Fin.last gs.length)) = 0 := by simp [cf, e]
                    rw [hlast0, zero_mul, add_zero, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                    refine Finset.sum_congr rfl fun k _ => ?_
                    simp only [cf, e, finCongr_apply, Fin.val_cast, Fin.val_castSucc, Fin.eta, k.isLt, ↓reduceDIte]
                    ring
                  rw [hsum]; ring
    obtain ⟨Mlast, hMlast_rk, hlast0, hlast1⟩ := hlast_build
    let M : Fin (gs ++ [g]).length → Matrix (Fin n) (Fin m) F2 := fun k =>
      if hk : k.val < gs.length then Mprev ⟨k.val, hk⟩ else Mlast
    refine ⟨M, ?_, ?_⟩
    · intro k; dsimp only [M]; split_ifs with hk
      · exact hMrk ⟨k.val, hk⟩
      · exact hMlast_rk
    · intro w hw
      have hlen : (gs ++ [g]).length = gs.length + 1 := by simp
      by_cases hlt : w < n + m + gs.length
      · have hd_old : (depthsOf (n + m) (gs ++ [g])).getD w 0 = ds.getD w 0 := by
          rw [hds_new, depthStep]
          exact getD_append_left ds _ w 0 (by omega)
        have hw_old : ∀ x y, (wiresOf (gs ++ [g]) (oneEach x y)).getD w false =
            (wiresOf gs (oneEach x y)).getD w false := fun x y => by
          rw [hws_new, wireStep]
          exact getD_append_left _ _ w false (by rw [hws_len]; omega)
        constructor
        · intro hd0
          rw [hd_old] at hd0
          obtain ⟨α, β, c, hxy⟩ := (hWprev w hlt).1 hd0
          exact ⟨α, β, c, fun x y => by rw [hw_old]; exact hxy x y⟩
        · intro hd1
          rw [hd_old] at hd1
          obtain ⟨cfprev, α, β, c, hsupp, hxy⟩ := (hWprev w hlt).2 hd1
          let cf : Fin (gs ++ [g]).length → F2 := fun k =>
            if hk : k.val < gs.length then cfprev ⟨k.val, hk⟩ else 0
          refine ⟨cf, α, β, c, ?_, ?_⟩
          · intro k hk
            by_cases hklt : k.val < gs.length
            · simp only [cf, dif_pos hklt] at hk
              have hget : (gs ++ [g]).get k = gs.get ⟨k.val, hklt⟩ := by
                simp [List.getElem_append_left hklt]
              rw [hget]
              exact hsupp ⟨k.val, hklt⟩ hk
            · simp only [cf, dif_neg hklt] at hk; exact absurd rfl hk
          · intro x y
            rw [hw_old, hxy x y]
            have hsum : (∑ k : Fin (gs ++ [g]).length, cf k * M k x y) =
                ∑ k : Fin gs.length, cfprev k * Mprev k x y := by
              let e : Fin (gs.length + 1) ≃ Fin (gs ++ [g]).length := finCongr hlen.symm
              rw [← Equiv.sum_comp e, Fin.sum_univ_castSucc]
              have hlast0 : cf (e (Fin.last gs.length)) = 0 := by simp [cf, e]
              rw [hlast0, zero_mul, add_zero]
              refine Finset.sum_congr rfl fun k _ => ?_
              simp only [cf, M, e, finCongr_apply, Fin.val_cast, Fin.val_castSucc, Fin.eta, k.isLt, ↓reduceDIte]
            rw [hsum]
      · have hweq : w = n + m + gs.length := by omega
        subst hweq
        exact ⟨hlast0, fun hd1 => by
          obtain ⟨cf, α, β, c, hsupp, hxy⟩ := hlast1 hd1
          refine ⟨cf, α, β, c, hsupp, fun x y => ?_⟩
          have hsum_eq : (∑ k : Fin (gs ++ [g]).length,
              cf k * (if hk : k.val < gs.length then Mprev ⟨k.val, hk⟩ x y else Mlast x y)) =
              ∑ k : Fin (gs ++ [g]).length, cf k * M k x y :=
            Finset.sum_congr rfl fun k _ => by dsimp only [M]; split_ifs <;> rfl
          rw [hxy x y, hsum_eq]⟩

lemma dd_rank_le {n m : ℕ} (M : Matrix (Fin n) (Fin m) F2) (u : Fin n) (v : Fin m) :
    (Matrix.of fun x y => M x y + M x v + M u y + M u v).rank ≤ M.rank := by
  let L : (Fin m → F2) →ₗ[F2] (Fin n → F2) :=
    { toFun := fun w x => M.mulVec w x + M.mulVec w u
      map_add' := fun w1 w2 => by
        ext x; simp only [Matrix.mulVec_add, Pi.add_apply]; ring
      map_smul' := fun r w => by
        ext x; simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  let P : (Fin n → F2) →ₗ[F2] (Fin n → F2) :=
    { toFun := fun z x => z x + z u
      map_add' := fun z1 z2 => by ext x; simp; ring
      map_smul' := fun r z => by ext x; simp; ring }
  let D : Matrix (Fin n) (Fin m) F2 := Matrix.of fun x y => M x y + M x v + M u y + M u v
  have hsub : LinearMap.range D.mulVecLin ≤ (LinearMap.range M.mulVecLin).map P := by
    rintro _ ⟨w, rfl⟩
    let w' : Fin m → F2 := fun y => w y + (if y = v then ∑ z : Fin m, w z else 0)
    refine ⟨M.mulVecLin w', ⟨w', rfl⟩, ?_⟩
    ext x
    simp only [P, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply, Matrix.mulVec,
      dotProduct, Matrix.of_apply, D, w']
    have hmul : ∀ a : Fin n, ∑ y : Fin m, M a y * (w y + if y = v then ∑ z, w z else 0) =
        (∑ y, M a y * w y) + M a v * ∑ z, w z := by
      intro a
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
    rw [hmul x, hmul u]
    simp_rw [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have h1 := Submodule.finrank_mono hsub
  have hmap_eq : (LinearMap.range M.mulVecLin).map P =
      LinearMap.range (P.comp (LinearMap.range M.mulVecLin).subtype) := by
    ext z; simp [Submodule.mem_map]
  have h2 : Module.finrank F2 ((LinearMap.range M.mulVecLin).map P) ≤
      Module.finrank F2 (LinearMap.range M.mulVecLin) := by
    rw [hmap_eq]
    have hrk := LinearMap.finrank_range_add_finrank_ker (P.comp (LinearMap.range M.mulVecLin).subtype)
    omega
  exact le_trans h1 h2

lemma countP_eq_card_filter {α : Type} (l : List α) (p : α → Bool) :
    l.countP p = (Finset.univ.filter (fun k : Fin l.length => p (l.get k) = true)).card := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, ih]
    have hcard : (Finset.univ.filter (fun k : Fin (a :: t).length => p ((a :: t).get k) = true)).card =
        (if p a = true then 1 else 0) +
        (Finset.univ.filter (fun k : Fin t.length => p (t.get k) = true)).card := by
      simp only [Finset.card_filter, List.length_cons, Fin.sum_univ_succ]
      cases hpa : p a <;> simp [hpa]
    rw [hcard]
    cases p a <;> simp <;> omega

lemma lower_bound (n m : ℕ) (G : Fin 2 → Fin n → Fin m → Bool) (u : Fin n) (v : Fin m)
    (X Y : Matrix (Fin n) (Fin m) F2)
    (hX : ∀ x y, X x y = b2f (G 0 x y) + b2f (G 0 x v) + b2f (G 0 u y) + b2f (G 0 u v))
    (hY : ∀ x y, Y x y = b2f (G 1 x y) + b2f (G 1 x v) + b2f (G 1 u y) + b2f (G 1 u v))
    (hdisjCols : (Matrix.fromCols X Y).rank = X.rank + Y.rank)
    (t : ℕ)
    (C : Circuit) (tap : Fin 2 → ℕ)
    (hrb : ReadsBack (n + m) C)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hcnt : C.gates.countP nlGate ≤ t)
    (htap : ∀ j : Fin 2, (depthsOf (n + m) C.gates).getD (tap j) 0 ≤ 1 ∧ Represents (G j) ⟨C.gates, tap j⟩) :
    let r := X.rank
    let s := Y.rank
    let save := if r % 2 = 1 ∧ s % 2 = 1 ∧ (Matrix.fromRows X Y).rank + 2 ≤ r + s then 1 else 0
    (r + 1) / 2 + (s + 1) / 2 - save ≤ t := by
  intro r s save
  obtain ⟨M, hMrk, hW⟩ := circuit_depth1_decomp n m C.gates hrb hfan
  have htap_rep : ∀ j : Fin 2, ∃ (cf : Fin C.gates.length → F2) (α : Fin n → F2) (β : Fin m → F2) (c : F2),
      (∀ k, cf k ≠ 0 → nlGate (C.gates.get k) = true) ∧
      ∀ x y, b2f (G j x y) = (∑ k : Fin C.gates.length, cf k * M k x y) + α x + β y + c := by
    intro j
    have hrep : ∀ x y, (wiresOf C.gates (oneEach x y)).getD (tap j) false = G j x y :=
      fun x y => (htap j).2 x y
    by_cases hlt : tap j < n + m + C.gates.length
    · obtain ⟨cf, α, β, c, hsupp, hxy⟩ := (hW (tap j) hlt).2 (htap j).1
      exact ⟨cf, α, β, c, hsupp, fun x y => by rw [← hrep x y]; exact hxy x y⟩
    · refine ⟨0, 0, 0, 0, fun k hk => absurd rfl hk, fun x y => ?_⟩
      rw [← hrep x y]
      have hge : (wiresOf C.gates (oneEach x y)).length ≤ tap j := by
        simp [wiresOf_length, oneEach]; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, b2f]
  obtain ⟨cf0, α0, β0, c0, hsupp0, hG0⟩ := htap_rep 0
  obtain ⟨cf1, α1, β1, c1, hsupp1, hG1⟩ := htap_rep 1
  let D : Fin C.gates.length → Matrix (Fin n) (Fin m) F2 := fun k =>
    Matrix.of fun x y => M k x y + M k x v + M k u y + M k u v
  have hDrk : ∀ k, (D k).rank ≤ 2 := fun k => le_trans (dd_rank_le (M k) u v) (hMrk k)
  have hXsum : X = ∑ k : Fin C.gates.length, cf0 k • D k := by
    ext x y
    rw [hX x y, hG0 x y, hG0 x v, hG0 u y, hG0 u v]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, D]
    simp_rw [mul_add, Finset.sum_add_distrib]
    have h1 := f2_add_self (α0 x)
    have h2 := f2_add_self (α0 u)
    have h3 := f2_add_self (β0 y)
    have h4 := f2_add_self (β0 v)
    have h5 := f2_add_self c0
    linear_combination h1 + h2 + h3 + h4 + h5 + h5
  have hYsum : Y = ∑ k : Fin C.gates.length, cf1 k • D k := by
    ext x y
    rw [hY x y, hG1 x y, hG1 x v, hG1 u y, hG1 u v]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, D]
    simp_rw [mul_add, Finset.sum_add_distrib]
    have h1 := f2_add_self (α1 x)
    have h2 := f2_add_self (α1 u)
    have h3 := f2_add_self (β1 y)
    have h4 := f2_add_self (β1 v)
    have h5 := f2_add_self c1
    linear_combination h1 + h2 + h3 + h4 + h5 + h5
  let Aset : Finset (Fin C.gates.length) := Finset.univ.filter (fun k => cf0 k = 1 ∧ cf1 k = 0)
  let Bset : Finset (Fin C.gates.length) := Finset.univ.filter (fun k => cf0 k = 0 ∧ cf1 k = 1)
  let Cset : Finset (Fin C.gates.length) := Finset.univ.filter (fun k => cf0 k = 1 ∧ cf1 k = 1)
  let NLset : Finset (Fin C.gates.length) := Finset.univ.filter (fun k => nlGate (C.gates.get k) = true)
  have hdisjAB : Disjoint Aset Bset := by
    rw [Finset.disjoint_left]; intro k hkA hkB
    simp only [Aset, Bset, Finset.mem_filter, Finset.mem_univ, true_and] at hkA hkB
    exact absurd (hkA.1.symm.trans hkB.1) (by decide)
  have hdisjAC : Disjoint Aset Cset := by
    rw [Finset.disjoint_left]; intro k hkA hkC
    simp only [Aset, Cset, Finset.mem_filter, Finset.mem_univ, true_and] at hkA hkC
    exact absurd (hkA.2.symm.trans hkC.2) (by decide)
  have hdisjBC : Disjoint Bset Cset := by
    rw [Finset.disjoint_left]; intro k hkB hkC
    simp only [Bset, Cset, Finset.mem_filter, Finset.mem_univ, true_and] at hkB hkC
    exact absurd (hkB.1.symm.trans hkC.1) (by decide)
  have hsubNL : Aset ∪ Bset ∪ Cset ⊆ NLset := by
    intro k hk
    simp only [Finset.mem_union, Aset, Bset, Cset, NLset, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rcases hk with (⟨h1, _⟩ | ⟨_, h2⟩) | ⟨h1, _⟩
    · exact hsupp0 k (by rw [h1]; decide)
    · exact hsupp1 k (by rw [h2]; decide)
    · exact hsupp0 k (by rw [h1]; decide)
  have habc_le : Aset.card + Bset.card + Cset.card ≤ t := by
    have hcard : (Aset ∪ Bset ∪ Cset).card = Aset.card + Bset.card + Cset.card := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdisjAC, hdisjBC⟩),
        Finset.card_union_of_disjoint hdisjAB]
    have h1 := Finset.card_le_card hsubNL
    rw [hcard] at h1
    have h2 : NLset.card = C.gates.countP nlGate := (countP_eq_card_filter C.gates nlGate).symm
    omega
  let Xp := ∑ k ∈ Aset, D k
  let Yp := ∑ k ∈ Bset, D k
  let Z := ∑ k ∈ Cset, D k
  have hX_eq : X = Xp + Z := by
    rw [hXsum]
    have hsplit : ∑ k : Fin C.gates.length, cf0 k • D k = ∑ k ∈ Aset ∪ Cset, D k := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => cf0 k = 1)]
      have h0 : ∑ k ∈ Finset.univ.filter (fun k => ¬ cf0 k = 1), cf0 k • D k = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hne : cf0 k ≠ 1 := (Finset.mem_filter.mp hk).2
        rcases f2_cases (cf0 k) with h0 | h1
        · simp [h0]
        · exact absurd h1 hne
      rw [h0, add_zero]
      have hset : Finset.univ.filter (fun k : Fin C.gates.length => cf0 k = 1) = Aset ∪ Cset := by
        ext k
        simp only [Finset.mem_union, Aset, Cset, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases f2_cases (cf1 k) with h1 | h1 <;> simp [h1]
      rw [hset]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_union, Aset, Cset, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rcases hk with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [h1]
    rw [hsplit, Finset.sum_union hdisjAC]
  have hY_eq : Y = Yp + Z := by
    rw [hYsum]
    have hsplit : ∑ k : Fin C.gates.length, cf1 k • D k = ∑ k ∈ Bset ∪ Cset, D k := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => cf1 k = 1)]
      have h0 : ∑ k ∈ Finset.univ.filter (fun k => ¬ cf1 k = 1), cf1 k • D k = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hne : cf1 k ≠ 1 := (Finset.mem_filter.mp hk).2
        rcases f2_cases (cf1 k) with h0 | h1
        · simp [h0]
        · exact absurd h1 hne
      rw [h0, add_zero]
      have hset : Finset.univ.filter (fun k : Fin C.gates.length => cf1 k = 1) = Bset ∪ Cset := by
        ext k
        simp only [Finset.mem_union, Bset, Cset, Finset.mem_filter, Finset.mem_univ, true_and]
        rcases f2_cases (cf0 k) with h0 | h0 <;> simp [h0]
      rw [hset]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_union, Bset, Cset, Finset.mem_filter, Finset.mem_univ, true_and] at hk
      rcases hk with ⟨_, h1⟩ | ⟨_, h1⟩ <;> simp [h1]
    rw [hsplit, Finset.sum_union hdisjBC]
  have hXY_eq : X + Y = Xp + Yp := by
    rw [hX_eq, hY_eq]
    ext x y
    simp only [Matrix.add_apply]
    have hz := f2_add_self (Z x y)
    linear_combination hz
  have hXp_rk : Xp.rank ≤ 2 * Aset.card := by
    calc Xp.rank ≤ ∑ k ∈ Aset, (D k).rank := rank_sum_le Aset D
      _ ≤ ∑ _k ∈ Aset, 2 := Finset.sum_le_sum fun k _ => hDrk k
      _ = 2 * Aset.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hYp_rk : Yp.rank ≤ 2 * Bset.card := by
    calc Yp.rank ≤ ∑ k ∈ Bset, (D k).rank := rank_sum_le Bset D
      _ ≤ ∑ _k ∈ Bset, 2 := Finset.sum_le_sum fun k _ => hDrk k
      _ = 2 * Bset.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hZ_rk : Z.rank ≤ 2 * Cset.card := by
    calc Z.rank ≤ ∑ k ∈ Cset, (D k).rank := rank_sum_le Cset D
      _ ≤ ∑ _k ∈ Cset, 2 := Finset.sum_le_sum fun k _ => hDrk k
      _ = 2 * Cset.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hI1 : r ≤ 2 * Aset.card + 2 * Cset.card := by
    have h1 : r ≤ Xp.rank + Z.rank := by dsimp only [r]; rw [hX_eq]; exact rank_add_le Xp Z
    omega
  have hI2 : s ≤ 2 * Bset.card + 2 * Cset.card := by
    have h1 : s ≤ Yp.rank + Z.rank := by dsimp only [s]; rw [hY_eq]; exact rank_add_le Yp Z
    omega
  have hI3 : r + s ≤ 2 * Aset.card + 2 * Bset.card + 2 * Cset.card := by
    have h1 : (Matrix.fromCols X Y).rank ≤ Xp.rank + Yp.rank + Z.rank := by
      rw [hX_eq, hY_eq]; exact rank_fromCols_split_le Xp Yp Z
    omega
  have hdisj := rank_fromCols_eq_add_imp_disjoint X Y hdisjCols
  have hI4 : (Matrix.fromRows X Y).rank ≤ 2 * Aset.card + 2 * Bset.card := by
    rw [rank_fromRows_eq_rank_add X Y hdisj, hXY_eq]
    have h1 := rank_add_le Xp Yp
    omega
  dsimp only [save]
  split_ifs with hsave
  · omega
  · by_cases hC0 : Cset.card = 0
    · omega
    · omega

-- Section 3: Upper bound circuit builder (XOR trees + depth-1 AND products)

def isLinearOK (gs : List Gate) (width : ℕ) : Prop :=
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < width + j) ∧
  (∀ g ∈ gs, g.inputs.length ≤ 2)

lemma isLinearOK_append {width : ℕ} {gs1 gs2 : List Gate}
    (h1 : isLinearOK gs1 width) (h2 : isLinearOK gs2 (width + gs1.length)) :
    isLinearOK (gs1 ++ gs2) width := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    by_cases hlt : j < gs1.length
    · rw [getD_append_left gs1 gs2 j _ hlt] at hi
      exact h1.1 j hlt i hi
    · have hge : gs1.length ≤ j := Nat.le_of_not_lt hlt
      have hgd : (gs1 ++ gs2).getD j ⟨GateOp.or, []⟩ = gs2.getD (j - gs1.length) ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge]
      rw [hgd] at hi
      have hj2 : j - gs1.length < gs2.length := by simp at hj; omega
      have hlt2 := h2.1 (j - gs1.length) hj2 i hi
      omega
  · intro g hg
    simp only [List.mem_append] at hg
    rcases hg with hg1 | hg2
    · exact h1.2 g hg1
    · exact h2.2 g hg2

-- Append a single XOR of two earlier wires `a, b < base` (2 linear gates: mod 2 then not)
def xor2Gates (base a b : ℕ) : List Gate :=
  [⟨GateOp.mod 2, [a, b]⟩, ⟨GateOp.not, [base]⟩]

lemma xor2Gates_ok (base a b : ℕ) (ha : a < base) (hb : b < base) :
    isLinearOK (xor2Gates base a b) base := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    simp only [xor2Gates, List.length_cons, List.length_nil] at hj
    interval_cases j
    · simp only [xor2Gates, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · simp only [xor2Gates, List.getD_cons_succ, List.getD_cons_zero, List.mem_singleton] at hi
      omega
  · intro g hg
    simp only [xor2Gates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp

lemma isLinearOK_eq {gs : List Gate} {w₁ w₂ : ℕ} (h : isLinearOK gs w₁) (heq : w₁ = w₂) :
    isLinearOK gs w₂ := heq ▸ h

lemma nlGate_mod2 (a b : ℕ) : nlGate ⟨GateOp.mod 2, [a, b]⟩ = false := by
  simp only [nlGate, List.length_cons, List.length_nil]
  decide

lemma nlGate_not (a : ℕ) : nlGate ⟨GateOp.not, [a]⟩ = false := by
  simp only [nlGate, List.length_cons, List.length_nil]
  decide

lemma nlGate_and2 (a b : ℕ) : nlGate ⟨GateOp.and, [a, b]⟩ = true := by
  simp only [nlGate, List.length_cons, List.length_nil]
  decide

lemma xor2Gates_nl (base a b : ℕ) : (xor2Gates base a b).countP nlGate = 0 := by
  simp [xor2Gates, nlGate_mod2, nlGate_not]

lemma xor2Gates_val (ws : List Bool) (a b : ℕ) :
    b2f (((xor2Gates ws.length a b).foldl wireStep ws).getD (ws.length + 1) false) =
      b2f (ws.getD a false) + b2f (ws.getD b false) := by
  simp only [xor2Gates, List.foldl_cons, List.foldl_nil, wireStep, List.map_cons, List.map_nil]
  let v := (GateOp.mod 2).eval [ws.getD a false, ws.getD b false]
  have hl1 : (ws ++ [v]).length = ws.length + 1 := by simp
  have hget1 : (ws ++ [v]).getD ws.length false = v := getD_append_self ws v false
  have hget2 : ((ws ++ [v]) ++ [GateOp.not.eval [(ws ++ [v]).getD ws.length false]]).getD
      (ws.length + 1) false =
      GateOp.not.eval [(ws ++ [v]).getD ws.length false] := by
    rw [← hl1]; exact getD_append_self (ws ++ [v]) _ false
  rw [hget2, hget1]
  dsimp only [v]
  cases ws.getD a false <;> cases ws.getD b false <;> decide

lemma xor2Gates_depth (ds : List ℕ) (a b : ℕ) (d : ℕ)
    (hda : ds.getD a 0 ≤ d) (hdb : ds.getD b 0 ≤ d) :
    ((xor2Gates ds.length a b).foldl depthStep ds).getD (ds.length + 1) 0 ≤ d := by
  simp only [xor2Gates, List.foldl_cons, List.foldl_nil, depthStep, List.map_cons, List.map_nil,
    List.foldr_cons, List.foldr_nil, nlGate_mod2, nlGate_not, Bool.toNat_false, add_zero, nat_max_zero]
  have hl1 : (ds ++ [max (ds.getD a 0) (ds.getD b 0)]).length = ds.length + 1 := by simp
  have hg1 : (ds ++ [max (ds.getD a 0) (ds.getD b 0)]).getD ds.length 0 =
      max (ds.getD a 0) (ds.getD b 0) := getD_append_self ds _ 0
  have hg2 : ((ds ++ [max (ds.getD a 0) (ds.getD b 0)]) ++
      [(ds ++ [max (ds.getD a 0) (ds.getD b 0)]).getD ds.length 0]).getD (ds.length + 1) 0 =
      (ds ++ [max (ds.getD a 0) (ds.getD b 0)]).getD ds.length 0 := by
    rw [← hl1]; exact getD_append_self _ _ 0
  rw [hg2, hg1]
  exact max_le hda hdb

-- XOR a list of existing wires `idxs` (all < base) starting from base; returns (gates, outputWire)
def xorListBuild (base : ℕ) (l : List ℕ) : List Gate × ℕ :=
  match l with
  | [] => ([⟨GateOp.or, []⟩], base)
  | [a] => ([], a)
  | a :: b :: rest =>
    let g1 := xor2Gates base a b
    let mid := base + 1
    let res := xorListBuild (base + 2) (mid :: rest)
    (g1 ++ res.1, res.2)
termination_by l.length

lemma xorListBuild_spec_aux : ∀ (k : ℕ) (idxs : List ℕ), idxs.length = k →
    ∀ base : ℕ, (∀ w ∈ idxs, w < base) →
      let p := xorListBuild base idxs
      isLinearOK p.1 base ∧
      p.1.countP nlGate = 0 ∧
      p.2 < base + p.1.length ∧
      (∀ (ws : List Bool), ws.length = base →
        b2f ((p.1.foldl wireStep ws).getD p.2 false) =
          (idxs.map (fun w => b2f (ws.getD w false))).sum) ∧
      (∀ (ds : List ℕ) (d : ℕ), ds.length = base → (∀ w ∈ idxs, ds.getD w 0 ≤ d) →
        (p.1.foldl depthStep ds).getD p.2 0 ≤ d) := by
  intro k
  induction k with
  | zero =>
    intro idxs hk base _
    have hnil : idxs = [] := List.eq_nil_of_length_eq_zero hk
    subst hnil
    simp only [xorListBuild, List.length_singleton, List.map_nil, List.sum_nil]
    have hnl0 : nlGate ⟨GateOp.or, []⟩ = false := by decide
    refine ⟨⟨?_, ?_⟩, by simp [hnl0], by omega, ?_, ?_⟩
    · intro j hj i hi
      simp only [List.length_singleton] at hj
      have hj0 : j = 0 := by omega
      subst hj0; simp at hi
    · intro g hg; simp at hg; subst hg; simp
    · intro ws hlen
      simp only [List.foldl_cons, List.foldl_nil, wireStep, List.map_nil]
      rw [← hlen, getD_append_self]; decide
    · intro ds d hlen _
      simp only [List.foldl_cons, List.foldl_nil, depthStep, hnl0, List.map_nil, List.foldr_nil,
        Bool.toNat_false, add_zero]
      rw [← hlen, getD_append_self]; omega
  | succ k ih =>
    intro idxs hk base hlt
    cases idxs with
    | nil => simp at hk
    | cons a rest =>
      cases rest with
      | nil =>
        have ha : a < base := hlt a (by simp)
        simp only [xorListBuild, List.length_nil, add_zero, List.countP_nil, List.foldl_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        refine ⟨⟨fun j hj => absurd hj (Nat.not_lt_zero _), fun _ h => by simp at h⟩,
          trivial, ha, fun _ _ => trivial, fun ds d _ hd => hd a (by simp)⟩
      | cons b rest2 =>
        have ha : a < base := hlt a (by simp)
        have hb : b < base := hlt b (by simp)
        have hlen2 : ((base + 1) :: rest2).length = k := by simp at hk; simp; omega
        have hrest : ∀ w ∈ (base + 1) :: rest2, w < base + 2 := by
          intro w hw
          simp only [List.mem_cons] at hw
          rcases hw with rfl | hw2
          · omega
          · have := hlt w (by simp [hw2]); omega
        obtain ⟨hok2, hnl2, hlt2, hval2, hdep2⟩ := ih ((base + 1) :: rest2) hlen2 (base + 2) hrest
        simp only [xorListBuild]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · have hok1 := xor2Gates_ok base a b ha hb
          have hl : (xor2Gates base a b).length = 2 := rfl
          exact isLinearOK_append hok1 (by simpa [hl] using hok2)
        · rw [List.countP_append, xor2Gates_nl, hnl2]
        · simp only [List.length_append]
          have hl : (xor2Gates base a b).length = 2 := rfl
          omega
        · intro ws hlen
          rw [List.foldl_append]
          let ws1 := (xor2Gates base a b).foldl wireStep ws
          have hlen1 : ws1.length = base + 2 := by
            dsimp only [ws1]; rw [foldl_wireStep_length, hlen]; rfl
          rw [hval2 ws1 hlen1]
          simp only [List.map_cons, List.sum_cons]
          have hmid : b2f (ws1.getD (base + 1) false) = b2f (ws.getD a false) + b2f (ws.getD b false) := by
            dsimp only [ws1]; rw [← hlen]; exact xor2Gates_val ws a b
          have htail : rest2.map (fun w => b2f (ws1.getD w false)) =
              rest2.map (fun w => b2f (ws.getD w false)) := by
            refine List.map_congr_left fun w hw => ?_
            have hwlt : w < ws.length := by
              have := hlt w (by simp [hw]); omega
            rw [foldl_wireStep_getD_old ws (xor2Gates base a b) w hwlt]
          rw [hmid, htail, add_assoc]
        · intro ds d hlen hd
          rw [List.foldl_append]
          let ds1 := (xor2Gates base a b).foldl depthStep ds
          have hlen1 : ds1.length = base + 2 := by
            dsimp only [ds1]; rw [foldl_depthStep_length, hlen]; rfl
          refine hdep2 ds1 d hlen1 ?_
          intro w hw
          simp only [List.mem_cons] at hw
          rcases hw with rfl | hw2
          · dsimp only [ds1]; rw [← hlen]
            exact xor2Gates_depth ds a b d (hd a (by simp)) (hd b (by simp))
          · have hwlt : w < ds.length := by
              have := hlt w (by simp [hw2]); omega
            rw [foldl_depthStep_getD_old ds (xor2Gates base a b) w hwlt]
            exact hd w (by simp [hw2])

lemma xorListBuild_spec (idxs : List ℕ) (base : ℕ) (hlt : ∀ w ∈ idxs, w < base) :
    let p := xorListBuild base idxs
    isLinearOK p.1 base ∧
    p.1.countP nlGate = 0 ∧
    p.2 < base + p.1.length ∧
    (∀ (ws : List Bool), ws.length = base →
      b2f ((p.1.foldl wireStep ws).getD p.2 false) =
        (idxs.map (fun w => b2f (ws.getD w false))).sum) ∧
    (∀ (ds : List ℕ) (d : ℕ), ds.length = base → (∀ w ∈ idxs, ds.getD w 0 ≤ d) →
      (p.1.foldl depthStep ds).getD p.2 0 ≤ d) :=
  xorListBuild_spec_aux idxs.length idxs rfl base hlt

lemma sum_filter_nodup_fin {n : ℕ} (l : List (Fin n)) (hl : l.Nodup)
    (p : Fin n → Bool) (x : Fin n) :
    ((l.filter p).map (fun i => b2f (decide (x.val = i.val)))).sum =
      if x ∈ l ∧ p x = true then 1 else 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    by_cases hax : x = a
    · subst hax
      have hxt : x ∉ t := hl.1
      have iht := ih hl.2
      simp only [hxt, false_and, ↓reduceIte] at iht
      cases hpa : p x with
      | false =>
        simp [hpa, iht]
      | true =>
        have hxx : b2f (decide True) = 1 := rfl
        simp only [List.filter_cons, hpa, ↓reduceIte, List.map_cons, List.sum_cons, eq_self_iff_true, hxx, iht, add_zero, List.mem_cons, true_or, and_self]
    · have hvne : x.val ≠ a.val := fun h => hax (Fin.ext h)
      have iht := ih hl.2
      cases hpa : p a with
      | false =>
        simp [hpa, iht, hax]
      | true =>
        have hxa : b2f (decide (x.val = a.val)) = 0 := by simp [b2f, hvne]
        simp only [List.filter_cons, hpa, ↓reduceIte, List.map_cons, List.sum_cons, hxa, zero_add,
          iht, List.mem_cons, hax, false_or]

lemma sum_finRange_filter {n : ℕ} (α : Fin n → F2) (x : Fin n) :
    (((List.finRange n).filter (fun i => decide (α i = 1))).map
      (fun i => b2f (decide (x.val = i.val)))).sum = α x := by
  rw [sum_filter_nodup_fin (List.finRange n) (List.nodup_finRange n) _ x]
  have hmem : x ∈ List.finRange n := List.mem_finRange x
  rcases f2_cases (α x) with h0 | h1
  · simp [hmem, h0]
  · simp [hmem, h1]

def affineIdxs (n m base : ℕ) (α : Fin n → F2) (β : Fin m → F2) (c : F2) : List ℕ :=
  ((List.finRange n).filter (fun i => decide (α i = 1))).map Fin.val ++
  ((List.finRange m).filter (fun j => decide (β j = 1))).map (fun j => n + j.val) ++
  (if c = 1 then [base] else [])

def affineBuild (n m base : ℕ) (α : Fin n → F2) (β : Fin m → F2) (c : F2) : List Gate × ℕ :=
  let g0 : List Gate := [⟨GateOp.and, []⟩]
  let res := xorListBuild (base + 1) (affineIdxs n m base α β c)
  (g0 ++ res.1, res.2)

lemma affineBuild_spec (n m base : ℕ) (hbase : n + m ≤ base)
    (α : Fin n → F2) (β : Fin m → F2) (c : F2) :
    let p := affineBuild n m base α β c
    isLinearOK p.1 base ∧
    p.1.countP nlGate = 0 ∧
    p.2 < base + p.1.length ∧
    (∀ (x : Fin n) (y : Fin m) (ws : List Bool),
      ws.length = base →
      (∀ w < n + m, ws.getD w false = (oneEach x y).getD w false) →
      b2f ((p.1.foldl wireStep ws).getD p.2 false) = α x + β y + c) ∧
    (∀ (ds : List ℕ),
      ds.length = base →
      (∀ w < n + m, ds.getD w 0 = 0) →
      (p.1.foldl depthStep ds).getD p.2 0 = 0) := by
  have hidxs_lt : ∀ w ∈ affineIdxs n m base α β c, w < base + 1 := by
    intro w hw
    simp only [affineIdxs, List.mem_append, List.mem_map, List.mem_filter] at hw
    rcases hw with (⟨i, _, rfl⟩ | ⟨j, _, rfl⟩) | hc
    · omega
    · omega
    · split_ifs at hc with h1
      · simp at hc; omega
      · simp at hc
  obtain ⟨hok2, hnl2, hlt2, hval2, hdep2⟩ := xorListBuild_spec (affineIdxs n m base α β c) (base + 1) hidxs_lt
  have hok0 : isLinearOK [⟨GateOp.and, []⟩] base := by
    refine ⟨?_, ?_⟩
    · intro j hj i hi
      simp only [List.length_singleton] at hj
      have hj0 : j = 0 := by omega
      subst hj0; simp at hi
    · intro g hg; simp at hg; subst hg; simp
  have hnl0 : ([⟨GateOp.and, []⟩] : List Gate).countP nlGate = 0 := by
    have h : nlGate ⟨GateOp.and, []⟩ = false := by decide
    simp [h]
  simp only [affineBuild]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact isLinearOK_append hok0 (by simpa using hok2)
  · rw [List.countP_append, hnl0, hnl2]
  · simp only [List.length_append, List.length_singleton]; omega
  · intro x y ws hlen hws
    rw [List.foldl_append]
    let ws1 := ([⟨GateOp.and, []⟩] : List Gate).foldl wireStep ws
    have hlen1 : ws1.length = base + 1 := by simp [ws1, wireStep, hlen]
    rw [hval2 ws1 hlen1]
    have hget_old : ∀ w < n + m, ws1.getD w false = (oneEach x y).getD w false := by
      intro w hw
      have h1 := foldl_wireStep_getD_old ws [⟨GateOp.and, []⟩] w (by omega)
      exact h1.trans (hws w hw)
    have hget_base : b2f (ws1.getD base false) = 1 := by
      dsimp only [ws1]
      simp only [List.foldl_cons, List.foldl_nil, wireStep, List.map_nil]
      rw [← hlen, getD_append_self]
      decide
    simp only [affineIdxs, List.map_append, List.sum_append, List.map_map]
    have hsum1 : (((List.finRange n).filter (fun i => decide (α i = 1))).map
        ((fun w => b2f (ws1.getD w false)) ∘ Fin.val)).sum = α x := by
      have hcongr : (((List.finRange n).filter (fun i => decide (α i = 1))).map
          ((fun w => b2f (ws1.getD w false)) ∘ Fin.val)) =
          (((List.finRange n).filter (fun i => decide (α i = 1))).map
          (fun i => b2f (decide (x.val = i.val)))) := by
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp_apply, hget_old i.val (by omega),
          oneEach_getD x y i.val (by omega), i.isLt, ↓reduceDIte]
      rw [hcongr]
      exact sum_finRange_filter α x
    have hsum2 : (((List.finRange m).filter (fun j => decide (β j = 1))).map
        ((fun w => b2f (ws1.getD w false)) ∘ fun j => n + j.val)).sum = β y := by
      have hcongr : (((List.finRange m).filter (fun j => decide (β j = 1))).map
          ((fun w => b2f (ws1.getD w false)) ∘ fun j => n + j.val)) =
          (((List.finRange m).filter (fun j => decide (β j = 1))).map
          (fun j => b2f (decide (y.val = j.val)))) := by
        refine List.map_congr_left fun j _ => ?_
        have hnotlt : ¬ n + j.val < n := by omega
        have hsub : n + j.val - n = j.val := by omega
        simp only [Function.comp_apply, hget_old (n + j.val) (by omega),
          oneEach_getD x y (n + j.val) (by omega), hnotlt, ↓reduceDIte, hsub]
      rw [hcongr]
      exact sum_finRange_filter β y
    have hsum3 : ((if c = 1 then [base] else []).map (fun w => b2f (ws1.getD w false))).sum = c := by
      rcases f2_cases c with rfl | rfl
      · simp
      · simp only [↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
          hget_base]
    rw [hsum1, hsum2, hsum3]
  · intro ds hlen hds
    rw [List.foldl_append]
    let ds1 := ([⟨GateOp.and, []⟩] : List Gate).foldl depthStep ds
    have hlen1 : ds1.length = base + 1 := by simp [ds1, depthStep, hlen]
    have h0 : ((xorListBuild (base + 1) (affineIdxs n m base α β c)).1.foldl depthStep ds1).getD
        (xorListBuild (base + 1) (affineIdxs n m base α β c)).2 0 ≤ 0 := by
      refine hdep2 ds1 0 hlen1 ?_
      intro w hw
      simp only [affineIdxs, List.mem_append, List.mem_map, List.mem_filter] at hw
      rcases hw with (⟨i, _, rfl⟩ | ⟨j, _, rfl⟩) | hc
      · rw [foldl_depthStep_getD_old ds _ i.val (by omega), hds i.val (by omega)]
      · rw [foldl_depthStep_getD_old ds _ (n + j.val) (by omega), hds (n + j.val) (by omega)]
      · split_ifs at hc with h1
        · simp only [List.mem_singleton] at hc
          subst hc
          dsimp only [ds1]
          have hnl_and : nlGate ⟨GateOp.and, []⟩ = false := by decide
          simp only [List.foldl_cons, List.foldl_nil, depthStep, hnl_and, List.map_nil,
            List.foldr_nil, Bool.toNat_false, add_zero]
          rw [← hlen, getD_append_self]
        · simp at hc
    exact Nat.eq_zero_of_le_zero h0

def pairGadget (n m base : ℕ) (p1 p2 : Fin n → F2) (q1 q2 : Fin m → F2) : List Gate × ℕ :=
  let a1 := affineBuild n m base p1 q2 0
  let base1 := base + a1.1.length
  let a2 := affineBuild n m base1 p2 q1 0
  let base2 := base1 + a2.1.length
  let gand : Gate := ⟨GateOp.and, [a1.2, a2.2]⟩
  (a1.1 ++ a2.1 ++ [gand], base2)

lemma pairGadget_spec (n m base : ℕ) (hbase : n + m ≤ base)
    (p1 p2 : Fin n → F2) (q1 q2 : Fin m → F2) :
    let g := pairGadget n m base p1 p2 q1 q2
    isLinearOK g.1 base ∧
    g.1.countP nlGate = 1 ∧
    g.2 < base + g.1.length ∧
    (∀ (x : Fin n) (y : Fin m) (ws : List Bool),
      ws.length = base →
      (∀ w < n + m, ws.getD w false = (oneEach x y).getD w false) →
      b2f ((g.1.foldl wireStep ws).getD g.2 false) =
        p1 x * q1 y + p2 x * q2 y + p1 x * p2 x + q1 y * q2 y) ∧
    (∀ (ds : List ℕ),
      ds.length = base →
      (∀ w < n + m, ds.getD w 0 = 0) →
      (g.1.foldl depthStep ds).getD g.2 0 ≤ 1) := by
  dsimp only [pairGadget]
  set a1 := affineBuild n m base p1 q2 0
  set base1 := base + a1.1.length with hbase1
  set a2 := affineBuild n m base1 p2 q1 0
  set base2 := base1 + a2.1.length with hbase2
  set gand : Gate := ⟨GateOp.and, [a1.2, a2.2]⟩
  obtain ⟨hok1, hnl1, hlt1, hval1, hdep1⟩ := affineBuild_spec n m base hbase p1 q2 0
  change isLinearOK a1.1 base at hok1
  change a1.1.countP nlGate = 0 at hnl1
  change a1.2 < base1 at hlt1
  obtain ⟨hok2, hnl2, hlt2, hval2, hdep2⟩ := affineBuild_spec n m base1 (by omega) p2 q1 0
  change isLinearOK a2.1 base1 at hok2
  change a2.1.countP nlGate = 0 at hnl2
  change a2.2 < base2 at hlt2
  have hok_and : isLinearOK [gand] base2 := by
    refine ⟨?_, ?_⟩
    · intro j hj i hi
      simp only [List.length_singleton] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      simp only [List.getD_cons_zero, gand, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · intro g hg; simp at hg; subst hg; simp [gand]
  have hnl_and : nlGate gand = true := nlGate_and2 a1.2 a2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h12 := isLinearOK_append hok1 hok2
    exact isLinearOK_append h12 (isLinearOK_eq hok_and (by simp [List.length_append, hbase1, hbase2]; omega))
  · simp [List.countP_append, hnl1, hnl2, hnl_and]
  · simp only [List.length_append, List.length_singleton]; omega
  · intro x y ws hlen hws
    rw [List.foldl_append, List.foldl_append]
    let ws1 := a1.1.foldl wireStep ws
    have hlen1 : ws1.length = base1 := by simp [ws1, foldl_wireStep_length, hlen, hbase1]
    have hws1 : ∀ w < n + m, ws1.getD w false = (oneEach x y).getD w false := fun w hw =>
      (foldl_wireStep_getD_old ws a1.1 w (by omega)).trans (hws w hw)
    let ws2 := a2.1.foldl wireStep ws1
    have hlen2 : ws2.length = base2 := by simp [ws2, foldl_wireStep_length, hlen1, hbase2]
    have hw1 : b2f (ws2.getD a1.2 false) = p1 x + q2 y := by
      have hold := foldl_wireStep_getD_old ws1 a2.1 a1.2 (by omega)
      rw [hold, hval1 x y ws hlen hws, add_zero]
    have hw2 : b2f (ws2.getD a2.2 false) = p2 x + q1 y := by
      rw [hval2 x y ws1 hlen1 hws1, add_zero]
    simp only [List.foldl_cons, List.foldl_nil, wireStep, gand, List.map_cons, List.map_nil]
    change b2f ((ws2 ++ [GateOp.and.eval [ws2.getD a1.2 false, ws2.getD a2.2 false]]).getD base2 false) = _
    rw [← hlen2, getD_append_self]
    have hand : b2f (GateOp.and.eval [ws2.getD a1.2 false, ws2.getD a2.2 false]) =
        b2f (ws2.getD a1.2 false) * b2f (ws2.getD a2.2 false) := by
      cases ws2.getD a1.2 false <;> cases ws2.getD a2.2 false <;> decide
    rw [hand, hw1, hw2]
    ring
  · intro ds hlen hds
    rw [List.foldl_append, List.foldl_append]
    let ds1 := a1.1.foldl depthStep ds
    have hlen1 : ds1.length = base1 := by simp [ds1, foldl_depthStep_length, hlen, hbase1]
    have hds1 : ∀ w < n + m, ds1.getD w 0 = 0 := fun w hw =>
      (foldl_depthStep_getD_old ds a1.1 w (by omega)).trans (hds w hw)
    let ds2 := a2.1.foldl depthStep ds1
    have hlen2 : ds2.length = base2 := by simp [ds2, foldl_depthStep_length, hlen1, hbase2]
    have hd1 : ds2.getD a1.2 0 = 0 := by
      rw [foldl_depthStep_getD_old ds1 a2.1 a1.2 (by omega), hdep1 ds hlen hds]
    have hd2 : ds2.getD a2.2 0 = 0 := hdep2 ds1 hlen1 hds1
    simp only [List.foldl_cons, List.foldl_nil, depthStep, gand, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, hnl_and, Bool.toNat_true, nat_max_zero]
    change (ds2 ++ [max (ds2.getD a1.2 0) (ds2.getD a2.2 0) + 1]).getD base2 0 ≤ 1
    rw [← hlen2, getD_append_self, hd1, hd2]
    omega

def pairListBuild (n m : ℕ) :
    ℕ → List ((Fin n → F2) × (Fin n → F2) × (Fin m → F2) × (Fin m → F2)) → List Gate × List ℕ
  | _, [] => ([], [])
  | base, (p1, p2, q1, q2) :: rest =>
    let g1 := pairGadget n m base p1 p2 q1 q2
    let r := pairListBuild n m (base + g1.1.length) rest
    (g1.1 ++ r.1, g1.2 :: r.2)

lemma pairListBuild_spec (n m : ℕ)
    (pairs : List ((Fin n → F2) × (Fin n → F2) × (Fin m → F2) × (Fin m → F2))) :
    ∀ base : ℕ, n + m ≤ base →
      let res := pairListBuild n m base pairs
      isLinearOK res.1 base ∧
      res.1.countP nlGate = pairs.length ∧
      (∀ w ∈ res.2, w < base + res.1.length) ∧
      (∀ (x : Fin n) (y : Fin m) (ws : List Bool),
        ws.length = base →
        (∀ w < n + m, ws.getD w false = (oneEach x y).getD w false) →
        (res.2.map (fun w => b2f ((res.1.foldl wireStep ws).getD w false))).sum =
          (pairs.map (fun t => t.1 x * t.2.2.1 y + t.2.1 x * t.2.2.2 y)).sum +
          (pairs.map (fun t => t.1 x * t.2.1 x)).sum +
          (pairs.map (fun t => t.2.2.1 y * t.2.2.2 y)).sum) ∧
      (∀ (ds : List ℕ),
        ds.length = base →
        (∀ w < n + m, ds.getD w 0 = 0) →
        ∀ w ∈ res.2, (res.1.foldl depthStep ds).getD w 0 ≤ 1) := by
  induction pairs with
  | nil =>
    intro base _
    simp only [pairListBuild, List.length_nil, List.countP_nil, List.map_nil, List.sum_nil, add_zero]
    exact ⟨⟨fun j hj => absurd hj (Nat.not_lt_zero _), fun _ h => by simp at h⟩,
      trivial, fun _ h => by simp at h, fun _ _ _ _ _ => trivial,
      fun _ _ _ _ h => by simp at h⟩
  | cons hd rest ih =>
    rcases hd with ⟨p1, p2, q1, q2⟩
    intro base hbase
    dsimp only [pairListBuild]
    set g1 := pairGadget n m base p1 p2 q1 q2
    set r := pairListBuild n m (base + g1.1.length) rest
    obtain ⟨hok1, hnl1, hlt1, hval1, hdep1⟩ := pairGadget_spec n m base hbase p1 p2 q1 q2
    change isLinearOK g1.1 base at hok1
    change g1.1.countP nlGate = 1 at hnl1
    change g1.2 < base + g1.1.length at hlt1
    obtain ⟨hok2, hnl2, hlt2, hval2, hdep2⟩ := ih (base + g1.1.length) (by omega)
    change isLinearOK r.1 (base + g1.1.length) at hok2
    change r.1.countP nlGate = rest.length at hnl2
    change ∀ w ∈ r.2, w < base + g1.1.length + r.1.length at hlt2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact isLinearOK_append hok1 hok2
    · rw [List.countP_append, hnl1, hnl2]; simp; omega
    · intro w hw
      simp only [List.mem_cons] at hw
      simp only [List.length_append]
      rcases hw with rfl | hw2
      · omega
      · have := hlt2 w hw2; omega
    · intro x y ws hlen hws
      rw [List.foldl_append]
      let ws1 := g1.1.foldl wireStep ws
      have hlen1 : ws1.length = base + g1.1.length := by simp [ws1, foldl_wireStep_length, hlen]
      have hws1 : ∀ w < n + m, ws1.getD w false = (oneEach x y).getD w false := fun w hw =>
        (foldl_wireStep_getD_old ws g1.1 w (by omega)).trans (hws w hw)
      simp only [List.map_cons, List.sum_cons]
      have hhead : b2f ((r.1.foldl wireStep ws1).getD g1.2 false) =
          p1 x * q1 y + p2 x * q2 y + p1 x * p2 x + q1 y * q2 y := by
        have hlt1' : g1.2 < ws1.length := by rw [hlen1]; exact hlt1
        rw [foldl_wireStep_getD_old ws1 r.1 g1.2 hlt1']
        exact hval1 x y ws hlen hws
      rw [hhead, hval2 x y ws1 hlen1 hws1]
      ring
    · intro ds hlen hds w hw
      rw [List.foldl_append]
      let ds1 := g1.1.foldl depthStep ds
      have hlen1 : ds1.length = base + g1.1.length := by simp [ds1, foldl_depthStep_length, hlen]
      have hds1 : ∀ w < n + m, ds1.getD w 0 = 0 := fun w hw =>
        (foldl_depthStep_getD_old ds g1.1 w (by omega)).trans (hds w hw)
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw2
      · have hlt1' : g1.2 < ds1.length := by rw [hlen1]; exact hlt1
        rw [foldl_depthStep_getD_old ds1 r.1 g1.2 hlt1']
        exact hdep1 ds hlen hds
      · exact hdep2 ds1 hlen1 hds1 w hw2

lemma rankPairs_aux {n m : ℕ} :
    ∀ (r : ℕ) (p : Fin r → Fin n → F2) (q : Fin r → Fin m → F2),
      ∃ (pairs : List ((Fin n → F2) × (Fin n → F2) × (Fin m → F2) × (Fin m → F2))),
        pairs.length = (r + 1) / 2 ∧
        ∀ x y, (∑ i : Fin r, p i x * q i y) =
          (pairs.map (fun t => t.1 x * t.2.2.1 y + t.2.1 x * t.2.2.2 y)).sum
  | 0, _, _ => ⟨[], rfl, fun _ _ => by simp⟩
  | 1, p, q =>
    ⟨[(p 0, 0, q 0, 0)], rfl, fun x y => by simp [Fin.sum_univ_one]⟩
  | r + 2, p, q => by
    obtain ⟨pairs', hlen', hsum'⟩ := rankPairs_aux r
      (fun i => p i.castSucc.castSucc) (fun i => q i.castSucc.castSucc)
    refine ⟨(p (Fin.last r).castSucc, p (Fin.last (r + 1)),
        q (Fin.last r).castSucc, q (Fin.last (r + 1))) :: pairs', ?_, ?_⟩
    · simp only [List.length_cons, hlen']; omega
    · intro x y
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [List.map_cons, List.sum_cons, ← hsum' x y]
      ring

lemma rankPairs {n m : ℕ} (M : Matrix (Fin n) (Fin m) F2) :
    ∃ (pairs : List ((Fin n → F2) × (Fin n → F2) × (Fin m → F2) × (Fin m → F2))),
      pairs.length = (M.rank + 1) / 2 ∧
      ∀ x y, M x y = (pairs.map (fun t => t.1 x * t.2.2.1 y + t.2.1 x * t.2.2.2 y)).sum := by
  obtain ⟨p, q, hM⟩ := rank_decomp M
  obtain ⟨pairs, hlen, hsum⟩ := rankPairs_aux M.rank p q
  exact ⟨pairs, hlen, fun x y => (hM x y).trans (hsum x y)⟩

lemma upper_bound (n m : ℕ) (G : Fin 2 → Fin n → Fin m → Bool) (u : Fin n) (v : Fin m)
    (X Y : Matrix (Fin n) (Fin m) F2)
    (hX : ∀ x y, X x y = b2f (G 0 x y) + b2f (G 0 x v) + b2f (G 0 u y) + b2f (G 0 u v))
    (hY : ∀ x y, Y x y = b2f (G 1 x y) + b2f (G 1 x v) + b2f (G 1 u y) + b2f (G 1 u v))
    (t : ℕ)
    (ht : (X.rank + 1) / 2 + (Y.rank + 1) / 2 -
      (if X.rank % 2 = 1 ∧ Y.rank % 2 = 1 ∧ (Matrix.fromRows X Y).rank + 2 ≤ X.rank + Y.rank
        then 1 else 0) ≤ t) :
    ∃ (C : Circuit) (tap : Fin 2 → ℕ),
      ReadsBack (n + m) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      C.gates.countP nlGate ≤ t ∧
      ∀ j : Fin 2, (depthsOf (n + m) C.gates).getD (tap j) 0 ≤ 1 ∧
        Represents (G j) ⟨C.gates, tap j⟩ := by
  -- Step 1: Produce pairsX, pairsY, pairsZ
  have hpairs : ∃ (pairsX pairsY pairsZ :
      List ((Fin n → F2) × (Fin n → F2) × (Fin m → F2) × (Fin m → F2))),
      pairsX.length + pairsY.length + pairsZ.length ≤ t ∧
      (∀ x y, X x y = ((pairsX ++ pairsZ).map (fun t => t.1 x * t.2.2.1 y + t.2.1 x * t.2.2.2 y)).sum) ∧
      (∀ x y, Y x y = ((pairsY ++ pairsZ).map (fun t => t.1 x * t.2.2.1 y + t.2.1 x * t.2.2.2 y)).sum) := by
    by_cases hsave : X.rank % 2 = 1 ∧ Y.rank % 2 = 1 ∧ (Matrix.fromRows X Y).rank + 2 ≤ X.rank + Y.rank
    · rw [if_pos hsave] at ht
      obtain ⟨p1, p2, q1, q2, hXr, hYr⟩ := shared_rank2_decomp X Y hsave.2.2
      let Z : Matrix (Fin n) (Fin m) F2 := Matrix.of fun x y => p1 x * q1 y + p2 x * q2 y
      obtain ⟨pairsX, hlenX, hsumX⟩ := rankPairs (X + Z)
      obtain ⟨pairsY, hlenY, hsumY⟩ := rankPairs (Y + Z)
      refine ⟨pairsX, pairsY, [(p1, p2, q1, q2)], ?_, ?_, ?_⟩
      · simp only [List.length_singleton, hlenX, hlenY]
        change (X + Z).rank ≤ X.rank - 1 at hXr
        change (Y + Z).rank ≤ Y.rank - 1 at hYr
        omega
      · intro x y
        simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero, ← hsumX x y, Matrix.add_apply]
        dsimp only [Z, Matrix.of_apply]
        have hz := f2_add_self (p1 x * q1 y + p2 x * q2 y)
        linear_combination -hz
      · intro x y
        simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero, ← hsumY x y, Matrix.add_apply]
        dsimp only [Z, Matrix.of_apply]
        have hz := f2_add_self (p1 x * q1 y + p2 x * q2 y)
        linear_combination -hz
    · rw [if_neg hsave] at ht
      obtain ⟨pairsX, hlenX, hsumX⟩ := rankPairs X
      obtain ⟨pairsY, hlenY, hsumY⟩ := rankPairs Y
      refine ⟨pairsX, pairsY, [], ?_, ?_, ?_⟩
      · simp only [List.length_nil, add_zero, hlenX, hlenY]; omega
      · intro x y; simp [hsumX x y]
      · intro x y; simp [hsumY x y]
  obtain ⟨pairsX, pairsY, pairsZ, hplen, hpX, hpY⟩ := hpairs
  -- Step 2: Build the three blocks of pair gadgets
  let bX := pairListBuild n m (n + m) pairsX
  let base1 := n + m + bX.1.length
  have hbase1 : base1 = n + m + bX.1.length := rfl
  let bY := pairListBuild n m base1 pairsY
  let base2 := base1 + bY.1.length
  have hbase2 : base2 = base1 + bY.1.length := rfl
  let bZ := pairListBuild n m base2 pairsZ
  let baseP := base2 + bZ.1.length
  have hbaseP : baseP = base2 + bZ.1.length := rfl
  let gP := bX.1 ++ bY.1 ++ bZ.1
  obtain ⟨hokX, hnlX, hltX, hvalX, hdepX⟩ := pairListBuild_spec n m pairsX (n + m) (le_refl _)
  change isLinearOK bX.1 (n + m) at hokX
  change bX.1.countP nlGate = pairsX.length at hnlX
  change ∀ w ∈ bX.2, w < base1 at hltX
  obtain ⟨hokY, hnlY, hltY, hvalY, hdepY⟩ := pairListBuild_spec n m pairsY base1 (by omega)
  change isLinearOK bY.1 base1 at hokY
  change bY.1.countP nlGate = pairsY.length at hnlY
  change ∀ w ∈ bY.2, w < base2 at hltY
  obtain ⟨hokZ, hnlZ, hltZ, hvalZ, hdepZ⟩ := pairListBuild_spec n m pairsZ base2 (by omega)
  change isLinearOK bZ.1 base2 at hokZ
  change bZ.1.countP nlGate = pairsZ.length at hnlZ
  change ∀ w ∈ bZ.2, w < baseP at hltZ
  have hlenP : n + m + gP.length = baseP := by simp [gP, List.length_append, hbase1, hbase2, hbaseP]; omega
  -- Step 3: Output 0 affine residual + XOR
  let α0 : Fin n → F2 := fun x =>
    b2f (G 0 x v) + ((pairsX ++ pairsZ).map (fun t => t.1 x * t.2.1 x)).sum
  let β0 : Fin m → F2 := fun y =>
    b2f (G 0 u y) + ((pairsX ++ pairsZ).map (fun t => t.2.2.1 y * t.2.2.2 y)).sum
  let c0 : F2 := b2f (G 0 u v)
  let aff0 := affineBuild n m baseP α0 β0 c0
  let baseA0 := baseP + aff0.1.length
  have hbaseA0 : baseA0 = baseP + aff0.1.length := rfl
  let out0 := xorListBuild baseA0 (aff0.2 :: (bX.2 ++ bZ.2))
  let base0 := baseA0 + out0.1.length
  have hbase0 : base0 = baseA0 + out0.1.length := rfl
  -- Step 4: Output 1 affine residual + XOR
  let α1 : Fin n → F2 := fun x =>
    b2f (G 1 x v) + ((pairsY ++ pairsZ).map (fun t => t.1 x * t.2.1 x)).sum
  let β1 : Fin m → F2 := fun y =>
    b2f (G 1 u y) + ((pairsY ++ pairsZ).map (fun t => t.2.2.1 y * t.2.2.2 y)).sum
  let c1 : F2 := b2f (G 1 u v)
  let aff1 := affineBuild n m base0 α1 β1 c1
  let baseA1 := base0 + aff1.1.length
  have hbaseA1 : baseA1 = base0 + aff1.1.length := rfl
  let out1 := xorListBuild baseA1 (aff1.2 :: (bY.2 ++ bZ.2))
  -- Specs for aff0, out0, aff1, out1
  obtain ⟨hokA0, hnlA0, hltA0, hvalA0, hdepA0⟩ := affineBuild_spec n m baseP (by omega) α0 β0 c0
  change isLinearOK aff0.1 baseP at hokA0
  change aff0.1.countP nlGate = 0 at hnlA0
  change aff0.2 < baseA0 at hltA0
  have hlt_in0 : ∀ w ∈ aff0.2 :: (bX.2 ++ bZ.2), w < baseA0 := by
    intro w hw
    simp only [List.mem_cons, List.mem_append] at hw
    rcases hw with rfl | hwx | hwz
    · exact hltA0
    · have := hltX w hwx; omega
    · have := hltZ w hwz; omega
  obtain ⟨hokO0, hnlO0, hltO0, hvalO0, hdepO0⟩ := xorListBuild_spec _ baseA0 hlt_in0
  change isLinearOK out0.1 baseA0 at hokO0
  change out0.1.countP nlGate = 0 at hnlO0
  change out0.2 < base0 at hltO0
  obtain ⟨hokA1, hnlA1, hltA1, hvalA1, hdepA1⟩ := affineBuild_spec n m base0 (by omega) α1 β1 c1
  change isLinearOK aff1.1 base0 at hokA1
  change aff1.1.countP nlGate = 0 at hnlA1
  change aff1.2 < baseA1 at hltA1
  have hlt_in1 : ∀ w ∈ aff1.2 :: (bY.2 ++ bZ.2), w < baseA1 := by
    intro w hw
    simp only [List.mem_cons, List.mem_append] at hw
    rcases hw with rfl | hwy | hwz
    · exact hltA1
    · have := hltY w hwy; omega
    · have := hltZ w hwz; omega
  obtain ⟨hokO1, hnlO1, hltO1, hvalO1, hdepO1⟩ := xorListBuild_spec _ baseA1 hlt_in1
  change isLinearOK out1.1 baseA1 at hokO1
  change out1.1.countP nlGate = 0 at hnlO1
  change out1.2 < baseA1 + out1.1.length at hltO1
  -- Assemble the full gate list
  let gs := gP ++ aff0.1 ++ out0.1 ++ aff1.1 ++ out1.1
  have hokAll : isLinearOK gs (n + m) := by
    have h1 := isLinearOK_append hokX hokY
    have h2 : isLinearOK gP (n + m) :=
      isLinearOK_append h1 (isLinearOK_eq hokZ (by simp [List.length_append, hbase1, hbase2]; omega))
    have h3 : isLinearOK (gP ++ aff0.1) (n + m) :=
      isLinearOK_append h2 (isLinearOK_eq hokA0 hlenP.symm)
    have h4 : isLinearOK (gP ++ aff0.1 ++ out0.1) (n + m) :=
      isLinearOK_append h3 (isLinearOK_eq hokO0 (by simp [List.length_append, hlenP, hbaseA0]; omega))
    have h5 : isLinearOK (gP ++ aff0.1 ++ out0.1 ++ aff1.1) (n + m) :=
      isLinearOK_append h4 (isLinearOK_eq hokA1 (by simp [List.length_append, hlenP, hbaseA0, hbase0]; omega))
    exact isLinearOK_append h5
      (isLinearOK_eq hokO1 (by simp [List.length_append, hlenP, hbaseA0, hbase0, hbaseA1]; omega))
  refine ⟨⟨gs, 0⟩, fun j => if j = 0 then out0.2 else out1.2, hokAll.1, hokAll.2, ?_, ?_⟩
  · simp only [gs, gP, List.countP_append, hnlX, hnlY, hnlZ, hnlA0, hnlO0, hnlA1, hnlO1]
    omega
  · intro j
    -- Compute depths up to each block
    let ds0 := List.replicate (n + m) 0
    let dsX := bX.1.foldl depthStep ds0
    let dsY := bY.1.foldl depthStep dsX
    let dsP := bZ.1.foldl depthStep dsY
    let dsA0 := aff0.1.foldl depthStep dsP
    let dsO0 := out0.1.foldl depthStep dsA0
    let dsA1 := aff1.1.foldl depthStep dsO0
    have hds0_len : ds0.length = n + m := List.length_replicate
    have hds0_get : ∀ w < n + m, ds0.getD w 0 = 0 := fun w hw => by
      simp [ds0, List.getD_eq_getElem?_getD, hw]
    have hdsX_len : dsX.length = base1 := by simp [dsX, foldl_depthStep_length, hds0_len, base1]
    have hdsX_get : ∀ w < n + m, dsX.getD w 0 = 0 := fun w hw =>
      (foldl_depthStep_getD_old ds0 bX.1 w (by omega)).trans (hds0_get w hw)
    have hdsY_len : dsY.length = base2 := by simp [dsY, foldl_depthStep_length, hdsX_len, base2]
    have hdsY_get : ∀ w < n + m, dsY.getD w 0 = 0 := fun w hw =>
      (foldl_depthStep_getD_old dsX bY.1 w (by omega)).trans (hdsX_get w hw)
    have hdsP_len : dsP.length = baseP := by simp [dsP, foldl_depthStep_length, hdsY_len, baseP]
    have hdsP_get : ∀ w < n + m, dsP.getD w 0 = 0 := fun w hw =>
      (foldl_depthStep_getD_old dsY bZ.1 w (by omega)).trans (hdsY_get w hw)
    have hdsA0_len : dsA0.length = baseA0 := by simp [dsA0, foldl_depthStep_length, hdsP_len, baseA0]
    have hdsA0_get : ∀ w < n + m, dsA0.getD w 0 = 0 := fun w hw =>
      (foldl_depthStep_getD_old dsP aff0.1 w (by omega)).trans (hdsP_get w hw)
    have hdsO0_len : dsO0.length = base0 := by simp [dsO0, foldl_depthStep_length, hdsA0_len, base0]
    have hdsO0_get : ∀ w < n + m, dsO0.getD w 0 = 0 := fun w hw =>
      (foldl_depthStep_getD_old dsA0 out0.1 w (by omega)).trans (hdsA0_get w hw)
    have hdsA1_len : dsA1.length = baseA1 := by simp [dsA1, foldl_depthStep_length, hdsO0_len, baseA1]
    have hdep_all_bX : ∀ w ∈ bX.2, dsP.getD w 0 ≤ 1 := fun w hw => by
      have hw1 := hltX w hw
      rw [foldl_depthStep_getD_old dsY bZ.1 w (by omega),
        foldl_depthStep_getD_old dsX bY.1 w (by omega)]
      exact hdepX ds0 hds0_len hds0_get w hw
    have hdep_all_bY : ∀ w ∈ bY.2, dsP.getD w 0 ≤ 1 := fun w hw => by
      have hw2 := hltY w hw
      rw [foldl_depthStep_getD_old dsY bZ.1 w (by omega)]
      exact hdepY dsX hdsX_len hdsX_get w hw
    have hdep_all_bZ : ∀ w ∈ bZ.2, dsP.getD w 0 ≤ 1 := fun w hw =>
      hdepZ dsY hdsY_len hdsY_get w hw
    have hdep_out0 : dsO0.getD out0.2 0 ≤ 1 := by
      refine hdepO0 dsA0 1 hdsA0_len ?_
      intro w hw
      simp only [List.mem_cons, List.mem_append] at hw
      rcases hw with rfl | hwx | hwz
      · rw [hdepA0 dsP hdsP_len hdsP_get]; omega
      · have hw1 := hltX w hwx
        rw [foldl_depthStep_getD_old dsP aff0.1 w (by omega)]
        exact hdep_all_bX w hwx
      · have hw3 := hltZ w hwz
        rw [foldl_depthStep_getD_old dsP aff0.1 w (by omega)]
        exact hdep_all_bZ w hwz
    have hdep_out1 : (out1.1.foldl depthStep dsA1).getD out1.2 0 ≤ 1 := by
      refine hdepO1 dsA1 1 hdsA1_len ?_
      intro w hw
      simp only [List.mem_cons, List.mem_append] at hw
      rcases hw with rfl | hwy | hwz
      · rw [hdepA1 dsO0 hdsO0_len hdsO0_get]; omega
      · have hw2 := hltY w hwy
        rw [foldl_depthStep_getD_old dsO0 aff1.1 w (by omega),
          foldl_depthStep_getD_old dsA0 out0.1 w (by omega),
          foldl_depthStep_getD_old dsP aff0.1 w (by omega)]
        exact hdep_all_bY w hwy
      · have hw3 := hltZ w hwz
        rw [foldl_depthStep_getD_old dsO0 aff1.1 w (by omega),
          foldl_depthStep_getD_old dsA0 out0.1 w (by omega),
          foldl_depthStep_getD_old dsP aff0.1 w (by omega)]
        exact hdep_all_bZ w hwz
    -- Now split j = 0 vs j = 1
    fin_cases j
    · simp only [Fin.zero_eta, ↓reduceIte]
      constructor
      · change (gs.foldl depthStep ds0).getD out0.2 0 ≤ 1
        simp only [gs, gP, List.foldl_append]
        change ((out1.1.foldl depthStep (aff1.1.foldl depthStep dsO0)).getD out0.2 0) ≤ 1
        rw [foldl_depthStep_getD_old dsA1 out1.1 out0.2 (by omega),
          foldl_depthStep_getD_old dsO0 aff1.1 out0.2 (by omega)]
        exact hdep_out0
      · intro x y
        apply b2f_inj
        change b2f ((gs.foldl wireStep (oneEach x y)).getD out0.2 false) = b2f (G 0 x y)
        let ws0 := oneEach x y
        let wsX := bX.1.foldl wireStep ws0
        let wsY := bY.1.foldl wireStep wsX
        let wsP := bZ.1.foldl wireStep wsY
        let wsA0 := aff0.1.foldl wireStep wsP
        let wsO0 := out0.1.foldl wireStep wsA0
        let wsA1 := aff1.1.foldl wireStep wsO0
        have hws0_len : ws0.length = n + m := by simp [ws0, oneEach]
        have hws0_get : ∀ w < n + m, ws0.getD w false = (oneEach x y).getD w false := fun _ _ => rfl
        have hwsX_len : wsX.length = base1 := by simp [wsX, foldl_wireStep_length, hws0_len, base1]
        have hwsX_get : ∀ w < n + m, wsX.getD w false = (oneEach x y).getD w false := fun w hw =>
          (foldl_wireStep_getD_old ws0 bX.1 w (by omega)).trans (hws0_get w hw)
        have hwsY_len : wsY.length = base2 := by simp [wsY, foldl_wireStep_length, hwsX_len, base2]
        have hwsY_get : ∀ w < n + m, wsY.getD w false = (oneEach x y).getD w false := fun w hw =>
          (foldl_wireStep_getD_old wsX bY.1 w (by omega)).trans (hwsX_get w hw)
        have hwsP_len : wsP.length = baseP := by simp [wsP, foldl_wireStep_length, hwsY_len, baseP]
        have hwsP_get : ∀ w < n + m, wsP.getD w false = (oneEach x y).getD w false := fun w hw =>
          (foldl_wireStep_getD_old wsY bZ.1 w (by omega)).trans (hwsY_get w hw)
        have hwsA0_len : wsA0.length = baseA0 := by simp [wsA0, foldl_wireStep_length, hwsP_len, baseA0]
        have hwsO0_len : wsO0.length = base0 := by simp [wsO0, foldl_wireStep_length, hwsA0_len, base0]
        have hwsA1_len : wsA1.length = baseA1 := by simp [wsA1, foldl_wireStep_length, hwsO0_len, baseA1]
        simp only [gs, gP, List.foldl_append]
        change b2f ((out1.1.foldl wireStep wsA1).getD out0.2 false) = b2f (G 0 x y)
        rw [foldl_wireStep_getD_old wsA1 out1.1 out0.2 (by omega),
          foldl_wireStep_getD_old wsO0 aff1.1 out0.2 (by omega)]
        rw [hvalO0 wsA0 hwsA0_len]
        simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append]
        have ha0_v : b2f (wsA0.getD aff0.2 false) = α0 x + β0 y + c0 :=
          hvalA0 x y wsP hwsP_len hwsP_get
        have hX_v : (bX.2.map (fun w => b2f (wsA0.getD w false))).sum =
            (pairsX.map (fun t => t.1 x * t.2.2.1 y + t.2.1 x * t.2.2.2 y)).sum +
            (pairsX.map (fun t => t.1 x * t.2.1 x)).sum +
            (pairsX.map (fun t => t.2.2.1 y * t.2.2.2 y)).sum := by
          have hcongr : bX.2.map (fun w => b2f (wsA0.getD w false)) =
              bX.2.map (fun w => b2f (wsX.getD w false)) := by
            refine List.map_congr_left fun w hw => ?_
            have hw1 := hltX w hw
            rw [foldl_wireStep_getD_old wsP aff0.1 w (by omega),
              foldl_wireStep_getD_old wsY bZ.1 w (by omega),
              foldl_wireStep_getD_old wsX bY.1 w (by omega)]
          rw [hcongr]
          exact hvalX x y ws0 hws0_len hws0_get
        have hZ_v : (bZ.2.map (fun w => b2f (wsA0.getD w false))).sum =
            (pairsZ.map (fun t => t.1 x * t.2.2.1 y + t.2.1 x * t.2.2.2 y)).sum +
            (pairsZ.map (fun t => t.1 x * t.2.1 x)).sum +
            (pairsZ.map (fun t => t.2.2.1 y * t.2.2.2 y)).sum := by
          have hcongr : bZ.2.map (fun w => b2f (wsA0.getD w false)) =
              bZ.2.map (fun w => b2f (wsP.getD w false)) := by
            refine List.map_congr_left fun w hw => ?_
            have hw3 := hltZ w hw
            rw [foldl_wireStep_getD_old wsP aff0.1 w (by omega)]
          rw [hcongr]
          exact hvalZ x y wsY hwsY_len hwsY_get
        rw [ha0_v, hX_v, hZ_v]
        have hXp := hpX x y
        have hXx := hX x y
        dsimp only [α0, β0, c0]
        simp only [List.map_append, List.sum_append] at hXp ⊢
        have h1 := f2_add_self (b2f (G 0 x v))
        have h2 := f2_add_self (b2f (G 0 u y))
        have h3 := f2_add_self (b2f (G 0 u v))
        have h4 := f2_add_self ((pairsX.map (fun t => t.1 x * t.2.1 x)).sum)
        have h5 := f2_add_self ((pairsZ.map (fun t => t.1 x * t.2.1 x)).sum)
        have h6 := f2_add_self ((pairsX.map (fun t => t.2.2.1 y * t.2.2.2 y)).sum)
        have h7 := f2_add_self ((pairsZ.map (fun t => t.2.2.1 y * t.2.2.2 y)).sum)
        linear_combination hXx - hXp + h1 + h2 + h3 + h4 + h5 + h6 + h7
    · have h10 : (1 : Fin 2) ≠ 0 := by decide
      simp only [Fin.mk_one, h10, ↓reduceIte]
      constructor
      · change (gs.foldl depthStep ds0).getD out1.2 0 ≤ 1
        simp only [gs, gP, List.foldl_append]
        exact hdep_out1
      · intro x y
        apply b2f_inj
        change b2f ((gs.foldl wireStep (oneEach x y)).getD out1.2 false) = b2f (G 1 x y)
        let ws0 := oneEach x y
        let wsX := bX.1.foldl wireStep ws0
        let wsY := bY.1.foldl wireStep wsX
        let wsP := bZ.1.foldl wireStep wsY
        let wsA0 := aff0.1.foldl wireStep wsP
        let wsO0 := out0.1.foldl wireStep wsA0
        let wsA1 := aff1.1.foldl wireStep wsO0
        have hws0_len : ws0.length = n + m := by simp [ws0, oneEach]
        have hws0_get : ∀ w < n + m, ws0.getD w false = (oneEach x y).getD w false := fun _ _ => rfl
        have hwsX_len : wsX.length = base1 := by simp [wsX, foldl_wireStep_length, hws0_len, base1]
        have hwsX_get : ∀ w < n + m, wsX.getD w false = (oneEach x y).getD w false := fun w hw =>
          (foldl_wireStep_getD_old ws0 bX.1 w (by omega)).trans (hws0_get w hw)
        have hwsY_len : wsY.length = base2 := by simp [wsY, foldl_wireStep_length, hwsX_len, base2]
        have hwsY_get : ∀ w < n + m, wsY.getD w false = (oneEach x y).getD w false := fun w hw =>
          (foldl_wireStep_getD_old wsX bY.1 w (by omega)).trans (hwsX_get w hw)
        have hwsP_len : wsP.length = baseP := by simp [wsP, foldl_wireStep_length, hwsY_len, baseP]
        have hwsP_get : ∀ w < n + m, wsP.getD w false = (oneEach x y).getD w false := fun w hw =>
          (foldl_wireStep_getD_old wsY bZ.1 w (by omega)).trans (hwsY_get w hw)
        have hwsA0_len : wsA0.length = baseA0 := by simp [wsA0, foldl_wireStep_length, hwsP_len, baseA0]
        have hwsA0_get : ∀ w < n + m, wsA0.getD w false = (oneEach x y).getD w false := fun w hw =>
          (foldl_wireStep_getD_old wsP aff0.1 w (by omega)).trans (hwsP_get w hw)
        have hwsO0_len : wsO0.length = base0 := by simp [wsO0, foldl_wireStep_length, hwsA0_len, base0]
        have hwsO0_get : ∀ w < n + m, wsO0.getD w false = (oneEach x y).getD w false := fun w hw =>
          (foldl_wireStep_getD_old wsA0 out0.1 w (by omega)).trans (hwsA0_get w hw)
        have hwsA1_len : wsA1.length = baseA1 := by simp [wsA1, foldl_wireStep_length, hwsO0_len, baseA1]
        simp only [gs, gP, List.foldl_append]
        change b2f ((out1.1.foldl wireStep wsA1).getD out1.2 false) = b2f (G 1 x y)
        rw [hvalO1 wsA1 hwsA1_len]
        simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append]
        have ha1_v : b2f (wsA1.getD aff1.2 false) = α1 x + β1 y + c1 :=
          hvalA1 x y wsO0 hwsO0_len hwsO0_get
        have hY_v : (bY.2.map (fun w => b2f (wsA1.getD w false))).sum =
            (pairsY.map (fun t => t.1 x * t.2.2.1 y + t.2.1 x * t.2.2.2 y)).sum +
            (pairsY.map (fun t => t.1 x * t.2.1 x)).sum +
            (pairsY.map (fun t => t.2.2.1 y * t.2.2.2 y)).sum := by
          have hcongr : bY.2.map (fun w => b2f (wsA1.getD w false)) =
              bY.2.map (fun w => b2f (wsY.getD w false)) := by
            refine List.map_congr_left fun w hw => ?_
            have hw2 := hltY w hw
            rw [foldl_wireStep_getD_old wsO0 aff1.1 w (by omega),
              foldl_wireStep_getD_old wsA0 out0.1 w (by omega),
              foldl_wireStep_getD_old wsP aff0.1 w (by omega),
              foldl_wireStep_getD_old wsY bZ.1 w (by omega)]
          rw [hcongr]
          exact hvalY x y wsX hwsX_len hwsX_get
        have hZ_v : (bZ.2.map (fun w => b2f (wsA1.getD w false))).sum =
            (pairsZ.map (fun t => t.1 x * t.2.2.1 y + t.2.1 x * t.2.2.2 y)).sum +
            (pairsZ.map (fun t => t.1 x * t.2.1 x)).sum +
            (pairsZ.map (fun t => t.2.2.1 y * t.2.2.2 y)).sum := by
          have hcongr : bZ.2.map (fun w => b2f (wsA1.getD w false)) =
              bZ.2.map (fun w => b2f (wsP.getD w false)) := by
            refine List.map_congr_left fun w hw => ?_
            have hw3 := hltZ w hw
            rw [foldl_wireStep_getD_old wsO0 aff1.1 w (by omega),
              foldl_wireStep_getD_old wsA0 out0.1 w (by omega),
              foldl_wireStep_getD_old wsP aff0.1 w (by omega)]
          rw [hcongr]
          exact hvalZ x y wsY hwsY_len hwsY_get
        rw [ha1_v, hY_v, hZ_v]
        have hYp := hpY x y
        have hYy := hY x y
        dsimp only [α1, β1, c1]
        simp only [List.map_append, List.sum_append] at hYp ⊢
        have h1 := f2_add_self (b2f (G 1 x v))
        have h2 := f2_add_self (b2f (G 1 u y))
        have h3 := f2_add_self (b2f (G 1 u v))
        have h4 := f2_add_self ((pairsY.map (fun t => t.1 x * t.2.1 x)).sum)
        have h5 := f2_add_self ((pairsZ.map (fun t => t.1 x * t.2.1 x)).sum)
        have h6 := f2_add_self ((pairsY.map (fun t => t.2.2.1 y * t.2.2.2 y)).sum)
        have h7 := f2_add_self ((pairsZ.map (fun t => t.2.2.1 y * t.2.2.2 y)).sum)
        linear_combination hYy - hYp + h1 + h2 + h3 + h4 + h5 + h6 + h7

end PEqualNP.Outside.L_meta_25752

theorem PEqualNP.Outside.L_meta_25752 :
    let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
      (g.inputs.length == 2) &&
      xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
          (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
    let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      C.gates.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
        (List.replicate width 0)
    let fits := fun (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) =>
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
        (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
        ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
          PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩
    ∀ (n m : ℕ) (G : Fin 2 → Fin n → Fin m → Bool) (u : Fin n) (v : Fin m),
      let F := ZMod 2
      let entry := fun j x y => if G j x y then (1 : F) else 0
      let A : Fin 2 → Matrix (Fin n) (Fin m) F := fun j x y =>
        entry j x y + entry j x v + entry j u y + entry j u v
      let X := A 0
      let Y := A 1
      let r := X.rank
      let s := Y.rank
      (Matrix.fromCols X Y).rank = r+s →
      let save := if r%2 = 1 ∧ s%2 = 1 ∧ (Matrix.fromRows X Y).rank+2 ≤ r+s then 1 else 0
      ∀ t : ℕ, fits n m 2 G t ↔ (r+1)/2+(s+1)/2-save ≤ t := by
  intro nonlinear depths fits n m G u v F entry A X Y r s hdisjCols save t
  constructor
  · rintro ⟨C, tap, hrb, hfan, hcnt, htap⟩
    exact PEqualNP.Outside.L_meta_25752.lower_bound n m G u v X Y (fun _ _ => rfl) (fun _ _ => rfl)
      hdisjCols t C tap hrb hfan hcnt htap
  · intro ht
    exact PEqualNP.Outside.L_meta_25752.upper_bound n m G u v X Y (fun _ _ => rfl) (fun _ _ => rfl) t ht
