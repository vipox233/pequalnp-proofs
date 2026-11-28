import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_374

open Finset

noncomputable section

section MatrixHelpers

def E0 (α : Type*) [Zero α] [One α] : Matrix Bool Bool α :=
  Matrix.of fun a b => if a = false ∧ b = false then 1 else 0

@[simp] lemma E0_apply {α : Type*} [Zero α] [One α] (a b : Bool) :
    E0 α a b = if a = false ∧ b = false then 1 else 0 := rfl

lemma E0_mul_apply {α : Type*} [CommSemiring α] (M : Matrix Bool Bool α) (a b : Bool) :
    (E0 α * M) a b = if a = false then M false b else 0 := by
  cases a <;> simp [Matrix.mul_apply, Fintype.sum_bool]

lemma mul_E0_apply {α : Type*} [CommSemiring α] (M : Matrix Bool Bool α) (a b : Bool) :
    (M * E0 α) a b = if b = false then M a false else 0 := by
  cases b <;> simp [Matrix.mul_apply, Fintype.sum_bool]

lemma E0_mul_M_mul_E0 {α : Type*} [CommSemiring α] (M : Matrix Bool Bool α) :
    E0 α * M * E0 α = M false false • E0 α := by
  ext a b
  cases a <;> cases b <;> simp [Matrix.mul_apply, Fintype.sum_bool]

lemma trace_E0_mul {α : Type*} [CommSemiring α] (M : Matrix Bool Bool α) :
    Matrix.trace (E0 α * M) = M false false := by
  simp [Matrix.trace, Fintype.sum_bool, E0_mul_apply]

lemma trace_list_append_comm {α : Type*} [CommSemiring α] (l1 l2 : List (Matrix Bool Bool α)) :
    Matrix.trace (l1 ++ l2).prod = Matrix.trace (l2 ++ l1).prod := by
  rw [List.prod_append, List.prod_append, Matrix.trace_mul_comm]

lemma trace_list_rotate {α : Type*} [CommSemiring α] (l : List (Matrix Bool Bool α)) (k : ℕ) :
    Matrix.trace (l.rotate k).prod = Matrix.trace l.prod := by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    rcases l with _ | ⟨hd, tl⟩
    · simp
    · have h1 : (hd :: tl).rotate (k + 1) = (tl ++ [hd]).rotate k :=
        List.rotate_cons_succ tl hd k
      rw [h1, ih, trace_list_append_comm tl [hd], List.singleton_append]

def collectGaps (cur : ℕ) : List Bool → List ℕ
  | [] => [cur]
  | false :: xs => collectGaps (cur + 1) xs
  | true :: xs => cur :: collectGaps 1 xs

lemma collectGaps_pos (cur : ℕ) (hcur : 1 ≤ cur) (xs : List Bool) :
    ∀ g ∈ collectGaps cur xs, 1 ≤ g := by
  induction xs generalizing cur with
  | nil =>
    intro g hg
    simp [collectGaps] at hg
    omega
  | cons b xs ih =>
    cases b with
    | false =>
      intro g hg
      exact ih (cur + 1) (by omega) g hg
    | true =>
      intro g hg
      simp [collectGaps] at hg
      rcases hg with rfl | hg
      · exact hcur
      · exact ih 1 (by omega) g hg

lemma collectGaps_sum (cur : ℕ) (xs : List Bool) :
    (collectGaps cur xs).sum = cur + xs.length := by
  induction xs generalizing cur with
  | nil => simp [collectGaps]
  | cons b xs ih =>
    cases b with
    | false =>
      simp [collectGaps, ih (cur + 1)]
      omega
    | true =>
      simp [collectGaps, ih 1]
      omega

lemma collectGaps_replicate_false (cur k : ℕ) (xs : List Bool) :
    collectGaps cur (List.replicate k false ++ xs) = collectGaps (cur + k) xs := by
  induction k generalizing cur with
  | zero => simp
  | succ k ih =>
    simp [List.replicate_succ, collectGaps, ih]
    ring_nf

lemma collectGaps_flatMap (cur : ℕ) (gs : List ℕ) (hgs : ∀ g ∈ gs, 1 ≤ g) :
    collectGaps cur (gs.flatMap (fun g => true :: List.replicate (g - 1) false)) = cur :: gs := by
  induction gs generalizing cur with
  | nil => simp [collectGaps]
  | cons g gs ih =>
    have hg1 : 1 ≤ g := hgs g (by simp)
    have hgs1 : ∀ x ∈ gs, 1 ≤ x := fun x hx => hgs x (by simp [hx])
    simp only [List.flatMap_cons, List.cons_append, collectGaps]
    rw [collectGaps_replicate_false, show 1 + (g - 1) = g by omega]
    rw [ih g hgs1]

lemma trace_collectGaps {α : Type*} [CommSemiring α] (N : Matrix Bool Bool α)
    (cur : ℕ) (xs : List Bool) :
    Matrix.trace (E0 α * N ^ cur * (xs.map (fun b => if b then E0 α * N else N)).prod) =
      ((collectGaps cur xs).map (fun g => (N ^ g) false false)).prod := by
  induction xs generalizing cur with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Matrix.mul_one, collectGaps, List.map_cons,
      List.prod_cons, mul_one]
    rw [trace_E0_mul]
  | cons b xs ih =>
    cases b with
    | false =>
      simp only [List.map_cons, List.prod_cons, Bool.false_eq_true, ↓reduceIte, collectGaps]
      have h1 : E0 α * N ^ cur * (N * (xs.map (fun b => if b then E0 α * N else N)).prod) =
          E0 α * N ^ (cur + 1) * (xs.map (fun b => if b then E0 α * N else N)).prod := by
        simp only [pow_succ, Matrix.mul_assoc]
      rw [h1, ih (cur + 1)]
    | true =>
      simp only [List.map_cons, List.prod_cons, ↓reduceIte, collectGaps]
      have h1 : E0 α * N ^ cur * (E0 α * N * (xs.map (fun b => if b then E0 α * N else N)).prod) =
          (E0 α * N ^ cur * E0 α) * (N * (xs.map (fun b => if b then E0 α * N else N)).prod) := by
        simp only [Matrix.mul_assoc]
      rw [h1, E0_mul_M_mul_E0, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
      have h2 : E0 α * (N * (xs.map (fun b => if b then E0 α * N else N)).prod) =
          E0 α * N ^ 1 * (xs.map (fun b => if b then E0 α * N else N)).prod := by
        simp [pow_one, Matrix.mul_assoc]
      rw [h2, ih 1]

lemma list_prod_finRange_entry {α : Type*} [CommSemiring α] :
    ∀ (r : ℕ) (g : Fin r → Matrix Bool Bool α) (a b : Bool),
      ((List.finRange r).map g).prod a b =
        ∑ v ∈ (Finset.univ : Finset (Fin (r + 1) → Bool)).filter (fun v => v 0 = a ∧ v (Fin.last r) = b),
          ∏ i : Fin r, g i (v i.castSucc) (v i.succ) := by
  intro r
  induction r with
  | zero =>
    intro g a b
    simp only [List.finRange_zero, List.map_nil, List.prod_nil, Fin.isValue, Fin.last_zero,
      Fin.prod_univ_zero]
    by_cases hab : a = b
    · subst hab
      have h1 : (Finset.univ : Finset (Fin 1 → Bool)).filter (fun v => v 0 = a ∧ v 0 = a) = {fun _ => a} := by
        ext v
        simp [funext_iff, Fin.forall_fin_one]
      rw [h1, sum_singleton]
      simp
    · have h1 : (Finset.univ : Finset (Fin 1 → Bool)).filter (fun v => v 0 = a ∧ v 0 = b) = ∅ := by
        ext v
        simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_and]
        intro h1 h2
        exact hab (h1.symm.trans h2)
      rw [h1, sum_empty]
      simp [Matrix.one_apply, hab]
  | succ r ih =>
    intro g a b
    rw [List.finRange_succ_last, List.map_append, List.map_cons, List.map_nil, List.prod_append,
      List.prod_cons, List.prod_nil, Matrix.mul_one, Matrix.mul_apply, List.map_map]
    have hsum : ∑ c : Bool, ((List.finRange r).map (g ∘ Fin.castSucc)).prod a c * g (Fin.last r) c b =
        ∑ c : Bool, ∑ v' ∈ (Finset.univ : Finset (Fin (r + 1) → Bool)).filter (fun v => v 0 = a ∧ v (Fin.last r) = c),
          (∏ i : Fin r, g i.castSucc (v' i.castSucc) (v' i.succ)) * g (Fin.last r) c b := by
      apply sum_congr rfl
      intro c _
      rw [ih (g ∘ Fin.castSucc) a c, sum_mul]
      rfl
    rw [hsum]
    let e : (Fin (r + 1) → Bool) ↪ (Fin (r + 2) → Bool) :=
      ⟨fun v' => Fin.snoc (α := fun _ => Bool) v' b, fun x y h => by
        ext i
        have := congrFun h i.castSucc
        simpa [Fin.snoc_castSucc] using this⟩
    have he : ∀ v', e v' = Fin.snoc (α := fun _ => Bool) v' b := fun _ => rfl
    have hsplit : (Finset.univ : Finset (Fin (r + 2) → Bool)).filter (fun v => v 0 = a ∧ v (Fin.last (r + 1)) = b) =
        ((Finset.univ : Finset (Fin (r + 1) → Bool)).filter (fun v => v 0 = a ∧ v (Fin.last r) = true)).map e ∪
        ((Finset.univ : Finset (Fin (r + 1) → Bool)).filter (fun v => v 0 = a ∧ v (Fin.last r) = false)).map e := by
      ext v
      simp only [mem_filter, mem_univ, true_and, mem_union, mem_map]
      constructor
      · rintro ⟨hv0, hvlast⟩
        by_cases hc : v (Fin.last r).castSucc = true
        · refine Or.inl ⟨Fin.init v, ⟨by simpa [Fin.init] using hv0, hc⟩, ?_⟩
          rw [he]
          ext i
          refine Fin.lastCases (by simpa [Fin.snoc_last] using hvlast.symm) (fun j => by simp [Fin.snoc_castSucc, Fin.init]) i
        · have hcf : v (Fin.last r).castSucc = false := Bool.eq_false_iff.mpr hc
          refine Or.inr ⟨Fin.init v, ⟨by simpa [Fin.init] using hv0, hcf⟩, ?_⟩
          rw [he]
          ext i
          refine Fin.lastCases (by simpa [Fin.snoc_last] using hvlast.symm) (fun j => by simp [Fin.snoc_castSucc, Fin.init]) i
      · rintro (⟨v', ⟨hv0, _⟩, rfl⟩ | ⟨v', ⟨hv0, _⟩, rfl⟩)
        · rw [he]
          exact ⟨by simpa [Fin.snoc_castSucc] using hv0, by simp [Fin.snoc_last]⟩
        · rw [he]
          exact ⟨by simpa [Fin.snoc_castSucc] using hv0, by simp [Fin.snoc_last]⟩
    have hdisj : Disjoint
        (((Finset.univ : Finset (Fin (r + 1) → Bool)).filter (fun v => v 0 = a ∧ v (Fin.last r) = true)).map e)
        (((Finset.univ : Finset (Fin (r + 1) → Bool)).filter (fun v => v 0 = a ∧ v (Fin.last r) = false)).map e) := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      simp only [mem_map, mem_filter, mem_univ, true_and] at hv1 hv2
      rcases hv1 with ⟨v1, hv1, rfl⟩
      rcases hv2 with ⟨v2, hv2, hv⟩
      rw [he, he] at hv
      have := congrFun hv (Fin.last r).castSucc
      simp only [Fin.snoc_castSucc, hv1.2, hv2.2] at this
      exact Bool.false_ne_true this
    rw [hsplit, sum_union hdisj, sum_map, sum_map, Fintype.sum_bool]
    congr 1
    · apply sum_congr rfl
      intro v' hv'
      simp only [mem_filter, mem_univ, true_and] at hv'
      rw [Fin.prod_univ_castSucc]
      congr 1
      · apply prod_congr rfl
        intro i _
        rw [he, Fin.snoc_castSucc, show i.castSucc.succ = i.succ.castSucc from rfl, Fin.snoc_castSucc]
      · rw [he, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, hv'.2]
    · apply sum_congr rfl
      intro v' hv'
      simp only [mem_filter, mem_univ, true_and] at hv'
      rw [Fin.prod_univ_castSucc]
      congr 1
      · apply prod_congr rfl
        intro i _
        rw [he, Fin.snoc_castSucc, show i.castSucc.succ = i.succ.castSucc from rfl, Fin.snoc_castSucc]
      · rw [he, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, hv'.2]

lemma trace_finRange_prod {α : Type*} [CommSemiring α] (m : ℕ) (f : Fin (m + 1) → Matrix Bool Bool α) :
    Matrix.trace ((List.finRange (m + 1)).map f).prod =
      ∑ x : Fin (m + 1) → Bool, ∏ i : Fin (m + 1), f i (x i) (x (i + 1)) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  have h1 : ∀ a : Bool, ((List.finRange (m + 1)).map f).prod a a =
      ∑ v ∈ (Finset.univ : Finset (Fin (m + 2) → Bool)).filter (fun v => v 0 = a ∧ v (Fin.last (m + 1)) = a),
        ∏ i : Fin (m + 1), f i (v i.castSucc) (v i.succ) := fun a =>
    list_prod_finRange_entry (m + 1) f a a
  simp_rw [h1]
  let emb : (Fin (m + 1) → Bool) ↪ (Fin (m + 2) → Bool) :=
    ⟨fun x => Fin.snoc (α := fun _ => Bool) x (x 0), fun x y h => by
      ext i
      have := congrFun h i.castSucc
      simpa [Fin.snoc_castSucc] using this⟩
  have hemb : ∀ x, emb x = Fin.snoc (α := fun _ => Bool) x (x 0) := fun _ => rfl
  have hunion : ∀ a : Bool,
      (Finset.univ : Finset (Fin (m + 2) → Bool)).filter (fun v => v 0 = a ∧ v (Fin.last (m + 1)) = a) =
      ((Finset.univ : Finset (Fin (m + 1) → Bool)).filter (fun x => x 0 = a)).map emb := by
    intro a
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_map]
    constructor
    · rintro ⟨hv0, hvlast⟩
      refine ⟨Fin.init v, by simpa [Fin.init] using hv0, ?_⟩
      rw [hemb]
      ext i
      refine Fin.lastCases ?_ ?_ i
      · rw [Fin.snoc_last]
        exact (show Fin.init v 0 = v 0 from rfl).trans (hv0.trans hvlast.symm)
      · intro j
        simp [Fin.snoc_castSucc, Fin.init]
    · rintro ⟨x, hx0, rfl⟩
      rw [hemb]
      exact ⟨by simpa [Fin.snoc_castSucc] using hx0, by simp [Fin.snoc_last, hx0]⟩
  simp_rw [hunion, sum_map]
  have hsplit : (Finset.univ : Finset (Fin (m + 1) → Bool)) =
      (Finset.univ : Finset (Fin (m + 1) → Bool)).filter (fun x => x 0 = true) ∪
      (Finset.univ : Finset (Fin (m + 1) → Bool)).filter (fun x => x 0 = false) := by
    ext x
    simp
  have hdisj : Disjoint
      ((Finset.univ : Finset (Fin (m + 1) → Bool)).filter (fun x => x 0 = true))
      ((Finset.univ : Finset (Fin (m + 1) → Bool)).filter (fun x => x 0 = false)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [mem_filter, mem_univ, true_and] at hx1 hx2
    exact Bool.false_ne_true (hx2.symm.trans hx1)
  conv_rhs => rw [hsplit, sum_union hdisj]
  rw [Fintype.sum_bool]
  congr 1
  · apply sum_congr rfl
    intro x _
    apply prod_congr rfl
    intro i _
    rw [hemb]
    congr 1
    · rw [Fin.snoc_castSucc]
    · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp i.isLt) with hi | hi
      · have hne : i ≠ Fin.last m := fun h => by subst h; simp at hi
        have hisucc : i.succ = (i + 1).castSucc := by
          ext
          simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_add_one]
          rw [if_neg hne]
        rw [hisucc, Fin.snoc_castSucc]
      · have hisucc : i.succ = Fin.last (m + 1) := by
          ext
          simp [Fin.val_succ, hi]
        have hiadd : i + 1 = 0 := by
          ext
          simp [Fin.val_add, hi]
        rw [hisucc, Fin.snoc_last, hiadd]
  · apply sum_congr rfl
    intro x _
    apply prod_congr rfl
    intro i _
    rw [hemb]
    congr 1
    · rw [Fin.snoc_castSucc]
    · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp i.isLt) with hi | hi
      · have hne : i ≠ Fin.last m := fun h => by subst h; simp at hi
        have hisucc : i.succ = (i + 1).castSucc := by
          ext
          simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_add_one]
          rw [if_neg hne]
        rw [hisucc, Fin.snoc_castSucc]
      · have hisucc : i.succ = Fin.last (m + 1) := by
          ext
          simp [Fin.val_succ, hi]
        have hiadd : i + 1 = 0 := by
          ext
          simp [Fin.val_add, hi]
        rw [hisucc, Fin.snoc_last, hiadd]

end MatrixHelpers

section Polynomials

abbrev R2 := Polynomial (Polynomial ℤ)
abbrev R1 := Polynomial ℤ

def varU : R2 := Polynomial.X
def varV : R2 := Polynomial.C Polynomial.X

def N2 : Matrix Bool Bool R2 :=
  Matrix.of fun a c => if a = c then 1 + varU * varV else varU + varV

@[simp] lemma N2_apply (a c : Bool) :
    N2 a c = if a = c then 1 + varU * varV else varU + varV := rfl

lemma sum_bool_UV (a c : Bool) :
    ∑ b : Bool, varU ^ (if b ≠ c then 1 else 0) * varV ^ (if a ≠ b then 1 else 0) = N2 a c := by
  cases a <;> cases c <;> simp [Fintype.sum_bool, N2_apply] <;> ring

def evalDiag : R2 →+* R1 := Polynomial.evalRingHom Polynomial.X

@[simp] lemma evalDiag_U : evalDiag varU = Polynomial.X := by simp [evalDiag, varU]
@[simp] lemma evalDiag_V : evalDiag varV = Polynomial.X := by simp [evalDiag, varV]

def DegLe (d : ℕ) (P : R1) : Prop := ∀ i, d < i → P.coeff i = 0

lemma degLe_zero_C (z : ℤ) : DegLe 0 (Polynomial.C z) := by
  intro i hi
  rw [Polynomial.coeff_C, if_neg (by omega)]

lemma degLe_X_pow (k : ℕ) : DegLe k (Polynomial.X ^ k : R1) := by
  intro i hi
  rw [Polynomial.coeff_X_pow, if_neg (by omega)]

lemma degLe_add {d : ℕ} {P Q : R1} (hP : DegLe d P) (hQ : DegLe d Q) : DegLe d (P + Q) := by
  intro i hi
  rw [Polynomial.coeff_add, hP i hi, hQ i hi, add_zero]

lemma degLe_mono {d1 d2 : ℕ} {P : R1} (h : d1 ≤ d2) (hP : DegLe d1 P) : DegLe d2 P := by
  intro i hi
  exact hP i (lt_of_le_of_lt h hi)

lemma degLe_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (d : ℕ) (f : ι → R1)
    (hf : ∀ x ∈ s, DegLe d (f x)) : DegLe d (∑ x ∈ s, f x) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    intro i _; simp
  | @insert x s hx ih =>
    rw [sum_insert hx]
    exact degLe_add (hf x (mem_insert_self x s)) (ih fun y hy => hf y (mem_insert_of_mem hy))

lemma degLe_smul {d : ℕ} (z : ℤ) {P : R1} (hP : DegLe d P) : DegLe d (z • P) := by
  intro i hi
  rw [Polynomial.coeff_smul, hP i hi, smul_zero]

lemma degLe_mul {d1 d2 : ℕ} {P Q : R1} (hP : DegLe d1 P) (hQ : DegLe d2 Q) :
    DegLe (d1 + d2) (P * Q) := by
  intro i hi
  rw [Polynomial.coeff_mul]
  apply sum_eq_zero
  intro ab hab
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
  by_cases ha : d1 < ab.1
  · rw [hP ab.1 ha, zero_mul]
  · have hb : d2 < ab.2 := by omega
    rw [hQ ab.2 hb, mul_zero]

lemma degLe_pow {d : ℕ} (k : ℕ) {P : R1} (hP : DegLe d P) : DegLe (k * d) (P ^ k) := by
  induction k with
  | zero =>
    simpa [pow_zero] using degLe_zero_C 1
  | succ k ih =>
    rw [pow_succ, show (k + 1) * d = k * d + d by ring]
    exact degLe_mul ih hP

lemma degLe_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (d : ι → ℕ) (f : ι → R1)
    (hf : ∀ x ∈ s, DegLe (d x) (f x)) : DegLe (∑ x ∈ s, d x) (∏ x ∈ s, f x) := by
  induction s using Finset.induction_on with
  | empty =>
    simpa using degLe_zero_C 1
  | @insert x s hx ih =>
    rw [prod_insert hx, sum_insert hx]
    exact degLe_mul (hf x (mem_insert_self x s)) (ih fun y hy => hf y (mem_insert_of_mem hy))

def homog (d : ℕ) (P : R1) : R1 :=
  ∑ i ∈ Finset.range (d + 1), Polynomial.C (P.coeff i) * (1 - Polynomial.X) ^ i * (1 + Polynomial.X) ^ (d - i)

lemma homog_zero_C (z : ℤ) : homog 0 (Polynomial.C z) = Polynomial.C z := by
  simp [homog]

lemma homog_add (d : ℕ) (P Q : R1) : homog d (P + Q) = homog d P + homog d Q := by
  simp only [homog, Polynomial.coeff_add, map_add, add_mul, sum_add_distrib]

lemma homog_smul (d : ℕ) (z : ℤ) (P : R1) : homog d (z • P) = z • homog d P := by
  simp only [homog]
  rw [smul_sum]
  apply sum_congr rfl
  intro i _
  rw [Polynomial.coeff_smul, zsmul_eq_mul, zsmul_eq_mul, map_mul, map_intCast]
  ring

lemma homog_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (d : ℕ) (f : ι → R1) :
    homog d (∑ x ∈ s, f x) = ∑ x ∈ s, homog d (f x) := by
  induction s using Finset.induction_on with
  | empty => simp [homog]
  | @insert x s hx ih => rw [sum_insert hx, sum_insert hx, homog_add, ih]

lemma homog_X_pow (d k : ℕ) (hk : k ≤ d) :
    homog d (Polynomial.X ^ k) = (1 - Polynomial.X) ^ k * (1 + Polynomial.X) ^ (d - k) := by
  unfold homog
  rw [sum_eq_single k]
  · simp
  · intro i _ hik
    simp [Polynomial.coeff_X_pow, hik]
  · intro hk_not
    exfalso
    exact hk_not (mem_range.mpr (by omega))

lemma homog_C_mul_X_pow (d k : ℕ) (hk : k ≤ d) (z : ℤ) :
    homog d (Polynomial.C z * Polynomial.X ^ k) =
      Polynomial.C z * (1 - Polynomial.X) ^ k * (1 + Polynomial.X) ^ (d - k) := by
  have h : Polynomial.C z * Polynomial.X ^ k = z • (Polynomial.X ^ k : R1) := by
    simp [zsmul_eq_mul]
  rw [h, homog_smul, homog_X_pow d k hk, zsmul_eq_mul]
  simp only [← Polynomial.C_eq_intCast, Int.cast_id]
  ring

lemma eq_sum_range_of_degLe {d : ℕ} {P : R1} (hP : DegLe d P) :
    P = ∑ i ∈ Finset.range (d + 1), Polynomial.C (P.coeff i) * Polynomial.X ^ i := by
  ext k
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hk : k ≤ d
  · rw [sum_eq_single k]
    · simp
    · intro i _ hik
      simp [hik.symm]
    · intro hk_not
      exfalso
      exact hk_not (mem_range.mpr (by omega))
  · have hgt : d < k := by omega
    rw [hP k hgt]
    symm
    apply sum_eq_zero
    intro i hi
    rw [mem_range] at hi
    have hik : k ≠ i := by omega
    simp [hik]

lemma homog_mul {d1 d2 : ℕ} {P Q : R1} (hP : DegLe d1 P) (hQ : DegLe d2 Q) :
    homog (d1 + d2) (P * Q) = homog d1 P * homog d2 Q := by
  conv_lhs => rw [eq_sum_range_of_degLe hP, eq_sum_range_of_degLe hQ]
  rw [sum_mul]
  simp only [mul_sum, homog_sum]
  have hp1 : homog d1 P = ∑ i ∈ range (d1 + 1), homog d1 (Polynomial.C (P.coeff i) * Polynomial.X ^ i) := by
    conv_lhs => rw [eq_sum_range_of_degLe hP, homog_sum]
  have hq1 : homog d2 Q = ∑ j ∈ range (d2 + 1), homog d2 (Polynomial.C (Q.coeff j) * Polynomial.X ^ j) := by
    conv_lhs => rw [eq_sum_range_of_degLe hQ, homog_sum]
  rw [hp1, hq1, sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  have hmul : (Polynomial.C (P.coeff i) * Polynomial.X ^ i) * (Polynomial.C (Q.coeff j) * Polynomial.X ^ j) =
      Polynomial.C (P.coeff i * Q.coeff j) * Polynomial.X ^ (i + j) := by
    rw [map_mul, pow_add]
    ring
  rw [hmul, homog_C_mul_X_pow (d1 + d2) (i + j) (by omega),
    homog_C_mul_X_pow d1 i (by omega), homog_C_mul_X_pow d2 j (by omega)]
  have hexp1 : (1 - Polynomial.X : R1) ^ (i + j) = (1 - Polynomial.X) ^ i * (1 - Polynomial.X) ^ j := pow_add _ i j
  have hexp2 : (1 + Polynomial.X : R1) ^ (d1 + d2 - (i + j)) =
      (1 + Polynomial.X) ^ (d1 - i) * (1 + Polynomial.X) ^ (d2 - j) := by
    rw [← pow_add]
    congr 1
    omega
  rw [map_mul, hexp1, hexp2]
  ring

lemma homog_pow {d : ℕ} (k : ℕ) {P : R1} (hP : DegLe d P) :
    homog (k * d) (P ^ k) = (homog d P) ^ k := by
  induction k with
  | zero =>
    rw [zero_mul, pow_zero, pow_zero, ← Polynomial.C_1, homog_zero_C, Polynomial.C_1]
  | succ k ih =>
    rw [pow_succ, pow_succ, show (k + 1) * d = k * d + d by ring,
      homog_mul (degLe_pow k hP) hP, ih]

lemma homog_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (d : ι → ℕ) (f : ι → R1)
    (hf : ∀ x ∈ s, DegLe (d x) (f x)) :
    homog (∑ x ∈ s, d x) (∏ x ∈ s, f x) = ∏ x ∈ s, homog (d x) (f x) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [sum_empty, prod_empty, prod_empty, ← Polynomial.C_1, homog_zero_C, Polynomial.C_1]
  | @insert x s hx ih =>
    rw [prod_insert hx, prod_insert hx, sum_insert hx,
      homog_mul (hf x (mem_insert_self x s)) (degLe_prod s d f fun y hy => hf y (mem_insert_of_mem hy)),
      ih fun y hy => hf y (mem_insert_of_mem hy)]

def N1 : Matrix Bool Bool R1 := N2.map evalDiag

def N : Matrix Bool Bool R1 :=
  Matrix.of fun a b => if a = b then 2 * (1 + Polynomial.X ^ 2) else 2 * (1 - Polynomial.X ^ 2)

lemma N1_pow_eq_map (j : ℕ) : N1 ^ j = (N2 ^ j).map evalDiag := by
  induction j with
  | zero =>
    ext a b
    cases a <;> cases b <;> simp
  | succ j ih =>
    rw [pow_succ, pow_succ, ih]
    ext a b
    simp [Matrix.mul_apply, N1, N2_apply]
    split_ifs <;> simp

lemma N1_degLe (a b : Bool) : DegLe 2 (N1 a b) := by
  cases a <;> cases b <;> simp [N1, N2_apply]
  · rw [← sq]
    exact degLe_add (degLe_mono (by omega) (degLe_zero_C 1)) (degLe_X_pow 2)
  · intro i hi
    have hne : i ≠ 1 := by omega
    have : ((2 * Polynomial.X : R1).coeff i) = 0 := by
      rw [show (2 * Polynomial.X : R1) = Polynomial.C 2 * Polynomial.X ^ 1 by simp,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne, mul_zero]
    simpa [two_mul] using this
  · intro i hi
    have hne : i ≠ 1 := by omega
    have : ((2 * Polynomial.X : R1).coeff i) = 0 := by
      rw [show (2 * Polynomial.X : R1) = Polynomial.C 2 * Polynomial.X ^ 1 by simp,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne, mul_zero]
    simpa [two_mul] using this
  · rw [← sq]
    exact degLe_add (degLe_mono (by omega) (degLe_zero_C 1)) (degLe_X_pow 2)

lemma homog_N1 (a b : Bool) : homog 2 (N1 a b) = N a b := by
  cases a <;> cases b <;>
    simp [N1, N2_apply, N, homog, Finset.sum_range_succ, Polynomial.coeff_X, Polynomial.coeff_one,
      ← sq] <;> ring

lemma N1_pow_degLe_and_homog (j : ℕ) :
    (∀ a b : Bool, DegLe (2 * j) ((N1 ^ j) a b)) ∧
    (∀ a b : Bool, homog (2 * j) ((N1 ^ j) a b) = (N ^ j) a b) := by
  induction j with
  | zero =>
    constructor
    · intro a b
      cases a <;> cases b
      · intro i hi
        have hne : i ≠ 0 := by omega
        rw [pow_zero]
        simp [Matrix.one_apply, Polynomial.coeff_one, hne]
      · intro i _; simp
      · intro i _; simp
      · intro i hi
        have hne : i ≠ 0 := by omega
        rw [pow_zero]
        simp [Matrix.one_apply, Polynomial.coeff_one, hne]
    · intro a b
      cases a <;> cases b <;> simp [homog, Polynomial.coeff_one]
  | succ j ih =>
    rcases ih with ⟨ihdeg, ihhom⟩
    constructor
    · intro a b
      rw [pow_succ, Matrix.mul_apply, Fintype.sum_bool]
      exact degLe_add
        (degLe_mul (ihdeg a true) (N1_degLe true b))
        (degLe_mul (ihdeg a false) (N1_degLe false b))
    · intro a b
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_bool, Fintype.sum_bool,
        homog_add, show 2 * (j + 1) = 2 * j + 2 by ring,
        homog_mul (ihdeg a true) (N1_degLe true b),
        homog_mul (ihdeg a false) (N1_degLe false b),
        ihhom a true, ihhom a false, homog_N1 true b, homog_N1 false b]

lemma N_pow_formula (j : ℕ) (hj : 1 ≤ j) (a b : Bool) :
    (N ^ j) a b =
      if a = b then (2 : R1) ^ (2 * j - 1) * (1 + Polynomial.X ^ (2 * j))
      else (2 : R1) ^ (2 * j - 1) * (1 - Polynomial.X ^ (2 * j)) := by
  induction j generalizing a b with
  | zero => omega
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · cases a <;> cases b <;> simp [N]
    · have ih' := ih hjpos
      have hpow1 : (2 : R1) ^ (2 * j - 1) * 4 = (2 : R1) ^ (2 * (j + 1) - 1) := by
        have h4 : (4 : R1) = 2 ^ 2 := by norm_num
        have h2j : 2 * j - 1 + 2 = 2 * (j + 1) - 1 := by omega
        rw [h4, ← pow_add, h2j]
      have hpow2 : (Polynomial.X : R1) ^ (2 * j) * Polynomial.X ^ 2 = Polynomial.X ^ (2 * (j + 1)) := by
        rw [← pow_add, show 2 * j + 2 = 2 * (j + 1) by ring]
      rw [pow_succ, Matrix.mul_apply, Fintype.sum_bool]
      rw [ih' a true, ih' a false]
      cases a <;> cases b <;>
        simp only [N, Matrix.of_apply, Bool.false_eq_true, ↓reduceIte, Bool.true_eq_false]
      · calc _ = (2 : R1) ^ (2 * j - 1) * 4 * (1 + Polynomial.X ^ (2 * j) * Polynomial.X ^ 2) := by ring
          _ = _ := by rw [hpow1, hpow2]
      · calc _ = (2 : R1) ^ (2 * j - 1) * 4 * (1 - Polynomial.X ^ (2 * j) * Polynomial.X ^ 2) := by ring
          _ = _ := by rw [hpow1, hpow2]
      · calc _ = (2 : R1) ^ (2 * j - 1) * 4 * (1 - Polynomial.X ^ (2 * j) * Polynomial.X ^ 2) := by ring
          _ = _ := by rw [hpow1, hpow2]
      · calc _ = (2 : R1) ^ (2 * j - 1) * 4 * (1 + Polynomial.X ^ (2 * j) * Polynomial.X ^ 2) := by ring
          _ = _ := by rw [hpow1, hpow2]

end Polynomials

section CycleSum

def cycleSum2 (m : ℕ) (S : Finset (Fin (m + 1))) : R2 :=
  ∑ x : Bool × Fin (m + 1) → Bool,
    if (∀ k ∈ S, x (false, k) = false) then
      varU ^ (Finset.univ.filter (fun k : Fin (m + 1) => x (false, k) ≠ x (true, k))).card *
      varV ^ (Finset.univ.filter (fun k : Fin (m + 1) => x (false, k) ≠ x (true, k + 1))).card
    else 0

lemma cycleSum2_eq_trace (m : ℕ) (S : Finset (Fin (m + 1))) :
    cycleSum2 m S =
      Matrix.trace ((List.finRange (m + 1)).map (fun k => (if k ∈ S then E0 R2 else 1) * N2)).prod := by
  rw [trace_finRange_prod]
  let e : (Bool × Fin (m + 1) → Bool) ≃ (Fin (m + 1) → Bool) × (Fin (m + 1) → Bool) :=
    { toFun := fun x => (fun k => x (false, k), fun k => x (true, k + 1))
      invFun := fun p (b, k) => if b then p.2 (k - 1) else p.1 k
      left_inv := fun x => by
        ext ⟨b, k⟩
        cases b <;> simp
      right_inv := fun ⟨p1, p2⟩ => by
        ext k <;> simp }
  unfold cycleSum2
  rw [← Equiv.sum_comp e.symm]
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro xF _
  have hcond : ∀ xT : Fin (m + 1) → Bool,
      (∀ k ∈ S, e.symm (xF, xT) (false, k) = false) ↔ (∀ k ∈ S, xF k = false) := by
    intro xT
    simp [e]
  have hd1 : ∀ xT : Fin (m + 1) → Bool,
      (Finset.univ.filter (fun k : Fin (m + 1) => e.symm (xF, xT) (false, k) ≠ e.symm (xF, xT) (true, k))).card =
        ∑ k : Fin (m + 1), if xT k ≠ xF (k + 1) then 1 else 0 := by
    intro xT
    rw [Finset.card_filter]
    have hrew := Equiv.sum_comp (Equiv.addRight (1 : Fin (m + 1)))
      (fun k : Fin (m + 1) => if e.symm (xF, xT) (false, k) ≠ e.symm (xF, xT) (true, k) then 1 else 0)
    rw [← hrew]
    apply sum_congr rfl
    intro k _
    simp only [Equiv.coe_addRight, Equiv.coe_fn_symm_mk, e, Bool.false_eq_true, ↓reduceIte, add_sub_cancel_right, ne_comm]
  have hd2 : ∀ xT : Fin (m + 1) → Bool,
      (Finset.univ.filter (fun k : Fin (m + 1) => e.symm (xF, xT) (false, k) ≠ e.symm (xF, xT) (true, k + 1))).card =
        ∑ k : Fin (m + 1), if xF k ≠ xT k then 1 else 0 := by
    intro xT
    rw [Finset.card_filter]
    apply sum_congr rfl
    intro k _
    simp [e]
  have hinner : (∑ xT : Fin (m + 1) → Bool,
      if (∀ k ∈ S, e.symm (xF, xT) (false, k) = false) then
        varU ^ (Finset.univ.filter (fun k : Fin (m + 1) => e.symm (xF, xT) (false, k) ≠ e.symm (xF, xT) (true, k))).card *
        varV ^ (Finset.univ.filter (fun k : Fin (m + 1) => e.symm (xF, xT) (false, k) ≠ e.symm (xF, xT) (true, k + 1))).card
      else 0) =
      (if (∀ k ∈ S, xF k = false) then 1 else 0) * ∏ k : Fin (m + 1), N2 (xF k) (xF (k + 1)) := by
    by_cases hp : ∀ k ∈ S, xF k = false
    · rw [if_pos hp, one_mul]
      have hterm : ∀ xT : Fin (m + 1) → Bool,
          (if (∀ k ∈ S, e.symm (xF, xT) (false, k) = false) then
            varU ^ (Finset.univ.filter (fun k : Fin (m + 1) => e.symm (xF, xT) (false, k) ≠ e.symm (xF, xT) (true, k))).card *
            varV ^ (Finset.univ.filter (fun k : Fin (m + 1) => e.symm (xF, xT) (false, k) ≠ e.symm (xF, xT) (true, k + 1))).card
          else 0) =
            ∏ k : Fin (m + 1), (varU ^ (if xT k ≠ xF (k + 1) then 1 else 0) * varV ^ (if xF k ≠ xT k then 1 else 0)) := by
        intro xT
        rw [if_pos ((hcond xT).mpr hp), hd1 xT, hd2 xT, ← Finset.prod_pow_eq_pow_sum,
          ← Finset.prod_pow_eq_pow_sum, prod_mul_distrib]
      simp_rw [hterm]
      rw [← Fintype.prod_sum (fun k b => varU ^ (if b ≠ xF (k + 1) then 1 else 0) * varV ^ (if xF k ≠ b then 1 else 0))]
      apply prod_congr rfl
      intro k _
      exact sum_bool_UV (xF k) (xF (k + 1))
    · rw [if_neg hp, zero_mul]
      apply sum_eq_zero
      intro xT _
      rw [if_neg (fun h => hp ((hcond xT).mp h))]
  rw [hinner]
  by_cases hp : ∀ k ∈ S, xF k = false
  · rw [if_pos hp, one_mul]
    apply prod_congr rfl
    intro k _
    by_cases hk : k ∈ S
    · rw [if_pos hk, E0_mul_apply, if_pos (hp k hk), hp k hk]
    · rw [if_neg hk, Matrix.one_mul]
  · rw [if_neg hp, zero_mul]
    push_neg at hp
    rcases hp with ⟨k0, hk0, hfk0⟩
    symm
    apply prod_eq_zero (mem_univ k0)
    rw [if_pos hk0, E0_mul_apply, if_neg hfk0]

lemma cycleSum2_empty (m : ℕ) :
    cycleSum2 m ∅ = 2 * (N2 ^ (m + 1)) false false := by
  rw [cycleSum2_eq_trace]
  have hmap : (List.finRange (m + 1)).map (fun k : Fin (m + 1) => (if k ∈ (∅ : Finset (Fin (m + 1))) then E0 R2 else 1) * N2) =
      List.replicate (m + 1) N2 := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp
  rw [hmap, List.prod_replicate, Matrix.trace]
  simp only [Matrix.diag_apply, Fintype.sum_bool]
  have hdiag : ∀ k : ℕ, (N2 ^ k) true true = (N2 ^ k) false false := by
    intro k
    have hconj : ∀ a b : Bool, (N2 ^ k) (!a) (!b) = (N2 ^ k) a b := by
      induction k with
      | zero =>
        intro a b
        cases a <;> cases b <;> simp [Matrix.one_apply]
      | succ k ih =>
        intro a b
        rw [pow_succ, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_bool, Fintype.sum_bool]
        have h1 : N2 true (!b) = N2 false b := by cases b <;> simp [N2_apply]
        have h2 : N2 false (!b) = N2 true b := by cases b <;> simp [N2_apply]
        have ihF := ih a false
        have ihT := ih a true
        simp only [Bool.not_true, Bool.not_false] at ihF ihT
        rw [ihF, ihT, h1, h2]
        ring
    exact hconj false false
  rw [hdiag (m + 1)]
  ring

def gapsOfPins (m : ℕ) (S : Finset (Fin (m + 1))) (hS : S.Nonempty) : List ℕ :=
  let k0 := S.min' hS
  let bs := ((List.finRange (m + 1)).rotate k0.val).tail.map (fun k => decide (k ∈ S))
  collectGaps 1 bs

lemma gapsOfPins_pos (m : ℕ) (S : Finset (Fin (m + 1))) (hS : S.Nonempty) :
    ∀ g ∈ gapsOfPins m S hS, 1 ≤ g :=
  collectGaps_pos 1 (by omega) _

lemma gapsOfPins_sum (m : ℕ) (S : Finset (Fin (m + 1))) (hS : S.Nonempty) :
    (gapsOfPins m S hS).sum = m + 1 := by
  unfold gapsOfPins
  rw [collectGaps_sum]
  simp only [List.length_map, List.length_tail, List.length_rotate, List.length_finRange]
  omega

lemma gapsOfPins_nonempty (m : ℕ) (S : Finset (Fin (m + 1))) (hS : S.Nonempty) :
    gapsOfPins m S hS ≠ [] := by
  intro h
  have hs := gapsOfPins_sum m S hS
  rw [h] at hs
  simp at hs

lemma cycleSum2_nonempty (m : ℕ) (S : Finset (Fin (m + 1))) (hS : S.Nonempty) :
    cycleSum2 m S = ((gapsOfPins m S hS).map (fun g => (N2 ^ g) false false)).prod := by
  rw [cycleSum2_eq_trace]
  let k0 := S.min' hS
  let f : Fin (m + 1) → Matrix Bool Bool R2 := fun k => (if k ∈ S then E0 R2 else 1) * N2
  have hrot : Matrix.trace ((List.finRange (m + 1)).map f).prod =
      Matrix.trace (((List.finRange (m + 1)).rotate k0.val).map f).prod := by
    rw [List.map_rotate, trace_list_rotate]
  rw [hrot]
  have hhead : ((List.finRange (m + 1)).rotate k0.val).head? = some k0 := by
    rw [List.head?_eq_getElem?]
    have hlen : 0 < ((List.finRange (m + 1)).rotate k0.val).length := by simp
    rw [List.getElem?_eq_getElem hlen, List.getElem_rotate]
    simp [Nat.mod_eq_of_lt k0.isLt]
  rcases hcons : (List.finRange (m + 1)).rotate k0.val with _ | ⟨hd, tl⟩
  · rw [hcons] at hhead; simp at hhead
  · rw [hcons] at hhead
    simp only [List.head?_cons, Option.some.injEq] at hhead
    rw [hhead]
    have hmem : k0 ∈ S := S.min'_mem hS
    simp only [List.map_cons, List.prod_cons, f, if_pos hmem]
    have htl : tl.map (fun k => (if k ∈ S then E0 R2 else 1) * N2) =
        (tl.map (fun k => decide (k ∈ S))).map (fun b => if b then E0 R2 * N2 else N2) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro k _
      by_cases hk : k ∈ S <;> simp [hk]
    rw [htl]
    have hassoc : E0 R2 * N2 * ((tl.map (fun k => decide (k ∈ S))).map (fun b => if b then E0 R2 * N2 else N2)).prod =
        E0 R2 * N2 ^ 1 * ((tl.map (fun k => decide (k ∈ S))).map (fun b => if b then E0 R2 * N2 else N2)).prod := by
      simp [pow_one]
    rw [hassoc, trace_collectGaps]
    rw [gapsOfPins, hcons, List.tail_cons]

end CycleSum

section GlobalGenerating

def histFn (c : ℕ) (L : Fin c → ℕ)
    (pins : Finset ((i : Fin c) × Fin (L i + 1)))
    (d : Fin (∑ i : Fin c, (L i + 1) + 1) × Fin (∑ i : Fin c, (L i + 1) + 1)) : ℕ :=
  ((Finset.univ : Finset (Bool × ((i : Fin c) × Fin (L i + 1)) → Bool)).filter (fun x =>
    (∀ i ∈ pins, x (false, i) = false) ∧
    (Finset.univ.filter (fun i : (i : Fin c) × Fin (L i + 1) => x (false, i) ≠ x (true, i))).card = d.1.val ∧
    (Finset.univ.filter (fun i : (i : Fin c) × Fin (L i + 1) => x (false, i) ≠
      x (true, (⟨i.1, i.2 + 1⟩ : (i : Fin c) × Fin (L i + 1))))).card = d.2.val)).card

def partsFn (c : ℕ) (L : Fin c → ℕ) :
    Finset (Fin (∑ i : Fin c, (L i + 1) + 1) → Fin (∑ i : Fin c, (L i + 1) + 1)) :=
  (Finset.univ : Finset (Fin (∑ i : Fin c, (L i + 1) + 1) → Fin (∑ i : Fin c, (L i + 1) + 1))).filter
    (fun p => (p 0).val = 0 ∧
      ∃ alloc : Fin c → (Fin (∑ i : Fin c, (L i + 1) + 1) → Fin (∑ i : Fin c, (L i + 1) + 1)),
        (∀ i, (∑ j : Fin (∑ i : Fin c, (L i + 1) + 1), j.val * (alloc i j).val) = L i + 1) ∧
        ∀ j, (∑ i : Fin c, (alloc i j).val) = (p j).val)

def histGen2 (c : ℕ) (L : Fin c → ℕ)
    (pins : Finset ((i : Fin c) × Fin (L i + 1))) : R2 :=
  ∑ d : Fin (∑ i : Fin c, (L i + 1) + 1) × Fin (∑ i : Fin c, (L i + 1) + 1),
    (histFn c L pins d : ℤ) • (varU ^ d.1.val * varV ^ d.2.val)

lemma histGen2_coeff (c : ℕ) (L : Fin c → ℕ)
    (pins : Finset ((i : Fin c) × Fin (L i + 1)))
    (d : Fin (∑ i : Fin c, (L i + 1) + 1) × Fin (∑ i : Fin c, (L i + 1) + 1)) :
    ((histGen2 c L pins).coeff d.1.val).coeff d.2.val = (histFn c L pins d : ℤ) := by
  unfold histGen2
  rw [Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  rw [sum_eq_single d]
  · have hterm : (varU ^ d.1.val * varV ^ d.2.val : R2) =
        Polynomial.C (Polynomial.X ^ d.2.val) * Polynomial.X ^ d.1.val := by
      simp only [varU, varV, ← Polynomial.C_pow]
      ring
    rw [zsmul_eq_mul, Int.cast_natCast, hterm, ← mul_assoc, ← Polynomial.C_eq_natCast,
      ← map_mul, Polynomial.coeff_C_mul_X_pow]
    simp
  · intro d' _ hne
    have hterm : (varU ^ d'.1.val * varV ^ d'.2.val : R2) =
        Polynomial.C (Polynomial.X ^ d'.2.val) * Polynomial.X ^ d'.1.val := by
      simp only [varU, varV, ← Polynomial.C_pow]
      ring
    rw [zsmul_eq_mul, Int.cast_natCast, hterm, ← mul_assoc, ← Polynomial.C_eq_natCast,
      ← map_mul, Polynomial.coeff_C_mul_X_pow]
    by_cases h1 : d.1.val = d'.1.val
    · have h2 : d.2.val ≠ d'.2.val := fun h2 => hne (Prod.ext (Fin.ext h1) (Fin.ext h2)).symm
      rw [← h1, if_pos rfl]
      simp [h2]
    · rw [if_neg h1]
      simp
  · intro hd
    exfalso
    exact hd (mem_univ d)

def pinSlice {c : ℕ} {L : Fin c → ℕ}
    (pins : Finset ((i : Fin c) × Fin (L i + 1))) (i : Fin c) : Finset (Fin (L i + 1)) :=
  Finset.univ.filter (fun k => (⟨i, k⟩ : (i : Fin c) × Fin (L i + 1)) ∈ pins)

lemma card_sigma_eq (c : ℕ) (L : Fin c → ℕ) :
    Fintype.card ((i : Fin c) × Fin (L i + 1)) = ∑ i : Fin c, (L i + 1) := by
  simp [Fintype.card_sigma]

lemma histGen2_eq_prod (c : ℕ) (L : Fin c → ℕ)
    (pins : Finset ((i : Fin c) × Fin (L i + 1))) :
    histGen2 c L pins = ∏ i : Fin c, cycleSum2 (L i) (pinSlice pins i) := by
  let n := ∑ i : Fin c, (L i + 1)
  let I := (i : Fin c) × Fin (L i + 1)
  let V := Bool × I
  let J := Fin (n + 1)
  have hcardI : Fintype.card I = n := card_sigma_eq c L
  let d1 : (V → Bool) → ℕ := fun x => (Finset.univ.filter (fun i : I => x (false, i) ≠ x (true, i))).card
  let d2 : (V → Bool) → ℕ := fun x => (Finset.univ.filter (fun i : I => x (false, i) ≠ x (true, ⟨i.1, i.2 + 1⟩))).card
  have hd1_le : ∀ x, d1 x < n + 1 := fun x => by
    have hle := card_filter_le (Finset.univ : Finset I) (fun i : I => x (false, i) ≠ x (true, i))
    rw [card_univ, hcardI] at hle
    change d1 x ≤ n at hle
    omega
  have hd2_le : ∀ x, d2 x < n + 1 := fun x => by
    have hle := card_filter_le (Finset.univ : Finset I) (fun i : I => x (false, i) ≠ x (true, ⟨i.1, i.2 + 1⟩))
    rw [card_univ, hcardI] at hle
    change d2 x ≤ n at hle
    omega
  have hsum_x : histGen2 c L pins =
      ∑ x : V → Bool, if (∀ i ∈ pins, x (false, i) = false) then varU ^ d1 x * varV ^ d2 x else 0 := by
    unfold histGen2 histFn
    have hexpand : ∀ d : J × J,
        (((Finset.univ : Finset (V → Bool)).filter (fun x =>
          (∀ i ∈ pins, x (false, i) = false) ∧ d1 x = d.1.val ∧ d2 x = d.2.val)).card : ℤ) •
          (varU ^ d.1.val * varV ^ d.2.val) =
        ∑ x ∈ (Finset.univ : Finset (V → Bool)).filter (fun x =>
          (∀ i ∈ pins, x (false, i) = false) ∧ d1 x = d.1.val ∧ d2 x = d.2.val),
          (varU ^ d1 x * varV ^ d2 x) := by
      intro d
      rw [zsmul_eq_mul, Finset.card_eq_sum_ones, Nat.cast_sum, Int.cast_sum, sum_mul]
      apply sum_congr rfl
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      rw [hx.2.1, hx.2.2, Nat.cast_one, Int.cast_one, one_mul]
    change ∑ d : J × J,
      (((Finset.univ : Finset (V → Bool)).filter (fun x =>
        (∀ i ∈ pins, x (false, i) = false) ∧ d1 x = d.1.val ∧ d2 x = d.2.val)).card : ℤ) •
        (varU ^ d.1.val * varV ^ d.2.val) = _
    simp_rw [hexpand]
    rw [← sum_fiberwise (Finset.univ : Finset (V → Bool))
      (fun x : V → Bool => ((⟨d1 x, hd1_le x⟩, ⟨d2 x, hd2_le x⟩) : J × J))
      (fun x => if (∀ i ∈ pins, x (false, i) = false) then varU ^ d1 x * varV ^ d2 x else 0)]
    apply sum_congr rfl
    intro d _
    have hsplit : (Finset.univ : Finset (V → Bool)).filter
        (fun x => (⟨d1 x, hd1_le x⟩, ⟨d2 x, hd2_le x⟩) = d) =
        ((Finset.univ : Finset (V → Bool)).filter (fun x =>
          (∀ i ∈ pins, x (false, i) = false) ∧ d1 x = d.1.val ∧ d2 x = d.2.val)) ∪
        ((Finset.univ : Finset (V → Bool)).filter (fun x =>
          ¬(∀ i ∈ pins, x (false, i) = false) ∧ d1 x = d.1.val ∧ d2 x = d.2.val)) := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_union, Prod.ext_iff]
      rw [show (⟨d1 x, hd1_le x⟩ = d.1) ↔ d1 x = d.1.val from Fin.ext_iff,
        show (⟨d2 x, hd2_le x⟩ = d.2) ↔ d2 x = d.2.val from Fin.ext_iff]
      tauto
    rw [hsplit, sum_union]
    · have hzero : ∑ x ∈ (Finset.univ : Finset (V → Bool)).filter (fun x =>
          ¬(∀ i ∈ pins, x (false, i) = false) ∧ d1 x = d.1.val ∧ d2 x = d.2.val),
          (if (∀ i ∈ pins, x (false, i) = false) then varU ^ d1 x * varV ^ d2 x else 0) = 0 := by
        apply sum_eq_zero
        intro x hx
        simp only [mem_filter, mem_univ, true_and] at hx
        rw [if_neg hx.1]
      rw [hzero, add_zero]
      apply sum_congr rfl
      intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      rw [if_pos hx.1]
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [mem_filter, mem_univ, true_and] at hx1 hx2
      exact hx2.1 hx1.1
  rw [hsum_x]
  let equivSplit : (V → Bool) ≃ (∀ i : Fin c, Bool × Fin (L i + 1) → Bool) :=
    { toFun := fun x i (b, k) => x (b, ⟨i, k⟩)
      invFun := fun f (b, p) => f p.1 (b, p.2)
      left_inv := fun x => by ext ⟨b, ⟨i, k⟩⟩; rfl
      right_inv := fun f => by ext i ⟨b, k⟩; rfl }
  rw [← Equiv.sum_comp equivSplit.symm]
  have hprod : (∑ f : ∀ i : Fin c, Bool × Fin (L i + 1) → Bool,
      if (∀ p ∈ pins, equivSplit.symm f (false, p) = false) then
        varU ^ d1 (equivSplit.symm f) * varV ^ d2 (equivSplit.symm f)
      else 0) =
      ∑ f : ∀ i : Fin c, Bool × Fin (L i + 1) → Bool, ∏ i : Fin c,
        (if (∀ k ∈ pinSlice pins i, f i (false, k) = false) then
          varU ^ (Finset.univ.filter (fun k : Fin (L i + 1) => f i (false, k) ≠ f i (true, k))).card *
          varV ^ (Finset.univ.filter (fun k : Fin (L i + 1) => f i (false, k) ≠ f i (true, k + 1))).card
        else 0) := by
    apply sum_congr rfl
    intro f _
    have hpin : (∀ p ∈ pins, equivSplit.symm f (false, p) = false) ↔
        ∀ i : Fin c, ∀ k ∈ pinSlice pins i, f i (false, k) = false := by
      simp only [pinSlice, mem_filter, mem_univ, true_and, equivSplit, Equiv.coe_fn_symm_mk]
      constructor
      · intro h i k hk; exact h ⟨i, k⟩ hk
      · intro h ⟨i, k⟩ hk; exact h i k hk
    have hd1f : d1 (equivSplit.symm f) =
        ∑ i : Fin c, (Finset.univ.filter (fun k : Fin (L i + 1) => f i (false, k) ≠ f i (true, k))).card := by
      simp only [d1, Finset.card_filter]
      change (∑ p : (i : Fin c) × Fin (L i + 1), _) = _
      rw [Fintype.sum_sigma]
      rfl
    have hd2f : d2 (equivSplit.symm f) =
        ∑ i : Fin c, (Finset.univ.filter (fun k : Fin (L i + 1) => f i (false, k) ≠ f i (true, k + 1))).card := by
      simp only [d2, Finset.card_filter]
      change (∑ p : (i : Fin c) × Fin (L i + 1), _) = _
      rw [Fintype.sum_sigma]
      rfl
    by_cases hp : ∀ i : Fin c, ∀ k ∈ pinSlice pins i, f i (false, k) = false
    · rw [if_pos (hpin.mpr hp), hd1f, hd2f, ← Finset.prod_pow_eq_pow_sum,
        ← Finset.prod_pow_eq_pow_sum, ← prod_mul_distrib]
      apply prod_congr rfl
      intro i _
      rw [if_pos (hp i)]
    · rw [if_neg (fun h => hp (hpin.mp h))]
      push_neg at hp
      rcases hp with ⟨i0, k0, hk0, hfk0⟩
      symm
      apply prod_eq_zero (mem_univ i0)
      simp only [ite_eq_right_iff]
      intro hi0
      exact absurd (hi0 k0 hk0) hfk0
  rw [hprod]
  symm
  unfold cycleSum2
  exact Fintype.prod_sum (fun (i : Fin c) (x : Bool × Fin (L i + 1) → Bool) =>
    if (∀ k ∈ pinSlice pins i, x (false, k) = false) then
      varU ^ (Finset.univ.filter (fun k : Fin (L i + 1) => x (false, k) ≠ x (true, k))).card *
      varV ^ (Finset.univ.filter (fun k : Fin (L i + 1) => x (false, k) ≠ x (true, k + 1))).card
    else 0)

def gapsOfComp (c : ℕ) (L : Fin c → ℕ) (pins : Finset ((i : Fin c) × Fin (L i + 1))) (i : Fin c) : List ℕ :=
  if h : (pinSlice pins i).Nonempty then gapsOfPins (L i) (pinSlice pins i) h else [L i + 1]

def uOfComp (c : ℕ) (L : Fin c → ℕ) (pins : Finset ((i : Fin c) × Fin (L i + 1))) (i : Fin c) : ℕ :=
  if (pinSlice pins i).Nonempty then 0 else 1

lemma gapsOfComp_pos (c : ℕ) (L : Fin c → ℕ) (pins : Finset ((i : Fin c) × Fin (L i + 1))) (i : Fin c) :
    ∀ g ∈ gapsOfComp c L pins i, 1 ≤ g := by
  unfold gapsOfComp
  split_ifs with h
  · exact gapsOfPins_pos (L i) (pinSlice pins i) h
  · intro g hg
    simp at hg
    omega

lemma gapsOfComp_sum (c : ℕ) (L : Fin c → ℕ) (pins : Finset ((i : Fin c) × Fin (L i + 1))) (i : Fin c) :
    (gapsOfComp c L pins i).sum = L i + 1 := by
  unfold gapsOfComp
  split_ifs with h
  · exact gapsOfPins_sum (L i) (pinSlice pins i) h
  · simp

lemma list_sum_count_mul {m : ℕ} (gs : List ℕ) (hgs : ∀ g ∈ gs, g ≤ m) :
    ∑ j : Fin (m + 1), j.val * gs.count j.val = gs.sum := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg : g ≤ m := hgs g (by simp)
    have hgs' : ∀ x ∈ gs, x ≤ m := fun x hx => hgs x (by simp [hx])
    simp only [List.count_cons, List.sum_cons, mul_add, sum_add_distrib, ih hgs']
    rw [add_comm g gs.sum]
    congr 1
    let j0 : Fin (m + 1) := ⟨g, by omega⟩
    rw [sum_eq_single j0]
    · simp [j0]
    · intro j _ hj
      have hne : g ≠ j.val := fun h => hj (Fin.ext h.symm)
      simp [beq_iff_eq, hne]
    · intro h
      exfalso
      exact h (mem_univ j0)

lemma list_prod_map_count {α : Type*} [CommMonoid α] {m : ℕ} (gs : List ℕ) (f : ℕ → α)
    (hgs : ∀ g ∈ gs, g ≤ m) :
    (gs.map f).prod = ∏ j : Fin (m + 1), (f j.val) ^ (gs.count j.val) := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg : g ≤ m := hgs g (by simp)
    have hgs' : ∀ x ∈ gs, x ≤ m := fun x hx => hgs x (by simp [hx])
    simp only [List.map_cons, List.prod_cons, List.count_cons, pow_add, prod_mul_distrib, ih hgs']
    rw [mul_comm (f g)]
    congr 1
    let j0 : Fin (m + 1) := ⟨g, by omega⟩
    rw [prod_eq_single j0]
    · simp [j0]
    · intro j _ hj
      have hne : g ≠ j.val := fun h => hj (Fin.ext h.symm)
      simp [beq_iff_eq, hne]
    · intro h
      exfalso
      exact h (mem_univ j0)

lemma list_elem_le_sum (gs : List ℕ) (g : ℕ) (hg : g ∈ gs) : g ≤ gs.sum := by
  induction gs with
  | nil => simp at hg
  | cons x xs ih =>
    simp at hg
    rcases hg with rfl | hg
    · simp
    · exact le_trans (ih hg) (by simp)

lemma count_le_sum (gs : List ℕ) (hgs : ∀ g ∈ gs, 1 ≤ g) (x : ℕ) : gs.count x ≤ gs.sum := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg : 1 ≤ g := hgs g (by simp)
    have hgs' : ∀ y ∈ gs, 1 ≤ y := fun y hy => hgs y (by simp [hy])
    have ih' := ih hgs'
    simp only [List.count_cons, List.sum_cons]
    split_ifs <;> omega

end GlobalGenerating

section MainProof

def partOfPins (c : ℕ) (L : Fin c → ℕ)
    (pins : Finset ((i : Fin c) × Fin (L i + 1))) :
    Fin (∑ i : Fin c, (L i + 1) + 1) → Fin (∑ i : Fin c, (L i + 1) + 1) :=
  fun j => ⟨∑ i : Fin c, (gapsOfComp c L pins i).count j.val, by
    have hle : ∀ i : Fin c, (gapsOfComp c L pins i).count j.val ≤ L i + 1 := fun i => by
      calc (gapsOfComp c L pins i).count j.val
          ≤ (gapsOfComp c L pins i).sum := count_le_sum _ (gapsOfComp_pos c L pins i) j.val
        _ = L i + 1 := gapsOfComp_sum c L pins i
    have hsum : ∑ i : Fin c, (gapsOfComp c L pins i).count j.val ≤ ∑ i : Fin c, (L i + 1) :=
      Finset.sum_le_sum (fun i _ => hle i)
    omega⟩

def uOfPins (c : ℕ) (L : Fin c → ℕ)
    (pins : Finset ((i : Fin c) × Fin (L i + 1))) : ℕ :=
  ∑ i : Fin c, uOfComp c L pins i

def maxU (c : ℕ) (L : Fin c → ℕ)
    (p : Fin (∑ i : Fin c, (L i + 1) + 1) → Fin (∑ i : Fin c, (L i + 1) + 1)) : ℕ :=
  ∑ j : Fin (∑ i : Fin c, (L i + 1) + 1),
    min (p j).val ((Finset.univ : Finset (Fin c)).filter (fun i => L i + 1 = j.val)).card

lemma gapsOfComp_le_n (c : ℕ) (L : Fin c → ℕ)
    (pins : Finset ((i : Fin c) × Fin (L i + 1))) (i : Fin c) :
    ∀ g ∈ gapsOfComp c L pins i, g ≤ ∑ k : Fin c, (L k + 1) := by
  intro g hg
  calc g ≤ (gapsOfComp c L pins i).sum := list_elem_le_sum _ g hg
    _ = L i + 1 := gapsOfComp_sum c L pins i
    _ ≤ ∑ k : Fin c, (L k + 1) := Finset.single_le_sum (fun k _ => Nat.zero_le (L k + 1)) (mem_univ i)

lemma cycleSum2_eq_gapsOfComp (c : ℕ) (L : Fin c → ℕ)
    (pins : Finset ((i : Fin c) × Fin (L i + 1))) (i : Fin c) :
    cycleSum2 (L i) (pinSlice pins i) =
      (2 : R2) ^ (uOfComp c L pins i) *
        ((gapsOfComp c L pins i).map (fun g => (N2 ^ g) false false)).prod := by
  unfold gapsOfComp uOfComp
  split_ifs with h
  · rw [pow_zero, one_mul]
    exact cycleSum2_nonempty (L i) (pinSlice pins i) h
  · rw [Finset.not_nonempty_iff_eq_empty.mp h, cycleSum2_empty]
    simp

lemma histGen2_eq_prod_part (c : ℕ) (L : Fin c → ℕ)
    (pins : Finset ((i : Fin c) × Fin (L i + 1))) :
    histGen2 c L pins =
      (2 : R2) ^ uOfPins c L pins *
        ∏ j : Fin (∑ i : Fin c, (L i + 1) + 1), ((N2 ^ j.val) false false) ^ (partOfPins c L pins j).val := by
  rw [histGen2_eq_prod]
  simp_rw [cycleSum2_eq_gapsOfComp]
  have hmap : ∀ i : Fin c,
      ((gapsOfComp c L pins i).map (fun g => (N2 ^ g) false false)).prod =
        ∏ j : Fin (∑ k : Fin c, (L k + 1) + 1), ((N2 ^ j.val) false false) ^ ((gapsOfComp c L pins i).count j.val) :=
    fun i => list_prod_map_count (gapsOfComp c L pins i) (fun g => (N2 ^ g) false false) (gapsOfComp_le_n c L pins i)
  simp_rw [hmap, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Finset.prod_comm]
  apply prod_congr rfl
  intro j _
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

lemma partOfPins_zero (c : ℕ) (L : Fin c → ℕ)
    (pins : Finset ((i : Fin c) × Fin (L i + 1))) :
    (partOfPins c L pins 0).val = 0 := by
  unfold partOfPins
  simp only [Fin.val_zero]
  apply sum_eq_zero
  intro i _
  rw [List.count_eq_zero]
  intro h0
  have h1 := gapsOfComp_pos c L pins i 0 h0
  omega

lemma partOfPins_mem_partsFn (c : ℕ) (L : Fin c → ℕ)
    (pins : Finset ((i : Fin c) × Fin (L i + 1))) :
    partOfPins c L pins ∈ partsFn c L := by
  unfold partsFn
  simp only [mem_filter, mem_univ, true_and]
  refine ⟨partOfPins_zero c L pins, ?_⟩
  refine ⟨fun i j => ⟨(gapsOfComp c L pins i).count j.val, by
    have h1 : (gapsOfComp c L pins i).count j.val ≤ (gapsOfComp c L pins i).sum :=
      count_le_sum _ (gapsOfComp_pos c L pins i) j.val
    rw [gapsOfComp_sum] at h1
    have h2 : L i + 1 ≤ ∑ k : Fin c, (L k + 1) :=
      Finset.single_le_sum (f := fun k => L k + 1) (fun k _ => Nat.zero_le _) (mem_univ i)
    omega⟩, ?_, ?_⟩
  · intro i
    simp only
    rw [list_sum_count_mul (gapsOfComp c L pins i) (gapsOfComp_le_n c L pins i), gapsOfComp_sum]
  · intro j
    rfl

lemma partOfPins_sum_mul (c : ℕ) (L : Fin c → ℕ)
    (pins : Finset ((i : Fin c) × Fin (L i + 1))) :
    ∑ j : Fin (∑ i : Fin c, (L i + 1) + 1), j.val * (partOfPins c L pins j).val = ∑ i : Fin c, (L i + 1) := by
  simp only [partOfPins, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro i _
  rw [list_sum_count_mul (gapsOfComp c L pins i) (gapsOfComp_le_n c L pins i), gapsOfComp_sum]

lemma uOfPins_le_maxU (c : ℕ) (L : Fin c → ℕ)
    (pins : Finset ((i : Fin c) × Fin (L i + 1))) :
    uOfPins c L pins ≤ maxU c L (partOfPins c L pins) := by
  let n := ∑ i : Fin c, (L i + 1)
  let J := Fin (n + 1)
  let jOf : Fin c → J := fun i => ⟨L i + 1, by
    have h : L i + 1 ≤ n :=
      Finset.single_le_sum (f := fun k => L k + 1) (fun k _ => Nat.zero_le _) (mem_univ i)
    omega⟩
  unfold uOfPins maxU
  rw [← sum_fiberwise (Finset.univ : Finset (Fin c)) jOf (fun i => uOfComp c L pins i)]
  apply Finset.sum_le_sum
  intro j _
  apply le_min
  · calc ∑ i ∈ (Finset.univ : Finset (Fin c)).filter (fun i => jOf i = j), uOfComp c L pins i
        ≤ ∑ i ∈ (Finset.univ : Finset (Fin c)).filter (fun i => jOf i = j), (gapsOfComp c L pins i).count j.val := by
          apply Finset.sum_le_sum
          intro i hi
          simp only [mem_filter, mem_univ, true_and] at hi
          unfold uOfComp gapsOfComp
          split_ifs with h
          · exact Nat.zero_le _
          · have hval : L i + 1 = j.val := congrArg Fin.val hi
            simp [hval]
      _ ≤ ∑ i : Fin c, (gapsOfComp c L pins i).count j.val :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = (partOfPins c L pins j).val := rfl
  · calc ∑ i ∈ (Finset.univ : Finset (Fin c)).filter (fun i => jOf i = j), uOfComp c L pins i
        ≤ ∑ _i ∈ (Finset.univ : Finset (Fin c)).filter (fun i => jOf i = j), 1 := by
          apply Finset.sum_le_sum
          intro i _
          unfold uOfComp
          split_ifs <;> omega
      _ = ((Finset.univ : Finset (Fin c)).filter (fun i => L i + 1 = j.val)).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_one]
          refine congrArg Finset.card (by ext i; simp only [mem_filter, mem_univ, true_and, jOf]; exact Fin.ext_iff)

def polyQ (n : ℕ) (p : Fin (n + 1) → Fin (n + 1)) : R1 :=
  ∏ j : Fin (n + 1), if 0 < j.val then (1 + Polynomial.X ^ (2 * j.val)) ^ (p j).val else 1

def expTwo (n : ℕ) (u : ℕ) (p : Fin (n + 1) → Fin (n + 1)) : ℕ :=
  u + ∑ j : Fin (n + 1), if 0 < j.val then (2 * j.val - 1) * (p j).val else 0

lemma homog_evalDiag_histGen2 (c : ℕ) (L : Fin c → ℕ)
    (pins : Finset ((i : Fin c) × Fin (L i + 1))) :
    homog (2 * ∑ i : Fin c, (L i + 1)) (evalDiag (histGen2 c L pins)) =
      Polynomial.C ((2 : ℤ) ^ expTwo (∑ i : Fin c, (L i + 1)) (uOfPins c L pins) (partOfPins c L pins)) *
        polyQ (∑ i : Fin c, (L i + 1)) (partOfPins c L pins) := by
  let n := ∑ i : Fin c, (L i + 1)
  let p := partOfPins c L pins
  let u := uOfPins c L pins
  have heval : evalDiag (histGen2 c L pins) =
      (2 : R1) ^ u * ∏ j : Fin (n + 1), ((N1 ^ j.val) false false) ^ (p j).val := by
    rw [histGen2_eq_prod_part, map_mul, map_pow, map_prod]
    have h2 : evalDiag (2 : R2) = (2 : R1) := map_ofNat evalDiag 2
    rw [h2]
    congr 1
    apply prod_congr rfl
    intro j _
    rw [map_pow, N1_pow_eq_map, Matrix.map_apply]
  have hdeg_prod : DegLe (2 * n) (∏ j : Fin (n + 1), ((N1 ^ j.val) false false) ^ (p j).val) := by
    have h1 := degLe_prod (Finset.univ : Finset (Fin (n + 1)))
      (fun j => (p j).val * (2 * j.val))
      (fun j => ((N1 ^ j.val) false false) ^ (p j).val)
      (fun j _ => degLe_pow (p j).val ((N1_pow_degLe_and_homog j.val).1 false false))
    have hsum : ∑ j : Fin (n + 1), (p j).val * (2 * j.val) = 2 * n := by
      calc ∑ j : Fin (n + 1), (p j).val * (2 * j.val)
          = 2 * ∑ j : Fin (n + 1), j.val * (p j).val := by
            rw [Finset.mul_sum]
            apply sum_congr rfl
            intro j _
            ring
        _ = 2 * n := by rw [partOfPins_sum_mul]
    rw [hsum] at h1
    exact h1
  have h2u : (2 : R1) ^ u = Polynomial.C ((2 : ℤ) ^ u) := by
    rw [map_pow, map_ofNat]
  rw [heval, h2u, show 2 * n = 0 + 2 * n by omega, homog_mul (degLe_zero_C _) hdeg_prod, homog_zero_C]
  have hhom_prod : homog (2 * n) (∏ j : Fin (n + 1), ((N1 ^ j.val) false false) ^ (p j).val) =
      ∏ j : Fin (n + 1), ((N ^ j.val) false false) ^ (p j).val := by
    have h1 := homog_prod (Finset.univ : Finset (Fin (n + 1)))
      (fun j => (p j).val * (2 * j.val))
      (fun j => ((N1 ^ j.val) false false) ^ (p j).val)
      (fun j _ => degLe_pow (p j).val ((N1_pow_degLe_and_homog j.val).1 false false))
    have hsum : ∑ j : Fin (n + 1), (p j).val * (2 * j.val) = 2 * n := by
      calc ∑ j : Fin (n + 1), (p j).val * (2 * j.val)
          = 2 * ∑ j : Fin (n + 1), j.val * (p j).val := by
            rw [Finset.mul_sum]
            apply sum_congr rfl
            intro j _
            ring
        _ = 2 * n := by rw [partOfPins_sum_mul]
    rw [hsum] at h1
    rw [h1]
    apply prod_congr rfl
    intro j _
    rw [homog_pow (p j).val ((N1_pow_degLe_and_homog j.val).1 false false),
      (N1_pow_degLe_and_homog j.val).2 false false]
  rw [hhom_prod]
  have hfactor : ∀ j : Fin (n + 1),
      ((N ^ j.val) false false) ^ (p j).val =
        (2 : R1) ^ (if 0 < j.val then (2 * j.val - 1) * (p j).val else 0) *
        (if 0 < j.val then (1 + Polynomial.X ^ (2 * j.val)) ^ (p j).val else 1) := by
    intro j
    by_cases hj : 0 < j.val
    · rw [if_pos hj, if_pos hj, N_pow_formula j.val hj false false, if_pos rfl, mul_pow, ← pow_mul]
    · rw [if_neg hj, if_neg hj, pow_zero, mul_one]
      have hj0 : j = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
      rw [hj0, partOfPins_zero, pow_zero]
  simp_rw [hfactor, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  change Polynomial.C ((2 : ℤ) ^ u) * ((2 : R1) ^ _ * polyQ n p) = _
  unfold expTwo
  rw [← h2u, ← mul_assoc, ← pow_add, map_pow, map_ofNat]

lemma one_add_X_pow_coeff_zero (d m : ℕ) (hd : 0 < d) :
    ((1 + Polynomial.X ^ d : R1) ^ m).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_one, Polynomial.eval_X_pow, zero_pow hd.ne', add_zero, one_pow]

lemma one_add_X_pow_coeff_self (d m : ℕ) (hd : 0 < d) :
    ((1 + Polynomial.X ^ d : R1) ^ m).coeff d = (m : ℤ) := by
  induction m with
  | zero => simp [Polynomial.coeff_one, hd.ne']
  | succ m ih =>
    have hmul := Polynomial.coeff_mul_X_pow ((1 + Polynomial.X ^ d : R1) ^ m) d 0
    rw [zero_add] at hmul
    rw [pow_succ, mul_add, mul_one, Polynomial.coeff_add, ih, hmul,
      one_add_X_pow_coeff_zero d m hd, Nat.cast_succ]

lemma one_add_X_pow_coeff_lt (d m r : ℕ) (hr0 : 0 < r) (hrd : r < d) :
    ((1 + Polynomial.X ^ d : R1) ^ m).coeff r = 0 := by
  induction m with
  | zero => simp [Polynomial.coeff_one, hr0.ne']
  | succ m ih =>
    rw [pow_succ, mul_add, mul_one, Polynomial.coeff_add, ih, zero_add,
      Polynomial.coeff_mul, sum_eq_zero]
    intro ab hab
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    rw [Polynomial.coeff_X_pow]
    split_ifs with h
    · omega
    · simp

lemma tail_prod_coeff {n : ℕ} (p : Fin (n + 1) → Fin (n + 1)) (s : Finset (Fin (n + 1)))
    (B : ℕ) (hs : ∀ j ∈ s, B < 2 * j.val) :
    (∏ j ∈ s, (if 0 < j.val then (1 + Polynomial.X ^ (2 * j.val)) ^ (p j).val else (1 : R1))).coeff 0 = 1 ∧
    ∀ r, 0 < r → r ≤ B →
      (∏ j ∈ s, (if 0 < j.val then (1 + Polynomial.X ^ (2 * j.val)) ^ (p j).val else (1 : R1))).coeff r = 0 := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simp, fun r hr0 _ => ?_⟩
    simp [Polynomial.coeff_one, hr0.ne']
  | @insert j s hj ih =>
    have hjB : B < 2 * j.val := hs j (mem_insert_self j s)
    have ih' := ih (fun x hx => hs x (mem_insert_of_mem hx))
    have hjd : 0 < 2 * j.val := by omega
    have hjpos : 0 < j.val := by omega
    rw [prod_insert hj, if_pos hjpos]
    set P : R1 := (1 + Polynomial.X ^ (2 * j.val) : R1) ^ (p j).val
    set Q : R1 := ∏ x ∈ s, (if 0 < x.val then (1 + Polynomial.X ^ (2 * x.val)) ^ (p x).val else (1 : R1))
    constructor
    · rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_mul,
        ← Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coeff_zero_eq_eval_zero,
        one_add_X_pow_coeff_zero (2 * j.val) (p j).val hjd, ih'.1, mul_one]
    · intro r hr0 hrB
      rw [Polynomial.coeff_mul]
      apply sum_eq_zero
      intro ab hab
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
      by_cases ha : ab.1 = 0
      · have hb0 : 0 < ab.2 := by omega
        have hbB : ab.2 ≤ B := by omega
        rw [ih'.2 ab.2 hb0 hbB, mul_zero]
      · have ha0 : 0 < ab.1 := by omega
        have had : ab.1 < 2 * j.val := by omega
        rw [one_add_X_pow_coeff_lt (2 * j.val) (p j).val ab.1 ha0 had, zero_mul]

lemma polyQ_coeff_zero (n : ℕ) (p : Fin (n + 1) → Fin (n + 1)) :
    (polyQ n p).coeff 0 = 1 := by
  unfold polyQ
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  apply Finset.prod_eq_one
  intro j _
  split_ifs with hj
  · rw [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X_pow,
      zero_pow (by omega), add_zero, one_pow]
  · simp

lemma polyQ_inj {n : ℕ} {p1 p2 : Fin (n + 1) → Fin (n + 1)}
    (hp1 : (p1 0).val = 0) (hp2 : (p2 0).val = 0)
    (heq : polyQ n p1 = polyQ n p2) : p1 = p2 := by
  by_contra hne
  have hdiff_ne : ((Finset.univ : Finset (Fin (n + 1))).filter (fun j => p1 j ≠ p2 j)).Nonempty := by
    by_contra hemp
    apply hne
    ext j
    have hmem : j ∉ (Finset.univ : Finset (Fin (n + 1))).filter (fun j => p1 j ≠ p2 j) := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hemp]
      simp
    simp only [mem_filter, mem_univ, true_and, not_not] at hmem
    exact congrArg Fin.val hmem
  let k := ((Finset.univ : Finset (Fin (n + 1))).filter (fun j => p1 j ≠ p2 j)).min' hdiff_ne
  have hk_mem : k ∈ (Finset.univ : Finset (Fin (n + 1))).filter (fun j => p1 j ≠ p2 j) :=
    Finset.min'_mem _ hdiff_ne
  have hk_ne : p1 k ≠ p2 k := (mem_filter.mp hk_mem).2
  have hk_pos : 0 < k.val := by
    by_contra hk0
    have hk_eq0 : k = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    apply hk_ne
    rw [hk_eq0]
    exact Fin.ext (hp1.trans hp2.symm)
  let sLt := (Finset.univ : Finset (Fin (n + 1))).filter (fun j => j < k)
  let sGt := (Finset.univ : Finset (Fin (n + 1))).filter (fun j => k < j)
  let f : (Fin (n + 1) → Fin (n + 1)) → Fin (n + 1) → R1 :=
    fun p j => if 0 < j.val then (1 + Polynomial.X ^ (2 * j.val)) ^ (p j).val else 1
  have hsplit : ∀ p, polyQ n p = (∏ j ∈ sLt, f p j) * f p k * (∏ j ∈ sGt, f p j) := by
    intro p
    unfold polyQ
    change (∏ j : Fin (n + 1), f p j) = _
    have huniv : (Finset.univ : Finset (Fin (n + 1))) = insert k (sLt ∪ sGt) := by
      ext j
      simp only [mem_univ, mem_insert, mem_union, mem_filter, true_and, true_iff, sLt, sGt]
      exact lt_trichotomy j k |>.elim (fun h => Or.inr (Or.inl h))
        (fun h => h.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inr h)))
    have hk_not : k ∉ sLt ∪ sGt := by
      simp [sLt, sGt]
    have hdisj : Disjoint sLt sGt := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [sLt, sGt, mem_filter, mem_univ, true_and] at hj1 hj2
      exact absurd (lt_trans hj1 hj2) (lt_irrefl j)
    rw [huniv, prod_insert hk_not, prod_union hdisj]
    ring
  have hpref : ∏ j ∈ sLt, f p1 j = ∏ j ∈ sLt, f p2 j := by
    apply prod_congr rfl
    intro j hj
    simp only [sLt, mem_filter, mem_univ, true_and] at hj
    have hnot : j ∉ (Finset.univ : Finset (Fin (n + 1))).filter (fun j => p1 j ≠ p2 j) :=
      fun h => absurd (Finset.min'_le _ j h) (not_le_of_gt hj)
    simp only [mem_filter, mem_univ, true_and, not_not] at hnot
    simp [f, hnot]
  have hpref_ne : ∏ j ∈ sLt, f p1 j ≠ 0 := by
    intro hz
    have hev0 : (∏ j ∈ sLt, f p1 j).eval 0 = 0 := by rw [hz, Polynomial.eval_zero]
    have hev1 : (∏ j ∈ sLt, f p1 j).eval 0 = 1 := by
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_one
      intro j _
      simp only [f]
      split_ifs with hj
      · rw [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X_pow,
          zero_pow (by omega), add_zero, one_pow]
      · simp
    omega
  rw [hsplit p1, hsplit p2, ← hpref, mul_assoc, mul_assoc] at heq
  have heq' := mul_left_cancel₀ hpref_ne heq
  simp only [f, if_pos hk_pos] at heq'
  have htail1 := tail_prod_coeff p1 sGt (2 * k.val) (fun j hj => by
    simp only [sGt, mem_filter, mem_univ, true_and] at hj
    have : k.val < j.val := hj
    omega)
  have htail2 := tail_prod_coeff p2 sGt (2 * k.val) (fun j hj => by
    simp only [sGt, mem_filter, mem_univ, true_and] at hj
    have : k.val < j.val := hj
    omega)
  have hcoeff1 : (((1 + Polynomial.X ^ (2 * k.val) : R1) ^ (p1 k).val) * ∏ j ∈ sGt, f p1 j).coeff (2 * k.val) =
      ((p1 k).val : ℤ) := by
    rw [Polynomial.coeff_mul, sum_eq_single (2 * k.val, 0)]
    · dsimp only
      rw [one_add_X_pow_coeff_self (2 * k.val) (p1 k).val (by omega)]
      have ht1 : (∏ j ∈ sGt, f p1 j).coeff 0 = 1 := htail1.1
      rw [ht1, mul_one]
    · intro ab hab hne_ab
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
      by_cases hb : ab.2 = 0
      · exfalso
        apply hne_ab
        ext <;> omega
      · have hb0 : 0 < ab.2 := by omega
        have hbB : ab.2 ≤ 2 * k.val := by omega
        have ht1 : (∏ j ∈ sGt, f p1 j).coeff ab.2 = 0 := htail1.2 ab.2 hb0 hbB
        rw [ht1, mul_zero]
    · intro hnot
      exfalso
      exact hnot (Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero _))
  have hcoeff2 : (((1 + Polynomial.X ^ (2 * k.val) : R1) ^ (p2 k).val) * ∏ j ∈ sGt, f p2 j).coeff (2 * k.val) =
      ((p2 k).val : ℤ) := by
    rw [Polynomial.coeff_mul, sum_eq_single (2 * k.val, 0)]
    · dsimp only
      rw [one_add_X_pow_coeff_self (2 * k.val) (p2 k).val (by omega)]
      have ht2 : (∏ j ∈ sGt, f p2 j).coeff 0 = 1 := htail2.1
      rw [ht2, mul_one]
    · intro ab hab hne_ab
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
      by_cases hb : ab.2 = 0
      · exfalso
        apply hne_ab
        ext <;> omega
      · have hb0 : 0 < ab.2 := by omega
        have hbB : ab.2 ≤ 2 * k.val := by omega
        have ht2 : (∏ j ∈ sGt, f p2 j).coeff ab.2 = 0 := htail2.2 ab.2 hb0 hbB
        rw [ht2, mul_zero]
    · intro hnot
      exfalso
      exact hnot (Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero _))
  have hce := congrArg (fun P : R1 => P.coeff (2 * k.val)) heq'
  rw [hcoeff1, hcoeff2] at hce
  exact hk_ne (Fin.ext (Int.ofNat.inj hce))

lemma histFn_eq_iff (c : ℕ) (L : Fin c → ℕ)
    (pins1 pins2 : Finset ((i : Fin c) × Fin (L i + 1))) :
    histFn c L pins1 = histFn c L pins2 ↔
      partOfPins c L pins1 = partOfPins c L pins2 ∧ uOfPins c L pins1 = uOfPins c L pins2 := by
  constructor
  · intro hhist
    have hgen : histGen2 c L pins1 = histGen2 c L pins2 := by
      unfold histGen2
      rw [hhist]
    have hhom := congrArg (fun P => homog (2 * ∑ i : Fin c, (L i + 1)) (evalDiag P)) hgen
    rw [homog_evalDiag_histGen2, homog_evalDiag_histGen2] at hhom
    have hc0 := congrArg (fun P : R1 => P.coeff 0) hhom
    simp only [Polynomial.coeff_C_mul, polyQ_coeff_zero, mul_one] at hc0
    have hc0_nat : 2 ^ expTwo (∑ i : Fin c, (L i + 1)) (uOfPins c L pins1) (partOfPins c L pins1) =
        2 ^ expTwo (∑ i : Fin c, (L i + 1)) (uOfPins c L pins2) (partOfPins c L pins2) := by
      exact_mod_cast hc0
    have hexp : expTwo (∑ i : Fin c, (L i + 1)) (uOfPins c L pins1) (partOfPins c L pins1) =
        expTwo (∑ i : Fin c, (L i + 1)) (uOfPins c L pins2) (partOfPins c L pins2) :=
      Nat.pow_right_injective (by norm_num) hc0_nat
    rw [hexp] at hhom
    have hc_ne : Polynomial.C ((2 : ℤ) ^ expTwo (∑ i : Fin c, (L i + 1)) (uOfPins c L pins2) (partOfPins c L pins2)) ≠ 0 := by
      simp
    have hq := mul_left_cancel₀ hc_ne hhom
    have hp : partOfPins c L pins1 = partOfPins c L pins2 :=
      polyQ_inj (partOfPins_zero c L pins1) (partOfPins_zero c L pins2) hq
    refine ⟨hp, ?_⟩
    unfold expTwo at hexp
    rw [hp] at hexp
    omega
  · rintro ⟨hp, hu⟩
    have hgen : histGen2 c L pins1 = histGen2 c L pins2 := by
      rw [histGen2_eq_prod_part, histGen2_eq_prod_part, hp, hu]
    ext d
    have h1 := histGen2_coeff c L pins1 d
    have h2 := histGen2_coeff c L pins2 d
    rw [hgen] at h1
    omega

lemma exists_max_singleton_alloc (c : ℕ) (L : Fin c → ℕ)
    (p : Fin (∑ i : Fin c, (L i + 1) + 1) → Fin (∑ i : Fin c, (L i + 1) + 1))
    (hp : p ∈ partsFn c L) :
    ∃ alloc : Fin c → (Fin (∑ i : Fin c, (L i + 1) + 1) → Fin (∑ i : Fin c, (L i + 1) + 1)),
      (∀ i, (∑ j : Fin (∑ i : Fin c, (L i + 1) + 1), j.val * (alloc i j).val) = L i + 1) ∧
      (∀ j, (∑ i : Fin c, (alloc i j).val) = (p j).val) ∧
      ((Finset.univ : Finset (Fin c)).filter (fun i =>
        0 < (alloc i ⟨L i + 1, by
          have h := Finset.single_le_sum (fun k _ => Nat.zero_le (L k + 1)) (mem_univ i)
          omega⟩).val)).card = maxU c L p := by
  let n := ∑ i : Fin c, (L i + 1)
  let J := Fin (n + 1)
  let jOf : Fin c → J := fun i => ⟨L i + 1, by
    have h : L i + 1 ≤ n :=
      Finset.single_le_sum (f := fun k => L k + 1) (fun k _ => Nat.zero_le _) (mem_univ i)
    omega⟩
  let Allocs : Finset (Fin c → J → J) :=
    Finset.univ.filter (fun alloc =>
      (∀ i, (∑ j : J, j.val * (alloc i j).val) = L i + 1) ∧
      (∀ j, (∑ i : Fin c, (alloc i j).val) = (p j).val))
  have hp' := (mem_filter.mp hp).2
  have hp0 : (p 0).val = 0 := hp'.1
  have hAllocs_ne : Allocs.Nonempty := by
    rcases hp'.2 with ⟨alloc, ha1, ha2⟩
    exact ⟨alloc, mem_filter.mpr ⟨mem_univ _, ha1, ha2⟩⟩
  let singles : (Fin c → J → J) → Finset (Fin c) :=
    fun alloc => Finset.univ.filter (fun i => 0 < (alloc i (jOf i)).val)
  rcases Finset.exists_max_image Allocs (fun alloc => (singles alloc).card) hAllocs_ne with
    ⟨alloc, hmem, hmax⟩
  rcases (mem_filter.mp hmem).2 with ⟨ha1, ha2⟩
  refine ⟨alloc, ha1, ha2, ?_⟩
  have hle : (singles alloc).card ≤ maxU c L p := by
    unfold maxU
    rw [Finset.card_eq_sum_ones, ← Finset.sum_fiberwise (singles alloc) jOf (fun _ => (1 : ℕ))]
    apply Finset.sum_le_sum
    intro j _
    rw [Finset.sum_const, smul_eq_mul, mul_one]
    apply le_min
    · calc ((singles alloc).filter (fun i => jOf i = j)).card
          = ∑ _i ∈ (singles alloc).filter (fun i => jOf i = j), 1 := by simp
        _ ≤ ∑ i ∈ (singles alloc).filter (fun i => jOf i = j), (alloc i j).val := by
            apply Finset.sum_le_sum
            intro i hi
            simp only [mem_filter, singles, mem_univ, true_and] at hi
            rw [← hi.2]
            exact hi.1
        _ ≤ ∑ i : Fin c, (alloc i j).val :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ = (p j).val := ha2 j
    · apply Finset.card_le_card
      intro i hi
      simp only [mem_filter, singles, mem_univ, true_and] at hi ⊢
      exact congrArg Fin.val hi.2
  by_contra hne
  have hlt : (singles alloc).card < maxU c L p := lt_of_le_of_ne hle hne
  rw [Finset.card_eq_sum_ones, ← Finset.sum_fiberwise (singles alloc) jOf (fun _ => (1 : ℕ))] at hlt
  have hex : ∃ j0 ∈ (Finset.univ : Finset J),
      ∑ _i ∈ (singles alloc).filter (fun i => jOf i = j0), 1 <
        min (p j0).val ((Finset.univ : Finset (Fin c)).filter (fun i => L i + 1 = j0.val)).card := by
    by_contra hno
    push Not at hno
    exact absurd (Finset.sum_le_sum hno) (not_le_of_gt hlt)
  rcases hex with ⟨j0, _, hj0_lt⟩
  rw [Finset.sum_const, smul_eq_mul, mul_one] at hj0_lt
  have hj0_min1 : ((singles alloc).filter (fun i => jOf i = j0)).card < (p j0).val :=
    lt_of_lt_of_le hj0_lt (min_le_left _ _)
  have hj0_min2 : ((singles alloc).filter (fun i => jOf i = j0)).card <
      ((Finset.univ : Finset (Fin c)).filter (fun i => L i + 1 = j0.val)).card :=
    lt_of_lt_of_le hj0_lt (min_le_right _ _)
  have hj0_pos : 0 < j0.val := by
    by_contra h0
    have hj0_eq : j0 = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    rw [hj0_eq, hp0] at hj0_min1
    omega
  have hex_i0 : ∃ i0 ∈ (Finset.univ : Finset (Fin c)).filter (fun i => L i + 1 = j0.val),
      i0 ∉ (singles alloc).filter (fun i => jOf i = j0) := by
    by_contra hno
    push Not at hno
    have hsub : (Finset.univ : Finset (Fin c)).filter (fun i => L i + 1 = j0.val) ⊆
        (singles alloc).filter (fun i => jOf i = j0) := fun i hi => hno i hi
    exact absurd (Finset.card_le_card hsub) (not_le_of_gt hj0_min2)
  rcases hex_i0 with ⟨i0, hi0_mem, hi0_not⟩
  have hi0_L : jOf i0 = j0 := Fin.ext (mem_filter.mp hi0_mem).2
  have hi0_not_sing : i0 ∉ singles alloc := fun h => hi0_not (mem_filter.mpr ⟨h, hi0_L⟩)
  have hi0_val : (alloc i0 j0).val = 0 := by
    simp only [singles, mem_filter, mem_univ, true_and, not_lt, Nat.le_zero] at hi0_not_sing
    rw [← hi0_L]
    exact hi0_not_sing
  have hsingle_val : ∀ i ∈ (singles alloc).filter (fun i => jOf i = j0), (alloc i j0).val = 1 := by
    intro i hi
    simp only [mem_filter, singles, mem_univ, true_and] at hi
    have hsum_i := ha1 i
    have hterm : j0.val * (alloc i j0).val ≤ ∑ j : J, j.val * (alloc i j).val :=
      Finset.single_le_sum (f := fun j : J => j.val * (alloc i j).val) (fun j _ => Nat.zero_le _) (mem_univ j0)
    rw [hsum_i, ← congrArg Fin.val hi.2] at hterm
    change (L i + 1) * (alloc i j0).val ≤ L i + 1 at hterm
    have hpos : 0 < (alloc i j0).val := by rw [← hi.2]; exact hi.1
    nlinarith
  have hsum_eq_j0 : ∑ i ∈ (Finset.univ : Finset (Fin c)).filter (fun i => jOf i = j0), (alloc i j0).val =
      ((singles alloc).filter (fun i => jOf i = j0)).card := by
    calc ∑ i ∈ (Finset.univ : Finset (Fin c)).filter (fun i => jOf i = j0), (alloc i j0).val
        = ∑ i ∈ (singles alloc).filter (fun i => jOf i = j0), (alloc i j0).val := by
          rw [← Finset.sum_subset]
          · intro i hi
            simp only [mem_filter, singles, mem_univ, true_and] at hi ⊢
            exact hi.2
          · intro i hi hnot
            simp only [mem_filter, singles, mem_univ, true_and] at hi hnot ⊢
            by_contra hne0
            apply hnot
            refine ⟨?_, hi⟩
            rw [hi]
            omega
      _ = ∑ _i ∈ (singles alloc).filter (fun i => jOf i = j0), 1 :=
          sum_congr rfl (fun i hi => hsingle_val i hi)
      _ = ((singles alloc).filter (fun i => jOf i = j0)).card := by simp
  have hex_i1 : ∃ i1 : Fin c, jOf i1 ≠ j0 ∧ 0 < (alloc i1 j0).val := by
    by_contra hno
    push Not at hno
    have hsum_all : ∑ i : Fin c, (alloc i j0).val =
        ∑ i ∈ (Finset.univ : Finset (Fin c)).filter (fun i => jOf i = j0), (alloc i j0).val := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      simp only [mem_filter, mem_univ, true_and] at hi
      have h0 := hno i hi
      omega
    rw [ha2 j0, hsum_eq_j0] at hsum_all
    omega
  rcases hex_i1 with ⟨i1, hi1_ne, hi1_pos⟩
  have hi1_ne_i0 : i1 ≠ i0 := fun h => hi1_ne (h ▸ hi0_L)
  have hi1_not_sing : i1 ∉ singles alloc := by
    intro hi1_sing
    simp only [singles, mem_filter, mem_univ, true_and] at hi1_sing
    have hsum_i1 := ha1 i1
    have htwo : (jOf i1).val * (alloc i1 (jOf i1)).val + j0.val * (alloc i1 j0).val ≤
        ∑ j : J, j.val * (alloc i1 j).val :=
      Finset.add_le_sum (f := fun j : J => j.val * (alloc i1 j).val)
        (fun j _ => Nat.zero_le _) (mem_univ (jOf i1)) (mem_univ j0) hi1_ne
    rw [hsum_i1] at htwo
    change (L i1 + 1) * (alloc i1 (jOf i1)).val + j0.val * (alloc i1 j0).val ≤ L i1 + 1 at htwo
    nlinarith
  have hle_p : ∀ j : J, (alloc i1 j).val + (alloc i0 j).val ≤ (p j).val := fun j => by
    have h := Finset.add_le_sum (fun i _ => Nat.zero_le (alloc i j).val)
      (mem_univ i1) (mem_univ i0) hi1_ne_i0
    rw [ha2 j] at h
    exact h
  let alloc' : Fin c → J → J := fun i j =>
    if i = i0 then (if j = j0 then ⟨1, by omega⟩ else 0)
    else if i = i1 then ⟨(alloc i1 j).val + (alloc i0 j).val - (if j = j0 then 1 else 0), by
      have h := hle_p j
      have hpj := (p j).isLt
      omega⟩
    else alloc i j
  have halloc'_mem : alloc' ∈ Allocs := by
    rw [mem_filter]
    refine ⟨mem_univ _, ?_, ?_⟩
    · intro i
      by_cases hi0 : i = i0
      · rw [hi0]
        have hsum0 : ∑ j : J, j.val * (alloc' i0 j).val = j0.val := by
          rw [sum_eq_single j0]
          · simp [alloc']
          · intro j _ hj
            simp [alloc', hj]
          · intro hnot
            exfalso
            exact hnot (mem_univ j0)
        rw [hsum0]
        exact (congrArg Fin.val hi0_L).symm
      · by_cases hi1 : i = i1
        · rw [hi1]
          have hterm : ∀ j : J, j.val * (alloc' i1 j).val + (if j = j0 then j0.val else 0) =
              j.val * (alloc i1 j).val + j.val * (alloc i0 j).val := fun j => by
            simp only [alloc', if_neg hi1_ne_i0, if_pos rfl]
            by_cases hj : j = j0
            · rw [hj]
              simp only [↓reduceIte]
              have hval : (alloc i1 j0).val + (alloc i0 j0).val ≥ 1 := by omega
              zify [hval]
              ring
            · simp only [hj, ↓reduceIte, Nat.sub_zero, add_zero]
              ring
          have hsum_eq := Finset.sum_congr (s₁ := (Finset.univ : Finset J)) rfl (fun j _ => hterm j)
          simp only [Finset.sum_add_distrib] at hsum_eq
          have hif : ∑ j : J, (if j = j0 then j0.val else 0) = j0.val := by simp
          have hL0 : L i0 + 1 = j0.val := congrArg Fin.val hi0_L
          rw [hif, ha1 i1, ha1 i0, hL0] at hsum_eq
          omega
        · simp only [alloc', if_neg hi0, if_neg hi1]
          exact ha1 i
    · intro j
      have hpair : ∑ i : Fin c, (alloc' i j).val =
          (alloc' i0 j).val + ((alloc' i1 j).val +
            ∑ i ∈ (Finset.univ : Finset (Fin c)).erase i0 |>.erase i1, (alloc' i j).val) := by
        rw [← Finset.add_sum_erase _ _ (mem_univ i0)]
        congr 1
        rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hi1_ne_i0, mem_univ i1⟩)]
      have hpair_orig : ∑ i : Fin c, (alloc i j).val =
          (alloc i0 j).val + ((alloc i1 j).val +
            ∑ i ∈ (Finset.univ : Finset (Fin c)).erase i0 |>.erase i1, (alloc i j).val) := by
        rw [← Finset.add_sum_erase _ _ (mem_univ i0)]
        congr 1
        rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hi1_ne_i0, mem_univ i1⟩)]
      rw [← ha2 j, hpair, hpair_orig]
      have hrest : ∑ i ∈ (Finset.univ : Finset (Fin c)).erase i0 |>.erase i1, (alloc' i j).val =
          ∑ i ∈ (Finset.univ : Finset (Fin c)).erase i0 |>.erase i1, (alloc i j).val := by
        apply sum_congr rfl
        intro i hi
        have h1 : i ≠ i1 := (Finset.mem_erase.mp hi).1
        have h0 : i ≠ i0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        simp [alloc', h0, h1]
      rw [hrest]
      by_cases hj : j = j0
      · subst hj
        simp only [alloc', if_pos rfl, if_neg hi1_ne_i0, ↓reduceIte]
        omega
      · simp only [alloc', if_pos rfl, if_neg hj, if_neg hi1_ne_i0, Nat.sub_zero, Fin.val_zero, ↓reduceIte]
        omega
  have hsub_sing : insert i0 (singles alloc) ⊆ singles alloc' := by
    intro i hi
    simp only [mem_insert, singles, mem_filter, mem_univ, true_and] at hi ⊢
    rcases hi with rfl | hi
    · simp [alloc', hi0_L]
    · have hine0 : i ≠ i0 := fun h => hi0_not_sing (mem_filter.mpr ⟨mem_univ _, h ▸ hi⟩)
      have hine1 : i ≠ i1 := fun h => hi1_not_sing (mem_filter.mpr ⟨mem_univ _, h ▸ hi⟩)
      simp [alloc', hine0, hine1, hi]
  have hcard_lt : (singles alloc).card < (singles alloc').card := by
    calc (singles alloc).card < (insert i0 (singles alloc)).card := by
          rw [Finset.card_insert_of_notMem hi0_not_sing]
          omega
      _ ≤ (singles alloc').card := Finset.card_le_card hsub_sing
  exact absurd (hmax alloc' halloc'_mem) (not_le_of_gt hcard_lt)

lemma count_flatMap_replicate {m : ℕ} (l : List (Fin (m + 1))) (hl : l.Nodup)
    (f : Fin (m + 1) → ℕ) (j : Fin (m + 1)) :
    (l.flatMap (fun x => List.replicate (f x) x.val)).count j.val = if j ∈ l then f j else 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx_not : x ∉ xs := (List.nodup_cons.mp hl).1
    have hxs_nd : xs.Nodup := (List.nodup_cons.mp hl).2
    rw [List.flatMap_cons, List.count_append, ih hxs_nd, List.count_replicate]
    by_cases hjx : x = j
    · subst hjx
      simp only [beq_self_eq_true, ↓reduceIte, List.mem_cons, true_or]
      rw [if_neg hx_not, add_zero]
    · have hval_ne : x.val ≠ j.val := fun h => hjx (Fin.ext h)
      simp only [beq_iff_eq, if_neg hval_ne, zero_add, List.mem_cons, Ne.symm hjx, false_or]

lemma flatMap_gap_length (gs : List ℕ) (hgs : ∀ g ∈ gs, 1 ≤ g) :
    (gs.flatMap (fun g => true :: List.replicate (g - 1) false)).length = gs.sum := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg : 1 ≤ g := hgs g (by simp)
    have hgs' : ∀ x ∈ gs, 1 ≤ x := fun x hx => hgs x (by simp [hx])
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      List.length_replicate, ih hgs', List.sum_cons]
    omega

lemma realize_gaps_list (m : ℕ) (gs : List ℕ) (hgs : ∀ g ∈ gs, 1 ≤ g) (hsum : gs.sum = m + 1) :
    ∃ (S : Finset (Fin (m + 1))) (hS : S.Nonempty), gapsOfPins m S hS = gs := by
  rcases gs with _ | ⟨g0, gs'⟩
  · simp at hsum
  · have hg0 : 1 ≤ g0 := hgs g0 (by simp)
    have hgs' : ∀ g ∈ gs', 1 ≤ g := fun g hg => hgs g (by simp [hg])
    let bs : List Bool := List.replicate (g0 - 1) false ++
      gs'.flatMap (fun g => true :: List.replicate (g - 1) false)
    have hbs_len : bs.length = m := by
      simp only [bs, List.length_append, List.length_replicate, flatMap_gap_length gs' hgs']
      simp only [List.sum_cons] at hsum
      omega
    let fullBs : List Bool := true :: bs
    have hfull_len : fullBs.length = m + 1 := by simp [fullBs, hbs_len]
    let S : Finset (Fin (m + 1)) :=
      Finset.univ.filter (fun k => fullBs[k.val]'(by rw [hfull_len]; exact k.isLt) = true)
    have h0 : (0 : Fin (m + 1)) ∈ S := by
      simp [S, fullBs]
    have hS : S.Nonempty := ⟨0, h0⟩
    have hmin : S.min' hS = 0 :=
      le_antisymm (S.min'_le 0 h0) (Fin.zero_le _)
    have htail : ((List.finRange (m + 1)).rotate (S.min' hS).val).tail.map (fun k => decide (k ∈ S)) = bs := by
      rw [hmin, Fin.val_zero, List.rotate_zero, List.finRange_succ, List.tail_cons, List.map_map]
      apply List.ext_getElem
      · simp [hbs_len]
      · intro idx h1 h2
        simp only [List.length_map, List.length_finRange] at h1
        simp only [List.getElem_map, List.getElem_finRange, Function.comp_apply, Fin.val_succ,
          Fin.val_cast, S, mem_filter, mem_univ, true_and, fullBs, List.getElem_cons_succ]
        by_cases hb : bs[idx] = true <;> simp [hb]
    refine ⟨S, hS, ?_⟩
    unfold gapsOfPins
    dsimp only
    rw [htail]
    simp only [bs]
    rw [collectGaps_replicate_false, show 1 + (g0 - 1) = g0 by omega,
      collectGaps_flatMap g0 gs' hgs']

lemma exists_pins_of_mem_partsFn (c : ℕ) (L : Fin c → ℕ)
    (p : Fin (∑ i : Fin c, (L i + 1) + 1) → Fin (∑ i : Fin c, (L i + 1) + 1))
    (hp : p ∈ partsFn c L) (u : ℕ) (hu : u ≤ maxU c L p) :
    ∃ pins : Finset ((i : Fin c) × Fin (L i + 1)),
      partOfPins c L pins = p ∧ uOfPins c L pins = u := by
  let n := ∑ i : Fin c, (L i + 1)
  let J := Fin (n + 1)
  let jOf : Fin c → J := fun i => ⟨L i + 1, by
    have h : L i + 1 ≤ n :=
      Finset.single_le_sum (f := fun k => L k + 1) (fun k _ => Nat.zero_le _) (mem_univ i)
    omega⟩
  rcases exists_max_singleton_alloc c L p hp with ⟨alloc, ha1, ha2, hmax_card⟩
  let singles := (Finset.univ : Finset (Fin c)).filter (fun i => 0 < (alloc i (jOf i)).val)
  have hu_le_sing : u ≤ singles.card := by
    rw [hmax_card]
    exact hu
  rcases Finset.exists_subset_card_eq hu_le_sing with ⟨T, hT_sub, hT_card⟩
  have hp0 : (p 0).val = 0 := ((mem_filter.mp hp).2).1
  have ha0 : ∀ i : Fin c, (alloc i 0).val = 0 := fun i => by
    have hle := Finset.single_le_sum (fun k _ => Nat.zero_le (alloc k 0).val) (mem_univ i)
    rw [ha2 0, hp0] at hle
    omega
  have hcomp : ∀ i : Fin c, ∃ S : Finset (Fin (L i + 1)),
      (if S.Nonempty then 0 else 1) = (if i ∈ T then 1 else 0) ∧
      ∀ j : J, (if hS : S.Nonempty then gapsOfPins (L i) S hS else [L i + 1]).count j.val = (alloc i j).val := by
    intro i
    by_cases hiT : i ∈ T
    · have hi_sing : i ∈ singles := hT_sub hiT
      have hpos : 0 < (alloc i (jOf i)).val := (mem_filter.mp hi_sing).2
      have hsum_i := ha1 i
      have halloc_eq : ∀ j : J, (alloc i j).val = if j = jOf i then 1 else 0 := by
        intro j
        by_cases hj : j = jOf i
        · subst hj
          have hterm := Finset.single_le_sum (fun k _ => Nat.zero_le (k.val * (alloc i k).val)) (mem_univ (jOf i))
          rw [hsum_i] at hterm
          change (L i + 1) * (alloc i (jOf i)).val ≤ L i + 1 at hterm
          rw [if_pos rfl]
          nlinarith
        · rw [if_neg hj]
          by_contra hne0
          have hpos_j : 0 < (alloc i j).val := by omega
          have hj_pos : 0 < j.val := by
            by_contra hj0
            have hj_eq : j = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
            rw [hj_eq, ha0 i] at hpos_j
            omega
          have htwo := Finset.add_le_sum (fun k _ => Nat.zero_le (k.val * (alloc i k).val))
            (mem_univ (jOf i)) (mem_univ j) (Ne.symm hj)
          rw [hsum_i] at htwo
          change (L i + 1) * (alloc i (jOf i)).val + j.val * (alloc i j).val ≤ L i + 1 at htwo
          nlinarith
      refine ⟨∅, ?_, ?_⟩
      · simp [hiT]
      · intro j
        rw [dif_neg Finset.not_nonempty_empty, List.count_singleton, halloc_eq j]
        by_cases hj : j = jOf i
        · subst hj
          simp [jOf]
        · have hjval : (jOf i).val ≠ j.val := fun h => hj (Fin.ext h.symm)
          simp [hj, hjval, jOf]
    · let gs : List ℕ := (List.finRange (n + 1)).flatMap (fun j => List.replicate (alloc i j).val j.val)
      have hgs_count : ∀ j : J, gs.count j.val = (alloc i j).val := fun j => by
        rw [count_flatMap_replicate _ (List.nodup_finRange _) (fun k => (alloc i k).val) j]
        simp [List.mem_finRange]
      have hgs_pos : ∀ g ∈ gs, 1 ≤ g := by
        intro g hg
        simp only [gs, List.mem_flatMap, List.mem_finRange, List.mem_replicate, true_and] at hg
        rcases hg with ⟨j, hrep, rfl⟩
        by_contra hj0
        have hj_eq : j = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
        subst hj_eq
        exact absurd (ha0 i) hrep
      have hgs_le : ∀ g ∈ gs, g ≤ n := by
        intro g hg
        simp only [gs, List.mem_flatMap, List.mem_finRange, List.mem_replicate, true_and] at hg
        rcases hg with ⟨j, _, rfl⟩
        omega
      have hgs_sum : gs.sum = L i + 1 := by
        rw [← list_sum_count_mul gs hgs_le]
        simp_rw [hgs_count]
        exact ha1 i
      rcases realize_gaps_list (L i) gs hgs_pos hgs_sum with ⟨S, hS, hgaps⟩
      refine ⟨S, ?_, ?_⟩
      · simp [hiT, hS]
      · intro j
        rw [dif_pos hS, hgaps, hgs_count j]
  choose S hS_u hS_count using hcomp
  let pins : Finset ((i : Fin c) × Fin (L i + 1)) :=
    Finset.univ.filter (fun x => x.2 ∈ S x.1)
  have hslice : ∀ i : Fin c, pinSlice pins i = S i := fun i => by
    ext k
    simp [pinSlice, pins]
  refine ⟨pins, ?_, ?_⟩
  · ext j
    simp only [partOfPins]
    have hcnt : ∀ i : Fin c, (gapsOfComp c L pins i).count j.val = (alloc i j).val := fun i => by
      unfold gapsOfComp
      rw [hslice i]
      exact hS_count i j
    simp_rw [hcnt]
    exact ha2 j
  · unfold uOfPins uOfComp
    simp_rw [hslice, hS_u]
    simp [hT_card]

lemma card_image_eq_of_eq_iff {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (f : α → β) (g : α → γ) (h : ∀ x ∈ s, ∀ y ∈ s, f x = f y ↔ g x = g y) :
    (s.image f).card = (s.image g).card := by
  classical
  refine Finset.card_bij
    (fun b hb => g (Classical.choose (Finset.mem_image.mp hb)))
    (fun b hb => by
      have hch := Classical.choose_spec (Finset.mem_image.mp hb)
      exact Finset.mem_image.mpr ⟨_, hch.1, rfl⟩)
    (fun b1 hb1 b2 hb2 heq => by
      have h1 := Classical.choose_spec (Finset.mem_image.mp hb1)
      have h2 := Classical.choose_spec (Finset.mem_image.mp hb2)
      rw [← h1.2, ← h2.2]
      exact (h _ h1.1 _ h2.1).mpr heq)
    (fun c hc => by
      rcases Finset.mem_image.mp hc with ⟨x, hx, rfl⟩
      have hfx : f x ∈ s.image f := Finset.mem_image.mpr ⟨x, hx, rfl⟩
      refine ⟨f x, hfx, ?_⟩
      have h1 := Classical.choose_spec (Finset.mem_image.mp hfx)
      exact (h _ h1.1 _ hx).mp h1.2)

lemma main_eq (c : ℕ) (L : Fin c → ℕ) :
    ((Finset.univ : Finset (Finset ((i : Fin c) × Fin (L i + 1)))).image (histFn c L)).card =
      ∑ p ∈ partsFn c L, (1 + maxU c L p) := by
  classical
  let phi : Finset ((i : Fin c) × Fin (L i + 1)) →
      Sigma (fun _ : (Fin (∑ i : Fin c, (L i + 1) + 1) → Fin (∑ i : Fin c, (L i + 1) + 1)) => ℕ) :=
    fun pins => ⟨partOfPins c L pins, uOfPins c L pins⟩
  have hcard : ((Finset.univ : Finset (Finset ((i : Fin c) × Fin (L i + 1)))).image (histFn c L)).card =
      ((Finset.univ : Finset (Finset ((i : Fin c) × Fin (L i + 1)))).image phi).card := by
    apply card_image_eq_of_eq_iff
    intro p1 _ p2 _
    rw [histFn_eq_iff]
    simp [phi]
  rw [hcard]
  have himg : (Finset.univ : Finset (Finset ((i : Fin c) × Fin (L i + 1)))).image phi =
      (partsFn c L).sigma (fun p => Finset.range (maxU c L p + 1)) := by
    ext ⟨p, u⟩
    simp only [mem_image, mem_univ, true_and, mem_sigma, Finset.mem_range, phi]
    constructor
    · rintro ⟨pins, hpins⟩
      have hp_eq : partOfPins c L pins = p := congrArg Sigma.fst hpins
      have hu_eq : uOfPins c L pins = u := by
        have := congrArg Sigma.snd hpins
        simpa using this
      refine ⟨?_, ?_⟩
      · rw [← hp_eq]
        exact partOfPins_mem_partsFn c L pins
      · rw [← hp_eq, ← hu_eq]
        exact Nat.lt_succ_of_le (uOfPins_le_maxU c L pins)
    · rintro ⟨hp, hu⟩
      rcases exists_pins_of_mem_partsFn c L p hp u (Nat.lt_succ_iff.mp hu) with ⟨pins, hp_eq, hu_eq⟩
      refine ⟨pins, ?_⟩
      simp [hp_eq, hu_eq]
  rw [himg, Finset.card_sigma]
  apply sum_congr rfl
  intro p _
  rw [Finset.card_range, add_comm]

end MainProof

end

end PEqualNP.Outside.L_pcx_374

theorem PEqualNP.Outside.L_pcx_374 : (∀ (c : ℕ) (L : Fin c → ℕ),
  let n := ∑ i : Fin c, (L i+1)
  let I := (i : Fin c) × Fin (L i+1)
  let V := Bool × I
  let J := Fin (n+1)
  let Part := J → J
  let hist := fun (pins : Finset I) (d : J × J) =>
    ((Finset.univ : Finset (V → Bool)).filter (fun x =>
      (∀ i ∈ pins, x (false,i) = false) ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,i))).card = d.1.val ∧
      (Finset.univ.filter (fun i : I => x (false,i) ≠
        x (true,(⟨i.1,i.2+1⟩ : I)))).card = d.2.val)).card
  let parts := (Finset.univ : Finset Part).filter (fun p => (p 0).val = 0 ∧
    ∃ alloc : Fin c → Part,
      (∀ i, (∑ j : J, j.val * (alloc i j).val) = L i + 1) ∧
      ∀ j, (∑ i : Fin c, (alloc i j).val) = (p j).val)
  ((Finset.univ : Finset (Finset I)).image hist).card =
    ∑ p ∈ parts, (1 + ∑ j : J,
      min (p j).val ((Finset.univ : Finset (Fin c)).filter (fun i => L i+1 = j.val)).card)) := by
  intro c L
  exact PEqualNP.Outside.L_pcx_374.main_eq c L
