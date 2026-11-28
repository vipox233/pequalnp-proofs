import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1089

abbrev F := ZMod 2

abbrev Vec (s k : ℕ) := (Fin s → Fin 2 → F) × ((Fin k → F) × (Fin k → F))

abbrev Coord (s k : ℕ) := (Fin s × Fin 2) ⊕ (Fin k ⊕ Fin k)

lemma f2_eq_zero_or_one (x : F) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩
  interval_cases v
  · left; rfl
  · right; rfl

lemma f2_eq_one_of_ne_zero {x : F} (hx : x ≠ 0) : x = 1 := by
  rcases f2_eq_zero_or_one x with rfl | rfl
  · exact absurd rfl hx
  · rfl

lemma f2_mul_self (x : F) : x * x = x := by
  rcases f2_eq_zero_or_one x with rfl | rfl <;> decide

lemma f2_add_self (x : F) : x + x = 0 := by
  rcases f2_eq_zero_or_one x with rfl | rfl <;> decide

lemma f2_sq_sum {ι : Type*} (t : Finset ι) (u : ι → F) :
    (∑ i ∈ t, u i) * (∑ i ∈ t, u i) = ∑ i ∈ t, u i := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    have h1 : (u a + ∑ i ∈ t, u i) * (u a + ∑ i ∈ t, u i) =
        u a * u a + (u a * ∑ i ∈ t, u i + u a * ∑ i ∈ t, u i) +
        (∑ i ∈ t, u i) * (∑ i ∈ t, u i) := by ring
    rw [h1, f2_mul_self, f2_add_self, add_zero, ih]

def coordEval {s k : ℕ} (x : Vec s k) : Coord s k → F
  | Sum.inl (i, p) => x.1 i p
  | Sum.inr (Sum.inl h) => x.2.1 h
  | Sum.inr (Sum.inr h) => x.2.2 h

def coordOfFun {s k : ℕ} (f : Coord s k → F) : Vec s k :=
  (fun i p => f (Sum.inl (i, p)), (fun h => f (Sum.inr (Sum.inl h)), fun h => f (Sum.inr (Sum.inr h))))

def coordEquiv (s k : ℕ) : Vec s k ≃ (Coord s k → F) where
  toFun := coordEval
  invFun := coordOfFun
  left_inv x := by
    rcases x with ⟨x1, ⟨x21, x22⟩⟩
    rfl
  right_inv f := by
    funext c
    rcases c with ⟨i, p⟩ | (h | h) <;> rfl

def supp {s k : ℕ} (x : Vec s k) : Finset (Coord s k) :=
  Finset.univ.filter (fun c => coordEval x c = 1)

def ofSupp {s k : ℕ} (T : Finset (Coord s k)) : Vec s k :=
  coordOfFun (fun c => if c ∈ T then 1 else 0)

lemma coordEval_coordOfFun {s k : ℕ} (f : Coord s k → F) (c : Coord s k) :
    coordEval (coordOfFun f) c = f c := by
  rcases c with ⟨i, p⟩ | (h | h) <;> rfl

def suppEquiv (s k : ℕ) : Vec s k ≃ Finset (Coord s k) where
  toFun := supp
  invFun := ofSupp
  left_inv x := by
    apply (coordEquiv s k).injective
    funext c
    dsimp only [coordEquiv, Equiv.coe_fn_mk, ofSupp]
    rw [coordEval_coordOfFun]
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases f2_eq_zero_or_one (coordEval x c) with h | h <;> simp [h]
  right_inv T := by
    ext c
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, ofSupp, coordEval_coordOfFun]
    by_cases hc : c ∈ T <;> simp [hc]

lemma sum_subset_interval_f2 {α : Type*} [Fintype α] [DecidableEq α] (U T : Finset α) :
    (∑ S : Finset α, if U ⊆ S ∧ S ⊆ T then (1 : F) else 0) = if U = T then 1 else 0 := by
  by_cases hsub : U ⊆ T
  · by_cases heq : U = T
    · subst heq
      rw [if_pos rfl]
      rw [Finset.sum_eq_single U]
      · simp
      · intro S _ hne
        rw [if_neg]
        intro h
        exact hne (Finset.Subset.antisymm h.2 h.1)
      · intro h; exact absurd (Finset.mem_univ U) h
    · rw [if_neg heq]
      have hssub : U ⊂ T := ssubset_iff_subset_ne.mpr ⟨hsub, heq⟩
      obtain ⟨c, hcT, hcU⟩ := Finset.exists_of_ssubset hssub
      let flip : Finset α → Finset α := fun S => if c ∈ S then S.erase c else insert c S
      have hflip_inv : ∀ S, flip (flip S) = S := by
        intro S
        by_cases hc : c ∈ S
        · simp [flip, hc, Finset.insert_erase hc]
        · simp [flip, hc, Finset.erase_insert hc]
      have hflip_mem : ∀ S, (U ⊆ flip S ∧ flip S ⊆ T) ↔ (U ⊆ S ∧ S ⊆ T) := by
        intro S
        constructor
        · intro h
          have h' : U ⊆ flip (flip S) ∧ flip (flip S) ⊆ T := by
            by_cases hc : c ∈ flip S
            · refine ⟨?_, ?_⟩
              · intro x hx
                have hxf : x ∈ flip S := h.1 hx
                have hxc : x ≠ c := fun hxe => hcU (hxe ▸ hx)
                simp [flip, hc, hxc, hxf]
              · intro x hx
                simp only [flip, hc, ↓reduceIte, Finset.mem_erase] at hx
                exact h.2 hx.2
            · refine ⟨?_, ?_⟩
              · intro x hx
                simp only [flip, hc, ↓reduceIte, Finset.mem_insert]
                exact Or.inr (h.1 hx)
              · intro x hx
                simp only [flip, hc, ↓reduceIte, Finset.mem_insert] at hx
                rcases hx with rfl | hx
                · exact hcT
                · exact h.2 hx
          rwa [hflip_inv] at h'
        · intro h
          by_cases hc : c ∈ S
          · refine ⟨?_, ?_⟩
            · intro x hx
              have hxc : x ≠ c := fun hxe => hcU (hxe ▸ hx)
              simp [flip, hc, hxc, h.1 hx]
            · intro x hx
              simp only [flip, hc, ↓reduceIte, Finset.mem_erase] at hx
              exact h.2 hx.2
          · refine ⟨?_, ?_⟩
            · intro x hx
              simp only [flip, hc, ↓reduceIte, Finset.mem_insert]
              exact Or.inr (h.1 hx)
            · intro x hx
              simp only [flip, hc, ↓reduceIte, Finset.mem_insert] at hx
              rcases hx with rfl | hx
              · exact hcT
              · exact h.2 hx
      let A := (Finset.univ : Finset (Finset α)).filter (fun S => U ⊆ S ∧ S ⊆ T ∧ c ∈ S)
      let B := (Finset.univ : Finset (Finset α)).filter (fun S => U ⊆ S ∧ S ⊆ T ∧ c ∉ S)
      have hA_eq : A.card = B.card := by
        refine Finset.card_bij (fun S _ => flip S) ?_ ?_ ?_
        · intro S hS
          simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
          have hm := (hflip_mem S).mpr ⟨hS.1, hS.2.1⟩
          refine ⟨hm.1, hm.2, ?_⟩
          simp [flip, hS.2.2]
        · intro S₁ _ S₂ _ h
          have := congrArg flip h
          rwa [hflip_inv, hflip_inv] at this
        · intro S hS
          simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hS
          refine ⟨flip S, ?_, hflip_inv S⟩
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
          have hm := (hflip_mem S).mpr ⟨hS.1, hS.2.1⟩
          refine ⟨hm.1, hm.2, ?_⟩
          simp [flip, hS.2.2]
      have htot : (Finset.univ : Finset (Finset α)).filter (fun S => U ⊆ S ∧ S ⊆ T) = A ∪ B := by
        ext S
        simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      have hdj : Disjoint A B := by
        rw [Finset.disjoint_left]
        intro S h1 h2
        simp only [A, B, Finset.mem_filter] at h1 h2
        exact h2.2.2.2 h1.2.2.2
      rw [← Finset.sum_filter, htot, Finset.sum_union hdj, Finset.sum_const, Finset.sum_const,
          hA_eq, nsmul_eq_mul, mul_one, f2_add_self]
  · have hne : U ≠ T := fun h => hsub (h ▸ Finset.Subset.refl _)
    rw [if_neg hne]
    apply Finset.sum_eq_zero
    intro S _
    rw [if_neg]
    intro h
    exact hsub (Finset.Subset.trans h.1 h.2)

def Emat (s k : ℕ) : Matrix (Vec s k) (Finset (Coord s k)) F :=
  fun x S => ∏ c ∈ S, coordEval x c

def Einv (s k : ℕ) : Matrix (Finset (Coord s k)) (Vec s k) F :=
  fun S y => if supp y ⊆ S then 1 else 0

lemma Emat_eq_ite {s k : ℕ} (x : Vec s k) (S : Finset (Coord s k)) :
    Emat s k x S = if S ⊆ supp x then 1 else 0 := by
  dsimp only [Emat]
  by_cases h : S ⊆ supp x
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro c hc
    have hcx := h hc
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hcx
    exact hcx
  · rw [if_neg h]
    rw [Finset.not_subset] at h
    rcases h with ⟨c, hcS, hcx⟩
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hcx
    have h0 : coordEval x c = 0 := by
      rcases f2_eq_zero_or_one (coordEval x c) with h0 | h1
      · exact h0
      · exact absurd h1 hcx
    exact Finset.prod_eq_zero hcS h0

lemma Emat_mul_Einv (s k : ℕ) : Emat s k * Einv s k = 1 := by
  ext x y
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp_rw [Emat_eq_ite, Einv]
  have h1 : (∑ S : Finset (Coord s k),
      (if S ⊆ supp x then (1 : F) else 0) * (if supp y ⊆ S then 1 else 0)) =
      ∑ S : Finset (Coord s k), if supp y ⊆ S ∧ S ⊆ supp x then (1 : F) else 0 := by
    refine Finset.sum_congr rfl (fun S _ => ?_)
    by_cases h1 : S ⊆ supp x <;> by_cases h2 : supp y ⊆ S <;> simp [h1, h2]
  rw [h1, sum_subset_interval_f2]
  by_cases hxy : x = y
  · subst hxy; simp
  · have hne : supp y ≠ supp x := fun heq => hxy ((suppEquiv s k).injective heq.symm)
    simp [hxy, hne]

lemma Einv_mul_Emat (s k : ℕ) : Einv s k * Emat s k = 1 := by
  ext S T
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp_rw [Emat_eq_ite, Einv]
  rw [Fintype.sum_equiv (suppEquiv s k) _
      (fun U : Finset (Coord s k) => if T ⊆ U ∧ U ⊆ S then (1 : F) else 0)
      (fun y => by
        change (if supp y ⊆ S then (1 : F) else 0) * (if T ⊆ supp y then 1 else 0) =
          if T ⊆ supp y ∧ supp y ⊆ S then 1 else 0
        by_cases h1 : supp y ⊆ S <;> by_cases h2 : T ⊆ supp y <;> simp [h1, h2])]
  rw [sum_subset_interval_f2]
  by_cases hST : S = T
  · subst hST; simp
  · have hTS : T ≠ S := fun h => hST h.symm
    simp [hST, hTS]

lemma rank_conj_Emat {s k : ℕ}
    (C : Matrix (Finset (Coord s k)) (Finset (Coord s k)) F) :
    (Emat s k * C * (Emat s k).transpose).rank = C.rank := by
  have hle1 : (Emat s k * C * (Emat s k).transpose).rank ≤ C.rank :=
    le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)
  have hrec : C = Einv s k * (Emat s k * C * (Emat s k).transpose) * (Einv s k).transpose := by
    have hT : (Emat s k).transpose * (Einv s k).transpose = 1 := by
      rw [← Matrix.transpose_mul, Einv_mul_Emat, Matrix.transpose_one]
    calc
      C = 1 * C * 1 := by rw [Matrix.one_mul, Matrix.mul_one]
      _ = (Einv s k * Emat s k) * C * ((Emat s k).transpose * (Einv s k).transpose) := by
            rw [Einv_mul_Emat, hT]
      _ = Einv s k * (Emat s k * C * (Emat s k).transpose) * (Einv s k).transpose := by
            simp only [Matrix.mul_assoc]
  have hle2 : C.rank ≤ (Emat s k * C * (Emat s k).transpose).rank := by
    conv_lhs => rw [hrec]
    exact le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)
  exact le_antisymm hle1 hle2

-- ============================================================
-- Explicit monomial basis and coefficient matrix C
-- ============================================================

def mU {s k : ℕ} (h : Fin k) : Finset (Coord s k) := {Sum.inr (Sum.inl h)}
def mV {s k : ℕ} (h : Fin k) : Finset (Coord s k) := {Sum.inr (Sum.inr h)}
def mE {s k : ℕ} (i : Fin s) (p : Fin 2) : Finset (Coord s k) := {Sum.inl (i, p)}
def mEU {s k : ℕ} (i : Fin s) (p : Fin 2) (h : Fin k) : Finset (Coord s k) :=
  {Sum.inl (i, p), Sum.inr (Sum.inl h)}
def mEV {s k : ℕ} (i : Fin s) (p : Fin 2) (h : Fin k) : Finset (Coord s k) :=
  {Sum.inl (i, p), Sum.inr (Sum.inr h)}
def mEE {s k : ℕ} (i j : Fin s) (p q : Fin 2) : Finset (Coord s k) :=
  {Sum.inl (i, p), Sum.inl (j, q)}

lemma Emat_mU {s k : ℕ} (x : Vec s k) (h : Fin k) : Emat s k x (mU h) = x.2.1 h := by
  simp [Emat, mU, coordEval]

lemma Emat_mV {s k : ℕ} (x : Vec s k) (h : Fin k) : Emat s k x (mV h) = x.2.2 h := by
  simp [Emat, mV, coordEval]

lemma Emat_mE {s k : ℕ} (x : Vec s k) (i : Fin s) (p : Fin 2) :
    Emat s k x (mE i p) = x.1 i p := by
  simp [Emat, mE, coordEval]

lemma Emat_mEU {s k : ℕ} (x : Vec s k) (i : Fin s) (p : Fin 2) (h : Fin k) :
    Emat s k x (mEU i p h) = x.1 i p * x.2.1 h := by
  have hne : (Sum.inl (i, p) : Coord s k) ≠ Sum.inr (Sum.inl h) := by simp
  simp [Emat, mEU, coordEval, Finset.prod_pair hne]

lemma Emat_mEV {s k : ℕ} (x : Vec s k) (i : Fin s) (p : Fin 2) (h : Fin k) :
    Emat s k x (mEV i p h) = x.1 i p * x.2.2 h := by
  have hne : (Sum.inl (i, p) : Coord s k) ≠ Sum.inr (Sum.inr h) := by simp
  simp [Emat, mEV, coordEval, Finset.prod_pair hne]

lemma Emat_mEE {s k : ℕ} (x : Vec s k) {i j : Fin s} (hij : i < j) (p q : Fin 2) :
    Emat s k x (mEE i j p q) = x.1 i p * x.1 j q := by
  have hne : (Sum.inl (i, p) : Coord s k) ≠ Sum.inl (j, q) := by
    intro h
    have := congrArg Prod.fst (Sum.inl.inj h)
    exact ne_of_lt hij this
  simp [Emat, mEE, coordEval, Finset.prod_pair hne]

lemma Emat_single_EmatT {s k : ℕ} (S T : Finset (Coord s k)) (v : F) (x y : Vec s k) :
    (Emat s k * Matrix.single S T v * (Emat s k).transpose) x y = v * Emat s k x S * Emat s k y T := by
  rw [Matrix.mul_apply]
  have h1 : ∀ U, (Emat s k * Matrix.single S T v) x U = if U = T then Emat s k x S * v else 0 := by
    intro U
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single S]
    · by_cases hUT : U = T
      · subst hUT; simp [Matrix.single_apply]
      · simp [Matrix.single_apply, hUT, Ne.symm hUT]
    · intro W _ hWS
      have : Matrix.single S T v W U = 0 := by
        simp [Matrix.single_apply, hWS.symm]
      rw [this, mul_zero]
    · intro h; exact absurd (Finset.mem_univ S) h
  simp_rw [h1, Matrix.transpose_apply]
  rw [Finset.sum_eq_single T]
  · simp only [↓reduceIte]; ring
  · intro U _ hUT; simp [hUT]
  · intro h; exact absurd (Finset.mem_univ T) h

def cDiag {s k : ℕ} (a b : Fin s → Fin k → F) (d : Fin s → F) (i : Fin s) : F :=
  d i + ∑ h : Fin k, a i h * b i h

def omega {s k : ℕ} (a b : Fin s → Fin k → F) (i j : Fin s) : F :=
  ∑ h : Fin k, (a i h * b j h + b i h * a j h)

def Cmat {s k : ℕ} (a b : Fin s → Fin k → F) (d : Fin s → F) :
    Matrix (Finset (Coord s k)) (Finset (Coord s k)) F :=
  (∑ h : Fin k, (Matrix.single (mU h) (mV h) 1 + Matrix.single (mV h) (mU h) 1)) +
  (∑ i : Fin s, ∑ p : Fin 2,
    (Matrix.single (mE i p) (mE i p) (cDiag a b d i) +
      ∑ h : Fin k,
        (Matrix.single (mEU i p h) (mE i p) (b i h) +
         Matrix.single (mEV i p h) (mE i p) (a i h) +
         Matrix.single (mE i p) (mEU i p h) (b i h) +
         Matrix.single (mE i p) (mEV i p h) (a i h)))) +
  (∑ i : Fin s, ∑ j : Fin s, if i < j then
    ∑ p : Fin 2, ∑ q : Fin 2, Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mEE i j p q) (mEE i j p q) (omega a b i j) else 0)

lemma sum_pairs_symm {s : ℕ} (f : Fin s → Fin s → F) :
    (∑ i : Fin s, ∑ j : Fin s, f i j) =
      (∑ i : Fin s, f i i) +
      ∑ i : Fin s, ∑ j : Fin s, if i < j then (f i j + f j i) else 0 := by
  have hsplit : ∀ i j : Fin s,
      f i j = (if i = j then f i j else 0) +
              (if i < j then f i j else 0) +
              (if j < i then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · have hne : i ≠ j := ne_of_lt hlt
      have hng : ¬ j < i := not_lt_of_gt hlt
      simp [hlt, hne, hng]
    · simp
    · have hne : i ≠ j := ne_of_gt hgt
      have hnl : ¬ i < j := not_lt_of_gt hgt
      simp [hgt, hne, hnl]
  conv_lhs =>
    arg 2; ext i; arg 2; ext j
    rw [hsplit i j]
  simp_rw [Finset.sum_add_distrib]
  have hdiag : (∑ i : Fin s, ∑ j : Fin s, if i = j then f i j else 0) = ∑ i : Fin s, f i i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp
  have hswap : (∑ i : Fin s, ∑ j : Fin s, if j < i then f i j else 0) =
      ∑ i : Fin s, ∑ j : Fin s, if i < j then f j i else 0 := by
    rw [Finset.sum_comm]
  rw [hdiag, hswap, add_assoc]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs <;> ring

lemma X_eq_conj_Cmat {s k : ℕ} (a b : Fin s → Fin k → F) (d : Fin s → F) :
    let g := fun (i : Fin s) (x y : Vec s k) => ∑ p : Fin 2, x.1 i p * y.1 i p
    let val := fun (x y : Vec s k) =>
      (∑ h : Fin k,
        (x.2.1 h + y.2.1 h + ∑ i : Fin s, a i h * g i x y) *
        (x.2.2 h + y.2.2 h + ∑ i : Fin s, b i h * g i x y)) +
        ∑ i : Fin s, d i * g i x y
    (fun x y : Vec s k => val x y + val x 0 + val 0 y + val 0 0) =
      Emat s k * Cmat a b d * (Emat s k).transpose := by
  intro g val
  ext x y
  -- Evaluate RHS
  have hrhs : (Emat s k * Cmat a b d * (Emat s k).transpose) x y =
      (∑ h : Fin k, (x.2.1 h * y.2.2 h + x.2.2 h * y.2.1 h)) +
      (∑ i : Fin s, ∑ p : Fin 2,
        (cDiag a b d i * x.1 i p * y.1 i p +
          ∑ h : Fin k,
            (b i h * (x.1 i p * x.2.1 h) * y.1 i p +
             a i h * (x.1 i p * x.2.2 h) * y.1 i p +
             b i h * x.1 i p * (y.1 i p * y.2.1 h) +
             a i h * x.1 i p * (y.1 i p * y.2.2 h)))) +
      (∑ i : Fin s, ∑ j : Fin s, if i < j then
        ∑ p : Fin 2, ∑ q : Fin 2, omega a b i j * (x.1 i p * x.1 j q) * (y.1 i p * y.1 j q) else 0) := by
    dsimp only [Cmat]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply,
               Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply,
               Emat_single_EmatT, Emat_mU, Emat_mV, Emat_mE, Emat_mEU, Emat_mEV]
    congr 1
    · congr 1
      · refine Finset.sum_congr rfl (fun h _ => by ring)
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases hij : i < j
      · simp only [hij, ↓reduceIte, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply,
                   Emat_single_EmatT, Emat_mEE _ hij]
      · simp [hij]
  rw [hrhs]
  -- Evaluate LHS
  have hg0l : ∀ i, g i 0 y = 0 := fun i => by simp [g]
  have hg0r : ∀ i, g i x 0 = 0 := fun i => by simp [g]
  have hvx0 : val x 0 = ∑ h : Fin k, x.2.1 h * x.2.2 h := by simp [val, hg0r]
  have hv0y : val 0 y = ∑ h : Fin k, y.2.1 h * y.2.2 h := by simp [val, hg0l]
  have hg00 : ∀ i, g i 0 0 = 0 := fun i => by simp [g]
  have hv00 : val 0 0 = 0 := by simp [val, hg00]
  rw [hvx0, hv0y, hv00, add_zero]
  dsimp only [val]
  have hexp_h : ∀ h : Fin k,
      (x.2.1 h + y.2.1 h + ∑ i : Fin s, a i h * g i x y) *
        (x.2.2 h + y.2.2 h + ∑ j : Fin s, b j h * g j x y) +
        x.2.1 h * x.2.2 h + y.2.1 h * y.2.2 h =
      (x.2.1 h * y.2.2 h + x.2.2 h * y.2.1 h) +
      (∑ i : Fin s, (b i h * x.2.1 h + a i h * x.2.2 h + b i h * y.2.1 h + a i h * y.2.2 h) * g i x y) +
      (∑ i : Fin s, ∑ j : Fin s, a i h * b j h * (g i x y * g j x y)) := by
    intro h
    have hmul :
        (∑ i : Fin s, a i h * g i x y) * (∑ j : Fin s, b j h * g j x y) =
          ∑ i : Fin s, ∑ j : Fin s, a i h * b j h * (g i x y * g j x y) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    have hlin :
        (x.2.1 h + y.2.1 h) * (∑ i : Fin s, b i h * g i x y) +
        (∑ i : Fin s, a i h * g i x y) * (x.2.2 h + y.2.2 h) =
        ∑ i : Fin s, (b i h * x.2.1 h + a i h * x.2.2 h + b i h * y.2.1 h + a i h * y.2.2 h) * g i x y := by
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    have h1 :
        (x.2.1 h + y.2.1 h + ∑ i : Fin s, a i h * g i x y) *
          (x.2.2 h + y.2.2 h + ∑ j : Fin s, b j h * g j x y) +
          x.2.1 h * x.2.2 h + y.2.1 h * y.2.2 h =
        (x.2.1 h * x.2.2 h + x.2.1 h * x.2.2 h) + (y.2.1 h * y.2.2 h + y.2.1 h * y.2.2 h) +
        (x.2.1 h * y.2.2 h + x.2.2 h * y.2.1 h) +
        ((x.2.1 h + y.2.1 h) * (∑ i : Fin s, b i h * g i x y) +
         (∑ i : Fin s, a i h * g i x y) * (x.2.2 h + y.2.2 h)) +
        (∑ i : Fin s, a i h * g i x y) * (∑ j : Fin s, b j h * g j x y) := by ring
    rw [h1, f2_add_self, f2_add_self, zero_add, zero_add, hlin, hmul]
  have hlhs_group :
      (∑ h : Fin k,
        (x.2.1 h + y.2.1 h + ∑ i : Fin s, a i h * g i x y) *
        (x.2.2 h + y.2.2 h + ∑ i : Fin s, b i h * g i x y)) +
        (∑ i : Fin s, d i * g i x y) +
        (∑ h : Fin k, x.2.1 h * x.2.2 h) +
        (∑ h : Fin k, y.2.1 h * y.2.2 h) =
      (∑ h : Fin k,
        ((x.2.1 h + y.2.1 h + ∑ i : Fin s, a i h * g i x y) *
         (x.2.2 h + y.2.2 h + ∑ j : Fin s, b j h * g j x y) +
         x.2.1 h * x.2.2 h + y.2.1 h * y.2.2 h)) +
        ∑ i : Fin s, d i * g i x y := by
    simp_rw [Finset.sum_add_distrib]
    ring
  rw [hlhs_group]
  simp_rw [hexp_h, Finset.sum_add_distrib]
  -- Swap sums in double sum over h, i, j
  have hquad :
      (∑ h : Fin k, ∑ i : Fin s, ∑ j : Fin s, a i h * b j h * (g i x y * g j x y)) =
      (∑ i : Fin s, (∑ h : Fin k, a i h * b i h) * g i x y) +
      (∑ i : Fin s, ∑ j : Fin s, if i < j then omega a b i j * (g i x y * g j x y) else 0) := by
    have hsw :
        (∑ h : Fin k, ∑ i : Fin s, ∑ j : Fin s, a i h * b j h * (g i x y * g j x y)) =
        ∑ i : Fin s, ∑ j : Fin s, (∑ h : Fin k, a i h * b j h) * (g i x y * g j x y) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Finset.sum_mul]
    rw [hsw, sum_pairs_symm]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      have hsq : g i x y * g i x y = g i x y := f2_sq_sum Finset.univ (fun p => x.1 i p * y.1 i p)
      rw [hsq]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      split_ifs
      · dsimp only [omega]
        rw [mul_comm (g j x y) (g i x y), ← add_mul, ← Finset.sum_add_distrib]
        refine congrArg (· * (g i x y * g j x y)) ?_
        refine Finset.sum_congr rfl (fun h _ => by ring)
      · rfl
  rw [hquad]
  have hpair_exp :
      (∑ i : Fin s, ∑ j : Fin s, if i < j then omega a b i j * (g i x y * g j x y) else 0) =
      ∑ i : Fin s, ∑ j : Fin s, if i < j then
        ∑ p : Fin 2, ∑ q : Fin 2, omega a b i j * (x.1 i p * x.1 j q) * (y.1 i p * y.1 j q) else 0 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs
    · dsimp only [g]
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun q _ => by ring)
    · rfl
  have hmid :
      (∑ h : Fin k, ∑ i : Fin s,
        (b i h * x.2.1 h + a i h * x.2.2 h + b i h * y.2.1 h + a i h * y.2.2 h) * g i x y) +
      (∑ i : Fin s, (∑ h : Fin k, a i h * b i h) * g i x y) +
      (∑ i : Fin s, d i * g i x y) =
      ∑ i : Fin s, ∑ p : Fin 2,
        (cDiag a b d i * x.1 i p * y.1 i p +
          ∑ h : Fin k,
            (b i h * (x.1 i p * x.2.1 h) * y.1 i p +
             a i h * (x.1 i p * x.2.2 h) * y.1 i p +
             b i h * x.1 i p * (y.1 i p * y.2.1 h) +
             a i h * x.1 i p * (y.1 i p * y.2.2 h))) := by
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun h i => (b i h * x.2.1 h + a i h * x.2.2 h + b i h * y.2.1 h + a i h * y.2.2 h) * g i x y)]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    dsimp only [g, cDiag]
    rw [Finset.sum_add_distrib]
    have h1 :
        (∑ h : Fin k, (b i h * x.2.1 h + a i h * x.2.2 h + b i h * y.2.1 h + a i h * y.2.2 h) *
          ∑ p : Fin 2, x.1 i p * y.1 i p) =
        ∑ p : Fin 2, ∑ h : Fin k,
          (b i h * (x.1 i p * x.2.1 h) * y.1 i p +
           a i h * (x.1 i p * x.2.2 h) * y.1 i p +
           b i h * x.1 i p * (y.1 i p * y.2.1 h) +
           a i h * x.1 i p * (y.1 i p * y.2.2 h)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun h _ => by ring))
    have h2 :
        (∑ h : Fin k, a i h * b i h) * (∑ p : Fin 2, x.1 i p * y.1 i p) +
        d i * (∑ p : Fin 2, x.1 i p * y.1 i p) =
        ∑ p : Fin 2, (d i + ∑ h : Fin k, a i h * b i h) * x.1 i p * y.1 i p := by
      rw [← add_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun p _ => by ring)
    rw [h1, add_assoc, h2, add_comm]
  rw [hpair_exp]
  simp_rw [Finset.sum_add_distrib] at hmid
  linear_combination hmid

-- ============================================================
-- Exact row/column space basis of Cmat
-- ============================================================

lemma single_transpose_eq {α : Type*} [DecidableEq α] (A B : α) (v : F) :
    (Matrix.single A B v).transpose = Matrix.single B A v := by
  ext S T
  simp [Matrix.transpose_apply, Matrix.single_apply, and_comm]

lemma Cmat_symm {s k : ℕ} (a b : Fin s → Fin k → F) (d : Fin s → F) :
    (Cmat a b d).transpose = Cmat a b d := by
  dsimp only [Cmat]
  rw [Matrix.transpose_add, Matrix.transpose_add]
  congr 1
  · congr 1
    · rw [Matrix.transpose_sum]
      refine Finset.sum_congr rfl (fun h _ => ?_)
      rw [Matrix.transpose_add, single_transpose_eq, single_transpose_eq, add_comm]
    · rw [Matrix.transpose_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Matrix.transpose_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Matrix.transpose_add, single_transpose_eq, Matrix.transpose_sum]
      congr 1
      refine Finset.sum_congr rfl (fun h _ => ?_)
      rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_add,
          single_transpose_eq, single_transpose_eq, single_transpose_eq, single_transpose_eq]
      abel
  · rw [Matrix.transpose_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Matrix.transpose_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs
    · rw [Matrix.transpose_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Matrix.transpose_sum]
      refine Finset.sum_congr rfl (fun q _ => single_transpose_eq _ _ _)
    · exact Matrix.transpose_zero

-- Disjointness lemmas for monomial Finsets
lemma mU_ne_mV {s k : ℕ} (h₁ h₂ : Fin k) : (mU h₁ : Finset (Coord s k)) ≠ mV h₂ := by
  intro h
  have : (Sum.inr (Sum.inl h₁) : Coord s k) ∈ mV h₂ := h ▸ Finset.mem_singleton_self _
  simp [mV] at this

lemma mU_ne_mE {s k : ℕ} (h : Fin k) (i : Fin s) (p : Fin 2) :
    (mU h : Finset (Coord s k)) ≠ mE i p := by
  intro heq
  have : (Sum.inr (Sum.inl h) : Coord s k) ∈ mE i p := heq ▸ Finset.mem_singleton_self _
  simp [mE] at this

lemma mV_ne_mE {s k : ℕ} (h : Fin k) (i : Fin s) (p : Fin 2) :
    (mV h : Finset (Coord s k)) ≠ mE i p := by
  intro heq
  have : (Sum.inr (Sum.inr h) : Coord s k) ∈ mE i p := heq ▸ Finset.mem_singleton_self _
  simp [mE] at this

lemma card_mU {s k : ℕ} (h : Fin k) : (mU h : Finset (Coord s k)).card = 1 :=
  Finset.card_singleton _

lemma card_mV {s k : ℕ} (h : Fin k) : (mV h : Finset (Coord s k)).card = 1 :=
  Finset.card_singleton _

lemma card_mE {s k : ℕ} (i : Fin s) (p : Fin 2) : (mE i p : Finset (Coord s k)).card = 1 :=
  Finset.card_singleton _

lemma card_mEU {s k : ℕ} (i : Fin s) (p : Fin 2) (h : Fin k) :
    (mEU i p h : Finset (Coord s k)).card = 2 := by
  exact Finset.card_pair (by simp)

lemma card_mEV {s k : ℕ} (i : Fin s) (p : Fin 2) (h : Fin k) :
    (mEV i p h : Finset (Coord s k)).card = 2 := by
  exact Finset.card_pair (by simp)

lemma card_mEE {s k : ℕ} {i j : Fin s} (hij : i < j) (p q : Fin 2) :
    (mEE i j p q : Finset (Coord s k)).card = 2 := by
  refine Finset.card_pair ?_
  intro h
  exact ne_of_lt hij (congrArg Prod.fst (Sum.inl.inj h))

lemma card_ne_one_of_two {α : Type*} {S T : Finset α} (hS : S.card = 1) (hT : T.card = 2) :
    S ≠ T := fun h => by rw [h, hT] at hS; omega

lemma mEU_ne_mEV {s k : ℕ} (i₁ i₂ : Fin s) (p₁ p₂ : Fin 2) (h₁ h₂ : Fin k) :
    (mEU i₁ p₁ h₁ : Finset (Coord s k)) ≠ mEV i₂ p₂ h₂ := by
  intro h
  have : (Sum.inr (Sum.inl h₁) : Coord s k) ∈ mEV i₂ p₂ h₂ := h ▸ by simp [mEU]
  simp [mEV] at this

lemma mEU_ne_mEE {s k : ℕ} (i₁ i₂ j₂ : Fin s) (p₁ p₂ q₂ : Fin 2) (h₁ : Fin k) :
    (mEU i₁ p₁ h₁ : Finset (Coord s k)) ≠ mEE i₂ j₂ p₂ q₂ := by
  intro h
  have : (Sum.inr (Sum.inl h₁) : Coord s k) ∈ mEE i₂ j₂ p₂ q₂ := h ▸ by simp [mEU]
  simp [mEE] at this

lemma mEV_ne_mEE {s k : ℕ} (i₁ i₂ j₂ : Fin s) (p₁ p₂ q₂ : Fin 2) (h₁ : Fin k) :
    (mEV i₁ p₁ h₁ : Finset (Coord s k)) ≠ mEE i₂ j₂ p₂ q₂ := by
  intro h
  have : (Sum.inr (Sum.inr h₁) : Coord s k) ∈ mEE i₂ j₂ p₂ q₂ := h ▸ by simp [mEV]
  simp [mEE] at this

lemma mU_inj {s k : ℕ} {h₁ h₂ : Fin k} (h : (mU h₁ : Finset (Coord s k)) = mU h₂) : h₁ = h₂ := by
  have : (Sum.inr (Sum.inl h₁) : Coord s k) ∈ mU h₂ := h ▸ Finset.mem_singleton_self _
  simpa [mU] using this

lemma mV_inj {s k : ℕ} {h₁ h₂ : Fin k} (h : (mV h₁ : Finset (Coord s k)) = mV h₂) : h₁ = h₂ := by
  have : (Sum.inr (Sum.inr h₁) : Coord s k) ∈ mV h₂ := h ▸ Finset.mem_singleton_self _
  simpa [mV] using this

lemma mE_inj {s k : ℕ} {i₁ i₂ : Fin s} {p₁ p₂ : Fin 2}
    (h : (mE i₁ p₁ : Finset (Coord s k)) = mE i₂ p₂) : i₁ = i₂ ∧ p₁ = p₂ := by
  have : (Sum.inl (i₁, p₁) : Coord s k) ∈ mE i₂ p₂ := h ▸ Finset.mem_singleton_self _
  simpa [mE] using this

lemma mEU_inj {s k : ℕ} {i₁ i₂ : Fin s} {p₁ p₂ : Fin 2} {h₁ h₂ : Fin k}
    (h : (mEU i₁ p₁ h₁ : Finset (Coord s k)) = mEU i₂ p₂ h₂) : i₁ = i₂ ∧ p₁ = p₂ ∧ h₁ = h₂ := by
  have h1 : (Sum.inl (i₁, p₁) : Coord s k) ∈ mEU i₂ p₂ h₂ := h ▸ by simp [mEU]
  have h2 : (Sum.inr (Sum.inl h₁) : Coord s k) ∈ mEU i₂ p₂ h₂ := h ▸ by simp [mEU]
  simp [mEU] at h1 h2
  exact ⟨h1.1, h1.2, h2⟩

lemma mEV_inj {s k : ℕ} {i₁ i₂ : Fin s} {p₁ p₂ : Fin 2} {h₁ h₂ : Fin k}
    (h : (mEV i₁ p₁ h₁ : Finset (Coord s k)) = mEV i₂ p₂ h₂) : i₁ = i₂ ∧ p₁ = p₂ ∧ h₁ = h₂ := by
  have h1 : (Sum.inl (i₁, p₁) : Coord s k) ∈ mEV i₂ p₂ h₂ := h ▸ by simp [mEV]
  have h2 : (Sum.inr (Sum.inr h₁) : Coord s k) ∈ mEV i₂ p₂ h₂ := h ▸ by simp [mEV]
  simp [mEV] at h1 h2
  exact ⟨h1.1, h1.2, h2⟩

lemma mEE_inj {s k : ℕ} {i₁ j₁ i₂ j₂ : Fin s} (h₁ : i₁ < j₁) (h₂ : i₂ < j₂)
    {p₁ q₁ p₂ q₂ : Fin 2}
    (h : (mEE i₁ j₁ p₁ q₁ : Finset (Coord s k)) = mEE i₂ j₂ p₂ q₂) :
    i₁ = i₂ ∧ j₁ = j₂ ∧ p₁ = p₂ ∧ q₁ = q₂ := by
  have hm1 : (Sum.inl (i₁, p₁) : Coord s k) ∈ mEE i₂ j₂ p₂ q₂ := h ▸ by simp [mEE]
  have hm2 : (Sum.inl (j₁, q₁) : Coord s k) ∈ mEE i₂ j₂ p₂ q₂ := h ▸ by simp [mEE]
  simp [mEE] at hm1 hm2
  rcases hm1 with ⟨hi, hp⟩ | ⟨hi, hp⟩
  · rcases hm2 with ⟨hj, hq⟩ | ⟨hj, hq⟩
    · exfalso; exact ne_of_lt h₁ (hi.trans hj.symm)
    · exact ⟨hi, hj, hp, hq⟩
  · rcases hm2 with ⟨hj, hq⟩ | ⟨hj, hq⟩
    · exfalso; exact not_lt_of_gt h₂ (hj ▸ hi ▸ h₁)
    · exfalso; exact ne_of_lt h₁ (hi.trans hj.symm)

-- Compute rows of Cmat explicitly
def wVec {s k : ℕ} (a b : Fin s → Fin k → F) (i : Fin s) (p : Fin 2) :
    Finset (Coord s k) → F :=
  ∑ h : Fin k, (b i h • Pi.single (mEU i p h) (1 : F) + a i h • Pi.single (mEV i p h) (1 : F))

lemma Cmat_row_mU {s k : ℕ} (a b : Fin s → Fin k → F) (d : Fin s → F) (h₀ : Fin k) :
    Cmat a b d (mU h₀) = Pi.single (mV h₀) (1 : F) := by
  ext T
  dsimp only [Cmat]
  simp only [Matrix.add_apply, Matrix.sum_apply, Pi.single_apply]
  have h1 : (∑ h : Fin k, (Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mU h) (mV h) (1 : F) (mU h₀) T +
      Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mV h) (mU h) (1 : F) (mU h₀) T)) = if T = mV h₀ then 1 else 0 := by
    rw [Finset.sum_eq_single h₀]
    · simp [Matrix.single_apply, (mU_ne_mV h₀ h₀).symm, eq_comm]
    · intro h _ hne
      have hU : (mU h : Finset (Coord s k)) ≠ mU h₀ := fun heq => hne (mU_inj heq)
      simp [Matrix.single_apply, hU, (mU_ne_mV h₀ h).symm]
    · intro h; exact absurd (Finset.mem_univ h₀) h
  have h2 : (∑ i : Fin s, ∑ p : Fin 2,
      (Matrix.single (mE i p) (mE i p) (cDiag a b d i) (mU h₀) T +
       ∑ h : Fin k,
         (Matrix.single (mEU i p h) (mE i p) (b i h) (mU h₀) T +
          Matrix.single (mEV i p h) (mE i p) (a i h) (mU h₀) T +
          Matrix.single (mE i p) (mEU i p h) (b i h) (mU h₀) T +
          Matrix.single (mE i p) (mEV i p h) (a i h) (mU h₀) T))) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro p _
    have hE : mE i p ≠ mU h₀ := (mU_ne_mE h₀ i p).symm
    have hEU : ∀ h, mEU i p h ≠ mU h₀ := fun h => (card_ne_one_of_two (card_mU h₀) (card_mEU i p h)).symm
    have hEV : ∀ h, mEV i p h ≠ mU h₀ := fun h => (card_ne_one_of_two (card_mU h₀) (card_mEV i p h)).symm
    simp [Matrix.single_apply, hE, hEU, hEV]
  have h3 : (∑ i : Fin s, ∑ j : Fin s,
      (if i < j then ∑ p : Fin 2, ∑ q : Fin 2,
        Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mEE i j p q) (mEE i j p q) (omega a b i j) else (0 : Matrix (Finset (Coord s k)) (Finset (Coord s k)) F)) (mU h₀) T) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    split_ifs with hij
    · simp only [Matrix.sum_apply, Matrix.single_apply]
      apply Finset.sum_eq_zero; intro p _
      apply Finset.sum_eq_zero; intro q _
      have hEE : mEE i j p q ≠ mU h₀ := (card_ne_one_of_two (card_mU h₀) (card_mEE hij p q)).symm
      simp [hEE]
    · rfl
  rw [h1, h2, h3, add_zero, add_zero]

lemma Cmat_row_mV {s k : ℕ} (a b : Fin s → Fin k → F) (d : Fin s → F) (h₀ : Fin k) :
    Cmat a b d (mV h₀) = Pi.single (mU h₀) (1 : F) := by
  ext T
  dsimp only [Cmat]
  simp only [Matrix.add_apply, Matrix.sum_apply, Pi.single_apply]
  have h1 : (∑ h : Fin k, (Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mU h) (mV h) (1 : F) (mV h₀) T +
      Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mV h) (mU h) (1 : F) (mV h₀) T)) = if T = mU h₀ then 1 else 0 := by
    rw [Finset.sum_eq_single h₀]
    · simp [Matrix.single_apply, mU_ne_mV h₀ h₀, eq_comm]
    · intro h _ hne
      have hV : (mV h : Finset (Coord s k)) ≠ mV h₀ := fun heq => hne (mV_inj heq)
      simp [Matrix.single_apply, hV, mU_ne_mV h h₀]
    · intro h; exact absurd (Finset.mem_univ h₀) h
  have h2 : (∑ i : Fin s, ∑ p : Fin 2,
      (Matrix.single (mE i p) (mE i p) (cDiag a b d i) (mV h₀) T +
       ∑ h : Fin k,
         (Matrix.single (mEU i p h) (mE i p) (b i h) (mV h₀) T +
          Matrix.single (mEV i p h) (mE i p) (a i h) (mV h₀) T +
          Matrix.single (mE i p) (mEU i p h) (b i h) (mV h₀) T +
          Matrix.single (mE i p) (mEV i p h) (a i h) (mV h₀) T))) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro p _
    have hE : mE i p ≠ mV h₀ := (mV_ne_mE h₀ i p).symm
    have hEU : ∀ h, mEU i p h ≠ mV h₀ := fun h => (card_ne_one_of_two (card_mV h₀) (card_mEU i p h)).symm
    have hEV : ∀ h, mEV i p h ≠ mV h₀ := fun h => (card_ne_one_of_two (card_mV h₀) (card_mEV i p h)).symm
    simp [Matrix.single_apply, hE, hEU, hEV]
  have h3 : (∑ i : Fin s, ∑ j : Fin s,
      (if i < j then ∑ p : Fin 2, ∑ q : Fin 2,
        Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mEE i j p q) (mEE i j p q) (omega a b i j) else (0 : Matrix (Finset (Coord s k)) (Finset (Coord s k)) F)) (mV h₀) T) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    split_ifs with hij
    · simp only [Matrix.sum_apply, Matrix.single_apply]
      apply Finset.sum_eq_zero; intro p _
      apply Finset.sum_eq_zero; intro q _
      have hEE : mEE i j p q ≠ mV h₀ := (card_ne_one_of_two (card_mV h₀) (card_mEE hij p q)).symm
      simp [hEE]
    · rfl
  rw [h1, h2, h3, add_zero, add_zero]

lemma Cmat_row_mE {s k : ℕ} (a b : Fin s → Fin k → F) (d : Fin s → F)
    (i₀ : Fin s) (p₀ : Fin 2) :
    Cmat a b d (mE i₀ p₀) = cDiag a b d i₀ • Pi.single (mE i₀ p₀) (1 : F) + wVec a b i₀ p₀ := by
  ext T
  dsimp only [Cmat, wVec]
  simp only [Matrix.add_apply, Matrix.sum_apply, Pi.add_apply, Pi.smul_apply,
             Finset.sum_apply, smul_eq_mul, Pi.single_apply]
  have h1 : (∑ h : Fin k, (Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mU h) (mV h) (1 : F) (mE i₀ p₀) T +
      Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mV h) (mU h) (1 : F) (mE i₀ p₀) T)) = 0 := by
    apply Finset.sum_eq_zero; intro h _
    simp [Matrix.single_apply, mU_ne_mE h i₀ p₀, mV_ne_mE h i₀ p₀]
  have h3 : (∑ i : Fin s, ∑ j : Fin s,
      (if i < j then ∑ p : Fin 2, ∑ q : Fin 2,
        Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mEE i j p q) (mEE i j p q) (omega a b i j) else (0 : Matrix (Finset (Coord s k)) (Finset (Coord s k)) F)) (mE i₀ p₀) T) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    split_ifs with hij
    · simp only [Matrix.sum_apply, Matrix.single_apply]
      apply Finset.sum_eq_zero; intro p _
      apply Finset.sum_eq_zero; intro q _
      have hEE : (mEE i j p q : Finset (Coord s k)) ≠ mE i₀ p₀ := (card_ne_one_of_two (card_mE (k := k) i₀ p₀) (card_mEE (k := k) hij p q)).symm
      simp [hEE]
    · rfl
  have h2 : (∑ i : Fin s, ∑ p : Fin 2,
      (Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mE i p) (mE i p) (cDiag a b d i) (mE i₀ p₀) T +
       ∑ h : Fin k,
         (Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mEU i p h) (mE i p) (b i h) (mE i₀ p₀) T +
          Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mEV i p h) (mE i p) (a i h) (mE i₀ p₀) T +
          Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mE i p) (mEU i p h) (b i h) (mE i₀ p₀) T +
          Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mE i p) (mEV i p h) (a i h) (mE i₀ p₀) T))) =
      cDiag a b d i₀ * (if T = mE i₀ p₀ then 1 else 0) +
      ∑ h : Fin k, (b i₀ h * (if T = mEU i₀ p₀ h then 1 else 0) +
                    a i₀ h * (if T = mEV i₀ p₀ h then 1 else 0)) := by
    rw [Finset.sum_eq_single i₀]
    · rw [Finset.sum_eq_single p₀]
      · congr 1
        · simp [Matrix.single_apply, eq_comm]
        · refine Finset.sum_congr rfl (fun h _ => ?_)
          have hEU : mEU i₀ p₀ h ≠ mE i₀ p₀ := (card_ne_one_of_two (card_mE i₀ p₀) (card_mEU i₀ p₀ h)).symm
          have hEV : mEV i₀ p₀ h ≠ mE i₀ p₀ := (card_ne_one_of_two (card_mE i₀ p₀) (card_mEV i₀ p₀ h)).symm
          simp [Matrix.single_apply, hEU, hEV, eq_comm]
      · intro p _ hp
        have hE : (mE i₀ p : Finset (Coord s k)) ≠ mE i₀ p₀ := fun heq => hp (mE_inj heq).2
        have hEU : ∀ h : Fin k, mEU i₀ p h ≠ mE i₀ p₀ := fun h => (card_ne_one_of_two (card_mE i₀ p₀) (card_mEU i₀ p h)).symm
        have hEV : ∀ h : Fin k, mEV i₀ p h ≠ mE i₀ p₀ := fun h => (card_ne_one_of_two (card_mE i₀ p₀) (card_mEV i₀ p h)).symm
        simp [Matrix.single_apply, hE, hEU, hEV]
      · intro h; exact absurd (Finset.mem_univ p₀) h
    · intro i _ hi
      apply Finset.sum_eq_zero; intro p _
      have hE : (mE i p : Finset (Coord s k)) ≠ mE i₀ p₀ := fun heq => hi (mE_inj heq).1
      have hEU : ∀ h : Fin k, mEU i p h ≠ mE i₀ p₀ := fun h => (card_ne_one_of_two (card_mE i₀ p₀) (card_mEU i p h)).symm
      have hEV : ∀ h : Fin k, mEV i p h ≠ mE i₀ p₀ := fun h => (card_ne_one_of_two (card_mE i₀ p₀) (card_mEV i p h)).symm
      simp [Matrix.single_apply, hE, hEU, hEV]
    · intro h; exact absurd (Finset.mem_univ i₀) h
  rw [h1, h2, h3, zero_add, add_zero]

lemma Cmat_row_mEU {s k : ℕ} (a b : Fin s → Fin k → F) (d : Fin s → F)
    (i₀ : Fin s) (p₀ : Fin 2) (h₀ : Fin k) :
    Cmat a b d (mEU i₀ p₀ h₀) = b i₀ h₀ • Pi.single (mE i₀ p₀) (1 : F) := by
  ext T
  dsimp only [Cmat]
  simp only [Matrix.add_apply, Matrix.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  have h1 : (∑ h : Fin k, (Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mU h) (mV h) (1 : F) (mEU i₀ p₀ h₀) T +
      Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mV h) (mU h) (1 : F) (mEU i₀ p₀ h₀) T)) = 0 := by
    apply Finset.sum_eq_zero; intro h _
    have hU : mU h ≠ mEU i₀ p₀ h₀ := card_ne_one_of_two (card_mU h) (card_mEU i₀ p₀ h₀)
    have hV : mV h ≠ mEU i₀ p₀ h₀ := card_ne_one_of_two (card_mV h) (card_mEU i₀ p₀ h₀)
    simp [Matrix.single_apply, hU, hV]
  have h3 : (∑ i : Fin s, ∑ j : Fin s,
      (if i < j then ∑ p : Fin 2, ∑ q : Fin 2,
        Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mEE i j p q) (mEE i j p q) (omega a b i j) else (0 : Matrix (Finset (Coord s k)) (Finset (Coord s k)) F)) (mEU i₀ p₀ h₀) T) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    split_ifs with hij
    · simp only [Matrix.sum_apply, Matrix.single_apply]
      apply Finset.sum_eq_zero; intro p _
      apply Finset.sum_eq_zero; intro q _
      simp [(mEU_ne_mEE i₀ i j p₀ p q h₀).symm]
    · rfl
  have h2 : (∑ i : Fin s, ∑ p : Fin 2,
      (Matrix.single (mE i p) (mE i p) (cDiag a b d i) (mEU i₀ p₀ h₀) T +
       ∑ h : Fin k,
         (Matrix.single (mEU i p h) (mE i p) (b i h) (mEU i₀ p₀ h₀) T +
          Matrix.single (mEV i p h) (mE i p) (a i h) (mEU i₀ p₀ h₀) T +
          Matrix.single (mE i p) (mEU i p h) (b i h) (mEU i₀ p₀ h₀) T +
          Matrix.single (mE i p) (mEV i p h) (a i h) (mEU i₀ p₀ h₀) T))) =
      b i₀ h₀ * (if T = mE i₀ p₀ then 1 else 0) := by
    rw [Finset.sum_eq_single i₀]
    · rw [Finset.sum_eq_single p₀]
      · have hE : mE i₀ p₀ ≠ mEU i₀ p₀ h₀ := card_ne_one_of_two (card_mE i₀ p₀) (card_mEU i₀ p₀ h₀)
        rw [show Matrix.single (mE i₀ p₀) (mE i₀ p₀) (cDiag a b d i₀) (mEU i₀ p₀ h₀) T = 0 by
              simp [Matrix.single_apply, hE], zero_add]
        rw [Finset.sum_eq_single h₀]
        · simp [Matrix.single_apply, hE, (mEU_ne_mEV i₀ i₀ p₀ p₀ h₀ h₀).symm, eq_comm]
        · intro h _ hh
          have hEU : mEU i₀ p₀ h ≠ mEU i₀ p₀ h₀ := fun heq => hh (mEU_inj heq).2.2
          simp [Matrix.single_apply, hE, hEU, (mEU_ne_mEV i₀ i₀ p₀ p₀ h₀ h).symm]
        · intro h; exact absurd (Finset.mem_univ h₀) h
      · intro p _ hp
        have hE : mE i₀ p ≠ mEU i₀ p₀ h₀ := card_ne_one_of_two (card_mE i₀ p) (card_mEU i₀ p₀ h₀)
        have hEU : ∀ h, mEU i₀ p h ≠ mEU i₀ p₀ h₀ := fun h heq => hp (mEU_inj heq).2.1
        have hEV : ∀ h, mEV i₀ p h ≠ mEU i₀ p₀ h₀ := fun h => (mEU_ne_mEV i₀ i₀ p₀ p h₀ h).symm
        simp [Matrix.single_apply, hE, hEU, hEV]
      · intro h; exact absurd (Finset.mem_univ p₀) h
    · intro i _ hi
      apply Finset.sum_eq_zero; intro p _
      have hE : mE i p ≠ mEU i₀ p₀ h₀ := card_ne_one_of_two (card_mE i p) (card_mEU i₀ p₀ h₀)
      have hEU : ∀ h, mEU i p h ≠ mEU i₀ p₀ h₀ := fun h heq => hi (mEU_inj heq).1
      have hEV : ∀ h, mEV i p h ≠ mEU i₀ p₀ h₀ := fun h => (mEU_ne_mEV i₀ i p₀ p h₀ h).symm
      simp [Matrix.single_apply, hE, hEU, hEV]
    · intro h; exact absurd (Finset.mem_univ i₀) h
  rw [h1, h2, h3, zero_add, add_zero]

lemma Cmat_row_mEV {s k : ℕ} (a b : Fin s → Fin k → F) (d : Fin s → F)
    (i₀ : Fin s) (p₀ : Fin 2) (h₀ : Fin k) :
    Cmat a b d (mEV i₀ p₀ h₀) = a i₀ h₀ • Pi.single (mE i₀ p₀) (1 : F) := by
  ext T
  dsimp only [Cmat]
  simp only [Matrix.add_apply, Matrix.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  have h1 : (∑ h : Fin k, (Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mU h) (mV h) (1 : F) (mEV i₀ p₀ h₀) T +
      Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mV h) (mU h) (1 : F) (mEV i₀ p₀ h₀) T)) = 0 := by
    apply Finset.sum_eq_zero; intro h _
    have hU : mU h ≠ mEV i₀ p₀ h₀ := card_ne_one_of_two (card_mU h) (card_mEV i₀ p₀ h₀)
    have hV : mV h ≠ mEV i₀ p₀ h₀ := card_ne_one_of_two (card_mV h) (card_mEV i₀ p₀ h₀)
    simp [Matrix.single_apply, hU, hV]
  have h3 : (∑ i : Fin s, ∑ j : Fin s,
      (if i < j then ∑ p : Fin 2, ∑ q : Fin 2,
        Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mEE i j p q) (mEE i j p q) (omega a b i j) else (0 : Matrix (Finset (Coord s k)) (Finset (Coord s k)) F)) (mEV i₀ p₀ h₀) T) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    split_ifs with hij
    · simp only [Matrix.sum_apply, Matrix.single_apply]
      apply Finset.sum_eq_zero; intro p _
      apply Finset.sum_eq_zero; intro q _
      simp [(mEV_ne_mEE i₀ i j p₀ p q h₀).symm]
    · rfl
  have h2 : (∑ i : Fin s, ∑ p : Fin 2,
      (Matrix.single (mE i p) (mE i p) (cDiag a b d i) (mEV i₀ p₀ h₀) T +
       ∑ h : Fin k,
         (Matrix.single (mEU i p h) (mE i p) (b i h) (mEV i₀ p₀ h₀) T +
          Matrix.single (mEV i p h) (mE i p) (a i h) (mEV i₀ p₀ h₀) T +
          Matrix.single (mE i p) (mEU i p h) (b i h) (mEV i₀ p₀ h₀) T +
          Matrix.single (mE i p) (mEV i p h) (a i h) (mEV i₀ p₀ h₀) T))) =
      a i₀ h₀ * (if T = mE i₀ p₀ then 1 else 0) := by
    rw [Finset.sum_eq_single i₀]
    · rw [Finset.sum_eq_single p₀]
      · have hE : mE i₀ p₀ ≠ mEV i₀ p₀ h₀ := card_ne_one_of_two (card_mE i₀ p₀) (card_mEV i₀ p₀ h₀)
        rw [show Matrix.single (mE i₀ p₀) (mE i₀ p₀) (cDiag a b d i₀) (mEV i₀ p₀ h₀) T = 0 by
              simp [Matrix.single_apply, hE], zero_add]
        rw [Finset.sum_eq_single h₀]
        · simp [Matrix.single_apply, hE, mEU_ne_mEV i₀ i₀ p₀ p₀ h₀ h₀, eq_comm]
        · intro h _ hh
          have hEV : mEV i₀ p₀ h ≠ mEV i₀ p₀ h₀ := fun heq => hh (mEV_inj heq).2.2
          simp [Matrix.single_apply, hE, hEV, mEU_ne_mEV i₀ i₀ p₀ p₀ h h₀]
        · intro h; exact absurd (Finset.mem_univ h₀) h
      · intro p _ hp
        have hE : mE i₀ p ≠ mEV i₀ p₀ h₀ := card_ne_one_of_two (card_mE i₀ p) (card_mEV i₀ p₀ h₀)
        have hEU : ∀ h, mEU i₀ p h ≠ mEV i₀ p₀ h₀ := fun h => mEU_ne_mEV i₀ i₀ p p₀ h h₀
        have hEV : ∀ h, mEV i₀ p h ≠ mEV i₀ p₀ h₀ := fun h heq => hp (mEV_inj heq).2.1
        simp [Matrix.single_apply, hE, hEU, hEV]
      · intro h; exact absurd (Finset.mem_univ p₀) h
    · intro i _ hi
      apply Finset.sum_eq_zero; intro p _
      have hE : mE i p ≠ mEV i₀ p₀ h₀ := card_ne_one_of_two (card_mE i p) (card_mEV i₀ p₀ h₀)
      have hEU : ∀ h, mEU i p h ≠ mEV i₀ p₀ h₀ := fun h => mEU_ne_mEV i i₀ p p₀ h h₀
      have hEV : ∀ h, mEV i p h ≠ mEV i₀ p₀ h₀ := fun h heq => hi (mEV_inj heq).1
      simp [Matrix.single_apply, hE, hEU, hEV]
    · intro h; exact absurd (Finset.mem_univ i₀) h
  rw [h1, h2, h3, zero_add, add_zero]

lemma Cmat_row_mEE {s k : ℕ} (a b : Fin s → Fin k → F) (d : Fin s → F)
    {i₀ j₀ : Fin s} (hij₀ : i₀ < j₀) (p₀ q₀ : Fin 2) :
    Cmat a b d (mEE i₀ j₀ p₀ q₀) = omega a b i₀ j₀ • Pi.single (mEE i₀ j₀ p₀ q₀) (1 : F) := by
  ext T
  dsimp only [Cmat]
  simp only [Matrix.add_apply, Matrix.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  have h1 : (∑ h : Fin k, (Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mU h) (mV h) (1 : F) (mEE i₀ j₀ p₀ q₀) T +
      Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mV h) (mU h) (1 : F) (mEE i₀ j₀ p₀ q₀) T)) = 0 := by
    apply Finset.sum_eq_zero; intro h _
    have hU : mU h ≠ mEE i₀ j₀ p₀ q₀ := card_ne_one_of_two (card_mU h) (card_mEE hij₀ p₀ q₀)
    have hV : mV h ≠ mEE i₀ j₀ p₀ q₀ := card_ne_one_of_two (card_mV h) (card_mEE hij₀ p₀ q₀)
    simp [Matrix.single_apply, hU, hV]
  have h2 : (∑ i : Fin s, ∑ p : Fin 2,
      (Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mE i p) (mE i p) (cDiag a b d i) (mEE i₀ j₀ p₀ q₀) T +
       ∑ h : Fin k,
         (Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mEU i p h) (mE i p) (b i h) (mEE i₀ j₀ p₀ q₀) T +
          Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mEV i p h) (mE i p) (a i h) (mEE i₀ j₀ p₀ q₀) T +
          Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mE i p) (mEU i p h) (b i h) (mEE i₀ j₀ p₀ q₀) T +
          Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mE i p) (mEV i p h) (a i h) (mEE i₀ j₀ p₀ q₀) T))) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro p _
    have hE : (mE i p : Finset (Coord s k)) ≠ mEE i₀ j₀ p₀ q₀ := card_ne_one_of_two (card_mE (k := k) i p) (card_mEE (k := k) hij₀ p₀ q₀)
    have hEU : ∀ h : Fin k, mEU i p h ≠ mEE i₀ j₀ p₀ q₀ := fun h => mEU_ne_mEE i i₀ j₀ p p₀ q₀ h
    have hEV : ∀ h : Fin k, mEV i p h ≠ mEE i₀ j₀ p₀ q₀ := fun h => mEV_ne_mEE i i₀ j₀ p p₀ q₀ h
    simp [Matrix.single_apply, hE, hEU, hEV]
  have h3 : (∑ i : Fin s, ∑ j : Fin s,
      (if i < j then ∑ p : Fin 2, ∑ q : Fin 2,
        Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mEE i j p q) (mEE i j p q) (omega a b i j) else (0 : Matrix (Finset (Coord s k)) (Finset (Coord s k)) F)) (mEE i₀ j₀ p₀ q₀) T) =
      omega a b i₀ j₀ * (if T = mEE i₀ j₀ p₀ q₀ then 1 else 0) := by
    rw [Finset.sum_eq_single i₀]
    · rw [Finset.sum_eq_single j₀]
      · simp only [hij₀, ↓reduceIte, Matrix.sum_apply, Matrix.single_apply]
        rw [Finset.sum_eq_single p₀]
        · rw [Finset.sum_eq_single q₀]
          · simp [eq_comm]
          · intro q _ hq
            have hne : (mEE i₀ j₀ p₀ q : Finset (Coord s k)) ≠ mEE i₀ j₀ p₀ q₀ :=
              fun heq => hq (mEE_inj hij₀ hij₀ heq).2.2.2
            simp [hne]
          · intro h; exact absurd (Finset.mem_univ q₀) h
        · intro p _ hp
          apply Finset.sum_eq_zero; intro q _
          have hne : (mEE i₀ j₀ p q : Finset (Coord s k)) ≠ mEE i₀ j₀ p₀ q₀ :=
            fun heq => hp (mEE_inj hij₀ hij₀ heq).2.2.1
          simp [hne]
        · intro h; exact absurd (Finset.mem_univ p₀) h
      · intro j _ hj
        split_ifs with hij
        · simp only [Matrix.sum_apply, Matrix.single_apply]
          apply Finset.sum_eq_zero; intro p _
          apply Finset.sum_eq_zero; intro q _
          have hne : (mEE i₀ j p q : Finset (Coord s k)) ≠ mEE i₀ j₀ p₀ q₀ :=
            fun heq => hj (mEE_inj hij hij₀ heq).2.1
          simp [hne]
        · rfl
      · intro h; exact absurd (Finset.mem_univ j₀) h
    · intro i _ hi
      apply Finset.sum_eq_zero; intro j _
      split_ifs with hij
      · simp only [Matrix.sum_apply, Matrix.single_apply]
        apply Finset.sum_eq_zero; intro p _
        apply Finset.sum_eq_zero; intro q _
        have hne : (mEE i j p q : Finset (Coord s k)) ≠ mEE i₀ j₀ p₀ q₀ :=
          fun heq => hi (mEE_inj hij hij₀ heq).1
        simp [hne]
      · rfl
    · intro h; exact absurd (Finset.mem_univ i₀) h
  rw [h1, h2, h3, zero_add, zero_add]

lemma Cmat_row_other {s k : ℕ} (a b : Fin s → Fin k → F) (d : Fin s → F)
    (S : Finset (Coord s k))
    (hU : ∀ h, S ≠ mU h) (hV : ∀ h, S ≠ mV h) (hE : ∀ i p, S ≠ mE i p)
    (hEU : ∀ i p h, S ≠ mEU i p h) (hEV : ∀ i p h, S ≠ mEV i p h)
    (hEE : ∀ i j, i < j → ∀ p q, S ≠ mEE i j p q) :
    Cmat a b d S = 0 := by
  ext T
  dsimp only [Cmat]
  simp only [Matrix.add_apply, Matrix.sum_apply, Pi.zero_apply]
  have h1 : (∑ h : Fin k, (Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mU h) (mV h) (1 : F) S T +
      Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mV h) (mU h) (1 : F) S T)) = 0 := by
    apply Finset.sum_eq_zero; intro h _
    simp [Matrix.single_apply, (hU h).symm, (hV h).symm]
  have h2 : (∑ i : Fin s, ∑ p : Fin 2,
      (Matrix.single (mE i p) (mE i p) (cDiag a b d i) S T +
       ∑ h : Fin k,
         (Matrix.single (mEU i p h) (mE i p) (b i h) S T +
          Matrix.single (mEV i p h) (mE i p) (a i h) S T +
          Matrix.single (mE i p) (mEU i p h) (b i h) S T +
          Matrix.single (mE i p) (mEV i p h) (a i h) S T))) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro p _
    simp [Matrix.single_apply, (hE i p).symm, fun h => (hEU i p h).symm, fun h => (hEV i p h).symm]
  have h3 : (∑ i : Fin s, ∑ j : Fin s,
      (if i < j then ∑ p : Fin 2, ∑ q : Fin 2,
        Matrix.single (m := Finset (Coord s k)) (n := Finset (Coord s k)) (mEE i j p q) (mEE i j p q) (omega a b i j) else (0 : Matrix (Finset (Coord s k)) (Finset (Coord s k)) F)) S T) = 0 := by
    apply Finset.sum_eq_zero; intro i _
    apply Finset.sum_eq_zero; intro j _
    split_ifs with hij
    · simp only [Matrix.sum_apply, Matrix.single_apply]
      apply Finset.sum_eq_zero; intro p _
      apply Finset.sum_eq_zero; intro q _
      simp [(hEE i j hij p q).symm]
    · rfl
  rw [h1, h2, h3, add_zero, add_zero]

lemma wVec_apply_mEU {s k : ℕ} (a b : Fin s → Fin k → F) (i : Fin s) (p : Fin 2)
    (i' : Fin s) (p' : Fin 2) (h' : Fin k) :
    wVec a b i p (mEU i' p' h') = if i = i' ∧ p = p' then b i h' else 0 := by
  dsimp only [wVec]
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hip : i = i' ∧ p = p'
  · rcases hip with ⟨rfl, rfl⟩
    rw [if_pos ⟨rfl, rfl⟩, Finset.sum_eq_single h']
    · simp [mEU_ne_mEV]
    · intro h _ hne
      have h1 : mEU i p h' ≠ mEU i p h := fun heq => hne (mEU_inj heq).2.2.symm
      simp [h1, mEU_ne_mEV]
    · intro h; exact absurd (Finset.mem_univ h') h
  · rw [if_neg hip]
    apply Finset.sum_eq_zero; intro h _
    have h1 : mEU i' p' h' ≠ mEU i p h := fun heq => by
      have hi := mEU_inj heq
      exact hip ⟨hi.1.symm, hi.2.1.symm⟩
    simp [h1, mEU_ne_mEV]

lemma wVec_apply_mEV {s k : ℕ} (a b : Fin s → Fin k → F) (i : Fin s) (p : Fin 2)
    (i' : Fin s) (p' : Fin 2) (h' : Fin k) :
    wVec a b i p (mEV i' p' h') = if i = i' ∧ p = p' then a i h' else 0 := by
  dsimp only [wVec]
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hip : i = i' ∧ p = p'
  · rcases hip with ⟨rfl, rfl⟩
    rw [if_pos ⟨rfl, rfl⟩, Finset.sum_eq_single h']
    · simp [(mEU_ne_mEV i i p p h' h').symm]
    · intro h _ hne
      have h1 : mEV i p h' ≠ mEV i p h := fun heq => hne (mEV_inj heq).2.2.symm
      simp [h1, (mEU_ne_mEV i i p p h h').symm]
    · intro h; exact absurd (Finset.mem_univ h') h
  · rw [if_neg hip]
    apply Finset.sum_eq_zero; intro h _
    have h1 : mEV i' p' h' ≠ mEV i p h := fun heq => by
      have hi := mEV_inj heq
      exact hip ⟨hi.1.symm, hi.2.1.symm⟩
    simp [h1, (mEU_ne_mEV i i' p p' h h').symm]

lemma wVec_apply_other {s k : ℕ} (a b : Fin s → Fin k → F) (i : Fin s) (p : Fin 2)
    (T : Finset (Coord s k))
    (hEU : ∀ h, T ≠ mEU i p h) (hEV : ∀ h, T ≠ mEV i p h) :
    wVec a b i p T = 0 := by
  dsimp only [wVec]
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  apply Finset.sum_eq_zero; intro h _
  simp [hEU h, hEV h]

lemma linearIndependent_of_disjoint_witness {ι α : Type*} [Fintype ι]
    (v : ι → α → F)
    (hwit : ∀ idx : ι, ∃ x : α, v idx x ≠ 0 ∧ ∀ idx' : ι, idx' ≠ idx → v idx' x = 0) :
    LinearIndependent F v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc idx
  rcases hwit idx with ⟨x, hne, hzero⟩
  have hx := congrFun hc x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hx
  rw [Finset.sum_eq_single idx] at hx
  · exact (mul_eq_zero.mp hx).resolve_right hne
  · intro idx' _ hne'
    rw [hzero idx' hne', mul_zero]
  · intro h; exact absurd (Finset.mem_univ idx) h

lemma rank_Cmat {s k : ℕ} (a b : Fin s → Fin k → F) (d : Fin s → F) :
    let active := fun i : Fin s => a i ≠ 0 ∨ b i ≠ 0
    let edges := (Finset.univ : Finset (Fin s × Fin s)).filter (fun h =>
      h.1 < h.2 ∧ (∑ j, (a h.1 j * b h.2 j + b h.1 j * a h.2 j)) ≠ 0)
    (Cmat a b d).rank = 2 * k + 4 * (Finset.univ.filter active).card +
      2 * (Finset.univ.filter (fun i => ¬ active i ∧ d i ≠ 0)).card + 4 * edges.card := by
  classical
  intro active edges
  let Act := {i : Fin s // i ∈ Finset.univ.filter active}
  let Inact := {i : Fin s // i ∈ Finset.univ.filter (fun i => ¬ active i ∧ d i ≠ 0)}
  let Edg := {e : Fin s × Fin s // e ∈ edges}
  let Idx :=
    (Fin k ⊕ Fin k) ⊕
    ((Act × Fin 2 × Fin 2) ⊕ (Inact × Fin 2)) ⊕
    (Edg × Fin 2 × Fin 2)
  let B : Idx → (Finset (Coord s k) → F)
    | Sum.inl (Sum.inl h) => Pi.single (mV h) 1
    | Sum.inl (Sum.inr h) => Pi.single (mU h) 1
    | Sum.inr (Sum.inl (Sum.inl (i, p, r))) =>
        if r.val = 0 then Pi.single (mE i.val p) 1 else wVec a b i.val p
    | Sum.inr (Sum.inl (Sum.inr (i, p))) => Pi.single (mE i.val p) 1
    | Sum.inr (Sum.inr (e, p, q)) => Pi.single (mEE e.val.1 e.val.2 p q) 1
  have hB_li : LinearIndependent F B := by
    apply linearIndependent_of_disjoint_witness B
    intro idx
    rcases idx with (h | h) | ((⟨⟨i, hi⟩, p, r⟩ | ⟨⟨i, hi⟩, p⟩) | ⟨⟨⟨i, j⟩, he⟩, p, q⟩)
    · refine ⟨mV h, by simp [B], ?_⟩
      intro idx' hne
      rcases idx' with (h' | h') | ((⟨⟨i', hi'⟩, p', r'⟩ | ⟨⟨i', hi'⟩, p'⟩) | ⟨⟨⟨i', j'⟩, he'⟩, p', q'⟩)
      · have hhh : h' ≠ h := fun e => hne (by subst e; rfl)
        have hne' : (mV h : Finset (Coord s k)) ≠ mV h' := fun e => hhh (mV_inj e).symm
        simp [B, hne']
      · simp [B, Pi.single_apply, (mU_ne_mV h' h).symm]
      · dsimp only [B]
        split_ifs
        · simp [Pi.single_apply, mV_ne_mE h i' p']
        · exact wVec_apply_other a b i' p' (mV h)
            (fun h1 => card_ne_one_of_two (card_mV h) (card_mEU i' p' h1))
            (fun h1 => card_ne_one_of_two (card_mV h) (card_mEV i' p' h1))
      · simp [B, Pi.single_apply, mV_ne_mE h i' p']
      · have hij' : i' < j' := (Finset.mem_filter.mp he').2.1
        simp [B, Pi.single_apply, card_ne_one_of_two (card_mV h) (card_mEE hij' p' q')]
    · refine ⟨mU h, by simp [B], ?_⟩
      intro idx' hne
      rcases idx' with (h' | h') | ((⟨⟨i', hi'⟩, p', r'⟩ | ⟨⟨i', hi'⟩, p'⟩) | ⟨⟨⟨i', j'⟩, he'⟩, p', q'⟩)
      · simp [B, Pi.single_apply, mU_ne_mV h h']
      · have hhh : h' ≠ h := fun e => hne (by subst e; rfl)
        have hne' : (mU h : Finset (Coord s k)) ≠ mU h' := fun e => hhh (mU_inj e).symm
        simp [B, hne']
      · dsimp only [B]
        split_ifs
        · simp [Pi.single_apply, mU_ne_mE h i' p']
        · exact wVec_apply_other a b i' p' (mU h)
            (fun h1 => card_ne_one_of_two (card_mU h) (card_mEU i' p' h1))
            (fun h1 => card_ne_one_of_two (card_mU h) (card_mEV i' p' h1))
      · simp [B, Pi.single_apply, mU_ne_mE h i' p']
      · have hij' : i' < j' := (Finset.mem_filter.mp he').2.1
        simp [B, Pi.single_apply, card_ne_one_of_two (card_mU h) (card_mEE hij' p' q')]
    · fin_cases r
      · refine ⟨mE i p, by simp [B], ?_⟩
        intro idx' hne
        rcases idx' with (h' | h') | ((⟨⟨i', hi'⟩, p', r'⟩ | ⟨⟨i', hi'⟩, p'⟩) | ⟨⟨⟨i', j'⟩, he'⟩, p', q'⟩)
        · simp [B, Pi.single_apply, (mV_ne_mE h' i p).symm]
        · simp [B, Pi.single_apply, (mU_ne_mE h' i p).symm]
        · fin_cases r'
          · have hne_ip : i' ≠ i ∨ p' ≠ p := by
              by_contra h
              push_neg at h
              rcases h with ⟨rfl, rfl⟩
              exact hne rfl
            dsimp only [B]
            simp only [↓reduceIte, Pi.single_apply]
            rw [if_neg]
            intro heq
            rcases mE_inj heq with ⟨hi_eq, hp_eq⟩
            rcases hne_ip with h1 | h2
            · exact h1 hi_eq.symm
            · exact h2 hp_eq.symm
          · dsimp only [B]
            simp only [Nat.one_ne_zero, ↓reduceIte]
            exact wVec_apply_other a b i' p' (mE i p)
              (fun h1 => card_ne_one_of_two (card_mE i p) (card_mEU i' p' h1))
              (fun h1 => card_ne_one_of_two (card_mE i p) (card_mEV i' p' h1))
        · have hi_act : active i := (Finset.mem_filter.mp hi).2
          have hi'_inact : ¬ active i' := (Finset.mem_filter.mp hi').2.1
          have hne_i : i ≠ i' := fun e => hi'_inact (e ▸ hi_act)
          simp only [B, Pi.single_apply]
          rw [if_neg (fun heq => hne_i (mE_inj heq).1)]
        · have hij' : i' < j' := (Finset.mem_filter.mp he').2.1
          simp [B, Pi.single_apply, card_ne_one_of_two (card_mE i p) (card_mEE hij' p' q')]
      · have hi_act : active i := (Finset.mem_filter.mp hi).2
        have hnz : (∃ h : Fin k, a i h ≠ 0) ∨ (∃ h : Fin k, b i h ≠ 0) := by
          rcases hi_act with ha | hb
          · left
            by_contra h; push_neg at h
            exact ha (funext h)
          · right
            by_contra h; push_neg at h
            exact hb (funext h)
        rcases hnz with ⟨h0, ha0⟩ | ⟨h0, hb0⟩
        · refine ⟨mEV i p h0, ?_, ?_⟩
          · dsimp only [B]
            simp only [Nat.one_ne_zero, ↓reduceIte]; rw [wVec_apply_mEV]
            simp [ha0]
          · intro idx' hne
            rcases idx' with (h' | h') | ((⟨⟨i', hi'⟩, p', r'⟩ | ⟨⟨i', hi'⟩, p'⟩) | ⟨⟨⟨i', j'⟩, he'⟩, p', q'⟩)
            · simp [B, Pi.single_apply, (card_ne_one_of_two (card_mV h') (card_mEV i p h0)).symm]
            · simp [B, Pi.single_apply, (card_ne_one_of_two (card_mU h') (card_mEV i p h0)).symm]
            · fin_cases r'
              · simp [B, Pi.single_apply, (card_ne_one_of_two (card_mE i' p') (card_mEV i p h0)).symm]
              · dsimp only [B]
                simp only [Nat.one_ne_zero, ↓reduceIte]; rw [wVec_apply_mEV]
                rw [if_neg]
                rintro ⟨rfl, rfl⟩
                exact hne rfl
            · simp [B, Pi.single_apply, (card_ne_one_of_two (card_mE i' p') (card_mEV i p h0)).symm]
            · simp [B, Pi.single_apply, mEV_ne_mEE i i' j' p p' q' h0]
        · refine ⟨mEU i p h0, ?_, ?_⟩
          · dsimp only [B]
            simp only [Nat.one_ne_zero, ↓reduceIte]; rw [wVec_apply_mEU]
            simp [hb0]
          · intro idx' hne
            rcases idx' with (h' | h') | ((⟨⟨i', hi'⟩, p', r'⟩ | ⟨⟨i', hi'⟩, p'⟩) | ⟨⟨⟨i', j'⟩, he'⟩, p', q'⟩)
            · simp [B, Pi.single_apply, (card_ne_one_of_two (card_mV h') (card_mEU i p h0)).symm]
            · simp [B, Pi.single_apply, (card_ne_one_of_two (card_mU h') (card_mEU i p h0)).symm]
            · fin_cases r'
              · simp [B, Pi.single_apply, (card_ne_one_of_two (card_mE i' p') (card_mEU i p h0)).symm]
              · dsimp only [B]
                simp only [Nat.one_ne_zero, ↓reduceIte]; rw [wVec_apply_mEU]
                rw [if_neg]
                rintro ⟨rfl, rfl⟩
                exact hne rfl
            · simp [B, Pi.single_apply, (card_ne_one_of_two (card_mE i' p') (card_mEU i p h0)).symm]
            · simp [B, Pi.single_apply, mEU_ne_mEE i i' j' p p' q' h0]
    · refine ⟨mE i p, by simp [B], ?_⟩
      intro idx' hne
      rcases idx' with (h' | h') | ((⟨⟨i', hi'⟩, p', r'⟩ | ⟨⟨i', hi'⟩, p'⟩) | ⟨⟨⟨i', j'⟩, he'⟩, p', q'⟩)
      · simp [B, Pi.single_apply, (mV_ne_mE h' i p).symm]
      · simp [B, Pi.single_apply, (mU_ne_mE h' i p).symm]
      · fin_cases r'
        · have hi_inact : ¬ active i := (Finset.mem_filter.mp hi).2.1
          have hi'_act : active i' := (Finset.mem_filter.mp hi').2
          have hne_i : i ≠ i' := fun e => hi_inact (e ▸ hi'_act)
          dsimp only [B]
          simp only [↓reduceIte, Pi.single_apply]
          rw [if_neg (fun heq => hne_i (mE_inj heq).1)]
        · dsimp only [B]
          simp only [Nat.one_ne_zero, ↓reduceIte]
          exact wVec_apply_other a b i' p' (mE i p)
            (fun h1 => card_ne_one_of_two (card_mE i p) (card_mEU i' p' h1))
            (fun h1 => card_ne_one_of_two (card_mE i p) (card_mEV i' p' h1))
      · have hne_ip : i' ≠ i ∨ p' ≠ p := by
          by_contra h; push_neg at h
          rcases h with ⟨rfl, rfl⟩
          exact hne rfl
        simp only [B, Pi.single_apply]
        rw [if_neg]
        intro heq
        rcases mE_inj heq with ⟨hi_eq, hp_eq⟩
        rcases hne_ip with h1 | h2
        · exact h1 hi_eq.symm
        · exact h2 hp_eq.symm
      · have hij' : i' < j' := (Finset.mem_filter.mp he').2.1
        simp [B, Pi.single_apply, card_ne_one_of_two (card_mE i p) (card_mEE hij' p' q')]
    · have hij : i < j := (Finset.mem_filter.mp he).2.1
      refine ⟨mEE i j p q, by simp [B], ?_⟩
      intro idx' hne
      rcases idx' with (h' | h') | ((⟨⟨i', hi'⟩, p', r'⟩ | ⟨⟨i', hi'⟩, p'⟩) | ⟨⟨⟨i', j'⟩, he'⟩, p', q'⟩)
      · simp [B, Pi.single_apply, (card_ne_one_of_two (card_mV h') (card_mEE hij p q)).symm]
      · simp [B, Pi.single_apply, (card_ne_one_of_two (card_mU h') (card_mEE hij p q)).symm]
      · fin_cases r'
        · simp [B, Pi.single_apply, (card_ne_one_of_two (card_mE i' p') (card_mEE hij p q)).symm]
        · dsimp only [B]
          simp only [Nat.one_ne_zero, ↓reduceIte]
          exact wVec_apply_other a b i' p' (mEE i j p q)
            (fun h1 => (mEU_ne_mEE i' i j p' p q h1).symm)
            (fun h1 => (mEV_ne_mEE i' i j p' p q h1).symm)
      · simp [B, Pi.single_apply, (card_ne_one_of_two (card_mE i' p') (card_mEE hij p q)).symm]
      · have hij' : i' < j' := (Finset.mem_filter.mp he').2.1
        simp only [B, Pi.single_apply]
        rw [if_neg]
        intro heq
        rcases mEE_inj hij hij' heq with ⟨rfl, rfl, rfl, rfl⟩
        exact hne rfl
  -- Show span(range B) = span(range (Cmat a b d))
  have hspan_eq : Submodule.span F (Set.range (Cmat a b d)) = Submodule.span F (Set.range B) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨S, rfl⟩
      by_cases hU : ∃ h, S = mU h
      · rcases hU with ⟨h, rfl⟩
        rw [Cmat_row_mU]
        exact Submodule.subset_span ⟨Sum.inl (Sum.inl h), rfl⟩
      by_cases hV : ∃ h, S = mV h
      · rcases hV with ⟨h, rfl⟩
        rw [Cmat_row_mV]
        exact Submodule.subset_span ⟨Sum.inl (Sum.inr h), rfl⟩
      by_cases hE : ∃ i p, S = mE i p
      · rcases hE with ⟨i, p, rfl⟩
        rw [Cmat_row_mE]
        by_cases hact : active i
        · have hi : i ∈ Finset.univ.filter active := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hact⟩
          refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) ?_
          · exact Submodule.subset_span ⟨Sum.inr (Sum.inl (Sum.inl (⟨i, hi⟩, p, 0))), rfl⟩
          · exact Submodule.subset_span ⟨Sum.inr (Sum.inl (Sum.inl (⟨i, hi⟩, p, 1))), by
              dsimp only [B]; simp⟩
        · have ha0 : a i = 0 := by
            by_contra h; exact hact (Or.inl h)
          have hb0 : b i = 0 := by
            by_contra h; exact hact (Or.inr h)
          have hw0 : wVec a b i p = 0 := by
            dsimp only [wVec]
            have ha0' : ∀ h, a i h = 0 := fun h => congrFun ha0 h
            have hb0' : ∀ h, b i h = 0 := fun h => congrFun hb0 h
            simp [ha0', hb0']
          have hc_eq : cDiag a b d i = d i := by
            dsimp only [cDiag]
            have ha0' : ∀ h, a i h = 0 := fun h => congrFun ha0 h
            simp [ha0']
          rw [hw0, add_zero, hc_eq]
          by_cases hd0 : d i = 0
          · rw [hd0, zero_smul]; exact Submodule.zero_mem _
          · have hi : i ∈ Finset.univ.filter (fun i => ¬ active i ∧ d i ≠ 0) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hact, hd0⟩
            exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr (Sum.inl (Sum.inr (⟨i, hi⟩, p))), rfl⟩)
      by_cases hEU : ∃ i p h, S = mEU i p h
      · rcases hEU with ⟨i, p, h, rfl⟩
        rw [Cmat_row_mEU]
        by_cases hb0 : b i h = 0
        · rw [hb0, zero_smul]; exact Submodule.zero_mem _
        · have hact : active i := Or.inr (fun heq => hb0 (congrFun heq h))
          have hi : i ∈ Finset.univ.filter active := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hact⟩
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr (Sum.inl (Sum.inl (⟨i, hi⟩, p, 0))), rfl⟩)
      by_cases hEV : ∃ i p h, S = mEV i p h
      · rcases hEV with ⟨i, p, h, rfl⟩
        rw [Cmat_row_mEV]
        by_cases ha0 : a i h = 0
        · rw [ha0, zero_smul]; exact Submodule.zero_mem _
        · have hact : active i := Or.inl (fun heq => ha0 (congrFun heq h))
          have hi : i ∈ Finset.univ.filter active := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hact⟩
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr (Sum.inl (Sum.inl (⟨i, hi⟩, p, 0))), rfl⟩)
      by_cases hEE : ∃ i j, i < j ∧ ∃ p q, S = mEE i j p q
      · rcases hEE with ⟨i, j, hij, p, q, rfl⟩
        rw [Cmat_row_mEE a b d hij p q]
        by_cases hom : omega a b i j = 0
        · rw [hom, zero_smul]; exact Submodule.zero_mem _
        · have he : (i, j) ∈ edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij, hom⟩
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr (Sum.inr (⟨(i, j), he⟩, p, q)), rfl⟩)
      · push_neg at hU hV hE hEU hEV hEE
        rw [Cmat_row_other a b d S hU hV hE hEU hEV hEE]
        exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      rintro _ ⟨idx, rfl⟩
      rcases idx with (h | h) | ((⟨⟨i, hi⟩, p, r⟩ | ⟨⟨i, hi⟩, p⟩) | ⟨⟨⟨i, j⟩, he⟩, p, q⟩)
      · dsimp only [B]
        rw [← Cmat_row_mU a b d h]
        exact Submodule.subset_span ⟨mU h, rfl⟩
      · dsimp only [B]
        rw [← Cmat_row_mV a b d h]
        exact Submodule.subset_span ⟨mV h, rfl⟩
      · have hi_act : active i := (Finset.mem_filter.mp hi).2
        have hE_mem : Pi.single (mE i p) (1 : F) ∈ Submodule.span F (Set.range (Cmat a b d)) := by
          rcases hi_act with ha | hb
          · have : ∃ h, a i h ≠ 0 := by by_contra h; push_neg at h; exact ha (funext h)
            rcases this with ⟨h, hh⟩
            have h1 : a i h = 1 := f2_eq_one_of_ne_zero hh
            have hrow := Cmat_row_mEV a b d i p h
            rw [h1, one_smul] at hrow
            rw [← hrow]
            exact Submodule.subset_span ⟨mEV i p h, rfl⟩
          · have : ∃ h, b i h ≠ 0 := by by_contra h; push_neg at h; exact hb (funext h)
            rcases this with ⟨h, hh⟩
            have h1 : b i h = 1 := f2_eq_one_of_ne_zero hh
            have hrow := Cmat_row_mEU a b d i p h
            rw [h1, one_smul] at hrow
            rw [← hrow]
            exact Submodule.subset_span ⟨mEU i p h, rfl⟩
        fin_cases r
        · exact hE_mem
        · dsimp only [B]
          simp only [Nat.one_ne_zero, ↓reduceIte]
          have hw_eq : wVec a b i p = Cmat a b d (mE i p) + cDiag a b d i • Pi.single (mE i p) (1 : F) := by
            rw [Cmat_row_mE]
            ext T
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            rw [add_comm (cDiag a b d i * _), add_assoc, f2_add_self, add_zero]
          rw [hw_eq]
          exact Submodule.add_mem _ (Submodule.subset_span ⟨mE i p, rfl⟩)
            (Submodule.smul_mem _ _ hE_mem)
      · have hi_inact : ¬ active i := (Finset.mem_filter.mp hi).2.1
        have hd_ne : d i ≠ 0 := (Finset.mem_filter.mp hi).2.2
        have ha0 : a i = 0 := by by_contra h; exact hi_inact (Or.inl h)
        have hb0 : b i = 0 := by by_contra h; exact hi_inact (Or.inr h)
        have hw0 : wVec a b i p = 0 := by
          dsimp only [wVec]
          have ha0' : ∀ h, a i h = 0 := fun h => congrFun ha0 h
          have hb0' : ∀ h, b i h = 0 := fun h => congrFun hb0 h
          simp [ha0', hb0']
        have hc1 : cDiag a b d i = 1 := by
          dsimp only [cDiag]
          have ha0' : ∀ h, a i h = 0 := fun h => congrFun ha0 h
          simp [ha0', f2_eq_one_of_ne_zero hd_ne]
        have hrow := Cmat_row_mE a b d i p
        rw [hc1, one_smul, hw0, add_zero] at hrow
        dsimp only [B]
        rw [← hrow]
        exact Submodule.subset_span ⟨mE i p, rfl⟩
      · have hij : i < j := (Finset.mem_filter.mp he).2.1
        have hom : omega a b i j ≠ 0 := (Finset.mem_filter.mp he).2.2
        have hrow := Cmat_row_mEE a b d hij p q
        rw [f2_eq_one_of_ne_zero hom, one_smul] at hrow
        dsimp only [B]
        rw [← hrow]
        exact Submodule.subset_span ⟨mEE i j p q, rfl⟩
  -- Relate Cmat.rank to finrank of span(range Cmat)
  have hrange_eq : LinearMap.range (Cmat a b d).mulVecLin = Submodule.span F (Set.range (Cmat a b d)) := by
    rw [Matrix.range_mulVecLin]
    have hcol : (Cmat a b d).col = Cmat a b d := by
      ext S T
      exact congrFun (congrFun (Cmat_symm a b d) S) T
    rw [hcol]
  have hrank : (Cmat a b d).rank = Fintype.card Idx := by
    dsimp only [Matrix.rank]
    rw [hrange_eq, hspan_eq, finrank_span_eq_card hB_li]
  rw [hrank]
  dsimp only [Idx, Act, Inact, Edg]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  ring

end PEqualNP.Outside.L_lib_1089

theorem PEqualNP.Outside.L_lib_1089 :
  let F := ZMod 2
  ∀ (s k : ℕ) (a b : Fin s → Fin k → F) (d : Fin s → F),
    let V := (Fin s → Fin 2 → F) × ((Fin k → F) × (Fin k → F))
    let g := fun (i : Fin s) (x y : V) => ∑ p : Fin 2, x.1 i p * y.1 i p
    let val := fun (x y : V) =>
      (∑ h : Fin k,
        (x.2.1 h + y.2.1 h + ∑ i : Fin s, a i h * g i x y) *
        (x.2.2 h + y.2.2 h + ∑ i : Fin s, b i h * g i x y)) +
        ∑ i : Fin s, d i * g i x y
    let X : Matrix V V F := fun x y => val x y + val x 0 + val 0 y + val 0 0
    let active := fun i : Fin s => a i ≠ 0 ∨ b i ≠ 0
    let edges := (Finset.univ : Finset (Fin s × Fin s)).filter (fun h =>
      h.1 < h.2 ∧ (∑ j, (a h.1 j * b h.2 j + b h.1 j * a h.2 j)) ≠ 0)
    X.rank = 2*k + 4*(Finset.univ.filter active).card +
      2*(Finset.univ.filter (fun i => ¬ active i ∧ d i ≠ 0)).card + 4*edges.card := by
  intro F s k a b d V g val X active edges
  have hX : X = PEqualNP.Outside.L_lib_1089.Emat s k *
      PEqualNP.Outside.L_lib_1089.Cmat a b d *
      (PEqualNP.Outside.L_lib_1089.Emat s k).transpose :=
    PEqualNP.Outside.L_lib_1089.X_eq_conj_Cmat a b d
  rw [hX, PEqualNP.Outside.L_lib_1089.rank_conj_Emat]
  exact PEqualNP.Outside.L_lib_1089.rank_Cmat a b d
