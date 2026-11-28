import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_456_aux

open Classical

abbrev F2 := ZMod 2

lemma z2_cases (a : F2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma z2_add_self (a : F2) : a + a = 0 := by
  fin_cases a <;> decide

lemma z2_vec_add_self {n : ℕ} (v : Fin n → F2) : v + v = 0 := by
  funext i; exact z2_add_self (v i)

lemma z2_vec_sub_eq_add {n : ℕ} (u v : Fin n → F2) : u - v = u + v := by
  funext i
  have : u i - v i = u i + v i := by
    rcases z2_cases (u i) with h1 | h1 <;> rcases z2_cases (v i) with h2 | h2 <;> rw [h1, h2] <;> decide
  exact this

def sgn (b : F2) : ℤ := if b = 0 then 1 else -1

lemma sgn_abs (b : F2) : |sgn b| = 1 := by
  rcases z2_cases b with rfl | rfl <;> decide

lemma sgn_add (a b : F2) : sgn (a + b) = sgn a * sgn b := by
  rcases z2_cases a with rfl | rfl <;> rcases z2_cases b with rfl | rfl <;> decide

lemma sgn_eq_iff (a b : F2) : (if a = b then (1 : ℤ) else -1) = sgn (a + b) := by
  rcases z2_cases a with rfl | rfl <;> rcases z2_cases b with rfl | rfl <;> decide

lemma z2_decide_eq_iff (a b c : F2) : (decide (a = c) = decide (b = c)) ↔ a = b := by
  rcases z2_cases a with rfl | rfl <;> rcases z2_cases b with rfl | rfl <;> rcases z2_cases c with rfl | rfl <;> decide

lemma sq_eq_two_pow (a d : ℕ) (h : a ^ 2 = 2 ^ d) : Even d ∧ a = 2 ^ (d / 2) := by
  induction d using Nat.strong_induction_on generalizing a with
  | ind d ih =>
    match d with
    | 0 =>
      have ha : a = 1 := by
        have h1 : a * a = 1 := by simpa [sq] using h
        nlinarith
      exact ⟨⟨0, rfl⟩, ha⟩
    | 1 =>
      exfalso
      have h1 : a * a = 2 := by simpa [sq] using h
      have hlt : a < 2 := by nlinarith
      interval_cases a <;> omega
    | d' + 2 =>
      have h2div : 2 ∣ a ^ 2 := by
        rw [h, pow_add, show (2 : ℕ) ^ 2 = 4 by norm_num]
        exact ⟨2 * 2 ^ d', by ring⟩
      have h2a : 2 ∣ a := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2div
      rcases h2a with ⟨b, rfl⟩
      have hb : b ^ 2 = 2 ^ d' := by
        have h1 : 4 * b ^ 2 = 4 * 2 ^ d' := by
          calc 4 * b ^ 2 = (2 * b) ^ 2 := by ring
            _ = 2 ^ (d' + 2) := h
            _ = 4 * 2 ^ d' := by rw [pow_add]; ring
        omega
      rcases ih d' (by omega) b hb with ⟨⟨k, hk⟩, hbeq⟩
      refine ⟨⟨k + 1, by omega⟩, ?_⟩
      rw [hbeq, show (d' + 2) / 2 = d' / 2 + 1 by omega, pow_succ, mul_comm]

lemma card_submodule_z2 {n : ℕ} (U : Submodule F2 (Fin n → F2)) :
    Fintype.card U = 2 ^ Module.finrank F2 U := by
  have h := Module.card_eq_pow_finrank (K := F2) (V := U)
  simp only [Nat.card_eq_fintype_card, ZMod.card] at h
  exact h

def dotLin {n : ℕ} (a : Fin n → F2) : (Fin n → F2) →ₗ[F2] F2 where
  toFun := fun x => dotProduct a x
  map_add' := fun x y => dotProduct_add a x y
  map_smul' := fun c x => by simp [dotProduct_smul]

def orthoComp {n : ℕ} (U : Submodule F2 (Fin n → F2)) : Submodule F2 (Fin n → F2) :=
  { carrier := {v | ∀ u ∈ U, dotProduct v u = 0}
    zero_mem' := fun u _ => by simp
    smul_mem' := fun a {v} hv u hu => (by rw [smul_dotProduct, hv u hu, smul_zero]), add_mem' := fun {v1 v2} h1 h2 u hu => (by rw [add_dotProduct, h1 u hu, h2 u hu, add_zero]) }

lemma vec_eq_sum_single {n : ℕ} (x : Fin n → F2) :
    x = ∑ i : Fin n, x i • Pi.single i (1 : F2) := by
  funext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

lemma linear_coord_dot {n : ℕ} (f : (Fin n → F2) →ₗ[F2] F2) :
    ∃ a : Fin n → F2, ∀ x, f x = dotProduct a x := by
  refine ⟨fun i => f (Pi.single i 1), fun x => ?_⟩
  conv_lhs => rw [vec_eq_sum_single x]
  rw [map_sum]
  unfold dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

lemma finrank_orthoComp {n : ℕ} (U : Submodule F2 (Fin n → F2)) :
    Module.finrank F2 (orthoComp U) + Module.finrank F2 U = n := by
  let e : (Fin n → F2) →ₗ[F2] Module.Dual F2 U :=
    { toFun := fun v =>
        { toFun := fun u => dotProduct v u.val
          map_add' := fun x y => dotProduct_add v x.val y.val
          map_smul' := fun c x => by simp [dotProduct_smul] }
      map_add' := fun v1 v2 => by ext u; exact add_dotProduct v1 v2 u.val
      map_smul' := fun c v => by ext u; simp [smul_dotProduct] }
  have hker : LinearMap.ker e = orthoComp U := by
    ext v; constructor
    · intro hv u hu
      have h0 := LinearMap.congr_fun hv ⟨u, hu⟩
      exact h0
    · intro hv; ext u; exact hv u.val u.property
  have hsurj : Function.Surjective e := by
    intro φ
    obtain ⟨W, hW⟩ := Submodule.exists_isCompl U
    let proj : (Fin n → F2) →ₗ[F2] U := Submodule.projectionOnto U W hW
    let g : (Fin n → F2) →ₗ[F2] F2 := φ.comp proj
    obtain ⟨v, hv⟩ := linear_coord_dot g
    refine ⟨v, ?_⟩
    ext u
    show dotProduct v u.val = φ u
    rw [← hv u.val]
    change φ (proj u.val) = φ u
    have hp : proj u.val = u := Submodule.projectionOnto_apply_left hW u
    rw [hp]
  have hrk := LinearMap.finrank_range_add_finrank_ker e
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker, Subspace.dual_finrank_eq,
      Module.finrank_fin_fun] at hrk
  omega

lemma sum_sgn_linear_submodule {n : ℕ} (U : Submodule F2 (Fin n → F2))
    (L : U →ₗ[F2] F2) :
    (∑ u : U, sgn (L u)) = if L = 0 then (2 : ℤ) ^ Module.finrank F2 U else 0 := by
  by_cases hL : L = 0
  · rw [if_pos hL]
    have h1 : ∀ u : U, sgn (L u) = 1 := fun u => by rw [hL]; rfl
    simp_rw [h1]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, card_submodule_z2]
    push_cast; rfl
  · rw [if_neg hL]
    have hex : ∃ u0 : U, L u0 = 1 := by
      by_contra hno; push Not at hno; apply hL; ext u
      rcases z2_cases (L u) with h | h
      · exact h
      · exact absurd h (hno u)
    obtain ⟨u0, hu0⟩ := hex
    let e : U ≃ U :=
      { toFun := fun u => u + u0
        invFun := fun u => u + u0
        left_inv := fun u => Subtype.ext (by show u.val + u0.val + u0.val = u.val; rw [add_assoc, z2_vec_add_self, add_zero])
        right_inv := fun u => Subtype.ext (by show u.val + u0.val + u0.val = u.val; rw [add_assoc, z2_vec_add_self, add_zero]) }
    have hneg : (∑ u : U, sgn (L u)) = -(∑ u : U, sgn (L u)) := by
      calc (∑ u : U, sgn (L u))
          = ∑ u : U, sgn (L (e u)) := (Equiv.sum_comp e _).symm
        _ = ∑ u : U, -sgn (L u) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            show sgn (L (u + u0)) = -sgn (L u)
            rw [map_add, hu0, sgn_add]
            change sgn (L u) * (-1) = -sgn (L u); ring
        _ = -(∑ u : U, sgn (L u)) := by rw [Finset.sum_neg_distrib]
    omega

lemma sum_sgn_dot_submodule {n : ℕ} (U : Submodule F2 (Fin n → F2)) (a : Fin n → F2) :
    (∑ u : U, sgn (dotProduct a u.val)) =
      if a ∈ orthoComp U then (2 : ℤ) ^ Module.finrank F2 U else 0 := by
  let L : U →ₗ[F2] F2 :=
    { toFun := fun u => dotProduct a u.val
      map_add' := fun x y => dotProduct_add a x.val y.val
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have h := sum_sgn_linear_submodule U L
  have hiff : L = 0 ↔ a ∈ orthoComp U := by
    constructor
    · intro h0 u hu; exact LinearMap.congr_fun h0 ⟨u, hu⟩
    · intro ha; ext u; exact ha u.val u.property
  simpa [L, hiff] using h

lemma rank_add_ker_mat {n : ℕ} (M : Matrix (Fin n) (Fin n) F2) :
    M.rank + Module.finrank F2 (LinearMap.ker M.mulVecLin) = n := by
  have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fin_fun] at h
  exact h

lemma quad_bilin_matrix {n : ℕ} (f : (Fin n → F2) → F2)
    (hf : ∀ p u v : Fin n → F2,
      f (p + u + v) + f (p + u) + f (p + v) + f p = f (u + v) + f u + f v + f 0) :
    ∃ M : Matrix (Fin n) (Fin n) F2,
      (∀ u v, f (u + v) + f u + f v + f 0 = dotProduct u (M.mulVec v)) ∧
      (∀ u v, dotProduct u (M.mulVec v) = dotProduct v (M.mulVec u)) ∧
      (∀ u, dotProduct u (M.mulVec u) = 0) := by
  let B : (Fin n → F2) → (Fin n → F2) → F2 := fun u v => f (u + v) + f u + f v + f 0
  have hB_symm : ∀ u v, B u v = B v u := fun u v => by
    dsimp only [B]; rw [add_comm u v]; ring
  have hB_self : ∀ u, B u u = 0 := fun u => by
    dsimp only [B]; rw [z2_vec_add_self]
    have h1 := z2_add_self (f 0); have h2 := z2_add_self (f u); linear_combination h1 + h2
  have hB_add_left : ∀ u w v, B (u + w) v = B u v + B w v := fun u w v => by
    have h1 := hf u w v
    dsimp only [B] at h1 ⊢
    have h2 := z2_add_self (f (u + v))
    have h3 := z2_add_self (f u)
    linear_combination h1 - h2 - h3
  have hB_add_right : ∀ u v w, B u (v + w) = B u v + B u w := fun u v w => by
    rw [hB_symm, hB_add_left, hB_symm v u, hB_symm w u]
  have hB_smul_left : ∀ (c : F2) (u v : Fin n → F2), B (c • u) v = c * B u v := fun c u v => by
    rcases z2_cases c with rfl | rfl
    · simp only [zero_smul, zero_mul, B, zero_add]
      have h1 := z2_add_self (f v); have h2 := z2_add_self (f 0); linear_combination h1 + h2
    · simp
  have hB_smul_right : ∀ (c : F2) (u v : Fin n → F2), B u (c • v) = c * B u v := fun c u v => by
    rw [hB_symm, hB_smul_left, hB_symm]
  let M : Matrix (Fin n) (Fin n) F2 := Matrix.of fun i j => B (Pi.single i 1) (Pi.single j 1)
  have hM : ∀ u v, B u v = dotProduct u (M.mulVec v) := by
    intro u v
    have hleft : ∀ x, B x v = ∑ i : Fin n, x i * B (Pi.single i 1) v := by
      intro x
      conv_lhs => rw [vec_eq_sum_single x]
      have hsum : ∀ s : Finset (Fin n), B (∑ i ∈ s, x i • Pi.single i (1 : F2)) v =
          ∑ i ∈ s, x i * B (Pi.single i 1) v := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
          simp only [Finset.sum_empty]
          simpa using hB_smul_left 0 0 v
        | insert a s ha ih =>
          rw [Finset.sum_insert ha, hB_add_left, hB_smul_left, ih, Finset.sum_insert ha]
      exact hsum Finset.univ
    have hright : ∀ i, B (Pi.single i 1) v = ∑ j : Fin n, M i j * v j := by
      intro i
      conv_lhs => rw [vec_eq_sum_single v]
      have hsum : ∀ s : Finset (Fin n), B (Pi.single i 1) (∑ j ∈ s, v j • Pi.single j (1 : F2)) =
          ∑ j ∈ s, M i j * v j := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
          simp only [Finset.sum_empty]
          simpa using hB_smul_right 0 (Pi.single i 1) 0
        | insert a s ha ih =>
          rw [Finset.sum_insert ha, hB_add_right, hB_smul_right, ih, Finset.sum_insert ha]
          simp [M, mul_comm]
      exact hsum Finset.univ
    rw [hleft u]
    unfold dotProduct Matrix.mulVec
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hright i]; rfl
  refine ⟨M, hM, fun u v => by rw [← hM, ← hM, hB_symm], fun u => by rw [← hM, hB_self]⟩

lemma affine_of_rank_zero {n : ℕ} (f : (Fin n → F2) → F2) (M : Matrix (Fin n) (Fin n) F2)
    (hf : ∀ x y, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y)) (h0 : M.rank = 0) :
    ∃ (a : Fin n → F2) (b : F2), ∀ x, f x = dotProduct a x + b := by
  have hker : LinearMap.ker M.mulVecLin = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by have := rank_add_ker_mat M; rw [Module.finrank_fin_fun]; omega)
  have hM0 : ∀ y, M.mulVec y = 0 := fun y => by
    have hy : y ∈ LinearMap.ker M.mulVecLin := by rw [hker]; trivial
    exact hy
  let L : (Fin n → F2) →ₗ[F2] F2 :=
    { toFun := fun x => f x + f 0
      map_add' := fun x y => by
        have h := hf x y; rw [hM0 y, dotProduct_zero] at h
        have hz0 := z2_add_self (f 0); have hzx := z2_add_self (f x); have hzy := z2_add_self (f y)
        linear_combination h - hzx - hzy - hz0
      map_smul' := fun c x => by
        rcases z2_cases c with rfl | rfl
        · simp [z2_add_self]
        · simp }
  obtain ⟨a, ha⟩ := linear_coord_dot L
  refine ⟨a, f 0, fun x => ?_⟩
  have h1 := ha x
  dsimp only [L, LinearMap.coe_mk, AddHom.coe_mk] at h1
  have hz := z2_add_self (f 0)
  linear_combination h1 - hz

lemma polar_symm {n : ℕ} (f : (Fin n → F2) → F2) (M : Matrix (Fin n) (Fin n) F2)
    (hf : ∀ u v, f (u + v) + f u + f v + f 0 = dotProduct u (M.mulVec v)) (u v : Fin n → F2) :
    dotProduct u (M.mulVec v) = dotProduct v (M.mulVec u) := by
  rw [← hf u v, ← hf v u, add_comm u v]; ring

lemma polar_self {n : ℕ} (f : (Fin n → F2) → F2) (M : Matrix (Fin n) (Fin n) F2)
    (hf : ∀ u v, f (u + v) + f u + f v + f 0 = dotProduct u (M.mulVec v)) (u : Fin n → F2) :
    dotProduct u (M.mulVec u) = 0 := by
  have h := hf u u; rw [z2_vec_add_self] at h
  have h1 := z2_add_self (f 0); have h2 := z2_add_self (f u)
  linear_combination -h + h1 + h2

lemma symplectic_peel_step {n : ℕ} (f : (Fin n → F2) → F2) (M : Matrix (Fin n) (Fin n) F2)
    (hf : ∀ x y, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (hne0 : M.rank ≠ 0) :
    ∃ (u v c1 c2 : Fin n → F2) (M' : Matrix (Fin n) (Fin n) F2),
      let f' := fun x => f x + dotProduct c1 x * dotProduct c2 x
      M'.rank + 2 = M.rank ∧
      (∀ x y, f' (x + y) + f' x + f' y + f' 0 = dotProduct x (M'.mulVec y)) ∧
      (∀ w, M.mulVec w = 0 → M'.mulVec w = 0) ∧
      M'.mulVec u = 0 ∧ M'.mulVec v = 0 ∧
      dotProduct c1 u = 0 ∧ dotProduct c1 v = 1 ∧ dotProduct c2 u = 1 ∧ dotProduct c2 v = 0 ∧
      (∀ w, M.mulVec w = 0 → dotProduct c1 w = 0 ∧ dotProduct c2 w = 0) := by
  have hexv : ∃ v : Fin n → F2, M.mulVec v ≠ 0 := by
    by_contra hno; push Not at hno
    have hker : LinearMap.ker M.mulVecLin = ⊤ := eq_top_iff.mpr fun y _ => hno y
    have := rank_add_ker_mat M; rw [hker, finrank_top, Module.finrank_fin_fun] at this; omega
  obtain ⟨v, hv⟩ := hexv
  have hexi : ∃ i : Fin n, M.mulVec v i = 1 := by
    by_contra hno; push Not at hno; apply hv; funext i
    rcases z2_cases (M.mulVec v i) with h | h; exact h; exact absurd h (hno i)
  obtain ⟨i, hi⟩ := hexi
  let u : Fin n → F2 := Pi.single i 1
  have huv : dotProduct u (M.mulVec v) = 1 := by simp [u, single_dotProduct, hi]
  let c1 : Fin n → F2 := M.mulVec u
  let c2 : Fin n → F2 := M.mulVec v
  have hc1 : ∀ x, dotProduct c1 x = dotProduct u (M.mulVec x) := fun x => by rw [dotProduct_comm, polar_symm f M hf]
  have hc2 : ∀ x, dotProduct c2 x = dotProduct v (M.mulVec x) := fun x => by rw [dotProduct_comm, polar_symm f M hf]
  have hc1u : dotProduct c1 u = 0 := by rw [hc1, polar_self f M hf]
  have hc1v : dotProduct c1 v = 1 := by rw [hc1, huv]
  have hc2u : dotProduct c2 u = 1 := by rw [hc2, polar_symm f M hf, huv]
  have hc2v : dotProduct c2 v = 0 := by rw [hc2, polar_self f M hf]
  let M' : Matrix (Fin n) (Fin n) F2 := Matrix.of fun a b => M a b + c1 a * c2 b + c2 a * c1 b
  have hM'mul : ∀ y a, M'.mulVec y a = M.mulVec y a + c1 a * dotProduct c2 y + c2 a * dotProduct c1 y := by
    intro y a
    simp only [Matrix.mulVec, dotProduct, M', Matrix.of_apply, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · congr 1; refine Finset.sum_congr rfl fun b _ => by ring
    · refine Finset.sum_congr rfl fun b _ => by ring
  have hM'dot : ∀ x y, dotProduct x (M'.mulVec y) =
      dotProduct x (M.mulVec y) + dotProduct c1 x * dotProduct c2 y + dotProduct c2 x * dotProduct c1 y := by
    intro x y
    unfold dotProduct
    simp_rw [hM'mul, mul_add, Finset.sum_add_distrib]
    have h1 : (∑ a : Fin n, x a * (c1 a * dotProduct c2 y)) = (∑ a, c1 a * x a) * (∑ b, c2 b * y b) := by
      unfold dotProduct; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun a _ => by ring
    have h2 : (∑ a : Fin n, x a * (c2 a * dotProduct c1 y)) = (∑ a, c2 a * x a) * (∑ b, c1 b * y b) := by
      unfold dotProduct; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun a _ => by ring
    rw [h1, h2]
  have hu_ker : M'.mulVec u = 0 := by
    funext a; rw [hM'mul, hc2u, hc1u, mul_one, mul_zero, add_zero]; exact z2_add_self (c1 a)
  have hv_ker : M'.mulVec v = 0 := by
    funext a; rw [hM'mul, hc2v, hc1v, mul_zero, add_zero, mul_one]; exact z2_add_self (c2 a)
  have hker_eq : LinearMap.ker M'.mulVecLin =
      LinearMap.ker M.mulVecLin ⊔ (Submodule.span F2 {u} ⊔ Submodule.span F2 {v}) := by
    apply le_antisymm
    · intro w hw
      have hw0 : M'.mulVec w = 0 := hw
      let w0 := w + dotProduct c2 w • u + dotProduct c1 w • v
      have hw0_ker : w0 ∈ LinearMap.ker M.mulVecLin := by
        show M.mulVec w0 = 0
        funext a
        have hwa : M'.mulVec w a = 0 := congrFun hw0 a
        rw [hM'mul] at hwa
        simp only [w0, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        change M.mulVec w a + dotProduct c2 w * c1 a + dotProduct c1 w * c2 a = 0
        linear_combination hwa
      have hw_eq : w = w0 + (dotProduct c2 w • u + dotProduct c1 w • v) := by
        dsimp only [w0]
        calc w = w + (dotProduct c2 w • u + dotProduct c2 w • u) + (dotProduct c1 w • v + dotProduct c1 w • v) := by
                rw [z2_vec_add_self, z2_vec_add_self, add_zero, add_zero]
          _ = (w + dotProduct c2 w • u + dotProduct c1 w • v) + (dotProduct c2 w • u + dotProduct c1 w • v) := by abel
      rw [hw_eq]
      refine Submodule.add_mem_sup hw0_ker (Submodule.add_mem_sup ?_ ?_)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · refine sup_le (fun y hy => ?_) (sup_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hu_ker))
        (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv_ker)))
      show M'.mulVec y = 0
      funext a; rw [hM'mul, hc2 y, hc1 y]
      have hy0 : M.mulVec y = 0 := hy
      rw [hy0]; simp
  let S : Submodule F2 (Fin n → F2) := Submodule.span F2 {u} ⊔ Submodule.span F2 {v}
  have hune : u ≠ 0 := fun h => by rw [h, zero_dotProduct] at huv; exact one_ne_zero huv.symm
  have hvne : v ≠ 0 := fun h => by rw [h, Matrix.mulVec_zero, dotProduct_zero] at huv; exact one_ne_zero huv.symm
  have hdisj_uv : Submodule.span F2 {u} ⊓ Submodule.span F2 {v} = ⊥ := by
    rw [eq_bot_iff]; intro w hw
    rw [Submodule.mem_inf, Submodule.mem_span_singleton, Submodule.mem_span_singleton] at hw
    obtain ⟨⟨a1, rfl⟩, ⟨a2, ha2⟩⟩ := hw
    rcases z2_cases a1 with rfl | rfl
    · simp
    · rcases z2_cases a2 with rfl | rfl
      · simp at ha2; exact absurd ha2.symm hune
      · simp only [one_smul] at ha2; rw [← ha2, polar_self f M hf v] at huv; exact absurd huv (by decide)
  have hSdim : Module.finrank F2 S = 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F2 {u}) (Submodule.span F2 {v})
    rw [hdisj_uv, finrank_bot, add_zero, finrank_span_singleton hune, finrank_span_singleton hvne] at h
    exact h
  have hdisj_ker : LinearMap.ker M.mulVecLin ⊓ S = ⊥ := by
    rw [eq_bot_iff]; intro w hw
    rcases Submodule.mem_inf.mp hw with ⟨hwk, hwS⟩
    rcases Submodule.mem_sup.mp hwS with ⟨w1, hw1, w2, hw2, rfl⟩
    rcases Submodule.mem_span_singleton.mp hw1 with ⟨α, rfl⟩
    rcases Submodule.mem_span_singleton.mp hw2 with ⟨β, rfl⟩
    have h0 : M.mulVec (α • u + β • v) = 0 := hwk
    have hβ : β = 0 := by
      have h1 := congrArg (dotProduct u) h0
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, dotProduct_smul,
          polar_self f M hf u, huv, dotProduct_zero] at h1
      simpa using h1
    have hα : α = 0 := by
      have h1 := congrArg (dotProduct v) h0
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul, dotProduct_smul,
          polar_self f M hf v, polar_symm f M hf v u, huv, dotProduct_zero] at h1
      simpa using h1
    rw [hα, hβ]; simp
  have hM'rk : M'.rank + 2 = M.rank := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker M.mulVecLin) S
    rw [← hker_eq, hdisj_ker, finrank_bot, add_zero, hSdim] at hdim
    have h1 := rank_add_ker_mat M
    have h2 := rank_add_ker_mat M'
    omega
  refine ⟨u, v, c1, c2, M', hM'rk, ?_, ?_, hu_ker, hv_ker, hc1u, hc1v, hc2u, hc2v, ?_⟩
  · intro x y
    dsimp only
    rw [hM'dot, ← hf x y, dotProduct_add, dotProduct_add, dotProduct_zero, dotProduct_zero]
    have hz1 := z2_add_self (dotProduct c1 x * dotProduct c2 x)
    have hz2 := z2_add_self (dotProduct c1 y * dotProduct c2 y)
    linear_combination hz1 + hz2
  · intro w hw; funext a; rw [hM'mul, hc1 w, hc2 w, hw]; simp
  · intro w hw; exact ⟨by rw [hc1 w, hw, dotProduct_zero], by rw [hc2 w, hw, dotProduct_zero]⟩

lemma symplectic_normal_form {n : ℕ} : ∀ (rk : ℕ) (f : (Fin n → F2) → F2) (M : Matrix (Fin n) (Fin n) F2),
    M.rank = rk →
    (∀ x y, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y)) →
    ∃ (m : ℕ) (c1 c2 v : Fin m → (Fin n → F2)) (a : Fin n → F2) (b : F2),
      rk = 2 * m ∧
      (∀ x, f x = (∑ i : Fin m, dotProduct (c1 i) x * dotProduct (c2 i) x) + dotProduct a x + b) ∧
      (∀ i : Fin m, dotProduct (c1 i) (v i) = 1) ∧
      (∀ i j : Fin m, j < i → dotProduct (c1 i) (v j) = 0) := by
  intro rk
  induction rk using Nat.strong_induction_on with
  | ind rk ih =>
    intro f M hrk hf
    by_cases h0 : rk = 0
    · subst h0
      obtain ⟨a, b, hab⟩ := affine_of_rank_zero f M hf hrk
      exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, a, b, rfl, fun x => by simp [hab x],
        fun i => i.elim0, fun i => i.elim0⟩
    · have hne0 : M.rank ≠ 0 := by omega
      obtain ⟨u0, v0, c10, c20, M', hM'rk, hf', hker_pres, _, hv0ker, _, hc10v0, _, _, _⟩ :=
        symplectic_peel_step f M hf hne0
      have hlt : M'.rank < rk := by omega
      have hM'ker_c : ∀ (rk' : ℕ) (g : (Fin n → F2) → F2) (N : Matrix (Fin n) (Fin n) F2),
          N.rank = rk' →
          (∀ x y, g (x + y) + g x + g y + g 0 = dotProduct x (N.mulVec y)) →
          ∀ (S : Finset (Fin n → F2)), (∀ w ∈ S, N.mulVec w = 0) →
          ∃ (m : ℕ) (c1 c2 v : Fin m → (Fin n → F2)) (a : Fin n → F2) (b : F2),
            rk' = 2 * m ∧
            (∀ x, g x = (∑ i : Fin m, dotProduct (c1 i) x * dotProduct (c2 i) x) + dotProduct a x + b) ∧
            (∀ i : Fin m, dotProduct (c1 i) (v i) = 1) ∧
            (∀ i j : Fin m, j < i → dotProduct (c1 i) (v j) = 0) ∧
            (∀ i : Fin m, ∀ w ∈ S, dotProduct (c1 i) w = 0) := by
        intro rk'
        induction rk' using Nat.strong_induction_on with
        | ind rk' ih' =>
          intro g N hNrk hg S hS
          by_cases h0' : rk' = 0
          · subst h0'
            obtain ⟨a, b, hab⟩ := affine_of_rank_zero g N hg hNrk
            exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, a, b, rfl, fun x => by simp [hab x],
              fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
          · obtain ⟨u1, v1, c11, c21, N', hN'rk, hg', hNker, _, hv1ker, _, hc11v1, _, _, hNker_c⟩ :=
              symplectic_peel_step g N hg (by omega)
            have hS' : ∀ w ∈ insert v1 S, N'.mulVec w = 0 := by
              intro w hw
              rcases Finset.mem_insert.mp hw with rfl | hmem
              · exact hv1ker
              · exact hNker w (hS w hmem)
            obtain ⟨m1, c1', c2', v', a', b', hrk1, hform', hdiag', htri', horth'⟩ :=
              ih' N'.rank (by omega) (fun x => g x + dotProduct c11 x * dotProduct c21 x) N' rfl hg' (insert v1 S) hS'
            refine ⟨m1 + 1, Fin.cons c11 c1', Fin.cons c21 c2', Fin.cons v1 v', a', b', by omega, ?_, ?_, ?_, ?_⟩
            · intro x
              rw [Fin.sum_univ_succ]
              simp only [Fin.cons_zero, Fin.cons_succ]
              have hfx := hform' x
              have hz := z2_add_self (dotProduct c11 x * dotProduct c21 x)
              linear_combination hfx - hz
            · intro i
              refine Fin.cases ?_ (fun j => ?_) i
              · simpa using hc11v1
              · simpa using hdiag' j
            · intro i j hji
              refine Fin.cases (by intro h; exact absurd h (Fin.not_lt_zero j)) (fun i' => ?_) i hji
              refine Fin.cases (fun _ => ?_) (fun j' h => ?_) j
              · simp only [Fin.cons_succ, Fin.cons_zero]
                exact horth' i' v1 (Finset.mem_insert_self v1 S)
              · simp only [Fin.cons_succ]
                exact htri' i' j' (Fin.succ_lt_succ_iff.mp h)
            · intro i w hw
              refine Fin.cases ?_ (fun i' => ?_) i
              · exact (hNker_c w (hS w hw)).1
              · exact horth' i' w (Finset.mem_insert_of_mem hw)
      obtain ⟨m, c1, c2, v, a, b, hrk_eq, hform, hdiag, htri, _⟩ :=
        hM'ker_c M.rank f M rfl hf ∅ (by simp)
      exact ⟨m, c1, c2, v, a, b, by omega, hform, hdiag, htri⟩

lemma quad_coset_bias_structure {n m : ℕ} (f : (Fin n → F2) → F2) (M : Matrix (Fin n) (Fin n) F2)
    (hrk : M.rank = 2 * m)
    (hf : ∀ x y, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (a : Fin n → F2) (U : Submodule F2 (Fin n → F2)) :
    let K : Submodule F2 (Fin n → F2) :=
      U ⊓ ({ carrier := {w | ∀ v ∈ U, dotProduct v (M.mulVec w) = 0}
             zero_mem' := fun v _ => by simp
             smul_mem' := fun c {w} hw v hv => (by rw [Matrix.mulVec_smul, dotProduct_smul, hw v hv, smul_zero]), add_mem' := fun {w1 w2} h1 h2 v hv => (by rw [Matrix.mulVec_add, dotProduct_add, h1 v hv, h2 v hv, add_zero]) } : Submodule F2 (Fin n → F2))
    let S : ℤ := ∑ v : U, sgn (f (a + v.val))
    Module.finrank F2 U + Module.finrank F2 K ≤ 2 * (n - m) ∧
    (S = 0 ∨ (S.natAbs = 2 ^ ((Module.finrank F2 U + Module.finrank F2 K) / 2) ∧
      Even (Module.finrank F2 U + Module.finrank F2 K) ∧
      ∀ w ∈ K, f (a + w) = f a)) := by
  intro K S
  have h2m_le_n : 2 * m ≤ n := by have := rank_add_ker_mat M; omega
  have hdim_sum : Module.finrank F2 U + Module.finrank F2 K ≤ 2 * (n - m) := by
    let T : K →ₗ[F2] orthoComp U :=
      { toFun := fun w => ⟨M.mulVec w.val, fun v hv => by rw [dotProduct_comm]; exact w.property.2 v hv⟩
        map_add' := fun x y => Subtype.ext (Matrix.mulVec_add M x.val y.val)
        map_smul' := fun c x => Subtype.ext (Matrix.mulVec_smul M c x.val) }
    have hrkT := LinearMap.finrank_range_add_finrank_ker T
    have hran : Module.finrank F2 (LinearMap.range T) ≤ Module.finrank F2 (orthoComp U) := Submodule.finrank_le _
    let embKer : LinearMap.ker T →ₗ[F2] LinearMap.ker M.mulVecLin :=
      { toFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hemb_inj : Function.Injective embKer := fun x y hxy => by
      have h : (embKer x).val = (embKer y).val := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h)
    have hker_le : Module.finrank F2 (LinearMap.ker T) ≤ Module.finrank F2 (LinearMap.ker M.mulVecLin) :=
      LinearMap.finrank_le_finrank_of_injective hemb_inj
    have horth := finrank_orthoComp U
    have hMrk := rank_add_ker_mat M
    omega
  have hbil : ∀ v w : Fin n → F2, f (a + (v + w)) + f (a + v) + f (a + w) + f a = dotProduct v (M.mulVec w) := by
    intro v w
    have e1 := hf a (v + w)
    have e2 := hf a v
    have e3 := hf a w
    have e4 := hf v w
    rw [Matrix.mulVec_add, dotProduct_add] at e1
    have hz1 := z2_add_self (f a); have hz2 := z2_add_self (f (v + w))
    have hz3 := z2_add_self (f v); have hz4 := z2_add_self (f w)
    have hz5 := z2_add_self (f 0); have hz6 := z2_add_self (dotProduct a (M.mulVec v))
    have hz7 := z2_add_self (dotProduct a (M.mulVec w))
    linear_combination e1 + e2 + e3 + e4 - hz1 - hz2 - hz3 - hz4 - hz5 - hz5 + hz6 + hz7
  have hsq : S * S = (2 : ℤ) ^ Module.finrank F2 U * ∑ w : K, sgn (f (a + w.val) + f a) := by
    have h1 : S * S = ∑ w : U, sgn (f (a + w.val) + f a) * ∑ v : U, sgn (dotProduct (M.mulVec w.val) v.val) := by
      calc S * S = ∑ v : U, ∑ v' : U, sgn (f (a + v'.val)) * sgn (f (a + v.val)) := by
            simp only [S, Finset.sum_mul, Finset.mul_sum]
        _ = ∑ v : U, ∑ w : U, sgn (f (a + (v.val + w.val))) * sgn (f (a + v.val)) := by
            refine Finset.sum_congr rfl fun v _ => ?_
            let e : U ≃ U :=
              { toFun := fun w => v + w
                invFun := fun w => v + w
                left_inv := fun w => Subtype.ext (by show v.val + (v.val + w.val) = w.val; rw [← add_assoc, z2_vec_add_self, zero_add])
                right_inv := fun w => Subtype.ext (by show v.val + (v.val + w.val) = w.val; rw [← add_assoc, z2_vec_add_self, zero_add]) }
            exact (Equiv.sum_comp e (fun v' : U => sgn (f (a + v'.val)) * sgn (f (a + v.val)))).symm
        _ = ∑ w : U, ∑ v : U, sgn (f (a + (v.val + w.val)) + f (a + v.val)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v _ => ?_
            exact (sgn_add (f (a + (v.val + w.val))) (f (a + v.val))).symm
        _ = ∑ w : U, sgn (f (a + w.val) + f a) * ∑ v : U, sgn (dotProduct (M.mulVec w.val) v.val) := by
            refine Finset.sum_congr rfl fun w _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun v _ => ?_
            have heq : f (a + (v.val + w.val)) + f (a + v.val) = (f (a + w.val) + f a) + dotProduct (M.mulVec w.val) v.val := by
              have hb := hbil v.val w.val
              rw [dotProduct_comm] at hb
              have hz1 := z2_add_self (f (a + w.val)); have hz2 := z2_add_self (f a)
              linear_combination hb - hz1 - hz2
            rw [heq, sgn_add]
    rw [h1]
    simp_rw [sum_sgn_dot_submodule U]
    have hfilt : (∑ w : U, sgn (f (a + w.val) + f a) *
          if M.mulVec w.val ∈ orthoComp U then (2 : ℤ) ^ Module.finrank F2 U else 0) =
        (2 : ℤ) ^ Module.finrank F2 U * ∑ w : K, sgn (f (a + w.val) + f a) := by
      have hite : ∀ w : U, sgn (f (a + w.val) + f a) *
            (if M.mulVec w.val ∈ orthoComp U then (2 : ℤ) ^ Module.finrank F2 U else 0) =
          if M.mulVec w.val ∈ orthoComp U then (2 : ℤ) ^ Module.finrank F2 U * sgn (f (a + w.val) + f a) else 0 := by
        intro w; split_ifs <;> ring
      simp_rw [hite, ← Finset.sum_filter, ← Finset.mul_sum]
      congr 1
      let eK : K ≃ {w : U // M.mulVec w.val ∈ orthoComp U} :=
        { toFun := fun w => ⟨⟨w.val, w.property.1⟩, fun v hv => by rw [dotProduct_comm]; exact w.property.2 v hv⟩
          invFun := fun w => ⟨w.val.val, ⟨w.val.property, fun v hv => by rw [dotProduct_comm]; exact w.property v hv⟩⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Finset.sum_subtype (Finset.univ.filter (fun w : U => M.mulVec w.val ∈ orthoComp U))
        (p := fun w : U => M.mulVec w.val ∈ orthoComp U)
        (fun w => by simp) (fun w => sgn (f (a + w.val) + f a))]
      exact (Equiv.sum_comp eK (fun w : {w : U // M.mulVec w.val ∈ orthoComp U} => sgn (f (a + w.val.val) + f a))).symm
    exact hfilt
  let L : K →ₗ[F2] F2 :=
    { toFun := fun w => f (a + w.val) + f a
      map_add' := fun w1 w2 => by
        have hb := hbil w1.val w2.val
        have h0 : dotProduct w1.val (M.mulVec w2.val) = 0 := w2.property.2 w1.val w1.property.1
        rw [h0] at hb
        have hz1 := z2_add_self (f (a + w1.val)); have hz2 := z2_add_self (f (a + w2.val))
        have hz3 := z2_add_self (f a)
        linear_combination hb - hz1 - hz2 - hz3
      map_smul' := fun c w => by
        rcases z2_cases c with rfl | rfl
        · simp [z2_add_self]
        · simp }
  have hsumL : (∑ w : K, sgn (f (a + w.val) + f a)) = if L = 0 then (2 : ℤ) ^ Module.finrank F2 K else 0 :=
    sum_sgn_linear_submodule K L
  rw [hsumL] at hsq
  refine ⟨hdim_sum, ?_⟩
  by_cases hL0 : L = 0
  · rw [if_pos hL0] at hsq
    right
    have hnat : S.natAbs ^ 2 = 2 ^ (Module.finrank F2 U + Module.finrank F2 K) := by
      have hz : (S.natAbs : ℤ) ^ 2 = (2 : ℤ) ^ (Module.finrank F2 U + Module.finrank F2 K) := by
        rw [sq, ← Nat.cast_mul, Int.natAbs_mul_self, hsq, ← pow_add]
      exact_mod_cast hz
    rcases sq_eq_two_pow S.natAbs (Module.finrank F2 U + Module.finrank F2 K) hnat with ⟨heven, habs⟩
    refine ⟨habs, heven, fun w hw => ?_⟩
    have h0 : f (a + w) + f a = 0 := LinearMap.congr_fun hL0 ⟨w, hw⟩
    have hz := z2_add_self (f a)
    linear_combination h0 - hz
  · rw [if_neg hL0, mul_zero] at hsq
    left
    exact mul_self_eq_zero.mp hsq

lemma full_bias_cell_props {n m : ℕ} (f : (Fin n → F2) → F2) (M : Matrix (Fin n) (Fin n) F2)
    (hrk : M.rank = 2 * m)
    (hf : ∀ x y, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (a : Fin n → F2) (U : Submodule F2 (Fin n → F2))
    (hfull : (∑ v : U, sgn (f (a + v.val))).natAbs = 2 ^ (n - m)) :
    let K : Submodule F2 (Fin n → F2) :=
      U ⊓ ({ carrier := {w | ∀ v ∈ U, dotProduct v (M.mulVec w) = 0}
             zero_mem' := fun v _ => by simp
             smul_mem' := fun c {w} hw v hv => (by rw [Matrix.mulVec_smul, dotProduct_smul, hw v hv, smul_zero]), add_mem' := fun {w1 w2} h1 h2 v hv => (by rw [Matrix.mulVec_add, dotProduct_add, h1 v hv, h2 v hv, add_zero]) } : Submodule F2 (Fin n → F2))
    Module.finrank F2 U + Module.finrank F2 K = 2 * (n - m) ∧
    LinearMap.ker M.mulVecLin ≤ K ∧
    (∀ w ∈ K, f (a + w) = f a) ∧
    orthoComp (Submodule.map M.mulVecLin K) = U ∧
    (∑ x : Fin n → F2, sgn (f x)) = ∑ v : U, sgn (f (a + v.val)) := by
  intro K
  have h2m_le_n : 2 * m ≤ n := by have := rank_add_ker_mat M; omega
  rcases quad_coset_bias_structure f M hrk hf a U with ⟨hdim_le, hzero | ⟨habs, heven, hconst⟩⟩
  · exfalso; rw [hzero] at hfull; change 0 = 2 ^ (n - m) at hfull; have hpos : 0 < 2 ^ (n - m) := (by positivity); omega
  have hdim_eq : Module.finrank F2 U + Module.finrank F2 K = 2 * (n - m) := by
    have h1 : (Module.finrank F2 U + Module.finrank F2 K) / 2 = n - m := by
      have hpow : 2 ^ ((Module.finrank F2 U + Module.finrank F2 K) / 2) = 2 ^ (n - m) := by
        rw [← habs, hfull]
      exact Nat.pow_right_injective (by omega) hpow
    rcases heven with ⟨k, hk⟩
    rw [hk] at h1 ⊢; omega
  have hR_le_K : LinearMap.ker M.mulVecLin ≤ K := by
    let T : K →ₗ[F2] orthoComp U :=
      { toFun := fun w => ⟨M.mulVec w.val, fun v hv => by rw [dotProduct_comm]; exact w.property.2 v hv⟩
        map_add' := fun x y => Subtype.ext (Matrix.mulVec_add M x.val y.val)
        map_smul' := fun c x => Subtype.ext (Matrix.mulVec_smul M c x.val) }
    have hrkT := LinearMap.finrank_range_add_finrank_ker T
    have hran : Module.finrank F2 (LinearMap.range T) ≤ Module.finrank F2 (orthoComp U) := Submodule.finrank_le _
    let embKer : LinearMap.ker T →ₗ[F2] LinearMap.ker M.mulVecLin :=
      { toFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hemb_inj : Function.Injective embKer := fun x y hxy => by
      have h : (embKer x).val = (embKer y).val := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h)
    have hker_le : Module.finrank F2 (LinearMap.ker T) ≤ Module.finrank F2 (LinearMap.ker M.mulVecLin) :=
      LinearMap.finrank_le_finrank_of_injective hemb_inj
    have horth := finrank_orthoComp U
    have hMrk := rank_add_ker_mat M
    have hker_eq : Module.finrank F2 (LinearMap.ker T) = Module.finrank F2 (LinearMap.ker M.mulVecLin) := by omega
    have hcard_eq : Fintype.card (LinearMap.ker T) = Fintype.card (LinearMap.ker M.mulVecLin) := by
      have hc1 := Module.card_eq_pow_finrank (K := F2) (V := LinearMap.ker T)
      have hc2 := Module.card_eq_pow_finrank (K := F2) (V := LinearMap.ker M.mulVecLin)
      simp only [Nat.card_eq_fintype_card, ZMod.card] at hc1 hc2
      rw [hc1, hc2, hker_eq]
    have hsurj : Function.Surjective embKer :=
      ((Fintype.bijective_iff_injective_and_card embKer).mpr ⟨hemb_inj, hcard_eq⟩).2
    intro r hr
    obtain ⟨x, hx⟩ := hsurj ⟨r, hr⟩
    have hxr : x.val.val = r := congrArg Subtype.val hx
    rw [← hxr]; exact x.val.property
  have hKorth : orthoComp (Submodule.map M.mulVecLin K) = U := by
    have hle : U ≤ orthoComp (Submodule.map M.mulVecLin K) := by
      intro u hu z hz
      rcases Submodule.mem_map.mp hz with ⟨w, hw, rfl⟩
      exact hw.2 u hu
    have hdim_img : Module.finrank F2 (Submodule.map M.mulVecLin K) + Module.finrank F2 (LinearMap.ker M.mulVecLin) =
        Module.finrank F2 K := by
      have h1 := LinearMap.finrank_range_add_finrank_ker (M.mulVecLin.domRestrict K)
      have hr : LinearMap.range (M.mulVecLin.domRestrict K) = Submodule.map M.mulVecLin K := by
        ext z; simp [Submodule.mem_map]
      let eK : LinearMap.ker (M.mulVecLin.domRestrict K) ≃ₗ[F2] LinearMap.ker M.mulVecLin :=
        { toFun := fun x => ⟨x.val.val, x.property⟩
          invFun := fun r => ⟨⟨r.val, hR_le_K r.property⟩, r.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      rw [hr, LinearEquiv.finrank_eq eK] at h1
      exact h1
    have hMrk := rank_add_ker_mat M
    have horth := finrank_orthoComp (Submodule.map M.mulVecLin K)
    have hdim_eq_U : Module.finrank F2 U = Module.finrank F2 (orthoComp (Submodule.map M.mulVecLin K)) := by omega
    exact (Submodule.eq_of_le_of_finrank_eq hle hdim_eq_U).symm
  have hsum_eq : (∑ x : Fin n → F2, sgn (f x)) = ∑ v : U, sgn (f (a + v.val)) := by
    have hshift : (∑ x : Fin n → F2, sgn (f x)) = ∑ x : Fin n → F2, sgn (f (a + x)) := by
      let e : (Fin n → F2) ≃ (Fin n → F2) :=
        { toFun := fun x => a + x
          invFun := fun x => a + x
          left_inv := fun x => by dsimp only; rw [← add_assoc, z2_vec_add_self, zero_add]
          right_inv := fun x => by dsimp only; rw [← add_assoc, z2_vec_add_self, zero_add] }
      exact (Equiv.sum_comp e (fun x => sgn (f x))).symm
    have hmul : (2 : ℤ) ^ Module.finrank F2 K * (∑ x : Fin n → F2, sgn (f (a + x))) =
        (2 : ℤ) ^ Module.finrank F2 K * (∑ v : U, sgn (f (a + v.val))) := by
      have hcardK : ((2 : ℤ) ^ Module.finrank F2 K) = ∑ _w : K, (1 : ℤ) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, card_submodule_z2]
        push_cast; rfl
      calc (2 : ℤ) ^ Module.finrank F2 K * (∑ x : Fin n → F2, sgn (f (a + x)))
          = ∑ w : K, ∑ x : Fin n → F2, sgn (f (a + x)) := by
              rw [hcardK, Finset.sum_mul]; refine Finset.sum_congr rfl fun _ _ => one_mul _
        _ = ∑ w : K, ∑ x : Fin n → F2, sgn (f (a + (x + w.val))) := by
              refine Finset.sum_congr rfl fun w _ => ?_
              let ew : (Fin n → F2) ≃ (Fin n → F2) :=
                { toFun := fun x => x + w.val
                  invFun := fun x => x + w.val
                  left_inv := fun x => by dsimp only; rw [add_assoc, z2_vec_add_self, add_zero]
                  right_inv := fun x => by dsimp only; rw [add_assoc, z2_vec_add_self, add_zero] }
              exact (Equiv.sum_comp ew (fun x => sgn (f (a + x)))).symm
        _ = ∑ x : Fin n → F2, sgn (f (a + x)) * ∑ w : K, sgn (dotProduct (M.mulVec x) w.val) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun w _ => ?_
              have hbil : f (a + (x + w.val)) = f (a + x) + dotProduct (M.mulVec x) w.val := by
                have e1 := hf a (x + w.val); have e2 := hf a x; have e3 := hf a w.val; have e4 := hf x w.val
                rw [Matrix.mulVec_add, dotProduct_add] at e1
                have hcw : f (a + w.val) = f a := hconst w.val w.property
                have hsym := polar_symm f M hf x w.val
                have hz1 := z2_add_self (f (a + x)); have hz2 := z2_add_self (f (x + w.val))
                have hz3 := z2_add_self (f x); have hz4 := z2_add_self (f w.val)
                have hz5 := z2_add_self (f 0); have hz6 := z2_add_self (f a)
                have hz7 := z2_add_self (dotProduct a (M.mulVec x))
                have hz8 := z2_add_self (dotProduct a (M.mulVec w.val))
                rw [dotProduct_comm w.val] at hsym
                linear_combination e1 + e2 + e3 + e4 - hcw + hsym - hz1 - hz2 - hz3 - hz4 - 2 * hz5 - 2 * hz6 + hz7 + hz8
              rw [hbil, sgn_add]
        _ = ∑ x : Fin n → F2, sgn (f (a + x)) * if x ∈ U then (2 : ℤ) ^ Module.finrank F2 K else 0 := by
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [sum_sgn_dot_submodule K]
              have hmem : M.mulVec x ∈ orthoComp K ↔ x ∈ U := by
                rw [← hKorth]
                constructor
                · intro hx z hz
                  rcases Submodule.mem_map.mp hz with ⟨w, hw, rfl⟩
                  change dotProduct x (M.mulVec w) = 0
                  rw [polar_symm f M hf, dotProduct_comm]
                  exact hx w hw
                · intro hx w hw
                  rw [dotProduct_comm, ← polar_symm f M hf]
                  exact hx (M.mulVec w) (Submodule.mem_map_of_mem hw)
              rw [hmem]
        _ = (2 : ℤ) ^ Module.finrank F2 K * ∑ v : U, sgn (f (a + v.val)) := by
              have hite : ∀ x : Fin n → F2, sgn (f (a + x)) * (if x ∈ U then (2 : ℤ) ^ Module.finrank F2 K else 0) =
                  if x ∈ U then (2 : ℤ) ^ Module.finrank F2 K * sgn (f (a + x)) else 0 := by
                intro x; split_ifs <;> ring
              simp_rw [hite, ← Finset.sum_filter, ← Finset.mul_sum]
              congr 1
              exact Finset.sum_subtype (Finset.univ.filter (fun x : Fin n → F2 => x ∈ U))
                (p := fun x => x ∈ U)
                (fun x => by simp) (fun x => sgn (f (a + x)))
    rw [hshift]
    have hpos : (2 : ℤ) ^ Module.finrank F2 K ≠ 0 := by positivity
    exact mul_left_cancel₀ hpos hmul
  exact ⟨hdim_eq, hR_le_K, hconst, hKorth, hsum_eq⟩

lemma full_bias_cells_intersect {n m : ℕ} (f : (Fin n → F2) → F2) (M : Matrix (Fin n) (Fin n) F2)
    (hrk : M.rank = 2 * m)
    (hf : ∀ x y, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (a1 a2 : Fin n → F2) (U1 U2 : Submodule F2 (Fin n → F2))
    (h1 : (∑ v : U1, sgn (f (a1 + v.val))).natAbs = 2 ^ (n - m))
    (h2 : (∑ v : U2, sgn (f (a2 + v.val))).natAbs = 2 ^ (n - m)) :
    ∃ x : Fin n → F2, x - a1 ∈ U1 ∧ x - a2 ∈ U2 := by
  let K1 : Submodule F2 (Fin n → F2) :=
    U1 ⊓ ({ carrier := {w | ∀ v ∈ U1, dotProduct v (M.mulVec w) = 0}
            zero_mem' := fun v _ => by simp
            smul_mem' := fun c {w} hw v hv => (by rw [Matrix.mulVec_smul, dotProduct_smul, hw v hv, smul_zero]), add_mem' := fun {w1 w2} ha hb v hv => (by rw [Matrix.mulVec_add, dotProduct_add, ha v hv, hb v hv, add_zero]) } : Submodule F2 (Fin n → F2))
  let K2 : Submodule F2 (Fin n → F2) :=
    U2 ⊓ ({ carrier := {w | ∀ v ∈ U2, dotProduct v (M.mulVec w) = 0}
            zero_mem' := fun v _ => by simp
            smul_mem' := fun c {w} hw v hv => (by rw [Matrix.mulVec_smul, dotProduct_smul, hw v hv, smul_zero]), add_mem' := fun {w1 w2} ha hb v hv => (by rw [Matrix.mulVec_add, dotProduct_add, ha v hv, hb v hv, add_zero]) } : Submodule F2 (Fin n → F2))
  rcases full_bias_cell_props f M hrk hf a1 U1 h1 with ⟨hd1, hR1, hc1, hKo1, _⟩
  rcases full_bias_cell_props f M hrk hf a2 U2 h2 with ⟨hd2, hR2, hc2, hKo2, _⟩
  let W : Submodule F2 (Fin n → F2) := K1 ⊓ K2
  have hR_le_W : LinearMap.ker M.mulVecLin ≤ W := le_inf hR1 hR2
  have hdiff_mem : a1 - a2 ∈ orthoComp (Submodule.map M.mulVecLin W) := by
    intro z hz
    rcases Submodule.mem_map.mp hz with ⟨w, hw, rfl⟩
    rw [z2_vec_sub_eq_add, add_dotProduct]
    have e1 := hf a1 w
    have e2 := hf a2 w
    have hcw1 : f (a1 + w) = f a1 := hc1 w hw.1
    have hcw2 : f (a2 + w) = f a2 := hc2 w hw.2
    have hz1 := z2_add_self (f a1); have hz2 := z2_add_self (f a2)
    have hz3 := z2_add_self (f w); have hz4 := z2_add_self (f 0)
    change dotProduct a1 (M.mulVec w) + dotProduct a2 (M.mulVec w) = 0
    rw [← e1, ← e2, hcw1, hcw2]
    linear_combination hz1 + hz2 + hz3 + hz4
  have hsup_le : U1 ⊔ U2 ≤ orthoComp (Submodule.map M.mulVecLin W) := by
    refine sup_le ?_ ?_
    · rw [← hKo1]; intro u hu z hz
      rcases Submodule.mem_map.mp hz with ⟨w, hw, rfl⟩
      exact hu (M.mulVec w) (Submodule.mem_map_of_mem hw.1)
    · rw [← hKo2]; intro u hu z hz
      rcases Submodule.mem_map.mp hz with ⟨w, hw, rfl⟩
      exact hu (M.mulVec w) (Submodule.mem_map_of_mem hw.2)
  have hdim_map_ge : ∀ (A : Submodule F2 (Fin n → F2)), LinearMap.ker M.mulVecLin ≤ A →
      Module.finrank F2 (Submodule.map M.mulVecLin A) + Module.finrank F2 (LinearMap.ker M.mulVecLin) =
        Module.finrank F2 A := by
    intro A hRA
    have h1 := LinearMap.finrank_range_add_finrank_ker (M.mulVecLin.domRestrict A)
    have hr : LinearMap.range (M.mulVecLin.domRestrict A) = Submodule.map M.mulVecLin A := by
      ext z; simp [Submodule.mem_map]
    let eA : LinearMap.ker (M.mulVecLin.domRestrict A) ≃ₗ[F2] LinearMap.ker M.mulVecLin :=
      { toFun := fun x => ⟨x.val.val, x.property⟩
        invFun := fun r => ⟨⟨r.val, hRA r.property⟩, r.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    rw [hr, LinearEquiv.finrank_eq eA] at h1
    exact h1
  have hmap_sup_le : Submodule.map M.mulVecLin (K1 ⊔ K2) ≤ orthoComp (U1 ⊓ U2) := by
    intro z hz u hu
    rcases Submodule.mem_map.mp hz with ⟨w, hw, rfl⟩
    rcases Submodule.mem_sup.mp hw with ⟨w1, hw1, w2, hw2, rfl⟩
    rw [map_add, add_dotProduct]
    change dotProduct (M.mulVec w1) u + dotProduct (M.mulVec w2) u = 0
    rw [dotProduct_comm (M.mulVec w1) u, dotProduct_comm (M.mulVec w2) u, hw1.2 u hu.1, hw2.2 u hu.2, add_zero]
  have hdim_map_W := hdim_map_ge W hR_le_W
  have hdim_map_sup := hdim_map_ge (K1 ⊔ K2) (le_trans hR1 le_sup_left)
  have hdim_K_sup := Submodule.finrank_sup_add_finrank_inf_eq K1 K2
  have hdim_U_sup := Submodule.finrank_sup_add_finrank_inf_eq U1 U2
  have hdim_orth_W := finrank_orthoComp (Submodule.map M.mulVecLin W)
  have hdim_orth_U := finrank_orthoComp (U1 ⊓ U2)
  have hdim_le_orth : Module.finrank F2 (Submodule.map M.mulVecLin (K1 ⊔ K2)) ≤
      Module.finrank F2 (orthoComp (U1 ⊓ U2)) := Submodule.finrank_mono hmap_sup_le
  have hMrk := rank_add_ker_mat M
  have hdim_eq : Module.finrank F2 ↥(U1 ⊔ U2) = Module.finrank F2 (orthoComp (Submodule.map M.mulVecLin W)) := by
    have hle := Submodule.finrank_mono hsup_le
    dsimp only [W] at hdim_map_W hdim_orth_W hle ⊢
    change Module.finrank F2 U1 + Module.finrank F2 K1 = 2 * (n - m) at hd1
    change Module.finrank F2 U2 + Module.finrank F2 K2 = 2 * (n - m) at hd2
    omega
  have hsup_eq : U1 ⊔ U2 = orthoComp (Submodule.map M.mulVecLin W) :=
    Submodule.eq_of_le_of_finrank_eq hsup_le hdim_eq
  rw [← hsup_eq] at hdiff_mem
  rcases Submodule.mem_sup.mp hdiff_mem with ⟨u1, hu1, u2, hu2, hu12⟩
  refine ⟨a1 + u1, ?_, ?_⟩
  · simpa [z2_vec_sub_eq_add, add_assoc] using hu1
  · have hEq : a1 + u1 - a2 = u2 := by
      have hsub : a1 - a2 = u1 + u2 := hu12.symm
      rw [z2_vec_sub_eq_add] at hsub ⊢
      calc a1 + u1 + a2 = (a1 + a2) + u1 := by abel
        _ = (u1 + u2) + u1 := by rw [hsub]
        _ = (u1 + u1) + u2 := by abel
        _ = u2 := by rw [z2_vec_add_self, zero_add]
    rw [hEq]; exact hu2

lemma tree_mem_J_of_prefix {N J : Finset (List Bool)}
    (hback : ∀ (p : List Bool) (v : Bool), p ++ [v] ∈ N → p ∈ J)
    (hJN : J ⊆ N) :
    ∀ (p q : List Bool), q ≠ [] → p ++ q ∈ N → p ∈ J := by
  intro p q hqne hpq
  induction q using List.reverseRecOn generalizing p with
  | nil => exact absurd rfl hqne
  | append_singleton q' v ih =>
    have hmem : (p ++ q') ++ [v] ∈ N := by simpa [List.append_assoc] using hpq
    have hJ' : p ++ q' ∈ J := hback (p ++ q') v hmem
    cases q' with
    | nil => simpa using hJ'
    | cons b t => exact ih p (by simp) (hJN hJ')

lemma tree_leaf_partition {n : ℕ} (N J : Finset (List Bool))
    (q : List Bool → (Fin n → F2) →ₗ[F2] F2) (offset : List Bool → F2)
    (hroot : [] ∈ N) (hJN : J ⊆ N)
    (hback : ∀ (p : List Bool) (v : Bool), p ++ [v] ∈ N → p ∈ J)
    (hfwd : ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) :
    let leaf := N \ J
    let reaches := fun (p : List Bool) (x : Fin n → F2) => ∀ step : Fin p.length,
      decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step
    ∀ x : Fin n → F2, ∃! p : List Bool, p ∈ leaf ∧ reaches p x := by
  intro leaf reaches x
  have hex : ∀ (k : ℕ) (p : List Bool), p ∈ N → reaches p x →
      N.sup List.length - p.length ≤ k → ∃ p' ∈ leaf, reaches p' x := by
    intro k
    induction k with
    | zero =>
      intro p hp hr hk
      by_cases hJ : p ∈ J
      · exfalso
        have hf1 := (hfwd p hJ).1
        have hle : (p ++ [false]).length ≤ N.sup List.length := Finset.le_sup (f := List.length) hf1
        simp only [List.length_append, List.length_singleton] at hle
        omega
      · exact ⟨p, Finset.mem_sdiff.mpr ⟨hp, hJ⟩, hr⟩
    | succ k ih =>
      intro p hp hr hk
      by_cases hJ : p ∈ J
      · let b : Bool := decide (q p x = offset p)
        have hpb : p ++ [b] ∈ N := by cases b; exact (hfwd p hJ).1; exact (hfwd p hJ).2
        have hreach : reaches (p ++ [b]) x := by
          intro step
          by_cases hlt : step.val < p.length
          · have htake : (p ++ [b]).take step.val = p.take step.val := by
              rw [List.take_append_of_le_length (by omega)]
            have hget : (p ++ [b]).get step = p.get ⟨step.val, hlt⟩ := by
              simp [List.get_eq_getElem, List.getElem_append_left hlt]
            rw [htake, hget]; exact hr ⟨step.val, hlt⟩
          · have heq : step.val = p.length := by
              have := step.isLt; simp only [List.length_append, List.length_singleton] at this; omega
            have htake : (p ++ [b]).take step.val = p := by rw [heq]; simp
            have hget : (p ++ [b]).get step = b := by
              simp [List.get_eq_getElem, heq]
            rw [htake, hget]
        exact ih (p ++ [b]) hpb hreach (by simp only [List.length_append, List.length_singleton]; omega)
      · exact ⟨p, Finset.mem_sdiff.mpr ⟨hp, hJ⟩, hr⟩
  obtain ⟨p0, hp0, hr0⟩ := hex (N.sup List.length) [] hroot (fun s => s.elim0) (by omega)
  refine ⟨p0, ⟨hp0, hr0⟩, ?_⟩
  intro p1 ⟨hp1, hr1⟩
  by_contra hne
  have hprefix_or_diff : (∃ j : ℕ, ∃ h1 : j < p1.length, ∃ h0 : j < p0.length,
      p1.get ⟨j, h1⟩ ≠ p0.get ⟨j, h0⟩ ∧ ∀ i < j, ∀ hi1 : i < p1.length, ∀ hi0 : i < p0.length,
        p1.get ⟨i, hi1⟩ = p0.get ⟨i, hi0⟩) ∨
      (∃ r : List Bool, r ≠ [] ∧ (p1 ++ r = p0 ∨ p0 ++ r = p1)) := by
    by_cases hdiff : ∃ j : ℕ, ∃ h1 : j < p1.length, ∃ h0 : j < p0.length, p1.get ⟨j, h1⟩ ≠ p0.get ⟨j, h0⟩
    · left
      let j := Nat.find hdiff
      rcases Nat.find_spec hdiff with ⟨h1, h0, hne_j⟩
      refine ⟨j, h1, h0, hne_j, fun i hi hi1 hi0 => ?_⟩
      by_contra hne_i
      exact Nat.find_min hdiff hi ⟨hi1, hi0, hne_i⟩
    · right
      push Not at hdiff
      by_cases hlen : p1.length < p0.length
      · refine ⟨p0.drop p1.length, by intro hd; have := congrArg List.length hd; simp at this; omega, Or.inl ?_⟩
        apply List.ext_getElem (by simp; omega)
        intro i hi1 hi0
        by_cases hlt : i < p1.length
        · rw [List.getElem_append_left hlt]
          exact hdiff i hlt (by omega)
        · rw [List.getElem_append_right (by omega)]; simp [Nat.add_sub_cancel' (by omega : p1.length ≤ i)]
      · have hlen2 : p0.length < p1.length := by
          by_contra hge
          have heql : p1.length = p0.length := by omega
          apply hne
          apply List.ext_getElem heql
          intro i hi1 hi0
          exact hdiff i hi1 hi0
        refine ⟨p1.drop p0.length, by intro hd; have := congrArg List.length hd; simp at this; omega, Or.inr ?_⟩
        apply List.ext_getElem (by simp; omega)
        intro i hi1 hi0
        by_cases hlt : i < p0.length
        · rw [List.getElem_append_left hlt]
          exact (hdiff i (by omega) hlt).symm
        · rw [List.getElem_append_right (by omega)]; simp [Nat.add_sub_cancel' (by omega : p0.length ≤ i)]
  rcases hprefix_or_diff with ⟨j, h1, h0, hne_j, hlt_eq⟩ | ⟨r, hrne, hcat | hcat⟩
  · have htake : p1.take j = p0.take j := by
      apply List.ext_getElem (by simp; omega)
      intro i hi1 hi0
      simp only [List.getElem_take]
      have hij : i < j := by simp at hi1; omega
      exact hlt_eq i hij (by omega) (by omega)
    have h1' := hr1 ⟨j, h1⟩
    have h0' := hr0 ⟨j, h0⟩
    rw [htake] at h1'
    exact hne_j (h1'.symm.trans h0')
  · have hJ1 : p1 ∈ J := tree_mem_J_of_prefix hback hJN p1 r hrne (hcat ▸ (Finset.mem_sdiff.mp hp0).1)
    exact (Finset.mem_sdiff.mp hp1).2 hJ1
  · have hJ0 : p0 ∈ J := tree_mem_J_of_prefix hback hJN p0 r hrne (hcat ▸ (Finset.mem_sdiff.mp hp1).1)
    exact (Finset.mem_sdiff.mp hp0).2 hJ0

lemma finrank_inf_ker_le {n : ℕ} (U : Submodule F2 (Fin n → F2)) (L : (Fin n → F2) →ₗ[F2] F2) :
    Module.finrank F2 U ≤ Module.finrank F2 ↥(U ⊓ LinearMap.ker L) + 1 := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (L.domRestrict U)
  have h1 : Module.finrank F2 (LinearMap.range (L.domRestrict U)) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range (L.domRestrict U))
    rwa [Module.finrank_self] at this
  let e : LinearMap.ker (L.domRestrict U) ≃ₗ[F2] (U ⊓ LinearMap.ker L : Submodule F2 (Fin n → F2)) :=
    { toFun := fun x => ⟨x.val.val, ⟨x.val.property, x.property⟩⟩
      invFun := fun y => ⟨⟨y.val, y.property.1⟩, y.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  rw [LinearEquiv.finrank_eq e] at hrk
  omega

lemma tree_leaf_coset {n : ℕ} (q : List Bool → (Fin n → F2) →ₗ[F2] F2) (offset : List Bool → F2)
    (p : List Bool) (a : Fin n → F2)
    (ha : ∀ step : Fin p.length, decide (q (p.take step.val) a = offset (p.take step.val)) = p.get step) :
    let S : Submodule F2 (Fin n → F2) := ⨅ step : Fin p.length, LinearMap.ker (q (p.take step.val))
    n ≤ Module.finrank F2 S + p.length ∧
    ∀ x : Fin n → F2,
      (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step) ↔
        x - a ∈ S := by
  intro S
  have hcodim : ∀ (l : List ((Fin n → F2) →ₗ[F2] F2)),
      n ≤ Module.finrank F2 ↥(⨅ i : Fin l.length, LinearMap.ker (l.get i)) + l.length := by
    intro l
    induction l with
    | nil =>
      have : (⨅ i : Fin ([] : List ((Fin n → F2) →ₗ[F2] F2)).length, LinearMap.ker (([] : List _).get i)) = ⊤ := by
        ext x; simp
      rw [this, finrank_top, Module.finrank_fin_fun]; simp
    | cons L tl ih =>
      have hinf : (⨅ i : Fin (L :: tl).length, LinearMap.ker ((L :: tl).get i)) =
          (⨅ i : Fin tl.length, LinearMap.ker (tl.get i)) ⊓ LinearMap.ker L := by
        ext x
        simp only [Submodule.mem_iInf, Submodule.mem_inf]
        constructor
        · intro h
          refine ⟨fun i => h i.succ, h 0⟩
        · rintro ⟨htl, h0⟩ i
          exact Fin.cases h0 htl i
      rw [hinf]
      have hstep := finrank_inf_ker_le (⨅ i : Fin tl.length, LinearMap.ker (tl.get i)) L
      simp only [List.length_cons]; omega
  refine ⟨?_, ?_⟩
  · let l : List ((Fin n → F2) →ₗ[F2] F2) := (List.finRange p.length).map fun step => q (p.take step.val)
    have hS : S = ⨅ i : Fin l.length, LinearMap.ker (l.get i) := by
      ext x
      simp only [S, Submodule.mem_iInf, LinearMap.mem_ker]
      constructor
      · intro h i
        have hi : i.val < p.length := by simpa [l] using i.isLt
        have hget : l.get i = q (p.take i.val) := by
          simp [l, List.get_eq_getElem]
        rw [hget]; exact h ⟨i.val, hi⟩
      · intro h step
        have hi : step.val < l.length := by simpa [l] using step.isLt
        have hget : l.get ⟨step.val, hi⟩ = q (p.take step.val) := by
          simp [l, List.get_eq_getElem]
        rw [← hget]; exact h ⟨step.val, hi⟩
    rw [hS]
    have hlen : l.length = p.length := by simp [l]
    have hc := hcodim l
    omega
  · intro x
    simp only [S, Submodule.mem_iInf, LinearMap.mem_ker, map_sub, sub_eq_zero]
    refine forall_congr' fun step => ?_
    rw [← ha step, z2_decide_eq_iff]

lemma nat_pow_ge_add_one (d : ℕ) : d + 1 ≤ 2 ^ d := by
  induction d with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

lemma tree_cost_adv_bound {n m : ℕ} (f : (Fin n → F2) → F2) (M : Matrix (Fin n) (Fin n) F2)
    (hrk : M.rank = 2 * m)
    (hf : ∀ x y, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (cost adv : ℚ)
    (N J : Finset (List Bool)) (q : List Bool → (Fin n → F2) →ₗ[F2] F2) (offset out : List Bool → F2)
    (hroot : [] ∈ N) (hJN : J ⊆ N)
    (hback : ∀ (p : List Bool) (v : Bool), p ++ [v] ∈ N → p ∈ J)
    (hfwd : ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N)
    (hcost : cost * (Nat.card (Fin n → F2) : ℚ) =
      ∑ p ∈ N \ J, (p.length : ℚ) * (Nat.card {x : Fin n → F2 // ∀ step : Fin p.length,
        decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step} : ℚ))
    (hadv : (adv + 1) * (Nat.card (Fin n → F2) : ℚ) =
      2 * (Nat.card {x : Fin n → F2 // ∃ p ∈ N \ J, (∀ step : Fin p.length,
        decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step) ∧ f x = out p} : ℚ)) :
    let bal := Nat.card {x : Fin n → F2 // f x = 0} = Nat.card {x : Fin n → F2 // f x = 1}
    let rootBias : ℚ := if bal then 0 else 1 / (2 : ℚ) ^ m
    let exactCost : ℚ := (m : ℚ) + 1 - rootBias
    0 ≤ cost ∧ adv ≤ 1 ∧
    (J = ∅ → cost = 0 ∧ adv ≤ rootBias) ∧
    (J ≠ ∅ → ((m : ℚ) + 1) * adv - rootBias ≤ cost ∧ (adv = rootBias → 0 < cost)) ∧
    (1 - rootBias) * cost ≥ exactCost * (adv - rootBias) ∧
    ((¬ bal) → 0 < m → (1 - rootBias) * cost = exactCost * (adv - rootBias) →
      (cost = 0 ∧ adv = rootBias) ∨ (cost = exactCost ∧ adv = 1)) := by
  intro bal rootBias exactCost
  have h2m_le_n : 2 * m ≤ n := by have := rank_add_ker_mat M; omega
  have hcardX : (Nat.card (Fin n → F2) : ℚ) = (2 : ℚ) ^ n := by
    rw [Nat.card_eq_fintype_card]; simp [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have h2n_pos : (0 : ℚ) < (2 : ℚ) ^ n := by positivity
  let leaf := N \ J
  let reaches := fun (p : List Bool) (x : Fin n → F2) => ∀ step : Fin p.length,
    decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step
  have hpart := tree_leaf_partition N J q offset hroot hJN hback hfwd
  have hcost_nonneg : 0 ≤ cost := by
    have hsum_nn : (0 : ℚ) ≤ ∑ p ∈ leaf, (p.length : ℚ) * (Nat.card {x : Fin n → F2 // reaches p x} : ℚ) :=
      Finset.sum_nonneg fun p _ => by positivity
    rw [hcardX] at hcost
    nlinarith
  have hadv_le1 : adv ≤ 1 := by
    have hcard_le : Nat.card {x : Fin n → F2 // ∃ p ∈ leaf, reaches p x ∧ f x = out p} ≤ 2 ^ n := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      have h := Finset.card_filter_le (Finset.univ : Finset (Fin n → F2))
        (fun x => ∃ p ∈ leaf, reaches p x ∧ f x = out p)
      simpa [Fintype.card_fun, Fintype.card_fin, ZMod.card] using h
    have hq : (Nat.card {x : Fin n → F2 // ∃ p ∈ leaf, reaches p x ∧ f x = out p} : ℚ) ≤ (2 : ℚ) ^ n := by
      exact_mod_cast hcard_le
    rw [hcardX] at hadv
    nlinarith
  have hSf_spec : let Sf : ℤ := ∑ x : Fin n → F2, sgn (f x)
      (bal ↔ Sf = 0) ∧ (¬ bal → Sf.natAbs = 2 ^ (n - m)) := by
    intro Sf
    have hSf_diff : Sf = (Nat.card {x : Fin n → F2 // f x = 0} : ℤ) -
        (Nat.card {x : Fin n → F2 // f x = 1} : ℤ) := by
      dsimp only [Sf]
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype]
      have h1 : ∀ x : Fin n → F2, sgn (f x) = (if f x = 0 then (1 : ℤ) else 0) - (if f x = 1 then (1 : ℤ) else 0) := by
        intro x; rcases z2_cases (f x) with h | h <;> rw [h] <;> decide
      simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_boole]
    have hbal_iff : bal ↔ Sf = 0 := by
      dsimp only [bal]; rw [hSf_diff]; omega
    refine ⟨hbal_iff, fun hnbal => ?_⟩
    have hne : Sf ≠ 0 := fun h => hnbal (hbal_iff.mpr h)
    have htop := quad_coset_bias_structure f M hrk hf 0 (⊤ : Submodule F2 (Fin n → F2))
    have hKtop : ((⊤ : Submodule F2 (Fin n → F2)) ⊓
      ({ carrier := {w | ∀ v ∈ (⊤ : Submodule F2 (Fin n → F2)), dotProduct v (M.mulVec w) = 0}
         zero_mem' := fun v _ => by simp
         smul_mem' := fun c {w} hw v hv => (by rw [Matrix.mulVec_smul, dotProduct_smul, hw v hv, smul_zero]), add_mem' := fun {w1 w2} h1 h2 v hv => (by rw [Matrix.mulVec_add, dotProduct_add, h1 v hv, h2 v hv, add_zero]) } : Submodule F2 (Fin n → F2))) =
        LinearMap.ker M.mulVecLin := by
      ext w
      simp only [Submodule.mem_inf, Submodule.mem_top, true_and, LinearMap.mem_ker]
      constructor
      · intro hw; funext i
        have := hw (Pi.single i 1) trivial
        simpa [single_dotProduct] using this
      · intro hw v _; change M.mulVec w = 0 at hw; rw [hw, dotProduct_zero]
    have hSf_top : (∑ v : (⊤ : Submodule F2 (Fin n → F2)), sgn (f (0 + v.val))) = Sf := by
      let eT : (⊤ : Submodule F2 (Fin n → F2)) ≃ (Fin n → F2) :=
        { toFun := fun v => v.val, invFun := fun x => ⟨x, trivial⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
      simp_rw [zero_add]
      exact Equiv.sum_comp eT (fun x => sgn (f x))
    rw [hSf_top] at htop
    rcases htop.2 with h0 | ⟨habs, _, _⟩
    · exact absurd h0 hne
    · rw [hKtop, finrank_top, Module.finrank_fin_fun] at habs
      have hMrk := rank_add_ker_mat M
      have hdiv : (n + Module.finrank F2 (LinearMap.ker M.mulVecLin)) / 2 = n - m := by omega
      rwa [hdiv] at habs
  have hadv_sum : adv * (2 : ℚ) ^ n =
      ∑ p ∈ leaf, ((∑ x ∈ Finset.univ.filter (fun x => reaches p x), sgn (f x + out p) : ℤ) : ℚ) := by
    rw [hcardX] at hadv
    have hsum_all : (∑ p ∈ leaf, ∑ x ∈ Finset.univ.filter (fun x => reaches p x), sgn (f x + out p)) =
        2 * (Nat.card {x : Fin n → F2 // ∃ p ∈ leaf, reaches p x ∧ f x = out p} : ℤ) - (2 : ℤ) ^ n := by
      have hpart_sum : ∀ (g : List Bool → (Fin n → F2) → ℤ),
          (∑ p ∈ leaf, ∑ x ∈ Finset.univ.filter (fun x => reaches p x), g p x) =
          ∑ x : Fin n → F2, g (hpart x).choose x := by
        intro g
        have h1 : ∀ p ∈ leaf, (∑ x ∈ Finset.univ.filter (fun x => reaches p x), g p x) =
            ∑ x : Fin n → F2, if p = (hpart x).choose then g p x else 0 := by
          intro p hp
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hr; exact (hpart x).choose_spec.2 p ⟨hp, hr⟩
          · intro heq; rw [heq]; exact (hpart x).choose_spec.1.2
        rw [Finset.sum_congr rfl h1, Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_ite_eq', if_pos (hpart x).choose_spec.1.1]
      rw [hpart_sum (fun p x => sgn (f x + out p))]
      have hcard_eq : (Nat.card {x : Fin n → F2 // ∃ p ∈ leaf, reaches p x ∧ f x = out p} : ℤ) =
          ∑ x : Fin n → F2, if f x = out (hpart x).choose then (1 : ℤ) else 0 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.sum_boole]
        refine Finset.sum_congr rfl fun x _ => ?_
        have hiff : (∃ p ∈ leaf, reaches p x ∧ f x = out p) ↔ f x = out (hpart x).choose := by
          constructor
          · rintro ⟨p, hp, hr, hfe⟩
            have heq : p = (hpart x).choose := (hpart x).choose_spec.2 p ⟨hp, hr⟩
            rwa [heq] at hfe
          · intro hfe
            exact ⟨(hpart x).choose, (hpart x).choose_spec.1.1, (hpart x).choose_spec.1.2, hfe⟩
        simp only [hiff]
      rw [hcard_eq, Finset.mul_sum]
      have h2n : (2 : ℤ) ^ n = ∑ _x : Fin n → F2, (1 : ℤ) := by simp [Fintype.card_fun, Fintype.card_fin, ZMod.card]
      rw [h2n, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← sgn_eq_iff]
      split_ifs <;> norm_num
    have hq_all : (∑ p ∈ leaf, ((∑ x ∈ Finset.univ.filter (fun x => reaches p x), sgn (f x + out p) : ℤ) : ℚ)) =
        2 * (Nat.card {x : Fin n → F2 // ∃ p ∈ leaf, reaches p x ∧ f x = out p} : ℚ) - (2 : ℚ) ^ n := by
      have h := congrArg (fun z : ℤ => (z : ℚ)) hsum_all
      simpa only [Int.cast_sum, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast] using h
    linarith
  have hJ_empty : J = ∅ → cost = 0 ∧ adv ≤ rootBias := by
    intro hJe
    have hleaf_eq : leaf = {[]} := by
      ext p; simp only [leaf, hJe, Finset.sdiff_empty, Finset.mem_singleton]
      constructor
      · intro hp
        cases p with
        | nil => rfl
        | cons b tl =>
          exfalso
          have hrev : (b :: tl) = (b :: tl).dropLast ++ [(b :: tl).getLast (by simp)] :=
            (List.dropLast_append_getLast (by simp)).symm
          rw [hrev] at hp
          have hJmem := hback _ _ hp
          rw [hJe] at hJmem; simp at hJmem
      · rintro rfl; exact hroot
    have hcost0 : cost = 0 := by
      rw [hcardX] at hcost
      have h0 : (∑ p ∈ leaf, (p.length : ℚ) * (Nat.card {x : Fin n → F2 // reaches p x} : ℚ)) = 0 := by
        rw [hleaf_eq]; simp
      rw [h0] at hcost
      nlinarith
    have hadv_le : adv ≤ rootBias := by
      rw [hleaf_eq, Finset.sum_singleton] at hadv_sum
      have hall : Finset.univ.filter (fun x : Fin n → F2 => reaches [] x) = Finset.univ := by
        ext x; simp [reaches]
      rw [hall] at hadv_sum
      have hS_out : (∑ x : Fin n → F2, sgn (f x + out [])) = sgn (out []) * ∑ x : Fin n → F2, sgn (f x) := by
        simp_rw [sgn_add, mul_comm (sgn (f _)), ← Finset.mul_sum]
      rw [hS_out] at hadv_sum
      by_cases hbal : bal
      · have hSf0 : (∑ x : Fin n → F2, sgn (f x)) = 0 := hSf_spec.1.mp hbal
        rw [hSf0, mul_zero, Int.cast_zero] at hadv_sum
        have hadv0 : adv = 0 := by nlinarith
        dsimp only [rootBias]; rw [if_pos hbal, hadv0]
      · have hSf_abs : (∑ x : Fin n → F2, sgn (f x)).natAbs = 2 ^ (n - m) := hSf_spec.2 hbal
        have hle_z : sgn (out []) * (∑ x : Fin n → F2, sgn (f x)) ≤ (2 : ℤ) ^ (n - m) := by
          have habs1 : |sgn (out []) * ∑ x : Fin n → F2, sgn (f x)| = (2 : ℤ) ^ (n - m) := by
            rw [abs_mul, sgn_abs, one_mul, ← Int.natCast_natAbs, hSf_abs]; push_cast; rfl
          linarith [le_abs_self (sgn (out []) * ∑ x : Fin n → F2, sgn (f x))]
        have hle_q : ((sgn (out []) * ∑ x : Fin n → F2, sgn (f x) : ℤ) : ℚ) ≤ (2 : ℚ) ^ (n - m) := by
          exact_mod_cast hle_z
        rw [← hadv_sum] at hle_q
        dsimp only [rootBias]; rw [if_neg hbal]
        have hpow : (2 : ℚ) ^ n = (2 : ℚ) ^ (n - m) * (2 : ℚ) ^ m := by
          rw [← pow_add, show (n - m) + m = n by omega]
        rw [hpow] at hle_q
        have h2m_pos : (0 : ℚ) < (2 : ℚ) ^ m := by positivity
        have h2nm_pos : (0 : ℚ) < (2 : ℚ) ^ (n - m) := by positivity
        rw [le_div_iff₀ h2m_pos]
        nlinarith
    exact ⟨hcost0, hadv_le⟩
  have hJ_nonempty : J ≠ ∅ → ((m : ℚ) + 1) * adv - rootBias ≤ cost ∧ (adv = rootBias → 0 < cost) := by
    intro hJne
    have hnil_J : [] ∈ J := by
      rcases Finset.nonempty_iff_ne_empty.mpr hJne with ⟨p0, hp0⟩
      cases p0 with
      | nil => exact hp0
      | cons b tl => exact tree_mem_J_of_prefix hback hJN [] (b :: tl) (by simp) (hJN hp0)
    have hlen_ge1 : ∀ p ∈ leaf, 1 ≤ p.length := by
      intro p hp
      have hne : p ≠ [] := fun h => (Finset.mem_sdiff.mp hp).2 (h ▸ hnil_J)
      cases p with
      | nil => exact absurd rfl hne
      | cons _ _ => simp
    have hcost_pos : 0 < cost := by
      rw [hcardX] at hcost
      have hsum_card : ∑ p ∈ leaf, (Nat.card {x : Fin n → F2 // reaches p x} : ℚ) = (2 : ℚ) ^ n := by
        have hnat : ∑ p ∈ leaf, (Finset.univ.filter (fun x : Fin n → F2 => reaches p x)).card = 2 ^ n := by
          have h1 : ∀ p ∈ leaf, (Finset.univ.filter (fun x : Fin n → F2 => reaches p x)).card =
              ∑ x : Fin n → F2, if p = (hpart x).choose then 1 else 0 := by
            intro p hp
            rw [← Finset.card_filter]
            congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hr; exact (hpart x).choose_spec.2 p ⟨hp, hr⟩
            · intro heq; rw [heq]; exact (hpart x).choose_spec.1.2
          rw [Finset.sum_congr rfl h1, Finset.sum_comm]
          have h2 : ∀ x : Fin n → F2, (∑ p ∈ leaf, if p = (hpart x).choose then 1 else 0) = 1 := by
            intro x; rw [Finset.sum_ite_eq', if_pos (hpart x).choose_spec.1.1]
          simp_rw [h2]; simp [Fintype.card_fun, Fintype.card_fin, ZMod.card]
        have hq : ∑ p ∈ leaf, ((Finset.univ.filter (fun x : Fin n → F2 => reaches p x)).card : ℚ) = (2 : ℚ) ^ n := by
          exact_mod_cast hnat
        rw [← hq]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      have hge : (2 : ℚ) ^ n ≤ ∑ p ∈ leaf, (p.length : ℚ) * (Nat.card {x : Fin n → F2 // reaches p x} : ℚ) := by
        rw [← hsum_card]
        refine Finset.sum_le_sum fun p hp => ?_
        have h1 : (1 : ℚ) ≤ (p.length : ℚ) := by exact_mod_cast hlen_ge1 p hp
        nlinarith [Nat.cast_nonneg (α := ℚ) (Nat.card {x : Fin n → F2 // reaches p x})]
      nlinarith
    have hmain_le : ((m : ℚ) + 1) * adv - rootBias ≤ cost := by
      let cellSum : List Bool → ℤ := fun p => ∑ x ∈ Finset.univ.filter (fun x => reaches p x), sgn (f x + out p)
      let cellBias : List Bool → ℤ := fun p => ∑ x ∈ Finset.univ.filter (fun x => reaches p x), sgn (f x)
      have hcell_abs : ∀ p : List Bool, (cellSum p).natAbs = (cellBias p).natAbs := by
        intro p
        have heq : cellSum p = sgn (out p) * cellBias p := by
          dsimp only [cellSum, cellBias]
          simp_rw [sgn_add, mul_comm (sgn (f _)), ← Finset.mul_sum]
        rw [heq, Int.natAbs_mul]
        have h1 : (sgn (out p)).natAbs = 1 := by rcases z2_cases (out p) with h | h <;> rw [h] <;> decide
        rw [h1, one_mul]
      let isFull : List Bool → Prop := fun p => p ∈ leaf ∧ (cellBias p).natAbs = 2 ^ (n - m)
      have hcell_props : ∀ p ∈ leaf,
          (cellBias p).natAbs ≤ 2 ^ (n - m) ∧
          (¬ isFull p → 2 * (cellBias p).natAbs ≤ 2 ^ (n - m)) ∧
          (((m : ℚ) + 1) * ((cellSum p : ℤ) : ℚ) - (p.length : ℚ) * (Nat.card {x : Fin n → F2 // reaches p x} : ℚ) ≤
            if isFull p then (2 : ℚ) ^ (n - m) else 0) := by
        intro p hp
        have hplen : 1 ≤ p.length := hlen_ge1 p hp
        by_cases hemp : ¬ ∃ a : Fin n → F2, reaches p a
        · push Not at hemp
          have hfilt0 : Finset.univ.filter (fun x : Fin n → F2 => reaches p x) = ∅ := by
            ext x; simp [hemp x]
          have hcb0 : cellBias p = 0 := by dsimp only [cellBias]; rw [hfilt0]; simp
          have hcs0 : cellSum p = 0 := by dsimp only [cellSum]; rw [hfilt0]; simp
          have hcard0 : Nat.card {x : Fin n → F2 // reaches p x} = 0 := by
            rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hfilt0]; simp
          have hnf : ¬ isFull p := fun h => by
            dsimp only [isFull] at h; rw [hcb0] at h
            have hpos : 0 < 2 ^ (n - m) := by positivity
            have := h.2; simp at this; omega
          refine ⟨by rw [hcb0]; simp, fun _ => by rw [hcb0]; simp, ?_⟩
          rw [if_neg hnf, hcs0, hcard0]; simp
        · push Not at hemp
          rcases hemp with ⟨ap, hap⟩
          have hcoset := tree_leaf_coset q offset p ap hap
          let Up : Submodule F2 (Fin n → F2) := ⨅ step : Fin p.length, LinearMap.ker (q (p.take step.val))
          have hcodim : n ≤ Module.finrank F2 Up + p.length := hcoset.1
          have hcard_eq : Nat.card {x : Fin n → F2 // reaches p x} = 2 ^ Module.finrank F2 Up := by
            rw [Nat.card_eq_fintype_card]
            let eU : Up ≃ {x : Fin n → F2 // reaches p x} :=
              { toFun := fun v => ⟨ap + v.val, (hcoset.2 (ap + v.val)).mpr (by simpa using v.property)⟩
                invFun := fun x => ⟨x.val - ap, (hcoset.2 x.val).mp x.property⟩
                left_inv := fun v => Subtype.ext (by show ap + v.val - ap = v.val; simp)
                right_inv := fun x => Subtype.ext (by show ap + (x.val - ap) = x.val; abel) }
            rw [← Fintype.card_congr eU, card_submodule_z2]
          have hbias_eq : cellBias p = ∑ v : Up, sgn (f (ap + v.val)) := by
            dsimp only [cellBias]
            let eU : Up ≃ {x : Fin n → F2 // reaches p x} :=
              { toFun := fun v => ⟨ap + v.val, (hcoset.2 (ap + v.val)).mpr (by simpa using v.property)⟩
                invFun := fun x => ⟨x.val - ap, (hcoset.2 x.val).mp x.property⟩
                left_inv := fun v => Subtype.ext (by show ap + v.val - ap = v.val; simp)
                right_inv := fun x => Subtype.ext (by show ap + (x.val - ap) = x.val; abel) }
            rw [Finset.sum_subtype (Finset.univ.filter (fun x => reaches p x)) (p := fun x => reaches p x) (fun x => by simp) (fun x => sgn (f x))]
            exact (Equiv.sum_comp eU (fun x : {x : Fin n → F2 // reaches p x} => sgn (f x.val))).symm
          have hbias_le_card : (cellBias p).natAbs ≤ 2 ^ Module.finrank F2 Up := by
            rw [hbias_eq]
            have htri := Finset.abs_sum_le_sum_abs (fun v : Up => sgn (f (ap + v.val))) Finset.univ
            simp_rw [sgn_abs] at htri
            have h1 : ((∑ v : Up, sgn (f (ap + v.val))).natAbs : ℤ) ≤ (Fintype.card Up : ℤ) := by
              simpa [Int.natCast_natAbs] using htri
            rw [card_submodule_z2] at h1
            exact_mod_cast h1
          rcases quad_coset_bias_structure f M hrk hf ap Up with ⟨hdim_le, hzero | ⟨habs_U, heven_U, _⟩⟩
          · have hcb0 : cellBias p = 0 := by rw [hbias_eq, hzero]
            have hcs0 : cellSum p = 0 := by
              have h := hcell_abs p; rw [hcb0] at h; exact Int.natAbs_eq_zero.mp h
            have hnf : ¬ isFull p := fun h => by
              dsimp only [isFull] at h; rw [hcb0] at h
              have hpos : 0 < 2 ^ (n - m) := by positivity
              have := h.2; simp at this; omega
            refine ⟨by rw [hcb0]; simp, fun _ => by rw [hcb0]; simp, ?_⟩
            rw [if_neg hnf, hcs0]
            simp only [Int.cast_zero, mul_zero, zero_sub, neg_nonpos]
            positivity
          · rw [← hbias_eq] at habs_U
            have hle_full : (cellBias p).natAbs ≤ 2 ^ (n - m) := by
              rw [habs_U]; exact Nat.pow_le_pow_right (by omega) (by omega)
            have hnot_full : ¬ isFull p → 2 * (cellBias p).natAbs ≤ 2 ^ (n - m) := by
              intro hnf
              have hlt : (cellBias p).natAbs < 2 ^ (n - m) := lt_of_le_of_ne hle_full (fun h => hnf ⟨hp, h⟩)
              rw [habs_U] at hlt ⊢
              have hlt_exp := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hlt
              rw [← pow_succ']
              exact Nat.pow_le_pow_right (by omega) (by omega)
            have hcs_le : ((cellSum p : ℤ) : ℚ) ≤ ((cellBias p).natAbs : ℚ) := by
              have h1 : (cellSum p : ℤ) ≤ ((cellSum p).natAbs : ℤ) := Int.le_natAbs
              rw [hcell_abs p] at h1
              have h2 := Int.cast_le (R := ℚ).mpr h1
              simpa only [Int.cast_natCast] using h2
            refine ⟨hle_full, hnot_full, ?_⟩
            by_cases hfull_p : isFull p
            · rw [if_pos hfull_p]
              have hfull_eq : (cellBias p).natAbs = 2 ^ (n - m) := hfull_p.2
              have hcs_le' : ((cellSum p : ℤ) : ℚ) ≤ (2 : ℚ) ^ (n - m) := by
                have h : ((cellBias p).natAbs : ℚ) = (2 : ℚ) ^ (n - m) := by exact_mod_cast hfull_eq
                linarith
              have hnat_ineq : m * 2 ^ (n - m) ≤ p.length * 2 ^ Module.finrank F2 Up := by
                by_cases hle_u : n - m ≤ Module.finrank F2 Up
                · have hd : n - Module.finrank F2 Up ≤ m := by omega
                  have h1 : m ≤ p.length * 2 ^ (Module.finrank F2 Up - (n - m)) := by
                    have hpow := nat_pow_ge_add_one (Module.finrank F2 Up - (n - m))
                    have hmul : p.length * (Module.finrank F2 Up - (n - m) + 1) ≤
                        p.length * 2 ^ (Module.finrank F2 Up - (n - m)) := Nat.mul_le_mul_left _ hpow
                    have hlin : m ≤ p.length * (Module.finrank F2 Up - (n - m) + 1) := by
                      have hm_le : m ≤ p.length + (Module.finrank F2 Up - (n - m)) := by omega
                      have hd_le : Module.finrank F2 Up - (n - m) ≤ p.length * (Module.finrank F2 Up - (n - m)) :=
                        Nat.le_mul_of_pos_left _ (by omega)
                      rw [Nat.mul_add, Nat.mul_one]; omega
                    omega
                  calc m * 2 ^ (n - m)
                      ≤ (p.length * 2 ^ (Module.finrank F2 Up - (n - m))) * 2 ^ (n - m) := Nat.mul_le_mul_right _ h1
                    _ = p.length * (2 ^ (Module.finrank F2 Up - (n - m)) * 2 ^ (n - m)) := by ring
                    _ = p.length * 2 ^ Module.finrank F2 Up := by
                        rw [← pow_add, show (Module.finrank F2 Up - (n - m)) + (n - m) = Module.finrank F2 Up by omega]
                · exfalso
                  have hlt : 2 ^ Module.finrank F2 Up < 2 ^ (n - m) := Nat.pow_lt_pow_right (by omega) (by omega)
                  omega
              have hq_ineq : (m : ℚ) * (2 : ℚ) ^ (n - m) ≤ (p.length : ℚ) * (Nat.card {x : Fin n → F2 // reaches p x} : ℚ) := by
                rw [hcard_eq]; exact_mod_cast hnat_ineq
              have hm1_nn : (0 : ℚ) ≤ (m : ℚ) + 1 := by positivity
              nlinarith
            · rw [if_neg hfull_p]
              have hnf := hnot_full hfull_p
              have hnat_ineq : (m + 1) * (cellBias p).natAbs ≤ p.length * 2 ^ Module.finrank F2 Up := by
                by_cases hpm : m + 1 ≤ p.length
                · exact Nat.mul_le_mul hpm hbias_le_card
                · have hdim_ge : n - m ≤ Module.finrank F2 Up := by omega
                  have hd_ge : 1 ≤ Module.finrank F2 Up - (n - m) + 1 := by omega
                  have h2 : (m + 1) ≤ p.length * 2 ^ (Module.finrank F2 Up - (n - m) + 1) := by
                    have hpow := nat_pow_ge_add_one (Module.finrank F2 Up - (n - m) + 1)
                    have hmul := Nat.mul_le_mul_left p.length hpow
                    have hlin : m + 1 ≤ p.length * (Module.finrank F2 Up - (n - m) + 1 + 1) := by
                      have hm_le : m + 1 ≤ p.length + (Module.finrank F2 Up - (n - m) + 1) := by omega
                      have hd_le : Module.finrank F2 Up - (n - m) + 1 ≤ p.length * (Module.finrank F2 Up - (n - m) + 1) :=
                        Nat.le_mul_of_pos_left _ (by omega)
                      rw [Nat.mul_add, Nat.mul_one]; omega
                    omega
                  have hmul2 : (m + 1) * (2 * (cellBias p).natAbs) ≤ (m + 1) * 2 ^ (n - m) :=
                    Nat.mul_le_mul_left _ hnf
                  have h3 : (m + 1) * 2 ^ (n - m) ≤ 2 * (p.length * 2 ^ Module.finrank F2 Up) := by
                    calc (m + 1) * 2 ^ (n - m)
                        ≤ (p.length * 2 ^ (Module.finrank F2 Up - (n - m) + 1)) * 2 ^ (n - m) :=
                          Nat.mul_le_mul_right _ h2
                      _ = p.length * (2 ^ (Module.finrank F2 Up - (n - m) + 1) * 2 ^ (n - m)) := by ring
                      _ = p.length * 2 ^ (Module.finrank F2 Up + 1) := by
                          rw [← pow_add, show (Module.finrank F2 Up - (n - m) + 1) + (n - m) = Module.finrank F2 Up + 1 by omega]
                      _ = 2 * (p.length * 2 ^ Module.finrank F2 Up) := by rw [pow_succ]; ring
                  have h4 : 2 * ((m + 1) * (cellBias p).natAbs) ≤ 2 * (p.length * 2 ^ Module.finrank F2 Up) := by
                    calc 2 * ((m + 1) * (cellBias p).natAbs)
                        = (m + 1) * (2 * (cellBias p).natAbs) := by ring
                      _ ≤ (m + 1) * 2 ^ (n - m) := hmul2
                      _ ≤ 2 * (p.length * 2 ^ Module.finrank F2 Up) := h3
                  omega
              have hq_ineq : ((m : ℚ) + 1) * ((cellBias p).natAbs : ℚ) ≤
                  (p.length : ℚ) * (Nat.card {x : Fin n → F2 // reaches p x} : ℚ) := by
                rw [hcard_eq]; exact_mod_cast hnat_ineq
              have hm1_nn : (0 : ℚ) ≤ (m : ℚ) + 1 := by positivity
              nlinarith
      have hfull_uniq : ∀ p1 ∈ leaf, ∀ p2 ∈ leaf, isFull p1 → isFull p2 → p1 = p2 := by
        intro p1 hp1 p2 hp2 hf1 hf2
        have hne1 : ∃ a1, reaches p1 a1 := by
          by_contra hno; push Not at hno
          have hf0 : Finset.univ.filter (fun x : Fin n → F2 => reaches p1 x) = ∅ := by ext x; simp [hno x]
          have h0 : cellBias p1 = 0 := by dsimp only [cellBias]; rw [hf0]; simp
          have hpos : 0 < 2 ^ (n - m) := by positivity
          have := hf1.2; rw [h0] at this; simp at this; omega
        have hne2 : ∃ a2, reaches p2 a2 := by
          by_contra hno; push Not at hno
          have hf0 : Finset.univ.filter (fun x : Fin n → F2 => reaches p2 x) = ∅ := by ext x; simp [hno x]
          have h0 : cellBias p2 = 0 := by dsimp only [cellBias]; rw [hf0]; simp
          have hpos : 0 < 2 ^ (n - m) := by positivity
          have := hf2.2; rw [h0] at this; simp at this; omega
        rcases hne1 with ⟨a1, ha1⟩
        rcases hne2 with ⟨a2, ha2⟩
        have hc1 := tree_leaf_coset q offset p1 a1 ha1
        have hc2 := tree_leaf_coset q offset p2 a2 ha2
        let U1 : Submodule F2 (Fin n → F2) := ⨅ step : Fin p1.length, LinearMap.ker (q (p1.take step.val))
        let U2 : Submodule F2 (Fin n → F2) := ⨅ step : Fin p2.length, LinearMap.ker (q (p2.take step.val))
        have hb1 : cellBias p1 = ∑ v : U1, sgn (f (a1 + v.val)) := by
          dsimp only [cellBias]
          let eU : U1 ≃ {x : Fin n → F2 // reaches p1 x} :=
            { toFun := fun v => ⟨a1 + v.val, (hc1.2 (a1 + v.val)).mpr (by simpa using v.property)⟩
              invFun := fun x => ⟨x.val - a1, (hc1.2 x.val).mp x.property⟩
              left_inv := fun v => Subtype.ext (by show a1 + v.val - a1 = v.val; simp)
              right_inv := fun x => Subtype.ext (by show a1 + (x.val - a1) = x.val; abel) }
          rw [Finset.sum_subtype (Finset.univ.filter (fun x => reaches p1 x)) (p := fun x => reaches p1 x) (fun x => by simp) (fun x => sgn (f x))]
          exact (Equiv.sum_comp eU (fun x : {x : Fin n → F2 // reaches p1 x} => sgn (f x.val))).symm
        have hb2 : cellBias p2 = ∑ v : U2, sgn (f (a2 + v.val)) := by
          dsimp only [cellBias]
          let eU : U2 ≃ {x : Fin n → F2 // reaches p2 x} :=
            { toFun := fun v => ⟨a2 + v.val, (hc2.2 (a2 + v.val)).mpr (by simpa using v.property)⟩
              invFun := fun x => ⟨x.val - a2, (hc2.2 x.val).mp x.property⟩
              left_inv := fun v => Subtype.ext (by show a2 + v.val - a2 = v.val; simp)
              right_inv := fun x => Subtype.ext (by show a2 + (x.val - a2) = x.val; abel) }
          rw [Finset.sum_subtype (Finset.univ.filter (fun x => reaches p2 x)) (p := fun x => reaches p2 x) (fun x => by simp) (fun x => sgn (f x))]
          exact (Equiv.sum_comp eU (fun x : {x : Fin n → F2 // reaches p2 x} => sgn (f x.val))).symm
        obtain ⟨x, hx1, hx2⟩ := full_bias_cells_intersect f M hrk hf a1 a2 U1 U2 (hb1 ▸ hf1.2) (hb2 ▸ hf2.2)
        have hr1 : reaches p1 x := (hc1.2 x).mpr hx1
        have hr2 : reaches p2 x := (hc2.2 x).mpr hx2
        have h1u := (hpart x).choose_spec.2 p1 ⟨hp1, hr1⟩
        have h2u := (hpart x).choose_spec.2 p2 ⟨hp2, hr2⟩
        exact h1u.trans h2u.symm
      have hfull_nbal : ∀ p ∈ leaf, isFull p → ¬ bal := by
        intro p hp hfp hbal
        have hne1 : ∃ a1, reaches p a1 := by
          by_contra hno; push Not at hno
          have hf0 : Finset.univ.filter (fun x : Fin n → F2 => reaches p x) = ∅ := by ext x; simp [hno x]
          have h0 : cellBias p = 0 := by dsimp only [cellBias]; rw [hf0]; simp
          have hpos : 0 < 2 ^ (n - m) := by positivity
          have := hfp.2; rw [h0] at this; simp at this; omega
        rcases hne1 with ⟨a1, ha1⟩
        have hc1 := tree_leaf_coset q offset p a1 ha1
        let U1 : Submodule F2 (Fin n → F2) := ⨅ step : Fin p.length, LinearMap.ker (q (p.take step.val))
        have hb1 : cellBias p = ∑ v : U1, sgn (f (a1 + v.val)) := by
          dsimp only [cellBias]
          let eU : U1 ≃ {x : Fin n → F2 // reaches p x} :=
            { toFun := fun v => ⟨a1 + v.val, (hc1.2 (a1 + v.val)).mpr (by simpa using v.property)⟩
              invFun := fun x => ⟨x.val - a1, (hc1.2 x.val).mp x.property⟩
              left_inv := fun v => Subtype.ext (by show a1 + v.val - a1 = v.val; simp)
              right_inv := fun x => Subtype.ext (by show a1 + (x.val - a1) = x.val; abel) }
          rw [Finset.sum_subtype (Finset.univ.filter (fun x => reaches p x)) (p := fun x => reaches p x) (fun x => by simp) (fun x => sgn (f x))]
          exact (Equiv.sum_comp eU (fun x : {x : Fin n → F2 // reaches p x} => sgn (f x.val))).symm
        have hSf_eq := (full_bias_cell_props f M hrk hf a1 U1 (hb1 ▸ hfp.2)).2.2.2.2
        have hSf0 : (∑ x : Fin n → F2, sgn (f x)) = 0 := hSf_spec.1.mp hbal
        rw [hSf0, ← hb1] at hSf_eq
        have hpos : 0 < 2 ^ (n - m) := by positivity
        have := hfp.2; rw [← hSf_eq] at this; simp at this; omega
      have hsum_full : (∑ p ∈ leaf, if isFull p then (2 : ℚ) ^ (n - m) else 0) ≤ rootBias * (2 : ℚ) ^ n := by
        by_cases hex : ∃ p ∈ leaf, isFull p
        · rcases hex with ⟨p0, hp0, hfp0⟩
          have hnb : ¬ bal := hfull_nbal p0 hp0 hfp0
          have heq : (∑ p ∈ leaf, if isFull p then (2 : ℚ) ^ (n - m) else 0) = (2 : ℚ) ^ (n - m) := by
            rw [Finset.sum_eq_single p0]
            · rw [if_pos hfp0]
            · intro p hp hne; rw [if_neg (fun hf => hne (hfull_uniq p hp p0 hp0 hf hfp0))]
            · intro h; exact absurd hp0 h
          rw [heq]
          dsimp only [rootBias]; rw [if_neg hnb]
          have hpow : (2 : ℚ) ^ n = (2 : ℚ) ^ (n - m) * (2 : ℚ) ^ m := by
            rw [← pow_add, show (n - m) + m = n by omega]
          rw [hpow]; field_simp; rfl
        · push Not at hex
          have h0 : (∑ p ∈ leaf, if isFull p then (2 : ℚ) ^ (n - m) else 0) = 0 :=
            Finset.sum_eq_zero fun p hp => if_neg (hex p hp)
          rw [h0]
          have hrb : 0 ≤ rootBias := by dsimp only [rootBias]; split_ifs <;> positivity
          positivity
      have htot_sum : ((m : ℚ) + 1) * (adv * (2 : ℚ) ^ n) - cost * (2 : ℚ) ^ n ≤ rootBias * (2 : ℚ) ^ n := by
        rw [hadv_sum, ← hcardX, hcost, Finset.mul_sum, ← Finset.sum_sub_distrib, hcardX]
        exact le_trans (Finset.sum_le_sum fun p hp => (hcell_props p hp).2.2) hsum_full
      nlinarith
    exact ⟨hmain_le, fun _ => hcost_pos⟩
  have hrb_nonneg : 0 ≤ rootBias := by dsimp only [rootBias]; split_ifs <;> positivity
  have hrb_le1 : rootBias ≤ 1 := by
    dsimp only [rootBias]; split_ifs
    · norm_num
    · rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hexact_nonneg : 0 ≤ exactCost := by dsimp only [exactCost]; linarith
  have hkey : (1 - rootBias) * cost ≥ exactCost * (adv - rootBias) := by
    by_cases hJe : J = ∅
    · rcases hJ_empty hJe with ⟨hc0, hav⟩
      rw [hc0, mul_zero]
      nlinarith
    · rcases hJ_nonempty hJe with ⟨hle, _⟩
      have hid : (1 - rootBias) * (((m : ℚ) + 1) * adv - rootBias) - exactCost * (adv - rootBias) =
          (m : ℚ) * rootBias * (1 - adv) := by dsimp only [exactCost]; ring
      have h1 : (1 - rootBias) * (((m : ℚ) + 1) * adv - rootBias) ≤ (1 - rootBias) * cost :=
        mul_le_mul_of_nonneg_left hle (by linarith)
      have h2 : 0 ≤ (m : ℚ) * rootBias * (1 - adv) :=
        mul_nonneg (mul_nonneg (by positivity) hrb_nonneg) (by linarith)
      linarith
  have huniq : (¬ bal) → 0 < m → (1 - rootBias) * cost = exactCost * (adv - rootBias) →
      (cost = 0 ∧ adv = rootBias) ∨ (cost = exactCost ∧ adv = 1) := by
    intro hnb hmpos heq
    have hrb_pos : 0 < rootBias := by dsimp only [rootBias]; rw [if_neg hnb]; positivity
    have hrb_lt1 : rootBias < 1 := by
      dsimp only [rootBias]; rw [if_neg hnb]
      rw [div_lt_one (by positivity)]
      have h2 : (2 : ℚ) ^ 1 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have hexact_pos : 0 < exactCost := by
      dsimp only [exactCost]
      have hm1 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hmpos
      linarith
    by_cases hJe : J = ∅
    · rcases hJ_empty hJe with ⟨hc0, hav⟩
      rw [hc0, mul_zero] at heq
      have hav_eq : adv = rootBias := by nlinarith
      exact Or.inl ⟨hc0, hav_eq⟩
    · rcases hJ_nonempty hJe with ⟨hle, _⟩
      have hid : (1 - rootBias) * (((m : ℚ) + 1) * adv - rootBias) - exactCost * (adv - rootBias) =
          (m : ℚ) * rootBias * (1 - adv) := by dsimp only [exactCost]; ring
      have h1 : (1 - rootBias) * (((m : ℚ) + 1) * adv - rootBias) ≤ (1 - rootBias) * cost :=
        mul_le_mul_of_nonneg_left hle (by linarith)
      have hm_pos_q : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hmpos
      have hprod_le : (m : ℚ) * rootBias * (1 - adv) ≤ 0 := by linarith
      have hadv1 : adv = 1 := by
        have hmrb_pos : 0 < (m : ℚ) * rootBias := mul_pos hm_pos_q hrb_pos
        nlinarith
      rw [hadv1] at heq
      have hcost_eq : cost = exactCost := by nlinarith
      exact Or.inr ⟨hcost_eq, hadv1⟩
  exact ⟨hcost_nonneg, hadv_le1, hJ_empty, hJ_nonempty, hkey, huniq⟩

lemma exists_trivial_tree {n m : ℕ} (f : (Fin n → F2) → F2) (M : Matrix (Fin n) (Fin n) F2)
    (hrk : M.rank = 2 * m)
    (hf : ∀ x y, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y)) :
    let bal := Nat.card {x : Fin n → F2 // f x = 0} = Nat.card {x : Fin n → F2 // f x = 1}
    let rootBias : ℚ := if bal then 0 else 1 / (2 : ℚ) ^ m
    ∃ (N J : Finset (List Bool)) (q : List Bool → (Fin n → F2) →ₗ[F2] F2) (offset out : List Bool → F2),
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (v : Bool), p ++ [v] ∈ N → p ∈ J) ∧
      (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
      (0 : ℚ) * (Nat.card (Fin n → F2) : ℚ) = ∑ p ∈ N \ J, (p.length : ℚ) *
        (Nat.card {x : Fin n → F2 // ∀ step : Fin p.length,
          decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step} : ℚ) ∧
      (rootBias + 1) * (Nat.card (Fin n → F2) : ℚ) = 2 *
        (Nat.card {x : Fin n → F2 // ∃ p ∈ N \ J, (∀ step : Fin p.length,
          decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step) ∧ f x = out p} : ℚ) := by
  intro bal rootBias
  have h2m_le_n : 2 * m ≤ n := by have := rank_add_ker_mat M; omega
  let Sf : ℤ := ∑ x : Fin n → F2, sgn (f x)
  have hSf_diff : Sf = (Nat.card {x : Fin n → F2 // f x = 0} : ℤ) -
      (Nat.card {x : Fin n → F2 // f x = 1} : ℤ) := by
    dsimp only [Sf]
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype]
    have h1 : ∀ x : Fin n → F2, sgn (f x) = (if f x = 0 then (1 : ℤ) else 0) - (if f x = 1 then (1 : ℤ) else 0) := by
      intro x; rcases z2_cases (f x) with h | h <;> rw [h] <;> decide
    simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_boole]
  have hsum_cards : Nat.card {x : Fin n → F2 // f x = 0} + Nat.card {x : Fin n → F2 // f x = 1} = 2 ^ n := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype]
    have h1 : Finset.univ.filter (fun x : Fin n → F2 => f x = 1) =
        Finset.univ.filter (fun x : Fin n → F2 => ¬ f x = 0) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases z2_cases (f x) with h | h <;> rw [h] <;> decide
    have hunion : Finset.univ.filter (fun x : Fin n → F2 => f x = 0) ∪
        Finset.univ.filter (fun x : Fin n → F2 => ¬ f x = 0) = Finset.univ := by
      ext x; simp; exact Classical.em _
    rw [h1, ← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h0 h1 => h1 h0), hunion]
    simp [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have hSf_spec : (bal ↔ Sf = 0) ∧ (¬ bal → Sf.natAbs = 2 ^ (n - m)) := by
    have hbal_iff : bal ↔ Sf = 0 := by dsimp only [bal]; rw [hSf_diff]; omega
    refine ⟨hbal_iff, fun hnbal => ?_⟩
    have hne : Sf ≠ 0 := fun h => hnbal (hbal_iff.mpr h)
    have htop := quad_coset_bias_structure f M hrk hf 0 (⊤ : Submodule F2 (Fin n → F2))
    have hKtop : ((⊤ : Submodule F2 (Fin n → F2)) ⊓
      ({ carrier := {w | ∀ v ∈ (⊤ : Submodule F2 (Fin n → F2)), dotProduct v (M.mulVec w) = 0}
         zero_mem' := fun v _ => by simp
         smul_mem' := fun c {w} hw v hv => (by rw [Matrix.mulVec_smul, dotProduct_smul, hw v hv, smul_zero]), add_mem' := fun {w1 w2} h1 h2 v hv => (by rw [Matrix.mulVec_add, dotProduct_add, h1 v hv, h2 v hv, add_zero]) } : Submodule F2 (Fin n → F2))) =
        LinearMap.ker M.mulVecLin := by
      ext w
      simp only [Submodule.mem_inf, Submodule.mem_top, true_and, LinearMap.mem_ker]
      constructor
      · intro hw; funext i
        have := hw (Pi.single i 1) trivial
        simpa [single_dotProduct] using this
      · intro hw v _; change M.mulVec w = 0 at hw; rw [hw, dotProduct_zero]
    have hSf_top : (∑ v : (⊤ : Submodule F2 (Fin n → F2)), sgn (f (0 + v.val))) = Sf := by
      let eT : (⊤ : Submodule F2 (Fin n → F2)) ≃ (Fin n → F2) :=
        { toFun := fun v => v.val, invFun := fun x => ⟨x, trivial⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
      simp_rw [zero_add]
      exact Equiv.sum_comp eT (fun x => sgn (f x))
    rw [hSf_top] at htop
    rcases htop.2 with h0 | ⟨habs, _, _⟩
    · exact absurd h0 hne
    · rw [hKtop, finrank_top, Module.finrank_fin_fun] at habs
      have hMrk := rank_add_ker_mat M
      have hdiv : (n + Module.finrank F2 (LinearMap.ker M.mulVecLin)) / 2 = n - m := by omega
      rwa [hdiv] at habs
  let out0 : F2 := if 0 ≤ Sf then 0 else 1
  refine ⟨{[]}, ∅, fun _ => 0, fun _ => 0, fun _ => out0, by simp, by simp, ?_, by simp, ?_, ?_⟩
  · intro p v h; simp at h
  · simp
  · have hcardX : (Nat.card (Fin n → F2) : ℚ) = (2 : ℚ) ^ n := by
      rw [Nat.card_eq_fintype_card]; simp [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    have heq_set : Nat.card {x : Fin n → F2 // ∃ p ∈ ({[]} : Finset (List Bool)) \ ∅,
        (∀ step : Fin p.length, decide ((0 : (Fin n → F2) →ₗ[F2] F2) x = 0) = p.get step) ∧ f x = out0} =
        Nat.card {x : Fin n → F2 // f x = out0} := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype]
      congr 1; ext x; simp
    rw [heq_set, hcardX]
    have h2out : 2 * (Nat.card {x : Fin n → F2 // f x = out0} : ℤ) = (2 : ℤ) ^ n + (Sf.natAbs : ℤ) := by
      have hsum_z : (Nat.card {x : Fin n → F2 // f x = 0} : ℤ) + (Nat.card {x : Fin n → F2 // f x = 1} : ℤ) = (2 : ℤ) ^ n := by
        exact_mod_cast hsum_cards
      dsimp only [out0]
      by_cases hpos : 0 ≤ Sf
      · rw [if_pos hpos]
        have habs : (Sf.natAbs : ℤ) = Sf := by rw [Int.natCast_natAbs, abs_of_nonneg hpos]
        omega
      · rw [if_neg hpos]
        have habs : (Sf.natAbs : ℤ) = -Sf := by rw [Int.natCast_natAbs, abs_of_neg (by omega)]
        omega
    have h2out_q : 2 * (Nat.card {x : Fin n → F2 // f x = out0} : ℚ) = (2 : ℚ) ^ n + (Sf.natAbs : ℚ) := by
      exact_mod_cast h2out
    rw [h2out_q]
    by_cases hbal : bal
    · have h0 : Sf.natAbs = 0 := Int.natAbs_eq_zero.mpr (hSf_spec.1.mp hbal)
      dsimp only [rootBias]; rw [if_pos hbal, h0]; simp
    · have ha : Sf.natAbs = 2 ^ (n - m) := hSf_spec.2 hbal
      dsimp only [rootBias]; rw [if_neg hbal, ha]
      have hpow : (2 : ℚ) ^ n = (2 : ℚ) ^ (n - m) * (2 : ℚ) ^ m := by
        rw [← pow_add, show (n - m) + m = n by omega]
      push_cast; rw [hpow]; field_simp; ring

lemma exists_peel_tree {n m : ℕ} (f : (Fin n → F2) → F2) (M : Matrix (Fin n) (Fin n) F2)
    (hrk : M.rank = 2 * m)
    (hf : ∀ x y, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y)) :
    let bal := Nat.card {x : Fin n → F2 // f x = 0} = Nat.card {x : Fin n → F2 // f x = 1}
    let rootBias : ℚ := if bal then 0 else 1 / (2 : ℚ) ^ m
    let exactCost : ℚ := (m : ℚ) + 1 - rootBias
    ∃ (N J : Finset (List Bool)) (q : List Bool → (Fin n → F2) →ₗ[F2] F2) (offset out : List Bool → F2),
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (v : Bool), p ++ [v] ∈ N → p ∈ J) ∧
      (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
      exactCost * (Nat.card (Fin n → F2) : ℚ) = ∑ p ∈ N \ J, (p.length : ℚ) *
        (Nat.card {x : Fin n → F2 // ∀ step : Fin p.length,
          decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step} : ℚ) ∧
      ((1 : ℚ) + 1) * (Nat.card (Fin n → F2) : ℚ) = 2 *
        (Nat.card {x : Fin n → F2 // ∃ p ∈ N \ J, (∀ step : Fin p.length,
          decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step) ∧ f x = out p} : ℚ) := by
  intro bal rootBias exactCost
  have h2m_le_n : 2 * m ≤ n := by have := rank_add_ker_mat M; omega
  have hcardX : (Nat.card (Fin n → F2) : ℚ) = (2 : ℚ) ^ n := by
    rw [Nat.card_eq_fintype_card]; simp [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  obtain ⟨m', c1, c2, v, a, b, hrk_eq, hform, hdiag, htri⟩ := symplectic_normal_form M.rank f M rfl hf
  rcases (by omega : m = m') with rfl
  let Φ : (Fin n → F2) →ₗ[F2] (Fin m → F2) :=
    { toFun := fun x i => dotProduct (c1 i) x
      map_add' := fun x y => by funext i; exact dotProduct_add (c1 i) x y
      map_smul' := fun c x => by funext i; simp [dotProduct_smul] }
  have hΦ_surj : Function.Surjective Φ := by
    intro y
    have hbuild : ∀ (k : ℕ) (hk : k ≤ m), ∃ x : Fin n → F2, ∀ i : Fin m, m - k ≤ i.val → dotProduct (c1 i) x = y i := by
      intro k
      induction k with
      | zero => intro _ ; exact ⟨0, fun i hi => by omega⟩
      | succ k ih =>
        intro hk
        obtain ⟨x0, hx0⟩ := ih (by omega)
        let idx : Fin m := ⟨m - (k + 1), by omega⟩
        let δ : F2 := y idx + dotProduct (c1 idx) x0
        refine ⟨x0 + δ • v idx, fun i hi => ?_⟩
        rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
        by_cases hgt : m - k ≤ i.val
        · have hij : idx < i := by show m - (k + 1) < i.val; omega
          have h0 : dotProduct (c1 i) (v idx) = 0 := htri i idx hij
          rw [hx0 i hgt, h0, mul_zero, add_zero]
        · have heq : i = idx := Fin.ext (by dsimp only [idx]; omega)
          subst heq
          rw [hdiag idx, mul_one]
          dsimp only [δ]
          have hz := z2_add_self (dotProduct (c1 idx) x0)
          linear_combination hz
    obtain ⟨x, hx⟩ := hbuild m (le_refl m)
    exact ⟨x, funext fun i => hx i (by omega)⟩
  have hΦ_fiber_card : ∀ y : Fin m → F2, (Finset.univ.filter (fun x : Fin n → F2 => Φ x = y)).card = 2 ^ (n - m) := by
    intro y
    obtain ⟨x0, hx0⟩ := hΦ_surj y
    let eK : LinearMap.ker Φ ≃ {x : Fin n → F2 // Φ x = y} :=
      { toFun := fun u => ⟨x0 + u.val, by rw [map_add, hx0, LinearMap.mem_ker.mp u.property, add_zero]⟩
        invFun := fun x => ⟨x.val - x0, by show Φ (x.val - x0) = 0; rw [map_sub, x.property, hx0, sub_self]⟩
        left_inv := fun u => Subtype.ext (by show x0 + u.val - x0 = u.val; simp)
        right_inv := fun x => Subtype.ext (by show x0 + (x.val - x0) = x.val; abel) }
    have hrkΦ := LinearMap.finrank_range_add_finrank_ker Φ
    rw [LinearMap.range_eq_top.mpr hΦ_surj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hrkΦ
    rw [← Fintype.card_subtype, ← Fintype.card_congr eK, card_submodule_z2]
    congr 1; omega
  let toVec : List Bool → (Fin m → F2) := fun p i => if p.getD i.val false then 1 else 0
  let ofVec : (Fin m → F2) → List Bool := fun y => List.ofFn fun i : Fin m => decide (y i = 1)
  have hofVec_len : ∀ y, (ofVec y).length = m := fun y => by simp [ofVec]
  have htoVec_ofVec : ∀ y, toVec (ofVec y) = y := fun y => by
    funext i
    simp only [toVec, ofVec, List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some]
    rcases z2_cases (y i) with h | h <;> rw [h] <;> decide
  have hofVec_toVec : ∀ p : List Bool, p.length = m → ofVec (toVec p) = p := fun p hp => by
    apply List.ext_getElem (by simp [ofVec, hp])
    intro i hi1 hi2
    simp only [ofVec, toVec, List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2, Option.getD_some]
    cases p[i] <;> decide
  let linOf : List Bool → (Fin n → F2) := fun p => a + ∑ i : Fin m, (if p.getD i.val false then (1 : F2) else 0) • c2 i
  have hf_on_vec : ∀ (p : List Bool) (x : Fin n → F2), Φ x = toVec p →
      f x = dotProduct (linOf p) x + b := by
    intro p x hΦx
    rw [hform x]
    have hdot : dotProduct (linOf p) x = dotProduct a x + ∑ i : Fin m, (if p.getD i.val false then (1 : F2) else 0) * dotProduct (c2 i) x := by
      simp only [linOf, add_dotProduct, sum_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [hdot]
    have hsum : (∑ i : Fin m, dotProduct (c1 i) x * dotProduct (c2 i) x) =
        ∑ i : Fin m, (if p.getD i.val false then (1 : F2) else 0) * dotProduct (c2 i) x := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : dotProduct (c1 i) x = toVec p i := congrFun hΦx i
      rw [hi]
    rw [hsum]; ring
  let allDepth : ℕ → Finset (List Bool) := fun k =>
    (Finset.univ : Finset (Fin k → Bool)).image (fun g => List.ofFn g)
  have hmem_allDepth : ∀ (k : ℕ) (p : List Bool), p ∈ allDepth k ↔ p.length = k := by
    intro k p
    simp only [allDepth, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨g, rfl⟩; simp
    · intro hp; refine ⟨fun i => p.get ⟨i.val, by omega⟩, ?_⟩
      apply List.ext_getElem (by simp [hp])
      intro i hi1 hi2; simp [List.get_eq_getElem]
  let prefNodes : Finset (List Bool) := (Finset.range m).biUnion allDepth
  have hmem_pref : ∀ p : List Bool, p ∈ prefNodes ↔ p.length < m := by
    intro p; simp only [prefNodes, Finset.mem_biUnion, Finset.mem_range, hmem_allDepth]
    exact ⟨fun ⟨k, hk, hlen⟩ => hlen ▸ hk, fun h => ⟨p.length, h, rfl⟩⟩
  by_cases hbal : bal
  · let J : Finset (List Bool) := prefNodes ∪ allDepth m
    let N : Finset (List Bool) := J ∪ allDepth (m + 1)
    let q : List Bool → (Fin n → F2) →ₗ[F2] F2 := fun p =>
      if h : p.length < m then dotLin (c1 ⟨p.length, h⟩) else dotLin (linOf p)
    let offset : List Bool → F2 := fun _ => 1
    let out : List Bool → F2 := fun p => b + (if p.getD m false then 1 else 0)
    have hmemJ : ∀ p, p ∈ J ↔ p.length ≤ m := fun p => by
      simp only [J, Finset.mem_union, hmem_pref, hmem_allDepth]; omega
    have hmemN : ∀ p, p ∈ N ↔ p.length ≤ m + 1 := fun p => by
      simp only [N, Finset.mem_union, hmemJ, hmem_allDepth]; omega
    have hleaf_iff : ∀ p, p ∈ N \ J ↔ p.length = m + 1 := fun p => by
      simp only [Finset.mem_sdiff, hmemN, hmemJ]; omega
    have hreaches_m1 : ∀ (p : List Bool) (hp : p.length = m + 1) (x : Fin n → F2),
        (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step) ↔
        (Φ x = toVec p ∧ decide (dotProduct (linOf (p.take m)) x = 1) = p.get ⟨m, by omega⟩) := by
      intro p hp x
      constructor
      · intro hr
        refine ⟨funext fun i => ?_, ?_⟩
        · have hs := hr ⟨i.val, by omega⟩
          have hlt : (p.take i.val).length < m := by rw [List.length_take]; omega
          simp only [q, hlt, ↓reduceDIte, offset] at hs
          have htake_len : (p.take i.val).length = i.val := by rw [List.length_take]; omega
          have hci : c1 ⟨(p.take i.val).length, hlt⟩ = c1 i := congrArg c1 (Fin.ext htake_len)
          change decide (dotProduct (c1 ⟨(p.take i.val).length, hlt⟩) x = 1) = p.get ⟨i.val, by omega⟩ at hs
          rw [hci, List.get_eq_getElem] at hs
          dsimp only [toVec]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i.val < p.length), Option.getD_some, ← hs]
          change dotProduct (c1 i) x = _
          rcases z2_cases (dotProduct (c1 i) x) with h | h <;> rw [h] <;> decide
        · have hs := hr ⟨m, by omega⟩
          have hnot : ¬ (p.take m).length < m := by simp; omega
          simp only [q, hnot, ↓reduceDIte, offset] at hs
          exact hs
      · rintro ⟨hΦx, hm_eq⟩ step
        by_cases hlt : step.val < m
        · have hlt' : (p.take step.val).length < m := by simp; omega
          simp only [q, hlt', ↓reduceDIte, offset]
          have htake_len : (p.take step.val).length = step.val := by rw [List.length_take]; omega
          have hci : c1 ⟨(p.take step.val).length, hlt'⟩ = c1 ⟨step.val, hlt⟩ := congrArg c1 (Fin.ext htake_len)
          change decide (dotProduct (c1 ⟨(p.take step.val).length, hlt'⟩) x = 1) = p.get step
          rw [hci]
          have hi : dotProduct (c1 ⟨step.val, hlt⟩) x = toVec p ⟨step.val, hlt⟩ := congrFun hΦx ⟨step.val, hlt⟩
          rw [hi]
          simp only [toVec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem step.isLt, Option.getD_some, List.get_eq_getElem]
          cases p[step.val] <;> decide
        · have hlt_m : m < p.length := by omega
          have hstep_lt := step.isLt
          have heq_m : step.val = m := by omega
          have hstep : step = ⟨m, hlt_m⟩ := Fin.ext heq_m
          subst hstep
          have hnot : ¬ (p.take m).length < m := by simp; omega
          simp only [q, hnot, ↓reduceDIte, offset]
          exact hm_eq
    have hroot : [] ∈ N := (hmemN []).mpr (by simp)
    have hJN : J ⊆ N := Finset.subset_union_left
    have hback : ∀ (p : List Bool) (v : Bool), p ++ [v] ∈ N → p ∈ J := fun p v h => by
      rw [hmemN, List.length_append, List.length_singleton] at h; rw [hmemJ]; omega
    have hfwd : ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N := fun p hp => by
      rw [hmemJ] at hp; rw [hmemN, hmemN]; simp; omega
    have hpart := tree_leaf_partition N J q offset hroot hJN hback hfwd
    refine ⟨N, J, q, offset, out, hroot, hJN, hback, hfwd, ?_, ?_⟩
    · have hexact : exactCost = (m : ℚ) + 1 := by dsimp only [exactCost, rootBias]; rw [if_pos hbal]; ring
      rw [hexact, hcardX]
      have hlen_eq : ∀ p ∈ N \ J, (p.length : ℚ) = (m : ℚ) + 1 := fun p hp => by
        have := (hleaf_iff p).mp hp; exact_mod_cast this
      have hsum_cards : ∑ p ∈ N \ J, (Nat.card {x : Fin n → F2 // ∀ step : Fin p.length,
            decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step} : ℚ) = (2 : ℚ) ^ n := by
        have hnat : ∑ p ∈ N \ J, (Finset.univ.filter (fun x : Fin n → F2 => ∀ step : Fin p.length,
            decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step)).card = 2 ^ n := by
          have h1 : ∀ p ∈ N \ J, (Finset.univ.filter (fun x : Fin n → F2 => ∀ step : Fin p.length,
              decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step)).card =
              ∑ x : Fin n → F2, if p = (hpart x).choose then 1 else 0 := by
            intro p hp
            rw [← Finset.card_filter]
            congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hr; exact (hpart x).choose_spec.2 p ⟨hp, hr⟩
            · intro heq; rw [heq]; exact (hpart x).choose_spec.1.2
          rw [Finset.sum_congr rfl h1, Finset.sum_comm]
          have h2 : ∀ x : Fin n → F2, (∑ p ∈ N \ J, if p = (hpart x).choose then 1 else 0) = 1 := by
            intro x; rw [Finset.sum_ite_eq', if_pos (hpart x).choose_spec.1.1]
          simp_rw [h2]; simp [Fintype.card_fun, Fintype.card_fin, ZMod.card]
        have hq : ∑ p ∈ N \ J, ((Finset.univ.filter (fun x : Fin n → F2 => ∀ step : Fin p.length,
            decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step)).card : ℚ) = (2 : ℚ) ^ n := by
          exact_mod_cast hnat
        rw [← hq]; refine Finset.sum_congr rfl fun p _ => ?_
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      rw [← hsum_cards, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p hp => by rw [hlen_eq p hp]
    · have hall_exact : ∀ x : Fin n → F2, ∃ p ∈ N \ J,
          (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step) ∧ f x = out p := by
        intro x
        let p0 := (hpart x).choose
        have hp0 : p0 ∈ N \ J := (hpart x).choose_spec.1.1
        have hr0 : ∀ step : Fin p0.length, decide (q (p0.take step.val) x = offset (p0.take step.val)) = p0.get step :=
          (hpart x).choose_spec.1.2
        have hlen : p0.length = m + 1 := (hleaf_iff p0).mp hp0
        rcases (hreaches_m1 p0 hlen x).mp hr0 with ⟨hΦx, hm_eq⟩
        refine ⟨p0, hp0, hr0, ?_⟩
        have hto_take : toVec (p0.take m) = toVec p0 := by
          funext i
          simp only [toVec, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt i.isLt]
        have hfx := hf_on_vec (p0.take m) x (by rw [hΦx, hto_take])
        rw [hfx]
        dsimp only [out]
        rw [List.get_eq_getElem] at hm_eq
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : m < p0.length), Option.getD_some, ← hm_eq]
        rcases z2_cases (dotProduct (linOf (p0.take m)) x) with h | h <;> rw [h] <;> simp [add_comm]
      have hcard_all : Nat.card {x : Fin n → F2 // ∃ p ∈ N \ J,
          (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step) ∧ f x = out p} =
          Nat.card (Fin n → F2) := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
        have hf_univ : Finset.univ.filter (fun x : Fin n → F2 => ∃ p ∈ N \ J,
            (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step) ∧ f x = out p) =
            Finset.univ := by ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; exact hall_exact x
        rw [hf_univ, Finset.card_univ]
      rw [hcard_all]; ring
  · have hSf_ne : (∑ x : Fin n → F2, sgn (f x)) ≠ 0 := by
      intro h0
      apply hbal
      have hdiff : (∑ x : Fin n → F2, sgn (f x)) = (Nat.card {x : Fin n → F2 // f x = 0} : ℤ) -
          (Nat.card {x : Fin n → F2 // f x = 1} : ℤ) := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype]
        have h1 : ∀ x : Fin n → F2, sgn (f x) = (if f x = 0 then (1 : ℤ) else 0) - (if f x = 1 then (1 : ℤ) else 0) := by
          intro x; rcases z2_cases (f x) with h | h <;> rw [h] <;> decide
        simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_boole]
      omega
    have hex_y : ∃ yStar : Fin m → F2, (∑ x ∈ Finset.univ.filter (fun x : Fin n → F2 => Φ x = yStar), sgn (f x)) ≠ 0 := by
      by_contra hno; push Not at hno
      apply hSf_ne
      have hpart_y : (∑ x : Fin n → F2, sgn (f x)) =
          ∑ y : Fin m → F2, ∑ x ∈ Finset.univ.filter (fun x : Fin n → F2 => Φ x = y), sgn (f x) := by
        rw [← Finset.sum_biUnion]
        · congr 1; ext x; simp
        · intro y1 _ y2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]; intro x hx1 hx2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
          exact hne (hx1.symm.trans hx2)
      rw [hpart_y]
      exact Finset.sum_eq_zero fun y _ => hno y
    obtain ⟨yStar, hyStar_ne⟩ := hex_y
    let pStar : List Bool := ofVec yStar
    have hpStar_len : pStar.length = m := hofVec_len yStar
    have hconst_pStar : ∃ cStar : F2, ∀ x : Fin n → F2, Φ x = yStar → f x = cStar := by
      obtain ⟨x0, hx0⟩ := hΦ_surj yStar
      have hlin_ker : ∀ u ∈ LinearMap.ker Φ, dotProduct (linOf pStar) u = 0 := by
        by_contra hne
        push Not at hne
        let L : LinearMap.ker Φ →ₗ[F2] F2 :=
          { toFun := fun u => dotProduct (linOf pStar) u.val
            map_add' := fun u1 u2 => dotProduct_add _ u1.val u2.val
            map_smul' := fun c u => by simp [dotProduct_smul] }
        have hLne : L ≠ 0 := by
          intro h0; rcases hne with ⟨u, hu, hdu⟩
          exact hdu (LinearMap.congr_fun h0 ⟨u, hu⟩)
        have hsum0 := sum_sgn_linear_submodule (LinearMap.ker Φ) L
        rw [if_neg hLne] at hsum0
        apply hyStar_ne
        let eK : LinearMap.ker Φ ≃ {x : Fin n → F2 // Φ x = yStar} :=
          { toFun := fun u => ⟨x0 + u.val, by rw [map_add, hx0, LinearMap.mem_ker.mp u.property, add_zero]⟩
            invFun := fun x => ⟨x.val - x0, by show Φ (x.val - x0) = 0; rw [map_sub, x.property, hx0, sub_self]⟩
            left_inv := fun u => Subtype.ext (by show x0 + u.val - x0 = u.val; simp)
            right_inv := fun x => Subtype.ext (by show x0 + (x.val - x0) = x.val; abel) }
        rw [Finset.sum_subtype (Finset.univ.filter (fun x : Fin n → F2 => Φ x = yStar))
            (p := fun x => Φ x = yStar) (fun x => by simp) (fun x => sgn (f x)),
            ← Equiv.sum_comp eK]
        have hterm : ∀ u : LinearMap.ker Φ, sgn (f (eK u).val) = sgn (dotProduct (linOf pStar) x0 + b) * sgn (L u) := by
          intro u
          change sgn (f (x0 + u.val)) = sgn (dotProduct (linOf pStar) x0 + b) * sgn (L u)
          have hΦu : Φ (x0 + u.val) = toVec pStar := by rw [map_add, hx0, LinearMap.mem_ker.mp u.property, add_zero, htoVec_ofVec]
          rw [hf_on_vec pStar (x0 + u.val) hΦu, dotProduct_add]
          dsimp only [L, LinearMap.coe_mk, AddHom.coe_mk]
          rw [show dotProduct (linOf pStar) x0 + dotProduct (linOf pStar) u.val + b =
              (dotProduct (linOf pStar) x0 + b) + dotProduct (linOf pStar) u.val by ring, sgn_add]
        simp_rw [hterm, ← Finset.mul_sum, hsum0, mul_zero]
      refine ⟨dotProduct (linOf pStar) x0 + b, fun x hx => ?_⟩
      have hΦx : Φ x = toVec pStar := by rw [hx, htoVec_ofVec]
      rw [hf_on_vec pStar x hΦx]
      have hdiff : x - x0 ∈ LinearMap.ker Φ := by show Φ (x - x0) = 0; rw [map_sub, hx, hx0, sub_self]
      have h0 := hlin_ker (x - x0) hdiff
      rw [z2_vec_sub_eq_add, dotProduct_add] at h0
      have hz := z2_add_self (dotProduct (linOf pStar) x0)
      linear_combination h0 - hz
    obtain ⟨cStar, hcStar⟩ := hconst_pStar
    let J : Finset (List Bool) := prefNodes ∪ (allDepth m).erase pStar
    let N : Finset (List Bool) := prefNodes ∪ allDepth m ∪ (allDepth (m + 1)).filter (fun p => p.take m ≠ pStar)
    let q : List Bool → (Fin n → F2) →ₗ[F2] F2 := fun p =>
      if h : p.length < m then dotLin (c1 ⟨p.length, h⟩) else dotLin (linOf p)
    let offset : List Bool → F2 := fun _ => 1
    let out : List Bool → F2 := fun p => if p = pStar then cStar else b + (if p.getD m false then 1 else 0)
    have hmemJ : ∀ p, p ∈ J ↔ p.length < m ∨ (p.length = m ∧ p ≠ pStar) := fun p => by
      simp only [J, Finset.mem_union, hmem_pref, Finset.mem_erase, hmem_allDepth]
      tauto
    have hmemN : ∀ p, p ∈ N ↔ p.length ≤ m ∨ (p.length = m + 1 ∧ p.take m ≠ pStar) := fun p => by
      simp only [N, Finset.mem_union, hmem_pref, hmem_allDepth, Finset.mem_filter]
      constructor
      · rintro ((h | h) | ⟨h1, h2⟩); left; omega; left; omega; right; exact ⟨h1, h2⟩
      · rintro (h | ⟨h1, h2⟩)
        · by_cases hlt : p.length < m
          · exact Or.inl (Or.inl hlt)
          · exact Or.inl (Or.inr (by omega))
        · exact Or.inr ⟨h1, h2⟩
    have hroot : [] ∈ N := (hmemN []).mpr (Or.inl (by simp))
    have hJN : J ⊆ N := by
      intro p hp; rw [hmemJ] at hp; rw [hmemN]
      rcases hp with h | ⟨h, _⟩ <;> exact Or.inl (by omega)
    have hback : ∀ (p : List Bool) (v : Bool), p ++ [v] ∈ N → p ∈ J := by
      intro p v h
      rw [hmemN] at h; rw [hmemJ]
      simp only [List.length_append, List.length_singleton] at h
      rcases h with hle | ⟨heq, hne⟩
      · left; omega
      · right
        have hlen : p.length = m := by omega
        have htake : (p ++ [v]).take m = p := by rw [← hlen]; simp
        rw [htake] at hne
        exact ⟨hlen, hne⟩
    have hfwd : ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N := by
      intro p hp
      rw [hmemJ] at hp; rw [hmemN, hmemN]
      simp only [List.length_append, List.length_singleton]
      rcases hp with hlt | ⟨heq, hne⟩
      · exact ⟨Or.inl (by omega), Or.inl (by omega)⟩
      · have ht1 : (p ++ [false]).take m = p := by rw [← heq]; simp
        have ht2 : (p ++ [true]).take m = p := by rw [← heq]; simp
        exact ⟨Or.inr ⟨by omega, by rw [ht1]; exact hne⟩, Or.inr ⟨by omega, by rw [ht2]; exact hne⟩⟩
    have hleaf_iff : ∀ p, p ∈ N \ J ↔ p = pStar ∨ (p.length = m + 1 ∧ p.take m ≠ pStar) := fun p => by
      simp only [Finset.mem_sdiff, hmemN, hmemJ]
      constructor
      · rintro ⟨h1 | h2, hnot⟩
        · left; by_contra hne
          apply hnot
          by_cases hlt : p.length < m
          · exact Or.inl hlt
          · exact Or.inr ⟨by omega, hne⟩
        · exact Or.inr h2
      · rintro (rfl | ⟨h1, h2⟩)
        · refine ⟨Or.inl (by omega), ?_⟩
          rintro (hlt | ⟨_, hne⟩); omega; exact hne rfl
        · refine ⟨Or.inr ⟨h1, h2⟩, ?_⟩
          rintro (hlt | ⟨heq, _⟩) <;> omega
    have hreaches_m : ∀ (p : List Bool) (hp : p.length = m) (x : Fin n → F2),
        (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step) ↔
        Φ x = toVec p := by
      intro p hp x
      constructor
      · intro hr
        funext i
        have hs := hr ⟨i.val, by omega⟩
        have hlt : (p.take i.val).length < m := by rw [List.length_take]; omega
        simp only [q, hlt, ↓reduceDIte, offset] at hs
        have htake_len : (p.take i.val).length = i.val := by rw [List.length_take]; omega
        have hci : c1 ⟨(p.take i.val).length, hlt⟩ = c1 i := congrArg c1 (Fin.ext htake_len)
        change decide (dotProduct (c1 ⟨(p.take i.val).length, hlt⟩) x = 1) = p.get ⟨i.val, by omega⟩ at hs
        rw [hci, List.get_eq_getElem] at hs
        dsimp only [toVec]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i.val < p.length), Option.getD_some, ← hs]
        change dotProduct (c1 i) x = _
        rcases z2_cases (dotProduct (c1 i) x) with h | h <;> rw [h] <;> decide
      · intro hΦx step
        have hlt : step.val < m := by omega
        have hlt' : (p.take step.val).length < m := by simp; omega
        simp only [q, hlt', ↓reduceDIte, offset]
        have htake_len : (p.take step.val).length = step.val := by rw [List.length_take]; omega
        have hci : c1 ⟨(p.take step.val).length, hlt'⟩ = c1 ⟨step.val, hlt⟩ := congrArg c1 (Fin.ext htake_len)
        change decide (dotProduct (c1 ⟨(p.take step.val).length, hlt'⟩) x = 1) = p.get step
        rw [hci]
        have hi : dotProduct (c1 ⟨step.val, hlt⟩) x = toVec p ⟨step.val, hlt⟩ := congrFun hΦx ⟨step.val, hlt⟩
        rw [hi]
        simp only [toVec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem step.isLt, Option.getD_some, List.get_eq_getElem]
        cases p[step.val] <;> decide
    have hreaches_m1 : ∀ (p : List Bool) (hp : p.length = m + 1) (x : Fin n → F2),
        (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step) ↔
        (Φ x = toVec p ∧ decide (dotProduct (linOf (p.take m)) x = 1) = p.get ⟨m, by omega⟩) := by
      intro p hp x
      constructor
      · intro hr
        refine ⟨funext fun i => ?_, ?_⟩
        · have hs := hr ⟨i.val, by omega⟩
          have hlt : (p.take i.val).length < m := by rw [List.length_take]; omega
          simp only [q, hlt, ↓reduceDIte, offset] at hs
          have htake_len : (p.take i.val).length = i.val := by rw [List.length_take]; omega
          have hci : c1 ⟨(p.take i.val).length, hlt⟩ = c1 i := congrArg c1 (Fin.ext htake_len)
          change decide (dotProduct (c1 ⟨(p.take i.val).length, hlt⟩) x = 1) = p.get ⟨i.val, by omega⟩ at hs
          rw [hci, List.get_eq_getElem] at hs
          dsimp only [toVec]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i.val < p.length), Option.getD_some, ← hs]
          change dotProduct (c1 i) x = _
          rcases z2_cases (dotProduct (c1 i) x) with h | h <;> rw [h] <;> decide
        · have hs := hr ⟨m, by omega⟩
          have hnot : ¬ (p.take m).length < m := by simp; omega
          simp only [q, hnot, ↓reduceDIte, offset] at hs
          exact hs
      · rintro ⟨hΦx, hm_eq⟩ step
        by_cases hlt : step.val < m
        · have hlt' : (p.take step.val).length < m := by simp; omega
          simp only [q, hlt', ↓reduceDIte, offset]
          have htake_len : (p.take step.val).length = step.val := by rw [List.length_take]; omega
          have hci : c1 ⟨(p.take step.val).length, hlt'⟩ = c1 ⟨step.val, hlt⟩ := congrArg c1 (Fin.ext htake_len)
          change decide (dotProduct (c1 ⟨(p.take step.val).length, hlt'⟩) x = 1) = p.get step
          rw [hci]
          have hi : dotProduct (c1 ⟨step.val, hlt⟩) x = toVec p ⟨step.val, hlt⟩ := congrFun hΦx ⟨step.val, hlt⟩
          rw [hi]
          simp only [toVec, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem step.isLt, Option.getD_some, List.get_eq_getElem]
          cases p[step.val] <;> decide
        · have hlt_m : m < p.length := by omega
          have hstep_lt := step.isLt
          have heq_m : step.val = m := by omega
          have hstep : step = ⟨m, hlt_m⟩ := Fin.ext heq_m
          subst hstep
          have hnot : ¬ (p.take m).length < m := by simp; omega
          simp only [q, hnot, ↓reduceDIte, offset]
          exact hm_eq
    have hpart := tree_leaf_partition N J q offset hroot hJN hback hfwd
    refine ⟨N, J, q, offset, out, hroot, hJN, hback, hfwd, ?_, ?_⟩
    · have hpStar_leaf : pStar ∈ N \ J := (hleaf_iff pStar).mpr (Or.inl rfl)
      have hcard_pStar : Nat.card {x : Fin n → F2 // ∀ step : Fin pStar.length,
          decide (q (pStar.take step.val) x = offset (pStar.take step.val)) = pStar.get step} = 2 ^ (n - m) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← hΦ_fiber_card yStar]
        congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hreaches_m pStar hpStar_len x, htoVec_ofVec]
      have hsum_cards : ∑ p ∈ N \ J, (Nat.card {x : Fin n → F2 // ∀ step : Fin p.length,
            decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step} : ℚ) = (2 : ℚ) ^ n := by
        have hnat : ∑ p ∈ N \ J, (Finset.univ.filter (fun x : Fin n → F2 => ∀ step : Fin p.length,
            decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step)).card = 2 ^ n := by
          have h1 : ∀ p ∈ N \ J, (Finset.univ.filter (fun x : Fin n → F2 => ∀ step : Fin p.length,
              decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step)).card =
              ∑ x : Fin n → F2, if p = (hpart x).choose then 1 else 0 := by
            intro p hp
            rw [← Finset.card_filter]
            congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hr; exact (hpart x).choose_spec.2 p ⟨hp, hr⟩
            · intro heq; rw [heq]; exact (hpart x).choose_spec.1.2
          rw [Finset.sum_congr rfl h1, Finset.sum_comm]
          have h2 : ∀ x : Fin n → F2, (∑ p ∈ N \ J, if p = (hpart x).choose then 1 else 0) = 1 := by
            intro x; rw [Finset.sum_ite_eq', if_pos (hpart x).choose_spec.1.1]
          simp_rw [h2]; simp [Fintype.card_fun, Fintype.card_fin, ZMod.card]
        have hq : ∑ p ∈ N \ J, ((Finset.univ.filter (fun x : Fin n → F2 => ∀ step : Fin p.length,
            decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step)).card : ℚ) = (2 : ℚ) ^ n := by
          exact_mod_cast hnat
        rw [← hq]; refine Finset.sum_congr rfl fun p _ => ?_
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      have hsplit : ∑ p ∈ N \ J, (p.length : ℚ) * (Nat.card {x : Fin n → F2 // ∀ step : Fin p.length,
            decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step} : ℚ) =
          ((m : ℚ) + 1) * (2 : ℚ) ^ n - (2 : ℚ) ^ (n - m) := by
        have hterm : ∀ p ∈ N \ J, (p.length : ℚ) * (Nat.card {x : Fin n → F2 // ∀ step : Fin p.length,
              decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step} : ℚ) =
            ((m : ℚ) + 1) * (Nat.card {x : Fin n → F2 // ∀ step : Fin p.length,
              decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step} : ℚ) -
            (if p = pStar then (2 : ℚ) ^ (n - m) else 0) := by
          intro p hp
          rcases (hleaf_iff p).mp hp with rfl | ⟨hlen, _⟩
          · have hlen_q : (pStar.length : ℚ) = (m : ℚ) := by exact_mod_cast hpStar_len
            rw [if_pos rfl, hlen_q, hcard_pStar]; push_cast; ring
          · have hne : p ≠ pStar := fun h => by rw [h, hpStar_len] at hlen; omega
            have hlen_q : (p.length : ℚ) = (m : ℚ) + 1 := by exact_mod_cast hlen
            rw [if_neg hne, hlen_q]; ring
        rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum_cards]
        have hite : (∑ p ∈ N \ J, if p = pStar then (2 : ℚ) ^ (n - m) else 0) = (2 : ℚ) ^ (n - m) := by
          rw [Finset.sum_ite_eq']; simp [hpStar_leaf]
        rw [hite]
      rw [hsplit, hcardX]
      dsimp only [exactCost, rootBias]; rw [if_neg hbal]
      have hpow : (2 : ℚ) ^ n = (2 : ℚ) ^ (n - m) * (2 : ℚ) ^ m := by
        rw [← pow_add, show (n - m) + m = n by omega]
      rw [hpow]; field_simp
    · have hall_exact : ∀ x : Fin n → F2, ∃ p ∈ N \ J,
          (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step) ∧ f x = out p := by
        intro x
        let p0 := (hpart x).choose
        have hp0 : p0 ∈ N \ J := (hpart x).choose_spec.1.1
        have hr0 : ∀ step : Fin p0.length, decide (q (p0.take step.val) x = offset (p0.take step.val)) = p0.get step :=
          (hpart x).choose_spec.1.2
        refine ⟨p0, hp0, hr0, ?_⟩
        rcases (hleaf_iff p0).mp hp0 with heq | ⟨hlen, _⟩
        · rw [heq] at hr0
          have hΦx : Φ x = toVec pStar := (hreaches_m pStar hpStar_len x).mp hr0
          rw [htoVec_ofVec] at hΦx
          dsimp only [out]; rw [if_pos heq]
          exact hcStar x hΦx
        · have hne : p0 ≠ pStar := fun h => by rw [h, hpStar_len] at hlen; omega
          rcases (hreaches_m1 p0 hlen x).mp hr0 with ⟨hΦx, hm_eq⟩
          have hto_take : toVec (p0.take m) = toVec p0 := by
            funext i; simp only [toVec, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt i.isLt]
          have hfx := hf_on_vec (p0.take m) x (by rw [hΦx, hto_take])
          rw [hfx]
          dsimp only [out]; rw [if_neg hne]
          rw [List.get_eq_getElem] at hm_eq
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : m < p0.length), Option.getD_some, ← hm_eq]
          rcases z2_cases (dotProduct (linOf (p0.take m)) x) with h | h <;> rw [h] <;> simp [add_comm]
      have hcard_all : Nat.card {x : Fin n → F2 // ∃ p ∈ N \ J,
          (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step) ∧ f x = out p} =
          Nat.card (Fin n → F2) := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
        have hf_univ : Finset.univ.filter (fun x : Fin n → F2 => ∃ p ∈ N \ J,
            (∀ step : Fin p.length, decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step) ∧ f x = out p) =
            Finset.univ := by ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; exact hall_exact x
        rw [hf_univ, Finset.card_univ]
      rw [hcard_all]; ring

lemma main_pcx_456 (n : ℕ) (f : (Fin n → F2) → F2)
    (hf : ∀ p u v : Fin n → F2, f (p + u + v) + f (p + u) + f (p + v) + f p = f (u + v) + f u + f v + f 0) :
    let B := fun u v : Fin n → F2 => f (u + v) + f u + f v + f 0
    let m := (n - (Nat.card {u : Fin n → F2 // ∀ v : Fin n → F2, B u v = 0}).log2) / 2
    let bal := Nat.card {x : Fin n → F2 // f x = 0} = Nat.card {x : Fin n → F2 // f x = 1}
    let rootBias : ℚ := if bal then 0 else 1 / (2 : ℚ) ^ m
    let size := (Nat.card (Fin n → F2) : ℚ)
    let tree := fun (cost adv : ℚ) => ∃ (N J : Finset (List Bool))
      (q : List Bool → (Fin n → F2) →ₗ[F2] F2) (offset out : List Bool → F2),
      let leaf := N \ J
      let reaches := fun (p : List Bool) (x : Fin n → F2) => ∀ step : Fin p.length,
        decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (v : Bool), p ++ [v] ∈ N → p ∈ J) ∧
      (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
      cost * size = ∑ p ∈ leaf, (p.length : ℚ) * (Nat.card {x : Fin n → F2 // reaches p x} : ℚ) ∧
      (adv + 1) * size = 2 * (Nat.card {x : Fin n → F2 // ∃ p ∈ leaf, reaches p x ∧ f x = out p} : ℚ)
    let mix := fun (r : ℕ) (w c v : Fin r → ℚ) => (∀ i, 0 ≤ w i ∧ tree (c i) (v i)) ∧ (∑ i, w i) = 1
    let exactCost := (m : ℚ) + 1 - rootBias
    ∀ t : ℚ, 0 ≤ t → t ≤ 1 →
      let target := rootBias + (1 - rootBias) * t
      (∀ budget : ℚ,
        (∃ (r : ℕ) (w c v : Fin r → ℚ), mix r w c v ∧ (∑ i, w i * c i) ≤ budget ∧ target ≤ ∑ i, w i * v i) ↔
        t * exactCost ≤ budget) ∧
      ((Not bal) → (0 < m) → ∀ (r : ℕ) (w c v : Fin r → ℚ), mix r w c v →
        (∑ i, w i * c i) ≤ t * exactCost → target ≤ (∑ i, w i * v i) →
        ∀ j, (0 < w j) → (c j = 0 ∧ v j = rootBias) ∨ (c j = exactCost ∧ v j = 1)) := by
  intro B m bal rootBias size tree mix exactCost t ht0 ht1 target
  obtain ⟨M, hM, hMsymm, _⟩ := quad_bilin_matrix f hf
  obtain ⟨m0, _, _, _, _, _, hrk_eq, _, _, _⟩ := symplectic_normal_form M.rank f M rfl hM
  have hker_card : Nat.card {u : Fin n → F2 // ∀ v : Fin n → F2, B u v = 0} = 2 ^ Module.finrank F2 (LinearMap.ker M.mulVecLin) := by
    rw [Nat.card_eq_fintype_card]
    let eR : LinearMap.ker M.mulVecLin ≃ {u : Fin n → F2 // ∀ v : Fin n → F2, B u v = 0} :=
      { toFun := fun u => ⟨u.val, fun v => by dsimp only [B]; rw [hM, hMsymm]; change dotProduct v (M.mulVec u.val) = 0; have h0 : M.mulVec u.val = 0 := u.property; rw [h0, dotProduct_zero]⟩
        invFun := fun u => ⟨u.val, by
          show M.mulVec u.val = 0
          funext i
          have hi := u.property (Pi.single i 1)
          dsimp only [B] at hi
          rw [hM, hMsymm] at hi
          simpa [single_dotProduct] using hi⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← Fintype.card_congr eR, card_submodule_z2]
  have hm_eq : m = m0 := by
    dsimp only [m]
    rw [hker_card, Nat.log2_two_pow]
    have hMrk := rank_add_ker_mat M
    omega
  have hrk_m : M.rank = 2 * m := by omega
  have hrb_le1 : rootBias ≤ 1 := by
    dsimp only [rootBias]; split_ifs
    · norm_num
    · rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have htriv : tree 0 rootBias := exists_trivial_tree f M hrk_m hM
  have hpeel : tree exactCost 1 := exists_peel_tree f M hrk_m hM
  constructor
  · intro budget
    constructor
    · rintro ⟨r, w, c, v, ⟨hw_tree, hw_sum⟩, hbud, htar⟩
      have htree_all : ∀ i : Fin r, 0 ≤ c i ∧ (1 - rootBias) * c i ≥ exactCost * (v i - rootBias) := by
        intro i
        rcases (hw_tree i).2 with ⟨N, J, q, offset, out, h1, h2, h3, h4, h5, h6⟩
        have hb := tree_cost_adv_bound f M hrk_m hM (c i) (v i) N J q offset out h1 h2 h3 h4 h5 h6
        exact ⟨hb.1, hb.2.2.2.2.1⟩
      by_cases hrb1 : rootBias = 1
      · have hex0 : exactCost = 0 := by
          dsimp only [exactCost, rootBias] at hrb1 ⊢
          by_cases hbal : bal
          · rw [if_pos hbal] at hrb1; norm_num at hrb1
          · rw [if_neg hbal] at hrb1 ⊢
            have hpow1 : (2 : ℚ) ^ m = 1 := by
              have := (div_eq_iff (by positivity : (2 : ℚ) ^ m ≠ 0)).mp hrb1
              linarith
            have hm0 : m = 0 := by
              by_contra hne
              have : (2 : ℚ) ^ 1 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
              linarith
            rw [hm0]; norm_num
        rw [hex0, mul_zero]
        have hnn : 0 ≤ ∑ i : Fin r, w i * c i :=
          Finset.sum_nonneg fun i _ => mul_nonneg (hw_tree i).1 (htree_all i).1
        linarith
      · have h1m_pos : 0 < 1 - rootBias := lt_of_le_of_ne (by linarith) (fun h => hrb1 (by linarith))
        have hsum_ineq : (1 - rootBias) * (∑ i : Fin r, w i * c i) ≥ exactCost * ((∑ i : Fin r, w i * v i) - rootBias) := by
          have h1 : (1 - rootBias) * (∑ i : Fin r, w i * c i) = ∑ i : Fin r, w i * ((1 - rootBias) * c i) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
          have h2 : exactCost * ((∑ i : Fin r, w i * v i) - rootBias) = ∑ i : Fin r, w i * (exactCost * (v i - rootBias)) := by
            have hrb_sum : rootBias = ∑ i : Fin r, w i * rootBias := by rw [← Finset.sum_mul, hw_sum, one_mul]
            conv_lhs => rw [hrb_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => by ring
          rw [h1, h2]
          exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (htree_all i).2 (hw_tree i).1
        have hex_nn : 0 ≤ exactCost := by dsimp only [exactCost]; linarith
        have htar' : (1 - rootBias) * t ≤ (∑ i : Fin r, w i * v i) - rootBias := by dsimp only [target] at htar; linarith
        have hmul : exactCost * ((1 - rootBias) * t) ≤ exactCost * ((∑ i : Fin r, w i * v i) - rootBias) :=
          mul_le_mul_of_nonneg_left htar' hex_nn
        have hcomb : (1 - rootBias) * (t * exactCost) ≤ (1 - rootBias) * budget := by
          have : (1 - rootBias) * (∑ i : Fin r, w i * c i) ≤ (1 - rootBias) * budget :=
            mul_le_mul_of_nonneg_left hbud (le_of_lt h1m_pos)
          linarith
        nlinarith
    · intro hbud
      refine ⟨2, fun i => if i = 0 then 1 - t else t, fun i => if i = 0 then 0 else exactCost,
        fun i => if i = 0 then rootBias else 1, ⟨?_, ?_⟩, ?_, ?_⟩
      · intro i; fin_cases i
        · simp only [Fin.zero_eta, ↓reduceIte]; exact ⟨by linarith, htriv⟩
        · simp only [Fin.mk_one, Fin.one_eq_zero_iff, Nat.reduceEqDiff, ↓reduceIte]; exact ⟨ht0, hpeel⟩
      · simp only [Fin.sum_univ_two, Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]; ring
      · simp only [Fin.sum_univ_two, Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]; linarith
      · simp only [Fin.sum_univ_two, Fin.isValue, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
        dsimp only [target]; linarith
  · intro hnb hmpos r w c v ⟨hw_tree, hw_sum⟩ hbud htar j hwj
    have htree_all : ∀ i : Fin r, (1 - rootBias) * c i ≥ exactCost * (v i - rootBias) ∧
        ((1 - rootBias) * c i = exactCost * (v i - rootBias) → (c i = 0 ∧ v i = rootBias) ∨ (c i = exactCost ∧ v i = 1)) := by
      intro i
      rcases (hw_tree i).2 with ⟨N, J, q, offset, out, h1, h2, h3, h4, h5, h6⟩
      have hb := tree_cost_adv_bound f M hrk_m hM (c i) (v i) N J q offset out h1 h2 h3 h4 h5 h6
      exact ⟨hb.2.2.2.2.1, hb.2.2.2.2.2 hnb hmpos⟩
    let gap : Fin r → ℚ := fun i => (1 - rootBias) * c i - exactCost * (v i - rootBias)
    have hgap_nn : ∀ i : Fin r, 0 ≤ gap i := fun i => by dsimp only [gap]; linarith [(htree_all i).1]
    have hrb_lt1 : rootBias < 1 := by
      dsimp only [rootBias]; rw [if_neg hnb, div_lt_one (by positivity)]
      have : (2 : ℚ) ^ 1 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have hex_nn : 0 ≤ exactCost := by dsimp only [exactCost]; linarith
    have hsum_le0 : ∑ i : Fin r, w i * gap i ≤ 0 := by
      have h1 : ∑ i : Fin r, w i * gap i =
          (1 - rootBias) * (∑ i : Fin r, w i * c i) - exactCost * ((∑ i : Fin r, w i * v i) - rootBias) := by
        have hrb_sum : ∑ i : Fin r, w i * rootBias = rootBias := by rw [← Finset.sum_mul, hw_sum, one_mul]
        have ha : ∑ i : Fin r, w i * ((1 - rootBias) * c i) = (1 - rootBias) * (∑ i : Fin r, w i * c i) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
        have hb : ∑ i : Fin r, w i * (exactCost * (v i - rootBias)) = exactCost * ((∑ i : Fin r, w i * v i) - rootBias) := by
          have hsub : ∑ i : Fin r, w i * (exactCost * (v i - rootBias)) =
              exactCost * (∑ i : Fin r, w i * v i) - exactCost * (∑ i : Fin r, w i * rootBias) := by
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun i _ => by ring
          rw [hsub, hrb_sum]; ring
        have hsplit : ∑ i : Fin r, w i * gap i =
            (∑ i : Fin r, w i * ((1 - rootBias) * c i)) - (∑ i : Fin r, w i * (exactCost * (v i - rootBias))) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ => by dsimp only [gap]; ring
        rw [hsplit, ha, hb]
      rw [h1]
      have htar' : (1 - rootBias) * t ≤ (∑ i : Fin r, w i * v i) - rootBias := by dsimp only [target] at htar; linarith
      have hc_le : (1 - rootBias) * (∑ i : Fin r, w i * c i) ≤ (1 - rootBias) * (t * exactCost) :=
        mul_le_mul_of_nonneg_left hbud (by linarith)
      have hv_ge : exactCost * ((1 - rootBias) * t) ≤ exactCost * ((∑ i : Fin r, w i * v i) - rootBias) :=
        mul_le_mul_of_nonneg_left htar' hex_nn
      linarith
    have hsum_ge0 : 0 ≤ ∑ i : Fin r, w i * gap i :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hw_tree i).1 (hgap_nn i)
    have hsum_eq0 : ∑ i : Fin r, w i * gap i = 0 := le_antisymm hsum_le0 hsum_ge0
    have hwgap0 : w j * gap j = 0 := by
      have hle : w j * gap j ≤ ∑ i : Fin r, w i * gap i :=
        Finset.single_le_sum (fun i _ => mul_nonneg (hw_tree i).1 (hgap_nn i)) (Finset.mem_univ j)
      have hge : 0 ≤ w j * gap j := mul_nonneg (hw_tree j).1 (hgap_nn j)
      linarith
    have hgap0 : gap j = 0 := (mul_eq_zero.mp hwgap0).resolve_left (ne_of_gt hwj)
    exact (htree_all j).2 (by dsimp only [gap] at hgap0; linarith)

end PEqualNP.Outside.L_pcx_456_aux

theorem PEqualNP.Outside.L_pcx_456 :
∀ (n : ℕ),
  let F := ZMod 2
  let X := Fin n → F
  ∀ f : X → F,
    let B := fun u v : X => f (u+v)+f u+f v+f 0
    (∀ p u v : X, f (p+u+v)+f (p+u)+f (p+v)+f p=B u v) →
    let m := (n-(Nat.card {u : X // ∀ v : X, B u v=0}).log2)/2
    let bal := Nat.card {x : X // f x=0} = Nat.card {x : X // f x=1}
    let rootBias := if bal then (0 : ℚ) else 1/(2:ℚ)^m
    let size := (Nat.card X : ℚ)
    let tree := fun (cost adv : ℚ) => ∃ (N J : Finset (List Bool))
      (q : List Bool → X →ₗ[F] F) (offset out : List Bool → F),
      let leaf := N \ J
      let reaches := fun (p : List Bool) (x : X) => ∀ step : Fin p.length,
        decide (q (p.take step.val) x = offset (p.take step.val)) = p.get step
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (v : Bool), p ++ [v] ∈ N → p ∈ J) ∧
      (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
      cost*size = ∑ p ∈ leaf, (p.length : ℚ)*(Nat.card {x : X // reaches p x} : ℚ) ∧
      (adv+1)*size = 2*(Nat.card {x : X // ∃ p ∈ leaf, reaches p x ∧ f x=out p} : ℚ)
    let mix := fun (r : ℕ) (w c v : Fin r → ℚ) =>
      (∀ i, 0≤w i ∧ tree (c i) (v i)) ∧ (∑ i, w i)=1
    let exactCost := (m:ℚ)+1-rootBias
    ∀ t : ℚ, 0≤t → t≤1 →
      let target := rootBias+(1-rootBias)*t
      (∀ budget : ℚ,
        (∃ (r : ℕ) (w c v : Fin r → ℚ), mix r w c v ∧
          (∑ i, w i*c i) ≤ budget ∧ target ≤ ∑ i, w i*v i) ↔
        t*exactCost ≤ budget) ∧
      ((Not bal) → (0 < m) → ∀ (r : ℕ) (w c v : Fin r → ℚ), mix r w c v →
        (∑ i, w i*c i) ≤ t*exactCost → target ≤ (∑ i, w i*v i) →
        ∀ j, (0 < w j) → (c j=0 ∧ v j=rootBias) ∨ (c j=exactCost ∧ v j=1)) := by
  intro n F X f B hf m bal rootBias size tree mix exactCost t ht0 ht1 target
  exact PEqualNP.Outside.L_pcx_456_aux.main_pcx_456 n f hf t ht0 ht1
