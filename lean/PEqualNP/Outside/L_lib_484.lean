import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_484_aux

private theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private theorem zmod2_vec_add_self {n : ℕ} (x : Fin n → ZMod 2) : x + x = 0 := by
  funext i
  exact zmod2_add_self (x i)

private theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem zmod2_add_cancel {a b c : ZMod 2} (h : a + b = c) : a = c + b := by
  rw [← h, add_assoc, zmod2_add_self, add_zero]

private theorem dotProduct_single_mulVec_single {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) (i j : Fin n) :
    dotProduct (Pi.single i (1 : ZMod 2)) (M.mulVec (Pi.single j 1)) = M i j := by
  simp only [dotProduct, Matrix.mulVec]
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, one_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hlj
      simp [Pi.single_eq_of_ne hlj]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · intro k _ hki
    simp [Pi.single_eq_of_ne hki]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private theorem matrix_eq_of_bilin_eq {n : ℕ}
    (M₁ M₂ : Matrix (Fin n) (Fin n) (ZMod 2))
    (h : ∀ x y : Fin n → ZMod 2, dotProduct x (M₁.mulVec y) = dotProduct x (M₂.mulVec y)) :
    M₁ = M₂ := by
  ext i j
  have hij := h (Pi.single i 1) (Pi.single j 1)
  rwa [dotProduct_single_mulVec_single, dotProduct_single_mulVec_single] at hij

private theorem vecMulVec_mulVec_eq {n : ℕ} (u v y : Fin n → ZMod 2) :
    (Matrix.vecMulVec u v).mulVec y = (dotProduct v y) • u := by
  funext i
  simp only [Matrix.mulVec, Matrix.vecMulVec, Matrix.of_apply, dotProduct, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem dotProduct_vecMulVec_mulVec {n : ℕ} (u v x y : Fin n → ZMod 2) :
    dotProduct x ((Matrix.vecMulVec u v).mulVec y) = dotProduct u x * dotProduct v y := by
  rw [vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul, dotProduct_comm x u, mul_comm]

private theorem rank_zero_eq {n : ℕ} : (0 : Matrix (Fin n) (Fin n) (ZMod 2)).rank = 0 := by
  simp [Matrix.rank]

private theorem eq_zero_of_rank_zero {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) (h : M.rank = 0) : M = 0 := by
  rw [Matrix.rank, Submodule.finrank_eq_zero] at h
  apply matrix_eq_of_bilin_eq M 0
  intro x y
  have hy : M.mulVec y ∈ LinearMap.range M.mulVecLin := ⟨y, rfl⟩
  rw [h, Submodule.mem_bot] at hy
  simp [hy]

private theorem rank_vecMulVec_le_one {n : ℕ} (u v : Fin n → ZMod 2) :
    (Matrix.vecMulVec u v).rank ≤ 1 := by
  rw [Matrix.rank]
  have hle : LinearMap.range (Matrix.vecMulVec u v).mulVecLin ≤ Submodule.span (ZMod 2) {u} := by
    rintro _ ⟨y, rfl⟩
    change (Matrix.vecMulVec u v).mulVec y ∈ Submodule.span (ZMod 2) {u}
    rw [vecMulVec_mulVec_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  have h1 := Submodule.finrank_mono hle
  by_cases hu : u = 0
  · subst hu
    have hbot : Submodule.span (ZMod 2) ({0} : Set (Fin n → ZMod 2)) = ⊥ := by
      simp
    rw [hbot, finrank_bot] at h1
    omega
  · rw [finrank_span_singleton hu] at h1
    exact h1

private theorem rank_add_le_aux {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (A + B).rank ≤ A.rank + B.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.rank]
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨y, rfl⟩
    have hadd : (A + B).mulVecLin y = A.mulVecLin y + B.mulVecLin y := by
      change (A + B).mulVec y = A.mulVec y + B.mulVec y
      exact Matrix.add_mulVec A B y
    rw [hadd]
    exact Submodule.add_mem_sup ⟨y, rfl⟩ ⟨y, rfl⟩
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  omega

private theorem rank_sum_le_aux {n : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → Matrix (Fin n) (Fin n) (ZMod 2)) :
    (∑ i ∈ s, F i).rank ≤ ∑ i ∈ s, (F i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [rank_zero_eq]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact le_trans (rank_add_le_aux _ _) (Nat.add_le_add_left ih _)

private theorem polar_prod {n : ℕ} (a b x y : Fin n → ZMod 2) :
    dotProduct a (x + y) * dotProduct b (x + y) +
      dotProduct a x * dotProduct b x + dotProduct a y * dotProduct b y +
      dotProduct a 0 * dotProduct b 0 =
    dotProduct x ((Matrix.vecMulVec a b + Matrix.vecMulVec b a).mulVec y) := by
  rw [dotProduct_add, dotProduct_add, dotProduct_zero, dotProduct_zero, zero_mul, add_zero,
    Matrix.add_mulVec, dotProduct_add, dotProduct_vecMulVec_mulVec, dotProduct_vecMulVec_mulVec]
  have h1 : dotProduct a x * dotProduct b x + dotProduct a x * dotProduct b x = 0 :=
    zmod2_add_self _
  have h2 : dotProduct a y * dotProduct b y + dotProduct a y * dotProduct b y = 0 :=
    zmod2_add_self _
  calc
    (dotProduct a x + dotProduct a y) * (dotProduct b x + dotProduct b y) +
        dotProduct a x * dotProduct b x + dotProduct a y * dotProduct b y
      = (dotProduct a x * dotProduct b x + dotProduct a x * dotProduct b x) +
        (dotProduct a y * dotProduct b y + dotProduct a y * dotProduct b y) +
        (dotProduct a x * dotProduct b y + dotProduct b x * dotProduct a y) := by ring
    _ = dotProduct a x * dotProduct b y + dotProduct b x * dotProduct a y := by
        rw [h1, h2, zero_add, zero_add]

private theorem linear_of_zero_polar {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2)
    (h0 : ∀ x y : Fin n → ZMod 2, f (x + y) + f x + f y + f 0 = 0) :
    ∃ (c : Fin n → ZMod 2) (e : ZMod 2), ∀ x : Fin n → ZMod 2, f x = dotProduct c x + e := by
  let g : (Fin n → ZMod 2) → ZMod 2 := fun x => f x + f 0
  have hg0 : g 0 = 0 := zmod2_add_self (f 0)
  have hg_add : ∀ x y : Fin n → ZMod 2, g (x + y) = g x + g y := by
    intro x y
    have hxy := h0 x y
    have h1 : g (x + y) + (g x + g y) = 0 := by
      dsimp only [g]
      have hff : f 0 + f 0 = 0 := zmod2_add_self (f 0)
      calc
        f (x + y) + f 0 + (f x + f 0 + (f y + f 0))
          = (f (x + y) + f x + f y + f 0) + (f 0 + f 0) := by ring
        _ = 0 := by rw [hxy, hff, add_zero]
    have h2 := zmod2_add_cancel h1
    simpa only [zero_add] using h2
  have hg_sum : ∀ (s : Finset (Fin n)) (u : Fin n → (Fin n → ZMod 2)),
      g (∑ i ∈ s, u i) = ∑ i ∈ s, g (u i) := by
    intro s u
    classical
    induction s using Finset.induction_on with
    | empty => simp [hg0]
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, hg_add, ih]
  let c : Fin n → ZMod 2 := fun i => g (Pi.single i 1)
  refine ⟨c, f 0, fun x => ?_⟩
  have hx_eq : x = ∑ i : Fin n, Pi.single i (x i) := by
    funext j
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp [Pi.single_eq_of_ne (Ne.symm hkj)]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hgx : g x = dotProduct c x := by
    conv_lhs => rw [hx_eq]
    rw [hg_sum]
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    rcases zmod2_eq_zero_or_one (x i) with hxi | hxi
    · rw [hxi, Pi.single_zero, hg0, mul_zero]
    · rw [hxi, mul_one]
  have hfx : f x = g x + f 0 := by
    dsimp only [g]
    rw [add_assoc, zmod2_add_self, add_zero]
  rw [hfx, hgx]

private theorem rank_step_drop {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (halt : ∀ x : Fin n → ZMod 2, dotProduct x (M.mulVec x) = 0)
    (hsym : ∀ x y : Fin n → ZMod 2, dotProduct x (M.mulVec y) = dotProduct y (M.mulVec x))
    (u v : Fin n → ZMod 2) (huv : dotProduct u (M.mulVec v) = 1) :
    let a := M.mulVec v
    let b := M.mulVec u
    let M' := M + Matrix.vecMulVec a b + Matrix.vecMulVec b a
    M'.rank + 2 ≤ M.rank := by
  intro a b M'
  have hvu : dotProduct v (M.mulVec u) = 1 := by rw [← hsym u v, huv]
  have hau : dotProduct a u = 1 := by rw [dotProduct_comm, huv]
  have hav : dotProduct a v = 0 := by rw [dotProduct_comm]; exact halt v
  have hbu : dotProduct b u = 0 := by rw [dotProduct_comm]; exact halt u
  have hbv : dotProduct b v = 1 := by rw [dotProduct_comm, hvu]
  have hM'_mul : ∀ w : Fin n → ZMod 2,
      M'.mulVec w = M.mulVec w + (dotProduct b w) • a + (dotProduct a w) • b := by
    intro w
    simp only [M', Matrix.add_mulVec, vecMulVec_mulVec_eq]
  let K := LinearMap.ker M.mulVecLin
  let K' := LinearMap.ker M'.mulVecLin
  let H1 := Submodule.span (ZMod 2) ({u} : Set (Fin n → ZMod 2))
  let H2 := Submodule.span (ZMod 2) ({v} : Set (Fin n → ZMod 2))
  let H := H1 ⊔ H2
  have hKK' : K ≤ K' := by
    intro w hw
    change M'.mulVec w = 0
    have hMw : M.mulVec w = 0 := hw
    have haw : dotProduct a w = 0 := by
      dsimp only [a]
      rw [dotProduct_comm, hsym w v, hMw, dotProduct_zero]
    have hbw : dotProduct b w = 0 := by
      dsimp only [b]
      rw [dotProduct_comm, hsym w u, hMw, dotProduct_zero]
    rw [hM'_mul w, hMw, haw, hbw, zero_smul, zero_smul, add_zero, add_zero]
  have huK' : u ∈ K' := by
    change M'.mulVec u = 0
    rw [hM'_mul u, hbu, hau, zero_smul, one_smul, add_zero]
    exact zmod2_vec_add_self b
  have hvK' : v ∈ K' := by
    change M'.mulVec v = 0
    rw [hM'_mul v, hbv, hav, one_smul, zero_smul, add_zero]
    exact zmod2_vec_add_self a
  have hHK' : H ≤ K' := by
    refine sup_le ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem]; exact huK'
    · rw [Submodule.span_singleton_le_iff_mem]; exact hvK'
  have hu_ne : u ≠ 0 := by
    intro h0
    rw [h0, zero_dotProduct] at huv
    exact zero_ne_one huv
  have hv_ne : v ≠ 0 := by
    intro h0
    rw [h0, Matrix.mulVec_zero, dotProduct_zero] at huv
    exact zero_ne_one huv
  have hH12 : H1 ⊓ H2 = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    rcases Submodule.mem_span_singleton.1 hw.1 with ⟨c1, hc1⟩
    rcases Submodule.mem_span_singleton.1 hw.2 with ⟨c2, hc2⟩
    have hdot := congrArg (fun z => dotProduct z a) (hc1.trans hc2.symm)
    simp only [smul_dotProduct, smul_eq_mul] at hdot
    rw [dotProduct_comm u a, hau, dotProduct_comm v a, hav, mul_one, mul_zero] at hdot
    rw [← hc1, hdot, zero_smul]
  have hfinH : Module.finrank (ZMod 2) H = 2 := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq H1 H2
    rw [hH12, finrank_bot, add_zero, finrank_span_singleton hu_ne,
      finrank_span_singleton hv_ne] at hsum
    exact hsum
  have hKH : K ⊓ H = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    have hMw : M.mulVec w = 0 := hw.1
    rcases Submodule.mem_sup.1 hw.2 with ⟨w1, hw1, w2, hw2, rfl⟩
    rcases Submodule.mem_span_singleton.1 hw1 with ⟨c1, rfl⟩
    rcases Submodule.mem_span_singleton.1 hw2 with ⟨c2, rfl⟩
    have hv_dot : dotProduct v (M.mulVec (c1 • u + c2 • v)) = 0 := by
      rw [hMw, dotProduct_zero]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      hvu, halt v, mul_one, mul_zero, add_zero] at hv_dot
    have hu_dot : dotProduct u (M.mulVec (c1 • u + c2 • v)) = 0 := by
      rw [hMw, dotProduct_zero]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      halt u, huv, mul_zero, mul_one, zero_add] at hu_dot
    rw [hv_dot, hu_dot, zero_smul, zero_smul, add_zero]
  have hker_le : Module.finrank (ZMod 2) K + 2 ≤ Module.finrank (ZMod 2) K' := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq K H
    rw [hKH, finrank_bot, add_zero, hfinH] at h1
    have h2 := Submodule.finrank_mono (sup_le hKK' hHK')
    omega
  have hrnM := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hrnM' := LinearMap.finrank_range_add_finrank_ker M'.mulVecLin
  rw [Matrix.rank, Matrix.rank]
  dsimp only [K, K'] at hker_le
  omega

private theorem forward_dir (n t : ℕ) :
    ∀ (f : (Fin n → ZMod 2) → ZMod 2) (M : Matrix (Fin n) (Fin n) (ZMod 2)),
      (∀ x y : Fin n → ZMod 2, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y)) →
      M.rank ≤ 2 * t →
      ∃ (A B : Fin t → (Fin n → ZMod 2)) (c : Fin n → ZMod 2) (e : ZMod 2),
        ∀ x : Fin n → ZMod 2, f x = dotProduct c x + e +
          ∑ i : Fin t, dotProduct (A i) x * dotProduct (B i) x := by
  induction t with
  | zero =>
    intro f M hM hrank
    have hM0 : M = 0 := eq_zero_of_rank_zero M (by omega)
    have h0 : ∀ x y : Fin n → ZMod 2, f (x + y) + f x + f y + f 0 = 0 := by
      intro x y
      rw [hM x y, hM0, Matrix.zero_mulVec, dotProduct_zero]
    obtain ⟨c, e, hce⟩ := linear_of_zero_polar f h0
    refine ⟨Fin.elim0, Fin.elim0, c, e, fun x => ?_⟩
    simp [hce x]
  | succ t ih =>
    intro f M hM hrank
    by_cases hM0 : M = 0
    · have h0 : ∀ x y : Fin n → ZMod 2, f (x + y) + f x + f y + f 0 = 0 := by
        intro x y
        rw [hM x y, hM0, Matrix.zero_mulVec, dotProduct_zero]
      obtain ⟨c, e, hce⟩ := linear_of_zero_polar f h0
      refine ⟨fun _ => 0, fun _ => 0, c, e, fun x => ?_⟩
      simp [hce x]
    · have halt : ∀ x : Fin n → ZMod 2, dotProduct x (M.mulVec x) = 0 := by
        intro x
        have hx := hM x x
        rw [zmod2_vec_add_self, add_assoc (f 0), zmod2_add_self, add_zero, zmod2_add_self] at hx
        exact hx.symm
      have hsym : ∀ x y : Fin n → ZMod 2, dotProduct x (M.mulVec y) = dotProduct y (M.mulVec x) := by
        intro x y
        rw [← hM x y, ← hM y x, add_comm x y]
        ring
      have hex : ∃ u v : Fin n → ZMod 2, dotProduct u (M.mulVec v) = 1 := by
        have hij : ∃ i j : Fin n, M i j ≠ 0 := by
          by_contra hall
          push_neg at hall
          apply hM0
          ext i j
          exact hall i j
        obtain ⟨i, j, hij⟩ := hij
        have h1 : M i j = 1 := by
          rcases zmod2_eq_zero_or_one (M i j) with h | h
          · exact absurd h hij
          · exact h
        exact ⟨Pi.single i 1, Pi.single j 1, by rw [dotProduct_single_mulVec_single, h1]⟩
      obtain ⟨u, v, huv⟩ := hex
      let a := M.mulVec v
      let b := M.mulVec u
      let f' : (Fin n → ZMod 2) → ZMod 2 := fun x => f x + dotProduct a x * dotProduct b x
      let M' := M + Matrix.vecMulVec a b + Matrix.vecMulVec b a
      have hM' : ∀ x y : Fin n → ZMod 2, f' (x + y) + f' x + f' y + f' 0 = dotProduct x (M'.mulVec y) := by
        intro x y
        have hp := polar_prod a b x y
        have hxy := hM x y
        have hadd : dotProduct x (M'.mulVec y) =
            dotProduct x (M.mulVec y) +
              dotProduct x ((Matrix.vecMulVec a b + Matrix.vecMulVec b a).mulVec y) := by
          simp only [M', add_assoc, Matrix.add_mulVec, dotProduct_add]
        rw [hadd, ← hxy, ← hp]
        dsimp only [f']
        ring
      have hdrop : M'.rank + 2 ≤ M.rank := rank_step_drop M halt hsym u v huv
      obtain ⟨A', B', c, e, hce⟩ := ih f' M' hM' (by omega)
      refine ⟨Fin.cons a A', Fin.cons b B', c, e, fun x => ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have hfx : f x = f' x + dotProduct a x * dotProduct b x := by
        dsimp only [f']
        rw [add_assoc, zmod2_add_self, add_zero]
      rw [hfx, hce x]
      ring

private theorem main_core (n : ℕ) (f : (Fin n → ZMod 2) → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hM : ∀ x y : Fin n → ZMod 2, f (x + y) + f x + f y + f 0 = dotProduct x (M.mulVec y))
    (t : ℕ) :
    M.rank ≤ 2 * t ↔
      ∃ (A B : Fin t → (Fin n → ZMod 2)) (c : Fin n → ZMod 2) (e : ZMod 2),
        ∀ x : Fin n → ZMod 2, f x = dotProduct c x + e +
          ∑ i : Fin t, dotProduct (A i) x * dotProduct (B i) x := by
  constructor
  · exact forward_dir n t f M hM
  · rintro ⟨A, B, c, e, hce⟩
    let M' : Matrix (Fin n) (Fin n) (ZMod 2) :=
      ∑ i : Fin t, (Matrix.vecMulVec (A i) (B i) + Matrix.vecMulVec (B i) (A i))
    have hMeq : M = M' := by
      apply matrix_eq_of_bilin_eq
      intro x y
      rw [← hM x y, hce (x + y), hce x, hce y, hce 0]
      have hlin : (dotProduct c (x + y) + e) + (dotProduct c x + e) +
          (dotProduct c y + e) + (dotProduct c 0 + e) = 0 := by
        rw [dotProduct_add, dotProduct_zero]
        have hcx := zmod2_add_self (dotProduct c x)
        have hcy := zmod2_add_self (dotProduct c y)
        have he := zmod2_add_self e
        calc
          dotProduct c x + dotProduct c y + e + (dotProduct c x + e) +
              (dotProduct c y + e) + (0 + e)
            = (dotProduct c x + dotProduct c x) + (dotProduct c y + dotProduct c y) +
              (e + e) + (e + e) := by ring
          _ = 0 := by rw [hcx, hcy, he]; ring
      have hquad : ∑ i : Fin t, dotProduct (A i) (x + y) * dotProduct (B i) (x + y) +
          ∑ i : Fin t, dotProduct (A i) x * dotProduct (B i) x +
          ∑ i : Fin t, dotProduct (A i) y * dotProduct (B i) y +
          ∑ i : Fin t, dotProduct (A i) 0 * dotProduct (B i) 0 =
          dotProduct x (M'.mulVec y) := by
        simp only [← Finset.sum_add_distrib, M']
        have hmul_sum : (∑ i : Fin t, (Matrix.vecMulVec (A i) (B i) + Matrix.vecMulVec (B i) (A i))).mulVec y =
            ∑ i : Fin t, (Matrix.vecMulVec (A i) (B i) + Matrix.vecMulVec (B i) (A i)).mulVec y := by
          funext r
          simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Matrix.sum_apply, Finset.sum_mul]
          exact Finset.sum_comm
        rw [hmul_sum, dotProduct_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact polar_prod (A i) (B i) x y
      calc
        dotProduct c (x + y) + e + ∑ i : Fin t, dotProduct (A i) (x + y) * dotProduct (B i) (x + y) +
            (dotProduct c x + e + ∑ i : Fin t, dotProduct (A i) x * dotProduct (B i) x) +
            (dotProduct c y + e + ∑ i : Fin t, dotProduct (A i) y * dotProduct (B i) y) +
            (dotProduct c 0 + e + ∑ i : Fin t, dotProduct (A i) 0 * dotProduct (B i) 0)
          = ((dotProduct c (x + y) + e) + (dotProduct c x + e) +
              (dotProduct c y + e) + (dotProduct c 0 + e)) +
            (∑ i : Fin t, dotProduct (A i) (x + y) * dotProduct (B i) (x + y) +
              ∑ i : Fin t, dotProduct (A i) x * dotProduct (B i) x +
              ∑ i : Fin t, dotProduct (A i) y * dotProduct (B i) y +
              ∑ i : Fin t, dotProduct (A i) 0 * dotProduct (B i) 0) := by ring
        _ = dotProduct x (M'.mulVec y) := by rw [hlin, zero_add, hquad]
    rw [hMeq]
    have hsum_le := rank_sum_le_aux (Finset.univ : Finset (Fin t))
      (fun i => Matrix.vecMulVec (A i) (B i) + Matrix.vecMulVec (B i) (A i))
    have hterm : ∑ i : Fin t, (Matrix.vecMulVec (A i) (B i) + Matrix.vecMulVec (B i) (A i)).rank ≤
        ∑ _i : Fin t, (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      have h1 := rank_add_le_aux (Matrix.vecMulVec (A i) (B i)) (Matrix.vecMulVec (B i) (A i))
      have h2 := rank_vecMulVec_le_one (A i) (B i)
      have h3 := rank_vecMulVec_le_one (B i) (A i)
      omega
    have hconst : ∑ _i : Fin t, (2 : ℕ) = 2 * t := by
      simp [mul_comm]
    dsimp only [M']
    exact le_trans hsum_le (le_trans hterm (le_of_eq hconst))

end PEqualNP.Outside.L_lib_484_aux

theorem PEqualNP.Outside.L_lib_484 : (∀ n : ℕ,
  let V := Fin n → ZMod 2
  ∀ (f : V → ZMod 2) (M : Matrix (Fin n) (Fin n) (ZMod 2)),
    (∀ x y : V, f (x+y) + f x + f y + f 0 = dotProduct x (M.mulVec y)) →
    ∀ t : ℕ, M.rank ≤ 2*t ↔
      ∃ (A B : Fin t → V) (c : V) (e : ZMod 2),
        ∀ x : V, f x = dotProduct c x + e +
          ∑ i : Fin t, dotProduct (A i) x * dotProduct (B i) x) := by
  intro n V f M hM t
  exact PEqualNP.Outside.L_lib_484_aux.main_core n f M hM t
