import PEqualNP.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace PEqualNP.Outside.L_lib_950_aux

private def red42 : ZMod 4 →+* ZMod 2 :=
  ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)

private lemma zmod4_cases (z : ZMod 4) : z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

private lemma zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma red42_eq_val (z : ZMod 4) : (z.val : ZMod 2) = red42 z := by
  rcases zmod4_cases z with rfl | rfl | rfl | rfl <;> decide

private lemma zmod4_even_iff (z : ZMod 4) : (z = 0 ∨ z = 2) ↔ red42 z = 0 := by
  rcases zmod4_cases z with rfl | rfl | rfl | rfl <;> decide

private lemma zmod4_killed_iff (z : ZMod 4) : (z + z = 0) ↔ (z = 0 ∨ z = 2) := by
  rcases zmod4_cases z with rfl | rfl | rfl | rfl <;> decide

private def half4 (z : ZMod 4) : ZMod 4 :=
  if z = 0 then 0 else 1

private lemma two_mul_half4 {z : ZMod 4} (hz : red42 z = 0) : 2 * half4 z = z := by
  rcases zmod4_cases z with rfl | rfl | rfl | rfl
  · decide
  · exact absurd hz (by decide)
  · decide
  · exact absurd hz (by decide)

private def lift2 (z : ZMod 2) : ZMod 4 :=
  if z = 0 then 0 else 2

private lemma lift2_red42 (z : ZMod 4) : lift2 (red42 z) = 2 * z := by
  rcases zmod4_cases z with rfl | rfl | rfl | rfl <;> decide

private def redMat {a b : ℕ} (M : Matrix (Fin a) (Fin b) (ZMod 4)) :
    Matrix (Fin a) (Fin b) (ZMod 2) :=
  fun i j => ((M i j).val : ZMod 2)

private lemma redMat_eq_map {a b : ℕ} (M : Matrix (Fin a) (Fin b) (ZMod 4)) :
    redMat M = M.map red42 := by
  ext i j
  exact red42_eq_val (M i j)

private lemma redMat_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) (ZMod 4))
    (B : Matrix (Fin b) (Fin c) (ZMod 4)) :
    redMat (A * B) = redMat A * redMat B := by
  rw [redMat_eq_map, redMat_eq_map, redMat_eq_map]
  exact Matrix.map_mul

private lemma redMat_one {a : ℕ} : redMat (1 : Matrix (Fin a) (Fin a) (ZMod 4)) = 1 := by
  rw [redMat_eq_map]
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

private lemma redMat_mulVec {a b : ℕ} (M : Matrix (Fin a) (Fin b) (ZMod 4))
    (x : Fin b → ZMod 4) :
    (fun i => red42 ((M.mulVec x) i)) = (redMat M).mulVec (fun j => red42 (x j)) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, redMat_eq_map, Matrix.map_apply]

private def swapMat {n : ℕ} (a b : Fin n) : Matrix (Fin n) (Fin n) (ZMod 4) :=
  Matrix.of fun i j => if j = Equiv.swap a b i then 1 else 0

private lemma swapMat_mul_self {n : ℕ} (a b : Fin n) :
    swapMat a b * swapMat a b = 1 := by
  ext i j
  simp only [Matrix.mul_apply, swapMat, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (Equiv.swap a b i)]
  · simp [Equiv.swap_apply_self]
    by_cases h : j = i
    · subst h; simp
    · have h' : i ≠ j := Ne.symm h
      simp [h, h']
  · intro k _ hk; simp [hk]
  · intro h; exact (h (Finset.mem_univ _)).elim

private lemma swapMat_mul_apply {n m : ℕ} (a b : Fin n) (M : Matrix (Fin n) (Fin m) (ZMod 4))
    (i : Fin n) (j : Fin m) :
    (swapMat a b * M) i j = M (Equiv.swap a b i) j := by
  simp only [Matrix.mul_apply, swapMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (Equiv.swap a b i)]
  · simp
  · intro k _ hk; simp [hk]
  · intro h; exact (h (Finset.mem_univ _)).elim

private lemma mul_swapMat_apply {n m : ℕ} (a b : Fin m) (M : Matrix (Fin n) (Fin m) (ZMod 4))
    (i : Fin n) (j : Fin m) :
    (M * swapMat a b) i j = M i (Equiv.swap a b j) := by
  simp only [Matrix.mul_apply, swapMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (Equiv.swap a b j)]
  · simp [Equiv.swap_apply_self]
  · intro k _ hk
    have hne : j ≠ Equiv.swap a b k := by
      intro heq
      apply hk
      rw [heq, Equiv.swap_apply_self]
    simp [hne]
  · intro h; exact (h (Finset.mem_univ _)).elim

private def scale0Mat {n : ℕ} (a : ZMod 4) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 4) :=
  Matrix.of fun i j => if i = j then (if i = 0 then a else 1) else 0

private lemma scale0Mat_mul_self {n : ℕ} {a : ZMod 4} (ha : a * a = 1) :
    scale0Mat (n := n) a * scale0Mat (n := n) a = 1 := by
  ext i j
  simp only [Matrix.mul_apply, scale0Mat, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single i]
  · by_cases hij : i = j
    · subst hij
      by_cases hi : i = 0 <;> simp [hi, ha]
    · simp [hij]
  · intro k _ hk; simp [Ne.symm hk]
  · intro h; exact (h (Finset.mem_univ _)).elim

private lemma scale0Mat_mul_apply {n m : ℕ} (a : ZMod 4) (M : Matrix (Fin (n + 1)) (Fin m) (ZMod 4))
    (i : Fin (n + 1)) (j : Fin m) :
    (scale0Mat (n := n) a * M) i j = (if i = 0 then a else 1) * M i j := by
  simp only [Matrix.mul_apply, scale0Mat, Matrix.of_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk; simp [Ne.symm hk]
  · intro h; exact (h (Finset.mem_univ _)).elim

private def rowElimMat {n : ℕ} (c : Fin n → ZMod 4) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 4) :=
  Matrix.of fun i j => (if i = j then 1 else 0) + (if j = 0 then Fin.cases 0 c i else 0)

private lemma rowElimMat_mul_neg {n : ℕ} (c : Fin n → ZMod 4) :
    rowElimMat c * rowElimMat (-c) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, rowElimMat, Matrix.of_apply, Matrix.one_apply, Fin.sum_univ_succ]
  cases i using Fin.cases with
  | zero =>
    simp only [Fin.cases_zero, Fin.succ_ne_zero, ↓reduceIte, add_zero]
    have hrest : ∑ x : Fin n,
        (if (0 : Fin (n + 1)) = x.succ then (1 : ZMod 4) else 0) *
        ((if x.succ = j then 1 else 0) + (if j = 0 then Fin.cases 0 (-c) x.succ else 0)) = 0 :=
      Finset.sum_eq_zero fun x _ => by simp [(Fin.succ_ne_zero x).symm]
    rw [hrest, add_zero]
    cases j using Fin.cases <;> simp
  | succ i' =>
    simp only [Fin.cases_succ]
    have hrest : ∑ k : Fin n,
        ((if i'.succ = k.succ then (1 : ZMod 4) else 0) + (if k.succ = 0 then c i' else 0)) *
        ((if k.succ = j then 1 else 0) + (if j = 0 then (-c) k else 0)) =
        (if i'.succ = j then 1 else 0) + (if j = 0 then -c i' else 0) := by
      rw [Finset.sum_eq_single i']
      · simp [Fin.succ_ne_zero]
      · intro k _ hk; simp [Fin.succ_inj, Ne.symm hk, Fin.succ_ne_zero]
      · intro h; exact (h (Finset.mem_univ _)).elim
    rw [hrest]
    cases j using Fin.cases with
    | zero => simp [Fin.succ_ne_zero]
    | succ j' =>
      by_cases hij : i' = j'
      · subst hij; simp [Fin.succ_ne_zero, (Fin.succ_ne_zero i').symm]
      · simp [Fin.succ_ne_zero, (Fin.succ_ne_zero j').symm, Fin.succ_inj, hij]

private lemma rowElimMat_mul_zero {n m : ℕ} (c : Fin n → ZMod 4)
    (M : Matrix (Fin (n + 1)) (Fin m) (ZMod 4)) (j : Fin m) :
    (rowElimMat c * M) 0 j = M 0 j := by
  simp only [Matrix.mul_apply, rowElimMat, Matrix.of_apply, Fin.cases_zero]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk; simp [Ne.symm hk]
  · intro h; exact (h (Finset.mem_univ _)).elim

private lemma rowElimMat_mul_succ {n m : ℕ} (c : Fin n → ZMod 4)
    (M : Matrix (Fin (n + 1)) (Fin m) (ZMod 4)) (i : Fin n) (j : Fin m) :
    (rowElimMat c * M) i.succ j = M i.succ j + c i * M 0 j := by
  simp only [Matrix.mul_apply, rowElimMat, Matrix.of_apply, Fin.cases_succ, Fin.sum_univ_succ]
  have hrest : ∑ k : Fin n,
      ((if i.succ = k.succ then (1 : ZMod 4) else 0) + (if k.succ = 0 then c i else 0)) * M k.succ j =
      M i.succ j := by
    rw [Finset.sum_eq_single i]
    · simp [Fin.succ_ne_zero]
    · intro k _ hk; simp [Fin.succ_inj, Ne.symm hk, Fin.succ_ne_zero]
    · intro h; exact (h (Finset.mem_univ _)).elim
  rw [hrest]
  simp [Fin.succ_ne_zero, add_comm]

private def colElimMat {m : ℕ} (c : Fin m → ZMod 4) : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 4) :=
  Matrix.of fun i j => (if i = j then 1 else 0) + (if i = 0 then Fin.cases 0 c j else 0)

private lemma colElimMat_mul_neg {m : ℕ} (c : Fin m → ZMod 4) :
    colElimMat c * colElimMat (-c) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, colElimMat, Matrix.of_apply, Matrix.one_apply, Fin.sum_univ_succ]
  cases j using Fin.cases with
  | zero =>
    have hrest : ∑ k : Fin m,
        ((if i = k.succ then (1 : ZMod 4) else 0) + (if i = 0 then Fin.cases 0 c k.succ else 0)) *
        ((if k.succ = 0 then 1 else 0) + (if k.succ = 0 then 0 else 0)) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [Fin.succ_ne_zero]
    simp only [Fin.cases_zero]
    rw [hrest, add_zero]
    cases i using Fin.cases <;> simp [Fin.succ_ne_zero]
  | succ j' =>
    simp only [Fin.cases_succ]
    have hrest : ∑ k : Fin m,
        ((if i = k.succ then (1 : ZMod 4) else 0) + (if i = 0 then c k else 0)) *
        ((if k.succ = j'.succ then 1 else 0) + (if k.succ = 0 then (-c) j' else 0)) =
        (if i = j'.succ then 1 else 0) + (if i = 0 then c j' else 0) := by
      rw [Finset.sum_eq_single j']
      · simp [Fin.succ_ne_zero]
      · intro k _ hk; simp [Fin.succ_inj, hk, Fin.succ_ne_zero]
      · intro h; exact (h (Finset.mem_univ _)).elim
    rw [hrest]
    cases i using Fin.cases with
    | zero => simp [(Fin.succ_ne_zero j').symm]
    | succ i' =>
      by_cases hij : i' = j'
      · subst hij; simp [Fin.succ_ne_zero]
      · simp [Fin.succ_ne_zero, Fin.succ_inj, hij]

private lemma mul_colElimMat_zero {n m : ℕ} (c : Fin m → ZMod 4)
    (M : Matrix (Fin n) (Fin (m + 1)) (ZMod 4)) (i : Fin n) :
    (M * colElimMat c) i 0 = M i 0 := by
  simp only [Matrix.mul_apply, colElimMat, Matrix.of_apply, Fin.cases_zero]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk; simp [hk]
  · intro h; exact (h (Finset.mem_univ _)).elim

private lemma mul_colElimMat_succ {n m : ℕ} (c : Fin m → ZMod 4)
    (M : Matrix (Fin n) (Fin (m + 1)) (ZMod 4)) (i : Fin n) (j : Fin m) :
    (M * colElimMat c) i j.succ = M i j.succ + M i 0 * c j := by
  simp only [Matrix.mul_apply, colElimMat, Matrix.of_apply, Fin.cases_succ, Fin.sum_univ_succ]
  have hrest : ∑ k : Fin m,
      M i k.succ * ((if k.succ = j.succ then (1 : ZMod 4) else 0) + (if k.succ = 0 then c j else 0)) =
      M i j.succ := by
    rw [Finset.sum_eq_single j]
    · simp [Fin.succ_ne_zero]
    · intro k _ hk; simp [Fin.succ_inj, hk, Fin.succ_ne_zero]
    · intro h; exact (h (Finset.mem_univ _)).elim
  rw [hrest]
  simp [(Fin.succ_ne_zero j).symm, add_comm]

private def block1 {n : ℕ} (P : Matrix (Fin n) (Fin n) (ZMod 4)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod 4) :=
  Matrix.of fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => P i' j') j) i

private lemma block1_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) (ZMod 4)) :
    block1 A * block1 B = block1 (A * B) := by
  ext i j
  simp only [Matrix.mul_apply, block1, Matrix.of_apply, Fin.sum_univ_succ]
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases <;> simp
  | succ i' =>
    cases j using Fin.cases <;> simp

private lemma block1_one {n : ℕ} : block1 (1 : Matrix (Fin n) (Fin n) (ZMod 4)) = 1 := by
  ext i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => simp [block1, Matrix.one_apply]
    | succ j' => simp [block1, Matrix.one_apply, (Fin.succ_ne_zero j').symm]
  | succ i' =>
    cases j using Fin.cases with
    | zero => simp [block1, Matrix.one_apply, Fin.succ_ne_zero]
    | succ j' => simp [block1, Matrix.one_apply, Fin.succ_inj]

private lemma block1_mul_diag {n m : ℕ} (P : Matrix (Fin n) (Fin n) (ZMod 4))
    (Q : Matrix (Fin m) (Fin m) (ZMod 4))
    (M : Matrix (Fin (n + 1)) (Fin (m + 1)) (ZMod 4))
    (hcol : ∀ i : Fin n, M i.succ 0 = 0) (hrow : ∀ j : Fin m, M 0 j.succ = 0) :
    (block1 P * M * block1 Q) 0 0 = M 0 0 ∧
    (∀ i : Fin n, (block1 P * M * block1 Q) i.succ 0 = 0) ∧
    (∀ j : Fin m, (block1 P * M * block1 Q) 0 j.succ = 0) ∧
    (∀ (i : Fin n) (j : Fin m),
      (block1 P * M * block1 Q) i.succ j.succ =
        (P * (Matrix.of fun (a : Fin n) (b : Fin m) => M a.succ b.succ) * Q) i j) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [Matrix.mul_apply, Fin.sum_univ_succ, block1]
  · intro i
    simp [Matrix.mul_apply, Fin.sum_univ_succ, block1, hcol]
  · intro j
    simp [Matrix.mul_apply, Fin.sum_univ_succ, block1, hrow]
  · intro i j
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, block1, Matrix.of_apply, Fin.cases_zero,
      Fin.cases_succ, mul_zero, zero_mul, zero_add]

private def diagUV (n m u v : ℕ) : Matrix (Fin n) (Fin m) (ZMod 4) :=
  Matrix.of fun i j =>
    if i.val = j.val then (if i.val < u then 1 else if i.val < u + v then 2 else 0) else 0

private lemma even_mul_even {a b c : ℕ} (A : Matrix (Fin a) (Fin b) (ZMod 4))
    (B : Matrix (Fin b) (Fin c) (ZMod 4))
    (hB : ∀ i j, red42 (B i j) = 0) (i : Fin a) (j : Fin c) :
    red42 ((A * B) i j) = 0 := by
  simp only [Matrix.mul_apply, map_sum, map_mul]
  exact Finset.sum_eq_zero fun k _ => by rw [hB k j, mul_zero]

private lemma even_mul_right {a b c : ℕ} (A : Matrix (Fin a) (Fin b) (ZMod 4))
    (B : Matrix (Fin b) (Fin c) (ZMod 4))
    (hA : ∀ i j, red42 (A i j) = 0) (i : Fin a) (j : Fin c) :
    red42 ((A * B) i j) = 0 := by
  simp only [Matrix.mul_apply, map_sum, map_mul]
  exact Finset.sum_eq_zero fun k _ => by rw [hA i k, zero_mul]

private lemma snf_zmod4 : ∀ (n m : ℕ) (G : Matrix (Fin n) (Fin m) (ZMod 4)),
    ∃ (u v : ℕ) (P P' : Matrix (Fin n) (Fin n) (ZMod 4))
      (Q Q' : Matrix (Fin m) (Fin m) (ZMod 4)),
      u + v ≤ n ∧ u + v ≤ m ∧
      P * P' = 1 ∧ P' * P = 1 ∧ Q * Q' = 1 ∧ Q' * Q = 1 ∧
      P * G * Q = diagUV n m u v := by
  intro n
  induction n with
  | zero =>
    intro m G
    refine ⟨0, 0, 1, 1, 1, 1, Nat.zero_le _, Nat.zero_le _, by simp, by simp, by simp, by simp, ?_⟩
    ext i; exact Fin.elim0 i
  | succ n ih =>
    intro m G
    cases m with
    | zero =>
      refine ⟨0, 0, 1, 1, 1, 1, Nat.zero_le _, Nat.zero_le _, by simp, by simp, by simp, by simp, ?_⟩
      ext _ j; exact Fin.elim0 j
    | succ m =>
      by_cases hunit : ∃ (i₀ : Fin (n + 1)) (j₀ : Fin (m + 1)), G i₀ j₀ = 1 ∨ G i₀ j₀ = 3
      · obtain ⟨i₀, j₀, hval⟩ := hunit
        let a := G i₀ j₀
        have ha2 : a * a = 1 := by
          rcases hval with h1 | h3
          · change G i₀ j₀ * G i₀ j₀ = 1; rw [h1]; decide
          · change G i₀ j₀ * G i₀ j₀ = 1; rw [h3]; decide
        let Er := swapMat (0 : Fin (n + 1)) i₀
        let Ec := swapMat (0 : Fin (m + 1)) j₀
        let Sa := scale0Mat (n := n) a
        let G1 := Sa * (Er * G * Ec)
        have hG1_00 : G1 0 0 = 1 := by
          dsimp only [G1, Sa, Er, Ec]
          rw [scale0Mat_mul_apply, mul_swapMat_apply, swapMat_mul_apply]
          simp [Equiv.swap_apply_left, a, ha2]
        let cr : Fin n → ZMod 4 := fun i => -G1 i.succ 0
        let L := rowElimMat cr
        let L' := rowElimMat (-cr)
        let G2 := L * G1
        have hG2_00 : G2 0 0 = 1 := by
          rw [show G2 0 0 = G1 0 0 from rowElimMat_mul_zero cr G1 0, hG1_00]
        have hG2_col : ∀ i : Fin n, G2 i.succ 0 = 0 := by
          intro i
          rw [show G2 i.succ 0 = G1 i.succ 0 + cr i * G1 0 0 from rowElimMat_mul_succ cr G1 i 0,
            hG1_00]
          simp [cr]
        let cc : Fin m → ZMod 4 := fun j => -G2 0 j.succ
        let R := colElimMat cc
        let R' := colElimMat (-cc)
        let G3 := G2 * R
        have hG3_00 : G3 0 0 = 1 := by
          rw [show G3 0 0 = G2 0 0 from mul_colElimMat_zero cc G2 0, hG2_00]
        have hG3_col : ∀ i : Fin n, G3 i.succ 0 = 0 := by
          intro i
          rw [show G3 i.succ 0 = G2 i.succ 0 from mul_colElimMat_zero cc G2 i.succ, hG2_col i]
        have hG3_row : ∀ j : Fin m, G3 0 j.succ = 0 := by
          intro j
          rw [show G3 0 j.succ = G2 0 j.succ + G2 0 0 * cc j from mul_colElimMat_succ cc G2 0 j,
            hG2_00]
          simp [cc]
        let Gsub : Matrix (Fin n) (Fin m) (ZMod 4) := Matrix.of fun i j => G3 i.succ j.succ
        obtain ⟨u', v', P1, P1', Q1, Q1', huvn, huvm, hPP1, hPP1', hQQ1, hQQ1', hD1⟩ := ih m Gsub
        let P := block1 P1 * L * Sa * Er
        let P' := Er * Sa * L' * block1 P1'
        let Q := Ec * R * block1 Q1
        let Q' := block1 Q1' * R' * Ec
        have hEr2 : Er * Er = 1 := swapMat_mul_self 0 i₀
        have hEc2 : Ec * Ec = 1 := swapMat_mul_self 0 j₀
        have hSa2 : Sa * Sa = 1 := scale0Mat_mul_self ha2
        have hLL' : L * L' = 1 := rowElimMat_mul_neg cr
        have hL'L : L' * L = 1 := by
          have := rowElimMat_mul_neg (-cr); simpa [L, L'] using this
        have hRR' : R * R' = 1 := colElimMat_mul_neg cc
        have hR'R : R' * R = 1 := by
          have := colElimMat_mul_neg (-cc); simpa [R, R'] using this
        have hB1P : block1 P1 * block1 P1' = 1 := by rw [block1_mul, hPP1, block1_one]
        have hB1P' : block1 P1' * block1 P1 = 1 := by rw [block1_mul, hPP1', block1_one]
        have hB1Q : block1 Q1 * block1 Q1' = 1 := by rw [block1_mul, hQQ1, block1_one]
        have hB1Q' : block1 Q1' * block1 Q1 = 1 := by rw [block1_mul, hQQ1', block1_one]
        have hPP' : P * P' = 1 := by
          calc P * P' = block1 P1 * L * Sa * (Er * Er) * Sa * L' * block1 P1' := by
                simp only [P, P', Matrix.mul_assoc]
            _ = block1 P1 * L * (Sa * Sa) * L' * block1 P1' := by
                rw [hEr2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
            _ = block1 P1 * (L * L') * block1 P1' := by
                rw [hSa2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
            _ = 1 := by rw [hLL', Matrix.mul_one, hB1P]
        have hP'P : P' * P = 1 := by
          calc P' * P = Er * Sa * L' * (block1 P1' * block1 P1) * L * Sa * Er := by
                simp only [P, P', Matrix.mul_assoc]
            _ = Er * Sa * (L' * L) * Sa * Er := by
                rw [hB1P', Matrix.mul_one]; simp only [Matrix.mul_assoc]
            _ = Er * (Sa * Sa) * Er := by
                rw [hL'L, Matrix.mul_one]; simp only [Matrix.mul_assoc]
            _ = 1 := by rw [hSa2, Matrix.mul_one, hEr2]
        have hQQ' : Q * Q' = 1 := by
          calc Q * Q' = Ec * R * (block1 Q1 * block1 Q1') * R' * Ec := by
                simp only [Q, Q', Matrix.mul_assoc]
            _ = Ec * (R * R') * Ec := by
                rw [hB1Q, Matrix.mul_one]; simp only [Matrix.mul_assoc]
            _ = 1 := by rw [hRR', Matrix.mul_one, hEc2]
        have hQ'Q : Q' * Q = 1 := by
          calc Q' * Q = block1 Q1' * R' * (Ec * Ec) * R * block1 Q1 := by
                simp only [Q, Q', Matrix.mul_assoc]
            _ = block1 Q1' * (R' * R) * block1 Q1 := by
                rw [hEc2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
            _ = 1 := by rw [hR'R, Matrix.mul_one, hB1Q']
        have hPGQ : P * G * Q = block1 P1 * G3 * block1 Q1 := by
          simp only [P, Q, G3, G2, G1, Matrix.mul_assoc]
        obtain ⟨hd00, hdcol, hdrow, hdsub⟩ := block1_mul_diag P1 Q1 G3 hG3_col hG3_row
        refine ⟨u' + 1, v', P, P', Q, Q', by omega, by omega, hPP', hP'P, hQQ', hQ'Q, ?_⟩
        rw [hPGQ]
        ext i j
        cases i using Fin.cases with
        | zero =>
          cases j using Fin.cases with
          | zero => rw [hd00, hG3_00]; simp [diagUV]
          | succ j' => rw [hdrow j']; simp [diagUV]
        | succ i' =>
          cases j using Fin.cases with
          | zero => rw [hdcol i']; simp [diagUV]
          | succ j' =>
            rw [hdsub i' j', hD1]
            simp only [diagUV, Matrix.of_apply, Fin.val_succ, Nat.add_right_cancel_iff]
            by_cases h1 : i'.val = j'.val
            · simp only [h1, ↓reduceIte]
              have hc1 : (j'.val + 1 < u' + 1) ↔ (j'.val < u') := by omega
              have hc2 : (j'.val + 1 < u' + 1 + v') ↔ (j'.val < u' + v') := by omega
              simp only [hc1, hc2]
            · simp [h1]
      · have hevenG : ∀ i j, red42 (G i j) = 0 := by
          intro i j
          rcases zmod4_cases (G i j) with h0 | h1 | h2 | h3
          · rw [h0]; decide
          · exact (hunit ⟨i, j, Or.inl h1⟩).elim
          · rw [h2]; decide
          · exact (hunit ⟨i, j, Or.inr h3⟩).elim
        by_cases hzero : ∀ i j, G i j = 0
        · refine ⟨0, 0, 1, 1, 1, 1, Nat.zero_le _, Nat.zero_le _, by simp, by simp, by simp, by simp, ?_⟩
          ext i j
          simp [diagUV, hzero i j]
        · have hex2 : ∃ (i₀ : Fin (n + 1)) (j₀ : Fin (m + 1)), G i₀ j₀ = 2 := by
            by_contra hall
            apply hzero
            intro i j
            rcases (zmod4_even_iff (G i j)).mpr (hevenG i j) with h0 | h2
            · exact h0
            · exact (hall ⟨i, j, h2⟩).elim
          obtain ⟨i₀, j₀, hG20⟩ := hex2
          let Er := swapMat (0 : Fin (n + 1)) i₀
          let Ec := swapMat (0 : Fin (m + 1)) j₀
          let G1 := Er * G * Ec
          have hevenG1 : ∀ i j, red42 (G1 i j) = 0 :=
            fun i j => even_mul_right (Er * G) Ec (fun a b => even_mul_even Er G hevenG a b) i j
          have hG1_00 : G1 0 0 = 2 := by
            dsimp only [G1, Er, Ec]
            rw [mul_swapMat_apply, swapMat_mul_apply]
            simpa [Equiv.swap_apply_left] using hG20
          let cr : Fin n → ZMod 4 := fun i => if G1 i.succ 0 = 0 then 0 else -1
          let L := rowElimMat cr
          let L' := rowElimMat (-cr)
          let G2 := L * G1
          have hevenG2 : ∀ i j, red42 (G2 i j) = 0 := fun i j => even_mul_even L G1 hevenG1 i j
          have hG2_00 : G2 0 0 = 2 := by
            rw [show G2 0 0 = G1 0 0 from rowElimMat_mul_zero cr G1 0, hG1_00]
          have hG2_col : ∀ i : Fin n, G2 i.succ 0 = 0 := by
            intro i
            rw [show G2 i.succ 0 = G1 i.succ 0 + cr i * G1 0 0 from rowElimMat_mul_succ cr G1 i 0,
              hG1_00]
            rcases (zmod4_even_iff (G1 i.succ 0)).mpr (hevenG1 i.succ 0) with h0 | h2
            · simp [cr, h0]
            · simp [cr, h2]
              decide
          let cc : Fin m → ZMod 4 := fun j => if G2 0 j.succ = 0 then 0 else -1
          let R := colElimMat cc
          let R' := colElimMat (-cc)
          let G3 := G2 * R
          have hevenG3 : ∀ i j, red42 (G3 i j) = 0 := fun i j => even_mul_right G2 R hevenG2 i j
          have hG3_00 : G3 0 0 = 2 := by
            rw [show G3 0 0 = G2 0 0 from mul_colElimMat_zero cc G2 0, hG2_00]
          have hG3_col : ∀ i : Fin n, G3 i.succ 0 = 0 := by
            intro i
            rw [show G3 i.succ 0 = G2 i.succ 0 from mul_colElimMat_zero cc G2 i.succ, hG2_col i]
          have hG3_row : ∀ j : Fin m, G3 0 j.succ = 0 := by
            intro j
            rw [show G3 0 j.succ = G2 0 j.succ + G2 0 0 * cc j from mul_colElimMat_succ cc G2 0 j,
              hG2_00]
            rcases (zmod4_even_iff (G2 0 j.succ)).mpr (hevenG2 0 j.succ) with h0 | h2
            · simp [cc, h0]
            · simp [cc, h2]
              decide
          let Gsub : Matrix (Fin n) (Fin m) (ZMod 4) := Matrix.of fun i j => G3 i.succ j.succ
          have hevenSub : ∀ i j, red42 (Gsub i j) = 0 := fun i j => hevenG3 i.succ j.succ
          obtain ⟨u', v', P1, P1', Q1, Q1', huvn, huvm, hPP1, hPP1', hQQ1, hQQ1', hD1⟩ := ih m Gsub
          have hu'0 : u' = 0 := by
            by_contra hne
            have hlt1 : 0 < u' := Nat.pos_of_ne_zero hne
            have h0n : 0 < n := by omega
            have h0m : 0 < m := by omega
            have hev := even_mul_right (P1 * Gsub) Q1 (fun a b => even_mul_even P1 Gsub hevenSub a b)
              ⟨0, h0n⟩ ⟨0, h0m⟩
            rw [hD1] at hev
            simp only [diagUV, Matrix.of_apply, hlt1, ↓reduceIte] at hev
            exact (by decide : red42 1 ≠ 0) hev
          subst hu'0
          let P := block1 P1 * L * Er
          let P' := Er * L' * block1 P1'
          let Q := Ec * R * block1 Q1
          let Q' := block1 Q1' * R' * Ec
          have hEr2 : Er * Er = 1 := swapMat_mul_self 0 i₀
          have hEc2 : Ec * Ec = 1 := swapMat_mul_self 0 j₀
          have hLL' : L * L' = 1 := rowElimMat_mul_neg cr
          have hL'L : L' * L = 1 := by
            have := rowElimMat_mul_neg (-cr); simpa [L, L'] using this
          have hRR' : R * R' = 1 := colElimMat_mul_neg cc
          have hR'R : R' * R = 1 := by
            have := colElimMat_mul_neg (-cc); simpa [R, R'] using this
          have hB1P : block1 P1 * block1 P1' = 1 := by rw [block1_mul, hPP1, block1_one]
          have hB1P' : block1 P1' * block1 P1 = 1 := by rw [block1_mul, hPP1', block1_one]
          have hB1Q : block1 Q1 * block1 Q1' = 1 := by rw [block1_mul, hQQ1, block1_one]
          have hB1Q' : block1 Q1' * block1 Q1 = 1 := by rw [block1_mul, hQQ1', block1_one]
          have hPP' : P * P' = 1 := by
            calc P * P' = block1 P1 * L * (Er * Er) * L' * block1 P1' := by
                  simp only [P, P', Matrix.mul_assoc]
              _ = block1 P1 * (L * L') * block1 P1' := by
                  rw [hEr2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
              _ = 1 := by rw [hLL', Matrix.mul_one, hB1P]
          have hP'P : P' * P = 1 := by
            calc P' * P = Er * L' * (block1 P1' * block1 P1) * L * Er := by
                  simp only [P, P', Matrix.mul_assoc]
              _ = Er * (L' * L) * Er := by
                  rw [hB1P', Matrix.mul_one]; simp only [Matrix.mul_assoc]
              _ = 1 := by rw [hL'L, Matrix.mul_one, hEr2]
          have hQQ' : Q * Q' = 1 := by
            calc Q * Q' = Ec * R * (block1 Q1 * block1 Q1') * R' * Ec := by
                  simp only [Q, Q', Matrix.mul_assoc]
              _ = Ec * (R * R') * Ec := by
                  rw [hB1Q, Matrix.mul_one]; simp only [Matrix.mul_assoc]
              _ = 1 := by rw [hRR', Matrix.mul_one, hEc2]
          have hQ'Q : Q' * Q = 1 := by
            calc Q' * Q = block1 Q1' * R' * (Ec * Ec) * R * block1 Q1 := by
                  simp only [Q, Q', Matrix.mul_assoc]
              _ = block1 Q1' * (R' * R) * block1 Q1 := by
                  rw [hEc2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
              _ = 1 := by rw [hR'R, Matrix.mul_one, hB1Q']
          have hPGQ : P * G * Q = block1 P1 * G3 * block1 Q1 := by
            simp only [P, Q, G3, G2, G1, Matrix.mul_assoc]
          obtain ⟨hd00, hdcol, hdrow, hdsub⟩ := block1_mul_diag P1 Q1 G3 hG3_col hG3_row
          refine ⟨0, v' + 1, P, P', Q, Q', by omega, by omega, hPP', hP'P, hQQ', hQ'Q, ?_⟩
          rw [hPGQ]
          ext i j
          cases i using Fin.cases with
          | zero =>
            cases j using Fin.cases with
            | zero => rw [hd00, hG3_00]; simp [diagUV]
            | succ j' => rw [hdrow j']; simp [diagUV]
          | succ i' =>
            cases j using Fin.cases with
            | zero => rw [hdcol i']; simp [diagUV]
            | succ j' =>
              rw [hdsub i' j', hD1]
              simp only [diagUV, Matrix.of_apply, Fin.val_succ, Nat.add_right_cancel_iff]
              by_cases h1 : i'.val = j'.val
              · simp only [h1, ↓reduceIte]
                have hc2 : (j'.val + 1 < 0 + (v' + 1)) ↔ (j'.val < 0 + v') := by omega
                simp only [hc2]
                have hnot0 : ¬(j'.val + 1 < 0) := by omega
                have hnot0' : ¬(j'.val < 0) := by omega
                simp only [hnot0, hnot0', ↓reduceIte]
              · simp [h1]

private lemma rank_diag_mask (n m : ℕ) (S : Finset ℕ)
    (hSn : ∀ k ∈ S, k < n) (hSm : ∀ k ∈ S, k < m) :
    Matrix.rank (Matrix.of (fun (i : Fin n) (j : Fin m) =>
      if i.val = j.val ∧ i.val ∈ S then (1 : ZMod 2) else 0)) = S.card := by
  let M : Matrix (Fin n) (Fin m) (ZMod 2) :=
    Matrix.of fun i j => if i.val = j.val ∧ i.val ∈ S then 1 else 0
  have hmulVec : ∀ (x : Fin m → ZMod 2) (i : Fin n),
      M.mulVec x i = if h : i.val ∈ S then x ⟨i.val, hSm i.val h⟩ else 0 := by
    intro x i
    simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply]
    by_cases hi : i.val ∈ S
    · rw [dif_pos hi]
      rw [Finset.sum_eq_single ⟨i.val, hSm i.val hi⟩]
      · simp [hi]
      · intro j _ hj
        have hne : i.val ≠ j.val := fun h => hj (Fin.ext h.symm)
        simp [hne]
      · intro h; exact (h (Finset.mem_univ _)).elim
    · rw [dif_neg hi]
      apply Finset.sum_eq_zero; intro j _; simp [hi]
  let eqv : (S → ZMod 2) ≃ₗ[ZMod 2] LinearMap.range M.mulVecLin :=
    { toFun := fun f =>
        ⟨fun i => if hi : i.val ∈ S then f ⟨i.val, hi⟩ else 0,
         ⟨fun j => if hj : j.val ∈ S then f ⟨j.val, hj⟩ else 0, by
            ext i; change M.mulVec _ i = _; rw [hmulVec]
            by_cases hi : i.val ∈ S
            · simp [dif_pos hi]
            · simp [dif_neg hi]⟩⟩
      invFun := fun y s => y.1 ⟨s.1, hSn s.1 s.2⟩
      map_add' := fun f g => by
        apply Subtype.ext; ext i
        by_cases hi : i.val ∈ S <;> simp [hi]
      map_smul' := fun c f => by
        apply Subtype.ext; ext i
        by_cases hi : i.val ∈ S <;> simp [hi]
      left_inv := fun f => by
        ext ⟨s, hs⟩; simp [hs]
      right_inv := fun y => by
        apply Subtype.ext; ext i
        rcases y.2 with ⟨x, hx⟩
        change (if hi : i.val ∈ S then y.1 ⟨i.val, hSn i.val hi⟩ else 0) = y.1 i
        by_cases hi : i.val ∈ S
        · simp [dif_pos hi]
        · rw [dif_neg hi, ← hx]
          change 0 = M.mulVec x i
          rw [hmulVec, dif_neg hi] }
  change Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) = S.card
  rw [← eqv.finrank_eq, Module.finrank_pi, Fintype.card_coe]

private lemma rank_redMat_inv {n m : ℕ}
    (P P' : Matrix (Fin n) (Fin n) (ZMod 4))
    (Q Q' : Matrix (Fin m) (Fin m) (ZMod 4))
    (G : Matrix (Fin n) (Fin m) (ZMod 4))
    (hPP' : P * P' = 1) (hP'P : P' * P = 1)
    (hQQ' : Q * Q' = 1) (hQ'Q : Q' * Q = 1) :
    Matrix.rank (redMat (P * G * Q)) = Matrix.rank (redMat G) := by
  have h1 : Matrix.rank (redMat (P * G * Q)) ≤ Matrix.rank (redMat G) := by
    rw [redMat_mul, redMat_mul]
    exact le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)
  have h2 : Matrix.rank (redMat G) ≤ Matrix.rank (redMat (P * G * Q)) := by
    have hG : G = P' * (P * G * Q) * Q' := by
      calc G = (1 : Matrix (Fin n) (Fin n) (ZMod 4)) * G * (1 : Matrix (Fin m) (Fin m) (ZMod 4)) := by
            rw [Matrix.one_mul, Matrix.mul_one]
        _ = (P' * P) * G * (Q * Q') := by rw [hP'P, hQQ']
        _ = P' * (P * G * Q) * Q' := by simp only [Matrix.mul_assoc]
    conv_lhs => rw [hG]
    rw [redMat_mul, redMat_mul]
    exact le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)
  exact le_antisymm h1 h2

private lemma outputs_killed_inv {n m : ℕ}
    (P P' : Matrix (Fin n) (Fin n) (ZMod 4))
    (Q Q' : Matrix (Fin m) (Fin m) (ZMod 4))
    (G : Matrix (Fin n) (Fin m) (ZMod 4))
    (hPP' : P * P' = 1) (hP'P : P' * P = 1)
    (hQQ' : Q * Q' = 1) (hQ'Q : Q' * Q = 1) :
    (Finset.univ.image (fun x : Fin m → ZMod 4 => (P * G * Q).mulVec x)).card =
      (Finset.univ.image (fun x : Fin m → ZMod 4 => G.mulVec x)).card ∧
    ((Finset.univ.image (fun x : Fin m → ZMod 4 => (P * G * Q).mulVec x)).filter
      (fun y => ∀ i, y i + y i = 0)).card =
    ((Finset.univ.image (fun x : Fin m → ZMod 4 => G.mulVec x)).filter
      (fun y => ∀ i, y i + y i = 0)).card := by
  have hP_inj : Function.Injective (fun y : Fin n → ZMod 4 => P.mulVec y) := by
    intro y₁ y₂ h
    have h' := congr_arg P'.mulVec h
    simpa [Matrix.mulVec_mulVec, hP'P] using h'
  have hImg : Finset.univ.image (fun x : Fin m → ZMod 4 => (P * G * Q).mulVec x) =
      (Finset.univ.image (fun x : Fin m → ZMod 4 => G.mulVec x)).image (fun y => P.mulVec y) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨G.mulVec (Q.mulVec x), ⟨Q.mulVec x, rfl⟩, ?_⟩
      simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨Q'.mulVec x, ?_⟩
      simp [Matrix.mulVec_mulVec, Matrix.mul_assoc, hQQ']
  have hKill : ∀ z : Fin n → ZMod 4,
      (∀ i, (P.mulVec z) i + (P.mulVec z) i = 0) ↔ (∀ i, z i + z i = 0) := by
    intro z
    have hadd : (fun i => (P.mulVec z) i + (P.mulVec z) i) = P.mulVec (z + z) := by
      rw [Matrix.mulVec_add]; rfl
    constructor
    · intro h i
      have h0 : P.mulVec (z + z) = P.mulVec 0 := by
        rw [← hadd, Matrix.mulVec_zero]; ext j; exact h j
      have hz0 := hP_inj h0
      exact congr_fun hz0 i
    · intro h i
      have hz0 : z + z = 0 := funext h
      have := congr_fun hadd i
      rw [this, hz0, Matrix.mulVec_zero]; rfl
  constructor
  · rw [hImg, Finset.card_image_of_injective _ hP_inj]
  · rw [hImg]
    have hfilt : ((Finset.univ.image (fun x : Fin m → ZMod 4 => G.mulVec x)).image (fun y => P.mulVec y)).filter
        (fun y => ∀ i, y i + y i = 0) =
        ((Finset.univ.image (fun x : Fin m → ZMod 4 => G.mulVec x)).filter
          (fun y => ∀ i, y i + y i = 0)).image (fun y => P.mulVec y) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hk⟩
        exact ⟨z, ⟨hz, (hKill z).mp hk⟩, rfl⟩
      · rintro ⟨z, ⟨hz, hk⟩, rfl⟩
        exact ⟨⟨z, hz, rfl⟩, (hKill z).mpr hk⟩
    rw [hfilt, Finset.card_image_of_injective _ hP_inj]

private lemma diagUV_invariants {n m u v : ℕ} (hun : u + v ≤ n) (hum : u + v ≤ m) :
    Matrix.rank (redMat (diagUV n m u v)) = u ∧
    (Finset.univ.image (fun x : Fin m → ZMod 4 => (diagUV n m u v).mulVec x)).card = 2 ^ (2 * u + v) ∧
    ((Finset.univ.image (fun x : Fin m → ZMod 4 => (diagUV n m u v).mulVec x)).filter
      (fun y => ∀ i, y i + y i = 0)).card = 2 ^ (u + v) := by
  let D := diagUV n m u v
  have hmul : ∀ (x : Fin m → ZMod 4) (i : Fin n),
      D.mulVec x i =
        if h1 : i.val < u then x ⟨i.val, by omega⟩
        else if h2 : i.val < u + v then 2 * x ⟨i.val, by omega⟩
        else 0 := by
    intro x i
    simp only [Matrix.mulVec, dotProduct, D, diagUV, Matrix.of_apply]
    by_cases h1 : i.val < u
    · rw [dif_pos h1, Finset.sum_eq_single ⟨i.val, by omega⟩]
      · simp [h1]
      · intro j _ hj; have hne : i.val ≠ j.val := fun h => hj (Fin.ext h.symm); simp [hne]
      · intro h; exact (h (Finset.mem_univ _)).elim
    · rw [dif_neg h1]
      by_cases h2 : i.val < u + v
      · rw [dif_pos h2, Finset.sum_eq_single ⟨i.val, by omega⟩]
        · simp [h1, h2]
        · intro j _ hj; have hne : i.val ≠ j.val := fun h => hj (Fin.ext h.symm); simp [hne]
        · intro h; exact (h (Finset.mem_univ _)).elim
      · rw [dif_neg h2]
        apply Finset.sum_eq_zero; intro j _
        by_cases heq : i.val = j.val
        · rw [if_pos heq, if_neg h1, if_neg h2, zero_mul]
        · simp [heq]
  have hrank : Matrix.rank (redMat D) = u := by
    have hred : redMat D = Matrix.of (fun (i : Fin n) (j : Fin m) =>
        if i.val = j.val ∧ i.val ∈ Finset.range u then (1 : ZMod 2) else 0) := by
      ext i j
      rw [redMat_eq_map]
      simp only [D, diagUV, Matrix.map_apply, Matrix.of_apply, Finset.mem_range]
      by_cases hij : i.val = j.val
      · rw [if_pos hij]
        simp only [hij, true_and]
        by_cases hu : j.val < u
        · rw [if_pos hu, if_pos hu]; simp
        · rw [if_neg hu, if_neg hu]
          by_cases huv : j.val < u + v
          · rw [if_pos huv]; decide
          · rw [if_neg huv]; simp
      · simp [hij]
    rw [hred, rank_diag_mask n m (Finset.range u) (fun k hk => by simp at hk; omega)
      (fun k hk => by simp at hk; omega), Finset.card_range]
  let outD := Finset.univ.image (fun x : Fin m → ZMod 4 => D.mulVec x)
  have hout_mem : ∀ y : Fin n → ZMod 4, y ∈ outD ↔
      (∀ i : Fin n, u ≤ i.val → i.val < u + v → y i = 0 ∨ y i = 2) ∧
      (∀ i : Fin n, u + v ≤ i.val → y i = 0) := by
    intro y
    simp only [outD, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨fun i hu huv => ?_, fun i huv => ?_⟩
      · rw [hmul x i, dif_neg (by omega), dif_pos huv]
        rcases zmod4_cases (x ⟨i.val, by omega⟩) with h | h | h | h <;> rw [h] <;> decide
      · rw [hmul x i, dif_neg (by omega), dif_neg (by omega)]
    · rintro ⟨hmid, htail⟩
      refine ⟨fun j => if h1 : j.val < u then y ⟨j.val, by omega⟩
        else if h2 : j.val < u + v then half4 (y ⟨j.val, by omega⟩) else 0, ?_⟩
      ext i
      rw [hmul]
      by_cases h1 : i.val < u
      · simp [dif_pos h1]
      · rw [dif_neg h1]
        by_cases h2 : i.val < u + v
        · rw [dif_pos h2, dif_neg h1, dif_pos h2]
          exact two_mul_half4 ((zmod4_even_iff _).mp (hmid i (by omega) h2))
        · rw [dif_neg h2]
          exact (htail i (by omega)).symm
  have hout_card : outD.card = 2 ^ (2 * u + v) := by
    rw [← Fintype.card_coe]
    have heqv : outD ≃ (Fin u → ZMod 4) × (Fin v → ZMod 2) :=
      { toFun := fun y =>
          (fun a => y.1 ⟨a.val, by omega⟩,
           fun b => if y.1 ⟨u + b.val, by omega⟩ = 0 then 0 else 1)
        invFun := fun p =>
          ⟨fun i => if h1 : i.val < u then p.1 ⟨i.val, h1⟩
            else if h2 : i.val < u + v then lift2 (p.2 ⟨i.val - u, by omega⟩)
            else 0,
            (hout_mem _).mpr ⟨fun i hu huv => by
              rw [dif_neg (by omega), dif_pos huv]
              rcases zmod2_cases (p.2 ⟨i.val - u, by omega⟩) with h | h <;> simp [lift2, h],
            fun i huv => by rw [dif_neg (by omega), dif_neg (by omega)]⟩⟩
        left_inv := fun y => by
          apply Subtype.ext; ext i
          dsimp only
          obtain ⟨hmid, htail⟩ := (hout_mem y.1).mp y.2
          by_cases h1 : i.val < u
          · simp [dif_pos h1]
          · rw [dif_neg h1]
            by_cases h2 : i.val < u + v
            · rw [dif_pos h2]
              have heq : (⟨u + (i.val - u), by omega⟩ : Fin n) = i := Fin.ext (by dsimp only; omega)
              rw [heq]
              rcases hmid i (by omega) h2 with h0 | h2'
              · simp [lift2, h0]
              · have h20 : (2 : ZMod 4) ≠ 0 := by decide
                simp [lift2, h2', h20]
            · rw [dif_neg h2]; exact (htail i (by omega)).symm
        right_inv := fun p => by
          apply Prod.ext
          · ext a; dsimp only; simp [a.isLt]
          · ext b; dsimp only
            have h1 : ¬(u + b.val < u) := by omega
            have h2 : u + b.val < u + v := by omega
            simp only [dif_neg h1, dif_pos h2]
            have heq : (⟨u + b.val - u, by omega⟩ : Fin v) = b := Fin.ext (by dsimp only; omega)
            rw [heq]
            have h20 : (2 : ZMod 4) ≠ 0 := by decide
            rcases zmod2_cases (p.2 b) with h | h <;> simp [lift2, h, h20] }
    rw [Fintype.card_congr heqv, Fintype.card_prod, Fintype.card_pi, Fintype.card_pi]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ZMod.card]
    have h4 : 4 ^ u = 2 ^ (2 * u) := by
      rw [pow_mul]; norm_num
    rw [h4, ← pow_add]
  have hkill_card : (outD.filter (fun y => ∀ i, y i + y i = 0)).card = 2 ^ (u + v) := by
    let killD := outD.filter (fun y => ∀ i, y i + y i = 0)
    have hkm : ∀ y : Fin n → ZMod 4, y ∈ killD ↔
        (∀ i : Fin n, i.val < u + v → y i = 0 ∨ y i = 2) ∧
        (∀ i : Fin n, u + v ≤ i.val → y i = 0) := by
      intro y
      simp only [killD, Finset.mem_filter, hout_mem, zmod4_killed_iff]
      constructor
      · rintro ⟨⟨_, htail⟩, hall⟩
        exact ⟨fun i _ => hall i, htail⟩
      · rintro ⟨hhead, htail⟩
        refine ⟨⟨fun i _ huv => hhead i huv, htail⟩, fun i => ?_⟩
        by_cases h : i.val < u + v
        · exact hhead i h
        · exact Or.inl (htail i (by omega))
    rw [← Fintype.card_coe]
    have heqv : killD ≃ (Fin (u + v) → ZMod 2) :=
      { toFun := fun y a => if y.1 ⟨a.val, by omega⟩ = 0 then 0 else 1
        invFun := fun p =>
          ⟨fun i => if h : i.val < u + v then lift2 (p ⟨i.val, h⟩) else 0,
           (hkm _).mpr ⟨fun i h => by
              rw [dif_pos h]
              rcases zmod2_cases (p ⟨i.val, h⟩) with h0 | h1
              · simp [lift2, h0]
              · simp [lift2, h1],
            fun i h => by rw [dif_neg (by omega)]⟩⟩
        left_inv := fun y => by
          apply Subtype.ext; ext i
          dsimp only
          obtain ⟨hhead, htail⟩ := (hkm y.1).mp y.2
          by_cases h : i.val < u + v
          · rw [dif_pos h]
            rcases hhead i h with h0 | h2
            · simp [lift2, h0]
            · have h20 : (2 : ZMod 4) ≠ 0 := by decide
              simp [lift2, h2, h20]
          · rw [dif_neg h]; exact (htail i (by omega)).symm
        right_inv := fun p => by
          ext a; dsimp only
          simp only [dif_pos a.isLt]
          have h20 : (2 : ZMod 4) ≠ 0 := by decide
          rcases zmod2_cases (p a) with h | h <;> simp [lift2, h, h20] }
    rw [Fintype.card_congr heqv, Fintype.card_pi]
    simp [ZMod.card]
  exact ⟨hrank, hout_card, hkill_card⟩

private lemma card_range_mulVec_zmod2 {a b : ℕ} (M : Matrix (Fin a) (Fin b) (ZMod 2)) :
    (Finset.univ.image (fun x : Fin b → ZMod 2 => M.mulVec x)).card = 2 ^ Matrix.rank M := by
  let _ : Fintype (LinearMap.range M.mulVecLin) := Fintype.ofFinite _
  have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.range M.mulVecLin)
  simp only [ZMod.card] at h1
  rw [← Fintype.card_coe]
  have heqv : (Finset.univ.image (fun x : Fin b → ZMod 2 => M.mulVec x)) ≃ LinearMap.range M.mulVecLin :=
    { toFun := fun y =>
        ⟨y.1, by
          obtain ⟨x, _, hx⟩ := Finset.mem_image.mp y.2
          exact ⟨x, hx⟩⟩
      invFun := fun y =>
        ⟨y.1, by
          obtain ⟨x, hx⟩ := y.2
          exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr heqv]
  exact h1

end PEqualNP.Outside.L_lib_950_aux

open PEqualNP.Outside.L_lib_950_aux in
theorem PEqualNP.Outside.L_lib_950 : (∀ (n m w p q : ℕ) (G : Matrix (Fin n) (Fin m) (ZMod 4)),
  let reduce := fun {a b : ℕ} (M : Matrix (Fin a) (Fin b) (ZMod 4)) =>
    (fun i j => ((M i j).val : ZMod 2) : Matrix (Fin a) (Fin b) (ZMod 2))
  let outputs := Finset.univ.image (fun x : Fin m → ZMod 4 => G.mulVec x)
  let killed := outputs.filter (fun y => ∀ i, y i + y i = 0)
  (∃ (U : Matrix (Fin n) (Fin w) (ZMod 4)) (V : Matrix (Fin w) (Fin m) (ZMod 4)),
    U * V = G ∧ Matrix.rank (reduce U) ≤ p ∧ Matrix.rank (reduce V) ≤ q) ↔
    Matrix.rank (reduce G) ≤ min p q ∧ outputs.card ≤ 2^(p+q) ∧ killed.card ≤ 2^w) := by
  intro n m w p q G reduce outputs killed
  constructor
  · rintro ⟨U, V, hUV, hUp, hVq⟩
    have hrankG : Matrix.rank (reduce G) ≤ min p q := by
      have hmul : redMat G = redMat U * redMat V := by rw [← hUV, redMat_mul]
      change Matrix.rank (redMat G) ≤ min p q
      rw [hmul]
      exact le_min (le_trans (Matrix.rank_mul_le_left _ _) hUp)
        (le_trans (Matrix.rank_mul_le_right _ _) hVq)
    have hkilled : killed.card ≤ 2 ^ w := by
      let outU := Finset.univ.image (fun z : Fin w → ZMod 4 => U.mulVec z)
      let killU := outU.filter (fun y => ∀ i, y i + y i = 0)
      have hsub : killed ⊆ killU := by
        intro y hy
        obtain ⟨hyOut, hyKill⟩ := Finset.mem_filter.mp hy
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hyOut
        refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨V.mulVec x, Finset.mem_univ _, ?_⟩, hyKill⟩
        rw [← hUV, Matrix.mulVec_mulVec]
      obtain ⟨u', v', P, P', Q, Q', hun, huw, hPP', hP'P, hQQ', hQ'Q, hDU⟩ := snf_zmod4 n w U
      have hinv := (outputs_killed_inv P P' Q Q' U hPP' hP'P hQQ' hQ'Q).2
      rw [hDU] at hinv
      have hcardU := (diagUV_invariants hun huw).2.2
      have hkillU : killU.card = 2 ^ (u' + v') := by
        change ((Finset.univ.image (fun z : Fin w → ZMod 4 => U.mulVec z)).filter _).card = _
        rw [← hinv, hcardU]
      exact le_trans (Finset.card_le_card hsub) (by rw [hkillU]; exact Nat.pow_le_pow_right (by omega) huw)
    have houtputs : outputs.card ≤ 2 ^ (p + q) := by
      let par : (Fin m → ZMod 4) → (Fin w → ZMod 2) := fun x i => red42 ((V.mulVec x) i)
      let parImg := Finset.univ.image par
      have hparSub : parImg ⊆ Finset.univ.image (fun z : Fin m → ZMod 2 => (redMat V).mulVec z) := by
        intro c hc
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hc
        refine Finset.mem_image.mpr ⟨fun j => red42 (x j), Finset.mem_univ _, ?_⟩
        exact (redMat_mulVec V x).symm
      have hparCard : parImg.card ≤ 2 ^ q := by
        calc parImg.card ≤ (Finset.univ.image (fun z : Fin m → ZMod 2 => (redMat V).mulVec z)).card :=
              Finset.card_le_card hparSub
          _ = 2 ^ Matrix.rank (redMat V) := card_range_mulVec_zmod2 (redMat V)
          _ ≤ 2 ^ q := Nat.pow_le_pow_right (by omega) hVq
      let fiber : (Fin w → ZMod 2) → Finset (Fin n → ZMod 4) := fun c =>
        (Finset.univ.filter (fun x : Fin m → ZMod 4 => par x = c)).image (fun x => G.mulVec x)
      have hcover : outputs ⊆ parImg.biUnion fiber := by
        intro y hy
        obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
        refine Finset.mem_biUnion.mpr ⟨par x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩, ?_⟩
        exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
      have hfiber_le : ∀ c ∈ parImg, (fiber c).card ≤ 2 ^ p := by
        intro c hc
        obtain ⟨x₀, _, hx₀⟩ := Finset.mem_image.mp hc
        let outU2 := Finset.univ.image (fun b : Fin w → ZMod 2 => (redMat U).mulVec b)
        let shiftMap : (Fin n → ZMod 2) → (Fin n → ZMod 4) :=
          fun v i => G.mulVec x₀ i + lift2 (v i)
        have hsub : fiber c ⊆ outU2.image shiftMap := by
          intro y hy
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
          have hpx : par x = c := (Finset.mem_filter.mp hx).2
          let δ : Fin w → ZMod 4 := V.mulVec x - V.mulVec x₀
          have hδ_even : ∀ j, red42 (δ j) = 0 := by
            intro j
            have hj : red42 ((V.mulVec x) j) = red42 ((V.mulVec x₀) j) := by
              change par x j = par x₀ j; rw [hpx, hx₀]
            simp [δ, hj]
          let b4 : Fin w → ZMod 4 := fun j => half4 (δ j)
          have hδ_eq : δ = (2 : ZMod 4) • b4 := by
            ext j
            change δ j = 2 * half4 (δ j)
            exact (two_mul_half4 (hδ_even j)).symm
          refine Finset.mem_image.mpr ⟨(redMat U).mulVec (fun j => red42 (b4 j)),
            Finset.mem_image.mpr ⟨fun j => red42 (b4 j), Finset.mem_univ _, rfl⟩, ?_⟩
          ext i
          dsimp only [shiftMap]
          have hstep : G.mulVec x i - G.mulVec x₀ i = lift2 (((redMat U).mulVec (fun j => red42 (b4 j))) i) := by
            rw [← redMat_mulVec U b4, lift2_red42]
            have h1 : G.mulVec x - G.mulVec x₀ = U.mulVec δ := by
              rw [← hUV, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub]
            have h2 := congr_fun h1 i
            rw [hδ_eq, Matrix.mulVec_smul] at h2
            exact h2
          calc G.mulVec x₀ i + lift2 (((redMat U).mulVec (fun j => red42 (b4 j))) i)
              = G.mulVec x₀ i + (G.mulVec x i - G.mulVec x₀ i) := by rw [hstep]
            _ = G.mulVec x i := by ring
        calc (fiber c).card ≤ (outU2.image shiftMap).card := Finset.card_le_card hsub
          _ ≤ outU2.card := Finset.card_image_le
          _ = 2 ^ Matrix.rank (redMat U) := card_range_mulVec_zmod2 (redMat U)
          _ ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) hUp
      calc outputs.card ≤ (parImg.biUnion fiber).card := Finset.card_le_card hcover
        _ ≤ ∑ c ∈ parImg, (fiber c).card := Finset.card_biUnion_le
        _ ≤ ∑ _c ∈ parImg, 2 ^ p := Finset.sum_le_sum hfiber_le
        _ = parImg.card * 2 ^ p := by simp
        _ ≤ 2 ^ q * 2 ^ p := Nat.mul_le_mul_right _ hparCard
        _ = 2 ^ (p + q) := by rw [← pow_add, add_comm]
    exact ⟨hrankG, houtputs, hkilled⟩
  · rintro ⟨hrankG, houtputs, hkilled⟩
    obtain ⟨u, v, P, P', Q, Q', huvn, huvm, hPP', hP'P, hQQ', hQ'Q, hD⟩ := snf_zmod4 n m G
    have hinvR := rank_redMat_inv P P' Q Q' G hPP' hP'P hQQ' hQ'Q
    have hinvOK := outputs_killed_inv P P' Q Q' G hPP' hP'P hQQ' hQ'Q
    rw [hD] at hinvR hinvOK
    obtain ⟨hDrank, hDout, hDkill⟩ := diagUV_invariants huvn huvm
    have hu_le_pq : u ≤ min p q := by
      have : Matrix.rank (reduce G) = u := by
        change Matrix.rank (redMat G) = u
        rw [← hinvR, hDrank]
      omega
    have hu_p : u ≤ p := le_trans hu_le_pq (min_le_left p q)
    have hu_q : u ≤ q := le_trans hu_le_pq (min_le_right p q)
    have h2uv : 2 * u + v ≤ p + q := by
      have hcard : outputs.card = 2 ^ (2 * u + v) := by rw [← hinvOK.1, hDout]
      rw [hcard] at houtputs
      exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp houtputs
    have huv_w : u + v ≤ w := by
      have hcard : killed.card = 2 ^ (u + v) := by rw [← hinvOK.2, hDkill]
      rw [hcard] at hkilled
      exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hkilled
    let v1 := min v (p - u)
    let v2 := v - v1
    have hv12 : v1 + v2 = v := by omega
    have huv1_p : u + v1 ≤ p := by omega
    have huv2_q : u + v2 ≤ q := by omega
    let A : Matrix (Fin n) (Fin w) (ZMod 4) := Matrix.of fun i k =>
      if i.val = k.val then
        if i.val < u + v1 then 1 else if i.val < u + v then 2 else 0
      else 0
    let B : Matrix (Fin w) (Fin m) (ZMod 4) := Matrix.of fun k j =>
      if k.val = j.val then
        if k.val < u then 1 else if k.val < u + v1 then 2 else if k.val < u + v then 1 else 0
      else 0
    have hAB : A * B = diagUV n m u v := by
      ext i j
      simp only [Matrix.mul_apply, A, B, diagUV, Matrix.of_apply]
      by_cases hij : i.val = j.val
      · by_cases huv : i.val < u + v
        · rw [Finset.sum_eq_single ⟨i.val, by omega⟩]
          · simp only [hij, ↓reduceIte]
            by_cases h1 : j.val < u
            · have h1' : j.val < u + v1 := by omega
              simp [h1, h1']
            · by_cases h2 : j.val < u + v1
              · have h2' : j.val < u + v := by omega
                simp [h1, h2, h2']
              · have h3 : j.val < u + v := by omega
                simp [h1, h2, h3]
          · intro k _ hk
            have hne : i.val ≠ k.val := fun h => hk (Fin.ext h.symm)
            simp [hne]
          · intro h; exact (h (Finset.mem_univ _)).elim
        · simp only [hij, ↓reduceIte]
          have hnot1 : ¬(j.val < u) := by omega
          have hnot2 : ¬(j.val < u + v) := by omega
          have hnot3 : ¬(j.val < u + v1) := by omega
          simp only [hnot1, hnot2, hnot3, ↓reduceIte]
          apply Finset.sum_eq_zero; intro k _
          simp
      · simp only [hij, ↓reduceIte]
        apply Finset.sum_eq_zero; intro k _
        by_cases hik : i.val = k.val
        · have hkj : k.val ≠ j.val := by omega
          simp [hik, hkj]
        · simp [hik]
    have hrankA : Matrix.rank (redMat A) ≤ p := by
      have hredA : redMat A = Matrix.of (fun (i : Fin n) (k : Fin w) =>
          if i.val = k.val ∧ i.val ∈ Finset.range (u + v1) then (1 : ZMod 2) else 0) := by
        ext i k
        rw [redMat_eq_map]
        simp only [A, Matrix.map_apply, Matrix.of_apply, Finset.mem_range]
        by_cases hik : i.val = k.val
        · rw [if_pos hik]
          simp only [hik, true_and]
          by_cases h1 : k.val < u + v1
          · simp [h1]
          · rw [if_neg h1, if_neg h1]
            by_cases h2 : k.val < u + v
            · rw [if_pos h2]; decide
            · rw [if_neg h2]; simp
        · simp [hik]
      rw [hredA, rank_diag_mask n w (Finset.range (u + v1))
        (fun k hk => by simp at hk; omega) (fun k hk => by simp at hk; omega), Finset.card_range]
      exact huv1_p
    have hrankB : Matrix.rank (redMat B) ≤ q := by
      let SB : Finset ℕ := Finset.range u ∪ Finset.Ico (u + v1) (u + v)
      have hSB_card : SB.card = u + v2 := by
        have hdisj : Disjoint (Finset.range u) (Finset.Ico (u + v1) (u + v)) := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          simp only [Finset.mem_range, Finset.mem_Ico] at hx1 hx2
          omega
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_range, Nat.card_Ico]
        omega
      have hredB : redMat B = Matrix.of (fun (k : Fin w) (j : Fin m) =>
          if k.val = j.val ∧ k.val ∈ SB then (1 : ZMod 2) else 0) := by
        ext k j
        rw [redMat_eq_map]
        simp only [B, SB, Matrix.map_apply, Matrix.of_apply, Finset.mem_union, Finset.mem_range,
          Finset.mem_Ico]
        by_cases hkj : k.val = j.val
        · rw [if_pos hkj]
          simp only [hkj, true_and]
          by_cases h1 : j.val < u
          · rw [if_pos h1, if_pos (Or.inl h1)]; simp
          · rw [if_neg h1]
            by_cases h2 : j.val < u + v1
            · have hnot : ¬(j.val < u ∨ u + v1 ≤ j.val ∧ j.val < u + v) := by omega
              rw [if_pos h2, if_neg hnot]; decide
            · rw [if_neg h2]
              by_cases h3 : j.val < u + v
              · have hyes : j.val < u ∨ u + v1 ≤ j.val ∧ j.val < u + v := Or.inr ⟨by omega, h3⟩
                rw [if_pos h3, if_pos hyes]; simp
              · have hnot : ¬(j.val < u ∨ u + v1 ≤ j.val ∧ j.val < u + v) := by omega
                rw [if_neg h3, if_neg hnot]; simp
        · simp [hkj]
      rw [hredB, rank_diag_mask w m SB
        (fun k hk => by simp only [SB, Finset.mem_union, Finset.mem_range, Finset.mem_Ico] at hk; omega)
        (fun k hk => by simp only [SB, Finset.mem_union, Finset.mem_range, Finset.mem_Ico] at hk; omega),
        hSB_card]
      exact huv2_q
    refine ⟨P' * A, B * Q', ?_, ?_, ?_⟩
    · calc (P' * A) * (B * Q') = P' * (A * B) * Q' := by simp only [Matrix.mul_assoc]
        _ = P' * (P * G * Q) * Q' := by rw [hAB, ← hD]
        _ = (P' * P) * G * (Q * Q') := by simp only [Matrix.mul_assoc]
        _ = G := by rw [hP'P, hQQ', Matrix.one_mul, Matrix.mul_one]
    · change Matrix.rank (redMat (P' * A)) ≤ p
      rw [redMat_mul]
      exact le_trans (Matrix.rank_mul_le_right _ _) hrankA
    · change Matrix.rank (redMat (B * Q')) ≤ q
      rw [redMat_mul]
      exact le_trans (Matrix.rank_mul_le_left _ _) hrankB
