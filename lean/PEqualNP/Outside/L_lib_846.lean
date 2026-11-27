import PEqualNP.Defs

open scoped BigOperators

namespace PEqualNP.Outside.L_lib_846_aux

def defectVal {m : ℕ} (a b : Fin m → ℕ) (s : Fin m → Bool) (right top : Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin m =>
    ((if right then a i else 0) + (if top then b i else 0)) % 2 ≠ (s i).toNat)).card

lemma mod2_sum_fin {m : ℕ} (f : Fin m → ℕ) :
    (∑ i : Fin m, f i) % 2 = (∑ i : Fin m, f i % 2) % 2 := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have := ih (fun i => f i.castSucc)
    omega

lemma defect_mod2 {m : ℕ} (a b : Fin m → ℕ) (s : Fin m → Bool) (right top : Bool) :
    defectVal a b s right top % 2 =
    ((if right then ∑ i : Fin m, a i else 0) +
     (if top then ∑ i : Fin m, b i else 0) +
     ∑ i : Fin m, (s i).toNat) % 2 := by
  induction m with
  | zero =>
    simp [defectVal]
  | succ n ih =>
    let a' : Fin n → ℕ := fun i => a i.castSucc
    let b' : Fin n → ℕ := fun i => b i.castSucc
    let s' : Fin n → Bool := fun i => s i.castSucc
    have hsplit : defectVal a b s right top = defectVal a' b' s' right top +
        if ((if right then a (Fin.last n) else 0) + (if top then b (Fin.last n) else 0)) % 2 ≠
            (s (Fin.last n)).toNat then 1 else 0 := by
      simp only [defectVal, Finset.card_filter, Fin.sum_univ_castSucc]
      rfl
    have hih := ih a' b' s'
    have hA : ∑ i : Fin (n + 1), a i = (∑ i : Fin n, a' i) + a (Fin.last n) :=
      Fin.sum_univ_castSucc a
    have hB : ∑ i : Fin (n + 1), b i = (∑ i : Fin n, b' i) + b (Fin.last n) :=
      Fin.sum_univ_castSucc b
    have hS : ∑ i : Fin (n + 1), (s i).toNat = (∑ i : Fin n, (s' i).toNat) + (s (Fin.last n)).toNat :=
      Fin.sum_univ_castSucc (fun i => (s i).toNat)
    rw [hsplit, hA, hB, hS]
    cases right <;> cases top <;> cases hs : s (Fin.last n) <;> simp only [Bool.toNat_false,
      Bool.toNat_true, Bool.false_eq_true, ↓reduceIte] at hih ⊢ <;> split_ifs <;> omega

lemma defect_pair_bounds {m : ℕ} (a b : Fin m → ℕ) (s : Fin m → Bool)
    (hpos : ∀ i, 0 < a i ∧ 0 < b i) :
    defectVal a b s false false + defectVal a b s false true ≤ ∑ i : Fin m, b i ∧
    defectVal a b s true false + defectVal a b s true true ≤ ∑ i : Fin m, b i ∧
    defectVal a b s false false + defectVal a b s true false ≤ ∑ i : Fin m, a i ∧
    defectVal a b s false true + defectVal a b s true true ≤ ∑ i : Fin m, a i := by
  have h1 : ∀ right : Bool, defectVal a b s right false + defectVal a b s right true ≤ ∑ i : Fin m, b i := by
    intro right
    simp only [defectVal, Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hbi := (hpos i).2
    cases right <;> cases hs : s i <;> simp only [Bool.toNat_false, Bool.toNat_true,
      Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;> omega
  have h2 : ∀ top : Bool, defectVal a b s false top + defectVal a b s true top ≤ ∑ i : Fin m, a i := by
    intro top
    simp only [defectVal, Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hai := (hpos i).1
    cases top <;> cases hs : s i <;> simp only [Bool.toNat_false, Bool.toNat_true,
      Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;> omega
  exact ⟨h1 false, h1 true, h2 false, h2 true⟩

lemma forward_dir {m : ℕ} (a b : Fin m → ℕ) (s : Fin m → Bool)
    (u v : ℕ) (x y : Fin m → ℕ)
    (hxy : ∀ i, x i ≤ a i ∧ y i ≤ b i ∧ (x i + y i) % 2 = (s i).toNat)
    (hu : ∑ i : Fin m, x i = u) (hv : ∑ i : Fin m, y i = v) :
    let A := ∑ i : Fin m, a i
    let B := ∑ i : Fin m, b i
    u ≤ A ∧ v ≤ B ∧ (u + v) % 2 = (∑ i : Fin m, (s i).toNat) % 2 ∧
    ∀ right top : Bool, defectVal a b s right top ≤
      (if right then A - u else u) + (if top then B - v else v) := by
  dsimp only
  have huA : u ≤ ∑ i : Fin m, a i := by
    rw [← hu]; exact Finset.sum_le_sum (fun i _ => (hxy i).1)
  have hvB : v ≤ ∑ i : Fin m, b i := by
    rw [← hv]; exact Finset.sum_le_sum (fun i _ => (hxy i).2.1)
  have hpar : (u + v) % 2 = (∑ i : Fin m, (s i).toNat) % 2 := by
    rw [← hu, ← hv, ← Finset.sum_add_distrib, mod2_sum_fin]
    have heq : ∑ i : Fin m, (x i + y i) % 2 = ∑ i : Fin m, (s i).toNat :=
      Finset.sum_congr rfl (fun i _ => (hxy i).2.2)
    rw [heq]
  refine ⟨huA, hvB, hpar, ?_⟩
  intro right top
  have hdist : ∑ i : Fin m,
      ((if right then a i - x i else x i) + (if top then b i - y i else y i)) =
      (if right then (∑ i : Fin m, a i) - u else u) +
      (if top then (∑ i : Fin m, b i) - v else v) := by
    rw [Finset.sum_add_distrib]
    congr 1
    · cases right
      · simp [hu]
      · simp only [↓reduceIte, ← hu]
        have hsub : ∀ s' : Finset (Fin m), (∀ i ∈ s', x i ≤ a i) →
            ∑ i ∈ s', (a i - x i) = ∑ i ∈ s', a i - ∑ i ∈ s', x i := by
          intro s' hs'
          have hadd : (∑ i ∈ s', (a i - x i)) + ∑ i ∈ s', x i = ∑ i ∈ s', a i := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun i hi => Nat.sub_add_cancel (hs' i hi))
          omega
        exact hsub Finset.univ (fun i _ => (hxy i).1)
    · cases top
      · simp [hv]
      · simp only [↓reduceIte, ← hv]
        have hsub : ∀ s' : Finset (Fin m), (∀ i ∈ s', y i ≤ b i) →
            ∑ i ∈ s', (b i - y i) = ∑ i ∈ s', b i - ∑ i ∈ s', y i := by
          intro s' hs'
          have hadd : (∑ i ∈ s', (b i - y i)) + ∑ i ∈ s', y i = ∑ i ∈ s', b i := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun i hi => Nat.sub_add_cancel (hs' i hi))
          omega
        exact hsub Finset.univ (fun i _ => (hxy i).2.1)
  rw [← hdist]
  simp only [defectVal, Finset.card_filter]
  apply Finset.sum_le_sum
  intro i _
  have h1 := (hxy i).1
  have h2 := (hxy i).2.1
  have h3 := (hxy i).2.2
  cases right <;> cases top <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;> omega

lemma max_eq_min_end (A a' u : ℤ) (hA : 1 ≤ A) (ha' : 1 ≤ a')
    (h : max 0 (u - A) = min a' u) : u = 0 ∨ u = A + a' := by
  rcases max_choice 0 (u - A) with h1 | h1 <;> rcases min_choice a' u with h2 | h2 <;> omega

lemma corner_eq_par (d x R : ℤ) (s : Bool) (hd : 0 ≤ d) (hR : R = 0)
    (hc : d + (if x % 2 ≠ (s.toNat : ℤ) then 1 else 0) ≤ R) :
    x % 2 = (s.toNat : ℤ) := by
  split_ifs at hc with hne
  · omega
  · exact not_not.mp hne

lemma recover_xy (A B a' b' u v d00 d01 d10 d11 P Q : ℤ) (s' : Bool)
    (hPpar : P % 2 = (s'.toNat : ℤ)) (hQpar : Q % 2 = (s'.toNat : ℤ))
    (h1 : u + v - A - B + d11 ≤ P) (h5 : P ≤ u + v - d00)
    (hQlo : u - v - A + d10 ≤ Q) (hQhi : Q ≤ u - v + B - d01)
    (h2Lx : 2 * max 0 (u - A) - P ≤ Q) (h2Ux : Q ≤ 2 * min a' u - P)
    (h2Uy : P - 2 * min b' v ≤ Q) (h2Ly : Q ≤ P - 2 * max 0 (v - B)) :
    0 ≤ (P + Q) / 2 ∧ (P + Q) / 2 ≤ a' ∧ 0 ≤ (P - Q) / 2 ∧ (P - Q) / 2 ≤ b' ∧
    ((P + Q) / 2 + (P - Q) / 2) % 2 = (s'.toNat : ℤ) ∧
    0 ≤ u - (P + Q) / 2 ∧ u - (P + Q) / 2 ≤ A ∧ 0 ≤ v - (P - Q) / 2 ∧ v - (P - Q) / 2 ≤ B ∧
    d00 ≤ (u - (P + Q) / 2) + (v - (P - Q) / 2) ∧
    d01 ≤ (u - (P + Q) / 2) + (B - (v - (P - Q) / 2)) ∧
    d10 ≤ (A - (u - (P + Q) / 2)) + (v - (P - Q) / 2) ∧
    d11 ≤ (A - (u - (P + Q) / 2)) + (B - (v - (P - Q) / 2)) := by
  have hLx0 : 0 ≤ (P + Q) / 2 := by have := le_max_left 0 (u - A); omega
  have hLx1 : u - A ≤ (P + Q) / 2 := by have := le_max_right 0 (u - A); omega
  have hUx0 : (P + Q) / 2 ≤ a' := by have := min_le_left a' u; omega
  have hUx1 : (P + Q) / 2 ≤ u := by have := min_le_right a' u; omega
  have hLy0 : 0 ≤ (P - Q) / 2 := by have := le_max_left 0 (v - B); omega
  have hLy1 : v - B ≤ (P - Q) / 2 := by have := le_max_right 0 (v - B); omega
  have hUy0 : (P - Q) / 2 ≤ b' := by have := min_le_left b' v; omega
  have hUy1 : (P - Q) / 2 ≤ v := by have := min_le_right b' v; omega
  have hsum : (P + Q) / 2 + (P - Q) / 2 = P := by
    cases s' <;> simp only [Bool.toNat_false, Bool.toNat_true] at hPpar hQpar <;> omega
  have hdiff : (P + Q) / 2 - (P - Q) / 2 = Q := by
    cases s' <;> simp only [Bool.toNat_false, Bool.toNat_true] at hPpar hQpar <;> omega
  refine ⟨hLx0, hUx0, hLy0, hUy0, ?_, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega⟩
  rw [hsum]; exact hPpar

lemma backward_step_int (A B a' b' u v d00 d01 d10 d11 : ℤ) (s' : Bool)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (ha' : 1 ≤ a') (hb' : 1 ≤ b')
    (hu0 : 0 ≤ u) (huA : u ≤ A + a') (hv0 : 0 ≤ v) (hvB : v ≤ B + b')
    (h00_01 : d00 + d01 ≤ B) (h10_11 : d10 + d11 ≤ B)
    (h00_10 : d00 + d10 ≤ A) (h01_11 : d01 + d11 ≤ A)
    (hd00 : 0 ≤ d00) (hd01 : 0 ≤ d01) (hd10 : 0 ≤ d10) (hd11 : 0 ≤ d11)
    (hp00 : (u + v - d00) % 2 = (s'.toNat : ℤ))
    (hp11 : (u + v - A - B + d11) % 2 = (s'.toNat : ℤ))
    (hp01 : (u - v + B - d01) % 2 = (s'.toNat : ℤ))
    (hp10 : (u - v - A + d10) % 2 = (s'.toNat : ℤ))
    (hc00 : d00 + (if (0 : ℤ) % 2 ≠ (s'.toNat : ℤ) then 1 else 0) ≤ u + v)
    (hc01 : d01 + (if b' % 2 ≠ (s'.toNat : ℤ) then 1 else 0) ≤ u + (B + b' - v))
    (hc10 : d10 + (if a' % 2 ≠ (s'.toNat : ℤ) then 1 else 0) ≤ (A + a' - u) + v)
    (hc11 : d11 + (if (a' + b') % 2 ≠ (s'.toNat : ℤ) then 1 else 0) ≤ (A + a' - u) + (B + b' - v)) :
    ∃ x' y' : ℤ,
      0 ≤ x' ∧ x' ≤ a' ∧ 0 ≤ y' ∧ y' ≤ b' ∧ (x' + y') % 2 = (s'.toNat : ℤ) ∧
      0 ≤ u - x' ∧ u - x' ≤ A ∧ 0 ≤ v - y' ∧ v - y' ≤ B ∧
      d00 ≤ (u - x') + (v - y') ∧
      d01 ≤ (u - x') + (B - (v - y')) ∧
      d10 ≤ (A - (u - x')) + (v - y') ∧
      d11 ≤ (A - (u - x')) + (B - (v - y')) := by
  have hc00' : d00 ≤ u + v := by
    have : (0 : ℤ) ≤ if (0 : ℤ) % 2 ≠ (s'.toNat : ℤ) then 1 else 0 := by split_ifs <;> norm_num
    linarith
  have hc01' : d01 ≤ u + (B + b' - v) := by
    have : (0 : ℤ) ≤ if b' % 2 ≠ (s'.toNat : ℤ) then 1 else 0 := by split_ifs <;> norm_num
    linarith
  have hc10' : d10 ≤ (A + a' - u) + v := by
    have : (0 : ℤ) ≤ if a' % 2 ≠ (s'.toNat : ℤ) then 1 else 0 := by split_ifs <;> norm_num
    linarith
  have hc11' : d11 ≤ (A + a' - u) + (B + b' - v) := by
    have : (0 : ℤ) ≤ if (a' + b') % 2 ≠ (s'.toNat : ℤ) then 1 else 0 := by split_ifs <;> norm_num
    linarith
  let Lx := max 0 (u - A)
  let Ux := min a' u
  let Ly := max 0 (v - B)
  let Uy := min b' v
  let Plo := u + v - A - B + d11
  let Phi := u + v - d00
  let Qlo := u - v - A + d10
  let Qhi := u - v + B - d01
  have hLxUx : Lx ≤ Ux := max_le (le_min (by linarith) hu0) (le_min (by linarith) (by linarith))
  have hLyUy : Ly ≤ Uy := max_le (le_min (by linarith) hv0) (le_min (by linarith) (by linarith))
  have h11 : Plo ≤ Phi := by dsimp only [Plo, Phi]; linarith
  have h12 : Plo ≤ Ux + Uy := by
    dsimp only [Plo, Ux, Uy]
    rcases min_choice a' u with h1 | h1 <;> rcases min_choice b' v with h2 | h2 <;> linarith
  have h13 : Plo ≤ 2 * Ux - Qlo := by
    dsimp only [Plo, Ux, Qlo]
    rcases min_choice a' u with h1 | h1 <;> linarith
  have h14 : Plo ≤ Qhi + 2 * Uy := by
    dsimp only [Plo, Qhi, Uy]
    rcases min_choice b' v with h1 | h1 <;> linarith
  have h21 : Lx + Ly ≤ Phi := by
    dsimp only [Lx, Ly, Phi]
    rcases max_choice 0 (u - A) with h1 | h1 <;> rcases max_choice 0 (v - B) with h2 | h2 <;> linarith
  have h22 : Lx + Ly ≤ Ux + Uy := add_le_add hLxUx hLyUy
  have hQlo_le : Qlo ≤ Ux - Ly := by
    dsimp only [Qlo, Ux, Ly]
    rcases min_choice a' u with h1 | h1 <;> rcases max_choice 0 (v - B) with h2 | h2 <;> linarith
  have hQhi_ge : Lx - Uy ≤ Qhi := by
    dsimp only [Lx, Uy, Qhi]
    rcases max_choice 0 (u - A) with h1 | h1 <;> rcases min_choice b' v with h2 | h2 <;> linarith
  have h23 : Lx + Ly ≤ 2 * Ux - Qlo := by linarith
  have h24 : Lx + Ly ≤ Qhi + 2 * Uy := by linarith
  have h31 : Qlo + 2 * Ly ≤ Phi := by
    dsimp only [Qlo, Ly, Phi]
    rcases max_choice 0 (v - B) with h1 | h1 <;> linarith
  have h32 : Qlo + 2 * Ly ≤ Ux + Uy := by linarith
  have h33 : Qlo + 2 * Ly ≤ 2 * Ux - Qlo := by linarith
  have h34 : Qlo + 2 * Ly ≤ Qhi + 2 * Uy := by dsimp only [Qlo, Qhi]; linarith
  have h41 : 2 * Lx - Qhi ≤ Phi := by
    dsimp only [Lx, Qhi, Phi]
    rcases max_choice 0 (u - A) with h1 | h1 <;> linarith
  have h42 : 2 * Lx - Qhi ≤ Ux + Uy := by linarith
  have h43 : 2 * Lx - Qhi ≤ 2 * Ux - Qlo := by dsimp only [Qlo, Qhi]; linarith
  have h44 : 2 * Lx - Qhi ≤ Qhi + 2 * Uy := by linarith
  let AP := max (max Plo (Lx + Ly)) (max (Qlo + 2 * Ly) (2 * Lx - Qhi))
  let BP := min (min Phi (Ux + Uy)) (min (2 * Ux - Qlo) (Qhi + 2 * Uy))
  have hAP_le_BP : AP ≤ BP := by
    dsimp only [AP, BP]
    exact max_le
      (max_le (le_min (le_min h11 h12) (le_min h13 h14))
              (le_min (le_min h21 h22) (le_min h23 h24)))
      (max_le (le_min (le_min h31 h32) (le_min h33 h34))
              (le_min (le_min h41 h42) (le_min h43 h44)))
  have hP_exists : ∃ P : ℤ, AP ≤ P ∧ P ≤ BP ∧ P % 2 = (s'.toNat : ℤ) := by
    by_cases hlt : AP < BP
    · by_cases hpar : AP % 2 = (s'.toNat : ℤ)
      · exact ⟨AP, le_rfl, le_of_lt hlt, hpar⟩
      · refine ⟨AP + 1, by linarith, by linarith, ?_⟩
        cases s' <;> simp only [Bool.toNat_false, Bool.toNat_true] at hpar ⊢ <;> omega
    · have heq : AP = BP := le_antisymm hAP_le_BP (not_lt.mp hlt)
      refine ⟨AP, le_rfl, le_of_eq heq, ?_⟩
      by_cases h1 : AP = Plo ∨ AP = Qlo + 2 * Ly ∨ AP = 2 * Lx - Qhi ∨
          BP = Phi ∨ BP = 2 * Ux - Qlo ∨ BP = Qhi + 2 * Uy
      · rcases h1 with h | h | h | h | h | h
        · rw [h]; exact hp11
        · rw [h]; have : (Qlo + 2 * Ly) % 2 = Qlo % 2 := by omega
          rw [this]; exact hp10
        · rw [h]; have : (2 * Lx - Qhi) % 2 = Qhi % 2 := by omega
          rw [this]; exact hp01
        · rw [heq, h]; exact hp00
        · rw [heq, h]; have : (2 * Ux - Qlo) % 2 = Qlo % 2 := by omega
          rw [this]; exact hp10
        · rw [heq, h]; have : (Qhi + 2 * Uy) % 2 = Qhi % 2 := by omega
          rw [this]; exact hp01
      · push Not at h1
        rcases h1 with ⟨hn1, hn2, hn3, hn4, hn5, hn6⟩
        have hL : AP = Lx + Ly := by
          rcases max_choice (max Plo (Lx + Ly)) (max (Qlo + 2 * Ly) (2 * Lx - Qhi)) with hA1 | hA1
          · rcases max_choice Plo (Lx + Ly) with hA2 | hA2
            · exact absurd (hA1.trans hA2) hn1
            · exact hA1.trans hA2
          · rcases max_choice (Qlo + 2 * Ly) (2 * Lx - Qhi) with hA2 | hA2
            · exact absurd (hA1.trans hA2) hn2
            · exact absurd (hA1.trans hA2) hn3
        have hU : BP = Ux + Uy := by
          rcases min_choice (min Phi (Ux + Uy)) (min (2 * Ux - Qlo) (Qhi + 2 * Uy)) with hB1 | hB1
          · rcases min_choice Phi (Ux + Uy) with hB2 | hB2
            · exact absurd (hB1.trans hB2) hn4
            · exact hB1.trans hB2
          · rcases min_choice (2 * Ux - Qlo) (Qhi + 2 * Uy) with hB2 | hB2
            · exact absurd (hB1.trans hB2) hn5
            · exact absurd (hB1.trans hB2) hn6
        have hxy : Lx = Ux ∧ Ly = Uy :=
          ⟨le_antisymm hLxUx (by linarith), le_antisymm hLyUy (by linarith)⟩
        rw [hL]
        have hu_end : u = 0 ∨ u = A + a' := max_eq_min_end A a' u hA ha' hxy.1
        have hv_end : v = 0 ∨ v = B + b' := max_eq_min_end B b' v hB hb' hxy.2
        dsimp only [Lx, Ly]
        rcases hu_end with rfl | rfl
        · rcases hv_end with rfl | rfl
          · have hL0 : max 0 (0 - A) + max 0 (0 - B) = 0 := by
              rw [max_eq_left (by linarith), max_eq_left (by linarith)]; ring
            rw [hL0]; exact corner_eq_par d00 0 (0 + 0) s' hd00 rfl hc00
          · have hL0 : max 0 (0 - A) + max 0 (B + b' - B) = b' := by
              rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
            rw [hL0]; exact corner_eq_par d01 b' (0 + (B + b' - (B + b'))) s' hd01 (by ring) hc01
        · rcases hv_end with rfl | rfl
          · have hL0 : max 0 (A + a' - A) + max 0 (0 - B) = a' := by
              rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
            rw [hL0]; exact corner_eq_par d10 a' ((A + a' - (A + a')) + 0) s' hd10 (by ring) hc10
          · have hL0 : max 0 (A + a' - A) + max 0 (B + b' - B) = a' + b' := by
              rw [max_eq_right (by linarith), max_eq_right (by linarith)]; ring
            rw [hL0]
            exact corner_eq_par d11 (a' + b') ((A + a' - (A + a')) + (B + b' - (B + b'))) s' hd11 (by ring) hc11
  rcases hP_exists with ⟨P, hAP, hBP, hPpar⟩
  have h1 : Plo ≤ P := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hAP
  have h2 : Lx + Ly ≤ P := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hAP
  have h3 : Qlo + 2 * Ly ≤ P := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hAP
  have h4 : 2 * Lx - Qhi ≤ P := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hAP
  have h5 : P ≤ Phi := hBP.trans (le_trans (min_le_left _ _) (min_le_left _ _))
  have h6 : P ≤ Ux + Uy := hBP.trans (le_trans (min_le_left _ _) (min_le_right _ _))
  have h7 : P ≤ 2 * Ux - Qlo := hBP.trans (le_trans (min_le_right _ _) (min_le_left _ _))
  have h8 : P ≤ Qhi + 2 * Uy := hBP.trans (le_trans (min_le_right _ _) (min_le_right _ _))
  have hQ : Qlo ≤ Qhi := by dsimp only [Qlo, Qhi]; linarith
  let AQ := max Qlo (max (2 * Lx - P) (P - 2 * Uy))
  let BQ := min Qhi (min (2 * Ux - P) (P - 2 * Ly))
  have hAQ_le_BQ : AQ ≤ BQ := by
    dsimp only [AQ, BQ]
    exact max_le
      (le_min hQ (le_min (by linarith) (by linarith)))
      (max_le (le_min (by linarith) (le_min (by linarith) (by linarith)))
              (le_min (by linarith) (le_min (by linarith) (by linarith))))
  have hAQ_par : AQ % 2 = (s'.toNat : ℤ) := by
    have hm2 : (2 * Lx - P) % 2 = (s'.toNat : ℤ) := by
      have : (2 * Lx - P) % 2 = P % 2 := by omega
      rw [this]; exact hPpar
    have hm3 : (P - 2 * Uy) % 2 = (s'.toNat : ℤ) := by
      have : (P - 2 * Uy) % 2 = P % 2 := by omega
      rw [this]; exact hPpar
    dsimp only [AQ]
    rcases max_choice Qlo (max (2 * Lx - P) (P - 2 * Uy)) with hA1 | hA1
    · rw [hA1]; exact hp10
    · rw [hA1]
      rcases max_choice (2 * Lx - P) (P - 2 * Uy) with hA2 | hA2
      · rw [hA2]; exact hm2
      · rw [hA2]; exact hm3
  let Q := AQ
  have hQlo : Qlo ≤ Q := le_max_left _ _
  have hQ2Lx : 2 * Lx - P ≤ Q := le_trans (le_max_left _ _) (le_max_right _ _)
  have hQ2Uy : P - 2 * Uy ≤ Q := le_trans (le_max_right _ _) (le_max_right _ _)
  have hQhi : Q ≤ Qhi := hAQ_le_BQ.trans (min_le_left _ _)
  have hQ2Ux : Q ≤ 2 * Ux - P := hAQ_le_BQ.trans (le_trans (min_le_right _ _) (min_le_left _ _))
  have hQ2Ly : Q ≤ P - 2 * Ly := hAQ_le_BQ.trans (le_trans (min_le_right _ _) (min_le_right _ _))
  exact ⟨(P + Q) / 2, (P - Q) / 2,
    recover_xy A B a' b' u v d00 d01 d10 d11 P Q s' hPpar hAQ_par
      h1 h5 hQlo hQhi hQ2Lx hQ2Ux hQ2Uy hQ2Ly⟩

lemma cast_corner_le (d x y : ℕ) (s : Bool) (h : d + (if x % 2 ≠ s.toNat then 1 else 0) ≤ y) :
    (d : ℤ) + (if (x : ℤ) % 2 ≠ (s.toNat : ℤ) then 1 else 0) ≤ (y : ℤ) := by
  split_ifs at h ⊢ <;> omega

lemma cast_add_sub_nat (u B bl v : ℕ) (hv : v ≤ B + bl) :
    ((u + (B + bl - v) : ℕ) : ℤ) = (u : ℤ) + ((B : ℤ) + (bl : ℤ) - (v : ℤ)) := by omega

lemma cast_sub_add_nat (A al u v : ℕ) (hu : u ≤ A + al) :
    (((A + al - u) + v : ℕ) : ℤ) = ((A : ℤ) + (al : ℤ) - (u : ℤ)) + (v : ℤ) := by omega

lemma cast_sub_add_sub_nat (A al u B bl v : ℕ) (hu : u ≤ A + al) (hv : v ≤ B + bl) :
    (((A + al - u) + (B + bl - v) : ℕ) : ℤ) =
    ((A : ℤ) + (al : ℤ) - (u : ℤ)) + ((B : ℤ) + (bl : ℤ) - (v : ℤ)) := by omega

lemma step_nat_transfer (A B al bl u v d00 d01 d10 d11 S : ℕ) (sl : Bool) (xlZ ylZ : ℤ)
    (hxl0 : 0 ≤ xlZ) (hxlA : xlZ ≤ (al : ℤ)) (hyl0 : 0 ≤ ylZ) (hylB : ylZ ≤ (bl : ℤ))
    (hparl : (xlZ + ylZ) % 2 = (sl.toNat : ℤ))
    (hux0 : 0 ≤ (u : ℤ) - xlZ) (huxA : (u : ℤ) - xlZ ≤ (A : ℤ))
    (hvy0 : 0 ≤ (v : ℤ) - ylZ) (hvyB : (v : ℤ) - ylZ ≤ (B : ℤ))
    (hd00' : (d00 : ℤ) ≤ ((u : ℤ) - xlZ) + ((v : ℤ) - ylZ))
    (hd01' : (d01 : ℤ) ≤ ((u : ℤ) - xlZ) + ((B : ℤ) - ((v : ℤ) - ylZ)))
    (hd10' : (d10 : ℤ) ≤ ((A : ℤ) - ((u : ℤ) - xlZ)) + ((v : ℤ) - ylZ))
    (hd11' : (d11 : ℤ) ≤ ((A : ℤ) - ((u : ℤ) - xlZ)) + ((B : ℤ) - ((v : ℤ) - ylZ)))
    (hpar : (u + v) % 2 = (S + sl.toNat) % 2) :
    xlZ.toNat ≤ al ∧ ylZ.toNat ≤ bl ∧ (xlZ.toNat + ylZ.toNat) % 2 = sl.toNat ∧
    xlZ.toNat ≤ u ∧ ylZ.toNat ≤ v ∧
    u - xlZ.toNat ≤ A ∧ v - ylZ.toNat ≤ B ∧
    ((u - xlZ.toNat) + (v - ylZ.toNat)) % 2 = S % 2 ∧
    d00 ≤ (u - xlZ.toNat) + (v - ylZ.toNat) ∧
    d01 ≤ (u - xlZ.toNat) + (B - (v - ylZ.toNat)) ∧
    d10 ≤ (A - (u - xlZ.toNat)) + (v - ylZ.toNat) ∧
    d11 ≤ (A - (u - xlZ.toNat)) + (B - (v - ylZ.toNat)) := by
  have hx : (xlZ.toNat : ℤ) = xlZ := Int.toNat_of_nonneg hxl0
  have hy : (ylZ.toNat : ℤ) = ylZ := Int.toNat_of_nonneg hyl0
  omega

lemma par_00_int (u v S d : ℕ) (s : Bool) (h1 : (u + v) % 2 = (S + s.toNat) % 2)
    (h2 : d % 2 = S % 2) : ((u : ℤ) + (v : ℤ) - (d : ℤ)) % 2 = (s.toNat : ℤ) := by
  cases s <;> simp at h1 ⊢ <;> omega

lemma par_11_int (u v A B S d : ℕ) (s : Bool) (h1 : (u + v) % 2 = (S + s.toNat) % 2)
    (h2 : d % 2 = (A + B + S) % 2) : ((u : ℤ) + (v : ℤ) - (A : ℤ) - (B : ℤ) + (d : ℤ)) % 2 = (s.toNat : ℤ) := by
  cases s <;> simp at h1 ⊢ <;> omega

lemma par_01_int (u v B S d : ℕ) (s : Bool) (h1 : (u + v) % 2 = (S + s.toNat) % 2)
    (h2 : d % 2 = (B + S) % 2) : ((u : ℤ) - (v : ℤ) + (B : ℤ) - (d : ℤ)) % 2 = (s.toNat : ℤ) := by
  cases s <;> simp at h1 ⊢ <;> omega

lemma par_10_int (u v A S d : ℕ) (s : Bool) (h1 : (u + v) % 2 = (S + s.toNat) % 2)
    (h2 : d % 2 = (A + S) % 2) : ((u : ℤ) - (v : ℤ) - (A : ℤ) + (d : ℤ)) % 2 = (s.toNat : ℤ) := by
  cases s <;> simp at h1 ⊢ <;> omega

lemma backward_dir (m : ℕ) :
    ∀ (a b : Fin m → ℕ) (s : Fin m → Bool),
      (∀ i, 0 < a i ∧ 0 < b i) →
      ∀ u v : ℕ,
        let A := ∑ i : Fin m, a i
        let B := ∑ i : Fin m, b i
        u ≤ A ∧ v ≤ B ∧ (u + v) % 2 = (∑ i : Fin m, (s i).toNat) % 2 ∧
        (∀ right top : Bool, defectVal a b s right top ≤
          (if right then A - u else u) + (if top then B - v else v)) →
        ∃ x y : Fin m → ℕ,
          (∀ i, x i ≤ a i ∧ y i ≤ b i ∧ (x i + y i) % 2 = (s i).toNat) ∧
          (∑ i : Fin m, x i) = u ∧ (∑ i : Fin m, y i) = v := by
  induction m with
  | zero =>
    intro a b s _ u v
    dsimp only
    rintro ⟨hu, hv, _, _⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.le_zero] at hu hv
    subst hu; subst hv
    exact ⟨Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, rfl, rfl⟩
  | succ n ih =>
    intro a b s hpos u v
    dsimp only
    rintro ⟨huA, hvB, hpar, hdef⟩
    by_cases hn0 : n = 0
    · subst hn0
      have hsum1 : ∀ f : Fin (0 + 1) → ℕ, ∑ i : Fin (0 + 1), f i = f 0 := fun f => by
        rw [Fin.sum_univ_castSucc]; simp
      refine ⟨fun _ => u, fun _ => v, ?_, by rw [hsum1], by rw [hsum1]⟩
      intro i
      have hi : i = 0 := Fin.ext (by omega)
      subst hi
      rw [hsum1] at huA hvB hpar
      exact ⟨huA, hvB, hpar.trans (Nat.mod_eq_of_lt (by cases s 0 <;> decide))⟩
    · let a' : Fin n → ℕ := fun i => a i.castSucc
      let b' : Fin n → ℕ := fun i => b i.castSucc
      let s' : Fin n → Bool := fun i => s i.castSucc
      let al := a (Fin.last n)
      let bl := b (Fin.last n)
      let sl := s (Fin.last n)
      have hpos' : ∀ i : Fin n, 0 < a' i ∧ 0 < b' i := fun i => hpos i.castSucc
      let A : ℕ := ∑ i : Fin n, a' i
      let B : ℕ := ∑ i : Fin n, b' i
      have hA_eq : ∑ i : Fin (n + 1), a i = A + al := Fin.sum_univ_castSucc a
      have hB_eq : ∑ i : Fin (n + 1), b i = B + bl := Fin.sum_univ_castSucc b
      have hS_eq : ∑ i : Fin (n + 1), (s i).toNat = (∑ i : Fin n, (s' i).toNat) + sl.toNat :=
        Fin.sum_univ_castSucc (fun i => (s i).toNat)
      have hA_pos : 1 ≤ A := by
        have h0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn0⟩
        calc 1 ≤ a' h0 := (hpos' h0).1
          _ ≤ ∑ i : Fin n, a' i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ h0)
      have hB_pos : 1 ≤ B := by
        have h0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn0⟩
        calc 1 ≤ b' h0 := (hpos' h0).2
          _ ≤ ∑ i : Fin n, b' i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ h0)
      have hdef_split : ∀ right top : Bool,
          defectVal a b s right top = defectVal a' b' s' right top +
            if ((if right then al else 0) + (if top then bl else 0)) % 2 ≠ sl.toNat then 1 else 0 := by
        intro right top
        simp only [defectVal, Finset.card_filter, Fin.sum_univ_castSucc]
        rfl
      have hpair := defect_pair_bounds a' b' s' hpos'
      have hm00 : defectVal a' b' s' false false % 2 = (∑ i : Fin n, (s' i).toNat) % 2 := by
        simpa using defect_mod2 a' b' s' false false
      have hm01 : defectVal a' b' s' false true % 2 = (B + ∑ i : Fin n, (s' i).toNat) % 2 := by
        simpa [B] using defect_mod2 a' b' s' false true
      have hm10 : defectVal a' b' s' true false % 2 = (A + ∑ i : Fin n, (s' i).toNat) % 2 := by
        simpa [A] using defect_mod2 a' b' s' true false
      have hm11 : defectVal a' b' s' true true % 2 = (A + B + ∑ i : Fin n, (s' i).toNat) % 2 := by
        simpa [A, B] using defect_mod2 a' b' s' true true
      have hc00_nat := hdef false false
      have hc01_nat := hdef false true
      have hc10_nat := hdef true false
      have hc11_nat := hdef true true
      rw [hdef_split false false, hA_eq, hB_eq] at hc00_nat
      rw [hdef_split false true, hA_eq, hB_eq] at hc01_nat
      rw [hdef_split true false, hA_eq, hB_eq] at hc10_nat
      rw [hdef_split true true, hA_eq, hB_eq] at hc11_nat
      rw [hA_eq] at huA
      rw [hB_eq] at hvB
      rw [hS_eq] at hpar
      simp only [Bool.false_eq_true, ↓reduceIte, zero_add, add_zero] at hc00_nat hc01_nat hc10_nat hc11_nat
      have hal : 1 ≤ al := (hpos (Fin.last n)).1
      have hbl : 1 ≤ bl := (hpos (Fin.last n)).2
      let S : ℕ := ∑ i : Fin n, (s' i).toNat
      have hpar' : (u + v) % 2 = (S + sl.toNat) % 2 := hpar
      have hm00' : defectVal a' b' s' false false % 2 = S % 2 := hm00
      have hm01' : defectVal a' b' s' false true % 2 = (B + S) % 2 := hm01
      have hm10' : defectVal a' b' s' true false % 2 = (A + S) % 2 := hm10
      have hm11' : defectVal a' b' s' true true % 2 = (A + B + S) % 2 := hm11
      have hc00_z : (defectVal a' b' s' false false : ℤ) + (if (0 : ℤ) % 2 ≠ (sl.toNat : ℤ) then 1 else 0) ≤ (u : ℤ) + (v : ℤ) := by
        simpa [Nat.cast_add] using cast_corner_le (defectVal a' b' s' false false) 0 (u + v) sl hc00_nat
      have hc01_z : (defectVal a' b' s' false true : ℤ) + (if (bl : ℤ) % 2 ≠ (sl.toNat : ℤ) then 1 else 0) ≤ (u : ℤ) + ((B : ℤ) + (bl : ℤ) - (v : ℤ)) := by
        have h := cast_corner_le (defectVal a' b' s' false true) bl (u + (B + bl - v)) sl hc01_nat
        rwa [cast_add_sub_nat u B bl v hvB] at h
      have hc10_z : (defectVal a' b' s' true false : ℤ) + (if (al : ℤ) % 2 ≠ (sl.toNat : ℤ) then 1 else 0) ≤ ((A : ℤ) + (al : ℤ) - (u : ℤ)) + (v : ℤ) := by
        have h := cast_corner_le (defectVal a' b' s' true false) al ((A + al - u) + v) sl hc10_nat
        rwa [cast_sub_add_nat A al u v huA] at h
      have hc11_z : (defectVal a' b' s' true true : ℤ) + (if ((al : ℤ) + (bl : ℤ)) % 2 ≠ (sl.toNat : ℤ) then 1 else 0) ≤ ((A : ℤ) + (al : ℤ) - (u : ℤ)) + ((B : ℤ) + (bl : ℤ) - (v : ℤ)) := by
        have h := cast_corner_le (defectVal a' b' s' true true) (al + bl) ((A + al - u) + (B + bl - v)) sl hc11_nat
        rw [cast_sub_add_sub_nat A al u B bl v huA hvB, Nat.cast_add] at h
        exact h
      have hstep := backward_step_int (A : ℤ) (B : ℤ) (al : ℤ) (bl : ℤ) (u : ℤ) (v : ℤ)
        (defectVal a' b' s' false false : ℤ) (defectVal a' b' s' false true : ℤ)
        (defectVal a' b' s' true false : ℤ) (defectVal a' b' s' true true : ℤ) sl
        (by exact_mod_cast hA_pos) (by exact_mod_cast hB_pos)
        (by exact_mod_cast hal) (by exact_mod_cast hbl)
        (by positivity) (by exact_mod_cast huA) (by positivity) (by exact_mod_cast hvB)
        (by exact_mod_cast hpair.1) (by exact_mod_cast hpair.2.1)
        (by exact_mod_cast hpair.2.2.1) (by exact_mod_cast hpair.2.2.2)
        (by positivity) (by positivity) (by positivity) (by positivity)
        (par_00_int u v S (defectVal a' b' s' false false) sl hpar' hm00')
        (par_11_int u v A B S (defectVal a' b' s' true true) sl hpar' hm11')
        (par_01_int u v B S (defectVal a' b' s' false true) sl hpar' hm01')
        (par_10_int u v A S (defectVal a' b' s' true false) sl hpar' hm10')
        hc00_z hc01_z hc10_z hc11_z
      rcases hstep with ⟨xlZ, ylZ, hxl0, hxlA, hyl0, hylB, hparl, hux0, huxA, hvy0, hvyB,
        hd00', hd01', hd10', hd11'⟩
      have htr := step_nat_transfer A B al bl u v
        (defectVal a' b' s' false false) (defectVal a' b' s' false true)
        (defectVal a' b' s' true false) (defectVal a' b' s' true true)
        S sl xlZ ylZ hxl0 hxlA hyl0 hylB hparl hux0 huxA hvy0 hvyB
        hd00' hd01' hd10' hd11' hpar'
      rcases htr with ⟨hxl_le, hyl_le, hparl_nat, hxl_u, hyl_v, hux_le, hvy_le, hpar_rem,
        hd00_n, hd01_n, hd10_n, hd11_n⟩
      let xl : ℕ := xlZ.toNat
      let yl : ℕ := ylZ.toNat
      have hih := ih a' b' s' hpos' (u - xl) (v - yl) ⟨hux_le, hvy_le, hpar_rem, ?_⟩
      · rcases hih with ⟨x', y', hxy', hxsum, hysum⟩
        refine ⟨Fin.snoc x' xl, Fin.snoc y' yl, ?_, ?_, ?_⟩
        · intro i
          refine Fin.lastCases ?_ ?_ i
          · simp only [Fin.snoc_last]
            exact ⟨hxl_le, hyl_le, hparl_nat⟩
          · intro j
            simp only [Fin.snoc_castSucc]
            exact hxy' j
        · rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
          rw [hxsum]; exact Nat.sub_add_cancel hxl_u
        · rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
          rw [hysum]; exact Nat.sub_add_cancel hyl_v
      · intro right top
        cases right <;> cases top <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · exact hd00_n
        · exact hd01_n
        · exact hd10_n
        · exact hd11_n

end PEqualNP.Outside.L_lib_846_aux

theorem PEqualNP.Outside.L_lib_846 :
∀ (m : ℕ) (a b : Fin m → ℕ) (s : Fin m → Bool),
  (∀ i, 0 < a i ∧ 0 < b i) →
  let A := ∑ i : Fin m, a i
  let B := ∑ i : Fin m, b i
  let defect := fun (right top : Bool) =>
    (Finset.univ.filter (fun i : Fin m =>
      ((if right then a i else 0) + (if top then b i else 0)) % 2 ≠ (s i).toNat)).card
  ∀ u v : ℕ,
    (∃ x y : Fin m → ℕ,
      (∀ i, x i ≤ a i ∧ y i ≤ b i ∧ (x i + y i) % 2 = (s i).toNat) ∧
      (∑ i : Fin m, x i) = u ∧ (∑ i : Fin m, y i) = v) ↔
    u ≤ A ∧ v ≤ B ∧ (u+v)%2 = (∑ i : Fin m, (s i).toNat)%2 ∧
    ∀ right top : Bool, defect right top ≤
      (if right then A-u else u) + (if top then B-v else v) := by
  intro m a b s hpos
  dsimp only
  intro u v
  constructor
  · rintro ⟨x, y, hxy, hu, hv⟩
    exact PEqualNP.Outside.L_lib_846_aux.forward_dir a b s u v x y hxy hu hv
  · intro h
    exact PEqualNP.Outside.L_lib_846_aux.backward_dir m a b s hpos u v h
