import PEqualNP.Defs
import Mathlib.Data.Nat.Dist

namespace PEqualNP.Outside.L_lib_595_aux

lemma natDist_sq_int (a b : ℕ) : ((Nat.dist a b : ℕ) : ℤ) ^ 2 = ((a : ℤ) - (b : ℤ)) ^ 2 := by
  by_cases h : a ≤ b
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h]
    ring
  · have hle : b ≤ a := by omega
    rw [Nat.dist_eq_sub_of_le_right hle, Nat.cast_sub hle]

lemma sum_fin_val (Q : ℕ) :
    2 * (∑ u : Fin Q, (u.val : ℤ)) = (Q : ℤ) * ((Q : ℤ) - 1) := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_succ]
    linarith

lemma sum_fin_val_sq (Q : ℕ) :
    6 * (∑ u : Fin Q, (u.val : ℤ) ^ 2) = (Q : ℤ) * ((Q : ℤ) - 1) * (2 * (Q : ℤ) - 1) := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_succ]
    linarith

def coordTerm (Q : ℕ) (u v : Fin Q) : ℤ :=
  6 * ((u.val : ℤ) - (v.val : ℤ)) ^ 2 - ((Q : ℤ) ^ 2 - 1)

lemma sum_coordTerm (Q : ℕ) :
    ∑ u : Fin Q, ∑ v : Fin Q, coordTerm Q u v = 0 := by
  have h1 := sum_fin_val Q
  have h2 := sum_fin_val_sq Q
  have hexp :
      ∑ u : Fin Q, ∑ v : Fin Q, ((u.val : ℤ) - (v.val : ℤ)) ^ 2 =
        2 * (Q : ℤ) * (∑ u : Fin Q, (u.val : ℤ) ^ 2) -
          2 * (∑ u : Fin Q, (u.val : ℤ)) ^ 2 := by
    have hsub : ∀ u v : Fin Q,
        ((u.val : ℤ) - (v.val : ℤ)) ^ 2 =
          (u.val : ℤ) ^ 2 - 2 * (u.val : ℤ) * (v.val : ℤ) + (v.val : ℤ) ^ 2 := by
      intro u v; ring
    simp_rw [hsub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hmul :
        ∑ u : Fin Q, ∑ v : Fin Q, 2 * (u.val : ℤ) * (v.val : ℤ) =
          2 * (∑ u : Fin Q, (u.val : ℤ)) ^ 2 := by
      have hinner : ∀ u : Fin Q,
          ∑ v : Fin Q, 2 * (u.val : ℤ) * (v.val : ℤ) =
            (2 * (u.val : ℤ)) * (∑ v : Fin Q, (v.val : ℤ)) := fun u => (Finset.mul_sum _ _ _).symm
      simp_rw [hinner, ← Finset.sum_mul, ← Finset.mul_sum]
      ring
    rw [hmul, ← Finset.mul_sum]
    ring
  have h6 : 6 * (∑ u : Fin Q, ∑ v : Fin Q, ((u.val : ℤ) - (v.val : ℤ)) ^ 2) =
      (Q : ℤ) ^ 2 * ((Q : ℤ) ^ 2 - 1) := by
    rw [hexp]
    nlinarith
  simp only [coordTerm, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

lemma coordTerm_sq_le (Q : ℕ) (u v : Fin Q) :
    (coordTerm Q u v) ^ 2 ≤ 36 * (Q : ℤ) ^ 4 := by
  dsimp only [coordTerm]
  have hu0 : (0 : ℤ) ≤ (u.val : ℤ) := Nat.cast_nonneg _
  have hv0 : (0 : ℤ) ≤ (v.val : ℤ) := Nat.cast_nonneg _
  have huQ : (u.val : ℤ) ≤ (Q : ℤ) := by exact_mod_cast le_of_lt u.isLt
  have hvQ : (v.val : ℤ) ≤ (Q : ℤ) := by exact_mod_cast le_of_lt v.isLt
  have hQ1 : (1 : ℤ) ≤ (Q : ℤ) := by
    have : 0 < Q := Nat.pos_of_ne_zero (fun h => by subst h; exact Fin.elim0 u)
    exact_mod_cast this
  have hd : ((u.val : ℤ) - (v.val : ℤ)) ^ 2 ≤ (Q : ℤ) ^ 2 := by nlinarith
  have hd0 : (0 : ℤ) ≤ ((u.val : ℤ) - (v.val : ℤ)) ^ 2 := sq_nonneg _
  have hlo : -(6 * (Q : ℤ) ^ 2) ≤ 6 * ((u.val : ℤ) - (v.val : ℤ)) ^ 2 - ((Q : ℤ) ^ 2 - 1) := by nlinarith
  have hhi : 6 * ((u.val : ℤ) - (v.val : ℤ)) ^ 2 - ((Q : ℤ) ^ 2 - 1) ≤ 6 * (Q : ℤ) ^ 2 := by nlinarith
  nlinarith

lemma sum_prod_offdiag_zero {m Q : ℕ} (j1 j2 : Fin m) (hne : j1 ≠ j2) :
    ∑ x : Fin m → Fin Q, ∑ y : Fin m → Fin Q,
      coordTerm Q (x j1) (y j1) * coordTerm Q (x j2) (y j2) = 0 := by
  let Other := { j : Fin m // j ≠ j1 } → Fin Q
  let e : (Fin m → Fin Q) ≃ Fin Q × Other :=
    { toFun := fun x => (x j1, fun j => x j.1)
      invFun := fun p j => if h : j = j1 then p.1 else p.2 ⟨j, h⟩
      left_inv := fun x => by
        funext j
        by_cases h : j = j1
        · subst j; simp
        · simp [h]
      right_inv := fun p => by
        refine Prod.ext (by simp) ?_
        funext j
        simp [j.2] }
  have hrew :
      ∑ x : Fin m → Fin Q, ∑ y : Fin m → Fin Q,
        coordTerm Q (x j1) (y j1) * coordTerm Q (x j2) (y j2) =
      ∑ px : Fin Q × Other, ∑ py : Fin Q × Other,
        coordTerm Q px.1 py.1 * coordTerm Q (px.2 ⟨j2, hne.symm⟩) (py.2 ⟨j2, hne.symm⟩) := by
    refine Fintype.sum_equiv e _ _ (fun x => ?_)
    refine Fintype.sum_equiv e _ _ (fun y => ?_)
    rfl
  rw [hrew]
  simp_rw [Fintype.sum_prod_type]
  have hswap :
      ∑ u : Fin Q, ∑ ox : Other, ∑ v : Fin Q, ∑ oy : Other,
        coordTerm Q u v * coordTerm Q (ox ⟨j2, hne.symm⟩) (oy ⟨j2, hne.symm⟩) =
      ∑ ox : Other, ∑ oy : Other,
        (∑ u : Fin Q, ∑ v : Fin Q, coordTerm Q u v) *
          coordTerm Q (ox ⟨j2, hne.symm⟩) (oy ⟨j2, hne.symm⟩) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ox _ => ?_)
    trans (∑ v : Fin Q, ∑ u : Fin Q, ∑ oy : Other,
        coordTerm Q u v * coordTerm Q (ox ⟨j2, hne.symm⟩) (oy ⟨j2, hne.symm⟩))
    · rw [Finset.sum_comm]
    · trans (∑ oy : Other, ∑ v : Fin Q, ∑ u : Fin Q,
          coordTerm Q u v * coordTerm Q (ox ⟨j2, hne.symm⟩) (oy ⟨j2, hne.symm⟩))
      · trans (∑ v : Fin Q, ∑ oy : Other, ∑ u : Fin Q,
            coordTerm Q u v * coordTerm Q (ox ⟨j2, hne.symm⟩) (oy ⟨j2, hne.symm⟩))
        · refine Finset.sum_congr rfl (fun v _ => Finset.sum_comm)
        · exact Finset.sum_comm
      · refine Finset.sum_congr rfl (fun oy _ => ?_)
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul]
  rw [hswap, sum_coordTerm]
  simp

lemma edges_card_lower (m b : ℕ) (hm : 0 < m) :
    let Q := 2 ^ b
    let X := Fin m → Fin Q
    let radius := 12 * Q ^ 2 * (Nat.sqrt m + 1)
    let center := m * (Q ^ 2 - 1)
    let dist := fun (x y : X) => ∑ j : Fin m, (Nat.dist (x j).val (y j).val) ^ 2
    let edges := Finset.univ.filter (fun p : X × X => Nat.dist (6 * dist p.1 p.2) center ≤ radius)
    2 ^ (2 * m * b) ≤ 2 * edges.card := by
  dsimp only
  let Q := 2 ^ b
  let X := Fin m → Fin Q
  let radius := 12 * Q ^ 2 * (Nat.sqrt m + 1)
  let center := m * (Q ^ 2 - 1)
  let dist : X → X → ℕ := fun x y => ∑ j : Fin m, (Nat.dist (x j).val (y j).val) ^ 2
  let edges : Finset (X × X) :=
    Finset.univ.filter (fun p => Nat.dist (6 * dist p.1 p.2) center ≤ radius)
  let bad : Finset (X × X) :=
    Finset.univ.filter (fun p => ¬ Nat.dist (6 * dist p.1 p.2) center ≤ radius)
  have hQpos : 1 ≤ Q := Nat.one_le_two_pow
  have hQ2 : 1 ≤ Q ^ 2 := by nlinarith
  have hG_eq : ∀ x y : X,
      ∑ j : Fin m, coordTerm Q (x j) (y j) = (6 * dist x y : ℤ) - (center : ℤ) := by
    intro x y
    simp only [coordTerm, dist, center, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Nat.cast_mul, Nat.cast_sub hQ2]
    simp only [Nat.cast_pow, Nat.cast_one, Nat.cast_sum]
    have hsum_eq :
        ∑ j : Fin m, ((x j).val - (y j).val : ℤ) ^ 2 =
          ∑ j : Fin m, ((Nat.dist (x j).val (y j).val : ℤ) ^ 2) := by
      refine Finset.sum_congr rfl (fun j _ => (natDist_sq_int (x j).val (y j).val).symm)
    rw [hsum_eq]
    ring
  have hcardX : Fintype.card X = 2 ^ (m * b) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul, mul_comm]
  have hcardXX : Fintype.card (X × X) = 2 ^ (2 * m * b) := by
    rw [Fintype.card_prod, hcardX, ← pow_add]
    congr 1
    ring
  have hvar :
      ∑ p : X × X, ((6 * dist p.1 p.2 : ℤ) - (center : ℤ)) ^ 2 ≤
        (m : ℤ) * (2 ^ (2 * m * b) : ℤ) * (36 * (Q : ℤ) ^ 4) := by
    have hsq : ∀ p : X × X,
        ((6 * dist p.1 p.2 : ℤ) - (center : ℤ)) ^ 2 =
          ∑ j1 : Fin m, ∑ j2 : Fin m, coordTerm Q (p.1 j1) (p.2 j1) * coordTerm Q (p.1 j2) (p.2 j2) := by
      intro p
      rw [← hG_eq p.1 p.2, sq, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j1 _ => Finset.mul_sum _ _ _)
    simp_rw [hsq]
    rw [Fintype.sum_prod_type]
    have hswap' :
        ∑ x : X, ∑ y : X, ∑ j1 : Fin m, ∑ j2 : Fin m,
          coordTerm Q (x j1) (y j1) * coordTerm Q (x j2) (y j2) =
        ∑ j1 : Fin m, ∑ j2 : Fin m, ∑ x : X, ∑ y : X,
          coordTerm Q (x j1) (y j1) * coordTerm Q (x j2) (y j2) := by
      trans (∑ x : X, ∑ j1 : Fin m, ∑ y : X, ∑ j2 : Fin m,
          coordTerm Q (x j1) (y j1) * coordTerm Q (x j2) (y j2))
      · refine Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j1 _ => ?_)
        trans (∑ x : X, ∑ j2 : Fin m, ∑ y : X,
            coordTerm Q (x j1) (y j1) * coordTerm Q (x j2) (y j2))
        · refine Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
        · exact Finset.sum_comm
    rw [hswap']
    have hdiag : ∀ j1 : Fin m,
        ∑ j2 : Fin m, ∑ x : X, ∑ y : X,
          coordTerm Q (x j1) (y j1) * coordTerm Q (x j2) (y j2) =
        ∑ x : X, ∑ y : X, (coordTerm Q (x j1) (y j1)) ^ 2 := by
      intro j1
      rw [Finset.sum_eq_single j1]
      · simp_rw [sq]
      · intro j2 _ hne
        exact sum_prod_offdiag_zero j1 j2 hne.symm
      · intro h; exact absurd (Finset.mem_univ j1) h
    simp_rw [hdiag]
    have hle1 : ∀ j1 : Fin m,
        ∑ x : X, ∑ y : X, (coordTerm Q (x j1) (y j1)) ^ 2 ≤
          (2 ^ (2 * m * b) : ℤ) * (36 * (Q : ℤ) ^ 4) := by
      intro j1
      calc ∑ x : X, ∑ y : X, (coordTerm Q (x j1) (y j1)) ^ 2
          ≤ ∑ _x : X, ∑ _y : X, (36 * (Q : ℤ) ^ 4) :=
            Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => coordTerm_sq_le Q (x j1) (y j1)))
        _ = (Fintype.card X : ℤ) * ((Fintype.card X : ℤ) * (36 * (Q : ℤ) ^ 4)) := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = (2 ^ (2 * m * b) : ℤ) * (36 * (Q : ℤ) ^ 4) := by
            rw [hcardX]
            push_cast
            rw [← mul_assoc, ← pow_add]
            congr 2
            ring
    calc ∑ j1 : Fin m, ∑ x : X, ∑ y : X, (coordTerm Q (x j1) (y j1)) ^ 2
        ≤ ∑ _j1 : Fin m, (2 ^ (2 * m * b) : ℤ) * (36 * (Q : ℤ) ^ 4) :=
          Finset.sum_le_sum (fun j1 _ => hle1 j1)
      _ = (m : ℤ) * ((2 ^ (2 * m * b) : ℤ) * (36 * (Q : ℤ) ^ 4)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (m : ℤ) * (2 ^ (2 * m * b) : ℤ) * (36 * (Q : ℤ) ^ 4) := by ring
  have hbad_le : (bad.card : ℤ) * (radius : ℤ) ^ 2 ≤
      (m : ℤ) * (2 ^ (2 * m * b) : ℤ) * (36 * (Q : ℤ) ^ 4) := by
    calc (bad.card : ℤ) * (radius : ℤ) ^ 2
        = ∑ _p ∈ bad, (radius : ℤ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ bad, ((6 * dist p.1 p.2 : ℤ) - (center : ℤ)) ^ 2 := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hgt : radius < Nat.dist (6 * dist p.1 p.2) center := by
            have := (Finset.mem_filter.mp hp).2
            omega
          have hsq := natDist_sq_int (6 * dist p.1 p.2) center
          have hle_z : (radius : ℤ) ≤ (Nat.dist (6 * dist p.1 p.2) center : ℤ) := by
            exact_mod_cast le_of_lt hgt
          have hr0 : (0 : ℤ) ≤ (radius : ℤ) := Nat.cast_nonneg _
          have hcast : ((6 * dist p.1 p.2 : ℕ) : ℤ) = (6 * dist p.1 p.2 : ℤ) := by push_cast; rfl
          rw [← hcast, ← hsq]
          nlinarith
      _ ≤ ∑ p : X × X, ((6 * dist p.1 p.2 : ℤ) - (center : ℤ)) ^ 2 := by
          refine Finset.sum_le_univ_sum_of_nonneg (fun p => sq_nonneg _)
      _ ≤ (m : ℤ) * (2 ^ (2 * m * b) : ℤ) * (36 * (Q : ℤ) ^ 4) := hvar
  have hsqrt : (m : ℤ) ≤ ((Nat.sqrt m + 1 : ℕ) : ℤ) ^ 2 := by
    have h1 : m ≤ (Nat.sqrt m + 1) ^ 2 := by
      have := Nat.lt_succ_sqrt m
      rw [sq]
      exact le_of_lt this
    exact_mod_cast h1
  have hrad_sq : 2 * ((m : ℤ) * (36 * (Q : ℤ) ^ 4)) ≤ (radius : ℤ) ^ 2 := by
    have hr : (radius : ℤ) = 12 * (Q : ℤ) ^ 2 * ((Nat.sqrt m + 1 : ℕ) : ℤ) := by
      dsimp only [radius]; push_cast; ring
    rw [hr]
    have hQ4 : (0 : ℤ) ≤ (Q : ℤ) ^ 4 := by positivity
    nlinarith
  have hrad_pos : (0 : ℤ) < (radius : ℤ) ^ 2 := by
    have : 0 < radius := by dsimp only [radius]; positivity
    have : (0 : ℤ) < (radius : ℤ) := by exact_mod_cast this
    positivity
  have h2bad_z : (2 * (bad.card : ℤ)) * (radius : ℤ) ^ 2 ≤ (2 ^ (2 * m * b) : ℤ) * (radius : ℤ) ^ 2 := by
    have hpow0 : (0 : ℤ) ≤ (2 ^ (2 * m * b) : ℤ) := by positivity
    calc (2 * (bad.card : ℤ)) * (radius : ℤ) ^ 2
        = 2 * ((bad.card : ℤ) * (radius : ℤ) ^ 2) := by ring
      _ ≤ 2 * ((m : ℤ) * (2 ^ (2 * m * b) : ℤ) * (36 * (Q : ℤ) ^ 4)) := by linarith
      _ = (2 ^ (2 * m * b) : ℤ) * (2 * ((m : ℤ) * (36 * (Q : ℤ) ^ 4))) := by ring
      _ ≤ (2 ^ (2 * m * b) : ℤ) * (radius : ℤ) ^ 2 := mul_le_mul_of_nonneg_left hrad_sq hpow0
  have h2bad : 2 * bad.card ≤ 2 ^ (2 * m * b) := by
    have hle_z : 2 * (bad.card : ℤ) ≤ (2 ^ (2 * m * b) : ℤ) := by nlinarith
    exact_mod_cast hle_z
  have hsum_card : edges.card + bad.card = 2 ^ (2 * m * b) := by
    rw [← Finset.card_union_of_disjoint]
    · have hun : edges ∪ bad = Finset.univ := by
        ext p
        simp only [edges, bad, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact em _
      rw [hun, Finset.card_univ, hcardXX]
    · rw [Finset.disjoint_left]
      intro p h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  change 2 ^ (2 * m * b) ≤ 2 * edges.card
  omega

lemma card_matrices_annihilating {α : Type*} [Fintype α] [DecidableEq α] {f : ℕ}
    (w : α → ZMod 2) (hw : w ≠ 0) :
    ((Finset.univ : Finset (Matrix (Fin f) α (ZMod 2))).filter
      (fun M => M.mulVec w = 0)).card * 2 ^ f =
      Fintype.card (Matrix (Fin f) α (ZMod 2)) := by
  have hex : ∃ j0 : α, w j0 ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hw (funext hall)
  obtain ⟨j0, hj0⟩ := hex
  have hwj0 : w j0 = 1 := by
    rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 by decide) (w j0) with h | h
    · exact absurd h hj0
    · exact h
  let Other := Matrix (Fin f) { j : α // j ≠ j0 } (ZMod 2)
  let e : Matrix (Fin f) α (ZMod 2) ≃ Other × (Fin f → ZMod 2) :=
    { toFun := fun M => (fun i j => M i j.1, M.mulVec w)
      invFun := fun p i j =>
        if h : j = j0 then
          p.2 i - ∑ k : { k : α // k ≠ j0 }, p.1 i k * w k.1
        else p.1 i ⟨j, h⟩
      left_inv := fun M => by
        ext i j
        by_cases h : j = j0
        · subst j
          simp only [↓reduceDIte, Matrix.mulVec, dotProduct]
          have hsum :
              ∑ k : α, M i k * w k =
                M i j0 + ∑ k : { k : α // k ≠ j0 }, M i k.1 * w k.1 := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0), hwj0, mul_one]
            congr 1
            refine Finset.sum_bij (fun k hk => ⟨k, Finset.ne_of_mem_erase hk⟩)
              (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
            · intro k1 _ k2 _ heq
              exact congrArg Subtype.val heq
            · intro k _
              exact ⟨k.1, Finset.mem_erase.mpr ⟨k.2, Finset.mem_univ _⟩, rfl⟩
          rw [hsum]
          ring
        · simp [h]
      right_inv := fun p => by
        refine Prod.ext (by ext i j; simp [j.2]) ?_
        ext i
        simp only [Matrix.mulVec, dotProduct]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0), hwj0, mul_one]
        simp only [↓reduceDIte]
        have hsum :
            ∑ k ∈ Finset.univ.erase j0,
              (if h : k = j0 then p.2 i - ∑ k : { k : α // k ≠ j0 }, p.1 i k * w k.1
                else p.1 i ⟨k, h⟩) * w k =
            ∑ k : { k : α // k ≠ j0 }, p.1 i k * w k.1 := by
          refine Finset.sum_bij (fun k hk => ⟨k, Finset.ne_of_mem_erase hk⟩)
            (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
          · intro k1 _ k2 _ heq
            exact congrArg Subtype.val heq
          · intro k _
            exact ⟨k.1, Finset.mem_erase.mpr ⟨k.2, Finset.mem_univ _⟩, rfl⟩
          · intro k hk
            have hne : k ≠ j0 := Finset.ne_of_mem_erase hk
            simp [hne]
        rw [hsum]
        ring }
  have hfib :
      ((Finset.univ : Finset (Matrix (Fin f) α (ZMod 2))).filter
        (fun M => M.mulVec w = 0)).card = Fintype.card Other := by
    trans (Finset.univ : Finset Other).card
    · refine Finset.card_bij (t := (Finset.univ : Finset Other))
        (fun M _ => (e M).1) (fun _ _ => Finset.mem_univ _) ?_ ?_
      · intro M1 hM1 M2 hM2 heq
        have h1 : (e M1).2 = 0 := (Finset.mem_filter.mp hM1).2
        have h2 : (e M2).2 = 0 := (Finset.mem_filter.mp hM2).2
        exact e.injective (Prod.ext heq (h1.trans h2.symm))
      · intro A _
        refine ⟨e.symm (A, 0), ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact congrArg Prod.snd (e.apply_symm_apply (A, 0))
    · simp
  rw [hfib]
  have hcard := Fintype.card_congr e
  rw [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin] at hcard
  exact hcard.symm

lemma exists_detecting_linear {α : Type*} [Fintype α] [DecidableEq α] {f : ℕ}
    (S : Finset (α → ZMod 2)) (h0 : ∀ w ∈ S, w ≠ 0) (hcard : S.card < 2 ^ f) :
    ∃ H : (α → ZMod 2) →ₗ[ZMod 2] (Fin f → ZMod 2), ∀ w ∈ S, H w ≠ 0 := by
  let Bad : Finset (Matrix (Fin f) α (ZMod 2)) :=
    Finset.univ.filter (fun M => ∃ w ∈ S, M.mulVec w = 0)
  have hBad_sub : Bad ⊆ S.biUnion (fun w =>
      (Finset.univ : Finset (Matrix (Fin f) α (ZMod 2))).filter (fun M => M.mulVec w = 0)) := by
    intro M hM
    simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hM ⊢
    exact hM
  have hBad_mul :
      Bad.card * 2 ^ f ≤ S.card * Fintype.card (Matrix (Fin f) α (ZMod 2)) := by
    calc Bad.card * 2 ^ f
        ≤ (S.biUnion (fun w =>
            (Finset.univ : Finset (Matrix (Fin f) α (ZMod 2))).filter
              (fun M => M.mulVec w = 0))).card * 2 ^ f :=
          Nat.mul_le_mul_right _ (Finset.card_le_card hBad_sub)
      _ ≤ (∑ w ∈ S, ((Finset.univ : Finset (Matrix (Fin f) α (ZMod 2))).filter
            (fun M => M.mulVec w = 0)).card) * 2 ^ f :=
          Nat.mul_le_mul_right _ Finset.card_biUnion_le
      _ = ∑ w ∈ S, ((Finset.univ : Finset (Matrix (Fin f) α (ZMod 2))).filter
            (fun M => M.mulVec w = 0)).card * 2 ^ f := Finset.sum_mul _ _ _
      _ = ∑ _w ∈ S, Fintype.card (Matrix (Fin f) α (ZMod 2)) :=
          Finset.sum_congr rfl (fun w hw => card_matrices_annihilating w (h0 w hw))
      _ = S.card * Fintype.card (Matrix (Fin f) α (ZMod 2)) := by
          rw [Finset.sum_const, smul_eq_mul]
  have htot_pos : 0 < Fintype.card (Matrix (Fin f) α (ZMod 2)) := by
    have : Nonempty (Matrix (Fin f) α (ZMod 2)) := ⟨0⟩
    exact Fintype.card_pos
  have hlt : Bad.card < Fintype.card (Matrix (Fin f) α (ZMod 2)) := by
    have hmul : Bad.card * 2 ^ f < Fintype.card (Matrix (Fin f) α (ZMod 2)) * 2 ^ f := by
      calc Bad.card * 2 ^ f
          ≤ S.card * Fintype.card (Matrix (Fin f) α (ZMod 2)) := hBad_mul
        _ < 2 ^ f * Fintype.card (Matrix (Fin f) α (ZMod 2)) :=
            Nat.mul_lt_mul_of_pos_right hcard htot_pos
        _ = Fintype.card (Matrix (Fin f) α (ZMod 2)) * 2 ^ f := mul_comm _ _
    exact Nat.lt_of_mul_lt_mul_right hmul
  have hex : ∃ M : Matrix (Fin f) α (ZMod 2), M ∉ Bad := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset (Matrix (Fin f) α (ZMod 2))) ⊆ Bad := fun M _ => hall M
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ] at hle
    omega
  obtain ⟨M, hM⟩ := hex
  refine ⟨Matrix.mulVecLin M, fun w hw hzero => ?_⟩
  exact hM (Finset.mem_filter.mpr ⟨Finset.mem_univ M, w, hw, hzero⟩)

lemma sparse_card_lt (m b radius : ℕ) :
    let Q := 2 ^ b
    let f := 1 + radius * Nat.clog 2 (m * Q + 1)
    let B : Finset ((Fin m × Fin b) → ZMod 2) :=
      Finset.univ.filter (fun w =>
        w ≠ 0 ∧ (Finset.univ.filter (fun j : Fin m => ∃ i : Fin b, w (j, i) ≠ 0)).card ≤ radius)
    B.card < 2 ^ f := by
  dsimp only
  let Q := 2 ^ b
  let B : Finset ((Fin m × Fin b) → ZMod 2) :=
    Finset.univ.filter (fun w =>
      w ≠ 0 ∧ (Finset.univ.filter (fun j : Fin m => ∃ i : Fin b, w (j, i) ≠ 0)).card ≤ radius)
  let supp : ((Fin m × Fin b) → ZMod 2) → Finset (Fin m) :=
    fun w => Finset.univ.filter (fun j : Fin m => ∃ i : Fin b, w (j, i) ≠ 0)
  let enc : ((Fin m × Fin b) → ZMod 2) → (Fin radius → Option (Fin m × (Fin b → ZMod 2))) :=
    fun w t =>
      let L := (supp w).sort (· ≤ ·)
      if h : t.val < L.length then some (L[t.val], fun i => w (L[t.val], i)) else none
  have hinj : Set.InjOn enc B := by
    intro w1 hw1 w2 hw2 heq
    have hlen1 : ((supp w1).sort (· ≤ ·)).length ≤ radius := by
      rw [Finset.length_sort]
      exact (Finset.mem_filter.mp hw1).2.2
    have hlen2 : ((supp w2).sort (· ≤ ·)).length ≤ radius := by
      rw [Finset.length_sort]
      exact (Finset.mem_filter.mp hw2).2.2
    funext ⟨j, i⟩
    by_cases h1 : j ∈ supp w1
    · have hmem : j ∈ (supp w1).sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr h1
      obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp hmem
      have hidx_r : idx < radius := lt_of_lt_of_le hidx hlen1
      have hpos := congrFun heq ⟨idx, hidx_r⟩
      simp only [enc, hidx, ↓reduceDIte] at hpos
      split_ifs at hpos with hidx2
      have hpair := Option.some.inj hpos
      have hj2 : ((supp w2).sort (· ≤ ·))[idx] = j := (congrArg Prod.fst hpair).symm.trans hget
      have hfn := congrArg Prod.snd hpair
      have hi := congrFun hfn i
      rw [hget, hj2] at hi
      exact hi
    · by_cases h2 : j ∈ supp w2
      · have hmem : j ∈ (supp w2).sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr h2
        obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp hmem
        have hidx_r : idx < radius := lt_of_lt_of_le hidx hlen2
        have hpos := congrFun heq ⟨idx, hidx_r⟩
        simp only [enc, hidx, ↓reduceDIte] at hpos
        split_ifs at hpos with hidx1
        have hpair := Option.some.inj hpos
        have hj1 : ((supp w1).sort (· ≤ ·))[idx] = j := (congrArg Prod.fst hpair).trans hget
        have hfn := congrArg Prod.snd hpair
        have hi := congrFun hfn i
        rw [hj1, hget] at hi
        exact hi
      · have hw1_0 : w1 (j, i) = 0 := by
          by_contra hne
          exact h1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hne⟩)
        have hw2_0 : w2 (j, i) = 0 := by
          by_contra hne
          exact h2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hne⟩)
        exact hw1_0.trans hw2_0.symm
  have hle : B.card ≤ (m * Q + 1) ^ radius := by
    have hcard := Finset.card_le_card_of_injOn enc (fun _ _ => Finset.mem_univ _) hinj
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_option, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_fin] at hcard
    exact hcard
  have hclog : m * Q + 1 ≤ 2 ^ Nat.clog 2 (m * Q + 1) :=
    Nat.le_pow_clog (by norm_num : 1 < 2) _
  have hpow : (m * Q + 1) ^ radius ≤ 2 ^ (radius * Nat.clog 2 (m * Q + 1)) := by
    calc (m * Q + 1) ^ radius
        ≤ (2 ^ Nat.clog 2 (m * Q + 1)) ^ radius := Nat.pow_le_pow_left hclog radius
      _ = 2 ^ (Nat.clog 2 (m * Q + 1) * radius) := (pow_mul _ _ _).symm
      _ = 2 ^ (radius * Nat.clog 2 (m * Q + 1)) := by rw [mul_comm]
  have hlt : 2 ^ (radius * Nat.clog 2 (m * Q + 1)) < 2 ^ (1 + radius * Nat.clog 2 (m * Q + 1)) := by
    rw [add_comm 1, pow_succ]
    have hpos : 0 < 2 ^ (radius * Nat.clog 2 (m * Q + 1)) := by positivity
    omega
  change B.card < 2 ^ (1 + radius * Nat.clog 2 (m * Q + 1))
  omega

lemma cross_dist_identity {m Q : ℕ} (p1 p2 r1 r2 : Fin m → Fin Q)
    (hsum : ∀ j : Fin m, (p1 j).val + (p2 j).val = (r1 j).val + (r2 j).val) :
    (∑ j : Fin m, (Nat.dist (p1 j).val (r2 j).val) ^ 2) =
      (∑ j : Fin m, (Nat.dist (r1 j).val (p2 j).val) ^ 2) ∧
    ((∑ j : Fin m, (Nat.dist (p1 j).val (p2 j).val) ^ 2 : ℕ) : ℤ) +
      ((∑ j : Fin m, (Nat.dist (r1 j).val (r2 j).val) ^ 2 : ℕ) : ℤ) =
      2 * ((∑ j : Fin m, (Nat.dist (p1 j).val (r2 j).val) ^ 2 : ℕ) : ℤ) +
      2 * (∑ j : Fin m, (((p1 j).val : ℤ) - ((r1 j).val : ℤ)) ^ 2) := by
  constructor
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj : ((p1 j).val : ℤ) + ((p2 j).val : ℤ) = ((r1 j).val : ℤ) + ((r2 j).val : ℤ) := by
      exact_mod_cast hsum j
    have hsq : (((Nat.dist (p1 j).val (r2 j).val) ^ 2 : ℕ) : ℤ) =
        (((Nat.dist (r1 j).val (p2 j).val) ^ 2 : ℕ) : ℤ) := by
      rw [Nat.cast_pow, Nat.cast_pow, natDist_sq_int, natDist_sq_int]
      have hdiff : ((p1 j).val : ℤ) - ((r2 j).val : ℤ) = ((r1 j).val : ℤ) - ((p2 j).val : ℤ) := by
        linarith
      rw [hdiff]
    exact_mod_cast hsq
  · simp only [Nat.cast_sum, Nat.cast_pow, natDist_sq_int, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj : ((p1 j).val : ℤ) + ((p2 j).val : ℤ) = ((r1 j).val : ℤ) + ((r2 j).val : ℤ) := by
      exact_mod_cast hsum j
    have hd : ((r2 j).val : ℤ) = ((p1 j).val : ℤ) + ((p2 j).val : ℤ) - ((r1 j).val : ℤ) := by
      linarith
    rw [hd]
    ring

end PEqualNP.Outside.L_lib_595_aux

theorem PEqualNP.Outside.L_lib_595 : (∀ (m b : ℕ), 0 < m → 0 < b →
  let Q := 2^b
  let X := Fin m → Fin Q
  let radius := 12*Q^2*(Nat.sqrt m + 1)
  let center := m*(Q^2-1)
  let dist := fun (x y : X) => ∑ j : Fin m, (Nat.dist (x j).val (y j).val)^2
  let edges := Finset.univ.filter (fun p : X × X => Nat.dist (6*dist p.1 p.2) center ≤ radius)
  let f := 1 + radius * Nat.clog 2 (m*Q+1)
  let vec := fun (x : X) (j : Fin m × Fin b) => if (x j.1).val.testBit j.2.val then
    (1 : ZMod 2) else 0
  2^(2*m*b) ≤ 2*edges.card ∧
    ∃ H : ((Fin m × Fin b) → ZMod 2) →ₗ[ZMod 2] (Fin f → ZMod 2),
      (∀ x y : X, x ≠ y → (Finset.univ.filter (fun j : Fin m => x j ≠ y j)).card ≤ radius →
        H (vec x) ≠ H (vec y)) ∧
      ∀ p ∈ edges, ∀ r ∈ edges, p ≠ r →
        (∀ j : Fin m, (p.1 j).val + (p.2 j).val = (r.1 j).val + (r.2 j).val) →
        H (vec p.1) = H (vec r.1) →
          p.1 ≠ r.1 ∧ p.2 ≠ r.2 ∧ (p.1, r.2) ∉ edges ∧ (r.1, p.2) ∉ edges) := by
  intro m b hm hb
  dsimp only
  refine ⟨PEqualNP.Outside.L_lib_595_aux.edges_card_lower m b hm, ?_⟩
  let Q := 2 ^ b
  let X := Fin m → Fin Q
  let radius := 12 * Q ^ 2 * (Nat.sqrt m + 1)
  let center := m * (Q ^ 2 - 1)
  let dist : X → X → ℕ := fun x y => ∑ j : Fin m, (Nat.dist (x j).val (y j).val) ^ 2
  let edges : Finset (X × X) :=
    Finset.univ.filter (fun p => Nat.dist (6 * dist p.1 p.2) center ≤ radius)
  let f := 1 + radius * Nat.clog 2 (m * Q + 1)
  let vec : X → ((Fin m × Fin b) → ZMod 2) :=
    fun x j => if (x j.1).val.testBit j.2.val then (1 : ZMod 2) else 0
  let B : Finset ((Fin m × Fin b) → ZMod 2) :=
    Finset.univ.filter (fun w =>
      w ≠ 0 ∧ (Finset.univ.filter (fun j : Fin m => ∃ i : Fin b, w (j, i) ≠ 0)).card ≤ radius)
  have hB0 : ∀ w ∈ B, w ≠ 0 := fun w hw => (Finset.mem_filter.mp hw).2.1
  have hBcard : B.card < 2 ^ f := PEqualNP.Outside.L_lib_595_aux.sparse_card_lt m b radius
  obtain ⟨H, hH⟩ := PEqualNP.Outside.L_lib_595_aux.exists_detecting_linear B hB0 hBcard
  have hvec_inj : Function.Injective vec := by
    intro x y hxy
    funext j
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro t
    by_cases ht : t < b
    · have hbit := congrFun hxy (j, ⟨t, ht⟩)
      simp only [vec] at hbit
      rcases Bool.eq_false_or_eq_true ((x j).val.testBit t) with hx | hx <;>
        rcases Bool.eq_false_or_eq_true ((y j).val.testBit t) with hy | hy
      · rw [hx, hy]
      · rw [hx, hy] at hbit; exact absurd hbit (by decide)
      · rw [hx, hy] at hbit; exact absurd hbit (by decide)
      · rw [hx, hy]
    · have hx : (x j).val < 2 ^ t := lt_of_lt_of_le (x j).isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hy : (y j).val < 2 ^ t := lt_of_lt_of_le (y j).isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]
  have hdet : ∀ x y : X, x ≠ y → (Finset.univ.filter (fun j : Fin m => x j ≠ y j)).card ≤ radius →
      H (vec x) ≠ H (vec y) := by
    intro x y hxy hcard hHeq
    have hne0 : vec x - vec y ≠ 0 := by
      intro h0
      exact hxy (hvec_inj (sub_eq_zero.mp h0))
    have hsub :
        Finset.univ.filter (fun j : Fin m => ∃ i : Fin b, (vec x - vec y) (j, i) ≠ 0) ⊆
          Finset.univ.filter (fun j : Fin m => x j ≠ y j) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      intro heq
      obtain ⟨i, hi⟩ := hj
      apply hi
      simp only [Pi.sub_apply, vec, heq, sub_self]
    have hmem : vec x - vec y ∈ B :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne0, le_trans (Finset.card_le_card hsub) hcard⟩
    have hzero : H (vec x - vec y) = 0 := by
      rw [map_sub, hHeq, sub_self]
    exact hH _ hmem hzero
  refine ⟨H, hdet, fun p hp r hr hpr hsum hHpr => ?_⟩
  have hp1r1 : p.1 ≠ r.1 := by
    intro heq
    apply hpr
    refine Prod.ext heq ?_
    funext j
    have hj := hsum j
    rw [heq] at hj
    exact Fin.ext (by omega)
  have hp2r2 : p.2 ≠ r.2 := by
    intro heq
    apply hpr
    refine Prod.ext ?_ heq
    funext j
    have hj := hsum j
    rw [heq] at hj
    exact Fin.ext (by omega)
  have hdiff_gt : radius < (Finset.univ.filter (fun j : Fin m => p.1 j ≠ r.1 j)).card := by
    by_contra hle
    push Not at hle
    exact hdet p.1 r.1 hp1r1 hle hHpr
  obtain ⟨hcross_eq, hcross_id⟩ := PEqualNP.Outside.L_lib_595_aux.cross_dist_identity p.1 p.2 r.1 r.2 hsum
  have hsq_ge :
      ((Finset.univ.filter (fun j : Fin m => p.1 j ≠ r.1 j)).card : ℤ) ≤
        ∑ j : Fin m, (((p.1 j).val : ℤ) - ((r.1 j).val : ℤ)) ^ 2 := by
    calc ((Finset.univ.filter (fun j : Fin m => p.1 j ≠ r.1 j)).card : ℤ)
        = ∑ _j ∈ Finset.univ.filter (fun j : Fin m => p.1 j ≠ r.1 j), (1 : ℤ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin m => p.1 j ≠ r.1 j),
            (((p.1 j).val : ℤ) - ((r.1 j).val : ℤ)) ^ 2 := by
          refine Finset.sum_le_sum (fun j hj => ?_)
          have hne : p.1 j ≠ r.1 j := (Finset.mem_filter.mp hj).2
          have hne_z : ((p.1 j).val : ℤ) ≠ ((r.1 j).val : ℤ) := by
            intro h
            exact hne (Fin.ext (by exact_mod_cast h))
          have hdiff_ne : ((p.1 j).val : ℤ) - ((r.1 j).val : ℤ) ≠ 0 := sub_ne_zero.mpr hne_z
          have hpos : 0 < (((p.1 j).val : ℤ) - ((r.1 j).val : ℤ)) ^ 2 := sq_pos_of_ne_zero hdiff_ne
          omega
      _ ≤ ∑ j : Fin m, (((p.1 j).val : ℤ) - ((r.1 j).val : ℤ)) ^ 2 :=
          Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
  have hp_le : (6 * dist p.1 p.2 : ℤ) ≤ (center : ℤ) + (radius : ℤ) := by
    have h : Nat.dist (6 * dist p.1 p.2) center ≤ radius := (Finset.mem_filter.mp hp).2
    by_cases hge : center ≤ 6 * dist p.1 p.2
    · rw [Nat.dist_eq_sub_of_le_right hge] at h
      exact_mod_cast (show 6 * dist p.1 p.2 ≤ center + radius by omega)
    · exact_mod_cast (show 6 * dist p.1 p.2 ≤ center + radius by omega)
  have hr_le : (6 * dist r.1 r.2 : ℤ) ≤ (center : ℤ) + (radius : ℤ) := by
    have h : Nat.dist (6 * dist r.1 r.2) center ≤ radius := (Finset.mem_filter.mp hr).2
    by_cases hge : center ≤ 6 * dist r.1 r.2
    · rw [Nat.dist_eq_sub_of_le_right hge] at h
      exact_mod_cast (show 6 * dist r.1 r.2 ≤ center + radius by omega)
    · exact_mod_cast (show 6 * dist r.1 r.2 ≤ center + radius by omega)
  have hlt_cross : 6 * dist p.1 r.2 + radius < center := by
    have hgt_z : (radius : ℤ) + 1 ≤ ((Finset.univ.filter (fun j : Fin m => p.1 j ≠ r.1 j)).card : ℤ) := by
      exact_mod_cast hdiff_gt
    have hrad_pos : (0 : ℤ) < (radius : ℤ) := by
      have : 0 < radius := by dsimp only [radius]; positivity
      exact_mod_cast this
    have hlt_z : (6 * dist p.1 r.2 : ℤ) + (radius : ℤ) < (center : ℤ) := by
      dsimp only [dist] at hp_le hr_le ⊢
      linarith
    exact_mod_cast hlt_z
  refine ⟨hp1r1, hp2r2, ?_, ?_⟩
  · intro hmem
    have h : Nat.dist (6 * dist p.1 r.2) center ≤ radius := (Finset.mem_filter.mp hmem).2
    have hle : 6 * dist p.1 r.2 ≤ center := by omega
    rw [Nat.dist_eq_sub_of_le hle] at h
    omega
  · intro hmem
    have h : Nat.dist (6 * dist r.1 p.2) center ≤ radius := (Finset.mem_filter.mp hmem).2
    have hcross_eq' : dist r.1 p.2 = dist p.1 r.2 := hcross_eq.symm
    rw [hcross_eq'] at h
    have hle : 6 * dist p.1 r.2 ≤ center := by omega
    rw [Nat.dist_eq_sub_of_le hle] at h
    omega
