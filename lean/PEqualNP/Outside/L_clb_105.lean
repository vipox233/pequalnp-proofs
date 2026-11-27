import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_105_aux

abbrev Mat (α : Type) := α → α → ZMod 2

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

lemma zmod2_testBit0 (c : ℕ) (b : Bool) (h : (c : ZMod 2) = if b then 1 else 0) :
    c.testBit 0 = b := by
  rw [Nat.testBit_zero]
  have hmod : c % 2 = 0 ∨ c % 2 = 1 := by omega
  have hc : (c : ZMod 2) = ((c % 2 : ℕ) : ZMod 2) := (ZMod.natCast_mod c 2).symm
  rw [hc] at h
  rcases hmod with h0 | h1
  · rw [h0] at h ⊢
    cases b
    · rfl
    · exfalso; exact absurd h (by decide)
  · rw [h1] at h ⊢
    cases b
    · exfalso; exact absurd h (by decide)
    · rfl

section MatrixOps

variable {α : Type} [Fintype α] [DecidableEq α]

def matId : Mat α := fun x y => if x = y then 1 else 0

def matMul (A B : Mat α) : Mat α := fun x z => ∑ y : α, A x y * B y z

omit [DecidableEq α] in
lemma matMul_assoc (A B C : Mat α) : matMul (matMul A B) C = matMul A (matMul B C) := by
  funext x z
  simp only [matMul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro w _
  ring

lemma matMul_id_left (A : Mat α) : matMul matId A = A := by
  funext x z
  simp [matMul, matId]

lemma matMul_id_right (A : Mat α) : matMul A matId = A := by
  funext x z
  simp [matMul, matId]

def matProd : List (Mat α) → Mat α
  | [] => matId
  | M :: Ms => matMul M (matProd Ms)

lemma matProd_nil : matProd ([] : List (Mat α)) = matId := rfl

lemma matProd_cons (M : Mat α) (Ms : List (Mat α)) :
    matProd (M :: Ms) = matMul M (matProd Ms) := rfl

lemma matProd_append (L1 L2 : List (Mat α)) :
    matProd (L1 ++ L2) = matMul (matProd L1) (matProd L2) := by
  induction L1 with
  | nil => simp [matProd, matMul_id_left]
  | cons M rest ih => simp [matProd, ih, matMul_assoc]

lemma matProd_flatten (Ls : List (List (Mat α))) :
    matProd Ls.flatten = matProd (Ls.map matProd) := by
  induction Ls with
  | nil => rfl
  | cons L rest ih => simp [List.flatten_cons, matProd_append, ih, matProd_cons]

lemma matProd_replicate_id (m : ℕ) : matProd (List.replicate m (matId : Mat α)) = matId := by
  induction m with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, matProd_cons, ih, matMul_id_left]

def diagMat (R : α → Bool) : Mat α := fun x y => if x = y ∧ R x = true then 1 else 0

def transv (u v : α) : Mat α :=
  fun x y => (if x = y then 1 else 0) + (if x = u ∧ y = v then 1 else 0)

lemma matMul_transv_left (u v : α) (A : Mat α) :
    matMul (transv u v) A = fun x z => A x z + (if x = u then A v z else 0) := by
  funext x z
  simp only [matMul, transv, add_mul, Finset.sum_add_distrib]
  have h1 : (∑ y : α, (if x = y then (1 : ZMod 2) else 0) * A y z) = A x z := by
    simp
  have h2 : (∑ y : α, (if x = u ∧ y = v then (1 : ZMod 2) else 0) * A y z) =
      if x = u then A v z else 0 := by
    by_cases hxu : x = u
    · simp [hxu]
    · simp [hxu]
  rw [h1, h2]

lemma matMul_transv_right (u v : α) (A : Mat α) :
    matMul A (transv u v) = fun x z => A x z + (if z = v then A x u else 0) := by
  funext x z
  simp only [matMul, transv, mul_add, Finset.sum_add_distrib]
  have h1 : (∑ y : α, A x y * (if y = z then (1 : ZMod 2) else 0)) = A x z := by
    simp
  have h2 : (∑ y : α, A x y * (if y = u ∧ z = v then (1 : ZMod 2) else 0)) =
      if z = v then A x u else 0 := by
    by_cases hzv : z = v
    · simp [hzv]
    · simp [hzv]
  rw [h1, h2]

lemma transv_sq (u v : α) (huv : u ≠ v) : matMul (transv u v) (transv u v) = matId := by
  rw [matMul_transv_left]
  funext x z
  simp only [transv, matId]
  have hvu : v ≠ u := huv.symm
  by_cases hxu : x = u
  · rw [hxu]
    by_cases hvz : v = z
    · rw [← hvz]
      simp [huv, hvu, zmod2_add_self]
    · simp [hvu, hvz, Ne.symm hvz]
  · simp [hxu]

def swapFun (u v x : α) : α := if x = u then v else if x = v then u else x

omit [Fintype α] in
lemma swapFun_invol (u v x : α) : swapFun u v (swapFun u v x) = x := by
  unfold swapFun
  by_cases h1 : x = u
  · rw [h1]
    by_cases h2 : v = u <;> simp [h2]
  · by_cases h2 : x = v
    · rw [h2]; simp
    · simp [h1, h2]

omit [Fintype α] in
lemma swapFun_eq_iff (u v x y : α) : swapFun u v x = y ↔ x = swapFun u v y := by
  constructor
  · intro h; rw [← h, swapFun_invol]
  · intro h; rw [h, swapFun_invol]

def swapMat (u v : α) : Mat α := fun x y => if y = swapFun u v x then 1 else 0

lemma matMul_swap_left (u v : α) (A : Mat α) :
    matMul (swapMat u v) A = fun x z => A (swapFun u v x) z := by
  funext x z
  simp [matMul, swapMat]

lemma matMul_swap_right (u v : α) (A : Mat α) :
    matMul A (swapMat u v) = fun x z => A x (swapFun u v z) := by
  funext x z
  have h : (∑ y : α, A x y * (if z = swapFun u v y then (1 : ZMod 2) else 0)) =
      ∑ y : α, A x y * (if y = swapFun u v z then (1 : ZMod 2) else 0) := by
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y = swapFun u v z
    · have hz : z = swapFun u v y := ((swapFun_eq_iff u v y z).mpr hy).symm
      rw [if_pos hz, if_pos hy]
    · have hz : z ≠ swapFun u v y := fun h => hy ((swapFun_eq_iff u v y z).mp h.symm)
      rw [if_neg hz, if_neg hy]
  simpa [matMul, swapMat] using h

lemma swapMat_eq_transv (u v : α) (huv : u ≠ v) :
    matMul (matMul (transv u v) (transv v u)) (transv u v) = swapMat u v := by
  rw [matMul_transv_left, matMul_transv_right]
  funext x z
  simp only [transv, swapMat, swapFun]
  have hvu : v ≠ u := huv.symm
  by_cases hxu : x = u
  · rw [hxu]
    by_cases hzv : z = v
    · rw [hzv]; simp [huv, hvu, zmod2_add_self]
    · by_cases hzu : z = u
      · rw [hzu]; simp [huv, hvu, zmod2_add_self]
      · simp [huv, hzv, hzu, Ne.symm hzv, Ne.symm hzu]
  · by_cases hxv : x = v
    · rw [hxv]
      by_cases hzu : z = u
      · rw [hzu]; simp [huv, hvu, zmod2_add_self]
      · by_cases hzv : z = v
        · rw [hzv]; simp [huv, hvu, zmod2_add_self]
        · simp [hvu, hzu, hzv, Ne.symm hzv]
    · by_cases hzv : z = v
      · rw [hzv]; simp [hxu, hxv, hvu, Ne.symm hxv]
      · simp [hxu, hxv, hzv]
        simp only [eq_comm]

lemma conj_swap_transv (a b u v : α) :
    matMul (matMul (swapMat a b) (transv u v)) (swapMat a b) =
      transv (swapFun a b u) (swapFun a b v) := by
  rw [matMul_swap_left, matMul_swap_right]
  funext x z
  simp only [transv]
  have h1 : (swapFun a b x = swapFun a b z) ↔ (x = z) := by
    constructor
    · intro h
      have := congrArg (swapFun a b) h
      simpa [swapFun_invol] using this
    · intro h; rw [h]
  have h2 : (swapFun a b x = u ∧ swapFun a b z = v) ↔ (x = swapFun a b u ∧ z = swapFun a b v) := by
    rw [swapFun_eq_iff, swapFun_eq_iff]
  simp only [h1, h2]

def transvProd (L : List (α × α)) : Mat α := matProd (L.map (fun p => transv p.1 p.2))

lemma transvProd_nil : transvProd ([] : List (α × α)) = matId := rfl

lemma transvProd_cons (p : α × α) (L : List (α × α)) :
    transvProd (p :: L) = matMul (transv p.1 p.2) (transvProd L) := rfl

lemma transvProd_append (L1 L2 : List (α × α)) :
    transvProd (L1 ++ L2) = matMul (transvProd L1) (transvProd L2) := by
  simp [transvProd, matProd_append]

lemma transvProd_mul_reverse (L : List (α × α)) (hL : ∀ p ∈ L, p.1 ≠ p.2) :
    matMul (transvProd L) (transvProd L.reverse) = matId := by
  induction L with
  | nil => simp [transvProd, matProd, matMul_id_left]
  | cons p rest ih =>
    have hp : p.1 ≠ p.2 := hL p (List.mem_cons_self ..)
    have hrest : ∀ q ∈ rest, q.1 ≠ q.2 := fun q hq => hL q (List.mem_cons_of_mem _ hq)
    simp only [List.reverse_cons, transvProd_cons, transvProd_append]
    rw [matMul_assoc, ← matMul_assoc (transvProd rest), ih hrest, matMul_id_left]
    simp only [transvProd, List.map_cons, List.map_nil, matProd, matMul_id_right]
    exact transv_sq p.1 p.2 hp

lemma transvProd_reverse_mul (L : List (α × α)) (hL : ∀ p ∈ L, p.1 ≠ p.2) :
    matMul (transvProd L.reverse) (transvProd L) = matId := by
  have hrev : ∀ p ∈ L.reverse, p.1 ≠ p.2 := fun p hp => hL p (List.mem_reverse.mp hp)
  have h := transvProd_mul_reverse L.reverse hrev
  simpa [List.reverse_reverse] using h

end MatrixOps

section GaussElim

lemma matMul_rowElim {D : ℕ} (kFin : Fin D) (rs : List (Fin D))
    (hnd : rs.Nodup) (hk : kFin ∉ rs) (A : Mat (Fin D)) :
    matMul (transvProd (rs.map (fun i => (i, kFin)))) A =
      fun i j => A i j + (if i ∈ rs then A kFin j else 0) := by
  induction rs with
  | nil =>
    simp [transvProd, matProd, matMul_id_left]
  | cons r rest ih =>
    have hnd_rest : rest.Nodup := (List.nodup_cons.mp hnd).2
    have hr_not : r ∉ rest := (List.nodup_cons.mp hnd).1
    have hk_rest : kFin ∉ rest := fun h => hk (List.mem_cons_of_mem _ h)
    have hrk : r ≠ kFin := fun h => hk (h ▸ List.mem_cons_self ..)
    simp only [List.map_cons, transvProd_cons, matMul_assoc]
    rw [ih hnd_rest hk_rest, matMul_transv_left]
    funext i j
    simp only [hk_rest, ↓reduceIte, add_zero, List.mem_cons]
    by_cases hir : i = r
    · subst hir
      simp [hr_not]
    · simp [hir]

lemma matMul_colElim {D : ℕ} (kFin : Fin D) (cs : List (Fin D))
    (hnd : cs.Nodup) (hk : kFin ∉ cs) (A : Mat (Fin D)) :
    matMul A (transvProd (cs.map (fun j => (kFin, j)))) =
      fun i j => A i j + (if j ∈ cs then A i kFin else 0) := by
  induction cs generalizing A with
  | nil =>
    simp [transvProd, matProd, matMul_id_right]
  | cons c rest ih =>
    have hnd_rest : rest.Nodup := (List.nodup_cons.mp hnd).2
    have hc_not : c ∉ rest := (List.nodup_cons.mp hnd).1
    have hk_rest : kFin ∉ rest := fun h => hk (List.mem_cons_of_mem _ h)
    have hkc : kFin ≠ c := fun h => hk (h ▸ List.mem_cons_self ..)
    simp only [List.map_cons, transvProd_cons, ← matMul_assoc]
    rw [ih hnd_rest hk_rest, matMul_transv_right]
    funext i j
    have hk_ne_c : ¬ (kFin = c) := hkc
    simp only [hk_ne_c, ↓reduceIte, add_zero, List.mem_cons]
    by_cases hjc : j = c
    · subst hjc
      simp [hc_not]
    · simp [hjc]

lemma gauss_elim_step (D : ℕ) :
    ∀ m : ℕ, m ≤ D →
      ∀ A : Mat (Fin D),
        (∀ i j : Fin D, (i.val < D - m ∨ j.val < D - m) → i ≠ j → A i j = 0) →
        ∃ (PL QL : List (Fin D × Fin D)) (R : Fin D → Bool),
          (∀ p ∈ PL, p.1 ≠ p.2) ∧
          (∀ q ∈ QL, q.1 ≠ q.2) ∧
          2 * PL.length ≤ m * (m + 5) ∧
          2 * QL.length ≤ m * (m + 5) ∧
          matMul (matMul (transvProd PL) A) (transvProd QL) = diagMat R := by
  intro m
  induction m with
  | zero =>
    intro _ A hA
    refine ⟨[], [], fun i => decide (A i i = 1), by simp, by simp, by simp, by simp, ?_⟩
    rw [transvProd_nil, matMul_id_left, matMul_id_right]
    funext i j
    simp only [diagMat]
    by_cases hij : i = j
    · subst hij
      rcases zmod2_eq_zero_or_one (A i i) with h0 | h1
      · simp [h0]
      · simp [h1]
    · have hi : i.val < D - 0 := by omega
      have h0 := hA i j (Or.inl hi) hij
      simp [hij, h0]
  | succ m ih =>
    intro hm A hA
    let k := D - (m + 1)
    have hk_lt : k < D := by omega
    let kFin : Fin D := ⟨k, hk_lt⟩
    by_cases hex : ∃ r c : Fin D, k ≤ r.val ∧ k ≤ c.val ∧ A r c ≠ 0
    · rcases hex with ⟨r, c, hrk, hck, harc⟩
      have harc1 : A r c = 1 := by
        rcases zmod2_eq_zero_or_one (A r c) with h0 | h1
        · exact absurd h0 harc
        · exact h1
      let L_sw : List (Fin D × Fin D) :=
        if r = kFin then [] else [(r, kFin), (kFin, r), (r, kFin)]
      let R_sw : List (Fin D × Fin D) :=
        if c = kFin then [] else [(c, kFin), (kFin, c), (c, kFin)]
      have hLsw_ne : ∀ p ∈ L_sw, p.1 ≠ p.2 := by
        intro p hp
        dsimp only [L_sw] at hp
        split_ifs at hp with hr
        · simp at hp
        · rcases List.mem_cons.mp hp with rfl | hp
          · exact hr
          · rcases List.mem_cons.mp hp with rfl | hp
            · exact Ne.symm hr
            · rcases List.mem_singleton.mp hp with rfl
              exact hr
      have hRsw_ne : ∀ q ∈ R_sw, q.1 ≠ q.2 := by
        intro q hq
        dsimp only [R_sw] at hq
        split_ifs at hq with hc
        · simp at hq
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact hc
          · rcases List.mem_cons.mp hq with rfl | hq
            · exact Ne.symm hc
            · rcases List.mem_singleton.mp hq with rfl
              exact hc
      have hLsw_len : L_sw.length ≤ 3 := by dsimp only [L_sw]; split_ifs <;> simp
      have hRsw_len : R_sw.length ≤ 3 := by dsimp only [R_sw]; split_ifs <;> simp
      have hLsw_mat : transvProd L_sw = swapMat r kFin := by
        dsimp only [L_sw]
        split_ifs with hr
        · rw [hr]
          funext x y
          by_cases hx : x = kFin
          · simp [transvProd, matProd, matId, swapMat, swapFun, hx, eq_comm]
          · simp [transvProd, matProd, matId, swapMat, swapFun, hx]
            simp only [eq_comm]
        · simp only [transvProd, List.map_cons, List.map_nil, matProd, matMul_id_right]
          rw [← matMul_assoc]
          exact swapMat_eq_transv r kFin hr
      have hRsw_mat : transvProd R_sw = swapMat c kFin := by
        dsimp only [R_sw]
        split_ifs with hc
        · rw [hc]
          funext x y
          by_cases hx : x = kFin
          · simp [transvProd, matProd, matId, swapMat, swapFun, hx, eq_comm]
          · simp [transvProd, matProd, matId, swapMat, swapFun, hx]
            simp only [eq_comm]
        · simp only [transvProd, List.map_cons, List.map_nil, matProd, matMul_id_right]
          rw [← matMul_assoc]
          exact swapMat_eq_transv c kFin hc
      let A1 : Mat (Fin D) := matMul (matMul (transvProd L_sw) A) (transvProd R_sw)
      have hA1_eq : ∀ i j : Fin D, A1 i j = A (swapFun r kFin i) (swapFun c kFin j) := by
        intro i j
        dsimp only [A1]
        rw [hLsw_mat, hRsw_mat, matMul_swap_left, matMul_swap_right]
      have hA1_kk : A1 kFin kFin = 1 := by
        rw [hA1_eq]
        have h1 : swapFun r kFin kFin = r := by
          unfold swapFun
          by_cases hr : kFin = r
          · simp [hr]
          · simp [hr]
        have h2 : swapFun c kFin kFin = c := by
          unfold swapFun
          by_cases hc : kFin = c
          · simp [hc]
          · simp [hc]
        rw [h1, h2, harc1]
      have hswap_lt : ∀ (u i : Fin D), k ≤ u.val → i.val < k → swapFun u kFin i = i := by
        intro u i hu hi
        unfold swapFun
        have h1 : i ≠ u := fun h => by subst h; omega
        have h2 : i ≠ kFin := fun h => by subst h; dsimp only [kFin] at hi; omega
        simp [h1, h2]
      have hswap_ge : ∀ (u i : Fin D), k ≤ u.val → k ≤ i.val → k ≤ (swapFun u kFin i).val := by
        intro u i hu hi
        unfold swapFun
        have hkval : kFin.val = k := rfl
        split_ifs <;> omega
      have hA1_clean : ∀ i j : Fin D, (i.val < k ∨ j.val < k) → i ≠ j → A1 i j = 0 := by
        intro i j hij hne
        rw [hA1_eq]
        rcases hij with hi | hj
        · rw [hswap_lt r i hrk hi]
          have hne' : i ≠ swapFun c kFin j := by
            by_cases hj' : j.val < k
            · rw [hswap_lt c j hck hj']; exact hne
            · have hge := hswap_ge c j hck (by omega)
              intro heq; rw [← heq] at hge; omega
          exact hA i (swapFun c kFin j) (Or.inl hi) hne'
        · rw [hswap_lt c j hck hj]
          have hne' : swapFun r kFin i ≠ j := by
            by_cases hi' : i.val < k
            · rw [hswap_lt r i hrk hi']; exact hne
            · have hge := hswap_ge r i hrk (by omega)
              intro heq; rw [heq] at hge; omega
          exact hA (swapFun r kFin i) j (Or.inr hj) hne'
      let rs : List (Fin D) := (List.finRange D).filter (fun i => decide (k < i.val) && decide (A1 i kFin = 1))
      have hrs_nd : rs.Nodup := (List.nodup_finRange D).filter _
      have hrs_hk : kFin ∉ rs := by
        intro hmem
        have := (List.mem_filter.mp hmem).2
        simp [kFin] at this
      have hrs_len : rs.length ≤ m := by
        have hsub : rs.toFinset ⊆ Finset.univ.filter (fun i : Fin D => k < i.val) := by
          intro i hi
          rw [List.mem_toFinset] at hi
          have := (List.mem_filter.mp hi).2
          simp only [Bool.and_eq_true, decide_eq_true_eq] at this
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, this.1⟩
        have hcard1 : rs.length = rs.toFinset.card := (List.toFinset_card_of_nodup hrs_nd).symm
        have hcard2 : (Finset.univ.filter (fun i : Fin D => k < i.val)).card = m := by
          have hbij : (Finset.univ.filter (fun i : Fin D => k < i.val)).card = (Finset.range m).card := by
            apply Finset.card_bij (fun i _ => i.val - (k + 1))
            · intro i hi
              have hlt := (Finset.mem_filter.mp hi).2
              rw [Finset.mem_range]; omega
            · intro i1 hi1 i2 hi2 heq
              have h1 := (Finset.mem_filter.mp hi1).2
              have h2 := (Finset.mem_filter.mp hi2).2
              exact Fin.ext (by omega)
            · intro t ht
              rw [Finset.mem_range] at ht
              refine ⟨⟨k + 1 + t, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, by dsimp only; omega⟩
          rw [hbij, Finset.card_range]
        calc rs.length = rs.toFinset.card := hcard1
          _ ≤ (Finset.univ.filter (fun i : Fin D => k < i.val)).card := Finset.card_le_card hsub
          _ = m := hcard2
      let L_el : List (Fin D × Fin D) := rs.map (fun i => (i, kFin))
      have hLel_ne : ∀ p ∈ L_el, p.1 ≠ p.2 := by
        intro p hp
        rcases List.mem_map.mp hp with ⟨i, hi, rfl⟩
        intro heq; dsimp only at heq; rw [heq] at hi; exact hrs_hk hi
      let A2 : Mat (Fin D) := matMul (transvProd L_el) A1
      have hA2_eq : ∀ i j : Fin D, A2 i j = A1 i j + (if i ∈ rs then A1 kFin j else 0) := by
        intro i j
        dsimp only [A2, L_el]
        rw [matMul_rowElim kFin rs hrs_nd hrs_hk A1]
      have hA2_kk : A2 kFin kFin = 1 := by
        rw [hA2_eq, if_neg hrs_hk, add_zero, hA1_kk]
      have hA2_colk : ∀ i : Fin D, i ≠ kFin → A2 i kFin = 0 := by
        intro i hi
        rw [hA2_eq]
        by_cases hilt : i.val < k
        · have hnot : i ∉ rs := by
            intro hmem
            have := (List.mem_filter.mp hmem).2
            simp only [Bool.and_eq_true, decide_eq_true_eq] at this
            omega
          rw [if_neg hnot, add_zero]
          exact hA1_clean i kFin (Or.inl hilt) hi
        · have higt : k < i.val := by
            have : i.val ≠ k := fun h => hi (Fin.ext h)
            omega
          rcases zmod2_eq_zero_or_one (A1 i kFin) with h0 | h1
          · have hnot : i ∉ rs := by
              intro hmem
              have := (List.mem_filter.mp hmem).2
              simp [h0] at this
            rw [if_neg hnot, add_zero, h0]
          · have hmem : i ∈ rs := by
              rw [List.mem_filter]
              exact ⟨List.mem_finRange i, by simp [higt, h1]⟩
            rw [if_pos hmem, h1, hA1_kk, zmod2_add_self]
      have hA2_clean : ∀ i j : Fin D, (i.val < k ∨ j.val < k) → i ≠ j → A2 i j = 0 := by
        intro i j hij hne
        rw [hA2_eq]
        rcases hij with hi | hj
        · have hnot : i ∉ rs := by
            intro hmem
            have := (List.mem_filter.mp hmem).2
            simp only [Bool.and_eq_true, decide_eq_true_eq] at this
            omega
          rw [if_neg hnot, add_zero]
          exact hA1_clean i j (Or.inl hi) hne
        · have h1 := hA1_clean i j (Or.inr hj) hne
          have h2 : A1 kFin j = 0 := hA1_clean kFin j (Or.inr hj) (fun h => by subst h; dsimp only [kFin] at hj; omega)
          rw [h1, h2]
          split_ifs <;> simp
      let cs : List (Fin D) := (List.finRange D).filter (fun j => decide (k < j.val) && decide (A2 kFin j = 1))
      have hcs_nd : cs.Nodup := (List.nodup_finRange D).filter _
      have hcs_hk : kFin ∉ cs := by
        intro hmem
        have := (List.mem_filter.mp hmem).2
        simp [kFin] at this
      have hcs_len : cs.length ≤ m := by
        have hsub : cs.toFinset ⊆ Finset.univ.filter (fun j : Fin D => k < j.val) := by
          intro j hj
          rw [List.mem_toFinset] at hj
          have := (List.mem_filter.mp hj).2
          simp only [Bool.and_eq_true, decide_eq_true_eq] at this
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, this.1⟩
        have hcard1 : cs.length = cs.toFinset.card := (List.toFinset_card_of_nodup hcs_nd).symm
        have hcard2 : (Finset.univ.filter (fun j : Fin D => k < j.val)).card = m := by
          have hbij : (Finset.univ.filter (fun j : Fin D => k < j.val)).card = (Finset.range m).card := by
            apply Finset.card_bij (fun j _ => j.val - (k + 1))
            · intro j hj
              have hlt := (Finset.mem_filter.mp hj).2
              rw [Finset.mem_range]; omega
            · intro j1 hj1 j2 hj2 heq
              have h1 := (Finset.mem_filter.mp hj1).2
              have h2 := (Finset.mem_filter.mp hj2).2
              exact Fin.ext (by omega)
            · intro t ht
              rw [Finset.mem_range] at ht
              refine ⟨⟨k + 1 + t, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega⟩, by dsimp only; omega⟩
          rw [hbij, Finset.card_range]
        calc cs.length = cs.toFinset.card := hcard1
          _ ≤ (Finset.univ.filter (fun j : Fin D => k < j.val)).card := Finset.card_le_card hsub
          _ = m := hcard2
      let R_el : List (Fin D × Fin D) := cs.map (fun j => (kFin, j))
      have hRel_ne : ∀ q ∈ R_el, q.1 ≠ q.2 := by
        intro q hq
        rcases List.mem_map.mp hq with ⟨j, hj, rfl⟩
        intro heq; dsimp only at heq; rw [← heq] at hj; exact hcs_hk hj
      let A3 : Mat (Fin D) := matMul A2 (transvProd R_el)
      have hA3_eq : ∀ i j : Fin D, A3 i j = A2 i j + (if j ∈ cs then A2 i kFin else 0) := by
        intro i j
        dsimp only [A3, R_el]
        rw [matMul_colElim kFin cs hcs_nd hcs_hk A2]
      have hA3_clean : ∀ i j : Fin D, (i.val < D - m ∨ j.val < D - m) → i ≠ j → A3 i j = 0 := by
        intro i j hij hne
        have hdm : D - m = k + 1 := by omega
        rw [hdm] at hij
        rw [hA3_eq]
        rcases hij with hi | hj
        · by_cases hilt : i.val < k
          · have h1 := hA2_clean i j (Or.inl hilt) hne
            have h2 := hA2_colk i (fun h => by subst h; dsimp only [kFin] at hilt; omega)
            rw [h1, h2]
            split_ifs <;> simp
          · have hik : i = kFin := Fin.ext (by dsimp only [kFin]; omega)
            subst hik
            by_cases hjlt : j.val < k
            · have hnot : j ∉ cs := by
                intro hmem
                have := (List.mem_filter.mp hmem).2
                simp only [Bool.and_eq_true, decide_eq_true_eq] at this
                omega
              rw [if_neg hnot, add_zero]
              exact hA2_clean kFin j (Or.inr hjlt) hne
            · have hjgt : k < j.val := by
                have : j.val ≠ k := fun h => hne (Fin.ext (by dsimp only [kFin]; omega))
                omega
              rcases zmod2_eq_zero_or_one (A2 kFin j) with h0 | h1
              · have hnot : j ∉ cs := by
                  intro hmem
                  have := (List.mem_filter.mp hmem).2
                  simp [h0] at this
                rw [if_neg hnot, add_zero, h0]
              · have hmem : j ∈ cs := by
                  rw [List.mem_filter]
                  exact ⟨List.mem_finRange j, by simp [hjgt, h1]⟩
                rw [if_pos hmem, h1, hA2_kk, zmod2_add_self]
        · by_cases hjlt : j.val < k
          · have hnot : j ∉ cs := by
              intro hmem
              have := (List.mem_filter.mp hmem).2
              simp only [Bool.and_eq_true, decide_eq_true_eq] at this
              omega
            rw [if_neg hnot, add_zero]
            exact hA2_clean i j (Or.inr hjlt) hne
          · have hjk : j = kFin := Fin.ext (by dsimp only [kFin]; omega)
            subst hjk
            rw [if_neg hcs_hk, add_zero]
            exact hA2_colk i hne
      rcases ih (by omega) A3 hA3_clean with ⟨PL', QL', R, hPL'_ne, hQL'_ne, hPL'_len, hQL'_len, hdiag⟩
      refine ⟨PL' ++ L_el ++ L_sw, R_sw ++ R_el ++ QL', R, ?_, ?_, ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · rcases List.mem_append.mp hp with hp | hp
          · exact hPL'_ne p hp
          · exact hLel_ne p hp
        · exact hLsw_ne p hp
      · intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · rcases List.mem_append.mp hq with hq | hq
          · exact hRsw_ne q hq
          · exact hRel_ne q hq
        · exact hQL'_ne q hq
      · simp only [List.length_append, L_el, List.length_map]
        nlinarith
      · simp only [List.length_append, R_el, List.length_map]
        nlinarith
      · simp only [transvProd_append]
        have hA3_def : A3 = matMul (matMul (matMul (transvProd L_el) (transvProd L_sw)) A)
            (matMul (transvProd R_sw) (transvProd R_el)) := by
          dsimp only [A3, A2, A1]
          simp only [matMul_assoc]
        rw [← hdiag, hA3_def]
        simp only [matMul_assoc]
    · push_neg at hex
      refine ⟨[], [], fun i => decide (A i i = 1), by simp, by simp, by simp, by simp, ?_⟩
      rw [transvProd_nil, matMul_id_left, matMul_id_right]
      funext i j
      simp only [diagMat]
      by_cases hij : i = j
      · subst hij
        rcases zmod2_eq_zero_or_one (A i i) with h0 | h1
        · simp [h0]
        · simp [h1]
      · by_cases hi : i.val < k
        · simp [hij, hA i j (Or.inl hi) hij]
        · by_cases hj : j.val < k
          · simp [hij, hA i j (Or.inr hj) hij]
          · simp [hij, hex i j (by omega) (by omega)]

lemma gauss_elim_fin (D : ℕ) (hD : 1 ≤ D) (T : Mat (Fin D)) :
    ∃ (P Q : List (Fin D × Fin D)) (R : Fin D → Bool),
      (∀ p ∈ P, p.1 ≠ p.2) ∧
      (∀ q ∈ Q, q.1 ≠ q.2) ∧
      P.length ≤ D * (D + 2) ∧
      Q.length ≤ D * (D + 2) ∧
      T = matMul (matMul (transvProd P) (diagMat R)) (transvProd Q) := by
  have hclean : ∀ i j : Fin D, (i.val < D - D ∨ j.val < D - D) → i ≠ j → T i j = 0 := by
    intro i j h; omega
  rcases gauss_elim_step D D le_rfl T hclean with ⟨PL, QL, R, hPL_ne, hQL_ne, hPL_len, hQL_len, hdiag⟩
  refine ⟨PL.reverse, QL.reverse, R, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp; exact hPL_ne p (List.mem_reverse.mp hp)
  · intro q hq; exact hQL_ne q (List.mem_reverse.mp hq)
  · rw [List.length_reverse]
    have : D * (D + 5) ≤ 2 * (D * (D + 2)) := by nlinarith
    omega
  · rw [List.length_reverse]
    have : D * (D + 5) ≤ 2 * (D * (D + 2)) := by nlinarith
    omega
  · rw [← hdiag]
    calc T = matMul (matMul matId T) matId := by rw [matMul_id_left, matMul_id_right]
      _ = matMul (matMul (matMul (transvProd PL.reverse) (transvProd PL)) T)
            (matMul (transvProd QL) (transvProd QL.reverse)) := by
          rw [transvProd_reverse_mul PL hPL_ne, transvProd_mul_reverse QL hQL_ne]
      _ = matMul (matMul (transvProd PL.reverse) (matMul (matMul (transvProd PL) T) (transvProd QL)))
            (transvProd QL.reverse) := by
          simp only [matMul_assoc]

lemma matMul_pullback {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (A B : Mat β) :
    (fun x z => matMul A B (e x) (e z)) = matMul (fun x y => A (e x) (e y)) (fun y z => B (e y) (e z)) := by
  funext x z
  simp only [matMul]
  exact (Equiv.sum_comp e (fun y => A (e x) y * B y (e z))).symm

lemma transvProd_pullback {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (L : List (β × β)) :
    (fun x y => transvProd L (e x) (e y)) =
      transvProd (L.map (fun p => (e.symm p.1, e.symm p.2))) := by
  induction L with
  | nil =>
    funext x y
    simp [transvProd, matProd, matId]
  | cons p rest ih =>
    simp only [List.map_cons, transvProd_cons]
    rw [matMul_pullback e (transv p.1 p.2) (transvProd rest), ih]
    have htr : (fun x y => transv p.1 p.2 (e x) (e y)) = transv (e.symm p.1) (e.symm p.2) := by
      funext x y
      simp only [transv, Equiv.apply_eq_iff_eq, Equiv.apply_eq_iff_eq_symm_apply, Equiv.symm_apply_apply]
    rw [htr]

lemma gauss_elim_equiv {α : Type} [Fintype α] [DecidableEq α] (D : ℕ) (hD : 1 ≤ D)
    (e : α ≃ Fin D) (T : Mat α) :
    ∃ (P Q : List (α × α)) (R : α → Bool),
      (∀ p ∈ P, p.1 ≠ p.2) ∧
      (∀ q ∈ Q, q.1 ≠ q.2) ∧
      P.length ≤ D * (D + 2) ∧
      Q.length ≤ D * (D + 2) ∧
      T = matMul (matMul (transvProd P) (diagMat R)) (transvProd Q) := by
  let T' : Mat (Fin D) := fun i j => T (e.symm i) (e.symm j)
  rcases gauss_elim_fin D hD T' with ⟨P', Q', R', hP'_ne, hQ'_ne, hP'_len, hQ'_len, hT'⟩
  refine ⟨P'.map (fun p => (e.symm p.1, e.symm p.2)),
          Q'.map (fun q => (e.symm q.1, e.symm q.2)),
          fun x => R' (e x), ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases List.mem_map.mp hp with ⟨p', hp', rfl⟩
    intro h; exact hP'_ne p' hp' (e.symm.injective h)
  · intro q hq
    rcases List.mem_map.mp hq with ⟨q', hq', rfl⟩
    intro h; exact hQ'_ne q' hq' (e.symm.injective h)
  · simp [hP'_len]
  · simp [hQ'_len]
  · have hpull : (fun x z => T' (e x) (e z)) = T := by
      funext x z; simp [T']
    rw [← hpull, hT', matMul_pullback e, matMul_pullback e,
        transvProd_pullback e, transvProd_pullback e]
    congr 2
    funext x y
    simp [diagMat]

end GaussElim

section ShiftRegister

variable (d : ℕ)

abbrev State := Fin (d + 1) → Bool
abbrev StepTable := (Fin (d + 2) → Bool) → Bool

def shiftState (s : State d) (b : Bool) : State d :=
  fun j => if h : j.val + 1 < d + 1 then s ⟨j.val + 1, h⟩ else b

def combineWindow (s : State d) (b : Bool) : Fin (d + 2) → Bool :=
  fun off => if h : off.val < d + 1 then s ⟨off.val, h⟩ else b

def stepMat (t : StepTable d) : Mat (State d) :=
  fun s s' => ∑ b : Bool, if shiftState d s b = s' ∧ t (combineWindow d s b) = true then (1 : ZMod 2) else 0

lemma shiftState_inj (s : State d) (b1 b2 : Bool) (h : shiftState d s b1 = shiftState d s b2) :
    b1 = b2 := by
  have hval := congrFun h ⟨d, Nat.lt_succ_self d⟩
  simp [shiftState] at hval
  exact hval

def acceptsList (tables : List (StepTable d)) (first last : State d)
    (word : Fin (tables.length + (d + 1)) → Bool) : Prop :=
  (∀ j : Fin (d + 1),
      word ⟨j.val, by omega⟩ = first j ∧
      word ⟨tables.length + j.val, by omega⟩ = last j) ∧
  ∀ i : Fin tables.length,
    tables[i.val] (fun off : Fin (d + 2) => word ⟨i.val + off.val, by omega⟩) = true

instance instDecidableAcceptsList (tables : List (StepTable d)) (first last : State d) :
    DecidablePred (acceptsList d tables first last) := fun _ => by
  unfold acceptsList
  infer_instance

lemma card_acceptsList_zmod2 (tables : List (StepTable d)) :
    ∀ first last : State d,
      ((Finset.univ.filter (acceptsList d tables first last)).card : ZMod 2) =
        matProd (tables.map (stepMat d)) first last := by
  induction tables with
  | nil =>
    intro first last
    simp only [List.map_nil, matProd_nil, matId]
    by_cases hfl : first = last
    · subst hfl
      have hcard : (Finset.univ.filter (acceptsList d [] first first)).card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨fun k => first ⟨k.val, by have := k.isLt; simp at this; omega⟩, ?_⟩
        ext word
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, acceptsList,
          List.length_nil, zero_add]
        constructor
        · intro h
          funext k
          have hk := (h.1 ⟨k.val, by have := k.isLt; simp only [List.length_nil, zero_add] at this; exact this⟩).1
          simpa using hk
        · intro h
          subst h
          refine ⟨fun j => ⟨rfl, rfl⟩, fun i => Fin.elim0 i⟩
      simp [hcard]
    · have hcard : (Finset.univ.filter (acceptsList d [] first last)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro word _ hacc
        apply hfl
        funext j
        have hj := hacc.1 j
        simp only [List.length_nil, zero_add] at hj
        exact hj.1.symm.trans hj.2
      simp [hfl, hcard]
  | cons t rest ih =>
    intro first last
    simp only [List.map_cons, matProd_cons]
    let S := Finset.univ.filter (acceptsList d (t :: rest) first last)
    let T_b := fun b : Bool =>
      if t (combineWindow d first b) = true then
        Finset.univ.filter (acceptsList d rest (shiftState d first b) last)
      else ∅
    have hcard_eq : S.card = (T_b false).card + (T_b true).card := by
      have hd1_lt : d + 1 < (t :: rest).length + (d + 1) := by simp only [List.length_cons]; omega
      have hdisj : Disjoint
          (S.filter (fun word => word ⟨d + 1, hd1_lt⟩ = false))
          (S.filter (fun word => word ⟨d + 1, hd1_lt⟩ = true)) := by
        rw [Finset.disjoint_left]
        intro word h1 h2
        have hb1 := (Finset.mem_filter.mp h1).2
        have hb2 := (Finset.mem_filter.mp h2).2
        rw [hb1] at hb2
        exact Bool.false_ne_true hb2
      have hunion : S =
          (S.filter (fun word => word ⟨d + 1, hd1_lt⟩ = false)) ∪
          (S.filter (fun word => word ⟨d + 1, hd1_lt⟩ = true)) := by
        ext word
        simp only [Finset.mem_union, Finset.mem_filter]
        cases h : word ⟨d + 1, hd1_lt⟩ <;> simp
      have hpart : ∀ b : Bool,
          (S.filter (fun word => word ⟨d + 1, hd1_lt⟩ = b)).card = (T_b b).card := by
        intro b
        dsimp only [T_b]
        by_cases ht : t (combineWindow d first b) = true
        · rw [if_pos ht]
          apply Finset.card_bij (fun word _ => fun k : Fin (rest.length + (d + 1)) =>
            word ⟨k.val + 1, by have := k.isLt; simp only [List.length_cons]; omega⟩)
          · intro word hw
            rcases Finset.mem_filter.mp hw with ⟨hwS, hwb⟩
            have hacc := (Finset.mem_filter.mp hwS).2
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, ?_, ?_⟩
            · intro j
              constructor
              · dsimp only [shiftState]
                split_ifs with hj
                · have h1 := (hacc.1 ⟨j.val + 1, hj⟩).1
                  exact h1
                · have hjeq : j.val + 1 = d + 1 := by have := j.isLt; omega
                  simpa [hjeq] using hwb
              · dsimp only
                have h2 := (hacc.1 j).2
                have hidx : (⟨rest.length + j.val + 1, by have := j.isLt; simp only [List.length_cons]; omega⟩ : Fin ((t :: rest).length + (d + 1))) =
                    ⟨(t :: rest).length + j.val, by have := j.isLt; simp only [List.length_cons]; omega⟩ := by
                  apply Fin.ext; simp only [List.length_cons]; omega
                rw [hidx]
                exact h2
            · intro i
              have hi_lt : i.val + 1 < (t :: rest).length := by have := i.isLt; simp only [List.length_cons]; omega
              have hi := hacc.2 ⟨i.val + 1, hi_lt⟩
              have hteq : (t :: rest)[i.val + 1]'hi_lt = rest[i.val]'i.isLt := rfl
              rw [hteq] at hi
              convert hi using 2
              funext off
              dsimp only
              congr 1
              apply Fin.ext; dsimp only; omega
          · intro w1 hw1 w2 hw2 heq
            have hacc1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hw1).1).2
            have hacc2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hw2).1).2
            funext k
            by_cases hk : k.val = 0
            · have h1 := (hacc1.1 ⟨0, Nat.succ_pos d⟩).1
              have h2 := (hacc2.1 ⟨0, Nat.succ_pos d⟩).1
              have hkeq : k = ⟨0, by simp only [List.length_cons]; omega⟩ := Fin.ext hk
              rw [hkeq, h1, h2]
            · have hk1 : k.val - 1 < rest.length + (d + 1) := by
                have := k.isLt; simp only [List.length_cons] at this; omega
              have hfun := congrFun heq ⟨k.val - 1, hk1⟩
              dsimp only at hfun
              have hkeq : (⟨k.val - 1 + 1, by have := k.isLt; simp only [List.length_cons] at this ⊢; omega⟩ : Fin ((t :: rest).length + (d + 1))) = k :=
                Fin.ext (by dsimp only; omega)
              rw [hkeq] at hfun
              exact hfun
          · intro w' hw'
            have hacc' := (Finset.mem_filter.mp hw').2
            let word : Fin ((t :: rest).length + (d + 1)) → Bool := fun k =>
              if hk : k.val = 0 then first ⟨0, Nat.succ_pos d⟩
              else w' ⟨k.val - 1, by have := k.isLt; simp only [List.length_cons] at this; omega⟩
            refine ⟨word, ?_, ?_⟩
            · rw [Finset.mem_filter]
              have hwb : word ⟨d + 1, hd1_lt⟩ = b := by
                dsimp only [word]
                have hne : ¬ (d + 1 = 0) := by omega
                rw [dif_neg hne]
                have h1 := (hacc'.1 ⟨d, Nat.lt_succ_self d⟩).1
                simpa [shiftState] using h1
              refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, hwb⟩
              · intro j
                constructor
                · dsimp only [word]
                  by_cases hj : j.val = 0
                  · rw [dif_pos hj]
                    congr 1; exact Fin.ext hj.symm
                  · rw [dif_neg hj]
                    have h1 := (hacc'.1 ⟨j.val - 1, by have := j.isLt; omega⟩).1
                    have hlt : j.val - 1 + 1 < d + 1 := by have := j.isLt; omega
                    simp only [shiftState, hlt, ↓reduceDIte] at h1
                    have hjeq : (⟨j.val - 1 + 1, hlt⟩ : Fin (d + 1)) = j := Fin.ext (by dsimp only; omega)
                    rw [hjeq] at h1
                    exact h1
                · dsimp only [word]
                  have hne : ¬ ((t :: rest).length + j.val = 0) := by simp only [List.length_cons]; omega
                  rw [dif_neg hne]
                  have h2 := (hacc'.1 j).2
                  have hidx : (⟨(t :: rest).length + j.val - 1, by have := j.isLt; simp only [List.length_cons]; omega⟩ : Fin (rest.length + (d + 1))) =
                      ⟨rest.length + j.val, by have := j.isLt; omega⟩ := by
                    apply Fin.ext; simp only [List.length_cons]; omega
                  rw [hidx]
                  exact h2
              · intro i
                by_cases hi : i.val = 0
                · have hteq : (t :: rest)[i.val]'i.isLt = t := by simp [hi]
                  rw [hteq]
                  have hwin : (fun off : Fin (d + 2) => word ⟨i.val + off.val, by omega⟩) =
                      combineWindow d first b := by
                    funext off
                    dsimp only [combineWindow]
                    split_ifs with hoff
                    · have hidx : (⟨i.val + off.val, by omega⟩ : Fin ((t :: rest).length + (d + 1))) =
                          ⟨off.val, by simp only [List.length_cons]; omega⟩ := Fin.ext (by dsimp only; omega)
                      rw [hidx]
                      dsimp only [word]
                      by_cases ho0 : off.val = 0
                      · rw [dif_pos ho0]; congr 1; exact Fin.ext ho0.symm
                      · rw [dif_neg ho0]
                        have h1 := (hacc'.1 ⟨off.val - 1, by omega⟩).1
                        have hlt : off.val - 1 + 1 < d + 1 := by omega
                        simp only [shiftState, hlt, ↓reduceDIte] at h1
                        have hoeq : (⟨off.val - 1 + 1, hlt⟩ : Fin (d + 1)) = ⟨off.val, hoff⟩ :=
                          Fin.ext (by dsimp only; omega)
                        rw [hoeq] at h1
                        exact h1
                    · have hoeq : off.val = d + 1 := by have := off.isLt; omega
                      have hidx : (⟨i.val + off.val, by omega⟩ : Fin ((t :: rest).length + (d + 1))) =
                          ⟨d + 1, hd1_lt⟩ := Fin.ext (by dsimp only; omega)
                      rw [hidx, hwb]
                  rw [hwin]
                  exact ht
                · have hi1 : i.val - 1 < rest.length := by
                    have := i.isLt; simp only [List.length_cons] at this; omega
                  have hteq : (t :: rest)[i.val]'i.isLt = rest[i.val - 1]'hi1 := by
                    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hi
                    simp [hr]
                  rw [hteq]
                  have hi' := hacc'.2 ⟨i.val - 1, hi1⟩
                  convert hi' using 2
                  funext off
                  dsimp only [word]
                  have hne : ¬ (i.val + off.val = 0) := by omega
                  rw [dif_neg hne]
                  congr 1
                  apply Fin.ext; dsimp only; omega
            · funext k
              dsimp only [word]
              have hne : ¬ (k.val + 1 = 0) := by omega
              rw [dif_neg hne]
              congr 1
        · rw [if_neg ht, Finset.card_empty, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro word hwS hwb
          have hacc := (Finset.mem_filter.mp hwS).2
          have h0 := hacc.2 ⟨0, by simp only [List.length_cons]; omega⟩
          have hwin : (fun off : Fin (d + 2) => word ⟨0 + off.val, by have := off.isLt; simp only [List.length_cons]; omega⟩) =
              combineWindow d first b := by
            funext off
            dsimp only [combineWindow]
            split_ifs with hoff
            · have h1 := (hacc.1 ⟨off.val, hoff⟩).1
              simpa using h1
            · have hoeq : off.val = d + 1 := by have := off.isLt; omega
              simpa [hoeq] using hwb
          simp only [List.getElem_cons_zero] at h0
          rw [hwin] at h0
          exact ht h0
      rw [hunion, Finset.card_union_of_disjoint hdisj, hpart false, hpart true]
    change (S.card : ZMod 2) = matMul (stepMat d t) (matProd (rest.map (stepMat d))) first last
    rw [hcard_eq, Nat.cast_add]
    have hT : ∀ b : Bool, ((T_b b).card : ZMod 2) =
        if t (combineWindow d first b) = true then
          matProd (rest.map (stepMat d)) (shiftState d first b) last
        else 0 := by
      intro b
      dsimp only [T_b]
      split_ifs with ht
      · exact ih (shiftState d first b) last
      · simp
    rw [hT false, hT true]
    simp only [matMul, stepMat, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Fintype.sum_bool]
    have hterm : ∀ b : Bool,
        (∑ s' : State d,
          (if shiftState d first b = s' ∧ t (combineWindow d first b) = true then (1 : ZMod 2) else 0) *
            matProd (rest.map (stepMat d)) s' last) =
        if t (combineWindow d first b) = true then
          matProd (rest.map (stepMat d)) (shiftState d first b) last
        else 0 := by
      intro b
      by_cases ht : t (combineWindow d first b) = true
      · simp [ht]
      · simp [ht]
    rw [hterm true, hterm false, add_comm]

def rot (r : ℕ) (s : State d) : State d :=
  fun j => s ⟨(j.val + r) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩

lemma rot_zero (s : State d) : rot d 0 s = s := by
  funext j
  simp [rot, Nat.mod_eq_of_lt j.isLt]

lemma rot_add (r1 r2 : ℕ) (s : State d) : rot d r1 (rot d r2 s) = rot d (r1 + r2) s := by
  funext j
  simp only [rot]
  congr 1
  apply Fin.ext
  dsimp only
  rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl _), ← Nat.add_mod, Nat.add_assoc]

lemma rot_self (s : State d) : rot d (d + 1) s = s := by
  funext j
  simp only [rot]
  congr 1
  apply Fin.ext
  dsimp only
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]

lemma shiftState_rot (s : State d) : shiftState d s (s ⟨0, Nat.succ_pos d⟩) = rot d 1 s := by
  funext j
  simp only [shiftState, rot]
  split_ifs with hj
  · congr 1; apply Fin.ext; dsimp only; rw [Nat.mod_eq_of_lt hj]
  · have hjeq : j.val = d := by have := j.isLt; omega
    congr 1; apply Fin.ext; dsimp only; rw [hjeq, Nat.mod_self]

def rotPowMat (r : ℕ) : Mat (State d) := fun x y => if y = rot d r x then 1 else 0

lemma matMul_rotPow (r1 r2 : ℕ) :
    matMul (rotPowMat d r1) (rotPowMat d r2) = rotPowMat d (r1 + r2) := by
  funext x z
  simp only [matMul, rotPowMat]
  have : (∑ y : State d, (if y = rot d r1 x then (1 : ZMod 2) else 0) *
      (if z = rot d r2 y then 1 else 0)) = if z = rot d r2 (rot d r1 x) then 1 else 0 := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [this, rot_add, Nat.add_comm r2 r1]

def idStep : StepTable d :=
  fun win => win ⟨d + 1, Nat.lt_succ_self (d + 1)⟩ == win ⟨0, Nat.succ_pos (d + 1)⟩

lemma stepMat_idStep : stepMat d (idStep d) = rotPowMat d 1 := by
  funext x y
  simp only [stepMat, idStep, combineWindow, rotPowMat, Fintype.sum_bool]
  have h0 : ¬ (d + 1 < d + 1) := Nat.lt_irrefl _
  have h1 : 0 < d + 1 := Nat.succ_pos d
  simp only [h0, ↓reduceDIte, h1, beq_iff_eq]
  cases hx0 : x ⟨0, Nat.succ_pos d⟩
  · have hrot : shiftState d x false = rot d 1 x := by
      rw [← hx0]; exact shiftState_rot d x
    simp [hrot, eq_comm]
  · have hrot : shiftState d x true = rot d 1 x := by
      rw [← hx0]; exact shiftState_rot d x
    simp [hrot, eq_comm]

lemma matProd_replicate_idStep (r : ℕ) :
    matProd ((List.replicate r (idStep d)).map (stepMat d)) = rotPowMat d r := by
  induction r with
  | zero =>
    funext x y
    simp [matProd, matId, rotPowMat, rot_zero, eq_comm]
  | succ k ih =>
    simp only [List.replicate_succ, List.map_cons, matProd_cons, stepMat_idStep, ih, matMul_rotPow,
      Nat.add_comm 1 k]

def idSweep : List (StepTable d) := List.replicate (d + 1) (idStep d)

lemma idSweep_length : (idSweep d).length = d + 1 := List.length_replicate ..

lemma idSweep_mat : matProd ((idSweep d).map (stepMat d)) = matId := by
  rw [idSweep, matProd_replicate_idStep]
  funext x y
  simp [rotPowMat, rot_self, matId, eq_comm]

def diagStep (R : State d → Bool) : StepTable d :=
  fun win =>
    R (fun j : Fin (d + 1) => win ⟨j.val, by omega⟩) &&
    (win ⟨d + 1, Nat.lt_succ_self (d + 1)⟩ == win ⟨0, Nat.succ_pos (d + 1)⟩)

lemma stepMat_diagStep (R : State d → Bool) :
    stepMat d (diagStep d R) = matMul (diagMat R) (rotPowMat d 1) := by
  funext x y
  simp only [stepMat, diagStep, combineWindow, matMul, diagMat, rotPowMat, Fintype.sum_bool]
  have h0 : ¬ (d + 1 < d + 1) := Nat.lt_irrefl _
  have h1 : 0 < d + 1 := Nat.succ_pos d
  have hwin : ∀ b : Bool,
      (fun j : Fin (d + 1) => if h : j.val < d + 1 then x ⟨j.val, h⟩ else b) = x := by
    intro b; funext j; simp [j.isLt]
  simp only [h0, ↓reduceDIte, h1, hwin, Bool.and_eq_true, beq_iff_eq]
  have hrhs : (∑ z : State d, (if x = z ∧ R x = true then (1 : ZMod 2) else 0) *
      (if y = rot d 1 z then 1 else 0)) = if R x = true ∧ y = rot d 1 x then 1 else 0 := by
    by_cases hR : R x = true
    · simp only [hR, and_true, true_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ↓reduceIte]
    · simp [hR]
  rw [hrhs]
  cases hx0 : x ⟨0, Nat.succ_pos d⟩
  · have hrot : shiftState d x false = rot d 1 x := by
      rw [← hx0]; exact shiftState_rot d x
    by_cases hR : R x = true <;> simp [hrot, hR, eq_comm]
  · have hrot : shiftState d x true = rot d 1 x := by
      rw [← hx0]; exact shiftState_rot d x
    by_cases hR : R x = true <;> simp [hrot, hR, eq_comm]

def diagSweep (R : State d → Bool) : List (StepTable d) :=
  diagStep d R :: List.replicate d (idStep d)

lemma diagSweep_length (R : State d → Bool) : (diagSweep d R).length = d + 1 := by
  simp [diagSweep]

lemma diagSweep_mat (R : State d → Bool) :
    matProd ((diagSweep d R).map (stepMat d)) = diagMat R := by
  simp only [diagSweep, List.map_cons, matProd_cons, stepMat_diagStep, matProd_replicate_idStep,
    matMul_assoc, matMul_rotPow]
  have hrot : rotPowMat d (1 + d) = matId := by
    funext x y
    rw [Nat.add_comm]
    simp [rotPowMat, rot_self, matId, eq_comm]
  rw [hrot, matMul_id_right]

def flipBit (u : State d) (p : Fin (d + 1)) : State d :=
  fun j => if j = p then !(u j) else u j

lemma flipBit_ne (u : State d) (p : Fin (d + 1)) : u ≠ flipBit d u p := by
  intro h
  have hp := congrFun h p
  simp only [flipBit, ↓reduceIte] at hp
  cases hu : u p <;> simp [hu] at hp

lemma flipBit_invol (u : State d) (p : Fin (d + 1)) : flipBit d (flipBit d u p) p = u := by
  funext j
  unfold flipBit
  by_cases hjp : j = p
  · subst hjp; simp
  · simp [hjp]

lemma shiftState_rot_flip (u : State d) (p : Fin (d + 1)) :
    shiftState d (rot d p.val u) (!((rot d p.val u) ⟨0, Nat.succ_pos d⟩)) =
      rot d (p.val + 1) (flipBit d u p) := by
  funext j
  simp only [shiftState, rot, flipBit]
  have hp0 : (⟨(0 + p.val) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩ : Fin (d + 1)) = p := by
    apply Fin.ext; dsimp only; rw [Nat.zero_add, Nat.mod_eq_of_lt p.isLt]
  by_cases hj : j.val + 1 < d + 1
  · simp only [hj, ↓reduceDIte]
    have hne : (⟨(j.val + (p.val + 1)) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩ : Fin (d + 1)) ≠ p := by
      intro hjp
      have hval := congrArg Fin.val hjp
      dsimp only at hval
      have hsum : j.val + (p.val + 1) = p.val + (j.val + 1) := by omega
      rw [hsum] at hval
      by_cases hlt : p.val + (j.val + 1) < d + 1
      · rw [Nat.mod_eq_of_lt hlt] at hval; omega
      · have hlt2 : p.val + (j.val + 1) - (d + 1) < d + 1 := by have := p.isLt; omega
        have hmod2 : (p.val + (j.val + 1)) % (d + 1) = p.val + (j.val + 1) - (d + 1) := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2]
        rw [hmod2] at hval; omega
    simp only [hne, ↓reduceIte]
    congr 1
    apply Fin.ext
    dsimp only
    have : j.val + 1 + p.val = j.val + (p.val + 1) := by omega
    rw [this]
  · simp only [hj, ↓reduceDIte]
    have heq : (⟨(j.val + (p.val + 1)) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩ : Fin (d + 1)) = p := by
      apply Fin.ext
      dsimp only
      have hjeq : j.val = d := by have := j.isLt; omega
      rw [hjeq]
      have : d + (p.val + 1) = p.val + (d + 1) := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt p.isLt]
    simp only [heq, ↓reduceIte, hp0]

def branchStep (target : State d) : StepTable d :=
  fun win =>
    (win ⟨d + 1, Nat.lt_succ_self (d + 1)⟩ == win ⟨0, Nat.succ_pos (d + 1)⟩) ||
    ((fun j : Fin (d + 1) => win ⟨j.val, by omega⟩) == target)

lemma stepMat_branchStep (u : State d) (p : Fin (d + 1)) :
    stepMat d (branchStep d (rot d p.val u)) =
      fun x y => (if y = rot d 1 x then 1 else 0) +
        (if x = rot d p.val u ∧ y = rot d (p.val + 1) (flipBit d u p) then 1 else 0) := by
  funext x y
  simp only [stepMat, branchStep, combineWindow, Fintype.sum_bool]
  have h0 : ¬ (d + 1 < d + 1) := Nat.lt_irrefl _
  have h1 : 0 < d + 1 := Nat.succ_pos d
  have hwin : ∀ b : Bool,
      (fun j : Fin (d + 1) => if h : j.val < d + 1 then x ⟨j.val, h⟩ else b) = x := by
    intro b; funext j; simp [j.isLt]
  simp only [h0, ↓reduceDIte, h1, hwin, Bool.or_eq_true, beq_iff_eq]
  cases hx0 : x ⟨0, Nat.succ_pos d⟩
  · have hrot : shiftState d x false = rot d 1 x := by
      rw [← hx0]; exact shiftState_rot d x
    by_cases hxu : x = rot d p.val u
    · subst hxu
      have hflip : shiftState d (rot d p.val u) true = rot d (p.val + 1) (flipBit d u p) := by
        have ht : (!((rot d p.val u) ⟨0, Nat.succ_pos d⟩)) = true := by rw [hx0]; rfl
        rw [← ht]; exact shiftState_rot_flip d u p
      simp [hrot, hflip, eq_comm, add_comm]
    · simp [hrot, hxu, eq_comm]
  · have hrot : shiftState d x true = rot d 1 x := by
      rw [← hx0]; exact shiftState_rot d x
    by_cases hxu : x = rot d p.val u
    · subst hxu
      have hflip : shiftState d (rot d p.val u) false = rot d (p.val + 1) (flipBit d u p) := by
        have hf : (!((rot d p.val u) ⟨0, Nat.succ_pos d⟩)) = false := by rw [hx0]; rfl
        rw [← hf]; exact shiftState_rot_flip d u p
      simp [hrot, hflip, eq_comm]
    · simp [hrot, hxu, eq_comm]

def adjTransvSweep (u : State d) (p : Fin (d + 1)) : List (StepTable d) :=
  List.replicate p.val (idStep d) ++ [branchStep d (rot d p.val u)] ++
    List.replicate (d - p.val) (idStep d)

lemma adjTransvSweep_length (u : State d) (p : Fin (d + 1)) :
    (adjTransvSweep d u p).length = d + 1 := by
  simp only [adjTransvSweep, List.length_append, List.length_replicate, List.length_singleton]
  have := p.isLt; omega

lemma rot_inj (r : ℕ) (x y : State d) (h : rot d r x = rot d r y) : x = y := by
  have h1 : rot d ((d + 1) - r % (d + 1)) (rot d r x) = rot d ((d + 1) - r % (d + 1)) (rot d r y) :=
    congrArg _ h
  simp only [rot_add] at h1
  have hmod : ∀ z : State d, rot d (((d + 1) - r % (d + 1)) + r) z = z := by
    intro z
    funext j
    simp only [rot]
    congr 1; apply Fin.ext; dsimp only
    have hr : r % (d + 1) < d + 1 := Nat.mod_lt r (Nat.succ_pos d)
    have hmul : (d + 1) - r % (d + 1) + r = (r / (d + 1) + 1) * (d + 1) := by
      have hdiv := Nat.div_add_mod r (d + 1)
      have hcomm : (r / (d + 1) + 1) * (d + 1) = (d + 1) * (r / (d + 1)) + (d + 1) := by ring
      omega
    rw [hmul, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
  rw [hmod x, hmod y] at h1
  exact h1

lemma adjTransvSweep_mat (u : State d) (p : Fin (d + 1)) :
    matProd ((adjTransvSweep d u p).map (stepMat d)) = transv u (flipBit d u p) := by
  simp only [adjTransvSweep, List.map_append, List.map_cons, List.map_nil, matProd_append,
    matProd_cons, matProd_nil, matMul_id_right, matProd_replicate_idStep, stepMat_branchStep]
  funext x z
  simp only [matMul, rotPowMat, transv]
  have hleft : ∀ w : State d,
      (∑ y : State d, (if y = rot d p.val x then (1 : ZMod 2) else 0) *
        ((if w = rot d 1 y then 1 else 0) +
          (if y = rot d p.val u ∧ w = rot d (p.val + 1) (flipBit d u p) then 1 else 0))) =
      (if w = rot d (p.val + 1) x then 1 else 0) +
        (if x = u ∧ w = rot d (p.val + 1) (flipBit d u p) then 1 else 0) := by
    intro w
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [rot_add, Nat.add_comm 1 p.val]
    have hxu : (rot d p.val x = rot d p.val u) ↔ (x = u) :=
      ⟨rot_inj d p.val x u, fun h => h ▸ rfl⟩
    simp only [hxu]
  simp only [hleft, add_mul, Finset.sum_add_distrib]
  have hs1 : (∑ w : State d, (if w = rot d (p.val + 1) x then (1 : ZMod 2) else 0) *
      (if z = rot d (d - p.val) w then 1 else 0)) = if x = z then 1 else 0 := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      rot_add]
    have hsum : d - p.val + (p.val + 1) = d + 1 := by have := p.isLt; omega
    rw [hsum, rot_self]
    simp only [eq_comm]
  have hs2 : (∑ w : State d,
      (if x = u ∧ w = rot d (p.val + 1) (flipBit d u p) then (1 : ZMod 2) else 0) *
      (if z = rot d (d - p.val) w then 1 else 0)) =
      if x = u ∧ z = flipBit d u p then 1 else 0 := by
    by_cases hxu : x = u
    · simp only [hxu, true_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, rot_add]
      have hsum : d - p.val + (p.val + 1) = d + 1 := by have := p.isLt; omega
      rw [hsum, rot_self]
    · simp [hxu]
  rw [hs1, hs2]

def hammingDist (u v : State d) : ℕ :=
  (Finset.univ.filter (fun p : Fin (d + 1) => u p ≠ v p)).card

lemma hammingDist_pos (u v : State d) (huv : u ≠ v) : 0 < hammingDist d u v := by
  rw [hammingDist, Finset.card_pos]
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  apply huv
  funext p
  by_contra hne
  have : p ∈ Finset.univ.filter (fun p : Fin (d + 1) => u p ≠ v p) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ p, hne⟩
  rw [h] at this
  exact Finset.notMem_empty p this

lemma hammingDist_le (u v : State d) : hammingDist d u v ≤ d + 1 := by
  calc hammingDist d u v ≤ (Finset.univ : Finset (Fin (d + 1))).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = d + 1 := Fintype.card_fin (d + 1)

lemma hammingDist_flipBit (u v : State d) (p : Fin (d + 1)) (hp : u p ≠ v p) :
    hammingDist d (flipBit d u p) v + 1 = hammingDist d u v := by
  unfold hammingDist
  let S := Finset.univ.filter (fun q : Fin (d + 1) => u q ≠ v q)
  let S' := Finset.univ.filter (fun q : Fin (d + 1) => flipBit d u p q ≠ v q)
  have hpS : p ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩
  have hpS' : p ∉ S' := by
    intro h
    have hne := (Finset.mem_filter.mp h).2
    simp only [flipBit, ↓reduceIte] at hne
    cases hu : u p <;> cases hv : v p <;> simp [hu, hv] at hp hne
  have heq : insert p S' = S := by
    ext q
    simp only [Finset.mem_insert, S', S, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hqp : q = p
    · subst hqp; simp [hp]
    · simp [flipBit, hqp]
  change S'.card + 1 = S.card
  rw [← heq, Finset.card_insert_of_notMem hpS']

lemma realize_transv_aux :
    ∀ k : ℕ, 1 ≤ k →
      ∀ u v : State d, hammingDist d u v = k →
        ∃ sweeps : List (List (StepTable d)),
          (∀ sw ∈ sweeps, sw.length = d + 1) ∧
          sweeps.length ≤ 6 * (k - 1) + 1 ∧
          matProd (sweeps.flatten.map (stepMat d)) = transv u v := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro _ u v hdist
    have hpos : 0 < hammingDist d u v := by omega
    rw [hammingDist, Finset.card_pos] at hpos
    rcases hpos with ⟨p, hp⟩
    have hup : u p ≠ v p := (Finset.mem_filter.mp hp).2
    let u' := flipBit d u p
    have hdist' : hammingDist d u' v = k := by
      have := hammingDist_flipBit d u v p hup
      dsimp only [u']
      omega
    by_cases hk0 : k = 0
    · subst hk0
      have hu'v : u' = v := by
        by_contra hne
        have := hammingDist_pos d u' v hne
        omega
      refine ⟨[adjTransvSweep d u p], ?_, by simp, ?_⟩
      · intro sw hsw
        rcases List.mem_singleton.mp hsw with rfl
        exact adjTransvSweep_length d u p
      · simp only [List.flatten_cons, List.flatten_nil, List.append_nil, adjTransvSweep_mat]
        rw [← hu'v]
    · have hk1 : 1 ≤ k := by omega
      rcases ih hk1 u' v hdist' with ⟨sw', hsw'_len, hsw'_cnt, hsw'_mat⟩
      have hu'v : u' ≠ v := by
        intro heq
        subst heq
        have : hammingDist d u' u' = 0 := by simp [hammingDist]
        omega
      have huv : u ≠ v := by
        intro heq
        subst heq
        exact hup rfl
      have huu' : u ≠ u' := flipBit_ne d u p
      let swSwap : List (List (StepTable d)) :=
        [adjTransvSweep d u p, adjTransvSweep d u' p, adjTransvSweep d u p]
      have hswSwap_len : ∀ sw ∈ swSwap, sw.length = d + 1 := by
        intro sw hsw
        dsimp only [swSwap] at hsw
        rcases List.mem_cons.mp hsw with rfl | hsw
        · exact adjTransvSweep_length d u p
        · rcases List.mem_cons.mp hsw with rfl | hsw
          · exact adjTransvSweep_length d u' p
          · rcases List.mem_singleton.mp hsw with rfl
            exact adjTransvSweep_length d u p
      have hswSwap_mat : matProd (swSwap.flatten.map (stepMat d)) = swapMat u u' := by
        dsimp only [swSwap]
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.map_append,
          matProd_append, adjTransvSweep_mat, u', flipBit_invol]
        rw [← matMul_assoc]
        exact swapMat_eq_transv u (flipBit d u p) huu'
      refine ⟨swSwap ++ sw' ++ swSwap, ?_, ?_, ?_⟩
      · intro sw hsw
        rcases List.mem_append.mp hsw with hsw | hsw
        · rcases List.mem_append.mp hsw with hsw | hsw
          · exact hswSwap_len sw hsw
          · exact hsw'_len sw hsw
        · exact hswSwap_len sw hsw
      · simp only [List.length_append, swSwap, List.length_cons, List.length_nil]
        omega
      · simp only [List.flatten_append, List.map_append, matProd_append, hswSwap_mat, hsw'_mat]
        rw [conj_swap_transv]
        have h1 : swapFun u u' u' = u := by
          unfold swapFun
          simp [huu'.symm]
        have h2 : swapFun u u' v = v := by
          unfold swapFun
          simp [huv.symm, hu'v.symm]
        rw [h1, h2]

lemma realize_transv (u v : State d) (huv : u ≠ v) :
    ∃ sweeps : List (List (StepTable d)),
      (∀ sw ∈ sweeps, sw.length = d + 1) ∧
      sweeps.length ≤ 6 * (d + 1) ∧
      matProd (sweeps.flatten.map (stepMat d)) = transv u v := by
  have hpos := hammingDist_pos d u v huv
  have hle := hammingDist_le d u v
  rcases realize_transv_aux d (hammingDist d u v) hpos u v rfl with ⟨sw, hlen, hcnt, hmat⟩
  exact ⟨sw, hlen, by omega, hmat⟩

lemma realize_transvProd (L : List (State d × State d)) (hL : ∀ p ∈ L, p.1 ≠ p.2) :
    ∃ sweeps : List (List (StepTable d)),
      (∀ sw ∈ sweeps, sw.length = d + 1) ∧
      sweeps.length ≤ 6 * (d + 1) * L.length ∧
      matProd (sweeps.flatten.map (stepMat d)) = transvProd L := by
  induction L with
  | nil =>
    exact ⟨[], by simp, by simp, rfl⟩
  | cons p rest ih =>
    have hp := hL p (List.mem_cons_self ..)
    have hrest : ∀ q ∈ rest, q.1 ≠ q.2 := fun q hq => hL q (List.mem_cons_of_mem _ hq)
    rcases realize_transv d p.1 p.2 hp with ⟨sw1, h1len, h1cnt, h1mat⟩
    rcases ih hrest with ⟨sw2, h2len, h2cnt, h2mat⟩
    refine ⟨sw1 ++ sw2, ?_, ?_, ?_⟩
    · intro sw hsw
      rcases List.mem_append.mp hsw with hsw | hsw
      · exact h1len sw hsw
      · exact h2len sw hsw
    · simp only [List.length_append, List.length_cons]
      nlinarith
    · simp only [List.flatten_append, List.map_append, matProd_append, h1mat, h2mat, transvProd_cons]

lemma flatten_length_const {α : Type} (w : ℕ) (Ls : List (List α)) (h : ∀ L ∈ Ls, L.length = w) :
    Ls.flatten.length = Ls.length * w := by
  induction Ls with
  | nil => simp
  | cons L rest ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons,
      h L (List.mem_cons_self ..), ih (fun M hM => h M (List.mem_cons_of_mem _ hM))]
    ring

end ShiftRegister


section CLB105

lemma zmod2_testBit0_eq (a b : ℕ) (h : (a : ZMod 2) = (b : ZMod 2)) :
    a.testBit 0 = b.testBit 0 := by
  have h1 : (a : ZMod 2) = if a.testBit 0 then 1 else 0 := by
    rw [Nat.testBit_zero]
    have hmod : a % 2 = 0 ∨ a % 2 = 1 := by omega
    rw [← ZMod.natCast_mod a 2]
    rcases hmod with h0 | h1
    · simp [h0]
    · simp [h1]
  have h2 : (b : ZMod 2) = if b.testBit 0 then 1 else 0 := by
    rw [Nat.testBit_zero]
    have hmod : b % 2 = 0 ∨ b % 2 = 1 := by omega
    rw [← ZMod.natCast_mod b 2]
    rcases hmod with h0 | h1
    · simp [h0]
    · simp [h1]
  rw [h1, h2] at h
  cases ha : a.testBit 0 <;> cases hb : b.testBit 0 <;> simp [ha, hb] at h ⊢

lemma rotPowMat_inv_mul (d pad : ℕ) :
    matMul (rotPowMat d ((d + 1) - pad % (d + 1))) (rotPowMat d pad) = matId := by
  rw [matMul_rotPow]
  funext x y
  simp only [rotPowMat, matId]
  have hrot : rot d (((d + 1) - pad % (d + 1)) + pad) x = x := by
    funext j
    simp only [rot]
    congr 1; apply Fin.ext; dsimp only
    have hr : pad % (d + 1) < d + 1 := Nat.mod_lt pad (Nat.succ_pos d)
    have hdiv := Nat.div_add_mod pad (d + 1)
    have hcomm : (pad / (d + 1) + 1) * (d + 1) = (d + 1) * (pad / (d + 1)) + (d + 1) := by ring
    have hmul : (d + 1) - pad % (d + 1) + pad = (pad / (d + 1) + 1) * (d + 1) := by omega
    rw [hmul, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
  rw [hrot]
  simp only [eq_comm]

lemma shift_compiler (d : ℕ) (T : Mat (State d)) :
    ∃ tables : List (StepTable d),
      tables.length = (12 * (d + 1) * (2 ^ (d + 1)) * (2 ^ (d + 1) + 2) + 1) * (d + 1) ∧
      matProd (tables.map (stepMat d)) = T := by
  let w := d + 1
  let D := 2 ^ w
  have hD_pos : 1 ≤ D := Nat.one_le_pow w 2 (by omega)
  have hcard : Fintype.card (State d) = D := by
    simp [State, D, w, Fintype.card_bool, Fintype.card_fin]
  let e : State d ≃ Fin D := Fintype.equivFinOfCardEq hcard
  rcases gauss_elim_equiv D hD_pos e T with ⟨P, Q, R, hP_ne, hQ_ne, hP_len, hQ_len, hT⟩
  rcases realize_transvProd d P hP_ne with ⟨swP, hswP_len, hswP_cnt, hswP_mat⟩
  rcases realize_transvProd d Q hQ_ne with ⟨swQ, hswQ_len, hswQ_cnt, hswQ_mat⟩
  let S_core : List (List (StepTable d)) := swP ++ [diagSweep d R] ++ swQ
  have hScore_cnt : S_core.length ≤ 12 * w * D * (D + 2) + 1 := by
    simp only [S_core, List.length_append, List.length_singleton]
    have h1 : swP.length ≤ 6 * w * (D * (D + 2)) :=
      le_trans hswP_cnt (Nat.mul_le_mul_left (6 * w) hP_len)
    have h2 : swQ.length ≤ 6 * w * (D * (D + 2)) :=
      le_trans hswQ_cnt (Nat.mul_le_mul_left (6 * w) hQ_len)
    nlinarith
  let pad := (12 * w * D * (D + 2) + 1) - S_core.length
  let allSweeps : List (List (StepTable d)) := S_core ++ List.replicate pad (idSweep d)
  have hall_len : ∀ sw ∈ allSweeps, sw.length = w := by
    intro sw hsw
    rcases List.mem_append.mp hsw with hsw | hsw
    · rcases List.mem_append.mp hsw with hsw | hsw
      · rcases List.mem_append.mp hsw with hsw | hsw
        · exact hswP_len sw hsw
        · rcases List.mem_singleton.mp hsw with rfl
          exact diagSweep_length d R
      · exact hswQ_len sw hsw
    · rw [List.mem_replicate] at hsw
      rw [hsw.2]
      exact idSweep_length d
  have hall_cnt : allSweeps.length = 12 * w * D * (D + 2) + 1 := by
    simp only [allSweeps, List.length_append, List.length_replicate, pad]
    omega
  have hpad_mat : matProd ((List.replicate pad (idSweep d)).flatten.map (stepMat d)) = matId := by
    rw [List.map_flatten, matProd_flatten, List.map_map]
    have hmap : (List.replicate pad (idSweep d)).map (matProd ∘ List.map (stepMat d)) =
        List.replicate pad (matId : Mat (State d)) := by
      rw [List.map_replicate]
      congr 1
      exact idSweep_mat d
    rw [hmap, matProd_replicate_id]
  refine ⟨allSweeps.flatten, ?_, ?_⟩
  · rw [flatten_length_const w allSweeps hall_len, hall_cnt]
  · dsimp only [allSweeps, S_core]
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.map_append, matProd_append, hswP_mat, diagSweep_mat, hswQ_mat, hpad_mat, matMul_id_right]
    exact hT.symm

lemma shift_compiler_pad (d pad : ℕ) (T : Mat (State d)) :
    ∃ tables : List (StepTable d),
      tables.length = (12 * (d + 1) * (2 ^ (d + 1)) * (2 ^ (d + 1) + 2) + 1) * (d + 1) + pad ∧
      matProd (tables.map (stepMat d)) = T := by
  let T' : Mat (State d) := matMul T (rotPowMat d ((d + 1) - pad % (d + 1)))
  rcases shift_compiler d T' with ⟨tables0, hlen0, hmat0⟩
  refine ⟨tables0 ++ List.replicate pad (idStep d), ?_, ?_⟩
  · simp [hlen0]
  · simp only [List.map_append, matProd_append, hmat0, matProd_replicate_idStep, T', matMul_assoc,
      rotPowMat_inv_mul, matMul_id_right]

lemma card_cyclic_good_zmod2 (d leftLen rightLen : ℕ)
    (hL : d + 1 ≤ leftLen) (hR : d + 1 ≤ rightLen)
    (hn : 0 < leftLen + rightLen)
    (P : Fin leftLen × (Fin (d + 2) → Bool) → Bool)
    (Q : Fin rightLen × (Fin (d + 2) → Bool) → Bool) :
    let pos := fun k : ℕ => (⟨k % (leftLen + rightLen), Nat.mod_lt k hn⟩ : Fin (leftLen + rightLen))
    let good := fun x : Fin (leftLen + rightLen) → Bool =>
      (∀ i : Fin leftLen, P (i, fun j => x (pos (i.val + j.val))) = true) ∧
      ∀ i : Fin rightLen, Q (i, fun j => x (pos (leftLen + i.val + j.val))) = true
    let tablesP := List.ofFn (fun i : Fin leftLen => fun win : Fin (d + 2) → Bool => P (i, win))
    let tablesQ := List.ofFn (fun i : Fin rightLen => fun win : Fin (d + 2) → Bool => Q (i, win))
    ((Finset.univ.filter good).card : ZMod 2) =
      ∑ s1 : State d, ∑ s2 : State d,
        matProd (tablesP.map (stepMat d)) s1 s2 * matProd (tablesQ.map (stepMat d)) s2 s1 := by
  intro pos good tablesP tablesQ
  have hlenP : tablesP.length = leftLen := List.length_ofFn
  have hlenQ : tablesQ.length = rightLen := List.length_ofFn
  let startWin : (Fin (leftLen + rightLen) → Bool) → State d := fun x j => x (pos j.val)
  let midWin : (Fin (leftLen + rightLen) → Bool) → State d := fun x j => x (pos (leftLen + j.val))
  let F := fun p : State d × State d =>
    (Finset.univ.filter good).filter (fun x => startWin x = p.1 ∧ midWin x = p.2)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (State d × State d))) F := by
    intro p _ q _ hpq
    change Disjoint (F p) (F q)
    rw [Finset.disjoint_left]
    intro x hxp hxq
    have hp1 := (Finset.mem_filter.mp hxp).2
    have hq1 := (Finset.mem_filter.mp hxq).2
    exact hpq (Prod.ext (hp1.1.symm.trans hq1.1) (hp1.2.symm.trans hq1.2))
  have hbi : Finset.univ.filter good = (Finset.univ : Finset (State d × State d)).biUnion F := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, F, Finset.mem_filter]
    constructor
    · intro hx; exact ⟨(startWin x, midWin x), hx, rfl, rfl⟩
    · rintro ⟨_, hx, _, _⟩; exact hx
  have hF_card : ∀ p : State d × State d,
      (F p).card =
        (Finset.univ.filter (acceptsList d tablesP p.1 p.2)).card *
        (Finset.univ.filter (acceptsList d tablesQ p.2 p.1)).card := by
    rintro ⟨s1, s2⟩
    rw [← Finset.card_product]
    apply Finset.card_bij (fun x _ =>
      (fun k : Fin (tablesP.length + (d + 1)) => x (pos k.val),
       fun k : Fin (tablesQ.length + (d + 1)) => x (pos (leftLen + k.val))))
    · intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxgood, hs1, hs2⟩
      have hgood := (Finset.mem_filter.mp hxgood).2
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, ?_, ?_⟩, ⟨Finset.mem_univ _, ?_, ?_⟩⟩
      · intro j
        constructor
        · exact congrFun hs1 j
        · simp only [hlenP]
          exact congrFun hs2 j
      · intro i
        have hi := hgood.1 ⟨i.val, by omega⟩
        have hget : tablesP[i.val]'i.isLt = fun win => P (⟨i.val, by omega⟩, win) := by
          simp [tablesP]
        rw [hget]
        exact hi
      · intro j
        constructor
        · exact congrFun hs2 j
        · dsimp only
          have hjlt : j.val < leftLen + rightLen := by have := j.isLt; omega
          have hmod : (leftLen + (tablesQ.length + j.val)) % (leftLen + rightLen) = j.val := by
            have h1 : leftLen + (tablesQ.length + j.val) = j.val + (leftLen + rightLen) := by omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hjlt]
          have hpos : pos (leftLen + (tablesQ.length + j.val)) = pos j.val := by
            apply Fin.ext
            simp only [pos, hmod, Nat.mod_eq_of_lt hjlt]
          rw [hpos]
          exact congrFun hs1 j
      · intro i
        have hi := hgood.2 ⟨i.val, by omega⟩
        have hget : tablesQ[i.val]'i.isLt = fun win => Q (⟨i.val, by omega⟩, win) := by
          simp [tablesQ]
        rw [hget]
        convert hi using 2
        funext off
        dsimp only
        congr 1
        apply Fin.ext
        simp only [pos]
        have : leftLen + (i.val + off.val) = leftLen + i.val + off.val := by omega
        rw [this]
    · intro x1 _ x2 _ heq
      have hL_eq : (fun k : Fin (tablesP.length + (d + 1)) => x1 (pos k.val)) =
          (fun k : Fin (tablesP.length + (d + 1)) => x2 (pos k.val)) := congrArg Prod.fst heq
      have hR_eq : (fun k : Fin (tablesQ.length + (d + 1)) => x1 (pos (leftLen + k.val))) =
          (fun k : Fin (tablesQ.length + (d + 1)) => x2 (pos (leftLen + k.val))) := congrArg Prod.snd heq
      funext k
      by_cases hk : k.val < leftLen
      · have hf := congrFun hL_eq ⟨k.val, by omega⟩
        have hp : pos k.val = k := Fin.ext (Nat.mod_eq_of_lt k.isLt)
        simpa only [hp] using hf
      · have hf := congrFun hR_eq ⟨k.val - leftLen, by have := k.isLt; omega⟩
        have hp : pos (leftLen + (k.val - leftLen)) = k := by
          apply Fin.ext
          have : leftLen + (k.val - leftLen) = k.val := by omega
          simp only [pos, this, Nat.mod_eq_of_lt k.isLt]
        simpa only [hp] using hf
    · rintro ⟨wL, wR⟩ hw
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hw
      have haccL := hw.1.2
      have haccR := hw.2.2
      let x : Fin (leftLen + rightLen) → Bool := fun k =>
        if hk : k.val < leftLen then wL ⟨k.val, by omega⟩
        else wR ⟨k.val - leftLen, by have := k.isLt; omega⟩
      have hxL : ∀ k : Fin (tablesP.length + (d + 1)), x (pos k.val) = wL k := by
        intro k
        have hklt : k.val < leftLen + rightLen := by have := k.isLt; omega
        have hposv : (pos k.val).val = k.val := Nat.mod_eq_of_lt hklt
        dsimp only [x]
        by_cases hk : k.val < leftLen
        · have hk' : (pos k.val).val < leftLen := by omega
          rw [dif_pos hk']
          congr 1; exact Fin.ext hposv
        · have hk' : ¬ (pos k.val).val < leftLen := by omega
          rw [dif_neg hk']
          have hj : k.val - leftLen < d + 1 := by have := k.isLt; omega
          have h1 := (haccR.1 ⟨k.val - leftLen, hj⟩).1
          have h2 := (haccL.1 ⟨k.val - leftLen, hj⟩).2
          dsimp only at h1 h2
          have hidx1 : (⟨(pos k.val).val - leftLen, by have := (pos k.val).isLt; omega⟩ : Fin (tablesQ.length + (d + 1))) =
              ⟨k.val - leftLen, by omega⟩ := Fin.ext (by dsimp only; omega)
          have hidx2 : (⟨tablesP.length + (k.val - leftLen), by omega⟩ : Fin (tablesP.length + (d + 1))) = k :=
            Fin.ext (by dsimp only; omega)
          rw [hidx1, h1, ← h2, hidx2]
      have hxR : ∀ k : Fin (tablesQ.length + (d + 1)), x (pos (leftLen + k.val)) = wR k := by
        intro k
        dsimp only [x]
        by_cases hk : k.val < rightLen
        · have hklt : leftLen + k.val < leftLen + rightLen := by omega
          have hposv : (pos (leftLen + k.val)).val = leftLen + k.val := Nat.mod_eq_of_lt hklt
          have hk' : ¬ (pos (leftLen + k.val)).val < leftLen := by omega
          rw [dif_neg hk']
          congr 1; apply Fin.ext; dsimp only; omega
        · have hj : k.val - rightLen < d + 1 := by have := k.isLt; omega
          have hposv : (pos (leftLen + k.val)).val = k.val - rightLen := by
            have h1 : leftLen + k.val = (k.val - rightLen) + (leftLen + rightLen) := by omega
            simp only [pos, h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : k.val - rightLen < leftLen + rightLen)]
          have hk' : (pos (leftLen + k.val)).val < leftLen := by omega
          rw [dif_pos hk']
          have h1 := (haccL.1 ⟨k.val - rightLen, hj⟩).1
          have h2 := (haccR.1 ⟨k.val - rightLen, hj⟩).2
          dsimp only at h1 h2
          have hidx1 : (⟨(pos (leftLen + k.val)).val, by omega⟩ : Fin (tablesP.length + (d + 1))) =
              ⟨k.val - rightLen, by omega⟩ := Fin.ext (by dsimp only; omega)
          have hidx2 : (⟨tablesQ.length + (k.val - rightLen), by omega⟩ : Fin (tablesQ.length + (d + 1))) = k :=
            Fin.ext (by dsimp only; omega)
          rw [hidx1, h1, ← h2, hidx2]
      refine ⟨x, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_filter]
        refine ⟨⟨Finset.mem_univ _, ?_, ?_⟩, ?_, ?_⟩
        · intro i
          have hi := haccL.2 ⟨i.val, by omega⟩
          have hget : tablesP[i.val]'(by omega) = fun win => P (i, win) := by
            simp [tablesP]
          rw [hget] at hi
          convert hi using 2
          congr 1
          funext off
          exact hxL ⟨i.val + off.val, by have := i.isLt; have := off.isLt; omega⟩
        · intro i
          have hi := haccR.2 ⟨i.val, by omega⟩
          have hget : tablesQ[i.val]'(by omega) = fun win => Q (i, win) := by
            simp [tablesQ]
          rw [hget] at hi
          convert hi using 2
          congr 1
          funext off
          have h1 : leftLen + i.val + off.val = leftLen + (i.val + off.val) := by omega
          rw [h1]
          exact hxR ⟨i.val + off.val, by have := i.isLt; have := off.isLt; omega⟩
        · funext j
          dsimp only [startWin]
          rw [hxL ⟨j.val, by omega⟩]
          exact (haccL.1 j).1
        · funext j
          dsimp only [midWin]
          rw [hxR ⟨j.val, by omega⟩]
          exact (haccR.1 j).1
      · apply Prod.ext
        · funext k; exact hxL k
        · funext k; exact hxR k
  rw [hbi, Finset.card_biUnion hdisj, Nat.cast_sum]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s1 _
  apply Finset.sum_congr rfl
  intro s2 _
  rw [hF_card (s1, s2), Nat.cast_mul, card_acceptsList_zmod2, card_acceptsList_zmod2]

abbrev VecZ (m : ℕ) := Fin m → ZMod 2

def dotZ (m : ℕ) (u v : VecZ m) : ZMod 2 := ∑ j : Fin m, u j * v j

lemma vecZ_add_self (m : ℕ) (x : VecZ m) : x + x = 0 := by
  funext j; exact zmod2_add_self (x j)

lemma dotZ_zero_left (m : ℕ) (v : VecZ m) : dotZ m 0 v = 0 := by simp [dotZ]

lemma dotZ_zero_right (m : ℕ) (u : VecZ m) : dotZ m u 0 = 0 := by simp [dotZ]

lemma dotZ_comm (m : ℕ) (u v : VecZ m) : dotZ m u v = dotZ m v u := by
  unfold dotZ; apply Finset.sum_congr rfl; intro j _; ring

lemma dotZ_add_left (m : ℕ) (u v w : VecZ m) : dotZ m (u + v) w = dotZ m u w + dotZ m v w := by
  simp only [dotZ, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dotZ_add_right (m : ℕ) (u v w : VecZ m) : dotZ m u (v + w) = dotZ m u v + dotZ m u w := by
  simp only [dotZ, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma card_dotZ_eq (m : ℕ) (hm : 1 ≤ m) (u : VecZ m) (hu : u ≠ 0) (a : ZMod 2) :
    (Finset.univ.filter (fun x : VecZ m => dotZ m u x = a)).card = 2 ^ (m - 1) := by
  have hex : ∃ i : Fin m, u i = 1 := by
    by_contra h
    apply hu
    funext i
    rcases zmod2_eq_zero_or_one (u i) with h0 | h1
    · exact h0
    · exact absurd ⟨i, h1⟩ h
  rcases hex with ⟨i, hi⟩
  let e1 : VecZ m := Pi.single i 1
  have he1 : dotZ m u e1 = 1 := by simp [dotZ, e1, Pi.single_apply, hi]
  let S0 := Finset.univ.filter (fun x : VecZ m => dotZ m u x = 0)
  let S1 := Finset.univ.filter (fun x : VecZ m => dotZ m u x = 1)
  have hdisj : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]
    intro x h0 h1
    have hx0 := (Finset.mem_filter.mp h0).2
    have hx1 := (Finset.mem_filter.mp h1).2
    rw [hx0] at hx1; exact absurd hx1 (by decide)
  have hunion : S0 ∪ S1 = Finset.univ := by
    ext x
    simp only [Finset.mem_union, S0, S1, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact zmod2_eq_zero_or_one (dotZ m u x)
  have hbij : S0.card = S1.card := by
    apply Finset.card_bij (fun x _ => x + e1)
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [dotZ_add_right, hx.2, he1, zero_add]
    · intro x _ y _ heq
      have h := congrArg (fun z => z + e1) heq
      simpa only [add_assoc, vecZ_add_self, add_zero] using h
    · intro y hy
      rw [Finset.mem_filter] at hy
      refine ⟨y + e1, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [dotZ_add_right, hy.2, he1, zmod2_add_self]
      · simp only [add_assoc, vecZ_add_self, add_zero]
  have htot : S0.card + S1.card = 2 ^ m := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
    simp [VecZ]
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    have : m = (m - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ]
    ring
  rcases zmod2_eq_zero_or_one a with rfl | rfl
  · change S0.card = 2 ^ (m - 1); omega
  · change S1.card = 2 ^ (m - 1); omega

def chiZ (a : ZMod 2) : ℤ := if a = 0 then 1 else -1

lemma chiZ_add (a b : ZMod 2) : chiZ (a + b) = chiZ a * chiZ b := by
  fin_cases a <;> fin_cases b <;> decide

lemma sum_chiZ_dot (m : ℕ) (hm : 1 ≤ m) (z : VecZ m) :
    (∑ v : VecZ m, chiZ (dotZ m z v)) = if z = 0 then (2 ^ m : ℤ) else 0 := by
  by_cases hz : z = 0
  · subst hz
    simp only [dotZ_zero_left, chiZ, ↓reduceIte, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one]
    simp [VecZ]
  · simp only [hz, ↓reduceIte]
    let S0 := Finset.univ.filter (fun v : VecZ m => dotZ m z v = 0)
    let S1 := Finset.univ.filter (fun v : VecZ m => dotZ m z v = 1)
    have hdisj : Disjoint S0 S1 := by
      rw [Finset.disjoint_left]
      intro v h0 h1
      have hv0 := (Finset.mem_filter.mp h0).2
      have hv1 := (Finset.mem_filter.mp h1).2
      rw [hv0] at hv1; exact absurd hv1 (by decide)
    have hunion : S0 ∪ S1 = Finset.univ := by
      ext v
      simp only [Finset.mem_union, S0, S1, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact zmod2_eq_zero_or_one (dotZ m z v)
    rw [← hunion, Finset.sum_union hdisj]
    have h0 : (∑ v ∈ S0, chiZ (dotZ m z v)) = (S0.card : ℤ) := by
      have : ∀ v ∈ S0, chiZ (dotZ m z v) = 1 := fun v hv => by
        simp [chiZ, (Finset.mem_filter.mp hv).2]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h1 : (∑ v ∈ S1, chiZ (dotZ m z v)) = -(S1.card : ℤ) := by
      have : ∀ v ∈ S1, chiZ (dotZ m z v) = -1 := fun v hv => by
        have hvv := (Finset.mem_filter.mp hv).2
        simp only [chiZ, hvv]; decide
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [h0, h1, card_dotZ_eq m hm z hz 0, card_dotZ_eq m hm z hz 1]
    ring

lemma card_rect_dotZ_le (m : ℕ) (hm : 1 ≤ m) (U W : Finset (VecZ m))
    (hUW : ∀ u ∈ U, ∀ v ∈ W, dotZ m u v = 1) :
    U.card * W.card ≤ 2 ^ (m - 1) := by
  by_cases hU : U = ∅
  · simp [hU]
  by_cases hW : W = ∅
  · simp [hW]
  rcases Finset.nonempty_iff_ne_empty.mpr hU with ⟨a, ha⟩
  rcases Finset.nonempty_iff_ne_empty.mpr hW with ⟨b, hb⟩
  let K : Finset (VecZ m) := Finset.univ.filter (fun z : VecZ m => ∀ v ∈ W, dotZ m z v = 0)
  have hK0 : (0 : VecZ m) ∈ K := by
    simp [K, dotZ_zero_left]
  have hKadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K := by
    intro x hx y hy
    rw [Finset.mem_filter] at hx hy ⊢
    refine ⟨Finset.mem_univ _, fun v hv => ?_⟩
    rw [dotZ_add_left, hx.2 v hv, hy.2 v hv, add_zero]
  have hUK : U.card ≤ K.card := by
    have hinj : (U.image (fun u => u + a)).card = U.card := by
      apply Finset.card_image_of_injOn
      intro u1 _ u2 _ heq
      have h := congrArg (fun z => z + a) heq
      simpa only [add_assoc, vecZ_add_self, add_zero] using h
    rw [← hinj]
    apply Finset.card_le_card
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨u, hu, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun v hv => ?_⟩
    rw [dotZ_add_left, hUW u hu v hv, hUW a ha v hv, zmod2_add_self]
  let L : Finset (VecZ m) := Finset.univ.filter (fun v : VecZ m => ∀ z ∈ K, dotZ m z v = 0)
  have hKL : K.card * L.card = 2 ^ m := by
    have hway1 : (∑ z ∈ K, ∑ v : VecZ m, chiZ (dotZ m z v)) = (2 ^ m : ℤ) := by
      have hsub : ∀ z ∈ K, (∑ v : VecZ m, chiZ (dotZ m z v)) = if z = 0 then (2 ^ m : ℤ) else 0 :=
        fun z _ => sum_chiZ_dot m hm z
      rw [Finset.sum_congr rfl hsub, Finset.sum_ite_eq']
      simp only [hK0, ↓reduceIte]
    have hway2 : (∑ v : VecZ m, ∑ z ∈ K, chiZ (dotZ m z v)) = (L.card : ℤ) * (K.card : ℤ) := by
      have hterm : ∀ v : VecZ m, (∑ z ∈ K, chiZ (dotZ m z v)) = if v ∈ L then (K.card : ℤ) else 0 := by
        intro v
        by_cases hv : v ∈ L
        · simp only [hv, ↓reduceIte]
          have hall : ∀ z ∈ K, chiZ (dotZ m z v) = 1 := fun z hz => by
            have := (Finset.mem_filter.mp hv).2 z hz
            simp [chiZ, this]
          rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, mul_one]
        · simp only [hv, ↓reduceIte]
          have hex : ∃ z0 ∈ K, dotZ m z0 v = 1 := by
            by_contra hno
            apply hv
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ _, fun z hz => ?_⟩
            rcases zmod2_eq_zero_or_one (dotZ m z v) with h0 | h1
            · exact h0
            · exact absurd ⟨z, hz, h1⟩ hno
          rcases hex with ⟨z0, hz0, hzv⟩
          have hneg : (∑ z ∈ K, chiZ (dotZ m z v)) = -(∑ z ∈ K, chiZ (dotZ m z v)) := by
            have hbij : (∑ z ∈ K, chiZ (dotZ m (z + z0) v)) = ∑ z ∈ K, chiZ (dotZ m z v) := by
              apply Finset.sum_bij (fun z _ => z + z0)
              · intro z hz; exact hKadd z hz z0 hz0
              · intro z1 _ z2 _ heq
                have h := congrArg (fun t => t + z0) heq
                simpa only [add_assoc, vecZ_add_self, add_zero] using h
              · intro w hw
                refine ⟨w + z0, hKadd w hw z0 hz0, ?_⟩
                simp only [add_assoc, vecZ_add_self, add_zero]
              · intro _ _; rfl
            have hflip : ∀ z ∈ K, chiZ (dotZ m (z + z0) v) = -chiZ (dotZ m z v) := by
              intro z _
              rw [dotZ_add_left, chiZ_add, hzv]
              have hc : chiZ 1 = -1 := by decide
              rw [hc]; ring
            calc (∑ z ∈ K, chiZ (dotZ m z v))
                = ∑ z ∈ K, chiZ (dotZ m (z + z0) v) := hbij.symm
              _ = ∑ z ∈ K, -chiZ (dotZ m z v) := Finset.sum_congr rfl hflip
              _ = -(∑ z ∈ K, chiZ (dotZ m z v)) := Finset.sum_neg_distrib (f := fun z => chiZ (dotZ m z v))
          linarith
      simp_rw [hterm]
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
      have hfilt : (Finset.univ : Finset (VecZ m)).filter (fun v => v ∈ L) = L := by
        ext v; simp
      rw [hfilt]
    have hZ : (L.card : ℤ) * (K.card : ℤ) = (2 ^ m : ℤ) := by
      rw [← hway2, Finset.sum_comm, hway1]
    have hN : L.card * K.card = 2 ^ m := by exact_mod_cast hZ
    linarith
  let L0 := L.filter (fun v => dotZ m a v = 0)
  let L1 := L.filter (fun v => dotZ m a v = 1)
  have hdisjL : Disjoint L0 L1 := by
    rw [Finset.disjoint_left]
    intro v h0 h1
    have hv0 := (Finset.mem_filter.mp h0).2
    have hv1 := (Finset.mem_filter.mp h1).2
    rw [hv0] at hv1; exact absurd hv1 (by decide)
  have hunionL : L0 ∪ L1 = L := by
    ext v
    simp only [Finset.mem_union, L0, L1, Finset.mem_filter]
    constructor
    · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
    · intro hv
      rcases zmod2_eq_zero_or_one (dotZ m a v) with h0 | h1
      · left; exact ⟨hv, h0⟩
      · right; exact ⟨hv, h1⟩
  have hWL1 : W ⊆ L1 := by
    intro v hv
    rw [Finset.mem_filter, Finset.mem_filter]
    exact ⟨⟨Finset.mem_univ _, fun z hz => (Finset.mem_filter.mp hz).2 v hv⟩, hUW a ha v hv⟩
  have hbL : b ∈ L := (Finset.mem_filter.mp (hWL1 hb)).1
  have hb1 : dotZ m a b = 1 := hUW a ha b hb
  have hLadd : ∀ v1 ∈ L, ∀ v2 ∈ L, v1 + v2 ∈ L := by
    intro v1 hv1 v2 hv2
    rw [Finset.mem_filter] at hv1 hv2 ⊢
    refine ⟨Finset.mem_univ _, fun z hz => ?_⟩
    rw [dotZ_add_right, hv1.2 z hz, hv2.2 z hz, add_zero]
  have hL0L1 : L0.card = L1.card := by
    apply Finset.card_bij (fun v _ => v + b)
    · intro v hv
      rw [Finset.mem_filter] at hv ⊢
      refine ⟨hLadd v hv.1 b hbL, ?_⟩
      rw [dotZ_add_right, hv.2, hb1, zero_add]
    · intro v1 _ v2 _ heq
      have h := congrArg (fun t => t + b) heq
      simpa only [add_assoc, vecZ_add_self, add_zero] using h
    · intro v hv
      rw [Finset.mem_filter] at hv
      refine ⟨v + b, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨hLadd v hv.1 b hbL, ?_⟩
        rw [dotZ_add_right, hv.2, hb1, zmod2_add_self]
      · simp only [add_assoc, vecZ_add_self, add_zero]
  have hL2 : 2 * L1.card = L.card := by
    have h := Finset.card_union_of_disjoint hdisjL
    rw [hunionL, hL0L1] at h
    omega
  have hWL : W.card ≤ L1.card := Finset.card_le_card hWL1
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    have : m = (m - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ]
    ring
  have h1 : 2 * (U.card * W.card) ≤ K.card * (2 * L1.card) := by
    have hmul : U.card * W.card ≤ K.card * L1.card := Nat.mul_le_mul hUK hWL
    linarith
  rw [hL2, hKL, hpow] at h1
  omega

lemma card_dotZ_ones (m : ℕ) (hm : 1 ≤ m) :
    (Finset.univ.filter (fun p : VecZ m × VecZ m => dotZ m p.1 p.2 = 1)).card =
      (2 ^ m - 1) * 2 ^ (m - 1) := by
  have hsum : (Finset.univ.filter (fun p : VecZ m × VecZ m => dotZ m p.1 p.2 = 1)).card =
      ∑ u : VecZ m, (Finset.univ.filter (fun v : VecZ m => dotZ m u v = 1)).card := by
    have h1 : (Finset.univ.filter (fun p : VecZ m × VecZ m => dotZ m p.1 p.2 = 1)).card =
        ∑ p : VecZ m × VecZ m, if dotZ m p.1 p.2 = 1 then 1 else 0 := by
      rw [Finset.sum_boole, Nat.cast_id]
    rw [h1, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.sum_boole, Nat.cast_id]
  rw [hsum]
  have hsplit : (∑ u : VecZ m, (Finset.univ.filter (fun v : VecZ m => dotZ m u v = 1)).card) =
      (Finset.univ.filter (fun v : VecZ m => dotZ m 0 v = 1)).card +
      ∑ u ∈ (Finset.univ : Finset (VecZ m)).erase 0,
        (Finset.univ.filter (fun v : VecZ m => dotZ m u v = 1)).card :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ (0 : VecZ m))).symm
  have hzero : (Finset.univ.filter (fun v : VecZ m => dotZ m 0 v = 1)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v _
    rw [dotZ_zero_left]
    decide
  have hnz : ∀ u ∈ (Finset.univ : Finset (VecZ m)).erase 0,
      (Finset.univ.filter (fun v : VecZ m => dotZ m u v = 1)).card = 2 ^ (m - 1) := by
    intro u hu
    exact card_dotZ_eq m hm u (Finset.mem_erase.mp hu).1 1
  rw [hsplit, hzero, zero_add, Finset.sum_congr rfl hnz, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
  simp [VecZ]

end CLB105

end PEqualNP.Outside.L_clb_105_aux

theorem PEqualNP.Outside.L_clb_105 : (∀ (d paddingLeft paddingRight : ℕ),
  let w := d + 1
  let D := 2 ^ w
  let L := (12 * w * D * (D + 2) + 1) * w
  let leftLen := L + paddingLeft
  let rightLen := L + paddingRight
  let n := leftLen + rightLen
  let pos := fun k : ℕ => (⟨k % n, Nat.mod_lt _ (Nat.add_pos_left (Nat.add_pos_left (Nat.mul_pos (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)) _) _)⟩ : Fin n)
  let Raw := fun len : ℕ => Fin len × (Fin (w + 1) → Bool)
  let oddCount := fun (P : Raw leftLen → Bool) (Q : Raw rightLen → Bool) =>
    let good := fun x : Fin n → Bool =>
      (∀ i : Fin leftLen, P (i, fun j => x (pos (i.val + j.val))) = true) ∧
      ∀ i : Fin rightLen, Q (i, fun j => x (pos (leftLen + i.val + j.val))) = true
    (Finset.univ.filter good).card.testBit 0
  let Vector := Fin (D * D) → Bool
  let dot := fun (u v : Vector) =>
    (Finset.univ.filter (fun coord : Fin (D * D) => u coord = true ∧ v coord = true)).card.testBit 0
  ∃ (first : (Raw leftLen → Bool) → Vector) (last : (Raw rightLen → Bool) → Vector),
    Function.Surjective first ∧ Function.Surjective last ∧
    (∀ P Q, oddCount P Q = dot (first P) (last Q)) ∧
    (∀ P P', first P = first P' ↔ ∀ R, oddCount P R = oddCount P' R) ∧
    ∀ count : ℕ,
      (∃ (A : Fin count → (Raw leftLen → Bool) → Prop)
         (B : Fin count → (Raw rightLen → Bool) → Prop),
        ∀ P Q, oddCount P Q = true ↔ ∃ i : Fin count, A i P ∧ B i Q) ↔
      2 ^ (D * D) - 1 ≤ count) := by
  intro d paddingLeft paddingRight w D L leftLen rightLen n pos Raw oddCount Vector dot
  open PEqualNP.Outside.L_clb_105_aux in
  have hcardS : Fintype.card (State d) = D := by
    simp [State, D, w, Fintype.card_bool, Fintype.card_fin]
  let eS : State d ≃ Fin D := Fintype.equivFinOfCardEq hcardS
  let ePair : State d × State d ≃ Fin (D * D) := (Equiv.prodCongr eS eS).trans finProdFinEquiv
  let matOfP : (Raw leftLen → Bool) → Mat (State d) := fun P =>
    matProd ((List.ofFn (fun i : Fin leftLen => fun win : Fin (w + 1) → Bool => P (i, win))).map (stepMat d))
  let matOfQ : (Raw rightLen → Bool) → Mat (State d) := fun Q =>
    matProd ((List.ofFn (fun i : Fin rightLen => fun win : Fin (w + 1) → Bool => Q (i, win))).map (stepMat d))
  let first : (Raw leftLen → Bool) → Vector := fun P coord =>
    decide (matOfP P (ePair.symm coord).1 (ePair.symm coord).2 = 1)
  let last : (Raw rightLen → Bool) → Vector := fun Q coord =>
    decide (matOfQ Q (ePair.symm coord).2 (ePair.symm coord).1 = 1)
  have hsurjF : Function.Surjective first := by
    intro v
    let T : Mat (State d) := fun s1 s2 => if v (ePair (s1, s2)) = true then 1 else 0
    rcases shift_compiler_pad d paddingLeft T with ⟨tables, hlen, hmat⟩
    have hlen' : tables.length = leftLen := hlen
    let P : Raw leftLen → Bool := fun (p : Fin leftLen × (Fin (w + 1) → Bool)) =>
      (tables[p.1.val]'(by have := p.1.isLt; omega)) p.2
    refine ⟨P, ?_⟩
    have hlist : List.ofFn (fun i : Fin leftLen => fun win : Fin (w + 1) → Bool => P (i, win)) = tables := by
      apply List.ext_getElem
      · simp [hlen']
      · intro i hi1 hi2
        simp [P]
    have hMP : matOfP P = T := by
      dsimp only [matOfP]
      rw [hlist, hmat]
    funext coord
    dsimp only [first]
    rw [hMP]
    dsimp only [T]
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]
    cases hv : v coord <;> decide
  have hsurjL : Function.Surjective last := by
    intro v
    let T : Mat (State d) := fun s2 s1 => if v (ePair (s1, s2)) = true then 1 else 0
    rcases shift_compiler_pad d paddingRight T with ⟨tables, hlen, hmat⟩
    have hlen' : tables.length = rightLen := hlen
    let Q : Raw rightLen → Bool := fun (p : Fin rightLen × (Fin (w + 1) → Bool)) =>
      (tables[p.1.val]'(by have := p.1.isLt; omega)) p.2
    refine ⟨Q, ?_⟩
    have hlist : List.ofFn (fun i : Fin rightLen => fun win : Fin (w + 1) → Bool => Q (i, win)) = tables := by
      apply List.ext_getElem
      · simp [hlen']
      · intro i hi1 hi2
        simp [Q]
    have hMQ : matOfQ Q = T := by
      dsimp only [matOfQ]
      rw [hlist, hmat]
    funext coord
    dsimp only [last]
    rw [hMQ]
    dsimp only [T]
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]
    cases hv : v coord <;> decide
  have hodd : ∀ P Q, oddCount P Q = dot (first P) (last Q) := by
    intro P Q
    dsimp only [oddCount, dot]
    apply zmod2_testBit0_eq
    have hL_ge : d + 1 ≤ leftLen := by
      have h1 : 1 ≤ 12 * w * D * (D + 2) + 1 := by omega
      have h2 : w ≤ (12 * w * D * (D + 2) + 1) * w := Nat.le_mul_of_pos_left w h1
      dsimp only [leftLen, L, w] at h2 ⊢
      omega
    have hR_ge : d + 1 ≤ rightLen := by
      have h1 : 1 ≤ 12 * w * D * (D + 2) + 1 := by omega
      have h2 : w ≤ (12 * w * D * (D + 2) + 1) * w := Nat.le_mul_of_pos_left w h1
      dsimp only [rightLen, L, w] at h2 ⊢
      omega
    have hn_pos : 0 < leftLen + rightLen := by omega
    have hcyc := card_cyclic_good_zmod2 d leftLen rightLen hL_ge hR_ge hn_pos P Q
    change ((Finset.univ.filter (fun x : Fin (leftLen + rightLen) → Bool =>
      (∀ i : Fin leftLen, P (i, fun j => x (pos (i.val + j.val))) = true) ∧
      ∀ i : Fin rightLen, Q (i, fun j => x (pos (leftLen + i.val + j.val))) = true)).card : ZMod 2) = _
    rw [hcyc]
    have hsum1 : (∑ s1 : State d, ∑ s2 : State d, matOfP P s1 s2 * matOfQ Q s2 s1) =
        ∑ p : State d × State d, matOfP P p.1 p.2 * matOfQ Q p.2 p.1 :=
      (Fintype.sum_prod_type (fun p : State d × State d => matOfP P p.1 p.2 * matOfQ Q p.2 p.1)).symm
    change (∑ s1 : State d, ∑ s2 : State d, matOfP P s1 s2 * matOfQ Q s2 s1) = _
    rw [hsum1, ← Equiv.sum_comp ePair.symm]
    have hterm : ∀ coord : Fin (D * D),
        matOfP P (ePair.symm coord).1 (ePair.symm coord).2 *
          matOfQ Q (ePair.symm coord).2 (ePair.symm coord).1 =
        if first P coord = true ∧ last Q coord = true then (1 : ZMod 2) else 0 := by
      intro coord
      dsimp only [first, last]
      rcases zmod2_eq_zero_or_one (matOfP P (ePair.symm coord).1 (ePair.symm coord).2) with hp | hp <;>
      rcases zmod2_eq_zero_or_one (matOfQ Q (ePair.symm coord).2 (ePair.symm coord).1) with hq | hq <;>
      simp [hp, hq]
    simp_rw [hterm]
    rw [Finset.sum_boole]
  have hsep : ∀ P P', first P = first P' ↔ ∀ R, oddCount P R = oddCount P' R := by
    intro P P'
    constructor
    · intro h R
      rw [hodd P R, hodd P' R, h]
    · intro h
      funext c
      rcases hsurjL (fun j : Fin (D * D) => decide (j = c)) with ⟨R, hR⟩
      have hdot_unit : ∀ u : Vector, dot u (fun j : Fin (D * D) => decide (j = c)) = u c := by
        intro u
        dsimp only [dot]
        by_cases huc : u c = true
        · have hfilt : Finset.univ.filter (fun coord : Fin (D * D) => u coord = true ∧ decide (coord = c) = true) = {c} := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
              Finset.mem_singleton]
            constructor
            · rintro ⟨_, rfl⟩; rfl
            · rintro rfl; exact ⟨huc, rfl⟩
          rw [hfilt, Finset.card_singleton, huc]; rfl
        · have hucf : u c = false := Bool.eq_false_iff.mpr huc
          have hfilt : Finset.univ.filter (fun coord : Fin (D * D) => u coord = true ∧ decide (coord = c) = true) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro j _ ⟨hj1, hj2⟩
            rw [decide_eq_true_eq] at hj2
            subst hj2
            exact huc hj1
          rw [hfilt, Finset.card_empty, hucf]; rfl
      have hPR := h R
      rw [hodd P R, hodd P' R, hR, hdot_unit, hdot_unit] at hPR
      exact hPR
  refine ⟨first, last, hsurjF, hsurjL, hodd, hsep, ?_⟩
  intro count
  have hm_pos : 1 ≤ D * D := by
    have hD1 : 1 ≤ D := Nat.one_le_pow w 2 (by omega)
    nlinarith
  let toZ : Vector → VecZ (D * D) := fun u c => if u c = true then 1 else 0
  let fromZ : VecZ (D * D) → Vector := fun u c => decide (u c = 1)
  have htoFrom : ∀ u : VecZ (D * D), toZ (fromZ u) = u := by
    intro u; funext c; dsimp only [toZ, fromZ]
    rcases zmod2_eq_zero_or_one (u c) with h0 | h1
    · simp [h0]
    · simp [h1]
  have hdotZ_iff : ∀ u v : VecZ (D * D), dot (fromZ u) (fromZ v) = true ↔ dotZ (D * D) u v = 1 := by
    intro u v
    dsimp only [dot]
    have hcast : ((Finset.univ.filter (fun coord : Fin (D * D) =>
        fromZ u coord = true ∧ fromZ v coord = true)).card : ZMod 2) = dotZ (D * D) u v := by
      rw [← Finset.sum_boole]
      unfold dotZ
      apply Finset.sum_congr rfl
      intro c _
      dsimp only [fromZ]
      rcases zmod2_eq_zero_or_one (u c) with hu | hu <;>
      rcases zmod2_eq_zero_or_one (v c) with hv | hv <;> simp [hu, hv]
    constructor
    · intro h
      have htb : (Finset.univ.filter (fun coord : Fin (D * D) =>
          fromZ u coord = true ∧ fromZ v coord = true)).card.testBit 0 = true := h
      rw [Nat.testBit_zero, decide_eq_true_eq] at htb
      rw [← hcast, ← ZMod.natCast_mod _ 2, htb]
      rfl
    · intro h
      apply zmod2_testBit0
      rw [hcast, h]
      rfl
  constructor
  · rintro ⟨A, B, hcov⟩
    classical
    let secL : VecZ (D * D) → (Raw leftLen → Bool) := fun u => Classical.choose (hsurjF (fromZ u))
    let secR : VecZ (D * D) → (Raw rightLen → Bool) := fun v => Classical.choose (hsurjL (fromZ v))
    have hsecL : ∀ u : VecZ (D * D), first (secL u) = fromZ u :=
      fun u => Classical.choose_spec (hsurjF (fromZ u))
    have hsecR : ∀ v : VecZ (D * D), last (secR v) = fromZ v :=
      fun v => Classical.choose_spec (hsurjL (fromZ v))
    let U : Fin count → Finset (VecZ (D * D)) := fun i =>
      Finset.univ.filter (fun u => A i (secL u))
    let W : Fin count → Finset (VecZ (D * D)) := fun i =>
      Finset.univ.filter (fun v => B i (secR v))
    have hrect : ∀ i : Fin count, (U i).card * (W i).card ≤ 2 ^ (D * D - 1) := by
      intro i
      apply card_rect_dotZ_le (D * D) hm_pos (U i) (W i)
      intro u hu v hv
      have huA : A i (secL u) := (Finset.mem_filter.mp hu).2
      have hvB : B i (secR v) := (Finset.mem_filter.mp hv).2
      have hodd1 : oddCount (secL u) (secR v) = true := (hcov (secL u) (secR v)).mpr ⟨i, huA, hvB⟩
      rw [hodd, hsecL, hsecR] at hodd1
      exact (hdotZ_iff u v).mp hodd1
    have hsub : Finset.univ.filter (fun p : VecZ (D * D) × VecZ (D * D) => dotZ (D * D) p.1 p.2 = 1) ⊆
        (Finset.univ : Finset (Fin count)).biUnion (fun i => U i ×ˢ W i) := by
      rintro ⟨u, v⟩ hp
      have h1 : dotZ (D * D) u v = 1 := (Finset.mem_filter.mp hp).2
      have hd : dot (fromZ u) (fromZ v) = true := (hdotZ_iff u v).mpr h1
      have hodd1 : oddCount (secL u) (secR v) = true := by rw [hodd, hsecL, hsecR]; exact hd
      rcases (hcov (secL u) (secR v)).mp hodd1 with ⟨i, hiA, hiB⟩
      rw [Finset.mem_biUnion]
      refine ⟨i, Finset.mem_univ i, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hiA⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hiB⟩
    have hcard_le : (2 ^ (D * D) - 1) * 2 ^ (D * D - 1) ≤ count * 2 ^ (D * D - 1) := by
      calc (2 ^ (D * D) - 1) * 2 ^ (D * D - 1)
          = (Finset.univ.filter (fun p : VecZ (D * D) × VecZ (D * D) => dotZ (D * D) p.1 p.2 = 1)).card :=
            (card_dotZ_ones (D * D) hm_pos).symm
        _ ≤ ((Finset.univ : Finset (Fin count)).biUnion (fun i => U i ×ˢ W i)).card :=
            Finset.card_le_card hsub
        _ ≤ ∑ i : Fin count, (U i ×ˢ W i).card := Finset.card_biUnion_le
        _ = ∑ i : Fin count, (U i).card * (W i).card := by
            apply Finset.sum_congr rfl; intro i _; exact Finset.card_product _ _
        _ ≤ ∑ _ : Fin count, 2 ^ (D * D - 1) := Finset.sum_le_sum (fun i _ => hrect i)
        _ = count * 2 ^ (D * D - 1) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hpos2 : 0 < 2 ^ (D * D - 1) := Nat.pos_of_ne_zero (by positivity)
    exact Nat.le_of_mul_le_mul_right hcard_le hpos2
  · intro hcnt
    let nz : Finset Vector := (Finset.univ : Finset Vector).erase (fun _ => false)
    have hnz_card : Fintype.card { u : Vector // u ∈ nz } = 2 ^ (D * D) - 1 := by
      rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      simp [Vector]
    let eNz : { u : Vector // u ∈ nz } ≃ Fin (2 ^ (D * D) - 1) := Fintype.equivFinOfCardEq hnz_card
    let A : Fin count → (Raw leftLen → Bool) → Prop := fun i P =>
      ∃ h : i.val < 2 ^ (D * D) - 1, first P = (eNz.symm ⟨i.val, h⟩).1
    let B : Fin count → (Raw rightLen → Bool) → Prop := fun i Q =>
      ∃ h : i.val < 2 ^ (D * D) - 1, dot (eNz.symm ⟨i.val, h⟩).1 (last Q) = true
    refine ⟨A, B, ?_⟩
    intro P Q
    rw [hodd P Q]
    constructor
    · intro hd
      have hne : first P ≠ (fun _ => false) := by
        intro hz
        rw [hz] at hd
        dsimp only [dot] at hd
        have hemp : Finset.univ.filter (fun coord : Fin (D * D) => false = true ∧ last Q coord = true) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro c _; simp
        rw [hemp, Finset.card_empty] at hd
        exact absurd hd (by decide)
      have hmem : first P ∈ nz := Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩
      let idx := eNz ⟨first P, hmem⟩
      refine ⟨⟨idx.val, by omega⟩, ⟨idx.isLt, ?_⟩, ⟨idx.isLt, ?_⟩⟩
      · have heq : (eNz.symm ⟨idx.val, idx.isLt⟩).1 = first P := by
          have : (⟨idx.val, idx.isLt⟩ : Fin (2 ^ (D * D) - 1)) = idx := Fin.ext rfl
          rw [this, Equiv.symm_apply_apply]
        exact heq.symm
      · have heq : (eNz.symm ⟨idx.val, idx.isLt⟩).1 = first P := by
          have : (⟨idx.val, idx.isLt⟩ : Fin (2 ^ (D * D) - 1)) = idx := Fin.ext rfl
          rw [this, Equiv.symm_apply_apply]
        rw [heq]; exact hd
    · rintro ⟨i, ⟨h1, hP⟩, ⟨h2, hQ⟩⟩
      rw [hP]
      exact hQ
