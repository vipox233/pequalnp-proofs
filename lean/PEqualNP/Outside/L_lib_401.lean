import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_401_aux

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

end PEqualNP.Outside.L_lib_401_aux

theorem PEqualNP.Outside.L_lib_401 : (∀ d : ℕ,
  let w := d + 1
  let D := 2 ^ w
  let L := (12 * w * D * (D + 2) + 1) * w
  let State := Fin w → Bool
  let loc := fun k : ℕ => (⟨k % (L + w), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩ : Fin (L + w))
  ∀ target : State → State → Bool,
    ∃ table : Fin L → (Fin (w + 1) → Bool) → Bool,
      ∀ first last : State,
        let accepts := fun word : Fin (L + w) → Bool =>
          (∀ j : Fin w, word (loc j.val) = first j ∧ word (loc (L + j.val)) = last j) ∧
          ∀ i : Fin L, table i (fun offset => word (loc (i.val + offset.val))) = true
        (Finset.univ.filter accepts).card.testBit 0 = target first last) := by
  intro d w D L State loc target
  open PEqualNP.Outside.L_lib_401_aux in
  have hD_pos : 1 ≤ D := Nat.one_le_pow w 2 (by omega)
  have hcard : Fintype.card State = D := by
    simp [State, D, Fintype.card_bool, Fintype.card_fin]
  let e : State ≃ Fin D := Fintype.equivFinOfCardEq hcard
  let T : Mat State := fun x y => if target x y = true then 1 else 0
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
  let tables : List (StepTable d) := allSweeps.flatten
  have htables_len : tables.length = L := by
    dsimp only [tables]
    rw [flatten_length_const w allSweeps hall_len, hall_cnt]
  have hpad_mat : matProd ((List.replicate pad (idSweep d)).flatten.map (stepMat d)) = matId := by
    rw [List.map_flatten, matProd_flatten, List.map_map]
    have hmap : (List.replicate pad (idSweep d)).map (matProd ∘ List.map (stepMat d)) =
        List.replicate pad (matId : Mat State) := by
      rw [List.map_replicate]
      congr 1
      exact idSweep_mat d
    rw [hmap, matProd_replicate_id]
  have htables_mat : matProd (tables.map (stepMat d)) = T := by
    dsimp only [tables, allSweeps, S_core]
    simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.map_append, matProd_append, hswP_mat, diagSweep_mat, hswQ_mat, hpad_mat, matMul_id_right]
    exact hT.symm
  let table : Fin L → (Fin (w + 1) → Bool) → Bool :=
    fun i => tables[i.val]'(by omega)
  refine ⟨table, ?_⟩
  intro first last
  apply zmod2_testBit0
  have hcast_eq :
      (Finset.univ.filter (fun word : Fin (L + w) → Bool =>
          (∀ j : Fin w, word (loc j.val) = first j ∧ word (loc (L + j.val)) = last j) ∧
          ∀ i : Fin L, table i (fun offset => word (loc (i.val + offset.val))) = true)).card =
      (Finset.univ.filter (acceptsList d tables first last)).card := by
    let eIdx : Fin (L + w) ≃ Fin (tables.length + w) := Fin.castOrderIso (by rw [htables_len]) |>.toEquiv
    apply Finset.card_bij (fun word _ => fun k => word (eIdx.symm k))
    · intro word hword
      have hacc := (Finset.mem_filter.mp hword).2
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro j
        dsimp only
        have hj := hacc.1 j
        have hloc1 : loc j.val = eIdx.symm ⟨j.val, by omega⟩ := by
          apply Fin.ext; simp [loc, eIdx, Nat.mod_eq_of_lt (by have := j.isLt; omega : j.val < L + w)]
        have hloc2 : loc (L + j.val) = eIdx.symm ⟨tables.length + j.val, by omega⟩ := by
          apply Fin.ext; simp [loc, eIdx, htables_len, Nat.mod_eq_of_lt (by have := j.isLt; omega : L + j.val < L + w)]
        rw [← hloc1, ← hloc2]
        exact hj
      · intro i
        have hi := hacc.2 ⟨i.val, by omega⟩
        dsimp only [table] at hi
        convert hi using 2
        funext off
        dsimp only
        congr 1
        apply Fin.ext
        have hlt : i.val + off.val < L + w := by have := i.isLt; have := off.isLt; omega
        simp [loc, eIdx, Nat.mod_eq_of_lt hlt]
    · intro w1 _ w2 _ heq
      funext k
      have h := congrFun heq (eIdx k)
      simpa using h
    · intro w' hw'
      have hacc' := (Finset.mem_filter.mp hw').2
      refine ⟨fun k => w' (eIdx k), ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · intro j
          dsimp only
          have hj := hacc'.1 j
          have h1 : eIdx (loc j.val) = ⟨j.val, by omega⟩ := by
            apply Fin.ext; simp [loc, eIdx, Nat.mod_eq_of_lt (by have := j.isLt; omega : j.val < L + w)]
          have h2 : eIdx (loc (L + j.val)) = ⟨tables.length + j.val, by omega⟩ := by
            apply Fin.ext; simp [loc, eIdx, htables_len, Nat.mod_eq_of_lt (by have := j.isLt; omega : L + j.val < L + w)]
          rw [h1, h2]
          exact hj
        · intro i
          have hi := hacc'.2 ⟨i.val, by omega⟩
          dsimp only [table]
          convert hi using 2
          funext off
          dsimp only
          congr 1
          apply Fin.ext
          have hlt : i.val + off.val < L + w := by have := i.isLt; have := off.isLt; omega
          simp [loc, eIdx, Nat.mod_eq_of_lt hlt]
      · funext k
        dsimp only
        exact congrArg w' (eIdx.apply_symm_apply k)
  rw [hcast_eq, card_acceptsList_zmod2 d tables first last, htables_mat]
