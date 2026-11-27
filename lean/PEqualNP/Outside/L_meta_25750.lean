import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25750_aux

abbrev B := ZMod 2

def signZ (t : B) : ℤ := if t = 0 then 1 else -1

lemma signZ_zero : signZ 0 = 1 := rfl

lemma signZ_one : signZ 1 = -1 := by decide

lemma signZ_add (a b : B) : signZ (a + b) = signZ a * signZ b := by
  fin_cases a <;> fin_cases b <;> decide

lemma signZ_sum {α : Type*} [DecidableEq α] (s : Finset α) (f : α → B) :
    signZ (∑ i ∈ s, f i) = ∏ i ∈ s, signZ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [signZ_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, signZ_add, ih]

lemma z2_add_self (x : B) : x + x = 0 := by
  fin_cases x <;> decide

lemma z2_eq_zero_or_one (x : B) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

def mixFn {k : ℕ} (d : ℕ) (x : ZMod k → B) (i : ZMod k) : B :=
  x (i - (d : ZMod k)) + x i + x (i + (d : ZMod k))

def nlFn {k : ℕ} (y : ZMod k → B) (j : ZMod k) : B :=
  y j + (1 + y (j + 1)) * y (j + 2)

def transferMat {k : ℕ} (u b : ZMod k → B) (j : ℕ) : Matrix B B ℤ :=
  let i : ZMod k := (j : ZMod k)
  fun left right => signZ ((u i + b i + b (i - 2)) * left + b (i - 1) * left * right)

lemma mixFn_zero {k : ℕ} (d : ℕ) : mixFn (k := k) d 0 = 0 := by
  funext i
  simp [mixFn]

lemma mixFn_add {k : ℕ} (d : ℕ) (x y : ZMod k → B) :
    mixFn d (x + y) = mixFn d x + mixFn d y := by
  funext i
  simp only [mixFn, Pi.add_apply]
  ring

lemma dotProduct_add_left {α : Type*} [Fintype α] (u v w : α → B) :
    dotProduct (u + v) w = dotProduct u w + dotProduct v w := by
  simp only [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dotProduct_add_right {α : Type*} [Fintype α] (u v w : α → B) :
    dotProduct u (v + w) = dotProduct u v + dotProduct u w := by
  simp only [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dotProduct_zero_left {α : Type*} [Fintype α] (w : α → B) :
    dotProduct (0 : α → B) w = 0 := by
  simp [dotProduct]

lemma dotProduct_mixFn {k : ℕ} [NeZero k] (d : ℕ) (u x : ZMod k → B) :
    dotProduct u (mixFn d x) = dotProduct (mixFn d u) x := by
  simp only [dotProduct, mixFn, mul_add, add_mul, Finset.sum_add_distrib]
  have h1 : (∑ i : ZMod k, u i * x (i - (d : ZMod k))) =
      ∑ i : ZMod k, u (i + (d : ZMod k)) * x i := by
    refine Equiv.sum_comp (Equiv.addRight (d : ZMod k)) (fun i => u i * x (i - (d : ZMod k))) |>.symm.trans ?_
    apply Finset.sum_congr rfl
    intro i _
    simp
  have h2 : (∑ i : ZMod k, u i * x (i + (d : ZMod k))) =
      ∑ i : ZMod k, u (i - (d : ZMod k)) * x i := by
    refine Equiv.sum_comp (Equiv.addRight (-(d : ZMod k))) (fun i => u i * x (i + (d : ZMod k))) |>.symm.trans ?_
    apply Finset.sum_congr rfl
    intro i _
    simp [sub_eq_add_neg]
  rw [h1, h2]
  ring

lemma sum_signZ_dotProduct {k : ℕ} [NeZero k] (v : ZMod k → B) :
    (∑ y : ZMod k → B, signZ (dotProduct v y)) =
      if v = 0 then (Fintype.card (ZMod k → B) : ℤ) else 0 := by
  by_cases hv : v = 0
  · subst hv
    simp [signZ_zero]
  · simp only [hv, ↓reduceIte]
    have hex : ∃ i0 : ZMod k, v i0 ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hv (funext hall)
    obtain ⟨i0, hi0⟩ := hex
    have hi0_one : v i0 = 1 := by
      rcases z2_eq_zero_or_one (v i0) with h0 | h1
      · exact absurd h0 hi0
      · exact h1
    let flip : (ZMod k → B) ≃ (ZMod k → B) :=
      Equiv.addRight (Pi.single i0 (1 : B))
    have hflip_dot : ∀ y : ZMod k → B,
        dotProduct v (flip y) = dotProduct v y + 1 := by
      intro y
      change dotProduct v (y + Pi.single i0 (1 : B)) = dotProduct v y + 1
      rw [dotProduct_add_right]
      have hsingle : dotProduct v (Pi.single i0 (1 : B)) = 1 := by
        simp [dotProduct, Pi.single_apply, hi0_one]
      rw [hsingle]
    have hS : (∑ y : ZMod k → B, signZ (dotProduct v y)) =
        -(∑ y : ZMod k → B, signZ (dotProduct v y)) := by
      calc
        ∑ y : ZMod k → B, signZ (dotProduct v y)
          = ∑ y : ZMod k → B, signZ (dotProduct v (flip y)) :=
            (Equiv.sum_comp flip (fun y => signZ (dotProduct v y))).symm
        _ = ∑ y : ZMod k → B, (-signZ (dotProduct v y)) := by
            apply Finset.sum_congr rfl
            intro y _
            rw [hflip_dot y, signZ_add, signZ_one]
            ring
        _ = -(∑ y : ZMod k → B, signZ (dotProduct v y)) := by rw [Finset.sum_neg_distrib]
    omega

lemma list_prod_transfer_entry (M : ℕ → Matrix B B ℤ) :
    ∀ (m : ℕ) (s t : B),
      (((List.range m).map M).prod) s t =
        ∑ w : Fin (m + 1) → B,
          if w 0 = s ∧ w (Fin.last m) = t then
            ∏ j : Fin m, M j.val (w j.castSucc) (w j.succ)
          else 0 := by
  intro m
  induction m with
  | zero =>
    intro s t
    simp only [List.range_zero, List.map_nil, List.prod_nil, Matrix.one_apply,
      Finset.univ_eq_empty, Finset.prod_empty, Fin.last_zero]
    have h1 : (∑ w : Fin 1 → B, if w 0 = s ∧ w 0 = t then (1 : ℤ) else 0) =
        ∑ b : B, if b = s ∧ b = t then (1 : ℤ) else 0 := by
      let e : (Fin 1 → B) ≃ B :=
        { toFun := fun w => w 0
          invFun := fun b _ => b
          left_inv := fun w => by funext i; fin_cases i; rfl
          right_inv := fun _ => rfl }
      exact Equiv.sum_comp e (fun b => if b = s ∧ b = t then (1 : ℤ) else 0)
    rw [h1]
    fin_cases s <;> fin_cases t <;> decide
  | succ m ih =>
    intro s t
    rw [List.range_succ, List.map_append, List.map_singleton, List.prod_append,
      List.prod_singleton, Matrix.mul_apply]
    have hstep : ∀ u : B,
        (((List.range m).map M).prod) s u * M m u t =
          ∑ w : Fin (m + 1) → B,
            if w 0 = s ∧ w (Fin.last m) = u then
              (∏ j : Fin m, M j.val (w j.castSucc) (w j.succ)) * M m u t
            else 0 := by
      intro u
      rw [ih s u, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w _
      split_ifs <;> simp
    simp_rw [hstep]
    let e : (Fin (m + 2) → B) ≃ (Fin (m + 1) → B) × B :=
      { toFun := fun w => (fun i => w i.castSucc, w (Fin.last (m + 1)))
        invFun := fun p => Fin.snoc p.1 p.2
        left_inv := fun w => by
          funext i
          refine Fin.lastCases ?_ ?_ i
          · simp [Fin.snoc_last]
          · intro j; simp [Fin.snoc_castSucc]
        right_inv := fun p => by
          ext i
          · simp [Fin.snoc_castSucc]
          · simp [Fin.snoc_last] }
    have hprod_split : ∀ w : Fin (m + 2) → B,
        (∏ j : Fin (m + 1), M j.val (w j.castSucc) (w j.succ)) =
          (∏ j : Fin m, M j.val (w j.castSucc.castSucc) (w j.succ.castSucc)) *
            M m (w (Fin.last m).castSucc) (w (Fin.last (m + 1))) := by
      intro w
      rw [Fin.prod_univ_castSucc]
      rfl
    have hlast_eq : ∀ w : Fin (m + 2) → B,
        w (Fin.last m).castSucc = (e w).1 (Fin.last m) := fun _ => rfl
    have hzero_eq : ∀ w : Fin (m + 2) → B,
        w 0 = (e w).1 0 := fun _ => rfl
    have hsum_eq :
        (∑ u : B, ∑ w : Fin (m + 1) → B,
          if w 0 = s ∧ w (Fin.last m) = u then
            (∏ j : Fin m, M j.val (w j.castSucc) (w j.succ)) * M m u t
          else 0) =
        ∑ p : (Fin (m + 1) → B) × B,
          if p.1 0 = s ∧ p.2 = t then
            (∏ j : Fin m, M j.val (p.1 j.castSucc) (p.1 j.succ)) * M m (p.1 (Fin.last m)) p.2
          else 0 := by
      rw [Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      have hL : (∑ u : B, if w 0 = s ∧ w (Fin.last m) = u then
          (∏ j : Fin m, M j.val (w j.castSucc) (w j.succ)) * M m u t else 0) =
          if w 0 = s then
            (∏ j : Fin m, M j.val (w j.castSucc) (w j.succ)) * M m (w (Fin.last m)) t
          else 0 := by
        by_cases h0 : w 0 = s
        · simp only [h0, true_and, ↓reduceIte]
          rw [Finset.sum_ite_eq Finset.univ (w (Fin.last m))
            (fun u => (∏ j : Fin m, M j.val (w j.castSucc) (w j.succ)) * M m u t)]
          simp
        · simp [h0]
      have hR : (∑ v : B, if w 0 = s ∧ v = t then
          (∏ j : Fin m, M j.val (w j.castSucc) (w j.succ)) * M m (w (Fin.last m)) v else 0) =
          if w 0 = s then
            (∏ j : Fin m, M j.val (w j.castSucc) (w j.succ)) * M m (w (Fin.last m)) t
          else 0 := by
        by_cases h0 : w 0 = s
        · simp only [h0, true_and, ↓reduceIte]
          rw [Finset.sum_ite_eq' Finset.univ t]
          simp
        · simp [h0]
      rw [hL, hR]
    rw [hsum_eq]
    refine (Equiv.sum_comp e (fun p : (Fin (m + 1) → B) × B =>
      if p.1 0 = s ∧ p.2 = t then
        (∏ j : Fin m, M j.val (p.1 j.castSucc) (p.1 j.succ)) * M m (p.1 (Fin.last m)) p.2
      else 0)).symm.trans ?_
    apply Finset.sum_congr rfl
    intro w _
    rw [hprod_split w]
    rfl

noncomputable def finToZMod (k : ℕ) [NeZero k] : Fin k ≃ ZMod k :=
  let f : Fin k → ZMod k := fun j => (j.val : ZMod k)
  have hinj : Function.Injective f := by
    intro a b hab
    have hval : a.val % k = b.val % k := by
      have h1 := congrArg ZMod.val hab
      simpa [f, ZMod.val_natCast] using h1
    rw [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] at hval
    exact Fin.ext hval
  have hcard : Fintype.card (Fin k) = Fintype.card (ZMod k) := by
    rw [Fintype.card_fin, ZMod.card]
  Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩)

lemma trace_list_prod_transfer {k : ℕ} [NeZero k] (M : ℕ → Matrix B B ℤ) :
    Matrix.trace (((List.range k).map M).prod) =
      ∑ y : ZMod k → B, ∏ j : Fin k, M j.val (y (j.val : ZMod k)) (y ((j.val : ZMod k) + 1)) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  have hentry : ∀ s : B,
      (((List.range k).map M).prod) s s =
        ∑ w : Fin (k + 1) → B,
          if w 0 = s ∧ w (Fin.last k) = s then
            ∏ j : Fin k, M j.val (w j.castSucc) (w j.succ)
          else 0 := fun s => list_prod_transfer_entry M k s s
  simp_rw [hentry]
  rw [Finset.sum_comm]
  have hcollapse : ∀ w : Fin (k + 1) → B,
      (∑ s : B, if w 0 = s ∧ w (Fin.last k) = s then
        ∏ j : Fin k, M j.val (w j.castSucc) (w j.succ) else 0) =
      if w 0 = w (Fin.last k) then
        ∏ j : Fin k, M j.val (w j.castSucc) (w j.succ)
      else 0 := by
    intro w
    by_cases heq : w 0 = w (Fin.last k)
    · rw [if_pos heq]
      have h1 : ∀ s : B, (w 0 = s ∧ w (Fin.last k) = s) ↔ w 0 = s := by
        intro s; rw [← heq]; simp
      simp_rw [h1]
      rw [Finset.sum_ite_eq Finset.univ (w 0)
        (fun _ => ∏ j : Fin k, M j.val (w j.castSucc) (w j.succ))]
      simp
    · rw [if_neg heq]
      apply Finset.sum_eq_zero
      intro s _
      split_ifs with h
      · exact absurd (h.1.trans h.2.symm) heq
      · rfl
  simp_rw [hcollapse]
  rw [← Finset.sum_filter]
  let S := Finset.univ.filter (fun w : Fin (k + 1) → B => w 0 = w (Fin.last k))
  let toW : (ZMod k → B) → (Fin (k + 1) → B) := fun y j => y (j.val : ZMod k)
  symm
  refine Finset.sum_bij (fun y _ => toW y) ?_ ?_ ?_ ?_
  · intro y _
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simp [toW]
  · intro y1 _ y2 _ hEq
    funext i
    let j : Fin k := (finToZMod k).symm i
    have hj : (j.val : ZMod k) = i := (finToZMod k).apply_symm_apply i
    have hval := congrFun hEq j.castSucc
    simpa [toW, hj] using hval
  · intro w hw
    have hwEq : w 0 = w (Fin.last k) := (Finset.mem_filter.mp hw).2
    let y : ZMod k → B := fun i => w ((finToZMod k).symm i).castSucc
    refine ⟨y, Finset.mem_univ y, ?_⟩
    funext j
    refine Fin.lastCases ?_ ?_ j
    · simp only [toW, y, Fin.val_last, ZMod.natCast_self]
      have h0 : (finToZMod k).symm 0 = ⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩ := by
        apply (finToZMod k).injective
        rw [(finToZMod k).apply_symm_apply]
        simp [finToZMod]
      rw [h0]
      exact hwEq
    · intro j'
      simp only [toW, y, Fin.val_castSucc]
      have hj' : (finToZMod k).symm (j'.val : ZMod k) = j' := by
        apply (finToZMod k).injective
        rw [(finToZMod k).apply_symm_apply]
        rfl
      rw [hj']
  · intro y _
    apply Finset.prod_congr rfl
    intro j _
    simp [toW, Nat.cast_add]

lemma trace_transfer_eq_walsh {k : ℕ} [NeZero k] (u b : ZMod k → B) :
    Matrix.trace (((List.range k).map (transferMat u b)).prod) =
      ∑ y : ZMod k → B, signZ (dotProduct u y + dotProduct b (nlFn y)) := by
  rw [trace_list_prod_transfer (transferMat u b)]
  apply Finset.sum_congr rfl
  intro y _
  simp only [transferMat]
  rw [← signZ_sum]
  congr 1
  have hreidx : (∑ j : Fin k,
      ((u (j.val : ZMod k) + b (j.val : ZMod k) + b ((j.val : ZMod k) - 2)) * y (j.val : ZMod k) +
       b ((j.val : ZMod k) - 1) * y (j.val : ZMod k) * y ((j.val : ZMod k) + 1))) =
      ∑ i : ZMod k,
        ((u i + b i + b (i - 2)) * y i + b (i - 1) * y i * y (i + 1)) :=
    Equiv.sum_comp (finToZMod k) (fun i : ZMod k =>
      (u i + b i + b (i - 2)) * y i + b (i - 1) * y i * y (i + 1))
  rw [hreidx]
  have h1 : (∑ i : ZMod k, b (i - 2) * y i) = ∑ j : ZMod k, b j * y (j + 2) := by
    refine (Equiv.sum_comp (Equiv.addRight (2 : ZMod k)) (fun i => b (i - 2) * y i)).symm.trans ?_
    apply Finset.sum_congr rfl
    intro j _
    simp
  have h2 : (∑ i : ZMod k, b (i - 1) * y i * y (i + 1)) =
      ∑ j : ZMod k, b j * (y (j + 1) * y (j + 2)) := by
    refine (Equiv.sum_comp (Equiv.addRight (1 : ZMod k))
      (fun i => b (i - 1) * y i * y (i + 1))).symm.trans ?_
    apply Finset.sum_congr rfl
    intro j _
    have h11 : j + 1 + 1 = j + (2 : ZMod k) := by ring
    simp [mul_assoc, h11]
  have hsplit : (∑ i : ZMod k, ((u i + b i + b (i - 2)) * y i + b (i - 1) * y i * y (i + 1))) =
      (∑ i : ZMod k, u i * y i) + (∑ i : ZMod k, b i * y i) +
      (∑ i : ZMod k, b (i - 2) * y i) + (∑ i : ZMod k, b (i - 1) * y i * y (i + 1)) := by
    simp only [add_mul, Finset.sum_add_distrib]
  rw [hsplit, h1, h2]
  simp only [dotProduct, nlFn, mul_add, add_mul, Finset.sum_add_distrib]
  ring

lemma card_lifts_of_mem {k : ℕ} [NeZero k] (d : ℕ) (a : ZMod k → B)
    (y0 : ZMod k → B) (hy0 : mixFn d y0 = a) :
    (Finset.univ.filter (fun u : ZMod k → B => mixFn d u = a)).card =
      (Finset.univ.filter (fun v : ZMod k → B => mixFn d v = 0)).card := by
  symm
  refine Finset.card_bij (fun v _ => v + y0) ?_ ?_ ?_
  · intro v hv
    have hv0 : mixFn d v = 0 := (Finset.mem_filter.mp hv).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [mixFn_add, hv0, hy0, zero_add]
  · intro v1 _ v2 _ hEq
    exact add_right_cancel hEq
  · intro u hu
    have hua : mixFn d u = a := (Finset.mem_filter.mp hu).2
    refine ⟨u + y0, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [mixFn_add, hua, hy0]
      funext i
      exact z2_add_self (a i)
    · funext i
      simp only [Pi.add_apply]
      rw [add_assoc, z2_add_self, add_zero]

lemma img_eq_kerPerp {k : ℕ} [NeZero k] (d : ℕ) :
    let kerMix := Finset.univ.filter (fun v : ZMod k → B => mixFn d v = 0)
    let imgMix := Finset.univ.image (mixFn (k := k) d)
    let kerPerp := Finset.univ.filter (fun y : ZMod k → B => ∀ v ∈ kerMix, dotProduct v y = 0)
    imgMix = kerPerp := by
  intro kerMix imgMix kerPerp
  have hsub : imgMix ⊆ kerPerp := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, _, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro v hv
    have hv0 : mixFn d v = 0 := (Finset.mem_filter.mp hv).2
    rw [dotProduct_mixFn, hv0, dotProduct_zero_left]
  have hker_pos : 0 < kerMix.card := by
    apply Finset.card_pos.mpr
    exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, mixFn_zero d⟩⟩
  have himg_card : imgMix.card * kerMix.card = Fintype.card (ZMod k → B) := by
    have hpart : (Finset.univ : Finset (ZMod k → B)).card =
        ∑ y ∈ imgMix, (Finset.univ.filter (fun x : ZMod k → B => mixFn d x = y)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext x
        simp [imgMix]
      · intro y1 _ y2 _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro x h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hconst : ∀ y ∈ imgMix,
        (Finset.univ.filter (fun x : ZMod k → B => mixFn d x = y)).card = kerMix.card := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨x0, _, hx0⟩
      exact card_lifts_of_mem d y x0 hx0
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul] at hpart
    rw [Finset.card_univ] at hpart
    exact hpart.symm
  have hperp_card : kerPerp.card * kerMix.card = Fintype.card (ZMod k → B) := by
    have hdouble : (∑ y : ZMod k → B, ∑ v ∈ kerMix, signZ (dotProduct v y)) =
        (Fintype.card (ZMod k → B) : ℤ) := by
      rw [Finset.sum_comm]
      have hinner : ∀ v ∈ kerMix,
          (∑ y : ZMod k → B, signZ (dotProduct v y)) =
            if v = 0 then (Fintype.card (ZMod k → B) : ℤ) else 0 :=
        fun v _ => sum_signZ_dotProduct v
      rw [Finset.sum_congr rfl hinner]
      have h0mem : (0 : ZMod k → B) ∈ kerMix :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, mixFn_zero d⟩
      rw [Finset.sum_ite_eq' kerMix (0 : ZMod k → B)]
      simp [h0mem]
    have hker_sum : ∀ y : ZMod k → B,
        (∑ v ∈ kerMix, signZ (dotProduct v y)) =
          if y ∈ kerPerp then (kerMix.card : ℤ) else 0 := by
      intro y
      by_cases hy : y ∈ kerPerp
      · rw [if_pos hy]
        have hall : ∀ v ∈ kerMix, signZ (dotProduct v y) = 1 := by
          intro v hv
          rw [(Finset.mem_filter.mp hy).2 v hv, signZ_zero]
        rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, mul_one]
      · rw [if_neg hy]
        have hex : ∃ v0 ∈ kerMix, dotProduct v0 y ≠ 0 := by
          by_contra hall
          push Not at hall
          exact hy (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩)
        obtain ⟨v0, hv0, hdot0⟩ := hex
        have hdot1 : dotProduct v0 y = 1 := by
          rcases z2_eq_zero_or_one (dotProduct v0 y) with h0 | h1
          · exact absurd h0 hdot0
          · exact h1
        have hS : (∑ v ∈ kerMix, signZ (dotProduct v y)) =
            -(∑ v ∈ kerMix, signZ (dotProduct v y)) := by
          have hbij : (∑ v ∈ kerMix, signZ (dotProduct v y)) =
              ∑ v ∈ kerMix, signZ (dotProduct (v + v0) y) := by
            symm
            refine Finset.sum_bij (fun v _ => v + v0) ?_ ?_ ?_ ?_
            · intro v hv
              apply Finset.mem_filter.mpr
              refine ⟨Finset.mem_univ _, ?_⟩
              rw [mixFn_add, (Finset.mem_filter.mp hv).2, (Finset.mem_filter.mp hv0).2, add_zero]
            · intro v1 _ v2 _ hEq
              exact add_right_cancel hEq
            · intro v hv
              refine ⟨v + v0, ?_, ?_⟩
              · apply Finset.mem_filter.mpr
                refine ⟨Finset.mem_univ _, ?_⟩
                rw [mixFn_add, (Finset.mem_filter.mp hv).2, (Finset.mem_filter.mp hv0).2, add_zero]
              · funext i; simp only [Pi.add_apply]; rw [add_assoc, z2_add_self, add_zero]
            · intro v _; rfl
          calc
            ∑ v ∈ kerMix, signZ (dotProduct v y)
              = ∑ v ∈ kerMix, signZ (dotProduct (v + v0) y) := hbij
            _ = ∑ v ∈ kerMix, (-signZ (dotProduct v y)) := by
                apply Finset.sum_congr rfl
                intro v _
                rw [dotProduct_add_left, hdot1, signZ_add, signZ_one]
                ring
            _ = -(∑ v ∈ kerMix, signZ (dotProduct v y)) := by rw [Finset.sum_neg_distrib]
        omega
    simp_rw [hker_sum] at hdouble
    rw [← Finset.sum_filter] at hdouble
    have hf : Finset.univ.filter (fun y : ZMod k → B => y ∈ kerPerp) = kerPerp := by
      ext y; simp
    rw [hf, Finset.sum_const, nsmul_eq_mul] at hdouble
    exact Int.ofNat.inj (by simpa [Nat.cast_mul] using hdouble)
  have hcard_eq : kerPerp.card = imgMix.card :=
    Nat.eq_of_mul_eq_mul_right hker_pos (hperp_card.trans himg_card.symm)
  exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_eq)

lemma walsh_transfer_identity {k : ℕ} [NeZero k] (d : ℕ) (a b : ZMod k → B) :
    (∑ x : ZMod k → B, signZ (dotProduct a x + dotProduct b (nlFn (mixFn d x)))) =
      ∑ u ∈ Finset.univ.filter (fun u : ZMod k → B => mixFn d u = a),
        Matrix.trace (((List.range k).map (transferMat u b)).prod) := by
  let kerMix := Finset.univ.filter (fun v : ZMod k → B => mixFn d v = 0)
  let imgMix := Finset.univ.image (mixFn (k := k) d)
  let kerPerp := Finset.univ.filter (fun y : ZMod k → B => ∀ v ∈ kerMix, dotProduct v y = 0)
  have heq_img : imgMix = kerPerp := img_eq_kerPerp d
  have htr : ∀ u ∈ Finset.univ.filter (fun u : ZMod k → B => mixFn d u = a),
      Matrix.trace (((List.range k).map (transferMat u b)).prod) =
        ∑ y : ZMod k → B, signZ (dotProduct u y + dotProduct b (nlFn y)) :=
    fun u _ => trace_transfer_eq_walsh u b
  rw [Finset.sum_congr rfl htr]
  by_cases ha : a ∈ imgMix
  · rcases Finset.mem_image.mp ha with ⟨u0, _, hu0⟩
    rw [Finset.sum_comm]
    have hinner : ∀ y : ZMod k → B,
        (∑ u ∈ Finset.univ.filter (fun u : ZMod k → B => mixFn d u = a),
          signZ (dotProduct u y + dotProduct b (nlFn y))) =
        if y ∈ imgMix then
          (kerMix.card : ℤ) * signZ (dotProduct u0 y + dotProduct b (nlFn y))
        else 0 := by
      intro y
      have hshift :
          (∑ u ∈ Finset.univ.filter (fun u : ZMod k → B => mixFn d u = a),
            signZ (dotProduct u y + dotProduct b (nlFn y))) =
          signZ (dotProduct u0 y + dotProduct b (nlFn y)) *
            ∑ v ∈ kerMix, signZ (dotProduct v y) := by
        rw [Finset.mul_sum]
        symm
        refine Finset.sum_bij (fun v _ => v + u0) ?_ ?_ ?_ ?_
        · intro v hv
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [mixFn_add, (Finset.mem_filter.mp hv).2, hu0, zero_add]
        · intro v1 _ v2 _ hEq
          exact add_right_cancel hEq
        · intro u hu
          refine ⟨u + u0, ?_, ?_⟩
          · apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_univ _, ?_⟩
            rw [mixFn_add, (Finset.mem_filter.mp hu).2, hu0]
            funext i; exact z2_add_self (a i)
          · funext i; simp only [Pi.add_apply]; rw [add_assoc, z2_add_self, add_zero]
        · intro v _
          rw [dotProduct_add_left, ← signZ_add]
          congr 1
          ring
      rw [hshift]
      by_cases hy : y ∈ imgMix
      · rw [if_pos hy]
        have hyP : y ∈ kerPerp := heq_img ▸ hy
        have hall : ∀ v ∈ kerMix, signZ (dotProduct v y) = 1 := by
          intro v hv
          rw [(Finset.mem_filter.mp hyP).2 v hv, signZ_zero]
        rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, mul_one, mul_comm]
      · rw [if_neg hy]
        have hyNP : y ∉ kerPerp := by rw [← heq_img]; exact hy
        have hex : ∃ v0 ∈ kerMix, dotProduct v0 y ≠ 0 := by
          by_contra hall
          push Not at hall
          exact hyNP (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩)
        obtain ⟨v0, hv0, hdot0⟩ := hex
        have hdot1 : dotProduct v0 y = 1 := by
          rcases z2_eq_zero_or_one (dotProduct v0 y) with h0 | h1
          · exact absurd h0 hdot0
          · exact h1
        have hzero : (∑ v ∈ kerMix, signZ (dotProduct v y)) = 0 := by
          have hS : (∑ v ∈ kerMix, signZ (dotProduct v y)) =
              -(∑ v ∈ kerMix, signZ (dotProduct v y)) := by
            have hbij : (∑ v ∈ kerMix, signZ (dotProduct v y)) =
                ∑ v ∈ kerMix, signZ (dotProduct (v + v0) y) := by
              symm
              refine Finset.sum_bij (fun v _ => v + v0) ?_ ?_ ?_ ?_
              · intro v hv
                apply Finset.mem_filter.mpr
                refine ⟨Finset.mem_univ _, ?_⟩
                rw [mixFn_add, (Finset.mem_filter.mp hv).2, (Finset.mem_filter.mp hv0).2, add_zero]
              · intro v1 _ v2 _ hEq
                exact add_right_cancel hEq
              · intro v hv
                refine ⟨v + v0, ?_, ?_⟩
                · apply Finset.mem_filter.mpr
                  refine ⟨Finset.mem_univ _, ?_⟩
                  rw [mixFn_add, (Finset.mem_filter.mp hv).2, (Finset.mem_filter.mp hv0).2, add_zero]
                · funext i; simp only [Pi.add_apply]; rw [add_assoc, z2_add_self, add_zero]
              · intro v _; rfl
            calc
              ∑ v ∈ kerMix, signZ (dotProduct v y)
                = ∑ v ∈ kerMix, signZ (dotProduct (v + v0) y) := hbij
              _ = ∑ v ∈ kerMix, (-signZ (dotProduct v y)) := by
                  apply Finset.sum_congr rfl
                  intro v _
                  rw [dotProduct_add_left, hdot1, signZ_add, signZ_one]
                  ring
              _ = -(∑ v ∈ kerMix, signZ (dotProduct v y)) := by rw [Finset.sum_neg_distrib]
          omega
        rw [hzero, mul_zero]
    simp_rw [hinner]
    rw [← Finset.sum_filter]
    have hf : Finset.univ.filter (fun y : ZMod k → B => y ∈ imgMix) = imgMix := by
      ext y; simp
    rw [hf]
    have hpart : (∑ x : ZMod k → B, signZ (dotProduct a x + dotProduct b (nlFn (mixFn d x)))) =
        ∑ y ∈ imgMix, ∑ x ∈ Finset.univ.filter (fun x : ZMod k → B => mixFn d x = y),
          signZ (dotProduct a x + dotProduct b (nlFn (mixFn d x))) := by
      rw [← Finset.sum_biUnion]
      · congr 1
        ext x; simp [imgMix]
      · intro y1 _ y2 _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro x h1 h2
        exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    rw [hpart]
    apply Finset.sum_congr rfl
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x0, _, hx0⟩
    have hconst : ∀ x ∈ Finset.univ.filter (fun x : ZMod k → B => mixFn d x = y),
        signZ (dotProduct a x + dotProduct b (nlFn (mixFn d x))) =
          signZ (dotProduct u0 y + dotProduct b (nlFn y)) := by
      intro x hx
      have hxy : mixFn d x = y := (Finset.mem_filter.mp hx).2
      rw [hxy, ← hu0, ← dotProduct_mixFn, hxy]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul,
      card_lifts_of_mem d y x0 hx0]
  · have hempty : Finset.univ.filter (fun u : ZMod k → B => mixFn d u = a) = ∅ := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hEq
      exact ha (Finset.mem_image.mpr ⟨u, Finset.mem_univ u, hEq⟩)
    rw [hempty, Finset.sum_empty]
    have haNP : a ∉ kerPerp := by rw [← heq_img]; exact ha
    have hex : ∃ v0 ∈ kerMix, dotProduct v0 a ≠ 0 := by
      by_contra hall
      push Not at hall
      exact haNP (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩)
    obtain ⟨v0, hv0, hdot0⟩ := hex
    have hdot1 : dotProduct a v0 = 1 := by
      have hcomm : dotProduct a v0 = dotProduct v0 a := dotProduct_comm a v0
      rw [hcomm]
      rcases z2_eq_zero_or_one (dotProduct v0 a) with h0 | h1
      · exact absurd h0 hdot0
      · exact h1
    have hv0_mix : mixFn d v0 = 0 := (Finset.mem_filter.mp hv0).2
    let shift : (ZMod k → B) ≃ (ZMod k → B) := Equiv.addRight v0
    have hS : (∑ x : ZMod k → B, signZ (dotProduct a x + dotProduct b (nlFn (mixFn d x)))) =
        -(∑ x : ZMod k → B, signZ (dotProduct a x + dotProduct b (nlFn (mixFn d x)))) := by
      calc
        ∑ x : ZMod k → B, signZ (dotProduct a x + dotProduct b (nlFn (mixFn d x)))
          = ∑ x : ZMod k → B,
              signZ (dotProduct a (shift x) + dotProduct b (nlFn (mixFn d (shift x)))) :=
            (Equiv.sum_comp shift _).symm
        _ = ∑ x : ZMod k → B,
              (-signZ (dotProduct a x + dotProduct b (nlFn (mixFn d x)))) := by
            apply Finset.sum_congr rfl
            intro x _
            have hm : mixFn d (shift x) = mixFn d x := by
              change mixFn d (x + v0) = mixFn d x
              rw [mixFn_add, hv0_mix, add_zero]
            have hd : dotProduct a (shift x) = dotProduct a x + 1 := by
              change dotProduct a (x + v0) = dotProduct a x + 1
              rw [dotProduct_add_right, hdot1]
            rw [hm, hd]
            have hadd : dotProduct a x + 1 + dotProduct b (nlFn (mixFn d x)) =
                (dotProduct a x + dotProduct b (nlFn (mixFn d x))) + 1 := by ring
            rw [hadd, signZ_add, signZ_one]
            ring
        _ = -(∑ x : ZMod k → B, signZ (dotProduct a x + dotProduct b (nlFn (mixFn d x)))) :=
            by rw [Finset.sum_neg_distrib]
    omega

def seq3 (a b : B) (n : ℕ) : B :=
  match n % 3 with
  | 0 => a
  | 1 => b
  | _ => a + b

lemma seq3_step (a b : B) (n : ℕ) :
    seq3 a b n + seq3 a b (n + 1) + seq3 a b (n + 2) = 0 := by
  have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h with h0 | h1 | h2
  · have h1' : (n + 1) % 3 = 1 := by omega
    have h2' : (n + 2) % 3 = 2 := by omega
    simp only [seq3, h0, h1', h2']
    fin_cases a <;> fin_cases b <;> decide
  · have h1' : (n + 1) % 3 = 2 := by omega
    have h2' : (n + 2) % 3 = 0 := by omega
    simp only [seq3, h1, h1', h2']
    fin_cases a <;> fin_cases b <;> decide
  · have h1' : (n + 1) % 3 = 0 := by omega
    have h2' : (n + 2) % 3 = 1 := by omega
    simp only [seq3, h2, h1', h2']
    fin_cases a <;> fin_cases b <;> decide

lemma sol_eq_seq3 {m : ℕ} [NeZero m] (w : ZMod m → B)
    (hw : ∀ t : ZMod m, w (t - 1) + w t + w (t + 1) = 0) :
    ∀ n : ℕ, w (n : ZMod m) = seq3 (w 0) (w 1) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 => simp [seq3]
    | 1 => simp [seq3]
    | n + 2 =>
      have h0 : w (n : ZMod m) = seq3 (w 0) (w 1) n := ih n (by omega)
      have h1 : w ((n + 1 : ℕ) : ZMod m) = seq3 (w 0) (w 1) (n + 1) := ih (n + 1) (by omega)
      have hrec := hw ((n + 1 : ℕ) : ZMod m)
      have hm1 : ((n + 1 : ℕ) : ZMod m) - 1 = (n : ZMod m) := by push_cast; ring
      have hp1 : ((n + 1 : ℕ) : ZMod m) + 1 = ((n + 2 : ℕ) : ZMod m) := by push_cast; ring
      rw [hm1, hp1, h0, h1] at hrec
      have hseq := seq3_step (w 0) (w 1) n
      have hsum : seq3 (w 0) (w 1) n + seq3 (w 0) (w 1) (n + 1) + w ((n + 2 : ℕ) : ZMod m) =
          seq3 (w 0) (w 1) n + seq3 (w 0) (w 1) (n + 1) + seq3 (w 0) (w 1) (n + 2) :=
        hrec.trans hseq.symm
      exact add_left_cancel hsum

lemma card_sol_cycle (m : ℕ) [NeZero m] :
    (Finset.univ.filter (fun w : ZMod m → B =>
      ∀ t : ZMod m, w (t - 1) + w t + w (t + 1) = 0)).card =
      if 3 ∣ m then 4 else 1 := by
  let S := Finset.univ.filter (fun w : ZMod m → B =>
    ∀ t : ZMod m, w (t - 1) + w t + w (t + 1) = 0)
  by_cases h3 : 3 ∣ m
  · rw [if_pos h3]
    have hm_pos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    have hm3 : 3 ≤ m := Nat.le_of_dvd hm_pos h3
    have hmod3 : ∀ n : ℕ, (n % m) % 3 = n % 3 := by
      intro n
      rcases h3 with ⟨q, rfl⟩
      have hdiv : (n % (3 * q)) % 3 = n % 3 := Nat.mod_mod_of_dvd n ⟨q, rfl⟩
      exact hdiv
    have hcard : S.card = Fintype.card (B × B) := by
      symm
      refine Finset.card_bij (fun p _ => fun t : ZMod m => seq3 p.1 p.2 t.val) ?_ ?_ ?_
      · intro p _
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro t
        have hstep : ∀ n : ℕ, seq3 p.1 p.2 (n : ZMod m).val = seq3 p.1 p.2 n := by
          intro n
          simp only [ZMod.val_natCast, seq3, hmod3]
        have ht : t = (t.val : ZMod m) := (ZMod.natCast_zmod_val t).symm
        have hsub : t - 1 = ((t.val + m - 1 : ℕ) : ZMod m) := by
          have hm1 : 1 ≤ t.val + m := by omega
          rw [Nat.cast_sub hm1, Nat.cast_add, ZMod.natCast_self, add_zero, Nat.cast_one, ← ht]
        have hadd : t + 1 = ((t.val + m + 1 : ℕ) : ZMod m) := by
          rw [Nat.cast_add, Nat.cast_add, ZMod.natCast_self, add_zero, Nat.cast_one, ← ht]
        have ht' : t = ((t.val + m : ℕ) : ZMod m) := by
          rw [Nat.cast_add, ZMod.natCast_self, add_zero, ← ht]
        rw [hsub, hadd]
        conv_lhs => arg 1; arg 2; rw [ht']
        dsimp only
        rw [hstep, hstep, hstep]
        have hstep0 := seq3_step p.1 p.2 (t.val + m - 1)
        have h1 : t.val + m - 1 + 1 = t.val + m := by omega
        have h2 : t.val + m - 1 + 2 = t.val + m + 1 := by omega
        rw [h1, h2] at hstep0
        exact hstep0
      · intro p1 _ p2 _ hEq
        have h0 := congrFun hEq 0
        have h1 := congrFun hEq 1
        have hv0 : (0 : ZMod m).val = 0 := ZMod.val_zero
        have hv1 : (1 : ZMod m).val = 1 := by
          rw [← Nat.cast_one, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
        rw [hv0] at h0
        rw [hv1] at h1
        simp only [seq3] at h0 h1
        exact Prod.ext h0 h1
      · intro w hw
        have hrec := (Finset.mem_filter.mp hw).2
        refine ⟨(w 0, w 1), Finset.mem_univ _, ?_⟩
        funext t
        have h1 := sol_eq_seq3 w hrec t.val
        rw [ZMod.natCast_zmod_val] at h1
        exact h1.symm
    rw [hcard]
    decide
  · rw [if_neg h3]
    have huniq : S = {0} := by
      ext w
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hw
        have hseq := sol_eq_seq3 w hw
        have hm0 : seq3 (w 0) (w 1) m = w 0 := by
          have h := hseq m
          rw [ZMod.natCast_self] at h
          exact h.symm
        have hm1 : seq3 (w 0) (w 1) (m + 1) = w 1 := by
          have h := hseq (m + 1)
          have hc : ((m + 1 : ℕ) : ZMod m) = 1 := by
            rw [Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
          rw [hc] at h
          exact h.symm
        have hmod : m % 3 = 1 ∨ m % 3 = 2 := by
          have hne0 : m % 3 ≠ 0 := fun h0 => h3 (Nat.dvd_of_mod_eq_zero h0)
          omega
        have hw01 : w 0 = 0 ∧ w 1 = 0 := by
          rcases hmod with h1 | h2
          · have h1' : (m + 1) % 3 = 2 := by omega
            simp only [seq3, h1, h1'] at hm0 hm1
            rcases z2_eq_zero_or_one (w 0) with ha | ha <;>
              rcases z2_eq_zero_or_one (w 1) with hb | hb <;>
              simp [ha, hb] at hm0 hm1 ⊢
          · have h2' : (m + 1) % 3 = 0 := by omega
            simp only [seq3, h2, h2'] at hm0 hm1
            rcases z2_eq_zero_or_one (w 0) with ha | ha <;>
              rcases z2_eq_zero_or_one (w 1) with hb | hb <;>
              simp [ha, hb] at hm0 hm1 ⊢
        funext t
        have h := hseq t.val
        rw [ZMod.natCast_zmod_val, hw01.1, hw01.2] at h
        rw [h]
        have hzero : ∀ n : ℕ, seq3 0 0 n = 0 := by
          intro n
          have h3c : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
          rcases h3c with c0 | c1 | c2
          · simp [seq3, c0]
          · simp [seq3, c1]
          · simp [seq3, c2]
        exact hzero t.val
      · rintro rfl t
        simp
    change S.card = 1
    rw [huniq, Finset.card_singleton]

lemma card_kerMix {k : ℕ} [NeZero k] (d : ℕ) :
    (Finset.univ.filter (fun v : ZMod k → B => mixFn d v = 0)).card =
      if 3 ∣ (k / Nat.gcd k d) then 4 ^ (Nat.gcd k d) else 1 := by
  let g := Nat.gcd k d
  let m := k / g
  let d' := d / g
  have hk_pos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hg_dvd_k : g ∣ k := Nat.gcd_dvd_left k d
  have hg_dvd_d : g ∣ d := Nat.gcd_dvd_right k d
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left d hk_pos
  have hgm : g * m = k := Nat.mul_div_cancel' hg_dvd_k
  have hgd : g * d' = d := Nat.mul_div_cancel' hg_dvd_d
  have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hk_pos hg_dvd_k) hg_pos
  have : NeZero m := ⟨Nat.ne_of_gt hm_pos⟩
  have hcop : Nat.Coprime m d' := by
    rw [Nat.coprime_iff_gcd_eq_one]
    let c := Nat.gcd m d'
    have hc_pos : 0 < c := Nat.gcd_pos_of_pos_left d' hm_pos
    have hgc_k : g * c ∣ k := by
      rw [← hgm]
      exact Nat.mul_dvd_mul_left g (Nat.gcd_dvd_left m d')
    have hgc_d : g * c ∣ d := by
      rw [← hgd]
      exact Nat.mul_dvd_mul_left g (Nat.gcd_dvd_right m d')
    have hgc_g : g * c ∣ g := Nat.dvd_gcd hgc_k hgc_d
    have hle : g * c ≤ g := Nat.le_of_dvd hg_pos hgc_g
    have hc_le : c ≤ 1 := by
      have : g * c ≤ g * 1 := by simpa using hle
      exact Nat.le_of_mul_le_mul_left this hg_pos
    omega
  let phi : Fin g × ZMod m → ZMod k := fun p => (p.1.val : ZMod k) + ((p.2.val * d : ℕ) : ZMod k)
  have hphi_inj : Function.Injective phi := by
    rintro ⟨r1, t1⟩ ⟨r2, t2⟩ hEq
    have hmod_k : (r1.val + t1.val * d) % k = (r2.val + t2.val * d) % k := by
      have hcast : ((r1.val + t1.val * d : ℕ) : ZMod k) = ((r2.val + t2.val * d : ℕ) : ZMod k) := by
        simpa [phi, Nat.cast_add] using hEq
      have h1 := congrArg ZMod.val hcast
      rw [ZMod.val_natCast, ZMod.val_natCast] at h1
      exact h1
    have hmod_g : (r1.val + t1.val * d) % g = (r2.val + t2.val * d) % g := by
      have h1 := congrArg (· % g) hmod_k
      rwa [Nat.mod_mod_of_dvd _ hg_dvd_k, Nat.mod_mod_of_dvd _ hg_dvd_k] at h1
    have hr1_mod : (r1.val + t1.val * d) % g = r1.val := by
      rw [← hgd, ← mul_assoc, mul_comm t1.val g, mul_assoc, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt r1.isLt]
    have hr2_mod : (r2.val + t2.val * d) % g = r2.val := by
      rw [← hgd, ← mul_assoc, mul_comm t2.val g, mul_assoc, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt r2.isLt]
    rw [hr1_mod, hr2_mod] at hmod_g
    have hrEq : r1 = r2 := Fin.ext hmod_g
    subst hrEq
    have htd : ((t1.val * d : ℕ) : ZMod k) = ((t2.val * d : ℕ) : ZMod k) := by
      exact add_left_cancel hEq
    have htd_mod : (t1.val * d) % k = (t2.val * d) % k := by
      have h1 := congrArg ZMod.val htd
      rw [ZMod.val_natCast, ZMod.val_natCast] at h1
      exact h1
    have hdiv_mod : (t1.val * d') % m = (t2.val * d') % m := by
      rw [← hgd, ← hgm] at htd_mod
      have h1 : t1.val * (g * d') = g * (t1.val * d') := by ring
      have h2 : t2.val * (g * d') = g * (t2.val * d') := by ring
      rw [h1, h2, Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at htd_mod
      exact Nat.eq_of_mul_eq_mul_left hg_pos htd_mod
    have hcast_mod : ∀ n : ℕ, ((n % m : ℕ) : ZMod m) = (n : ZMod m) := by
      intro n
      have h := congrArg (fun x : ℕ => (x : ZMod m)) (Nat.div_add_mod n m)
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add] at h
      exact h
    have hzm : ((t1.val * d' : ℕ) : ZMod m) = ((t2.val * d' : ℕ) : ZMod m) := by
      rw [← hcast_mod (t1.val * d'), ← hcast_mod (t2.val * d'), hdiv_mod]
    have hcop_z : IsUnit (d' : ZMod m) := (ZMod.isUnit_iff_coprime d' m).mpr hcop.symm
    have ht_eq : (t1.val : ZMod m) = (t2.val : ZMod m) := by
      rw [Nat.cast_mul, Nat.cast_mul] at hzm
      exact hcop_z.mul_right_cancel hzm
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at ht_eq
    exact Prod.ext rfl ht_eq
  have hphi_card : Fintype.card (Fin g × ZMod m) = Fintype.card (ZMod k) := by
    rw [Fintype.card_prod, Fintype.card_fin, ZMod.card, ZMod.card, hgm]
  let phiEquiv : Fin g × ZMod m ≃ ZMod k :=
    Equiv.ofBijective phi ((Fintype.bijective_iff_injective_and_card phi).mpr ⟨hphi_inj, hphi_card⟩)
  have hmd_zero : ((m * d : ℕ) : ZMod k) = 0 := by
    have hdvd : k ∣ m * d := by
      rw [← hgm, ← hgd]
      refine ⟨d', ?_⟩
      ring
    exact (ZMod.natCast_eq_zero_iff (m * d) k).mpr hdvd
  have hphi_step : ∀ (r : Fin g) (t : ZMod m),
      phi (r, t + 1) = phi (r, t) + (d : ZMod k) := by
    intro r t
    simp only [phi]
    have hval : (t + 1).val = (t.val + 1) % m := by
      have h1 : t + 1 = ((t.val + 1 : ℕ) : ZMod m) := by
        rw [Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one]
      rw [h1, ZMod.val_natCast]
    have hmul : (((t + 1).val * d : ℕ) : ZMod k) = ((t.val * d : ℕ) : ZMod k) + (d : ZMod k) := by
      rw [hval]
      have hq := Nat.div_add_mod (t.val + 1) m
      have hcast : ((t.val + 1) * d : ℕ) = (m * ((t.val + 1) / m)) * d + ((t.val + 1) % m) * d := by
        calc
          (t.val + 1) * d = (m * ((t.val + 1) / m) + (t.val + 1) % m) * d := by rw [hq]
          _ = (m * ((t.val + 1) / m)) * d + ((t.val + 1) % m) * d := by ring
      have hz := congrArg (fun n : ℕ => (n : ZMod k)) hcast
      have hq0 : (((m * ((t.val + 1) / m)) * d : ℕ) : ZMod k) = 0 := by
        have hre : (m * ((t.val + 1) / m)) * d = ((t.val + 1) / m) * (m * d) := by ring
        rw [hre, Nat.cast_mul, hmd_zero, mul_zero]
      rw [Nat.cast_add, hq0, zero_add] at hz
      rw [← hz]
      push_cast
      ring
    rw [hmul, add_assoc]
  have hphi_sub : ∀ (r : Fin g) (t : ZMod m),
      phi (r, t - 1) = phi (r, t) - (d : ZMod k) := by
    intro r t
    have h := hphi_step r (t - 1)
    rw [sub_add_cancel] at h
    rw [h, add_sub_cancel_right]
  let Sol := Finset.univ.filter (fun w : ZMod m → B =>
    ∀ t : ZMod m, w (t - 1) + w t + w (t + 1) = 0)
  let kerMix := Finset.univ.filter (fun v : ZMod k → B => mixFn d v = 0)
  have hbij : kerMix.card = Fintype.card (Fin g → ↥Sol) := by
    refine Finset.card_bij
      (fun v hv => fun r : Fin g =>
        (⟨fun t => v (phi (r, t)), by
          have hv0 : mixFn d v = 0 := (Finset.mem_filter.mp hv).2
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          intro t
          have h := congrFun hv0 (phi (r, t))
          simpa [mixFn, hphi_step, hphi_sub] using h⟩ : ↥Sol))
      ?_ ?_ ?_
    · intro v _; exact Finset.mem_univ _
    · intro v1 _ v2 _ hEq
      funext i
      let p := phiEquiv.symm i
      have hp : phi p = i := phiEquiv.apply_symm_apply i
      have hfun := congrArg (fun f : Fin g → ↥Sol => (f p.1).1 p.2) hEq
      simpa [hp] using hfun
    · intro f _
      let v : ZMod k → B := fun i => (f (phiEquiv.symm i).1).1 (phiEquiv.symm i).2
      refine ⟨v, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        funext i
        let p := phiEquiv.symm i
        have hp : phi p = i := phiEquiv.apply_symm_apply i
        have hmem := (Finset.mem_filter.mp (f p.1).2).2 p.2
        have hleft : phiEquiv.symm (i - (d : ZMod k)) = (p.1, p.2 - 1) := by
          apply phiEquiv.injective
          rw [phiEquiv.apply_symm_apply]
          change i - (d : ZMod k) = phi (p.1, p.2 - 1)
          rw [hphi_sub, ← hp]
        have hright : phiEquiv.symm (i + (d : ZMod k)) = (p.1, p.2 + 1) := by
          apply phiEquiv.injective
          rw [phiEquiv.apply_symm_apply]
          change i + (d : ZMod k) = phi (p.1, p.2 + 1)
          rw [hphi_step, ← hp]
        simpa [mixFn, v, hleft, hright, p] using hmem
      · funext r
        apply Subtype.ext
        funext t
        have hinv : phiEquiv.symm (phi (r, t)) = (r, t) := phiEquiv.symm_apply_apply (r, t)
        simp [v, hinv]
  rw [hbij, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, card_sol_cycle m]
  split_ifs with h3
  · rfl
  · simp

lemma card_lifts_formula {k : ℕ} [NeZero k] (d : ℕ) (a : ZMod k → B) :
    (Finset.univ.filter (fun u : ZMod k → B => mixFn d u = a)).card =
      if (∃ y : ZMod k → B, mixFn d y = a) then
        (if 3 ∣ (k / Nat.gcd k d) then 4 ^ (Nat.gcd k d) else 1)
      else 0 := by
  by_cases hex : ∃ y : ZMod k → B, mixFn d y = a
  · rw [if_pos hex]
    obtain ⟨y0, hy0⟩ := hex
    rw [card_lifts_of_mem d a y0 hy0, card_kerMix d]
  · rw [if_neg hex]
    have hempty : Finset.univ.filter (fun u : ZMod k → B => mixFn d u = a) = ∅ := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hu
      exact hex ⟨u, hu⟩
    rw [hempty, Finset.card_empty]

end PEqualNP.Outside.L_meta_25750_aux

theorem PEqualNP.Outside.L_meta_25750 :
∀ (k : ℕ) [NeZero k] (d : ℕ),
  let I := ZMod k
  let B := ZMod 2
  let V := I → B
  let sign := fun (t : B) => if t = 0 then (1 : ℤ) else -1
  let mix := fun (x : V) (i : I) => x (i-(d : I)) + x i + x (i+(d : I))
  let nl := fun (y : V) (j : I) => y j + (1+y (j+1))*y (j+2)
  let lifts := fun (a : V) => Finset.univ.filter (fun u : V => mix u = a)
  let transfer := fun (u b : V) (j : ℕ) =>
    let i := (j : I)
    (fun (left right : B) =>
      sign ((u i+b i+b (i-2))*left + b (i-1)*left*right) : Matrix B B ℤ)
  let g := Nat.gcd k d
  ∀ (a b : V),
    (∑ x : V, sign (dotProduct a x + dotProduct b (nl (mix x)))) =
      ∑ u ∈ lifts a, Matrix.trace (List.prod (α := Matrix B B ℤ) ((List.range k).map (transfer u b))) ∧
    (lifts a).card = (if (∃ y : V, mix y = a) then
      (if 3 ∣ (k/g) then 4^g else 1) else 0) := by
  intro k _ d
  dsimp only
  intro a b
  exact ⟨PEqualNP.Outside.L_meta_25750_aux.walsh_transfer_identity d a b,
         PEqualNP.Outside.L_meta_25750_aux.card_lifts_formula d a⟩
