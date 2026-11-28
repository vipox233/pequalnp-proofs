import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1068_aux

private lemma card_filter_mod_add_lt (N t c : ℕ) (ht : t ≤ N) (hN : 0 < N) :
    ((Finset.univ : Finset (Fin N)).filter (fun x => (x.val + c) % N < t)).card = t := by
  let f : Fin N → Fin N := fun x => ⟨(x.val + c) % N, Nat.mod_lt _ hN⟩
  have hf_bij : Function.Bijective f := by
    refine (Finite.injective_iff_bijective).mp ?_
    intro x1 x2 heq
    have hmod : (x1.val + c) % N = (x2.val + c) % N := congrArg Fin.val heq
    have h1 := x1.isLt
    have h2 := x2.isLt
    have hq : x1.val = x2.val := by
      have hm1 : (x1.val + c) % N = ((x1.val + c) % N) := rfl
      have hsub : (x1.val + c + (N - c % N)) % N = (x2.val + c + (N - c % N)) % N := by
        rw [Nat.add_mod, hmod, ← Nat.add_mod]
      have hleft : (x1.val + c + (N - c % N)) % N = x1.val := by
        have hcm : c = N * (c / N) + c % N := (Nat.div_add_mod c N).symm
        have hle : c % N ≤ N := le_of_lt (Nat.mod_lt c hN)
        have hmul : N * (c / N + 1) = N * (c / N) + N := by ring
        have heq1 : x1.val + c + (N - c % N) = x1.val + N * (c / N + 1) := by omega
        rw [heq1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
      have hright : (x2.val + c + (N - c % N)) % N = x2.val := by
        have hcm : c = N * (c / N) + c % N := (Nat.div_add_mod c N).symm
        have hle : c % N ≤ N := le_of_lt (Nat.mod_lt c hN)
        have hmul : N * (c / N + 1) = N * (c / N) + N := by ring
        have heq2 : x2.val + c + (N - c % N) = x2.val + N * (c / N + 1) := by omega
        rw [heq2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
      rw [hleft, hright] at hsub
      exact hsub
    exact Fin.ext hq
  let e : Fin N ≃ Fin N := Equiv.ofBijective f hf_bij
  have hbij : ((Finset.univ : Finset (Fin N)).filter (fun x => (x.val + c) % N < t)).card =
      ((Finset.univ : Finset (Fin N)).filter (fun y => y.val < t)).card := by
    refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx
    · intro x1 _ x2 _ heq; exact e.injective heq
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hval : (e (e.symm y)).val = y.val := congrArg Fin.val (e.apply_symm_apply y)
      rwa [← hval] at hy
  rw [hbij]
  have hbij2 : ((Finset.univ : Finset (Fin N)).filter (fun y => y.val < t)).card =
      (Finset.univ : Finset (Fin t)).card := by
    refine Finset.card_bij (fun y hy => ⟨y.val, (Finset.mem_filter.mp hy).2⟩) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro y1 _ y2 _ heq; exact Fin.ext (by simpa using congrArg Fin.val heq)
    · intro j _
      refine ⟨⟨j.val, lt_of_lt_of_le j.isLt ht⟩, ?_, Fin.ext rfl⟩
      simp [j.isLt]
  rw [hbij2, Finset.card_univ, Fintype.card_fin]

private lemma card_filter_mod_sub_lt (N t c : ℕ) (ht : t ≤ N) (hN : 0 < N) (hc : N ≤ c) :
    ((Finset.univ : Finset (Fin N)).filter (fun x => (c - x.val) % N < t)).card = t := by
  let rev : Fin N → Fin N := fun x => ⟨(N - x.val) % N, Nat.mod_lt _ hN⟩
  have hrev_inv : ∀ x : Fin N, rev (rev x) = x := by
    intro x
    apply Fin.ext
    dsimp only [rev]
    have hx := x.isLt
    by_cases hx0 : x.val = 0
    · simp [hx0]
    · have h1 : (N - x.val) % N = N - x.val := Nat.mod_eq_of_lt (by omega)
      rw [h1]
      have h2 : N - (N - x.val) = x.val := by omega
      rw [h2, Nat.mod_eq_of_lt hx]
  have hbij : ((Finset.univ : Finset (Fin N)).filter (fun x => (c - x.val) % N < t)).card =
      ((Finset.univ : Finset (Fin N)).filter (fun y => (y.val + c) % N < t)).card := by
    refine Finset.card_bij (fun x _ => rev x) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have hxlt := x.isLt
      have hmod : ((rev x).val + c) % N = (c - x.val) % N := by
        dsimp only [rev]
        by_cases hx0 : x.val = 0
        · simp [hx0]
        · rw [Nat.mod_eq_of_lt (by omega : N - x.val < N)]
          have heq : N - x.val + c = (c - x.val) + N := by omega
          rw [heq, Nat.add_mod_right]
      rwa [hmod]
    · intro x1 _ x2 _ heq
      have := congrArg rev heq
      rwa [hrev_inv, hrev_inv] at this
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine ⟨rev y, ?_, hrev_inv y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hylt := y.isLt
      have hmod : (c - (rev y).val) % N = (y.val + c) % N := by
        dsimp only [rev]
        by_cases hy0 : y.val = 0
        · simp [hy0]
        · rw [Nat.mod_eq_of_lt (by omega : N - y.val < N)]
          have heq : y.val + c = (c - (N - y.val)) + N := by omega
          rw [heq, Nat.add_mod_right]
      rwa [hmod]
  rw [hbij]
  exact card_filter_mod_add_lt N t c ht hN

private lemma card_flip_two {α : Type*} [Fintype α] [DecidableEq α]
    (P : α → Bool) (a b : α) (hab : a ≠ b) (ha : P a = true) (hb : P b = false) :
    ((Finset.univ : Finset α).filter (fun x =>
      if x = a then false else if x = b then true else P x)).card =
    ((Finset.univ : Finset α).filter (fun x => P x)).card := by
  let Q : α → Bool := fun x => if x = a then false else if x = b then true else P x
  let sw : Equiv.Perm α := Equiv.swap a b
  refine Finset.card_bij (fun x _ => sw x) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    by_cases hxa : x = a
    · subst hxa; simp at hx
    · by_cases hxb : x = b
      · subst hxb; simp [sw, ha]
      · simp only [hxa, hxb, ↓reduceIte] at hx
        have hsw : sw x = x := Equiv.swap_apply_of_ne_of_ne hxa hxb
        rwa [hsw]
  · intro x1 _ x2 _ heq; exact sw.injective heq
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    refine ⟨sw y, ?_, sw.apply_symm_apply y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hya : y = a
    · subst hya; simp [sw, Ne.symm hab]
    · by_cases hyb : y = b
      · subst hyb; rw [hb] at hy; exact Bool.noConfusion hy
      · have hsw : sw y = y := Equiv.swap_apply_of_ne_of_ne hya hyb
        rw [hsw]
        simp [hya, hyb, hy]

private lemma sum_eq_zero_of_uniform {N t : ℕ} (hN : 0 < N)
    (G : Fin N → Fin N → Fin N → Bool)
    (hcov : ∀ u v : Fin N, ((Finset.univ : Finset (Fin N)).filter (fun y => G y u v)).card = t)
    (B : Fin N → Fin N → ℝ) :
    ∑ y : Fin N, ((∑ u : Fin N, ∑ v : Fin N, if G y u v then B u v else 0) -
      (t : ℝ) / (N : ℝ) * (∑ u : Fin N, ∑ v : Fin N, B u v)) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hswap : (∑ y : Fin N, ∑ u : Fin N, ∑ v : Fin N, if G y u v then B u v else 0) =
      (t : ℝ) * (∑ u : Fin N, ∑ v : Fin N, B u v) := by
    rw [Finset.sum_comm]
    have h1 : ∀ u : Fin N, (∑ y : Fin N, ∑ v : Fin N, if G y u v then B u v else 0) =
        (t : ℝ) * (∑ v : Fin N, B u v) := by
      intro u
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      have h2 : (∑ y : Fin N, if G y u v then B u v else 0) =
          (((Finset.univ : Finset (Fin N)).filter (fun y => G y u v)).card : ℝ) * B u v := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      rw [h2, hcov u v]
    rw [Finset.sum_congr rfl (fun u _ => h1 u), ← Finset.mul_sum]
  rw [hswap]
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN)
  field_simp [hNne]
  ring

private lemma diff_le_of_cycle_bound {N : ℕ} (hN : 0 < N) (g : Fin N → ℝ)
    (s t : Fin N → ℝ) (h : ℝ)
    (_hs_sum : ∑ y : Fin N, s y = 0) (ht_sum : ∑ y : Fin N, t y = 0)
    (hs_le : ∀ y, s y ≤ h) (ht_le : ∀ y, t y ≤ h)
    (hstep : ∀ y : Fin N, g y - g ⟨(y.val + 1) % N, Nat.mod_lt _ hN⟩ = s y - t y) :
    ∀ y1 y2 : Fin N, g y1 - g y2 ≤ (N : ℝ) * h := by
  intro y1 y2
  let k : ℕ := (y2.val + N - y1.val) % N
  have hk_lt : k < N := Nat.mod_lt _ hN
  let pt : ℕ → Fin N := fun j => ⟨(y1.val + j) % N, Nat.mod_lt _ hN⟩
  have hpt0 : pt 0 = y1 := Fin.ext (by dsimp only [pt]; rw [add_zero, Nat.mod_eq_of_lt y1.isLt])
  have hptk : pt k = y2 := by
    apply Fin.ext
    dsimp only [pt, k]
    have h1 := y1.isLt
    have h2 := y2.isLt
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have heq : y1.val + (y2.val + N - y1.val) = y2.val + N := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt h2]
  have hpt_next : ∀ j : ℕ, pt (j + 1) = ⟨((pt j).val + 1) % N, Nat.mod_lt _ hN⟩ := by
    intro j
    apply Fin.ext
    dsimp only [pt]
    rw [← add_assoc, Nat.add_mod]
    conv_rhs => rw [Nat.add_mod, Nat.mod_mod]
  have htelesc : ∀ m : ℕ, g y1 - g (pt m) = ∑ j ∈ Finset.range m, (s (pt j) - t (pt j)) := by
    intro m
    induction m with
    | zero => simp [hpt0]
    | succ m ih =>
      rw [Finset.sum_range_succ, ← ih, hpt_next m, ← hstep (pt m)]
      ring
  have hmain := htelesc k
  rw [hptk, Finset.sum_sub_distrib] at hmain
  have hS_bound : ∑ j ∈ Finset.range k, s (pt j) ≤ (k : ℝ) * h := by
    calc ∑ j ∈ Finset.range k, s (pt j)
        ≤ ∑ _j ∈ Finset.range k, h := Finset.sum_le_sum (fun j _ => hs_le _)
      _ = (k : ℝ) * h := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hpt_inj : ∀ j1 ∈ Finset.range N, ∀ j2 ∈ Finset.range N, pt j1 = pt j2 → j1 = j2 := by
    intro j1 hj1 j2 hj2 heq
    have h1 : j1 < N := Finset.mem_range.mp hj1
    have h2 : j2 < N := Finset.mem_range.mp hj2
    have hmod : (y1.val + j1) % N = (y1.val + j2) % N := congrArg Fin.val heq
    have hy1 := y1.isLt
    have hadd : (y1.val + j1 + (N - y1.val)) % N = (y1.val + j2 + (N - y1.val)) % N := by
      rw [Nat.add_mod, hmod, ← Nat.add_mod]
    have hl : (y1.val + j1 + (N - y1.val)) % N = j1 := by
      have : y1.val + j1 + (N - y1.val) = j1 + N := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt h1]
    have hr : (y1.val + j2 + (N - y1.val)) % N = j2 := by
      have : y1.val + j2 + (N - y1.val) = j2 + N := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt h2]
    rw [hl, hr] at hadd
    exact hadd
  have hT_all : ∑ j ∈ Finset.range N, t (pt j) = 0 := by
    rw [← ht_sum]
    refine Finset.sum_bij (fun j _ => pt j) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · exact hpt_inj
    · intro y _
      let j := (y.val + N - y1.val) % N
      refine ⟨j, Finset.mem_range.mpr (Nat.mod_lt _ hN), ?_⟩
      apply Fin.ext
      dsimp only [pt, j]
      have h1 := y1.isLt
      have h2 := y.isLt
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have heq : y1.val + (y.val + N - y1.val) = y.val + N := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt h2]
    · intro _ _; rfl
  have hT_split : (∑ j ∈ Finset.range k, t (pt j)) + ∑ j ∈ Finset.Ico k N, t (pt j) = 0 := by
    rw [← Finset.sum_union (Finset.disjoint_left.mpr (fun x hx1 hx2 => by
      have := Finset.mem_range.mp hx1; have := (Finset.mem_Ico.mp hx2).1; omega))]
    have hunion : Finset.range k ∪ Finset.Ico k N = Finset.range N := by
      ext x
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hunion, hT_all]
  have hT_bound : -(∑ j ∈ Finset.range k, t (pt j)) ≤ ((N - k : ℕ) : ℝ) * h := by
    have hneg : -(∑ j ∈ Finset.range k, t (pt j)) = ∑ j ∈ Finset.Ico k N, t (pt j) := by linarith
    rw [hneg]
    calc ∑ j ∈ Finset.Ico k N, t (pt j)
        ≤ ∑ _j ∈ Finset.Ico k N, h := Finset.sum_le_sum (fun j _ => ht_le _)
      _ = ((N - k : ℕ) : ℝ) * h := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hcast : (k : ℝ) + ((N - k : ℕ) : ℝ) = (N : ℝ) := by
    rw [← Nat.cast_add, Nat.add_sub_of_le (le_of_lt hk_lt)]
  have hmul : (k : ℝ) * h + ((N - k : ℕ) : ℝ) * h = (N : ℝ) * h := by
    rw [← add_mul, hcast]
  rw [hmain]
  linarith [hS_bound, hT_bound, hmul]

end PEqualNP.Outside.L_lib_1068_aux

open PEqualNP.Outside.L_lib_1068_aux

theorem PEqualNP.Outside.L_lib_1068 :
    (∀ N t : ℕ, 0 < t → t < N →
  let X := Fin N
  let L := 2*N*(N-1)
  let reg := fun (T : X → X → Bool) =>
    (∀ x, (Finset.univ.filter (fun y => T x y)).card = t) ∧
    (∀ y, (Finset.univ.filter (fun x => T x y)).card = t)
  let score := fun (B : X → X → ℝ) (T : X → X → Bool) => ∑ x, ∑ y, if T x y then B x y else 0
  let mean := fun (B : X → X → ℝ) => (t : ℝ)/(N : ℝ)*(∑ x, ∑ y, B x y)
  ∃ test : Fin L → X → X → Bool, (∀ i, reg (test i)) ∧
    (∀ x y, (Finset.univ.filter (fun i => test i x y)).card = 2*t*(N-1)) ∧
    ∀ (B : X → X → ℝ) (h : ℝ), 0 ≤ h → (∀ i, score B (test i) ≤ mean B + h) →
      (∃ a b : X → ℝ, ∀ x y, |B x y - a x - b y| ≤ (N : ℝ)*h/2) ∧
      ∀ T, reg T → |score B T - mean B| ≤ (((N-1)*t*(N-t) : ℕ) : ℝ)*h) := by
  intro N t ht_pos htN
  dsimp only
  have hN_pos : 0 < N := lt_trans ht_pos htN
  have hN_ge2 : 2 ≤ N := by omega
  let X := Fin N
  let L := 2 * N * (N - 1)
  let reg : (X → X → Bool) → Prop := fun T =>
    (∀ x, (Finset.univ.filter (fun y => T x y)).card = t) ∧
    (∀ y, (Finset.univ.filter (fun x => T x y)).card = t)
  let score : (X → X → ℝ) → (X → X → Bool) → ℝ := fun B T =>
    ∑ x, ∑ y, if T x y then B x y else 0
  let mean : (X → X → ℝ) → ℝ := fun B => (t : ℝ) / (N : ℝ) * (∑ x, ∑ y, B x y)
  let next : X → X := fun y => ⟨(y.val + 1) % N, Nat.mod_lt _ hN_pos⟩
  let prev : X → X := fun y => ⟨(y.val + N - 1) % N, Nat.mod_lt _ hN_pos⟩
  have hnext_ne : ∀ y : X, y ≠ next y := by
    intro y heq
    have hv : y.val = (y.val + 1) % N := congrArg Fin.val heq
    have hy := y.isLt
    by_cases hlast : y.val + 1 = N
    · rw [hlast, Nat.mod_self] at hv; omega
    · rw [Nat.mod_eq_of_lt (by omega)] at hv; omega
  have hnext_prev : ∀ y : X, next (prev y) = y := by
    intro y
    apply Fin.ext
    dsimp only [next, prev]
    have hy := y.isLt
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have heq : y.val + N - 1 + 1 = y.val + N := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hy]
  have hprev_next : ∀ y : X, prev (next y) = y := by
    intro y
    apply Fin.ext
    dsimp only [next, prev]
    have hy := y.isLt
    by_cases hlast : y.val + 1 = N
    · rw [hlast, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega : N - 1 < N)]
      omega
    · have hlt : y.val + 1 < N := by omega
      rw [Nat.mod_eq_of_lt hlt]
      have heq : y.val + 1 + N - 1 = y.val + N := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hy]
  let rowOf : Fin (N - 1) → X := fun d => ⟨d.val + 1, by have := d.isLt; omega⟩
  have hrowOf_ne0 : ∀ d : Fin (N - 1), rowOf d ≠ ⟨0, hN_pos⟩ := by
    intro d heq
    have := congrArg Fin.val heq
    dsimp only [rowOf] at this
    omega
  let u0 : X := ⟨0, hN_pos⟩
  let ut : X := ⟨t, htN⟩
  have hut_ne0 : ut ≠ u0 := by
    intro heq
    have := congrArg Fin.val heq
    dsimp only [ut, u0] at this
    omega
  let swapRow : Fin (N - 1) → Equiv.Perm X := fun d => Equiv.swap (rowOf d) ut
  have hswap0 : ∀ d, swapRow d u0 = u0 := fun d =>
    Equiv.swap_apply_of_ne_of_ne (Ne.symm (hrowOf_ne0 d)) (Ne.symm hut_ne0)
  have hswapd : ∀ d, swapRow d (rowOf d) = ut := fun d => Equiv.swap_apply_left _ _
  let shift : X → X → X → Bool := fun y u v =>
    decide ((v.val + t + 2 * N - 1 - y.val - u.val) % N < t)
  let S : Fin (N - 1) → X → X → X → Bool := fun d y u v => shift y (swapRow d u) v
  let T : Fin (N - 1) → X → X → X → Bool := fun d y u v =>
    if (u = u0 ∧ v = y) ∨ (u = rowOf d ∧ v = next y) then false
    else if (u = u0 ∧ v = next y) ∨ (u = rowOf d ∧ v = y) then true
    else S d y u v
  have hS_0_y : ∀ d y, S d y u0 y = true := by
    intro d y
    dsimp only [S, shift]
    rw [hswap0 d]
    simp only [decide_eq_true_eq]
    have hy := y.isLt
    have heq : y.val + t + 2 * N - 1 - y.val - u0.val = (t - 1) + 2 * N := by dsimp only [u0]; omega
    rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    omega
  have hS_0_ny : ∀ d y, S d y u0 (next y) = false := by
    intro d y
    dsimp only [S, shift]
    rw [hswap0 d]
    simp only [decide_eq_false_iff_not]
    have hy := y.isLt
    have hmod : ((next y).val + t + 2 * N - 1 - y.val - u0.val) % N = t := by
      dsimp only [next, u0]
      by_cases hlast : y.val + 1 = N
      · rw [hlast, Nat.mod_self]
        have heq : 0 + t + 2 * N - 1 - y.val - 0 = t + N := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt htN]
      · have hlt : y.val + 1 < N := by omega
        rw [Nat.mod_eq_of_lt hlt]
        have heq : y.val + 1 + t + 2 * N - 1 - y.val - 0 = t + 2 * N := by omega
        rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt htN]
    rw [hmod]
    omega
  have hS_d_y : ∀ d y, S d y (rowOf d) y = false := by
    intro d y
    dsimp only [S, shift]
    rw [hswapd d]
    simp only [decide_eq_false_iff_not]
    have hy := y.isLt
    have heq : y.val + t + 2 * N - 1 - y.val - ut.val = (N - 1) + N := by dsimp only [ut]; omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  have hS_d_ny : ∀ d y, S d y (rowOf d) (next y) = true := by
    intro d y
    dsimp only [S, shift]
    rw [hswapd d]
    simp only [decide_eq_true_eq]
    have hy := y.isLt
    have hmod : ((next y).val + t + 2 * N - 1 - y.val - ut.val) % N = 0 := by
      dsimp only [next, ut]
      by_cases hlast : y.val + 1 = N
      · rw [hlast, Nat.mod_self]
        have heq : 0 + t + 2 * N - 1 - y.val - t = N := by omega
        rw [heq, Nat.mod_self]
      · have hlt : y.val + 1 < N := by omega
        rw [Nat.mod_eq_of_lt hlt]
        have heq : y.val + 1 + t + 2 * N - 1 - y.val - t = 2 * N := by omega
        rw [heq, Nat.mul_mod_left]
    rw [hmod]
    exact ht_pos
  have hS_reg : ∀ d y, reg (S d y) := by
    intro d y
    constructor
    · intro u
      dsimp only [S, shift]
      have hc : ∀ v : X, (v.val + t + 2 * N - 1 - y.val - (swapRow d u).val) =
          v.val + (t + 2 * N - 1 - y.val - (swapRow d u).val) := by
        intro v; have := y.isLt; have := (swapRow d u).isLt; omega
      simp_rw [hc, decide_eq_true_eq]
      exact card_filter_mod_add_lt N t _ (le_of_lt htN) hN_pos
    · intro v
      have hbij : ((Finset.univ : Finset X).filter (fun u => S d y u v)).card =
          ((Finset.univ : Finset X).filter (fun u => shift y u v)).card := by
        refine Finset.card_bij (fun u _ => swapRow d u) ?_ ?_ ?_
        · intro u hu; simpa [S] using hu
        · intro u1 _ u2 _ heq; exact (swapRow d).injective heq
        · intro u hu
          refine ⟨(swapRow d).symm u, ?_, (swapRow d).apply_symm_apply u⟩
          simpa [S] using hu
      rw [hbij]
      dsimp only [shift]
      simp_rw [decide_eq_true_eq]
      exact card_filter_mod_sub_lt N t (v.val + t + 2 * N - 1 - y.val) (le_of_lt htN) hN_pos
        (by have := y.isLt; omega)
  have hT_reg : ∀ d y, reg (T d y) := by
    intro d y
    constructor
    · intro u
      by_cases hu0 : u = u0
      · subst hu0
        have hrew : ∀ v, T d y u0 v =
            (if v = y then false else if v = next y then true else S d y u0 v) := by
          intro v
          dsimp only [T]
          have hne : u0 ≠ rowOf d := Ne.symm (hrowOf_ne0 d)
          by_cases hvy : v = y
          · simp [hvy]
          · by_cases hvny : v = next y
            · simp [hvy, hvny, hne]
            · simp [hvy, hvny, hne]
        simp_rw [hrew]
        rw [card_flip_two (fun v => S d y u0 v) y (next y) (hnext_ne y) (hS_0_y d y) (hS_0_ny d y)]
        exact (hS_reg d y).1 u0
      · by_cases hud : u = rowOf d
        · subst hud
          have hrew : ∀ v, T d y (rowOf d) v =
              (if v = next y then false else if v = y then true else S d y (rowOf d) v) := by
            intro v
            dsimp only [T]
            by_cases hvny : v = next y
            · simp [hvny]
            · by_cases hvy : v = y
              · simp [hvy, hvny, hu0]
              · simp [hvy, hvny, hu0]
          simp_rw [hrew]
          rw [card_flip_two (fun v => S d y (rowOf d) v) (next y) y (Ne.symm (hnext_ne y))
            (hS_d_ny d y) (hS_d_y d y)]
          exact (hS_reg d y).1 (rowOf d)
        · have hrew : ∀ v, T d y u v = S d y u v := by
            intro v; dsimp only [T]; simp [hu0, hud]
          simp_rw [hrew]
          exact (hS_reg d y).1 u
    · intro v
      by_cases hvy : v = y
      · subst v
        have hrew : ∀ u, T d y u y =
            (if u = u0 then false else if u = rowOf d then true else S d y u y) := by
          intro u
          dsimp only [T]
          have hne : y ≠ next y := hnext_ne y
          by_cases hu0 : u = u0
          · simp [hu0]
          · by_cases hud : u = rowOf d
            · simp [hu0, hud, hne]
            · simp [hu0, hud, hne]
        simp_rw [hrew]
        rw [card_flip_two (fun u => S d y u y) u0 (rowOf d) (Ne.symm (hrowOf_ne0 d))
          (hS_0_y d y) (hS_d_y d y)]
        exact (hS_reg d y).2 y
      · by_cases hvny : v = next y
        · subst v
          have hrew : ∀ u, T d y u (next y) =
              (if u = rowOf d then false else if u = u0 then true else S d y u (next y)) := by
            intro u
            dsimp only [T]
            by_cases hud : u = rowOf d
            · simp [hud]
            · by_cases hu0 : u = u0
              · simp [hu0, hud, hvy]
              · simp [hu0, hud, hvy]
          simp_rw [hrew]
          rw [card_flip_two (fun u => S d y u (next y)) (rowOf d) u0 (hrowOf_ne0 d)
            (hS_d_ny d y) (hS_0_ny d y)]
          exact (hS_reg d y).2 (next y)
        · have hrew : ∀ u, T d y u v = S d y u v := by
            intro u; dsimp only [T]; simp [hvy, hvny]
          simp_rw [hrew]
          exact (hS_reg d y).2 v
  have hS_cov : ∀ d u v, ((Finset.univ : Finset X).filter (fun y => S d y u v)).card = t := by
    intro d u v
    dsimp only [S, shift]
    have hrew : ∀ y : X, v.val + t + 2 * N - 1 - y.val - (swapRow d u).val =
        (v.val + t + 2 * N - 1 - (swapRow d u).val) - y.val := by
      intro y; have := y.isLt; have := (swapRow d u).isLt; omega
    simp_rw [hrew, decide_eq_true_eq]
    exact card_filter_mod_sub_lt N t (v.val + t + 2 * N - 1 - (swapRow d u).val) (le_of_lt htN) hN_pos
      (by have := (swapRow d u).isLt; omega)
  have hT_cov : ∀ d u v, ((Finset.univ : Finset X).filter (fun y => T d y u v)).card = t := by
    intro d u v
    by_cases hu0 : u = u0
    · subst hu0
      have hrew : ∀ y, T d y u0 v =
          (if y = v then false else if y = prev v then true else S d y u0 v) := by
        intro y
        dsimp only [T]
        have hne : u0 ≠ rowOf d := Ne.symm (hrowOf_ne0 d)
        by_cases hyv : y = v
        · simp [hyv]
        · by_cases hypv : y = prev v
          · have hvny : v = next y := by rw [hypv, hnext_prev]
            have h1 : ¬ ((u0 = u0 ∧ v = y) ∨ (u0 = rowOf d ∧ v = next y)) := by
              rintro (⟨_, h⟩ | ⟨h, _⟩)
              · exact hyv h.symm
              · exact hne h
            have h2 : (u0 = u0 ∧ v = next y) ∨ (u0 = rowOf d ∧ v = y) := Or.inl ⟨rfl, hvny⟩
            rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2),
              ite_eq_right_of_eq_false _ _ (eq_false hyv), ite_eq_left_of_eq_true _ _ (eq_true hypv)]
          · have hvny : v ≠ next y := fun h => hypv (by rw [h, hprev_next])
            have h1 : ¬ ((u0 = u0 ∧ v = y) ∨ (u0 = rowOf d ∧ v = next y)) := by
              rintro (⟨_, h⟩ | ⟨h, _⟩)
              · exact hyv h.symm
              · exact hne h
            have h2 : ¬ ((u0 = u0 ∧ v = next y) ∨ (u0 = rowOf d ∧ v = y)) := by
              rintro (⟨_, h⟩ | ⟨h, _⟩)
              · exact hvny h
              · exact hne h
            rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2)]
            simp only [hyv, hypv, ↓reduceIte]
      have hv_ne_pv : v ≠ prev v := fun h => hnext_ne (prev v) (by rw [hnext_prev, ← h])
      have hS_pv : S d (prev v) u0 v = false := by
        have := hS_0_ny d (prev v); rwa [hnext_prev] at this
      simp_rw [hrew]
      rw [card_flip_two (fun y => S d y u0 v) v (prev v) hv_ne_pv (hS_0_y d v) hS_pv]
      exact hS_cov d u0 v
    · by_cases hud : u = rowOf d
      · subst hud
        have hrew : ∀ y, T d y (rowOf d) v =
            (if y = prev v then false else if y = v then true else S d y (rowOf d) v) := by
          intro y
          dsimp only [T]
          by_cases hypv : y = prev v
          · have hvny : v = next y := by rw [hypv, hnext_prev]
            have h1 : (rowOf d = u0 ∧ v = y) ∨ (rowOf d = rowOf d ∧ v = next y) := Or.inr ⟨rfl, hvny⟩
            rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
            simp only [hypv, ↓reduceIte]
          · by_cases hyv : y = v
            · have hvny : v ≠ next y := fun h => hypv (by rw [h, hprev_next])
              have h1 : ¬ ((rowOf d = u0 ∧ v = y) ∨ (rowOf d = rowOf d ∧ v = next y)) := by
                rintro (⟨h, _⟩ | ⟨_, h⟩)
                · exact hu0 h
                · exact hvny h
              have h2 : (rowOf d = u0 ∧ v = next y) ∨ (rowOf d = rowOf d ∧ v = y) := Or.inr ⟨rfl, hyv.symm⟩
              rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2),
                ite_eq_right_of_eq_false _ _ (eq_false hypv), ite_eq_left_of_eq_true _ _ (eq_true hyv)]
            · have hvny : v ≠ next y := fun h => hypv (by rw [h, hprev_next])
              have h1 : ¬ ((rowOf d = u0 ∧ v = y) ∨ (rowOf d = rowOf d ∧ v = next y)) := by
                rintro (⟨h, _⟩ | ⟨_, h⟩)
                · exact hu0 h
                · exact hvny h
              have h2 : ¬ ((rowOf d = u0 ∧ v = next y) ∨ (rowOf d = rowOf d ∧ v = y)) := by
                rintro (⟨h, _⟩ | ⟨_, h⟩)
                · exact hu0 h
                · exact hyv h.symm
              rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2)]
              simp only [hypv, hyv, ↓reduceIte]
        have hpv_ne_v : prev v ≠ v := fun h => hnext_ne (prev v) (by rw [hnext_prev, h])
        have hS_pv : S d (prev v) (rowOf d) v = true := by
          have := hS_d_ny d (prev v); rwa [hnext_prev] at this
        simp_rw [hrew]
        rw [card_flip_two (fun y => S d y (rowOf d) v) (prev v) v hpv_ne_v hS_pv (hS_d_y d v)]
        exact hS_cov d (rowOf d) v
      · have hrew : ∀ y, T d y u v = S d y u v := by
          intro y; dsimp only [T]; simp [hu0, hud]
        simp_rw [hrew]
        exact hS_cov d u v
  let Idx := Bool × Fin (N - 1) × X
  have hcardIdx : Fintype.card Idx = L := by
    dsimp only [Idx, L]
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, Fintype.card_fin]
    ring
  let eL : Fin L ≃ Idx := (Fintype.equivFinOfCardEq hcardIdx).symm
  let test : Fin L → X → X → Bool := fun i =>
    let p := eL i
    if p.1 then S p.2.1 p.2.2 else T p.2.1 p.2.2
  refine ⟨test, ?_, ?_, ?_⟩
  · intro i
    dsimp only [test]
    by_cases hb : (eL i).1 = true
    · simp only [hb, ↓reduceIte]; exact hS_reg _ _
    · simp only [hb, ↓reduceIte]; exact hT_reg _ _
  · intro u v
    have hbij : ((Finset.univ : Finset (Fin L)).filter (fun i => test i u v)).card =
        ((Finset.univ : Finset Idx).filter (fun p => (if p.1 then S p.2.1 p.2.2 else T p.2.1 p.2.2) u v)).card := by
      refine Finset.card_bij (fun i _ => eL i) ?_ ?_ ?_
      · intro i hi; simpa [test] using hi
      · intro i1 _ i2 _ heq; exact eL.injective heq
      · intro p hp
        refine ⟨eL.symm p, ?_, eL.apply_symm_apply p⟩
        simpa [test] using hp
    rw [hbij]
    have hsum : ((Finset.univ : Finset Idx).filter (fun p =>
          (if p.1 then S p.2.1 p.2.2 else T p.2.1 p.2.2) u v)).card =
        ∑ p : Idx, if (if p.1 then S p.2.1 p.2.2 else T p.2.1 p.2.2) u v then 1 else 0 := by
      rw [Finset.card_filter]
    rw [hsum, Fintype.sum_prod_type, Fintype.sum_bool]
    have htrue : (∑ q : Fin (N - 1) × X, if S q.1 q.2 u v then 1 else 0) = (N - 1) * t := by
      rw [Fintype.sum_prod_type]
      have h1 : ∀ d : Fin (N - 1), (∑ y : X, if S d y u v then 1 else 0) = t := by
        intro d; rw [← Finset.card_filter]; exact hS_cov d u v
      rw [Finset.sum_congr rfl (fun d _ => h1 d), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
    have hfalse : (∑ q : Fin (N - 1) × X, if T q.1 q.2 u v then 1 else 0) = (N - 1) * t := by
      rw [Fintype.sum_prod_type]
      have h1 : ∀ d : Fin (N - 1), (∑ y : X, if T d y u v then 1 else 0) = t := by
        intro d; rw [← Finset.card_filter]; exact hT_cov d u v
      rw [Finset.sum_congr rfl (fun d _ => h1 d), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
    simp only [↓reduceIte, Bool.false_eq_true]
    rw [htrue, hfalse]
    ring
  · intro B h hh hbound
    have hS_bound : ∀ d y, score B (S d y) - mean B ≤ h := by
      intro d y
      have h1 := hbound (eL.symm (true, d, y))
      simp only [test, Equiv.apply_symm_apply, ↓reduceIte] at h1
      linarith
    have hT_bound : ∀ d y, score B (T d y) - mean B ≤ h := by
      intro d y
      have h1 := hbound (eL.symm (false, d, y))
      simp only [test, Equiv.apply_symm_apply, Bool.false_eq_true, ↓reduceIte] at h1
      linarith
    have hdiff_ST : ∀ d y, score B (S d y) - score B (T d y) =
        (B u0 y - B (rowOf d) y) - (B u0 (next y) - B (rowOf d) (next y)) := by
      intro d y
      dsimp only [score]
      rw [← Finset.sum_sub_distrib]
      have hrow_diff : ∀ u : X,
          ((∑ v : X, if S d y u v then B u v else 0) - ∑ v : X, if T d y u v then B u v else 0) =
          if u = u0 then B u0 y - B u0 (next y)
          else if u = rowOf d then B (rowOf d) (next y) - B (rowOf d) y
          else 0 := by
        intro u
        rw [← Finset.sum_sub_distrib]
        by_cases hu0 : u = u0
        · subst hu0
          simp only [↓reduceIte]
          have hterm : ∀ v : X,
              ((if S d y u0 v then B u0 v else 0) - (if T d y u0 v then B u0 v else 0)) =
              if v = y then B u0 y else if v = next y then -B u0 (next y) else 0 := by
            intro v
            have hne : u0 ≠ rowOf d := Ne.symm (hrowOf_ne0 d)
            by_cases hvy : v = y
            · subst v; dsimp only [T]; simp [hS_0_y d y]
            · by_cases hvny : v = next y
              · subst v; dsimp only [T]; simp [hS_0_ny d y, hvy, hne]
              · dsimp only [T]; simp [hvy, hvny, hne]
          rw [Finset.sum_congr rfl (fun v _ => hterm v)]
          have h2 : ∑ v ∈ Finset.univ.filter (fun v => v ≠ y), (if v = next y then -B u0 (next y) else 0) =
              -B u0 (next y) := by
            rw [Finset.sum_ite_eq']
            simp [Ne.symm (hnext_ne y)]
          have hsplit : (∑ v : X, if v = y then B u0 y else if v = next y then -B u0 (next y) else 0) =
              B u0 y + ∑ v ∈ Finset.univ.filter (fun v => v ≠ y), (if v = next y then -B u0 (next y) else 0) := by
            rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v : X => v = y)]
            congr 1
            · rw [Finset.filter_eq' Finset.univ y]; simp
            · refine Finset.sum_congr rfl (fun v hv => ?_)
              have hne : v ≠ y := (Finset.mem_filter.mp hv).2
              simp [hne]
          rw [hsplit, h2]
          ring
        · by_cases hud : u = rowOf d
          · subst hud
            simp only [hu0, ↓reduceIte]
            have hterm : ∀ v : X,
                ((if S d y (rowOf d) v then B (rowOf d) v else 0) -
                  (if T d y (rowOf d) v then B (rowOf d) v else 0)) =
                if v = next y then B (rowOf d) (next y) else if v = y then -B (rowOf d) y else 0 := by
              intro v
              by_cases hvny : v = next y
              · subst v; dsimp only [T]; simp [hS_d_ny d y]
              · by_cases hvy : v = y
                · subst v; dsimp only [T]; simp [hS_d_y d y, hvny, hu0]
                · dsimp only [T]; simp [hvy, hvny, hu0]
            rw [Finset.sum_congr rfl (fun v _ => hterm v)]
            rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v : X => v = next y)]
            have h1 : ∑ v ∈ Finset.univ.filter (fun v => v = next y),
                (if v = next y then B (rowOf d) (next y) else if v = y then -B (rowOf d) y else 0) =
                B (rowOf d) (next y) := by
              rw [Finset.filter_eq' Finset.univ (next y)]; simp
            have h2 : ∑ v ∈ Finset.univ.filter (fun v => v ≠ next y),
                (if v = next y then B (rowOf d) (next y) else if v = y then -B (rowOf d) y else 0) =
                -B (rowOf d) y := by
              have hcongr : ∑ v ∈ Finset.univ.filter (fun v => v ≠ next y),
                  (if v = next y then B (rowOf d) (next y) else if v = y then -B (rowOf d) y else 0) =
                  ∑ v ∈ Finset.univ.filter (fun v => v ≠ next y), if v = y then -B (rowOf d) y else 0 :=
                Finset.sum_congr rfl (fun v hv => by simp [(Finset.mem_filter.mp hv).2])
              rw [hcongr, Finset.sum_ite_eq']
              simp [hnext_ne y]
            rw [h1, h2]
            ring
          · simp only [hu0, hud, ↓reduceIte]
            refine Finset.sum_eq_zero (fun v _ => ?_)
            dsimp only [T]
            simp [hu0, hud]
      rw [Finset.sum_congr rfl (fun u _ => hrow_diff u)]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun u : X => u = u0)]
      have h1 : ∑ u ∈ Finset.univ.filter (fun u => u = u0),
          (if u = u0 then B u0 y - B u0 (next y) else if u = rowOf d then B (rowOf d) (next y) - B (rowOf d) y else 0) =
          B u0 y - B u0 (next y) := by
        rw [Finset.filter_eq' Finset.univ u0]; simp
      have h2 : ∑ u ∈ Finset.univ.filter (fun u => u ≠ u0),
          (if u = u0 then B u0 y - B u0 (next y) else if u = rowOf d then B (rowOf d) (next y) - B (rowOf d) y else 0) =
          B (rowOf d) (next y) - B (rowOf d) y := by
        have hcongr : ∑ u ∈ Finset.univ.filter (fun u => u ≠ u0),
            (if u = u0 then B u0 y - B u0 (next y) else if u = rowOf d then B (rowOf d) (next y) - B (rowOf d) y else 0) =
            ∑ u ∈ Finset.univ.filter (fun u => u ≠ u0), if u = rowOf d then B (rowOf d) (next y) - B (rowOf d) y else 0 :=
          Finset.sum_congr rfl (fun u hu => by simp [(Finset.mem_filter.mp hu).2])
        rw [hcongr, Finset.sum_ite_eq']
        have hmem : rowOf d ∈ Finset.univ.filter (fun u : X => u ≠ u0) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrowOf_ne0 d⟩
        simp only [hmem, ↓reduceIte]
      rw [h1, h2]
      ring
    have hosc : ∀ d : Fin (N - 1), ∀ y1 y2 : X,
        (B u0 y1 - B (rowOf d) y1) - (B u0 y2 - B (rowOf d) y2) ≤ (N : ℝ) * h := by
      intro d
      exact diff_le_of_cycle_bound hN_pos (fun y => B u0 y - B (rowOf d) y)
        (fun y => score B (S d y) - mean B) (fun y => score B (T d y) - mean B) h
        (sum_eq_zero_of_uniform hN_pos (S d) (hS_cov d) B)
        (sum_eq_zero_of_uniform hN_pos (T d) (hT_cov d) B)
        (hS_bound d) (hT_bound d)
        (fun y => by rw [← hdiff_ST d y]; ring)
    let b : X → ℝ := fun y => B u0 y
    have hneX : (Finset.univ : Finset X).Nonempty := ⟨u0, Finset.mem_univ u0⟩
    let a : X → ℝ := fun x =>
      if hx : x = u0 then 0
      else ((Finset.univ.image (fun y => B x y - b y)).max' (hneX.image _) +
            (Finset.univ.image (fun y => B x y - b y)).min' (hneX.image _)) / 2
    have hab_bound : ∀ x y : X, |B x y - a x - b y| ≤ (N : ℝ) * h / 2 := by
      intro x y
      by_cases hx : x = u0
      · subst hx
        simp only [a, ↓reduceDIte, sub_zero, b, sub_self, abs_zero]
        have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith [mul_nonneg this hh]
      · simp only [a, hx, ↓reduceDIte]
        have hxpos : 0 < x.val := by
          by_contra h0; push Not at h0
          exact hx (Fin.ext (by dsimp only [u0]; omega))
        let d : Fin (N - 1) := ⟨x.val - 1, by have := x.isLt; omega⟩
        have hxd : rowOf d = x := Fin.ext (by dsimp only [rowOf, d]; omega)
        let img := Finset.univ.image (fun z : X => B x z - b z)
        have hmax_mem : img.max' (hneX.image _) ∈ img := Finset.max'_mem img _
        have hmin_mem : img.min' (hneX.image _) ∈ img := Finset.min'_mem img _
        rcases Finset.mem_image.mp hmax_mem with ⟨ymax, _, hymax⟩
        rcases Finset.mem_image.mp hmin_mem with ⟨ymin, _, hymin⟩
        have hle_max : B x y - b y ≤ B x ymax - b ymax := by
          rw [hymax]; exact Finset.le_max' img _ (Finset.mem_image_of_mem _ (Finset.mem_univ y))
        have hmin_le : B x ymin - b ymin ≤ B x y - b y := by
          rw [hymin]; exact Finset.min'_le img _ (Finset.mem_image_of_mem _ (Finset.mem_univ y))
        have hgap : (B x ymax - b ymax) - (B x ymin - b ymin) ≤ (N : ℝ) * h := by
          have h1 := hosc d ymin ymax
          rw [hxd] at h1
          dsimp only [b]
          linarith
        rw [← hymax, ← hymin, abs_le]
        constructor <;> linarith
    refine ⟨⟨a, b, hab_bound⟩, ?_⟩
    intro G hG
    let C : X → X → ℝ := fun x y => B x y - a x - b y
    have hC0 : ∀ y : X, C u0 y = 0 := by
      intro y; dsimp only [C, a, b]; simp
    have hscore_eq : score B G - mean B =
        ∑ x : X, ∑ y : X, ((if G x y then (1 : ℝ) else 0) - (t : ℝ) / (N : ℝ)) * C x y := by
      have hG_ab : ∑ x : X, ∑ y : X, (if G x y then (a x + b y) else 0) =
          (t : ℝ) * (∑ x : X, a x) + (t : ℝ) * (∑ y : X, b y) := by
        have h1 : ∑ x : X, ∑ y : X, (if G x y then (a x + b y) else 0) =
            (∑ x : X, ∑ y : X, if G x y then a x else 0) +
            (∑ x : X, ∑ y : X, if G x y then b y else 0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun y _ => by split_ifs <;> ring)
        rw [h1]
        congr 1
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [← Finset.sum_filter, Finset.sum_const, hG.1 x, nsmul_eq_mul]
        · rw [Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [← Finset.sum_filter, Finset.sum_const, hG.2 y, nsmul_eq_mul]
      have hall_ab : ∑ x : X, ∑ y : X, (a x + b y) =
          (N : ℝ) * (∑ x : X, a x) + (N : ℝ) * (∑ y : X, b y) := by
        have h1 : ∑ x : X, ∑ y : X, (a x + b y) =
            (∑ x : X, ∑ _y : X, a x) + (∑ _x : X, ∑ y : X, b y) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun x _ => Finset.sum_add_distrib)
        rw [h1]
        congr 1
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun x _ => by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])
        · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN_pos)
      have hrhs : (∑ x : X, ∑ y : X, ((if G x y then (1 : ℝ) else 0) - (t : ℝ) / (N : ℝ)) * C x y) =
          (score B G - ∑ x : X, ∑ y : X, if G x y then (a x + b y) else 0) -
          (mean B - (t : ℝ) / (N : ℝ) * ∑ x : X, ∑ y : X, (a x + b y)) := by
        dsimp only [score, mean, C]
        have h1 : ∀ x : X, (∑ y : X, ((if G x y then (1 : ℝ) else 0) - (t : ℝ) / (N : ℝ)) * (B x y - a x - b y)) =
            ((∑ y : X, if G x y then B x y else 0) - ∑ y : X, if G x y then (a x + b y) else 0) -
            (t : ℝ) / (N : ℝ) * ((∑ y : X, B x y) - ∑ y : X, (a x + b y)) := by
          intro x
          rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun y _ => by split_ifs <;> ring)
        rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_sub_distrib, mul_sub]
      rw [hrhs, hG_ab, hall_ab]
      field_simp [hNne]
      ring
    rw [hscore_eq]
    have hrow_abs : ∀ x : X,
        |∑ y : X, ((if G x y then (1 : ℝ) else 0) - (t : ℝ) / (N : ℝ)) * C x y| ≤
        if x = u0 then 0 else ((t * (N - t) : ℕ) : ℝ) * h := by
      intro x
      by_cases hx : x = u0
      · subst hx
        simp only [↓reduceIte]
        have h0 : ∑ y : X, ((if G u0 y then (1 : ℝ) else 0) - (t : ℝ) / (N : ℝ)) * C u0 y = 0 :=
          Finset.sum_eq_zero (fun y _ => by rw [hC0 y, mul_zero])
        rw [h0, abs_zero]
      · simp only [hx, ↓reduceIte]
        have h1 : |∑ y : X, ((if G x y then (1 : ℝ) else 0) - (t : ℝ) / (N : ℝ)) * C x y| ≤
            ∑ y : X, |((if G x y then (1 : ℝ) else 0) - (t : ℝ) / (N : ℝ)) * C x y| :=
          Finset.abs_sum_le_sum_abs _ _
        have h2 : ∑ y : X, |((if G x y then (1 : ℝ) else 0) - (t : ℝ) / (N : ℝ)) * C x y| ≤
            ∑ y : X, |(if G x y then (1 : ℝ) else 0) - (t : ℝ) / (N : ℝ)| * ((N : ℝ) * h / 2) := by
          refine Finset.sum_le_sum (fun y _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hab_bound x y) (abs_nonneg _)
        have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hN_pos)
        have hNposR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN_pos
        have h3 : (∑ y : X, |(if G x y then (1 : ℝ) else 0) - (t : ℝ) / (N : ℝ)|) =
            2 * ((t * (N - t) : ℕ) : ℝ) / (N : ℝ) := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun y : X => G x y = true)]
          have hpos_val : (0 : ℝ) ≤ 1 - (t : ℝ) / (N : ℝ) := by
            have : (t : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr (le_of_lt htN)
            have : (t : ℝ) / (N : ℝ) ≤ 1 := (div_le_one hNposR).mpr this
            linarith
          have hneg_val : (0 : ℝ) ≤ (t : ℝ) / (N : ℝ) := div_nonneg (Nat.cast_nonneg t) (le_of_lt hNposR)
          have ha : ∑ y ∈ Finset.univ.filter (fun y => G x y = true),
              |(if G x y then (1 : ℝ) else 0) - (t : ℝ) / (N : ℝ)| =
              (t : ℝ) * (1 - (t : ℝ) / (N : ℝ)) := by
            have hcongr : ∑ y ∈ Finset.univ.filter (fun y => G x y = true),
                |(if G x y then (1 : ℝ) else 0) - (t : ℝ) / (N : ℝ)| =
                ∑ _y ∈ Finset.univ.filter (fun y => G x y = true), (1 - (t : ℝ) / (N : ℝ)) :=
              Finset.sum_congr rfl (fun y hy => by
                rw [(Finset.mem_filter.mp hy).2]; simp [abs_of_nonneg hpos_val])
            rw [hcongr, Finset.sum_const, hG.1 x, nsmul_eq_mul]
          have hb : ∑ y ∈ Finset.univ.filter (fun y => ¬ G x y = true),
              |(if G x y then (1 : ℝ) else 0) - (t : ℝ) / (N : ℝ)| =
              ((N - t : ℕ) : ℝ) * ((t : ℝ) / (N : ℝ)) := by
            have hcongr : ∑ y ∈ Finset.univ.filter (fun y => ¬ G x y = true),
                |(if G x y then (1 : ℝ) else 0) - (t : ℝ) / (N : ℝ)| =
                ∑ _y ∈ Finset.univ.filter (fun y => ¬ G x y = true), ((t : ℝ) / (N : ℝ)) :=
              Finset.sum_congr rfl (fun y hy => by
                have hnf : G x y = false := Bool.eq_false_iff.mpr (Finset.mem_filter.mp hy).2
                rw [hnf]; simp [abs_neg, abs_of_nonneg hneg_val])
            have hcard_not : (Finset.univ.filter (fun y : X => ¬ G x y = true)).card = N - t := by
              have hsum_c := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset X))
                (p := fun y => G x y = true)
              rw [hG.1 x, Finset.card_univ, Fintype.card_fin] at hsum_c
              omega
            rw [hcongr, Finset.sum_const, hcard_not, nsmul_eq_mul]
          rw [ha, hb, Nat.cast_mul, Nat.cast_sub (le_of_lt htN)]
          field_simp [hNne]
          ring
        calc |∑ y : X, ((if G x y then (1 : ℝ) else 0) - (t : ℝ) / (N : ℝ)) * C x y|
            ≤ ∑ y : X, |(if G x y then (1 : ℝ) else 0) - (t : ℝ) / (N : ℝ)| * ((N : ℝ) * h / 2) := le_trans h1 h2
          _ = (∑ y : X, |(if G x y then (1 : ℝ) else 0) - (t : ℝ) / (N : ℝ)|) * ((N : ℝ) * h / 2) := by
              rw [Finset.sum_mul]
          _ = (2 * ((t * (N - t) : ℕ) : ℝ) / (N : ℝ)) * ((N : ℝ) * h / 2) := by rw [h3]
          _ = ((t * (N - t) : ℕ) : ℝ) * h := by field_simp [hNne]
    calc |∑ x : X, ∑ y : X, ((if G x y then (1 : ℝ) else 0) - (t : ℝ) / (N : ℝ)) * C x y|
        ≤ ∑ x : X, |∑ y : X, ((if G x y then (1 : ℝ) else 0) - (t : ℝ) / (N : ℝ)) * C x y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x : X, if x = u0 then 0 else ((t * (N - t) : ℕ) : ℝ) * h :=
          Finset.sum_le_sum (fun x _ => hrow_abs x)
      _ = (((N - 1) * t * (N - t) : ℕ) : ℝ) * h := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : X => x = u0)]
          have h1 : ∑ x ∈ Finset.univ.filter (fun x => x = u0),
              (if x = u0 then (0 : ℝ) else ((t * (N - t) : ℕ) : ℝ) * h) = 0 :=
            Finset.sum_eq_zero (fun x hx => by simp [(Finset.mem_filter.mp hx).2])
          have h2 : ∑ x ∈ Finset.univ.filter (fun x => x ≠ u0),
              (if x = u0 then (0 : ℝ) else ((t * (N - t) : ℕ) : ℝ) * h) =
              ((N - 1 : ℕ) : ℝ) * (((t * (N - t) : ℕ) : ℝ) * h) := by
            have hcongr : ∑ x ∈ Finset.univ.filter (fun x => x ≠ u0),
                (if x = u0 then (0 : ℝ) else ((t * (N - t) : ℕ) : ℝ) * h) =
                ∑ _x ∈ Finset.univ.filter (fun x => x ≠ u0), (((t * (N - t) : ℕ) : ℝ) * h) :=
              Finset.sum_congr rfl (fun x hx => by simp [(Finset.mem_filter.mp hx).2])
            have hcard : (Finset.univ.filter (fun x : X => x ≠ u0)).card = N - 1 := by
              have hfilt : Finset.univ.filter (fun x : X => x ≠ u0) = Finset.univ.erase u0 := by
                ext x; simp [Finset.mem_erase]
              rw [hfilt, Finset.card_erase_of_mem (Finset.mem_univ u0), Finset.card_univ, Fintype.card_fin]
            rw [hcongr, Finset.sum_const, hcard, nsmul_eq_mul]
          rw [h1, zero_add, h2]
          push_cast
          ring
