import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_432

private lemma upper_bound (n d : ℕ) (hn : 1 ≤ n) (hd : n - 1 ≤ d) :
    ∃ A B : Fin d → Finset (Fin n),
      (∀ t, Disjoint (A t) (B t)) ∧
      ∀ i j : Fin n, i ≠ j → (Finset.univ.filter (fun s : Fin d =>
        (i ∈ A s ∧ j ∈ B s) ∨ (j ∈ A s ∧ i ∈ B s))).card = 1 := by
  let A : Fin d → Finset (Fin n) := fun t =>
    if h : t.1 < n - 1 then {⟨t.1, by omega⟩} else ∅
  let B : Fin d → Finset (Fin n) := fun t =>
    if t.1 < n - 1 then Finset.univ.filter (fun j : Fin n => t.1 < j.1) else ∅
  refine ⟨A, B, ?_, ?_⟩
  · intro t
    dsimp only [A, B]
    split_ifs with h
    · rw [Finset.disjoint_singleton_left]
      simp
    · exact Finset.disjoint_empty_left _
  · intro i j hij
    have hmin : min i.1 j.1 < n - 1 := by
      have hi := i.2
      have hj := j.2
      have hne : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
      omega
    let s0 : Fin d := ⟨min i.1 j.1, by omega⟩
    have hfilt :
        Finset.univ.filter (fun s : Fin d => (i ∈ A s ∧ j ∈ B s) ∨ (j ∈ A s ∧ i ∈ B s)) = {s0} := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro (⟨hiA, hjB⟩ | ⟨hjA, hiB⟩)
        · dsimp only [A, B] at hiA hjB
          split_ifs at hiA hjB with hs
          · simp only [Finset.mem_singleton] at hiA
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjB
            have his : i.1 = s.1 := congrArg Fin.val hiA
            apply Fin.ext
            show s.1 = min i.1 j.1
            omega
          · simp at hiA
        · dsimp only [A, B] at hjA hiB
          split_ifs at hjA hiB with hs
          · simp only [Finset.mem_singleton] at hjA
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiB
            have hjs : j.1 = s.1 := congrArg Fin.val hjA
            apply Fin.ext
            show s.1 = min i.1 j.1
            omega
          · simp at hjA
      · intro hs
        subst hs
        have hne : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · left
          dsimp only [A, B]
          rw [dite_eq_left hmin, ite_eq_left hmin]
          refine ⟨?_, ?_⟩
          · simp only [Finset.mem_singleton]
            apply Fin.ext
            show i.1 = min i.1 j.1
            omega
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            show min i.1 j.1 < j.1
            omega
        · right
          dsimp only [A, B]
          rw [dite_eq_left hmin, ite_eq_left hmin]
          refine ⟨?_, ?_⟩
          · simp only [Finset.mem_singleton]
            apply Fin.ext
            show j.1 = min i.1 j.1
            omega
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            show min i.1 j.1 < i.1
            omega
    rw [hfilt, Finset.card_singleton]

private lemma exists_nonzero_solution (n d : ℕ) (hlt : d + 1 < n)
    (A : Fin d → Finset (Fin n)) :
    ∃ x : Fin n → ℚ, x ≠ 0 ∧ (∑ i : Fin n, x i = 0) ∧ ∀ t : Fin d, ∑ i ∈ A t, x i = 0 := by
  let L : (Fin n → ℚ) →ₗ[ℚ] (Fin (d + 1) → ℚ) :=
    { toFun := fun x k => if hk : k.1 < d then ∑ i ∈ A ⟨k.1, hk⟩, x i else ∑ i : Fin n, x i
      map_add' := by
        intro x y
        funext k
        dsimp only [Pi.add_apply]
        split_ifs <;> exact Finset.sum_add_distrib
      map_smul' := by
        intro c x
        funext k
        dsimp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs <;> rw [Finset.mul_sum] }
  have hker_ne : LinearMap.ker L ≠ ⊥ := by
    intro hbot
    have hsum := LinearMap.finrank_range_add_finrank_ker L
    rw [hbot, finrank_bot, add_zero] at hsum
    have hle : Module.finrank ℚ (LinearMap.range L) ≤ Module.finrank ℚ (Fin (d + 1) → ℚ) :=
      Submodule.finrank_le _
    rw [Module.finrank_fin_fun] at hsum hle
    omega
  obtain ⟨x, hxmem, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  rw [LinearMap.mem_ker] at hxmem
  refine ⟨x, hxne, ?_, ?_⟩
  · have h := congrFun hxmem ⟨d, Nat.lt_succ_self d⟩
    simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, Nat.lt_irrefl, dite_false, Pi.zero_apply] using h
  · intro t
    have h := congrFun hxmem ⟨t.1, Nat.lt_succ_of_lt t.2⟩
    simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, t.2, dite_true, Fin.eta, Pi.zero_apply] using h

private lemma lower_bound (n d : ℕ) (hn : 1 ≤ n)
    (A B : Fin d → Finset (Fin n))
    (hdisj : ∀ t, Disjoint (A t) (B t))
    (hpart : ∀ i j : Fin n, i ≠ j → (Finset.univ.filter (fun s : Fin d =>
      (i ∈ A s ∧ j ∈ B s) ∨ (j ∈ A s ∧ i ∈ B s))).card = 1) :
    n - 1 ≤ d := by
  by_contra hnot
  have hlt : d + 1 < n := by omega
  obtain ⟨x, hxne, hxall, hxA⟩ := exists_nonzero_solution n d hlt A
  have htotal : (∑ i : Fin n, ∑ j : Fin n, x i * x j) = 0 := by
    rw [← Finset.sum_mul_sum, hxall, zero_mul]
  have hsplit :
      (∑ i : Fin n, ∑ j : Fin n, x i * x j) =
      (∑ i : Fin n, x i * x i) + (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then x i * x j else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hdiag : x i * x i = ∑ j : Fin n, if i = j then x i * x j else 0 := by
      simp
    rw [hdiag, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : i = j <;> simp [h]
  have hpair : ∀ i j : Fin n,
      (if i ≠ j then x i * x j else 0) =
      ∑ t : Fin d, ((if i ∈ A t ∧ j ∈ B t then x i * x j else 0) +
        (if j ∈ A t ∧ i ∈ B t then x i * x j else 0)) := by
    intro i j
    have hterm : ∀ t : Fin d,
        (if i ∈ A t ∧ j ∈ B t then x i * x j else 0) +
        (if j ∈ A t ∧ i ∈ B t then x i * x j else 0) =
        if (i ∈ A t ∧ j ∈ B t) ∨ (j ∈ A t ∧ i ∈ B t) then x i * x j else 0 := by
      intro t
      by_cases h1 : i ∈ A t ∧ j ∈ B t
      · have h2 : ¬ (j ∈ A t ∧ i ∈ B t) := fun h2 =>
          Finset.disjoint_left.mp (hdisj t) h1.1 h2.2
        simp [h1, h2]
      · by_cases h2 : j ∈ A t ∧ i ∈ B t <;> simp [h1, h2]
    simp_rw [hterm]
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_right (not_not.mpr rfl)]
      symm
      apply Finset.sum_eq_zero
      intro t _
      have hno : ¬ (i ∈ A t ∧ i ∈ B t) := fun h =>
        Finset.disjoint_left.mp (hdisj t) h.1 h.2
      simp [hno]
    · rw [ite_eq_left hij]
      rw [← Finset.sum_filter, Finset.sum_const, hpart i j hij, one_nsmul]
  have hS_zero : (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then x i * x j else 0) = 0 := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, if i ≠ j then x i * x j else 0)
          = ∑ i : Fin n, ∑ j : Fin n, ∑ t : Fin d,
              ((if i ∈ A t ∧ j ∈ B t then x i * x j else 0) +
               (if j ∈ A t ∧ i ∈ B t then x i * x j else 0)) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hpair i j
      _ = ∑ t : Fin d, ∑ i : Fin n, ∑ j : Fin n,
            ((if i ∈ A t ∧ j ∈ B t then x i * x j else 0) +
             (if j ∈ A t ∧ i ∈ B t then x i * x j else 0)) := by
            trans (∑ i : Fin n, ∑ t : Fin d, ∑ j : Fin n,
              ((if i ∈ A t ∧ j ∈ B t then x i * x j else 0) +
               (if j ∈ A t ∧ i ∈ B t then x i * x j else 0)))
            · exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
            · exact Finset.sum_comm
      _ = ∑ t : Fin d, 0 := by
            refine Finset.sum_congr rfl fun t _ => ?_
            simp_rw [Finset.sum_add_distrib]
            have h1 : (∑ i : Fin n, ∑ j : Fin n, if i ∈ A t ∧ j ∈ B t then x i * x j else 0) = 0 := by
              have hstep : ∀ i : Fin n,
                  (∑ j : Fin n, if i ∈ A t ∧ j ∈ B t then x i * x j else 0) =
                  if i ∈ A t then ∑ j ∈ B t, x i * x j else 0 := by
                intro i
                by_cases hi : i ∈ A t
                · simp [hi]
                · simp [hi]
              simp_rw [hstep, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
              rw [← Finset.sum_mul_sum, hxA t, zero_mul]
            have h2 : (∑ i : Fin n, ∑ j : Fin n, if j ∈ A t ∧ i ∈ B t then x i * x j else 0) = 0 := by
              have hstep : ∀ i : Fin n,
                  (∑ j : Fin n, if j ∈ A t ∧ i ∈ B t then x i * x j else 0) =
                  if i ∈ B t then ∑ j ∈ A t, x i * x j else 0 := by
                intro i
                by_cases hi : i ∈ B t
                · simp [hi]
                · simp [hi]
              simp_rw [hstep, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
              rw [← Finset.sum_mul_sum, hxA t, mul_zero]
            rw [h1, h2, add_zero]
      _ = 0 := by simp
  have hsq_zero : (∑ i : Fin n, x i * x i) = 0 := by
    rw [hS_zero, add_zero] at hsplit
    exact hsplit.symm.trans htotal
  have hex : ∃ i : Fin n, x i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hxne (funext hall)
  obtain ⟨i0, hi0⟩ := hex
  have hpos : (0 : ℚ) < ∑ i : Fin n, x i * x i :=
    Finset.sum_pos' (fun i _ => mul_self_nonneg (x i)) ⟨i0, Finset.mem_univ i0, mul_self_pos.mpr hi0⟩
  exact ne_of_gt hpos hsq_zero

end PEqualNP.Outside.L_lib_432

theorem PEqualNP.Outside.L_lib_432 :
    ∀ (n d : ℕ), 1 ≤ n →
      ((∃ A B : Fin d → Finset (Fin n),
        (∀ t, Disjoint (A t) (B t)) ∧
        ∀ i j : Fin n, i ≠ j → (Finset.univ.filter (fun s : Fin d =>
          (i ∈ A s ∧ j ∈ B s) ∨ (j ∈ A s ∧ i ∈ B s))).card = 1) ↔ n - 1 ≤ d) := by
  intro n d hn
  constructor
  · rintro ⟨A, B, hdisj, hpart⟩
    exact PEqualNP.Outside.L_lib_432.lower_bound n d hn A B hdisj hpart
  · intro hd
    exact PEqualNP.Outside.L_lib_432.upper_bound n d hn hd
