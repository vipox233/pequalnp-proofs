import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_518_aux

private lemma sq_sum_le_card_mul_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 := by
  have hnn : (0 : ℝ) ≤ ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hexp : ∑ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 =
      2 * ((s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 - (∑ i ∈ s, f i) ^ 2) := by
    have h1 : ∀ i ∈ s, ∑ j ∈ s, (f i - f j) ^ 2 =
        (s.card : ℝ) * (f i) ^ 2 - 2 * f i * (∑ j ∈ s, f j) + ∑ j ∈ s, (f j) ^ 2 := by
      intro i _
      have hsq : ∀ j, (f i - f j) ^ 2 = (f i) ^ 2 - 2 * f i * f j + (f j) ^ 2 := fun j => by ring
      simp_rw [hsq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    ring
  linarith

private theorem solve_518 (u d q : Nat) (w : Fin u → Nat) (h : Fin d → Fin u → Fin q)
    (_hq : 0 < q)
    (huniv : ∀ x z : Fin u, x ≠ z →
      q * (Finset.univ.filter (fun s : Fin d => h s x = h s z)).card ≤ d) :
    let mass : ℝ := ∑ x : Fin u, (w x : ℝ)
    let load := fun (s : Fin d) (b : Fin q) =>
      ∑ x : Fin u, if h s x = b then (w x : ℝ) else 0
    (∑ s : Fin d, ∑ b : Fin q, |(q : ℝ) * load s b - mass|) ^ 2 ≤
      (d : ℝ) ^ 2 * (q : ℝ) ^ 2 * ((q : ℝ) - 1) * (∑ x : Fin u, (w x : ℝ) ^ 2) := by
  intro mass load
  have hsum_load : ∀ s : Fin d, ∑ b : Fin q, load s b = mass := by
    intro s
    dsimp only [load, mass]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simp
  have hsq_load : ∑ s : Fin d, ∑ b : Fin q, (load s b) ^ 2 =
      ∑ x : Fin u, ∑ z : Fin u,
        (w x : ℝ) * (w z : ℝ) * ((Finset.univ.filter (fun s : Fin d => h s x = h s z)).card : ℝ) := by
    have hinner : ∀ s : Fin d, ∑ b : Fin q, (load s b) ^ 2 =
        ∑ x : Fin u, ∑ z : Fin u, if h s x = h s z then (w x : ℝ) * (w z : ℝ) else 0 := by
      intro s
      have h1 : ∀ b : Fin q, (load s b) ^ 2 =
          ∑ x : Fin u, ∑ z : Fin u,
            if h s x = b ∧ h s z = b then (w x : ℝ) * (w z : ℝ) else 0 := by
        intro b
        rw [sq]
        dsimp only [load]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        split_ifs <;> simp_all
      simp_rw [h1]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hxz : h s x = h s z
      · simp only [hxz, ↓reduceIte]
        rw [Finset.sum_eq_single (h s z)]
        · simp
        · intro b _ hb; simp [hb.symm]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      · simp only [hxz, ↓reduceIte]
        apply Finset.sum_eq_zero
        intro b _
        have hnot : ¬ (h s x = b ∧ h s z = b) := fun ⟨h1, h2⟩ => hxz (h1.trans h2.symm)
        simp [hnot]
    simp_rw [hinner]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hpair_bound : (q : ℝ) * (∑ s : Fin d, ∑ b : Fin q, (load s b) ^ 2) ≤
      (d : ℝ) * ((q : ℝ) - 1) * (∑ x : Fin u, (w x : ℝ) ^ 2) + (d : ℝ) * mass ^ 2 := by
    rw [hsq_load, Finset.mul_sum]
    have hterm : ∀ x : Fin u,
        (q : ℝ) * ∑ z : Fin u, (w x : ℝ) * (w z : ℝ) *
          ((Finset.univ.filter (fun s : Fin d => h s x = h s z)).card : ℝ) ≤
        (d : ℝ) * ((q : ℝ) - 1) * (w x : ℝ) ^ 2 + (d : ℝ) * (w x : ℝ) * mass := by
      intro x
      rw [Finset.mul_sum]
      have hrhs : (d : ℝ) * ((q : ℝ) - 1) * (w x : ℝ) ^ 2 + (d : ℝ) * (w x : ℝ) * mass =
          ∑ z : Fin u, (if x = z then (q : ℝ) * (d : ℝ) * (w x : ℝ) ^ 2
                        else (d : ℝ) * ((w x : ℝ) * (w z : ℝ))) := by
        have hsplit : ∑ z : Fin u, (if x = z then (q : ℝ) * (d : ℝ) * (w x : ℝ) ^ 2
                        else (d : ℝ) * ((w x : ℝ) * (w z : ℝ))) =
            ∑ z : Fin u, ((if x = z then (d : ℝ) * ((q : ℝ) - 1) * (w x : ℝ) ^ 2 else 0) +
                          (d : ℝ) * ((w x : ℝ) * (w z : ℝ))) := by
          apply Finset.sum_congr rfl
          intro z _
          by_cases hxz : x = z
          · subst hxz; simp; ring
          · simp [hxz]
        rw [hsplit, Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        congr 1
        dsimp only [mass]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _; ring
      rw [hrhs]
      apply Finset.sum_le_sum
      intro z _
      by_cases hxz : x = z
      · subst hxz
        simp only [↓reduceIte, Finset.filter_true, Finset.card_univ, Fintype.card_fin]
        nlinarith
      · simp only [hxz, ↓reduceIte]
        have hnat : ((q * (Finset.univ.filter (fun s : Fin d => h s x = h s z)).card : Nat) : ℝ) ≤ (d : ℝ) :=
          Nat.cast_le.mpr (huniv x z hxz)
        push_cast at hnat
        have hwx : 0 ≤ (w x : ℝ) * (w z : ℝ) := by positivity
        nlinarith
    calc ∑ x : Fin u, (q : ℝ) * ∑ z : Fin u, (w x : ℝ) * (w z : ℝ) *
            ((Finset.univ.filter (fun s : Fin d => h s x = h s z)).card : ℝ)
        ≤ ∑ x : Fin u, ((d : ℝ) * ((q : ℝ) - 1) * (w x : ℝ) ^ 2 + (d : ℝ) * (w x : ℝ) * mass) :=
          Finset.sum_le_sum (fun x _ => hterm x)
      _ = (d : ℝ) * ((q : ℝ) - 1) * (∑ x : Fin u, (w x : ℝ) ^ 2) + (d : ℝ) * mass ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 1
          rw [← Finset.sum_mul, ← Finset.mul_sum]
          change (d : ℝ) * mass * mass = (d : ℝ) * mass ^ 2
          ring
  have hvar : ∑ s : Fin d, ∑ b : Fin q, ((q : ℝ) * load s b - mass) ^ 2 ≤
      (d : ℝ) * (q : ℝ) * ((q : ℝ) - 1) * (∑ x : Fin u, (w x : ℝ) ^ 2) := by
    have hexp : ∑ s : Fin d, ∑ b : Fin q, ((q : ℝ) * load s b - mass) ^ 2 =
        (q : ℝ) ^ 2 * (∑ s : Fin d, ∑ b : Fin q, (load s b) ^ 2) - (d : ℝ) * (q : ℝ) * mass ^ 2 := by
      have h1 : ∀ s : Fin d, ∑ b : Fin q, ((q : ℝ) * load s b - mass) ^ 2 =
          (q : ℝ) ^ 2 * (∑ b : Fin q, (load s b) ^ 2) - (q : ℝ) * mass ^ 2 := by
        intro s
        have hsq : ∀ b : Fin q, ((q : ℝ) * load s b - mass) ^ 2 =
            (q : ℝ) ^ 2 * (load s b) ^ 2 - 2 * (q : ℝ) * mass * load s b + mass ^ 2 := by
          intro b; ring
        simp_rw [hsq, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum_load s]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      simp_rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hexp]
    have hq_nn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
    nlinarith
  have hcs : (∑ s : Fin d, ∑ b : Fin q, |(q : ℝ) * load s b - mass|) ^ 2 ≤
      ((d * q : Nat) : ℝ) * ∑ s : Fin d, ∑ b : Fin q, |(q : ℝ) * load s b - mass| ^ 2 := by
    have hpair : (∑ p : Fin d × Fin q, |(q : ℝ) * load p.1 p.2 - mass|) ^ 2 ≤
        ((Finset.univ : Finset (Fin d × Fin q)).card : ℝ) *
          ∑ p : Fin d × Fin q, |(q : ℝ) * load p.1 p.2 - mass| ^ 2 :=
      sq_sum_le_card_mul_sum_sq Finset.univ (fun p : Fin d × Fin q => |(q : ℝ) * load p.1 p.2 - mass|)
    simp only [Fintype.sum_prod_type, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hpair
    exact hpair
  have habs_sq : ∑ s : Fin d, ∑ b : Fin q, |(q : ℝ) * load s b - mass| ^ 2 =
      ∑ s : Fin d, ∑ b : Fin q, ((q : ℝ) * load s b - mass) ^ 2 := by
    simp only [sq_abs]
  rw [habs_sq] at hcs
  have hdq_nn : (0 : ℝ) ≤ ((d * q : Nat) : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hvar hdq_nn
  have hfin : ((d * q : Nat) : ℝ) * ((d : ℝ) * (q : ℝ) * ((q : ℝ) - 1) * (∑ x : Fin u, (w x : ℝ) ^ 2)) =
      (d : ℝ) ^ 2 * (q : ℝ) ^ 2 * ((q : ℝ) - 1) * (∑ x : Fin u, (w x : ℝ) ^ 2) := by
    push_cast; ring
  linarith

end PEqualNP.Outside.L_lib_518_aux

theorem PEqualNP.Outside.L_lib_518 : ∀ (u d q : Nat) (w : Fin u → ℕ) (h : Fin d → Fin u → Fin q), 0 < q →
  (∀ x z : Fin u, x ≠ z →
    q * (Finset.univ.filter (fun s : Fin d => h s x = h s z)).card ≤ d) →
  let mass : ℝ := ∑ x : Fin u, (w x : ℝ)
  let load := fun (s : Fin d) (b : Fin q) =>
    ∑ x : Fin u, if h s x = b then (w x : ℝ) else 0
  (∑ s : Fin d, ∑ b : Fin q, |(q : ℝ)*load s b-mass|)^2 ≤
    (d : ℝ)^2*(q : ℝ)^2*((q : ℝ)-1)*(∑ x : Fin u, (w x : ℝ)^2) := by
  intro u d q w h hq huniv
  exact PEqualNP.Outside.L_lib_518_aux.solve_518 u d q w h hq huniv
