import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_531_aux

private lemma sum_val_ge_prefix {m : ℕ} (k : Fin m) (T : Finset (Fin m))
    (hcard : T.card = k.val + 1) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ≤ k), (i.val + 1 : ℝ) ≤
      ∑ i ∈ T, (i.val + 1 : ℝ) := by
  let I : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => i ≤ k)
  have hI_card : I.card = k.val + 1 := by
    have hbij : I.card = (Finset.univ : Finset (Fin (k.val + 1))).card := by
      apply Finset.card_bij (fun i hi => ⟨i.val, Nat.lt_succ_of_le (Finset.mem_filter.mp hi).2⟩)
      · intro _ _; exact Finset.mem_univ _
      · intro a _ b _ h; exact Fin.ext (congrArg (Fin.val : Fin (k.val + 1) → ℕ) h)
      · intro j _
        refine ⟨⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩, ?_, ?_⟩
        · simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Nat.le_of_lt_succ j.isLt
        · ext; rfl
    simpa using hbij
  have hsdiff_card : (I \ T).card = (T \ I).card := by
    have h1 : (I ∩ T).card + (I \ T).card = I.card := Finset.card_inter_add_card_sdiff I T
    have h2 : (T ∩ I).card + (T \ I).card = T.card := Finset.card_inter_add_card_sdiff T I
    rw [Finset.inter_comm] at h2
    omega
  have hI_split : ∑ i ∈ I, (i.val + 1 : ℝ) =
      (∑ i ∈ I ∩ T, (i.val + 1 : ℝ)) + ∑ i ∈ I \ T, (i.val + 1 : ℝ) := by
    have hd : Disjoint (I ∩ T) (I \ T) :=
      Finset.disjoint_left.mpr (fun x h1 h2 => (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2)
    have hu : (I ∩ T) ∪ (I \ T) = I := by ext x; by_cases hx : x ∈ T <;> simp [hx]
    rw [← Finset.sum_union hd, hu]
  have hT_split : ∑ i ∈ T, (i.val + 1 : ℝ) =
      (∑ i ∈ I ∩ T, (i.val + 1 : ℝ)) + ∑ i ∈ T \ I, (i.val + 1 : ℝ) := by
    have hd : Disjoint (I ∩ T) (T \ I) :=
      Finset.disjoint_left.mpr (fun x h1 h2 => (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).1)
    have hu : (I ∩ T) ∪ (T \ I) = T := by ext x; by_cases hx : x ∈ I <;> simp [hx]
    rw [← Finset.sum_union hd, hu]
  have hle1 : ∑ i ∈ I \ T, (i.val + 1 : ℝ) ≤ ((I \ T).card : ℝ) * (k.val + 1 : ℝ) := by
    calc
      ∑ i ∈ I \ T, (i.val + 1 : ℝ)
          ≤ ∑ _i ∈ I \ T, (k.val + 1 : ℝ) := by
            apply Finset.sum_le_sum
            intro i hi
            have hiI : i ≤ k := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).2
            have hi_nat : i.val ≤ k.val := hiI
            exact_mod_cast Nat.add_le_add_right hi_nat 1
      _ = ((I \ T).card : ℝ) * (k.val + 1 : ℝ) := by simp; ring
  have hle2 : ((T \ I).card : ℝ) * (k.val + 1 : ℝ) ≤ ∑ i ∈ T \ I, (i.val + 1 : ℝ) := by
    calc
      ((T \ I).card : ℝ) * (k.val + 1 : ℝ)
          = ∑ _i ∈ T \ I, (k.val + 1 : ℝ) := by simp; ring
      _ ≤ ∑ i ∈ T \ I, (i.val + 1 : ℝ) := by
            apply Finset.sum_le_sum
            intro i hi
            have hni : i ∉ I := (Finset.mem_sdiff.mp hi).2
            have hgt : k.val < i.val := by
              by_contra hle
              apply hni
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, Nat.le_of_not_lt hle⟩
            have hnat : k.val + 1 ≤ i.val + 1 := by omega
            exact_mod_cast hnat
  have hcardR : ((I \ T).card : ℝ) = ((T \ I).card : ℝ) := by exact_mod_cast hsdiff_card
  change ∑ i ∈ I, (i.val + 1 : ℝ) ≤ ∑ i ∈ T, (i.val + 1 : ℝ)
  rw [hcardR] at hle1
  linarith

private lemma telescoping_antitone {m : ℕ} (p : Fin m → ℝ) (i : Fin m) :
    let step : Fin m → ℝ := fun k =>
      if hk : k.val + 1 < m then p k - p ⟨k.val + 1, hk⟩ else p k
    p i = ∑ k ∈ Finset.univ.filter (fun k : Fin m => i ≤ k), step k := by
  intro step
  have hind : ∀ d : ℕ, ∀ (j : Fin m), m - 1 - j.val = d →
      p j = ∑ k ∈ Finset.univ.filter (fun k : Fin m => j ≤ k), step k := by
    intro d
    induction d with
    | zero =>
      intro j hj
      have hj_last : j.val + 1 = m := by omega
      have hfilt : Finset.univ.filter (fun k : Fin m => j ≤ k) = {j} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hjk
          apply Fin.ext
          have : j.val ≤ k.val := hjk
          have := k.isLt
          omega
        · rintro rfl; exact le_refl _
      rw [hfilt, Finset.sum_singleton]
      have hnot : ¬ j.val + 1 < m := by omega
      simp [step, hnot]
    | succ d ih =>
      intro j hj
      have hlt : j.val + 1 < m := by omega
      let j' : Fin m := ⟨j.val + 1, hlt⟩
      have hj' : m - 1 - j'.val = d := by dsimp [j']; omega
      have hih := ih j' hj'
      have hsplit : Finset.univ.filter (fun k : Fin m => j ≤ k) =
          insert j (Finset.univ.filter (fun k : Fin m => j' ≤ k)) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hjk
          by_cases heq : k = j
          · exact Or.inl heq
          · right
            have h1 : j.val ≤ k.val := hjk
            have h2 : k.val ≠ j.val := fun h => heq (Fin.ext h)
            change j.val + 1 ≤ k.val
            omega
        · rintro (rfl | hk)
          · exact le_refl _
          · exact le_trans (show j ≤ j' from Nat.le_succ j.val) hk
      have hnotmem : j ∉ Finset.univ.filter (fun k : Fin m => j' ≤ k) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change ¬ (j.val + 1 ≤ j.val)
        omega
      rw [hsplit, Finset.sum_insert hnotmem, ← hih]
      simp only [step, hlt, ↓reduceDIte]
      ring
  exact hind (m - 1 - i.val) i rfl

end PEqualNP.Outside.L_lib_531_aux

open PEqualNP.Outside.L_lib_531_aux in
theorem PEqualNP.Outside.L_lib_531 :
∀ (m : ℕ) (p : Fin m → ℝ),
  (∀ i, 0 < p i) → (∑ i, p i) = 1 →
  (∀ i j, i ≤ j → p j ≤ p i) →
  let G := ∑ i, (i.val+1 : ℝ)*p i
  let H := ∑ i : Fin m, 1/(i.val+1 : ℝ)
  let S := ∑ i, Real.sqrt (p i)
  (∀ perm : Equiv.Perm (Fin m), G ≤ ∑ i, (i.val+1 : ℝ)*p (perm i)) ∧
    S^2 ≤ G*H ∧ G ≤ S^2 := by
  intro m p hp hsum hanti
  dsimp only
  let G : ℝ := ∑ i : Fin m, (i.val + 1 : ℝ) * p i
  let H : ℝ := ∑ i : Fin m, 1 / (i.val + 1 : ℝ)
  let S : ℝ := ∑ i : Fin m, Real.sqrt (p i)
  refine ⟨?_, ?_, ?_⟩
  · intro perm
    let step : Fin m → ℝ := fun k =>
      if hk : k.val + 1 < m then p k - p ⟨k.val + 1, hk⟩ else p k
    have hstep_nonneg : ∀ k : Fin m, 0 ≤ step k := by
      intro k
      by_cases hk : k.val + 1 < m
      · simp only [step, hk, ↓reduceDIte]
        have hle : p ⟨k.val + 1, hk⟩ ≤ p k := hanti k ⟨k.val + 1, hk⟩ (Nat.le_succ k.val)
        linarith
      · simp only [step, hk, ↓reduceDIte]
        exact le_of_lt (hp k)
    have hrewrite : ∀ f : Equiv.Perm (Fin m),
        ∑ i : Fin m, (i.val + 1 : ℝ) * p (f i) =
        ∑ k : Fin m, step k * ∑ i ∈ Finset.univ.filter (fun i : Fin m => f i ≤ k), (i.val + 1 : ℝ) := by
      intro f
      calc
        ∑ i : Fin m, (i.val + 1 : ℝ) * p (f i)
            = ∑ i : Fin m, (i.val + 1 : ℝ) *
                ∑ k ∈ Finset.univ.filter (fun k : Fin m => f i ≤ k), step k := by
                refine Finset.sum_congr rfl (fun i _ => by rw [telescoping_antitone p (f i)])
        _ = ∑ i : Fin m, ∑ k : Fin m,
              if f i ≤ k then (i.val + 1 : ℝ) * step k else 0 := by
                refine Finset.sum_congr rfl ?_
                intro i _
                rw [Finset.mul_sum, Finset.sum_filter]
        _ = ∑ k : Fin m, ∑ i : Fin m,
              if f i ≤ k then (i.val + 1 : ℝ) * step k else 0 := Finset.sum_comm
        _ = ∑ k : Fin m, step k * ∑ i ∈ Finset.univ.filter (fun i : Fin m => f i ≤ k), (i.val + 1 : ℝ) := by
                refine Finset.sum_congr rfl ?_
                intro k _
                rw [Finset.mul_sum, Finset.sum_filter]
                refine Finset.sum_congr rfl (fun i _ => by split_ifs <;> ring)
    have hG_eq : ∑ i : Fin m, (i.val + 1 : ℝ) * p i = ∑ k : Fin m, step k *
        ∑ i ∈ Finset.univ.filter (fun i : Fin m => i ≤ k), (i.val + 1 : ℝ) :=
      hrewrite (Equiv.refl (Fin m))
    rw [hG_eq, hrewrite perm]
    apply Finset.sum_le_sum
    intro k _
    apply mul_le_mul_of_nonneg_left _ (hstep_nonneg k)
    apply sum_val_ge_prefix k
    have hbij : (Finset.univ.filter (fun i : Fin m => perm i ≤ k)).card =
        (Finset.univ : Finset (Fin (k.val + 1))).card := by
      apply Finset.card_bij (fun i hi => ⟨(perm i).val, Nat.lt_succ_of_le (Finset.mem_filter.mp hi).2⟩)
      · intro _ _; exact Finset.mem_univ _
      · intro a _ b _ heq
        exact perm.injective (Fin.ext (congrArg (Fin.val : Fin (k.val + 1) → ℕ) heq))
      · intro j _
        refine ⟨perm.symm ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
          exact Nat.le_of_lt_succ j.isLt
        · ext; simp
    simpa using hbij
  · have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m))
      (fun i : Fin m => Real.sqrt ((i.val + 1 : ℝ) * p i))
      (fun i : Fin m => 1 / Real.sqrt (i.val + 1 : ℝ))
    have hL : ∑ i : Fin m, Real.sqrt ((i.val + 1 : ℝ) * p i) * (1 / Real.sqrt (i.val + 1 : ℝ)) = S := by
      refine Finset.sum_congr rfl ?_
      intro i _
      have hi_pos : (0 : ℝ) < (i.val + 1 : ℝ) := by positivity
      have hsq_ne : Real.sqrt (i.val + 1 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hi_pos)
      rw [Real.sqrt_mul (le_of_lt hi_pos)]
      field_simp [hsq_ne]
    have hR1 : ∑ i : Fin m, (Real.sqrt ((i.val + 1 : ℝ) * p i)) ^ 2 = G := by
      refine Finset.sum_congr rfl ?_
      intro i _
      have hnn : 0 ≤ (i.val + 1 : ℝ) * p i := mul_nonneg (by positivity) (le_of_lt (hp i))
      exact Real.sq_sqrt hnn
    have hR2 : ∑ i : Fin m, (1 / Real.sqrt (i.val + 1 : ℝ)) ^ 2 = H := by
      refine Finset.sum_congr rfl ?_
      intro i _
      have hi_nn : (0 : ℝ) ≤ (i.val + 1 : ℝ) := by positivity
      rw [div_pow, one_pow, Real.sq_sqrt hi_nn]
    rw [hL, hR1, hR2] at hcs
    exact hcs
  · have hSsq : S ^ 2 = ∑ i : Fin m, ∑ j : Fin m, Real.sqrt (p i) * Real.sqrt (p j) := by
      dsimp only [S]
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
    change G ≤ S ^ 2
    rw [hSsq]
    apply Finset.sum_le_sum
    intro i _
    have hcard_le : (Finset.univ.filter (fun j : Fin m => j ≤ i)).card = i.val + 1 := by
      have hbij : (Finset.univ.filter (fun j : Fin m => j ≤ i)).card =
          (Finset.univ : Finset (Fin (i.val + 1))).card := by
        apply Finset.card_bij (fun j hj => ⟨j.val, Nat.lt_succ_of_le (Finset.mem_filter.mp hj).2⟩)
        · intro _ _; exact Finset.mem_univ _
        · intro a _ b _ h; exact Fin.ext (congrArg (Fin.val : Fin (i.val + 1) → ℕ) h)
        · intro k _
          refine ⟨⟨k.val, lt_of_lt_of_le k.isLt (Nat.succ_le_of_lt i.isLt)⟩, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact Nat.le_of_lt_succ k.isLt
          · ext; rfl
      simpa using hbij
    calc
      (i.val + 1 : ℝ) * p i
          = ((Finset.univ.filter (fun j : Fin m => j ≤ i)).card : ℝ) * p i := by
            rw [hcard_le]; push_cast; rfl
      _ = ∑ _j ∈ Finset.univ.filter (fun j : Fin m => j ≤ i), p i := by simp
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin m => j ≤ i), Real.sqrt (p i) * Real.sqrt (p j) := by
            apply Finset.sum_le_sum
            intro j hj
            have hji : j ≤ i := (Finset.mem_filter.mp hj).2
            have hpij : p i ≤ p j := hanti j i hji
            have hsq : Real.sqrt (p i) ≤ Real.sqrt (p j) := Real.sqrt_le_sqrt hpij
            calc
              p i = Real.sqrt (p i) * Real.sqrt (p i) := (Real.mul_self_sqrt (le_of_lt (hp i))).symm
              _ ≤ Real.sqrt (p i) * Real.sqrt (p j) :=
                  mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
      _ ≤ ∑ j : Fin m, Real.sqrt (p i) * Real.sqrt (p j) :=
            Finset.sum_le_univ_sum_of_nonneg (fun j => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
