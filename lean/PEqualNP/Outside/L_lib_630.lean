import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_630_aux

def target {r : ℕ} (s : Fin r → Bool) : Bool :=
  decide (∀ j, s j = true)

def low {r : ℕ} (f : (Fin r → Bool) → Bool) : Prop :=
  ∃ T : Finset (Finset (Fin r)),
    (∀ mon ∈ T, mon.card < r) ∧ ∀ input,
      f input = (((T.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)

def errSet {r : ℕ} (f : (Fin r → Bool) → Bool) : Finset (Fin r → Bool) :=
  Finset.univ.filter (fun s => f s ≠ target s)

lemma even_card_mon_true {r : ℕ} (mon : Finset (Fin r)) (hcard : mon.card < r) :
    Even ((Finset.univ : Finset (Fin r → Bool)).filter (fun s => ∀ j ∈ mon, s j = true)).card := by
  have hex : ∃ j0 : Fin r, j0 ∉ mon := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset (Fin r)) ⊆ mon := fun j _ => hall j
    have hle := Finset.card_le_card hsub
    simp only [Finset.card_univ, Fintype.card_fin] at hle
    omega
  obtain ⟨j0, hj0⟩ := hex
  let S := (Finset.univ : Finset (Fin r → Bool)).filter (fun s => ∀ j ∈ mon, s j = true)
  let ST := S.filter (fun s => s j0 = true)
  let SF := S.filter (fun s => s j0 = false)
  have hdisj : Disjoint ST SF := by
    rw [Finset.disjoint_left]
    intro s h1 h2
    simp only [ST, SF, Finset.mem_filter] at h1 h2
    rw [h1.2] at h2
    exact Bool.noConfusion h2.2
  have hun : ST ∪ SF = S := by
    ext s
    simp only [ST, SF, Finset.mem_union, Finset.mem_filter]
    cases s j0 <;> simp
  have hbij : ST.card = SF.card := by
    refine Finset.card_bij (fun s _ => Function.update s j0 false) ?_ ?_ ?_
    · intro s hs
      simp only [ST, SF, S, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      refine ⟨fun j hj => ?_, by simp⟩
      have hne : j ≠ j0 := fun h => hj0 (h ▸ hj)
      rw [Function.update_of_ne hne]
      exact hs.1 j hj
    · intro s1 hs1 s2 hs2 heq
      simp only [ST, Finset.mem_filter] at hs1 hs2
      funext j
      by_cases hj : j = j0
      · subst hj
        rw [hs1.2, hs2.2]
      · have := congrFun heq j
        rwa [Function.update_of_ne hj, Function.update_of_ne hj] at this
    · intro s hs
      simp only [ST, SF, S, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      refine ⟨Function.update s j0 true, ⟨fun j hj => ?_, by simp⟩, ?_⟩
      · have hne : j ≠ j0 := fun h => hj0 (h ▸ hj)
        rw [Function.update_of_ne hne]
        exact hs.1 j hj
      · funext j
        by_cases hj : j = j0
        · subst hj
          simp [hs.2]
        · simp [Function.update_of_ne hj]
  have hsum : S.card = ST.card + SF.card := by
    rw [← hun, Finset.card_union_of_disjoint hdisj]
  rw [hsum, hbij]
  exact ⟨SF.card, rfl⟩

lemma nat_mod_two_eq_one_iff_zmod (n : ℕ) :
    ((n % 2 == 1) = true) ↔ (n : ZMod 2) = 1 := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
  have hcast : (n : ZMod 2) = ((n % 2 : ℕ) : ZMod 2) := by
    conv_lhs => rw [← Nat.div_add_mod n 2]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_mul, zero_add]
  rw [hcast]
  rcases h with h0 | h1
  · rw [h0]
    decide
  · rw [h1]
    decide

lemma bool_to_zmod_eq (b : Bool) (z : ZMod 2) :
    (b = true ↔ z = 1) → (if b = true then (1 : ZMod 2) else 0) = z := by
  intro h
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hne : z ≠ 1 := by
      intro hz
      have := h.mpr hz
      exact Bool.noConfusion this
    fin_cases z
    · rfl
    · exact absurd rfl hne
  · simp only [↓reduceIte]
    exact (h.mp rfl).symm

lemma low_imp_odd_errSet {r : ℕ} (f : (Fin r → Bool) → Bool) (hf : low f) :
    Odd (errSet f).card := by
  obtain ⟨T, hTlt, hTeq⟩ := hf
  have hsum_f : ∑ s : Fin r → Bool, (if f s = true then (1 : ZMod 2) else 0) = 0 := by
    have hpt : ∀ s : Fin r → Bool,
        (if f s = true then (1 : ZMod 2) else 0) =
          ∑ mon ∈ T, if ∀ j ∈ mon, s j = true then (1 : ZMod 2) else 0 := by
      intro s
      have hcard_z :
          ((T.filter (fun mon => ∀ j ∈ mon, s j = true)).card : ZMod 2) =
            ∑ mon ∈ T, if ∀ j ∈ mon, s j = true then (1 : ZMod 2) else 0 := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [← hcard_z]
      apply bool_to_zmod_eq
      rw [hTeq s]
      exact nat_mod_two_eq_one_iff_zmod _
    simp_rw [hpt]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun mon hmon => ?_)
    have hev := even_card_mon_true mon (hTlt mon hmon)
    have hcard_z :
        ∑ s : Fin r → Bool, (if ∀ j ∈ mon, s j = true then (1 : ZMod 2) else 0) =
          (((Finset.univ : Finset (Fin r → Bool)).filter (fun s => ∀ j ∈ mon, s j = true)).card : ZMod 2) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcard_z]
    rcases hev with ⟨k, hk⟩
    rw [hk]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := by decide
    have : (k : ZMod 2) + (k : ZMod 2) = (2 : ZMod 2) * (k : ZMod 2) := by ring
    rw [this, h2, zero_mul]
  have hsum_t : ∑ s : Fin r → Bool, (if target s = true then (1 : ZMod 2) else 0) = 1 := by
    rw [Finset.sum_eq_single (fun _ : Fin r => true)]
    · simp [target]
    · intro s _ hs
      have hnot : ¬ (∀ j, s j = true) := by
        intro hall
        exact hs (funext hall)
      simp [target, hnot]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hsum_err :
      ((errSet f).card : ZMod 2) =
        (∑ s : Fin r → Bool, if f s = true then (1 : ZMod 2) else 0) +
        (∑ s : Fin r → Bool, if target s = true then (1 : ZMod 2) else 0) := by
    rw [← Finset.sum_add_distrib]
    unfold errSet
    have hpt : ∀ s : Fin r → Bool,
        (if f s ≠ target s then (1 : ZMod 2) else 0) =
          (if f s = true then (1 : ZMod 2) else 0) + (if target s = true then (1 : ZMod 2) else 0) := by
      intro s
      cases f s <;> cases target s <;> decide
    have hcard_eq :
        ((Finset.univ.filter (fun s : Fin r → Bool => f s ≠ target s)).card : ZMod 2) =
          ∑ s : Fin r → Bool, if f s ≠ target s then (1 : ZMod 2) else 0 := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcard_eq]
    exact Finset.sum_congr rfl (fun s _ => hpt s)
  rw [hsum_f, hsum_t, zero_add] at hsum_err
  have hmod : (errSet f).card % 2 = 1 := by
    have := (nat_mod_two_eq_one_iff_zmod (errSet f).card).mpr hsum_err
    simpa using this
  exact Nat.odd_iff.mpr hmod

lemma odd_card_imp_low {r : ℕ} (E : Finset (Fin r → Bool)) (hE : Odd E.card) :
    ∃ f : (Fin r → Bool) → Bool, low f ∧ errSet f = E := by
  let f : (Fin r → Bool) → Bool := fun s => xor (decide (s ∈ E)) (target s)
  have herr : errSet f = E := by
    ext s
    simp only [errSet, Finset.mem_filter, Finset.mem_univ, true_and, f]
    by_cases hs : s ∈ E <;> cases target s <;> simp [hs]
  let Ftrue : Finset (Fin r → Bool) := Finset.univ.filter (fun s => f s = true)
  have hFtrue_even : (Ftrue.card : ZMod 2) = 0 := by
    have hsum_err :
        (E.card : ZMod 2) =
          (Ftrue.card : ZMod 2) +
          (∑ s : Fin r → Bool, if target s = true then (1 : ZMod 2) else 0) := by
      rw [← herr]
      have hc1 : ((errSet f).card : ZMod 2) = ∑ s : Fin r → Bool, if f s ≠ target s then (1 : ZMod 2) else 0 := by
        unfold errSet
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hc2 : (Ftrue.card : ZMod 2) = ∑ s : Fin r → Bool, if f s = true then (1 : ZMod 2) else 0 := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [hc1, hc2, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      cases f s <;> cases target s <;> decide
    have hsum_t : ∑ s : Fin r → Bool, (if target s = true then (1 : ZMod 2) else 0) = 1 := by
      rw [Finset.sum_eq_single (fun _ : Fin r => true)]
      · simp [target]
      · intro s _ hs
        have hnot : ¬ (∀ j, s j = true) := fun hall => hs (funext hall)
        simp [target, hnot]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hE1 : (E.card : ZMod 2) = 1 := by
      apply (nat_mod_two_eq_one_iff_zmod E.card).mp
      have hm := Nat.odd_iff.mp hE
      simp [hm]
    rw [hE1, hsum_t] at hsum_err
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have hcalc : (Ftrue.card : ZMod 2) = (Ftrue.card : ZMod 2) + 1 + 1 := by
      rw [add_assoc, h11, add_zero]
    rw [hcalc, ← hsum_err, h11]
  let T : Finset (Finset (Fin r)) :=
    Finset.univ.filter (fun mon =>
      ((Ftrue.filter (fun s0 => ∀ j, s0 j = true → j ∈ mon)).card : ZMod 2) = 1)
  have hTlt : ∀ mon ∈ T, mon.card < r := by
    intro mon hmon
    have hle : mon.card ≤ r := by
      simpa using Finset.card_le_univ mon
    by_contra hge
    have heq : mon.card = r := by omega
    have huniv : mon = Finset.univ := Finset.eq_univ_of_card mon (by simpa using heq)
    subst huniv
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, implies_true,
      Finset.filter_true] at hmon
    rw [hFtrue_even] at hmon
    exact absurd hmon (by decide)
  have hpair : ∀ (s0 input : Fin r → Bool),
      (∑ mon : Finset (Fin r),
        (if (∀ j, s0 j = true → j ∈ mon) ∧ (∀ j ∈ mon, input j = true) then (1 : ZMod 2) else 0)) =
      if input = s0 then 1 else 0 := by
    intro s0 input
    let A := Finset.univ.filter (fun j : Fin r => s0 j = true)
    let B := Finset.univ.filter (fun j : Fin r => input j = true)
    have hfilt :
        (Finset.univ.filter (fun mon : Finset (Fin r) =>
          (∀ j, s0 j = true → j ∈ mon) ∧ (∀ j ∈ mon, input j = true))) =
        Finset.univ.filter (fun mon : Finset (Fin r) => A ⊆ mon ∧ mon ⊆ B) := by
      ext mon
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.subset_iff, A, B]
    have hsum_eq :
        (∑ mon : Finset (Fin r),
          (if (∀ j, s0 j = true → j ∈ mon) ∧ (∀ j ∈ mon, input j = true) then (1 : ZMod 2) else 0)) =
        ((Finset.univ.filter (fun mon : Finset (Fin r) => A ⊆ mon ∧ mon ⊆ B)).card : ZMod 2) := by
      rw [← hfilt, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hsum_eq]
    by_cases heq : input = s0
    · subst heq
      have hAB : B = A := rfl
      have hsing :
          Finset.univ.filter (fun mon : Finset (Fin r) => A ⊆ mon ∧ mon ⊆ B) = {A} := by
        ext mon
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hAB]
        exact ⟨fun h => Finset.Subset.antisymm h.2 h.1, fun h => h ▸ ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩⟩
      rw [hsing]
      simp
    · simp only [heq, ↓reduceIte]
      by_cases hsub : A ⊆ B
      · have hneAB : A ≠ B := by
          intro hAB
          apply heq
          funext j
          have := Finset.ext_iff.mp hAB j
          simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at this
          cases h1 : input j <;> cases h2 : s0 j <;> simp_all
        have hex : ∃ j0 ∈ B, j0 ∉ A := by
          by_contra hall
          push Not at hall
          exact hneAB (Finset.Subset.antisymm hsub hall)
        obtain ⟨j0, hj0B, hj0A⟩ := hex
        let M := Finset.univ.filter (fun mon : Finset (Fin r) => A ⊆ mon ∧ mon ⊆ B)
        let M1 := M.filter (fun mon => j0 ∈ mon)
        let M0 := M.filter (fun mon => j0 ∉ mon)
        have hdisj : Disjoint M1 M0 := by
          rw [Finset.disjoint_left]
          intro mon h1 h2
          exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
        have hun : M1 ∪ M0 = M := by
          ext mon
          simp only [M1, M0, Finset.mem_union, Finset.mem_filter]
          tauto
        have hbij : M1.card = M0.card := by
          refine Finset.card_bij (fun mon _ => mon.erase j0) ?_ ?_ ?_
          · intro mon hmon
            simp only [M1, M0, M, Finset.mem_filter, Finset.mem_univ, true_and] at hmon ⊢
            refine ⟨⟨?_, Finset.Subset.trans (Finset.erase_subset _ _) hmon.1.2⟩, Finset.notMem_erase _ _⟩
            intro j hjA
            exact Finset.mem_erase.mpr ⟨fun h => hj0A (h ▸ hjA), hmon.1.1 hjA⟩
          · intro m1 hm1 m2 hm2 h
            simp only [M1, Finset.mem_filter] at hm1 hm2
            have := congrArg (insert j0) h
            rwa [Finset.insert_erase hm1.2, Finset.insert_erase hm2.2] at this
          · intro mon hmon
            simp only [M1, M0, M, Finset.mem_filter, Finset.mem_univ, true_and] at hmon ⊢
            refine ⟨insert j0 mon, ⟨⟨Finset.Subset.trans hmon.1.1 (Finset.subset_insert _ _),
              Finset.insert_subset_iff.mpr ⟨hj0B, hmon.1.2⟩⟩, Finset.mem_insert_self _ _⟩,
              Finset.erase_insert hmon.2⟩
        have hcard : M.card = M0.card + M0.card := by
          rw [← hun, Finset.card_union_of_disjoint hdisj, hbij]
        change (M.card : ZMod 2) = 0
        rw [hcard]
        push_cast
        have h2 : (2 : ZMod 2) = 0 := by decide
        have : (M0.card : ZMod 2) + (M0.card : ZMod 2) = (2 : ZMod 2) * (M0.card : ZMod 2) := by ring
        rw [this, h2, zero_mul]
      · have hemp : Finset.univ.filter (fun mon : Finset (Fin r) => A ⊆ mon ∧ mon ⊆ B) = ∅ := by
          ext mon
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          intro h
          exact hsub (Finset.Subset.trans h.1 h.2)
        rw [hemp]
        simp
  refine ⟨f, ⟨T, hTlt, fun input => ?_⟩, herr⟩
  have hcalc :
      ((T.filter (fun mon => ∀ j ∈ mon, input j = true)).card : ZMod 2) =
        if f input = true then (1 : ZMod 2) else 0 := by
    have h1 :
        ((T.filter (fun mon => ∀ j ∈ mon, input j = true)).card : ZMod 2) =
          ∑ mon : Finset (Fin r),
            (if ∀ j ∈ mon, input j = true then (1 : ZMod 2) else 0) *
            (∑ s0 ∈ Ftrue, if ∀ j, s0 j = true → j ∈ mon then (1 : ZMod 2) else 0) := by
      have hLHS :
          ((T.filter (fun mon => ∀ j ∈ mon, input j = true)).card : ZMod 2) =
            ∑ mon : Finset (Fin r),
              (if ∀ j ∈ mon, input j = true then (1 : ZMod 2) else 0) *
              (if mon ∈ T then (1 : ZMod 2) else 0) := by
        have hfeq :
            T.filter (fun mon => ∀ j ∈ mon, input j = true) =
              Finset.univ.filter (fun mon => mon ∈ T ∧ ∀ j ∈ mon, input j = true) := by
          ext mon
          simp
        have hstep :
            ((Finset.univ.filter (fun mon : Finset (Fin r) => mon ∈ T ∧ ∀ j ∈ mon, input j = true)).card : ZMod 2) =
              ∑ mon : Finset (Fin r), if mon ∈ T ∧ ∀ j ∈ mon, input j = true then (1 : ZMod 2) else 0 := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [hfeq, hstep]
        refine Finset.sum_congr rfl (fun mon _ => ?_)
        by_cases h1 : mon ∈ T <;> by_cases h2 : ∀ j ∈ mon, input j = true <;> simp [h1, h2]
      rw [hLHS]
      refine Finset.sum_congr rfl (fun mon _ => ?_)
      congr 1
      have hcard_mon :
          ((Ftrue.filter (fun s0 => ∀ j, s0 j = true → j ∈ mon)).card : ZMod 2) =
            ∑ s0 ∈ Ftrue, if ∀ j, s0 j = true → j ∈ mon then (1 : ZMod 2) else 0 := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      rw [← hcard_mon]
      have hmT : mon ∈ T ↔ ((Ftrue.filter (fun s0 => ∀ j, s0 j = true → j ∈ mon)).card : ZMod 2) = 1 := by
        simp [T]
      by_cases h : mon ∈ T
      · simp only [h, ↓reduceIte]
        exact (hmT.mp h).symm
      · simp only [h, ↓reduceIte]
        have hne : ((Ftrue.filter (fun s0 => ∀ j, s0 j = true → j ∈ mon)).card : ZMod 2) ≠ 1 :=
          fun h1 => h (hmT.mpr h1)
        generalize ((Ftrue.filter (fun s0 => ∀ j, s0 j = true → j ∈ mon)).card : ZMod 2) = z at hne ⊢
        fin_cases z
        · rfl
        · exact absurd rfl hne
    rw [h1]
    have h2 :
        ∑ mon : Finset (Fin r),
          (if ∀ j ∈ mon, input j = true then (1 : ZMod 2) else 0) *
          (∑ s0 ∈ Ftrue, if ∀ j, s0 j = true → j ∈ mon then (1 : ZMod 2) else 0) =
        ∑ s0 ∈ Ftrue,
          ∑ mon : Finset (Fin r),
            if (∀ j, s0 j = true → j ∈ mon) ∧ (∀ j ∈ mon, input j = true) then (1 : ZMod 2) else 0 := by
      have hin : ∀ mon : Finset (Fin r),
          (if ∀ j ∈ mon, input j = true then (1 : ZMod 2) else 0) *
            (∑ s0 ∈ Ftrue, if ∀ j, s0 j = true → j ∈ mon then (1 : ZMod 2) else 0) =
          ∑ s0 ∈ Ftrue,
            if (∀ j, s0 j = true → j ∈ mon) ∧ (∀ j ∈ mon, input j = true) then (1 : ZMod 2) else 0 := by
        intro mon
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun s0 _ => ?_)
        split_ifs <;> simp_all
      simp_rw [hin]
      exact Finset.sum_comm
    rw [h2]
    simp_rw [hpair]
    by_cases hin : input ∈ Ftrue
    · have hf_true : f input = true := (Finset.mem_filter.mp hin).2
      rw [Finset.sum_eq_single input]
      · simp [hf_true]
      · intro s0 _ hs0
        have hne : input ≠ s0 := Ne.symm hs0
        simp [hne]
      · intro h
        exact absurd hin h
    · have hf_false : f input ≠ true := fun ht => hin (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)
      simp only [hf_false]
      refine Finset.sum_eq_zero (fun s0 hs0 => ?_)
      have hne : input ≠ s0 := fun h => hin (h ▸ hs0)
      simp [hne]
  apply Bool.eq_iff_iff.mpr
  rw [nat_mod_two_eq_one_iff_zmod, hcalc]
  cases f input <;> decide

def occ (alphabet labels width : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin width → Fin alphabet)).filter (fun w =>
    ∀ k : Fin labels, ∃ j, (w j).val = k.val)).card

lemma occ_pos {alphabet labels width : ℕ} (h1 : labels ≤ alphabet) (h2 : labels ≤ width)
    (h3 : 0 < alphabet) : 0 < occ alphabet labels width := by
  unfold occ
  rw [Finset.card_pos]
  let w : Fin width → Fin alphabet := fun j =>
    if hj : j.val < labels then ⟨j.val, lt_of_lt_of_le hj h1⟩ else ⟨0, h3⟩
  refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, fun k => ?_⟩⟩
  refine ⟨⟨k.val, lt_of_lt_of_le k.isLt h2⟩, ?_⟩
  simp only [w, k.isLt, ↓reduceDIte]

def hitSets {S : Type} [Fintype S] [DecidableEq S] {m L : ℕ}
    (bad : Fin m → Fin L → Finset S) : ℕ :=
  ((Finset.univ : Finset (Fin m → S)).filter (fun w =>
    ∃ a : Fin L, ∀ i : Fin m, w i ∉ bad i a)).card

lemma hitSets_mono {S : Type} [Fintype S] [DecidableEq S] {m L : ℕ}
    (bad1 bad2 : Fin m → Fin L → Finset S)
    (hsub : ∀ i a, bad1 i a ⊆ bad2 i a) :
    hitSets bad2 ≤ hitSets bad1 := by
  refine Finset.card_le_card ?_
  intro w hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  rcases hw with ⟨a, ha⟩
  exact ⟨a, fun i hi => ha i (hsub i a hi)⟩

lemma hitSets_col_split {S : Type} [Fintype S] [DecidableEq S] {m L : ℕ}
    (bad : Fin m → Fin L → Finset S) (i0 : Fin m) :
    hitSets bad =
      ∑ w' : { i : Fin m // i ≠ i0 } → S,
        ((Finset.univ : Finset S).filter (fun x =>
          ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad j.1 a) ∧ x ∉ bad i0 a)).card := by
  let e : (Fin m → S) ≃ S × ({ i : Fin m // i ≠ i0 } → S) :=
    { toFun := fun w => (w i0, fun j => w j.1)
      invFun := fun p i => if h : i = i0 then p.1 else p.2 ⟨i, h⟩
      left_inv := fun w => by
        funext i
        by_cases h : i = i0
        · subst h
          simp
        · simp [h]
      right_inv := fun p => by
        refine Prod.ext (by simp) ?_
        funext j
        simp [j.2] }
  have h1 :
      hitSets bad =
        ((Finset.univ : Finset (S × ({ i : Fin m // i ≠ i0 } → S))).filter (fun p =>
          ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, p.2 j ∉ bad j.1 a) ∧ p.1 ∉ bad i0 a)).card := by
    unfold hitSets
    refine Finset.card_bij (fun w _ => e w) ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      rcases hw with ⟨a, ha⟩
      exact ⟨a, fun j => ha j.1, ha i0⟩
    · intro w1 _ w2 _ h
      exact e.injective h
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hp with ⟨a, ha1, ha2⟩
      refine ⟨a, fun i => ?_⟩
      by_cases hi : i = i0
      · subst hi
        simpa [e] using ha2
      · simpa [e, hi] using ha1 ⟨i, hi⟩
  rw [h1]
  have h2 :
      ((Finset.univ : Finset (S × ({ i : Fin m // i ≠ i0 } → S))).filter (fun p =>
        ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, p.2 j ∉ bad j.1 a) ∧ p.1 ∉ bad i0 a)).card =
      ∑ w' : { i : Fin m // i ≠ i0 } → S,
        ((Finset.univ : Finset S).filter (fun x =>
          ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad j.1 a) ∧ x ∉ bad i0 a)).card := by
    have hsum :
        ∀ (P : S → ({ i : Fin m // i ≠ i0 } → S) → Prop) [∀ x y, Decidable (P x y)],
          ((Finset.univ : Finset (S × ({ i : Fin m // i ≠ i0 } → S))).filter (fun p => P p.1 p.2)).card =
            ∑ w' : { i : Fin m // i ≠ i0 } → S, ((Finset.univ : Finset S).filter (fun x => P x w')).card := by
      intro P _
      have hL :
          ((Finset.univ : Finset (S × ({ i : Fin m // i ≠ i0 } → S))).filter (fun p => P p.1 p.2)).card =
            ∑ p : S × ({ i : Fin m // i ≠ i0 } → S), if P p.1 p.2 then 1 else 0 := by
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      have hR :
          ∑ w' : { i : Fin m // i ≠ i0 } → S, ((Finset.univ : Finset S).filter (fun x => P x w')).card =
            ∑ w' : { i : Fin m // i ≠ i0 } → S, ∑ x : S, if P x w' then 1 else 0 := by
        refine Finset.sum_congr rfl (fun w' _ => ?_)
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      rw [hL, hR, Fintype.sum_prod_type, Finset.sum_comm]
    exact hsum (fun x w' => ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad j.1 a) ∧ x ∉ bad i0 a)
  exact h2

lemma col_replace_le {S : Type} [Fintype S] [DecidableEq S] {m L : ℕ}
    (bad : Fin m → Fin L → Finset S) (i0 : Fin m)
    (hne : ∀ a : Fin L, (bad i0 a).Nonempty)
    (col' : Fin L → S) (hinj : Function.Injective col') :
    hitSets bad ≤ hitSets (Function.update bad i0 (fun a => {col' a})) := by
  rw [hitSets_col_split bad i0, hitSets_col_split (Function.update bad i0 (fun a => {col' a})) i0]
  refine Finset.sum_le_sum (fun w' _ => ?_)
  have hupd_ne : ∀ j : { i : Fin m // i ≠ i0 }, Function.update bad i0 (fun a => {col' a}) j.1 = bad j.1 :=
    fun j => Function.update_of_ne j.2 _ _
  have hupd_eq : Function.update bad i0 (fun a => {col' a}) i0 = (fun a => {col' a}) :=
    Function.update_self i0 _ _
  simp_rw [hupd_ne, hupd_eq]
  let Surv := Finset.univ.filter (fun a : Fin L => ∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad j.1 a)
  by_cases h0 : Surv.card = 0
  · have hemp : Surv = ∅ := Finset.card_eq_zero.mp h0
    have hL0 : ((Finset.univ : Finset S).filter (fun x =>
        ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad j.1 a) ∧ x ∉ bad i0 a)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro x _ ⟨a, ha, _⟩
      have haS : a ∈ Surv := Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩
      rw [hemp] at haS
      exact Finset.notMem_empty a haS
    omega
  · by_cases h1 : Surv.card = 1
    · obtain ⟨a, haS⟩ := Finset.card_eq_one.mp h1
      have ha_surv : ∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad j.1 a := by
        have : a ∈ Surv := by rw [haS]; exact Finset.mem_singleton_self a
        exact (Finset.mem_filter.mp this).2
      have honly : ∀ b : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad j.1 b) ↔ b = a := by
        intro b
        have : b ∈ Surv ↔ b = a := by rw [haS, Finset.mem_singleton]
        simpa [Surv] using this
      obtain ⟨s0, hs0⟩ := hne a
      have hLle : ((Finset.univ : Finset S).filter (fun x =>
          ∃ b : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad j.1 b) ∧ x ∉ bad i0 b)).card ≤
          Fintype.card S - 1 := by
        have hsub : (Finset.univ : Finset S).filter (fun x =>
            ∃ b : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad j.1 b) ∧ x ∉ bad i0 b) ⊆
            Finset.univ.erase s0 := by
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hx ⊢
          rcases hx with ⟨b, hb, hxb⟩
          have hba := (honly b).mp hb
          subst hba
          exact ⟨fun hxs => hxb (hxs ▸ hs0), trivial⟩
        have hc := Finset.card_le_card hsub
        simpa [Finset.card_erase_of_mem (Finset.mem_univ s0)] using hc
      have hReq : ((Finset.univ : Finset S).filter (fun x =>
          ∃ b : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad j.1 b) ∧ x ∉ ({col' b} : Finset S))).card =
          Fintype.card S - 1 := by
        have heq : (Finset.univ : Finset S).filter (fun x =>
            ∃ b : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad j.1 b) ∧ x ∉ ({col' b} : Finset S)) =
            Finset.univ.erase (col' a) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
            Finset.mem_singleton, honly, exists_eq_left, and_true]
        rw [heq]
        simp [Finset.card_erase_of_mem (Finset.mem_univ (col' a))]
      omega
    · have hge2 : 1 < Surv.card := by omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hge2
      have ha_surv := (Finset.mem_filter.mp ha).2
      have hb_surv := (Finset.mem_filter.mp hb).2
      have hReq : ((Finset.univ : Finset S).filter (fun x =>
          ∃ c : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad j.1 c) ∧ x ∉ ({col' c} : Finset S))).card =
          Fintype.card S := by
        have heq : (Finset.univ : Finset S).filter (fun x =>
            ∃ c : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad j.1 c) ∧ x ∉ ({col' c} : Finset S)) =
            Finset.univ := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, iff_true]
          by_cases hxa : x = col' a
          · refine ⟨b, hb_surv, ?_⟩
            intro hxb
            exact hab (hinj (hxa.symm.trans hxb))
          · exact ⟨a, ha_surv, hxa⟩
        rw [heq, Finset.card_univ]
      rw [hReq]
      exact Finset.card_le_univ _

lemma hitSets_injective_eq {S : Type} [Fintype S] [DecidableEq S] {m L q : ℕ}
    (hq : Fintype.card S = q) (hLq : L ≤ q)
    (tab : Fin m → Fin L → S) (hinj : ∀ i, Function.Injective (tab i)) :
    hitSets (fun i a => {tab i a}) = q ^ m - occ q L m := by
  have hex_e : ∀ i : Fin m, ∃ e : S ≃ Fin q, ∀ a : Fin L, (e (tab i a)).val = a.val := by
    intro i
    let img : Finset S := Finset.univ.image (tab i)
    let tgt : Finset (Fin q) := Finset.univ.filter (fun x : Fin q => x.val < L)
    have himg_card : img.card = L := by
      rw [Finset.card_image_of_injective _ (hinj i), Finset.card_univ, Fintype.card_fin]
    have htgt_card : tgt.card = L := by
      trans (Finset.univ : Finset (Fin L)).card
      · refine Finset.card_bij (t := (Finset.univ : Finset (Fin L)))
          (fun x hx => ⟨x.val, (Finset.mem_filter.mp hx).2⟩) (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ _ h => Fin.ext (congrArg (fun z : Fin L => z.val) h))
          (fun a _ => ⟨⟨a.val, lt_of_lt_of_le a.isLt hLq⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.isLt⟩, Fin.ext rfl⟩)
      · simp
    have hcomp_card :
        Fintype.card { s : S // s ∉ img } = Fintype.card { x : Fin q // x ∉ tgt } := by
      have h1 : (Finset.univ \ img).card = q - L := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hq, himg_card]
      have h2 : (Finset.univ \ tgt).card = q - L := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, htgt_card]
      have h1' : Fintype.card { s : S // s ∉ img } = (Finset.univ \ img).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext s
        simp
      have h2' : Fintype.card { x : Fin q // x ∉ tgt } = (Finset.univ \ tgt).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext x
        simp
      rw [h1', h2', h1, h2]
    let eComp : { s : S // s ∉ img } ≃ { x : Fin q // x ∉ tgt } := Fintype.equivOfCardEq hcomp_card
    let eImg : { s : S // s ∈ img } ≃ { x : Fin q // x ∈ tgt } :=
      { toFun := fun s =>
          let a := Classical.choose (Finset.mem_image.mp s.2)
          ⟨⟨a.val, lt_of_lt_of_le a.isLt hLq⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.isLt⟩⟩
        invFun := fun x =>
          let a : Fin L := ⟨x.1.val, (Finset.mem_filter.mp x.2).2⟩
          ⟨tab i a, Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩
        left_inv := fun s => by
          apply Subtype.ext
          exact (Classical.choose_spec (Finset.mem_image.mp s.2)).2
        right_inv := fun x => by
          apply Subtype.ext
          apply Fin.ext
          dsimp only
          generalize_proofs _ h1
          exact congrArg Fin.val (hinj i (Classical.choose_spec h1).2) }
    let e : S ≃ Fin q :=
      (Equiv.sumCompl (· ∈ img)).symm.trans ((Equiv.sumCongr eImg eComp).trans (Equiv.sumCompl (· ∈ tgt)))
    refine ⟨e, fun a => ?_⟩
    have hmem : tab i a ∈ img := Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
    have hev : e (tab i a) = (eImg ⟨tab i a, hmem⟩).1 := by
      simp [e, Equiv.sumCompl_symm_apply_of_pos hmem]
    rw [hev]
    have hspec := (Classical.choose_spec (Finset.mem_image.mp hmem)).2
    have heqa : Classical.choose (Finset.mem_image.mp hmem) = a := hinj i hspec
    exact congrArg Fin.val heqa
  choose e he using hex_e
  have hmiss :
      ((Finset.univ : Finset (Fin m → S)).filter (fun w =>
        ¬ ∃ a : Fin L, ∀ i : Fin m, w i ∉ ({tab i a} : Finset S))).card = occ q L m := by
    unfold occ
    refine Finset.card_bij (fun w _ i => e i (w i)) ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hw ⊢
      push Not at hw
      intro a
      obtain ⟨i, hi⟩ := hw a
      exact ⟨i, by rw [hi, he i a]⟩
    · intro w1 _ w2 _ h
      funext i
      exact (e i).injective (congrFun h i)
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      refine ⟨fun i => (e i).symm (u i), ?_, by funext i; simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      push Not
      intro a
      obtain ⟨i, hi⟩ := hu a
      refine ⟨i, ?_⟩
      apply (e i).injective
      rw [Equiv.apply_symm_apply]
      apply Fin.ext
      rw [hi, he i a]
  have htot :
      hitSets (fun i a => {tab i a}) +
        ((Finset.univ : Finset (Fin m → S)).filter (fun w =>
          ¬ ∃ a : Fin L, ∀ i : Fin m, w i ∉ ({tab i a} : Finset S))).card = q ^ m := by
    unfold hitSets
    rw [← Finset.card_union_of_disjoint]
    · have hun :
          (Finset.univ : Finset (Fin m → S)).filter (fun w =>
            ∃ a : Fin L, ∀ i : Fin m, w i ∉ ({tab i a} : Finset S)) ∪
          (Finset.univ : Finset (Fin m → S)).filter (fun w =>
            ¬ ∃ a : Fin L, ∀ i : Fin m, w i ∉ ({tab i a} : Finset S)) = Finset.univ := by
        ext w
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact em _
      rw [hun, Finset.card_univ, Fintype.card_fun, hq, Fintype.card_fin]
    · rw [Finset.disjoint_left]
      intro w h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  omega

lemma card_surv_pair_eq_occ {S : Type} [Fintype S] [DecidableEq S] {m L q : ℕ}
    (hq : Fintype.card S = q) (hLq : L ≤ q) (hL2 : 2 ≤ L) (i0 : Fin m)
    (tab : Fin m → Fin L → S) (hinj : ∀ i ≠ i0, Function.Injective (tab i))
    (a0 b0 : Fin L) (hab : a0 ≠ b0) :
    ((Finset.univ : Finset ({ i : Fin m // i ≠ i0 } → S)).filter (fun w' =>
      ∀ c : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ≠ tab j.1 c) ↔ c = a0 ∨ c = b0)).card =
      occ (q - 2) (L - 2) (m - 1) := by
  have heL : Fintype.card { c : Fin L // c ≠ a0 ∧ c ≠ b0 } = L - 2 := by
    have hcard : (Finset.univ \ ({a0, b0} : Finset (Fin L))).card = L - 2 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
        Finset.card_pair hab]
    rw [Fintype.card_subtype, ← hcard]
    congr 1
    ext c
    simp [not_or]
  let eL : { c : Fin L // c ≠ a0 ∧ c ≠ b0 } ≃ Fin (L - 2) := Fintype.equivOfCardEq (by simp [heL])
  have heM : Fintype.card { i : Fin m // i ≠ i0 } = m - 1 := by
    have hcard : (Finset.univ.erase i0).card = m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ, Fintype.card_fin]
    rw [Fintype.card_subtype, ← hcard]
    congr 1
    ext i
    simp
  let eM : { i : Fin m // i ≠ i0 } ≃ Fin (m - 1) := Fintype.equivOfCardEq (by simp [heM])
  have hex_e : ∀ j : { i : Fin m // i ≠ i0 },
      ∃ e : { s : S // s ≠ tab j.1 a0 ∧ s ≠ tab j.1 b0 } ≃ Fin (q - 2),
        ∀ c : { c : Fin L // c ≠ a0 ∧ c ≠ b0 },
          (e ⟨tab j.1 c.1, ⟨fun h => c.2.1 (hinj j.1 j.2 h), fun h => c.2.2 (hinj j.1 j.2 h)⟩⟩).val =
            (eL c).val := by
    intro j
    let T := { s : S // s ≠ tab j.1 a0 ∧ s ≠ tab j.1 b0 }
    have hTcard : Fintype.card T = q - 2 := by
      have hne : tab j.1 a0 ≠ tab j.1 b0 := fun h => hab (hinj j.1 j.2 h)
      have hcard : (Finset.univ \ ({tab j.1 a0, tab j.1 b0} : Finset S)).card = q - 2 := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hq, Finset.card_pair hne]
      rw [Fintype.card_subtype, ← hcard]
      congr 1
      ext s
      simp [not_or]
    let f : Fin (L - 2) → T := fun k =>
      let c := eL.symm k
      ⟨tab j.1 c.1, ⟨fun h => c.2.1 (hinj j.1 j.2 h), fun h => c.2.2 (hinj j.1 j.2 h)⟩⟩
    have hfinj : Function.Injective f := by
      intro k1 k2 h
      have hval : tab j.1 (eL.symm k1).1 = tab j.1 (eL.symm k2).1 := congrArg Subtype.val h
      exact eL.symm.injective (Subtype.ext (hinj j.1 j.2 hval))
    let img : Finset T := Finset.univ.image f
    let tgt : Finset (Fin (q - 2)) := Finset.univ.filter (fun x : Fin (q - 2) => x.val < L - 2)
    have hLq2 : L - 2 ≤ q - 2 := by omega
    have himg_card : img.card = L - 2 := by
      rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
    have htgt_card : tgt.card = L - 2 := by
      trans (Finset.univ : Finset (Fin (L - 2))).card
      · refine Finset.card_bij (t := (Finset.univ : Finset (Fin (L - 2))))
          (fun x hx => ⟨x.val, (Finset.mem_filter.mp hx).2⟩) (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ _ h => Fin.ext (congrArg (fun z : Fin (L - 2) => z.val) h))
          (fun k _ => ⟨⟨k.val, lt_of_lt_of_le k.isLt hLq2⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩, Fin.ext rfl⟩)
      · simp
    have hcomp_card :
        Fintype.card { s : T // s ∉ img } = Fintype.card { x : Fin (q - 2) // x ∉ tgt } := by
      have h1 : (Finset.univ \ img).card = (q - 2) - (L - 2) := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hTcard, himg_card]
      have h2 : (Finset.univ \ tgt).card = (q - 2) - (L - 2) := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, htgt_card]
      have h1' : Fintype.card { s : T // s ∉ img } = (Finset.univ \ img).card := by
        rw [Fintype.card_subtype]; congr 1; ext s; simp
      have h2' : Fintype.card { x : Fin (q - 2) // x ∉ tgt } = (Finset.univ \ tgt).card := by
        rw [Fintype.card_subtype]; congr 1; ext x; simp
      rw [h1', h2', h1, h2]
    let eComp : { s : T // s ∉ img } ≃ { x : Fin (q - 2) // x ∉ tgt } := Fintype.equivOfCardEq hcomp_card
    let eImg : { s : T // s ∈ img } ≃ { x : Fin (q - 2) // x ∈ tgt } :=
      { toFun := fun s =>
          let k := Classical.choose (Finset.mem_image.mp s.2)
          ⟨⟨k.val, lt_of_lt_of_le k.isLt hLq2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩⟩
        invFun := fun x =>
          let k : Fin (L - 2) := ⟨x.1.val, (Finset.mem_filter.mp x.2).2⟩
          ⟨f k, Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩⟩
        left_inv := fun s => by
          apply Subtype.ext
          exact (Classical.choose_spec (Finset.mem_image.mp s.2)).2
        right_inv := fun x => by
          apply Subtype.ext
          apply Fin.ext
          dsimp only
          generalize_proofs _ h1
          exact congrArg Fin.val (hfinj (Classical.choose_spec h1).2) }
    let e : T ≃ Fin (q - 2) :=
      (Equiv.sumCompl (· ∈ img)).symm.trans ((Equiv.sumCongr eImg eComp).trans (Equiv.sumCompl (· ∈ tgt)))
    refine ⟨e, fun c => ?_⟩
    let s : T := ⟨tab j.1 c.1, ⟨fun h => c.2.1 (hinj j.1 j.2 h), fun h => c.2.2 (hinj j.1 j.2 h)⟩⟩
    have hs_eq : f (eL c) = s := by
      apply Subtype.ext
      simp [f, s]
    have hmem : s ∈ img := Finset.mem_image.mpr ⟨eL c, Finset.mem_univ _, hs_eq⟩
    have hev : e s = (eImg ⟨s, hmem⟩).1 := by
      simp [e, Equiv.sumCompl_symm_apply_of_pos hmem]
    rw [hev]
    have hspec := (Classical.choose_spec (Finset.mem_image.mp hmem)).2
    have heqk : Classical.choose (Finset.mem_image.mp hmem) = eL c := hfinj (hspec.trans hs_eq.symm)
    exact congrArg Fin.val heqk
  choose e he using hex_e
  unfold occ
  refine Finset.card_bij
    (fun w' hw' idx =>
      let j := eM.symm idx
      have hw := (Finset.mem_filter.mp hw').2
      e j ⟨w' j, ⟨(hw a0).mpr (Or.inl rfl) j, (hw b0).mpr (Or.inr rfl) j⟩⟩) ?_ ?_ ?_
  · intro w' hw'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw' ⊢
    intro k
    let c := eL.symm k
    have hnot : ¬ (∀ j : { i : Fin m // i ≠ i0 }, w' j ≠ tab j.1 c.1) := by
      intro hall
      have := (hw' c.1).mp hall
      rcases this with h1 | h2
      · exact c.2.1 h1
      · exact c.2.2 h2
    push Not at hnot
    obtain ⟨j, hj⟩ := hnot
    refine ⟨eM j, ?_⟩
    generalize hjj : eM.symm (eM j) = j'
    have hjeq : j' = j := hjj.symm.trans (eM.symm_apply_apply j)
    clear hjj
    subst j'
    have hsub :
        (⟨w' j, ⟨(hw' a0).mpr (Or.inl rfl) j, (hw' b0).mpr (Or.inr rfl) j⟩⟩ :
          { s : S // s ≠ tab j.1 a0 ∧ s ≠ tab j.1 b0 }) =
        ⟨tab j.1 c.1, ⟨fun h => c.2.1 (hinj j.1 j.2 h), fun h => c.2.2 (hinj j.1 j.2 h)⟩⟩ :=
      Subtype.ext hj
    rw [hsub, he j c]
    simp [c]
  · intro w1 hw1 w2 hw2 h
    funext j
    have hidx := congrFun h (eM j)
    dsimp only at hidx
    generalize hjj : eM.symm (eM j) = j' at hidx
    have hjeq : j' = j := hjj.symm.trans (eM.symm_apply_apply j)
    clear hjj
    subst j'
    exact congrArg Subtype.val ((e j).injective hidx)
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    let w' : { i : Fin m // i ≠ i0 } → S := fun j => ((e j).symm (u (eM j))).1
    have hw'_mem : ∀ c : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ≠ tab j.1 c) ↔ c = a0 ∨ c = b0 := by
      intro c
      constructor
      · intro hall
        by_contra hnot
        push Not at hnot
        obtain ⟨idx, hidx⟩ := hu (eL ⟨c, hnot⟩)
        let j := eM.symm idx
        have hj_eq : u (eM j) = e j ⟨tab j.1 c,
            ⟨fun h => hnot.1 (hinj j.1 j.2 h), fun h => hnot.2 (hinj j.1 j.2 h)⟩⟩ := by
          apply Fin.ext
          rw [Equiv.apply_symm_apply, hidx, he j ⟨c, hnot⟩]
        have hwj : w' j = tab j.1 c := by
          dsimp only [w']
          rw [hj_eq, Equiv.symm_apply_apply]
        exact hall j hwj
      · rintro (rfl | rfl) j
        · exact ((e j).symm (u (eM j))).2.1
        · exact ((e j).symm (u (eM j))).2.2
    refine ⟨w', Finset.mem_filter.mpr ⟨Finset.mem_univ w', hw'_mem⟩, ?_⟩
    funext idx
    dsimp only
    have heq_sub :
        (⟨w' (eM.symm idx), ⟨(hw'_mem a0).mpr (Or.inl rfl) (eM.symm idx),
          (hw'_mem b0).mpr (Or.inr rfl) (eM.symm idx)⟩⟩ :
          { s : S // s ≠ tab (eM.symm idx).1 a0 ∧ s ≠ tab (eM.symm idx).1 b0 }) =
        (e (eM.symm idx)).symm (u (eM (eM.symm idx))) := Subtype.ext rfl
    rw [heq_sub, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

lemma card_surv_single_eq_occ {S : Type} [Fintype S] [DecidableEq S] {m L q : ℕ}
    (hq : Fintype.card S = q) (hLq : L ≤ q) (i0 : Fin m)
    (tab : Fin m → Fin L → S) (hinj : ∀ i ≠ i0, Function.Injective (tab i))
    (a0 : Fin L) :
    ((Finset.univ : Finset ({ i : Fin m // i ≠ i0 } → S)).filter (fun w' =>
      ∀ c : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ≠ tab j.1 c) ↔ c = a0)).card =
      occ (q - 1) (L - 1) (m - 1) := by
  have heL : Fintype.card { c : Fin L // c ≠ a0 } = L - 1 := by
    have hcard : (Finset.univ.erase a0).card = L - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ a0), Finset.card_univ, Fintype.card_fin]
    rw [Fintype.card_subtype, ← hcard]
    congr 1
    ext c
    simp
  let eL : { c : Fin L // c ≠ a0 } ≃ Fin (L - 1) := Fintype.equivOfCardEq (by simp [heL])
  have heM : Fintype.card { i : Fin m // i ≠ i0 } = m - 1 := by
    have hcard : (Finset.univ.erase i0).card = m - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i0), Finset.card_univ, Fintype.card_fin]
    rw [Fintype.card_subtype, ← hcard]
    congr 1
    ext i
    simp
  let eM : { i : Fin m // i ≠ i0 } ≃ Fin (m - 1) := Fintype.equivOfCardEq (by simp [heM])
  have hex_e : ∀ j : { i : Fin m // i ≠ i0 },
      ∃ e : { s : S // s ≠ tab j.1 a0 } ≃ Fin (q - 1),
        ∀ c : { c : Fin L // c ≠ a0 },
          (e ⟨tab j.1 c.1, fun h => c.2 (hinj j.1 j.2 h)⟩).val = (eL c).val := by
    intro j
    let T := { s : S // s ≠ tab j.1 a0 }
    have hTcard : Fintype.card T = q - 1 := by
      have hcard : (Finset.univ.erase (tab j.1 a0)).card = q - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hq]
      rw [Fintype.card_subtype, ← hcard]
      congr 1
      ext s
      simp
    let f : Fin (L - 1) → T := fun k =>
      let c := eL.symm k
      ⟨tab j.1 c.1, fun h => c.2 (hinj j.1 j.2 h)⟩
    have hfinj : Function.Injective f := by
      intro k1 k2 h
      have hval : tab j.1 (eL.symm k1).1 = tab j.1 (eL.symm k2).1 := congrArg Subtype.val h
      exact eL.symm.injective (Subtype.ext (hinj j.1 j.2 hval))
    let img : Finset T := Finset.univ.image f
    let tgt : Finset (Fin (q - 1)) := Finset.univ.filter (fun x : Fin (q - 1) => x.val < L - 1)
    have hLq1 : L - 1 ≤ q - 1 := by omega
    have himg_card : img.card = L - 1 := by
      rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ, Fintype.card_fin]
    have htgt_card : tgt.card = L - 1 := by
      trans (Finset.univ : Finset (Fin (L - 1))).card
      · refine Finset.card_bij (t := (Finset.univ : Finset (Fin (L - 1))))
          (fun x hx => ⟨x.val, (Finset.mem_filter.mp hx).2⟩) (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ _ h => Fin.ext (congrArg (fun z : Fin (L - 1) => z.val) h))
          (fun k _ => ⟨⟨k.val, lt_of_lt_of_le k.isLt hLq1⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩, Fin.ext rfl⟩)
      · simp
    have hcomp_card :
        Fintype.card { s : T // s ∉ img } = Fintype.card { x : Fin (q - 1) // x ∉ tgt } := by
      have h1 : (Finset.univ \ img).card = (q - 1) - (L - 1) := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hTcard, himg_card]
      have h2 : (Finset.univ \ tgt).card = (q - 1) - (L - 1) := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, htgt_card]
      have h1' : Fintype.card { s : T // s ∉ img } = (Finset.univ \ img).card := by
        rw [Fintype.card_subtype]; congr 1; ext s; simp
      have h2' : Fintype.card { x : Fin (q - 1) // x ∉ tgt } = (Finset.univ \ tgt).card := by
        rw [Fintype.card_subtype]; congr 1; ext x; simp
      rw [h1', h2', h1, h2]
    let eComp : { s : T // s ∉ img } ≃ { x : Fin (q - 1) // x ∉ tgt } := Fintype.equivOfCardEq hcomp_card
    let eImg : { s : T // s ∈ img } ≃ { x : Fin (q - 1) // x ∈ tgt } :=
      { toFun := fun s =>
          let k := Classical.choose (Finset.mem_image.mp s.2)
          ⟨⟨k.val, lt_of_lt_of_le k.isLt hLq1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩⟩
        invFun := fun x =>
          let k : Fin (L - 1) := ⟨x.1.val, (Finset.mem_filter.mp x.2).2⟩
          ⟨f k, Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩⟩
        left_inv := fun s => by
          apply Subtype.ext
          exact (Classical.choose_spec (Finset.mem_image.mp s.2)).2
        right_inv := fun x => by
          apply Subtype.ext
          apply Fin.ext
          dsimp only
          generalize_proofs _ h1
          exact congrArg Fin.val (hfinj (Classical.choose_spec h1).2) }
    let e : T ≃ Fin (q - 1) :=
      (Equiv.sumCompl (· ∈ img)).symm.trans ((Equiv.sumCongr eImg eComp).trans (Equiv.sumCompl (· ∈ tgt)))
    refine ⟨e, fun c => ?_⟩
    let s : T := ⟨tab j.1 c.1, fun h => c.2 (hinj j.1 j.2 h)⟩
    have hs_eq : f (eL c) = s := by
      apply Subtype.ext
      simp [f, s]
    have hmem : s ∈ img := Finset.mem_image.mpr ⟨eL c, Finset.mem_univ _, hs_eq⟩
    have hev : e s = (eImg ⟨s, hmem⟩).1 := by
      simp [e, Equiv.sumCompl_symm_apply_of_pos hmem]
    rw [hev]
    have hspec := (Classical.choose_spec (Finset.mem_image.mp hmem)).2
    have heqk : Classical.choose (Finset.mem_image.mp hmem) = eL c := hfinj (hspec.trans hs_eq.symm)
    exact congrArg Fin.val heqk
  choose e he using hex_e
  unfold occ
  refine Finset.card_bij
    (fun w' hw' idx =>
      let j := eM.symm idx
      have hw := (Finset.mem_filter.mp hw').2
      e j ⟨w' j, (hw a0).mpr rfl j⟩) ?_ ?_ ?_
  · intro w' hw'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw' ⊢
    intro k
    let c := eL.symm k
    have hnot : ¬ (∀ j : { i : Fin m // i ≠ i0 }, w' j ≠ tab j.1 c.1) := by
      intro hall
      exact c.2 ((hw' c.1).mp hall)
    push Not at hnot
    obtain ⟨j, hj⟩ := hnot
    refine ⟨eM j, ?_⟩
    generalize hjj : eM.symm (eM j) = j'
    have hjeq : j' = j := hjj.symm.trans (eM.symm_apply_apply j)
    clear hjj
    subst j'
    have hsub :
        (⟨w' j, (hw' a0).mpr rfl j⟩ : { s : S // s ≠ tab j.1 a0 }) =
        ⟨tab j.1 c.1, fun h => c.2 (hinj j.1 j.2 h)⟩ := Subtype.ext hj
    rw [hsub, he j c]
    simp [c]
  · intro w1 hw1 w2 hw2 h
    funext j
    have hidx := congrFun h (eM j)
    dsimp only at hidx
    generalize hjj : eM.symm (eM j) = j' at hidx
    have hjeq : j' = j := hjj.symm.trans (eM.symm_apply_apply j)
    clear hjj
    subst j'
    exact congrArg Subtype.val ((e j).injective hidx)
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    let w' : { i : Fin m // i ≠ i0 } → S := fun j => ((e j).symm (u (eM j))).1
    have hw'_mem : ∀ c : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ≠ tab j.1 c) ↔ c = a0 := by
      intro c
      constructor
      · intro hall
        by_contra hnot
        obtain ⟨idx, hidx⟩ := hu (eL ⟨c, hnot⟩)
        let j := eM.symm idx
        have hj_eq : u (eM j) = e j ⟨tab j.1 c, fun h => hnot (hinj j.1 j.2 h)⟩ := by
          apply Fin.ext
          rw [Equiv.apply_symm_apply, hidx, he j ⟨c, hnot⟩]
        have hwj : w' j = tab j.1 c := by
          dsimp only [w']
          rw [hj_eq, Equiv.symm_apply_apply]
        exact hall j hwj
      · rintro rfl j
        exact ((e j).symm (u (eM j))).2
    refine ⟨w', Finset.mem_filter.mpr ⟨Finset.mem_univ w', hw'_mem⟩, ?_⟩
    funext idx
    dsimp only
    have heq_sub :
        (⟨w' (eM.symm idx), (hw'_mem a0).mpr rfl (eM.symm idx)⟩ :
          { s : S // s ≠ tab (eM.symm idx).1 a0 }) =
        (e (eM.symm idx)).symm (u (eM (eM.symm idx))) := Subtype.ext rfl
    rw [heq_sub, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

lemma replace_other_cols {S : Type} [Fintype S] [DecidableEq S] {m L : ℕ}
    (bad : Fin m → Fin L → Finset S) (i0 : Fin m)
    (hne : ∀ i a, (bad i a).Nonempty)
    (col_inj : Fin L → S) (hinj : Function.Injective col_inj) :
    hitSets bad ≤ hitSets (fun i => if i = i0 then bad i0 else fun a => {col_inj a}) := by
  have hgen : ∀ (K : Finset (Fin m)), i0 ∉ K →
      hitSets bad ≤ hitSets (fun i => if i ∈ K then (fun a => {col_inj a}) else bad i) := by
    intro K
    induction K using Finset.induction_on with
    | empty =>
      intro _
      simp
    | @insert i1 s hi1 ih =>
      intro hi0
      have hi0s : i0 ∉ s := fun h => hi0 (Finset.mem_insert_of_mem h)
      have h1 := ih hi0s
      let bad_s : Fin m → Fin L → Finset S := fun i => if i ∈ s then (fun a => {col_inj a}) else bad i
      have hne_s : ∀ a, (bad_s i1 a).Nonempty := by
        intro a
        simp only [bad_s, hi1, ↓reduceIte]
        exact hne i1 a
      have h2 := col_replace_le bad_s i1 hne_s col_inj hinj
      have hupd : Function.update bad_s i1 (fun a => {col_inj a}) =
          (fun i => if i ∈ insert i1 s then (fun a => {col_inj a}) else bad i) := by
        funext i
        by_cases hi : i = i1
        · subst hi
          simp
        · simp [bad_s, hi]
      rw [hupd] at h2
      exact le_trans h1 h2
  have h := hgen (Finset.univ.erase i0) (Finset.notMem_erase i0 _)
  have heq : (fun i => if i ∈ Finset.univ.erase i0 then (fun a => {col_inj a}) else bad i) =
      (fun i => if i = i0 then bad i0 else fun a => {col_inj a}) := by
    funext i
    by_cases hi : i = i0
    · subst hi
      simp
    · simp [hi]
  rwa [heq] at h

lemma hitSets_collide_le {S : Type} [Fintype S] [DecidableEq S] {m L q : ℕ}
    (hq : Fintype.card S = q) (hLq : L ≤ q) (hL2 : 2 ≤ L)
    (bad : Fin m → Fin L → Finset S)
    (hne : ∀ i a, (bad i a).Nonempty)
    (i0 : Fin m) (a0 b0 : Fin L) (hab : a0 ≠ b0) (s0 : S)
    (ha0 : s0 ∈ bad i0 a0) (hb0 : s0 ∈ bad i0 b0) :
    hitSets bad + occ (q - 2) (L - 2) (m - 1) ≤ q ^ m - occ q L m := by
  let eS : Fin q ≃ S := (Fintype.equivOfCardEq (by simp [hq])).symm
  let col_inj : Fin L → S := fun a => eS ⟨a.val, lt_of_lt_of_le a.isLt hLq⟩
  have hcol_inj : Function.Injective col_inj := fun a b h =>
    Fin.ext (congrArg (fun z : Fin q => z.val) (eS.injective h))
  let bad1 : Fin m → Fin L → Finset S := fun i =>
    if i = i0 then bad i0 else fun a => {col_inj a}
  have hle1 : hitSets bad ≤ hitSets bad1 := replace_other_cols bad i0 hne col_inj hcol_inj
  let bad2 : Fin m → Fin L → Finset S := fun _ a => {col_inj a}
  have hbest : hitSets bad2 = q ^ m - occ q L m :=
    hitSets_injective_eq hq hLq (fun _ => col_inj) (fun _ => hcol_inj)
  rw [← hbest]
  suffices hdiff : hitSets bad1 + occ (q - 2) (L - 2) (m - 1) ≤ hitSets bad2 by omega
  rw [hitSets_col_split bad1 i0, hitSets_col_split bad2 i0]
  let tab : Fin m → Fin L → S := fun _ => col_inj
  let Wpair := (Finset.univ : Finset ({ i : Fin m // i ≠ i0 } → S)).filter (fun w' =>
    ∀ c : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ≠ tab j.1 c) ↔ c = a0 ∨ c = b0)
  have hWcard : Wpair.card = occ (q - 2) (L - 2) (m - 1) :=
    card_surv_pair_eq_occ hq hLq hL2 i0 tab (fun _ _ => hcol_inj) a0 b0 hab
  rw [← hWcard]
  have hsum_step :
      (∑ w' : { i : Fin m // i ≠ i0 } → S,
        ((Finset.univ : Finset S).filter (fun x =>
          ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad1 j.1 a) ∧ x ∉ bad1 i0 a)).card) +
      (∑ w' : { i : Fin m // i ≠ i0 } → S, if w' ∈ Wpair then 1 else 0) ≤
      ∑ w' : { i : Fin m // i ≠ i0 } → S,
        ((Finset.univ : Finset S).filter (fun x =>
          ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad2 j.1 a) ∧ x ∉ bad2 i0 a)).card := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun w' _ => ?_)
    have hbad1_ne : ∀ j : { i : Fin m // i ≠ i0 }, bad1 j.1 = fun a => {col_inj a} := by
      intro j; simp [bad1, j.2]
    have hbad1_eq : bad1 i0 = bad i0 := by simp [bad1]
    simp_rw [hbad1_ne, hbad1_eq]
    by_cases hw' : w' ∈ Wpair
    · simp only [hw', ↓reduceIte]
      have hpair := (Finset.mem_filter.mp hw').2
      have hLle :
          ((Finset.univ : Finset S).filter (fun x =>
            ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ ({col_inj a} : Finset S)) ∧
              x ∉ bad i0 a)).card ≤ q - 1 := by
        have hsub :
            (Finset.univ : Finset S).filter (fun x =>
              ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ ({col_inj a} : Finset S)) ∧
                x ∉ bad i0 a) ⊆ Finset.univ.erase s0 := by
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
            Finset.mem_singleton] at hx ⊢
          rcases hx with ⟨a, ha, hxa⟩
          have hab' := (hpair a).mp ha
          refine ⟨fun hxs => ?_, trivial⟩
          subst hxs
          rcases hab' with rfl | rfl
          · exact hxa ha0
          · exact hxa hb0
        have hc := Finset.card_le_card hsub
        simpa [Finset.card_erase_of_mem (Finset.mem_univ s0), hq] using hc
      have hReq :
          ((Finset.univ : Finset S).filter (fun x =>
            ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad2 j.1 a) ∧
              x ∉ bad2 i0 a)).card = q := by
        have heq :
            (Finset.univ : Finset S).filter (fun x =>
              ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad2 j.1 a) ∧
                x ∉ bad2 i0 a) = Finset.univ := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, bad2, Finset.mem_singleton, iff_true]
          by_cases hxa : x = col_inj a0
          · refine ⟨b0, (hpair b0).mpr (Or.inr rfl), fun hxb => hab (hcol_inj (hxa.symm.trans hxb))⟩
          · exact ⟨a0, (hpair a0).mpr (Or.inl rfl), hxa⟩
        rw [heq, Finset.card_univ, hq]
      have hqpos : 0 < q := by omega
      omega
    · simp only [hw', ↓reduceIte, add_zero]
      let bad_tmp := Function.update bad1 i0 (fun a => {col_inj a})
      have htmp : bad_tmp = bad2 := by
        funext i
        by_cases hi : i = i0
        · subst hi; simp [bad_tmp, bad2]
        · simp [bad_tmp, bad1, bad2, hi]
      let Surv := Finset.univ.filter (fun a : Fin L => ∀ j : { i : Fin m // i ≠ i0 }, w' j ≠ col_inj a)
      by_cases h0 : Surv.card = 0
      · have hemp := Finset.card_eq_zero.mp h0
        have hL0 : ((Finset.univ : Finset S).filter (fun x =>
            ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ ({col_inj a} : Finset S)) ∧
              x ∉ bad i0 a)).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          rintro x _ ⟨a, ha, _⟩
          have haS : a ∈ Surv := Finset.mem_filter.mpr ⟨Finset.mem_univ a, by simpa using ha⟩
          rw [hemp] at haS
          exact Finset.notMem_empty a haS
        omega
      · by_cases h1 : Surv.card = 1
        · obtain ⟨a, haS⟩ := Finset.card_eq_one.mp h1
          have honly : ∀ b : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ≠ col_inj b) ↔ b = a := by
            intro b
            have : b ∈ Surv ↔ b = a := by rw [haS, Finset.mem_singleton]
            simpa [Surv] using this
          obtain ⟨sa, hsa⟩ := hne i0 a
          have hLle : ((Finset.univ : Finset S).filter (fun x =>
              ∃ b : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ ({col_inj b} : Finset S)) ∧
                x ∉ bad i0 b)).card ≤ q - 1 := by
            have hsub : (Finset.univ : Finset S).filter (fun x =>
                ∃ b : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ ({col_inj b} : Finset S)) ∧
                  x ∉ bad i0 b) ⊆ Finset.univ.erase sa := by
              intro x hx
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
                Finset.mem_singleton] at hx ⊢
              rcases hx with ⟨b, hb, hxb⟩
              have hba := (honly b).mp hb
              subst hba
              exact ⟨fun hxs => hxb (hxs ▸ hsa), trivial⟩
            have hc := Finset.card_le_card hsub
            simpa [Finset.card_erase_of_mem (Finset.mem_univ sa), hq] using hc
          have hReq : ((Finset.univ : Finset S).filter (fun x =>
              ∃ b : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad2 j.1 b) ∧
                x ∉ bad2 i0 b)).card = q - 1 := by
            have heq : (Finset.univ : Finset S).filter (fun x =>
                ∃ b : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad2 j.1 b) ∧
                  x ∉ bad2 i0 b) = Finset.univ.erase (col_inj a) := by
              ext x
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
                bad2, Finset.mem_singleton, honly, exists_eq_left, and_true]
            rw [heq]
            simp [Finset.card_erase_of_mem (Finset.mem_univ (col_inj a)), hq]
          omega
        · have hge2 : 1 < Surv.card := by omega
          obtain ⟨a, ha, b, hb, hab'⟩ := Finset.one_lt_card.mp hge2
          have hReq : ((Finset.univ : Finset S).filter (fun x =>
              ∃ c : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad2 j.1 c) ∧
                x ∉ bad2 i0 c)).card = q := by
            have heq : (Finset.univ : Finset S).filter (fun x =>
                ∃ c : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad2 j.1 c) ∧
                  x ∉ bad2 i0 c) = Finset.univ := by
              ext x
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, bad2, Finset.mem_singleton, iff_true]
              by_cases hxa : x = col_inj a
              · exact ⟨b, (Finset.mem_filter.mp hb).2, fun hxb => hab' (hcol_inj (hxa.symm.trans hxb))⟩
              · exact ⟨a, (Finset.mem_filter.mp ha).2, hxa⟩
            rw [heq, Finset.card_univ, hq]
          rw [hReq, ← hq]
          exact Finset.card_le_univ _
  have hWsum : (∑ w' : { i : Fin m // i ≠ i0 } → S, if w' ∈ Wpair then 1 else 0) = Wpair.card := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    congr 1
    ext w'
    simp
  rw [hWsum] at hsum_step
  exact hsum_step

lemma hitSets_enlarge_eq {S : Type} [Fintype S] [DecidableEq S] {m L q : ℕ}
    (hq : Fintype.card S = q) (hLq : L ≤ q)
    (tab : Fin m → Fin L → S) (hinj : ∀ i, Function.Injective (tab i))
    (i0 : Fin m) (a0 : Fin L) (s2 s3 : S)
    (hs2_ne : ∀ a : Fin L, s2 ≠ tab i0 a) (hs3_ne : ∀ a : Fin L, s3 ≠ tab i0 a) (hs23 : s2 ≠ s3) :
    hitSets (fun i a => if i = i0 ∧ a = a0 then {tab i0 a0, s2, s3} else {tab i a}) +
      2 * occ (q - 1) (L - 1) (m - 1) = q ^ m - occ q L m := by
  let bad1 : Fin m → Fin L → Finset S :=
    fun i a => if i = i0 ∧ a = a0 then {tab i0 a0, s2, s3} else {tab i a}
  let bad2 : Fin m → Fin L → Finset S := fun i a => {tab i a}
  have hbest : hitSets bad2 = q ^ m - occ q L m := hitSets_injective_eq hq hLq tab hinj
  rw [← hbest, hitSets_col_split bad1 i0, hitSets_col_split bad2 i0]
  let Wsing := (Finset.univ : Finset ({ i : Fin m // i ≠ i0 } → S)).filter (fun w' =>
    ∀ c : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ≠ tab j.1 c) ↔ c = a0)
  have hWcard : Wsing.card = occ (q - 1) (L - 1) (m - 1) :=
    card_surv_single_eq_occ hq hLq i0 tab (fun i _ => hinj i) a0
  rw [← hWcard]
  have hWsum : 2 * Wsing.card = ∑ w' : { i : Fin m // i ≠ i0 } → S, if w' ∈ Wsing then 2 else 0 := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
    congr 2
    ext w'
    simp
  rw [hWsum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w' _ => ?_)
  have hbad1_ne : ∀ j : { i : Fin m // i ≠ i0 }, ∀ a : Fin L, bad1 j.1 a = {tab j.1 a} := by
    intro j a
    simp [bad1, j.2]
  simp_rw [hbad1_ne]
  let Surv := Finset.univ.filter (fun a : Fin L => ∀ j : { i : Fin m // i ≠ i0 }, w' j ≠ tab j.1 a)
  by_cases hw' : w' ∈ Wsing
  · simp only [hw', ↓reduceIte]
    have hsing := (Finset.mem_filter.mp hw').2
    have hcard3 : ({tab i0 a0, s2, s3} : Finset S).card = 3 := by
      have h1 : tab i0 a0 ∉ ({s2, s3} : Finset S) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨(hs2_ne a0).symm, (hs3_ne a0).symm⟩
      rw [Finset.card_insert_of_notMem h1, Finset.card_pair hs23]
    have hL :
        ((Finset.univ : Finset S).filter (fun x =>
          ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ ({tab j.1 a} : Finset S)) ∧
            x ∉ bad1 i0 a)).card = q - 3 := by
      have heq :
          (Finset.univ : Finset S).filter (fun x =>
            ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ ({tab j.1 a} : Finset S)) ∧
              x ∉ bad1 i0 a) = Finset.univ \ ({tab i0 a0, s2, s3} : Finset S) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
          Finset.mem_singleton, hsing, exists_eq_left, bad1, ↓reduceIte]
      rw [heq, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hq, hcard3]
    have hR :
        ((Finset.univ : Finset S).filter (fun x =>
          ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad2 j.1 a) ∧
            x ∉ bad2 i0 a)).card = q - 1 := by
      have heq :
          (Finset.univ : Finset S).filter (fun x =>
            ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad2 j.1 a) ∧
              x ∉ bad2 i0 a) = Finset.univ.erase (tab i0 a0) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
          bad2, Finset.mem_singleton, hsing, exists_eq_left, and_true]
      rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hq]
    have h3q : 3 ≤ q := by
      have := Finset.card_le_univ ({tab i0 a0, s2, s3} : Finset S)
      rw [hcard3, hq] at this
      exact this
    rw [hL, hR]
    omega
  · simp only [hw', ↓reduceIte, add_zero]
    apply congrArg Finset.card
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, bad2, Finset.mem_singleton]
    constructor
    · rintro ⟨a, ha, hxa⟩
      refine ⟨a, ha, ?_⟩
      by_cases haa0 : a = a0
      · subst a
        simp only [bad1, and_self, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton, not_or] at hxa
        exact hxa.1
      · simp only [bad1, haa0, and_false, ↓reduceIte, Finset.mem_singleton] at hxa
        exact hxa
    · rintro ⟨a, ha, hxa⟩
      by_cases haa0 : a = a0
      · subst a
        by_cases hx23 : x = s2 ∨ x = s3
        · have hex_other : ∃ b : Fin L, b ≠ a0 ∧ ∀ j : { i : Fin m // i ≠ i0 }, w' j ≠ tab j.1 b := by
            by_contra hno
            push Not at hno
            apply hw'
            simp only [Wsing, Finset.mem_filter, Finset.mem_univ, true_and]
            intro c
            constructor
            · intro hc
              by_contra hca
              obtain ⟨j, hj⟩ := hno c hca
              exact hc j hj
            · rintro rfl
              exact ha
          obtain ⟨b, hba, hb⟩ := hex_other
          refine ⟨b, hb, ?_⟩
          simp only [bad1, hba, and_false, ↓reduceIte, Finset.mem_singleton]
          rcases hx23 with rfl | rfl
          · exact hs2_ne b
          · exact hs3_ne b
        · refine ⟨a0, ha, ?_⟩
          simp only [bad1, and_self, ↓reduceIte, Finset.mem_insert, Finset.mem_singleton, not_or]
          push Not at hx23
          exact ⟨hxa, hx23.1, hx23.2⟩
      · refine ⟨a, ha, ?_⟩
        simp only [bad1, haa0, and_false, ↓reduceIte, Finset.mem_singleton]
        exact hxa

lemma hitSets_single_collide_eq {S : Type} [Fintype S] [DecidableEq S] {m L q : ℕ}
    (hq : Fintype.card S = q) (hLq : L ≤ q) (hL2 : 2 ≤ L)
    (tab : Fin m → Fin L → S) (hinj : ∀ i, Function.Injective (tab i))
    (i0 : Fin m) (a0 b0 : Fin L) (hab : a0 ≠ b0) :
    let tab' : Fin m → Fin L → S :=
      fun i a => if i = i0 ∧ a = b0 then tab i0 a0 else tab i a
    hitSets (fun i a => {tab' i a}) + occ (q - 2) (L - 2) (m - 1) = q ^ m - occ q L m := by
  dsimp only
  let bad1 : Fin m → Fin L → Finset S :=
    fun i a => {if i = i0 ∧ a = b0 then tab i0 a0 else tab i a}
  let bad2 : Fin m → Fin L → Finset S := fun i a => {tab i a}
  have hbest : hitSets bad2 = q ^ m - occ q L m := hitSets_injective_eq hq hLq tab hinj
  rw [← hbest, hitSets_col_split bad1 i0, hitSets_col_split bad2 i0]
  let Wpair := (Finset.univ : Finset ({ i : Fin m // i ≠ i0 } → S)).filter (fun w' =>
    ∀ c : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ≠ tab j.1 c) ↔ c = a0 ∨ c = b0)
  have hWcard : Wpair.card = occ (q - 2) (L - 2) (m - 1) :=
    card_surv_pair_eq_occ hq hLq hL2 i0 tab (fun i _ => hinj i) a0 b0 hab
  rw [← hWcard]
  have hWsum : Wpair.card = ∑ w' : { i : Fin m // i ≠ i0 } → S, if w' ∈ Wpair then 1 else 0 := by
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    congr 1
    ext w'
    simp
  rw [hWsum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun w' _ => ?_)
  have hbad1_ne : ∀ j : { i : Fin m // i ≠ i0 }, ∀ a : Fin L, bad1 j.1 a = {tab j.1 a} := by
    intro j a
    simp [bad1, j.2]
  simp_rw [hbad1_ne]
  by_cases hw' : w' ∈ Wpair
  · simp only [hw', ↓reduceIte]
    have hpair := (Finset.mem_filter.mp hw').2
    have hL :
        ((Finset.univ : Finset S).filter (fun x =>
          ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ ({tab j.1 a} : Finset S)) ∧
            x ∉ bad1 i0 a)).card = q - 1 := by
      have heq :
          (Finset.univ : Finset S).filter (fun x =>
            ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ ({tab j.1 a} : Finset S)) ∧
              x ∉ bad1 i0 a) = Finset.univ.erase (tab i0 a0) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
          Finset.mem_singleton, hpair, bad1, true_and]
        constructor
        · rintro ⟨a, ha | ha, hxa⟩
          · subst a
            simp only [hab, ↓reduceIte] at hxa
            exact ⟨hxa, trivial⟩
          · subst a
            simp only [↓reduceIte] at hxa
            exact ⟨hxa, trivial⟩
        · rintro ⟨hx, _⟩
          refine ⟨a0, Or.inl rfl, ?_⟩
          simp only [hab, ↓reduceIte]
          exact hx
      rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hq]
    have hR :
        ((Finset.univ : Finset S).filter (fun x =>
          ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad2 j.1 a) ∧
            x ∉ bad2 i0 a)).card = q := by
      have heq :
          (Finset.univ : Finset S).filter (fun x =>
            ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad2 j.1 a) ∧
              x ∉ bad2 i0 a) = Finset.univ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, bad2, Finset.mem_singleton, iff_true]
        by_cases hxa : x = tab i0 a0
        · exact ⟨b0, (hpair b0).mpr (Or.inr rfl), fun hxb => hab (hinj i0 (hxa.symm.trans hxb))⟩
        · exact ⟨a0, (hpair a0).mpr (Or.inl rfl), hxa⟩
      rw [heq, Finset.card_univ, hq]
    have hqpos : 0 < q := by omega
    rw [hL, hR]
    omega
  · simp only [hw', ↓reduceIte, add_zero]
    let Surv := Finset.univ.filter (fun a : Fin L => ∀ j : { i : Fin m // i ≠ i0 }, w' j ≠ tab j.1 a)
    by_cases h0 : Surv.card = 0
    · have hemp := Finset.card_eq_zero.mp h0
      have hL0 : ((Finset.univ : Finset S).filter (fun x =>
          ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ ({tab j.1 a} : Finset S)) ∧
            x ∉ bad1 i0 a)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro x _ ⟨a, ha, _⟩
        have haS : a ∈ Surv := Finset.mem_filter.mpr ⟨Finset.mem_univ a, by simpa using ha⟩
        rw [hemp] at haS
        exact Finset.notMem_empty a haS
      have hR0 : ((Finset.univ : Finset S).filter (fun x =>
          ∃ a : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad2 j.1 a) ∧
            x ∉ bad2 i0 a)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro x _ ⟨a, ha, _⟩
        have haS : a ∈ Surv := Finset.mem_filter.mpr ⟨Finset.mem_univ a, by simpa [bad2] using ha⟩
        rw [hemp] at haS
        exact Finset.notMem_empty a haS
      rw [hL0, hR0]
    · by_cases h1 : Surv.card = 1
      · obtain ⟨a, haS⟩ := Finset.card_eq_one.mp h1
        have honly : ∀ c : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ≠ tab j.1 c) ↔ c = a := by
          intro c
          have : c ∈ Surv ↔ c = a := by rw [haS, Finset.mem_singleton]
          simpa [Surv] using this
        have hL : ((Finset.univ : Finset S).filter (fun x =>
            ∃ c : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ ({tab j.1 c} : Finset S)) ∧
              x ∉ bad1 i0 c)).card = q - 1 := by
          have heq : (Finset.univ : Finset S).filter (fun x =>
              ∃ c : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ ({tab j.1 c} : Finset S)) ∧
                x ∉ bad1 i0 c) = Finset.univ.erase (if a = b0 then tab i0 a0 else tab i0 a) := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
              Finset.mem_singleton, honly, exists_eq_left, bad1, true_and, and_true]
          rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hq]
        have hR : ((Finset.univ : Finset S).filter (fun x =>
            ∃ c : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad2 j.1 c) ∧
              x ∉ bad2 i0 c)).card = q - 1 := by
          have heq : (Finset.univ : Finset S).filter (fun x =>
              ∃ c : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad2 j.1 c) ∧
                x ∉ bad2 i0 c) = Finset.univ.erase (tab i0 a) := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
              bad2, Finset.mem_singleton, honly, exists_eq_left, and_true]
          rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hq]
        rw [hL, hR]
      · have hge2 : 1 < Surv.card := by omega
        obtain ⟨c1, hc1, c2, hc2, hc12⟩ := Finset.one_lt_card.mp hge2
        have hpair_diff : ∃ d1 ∈ Surv, ∃ d2 ∈ Surv,
            (if d1 = b0 then tab i0 a0 else tab i0 d1) ≠ (if d2 = b0 then tab i0 a0 else tab i0 d2) := by
          by_cases hsub : Surv ⊆ {a0, b0}
          · exfalso
            apply hw'
            simp only [Wpair, Finset.mem_filter, Finset.mem_univ, true_and]
            have hcard_le : Surv.card ≤ 2 := by
              have hc := Finset.card_le_card hsub
              rwa [Finset.card_pair hab] at hc
            have heqS : Surv = {a0, b0} := Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hab]; omega)
            intro c
            have : c ∈ Surv ↔ c = a0 ∨ c = b0 := by rw [heqS, Finset.mem_insert, Finset.mem_singleton]
            simpa [Surv] using this
          · rw [Finset.not_subset] at hsub
            obtain ⟨d1, hd1S, hd1not⟩ := hsub
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd1not
            have hex2 : ∃ d2 ∈ Surv, d2 ≠ d1 := by
              by_cases h : c1 = d1
              · exact ⟨c2, hc2, h ▸ hc12.symm⟩
              · exact ⟨c1, hc1, h⟩
            obtain ⟨d2, hd2S, hd21⟩ := hex2
            refine ⟨d1, hd1S, d2, hd2S, ?_⟩
            simp only [hd1not.2, ↓reduceIte]
            by_cases hd2b : d2 = b0
            · simp only [hd2b, ↓reduceIte]
              exact fun heq => hd1not.1 (hinj i0 heq)
            · simp only [hd2b, ↓reduceIte]
              exact fun heq => hd21 (hinj i0 heq).symm
        obtain ⟨d1, hd1S, d2, hd2S, hne12⟩ := hpair_diff
        have hL : ((Finset.univ : Finset S).filter (fun x =>
            ∃ c : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ ({tab j.1 c} : Finset S)) ∧
              x ∉ bad1 i0 c)).card = q := by
          have heq : (Finset.univ : Finset S).filter (fun x =>
              ∃ c : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ ({tab j.1 c} : Finset S)) ∧
                x ∉ bad1 i0 c) = Finset.univ := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, bad1, Finset.mem_singleton,
              true_and, iff_true]
            by_cases hx1 : x = if d1 = b0 then tab i0 a0 else tab i0 d1
            · exact ⟨d2, (Finset.mem_filter.mp hd2S).2, fun hx2 => hne12 (hx1.symm.trans hx2)⟩
            · exact ⟨d1, (Finset.mem_filter.mp hd1S).2, hx1⟩
          rw [heq, Finset.card_univ, hq]
        have hR : ((Finset.univ : Finset S).filter (fun x =>
            ∃ c : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad2 j.1 c) ∧
              x ∉ bad2 i0 c)).card = q := by
          have heq : (Finset.univ : Finset S).filter (fun x =>
              ∃ c : Fin L, (∀ j : { i : Fin m // i ≠ i0 }, w' j ∉ bad2 j.1 c) ∧
                x ∉ bad2 i0 c) = Finset.univ := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, bad2, Finset.mem_singleton, iff_true]
            by_cases hxc : x = tab i0 c1
            · exact ⟨c2, (Finset.mem_filter.mp hc2).2, fun hxc2 => hc12 (hinj i0 (hxc.symm.trans hxc2))⟩
            · exact ⟨c1, (Finset.mem_filter.mp hc1).2, hxc⟩
          rw [heq, Finset.card_univ, hq]
        rw [hL, hR]

end PEqualNP.Outside.L_lib_630_aux

theorem PEqualNP.Outside.L_lib_630 : (∀ (r m L : Nat), 2 ≤ r → 2 ≤ L → L ≤ 2^r → L ≤ m →
  let q := 2^r
  let S := Fin r → Bool
  let Menu := Fin m → Fin L → S → Bool
  let target := fun (s : S) => decide (∀ j, s j = true)
  let low := fun (f : S → Bool) => ∃ T : Finset (Finset (Fin r)),
    (∀ mon ∈ T, mon.card < r) ∧ ∀ input,
      f input = (((T.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)
  let legal := fun (p : Menu) => ∀ i a, low (p i a)
  let hit := fun (p : Menu) =>
    ((Finset.univ : Finset (Fin m → S)).filter (fun word =>
      ∃ a, ∀ i, p i a (word i) = target (word i))).card
  let occ := fun (alphabet labels width : Nat) =>
    ((Finset.univ : Finset (Fin width → Fin alphabet)).filter (fun w =>
      ∀ k : Fin labels, ∃ j, (w j).val = k.val)).card
  let best := q^m - occ q L m
  let collide := occ (q-2) (L-2) (m-1)
  let enlarge := 2 * occ (q-1) (L-1) (m-1)
  let gap := if L+2 ≤ q then min collide enlarge else collide
  (∀ p : Menu, legal p → hit p ≤ best ∧
    (hit p = best ↔ ∃ bad : Fin m → Fin L → S,
      (∀ i, Function.Injective (bad i)) ∧
      ∀ i a word, (p i a word ≠ target word ↔ word = bad i a))) ∧
  (∃ p : Menu, legal p ∧ hit p = best) ∧ 0 < gap ∧
  (∀ p : Menu, legal p → hit p < best → hit p + gap ≤ best) ∧
  ∃ p : Menu, legal p ∧ hit p + gap = best) := by
  intro r m L hr hL2 hLq hLm
  dsimp only
  let q := 2 ^ r
  let S := Fin r → Bool
  have hq_card : Fintype.card S = q := by
    simp [S, q]
  have hq4 : 4 ≤ q := by
    have : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr
    simpa [q] using this
  have hcol_pos : 0 < PEqualNP.Outside.L_lib_630_aux.occ (q - 2) (L - 2) (m - 1) :=
    PEqualNP.Outside.L_lib_630_aux.occ_pos (by omega) (by omega) (by omega)
  have henl_pos : 0 < 2 * PEqualNP.Outside.L_lib_630_aux.occ (q - 1) (L - 1) (m - 1) := by
    have h1 := PEqualNP.Outside.L_lib_630_aux.occ_pos (alphabet := q - 1) (labels := L - 1)
      (width := m - 1) (by omega) (by omega) (by omega)
    omega
  have hgap_pos : 0 < if L + 2 ≤ q then
      min (PEqualNP.Outside.L_lib_630_aux.occ (q - 2) (L - 2) (m - 1))
          (2 * PEqualNP.Outside.L_lib_630_aux.occ (q - 1) (L - 1) (m - 1))
      else PEqualNP.Outside.L_lib_630_aux.occ (q - 2) (L - 2) (m - 1) := by
    by_cases h : L + 2 ≤ q
    · simp only [h, ↓reduceIte, lt_min_iff]
      exact ⟨hcol_pos, henl_pos⟩
    · simp only [h, ↓reduceIte]
      exact hcol_pos
  have hhit_eq : ∀ p : Fin m → Fin L → S → Bool,
      ((Finset.univ : Finset (Fin m → S)).filter (fun word =>
        ∃ a, ∀ i, p i a (word i) = decide (∀ j, word i j = true))).card =
      PEqualNP.Outside.L_lib_630_aux.hitSets (fun i a => PEqualNP.Outside.L_lib_630_aux.errSet (p i a)) := by
    intro p
    unfold PEqualNP.Outside.L_lib_630_aux.hitSets PEqualNP.Outside.L_lib_630_aux.errSet
      PEqualNP.Outside.L_lib_630_aux.target
    congr 1
    ext word
    simp
  let eS : Fin q ≃ S := (Fintype.equivOfCardEq (by simp [hq_card])).symm
  let col_inj : Fin L → S := fun a => eS ⟨a.val, lt_of_lt_of_le a.isLt hLq⟩
  have hcol_inj : Function.Injective col_inj := fun a b h =>
    Fin.ext (congrArg (fun z : Fin q => z.val) (eS.injective h))
  have hle_best : ∀ p : Fin m → Fin L → S → Bool,
      (∀ i a, PEqualNP.Outside.L_lib_630_aux.low (p i a)) →
      PEqualNP.Outside.L_lib_630_aux.hitSets (fun i a => PEqualNP.Outside.L_lib_630_aux.errSet (p i a)) ≤
        q ^ m - PEqualNP.Outside.L_lib_630_aux.occ q L m := by
    intro p hleg
    have hne : ∀ i a, (PEqualNP.Outside.L_lib_630_aux.errSet (p i a)).Nonempty := by
      intro i a
      have hodd := PEqualNP.Outside.L_lib_630_aux.low_imp_odd_errSet (p i a) (hleg i a)
      exact Finset.card_pos.mp (by rcases hodd with ⟨k, hk⟩; omega)
    let i0 : Fin m := ⟨0, by omega⟩
    have h1 := PEqualNP.Outside.L_lib_630_aux.replace_other_cols
      (fun i a => PEqualNP.Outside.L_lib_630_aux.errSet (p i a)) i0 hne col_inj hcol_inj
    let bad1 : Fin m → Fin L → Finset S :=
      fun i => if i = i0 then fun a => PEqualNP.Outside.L_lib_630_aux.errSet (p i0 a)
        else fun a => {col_inj a}
    have hne1 : ∀ a, (bad1 i0 a).Nonempty := by
      intro a
      simpa [bad1] using hne i0 a
    have h2 := PEqualNP.Outside.L_lib_630_aux.col_replace_le bad1 i0 hne1 col_inj hcol_inj
    have hupd : Function.update bad1 i0 (fun a => {col_inj a}) = fun _ a => {col_inj a} := by
      funext i
      by_cases hi : i = i0
      · subst hi; simp [bad1]
      · simp [bad1, hi]
    rw [hupd, PEqualNP.Outside.L_lib_630_aux.hitSets_injective_eq hq_card hLq (fun _ => col_inj)
      (fun _ => hcol_inj)] at h2
    exact le_trans h1 h2
  have hsub_gap : ∀ p : Fin m → Fin L → S → Bool,
      (∀ i a, PEqualNP.Outside.L_lib_630_aux.low (p i a)) →
      (¬ ∃ bad : Fin m → Fin L → S, (∀ i, Function.Injective (bad i)) ∧
        ∀ i a word, (p i a word ≠ PEqualNP.Outside.L_lib_630_aux.target word ↔ word = bad i a)) →
      PEqualNP.Outside.L_lib_630_aux.hitSets (fun i a => PEqualNP.Outside.L_lib_630_aux.errSet (p i a)) +
        (if L + 2 ≤ q then
          min (PEqualNP.Outside.L_lib_630_aux.occ (q - 2) (L - 2) (m - 1))
              (2 * PEqualNP.Outside.L_lib_630_aux.occ (q - 1) (L - 1) (m - 1))
          else PEqualNP.Outside.L_lib_630_aux.occ (q - 2) (L - 2) (m - 1)) ≤
        q ^ m - PEqualNP.Outside.L_lib_630_aux.occ q L m := by
    intro p hleg hnot_opt
    have hodd : ∀ i a, Odd (PEqualNP.Outside.L_lib_630_aux.errSet (p i a)).card :=
      fun i a => PEqualNP.Outside.L_lib_630_aux.low_imp_odd_errSet (p i a) (hleg i a)
    have hne : ∀ i a, (PEqualNP.Outside.L_lib_630_aux.errSet (p i a)).Nonempty := fun i a =>
      Finset.card_pos.mp (by rcases hodd i a with ⟨k, hk⟩; omega)
    by_cases hcoll : ∃ i0 : Fin m, ∃ a0 b0 : Fin L, a0 ≠ b0 ∧
        ∃ s0 : S, s0 ∈ PEqualNP.Outside.L_lib_630_aux.errSet (p i0 a0) ∧
          s0 ∈ PEqualNP.Outside.L_lib_630_aux.errSet (p i0 b0)
    · obtain ⟨i0, a0, b0, hab, s0, ha0, hb0⟩ := hcoll
      have hbd := PEqualNP.Outside.L_lib_630_aux.hitSets_collide_le hq_card hLq hL2
        (fun i a => PEqualNP.Outside.L_lib_630_aux.errSet (p i a)) hne i0 a0 b0 hab s0 ha0 hb0
      by_cases h : L + 2 ≤ q
      · simp only [h, ↓reduceIte]
        have hmin : min (PEqualNP.Outside.L_lib_630_aux.occ (q - 2) (L - 2) (m - 1))
            (2 * PEqualNP.Outside.L_lib_630_aux.occ (q - 1) (L - 1) (m - 1)) ≤
            PEqualNP.Outside.L_lib_630_aux.occ (q - 2) (L - 2) (m - 1) := min_le_left _ _
        omega
      · simp only [h, ↓reduceIte]
        exact hbd
    · push Not at hcoll
      have hex_big : ∃ i0 : Fin m, ∃ a0 : Fin L,
          3 ≤ (PEqualNP.Outside.L_lib_630_aux.errSet (p i0 a0)).card := by
        by_contra hno
        push Not at hno
        have hcard1 : ∀ i a, (PEqualNP.Outside.L_lib_630_aux.errSet (p i a)).card = 1 := by
          intro i a
          have hlt := hno i a
          rcases hodd i a with ⟨k, hk⟩
          omega
        have hex_s : ∀ i a, ∃ s : S, PEqualNP.Outside.L_lib_630_aux.errSet (p i a) = {s} :=
          fun i a => Finset.card_eq_one.mp (hcard1 i a)
        choose bad hbad using hex_s
        apply hnot_opt
        refine ⟨bad, fun i a b heq => ?_, fun i a word => ?_⟩
        · by_contra hab
          have ha_mem : bad i a ∈ PEqualNP.Outside.L_lib_630_aux.errSet (p i a) := by
            rw [hbad i a]; exact Finset.mem_singleton_self _
          have hb_mem : bad i a ∈ PEqualNP.Outside.L_lib_630_aux.errSet (p i b) := by
            rw [hbad i b, heq]; exact Finset.mem_singleton_self _
          exact hcoll i a b hab (bad i a) ha_mem hb_mem
        · have hmem : word ∈ PEqualNP.Outside.L_lib_630_aux.errSet (p i a) ↔ word = bad i a := by
            rw [hbad i a, Finset.mem_singleton]
          simpa [PEqualNP.Outside.L_lib_630_aux.errSet] using hmem
      obtain ⟨i0, a0, hbig⟩ := hex_big
      have hdisj_i0 : ∀ a b : Fin L, a ≠ b →
          Disjoint (PEqualNP.Outside.L_lib_630_aux.errSet (p i0 a))
            (PEqualNP.Outside.L_lib_630_aux.errSet (p i0 b)) := by
        intro a b hab
        rw [Finset.disjoint_left]
        exact fun s hs1 hs2 => hcoll i0 a b hab s hs1 hs2
      have hL2q : L + 2 ≤ q := by
        have hsum_le :
            ∑ a : Fin L, (PEqualNP.Outside.L_lib_630_aux.errSet (p i0 a)).card ≤ q := by
          rw [← Finset.card_biUnion (fun a _ b _ hab => hdisj_i0 a b hab), ← hq_card]
          exact Finset.card_le_univ _
        have hsum_ge :
            L + 2 ≤ ∑ a : Fin L, (PEqualNP.Outside.L_lib_630_aux.errSet (p i0 a)).card := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a0)]
          have hrest :
              L - 1 ≤ ∑ a ∈ Finset.univ.erase a0, (PEqualNP.Outside.L_lib_630_aux.errSet (p i0 a)).card := by
            calc L - 1 = (Finset.univ.erase a0).card := by
                  rw [Finset.card_erase_of_mem (Finset.mem_univ a0), Finset.card_univ, Fintype.card_fin]
              _ = ∑ _a ∈ Finset.univ.erase a0, 1 := by simp
              _ ≤ ∑ a ∈ Finset.univ.erase a0, (PEqualNP.Outside.L_lib_630_aux.errSet (p i0 a)).card :=
                  Finset.sum_le_sum (fun a _ => Finset.card_pos.mpr (hne i0 a))
          omega
        omega
      simp only [hL2q, ↓reduceIte]
      have hex3 : ∃ s1 ∈ PEqualNP.Outside.L_lib_630_aux.errSet (p i0 a0),
          ∃ s2 ∈ PEqualNP.Outside.L_lib_630_aux.errSet (p i0 a0),
          ∃ s3 ∈ PEqualNP.Outside.L_lib_630_aux.errSet (p i0 a0),
          s1 ≠ s2 ∧ s1 ≠ s3 ∧ s2 ≠ s3 := by
        obtain ⟨s1, hs1⟩ := hne i0 a0
        have hge2 : 1 < ((PEqualNP.Outside.L_lib_630_aux.errSet (p i0 a0)).erase s1).card := by
          rw [Finset.card_erase_of_mem hs1]
          omega
        obtain ⟨s2, hs2, s3, hs3, hs23⟩ := Finset.one_lt_card.mp hge2
        simp only [Finset.mem_erase] at hs2 hs3
        exact ⟨s1, hs1, s2, hs2.2, s3, hs3.2, Ne.symm hs2.1, Ne.symm hs3.1, hs23⟩
      obtain ⟨s1, hs1, s2, hs2, s3, hs3, hs12, hs13, hs23⟩ := hex3
      let col0 : Fin L → S := fun a =>
        if a = a0 then s1 else (hne i0 a).choose
      have hcol0_mem : ∀ a : Fin L, col0 a ∈ PEqualNP.Outside.L_lib_630_aux.errSet (p i0 a) := by
        intro a
        by_cases ha : a = a0
        · subst ha; simpa [col0] using hs1
        · simp only [col0, ha, ↓reduceIte]
          exact (hne i0 a).choose_spec
      have hcol0_inj : Function.Injective col0 := by
        intro a b hab
        by_contra hneab
        exact hcoll i0 a b hneab (col0 a) (hcol0_mem a) (hab ▸ hcol0_mem b)
      have hs2_ne : ∀ a : Fin L, s2 ≠ col0 a := by
        intro a
        by_cases ha : a = a0
        · subst ha; simp [col0, Ne.symm hs12]
        · intro heq
          exact hcoll i0 a0 a (Ne.symm ha) s2 hs2 (heq ▸ hcol0_mem a)
      have hs3_ne : ∀ a : Fin L, s3 ≠ col0 a := by
        intro a
        by_cases ha : a = a0
        · subst ha; simp [col0, Ne.symm hs13]
        · intro heq
          exact hcoll i0 a0 a (Ne.symm ha) s3 hs3 (heq ▸ hcol0_mem a)
      let bad_sub : Fin m → Fin L → Finset S := fun i a =>
        if i = i0 then
          if a = a0 then {col0 a0, s2, s3} else {col0 a}
        else PEqualNP.Outside.L_lib_630_aux.errSet (p i a)
      have hle1 : PEqualNP.Outside.L_lib_630_aux.hitSets
          (fun i a => PEqualNP.Outside.L_lib_630_aux.errSet (p i a)) ≤
          PEqualNP.Outside.L_lib_630_aux.hitSets bad_sub := by
        refine PEqualNP.Outside.L_lib_630_aux.hitSets_mono _ _ (fun i a => ?_)
        by_cases hi : i = i0
        · subst hi
          by_cases ha : a = a0
          · subst ha
            simp only [bad_sub, col0, ↓reduceIte]
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl
            · exact hs1
            · exact hs2
            · exact hs3
          · simp only [bad_sub, ha, ↓reduceIte, Finset.singleton_subset_iff]
            exact hcol0_mem a
        · simp only [bad_sub, hi, ↓reduceIte]
          exact Finset.Subset.refl _
      have hne_sub : ∀ i a, (bad_sub i a).Nonempty := by
        intro i a
        by_cases hi : i = i0
        · subst hi
          by_cases ha : a = a0 <;> simp [bad_sub, ha]
        · simp only [bad_sub, hi, ↓reduceIte]
          exact hne i a
      have hle2 := PEqualNP.Outside.L_lib_630_aux.replace_other_cols bad_sub i0 hne_sub col0 hcol0_inj
      have heq_bad :
          (fun i => if i = i0 then bad_sub i0 else fun a => {col0 a}) =
          (fun i a => if i = i0 ∧ a = a0 then {col0 a0, s2, s3} else {col0 a}) := by
        funext i a
        by_cases hi : i = i0
        · subst hi
          by_cases ha : a = a0 <;> simp [bad_sub, ha]
        · simp [hi]
      rw [heq_bad] at hle2
      have hbd := PEqualNP.Outside.L_lib_630_aux.hitSets_enlarge_eq hq_card hLq (fun _ => col0)
        (fun _ => hcol0_inj) i0 a0 s2 s3 hs2_ne hs3_ne hs23
      have hmin : min (PEqualNP.Outside.L_lib_630_aux.occ (q - 2) (L - 2) (m - 1))
          (2 * PEqualNP.Outside.L_lib_630_aux.occ (q - 1) (L - 1) (m - 1)) ≤
          2 * PEqualNP.Outside.L_lib_630_aux.occ (q - 1) (L - 1) (m - 1) := min_le_right _ _
      omega
  refine ⟨fun p hleg => ⟨?_, ?_⟩, ?_, hgap_pos, ?_, ?_⟩
  · rw [hhit_eq p]
    exact hle_best p hleg
  · constructor
    · intro hEq
      by_contra hnot
      have hbd := hsub_gap p hleg hnot
      rw [hhit_eq p] at hEq
      change PEqualNP.Outside.L_lib_630_aux.hitSets
          (fun i a => PEqualNP.Outside.L_lib_630_aux.errSet (p i a)) =
          q ^ m - PEqualNP.Outside.L_lib_630_aux.occ q L m at hEq
      omega
    · rintro ⟨bad, hinj, hbad⟩
      rw [hhit_eq p]
      have herr_eq : (fun i a => PEqualNP.Outside.L_lib_630_aux.errSet (p i a)) =
          fun i a => {bad i a} := by
        funext i a
        ext word
        rw [PEqualNP.Outside.L_lib_630_aux.errSet, Finset.mem_filter, Finset.mem_singleton]
        simp only [Finset.mem_univ, true_and]
        exact hbad i a word
      rw [herr_eq]
      exact PEqualNP.Outside.L_lib_630_aux.hitSets_injective_eq hq_card hLq bad hinj
  · have hex_f : ∀ (i : Fin m) (a : Fin L),
        ∃ f : S → Bool, PEqualNP.Outside.L_lib_630_aux.low f ∧
          PEqualNP.Outside.L_lib_630_aux.errSet f = {col_inj a} := by
      intro i a
      exact PEqualNP.Outside.L_lib_630_aux.odd_card_imp_low {col_inj a} (by simp)
    choose p hp using hex_f
    refine ⟨p, fun i a => (hp i a).1, ?_⟩
    rw [hhit_eq p]
    have herr_eq : (fun i a => PEqualNP.Outside.L_lib_630_aux.errSet (p i a)) =
        fun _ a => {col_inj a} := by
      funext i a
      exact (hp i a).2
    rw [herr_eq]
    exact PEqualNP.Outside.L_lib_630_aux.hitSets_injective_eq hq_card hLq (fun _ => col_inj)
      (fun _ => hcol_inj)
  · intro p hleg hlt
    rw [hhit_eq p] at hlt ⊢
    refine hsub_gap p hleg ?_
    rintro ⟨bad, hinj, hbad⟩
    have herr_eq : (fun i a => PEqualNP.Outside.L_lib_630_aux.errSet (p i a)) =
        fun i a => {bad i a} := by
      funext i a
      ext word
      rw [PEqualNP.Outside.L_lib_630_aux.errSet, Finset.mem_filter, Finset.mem_singleton]
      simp only [Finset.mem_univ, true_and]
      exact hbad i a word
    rw [herr_eq, PEqualNP.Outside.L_lib_630_aux.hitSets_injective_eq hq_card hLq bad hinj] at hlt
    exact lt_irrefl _ hlt
  · let i0 : Fin m := ⟨0, by omega⟩
    let a0 : Fin L := ⟨0, by omega⟩
    let b0 : Fin L := ⟨1, by omega⟩
    have hab : a0 ≠ b0 := by
      intro h
      have := congrArg Fin.val h
      simp [a0, b0] at this
    by_cases hcase : L + 2 ≤ q ∧
        2 * PEqualNP.Outside.L_lib_630_aux.occ (q - 1) (L - 1) (m - 1) ≤
          PEqualNP.Outside.L_lib_630_aux.occ (q - 2) (L - 2) (m - 1)
    · rcases hcase with ⟨hL2q, hen_le⟩
      let s2 : S := eS ⟨L, by omega⟩
      let s3 : S := eS ⟨L + 1, by omega⟩
      have hs2_ne : ∀ a : Fin L, s2 ≠ col_inj a := by
        intro a h
        have hv := congrArg Fin.val (eS.injective h)
        have ha := a.isLt
        dsimp at hv
        omega
      have hs3_ne : ∀ a : Fin L, s3 ≠ col_inj a := by
        intro a h
        have hv := congrArg Fin.val (eS.injective h)
        have ha := a.isLt
        dsimp at hv
        omega
      have hs23 : s2 ≠ s3 := by
        intro h
        have hv := congrArg Fin.val (eS.injective h)
        dsimp at hv
        omega
      let bad : Fin m → Fin L → Finset S := fun i a =>
        if i = i0 ∧ a = a0 then {col_inj a0, s2, s3} else {col_inj a}
      have hodd : ∀ i a, Odd (bad i a).card := by
        intro i a
        by_cases h : i = i0 ∧ a = a0
        · simp only [bad, h, and_self, ↓reduceIte]
          have h1 : col_inj a0 ∉ ({s2, s3} : Finset S) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨(hs2_ne a0).symm, (hs3_ne a0).symm⟩
          rw [Finset.card_insert_of_notMem h1, Finset.card_pair hs23]
          exact ⟨1, rfl⟩
        · simp [bad, h]
      have hex_f : ∀ i a, ∃ f : S → Bool, PEqualNP.Outside.L_lib_630_aux.low f ∧
          PEqualNP.Outside.L_lib_630_aux.errSet f = bad i a :=
        fun i a => PEqualNP.Outside.L_lib_630_aux.odd_card_imp_low (bad i a) (hodd i a)
      choose p hp using hex_f
      refine ⟨p, fun i a => (hp i a).1, ?_⟩
      rw [hhit_eq p]
      have herr_eq : (fun i a => PEqualNP.Outside.L_lib_630_aux.errSet (p i a)) = bad := by
        funext i a
        exact (hp i a).2
      rw [herr_eq]
      change PEqualNP.Outside.L_lib_630_aux.hitSets bad +
          (if L + 2 ≤ q then
            min (PEqualNP.Outside.L_lib_630_aux.occ (q - 2) (L - 2) (m - 1))
                (2 * PEqualNP.Outside.L_lib_630_aux.occ (q - 1) (L - 1) (m - 1))
            else PEqualNP.Outside.L_lib_630_aux.occ (q - 2) (L - 2) (m - 1)) =
          q ^ m - PEqualNP.Outside.L_lib_630_aux.occ q L m
      simp only [hL2q, ↓reduceIte, min_eq_right hen_le]
      exact PEqualNP.Outside.L_lib_630_aux.hitSets_enlarge_eq hq_card hLq (fun _ => col_inj)
        (fun _ => hcol_inj) i0 a0 s2 s3 hs2_ne hs3_ne hs23
    · let tab' : Fin m → Fin L → S := fun i a =>
        if i = i0 ∧ a = b0 then col_inj a0 else col_inj a
      have hex_f : ∀ i a, ∃ f : S → Bool, PEqualNP.Outside.L_lib_630_aux.low f ∧
          PEqualNP.Outside.L_lib_630_aux.errSet f = {tab' i a} :=
        fun i a => PEqualNP.Outside.L_lib_630_aux.odd_card_imp_low {tab' i a} (by simp)
      choose p hp using hex_f
      refine ⟨p, fun i a => (hp i a).1, ?_⟩
      rw [hhit_eq p]
      have herr_eq : (fun i a => PEqualNP.Outside.L_lib_630_aux.errSet (p i a)) =
          fun i a => {tab' i a} := by
        funext i a
        exact (hp i a).2
      rw [herr_eq]
      change PEqualNP.Outside.L_lib_630_aux.hitSets (fun i a => {tab' i a}) +
          (if L + 2 ≤ q then
            min (PEqualNP.Outside.L_lib_630_aux.occ (q - 2) (L - 2) (m - 1))
                (2 * PEqualNP.Outside.L_lib_630_aux.occ (q - 1) (L - 1) (m - 1))
            else PEqualNP.Outside.L_lib_630_aux.occ (q - 2) (L - 2) (m - 1)) =
          q ^ m - PEqualNP.Outside.L_lib_630_aux.occ q L m
      have hgap_eq :
          (if L + 2 ≤ q then
            min (PEqualNP.Outside.L_lib_630_aux.occ (q - 2) (L - 2) (m - 1))
                (2 * PEqualNP.Outside.L_lib_630_aux.occ (q - 1) (L - 1) (m - 1))
            else PEqualNP.Outside.L_lib_630_aux.occ (q - 2) (L - 2) (m - 1)) =
          PEqualNP.Outside.L_lib_630_aux.occ (q - 2) (L - 2) (m - 1) := by
        by_cases h : L + 2 ≤ q
        · simp only [h, ↓reduceIte]
          have hle : PEqualNP.Outside.L_lib_630_aux.occ (q - 2) (L - 2) (m - 1) ≤
              2 * PEqualNP.Outside.L_lib_630_aux.occ (q - 1) (L - 1) (m - 1) := by
            by_contra hlt
            exact hcase ⟨h, by omega⟩
          exact min_eq_left hle
        · simp [h]
      rw [hgap_eq]
      exact PEqualNP.Outside.L_lib_630_aux.hitSets_single_collide_eq hq_card hLq hL2
        (fun _ => col_inj) (fun _ => hcol_inj) i0 a0 b0 hab
