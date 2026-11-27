import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_744

lemma card_badSets_eq_scoreTerm {α : Type} [DecidableEq α]
    (U B P : Finset α) (hBU : B ⊆ U) (hPU : P ⊆ U) (m : ℕ) :
    (((U \ P).powersetCard (m - P.card)).filter
      (fun Q => 64 * ((P ∪ Q) ∩ B).card < m)).card =
    ∑ z ∈ (Finset.range (m - P.card + 1)).filter (fun z => 64 * ((P ∩ B).card + z) < m),
      Nat.choose (B \ P).card z * Nat.choose ((U \ P) \ B).card (m - P.card - z) := by
  classical
  set d := m - P.card
  let lhsSet := ((U \ P).powersetCard d).filter (fun Q => 64 * ((P ∪ Q) ∩ B).card < m)
  let Z := (Finset.range (d + 1)).filter (fun z => 64 * ((P ∩ B).card + z) < m)
  have hmaps : ∀ Q ∈ lhsSet, (Q ∩ B).card ∈ Z := by
    intro Q hQ
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hQ
    obtain ⟨⟨hQsub, hQcard⟩, hlt⟩ := hQ
    have hdisj : Disjoint P Q := by
      rw [Finset.disjoint_left]
      intro x hxP hxQ
      exact (Finset.mem_sdiff.mp (hQsub hxQ)).2 hxP
    have hcard_un : ((P ∪ Q) ∩ B).card = (P ∩ B).card + (Q ∩ B).card := by
      rw [Finset.union_inter_distrib_right, Finset.card_union_of_disjoint]
      exact Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left hdisj
    rw [Finset.mem_filter, Finset.mem_range]
    have hle : (Q ∩ B).card ≤ d := by rw [← hQcard]; exact Finset.card_le_card Finset.inter_subset_left
    exact ⟨by omega, by omega⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Finset.mem_filter, Finset.mem_range] at hz
  obtain ⟨hz_lt, hz_64⟩ := hz
  have hz_le : z ≤ d := by omega
  let A := (B \ P).powersetCard z
  let C := ((U \ P) \ B).powersetCard (d - z)
  have hbij : (lhsSet.filter (fun Q => (Q ∩ B).card = z)).card = (A ×ˢ C).card := by
    refine Finset.card_bij (fun Q _ => (Q ∩ B, Q \ B)) ?_ ?_ ?_
    · intro Q hQ
      rw [Finset.mem_filter] at hQ
      obtain ⟨hQlhs, hQz⟩ := hQ
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hQlhs
      obtain ⟨⟨hQsub, hQcard⟩, _⟩ := hQlhs
      rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard]
      refine ⟨⟨?_, hQz⟩, ⟨?_, ?_⟩⟩
      · intro x hx
        rw [Finset.mem_inter] at hx
        exact Finset.mem_sdiff.mpr ⟨hx.2, (Finset.mem_sdiff.mp (hQsub hx.1)).2⟩
      · intro x hx
        rw [Finset.mem_sdiff] at hx
        exact Finset.mem_sdiff.mpr ⟨hQsub hx.1, hx.2⟩
      · dsimp only
        have hsplit := Finset.card_sdiff_add_card_inter Q B
        omega
    · intro Q1 _ Q2 _ heq
      have h1 : Q1 ∩ B = Q2 ∩ B := congrArg Prod.fst heq
      have h2 : Q1 \ B = Q2 \ B := congrArg Prod.snd heq
      ext x
      by_cases hx : x ∈ B
      · have h1x := Finset.ext_iff.mp h1 x
        simpa [hx] using h1x
      · have h2x := Finset.ext_iff.mp h2 x
        simpa [hx] using h2x
    · rintro ⟨X, Y⟩ hXY
      rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard] at hXY
      obtain ⟨⟨hXsub, hXcard⟩, ⟨hYsub, hYcard⟩⟩ := hXY
      have hdisjXY : Disjoint X Y := by
        rw [Finset.disjoint_left]
        intro x hxX hxY
        exact (Finset.mem_sdiff.mp (hYsub hxY)).2 (Finset.mem_sdiff.mp (hXsub hxX)).1
      have hXYsub : X ∪ Y ⊆ U \ P := by
        intro x hx
        rw [Finset.mem_union] at hx
        rcases hx with hxX | hxY
        · have hx' := Finset.mem_sdiff.mp (hXsub hxX)
          exact Finset.mem_sdiff.mpr ⟨hBU hx'.1, hx'.2⟩
        · exact (Finset.mem_sdiff.mp (hYsub hxY)).1
      have hXYcard : (X ∪ Y).card = d := by
        rw [Finset.card_union_of_disjoint hdisjXY, hXcard, hYcard]; omega
      have hXYinter : (X ∪ Y) ∩ B = X := by
        ext x; simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hxX | hxY, hxB⟩
          · exact hxX
          · exact False.elim ((Finset.mem_sdiff.mp (hYsub hxY)).2 hxB)
        · intro hxX
          exact ⟨Or.inl hxX, (Finset.mem_sdiff.mp (hXsub hxX)).1⟩
      have hXYsdiff : (X ∪ Y) \ B = Y := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hxX | hxY, hxB⟩
          · exact False.elim (hxB (Finset.mem_sdiff.mp (hXsub hxX)).1)
          · exact hxY
        · intro hxY
          exact ⟨Or.inr hxY, (Finset.mem_sdiff.mp (hYsub hxY)).2⟩
      have hdisjP : Disjoint P (X ∪ Y) := by
        rw [Finset.disjoint_left]
        intro x hxP hxXY
        exact (Finset.mem_sdiff.mp (hXYsub hxXY)).2 hxP
      have h64 : 64 * ((P ∪ (X ∪ Y)) ∩ B).card < m := by
        rw [Finset.union_inter_distrib_right, Finset.card_union_of_disjoint
            (Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left hdisjP),
            hXYinter, hXcard]
        exact hz_64
      refine ⟨X ∪ Y, ?_, Prod.ext hXYinter hXYsdiff⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hXYsub, hXYcard⟩, h64⟩, ?_⟩
      rw [hXYinter, hXcard]
  rw [hbij, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard]

lemma sum_badSets_insert {α : Type} [DecidableEq α]
    (U B P : Finset α) (m : ℕ) (hPm : P.card < m) :
    ∑ x ∈ U \ P,
      (((U \ insert x P).powersetCard (m - (insert x P).card)).filter
        (fun Q' => 64 * ((insert x P ∪ Q') ∩ B).card < m)).card =
    (m - P.card) *
      (((U \ P).powersetCard (m - P.card)).filter
        (fun Q => 64 * ((P ∪ Q) ∩ B).card < m)).card := by
  classical
  let badP := ((U \ P).powersetCard (m - P.card)).filter (fun Q => 64 * ((P ∪ Q) ∩ B).card < m)
  have hterm : ∀ x ∈ U \ P,
      (((U \ insert x P).powersetCard (m - (insert x P).card)).filter
        (fun Q' => 64 * ((insert x P ∪ Q') ∩ B).card < m)).card =
      (badP.filter (fun Q => x ∈ Q)).card := by
    intro x hx
    have hxU : x ∈ U := (Finset.mem_sdiff.mp hx).1
    have hxP : x ∉ P := (Finset.mem_sdiff.mp hx).2
    have hcard_ins : (insert x P).card = P.card + 1 := Finset.card_insert_of_notMem hxP
    refine Finset.card_bij (fun Q' _ => insert x Q') ?_ ?_ ?_
    · intro Q' hQ'
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hQ'
      obtain ⟨⟨hQ'sub, hQ'card⟩, h64⟩ := hQ'
      have hxQ' : x ∉ Q' := fun hm => (Finset.mem_sdiff.mp (hQ'sub hm)).2 (Finset.mem_insert_self _ _)
      have hsub : insert x Q' ⊆ U \ P := by
        intro y hy
        rw [Finset.mem_insert] at hy
        rcases hy with rfl | hyQ'
        · exact hx
        · have hy' := Finset.mem_sdiff.mp (hQ'sub hyQ')
          exact Finset.mem_sdiff.mpr ⟨hy'.1, fun hm => hy'.2 (Finset.mem_insert_of_mem hm)⟩
      have hcard : (insert x Q').card = m - P.card := by
        rw [Finset.card_insert_of_notMem hxQ', hQ'card, hcard_ins]; omega
      have hunion : P ∪ insert x Q' = insert x P ∪ Q' := by ext y; simp
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩, ?_⟩,
              Finset.mem_insert_self _ _⟩
      rw [hunion]; exact h64
    · intro Q1 hQ1 Q2 hQ2 heq
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hQ1 hQ2
      have hx1 : x ∉ Q1 := fun hm => (Finset.mem_sdiff.mp (hQ1.1.1 hm)).2 (Finset.mem_insert_self _ _)
      have hx2 : x ∉ Q2 := fun hm => (Finset.mem_sdiff.mp (hQ2.1.1 hm)).2 (Finset.mem_insert_self _ _)
      have h1 : (insert x Q1).erase x = Q1 := Finset.erase_insert hx1
      have h2 : (insert x Q2).erase x = Q2 := Finset.erase_insert hx2
      rw [← h1, ← h2, heq]
    · intro Q hQ
      rw [Finset.mem_filter] at hQ
      obtain ⟨hQbad, hxQ⟩ := hQ
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hQbad
      obtain ⟨⟨hQsub, hQcard⟩, h64⟩ := hQbad
      refine ⟨Q.erase x, ?_, Finset.insert_erase hxQ⟩
      rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro y hy
        rw [Finset.mem_erase] at hy
        have hy' := Finset.mem_sdiff.mp (hQsub hy.2)
        exact Finset.mem_sdiff.mpr ⟨hy'.1, fun hm => by
          rw [Finset.mem_insert] at hm
          rcases hm with rfl | hyP
          · exact hy.1 rfl
          · exact hy'.2 hyP⟩
      · rw [Finset.card_erase_of_mem hxQ, hQcard, hcard_ins]; omega
      · have hunion : insert x P ∪ Q.erase x = P ∪ Q := by
          ext y; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
          by_cases hyx : y = x
          · subst hyx; simp [hxQ]
          · simp [hyx]
        rw [hunion]; exact h64
  rw [Finset.sum_congr rfl hterm]
  have hdouble : ∑ x ∈ U \ P, (badP.filter (fun Q => x ∈ Q)).card =
      ∑ Q ∈ badP, (Q ∩ (U \ P)).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun Q _ => ?_
    simp only [← Finset.card_filter]
    congr 1; ext x; simp [and_comm]
  rw [hdouble]
  have hQcard : ∀ Q ∈ badP, (Q ∩ (U \ P)).card = m - P.card := by
    intro Q hQ
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hQ
    rw [Finset.inter_eq_left.mpr hQ.1.1, hQ.1.2]
  rw [Finset.sum_congr rfl hQcard, Finset.sum_const, smul_eq_mul, mul_comm]

lemma choose_absorb (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    k * Nat.choose N k = N * Nat.choose (N - 1) (k - 1) := by
  have hpos : 0 < (k - 1).factorial * (N - k).factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  apply Nat.eq_of_mul_eq_mul_right hpos
  have hk1 : k * (k - 1).factorial = k.factorial := by
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    exact (Nat.factorial_succ k').symm
  have hN1 : N * (N - 1).factorial = N.factorial := by
    obtain ⟨N', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    exact (Nat.factorial_succ N').symm
  have hsub : N - 1 - (k - 1) = N - k := by omega
  have h1 : Nat.choose N k * k.factorial * (N - k).factorial = N.factorial :=
    Nat.choose_mul_factorial_mul_factorial hkN
  have h2 : Nat.choose (N - 1) (k - 1) * (k - 1).factorial * (N - k).factorial = (N - 1).factorial := by
    rw [← hsub]; exact Nat.choose_mul_factorial_mul_factorial (by omega)
  calc k * Nat.choose N k * ((k - 1).factorial * (N - k).factorial)
      = Nat.choose N k * (k * (k - 1).factorial) * (N - k).factorial := by ring
    _ = Nat.choose N k * k.factorial * (N - k).factorial := by rw [hk1]
    _ = N.factorial := h1
    _ = N * (N - 1).factorial := hN1.symm
    _ = N * (Nat.choose (N - 1) (k - 1) * (k - 1).factorial * (N - k).factorial) := by rw [h2]
    _ = N * Nat.choose (N - 1) (k - 1) * ((k - 1).factorial * (N - k).factorial) := by ring

lemma descFactorial_ratio_le (N b j : ℕ) (h16 : N ≤ 16 * b) :
    16 ^ j * (N - b).descFactorial j ≤ 15 ^ j * N.descFactorial j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
    have hstep : 16 * (N - b - j) ≤ 15 * (N - j) := by omega
    calc 16 ^ j * 16 * ((N - b - j) * (N - b).descFactorial j)
        = (16 * (N - b - j)) * (16 ^ j * (N - b).descFactorial j) := by ring
      _ ≤ (15 * (N - j)) * (15 ^ j * N.descFactorial j) := Nat.mul_le_mul hstep ih
      _ = 15 ^ j * 15 * ((N - j) * N.descFactorial j) := by ring

lemma choose_descFactorial_id (N m j : ℕ) (hjm : j ≤ m) (hmN : m ≤ N) :
    Nat.choose (N - j) (m - j) * N.descFactorial j =
      j.factorial * Nat.choose m j * Nat.choose N m := by
  have hpos : 0 < (m - j).factorial * (N - m).factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  apply Nat.eq_of_mul_eq_mul_right hpos
  have hsub : N - j - (m - j) = N - m := by omega
  have h1 : Nat.choose (N - j) (m - j) * (m - j).factorial * (N - m).factorial = (N - j).factorial := by
    rw [← hsub]; exact Nat.choose_mul_factorial_mul_factorial (by omega)
  have h2 : N.descFactorial j * (N - j).factorial = N.factorial := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, mul_comm j.factorial]
    exact Nat.choose_mul_factorial_mul_factorial (by omega)
  have h3 : Nat.choose m j * j.factorial * (m - j).factorial = m.factorial :=
    Nat.choose_mul_factorial_mul_factorial hjm
  have h4 : Nat.choose N m * m.factorial * (N - m).factorial = N.factorial :=
    Nat.choose_mul_factorial_mul_factorial hmN
  calc Nat.choose (N - j) (m - j) * N.descFactorial j * ((m - j).factorial * (N - m).factorial)
      = N.descFactorial j * (Nat.choose (N - j) (m - j) * (m - j).factorial * (N - m).factorial) := by ring
    _ = N.descFactorial j * (N - j).factorial := by rw [h1]
    _ = N.factorial := h2
    _ = Nat.choose N m * m.factorial * (N - m).factorial := h4.symm
    _ = Nat.choose N m * (Nat.choose m j * j.factorial * (m - j).factorial) * (N - m).factorial := by rw [h3]
    _ = j.factorial * Nat.choose m j * Nat.choose N m * ((m - j).factorial * (N - m).factorial) := by ring

lemma hypergeom_term_le (N b m j : ℕ) (h16 : N ≤ 16 * b) (hjm : j ≤ m) (hmN : m ≤ N) :
    16 ^ j * (Nat.choose (N - b) j * Nat.choose (N - j) (m - j)) ≤
      15 ^ j * (Nat.choose m j * Nat.choose N m) := by
  have hpos : 0 < N.descFactorial j := Nat.descFactorial_pos.mpr (by omega)
  apply Nat.le_of_mul_le_mul_right _ hpos
  have hmul : Nat.choose (N - b) j * Nat.choose (N - j) (m - j) * N.descFactorial j =
      (N - b).descFactorial j * (Nat.choose m j * Nat.choose N m) := by
    calc Nat.choose (N - b) j * Nat.choose (N - j) (m - j) * N.descFactorial j
        = Nat.choose (N - b) j * (Nat.choose (N - j) (m - j) * N.descFactorial j) := by ring
      _ = Nat.choose (N - b) j * (j.factorial * Nat.choose m j * Nat.choose N m) := by
          rw [choose_descFactorial_id N m j hjm hmN]
      _ = (j.factorial * Nat.choose (N - b) j) * (Nat.choose m j * Nat.choose N m) := by ring
      _ = (N - b).descFactorial j * (Nat.choose m j * Nat.choose N m) := by
          rw [Nat.descFactorial_eq_factorial_mul_choose]
  calc 16 ^ j * (Nat.choose (N - b) j * Nat.choose (N - j) (m - j)) * N.descFactorial j
      = 16 ^ j * (Nat.choose (N - b) j * Nat.choose (N - j) (m - j) * N.descFactorial j) := by ring
    _ = (16 ^ j * (N - b).descFactorial j) * (Nat.choose m j * Nat.choose N m) := by rw [hmul]; ring
    _ ≤ (15 ^ j * N.descFactorial j) * (Nat.choose m j * Nat.choose N m) :=
        Nat.mul_le_mul_right _ (descFactorial_ratio_le N b j h16)
    _ = 15 ^ j * (Nat.choose m j * Nat.choose N m) * N.descFactorial j := by ring

lemma sum_two_pow_misses {α : Type} [DecidableEq α]
    (U B : Finset α) (hBU : B ⊆ U) (m : ℕ) :
    ∑ Q ∈ U.powersetCard m, 2 ^ (m - (Q ∩ B).card) =
      ∑ j ∈ Finset.range (m + 1),
        Nat.choose (U.card - B.card) j * Nat.choose (U.card - j) (m - j) := by
  classical
  have hlhs : ∑ Q ∈ U.powersetCard m, 2 ^ (m - (Q ∩ B).card) =
      ∑ Q ∈ U.powersetCard m, ((U \ B).powerset.filter (fun J => J ⊆ Q)).card := by
    refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [Finset.mem_powersetCard] at hQ
    have hfilt : (U \ B).powerset.filter (fun J => J ⊆ Q) = (Q \ B).powerset := by
      ext J
      simp only [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨hJ1, hJ2⟩ x hx
        exact Finset.mem_sdiff.mpr ⟨hJ2 hx, (Finset.mem_sdiff.mp (hJ1 hx)).2⟩
      · intro hJ
        refine ⟨fun x hx => Finset.mem_sdiff.mpr ⟨hQ.1 (Finset.mem_sdiff.mp (hJ hx)).1,
            (Finset.mem_sdiff.mp (hJ hx)).2⟩,
          fun x hx => (Finset.mem_sdiff.mp (hJ hx)).1⟩
    rw [hfilt, Finset.card_powerset]
    have hsplit := Finset.card_sdiff_add_card_inter Q B
    rw [hQ.2] at hsplit
    congr 1; omega
  rw [hlhs]
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  have hterm : ∀ J ∈ (U \ B).powerset,
      (∑ Q ∈ U.powersetCard m, if J ⊆ Q then 1 else 0) =
        if J.card ≤ m then Nat.choose (U.card - J.card) (m - J.card) else 0 := by
    intro J hJ
    have hJU : J ⊆ U := Finset.Subset.trans (Finset.mem_powerset.mp hJ) Finset.sdiff_subset
    rw [← Finset.card_filter]
    by_cases hJm : J.card ≤ m
    · rw [if_pos hJm]
      have hbij : ((U.powersetCard m).filter (fun Q => J ⊆ Q)).card =
          ((U \ J).powersetCard (m - J.card)).card := by
        refine Finset.card_bij (fun Q _ => Q \ J) ?_ ?_ ?_
        · intro Q hQ
          rw [Finset.mem_filter, Finset.mem_powersetCard] at hQ
          rw [Finset.mem_powersetCard]
          refine ⟨Finset.sdiff_subset_sdiff hQ.1.1 Finset.Subset.rfl, ?_⟩
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hQ.2, hQ.1.2]
        · intro Q1 hQ1 Q2 hQ2 heq
          rw [Finset.mem_filter] at hQ1 hQ2
          rw [← Finset.sdiff_union_of_subset hQ1.2, ← Finset.sdiff_union_of_subset hQ2.2, heq]
        · intro R hR
          rw [Finset.mem_powersetCard] at hR
          have hdisj : Disjoint R J := by
            rw [Finset.disjoint_left]
            intro x hxR hxJ
            exact (Finset.mem_sdiff.mp (hR.1 hxR)).2 hxJ
          refine ⟨R ∪ J, ?_, ?_⟩
          · rw [Finset.mem_filter, Finset.mem_powersetCard]
            refine ⟨⟨Finset.union_subset (Finset.Subset.trans hR.1 Finset.sdiff_subset) hJU, ?_⟩,
              Finset.subset_union_right⟩
            rw [Finset.card_union_of_disjoint hdisj, hR.2]; omega
          · exact Finset.union_sdiff_cancel_right hdisj
      rw [hbij, Finset.card_powersetCard, Finset.card_sdiff, Finset.inter_eq_left.mpr hJU]
    · rw [if_neg hJm]
      have hempty : (U.powersetCard m).filter (fun Q => J ⊆ Q) = ∅ := by
        ext Q; simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.notMem_empty, iff_false]
        rintro ⟨⟨_, hQm⟩, hJQ⟩
        have := Finset.card_le_card hJQ; omega
      rw [hempty, Finset.card_empty]
  rw [Finset.sum_congr rfl hterm]
  have hfilt_le : ∑ J ∈ (U \ B).powerset,
      (if J.card ≤ m then Nat.choose (U.card - J.card) (m - J.card) else 0) =
      ∑ J ∈ (U \ B).powerset.filter (fun J => J.card ≤ m),
        Nat.choose (U.card - J.card) (m - J.card) := by
    rw [Finset.sum_filter]
  rw [hfilt_le]
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range (m + 1)) (g := Finset.card)
      (fun J hJ => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hJ).2))]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj_le : j ≤ m := by rw [Finset.mem_range] at hj; omega
  have hconst : ∀ J ∈ ((U \ B).powerset.filter (fun J => J.card ≤ m)).filter (fun J => J.card = j),
      Nat.choose (U.card - J.card) (m - J.card) = Nat.choose (U.card - j) (m - j) := by
    intro J hJ; rw [(Finset.mem_filter.mp hJ).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
  congr 1
  have hpc : ((U \ B).powerset.filter (fun J => J.card ≤ m)).filter (fun J => J.card = j) =
      (U \ B).powersetCard j := by
    ext J
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hJsub, _⟩, hJcard⟩; exact ⟨hJsub, hJcard⟩
    · rintro ⟨hJsub, hJcard⟩; exact ⟨⟨hJsub, by omega⟩, hJcard⟩
  rw [hpc, Finset.card_powersetCard, Finset.card_sdiff, Finset.inter_eq_left.mpr hBU]

lemma pow_31_256_lt : 31 ^ 256 < 2 ^ 1269 := by
  have h2 : (2 : ℕ) ^ 1269 = ((2 ^ 250) ^ 5) * 2 ^ 19 := by
    rw [← pow_mul, ← pow_add]
  rw [h2]; norm_num

lemma fiber_bad_bound {α : Type} [DecidableEq α]
    (U B : Finset α) (hBU : B ⊆ U) (s : ℕ) (hs : 1 ≤ s)
    (hmU : 256 * s ≤ U.card) (h16 : U.card ≤ 16 * B.card) :
    2 ^ (3 * s + 3) *
      (((U.powersetCard (256 * s)).filter (fun Q => 64 * (Q ∩ B).card < 256 * s)).card) <
    Nat.choose U.card (256 * s) := by
  classical
  set m := 256 * s
  have hmarkov : 2 ^ (252 * s) *
      ((U.powersetCard m).filter (fun Q => 64 * (Q ∩ B).card < m)).card ≤
      ∑ Q ∈ U.powersetCard m, 2 ^ (m - (Q ∩ B).card) := by
    calc 2 ^ (252 * s) * ((U.powersetCard m).filter (fun Q => 64 * (Q ∩ B).card < m)).card
        = ∑ _Q ∈ (U.powersetCard m).filter (fun Q => 64 * (Q ∩ B).card < m), 2 ^ (252 * s) := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ Q ∈ (U.powersetCard m).filter (fun Q => 64 * (Q ∩ B).card < m), 2 ^ (m - (Q ∩ B).card) := by
          refine Finset.sum_le_sum fun Q hQ => ?_
          have hlt := (Finset.mem_filter.mp hQ).2
          exact Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ ∑ Q ∈ U.powersetCard m, 2 ^ (m - (Q ∩ B).card) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have h16m : 16 ^ m * ∑ Q ∈ U.powersetCard m, 2 ^ (m - (Q ∩ B).card) ≤
      31 ^ m * Nat.choose U.card m := by
    rw [sum_two_pow_misses U B hBU m, Finset.mul_sum]
    have hle : ∑ j ∈ Finset.range (m + 1),
        16 ^ m * (Nat.choose (U.card - B.card) j * Nat.choose (U.card - j) (m - j)) ≤
      ∑ j ∈ Finset.range (m + 1),
        (15 ^ j * 16 ^ (m - j) * Nat.choose m j) * Nat.choose U.card m := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjm : j ≤ m := by rw [Finset.mem_range] at hj; omega
      have hpow : 16 ^ m = 16 ^ (m - j) * 16 ^ j := by rw [← pow_add, Nat.sub_add_cancel hjm]
      rw [hpow]
      calc 16 ^ (m - j) * 16 ^ j * (Nat.choose (U.card - B.card) j * Nat.choose (U.card - j) (m - j))
          = 16 ^ (m - j) * (16 ^ j * (Nat.choose (U.card - B.card) j * Nat.choose (U.card - j) (m - j))) := by ring
        _ ≤ 16 ^ (m - j) * (15 ^ j * (Nat.choose m j * Nat.choose U.card m)) :=
            Nat.mul_le_mul_left _ (hypergeom_term_le U.card B.card m j h16 hjm hmU)
        _ = (15 ^ j * 16 ^ (m - j) * Nat.choose m j) * Nat.choose U.card m := by ring
    refine le_trans hle ?_
    rw [← Finset.sum_mul]
    have hbin : ∑ j ∈ Finset.range (m + 1), 15 ^ j * 16 ^ (m - j) * Nat.choose m j = 31 ^ m := by
      have := add_pow (15 : ℕ) 16 m
      simpa using this.symm
    rw [hbin]
  have hcomb : 2 ^ (1276 * s) *
      ((U.powersetCard m).filter (fun Q => 64 * (Q ∩ B).card < m)).card ≤
      31 ^ m * Nat.choose U.card m := by
    have hpow2 : 2 ^ (1276 * s) = 16 ^ m * 2 ^ (252 * s) := by
      have h16eq : (16 : ℕ) ^ m = 2 ^ (4 * m) := by
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
      rw [h16eq, ← pow_add]; congr 1; omega
    rw [hpow2, mul_assoc]
    exact le_trans (Nat.mul_le_mul_left _ hmarkov) h16m
  have h31lt : 2 ^ (3 * s + 3) * 31 ^ m < 2 ^ (1276 * s) := by
    have h1 : 31 ^ m < 2 ^ (1269 * s) := by
      have hlhs : 31 ^ m = (31 ^ 256) ^ s := by rw [← pow_mul]
      have hrhs : 2 ^ (1269 * s) = (2 ^ 1269) ^ s := by rw [← pow_mul]
      rw [hlhs, hrhs]
      exact Nat.pow_lt_pow_left pow_31_256_lt (by omega)
    have h2 : 2 ^ (3 * s + 3) * 31 ^ m < 2 ^ (3 * s + 3) * 2 ^ (1269 * s) :=
      Nat.mul_lt_mul_of_pos_left h1 (by positivity)
    have h3 : 2 ^ (3 * s + 3) * 2 ^ (1269 * s) ≤ 2 ^ (1276 * s) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hch_pos : 0 < Nat.choose U.card m := Nat.choose_pos hmU
  have hmul_lt : 2 ^ (1276 * s) * (2 ^ (3 * s + 3) *
      ((U.powersetCard m).filter (fun Q => 64 * (Q ∩ B).card < m)).card) <
      2 ^ (1276 * s) * Nat.choose U.card m := by
    calc 2 ^ (1276 * s) * (2 ^ (3 * s + 3) *
          ((U.powersetCard m).filter (fun Q => 64 * (Q ∩ B).card < m)).card)
        = 2 ^ (3 * s + 3) * (2 ^ (1276 * s) *
          ((U.powersetCard m).filter (fun Q => 64 * (Q ∩ B).card < m)).card) := by ring
      _ ≤ 2 ^ (3 * s + 3) * (31 ^ m * Nat.choose U.card m) := Nat.mul_le_mul_left _ hcomb
      _ = (2 ^ (3 * s + 3) * 31 ^ m) * Nat.choose U.card m := by ring
      _ < 2 ^ (1276 * s) * Nat.choose U.card m := Nat.mul_lt_mul_of_pos_right h31lt hch_pos
  exact Nat.lt_of_mul_lt_mul_left hmul_lt

end PEqualNP.Outside.L_lib_744

open PEqualNP.Outside.L_lib_744 in
theorem PEqualNP.Outside.L_lib_744 : ∀ s : ℕ, 4 ≤ s →
  let F := ZMod 2
  let W := Fin s → F
  let R := Fin 3 → F
  let U : Finset W := Finset.univ.erase 0
  let m := min (256*s) U.card
  let E := (Fin 3 → W) × R
  let fiber := fun e : E => U.filter (fun y =>
    ∀ i : Fin 3, (∑ j : Fin s, e.1 i j * y j) = e.2 i)
  let tests := (Finset.univ : Finset E).filter (fun e => U.card ≤ 16*(fiber e).card)
  let score := fun P : Finset W =>
    let d := m-P.card
    ∑ e ∈ tests,
      let B := fiber e
      ∑ z ∈ (Finset.range (d+1)).filter (fun z => 64*((P ∩ B).card+z) < m),
        Nat.choose (B \ P).card z *
          Nat.choose ((U \ P) \ B).card (d-z)
  let greedy := fun walk : ℕ → Finset W =>
    walk 0 = ∅ ∧ ∀ i : ℕ, i < m →
      ∃ y ∈ U \ walk i, walk (i+1) = insert y (walk i) ∧
        ∀ x ∈ U \ walk i, score (walk (i+1)) ≤ score (insert x (walk i))
  (∃ walk, greedy walk) ∧ ∀ walk, greedy walk →
    walk m ⊆ U ∧ (walk m).card = m ∧ ∀ e ∈ tests, m ≤ 64*((walk m ∩ fiber e).card) := by
  classical
  intro s hs F W R U m E fiber tests score greedy
  have hm_le_U : m ≤ U.card := min_le_right _ _
  have hfiber_sub : ∀ e : E, fiber e ⊆ U := fun e => Finset.filter_subset _ _
  constructor
  · -- Existence of a greedy walk
    let stepG : Finset W → Finset W := fun P =>
      if hne : (U \ P).Nonempty then
        insert ((Finset.exists_min_image (U \ P) (fun x => score (insert x P)) hne).choose) P
      else P
    let walk : ℕ → Finset W := fun i => Nat.rec ∅ (fun _ prev => stepG prev) i
    have hwalk_inv : ∀ i : ℕ, i ≤ m → walk i ⊆ U ∧ (walk i).card = i := by
      intro i
      induction i with
      | zero => intro _; exact ⟨Finset.empty_subset _, Finset.card_empty⟩
      | succ i ih =>
        intro hi
        obtain ⟨hsub, hcard⟩ := ih (by omega)
        have hne : (U \ walk i).Nonempty := by
          apply Finset.card_pos.mp
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hcard]; omega
        have hw_succ : walk (i + 1) =
            insert ((Finset.exists_min_image (U \ walk i) (fun x => score (insert x (walk i))) hne).choose)
              (walk i) := by
          change stepG (walk i) = _
          dsimp only [stepG]; rw [dif_pos hne]
        have hy_mem : (Finset.exists_min_image (U \ walk i) (fun x => score (insert x (walk i))) hne).choose ∈
            U \ walk i :=
          (Finset.exists_min_image (U \ walk i) (fun x => score (insert x (walk i))) hne).choose_spec.1
        rw [hw_succ]
        refine ⟨Finset.insert_subset (Finset.mem_sdiff.mp hy_mem).1 hsub, ?_⟩
        rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hy_mem).2, hcard]
    refine ⟨walk, rfl, fun i hi => ?_⟩
    obtain ⟨hsub, hcard⟩ := hwalk_inv i (by omega)
    have hne : (U \ walk i).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, hcard]; omega
    let hmin := Finset.exists_min_image (U \ walk i) (fun x => score (insert x (walk i))) hne
    refine ⟨hmin.choose, hmin.choose_spec.1, ?_, fun x hx => ?_⟩
    · change stepG (walk i) = _; dsimp only [stepG]; rw [dif_pos hne]
    · have hw_eq : walk (i + 1) = insert hmin.choose (walk i) := by
        change stepG (walk i) = _; dsimp only [stepG]; rw [dif_pos hne]
      rw [hw_eq]
      exact hmin.choose_spec.2 x hx
  · -- Any greedy walk satisfies the bound
    intro walk hgreedy
    obtain ⟨hw0, hwstep⟩ := hgreedy
    have hwalk_inv : ∀ i : ℕ, i ≤ m → walk i ⊆ U ∧ (walk i).card = i := by
      intro i
      induction i with
      | zero => intro _; rw [hw0]; exact ⟨Finset.empty_subset _, Finset.card_empty⟩
      | succ i ih =>
        intro hi
        obtain ⟨hsub, hcard⟩ := ih (by omega)
        obtain ⟨y, hy, hweq, _⟩ := hwstep i (by omega)
        rw [hweq]
        refine ⟨Finset.insert_subset (Finset.mem_sdiff.mp hy).1 hsub, ?_⟩
        rw [Finset.card_insert_of_notMem (Finset.mem_sdiff.mp hy).2, hcard]
    obtain ⟨hsub_m, hcard_m⟩ := hwalk_inv m le_rfl
    refine ⟨hsub_m, hcard_m, ?_⟩
    by_cases hsmall : U.card ≤ 256 * s
    · -- Case m = U.card: walk m = U
      have hm_eq : m = U.card := min_eq_right hsmall
      have hwalk_eq : walk m = U := Finset.eq_of_subset_of_card_le hsub_m (by omega)
      intro e he
      rw [hwalk_eq, Finset.inter_eq_right.mpr (hfiber_sub e), hm_eq]
      have h16 := (Finset.mem_filter.mp he).2
      omega
    · -- Case 256 * s < U.card: m = 256 * s
      have hm_eq : m = 256 * s := min_eq_left (by omega)
      have hscore_eq : ∀ P : Finset W, P ⊆ U →
          score P = ∑ e ∈ tests,
            (((U \ P).powersetCard (m - P.card)).filter
              (fun Q => 64 * ((P ∪ Q) ∩ fiber e).card < m)).card := by
        intro P hPU
        dsimp only [score]
        refine Finset.sum_congr rfl fun e _ => ?_
        exact (card_badSets_eq_scoreTerm U (fiber e) P (hfiber_sub e) hPU m).symm
      have hstep_avg : ∀ i : ℕ, i < m →
          (U.card - i) * score (walk (i + 1)) ≤ (m - i) * score (walk i) := by
        intro i hi
        obtain ⟨hsub_i, hcard_i⟩ := hwalk_inv i (by omega)
        obtain ⟨y, hy, hweq, hmin⟩ := hwstep i hi
        have hsum_ins : ∑ x ∈ U \ walk i, score (insert x (walk i)) =
            (m - i) * score (walk i) := by
          have h1 : ∀ x ∈ U \ walk i,
              score (insert x (walk i)) = ∑ e ∈ tests,
                (((U \ insert x (walk i)).powersetCard (m - (insert x (walk i)).card)).filter
                  (fun Q' => 64 * ((insert x (walk i) ∪ Q') ∩ fiber e).card < m)).card := by
            intro x hx
            exact hscore_eq (insert x (walk i)) (Finset.insert_subset (Finset.mem_sdiff.mp hx).1 hsub_i)
          rw [Finset.sum_congr rfl h1, Finset.sum_comm, hscore_eq (walk i) hsub_i, Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => ?_
          exact (sum_badSets_insert U (fiber e) (walk i) m (by omega)).trans
            (congrArg (· * _) (by rw [hcard_i]))
        have hcard_diff : (U \ walk i).card = U.card - i := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub_i, hcard_i]
        calc (U.card - i) * score (walk (i + 1))
            = ∑ _x ∈ U \ walk i, score (walk (i + 1)) := by rw [Finset.sum_const, smul_eq_mul, hcard_diff]
          _ ≤ ∑ x ∈ U \ walk i, score (insert x (walk i)) := Finset.sum_le_sum fun x hx => hmin x hx
          _ = (m - i) * score (walk i) := hsum_ins
      have htele : ∀ i : ℕ, i ≤ m →
          score (walk i) * Nat.choose U.card m ≤ score ∅ * Nat.choose (U.card - i) (m - i) := by
        intro i
        induction i with
        | zero => intro _; rw [hw0]; simp
        | succ i ih =>
          intro hi
          have hprev := ih (by omega)
          have havg := hstep_avg i (by omega)
          have habs := choose_absorb (U.card - i) (m - i) (by omega) (by omega)
          have hsub1 : U.card - i - 1 = U.card - (i + 1) := by omega
          have hsub2 : m - i - 1 = m - (i + 1) := by omega
          rw [hsub1, hsub2] at habs
          have hstep_ch : score (walk (i + 1)) * Nat.choose (U.card - i) (m - i) ≤
              score (walk i) * Nat.choose (U.card - (i + 1)) (m - (i + 1)) := by
            have hpos_Ui : 0 < U.card - i := by omega
            apply Nat.le_of_mul_le_mul_left _ hpos_Ui
            calc (U.card - i) * (score (walk (i + 1)) * Nat.choose (U.card - i) (m - i))
                = ((U.card - i) * score (walk (i + 1))) * Nat.choose (U.card - i) (m - i) := by ring
              _ ≤ ((m - i) * score (walk i)) * Nat.choose (U.card - i) (m - i) :=
                  Nat.mul_le_mul_right _ havg
              _ = score (walk i) * ((m - i) * Nat.choose (U.card - i) (m - i)) := by ring
              _ = score (walk i) * ((U.card - i) * Nat.choose (U.card - (i + 1)) (m - (i + 1))) := by rw [habs]
              _ = (U.card - i) * (score (walk i) * Nat.choose (U.card - (i + 1)) (m - (i + 1))) := by ring
          have hch_pos : 0 < Nat.choose (U.card - i) (m - i) := Nat.choose_pos (by omega)
          apply Nat.le_of_mul_le_mul_right _ hch_pos
          calc score (walk (i + 1)) * Nat.choose U.card m * Nat.choose (U.card - i) (m - i)
              = (score (walk (i + 1)) * Nat.choose (U.card - i) (m - i)) * Nat.choose U.card m := by ring
            _ ≤ (score (walk i) * Nat.choose (U.card - (i + 1)) (m - (i + 1))) * Nat.choose U.card m :=
                Nat.mul_le_mul_right _ hstep_ch
            _ = (score (walk i) * Nat.choose U.card m) * Nat.choose (U.card - (i + 1)) (m - (i + 1)) := by ring
            _ ≤ (score ∅ * Nat.choose (U.card - i) (m - i)) * Nat.choose (U.card - (i + 1)) (m - (i + 1)) :=
                Nat.mul_le_mul_right _ hprev
            _ = score ∅ * Nat.choose (U.card - (i + 1)) (m - (i + 1)) * Nat.choose (U.card - i) (m - i) := by ring
      have htele_m : score (walk m) * Nat.choose U.card m ≤ score ∅ := by
        have h := htele m le_rfl
        simpa [Nat.sub_self, Nat.choose_zero_right] using h
      have hscore0_lt : score ∅ < Nat.choose U.card m := by
        rw [hscore_eq ∅ (Finset.empty_subset _)]
        have hcard_E : Fintype.card E = 2 ^ (3 * s + 3) := by
          dsimp only [E, W, R, F]
          rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
              ZMod.card, Fintype.card_fin, Fintype.card_fin]
          rw [← pow_mul, ← pow_add]; congr 1; ring
        have htests_le : tests.card ≤ 2 ^ (3 * s + 3) := by
          calc tests.card ≤ (Finset.univ : Finset E).card := Finset.card_le_univ _
            _ = Fintype.card E := Finset.card_univ
            _ = 2 ^ (3 * s + 3) := hcard_E
        have hch_pos : 0 < Nat.choose U.card m := Nat.choose_pos hm_le_U
        have hsum_lt : 2 ^ (3 * s + 3) *
            ∑ e ∈ tests,
              (((U \ ∅).powersetCard (m - (∅ : Finset W).card)).filter
                (fun Q => 64 * ((∅ ∪ Q) ∩ fiber e).card < m)).card <
            2 ^ (3 * s + 3) * Nat.choose U.card m := by
          by_cases hte : tests = ∅
          · rw [hte, Finset.sum_empty, mul_zero]; positivity
          · have hte_pos : 0 < tests.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hte)
            rw [Finset.mul_sum]
            have heach : ∀ e ∈ tests,
                2 ^ (3 * s + 3) *
                  (((U \ ∅).powersetCard (m - (∅ : Finset W).card)).filter
                    (fun Q => 64 * ((∅ ∪ Q) ∩ fiber e).card < m)).card <
                Nat.choose U.card m := by
              intro e he
              simp only [Finset.sdiff_empty, Finset.card_empty, Nat.sub_zero, Finset.empty_union, hm_eq]
              exact fiber_bad_bound U (fiber e) (hfiber_sub e) s (by omega) (by omega)
                (Finset.mem_filter.mp he).2
            calc ∑ e ∈ tests, 2 ^ (3 * s + 3) *
                  (((U \ ∅).powersetCard (m - (∅ : Finset W).card)).filter
                    (fun Q => 64 * ((∅ ∪ Q) ∩ fiber e).card < m)).card
                < ∑ _e ∈ tests, Nat.choose U.card m :=
                  Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp hte_pos) heach
              _ = tests.card * Nat.choose U.card m := by rw [Finset.sum_const, smul_eq_mul]
              _ ≤ 2 ^ (3 * s + 3) * Nat.choose U.card m := Nat.mul_le_mul_right _ htests_le
        exact Nat.lt_of_mul_lt_mul_left hsum_lt
      have hscore_m_zero : score (walk m) = 0 := by
        have hch_pos : 0 < Nat.choose U.card m := Nat.choose_pos hm_le_U
        by_contra hne
        have h1 : 1 ≤ score (walk m) := by omega
        have hmul : Nat.choose U.card m ≤ score (walk m) * Nat.choose U.card m := by
          simpa using Nat.mul_le_mul_right (Nat.choose U.card m) h1
        omega
      intro e he
      by_contra hlt
      have hlt' : 64 * (walk m ∩ fiber e).card < m := by omega
      have hterm_ge : 1 ≤ ∑ z ∈ (Finset.range (m - (walk m).card + 1)).filter
          (fun z => 64 * ((walk m ∩ fiber e).card + z) < m),
          Nat.choose (fiber e \ walk m).card z *
            Nat.choose ((U \ walk m) \ fiber e).card (m - (walk m).card - z) := by
        rw [hcard_m, Nat.sub_self]
        have h0mem : 0 ∈ (Finset.range (0 + 1)).filter
            (fun z => 64 * ((walk m ∩ fiber e).card + z) < m) := by
          simp [hlt']
        have hle := Finset.single_le_sum (f := fun z =>
            Nat.choose (fiber e \ walk m).card z *
              Nat.choose ((U \ walk m) \ fiber e).card (0 - z))
          (fun _ _ => Nat.zero_le _) h0mem
        simpa using hle
      have hle_score := Finset.single_le_sum (f := fun e' =>
          ∑ z ∈ (Finset.range (m - (walk m).card + 1)).filter
            (fun z => 64 * ((walk m ∩ fiber e').card + z) < m),
            Nat.choose (fiber e' \ walk m).card z *
              Nat.choose ((U \ walk m) \ fiber e').card (m - (walk m).card - z))
        (fun _ _ => Nat.zero_le _) he
      have hge1 : 1 ≤ score (walk m) := le_trans hterm_ge hle_score
      omega
