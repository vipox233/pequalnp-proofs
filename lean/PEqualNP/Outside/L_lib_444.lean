import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_444

private def total {n q : Nat} (w : Fin n → Fin q) (s : Finset (Fin n)) : Nat :=
  ∑ i ∈ s, ((w i).val + 1)

private def restTotal {n q : Nat} (i : Fin n) (w : Fin n → Fin q) (s : Finset (Fin n)) : Nat :=
  ∑ j ∈ s.erase i, ((w j).val + 1)

private lemma total_of_mem {n q : Nat} (i : Fin n) (w : Fin n → Fin q)
    {s : Finset (Fin n)} (hi : i ∈ s) :
    total w s = ((w i).val + 1) + restTotal i w s :=
  (Finset.add_sum_erase s (fun j => (w j).val + 1) hi).symm

private lemma total_of_notMem {n q : Nat} (i : Fin n) (w : Fin n → Fin q)
    {s : Finset (Fin n)} (hi : i ∉ s) :
    total w s = restTotal i w s := by
  unfold total restTotal
  rw [Finset.erase_eq_of_notMem hi]

private lemma restTotal_congr {n q : Nat} (i : Fin n) {w₁ w₂ : Fin n → Fin q}
    (hagree : ∀ j, j ≠ i → w₁ j = w₂ j) (s : Finset (Fin n)) :
    restTotal i w₁ s = restTotal i w₂ s := by
  unfold restTotal
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hagree j (Finset.ne_of_mem_erase hj)]

private def badAt (n q : Nat) (family : Finset (Finset (Fin n))) (i : Fin n)
    (w : Fin n → Fin q) : Prop :=
  ∃ s₁ ∈ family, ∃ s₂ ∈ family, i ∈ s₁ ∧ i ∉ s₂ ∧
    (∀ z ∈ family, total w s₁ ≤ total w z) ∧
    (∀ z ∈ family, total w s₂ ≤ total w z)

private lemma badAt_unique {n q : Nat} (family : Finset (Finset (Fin n))) (i : Fin n)
    {w₁ w₂ : Fin n → Fin q}
    (hagree : ∀ j, j ≠ i → w₁ j = w₂ j)
    (h₁ : badAt n q family i w₁) (h₂ : badAt n q family i w₂) :
    w₁ i = w₂ i := by
  rcases h₁ with ⟨s₁, hs₁, s₂, hs₂, his₁, hnis₂, hmin_s₁, hmin_s₂⟩
  rcases h₂ with ⟨t₁, ht₁, t₂, ht₂, hit₁, hnit₂, hmin_t₁, hmin_t₂⟩
  have h1 := hmin_s₁ t₁ ht₁
  have h2 := hmin_t₁ s₁ hs₁
  have h3 := hmin_s₂ t₂ ht₂
  have h4 := hmin_t₂ s₂ hs₂
  have h5 := hmin_s₁ s₂ hs₂
  have h6 := hmin_s₂ s₁ hs₁
  have h7 := hmin_t₁ t₂ ht₂
  have h8 := hmin_t₂ t₁ ht₁
  rw [total_of_mem i w₁ his₁, total_of_mem i w₁ hit₁] at h1
  rw [total_of_mem i w₂ hit₁, total_of_mem i w₂ his₁,
      ← restTotal_congr i hagree t₁, ← restTotal_congr i hagree s₁] at h2
  rw [total_of_notMem i w₁ hnis₂, total_of_notMem i w₁ hnit₂] at h3
  rw [total_of_notMem i w₂ hnit₂, total_of_notMem i w₂ hnis₂,
      ← restTotal_congr i hagree t₂, ← restTotal_congr i hagree s₂] at h4
  rw [total_of_mem i w₁ his₁, total_of_notMem i w₁ hnis₂] at h5
  rw [total_of_notMem i w₁ hnis₂, total_of_mem i w₁ his₁] at h6
  rw [total_of_mem i w₂ hit₁, total_of_notMem i w₂ hnit₂,
      ← restTotal_congr i hagree t₁, ← restTotal_congr i hagree t₂] at h7
  rw [total_of_notMem i w₂ hnit₂, total_of_mem i w₂ hit₁,
      ← restTotal_congr i hagree t₂, ← restTotal_congr i hagree t₁] at h8
  exact Fin.ext (by omega)

private lemma card_badAt_le (n q : Nat) (family : Finset (Finset (Fin n))) (i : Fin n)
    [DecidablePred (badAt n q family i)] :
    q * (Finset.univ.filter (badAt n q family i)).card ≤ Fintype.card (Fin n → Fin q) := by
  let B : Finset (Fin n → Fin q) := Finset.univ.filter (badAt n q family i)
  let S : Finset ((Fin n → Fin q) × Fin q) := B ×ˢ Finset.univ
  let f : (Fin n → Fin q) × Fin q → (Fin n → Fin q) := fun p => Function.update p.1 i p.2
  have hinj : Set.InjOn f (S : Set _) := by
    rintro ⟨w₁, c₁⟩ hp₁ ⟨w₂, c₂⟩ hp₂ hfeq
    rw [Finset.mem_coe, Finset.mem_product] at hp₁ hp₂
    have hw₁ : badAt n q family i w₁ := (Finset.mem_filter.mp hp₁.1).2
    have hw₂ : badAt n q family i w₂ := (Finset.mem_filter.mp hp₂.1).2
    have hc : c₁ = c₂ := by
      have h := congrFun hfeq i
      simpa [f] using h
    have hagree : ∀ j, j ≠ i → w₁ j = w₂ j := by
      intro j hj
      have h := congrFun hfeq j
      simpa [f, hj] using h
    have hi : w₁ i = w₂ i := badAt_unique family i hagree hw₁ hw₂
    have hw : w₁ = w₂ := by
      funext j
      by_cases hj : j = i
      · subst hj
        exact hi
      · exact hagree j hj
    exact Prod.ext hw hc
  have hcard : S.card ≤ (Finset.univ : Finset (Fin n → Fin q)).card :=
    Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, Finset.card_univ, mul_comm] at hcard
  exact hcard

private lemma isolation_lemma (n q : Nat) (family : Finset (Finset (Fin n)))
    (_hq : 0 < q) (hfam : family.Nonempty) :
    let good := Finset.univ.filter (fun assignment : Fin n → Fin q =>
      ∃ s ∈ family, ∀ z ∈ family, z ≠ s → total assignment s < total assignment z)
    q * (Fintype.card (Fin n → Fin q) - good.card) ≤ n * Fintype.card (Fin n → Fin q) := by
  classical
  intro good
  let B : Fin n → Finset (Fin n → Fin q) := fun i => Finset.univ.filter (badAt n q family i)
  have hsub : Finset.univ \ good ⊆ Finset.univ.biUnion B := by
    intro w hw
    have hngood : w ∉ good := (Finset.mem_sdiff.mp hw).2
    obtain ⟨s₁, hs₁, hmin₁⟩ := Finset.exists_min_image family (total w) hfam
    have hex₂ : ∃ s₂ ∈ family, s₂ ≠ s₁ ∧ ¬ (total w s₁ < total w s₂) := by
      by_contra h
      push Not at h
      apply hngood
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, s₁, hs₁, h⟩
    rcases hex₂ with ⟨s₂, hs₂, hne, hnotlt⟩
    have hmin₂ : ∀ z ∈ family, total w s₂ ≤ total w z := by
      intro z hz
      have h12 : total w s₂ ≤ total w s₁ := Nat.le_of_not_lt hnotlt
      exact le_trans h12 (hmin₁ z hz)
    have hdiff : ∃ i : Fin n, (i ∈ s₁ ∧ i ∉ s₂) ∨ (i ∈ s₂ ∧ i ∉ s₁) := by
      by_contra h
      push Not at h
      apply hne
      ext i
      have hi := h i
      tauto
    rcases hdiff with ⟨i, ⟨his₁, hnis₂⟩ | ⟨his₂, hnis₁⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
        Finset.mem_filter.mpr ⟨Finset.mem_univ w, s₁, hs₁, s₂, hs₂, his₁, hnis₂, hmin₁, hmin₂⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
        Finset.mem_filter.mpr ⟨Finset.mem_univ w, s₂, hs₂, s₁, hs₁, his₂, hnis₁, hmin₂, hmin₁⟩⟩
  have hcard_diff : (Finset.univ \ good).card = Fintype.card (Fin n → Fin q) - good.card := by
    have hdisj : Disjoint (Finset.univ \ good) good := disjoint_sdiff_self_left
    have hunion : (Finset.univ \ good) ∪ good = Finset.univ :=
      Finset.sdiff_union_of_subset (Finset.subset_univ good)
    have hadd : (Finset.univ \ good).card + good.card = Fintype.card (Fin n → Fin q) := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
    omega
  calc
    q * (Fintype.card (Fin n → Fin q) - good.card)
        = q * (Finset.univ \ good).card := by rw [hcard_diff]
    _ ≤ q * (Finset.univ.biUnion B).card := Nat.mul_le_mul_left q (Finset.card_le_card hsub)
    _ ≤ q * ∑ i : Fin n, (B i).card := Nat.mul_le_mul_left q Finset.card_biUnion_le
    _ = ∑ i : Fin n, q * (B i).card := Finset.mul_sum _ _ _
    _ ≤ ∑ _i : Fin n, Fintype.card (Fin n → Fin q) :=
        Finset.sum_le_sum fun i _ => card_badAt_le n q family i
    _ = n * Fintype.card (Fin n → Fin q) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end PEqualNP.Outside.L_lib_444

theorem PEqualNP.Outside.L_lib_444 :
    ∀ (n q : Nat) (family : Finset (Finset (Fin n))), 0 < q → family.Nonempty →
      let total := fun (w : Fin n → Fin q) (s : Finset (Fin n)) =>
        ∑ i ∈ s, ((w i).val+1)
      let good := Finset.univ.filter (fun assignment : Fin n → Fin q =>
        ∃ s ∈ family, ∀ z ∈ family, z ≠ s → total assignment s < total assignment z)
      q * (Fintype.card (Fin n → Fin q) - good.card) ≤ n * Fintype.card (Fin n → Fin q) := by
  intro n q family hq hfam
  exact PEqualNP.Outside.L_lib_444.isolation_lemma n q family hq hfam
