import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_446 : ∀ (n r : Nat) (wrong : Fin (2^n) → Fin r → Bool), 0 < r →
  (∀ x, 8*(Finset.univ.filter (fun tape : Fin r => wrong x tape = true)).card ≤ r) →
  ∃ advice : Fin (2*n+2) → Fin r, ∀ x : Fin (2^n),
    (Finset.univ.filter (fun j : Fin (2*n+2) => wrong x (advice j) = true)).card < n+1 := by
  intro n r wrong hr hbound
  let bad : Fin (2 ^ n) → Finset (Fin (2 * n + 2) → Fin r) := fun x =>
    Finset.univ.filter (fun adv =>
      n + 1 ≤ (Finset.univ.filter (fun j : Fin (2 * n + 2) => wrong x (adv j) = true)).card)
  have hbad_x : ∀ x : Fin (2 ^ n), 8 ^ (n + 1) * (bad x).card ≤ 4 ^ (n + 1) * r ^ (2 * n + 2) := by
    intro x
    let W : Finset (Fin r) := Finset.univ.filter (fun tape : Fin r => wrong x tape = true)
    have hW : 8 * W.card ≤ r := hbound x
    let slice : Finset (Fin (2 * n + 2)) → Finset (Fin (2 * n + 2) → Fin r) := fun S =>
      Fintype.piFinset (fun j : Fin (2 * n + 2) => if j ∈ S then W else Finset.univ)
    have hsub : bad x ⊆ ((Finset.univ : Finset (Fin (2 * n + 2))).powersetCard (n + 1)).biUnion slice := by
      intro adv hadv
      have hcard : n + 1 ≤ (Finset.univ.filter (fun j : Fin (2 * n + 2) => wrong x (adv j) = true)).card :=
        (Finset.mem_filter.mp hadv).2
      rcases Finset.exists_subset_card_eq hcard with ⟨S, hSsub, hScard⟩
      refine Finset.mem_biUnion.mpr ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, hScard⟩, ?_⟩
      rw [Fintype.mem_piFinset]
      intro j
      split_ifs with hj
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp (hSsub hj)).2⟩
      · exact Finset.mem_univ _
    have hslice_card : ∀ S ∈ (Finset.univ : Finset (Fin (2 * n + 2))).powersetCard (n + 1),
        8 ^ (n + 1) * (slice S).card ≤ r ^ (2 * n + 2) := by
      intro S hS
      have hScard : S.card = n + 1 := (Finset.mem_powersetCard.mp hS).2
      have hcard_eq : (slice S).card = W.card ^ (n + 1) * r ^ (n + 1) := by
        dsimp only [slice]
        rw [Fintype.card_piFinset]
        have hprod : (∏ j : Fin (2 * n + 2), (if j ∈ S then W else Finset.univ).card) =
            ∏ j : Fin (2 * n + 2), (if j ∈ S then W.card else r) := by
          apply Finset.prod_congr rfl
          intro j _
          split_ifs
          · rfl
          · simp
        rw [hprod, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
        have h1 : (Finset.univ.filter (fun j : Fin (2 * n + 2) => j ∈ S)).card = n + 1 := by
          have : Finset.univ.filter (fun j : Fin (2 * n + 2) => j ∈ S) = S := by ext j; simp
          rw [this, hScard]
        have h2 : (Finset.univ.filter (fun j : Fin (2 * n + 2) => j ∉ S)).card = n + 1 := by
          have : Finset.univ.filter (fun j : Fin (2 * n + 2) => j ∉ S) = Sᶜ := by ext j; simp
          rw [this, Finset.card_compl, Fintype.card_fin, hScard]
          omega
        rw [h1, h2]
      rw [hcard_eq]
      calc 8 ^ (n + 1) * (W.card ^ (n + 1) * r ^ (n + 1))
          = (8 * W.card) ^ (n + 1) * r ^ (n + 1) := by rw [mul_pow, mul_assoc]
        _ ≤ r ^ (n + 1) * r ^ (n + 1) :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hW (n + 1))
        _ = r ^ (2 * n + 2) := by rw [← pow_add]; congr 1; omega
    have hpow_le : ((Finset.univ : Finset (Fin (2 * n + 2))).powersetCard (n + 1)).card ≤ 4 ^ (n + 1) := by
      have h1 : ((Finset.univ : Finset (Fin (2 * n + 2))).powersetCard (n + 1)).card ≤
          (Finset.univ : Finset (Fin (2 * n + 2))).powerset.card :=
        Finset.card_le_card (fun T hT => Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hT).1)
      rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin] at h1
      have h2 : 2 ^ (2 * n + 2) = 4 ^ (n + 1) := by
        rw [show 2 * n + 2 = 2 * (n + 1) by omega, pow_mul]
        norm_num
      omega
    calc 8 ^ (n + 1) * (bad x).card
        ≤ 8 ^ (n + 1) * (((Finset.univ : Finset (Fin (2 * n + 2))).powersetCard (n + 1)).biUnion slice).card :=
          Nat.mul_le_mul_left _ (Finset.card_le_card hsub)
      _ ≤ 8 ^ (n + 1) * ∑ S ∈ (Finset.univ : Finset (Fin (2 * n + 2))).powersetCard (n + 1), (slice S).card :=
          Nat.mul_le_mul_left _ Finset.card_biUnion_le
      _ = ∑ S ∈ (Finset.univ : Finset (Fin (2 * n + 2))).powersetCard (n + 1), 8 ^ (n + 1) * (slice S).card :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ _S ∈ (Finset.univ : Finset (Fin (2 * n + 2))).powersetCard (n + 1), r ^ (2 * n + 2) :=
          Finset.sum_le_sum hslice_card
      _ = ((Finset.univ : Finset (Fin (2 * n + 2))).powersetCard (n + 1)).card * r ^ (2 * n + 2) := by
          simp
      _ ≤ 4 ^ (n + 1) * r ^ (2 * n + 2) := Nat.mul_le_mul_right _ hpow_le
  have htot : (Finset.univ.biUnion bad).card < Fintype.card (Fin (2 * n + 2) → Fin r) := by
    have hcard_all : Fintype.card (Fin (2 * n + 2) → Fin r) = r ^ (2 * n + 2) := by
      simp
    rw [hcard_all]
    have hmul : 8 ^ (n + 1) * (Finset.univ.biUnion bad).card < 8 ^ (n + 1) * r ^ (2 * n + 2) := by
      have h1 : 8 ^ (n + 1) * (Finset.univ.biUnion bad).card ≤
          2 ^ n * (4 ^ (n + 1) * r ^ (2 * n + 2)) := by
        calc 8 ^ (n + 1) * (Finset.univ.biUnion bad).card
            ≤ 8 ^ (n + 1) * ∑ x : Fin (2 ^ n), (bad x).card :=
              Nat.mul_le_mul_left _ Finset.card_biUnion_le
          _ = ∑ x : Fin (2 ^ n), 8 ^ (n + 1) * (bad x).card := Finset.mul_sum _ _ _
          _ ≤ ∑ _x : Fin (2 ^ n), 4 ^ (n + 1) * r ^ (2 * n + 2) :=
              Finset.sum_le_sum (fun x _ => hbad_x x)
          _ = 2 ^ n * (4 ^ (n + 1) * r ^ (2 * n + 2)) := by simp
      have h2 : 2 ^ n * 4 ^ (n + 1) * 2 = 8 ^ (n + 1) := by
        calc 2 ^ n * 4 ^ (n + 1) * 2
            = 2 ^ (n + 1) * 4 ^ (n + 1) := by rw [pow_succ]; ring
          _ = (2 * 4) ^ (n + 1) := (mul_pow 2 4 (n + 1)).symm
          _ = 8 ^ (n + 1) := by norm_num
      have hpow_pos : 0 < 2 ^ n * 4 ^ (n + 1) := by positivity
      have hr_pos : 0 < r ^ (2 * n + 2) := pow_pos hr _
      have hstrict : 2 ^ n * 4 ^ (n + 1) < 8 ^ (n + 1) := by omega
      have hlt : (2 ^ n * 4 ^ (n + 1)) * r ^ (2 * n + 2) < 8 ^ (n + 1) * r ^ (2 * n + 2) :=
        Nat.mul_lt_mul_of_pos_right hstrict hr_pos
      calc 8 ^ (n + 1) * (Finset.univ.biUnion bad).card
          ≤ 2 ^ n * (4 ^ (n + 1) * r ^ (2 * n + 2)) := h1
        _ = (2 ^ n * 4 ^ (n + 1)) * r ^ (2 * n + 2) := by ring
        _ < 8 ^ (n + 1) * r ^ (2 * n + 2) := hlt
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hne : Finset.univ.biUnion bad ≠ Finset.univ := by
    intro heq
    rw [heq, Finset.card_univ] at htot
    exact lt_irrefl _ htot
  have hex : ∃ adv : Fin (2 * n + 2) → Fin r, adv ∉ Finset.univ.biUnion bad := by
    by_contra hall
    push Not at hall
    apply hne
    ext adv
    simp [hall adv]
  rcases hex with ⟨adv, hadv⟩
  refine ⟨adv, fun x => ?_⟩
  have hnotbad : adv ∉ bad x := fun h => hadv (Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, h⟩)
  simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnotbad
  exact hnotbad
