import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_486_aux

def dist {q n : ℕ} (x y : Fin n → Fin q) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => x i ≠ y i)).card

lemma dist_self {q n : ℕ} (x : Fin n → Fin q) : dist x x = 0 := by
  simp [dist]

lemma list_sum_range_eq {f : ℕ → ℕ} :
    ∀ m : ℕ, ((List.range m).map f).sum = ∑ j ∈ Finset.range m, f j
  | 0 => rfl
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, add_zero, Finset.sum_range_succ, list_sum_range_eq m]

lemma card_diff_eq_subset {q n : ℕ} (hq : 2 ≤ q) (point : Fin n → Fin q) (S : Finset (Fin n)) :
    ((Finset.univ : Finset (Fin n → Fin q)).filter
      (fun c => (Finset.univ : Finset (Fin n)).filter (fun i => point i ≠ c i) = S)).card =
      (q - 1) ^ S.card := by
  let shift : ∀ (i : Fin n), Fin (q - 1) → Fin q := fun i k =>
    if h : k.val < (point i).val then ⟨k.val, by have := (point i).isLt; omega⟩
    else ⟨k.val + 1, by have := k.isLt; omega⟩
  have hshift_ne : ∀ (i : Fin n) (k : Fin (q - 1)), shift i k ≠ point i := by
    intro i k heq
    have hval := congrArg Fin.val heq
    simp only [shift] at hval
    split_ifs at hval with h <;> (dsimp only at hval; omega)
  have hshift_inj : ∀ (i : Fin n), Function.Injective (shift i) := by
    intro i k₁ k₂ heq
    have hval := congrArg Fin.val heq
    simp only [shift] at hval
    split_ifs at hval <;> (dsimp only at hval; exact Fin.ext (by omega))
  have hshift_surj : ∀ (i : Fin n) (v : Fin q), v ≠ point i → ∃ k : Fin (q - 1), shift i k = v := by
    intro i v hv
    have hvne : v.val ≠ (point i).val := fun h => hv (Fin.ext h)
    have hvlt := v.isLt
    have hplt := (point i).isLt
    by_cases h : v.val < (point i).val
    · refine ⟨⟨v.val, by omega⟩, ?_⟩
      apply Fin.ext; simp [shift, h]
    · refine ⟨⟨v.val - 1, by omega⟩, ?_⟩
      apply Fin.ext
      have hnot : ¬ v.val - 1 < (point i).val := by omega
      simp only [shift, hnot, ↓reduceDIte]
      omega
  let toWord : (S → Fin (q - 1)) → (Fin n → Fin q) := fun f i =>
    if hi : i ∈ S then shift i (f ⟨i, hi⟩) else point i
  have hcard_fun : Fintype.card (S → Fin (q - 1)) = (q - 1) ^ S.card := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  rw [← hcard_fun, ← Finset.card_univ]
  symm
  refine Finset.card_bij (fun f _ => toWord f) ?_ ?_ ?_
  · intro f _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, toWord]
    by_cases hi : i ∈ S
    · simp only [hi, ↓reduceDIte, iff_true]
      exact (hshift_ne i (f ⟨i, hi⟩)).symm
    · simp [hi]
  · intro f₁ _ f₂ _ heq
    funext ⟨i, hi⟩
    have h := congrFun heq i
    simp only [toWord, hi, ↓reduceDIte] at h
    exact hshift_inj i h
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    have hmem : ∀ i : S, c i.val ≠ point i.val := by
      intro ⟨i, hi⟩
      rw [← hc] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hi.symm
    let f : S → Fin (q - 1) := fun i =>
      if h : (c i.val).val < (point i.val).val then
        ⟨(c i.val).val, by have := (point i.val).isLt; omega⟩
      else
        ⟨(c i.val).val - 1, by have := (c i.val).isLt; have := hmem i; omega⟩
    refine ⟨f, Finset.mem_univ f, ?_⟩
    funext i
    by_cases hi : i ∈ S
    · simp only [toWord, hi, ↓reduceDIte, f]
      have hne : (c i).val ≠ (point i).val := fun h => hmem ⟨i, hi⟩ (Fin.ext h)
      by_cases hlt : (c i).val < (point i).val
      · apply Fin.ext; simp [shift, hlt]
      · apply Fin.ext
        have hnot : ¬ (c i).val - 1 < (point i).val := by omega
        simp only [hlt, ↓reduceDIte, shift, hnot]
        omega
    · simp only [toWord, hi, ↓reduceDIte]
      by_contra hne
      have hmem' : i ∈ (Finset.univ : Finset (Fin n)).filter (fun j => point j ≠ c j) := by
        simp [hne]
      rw [hc] at hmem'
      exact hi hmem'

lemma card_sphere {q n j : ℕ} (hq : 2 ≤ q) (point : Fin n → Fin q) :
    ((Finset.univ : Finset (Fin n → Fin q)).filter (fun c => dist point c = j)).card =
      Nat.choose n j * (q - 1) ^ j := by
  let diffSet : (Fin n → Fin q) → Finset (Fin n) := fun c =>
    (Finset.univ : Finset (Fin n)).filter (fun i => point i ≠ c i)
  have hmaps : ∀ c ∈ (Finset.univ : Finset (Fin n → Fin q)).filter (fun c => dist point c = j),
      diffSet c ∈ Finset.powersetCard j (Finset.univ : Finset (Fin n)) := by
    intro c hc
    rw [Finset.mem_filter] at hc
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hc.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hterm : ∀ S ∈ Finset.powersetCard j (Finset.univ : Finset (Fin n)),
      (((Finset.univ : Finset (Fin n → Fin q)).filter (fun c => dist point c = j)).filter
        (fun c => diffSet c = S)).card = (q - 1) ^ j := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    have hfilt : ((Finset.univ : Finset (Fin n → Fin q)).filter (fun c => dist point c = j)).filter
        (fun c => diffSet c = S) =
        (Finset.univ : Finset (Fin n → Fin q)).filter (fun c => diffSet c = S) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        change (diffSet c).card = j
        rw [h, hS.2]
    rw [hfilt, card_diff_eq_subset hq point S, hS.2]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_fin, smul_eq_mul]

lemma card_ball {q n r : ℕ} (hq : 2 ≤ q) (point : Fin n → Fin q) :
    ((Finset.univ : Finset (Fin n → Fin q)).filter (fun c => dist point c ≤ r)).card =
      ((List.range (r + 1)).map (fun j => Nat.choose n j * (q - 1) ^ j)).sum := by
  rw [list_sum_range_eq]
  have hmaps : ∀ c ∈ (Finset.univ : Finset (Fin n → Fin q)).filter (fun c => dist point c ≤ r),
      dist point c ∈ Finset.range (r + 1) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    exact Finset.mem_range.mpr (by omega)
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hfilt : ((Finset.univ : Finset (Fin n → Fin q)).filter (fun c => dist point c ≤ r)).filter
      (fun c => dist point c = j) =
      (Finset.univ : Finset (Fin n → Fin q)).filter (fun c => dist point c = j) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  rw [hfilt, card_sphere hq point]

lemma covering_code_alteration (q n r t : ℕ) (hq : 2 ≤ q) :
    let Word := Fin n → Fin q
    let A := q ^ n
    let V := ((List.range (r + 1)).map (fun j => Nat.choose n j * (q - 1) ^ j)).sum
    ∃ C : Finset Word, (∀ point : Word, ∃ c ∈ C, dist point c ≤ r) ∧
      C.card * A ^ t ≤ t * A ^ t + A * (A - V) ^ t := by
  intro Word A V
  have hcardW : Fintype.card Word = A := by
    simp [Word, A]
  have hcardL : Fintype.card (Fin t → Word) = A ^ t := by
    rw [Fintype.card_fun, hcardW, Fintype.card_fin]
  have hApos : 0 < A := by
    have : 0 < q := by omega
    exact Nat.pow_pos this
  have hAtpos : 0 < A ^ t := Nat.pow_pos hApos
  let misses : (Fin t → Word) → Finset Word := fun L =>
    (Finset.univ : Finset Word).filter (fun p => ∀ i : Fin t, ¬ dist p (L i) ≤ r)
  have houtside : ∀ point : Word,
      ((Finset.univ : Finset Word).filter (fun c => ¬ dist point c ≤ r)).card = A - V := by
    intro point
    have hsum : ((Finset.univ : Finset Word).filter (fun c => dist point c ≤ r)).card +
        ((Finset.univ : Finset Word).filter (fun c => ¬ dist point c ≤ r)).card =
        (Finset.univ : Finset Word).card := by
      rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1)),
        Finset.filter_union_filter_not_eq]
    rw [Finset.card_univ, hcardW, card_ball hq point] at hsum
    omega
  have hmiss_point : ∀ point : Word,
      ((Finset.univ : Finset (Fin t → Word)).filter (fun L => ∀ i : Fin t, ¬ dist point (L i) ≤ r)).card =
        (A - V) ^ t := by
    intro point
    let Out := (Finset.univ : Finset Word).filter (fun c => ¬ dist point c ≤ r)
    have hcardOut : Fintype.card Out = A - V := by
      rw [Fintype.card_coe]; exact houtside point
    have hcardFun : Fintype.card (Fin t → Out) = (A - V) ^ t := by
      rw [Fintype.card_fun, hcardOut, Fintype.card_fin]
    rw [← hcardFun, ← Finset.card_univ]
    symm
    refine Finset.card_bij (fun f _ i => (f i).val) ?_ ?_ ?_
    · intro f _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro i
      have hi := (f i).property
      simp only [Out, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hi
    · intro f₁ _ f₂ _ heq
      funext i
      exact Subtype.ext (congrFun heq i)
    · intro L hL
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hL
      refine ⟨fun i => ⟨L i, ?_⟩, Finset.mem_univ _, rfl⟩
      simp only [Out, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hL i
  have hdouble : ∑ L : Fin t → Word, (misses L).card = A * (A - V) ^ t := by
    have h1 : ∑ L : Fin t → Word, (misses L).card =
        ∑ L : Fin t → Word, ∑ point : Word, if ∀ i : Fin t, ¬ dist point (L i) ≤ r then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro L _
      exact Finset.card_filter _ _
    rw [h1, Finset.sum_comm]
    have h2 : ∀ point : Word,
        (∑ L : Fin t → Word, if ∀ i : Fin t, ¬ dist point (L i) ≤ r then 1 else 0) = (A - V) ^ t := by
      intro point
      rw [← Finset.card_filter]
      exact hmiss_point point
    rw [Finset.sum_congr rfl (fun p _ => h2 p), Finset.sum_const, Finset.card_univ, hcardW, smul_eq_mul]
  have hexL : ∃ L₀ : Fin t → Word, (misses L₀).card * A ^ t ≤ A * (A - V) ^ t := by
    by_contra hall
    push_neg at hall
    have hlt : ∑ _L : Fin t → Word, A * (A - V) ^ t <
        ∑ L : Fin t → Word, (misses L).card * A ^ t := by
      apply Finset.sum_lt_sum_of_nonempty
      · have hne : (Finset.univ : Finset (Fin t → Word)).card = A ^ t := by
          rw [Finset.card_univ, hcardL]
        exact Finset.card_pos.mp (by omega)
      · intro L _
        exact hall L
    rw [Finset.sum_const, Finset.card_univ, hcardL, smul_eq_mul, ← Finset.sum_mul, hdouble] at hlt
    rw [Nat.mul_comm] at hlt
    exact Nat.lt_irrefl _ hlt
  rcases hexL with ⟨L₀, hL₀⟩
  let C : Finset Word := (Finset.univ.image L₀) ∪ misses L₀
  refine ⟨C, ?_, ?_⟩
  · intro point
    by_cases hcov : ∃ i : Fin t, dist point (L₀ i) ≤ r
    · rcases hcov with ⟨i, hi⟩
      exact ⟨L₀ i, Finset.mem_union_left _ (Finset.mem_image_of_mem L₀ (Finset.mem_univ i)), hi⟩
    · push_neg at hcov
      refine ⟨point, Finset.mem_union_right _ ?_, ?_⟩
      · simp only [misses, Finset.mem_filter, Finset.mem_univ, true_and]
        intro i; exact Nat.not_le.mpr (hcov i)
      · rw [dist_self]; exact Nat.zero_le r
  · have hCcard : C.card ≤ t + (misses L₀).card := by
      calc C.card ≤ (Finset.univ.image L₀).card + (misses L₀).card := Finset.card_union_le _ _
        _ ≤ (Finset.univ : Finset (Fin t)).card + (misses L₀).card :=
            Nat.add_le_add_right Finset.card_image_le _
        _ = t + (misses L₀).card := by rw [Finset.card_fin]
    calc C.card * A ^ t
        ≤ (t + (misses L₀).card) * A ^ t := Nat.mul_le_mul_right _ hCcard
      _ = t * A ^ t + (misses L₀).card * A ^ t := Nat.add_mul _ _ _
      _ ≤ t * A ^ t + A * (A - V) ^ t := Nat.add_le_add_left hL₀ _

end PEqualNP.Outside.L_lib_486_aux

theorem PEqualNP.Outside.L_lib_486 :
∀ (q n r t : Nat), 2 ≤ q → r ≤ n →
  let Word := Fin n → Fin q
  let dist := fun (x y : Word) =>
    ((Finset.univ : Finset (Fin n)).filter (fun i => x i ≠ y i)).card
  let A := q^n
  let V := ((List.range (r+1)).map (fun j => Nat.choose n j * (q-1)^j)).sum
  ∃ C : Finset Word, (∀ point : Word, ∃ c ∈ C, dist point c ≤ r) ∧
    C.card * A^t ≤ t*A^t + A*(A-V)^t := by
  intro q n r t hq _ Word dist A V
  exact PEqualNP.Outside.L_lib_486_aux.covering_code_alteration q n r t hq
