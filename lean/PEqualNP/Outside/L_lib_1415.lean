import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_1415 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let tag := fun (s w j : Nat) => Finset.Ico s (s+w*j)
let near := fun (a f : Nat) (W Y : Finset Nat) => (W \ Y).card ≤ a ∧ (Y \ W).card ≤ f
let inc := fun {m : Nat} (Y : Fin m → Finset Nat) => ∀ i j, i ≤ j → Y i ⊆ Y j
let trace := fun {m : Nat} (W : Fin m → Finset Nat) (r a f k : Nat) =>
  ∃ (lab : Fin k → Fin m) (Y : Fin k → Finset Nat), inc Y ∧
    (∀ i j, i.val+1=j.val → lab i ≠ lab j) ∧ ∀ i, Y i ⊆ Finset.range r ∧ near a f (W (lab i)) (Y i)
let base := fun (n m : Nat) => (n+2)*(m+1)
let size := fun (n m z : Nat) => base n m + m + z
let dim := fun (n m z : Nat) => 3*n+1+(2*n+1)*size n m z
let words := fun {n m : Nat} (F : Fin m → Finset (Fin n × Bool)) (z : Nat) (j : Fin (size n m z)) =>
  let t := m+1
  let left := t+z
  let i := j.val-left
  let pad := fun (C : Finset Nat) => C ∪ Finset.Ico (2*n) (2*n+(n+1-C.card))
  let A := if j.val < left then Finset.range (2*n) else if i < n*t then
    pad {2*(i/t), 2*(i/t)+1}
    else if h : i-n*t < m then
      pad ((F ⟨i-n*t,h⟩).image (fun l => 2*l.1.val + (if l.2 then 1 else 0)))
    else ∅
  A ∪ tag (3*n+1) (2*n+1) j.val
let score := fun {n m : Nat} (F : Fin m → Finset (Fin n × Bool)) =>
  Finset.univ.sup (fun v : Fin n → Bool =>
    (Finset.univ.filter (fun j : Fin m => ∃ l ∈ F j, v l.1 = l.2)).card)
∀ (n m z : Nat) (F : Fin m → Finset (Fin n × Bool)),
  let W := words F z
  (∀ j, W j ⊆ Finset.range (dim n m z)) ∧ (∀ i j, i < j → 2*n < (W j \ W i).card) ∧
  ∀ k : Nat, trace W (dim n m z) n n k ↔ k ≤ base n m + z + score F) := by
  generalize (fun a b : ℕ => Classical.propDecidable (a = b)) = inst
  intro tag near inc trace base size dim words score n m z F W
  have hN : size n m z = n*(m+1) + 2*(m+1) + m + z := by
    simp only [size, base]; ring
  have hsz : ∀ j : Fin (size n m z), j.val < n*(m+1) + 2*(m+1) + m + z := by
    intro j
    exact lt_of_lt_of_eq j.isLt hN
  have hF1 : ∀ j : Fin (size n m z), j.val < m+1+z → ∀ x, x ∈ W j ↔
      x < 2*n ∨ (3*n+1 ≤ x ∧ x < 3*n+1+(2*n+1)*j.val) := by
    intro j hj x
    simp only [W, words, tag]
    rw [if_pos hj]
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
  have hF2 : ∀ j : Fin (size n m z), ¬ (j.val < m+1+z) → j.val-(m+1+z) < n*(m+1) → ∀ x, x ∈ W j ↔
      (x = 2*((j.val-(m+1+z))/(m+1)) ∨ x = 2*((j.val-(m+1+z))/(m+1))+1 ∨ (2*n ≤ x ∧ x < 2*n+(n+1-2))) ∨
        (3*n+1 ≤ x ∧ x < 3*n+1+(2*n+1)*j.val) := by
    intro j hj hj2 x
    simp only [W, words, tag]
    rw [if_neg hj, if_pos hj2, Finset.card_pair (by omega)]
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_Ico]
    tauto
  obtain ⟨C, hC, hF3⟩ : ∃ C : Fin m → Finset ℕ,
      (∀ c x, x ∈ C c ↔ ∃ l ∈ F c, x = 2*l.1.val + l.2.toNat) ∧
      ∀ (j : Fin (size n m z)) (h : j.val-(m+1+z)-n*(m+1) < m), ¬ (j.val < m+1+z) →
        ¬ (j.val-(m+1+z) < n*(m+1)) → ∀ x, x ∈ W j ↔
        (x ∈ C ⟨_, h⟩ ∨ (2*n ≤ x ∧ x < 2*n+(n+1-(C ⟨_, h⟩).card))) ∨
          (3*n+1 ≤ x ∧ x < 3*n+1+(2*n+1)*j.val) := by
    refine ⟨fun c => (F c).image (fun l => 2*l.1.val + @ite _ (l.2 = true) (Classical.propDecidable _) 1 0), ?_, ?_⟩
    · intro c x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨⟨v, b⟩, hl, rfl⟩
        refine ⟨⟨v, b⟩, hl, ?_⟩
        cases b <;> simp
      · rintro ⟨⟨v, b⟩, hl, rfl⟩
        refine ⟨⟨v, b⟩, hl, ?_⟩
        cases b <;> simp
    · intro j h hj hj2 x
      simp only [W, words, tag]
      rw [if_neg hj, if_neg hj2, dif_pos h]
      simp only [Finset.mem_union, Finset.mem_Ico]
  have hF4 : ∀ j : Fin (size n m z), ¬ (j.val < m+1+z) → ¬ (j.val-(m+1+z) < n*(m+1)) →
      ¬ (j.val-(m+1+z)-n*(m+1) < m) → ∀ x, x ∈ W j ↔
        (3*n+1 ≤ x ∧ x < 3*n+1+(2*n+1)*j.val) := by
    intro j hj hj2 hj3 x
    simp only [W, words, tag]
    rw [if_neg hj, if_neg hj2, dif_neg hj3]
    simp only [Finset.mem_union, Finset.mem_Ico, Finset.notMem_empty, false_or]
  clear_value W
  have hsc1 : ∀ v : Fin n → Bool, ∃ T : Finset (Fin m),
      (∀ c, c ∈ T ↔ ∃ l ∈ F c, v l.1 = l.2) ∧ T.card ≤ score F := by
    intro v
    refine ⟨@Finset.filter _ (fun j : Fin m => ∃ l ∈ F j, v l.1 = l.2)
        (fun _ => Classical.propDecidable _) Finset.univ, ?_, ?_⟩
    · intro c
      exact ⟨fun h => ((@Finset.mem_filter _ _ (_) _ _).1 h).2,
        fun h => (@Finset.mem_filter _ _ (_) _ _).2 ⟨Finset.mem_univ _, h⟩⟩
    · exact Finset.le_sup (f := fun v : Fin n → Bool =>
        (@Finset.filter _ (fun j : Fin m => ∃ l ∈ F j, v l.1 = l.2)
          (fun _ => Classical.propDecidable _) Finset.univ).card) (s := @Finset.univ _ (_))
        (@Finset.mem_univ _ (_) v)
  have hsc2 : ∃ (a : Fin n → Bool) (T : Finset (Fin m)),
      (∀ c, c ∈ T ↔ ∃ l ∈ F c, a l.1 = l.2) ∧ T.card = score F := by
    obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup (@Finset.univ (Fin n → Bool) (_))
      ⟨fun _ => true, @Finset.mem_univ _ (_) _⟩
      (fun v : Fin n → Bool => (@Finset.filter _ (fun j : Fin m => ∃ l ∈ F j, v l.1 = l.2)
        (fun _ => Classical.propDecidable _) Finset.univ).card)
    refine ⟨a, @Finset.filter _ (fun j : Fin m => ∃ l ∈ F j, a l.1 = l.2)
        (fun _ => Classical.propDecidable _) Finset.univ, ?_, ?_⟩
    · intro c
      exact ⟨fun h => ((@Finset.mem_filter _ _ (_) _ _).1 h).2,
        fun h => (@Finset.mem_filter _ _ (_) _ _).2 ⟨Finset.mem_univ _, h⟩⟩
    · exact ha.symm
  have hClt : ∀ c x, x ∈ C c → x < 2*n := by
    intro c x hx
    obtain ⟨l, -, rfl⟩ := (hC c x).1 hx
    have := l.1.isLt
    have := Bool.toNat_le l.2
    omega
  have hT : ∀ (j : Fin (size n m z)) x, 3*n+1 ≤ x → (x ∈ W j ↔ x < 3*n+1+(2*n+1)*j.val) := by
    intro j x hx
    by_cases hj : j.val < m+1+z
    · rw [hF1 j hj]; omega
    · by_cases hj2 : j.val-(m+1+z) < n*(m+1)
      · rw [hF2 j hj hj2]
        have : (j.val-(m+1+z))/(m+1) < n := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj2)
        omega
      · by_cases hj3 : j.val-(m+1+z)-n*(m+1) < m
        · rw [hF3 j hj3 hj hj2]
          constructor
          · rintro ((h | h) | h)
            · exact absurd (hClt _ _ h) (by omega)
            · omega
            · omega
          · intro h
            exact Or.inr ⟨hx, h⟩
        · rw [hF4 j hj hj2 hj3]; omega
  have hbase : base n m = n*(m+1) + 2*(m+1) := by
    simp only [base]; ring
  have hdim : dim n m z = 3*n+1+(2*n+1)*(n*(m+1) + 2*(m+1) + m + z) := by
    simp only [dim, size, base]; ring
  refine ⟨?_, ?_, ?_⟩
  · intro j x hx
    rw [Finset.mem_range, hdim]
    have h1 := Nat.mul_le_mul_left (2*n+1) (le_of_lt (hsz j))
    by_cases hx3 : 3*n+1 ≤ x
    · have := (hT j x hx3).1 hx
      omega
    · omega
  · intro i j hij
    have hij' : i.val + 1 ≤ j.val := hij
    have h1 := Nat.mul_le_mul_left (2*n+1) hij'
    have h2 : (2*n+1)*(i.val+1) = (2*n+1)*i.val + (2*n+1) := by ring
    have hsub : Finset.Ico (3*n+1 + (2*n+1)*i.val) (3*n+1 + (2*n+1)*j.val) ⊆ W j \ W i := by
      intro x hx
      simp only [Finset.mem_Ico] at hx
      rw [Finset.mem_sdiff, hT j x (by omega), hT i x (by omega)]
      omega
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Ico] at hc
    omega
  · intro k
    constructor
    · rintro ⟨lab, Y, hinc, hne, hYn⟩
      have hinc' : ∀ i j : Fin k, i ≤ j → Y i ⊆ Y j := hinc
      have hnear : ∀ i : Fin k, (W (lab i) \ Y i).card ≤ n ∧ (Y i \ W (lab i)).card ≤ n :=
        fun i => (hYn i).2
      have hmono : ∀ i i' : Fin k, i ≤ i' → (lab i).val ≤ (lab i').val := by
        intro i i' hii
        by_contra hlt
        have hlt' : (lab i').val + 1 ≤ (lab i).val := by omega
        have h1 := Nat.mul_le_mul_left (2*n+1) hlt'
        have h2 : (2*n+1)*((lab i').val+1) = (2*n+1)*(lab i').val + (2*n+1) := by ring
        have hsub : Finset.Ico (3*n+1+(2*n+1)*(lab i').val) (3*n+1+(2*n+1)*(lab i).val) ⊆
            (W (lab i) \ Y i) ∪ (Y i' \ W (lab i')) := by
          intro x hx
          rw [Finset.mem_Ico] at hx
          rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_sdiff, hT _ x (by omega),
            hT _ x (by omega)]
          by_cases hxY : x ∈ Y i
          · exact Or.inr ⟨hinc' i i' hii hxY, by omega⟩
          · exact Or.inl ⟨hx.2, hxY⟩
        have hc := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
        rw [Nat.card_Ico] at hc
        have := (hnear i).1
        have := (hnear i').2
        omega
      have hsm : ∀ i i' : Fin k, i < i' → (lab i).val < (lab i').val := by
        intro i i' hii
        have hii' : i.val < i'.val := hii
        have hi1 : i.val + 1 < k := by have := i'.isLt; omega
        have h1 := hmono i ⟨i.val+1, hi1⟩ (by rw [Fin.le_def]; simp)
        have h2 := hmono ⟨i.val+1, hi1⟩ i' (by rw [Fin.le_def]; simp; omega)
        have h3 := hne i ⟨i.val+1, hi1⟩ rfl
        have h4 : (lab i).val ≠ (lab ⟨i.val+1, hi1⟩).val := fun h => h3 (Fin.ext h)
        omega
      have hle : ∀ i i' : Fin k, (lab i).val < (lab i').val → i ≤ i' := by
        intro i i' h
        by_contra hc
        have := hmono i' i (le_of_lt (not_le.1 hc))
        omega
      have hinj : Function.Injective (fun i : Fin k => (lab i).val) := by
        intro a b h
        simp only at h
        rcases lt_trichotomy a b with h1 | h1 | h1
        · have := hsm _ _ h1; omega
        · exact h1
        · have := hsm _ _ h1; omega
      obtain ⟨S', hS'⟩ : ∃ S' : Finset ℕ, S' = (Finset.univ : Finset (Fin k)).image (fun i => (lab i).val) := ⟨_, rfl⟩
      have hS'card : S'.card = k := by
        rw [hS', Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      have hS'mem : ∀ x, x ∈ S' ↔ ∃ i : Fin k, (lab i).val = x := by
        intro x
        rw [hS']
        simp
      have hblock : ∀ a, a + (m+1) ≤ n*(m+1) + 2*(m+1) + m + z →
          (∀ i : Fin k, ¬ (a ≤ (lab i).val ∧ (lab i).val < a + (m+1))) →
          k + (m+1) ≤ n*(m+1) + 2*(m+1) + m + z := by
        intro a ha hno
        have hdisj : Disjoint S' (Finset.Ico a (a+(m+1))) := by
          rw [Finset.disjoint_left]
          intro x hx hx2
          obtain ⟨i, rfl⟩ := (hS'mem x).1 hx
          rw [Finset.mem_Ico] at hx2
          exact hno i hx2
        have hsub : S' ∪ Finset.Ico a (a+(m+1)) ⊆ Finset.range (n*(m+1) + 2*(m+1) + m + z) := by
          intro x hx
          rw [Finset.mem_union] at hx
          rw [Finset.mem_range]
          rcases hx with hx | hx
          · obtain ⟨i, rfl⟩ := (hS'mem x).1 hx
            exact hsz (lab i)
          · rw [Finset.mem_Ico] at hx; omega
        have hc := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj, Nat.card_Ico, Finset.card_range, hS'card] at hc
        omega
      by_contra hk
      rw [hbase] at hk
      obtain ⟨i0, hi0⟩ : ∃ i0 : Fin k, (lab i0).val < m+1 := by
        by_contra hno
        have := hblock 0 (by omega) (fun i h => hno ⟨i, by omega⟩)
        omega
      obtain ⟨il, hil⟩ : ∃ il : Fin k, m+1+z+n*(m+1)+m ≤ (lab il).val := by
        by_contra hno
        have := hblock (m+1+z+n*(m+1)+m) (by omega) (fun i h => hno ⟨i, by omega⟩)
        omega
      have hv : ∀ v, v < n → ∃ i : Fin k, m+1+z+v*(m+1) ≤ (lab i).val ∧
          (lab i).val < m+1+z+v*(m+1)+(m+1) := by
        intro v hvn
        by_contra hno
        have h1 := Nat.mul_le_mul_right (m+1) (show v+1 ≤ n from hvn)
        have h2 : (v+1)*(m+1) = v*(m+1) + (m+1) := by ring
        have := hblock (m+1+z+v*(m+1)) (by omega) (fun i h => hno ⟨i, by omega⟩)
        omega
      have hi0l : i0 ≤ il := hle _ _ (by omega)
      obtain ⟨S, hSdef⟩ : ∃ S : Finset ℕ, S = Y i0 ∩ Finset.range (2*n) := ⟨_, rfl⟩
      have hSmem : ∀ x, x ∈ S ↔ x ∈ Y i0 ∧ x < 2*n := by
        intro x
        rw [hSdef, Finset.mem_inter, Finset.mem_range]
      have hSge : n ≤ S.card := by
        have hsub : Finset.range (2*n) \ Y i0 ⊆ W (lab i0) \ Y i0 := by
          intro x hx
          rw [Finset.mem_sdiff, Finset.mem_range] at hx
          rw [Finset.mem_sdiff, hF1 (lab i0) (by omega)]
          exact ⟨Or.inl hx.1, hx.2⟩
        have hc := Finset.card_le_card hsub
        have h3 := Finset.card_sdiff_add_card_inter (Finset.range (2*n)) (Y i0)
        rw [Finset.card_range, Finset.inter_comm, ← hSdef] at h3
        have := (hnear i0).1
        omega
      have hl4 : ∀ x, x < 3*n+1 → x ∉ W (lab il) := by
        intro x hx
        rw [hF4 (lab il) (by omega) (by omega) (by omega)]
        omega
      have hSsub : S ⊆ Y il \ W (lab il) := by
        intro x hx
        rw [hSmem] at hx
        rw [Finset.mem_sdiff]
        exact ⟨hinc' i0 il hi0l hx.1, hl4 x (by omega)⟩
      have hSeq : S = Y il \ W (lab il) :=
        Finset.eq_of_subset_of_card_le hSsub (le_trans (hnear il).2 hSge)
      have hSn : S.card = n :=
        le_antisymm (le_trans (Finset.card_le_card hSsub) (hnear il).2) hSge
      have hlow : ∀ i : Fin k, i ≤ il → ∀ x, x ∈ Y i → x < 3*n+1 → x ∈ S := by
        intro i hi x hx hx3
        rw [hSeq, Finset.mem_sdiff]
        exact ⟨hinc' i il hi hx, hl4 x hx3⟩
      have hkey : ∀ i : Fin k, i ≤ il → ∀ Q : Finset ℕ, (∀ x ∈ Q, x ∈ W (lab i) ∧ x < 3*n+1) →
          n+1 ≤ Q.card → ∃ x ∈ Q, x ∈ S := by
        intro i hi Q hQ hQc
        by_contra hno
        have hsub : Q ⊆ W (lab i) \ Y i := by
          intro x hx
          rw [Finset.mem_sdiff]
          exact ⟨(hQ x hx).1, fun hxY => hno ⟨x, hx, hlow i hi x hxY (hQ x hx).2⟩⟩
        have hc := Finset.card_le_card hsub
        have := (hnear i).1
        omega
      have hpair : ∀ v, v < n → 2*v ∈ S ∨ 2*v+1 ∈ S := by
        intro v hvn
        obtain ⟨i, hi1, hi2⟩ := hv v hvn
        have h1 := Nat.mul_le_mul_right (m+1) (show v+1 ≤ n from hvn)
        have h2 : (v+1)*(m+1) = v*(m+1) + (m+1) := by ring
        have hi : i ≤ il := hle _ _ (by omega)
        have hj : ¬ ((lab i).val < m+1+z) := by omega
        have hj2 : (lab i).val - (m+1+z) < n*(m+1) := by omega
        have hdiv : ((lab i).val - (m+1+z)) / (m+1) = v :=
          Nat.div_eq_of_lt_le (by omega) (by omega)
        have hF := hF2 (lab i) hj hj2
        rw [hdiv] at hF
        have hdisj : Disjoint ({2*v, 2*v+1} : Finset ℕ) (Finset.Ico (2*n) (2*n+(n+1-2))) := by
          rw [Finset.disjoint_left]
          intro x hx hx2
          rw [Finset.mem_insert, Finset.mem_singleton] at hx
          rw [Finset.mem_Ico] at hx2
          omega
        obtain ⟨x, hxQ, hxS⟩ := hkey i hi (({2*v, 2*v+1} : Finset ℕ) ∪ (Finset.Ico (2*n) (2*n+(n+1-2))))
          (by
            intro x hx
            rw [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_Ico] at hx
            rw [hF]
            refine ⟨Or.inl (by tauto), by omega⟩)
          (by
            rw [Finset.card_union_of_disjoint hdisj, Finset.card_pair (by omega), Nat.card_Ico]
            omega)
        have := ((hSmem x).1 hxS).2
        rw [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_Ico] at hxQ
        rcases hxQ with (h | h) | h
        · exact Or.inl (h ▸ hxS)
        · exact Or.inr (h ▸ hxS)
        · omega
      have hinjS : Set.InjOn (fun x : ℕ => x / 2) S := by
        rw [← Finset.card_image_iff]
        apply le_antisymm Finset.card_image_le
        have himg : Finset.range n ⊆ S.image (fun x : ℕ => x / 2) := by
          intro v hvn
          rw [Finset.mem_range] at hvn
          rw [Finset.mem_image]
          rcases hpair v hvn with h | h
          · exact ⟨_, h, by omega⟩
          · exact ⟨_, h, by omega⟩
        have hc := Finset.card_le_card himg
        rw [Finset.card_range] at hc
        omega
      have hone : ∀ v, 2*v ∈ S → 2*v+1 ∈ S → False := by
        intro v h1 h2
        have := hinjS h1 h2 (by show 2*v/2 = (2*v+1)/2; omega)
        omega
      have hsat : ∀ (i : Fin k) (c : Fin m), (lab i).val = m+1+z+n*(m+1)+c.val →
          ∃ l ∈ F c, decide (2*l.1.val+1 ∈ S) = l.2 := by
        intro i c hic
        have hcm := c.isLt
        have hi : i ≤ il := hle _ _ (by omega)
        have hj : ¬ ((lab i).val < m+1+z) := by omega
        have hj2 : ¬ ((lab i).val - (m+1+z) < n*(m+1)) := by omega
        have hj3 : (lab i).val - (m+1+z) - n*(m+1) < m := by omega
        have hF := hF3 (lab i) hj3 hj hj2
        have hceq : (⟨(lab i).val - (m+1+z) - n*(m+1), hj3⟩ : Fin m) = c := Fin.ext (by simp; omega)
        rw [hceq] at hF
        have hdisj : Disjoint (C c) (Finset.Ico (2*n) (2*n+(n+1-(C c).card))) := by
          rw [Finset.disjoint_left]
          intro x hx hx2
          have := hClt c x hx
          rw [Finset.mem_Ico] at hx2
          omega
        obtain ⟨x, hxQ, hxS⟩ := hkey i hi (C c ∪ (Finset.Ico (2*n) (2*n+(n+1-(C c).card))))
          (by
            intro x hx
            rw [Finset.mem_union, Finset.mem_Ico] at hx
            rw [hF]
            refine ⟨Or.inl hx, ?_⟩
            rcases hx with hx | hx
            · have := hClt c x hx
              omega
            · omega)
          (by
            rw [Finset.card_union_of_disjoint hdisj, Nat.card_Ico]
            omega)
        have hx2 := ((hSmem x).1 hxS).2
        rw [Finset.mem_union, Finset.mem_Ico] at hxQ
        rcases hxQ with h | h
        · obtain ⟨⟨v, b⟩, hl, rfl⟩ := (hC c x).1 h
          refine ⟨⟨v, b⟩, hl, ?_⟩
          cases b
          · simp only [Bool.toNat_false, Nat.add_zero] at hxS
            exact decide_eq_false (fun h => hone _ hxS h)
          · simp only [Bool.toNat_true] at hxS
            exact decide_eq_true hxS
        · omega
      obtain ⟨T, hT1, hT2⟩ := hsc1 (fun v : Fin n => decide (2*v.val+1 ∈ S))
      have hsub : S' ⊆ (Finset.range (n*(m+1)+2*(m+1)+m+z) \
          Finset.Ico (m+1+z+n*(m+1)) (m+1+z+n*(m+1)+m)) ∪
          T.image (fun c : Fin m => m+1+z+n*(m+1)+c.val) := by
        intro x hx
        obtain ⟨i, rfl⟩ := (hS'mem x).1 hx
        rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico, Finset.mem_image]
        by_cases hcl : m+1+z+n*(m+1) ≤ (lab i).val ∧ (lab i).val < m+1+z+n*(m+1)+m
        · right
          refine ⟨⟨(lab i).val - (m+1+z+n*(m+1)), by omega⟩, ?_, by simp only; omega⟩
          rw [hT1]
          exact hsat i _ (by simp only; omega)
        · exact Or.inl ⟨hsz (lab i), hcl⟩
      have hc := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
      have h3 := Finset.card_sdiff_add_card_inter (Finset.range (n*(m+1)+2*(m+1)+m+z))
        (Finset.Ico (m+1+z+n*(m+1)) (m+1+z+n*(m+1)+m))
      rw [Finset.inter_eq_right.2 (by
        intro x hx
        rw [Finset.mem_Ico] at hx
        rw [Finset.mem_range]
        omega), Finset.card_range, Nat.card_Ico] at h3
      have h4 : (T.image (fun c : Fin m => m+1+z+n*(m+1)+c.val)).card ≤ T.card :=
        Finset.card_image_le
      rw [hS'card] at hc
      omega
    · intro hk
      rw [hbase] at hk
      obtain ⟨a, T, hT1, hT2⟩ := hsc2
      obtain ⟨S, hS⟩ : ∃ S : Finset ℕ,
          S = (Finset.univ : Finset (Fin n)).image (fun v => 2*v.val + (a v).toNat) := ⟨_, rfl⟩
      have hSmem : ∀ x, x ∈ S ↔ ∃ v : Fin n, 2*v.val + (a v).toNat = x := by
        intro x
        rw [hS]
        simp
      have hSlt : ∀ x ∈ S, x < 2*n := by
        intro x hx
        obtain ⟨v, rfl⟩ := (hSmem x).1 hx
        have := v.isLt
        have := Bool.toNat_le (a v)
        omega
      have hScard : S.card = n := by
        rw [hS, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
        intro v w h
        simp only at h
        have := Bool.toNat_le (a v)
        have := Bool.toNat_le (a w)
        exact Fin.ext (by omega)
      have hScomp : (Finset.range (2*n) \ S).card = n := by
        have h3 := Finset.card_sdiff_add_card_inter (Finset.range (2*n)) S
        rw [Finset.inter_eq_right.2 (fun x hx => Finset.mem_range.2 (hSlt x hx)),
          Finset.card_range, hScard] at h3
        omega
      obtain ⟨L, hL⟩ : ∃ L : Finset ℕ, L = (Finset.range (n*(m+1)+2*(m+1)+m+z) \
          Finset.Ico (m+1+z+n*(m+1)) (m+1+z+n*(m+1)+m)) ∪
          T.image (fun c : Fin m => m+1+z+n*(m+1)+c.val) := ⟨_, rfl⟩
      have hTinj : Function.Injective (fun c : Fin m => m+1+z+n*(m+1) + c.val) := by
        intro c d h
        simp only at h
        exact Fin.ext (by omega)
      have hLcard : k ≤ L.card := by
        have hdisj : Disjoint (Finset.range (n*(m+1)+2*(m+1)+m+z) \
            Finset.Ico (m+1+z+n*(m+1)) (m+1+z+n*(m+1)+m))
            (T.image (fun c : Fin m => m+1+z+n*(m+1) + c.val)) := by
          rw [Finset.disjoint_left]
          intro x hx hx2
          rw [Finset.mem_sdiff, Finset.mem_Ico] at hx
          obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx2
          have := c.isLt
          omega
        have h3 := Finset.card_sdiff_add_card_inter (Finset.range (n*(m+1)+2*(m+1)+m+z))
          (Finset.Ico (m+1+z+n*(m+1)) (m+1+z+n*(m+1)+m))
        rw [Finset.inter_eq_right.2 (by
          intro x hx
          rw [Finset.mem_Ico] at hx
          rw [Finset.mem_range]
          omega), Finset.card_range, Nat.card_Ico] at h3
        rw [hL, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hTinj, hT2]
        omega
      have hLlt : ∀ x ∈ L, x < size n m z := by
        intro x hx
        rw [hN]
        rw [hL, Finset.mem_union, Finset.mem_sdiff, Finset.mem_range, Finset.mem_image] at hx
        rcases hx with h | ⟨c, -, rfl⟩
        · exact h.1
        · have := c.isLt
          omega
      obtain ⟨L', hL'sub, hL'card⟩ := Finset.exists_subset_card_eq hLcard
      obtain ⟨e, he⟩ : ∃ e : Fin k ↪o ℕ, ∀ i, e i ∈ L :=
        ⟨L'.orderEmbOfFin hL'card, fun i => hL'sub (Finset.orderEmbOfFin_mem L' hL'card i)⟩
      have hgood : ∀ j : Fin (size n m z), j.val ∈ L →
          (W j \ (S ∪ Finset.Ico (3*n+1) (3*n+1+(2*n+1)*j.val))).card ≤ n ∧
          ((S ∪ Finset.Ico (3*n+1) (3*n+1+(2*n+1)*j.val)) \ W j).card ≤ n := by
        intro j hjL
        obtain ⟨Yj, hYj⟩ : ∃ Yj : Finset ℕ, Yj = S ∪ Finset.Ico (3*n+1) (3*n+1+(2*n+1)*j.val) :=
          ⟨_, rfl⟩
        rw [← hYj]
        have hlowx : ∀ x, x ∈ W j \ Yj → x ∈ W j ∧ x < 3*n+1 ∧ x ∉ S := by
          intro x hx
          rw [hYj, Finset.mem_sdiff, Finset.mem_union, Finset.mem_Ico] at hx
          refine ⟨hx.1, ?_, fun h => hx.2 (Or.inl h)⟩
          by_contra h3
          have := (hT j x (by omega)).1 hx.1
          exact hx.2 (Or.inr ⟨by omega, this⟩)
        constructor
        · by_cases hj : j.val < m+1+z
          · have hsub : W j \ Yj ⊆ Finset.range (2*n) \ S := by
              intro x hx
              obtain ⟨h1, h2, h3⟩ := hlowx x hx
              rw [hF1 j hj] at h1
              rw [Finset.mem_sdiff, Finset.mem_range]
              exact ⟨by omega, h3⟩
            have := Finset.card_le_card hsub
            omega
          · by_cases hj2 : j.val-(m+1+z) < n*(m+1)
            · have hvn : (j.val-(m+1+z))/(m+1) < n :=
                Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hj2)
              obtain ⟨v, hv⟩ : ∃ v, v = (j.val-(m+1+z))/(m+1) := ⟨_, rfl⟩
              rw [← hv] at hvn
              have hvS : 2*v + (a ⟨v, hvn⟩).toNat ∈ S := (hSmem _).2 ⟨⟨v, hvn⟩, rfl⟩
              have hb := Bool.toNat_le (a ⟨v, hvn⟩)
              have hsub : W j \ Yj ⊆ {2*v + 1 - (a ⟨v, hvn⟩).toNat} ∪
                  Finset.Ico (2*n) (2*n+(n+1-2)) := by
                intro x hx
                obtain ⟨h1, h2, h3⟩ := hlowx x hx
                rw [hF2 j hj hj2, ← hv] at h1
                rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]
                have hne : x ≠ 2*v + (a ⟨v, hvn⟩).toNat := fun h => h3 (h ▸ hvS)
                omega
              have hc := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
              rw [Finset.card_singleton, Nat.card_Ico] at hc
              omega
            · by_cases hj3 : j.val-(m+1+z)-n*(m+1) < m
              · have hcT : (⟨_, hj3⟩ : Fin m) ∈ T := by
                  rw [hL, Finset.mem_union, Finset.mem_sdiff, Finset.mem_Ico, Finset.mem_image] at hjL
                  rcases hjL with h | ⟨c, hc, hcj⟩
                  · omega
                  · have : c = ⟨_, hj3⟩ := Fin.ext (by simp only; omega)
                    rw [← this]
                    exact hc
                obtain ⟨c, hc⟩ : ∃ c : Fin m, c = ⟨_, hj3⟩ := ⟨_, rfl⟩
                rw [← hc] at hcT
                obtain ⟨l, hl, hal⟩ := (hT1 c).1 hcT
                have hx0C : 2*l.1.val + l.2.toNat ∈ C c := (hC c _).2 ⟨l, hl, rfl⟩
                have hx0S : 2*l.1.val + l.2.toNat ∈ S := (hSmem _).2 ⟨l.1, by rw [hal]⟩
                have hsub : W j \ Yj ⊆ (C c \ S) ∪ Finset.Ico (2*n) (2*n+(n+1-(C c).card)) := by
                  intro x hx
                  obtain ⟨h1, h2, h3⟩ := hlowx x hx
                  rw [hF3 j hj3 hj hj2, ← hc] at h1
                  rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_Ico]
                  rcases h1 with (h | h) | h
                  · exact Or.inl ⟨h, h3⟩
                  · exact Or.inr h
                  · omega
                have hcc := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
                rw [Nat.card_Ico] at hcc
                have h3 := Finset.card_sdiff_add_card_inter (C c) S
                have h4 : 0 < (C c ∩ S).card :=
                  Finset.card_pos.2 ⟨_, Finset.mem_inter.2 ⟨hx0C, hx0S⟩⟩
                have h5 : (C c \ S).card ≤ (Finset.range (2*n) \ S).card :=
                  Finset.card_le_card (Finset.sdiff_subset_sdiff
                    (fun x hx => Finset.mem_range.2 (hClt c x hx)) (le_refl _))
                omega
              · have hsub : W j \ Yj ⊆ ∅ := by
                  intro x hx
                  obtain ⟨h1, h2, h3⟩ := hlowx x hx
                  rw [hF4 j hj hj2 hj3] at h1
                  omega
                have := Finset.card_le_card hsub
                rw [Finset.card_empty] at this
                omega
        · have hsub : Yj \ W j ⊆ S := by
            intro x hx
            rw [hYj, Finset.mem_sdiff, Finset.mem_union, Finset.mem_Ico] at hx
            rcases hx with ⟨h | h, h2⟩
            · exact h
            · exact absurd ((hT j x h.1).2 h.2) h2
          have := Finset.card_le_card hsub
          omega
      refine ⟨fun i => ⟨e i, hLlt _ (he i)⟩,
        fun i => S ∪ Finset.Ico (3*n+1) (3*n+1+(2*n+1)*(e i)), ?_, ?_, ?_⟩
      · intro i j hij x hx
        have h1 := Nat.mul_le_mul_left (2*n+1) (e.monotone hij)
        simp only [Finset.mem_union, Finset.mem_Ico] at hx ⊢
        rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (by omega)
      · intro i j hij h
        have h1 : e i < e j := e.strictMono (Fin.lt_def.2 (by omega))
        have h2 := congrArg Fin.val h
        simp only at h2
        omega
      · intro i
        refine ⟨?_, hgood ⟨e i, hLlt _ (he i)⟩ (he i)⟩
        intro x hx
        have h1 := Nat.mul_le_mul_left (2*n+1) (le_of_lt (lt_of_lt_of_eq (hLlt _ (he i)) hN))
        rw [Finset.mem_range, hdim]
        rw [Finset.mem_union, Finset.mem_Ico] at hx
        rcases hx with hx | hx
        · have := hSlt x hx
          omega
        · omega
