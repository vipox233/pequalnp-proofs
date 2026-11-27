import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_394_aux

private theorem finRange_succ_append (m : ℕ) :
    List.finRange (m + 1) = (List.finRange m).map Fin.castSucc ++ [Fin.last m] := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  by_cases hi : i < m
  · rw [List.getElem_append_left (by simp [hi])]
    simp
  · have him : i = m := by
      simp only [List.length_finRange] at h1
      omega
    subst him
    rw [List.getElem_append_right (by simp)]
    simp [Fin.last]

private theorem finRange_reverse_eq_map_rev (w : ℕ) :
    (List.finRange w).reverse = (List.finRange w).map Fin.rev := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.length_reverse, List.length_finRange] at h1
  rw [List.getElem_reverse, List.getElem_map]
  ext
  simp [Fin.rev]
  omega

private theorem finRange_four_mul (w : ℕ) :
    List.finRange (4 * w) =
      (List.finRange w).map (fun k => (⟨k.val, by omega⟩ : Fin (4 * w))) ++
      (List.finRange w).map (fun k => (⟨w + k.val, by omega⟩ : Fin (4 * w))) ++
      (List.finRange w).map (fun k => (⟨2 * w + k.val, by omega⟩ : Fin (4 * w))) ++
      (List.finRange w).map (fun k => (⟨3 * w + k.val, by omega⟩ : Fin (4 * w))) := by
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  simp only [List.length_finRange] at h1
  by_cases h0 : i < w
  · rw [List.getElem_append_left (by simp; omega),
      List.getElem_append_left (by simp; omega),
      List.getElem_append_left (by simp; omega)]
    simp
  · by_cases h1w : i < 2 * w
    · rw [List.getElem_append_left (by simp; omega),
        List.getElem_append_left (by simp; omega),
        List.getElem_append_right (by simp; omega)]
      ext
      simp only [List.getElem_finRange, List.getElem_map, List.length_map, List.length_finRange,
        Fin.val_cast]
      omega
    · by_cases h2w : i < 3 * w
      · rw [List.getElem_append_left (by simp; omega),
          List.getElem_append_right (by simp; omega)]
        ext
        simp only [List.getElem_finRange, List.getElem_map, List.length_append,
          List.length_map, List.length_finRange, Fin.val_cast]
        omega
      · rw [List.getElem_append_right (by simp; omega)]
        ext
        simp only [List.getElem_finRange, List.getElem_map, List.length_append,
          List.length_map, List.length_finRange, Fin.val_cast]
        omega

private theorem two_involutions_bicolor_aux {V : Type} [Fintype V] [DecidableEq V]
    (I1 I2 : Equiv.Perm V)
    (hI1_inv : ∀ x, I1 (I1 x) = x) (hI2_inv : ∀ x, I2 (I2 x) = x)
    (hI1_nfp : ∀ x, I1 x ≠ x) (hI2_nfp : ∀ x, I2 x ≠ x) :
    ∀ n : ℕ, ∀ S : Finset V, S.card ≤ n →
      (∀ x ∈ S, I1 x ∈ S) → (∀ x ∈ S, I2 x ∈ S) →
      ∃ χ : V → Bool, ∀ x ∈ S, χ (I1 x) = !(χ x) ∧ χ (I2 x) = !(χ x) := by
  intro n
  induction n with
  | zero =>
    intro S hS _ _
    refine ⟨fun _ => false, fun x hx => ?_⟩
    have hempty : S = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hS)
    rw [hempty] at hx
    exact False.elim (Finset.notMem_empty x hx)
  | succ n ih =>
    intro S hS hS1 hS2
    by_cases hSne : S.Nonempty
    · obtain ⟨x0, hx0⟩ := hSne
      let τ : Equiv.Perm V := I2 * I1
      have hτ_apply : ∀ x, τ x = I2 (I1 x) := fun _ => rfl
      have hτ_symm_apply : ∀ x, τ.symm x = I1 (I2 x) := by
        intro x
        apply τ.injective
        rw [Equiv.apply_symm_apply, hτ_apply, hI1_inv, hI2_inv]
      have hconj : ∀ (k : ℕ) (x : V), I1 ((τ ^ k) x) = (τ.symm ^ k) (I1 x) := by
        intro k
        induction k with
        | zero => intro x; rfl
        | succ k ihk =>
          intro x
          rw [pow_succ', Equiv.Perm.mul_apply, hτ_apply, pow_succ', Equiv.Perm.mul_apply,
            hτ_symm_apply, ← ihk x]
      have hex_per : ∃ m : ℕ, 0 < m ∧ (τ ^ m) x0 = x0 := by
        have hlt : Fintype.card V < Fintype.card (Fin (Fintype.card V + 1)) := by
          simp
        obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
          (fun k : Fin (Fintype.card V + 1) => (τ ^ k.val) x0) hlt
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hltij | hltji
        · refine ⟨j.val - i.val, by omega, ?_⟩
          apply (τ ^ i.val).injective
          rw [← Equiv.Perm.mul_apply, ← pow_add, show i.val + (j.val - i.val) = j.val by omega]
          exact heq.symm
        · refine ⟨i.val - j.val, by omega, ?_⟩
          apply (τ ^ j.val).injective
          rw [← Equiv.Perm.mul_apply, ← pow_add, show j.val + (i.val - j.val) = i.val by omega]
          exact heq
      obtain ⟨m, hm_pos, hm_per⟩ := hex_per
      have hper_mod : ∀ k : ℕ, (τ ^ (k % m)) x0 = (τ ^ k) x0 := by
        intro k
        have hdiv : ∀ q : ℕ, (τ ^ (m * q)) x0 = x0 := by
          intro q
          induction q with
          | zero => rfl
          | succ q ihq =>
            rw [Nat.mul_succ, pow_add, Equiv.Perm.mul_apply, hm_per, ihq]
        have hkm : m * (k / m) + k % m = k := Nat.div_add_mod k m
        calc (τ ^ (k % m)) x0 = (τ ^ (k % m)) ((τ ^ (m * (k / m))) x0) := by rw [hdiv]
          _ = (τ ^ (k % m + m * (k / m))) x0 := by rw [← Equiv.Perm.mul_apply, ← pow_add]
          _ = (τ ^ k) x0 := by rw [Nat.add_comm, hkm]
      let A : Finset V := (Finset.range m).image (fun k => (τ ^ k) x0)
      let B : Finset V := A.image I1
      have hpow_mem_A : ∀ k : ℕ, (τ ^ k) x0 ∈ A := by
        intro k
        rw [← hper_mod k]
        exact Finset.mem_image.2 ⟨k % m, Finset.mem_range.2 (Nat.mod_lt k hm_pos), rfl⟩
      have hx0A : x0 ∈ A := hpow_mem_A 0
      have hA_τ : ∀ x ∈ A, τ x ∈ A := by
        intro x hx
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hx
        have h1 : τ ((τ ^ k) x0) = (τ ^ (k + 1)) x0 := by
          rw [pow_succ']
          exact (Equiv.Perm.mul_apply τ (τ ^ k) x0).symm
        rw [h1]
        exact hpow_mem_A (k + 1)
      have hA_τs : ∀ x ∈ A, τ.symm x ∈ A := by
        intro x hx
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hx
        have h1 : τ.symm ((τ ^ k) x0) = (τ ^ (k + m - 1)) x0 := by
          apply τ.injective
          rw [Equiv.apply_symm_apply, ← Equiv.Perm.mul_apply, ← pow_succ',
            show k + m - 1 + 1 = k + m by omega, pow_add, Equiv.Perm.mul_apply, hm_per]
        rw [h1]
        exact hpow_mem_A (k + m - 1)
      have hdisj : Disjoint A B := by
        rw [Finset.disjoint_left]
        intro y hyA hyB
        obtain ⟨a, _, ha⟩ := Finset.mem_image.1 hyA
        obtain ⟨z, hzA, hz⟩ := Finset.mem_image.1 hyB
        obtain ⟨b, _, hb⟩ := Finset.mem_image.1 hzA
        have heq1 : I1 ((τ ^ b) x0) = (τ ^ a) x0 := by
          rw [hb, hz, ha]
        rw [hconj b x0] at heq1
        have heq2 : (τ ^ (b + a)) x0 = I1 x0 := by
          have h := congrArg (τ ^ b) heq1
          have hcancel : ∀ (t : ℕ) (v : V), (τ ^ t) ((τ.symm ^ t) v) = v := by
            intro t
            induction t with
            | zero => intro v; rfl
            | succ t iht =>
              intro v
              have h1 : (τ ^ (t + 1)) ((τ.symm ^ (t + 1)) v) =
                  (τ ^ t) (τ (τ.symm ((τ.symm ^ t) v))) := by
                rw [pow_succ, pow_succ']
                rfl
              rw [h1, Equiv.apply_symm_apply, iht v]
          have hadd : (τ ^ b) ((τ ^ a) x0) = (τ ^ (b + a)) x0 := by
            rw [pow_add]
            exact (Equiv.Perm.mul_apply (τ ^ b) (τ ^ a) x0).symm
          rw [hcancel b (I1 x0), hadd] at h
          exact h.symm
        have hcancelL : ∀ (t : ℕ) (v : V), (τ.symm ^ t) ((τ ^ t) v) = v := by
          intro t
          induction t with
          | zero => intro v; rfl
          | succ t iht =>
            intro v
            rw [pow_succ, pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
              Equiv.symm_apply_apply, iht v]
        rcases Nat.even_or_odd (b + a) with ⟨t, ht⟩ | ⟨t, ht⟩
        · have hfp : I1 ((τ ^ t) x0) = (τ ^ t) x0 := by
            rw [hconj t x0, ← heq2, ht, pow_add, Equiv.Perm.mul_apply, hcancelL t]
          exact hI1_nfp ((τ ^ t) x0) hfp
        · let w0 := I1 ((τ ^ t) x0)
          have hw1 : I2 w0 = (τ ^ (t + 1)) x0 := by
            change τ ((τ ^ t) x0) = (τ ^ (t + 1)) x0
            rw [pow_succ']
            exact (Equiv.Perm.mul_apply τ (τ ^ t) x0).symm
          have hw2 : w0 = (τ ^ (t + 1)) x0 := by
            change I1 ((τ ^ t) x0) = (τ ^ (t + 1)) x0
            rw [hconj t x0, ← heq2, show b + a = t + (t + 1) by omega,
              pow_add, Equiv.Perm.mul_apply, hcancelL t]
          exact hI2_nfp w0 (hw1.trans hw2.symm)
      have hI1_AB : ∀ x ∈ A, I1 x ∈ B := fun x hx => Finset.mem_image.2 ⟨x, hx, rfl⟩
      have hI1_BA : ∀ x ∈ B, I1 x ∈ A := by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
        rwa [hI1_inv]
      have hI2_AB : ∀ x ∈ A, I2 x ∈ B := by
        intro x hx
        have h1 : I2 x = I1 (τ.symm x) := by
          rw [hτ_symm_apply, hI1_inv]
        rw [h1]
        exact hI1_AB (τ.symm x) (hA_τs x hx)
      have hI2_BA : ∀ x ∈ B, I2 x ∈ A := by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
        exact hA_τ a ha
      let S' : Finset V := S \ (A ∪ B)
      have hS'_card : S'.card ≤ n := by
        have hlt : S'.card < S.card := by
          refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨Finset.sdiff_subset, ?_⟩)
          intro heq
          have hx0S' : x0 ∈ S' := by rw [heq]; exact hx0
          exact (Finset.mem_sdiff.1 hx0S').2 (Finset.mem_union_left B hx0A)
        omega
      have hS'1 : ∀ x ∈ S', I1 x ∈ S' := by
        intro x hx
        obtain ⟨hxS, hxnot⟩ := Finset.mem_sdiff.1 hx
        refine Finset.mem_sdiff.2 ⟨hS1 x hxS, fun hmem => hxnot ?_⟩
        rcases Finset.mem_union.1 hmem with hA | hB
        · exact Finset.mem_union_right A (by rw [← hI1_inv x]; exact hI1_AB _ hA)
        · exact Finset.mem_union_left B (by rw [← hI1_inv x]; exact hI1_BA _ hB)
      have hS'2 : ∀ x ∈ S', I2 x ∈ S' := by
        intro x hx
        obtain ⟨hxS, hxnot⟩ := Finset.mem_sdiff.1 hx
        refine Finset.mem_sdiff.2 ⟨hS2 x hxS, fun hmem => hxnot ?_⟩
        rcases Finset.mem_union.1 hmem with hA | hB
        · exact Finset.mem_union_right A (by rw [← hI2_inv x]; exact hI2_AB _ hA)
        · exact Finset.mem_union_left B (by rw [← hI2_inv x]; exact hI2_BA _ hB)
      obtain ⟨χ', hχ'⟩ := ih S' hS'_card hS'1 hS'2
      let χ : V → Bool := fun x => if x ∈ A then false else if x ∈ B then true else χ' x
      refine ⟨χ, fun x hx => ?_⟩
      by_cases hxA : x ∈ A
      · have h1B : I1 x ∈ B := hI1_AB x hxA
        have h1notA : I1 x ∉ A := fun h => Finset.disjoint_left.1 hdisj h h1B
        have h2B : I2 x ∈ B := hI2_AB x hxA
        have h2notA : I2 x ∉ A := fun h => Finset.disjoint_left.1 hdisj h h2B
        simp [χ, hxA, h1B, h1notA, h2B, h2notA]
      · by_cases hxB : x ∈ B
        · have h1A : I1 x ∈ A := hI1_BA x hxB
          have h2A : I2 x ∈ A := hI2_BA x hxB
          simp [χ, hxA, hxB, h1A, h2A]
        · have hxS' : x ∈ S' := Finset.mem_sdiff.2 ⟨hx, fun h => by
            rcases Finset.mem_union.1 h with hA | hB
            · exact hxA hA
            · exact hxB hB⟩
          have h1S' : I1 x ∈ S' := hS'1 x hxS'
          have h2S' : I2 x ∈ S' := hS'2 x hxS'
          have h1notA : I1 x ∉ A := fun h => (Finset.mem_sdiff.1 h1S').2 (Finset.mem_union_left B h)
          have h1notB : I1 x ∉ B := fun h => (Finset.mem_sdiff.1 h1S').2 (Finset.mem_union_right A h)
          have h2notA : I2 x ∉ A := fun h => (Finset.mem_sdiff.1 h2S').2 (Finset.mem_union_left B h)
          have h2notB : I2 x ∉ B := fun h => (Finset.mem_sdiff.1 h2S').2 (Finset.mem_union_right A h)
          simp only [χ, hxA, hxB, h1notA, h1notB, h2notA, h2notB, ↓reduceIte]
          exact hχ' x hxS'
    · refine ⟨fun _ => false, fun x hx => False.elim (hSne ⟨x, hx⟩)⟩

private theorem two_involutions_bicolor {V : Type} [Fintype V] [DecidableEq V]
    (I1 I2 : Equiv.Perm V)
    (hI1_inv : ∀ x, I1 (I1 x) = x) (hI2_inv : ∀ x, I2 (I2 x) = x)
    (hI1_nfp : ∀ x, I1 x ≠ x) (hI2_nfp : ∀ x, I2 x ≠ x) :
    ∃ χ : V → Bool, ∀ x : V, χ (I1 x) = !(χ x) ∧ χ (I2 x) = !(χ x) := by
  obtain ⟨χ, hχ⟩ := two_involutions_bicolor_aux I1 I2 hI1_inv hI2_inv hI1_nfp hI2_nfp
    (Fintype.card V) Finset.univ (by simp) (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
  exact ⟨χ, fun x => hχ x (Finset.mem_univ x)⟩

private def IndepOf {w : ℕ} (k : Fin w) (g : (Fin w → Bool) → Bool) : Prop :=
  ∀ s t : Fin w → Bool, (∀ i : Fin w, i ≠ k → s i = t i) → g s = g t

private def flipBit {w : ℕ} (k : Fin w) (g : (Fin w → Bool) → Bool) (s : Fin w → Bool) : Fin w → Bool :=
  Function.update s k (xor (s k) (g s))

private theorem flipBit_apply_eq {w : ℕ} (k : Fin w) (g : (Fin w → Bool) → Bool) (s : Fin w → Bool) :
    flipBit k g s k = xor (s k) (g s) := by
  simp [flipBit]

private theorem flipBit_apply_ne {w : ℕ} (k : Fin w) (g : (Fin w → Bool) → Bool)
    (s : Fin w → Bool) {i : Fin w} (hi : i ≠ k) :
    flipBit k g s i = s i := by
  simp [flipBit, hi]

private theorem flipBit_involutive {w : ℕ} (k : Fin w) (g : (Fin w → Bool) → Bool)
    (hg : IndepOf k g) (s : Fin w → Bool) :
    flipBit k g (flipBit k g s) = s := by
  have hgs : g (flipBit k g s) = g s := hg _ _ fun i hi => flipBit_apply_ne k g s hi
  ext i
  by_cases hi : i = k
  · subst hi
    rw [flipBit_apply_eq, flipBit_apply_eq, hgs]
    cases s i <;> cases g s <;> rfl
  · rw [flipBit_apply_ne k g _ hi, flipBit_apply_ne k g _ hi]

private def flipBitPerm {w : ℕ} (k : Fin w) (g : (Fin w → Bool) → Bool) (hg : IndepOf k g) :
    Equiv.Perm (Fin w → Bool) :=
  { toFun := flipBit k g
    invFun := flipBit k g
    left_inv := flipBit_involutive k g hg
    right_inv := flipBit_involutive k g hg }

private theorem peel_bit_zero {w : ℕ} (σ : Equiv.Perm (Fin (w + 1) → Bool)) :
    ∃ (a c : (Fin (w + 1) → Bool) → Bool),
      IndepOf 0 a ∧ IndepOf 0 c ∧
      ∀ s : Fin (w + 1) → Bool,
        flipBit 0 c (σ (flipBit 0 a s)) 0 = s 0 := by
  let I1 : Equiv.Perm (Fin (w + 1) → Bool) :=
    { toFun := fun s => Function.update s 0 (!(s 0))
      invFun := fun s => Function.update s 0 (!(s 0))
      left_inv := fun s => by
        ext i
        by_cases hi : i = 0
        · subst hi; simp
        · simp [hi]
      right_inv := fun s => by
        ext i
        by_cases hi : i = 0
        · subst hi; simp
        · simp [hi] }
  let I2 : Equiv.Perm (Fin (w + 1) → Bool) := σ.symm * I1 * σ
  have hI1_inv : ∀ s, I1 (I1 s) = s := I1.left_inv
  have hI2_inv : ∀ s, I2 (I2 s) = s := by
    intro s
    change σ.symm (I1 (σ (σ.symm (I1 (σ s))))) = s
    rw [Equiv.apply_symm_apply, hI1_inv, Equiv.symm_apply_apply]
  have hI1_nfp : ∀ s, I1 s ≠ s := by
    intro s h
    have h0 := congrFun h 0
    simp only [I1, Equiv.coe_fn_mk, Function.update_self] at h0
    cases hval : s 0 <;> simp [hval] at h0
  have hI2_nfp : ∀ s, I2 s ≠ s := by
    intro s h
    have h1 : I1 (σ s) = σ s := by
      have h2 := congrArg σ h
      change σ (σ.symm (I1 (σ s))) = σ s at h2
      rwa [Equiv.apply_symm_apply] at h2
    exact hI1_nfp (σ s) h1
  obtain ⟨χ, hχ⟩ := two_involutions_bicolor I1 I2 hI1_inv hI2_inv hI1_nfp hI2_nfp
  let a : (Fin (w + 1) → Bool) → Bool := fun s => χ (Function.update s 0 false)
  let c : (Fin (w + 1) → Bool) → Bool := fun t => χ (σ.symm (Function.update t 0 false))
  have ha_ind : IndepOf 0 a := by
    intro s t hst
    dsimp only [a]
    congr 1
    ext i
    by_cases hi : i = 0
    · subst hi; simp
    · simp [hi, hst i hi]
  have hc_ind : IndepOf 0 c := by
    intro s t hst
    dsimp only [c]
    congr 2
    ext i
    by_cases hi : i = 0
    · subst hi; simp
    · simp [hi, hst i hi]
  have hχ_a : ∀ s, xor (s 0) (a s) = χ s := by
    intro s
    cases hs0 : s 0
    · have hu : Function.update s 0 false = s := by
        ext i; by_cases hi : i = 0 <;> simp [hi, hs0]
      simp [a, hu]
    · have hu : I1 (Function.update s 0 false) = s := by
        ext i
        by_cases hi : i = 0
        · subst hi; simp [I1, hs0]
        · simp [I1, hi]
      have hflip := (hχ (Function.update s 0 false)).1
      rw [hu] at hflip
      simp [a, hflip]
  have hχ_c : ∀ t, xor (t 0) (c t) = χ (σ.symm t) := by
    intro t
    cases ht0 : t 0
    · have hu : Function.update t 0 false = t := by
        ext i; by_cases hi : i = 0 <;> simp [hi, ht0]
      simp [c, hu]
    · have hu : I2 (σ.symm (Function.update t 0 false)) = σ.symm t := by
        change σ.symm (I1 (σ (σ.symm (Function.update t 0 false)))) = σ.symm t
        rw [Equiv.apply_symm_apply]
        congr 1
        ext i
        by_cases hi : i = 0
        · subst hi; simp [I1, ht0]
        · simp [I1, hi]
      have hflip := (hχ (σ.symm (Function.update t 0 false))).2
      rw [hu] at hflip
      simp [c, hflip]
  refine ⟨a, c, ha_ind, hc_ind, fun s => ?_⟩
  rw [flipBit_apply_eq, hχ_c (σ (flipBit 0 a s)), Equiv.symm_apply_apply]
  rw [← hχ_a (flipBit 0 a s)]
  have ha_eq : a (flipBit 0 a s) = a s := ha_ind _ _ fun i hi => flipBit_apply_ne 0 a s hi
  rw [flipBit_apply_eq, ha_eq]
  cases s 0 <;> cases a s <;> rfl

private def fwdSweep {w : ℕ} (g : Fin w → (Fin w → Bool) → Bool) (x : Fin w → Bool) :
    Fin w → Bool :=
  (List.finRange w).foldl (fun s k => flipBit k (g k) s) x

private def bwdSweep {w : ℕ} (h : Fin w → (Fin w → Bool) → Bool) (x : Fin w → Bool) :
    Fin w → Bool :=
  (List.finRange w).reverse.foldl (fun s k => flipBit k (h k) s) x

private theorem lift_tail_foldl {w : ℕ} (L : List (Fin w))
    (g : Fin (w + 1) → (Fin (w + 1) → Bool) → Bool)
    (gT : Bool → Fin w → (Fin w → Bool) → Bool)
    (hg : ∀ (j : Fin w) (s : Fin (w + 1) → Bool),
      g j.succ s = gT (s 0) j (fun i => s i.succ)) :
    ∀ s : Fin (w + 1) → Bool,
      ((L.map Fin.succ).foldl (fun st k => flipBit k (g k) st) s 0 = s 0) ∧
      (fun i : Fin w => (L.map Fin.succ).foldl (fun st k => flipBit k (g k) st) s i.succ) =
        L.foldl (fun st j => flipBit j (gT (s 0) j) st) (fun i => s i.succ) := by
  induction L with
  | nil => intro s; exact ⟨rfl, rfl⟩
  | cons j rest ih =>
    intro s
    simp only [List.map_cons, List.foldl_cons]
    have h0 : flipBit j.succ (g j.succ) s 0 = s 0 :=
      flipBit_apply_ne j.succ (g j.succ) s (Fin.succ_ne_zero j).symm
    have htail : (fun i : Fin w => flipBit j.succ (g j.succ) s i.succ) =
        flipBit j (gT (s 0) j) (fun i => s i.succ) := by
      ext i
      by_cases hij : i = j
      · subst hij
        rw [flipBit_apply_eq, flipBit_apply_eq, hg i s]
      · have hne : i.succ ≠ j.succ := fun h => hij (Fin.succ_injective _ h)
        rw [flipBit_apply_ne j.succ _ s hne, flipBit_apply_ne j _ _ hij]
    obtain ⟨ih0, iht⟩ := ih (flipBit j.succ (g j.succ) s)
    rw [h0] at ih0 iht
    rw [htail] at iht
    exact ⟨ih0, iht⟩

private theorem benes_decomp : ∀ (w : ℕ) (σ : Equiv.Perm (Fin w → Bool)),
    ∃ (g h : Fin w → (Fin w → Bool) → Bool),
      (∀ k, IndepOf k (g k)) ∧ (∀ k, IndepOf k (h k)) ∧
      ∀ x : Fin w → Bool, bwdSweep h (fwdSweep g x) = σ x := by
  intro w
  induction w with
  | zero =>
    intro σ
    refine ⟨fun k => Fin.elim0 k, fun k => Fin.elim0 k,
      fun k => Fin.elim0 k, fun k => Fin.elim0 k, fun x => ?_⟩
    ext i
    exact Fin.elim0 i
  | succ w ih =>
    intro σ
    obtain ⟨a, c, ha_ind, hc_ind, hpres⟩ := peel_bit_zero σ
    let A : Equiv.Perm (Fin (w + 1) → Bool) := flipBitPerm 0 a ha_ind
    let C : Equiv.Perm (Fin (w + 1) → Bool) := flipBitPerm 0 c hc_ind
    let ρ : Equiv.Perm (Fin (w + 1) → Bool) := A.trans (σ.trans C)
    have hρ_pres : ∀ s, ρ s 0 = s 0 := hpres
    have hρ_symm_pres : ∀ s, ρ.symm s 0 = s 0 := by
      intro s
      have h := hρ_pres (ρ.symm s)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    let ρb : Bool → Equiv.Perm (Fin w → Bool) := fun b =>
      { toFun := fun t => fun i => ρ (Fin.cons b t) i.succ
        invFun := fun t => fun i => ρ.symm (Fin.cons b t) i.succ
        left_inv := fun t => by
          ext i
          dsimp only
          have hcons : Fin.cons b (fun j : Fin w => ρ (Fin.cons b t) j.succ) = ρ (Fin.cons b t) := by
            ext k
            refine Fin.cases ?_ ?_ k
            · simp [hρ_pres]
            · intro j; simp
          rw [hcons, Equiv.symm_apply_apply]
          simp
        right_inv := fun t => by
          ext i
          dsimp only
          have hcons : Fin.cons b (fun j : Fin w => ρ.symm (Fin.cons b t) j.succ) = ρ.symm (Fin.cons b t) := by
            ext k
            refine Fin.cases ?_ ?_ k
            · simp [hρ_symm_pres]
            · intro j; simp
          rw [hcons, Equiv.apply_symm_apply]
          simp }
    obtain ⟨gf, hf, hgf_ind, hhf_ind, hbf⟩ := ih (ρb false)
    obtain ⟨gt, ht, hgt_ind, hht_ind, hbt⟩ := ih (ρb true)
    let gT : Bool → Fin w → (Fin w → Bool) → Bool := fun b => if b then gt else gf
    let hT : Bool → Fin w → (Fin w → Bool) → Bool := fun b => if b then ht else hf
    let g : Fin (w + 1) → (Fin (w + 1) → Bool) → Bool :=
      Fin.cases a (fun j s => gT (s 0) j (fun i => s i.succ))
    let h : Fin (w + 1) → (Fin (w + 1) → Bool) → Bool :=
      Fin.cases c (fun j s => hT (s 0) j (fun i => s i.succ))
    have hg_ind : ∀ k, IndepOf k (g k) := by
      intro k
      refine Fin.cases ?_ ?_ k
      · exact ha_ind
      · intro j s t hst
        simp only [g, Fin.cases_succ]
        have h0 : s 0 = t 0 := hst 0 (Fin.succ_ne_zero j).symm
        rw [h0]
        cases htv : t 0
        · exact hgf_ind j _ _ fun i hi => hst i.succ (fun he => hi (Fin.succ_injective _ he))
        · exact hgt_ind j _ _ fun i hi => hst i.succ (fun he => hi (Fin.succ_injective _ he))
    have hh_ind : ∀ k, IndepOf k (h k) := by
      intro k
      refine Fin.cases ?_ ?_ k
      · exact hc_ind
      · intro j s t hst
        simp only [h, Fin.cases_succ]
        have h0 : s 0 = t 0 := hst 0 (Fin.succ_ne_zero j).symm
        rw [h0]
        cases htv : t 0
        · exact hhf_ind j _ _ fun i hi => hst i.succ (fun he => hi (Fin.succ_injective _ he))
        · exact hht_ind j _ _ fun i hi => hst i.succ (fun he => hi (Fin.succ_injective _ he))
    refine ⟨g, h, hg_ind, hh_ind, fun x => ?_⟩
    have hfwd : fwdSweep g x =
        ((List.finRange w).map Fin.succ).foldl (fun s k => flipBit k (g k) s) (A x) := by
      unfold fwdSweep
      rw [List.finRange_succ, List.foldl_cons]
      rfl
    have hbwd : ∀ y, bwdSweep h y =
        C (((List.finRange w).reverse.map Fin.succ).foldl (fun s k => flipBit k (h k) s) y) := by
      intro y
      unfold bwdSweep
      rw [List.finRange_succ, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
        List.map_reverse]
      rfl
    rw [hbwd, hfwd]
    set y := A x
    obtain ⟨hf0, hft⟩ := lift_tail_foldl (List.finRange w) g gT (fun j s => by simp [g]) y
    set z := ((List.finRange w).map Fin.succ).foldl (fun s k => flipBit k (g k) s) y
    obtain ⟨hb0, hbtail⟩ := lift_tail_foldl (List.finRange w).reverse h hT (fun j s => by simp [h]) z
    have hmid : ((List.finRange w).reverse.map Fin.succ).foldl (fun s k => flipBit k (h k) s) z = ρ y := by
      ext k
      refine Fin.cases ?_ ?_ k
      · rw [hb0, hf0, hρ_pres]
      · intro i
        have hti := congrFun hbtail i
        rw [hti, hf0, hft]
        have hcons : Fin.cons (y 0) (fun j : Fin w => y j.succ) = y := by
          ext m
          refine Fin.cases rfl (fun _ => rfl) m
        cases hy0 : y 0
        · have h1 := congrFun (hbf (fun j => y j.succ)) i
          simp only [gT, hT, Bool.false_eq_true, ↓reduceIte]
          change bwdSweep hf (fwdSweep gf (fun j => y j.succ)) i = ρ y i.succ
          rw [h1]
          simp only [ρb, Equiv.coe_fn_mk]
          rw [← hy0, hcons]
        · have h1 := congrFun (hbt (fun j => y j.succ)) i
          simp only [gT, hT, ↓reduceIte]
          change bwdSweep ht (fwdSweep gt (fun j => y j.succ)) i = ρ y i.succ
          rw [h1]
          simp only [ρb, Equiv.coe_fn_mk]
          rw [← hy0, hcons]
    rw [hmid]
    change flipBit 0 c (flipBit 0 c (σ (flipBit 0 a (flipBit 0 a x)))) = σ x
    rw [flipBit_involutive 0 c hc_ind, flipBit_involutive 0 a ha_ind]

private def revState {w : ℕ} (s : Fin w → Bool) : Fin w → Bool :=
  fun i => s i.rev

private theorem revState_involutive {w : ℕ} (s : Fin w → Bool) :
    revState (revState s) = s := by
  ext i
  simp [revState]

private def revPerm (w : ℕ) : Equiv.Perm (Fin w → Bool) :=
  { toFun := revState
    invFun := revState
    left_inv := revState_involutive
    right_inv := revState_involutive }

private theorem revState_flipBit {w : ℕ} (k : Fin w) (g : (Fin w → Bool) → Bool)
    (s : Fin w → Bool) :
    revState (flipBit k g s) = flipBit k.rev (fun t => g (revState t)) (revState s) := by
  ext i
  by_cases hi : i = k.rev
  · subst hi
    simp [revState, flipBit, revState_involutive]
  · have hne : i.rev ≠ k := fun h => hi (by rw [← h, Fin.rev_rev])
    simp [revState, flipBit, hi, hne]

private theorem rev_conj_bwdSweep {w : ℕ} (h : Fin w → (Fin w → Bool) → Bool)
    (hh : ∀ k, IndepOf k (h k)) :
    ∃ g : Fin w → (Fin w → Bool) → Bool,
      (∀ k, IndepOf k (g k)) ∧
      ∀ x : Fin w → Bool, fwdSweep g x = revState (bwdSweep h (revState x)) := by
  let g : Fin w → (Fin w → Bool) → Bool := fun k t => h k.rev (revState t)
  have hg : ∀ k, IndepOf k (g k) := by
    intro k s t hst
    refine hh k.rev (revState s) (revState t) fun i hi => ?_
    exact hst i.rev (fun he => hi (by rw [← he, Fin.rev_rev]))
  refine ⟨g, hg, fun x => ?_⟩
  have hgen : ∀ (L : List (Fin w)) (u : Fin w → Bool),
      revState (L.foldl (fun s k => flipBit k (h k) s) u) =
      (L.map Fin.rev).foldl (fun s k => flipBit k (g k) s) (revState u) := by
    intro L
    induction L with
    | nil => intro u; rfl
    | cons k rest ih =>
      intro u
      simp only [List.foldl_cons, List.map_cons]
      rw [ih (flipBit k (h k) u), revState_flipBit]
      have hg' : g k.rev = fun t => h k (revState t) := by
        ext t; simp [g]
      rw [hg']
  have h1 := hgen (List.finRange w).reverse (revState x)
  rw [revState_involutive] at h1
  have hmap : (List.finRange w).reverse.map Fin.rev = List.finRange w := by
    rw [finRange_reverse_eq_map_rev, List.map_map]
    have hcomp : Fin.rev ∘ Fin.rev = (id : Fin w → Fin w) := by
      ext k; simp
    rw [hcomp, List.map_id]
  rw [hmap] at h1
  exact h1.symm

private theorem rev_two_sweeps (w : ℕ) :
    ∃ (g1 g2 : Fin w → (Fin w → Bool) → Bool),
      (∀ k, IndepOf k (g1 k)) ∧ (∀ k, IndepOf k (g2 k)) ∧
      ∀ x : Fin w → Bool, fwdSweep g2 (fwdSweep g1 x) = revState x := by
  let g1 : Fin w → (Fin w → Bool) → Bool :=
    fun k s => if k = k.rev then false else s k.rev
  let g2 : Fin w → (Fin w → Bool) → Bool :=
    fun k s => if k.val < k.rev.val then s k.rev else false
  have hg1 : ∀ k, IndepOf k (g1 k) := by
    intro k s t hst
    dsimp only [g1]
    split_ifs with hk
    · rfl
    · exact hst k.rev (Ne.symm hk)
  have hg2 : ∀ k, IndepOf k (g2 k) := by
    intro k s t hst
    dsimp only [g2]
    by_cases hk : k.val < k.rev.val
    · have hne : k.rev ≠ k := fun h => by omega
      simp only [hk, ↓reduceIte]
      exact hst k.rev hne
    · simp only [hk, ↓reduceIte]
  refine ⟨g1, g2, hg1, hg2, fun x => ?_⟩
  have hS1_step : ∀ (m : ℕ) (hm : m ≤ w) (i : Fin w),
      (((List.finRange m).map (fun j => (⟨j.val, by omega⟩ : Fin w))).foldl
        (fun s k => flipBit k (g1 k) s) x) i =
      if i.val < m then
        if i.val < i.rev.val then xor (x i) (x i.rev) else x i.rev
      else x i := by
    intro m
    induction m with
    | zero =>
      intro _ i
      simp
    | succ m ihm =>
      intro hm i
      rw [finRange_succ_append, List.map_append, List.map_singleton, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      set km : Fin w := ⟨m, by omega⟩
      have hmap_eq : ((List.finRange m).map Fin.castSucc).map (fun j => (⟨j.val, by omega⟩ : Fin w)) =
          (List.finRange m).map (fun j => (⟨j.val, by omega⟩ : Fin w)) := by
        rw [List.map_map]
        rfl
      rw [hmap_eq]
      set prev := ((List.finRange m).map (fun j => (⟨j.val, by omega⟩ : Fin w))).foldl
        (fun s k => flipBit k (g1 k) s) x
      have hprev : ∀ j : Fin w, prev j =
          if j.val < m then
            if j.val < j.rev.val then xor (x j) (x j.rev) else x j.rev
          else x j := ihm (by omega)
      by_cases hik : i = km
      · subst hik
        change flipBit km (g1 km) prev km = _
        rw [flipBit_apply_eq, hprev km]
        have hkm_not : ¬ km.val < m := by simp [km]
        simp only [hkm_not, ↓reduceIte]
        have hlt_succ : km.val < m + 1 := by simp [km]
        simp only [hlt_succ, ↓reduceIte]
        dsimp only [g1]
        split_ifs with hrev_eq hlt hlt
        · have : km.val = km.rev.val := congrArg Fin.val hrev_eq
          omega
        · simp only [Bool.xor_false]
          exact congrArg x hrev_eq
        · rw [hprev km.rev]
          have hrev_not : ¬ km.rev.val < m := by
            have : km.val = m := rfl
            omega
          simp only [hrev_not, ↓reduceIte]
        · rw [hprev km.rev]
          have hgt : km.rev.val < km.val := by
            have hne : km.val ≠ km.rev.val := fun h => hrev_eq (Fin.ext h)
            omega
          have hrev_lt_m : km.rev.val < m := by
            have : km.val = m := rfl
            omega
          simp only [hrev_lt_m, Fin.rev_rev, hgt, ↓reduceIte]
          cases x km <;> cases x km.rev <;> rfl
      · change flipBit km (g1 km) prev i = _
        rw [flipBit_apply_ne km (g1 km) prev hik, hprev i]
        have hne : i.val ≠ m := fun h => hik (Fin.ext h)
        by_cases hilt : i.val < m
        · have hilt' : i.val < m + 1 := by omega
          simp [hilt, hilt']
        · have hnot' : ¬ i.val < m + 1 := by omega
          simp [hilt, hnot']
  have hS1 : ∀ i : Fin w, fwdSweep g1 x i =
      if i.val < i.rev.val then xor (x i) (x i.rev) else x i.rev := by
    intro i
    have h := hS1_step w (le_refl w) i
    have hmap : (List.finRange w).map (fun j => (⟨j.val, by omega⟩ : Fin w)) = List.finRange w := by
      refine List.ext_getElem (by simp) fun t h1 h2 => ?_
      simp
    rw [hmap] at h
    simpa [fwdSweep, i.isLt] using h
  set y := fwdSweep g1 x
  have hS2_step : ∀ (m : ℕ) (hm : m ≤ w) (i : Fin w),
      (((List.finRange m).map (fun j => (⟨j.val, by omega⟩ : Fin w))).foldl
        (fun s k => flipBit k (g2 k) s) y) i =
      if i.val < m then x i.rev else y i := by
    intro m
    induction m with
    | zero =>
      intro _ i
      simp
    | succ m ihm =>
      intro hm i
      rw [finRange_succ_append, List.map_append, List.map_singleton, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      set km : Fin w := ⟨m, by omega⟩
      have hmap_eq : ((List.finRange m).map Fin.castSucc).map (fun j => (⟨j.val, by omega⟩ : Fin w)) =
          (List.finRange m).map (fun j => (⟨j.val, by omega⟩ : Fin w)) := by
        rw [List.map_map]
        rfl
      rw [hmap_eq]
      set prev := ((List.finRange m).map (fun j => (⟨j.val, by omega⟩ : Fin w))).foldl
        (fun s k => flipBit k (g2 k) s) y
      have hprev : ∀ j : Fin w, prev j = if j.val < m then x j.rev else y j := ihm (by omega)
      by_cases hik : i = km
      · subst hik
        change flipBit km (g2 km) prev km = _
        rw [flipBit_apply_eq, hprev km]
        have hkm_not : ¬ km.val < m := by simp [km]
        have hlt_succ : km.val < m + 1 := by simp [km]
        simp only [hkm_not, hlt_succ, ↓reduceIte]
        dsimp only [g2]
        by_cases hlt : km.val < km.rev.val
        · simp only [hlt, ↓reduceIte]
          rw [hprev km.rev]
          have hrev_not : ¬ km.rev.val < m := by
            have : km.val = m := rfl
            omega
          simp only [hrev_not, ↓reduceIte]
          have hy1 : y km = xor (x km) (x km.rev) := by
            simp only [y, hS1 km, hlt, ↓reduceIte]
          have hnotlt2 : ¬ km.rev.val < km.val := by omega
          have hy2 : y km.rev = x km := by
            simp only [y, hS1 km.rev, Fin.rev_rev, hnotlt2, ↓reduceIte]
          rw [hy1, hy2]
          cases x km <;> cases x km.rev <;> rfl
        · simp only [hlt, ↓reduceIte, Bool.xor_false]
          simp only [y, hS1 km, hlt, ↓reduceIte]
      · change flipBit km (g2 km) prev i = _
        rw [flipBit_apply_ne km (g2 km) prev hik, hprev i]
        have hne : i.val ≠ m := fun h => hik (Fin.ext h)
        by_cases hilt : i.val < m
        · have hilt' : i.val < m + 1 := by omega
          simp [hilt, hilt']
        · have hnot' : ¬ i.val < m + 1 := by omega
          simp [hilt, hnot']
  ext i
  have h := hS2_step w (le_refl w) i
  have hmap : (List.finRange w).map (fun j => (⟨j.val, by omega⟩ : Fin w)) = List.finRange w := by
    refine List.ext_getElem (by simp) fun t h1 h2 => ?_
    simp
  rw [hmap] at h
  simpa [fwdSweep, revState, i.isLt] using h

private def rotPow {d : ℕ} (r : ℕ) (s : Fin (d + 1) → Bool) : Fin (d + 1) → Bool :=
  fun i => s ⟨(i.val + r) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩

private def shiftStep {d : ℕ} (f : (Fin d → Bool) → Bool) (s : Fin (d + 1) → Bool) :
    Fin (d + 1) → Bool :=
  let z : Fin d → Bool := fun j => s j.succ
  Fin.snoc (α := fun _ : Fin (d + 1) => Bool) z (xor (s 0) (f z))

private theorem rotPow_zero {d : ℕ} (s : Fin (d + 1) → Bool) : rotPow 0 s = s := by
  ext i
  simp [rotPow, Nat.mod_eq_of_lt i.isLt]

private theorem rotPow_period {d : ℕ} (s : Fin (d + 1) → Bool) : rotPow (d + 1) s = s := by
  ext i
  simp [rotPow, Nat.mod_eq_of_lt i.isLt]

private theorem rotPow_add {d : ℕ} (a b : ℕ) (s : Fin (d + 1) → Bool) :
    rotPow a (rotPow b s) = rotPow (a + b) s := by
  ext i
  simp only [rotPow]
  congr 1
  ext
  simp [Nat.mod_add_mod, Nat.add_assoc]

private theorem sweep_to_shift {d : ℕ} (g : Fin (d + 1) → (Fin (d + 1) → Bool) → Bool)
    (hg : ∀ k, IndepOf k (g k)) :
    ∃ f : Fin (d + 1) → (Fin d → Bool) → Bool,
      ∀ x : Fin (d + 1) → Bool,
        (List.finRange (d + 1)).foldl (fun s k => shiftStep (f k) s) x = fwdSweep g x := by
  let f : Fin (d + 1) → (Fin d → Bool) → Bool :=
    fun k z => g k (rotPow (d + 1 - k.val) (Fin.cons false z))
  refine ⟨f, fun x => ?_⟩
  have hstep : ∀ (k : Fin (d + 1)) (u : Fin (d + 1) → Bool),
      shiftStep (f k) (rotPow k.val u) = rotPow (k.val + 1) (flipBit k (g k) u) := by
    intro k u
    set t := rotPow k.val u
    have hfk : f k (fun j => t j.succ) = g k u := by
      dsimp only [f]
      refine hg k _ u fun i hi => ?_
      simp only [rotPow]
      have hne0 : (⟨(i.val + (d + 1 - k.val)) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩ :
          Fin (d + 1)) ≠ 0 := by
        intro h0
        have hv : (i.val + (d + 1 - k.val)) % (d + 1) = 0 :=
          (congrArg Fin.val h0).trans (Fin.val_zero (d + 1))
        have hik : i.val = k.val := by
          by_cases hlt : i.val < k.val
          · have hlt' : i.val + (d + 1 - k.val) < d + 1 := by omega
            rw [Nat.mod_eq_of_lt hlt'] at hv
            omega
          · by_cases hgt : k.val < i.val
            · have heq : i.val + (d + 1 - k.val) = (i.val - k.val) + (d + 1) := by omega
              rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hv
              omega
            · omega
        exact hi (Fin.ext hik)
      set idx : Fin (d + 1) :=
        ⟨(i.val + (d + 1 - k.val)) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩
      obtain ⟨j, hj⟩ := Fin.eq_succ_of_ne_zero hne0
      rw [hj, Fin.cons_succ, ← hj]
      change t idx = u i
      simp only [t, rotPow]
      congr 1
      ext
      have hmod : ((i.val + (d + 1 - k.val)) % (d + 1) + k.val) % (d + 1) = i.val := by
        rw [Nat.mod_add_mod]
        have heq : i.val + (d + 1 - k.val) + k.val = i.val + (d + 1) := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
      exact hmod
    ext i
    refine Fin.lastCases ?_ ?_ i
    · simp only [shiftStep, Fin.snoc_last, rotPow]
      rw [hfk]
      have hidx1 : (⟨((Fin.last d).val + (k.val + 1)) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩ :
          Fin (d + 1)) = k := by
        ext
        simp only [Fin.val_last]
        have : d + (k.val + 1) = k.val + (d + 1) := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt k.isLt]
      have hidx0 : (⟨(0 + k.val) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩ : Fin (d + 1)) = k := by
        ext
        simp [Nat.mod_eq_of_lt k.isLt]
      rw [hidx1, flipBit_apply_eq]
      simp only [t, rotPow, Fin.val_zero]
      rw [hidx0]
    · intro j
      simp only [shiftStep, Fin.snoc_castSucc, rotPow]
      have hidx : (⟨(j.castSucc.val + (k.val + 1)) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩ :
          Fin (d + 1)) =
          ⟨(j.succ.val + k.val) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩ := by
        ext
        simp only [Fin.val_castSucc, Fin.val_succ]
        congr 1
        omega
      have hne_k : (⟨(j.succ.val + k.val) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩ :
          Fin (d + 1)) ≠ k := by
        intro heq
        have hv : (j.val + 1 + k.val) % (d + 1) = k.val := by
          simpa [Fin.val_succ] using congrArg Fin.val heq
        have hjlt : j.val < d := j.isLt
        have hklt : k.val < d + 1 := k.isLt
        by_cases hlt : j.val + 1 + k.val < d + 1
        · rw [Nat.mod_eq_of_lt hlt] at hv
          omega
        · have heq2 : j.val + 1 + k.val = (j.val + 1 + k.val - (d + 1)) + (d + 1) := by omega
          rw [heq2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hv
          omega
      rw [hidx, flipBit_apply_ne k (g k) u hne_k]
      rfl
  have hprefix : ∀ (m : ℕ) (hm : m ≤ d + 1),
      ((List.finRange m).map (fun j => (⟨j.val, by omega⟩ : Fin (d + 1)))).foldl
        (fun s k => shiftStep (f k) s) x =
      rotPow m (((List.finRange m).map (fun j => (⟨j.val, by omega⟩ : Fin (d + 1)))).foldl
        (fun s k => flipBit k (g k) s) x) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp [rotPow_zero]
    | succ m ihm =>
      intro hm
      rw [finRange_succ_append, List.map_append, List.map_singleton, List.foldl_append,
        List.foldl_cons, List.foldl_nil, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hmap_eq : ((List.finRange m).map Fin.castSucc).map (fun j => (⟨j.val, by omega⟩ : Fin (d + 1))) =
          (List.finRange m).map (fun j => (⟨j.val, by omega⟩ : Fin (d + 1))) := by
        rw [List.map_map]; rfl
      rw [hmap_eq, ihm (by omega)]
      exact hstep ⟨m, by omega⟩ _
  have hfull := hprefix (d + 1) (le_refl (d + 1))
  have hmap : (List.finRange (d + 1)).map (fun j => (⟨j.val, by omega⟩ : Fin (d + 1))) =
      List.finRange (d + 1) := by
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp
  rw [hmap, rotPow_period] at hfull
  exact hfull

theorem main_aux (d : ℕ) (perm : Equiv.Perm (Fin (d + 1) → Bool)) :
    ∃ control : Fin (4 * (d + 1)) → (Fin d → Bool) → Bool,
      ∀ x : Fin (d + 1) → Bool, (List.finRange (4 * (d + 1))).foldl (fun (s : Fin (d + 1) → Bool) row =>
        let z : Fin d → Bool := fun j => s j.succ
        Fin.snoc (α := fun _ : Fin (d + 1) => Bool) z (xor (s 0) (control row z))) x = perm x := by
  let w := d + 1
  obtain ⟨g1, h4, hg1, hh4, hbenes⟩ := benes_decomp w (perm.trans (revPerm w))
  obtain ⟨g4, hg4, hconj4⟩ := rev_conj_bwdSweep h4 hh4
  obtain ⟨g2, g3, hg2, hg3, hrev23⟩ := rev_two_sweeps w
  obtain ⟨f1, hf1⟩ := sweep_to_shift g1 hg1
  obtain ⟨f2, hf2⟩ := sweep_to_shift g2 hg2
  obtain ⟨f3, hf3⟩ := sweep_to_shift g3 hg3
  obtain ⟨f4, hf4⟩ := sweep_to_shift g4 hg4
  let control : Fin (4 * w) → (Fin d → Bool) → Bool := fun row z =>
    let q := row.val / w
    let k : Fin w := ⟨row.val % w, Nat.mod_lt _ (Nat.succ_pos d)⟩
    if q = 0 then f1 k z
    else if q = 1 then f2 k z
    else if q = 2 then f3 k z
    else f4 k z
  refine ⟨control, fun x => ?_⟩
  have hctrl0 : ∀ k : Fin w, control ⟨k.val, by omega⟩ = f1 k := by
    intro k; ext z
    have hq : k.val / w = 0 := Nat.div_eq_of_lt k.isLt
    have hr : (⟨k.val % w, Nat.mod_lt _ (Nat.succ_pos d)⟩ : Fin w) = k :=
      Fin.ext (Nat.mod_eq_of_lt k.isLt)
    dsimp only [control]
    rw [hq, hr]
    rfl
  have hctrl1 : ∀ k : Fin w, control ⟨w + k.val, by omega⟩ = f2 k := by
    intro k; ext z
    have hq : (w + k.val) / w = 1 := by
      have : w + k.val = k.val + 1 * w := by omega
      rw [this, Nat.add_mul_div_right _ _ (Nat.succ_pos d), Nat.div_eq_of_lt k.isLt]
    have hr : (⟨(w + k.val) % w, Nat.mod_lt _ (Nat.succ_pos d)⟩ : Fin w) = k :=
      Fin.ext (by show (w + k.val) % w = k.val; simp [Nat.mod_eq_of_lt k.isLt])
    dsimp only [control]
    rw [hq, hr]
    rfl
  have hctrl2 : ∀ k : Fin w, control ⟨2 * w + k.val, by omega⟩ = f3 k := by
    intro k; ext z
    have hq : (2 * w + k.val) / w = 2 := by
      have : 2 * w + k.val = k.val + 2 * w := by omega
      rw [this, Nat.add_mul_div_right _ _ (Nat.succ_pos d), Nat.div_eq_of_lt k.isLt]
    have hr : (⟨(2 * w + k.val) % w, Nat.mod_lt _ (Nat.succ_pos d)⟩ : Fin w) = k :=
      Fin.ext (by
        show (2 * w + k.val) % w = k.val
        have : 2 * w + k.val = k.val + w * 2 := by omega
        rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k.isLt])
    dsimp only [control]
    rw [hq, hr]
    rfl
  have hctrl3 : ∀ k : Fin w, control ⟨3 * w + k.val, by omega⟩ = f4 k := by
    intro k; ext z
    have hq : (3 * w + k.val) / w = 3 := by
      have : 3 * w + k.val = k.val + 3 * w := by omega
      rw [this, Nat.add_mul_div_right _ _ (Nat.succ_pos d), Nat.div_eq_of_lt k.isLt]
    have hr : (⟨(3 * w + k.val) % w, Nat.mod_lt _ (Nat.succ_pos d)⟩ : Fin w) = k :=
      Fin.ext (by
        show (3 * w + k.val) % w = k.val
        have : 3 * w + k.val = k.val + w * 3 := by omega
        rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k.isLt])
    dsimp only [control]
    rw [hq, hr]
    rfl
  change (List.finRange (4 * w)).foldl (fun s row => shiftStep (control row) s) x = perm x
  rw [finRange_four_mul w, List.foldl_append, List.foldl_append, List.foldl_append,
    List.foldl_map, List.foldl_map, List.foldl_map, List.foldl_map]
  simp only [hctrl0, hctrl1, hctrl2, hctrl3]
  rw [hf1, hf2, hf3, hf4, hrev23, hconj4, revState_involutive, hbenes]
  exact revState_involutive (perm x)

end PEqualNP.Outside.L_lib_394_aux

theorem PEqualNP.Outside.L_lib_394 : ∀ d : ℕ,
  let w := d + 1
  let State := Fin w → Bool
  let Tail := Fin d → Bool
  ∀ perm : Equiv.Perm State,
    ∃ control : Fin (4 * w) → Tail → Bool,
      ∀ x : State, (List.finRange (4 * w)).foldl (fun (s : State) row =>
        let z : Tail := fun j => s j.succ
        Fin.snoc (α := fun _ : Fin w => Bool) z (xor (s 0) (control row z))) x = perm x := by
  intro d w State Tail perm
  exact PEqualNP.Outside.L_lib_394_aux.main_aux d perm
