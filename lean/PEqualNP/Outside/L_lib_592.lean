import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_377



namespace PEqualNP.Outside.L_lib_592_aux.RouteData

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

end PEqualNP.Outside.L_lib_592_aux.RouteData

namespace PEqualNP.Outside.L_lib_592_aux

theorem routeSource : ∀ d : ℕ,
  let w := d + 1
  let State := Fin w → Bool
  let Tail := Fin d → Bool
  ∀ perm : Equiv.Perm State,
    ∃ control : Fin (4 * w) → Tail → Bool,
      ∀ x : State, (List.finRange (4 * w)).foldl (fun (s : State) row =>
        let z : Tail := fun j => s j.succ
        Fin.snoc (α := fun _ : Fin w => Bool) z (xor (s 0) (control row z))) x = perm x := by
  intro d w State Tail perm
  exact PEqualNP.Outside.L_lib_592_aux.RouteData.main_aux d perm

end PEqualNP.Outside.L_lib_592_aux


namespace PEqualNP.Outside.L_lib_592_aux.RankData

lemma ringChar_dvd_iff {K : Type} [Field K] (n : ℕ) :
    ringChar K ∣ n ↔ (n : K) = 0 := by
  exact (CharP.cast_eq_zero_iff K (ringChar K) n).symm

lemma ringChar_eq_two_iff {K : Type} [Field K] :
    ringChar K = 2 ↔ (2 : K) = 0 := by
  constructor
  · intro h
    have hdiv : ringChar K ∣ 2 := by rw [h]
    exact (ringChar_dvd_iff 2).mp hdiv
  · intro h2
    have hdiv : ringChar K ∣ 2 := (ringChar_dvd_iff 2).mpr h2
    have hle : ringChar K ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    have hne0 : ringChar K ≠ 0 := by
      intro h0
      rw [h0] at hdiv
      exact absurd (zero_dvd_iff.mp hdiv) (by norm_num)
    have hne1 : ringChar K ≠ 1 := by
      intro h1
      have hdiv1 : ringChar K ∣ 1 := by rw [h1]
      have h10 : ((1 : ℕ) : K) = 0 := (ringChar_dvd_iff 1).mp hdiv1
      simp at h10
    omega

def delta {K : Type} [Field K] {α : Type} [DecidableEq α] (x y : α) : K :=
  if x = y then 1 else 0

lemma delta_comm {K : Type} [Field K] {α : Type} [DecidableEq α] (x y : α) :
    delta (K := K) x y = delta y x := by
  unfold delta
  by_cases h : x = y
  · subst h
    simp
  · have h' : y ≠ x := Ne.symm h
    simp [h, h']

lemma fixed_cast {K : Type} [Field K] {q : ℕ} (p r : Equiv.Perm (Fin q)) :
    (((Finset.univ : Finset (Fin q)).filter (fun i => r (p i) = i)).card : K) =
      ∑ i : Fin q, delta (K := K) (r (p i)) i := by
  unfold delta
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

def X {K : Type} [Field K] {b : ℕ} (p : Equiv.Perm (Fin (b + 2)))
    (i j : Fin (b + 1)) : K :=
  delta (p j.castSucc) i.castSucc - delta (p (Fin.last (b + 1))) i.castSucc

lemma sum_X_mul_delta {K : Type} [Field K] {b : ℕ} (r : Equiv.Perm (Fin (b + 2)))
    (i : Fin (b + 1)) (x : Fin (b + 2)) :
    ∑ k : Fin (b + 1), X (K := K) r i k * delta x k.castSucc =
      delta (r x) i.castSucc - delta (r (Fin.last (b + 1))) i.castSucc := by
  refine Fin.lastCases ?_ ?_ x
  · have hzero : ∀ k : Fin (b + 1), delta (K := K) (Fin.last (b + 1)) k.castSucc = 0 := by
      intro k
      unfold delta
      have hne : Fin.last (b + 1) ≠ k.castSucc := Ne.symm (Fin.castSucc_ne_last k)
      simp [hne]
    simp [hzero]
  · intro m
    rw [Finset.sum_eq_single m]
    · simp [delta, X]
    · intro k _ hkm
      unfold delta
      have hne : m.castSucc ≠ k.castSucc := fun h => hkm (Fin.castSucc_injective _ h).symm
      simp [hne]
    · intro hm
      exact absurd (Finset.mem_univ m) hm

lemma X_mul {K : Type} [Field K] {b : ℕ} (r p : Equiv.Perm (Fin (b + 2)))
    (i j : Fin (b + 1)) :
    ∑ k : Fin (b + 1), X (K := K) r i k * X (K := K) p k j = X (K := K) (r * p) i j := by
  have h1 :
      ∑ k : Fin (b + 1), X (K := K) r i k * X (K := K) p k j =
        (∑ k : Fin (b + 1), X (K := K) r i k * delta (p j.castSucc) k.castSucc) -
          (∑ k : Fin (b + 1), X (K := K) r i k * delta (p (Fin.last (b + 1))) k.castSucc) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold X
    ring
  rw [h1, sum_X_mul_delta, sum_X_mul_delta]
  unfold X
  simp only [Equiv.Perm.mul_apply]
  ring

lemma sum_delta_eq_one {K : Type} [Field K] {q : ℕ} (x : Fin q) :
    ∑ i : Fin q, delta (K := K) x i = 1 := by
  rw [Finset.sum_eq_single x]
  · unfold delta
    simp
  · intro i _ hix
    unfold delta
    have hne : x ≠ i := Ne.symm hix
    simp [hne]
  · intro hx
    exact absurd (Finset.mem_univ x) hx

lemma X_trace {K : Type} [Field K] {b : ℕ} (s : Equiv.Perm (Fin (b + 2))) :
    (∑ i : Fin (b + 1), X (K := K) s i i) + 1 =
      ∑ i : Fin (b + 2), delta (K := K) (s i) i := by
  have h1 :
      ∑ i : Fin (b + 2), delta (K := K) (s (Fin.last (b + 1))) i = 1 :=
    sum_delta_eq_one (s (Fin.last (b + 1)))
  rw [Fin.sum_univ_castSucc] at h1
  rw [Fin.sum_univ_castSucc (f := fun i : Fin (b + 2) => delta (K := K) (s i) i)]
  unfold X
  rw [Finset.sum_sub_distrib]
  linear_combination -h1

lemma X_row_sum {K : Type} [Field K] {b : ℕ} (hq : ((b + 2 : ℕ) : K) = 0)
    (s : Equiv.Perm (Fin (b + 2))) (i : Fin (b + 1)) :
    ∑ k : Fin (b + 1), X (K := K) s i k = 1 := by
  have hperm :
      ∑ k : Fin (b + 2), delta (K := K) (s k) i.castSucc = 1 := by
    rw [Equiv.sum_comp s (fun y => delta (K := K) y i.castSucc)]
    have hcomm :
        (∑ y : Fin (b + 2), delta (K := K) y i.castSucc) =
          ∑ y : Fin (b + 2), delta (K := K) i.castSucc y :=
      Finset.sum_congr rfl (fun y _ => delta_comm y i.castSucc)
    rw [hcomm]
    exact sum_delta_eq_one i.castSucc
  rw [Fin.sum_univ_castSucc] at hperm
  unfold X
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hq' : ((b + 1 : ℕ) : K) + 1 = 0 := by
    push_cast at hq ⊢
    linear_combination hq
  linear_combination hperm - delta (K := K) (s (Fin.last (b + 1))) i.castSucc * hq'

def Y {K : Type} [Field K] {b : ℕ} (p : Equiv.Perm (Fin (b + 2))) (i j : Fin b) : K :=
  X p i.castSucc j.castSucc - X p (Fin.last b) j.castSucc

lemma Y_mul {K : Type} [Field K] {b : ℕ} (hq : ((b + 2 : ℕ) : K) = 0)
    (r p : Equiv.Perm (Fin (b + 2))) (i j : Fin b) :
    ∑ k : Fin b, Y (K := K) r i k * Y (K := K) p k j = Y (K := K) (r * p) i j := by
  have hext :
      ∑ k : Fin b, Y (K := K) r i k * Y (K := K) p k j =
        ∑ k : Fin (b + 1),
          (X (K := K) r i.castSucc k - X (K := K) r (Fin.last b) k) *
            (X (K := K) p k j.castSucc - X (K := K) p (Fin.last b) j.castSucc) := by
    rw [Fin.sum_univ_castSucc]
    simp [Y]
  rw [hext]
  have hsplit :
      ∑ k : Fin (b + 1),
          (X (K := K) r i.castSucc k - X (K := K) r (Fin.last b) k) *
            (X (K := K) p k j.castSucc - X (K := K) p (Fin.last b) j.castSucc) =
        (∑ k : Fin (b + 1), X (K := K) r i.castSucc k * X (K := K) p k j.castSucc) -
          (∑ k : Fin (b + 1), X (K := K) r (Fin.last b) k * X (K := K) p k j.castSucc) -
          X (K := K) p (Fin.last b) j.castSucc *
            ((∑ k : Fin (b + 1), X (K := K) r i.castSucc k) -
              (∑ k : Fin (b + 1), X (K := K) r (Fin.last b) k)) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [hsplit, X_mul, X_mul, X_row_sum hq, X_row_sum hq]
  unfold Y
  ring

lemma Y_trace {K : Type} [Field K] {b : ℕ} (hq : ((b + 2 : ℕ) : K) = 0)
    (s : Equiv.Perm (Fin (b + 2))) :
    (∑ i : Fin b, Y (K := K) s i i) + 2 =
      ∑ i : Fin (b + 2), delta (K := K) (s i) i := by
  have hext :
      ∑ i : Fin b, Y (K := K) s i i =
        ∑ i : Fin (b + 1), (X (K := K) s i i - X (K := K) s (Fin.last b) i) := by
    rw [Fin.sum_univ_castSucc]
    simp [Y]
  rw [hext, Finset.sum_sub_distrib, X_row_sum hq s (Fin.last b)]
  have ht := X_trace (K := K) s
  linear_combination ht

lemma exists_factor_of_fintype {K : Type} [Field K] {P ι : Type} [Fintype ι] {d : ℕ}
    (f : P → P → K) (A0 B0 : P → ι → K)
    (hf : ∀ p r, f p r = ∑ x : ι, A0 p x * B0 r x)
    (hd : Fintype.card ι ≤ d) :
    ∃ A B : P → Fin d → K, ∀ p r, f p r = ∑ j : Fin d, A p j * B r j := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let A : P → Fin d → K := fun p j =>
    if hj : j.val < Fintype.card ι then A0 p (e.symm ⟨j.val, hj⟩) else 0
  let B : P → Fin d → K := fun r j =>
    if hj : j.val < Fintype.card ι then B0 r (e.symm ⟨j.val, hj⟩) else 0
  refine ⟨A, B, fun p r => ?_⟩
  rw [hf p r]
  have h1 :
      ∑ j : Fin d, A p j * B r j =
        ∑ m : Fin (Fintype.card ι), A0 p (e.symm m) * B0 r (e.symm m) := by
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (Fin.castLE hd)))]
    · rw [Finset.sum_image (fun a _ b _ hab => Fin.castLE_injective hd hab)]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      simp only [A, B, Fin.val_castLE, m.isLt, ↓reduceDIte]
    · intro j _ hj
      have hnot : ¬ j.val < Fintype.card ι := by
        intro hlt
        exact hj (Finset.mem_image.mpr ⟨⟨j.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      simp only [A, B, hnot, ↓reduceDIte, mul_zero]
  rw [h1]
  exact (Fintype.sum_equiv e.symm
    (fun m => A0 p (e.symm m) * B0 r (e.symm m))
    (fun x => A0 p x * B0 r x)
    (fun _ => rfl)).symm

lemma upper_bound_nondiv {K : Type} [Field K] (b d : ℕ)
    (hd : (b + 1) ^ 2 + 1 ≤ d) :
    ∃ (A B : Equiv.Perm (Fin (b + 2)) → Fin d → K),
      ∀ p r,
        (((Finset.univ : Finset (Fin (b + 2))).filter (fun i => r (p i) = i)).card : K) =
          ∑ j : Fin d, A p j * B r j := by
  let ι := (Fin (b + 1) × Fin (b + 1)) ⊕ Unit
  let A0 : Equiv.Perm (Fin (b + 2)) → ι → K := fun p x =>
    match x with
    | Sum.inl (i, j) => X p j i
    | Sum.inr () => 1
  let B0 : Equiv.Perm (Fin (b + 2)) → ι → K := fun r x =>
    match x with
    | Sum.inl (i, j) => X r i j
    | Sum.inr () => 1
  refine exists_factor_of_fintype _ A0 B0 (fun p r => ?_) ?_
  · rw [fixed_cast]
    dsimp only [ι]
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique (ι := Unit)]
    simp only [A0, B0, mul_one]
    have hmul :
        (∑ i : Fin (b + 1), ∑ j : Fin (b + 1), X (K := K) p j i * X (K := K) r i j) =
          ∑ i : Fin (b + 1), X (K := K) (r * p) i i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hcomm :
          (∑ j : Fin (b + 1), X (K := K) p j i * X (K := K) r i j) =
            ∑ j : Fin (b + 1), X (K := K) r i j * X (K := K) p j i :=
        Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      rw [hcomm, X_mul]
    rw [hmul]
    exact (X_trace (K := K) (r * p)).symm
  · simpa [ι, sq] using hd

lemma upper_bound_div_char2 {K : Type} [Field K] (b d : ℕ)
    (hq : ((b + 2 : ℕ) : K) = 0) (h2 : (2 : K) = 0) (hd : b ^ 2 ≤ d) :
    ∃ (A B : Equiv.Perm (Fin (b + 2)) → Fin d → K),
      ∀ p r,
        (((Finset.univ : Finset (Fin (b + 2))).filter (fun i => r (p i) = i)).card : K) =
          ∑ j : Fin d, A p j * B r j := by
  let ι := Fin b × Fin b
  let A0 : Equiv.Perm (Fin (b + 2)) → ι → K := fun p x => Y p x.2 x.1
  let B0 : Equiv.Perm (Fin (b + 2)) → ι → K := fun r x => Y r x.1 x.2
  refine exists_factor_of_fintype _ A0 B0 (fun p r => ?_) ?_
  · rw [fixed_cast]
    dsimp only [ι]
    rw [Fintype.sum_prod_type]
    simp only [A0, B0]
    have hmul :
        (∑ i : Fin b, ∑ j : Fin b, Y (K := K) p j i * Y (K := K) r i j) =
          ∑ i : Fin b, Y (K := K) (r * p) i i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hcomm :
          (∑ j : Fin b, Y (K := K) p j i * Y (K := K) r i j) =
            ∑ j : Fin b, Y (K := K) r i j * Y (K := K) p j i :=
        Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      rw [hcomm, Y_mul hq]
    rw [hmul]
    have ht := Y_trace (K := K) hq (r * p)
    rw [h2, add_zero] at ht
    exact ht.symm
  · simpa [ι, sq] using hd

lemma upper_bound_div_ne2 {K : Type} [Field K] (b d : ℕ)
    (hq : ((b + 2 : ℕ) : K) = 0) (hd : b ^ 2 + 1 ≤ d) :
    ∃ (A B : Equiv.Perm (Fin (b + 2)) → Fin d → K),
      ∀ p r,
        (((Finset.univ : Finset (Fin (b + 2))).filter (fun i => r (p i) = i)).card : K) =
          ∑ j : Fin d, A p j * B r j := by
  let ι := (Fin b × Fin b) ⊕ Unit
  let A0 : Equiv.Perm (Fin (b + 2)) → ι → K := fun p x =>
    match x with
    | Sum.inl (i, j) => Y p j i
    | Sum.inr () => 2
  let B0 : Equiv.Perm (Fin (b + 2)) → ι → K := fun r x =>
    match x with
    | Sum.inl (i, j) => Y r i j
    | Sum.inr () => 1
  refine exists_factor_of_fintype _ A0 B0 (fun p r => ?_) ?_
  · rw [fixed_cast]
    dsimp only [ι]
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique (ι := Unit)]
    simp only [A0, B0, mul_one]
    have hmul :
        (∑ i : Fin b, ∑ j : Fin b, Y (K := K) p j i * Y (K := K) r i j) =
          ∑ i : Fin b, Y (K := K) (r * p) i i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hcomm :
          (∑ j : Fin b, Y (K := K) p j i * Y (K := K) r i j) =
            ∑ j : Fin b, Y (K := K) r i j * Y (K := K) p j i :=
        Finset.sum_congr rfl (fun j _ => mul_comm _ _)
      rw [hcomm, Y_mul hq]
    rw [hmul]
    exact (Y_trace (K := K) hq (r * p)).symm
  · simpa [ι, sq] using hd

def p1 {b : ℕ} (i j : Fin (b + 1)) : Equiv.Perm (Fin (b + 2)) :=
  Equiv.swap i.castSucc j.castSucc

def p2 {b : ℕ} (i j : Fin (b + 1)) : Equiv.Perm (Fin (b + 2)) :=
  Equiv.swap j.castSucc (Fin.last (b + 1)) * Equiv.swap i.castSucc j.castSucc

lemma p1_apply_i {b : ℕ} (i j : Fin (b + 1)) :
    p1 i j i.castSucc = j.castSucc := by
  simp [p1]

lemma p1_apply_last {b : ℕ} (i j : Fin (b + 1)) :
    p1 i j (Fin.last (b + 1)) = Fin.last (b + 1) := by
  unfold p1
  rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm (Fin.castSucc_ne_last i))
    (Ne.symm (Fin.castSucc_ne_last j))]

lemma p2_apply_i {b : ℕ} (i j : Fin (b + 1)) :
    p2 i j i.castSucc = Fin.last (b + 1) := by
  simp [p2]

lemma p2_apply_last {b : ℕ} (i j : Fin (b + 1)) :
    p2 i j (Fin.last (b + 1)) = j.castSucc := by
  unfold p2
  rw [Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm (Fin.castSucc_ne_last i))
      (Ne.symm (Fin.castSucc_ne_last j)),
    Equiv.swap_apply_right]

lemma p2_eq_p1_of_ne {b : ℕ} (i j : Fin (b + 1)) (x : Fin (b + 2))
    (h1 : x ≠ i.castSucc) (h2 : x ≠ Fin.last (b + 1)) :
    p2 i j x = p1 i j x := by
  unfold p2 p1
  rw [Equiv.Perm.mul_apply]
  have hne1 : Equiv.swap i.castSucc j.castSucc x ≠ j.castSucc := by
    intro h
    have hx : x = i.castSucc := (Equiv.swap i.castSucc j.castSucc).injective (by
      rw [h, Equiv.swap_apply_left])
    exact h1 hx
  have hne2 : Equiv.swap i.castSucc j.castSucc x ≠ Fin.last (b + 1) := by
    intro h
    have hx : x = Fin.last (b + 1) := (Equiv.swap i.castSucc j.castSucc).injective (by
      rw [h, Equiv.swap_apply_of_ne_of_ne (Ne.symm (Fin.castSucc_ne_last i))
        (Ne.symm (Fin.castSucc_ne_last j))])
    exact h2 hx
  rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]

def H {K : Type} [Field K] {n : ℕ} (i j : Fin n) : K :=
  delta i j + 1

lemma H_comm {K : Type} [Field K] {n : ℕ} (i j : Fin n) :
    H (K := K) i j = H j i := by
  unfold H
  rw [delta_comm]

lemma fixed_diff_left {K : Type} [Field K] {b : ℕ} (i j : Fin (b + 1))
    (r : Equiv.Perm (Fin (b + 2))) :
    (∑ k : Fin (b + 2), delta (K := K) (r (p1 i j k)) k) -
        (∑ k : Fin (b + 2), delta (K := K) (r (p2 i j k)) k) =
      delta (r j.castSucc) i.castSucc - delta (r (Fin.last (b + 1))) i.castSucc +
        delta (r (Fin.last (b + 1))) (Fin.last (b + 1)) -
        delta (r j.castSucc) (Fin.last (b + 1)) := by
  rw [← Finset.sum_sub_distrib, Fin.sum_univ_castSucc]
  rw [p1_apply_last, p2_apply_last]
  have hsingle :
      ∑ k : Fin (b + 1),
          (delta (K := K) (r (p1 i j k.castSucc)) k.castSucc -
            delta (K := K) (r (p2 i j k.castSucc)) k.castSucc) =
        delta (r j.castSucc) i.castSucc - delta (r (Fin.last (b + 1))) i.castSucc := by
    rw [Finset.sum_eq_single i]
    · rw [p1_apply_i, p2_apply_i]
    · intro k _ hki
      have hne1 : k.castSucc ≠ i.castSucc := fun h => hki (Fin.castSucc_injective _ h)
      have hne2 : k.castSucc ≠ Fin.last (b + 1) := Fin.castSucc_ne_last k
      rw [p2_eq_p1_of_ne i j k.castSucc hne1 hne2, sub_self]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [hsingle]
  ring

lemma delta_p1_sub_p2 {K : Type} [Field K] {b : ℕ} (a c : Fin (b + 1))
    (x y : Fin (b + 2)) :
    delta (K := K) (p1 a c x) y - delta (K := K) (p2 a c x) y =
      (delta x a.castSucc - delta x (Fin.last (b + 1))) *
        (delta y c.castSucc - delta y (Fin.last (b + 1))) := by
  by_cases hx1 : x = a.castSucc
  · subst hx1
    rw [p1_apply_i, p2_apply_i]
    have hne : a.castSucc ≠ Fin.last (b + 1) := Fin.castSucc_ne_last a
    rw [delta_comm c.castSucc y, delta_comm (Fin.last (b + 1)) y]
    unfold delta
    simp [hne]
  · by_cases hx2 : x = Fin.last (b + 1)
    · subst hx2
      rw [p1_apply_last, p2_apply_last]
      have hne : Fin.last (b + 1) ≠ a.castSucc := Ne.symm (Fin.castSucc_ne_last a)
      rw [delta_comm c.castSucc y, delta_comm (Fin.last (b + 1)) y]
      unfold delta
      simp [hne]
    · rw [p2_eq_p1_of_ne a c x hx1 hx2, sub_self]
      unfold delta
      simp [hx1, hx2]

lemma fixed_diff_both {K : Type} [Field K] {b : ℕ} (i j a c : Fin (b + 1)) :
    ((∑ k : Fin (b + 2), delta (K := K) (p1 c a (p1 i j k)) k) -
      (∑ k : Fin (b + 2), delta (K := K) (p1 c a (p2 i j k)) k)) -
    ((∑ k : Fin (b + 2), delta (K := K) (p2 c a (p1 i j k)) k) -
      (∑ k : Fin (b + 2), delta (K := K) (p2 c a (p2 i j k)) k)) =
      H (K := K) i a * H (K := K) j c := by
  rw [fixed_diff_left i j (p1 c a), fixed_diff_left i j (p2 c a)]
  have h1 :
      (delta (K := K) (p1 c a j.castSucc) i.castSucc -
        delta (K := K) (p1 c a (Fin.last (b + 1))) i.castSucc +
        delta (K := K) (p1 c a (Fin.last (b + 1))) (Fin.last (b + 1)) -
        delta (K := K) (p1 c a j.castSucc) (Fin.last (b + 1))) -
      (delta (K := K) (p2 c a j.castSucc) i.castSucc -
        delta (K := K) (p2 c a (Fin.last (b + 1))) i.castSucc +
        delta (K := K) (p2 c a (Fin.last (b + 1))) (Fin.last (b + 1)) -
        delta (K := K) (p2 c a j.castSucc) (Fin.last (b + 1))) =
      (delta (p1 c a j.castSucc) i.castSucc - delta (p2 c a j.castSucc) i.castSucc) -
      (delta (p1 c a (Fin.last (b + 1))) i.castSucc -
        delta (p2 c a (Fin.last (b + 1))) i.castSucc) +
      (delta (p1 c a (Fin.last (b + 1))) (Fin.last (b + 1)) -
        delta (p2 c a (Fin.last (b + 1))) (Fin.last (b + 1))) -
      (delta (p1 c a j.castSucc) (Fin.last (b + 1)) -
        delta (p2 c a j.castSucc) (Fin.last (b + 1))) := by
    ring
  rw [h1, delta_p1_sub_p2, delta_p1_sub_p2, delta_p1_sub_p2, delta_p1_sub_p2]
  have hd_jc : delta (K := K) j.castSucc c.castSucc = delta j c := by
    unfold delta
    simp [Fin.castSucc_inj]
  have hd_ia : delta (K := K) i.castSucc a.castSucc = delta i a := by
    unfold delta
    simp [Fin.castSucc_inj]
  have hd_jL : delta (K := K) j.castSucc (Fin.last (b + 1)) = 0 := by
    unfold delta
    simp [Fin.castSucc_ne_last]
  have hd_iL : delta (K := K) i.castSucc (Fin.last (b + 1)) = 0 := by
    unfold delta
    simp [Fin.castSucc_ne_last]
  have hd_Lc : delta (K := K) (Fin.last (b + 1)) c.castSucc = 0 := by
    unfold delta
    simp [Ne.symm (Fin.castSucc_ne_last c)]
  have hd_La : delta (K := K) (Fin.last (b + 1)) a.castSucc = 0 := by
    unfold delta
    simp [Ne.symm (Fin.castSucc_ne_last a)]
  have hd_LL : delta (K := K) (Fin.last (b + 1)) (Fin.last (b + 1)) = 1 := by
    unfold delta
    simp
  rw [hd_jc, hd_ia, hd_jL, hd_iL, hd_Lc, hd_La, hd_LL]
  unfold H
  ring

lemma fixed_diff_one {K : Type} [Field K] {b : ℕ} (i j : Fin (b + 1)) :
    (∑ k : Fin (b + 2), delta (K := K) ((1 : Equiv.Perm (Fin (b + 2))) (p1 i j k)) k) -
      (∑ k : Fin (b + 2), delta (K := K) ((1 : Equiv.Perm (Fin (b + 2))) (p2 i j k)) k) =
      H (K := K) i j := by
  rw [fixed_diff_left]
  simp only [Equiv.Perm.one_apply]
  have hd_ji : delta (K := K) j.castSucc i.castSucc = delta i j := by
    rw [delta_comm]
    unfold delta
    simp [Fin.castSucc_inj]
  have hd_Li : delta (K := K) (Fin.last (b + 1)) i.castSucc = 0 := by
    unfold delta
    simp [Ne.symm (Fin.castSucc_ne_last i)]
  have hd_jL : delta (K := K) j.castSucc (Fin.last (b + 1)) = 0 := by
    unfold delta
    simp [Fin.castSucc_ne_last]
  have hd_LL : delta (K := K) (Fin.last (b + 1)) (Fin.last (b + 1)) = 1 := by
    unfold delta
    simp
  rw [hd_ji, hd_Li, hd_jL, hd_LL]
  unfold H
  ring

lemma fixed_one_diff {K : Type} [Field K] {b : ℕ} (a c : Fin (b + 1)) :
    (∑ k : Fin (b + 2), delta (K := K) (p1 c a ((1 : Equiv.Perm (Fin (b + 2))) k)) k) -
      (∑ k : Fin (b + 2), delta (K := K) (p2 c a ((1 : Equiv.Perm (Fin (b + 2))) k)) k) =
      H (K := K) a c := by
  have h := fixed_diff_one (K := K) c a
  simp only [Equiv.Perm.one_apply] at h ⊢
  rw [h, H_comm]

lemma fixed_one_one {K : Type} [Field K] {b : ℕ} :
    ∑ k : Fin (b + 2),
        delta (K := K) ((1 : Equiv.Perm (Fin (b + 2))) ((1 : Equiv.Perm (Fin (b + 2))) k)) k =
      ((b + 2 : ℕ) : K) := by
  simp [delta]

def dot {K : Type} [Field K] {d : ℕ} (u v : Fin d → K) : K :=
  ∑ k : Fin d, u k * v k

lemma dot_sub_left {K : Type} [Field K] {d : ℕ} (u1 u2 v : Fin d → K) :
    dot (u1 - u2) v = dot u1 v - dot u2 v := by
  unfold dot
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [sub_mul]

lemma dot_sub_right {K : Type} [Field K] {d : ℕ} (u v1 v2 : Fin d → K) :
    dot u (v1 - v2) = dot u v1 - dot u v2 := by
  unfold dot
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [mul_sub]

lemma dot_smul_left {K : Type} [Field K] {d : ℕ} (c : K) (u v : Fin d → K) :
    dot (c • u) v = c * dot u v := by
  unfold dot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp [mul_assoc]

lemma dot_smul_right {K : Type} [Field K] {d : ℕ} (c : K) (u v : Fin d → K) :
    dot u (c • v) = c * dot u v := by
  unfold dot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma dot_sum_left {K : Type} [Field K] {d : ℕ} {α : Type} (s : Finset α)
    (f : α → Fin d → K) (v : Fin d → K) :
    dot (∑ x ∈ s, f x) v = ∑ x ∈ s, dot (f x) v := by
  unfold dot
  simp only [Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

lemma dot_sum_right {K : Type} [Field K] {d : ℕ} {α : Type} (s : Finset α)
    (u : Fin d → K) (g : α → Fin d → K) :
    dot u (∑ x ∈ s, g x) = ∑ x ∈ s, dot u (g x) := by
  unfold dot
  simp only [Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

lemma card_le_of_biorthogonal {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (U V : ι → Fin d → K)
    (hUV : ∀ a c : ι, dot (U a) (V c) = delta a c) :
    Fintype.card ι ≤ d := by
  have hli : LinearIndependent K V := by
    rw [Fintype.linearIndependent_iff]
    intro g hg a
    have h0 : dot (U a) (∑ c : ι, g c • V c) = 0 := by
      rw [hg]
      simp [dot]
    rw [dot_sum_right] at h0
    have h1 :
        ∑ c : ι, dot (U a) (g c • V c) = g a := by
      rw [Finset.sum_eq_single a]
      · rw [dot_smul_right, hUV a a]
        unfold delta
        simp
      · intro c _ hca
        rw [dot_smul_right, hUV a c]
        unfold delta
        have hne : a ≠ c := Ne.symm hca
        simp [hne]
      · intro ha
        exact absurd (Finset.mem_univ a) ha
    rw [h1] at h0
    exact h0
  have hle := hli.fintype_card_le_finrank
  simpa [Module.finrank_fin_fun] using hle

def Hinv {K : Type} [Field K] {b : ℕ} (i j : Fin (b + 1)) : K :=
  delta i j - ((b + 2 : ℕ) : K)⁻¹

lemma H_mul_Hinv {K : Type} [Field K] {b : ℕ} (hq : ((b + 2 : ℕ) : K) ≠ 0)
    (i j : Fin (b + 1)) :
    ∑ k : Fin (b + 1), H (K := K) i k * Hinv (K := K) k j = delta i j := by
  have hsplit :
      ∑ k : Fin (b + 1), H (K := K) i k * Hinv (K := K) k j =
        (∑ k : Fin (b + 1), delta (K := K) i k * delta k j) -
        ((b + 2 : ℕ) : K)⁻¹ * (∑ k : Fin (b + 1), delta (K := K) i k) +
        (∑ k : Fin (b + 1), delta (K := K) k j) -
        ((b + 2 : ℕ) : K)⁻¹ * ((b + 1 : ℕ) : K) := by
    have hconst :
        ∑ k : Fin (b + 1), ((b + 2 : ℕ) : K)⁻¹ = ((b + 2 : ℕ) : K)⁻¹ * ((b + 1 : ℕ) : K) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
    rw [← hconst, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold H Hinv
    ring
  rw [hsplit]
  have hdd : ∑ k : Fin (b + 1), delta (K := K) i k * delta k j = delta i j := by
    rw [Finset.sum_eq_single i]
    · unfold delta
      simp
    · intro k _ hki
      unfold delta
      have hne : i ≠ k := Ne.symm hki
      simp [hne]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hd1 : ∑ k : Fin (b + 1), delta (K := K) i k = 1 := sum_delta_eq_one i
  have hd2 : ∑ k : Fin (b + 1), delta (K := K) k j = 1 := by
    have hcomm :
        (∑ k : Fin (b + 1), delta (K := K) k j) = ∑ k : Fin (b + 1), delta (K := K) j k :=
      Finset.sum_congr rfl (fun k _ => delta_comm k j)
    rw [hcomm]
    exact sum_delta_eq_one j
  rw [hdd, hd1, hd2]
  have hinv : ((b + 2 : ℕ) : K)⁻¹ * (1 + ((b + 1 : ℕ) : K)) = 1 := by
    have hsum : (1 : K) + ((b + 1 : ℕ) : K) = ((b + 2 : ℕ) : K) := by
      push_cast
      ring
    rw [hsum, inv_mul_cancel₀ hq]
  linear_combination -hinv

lemma Hinv_comm {K : Type} [Field K] {b : ℕ} (i j : Fin (b + 1)) :
    Hinv (K := K) i j = Hinv j i := by
  unfold Hinv
  rw [delta_comm]

lemma H_mul_H_of_char {K : Type} [Field K] {b : ℕ} (hq : ((b + 2 : ℕ) : K) = 0)
    (i j : Fin b) :
    ∑ k : Fin b, H (K := K) i k * H (K := K) k j = delta i j := by
  have hsplit :
      ∑ k : Fin b, H (K := K) i k * H (K := K) k j =
        (∑ k : Fin b, delta (K := K) i k * delta k j) +
        (∑ k : Fin b, delta (K := K) i k) +
        (∑ k : Fin b, delta (K := K) k j) +
        (b : K) := by
    have hconst : ∑ _k : Fin b, (1 : K) = (b : K) := by
      simp
    rw [← hconst, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold H
    ring
  rw [hsplit]
  have hdd : ∑ k : Fin b, delta (K := K) i k * delta k j = delta i j := by
    rw [Finset.sum_eq_single i]
    · unfold delta
      simp
    · intro k _ hki
      unfold delta
      have hne : i ≠ k := Ne.symm hki
      simp [hne]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hd1 : ∑ k : Fin b, delta (K := K) i k = 1 := sum_delta_eq_one i
  have hd2 : ∑ k : Fin b, delta (K := K) k j = 1 := by
    have hcomm : (∑ k : Fin b, delta (K := K) k j) = ∑ k : Fin b, delta (K := K) j k :=
      Finset.sum_congr rfl (fun k _ => delta_comm k j)
    rw [hcomm]
    exact sum_delta_eq_one j
  rw [hdd, hd1, hd2]
  have hq' : (b : K) + 2 = 0 := by
    push_cast at hq
    exact hq
  linear_combination hq'

lemma lower_bound_nondiv {K : Type} [Field K] (b d : ℕ)
    (hq : ((b + 2 : ℕ) : K) ≠ 0)
    (A B : Equiv.Perm (Fin (b + 2)) → Fin d → K)
    (hAB : ∀ p r,
      (((Finset.univ : Finset (Fin (b + 2))).filter (fun i => r (p i) = i)).card : K) =
        ∑ j : Fin d, A p j * B r j) :
    (b + 1) ^ 2 + 1 ≤ d := by
  have hdot : ∀ p r, dot (A p) (B r) = ∑ k : Fin (b + 2), delta (K := K) (r (p k)) k := by
    intro p r
    rw [← fixed_cast]
    exact (hAB p r).symm
  let uD : Fin (b + 1) → Fin (b + 1) → Fin d → K := fun i j => A (p1 i j) - A (p2 i j)
  let vD : Fin (b + 1) → Fin (b + 1) → Fin d → K := fun a c => B (p1 c a) - B (p2 c a)
  have hDD : ∀ i j a c, dot (uD i j) (vD a c) = H i a * H j c := by
    intro i j a c
    simp only [uD, vD, dot_sub_left, dot_sub_right, hdot]
    exact fixed_diff_both i j a c
  have hD1 : ∀ i j, dot (uD i j) (B 1) = H i j := by
    intro i j
    simp only [uD, dot_sub_left, hdot]
    exact fixed_diff_one i j
  have h1D : ∀ a c, dot (A 1) (vD a c) = H a c := by
    intro a c
    simp only [vD, dot_sub_right, hdot]
    exact fixed_one_diff a c
  have h11 : dot (A 1) (B 1) = ((b + 2 : ℕ) : K) := by
    rw [hdot]
    exact fixed_one_one
  let ι := (Fin (b + 1) × Fin (b + 1)) ⊕ Unit
  let U : ι → Fin d → K := fun x =>
    match x with
    | Sum.inl (i, j) => uD i j
    | Sum.inr () => A 1 - ∑ x : Fin (b + 1), ∑ y : Fin (b + 1), Hinv (K := K) x y • uD x y
  let V : ι → Fin d → K := fun x =>
    match x with
    | Sum.inl (a, c) =>
        ∑ x : Fin (b + 1), ∑ y : Fin (b + 1), (Hinv (K := K) a x * Hinv (K := K) c y) • vD x y
    | Sum.inr () => B 1 - ∑ x : Fin (b + 1), ∑ y : Fin (b + 1), Hinv (K := K) x y • vD x y
  have hsum_Hinv_D : ∀ i j,
      ∑ x : Fin (b + 1), ∑ y : Fin (b + 1), Hinv (K := K) x y * (H i x * H j y) = H i j := by
    intro i j
    have h1 :
        ∑ x : Fin (b + 1), ∑ y : Fin (b + 1), Hinv (K := K) x y * (H i x * H j y) =
          ∑ x : Fin (b + 1), H (K := K) i x * (∑ y : Fin (b + 1), H j y * Hinv y x) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Hinv_comm x y]
      ring
    rw [h1]
    have h2 :
        ∑ x : Fin (b + 1), H (K := K) i x * (∑ y : Fin (b + 1), H j y * Hinv y x) =
          ∑ x : Fin (b + 1), H (K := K) i x * delta j x := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [H_mul_Hinv hq]
    rw [h2, Finset.sum_eq_single j]
    · unfold delta
      simp
    · intro x _ hxj
      unfold delta
      have hne : j ≠ x := Ne.symm hxj
      simp [hne]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hUV : ∀ α β : ι, dot (U α) (V β) = delta α β := by
    intro α β
    cases α with
    | inl ij =>
      rcases ij with ⟨i, j⟩
      cases β with
      | inl ac =>
        rcases ac with ⟨a, c⟩
        simp only [U, V, dot_sum_right, dot_smul_right, hDD]
        have hfac :
            ∑ x : Fin (b + 1), ∑ y : Fin (b + 1),
                Hinv (K := K) a x * Hinv c y * (H i x * H j y) =
              (∑ x : Fin (b + 1), H (K := K) i x * Hinv x a) *
                (∑ y : Fin (b + 1), H (K := K) j y * Hinv y c) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [Hinv_comm a x, Hinv_comm c y]
          ring
        rw [hfac, H_mul_Hinv hq, H_mul_Hinv hq]
        unfold delta
        dsimp only [ι]
        by_cases hia : i = a <;> by_cases hjc : j = c <;> simp [hia, hjc]
      | inr u =>
        cases u
        simp only [U, V, dot_sub_right, dot_sum_right, dot_smul_right, hD1, hDD]
        rw [hsum_Hinv_D i j, sub_self]
        unfold delta
        simp
    | inr u =>
      cases u
      cases β with
      | inl ac =>
        rcases ac with ⟨a, c⟩
        have hzero : ∀ x y, dot (U (Sum.inr ())) (vD x y) = 0 := by
          intro x y
          simp only [U, dot_sub_left, dot_sum_left, dot_smul_left, h1D, hDD]
          have hcomm :
              ∑ s : Fin (b + 1), ∑ t : Fin (b + 1), Hinv (K := K) s t * (H s x * H t y) =
                ∑ s : Fin (b + 1), ∑ t : Fin (b + 1), Hinv (K := K) s t * (H x s * H y t) := by
            refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => ?_))
            rw [H_comm s x, H_comm t y]
          rw [hcomm, hsum_Hinv_D x y, sub_self]
        simp only [V, dot_sum_right, dot_smul_right, hzero, mul_zero, Finset.sum_const_zero]
        unfold delta
        simp
      | inr v =>
        cases v
        have hzero : ∀ x y, dot (U (Sum.inr ())) (vD x y) = 0 := by
          intro x y
          simp only [U, dot_sub_left, dot_sum_left, dot_smul_left, h1D, hDD]
          have hcomm :
              ∑ s : Fin (b + 1), ∑ t : Fin (b + 1), Hinv (K := K) s t * (H s x * H t y) =
                ∑ s : Fin (b + 1), ∑ t : Fin (b + 1), Hinv (K := K) s t * (H x s * H y t) := by
            refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => ?_))
            rw [H_comm s x, H_comm t y]
          rw [hcomm, hsum_Hinv_D x y, sub_self]
        simp only [V, dot_sub_right, dot_sum_right, dot_smul_right, hzero, mul_zero,
          Finset.sum_const_zero, sub_zero]
        simp only [U, dot_sub_left, dot_sum_left, dot_smul_left, h11, hD1]
        have htr :
            ∑ x : Fin (b + 1), ∑ y : Fin (b + 1), Hinv (K := K) x y * H x y = ((b + 1 : ℕ) : K) := by
          have h1 :
              ∑ x : Fin (b + 1), ∑ y : Fin (b + 1), Hinv (K := K) x y * H x y =
                ∑ x : Fin (b + 1), ∑ y : Fin (b + 1), H (K := K) x y * Hinv y x := by
            refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
            rw [Hinv_comm x y, mul_comm]
          rw [h1]
          have h2 :
              ∑ x : Fin (b + 1), ∑ y : Fin (b + 1), H (K := K) x y * Hinv y x =
                ∑ x : Fin (b + 1), delta (K := K) x x := by
            refine Finset.sum_congr rfl (fun x _ => H_mul_Hinv hq x x)
          rw [h2]
          simp [delta]
        rw [htr]
        unfold delta
        simp only [↓reduceIte]
        push_cast
        ring
  have hcard := card_le_of_biorthogonal U V hUV
  simpa [ι, sq] using hcard

lemma lower_bound_div_char2 {K : Type} [Field K] (b d : ℕ)
    (hq : ((b + 2 : ℕ) : K) = 0)
    (A B : Equiv.Perm (Fin (b + 2)) → Fin d → K)
    (hAB : ∀ p r,
      (((Finset.univ : Finset (Fin (b + 2))).filter (fun i => r (p i) = i)).card : K) =
        ∑ j : Fin d, A p j * B r j) :
    b ^ 2 ≤ d := by
  have hdot : ∀ p r, dot (A p) (B r) = ∑ k : Fin (b + 2), delta (K := K) (r (p k)) k := by
    intro p r
    rw [← fixed_cast]
    exact (hAB p r).symm
  let uD : Fin b → Fin b → Fin d → K := fun i j => A (p1 i.castSucc j.castSucc) - A (p2 i.castSucc j.castSucc)
  let vD : Fin b → Fin b → Fin d → K := fun a c => B (p1 c.castSucc a.castSucc) - B (p2 c.castSucc a.castSucc)
  have hH_cast : ∀ (i j : Fin b), H (K := K) i.castSucc j.castSucc = H i j := by
    intro i j
    unfold H delta
    simp [Fin.castSucc_inj]
  have hDD : ∀ i j a c, dot (uD i j) (vD a c) = H i a * H j c := by
    intro i j a c
    simp only [uD, vD, dot_sub_left, dot_sub_right, hdot]
    rw [fixed_diff_both i.castSucc j.castSucc a.castSucc c.castSucc, hH_cast, hH_cast]
  let ι := Fin b × Fin b
  let U : ι → Fin d → K := fun x => uD x.1 x.2
  let V : ι → Fin d → K := fun x =>
    ∑ s : Fin b, ∑ t : Fin b, (H (K := K) x.1 s * H (K := K) x.2 t) • vD s t
  have hUV : ∀ α β : ι, dot (U α) (V β) = delta α β := by
    intro α β
    rcases α with ⟨i, j⟩
    rcases β with ⟨a, c⟩
    simp only [U, V, dot_sum_right, dot_smul_right, hDD]
    have hfac :
        ∑ s : Fin b, ∑ t : Fin b, H (K := K) a s * H c t * (H i s * H j t) =
          (∑ s : Fin b, H (K := K) i s * H s a) * (∑ t : Fin b, H (K := K) j t * H t c) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [H_comm a s, H_comm c t]
      ring
    rw [hfac, H_mul_H_of_char hq, H_mul_H_of_char hq]
    unfold delta
    dsimp only [ι]
    by_cases hia : i = a <;> by_cases hjc : j = c <;> simp [hia, hjc]
  have hcard := card_le_of_biorthogonal U V hUV
  simpa [ι, sq] using hcard

lemma lower_bound_div_ne2 {K : Type} [Field K] (b d : ℕ)
    (hq : ((b + 2 : ℕ) : K) = 0) (h2 : (2 : K) ≠ 0)
    (A B : Equiv.Perm (Fin (b + 2)) → Fin d → K)
    (hAB : ∀ p r,
      (((Finset.univ : Finset (Fin (b + 2))).filter (fun i => r (p i) = i)).card : K) =
        ∑ j : Fin d, A p j * B r j) :
    b ^ 2 + 1 ≤ d := by
  have hdot : ∀ p r, dot (A p) (B r) = ∑ k : Fin (b + 2), delta (K := K) (r (p k)) k := by
    intro p r
    rw [← fixed_cast]
    exact (hAB p r).symm
  let uD : Fin b → Fin b → Fin d → K := fun i j => A (p1 i.castSucc j.castSucc) - A (p2 i.castSucc j.castSucc)
  let vD : Fin b → Fin b → Fin d → K := fun a c => B (p1 c.castSucc a.castSucc) - B (p2 c.castSucc a.castSucc)
  have hH_cast : ∀ (i j : Fin b), H (K := K) i.castSucc j.castSucc = H i j := by
    intro i j
    unfold H delta
    simp [Fin.castSucc_inj]
  have hDD : ∀ i j a c, dot (uD i j) (vD a c) = H i a * H j c := by
    intro i j a c
    simp only [uD, vD, dot_sub_left, dot_sub_right, hdot]
    rw [fixed_diff_both i.castSucc j.castSucc a.castSucc c.castSucc, hH_cast, hH_cast]
  have hD1 : ∀ i j, dot (uD i j) (B 1) = H i j := by
    intro i j
    simp only [uD, dot_sub_left, hdot]
    rw [fixed_diff_one i.castSucc j.castSucc, hH_cast]
  have h1D : ∀ a c, dot (A 1) (vD a c) = H a c := by
    intro a c
    simp only [vD, dot_sub_right, hdot]
    rw [fixed_one_diff a.castSucc c.castSucc, hH_cast]
  have h11 : dot (A 1) (B 1) = ((b + 2 : ℕ) : K) := by
    rw [hdot]
    exact fixed_one_one
  have hsum_H_D : ∀ i j,
      ∑ x : Fin b, ∑ y : Fin b, H (K := K) x y * (H i x * H j y) = H i j := by
    intro i j
    have h1 :
        ∑ x : Fin b, ∑ y : Fin b, H (K := K) x y * (H i x * H j y) =
          ∑ x : Fin b, H (K := K) i x * (∑ y : Fin b, H j y * H y x) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [H_comm x y]
      ring
    rw [h1]
    have h2' :
        ∑ x : Fin b, H (K := K) i x * (∑ y : Fin b, H j y * H y x) =
          ∑ x : Fin b, H (K := K) i x * delta j x := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [H_mul_H_of_char hq]
    rw [h2', Finset.sum_eq_single j]
    · unfold delta
      simp
    · intro x _ hxj
      unfold delta
      have hne : j ≠ x := Ne.symm hxj
      simp [hne]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  let ι := (Fin b × Fin b) ⊕ Unit
  let U : ι → Fin d → K := fun x =>
    match x with
    | Sum.inl (i, j) => uD i j
    | Sum.inr () => A 1 - ∑ x : Fin b, ∑ y : Fin b, H (K := K) x y • uD x y
  let V : ι → Fin d → K := fun x =>
    match x with
    | Sum.inl (a, c) =>
        ∑ x : Fin b, ∑ y : Fin b, (H (K := K) a x * H (K := K) c y) • vD x y
    | Sum.inr () => (2 : K)⁻¹ • (B 1 - ∑ x : Fin b, ∑ y : Fin b, H (K := K) x y • vD x y)
  have hUV : ∀ α β : ι, dot (U α) (V β) = delta α β := by
    intro α β
    cases α with
    | inl ij =>
      rcases ij with ⟨i, j⟩
      cases β with
      | inl ac =>
        rcases ac with ⟨a, c⟩
        simp only [U, V, dot_sum_right, dot_smul_right, hDD]
        have hfac :
            ∑ x : Fin b, ∑ y : Fin b, H (K := K) a x * H c y * (H i x * H j y) =
              (∑ x : Fin b, H (K := K) i x * H x a) * (∑ y : Fin b, H (K := K) j y * H y c) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [H_comm a x, H_comm c y]
          ring
        rw [hfac, H_mul_H_of_char hq, H_mul_H_of_char hq]
        unfold delta
        dsimp only [ι]
        by_cases hia : i = a <;> by_cases hjc : j = c <;> simp [hia, hjc]
      | inr u =>
        cases u
        simp only [U, V, dot_smul_right, dot_sub_right, dot_sum_right, hD1, hDD]
        rw [hsum_H_D i j, sub_self, mul_zero]
        unfold delta
        simp
    | inr u =>
      cases u
      have hzero : ∀ x y, dot (U (Sum.inr ())) (vD x y) = 0 := by
        intro x y
        simp only [U, dot_sub_left, dot_sum_left, dot_smul_left, h1D, hDD]
        have hcomm :
            ∑ s : Fin b, ∑ t : Fin b, H (K := K) s t * (H s x * H t y) =
              ∑ s : Fin b, ∑ t : Fin b, H (K := K) s t * (H x s * H y t) := by
          refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => ?_))
          rw [H_comm s x, H_comm t y]
        rw [hcomm, hsum_H_D x y, sub_self]
      cases β with
      | inl ac =>
        rcases ac with ⟨a, c⟩
        simp only [V, dot_sum_right, dot_smul_right, hzero, mul_zero, Finset.sum_const_zero]
        unfold delta
        simp
      | inr v =>
        cases v
        simp only [V, dot_smul_right, dot_sub_right, dot_sum_right, hzero, mul_zero,
          Finset.sum_const_zero, sub_zero]
        simp only [U, dot_sub_left, dot_sum_left, dot_smul_left, h11, hD1]
        have htr :
            ∑ x : Fin b, ∑ y : Fin b, H (K := K) x y * H x y = (b : K) := by
          have h1 :
              ∑ x : Fin b, ∑ y : Fin b, H (K := K) x y * H x y =
                ∑ x : Fin b, ∑ y : Fin b, H (K := K) x y * H y x := by
            refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
            rw [H_comm x y]
          rw [h1]
          have h2' :
              ∑ x : Fin b, ∑ y : Fin b, H (K := K) x y * H y x =
                ∑ x : Fin b, delta (K := K) x x := by
            refine Finset.sum_congr rfl (fun x _ => H_mul_H_of_char hq x x)
          rw [h2']
          simp [delta]
        rw [htr]
        unfold delta
        simp only [↓reduceIte]
        have hdiff : ((b + 2 : ℕ) : K) - (b : K) = 2 := by
          push_cast
          ring
        rw [hdiff, inv_mul_cancel₀ h2]
  have hcard := card_le_of_biorthogonal U V hUV
  simpa [ι, sq] using hcard

end PEqualNP.Outside.L_lib_592_aux.RankData

namespace PEqualNP.Outside.L_lib_592_aux

theorem priceSource : (∀ (K : Type) [Field K] (b d : ℕ),
  let q := b + 2
  let P := Equiv.Perm (Fin q)
  let fixed := fun (p r : P) =>
    ((Finset.univ : Finset (Fin q)).filter (fun i => r (p i) = i)).card
  let threshold := if ringChar K ∣ q then
      (q - 2) ^ 2 + (if ringChar K = 2 then 0 else 1)
    else (q - 1) ^ 2 + 1
  (∃ (A B : P → Fin d → K),
    ∀ p r, (fixed p r : K) = ∑ j : Fin d, A p j * B r j) ↔
    threshold ≤ d) := by
  intro K _ b d
  dsimp only
  by_cases hdiv : ringChar K ∣ b + 2
  · have hq : ((b + 2 : ℕ) : K) = 0 := (PEqualNP.Outside.L_lib_592_aux.RankData.ringChar_dvd_iff (b + 2)).mp hdiv
    by_cases h2 : ringChar K = 2
    · have h2K : (2 : K) = 0 := (PEqualNP.Outside.L_lib_592_aux.RankData.ringChar_eq_two_iff).mp h2
      simp only [hdiv, ↓reduceIte]
      simp only [h2, ↓reduceIte, Nat.add_sub_cancel, add_zero]
      constructor
      · rintro ⟨A, B, hAB⟩
        exact PEqualNP.Outside.L_lib_592_aux.RankData.lower_bound_div_char2 b d hq A B hAB
      · intro hd
        exact PEqualNP.Outside.L_lib_592_aux.RankData.upper_bound_div_char2 b d hq h2K hd
    · have h2K : (2 : K) ≠ 0 := by
        intro hc
        exact h2 ((PEqualNP.Outside.L_lib_592_aux.RankData.ringChar_eq_two_iff).mpr hc)
      simp only [hdiv, ↓reduceIte]
      simp only [h2, ↓reduceIte, Nat.add_sub_cancel]
      constructor
      · rintro ⟨A, B, hAB⟩
        exact PEqualNP.Outside.L_lib_592_aux.RankData.lower_bound_div_ne2 b d hq h2K A B hAB
      · intro hd
        exact PEqualNP.Outside.L_lib_592_aux.RankData.upper_bound_div_ne2 b d hq hd
  · have hq : ((b + 2 : ℕ) : K) ≠ 0 := by
      intro hc
      exact hdiv ((PEqualNP.Outside.L_lib_592_aux.RankData.ringChar_dvd_iff (b + 2)).mpr hc)
    simp only [hdiv, ↓reduceIte]
    have hsub : b + 2 - 1 = b + 1 := by omega
    rw [hsub]
    constructor
    · rintro ⟨A, B, hAB⟩
      exact PEqualNP.Outside.L_lib_592_aux.RankData.lower_bound_nondiv b d hq A B hAB
    · intro hd
      exact PEqualNP.Outside.L_lib_592_aux.RankData.upper_bound_nondiv b d hd

end PEqualNP.Outside.L_lib_592_aux
namespace PEqualNP.Outside.L_lib_592_aux
abbrev State (b : ℕ) := Fin (b+1) → Bool
abbrev Control (b : ℕ) := (Fin b → Bool) → Bool

def row {b : ℕ} (c : Control b) : Equiv.Perm (State b) where
  toFun s := Fin.snoc (α := fun _ : Fin (b+1) => Bool) (fun j => s j.succ)
    (xor (s 0) (c (fun j => s j.succ)))
  invFun t := Fin.cons (xor (t (Fin.last b)) (c (fun j => t j.castSucc))) (fun j => t j.castSucc)
  left_inv s := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  right_inv t := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp

def combine {G : Type*} [Group G] : List G → G
  | [] => 1
  | a::rest => combine rest * a

theorem combine_append {G : Type*} [Group G] (l r : List G) :
    combine (l++r)=combine r*combine l := by
  induction l with
  | nil => simp [combine]
  | cons a l ih => simp [combine,ih,mul_assoc]

theorem combine_eval {X I : Type*} (L : List I) (f : I → Equiv.Perm X) (x : X) :
    (combine (L.map f)) x = L.foldl (fun y i => f i y) x := by
  induction L generalizing x with
  | nil => rfl
  | cons i L ih => exact ih (f i x)

def word {b n : ℕ} (c : Fin n → Control b) : Equiv.Perm (State b) := combine (List.ofFn (fun i => row (c i)))

def fixCount {X : Type*} [Fintype X] [DecidableEq X] (p : Equiv.Perm X) :=
  (Finset.univ.filter (fun x => p x=x)).card

def graphMat {X : Type*} [Fintype X] [DecidableEq X] (p : Equiv.Perm X) : Matrix X X ℕ :=
  fun x y => if p x=y then 1 else 0

theorem graphMat_prod {X : Type*} [Fintype X] [DecidableEq X] (L : List (Equiv.Perm X)) :
    (L.map graphMat).prod = graphMat (combine L) := by
  induction L with
  | nil =>
    ext i j
    by_cases h : i=j <;> simp [graphMat,combine,Matrix.one_apply,h]
  | cons p L ih =>
    rw [List.map_cons,List.prod_cons,ih]
    ext i j
    rw [Matrix.mul_apply,Finset.sum_eq_single (p i)]
    · by_cases h : (combine L) (p i) = j <;> simp [graphMat,combine,h]
    · intro k _ hk
      simp [graphMat,Ne.symm hk]
    · simp

theorem trace_graph {X : Type*} [Fintype X] [DecidableEq X] (p : Equiv.Perm X) :
    Matrix.trace (graphMat p) = fixCount p := by
  change (∑ x, if p x=x then (1:ℕ) else 0) = (Finset.univ.filter (fun x => p x=x)).card
  rw [Finset.card_filter] <;> rfl

open PEqualNP.Outside.L_lib_377 in
theorem nx_eq {b : ℕ} (s : State b) (v : Bool) :
    nx s v = Fin.snoc (α := fun _ : Fin (b+1) => Bool) (fun j => s j.succ) v := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [nx]
  · have h : j.val+1<b+1 := by omega
    simp [nx,h]
    exact congrArg s (Fin.ext rfl)

def countWords (b a : ℕ) (C : Fin (a+1) → Control b) : ℕ :=
  ((Finset.univ : Finset (Fin (a+1) → Bool)).filter (fun x =>
    ∀ i : Fin (a+1), x (Fin.ofNat (a+1) (i.val+(b+1))) =
      xor (x i) (C i (fun j => x (Fin.ofNat (a+1) (i.val+1+j.val)))))).card

open PEqualNP.Outside.L_lib_377 in
theorem count_fix (b a : ℕ) (C : Fin (a+1) → Control b) :
    countWords b a C = fixCount (word C) := by
  let test := fun (i : Fin (a+1)) (s : State b) (t : Bool) =>
    decide (t = xor (s 0) (C i (fun j => s j.succ)))
  have eq := PEqualNP.Outside.L_lib_377 a (b+1) test
  change Matrix.trace (List.ofFn (Mat test)).prod = _ at eq
  have cell (i : Fin (a+1)) : Mat test i = graphMat (row (C i)) := by
    ext s t
    let v := xor (s 0) (C i (fun j => s j.succ))
    have nxv : nx s v = row (C i) s := nx_eq s v
    change (Finset.univ.filter (fun x : Bool => decide (x=v)=true ∧ nx s x=t)).card = _
    by_cases h : row (C i) s = t
    · have he : Finset.univ.filter (fun x : Bool => decide (x=v)=true ∧ nx s x=t) = {v} := by
        ext x
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq,Finset.mem_singleton]
        exact ⟨And.left,fun hv => ⟨hv,hv ▸ nxv.trans h⟩⟩
      rw [he]; simp [graphMat,h]
    · have he : Finset.univ.filter (fun x : Bool => decide (x=v)=true ∧ nx s x=t) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        obtain ⟨_,hx,he⟩ := Finset.mem_filter.mp hx
        have hv : x=v := of_decide_eq_true hx
        subst x
        exact h (nxv.symm.trans he)
      rw [he]; simp [graphMat,h]
  have hm : List.ofFn (Mat test) = (List.ofFn fun i => row (C i)).map graphMat := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext cell)
  rw [hm,graphMat_prod,trace_graph] at eq
  refine Eq.trans ?_ eq.symm
  unfold countWords
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,test,decide_eq_true_eq]
  apply forall_congr'
  intro i
  simp [ofNat_val,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

section Linear
variable {K G : Type} [Field K] [Group G] {m : ℕ}

def Fact (f : G → K) (m : ℕ) := ∃ A B : G → Fin m → K,
  ∀ p r, f (r*p) = ∑ i, A p i * B r i

theorem makeScan (f : G → K) (h : Fact f m) :
    ∃ (s : Fin m → K) (T : G → (Fin m → K) →ₗ[K] (Fin m → K))
      (o : (Fin m → K) →ₗ[K] K), ∀ L : List G, o (L.foldl (fun v g => T g v) s) = f (combine L) := by
  classical
  obtain ⟨A,B,fac⟩ := h
  let E : (Fin m → K) →ₗ[K] (G → K) :=
    { toFun := fun v r => ∑ i, v i * B r i
      map_add' := by intro x y; funext r; simp [add_mul,Finset.sum_add_distrib]
      map_smul' := by intro a x; funext r; simp [Finset.mul_sum,mul_assoc] }
  have value (p r : G) : E (A p) r = f (r*p) := (fac p r).symm
  obtain ⟨g,hg⟩ := E.rangeRestrict.exists_rightInverse_of_surjective E.range_rangeRestrict
  obtain ⟨π,hπ⟩ := E.range.subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  let J := g.comp π
  have back (v : Fin m → K) : E (J (E v)) = E v := by
    let z := E.rangeRestrict v
    have p : π (E v) = z := LinearMap.congr_fun hπ z
    have q : E.rangeRestrict (g z) = z := LinearMap.congr_fun hg z
    change E (g (π (E v))) = E v
    rw [p]; exact congrArg Subtype.val q
  let shift (u : G) : (G→K) →ₗ[K] (G→K) :=
    { toFun := fun x r => x (r*u)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have sh (u p : G) : shift u (E (A p)) = E (A (u*p)) := by
    funext r
    change E (A p) (r*u) = _
    rw [value,value,mul_assoc]
  let T (u : G) := J.comp ((shift u).comp E)
  let o := (LinearMap.proj (R:=K) (φ:=fun _ : G => K) (1:G)).comp E
  have go (L : List G) (p : G) (v : Fin m → K) (hv : E v=E (A p)) :
      E (L.foldl (fun x u => T u x) v) = E (A (combine L*p)) := by
    induction L generalizing v p with
    | nil => simpa [combine] using hv
    | cons u L ih =>
      change E (L.foldl _ (T u v)) = _
      have eq : E (T u v)=E (A (u*p)) := by
        change E (J (shift u (E v)))=_
        rw [hv,sh,back]
      simpa [combine,mul_assoc] using ih (u*p) (T u v) eq
  refine ⟨A 1,T,o,?_⟩
  intro L
  change E (L.foldl _ (A 1)) 1 = _
  have eq := congrFun (go L 1 (A 1) rfl) 1
  simpa [value] using eq

def linWord (l : List ((Fin m → K) →ₗ[K] (Fin m → K))) : (Fin m → K) →ₗ[K] (Fin m → K) :=
  l.foldr (fun a b => b.comp a) .id

theorem linWord_eval (l : List ((Fin m → K) →ₗ[K] (Fin m → K))) (v : Fin m→K) :
    linWord l v = l.foldl (fun x t => t x) v := by
  induction l generalizing v with
  | nil => rfl
  | cons t l ih => exact ih (t v)

theorem dotLinear (l : (Fin m → K) →ₗ[K] K) (v : Fin m → K) :
    l v = ∑ i, v i * l (Pi.single i 1) := by
  have hv : ∑ i : Fin m, v i • Pi.single i (1:K) = v := by
    funext j
    simp [Finset.sum_apply,Pi.single_apply,smul_eq_mul,mul_ite]
  calc
    l v = l (∑ i, v i • Pi.single i (1:K)) := congrArg l hv.symm
    _ = _ := by simp [smul_eq_mul]

end Linear
noncomputable def move {X Y : Type} (e : X ≃ Y) (p : Equiv.Perm X) : Equiv.Perm Y :=
  e.symm.trans (p.trans e)

theorem move_mul {X Y : Type} (e : X ≃ Y) (r p : Equiv.Perm X) :
    move e (r*p)=move e r*move e p := by
  ext y; simp [move]

theorem move_fix {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (e : X ≃ Y) (p : Equiv.Perm X) : fixCount (move e p)=fixCount p := by
  unfold fixCount
  rw [Finset.card_filter,Finset.card_filter]
  rw [← e.sum_comp (fun y => if move e p y = y then (1:ℕ) else 0)]
  simp [move]

theorem fact_transport {X Y K : Type} [Field K] [Fintype X] [Fintype Y] [DecidableEq X]
    [DecidableEq Y] (e : X ≃ Y) (m : ℕ)
    (h : Fact (fun p : Equiv.Perm Y => (fixCount p : K)) m) :
    Fact (fun p : Equiv.Perm X => (fixCount p : K)) m := by
  obtain ⟨A,B,hh⟩ := h
  refine ⟨fun p => A (move e p),fun r => B (move e r),?_⟩
  intro p r
  have q := hh (move e p) (move e r)
  change (fixCount (move e r * move e p) : K) = _ at q
  rwa [←move_mul,move_fix] at q

noncomputable def threshold (K : Type) [Field K] (b : ℕ) :=
  if ringChar K = 2 then (2^(b+1)-2)^2 else (2^(b+1)-1)^2+1

theorem price (K : Type) [Field K] (b m : ℕ) :
    Fact (fun p : Equiv.Perm (State b) => (fixCount p : K)) m ↔ threshold K b ≤ m := by
  classical
  let D := 2^(b+1)
  let u := D-2
  have uD : u+2=D := by
    have pos : 0<2^b := by positivity
    dsimp [u,D]; rw [pow_succ]; omega
  let e : State b ≃ Fin (u+2) := Fintype.equivFinOfCardEq (by simp [State,uD,D])
  have spec := priceSource K u m
  change Fact (fun p : Equiv.Perm (Fin (u+2)) => (fixCount p : K)) m ↔
    (if ringChar K ∣ u+2 then (u+2-2)^2+(if ringChar K=2 then 0 else 1)
      else (u+2-1)^2+1) ≤ m at spec
  have div : ringChar K ∣ u+2 ↔ ringChar K=2 := by
    rw [RankData.ringChar_dvd_iff,RankData.ringChar_eq_two_iff,uD]
    dsimp [D]
    push_cast
    constructor
    · intro h
      by_contra hn
      exact pow_ne_zero _ hn h
    · intro h
      simp [h]
  have heq : (if ringChar K ∣ u+2 then (u+2-2)^2+(if ringChar K=2 then 0 else 1)
      else (u+2-1)^2+1) = threshold K b := by
    by_cases hc : ringChar K=2
    · simp only [if_pos (div.mpr hc),if_pos hc,add_zero,threshold,uD,D]
      simp [hc]
    · rw [if_neg (fun h => hc (div.mp h)),threshold,if_neg hc,uD]
  rw [heq] at spec
  exact ⟨fun h => spec.mp (fact_transport e.symm _ h),fun h => fact_transport e _ (spec.mpr h)⟩
def Admits (K : Type) [Field K] (b n m : ℕ) :=
  ∃ (s : Fin m → K) (step : Fin n → Control b → (Fin m → K) →ₗ[K] (Fin m → K))
    (out : (Fin m → K) →ₗ[K] K), ∀ C : Fin n → Control b,
      out ((List.finRange n).foldl (fun v i => step i (C i) v) s) = (fixCount (word C) : K)

theorem upper (K : Type) [Field K] (b n m : ℕ) (h : threshold K b ≤ m) : Admits K b n m := by
  obtain ⟨s,T,o,ok⟩ := makeScan _ ((price K b m).mpr h)
  refine ⟨s,fun _ c => T (row c),o,?_⟩
  intro C
  have test := ok (List.ofFn fun i => row (C i))
  simpa only [List.ofFn_eq_map,List.foldl_map,word] using test

def glue {X : Type*} {u v : ℕ} (l : Fin u → X) (r : Fin v → X) : Fin (u+v) → X :=
  Fin.addCases (motive := fun _ => X) l r

theorem glue_l {X : Type*} {u v : ℕ} (l : Fin u → X) (r : Fin v → X) (i : Fin u) :
    glue l r (Fin.castLE (Nat.le_add_right u v) i) = l i := Fin.addCases_left i

theorem glue_r {X : Type*} {u v : ℕ} (l : Fin u → X) (r : Fin v → X) (i : Fin v) :
    glue l r (Fin.natAdd u i) = r i := Fin.addCases_right i

theorem word_glue {b u v : ℕ} (l : Fin u → Control b) (r : Fin v → Control b) :
    word (glue l r)=word r*word l := by
  unfold word
  rw [List.ofFn_add,combine_append]
  simp only [glue_l,glue_r]

theorem routed (b : ℕ) (p : Equiv.Perm (State b)) :
    ∃ C : Fin (4*(b+1)) → Control b, word C=p := by
  obtain ⟨C,hC⟩ := routeSource b p
  refine ⟨C,Equiv.ext fun x => ?_⟩
  unfold word
  rw [List.ofFn_eq_map,combine_eval]
  exact hC x

theorem routed_extra (b t : ℕ) (p : Equiv.Perm (State b)) :
    ∃ C : Fin (4*(b+1)+t) → Control b, word C=p := by
  let blank : Fin t → Control b := fun _ _ => false
  obtain ⟨c,h⟩ := routed b ((word blank)⁻¹*p)
  exact ⟨glue c blank,by rw [word_glue,h,mul_inv_cancel_left]⟩

theorem split_scan (K : Type) [Field K] (b u v m : ℕ)
    (pre : ∀ p : Equiv.Perm (State b), ∃ L : Fin u → Control b, word L=p)
    (suf : ∀ r : Equiv.Perm (State b), ∃ L : Fin v → Control b, word L=r)
    (h : Admits K b (u+v) m) : Fact (fun p : Equiv.Perm (State b) => (fixCount p : K)) m := by
  classical
  obtain ⟨s,step,out,works⟩ := h
  choose P hp using pre
  choose R hr using suf
  let first (p : Equiv.Perm (State b)) := List.ofFn (fun i : Fin u => step (Fin.castAdd v i) (P p i))
  let last (r : Equiv.Perm (State b)) := List.ofFn (fun j : Fin v => step (Fin.natAdd u j) (R r j))
  let A (p : Equiv.Perm (State b)) := linWord (first p) s
  let B (r : Equiv.Perm (State b)) := out.comp (linWord (last r))
  refine ⟨A,fun r j => B r (Pi.single j 1),?_⟩
  intro p r
  have hh := works (glue (P p) (R r))
  rw [word_glue,hp,hr] at hh
  have sub : List.ofFn (fun i => step i (glue (P p) (R r) i)) = first p ++ last r := by
    rw [List.ofFn_add]
    simp only [glue_l,glue_r,first,last] <;> rfl
  have fold : (List.finRange (u+v)).foldl (fun x i => step i (glue (P p) (R r) i) x) s =
      linWord (last r) (A p) := by
    have hv := congrArg (fun L : List ((Fin m→K) →ₗ[K] (Fin m→K)) =>
      L.foldl (fun x f => f x) s) sub
    simpa only [List.ofFn_eq_map,List.foldl_map,List.foldl_append,linWord_eval,A] using hv
  rw [fold] at hh
  exact hh.symm.trans (dotLinear (B r) (A p))

theorem lower (K : Type) [Field K] (b n m : ℕ) (len : 8*(b+1) ≤ n) (h : Admits K b n m) :
    threshold K b ≤ m := by
  obtain ⟨t,ht⟩ := Nat.exists_eq_add_of_le len
  have hsum : n = 4*(b+1)+(4*(b+1)+t) := by omega
  rw [hsum] at h
  exact (price K b m).mp (split_scan K b _ _ m (routed b) (routed_extra b t) h)

def Physical (K : Type) [Field K] (b a m : ℕ) :=
  ∃ (s : Fin m → K) (step : Fin (a+1) → Control b → (Fin m → K) →ₗ[K] (Fin m → K))
    (out : (Fin m → K) →ₗ[K] K), ∀ C : Fin (a+1) → Control b,
      out ((List.finRange (a+1)).foldl (fun v i => step i (C i) v) s) = (countWords b a C : K)

theorem physical (K : Type) [Field K] (b a m : ℕ) :
    Physical K b a m ↔ Admits K b (a+1) m := by
  unfold Physical Admits
  simp only [count_fix]

end PEqualNP.Outside.L_lib_592_aux

open PEqualNP.Outside.L_lib_592_aux

theorem PEqualNP.Outside.L_lib_592 : (
∀ (K : Type) [Field K] (b : ℕ),
  let w := b + 1
  let D := 2 ^ w
  let threshold := if ringChar K = 2 then (D - 2) ^ 2 else (D - 1) ^ 2 + 1
  let Control := (Fin b → Bool) → Bool
  ∀ (a m : ℕ),
    let n := a + 1
    let count := fun (C : Fin n → Control) =>
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
        ∀ i : Fin n,
          x (Fin.ofNat (a + 1) (i.val + w)) =
            xor (x i) (C i (fun j => x (Fin.ofNat (a + 1) (i.val + 1 + j.val)))))).card
    let admits :=
      ∃ (s : Fin m → K)
        (step : Fin n → Control → (Fin m → K) →ₗ[K] (Fin m → K))
        (out : (Fin m → K) →ₗ[K] K),
        ∀ C : Fin n → Control,
          out ((List.finRange n).foldl (fun v i => step i (C i) v) s) = (count C : K)
    (threshold ≤ m → admits) ∧ (8 * w ≤ n → admits → threshold ≤ m)) := by
  intro K _ b
  dsimp only
  intro a m
  change (threshold K b ≤ m → Physical K b a m) ∧
    (8*(b+1) ≤ a+1 → Physical K b a m → threshold K b ≤ m)
  exact ⟨fun h => (physical K b a m).mpr (upper K b (a+1) m h),
    fun hn h => lower K b (a+1) m hn ((physical K b a m).mp h)⟩
