import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_973

open Matrix

lemma z2_one_of_ne {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert a h; decide

lemma z2_add_one_ne_iff (a : ZMod 2) : a + 1 ≠ 0 ↔ a = 0 := by
  revert a; decide

lemma z2_toNat_decide (a : ZMod 2) : (((decide (a = 1)).toNat : ℕ) : ZMod 2) = a := by
  revert a; decide

lemma z2_decide_ne (a b : ZMod 2) : (decide (a = 1) ≠ decide (b = 1)) ↔ a ≠ b := by
  revert a b; decide

lemma bool_self_zero (a b : Bool) :
    ((a.toNat : ℕ) : ZMod 2) + ((b.toNat : ℕ) : ZMod 2) + ((a.toNat : ℕ) : ZMod 2)
      + ((b.toNat : ℕ) : ZMod 2) = 0 := by
  revert a b; decide

lemma bool_anchor (a b c d e f : Bool)
    (h : ((a.toNat : ℕ) : ZMod 2) + ((b.toNat : ℕ) : ZMod 2) + ((e.toNat : ℕ) : ZMod 2)
      + ((f.toNat : ℕ) : ZMod 2) = ((c.toNat : ℕ) : ZMod 2) + ((d.toNat : ℕ) : ZMod 2)
      + ((e.toNat : ℕ) : ZMod 2) + ((f.toNat : ℕ) : ZMod 2)) :
    (a ≠ c ↔ b ≠ d) := by
  revert a b c d e f; decide

lemma half_card {k : ℕ} (y z : Fin k → ZMod 2) (hyz : y ≠ z) (c c' : ZMod 2) :
    2 * (Finset.univ.filter (fun a : Fin k → ZMod 2 =>
      ∑ j, y j * a j + c ≠ ∑ j, z j * a j + c')).card = 2 ^ k := by
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hyz
  let f : (Fin k → ZMod 2) → ZMod 2 := fun a => (∑ j, y j * a j + c) - (∑ j, z j * a j + c')
  have hpred : ∀ a : Fin k → ZMod 2,
      (∑ j, y j * a j + c ≠ ∑ j, z j * a j + c') ↔ f a ≠ 0 := by
    intro a; simp only [f, ne_eq, sub_eq_zero]
  have h1 : y j0 - z j0 = 1 := z2_one_of_ne (sub_ne_zero.mpr hj0)
  have hshift : ∀ a, f (a + Pi.single j0 1) = f a + 1 := by
    intro a
    simp only [f, Pi.add_apply, mul_add, Finset.sum_add_distrib, Pi.single_apply, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← h1]; ring
  have hδ : (Pi.single j0 (1 : ZMod 2) : Fin k → ZMod 2) + Pi.single j0 1 = 0 := by
    rw [← Pi.single_add, show (1 : ZMod 2) + 1 = 0 by decide]; exact Pi.single_zero j0
  have hS : (Finset.univ.filter (fun a => f a ≠ 0)).card
      = (Finset.univ.filter (fun a => ¬ f a ≠ 0)).card := by
    apply Finset.card_nbij' (fun a => a + Pi.single j0 1) (fun a => a + Pi.single j0 1)
    · intro a ha
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha ⊢
      rw [hshift, z2_add_one_ne_iff]; exact ha
    · intro a ha
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha ⊢
      rw [hshift, z2_add_one_ne_iff]; exact not_not.mp ha
    · intro a _; simp only [add_assoc, hδ, add_zero]
    · intro a _; simp only [add_assoc, hδ, add_zero]
  have htot := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k → ZMod 2))) (fun a => f a ≠ 0)
  have hcard : (Finset.univ : Finset (Fin k → ZMod 2)).card = 2 ^ k := by
    simp [ZMod.card]
  rw [Finset.filter_congr (fun a _ => hpred a)]
  omega

end PEqualNP.Outside.L_lib_973

open PEqualNP.Outside.L_lib_973 Matrix in
theorem PEqualNP.Outside.L_lib_973 : ∀ (n k b r : ℕ) (_ : 2 ≤ n) (_ : 2^(k-1) < n) (_ : n ≤ 2^k) (_ : n-k ≤ b),
  let m := 2^k * b
  (∃ (T : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m),
    (∀ i j : Fin n, i ≠ j →
      2 * (Finset.univ.filter (fun c : Fin m => T i c ≠ T j c)).card = m) ∧
    let E := fun i j => ((T i j).toNat : ZMod 2)
    let A : Matrix (Fin n) (Fin m) (ZMod 2) := fun i j => E i j + E i v + E u j + E u v
    Matrix.rank A = r) ↔ k ≤ r ∧ r < n := by
  intro n k b r h2n hk1 hk2 hb m
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk2; omega
    · exact h
  have hkn : k < n := by
    have := Nat.lt_two_pow_self (n := k - 1)
    omega
  have hb0 : 0 < b := by omega
  have hm : 0 < m := Nat.mul_pos (by positivity) hb0
  constructor
  · rintro ⟨T, u, v, hd, hr⟩
    set A : Matrix (Fin n) (Fin m) (ZMod 2) := fun i j => ((T i j).toNat : ZMod 2)
      + ((T i v).toNat : ZMod 2) + ((T u j).toNat : ZMod 2) + ((T u v).toNat : ZMod 2) with hA
    have hr' : A.rank = r := hr
    have hAu : A.row u = 0 := by
      funext j; exact bool_self_zero _ _
    -- r < n
    have hlt : r < n := by
      have hspan : Submodule.span (ZMod 2) (Set.range A.row) ≤
          Submodule.span (ZMod 2) (((Finset.univ.erase u).image A.row : Finset _) : Set _) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        by_cases hi : i = u
        · subst hi; rw [hAu]; exact Submodule.zero_mem _
        · exact Submodule.subset_span
            (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, by simp [hi], rfl⟩))
      have h1 := Submodule.finrank_mono hspan
      have h2 := finrank_span_finset_le_card (R := ZMod 2) ((Finset.univ.erase u).image A.row)
      have h3 := Finset.card_image_le (s := Finset.univ.erase u) (f := A.row)
      rw [Finset.card_erase_of_mem (Finset.mem_univ u), Finset.card_univ, Fintype.card_fin] at h3
      rw [← rank_eq_finrank_span_row, hr'] at h1
      have h4 : r ≤ n - 1 := le_trans h1 (le_trans h2 h3)
      omega
    have hinj : Function.Injective A.row := by
      intro i j hij
      by_contra hne
      have key : ∀ c, (T i c ≠ T j c ↔ T i v ≠ T j v) :=
        fun c => bool_anchor _ _ _ _ _ _ (congrFun hij c)
      have hdij := hd i j hne
      by_cases hv : T i v = T j v
      · have hE : (Finset.univ.filter (fun c : Fin m => T i c ≠ T j c)) = ∅ := by
          apply Finset.filter_false_of_mem
          intro c _; rw [key c]; exact not_not.mpr hv
        rw [hE, Finset.card_empty] at hdij
        omega
      · have hU : (Finset.univ.filter (fun c : Fin m => T i c ≠ T j c)) = Finset.univ := by
          apply Finset.filter_true_of_mem
          intro c _; rw [key c]; exact hv
        rw [hU, Finset.card_univ, Fintype.card_fin] at hdij
        omega
    have hcard : n ≤ 2 ^ r := by
      let W := Submodule.span (ZMod 2) (Set.range A.row)
      let _ : Fintype W := Fintype.ofFinite W
      have h1 : Fintype.card (Fin n) ≤ Fintype.card W :=
        Fintype.card_le_of_injective (fun i => ⟨A.row i, Submodule.subset_span ⟨i, rfl⟩⟩)
          (fun i j h => hinj (congrArg Subtype.val h))
      rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := W), ZMod.card,
        ← rank_eq_finrank_span_row, hr', Fintype.card_fin] at h1
      exact h1
    have h5 : 2 ^ (k - 1) < 2 ^ r := lt_of_lt_of_le hk1 hcard
    have h6 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h5
    exact ⟨by omega, hlt⟩
  · rintro ⟨hkr, hrn⟩
    have hV : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by simp [ZMod.card]
    let e : Fin m ≃ Fin b × (Fin k → ZMod 2) :=
      Fintype.equivOfCardEq (by simp only [Fintype.card_fin, Fintype.card_prod, hV, m]; ring)
    let x : Fin n → Fin k → ZMod 2 := fun i j => if i.val.testBit j.val then 1 else 0
    let bas : Fin k → Fin n := fun j => ⟨2 ^ j.val,
      lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by have := j.isLt; omega)) hk1⟩
    let u : Fin n := ⟨0, by omega⟩
    let Z : Finset (Fin n) := insert u (Finset.univ.image bas)
    have hZc : r - k ≤ Zᶜ.card := by
      have h1 : Z.card ≤ k + 1 := by
        show (insert u (Finset.univ.image bas)).card ≤ k + 1
        have := Finset.card_insert_le u (Finset.univ.image bas)
        have h2 := Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := bas)
        simp only [Finset.card_univ, Fintype.card_fin] at h2
        omega
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    let p : Fin (r - k) ↪o Fin n := Zᶜ.orderEmbOfCardLe hZc
    have hp : ∀ t, p t ∉ Z := fun t => Finset.mem_compl.mp (Zᶜ.orderEmbOfCardLe_mem hZc t)
    let W : Fin n → Fin b → ZMod 2 := fun i s =>
      ∑ t : Fin (r - k), (if i = p t then 1 else 0) * (if s.val = t.val + 1 then 1 else 0)
    let g : Fin n → Fin b × (Fin k → ZMod 2) → ZMod 2 := fun i sa =>
      ∑ j, x i j * sa.2 j + W i sa.1
    let G : Matrix (Fin n) (Fin m) (ZMod 2) := fun i c => g i (e c)
    let T : Fin n → Fin m → Bool := fun i c => decide (G i c = 1)
    let v : Fin m := e.symm (⟨0, hb0⟩, 0)
    have hxu : x u = 0 := by funext j; simp [x, u]
    have hWZ : ∀ i ∈ Z, ∀ s, W i s = 0 := by
      intro i hi s
      apply Finset.sum_eq_zero
      intro t _
      have : i ≠ p t := fun h => hp t (h ▸ hi)
      simp [this]
    have hWu : ∀ s, W u s = 0 := hWZ u (Finset.mem_insert_self _ _)
    have hWbas : ∀ j s, W (bas j) s = 0 := fun j =>
      hWZ (bas j) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
    have hW0 : ∀ i, W i ⟨0, hb0⟩ = 0 := by
      intro i
      apply Finset.sum_eq_zero
      intro t _
      simp
    have hxinj : Function.Injective x := by
      intro i i' h
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < k
      · have := congrFun h ⟨j, hj⟩
        simp only [x] at this
        cases h1 : i.val.testBit j <;> cases h2 : i'.val.testBit j <;> simp_all
      · have hi : i.val < 2 ^ j :=
          lt_of_lt_of_le i.isLt (le_trans hk2 (Nat.pow_le_pow_right (by norm_num) (by omega)))
        have hi' : i'.val < 2 ^ j :=
          lt_of_lt_of_le i'.isLt (le_trans hk2 (Nat.pow_le_pow_right (by norm_num) (by omega)))
        rw [Nat.testBit_eq_false_of_lt hi, Nat.testBit_eq_false_of_lt hi']
    have hxbas : ∀ l j, x (bas l) j = if l = j then 1 else 0 := by
      intro l j
      simp only [x, bas]
      rw [Nat.testBit_two_pow]
      by_cases h : l = j
      · subst h; simp
      · have h' : l.val ≠ j.val := fun h'' => h (Fin.ext h'')
        simp [h, h']
    have hGv : ∀ i, G i v = 0 := by
      intro i
      simp only [G, g, v, Equiv.apply_symm_apply, Pi.zero_apply, mul_zero,
        Finset.sum_const_zero, zero_add]
      exact hW0 i
    have hGu : ∀ c, G u c = 0 := by
      intro c
      simp only [G, g, hxu, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
      exact hWu _
    refine ⟨T, u, v, ?_, ?_⟩
    · intro i j hij
      have hx : x i ≠ x j := fun h => hij (hxinj h)
      have hF : (Finset.univ.filter (fun c : Fin m => T i c ≠ T j c))
          = Finset.univ.filter (fun c => G i c ≠ G j c) :=
        Finset.filter_congr (fun c _ => z2_decide_ne _ _)
      rw [hF, Finset.card_filter, ← Equiv.sum_comp e.symm]
      simp only [G, Equiv.apply_symm_apply]
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      have hterm : ∀ s : Fin b,
          2 * ∑ a : Fin k → ZMod 2, (if g i (s, a) ≠ g j (s, a) then 1 else 0) = 2 ^ k := by
        intro s
        rw [← Finset.card_filter]
        exact half_card (x i) (x j) hx (W i s) (W j s)
      rw [Finset.sum_congr rfl (fun s _ => hterm s)]
      simp [m, mul_comm]
    · intro E A
      have hAG : A = G := by
        ext i c
        simp only [A, E, T, z2_toNat_decide, hGv, hGu, add_zero]
      show A.rank = r
      rw [hAG]
      apply le_antisymm
      · let P : Matrix (Fin n) (Fin k ⊕ Fin (r - k)) (ZMod 2) := fun i q =>
          Sum.elim (fun j => x i j) (fun t => if i = p t then 1 else 0) q
        let Q : Matrix (Fin k ⊕ Fin (r - k)) (Fin m) (ZMod 2) := fun q c =>
          Sum.elim (fun j => (e c).2 j) (fun t => if (e c).1.val = t.val + 1 then 1 else 0) q
        have hPQ : G = P * Q := by
          ext i c
          rw [Matrix.mul_apply, Fintype.sum_sum_type]
          rfl
        rw [hPQ]
        calc (P * Q).rank ≤ P.rank := rank_mul_le_left _ _
          _ ≤ Fintype.card (Fin k ⊕ Fin (r - k)) := rank_le_card_width _
          _ = r := by simp; omega
      · let f : Fin (r - k) ⊕ Fin k → Fin n := Sum.elim (fun t => p t) bas
        let gc : Fin (r - k) ⊕ Fin k → Fin m := Sum.elim
          (fun t => e.symm (⟨t.val + 1, by have := t.isLt; omega⟩, 0))
          (fun j => e.symm (⟨0, hb0⟩, Pi.single j 1))
        let M := G.submatrix f gc
        have h11 : M.toBlocks₁₁ = 1 := by
          ext t t'
          show G (f (Sum.inl t)) (gc (Sum.inl t')) = (1 : Matrix _ _ (ZMod 2)) t t'
          simp only [f, gc, Sum.elim_inl, G, g,
            Equiv.apply_symm_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, W]
          rw [Finset.sum_eq_single t]
          · by_cases h : t = t'
            · subst h; simp
            · have h' : t'.val + 1 ≠ t.val + 1 := fun h'' => h (Fin.ext (by omega))
              simp [h]
              omega
          · intro t'' _ ht''
            have : p t ≠ p t'' := fun h'' => ht'' (p.injective h'').symm
            simp [this]
          · intro h; exact absurd (Finset.mem_univ t) h
        have h21 : M.toBlocks₂₁ = 0 := by
          ext j t
          show G (f (Sum.inr j)) (gc (Sum.inl t)) = (0 : Matrix _ _ (ZMod 2)) j t
          simp only [f, gc, Sum.elim_inl, Sum.elim_inr,
            G, g, Equiv.apply_symm_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
            zero_add]
          exact hWbas j _
        have h22 : M.toBlocks₂₂ = 1 := by
          ext l j
          show G (f (Sum.inr l)) (gc (Sum.inr j)) = (1 : Matrix _ _ (ZMod 2)) l j
          simp only [f, gc, Sum.elim_inr, G, g,
            Equiv.apply_symm_apply, hWbas, add_zero, Pi.single_apply, mul_ite, mul_one, mul_zero,
            Finset.sum_ite_eq', Finset.mem_univ, ite_true, hxbas]
          exact Matrix.one_apply.symm
        have hblk := Matrix.fromBlocks_toBlocks M
        rw [h11, h21, h22] at hblk
        have hdet : M.det = 1 := by
          rw [← hblk, det_fromBlocks_zero₂₁]; simp
        have hunit : IsUnit M := by
          rw [Matrix.isUnit_iff_isUnit_det, hdet]; exact isUnit_one
        have hrM := rank_of_isUnit M hunit
        have hle := rank_submatrix_le G f gc
        rw [show G.submatrix f gc = M from rfl, hrM] at hle
        simpa [Fintype.card_sum, Fintype.card_fin, Nat.sub_add_cancel hkr] using hle
