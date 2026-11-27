import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_clb_056_aux

private def activeLeaves {I : ℕ} (S : Fin I → Bool) :
    PEqualNP.MetaComplexity.DMFormula I → ℕ
  | .lit i _ => if S i then 1 else 0
  | .and φ ψ => activeLeaves S φ + activeLeaves S ψ
  | .or φ ψ => activeLeaves S φ + activeLeaves S ψ

private theorem sum_activeLeaves_le {I d : ℕ} (tag : Fin I → Option (Fin d → Bool))
    (φ : PEqualNP.MetaComplexity.DMFormula I) :
    (∑ t : Fin d → Bool, activeLeaves (fun i => decide (tag i = some t)) φ) ≤ φ.leaves := by
  induction φ with
  | lit i b =>
    dsimp only [activeLeaves, PEqualNP.MetaComplexity.DMFormula.leaves]
    simp only [decide_eq_true_eq]
    cases tag i with
    | none => simp
    | some t0 => simp
  | and φ ψ ih1 ih2 =>
    dsimp only [activeLeaves, PEqualNP.MetaComplexity.DMFormula.leaves]
    rw [Finset.sum_add_distrib]
    omega
  | or φ ψ ih1 ih2 =>
    dsimp only [activeLeaves, PEqualNP.MetaComplexity.DMFormula.leaves]
    rw [Finset.sum_add_distrib]
    omega

private theorem cs_nat (e1 e2 L1 L2 a1 a2 b : ℕ)
    (h1 : e1 ^ 2 ≤ L1 * a1 * b) (h2 : e2 ^ 2 ≤ L2 * a2 * b) :
    (e1 + e2) ^ 2 ≤ (L1 + L2) * (a1 + a2) * b := by
  have h12 : 4 * (L1 * a2) * (L2 * a1) ≤ (L1 * a2 + L2 * a1) ^ 2 := by
    zify
    nlinarith [sq_nonneg ((L1 * a2 : ℤ) - L2 * a1)]
  have hsq : (2 * e1 * e2) ^ 2 ≤ ((L1 * a2 + L2 * a1) * b) ^ 2 := by
    calc (2 * e1 * e2) ^ 2 = 4 * e1 ^ 2 * e2 ^ 2 := by ring
      _ ≤ 4 * (L1 * a1 * b) * (L2 * a2 * b) := by nlinarith
      _ = 4 * (L1 * a2) * (L2 * a1) * b ^ 2 := by ring
      _ ≤ (L1 * a2 + L2 * a1) ^ 2 * b ^ 2 := by nlinarith
      _ = ((L1 * a2 + L2 * a1) * b) ^ 2 := by ring
  have hmid : 2 * e1 * e2 ≤ (L1 * a2 + L2 * a1) * b := by
    by_contra hlt
    have hgt : (L1 * a2 + L2 * a1) * b < 2 * e1 * e2 := by omega
    have : ((L1 * a2 + L2 * a1) * b) ^ 2 < (2 * e1 * e2) ^ 2 := Nat.pow_lt_pow_left hgt (by omega)
    omega
  nlinarith

private theorem khrapchenko_active {I : ℕ} (S : Fin I → Bool)
    (φ : PEqualNP.MetaComplexity.DMFormula I) :
    ∀ (A B : Finset (Fin I → Bool)) (E : Finset ((Fin I → Bool) × (Fin I → Bool))),
      (∀ x ∈ A, φ.eval x = true) →
      (∀ y ∈ B, φ.eval y = false) →
      (∀ p ∈ E, p.1 ∈ A ∧ p.2 ∈ B) →
      (∀ p ∈ E, ∀ i, S i = false → p.1 i = p.2 i) →
      (∀ i, S i = true → ∀ x, (E.filter (fun p => p.1 = x ∧ p.1 i ≠ p.2 i)).card ≤ 1) →
      (∀ i, S i = true → ∀ y, (E.filter (fun p => p.2 = y ∧ p.1 i ≠ p.2 i)).card ≤ 1) →
      E.card ^ 2 ≤ activeLeaves S φ * A.card * B.card := by
  induction φ with
  | lit i b =>
    intro A B E hA hB hEsub hEag hEm1 hEm2
    have hdiff : ∀ p ∈ E, p.1 i ≠ p.2 i := by
      intro p hp heq
      have h1 := hA p.1 (hEsub p hp).1
      have h2 := hB p.2 (hEsub p hp).2
      dsimp only [PEqualNP.MetaComplexity.DMFormula.eval] at h1 h2
      rw [heq] at h1
      rw [h1] at h2
      exact Bool.false_ne_true h2.symm
    cases hSi : S i with
    | false =>
      have hEe : E = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        exact hdiff p hp (hEag p hp i hSi)
      simp [hEe]
    | true =>
      dsimp only [activeLeaves]
      simp only [hSi, ↓reduceIte, one_mul]
      have hleA : E.card ≤ A.card := by
        apply Finset.card_le_card_of_injOn Prod.fst (fun p hp => (hEsub p hp).1)
        intro p1 hp1 p2 hp2 hfst
        have hc := hEm1 i hSi p1.1
        have hm1 : p1 ∈ E.filter (fun p => p.1 = p1.1 ∧ p.1 i ≠ p.2 i) :=
          Finset.mem_filter.mpr ⟨hp1, rfl, hdiff p1 hp1⟩
        have hm2 : p2 ∈ E.filter (fun p => p.1 = p1.1 ∧ p.1 i ≠ p.2 i) :=
          Finset.mem_filter.mpr ⟨hp2, hfst.symm, hdiff p2 hp2⟩
        exact Finset.card_le_one.mp hc p1 hm1 p2 hm2
      have hleB : E.card ≤ B.card := by
        apply Finset.card_le_card_of_injOn Prod.snd (fun p hp => (hEsub p hp).2)
        intro p1 hp1 p2 hp2 hsnd
        have hc := hEm2 i hSi p1.2
        have hm1 : p1 ∈ E.filter (fun p => p.2 = p1.2 ∧ p.1 i ≠ p.2 i) :=
          Finset.mem_filter.mpr ⟨hp1, rfl, hdiff p1 hp1⟩
        have hm2 : p2 ∈ E.filter (fun p => p.2 = p1.2 ∧ p.1 i ≠ p.2 i) :=
          Finset.mem_filter.mpr ⟨hp2, hsnd.symm, hdiff p2 hp2⟩
        exact Finset.card_le_one.mp hc p1 hm1 p2 hm2
      nlinarith
  | or φ1 φ2 ih1 ih2 =>
    intro A B E hA hB hEsub hEag hEm1 hEm2
    let A1 := A.filter (fun x => φ1.eval x = true)
    let A2 := A \ A1
    let E1 := E.filter (fun p => p.1 ∈ A1)
    let E2 := E.filter (fun p => p.1 ∈ A2)
    have hA1sub : A1 ⊆ A := Finset.filter_subset _ _
    have hAcard : A1.card + A2.card = A.card := by
      have := Finset.card_sdiff_add_card_eq_card hA1sub
      dsimp only [A2]; omega
    have hA1 : ∀ x ∈ A1, φ1.eval x = true := fun x hx => (Finset.mem_filter.mp hx).2
    have hA2 : ∀ x ∈ A2, φ2.eval x = true := by
      intro x hx
      obtain ⟨hxA, hxn⟩ := Finset.mem_sdiff.mp hx
      have h1 : φ1.eval x ≠ true := fun h => hxn (Finset.mem_filter.mpr ⟨hxA, h⟩)
      have hor := hA x hxA
      dsimp only [PEqualNP.MetaComplexity.DMFormula.eval] at hor
      cases hv1 : φ1.eval x
      · simpa [hv1] using hor
      · exact False.elim (h1 hv1)
    have hB1 : ∀ y ∈ B, φ1.eval y = false := by
      intro y hy; have h := hB y hy; dsimp only [PEqualNP.MetaComplexity.DMFormula.eval] at h
      exact (Bool.or_eq_false_iff.mp h).1
    have hB2 : ∀ y ∈ B, φ2.eval y = false := by
      intro y hy; have h := hB y hy; dsimp only [PEqualNP.MetaComplexity.DMFormula.eval] at h
      exact (Bool.or_eq_false_iff.mp h).2
    have hEcard : E.card = E1.card + E2.card := by
      have hdisj : Disjoint E1 E2 := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp2).2).2 (Finset.mem_filter.mp hp1).2
      have hun : E1 ∪ E2 = E := by
        ext p
        simp only [Finset.mem_union, E1, E2, Finset.mem_filter, A2, Finset.mem_sdiff]
        constructor
        · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
        · intro hp
          by_cases h1 : p.1 ∈ A1
          · exact Or.inl ⟨hp, h1⟩
          · exact Or.inr ⟨hp, (hEsub p hp).1, h1⟩
      rw [← hun, Finset.card_union_of_disjoint hdisj]
    have hsub_m1 : ∀ E' : Finset _, E' ⊆ E →
        ∀ i, S i = true → ∀ x, (E'.filter (fun p => p.1 = x ∧ p.1 i ≠ p.2 i)).card ≤ 1 := by
      intro E' hE' i hSi x
      exact (Finset.card_le_card (Finset.filter_subset_filter _ hE')).trans (hEm1 i hSi x)
    have hsub_m2 : ∀ E' : Finset _, E' ⊆ E →
        ∀ i, S i = true → ∀ y, (E'.filter (fun p => p.2 = y ∧ p.1 i ≠ p.2 i)).card ≤ 1 := by
      intro E' hE' i hSi y
      exact (Finset.card_le_card (Finset.filter_subset_filter _ hE')).trans (hEm2 i hSi y)
    have hc1 := ih1 A1 B E1 hA1 hB1
      (fun p hp => ⟨(Finset.mem_filter.mp hp).2, (hEsub p (Finset.mem_filter.mp hp).1).2⟩)
      (fun p hp => hEag p (Finset.mem_filter.mp hp).1)
      (hsub_m1 E1 (Finset.filter_subset _ _)) (hsub_m2 E1 (Finset.filter_subset _ _))
    have hc2 := ih2 A2 B E2 hA2 hB2
      (fun p hp => ⟨(Finset.mem_filter.mp hp).2, (hEsub p (Finset.mem_filter.mp hp).1).2⟩)
      (fun p hp => hEag p (Finset.mem_filter.mp hp).1)
      (hsub_m1 E2 (Finset.filter_subset _ _)) (hsub_m2 E2 (Finset.filter_subset _ _))
    dsimp only [activeLeaves]
    rw [hEcard, ← hAcard]
    exact cs_nat E1.card E2.card (activeLeaves S φ1) (activeLeaves S φ2) A1.card A2.card B.card hc1 hc2
  | and φ1 φ2 ih1 ih2 =>
    intro A B E hA hB hEsub hEag hEm1 hEm2
    let B1 := B.filter (fun y => φ1.eval y = false)
    let B2 := B \ B1
    let E1 := E.filter (fun p => p.2 ∈ B1)
    let E2 := E.filter (fun p => p.2 ∈ B2)
    have hB1sub : B1 ⊆ B := Finset.filter_subset _ _
    have hBcard : B1.card + B2.card = B.card := by
      have := Finset.card_sdiff_add_card_eq_card hB1sub
      dsimp only [B2]; omega
    have hB1 : ∀ y ∈ B1, φ1.eval y = false := fun y hy => (Finset.mem_filter.mp hy).2
    have hB2 : ∀ y ∈ B2, φ2.eval y = false := by
      intro y hy
      obtain ⟨hyB, hyn⟩ := Finset.mem_sdiff.mp hy
      have h1 : φ1.eval y ≠ false := fun h => hyn (Finset.mem_filter.mpr ⟨hyB, h⟩)
      have hand := hB y hyB
      dsimp only [PEqualNP.MetaComplexity.DMFormula.eval] at hand
      cases hv1 : φ1.eval y
      · exact False.elim (h1 hv1)
      · simpa [hv1] using hand
    have hA1 : ∀ x ∈ A, φ1.eval x = true := by
      intro x hx; have h := hA x hx; dsimp only [PEqualNP.MetaComplexity.DMFormula.eval] at h
      exact (Bool.and_eq_true _ _ |>.mp h).1
    have hA2 : ∀ x ∈ A, φ2.eval x = true := by
      intro x hx; have h := hA x hx; dsimp only [PEqualNP.MetaComplexity.DMFormula.eval] at h
      exact (Bool.and_eq_true _ _ |>.mp h).2
    have hEcard : E.card = E1.card + E2.card := by
      have hdisj : Disjoint E1 E2 := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp2).2).2 (Finset.mem_filter.mp hp1).2
      have hun : E1 ∪ E2 = E := by
        ext p
        simp only [Finset.mem_union, E1, E2, Finset.mem_filter, B2, Finset.mem_sdiff]
        constructor
        · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
        · intro hp
          by_cases h1 : p.2 ∈ B1
          · exact Or.inl ⟨hp, h1⟩
          · exact Or.inr ⟨hp, (hEsub p hp).2, h1⟩
      rw [← hun, Finset.card_union_of_disjoint hdisj]
    have hsub_m1 : ∀ E' : Finset _, E' ⊆ E →
        ∀ i, S i = true → ∀ x, (E'.filter (fun p => p.1 = x ∧ p.1 i ≠ p.2 i)).card ≤ 1 := by
      intro E' hE' i hSi x
      exact (Finset.card_le_card (Finset.filter_subset_filter _ hE')).trans (hEm1 i hSi x)
    have hsub_m2 : ∀ E' : Finset _, E' ⊆ E →
        ∀ i, S i = true → ∀ y, (E'.filter (fun p => p.2 = y ∧ p.1 i ≠ p.2 i)).card ≤ 1 := by
      intro E' hE' i hSi y
      exact (Finset.card_le_card (Finset.filter_subset_filter _ hE')).trans (hEm2 i hSi y)
    have hc1 := ih1 A B1 E1 hA1 hB1
      (fun p hp => ⟨(hEsub p (Finset.mem_filter.mp hp).1).1, (Finset.mem_filter.mp hp).2⟩)
      (fun p hp => hEag p (Finset.mem_filter.mp hp).1)
      (hsub_m1 E1 (Finset.filter_subset _ _)) (hsub_m2 E1 (Finset.filter_subset _ _))
    have hc2 := ih2 A B2 E2 hA2 hB2
      (fun p hp => ⟨(hEsub p (Finset.mem_filter.mp hp).1).1, (Finset.mem_filter.mp hp).2⟩)
      (fun p hp => hEag p (Finset.mem_filter.mp hp).1)
      (hsub_m1 E2 (Finset.filter_subset _ _)) (hsub_m2 E2 (Finset.filter_subset _ _))
    have hcs := cs_nat E1.card E2.card (activeLeaves S φ1) (activeLeaves S φ2) B1.card B2.card A.card
      (by nlinarith) (by nlinarith)
    dsimp only [activeLeaves]
    rw [hEcard, ← hBcard]
    nlinarith

private def xorList : List Bool → Bool
  | [] => false
  | b :: bs => xor b (xorList bs)

private theorem xorList_append (l1 l2 : List Bool) :
    xorList (l1 ++ l2) = xor (xorList l1) (xorList l2) := by
  induction l1 with
  | nil => simp [xorList]
  | cons b bs ih =>
    simp only [List.cons_append, xorList, ih]
    cases b <;> cases xorList bs <;> cases xorList l2 <;> rfl

private theorem xorList_snoc (l : List Bool) (b : Bool) :
    xorList (l ++ [b]) = xor (xorList l) b := by
  rw [xorList_append]; simp [xorList]

private theorem xor_finRange_shift {k : ℕ} (hk : 0 < k) (seq : ℕ → Bool) (u : ℕ) :
    xor (xorList ((List.finRange k).map (fun j => seq (u + j.val))))
      (xorList ((List.finRange k).map (fun j => seq (u + 1 + j.val)))) =
    xor (seq u) (seq (u + k)) := by
  have h1 : (List.finRange k).map (fun j => seq (u + j.val)) =
      seq u :: (List.finRange (k - 1)).map (fun j => seq (u + 1 + j.val)) := by
    apply List.ext_getElem
    · simp; omega
    · intro i hi1 hi2
      cases i with
      | zero => simp
      | succ i =>
        simp only [List.getElem_map, List.getElem_finRange, List.getElem_cons_succ, Fin.val_cast]
        congr 1; omega
  have h2 : (List.finRange k).map (fun j => seq (u + 1 + j.val)) =
      (List.finRange (k - 1)).map (fun j => seq (u + 1 + j.val)) ++ [seq (u + k)] := by
    apply List.ext_getElem
    · simp; omega
    · intro i hi1 hi2
      by_cases hi : i < k - 1
      · rw [List.getElem_append_left (by simp; omega)]
        simp only [List.getElem_map, List.getElem_finRange, Fin.val_cast]
      · rw [List.getElem_append_right (by simp; omega)]
        have heq : i = k - 1 := by simp at hi1; omega
        simp only [List.getElem_map, List.getElem_finRange, List.length_map, List.length_finRange,
          heq, Nat.sub_self, List.getElem_singleton, Fin.val_cast]
        congr 1; omega
  rw [h1, h2, xorList, xorList_snoc]
  generalize xorList ((List.finRange (k - 1)).map (fun j => seq (u + 1 + j.val))) = mid
  cases seq u <;> cases mid <;> cases seq (u + k) <;> rfl

private theorem xorList_rotate_eq {k : ℕ} (v : Fin (k + 1) → Bool)
    (hsum : xorList ((List.finRange (k + 1)).map v) = false) (u : ℕ) :
    xorList ((List.finRange k).map (fun j => v ⟨(u + j.val) % (k + 1), Nat.mod_lt _ (by omega)⟩)) =
    v ⟨(u + k) % (k + 1), Nat.mod_lt _ (by omega)⟩ := by
  have hfull : ∀ t : ℕ, xorList ((List.finRange (k + 1)).map
      (fun j => v ⟨(t + j.val) % (k + 1), Nat.mod_lt _ (by omega)⟩)) = false := by
    intro t
    induction t with
    | zero =>
      convert hsum using 2
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp only [List.getElem_map, List.getElem_finRange, zero_add]
        congr 1; ext; dsimp; exact Nat.mod_eq_of_lt (by simp at hi1; omega)
    | succ t ih =>
      have h1 : (List.finRange (k + 1)).map (fun j => v ⟨(t + j.val) % (k + 1), Nat.mod_lt _ (by omega)⟩) =
          v ⟨t % (k + 1), Nat.mod_lt _ (by omega)⟩ ::
            (List.finRange k).map (fun j => v ⟨(t + 1 + j.val) % (k + 1), Nat.mod_lt _ (by omega)⟩) := by
        apply List.ext_getElem
        · simp
        · intro i hi1 hi2
          cases i with
          | zero => simp
          | succ i =>
            simp only [List.getElem_map, List.getElem_finRange, List.getElem_cons_succ]
            congr 1; ext; dsimp; congr 1; omega
      have h2 : (List.finRange (k + 1)).map (fun j => v ⟨(t + 1 + j.val) % (k + 1), Nat.mod_lt _ (by omega)⟩) =
          (List.finRange k).map (fun j => v ⟨(t + 1 + j.val) % (k + 1), Nat.mod_lt _ (by omega)⟩) ++
            [v ⟨t % (k + 1), Nat.mod_lt _ (by omega)⟩] := by
        apply List.ext_getElem
        · simp
        · intro i hi1 hi2
          by_cases hi : i < k
          · rw [List.getElem_append_left (by simp; omega)]
            simp only [List.getElem_map, List.getElem_finRange, Fin.val_cast]
          · rw [List.getElem_append_right (by simp; omega)]
            have heq : i = k := by simp at hi1; omega
            simp only [List.getElem_map, List.getElem_finRange, List.length_map, List.length_finRange,
              heq, Nat.sub_self, List.getElem_singleton, Fin.val_cast]
            congr 1; ext; dsimp
            rw [show t + 1 + k = t + (k + 1) by omega, Nat.add_mod_right]
      rw [h1, xorList] at ih
      rw [h2, xorList_snoc, Bool.xor_comm]
      exact ih
  have hu := hfull u
  have hsplit : (List.finRange (k + 1)).map (fun j => v ⟨(u + j.val) % (k + 1), Nat.mod_lt _ (by omega)⟩) =
      (List.finRange k).map (fun j => v ⟨(u + j.val) % (k + 1), Nat.mod_lt _ (by omega)⟩) ++
        [v ⟨(u + k) % (k + 1), Nat.mod_lt _ (by omega)⟩] := by
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      by_cases hi : i < k
      · rw [List.getElem_append_left (by simp; omega)]
        simp only [List.getElem_map, List.getElem_finRange, Fin.val_cast]
      · rw [List.getElem_append_right (by simp; omega)]
        have heq : i = k := by simp at hi1; omega
        simp only [List.getElem_map, List.getElem_finRange, List.length_map, List.length_finRange,
          heq, Nat.sub_self, List.getElem_singleton, Fin.val_cast]
  rw [hsplit, xorList_snoc] at hu
  generalize hx : xorList ((List.finRange k).map (fun j => v ⟨(u + j.val) % (k + 1), Nat.mod_lt _ (by omega)⟩)) = xv
  generalize hy : v ⟨(u + k) % (k + 1), Nat.mod_lt _ (by omega)⟩ = yv
  rw [hx, hy] at hu
  cases xv <;> cases yv <;> simp_all

private def parity {m : ℕ} (x : Fin m → Bool) : Bool :=
  xorList ((List.finRange m).map x)

private theorem parity_update {m : ℕ} (x : Fin m → Bool) (j : Fin m) :
    parity (Function.update x j (!(x j))) = !(parity x) := by
  have haux : ∀ (l : List (Fin m)), j ∈ l → l.Nodup →
      xorList (l.map (Function.update x j (!(x j)))) = !(xorList (l.map x)) := by
    intro l hmem hnd
    induction l with
    | nil => simp at hmem
    | cons a ls ih =>
      simp only [List.nodup_cons] at hnd
      simp only [List.mem_cons] at hmem
      simp only [List.map_cons, xorList]
      rcases hmem with rfl | hmem'
      · have hrest : ls.map (Function.update x j (!(x j))) = ls.map x := by
          apply List.map_congr_left
          intro y hy
          have hne : y ≠ j := fun h => hnd.1 (h ▸ hy)
          exact Function.update_of_ne hne _ x
        rw [hrest, Function.update_self]
        cases x j <;> cases xorList (ls.map x) <;> rfl
      · have hne : a ≠ j := fun h => hnd.1 (h ▸ hmem')
        rw [Function.update_of_ne hne, ih hmem' hnd.2]
        cases x a <;> cases xorList (ls.map x) <;> rfl
  exact haux (List.finRange m) (List.mem_finRange j) (List.nodup_finRange m)

private theorem card_parity_eq {m : ℕ} (hm : 0 < m) :
    (Finset.univ.filter (fun x : Fin m → Bool => parity x = false)).card = 2 ^ (m - 1) ∧
    (Finset.univ.filter (fun x : Fin m → Bool => parity x = true)).card = 2 ^ (m - 1) := by
  let A := Finset.univ.filter (fun x : Fin m → Bool => parity x = false)
  let B := Finset.univ.filter (fun x : Fin m → Bool => parity x = true)
  let flip0 : (Fin m → Bool) → (Fin m → Bool) := fun x => Function.update x ⟨0, hm⟩ (!(x ⟨0, hm⟩))
  have hinv : ∀ x, flip0 (flip0 x) = x := by
    intro x; funext j; by_cases hj : j = ⟨0, hm⟩
    · subst hj; simp [flip0]
    · simp [flip0, hj]
  have hAB : A.card = B.card := by
    apply Finset.card_nbij' flip0 flip0
    · intro x hx
      simp only [Finset.mem_coe, A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [parity_update, hx]; rfl
    · intro x hx
      simp only [Finset.mem_coe, A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [parity_update, hx]; rfl
    · intro x _; exact hinv x
    · intro x _; exact hinv x
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have h1 := (Finset.mem_filter.mp hxA).2
    have h2 := (Finset.mem_filter.mp hxB).2
    rw [h1] at h2; exact Bool.false_ne_true h2
  have hun : A ∪ B = Finset.univ := by
    ext x; simp only [Finset.mem_union, A, B, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    cases parity x <;> simp
  have htot : A.card + B.card = 2 ^ m := by
    rw [← Finset.card_union_of_disjoint hdisj, hun, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ, Nat.mul_comm]
  dsimp only [A, B] at hAB htot
  exact ⟨by omega, by omega⟩

private theorem main_aux : ∀ d extra a q : ℕ,
    let k := d + 1
    let w := k + extra
    let m := a + 1
    let n := m * k + q * (k + 1)
    let hn : 0 < n := by dsimp [n, m, k]; positivity
    let stride := 2 ^ (w + 1)
    let I := n * stride
    ∀ F : PEqualNP.MetaComplexity.DMFormula I,
      (∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
        let inputs := fun addr : Fin I =>
          table ⟨(addr.val / stride) % n, Nat.mod_lt _ hn⟩ (fun bit => addr.val.testBit bit.val)
        F.eval inputs = true ↔ ∃ word : Fin n → Bool, ∀ i : Fin n,
          table i (fun j => word ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true) →
      2 ^ d * m ^ 2 ≤ F.leaves := by
  classical
  intro d extra a q k w m n hn stride I F hF
  have hk_pos : 0 < k := by dsimp [k]; omega
  have hm_pos : 0 < m := by dsimp [m]; omega
  have hstride_pos : 0 < stride := by dsimp [stride]; positivity
  have hkw : k ≤ w := by dsimp [w]; omega
  let tagOf (addr : Fin I) : Option (Fin d → Bool) :=
    let r := (addr.val / stride) % n
    if r < m * k ∧ r % k = 0 then
      some (fun j : Fin d => addr.val.testBit (j.val + 1))
    else none
  have hsum_tags := sum_activeLeaves_le tagOf F
  have hper_tag : ∀ t0 : Fin d → Bool,
      m ^ 2 ≤ activeLeaves (fun i => decide (tagOf i = some t0)) F := by
    intro t0
    let stepBit (t : Fin d → Bool) (x : Fin m → Bool) (b : Fin m) : Bool :=
      if t = t0 then x b else decide (b.val = 0)
    let tableOf (x : Fin m → Bool) (i : Fin n) (pat : Fin (w + 1) → Bool) : Bool :=
      if hi : i.val < m * k then
        if i.val % k = 0 then
          let b : Fin m := ⟨i.val / k, Nat.div_lt_of_lt_mul (by dsimp [k] at hi ⊢; linarith)⟩
          let t : Fin d → Bool := fun j => pat ⟨j.val + 1, by omega⟩
          pat ⟨k, by omega⟩ == xor (pat 0) (stepBit t x b)
        else
          pat ⟨k, by omega⟩ == pat 0
      else
        pat ⟨k, by omega⟩ == xorList ((List.finRange k).map (fun j => pat ⟨j.val, by omega⟩))
    let inputsOf (x : Fin m → Bool) : Fin I → Bool := fun addr =>
      tableOf x ⟨(addr.val / stride) % n, Nat.mod_lt _ hn⟩ (fun bit => addr.val.testBit bit.val)
    have hsat_iff : ∀ x : Fin m → Bool,
        F.eval (inputsOf x) = true ↔ parity x = false := by
      intro x
      have hFx := hF (tableOf x)
      dsimp only at hFx
      rw [hFx]
      constructor
      · rintro ⟨word, hword⟩
        let u0 := word ⟨0, hn⟩
        let t : Fin d → Bool := fun j => word ⟨(j.val + 1) % n, Nat.mod_lt _ hn⟩
        let pref (b : ℕ) : Bool :=
          xorList (((List.finRange m).take b).map (stepBit t x))
        have hsweep : ∀ (b : ℕ) (hb : b ≤ m),
            word ⟨(b * k) % n, Nat.mod_lt _ hn⟩ = xor u0 (pref b) ∧
            ∀ j : Fin d, word ⟨(b * k + j.val + 1) % n, Nat.mod_lt _ hn⟩ = t j := by
          intro b hb
          induction b with
          | zero =>
            refine ⟨by simp [u0, pref, xorList], fun j => by simp [t]⟩
          | succ b ih =>
            obtain ⟨ih0, iht⟩ := ih (by omega)
            have hbk_lt : b * k < m * k := Nat.mul_lt_mul_of_pos_right (by omega) hk_pos
            have hbk_n : b * k < n := by dsimp [n]; omega
            have hrow0 := hword ⟨b * k, hbk_n⟩
            dsimp only [tableOf] at hrow0
            have hmod0 : (b * k) % k = 0 := Nat.mul_mod_left b k
            have hdiv0 : (b * k) / k = b := Nat.mul_div_cancel b hk_pos
            simp only [hbk_lt, hmod0, ↓reduceDIte, ↓reduceIte, beq_iff_eq] at hrow0
            have hpat_t : (fun j : Fin d => word ⟨(b * k + j.val + 1) % n, Nat.mod_lt _ hn⟩) = t :=
              funext iht
            have hb_fin : (⟨(b * k) / k, Nat.div_lt_of_lt_mul (by dsimp [k] at hbk_lt ⊢; linarith)⟩ : Fin m) =
                ⟨b, by omega⟩ := Fin.ext hdiv0
            have h0_eq : (b * k + (0 : Fin (w + 1)).val) % n = (b * k) % n := by simp
            have hk_eq : (b * k + k) % n = ((b + 1) * k) % n := by congr 1; ring
            have hrow0' : word ⟨((b + 1) * k) % n, Nat.mod_lt _ hn⟩ =
                xor (word ⟨(b * k) % n, Nat.mod_lt _ hn⟩) (stepBit t x ⟨b, by omega⟩) := by
              have hfin1 : (⟨(b * k + k) % n, Nat.mod_lt _ hn⟩ : Fin n) =
                  ⟨((b + 1) * k) % n, Nat.mod_lt _ hn⟩ := Fin.ext hk_eq
              have hfin0 : (⟨(b * k + (0 : Fin (w + 1)).val) % n, Nat.mod_lt _ hn⟩ : Fin n) =
                  ⟨(b * k) % n, Nat.mod_lt _ hn⟩ := Fin.ext h0_eq
              have hpat_t' : (fun j : Fin d => word ⟨(b * k + (j.val + 1)) % n, Nat.mod_lt _ hn⟩) = t := by
                funext j
                have : (⟨(b * k + (j.val + 1)) % n, Nat.mod_lt _ hn⟩ : Fin n) =
                    ⟨(b * k + j.val + 1) % n, Nat.mod_lt _ hn⟩ := Fin.ext (by congr 1)
                rw [this, iht j]
              rw [hfin1, hfin0, hb_fin, hpat_t'] at hrow0
              exact hrow0
            have hpref_succ : pref (b + 1) = xor (pref b) (stepBit t x ⟨b, by omega⟩) := by
              dsimp only [pref]
              have hlt : b < (List.finRange m).length := by simp; omega
              rw [List.take_succ_eq_append_getElem hlt, List.map_append, List.map_singleton,
                xorList_snoc]
              simp
            constructor
            · rw [hrow0', ih0, hpref_succ]
              cases u0 <;> cases pref b <;> cases stepBit t x ⟨b, by omega⟩ <;> rfl
            · intro j
              have hij_lt : b * k + j.val + 1 < m * k := by
                have h1 : (b + 1) * k ≤ m * k := Nat.mul_le_mul_right _ (by omega)
                dsimp [k] at h1 ⊢; nlinarith [j.isLt]
              have hij_n : b * k + j.val + 1 < n := by dsimp [n]; omega
              have hrowj := hword ⟨b * k + j.val + 1, hij_n⟩
              dsimp only [tableOf] at hrowj
              have hmodj : (b * k + j.val + 1) % k ≠ 0 := by
                rw [show b * k + j.val + 1 = k * b + (j.val + 1) by ring, Nat.mul_add_mod,
                  Nat.mod_eq_of_lt (by dsimp [k]; omega)]
                omega
              simp only [hij_lt, hmodj, ↓reduceDIte, ↓reduceIte, beq_iff_eq] at hrowj
              have he1 : (b * k + j.val + 1 + k) % n = ((b + 1) * k + j.val + 1) % n := by
                congr 1; ring
              have he2 : (b * k + j.val + 1 + (0 : Fin (w + 1)).val) % n = (b * k + j.val + 1) % n := by
                simp
              have hfin1 : (⟨(b * k + j.val + 1 + k) % n, Nat.mod_lt _ hn⟩ : Fin n) =
                  ⟨((b + 1) * k + j.val + 1) % n, Nat.mod_lt _ hn⟩ := Fin.ext he1
              have hfin2 : (⟨(b * k + j.val + 1 + (0 : Fin (w + 1)).val) % n, Nat.mod_lt _ hn⟩ : Fin n) =
                  ⟨(b * k + j.val + 1) % n, Nat.mod_lt _ hn⟩ := Fin.ext he2
              rw [hfin1, hfin2] at hrowj
              exact hrowj.trans (iht j)
        obtain ⟨hm0, hmt⟩ := hsweep m le_rfl
        have hpad : ∀ (p : ℕ) (hp : p ≤ q) (r : Fin k),
            word ⟨(m * k + p * (k + 1) + r.val) % n, Nat.mod_lt _ hn⟩ =
            word ⟨(m * k + r.val) % n, Nat.mod_lt _ hn⟩ := by
          intro p hp
          induction p with
          | zero => intro r; simp
          | succ p ih =>
            intro r
            let base := m * k + p * (k + 1)
            let seq : ℕ → Bool := fun z => word ⟨(base + z) % n, Nat.mod_lt _ hn⟩
            have hstep_seq : ∀ u : ℕ, u ≤ k →
                seq (u + k) = xorList ((List.finRange k).map (fun j => seq (u + j.val))) := by
              intro u hu
              have hge : ¬ (base + u < m * k) := by dsimp [base]; omega
              have hlt : base + u < n := by
                have : (p + 1) * (k + 1) ≤ q * (k + 1) := Nat.mul_le_mul_right _ hp
                dsimp [base, n]; nlinarith
              have hrw := hword ⟨base + u, hlt⟩
              dsimp only [tableOf] at hrw
              simp only [hge, ↓reduceDIte, beq_iff_eq] at hrw
              convert hrw using 1
              · dsimp only [seq]; congr 1; ext; dsimp; congr 1; omega
              · congr 1; apply List.map_congr_left; intro j _
                dsimp only [seq]; congr 1; ext; dsimp; congr 1; omega
            have h1 := hstep_seq r.val (by omega)
            have h2 := hstep_seq (r.val + 1) (by omega)
            have hsh := xor_finRange_shift hk_pos seq r.val
            rw [← h1, ← h2] at hsh
            have hseq_eq : seq (r.val + 1 + k) = seq r.val := by
              generalize ha : seq (r.val + k) = va at hsh
              generalize hb : seq (r.val + 1 + k) = vb at hsh
              generalize hc : seq r.val = vc at hsh
              cases va <;> cases vb <;> cases vc <;> simp at hsh ⊢
            have hprev := ih (by omega) r
            rw [← hprev]
            convert hseq_eq using 1
            dsimp only [seq]; congr 1; ext; dsimp; congr 1; ring
        have hclose := hpad q le_rfl ⟨0, hk_pos⟩
        have hwrap : (m * k + q * (k + 1) + 0) % n = 0 := by
          change (n + 0) % n = 0; simp
        have hwrap_fin : (⟨(m * k + q * (k + 1) + 0) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨0, hn⟩ :=
          Fin.ext hwrap
        rw [hwrap_fin] at hclose
        have hm0' : word ⟨(m * k + 0) % n, Nat.mod_lt _ hn⟩ = xor u0 (pref m) := by simpa using hm0
        rw [hm0'] at hclose
        have hpm_false : pref m = false := by
          change u0 = xor u0 (pref m) at hclose
          generalize hu : u0 = vu at hclose
          generalize hp : pref m = vp at hclose
          cases vu <;> cases vp <;> simp at hclose ⊢
        have hpm_full : pref m = xorList ((List.finRange m).map (stepBit t x)) := by
          dsimp only [pref]; rw [List.take_of_length_le (by simp)]
        by_cases ht : t = t0
        · subst ht
          have : xorList ((List.finRange m).map (stepBit t x)) = parity x := by
            dsimp only [parity]; congr 1; apply List.map_congr_left; intro b _; simp [stepBit]
          rw [hpm_full, this] at hpm_false
          exact hpm_false
        · have hodd : xorList ((List.finRange m).map (stepBit t x)) = true := by
            have hfr : List.finRange m = ⟨0, hm_pos⟩ :: (List.finRange (m - 1)).map
                (fun j : Fin (m - 1) => ⟨j.val + 1, by omega⟩) := by
              apply List.ext_getElem
              · simp; omega
              · intro i hi1 hi2
                cases i with
                | zero => ext; simp
                | succ i => simp
            rw [hfr, List.map_cons, xorList]
            have hhead : stepBit t x ⟨0, hm_pos⟩ = true := by simp [stepBit, ht]
            have htail_false : ∀ l : List (Fin (m - 1)),
                xorList ((l.map (fun j : Fin (m - 1) => (⟨j.val + 1, by omega⟩ : Fin m))).map
                  (stepBit t x)) = false := by
              intro l; induction l with
              | nil => rfl
              | cons c cs ihc =>
                simp only [List.map_cons, xorList, ihc]
                have hc : stepBit t x ⟨c.val + 1, by omega⟩ = false := by simp [stepBit, ht]
                rw [hc]; rfl
            rw [hhead, htail_false]; rfl
          rw [hpm_full, hodd] at hpm_false
          exact False.elim (Bool.false_ne_true hpm_false.symm)
      · intro hpar
        let pref0 (b : ℕ) : Bool := xorList (((List.finRange m).take b).map x)
        have hpref0_0 : pref0 0 = false := rfl
        have hpref0_m : pref0 m = false := by
          dsimp only [pref0]; rw [List.take_of_length_le (by simp)]; exact hpar
        have hpref0_succ : ∀ b : Fin m, pref0 (b.val + 1) = xor (pref0 b.val) (x b) := by
          intro b; dsimp only [pref0]
          have hlt : b.val < (List.finRange m).length := by simp [b.isLt]
          rw [List.take_succ_eq_append_getElem hlt, List.map_append, List.map_singleton, xorList_snoc]
          simp
        let v : Fin (k + 1) → Bool := fun r =>
          if h0 : r.val = 0 then false
          else if hk1 : r.val < k then t0 ⟨r.val - 1, by dsimp [k] at hk1; omega⟩
          else xorList ((List.finRange d).map t0)
        have hv_sum : xorList ((List.finRange (k + 1)).map v) = false := by
          have hsp : (List.finRange (k + 1)).map v =
              false :: ((List.finRange d).map t0 ++ [xorList ((List.finRange d).map t0)]) := by
            apply List.ext_getElem
            · simp [k]
            · intro i hi1 hi2
              simp only [List.getElem_map, List.getElem_finRange]
              cases i with
              | zero => simp [v]
              | succ i =>
                simp only [List.getElem_cons_succ]
                by_cases hi : i < d
                · rw [List.getElem_append_left (by simp; omega), List.getElem_map, List.getElem_finRange]
                  dsimp only [v]
                  have h1 : ¬ (i + 1 = 0) := by omega
                  have h2 : i + 1 < k := by dsimp [k]; omega
                  simp only [Fin.val_cast, h1, h2, ↓reduceDIte]
                  congr 1
                · rw [List.getElem_append_right (by simp; omega)]
                  have heq : i = d := by simp at hi1; dsimp [k] at hi1; omega
                  simp only [List.length_map, List.length_finRange, heq, Nat.sub_self,
                    List.getElem_singleton]
                  dsimp only [v]
                  have h2 : ¬ (d + 1 < k) := by dsimp [k]; omega
                  simp [h2]
          rw [hsp, xorList, xorList_snoc]
          cases xorList ((List.finRange d).map t0) <;> rfl
        let word : Fin n → Bool := fun i =>
          if i.val < m * k then
            if hr : i.val % k = 0 then pref0 (i.val / k)
            else t0 ⟨i.val % k - 1, by have := Nat.mod_lt i.val hk_pos; dsimp [k] at this hr ⊢; omega⟩
          else
            v ⟨(i.val - m * k) % (k + 1), Nat.mod_lt _ (by omega)⟩
        have hword_v : ∀ (idx : ℕ), m * k ≤ idx → idx < n + k →
            word ⟨idx % n, Nat.mod_lt _ hn⟩ =
            v ⟨(idx - m * k) % (k + 1), Nat.mod_lt _ (by omega)⟩ := by
          intro idx hge hlt
          by_cases hlt_n : idx < n
          · rw [show (⟨idx % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨idx, hlt_n⟩ from Fin.ext (Nat.mod_eq_of_lt hlt_n)]
            dsimp only [word]
            have hnot : ¬ (idx < m * k) := by omega
            simp [hnot]
          · have hsub_lt : idx - n < k := by omega
            have hsub_mk : idx - n < m * k := by
              have : 1 * k ≤ m * k := Nat.mul_le_mul_right _ hm_pos
              omega
            have hsub_n : idx - n < n := by dsimp [n]; omega
            have hmod_n : idx % n = idx - n := by
              conv_lhs => rw [show idx = (idx - n) + n by omega]
              rw [Nat.add_mod_right, Nat.mod_eq_of_lt hsub_n]
            rw [show (⟨idx % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨idx - n, by omega⟩ from Fin.ext hmod_n]
            have hmod_k1 : (idx - m * k) % (k + 1) = idx - n := by
              have h1 : idx - m * k = (idx - n) + q * (k + 1) := by dsimp [n]; omega
              rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
            dsimp only [word]
            simp only [hsub_mk, ↓reduceIte]
            by_cases hz : idx - n = 0
            · have h0 : (idx - n) % k = 0 := by rw [hz]; simp
              have hdiv : (idx - n) / k = 0 := by rw [hz]; simp
              simp only [h0, ↓reduceDIte, hdiv, hpref0_0]
              have hv0 : (⟨(idx - m * k) % (k + 1), Nat.mod_lt _ (by omega)⟩ : Fin (k + 1)) = 0 := by
                ext; dsimp; omega
              rw [hv0]; simp [v]
            · have hnz : (idx - n) % k ≠ 0 := by rw [Nat.mod_eq_of_lt hsub_lt]; exact hz
              simp only [hnz, ↓reduceDIte]
              dsimp only [v]
              have hv_nz : ¬ ((idx - m * k) % (k + 1) = 0) := by omega
              have hv_lt : (idx - m * k) % (k + 1) < k := by omega
              simp only [hv_nz, hv_lt, ↓reduceDIte]
              congr 1; ext; dsimp; rw [Nat.mod_eq_of_lt hsub_lt, hmod_k1]
        have hword_tail : ∀ (r : Fin d) (b : ℕ), b ≤ m →
            word ⟨(b * k + r.val + 1) % n, Nat.mod_lt _ hn⟩ = t0 r := by
          intro r b hb
          by_cases hbm : b < m
          · have hlt : b * k + r.val + 1 < m * k := by
              have h1 : (b + 1) * k ≤ m * k := Nat.mul_le_mul_right _ hbm
              dsimp [k] at h1 ⊢; nlinarith [r.isLt]
            have hlt_n : b * k + r.val + 1 < n := by dsimp [n]; omega
            rw [show (⟨(b * k + r.val + 1) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨b * k + r.val + 1, hlt_n⟩ from
              Fin.ext (Nat.mod_eq_of_lt hlt_n)]
            dsimp only [word]
            have hmod : (b * k + r.val + 1) % k = r.val + 1 := by
              rw [show b * k + r.val + 1 = k * b + (r.val + 1) by ring, Nat.mul_add_mod,
                Nat.mod_eq_of_lt (by dsimp [k]; omega)]
            have hnz : (b * k + r.val + 1) % k ≠ 0 := by omega
            simp only [hlt, hnz, ↓reduceIte, ↓reduceDIte]
            congr 1; ext; dsimp; omega
          · have hbeq : b = m := by omega
            subst hbeq
            rw [hword_v (m * k + r.val + 1) (by omega) (by dsimp [n, k]; omega)]
            have hm1 : (m * k + r.val + 1 - m * k) % (k + 1) = r.val + 1 := by
              rw [show m * k + r.val + 1 - m * k = r.val + 1 by omega,
                Nat.mod_eq_of_lt (by dsimp [k]; omega)]
            dsimp only [v]
            have h1 : ¬ ((m * k + r.val + 1 - m * k) % (k + 1) = 0) := by rw [hm1]; omega
            have h2 : (m * k + r.val + 1 - m * k) % (k + 1) < k := by rw [hm1]; dsimp [k]; omega
            simp only [h1, h2, ↓reduceDIte]
            congr 1; ext; dsimp; omega
        have hword_head : ∀ (b : ℕ), b ≤ m →
            word ⟨(b * k) % n, Nat.mod_lt _ hn⟩ = pref0 b := by
          intro b hb
          by_cases hbm : b < m
          · have hlt : b * k < m * k := Nat.mul_lt_mul_of_pos_right hbm hk_pos
            have hlt_n : b * k < n := by dsimp [n]; omega
            rw [show (⟨(b * k) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨b * k, hlt_n⟩ from
              Fin.ext (Nat.mod_eq_of_lt hlt_n)]
            dsimp only [word]
            simp [hlt, Nat.mul_mod_left, Nat.mul_div_cancel b hk_pos]
          · have hbeq : b = m := by omega
            subst hbeq
            rw [hword_v (m * k) le_rfl (by dsimp [n, k]; omega), hpref0_m]
            simp [v]
        refine ⟨word, ?_⟩
        intro i
        dsimp only [tableOf]
        by_cases hi : i.val < m * k
        · simp only [hi, ↓reduceDIte]
          by_cases hmod : i.val % k = 0
          · simp only [hmod, ↓reduceIte, beq_iff_eq]
            let b : Fin m := ⟨i.val / k, Nat.div_lt_of_lt_mul (by dsimp [k] at hi ⊢; linarith)⟩
            have hib : i.val = b.val * k := by
              have := Nat.div_add_mod i.val k
              dsimp [b]; nlinarith
            have ht_eq : (fun j : Fin d => word ⟨(i.val + (j.val + 1)) % n, Nat.mod_lt _ hn⟩) = t0 := by
              funext j
              rw [show i.val + (j.val + 1) = b.val * k + j.val + 1 by omega]
              exact hword_tail j b.val (by omega)
            have hstep : stepBit (fun j : Fin d => word ⟨(i.val + (j.val + 1)) % n, Nat.mod_lt _ hn⟩) x b = x b := by
              rw [ht_eq]; simp [stepBit]
            rw [hstep]
            have h0 : word ⟨(i.val + (0 : Fin (w + 1)).val) % n, Nat.mod_lt _ hn⟩ = pref0 b.val := by
              rw [show i.val + (0 : Fin (w + 1)).val = b.val * k by simp [hib]]
              exact hword_head b.val (by omega)
            have hk1 : word ⟨(i.val + k) % n, Nat.mod_lt _ hn⟩ = pref0 (b.val + 1) := by
              rw [show i.val + k = (b.val + 1) * k by rw [hib]; ring]
              exact hword_head (b.val + 1) (by omega)
            rw [h0, hk1, hpref0_succ b]
          · simp only [hmod, ↓reduceIte, beq_iff_eq]
            let b := i.val / k
            let r : Fin d := ⟨i.val % k - 1, by have := Nat.mod_lt i.val hk_pos; dsimp [k] at this hmod ⊢; omega⟩
            have hib : i.val = b * k + r.val + 1 := by
              have hdm := Nat.div_add_mod i.val k
              rw [Nat.mul_comm] at hdm
              dsimp [b, r]; have := Nat.mod_lt i.val hk_pos; dsimp [k] at this hmod hdm ⊢; omega
            have hb_lt : b < m := Nat.div_lt_of_lt_mul (by dsimp [k] at hi ⊢; linarith)
            have h0 : word ⟨(i.val + (0 : Fin (w + 1)).val) % n, Nat.mod_lt _ hn⟩ = t0 r := by
              rw [show i.val + (0 : Fin (w + 1)).val = b * k + r.val + 1 by simp [hib]]
              exact hword_tail r b (by omega)
            have hk1 : word ⟨(i.val + k) % n, Nat.mod_lt _ hn⟩ = t0 r := by
              rw [show i.val + k = (b + 1) * k + r.val + 1 by rw [hib]; ring]
              exact hword_tail r (b + 1) (by omega)
            rw [h0, hk1]
        · simp only [hi, ↓reduceDIte, beq_iff_eq]
          let u := i.val - m * k
          have hge : m * k ≤ i.val := by omega
          have h1 : word ⟨(i.val + k) % n, Nat.mod_lt _ hn⟩ =
              v ⟨(u + k) % (k + 1), Nat.mod_lt _ (by omega)⟩ := by
            rw [hword_v (i.val + k) (by omega) (by have := i.isLt; omega)]
            congr 1; ext; dsimp [u]; congr 1; omega
          have h2 : (List.finRange k).map (fun j => word ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) =
              (List.finRange k).map (fun j => v ⟨(u + j.val) % (k + 1), Nat.mod_lt _ (by omega)⟩) := by
            apply List.map_congr_left
            intro j _
            rw [hword_v (i.val + j.val) (by omega) (by have := i.isLt; have := j.isLt; omega)]
            congr 1; ext; dsimp [u]; congr 1; omega
          rw [h1, h2, xorList_rotate_eq v hv_sum u]
    have hinj : Function.Injective inputsOf := by
      intro x1 x2 heq
      funext b
      let packBits : ℕ → ℕ := Nat.rec 0 (fun s acc =>
        acc ||| (if hs : s < d then (if t0 ⟨s, hs⟩ then 1 <<< (s + 1) else 0) else 0))
      have hpack_lt : ∀ s, s ≤ d → packBits s < 2 ^ (s + 1) := by
        intro s hs
        induction s with
        | zero => simp [packBits]
        | succ s ih =>
          change (packBits s ||| (if h : s < d then (if t0 ⟨s, h⟩ then 1 <<< (s + 1) else 0) else 0)) <
            2 ^ (s + 1 + 1)
          have h1 : packBits s < 2 ^ (s + 1 + 1) :=
            (ih (by omega)).trans (Nat.pow_lt_pow_right (by omega) (by omega))
          have h2 : (if h : s < d then (if t0 ⟨s, h⟩ then 1 <<< (s + 1) else 0) else 0) <
              2 ^ (s + 1 + 1) := by
            split_ifs
            · rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right (by omega) (by omega)
            · positivity
            · positivity
          exact Nat.or_lt_two_pow h1 h2
      have hpack_bit : ∀ s (hs : s ≤ d) r, (packBits s).testBit r =
          if h : 0 < r ∧ r ≤ s then t0 ⟨r - 1, by omega⟩ else false := by
        intro s
        induction s with
        | zero =>
          intro _ r
          have hn : ¬ (0 < r ∧ r ≤ 0) := by omega
          change (0 : ℕ).testBit r = _
          rw [Nat.zero_testBit]
          exact (dite_eq_right_iff.mpr (fun h => False.elim (hn h))).symm
        | succ s ih =>
          intro hs r
          change (packBits s ||| (if h : s < d then (if t0 ⟨s, h⟩ then 1 <<< (s + 1) else 0) else 0)).testBit r = _
          rw [Nat.testBit_or, ih (by omega) r]
          have hsd : s < d := by omega
          simp only [hsd, ↓reduceDIte]
          by_cases hr : r = s + 1
          · subst hr
            have hn : ¬ (0 < s + 1 ∧ s + 1 ≤ s) := by omega
            have hy : 0 < s + 1 ∧ s + 1 ≤ s + 1 := by omega
            rw [dite_eq_right_iff.mpr (fun h => False.elim (hn h)), Bool.false_or]
            cases ht : t0 ⟨s, hsd⟩ <;> simp [Nat.testBit_shiftLeft, ht, hy]
          · have hshift : (if t0 ⟨s, hsd⟩ then 1 <<< (s + 1) else 0).testBit r = false := by
              split_ifs
              · rw [Nat.testBit_shiftLeft]
                by_cases hge : s + 1 ≤ r
                · cases hsub : r - (s + 1) with
                  | zero => omega
                  | succ u => simp [hge, Nat.testBit_succ]
                · simp [hge]
              · simp
            rw [hshift, Bool.or_false]
            by_cases h1 : 0 < r ∧ r ≤ s
            · have h2 : 0 < r ∧ r ≤ s + 1 := by omega
              simp only [h1, h2]
            · have h2 : ¬ (0 < r ∧ r ≤ s + 1) := by omega
              simp only [h1, h2, ↓reduceDIte]
      let patNat : ℕ := (1 <<< k) ||| packBits d
      have hpat_lt : patNat < stride := by
        have h1 : 1 <<< k < 2 ^ (k + 1) := by
          rw [Nat.shiftLeft_eq, one_mul]; exact Nat.pow_lt_pow_right (by omega) (by omega)
        have h2 : packBits d < 2 ^ (k + 1) :=
          (hpack_lt d le_rfl).trans (Nat.pow_lt_pow_right (by omega) (by dsimp [k]; omega))
        exact (Nat.or_lt_two_pow h1 h2).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
      let addrVal := (b.val * k) * stride + patNat
      have haddr_lt : addrVal < I := by
        have h1 : b.val * k + 1 ≤ n := by
          have : (b.val + 1) * k ≤ m * k := Nat.mul_le_mul_right _ b.isLt
          dsimp [n]; nlinarith
        dsimp [addrVal, I]; nlinarith
      let addr : Fin I := ⟨addrVal, haddr_lt⟩
      have hdiv : addr.val / stride = b.val * k := by
        dsimp [addr, addrVal]
        rw [Nat.mul_comm (b.val * k) stride, Nat.mul_add_div hstride_pos,
          Nat.div_eq_of_lt hpat_lt, add_zero]
      have hrow_mod : (addr.val / stride) % n = b.val * k := by
        rw [hdiv, Nat.mod_eq_of_lt (by
          have : b.val * k < m * k := Nat.mul_lt_mul_of_pos_right b.isLt hk_pos
          dsimp [n]; omega)]
      have hbit_shift : ∀ (j : ℕ), j ≤ w → addr.val.testBit j = patNat.testBit j := by
        intro j hj
        dsimp [addr, addrVal]
        rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
        have hpow : stride = 2 ^ j * (2 * 2 ^ (w - j)) := by
          dsimp [stride]; rw [← pow_succ', ← pow_add]; congr 1; omega
        rw [hpow,
          show (b.val * k) * (2 ^ j * (2 * 2 ^ (w - j))) + patNat =
            2 ^ j * ((b.val * k) * (2 * 2 ^ (w - j))) + patNat by ring,
          Nat.mul_add_div (by positivity),
          show (b.val * k) * (2 * 2 ^ (w - j)) + patNat / 2 ^ j =
            2 * ((b.val * k) * 2 ^ (w - j)) + patNat / 2 ^ j by ring,
          Nat.mul_add_mod]
      have hbit0 : addr.val.testBit 0 = false := by
        rw [hbit_shift 0 (by omega)]
        dsimp only [patNat]; rw [Nat.testBit_or, hpack_bit d le_rfl 0, Nat.testBit_shiftLeft]
        have : ¬ (k ≤ 0) := by omega
        simp [this]
      have hbitk : addr.val.testBit k = true := by
        rw [hbit_shift k hkw]
        dsimp only [patNat]; rw [Nat.testBit_or, Nat.testBit_shiftLeft]
        simp
      have hbitt : (fun j : Fin d => addr.val.testBit (j.val + 1)) = t0 := by
        funext j
        rw [hbit_shift (j.val + 1) (by dsimp [k] at hkw; omega)]
        dsimp only [patNat]
        rw [Nat.testBit_or, hpack_bit d le_rfl (j.val + 1), Nat.testBit_shiftLeft]
        have h1 : ¬ (k ≤ j.val + 1) := by dsimp [k]; omega
        have h2 : 0 < j.val + 1 ∧ j.val + 1 ≤ d := by omega
        simp [h1, h2]
      have heval_x : ∀ x : Fin m → Bool, inputsOf x addr = x b := by
        intro x
        dsimp only [inputsOf, tableOf]
        have hlt_mk : (addr.val / stride) % n < m * k := by
          rw [hrow_mod]; exact Nat.mul_lt_mul_of_pos_right b.isLt hk_pos
        have hmod0 : ((addr.val / stride) % n) % k = 0 := by
          rw [hrow_mod]; exact Nat.mul_mod_left b.val k
        simp only [hlt_mk, hmod0, ↓reduceDIte, ↓reduceIte, Fin.val_zero]
        have hb_eq : (⟨((addr.val / stride) % n) / k,
            Nat.div_lt_of_lt_mul (by dsimp [k] at hlt_mk ⊢; linarith)⟩ : Fin m) = b := by
          ext; dsimp; rw [hrow_mod, Nat.mul_div_cancel b.val hk_pos]
        rw [hb_eq, hbitk, hbit0, hbitt]
        simp [stepBit]
      have h := congrFun heq addr
      rwa [heval_x x1, heval_x x2] at h
    let A0 := Finset.univ.filter (fun x : Fin m → Bool => parity x = false)
    let B0 := Finset.univ.filter (fun y : Fin m → Bool => parity y = true)
    let A := A0.image inputsOf
    let B := B0.image inputsOf
    let mkEdge : (Fin m → Bool) × Fin m → (Fin I → Bool) × (Fin I → Bool) :=
      fun p => (inputsOf p.1, inputsOf (Function.update p.1 p.2 (!(p.1 p.2))))
    let E0 : Finset ((Fin m → Bool) × Fin m) := A0 ×ˢ Finset.univ
    let E := E0.image mkEdge
    have hmk_inj : Function.Injective mkEdge := by
      rintro ⟨x1, j1⟩ ⟨x2, j2⟩ heq
      simp only [mkEdge, Prod.mk.injEq] at heq
      have hx : x1 = x2 := hinj heq.1
      subst hx
      have hu : Function.update x1 j1 (!(x1 j1)) = Function.update x1 j2 (!(x1 j2)) := hinj heq.2
      have hj : j1 = j2 := by
        by_contra hne
        have := congrFun hu j1
        rw [Function.update_self, Function.update_of_ne hne] at this
        cases x1 j1 <;> simp at this
      subst hj; rfl
    have hA_card : A.card = 2 ^ (m - 1) := by
      rw [Finset.card_image_of_injective A0 hinj, (card_parity_eq hm_pos).1]
    have hB_card : B.card = 2 ^ (m - 1) := by
      rw [Finset.card_image_of_injective B0 hinj, (card_parity_eq hm_pos).2]
    have hE_card : E.card = m * 2 ^ (m - 1) := by
      rw [Finset.card_image_of_injective E0 hmk_inj, Finset.card_product, Finset.card_univ,
        Fintype.card_fin, (card_parity_eq hm_pos).1, Nat.mul_comm]
    have hA_eval : ∀ u ∈ A, F.eval u = true := by
      intro u hu
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
      exact (hsat_iff x).mpr (Finset.mem_filter.mp hx).2
    have hB_eval : ∀ v ∈ B, F.eval v = false := by
      intro v hv
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
      have hpy : parity y = true := (Finset.mem_filter.mp hy).2
      cases hfv : F.eval (inputsOf y) with
      | false => rfl
      | true =>
        have := (hsat_iff y).mp hfv
        rw [hpy] at this; exact False.elim (Bool.false_ne_true this.symm)
    have hE_sub : ∀ p ∈ E, p.1 ∈ A ∧ p.2 ∈ B := by
      intro p hp
      obtain ⟨⟨x, j⟩, hxj, rfl⟩ := Finset.mem_image.mp hp
      have hxA0 : x ∈ A0 := (Finset.mem_product.mp hxj).1
      have hpx : parity x = false := (Finset.mem_filter.mp hxA0).2
      refine ⟨Finset.mem_image.mpr ⟨x, hxA0, rfl⟩, ?_⟩
      refine Finset.mem_image.mpr ⟨Function.update x j (!(x j)), ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [parity_update, hpx]; rfl⟩
    have hE_agree : ∀ p ∈ E, ∀ addr, decide (tagOf addr = some t0) = false → p.1 addr = p.2 addr := by
      intro p hp addr hnot
      obtain ⟨⟨x, j⟩, _, rfl⟩ := Finset.mem_image.mp hp
      have hne : tagOf addr ≠ some t0 := by simpa using hnot
      dsimp only [mkEdge, inputsOf, tableOf]
      by_cases hlt : (addr.val / stride) % n < m * k
      · simp only [hlt, ↓reduceDIte]
        by_cases hmod : ((addr.val / stride) % n) % k = 0
        · simp only [hmod, ↓reduceIte]
          have htn : (fun j : Fin d => addr.val.testBit (j.val + 1)) ≠ t0 := by
            intro hteq
            apply hne
            dsimp only [tagOf]
            have hcond : (addr.val / stride) % n < m * k ∧ ((addr.val / stride) % n) % k = 0 := ⟨hlt, hmod⟩
            simp [hcond, hteq]
          simp [stepBit, htn]
        · simp [hmod]
      · simp [hlt]
    have hdiff_coord : ∀ (x : Fin m → Bool) (j : Fin m) (addr : Fin I),
        decide (tagOf addr = some t0) = true →
        inputsOf x addr ≠ inputsOf (Function.update x j (!(x j))) addr →
        j.val = ((addr.val / stride) % n) / k := by
      intro x j addr htag hne
      have htag' : tagOf addr = some t0 := of_decide_eq_true htag
      dsimp only [tagOf] at htag'
      split_ifs at htag' with hcond
      obtain ⟨hlt, hmod⟩ := hcond
      by_contra hjne
      apply hne
      dsimp only [inputsOf, tableOf]
      simp only [hlt, hmod, ↓reduceDIte, ↓reduceIte]
      have hne_fin : (⟨((addr.val / stride) % n) / k,
          Nat.div_lt_of_lt_mul (by dsimp [k] at hlt ⊢; linarith)⟩ : Fin m) ≠ j := by
        intro h; exact hjne (congrArg Fin.val h).symm
      dsimp only [stepBit]
      rw [Function.update_of_ne hne_fin]
    have hE_m1 : ∀ addr, decide (tagOf addr = some t0) = true → ∀ u,
        (E.filter (fun p => p.1 = u ∧ p.1 addr ≠ p.2 addr)).card ≤ 1 := by
      intro addr htag u
      rw [Finset.card_le_one]
      intro p1 hp1 p2 hp2
      obtain ⟨hp1E, hp1u, hp1d⟩ := Finset.mem_filter.mp hp1
      obtain ⟨hp2E, hp2u, hp2d⟩ := Finset.mem_filter.mp hp2
      obtain ⟨⟨x1, j1⟩, _, rfl⟩ := Finset.mem_image.mp hp1E
      obtain ⟨⟨x2, j2⟩, _, rfl⟩ := Finset.mem_image.mp hp2E
      have hx : x1 = x2 := hinj (hp1u.trans hp2u.symm)
      have hj1 := hdiff_coord x1 j1 addr htag hp1d
      have hj2 := hdiff_coord x2 j2 addr htag hp2d
      have hj : j1 = j2 := Fin.ext (hj1.trans hj2.symm)
      subst hx; subst hj; rfl
    have hE_m2 : ∀ addr, decide (tagOf addr = some t0) = true → ∀ v,
        (E.filter (fun p => p.2 = v ∧ p.1 addr ≠ p.2 addr)).card ≤ 1 := by
      intro addr htag v
      rw [Finset.card_le_one]
      intro p1 hp1 p2 hp2
      obtain ⟨hp1E, hp1v, hp1d⟩ := Finset.mem_filter.mp hp1
      obtain ⟨hp2E, hp2v, hp2d⟩ := Finset.mem_filter.mp hp2
      obtain ⟨⟨x1, j1⟩, _, rfl⟩ := Finset.mem_image.mp hp1E
      obtain ⟨⟨x2, j2⟩, _, rfl⟩ := Finset.mem_image.mp hp2E
      have hj1 := hdiff_coord x1 j1 addr htag hp1d
      have hj2 := hdiff_coord x2 j2 addr htag hp2d
      have hj : j1 = j2 := Fin.ext (hj1.trans hj2.symm)
      subst hj
      have hu : Function.update x1 j1 (!(x1 j1)) = Function.update x2 j1 (!(x2 j1)) :=
        hinj (hp1v.trans hp2v.symm)
      have hx : x1 = x2 := by
        funext c
        by_cases hc : c = j1
        · subst hc
          have := congrFun hu c
          rw [Function.update_self, Function.update_self] at this
          cases h1 : x1 c <;> cases h2 : x2 c <;> simp_all
        · have := congrFun hu c
          rwa [Function.update_of_ne hc, Function.update_of_ne hc] at this
      subst hx; rfl
    have hkh := khrapchenko_active (fun i => decide (tagOf i = some t0)) F A B E
      hA_eval hB_eval hE_sub hE_agree hE_m1 hE_m2
    rw [hE_card, hA_card, hB_card] at hkh
    have hpow_pos : 0 < (2 ^ (m - 1)) ^ 2 := by positivity
    have hmul : m ^ 2 * (2 ^ (m - 1)) ^ 2 ≤
        activeLeaves (fun i => decide (tagOf i = some t0)) F * (2 ^ (m - 1)) ^ 2 := by
      calc m ^ 2 * (2 ^ (m - 1)) ^ 2 = (m * 2 ^ (m - 1)) ^ 2 := by ring
        _ ≤ activeLeaves (fun i => decide (tagOf i = some t0)) F * 2 ^ (m - 1) * 2 ^ (m - 1) := hkh
        _ = activeLeaves (fun i => decide (tagOf i = some t0)) F * (2 ^ (m - 1)) ^ 2 := by ring
    exact Nat.le_of_mul_le_mul_right hmul hpow_pos
  calc 2 ^ d * m ^ 2 = ∑ _t : Fin d → Bool, m ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, smul_eq_mul]
    _ ≤ ∑ t : Fin d → Bool, activeLeaves (fun i => decide (tagOf i = some t)) F :=
        Finset.sum_le_sum (fun t _ => hper_tag t)
    _ ≤ F.leaves := hsum_tags

end PEqualNP.Outside.L_clb_056_aux

theorem PEqualNP.Outside.L_clb_056 : ∀ d extra a q : ℕ,
  let k := d + 1
  let w := k + extra
  let m := a + 1
  let n := m * k + q * (k + 1)
  let hn : 0 < n := by dsimp [n, m, k]; positivity
  let stride := 2 ^ (w + 1)
  let I := n * stride
  ∀ F : PEqualNP.MetaComplexity.DMFormula I,
    (∀ table : Fin n → (Fin (w + 1) → Bool) → Bool,
      let inputs := fun addr : Fin I =>
        table ⟨(addr.val / stride) % n, Nat.mod_lt _ hn⟩ (fun bit => addr.val.testBit bit.val)
      F.eval inputs = true ↔ ∃ word : Fin n → Bool, ∀ i : Fin n,
        table i (fun k => word ⟨(i.val + k.val) % n, Nat.mod_lt _ hn⟩) = true) →
    2 ^ d * m ^ 2 ≤ F.leaves :=
  PEqualNP.Outside.L_clb_056_aux.main_aux
