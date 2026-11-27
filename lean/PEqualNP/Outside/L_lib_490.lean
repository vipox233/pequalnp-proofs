import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_490_aux

open PEqualNP.ProofComplexity

private def Proper {n : Nat} (C : Clause (Fin n)) : Prop :=
  ∀ i : Fin n, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C)

private def bad {n : Nat} (C : Clause (Fin n)) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun a => ∀ l ∈ C, a l.1 = !l.2)

private lemma mem_bad_iff {n : Nat} (C : Clause (Fin n)) (a : Fin n → Bool) :
    a ∈ bad C ↔ ¬ ClauseSat a C := by
  simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, ClauseSat, not_exists, not_and]
  constructor
  · intro h ⟨i, b⟩ hl heq
    have := h (i, b) hl
    dsimp only at heq this
    rw [heq] at this
    cases b <;> cases this
  · intro h l hl
    have hne := h l hl
    cases ha : a l.1 <;> cases hb : l.2 <;> simp_all

private lemma card_bad {n : Nat} (C : Clause (Fin n)) (hP : Proper C) :
    (bad C).card = 2 ^ (n - C.card) := by
  let V : Finset (Fin n) := C.image Prod.fst
  have hVcard : V.card = C.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    rcases x with ⟨ix, bx⟩
    rcases y with ⟨iy, by_⟩
    dsimp only at hxy
    subst hxy
    cases bx <;> cases by_
    · rfl
    · exact absurd ⟨hy, hx⟩ (hP ix)
    · exact absurd ⟨hx, hy⟩ (hP ix)
    · rfl
  let Free := {i : Fin n // i ∉ V}
  have hbij : (bad C).card = (Finset.univ : Finset (Free → Bool)).card := by
    refine Finset.card_bij (fun a _ => fun j : Free => a j.val) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a1 ha1 a2 ha2 heq
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at ha1 ha2
      funext i
      by_cases hi : i ∈ V
      · rcases Finset.mem_image.mp hi with ⟨⟨j, b⟩, hjb, hji⟩
        dsimp only at hji
        subst hji
        rw [ha1 (j, b) hjb, ha2 (j, b) hjb]
      · exact congrFun heq ⟨i, hi⟩
    · intro f _
      let a : Fin n → Bool := fun i =>
        if (i, true) ∈ C then false
        else if (i, false) ∈ C then true
        else if hi : i ∈ V then false
        else f ⟨i, hi⟩
      refine ⟨a, ?_, ?_⟩
      · simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
        intro ⟨i, b⟩ hib
        cases b with
        | true =>
          simp only [a, hib, ↓reduceIte, Bool.not_true]
        | false =>
          have hnt : (i, true) ∉ C := fun ht => hP i ⟨ht, hib⟩
          simp only [a, hnt, hib, ↓reduceIte, Bool.not_false]
      · funext ⟨i, hi⟩
        have hnt : (i, true) ∉ C := fun ht => hi (Finset.mem_image.mpr ⟨(i, true), ht, rfl⟩)
        have hnf : (i, false) ∉ C := fun hf => hi (Finset.mem_image.mpr ⟨(i, false), hf, rfl⟩)
        simp only [a, hnt, hnf, hi, ↓reduceIte, ↓reduceDIte]
  rw [hbij, Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  have hfree : Fintype.card Free = n - C.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hVcard]
  rw [hfree]

private lemma disjoint_bad_iff {n : Nat} {C E : Clause (Fin n)} (hC : Proper C) (hE : Proper E) :
    Disjoint (bad C) (bad E) ↔ ∃ i : Fin n, ∃ b : Bool, (i, b) ∈ C ∧ (i, !b) ∈ E := by
  constructor
  · intro hdisj
    by_contra hno
    push_neg at hno
    let a : Fin n → Bool := fun i =>
      if (i, true) ∈ C ∨ (i, true) ∈ E then false else true
    have haC : a ∈ bad C := by
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
      intro ⟨i, b⟩ hib
      cases b with
      | true =>
        simp only [a, Or.inl hib, ↓reduceIte, Bool.not_true]
      | false =>
        have hntC : (i, true) ∉ C := fun ht => hC i ⟨ht, hib⟩
        have hntE : (i, true) ∉ E := fun ht => hno i false hib (by simpa using ht)
        simp only [a, hntC, hntE, or_self, ↓reduceIte, Bool.not_false]
    have haE : a ∈ bad E := by
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
      intro ⟨i, b⟩ hib
      cases b with
      | true =>
        simp only [a, Or.inr hib, ↓reduceIte, Bool.not_true]
      | false =>
        have hntE : (i, true) ∉ E := fun ht => hE i ⟨ht, hib⟩
        have hntC : (i, true) ∉ C := fun ht => hno i true ht (by simpa using hib)
        simp only [a, hntC, hntE, or_self, ↓reduceIte, Bool.not_false]
    exact Finset.disjoint_left.mp hdisj haC haE
  · rintro ⟨i, b, hCmem, hEmem⟩
    rw [Finset.disjoint_left]
    intro a haC haE
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at haC haE
    have h1 := haC (i, b) hCmem
    have h2 := haE (i, !b) hEmem
    dsimp only at h1 h2
    rw [h1] at h2
    cases b <;> cases h2

private theorem solve_490 (n : Nat) (F : Finset (Clause (Fin n)))
    (hProp : ∀ C ∈ F, Proper C)
    (hUnsat : ¬ Satisfiable (↑F : Set (Clause (Fin n)))) :
    let mass := F.sum (fun C => 2 ^ (n - C.card))
    2 ^ n ≤ mass ∧
      (mass = 2 ^ n ↔ ∀ C ∈ F, ∀ E ∈ F, C ≠ E →
        ∃ i : Fin n, ∃ b : Bool, (i, b) ∈ C ∧ (i, !b) ∈ E) := by
  intro mass
  have hcover : F.biUnion bad = Finset.univ := by
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
    by_contra hnone
    push_neg at hnone
    apply hUnsat
    refine ⟨a, fun C hCF => ?_⟩
    have hnot := hnone C hCF
    rw [mem_bad_iff] at hnot
    exact not_not.mp hnot
  have hsum : mass = F.sum (fun C => (bad C).card) := by
    dsimp only [mass]
    apply Finset.sum_congr rfl
    intro C hCF
    exact (card_bad C (hProp C hCF)).symm
  have hcard_univ : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
    simp
  have hle : 2 ^ n ≤ mass := by
    rw [hsum, ← hcard_univ, ← hcover]
    exact Finset.card_biUnion_le
  refine ⟨hle, ?_⟩
  constructor
  · intro heq C hCF E hEF hne
    rw [← disjoint_bad_iff (hProp C hCF) (hProp E hEF)]
    rw [Finset.disjoint_left]
    intro a haC haE
    have hmem_rest : a ∈ (F.erase C).biUnion bad :=
      Finset.mem_biUnion.mpr ⟨E, Finset.mem_erase.mpr ⟨hne.symm, hEF⟩, haE⟩
    have hinter_pos : 0 < (bad C ∩ (F.erase C).biUnion bad).card :=
      Finset.card_pos.mpr ⟨a, Finset.mem_inter.mpr ⟨haC, hmem_rest⟩⟩
    have hunion_eq : bad C ∪ (F.erase C).biUnion bad = F.biUnion bad := by
      have h1 : insert C (F.erase C) = F := Finset.insert_erase hCF
      conv_rhs => rw [← h1]
      exact Finset.biUnion_insert.symm
    have hci := Finset.card_union_add_card_inter (bad C) ((F.erase C).biUnion bad)
    rw [hunion_eq, hcover, hcard_univ] at hci
    have hrest_le : ((F.erase C).biUnion bad).card ≤ (F.erase C).sum (fun D => (bad D).card) :=
      Finset.card_biUnion_le
    have hsum_split : (bad C).card + (F.erase C).sum (fun D => (bad D).card) =
        F.sum (fun D => (bad D).card) := Finset.add_sum_erase F (fun D => (bad D).card) hCF
    omega
  · intro hpair
    rw [hsum, ← hcard_univ, ← hcover]
    symm
    apply Finset.card_biUnion
    intro C hCF E hEF hne
    exact (disjoint_bad_iff (hProp C hCF) (hProp E hEF)).mpr (hpair C hCF E hEF hne)

end PEqualNP.Outside.L_lib_490_aux

theorem PEqualNP.Outside.L_lib_490 : ∀ (n : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Fin n))),
  (∀ C ∈ F, ∀ i : Fin n, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C)) →
  ¬ PEqualNP.ProofComplexity.Satisfiable (↑F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) →
  let mass := F.sum (fun C => 2 ^ (n - C.card))
  2 ^ n ≤ mass ∧
    (mass = 2 ^ n ↔ ∀ C ∈ F, ∀ E ∈ F, C ≠ E →
      ∃ i : Fin n, ∃ b : Bool, (i,b) ∈ C ∧ (i,!b) ∈ E) := by
  intro n F hP hU
  exact PEqualNP.Outside.L_lib_490_aux.solve_490 n F hP hU
