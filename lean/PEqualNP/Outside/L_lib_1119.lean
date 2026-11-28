import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1119

open Finset
open Classical

variable {n : ℕ}

def miss (H : Finset (Finset (Fin n))) (X : Finset (Fin n)) : Prop :=
  ∀ e ∈ H, ¬e ⊆ X

noncomputable def maximal (H : Finset (Finset (Fin n))) (A : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (univ : Finset (Finset (Fin n))).filter
    (fun X => X ⊆ A ∧ miss H X ∧ ∀ i ∈ A \ X, ¬miss H (insert i X))

def family (E : Finset (Finset (Fin n))) (D : Finset (Fin n)) :
    Finset (Finset (Finset (Fin n))) :=
  insert E (D.image (fun v => E.filter (fun e => v ∉ e)))

noncomputable def bank (E : Finset (Finset (Fin n))) (D : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  E ∪ maximal E univ ∪
    D.biUnion (fun v => ((maximal E univ).filter (fun X => v ∉ X)).image (insert v))

lemma mem_maximal {H : Finset (Finset (Fin n))} {A X : Finset (Fin n)} :
    X ∈ maximal H A ↔ X ⊆ A ∧ miss H X ∧ ∀ i ∈ A \ X, ¬miss H (insert i X) := by
  simp [maximal, mem_filter]

lemma miss_mono {H J : Finset (Finset (Fin n))} {X : Finset (Fin n)}
    (hHJ : H ⊆ J) (h : miss J X) : miss H X :=
  fun e he => h e (hHJ he)

lemma not_miss_mono {H J : Finset (Finset (Fin n))} {X : Finset (Fin n)}
    (hHJ : H ⊆ J) (h : ¬miss H X) : ¬miss J X :=
  fun hJ => h (miss_mono hHJ hJ)

lemma exists_edge_of_not_miss {H : Finset (Finset (Fin n))} {X : Finset (Fin n)}
    (h : ¬miss H X) : ∃ e ∈ H, e ⊆ X := by
  simpa [miss, not_forall, not_imp] using h

lemma not_miss_of_subset {H : Finset (Finset (Fin n))} {X Y : Finset (Fin n)}
    (hXY : X ⊆ Y) (h : ¬miss H X) : ¬miss H Y := by
  obtain ⟨e, he, heX⟩ := exists_edge_of_not_miss h
  exact fun hY => hY e he (heX.trans hXY)

lemma not_miss_of_mem {H : Finset (Finset (Fin n))} {e : Finset (Fin n)}
    (he : e ∈ H) : ¬miss H e :=
  fun h => h e he subset_rfl

lemma miss_filter_iff {E : Finset (Finset (Fin n))} {v : Fin n} {X : Finset (Fin n)} :
    miss (E.filter (fun e => v ∉ e)) X ↔ miss E (X.erase v) := by
  constructor
  · intro h e he heX
    have hv : v ∉ e := fun hv => (mem_erase.1 (heX hv)).1 rfl
    exact h e (mem_filter.2 ⟨he, hv⟩) (heX.trans (erase_subset v X))
  · intro h e he heX
    rw [mem_filter] at he
    refine h e he.1 ?_
    intro x hx
    exact mem_erase.2 ⟨fun hxv => he.2 (hxv ▸ hx), heX hx⟩

lemma exists_maximal_containing (H : Finset (Finset (Fin n))) (A X : Finset (Fin n))
    (hXA : X ⊆ A) (hX : miss H X) :
    ∃ Y, X ⊆ Y ∧ Y ∈ maximal H A := by
  generalize hk : (A \ X).card = k
  revert X
  induction k with
  | zero =>
    intro X hXA hX hk
    refine ⟨X, subset_rfl, mem_maximal.2 ⟨hXA, hX, ?_⟩⟩
    intro i hi
    have : A \ X = ∅ := card_eq_zero.1 hk
    exact (notMem_empty i (this ▸ hi)).elim
  | succ k ih =>
    intro X hXA hX hk
    by_cases hmax : ∀ i ∈ A \ X, ¬miss H (insert i X)
    · exact ⟨X, subset_rfl, mem_maximal.2 ⟨hXA, hX, hmax⟩⟩
    · have hex : ∃ i ∈ A, i ∉ X ∧ miss H (insert i X) := by
        simpa [not_forall, not_imp, mem_sdiff] using hmax
      obtain ⟨i, hiA, hiX, hi⟩ := hex
      have hiAX : i ∈ A \ X := mem_sdiff.2 ⟨hiA, hiX⟩
      have hcard : (A \ insert i X).card = k := by
        rw [sdiff_insert, card_erase_of_mem hiAX, hk]
        rfl
      have hins : insert i X ⊆ A := insert_subset (mem_sdiff.1 hiAX).1 hXA
      obtain ⟨Y, hXY, hY⟩ := ih (insert i X) hins hi hcard
      exact ⟨Y, (subset_insert i X).trans hXY, hY⟩

lemma determined
    {C : Finset (Fin n) → Bool}
    (hmono : ∀ X Y : Finset (Fin n), X ⊆ Y → C X = true → C Y = true)
    {H : Finset (Finset (Fin n))}
    (h1 : ∀ e ∈ H, C e = true)
    (h0 : ∀ A ∈ maximal H univ, C A = false) :
    ∀ X, C X = !decide (miss H X) := by
  intro X
  by_cases hm : miss H X
  · obtain ⟨A, hXA, hA⟩ := exists_maximal_containing H univ X (subset_univ X) hm
    have hAf : C A = false := h0 A hA
    have hXf : C X = false := by
      by_cases hXt : C X = true
      · have := hmono X A hXA hXt
        simp [hAf] at this
      · exact Bool.eq_false_of_ne_true hXt
    simp [hm, hXf]
  · obtain ⟨e, he, heX⟩ := exists_edge_of_not_miss hm
    have hXt : C X = true := hmono e X heX (h1 e he)
    simp [hm, hXt]

lemma mem_maximal_filter {E : Finset (Finset (Fin n))} {v : Fin n} {X : Finset (Fin n)}
    (hX : X ∈ maximal (E.filter (fun e => v ∉ e)) univ) :
    (X ∈ maximal E univ ∧ v ∈ X) ∨
      ∃ Y ∈ maximal E univ, v ∉ Y ∧ X = insert v Y := by
  have hmem := mem_maximal.1 hX
  have hmiss := hmem.2.1
  have hmax := hmem.2.2
  have hvX : v ∈ X := by
    by_contra hvX
    have hnot := hmax v (by simp [hvX])
    have h1 : miss (E.filter (fun e => v ∉ e)) X ↔ miss E X := by
      simpa [erase_eq_of_notMem hvX] using
        (miss_filter_iff (E := E) (v := v) (X := X))
    have h2 : miss (E.filter (fun e => v ∉ e)) (insert v X) ↔ miss E X := by
      simpa [erase_insert hvX] using
        (miss_filter_iff (E := E) (v := v) (X := insert v X))
    exact hnot (h2.2 (h1.1 hmiss))
  set Y := X.erase v
  have hXY : X = insert v Y := (insert_erase hvX).symm
  have hYv : v ∉ Y := notMem_erase v X
  have hmissY : miss E Y := (miss_filter_iff (E := E) (v := v) (X := X)).1 hmiss
  by_cases hmX : miss E X
  · refine Or.inl ⟨mem_maximal.2 ⟨subset_univ X, hmX, ?_⟩, hvX⟩
    intro i hi
    have hnot := hmax i hi
    have hive : i ≠ v := fun hiv => by
      have : v ∈ univ \ X := by simpa [hiv] using hi
      simp [hvX] at this
    have hnotY : ¬miss E (insert i Y) := by
      have := (Iff.not (miss_filter_iff (E := E) (v := v) (X := insert i X))).1 hnot
      simpa [erase_insert_of_ne hive] using this
    have hsub : insert i Y ⊆ insert i X := by
      intro x hx
      rw [mem_insert] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl rfl
      · exact Or.inr (erase_subset v X hx)
    exact not_miss_of_subset hsub hnotY
  · refine Or.inr ⟨Y, mem_maximal.2 ⟨subset_univ Y, hmissY, ?_⟩, hYv, hXY⟩
    intro i hi
    have hiY : i ∉ Y := (mem_sdiff.1 hi).2
    by_cases hiv : i = v
    · subst hiv
      simpa [hXY] using hmX
    · have hiX : i ∉ X := fun hiX => hiY (mem_erase.2 ⟨hiv, hiX⟩)
      have hnot := hmax i (by simp [hiX])
      have := (Iff.not (miss_filter_iff (E := E) (v := v) (X := insert i X))).1 hnot
      simpa [erase_insert_of_ne hiv] using this

lemma insert_mem_maximal_filter {E : Finset (Finset (Fin n))} {v : Fin n} {Y : Finset (Fin n)}
    (hY : Y ∈ maximal E univ) (hvY : v ∉ Y) :
    insert v Y ∈ maximal (E.filter (fun e => v ∉ e)) univ := by
  have hYm := mem_maximal.1 hY
  refine mem_maximal.2 ⟨subset_univ _, ?_, ?_⟩
  · exact (miss_filter_iff (E := E) (v := v) (X := insert v Y)).2
      (by simpa [erase_insert hvY] using hYm.2.1)
  · intro i hi
    have hiins : i ∉ insert v Y := (mem_sdiff.1 hi).2
    have hiv : i ≠ v := fun hiv => hiins (by simp [hiv])
    have hiY : i ∉ Y := fun hiY => hiins (mem_insert.2 (Or.inr hiY))
    have hnot : ¬miss E (insert i Y) := hYm.2.2 i (by simp [hiY])
    exact (Iff.not (miss_filter_iff (E := E) (v := v)
      (X := insert i (insert v Y)))).2
      (by simpa [erase_insert_of_ne hiv, erase_insert hvY] using hnot)

lemma family_subset {E : Finset (Finset (Fin n))} {D : Finset (Fin n)}
    {H : Finset (Finset (Fin n))} (hH : H ∈ family E D) : H ⊆ E := by
  simp only [family, mem_insert, mem_image] at hH
  rcases hH with rfl | ⟨v, _, rfl⟩
  · exact subset_rfl
  · intro e he
    exact (mem_filter.1 he).1

lemma eq_of_card_two_subset {e q : Finset (Fin n)}
    (he : e.card = 2) (hq : q.card = 2) (h : e ⊆ q) : e = q :=
  eq_of_subset_of_card_le h (by omega)

noncomputable def flipC (E : Finset (Finset (Fin n))) (q : Finset (Fin n)) :
    Finset (Finset (Fin n)) → Finset (Fin n) → Bool :=
  fun H X =>
    if q ∈ E then
      (!decide (miss H X)) && decide (X ≠ q)
    else if X = q then
      decide (¬miss H q ∨ q ∈ maximal H univ)
    else
      !decide (miss H X)

lemma flipC_edge {E : Finset (Finset (Fin n))} {q : Finset (Fin n)}
    (hqE : q ∈ E) (H : Finset (Finset (Fin n))) (X : Finset (Fin n)) :
    flipC E q H X = ((!decide (miss H X)) && decide (X ≠ q)) := by
  simp [flipC, hqE]

lemma flipC_raise_eq {E : Finset (Finset (Fin n))} {q : Finset (Fin n)}
    (hqE : q ∉ E) (H : Finset (Finset (Fin n))) :
    flipC E q H q = decide (¬miss H q ∨ q ∈ maximal H univ) := by
  simp [flipC, hqE]

lemma flipC_raise_ne {E : Finset (Finset (Fin n))} {q : Finset (Fin n)}
    (hqE : q ∉ E) (H : Finset (Finset (Fin n))) {X : Finset (Fin n)}
    (hXq : X ≠ q) :
    flipC E q H X = !decide (miss H X) := by
  simp [flipC, hqE, hXq]

lemma flipC_mono {E : Finset (Finset (Fin n))} (hE : ∀ e ∈ E, e.card = 2)
    {D : Finset (Fin n)} {q : Finset (Fin n)} {H : Finset (Finset (Fin n))}
    (hH : H ∈ family E D) {X Y : Finset (Fin n)}
    (hXY : X ⊆ Y) (hCt : flipC E q H X = true) : flipC E q H Y = true := by
  have hHE : H ⊆ E := family_subset hH
  by_cases hqE : q ∈ E
  · rw [flipC_edge hqE H X, Bool.and_eq_true, decide_eq_true_eq] at hCt
    have hhit : ¬miss H X := by simpa using hCt.1
    have hXq : X ≠ q := hCt.2
    have hYq : Y ≠ q := by
      intro hYeq
      obtain ⟨e, he, heX⟩ := exists_edge_of_not_miss hhit
      have heq : e = q :=
        eq_of_card_two_subset (hE e (hHE he)) (hE q hqE) (heX.trans (hYeq ▸ hXY))
      have : X = q := Subset.antisymm (hYeq ▸ hXY) (by simpa [heq] using heX)
      exact hXq this
    have hhitY : ¬miss H Y := not_miss_of_subset hXY hhit
    simp [flipC_edge hqE H Y, hhitY, hYq]
  · by_cases hXq : X = q
    · rw [hXq] at hCt hXY
      have hCq : ¬miss H q ∨ q ∈ maximal H univ := by
        simpa [flipC_raise_eq hqE H] using hCt
      by_cases hYq : Y = q
      · rw [hYq]
        simpa [flipC_raise_eq hqE H] using hCt
      · have hhitY : ¬miss H Y := by
          rcases hCq with hhit | hmaxq
          · exact not_miss_of_subset hXY hhit
          · have hmq := mem_maximal.1 hmaxq
            have hss : q ⊂ Y := ssubset_of_subset_of_ne hXY (Ne.symm hYq)
            obtain ⟨i, hiY, hiq⟩ := exists_of_ssubset hss
            have hnot := hmq.2.2 i (by simp [hiq])
            exact not_miss_of_subset (insert_subset hiY hXY) hnot
        simp [flipC_raise_ne hqE H hYq, hhitY]
    · have hhit : ¬miss H X := by
        simpa [flipC_raise_ne hqE H hXq] using hCt
      have hhitY : ¬miss H Y := not_miss_of_subset hXY hhit
      by_cases hYq : Y = q
      · rw [hYq] at hhitY ⊢
        simp [flipC_raise_eq hqE H, hhitY]
      · simp [flipC_raise_ne hqE H hYq, hhitY]

lemma flipC_ord {E : Finset (Finset (Fin n))} {q : Finset (Fin n)}
    {H J : Finset (Finset (Fin n))} (hHJ : H ⊆ J) {X : Finset (Fin n)}
    (hCt : flipC E q H X = true) : flipC E q J X = true := by
  by_cases hqE : q ∈ E
  · rw [flipC_edge hqE H X, Bool.and_eq_true, decide_eq_true_eq] at hCt
    have hhitJ : ¬miss J X := not_miss_mono hHJ (by simpa using hCt.1)
    simp [flipC_edge hqE J X, hhitJ, hCt.2]
  · by_cases hXq : X = q
    · rw [hXq] at hCt ⊢
      have hCq : ¬miss H q ∨ q ∈ maximal H univ := by
        simpa [flipC_raise_eq hqE H] using hCt
      have hCJ : ¬miss J q ∨ q ∈ maximal J univ := by
        rcases hCq with hhit | hmax
        · exact Or.inl (not_miss_mono hHJ hhit)
        · by_cases hmJ : miss J q
          · exact Or.inr (mem_maximal.2 ⟨subset_univ q, hmJ, fun i hi =>
              not_miss_mono hHJ ((mem_maximal.1 hmax).2.2 i hi)⟩)
          · exact Or.inl hmJ
      simpa [flipC_raise_eq hqE J] using hCJ
    · have hhit : ¬miss H X := by
        simpa [flipC_raise_ne hqE H hXq] using hCt
      simp [flipC_raise_ne hqE J hXq, not_miss_mono hHJ hhit]

lemma mem_bank {E : Finset (Finset (Fin n))} {D : Finset (Fin n)} {q : Finset (Fin n)}
    (hq : q ∈ bank E D) (hqE : q ∉ E) :
    q ∈ maximal E univ ∨
      ∃ v ∈ D, ∃ Y ∈ maximal E univ, v ∉ Y ∧ q = insert v Y := by
  simp only [bank, mem_union, mem_biUnion, mem_filter, mem_image] at hq
  rcases hq with (hE' | hbase) | hex
  · exact (hqE hE').elim
  · exact Or.inl hbase
  · obtain ⟨v, hv, X, ⟨hXbase, hvX⟩, rfl⟩ := hex
    exact Or.inr ⟨v, hv, X, hXbase, hvX, rfl⟩

lemma main (E : Finset (Finset (Fin n))) (hE : ∀ e ∈ E, e.card = 2)
    (D : Finset (Fin n)) (ord : Bool) (Q : Finset (Finset (Fin n))) :
    (∀ C : Finset (Finset (Fin n)) → Finset (Fin n) → Bool,
      (∀ H ∈ family E D, ∀ X Y : Finset (Fin n), X ⊆ Y → C H X = true → C H Y = true) →
      (ord = true → ∀ H ∈ family E D, ∀ J ∈ family E D, H ⊆ J →
        ∀ X, C H X = true → C J X = true) →
      (∀ H ∈ family E D, ∀ X ∈ Q, C H X = !decide (miss H X)) →
      ∀ H ∈ family E D, ∀ X, C H X = !decide (miss H X)) ↔
    bank E D ⊆ Q := by
  constructor
  · intro hdet q hqbank
    by_contra hqQ
    have hmono : ∀ H ∈ family E D, ∀ X Y : Finset (Fin n),
        X ⊆ Y → flipC E q H X = true → flipC E q H Y = true :=
      fun H hH X Y hXY hC => flipC_mono hE hH hXY hC
    have hordC : ord = true → ∀ H ∈ family E D, ∀ J ∈ family E D,
        H ⊆ J → ∀ X, flipC E q H X = true → flipC E q J X = true :=
      fun _ H _ J _ hHJ X hC => flipC_ord hHJ hC
    have hagree : ∀ H ∈ family E D, ∀ X ∈ Q,
        flipC E q H X = !decide (miss H X) := by
      intro H _ X hXQ
      have hXq : X ≠ q := fun h => hqQ (h ▸ hXQ)
      by_cases hqE : q ∈ E
      · simp [flipC_edge hqE H X, hXq]
      · simp [flipC_raise_ne hqE H hXq]
    have hCeq := hdet (flipC E q) hmono hordC hagree
    have hEfam : E ∈ family E D := mem_insert_self _ _
    by_cases hqE : q ∈ E
    · have hCq := hCeq E hEfam q
      have hfalse : flipC E q E q = false := by simp [flipC_edge hqE E q]
      have htrue : (!decide (miss E q)) = true := by
        simp [not_miss_of_mem hqE]
      simp [hfalse, htrue] at hCq
    · rcases mem_bank hqbank hqE with hbase | ⟨v, hv, Y, hY, hvY, rfl⟩
      · have hCq := hCeq E hEfam q
        have htrue : flipC E q E q = true := by
          simpa [flipC_raise_eq hqE E] using Or.inr hbase
        have hfalse : (!decide (miss E q)) = false := by
          have hm : miss E q := (mem_maximal.1 hbase).2.1
          simp [hm]
        simp [htrue, hfalse] at hCq
      · have hH : E.filter (fun e => v ∉ e) ∈ family E D :=
          mem_insert_of_mem (mem_image.2 ⟨v, hv, rfl⟩)
        have hCq := hCeq _ hH (insert v Y)
        have hmax : insert v Y ∈ maximal (E.filter (fun e => v ∉ e)) univ :=
          insert_mem_maximal_filter hY hvY
        have htrue :
            flipC E (insert v Y) (E.filter (fun e => v ∉ e)) (insert v Y) = true := by
          simpa [flipC_raise_eq hqE] using Or.inr hmax
        have hfalse :
            (!decide (miss (E.filter (fun e => v ∉ e)) (insert v Y))) = false := by
          have hm : miss (E.filter (fun e => v ∉ e)) (insert v Y) :=
            (mem_maximal.1 hmax).2.1
          simp [hm]
        simp [htrue, hfalse] at hCq
  · intro hbank C hmono _ hagree H hH X
    refine determined (C := C H) (fun A B hAB hC => hmono H hH A B hAB hC) ?h1 ?h0 X
    · intro e he
      have heE : e ∈ E := family_subset hH he
      have heQ : e ∈ Q := hbank (by
        simp only [bank, mem_union]
        exact Or.inl (Or.inl heE))
      have hCe := hagree H hH e heQ
      have : ¬miss H e := not_miss_of_mem he
      simpa [this] using hCe
    · intro A hA
      have hAQ : A ∈ Q := by
        simp only [family, mem_insert, mem_image] at hH
        rcases hH with rfl | ⟨v, hv, rfl⟩
        · exact hbank (by
            simp only [bank, mem_union]
            exact Or.inl (Or.inr hA))
        · rcases mem_maximal_filter hA with ⟨hbase, _⟩ | ⟨Y, hY, hvY, rfl⟩
          · exact hbank (by
              simp only [bank, mem_union]
              exact Or.inl (Or.inr hbase))
          · exact hbank (by
              simp only [bank, mem_union, mem_biUnion, mem_filter, mem_image]
              exact Or.inr ⟨v, hv, Y, ⟨hY, hvY⟩, rfl⟩)
      have hCA := hagree H hH A hAQ
      have hm : miss H A := (mem_maximal.1 hA).2.1
      simpa [hm] using hCA

end PEqualNP.Outside.L_lib_1119

open PEqualNP.Outside.L_lib_1119
open Finset
open Classical

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_lib_1119 : ∀ (n : Nat) (E : Finset (Finset (Fin n))), (∀ e ∈ E, e.card = 2) →
  let sets := (Finset.univ : Finset (Finset (Fin n)))
  let miss := fun (H : Finset (Finset (Fin n))) (X : Finset (Fin n)) => ∀ e ∈ H, ¬e ⊆ X
  let maximal := fun (H : Finset (Finset (Fin n))) (A : Finset (Fin n)) =>
    sets.filter (fun X => X ⊆ A ∧ miss H X ∧ ∀ i ∈ A \ X, ¬miss H (insert i X))
  let base := maximal E Finset.univ
  ∀ D : Finset (Fin n),
  let family := insert E (D.image (fun v => E.filter (fun e => v ∉ e)))
  let bank := E ∪ base ∪ D.biUnion (fun v => (base.filter (fun X => v ∉ X)).image (insert v))
  let determines := fun (ord : Bool) (Q : Finset (Finset (Fin n))) =>
    ∀ C : Finset (Finset (Fin n)) → Finset (Fin n) → Bool,
      (∀ H ∈ family, ∀ X Y : Finset (Fin n), X ⊆ Y → C H X = true → C H Y = true) →
      (ord = true → ∀ H ∈ family, ∀ J ∈ family, H ⊆ J → ∀ X, C H X = true → C J X = true) →
      (∀ H ∈ family, ∀ X ∈ Q, C H X = !decide (miss H X)) →
      ∀ H ∈ family, ∀ X, C H X = !decide (miss H X)
  ∀ ord Q, determines ord Q ↔ bank ⊆ Q := by
  intro n E hE sets miss maximal base D family bank determines ord Q
  have hf : family = L_lib_1119.family E D := rfl
  have hm : miss = L_lib_1119.miss := rfl
  have hM : maximal = L_lib_1119.maximal := by
    funext H A
    simp [maximal, L_lib_1119.maximal, sets, hm]
  have hb : bank = L_lib_1119.bank E D := by
    simp [bank, L_lib_1119.bank, base, hM]
  unfold determines
  simp [hf, hm, hb]
  exact main (n := n) E hE D ord Q
