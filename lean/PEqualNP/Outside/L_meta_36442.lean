import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36442_aux

theorem pair_eq {n : Nat} {e : Finset (Fin n)} (he : e.card = 2) {a b : Fin n}
    (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b) : e = {a, b} := by
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · rw [he, Finset.card_pair hab]

theorem other {n : Nat} {e : Finset (Fin n)} (he : e.card = 2) (c : Fin n) :
    ∃ j ∈ e, j ≠ c := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he
  by_cases h : a = c
  · exact ⟨b, by simp, fun h' => hab (h.trans h'.symm)⟩
  · exact ⟨a, by simp, h⟩

end PEqualNP.Outside.L_meta_36442_aux

open PEqualNP.Outside.L_meta_36442_aux in
theorem PEqualNP.Outside.L_meta_36442 : ∀ (n : Nat) (E : Finset (Finset (Fin n))) (C S : Finset (Fin n)),
  (∀ e ∈ E, e.card = 2) → S.Nonempty →
  let cover := fun (K : Finset (Fin n)) => ∀ e ∈ E, ∃ v ∈ e, v ∈ K
  cover C → (∀ v ∈ C, ¬cover (C.erase v)) →
  let N := fun (y : Fin n) =>
    (Finset.univ : Finset (Fin n)).filter (fun j => j ≠ y ∧ ({y, j} : Finset (Fin n)) ∈ E)
  let old := fun (X : Finset (Fin n)) => ∃ e ∈ E, e ⊆ X
  ∀ y : Fin n,
    (∃ (center : Finset (Fin n) → Fin n) (useCenter : Bool) (useLeaf : Fin n → Bool),
      (∀ e ∈ E, center e ∈ e ∧ center e ∈ C) ∧
      ∀ (X : Finset (Fin n)) (z : Bool),
        ((∃ e ∈ E,
          (center e ∈ X ∨ (z = true ∧ center e = y ∧ useCenter = true)) ∧
          ∃ j ∈ e, j ≠ center e ∧
            (j ∈ X ∨ (z = true ∧ j = y ∧ useLeaf (center e) = true))) ↔
         old X ∨ (z = true ∧ ∃ i ∈ S, i ∈ X))) ↔
    S ⊆ N y ∧ (y ∉ C ∨ Disjoint S (N y \ C) ∨ N y \ C ⊆ S) := by
  intro n E C S hE _hS
  dsimp only
  intro hC _hmin y
  classical
  set N := (Finset.univ : Finset (Fin n)).filter
    (fun j => j ≠ y ∧ ({y, j} : Finset (Fin n)) ∈ E) with hNdef
  have hN : ∀ j, j ∈ N ↔ j ≠ y ∧ ({y, j} : Finset (Fin n)) ∈ E := by
    intro j; simp [hNdef]
  constructor
  · rintro ⟨center, uC, uL, hcen, hiff⟩
    have key : ∀ i ∈ S, ∃ e ∈ E, (center e = i ∨ (center e = y ∧ uC = true)) ∧
        ∃ j ∈ e, j ≠ center e ∧ (j = i ∨ (j = y ∧ uL (center e) = true)) := by
      intro i hi
      obtain ⟨e, he, h1, j, hj, hjc, h2⟩ := (hiff {i} true).mpr (Or.inr ⟨rfl, i, hi, by simp⟩)
      refine ⟨e, he, ?_, j, hj, hjc, ?_⟩
      · rcases h1 with h | ⟨-, h, h'⟩
        · exact Or.inl (by simpa using h)
        · exact Or.inr ⟨h, h'⟩
      · rcases h2 with h | ⟨-, h, h'⟩
        · exact Or.inl (by simpa using h)
        · exact Or.inr ⟨h, h'⟩
    have hsub : S ⊆ N := by
      intro i hi
      obtain ⟨e, he, h1, j, hj, hjc, h2⟩ := key i hi
      rw [hN]
      rcases h1 with h1 | ⟨h1, -⟩ <;> rcases h2 with h2 | ⟨h2, -⟩
      · exact absurd (h2.trans h1.symm) hjc
      · have hh := pair_eq (hE e he) hj (hcen e he).1 hjc
        rw [h2, h1] at hh
        refine ⟨fun h => hjc (by rw [h2, h1, h]), ?_⟩
        rw [← hh]; exact he
      · have hh := pair_eq (hE e he) (hcen e he).1 hj (Ne.symm hjc)
        rw [h2, h1] at hh
        refine ⟨fun h => hjc (by rw [h2, h1, h]), ?_⟩
        rw [← hh]; exact he
      · exact absurd (h2.trans h1.symm) hjc
    refine ⟨hsub, ?_⟩
    by_cases hy : y ∈ C
    · right
      cases uC
      · left
        rw [Finset.disjoint_left]
        intro i hiS hiN
        rw [Finset.mem_sdiff] at hiN
        obtain ⟨e, he, h1, j, hj, hjc, h2⟩ := key i hiS
        rcases h1 with h1 | ⟨-, h1⟩
        · exact hiN.2 (h1 ▸ (hcen e he).2)
        · cases h1
      · right
        intro j hj
        rw [Finset.mem_sdiff, hN] at hj
        obtain ⟨⟨hjy, hyj⟩, hjC⟩ := hj
        have hc := hcen _ hyj
        have hcy : center {y, j} = y := by
          have hm : center {y, j} ∈ ({y, j} : Finset (Fin n)) := hc.1
          simp only [Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with h | h
          · exact h
          · exact absurd (h ▸ hc.2) hjC
        have := (hiff {j} true).mp ⟨{y, j}, hyj, Or.inr ⟨rfl, hcy, rfl⟩, j, by simp,
          by rw [hcy]; exact hjy, Or.inl (by simp)⟩
        rcases this with ⟨e, he, hsub'⟩ | ⟨-, i, hi, hiX⟩
        · exfalso
          have := Finset.card_le_card hsub'
          rw [hE e he] at this; simp at this
        · rw [Finset.mem_singleton] at hiX; exact hiX ▸ hi
    · exact Or.inl hy
  · rintro ⟨hsub, hcase⟩
    obtain ⟨uC, huC⟩ : ∃ b : Bool, (b = true ↔ (y ∈ C ∧ N \ C ⊆ S)) :=
      ⟨decide (y ∈ C ∧ N \ C ⊆ S), by simp⟩
    obtain ⟨P, hP⟩ : ∃ P : Finset (Fin n) → Prop, ∀ e, P e ↔
        (y ∈ e ∧ y ∈ C ∧ ∀ j ∈ e, j ≠ y → (j ∉ C ∨ (uC = true ∧ j ∈ S))) :=
      ⟨_, fun _ => Iff.rfl⟩
    obtain ⟨center, hc1, hc2⟩ : ∃ f : Finset (Fin n) → Fin n,
        (∀ e, (¬P e ∧ ∃ v ∈ e, v ∈ C ∧ v ≠ y) → f e ∈ e ∧ f e ∈ C ∧ f e ≠ y) ∧
        (∀ e, ¬(¬P e ∧ ∃ v ∈ e, v ∈ C ∧ v ≠ y) → f e = y) := by
      refine ⟨fun e => if h : ¬P e ∧ ∃ v ∈ e, v ∈ C ∧ v ≠ y then Classical.choose h.2 else y,
        ?_, ?_⟩
      · intro e h; dsimp only; rw [dif_pos h]; exact Classical.choose_spec h.2
      · intro e h; dsimp only; rw [dif_neg h]
    obtain ⟨uL, huL⟩ : ∃ g : Fin n → Bool, ∀ c, g c = true ↔ (uC = false ∧ c ∈ S) :=
      ⟨fun c => (!uC) && decide (c ∈ S), by intro c; cases uC <;> simp⟩
    have Ex : ∀ e ∈ E, ¬P e → ∃ v ∈ e, v ∈ C ∧ v ≠ y := by
      intro e he hp
      obtain ⟨v, hve, hvC⟩ := hC e he
      by_cases hv : v = y
      · by_contra hno
        apply hp
        rw [hP]
        refine ⟨by rw [← hv]; exact hve, by rw [← hv]; exact hvC, fun j hj hjy => ?_⟩
        by_cases hjC : j ∈ C
        · exact absurd ⟨j, hj, hjC, hjy⟩ hno
        · exact Or.inl hjC
      · exact ⟨v, hve, hvC, hv⟩
    have F1 : ∀ e ∈ E, center e ∈ e ∧ center e ∈ C := by
      intro e he
      by_cases h : (¬P e ∧ ∃ v ∈ e, v ∈ C ∧ v ≠ y)
      · exact ⟨(hc1 e h).1, (hc1 e h).2.1⟩
      · rw [hc2 e h]
        by_cases hp : P e
        · exact ⟨((hP e).1 hp).1, ((hP e).1 hp).2.1⟩
        · exact absurd ⟨hp, Ex e he hp⟩ h
    have Fa : ∀ e ∈ E, center e = y → P e := by
      intro e he hce
      by_contra hp
      exact (hc1 e ⟨hp, Ex e he hp⟩).2.2 hce
    refine ⟨center, uC, uL, F1, ?_⟩
    intro X z
    constructor
    · rintro ⟨e, he, h1, j, hj, hjc, h2⟩
      have hee : e = {j, center e} := pair_eq (hE e he) hj (F1 e he).1 hjc
      rcases h1 with h1 | ⟨hz, h1, hu⟩ <;> rcases h2 with h2 | ⟨hz', h2, hl⟩
      · left
        refine ⟨e, he, ?_⟩
        rw [hee, Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨h2, h1⟩
      · right
        exact ⟨hz', center e, ((huL _).1 hl).2, h1⟩
      · right
        refine ⟨hz, j, ?_, h2⟩
        have hp := (hP e).1 (Fa e he h1)
        have hjy : j ≠ y := by rw [← h1]; exact hjc
        rcases hp.2.2 j hj hjy with hjC | ⟨-, hjS⟩
        · apply (huC.1 hu).2
          rw [Finset.mem_sdiff, hN]
          refine ⟨⟨hjy, ?_⟩, hjC⟩
          rw [Finset.pair_comm, ← h1, ← hee]; exact he
        · exact hjS
      · exact absurd (h2.trans h1.symm) hjc
    · rintro (⟨e, he, hsX⟩ | ⟨hz, i, hi, hiX⟩)
      · obtain ⟨j, hj, hjc⟩ := other (hE e he) (center e)
        exact ⟨e, he, Or.inl (hsX (F1 e he).1), j, hj, hjc, Or.inl (hsX hj)⟩
      · obtain ⟨hiy, hyi⟩ := (hN i).1 (hsub hi)
        by_cases huc : uC = true
        · obtain ⟨hyC, -⟩ := huC.1 huc
          have hp : P {y, i} := by
            rw [hP]
            refine ⟨by simp, hyC, fun j hj hjy => ?_⟩
            simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            rcases hj with hj | hj
            · exact absurd hj hjy
            · exact Or.inr ⟨huc, hj ▸ hi⟩
          have hcy : center {y, i} = y := hc2 _ (fun h => h.1 hp)
          exact ⟨{y, i}, hyi, Or.inr ⟨hz, hcy, huc⟩, i, by simp, by rw [hcy]; exact hiy,
            Or.inl hiX⟩
        · have huc' : uC = false := by simpa using huc
          have hiC : i ∈ C := by
            by_contra hiC
            by_cases hyC : y ∈ C
            · rcases hcase with h | h | h
              · exact h hyC
              · exact Finset.disjoint_left.1 h hi (Finset.mem_sdiff.2 ⟨hsub hi, hiC⟩)
              · exact huc (huC.2 ⟨hyC, h⟩)
            · obtain ⟨v, hv, hvC⟩ := hC _ hyi
              simp only [Finset.mem_insert, Finset.mem_singleton] at hv
              rcases hv with hv | hv
              · exact hyC (hv ▸ hvC)
              · exact hiC (hv ▸ hvC)
          have hnp : ¬P {y, i} := by
            rw [hP]
            rintro ⟨-, -, h⟩
            rcases h i (by simp) hiy with h' | ⟨h', -⟩
            · exact h' hiC
            · exact huc h'
          have hm := hc1 _ ⟨hnp, i, by simp, hiC, hiy⟩
          have hce : center {y, i} = i := by
            have hm1 := hm.1
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm1
            rcases hm1 with h | h
            · exact absurd h hm.2.2
            · exact h
          exact ⟨{y, i}, hyi, Or.inl (by rw [hce]; exact hiX), y, by simp,
            Ne.symm hm.2.2, Or.inr ⟨hz, rfl, (huL _).2 ⟨huc', by rw [hce]; exact hi⟩⟩⟩
