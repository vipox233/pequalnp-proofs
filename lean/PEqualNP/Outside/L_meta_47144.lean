import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47144_aux

variable {n : Nat} [DecidableEq (Fin n)] (edge : Fin n → Fin n → Bool)

def indep (s : Finset (Fin n)) : Prop := ∀ i ∈ s, ∀ j ∈ s, edge i j = false

noncomputable def alpha (x : Finset (Fin n)) : Nat :=
  (@Finset.filter _ (indep edge) (fun _ => Classical.propDecidable _) x.powerset).sup Finset.card

def pack (f : Finset (Fin n) → Fin n → Bool) : Nat → Finset (Fin n) → Prop :=
  Nat.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
    (fun _ prev x => ∃ (u v : Finset (Fin n)) (j : Fin n), prev u ∧ u ⊆ v ∧ v ⊆ x ∧
      f u j = true ∧ f v j = false)

open Classical in
theorem le_alpha {s x : Finset (Fin n)} (h : s ⊆ x) (hs : indep edge s) :
    s.card ≤ alpha edge x :=
  Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 h, hs⟩)

open Classical in
theorem exists_alpha (x : Finset (Fin n)) :
    ∃ s, s ⊆ x ∧ indep edge s ∧ s.card = alpha edge x := by
  obtain ⟨s, hs, h⟩ := Finset.exists_mem_eq_sup
    (@Finset.filter _ (indep edge) (fun a => Classical.propDecidable _) x.powerset)
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset x, fun i hi => by simp at hi⟩⟩ Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hs
  exact ⟨s, hs.1, hs.2, h.symm⟩

theorem indep_mono {s t : Finset (Fin n)} (h : s ⊆ t) (ht : indep edge t) : indep edge s :=
  fun i hi j hj => ht i (h hi) j (h hj)

theorem alpha_mono {x y : Finset (Fin n)} (h : x ⊆ y) : alpha edge x ≤ alpha edge y := by
  obtain ⟨s, hs, hi, hc⟩ := exists_alpha edge x
  rw [← hc]
  exact le_alpha edge (hs.trans h) hi

theorem alpha_insert_le (x : Finset (Fin n)) (j : Fin n) :
    alpha edge (insert j x) ≤ alpha edge x + 1 := by
  obtain ⟨s, hs, hi, hc⟩ := exists_alpha edge (insert j x)
  have h1 := le_alpha edge (Finset.subset_insert_iff.1 hs)
    (indep_mono edge (Finset.erase_subset j s) hi)
  have h2 := Finset.pred_card_le_card_erase (s := s) (a := j)
  omega

variable (f : Finset (Fin n) → Fin n → Bool)
  (hf1 : ∀ x j, (j ∉ x ∧ ∀ i ∈ x, edge i j = false) → f x j = true)
  (hf2 : ∀ x j, j ∈ x → f x j = false)

include hf1 hf2 in
theorem packL : ∀ (l : Nat) (x : Finset (Fin n)), l ≤ alpha edge x → pack f l x := by
  intro l
  induction l with
  | zero => intro x _; trivial
  | succ k ih =>
    intro x h
    obtain ⟨S, hSx, hSi, hSc⟩ := exists_alpha edge x
    have hpos : 0 < S.card := by omega
    obtain ⟨j, hj⟩ := Finset.card_pos.1 hpos
    have h1 := le_alpha edge (Finset.Subset.refl (S.erase j))
      (indep_mono edge (Finset.erase_subset j S) hSi)
    have h2 := Finset.card_erase_of_mem hj
    refine ⟨S.erase j, x, j, ih _ (by omega), (Finset.erase_subset j S).trans hSx,
      Finset.Subset.refl x, hf1 _ _ ⟨Finset.notMem_erase j S, fun i hi => ?_⟩, hf2 _ _ (hSx hj)⟩
    exact hSi i (Finset.mem_of_mem_erase hi) j hj

theorem packU (hg : ∀ x j, f x j = true ↔ alpha edge (insert j x) = alpha edge x + 1) :
    ∀ (l : Nat) (x : Finset (Fin n)), pack f l x → l ≤ alpha edge x := by
  intro l
  induction l with
  | zero => intro x _; exact Nat.zero_le _
  | succ k ih =>
    rintro x ⟨u, v, j, hu, huv, hvx, fu, fv⟩
    have h1 := ih u hu
    have gu := (hg u j).1 fu
    have ngv : ¬ alpha edge (insert j v) = alpha edge v + 1 := fun h => by
      rw [(hg v j).2 h] at fv; cases fv
    have m1 := alpha_mono edge huv
    have m2 := alpha_mono edge hvx
    have m3 := alpha_mono edge (Finset.insert_subset_insert j huv)
    have m4 := alpha_insert_le edge v j
    omega

include hf1 hf2 in
theorem conj2 (x : Finset (Fin n)) (j : Fin n) (hfx : f x j = false)
    (hg : alpha edge (insert j x) = alpha edge x + 1) : pack f (alpha edge x + 1) x := by
  obtain ⟨T, hT, hTi, hTc⟩ := exists_alpha edge (insert j x)
  have hjT : j ∈ T := by
    by_contra h
    have := le_alpha edge ((Finset.subset_insert_iff_of_notMem h).1 hT) hTi
    omega
  have hu : indep edge (T.erase j) := indep_mono edge (Finset.erase_subset j T) hTi
  have h1 := le_alpha edge (Finset.Subset.refl (T.erase j)) hu
  have h2 := Finset.card_erase_of_mem hjT
  refine ⟨T.erase j, x, j, packL edge f hf1 hf2 _ _ (by omega), Finset.subset_insert_iff.1 hT,
    Finset.Subset.refl x, hf1 _ _ ⟨Finset.notMem_erase j T, fun i hi => ?_⟩, hfx⟩
  exact hTi i (Finset.mem_of_mem_erase hi) j hjT

include hf1 hf2 in
theorem conj3 (x : Finset (Fin n)) (j : Fin n) (hfx : f x j = true)
    (hg : ¬ alpha edge (insert j x) = alpha edge x + 1) :
    pack f (alpha edge (insert j x) + 1) (insert j x) := by
  have m1 := alpha_mono edge (Finset.subset_insert j x)
  have m2 := alpha_insert_le edge x j
  exact ⟨x, insert j x, j, packL edge f hf1 hf2 _ _ (by omega), Finset.subset_insert j x,
    Finset.Subset.refl _, hfx, hf2 _ _ (Finset.mem_insert_self j x)⟩

include hf1 hf2 in
theorem main :
    ((∀ x l, pack f l x ↔ l ≤ alpha edge x) ↔
      ∀ x j, f x j = true ↔ alpha edge (insert j x) = alpha edge x + 1) ∧
    (∀ x j, f x j = false → alpha edge (insert j x) = alpha edge x + 1 →
      pack f (alpha edge x + 1) x) ∧
    (∀ x j, f x j = true → ¬ alpha edge (insert j x) = alpha edge x + 1 →
      pack f (alpha edge (insert j x) + 1) (insert j x)) := by
  refine ⟨⟨fun h x j => ⟨fun hfx => ?_, fun hg => ?_⟩, fun hg x l =>
    ⟨packU edge f hg l x, packL edge f hf1 hf2 l x⟩⟩, conj2 edge f hf1 hf2, conj3 edge f hf1 hf2⟩
  · by_contra hg
    have := (h _ _).1 (conj3 edge f hf1 hf2 x j hfx hg)
    omega
  · by_contra hfx
    have := (h _ _).1 (conj2 edge f hf1 hf2 x j (by simpa using hfx) hg)
    omega

end PEqualNP.Outside.L_meta_47144_aux

theorem PEqualNP.Outside.L_meta_47144 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n : Nat) (edge : Fin n → Fin n → Bool),
  (∀ i, edge i i = false) → (∀ i j, edge i j = edge j i) →
  let X := Finset (Fin n)
  let independent := fun (s : X) => ∀ i ∈ s, ∀ j ∈ s, edge i j = false
  let alpha := fun (x : X) => (x.powerset.filter independent).sup Finset.card
  let gain := fun (x : X) (j : Fin n) => alpha (insert j x) = alpha x + 1
  ∀ (f : X → Fin n → Bool),
    (∀ x j, (j ∉ x ∧ ∀ i ∈ x, edge i j = false) → f x j = true) →
    (∀ x j, j ∈ x → f x j = false) →
    let pack := Nat.rec (motive := fun _ => X → Prop) (fun _ => True)
      (fun _ prev x => ∃ (u v : X) (j : Fin n), prev u ∧ u ⊆ v ∧ v ⊆ x ∧
        f u j = true ∧ f v j = false)
    ((∀ x l, pack l x ↔ l ≤ alpha x) ↔
      ∀ x j, f x j = true ↔ gain x j) ∧
    (∀ x j, f x j = false → gain x j → pack (alpha x + 1) x) ∧
    (∀ x j, f x j = true → ¬ gain x j →
      pack (alpha (insert j x) + 1) (insert j x))) := by
  intros
  exact @PEqualNP.Outside.L_meta_47144_aux.main _ (fun a b => Classical.propDecidable _) _ _ ‹_› ‹_›
