import PEqualNP.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic

namespace PEqualNP.Outside.L_lib_884.TwoHubs

def Hit {α : Type*} [DecidableEq α] (P : Equiv.Perm α) (S : Finset α) : Prop :=
  ∃ u ∈ S, P u ∈ S ∧ P u ≠ u

theorem swap_of_involutive {α : Type*} (P : Equiv.Perm α)
    (hP : Function.Involutive P) {a b : α} (h : P a = b) : P b = a := by
  rw [← h, hP]

theorem hit_triangle {α : Type*} [DecidableEq α] (P : Equiv.Perm α)
    (hP : Function.Involutive P) (a b c : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Hit P {a,b,c} ↔ P a = b ∨ P a = c ∨ P b = c := by
  constructor
  · rintro ⟨u, hu, hv, hn⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl
    · rcases hv with h | h | h
      · exact False.elim (hn h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases hv with h | h | h
      · exact Or.inl (swap_of_involutive P hP h)
      · exact False.elim (hn h)
      · exact Or.inr (Or.inr h)
    · rcases hv with h | h | h
      · exact Or.inr (Or.inl (swap_of_involutive P hP h))
      · exact Or.inr (Or.inr (swap_of_involutive P hP h))
      · exact False.elim (hn h)
  · rintro (h | h | h)
    · refine ⟨a, by simp, ?_, ?_⟩
      · rw [h]; simp
      · rw [h]; exact hab.symm
    · refine ⟨a, by simp, ?_, ?_⟩
      · rw [h]; simp
      · rw [h]; exact hac.symm
    · refine ⟨b, by simp, ?_, ?_⟩
      · rw [h]; simp
      · rw [h]; exact hbc.symm

variable {q k : ℕ} (name : (Option (Fin q) × Bool) ↪ Fin k)

def Hub (b : Bool) : Fin k := name (none,b)
def Leaf (c : Fin q) (b : Bool) : Fin k := name (some c,b)
def Star (b : Bool) : Finset (Fin k) :=
  insert (Hub name b) (Finset.univ.image (fun c : Fin q => Leaf name c b))

theorem hub_ne_leaf (a b : Bool) (c : Fin q) : Hub name a ≠ Leaf name c b := by
  simp [Hub, Leaf, name.injective.eq_iff]

theorem hub_injective : Function.Injective (Hub name) := by
  intro a b h
  exact (Prod.mk.inj (name.injective h)).2

theorem leaf_eq_iff (c d : Fin q) (a b : Bool) :
    Leaf name c a = Leaf name d b ↔ c = d ∧ a = b := by
  simp [Leaf, name.injective.eq_iff]

theorem leaf_ne_opposite (c d : Fin q) : Leaf name c false ≠ Leaf name d true := by
  simp [leaf_eq_iff]

theorem leaf_mem_star (c : Fin q) (a b : Bool) :
    Leaf name c a ∈ Star name b ↔ a = b := by
  simp [Star, (hub_ne_leaf name b a c).symm, leaf_eq_iff, eq_comm]

theorem hub_mem_star (a b : Bool) : Hub name a ∈ Star name b ↔ a = b := by
  simp [Star, Hub, Leaf, name.injective.eq_iff]

def Chosen (P : Equiv.Perm (Fin k)) (c : Fin q) : Prop :=
  (∀ b, P (Hub name b) = Leaf name c b) ∧
  ∀ j, j ≠ c → P (Leaf name j false) = Leaf name j true

theorem triangle_iff (P : Equiv.Perm (Fin k)) (hP : Function.Involutive P)
    (c : Fin q) (b : Bool) :
    Hit P {Hub name b, Leaf name c false, Leaf name c true} ↔
      P (Hub name b) = Leaf name c false ∨
      P (Hub name b) = Leaf name c true ∨
      P (Leaf name c false) = Leaf name c true :=
  hit_triangle P hP _ _ _ (hub_ne_leaf name _ _ _) (hub_ne_leaf name _ _ _)
    (leaf_ne_opposite name _ _)

theorem leaf_outside_triangle (P : Equiv.Perm (Fin k)) (hP : Function.Involutive P)
    (c : Fin q) (b : Bool) (v : Fin k)
    (ht : Hit P {Hub name b, Leaf name c false, Leaf name c true})
    (hv : P (Leaf name c false) = v) (hvh : v ≠ Hub name b)
    (hvl : v ≠ Leaf name c true) : P (Hub name b) = Leaf name c true := by
  rcases (triangle_iff name P hP c b).1 ht with h | h | h
  · have he := swap_of_involutive P hP h
    exact False.elim (hvh (hv.symm.trans he))
  · exact h
  · exact False.elim (hvl (hv.symm.trans h))

theorem star_forces_hub (P : Equiv.Perm (Fin k)) (hP : Function.Involutive P)
    (ht : ∀ c b, Hit P {Hub name b, Leaf name c false, Leaf name c true})
    (hs : Hit P (Star name false)) : ∃ c, P (Hub name false) = Leaf name c false := by
  obtain ⟨u, hu, hpu, hne⟩ := hs
  simp only [Star, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hu hpu
  rcases hu with rfl | ⟨c, rfl⟩
  · rcases hpu with he | ⟨c, hc⟩
    · exact False.elim (hne he)
    · exact ⟨c, hc.symm⟩
  · rcases hpu with he | ⟨d, hd⟩
    · exact ⟨c, swap_of_involutive P hP he⟩
    · have hf := leaf_outside_triangle name P hP c false (Leaf name d false)
        (ht c false) hd.symm (hub_ne_leaf name false false d).symm
        (leaf_ne_opposite name d c)
      have ht' := leaf_outside_triangle name P hP c true (Leaf name d false)
        (ht c true) hd.symm (hub_ne_leaf name true false d).symm
        (leaf_ne_opposite name d c)
      have bad : false = true := hub_injective name (P.injective (hf.trans ht'.symm))
      cases bad

theorem chosen_of_hub (P : Equiv.Perm (Fin k)) (hP : Function.Involutive P)
    (ht : ∀ c b, Hit P {Hub name b, Leaf name c false, Leaf name c true})
    (c : Fin q) (hc : P (Hub name false) = Leaf name c false) : Chosen name P c := by
  have hlc : P (Leaf name c false) = Hub name false := swap_of_involutive P hP hc
  have htc : P (Hub name true) = Leaf name c true := by
    apply leaf_outside_triangle name P hP c true (Hub name false) (ht c true) hlc
    · intro h
      have : false = true := hub_injective name h
      cases this
    · exact hub_ne_leaf name false true c
  constructor
  · intro b
    cases b
    · exact hc
    · exact htc
  · intro j hj
    rcases (triangle_iff name P hP j false).1 (ht j false) with h | h | h
    · exact False.elim (hj ((leaf_eq_iff name c j false false).1 (hc.symm.trans h)).1.symm)
    · exact False.elim (leaf_ne_opposite name c j (hc.symm.trans h))
    · exact h

theorem chosen_unique (P : Equiv.Perm (Fin k)) {c d : Fin q}
    (hc : Chosen name P c) (hd : Chosen name P d) : c = d :=
  ((leaf_eq_iff name c d false false).1 ((hc.1 false).symm.trans (hd.1 false))).1

theorem choice_characterization (P : Equiv.Perm (Fin k)) (hP : Function.Involutive P) :
    ((∀ c b, Hit P {Hub name b, Leaf name c false, Leaf name c true}) ∧
      Hit P (Star name false)) ↔ ∃! c, Chosen name P c := by
  constructor
  · rintro ⟨ht, hs⟩
    obtain ⟨c, hc⟩ := star_forces_hub name P hP ht hs
    have hchosen := chosen_of_hub name P hP ht c hc
    exact ⟨c, hchosen, fun d hd => chosen_unique name P hd hchosen⟩
  · rintro ⟨c, hc, -⟩
    constructor
    · intro j b
      apply (triangle_iff name P hP j b).2
      by_cases hj : j = c
      · subst j
        cases b
        · exact Or.inl (hc.1 false)
        · exact Or.inr (Or.inl (hc.1 true))
      · exact Or.inr (Or.inr (hc.2 j hj))
    · refine ⟨Hub name false, ?_, ?_, ?_⟩
      · exact (hub_mem_star name false false).2 rfl
      · rw [hc.1 false]
        exact (leaf_mem_star name c false false).2 rfl
      · rw [hc.1 false]
        exact (hub_ne_leaf name false false c).symm

end PEqualNP.Outside.L_lib_884.TwoHubs


namespace PEqualNP.Outside.L_lib_884.TwoHubs

variable {q k : ℕ} (name : (Option (Fin q) × Bool) ↪ Fin k)

def Neutral (S : Finset (Fin k)) : Prop :=
  ∃ c, Leaf name c false ∈ S ∧ Leaf name c true ∈ S

def Desired (c : Fin q) (S : Finset (Fin k)) : Prop :=
  (∃ b, Hub name b ∈ S ∧ Leaf name c b ∈ S) ∨
  (∃ j, j ≠ c ∧ Leaf name j false ∈ S ∧ Leaf name j true ∈ S)

theorem desired_of_not_neutral {S : Finset (Fin k)} (hn : ¬ Neutral name S)
    (c : Fin q) (hd : Desired name c S) :
    ∃ b, Hub name b ∈ S ∧ Leaf name c b ∈ S := by
  rcases hd with hd | ⟨j, _, hj⟩
  · exact hd
  · exact False.elim (hn ⟨j, hj⟩)

theorem star_card (b : Bool) : (Star name b).card = q+1 := by
  have hi : Function.Injective (fun c : Fin q => Leaf name c b) := by
    intro c d h
    exact ((leaf_eq_iff name c d b b).1 h).1
  have hn : Hub name b ∉ Finset.univ.image (fun c : Fin q => Leaf name c b) := by
    simp [Finset.mem_image, (hub_ne_leaf name b b _).symm]
  rw [Star, Finset.card_insert_of_notMem hn, Finset.card_image_of_injective _ hi]
  simp

theorem both_hubs_card {S : Finset (Fin k)}
    (hf : Hub name false ∈ S) (ht : Hub name true ∈ S)
    (hl : ∀ c, ∃ b, Hub name b ∈ S ∧ Leaf name c b ∈ S) : q+2 ≤ S.card := by
  classical
  let z : Fin q → Bool := fun c => Classical.choose (hl c)
  have hz : ∀ c, Leaf name c (z c) ∈ S := fun c => (Classical.choose_spec (hl c)).2
  let T : Finset (Fin k) := Finset.univ.image (fun c : Fin q => Leaf name c (z c))
  have hinj : Function.Injective (fun c : Fin q => Leaf name c (z c)) := by
    intro c d h
    exact ((leaf_eq_iff name c d (z c) (z d)).1 h).1
  have hcT : T.card = q := by
    dsimp only [T]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hfT : Hub name false ∉ T := by
    intro h
    obtain ⟨c, _, hc⟩ := Finset.mem_image.1 h
    exact hub_ne_leaf name false (z c) c hc.symm
  have htT : Hub name true ∉ T := by
    intro h
    obtain ⟨c, _, hc⟩ := Finset.mem_image.1 h
    exact hub_ne_leaf name true (z c) c hc.symm
  have hfins : Hub name false ∉ insert (Hub name true) T := by
    simp only [Finset.mem_insert, not_or]
    refine ⟨?_, hfT⟩
    intro h
    have : false = true := hub_injective name h
    cases this
  have hsub : insert (Hub name false) (insert (Hub name true) T) ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hf
    · rcases Finset.mem_insert.1 hx with rfl | hx
      · exact ht
      · obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hx
        exact hz c
  have hh := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hfins, Finset.card_insert_of_notMem htT, hcT] at hh
  omega

theorem star_characterization (hq : 0 < q) (S : Finset (Fin k)) (hcard : S.card ≤ q+1) :
    (¬ Neutral name S ∧ ∀ c, Desired name c S) ↔ S = Star name false ∨ S = Star name true := by
  classical
  constructor
  · rintro ⟨hn, hd⟩
    have hl : ∀ c, ∃ b, Hub name b ∈ S ∧ Leaf name c b ∈ S :=
      fun c => desired_of_not_neutral name hn c (hd c)
    have hnotboth : ¬ (Hub name false ∈ S ∧ Hub name true ∈ S) := by
      rintro ⟨hf, ht⟩
      have h := both_hubs_card name hf ht hl
      omega
    by_cases hf : Hub name false ∈ S
    · have ht : Hub name true ∉ S := fun ht => hnotboth ⟨hf, ht⟩
      have hleaves : ∀ c, Leaf name c false ∈ S := by
        intro c
        obtain ⟨b, hb, hc⟩ := hl c
        cases b
        · exact hc
        · exact False.elim (ht hb)
      have hsub : Star name false ⊆ S := by
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact hf
        · obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hx
          exact hleaves c
      exact Or.inl (Finset.eq_of_subset_of_card_le hsub (by simpa [star_card] using hcard)).symm
    · have ht : Hub name true ∈ S := by
        obtain ⟨b, hb, _⟩ := hl ⟨0, hq⟩
        cases b
        · exact False.elim (hf hb)
        · exact hb
      have hleaves : ∀ c, Leaf name c true ∈ S := by
        intro c
        obtain ⟨b, hb, hc⟩ := hl c
        cases b
        · exact False.elim (hf hb)
        · exact hc
      have hsub : Star name true ⊆ S := by
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact ht
        · obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hx
          exact hleaves c
      exact Or.inr (Finset.eq_of_subset_of_card_le hsub (by simpa [star_card] using hcard)).symm
  · have hs : ∀ b, ¬ Neutral name (Star name b) ∧ ∀ c, Desired name c (Star name b) := by
      intro b
      constructor
      · rintro ⟨c, hf, ht⟩
        have hfb := (leaf_mem_star name c false b).1 hf
        have htb := (leaf_mem_star name c true b).1 ht
        have : false = true := hfb.trans htb.symm
        cases this
      · intro c
        exact Or.inl ⟨b, (hub_mem_star name b b).2 rfl, (leaf_mem_star name c b b).2 rfl⟩
    rintro (rfl | rfl)
    · exact hs false
    · exact hs true

end PEqualNP.Outside.L_lib_884.TwoHubs

theorem PEqualNP.Outside.L_lib_884 :
∀ (q k : Nat), 2 ≤ q →
  let V := Option (Fin q) × Bool
  ∀ name : V ↪ Fin k,
  let hub := fun b : Bool => name (none,b)
  let leaf := fun (c : Fin q) (b : Bool) => name (some c,b)
  let star := fun b : Bool => insert (hub b) (Finset.univ.image (fun c : Fin q => leaf c b))
  let neutral := fun S : Finset (Fin k) => ∃ c, leaf c false ∈ S ∧ leaf c true ∈ S
  let desired := fun (c : Fin q) (S : Finset (Fin k)) =>
    (∃ b, hub b ∈ S ∧ leaf c b ∈ S) ∨
    (∃ j, j ≠ c ∧ leaf j false ∈ S ∧ leaf j true ∈ S)
  (∀ P : Equiv.Perm (Fin k), Function.Involutive P →
    let hit := fun S : Finset (Fin k) => ∃ u ∈ S, P u ∈ S ∧ P u ≠ u
    let chosen := fun c : Fin q =>
      (∀ b, P (hub b) = leaf c b) ∧
      ∀ j, j ≠ c → P (leaf j false) = leaf j true
    ((∀ (c : Fin q) (b : Bool), hit {hub b, leaf c false, leaf c true}) ∧ hit (star false)) ↔
      ∃! c, chosen c) ∧
  ∀ S : Finset (Fin k), S.card ≤ q+1 →
    ((¬ neutral S ∧ ∀ c, desired c S) ↔ S = star false ∨ S = star true) := by
  intro q k hq V name hub leaf star neutral desired
  constructor
  · intro P hP
    exact PEqualNP.Outside.L_lib_884.TwoHubs.choice_characterization name P hP
  · intro S hS
    exact PEqualNP.Outside.L_lib_884.TwoHubs.star_characterization name (by omega) S hS
