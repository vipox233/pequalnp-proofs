import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25711_aux

private theorem pair_eq_iff {α : Type*} [DecidableEq α] {a b x y : α} :
    ({a, b} : Finset α) = {x, y} ↔ (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
  constructor
  · intro h
    have ha : a ∈ ({x, y} : Finset α) := h ▸ Finset.mem_insert_self a {b}
    have hb : b ∈ ({x, y} : Finset α) := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    have hx : x ∈ ({a, b} : Finset α) := h.symm ▸ Finset.mem_insert_self x {y}
    have hy : y ∈ ({a, b} : Finset α) := h.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hx hy
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> tauto
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Finset.pair_comm a b

private theorem dir_fwd (n q : ℕ) (G : Fin n → Fin n → Bool) (π : Equiv.Perm (Fin n))
    (r c e : ℕ)
    (R C : Fin q → Finset (Fin n)) (out : Finset (Fin n) → (Fin q → Bool) → Bool)
    (hR : (∑ j, (R j).card) ≤ r) (hC : (∑ j, (C j).card) ≤ c)
    (hloss : ((Finset.univ : Finset (Fin n × Fin n)).filter (fun z =>
      out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠ G z.1 (π z.2))).card ≤ e) :
    ∃ f : Fin n → Fin q → Fin 3,
      (∑ j : Fin q, ((Finset.univ : Finset (Fin n)).filter (fun v => f v j = 1)).card) ≤ r ∧
      (∑ j : Fin q, ((Finset.univ : Finset (Fin n)).filter (fun w => f w j = 2)).card) ≤ c ∧
      ((Finset.univ : Finset (Fin n × Fin n)).filter (fun z => z.1 < z.2 ∧
        f z.1 = f z.2 ∧ G z.1 (π z.2) ≠ G z.2 (π z.1))).card ≤ e := by
  let f : Fin n → Fin q → Fin 3 := fun x j =>
    if x ∈ R j ∧ π x ∈ C j then 0
    else if x ∈ R j then 1
    else if π x ∈ C j then 2
    else 0
  refine ⟨f, ?_, ?_, ?_⟩
  · calc ∑ j : Fin q, ((Finset.univ : Finset (Fin n)).filter (fun v => f v j = 1)).card
        ≤ ∑ j : Fin q, (R j).card := by
          apply Finset.sum_le_sum
          intro j _
          apply Finset.card_le_card
          intro v hv
          have hf1 : f v j = 1 := (Finset.mem_filter.mp hv).2
          dsimp only [f] at hf1
          by_cases h1 : v ∈ R j
          · exact h1
          · by_cases h2 : π v ∈ C j <;> simp [h1, h2] at hf1
      _ ≤ r := hR
  · calc ∑ j : Fin q, ((Finset.univ : Finset (Fin n)).filter (fun w => f w j = 2)).card
        ≤ ∑ j : Fin q, (C j).card := by
          apply Finset.sum_le_sum
          intro j _
          have him : ((Finset.univ : Finset (Fin n)).filter (fun w => f w j = 2)).card =
              (((Finset.univ : Finset (Fin n)).filter (fun w => f w j = 2)).image π).card :=
            (Finset.card_image_of_injective _ π.injective).symm
          rw [him]
          apply Finset.card_le_card
          intro u hu
          rcases Finset.mem_image.mp hu with ⟨w, hw, rfl⟩
          have hf2 : f w j = 2 := (Finset.mem_filter.mp hw).2
          dsimp only [f] at hf2
          by_cases h2 : π w ∈ C j
          · exact h2
          · by_cases h1 : w ∈ R j <;> simp [h1, h2] at hf2
      _ ≤ c := hC
  · let pools : Fin n → Fin n → Fin q → Bool := fun x y j => decide (x ∈ R j ∨ π y ∈ C j)
    have hpools_eq : ∀ x y : Fin n, f x = f y → pools x y = pools y x := by
      intro x y hxy
      funext j
      have hj : f x j = f y j := congrFun hxy j
      dsimp only [f] at hj
      dsimp only [pools]
      by_cases hxR : x ∈ R j <;> by_cases hxC : π x ∈ C j <;>
        by_cases hyR : y ∈ R j <;> by_cases hyC : π y ∈ C j <;>
        simp [hxR, hxC, hyR, hyC] at hj ⊢
    let Bad := (Finset.univ : Finset (Fin n × Fin n)).filter (fun z =>
      z.1 < z.2 ∧ f z.1 = f z.2 ∧ G z.1 (π z.2) ≠ G z.2 (π z.1))
    let Err := (Finset.univ : Finset (Fin n × Fin n)).filter (fun z =>
      out {z.1, z.2} (pools z.1 z.2) ≠ G z.1 (π z.2))
    let φ : Fin n × Fin n → Fin n × Fin n := fun z =>
      if out {z.1, z.2} (pools z.1 z.2) ≠ G z.1 (π z.2) then z else (z.2, z.1)
    have hle : Bad.card ≤ Err.card := by
      refine Finset.card_le_card_of_injOn φ ?_ ?_
      · intro z hz
        rcases (Finset.mem_filter.mp hz).2 with ⟨_, hfeq, hGne⟩
        dsimp only [φ]
        split_ifs with herr
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, herr⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have h1 : out {z.1, z.2} (pools z.1 z.2) = G z.1 (π z.2) := by
            by_contra hne; exact herr hne
          rw [Finset.pair_comm z.2 z.1, ← hpools_eq z.1 z.2 hfeq, h1]
          exact hGne
      · intro z₁ hz₁ z₂ hz₂ heq
        have hlt1 : z₁.1 < z₁.2 := (Finset.mem_filter.mp hz₁).2.1
        have hlt2 : z₂.1 < z₂.2 := (Finset.mem_filter.mp hz₂).2.1
        dsimp only [φ] at heq
        split_ifs at heq with h1 h2
        · exact heq
        · have hfst := congrArg Prod.fst heq
          have hsnd := congrArg Prod.snd heq
          dsimp only at hfst hsnd
          rw [hfst, hsnd] at hlt1
          exact absurd hlt1 (not_lt.mpr (le_of_lt hlt2))
        · have hfst := congrArg Prod.fst heq
          have hsnd := congrArg Prod.snd heq
          dsimp only at hfst hsnd
          rw [← hfst, ← hsnd] at hlt2
          exact absurd hlt2 (not_lt.mpr (le_of_lt hlt1))
        · exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
    exact hle.trans hloss

private theorem dir_bwd (n q : ℕ) (G : Fin n → Fin n → Bool) (π : Equiv.Perm (Fin n))
    (r c e : ℕ) (f : Fin n → Fin q → Fin 3)
    (hf1 : (∑ j : Fin q, ((Finset.univ : Finset (Fin n)).filter (fun v => f v j = 1)).card) ≤ r)
    (hf2 : (∑ j : Fin q, ((Finset.univ : Finset (Fin n)).filter (fun w => f w j = 2)).card) ≤ c)
    (hbad : ((Finset.univ : Finset (Fin n × Fin n)).filter (fun z => z.1 < z.2 ∧
      f z.1 = f z.2 ∧ G z.1 (π z.2) ≠ G z.2 (π z.1))).card ≤ e) :
    ∃ (R C : Fin q → Finset (Fin n)) (out : Finset (Fin n) → (Fin q → Bool) → Bool),
      (∑ j, (R j).card) ≤ r ∧ (∑ j, (C j).card) ≤ c ∧
      ((Finset.univ : Finset (Fin n × Fin n)).filter (fun z =>
        out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠ G z.1 (π z.2))).card ≤ e := by
  classical
  let R : Fin q → Finset (Fin n) := fun j => Finset.univ.filter (fun v => f v j = 1)
  let C : Fin q → Finset (Fin n) := fun j => (Finset.univ.filter (fun w => f w j = 2)).image π
  let pools : Fin n → Fin n → Fin q → Bool := fun x y j => decide (x ∈ R j ∨ π y ∈ C j)
  have hpools_val : ∀ x y j, pools x y j = decide (f x j = 1 ∨ f y j = 2) := by
    intro x y j
    dsimp only [pools, R, C]
    have hmemC : π y ∈ (Finset.univ.filter (fun w => f w j = 2)).image π ↔ f y j = 2 := by
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨w, hw, heq⟩; rw [← π.injective heq]; exact hw
      · intro hy; exact ⟨y, hy, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmemC]
  have hpools_iff : ∀ x y : Fin n, pools x y = pools y x ↔ f x = f y := by
    intro x y
    constructor
    · intro h
      funext j
      have hj := congrFun h j
      rw [hpools_val, hpools_val] at hj
      generalize f x j = a at hj ⊢
      generalize f y j = b at hj ⊢
      fin_cases a <;> fin_cases b <;> simp_all
    · intro h
      funext j
      rw [hpools_val, hpools_val, congrFun h j]
  let out : Finset (Fin n) → (Fin q → Bool) → Bool := fun S sig =>
    decide (∃ a b : Fin n, {a, b} = S ∧ pools a b = sig ∧ G a (π b) = true ∧ (f a = f b → a ≤ b))
  refine ⟨R, C, out, hf1, ?_, ?_⟩
  · have hCcard : ∀ j : Fin q, (C j).card =
        ((Finset.univ : Finset (Fin n)).filter (fun w => f w j = 2)).card :=
      fun j => Finset.card_image_of_injective _ π.injective
    simp only [hCcard]
    exact hf2
  · have hout_eq_of_ne : ∀ x y : Fin n, f x ≠ f y → out {x, y} (pools x y) = G x (π y) := by
      intro x y hne
      dsimp only [out]
      have hiff : (∃ a b : Fin n, {a, b} = ({x, y} : Finset (Fin n)) ∧ pools a b = pools x y ∧
          G a (π b) = true ∧ (f a = f b → a ≤ b)) ↔ G x (π y) = true := by
        constructor
        · rintro ⟨a, b, hpair, hp, hG, _⟩
          rcases pair_eq_iff.mp hpair with ⟨hax, hby⟩ | ⟨hay, hbx⟩
          · rw [← hax, ← hby]; exact hG
          · rw [hay, hbx] at hp
            exact absurd ((hpools_iff x y).mp hp.symm) hne
        · intro hG
          exact ⟨x, y, rfl, rfl, hG, fun h => absurd h hne⟩
      cases hG : G x (π y)
      · simp [hiff, hG]
      · simp [hiff, hG]
    have hout_eq_of_le : ∀ x y : Fin n, f x = f y → x ≤ y → out {x, y} (pools x y) = G x (π y) := by
      intro x y hfeq hle
      dsimp only [out]
      have hiff : (∃ a b : Fin n, {a, b} = ({x, y} : Finset (Fin n)) ∧ pools a b = pools x y ∧
          G a (π b) = true ∧ (f a = f b → a ≤ b)) ↔ G x (π y) = true := by
        constructor
        · rintro ⟨a, b, hpair, _, hG, hord⟩
          rcases pair_eq_iff.mp hpair with ⟨hax, hby⟩ | ⟨hay, hbx⟩
          · rw [← hax, ← hby]; exact hG
          · rw [hay, hbx] at hG hord
            have hxy : x = y := le_antisymm hle (hord hfeq.symm)
            rw [hxy] at hG ⊢; exact hG
        · intro hG
          exact ⟨x, y, rfl, rfl, hG, fun _ => hle⟩
      cases hG : G x (π y)
      · simp [hiff, hG]
      · simp [hiff, hG]
    let Err := (Finset.univ : Finset (Fin n × Fin n)).filter (fun z =>
      out {z.1, z.2} (pools z.1 z.2) ≠ G z.1 (π z.2))
    let Bad := (Finset.univ : Finset (Fin n × Fin n)).filter (fun z =>
      z.1 < z.2 ∧ f z.1 = f z.2 ∧ G z.1 (π z.2) ≠ G z.2 (π z.1))
    have hle : Err.card ≤ Bad.card := by
      refine Finset.card_le_card_of_injOn (fun z => (z.2, z.1)) ?_ ?_
      · intro z hz
        have herr : out {z.1, z.2} (pools z.1 z.2) ≠ G z.1 (π z.2) := (Finset.mem_filter.mp hz).2
        have hfeq : f z.1 = f z.2 := by
          by_contra hne
          exact herr (hout_eq_of_ne z.1 z.2 hne)
        have hlt : z.2 < z.1 := by
          by_contra hnot
          exact herr (hout_eq_of_le z.1 z.2 hfeq (not_lt.mp hnot))
        have hout_swap : out {z.1, z.2} (pools z.1 z.2) = G z.2 (π z.1) := by
          rw [Finset.pair_comm z.1 z.2, (hpools_iff z.1 z.2).mpr hfeq]
          exact hout_eq_of_le z.2 z.1 hfeq.symm (le_of_lt hlt)
        rw [hout_swap] at herr
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt, hfeq.symm, herr⟩
      · intro z₁ _ z₂ _ heq
        exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
    exact hle.trans hbad

end PEqualNP.Outside.L_meta_25711_aux

theorem PEqualNP.Outside.L_meta_25711 :
∀ (n q : ℕ) (G : Fin n → Fin n → Bool) (π : Equiv.Perm (Fin n)),
  let I := Fin n
  let P := Fin q
  let pools := fun (R C : P → Finset I) (x y : I) (j : P) => decide (x ∈ R j ∨ π y ∈ C j)
  let loss := fun (R C : P → Finset I) (out : Finset I → (P → Bool) → Bool) =>
    ((Finset.univ : Finset (I × I)).filter (fun z =>
      out {z.1,z.2} (pools R C z.1 z.2) ≠ G z.1 (π z.2))).card
  ∀ (r c e : ℕ),
    (∃ (R C : P → Finset I) (out : Finset I → (P → Bool) → Bool),
      (∑ j, (R j).card) ≤ r ∧ (∑ j, (C j).card) ≤ c ∧ loss R C out ≤ e) ↔
    ∃ f : I → P → Fin 3,
      (∑ j : P, ((Finset.univ : Finset I).filter (fun v => f v j = 1)).card) ≤ r ∧
      (∑ j : P, ((Finset.univ : Finset I).filter (fun w => f w j = 2)).card) ≤ c ∧
      ((Finset.univ : Finset (I × I)).filter (fun z => z.1 < z.2 ∧
        f z.1 = f z.2 ∧ G z.1 (π z.2) ≠ G z.2 (π z.1))).card ≤ e := by
  intro n q G π I P pools loss r c e
  constructor
  · rintro ⟨R, C, out, hR, hC, hloss⟩
    exact PEqualNP.Outside.L_meta_25711_aux.dir_fwd n q G π r c e R C out hR hC hloss
  · rintro ⟨f, hf1, hf2, hbad⟩
    exact PEqualNP.Outside.L_meta_25711_aux.dir_bwd n q G π r c e f hf1 hf2 hbad
