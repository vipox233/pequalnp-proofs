import PEqualNP.Defs
import Mathlib.Data.ZMod.Basic

theorem PEqualNP.Outside.L_lib_447 : ∀ (n t : Nat) (S : Finset (Fin n → ZMod 2)),
  let Q := 2^n
  let covers := fun (shifts : Fin t → (Fin n → ZMod 2)) =>
    ∀ x : Fin n → ZMod 2, ∃ j : Fin t, x + shifts j ∈ S
  (Q*(Q-S.card)^t < Q^t → ∃ shifts, covers shifts) ∧
  (t*S.card < Q → ∀ shifts, ¬ covers shifts) := by
  intro n t S Q covers
  have hcardG : Fintype.card (Fin n → ZMod 2) = Q := by
    simp [Q]
  constructor
  · intro hlt
    let miss : (Fin n → ZMod 2) → Finset (Fin t → (Fin n → ZMod 2)) := fun x =>
      Fintype.piFinset (fun _ : Fin t => Finset.univ.filter (fun y : Fin n → ZMod 2 => x + y ∉ S))
    have hmiss_card : ∀ x : Fin n → ZMod 2, (miss x).card = (Q - S.card) ^ t := by
      intro x
      dsimp only [miss]
      rw [Fintype.card_piFinset]
      have hset : Finset.univ.filter (fun y : Fin n → ZMod 2 => x + y ∉ S) =
          Sᶜ.image (fun z => z - x) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_compl]
        constructor
        · intro hy
          exact ⟨x + y, hy, add_sub_cancel_left x y⟩
        · rintro ⟨z, hz, rfl⟩
          rwa [add_sub_cancel]
      have hinj : Function.Injective (fun z : Fin n → ZMod 2 => z - x) := sub_left_injective
      have h1 : (Finset.univ.filter (fun y : Fin n → ZMod 2 => x + y ∉ S)).card = Q - S.card := by
        rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_compl, hcardG]
      simp [h1]
    have hbi : (Finset.univ.biUnion miss).card < Fintype.card (Fin t → (Fin n → ZMod 2)) := by
      have htot : Fintype.card (Fin t → (Fin n → ZMod 2)) = Q ^ t := by
        simp [hcardG]
      rw [htot]
      calc (Finset.univ.biUnion miss).card
          ≤ ∑ x : Fin n → ZMod 2, (miss x).card := Finset.card_biUnion_le
        _ = ∑ _x : Fin n → ZMod 2, (Q - S.card) ^ t := Finset.sum_congr rfl (fun x _ => hmiss_card x)
        _ = Q * (Q - S.card) ^ t := by simp [hcardG]
        _ < Q ^ t := hlt
    have hex : ∃ shifts : Fin t → (Fin n → ZMod 2), shifts ∉ Finset.univ.biUnion miss := by
      by_contra hall
      push Not at hall
      have heq : Finset.univ.biUnion miss = Finset.univ := by
        ext s; simp [hall s]
      rw [heq, Finset.card_univ] at hbi
      exact lt_irrefl _ hbi
    rcases hex with ⟨shifts, hshifts⟩
    refine ⟨shifts, fun x => ?_⟩
    have hnot : shifts ∉ miss x := fun h => hshifts (Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ x, h⟩)
    dsimp only [miss] at hnot
    rw [Fintype.mem_piFinset] at hnot
    push Not at hnot
    rcases hnot with ⟨j, hj⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
    exact ⟨j, hj⟩
  · intro hlt shifts hcov
    have hsub : (Finset.univ : Finset (Fin n → ZMod 2)) ⊆
        (Finset.univ : Finset (Fin t)).biUnion (fun j => S.image (fun z => z - shifts j)) := by
      intro x _
      rcases hcov x with ⟨j, hj⟩
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j,
        Finset.mem_image.mpr ⟨x + shifts j, hj, add_sub_cancel_right x (shifts j)⟩⟩
    have hle : Q ≤ t * S.card := by
      calc Q = (Finset.univ : Finset (Fin n → ZMod 2)).card := by rw [Finset.card_univ, hcardG]
        _ ≤ ((Finset.univ : Finset (Fin t)).biUnion (fun j => S.image (fun z => z - shifts j))).card :=
            Finset.card_le_card hsub
        _ ≤ ∑ j : Fin t, (S.image (fun z => z - shifts j)).card := Finset.card_biUnion_le
        _ ≤ ∑ _j : Fin t, S.card := Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
        _ = t * S.card := by simp
    omega
