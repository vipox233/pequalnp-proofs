import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_487 : (∀ (n k t r : Nat), 0 < k →
  let V := Fin n
  let Point := V → Bool
  let Pick := Fin t → Fin k
  let dist := fun (x y : Point) => ((Finset.univ : Finset V).filter (fun i => x i ≠ y i)).card
  let miss := fun (a b : Pick) =>
    ((Finset.univ : Finset (Fin t)).filter (fun g => a g ≠ b g)).card
  ∀ (C : Finset Pick), (∀ picks : Pick, ∃ d ∈ C, miss picks d ≤ r) →
    ∀ (slot : Fin t × Fin k → V), Function.Injective slot →
    ∀ x y : Point, (∀ g : Fin t, ∃ h : Fin k, x (slot (g,h)) ≠ y (slot (g,h))) →
    ∃ c ∈ C,
      let changed := (Finset.univ : Finset (Fin t)).image (fun i => slot (i,c i))
      let next : Point := fun v => if v ∈ changed then !(x v) else x v
      dist next y + t ≤ dist x y + 2*r) := by
  intro n k t r _ V Point Pick dist miss C hC slot hslot x y hxy
  choose p hp using hxy
  obtain ⟨c, hcC, hc⟩ := hC p
  refine ⟨c, hcC, ?_⟩
  intro changed next

  have hinj : Function.Injective (fun i : Fin t => slot (i, c i)) := by
    intro i j h
    exact (Prod.ext_iff.mp (hslot h)).1
  have hch : changed.card = t := by
    simp only [changed]
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

  have key : ∀ v : V, (if next v ≠ y v then 1 else 0) + (if v ∈ changed then 1 else 0) =
      (if x v ≠ y v then 1 else 0) + 2 * (if v ∈ changed ∧ x v = y v then 1 else 0) := by
    intro v
    by_cases h : v ∈ changed <;> cases hx : x v <;> cases hy : y v <;> simp [next, h, hx]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset V)) rfl (fun v _ => key v)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  simp only [Finset.sum_boole, Nat.cast_id] at hsum
  have hmem : (Finset.univ.filter (fun v : V => v ∈ changed)) = changed := by
    ext v; simp
  rw [hmem, hch] at hsum

  have hS : (Finset.univ.filter (fun v : V => v ∈ changed ∧ x v = y v)).card ≤ r := by
    calc (Finset.univ.filter (fun v : V => v ∈ changed ∧ x v = y v)).card
        ≤ ((Finset.univ.filter (fun g : Fin t => p g ≠ c g)).image (fun i => slot (i, c i))).card := by
          apply Finset.card_le_card
          intro v hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, changed, Finset.mem_image] at hv
          obtain ⟨⟨i, rfl⟩, heq⟩ := hv
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨i, ?_, rfl⟩
          intro hpc
          exact hp i (by rw [hpc]; exact heq)
      _ ≤ (Finset.univ.filter (fun g : Fin t => p g ≠ c g)).card := Finset.card_image_le
      _ ≤ r := hc
  show (Finset.univ.filter (fun i => next i ≠ y i)).card + t ≤
    (Finset.univ.filter (fun i => x i ≠ y i)).card + 2 * r
  omega
