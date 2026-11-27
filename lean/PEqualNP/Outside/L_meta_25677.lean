import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25677_aux

private def G19 (i j : Fin 4) : Bool := (19 : ℕ).testBit (4 * i.val + j.val)

private def evalPerm (a b c d : Fin 4) : Fin 4 → Fin 4
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | ⟨3, _⟩ => d

private lemma no_perm :
    ∀ a b c d : Fin 4,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ¬ ∀ i j : Fin 4,
        Bool.xor (Bool.xor (G19 i (evalPerm a b c d i)) (G19 j (evalPerm a b c d j)))
          (Bool.xor (G19 i (evalPerm a b c d j)) (G19 j (evalPerm a b c d i))) = false := by
  decide

private lemma empty_shore_ok :
    ∀ i ∈ ({1, 2, 3} : Finset (Fin 4)), ∀ j ∈ ({1, 2, 3} : Finset (Fin 4)),
      Bool.xor (Bool.xor (G19 i i) (G19 j j)) (Bool.xor (G19 i j) (G19 j i)) =
      Bool.xor (decide (i ∈ (∅ : Finset (Fin 4)))) (decide (j ∈ (∅ : Finset (Fin 4)))) := by
  decide

private lemma one_shore_ok :
    ∀ i ∈ (Finset.univ : Finset (Fin 4)), ∀ j ∈ (Finset.univ : Finset (Fin 4)),
      Bool.xor (Bool.xor (G19 i i) (G19 j j)) (Bool.xor (G19 i j) (G19 j i)) =
      Bool.xor (decide (i ∈ ({0} : Finset (Fin 4)))) (decide (j ∈ ({0} : Finset (Fin 4)))) := by
  decide

end PEqualNP.Outside.L_meta_25677_aux

theorem PEqualNP.Outside.L_meta_25677 : (∀ u t : ℕ,
let G := fun (i j : Fin 4) => (19 : ℕ).testBit (4 * i.val + j.val)
(∃ (π : Equiv.Perm (Fin 4)) (K L : Finset (Fin 4)),
    L ⊆ K ∧ L.card ≤ u ∧ 4 ≤ K.card + t ∧
    ∀ i ∈ K, ∀ j ∈ K,
      Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) ↔ (if u = 0 then 1 else 0) ≤ t) := by
  intro u t
  dsimp only
  constructor
  · rintro ⟨π, K, L, _, hLu, hKt, hbox⟩
    by_cases hu : u = 0
    · subst hu
      simp only [↓reduceIte]
      by_contra ht
      have ht0 : t = 0 := by omega
      subst ht0
      have hKcard : K.card = 4 := by
        have hle : K.card ≤ 4 := by simpa using Finset.card_le_univ K
        omega
      have hK : K = Finset.univ := Finset.eq_univ_of_card K (by simpa using hKcard)
      have hL : L = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hK hL
      have hno := PEqualNP.Outside.L_meta_25677_aux.no_perm (π 0) (π 1) (π 2) (π 3)
        (fun h => absurd (π.injective h) (by decide))
        (fun h => absurd (π.injective h) (by decide))
        (fun h => absurd (π.injective h) (by decide))
        (fun h => absurd (π.injective h) (by decide))
        (fun h => absurd (π.injective h) (by decide))
        (fun h => absurd (π.injective h) (by decide))
      apply hno
      intro i j
      have hf : ∀ x : Fin 4,
          PEqualNP.Outside.L_meta_25677_aux.evalPerm (π 0) (π 1) (π 2) (π 3) x = π x := by
        rintro ⟨x, hx⟩
        match x, hx with
        | 0, _ => rfl
        | 1, _ => rfl
        | 2, _ => rfl
        | 3, _ => rfl
      have hij := hbox i (Finset.mem_univ i) j (Finset.mem_univ j)
      simp only [Finset.notMem_empty, decide_false, Bool.xor_self] at hij
      simpa only [hf, PEqualNP.Outside.L_meta_25677_aux.G19] using hij
    · simp [hu]
  · intro ht
    by_cases hu : u = 0
    · subst hu
      simp only [↓reduceIte] at ht
      refine ⟨Equiv.refl (Fin 4), {1, 2, 3}, ∅, Finset.empty_subset _, by simp, ?_, ?_⟩
      · have : ({1, 2, 3} : Finset (Fin 4)).card = 3 := by decide
        omega
      · exact PEqualNP.Outside.L_meta_25677_aux.empty_shore_ok
    · refine ⟨Equiv.refl (Fin 4), Finset.univ, {0}, Finset.subset_univ _, ?_, ?_, ?_⟩
      · simp; omega
      · simp
      · exact PEqualNP.Outside.L_meta_25677_aux.one_shore_ok
