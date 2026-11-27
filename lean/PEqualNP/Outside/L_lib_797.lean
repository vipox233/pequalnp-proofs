import Mathlib.Data.Finset.Basic

theorem PEqualNP.Outside.L_lib_797 : (∀ (n m : Nat) (r u : Fin n) (c v : Fin m) (S : Finset (Fin n)) (T : Finset (Fin m))
    (H : Finset (Fin n) → Finset (Fin m) → Bool)
    (D : Finset (Fin n) → Finset (Fin m) → Bool → Bool → Bool),
  r ≠ u → c ≠ v → r ∉ S → u ∉ S → c ∉ T → v ∉ T → H ∅ ∅ = false →
  D ∅ ∅ false true = false →
  (∀ X X' Y Y' w w' z z', X ⊆ X' → Y ⊆ Y' → w ≤ w' → z ≤ z' →
    D X Y w z ≤ D X' Y' w' z') →
  let A := fun (i : Fin n) (j : Fin m) =>
    let w := decide (i = u ∨ j = v)
    D (if i = r ∨ i = u ∨ i ∈ S then ∅ else {i})
      (if j = c ∨ j = v ∨ j ∈ T then ∅ else {j}) w
      (!(w || H (if i ∈ S then {i} else ∅) (if j ∈ T then {j} else ∅)))
  (∀ i ∈ S, (∀ j, A i j = A r j) ∨ (∀ k j, A i j ≤ A k j)) ∧
    (∀ j ∈ T, (∀ i, A i j = A i c) ∨ (∀ l i, A i j ≤ A i l))) := by
  intro n m r u c v S T H D hru hcv hr hu hc hv hH hD mono
  dsimp only
  have zero (z : Bool) : D ∅ ∅ false z = false := by
    apply le_antisymm _ (by cases D ∅ ∅ false z <;> decide)
    calc
      D ∅ ∅ false z ≤ D ∅ ∅ false true :=
        mono _ _ _ _ _ _ _ _ (by rfl) (by rfl) (by rfl) (by cases z <;> decide)
      _ = false := hD
  constructor
  · intro i hi
    have hiu : i ≠ u := fun e => hu (e ▸ hi)
    cases h : H {i} ∅ with
    | false =>
      left
      intro j
      by_cases hj : j ∈ T
      · have hjv : j ≠ v := fun e => hv (e ▸ hj)
        simp [hi, hiu, hr, hru, hj, hjv, zero]
      · simp [hi, hiu, hr, hru, hj, h, hH]
    | true =>
      right
      intro k j
      by_cases hjv : j = v
      · subst j
        simp [hi, hv]
        apply mono <;> simp
      · by_cases hj : j ∈ T
        · simp [hi, hiu, hjv, hj, zero]
        · simp [hi, hiu, hjv, hj, h]
          apply mono <;> simp
  · intro j hj
    have hjv : j ≠ v := fun e => hv (e ▸ hj)
    cases h : H ∅ {j} with
    | false =>
      left
      intro i
      by_cases hi : i ∈ S
      · have hiu : i ≠ u := fun e => hu (e ▸ hi)
        simp [hj, hjv, hc, hcv, hi, hiu, zero]
      · simp [hj, hjv, hc, hcv, hi, h, hH]
    | true =>
      right
      intro l i
      by_cases hiu : i = u
      · subst i
        simp [hj, hu]
        apply mono <;> simp
      · by_cases hi : i ∈ S
        · simp [hj, hjv, hiu, hi, zero]
        · simp [hj, hjv, hiu, hi, h]
          apply mono <;> simp
