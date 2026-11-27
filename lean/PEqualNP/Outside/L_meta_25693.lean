import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25534

theorem PEqualNP.Outside.L_meta_25693 : (¬ (∃ (G : Fin 4 → Fin 6 → Bool) (code : Fin 6 → Fin 4 → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ u v : Fin 4, u ≠ v → ∃ c, G u c = true ∧ G v c = false) ∧
  (∀ u v w : Fin 4, u ≠ v → u ≠ w → v ≠ w →
    ∃ c, G u c = true ∧ G v c = true ∧ G w c = false) ∧
  PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧
  ∀ (u : Fin 4) (c : Fin 6),
    C.eval (List.ofFn (fun i : Fin 4 => decide (i = u)) ++ List.ofFn (code c)) = G u c)) := by
  rintro ⟨G, code, C, hPair, hTriple, hMono, hSize, hEval⟩
  have hLower : 7 ≤ C.size :=
    PEqualNP.Outside.L_meta_25534 4 6 4 G code C (by decide) hPair hTriple hMono hEval
  exact (by decide : ¬ (7 ≤ 6)) (hLower.trans hSize)
