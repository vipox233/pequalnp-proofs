import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_29790
import PEqualNP.Outside.L_meta_29798
import PEqualNP.Outside.L_meta_29808
import PEqualNP.Outside.L_meta_29820
import PEqualNP.Outside.L_meta_29834
import PEqualNP.Outside.L_meta_29850
import PEqualNP.Outside.L_meta_29868
import PEqualNP.Outside.L_meta_29888
import PEqualNP.Outside.L_meta_29910

theorem PEqualNP.Outside.L_meta_32048 : (∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length),
  PEqualNP.MetaComplexity.FanInTwo C → C.size = 10 →
  (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
    (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) →
  0 ∈ (C.gates.get i).inputs → (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) →
  (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
  (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and → i.val < k.val →
  7 + i.val ∈ (C.gates.get k).inputs → 5 ∈ (C.gates.get i).inputs →
  ¬ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧
    (C.wires (List.ofFn x)).getD 5 false = true) := by
  intro C i k hf hs he h0 hu hor hand hik hk h5 hx
  obtain ⟨x, hx0, hx1, hx6, hw⟩ := hx
  have hlen : C.gates.length = 10 := hs
  have hkl := k.isLt
  obtain h | h | h | h | h | h | h | h | h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 := by omega
  · exact PEqualNP.Outside.L_meta_29790 ⟨C, i, k, h, hf, hs, he, h0, hu, hor, hand, hik, hk, h5, by decide, by omega, x, hx0, hx1, hx6, hw⟩
  · exact PEqualNP.Outside.L_meta_29798 ⟨C, i, k, h, hf, hs, he, h0, hu, hor, hand, hik, hk, h5, by decide, by omega, x, hx0, hx1, hx6, hw⟩
  · exact PEqualNP.Outside.L_meta_29808 ⟨C, i, k, h, hf, hs, he, h0, hu, hor, hand, hik, hk, h5, by decide, by omega, x, hx0, hx1, hx6, hw⟩
  · exact PEqualNP.Outside.L_meta_29820 ⟨C, i, k, h, hf, hs, he, h0, hu, hor, hand, hik, hk, h5, by decide, by omega, x, hx0, hx1, hx6, hw⟩
  · exact PEqualNP.Outside.L_meta_29834 ⟨C, i, k, h, hf, hs, he, h0, hu, hor, hand, hik, hk, h5, by decide, by omega, x, hx0, hx1, hx6, hw⟩
  · exact PEqualNP.Outside.L_meta_29850 ⟨C, i, k, h, hf, hs, he, h0, hu, hor, hand, hik, hk, h5, by decide, by omega, x, hx0, hx1, hx6, hw⟩
  · exact PEqualNP.Outside.L_meta_29868 ⟨C, i, k, h, hf, hs, he, h0, hu, hor, hand, hik, hk, h5, by decide, by omega, x, hx0, hx1, hx6, hw⟩
  · exact PEqualNP.Outside.L_meta_29888 ⟨C, i, k, h, hf, hs, he, h0, hu, hor, hand, hik, hk, h5, by decide, by omega, x, hx0, hx1, hx6, hw⟩
  · exact PEqualNP.Outside.L_meta_29910 ⟨C, i, k, h, hf, hs, he, h0, hu, hor, hand, hik, hk, h5, by decide, by omega, x, hx0, hx1, hx6, hw⟩
