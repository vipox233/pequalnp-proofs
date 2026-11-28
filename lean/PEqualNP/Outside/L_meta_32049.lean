import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.L27130
import PEqualNP.Outside.L_meta_32045
import PEqualNP.Outside.L_meta_32046
import PEqualNP.Outside.L_meta_32047
import PEqualNP.Outside.L_meta_32048

theorem PEqualNP.Outside.L_meta_32049 : (∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length) (h : ℕ),
  PEqualNP.MetaComplexity.FanInTwo C → C.size = 10 →
  (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
    (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) →
  0 ∈ (C.gates.get i).inputs → (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) →
  (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or →
  (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and → i.val < k.val →
  7 + i.val ∈ (C.gates.get k).inputs → h ∈ (C.gates.get i).inputs → h ≠ 0 → h < 7 + i.val →
  (∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧
    (C.wires (List.ofFn x)).getD h false = true) →
  7 ≤ h) := by
  intro C i k h hF hsz hev h0 huniq hor hand hik hk hh hne hlt hex
  by_contra hge
  have h7 : h < 7 := by omega
  interval_cases h
  · exact absurd rfl hne
  · exact PEqualNP.MetaComplexity.L27130 C 1 (Or.inl rfl) hex
  · exact PEqualNP.Outside.L_meta_32045 C i k hF hsz hev h0 huniq hor hand hik hk hh hex
  · exact PEqualNP.Outside.L_meta_32046 C i k hF hsz hev h0 huniq hor hand hik hk hh hex
  · exact PEqualNP.Outside.L_meta_32047 C i k hF hsz hev h0 huniq hor hand hik hk hh hex
  · exact PEqualNP.Outside.L_meta_32048 C i k hF hsz hev h0 huniq hor hand hik hk hh hex
  · exact PEqualNP.MetaComplexity.L27130 C 6 (Or.inr rfl) hex
