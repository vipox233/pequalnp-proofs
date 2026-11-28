import Mathlib
import PEqualNP.Defs

namespace PEqualNP.CircuitLowerBounds.CyclicParityBudget

abbrev RegisteredBound : Prop :=
∀ (n w : Nat) (hn : 0 < n),
  let P := 2^(w+1)
  let J := 2^(min n (w+1))
  let E := n*J
  let h := n-(w+1)
  let D := 2^w
  let admissible := fun H : Nat => H ≤ J ∨
    (0 < w ∧ 2*w ≤ n ∧ n % 2 = 0 ∧ H ≤ (D*min (n/2) D+19)/20) ∨
    (32 ≤ n ∧ h ≤ Nat.clog 2 (2*(n-n/2)) ∧ H ≤ 2^(n-13)) ∨
    (∃ a b q s : Nat, n = a+b ∧ 0 < q ∧ 0 < s ∧ s ≤ h ∧ q*h < a ∧
      (q+1)*h ≤ b ∧ H ≤ q^2*(2^s-1)^(2*(q-1))*2^(n-(2*q*s+(h-s))))
  let inv := fun (G : PEqualNP.CircuitLowerBounds.Circuit) =>
    (G.gates.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length
  let binary := fun (G : PEqualNP.CircuitLowerBounds.Circuit) => G.size - inv G
  let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ hn⟩ : Fin n)
  let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ ∀ raw : Fin (n*P) → Bool,
      let entries := List.ofFn raw
      let pass := fun (x : Fin n → Bool) => ∀ i : Fin n,
        let word := ∑ j : Fin (w+1), if x (loc (i.val+j.val)) then 2^j.val else 0
        entries.getD (i.val*P+word) false = true
      C.eval entries = (((Finset.univ : Finset (Fin n → Bool)).filter pass).card).testBit 0
  (∀ (H : Nat), 0 < H → admissible H → ∀ C, fits C →
     (E-H)+3*(H-1) ≤ binary C ∧ (E-H)+4*(H-1) ≤ C.size) ∧
    (n ≤ w+1 → ∃ C, fits C ∧ binary C = (E-J)+3*(J-1) ∧ C.size = (E-J)+4*(J-1))

theorem excludes123 (bound : RegisteredBound) : ¬ (
let n := 3
let w := 1
let P := 2^(w+1)
let inv := fun (G : PEqualNP.CircuitLowerBounds.Circuit) =>
  (G.gates.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length
let binary := fun (G : PEqualNP.CircuitLowerBounds.Circuit) => G.size - inv G
let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ (Nat.succ_pos 2)⟩ : Fin n)
let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo C ∧ ∀ raw : Fin (n*P) → Bool,
    let entries := List.ofFn raw
    let pass := fun (x : Fin n → Bool) => ∀ i : Fin n,
      let word := ∑ j : Fin (w+1), if x (loc (i.val+j.val)) then 2^j.val else 0
      entries.getD (i.val*P+word) false = true
    C.eval entries = (((Finset.univ : Finset (Fin n → Bool)).filter pass).card).testBit 0
∃ C, fits C ∧ binary C ≤ 16
) := by
  rintro ⟨C, fits, cap⟩
  have lower := ((bound 3 1 (by decide)).1 4 (by decide) (Or.inl (by decide)) C fits).1
  exact (by decide : ¬ (17 ≤ 16)) (le_trans lower cap)

theorem excludes124 (bound : RegisteredBound) : ¬ (
let n := 4
let w := 1
let P := 2^(w+1)
let inv := fun (G : PEqualNP.CircuitLowerBounds.Circuit) =>
  (G.gates.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length
let binary := fun (G : PEqualNP.CircuitLowerBounds.Circuit) => G.size - inv G
let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ (Nat.succ_pos 3)⟩ : Fin n)
let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.FanInTwo C ∧ ∀ raw : Fin (n*P) → Bool,
    let entries := List.ofFn raw
    let pass := fun (x : Fin n → Bool) => ∀ i : Fin n,
      let word := ∑ j : Fin (w+1), if x (loc (i.val+j.val)) then 2^j.val else 0
      entries.getD (i.val*P+word) false = true
    C.eval entries = (((Finset.univ : Finset (Fin n → Bool)).filter pass).card).testBit 0
∃ C, fits C ∧ binary C ≤ 20
) := by
  rintro ⟨C, fits, cap⟩
  have lower := ((bound 4 1 (by decide)).1 4 (by decide) (Or.inl (by decide)) C fits).1
  exact (by decide : ¬ (21 ≤ 20)) (le_trans lower cap)

end PEqualNP.CircuitLowerBounds.CyclicParityBudget
