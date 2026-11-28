import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25663

theorem PEqualNP.Outside.L_meta_49524 :
¬ (∃ s : ℕ, 0 < s ∧
  let k := 2 * s
  let N := 2 ^ k
  let dot := fun (x y : Fin N) =>
    ((Finset.univ : Finset (Fin k)).filter (fun i =>
      x.val.testBit i.val && y.val.testBit i.val)).card % 2 == 1
  let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
        (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
  ∃ G : Fin N → Fin N → Bool,
  (∀ u v : Fin N, u ≠ v →
    2 * ((Finset.univ : Finset (Fin N)).filter (fun c => G u c ≠ G v c)).card = N) ∧
  let represents := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C ∧
    PEqualNP.Represents.Represents G C
  ∃ C, represents C ∧ C.gates.countP nonlinear ≤ s ∧
    ∃ g ∈ C.gates, nonlinear g = true ∧ ∃ w ∈ g.inputs,
      let W := fun (x : Fin (N+N) → Bool) => (C.wires (List.ofFn x)).getD w false
      ∃ x y, xor (W x) (W y) ≠
        xor (W (fun i => xor (x i) (y i))) (W (fun _ => false))) := by
  rintro ⟨s, hs, G, hG, C, hC, hcost, g, hmem, hg, w, hw, x, y, hfail⟩
  exact hfail (((PEqualNP.Outside.L_meta_25663 s hs G hG).2 C hC hcost).2 g hmem hg w hw x y)
