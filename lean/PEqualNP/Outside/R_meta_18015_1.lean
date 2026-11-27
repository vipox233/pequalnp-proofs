import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18015_1
    (hCompile :
      ∀ (x2 : Fin (10 : ℕ)) (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 (9 : ℕ) x3 →
        PEqualNP.TopForm.IsAO2 ((10 : ℕ) + x3.size) x4 →
        x3.size + x4.size ≤ (17 : ℕ) →
        x3.output < (9 : ℕ) + x3.size →
        ∃ (c : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsAO2 (10 : ℕ) c ∧ c.size ≤ (18 : ℕ) ∧
          ∀ (x : Fin (10 : ℕ) → Bool),
            c.eval (List.ofFn x) =
              x4.eval (x3.wires (List.ofFn (x2.removeNth x)) ++ [x x2 || x3.eval (List.ofFn (x2.removeNth x))]))
    (hNoCircuit18 :
      ∀ (x1 : Fin (11 : ℕ)) (c : PEqualNP.CircuitLowerBounds.Circuit),
        ↑x1 < (4 : ℕ) →
        PEqualNP.TopForm.IsAO2 (10 : ℕ) c →
        c.size ≤ (18 : ℕ) →
        ∃ (x8 : Fin (10 : ℕ) → Bool),
          c.eval (List.ofFn x8) ≠
            have x10 : Fin (11 : ℕ) → Bool := x1.insertNth Bool.false x8
            [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ),
             (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)].any
              fun (x11 : ℕ) => x10 (Fin.ofNat (11 : ℕ) (x11 / (11 : ℕ))) && x10 (Fin.ofNat (11 : ℕ) (x11 % (11 : ℕ)))) :
    (∀ (x1 : Fin (11 : ℕ)) (x2 : Fin (10 : ℕ)) (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit),   ↑x1 < (4 : ℕ) →     PEqualNP.TopForm.IsAO2 (9 : ℕ) x3 →       PEqualNP.TopForm.IsAO2 ((10 : ℕ) + x3.size) x4 →         x3.size + x4.size ≤ (17 : ℕ) →           (9 : ℕ) ≤ x3.output →             x3.output < (9 : ℕ) + x3.size →               have x11 : (Fin (10 : ℕ) → Bool) → Bool := fun (x11 : Fin (10 : ℕ) → Bool) =>                 have x12 : Fin (11 : ℕ) → Bool := x1.insertNth Bool.false x11;                 [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)].any fun (x13 : ℕ) => x12 (Fin.ofNat (11 : ℕ) (x13 / (11 : ℕ))) && x12 (Fin.ofNat (11 : ℕ) (x13 % (11 : ℕ)));               (∀ (x12 : Fin (9 : ℕ) → Bool), x11 (x2.insertNth Bool.false x12) ≠ x11 (x2.insertNth Bool.true x12) → x3.eval (List.ofFn x12) = Bool.false) → ∃ (x13 : Fin (9 : ℕ) → Bool) (x14 : Bool), x4.eval (x3.wires (List.ofFn x13) ++ [x14 || x3.eval (List.ofFn x13)]) ≠ x11 (x2.insertNth x14 x13)) :=
  fun x1 x2 x3 x4 hLt hAO3 hAO4 hSz _ hOut _ =>
    (hCompile x2 x3 x4 hAO3 hAO4 hSz hOut).elim fun c hc =>
      (hNoCircuit18 x1 c hLt hc.1 hc.2.1).elim fun x8 hx8 =>
        ⟨x2.removeNth x8, x8 x2, fun hEq =>
          hx8 ((hc.2.2 x8).trans (hEq.trans (congrArg
            (fun (x11 : Fin (10 : ℕ) → Bool) =>
              have x10 : Fin (11 : ℕ) → Bool := x1.insertNth Bool.false x11
              [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ),
               (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)].any
                fun (x13 : ℕ) => x10 (Fin.ofNat (11 : ℕ) (x13 / (11 : ℕ))) && x10 (Fin.ofNat (11 : ℕ) (x13 % (11 : ℕ))))
            (Fin.insertNth_self_removeNth x2 x8))))⟩
