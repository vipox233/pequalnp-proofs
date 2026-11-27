import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17485_3
    (hDualSpec :
      ∀ (x6 : List ℕ),
        List.foldl (fun (a b : ℕ) => a ||| b) (0 : ℕ)
          (List.map (fun (l : ℕ) => x6.getD ((13 : ℕ) + l) (0 : ℕ) &&& List.foldl (fun (a b : ℕ) => a ||| b) (0 : ℕ) (List.map (fun (d : ℕ) => x6.getD ((d + (13 : ℕ) - l) % (13 : ℕ)) (0 : ℕ)) [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])) (List.range (13 : ℕ))) =
        List.foldl (fun (a b : ℕ) => a ||| b) (0 : ℕ)
          (List.map (fun (p : ℕ) => x6.getD p (0 : ℕ) &&& List.foldl (fun (a b : ℕ) => a ||| b) (0 : ℕ) (List.map (fun (d : ℕ) => x6.getD ((13 : ℕ) + (d + (13 : ℕ) - p) % (13 : ℕ)) (0 : ℕ)) [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])) (List.range (13 : ℕ))))
    (hDualCircuit :
      have x1 : List ℕ → Bool × ℕ × ℕ → List ℕ := fun (x1 : List ℕ) (x2 : Bool × ℕ × ℕ) => x1 ++ [if x2.1 = Bool.true then x1.getD x2.2.1 (0 : ℕ) ||| x1.getD x2.2.2 (0 : ℕ) else x1.getD x2.2.1 (0 : ℕ) &&& x1.getD x2.2.2 (0 : ℕ)]
      have x2d : List ℕ → ℕ := fun (x6 : List ℕ) => List.foldl (fun (a b : ℕ) => a ||| b) (0 : ℕ) (List.map (fun (p : ℕ) => x6.getD p (0 : ℕ) &&& List.foldl (fun (a b : ℕ) => a ||| b) (0 : ℕ) (List.map (fun (d : ℕ) => x6.getD ((13 : ℕ) + (d + (13 : ℕ) - p) % (13 : ℕ)) (0 : ℕ)) [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])) (List.range (13 : ℕ)))
      ∃ (x3 : List (Fin (13 : ℕ))) (x4 : List (Bool × ℕ × ℕ)),
        x3.length = (7 : ℕ) ∧
        ((0 : Fin (13 : ℕ)) :: x3).Nodup ∧
        x4.length ≤ (24 : ℕ) ∧
        have x5 : List (Bool × ℕ × ℕ) :=
          List.flatMap
            (fun (x5 : ℕ) =>
              have x6 : ℕ := ↑(((0 : Fin (13 : ℕ)) :: x3).getD x5 (0 : Fin (13 : ℕ)))
              have x7 : ℕ → ℕ := fun (x7 : ℕ) => (x7 + (13 : ℕ) - x6) % (13 : ℕ)
              have x8 : ℕ := (26 : ℕ) + ((5 : ℕ) * x5 - (1 : ℕ))
              [(Bool.true, x7 (0 : ℕ), x7 (1 : ℕ)), (Bool.true, x7 (3 : ℕ), x7 (9 : ℕ)), (Bool.true, x8, x8 + (1 : ℕ)), (Bool.false, (13 : ℕ) + x6, x8 + (2 : ℕ))] ++ if x5 = (0 : ℕ) then [] else [(Bool.true, x8 - (1 : ℕ), x8 + (3 : ℕ))])
            (List.range (8 : ℕ))
        ∀ (x6 : List ℕ), x6.length = (26 : ℕ) → (List.foldl x1 (List.foldl x1 x6 x5) x4).getLastD (0 : ℕ) = x2d x6) :
    (have x1 : List ℕ → Bool × ℕ × ℕ → List ℕ := fun (x1 : List ℕ) (x2 : Bool × ℕ × ℕ) => x1 ++ [if x2.1 = Bool.true then x1.getD x2.2.1 (0 : ℕ) ||| x1.getD x2.2.2 (0 : ℕ) else x1.getD x2.2.1 (0 : ℕ) &&& x1.getD x2.2.2 (0 : ℕ)]; have x2 : List ℕ → ℕ := fun (x2 : List ℕ) => List.foldl (fun (x3 x4 : ℕ) => x3 ||| x4) (0 : ℕ) (List.map (fun (x3 : ℕ) => x2.getD ((13 : ℕ) + x3) (0 : ℕ) &&& List.foldl (fun (x4 x5 : ℕ) => x4 ||| x5) (0 : ℕ) (List.map (fun (x4 : ℕ) => x2.getD ((x4 + (13 : ℕ) - x3) % (13 : ℕ)) (0 : ℕ)) [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])) (List.range (13 : ℕ))); ∃ (x3 : List (Fin (13 : ℕ))) (x4 : List (Bool × ℕ × ℕ)),   x3.length = (7 : ℕ) ∧     ((0 : Fin (13 : ℕ)) :: x3).Nodup ∧       x4.length ≤ (24 : ℕ) ∧         have x5 : List (Bool × ℕ × ℕ) :=           List.flatMap             (fun (x5 : ℕ) =>               have x6 : ℕ := ↑(((0 : Fin (13 : ℕ)) :: x3).getD x5 (0 : Fin (13 : ℕ)));               have x7 : ℕ → ℕ := fun (x7 : ℕ) => (x7 + (13 : ℕ) - x6) % (13 : ℕ);               have x8 : ℕ := (26 : ℕ) + ((5 : ℕ) * x5 - (1 : ℕ));               [(Bool.true, x7 (0 : ℕ), x7 (1 : ℕ)), (Bool.true, x7 (3 : ℕ), x7 (9 : ℕ)), (Bool.true, x8, x8 + (1 : ℕ)), (Bool.false, (13 : ℕ) + x6, x8 + (2 : ℕ))] ++ if x5 = (0 : ℕ) then [] else [(Bool.true, x8 - (1 : ℕ), x8 + (3 : ℕ))])             (List.range (8 : ℕ));         ∀ (x6 : List ℕ), x6.length = (26 : ℕ) → (List.foldl x1 (List.foldl x1 x6 x5) x4).getLastD (0 : ℕ) = x2 x6) := by
  obtain ⟨x3, x4, h7, hNd, h24, hEv⟩ := hDualCircuit
  exact ⟨x3, x4, h7, hNd, h24, fun x6 h6 => (hEv x6 h6).trans (hDualSpec x6).symm⟩
