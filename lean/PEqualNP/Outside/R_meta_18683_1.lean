import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18683_1
    (hFoldStep : ∀ (init : List ℕ) (ops : List (Bool × ℕ × ℕ)),
      init.length = (11 : ℕ) →
        ops.length = (21 : ℕ) →
          (∀ (j : Fin (21 : ℕ)), (ops.getD ↑j (Bool.false, (0 : ℕ), (0 : ℕ))).2.1 < (11 : ℕ) + ↑j ∧ (ops.getD ↑j (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 < (11 : ℕ) + ↑j) →
            have vals : List ℕ := List.foldl (fun (acc : List ℕ) (g : Bool × ℕ × ℕ) => acc ++ [if g.1 = Bool.true then acc.getD g.2.1 (0 : ℕ) ||| acc.getD g.2.2 (0 : ℕ) else acc.getD g.2.1 (0 : ℕ) &&& acc.getD g.2.2 (0 : ℕ)]) init ops;
            (∀ (i : Fin (11 : ℕ)), vals.getD ↑i (0 : ℕ) = init.getD ↑i (0 : ℕ)) ∧
              ∀ (j : Fin (21 : ℕ)), ∃ (a : Fin ((11 : ℕ) + ↑j)) (b : Fin ((11 : ℕ) + ↑j)), vals.getD ((11 : ℕ) + ↑j) (0 : ℕ) = vals.getD ↑a (0 : ℕ) ||| vals.getD ↑b (0 : ℕ) ∨ vals.getD ((11 : ℕ) + ↑j) (0 : ℕ) = vals.getD ↑a (0 : ℕ) &&& vals.getD ↑b (0 : ℕ))
    (hWitnessOps : ∃ (ops : List (Bool × ℕ × ℕ)),
      ops.length = (21 : ℕ) ∧
        (∀ (j : Fin (21 : ℕ)), (ops.getD ↑j (Bool.false, (0 : ℕ), (0 : ℕ))).2.1 < (11 : ℕ) + ↑j ∧ (ops.getD ↑j (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 < (11 : ℕ) + ↑j) ∧
          ∃ (x2 : Fin (32 : ℕ)), (List.foldl (fun (acc : List ℕ) (g : Bool × ℕ × ℕ) => acc ++ [if g.1 = Bool.true then acc.getD g.2.1 (0 : ℕ) ||| acc.getD g.2.2 (0 : ℕ) else acc.getD g.2.1 (0 : ℕ) &&& acc.getD g.2.2 (0 : ℕ)]) [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)] ops).getD ↑x2 (0 : ℕ) = (65535 : ℕ)) :
    ∃ (x1 : ℕ → ℕ), (∀ (x2 : Fin (11 : ℕ)), x1 ↑x2 = [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD ↑x2 (0 : ℕ)) ∧ (∃ (x2 : Fin (32 : ℕ)), x1 ↑x2 = (65535 : ℕ)) ∧ ∀ (x2 : Fin (21 : ℕ)), ∃ (x3 : Fin ((11 : ℕ) + ↑x2)) (x4 : Fin ((11 : ℕ) + ↑x2)), x1 ((11 : ℕ) + ↑x2) = x1 ↑x3 ||| x1 ↑x4 ∨ x1 ((11 : ℕ) + ↑x2) = x1 ↑x3 &&& x1 ↑x4 :=
  Exists.elim hWitnessOps fun ops h =>
    let init : List ℕ := [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)]
    let vals : List ℕ := List.foldl (fun (acc : List ℕ) (g : Bool × ℕ × ℕ) => acc ++ [if g.1 = Bool.true then acc.getD g.2.1 (0 : ℕ) ||| acc.getD g.2.2 (0 : ℕ) else acc.getD g.2.1 (0 : ℕ) &&& acc.getD g.2.2 (0 : ℕ)]) init ops
    let hf := hFoldStep init ops rfl h.1 h.2.1
    ⟨fun k => vals.getD k (0 : ℕ), hf.1, h.2.2, hf.2⟩
