import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17549_1
    (hDecomp :
      ∀ (pre post : List (Fin (32 : ℕ) × Fin (32 : ℕ))) (ab : Fin (32 : ℕ) × Fin (32 : ℕ)),
        have mk : List (Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) :=
          pre.map (fun (p : Fin (32 : ℕ) × Fin (32 : ℕ)) => (Bool.false, p)) ++
            (Bool.true, ab) :: post.map (fun (p : Fin (32 : ℕ) × Fin (32 : ℕ)) => (Bool.false, p));
        mk.length = pre.length + (1 : ℕ) + post.length ∧
        (List.filter (fun (g : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => g.1) mk).length = (1 : ℕ) ∧
        ∀ (i : Fin mk.length), (mk.get i).1 = Bool.true → (i : ℕ) = pre.length)
    (hDecomposed :
      ∃ (pre post x2 : List (Fin (32 : ℕ) × Fin (32 : ℕ))) (ab : Fin (32 : ℕ) × Fin (32 : ℕ)),
        have x1 : List (Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) :=
          pre.map (fun (p : Fin (32 : ℕ) × Fin (32 : ℕ)) => (Bool.false, p)) ++
            (Bool.true, ab) :: post.map (fun (p : Fin (32 : ℕ) × Fin (32 : ℕ)) => (Bool.false, p));
        have x3 : List ℕ := List.foldl (fun (x3 : List ℕ) (x4 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x3 ++ [if x4.1 = Bool.true then x3.getD ↑x4.2.1 (0 : ℕ) &&& x3.getD ↑x4.2.2 (0 : ℕ) else x3.getD ↑x4.2.1 (0 : ℕ) ||| x3.getD ↑x4.2.2 (0 : ℕ)]) [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ), (371245215936 : ℕ), (582520731713 : ℕ), (1066477318818 : ℕ), (549755842560 : ℕ), (728266404032 : ℕ)] x1;
        have x4 : Fin (32 : ℕ) × Fin (32 : ℕ) → ℕ := fun (x4 : Fin (32 : ℕ) × Fin (32 : ℕ)) => x3.getD ↑x4.1 (0 : ℕ) &&& x3.getD ↑x4.2 (0 : ℕ);
        (pre.length + (1 : ℕ) + post.length) + (2 : ℕ) * x2.length ≤ (15 : ℕ) ∧
        (∀ (x5 : Fin x1.length), ↑(x1.get x5).2.1 < (16 : ℕ) + ↑x5 ∧ ↑(x1.get x5).2.2 < (16 : ℕ) + ↑x5) ∧
        x3.getD ((16 : ℕ) + pre.length) (0 : ℕ) &&& (1099511562240 : ℕ) ≠ (0 : ℕ) ∧
        (∀ x5 ∈ x2, ↑x5.1 < (16 : ℕ) + (pre.length + (1 : ℕ) + post.length) ∧ ↑x5.2 < (16 : ℕ) + (pre.length + (1 : ℕ) + post.length) ∧ x4 x5 &&& (1099511562240 : ℕ) = (0 : ℕ)) ∧
        List.foldl (fun (x5 : ℕ) (x6 : Fin (32 : ℕ) × Fin (32 : ℕ)) => x5 ||| x4 x6) (28864 : ℕ) x2 = (65535 : ℕ)) :
    (∃ (x1 : List (Bool × Fin (32 : ℕ) × Fin (32 : ℕ))) (x2 : List (Fin (32 : ℕ) × Fin (32 : ℕ))),   have x3 : List ℕ := List.foldl (fun (x3 : List ℕ) (x4 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x3 ++ [if x4.1 = Bool.true then x3.getD ↑x4.2.1 (0 : ℕ) &&& x3.getD ↑x4.2.2 (0 : ℕ) else x3.getD ↑x4.2.1 (0 : ℕ) ||| x3.getD ↑x4.2.2 (0 : ℕ)]) [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ), (371245215936 : ℕ), (582520731713 : ℕ), (1066477318818 : ℕ), (549755842560 : ℕ), (728266404032 : ℕ)] x1;   have x4 : Fin (32 : ℕ) × Fin (32 : ℕ) → ℕ := fun (x4 : Fin (32 : ℕ) × Fin (32 : ℕ)) => x3.getD ↑x4.1 (0 : ℕ) &&& x3.getD ↑x4.2 (0 : ℕ);   x1.length + (2 : ℕ) * x2.length ≤ (15 : ℕ) ∧ (∀ (x5 : Fin x1.length), ↑(x1.get x5).2.1 < (16 : ℕ) + ↑x5 ∧ ↑(x1.get x5).2.2 < (16 : ℕ) + ↑x5) ∧ (List.filter (fun (x5 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x5.1) x1).length = (1 : ℕ) ∧ (∀ (x5 : Fin x1.length), (x1.get x5).1 = Bool.true → x3.getD ((16 : ℕ) + ↑x5) (0 : ℕ) &&& (1099511562240 : ℕ) ≠ (0 : ℕ)) ∧ (∀ x5 ∈ x2, ↑x5.1 < (16 : ℕ) + x1.length ∧ ↑x5.2 < (16 : ℕ) + x1.length ∧ x4 x5 &&& (1099511562240 : ℕ) = (0 : ℕ)) ∧ List.foldl (fun (x5 : ℕ) (x6 : Fin (32 : ℕ) × Fin (32 : ℕ)) => x5 ||| x4 x6) (28864 : ℕ) x2 = (65535 : ℕ)) :=
  Exists.elim hDecomposed fun pre h1 =>
    Exists.elim h1 fun post h2 =>
      Exists.elim h2 fun x2 h3 =>
        Exists.elim h3 fun ab h =>
          have hd := hDecomp pre post ab
          let x1 : List (Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) :=
            pre.map (fun p => (Bool.false, p)) ++ (Bool.true, ab) :: post.map (fun p => (Bool.false, p))
          ⟨x1, x2,
            Eq.subst (motive := fun n => n + (2 : ℕ) * x2.length ≤ (15 : ℕ)) hd.1.symm h.1,
            h.2.1,
            hd.2.1,
            fun i hi =>
              Eq.subst (motive := fun k => (List.foldl (fun (x3 : List ℕ) (x4 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x3 ++ [if x4.1 = Bool.true then x3.getD ↑x4.2.1 (0 : ℕ) &&& x3.getD ↑x4.2.2 (0 : ℕ) else x3.getD ↑x4.2.1 (0 : ℕ) ||| x3.getD ↑x4.2.2 (0 : ℕ)]) [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ), (371245215936 : ℕ), (582520731713 : ℕ), (1066477318818 : ℕ), (549755842560 : ℕ), (728266404032 : ℕ)] x1).getD ((16 : ℕ) + k) (0 : ℕ) &&& (1099511562240 : ℕ) ≠ (0 : ℕ))
                (hd.2.2 i hi).symm h.2.2.1,
            fun p hp =>
              have hpp := h.2.2.2.1 p hp
              ⟨Eq.subst (motive := fun n => (p.1 : ℕ) < (16 : ℕ) + n) hd.1.symm hpp.1,
               Eq.subst (motive := fun n => (p.2 : ℕ) < (16 : ℕ) + n) hd.1.symm hpp.2.1,
               hpp.2.2⟩,
            h.2.2.2.2⟩
