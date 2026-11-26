import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_19004_1
    (hDrop : ∀ D : Circuit, Monotone2 D → (∀ (x5 x6 : Finset (Fin 13)), D.eval (List.ofFn fun x7 : Fin 26 => if x7.val < 13 then decide (Fin.ofNat 13 x7.val ∈ x5) else decide (Fin.ofNat 13 x7.val ∈ x6)) = true ↔ ∃ x7 ∈ x5, ∃ x8 ∈ x6, (x7.val + x8.val) % 13 ∈ [0, 1, 3, 9]) → 50 ≤ {j : ℕ | ∃ g : Gate, D.gates[j]? = some g ∧ g.op = GateOp.or}.ncard)
    (hBin : ∀ C : Circuit, Monotone2 C → C.output + 1 = 26 + C.gates.length → (∃ a b : ℕ, a < 25 + C.gates.length ∧ b < 25 + C.gates.length ∧ a ≠ b ∧ C.gates.getLast? = some ⟨GateOp.or, [a, b]⟩) → (∀ (x5 x6 : Finset (Fin 13)), C.eval (List.ofFn fun x7 : Fin 26 => if x7.val < 13 then decide (Fin.ofNat 13 x7.val ∈ x5) else decide (Fin.ofNat 13 x7.val ∈ x6)) = true ↔ ∃ x7 ∈ x5, ∃ x8 ∈ x6, (x7.val + x8.val) % 13 ∈ [0, 1, 3, 9]) → 51 ≤ {j : ℕ | ∃ g : Gate, C.gates[j]? = some g ∧ g.op = GateOp.or}.ncard) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.output + (1 : ℕ) = (26 : ℕ) + x1.gates.length → (∃ (x4 : List ℕ), x1.gates.getLast? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x4 : PEqualNP.CircuitLowerBounds.Gate }) → (∀ (x5 x6 : Finset (Fin (13 : ℕ))), x1.eval (List.ofFn fun (x7 : Fin (26 : ℕ)) => if ↑x7 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x7 ∈ x5) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x7 ∈ x6)) = Bool.true ↔ ∃ x7 ∈ x5, ∃ x8 ∈ x6, (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → (51 : ℕ) ≤ {x6 : ℕ | ∃ (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard) := by
  intro C hMono hOut hLast hComp
  obtain ⟨cgs, co⟩ := C
  dsimp only at hMono hOut hLast hComp ⊢
  obtain ⟨ins, hLast'⟩ := hLast
  obtain ⟨gs, hgs⟩ := List.getLast?_eq_some_iff.mp hLast'
  subst hgs
  have hco : co = 26 + gs.length := by
    simp only [List.length_append, List.length_singleton] at hOut
    omega
  let stp : List Bool → Gate → List Bool := fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hFoldLen : ∀ (l : List Gate) (xs : List Bool), (l.foldl stp xs).length = xs.length + l.length := by
    intro l xs
    induction l using List.reverseRecOn with
    | nil => simp
    | append_singleton l g ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hstepLen : ∀ w : List Bool, (stp w g).length = w.length + 1 := fun w => by simp [stp]
      rw [hstepLen, ih, List.length_append, List.length_singleton]
      omega
  have hGetLast : ∀ (l : List Bool) (v : Bool), (l ++ [v]).getD l.length false = v := by
    intro l v
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
    rfl
  have hStepEval : ∀ (w : List Bool) (g : Gate), (stp w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
    intro w g
    dsimp only [stp]
    exact hGetLast w _
  have hOr0 : GateOp.or.eval [] = false := rfl
  have hOr1 : ∀ u : Bool, GateOp.or.eval [u] = u := fun u => by cases u <;> rfl
  have hOr2 : ∀ u v : Bool, GateOp.or.eval [u, v] = (u || v) := fun u v => by cases u <;> cases v <;> rfl
  have hOR : {j : ℕ | ∃ g : Gate, gs[j]? = some g ∧ g.op = GateOp.or}.ncard + 1 =
      {j : ℕ | ∃ g : Gate, (gs ++ [({ op := GateOp.or, inputs := ins } : Gate)])[j]? = some g ∧ g.op = GateOp.or}.ncard := by
    let S0 : Set ℕ := {j : ℕ | ∃ g : Gate, gs[j]? = some g ∧ g.op = GateOp.or}
    let S1 : Set ℕ := {j : ℕ | ∃ g : Gate, (gs ++ [({ op := GateOp.or, inputs := ins } : Gate)])[j]? = some g ∧ g.op = GateOp.or}
    have hEqS : S1 = insert gs.length S0 := by
      ext j
      simp only [S1, S0, Set.mem_ofPred_eq, Set.mem_insert_iff]
      rcases Nat.lt_trichotomy j gs.length with hlt | rfl | hgt
      · have hne : j ≠ gs.length := by omega
        rw [List.getElem?_append_left hlt]
        exact ⟨fun h => Or.inr h, fun h => h.elim (fun he => absurd he hne) id⟩
      · rw [List.getElem?_append_right (le_refl _), Nat.sub_self]
        simp
      · have h1 : (gs ++ [({ op := GateOp.or, inputs := ins } : Gate)])[j]? = none := List.getElem?_eq_none (by simp; omega)
        have h2 : gs[j]? = none := List.getElem?_eq_none (by omega)
        rw [h1, h2]
        simp [show j ≠ gs.length by omega]
    have hNotMem : gs.length ∉ S0 := by
      intro hm
      rcases hm with ⟨g, hg, _⟩
      rw [List.getElem?_eq_none (le_refl _)] at hg
      simp at hg
    have hFin : S0.Finite := by
      refine Set.Finite.subset (Finset.range gs.length).finite_toSet ?_
      intro j hj
      rcases hj with ⟨g, hg, _⟩
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hge
      rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hg
      simp at hg
    change S0.ncard + 1 = S1.ncard
    rw [hEqS, Set.ncard_insert_of_notMem hNotMem hFin]
  have hInsLen : ins.length ≤ 2 := (hMono ({ op := GateOp.or, inputs := ins } : Gate) (by simp)).2
  have hGsMono : ∀ w : ℕ, Monotone2 (⟨gs, w⟩ : Circuit) :=
    fun _ g hg => hMono g (List.mem_append_left _ hg)
  cases ins with
  | nil =>
    let zs : Finset (Fin 13) := {0}
    have hEvalT : (⟨gs ++ [({ op := GateOp.or, inputs := [] } : Gate)], co⟩ : Circuit).eval (List.ofFn fun x7 : Fin 26 =>
        if x7.val < 13 then decide (Fin.ofNat 13 x7.val ∈ zs)
        else decide (Fin.ofNat 13 x7.val ∈ zs)) = true :=
      (hComp zs zs).mpr ⟨0, by simp [zs], 0, by simp [zs], by decide⟩
    let xs : List Bool := List.ofFn fun x7 : Fin 26 =>
        if x7.val < 13 then decide (Fin.ofNat 13 x7.val ∈ zs)
        else decide (Fin.ofNat 13 x7.val ∈ zs)
    have hlen : (gs.foldl stp xs).length = co := by rw [hFoldLen, hco]; simp [xs]
    change ((gs ++ [({ op := GateOp.or, inputs := [] } : Gate)]).foldl stp xs).getD co false = true at hEvalT
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← hlen, hStepEval, List.map_nil, hOr0] at hEvalT
    exact False.elim (Bool.false_ne_true hEvalT)
  | cons a rest =>
    cases rest with
    | nil =>
      have hD : 50 ≤ {j : ℕ | ∃ g : Gate, gs[j]? = some g ∧ g.op = GateOp.or}.ncard := by
        refine hDrop ⟨gs, a⟩ (hGsMono a) fun x5 x6 => ?_
        let xs : List Bool := List.ofFn fun x7 : Fin 26 =>
          if x7.val < 13 then decide (Fin.ofNat 13 x7.val ∈ x5) else decide (Fin.ofNat 13 x7.val ∈ x6)
        have hlen : (gs.foldl stp xs).length = co := by rw [hFoldLen, hco]; simp [xs]
        have heq : (⟨gs, a⟩ : Circuit).eval xs = (⟨gs ++ [({ op := GateOp.or, inputs := [a] } : Gate)], co⟩ : Circuit).eval xs := by
          change (gs.foldl stp xs).getD a false = ((gs ++ [({ op := GateOp.or, inputs := [a] } : Gate)]).foldl stp xs).getD co false
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← hlen, hStepEval, List.map_cons, List.map_nil, hOr1]
        rw [heq]
        exact hComp x5 x6
      omega
    | cons b tail =>
      have htail : tail = [] := by
        simp only [List.length_cons] at hInsLen
        exact List.eq_nil_of_length_eq_zero (by omega)
      subst htail
      by_cases hab : a = b
      · subst hab
        have hD : 50 ≤ {j : ℕ | ∃ g : Gate, gs[j]? = some g ∧ g.op = GateOp.or}.ncard := by
          refine hDrop ⟨gs, a⟩ (hGsMono a) fun x5 x6 => ?_
          let xs : List Bool := List.ofFn fun x7 : Fin 26 =>
            if x7.val < 13 then decide (Fin.ofNat 13 x7.val ∈ x5) else decide (Fin.ofNat 13 x7.val ∈ x6)
          have hlen : (gs.foldl stp xs).length = co := by rw [hFoldLen, hco]; simp [xs]
          have heq : (⟨gs, a⟩ : Circuit).eval xs = (⟨gs ++ [({ op := GateOp.or, inputs := [a, a] } : Gate)], co⟩ : Circuit).eval xs := by
            change (gs.foldl stp xs).getD a false = ((gs ++ [({ op := GateOp.or, inputs := [a, a] } : Gate)]).foldl stp xs).getD co false
            rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← hlen, hStepEval, List.map_cons, List.map_cons, List.map_nil]
            dsimp only
            rw [hOr2, Bool.or_self]
          rw [heq]
          exact hComp x5 x6
        omega
      · by_cases ha : a < 26 + gs.length
        · by_cases hb : b < 26 + gs.length
          · exact hBin ⟨gs ++ [({ op := GateOp.or, inputs := [a, b] } : Gate)], co⟩ hMono hOut
              ⟨a, b, by simp; omega, by simp; omega, hab, hLast'⟩ hComp
          · have hD : 50 ≤ {j : ℕ | ∃ g : Gate, gs[j]? = some g ∧ g.op = GateOp.or}.ncard := by
              refine hDrop ⟨gs, a⟩ (hGsMono a) fun x5 x6 => ?_
              let xs : List Bool := List.ofFn fun x7 : Fin 26 =>
                if x7.val < 13 then decide (Fin.ofNat 13 x7.val ∈ x5) else decide (Fin.ofNat 13 x7.val ∈ x6)
              have hlen : (gs.foldl stp xs).length = 26 + gs.length := by rw [hFoldLen]; simp [xs]
              have hbg : (gs.foldl stp xs).getD b false = false := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlen]; omega)]
                rfl
              have heq : (⟨gs, a⟩ : Circuit).eval xs = (⟨gs ++ [({ op := GateOp.or, inputs := [a, b] } : Gate)], co⟩ : Circuit).eval xs := by
                change (gs.foldl stp xs).getD a false = ((gs ++ [({ op := GateOp.or, inputs := [a, b] } : Gate)]).foldl stp xs).getD co false
                rw [List.foldl_append, List.foldl_cons, List.foldl_nil, show co = (gs.foldl stp xs).length from by omega, hStepEval, List.map_cons, List.map_cons, List.map_nil]
                dsimp only
                rw [hbg, hOr2, Bool.or_false]
              rw [heq]
              exact hComp x5 x6
            omega
        · have hD : 50 ≤ {j : ℕ | ∃ g : Gate, gs[j]? = some g ∧ g.op = GateOp.or}.ncard := by
            refine hDrop ⟨gs, b⟩ (hGsMono b) fun x5 x6 => ?_
            let xs : List Bool := List.ofFn fun x7 : Fin 26 =>
              if x7.val < 13 then decide (Fin.ofNat 13 x7.val ∈ x5) else decide (Fin.ofNat 13 x7.val ∈ x6)
            have hlen : (gs.foldl stp xs).length = 26 + gs.length := by rw [hFoldLen]; simp [xs]
            have hag : (gs.foldl stp xs).getD a false = false := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hlen]; omega)]
              rfl
            have heq : (⟨gs, b⟩ : Circuit).eval xs = (⟨gs ++ [({ op := GateOp.or, inputs := [a, b] } : Gate)], co⟩ : Circuit).eval xs := by
              change (gs.foldl stp xs).getD b false = ((gs ++ [({ op := GateOp.or, inputs := [a, b] } : Gate)]).foldl stp xs).getD co false
              rw [List.foldl_append, List.foldl_cons, List.foldl_nil, show co = (gs.foldl stp xs).length from by omega, hStepEval, List.map_cons, List.map_cons, List.map_nil]
              dsimp only
              rw [hag, hOr2, Bool.false_or]
            rw [heq]
            exact hComp x5 x6
          omega
