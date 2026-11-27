import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18209_2
    (hNonEdgeAnd :
      have r : List (Fin (13 : ℕ)) := List.finRange (13 : ℕ)
      have pg : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun a b =>
        Decidable.decide (a - b = (0 : Fin (13 : ℕ)) ∨ a - b = (1 : Fin (13 : ℕ)) ∨ a - b = (3 : Fin (13 : ℕ)) ∨ a - b = (9 : Fin (13 : ℕ)))
      have evec : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun a b k =>
        Decidable.decide (k = Fin.castAdd (13 : ℕ) a ∨ k = Fin.natAdd (13 : ℕ) b)
      have arc : (Fin (13 : ℕ) → Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → Prop := fun q s =>
        r.countP s = (4 : ℕ) ∧ ∀ b : Fin (13 : ℕ), r.countP (fun a => s a && q a b) ≤ (2 : ℕ)
      have ind : (Fin (13 : ℕ) → Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun q s b =>
        r.all fun a => !s a || !q a b
      have sep : ((Fin (26 : ℕ) → Bool) → Bool) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun f c =>
        have ev : (Fin (26 : ℕ) → Bool) → Bool := fun v => c.eval (List.ofFn v ++ [f v])
        PEqualNP.MetaComplexity.Monotone2 c ∧ c.size ≤ (62 : ℕ) ∧
        (∀ a b : Fin (13 : ℕ), pg a b = Bool.true → ev (evec a b) = Bool.true) ∧
        (∀ s : Fin (13 : ℕ) → Bool, arc pg s → ev (Fin.append s (ind pg s)) = Bool.false) ∧
        (∀ s : Fin (13 : ℕ) → Bool, arc (fun a b => pg b a) s → ev (Fin.append (ind (fun a b => pg b a) s) s) = Bool.false)
      ∀ (f : (Fin (26 : ℕ) → Bool) → Bool) (c : PEqualNP.CircuitLowerBounds.Circuit),
        ((∀ v, f v = Bool.true) ∨ (∃ k : Fin (26 : ℕ), ∀ v, f v = v k) ∨
          (∀ a b : Fin (13 : ℕ), pg a b = Bool.true → f (evec a b) = Bool.false)) →
        sep f c → False)
    (hEdgeAnd :
      have r : List (Fin (13 : ℕ)) := List.finRange (13 : ℕ)
      have pg : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun a b =>
        Decidable.decide (a - b = (0 : Fin (13 : ℕ)) ∨ a - b = (1 : Fin (13 : ℕ)) ∨ a - b = (3 : Fin (13 : ℕ)) ∨ a - b = (9 : Fin (13 : ℕ)))
      have evec : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun a b k =>
        Decidable.decide (k = Fin.castAdd (13 : ℕ) a ∨ k = Fin.natAdd (13 : ℕ) b)
      have arc : (Fin (13 : ℕ) → Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → Prop := fun q s =>
        r.countP s = (4 : ℕ) ∧ ∀ b : Fin (13 : ℕ), r.countP (fun a => s a && q a b) ≤ (2 : ℕ)
      have ind : (Fin (13 : ℕ) → Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun q s b =>
        r.all fun a => !s a || !q a b
      have sep : ((Fin (26 : ℕ) → Bool) → Bool) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun f c =>
        have ev : (Fin (26 : ℕ) → Bool) → Bool := fun v => c.eval (List.ofFn v ++ [f v])
        PEqualNP.MetaComplexity.Monotone2 c ∧ c.size ≤ (62 : ℕ) ∧
        (∀ a b : Fin (13 : ℕ), pg a b = Bool.true → ev (evec a b) = Bool.true) ∧
        (∀ s : Fin (13 : ℕ) → Bool, arc pg s → ev (Fin.append s (ind pg s)) = Bool.false) ∧
        (∀ s : Fin (13 : ℕ) → Bool, arc (fun a b => pg b a) s → ev (Fin.append (ind (fun a b => pg b a) s) s) = Bool.false)
      ∀ (p q : Fin (13 : ℕ)) (c : PEqualNP.CircuitLowerBounds.Circuit),
        pg p q = Bool.true →
        sep (fun v => v (Fin.castAdd (13 : ℕ) p) && v (Fin.natAdd (13 : ℕ) q)) c → False) :
    (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 - x2 = (0 : Fin (13 : ℕ)) ∨ x1 - x2 = (1 : Fin (13 : ℕ)) ∨ x1 - x2 = (3 : Fin (13 : ℕ)) ∨ x1 - x2 = (9 : Fin (13 : ℕ)); have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x2 x3 : Finset (Fin (13 : ℕ))) => Fin.append (fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x2)) fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3); have x3 : PEqualNP.CircuitLowerBounds.Gate → (Fin (26 : ℕ) → Bool) → List Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Gate) (x4 : Fin (26 : ℕ) → Bool) =>   have x5 : List Bool := List.ofFn x4;   x5 ++ [x3.op.eval (List.map (fun (x6 : ℕ) => x5.getD x6 Bool.false) x3.inputs)]; ∀ (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 : PEqualNP.CircuitLowerBounds.Circuit), x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → x4.inputs.length ≤ (2 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.size ≤ (62 : ℕ) → (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → x5.eval (x3 x4 fun (x13 : Fin (26 : ℕ)) => Decidable.decide (x13 = Fin.castAdd (13 : ℕ) x10 ∨ x13 = Fin.natAdd (13 : ℕ) x11)) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) → (∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x11 | x1 x14 x13}.card ≤ (2 : ℕ)) → x5.eval (x3 x4 (x2 x11 {x14 : Fin (13 : ℕ) | ∀ x15 ∈ x11, ¬x1 x15 x14})) = Bool.false) → (∀ (x12 : Finset (Fin (13 : ℕ))), x12.card = (4 : ℕ) → (∀ (x14 : Fin (13 : ℕ)), {x15 ∈ x12 | x1 x14 x15}.card ≤ (2 : ℕ)) → x5.eval (x3 x4 (x2 {x15 : Fin (13 : ℕ) | ∀ x16 ∈ x12, ¬x1 x15 x16} x12)) = Bool.false) → False) := by
  intro x1 x2 x3 x4 x5 hOp hLen hMono hSz hPos hNegL hNegR
  let r : List (Fin 13) := List.finRange 13
  let pg : Fin 13 → Fin 13 → Bool := fun a b =>
    Decidable.decide (a - b = (0 : Fin 13) ∨ a - b = (1 : Fin 13) ∨ a - b = (3 : Fin 13) ∨ a - b = (9 : Fin 13))
  let evec : Fin 13 → Fin 13 → Fin 26 → Bool := fun a b k =>
    Decidable.decide (k = Fin.castAdd 13 a ∨ k = Fin.natAdd 13 b)
  let arc : (Fin 13 → Fin 13 → Bool) → (Fin 13 → Bool) → Prop := fun q s =>
    r.countP s = 4 ∧ ∀ b : Fin 13, r.countP (fun a => s a && q a b) ≤ 2
  let ind : (Fin 13 → Fin 13 → Bool) → (Fin 13 → Bool) → Fin 13 → Bool := fun q s b =>
    r.all fun a => !s a || !q a b
  let sep : ((Fin 26 → Bool) → Bool) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun f c =>
    have ev : (Fin 26 → Bool) → Bool := fun v => c.eval (List.ofFn v ++ [f v])
    PEqualNP.MetaComplexity.Monotone2 c ∧ c.size ≤ 62 ∧
    (∀ a b : Fin 13, pg a b = true → ev (evec a b) = true) ∧
    (∀ s : Fin 13 → Bool, arc pg s → ev (Fin.append s (ind pg s)) = false) ∧
    (∀ s : Fin 13 → Bool, arc (fun a b => pg b a) s → ev (Fin.append (ind (fun a b => pg b a) s) s) = false)
  let f : (Fin 26 → Bool) → Bool := fun v =>
    x4.op.eval (List.map (fun k => (List.ofFn v).getD k false) x4.inputs)
  have hcard : ∀ p : Fin 13 → Bool,
      (Finset.univ.filter fun a => p a = true).card = r.countP p := by
    intro p
    rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup ((List.nodup_finRange 13).filter p)]
    congr 1
    ext a
    simp
  have hget : ∀ (v : Fin 26 → Bool) (k : ℕ),
      (List.ofFn v).getD k false = if hk : k < 26 then v ⟨k, hk⟩ else false := by
    intro v k
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    by_cases hk : k < 26
    · simp only [hk, ↓reduceDIte, Option.getD_some]
    · simp only [hk, ↓reduceDIte, Option.getD_none]
  have hSep : ∀ g : (Fin 26 → Bool) → Bool, (∀ v, f v = g v) → sep g x5 := by
    intro g hfg
    refine ⟨hMono, hSz, ?_, ?_, ?_⟩
    · intro a b hab
      dsimp only
      rw [← hfg]
      exact hPos a b (of_decide_eq_true hab)
    · intro s hsh
      have hs := hsh.1
      have hdeg := hsh.2
      let S : Finset (Fin 13) := Finset.univ.filter fun a => s a = true
      have hScard : S.card = 4 := (hcard s).trans hs
      have hSdeg : ∀ b : Fin 13, (S.filter fun a => x1 a b).card ≤ 2 := by
        intro b
        have heq : S.filter (fun a => x1 a b) = Finset.univ.filter (fun a => (s a && pg a b) = true) := by
          ext a; simp [S, pg, x1]
        rw [heq, hcard]
        exact hdeg b
      have hvec : x2 S (Finset.univ.filter fun b => ∀ a ∈ S, ¬x1 a b) = Fin.append s (ind pg s) := by
        dsimp only [x2]
        congr 1
        · funext a; simp [S]
        · funext b
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq, Finset.mem_filter, Finset.mem_univ, true_and, S,
            ind, r, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true, Bool.not_eq_true',
            Bool.eq_false_iff, ne_eq, pg, x1]
          constructor
          · intro h a
            by_cases hsa : s a = true
            · exact Or.inr (h a hsa)
            · exact Or.inl hsa
          · intro h a hsa
            exact (h a).elim (fun h1 => absurd hsa h1) (fun h2 => h2)
      dsimp only
      rw [← hfg]
      have hres := hNegL S hScard hSdeg
      rw [hvec] at hres
      exact hres
    · intro s hsh
      have hs := hsh.1
      have hdeg := hsh.2
      let S : Finset (Fin 13) := Finset.univ.filter fun b => s b = true
      have hScard : S.card = 4 := (hcard s).trans hs
      have hSdeg : ∀ a : Fin 13, (S.filter fun b => x1 a b).card ≤ 2 := by
        intro a
        have heq : S.filter (fun b => x1 a b) = Finset.univ.filter (fun b => (s b && pg a b) = true) := by
          ext b; simp [S, pg, x1]
        rw [heq, hcard]
        exact hdeg a
      have hvec : x2 (Finset.univ.filter fun a => ∀ b ∈ S, ¬x1 a b) S =
          Fin.append (ind (fun a b => pg b a) s) s := by
        dsimp only [x2]
        congr 1
        · funext a
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq, Finset.mem_filter, Finset.mem_univ, true_and, S,
            ind, r, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true, Bool.not_eq_true',
            Bool.eq_false_iff, ne_eq, pg, x1]
          constructor
          · intro h b
            by_cases hsb : s b = true
            · exact Or.inr (h b hsb)
            · exact Or.inl hsb
          · intro h b hsb
            exact (h b).elim (fun h1 => absurd hsb h1) (fun h2 => h2)
        · funext b; simp [S]
      dsimp only
      rw [← hfg]
      have hres := hNegR S hScard hSdeg
      rw [hvec] at hres
      exact hres
  have hSepF : sep f x5 := hSep f (fun _ => rfl)
  have hcases : x4.inputs = [] ∨ (∃ i, x4.inputs = [i]) ∨ (∃ i j, x4.inputs = [i, j]) :=
    (List.casesOn (motive := fun l => l.length ≤ 2 → l = [] ∨ (∃ i, l = [i]) ∨ (∃ i j, l = [i, j]))
      x4.inputs
      (fun _ => Or.inl rfl)
      (fun i t1 =>
        List.casesOn (motive := fun l => (i :: l).length ≤ 2 → (i :: l) = [] ∨ (∃ a, i :: l = [a]) ∨ (∃ a b, i :: l = [a, b]))
          t1
          (fun _ => Or.inr (Or.inl ⟨i, rfl⟩))
          (fun j t2 =>
            List.casesOn (motive := fun l => (i :: j :: l).length ≤ 2 → (i :: j :: l) = [] ∨ (∃ a, i :: j :: l = [a]) ∨ (∃ a b, i :: j :: l = [a, b]))
              t2
              (fun _ => Or.inr (Or.inr ⟨i, j, rfl⟩))
              (fun k t3 hL => False.elim (by simp at hL))))) hLen
  refine hcases.elim (fun hx4 => ?_) (fun hrest => hrest.elim (fun hex1 => hex1.elim fun i hx4 => ?_) (fun hex2 => hex2.elim fun i hex2' => hex2'.elim fun j hx4 => ?_))
  · refine hNonEdgeAnd f x5 (Or.inl ?_) hSepF
    intro v
    dsimp only [f]; rw [hOp, hx4]; rfl
  · by_cases hi : i < 26
    · refine hNonEdgeAnd f x5 (Or.inr (Or.inl ⟨⟨i, hi⟩, ?_⟩)) hSepF
      intro v
      dsimp only [f]; rw [hOp, hx4]
      change ((List.ofFn v).getD i false && true) = v ⟨i, hi⟩
      rw [hget]; simp only [hi, ↓reduceDIte, Bool.and_true]
    · refine hNonEdgeAnd f x5 (Or.inr (Or.inr ?_)) hSepF
      intro a b _
      dsimp only [f]; rw [hOp, hx4]
      change ((List.ofFn _).getD i false && true) = false
      rw [hget]; simp only [hi, ↓reduceDIte, Bool.false_and]
  · by_cases hi : i < 26
    · by_cases hj : j < 26
      · by_cases hij : i = j
        · refine hNonEdgeAnd f x5 (Or.inr (Or.inl ⟨⟨i, hi⟩, ?_⟩)) hSepF
          intro v
          subst hij
          dsimp only [f]; rw [hOp, hx4]
          change ((List.ofFn v).getD i false && ((List.ofFn v).getD i false && true)) = v ⟨i, hi⟩
          rw [hget]; simp only [hi, ↓reduceDIte, Bool.and_true, Bool.and_self]
        · by_cases h1 : ∃ (hi13 : i < 13) (hj13 : 13 ≤ j), x1 ⟨i, hi13⟩ ⟨j - 13, by omega⟩
          · exact h1.elim fun hi13 h1a => h1a.elim fun hj13 hpg => by
              let p : Fin 13 := ⟨i, hi13⟩
              let q : Fin 13 := ⟨j - 13, by omega⟩
              refine hEdgeAnd p q x5 (decide_eq_true hpg)
                (hSep (fun v => v (Fin.castAdd 13 p) && v (Fin.natAdd 13 q)) ?_)
              intro v
              have hp : (⟨i, hi⟩ : Fin 26) = Fin.castAdd 13 p := Fin.ext rfl
              have hq : (⟨j, hj⟩ : Fin 26) = Fin.natAdd 13 q := Fin.ext (by simp [q]; omega)
              dsimp only [f]; rw [hOp, hx4]
              change ((List.ofFn v).getD i false && ((List.ofFn v).getD j false && true)) = _
              rw [hget, hget]; simp only [hi, hj, ↓reduceDIte, hp, hq, Bool.and_true]
          · by_cases h2 : ∃ (hj13 : j < 13) (hi13 : 13 ≤ i), x1 ⟨j, hj13⟩ ⟨i - 13, by omega⟩
            · exact h2.elim fun hj13 h2a => h2a.elim fun hi13 hpg => by
                let p : Fin 13 := ⟨j, hj13⟩
                let q : Fin 13 := ⟨i - 13, by omega⟩
                refine hEdgeAnd p q x5 (decide_eq_true hpg)
                  (hSep (fun v => v (Fin.castAdd 13 p) && v (Fin.natAdd 13 q)) ?_)
                intro v
                have hp : (⟨j, hj⟩ : Fin 26) = Fin.castAdd 13 p := Fin.ext rfl
                have hq : (⟨i, hi⟩ : Fin 26) = Fin.natAdd 13 q := Fin.ext (by simp [q]; omega)
                dsimp only [f]; rw [hOp, hx4]
                change ((List.ofFn v).getD i false && ((List.ofFn v).getD j false && true)) = _
                rw [hget, hget]; simp only [hi, hj, ↓reduceDIte, hp, hq, Bool.and_true]
                exact Bool.and_comm _ _
            · refine hNonEdgeAnd f x5 (Or.inr (Or.inr ?_)) hSepF
              intro a b hab
              have hpg : x1 a b := of_decide_eq_true hab
              apply Bool.eq_false_iff.mpr
              intro hboth
              dsimp only [f] at hboth; rw [hOp, hx4] at hboth
              change ((List.ofFn (evec a b)).getD i false && ((List.ofFn (evec a b)).getD j false && true)) = true at hboth
              rw [hget, hget] at hboth
              simp only [hi, hj, ↓reduceDIte, Bool.and_true, evec, Bool.and_eq_true, decide_eq_true_eq,
                Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at hboth
              exact hboth.1.elim
                (fun hiab => hboth.2.elim
                  (fun hjab => hij (hiab.trans hjab.symm))
                  (fun hjab => h1 ⟨by omega, by omega, by
                    have ha : (⟨i, by omega⟩ : Fin 13) = a := Fin.ext (by dsimp; omega)
                    have hb : (⟨j - 13, by omega⟩ : Fin 13) = b := Fin.ext (by dsimp; omega)
                    rw [ha, hb]; exact hpg⟩))
                (fun hiab => hboth.2.elim
                  (fun hjab => h2 ⟨by omega, by omega, by
                    have ha : (⟨j, by omega⟩ : Fin 13) = a := Fin.ext (by dsimp; omega)
                    have hb : (⟨i - 13, by omega⟩ : Fin 13) = b := Fin.ext (by dsimp; omega)
                    rw [ha, hb]; exact hpg⟩)
                  (fun hjab => hij (hiab.trans hjab.symm)))
      · refine hNonEdgeAnd f x5 (Or.inr (Or.inr ?_)) hSepF
        intro a b _
        dsimp only [f]; rw [hOp, hx4]
        change ((List.ofFn _).getD i false && ((List.ofFn _).getD j false && true)) = false
        rw [hget, hget]; simp only [hi, hj, ↓reduceDIte, Bool.false_and, Bool.and_false]
    · refine hNonEdgeAnd f x5 (Or.inr (Or.inr ?_)) hSepF
      intro a b _
      dsimp only [f]; rw [hOp, hx4]
      change ((List.ofFn _).getD i false && ((List.ofFn _).getD j false && true)) = false
      rw [hget]; simp only [hi, ↓reduceDIte, Bool.false_and]
