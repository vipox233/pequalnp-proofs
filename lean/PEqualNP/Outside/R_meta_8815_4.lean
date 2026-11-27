import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8815_4
    (hNorm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      G.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsAO2 n C →
      PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.TopForm.TopForm G D ∧ D.size ≤ C.size)
    (hTopLB : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (p : Equiv.Perm (Fin n))
      (G : SimpleGraph (Fin (n + n))) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
      (0 : ℕ) < n →
      (∀ a a' b b' : Fin n, a ≠ a' → b ≠ b' → ¬((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)) →
      (∀ a : Fin n, (a, p a) ∈ E) →
      (∀ u v : Fin (n + n), G.Adj u v ↔ ∃ a b : Fin n, (a, b) ∈ E ∧
        ((u = Fin.castAdd n a ∧ v = Fin.natAdd n b) ∨ (v = Fin.castAdd n a ∧ u = Fin.natAdd n b))) →
      PEqualNP.TopForm.IsLeastAO G D →
      PEqualNP.TopForm.TopForm G D →
      E.card + n ≤ D.size + (1 : ℕ)) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (0 : ℕ) < x1 →     (∀ (x6 x7 x8 x9 : Fin x1), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x2 ∧ (x6, x9) ∈ x2 ∧ (x7, x8) ∈ x2 ∧ (x7, x9) ∈ x2)) →       (∀ (x7 : Fin x1), (x7, x3 x7) ∈ x2) →         PEqualNP.TopForm.IsAO2 (x1 + x1) x4 →           (∀ (x9 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), (x10, x11) ∈ x2 ∧ x9 (Fin.castAdd x1 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) →             have x10 : List ℕ := x4.output :: List.flatMap (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => x10.inputs) x4.gates;             x2.card ≤ x1 + (x10.length - x10.toFinset.card) := by
  classical
  intro x1 x2 x3 x4 hpos hc4 hmatch hAO hfun
  let adj : Fin (x1 + x1) → Fin (x1 + x1) → Prop := fun a b =>
    ∃ u v : Fin x1, (u, v) ∈ x2 ∧
      ((a = Fin.castAdd x1 u ∧ b = Fin.natAdd x1 v) ∨
       (b = Fin.castAdd x1 u ∧ a = Fin.natAdd x1 v))
  let G : SimpleGraph (Fin (x1 + x1)) :=
    { Adj := adj
      symm := ⟨by
        rintro a b ⟨u, v, huv, hor⟩
        exact ⟨u, v, huv, hor.symm⟩⟩
      loopless := ⟨by
        rintro a ⟨u, v, _, hor⟩
        rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hv := congrArg Fin.val (h1.symm.trans h2)
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          omega
        · have hv := congrArg Fin.val (h1.symm.trans h2)
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          omega⟩ }
  have hG : ∀ a b : Fin (x1 + x1), G.Adj a b ↔
      ∃ u v : Fin x1, (u, v) ∈ x2 ∧
        ((a = Fin.castAdd x1 u ∧ b = Fin.natAdd x1 v) ∨
         (b = Fin.castAdd x1 u ∧ a = Fin.natAdd x1 v)) := fun _ _ => Iff.rfl
  let v0 : Fin x1 := ⟨0, hpos⟩
  have hne : G.edgeFinset.Nonempty := by
    refine ⟨s(Fin.castAdd x1 v0, Fin.natAdd x1 (x3 v0)), ?_⟩
    rw [SimpleGraph.mem_edgeFinset]
    exact ⟨v0, x3 v0, hmatch v0, Or.inl ⟨rfl, rfl⟩⟩
  have hcfun : PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
    funext z
    rw [hfun z]
    change decide (∃ u v : Fin x1, (u, v) ∈ x2 ∧ z (Fin.castAdd x1 u) = true ∧ z (Fin.natAdd x1 v) = true) =
      (decide (∃ a ∈ (∅ : Finset (Fin (x1 + x1))), z a = true) ||
       decide (∃ a b : Fin (x1 + x1), G.Adj a b ∧ z a = true ∧ z b = true))
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      exact ⟨Fin.castAdd x1 u, Fin.natAdd x1 v, ⟨u, v, huv, Or.inl ⟨rfl, rfl⟩⟩, hu, hv⟩
    · rintro ⟨a, b, ⟨u, v, huv, hor⟩, ha, hb⟩
      rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨u, v, huv, ha, hb⟩
      · exact ⟨u, v, huv, hb, ha⟩
  obtain ⟨D, hLeast, hTF, hDle⟩ := hNorm (x1 + x1) G x4 hne hAO hcfun
  have hSizeLB : x2.card + x1 ≤ x4.size + 1 :=
    Nat.le_trans (hTopLB x1 x2 x3 G D hpos hc4 hmatch hG hLeast hTF) (Nat.add_le_add_right hDle 1)
  have hflat : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, g.inputs.length = 2) →
      (gs.flatMap (fun g => g.inputs)).length = 2 * gs.length := by
    intro gs
    induction gs with
    | nil => intro _; rfl
    | cons g gs ih =>
      intro hg
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have h1 : g.inputs.length = 2 := hg g List.mem_cons_self
      have h2 := ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      omega
  have hfold : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (init : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init).length =
        init.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro init; rfl
    | cons g gs ih =>
      intro init
      change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (init ++ [g.op.eval (g.inputs.map fun i => init.getD i false)])).length =
        init.length + (gs.length + 1)
      rw [ih, List.length_append]
      change init.length + 1 + gs.length = init.length + (gs.length + 1)
      omega
  have hout_lt : x4.output < x1 + x1 + x4.size := by
    let f : Fin (x1 + x1) → Bool := fun i => decide (i = Fin.castAdd x1 v0 ∨ i = Fin.natAdd x1 (x3 v0))
    have htrue : PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 f = true := by
      rw [hfun f, decide_eq_true_eq]
      exact ⟨v0, x3 v0, hmatch v0, by simp [f], by simp [f]⟩
    have hget : (x4.wires (List.ofFn f)).getD x4.output false = true := htrue
    have hwlen : (x4.wires (List.ofFn f)).length = x1 + x1 + x4.size := by
      change (x4.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn f)).length = x1 + x1 + x4.gates.length
      rw [hfold, List.length_ofFn]
    by_contra hge
    have hle : (x4.wires (List.ofFn f)).length ≤ x4.output := by omega
    rw [List.getD_eq_default _ _ hle] at hget
    cases hget
  let x10 : List ℕ := x4.output :: List.flatMap (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs) x4.gates
  have hx10_len : x10.length = 2 * x4.size + 1 := by
    change (List.flatMap (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs) x4.gates).length + 1 =
      2 * x4.gates.length + 1
    rw [hflat x4.gates hAO.2.2]
  have hx10_sub : x10.toFinset ⊆ Finset.range (x1 + x1 + x4.size) := by
    intro w hw
    rw [Finset.mem_range]
    rw [List.mem_toFinset] at hw
    rcases List.mem_cons.mp hw with rfl | hfm
    · exact hout_lt
    · rw [List.mem_flatMap] at hfm
      rcases hfm with ⟨g, hg, hwg⟩
      rw [List.mem_iff_getElem] at hg
      rcases hg with ⟨j, hj, rfl⟩
      have hga : PEqualNP.MetaComplexity.NestedCover.gateAt x4 j = x4.gates[j]'hj :=
        List.getD_eq_getElem x4.gates ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ hj
      have hwj : w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).inputs := by
        rw [hga]; exact hwg
      have hlt : w < (x1 + x1) + j := hAO.2.1 j hj w hwj
      have hj' : j < x4.size := hj
      omega
  have hx10_card : x10.toFinset.card ≤ x1 + x1 + x4.size := by
    have := Finset.card_le_card hx10_sub
    rwa [Finset.card_range] at this
  change x2.card ≤ x1 + (x10.length - x10.toFinset.card)
  omega
