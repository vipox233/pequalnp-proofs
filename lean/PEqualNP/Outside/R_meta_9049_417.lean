import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_9049_417
    (starJunk :
      ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit),
        (G = SimpleGraph.fromRel fun a b : Fin 26 =>
          a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) →
        IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card → C.size ≤ 63 →
        centreless G C = ∅ →
        1 ≤ (mixing G C).card →
        4 ≤ (Ustar G C).card →
        (junk G C).card + (orN G C \ lam G C).card < 2 * (Ustar G C).card →
        13 ≤ (tops G C).card + (junk G C).card →
        (∀ g ∈ junk G C, ∃ v : Fin 26, ∀ e ∈ gammaE G C g ∩ Ustar G C, v ∈ e) →
        13 + (Ustar G C).card ≤ (tops G C).card + (junk G C).card + (orN G C \ lam G C).card)
    (disjointJunk :
      ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit),
        (G = SimpleGraph.fromRel fun a b : Fin 26 =>
          a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) →
        IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card → C.size ≤ 63 →
        centreless G C = ∅ →
        1 ≤ (mixing G C).card →
        4 ≤ (Ustar G C).card →
        (junk G C).card + (orN G C \ lam G C).card < 2 * (Ustar G C).card →
        52 ≤ 4 * (tops G C).card + (Ustar G C).card →
        (∃ g ∈ junk G C, ∃ e ∈ gammaE G C g ∩ Ustar G C, ∃ f ∈ gammaE G C g ∩ Ustar G C,
          ∀ v : Fin 26, v ∈ e → v ∉ f) →
        13 + (Ustar G C).card ≤ (tops G C).card + (junk G C).card + (orN G C \ lam G C).card)
    (withCentreless :
      ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit),
        (G = SimpleGraph.fromRel fun a b : Fin 26 =>
          a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) →
        IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card → C.size ≤ 63 →
        (centreless G C).Nonempty →
        4 ≤ (Ustar G C).card →
        52 ≤ 4 * (tops G C \ centreless G C).card + (Ustar G C).card →
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2 * (Ustar G C).card →
        (∃ g ∈ centreless G C ∪ junk G C ∪ mixing G C, 2 ≤ (gammaE G C g ∩ Ustar G C).card) →
        13 + (Ustar G C).card ≤
          (tops G C \ centreless G C).card + 2 * (centreless G C).card +
          (junk G C).card + (orN G C \ lam G C).card) :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),
      (x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) =>
        ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →
      PEqualNP.TopForm.IsLeastAO x1 x3 →
      PEqualNP.TopForm.TopForm x1 x3 →
      (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card →
      x3.size ≤ (63 : ℕ) →
      (13 : ℕ) + (PEqualNP.TopForm.Ustar x1 x3).card ≤
        (PEqualNP.TopForm.tops x1 x3 \ PEqualNP.TopForm.centreless x1 x3).card +
        (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card +
        (PEqualNP.TopForm.junk x1 x3).card +
        (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card := by
  classical
  let _ : DecidableEq GateOp := gateOpDecEq
  intro G inst C hG hL hT hJ hSize
  let rel0 : Fin 26 → Fin 26 → Prop := fun a b =>
    a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)
  have hAdj : ∀ u v : Fin 26, G.Adj u v ↔ rel0 u v ∨ rel0 v u := by
    intro u v
    rw [hG, SimpleGraph.fromRel_adj]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rintro rfl
      rcases h with h | h <;> dsimp only [rel0] at h <;> omega
  let shifts : Fin 4 → Fin 13 := fun k =>
    if k.val = 0 then 0 else if k.val = 1 then 1 else if k.val = 2 then 3 else 9
  have hShiftMem : ∀ k : Fin 4, (shifts k).val ∈ ([0, 1, 3, 9] : List ℕ) := by
    intro k; fin_cases k <;> decide
  have hMemShift : ∀ d : Fin 13, d.val ∈ ([0, 1, 3, 9] : List ℕ) → ∃ k : Fin 4, shifts k = d := by
    intro d hd
    have hcases : d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 9 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with h | h | h | h <;> [left; (right; left); (right; right; left); (right; right; right)] <;> exact Fin.ext h
    rcases hcases with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  have hShiftInj : Function.Injective shifts := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [shifts] at hij ⊢
  have hDiffUnique : ∀ i j k l : Fin 4,
      shifts i - shifts j = shifts k - shifts l → shifts i = shifts j ∨ i = k := by
    decide
  have hNoFour : NoFourCycle G := by
    intro a b hab
    rw [Finset.card_le_one]
    intro w1 hw1 w2 hw2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
    have hside : ∀ u v : Fin 26, G.Adj u v →
        (u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨
        (v.val < 13 ∧ 13 ≤ u.val ∧ (v.val + u.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) := fun u v h => (hAdj u v).1 h
    have to13 : ∀ u v : Fin 26, G.Adj u v →
        ∃ k : Fin 4, (⟨u.val % 13, Nat.mod_lt _ (by omega)⟩ : Fin 13) +
          ⟨v.val % 13, Nat.mod_lt _ (by omega)⟩ = shifts k := by
      intro u v huv
      have hm : (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) := by
        rcases hside u v huv with ⟨_, _, h⟩ | ⟨_, _, h⟩
        · exact h
        · rwa [Nat.add_comm]
      obtain ⟨k, hk⟩ := hMemShift ⟨(u.val + v.val) % 13, Nat.mod_lt _ (by omega)⟩ hm
      refine ⟨k, ?_⟩
      rw [hk]
      apply Fin.ext
      change (u.val % 13 + v.val % 13) % 13 = (u.val + v.val) % 13
      rw [← Nat.add_mod]
    obtain ⟨k1, hk1⟩ := to13 a w1 hw1.1
    obtain ⟨l1, hl1⟩ := to13 b w1 hw1.2
    obtain ⟨k2, hk2⟩ := to13 a w2 hw2.1
    obtain ⟨l2, hl2⟩ := to13 b w2 hw2.2
    have hdiff : shifts k1 - shifts l1 = shifts k2 - shifts l2 := by
      rw [← hk1, ← hl1, ← hk2, ← hl2]
      abel
    have ha13ne : (⟨a.val % 13, Nat.mod_lt _ (by omega)⟩ : Fin 13) ≠
        ⟨b.val % 13, Nat.mod_lt _ (by omega)⟩ := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp only at hval
      rcases hside a w1 hw1.1 with ⟨ha1, hw1b, _⟩ | ⟨hw1a, ha2, _⟩ <;>
        rcases hside b w1 hw1.2 with ⟨hb1, _, _⟩ | ⟨_, hb2, _⟩
      · exact hab (Fin.ext (by omega))
      · omega
      · omega
      · exact hab (Fin.ext (by omega))
    have hkne : shifts k1 ≠ shifts l1 := by
      intro heq
      rw [← hk1, ← hl1] at heq
      exact ha13ne (add_right_cancel heq)
    have hk12 : k1 = k2 := (hDiffUnique k1 l1 k2 l2 hdiff).resolve_left hkne
    have hw13eq : (⟨w1.val % 13, Nat.mod_lt _ (by omega)⟩ : Fin 13) =
        ⟨w2.val % 13, Nat.mod_lt _ (by omega)⟩ := by
      have heq : shifts k1 = shifts k2 := congrArg shifts hk12
      rw [← hk1, ← hk2] at heq
      exact add_left_cancel heq
    have hval := congrArg Fin.val hw13eq
    dsimp only at hval
    rcases hside a w1 hw1.1 with ⟨ha1, hw1b, _⟩ | ⟨hw1a, ha2, _⟩ <;>
      rcases hside a w2 hw2.1 with ⟨_, hw2b, _⟩ | ⟨hw2a, _, _⟩
    · exact Fin.ext (by omega)
    · omega
    · omega
    · exact Fin.ext (by omega)
  have hCard52 : 52 ≤ G.edgeFinset.card := by
    let emb : Fin 13 × Fin 4 → Sym2 (Fin 26) := fun p =>
      s(Fin.castAdd 13 p.1, Fin.natAdd 13 (shifts p.2 - p.1))
    have hmem : ∀ p ∈ (Finset.univ : Finset (Fin 13 × Fin 4)), emb p ∈ G.edgeFinset := by
      intro p _
      rw [SimpleGraph.mem_edgeFinset]
      apply (hAdj _ _).2
      left
      refine ⟨p.1.isLt, by simp, ?_⟩
      simp only [Fin.val_castAdd, Fin.val_natAdd]
      have h1 : (p.1.val + (13 + (shifts p.2 - p.1).val)) % 13 = (p.1 + (shifts p.2 - p.1)).val := by
        change (p.1.val + (13 + (shifts p.2 - p.1).val)) % 13 = (p.1.val + (shifts p.2 - p.1).val) % 13
        omega
      rw [h1, add_sub_cancel]
      exact hShiftMem p.2
    have hinj : Set.InjOn emb (Finset.univ : Finset (Fin 13 × Fin 4)) := by
      intro p _ q _ heq
      dsimp only [emb] at heq
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, h2⟩ | ⟨h1, _⟩
      · have hp : p.1 = q.1 := Fin.ext (by simpa using congrArg Fin.val h1)
        have hl : shifts p.2 - p.1 = shifts q.2 - q.1 := Fin.ext (by
          have hv := congrArg Fin.val h2
          simp only [Fin.val_natAdd] at hv
          omega)
        rw [hp] at hl
        have hs : p.2 = q.2 := hShiftInj (sub_left_inj.1 hl)
        exact Prod.ext hp hs
      · have hv := congrArg Fin.val h1
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        have := p.1.isLt
        omega
    have hle := Finset.card_le_card_of_injOn emb hmem hinj
    simpa using hle
  have hDeg : ∀ v : Fin 26, (Finset.univ.filter fun w : Fin 26 => G.Adj v w).card ≤ 4 := by
    intro v
    by_cases hv : v.val < 13
    · let v13 : Fin 13 := ⟨v.val, hv⟩
      have hsub : (Finset.univ.filter fun w : Fin 26 => G.Adj v w) ⊆
          (Finset.univ : Finset (Fin 4)).image fun k => Fin.natAdd 13 (shifts k - v13) := by
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        rcases (hAdj v w).1 hw with ⟨_, hw13, hmod⟩ | ⟨hw13, _, _⟩
        · let w13 : Fin 13 := ⟨w.val - 13, by omega⟩
          have hsum : (v.val + w.val) % 13 = (v13 + w13).val := by
            change (v.val + w.val) % 13 = (v.val + (w.val - 13)) % 13
            omega
          rw [hsum] at hmod
          obtain ⟨k, hk⟩ := hMemShift (v13 + w13) hmod
          refine Finset.mem_image.2 ⟨k, Finset.mem_univ _, ?_⟩
          apply Fin.ext
          rw [hk, add_sub_cancel_left]
          simp [w13]; omega
        · omega
      exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
    · let v13 : Fin 13 := ⟨v.val - 13, by omega⟩
      have hsub : (Finset.univ.filter fun w : Fin 26 => G.Adj v w) ⊆
          (Finset.univ : Finset (Fin 4)).image fun k => Fin.castAdd 13 (shifts k - v13) := by
        intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        rcases (hAdj v w).1 hw with ⟨hv13, _, _⟩ | ⟨hw13, _, hmod⟩
        · omega
        · let w13 : Fin 13 := ⟨w.val, hw13⟩
          have hsum : (w.val + v.val) % 13 = (w13 + v13).val := by
            change (w.val + v.val) % 13 = (w.val + (v.val - 13)) % 13
            omega
          rw [hsum] at hmod
          obtain ⟨k, hk⟩ := hMemShift (w13 + v13) hmod
          refine Finset.mem_image.2 ⟨k, Finset.mem_univ _, ?_⟩
          apply Fin.ext
          rw [hk, add_sub_cancel_right]
          simp [w13]
      exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
  have hMatch : ∀ i : Fin 13, G.Adj (Fin.castAdd 13 i) (Fin.natAdd 13 (-i)) := by
    intro i
    apply (hAdj _ _).2
    left
    refine ⟨i.isLt, by simp, ?_⟩
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    have h1 : (i.val + (13 + (-i).val)) % 13 = (i + (-i)).val := by
      change (i.val + (13 + (-i).val)) % 13 = (i.val + (-i).val) % 13
      omega
    rw [h1, add_neg_cancel]
    simp
  have hNoTri : ∀ a b c : Fin 26, G.Adj a b → G.Adj b c → ¬ G.Adj a c := by
    intro a b c hab hbc hac
    rcases (hAdj a b).1 hab with h1 | h1 <;>
      rcases (hAdj b c).1 hbc with h2 | h2 <;>
      rcases (hAdj a c).1 hac with h3 | h3 <;>
      dsimp only [rel0] at h1 h2 h3 <;> omega
  have hCover13 : ∀ W : Finset (Fin 26), (∀ u v : Fin 26, G.Adj u v → u ∈ W ∨ v ∈ W) → 13 ≤ W.card := by
    intro W hW
    let f : Fin 13 → Fin 26 := fun i =>
      if Fin.castAdd 13 i ∈ W then Fin.castAdd 13 i else Fin.natAdd 13 (-i)
    have hmap : ∀ i ∈ (Finset.univ : Finset (Fin 13)), f i ∈ W := by
      intro i _
      dsimp only [f]
      split_ifs with h
      · exact h
      · exact (hW _ _ (hMatch i)).resolve_left h
    have hinj : Set.InjOn f (Finset.univ : Finset (Fin 13)) := by
      intro i _ j _ hij
      dsimp only [f] at hij
      have hv := congrArg Fin.val hij
      split_ifs at hv with h1 h2 h2
      · simp only [Fin.val_castAdd] at hv
        exact Fin.ext hv
      · simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        have := i.isLt
        omega
      · simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        have := j.isLt
        omega
      · simp only [Fin.val_natAdd] at hv
        exact neg_inj.mp (Fin.ext (by omega))
    simpa using Finset.card_le_card_of_injOn f hmap hinj
  have hFoldLen : ∀ {α β : Type} (f : List β → α → β) (l : List α) (acc : List β),
      (l.foldl (fun w g => w ++ [f w g]) acc).length = acc.length + l.length := by
    intro α β f l
    induction l with
    | nil => intro acc; simp
    | cons a t ih =>
      intro acc
      simp only [List.foldl_cons, List.length_cons]
      rw [ih, List.length_append, List.length_singleton]
      omega
  have hFoldLt : ∀ {α β : Type} (f : List β → α → β) (l : List α) (acc : List β) (d : β) (k : ℕ),
      k < acc.length → (l.foldl (fun w g => w ++ [f w g]) acc).getD k d = acc.getD k d := by
    intro α β f l
    induction l with
    | nil => intro acc d k _; rfl
    | cons a t ih =>
      intro acc d k hk
      simp only [List.foldl_cons]
      have hk' : k < (acc ++ [f acc a]).length := by
        rw [List.length_append, List.length_singleton]
        omega
      rw [ih (acc ++ [f acc a]) d k hk', List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hk]
  have hFoldGate : ∀ {α β : Type} (f : List β → α → β) (l : List α) (acc : List β) (d : β)
      (j : ℕ) (_ : j < l.length) (dA : α),
      (l.foldl (fun w g => w ++ [f w g]) acc).getD (acc.length + j) d =
        f ((l.take j).foldl (fun w g => w ++ [f w g]) acc) (l.getD j dA) := by
    intro α β f l acc d j hj dA
    have hsplit : l = l.take j ++ l[j] :: l.drop (j + 1) := by
      have h1 := (List.take_append_drop j l).symm
      rw [List.drop_eq_getElem_cons hj] at h1
      exact h1
    have hget : l.getD j dA = l[j] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      rfl
    rw [hget]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    set pre := (l.take j).foldl (fun w g => w ++ [f w g]) acc
    have hpre : pre.length = acc.length + j := by
      rw [hFoldLen, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
    have hlt : acc.length + j < (pre ++ [f pre l[j]]).length := by
      rw [List.length_append, List.length_singleton, hpre]
      omega
    rw [hFoldLt f (l.drop (j + 1)) (pre ++ [f pre l[j]]) d (acc.length + j) hlt,
      List.getD_eq_getElem?_getD, ← hpre]
    simp
  have hFoldTake : ∀ {α β : Type} (f : List β → α → β) (l : List α) (acc : List β) (d : β)
      (j i : ℕ), j ≤ l.length → i < acc.length + j →
      ((l.take j).foldl (fun w g => w ++ [f w g]) acc).getD i d =
        (l.foldl (fun w g => w ++ [f w g]) acc).getD i d := by
    intro α β f l acc d j i hj hi
    have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
    conv_rhs => rw [hsplit, List.foldl_append]
    have hpre : ((l.take j).foldl (fun w g => w ++ [f w g]) acc).length = acc.length + j := by
      rw [hFoldLen, List.length_take, Nat.min_eq_left hj]
    rw [hFoldLt f (l.drop j) _ d i (hpre ▸ hi)]
  have hAO := hL.1
  have hGateMem : ∀ {j : ℕ}, j < C.gates.length → gateAt C j ∈ C.gates := by
    intro j hj
    unfold gateAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    exact List.getElem_mem hj
  have hInputsPair : ∀ {j : ℕ}, j < C.gates.length → (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
    intro j hj
    have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (hGateMem hj)
    unfold opnd
    rcases h : (gateAt C j).inputs with _ | ⟨w0, _ | ⟨w1, _ | _⟩⟩
    · simp [h] at hlen
    · simp [h] at hlen
    · simp
    · simp [h] at hlen
  have hOpndMem : ∀ {j : ℕ}, j < C.gates.length → ∀ b : Fin 2, opnd C j b ∈ (gateAt C j).inputs := by
    intro j hj b
    rw [hInputsPair hj]
    fin_cases b <;> simp
  have hOpndLt : ∀ {j : ℕ}, j < C.gates.length → ∀ b : Fin 2, opnd C j b < 26 + j :=
    fun hj b => hAO.2.1 _ hj _ (hOpndMem hj b)
  have hWireInput : ∀ (i : Fin 26) (x : Fin 26 → Bool), wireVal 26 C i.val x = x i := by
    intro i x
    unfold wireVal Circuit.wires
    have hi : i.val < (List.ofFn x).length := by rw [List.length_ofFn]; exact i.isLt
    rw [hFoldLt _ C.gates (List.ofFn x) false i.val hi,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simp only [Option.getD_some, List.getElem_ofFn, Fin.eta]
  have hWireGe : ∀ (w : ℕ) (x : Fin 26 → Bool), 26 + C.gates.length ≤ w → wireVal 26 C w x = false := by
    intro w x hw
    unfold wireVal Circuit.wires
    have hlen : (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn x)).length = 26 + C.gates.length := by
      rw [hFoldLen, List.length_ofFn]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  have hWireGate : ∀ {j : ℕ}, j < C.gates.length → ∀ (x : Fin 26 → Bool),
      wireVal 26 C (26 + j) x =
        (gateAt C j).op.eval ((gateAt C j).inputs.map fun w => wireVal 26 C w x) := by
    intro j hj x
    unfold wireVal Circuit.wires
    have hg := hFoldGate (fun w g => g.op.eval (g.inputs.map fun i => w.getD i false))
      C.gates (List.ofFn x) false j hj ⟨GateOp.or, []⟩
    rw [List.length_ofFn] at hg
    rw [hg]
    change (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        ((C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x)).getD i false) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x)).getD i false)
    congr 1
    apply List.map_congr_left
    intro i hi
    have hilt : i < (List.ofFn x).length + j := by
      rw [List.length_ofFn]
      exact hAO.2.1 j hj i hi
    exact hFoldTake _ C.gates (List.ofFn x) false j i (Nat.le_of_lt hj) hilt
  have hWireAnd : ∀ {j : ℕ}, j < C.gates.length → (gateAt C j).op = GateOp.and → ∀ (x : Fin 26 → Bool),
      gateVal 26 C j x = true ↔
        wireVal 26 C (opnd C j 0) x = true ∧ wireVal 26 C (opnd C j 1) x = true := by
    intro j hj hop x
    change wireVal 26 C (26 + j) x = true ↔ _
    rw [hWireGate hj x, hop, hInputsPair hj, List.map_cons, List.map_cons, List.map_nil]
    cases wireVal 26 C (opnd C j 0) x <;> cases wireVal 26 C (opnd C j 1) x <;> decide
  have hWireOr : ∀ {j : ℕ}, j < C.gates.length → (gateAt C j).op = GateOp.or → ∀ (x : Fin 26 → Bool),
      gateVal 26 C j x = true ↔
        wireVal 26 C (opnd C j 0) x = true ∨ wireVal 26 C (opnd C j 1) x = true := by
    intro j hj hop x
    change wireVal 26 C (26 + j) x = true ↔ _
    rw [hWireGate hj x, hop, hInputsPair hj, List.map_cons, List.map_cons, List.map_nil]
    cases wireVal 26 C (opnd C j 0) x <;> cases wireVal 26 C (opnd C j 1) x <;> decide
  let fOr : List (List ℕ) → Gate → List ℕ := fun cs gt =>
    cs.length :: (if gt.op = GateOp.or then
      (gt.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
        (fun w => cs.getD (w - 26) []) else [])
  have hOrSetsEq : ∀ l : List Gate, l.foldl (orStep 26) [] = l.foldl (fun w g => w ++ [fOr w g]) [] := by
    intro l; rfl
  have hOrSetsLen : (orSets 26 C).length = C.gates.length := by
    change (C.gates.foldl (orStep 26) []).length = C.gates.length
    rw [hOrSetsEq, hFoldLen]
    simp
  have hOrReachesIff : ∀ k g : ℕ, OrReaches 26 C (26 + k) g ↔
      k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ w ∈ (gateAt C k).inputs, w < 26 + k ∧ OrReaches 26 C w g)) := by
    intro k g
    unfold OrReaches
    simp only [Nat.le_add_right, true_and, Nat.add_sub_cancel_left]
    by_cases hk : k < C.gates.length
    · have hstep := hFoldGate fOr C.gates [] [] k hk ⟨GateOp.or, []⟩
      simp only [List.length_nil, Nat.zero_add] at hstep
      have hlenPre : ((C.gates.take k).foldl (fun w g => w ++ [fOr w g]) []).length = k := by
        rw [hFoldLen, List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
      have hget : (orSets 26 C).getD k [] = k :: (if (gateAt C k).op = GateOp.or then
          ((gateAt C k).inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + k))).flatMap
            (fun w => (orSets 26 C).getD (w - 26) []) else []) := by
        change (C.gates.foldl (orStep 26) []).getD k [] = _
        rw [hOrSetsEq, hstep]
        dsimp only [fOr]
        rw [hlenPre]
        change k :: (if (gateAt C k).op = GateOp.or then
            ((gateAt C k).inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + k))).flatMap
              (fun w => ((C.gates.take k).foldl (fun w g => w ++ [fOr w g]) []).getD (w - 26) []) else []) = _
        congr 1
        split_ifs with hop
        · apply List.flatMap_congr
          intro w hw
          simp only [List.mem_filter, decide_eq_true_eq] at hw
          have htake := hFoldTake fOr C.gates [] [] k (w - 26) (Nat.le_of_lt hk) (by omega)
          rw [htake]
          change (C.gates.foldl (fun w g => w ++ [fOr w g]) []).getD (w - 26) [] =
            (C.gates.foldl (orStep 26) []).getD (w - 26) []
          rw [hOrSetsEq]
        · rfl
      rw [hget, List.mem_cons]
      constructor
      · intro h
        refine ⟨hk, ?_⟩
        rcases h with rfl | h
        · exact Or.inl rfl
        · right
          split_ifs at h with hop
          · simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at h
            obtain ⟨w, ⟨hw, h26, hlt⟩, hmem⟩ := h
            exact ⟨hop, w, hw, hlt, h26, hmem⟩
          · simp at h
      · rintro ⟨_, rfl | ⟨hop, w, hw, hlt, h26, hmem⟩⟩
        · exact Or.inl rfl
        · right
          rw [ite_eq_left hop]
          simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
          exact ⟨w, ⟨hw, h26, hlt⟩, hmem⟩
    · have hnone : (orSets 26 C).getD k [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      rw [hnone]
      simp [hk]
  let fCone : List (List ℕ) → Gate → List ℕ := fun cs gt =>
    (gt.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
      (fun w => (w - 26) :: cs.getD (w - 26) [])
  have hConesEq : ∀ l : List Gate, l.foldl (coneStep 26) [] = l.foldl (fun w g => w ++ [fCone w g]) [] := by
    intro l; rfl
  have hConesLen : (cones 26 C).length = C.gates.length := by
    change (C.gates.foldl (coneStep 26) []).length = C.gates.length
    rw [hConesEq, hFoldLen]
    simp
  have hInConeIff : ∀ i j : ℕ, InCone 26 C i j ↔
      j < C.gates.length ∧ ∃ w ∈ (gateAt C j).inputs, 26 ≤ w ∧ w < 26 + j ∧
        (i = w - 26 ∨ InCone 26 C i (w - 26)) := by
    intro i j
    unfold InCone
    by_cases hj : j < C.gates.length
    · have hstep := hFoldGate fCone C.gates [] [] j hj ⟨GateOp.or, []⟩
      simp only [List.length_nil, Nat.zero_add] at hstep
      have hlenPre : ((C.gates.take j).foldl (fun w g => w ++ [fCone w g]) []).length = j := by
        rw [hFoldLen, List.length_nil, Nat.zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
      have hget : (cones 26 C).getD j [] =
          ((gateAt C j).inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + j))).flatMap
            (fun w => (w - 26) :: (cones 26 C).getD (w - 26) []) := by
        change (C.gates.foldl (coneStep 26) []).getD j [] = _
        rw [hConesEq, hstep]
        dsimp only [fCone]
        rw [hlenPre]
        change ((gateAt C j).inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + j))).flatMap
            (fun w => (w - 26) :: ((C.gates.take j).foldl (fun w g => w ++ [fCone w g]) []).getD (w - 26) []) = _
        apply List.flatMap_congr
        intro w hw
        simp only [List.mem_filter, decide_eq_true_eq] at hw
        have htake := hFoldTake fCone C.gates [] [] j (w - 26) (Nat.le_of_lt hj) (by omega)
        exact congrArg ((w - 26) :: ·) htake
      rw [hget]
      simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro ⟨w, ⟨hw, h26, hlt⟩, hmem⟩
        exact ⟨hj, w, hw, h26, hlt, hmem⟩
      · rintro ⟨_, w, hw, h26, hlt, hmem⟩
        exact ⟨w, ⟨hw, h26, hlt⟩, hmem⟩
    · have hnone : (cones 26 C).getD j [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      rw [hnone]
      simp [hj]
  have hOrReachesInCone : ∀ w g : ℕ, OrReaches 26 C w g →
      w = 26 + g ∨ InCone 26 C g (w - 26) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro g hr
      have h26 : 26 ≤ w := hr.1
      obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
      obtain ⟨hk, rfl | ⟨_, z, hz, hzlt, hrz⟩⟩ := (hOrReachesIff k g).1 hr
      · exact Or.inl rfl
      · right
        rw [Nat.add_sub_cancel_left]
        refine (hInConeIff g k).2 ⟨hk, z, hz, hrz.1, hzlt, ?_⟩
        rcases ih z hzlt g hrz with hzeq | hzcone
        · exact Or.inl (by omega)
        · exact Or.inr hzcone
  have hOrReachesVal : ∀ w g : ℕ, OrReaches 26 C w g → ∀ x : Fin 26 → Bool,
      gateVal 26 C g x = true → wireVal 26 C w x = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro g hr x hgx
      have h26 : 26 ≤ w := hr.1
      obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
      obtain ⟨hk, rfl | ⟨hop, z, hz, hzlt, hrz⟩⟩ := (hOrReachesIff k g).1 hr
      · exact hgx
      · have hzx := ih z hzlt g hrz x hgx
        have hmem : z = opnd C k 0 ∨ z = opnd C k 1 := by
          rw [hInputsPair hk] at hz
          simpa using hz
        rcases hmem with rfl | rfl
        · exact (hWireOr hk hop x).2 (Or.inl hzx)
        · exact (hWireOr hk hop x).2 (Or.inr hzx)
  have hOrInVal : ∀ w : ℕ, ∀ u : Fin 26, u ∈ orIn 26 C w → ∀ x : Fin 26 → Bool,
      x u = true → wireVal 26 C w x = true := by
    intro w u hu x hxu
    have hu' : (u : ℕ) = w ∨ ∃ k < C.gates.length, OrReaches 26 C w k ∧ (gateAt C k).op = GateOp.or ∧ (u : ℕ) ∈ (gateAt C k).inputs :=
      (Finset.mem_filter.1 hu).2
    rcases hu' with heq | ⟨k, hk, hr, hop, hin⟩
    · rw [← heq, hWireInput]
      exact hxu
    · apply hOrReachesVal w k hr x
      have hmem : (u : ℕ) = opnd C k 0 ∨ (u : ℕ) = opnd C k 1 := by
        rw [hInputsPair hk] at hin
        simpa using hin
      apply (hWireOr hk hop x).2
      rcases hmem with h0 | h1
      · exact Or.inl (by rw [← h0, hWireInput]; exact hxu)
      · exact Or.inr (by rw [← h1, hWireInput]; exact hxu)
  have hOrInAnd : ∀ j : ℕ, (gateAt C j).op = GateOp.and → orIn 26 C (26 + j) = ∅ := by
    intro j hop
    ext u
    refine ⟨fun hu => ?_, fun hu => (Finset.notMem_empty u hu).elim⟩
    rcases (Finset.mem_filter.1 hu).2 with heq | ⟨k, _, hr, hkop, _⟩
    · have := u.isLt; omega
    · obtain ⟨_, rfl | ⟨hor, _⟩⟩ := (hOrReachesIff j k).1 hr
      · rw [hop] at hkop; cases hkop
      · rw [hop] at hor; cases hor
  have hOrInOr : ∀ k : ℕ, k < C.gates.length → (gateAt C k).op = GateOp.or →
      orIn 26 C (26 + k) = orIn 26 C (opnd C k 0) ∪ orIn 26 C (opnd C k 1) := by
    intro k hk hop
    ext u
    rw [Finset.mem_union]
    constructor
    · intro hu
      rcases (Finset.mem_filter.1 hu).2 with heq | ⟨m, hm, hr, hmop, hin⟩
      · have := u.isLt; omega
      · obtain ⟨_, rfl | ⟨_, z, hz, _, hrz⟩⟩ := (hOrReachesIff k m).1 hr
        · rw [hInputsPair hk] at hin
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
          rcases hin with h0 | h1
          · exact Or.inl (Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl h0⟩)
          · exact Or.inr (Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl h1⟩)
        · rw [hInputsPair hk] at hz
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with rfl | rfl
          · exact Or.inl (Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr ⟨m, hm, hrz, hmop, hin⟩⟩)
          · exact Or.inr (Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr ⟨m, hm, hrz, hmop, hin⟩⟩)
    · rintro (hu | hu)
      · rcases (Finset.mem_filter.1 hu).2 with h0 | ⟨m, hm, hr, hmop, hin⟩
        · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr ⟨k, hk, (hOrReachesIff k k).2 ⟨hk, Or.inl rfl⟩, hop, h0 ▸ hOpndMem hk 0⟩⟩
        · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr ⟨m, hm, (hOrReachesIff k m).2 ⟨hk, Or.inr ⟨hop, opnd C k 0, hOpndMem hk 0, hOpndLt hk 0, hr⟩⟩, hmop, hin⟩⟩
      · rcases (Finset.mem_filter.1 hu).2 with h1 | ⟨m, hm, hr, hmop, hin⟩
        · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr ⟨k, hk, (hOrReachesIff k k).2 ⟨hk, Or.inl rfl⟩, hop, h1 ▸ hOpndMem hk 1⟩⟩
        · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inr ⟨m, hm, (hOrReachesIff k m).2 ⟨hk, Or.inr ⟨hop, opnd C k 1, hOpndMem hk 1, hOpndLt hk 1, hr⟩⟩, hmop, hin⟩⟩
  have hPairGraph : ∀ u v : Fin 26, graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
    intro u v
    change (decide (∃ a ∈ (∅ : Finset (Fin 26)), pairInput u v a = true) ||
      decide (∃ a b : Fin 26, G.Adj a b ∧ pairInput u v a = true ∧ pairInput u v b = true)) = true ↔ G.Adj u v
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · rintro (⟨a, ha, _⟩ | ⟨a, b, hab, ha, hb⟩)
      · exact (Finset.notMem_empty a ha).elim
      · change decide (a = u ∨ a = v) = true at ha
        change decide (b = u ∨ b = v) = true at hb
        rw [decide_eq_true_eq] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact (G.irrefl hab).elim
        · exact hab
        · exact hab.symm
        · exact (G.irrefl hab).elim
    · intro hab
      right
      refine ⟨u, v, hab, ?_, ?_⟩
      · exact decide_eq_true (Or.inl rfl)
      · exact decide_eq_true (Or.inr rfl)
  have hWireTrace : ∀ w : ℕ, ∀ u v : Fin 26, wireVal 26 C w (pairInput u v) = true →
      (∃ t ∈ orIn 26 C w, t = u ∨ t = v) ∨
      (∃ g < C.gates.length, (gateAt C g).op = GateOp.and ∧
        OrReaches 26 C w g ∧ gateVal 26 C g (pairInput u v) = true) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro u v hval
      by_cases hw : w < 26
      · let t : Fin 26 := ⟨w, hw⟩
        have htv : decide (t = u ∨ t = v) = true := by
          change pairInput u v t = true
          rw [← hWireInput t (pairInput u v)]
          exact hval
        rw [decide_eq_true_eq] at htv
        exact Or.inl ⟨t, Finset.mem_filter.2 ⟨Finset.mem_univ _, Or.inl rfl⟩, htv⟩
      · obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
        by_cases hk : k < C.gates.length
        · rcases hAO.1 _ (hGateMem hk) with hand | hor
          · exact Or.inr ⟨k, hk, hand, (hOrReachesIff k k).2 ⟨hk, Or.inl rfl⟩, hval⟩
          · rcases (hWireOr hk hor (pairInput u v)).1 hval with h0 | h1
            · rcases ih (opnd C k 0) (hOpndLt hk 0) u v h0 with ⟨t, ht, huv⟩ | ⟨g, hgl, hgop, hrg, hvg⟩
              · exact Or.inl ⟨t, by rw [hOrInOr k hk hor]; exact Finset.mem_union_left _ ht, huv⟩
              · exact Or.inr ⟨g, hgl, hgop, (hOrReachesIff k g).2 ⟨hk, Or.inr ⟨hor, _, hOpndMem hk 0, hOpndLt hk 0, hrg⟩⟩, hvg⟩
            · rcases ih (opnd C k 1) (hOpndLt hk 1) u v h1 with ⟨t, ht, huv⟩ | ⟨g, hgl, hgop, hrg, hvg⟩
              · exact Or.inl ⟨t, by rw [hOrInOr k hk hor]; exact Finset.mem_union_right _ ht, huv⟩
              · exact Or.inr ⟨g, hgl, hgop, (hOrReachesIff k g).2 ⟨hk, Or.inr ⟨hor, _, hOpndMem hk 1, hOpndLt hk 1, hrg⟩⟩, hvg⟩
        · rw [hWireGe (26 + k) (pairInput u v) (by omega)] at hval
          cases hval
  have hAcceptedTop : ∀ u v : Fin 26, G.Adj u v →
      ∃ a ∈ tops G C, gateVal 26 C a (pairInput u v) = true := by
    intro u v huv
    have hout : ∀ x : Fin 26 → Bool, wireVal 26 C C.output x = graphFun G ∅ x := fun x =>
      congrFun hL.2.1 x
    have hval : wireVal 26 C C.output (pairInput u v) = true := by
      rw [hout, hPairGraph]
      exact huv
    rcases hWireTrace C.output u v hval with ⟨t, ht, _⟩ | ⟨a, hal, haop, hra, hva⟩
    · exfalso
      have htt : graphFun G ∅ (pairInput t t) = true := by
        rw [← hout]
        exact hOrInVal C.output t ht (pairInput t t) (decide_eq_true (Or.inl rfl))
      exact G.irrefl ((hPairGraph t t).1 htt)
    · refine ⟨a, ?_, hva⟩
      refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hal, haop, fun x hx => ?_⟩
      rw [← hout]
      exact hOrReachesVal C.output a hra x hx
  have hTopAdj : ∀ a ∈ tops G C, ∀ u ∈ side (n := 26) C a 0, ∀ v ∈ side (n := 26) C a 1, G.Adj u v := by
    intro a ha u hu v hv
    have ha' := Finset.mem_filter.1 ha
    have hal : a < C.gates.length := Finset.mem_range.1 ha'.1
    obtain ⟨haop, hbel⟩ := ha'.2
    apply (hPairGraph u v).1
    apply hbel
    apply (hWireAnd hal haop (pairInput u v)).2
    exact ⟨hOrInVal _ u hu _ (decide_eq_true (Or.inl rfl)),
      hOrInVal _ v hv _ (decide_eq_true (Or.inr rfl))⟩
  have hBiclique : ∀ A B : Finset (Fin 26), (∀ a ∈ A, ∀ b ∈ B, G.Adj a b) → A.card ≤ 1 ∨ B.card ≤ 1 := by
    intro A B hab
    by_contra hcon
    simp only [not_or, not_le] at hcon
    obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.1 hcon.1
    obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.1 hcon.2
    have hsub : ({b, d} : Finset (Fin 26)) ⊆ Finset.univ.filter fun w => G.Adj a w ∧ G.Adj c w := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact ⟨hab a ha w hb, hab c hc w hb⟩
      · exact ⟨hab a ha w hd, hab c hc w hd⟩
    have hle := (Finset.card_le_card hsub).trans (hNoFour a c hac)
    rw [Finset.card_pair hbd] at hle
    omega
  let pick : ℕ → Finset (Fin 26) := fun a =>
    if (side (n := 26) C a 0).card ≤ 1 then side (n := 26) C a 0 else side (n := 26) C a 1
  let S : Finset (Fin 26) := (tops G C \ centreless G C).biUnion pick
  have hScard : S.card ≤ (tops G C \ centreless G C).card := by
    calc S.card ≤ ∑ a ∈ tops G C \ centreless G C, (pick a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ tops G C \ centreless G C, 1 := by
        apply Finset.sum_le_sum
        intro a ha
        have hat := (Finset.mem_sdiff.1 ha).1
        dsimp only [pick]
        split_ifs with h0
        · exact h0
        · exact (hBiclique _ _ (hTopAdj a hat)).resolve_left h0
      _ = (tops G C \ centreless G C).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  have hScov : ∀ e ∈ starEdges G C, ∃ v ∈ S, v ∈ e := by
    intro e he
    obtain ⟨a, ha, he1⟩ := Finset.mem_biUnion.1 he
    obtain ⟨⟨u, v⟩, hp, rfl⟩ := Finset.mem_image.1 he1
    obtain ⟨hu, hv⟩ := Finset.mem_product.1 hp
    have hac : a ∉ centreless G C := by
      intro hc
      rcases (Finset.mem_filter.1 hc).2 with h0 | h1
      · rw [h0] at hu; exact Finset.notMem_empty u hu
      · rw [h1] at hv; exact Finset.notMem_empty v hv
    have has : a ∈ tops G C \ centreless G C := Finset.mem_sdiff.2 ⟨ha, hac⟩
    by_cases h0 : (side (n := 26) C a 0).card ≤ 1
    · exact ⟨u, Finset.mem_biUnion.2 ⟨a, has, by dsimp only [pick]; rw [ite_eq_left h0]; exact hu⟩, Sym2.mem_mk_left u v⟩
    · exact ⟨v, Finset.mem_biUnion.2 ⟨a, has, by dsimp only [pick]; rw [ite_eq_right h0]; exact hv⟩, Sym2.mem_mk_right u v⟩
  have hDegBound : 52 ≤ 4 * (tops G C \ centreless G C).card + (Ustar G C).card := by
    have hsub : G.edgeFinset \ Ustar G C ⊆
        S.biUnion fun v => (Finset.univ.filter fun w : Fin 26 => G.Adj v w).image fun w => s(v, w) := by
      intro e
      refine Sym2.ind (fun u v he => ?_) e
      rw [Finset.mem_sdiff] at he
      have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.1 he.1
      have hstar : s(u, v) ∈ starEdges G C := by
        by_contra hns
        exact he.2 (Finset.mem_sdiff.2 ⟨he.1, hns⟩)
      obtain ⟨w, hwS, hwe⟩ := hScov _ hstar
      rw [Finset.mem_biUnion]
      rcases Sym2.mem_iff.1 hwe with rfl | rfl
      · exact ⟨w, hwS, Finset.mem_image.2 ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ _, hadj⟩, rfl⟩⟩
      · exact ⟨w, hwS, Finset.mem_image.2 ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ _, hadj.symm⟩, Sym2.eq_swap⟩⟩
    have hc1 : (G.edgeFinset \ Ustar G C).card ≤ 4 * S.card := by
      calc (G.edgeFinset \ Ustar G C).card
          ≤ (S.biUnion fun v => (Finset.univ.filter fun w : Fin 26 => G.Adj v w).image fun w => s(v, w)).card :=
            Finset.card_le_card hsub
        _ ≤ ∑ v ∈ S, ((Finset.univ.filter fun w : Fin 26 => G.Adj v w).image fun w => s(v, w)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _v ∈ S, 4 := Finset.sum_le_sum fun v _ => Finset.card_image_le.trans (hDeg v)
        _ = 4 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hc2 : G.edgeFinset.card ≤ (G.edgeFinset \ Ustar G C).card + (Ustar G C).card :=
      Finset.card_le_card_sdiff_add_card
    omega
  have hCoverBound : ∀ B : Finset (Fin 26), (∀ e ∈ Ustar G C, ∃ v ∈ B, v ∈ e) →
      13 ≤ (tops G C \ centreless G C).card + B.card := by
    intro B hB
    have hcov : ∀ u v : Fin 26, G.Adj u v → u ∈ S ∪ B ∨ v ∈ S ∪ B := by
      intro u v huv
      by_cases he : s(u, v) ∈ Ustar G C
      · obtain ⟨w, hwB, hwe⟩ := hB _ he
        rcases Sym2.mem_iff.1 hwe with rfl | rfl
        · exact Or.inl (Finset.mem_union_right _ hwB)
        · exact Or.inr (Finset.mem_union_right _ hwB)
      · have hstar : s(u, v) ∈ starEdges G C := by
          by_contra hns
          exact he (Finset.mem_sdiff.2 ⟨SimpleGraph.mem_edgeFinset.2 huv, hns⟩)
        obtain ⟨w, hwS, hwe⟩ := hScov _ hstar
        rcases Sym2.mem_iff.1 hwe with rfl | rfl
        · exact Or.inl (Finset.mem_union_left _ hwS)
        · exact Or.inr (Finset.mem_union_left _ hwS)
    have h13 := hCover13 (S ∪ B) hcov
    have hu := Finset.card_union_le S B
    omega
  have hDoubleWin : 2 * (Ustar G C).card ≤
      2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card →
      13 + (Ustar G C).card ≤
        (tops G C \ centreless G C).card + 2 * (centreless G C).card +
        (junk G C).card + (orN G C \ lam G C).card := by
    intro hle
    let B : Finset (Fin 26) := (Ustar G C).image fun e => e.out.1
    have hBcard : B.card ≤ (Ustar G C).card := Finset.card_image_le
    have hBcov : ∀ e ∈ Ustar G C, ∃ v ∈ B, v ∈ e := by
      intro e he
      refine ⟨e.out.1, Finset.mem_image.2 ⟨e, he, rfl⟩, ?_⟩
      have hq : s(e.out.1, e.out.2) = e := Quot.out_eq e
      have hm : e.out.1 ∈ s(e.out.1, e.out.2) := Sym2.mem_mk_left _ _
      rwa [hq] at hm
    have h13 := hCoverBound B hBcov
    omega
  have hMixSub : mixing G C ⊆ orN G C \ lam G C := by
    intro m hm
    rcases Finset.mem_filter.1 hm with ⟨hmN, hmix⟩
    refine Finset.mem_sdiff.2 ⟨hmN, fun hl => ?_⟩
    rcases Finset.mem_filter.1 hl with ⟨_, h0, h1, _⟩
    apply hmix
    simp only [← Finset.not_nonempty_iff_eq_empty, h0, h1]
  have hMixAlong : ∀ w g : ℕ, OrReaches 26 C w g → (gateAt C g).op = GateOp.and →
      (orIn 26 C w).Nonempty →
      ∃ m ∈ mixing G C, OrReaches 26 C (26 + m) g := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro g hr hgop hw
      have h26 : 26 ≤ w := hr.1
      obtain ⟨k, rfl⟩ : ∃ k, w = 26 + k := ⟨w - 26, by omega⟩
      obtain ⟨hk, rfl | ⟨hop, z, hz, hzlt, hrz⟩⟩ := (hOrReachesIff k g).1 hr
      · rw [hOrInAnd g hgop] at hw
        exact (Finset.not_nonempty_empty hw).elim
      · by_cases hzn : (orIn 26 C z).Nonempty
        · exact ih z hzlt g hrz hgop hzn
        · have hzE : orIn 26 C z = ∅ := Finset.not_nonempty_iff_eq_empty.1 hzn
          have hboth : (orIn 26 C (opnd C k 0) ∪ orIn 26 C (opnd C k 1)).Nonempty :=
            hOrInOr k hk hop ▸ hw
          have hnbel : ¬ BelowF G C k := by
            intro hbel
            obtain ⟨t, ht⟩ := hw
            have hval : gateVal 26 C k (pairInput t t) = true :=
              hOrInVal (26 + k) t ht (pairInput t t) (decide_eq_true (Or.inl rfl))
            exact G.irrefl ((hPairGraph t t).1 (hbel _ hval))
          have hkN : k ∈ orN G C := Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hop, hnbel⟩
          have hzPair : z = opnd C k 0 ∨ z = opnd C k 1 := by
            rw [hInputsPair hk] at hz
            simpa using hz
          have hkmix : k ∈ mixing G C := by
            refine Finset.mem_filter.2 ⟨hkN, ?_⟩
            rcases hzPair with rfl | rfl
            · have h1 : orIn 26 C (opnd C k 1) ≠ ∅ := by
                rwa [hzE, Finset.empty_union, Finset.nonempty_iff_ne_empty] at hboth
              intro heq
              exact h1 (heq ▸ hzE)
            · have h0 : orIn 26 C (opnd C k 0) ≠ ∅ := by
                rwa [hzE, Finset.union_empty, Finset.nonempty_iff_ne_empty] at hboth
              intro heq
              exact h0 (heq.symm ▸ hzE)
          exact ⟨k, hkmix, hr⟩
  have hUstarCover : ∀ e ∈ Ustar G C,
      (∃ c ∈ centreless G C, e ∈ gammaE G C c ∩ Ustar G C) ∨
      ((∃ g ∈ junk G C, e ∈ gammaE G C g ∩ Ustar G C) ∧
       (∃ m ∈ mixing G C, e ∈ gammaE G C m ∩ Ustar G C)) := by
    intro e
    refine Sym2.ind (fun u v he => ?_) e
    have hed : s(u, v) ∈ G.edgeFinset := (Finset.mem_sdiff.1 he).1
    have hns : s(u, v) ∉ starEdges G C := (Finset.mem_sdiff.1 he).2
    have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.1 hed
    obtain ⟨a, ha, hva⟩ := hAcceptedTop u v hadj
    have ha' := Finset.mem_filter.1 ha
    have hal : a < C.gates.length := Finset.mem_range.1 ha'.1
    have haop : (gateAt C a).op = GateOp.and := ha'.2.1
    obtain ⟨hv0, hv1⟩ := (hWireAnd hal haop (pairInput u v)).1 hva
    have hFindJunk : ∃ b : Fin 2, ∃ g ∈ junk G C, OrReaches 26 C (opnd C a b) g ∧
        gateVal 26 C g (pairInput u v) = true := by
      have mkJunk : ∀ b : Fin 2, ∀ g < C.gates.length, (gateAt C g).op = GateOp.and →
          OrReaches 26 C (opnd C a b) g → g ∈ junk G C := by
        intro b g hgl hgop hrg
        have hcone : InCone 26 C g a := by
          refine (hInConeIff g a).2 ⟨hal, opnd C a b, hOpndMem hal b, hrg.1, hOpndLt hal b, ?_⟩
          rcases hOrReachesInCone _ g hrg with heq | hci
          · exact Or.inl (by omega)
          · exact Or.inr hci
        have hnbel : ¬ BelowF G C g := fun hbel => hT g hgl a hal hgop hbel haop hcone
        refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hgl, hgop, hgl, ?_⟩
        by_contra hno
        apply hnbel
        intro x hgx
        cases hfx : graphFun G ∅ x
        · exact (hno ⟨x, hgx, hfx⟩).elim
        · rfl
      rcases hWireTrace (opnd C a 0) u v hv0 with ⟨t0, ht0, huv0⟩ | ⟨g, hgl, hgop, hrg, hvg⟩
      · rcases hWireTrace (opnd C a 1) u v hv1 with ⟨t1, ht1, huv1⟩ | ⟨g, hgl, hgop, hrg, hvg⟩
        · exfalso
          have htadj := hTopAdj a ha t0 ht0 t1 ht1
          have hst : s(t0, t1) ∈ starEdges G C :=
            Finset.mem_biUnion.2 ⟨a, ha, Finset.mem_image.2 ⟨(t0, t1), Finset.mem_product.2 ⟨ht0, ht1⟩, rfl⟩⟩
          rcases huv0 with rfl | rfl <;> rcases huv1 with rfl | rfl
          · exact G.irrefl htadj
          · exact hns hst
          · rw [Sym2.eq_swap] at hst; exact hns hst
          · exact G.irrefl htadj
        · exact ⟨1, g, mkJunk 1 g hgl hgop hrg, hrg, hvg⟩
      · exact ⟨0, g, mkJunk 0 g hgl hgop hrg, hrg, hvg⟩
    obtain ⟨b, g, hg, hrg, hvg⟩ := hFindJunk
    by_cases hc : a ∈ centreless G C
    · exact Or.inl ⟨a, hc, Finset.mem_inter.2 ⟨Finset.mem_filter.2 ⟨hed, u, v, rfl, hva⟩, he⟩⟩
    · right
      have hbn : (side (n := 26) C a b).Nonempty := by
        by_contra hne
        have hem := Finset.not_nonempty_iff_eq_empty.1 hne
        apply hc
        refine Finset.mem_filter.2 ⟨ha, ?_⟩
        fin_cases b
        · exact Or.inl hem
        · exact Or.inr hem
      have hgop : (gateAt C g).op = GateOp.and := (Finset.mem_filter.1 hg).2.1
      obtain ⟨m, hm, hmg⟩ := hMixAlong (opnd C a b) g hrg hgop hbn
      have hvm : gateVal 26 C m (pairInput u v) = true := hOrReachesVal (26 + m) g hmg _ hvg
      exact ⟨⟨g, hg, Finset.mem_inter.2 ⟨Finset.mem_filter.2 ⟨hed, u, v, rfl, hvg⟩, he⟩⟩,
        ⟨m, hm, Finset.mem_inter.2 ⟨Finset.mem_filter.2 ⟨hed, u, v, rfl, hvm⟩, he⟩⟩⟩
  by_cases hTwo : 2 * (Ustar G C).card ≤
      2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
  · exact hDoubleWin hTwo
  have hHlt : 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card <
      2 * (Ustar G C).card := by omega
  by_cases hU2 : (Ustar G C).card ≤ 2
  · omega
  have hH3 : 3 ≤ 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card := by
    by_contra hHle2
    have hT0z : (centreless G C).card = 0 := by omega
    have hOz : (orN G C \ lam G C).card = 0 := by omega
    have hT0e : centreless G C = ∅ := Finset.card_eq_zero.1 hT0z
    have hOe : orN G C \ lam G C = ∅ := Finset.card_eq_zero.1 hOz
    have hUe : Ustar G C = ∅ := by
      ext e
      refine ⟨fun he => ?_, fun he => (Finset.notMem_empty e he).elim⟩
      rcases hUstarCover e he with ⟨c, hc, _⟩ | ⟨_, m, hm, _⟩
      · rw [hT0e] at hc; exact (Finset.notMem_empty c hc).elim
      · have hmO := hMixSub hm
        rw [hOe] at hmO
        exact (Finset.notMem_empty m hmO).elim
    rw [hUe, Finset.card_empty] at hU2
    omega
  by_cases hU3 : (Ustar G C).card ≤ 3
  · omega
  have hU4 : 4 ≤ (Ustar G C).card := by omega
  have hHeavy : ∃ g ∈ centreless G C ∪ junk G C ∪ mixing G C, 2 ≤ (gammaE G C g ∩ Ustar G C).card := by
    by_contra hno
    have hle1 : ∀ g ∈ centreless G C ∪ junk G C ∪ mixing G C, (gammaE G C g ∩ Ustar G C).card ≤ 1 := by
      intro g hg
      by_contra hgt
      exact hno ⟨g, hg, by omega⟩
    let Uc := (centreless G C).biUnion fun c => gammaE G C c ∩ Ustar G C
    let Um := Ustar G C \ Uc
    have hUcSub : Uc ⊆ Ustar G C := Finset.biUnion_subset.2 fun _ _ => Finset.inter_subset_right
    have hUcCard : Uc.card ≤ (centreless G C).card := by
      calc Uc.card ≤ ∑ c ∈ centreless G C, (gammaE G C c ∩ Ustar G C).card := Finset.card_biUnion_le
        _ ≤ ∑ _c ∈ centreless G C, 1 := Finset.sum_le_sum fun c hc => hle1 c (Finset.mem_union_left _ (Finset.mem_union_left _ hc))
        _ = (centreless G C).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    have hUmJ : Um ⊆ (junk G C).biUnion fun g => gammaE G C g ∩ Ustar G C := by
      intro e he
      obtain ⟨heU, heNot⟩ := Finset.mem_sdiff.1 he
      rcases hUstarCover e heU with ⟨c, hc, hce⟩ | ⟨⟨g, hg, hge⟩, _⟩
      · exact (heNot (Finset.mem_biUnion.2 ⟨c, hc, hce⟩)).elim
      · exact Finset.mem_biUnion.2 ⟨g, hg, hge⟩
    have hUmM : Um ⊆ (mixing G C).biUnion fun m => gammaE G C m ∩ Ustar G C := by
      intro e he
      obtain ⟨heU, heNot⟩ := Finset.mem_sdiff.1 he
      rcases hUstarCover e heU with ⟨c, hc, hce⟩ | ⟨_, m, hm, hme⟩
      · exact (heNot (Finset.mem_biUnion.2 ⟨c, hc, hce⟩)).elim
      · exact Finset.mem_biUnion.2 ⟨m, hm, hme⟩
    have hUmCardJ : Um.card ≤ (junk G C).card := by
      calc Um.card ≤ ((junk G C).biUnion fun g => gammaE G C g ∩ Ustar G C).card := Finset.card_le_card hUmJ
        _ ≤ ∑ g ∈ junk G C, (gammaE G C g ∩ Ustar G C).card := Finset.card_biUnion_le
        _ ≤ ∑ _g ∈ junk G C, 1 := Finset.sum_le_sum fun g hg => hle1 g (Finset.mem_union_left _ (Finset.mem_union_right _ hg))
        _ = (junk G C).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    have hUmCardM : Um.card ≤ (orN G C \ lam G C).card := by
      calc Um.card ≤ ((mixing G C).biUnion fun m => gammaE G C m ∩ Ustar G C).card := Finset.card_le_card hUmM
        _ ≤ ∑ m ∈ mixing G C, (gammaE G C m ∩ Ustar G C).card := Finset.card_biUnion_le
        _ ≤ ∑ _m ∈ mixing G C, 1 := Finset.sum_le_sum fun m hm => hle1 m (Finset.mem_union_right _ hm)
        _ = (mixing G C).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ (orN G C \ lam G C).card := Finset.card_le_card hMixSub
    have hSplit : Um.card + Uc.card = (Ustar G C).card := Finset.card_sdiff_add_card_eq_card hUcSub
    omega
  by_cases hC0 : centreless G C = ∅
  · have hTopEq : tops G C \ centreless G C = tops G C := by rw [hC0, Finset.sdiff_empty]
    have hC0card : (centreless G C).card = 0 := by rw [hC0, Finset.card_empty]
    have hMixPos : 1 ≤ (mixing G C).card := by
      obtain ⟨e0, he0⟩ := Finset.card_pos.1 (by omega : 0 < (Ustar G C).card)
      rcases hUstarCover e0 he0 with ⟨c, hc, _⟩ | ⟨_, m, hm, _⟩
      · rw [hC0] at hc; exact (Finset.notMem_empty c hc).elim
      · exact Finset.card_pos.2 ⟨m, hm⟩
    have hHlt0 : (junk G C).card + (orN G C \ lam G C).card < 2 * (Ustar G C).card := by omega
    have hDeg0' : 52 ≤ 4 * (tops G C).card + (Ustar G C).card := by rwa [hTopEq] at hDegBound
    by_cases hDisj : ∃ g ∈ junk G C, ∃ e ∈ gammaE G C g ∩ Ustar G C, ∃ f ∈ gammaE G C g ∩ Ustar G C,
        ∀ v : Fin 26, v ∈ e → v ∉ f
    · have hres := disjointJunk G C hG hL hT hJ hSize hC0 hMixPos hU4 hHlt0 hDeg0' hDisj
      rw [hTopEq, hC0card]
      omega
    · have hStar : ∀ g ∈ junk G C, ∃ v : Fin 26, ∀ e ∈ gammaE G C g ∩ Ustar G C, v ∈ e := by
        intro g hg
        let X := gammaE G C g ∩ Ustar G C
        by_cases hXe : X = ∅
        · exact ⟨0, fun e he => (Finset.notMem_empty e (hXe ▸ he)).elim⟩
        · obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.2 hXe
          revert he0
          refine Sym2.ind (fun a b he0 => ?_) e0
          have hab : G.Adj a b :=
            SimpleGraph.mem_edgeFinset.1 (Finset.mem_sdiff.1 (Finset.mem_inter.1 he0).2).1
          by_cases haAll : ∀ e ∈ X, a ∈ e
          · exact ⟨a, haAll⟩
          · by_cases hbAll : ∀ e ∈ X, b ∈ e
            · exact ⟨b, hbAll⟩
            · exfalso
              have hna : ∃ e ∈ X, a ∉ e := by
                by_contra h
                exact haAll fun e he => Classical.byContradiction fun hne => h ⟨e, he, hne⟩
              have hnb : ∃ e ∈ X, b ∉ e := by
                by_contra h
                exact hbAll fun e he => Classical.byContradiction fun hne => h ⟨e, he, hne⟩
              obtain ⟨e1, he1, hna1⟩ := hna
              obtain ⟨e2, he2, hnb2⟩ := hnb
              have hmeet : ∀ e ∈ X, ∀ f ∈ X, ∃ w : Fin 26, w ∈ e ∧ w ∈ f := by
                intro e he f hf
                by_contra hno
                exact hDisj ⟨g, hg, e, he, f, hf, fun w hwe hwf => hno ⟨w, hwe, hwf⟩⟩
              obtain ⟨w1, hw1a, hw1e⟩ := hmeet _ he0 _ he1
              have hb1 : b ∈ e1 := by
                rcases Sym2.mem_iff.1 hw1a with rfl | rfl
                · exact (hna1 hw1e).elim
                · exact hw1e
              obtain ⟨c, he1eq⟩ := Sym2.mem_iff_exists.1 hb1
              have hbc : G.Adj b c := by
                have hmem := (Finset.mem_sdiff.1 (Finset.mem_inter.1 he1).2).1
                rw [he1eq, SimpleGraph.mem_edgeFinset] at hmem
                exact hmem
              have hacNe : a ≠ c := by
                rintro rfl
                exact hna1 (he1eq ▸ Sym2.mem_mk_right b a)
              obtain ⟨w2, hw2a, hw2e⟩ := hmeet _ he0 _ he2
              have ha2 : a ∈ e2 := by
                rcases Sym2.mem_iff.1 hw2a with rfl | rfl
                · exact hw2e
                · exact (hnb2 hw2e).elim
              obtain ⟨w3, hw3b, hw3e⟩ := hmeet _ he1 _ he2
              have hc2 : c ∈ e2 := by
                rw [he1eq] at hw3b
                rcases Sym2.mem_iff.1 hw3b with rfl | rfl
                · exact (hnb2 hw3e).elim
                · exact hw3e
              have he2eq : e2 = s(a, c) := (Sym2.mem_and_mem_iff hacNe).1 ⟨ha2, hc2⟩
              have hac : G.Adj a c := by
                have hmem := (Finset.mem_sdiff.1 (Finset.mem_inter.1 he2).2).1
                rw [he2eq, SimpleGraph.mem_edgeFinset] at hmem
                exact hmem
              exact hNoTri a b c hab hbc hac
      let B : Finset (Fin 26) := (junk G C).attach.image fun g => Classical.choose (hStar g.1 g.2)
      have hBcard : B.card ≤ (junk G C).card := by
        calc B.card ≤ (junk G C).attach.card := Finset.card_image_le
          _ = (junk G C).card := Finset.card_attach
      have hBcov : ∀ e ∈ Ustar G C, ∃ v ∈ B, v ∈ e := by
        intro e he
        rcases hUstarCover e he with ⟨c, hc, _⟩ | ⟨⟨g, hg, hge⟩, _⟩
        · rw [hC0] at hc; exact (Finset.notMem_empty c hc).elim
        · exact ⟨Classical.choose (hStar g hg),
            Finset.mem_image.2 ⟨⟨g, hg⟩, Finset.mem_attach _ _, rfl⟩,
            Classical.choose_spec (hStar g hg) e hge⟩
      have h13TJ : 13 ≤ (tops G C).card + (junk G C).card := by
        have h13 := hCoverBound B hBcov
        rw [hTopEq] at h13
        omega
      have hres := starJunk G C hG hL hT hJ hSize hC0 hMixPos hU4 hHlt0 h13TJ hStar
      rw [hTopEq, hC0card]
      omega
  · have hCne : (centreless G C).Nonempty := Finset.nonempty_iff_ne_empty.2 hC0
    exact withCentreless G C hG hL hT hJ hSize hCne hU4 hDegBound hHlt hHeavy
