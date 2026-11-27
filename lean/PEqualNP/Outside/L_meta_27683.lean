import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27683_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def target (x : Fin 9 → Bool) : Bool :=
  ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
    (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))

private def g0 : Gate := ⟨.or, [0, 1]⟩
private def g1 : Gate := ⟨.or, [2, 5]⟩

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem fold_indep (gs : List Gate) (i : ℕ) (hi : i ∉ gs.flatMap Gate.inputs)
    (a b : List Bool) (hl : a.length = b.length)
    (h : ∀ j : ℕ, j ≠ i → a.getD j false = b.getD j false) :
    ∀ j : ℕ, j ≠ i → (gs.foldl stepW a).getD j false = (gs.foldl stepW b).getD j false := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    have hn : i ∉ g.inputs ∧ i ∉ gs.flatMap Gate.inputs := by
      simpa using hi
    have hm : g.inputs.map (fun j => a.getD j false) =
        g.inputs.map (fun j => b.getD j false) := by
      apply List.map_congr_left
      intro j hj
      exact h j (fun he => hn.1 (he ▸ hj))
    simp only [List.foldl_cons]
    apply ih hn.2 (stepW a g) (stepW b g)
    · simp [stepW, hl]
    · intro j hj
      by_cases hk : j < a.length
      · simpa only [stepW, List.getD_append _ _ _ _ hk,
          List.getD_append _ _ _ _ (hl ▸ hk)] using h j hj
      · rw [stepW, stepW, List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hk),
          List.getD_append_right _ _ _ _ (hl ▸ Nat.le_of_not_gt hk), hm, hl]

private def pfx (x : Fin 9 → Bool) : List Bool :=
  stepW (stepW (List.ofFn x) g0) g1

private def witRow (i : Fin 9) (flip : Bool) (j : Fin 9) : Bool :=
  (([162, 97, 112, 132, 68, 70, 20, 12, 10] : List ℕ).getD i.val 0).testBit j.val || (flip && (j == i))

private theorem witRows (i : Fin 9) :
    target (witRow i false) ≠ target (witRow i true) ∧
      ∀ j : Fin 11, j.val ≠ i.val →
        (pfx (witRow i false)).getD j.val false = (pfx (witRow i true)).getD j.val false := by
  fin_cases i <;> decide +kernel

private theorem forceInputs (C : Circuit)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = target x)
    (ho : C.output + 1 = 9 + C.size)
    (gs : List Gate)
    (hg : C.gates = g0 :: g1 :: gs) :
    ∀ i : ℕ, i < 9 → i ∈ gs.flatMap Gate.inputs := by
  intro i hi
  by_contra hn
  let k : Fin 9 := ⟨i, hi⟩
  have hlen (x : Fin 9 → Bool) : (pfx x).length = 11 := by simp [pfx, stepW]
  have hrows := witRows k
  have hagree : ∀ j : ℕ, j ≠ i →
      (pfx (witRow k false)).getD j false = (pfx (witRow k true)).getD j false := by
    intro j hj
    by_cases hj' : j < 11
    · exact hrows.2 ⟨j, hj'⟩ hj
    · have ha : (pfx (witRow k false)).length ≤ j := by rw [hlen]; omega
      have hb : (pfx (witRow k true)).length ≤ j := by rw [hlen]; omega
      simp [ha, hb]
  have hout : C.output ≠ i := by
    simp [Circuit.size, hg] at ho
    omega
  have hEq := fold_indep gs i hn _ _ (by rw [hlen, hlen]) hagree C.output hout
  have heval (x : Fin 9 → Bool) : C.eval (List.ofFn x) =
      (gs.foldl stepW (pfx x)).getD C.output false := by
    simp only [Circuit.eval, Circuit.wires, hg, List.foldl_cons]
    rfl
  rw [← heval, ← heval, he, he] at hEq
  exact hrows.1 hEq

private theorem refLength (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := h g (by simp)
    have hs := ih (fun a ha => h a (by simp [ha]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

private theorem nodup_card_le (l m : List ℕ) (hnd : l.Nodup) (hsub : ∀ x ∈ l, x ∈ m) :
    l.length ≤ m.length := by
  have h1 : l.toFinset ⊆ m.toFinset := fun x hx =>
    List.mem_toFinset.mpr (hsub x (List.mem_toFinset.mp hx))
  have h2 := Finset.card_le_card h1
  rw [List.toFinset_card_of_nodup hnd] at h2
  exact h2.trans (List.toFinset_card_le m)

private theorem main_contra (C : Circuit) (hfan : FanInTwo C) (hsz : C.size ≤ 11)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = target x)
    (ho : C.output + 1 = 9 + C.size)
    (hlive : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs)
    (h0 : C.gates.head? = some g0)
    (h1 : C.gates.tail.head? = some g1) : False := by
  rcases C with ⟨gates, out⟩
  cases gates with
  | nil => simp at h0
  | cons a rest =>
    cases rest with
    | nil => simp at h1
    | cons b gs =>
      have ha : a = g0 := Option.some.inj h0
      have hb : b = g1 := Option.some.inj h1
      subst a; subst b
      have hinputs := forceInputs ⟨g0 :: g1 :: gs, out⟩ he ho gs rfl
      have hsub : ∀ z ∈ List.range (10 + gs.length), z ∈ gs.flatMap Gate.inputs := by
        intro z hz
        rw [List.mem_range] at hz
        by_cases hz9 : z < 9
        · exact hinputs z hz9
        · let j : Fin (g0 :: g1 :: gs).length := ⟨z - 9, by simp; omega⟩
          obtain ⟨k, hjk, hk⟩ := hlive j (by simp [j]; omega)
          let g := (g0 :: g1 :: gs).get k
          have hzg : z ∈ g.inputs := by
            have : 9 + j.val = z := by dsimp [j]; omega
            rwa [this] at hk
          have hmem : g ∈ gs := by
            rcases List.mem_cons.mp (List.get_mem _ k) with e | hrest
            · have hh : z ∈ g0.inputs := e ▸ hzg
              simp [g0] at hh; omega
            · rcases List.mem_cons.mp hrest with e | htail
              · have hh : z ∈ g1.inputs := e ▸ hzg
                simp [g1] at hh; omega
              · exact htail
          exact List.mem_flatMap.mpr ⟨g, hmem, hzg⟩
      have hcard := nodup_card_le (List.range (10 + gs.length)) (gs.flatMap Gate.inputs)
        (List.nodup_range) hsub
      rw [List.length_range] at hcard
      have hlen := refLength gs (fun g hg => (hfan g (by simp [hg])).2)
      change (g0 :: g1 :: gs).length ≤ 11 at hsz
      simp only [List.length_cons] at hsz
      omega

end PEqualNP.Outside.L_meta_27683_aux

theorem PEqualNP.Outside.L_meta_27683 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 5]⟩) := by
  rintro ⟨C, hfan, hsz, he, ho, _, _, hlive, h0, h1⟩
  exact PEqualNP.Outside.L_meta_27683_aux.main_contra C hfan hsz he ho hlive h0 h1
