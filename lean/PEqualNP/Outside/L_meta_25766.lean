import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25766_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.Represents

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

private lemma wiresFrom_len (gs : List Gate) : ∀ w : List Bool,
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wiresFrom]
  | cons g gs ih =>
    intro w
    simp only [wiresFrom, List.foldl_cons, List.length_cons]
    rw [← wiresFrom, ih]
    simp only [List.length_append, List.length_singleton]
    omega

private lemma wiresFrom_getD_lt (gs : List Gate) : ∀ (w : List Bool) (i : ℕ),
    i < w.length → (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    simp only [wiresFrom, List.foldl_cons]
    rw [← wiresFrom, ih _ i (by simp only [List.length_append, List.length_singleton]; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma wiresFrom_step (gs : List Gate) (j : ℕ) (hj : j < gs.length) (x : List Bool) :
    (wiresFrom gs x).getD (x.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < x.length + j then (wiresFrom gs x).getD i false else false) := by
  induction gs generalizing x j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [wiresFrom, List.foldl_cons, Nat.add_zero, List.getElem_cons_zero]
      rw [← wiresFrom]
      have hlen : x.length < (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]).length := by
        simp
      rw [wiresFrom_getD_lt gs _ x.length hlen]
      conv_lhs =>
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.getD_some]
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with hi
      · rw [wiresFrom_getD_lt gs _ i (by simp only [List.length_append, List.length_singleton]; omega)]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
    | succ j' =>
      simp only [wiresFrom, List.foldl_cons, List.getElem_cons_succ]
      rw [← wiresFrom]
      let x' := x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]
      have hx'len : x'.length = x.length + 1 := by simp [x']
      have hidx : x.length + (j' + 1) = x'.length + j' := by omega
      rw [hidx]
      have hj' : j' < gs.length := by simp at hj; omega
      exact ih j' hj' x'

private def isNot : GateOp → Bool
  | .not => true
  | _ => false

private lemma isNot_iff (op : GateOp) : isNot op = true ↔ op = .not := by
  cases op <;> simp [isNot]

private def effInputs (N : ℕ) (C : Circuit) (j : Fin C.size) : List ℕ :=
  let g := C.gates[j.val]'j.isLt
  if isNot g.op then (g.inputs.take 1).filter (fun i => decide (i < N + j.val))
  else g.inputs.filter (fun i => decide (i < N + j.val))

private lemma effInputs_lt {N : ℕ} {C : Circuit} (j : Fin C.size) {w : ℕ}
    (hw : w ∈ effInputs N C j) : w < N + j.val := by
  simp only [effInputs] at hw
  split_ifs at hw <;> simp only [List.mem_filter, decide_eq_true_eq] at hw <;> exact hw.2

private lemma effInputs_len_le {N : ℕ} {C : Circuit} (hF : FanInTwo C) (j : Fin C.size) :
    (effInputs N C j).length + (if isNot (C.gates[j.val]'j.isLt).op then 1 else 0) ≤ 2 := by
  have hg := hF (C.gates[j.val]'j.isLt) (List.getElem_mem j.isLt)
  simp only [effInputs]
  split_ifs with hnot
  · have h1 : (((C.gates[j.val]'j.isLt).inputs.take 1).filter (fun i => decide (i < N + j.val))).length ≤
        ((C.gates[j.val]'j.isLt).inputs.take 1).length := List.length_filter_le _ _
    have h2 : ((C.gates[j.val]'j.isLt).inputs.take 1).length ≤ 1 := by simp
    omega
  · have h1 : ((C.gates[j.val]'j.isLt).inputs.filter (fun i => decide (i < N + j.val))).length ≤
        (C.gates[j.val]'j.isLt).inputs.length := List.length_filter_le _ _
    have h2 : (C.gates[j.val]'j.isLt).inputs.length ≤ 2 := hg.2
    omega

private lemma eval_gate_congr {N : ℕ} {C : Circuit} (hF : FanInTwo C)
    (j : Fin C.size) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (heq : ∀ w ∈ effInputs N C j, (C.wires x).getD w false = (C.wires y).getD w false) :
    (C.wires x).getD (N + j.val) false = (C.wires y).getD (N + j.val) false := by
  have hgx := wiresFrom_step C.gates j.val j.isLt x
  have hgy := wiresFrom_step C.gates j.val j.isLt y
  change (wiresFrom C.gates x).getD (N + j.val) false = (wiresFrom C.gates y).getD (N + j.val) false
  rw [← hx, hgx, hx, ← hy, hgy, hy]
  by_cases hnot : isNot (C.gates[j.val]'j.isLt).op = true
  · have hnot' : (C.gates[j.val]'j.isLt).op = .not := (isNot_iff _).mp hnot
    rw [hnot']
    simp only [GateOp.eval]
    cases hin : (C.gates[j.val]'j.isLt).inputs with
    | nil => rfl
    | cons a rest =>
      simp only [List.map_cons, List.headD_cons]
      split_ifs with ha
      · have hmem : a ∈ effInputs N C j := by
          simp only [effInputs, hnot, ↓reduceIte, hin, List.take_succ_cons, List.take_zero,
            List.mem_filter, List.mem_cons, true_or, true_and, decide_eq_true_eq]
          exact ha
        have h1 : (wiresFrom C.gates x).getD a false = (wiresFrom C.gates y).getD a false := heq a hmem
        rw [h1]
      · rfl
  · congr 1
    refine List.map_congr_left fun a ha => ?_
    split_ifs with hlt
    · have hmem : a ∈ effInputs N C j := by
        simp only [effInputs, hnot, Bool.false_eq_true, ↓reduceIte, List.mem_filter, decide_eq_true_eq]
        exact ⟨ha, hlt⟩
      exact heq a hmem
    · rfl

private lemma eval_gate_mono {N : ℕ} {C : Circuit} (hF : FanInTwo C)
    (j : Fin C.size) (hnot : isNot (C.gates[j.val]'j.isLt).op ≠ true)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hmono : ∀ w ∈ effInputs N C j, (C.wires x).getD w false = true → (C.wires y).getD w false = true) :
    (C.wires x).getD (N + j.val) false = true → (C.wires y).getD (N + j.val) false = true := by
  have hgx := wiresFrom_step C.gates j.val j.isLt x
  have hgy := wiresFrom_step C.gates j.val j.isLt y
  change (wiresFrom C.gates x).getD (N + j.val) false = true →
    (wiresFrom C.gates y).getD (N + j.val) false = true
  rw [← hx, hgx, hx, ← hy, hgy, hy]
  have hg := (hF (C.gates[j.val]'j.isLt) (List.getElem_mem j.isLt)).1
  have hnot' : (C.gates[j.val]'j.isLt).op ≠ .not := fun h => hnot ((isNot_iff _).mpr h)
  have hop : (C.gates[j.val]'j.isLt).op = .and ∨ (C.gates[j.val]'j.isLt).op = .or := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hnot'
  rcases hop with hand | hor
  · rw [hand]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro h a ha
    have h1 := h a ha
    split_ifs at h1 ⊢ with hlt
    have hmem : a ∈ effInputs N C j := by
      simp only [effInputs, hnot, Bool.false_eq_true, ↓reduceIte, List.mem_filter, decide_eq_true_eq]
      exact ⟨ha, hlt⟩
    exact hmono a hmem h1
  · rw [hor]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨_, ⟨a, ha, rfl⟩, h1⟩
    refine ⟨_, ⟨a, ha, rfl⟩, ?_⟩
    split_ifs at h1 ⊢ with hlt
    have hmem : a ∈ effInputs N C j := by
      simp only [effInputs, hnot, Bool.false_eq_true, ↓reduceIte, List.mem_filter, decide_eq_true_eq]
      exact ⟨ha, hlt⟩
    exact hmono a hmem h1

private lemma eval_gate_not {N : ℕ} {C : Circuit}
    (j : Fin C.size) (hnot : isNot (C.gates[j.val]'j.isLt).op = true)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hanti : ∀ w ∈ effInputs N C j, (C.wires y).getD w false = true → (C.wires x).getD w false = true) :
    (C.wires x).getD (N + j.val) false = true → (C.wires y).getD (N + j.val) false = true := by
  have hgx := wiresFrom_step C.gates j.val j.isLt x
  have hgy := wiresFrom_step C.gates j.val j.isLt y
  change (wiresFrom C.gates x).getD (N + j.val) false = true →
    (wiresFrom C.gates y).getD (N + j.val) false = true
  have hnot' : (C.gates[j.val]'j.isLt).op = .not := (isNot_iff _).mp hnot
  rw [← hx, hgx, hx, ← hy, hgy, hy, hnot']
  simp only [GateOp.eval]
  cases hin : (C.gates[j.val]'j.isLt).inputs with
  | nil => intro h; exact h
  | cons a rest =>
    simp only [List.map_cons, List.headD_cons]
    split_ifs with ha
    · have hmem : a ∈ effInputs N C j := by
        simp only [effInputs, hnot, ↓reduceIte, hin, List.take_succ_cons, List.take_zero,
          List.mem_filter, List.mem_cons, true_or, true_and, decide_eq_true_eq]
        exact ha
      intro hx1
      have hxf : (wiresFrom C.gates x).getD a false = false := by
        cases hv : (wiresFrom C.gates x).getD a false
        · rfl
        · rw [hv] at hx1; simp at hx1
      cases hyv : (wiresFrom C.gates y).getD a false
      · rfl
      · exfalso
        have h1 : (wiresFrom C.gates x).getD a false = true := hanti a hmem hyv
        rw [hxf] at h1
        simp at h1
    · intro h; exact h

private inductive InCone (N : ℕ) (C : Circuit) (r0 : Fin C.size) : Fin C.size → Prop
  | root : InCone N C r0 r0
  | step (j h : Fin C.size) : InCone N C r0 j → N + h.val ∈ effInputs N C j → InCone N C r0 h

private lemma inCone_le {N : ℕ} {C : Circuit} {r0 : Fin C.size} {j : Fin C.size}
    (hj : InCone N C r0 j) : j.val ≤ r0.val := by
  induction hj with
  | root => exact le_refl _
  | step j h _ hmem ih =>
    have hlt := effInputs_lt j hmem
    omega

private inductive Dep (N : ℕ) (C : Circuit) (Cone : Finset (Fin C.size)) (k : ℕ) : ℕ → Prop
  | base : Dep N C Cone k k
  | step (j : Fin C.size) (w : ℕ) :
      j ∈ Cone → w ∈ effInputs N C j → Dep N C Cone k w → Dep N C Cone k (N + j.val)

private lemma dep_ge {N : ℕ} {C : Circuit} {Cone : Finset (Fin C.size)} {k w : ℕ}
    (h : Dep N C Cone k w) : k ≤ w := by
  induction h with
  | base => exact le_refl _
  | step j w _ hmem _ ih =>
    have hlt := effInputs_lt j hmem
    omega

private lemma dep_unique_step {N : ℕ} {C : Circuit} {Cone : Finset (Fin C.size)} {k : ℕ}
    (huses : ∀ w : ℕ, (∑ j ∈ Cone, (effInputs N C j).count w) ≤ 1) :
    ∀ (w2 w1 : ℕ), Dep N C Cone k w1 → Dep N C Cone k w2 → w1 < w2 →
      ∃ j ∈ Cone, w1 ∈ effInputs N C j ∧ Dep N C Cone k (N + j.val) ∧ N + j.val ≤ w2 := by
  intro w2
  induction w2 using Nat.strong_induction_on with
  | ind w2 ih =>
    intro w1 hw1 hw2 hlt
    have hk_le : k ≤ w1 := dep_ge hw1
    cases hw2 with
    | base => omega
    | step j2 w2' hj2 hmem2 hw2' =>
      have hw2'_lt : w2' < N + j2.val := effInputs_lt j2 hmem2
      rcases lt_trichotomy w1 w2' with h1 | h1 | h1
      · obtain ⟨j, hjC, hmem, hdep, hle⟩ := ih w2' hw2'_lt w1 hw1 hw2' h1
        exact ⟨j, hjC, hmem, hdep, le_trans hle (le_of_lt hw2'_lt)⟩
      · subst h1
        exact ⟨j2, hj2, hmem2, Dep.step j2 w1 hj2 hmem2 hw1, le_refl _⟩
      · obtain ⟨j, hjC, hmem, _, hle⟩ := ih w1 hlt w2' hw2' hw1 h1
        have hj_ne : j ≠ j2 := by
          intro heq
          subst heq
          omega
        have hsum_ge : 2 ≤ ∑ g ∈ Cone, (effInputs N C g).count w2' := by
          have hc1 : 1 ≤ (effInputs N C j).count w2' := List.count_pos_iff.mpr hmem
          have hc2 : 1 ≤ (effInputs N C j2).count w2' := List.count_pos_iff.mpr hmem2
          have hsub : ({j, j2} : Finset (Fin C.size)) ⊆ Cone := by
            intro g hg
            simp only [Finset.mem_insert, Finset.mem_singleton] at hg
            rcases hg with rfl | rfl <;> assumption
          have hle_sum : ∑ g ∈ ({j, j2} : Finset (Fin C.size)), (effInputs N C g).count w2' ≤
              ∑ g ∈ Cone, (effInputs N C g).count w2' :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
          rw [Finset.sum_pair hj_ne] at hle_sum
          omega
        have := huses w2'
        omega

private lemma dep_no_two_in_eff {N : ℕ} {C : Circuit} {Cone : Finset (Fin C.size)} {k : ℕ}
    (huses : ∀ w : ℕ, (∑ j ∈ Cone, (effInputs N C j).count w) ≤ 1)
    {j : Fin C.size} (hj : j ∈ Cone) {w1 w2 : ℕ}
    (h1 : w1 ∈ effInputs N C j) (h2 : w2 ∈ effInputs N C j)
    (hd1 : Dep N C Cone k w1) (hd2 : Dep N C Cone k w2) : w1 = w2 := by
  by_contra hne
  have hlt_case : ∀ (a b : ℕ), a ∈ effInputs N C j → b ∈ effInputs N C j →
      Dep N C Cone k a → Dep N C Cone k b → a < b → False := by
    intro a b ha hb hda hdb hab
    obtain ⟨j1, hj1, ha1, _, hle1⟩ := dep_unique_step huses b a hda hdb hab
    have hblt : b < N + j.val := effInputs_lt j hb
    have hj_ne : j1 ≠ j := by
      intro heq
      subst heq
      omega
    have hsum_ge : 2 ≤ ∑ g ∈ Cone, (effInputs N C g).count a := by
      have hc1 : 1 ≤ (effInputs N C j1).count a := List.count_pos_iff.mpr ha1
      have hc2 : 1 ≤ (effInputs N C j).count a := List.count_pos_iff.mpr ha
      have hsub : ({j1, j} : Finset (Fin C.size)) ⊆ Cone := by
        intro g hg
        simp only [Finset.mem_insert, Finset.mem_singleton] at hg
        rcases hg with rfl | rfl <;> assumption
      have hle_sum : ∑ g ∈ ({j1, j} : Finset (Fin C.size)), (effInputs N C g).count a ≤
          ∑ g ∈ Cone, (effInputs N C g).count a :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
      rw [Finset.sum_pair hj_ne] at hle_sum
      omega
    have := huses a
    omega
  rcases lt_trichotomy w1 w2 with h | h | h
  · exact hlt_case w1 w2 h1 h2 hd1 hd2 h
  · exact hne h
  · exact hlt_case w2 w1 h2 h1 hd2 hd1 h

private lemma oneEach_len {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

private lemma oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (hi : i < n + m) :
    (oneEach u v).getD i false =
      if h : i < n then decide (i = u.val) else decide (i - n = v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · simp only [h, ↓reduceDIte]
    rw [List.getElem?_append_left (by simp; exact h)]
    simp [List.getElem?_ofFn, h, Fin.ext_iff]
  · simp only [h, ↓reduceDIte]
    rw [List.getElem?_append_right (by simp; omega)]
    have hlen : (List.ofFn (fun i : Fin n => decide (i = u))).length = n := by simp
    rw [hlen]
    have hlt : i - n < m := by omega
    simp [List.getElem?_ofFn, hlt, Fin.ext_iff]

private theorem solve_25766 (n m : ℕ) (A : Fin n → Fin m → Bool) (C : Circuit)
    (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hrow : ∀ u u' : Fin n, u ≠ u' → ∃ v, A u v = true ∧ A u' v = false)
    (hcol : ∀ v v' : Fin m, v ≠ v' → ∃ u, A u v = true ∧ A u v' = false)
    (hF : FanInTwo C) (hR : Represents A C) : n + m - 1 ≤ C.size := by
  classical
  let N := n + m
  have hout_ge : N ≤ C.output := by
    by_contra hlt
    push Not at hlt
    by_cases hrow_wire : C.output < n
    · obtain ⟨v0, v1, hvne⟩ : ∃ v0 v1 : Fin m, v0 ≠ v1 :=
        ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by intro h; have := congrArg Fin.val h; simp at this⟩
      obtain ⟨u, hu0, hu1⟩ := hcol v0 v1 hvne
      have he0 : C.eval (oneEach u v0) = (oneEach u v0).getD C.output false :=
        wiresFrom_getD_lt C.gates (oneEach u v0) C.output (by rw [oneEach_len]; omega)
      have he1 : C.eval (oneEach u v1) = (oneEach u v1).getD C.output false :=
        wiresFrom_getD_lt C.gates (oneEach u v1) C.output (by rw [oneEach_len]; omega)
      rw [hR u v0, oneEach_getD u v0 C.output hlt] at he0
      rw [hR u v1, oneEach_getD u v1 C.output hlt] at he1
      simp only [hrow_wire, ↓reduceDIte] at he0 he1
      rw [hu0] at he0
      rw [hu1] at he1
      rw [← he0] at he1
      simp at he1
    · obtain ⟨u0, u1, hune⟩ : ∃ u0 u1 : Fin n, u0 ≠ u1 :=
        ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by intro h; have := congrArg Fin.val h; simp at this⟩
      obtain ⟨v, hv0, hv1⟩ := hrow u0 u1 hune
      have he0 : C.eval (oneEach u0 v) = (oneEach u0 v).getD C.output false :=
        wiresFrom_getD_lt C.gates (oneEach u0 v) C.output (by rw [oneEach_len]; omega)
      have he1 : C.eval (oneEach u1 v) = (oneEach u1 v).getD C.output false :=
        wiresFrom_getD_lt C.gates (oneEach u1 v) C.output (by rw [oneEach_len]; omega)
      rw [hR u0 v, oneEach_getD u0 v C.output hlt] at he0
      rw [hR u1 v, oneEach_getD u1 v C.output hlt] at he1
      simp only [hrow_wire, ↓reduceDIte] at he0 he1
      rw [hv0] at he0
      rw [hv1] at he1
      rw [← he0] at he1
      simp at he1
  have hout_lt : C.output < N + C.size := by
    by_contra hge
    push Not at hge
    obtain ⟨u0, u1, hune⟩ : ∃ u0 u1 : Fin n, u0 ≠ u1 :=
      ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by intro h; have := congrArg Fin.val h; simp at this⟩
    obtain ⟨v, hv0, _⟩ := hrow u0 u1 hune
    have he : C.eval (oneEach u0 v) = false := by
      simp only [Circuit.eval, List.getD_eq_getElem?_getD]
      have hlen : (C.wires (oneEach u0 v)).length = N + C.size := by
        change (wiresFrom C.gates (oneEach u0 v)).length = N + C.gates.length
        rw [wiresFrom_len, oneEach_len]
      rw [List.getElem?_eq_none (by omega)]
      rfl
    rw [hR u0 v, hv0] at he
    simp at he
  let r0 : Fin C.size := ⟨C.output - N, by omega⟩
  have hr0_eq : N + r0.val = C.output := by dsimp only [r0]; omega
  let Cone : Finset (Fin C.size) := Finset.univ.filter (fun j => InCone N C r0 j)
  have hr0_mem : r0 ∈ Cone := Finset.mem_filter.mpr ⟨Finset.mem_univ _, InCone.root⟩
  have hCone_step : ∀ j ∈ Cone, ∀ h : Fin C.size, N + h.val ∈ effInputs N C j → h ∈ Cone := by
    intro j hj h hmem
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, InCone.step j h (Finset.mem_filter.mp hj).2 hmem⟩
  let Uin : Finset (Fin N) := Finset.univ.filter (fun k => ∃ j ∈ Cone, k.val ∈ effInputs N C j)
  let uses (w : ℕ) : ℕ := ∑ j ∈ Cone, (effInputs N C j).count w
  let K := Cone.card
  let Knot := (Cone.filter (fun j => isNot (C.gates[j.val]'j.isLt).op = true)).card
  let excIn := ∑ k ∈ Uin, (uses k.val - 1)
  let excGate := ∑ h ∈ Cone.erase r0, (uses (N + h.val) - 1)
  have hE_upper : (∑ j ∈ Cone, (effInputs N C j).length) + Knot ≤ 2 * K := by
    have hKnot_sum : Knot = ∑ j ∈ Cone, if isNot (C.gates[j.val]'j.isLt).op = true then 1 else 0 := by
      dsimp only [Knot]
      rw [Finset.card_filter]
    rw [hKnot_sum, ← Finset.sum_add_distrib]
    calc ∑ j ∈ Cone, ((effInputs N C j).length + if isNot (C.gates[j.val]'j.isLt).op = true then 1 else 0)
        ≤ ∑ _j ∈ Cone, 2 := Finset.sum_le_sum fun j _ => effInputs_len_le hF j
      _ = 2 * K := by simp [K, mul_comm]
  have hE_lower : Uin.card + (K - 1) + excIn + excGate = ∑ j ∈ Cone, (effInputs N C j).length := by
    let Wset : Finset ℕ := Uin.image Fin.val ∪ (Cone.erase r0).image (fun h : Fin C.size => N + h.val)
    have hdisj : Disjoint (Uin.image Fin.val) ((Cone.erase r0).image (fun h : Fin C.size => N + h.val)) := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      simp only [Finset.mem_image] at h1 h2
      obtain ⟨k, _, rfl⟩ := h1
      obtain ⟨h, _, heq⟩ := h2
      omega
    have hlen_eq : ∀ j ∈ Cone, (effInputs N C j).length = ∑ w ∈ Wset, (effInputs N C j).count w := by
      intro j hj
      have hsub : ∀ w ∈ effInputs N C j, w ∈ Wset := by
        intro w hw
        have hwlt : w < N + j.val := effInputs_lt j hw
        by_cases hwN : w < N
        · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨w, hwN⟩, ?_, rfl⟩)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hj, hw⟩
        · have hjle : j.val ≤ r0.val := inCone_le (Finset.mem_filter.mp hj).2
          let h : Fin C.size := ⟨w - N, by omega⟩
          have hweq : N + h.val = w := by dsimp only [h]; omega
          have hhC : h ∈ Cone := hCone_step j hj h (hweq.symm ▸ hw)
          have hhne : h ≠ r0 := by
            intro heq
            have := congrArg Fin.val heq
            dsimp only [h] at this
            omega
          exact Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨h, Finset.mem_erase.mpr ⟨hhne, hhC⟩, hweq⟩)
      have hcnt : ∀ (l : List ℕ), (∀ w ∈ l, w ∈ Wset) → l.length = ∑ w ∈ Wset, l.count w := by
        intro l
        induction l with
        | nil => intro _; simp
        | cons a l ih =>
          intro hl
          simp only [List.length_cons, List.count_cons, Finset.sum_add_distrib]
          rw [ih (fun w hw => hl w (List.mem_cons_of_mem a hw))]
          have haW : a ∈ Wset := hl a (List.mem_cons_self)
          have h1 : (∑ w ∈ Wset, if a == w then 1 else 0) = 1 := by
            have : (∑ w ∈ Wset, if a == w then 1 else 0) = (Wset.filter (fun w => a = w)).card := by
              rw [Finset.card_filter]
              refine Finset.sum_congr rfl fun w _ => ?_
              by_cases h : a = w <;> simp [h]
            rw [this]
            have hfilt : Wset.filter (fun w => a = w) = {a} := by
              ext w
              simp only [Finset.mem_filter, Finset.mem_singleton]
              exact ⟨fun h => h.2.symm, fun h => ⟨h ▸ haW, h.symm⟩⟩
            rw [hfilt, Finset.card_singleton]
          rw [h1]
      exact hcnt (effInputs N C j) hsub
    have hsum_eq : ∑ j ∈ Cone, (effInputs N C j).length = ∑ w ∈ Wset, uses w := by
      rw [Finset.sum_congr rfl hlen_eq, Finset.sum_comm]
    rw [hsum_eq, Finset.sum_union hdisj]
    rw [Finset.sum_image (fun _ _ _ _ h => Fin.ext h)]
    rw [Finset.sum_image (fun _ _ _ _ h => Fin.ext (by omega))]
    have hu_in : ∀ k ∈ Uin, 1 ≤ uses k.val := by
      intro k hk
      obtain ⟨j, hj, hmem⟩ := (Finset.mem_filter.mp hk).2
      have hc : 1 ≤ (effInputs N C j).count k.val := List.count_pos_iff.mpr hmem
      have hle : (effInputs N C j).count k.val ≤ uses k.val :=
        Finset.single_le_sum (f := fun g => (effInputs N C g).count k.val) (fun _ _ => Nat.zero_le _) hj
      omega
    have hu_gate : ∀ h ∈ Cone.erase r0, 1 ≤ uses (N + h.val) := by
      intro h hh
      have hne : h ≠ r0 := (Finset.mem_erase.mp hh).1
      have hin : InCone N C r0 h := (Finset.mem_filter.mp (Finset.mem_erase.mp hh).2).2
      cases hin with
      | root => exact absurd rfl hne
      | step j _ hj hmem =>
        have hjC : j ∈ Cone := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
        have hc : 1 ≤ (effInputs N C j).count (N + h.val) := List.count_pos_iff.mpr hmem
        have hle : (effInputs N C j).count (N + h.val) ≤ uses (N + h.val) :=
          Finset.single_le_sum (f := fun g => (effInputs N C g).count (N + h.val)) (fun _ _ => Nat.zero_le _) hjC
        omega
    have hs1 : ∑ k ∈ Uin, uses k.val = Uin.card + excIn := by
      have : ∑ k ∈ Uin, uses k.val = ∑ k ∈ Uin, (1 + (uses k.val - 1)) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have := hu_in k hk
        omega
      rw [this, Finset.sum_add_distrib]
      simp [excIn]
    have hs2 : ∑ h ∈ Cone.erase r0, uses (N + h.val) = (K - 1) + excGate := by
      have : ∑ h ∈ Cone.erase r0, uses (N + h.val) = ∑ h ∈ Cone.erase r0, (1 + (uses (N + h.val) - 1)) := by
        refine Finset.sum_congr rfl fun h hh => ?_
        have := hu_gate h hh
        omega
      rw [this, Finset.sum_add_distrib]
      have herase : (Cone.erase r0).card = K - 1 := by
        have := Finset.card_erase_add_one hr0_mem
        dsimp only [K]
        omega
      simp [excGate, herase]
    rw [hs1, hs2]
    omega
  have hfund : Uin.card + excIn + excGate + Knot ≤ K + 1 := by
    have hKpos : 1 ≤ K := Finset.card_pos.mpr ⟨r0, hr0_mem⟩
    omega
  have hcone_agrees : ∀ (x y : List Bool), x.length = N → y.length = N →
      (∀ k ∈ Uin, x.getD k.val false = y.getD k.val false) →
      C.eval x = C.eval y := by
    intro x y hx hy hagree
    have hgate : ∀ (t : ℕ) (j : Fin C.size), j.val = t → j ∈ Cone →
        (C.wires x).getD (N + j.val) false = (C.wires y).getD (N + j.val) false := by
      intro t
      induction t using Nat.strong_induction_on with
      | ind t ih =>
        intro j hjt hjC
        refine eval_gate_congr hF j x y hx hy fun w hw => ?_
        have hwlt : w < N + j.val := effInputs_lt j hw
        by_cases hwN : w < N
        · have hkU : (⟨w, hwN⟩ : Fin N) ∈ Uin := Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjC, hw⟩
          have h1 := wiresFrom_getD_lt C.gates x w (by omega)
          have h2 := wiresFrom_getD_lt C.gates y w (by omega)
          change (wiresFrom C.gates x).getD w false = (wiresFrom C.gates y).getD w false
          rw [h1, h2]
          exact hagree ⟨w, hwN⟩ hkU
        · let h : Fin C.size := ⟨w - N, by omega⟩
          have hweq : N + h.val = w := by dsimp only [h]; omega
          have hhC : h ∈ Cone := hCone_step j hjC h (hweq.symm ▸ hw)
          rw [← hweq]
          exact ih h.val (by dsimp only [h]; omega) h rfl hhC
    change (C.wires x).getD C.output false = (C.wires y).getD C.output false
    rw [← hr0_eq]
    exact hgate r0.val r0 rfl hr0_mem
  have hcone_mono : Knot = 0 → ∀ (x y : List Bool), x.length = N → y.length = N →
      (∀ k ∈ Uin, x.getD k.val false = true → y.getD k.val false = true) →
      C.eval x = true → C.eval y = true := by
    intro hKnot0 x y hx hy hle
    have hnoNot : ∀ j ∈ Cone, isNot (C.gates[j.val]'j.isLt).op ≠ true := by
      intro j hj hnot
      have hmem : j ∈ Cone.filter (fun j => isNot (C.gates[j.val]'j.isLt).op = true) :=
        Finset.mem_filter.mpr ⟨hj, hnot⟩
      have hpos : 0 < Knot := Finset.card_pos.mpr ⟨j, hmem⟩
      omega
    have hgate : ∀ (t : ℕ) (j : Fin C.size), j.val = t → j ∈ Cone →
        (C.wires x).getD (N + j.val) false = true → (C.wires y).getD (N + j.val) false = true := by
      intro t
      induction t using Nat.strong_induction_on with
      | ind t ih =>
        intro j hjt hjC
        refine eval_gate_mono hF j (hnoNot j hjC) x y hx hy fun w hw => ?_
        have hwlt : w < N + j.val := effInputs_lt j hw
        by_cases hwN : w < N
        · have hkU : (⟨w, hwN⟩ : Fin N) ∈ Uin := Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjC, hw⟩
          have h1 := wiresFrom_getD_lt C.gates x w (by omega)
          have h2 := wiresFrom_getD_lt C.gates y w (by omega)
          change (wiresFrom C.gates x).getD w false = true → (wiresFrom C.gates y).getD w false = true
          rw [h1, h2]
          exact hle ⟨w, hwN⟩ hkU
        · let h : Fin C.size := ⟨w - N, by omega⟩
          have hweq : N + h.val = w := by dsimp only [h]; omega
          have hhC : h ∈ Cone := hCone_step j hjC h (hweq.symm ▸ hw)
          rw [← hweq]
          exact ih h.val (by dsimp only [h]; omega) h rfl hhC
    change (C.wires x).getD C.output false = true → (C.wires y).getD C.output false = true
    rw [← hr0_eq]
    exact hgate r0.val r0 rfl hr0_mem
  let unRow : Finset (Fin n) := Finset.univ.filter (fun u => (⟨u.val, by omega⟩ : Fin N) ∉ Uin)
  let unCol : Finset (Fin m) := Finset.univ.filter (fun v => (⟨n + v.val, by omega⟩ : Fin N) ∉ Uin)
  have hunRow_le : unRow.card ≤ 1 := by
    by_contra hgt
    push Not at hgt
    obtain ⟨u1, hu1, u2, hu2, hne⟩ := Finset.one_lt_card.mp hgt
    have hu1' : (⟨u1.val, by omega⟩ : Fin N) ∉ Uin := (Finset.mem_filter.mp hu1).2
    have hu2' : (⟨u2.val, by omega⟩ : Fin N) ∉ Uin := (Finset.mem_filter.mp hu2).2
    obtain ⟨v, hv1, hv2⟩ := hrow u1 u2 hne
    have heq := hcone_agrees (oneEach u1 v) (oneEach u2 v) (oneEach_len u1 v) (oneEach_len u2 v)
      (fun k hk => by
        rw [oneEach_getD u1 v k.val k.isLt, oneEach_getD u2 v k.val k.isLt]
        split_ifs with hlt
        · have hk1 : k.val ≠ u1.val := fun h => by
            have hkeq : (⟨u1.val, by omega⟩ : Fin N) = k := Fin.ext h.symm
            exact hu1' (hkeq ▸ hk)
          have hk2 : k.val ≠ u2.val := fun h => by
            have hkeq : (⟨u2.val, by omega⟩ : Fin N) = k := Fin.ext h.symm
            exact hu2' (hkeq ▸ hk)
          simp [hk1, hk2]
        · rfl)
    rw [hR u1 v, hR u2 v, hv1, hv2] at heq
    simp at heq
  have hunCol_le : unCol.card ≤ 1 := by
    by_contra hgt
    push Not at hgt
    obtain ⟨v1, hv1, v2, hv2, hne⟩ := Finset.one_lt_card.mp hgt
    have hv1' : (⟨n + v1.val, by omega⟩ : Fin N) ∉ Uin := (Finset.mem_filter.mp hv1).2
    have hv2' : (⟨n + v2.val, by omega⟩ : Fin N) ∉ Uin := (Finset.mem_filter.mp hv2).2
    obtain ⟨u, hu1, hu2⟩ := hcol v1 v2 hne
    have heq := hcone_agrees (oneEach u v1) (oneEach u v2) (oneEach_len u v1) (oneEach_len u v2)
      (fun k hk => by
        rw [oneEach_getD u v1 k.val k.isLt, oneEach_getD u v2 k.val k.isLt]
        split_ifs with hlt
        · rfl
        · have hk1 : k.val - n ≠ v1.val := fun h => by
            have hkeq : (⟨n + v1.val, by omega⟩ : Fin N) = k := Fin.ext (by dsimp only; omega)
            exact hv1' (hkeq ▸ hk)
          have hk2 : k.val - n ≠ v2.val := fun h => by
            have hkeq : (⟨n + v2.val, by omega⟩ : Fin N) = k := Fin.ext (by dsimp only; omega)
            exact hv2' (hkeq ▸ hk)
          simp [hk1, hk2])
    rw [hR u v1, hR u v2, hu1, hu2] at heq
    simp at heq
  have hUin_sum : Uin.card + unRow.card + unCol.card = N := by
    have hcompl : (Finset.univ \ Uin).card = unRow.card + unCol.card := by
      have hdisj : Disjoint (unRow.image (fun u : Fin n => (⟨u.val, by omega⟩ : Fin N)))
          (unCol.image (fun v : Fin m => (⟨n + v.val, by omega⟩ : Fin N))) := by
        rw [Finset.disjoint_left]
        intro k h1 h2
        simp only [Finset.mem_image] at h1 h2
        obtain ⟨u, _, rfl⟩ := h1
        obtain ⟨v, _, heq⟩ := h2
        have := congrArg Fin.val heq
        dsimp only at this
        omega
      have heq_set : Finset.univ \ Uin =
          unRow.image (fun u : Fin n => (⟨u.val, by omega⟩ : Fin N)) ∪
          unCol.image (fun v : Fin m => (⟨n + v.val, by omega⟩ : Fin N)) := by
        ext k
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image,
          unRow, unCol, Finset.mem_filter]
        constructor
        · intro hk
          by_cases hlt : k.val < n
          · exact Or.inl ⟨⟨k.val, hlt⟩, hk, Fin.ext rfl⟩
          · refine Or.inr ⟨⟨k.val - n, by omega⟩, ?_, Fin.ext (by dsimp only; omega)⟩
            have hkeq : (⟨n + (k.val - n), by omega⟩ : Fin N) = k := Fin.ext (by dsimp only; omega)
            rwa [hkeq]
        · rintro (⟨u, hu, rfl⟩ | ⟨v, hv, rfl⟩)
          · exact hu
          · exact hv
      rw [heq_set, Finset.card_union_of_disjoint hdisj]
      have hinj1 : Function.Injective (fun u : Fin n => (⟨u.val, by omega⟩ : Fin N)) :=
        fun _ _ h => Fin.ext (congrArg (fun k : Fin N => k.val) h)
      have hinj2 : Function.Injective (fun v : Fin m => (⟨n + v.val, by omega⟩ : Fin N)) :=
        fun _ _ h => Fin.ext (by have := congrArg (fun k : Fin N => k.val) h; dsimp only at this; omega)
      rw [Finset.card_image_of_injective unRow hinj1, Finset.card_image_of_injective unCol hinj2]
    have hadd : Uin.card + (Finset.univ \ Uin).card = N := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
      have : Uin.card ≤ N := by
        calc Uin.card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_card (Finset.subset_univ _)
          _ = N := by simp
      omega
    omega
  have hKnot_pos_row : 0 < unRow.card → 1 ≤ Knot := by
    intro hpos
    by_contra h0
    have hK0 : Knot = 0 := by omega
    obtain ⟨u0, hu0⟩ := Finset.card_pos.mp hpos
    have hu0' : (⟨u0.val, by omega⟩ : Fin N) ∉ Uin := (Finset.mem_filter.mp hu0).2
    have hex_u1 : ∃ u1 : Fin n, u1 ≠ u0 := by
      by_cases h : u0.val = 0
      · exact ⟨⟨1, by omega⟩, fun heq => by have := congrArg Fin.val heq; dsimp only at this; omega⟩
      · exact ⟨⟨0, by omega⟩, fun heq => by have := congrArg Fin.val heq; dsimp only at this; omega⟩
    obtain ⟨u1, hu1_ne⟩ := hex_u1
    obtain ⟨v, hv0, hv1⟩ := hrow u0 u1 hu1_ne.symm
    have hle := hcone_mono hK0 (oneEach u0 v) (oneEach u1 v) (oneEach_len u0 v) (oneEach_len u1 v)
      (fun k hk hkx => by
        rw [oneEach_getD u0 v k.val k.isLt] at hkx
        rw [oneEach_getD u1 v k.val k.isLt]
        split_ifs at hkx ⊢ with hlt
        · exfalso
          simp only [decide_eq_true_eq] at hkx
          have hkeq : (⟨u0.val, by omega⟩ : Fin N) = k := Fin.ext hkx.symm
          exact hu0' (hkeq ▸ hk)
        · exact hkx)
    rw [hR u0 v, hR u1 v, hv0, hv1] at hle
    have := hle rfl
    simp at this
  have hKnot_pos_col : 0 < unCol.card → 1 ≤ Knot := by
    intro hpos
    by_contra h0
    have hK0 : Knot = 0 := by omega
    obtain ⟨v0, hv0⟩ := Finset.card_pos.mp hpos
    have hv0' : (⟨n + v0.val, by omega⟩ : Fin N) ∉ Uin := (Finset.mem_filter.mp hv0).2
    have hex_v1 : ∃ v1 : Fin m, v1 ≠ v0 := by
      by_cases h : v0.val = 0
      · exact ⟨⟨1, by omega⟩, fun heq => by have := congrArg Fin.val heq; dsimp only at this; omega⟩
      · exact ⟨⟨0, by omega⟩, fun heq => by have := congrArg Fin.val heq; dsimp only at this; omega⟩
    obtain ⟨v1, hv1_ne⟩ := hex_v1
    obtain ⟨u, hu0, hu1⟩ := hcol v0 v1 hv1_ne.symm
    have hle := hcone_mono hK0 (oneEach u v0) (oneEach u v1) (oneEach_len u v0) (oneEach_len u v1)
      (fun k hk hkx => by
        rw [oneEach_getD u v0 k.val k.isLt] at hkx
        rw [oneEach_getD u v1 k.val k.isLt]
        split_ifs at hkx ⊢ with hlt
        · exact hkx
        · exfalso
          simp only [decide_eq_true_eq] at hkx
          have hkeq : (⟨n + v0.val, by omega⟩ : Fin N) = k := Fin.ext (by dsimp only; omega)
          exact hv0' (hkeq ▸ hk))
    rw [hR u v0, hR u v1, hu0, hu1] at hle
    have := hle rfl
    simp at this
  have hexc_pos_row : 0 < unRow.card → 1 ≤ excIn + excGate := by
    intro hpos
    by_contra h0
    have hexcIn0 : excIn = 0 := by omega
    have hexcGate0 : excGate = 0 := by omega
    have huses_le1 : ∀ w : ℕ, uses w ≤ 1 := by
      intro w
      by_cases hpos_u : uses w = 0
      · omega
      · have hex_j : ∃ j ∈ Cone, w ∈ effInputs N C j := by
          by_contra hno
          push Not at hno
          have hzero : uses w = 0 := by
            apply Finset.sum_eq_zero
            intro j hj
            exact List.count_eq_zero.mpr (hno j hj)
          exact hpos_u hzero
        obtain ⟨j, hjC, hmem⟩ := hex_j
        have hwlt : w < N + j.val := effInputs_lt j hmem
        by_cases hwN : w < N
        · have hkU : (⟨w, hwN⟩ : Fin N) ∈ Uin := Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjC, hmem⟩
          have hle : uses w - 1 ≤ excIn :=
            Finset.single_le_sum (f := fun k : Fin N => uses k.val - 1) (fun _ _ => Nat.zero_le _) hkU
          omega
        · have hjle : j.val ≤ r0.val := inCone_le (Finset.mem_filter.mp hjC).2
          let h : Fin C.size := ⟨w - N, by omega⟩
          have hweq : N + h.val = w := by dsimp only [h]; omega
          have hhC : h ∈ Cone := hCone_step j hjC h (hweq.symm ▸ hmem)
          have hhne : h ≠ r0 := by
            intro heq
            have := congrArg Fin.val heq
            dsimp only [h] at this
            omega
          have hhe : h ∈ Cone.erase r0 := Finset.mem_erase.mpr ⟨hhne, hhC⟩
          have hle : uses (N + h.val) - 1 ≤ excGate :=
            Finset.single_le_sum (f := fun g : Fin C.size => uses (N + g.val) - 1)
              (fun _ _ => Nat.zero_le _) hhe
          rw [hweq] at hle
          omega
    obtain ⟨u0, hu0⟩ := Finset.card_pos.mp hpos
    have hu0' : (⟨u0.val, by omega⟩ : Fin N) ∉ Uin := (Finset.mem_filter.mp hu0).2
    have hex_u1 : ∃ u1 : Fin n, u1 ≠ u0 := by
      by_cases h : u0.val = 0
      · exact ⟨⟨1, by omega⟩, fun heq => by have := congrArg Fin.val heq; dsimp only at this; omega⟩
      · exact ⟨⟨0, by omega⟩, fun heq => by have := congrArg Fin.val heq; dsimp only at this; omega⟩
    obtain ⟨u1, hu1_ne⟩ := hex_u1
    have hu1_in : (⟨u1.val, by omega⟩ : Fin N) ∈ Uin := by
      by_contra hnot
      have hu1_un : u1 ∈ unRow := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩
      have hcard2 : 2 ≤ unRow.card := by
        have hsub : ({u0, u1} : Finset (Fin n)) ⊆ unRow := by
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl <;> assumption
        have hle := Finset.card_le_card hsub
        rw [Finset.card_pair hu1_ne.symm] at hle
        exact hle
      omega
    let k0 := u1.val
    have hpol : ∀ (t : ℕ) (j : Fin C.size), j.val = t → j ∈ Cone →
        (¬ Dep N C Cone k0 (N + j.val) →
          ∀ v : Fin m, (C.wires (oneEach u0 v)).getD (N + j.val) false =
            (C.wires (oneEach u1 v)).getD (N + j.val) false) ∧
        (Dep N C Cone k0 (N + j.val) →
          (∀ v : Fin m, (C.wires (oneEach u0 v)).getD (N + j.val) false = true →
            (C.wires (oneEach u1 v)).getD (N + j.val) false = true) ∨
          (∀ v : Fin m, (C.wires (oneEach u1 v)).getD (N + j.val) false = true →
            (C.wires (oneEach u0 v)).getD (N + j.val) false = true)) := by
      intro t
      induction t using Nat.strong_induction_on with
      | ind t ih =>
        intro j hjt hjC
        have hwire_nondep : ∀ w ∈ effInputs N C j, ¬ Dep N C Cone k0 w →
            ∀ v : Fin m, (C.wires (oneEach u0 v)).getD w false =
              (C.wires (oneEach u1 v)).getD w false := by
          intro w hw hndep v
          have hwlt : w < N + j.val := effInputs_lt j hw
          by_cases hwN : w < N
          · have hkU : (⟨w, hwN⟩ : Fin N) ∈ Uin := Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjC, hw⟩
            have h1 := wiresFrom_getD_lt C.gates (oneEach u0 v) w (by rw [oneEach_len]; omega)
            have h2 := wiresFrom_getD_lt C.gates (oneEach u1 v) w (by rw [oneEach_len]; omega)
            change (wiresFrom C.gates (oneEach u0 v)).getD w false =
              (wiresFrom C.gates (oneEach u1 v)).getD w false
            rw [h1, h2, oneEach_getD u0 v w hwN, oneEach_getD u1 v w hwN]
            split_ifs with hlt
            · have hw_ne0 : w ≠ u0.val := fun h => by
                have hkeq : (⟨u0.val, by omega⟩ : Fin N) = ⟨w, hwN⟩ := Fin.ext h.symm
                exact hu0' (hkeq ▸ hkU)
              have hw_ne1 : w ≠ u1.val := fun h => hndep (h.symm ▸ Dep.base)
              simp [hw_ne0, hw_ne1]
            · rfl
          · let h : Fin C.size := ⟨w - N, by omega⟩
            have hweq : N + h.val = w := by dsimp only [h]; omega
            have hhC : h ∈ Cone := hCone_step j hjC h (hweq.symm ▸ hw)
            rw [← hweq]
            exact (ih h.val (by dsimp only [h]; omega) h rfl hhC).1 (hweq.symm ▸ hndep) v
        constructor
        · intro hndep v
          refine eval_gate_congr hF j (oneEach u0 v) (oneEach u1 v) (oneEach_len u0 v) (oneEach_len u1 v)
            fun w hw => ?_
          have hnd : ¬ Dep N C Cone k0 w := fun hd => hndep (Dep.step j w hjC hw hd)
          exact hwire_nondep w hw hnd v
        · intro hdep
          have hex_w : ∃ w ∈ effInputs N C j, Dep N C Cone k0 w := by
            generalize hwn : N + j.val = wn at hdep
            cases hdep with
            | base =>
              dsimp only [k0] at hwn
              omega
            | step j' w _ hmem hdw =>
              have hjeq : j' = j := Fin.ext (by omega)
              subst hjeq
              exact ⟨w, hmem, hdw⟩
          obtain ⟨w0, hw0_mem, hw0_dep⟩ := hex_w
          have hw0_uniq : ∀ w ∈ effInputs N C j, Dep N C Cone k0 w → w = w0 := fun w hw hdw =>
            dep_no_two_in_eff huses_le1 hjC hw hw0_mem hdw hw0_dep
          have hw0_pol : (∀ v : Fin m, (C.wires (oneEach u0 v)).getD w0 false = true →
                (C.wires (oneEach u1 v)).getD w0 false = true) ∨
              (∀ v : Fin m, (C.wires (oneEach u1 v)).getD w0 false = true →
                (C.wires (oneEach u0 v)).getD w0 false = true) := by
            have hwlt : w0 < N + j.val := effInputs_lt j hw0_mem
            by_cases hwN : w0 < N
            · left
              intro v htrue
              have hkU : (⟨w0, hwN⟩ : Fin N) ∈ Uin :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjC, hw0_mem⟩
              have h1 := wiresFrom_getD_lt C.gates (oneEach u0 v) w0 (by rw [oneEach_len]; omega)
              have h2 := wiresFrom_getD_lt C.gates (oneEach u1 v) w0 (by rw [oneEach_len]; omega)
              change (wiresFrom C.gates (oneEach u0 v)).getD w0 false = true at htrue
              change (wiresFrom C.gates (oneEach u1 v)).getD w0 false = true
              rw [h1, oneEach_getD u0 v w0 hwN] at htrue
              rw [h2, oneEach_getD u1 v w0 hwN]
              split_ifs at htrue ⊢ with hlt
              · exfalso
                simp only [decide_eq_true_eq] at htrue
                have hkeq : (⟨u0.val, by omega⟩ : Fin N) = ⟨w0, hwN⟩ := Fin.ext htrue.symm
                exact hu0' (hkeq ▸ hkU)
              · exact htrue
            · let h : Fin C.size := ⟨w0 - N, by omega⟩
              have hweq : N + h.val = w0 := by dsimp only [h]; omega
              have hhC : h ∈ Cone := hCone_step j hjC h (hweq.symm ▸ hw0_mem)
              rw [← hweq]
              exact (ih h.val (by dsimp only [h]; omega) h rfl hhC).2 (hweq.symm ▸ hw0_dep)
          by_cases hnot : isNot (C.gates[j.val]'j.isLt).op = true
          · rcases hw0_pol with hinc | hdec
            · right
              intro v
              refine eval_gate_not j hnot (oneEach u1 v) (oneEach u0 v) (oneEach_len u1 v) (oneEach_len u0 v)
                fun w hw => ?_
              by_cases hdw : Dep N C Cone k0 w
              · rw [hw0_uniq w hw hdw]; exact hinc v
              · rw [hwire_nondep w hw hdw v]; exact id
            · left
              intro v
              refine eval_gate_not j hnot (oneEach u0 v) (oneEach u1 v) (oneEach_len u0 v) (oneEach_len u1 v)
                fun w hw => ?_
              by_cases hdw : Dep N C Cone k0 w
              · rw [hw0_uniq w hw hdw]; exact hdec v
              · rw [hwire_nondep w hw hdw v]; exact id
          · rcases hw0_pol with hinc | hdec
            · left
              intro v
              refine eval_gate_mono hF j hnot (oneEach u0 v) (oneEach u1 v) (oneEach_len u0 v) (oneEach_len u1 v)
                fun w hw => ?_
              by_cases hdw : Dep N C Cone k0 w
              · rw [hw0_uniq w hw hdw]; exact hinc v
              · rw [hwire_nondep w hw hdw v]; exact id
            · right
              intro v
              refine eval_gate_mono hF j hnot (oneEach u1 v) (oneEach u0 v) (oneEach_len u1 v) (oneEach_len u0 v)
                fun w hw => ?_
              by_cases hdw : Dep N C Cone k0 w
              · rw [hw0_uniq w hw hdw]; exact hdec v
              · rw [hwire_nondep w hw hdw v]; exact id
    have hr0_pol := hpol r0.val r0 rfl hr0_mem
    obtain ⟨vA, hvA0, hvA1⟩ := hrow u0 u1 hu1_ne.symm
    obtain ⟨vB, hvB1, hvB0⟩ := hrow u1 u0 hu1_ne
    by_cases hdep_r0 : Dep N C Cone k0 (N + r0.val)
    · rcases hr0_pol.2 hdep_r0 with hinc | hdec
      · have h1 := hinc vA
        rw [hr0_eq] at h1
        change C.eval (oneEach u0 vA) = true → C.eval (oneEach u1 vA) = true at h1
        rw [hR u0 vA, hR u1 vA, hvA0, hvA1] at h1
        have := h1 rfl
        simp at this
      · have h1 := hdec vB
        rw [hr0_eq] at h1
        change C.eval (oneEach u1 vB) = true → C.eval (oneEach u0 vB) = true at h1
        rw [hR u1 vB, hR u0 vB, hvB1, hvB0] at h1
        have := h1 rfl
        simp at this
    · have h1 := hr0_pol.1 hdep_r0 vA
      rw [hr0_eq] at h1
      change C.eval (oneEach u0 vA) = C.eval (oneEach u1 vA) at h1
      rw [hR u0 vA, hR u1 vA, hvA0, hvA1] at h1
      simp at h1
  have hK_le : K ≤ C.size := by
    calc K ≤ (Finset.univ : Finset (Fin C.size)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = C.size := by simp
  by_cases hr : unRow.card = 0
  · by_cases hc : unCol.card = 0
    · omega
    · have := hKnot_pos_col (by omega)
      omega
  · have h1 := hKnot_pos_row (by omega)
    have h2 := hexc_pos_row (by omega)
    omega

end PEqualNP.Outside.L_meta_25766_aux

theorem PEqualNP.Outside.L_meta_25766 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ n → 2 ≤ m → (∀ u u' : Fin n, u ≠ u' → ∃ v, A u v = true ∧ A u' v = false) → (∀ v v' : Fin m, v ≠ v' → ∃ u, A u v = true ∧ A u v' = false) → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → n + m - 1 ≤ C.size := by
  intro n m A C hn hm hrow hcol hF hR
  exact PEqualNP.Outside.L_meta_25766_aux.solve_25766 n m A C hn hm hrow hcol hF hR
