import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25503

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (x : List Bool) : List Bool := gs.foldl stp x

theorem W_snoc (gs : List Gate) (g : Gate) (x : List Bool) : W (gs ++ [g]) x = stp (W gs x) g := by
  simp [W, List.foldl_append]

theorem W_len (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [stp, ih]; omega

theorem getD_app_l (l l' : List Bool) (i : ℕ) (h : i < l.length) : (l ++ l').getD i false = l.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_m (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_big (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem W_lt (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (W gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc, stp, getD_app_l _ _ _ (by rw [W_len]; omega)]; exact ih

theorem or_true_of (g : Gate) (w : List Bool) (c : ℕ) (hc : c ∈ g.inputs) (hv : w.getD c false = true) :
    GateOp.or.eval (g.inputs.map fun i => w.getD i false) = true := by
  simp only [GateOp.eval, List.any_eq_true, List.mem_map]
  exact ⟨true, ⟨c, hc, hv⟩, rfl⟩

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem eval_eq (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem W_stable (gs : List Gate) (g : Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (W (gs ++ [g]) x).getD i false = (W gs x).getD i false := by
  rw [W_snoc, stp, getD_app_l _ _ _ (by rw [W_len]; omega)]

theorem W_take (gs : List Gate) (x : List Bool) (k i : ℕ) (hi : i < x.length + k) :
    (W gs x).getD i false = (W (gs.take k) x).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih =>
    by_cases hk : k ≤ gs.length
    · rw [List.take_append_of_le_length hk, W_stable _ _ _ _ (by omega)]; exact ih
    · rw [List.take_of_length_le (by simp; omega)]

theorem W_val (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ i ∈ (gs[j]).inputs, i < x.length + j) :
    (W gs x).getD (x.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (W gs x).getD i false) := by
  have h1 : gs.take (j + 1) = gs.take j ++ [gs[j]] := by
    rw [List.take_succ]; simp [List.getElem?_eq_getElem hj]
  rw [W_take gs x (j + 1) _ (by omega), h1, W_snoc, stp]
  have hl : (W (gs.take j) x).length = x.length + j := by
    rw [W_len, List.length_take]; omega
  have := getD_app_m (W (gs.take j) x) ((gs[j]).op.eval ((gs[j]).inputs.map fun i => (W (gs.take j) x).getD i false))
  rw [hl] at this
  rw [this]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (W_take gs x j i (hrb i hi)).symm

theorem eval_mono (g : Gate) (h : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (hle : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (hv : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases h with h | h <;> rw [h] at hv ⊢
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, id] at hv ⊢
    intro i hi; exact hle i hi (hv i hi)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hv ⊢
    obtain ⟨v, ⟨i, hi, rfl⟩, hv⟩ := hv
    exact ⟨true, ⟨i, hi, hle i hi hv⟩, rfl⟩

theorem gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
  simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = (decide (i = u.val) || decide (i = n + v.val)) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simpa using h)]
    have : i ≠ n + v.val := by omega
    simp [List.getElem?_ofFn, h, this, Fin.ext_iff]
  · rw [List.getElem?_append_right (by simpa using h)]
    have hu : i ≠ u.val := by have := u.isLt; omega
    by_cases h2 : i - n < m
    · simp [List.getElem?_ofFn, h2, hu, Fin.ext_iff]; omega
    · have : i ≠ n + v.val := by have := v.isLt; omega
      simp [List.getElem?_ofFn, h2, hu, this]

theorem uniq (C : Circuit) (w : ℕ)
    (h1 : PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w = 1)
    (g0 : Gate) (hg0 : g0 ∈ C.gates) (hw0 : w ∈ g0.inputs)
    (j : ℕ) (g : Gate) (hj : C.gates[j]? = some g) (hw : w ∈ g.inputs) : g = g0 := by
  obtain ⟨j0, hj0, rfl⟩ := List.getElem_of_mem hg0
  by_contra hne
  have hjl : j < C.gates.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hj
    cases hj
  have hjj : j ≠ j0 := by
    rintro rfl
    rw [List.getElem?_eq_getElem hj0] at hj
    exact hne (Option.some.inj hj).symm
  have ga : PEqualNP.MetaComplexity.NestedCover.gateAt C j = g := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]
  have gb : PEqualNP.MetaComplexity.NestedCover.gateAt C j0 = C.gates[j0] := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD, hj0]
  have hsub : ({j, j0} : Finset ℕ) ⊆ Finset.range C.size := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    simp only [Finset.mem_range, Circuit.size]
    rcases ht with rfl | rfl <;> assumption
  have hle := Finset.sum_le_sum_of_subset (f := fun t => (PEqualNP.MetaComplexity.NestedCover.gateAt C t).inputs.count w) hsub
  rw [Finset.sum_pair hjj] at hle
  simp only [ga, gb] at hle
  have c1 : 0 < g.inputs.count w := List.count_pos_iff.mpr hw
  have c2 : 0 < (C.gates[j0]).inputs.count w := List.count_pos_iff.mpr hw0
  unfold PEqualNP.MetaComplexity.NestedCover.readsIn at h1
  omega

theorem W_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (X Y : List Bool)
    (hl : X.length = Y.length)
    (hle : ∀ i, X.getD i false = true → Y.getD i false = true) :
    ∀ i, (W gs X).getD i false = true → (W gs Y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using hle
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hm g' (by simp [hg']))
    intro i
    rw [W_snoc, W_snoc]
    unfold stp
    have e1 : (W gs X).length = X.length + gs.length := W_len _ _
    have e2 : (W gs Y).length = X.length + gs.length := by rw [W_len, hl]
    rcases lt_trichotomy i (X.length + gs.length) with h | h | h
    · rw [getD_app_l _ _ _ (by omega), getD_app_l _ _ _ (by omega)]; exact ih' i
    · subst h
      have a1 := getD_app_m (W gs X) (g.op.eval (g.inputs.map fun i => (W gs X).getD i false))
      have a2 := getD_app_m (W gs Y) (g.op.eval (g.inputs.map fun i => (W gs Y).getD i false))
      rw [e1] at a1
      rw [e2] at a2
      rw [a1, a2]
      exact eval_mono g (hm g (by simp)) _ _ (fun k _ => ih' k)
    · rw [getD_big _ _ (by simp [e1]; omega)]
      intro hf
      exact absurd hf (by decide)

theorem core2 (N : ℕ) (X Y : List Bool) (hX : X.length = N) (hY : Y.length = N) (bad : ℕ → Prop)
    (hin : ∀ i, ¬ bad i → X.getD i false = Y.getD i false) (gs : List Gate)
    (hrb : ∀ j (hj : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < N + j)
    (hg : ∀ j (hj : j < gs.length), (∃ i ∈ (gs[j]).inputs, bad i) →
      (W gs X).getD (N + j) false = (W gs Y).getD (N + j) false) :
    ∀ i, ¬ bad i → (W gs X).getD i false = (W gs Y).getD i false := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h1 : i < N
    · rw [W_lt _ _ _ (by omega), W_lt _ _ _ (by omega)]; exact hin i hi
    · by_cases h2 : i < N + gs.length
      · obtain ⟨j, rfl⟩ : ∃ j, i = N + j := ⟨i - N, by omega⟩
        have hj : j < gs.length := by omega
        by_cases hb : ∃ k ∈ (gs[j]).inputs, bad k
        · exact hg j hj hb
        · simp only [not_exists, not_and] at hb
          have vX := W_val gs X j hj (by rw [hX]; exact hrb j hj)
          have vY := W_val gs Y j hj (by rw [hY]; exact hrb j hj)
          rw [hX] at vX
          rw [hY] at vY
          rw [vX, vY]
          congr 1
          apply List.map_congr_left
          intro k hk
          exact ih k (hrb j hj k hk) (hb k hk)
      · rw [getD_big _ _ (by rw [W_len]; omega), getD_big _ _ (by rw [W_len]; omega)]

theorem uniq_idx (C : Circuit) (w : ℕ)
    (h1 : PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length) w = 1)
    (j0 : ℕ) (hj0 : j0 < C.gates.length) (hw0 : w ∈ (C.gates[j0]).inputs)
    (j : ℕ) (hj : j < C.gates.length) (hw : w ∈ (C.gates[j]).inputs) : j = j0 := by
  by_contra hjj
  have hsub : ({j, j0} : Finset ℕ) ⊆ Finset.range C.gates.length := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    simp only [Finset.mem_range]
    rcases ht with rfl | rfl <;> assumption
  have hle := Finset.sum_le_sum_of_subset (f := fun t => (PEqualNP.MetaComplexity.NestedCover.gateAt C t).inputs.count w) hsub
  rw [Finset.sum_pair hjj] at hle
  simp only [gateAt_eq C j hj, gateAt_eq C j0 hj0] at hle
  have c1 : 0 < (C.gates[j]).inputs.count w := List.count_pos_iff.mpr hw
  have c2 : 0 < (C.gates[j0]).inputs.count w := List.count_pos_iff.mpr hw0
  unfold PEqualNP.MetaComplexity.NestedCover.readsIn at h1
  omega

theorem rb_idx (C : Circuit) (N : ℕ) (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack N C) :
    ∀ j (hj : j < C.gates.length), ∀ i ∈ (C.gates[j]).inputs, i < N + j := by
  intro j hj i hi
  exact hrb j hj i (by rw [gateAt_eq C j hj]; exact hi)

theorem turnon (C : Circuit) (N a s ra : ℕ) (X Y : List Bool) (hX : X.length = N) (hY : Y.length = N)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack N C)
    (heq : ∀ i, i ≠ a → X.getD i false = Y.getD i false) (haN : a < N) (hYa : Y.getD a false = true)
    (hreads : PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length) a = 1)
    (hra : ra < C.gates.length) (hor : (C.gates[ra]).op = GateOp.or)
    (hinp : (C.gates[ra]).inputs = [a, s] ∨ (C.gates[ra]).inputs = [s, a])
    (hon : (W C.gates X).getD (N + ra) false = true) :
    ∀ i, i ≠ a → (W C.gates X).getD i false = (W C.gates Y).getD i false := by
  have hrb' := rb_idx C N hrb
  have hmem : a ∈ (C.gates[ra]).inputs := by rcases hinp with h | h <;> simp [h]
  apply core2 N X Y hX hY (fun i => i = a) (fun i hi => heq i hi) C.gates hrb'
  intro j hj ⟨i, hi, hbad⟩
  have hi' : a ∈ (C.gates[j]).inputs := hbad ▸ hi
  have hjr : j = ra := uniq_idx C a hreads ra hra hmem j hj hi'
  subst hjr
  rw [hon]
  have vY := W_val C.gates Y j hj (by rw [hY]; exact hrb' j hj)
  rw [hY] at vY
  rw [vY, hor]
  exact (or_true_of _ _ a hi' (by rw [W_lt _ _ _ (by omega)]; exact hYa)).symm

theorem col_getD {n m : ℕ} (c : Fin m) (i : ℕ) :
    (List.replicate n false ++ List.ofFn (fun b : Fin m => decide (b = c))).getD i false =
      decide (i = n + c.val) := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simpa using h)]
    have : i ≠ n + c.val := by omega
    simp [h, this]
  · rw [List.getElem?_append_right (by simpa using h)]
    by_cases h2 : i - n < m
    · simp [h2, Fin.ext_iff]; omega
    · have : i ≠ n + c.val := by have := c.isLt; omega
      simp [h2, this]

theorem two_getD {n m : ℕ} (w v : Fin n) (c : Fin m) (i : ℕ) :
    (List.ofFn (fun a : Fin n => decide (a = w) || decide (a = v)) ++
      List.ofFn (fun b : Fin m => decide (b = c))).getD i false =
      (decide (i = w.val) || decide (i = v.val) || decide (i = n + c.val)) := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simpa using h)]
    have : i ≠ n + c.val := by omega
    simp [h, this, Fin.ext_iff]
  · rw [List.getElem?_append_right (by simpa using h)]
    have hw : i ≠ w.val := by have := w.isLt; omega
    have hv : i ≠ v.val := by have := v.isLt; omega
    by_cases h2 : i - n < m
    · simp [h2, hw, hv, Fin.ext_iff]; omega
    · have : i ≠ n + c.val := by have := c.isLt; omega
      simp [h2, hw, hv, this]

theorem and_all (l : List ℕ) (f : ℕ → Bool) (h : GateOp.and.eval (l.map f) = true) :
    ∀ k ∈ l, f k = true := by
  simpa [GateOp.eval, List.all_eq_true] using h

theorem sq (n m a gap : ℕ) (G : Fin n → Fin n → Bool) (rowPair : (Fin m × Bool) ↪ Fin n)
    (π : Equiv.Perm (Fin n)) (kept : Finset (Fin n))
    (hrow : ∀ i, (Finset.univ.filter
      (fun col : Fin n => G (rowPair (i, false)) col ≠ G (rowPair (i, true)) col)).card ≤ a)
    (hcol : ∀ b c, b ≠ c → a + gap ≤ (Finset.univ.filter (fun row : Fin n => G row b ≠ G row c)).card)
    (hsym : ∀ u ∈ kept, ∀ v ∈ kept, G u (π v) = G v (π u)) :
    gap * m ≤ gap * (n - kept.card) + ∑ u ∈ Finset.univ \ kept,
      min (Finset.univ.filter (fun onCol : Fin n => G u onCol = true)).card
        (Finset.univ.filter (fun offCol : Fin n => G u offCol = false)).card := by
  classical
  have hD : (Finset.univ \ kept).card = n - kept.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ kept), Finset.card_univ, Fintype.card_fin]
  let S : Finset (Fin m) := Finset.univ.filter
    (fun i => rowPair (i, false) ∈ kept ∧ rowPair (i, true) ∈ kept)
  have hlost : (Finset.univ \ S).card ≤ (Finset.univ \ kept).card := by
    apply Finset.card_le_card_of_injOn
      (fun i => if rowPair (i, false) ∈ kept then rowPair (i, true) else rowPair (i, false))
    · intro i hi
      simp only [S, Finset.coe_sdiff, Finset.coe_univ, Set.mem_diff, Set.mem_univ, true_and,
        Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, not_and] at hi ⊢
      split_ifs with h
      · exact hi h
      · exact h
    · intro i _ j _ hij
      dsimp only at hij
      split_ifs at hij <;> simpa using rowPair.injective hij
  have hm : m ≤ S.card + (Finset.univ \ kept).card := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    rw [Finset.card_univ, Fintype.card_fin] at h
    omega
  have hsurv : ∀ i ∈ S, gap ≤ ((Finset.univ \ kept).filter
      (fun w => G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card := by
    intro i hi
    obtain ⟨hp, hq⟩ : rowPair (i, false) ∈ kept ∧ rowPair (i, true) ∈ kept := by
      simpa [S] using hi
    have hne : π (rowPair (i, false)) ≠ π (rowPair (i, true)) := by
      intro h
      have := rowPair.injective (π.injective h)
      simp at this
    have h1 := hcol _ _ hne
    have h2 : (Finset.univ.filter
        (fun w => G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card
        = (kept.filter
            (fun w => G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card
          + ((Finset.univ \ kept).filter
            (fun w => G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card := by
      rw [← Finset.card_union_of_disjoint, ← Finset.filter_union,
        Finset.union_sdiff_of_subset (Finset.subset_univ kept)]
      exact Finset.disjoint_filter_filter Finset.disjoint_sdiff
    have h3 : (kept.filter
        (fun w => G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card ≤ a := by
      refine le_trans ?_ (hrow i)
      apply Finset.card_le_card_of_injOn (fun w => π w)
      · intro w hw
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hw ⊢
        rw [← hsym w hw.1 _ hp, ← hsym w hw.1 _ hq]
        exact hw.2
      · exact π.injective.injOn
    omega
  have hsum : gap * S.card ≤ ∑ w ∈ Finset.univ \ kept, (S.filter
      (fun i => G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card := by
    calc gap * S.card = ∑ _i ∈ S, gap := by simp [mul_comm]
      _ ≤ ∑ i ∈ S, ((Finset.univ \ kept).filter
          (fun w => G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card :=
        Finset.sum_le_sum hsurv
      _ = _ := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
  have hmin : ∀ w : Fin n, (S.filter
      (fun i => G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card ≤
      min (Finset.univ.filter (fun onCol : Fin n => G w onCol = true)).card
        (Finset.univ.filter (fun offCol : Fin n => G w offCol = false)).card := by
    intro w
    apply le_min
    · apply Finset.card_le_card_of_injOn
        (fun i => if G w (π (rowPair (i, false))) = true then π (rowPair (i, false))
          else π (rowPair (i, true)))
      · intro i hi
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi ⊢
        split_ifs with h
        · exact h
        · have h' := hi.2
          revert h h'
          cases G w (π (rowPair (i, false))) <;> cases G w (π (rowPair (i, true))) <;> simp
      · intro i _ j _ hij
        dsimp only at hij
        split_ifs at hij <;> simpa using rowPair.injective (π.injective hij)
    · apply Finset.card_le_card_of_injOn
        (fun i => if G w (π (rowPair (i, false))) = false then π (rowPair (i, false))
          else π (rowPair (i, true)))
      · intro i hi
        simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi ⊢
        split_ifs with h
        · exact h
        · have h' := hi.2
          revert h h'
          cases G w (π (rowPair (i, false))) <;> cases G w (π (rowPair (i, true))) <;> simp
      · intro i _ j _ hij
        dsimp only at hij
        split_ifs at hij <;> simpa using rowPair.injective (π.injective hij)
  rw [← hD]
  calc gap * m ≤ gap * (S.card + (Finset.univ \ kept).card) := Nat.mul_le_mul_left _ hm
    _ = gap * (Finset.univ \ kept).card + gap * S.card := by ring
    _ ≤ _ := Nat.add_le_add_left (hsum.trans (Finset.sum_le_sum fun w _ => hmin w)) _

def P (m u v : ℕ) : Prop :=
  u / 2 = v / 2 ∨ (v % 2 = 0 ∧ (u / 2 = v / 2 + 1 ∨ u / 2 + m = v / 2 + 1)) ∨
    (v % 2 = 1 ∧ (u / 2 = v / 2 + 2 + u % 2 ∨ u / 2 + m = v / 2 + 2 + u % 2))

def Gm (m u v : ℕ) : Bool :=
  decide (u / 2 = v / 2 ∨ u / 2 = (v / 2 + if v % 2 = 0 then 1 else 2 + u % 2) % m)

theorem Gm_iff (m u v : ℕ) (hm : 5 ≤ m) (hu : u < 2 * m) (hv : v < 2 * m) :
    Gm m u v = true ↔ P m u v := by
  unfold Gm P
  rw [decide_eq_true_iff]
  by_cases hp : v % 2 = 0
  · rw [ite_eq_left hp]
    by_cases hlt : v / 2 + 1 < m
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · have e : (v / 2 + 1) % m = v / 2 + 1 - m := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [e]; omega
  · rw [ite_eq_right hp]
    by_cases hlt : v / 2 + (2 + u % 2) < m
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · have e : (v / 2 + (2 + u % 2)) % m = v / 2 + (2 + u % 2) - m := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [e]; omega

theorem f1 (m i v v' : ℕ) (hm : 5 ≤ m) (hi : i < m) (hv : v < 2 * m) (hv' : v' < 2 * m)
    (h1 : ¬ (P m (2 * i) v ↔ P m (2 * i + 1) v)) (h2 : ¬ (P m (2 * i) v' ↔ P m (2 * i + 1) v'))
    (h3 : P m (2 * i) v ↔ P m (2 * i) v') : v = v' := by
  by_cases a1 : P m (2 * i) v <;> by_cases a2 : P m (2 * i + 1) v <;>
    by_cases b1 : P m (2 * i) v' <;> by_cases b2 : P m (2 * i + 1) v' <;>
    first
    | (exfalso; exact h1 ⟨fun _ => a2, fun _ => a1⟩)
    | (exfalso; exact h1 ⟨fun h => absurd h a1, fun h => absurd h a2⟩)
    | (exfalso; exact h2 ⟨fun _ => b2, fun _ => b1⟩)
    | (exfalso; exact h2 ⟨fun h => absurd h b1, fun h => absurd h b2⟩)
    | (exfalso; exact b1 (h3.1 a1))
    | (exfalso; exact a1 (h3.2 b1))
    | (unfold P at a1 a2 b1 b2; omega)

def rw4 (m v e t : ℕ) : ℕ :=
  2 * (if e = 0 then v / 2 else
    if v / 2 + (if v % 2 = 0 then 1 else 2 + t) < m then v / 2 + (if v % 2 = 0 then 1 else 2 + t)
    else v / 2 + (if v % 2 = 0 then 1 else 2 + t) - m) + t

theorem rw4_lt (m v e t : ℕ) (hm : 5 ≤ m) (hv : v < 2 * m) (ht : t < 2) : rw4 m v e t < 2 * m := by
  unfold rw4; split_ifs <;> omega

theorem rw4_P (m v e t : ℕ) (hm : 5 ≤ m) (hv : v < 2 * m) (ht : t < 2) : P m (rw4 m v e t) v := by
  unfold rw4 P; split_ifs <;> omega

theorem rw4_inj (m v e t e' t' : ℕ) (hm : 5 ≤ m) (hv : v < 2 * m) (he : e < 2) (ht : t < 2)
    (he' : e' < 2) (ht' : t' < 2) (h : rw4 m v e t = rw4 m v e' t') : e = e' ∧ t = t' := by
  unfold rw4 at h; split_ifs at h <;> omega

theorem f3 (m r r' c c' : ℕ) (hm : 5 ≤ m) (hr : r < 2 * m) (hr' : r' < 2 * m) (hc : c < 2 * m)
    (hc' : c' < 2 * m) (hne : c ≠ c') (h1 : P m r c) (h2 : P m r c') (h3 : P m r' c) (h4 : P m r' c')
    (hf1 : c % 2 = 1 ∧ c' % 2 = 1 → (r / 2 = c / 2 ↔ r' / 2 = c / 2))
    (hf2 : ¬ (c % 2 = 1 ∧ c' % 2 = 1) → (r % 2 = 0 ↔ r' % 2 = 0)) : r = r' := by
  unfold P at *; omega

theorem f4 (m u v v' : ℕ) (hm : 5 ≤ m) (hv : v < 2 * m) (hv' : v' < 2 * m)
    (h1 : P m u v) (h2 : P m u v') (h3 : v % 2 = 0 ↔ v' % 2 = 0) (h4 : u / 2 = v / 2 ↔ u / 2 = v' / 2) :
    v = v' := by
  unfold P at *; omega

theorem f5 (m u : ℕ) (hm : 5 ≤ m) (hu : u < 2 * m) : ∃ c, c < 2 * m ∧ ¬ P m u c :=
  ⟨2 * (if u / 2 + 1 < m then u / 2 + 1 else u / 2 + 1 - m), by split_ifs <;> omega,
    by unfold P; split_ifs <;> omega⟩

theorem f6 (m c : ℕ) (hm : 5 ≤ m) (hc : c < 2 * m) : ∃ u, u < 2 * m ∧ ¬ P m u c :=
  ⟨2 * (if c / 2 + 4 < m then c / 2 + 4 else c / 2 + 4 - m), by split_ifs <;> omega,
    by unfold P; split_ifs <;> omega⟩

def GG (m : ℕ) : Fin (2 * m) → Fin (2 * m) → Bool := fun u v => Gm m u.val v.val

theorem GG_iff (m : ℕ) (hm : 5 ≤ m) (u v : Fin (2 * m)) : GG m u v = true ↔ P m u.val v.val :=
  Gm_iff m _ _ hm u.isLt v.isLt

def rp (m : ℕ) : (Fin m × Bool) ↪ Fin (2 * m) :=
  ⟨fun x => ⟨2 * x.1.val + (if x.2 = true then 1 else 0), by
    have := x.1.isLt
    split_ifs <;> omega⟩, by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    have h' : 2 * i.val + (if s = true then 1 else 0) = 2 * j.val + (if t = true then 1 else 0) :=
      congrArg Fin.val h
    have hi : i = j := Fin.ext (by split_ifs at h' <;> omega)
    subst hi
    have hst : s = t := by
      cases s <;> cases t <;> first | rfl | (exfalso; simp at h')
    rw [hst]⟩

theorem rp0 (m : ℕ) (i : Fin m) : (rp m (i, false)).val = 2 * i.val := by
  show 2 * i.val + (if (false : Bool) = true then 1 else 0) = 2 * i.val
  simp

theorem rp1 (m : ℕ) (i : Fin m) : (rp m (i, true)).val = 2 * i.val + 1 := by
  show 2 * i.val + (if (true : Bool) = true then 1 else 0) = 2 * i.val + 1
  simp

theorem rowdist (m : ℕ) (hm : 5 ≤ m) (i : Fin m) :
    (Finset.univ.filter
      (fun col : Fin (2 * m) => GG m (rp m (i, false)) col ≠ GG m (rp m (i, true)) col)).card ≤ 2 := by
  have hG0 : ∀ v : Fin (2 * m), GG m (rp m (i, false)) v = true ↔ P m (2 * i.val) v.val := by
    intro v
    have h := GG_iff m hm (rp m (i, false)) v
    rwa [rp0] at h
  have hG1 : ∀ v : Fin (2 * m), GG m (rp m (i, true)) v = true ↔ P m (2 * i.val + 1) v.val := by
    intro v
    have h := GG_iff m hm (rp m (i, true)) v
    rwa [rp1] at h
  calc _ ≤ (Finset.univ : Finset Bool).card := by
        apply Finset.card_le_card_of_injOn (fun v => GG m (rp m (i, false)) v)
        · intro v _
          exact Finset.mem_coe.2 (Finset.mem_univ _)
        · intro v hv v' hv' h
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv hv'
          apply Fin.ext
          apply f1 m i.val v.val v'.val hm i.isLt v.isLt v'.isLt
          · intro hiff
            exact hv (Bool.eq_iff_iff.2 ((hG0 v).trans (hiff.trans (hG1 v).symm)))
          · intro hiff
            exact hv' (Bool.eq_iff_iff.2 ((hG0 v').trans (hiff.trans (hG1 v').symm)))
          · rw [← hG0 v, ← hG0 v']
            dsimp only at h
            rw [h]
    _ = 2 := by simp

theorem col4 (m : ℕ) (hm : 5 ≤ m) (c : Fin (2 * m)) :
    4 ≤ (Finset.univ.filter (fun r : Fin (2 * m) => GG m r c = true)).card := by
  calc 4 = (Finset.univ : Finset (Fin 2 × Fin 2)).card := by simp
    _ ≤ _ := by
        apply Finset.card_le_card_of_injOn
          (fun x : Fin 2 × Fin 2 => (⟨rw4 m c.val x.1.val x.2.val,
            rw4_lt m c.val x.1.val x.2.val hm c.isLt x.2.isLt⟩ : Fin (2 * m)))
        · intro x _
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
          exact (GG_iff m hm _ c).2 (rw4_P m c.val x.1.val x.2.val hm c.isLt x.2.isLt)
        · intro x _ y _ h
          have h' := rw4_inj m c.val x.1.val x.2.val y.1.val y.2.val hm c.isLt x.1.isLt x.2.isLt
            y.1.isLt y.2.isLt (congrArg Fin.val h)
          exact Prod.ext (Fin.ext h'.1) (Fin.ext h'.2)

theorem common2 (m : ℕ) (hm : 5 ≤ m) (b c : Fin (2 * m)) (hbc : b ≠ c) :
    (Finset.univ.filter (fun r : Fin (2 * m) => GG m r b = true ∧ GG m r c = true)).card ≤ 2 := by
  calc _ ≤ (Finset.univ : Finset Bool).card := by
        apply Finset.card_le_card_of_injOn
          (fun r : Fin (2 * m) => if b.val % 2 = 1 ∧ c.val % 2 = 1 then decide (r.val / 2 = b.val / 2)
            else decide (r.val % 2 = 0))
        · intro v _
          exact Finset.mem_coe.2 (Finset.mem_univ _)
        · intro r hr r' hr' h
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hr hr'
          dsimp only at h
          apply Fin.ext
          apply f3 m r.val r'.val b.val c.val hm r.isLt r'.isLt b.isLt c.isLt
            (fun e => hbc (Fin.ext e))
            ((GG_iff m hm r b).1 hr.1) ((GG_iff m hm r c).1 hr.2)
            ((GG_iff m hm r' b).1 hr'.1) ((GG_iff m hm r' c).1 hr'.2)
          · intro hp
            rw [ite_eq_left hp, ite_eq_left hp] at h
            exact decide_eq_decide.1 h
          · intro hp
            rw [ite_eq_right hp, ite_eq_right hp] at h
            exact decide_eq_decide.1 h
    _ = 2 := by simp

theorem row4 (m : ℕ) (hm : 5 ≤ m) (u : Fin (2 * m)) :
    (Finset.univ.filter (fun v : Fin (2 * m) => GG m u v = true)).card ≤ 4 := by
  calc _ ≤ (Finset.univ : Finset (Bool × Bool)).card := by
        apply Finset.card_le_card_of_injOn
          (fun v : Fin (2 * m) => (decide (v.val % 2 = 0), decide (u.val / 2 = v.val / 2)))
        · intro v _
          exact Finset.mem_coe.2 (Finset.mem_univ _)
        · intro v hv v' hv' h
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv hv'
          dsimp only at h
          have h1 := decide_eq_decide.1 (congrArg Prod.fst h)
          have h2 := decide_eq_decide.1 (congrArg Prod.snd h)
          exact Fin.ext (f4 m u.val v.val v'.val hm v.isLt v'.isLt
            ((GG_iff m hm u v).1 hv) ((GG_iff m hm u v').1 hv') h1 h2)
    _ = 4 := by simp

theorem coldist (m : ℕ) (hm : 5 ≤ m) (b c : Fin (2 * m)) (hbc : b ≠ c) :
    2 + 2 ≤ (Finset.univ.filter (fun r : Fin (2 * m) => GG m r b ≠ GG m r c)).card := by
  have hb := col4 m hm b
  have hc := col4 m hm c
  have hbc2 := common2 m hm b c hbc
  have hcb2 := common2 m hm c b (Ne.symm hbc)
  have e1 : (Finset.univ.filter (fun r : Fin (2 * m) => GG m r b = true)).card ≤
      (Finset.univ.filter (fun r : Fin (2 * m) => GG m r b = true ∧ GG m r c = true)).card +
      (Finset.univ.filter (fun r : Fin (2 * m) => GG m r b = true ∧ ¬ GG m r c = true)).card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro r hr
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    by_cases h : GG m r c = true
    · exact Or.inl ⟨hr, h⟩
    · exact Or.inr ⟨hr, h⟩
  have e2 : (Finset.univ.filter (fun r : Fin (2 * m) => GG m r c = true)).card ≤
      (Finset.univ.filter (fun r : Fin (2 * m) => GG m r c = true ∧ GG m r b = true)).card +
      (Finset.univ.filter (fun r : Fin (2 * m) => GG m r c = true ∧ ¬ GG m r b = true)).card := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro r hr
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    by_cases h : GG m r b = true
    · exact Or.inl ⟨hr, h⟩
    · exact Or.inr ⟨hr, h⟩
  have hdisj : Disjoint
      (Finset.univ.filter (fun r : Fin (2 * m) => GG m r b = true ∧ ¬ GG m r c = true))
      (Finset.univ.filter (fun r : Fin (2 * m) => GG m r c = true ∧ ¬ GG m r b = true)) := by
    rw [Finset.disjoint_filter]
    intro r _ h1 h2
    exact h2.2 h1.1
  have hsub : (Finset.univ.filter (fun r : Fin (2 * m) => GG m r b = true ∧ ¬ GG m r c = true)) ∪
      (Finset.univ.filter (fun r : Fin (2 * m) => GG m r c = true ∧ ¬ GG m r b = true)) ⊆
      Finset.univ.filter (fun r : Fin (2 * m) => GG m r b ≠ GG m r c) := by
    intro r hr
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · intro h
      rw [h] at h1
      exact h2 h1
    · intro h
      rw [← h] at h1
      exact h2 h1
  have h := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at h
  omega

theorem main (m : ℕ) (hm : 5 ≤ m) (C : Circuit) (π : Equiv.Perm (Fin (2 * m)))
    (kept : Finset (Fin (2 * m)))
    (hkept : ∀ i ∈ kept,
      PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length) i.val = 1 ∧
      PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length)
        (2 * m + (π i).val) = 1 ∧
      ∃ g ∈ C.gates, g.op = GateOp.or ∧
        (g.inputs = [i.val, 2 * m + (π i).val] ∨ g.inputs = [2 * m + (π i).val, i.val]))
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 * m + 2 * m) C)
    (hrep : PEqualNP.Represents.Represents (GG m) C) :
    m ≤ 3 * (2 * m - kept.card) := by
  classical
  have hlen : ∀ a b : Fin (2 * m), (PEqualNP.Represents.oneEach a b).length = 2 * m + 2 * m := by
    intro a b
    simp [PEqualNP.Represents.oneEach]
  have hrb' := rb_idx C (2 * m + 2 * m) hrb
  have valT : ∀ (Z : List Bool) (_ : Z.length = 2 * m + 2 * m) (j : ℕ) (hj : j < C.gates.length)
      (_ : (C.gates[j]).op = GateOp.or) (w : ℕ) (_ : w ∈ (C.gates[j]).inputs)
      (_ : w < 2 * m + 2 * m) (_ : Z.getD w false = true),
      (W C.gates Z).getD (2 * m + 2 * m + j) false = true := by
    intro Z hZ j hj hor w hw hwN hZw
    have v := W_val C.gates Z j hj (by rw [hZ]; exact hrb' j hj)
    rw [hZ] at v
    rw [v, hor]
    exact or_true_of _ _ w hw (by rw [W_lt _ _ _ (by omega)]; exact hZw)
  have hsym : ∀ u ∈ kept, ∀ v ∈ kept, GG m u (π v) = GG m v (π u) := by
    intro u hu v hv
    by_cases huv : u = v
    · rw [huv]
    obtain ⟨ru, rcu, gu, hgu, hgor, hginp⟩ := hkept u hu
    obtain ⟨rv, rcv, gv, hgv, hgvor, hgvinp⟩ := hkept v hv
    obtain ⟨ju, hju, rfl⟩ := List.getElem_of_mem hgu
    obtain ⟨jv, hjv, rfl⟩ := List.getElem_of_mem hgv
    have hu2 := u.isLt
    have hv2 := v.isLt
    have hpu2 := (π u).isLt
    have hpv2 := (π v).isLt
    have hXl := hlen u (π v)
    have hYl := hlen v (π u)
    have hX : ∀ i, (PEqualNP.Represents.oneEach u (π v)).getD i false =
        (decide (i = u.val) || decide (i = 2 * m + (π v).val)) := oneEach_getD u (π v)
    have hY : ∀ i, (PEqualNP.Represents.oneEach v (π u)).getD i false =
        (decide (i = v.val) || decide (i = 2 * m + (π u).val)) := oneEach_getD v (π u)
    have hin : ∀ i, ¬ (i = u.val ∨ i = v.val ∨ i = 2 * m + (π u).val ∨ i = 2 * m + (π v).val) →
        (PEqualNP.Represents.oneEach u (π v)).getD i false =
          (PEqualNP.Represents.oneEach v (π u)).getD i false := by
      intro i hi
      simp only [not_or] at hi
      rw [hX, hY]
      simp [hi.1, hi.2.1, hi.2.2.1, hi.2.2.2]
    have mu1 : u.val ∈ (C.gates[ju]).inputs := by
      rcases hginp with h | h <;> rw [h] <;> simp
    have mu2 : 2 * m + (π u).val ∈ (C.gates[ju]).inputs := by
      rcases hginp with h | h <;> rw [h] <;> simp
    have mv1 : v.val ∈ (C.gates[jv]).inputs := by
      rcases hgvinp with h | h <;> rw [h] <;> simp
    have mv2 : 2 * m + (π v).val ∈ (C.gates[jv]).inputs := by
      rcases hgvinp with h | h <;> rw [h] <;> simp
    have hXu : (PEqualNP.Represents.oneEach u (π v)).getD u.val false = true := by rw [hX]; simp
    have hXv : (PEqualNP.Represents.oneEach u (π v)).getD (2 * m + (π v).val) false = true := by
      rw [hX]; simp
    have hYv : (PEqualNP.Represents.oneEach v (π u)).getD v.val false = true := by rw [hY]; simp
    have hYu : (PEqualNP.Represents.oneEach v (π u)).getD (2 * m + (π u).val) false = true := by
      rw [hY]; simp
    have gU : (W C.gates (PEqualNP.Represents.oneEach u (π v))).getD (2 * m + 2 * m + ju) false =
        (W C.gates (PEqualNP.Represents.oneEach v (π u))).getD (2 * m + 2 * m + ju) false := by
      rw [valT _ hXl ju hju hgor u.val mu1 (by omega) hXu,
        valT _ hYl ju hju hgor (2 * m + (π u).val) mu2 (by omega) hYu]
    have gV : (W C.gates (PEqualNP.Represents.oneEach u (π v))).getD (2 * m + 2 * m + jv) false =
        (W C.gates (PEqualNP.Represents.oneEach v (π u))).getD (2 * m + 2 * m + jv) false := by
      rw [valT _ hXl jv hjv hgvor (2 * m + (π v).val) mv2 (by omega) hXv,
        valT _ hYl jv hjv hgvor v.val mv1 (by omega) hYv]
    have hg : ∀ j (hj : j < C.gates.length),
        (∃ i ∈ (C.gates[j]).inputs,
          (i = u.val ∨ i = v.val ∨ i = 2 * m + (π u).val ∨ i = 2 * m + (π v).val)) →
        (W C.gates (PEqualNP.Represents.oneEach u (π v))).getD (2 * m + 2 * m + j) false =
          (W C.gates (PEqualNP.Represents.oneEach v (π u))).getD (2 * m + 2 * m + j) false := by
      intro j hj ⟨i, hi, hb⟩
      rcases hb with h | h | h | h
      · rw [h] at hi
        rw [uniq_idx C _ ru ju hju mu1 j hj hi]; exact gU
      · rw [h] at hi
        rw [uniq_idx C _ rv jv hjv mv1 j hj hi]; exact gV
      · rw [h] at hi
        rw [uniq_idx C _ rcu ju hju mu2 j hj hi]; exact gU
      · rw [h] at hi
        rw [uniq_idx C _ rcv jv hjv mv2 j hj hi]; exact gV
    have core := core2 (2 * m + 2 * m) _ _ hXl hYl
      (fun i => i = u.val ∨ i = v.val ∨ i = 2 * m + (π u).val ∨ i = 2 * m + (π v).val)
      hin C.gates hrb' hg
    have eX : GG m u (π v) =
        (W C.gates (PEqualNP.Represents.oneEach u (π v))).getD C.output false := by
      rw [← hrep u (π v)]; rfl
    have eY : GG m v (π u) =
        (W C.gates (PEqualNP.Represents.oneEach v (π u))).getD C.output false := by
      rw [← hrep v (π u)]; rfl
    have rowall : ∀ w : Fin (2 * m), C.output = w.val → False := by
      intro w h
      obtain ⟨c, hc, hnP⟩ := f5 m w.val hm w.isLt
      have hr := hrep w ⟨c, hc⟩
      have hw2 := w.isLt
      have ev : C.eval (PEqualNP.Represents.oneEach w (⟨c, hc⟩ : Fin (2 * m))) = true := by
        rw [eval_eq, h, W_lt _ _ _ (by rw [hlen]; omega), oneEach_getD]; simp
      rw [ev] at hr
      exact hnP ((GG_iff m hm w ⟨c, hc⟩).1 hr.symm)
    have colall : ∀ w : Fin (2 * m), C.output = 2 * m + w.val → False := by
      intro w h
      obtain ⟨r, hr0, hnP⟩ := f6 m w.val hm w.isLt
      have hr := hrep ⟨r, hr0⟩ w
      have hw2 := w.isLt
      have ev : C.eval (PEqualNP.Represents.oneEach (⟨r, hr0⟩ : Fin (2 * m)) w) = true := by
        rw [eval_eq, h, W_lt _ _ _ (by rw [hlen]; omega), oneEach_getD]; simp
      rw [ev] at hr
      exact hnP ((GG_iff m hm ⟨r, hr0⟩ w).1 hr.symm)
    by_cases hb : C.output = u.val ∨ C.output = v.val ∨ C.output = 2 * m + (π u).val ∨
        C.output = 2 * m + (π v).val
    · exfalso
      rcases hb with h | h | h | h
      · exact rowall u h
      · exact rowall v h
      · exact colall (π u) h
      · exact colall (π v) h
    · rw [eX, eY]
      exact core _ hb
  have hs := sq (2 * m) m 2 2 (GG m) (rp m) π kept (rowdist m hm) (coldist m hm) hsym
  have hsum : ∑ u ∈ Finset.univ \ kept,
      min (Finset.univ.filter (fun onCol : Fin (2 * m) => GG m u onCol = true)).card
        (Finset.univ.filter (fun offCol : Fin (2 * m) => GG m u offCol = false)).card ≤
      4 * (2 * m - kept.card) := by
    calc _ ≤ ∑ _u ∈ Finset.univ \ kept, 4 :=
          Finset.sum_le_sum (fun u _ => (min_le_left _ _).trans (row4 m hm u))
      _ = 4 * (2 * m - kept.card) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_sdiff_of_subset (Finset.subset_univ kept),
            Finset.card_univ, Fintype.card_fin, mul_comm]
  omega

end PEqualNP.Outside.L_meta_25503

theorem PEqualNP.Outside.L_meta_25503 : ∀ (m : ℕ), 5 ≤ m →
  let n := 2 * m
  let G := fun (u v : Fin n) =>
    let i := u.val / 2
    let j := v.val / 2
    let offset := if v.val % 2 = 0 then 1 else 2 + u.val % 2
    decide (i = j ∨ i = (j + offset) % m)
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (π : Equiv.Perm (Fin n)),
    let reads := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size)
    let paired := fun (i : Fin n) =>
      let x := i.val
      let y := n + (π i).val
      reads x = 1 ∧ reads y = 1 ∧
      ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        (g.inputs = [x, y] ∨ g.inputs = [y, x])
    let kept := @Finset.filter (Fin n) paired (fun _ => Classical.propDecidable _) Finset.univ
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + n) C →
    PEqualNP.Represents.Represents G C →
    m ≤ 3 * (n - kept.card) := by
  intro m hm
  dsimp only
  intro C π hrb hrep
  exact PEqualNP.Outside.L_meta_25503.main m hm C π _
    (fun i hi => ((@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _).mp hi).2) hrb hrep
