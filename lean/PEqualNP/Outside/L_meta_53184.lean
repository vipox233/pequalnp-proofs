import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53184

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


abbrev GA := PEqualNP.MetaComplexity.NestedCover.gateAt

theorem ga_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : GA C j = C.gates[j] := gateAt_eq C j hj

theorem fmin_le_init (l : List ℕ) (a : ℕ) : l.foldl min a ≤ a := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp only [List.foldl_cons]; exact le_trans (ih _) (min_le_left _ _)

theorem fmin_le (l : List ℕ) (a x : ℕ) (hx : x ∈ l) : l.foldl min a ≤ x := by
  induction l generalizing a with
  | nil => simp at hx
  | cons y l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hx with rfl | h
    · exact le_trans (fmin_le_init _ _) (min_le_right _ _)
    · exact ih _ h

theorem fmin_cases (l : List ℕ) (a : ℕ) : l.foldl min a = a ∨ l.foldl min a ∈ l := by
  induction l generalizing a with
  | nil => simp
  | cons y l ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rcases ih (min a y) with h | h
    · rw [h]; rcases min_choice a y with h' | h' <;> rw [h'] <;> simp
    · exact Or.inr (Or.inr h)

theorem cnt_sum (l : List Gate) (q : Gate → Bool) :
    ∑ j ∈ Finset.range l.length, (if q (l.getD j ⟨GateOp.or, []⟩) = true then 1 else 0) = (l.filter q).length := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [List.length_append, List.length_singleton, Finset.sum_range_succ, List.filter_append, List.length_append]
    rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
    have e : ∑ j ∈ Finset.range l.length, (if q ((l ++ [a]).getD j ⟨GateOp.or, []⟩) = true then 1 else 0)
        = ∑ j ∈ Finset.range l.length, (if q (l.getD j ⟨GateOp.or, []⟩) = true then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [List.getD_append _ _ _ _ (Finset.mem_range.1 hj)]
    rw [e, ih]
    cases h : q a <;> simp [h]

theorem sum_range_getD (L : List ℕ) (n : ℕ) (hn : L.length ≤ n) :
    ∑ i ∈ Finset.range n, L.getD i 0 = L.sum := by
  induction L generalizing n with
  | nil => simp
  | cons a L ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at hn; omega⟩
    rw [Finset.sum_range_succ', List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih m (by simp at hn; omega)]
    omega

def Clo (C : Circuit) (N : ℕ) (R : Set ℕ) : Prop :=
  C.output ∈ R ∧ ∀ j, j < C.gates.length → N + j ∈ R → (GA C j).op ≠ GateOp.not →
    ∀ i ∈ (GA C j).inputs, i ∈ R

def Rch (C : Circuit) (N w : ℕ) : Prop := ∀ R, Clo C N R → w ∈ R

theorem rch_out (C : Circuit) (N : ℕ) : Rch C N C.output := fun _ h => h.1

theorem rch_step (C : Circuit) (N j i : ℕ) (hj : j < C.gates.length) (h : Rch C N (N + j))
    (hop : (GA C j).op ≠ GateOp.not) (hi : i ∈ (GA C j).inputs) : Rch C N i :=
  fun R hR => hR.2 j hj (h R hR) hop i hi

theorem rch_inv (C : Circuit) (N w : ℕ) (h : Rch C N w) : w = C.output ∨
    ∃ j, j < C.gates.length ∧ Rch C N (N + j) ∧ (GA C j).op ≠ GateOp.not ∧ w ∈ (GA C j).inputs := by
  have key : Clo C N {w | w = C.output ∨ ∃ j, j < C.gates.length ∧ Rch C N (N + j) ∧
      (GA C j).op ≠ GateOp.not ∧ w ∈ (GA C j).inputs} := by
    refine ⟨Or.inl rfl, ?_⟩
    intro j hj hm hop i hi
    refine Or.inr ⟨j, hj, ?_, hop, hi⟩
    rcases hm with h1 | ⟨j', hj', h', hop', hi'⟩
    · rw [h1]; exact rch_out C N
    · exact rch_step C N j' _ hj' h' hop' hi'
  exact h _ key

theorem rch_lt (C : Circuit) (N : ℕ) (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack N C)
    (hout : C.output < N + C.gates.length) (w : ℕ) (h : Rch C N w) : w < N + C.gates.length := by
  have : Clo C N {w | w < N + C.gates.length} := by
    refine ⟨hout, ?_⟩
    intro j hj _ _ i hi
    have := hrb j hj i hi
    show i < _
    omega
  exact h _ this

open Classical in
theorem cone_count (C : Circuit) (N : ℕ) (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack N C)
    (hout : C.output < N + C.gates.length) :
    ((Finset.range C.gates.length).filter (fun j => Rch C N (N + j) ∧ (GA C j).op = GateOp.not)).card ≤
      ((Finset.range C.gates.length).filter
        (fun j => Rch C N (N + j) ∧ ¬ (GA C j).op = GateOp.not)).card + 1 := by
  set L := C.gates.length
  set Rs := (Finset.range (N + L)).filter (Rch C N)
  set Bn := (Finset.range L).filter (fun j => Rch C N (N + j) ∧ (GA C j).op = GateOp.not)
  set Cn := (Finset.range L).filter (fun j => Rch C N (N + j) ∧ ¬ (GA C j).op = GateOp.not)
  have h1 : Rs.erase C.output ⊆ Cn.biUnion (fun j => (GA C j).inputs.toFinset) := by
    intro w hw
    rcases Finset.mem_erase.1 hw with ⟨hne, hw⟩
    rcases rch_inv C N w (Finset.mem_filter.1 hw).2 with h | ⟨j, hj, hr, hop, hi⟩
    · exact absurd h hne
    · exact Finset.mem_biUnion.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hr, hop⟩,
        List.mem_toFinset.2 hi⟩
  have h2 : (Cn.biUnion (fun j => (GA C j).inputs.toFinset)).card ≤ 2 * Cn.card := by
    refine le_trans Finset.card_biUnion_le ?_
    calc ∑ j ∈ Cn, ((GA C j).inputs.toFinset).card ≤ Cn.card • 2 := by
          apply Finset.sum_le_card_nsmul
          intro j hj
          have hj' : j < L := Finset.mem_range.1 (Finset.mem_filter.1 hj).1
          refine le_trans (List.toFinset_card_le _) ?_
          rw [ga_eq C j hj']
          exact (hfan _ (List.getElem_mem hj')).2
      _ = 2 * Cn.card := by rw [smul_eq_mul, mul_comm]
  have h3 : Bn.card + Cn.card ≤ Rs.card := by
    have e : Bn.card + Cn.card = ((Finset.range L).filter (fun j => Rch C N (N + j))).card := by
      rw [← Finset.card_filter_add_card_filter_not
        (s := (Finset.range L).filter (fun j => Rch C N (N + j))) (fun j => (GA C j).op = GateOp.not)]
      rw [Finset.filter_filter, Finset.filter_filter]
    rw [e]
    apply Finset.card_le_card_of_injOn (fun j => N + j)
    · intro j hj
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hj
      simp only [Rs, Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
      exact ⟨by omega, hj.2⟩
    · intro a _ b _ h
      simp only at h
      omega
  have h4 := Finset.pred_card_le_card_erase (s := Rs) (a := C.output)
  have h5 := Finset.card_le_card h1
  omega

theorem fall (C : Circuit) (N : ℕ) (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack N C)
    (hout : C.output < N + C.gates.length) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hrise : ∀ l, x.getD l false = true → y.getD l false = true)
    (h0 : (W C.gates x).getD C.output false = true) (h1 : (W C.gates y).getD C.output false = false) :
    ∃ j, j < C.gates.length ∧ Rch C N (N + j) ∧ (GA C j).op = GateOp.not ∧
      (W C.gates x).getD (N + j) false = true ∧ (W C.gates y).getD (N + j) false = false := by
  by_contra hno
  have hrb' := rb_idx C N hrb
  have key : ∀ w, Rch C N w → (W C.gates x).getD w false = true → (W C.gates y).getD w false = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hr hv
      by_cases hwN : w < N
      · rw [W_lt _ _ _ (by omega)] at hv
        rw [W_lt _ _ _ (by omega)]
        exact hrise w hv
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
        have hj : j < C.gates.length := by have := rch_lt C N hrb hout _ hr; omega
        by_cases hop : (GA C j).op = GateOp.not
        · by_contra hc
          apply hno
          exact ⟨j, hj, hr, hop, hv, by simpa using hc⟩
        · have vX := W_val C.gates x j hj (by rw [hx]; exact hrb' j hj)
          have vY := W_val C.gates y j hj (by rw [hy]; exact hrb' j hj)
          rw [hx] at vX
          rw [hy] at vY
          rw [vX] at hv
          rw [vY]
          have hmem := (hfan _ (List.getElem_mem hj)).1
          rw [ga_eq C j hj] at hop
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
          have hao : (C.gates[j]).op = GateOp.and ∨ (C.gates[j]).op = GateOp.or := by
            rcases hmem with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exact absurd h hop
          refine eval_mono _ hao _ _ ?_ hv
          intro i hi hvi
          have hi' : i ∈ (GA C j).inputs := by rw [ga_eq C j hj]; exact hi
          rw [← ga_eq C j hj] at hop
          exact ih i (hrb' j hj i hi) (rch_step C N j i hj hr hop hi') hvi
  have := key _ (rch_out C N) h0
  rw [h1] at this
  exact absurd this (by decide)


open Classical in
theorem fwd_main (r d : ℕ) (S : Fin d → Finset (Fin r)) (cost : Fin d → ℕ) (W0 p b g : ℕ)
    (col : Fin d → Option (Fin r) → Bool) (hc0 : ∀ j, col j none = false)
    (hc1 : ∀ j e, col j (some e) = true ↔ e ∈ S j)
    (X : Option (Fin r) → List Bool) (hXl : ∀ z, (X z).length = d + 2)
    (hrise : ∀ e l, (X none).getD l false = true → (X (some e)).getD l false = true)
    (C : Circuit) (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (d + 2) C) (hout : C.output < d + 2 + C.size)
    (hval : ∀ z, (C.wires (X z)).getD C.output false = z.isNone)
    (hp : C.size - PEqualNP.NotBracket.notCount C ≤ p) (hb : PEqualNP.NotBracket.notCount C ≤ b)
    (hg : C.size ≤ g) (tl : ℕ → ℕ)
    (hlab : ∀ i, i < C.size → (GA C i).op = GateOp.not → ∃ j : Fin d,
      ((∀ z, (C.wires (X z)).getD (d + 2 + i) false = col j z) ∨
        (∀ z, (C.wires (X z)).getD (d + 2 + i) false = !(col j z))) ∧ cost j ≤ tl i)
    (hsum : ∀ B : Finset ℕ, (∀ i ∈ B, i < C.size ∧ (GA C i).op = GateOp.not) → ∑ i ∈ B, tl i ≤ W0) :
    ∃ J : Finset (Fin d), (∀ e : Fin r, ∃ j ∈ J, e ∈ S j) ∧
      J.card - 1 ≤ p ∧ J.card ≤ b ∧ J.card + (J.card - 1) ≤ g ∧ J.sum cost ≤ W0 := by
  have hsz : C.size = C.gates.length := rfl
  rw [hsz] at hout hp hg
  set L := C.gates.length
  set Bn := (Finset.range L).filter (fun j => Rch C (d + 2) (d + 2 + j) ∧ (GA C j).op = GateOp.not)
  set Cn := (Finset.range L).filter (fun j => Rch C (d + 2) (d + 2 + j) ∧ ¬ (GA C j).op = GateOp.not)
  have hcone : Bn.card ≤ Cn.card + 1 := cone_count C (d + 2) hfan hrb hout
  have hB : ∀ i ∈ Bn, ∃ j : Fin d,
      ((∀ z, (C.wires (X z)).getD (d + 2 + i) false = col j z) ∨
        (∀ z, (C.wires (X z)).getD (d + 2 + i) false = !(col j z))) ∧ cost j ≤ tl i := by
    intro i hi
    have hi' := Finset.mem_filter.1 hi
    exact hlab i (Finset.mem_range.1 hi'.1) hi'.2.2
  choose lab hlab' using hB
  refine ⟨Bn.attach.image (fun i => lab i.1 i.2), ?_, ?_⟩
  · intro e
    obtain ⟨i, hi, hr, hop, hv0, hv1⟩ := fall C (d + 2) hfan hrb hout (X none) (X (some e))
      (hXl _) (hXl _) (hrise e) (by rw [← wires_eq, hval]; rfl) (by rw [← wires_eq, hval]; rfl)
    have hiB : i ∈ Bn := Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hr, hop⟩
    refine ⟨lab i hiB, Finset.mem_image.2 ⟨⟨i, hiB⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
    rcases (hlab' i hiB).1 with h | h
    · have := h none
      rw [hc0, wires_eq, hv0] at this
      exact absurd this (by decide)
    · have := h (some e)
      rw [wires_eq, hv1] at this
      rw [← hc1]
      cases hcc : col (lab i hiB) (some e)
      · rw [hcc] at this; exact absurd this (by decide)
      · rfl
  · have hJ : (Bn.attach.image (fun i => lab i.1 i.2)).card ≤ Bn.card :=
      le_trans Finset.card_image_le (by rw [Finset.card_attach])
    have hnot : ((Finset.range L).filter (fun j => (GA C j).op = GateOp.not)).card =
        PEqualNP.NotBracket.notCount C := by
      rw [Finset.card_filter]
      unfold PEqualNP.NotBracket.notCount
      rw [← cnt_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp [GA, PEqualNP.MetaComplexity.NestedCover.gateAt]
    have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.range L)
      (fun j => (GA C j).op = GateOp.not)
    rw [Finset.card_range] at hsplit
    have hBs : Bn.card ≤ ((Finset.range L).filter (fun j => (GA C j).op = GateOp.not)).card := by
      apply Finset.card_le_card
      intro j hj
      have := Finset.mem_filter.1 hj
      exact Finset.mem_filter.2 ⟨this.1, this.2.2⟩
    have hCs : Cn.card ≤ ((Finset.range L).filter (fun j => ¬ (GA C j).op = GateOp.not)).card := by
      apply Finset.card_le_card
      intro j hj
      have := Finset.mem_filter.1 hj
      exact Finset.mem_filter.2 ⟨this.1, this.2.2⟩
    refine ⟨by omega, by omega, by omega, ?_⟩
    calc (Bn.attach.image (fun i => lab i.1 i.2)).sum cost
        ≤ ∑ i ∈ Bn.attach, cost (lab i.1 i.2) :=
          Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
      _ ≤ ∑ i ∈ Bn.attach, tl i.1 := Finset.sum_le_sum (fun i _ => (hlab' i.1 i.2).2)
      _ = ∑ i ∈ Bn, tl i := Finset.sum_attach Bn tl
      _ ≤ W0 := by
          apply hsum
          intro i hi
          have := Finset.mem_filter.1 hi
          exact ⟨Finset.mem_range.1 this.1, this.2.2⟩


def notG (j : ℕ) : Gate := ⟨GateOp.not, [j]⟩

def accW (N k t : ℕ) : ℕ := if t = 0 then N else N + k + t - 1

def andG (N k : ℕ) (t : Fin (k - 1)) : Gate := ⟨GateOp.and, [accW N k t.val, N + t.val + 1]⟩

def mkC (N : ℕ) (js : List ℕ) : Circuit :=
  ⟨js.map notG ++ List.ofFn (andG N js.length), accW N js.length (js.length - 1)⟩

theorem mk_len (N : ℕ) (js : List ℕ) : (mkC N js).gates.length = js.length + (js.length - 1) := by
  simp [mkC]

theorem mk_ga_lt (N : ℕ) (js : List ℕ) (i : ℕ) (hi : i < js.length) :
    GA (mkC N js) i = notG (js.getD i 0) := by
  simp only [GA, PEqualNP.MetaComplexity.NestedCover.gateAt, mkC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simpa using hi)]
  simp [hi]

theorem mk_ga_ge (N : ℕ) (js : List ℕ) (t : ℕ) (ht : t < js.length - 1) :
    GA (mkC N js) (js.length + t) = ⟨GateOp.and, [accW N js.length t, N + t + 1]⟩ := by
  simp [GA, PEqualNP.MetaComplexity.NestedCover.gateAt, mkC, List.getD_eq_getElem?_getD,
    List.getElem?_append_right, ht, andG]

theorem mk_fan (N : ℕ) (js : List ℕ) : PEqualNP.MetaComplexity.FanInTwo (mkC N js) := by
  intro g hg
  simp only [mkC, List.mem_append, List.mem_map, List.mem_ofFn'] at hg
  rcases hg with ⟨j, _, rfl⟩ | ⟨t, rfl⟩
  · simp [notG]
  · simp [andG]

theorem mk_ga_cases (N : ℕ) (js : List ℕ) (i : ℕ) (hi : i < (mkC N js).gates.length) :
    (i < js.length ∧ GA (mkC N js) i = notG (js.getD i 0)) ∨
    (∃ t, t < js.length - 1 ∧ i = js.length + t ∧
      GA (mkC N js) i = ⟨GateOp.and, [accW N js.length t, N + t + 1]⟩) := by
  rw [mk_len] at hi
  by_cases h : i < js.length
  · exact Or.inl ⟨h, mk_ga_lt N js i h⟩
  · obtain ⟨t, rfl⟩ : ∃ t, i = js.length + t := ⟨i - js.length, by omega⟩
    exact Or.inr ⟨t, by omega, rfl, mk_ga_ge N js t (by omega)⟩

theorem mk_rb (N : ℕ) (js : List ℕ) (hjs : ∀ j ∈ js, j < N) (hk : 1 ≤ js.length) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N (mkC N js) := by
  intro i hi w hw
  rcases mk_ga_cases N js i hi with ⟨h, e⟩ | ⟨t, ht, rfl, e⟩
  · rw [show PEqualNP.MetaComplexity.NestedCover.gateAt (mkC N js) i = GA (mkC N js) i from rfl, e] at hw
    simp only [notG, List.mem_singleton] at hw
    subst hw
    have : js.getD i 0 ∈ js := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; simp
    have := hjs _ this
    omega
  · rw [show PEqualNP.MetaComplexity.NestedCover.gateAt (mkC N js) _ = GA (mkC N js) _ from rfl, e] at hw
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
    unfold accW at hw
    rcases hw with rfl | rfl
    · split_ifs <;> omega
    · omega

theorem mk_out (N : ℕ) (js : List ℕ) (hk : 1 ≤ js.length) : (mkC N js).output < N + (mkC N js).size := by
  show accW N js.length (js.length - 1) < N + (mkC N js).gates.length
  rw [mk_len]
  unfold accW
  split_ifs <;> omega

theorem mk_notCount (N : ℕ) (js : List ℕ) : PEqualNP.NotBracket.notCount (mkC N js) = js.length := by
  unfold PEqualNP.NotBracket.notCount
  simp only [mkC, List.filter_append]
  rw [List.filter_eq_self.2, List.filter_eq_nil_iff.2]
  · simp
  · intro g hg
    simp only [List.mem_ofFn'] at hg
    obtain ⟨t, rfl⟩ := hg
    simp [andG]
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨j, _, rfl⟩ := hg
    simp [notG]

theorem mk_val1 (N : ℕ) (js : List ℕ) (hjs : ∀ j ∈ js, j < N) (hk : 1 ≤ js.length) (x : List Bool)
    (hx : x.length = N) (i : ℕ) (hi : i < js.length) :
    (W (mkC N js).gates x).getD (N + i) false = !(x.getD (js.getD i 0) false) := by
  have hl : i < (mkC N js).gates.length := by rw [mk_len]; omega
  have hrb' := rb_idx _ N (mk_rb N js hjs hk)
  have v := W_val _ x i hl (by rw [hx]; exact hrb' i hl)
  rw [hx] at v
  rw [v, ← ga_eq _ i hl, mk_ga_lt N js i hi]
  have hm : js.getD i 0 ∈ js := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; simp
  simp only [notG, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
  rw [W_lt _ _ _ (by rw [hx]; exact hjs _ hm)]

theorem mk_val2 (N : ℕ) (js : List ℕ) (hjs : ∀ j ∈ js, j < N) (hk : 1 ≤ js.length) (x : List Bool)
    (hx : x.length = N) (t : ℕ) (ht : t < js.length) :
    (W (mkC N js).gates x).getD (accW N js.length t) false = true ↔
      ∀ s, s ≤ t → x.getD (js.getD s 0) false = false := by
  induction t with
  | zero =>
    have := mk_val1 N js hjs hk x hx 0 (by omega)
    have e0 : accW N js.length 0 = N + 0 := by simp [accW]
    rw [e0, this]
    constructor
    · intro h s hs
      obtain rfl : s = 0 := by omega
      simpa using h
    · intro h
      simpa using h 0 (le_refl _)
  | succ t ih =>
    have ih' := ih (by omega)
    have hl : js.length + t < (mkC N js).gates.length := by rw [mk_len]; omega
    have hrb' := rb_idx _ N (mk_rb N js hjs hk)
    have v := W_val _ x (js.length + t) hl (by rw [hx]; exact hrb' _ hl)
    rw [hx] at v
    have ea : accW N js.length (t + 1) = N + (js.length + t) := by
      unfold accW; simp; omega
    rw [ea, v, ← ga_eq _ _ hl, mk_ga_ge N js t (by omega)]
    have v1 := mk_val1 N js hjs hk x hx (t + 1) ht
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true,
      Bool.and_eq_true]
    rw [ih', show N + t + 1 = N + (t + 1) by omega, v1]
    constructor
    · rintro ⟨h1, h2⟩ s hs
      rcases Nat.lt_or_ge s (t + 1) with h | h
      · exact h1 s (by omega)
      · obtain rfl : s = t + 1 := by omega
        simpa using h2
    · intro h
      exact ⟨fun s hs => h s (by omega), by simpa using h (t + 1) (le_refl _)⟩


theorem toll_ex (n W : ℕ) (P : Fin n → Prop) {dp : DecidablePred P} (c : Fin n → ℕ)
    (h : (List.ofFn (fun j => if P j then c j else W + 1)).foldl min (W + 1) ≤ W) :
    ∃ j, P j ∧ c j ≤ (List.ofFn (fun j => if P j then c j else W + 1)).foldl min (W + 1) := by
  rcases fmin_cases (List.ofFn (fun j => if P j then c j else W + 1)) (W + 1) with e | e
  · omega
  · rw [List.mem_ofFn'] at e
    obtain ⟨j, hj⟩ := e
    by_cases hp : P j
    · refine ⟨j, hp, ?_⟩
      simp only [hp, if_true] at hj
      omega
    · simp only [hp, if_false] at hj
      omega

theorem toll_le (n W : ℕ) (P : Fin n → Prop) {dp : DecidablePred P} (c : Fin n → ℕ) (j : Fin n)
    (hj : P j) : (List.ofFn (fun j => if P j then c j else W + 1)).foldl min (W + 1) ≤ c j := by
  apply fmin_le
  rw [List.mem_ofFn']
  exact ⟨j, by simp [hj]⟩

theorem inp_lt {d : ℕ} (f : Fin d → Bool) (l : ℕ) (h : l < d) :
    (List.ofFn f ++ [false, true]).getD l false = f ⟨l, h⟩ := by
  rw [List.getD_append _ _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

theorem inp_ge {d : ℕ} (f : Fin d → Bool) (l : ℕ) (h : d ≤ l) :
    (List.ofFn f ++ [false, true]).getD l false = decide (l = d + 1) := by
  rw [List.getD_append_right _ _ _ _ (by simpa using h)]
  simp only [List.length_ofFn]
  obtain ⟨t, rfl⟩ : ∃ t, l = d + t := ⟨l - d, by omega⟩
  rcases t with _ | _ | t
  · simp
  · simp
  · simp [List.getD_eq_getElem?_getD]


theorem get_ga (C : Circuit) (i : Fin C.size) : (C.gates.get i) = GA C i.val := by
  have hi : i.val < C.gates.length := i.isLt
  show C.gates.get i = C.gates.getD i.val ⟨GateOp.or, []⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

end PEqualNP.Outside.L_meta_53184

open PEqualNP.Outside.L_meta_53184 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_53184 : ∀ (r d p b g W : Nat) (S : Fin d → Finset (Fin r)) (cost : Fin d → Nat),
  letI : ∀ q : Prop, Decidable q := Classical.propDecidable
  let F := Option (Fin r) → Bool
  let col := fun (j : Fin d) (z : Option (Fin r)) => z.elim false (fun e => decide (e ∈ S j))
  let inv := fun (f : F) (z : Option (Fin r)) => !(f z)
  let toll := fun (f : F) => (List.ofFn (fun j =>
    if f = col j ∨ f = inv (col j) then cost j else W+1)).foldl min (W+1)
  let inputs := fun z => List.ofFn (fun j => col j z) ++ [false,true]
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    let wire := fun (n : Nat) (z : Option (Fin r)) => (C.wires (inputs z)).getD n false
    let neg := PEqualNP.NotBracket.notCount C
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (d+2) C ∧
    C.output < d+2+C.size ∧ (∀ z, wire C.output z = z.isNone) ∧
    C.size-neg ≤ p ∧ neg ≤ b ∧ C.size ≤ g ∧
    (Finset.univ : Finset (Fin C.size)).sum (fun i =>
      if (C.gates.get i).op = .not then toll (wire (d+2+i.val)) else 0) ≤ W) ↔
  ∃ J : Finset (Fin d), (∀ e : Fin r, ∃ j ∈ J, e ∈ S j) ∧
    J.card-1 ≤ p ∧ J.card ≤ b ∧ J.card+(J.card-1) ≤ g ∧ J.sum cost ≤ W := by
  intro r d p b g W S cost F col inv toll inputs
  classical
  have hc0 : ∀ j, col j none = false := fun j => rfl
  have hc1 : ∀ j e, col j (some e) = true ↔ e ∈ S j := by intro j e; simp [col]
  have hXl : ∀ z, (inputs z).length = d + 2 := by intro z; simp [inputs]
  have hXlt : ∀ z l (h : l < d), (inputs z).getD l false = col ⟨l, h⟩ z := fun z l h => inp_lt _ l h
  have hXge : ∀ z l, d ≤ l → (inputs z).getD l false = decide (l = d + 1) := fun z l h => inp_ge _ l h
  have hrise : ∀ e l, (inputs none).getD l false = true → (inputs (some e)).getD l false = true := by
    intro e l h
    rcases Nat.lt_or_ge l d with hl | hl
    · rw [hXlt _ _ hl, hc0] at h
      exact absurd h (by decide)
    · rw [hXge _ _ hl] at h ⊢
      exact h
  have htoll_le : ∀ j, toll (inv (col j)) ≤ cost j := fun j =>
    toll_le d W _ cost j (Or.inr rfl)
  have htoll_ex : ∀ f, toll f ≤ W → ∃ j, (f = col j ∨ f = inv (col j)) ∧ cost j ≤ toll f := fun f hf =>
    toll_ex d W _ cost hf
  constructor
  · rintro ⟨C, hC⟩
    dsimp only at hC
    obtain ⟨hfan, hrb, hout, hval, hp, hb, hg, hsum⟩ := hC
    apply fwd_main r d S cost W p b g col hc0 hc1 inputs hXl hrise C hfan hrb hout hval hp hb hg
      (fun i => toll (fun z => (C.wires (inputs z)).getD (d + 2 + i) false))
    · intro i hi hop
      have hop' : (C.gates.get ⟨i, hi⟩).op = GateOp.not := by
        exact (congrArg Gate.op (get_ga C ⟨i, hi⟩)).trans hop
      have h1 := Finset.single_le_sum (f := fun i : Fin C.size =>
        if (C.gates.get i).op = GateOp.not then
          toll (fun z => (C.wires (inputs z)).getD (d + 2 + i.val) false) else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨i, hi⟩)
      have h2 : toll (fun z => (C.wires (inputs z)).getD (d + 2 + i) false) ≤ W := by
        split_ifs at h1 with hh
        · exact le_trans h1 hsum
        · exact absurd hop' hh
      obtain ⟨j, hj, hcj⟩ := htoll_ex _ h2
      refine ⟨j, ?_, hcj⟩
      rcases hj with h | h
      · exact Or.inl (fun z => congrFun h z)
      · exact Or.inr (fun z => congrFun h z)
    · intro B hB
      have hBsub : B ⊆ (Finset.range C.size).filter (fun i => (GA C i).op = GateOp.not) := fun i hi =>
        Finset.mem_filter.2 ⟨Finset.mem_range.2 (hB i hi).1, (hB i hi).2⟩
      calc ∑ i ∈ B, toll (fun z => (C.wires (inputs z)).getD (d + 2 + i) false)
          ≤ ∑ i ∈ (Finset.range C.size).filter (fun i => (GA C i).op = GateOp.not),
              toll (fun z => (C.wires (inputs z)).getD (d + 2 + i) false) :=
            Finset.sum_le_sum_of_subset hBsub
        _ = ∑ i ∈ Finset.range C.size, (if (GA C i).op = GateOp.not then
              toll (fun z => (C.wires (inputs z)).getD (d + 2 + i) false) else 0) := Finset.sum_filter _ _
        _ = ∑ i : Fin C.size, (if (GA C i).op = GateOp.not then
              toll (fun z => (C.wires (inputs z)).getD (d + 2 + i.val) false) else 0) := Finset.sum_range _
        _ = ∑ i : Fin C.size, (if (C.gates.get i).op = GateOp.not then
              toll (fun z => (C.wires (inputs z)).getD (d + 2 + i.val) false) else 0) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [get_ga]
        _ ≤ W := hsum
  · rintro ⟨J, hcov, hp, hb, hg, hc⟩
    by_cases hJ : J.card = 0
    · rw [Finset.card_eq_zero] at hJ
      subst hJ
      refine ⟨⟨[], d + 1⟩, ?_⟩
      have hr : ∀ e : Fin r, False := fun e => by
        obtain ⟨j, hj, _⟩ := hcov e
        simp at hj
      dsimp only
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro g hg
        simp at hg
      · intro j hj
        simp at hj
      · show d + 1 < d + 2 + 0
        omega
      · intro z
        cases z with
        | none =>
          show (inputs none).getD (d + 1) false = true
          rw [hXge _ _ (by omega)]
          simp
        | some e => exact (hr e).elim
      · simp [Circuit.size]
      · simp [PEqualNP.NotBracket.notCount]
      · simp [Circuit.size]
      · refine le_trans (le_of_eq (Finset.sum_eq_zero ?_)) (Nat.zero_le W)
        intro i _
        exact absurd i.isLt (Nat.not_lt_zero _)
    · set js := J.toList.map Fin.val with hjsdef
      have hk : js.length = J.card := by simp [js]
      have hk1 : 1 ≤ js.length := by omega
      have hjs : ∀ j ∈ js, j < d + 2 := by
        intro j hj
        simp only [js, List.mem_map] at hj
        obtain ⟨a, _, rfl⟩ := hj
        omega
      have hlen : J.toList.length = js.length := by simp [js]
      have hjsget : ∀ s (hs : s < js.length), js.getD s 0 = (J.toList[s]'(by omega)).val := by
        intro s hs
        simp [js, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by omega : s < J.toList.length)]
      have hv1 : ∀ z i (hi : i < js.length), ((mkC (d + 2) js).wires (inputs z)).getD (d + 2 + i) false =
          !(col (J.toList[i]'(by omega)) z) := by
        intro z i hi
        rw [wires_eq, mk_val1 (d + 2) js hjs hk1 (inputs z) (hXl z) i hi, hjsget i hi,
          hXlt z _ (J.toList[i]'(by omega)).isLt]
      have hv2 : ∀ z, ((mkC (d + 2) js).wires (inputs z)).getD (mkC (d + 2) js).output false = true ↔
          ∀ s (hs : s < js.length), col (J.toList[s]'(by omega)) z = false := by
        intro z
        rw [wires_eq]
        show (PEqualNP.Outside.L_meta_53184.W _ _).getD (accW (d + 2) js.length (js.length - 1)) false = true ↔ _
        rw [mk_val2 (d + 2) js hjs hk1 (inputs z) (hXl z) _ (by omega)]
        constructor
        · intro h s hs
          have := h s (by omega)
          rwa [hjsget s hs, hXlt z _ (Fin.isLt _)] at this
        · intro h s hs
          rw [hjsget s (by omega), hXlt z _ (Fin.isLt _)]
          exact h s (by omega)
      have hsize : (mkC (d + 2) js).size = js.length + (js.length - 1) := mk_len _ _
      refine ⟨mkC (d + 2) js, ?_⟩
      dsimp only
      refine ⟨mk_fan _ _, mk_rb _ _ hjs hk1, mk_out _ _ hk1, ?_, ?_, ?_, ?_, ?_⟩
      · intro z
        cases z with
        | none =>
          rw [(hv2 none).2 (fun s hs => hc0 _)]
          rfl
        | some e =>
          obtain ⟨j, hj, hej⟩ := hcov e
          have hjl : j ∈ J.toList := Finset.mem_toList.2 hj
          obtain ⟨s, hs, rfl⟩ := List.mem_iff_getElem.1 hjl
          cases hh : ((mkC (d + 2) js).wires (inputs (some e))).getD (mkC (d + 2) js).output false
          · rfl
          · have := (hv2 (some e)).1 hh s (by omega)
            rw [(hc1 _ _).2 hej] at this
            exact absurd this (by decide)
      · rw [mk_notCount, hsize]; omega
      · rw [mk_notCount]; omega
      · rw [hsize]; omega
      · calc ∑ i : Fin (mkC (d + 2) js).size, (if ((mkC (d + 2) js).gates.get i).op = GateOp.not then
              toll (fun z => ((mkC (d + 2) js).wires (inputs z)).getD (d + 2 + i.val) false) else 0)
            ≤ ∑ i : Fin (mkC (d + 2) js).size, (J.toList.map cost).getD i 0 := by
              apply Finset.sum_le_sum
              intro i _
              split_ifs with hop
              · have hi : i.val < js.length := by
                  rcases mk_ga_cases (d + 2) js i i.isLt with ⟨h, _⟩ | ⟨t, ht, he, e⟩
                  · exact h
                  · exfalso
                    rw [get_ga, e] at hop
                    simp at hop
                have hw : (fun z => ((mkC (d + 2) js).wires (inputs z)).getD (d + 2 + i.val) false) =
                    inv (col (J.toList[i.val]'(by omega))) := funext (fun z => hv1 z i hi)
                rw [hw]
                refine le_trans (htoll_le _) (le_of_eq ?_)
                simp [List.getD_eq_getElem?_getD, List.getElem?_map,
                  List.getElem?_eq_getElem (by omega : i.val < J.toList.length)]
              · exact Nat.zero_le _
          _ = ∑ i ∈ Finset.range (mkC (d + 2) js).size, (J.toList.map cost).getD i 0 :=
              (Finset.sum_range (fun i => (J.toList.map cost).getD i 0)).symm
          _ = (J.toList.map cost).sum := sum_range_getD _ _ (by simp [hsize]; omega)
          _ = J.sum cost := Finset.sum_map_toList J cost
          _ ≤ W := hc
