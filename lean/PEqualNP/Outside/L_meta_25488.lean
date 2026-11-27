import PEqualNP.Defs

-- L-meta-25488: put x3 = oneEach u c plus row v; Monotone2 gives eval x3 >= eval (oneEach u c) = true.
-- Against x2 = oneEach v c, x3 differs only at u, read once (by I). If I were on at x2, or if T were I's only
-- reader (T on at both, J being on with v), every other wire agrees (strong induction), so eval x3 = eval x2 = false.
-- Wire machinery and oneEach lemmas copied from L_meta_25479 (itself from L_meta_23962).

namespace PEqualNP.Outside.L_meta_25488_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- copied via L_meta_25479_aux from PEqualNP.Outside.L_meta_23962_aux (lean/PEqualNP/Outside/L_meta_23962.lean)
theorem foldl_snoc_keeps {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    init <+: gs.foldl (fun R g => R ++ [F R g]) init := by
  induction gs generalizing init with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append init [F init g]).trans (ih _)

theorem foldl_snoc_length {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).length = init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih => simp [ih]; omega

theorem getD_of_initial {α : Type _} {P L : List α} (h : P <+: L) {i : ℕ} (hi : i < P.length)
    (d : α) : L.getD i d = P.getD i d := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_snoc_split {α β : Type _} (F : List α → β → α) (gs : List β) (init : List α)
    (j : ℕ) (hj : j < gs.length) (d : α) :
    (gs.foldl (fun R g => R ++ [F R g]) init).getD (init.length + j) d
      = F ((gs.take j).foldl (fun R g => R ++ [F R g]) init) gs[j] ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init) <+:
      gs.foldl (fun R g => R ++ [F R g]) init ∧
    ((gs.take j).foldl (fun R g => R ++ [F R g]) init).length = init.length + j := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set P := (gs.take j).foldl (fun R g => R ++ [F R g]) init with hP
  have hPl : P.length = init.length + j := by
    rw [hP, foldl_snoc_length F]; simp; omega
  have hpre : (P ++ [F P gs[j]]) <+: gs.foldl (fun R g => R ++ [F R g]) init := by
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    exact foldl_snoc_keeps F _ _
  refine ⟨?_, (List.prefix_append P _).trans hpre, hPl⟩
  rw [getD_of_initial hpre (by simp; omega), ← hPl]
  simp

def readGate (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)

theorem wireAt (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false = C.gates[j].op.eval
      (C.gates[j].inputs.map fun i => if i < x.length + j then (C.wires x).getD i false else false) := by
  obtain ⟨value,pre,len⟩ := foldl_snoc_split readGate C.gates x j hj false
  rw [show (C.wires x).getD (x.length + j) false = _ from value]
  unfold readGate
  congr 1
  apply List.map_congr_left
  intro i _
  split
  · exact (getD_of_initial pre (by omega) false).symm
  · apply List.getD_eq_default
    unfold readGate at len
    omega

theorem gate_value (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N)
    (hback : ReadsBack N C) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (N + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  have hw := wireAt C x j hj
  have he : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  rw [hx, ← he] at hw
  rw [hw]
  congr 1
  exact List.map_congr_left fun i hi => ite_eq_left (hback j hj i hi)

theorem only_reader (C : Circuit) (i j k : ℕ) (hj : j < C.size) (hk : k < C.size)
    (hc : readsIn C (Finset.range C.size) i = 1)
    (hij : i ∈ (gateAt C j).inputs) (hik : i ∈ (gateAt C k).inputs) : j = k := by
  by_contra h
  have hs : ({j, k} : Finset ℕ) ⊆ Finset.range C.size := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl <;> exact Finset.mem_range.mpr (by assumption)
  have hsum : (∑ g ∈ ({j, k} : Finset ℕ), (gateAt C g).inputs.count i) ≤
      readsIn C (Finset.range C.size) i :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair h, hc] at hsum
  have ha := List.count_pos_iff.mpr hij
  have hb := List.count_pos_iff.mpr hik
  omega
-- end of the copy

theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (PEqualNP.Represents.oneEach u v).length = n + m := by
  simp [PEqualNP.Represents.oneEach]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simpa using h)]
    simp only [List.getElem?_ofFn]
    simp [h, Fin.ext_iff]
    omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · simp [h2, Fin.ext_iff]
      have hu : ¬ i = u.val := by omega
      by_cases hv : i = n + v.val
      · simp [hv]
      · have hv' : ¬ i - n = v.val := by omega
        simp [hu, hv, hv']
    · simp [h2]
      omega

theorem wire_input (C : Circuit) {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) (hi : i < n + m) :
    (C.wires (PEqualNP.Represents.oneEach u v)).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  change (C.gates.foldl (fun w g => w ++ [readGate w g]) (PEqualNP.Represents.oneEach u v)).getD i false = _
  rw [getD_of_initial (foldl_snoc_keeps readGate C.gates _) (by rw [oneEach_length]; exact hi),
    oneEach_getD]

theorem wire_past (C : Circuit) (x : List Bool) (i : ℕ) (hi : x.length + C.gates.length ≤ i) :
    (C.wires x).getD i false = false := by
  apply List.getD_eq_default
  change (C.gates.foldl (fun w g => w ++ [readGate w g]) x).length ≤ i
  rw [foldl_snoc_length]
  exact hi

theorem wires_low (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  change (C.gates.foldl (fun w g => w ++ [readGate w g]) x).getD i false = _
  exact getD_of_initial (foldl_snoc_keeps readGate C.gates x) hi false

theorem mono_wires (N : ℕ) (C : Circuit) (hmono : Monotone2 C) (hback : ReadsBack N C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ w, (C.wires x).getD w false = true → (C.wires y).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hlo : w < N
    · rw [wires_low C y w (by omega)]
      rw [wires_low C x w (by omega)] at hw
      exact hxy w hw
    by_cases hhi : N + C.gates.length ≤ w
    · rw [wire_past C x w (by omega)] at hw
      exact absurd hw (by simp)
    obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
    have hj : j < C.gates.length := by omega
    rw [gate_value N C x hx hback j hj] at hw
    rw [gate_value N C y hy hback j hj]
    have hmem : gateAt C j ∈ C.gates := by
      rw [show gateAt C j = C.gates[j] from List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    have hop := (hmono _ hmem).1
    have hin : ∀ i ∈ (gateAt C j).inputs,
        (C.wires x).getD i false = true → (C.wires y).getD i false = true :=
      fun i hi => ih i (by have := hback j hj i hi; omega)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with h | h <;> rw [h] at hw ⊢ <;> simp only [GateOp.eval] at hw ⊢
    · simp only [List.all_eq_true, List.mem_map] at hw ⊢
      rintro _ ⟨i, hi, rfl⟩
      exact hin i hi (hw _ ⟨i, hi, rfl⟩)
    · simp only [List.any_eq_true, List.mem_map] at hw ⊢
      obtain ⟨_, ⟨i, hi, rfl⟩, hv⟩ := hw
      exact ⟨_, ⟨i, hi, rfl⟩, hin i hi hv⟩

theorem agree_off (N : ℕ) (C : Circuit) (hback : ReadsBack N C) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) (B : List ℕ)
    (hin : ∀ i < N, i ∉ B → x.getD i false = y.getD i false)
    (hgate : ∀ j < C.gates.length, N + j ∉ B → (∃ b ∈ B, b ∈ (gateAt C j).inputs) →
      (C.wires x).getD (N + j) false = (C.wires y).getD (N + j) false) :
    ∀ w, w ∉ B → (C.wires x).getD w false = (C.wires y).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hlo : w < N
    · rw [wires_low C x w (by omega), wires_low C y w (by omega)]
      exact hin w hlo hw
    by_cases hhi : N + C.gates.length ≤ w
    · rw [wire_past C x w (by omega), wire_past C y w (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
    have hj : j < C.gates.length := by omega
    by_cases hr : ∃ b ∈ B, b ∈ (gateAt C j).inputs
    · exact hgate j hj hw hr
    rw [gate_value N C x hx hback j hj, gate_value N C y hy hback j hj]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact ih i (hback j hj i hi) (fun hiB => hr ⟨i, hiB, hi⟩)

theorem or_value (N : ℕ) (C : Circuit) (z : List Bool) (hz : z.length = N)
    (hback : ReadsBack N C) (k : ℕ) (hk : k < C.gates.length) (a b : ℕ)
    (hop : (gateAt C k).op = GateOp.or)
    (hin : (gateAt C k).inputs = [a, b] ∨ (gateAt C k).inputs = [b, a]) :
    (C.wires z).getD (N + k) false = ((C.wires z).getD a false || (C.wires z).getD b false) := by
  rw [gate_value N C z hz hback k hk, hop]
  rcases hin with h | h
  · simp [h, GateOp.eval]
  · simp [h, GateOp.eval, Bool.or_comm]

end PEqualNP.Outside.L_meta_25488_aux

open PEqualNP.Outside.L_meta_25488_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_25488 : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : Fin n) (c : Fin m)
    (i j : Fin C.gates.length) (p q : ℕ),
  let g := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let wire := fun idx : Fin C.gates.length => n + m + idx.val
  let isOr := fun (z : Fin C.gates.length) (a b : ℕ) =>
    (g z.val).op = .or ∧ ((g z.val).inputs = [a, b] ∨ (g z.val).inputs = [b, a])
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C →
  u ≠ v → i ≠ j → isOr i u.val p → isOr j v.val q →
  PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.gates.length) u.val = 1 →
  C.output ∉ [u.val, wire i] → G u c = true → G v c = false →
  (C.wires (PEqualNP.Represents.oneEach v c)).getD (wire i) false = false ∧
    ∀ t : Fin C.gates.length, isOr t (wire i) (wire j) →
      ∃ h : Fin C.gates.length, h ≠ t ∧ wire i ∈ (g h.val).inputs := by
  classical
  intro n m G C u v c i j p q g wire isOr hmono hback hrep huv hij hI hJ hru hout hGu hGv
  let N := n + m
  have hu : (u : ℕ) < n := u.isLt
  have hv : (v : ℕ) < n := v.isLt
  have hc : (c : ℕ) < m := c.isLt
  have huv' : (u : ℕ) ≠ v := fun h => huv (Fin.ext h)
  let x1 := oneEach u c
  let x2 := oneEach v c
  let x3 := (List.range N).map (fun k => decide (k = u.val ∨ k = v.val ∨ k = n + c.val))
  have hl1 : x1.length = N := oneEach_length u c
  have hl2 : x2.length = N := oneEach_length v c
  have hl3 : x3.length = N := by simp [x3]
  have g3 : ∀ k, x3.getD k false = decide (k < N ∧ (k = u.val ∨ k = v.val ∨ k = n + c.val)) := by
    intro k
    simp only [x3, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range]
    by_cases hk : k < N <;> simp [hk]
  have hI' : (gateAt C i.val).op = GateOp.or ∧
      ((gateAt C i.val).inputs = [u.val, p] ∨ (gateAt C i.val).inputs = [p, u.val]) := hI
  have hJ' : (gateAt C j.val).op = GateOp.or ∧
      ((gateAt C j.val).inputs = [v.val, q] ∨ (gateAt C j.val).inputs = [q, v.val]) := hJ
  have hru' : readsIn C (Finset.range C.size) u.val = 1 := hru
  have hout' : C.output ∉ [u.val, N + i.val] := hout
  -- eval x3 = true by monotonicity from x1
  have e3 : C.eval x3 = true := by
    have e1 : C.eval x1 = true := (hrep u c).trans hGu
    exact mono_wires N C hmono hback x1 x3 hl1 hl3 (by
      intro k hk
      rw [oneEach_getD] at hk
      rw [g3]
      simp only [decide_eq_true_eq] at hk ⊢
      omega) C.output e1
  have e2 : C.eval x2 = false := (hrep v c).trans hGv
  -- inputs off u agree between x2 and x3
  have hin : ∀ k < N, k ∉ ([u.val] : List ℕ) → x2.getD k false = x3.getD k false := by
    intro k hk hku
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hku
    rw [oneEach_getD, g3]
    simp only [decide_eq_decide]
    constructor <;> intro h <;> omega
  have hin2 : ∀ k < N, k ∉ ([u.val, N + i.val] : List ℕ) → x2.getD k false = x3.getD k false := by
    intro k hk hku
    exact hin k hk (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hku ⊢; omega)
  -- the only reader of u is gate i
  have only_u : ∀ k < C.gates.length, u.val ∈ (gateAt C k).inputs → k = i.val := by
    intro k hk hk'
    have hmi : u.val ∈ (gateAt C i.val).inputs := by
      rcases hI'.2 with h | h <;> simp [h]
    exact only_reader C u.val k i.val hk i.isLt hru' hk' hmi
  have wI : ∀ z : List Bool, z.length = N → (C.wires z).getD (N + i.val) false =
      ((C.wires z).getD u.val false || (C.wires z).getD p false) :=
    fun z hz => or_value N C z hz hback i.val i.isLt u.val p hI'.1 hI'.2
  have wJ : ∀ z : List Bool, z.length = N → (C.wires z).getD (N + j.val) false =
      ((C.wires z).getD v.val false || (C.wires z).getD q false) :=
    fun z hz => or_value N C z hz hback j.val j.isLt v.val q hJ'.1 hJ'.2
  have u3 : (C.wires x3).getD u.val false = true := by
    rw [wires_low C x3 u.val (by omega), g3]; simp; omega
  have v2 : (C.wires x2).getD v.val false = true := by
    rw [wires_low C x2 v.val (by omega), oneEach_getD]; simp
  have v3 : (C.wires x3).getD v.val false = true := by
    rw [wires_low C x3 v.val (by omega), g3]; simp; omega
  have I3 : (C.wires x3).getD (N + i.val) false = true := by rw [wI x3 hl3, u3]; simp
  have J2 : (C.wires x2).getD (N + j.val) false = true := by rw [wJ x2 hl2, v2]; simp
  have J3 : (C.wires x3).getD (N + j.val) false = true := by rw [wJ x3 hl3, v3]; simp
  refine ⟨?_, ?_⟩
  · by_contra h1
    have h1' : (C.wires x2).getD (N + i.val) false = true := by simpa using h1
    have hag := agree_off N C hback x2 x3 hl2 hl3 [u.val] hin (by
      intro k hk _ hr
      obtain ⟨b, hb, hbk⟩ := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      have := only_u k hk hbk
      subst this
      rw [h1', I3]) C.output (by
        intro ho; apply hout'; simp only [List.mem_cons, List.not_mem_nil, or_false] at ho ⊢
        exact Or.inl ho)
    have : C.eval x2 = C.eval x3 := hag
    rw [e2, e3] at this
    exact Bool.false_ne_true this
  · intro t ht
    have ht' : (gateAt C t.val).op = GateOp.or ∧
        ((gateAt C t.val).inputs = [N + i.val, N + j.val] ∨
          (gateAt C t.val).inputs = [N + j.val, N + i.val]) := ht
    by_contra hno
    have only_I : ∀ k < C.gates.length, N + i.val ∈ (gateAt C k).inputs → k = t.val := by
      intro k hk hk'
      by_contra hkt
      exact hno ⟨⟨k, hk⟩, fun h => hkt (by rw [← h]), hk'⟩
    have wT : ∀ z : List Bool, z.length = N → (C.wires z).getD (N + j.val) false = true →
        (C.wires z).getD (N + t.val) false = true := by
      intro z hz hzj
      rw [or_value N C z hz hback t.val t.isLt _ _ ht'.1 ht'.2, hzj]; simp
    have hag := agree_off N C hback x2 x3 hl2 hl3 [u.val, N + i.val] hin2 (by
      intro k hk hkB hr
      obtain ⟨b, hb, hbk⟩ := hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb hkB
      rcases hb with rfl | rfl
      · have := only_u k hk hbk
        subst this
        exact absurd (Or.inr rfl) hkB
      · have := only_I k hk hbk
        subst this
        rw [wT x2 hl2 J2, wT x3 hl3 J3]) C.output hout'
    have : C.eval x2 = C.eval x3 := hag
    rw [e2, e3] at this
    exact Bool.false_ne_true this
