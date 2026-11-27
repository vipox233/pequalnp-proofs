import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25489_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

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
  obtain ⟨value, pre, len⟩ := foldl_snoc_split readGate C.gates x j hj false
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

theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  unfold oneEach
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

theorem agree_off_lt (N M : ℕ) (C : Circuit) (hback : ReadsBack N C) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) (B : List ℕ)
    (hin : ∀ i < N, i < M → i ∉ B → x.getD i false = y.getD i false)
    (hgate : ∀ j < C.gates.length, N + j < M → N + j ∉ B → (∃ b ∈ B, b ∈ (gateAt C j).inputs) →
      (C.wires x).getD (N + j) false = (C.wires y).getD (N + j) false) :
    ∀ w < M, w ∉ B → (C.wires x).getD w false = (C.wires y).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwM hw
    by_cases hlo : w < N
    · rw [wires_low C x w (by omega), wires_low C y w (by omega)]
      exact hin w hlo hwM hw
    by_cases hhi : N + C.gates.length ≤ w
    · rw [wire_past C x w (by omega), wire_past C y w (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
    have hj : j < C.gates.length := by omega
    by_cases hr : ∃ b ∈ B, b ∈ (gateAt C j).inputs
    · exact hgate j hj hwM hw hr
    rw [gate_value N C x hx hback j hj, gate_value N C y hy hback j hj]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hlt := hback j hj i hi
    exact ih i hlt (by omega) (fun hiB => hr ⟨i, hiB, hi⟩)

theorem agree_off (N : ℕ) (C : Circuit) (hback : ReadsBack N C) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) (B : List ℕ)
    (hin : ∀ i < N, i ∉ B → x.getD i false = y.getD i false)
    (hgate : ∀ j < C.gates.length, N + j ∉ B → (∃ b ∈ B, b ∈ (gateAt C j).inputs) →
      (C.wires x).getD (N + j) false = (C.wires y).getD (N + j) false) :
    ∀ w, w ∉ B → (C.wires x).getD w false = (C.wires y).getD w false :=
  fun w hw => agree_off_lt N (w + 1) C hback x y hx hy B
    (fun i hi _ hB => hin i hi hB)
    (fun j hj _ hB hr => hgate j hj hB hr)
    w (Nat.lt_succ_self w) hw

theorem or_value (N : ℕ) (C : Circuit) (z : List Bool) (hz : z.length = N)
    (hback : ReadsBack N C) (k : ℕ) (hk : k < C.gates.length) (a b : ℕ)
    (hop : (gateAt C k).op = GateOp.or)
    (hin : (gateAt C k).inputs = [a, b] ∨ (gateAt C k).inputs = [b, a]) :
    (C.wires z).getD (N + k) false = ((C.wires z).getD a false || (C.wires z).getD b false) := by
  rw [gate_value N C z hz hback k hk, hop]
  rcases hin with h | h
  · simp [h, GateOp.eval]
  · simp [h, GateOp.eval, Bool.or_comm]

theorem and_value (N : ℕ) (C : Circuit) (z : List Bool) (hz : z.length = N)
    (hback : ReadsBack N C) (k : ℕ) (hk : k < C.gates.length) (a b : ℕ)
    (hop : (gateAt C k).op = GateOp.and)
    (hin : (gateAt C k).inputs = [a, b] ∨ (gateAt C k).inputs = [b, a]) :
    (C.wires z).getD (N + k) false = ((C.wires z).getD a false && (C.wires z).getD b false) := by
  rw [gate_value N C z hz hback k hk, hop]
  rcases hin with h | h
  · simp [h, GateOp.eval]
  · simp [h, GateOp.eval, Bool.and_comm]

theorem list_two_mem {α : Type _} {l : List α} {a b : α} (hl : l.length ≤ 2) (hab : a ≠ b)
    (ha : a ∈ l) (hb : b ∈ l) : l = [a, b] ∨ l = [b, a] := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · simp at ha
  · simp at ha hb; exact absurd (ha.trans hb.symm) hab
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hab
  · simp at hl

def colOnly (n m : ℕ) (c : Fin m) : List Bool :=
  (List.range (n + m)).map (fun i => decide (i = n + c.val))

theorem colOnly_len (n m : ℕ) (c : Fin m) : (colOnly n m c).length = n + m := by
  simp [colOnly]

theorem colOnly_getD (n m : ℕ) (c : Fin m) (i : ℕ) :
    (colOnly n m c).getD i false = decide (i = n + c.val) := by
  simp only [colOnly, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < n + m
  · simp [h]
  · have hc := c.isLt
    have hne : i ≠ n + c.val := by omega
    simp [h, hne]

set_option maxHeartbeats 800000 in
theorem main_aux : ∀ (n k : ℕ) (G : Fin n → Fin (2 * k) → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit),
  2 ≤ k →
  Function.Injective G →
  (∀ u, (Finset.univ.filter (fun c => G u c = true)).card = k) →
  (∀ c, ∃ v, G v c = false) →
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2 * k) C →
  PEqualNP.Represents.Represents G C →
  (∀ x : Fin n,
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) x.val = 1 ∧
    ∃ (j : Fin C.gates.length) (s : ℕ),
      (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      ((C.gates.get j).inputs = [x.val, s] ∨ (C.gates.get j).inputs = [s, x.val])) →
  2 * n ≤ C.size := by
  classical
  intro n k G C hk2 hInj hCard hNonFull hmono hback hrep hRow
  let m := 2 * k
  let N := n + m
  have hRow' : ∀ x : Fin n,
      ∃ (j : Fin C.gates.length) (s : ℕ),
        (gateAt C j.val).op = GateOp.or ∧
        ((gateAt C j.val).inputs = [x.val, s] ∨ (gateAt C j.val).inputs = [s, x.val]) := by
    intro x
    obtain ⟨_, j, s, hop, hin⟩ := hRow x
    have hgj : gateAt C j.val = C.gates.get j := List.getD_eq_getElem _ _ j.isLt
    exact ⟨j, s, by rw [hgj]; exact hop, by rw [hgj]; exact hin⟩
  choose ρ s hρ_op hρ_in using hRow'
  have hρ_mem : ∀ x : Fin n, x.val ∈ (gateAt C (ρ x).val).inputs := by
    intro x; rcases hρ_in x with h | h <;> simp [h]
  have hs_mem : ∀ x : Fin n, s x ∈ (gateAt C (ρ x).val).inputs := by
    intro x; rcases hρ_in x with h | h <;> simp [h]
  have only_x : ∀ (x : Fin n) (j : ℕ), j < C.gates.length → x.val ∈ (gateAt C j).inputs → j = (ρ x).val := by
    intro x j hj hxj
    exact only_reader C x.val j (ρ x).val hj (ρ x).isLt (hRow x).1 hxj (hρ_mem x)
  have hρ_val : ∀ (x : Fin n) (z : List Bool), z.length = N →
      (C.wires z).getD (N + (ρ x).val) false =
        ((C.wires z).getD x.val false || (C.wires z).getD (s x) false) := by
    intro x z hz
    exact or_value N C z hz hback (ρ x).val (ρ x).isLt x.val (s x) (hρ_op x) (hρ_in x)
  have hExistsTrue : ∀ u : Fin n, ∃ c : Fin m, G u c = true := by
    intro u
    have hc : 0 < (Finset.univ.filter (fun c => G u c = true)).card := by rw [hCard u]; omega
    obtain ⟨c, hc'⟩ := Finset.card_pos.mp hc
    exact ⟨c, (Finset.mem_filter.mp hc').2⟩
  have hExistsFalse : ∀ u : Fin n, ∃ c : Fin m, G u c = false := by
    intro u
    have hc : (Finset.univ.filter (fun c => G u c = true)).card < (Finset.univ : Finset (Fin m)).card := by
      rw [hCard u, Finset.card_univ, Fintype.card_fin]; omega
    have hne : Finset.univ.filter (fun c => G u c = true) ≠ Finset.univ := fun h => by rw [h] at hc; exact lt_irrefl _ hc
    obtain ⟨c, _, hcf⟩ : ∃ c ∈ (Finset.univ : Finset (Fin m)), c ∉ Finset.univ.filter (fun c => G u c = true) := by
      by_contra hall; push Not at hall
      exact hne (Finset.Subset.antisymm (Finset.filter_subset _ _) hall)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hcf
    exact ⟨c, hcf⟩
  have hDiff : ∀ u v : Fin n, u ≠ v → ∃ c : Fin m, G u c = true ∧ G v c = false := by
    intro u v huv
    by_contra hall
    push Not at hall
    have hsub : Finset.univ.filter (fun c => G u c = true) ⊆ Finset.univ.filter (fun c => G v c = true) := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      cases hv : G v c
      · exact absurd hv (hall c hc)
      · rfl
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hCard u, hCard v])
    apply huv
    apply hInj
    funext c
    have hiff : G u c = true ↔ G v c = true := by
      have hm := Finset.ext_iff.mp heq c
      simpa using hm
    cases hu : G u c <;> cases hv : G v c <;> simp_all
  have hout_x : ∀ u : Fin n, C.output ≠ u.val := by
    intro u h
    obtain ⟨c, hc⟩ := hExistsFalse u
    have he := hrep u c
    rw [hc] at he
    have hw : C.eval (oneEach u c) = true := by
      unfold Circuit.eval
      rw [h, wires_low C _ _ (by rw [oneEach_length]; omega), oneEach_getD]
      simp
    rw [hw] at he
    exact (fun h => Bool.false_ne_true h.symm) he
  have hout_ρ : ∀ u : Fin n, C.output ≠ N + (ρ u).val := by
    intro u h
    obtain ⟨c, hc⟩ := hExistsFalse u
    have he := hrep u c
    rw [hc] at he
    have hw : C.eval (oneEach u c) = true := by
      unfold Circuit.eval
      rw [h, hρ_val u _ (oneEach_length u c), wires_low C _ _ (by rw [oneEach_length]; omega), oneEach_getD]
      simp
    rw [hw] at he
    exact (fun h => Bool.false_ne_true h.symm) he
  have hρ_inj : Function.Injective ρ := by
    intro u v huv
    by_contra hne
    have hne' : u.val ≠ v.val := fun h => hne (Fin.ext h)
    obtain ⟨c, hGu, hGv⟩ := hDiff u v hne
    have h1 := oneEach_length u c
    have h2 := oneEach_length v c
    have hm1 : u.val ∈ (gateAt C (ρ u).val).inputs := hρ_mem u
    have hm2 : v.val ∈ (gateAt C (ρ u).val).inputs := by rw [huv]; exact hρ_mem v
    have hρu_u : (C.wires (oneEach u c)).getD (N + (ρ u).val) false = true := by
      rw [hρ_val u _ h1, wires_low C _ _ (by rw [h1]; omega), oneEach_getD]; simp
    have hρu_v : (C.wires (oneEach v c)).getD (N + (ρ u).val) false = true := by
      rw [huv, hρ_val v _ h2, wires_low C _ _ (by rw [h2]; omega), oneEach_getD]; simp
    have hag := agree_off N C hback (oneEach u c) (oneEach v c) h1 h2 [u.val, v.val]
      (by
        intro i hi hiB
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hiB
        rw [oneEach_getD, oneEach_getD]
        simp only [decide_eq_decide]
        constructor <;> intro h <;> rcases h with rfl | rfl <;> omega)
      (by
        intro j hj _ hr
        obtain ⟨b, hb, hbj⟩ := hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · have := only_x u j hj hbj; subst this; rw [hρu_u, hρu_v]
        · have := only_x v j hj hbj; rw [← huv] at this; subst this; rw [hρu_u, hρu_v])
      C.output (by
        intro h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h
        · exact hout_x u h
        · exact hout_x v h)
    have : C.eval (oneEach u c) = C.eval (oneEach v c) := hag
    rw [hrep u c, hrep v c, hGu, hGv] at this
    exact (fun h => Bool.false_ne_true h.symm) this
  have hDom : ∀ (u v : Fin n) (c : Fin m), u ≠ v → G u c = true → G v c = false →
      (C.wires (oneEach v c)).getD (N + (ρ u).val) false = false := by
    intro u v c huv hGu hGv
    have huv' : u.val ≠ v.val := fun h => huv (Fin.ext h)
    let x1 := oneEach u c
    let x2 := oneEach v c
    let x3 := (List.range N).map (fun i => decide (i = u.val ∨ i = v.val ∨ i = n + c.val))
    have hl1 : x1.length = N := oneEach_length u c
    have hl2 : x2.length = N := oneEach_length v c
    have hl3 : x3.length = N := by simp [x3]
    have g3 : ∀ i, x3.getD i false = decide (i < N ∧ (i = u.val ∨ i = v.val ∨ i = n + c.val)) := by
      intro i
      simp only [x3, List.getD_eq_getElem?_getD, List.getElem?_map]
      by_cases hi : i < N <;> simp [hi]
    have e3 : C.eval x3 = true := by
      have e1 : C.eval x1 = true := (hrep u c).trans hGu
      exact mono_wires N C hmono hback x1 x3 hl1 hl3 (by
        intro i hi
        rw [oneEach_getD] at hi; rw [g3]
        simp only [decide_eq_true_eq] at hi ⊢; omega) C.output e1
    have e2 : C.eval x2 = false := (hrep v c).trans hGv
    by_contra h1
    have h1' : (C.wires x2).getD (N + (ρ u).val) false = true := by simpa using h1
    have I3 : (C.wires x3).getD (N + (ρ u).val) false = true := by
      rw [hρ_val u x3 hl3, wires_low C x3 u.val (by omega), g3]; simp; omega
    have hag := agree_off N C hback x2 x3 hl2 hl3 [u.val]
      (by
        intro i hi hiu
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hiu
        rw [oneEach_getD, g3]
        simp only [decide_eq_decide]
        constructor <;> intro h <;> omega)
      (by
        intro j hj _ hr
        obtain ⟨b, hb, hbj⟩ := hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        subst hb
        have := only_x u j hj hbj; subst this; rw [h1', I3])
      C.output (by
        intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; exact hout_x u h)
    have : C.eval x2 = C.eval x3 := hag
    rw [e2, e3] at this
    exact Bool.false_ne_true this
  have hColOff : ∀ (v : Fin n) (c : Fin m), G v c = true →
      (C.wires (colOnly n m c)).getD (N + (ρ v).val) false = false := by
    intro v c hGv
    by_contra h1
    have h1' : (C.wires (colOnly n m c)).getD (N + (ρ v).val) false = true := by simpa using h1
    have hl0 : (colOnly n m c).length = N := colOnly_len n m c
    have hl1 : (oneEach v c).length = N := oneEach_length v c
    have I1 : (C.wires (oneEach v c)).getD (N + (ρ v).val) false = true := by
      rw [hρ_val v _ hl1, wires_low C _ _ (by omega), oneEach_getD]; simp
    have hag := agree_off N C hback (colOnly n m c) (oneEach v c) hl0 hl1 [v.val]
      (by
        intro i hi hiv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hiv
        rw [colOnly_getD, oneEach_getD]
        simp only [decide_eq_decide]
        constructor <;> intro h <;> omega)
      (by
        intro j hj _ hr
        obtain ⟨b, hb, hbj⟩ := hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
        subst hb
        have := only_x v j hj hbj; subst this; rw [h1', I1])
      C.output (by
        intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h; exact hout_x v h)
    have he0 : C.eval (colOnly n m c) = true := hag.trans ((hrep v c).trans hGv)
    obtain ⟨w, hGw⟩ := hNonFull c
    have hew : C.eval (oneEach w c) = true :=
      mono_wires N C hmono hback (colOnly n m c) (oneEach w c) hl0 (oneEach_length w c) (by
        intro i hi
        rw [colOnly_getD] at hi; rw [oneEach_getD]
        simp only [decide_eq_true_eq] at hi ⊢; exact Or.inr hi) C.output he0
    rw [hrep w c, hGw] at hew
    exact Bool.false_ne_true hew
  have hNoRowRead : ∀ u v : Fin n, N + (ρ u).val ∉ (gateAt C (ρ v).val).inputs := by
    intro u v hmem
    by_cases huv : u = v
    · subst huv
      have := hback (ρ u).val (ρ u).isLt (N + (ρ u).val) hmem
      omega
    · obtain ⟨c, hGu, hGv⟩ := hDiff u v huv
      have hdom := hDom u v c huv hGu hGv
      have hs : s v = N + (ρ u).val := by
        rcases hρ_in v with h | h <;> rw [h] at hmem <;>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem <;>
          rcases hmem with h' | h'
        · omega
        · exact h'.symm
        · exact h'.symm
        · omega
      have hv_on : (C.wires (oneEach v c)).getD (N + (ρ v).val) false = true := by
        rw [hρ_val v _ (oneEach_length v c), wires_low C _ _ (by rw [oneEach_length]; omega), oneEach_getD]
        simp
      have hu_on : (C.wires (oneEach u c)).getD (N + (ρ v).val) false = true := by
        rw [hρ_val v _ (oneEach_length u c), hs]
        have hu1 : (C.wires (oneEach u c)).getD (N + (ρ u).val) false = true := by
          rw [hρ_val u _ (oneEach_length u c), wires_low C _ _ (by rw [oneEach_length]; omega), oneEach_getD]
          simp
        rw [hu1]; simp
      obtain ⟨c', hGv', hGu'⟩ := hDiff v u (Ne.symm huv)
      have hdom' := hDom v u c' (Ne.symm huv) hGv' hGu'
      have hu_on' : (C.wires (oneEach u c')).getD (N + (ρ v).val) false = true := by
        rw [hρ_val v _ (oneEach_length u c'), hs]
        have hu1 : (C.wires (oneEach u c')).getD (N + (ρ u).val) false = true := by
          rw [hρ_val u _ (oneEach_length u c'), wires_low C _ _ (by rw [oneEach_length]; omega), oneEach_getD]
          simp
        rw [hu1]; simp
      rw [hdom'] at hu_on'
      exact Bool.false_ne_true hu_on'
  let Readers : Fin n → Finset (Fin C.gates.length) :=
    fun u => Finset.univ.filter (fun t => N + (ρ u).val ∈ (gateAt C t.val).inputs)
  have hReadersNonempty : ∀ u : Fin n, (Readers u).Nonempty := by
    intro u
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    obtain ⟨c, hGu⟩ := hExistsTrue u
    obtain ⟨v, hGv⟩ := hNonFull c
    have huv : u ≠ v := fun h => by rw [h, hGv] at hGu; exact Bool.false_ne_true hGu
    let x1 := oneEach u c
    let x2 := oneEach v c
    let x3 := (List.range N).map (fun i => decide (i = u.val ∨ i = v.val ∨ i = n + c.val))
    have hl1 : x1.length = N := oneEach_length u c
    have hl2 : x2.length = N := oneEach_length v c
    have hl3 : x3.length = N := by simp [x3]
    have g3 : ∀ i, x3.getD i false = decide (i < N ∧ (i = u.val ∨ i = v.val ∨ i = n + c.val)) := by
      intro i
      simp only [x3, List.getD_eq_getElem?_getD, List.getElem?_map]
      by_cases hi : i < N <;> simp [hi]
    have e3 : C.eval x3 = true := by
      have e1 : C.eval x1 = true := (hrep u c).trans hGu
      exact mono_wires N C hmono hback x1 x3 hl1 hl3 (by
        intro i hi; rw [oneEach_getD] at hi; rw [g3]
        simp only [decide_eq_true_eq] at hi ⊢; omega) C.output e1
    have e2 : C.eval x2 = false := (hrep v c).trans hGv
    have hag := agree_off N C hback x2 x3 hl2 hl3 [u.val, N + (ρ u).val]
      (by
        intro i hi hiB
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hiB
        rw [oneEach_getD, g3]; simp only [decide_eq_decide]; constructor <;> intro h <;> omega)
      (by
        intro j hj hjB hr
        obtain ⟨b, hb, hbj⟩ := hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hb hjB
        rcases hb with rfl | rfl
        · have := only_x u j hj hbj; exact absurd (Or.inr (by omega)) hjB
        · have hmem : (⟨j, hj⟩ : Fin C.gates.length) ∈ Readers u := by
            simp only [Readers, Finset.mem_filter, Finset.mem_univ, true_and]; exact hbj
          rw [hemp] at hmem; simp at hmem)
      C.output (by
        intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h
        · exact hout_x u h
        · exact hout_ρ u h)
    have : C.eval x2 = C.eval x3 := hag
    rw [e2, e3] at this
    exact Bool.false_ne_true this
  let Rset : Finset (Fin C.gates.length) := Finset.univ.image ρ
  let AllReaders : Finset (Fin C.gates.length) := Finset.univ.biUnion Readers
  have hDisj_R_All : Disjoint Rset AllReaders := by
    rw [Finset.disjoint_left]
    intro t htR htA
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp htR
    obtain ⟨u, _, htU⟩ := Finset.mem_biUnion.mp htA
    simp only [Readers, Finset.mem_filter, Finset.mem_univ, true_and] at htU
    exact hNoRowRead u v htU
  let S_A : Finset (Fin n) := Finset.univ.filter (fun u => 2 ≤ (Readers u).card)
  let S_B : Finset (Fin n) := Finset.univ.filter (fun u => (Readers u).card = 1 ∧
      ∀ t ∈ Readers u, ∀ v : Fin n, v ≠ u → t ∉ Readers v)
  let S_C : Finset (Fin n) := Finset.univ.filter (fun u => (Readers u).card = 1 ∧
      ∃ t ∈ Readers u, ∃ v : Fin n, v ≠ u ∧ t ∈ Readers v)
  have hCaseC : ∀ u ∈ S_C, ∃ g : Fin C.gates.length,
      (∀ c : Fin m, (C.wires (colOnly n m c)).getD (N + g.val) false = G u c) ∧
      g ∉ Rset ∧ g ∉ AllReaders := by
    intro u huC
    simp only [S_C, Finset.mem_filter, Finset.mem_univ, true_and] at huC
    obtain ⟨hcard1, t, htU, v, hvu, htV⟩ := huC
    have huniq_t : ∀ j < C.gates.length, N + (ρ u).val ∈ (gateAt C j).inputs → j = t.val := by
      intro j hj hmem
      have hjR : (⟨j, hj⟩ : Fin C.gates.length) ∈ Readers u := by
        simp only [Readers, Finset.mem_filter, Finset.mem_univ, true_and]; exact hmem
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
      have h1 : t = w := by rw [hw] at htU; exact Finset.mem_singleton.mp htU
      have h2 : (⟨j, hj⟩ : Fin C.gates.length) = w := by rw [hw] at hjR; exact Finset.mem_singleton.mp hjR
      have h3 : (⟨j, hj⟩ : Fin C.gates.length) = t := h2.trans h1.symm
      exact congrArg Fin.val h3
    have ht_in_u : N + (ρ u).val ∈ (gateAt C t.val).inputs := (Finset.mem_filter.mp htU).2
    have ht_in_v : N + (ρ v).val ∈ (gateAt C t.val).inputs := (Finset.mem_filter.mp htV).2
    have hρuv_ne : N + (ρ u).val ≠ N + (ρ v).val := by
      intro h; apply hvu; exact (hρ_inj (Fin.ext (by omega))).symm
    have ht_memC : gateAt C t.val ∈ C.gates := by
      rw [show gateAt C t.val = C.gates[t.val] from List.getD_eq_getElem _ _ t.isLt]
      exact List.getElem_mem t.isLt
    have ht_in : (gateAt C t.val).inputs = [N + (ρ u).val, N + (ρ v).val] ∨
        (gateAt C t.val).inputs = [N + (ρ v).val, N + (ρ u).val] :=
      list_two_mem (hmono _ ht_memC).2 hρuv_ne ht_in_u ht_in_v
    have ht_op : (gateAt C t.val).op = GateOp.and := by
      have hop := (hmono _ ht_memC).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with h | h
      · exact h
      · exfalso
        obtain ⟨c, hGu, hGv⟩ := hDiff u v (Ne.symm hvu)
        let x1 := oneEach u c
        let x2 := oneEach v c
        let x3 := (List.range N).map (fun i => decide (i = u.val ∨ i = v.val ∨ i = n + c.val))
        have hl1 : x1.length = N := oneEach_length u c
        have hl2 : x2.length = N := oneEach_length v c
        have hl3 : x3.length = N := by simp [x3]
        have g3 : ∀ i, x3.getD i false = decide (i < N ∧ (i = u.val ∨ i = v.val ∨ i = n + c.val)) := by
          intro i
          simp only [x3, List.getD_eq_getElem?_getD, List.getElem?_map]
          by_cases hi : i < N <;> simp [hi]
        have e3 : C.eval x3 = true := by
          have e1 : C.eval x1 = true := (hrep u c).trans hGu
          exact mono_wires N C hmono hback x1 x3 hl1 hl3 (by
            intro i hi; rw [oneEach_getD] at hi; rw [g3]
            simp only [decide_eq_true_eq] at hi ⊢; omega) C.output e1
        have e2 : C.eval x2 = false := (hrep v c).trans hGv
        have J2 : (C.wires x2).getD (N + (ρ v).val) false = true := by
          rw [hρ_val v x2 hl2, wires_low C x2 v.val (by omega), oneEach_getD]; simp
        have J3 : (C.wires x3).getD (N + (ρ v).val) false = true := by
          rw [hρ_val v x3 hl3, wires_low C x3 v.val (by omega), g3]; simp; omega
        have T2 : (C.wires x2).getD (N + t.val) false = true := by
          rw [or_value N C x2 hl2 hback t.val t.isLt _ _ h ht_in, J2]; simp
        have T3 : (C.wires x3).getD (N + t.val) false = true := by
          rw [or_value N C x3 hl3 hback t.val t.isLt _ _ h ht_in, J3]; simp
        have hag := agree_off N C hback x2 x3 hl2 hl3 [u.val, N + (ρ u).val]
          (by
            intro i hi hiB
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hiB
            rw [oneEach_getD, g3]; simp only [decide_eq_decide]; constructor <;> intro hh <;> omega)
          (by
            intro j hj hjB hr
            obtain ⟨b, hb, hbj⟩ := hr
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hb hjB
            rcases hb with rfl | rfl
            · have := only_x u j hj hbj; exact absurd (Or.inr (by omega)) hjB
            · have := huniq_t j hj hbj; subst this; rw [T2, T3])
          C.output (by
            intro hh; simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
            rcases hh with hh | hh
            · exact hout_x u hh
            · exact hout_ρ u hh)
        have : C.eval x2 = C.eval x3 := hag
        rw [e2, e3] at this
        exact Bool.false_ne_true this
    have hsv_lt : s v < N + t.val := by
      have h1 := hback (ρ v).val (ρ v).isLt (s v) (hs_mem v)
      have h2 := hback t.val t.isLt (N + (ρ v).val) ht_in_v
      omega
    have hsv_ne_u : s v ≠ u.val := by
      intro h
      have h1 := only_x u (ρ v).val (ρ v).isLt (by rw [← h]; exact hs_mem v)
      exact hvu (hρ_inj (Fin.ext h1))
    have hsv_ne_ρu : s v ≠ N + (ρ u).val := by
      intro h
      exact hNoRowRead u v (by rw [← h]; exact hs_mem v)
    have hGu_imp : ∀ c : Fin m, G u c = true → (C.wires (colOnly n m c)).getD (s v) false = true := by
      intro c hGu
      by_contra hsf
      have hsf' : (C.wires (colOnly n m c)).getD (s v) false = false := by simpa using hsf
      have hl0 : (colOnly n m c).length = N := colOnly_len n m c
      have hl1 : (oneEach u c).length = N := oneEach_length u c
      have hsv_eq : (C.wires (colOnly n m c)).getD (s v) false = (C.wires (oneEach u c)).getD (s v) false := by
        exact agree_off_lt N (N + t.val) C hback (colOnly n m c) (oneEach u c) hl0 hl1
          [u.val, N + (ρ u).val]
          (by
            intro i hi _ hiB
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hiB
            rw [colOnly_getD, oneEach_getD]; simp only [decide_eq_decide]; constructor <;> intro hh <;> omega)
          (by
            intro j hj hjM hjB hr
            obtain ⟨b, hb, hbj⟩ := hr
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hb hjB
            rcases hb with rfl | rfl
            · have := only_x u j hj hbj; exact absurd (Or.inr (by omega)) hjB
            · have := huniq_t j hj hbj; omega)
          (s v) hsv_lt (by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto)
      have hsf1 : (C.wires (oneEach u c)).getD (s v) false = false := hsv_eq.symm.trans hsf'
      have hρv0 : (C.wires (colOnly n m c)).getD (N + (ρ v).val) false = false := by
        rw [hρ_val v _ hl0, wires_low C _ _ (by omega), colOnly_getD, hsf']
        have : v.val ≠ n + c.val := by omega
        simp [this]
      have hρv1 : (C.wires (oneEach u c)).getD (N + (ρ v).val) false = false := by
        rw [hρ_val v _ hl1, wires_low C _ _ (by omega), oneEach_getD, hsf1]
        have : v.val ≠ u.val := fun h => hvu (Fin.ext h)
        have : v.val ≠ n + c.val := by omega
        simp [*]
      have ht0 : (C.wires (colOnly n m c)).getD (N + t.val) false = false := by
        rw [and_value N C _ hl0 hback t.val t.isLt _ _ ht_op ht_in, hρv0]; simp
      have ht1 : (C.wires (oneEach u c)).getD (N + t.val) false = false := by
        rw [and_value N C _ hl1 hback t.val t.isLt _ _ ht_op ht_in, hρv1]; simp
      have hag := agree_off N C hback (colOnly n m c) (oneEach u c) hl0 hl1 [u.val, N + (ρ u).val]
        (by
          intro i hi hiB
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hiB
          rw [colOnly_getD, oneEach_getD]; simp only [decide_eq_decide]; constructor <;> intro hh <;> omega)
        (by
          intro j hj hjB hr
          obtain ⟨b, hb, hbj⟩ := hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb hjB
          rcases hb with rfl | rfl
          · have := only_x u j hj hbj; exact absurd (Or.inr (by omega)) hjB
          · have := huniq_t j hj hbj; subst this; rw [ht0, ht1])
        C.output (by
          intro hh; simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
          rcases hh with hh | hh
          · exact hout_x u hh
          · exact hout_ρ u hh)
      have he0 : C.eval (colOnly n m c) = true := hag.trans ((hrep u c).trans hGu)
      obtain ⟨w, hGw⟩ := hNonFull c
      have hew : C.eval (oneEach w c) = true :=
        mono_wires N C hmono hback (colOnly n m c) (oneEach w c) hl0 (oneEach_length w c) (by
          intro i hi; rw [colOnly_getD] at hi; rw [oneEach_getD]
          simp only [decide_eq_true_eq] at hi ⊢; exact Or.inr hi) C.output he0
      rw [hrep w c, hGw] at hew
      exact Bool.false_ne_true hew
    have hGv_imp : ∀ c : Fin m, G v c = true → (C.wires (colOnly n m c)).getD (s v) false = false := by
      intro c hGv
      have h1 := hColOff v c hGv
      rw [hρ_val v _ (colOnly_len n m c)] at h1
      exact (Bool.or_eq_false_iff.mp h1).2
    have hDisj_uv : Disjoint (Finset.univ.filter (fun c => G u c = true))
        (Finset.univ.filter (fun c => G v c = true)) := by
      rw [Finset.disjoint_left]
      intro c hcu hcv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcu hcv
      have h1 := hGu_imp c hcu
      have h2 := hGv_imp c hcv
      rw [h1] at h2
      exact (fun h => Bool.false_ne_true h.symm) h2
    have hUnion_uv : Finset.univ.filter (fun c => G u c = true) ∪
        Finset.univ.filter (fun c => G v c = true) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_union_of_disjoint hDisj_uv, hCard u, hCard v, Finset.card_univ, Fintype.card_fin]
      omega
    have hsv_exact : ∀ c : Fin m, (C.wires (colOnly n m c)).getD (s v) false = G u c := by
      intro c
      cases huc : G u c
      · have hvc : G v c = true := by
          have hm : c ∈ Finset.univ.filter (fun c => G u c = true) ∪
              Finset.univ.filter (fun c => G v c = true) := by rw [hUnion_uv]; exact Finset.mem_univ c
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, huc,
            Bool.false_eq_true, false_or] at hm
          exact hm
        exact hGv_imp c hvc
      · exact hGu_imp c huc
    have hsv_geN : N ≤ s v := by
      by_contra hlt
      push Not at hlt
      by_cases hln : s v < n
      · obtain ⟨c, hGu⟩ := hExistsTrue u
        have h1 := hsv_exact c
        rw [wires_low C _ _ (by rw [colOnly_len]; omega), colOnly_getD] at h1
        have hne : s v ≠ n + c.val := by omega
        simp [hne, hGu] at h1
      · have hc0 : s v - n < m := by omega
        let c0 : Fin m := ⟨s v - n, hc0⟩
        have hsub : Finset.univ.filter (fun c => G u c = true) ⊆ ({c0} : Finset (Fin m)) := by
          intro c hc
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
          have h1 := hsv_exact c
          rw [wires_low C _ _ (by rw [colOnly_len]; omega), colOnly_getD, hc] at h1
          simp only [decide_eq_true_eq] at h1
          simp only [Finset.mem_singleton]
          exact Fin.ext (by dsimp [c0]; omega)
        have hle := Finset.card_le_card hsub
        rw [hCard u, Finset.card_singleton] at hle
        omega
    have hsv_lt_tot : s v < N + C.gates.length := by
      have := hback (ρ v).val (ρ v).isLt (s v) (hs_mem v)
      omega
    let g : Fin C.gates.length := ⟨s v - N, by omega⟩
    have hg_eq : N + g.val = s v := by simp [g]; omega
    refine ⟨g, fun c => by rw [hg_eq]; exact hsv_exact c, ?_, ?_⟩
    · intro hgR
      obtain ⟨x, _, hxg⟩ := Finset.mem_image.mp hgR
      have hmem : N + (ρ x).val ∈ (gateAt C (ρ v).val).inputs := by
        rw [hxg, hg_eq]; exact hs_mem v
      exact hNoRowRead x v hmem
    · intro hgA
      obtain ⟨x, _, hgx⟩ := Finset.mem_biUnion.mp hgA
      simp only [Readers, Finset.mem_filter, Finset.mem_univ, true_and] at hgx
      have hxv : x ≠ v := by
        intro h; subst h
        have h1 := hback g.val g.isLt (N + (ρ x).val) hgx
        have h2 := hback (ρ x).val (ρ x).isLt (s x) (hs_mem x)
        omega
      have hg_memC : gateAt C g.val ∈ C.gates := by
        rw [show gateAt C g.val = C.gates[g.val] from List.getD_eq_getElem _ _ g.isLt]
        exact List.getElem_mem g.isLt
      have hop := (hmono _ hg_memC).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      rcases hop with hand | hor
      · have hex : ∃ c : Fin m, G x c = true ∧ G u c = true := by
          by_contra hall
          push Not at hall
          have hsub : Finset.univ.filter (fun c => G x c = true) ⊆
              Finset.univ.filter (fun c => G v c = true) := by
            intro c hc
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
            have huc : G u c = false := by
              cases h : G u c
              · rfl
              · exact absurd h (hall c hc)
            have hm : c ∈ Finset.univ.filter (fun c => G u c = true) ∪
                Finset.univ.filter (fun c => G v c = true) := by rw [hUnion_uv]; exact Finset.mem_univ c
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, huc,
              Bool.false_eq_true, false_or] at hm
            exact hm
          have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hCard x, hCard v])
          apply hxv
          apply hInj
          funext c
          have hiff : G x c = true ↔ G v c = true := by
            have hm := Finset.ext_iff.mp heq c; simpa using hm
          cases hx : G x c <;> cases hv : G v c <;> simp_all
        obtain ⟨c, hGx, hGu⟩ := hex
        have hg_on : (C.wires (colOnly n m c)).getD (N + g.val) false = true := by
          rw [hg_eq, hsv_exact c, hGu]
        have hg_on' := hg_on
        rw [gate_value N C _ (colOnly_len n m c) hback g.val g.isLt, hand] at hg_on'
        change ((gateAt C g.val).inputs.map fun i => (C.wires (colOnly n m c)).getD i false).all id = true at hg_on'
        have hρx_on : (C.wires (colOnly n m c)).getD (N + (ρ x).val) false = true := by
          have hall := List.all_eq_true.mp hg_on'
          exact hall _ (List.mem_map.mpr ⟨N + (ρ x).val, hgx, rfl⟩)
        have hρx_off := hColOff x c hGx
        rw [hρx_on] at hρx_off
        exact (fun h => Bool.false_ne_true h.symm) hρx_off
      · obtain ⟨c, hGv, hGx⟩ := hDiff v x (Ne.symm hxv)
        have hρx_on : (C.wires (oneEach x c)).getD (N + (ρ x).val) false = true := by
          rw [hρ_val x _ (oneEach_length x c), wires_low C _ _ (by rw [oneEach_length]; omega), oneEach_getD]
          simp
        have hg_on : (C.wires (oneEach x c)).getD (N + g.val) false = true := by
          rw [gate_value N C _ (oneEach_length x c) hback g.val g.isLt, hor]
          change ((gateAt C g.val).inputs.map fun i => (C.wires (oneEach x c)).getD i false).any id = true
          exact List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨N + (ρ x).val, hgx, hρx_on⟩, rfl⟩
        have hρv_on : (C.wires (oneEach x c)).getD (N + (ρ v).val) false = true := by
          rw [hρ_val v _ (oneEach_length x c), ← hg_eq, hg_on]; simp
        have hρv_off : (C.wires (oneEach x c)).getD (N + (ρ v).val) false = false :=
          hDom v x c (Ne.symm hxv) hGv hGx
        rw [hρv_on] at hρv_off
        exact (fun h => Bool.false_ne_true h.symm) hρv_off
  choose gc hgc_eq hgc_notR hgc_notA using hCaseC
  let G_C : Finset (Fin C.gates.length) := S_C.attach.image (fun x => gc x.val x.property)
  have hGC_card : G_C.card = S_C.card := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_attach
    · intro ⟨u1, hu1⟩ ⟨u2, hu2⟩ heq
      dsimp only at heq
      apply Subtype.ext
      apply hInj
      funext c
      rw [← hgc_eq u1 hu1 c, ← hgc_eq u2 hu2 c, heq]
  have hDisj_GC_R : Disjoint G_C Rset := by
    rw [Finset.disjoint_left]
    intro g hgGC
    obtain ⟨⟨u, hu⟩, _, rfl⟩ := Finset.mem_image.mp hgGC
    exact hgc_notR u hu
  have hDisj_GC_A : Disjoint G_C AllReaders := by
    rw [Finset.disjoint_left]
    intro g hgGC
    obtain ⟨⟨u, hu⟩, _, rfl⟩ := Finset.mem_image.mp hgGC
    exact hgc_notA u hu
  have hPart_cover : S_A ∪ S_B ∪ S_C = Finset.univ := by
    ext u
    simp only [Finset.mem_union, Finset.mem_univ, iff_true, S_A, S_B, S_C, Finset.mem_filter, true_and]
    have hpos : 0 < (Readers u).card := Finset.card_pos.mpr (hReadersNonempty u)
    by_cases h2 : 2 ≤ (Readers u).card
    · exact Or.inl (Or.inl h2)
    · have h1 : (Readers u).card = 1 := by omega
      by_cases hsh : ∃ t ∈ Readers u, ∃ v : Fin n, v ≠ u ∧ t ∈ Readers v
      · exact Or.inr ⟨h1, hsh⟩
      · push Not at hsh
        exact Or.inl (Or.inr ⟨h1, hsh⟩)
  have hDisj_AB : Disjoint S_A S_B := by
    rw [Finset.disjoint_left]; intro u ha hb
    simp only [S_A, S_B, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb; omega
  have hDisj_AC : Disjoint S_A S_C := by
    rw [Finset.disjoint_left]; intro u ha hc
    simp only [S_A, S_C, Finset.mem_filter, Finset.mem_univ, true_and] at ha hc; omega
  have hDisj_BC : Disjoint S_B S_C := by
    rw [Finset.disjoint_left]; intro u hb hc
    simp only [S_B, S_C, Finset.mem_filter, Finset.mem_univ, true_and] at hb hc
    obtain ⟨_, t, ht, v, hvu, htv⟩ := hc
    exact hb.2 t ht v hvu htv
  have hSum_n : S_A.card + S_B.card + S_C.card = n := by
    have h1 := Finset.card_union_of_disjoint hDisj_AB
    have h2 : Disjoint (S_A ∪ S_B) S_C := Finset.disjoint_union_left.mpr ⟨hDisj_AC, hDisj_BC⟩
    have h3 := Finset.card_union_of_disjoint h2
    rw [hPart_cover, Finset.card_univ, Fintype.card_fin] at h3
    omega
  have hB_pick : ∀ u ∈ S_B, ∃ t : Fin C.gates.length, t ∈ Readers u := fun u _ => hReadersNonempty u
  choose tb htb_mem using hB_pick
  let T_B : Finset (Fin C.gates.length) := S_B.attach.image (fun x => tb x.val x.property)
  have hTB_card : T_B.card = S_B.card := by
    rw [Finset.card_image_of_injective]
    · exact Finset.card_attach
    · intro ⟨u1, hu1⟩ ⟨u2, hu2⟩ heq
      dsimp only at heq
      apply Subtype.ext
      by_contra hne
      have h1 := (Finset.mem_filter.mp hu1).2.2 (tb u1 hu1) (htb_mem u1 hu1) u2 (Ne.symm hne)
      rw [heq] at h1
      exact h1 (htb_mem u2 hu2)
  have hTB_sub : T_B ⊆ AllReaders := by
    intro t ht
    obtain ⟨⟨u, hu⟩, _, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ u, htb_mem u hu⟩
  let T_other : Finset (Fin C.gates.length) := AllReaders \ T_B
  have hA_sub : ∀ u ∈ S_A, Readers u ⊆ T_other := by
    intro u huA t htU
    simp only [T_other, Finset.mem_sdiff]
    refine ⟨Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ u, htU⟩, ?_⟩
    intro htB
    obtain ⟨⟨w, hwB⟩, _, rfl⟩ := Finset.mem_image.mp htB
    have huw : u ≠ w := fun h => by subst h; exact Finset.disjoint_left.mp hDisj_AB huA hwB
    exact (Finset.mem_filter.mp hwB).2.2 (tb w hwB) (htb_mem w hwB) u huw htU
  have hInDeg : ∀ t : Fin C.gates.length, (S_A.filter (fun u => t ∈ Readers u)).card ≤ 2 := by
    intro t
    have ht_memC : gateAt C t.val ∈ C.gates := by
      rw [show gateAt C t.val = C.gates[t.val] from List.getD_eq_getElem _ _ t.isLt]
      exact List.getElem_mem t.isLt
    have hlen : (gateAt C t.val).inputs.length ≤ 2 := (hmono _ ht_memC).2
    let f : Fin n → ℕ := fun u => N + (ρ u).val
    have hfinj : Function.Injective f := fun a b h => hρ_inj (Fin.ext (by simp [f] at h; omega))
    have hsub : (S_A.filter (fun u => t ∈ Readers u)).image f ⊆ (gateAt C t.val).inputs.toFinset := by
      intro w hw
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      have htU := (Finset.mem_filter.mp hu).2
      have hmem := (Finset.mem_filter.mp htU).2
      exact List.mem_toFinset.mpr hmem
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hfinj] at h1
    have h2 : (gateAt C t.val).inputs.toFinset.card ≤ (gateAt C t.val).inputs.length :=
      List.toFinset_card_le _
    omega
  have hSA_le_Tother : S_A.card ≤ T_other.card := by
    have h1 : 2 * S_A.card ≤ ∑ u ∈ S_A, (Readers u).card := by
      calc 2 * S_A.card = ∑ _u ∈ S_A, 2 := by simp [mul_comm]
      _ ≤ ∑ u ∈ S_A, (Readers u).card := Finset.sum_le_sum (fun u hu => (Finset.mem_filter.mp hu).2)
    have h2 : ∑ u ∈ S_A, (Readers u).card =
        ∑ u ∈ S_A, ∑ t ∈ T_other, if t ∈ Readers u then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_boole, Nat.cast_id]
      congr 1
      ext t
      simp only [Finset.mem_filter]
      exact ⟨fun ht => ⟨hA_sub u hu ht, ht⟩, fun h => h.2⟩
    have h3 : ∑ u ∈ S_A, ∑ t ∈ T_other, (if t ∈ Readers u then 1 else 0) =
        ∑ t ∈ T_other, (S_A.filter (fun u => t ∈ Readers u)).card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.sum_boole, Nat.cast_id]
    have h4 : ∑ t ∈ T_other, (S_A.filter (fun u => t ∈ Readers u)).card ≤ 2 * T_other.card := by
      calc ∑ t ∈ T_other, (S_A.filter (fun u => t ∈ Readers u)).card
        _ ≤ ∑ _t ∈ T_other, 2 := Finset.sum_le_sum (fun t _ => hInDeg t)
        _ = 2 * T_other.card := by simp [mul_comm]
    omega
  have hAll_card : AllReaders.card = T_B.card + T_other.card := by
    have hsd : T_other.card + T_B.card = AllReaders.card :=
      Finset.card_sdiff_add_card_eq_card hTB_sub
    omega
  have hR_card : Rset.card = n := by
    rw [Finset.card_image_of_injective _ hρ_inj, Finset.card_univ, Fintype.card_fin]
  have hDisj_RA_GC : Disjoint (Rset ∪ AllReaders) G_C :=
    Finset.disjoint_union_left.mpr ⟨hDisj_GC_R.symm, hDisj_GC_A.symm⟩
  have hTot : (Rset ∪ AllReaders ∪ G_C).card ≤ C.size := by
    have h1 := Finset.card_le_univ (Rset ∪ AllReaders ∪ G_C)
    rw [Fintype.card_fin] at h1
    exact h1
  rw [Finset.card_union_of_disjoint hDisj_RA_GC, Finset.card_union_of_disjoint hDisj_R_All] at hTot
  omega

end PEqualNP.Outside.L_meta_25489_aux

theorem PEqualNP.Outside.L_meta_25489 : ∀ (n k : ℕ) (G : Fin n → Fin (2 * k) → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit),
  2 ≤ k →
  Function.Injective G →
  (∀ u, (Finset.univ.filter (fun c => G u c = true)).card = k) →
  (∀ c, ∃ v, G v c = false) →
  PEqualNP.MetaComplexity.Monotone2 C →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2 * k) C →
  PEqualNP.Represents.Represents G C →
  (∀ x : Fin n,
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) x.val = 1 ∧
    ∃ (j : Fin C.gates.length) (s : ℕ),
      (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      ((C.gates.get j).inputs = [x.val, s] ∨ (C.gates.get j).inputs = [s, x.val])) →
  2 * n ≤ C.size :=
  PEqualNP.Outside.L_meta_25489_aux.main_aux
