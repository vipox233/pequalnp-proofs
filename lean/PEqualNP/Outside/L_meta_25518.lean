import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25518_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (Monotone2 FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open PEqualNP.NotBracket (notCount)

private def paired {n : ℕ} (u v : Fin n) : List Bool :=
  List.ofFn (fun index : Fin n => decide (index = u ∨ index = v))

private def rawVec {n : ℕ} (T : Finset (Fin n)) (u : Fin n) : List Bool :=
  List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T))

private def inp {n : ℕ} (T : Finset (Fin n)) (u v : Fin n) : List Bool :=
  paired u v ++ rawVec T u

private theorem inp_len {n : ℕ} (T : Finset (Fin n)) (u v : Fin n) :
    (inp T u v).length = n + n := by
  simp [inp, paired, rawVec]

private theorem inp_getD_left {n : ℕ} (T : Finset (Fin n)) (u v i : Fin n) :
    (inp T u v).getD i.val false = decide (i = u ∨ i = v) := by
  unfold inp paired
  rw [List.getD_append _ _ _ _ (by simp [i.isLt])]
  rw [List.getD_eq_getElem _ _ (by simp [i.isLt]), List.getElem_ofFn]

private theorem inp_getD_right {n : ℕ} (T : Finset (Fin n)) (u v i : Fin n) :
    (inp T u v).getD (n + i.val) false = decide (i = u ∧ i ∈ T) := by
  unfold inp paired rawVec
  have hlen : (List.ofFn (fun index : Fin n => decide (index = u ∨ index = v))).length = n := by simp
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hlen, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simp [i.isLt]), List.getElem_ofFn]

private def stepFn (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_len (gs : List Gate) (x : List Bool) :
    (gs.foldl stepFn x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [stepFn, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem wires_getD_prefix (gs₁ gs₂ : List Gate) (x : List Bool) {w : ℕ}
    (hw : w < x.length + gs₁.length) :
    ((gs₁ ++ gs₂).foldl stepFn x).getD w false = (gs₁.foldl stepFn x).getD w false := by
  rw [List.foldl_append]
  have hlen : (gs₁.foldl stepFn x).length = x.length + gs₁.length := wires_len gs₁ x
  have hws : w < (gs₁.foldl stepFn x).length := by omega
  generalize hs : gs₁.foldl stepFn x = s at hws ⊢
  clear hs gs₁ x hw hlen
  induction gs₂ generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    rw [ih (stepFn s g) (by simp [stepFn]; omega)]
    exact List.getD_append _ _ _ _ hws

private theorem wires_getD_append_one (gs : List Gate) (g : Gate) (x : List Bool) :
    ((gs ++ [g]).foldl stepFn x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (gs.foldl stepFn x).getD i false) := by
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen := wires_len gs x
  change ((gs.foldl stepFn x) ++ [g.op.eval (g.inputs.map fun i => (gs.foldl stepFn x).getD i false)]).getD
    (x.length + gs.length) false = _
  rw [List.getD_append_right _ _ _ _ (by omega)]
  rw [hlen, Nat.sub_self, List.getD_cons_zero]

private def rawCount (n : ℕ) (gs : List Gate) (i : Fin n) : ℕ :=
  (gs.map (fun g => g.inputs.count (n + i.val))).sum

private theorem rawCount_append (n : ℕ) (gs₁ gs₂ : List Gate) (i : Fin n) :
    rawCount n (gs₁ ++ gs₂) i = rawCount n gs₁ i + rawCount n gs₂ i := by
  simp [rawCount, List.map_append, List.sum_append]

private def notCnt (gs : List Gate) : ℕ :=
  notCount ⟨gs, 0⟩

private theorem notCnt_append (gs₁ gs₂ : List Gate) :
    notCnt (gs₁ ++ gs₂) = notCnt gs₁ + notCnt gs₂ := by
  unfold notCnt notCount
  simp [List.filter_append, List.length_append]

private theorem notCnt_singleton_not (g : Gate) (h : g.op = GateOp.not) : notCnt [g] = 1 := by
  unfold notCnt notCount
  simp [h]

private theorem notCnt_singleton_ne (g : Gate) (h : g.op ≠ GateOp.not) : notCnt [g] = 0 := by
  unfold notCnt notCount
  simp [h]

private structure State (n : ℕ) (T : Finset (Fin n)) where
  gates : List Gate
  fan : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2
  reads : ReadsBack (n + n) ⟨gates, 0⟩
  notLen : ∀ g ∈ gates, g.op = GateOp.not → g.inputs.length = 1
  noOutT : ∀ i : Fin n, i ∉ T → ∀ g ∈ gates, n + i.val ∉ g.inputs

private def State.val {n : ℕ} {T : Finset (Fin n)} (S : State n T) (u v : Fin n) (w : ℕ) : Bool :=
  (S.gates.foldl stepFn (inp T u v)).getD w false

private theorem State.val_lt {n : ℕ} {T : Finset (Fin n)} (S : State n T) (u v : Fin n) (i : Fin n) :
    S.val u v i.val = decide (i = u ∨ i = v) := by
  unfold State.val
  have h := wires_getD_prefix [] S.gates (inp T u v) (w := i.val) (by rw [inp_len]; omega)
  exact h.trans (inp_getD_left T u v i)

private theorem State.val_raw {n : ℕ} {T : Finset (Fin n)} (S : State n T) (u v i : Fin n) :
    S.val u v (n + i.val) = decide (i = u ∧ i ∈ T) := by
  unfold State.val
  have h := wires_getD_prefix [] S.gates (inp T u v) (w := n + i.val) (by rw [inp_len]; omega)
  exact h.trans (inp_getD_right T u v i)

private def State.push {n : ℕ} {T : Finset (Fin n)} (S : State n T) (g : Gate)
    (hfan : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hr : ∀ w ∈ g.inputs, w < n + n + S.gates.length)
    (hnl : g.op = GateOp.not → g.inputs.length = 1)
    (hno : ∀ i : Fin n, i ∉ T → n + i.val ∉ g.inputs) : State n T :=
  { gates := S.gates ++ [g]
    fan := fun g' hg' => by
      rcases List.mem_append.mp hg' with h | h
      · exact S.fan g' h
      · rw [List.mem_singleton.mp h]; exact hfan
    reads := fun j hj w hw => by
      change j < (S.gates ++ [g]).length at hj
      change w ∈ ((S.gates ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at hw
      by_cases hlt : j < S.gates.length
      · rw [List.getD_append _ _ _ _ hlt] at hw
        exact S.reads j hlt w hw
      · have heq : j = S.gates.length := by simp at hj; omega
        subst heq
        rw [List.getD_append_right _ _ _ _ le_rfl] at hw
        simp only [Nat.sub_self, List.getD_cons_zero] at hw
        exact hr w hw
    notLen := fun g' hg' hop => by
      rcases List.mem_append.mp hg' with h | h
      · exact S.notLen g' h hop
      · rw [List.mem_singleton.mp h] at hop ⊢; exact hnl hop
    noOutT := fun i hi g' hg' => by
      rcases List.mem_append.mp hg' with h | h
      · exact S.noOutT i hi g' h
      · rw [List.mem_singleton.mp h]; exact hno i hi }

private theorem State.push_val_old {n : ℕ} {T : Finset (Fin n)} (S : State n T) (g : Gate)
    (hfan hr hnl hno) (u v : Fin n) {w : ℕ} (hw : w < n + n + S.gates.length) :
    (S.push g hfan hr hnl hno).val u v w = S.val u v w := by
  unfold State.val State.push
  exact wires_getD_prefix S.gates [g] (inp T u v) (by rw [inp_len]; exact hw)

private theorem State.push_val_new {n : ℕ} {T : Finset (Fin n)} (S : State n T) (g : Gate)
    (hfan hr hnl hno) (u v : Fin n) :
    (S.push g hfan hr hnl hno).val u v (n + n + S.gates.length) =
      g.op.eval (g.inputs.map fun w => S.val u v w) := by
  unfold State.val State.push
  have h := wires_getD_append_one S.gates g (inp T u v)
  rw [inp_len] at h
  exact h

private def reloc (n w : ℕ) : ℕ := if w < n then w else w + n

private theorem reloc_ne_raw {n w : ℕ} (i : Fin n) : reloc n w ≠ n + i.val := by
  unfold reloc
  split_ifs <;> omega

private theorem reloc_lt {n j w : ℕ} (hw : w < n + j) : reloc n w < n + n + j := by
  unfold reloc
  split_ifs <;> omega

private def initFromD {n : ℕ} (T : Finset (Fin n)) (D : Circuit)
    (hM : Monotone2 D) (hR : ReadsBack n D) : State n T :=
  { gates := D.gates.map (fun g => ⟨g.op, g.inputs.map (reloc n)⟩)
    fan := fun g' hg' => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
      obtain ⟨hop, hlen⟩ := hM g hg
      refine ⟨?_, by simpa using hlen⟩
      rcases hop with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    reads := fun j hj w hw => by
      change j < (D.gates.map (fun g => ({ op := g.op, inputs := g.inputs.map (reloc n) } : Gate))).length at hj
      rw [List.length_map] at hj
      change w ∈ ((D.gates.map (fun g => ({ op := g.op, inputs := g.inputs.map (reloc n) } : Gate))).getD j ⟨GateOp.or, []⟩).inputs at hw
      rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map] at hw
      obtain ⟨w₀, hw₀, rfl⟩ := List.mem_map.mp hw
      have hrb := hR j hj w₀
      unfold gateAt at hrb
      rw [List.getD_eq_getElem _ _ hj] at hrb
      exact reloc_lt (hrb hw₀)
    notLen := fun g' hg' hop => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
      obtain ⟨hgm, _⟩ := hM g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgm
      rcases hgm with h | h <;> simp [h] at hop
    noOutT := fun i _ g' hg' hmem => by
      obtain ⟨g, _, rfl⟩ := List.mem_map.mp hg'
      obtain ⟨w₀, _, hw₀⟩ := List.mem_map.mp hmem
      exact reloc_ne_raw i hw₀ }

private theorem initFromD_notCnt {n : ℕ} (T : Finset (Fin n)) (D : Circuit)
    (hM : Monotone2 D) (hR : ReadsBack n D) : notCnt (initFromD T D hM hR).gates = 0 := by
  unfold notCnt notCount initFromD
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro g' hg'
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg'
  obtain ⟨hgm, _⟩ := hM g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgm
  rcases hgm with h | h <;> simp [h]

private theorem initFromD_rawCount {n : ℕ} (T : Finset (Fin n)) (D : Circuit)
    (hM : Monotone2 D) (hR : ReadsBack n D) (i : Fin n) :
    rawCount n (initFromD T D hM hR).gates i = 0 := by
  unfold rawCount initFromD
  apply List.sum_eq_zero
  intro c hc
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hc
  obtain ⟨g, _, rfl⟩ := List.mem_map.mp hg'
  rw [List.count_eq_zero]
  intro hmem
  obtain ⟨w₀, _, hw₀⟩ := List.mem_map.mp hmem
  exact reloc_ne_raw i hw₀

private theorem initFromD_val {n : ℕ} (T : Finset (Fin n)) (D : Circuit)
    (hM : Monotone2 D) (hR : ReadsBack n D) (u v : Fin n) {w : ℕ} (hw : w < n + D.gates.length) :
    (initFromD T D hM hR).val u v (reloc n w) = (D.wires (paired u v)).getD w false := by
  unfold State.val initFromD Circuit.wires
  change ((D.gates.map (fun g => ⟨g.op, g.inputs.map (reloc n)⟩)).foldl stepFn (inp T u v)).getD (reloc n w) false =
    (D.gates.foldl stepFn (paired u v)).getD w false
  have hstep (k : ℕ) (hk : k ≤ D.gates.length) :
      ∀ w < n + k,
        (((D.gates.take k).map (fun g => ⟨g.op, g.inputs.map (reloc n)⟩)).foldl stepFn (inp T u v)).getD (reloc n w) false =
          ((D.gates.take k).foldl stepFn (paired u v)).getD w false := by
    induction k with
    | zero =>
      intro w hw0
      simp only [List.take_zero, List.map_nil, List.foldl_nil]
      have hwn : w < n := by omega
      have hrw : reloc n w = w := if_pos hwn
      rw [hrw]
      have h1 := inp_getD_left T u v ⟨w, hwn⟩
      unfold paired
      rw [h1, List.getD_eq_getElem _ _ (by simp [hwn]), List.getElem_ofFn]
    | succ k ih =>
      have hk' : k < D.gates.length := by omega
      have htake : D.gates.take (k + 1) = D.gates.take k ++ [D.gates[k]] :=
        List.take_succ_eq_append_getElem hk'
      let g := D.gates[k]
      let g' : Gate := ⟨g.op, g.inputs.map (reloc n)⟩
      have htake_map : (D.gates.take (k + 1)).map (fun g => ⟨g.op, g.inputs.map (reloc n)⟩) =
          (D.gates.take k).map (fun g => ⟨g.op, g.inputs.map (reloc n)⟩) ++ [g'] := by
        rw [htake, List.map_append, List.map_singleton]
      intro w hw1
      by_cases hlt : w < n + k
      · rw [htake_map, htake]
        have hL := wires_getD_prefix ((D.gates.take k).map (fun g => ⟨g.op, g.inputs.map (reloc n)⟩)) [g']
          (inp T u v) (w := reloc n w) (by rw [inp_len, List.length_map, List.length_take, Nat.min_eq_left (by omega)]; exact reloc_lt hlt)
        have hR' := wires_getD_prefix (D.gates.take k) [g] (paired u v) (w := w)
          (by simp only [paired, List.length_ofFn, List.length_take]; rw [Nat.min_eq_left (by omega)]; exact hlt)
        rw [hL, hR']
        exact ih (by omega) w hlt
      · obtain rfl : w = n + k := by omega
        have hrw : reloc n (n + k) = n + n + k := by
          unfold reloc; rw [if_neg (by omega)]; omega
        rw [hrw, htake_map, htake]
        have hL := wires_getD_append_one ((D.gates.take k).map (fun g => ⟨g.op, g.inputs.map (reloc n)⟩)) g' (inp T u v)
        rw [inp_len, List.length_map, List.length_take, Nat.min_eq_left (by omega)] at hL
        have hR' := wires_getD_append_one (D.gates.take k) g (paired u v)
        have hplen : (paired u v).length = n := by simp [paired]
        rw [hplen, List.length_take, Nat.min_eq_left (by omega)] at hR'
        rw [hL, hR']
        dsimp [g']
        congr 1
        rw [List.map_map]
        apply List.map_congr_left
        intro w₀ hw₀
        have hrb := hR k hk' w₀
        unfold gateAt at hrb
        rw [List.getD_eq_getElem _ _ hk'] at hrb
        exact ih (by omega) w₀ (hrb hw₀)
  have hfull := hstep D.gates.length le_rfl w hw
  rwa [List.take_length] at hfull

private theorem build_or_list {n : ℕ} {T : Finset (Fin n)} (S : State n T) (ws : List ℕ)
    (hne : ws ≠ [])
    (hws : ∀ w ∈ ws, w < n + n + S.gates.length)
    (hno : ∀ w ∈ ws, ∀ i : Fin n, i ∉ T → w ≠ n + i.val) :
    ∃ (S' : State n T) (out : ℕ),
      S'.gates.length = S.gates.length + (ws.length - 1) ∧
      notCnt S'.gates = notCnt S.gates ∧
      (∀ i : Fin n, rawCount n S'.gates i + (if out = n + i.val then 1 else 0) ≤
        rawCount n S.gates i + ws.count (n + i.val)) ∧
      (ws.length ≥ 2 → n + n + S.gates.length ≤ out) ∧
      (∀ i : Fin n, (∀ w ∈ ws, w ≠ n + i.val) → out ≠ n + i.val) ∧
      out < n + n + S'.gates.length ∧
      (∀ i : Fin n, i ∉ T → out ≠ n + i.val) ∧
      (∀ u v w, w < n + n + S.gates.length → S'.val u v w = S.val u v w) ∧
      (∀ u v, S'.val u v out = ws.any (fun w => S.val u v w)) := by
  induction ws generalizing S with
  | nil => exact (hne rfl).elim
  | cons a rest ih =>
    cases rest with
    | nil =>
      refine ⟨S, a, by simp, rfl, fun i => by
          by_cases ha : a = n + i.val <;> simp [ha, beq_iff_eq],
        fun h => by simp at h,
        fun i hi => hi a List.mem_cons_self,
        hws a List.mem_cons_self, hno a List.mem_cons_self, fun _ _ _ _ => rfl, fun u v => by simp⟩
    | cons b rest' =>
      cases rest' with
      | nil =>
        let g : Gate := ⟨GateOp.or, [a, b]⟩
        have hfan : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 :=
          ⟨Or.inr (Or.inl rfl), by simp [g]⟩
        have hrg : ∀ w ∈ g.inputs, w < n + n + S.gates.length := by
          intro w hw
          simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · exact hws _ (by simp)
          · exact hws _ (by simp)
        have hnl : g.op = GateOp.not → g.inputs.length = 1 := by simp [g]
        have hnog : ∀ i : Fin n, i ∉ T → n + i.val ∉ g.inputs := by
          intro i hi hmem
          simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with h | h
          · exact hno a (by simp) i hi h.symm
          · exact hno b (by simp) i hi h.symm
        let S' := S.push g hfan hrg hnl hnog
        let out := n + n + S.gates.length
        refine ⟨S', out, by simp [S', State.push],
          by unfold S' State.push; rw [notCnt_append, notCnt_singleton_ne g (by simp [g]), Nat.add_zero],
          fun i => by
            unfold S' State.push
            rw [rawCount_append]
            have hne_out : out ≠ n + i.val := by dsimp [out]; omega
            simp [rawCount, g, hne_out],
          fun _ => le_rfl,
          fun i _ h => by dsimp [out] at h; omega,
          by simp [S', State.push, out],
          fun i _ h => by dsimp [out] at h; omega,
          fun u v w hw => State.push_val_old _ _ _ _ _ _ u v hw,
          fun u v => by
            rw [State.push_val_new]
            simp [g, GateOp.eval]⟩
      | cons c cs =>
        obtain ⟨S₁, o₁, hlen₁, hnot₁, hraw₁, hge₁, _, ho₁, hno₁, hold₁, hval₁⟩ :=
          ih S (List.cons_ne_nil b (c :: cs))
            (fun w hw => hws w (List.mem_cons_of_mem a hw))
            (fun w hw => hno w (List.mem_cons_of_mem a hw))
        let g : Gate := ⟨GateOp.or, [a, o₁]⟩
        have hfan : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 :=
          ⟨Or.inr (Or.inl rfl), by simp [g]⟩
        have hrg : ∀ w ∈ g.inputs, w < n + n + S₁.gates.length := by
          intro w hw
          simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · have := hws _ List.mem_cons_self; omega
          · exact ho₁
        have hnl : g.op = GateOp.not → g.inputs.length = 1 := by simp [g]
        have hnog : ∀ i : Fin n, i ∉ T → n + i.val ∉ g.inputs := by
          intro i hi hmem
          simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with h | h
          · exact hno a List.mem_cons_self i hi h.symm
          · exact hno₁ i hi h.symm
        let S₂ := S₁.push g hfan hrg hnl hnog
        let out := n + n + S₁.gates.length
        have ho₁_ne_raw (i : Fin n) : o₁ ≠ n + i.val := by
          have := hge₁ (by simp)
          omega
        refine ⟨S₂, out, by unfold S₂ State.push; simp [hlen₁]; omega,
          by unfold S₂ State.push; rw [notCnt_append, hnot₁, notCnt_singleton_ne g (by simp [g]), Nat.add_zero],
          fun i => by
            unfold S₂ State.push
            rw [rawCount_append]
            have h1 := hraw₁ i
            have hne_out : out ≠ n + i.val := by dsimp [out]; omega
            have hg_cnt : g.inputs.count (n + i.val) = if a = n + i.val then 1 else 0 := by
              dsimp [g]
              by_cases ha : a = n + i.val
              · simp [ha, ho₁_ne_raw i, Ne.symm (ho₁_ne_raw i)]
              · simp [ha, ho₁_ne_raw i, Ne.symm (ho₁_ne_raw i)]
            have hrc : rawCount n [g] i = g.inputs.count (n + i.val) := by simp [rawCount]
            rw [hrc, hg_cnt, if_neg hne_out]
            have hcons : (a :: b :: c :: cs).count (n + i.val) =
                (b :: c :: cs).count (n + i.val) + if a = n + i.val then 1 else 0 := by
              rw [List.count_cons]
              by_cases ha : a = n + i.val <;> simp [ha, beq_iff_eq]
            omega,
          fun _ => by dsimp [out]; omega,
          fun i _ h => by dsimp [out] at h; omega,
          by simp [S₂, State.push, out],
          fun i _ h => by dsimp [out] at h; omega,
          fun u v w hw => by
            rw [State.push_val_old _ _ _ _ _ _ u v (by omega)]
            exact hold₁ u v w hw,
          fun u v => by
            rw [State.push_val_new]
            simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id, Bool.or_false]
            rw [hold₁ u v a (hws a List.mem_cons_self), hval₁ u v]
            rfl⟩

private theorem build_src_groups {n : ℕ} (G : Fin n → Fin n → Bool) (T : Finset (Fin n))
    (S : State n T) (srcList : List (Fin n)) (hnodup : srcList.Nodup)
    (hsubT : ∀ i ∈ srcList, i ∈ T)
    (hnonempty : ∀ i ∈ srcList, (Finset.univ.filter (fun j : Fin n => G i j = true ∧ G j i = false)).Nonempty) :
    ∃ (S' : State n T) (outs : List ℕ),
      outs.length = srcList.length ∧
      S'.gates.length = S.gates.length +
        (srcList.map (fun i => (Finset.univ.filter (fun j : Fin n => G i j = true ∧ G j i = false)).card)).sum ∧
      notCnt S'.gates = notCnt S.gates ∧
      (∀ i : Fin n, rawCount n S'.gates i ≤ rawCount n S.gates i + if i ∈ srcList then 1 else 0) ∧
      (∀ w ∈ outs, n + n + S.gates.length ≤ w ∧ w < n + n + S'.gates.length) ∧
      (∀ u v w, w < n + n + S.gates.length → S'.val u v w = S.val u v w) ∧
      (∀ u v, outs.any (fun w => S'.val u v w) =
        decide (∃ i ∈ srcList, u = i ∧ G i v = true ∧ G v i = false)) := by
  induction srcList generalizing S with
  | nil =>
    refine ⟨S, [], rfl, by simp, rfl, fun i => by simp, by simp, fun _ _ _ _ => rfl, fun u v => by simp⟩
  | cons i rest ih =>
    have hnd := List.nodup_cons.mp hnodup
    have hiT : i ∈ T := hsubT i List.mem_cons_self
    let jsFin := Finset.univ.filter (fun j : Fin n => G i j = true ∧ G j i = false)
    have hjs_ne : jsFin.Nonempty := hnonempty i List.mem_cons_self
    let jsList : List (Fin n) := jsFin.toList
    have hjs_len : jsList.length = jsFin.card := Finset.length_toList jsFin
    have hjs_ne' : jsList ≠ [] := by
      intro h; rw [h] at hjs_len; exact (Finset.card_pos.mpr hjs_ne).ne hjs_len
    let ws : List ℕ := jsList.map Fin.val
    have hws_ne : ws ≠ [] := by simp [ws, hjs_ne']
    have hws_lt : ∀ w ∈ ws, w < n + n + S.gates.length := by
      intro w hw; obtain ⟨j, _, rfl⟩ := List.mem_map.mp hw; omega
    have hws_no_raw : ∀ w ∈ ws, ∀ r : Fin n, w ≠ n + r.val := by
      intro w hw r; obtain ⟨j, _, rfl⟩ := List.mem_map.mp hw; omega
    have hws_cnt (r : Fin n) : ws.count (n + r.val) = 0 := by
      rw [List.count_eq_zero]; intro hmem; obtain ⟨j, _, hj⟩ := List.mem_map.mp hmem; omega
    obtain ⟨S₁, o₁, hlen₁, hnot₁, hraw₁, _, ho₁_ne_raw_all, ho₁, hno₁, hold₁, hval₁⟩ :=
      build_or_list S ws hws_ne hws_lt (fun w hw r _ => hws_no_raw w hw r)
    have ho₁_ne_raw (r : Fin n) : o₁ ≠ n + r.val := ho₁_ne_raw_all r (fun w hw => hws_no_raw w hw r)
    let g : Gate := ⟨GateOp.and, [n + i.val, o₁]⟩
    have hfan : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 :=
      ⟨Or.inl rfl, by simp [g]⟩
    have hrg : ∀ w ∈ g.inputs, w < n + n + S₁.gates.length := by
      intro w hw
      simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · omega
      · exact ho₁
    have hnl : g.op = GateOp.not → g.inputs.length = 1 := by simp [g]
    have hnog : ∀ r : Fin n, r ∉ T → n + r.val ∉ g.inputs := by
      intro r hr hmem
      simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h
      · exact hr (by have : r = i := Fin.ext (by omega); subst this; exact hiT)
      · exact hno₁ r hr h.symm
    let S₂ := S₁.push g hfan hrg hnl hnog
    let w_i := n + n + S₁.gates.length
    obtain ⟨S₃, outs_rest, hout_len, hlen₃, hnot₃, hraw₃, houts_b, hold₃, hval₃⟩ :=
      ih S₂ hnd.2 (fun r hr => hsubT r (List.mem_cons_of_mem i hr))
        (fun r hr => hnonempty r (List.mem_cons_of_mem i hr))
    have hwi_val (u v : Fin n) : S₂.val u v w_i = decide (u = i ∧ G i v = true ∧ G v i = false) := by
      rw [State.push_val_new]
      simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
      rw [S₁.val_raw u v i, hval₁ u v]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq, ws, List.any_eq_true, List.mem_map]
      constructor
      · rintro ⟨⟨hiu, _⟩, _, ⟨j, hj, rfl⟩, hjv⟩
        have hj' : G i j = true ∧ G j i = false := by
          have := Finset.mem_toList.mp hj; simpa [jsFin] using this
        rw [S.val_lt u v j, decide_eq_true_eq] at hjv
        subst hiu
        rcases hjv with rfl | rfl
        · exact absurd hj'.1 (by rw [hj'.2]; decide)
        · exact ⟨rfl, hj'⟩
      · rintro ⟨rfl, h1, h2⟩
        refine ⟨⟨rfl, hiT⟩, v.val, ⟨v, Finset.mem_toList.mpr (by simp [jsFin, h1, h2]), rfl⟩, ?_⟩
        rw [S.val_lt u v v, decide_eq_true_eq]; exact Or.inr rfl
    refine ⟨S₃, w_i :: outs_rest, by simp [hout_len], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hlen₃]
      have h2 : S₂.gates.length = S.gates.length + jsFin.card := by
        unfold S₂ State.push
        have hwslen : ws.length = jsFin.card := by simp [ws, hjs_len]
        have hpos : 1 ≤ jsFin.card := Finset.card_pos.mpr hjs_ne
        simp [hlen₁, hwslen]; omega
      dsimp [jsFin] at h2
      rw [h2]; simp; omega
    · rw [hnot₃]; unfold S₂ State.push; rw [notCnt_append, hnot₁, notCnt_singleton_ne g (by simp [g]), Nat.add_zero]
    · intro r
      have h3 := hraw₃ r
      have h2 : rawCount n S₂.gates r ≤ rawCount n S.gates r + if r = i then 1 else 0 := by
        unfold S₂ State.push
        rw [rawCount_append]
        have h1 := hraw₁ r
        rw [hws_cnt r] at h1
        have hg_cnt : rawCount n [g] r = if r = i then 1 else 0 := by
          simp only [rawCount, g, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
          by_cases hri : r = i
          · subst hri; simp [ho₁_ne_raw r, Ne.symm (ho₁_ne_raw r)]
          · have hne' : r.val ≠ i.val := fun h => hri (Fin.ext h)
            rw [if_neg hri]
            exact List.count_eq_zero.mpr (by simp [hne', Ne.symm (ho₁_ne_raw r)])
        omega
      by_cases hri : r = i
      · subst hri; simp [hnd.1] at h2 h3 ⊢; omega
      · simp [hri] at h2 h3 ⊢; omega
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · refine ⟨by dsimp [w_i]; omega, ?_⟩
        have : S₂.gates.length ≤ S₃.gates.length := by omega
        unfold S₂ State.push at this; dsimp [w_i]; simp at this; omega
      · obtain ⟨h1, h2⟩ := houts_b w hw
        have : S.gates.length ≤ S₂.gates.length := by unfold S₂ State.push; simp [hlen₁]; omega
        exact ⟨by omega, h2⟩
    · intro u v w hw
      rw [hold₃ u v w (by unfold S₂ State.push; simp [hlen₁]; omega),
        State.push_val_old _ _ _ _ _ _ u v (by omega), hold₁ u v w hw]
    · intro u v
      simp only [List.any_cons]
      rw [hold₃ u v w_i (by unfold S₂ State.push; simp [w_i]), hwi_val u v, hval₃ u v]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro (⟨rfl, h1, h2⟩ | ⟨r, hr, rfl, h1, h2⟩)
        · exact ⟨u, Or.inl rfl, rfl, h1, h2⟩
        · exact ⟨u, Or.inr hr, rfl, h1, h2⟩
      · rintro ⟨r, (rfl | hr), rfl, h1, h2⟩
        · exact Or.inl ⟨rfl, h1, h2⟩
        · exact Or.inr ⟨u, hr, rfl, h1, h2⟩

private theorem build_tgt_groups {n : ℕ} (G : Fin n → Fin n → Bool) (T : Finset (Fin n))
    (S : State n T) (tgtList : List (Fin n)) (hnodup : tgtList.Nodup)
    (hnonempty : ∀ j ∈ tgtList, (Finset.univ.filter (fun i : Fin n => i ∉ T ∧ G i j = true ∧ G j i = false)).Nonempty) :
    ∃ (S' : State n T) (outs : List ℕ),
      outs.length = tgtList.length ∧
      S'.gates.length = S.gates.length +
        (tgtList.map (fun j => (Finset.univ.filter (fun i : Fin n => i ∉ T ∧ G i j = true ∧ G j i = false)).card)).sum ∧
      notCnt S'.gates = notCnt S.gates ∧
      (∀ i : Fin n, rawCount n S'.gates i ≤ rawCount n S.gates i) ∧
      (∀ w ∈ outs, n + n + S.gates.length ≤ w ∧ w < n + n + S'.gates.length) ∧
      (∀ u v w, w < n + n + S.gates.length → S'.val u v w = S.val u v w) ∧
      (∀ u v, outs.any (fun w => S'.val u v w) =
        decide (∃ j ∈ tgtList, (j = u ∨ j = v) ∧
          ∃ i : Fin n, (i = u ∨ i = v) ∧ i ∉ T ∧ G i j = true ∧ G j i = false)) := by
  induction tgtList generalizing S with
  | nil =>
    refine ⟨S, [], rfl, by simp, rfl, fun _ => le_rfl, by simp, fun _ _ _ _ => rfl, fun u v => by simp⟩
  | cons j rest ih =>
    have hnd := List.nodup_cons.mp hnodup
    let isFin := Finset.univ.filter (fun i : Fin n => i ∉ T ∧ G i j = true ∧ G j i = false)
    have his_ne : isFin.Nonempty := hnonempty j List.mem_cons_self
    let isList : List (Fin n) := isFin.toList
    have his_len : isList.length = isFin.card := Finset.length_toList isFin
    have his_ne' : isList ≠ [] := by
      intro h; rw [h] at his_len; exact (Finset.card_pos.mpr his_ne).ne his_len
    let ws : List ℕ := isList.map Fin.val
    have hws_ne : ws ≠ [] := by simp [ws, his_ne']
    have hws_lt : ∀ w ∈ ws, w < n + n + S.gates.length := by
      intro w hw; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw; omega
    have hws_no_raw : ∀ w ∈ ws, ∀ r : Fin n, w ≠ n + r.val := by
      intro w hw r; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hw; omega
    have hws_cnt (r : Fin n) : ws.count (n + r.val) = 0 := by
      rw [List.count_eq_zero]; intro hmem; obtain ⟨i, _, hi⟩ := List.mem_map.mp hmem; omega
    obtain ⟨S₁, o₁, hlen₁, hnot₁, hraw₁, _, ho₁_ne_raw_all, ho₁, hno₁, hold₁, hval₁⟩ :=
      build_or_list S ws hws_ne hws_lt (fun w hw r _ => hws_no_raw w hw r)
    have ho₁_ne_raw (r : Fin n) : o₁ ≠ n + r.val := ho₁_ne_raw_all r (fun w hw => hws_no_raw w hw r)
    let g : Gate := ⟨GateOp.and, [j.val, o₁]⟩
    have hfan : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 :=
      ⟨Or.inl rfl, by simp [g]⟩
    have hrg : ∀ w ∈ g.inputs, w < n + n + S₁.gates.length := by
      intro w hw
      simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · omega
      · exact ho₁
    have hnl : g.op = GateOp.not → g.inputs.length = 1 := by simp [g]
    have hnog : ∀ r : Fin n, r ∉ T → n + r.val ∉ g.inputs := by
      intro r hr hmem
      simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h
      · omega
      · exact hno₁ r hr h.symm
    let S₂ := S₁.push g hfan hrg hnl hnog
    let w_j := n + n + S₁.gates.length
    obtain ⟨S₃, outs_rest, hout_len, hlen₃, hnot₃, hraw₃, houts_b, hold₃, hval₃⟩ :=
      ih S₂ hnd.2 (fun r hr => hnonempty r (List.mem_cons_of_mem j hr))
    have hwj_val (u v : Fin n) : S₂.val u v w_j =
        decide ((j = u ∨ j = v) ∧ ∃ i : Fin n, (i = u ∨ i = v) ∧ i ∉ T ∧ G i j = true ∧ G j i = false) := by
      rw [State.push_val_new]
      simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
      rw [S₁.val_lt u v j, hval₁ u v]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq, ws, List.any_eq_true, List.mem_map]
      constructor
      · rintro ⟨hjuv, _, ⟨i, hi, rfl⟩, hiuv⟩
        have hi' : i ∉ T ∧ G i j = true ∧ G j i = false := by
          have := Finset.mem_toList.mp hi; simpa [isFin] using this
        rw [S.val_lt u v i, decide_eq_true_eq] at hiuv
        exact ⟨hjuv, i, hiuv, hi'⟩
      · rintro ⟨hjuv, i, hiuv, hiT, h1, h2⟩
        refine ⟨hjuv, i.val, ⟨i, Finset.mem_toList.mpr (by simp [isFin, hiT, h1, h2]), rfl⟩, ?_⟩
        rw [S.val_lt u v i, decide_eq_true_eq]; exact hiuv
    refine ⟨S₃, w_j :: outs_rest, by simp [hout_len], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hlen₃]
      have h2 : S₂.gates.length = S.gates.length + isFin.card := by
        unfold S₂ State.push
        have hwslen : ws.length = isFin.card := by simp [ws, his_len]
        have hpos : 1 ≤ isFin.card := Finset.card_pos.mpr his_ne
        simp [hlen₁, hwslen]; omega
      dsimp [isFin] at h2
      rw [h2]; simp; omega
    · rw [hnot₃]; unfold S₂ State.push; rw [notCnt_append, hnot₁, notCnt_singleton_ne g (by simp [g]), Nat.add_zero]
    · intro r
      have h3 := hraw₃ r
      have h2 : rawCount n S₂.gates r ≤ rawCount n S.gates r := by
        unfold S₂ State.push
        rw [rawCount_append]
        have h1 := hraw₁ r
        rw [hws_cnt r, Nat.add_zero] at h1
        have hg_cnt : rawCount n [g] r = 0 := by
          simp only [rawCount, g, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
          have hne1 : j.val ≠ n + r.val := by omega
          simp [hne1, Ne.symm hne1, ho₁_ne_raw r, Ne.symm (ho₁_ne_raw r)]
        omega
      omega
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · refine ⟨by dsimp [w_j]; omega, ?_⟩
        have : S₂.gates.length ≤ S₃.gates.length := by omega
        unfold S₂ State.push at this; dsimp [w_j]; simp at this; omega
      · obtain ⟨h1, h2⟩ := houts_b w hw
        have : S.gates.length ≤ S₂.gates.length := by unfold S₂ State.push; simp [hlen₁]; omega
        exact ⟨by omega, h2⟩
    · intro u v w hw
      rw [hold₃ u v w (by unfold S₂ State.push; simp [hlen₁]; omega),
        State.push_val_old _ _ _ _ _ _ u v (by omega), hold₁ u v w hw]
    · intro u v
      simp only [List.any_cons]
      rw [hold₃ u v w_j (by unfold S₂ State.push; simp [w_j]), hwj_val u v, hval₃ u v]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro (h | ⟨r, hr, h⟩)
        · exact ⟨j, Or.inl rfl, h⟩
        · exact ⟨r, Or.inr hr, h⟩
      · rintro ⟨r, (rfl | hr), h⟩
        · exact Or.inl h
        · exact Or.inr ⟨r, hr, h⟩

private theorem sum_asym_split {n : ℕ} (G : Fin n → Fin n → Bool) (T : Finset (Fin n))
    (hT : ∀ i j, G i j = true → G j i = false → i ∈ T ∨ j ∈ T) :
    let srcFin := T.filter (fun i => (Finset.univ.filter (fun j : Fin n => G i j = true ∧ G j i = false)).Nonempty)
    let tgtFin := T.filter (fun j => (Finset.univ.filter (fun i : Fin n => i ∉ T ∧ G i j = true ∧ G j i = false)).Nonempty)
    let a := (Finset.univ.filter (fun p : Fin n × Fin n => G p.1 p.2 = true ∧ G p.2 p.1 = false)).card
    (∑ i ∈ srcFin, (Finset.univ.filter (fun j : Fin n => G i j = true ∧ G j i = false)).card) +
    (∑ j ∈ tgtFin, (Finset.univ.filter (fun i : Fin n => i ∉ T ∧ G i j = true ∧ G j i = false)).card) = a ∧
    srcFin.card + tgtFin.card ≤ min a (2 * T.card) := by
  intro srcFin tgtFin a
  let Asym := Finset.univ.filter (fun p : Fin n × Fin n => G p.1 p.2 = true ∧ G p.2 p.1 = false)
  let AsymS := Asym.filter (fun p => p.1 ∈ T)
  let AsymT := Asym.filter (fun p => p.1 ∉ T)
  have hpart : AsymS.card + AsymT.card = a := by
    have hu : AsymS ∪ AsymT = Asym := by
      ext p; simp only [AsymS, AsymT, Finset.mem_union, Finset.mem_filter]; by_cases h : p.1 ∈ T <;> simp [h]
    have hd : Disjoint AsymS AsymT := by
      rw [Finset.disjoint_left]; intro p h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    rw [← Finset.card_union_of_disjoint hd, hu]
  have hS : ∑ i ∈ srcFin, (Finset.univ.filter (fun j : Fin n => G i j = true ∧ G j i = false)).card = AsymS.card := by
    rw [← Finset.card_sigma]
    apply Finset.card_bij (fun q _ => (q.1, q.2))
    · intro q hq
      simp only [Finset.mem_sigma, srcFin, AsymS, Asym, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact ⟨hq.2, hq.1.1⟩
    · intro q₁ _ q₂ _ h
      cases q₁; cases q₂; simp only [Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩; rfl
    · intro p hp
      simp only [AsymS, Asym, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      refine ⟨⟨p.1, p.2⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, srcFin, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨hp.2, ⟨p.2, by simp [hp.1]⟩⟩, hp.1⟩
  have hTsum : ∑ j ∈ tgtFin, (Finset.univ.filter (fun i : Fin n => i ∉ T ∧ G i j = true ∧ G j i = false)).card = AsymT.card := by
    rw [← Finset.card_sigma]
    apply Finset.card_bij (fun q _ => (q.2, q.1))
    · intro q hq
      simp only [Finset.mem_sigma, tgtFin, AsymT, Asym, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      exact ⟨hq.2.2, hq.2.1⟩
    · intro q₁ _ q₂ _ h
      cases q₁; cases q₂; simp only [Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩; rfl
    · intro p hp
      simp only [AsymT, Asym, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have hp2T : p.2 ∈ T := (hT p.1 p.2 hp.1.1 hp.1.2).resolve_left hp.2
      refine ⟨⟨p.2, p.1⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, tgtFin, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨hp2T, ⟨p.1, by simp [hp.2, hp.1]⟩⟩, hp.2, hp.1⟩
  have hScard : srcFin.card ≤ AsymS.card := by
    rw [← hS]
    calc
      srcFin.card = ∑ _i ∈ srcFin, 1 := by simp
      _ ≤ ∑ i ∈ srcFin, (Finset.univ.filter (fun j : Fin n => G i j = true ∧ G j i = false)).card := by
        apply Finset.sum_le_sum
        intro i hi
        exact Finset.card_pos.mpr (Finset.mem_filter.mp hi).2
  have hTcard : tgtFin.card ≤ AsymT.card := by
    rw [← hTsum]
    calc
      tgtFin.card = ∑ _j ∈ tgtFin, 1 := by simp
      _ ≤ ∑ j ∈ tgtFin, (Finset.univ.filter (fun i : Fin n => i ∉ T ∧ G i j = true ∧ G j i = false)).card := by
        apply Finset.sum_le_sum
        intro j hj
        exact Finset.card_pos.mpr (Finset.mem_filter.mp hj).2
  have hS_le_T : srcFin.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hT_le_T : tgtFin.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
  refine ⟨by omega, le_min (by omega) (by omega)⟩

private theorem main_construct (n : ℕ) (G : Fin n → Fin n → Bool) (T : Finset (Fin n)) (D : Circuit)
    (hM : Monotone2 D) (hR : ReadsBack n D)
    (hD : ∀ u v, D.eval (paired u v) = (G u v && G v u))
    (hT : ∀ i j, G i j = true → G j i = false → i ∈ T ∨ j ∈ T) :
    let a := (Finset.univ.filter (fun p : Fin n × Fin n => G p.1 p.2 = true ∧ G p.2 p.1 = false)).card
    ∃ E : Circuit,
      FanInTwo E ∧
      ReadsBack (n + n) E ∧
      notCount E ≤ 1 ∧
      (∀ g ∈ E.gates, g.op = .not → g.inputs.length = 1) ∧
      E.output < (n + n) + E.size ∧
      E.size ≤ D.size + a + min a (2 * T.card) + T.card + 1 ∧
      (∀ i : Fin n, (E.gates.map (fun g => g.inputs.count (n + i.val))).sum ≤ 2) ∧
      (∀ i : Fin n, i ∉ T → E.output ≠ n + i.val ∧ ∀ g ∈ E.gates, n + i.val ∉ g.inputs) ∧
      ∀ u v, E.eval (paired u v ++ List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T))) = G u v := by
  intro a
  let S0 := initFromD T D hM hR
  have hS0_len : S0.gates.length = D.size := by simp [S0, initFromD, Circuit.size]
  have hS0_not : notCnt S0.gates = 0 := initFromD_notCnt T D hM hR
  have hS0_raw : ∀ i : Fin n, rawCount n S0.gates i = 0 := initFromD_rawCount T D hM hR
  let srcFin := T.filter (fun i => (Finset.univ.filter (fun j : Fin n => G i j = true ∧ G j i = false)).Nonempty)
  let tgtFin := T.filter (fun j => (Finset.univ.filter (fun i : Fin n => i ∉ T ∧ G i j = true ∧ G j i = false)).Nonempty)
  obtain ⟨hsum_a, hmin_bound⟩ := sum_asym_split G T hT
  have hsum_a' : (∑ i ∈ srcFin, (Finset.univ.filter (fun j : Fin n => G i j = true ∧ G j i = false)).card) +
      (∑ j ∈ tgtFin, (Finset.univ.filter (fun i : Fin n => i ∉ T ∧ G i j = true ∧ G j i = false)).card) = a := hsum_a
  have hmin_bound' : srcFin.card + tgtFin.card ≤ min a (2 * T.card) := hmin_bound
  let srcList := srcFin.toList
  let tgtList := tgtFin.toList
  obtain ⟨S1, srcOuts, hsrc_len, hS1_len, hS1_not, hS1_raw, hsrc_b, hS1_old, hsrc_val⟩ :=
    build_src_groups G T S0 srcList (Finset.nodup_toList srcFin)
      (fun i hi => (Finset.mem_filter.mp (Finset.mem_toList.mp hi)).1)
      (fun i hi => (Finset.mem_filter.mp (Finset.mem_toList.mp hi)).2)
  obtain ⟨S2, tgtOuts, htgt_len, hS2_len, hS2_not, hS2_raw, htgt_b, hS2_old, htgt_val⟩ :=
    build_tgt_groups G T S1 tgtList (Finset.nodup_toList tgtFin)
      (fun j hj => (Finset.mem_filter.mp (Finset.mem_toList.mp hj)).2)
  have hsum_src : (srcList.map (fun i => (Finset.univ.filter (fun j : Fin n => G i j = true ∧ G j i = false)).card)).sum =
      ∑ i ∈ srcFin, (Finset.univ.filter (fun j : Fin n => G i j = true ∧ G j i = false)).card := by
    dsimp [srcList]
    change (Multiset.map (fun i => (Finset.univ.filter (fun j : Fin n => G i j = true ∧ G j i = false)).card)
      (srcFin.toList : Multiset (Fin n))).sum = _
    rw [Finset.coe_toList]; rfl
  have hsum_tgt : (tgtList.map (fun j => (Finset.univ.filter (fun i : Fin n => i ∉ T ∧ G i j = true ∧ G j i = false)).card)).sum =
      ∑ j ∈ tgtFin, (Finset.univ.filter (fun i : Fin n => i ∉ T ∧ G i j = true ∧ G j i = false)).card := by
    dsimp [tgtList]
    change (Multiset.map (fun j => (Finset.univ.filter (fun i : Fin n => i ∉ T ∧ G i j = true ∧ G j i = false)).card)
      (tgtFin.toList : Multiset (Fin n))).sum = _
    rw [Finset.coe_toList]; rfl
  have hS2_size : S2.gates.length = D.size + a := by omega
  have hS2_not0 : notCnt S2.gates = 0 := by omega
  have hS2_raw1 (i : Fin n) : rawCount n S2.gates i ≤ 1 := by
    have h1 := hS1_raw i; have h2 := hS2_raw i; have h0 := hS0_raw i
    split_ifs at h1 <;> omega
  let dList : List ℕ := if D.output < n + D.size then [reloc n D.output] else []
  have hdList_val (u v : Fin n) (S' : State n T)
      (hold : ∀ w < n + n + S0.gates.length, S'.val u v w = S0.val u v w) :
      dList.any (fun w => S'.val u v w) = (G u v && G v u) := by
    dsimp [dList]
    split_ifs with hdlt
    · simp only [List.any_cons, List.any_nil, Bool.or_false]
      rw [hold _ (by rw [hS0_len]; exact reloc_lt hdlt), initFromD_val T D hM hR u v hdlt]
      exact hD u v
    · simp only [List.any_nil]
      have hfalse : D.eval (paired u v) = false := by
        unfold Circuit.eval
        rw [List.getD_eq_default]
        change (D.gates.foldl stepFn (paired u v)).length ≤ D.output
        rw [wires_len]
        have hplen : (paired u v).length = n := by simp [paired]
        rw [hplen]
        exact le_of_not_gt hdlt
      rw [← hD u v, hfalse]
  have hsrc_val_iff (u v : Fin n) :
      srcOuts.any (fun w => S2.val u v w) = decide (u ∈ T ∧ G u v = true ∧ G v u = false) := by
    have hsame : srcOuts.any (fun w => S2.val u v w) = srcOuts.any (fun w => S1.val u v w) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      exact ⟨fun ⟨w, hw, hv⟩ => ⟨w, hw, by rwa [← hS2_old u v w (hsrc_b w hw).2]⟩,
        fun ⟨w, hw, hv⟩ => ⟨w, hw, by rwa [hS2_old u v w (hsrc_b w hw).2]⟩⟩
    rw [hsame, hsrc_val u v]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, srcList, Finset.mem_toList, srcFin, Finset.mem_filter]
    constructor
    · rintro ⟨i, ⟨hiT, _⟩, rfl, h1, h2⟩; exact ⟨hiT, h1, h2⟩
    · rintro ⟨huT, h1, h2⟩; exact ⟨u, ⟨huT, ⟨v, by simp [h1, h2]⟩⟩, rfl, h1, h2⟩
  have finish_from (S' : State n T) (out : ℕ)
      (hnot : notCnt S'.gates ≤ 1)
      (hsize : S'.gates.length ≤ D.size + a + min a (2 * T.card) + T.card + 1)
      (hout_lt : out < n + n + S'.gates.length)
      (hraw : ∀ i : Fin n, rawCount n S'.gates i ≤ 2)
      (hout_no : ∀ i : Fin n, i ∉ T → out ≠ n + i.val)
      (heval : ∀ u v, S'.val u v out = G u v) :
      ∃ E : Circuit,
        FanInTwo E ∧
        ReadsBack (n + n) E ∧
        notCount E ≤ 1 ∧
        (∀ g ∈ E.gates, g.op = .not → g.inputs.length = 1) ∧
        E.output < (n + n) + E.size ∧
        E.size ≤ D.size + a + min a (2 * T.card) + T.card + 1 ∧
        (∀ i : Fin n, (E.gates.map (fun g => g.inputs.count (n + i.val))).sum ≤ 2) ∧
        (∀ i : Fin n, i ∉ T → E.output ≠ n + i.val ∧ ∀ g ∈ E.gates, n + i.val ∉ g.inputs) ∧
        ∀ u v, E.eval (paired u v ++ List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T))) = G u v := by
    refine ⟨⟨S'.gates, out⟩, ?_, S'.reads, hnot, S'.notLen, hout_lt, hsize, hraw,
      fun i hi => ⟨hout_no i hi, S'.noOutT i hi⟩, heval⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := S'.fan g hg
    exact ⟨by rcases hop with h | h | h <;> simp [h], hlen⟩
  by_cases htgt_empty : tgtOuts = []
  · have hno_asymT (u v : Fin n) (huT : u ∉ T) (h1 : G u v = true) (h2 : G v u = false) : False := by
      have hvT : v ∈ T := (hT u v h1 h2).resolve_left huT
      have hlen0 : tgtList.length = 0 := by rw [← htgt_len, htgt_empty]; rfl
      have hnil : tgtList = [] := List.eq_nil_of_length_eq_zero hlen0
      have hmem : v ∈ tgtList := Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hvT, ⟨u, by simp [huT, h1, h2]⟩⟩)
      rw [hnil] at hmem; simp at hmem
    let topList := srcOuts ++ dList
    by_cases htop_empty : topList = []
    · let g0 : Gate := ⟨GateOp.or, []⟩
      let S3 := S2.push g0 ⟨Or.inr (Or.inl rfl), by simp [g0]⟩ (by simp [g0]) (by simp [g0]) (fun _ _ => by simp [g0])
      apply finish_from S3 (n + n + S2.gates.length)
      · unfold S3 State.push; rw [notCnt_append, hS2_not0, notCnt_singleton_ne g0 (by simp [g0])]; omega
      · unfold S3 State.push; simp [hS2_size]; omega
      · unfold S3 State.push; simp
      · intro i; unfold S3 State.push; rw [rawCount_append]
        have hg0 : rawCount n [g0] i = 0 := by simp [rawCount, g0]
        rw [hg0]; have := hS2_raw1 i; omega
      · intro i _ h; omega
      · intro u v
        rw [State.push_val_new]
        simp only [g0, GateOp.eval, List.map_nil, List.any_nil]
        have hd0 : dList = [] := by
          have := List.append_eq_nil_iff.mp htop_empty; exact this.2
        have hs0 : srcOuts = [] := by
          have := List.append_eq_nil_iff.mp htop_empty; exact this.1
        have hdv := hdList_val u v S2 (fun w hw => (hS2_old u v w (by omega)).trans (hS1_old u v w hw))
        rw [hd0] at hdv; simp at hdv
        have hsv := hsrc_val_iff u v
        rw [hs0] at hsv; simp at hsv
        cases hguv : G u v
        · rfl
        · cases hgvu : G v u
          · by_cases huT : u ∈ T
            · exact absurd hgvu (by rw [hsv huT hguv]; decide)
            · exact (hno_asymT u v huT hguv hgvu).elim
          · simp [hguv, hgvu] at hdv
    · have htop_lt : ∀ w ∈ topList, w < n + n + S2.gates.length := by
        intro w hw
        rcases List.mem_append.mp hw with h | h
        · have := (hsrc_b w h).2; omega
        · dsimp [dList] at h
          split_ifs at h with hdlt
          · rw [List.mem_singleton.mp h]
            have := reloc_lt hdlt; omega
          · simp at h
      have htop_no_raw : ∀ w ∈ topList, ∀ i : Fin n, w ≠ n + i.val := by
        intro w hw i
        rcases List.mem_append.mp hw with h | h
        · have := (hsrc_b w h).1; omega
        · dsimp [dList] at h
          split_ifs at h with hdlt
          · rw [List.mem_singleton.mp h]; exact reloc_ne_raw i
          · simp at h
      have htop_cnt (i : Fin n) : topList.count (n + i.val) = 0 := by
        rw [List.count_eq_zero]; intro hmem; exact htop_no_raw _ hmem i rfl
      obtain ⟨S3, out, hS3_len, hS3_not, hS3_raw, _, _, hout_lt, hout_no, _, hout_val⟩ :=
        build_or_list S2 topList htop_empty htop_lt (fun w hw i _ => htop_no_raw w hw i)
      apply finish_from S3 out
      · omega
      · have htl : topList.length ≤ srcFin.card + 1 := by
          have hsl : srcOuts.length = srcFin.card := by rw [hsrc_len]; exact Finset.length_toList srcFin
          have hdl : dList.length ≤ 1 := by dsimp [dList]; split_ifs <;> simp
          simp only [topList, List.length_append]; omega
        omega
      · exact hout_lt
      · intro i; have h3 := hS3_raw i; rw [htop_cnt i] at h3; have := hS2_raw1 i; omega
      · exact hout_no
      · intro u v
        rw [hout_val u v]
        simp only [topList, List.any_append]
        rw [hsrc_val_iff u v, hdList_val u v S2 (fun w hw => (hS2_old u v w (by omega)).trans (hS1_old u v w hw))]
        cases hguv : G u v
        · simp
        · cases hgvu : G v u
          · by_cases huT : u ∈ T
            · simp [huT]
            · exact (hno_asymT u v huT hguv hgvu).elim
          · simp
  · have htgt_lt : ∀ w ∈ tgtOuts, w < n + n + S2.gates.length := fun w hw => (htgt_b w hw).2
    have htgt_no_raw : ∀ w ∈ tgtOuts, ∀ i : Fin n, w ≠ n + i.val := fun w hw i => by
      have := (htgt_b w hw).1; omega
    have htgt_cnt (i : Fin n) : tgtOuts.count (n + i.val) = 0 := by
      rw [List.count_eq_zero]; intro hmem; exact htgt_no_raw _ hmem i rfl
    obtain ⟨S3, targOr, hS3_len, hS3_not, hS3_raw, _, htarg_ne_raw, htarg_lt, htarg_no, hS3_old, htarg_val⟩ :=
      build_or_list S2 tgtOuts htgt_empty htgt_lt (fun w hw i _ => htgt_no_raw w hw i)
    have hT_ne : T.Nonempty := by
      have hpos : 0 < tgtList.length := by
        rw [← htgt_len]; exact List.length_pos_of_ne_nil htgt_empty
      have hcard_pos : 0 < tgtFin.card := by rwa [Finset.length_toList] at hpos
      obtain ⟨j, hj⟩ := Finset.card_pos.mp hcard_pos
      exact ⟨j, (Finset.mem_filter.mp hj).1⟩
    let rawWires : List ℕ := T.toList.map (fun t : Fin n => n + t.val)
    have hrawW_len : rawWires.length = T.card := by simp [rawWires, Finset.length_toList]
    have hrawW_ne : rawWires ≠ [] := by
      intro h; rw [h] at hrawW_len; exact (Finset.card_pos.mpr hT_ne).ne hrawW_len
    have hrawW_lt : ∀ w ∈ rawWires, w < n + n + S3.gates.length := by
      intro w hw; obtain ⟨t, _, rfl⟩ := List.mem_map.mp hw; omega
    have hrawW_no : ∀ w ∈ rawWires, ∀ i : Fin n, i ∉ T → w ≠ n + i.val := by
      intro w hw i hi heq
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw
      have hti : t = i := Fin.ext (by omega)
      subst hti
      exact hi (Finset.mem_toList.mp ht)
    have hrawW_cnt (i : Fin n) : rawWires.count (n + i.val) ≤ 1 := by
      have hnd : rawWires.Nodup := by
        apply List.Nodup.map
        · intro x y hxy; dsimp at hxy; exact Fin.ext (by omega)
        · exact Finset.nodup_toList T
      by_cases hmem : n + i.val ∈ rawWires
      · rw [List.Nodup.count hnd]; simp [hmem]
      · rw [List.count_eq_zero.mpr hmem]; omega
    obtain ⟨S4, anyRaw, hS4_len, hS4_not, hS4_raw, _, _, hany_lt, hany_no, hS4_old, hany_val⟩ :=
      build_or_list S3 rawWires hrawW_ne hrawW_lt hrawW_no
    let gNot : Gate := ⟨GateOp.not, [anyRaw]⟩
    let S5 := S4.push gNot ⟨Or.inr (Or.inr rfl), by simp [gNot]⟩
      (fun w hw => by simp [gNot] at hw; subst hw; exact hany_lt)
      (fun _ => rfl)
      (fun i hi hmem => by simp [gNot] at hmem; exact hany_no i hi hmem.symm)
    let guardW := n + n + S4.gates.length
    have hS5_not : notCnt S5.gates = 1 := by
      unfold S5 State.push; rw [notCnt_append, hS4_not, hS3_not, hS2_not0, notCnt_singleton_not gNot rfl]
    have hS5_raw (i : Fin n) : rawCount n S5.gates i ≤ 2 := by
      have h3 := hS3_raw i; rw [htgt_cnt i, Nat.add_zero] at h3
      have h4 := hS4_raw i; have hc := hrawW_cnt i
      have h2 := hS2_raw1 i
      unfold S5 State.push
      rw [rawCount_append]
      have hg_not_cnt : rawCount n [gNot] i = if anyRaw = n + i.val then 1 else 0 := by
        simp only [rawCount, gNot, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        by_cases h : anyRaw = n + i.val <;> simp [h, beq_iff_eq]
      rw [hg_not_cnt]
      omega
    let gAnd : Gate := ⟨GateOp.and, [targOr, guardW]⟩
    let S6 := S5.push gAnd ⟨Or.inl rfl, by simp [gAnd]⟩
      (fun w hw => by
        simp only [gAnd, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · unfold S5 State.push; simp; omega
        · unfold S5 State.push; simp [guardW])
      (by simp [gAnd])
      (fun i hi hmem => by
        simp only [gAnd, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h | h
        · exact htarg_no i hi h.symm
        · dsimp [guardW] at h; omega)
    let gatedTarg := n + n + S5.gates.length
    let topList := gatedTarg :: (srcOuts ++ dList)
    have htop_ne : topList ≠ [] := List.cons_ne_nil _ _
    have htop_lt : ∀ w ∈ topList, w < n + n + S6.gates.length := by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · unfold S6 State.push; simp [gatedTarg]
      · rcases List.mem_append.mp hw with h | h
        · have := (hsrc_b w h).2; unfold S6 S5 State.push; simp; omega
        · dsimp [dList] at h
          split_ifs at h with hdlt
          · rw [List.mem_singleton.mp h]; have := reloc_lt hdlt; unfold S6 S5 State.push; simp; omega
          · simp at h
    have htop_no_raw : ∀ w ∈ topList, ∀ i : Fin n, w ≠ n + i.val := by
      intro w hw i
      rcases List.mem_cons.mp hw with rfl | hw
      · dsimp [gatedTarg]; omega
      · rcases List.mem_append.mp hw with h | h
        · have := (hsrc_b w h).1; omega
        · dsimp [dList] at h
          split_ifs at h with hdlt
          · rw [List.mem_singleton.mp h]; exact reloc_ne_raw i
          · simp at h
    have htop_cnt (i : Fin n) : topList.count (n + i.val) = 0 := by
      rw [List.count_eq_zero]; intro hmem; exact htop_no_raw _ hmem i rfl
    obtain ⟨S7, out, hS7_len, hS7_not, hS7_raw, _, _, hout_lt, hout_no, _, hout_val⟩ :=
      build_or_list S6 topList htop_ne htop_lt (fun w hw i _ => htop_no_raw w hw i)
    apply finish_from S7 out
    · unfold S6 State.push at hS7_not; rw [hS7_not, notCnt_append, hS5_not, notCnt_singleton_ne gAnd (by simp [gAnd])]
    · have hS6_len : S6.gates.length = D.size + a + (tgtFin.card - 1) + (T.card - 1) + 2 := by
        unfold S6 S5 State.push
        have htgl : tgtOuts.length = tgtFin.card := by rw [htgt_len]; exact Finset.length_toList tgtFin
        simp [hS4_len, hS3_len, hS2_size, htgl, hrawW_len]
      have htl : topList.length ≤ srcFin.card + 2 := by
        have hsl : srcOuts.length = srcFin.card := by rw [hsrc_len]; exact Finset.length_toList srcFin
        have hdl : dList.length ≤ 1 := by dsimp [dList]; split_ifs <;> simp
        simp only [topList, List.length_cons, List.length_append]; omega
      have htgt_pos : 1 ≤ tgtFin.card := by
        have hpos : 0 < tgtList.length := by rw [← htgt_len]; exact List.length_pos_of_ne_nil htgt_empty
        rwa [Finset.length_toList] at hpos
      have hT_pos : 1 ≤ T.card := Finset.card_pos.mpr hT_ne
      omega
    · exact hout_lt
    · intro i
      have h7 := hS7_raw i; rw [htop_cnt i, Nat.add_zero] at h7
      have h6 : rawCount n S6.gates i = rawCount n S5.gates i := by
        unfold S6 State.push; rw [rawCount_append]
        have hg_cnt : rawCount n [gAnd] i = 0 := by
          simp only [rawCount, gAnd, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
          have hne1 : targOr ≠ n + i.val := htarg_ne_raw i (fun w hw => htgt_no_raw w hw i)
          have hne2 : guardW ≠ n + i.val := by dsimp [guardW]; omega
          simp [hne1, Ne.symm hne1, hne2, Ne.symm hne2]
        omega
      have := hS5_raw i; omega
    · exact hout_no
    · intro u v
      rw [hout_val u v]
      simp only [topList, List.any_cons, List.any_append]
      have hgated_val : S6.val u v gatedTarg = decide (u ∉ T ∧ G u v = true ∧ G v u = false) := by
        rw [State.push_val_new]
        simp only [gAnd, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true]
        have htarg_v : S5.val u v targOr =
            decide (∃ j ∈ tgtList, (j = u ∨ j = v) ∧
              ∃ i : Fin n, (i = u ∨ i = v) ∧ i ∉ T ∧ G i j = true ∧ G j i = false) := by
          rw [State.push_val_old _ _ _ _ _ _ u v (by omega), hS4_old u v targOr htarg_lt, htarg_val u v, htgt_val u v]
        have hguard_v : S5.val u v guardW = decide (u ∉ T) := by
          rw [State.push_val_new]
          simp only [gNot, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
          rw [hany_val u v]
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.not_eq_true', decide_eq_true_eq, rawWires, List.any_eq_false, List.mem_map,
            Finset.mem_toList, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
          constructor
          · intro h huT
            have hv := h u huT
            rw [S3.val_raw u v u] at hv
            simp [huT] at hv
          · intro huT t ht
            rw [S3.val_raw u v t]
            simp only [decide_eq_true_eq]
            rintro ⟨rfl, _⟩; exact huT ht
        rw [htarg_v, hguard_v]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, decide_eq_true_eq, tgtList, Finset.mem_toList, tgtFin, Finset.mem_filter]
        constructor
        · rintro ⟨⟨j, ⟨hjT, _⟩, hjuv, i, hiuv, hiT, h1, h2⟩, huT⟩
          have hju : j ≠ u := fun h => huT (h ▸ hjT)
          have hjv : j = v := hjuv.resolve_left hju
          subst hjv
          have hij : i ≠ j := fun h => hiT (h ▸ hjT)
          have hiu : i = u := hiuv.resolve_right hij
          subst hiu
          exact ⟨huT, h1, h2⟩
        · rintro ⟨huT, h1, h2⟩
          have hvT : v ∈ T := (hT u v h1 h2).resolve_left huT
          exact ⟨⟨v, ⟨hvT, ⟨u, by simp [huT, h1, h2]⟩⟩, Or.inr rfl, u, Or.inl rfl, huT, h1, h2⟩, huT⟩
      have hsrc_v : srcOuts.any (fun w => S6.val u v w) = decide (u ∈ T ∧ G u v = true ∧ G v u = false) := by
        have hsame : srcOuts.any (fun w => S6.val u v w) = srcOuts.any (fun w => S2.val u v w) := by
          apply Bool.eq_iff_iff.mpr
          simp only [List.any_eq_true]
          have hpt (w : ℕ) (hw : w ∈ srcOuts) : S6.val u v w = S2.val u v w := by
            have hlt2 : w < n + n + S2.gates.length := by have := (hsrc_b w hw).2; omega
            rw [State.push_val_old _ _ _ _ _ _ u v (by unfold S5 State.push; simp; omega),
              State.push_val_old _ _ _ _ _ _ u v (by omega), hS4_old u v w (by omega), hS3_old u v w hlt2]
          exact ⟨fun ⟨w, hw, hv⟩ => ⟨w, hw, by rwa [← hpt w hw]⟩,
            fun ⟨w, hw, hv⟩ => ⟨w, hw, by rwa [hpt w hw]⟩⟩
        rw [hsame, hsrc_val_iff u v]
      have hd_v : dList.any (fun w => S6.val u v w) = (G u v && G v u) := by
        apply hdList_val u v S6
        intro w hw
        rw [State.push_val_old _ _ _ _ _ _ u v (by unfold S5 State.push; simp; omega),
          State.push_val_old _ _ _ _ _ _ u v (by omega), hS4_old u v w (by omega),
          hS3_old u v w (by omega), hS2_old u v w (by omega), hS1_old u v w hw]
      rw [hgated_val, hsrc_v, hd_v]
      cases hguv : G u v
      · simp
      · cases hgvu : G v u
        · by_cases huT : u ∈ T <;> simp [huT]
        · simp

end PEqualNP.Outside.L_meta_25518_aux

theorem PEqualNP.Outside.L_meta_25518 : ∀ (n : ℕ) (G : Fin n → Fin n → Bool) (T : Finset (Fin n))
    (D : PEqualNP.CircuitLowerBounds.Circuit),
  let paired := fun (u v : Fin n) => List.ofFn (fun index : Fin n => decide (index = u ∨ index = v))
  let a := (Finset.univ.filter (fun p : Fin n × Fin n =>
    G p.1 p.2 = true ∧ G p.2 p.1 = false)).card
  PEqualNP.MetaComplexity.Monotone2 D →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack n D →
  (∀ u v, D.eval (paired u v) = (G u v && G v u)) →
  (∀ i j, G i j = true → G j i = false → i ∈ T ∨ j ∈ T) →
  ∃ E : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo E ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + n) E ∧
    PEqualNP.NotBracket.notCount E ≤ 1 ∧
    (∀ g ∈ E.gates, g.op = .not → g.inputs.length = 1) ∧
    E.output < (n + n) + E.size ∧
    E.size ≤ D.size + a + min a (2 * T.card) + T.card + 1 ∧
    (∀ i : Fin n, (E.gates.map (fun g => g.inputs.count (n + i.val))).sum ≤ 2) ∧
    (∀ i : Fin n, i ∉ T → E.output ≠ n + i.val ∧
      ∀ g ∈ E.gates, n + i.val ∉ g.inputs) ∧
    ∀ u v, E.eval (paired u v ++ List.ofFn (fun raw : Fin n => decide (raw = u ∧ raw ∈ T))) = G u v := by
  intro n G T D
  dsimp only
  intro hM hR hD hT
  exact PEqualNP.Outside.L_meta_25518_aux.main_construct n G T D hM hR hD hT
