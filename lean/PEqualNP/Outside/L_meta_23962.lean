import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23962_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

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

def zeroGate : Gate := ⟨.or, []⟩

def pin (C : Circuit) (q : ℕ) : Circuit := ⟨C.gates.set q zeroGate, C.output⟩

theorem pin_at (C : Circuit) (q j : ℕ) (hj : j < C.gates.length) :
    gateAt (pin C q) j = if j = q then zeroGate else gateAt C j := by
  change (C.gates.set q zeroGate).getD j ⟨GateOp.or, []⟩ =
    if j = q then zeroGate else C.gates.getD j ⟨GateOp.or, []⟩
  have hj' : j < (C.gates.set q zeroGate).length := by simpa using hj
  rw [List.getD_eq_getElem _ _ hj', List.getD_eq_getElem _ _ hj]
  by_cases h : j = q
  · subst j
    rw [ite_eq_left rfl, List.getElem_set_self]
  · rw [ite_eq_right h, List.getElem_set_ne (Ne.symm h)]

theorem pin_back (N : ℕ) (C : Circuit) (q : ℕ) (hb : ReadsBack N C) :
    ReadsBack N (pin C q) := by
  intro j hj i hi
  have hj' : j < C.gates.length := by simpa [pin] using hj
  rw [pin_at C q j hj'] at hi
  by_cases h : j = q
  · simp [h, zeroGate] at hi
  · exact hb j hj' i (by simpa [h] using hi)

theorem pin_fit (C : Circuit) (q : ℕ) (hf : FanInTwo C) : FanInTwo (pin C q) := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  have hj' : j < C.gates.length := by simpa [pin] using hj
  have he : gateAt (pin C q) j = (pin C q).gates[j] := List.getD_eq_getElem _ _ hj
  rw [← he, pin_at C q j hj']
  by_cases h : j = q
  · simp [h, zeroGate]
  · have hm : gateAt C j ∈ C.gates := by
      rw [gateAt, List.getD_eq_getElem _ _ hj']
      exact List.getElem_mem _
    simpa [h] using hf _ hm

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

theorem separate_operand (C : Circuit) (j a b : ℕ) (hj : j < C.size)
    (hc : readsIn C (Finset.range C.size) a = 1)
    (hi : (gateAt C j).inputs = [a, b] ∨ (gateAt C j).inputs = [b, a]) : b ≠ a := by
  intro h
  subst b
  have hle : (gateAt C j).inputs.count a ≤ readsIn C (Finset.range C.size) a :=
    Finset.single_le_sum (f := fun k => (gateAt C k).inputs.count a)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
  rcases hi with hi | hi <;> simp [hi, hc] at hle

theorem disjoint_three {a b : ℕ} {P Q S : Finset ℕ}
    (hpq : Disjoint P Q) (hps : Disjoint P S) (hqs : Disjoint Q S)
    (hp : a ∈ P ∨ b ∈ P) (hq : a ∈ Q ∨ b ∈ Q) (hs : a ∈ S ∨ b ∈ S) : False := by
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> rcases hs with hs | hs <;>
    first
    | exact Finset.disjoint_left.mp hpq hp hq
    | exact Finset.disjoint_left.mp hps hp hs
    | exact Finset.disjoint_left.mp hqs hq hs

def dropWire (atWire cap i : ℕ) : ℕ :=
  if i < atWire then i else if i = atWire then cap else i - 1

def dropMove (atWire cap : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (dropWire atWire cap)⟩

def step (x : List Bool) (g : Gate) : List Bool := x ++ [readGate x g]

theorem read_dropped (l r : List Bool) (cap i : ℕ) (hcap : l.length + r.length ≤ cap) :
    (l ++ false :: r).getD i false = (l ++ r).getD (dropWire l.length cap i) false := by
  rcases Nat.lt_trichotomy i l.length with hi | rfl | hi
  · rw [dropWire, ite_eq_left hi, List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hi]
  · unfold dropWire
    simp only [lt_self_iff_false, ite_false, ite_true]
    have hr : (l ++ r).getD cap false = false :=
      List.getD_eq_default (l ++ r) false (by simpa using hcap)
    rw [List.getD_append_right _ _ _ _ (by omega), Nat.sub_self,
      hr] <;> rfl
  · rw [dropWire, ite_eq_right (by omega), ite_eq_right (by omega),
      List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega)]
    have he : i - l.length = (i - 1 - l.length) + 1 := by omega
    rw [he]
    rfl

theorem fold_dropped (l r : List Bool) (gs : List Gate) (cap : ℕ)
    (hcap : l.length + r.length + gs.length ≤ cap) :
    ∀ i, (gs.foldl step (l ++ false :: r)).getD i false =
      ((gs.map (dropMove l.length cap)).foldl step (l ++ r)).getD (dropWire l.length cap i) false := by
  induction gs generalizing r with
  | nil => exact fun i => read_dropped l r cap i (by simp at hcap; omega)
  | cons g gs ih =>
    let b := readGate (l ++ false :: r) g
    have hb : readGate (l ++ r) (dropMove l.length cap g) = b := by
      simp only [readGate, dropMove, List.map_map, b]
      congr 1
      exact List.map_congr_left fun i _ => (read_dropped l r cap i (by omega)).symm
    have he₁ : step (l ++ false :: r) g = l ++ false :: (r ++ [b]) := by
      simp [step, b, List.append_assoc]
    have he₂ : step (l ++ r) (dropMove l.length cap g) = l ++ (r ++ [b]) := by
      simp [step, hb, List.append_assoc]
    simp only [List.foldl_cons, List.map_cons, he₁, he₂]
    exact ih _ (by simp at hcap ⊢; omega)

theorem remove_zero (N : ℕ) (C : Circuit) (l r : List Gate)
    (h : C.gates = l ++ zeroGate :: r) (hfit : FanInTwo C) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 1 = C.size ∧
      ∀ x : List Bool, x.length = N → C.eval x = D.eval x := by
  let cut := N + l.length
  let cap := N + C.gates.length
  let D : Circuit := ⟨l ++ r.map (dropMove cut cap), dropWire cut cap C.output⟩
  have hlen : C.gates.length = l.length + 1 + r.length := by
    rw [h]
    simp
    omega
  refine ⟨D, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hfit g (by rw [h]; exact List.mem_append_left _ hg)
    · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hg
      have hf := hfit old (by rw [h]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hold))
      exact ⟨hf.1, by simpa [dropMove] using hf.2⟩
  · change (l ++ r.map (dropMove cut cap)).length + 1 = C.gates.length
    simp
    omega
  · intro x hx
    let p := l.foldl step x
    have hp : p.length = cut := by
      change (l.foldl (fun w g => w ++ [readGate w g]) x).length = _
      rw [foldl_snoc_length readGate, hx]
    have hs : p.length + ([] : List Bool).length + r.length ≤ cap := by
      change p.length + 0 + r.length ≤ N + C.gates.length
      rw [hp]
      dsimp [cut]
      omega
    have hv := fold_dropped p [] r cap hs C.output
    change (C.gates.foldl step x).getD C.output false =
      ((l ++ r.map (dropMove cut cap)).foldl step x).getD (dropWire cut cap C.output) false
    rw [h, List.foldl_append, List.foldl_cons, List.foldl_append]
    have hz : step p zeroGate = p ++ [false] := rfl
    change (r.foldl step (step p zeroGate)).getD C.output false = _
    rw [hz]
    simpa only [hp, List.append_nil] using hv

end PEqualNP.Outside.L_meta_23962_aux

open PEqualNP.Outside.L_meta_23962_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents in
theorem PEqualNP.Outside.L_meta_23962 : ∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents A C →
  (∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
    PEqualNP.Represents.Represents A D → C.size ≤ D.size) →
  ∀ (p : List ℕ) (i2 i3 qa qb qc : ℕ) (Pa Pb Pc : Finset ℕ),
  0 < i2 → i2 < i3 → i3 < p.length →
  (∀ k < p.length, p.getD k 0 < C.size) →
  (∀ k, k + 1 < p.length →
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (n + m + p.getD k 0) = 1 ∧
    C.output ≠ n + m + p.getD k 0 ∧
    n + m + p.getD k 0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD (k + 1) 0)).inputs) →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD 0 0)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  qa ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD 0 0)).inputs →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i2 0)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  ((PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i2 0)).inputs = [n + m + p.getD (i2 - 1) 0, qb] ∨
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i2 0)).inputs = [qb, n + m + p.getD (i2 - 1) 0]) →
  (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i3 0)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
  ((PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i3 0)).inputs = [n + m + p.getD (i3 - 1) 0, qc] ∨
    (PEqualNP.MetaComplexity.NestedCover.gateAt C (p.getD i3 0)).inputs = [qc, n + m + p.getD (i3 - 1) 0]) →
  Disjoint Pa Pb → Disjoint Pa Pc → Disjoint Pb Pc →
  (∀ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD qa false = true →
    (u : ℕ) ∈ Pa ∨ n + (v : ℕ) ∈ Pa) →
  (∀ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD qb false = true →
    (u : ℕ) ∈ Pb ∨ n + (v : ℕ) ∈ Pb) →
  (∀ (u : Fin n) (v : Fin m), (C.wires (PEqualNP.Represents.oneEach u v)).getD qc false = true →
    (u : ℕ) ∈ Pc ∨ n + (v : ℕ) ∈ Pc) →
  False := by
  classical
  intro n m A C hfit hback hrep hmin p i2 i3 qa qb qc Pa Pb Pc
  intro h2 h23 h3 hindex hchain hOpA hqa hOpB hListB hOpC hListC hdAB hdAC hdBC ha hb hc
  let N := n + m
  let q := p.getD 0 0
  let P := pin C q
  have hq : q < C.gates.length := hindex 0 (by omega)
  have hlen : P.gates.length = C.gates.length := by simp [P, pin]
  have hbackP : ReadsBack N P := pin_back N C q hback
  have path_step (k : ℕ) (hk : k + 1 < p.length) : p.getD k 0 < p.getD (k + 1) 0 := by
    have hlt := hback (p.getD (k + 1) 0) (hindex _ hk) (N + p.getD k 0) (hchain k hk).2.2
    change N + p.getD k 0 < N + p.getD (k + 1) 0 at hlt
    omega
  have increasing (k l : ℕ) (hkl : k < l) (hl : l < p.length) :
      p.getD k 0 < p.getD l 0 := by
    induction l with
    | zero => omega
    | succ l ih =>
      have hs := path_step l (by omega : l + 1 < p.length)
      by_cases hk : k = l
      · simpa [hk] using hs
      · exact (ih (by omega) (by omega)).trans hs
  have index_unique (k l : ℕ) (hk : k < p.length) (hl : l < p.length)
      (he : p.getD k 0 = p.getD l 0) : k = l := by
    rcases Nat.lt_trichotomy k l with h | h | h
    · exact (Nat.ne_of_lt (increasing k l h hl) he).elim
    · exact h
    · exact (Nat.ne_of_lt (increasing l k h hk) he.symm).elim
  have next_reader {j k w : ℕ} (hj : j < C.gates.length) (hk : k + 1 < p.length)
      (hw : w = N + p.getD k 0) (hread : w ∈ (gateAt C j).inputs) : j = p.getD (k + 1) 0 := by
    subst w
    exact only_reader C _ j _ hj (hindex _ hk) (hchain k hk).1 hread (hchain k hk).2.2
  have hpreserve (u : Fin n) (v : Fin m) : P.eval (oneEach u v) = A u v := by
    let x := oneEach u v
    let V (i : ℕ) := (C.wires x).getD i false
    let V' (i : ℕ) := (P.wires x).getD i false
    have hx : x.length = N := by simp [x, oneEach, N]
    have wlen (B : Circuit) : (B.wires x).length = N + B.gates.length := by
      change (B.gates.foldl (fun w g => w ++ [readGate w g]) x).length = _
      rw [foldl_snoc_length readGate, hx]
    have small (B : Circuit) (i : ℕ) (hi : i < N) : (B.wires x).getD i false = x.getD i false :=
      getD_of_initial (foldl_snoc_keeps readGate B.gates x) (by rwa [hx]) false
    have go (j : ℕ) (hj : j < C.gates.length) :
        V (N + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map V) :=
      gate_value N C x hx hback j hj
    have gp (j : ℕ) (hj : j < C.gates.length) :
        V' (N + j) = (gateAt P j).op.eval ((gateAt P j).inputs.map V') :=
      gate_value N P x hx hbackP j (by rwa [hlen])
    have same_gate (j : ℕ) (hj : j < C.gates.length) (hn : j ≠ q) :
        gateAt P j = gateAt C j := by
      change gateAt (pin C q) j = _
      rw [pin_at C q j hj, ite_eq_right hn]
    have pinned_false : V' (N + q) = false := by
      rw [gp q hq]
      change (gateAt (pin C q) q).op.eval ((gateAt (pin C q) q).inputs.map V') = _
      rw [pin_at C q q hq, ite_eq_left rfl] <;> rfl
    have trace (w : ℕ) (hd : V w ≠ V' w) :
        ∃ k < i3, w = N + p.getD k 0 ∧ V qa = true ∧ (i2 ≤ k → V qb = true) := by
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        have hlo : N ≤ w := by
          by_contra h
          have hw : w < N := by omega
          exact hd ((small C w hw).trans (small P w hw).symm)
        have hhi : w < N + C.gates.length := by
          by_contra h
          have h₁ : V w = false := List.getD_eq_default (C.wires x) false (by rw [wlen]; omega)
          have h₂ : V' w = false := List.getD_eq_default (P.wires x) false (by rw [wlen, hlen]; omega)
          exact hd (h₁.trans h₂.symm)
        let j := w - N
        have hj : j < C.gates.length := by dsimp [j]; omega
        have hw : w = N + j := by dsimp [j]; omega
        by_cases hqj : j = q
        · have he : w = N + q := hw.trans (congrArg (fun i => N + i) hqj)
          have htrue : V (N + q) = true := by
            have hnot : V (N + q) ≠ false := by
              rw [he, pinned_false] at hd
              exact hd
            simpa using hnot
          have hv := (go q hq).symm.trans htrue
          change (gateAt C q).op = GateOp.and at hOpA
          rw [hOpA, GateOp.eval, List.all_map, List.all_eq_true] at hv
          exact ⟨0, by omega, he, hv qa hqa, fun h => by omega⟩
        · have hdInput : ∃ z ∈ (gateAt C j).inputs, V z ≠ V' z := by
            by_contra hn
            apply hd
            rw [hw, go j hj, gp j hj, same_gate j hj hqj]
            congr 1
            apply List.map_congr_left
            intro z hz
            by_contra hd'
            exact hn ⟨z, hz, hd'⟩
          obtain ⟨z, hzmem, hzdiff⟩ := hdInput
          have earlier {r : ℕ} (hr : r ∈ (gateAt C j).inputs) : r < w := by
            rw [hw]
            exact hback j hj r hr
          obtain ⟨k, hk, hz, haTrue, hbTrue⟩ := ih z (earlier hzmem) hzdiff
          have hk' : k + 1 < p.length := by omega
          have hnext := next_reader hj hk' hz hzmem
          have hcount : readsIn C (Finset.range C.size) z = 1 := by
            rw [hz]
            exact (hchain k hk').1
          have attach_true (r : ℕ) (hop : (gateAt C j).op = GateOp.and)
              (hlist : (gateAt C j).inputs = [z, r] ∨ (gateAt C j).inputs = [r, z]) :
              V r = true := by
            have hsep := separate_operand C j z r hj hcount hlist
            have hrmem : r ∈ (gateAt C j).inputs := by rcases hlist with h | h <;> simp [h]
            have hsame : V r = V' r := by
              by_contra hd'
              obtain ⟨l, hl, hrwire, _, _⟩ := ih r (earlier hrmem) hd'
              have hl' : l + 1 < p.length := by omega
              have hnext' := next_reader hj hl' hrwire hrmem
              have he := index_unique (l + 1) (k + 1) hl' hk' (hnext'.symm.trans hnext)
              have he' : l = k := by omega
              apply hsep
              rw [hrwire, hz, he']
            cases hr : V r with
            | true => rfl
            | false =>
              exfalso
              apply hd
              rw [hw, go j hj, gp j hj, same_gate j hj hqj, hop]
              rcases hlist with h | h <;> simp [h, GateOp.eval, hr, ← hsame]
          have past_second (hk2 : i2 ≤ k + 1) : V qb = true := by
            by_cases he : i2 ≤ k
            · exact hbTrue he
            · have eq : k + 1 = i2 := by omega
              have prev : i2 - 1 = k := by omega
              apply attach_true qb
              · rw [hnext, eq]
                exact hOpB
              · rw [hnext, eq, hz]
                simpa only [prev] using hListB
          by_cases hd3 : k + 1 < i3
          · exact ⟨k + 1, hd3, hw.trans (congrArg (fun i => N + i) hnext), haTrue, past_second⟩
          · have eq : k + 1 = i3 := by omega
            have prev : i3 - 1 = k := by omega
            have hcTrue : V qc = true := by
              apply attach_true qc
              · rw [hnext, eq]
                exact hOpC
              · rw [hnext, eq, hz]
                simpa only [prev] using hListC
            exact (disjoint_three hdAB hdAC hdBC (ha u v haTrue)
              (hb u v (past_second (by omega))) (hc u v hcTrue)).elim
    have hsame : V C.output = V' C.output := by
      by_contra hd
      obtain ⟨k, hk, hw, _, _⟩ := trace C.output hd
      exact (hchain k (by omega)).2.1 hw
    exact hsame.symm.trans (hrep u v)
  have hq' : q < P.gates.length := by rwa [hlen]
  have hzero : P.gates[q] = zeroGate := by
    rw [← List.getD_eq_getElem _ zeroGate hq']
    change gateAt (pin C q) q = zeroGate
    rw [pin_at C q q hq, ite_eq_left rfl]
  let l := P.gates.take q
  let r := P.gates.drop (q + 1)
  have hsplit : P.gates = l ++ zeroGate :: r := by
    have h : P.gates = P.gates.take q ++ P.gates[q] :: P.gates.drop (q + 1) := by simp
    simpa only [l, r, hzero] using h
  obtain ⟨D, hfitD, hsizeD, hevalD⟩ := remove_zero N P l r hsplit (pin_fit C q hfit)
  have hrepD : Represents A D := fun u v =>
    (hevalD (oneEach u v) (by simp [oneEach, N])).symm.trans (hpreserve u v)
  have he := hmin D hfitD hrepD
  have hsizeP : P.size = C.size := hlen
  omega
