import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1356_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open PEqualNP.NotBracket (notCount)

/-! ### Section 1: Circuit evaluation, extensions, and basic gate builders -/

private abbrev Allowed (g : Gate) : Prop :=
  g.op = .and ∨ g.op = .or ∨ g.op = .not

private abbrev GateShape (g : Gate) : Prop :=
  Allowed g ∧ g.inputs.length ≤ 2

private def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem wires_eq (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl gateStep x := rfl

private theorem fold_length (gs : List Gate) (x : List Bool) :
    (gs.foldl gateStep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, gateStep, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size :=
  fold_length C.gates x

private theorem fold_getD_lt (gs : List Gate) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    (gs.foldl gateStep x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    have hlt : i < (gateStep x g).length := by
      simp only [gateStep, List.length_append, List.length_singleton]; omega
    rw [List.foldl_cons, ih (gateStep x g) hlt]
    exact List.getD_append _ _ _ _ hi

private def value (C : Circuit) (x : List Bool) (i : ℕ) : Bool :=
  (C.wires x).getD i false

private def nextWire (N : ℕ) (C : Circuit) : ℕ := N + C.size

private def emptyCircuit : Circuit := ⟨[], 0⟩

private def appendGate (C : Circuit) (g : Gate) : Circuit :=
  ⟨C.gates ++ [g], C.output⟩

private def appendGates (C : Circuit) (gs : List Gate) : Circuit :=
  ⟨C.gates ++ gs, C.output⟩

private def appendFamily {k : ℕ} (C : Circuit) (g : Fin k → Gate) : Circuit :=
  appendGates C (List.ofFn g)

private theorem wires_prefix {C D : Circuit} (ext : C.gates <+: D.gates) (x : List Bool)
    {i : ℕ} (hi : i < x.length + C.size) :
    value D x i = value C x i := by
  obtain ⟨rest, hrest⟩ := ext
  unfold value
  rw [wires_eq, wires_eq, ← hrest, List.foldl_append]
  apply fold_getD_lt
  rw [fold_length]
  exact hi

private theorem wires_input (C : Circuit) (x : List Bool) {i : ℕ} (hi : i < x.length) :
    value C x i = x.getD i false :=
  fold_getD_lt C.gates x hi

private theorem wires_gate (C : Circuit) (x : List Bool) (hRB : ReadsBack x.length C)
    {j : ℕ} (hj : j < C.size) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  have hj' : j < C.gates.length := hj
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) :=
      List.drop_eq_getElem_cons hj'
    rw [h2] at h1
    rw [List.append_assoc]; exact h1.symm
  have htake_len : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj')
  have hgate : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
  let w0 := (C.gates.take j).foldl gateStep x
  have hw0_len : w0.length = x.length + j := by
    dsimp only [w0]; rw [fold_length, htake_len]
  have hprefix_w0 : ∀ i < x.length + j, (C.wires x).getD i false = w0.getD i false := by
    intro i hi
    rw [wires_eq, hsplit, List.append_assoc, List.foldl_append]
    exact fold_getD_lt _ _ (by rw [hw0_len]; exact hi)
  have hstep : (C.wires x).getD (x.length + j) false =
      (gateStep w0 C.gates[j]).getD (x.length + j) false := by
    conv_lhs => rw [wires_eq, hsplit, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    apply fold_getD_lt
    simp only [gateStep, List.length_append, List.length_singleton, fold_length, htake_len]
    omega
  rw [hstep, gateStep, List.getD_append_right _ _ _ _ (by omega : w0.length ≤ x.length + j)]
  have hsub : x.length + j - w0.length = 0 := by omega
  rw [hsub]
  simp only [List.getD_cons_zero, hgate]
  apply congrArg C.gates[j].op.eval
  apply List.map_congr_left
  intro i hi
  have hilt : i < x.length + j := by
    have := hRB j hj' i
    rw [hgate] at this
    exact this hi
  exact (hprefix_w0 i hilt).symm

private theorem notCount_append (gs1 gs2 : List Gate) (o : ℕ) :
    notCount ⟨gs1 ++ gs2, o⟩ = notCount ⟨gs1, 0⟩ + notCount ⟨gs2, 0⟩ := by
  simp [notCount, List.filter_append]

private theorem notCount_cons_not (l : List ℕ) :
    notCount ⟨[⟨GateOp.not, l⟩], 0⟩ = 1 := by
  simp [notCount]

private theorem notCount_all_nonNot (gs : List Gate) (h : ∀ g ∈ gs, g.op ≠ GateOp.not) :
    notCount ⟨gs, 0⟩ = 0 := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hne : g.op ≠ GateOp.not := h g (List.mem_cons_self ..)
    have ih' := ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))
    simpa [notCount, hne] using ih'

private theorem getD_ofFn_lt {α : Type*} {k : ℕ} (g : Fin k → α) (d : α) {m : ℕ} (hm : m < k) :
    (List.ofFn g).getD m d = g ⟨m, hm⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hm)]
  simp

private def Good (N : ℕ) (C : Circuit) : Prop :=
  FanInTwo C ∧ ReadsBack N C

private theorem emptyCircuit_good (N : ℕ) : Good N emptyCircuit := by
  refine ⟨?_, ?_⟩
  · intro g hg; cases hg
  · intro j hj; cases hj

private theorem appendFamily_prefix {k : ℕ} (C : Circuit) (g : Fin k → Gate) :
    C.gates <+: (appendFamily C g).gates :=
  ⟨List.ofFn g, rfl⟩

private theorem appendFamily_size {k : ℕ} (C : Circuit) (g : Fin k → Gate) :
    (appendFamily C g).size = C.size + k := by
  simp [appendFamily, appendGates, Circuit.size]

private theorem appendFamily_good {N k : ℕ} {C : Circuit} {g : Fin k → Gate}
    (hC : Good N C) (hshape : ∀ i, GateShape (g i))
    (hback : ∀ i, ∀ w ∈ (g i).inputs, w < nextWire N C) :
    Good N (appendFamily C g) := by
  refine ⟨?_, ?_⟩
  · intro gt hgt
    rcases List.mem_append.mp hgt with old | added
    · exact hC.1 gt old
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp added
      have hs := hshape i
      exact ⟨by simpa [Allowed] using hs.1, hs.2⟩
  · intro j hj w hw
    have hj' : j < C.gates.length + k := by
      simpa [appendFamily, appendGates] using hj
    by_cases hlt : j < C.gates.length
    · have hgt : gateAt (appendFamily C g) j = gateAt C j := by
        unfold gateAt appendFamily appendGates
        exact List.getD_append _ _ _ _ hlt
      rw [hgt] at hw
      exact hC.2 j hlt w hw
    · have hidx : j - C.gates.length < k := by omega
      have hgt : gateAt (appendFamily C g) j = g ⟨j - C.gates.length, hidx⟩ := by
        unfold gateAt appendFamily appendGates
        rw [List.getD_append_right _ _ _ _ (by omega : C.gates.length ≤ j)]
        exact getD_ofFn_lt g _ hidx
      rw [hgt] at hw
      have := hback ⟨j - C.gates.length, hidx⟩ w hw
      unfold nextWire Circuit.size at this
      omega

private theorem appendFamily_new {N k : ℕ} {C : Circuit} {g : Fin k → Gate}
    (hC : Good N C) (hshape : ∀ i, GateShape (g i))
    (hback : ∀ i, ∀ w ∈ (g i).inputs, w < nextWire N C)
    (x : List Bool) (hx : x.length = N) (i : Fin k) :
    value (appendFamily C g) x (nextWire N C + i.val) =
      (g i).op.eval ((g i).inputs.map fun w => value C x w) := by
  let D := appendFamily C g
  have hD : Good N D := appendFamily_good hC hshape hback
  have hlt : C.size + i.val < D.size := by
    rw [appendFamily_size]; have := i.isLt; omega
  have hgate : gateAt D (C.size + i.val) = g i := by
    simp only [gateAt, D, appendFamily, appendGates, Circuit.size]
    rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _)]
    have hsub : C.gates.length + i.val - C.gates.length = i.val := Nat.add_sub_cancel_left _ _
    rw [hsub]
    exact getD_ofFn_lt g _ i.isLt
  have hwg := wires_gate D x (hx.symm ▸ hD.2) hlt
  have hidx : x.length + (C.size + i.val) = nextWire N C + i.val := by
    unfold nextWire; omega
  rw [hidx, hgate] at hwg
  unfold value
  rw [hwg]
  apply congrArg (g i).op.eval
  apply List.map_congr_left
  intro w hw
  have hwlt : w < x.length + C.size := by
    have := hback i w hw; unfold nextWire at this; omega
  exact wires_prefix (appendFamily_prefix C g) x hwlt

private def binVal (conj : Bool) (a b : Bool) : Bool :=
  if conj then a && b else a || b

private theorem emit_not {X : Type*} {N : ℕ} {C : Circuit}
    (input : X → List Bool) (hlen : ∀ x, (input x).length = N)
    (hC : Good N C) {a : ℕ} (ha : a < nextWire N C) :
    ∃ D w, Good N D ∧ C.gates <+: D.gates ∧ w < nextWire N D ∧
      D.size = C.size + 1 ∧ notCount D = notCount C + 1 ∧
      ∀ x, value D (input x) w = !value C (input x) a := by
  let g : Fin 1 → Gate := fun _ => ⟨.not, [a]⟩
  have hshape : ∀ i, GateShape (g i) := fun _ => ⟨Or.inr (Or.inr rfl), by simp [g]⟩
  have hback : ∀ i, ∀ w ∈ (g i).inputs, w < nextWire N C := by
    intro _ w hw; simp [g] at hw; subst hw; exact ha
  let D := appendFamily C g
  refine ⟨D, nextWire N C, appendFamily_good hC hshape hback, appendFamily_prefix C g,
    by simp [D, nextWire, appendFamily_size], appendFamily_size C g, ?_, ?_⟩
  · change notCount ⟨C.gates ++ [⟨.not, [a]⟩], C.output⟩ = notCount C + 1
    rw [notCount_append, notCount_cons_not]; rfl
  · intro x
    have h := appendFamily_new hC hshape hback (input x) (hlen x) ⟨0, by decide⟩
    simpa [D, g, GateOp.eval] using h

private theorem emit_family {X : Type*} {N k : ℕ} {C : Circuit}
    (input : X → List Bool) (hlen : ∀ x, (input x).length = N)
    (hC : Good N C) (conj : Bool) (a b : Fin k → ℕ)
    (ha : ∀ i, a i < nextWire N C) (hb : ∀ i, b i < nextWire N C) :
    ∃ D, ∃ w : Fin k → ℕ, Good N D ∧ C.gates <+: D.gates ∧
      (∀ i, w i < nextWire N D) ∧ D.size = C.size + k ∧ notCount D = notCount C ∧
      ∀ x i, value D (input x) (w i) = binVal conj (value C (input x) (a i)) (value C (input x) (b i)) := by
  let g : Fin k → Gate := fun i => ⟨if conj then .and else .or, [a i, b i]⟩
  have hshape : ∀ i, GateShape (g i) := by
    intro i; cases conj <;> simp [GateShape, Allowed, g]
  have hback : ∀ i, ∀ w ∈ (g i).inputs, w < nextWire N C := by
    intro i w hw
    simp only [g, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ha i
    · exact hb i
  let D := appendFamily C g
  refine ⟨D, fun i => nextWire N C + i.val, appendFamily_good hC hshape hback,
    appendFamily_prefix C g, ?_, appendFamily_size C g, ?_, ?_⟩
  · intro i; simp only [D, nextWire, appendFamily_size]; have := i.isLt; omega
  · change notCount ⟨C.gates ++ List.ofFn g, C.output⟩ = notCount C
    rw [notCount_append, notCount_all_nonNot (List.ofFn g)]
    · simp [notCount]
    · intro gt hgt
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hgt
      cases conj <;> simp [g]
  · intro x i
    have h := appendFamily_new hC hshape hback (input x) (hlen x) i
    cases conj <;> simpa [D, g, binVal, GateOp.eval] using h

private theorem emit_binary {X : Type*} {N : ℕ} {C : Circuit}
    (input : X → List Bool) (hlen : ∀ x, (input x).length = N)
    (hC : Good N C) (conj : Bool) {a b : ℕ}
    (ha : a < nextWire N C) (hb : b < nextWire N C) :
    ∃ D w, Good N D ∧ C.gates <+: D.gates ∧ w < nextWire N D ∧
      D.size = C.size + 1 ∧ notCount D = notCount C ∧
      ∀ x, value D (input x) w = binVal conj (value C (input x) a) (value C (input x) b) := by
  obtain ⟨D, w, hD, he, hw, hs, hn, hv⟩ := emit_family input hlen hC (k := 1) conj
    (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hb)
  exact ⟨D, w ⟨0, by decide⟩, hD, he, hw ⟨0, by decide⟩, hs, hn, fun x => hv x ⟨0, by decide⟩⟩

private theorem nextWire_le_of_prefix {N : ℕ} {C D : Circuit} (ext : C.gates <+: D.gates) :
    nextWire N C ≤ nextWire N D := by
  obtain ⟨rest, hrest⟩ := ext
  unfold nextWire Circuit.size
  rw [← hrest, List.length_append]
  omega

private theorem emit_any {X : Type*} {N : ℕ}
    (input : X → List Bool) (hlen : ∀ x, (input x).length = N) (ws : List ℕ) :
    ∀ {C : Circuit} {a : ℕ}, Good N C → a < nextWire N C → (∀ w ∈ ws, w < nextWire N C) →
      ∃ D b, Good N D ∧ C.gates <+: D.gates ∧ b < nextWire N D ∧
        D.size = C.size + ws.length ∧ notCount D = notCount C ∧
        ∀ x, value D (input x) b = (value C (input x) a || ws.any (value C (input x))) := by
  induction ws with
  | nil =>
    intro C a hC ha _
    exact ⟨C, a, hC, List.prefix_refl _, ha, by simp, rfl, by simp⟩
  | cons w ws ih =>
    intro C a hC ha hws
    have hw : w < nextWire N C := hws w (List.mem_cons_self ..)
    obtain ⟨A, b, hA, e1, hb, s1, n1, v1⟩ := emit_binary input hlen hC false ha hw
    obtain ⟨D, d, hD, e2, hd, s2, n2, v2⟩ := ih hA hb
      (fun u hu => (hws u (List.mem_cons_of_mem _ hu)).trans_le (nextWire_le_of_prefix e1))
    refine ⟨D, d, hD, e1.trans e2, hd, ?_, n2.trans n1, ?_⟩
    · simp [s2, s1]; omega
    · intro x
      have hany : ws.any (value A (input x)) = ws.any (value C (input x)) := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true]
        constructor <;> rintro ⟨u, hu, hval⟩
        · have hu_lt : u < (input x).length + C.size := by
            rw [hlen x]; exact hws u (List.mem_cons_of_mem _ hu)
          exact ⟨u, hu, (wires_prefix e1 (input x) hu_lt).symm.trans hval⟩
        · have hu_lt : u < (input x).length + C.size := by
            rw [hlen x]; exact hws u (List.mem_cons_of_mem _ hu)
          exact ⟨u, hu, (wires_prefix e1 (input x) hu_lt).trans hval⟩
      rw [v2, v1, hany]
      simp [binVal, Bool.or_assoc]

/-! ### Section 2: Markov grade and monotone chain fall bound -/

private def bitOrder (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false ≤ y.getD i false

private theorem bool_order (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

private theorem bool_digit (b : Bool) : b.toNat ≤ 1 := by
  cases b <;> decide

private theorem digit_order {a b : Bool} (ab : a ≤ b) : a.toNat ≤ b.toNat := by
  cases a <;> cases b <;> simp_all [bool_order]

private theorem digit_inj {a b : Bool} (eq : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem order_append {x y : List Bool} (ordered : bitOrder x y) {a b : Bool} (ab : a ≤ b) :
    bitOrder (x ++ [a]) (y ++ [b]) := by
  refine ⟨by simp [ordered.1], ?_⟩
  intro i
  rcases lt_trichotomy i x.length with lt | eq | gt
  · have ly : i < y.length := ordered.1 ▸ lt
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left lt,
      List.getElem?_append_left ly] using ordered.2 i
  · subst i
    simpa [List.getD_eq_getElem?_getD, ordered.1] using ab
  · have noneX : (x ++ [a]).length ≤ i := by simp; omega
    have noneY : (y ++ [b]).length ≤ i := by simp [← ordered.1]; omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none noneX, List.getElem?_eq_none noneY]

private def incoming (g : Gate) (w : List Bool) : List Bool :=
  g.inputs.map (fun i => w.getD i false)

private def outputBit (g : Gate) (w : List Bool) : Bool := g.op.eval (incoming g w)

private def firstBit (g : Gate) (w : List Bool) : Bool := (incoming g w).headD false

private theorem first_order (g : Gate) {x y : List Bool} (ordered : bitOrder x y) :
    firstBit g x ≤ firstBit g y := by
  unfold firstBit incoming
  cases g.inputs with
  | nil => simp
  | cons i _ => exact ordered.2 i

private theorem and_order {g : Gate} (op : g.op = .and) {x y : List Bool} (ordered : bitOrder x y) :
    outputBit g x ≤ outputBit g y := by
  apply (bool_order _ _).mpr
  intro on
  simp only [outputBit, op, GateOp.eval, List.all_eq_true] at on ⊢
  intro v hm
  obtain ⟨i, here, rfl⟩ := List.mem_map.mp hm
  exact (bool_order _ _).mp (ordered.2 i) (on _ (List.mem_map.mpr ⟨i, here, rfl⟩))

private theorem or_order {g : Gate} (op : g.op = .or) {x y : List Bool} (ordered : bitOrder x y) :
    outputBit g x ≤ outputBit g y := by
  apply (bool_order _ _).mpr
  intro on
  simp only [outputBit, op, GateOp.eval, List.any_eq_true] at on ⊢
  obtain ⟨v, hm, active⟩ := on
  obtain ⟨i, here, rfl⟩ := List.mem_map.mp hm
  exact ⟨_, List.mem_map.mpr ⟨i, here, rfl⟩, (bool_order _ _).mp (ordered.2 i) active⟩

private def inverting (g : Gate) : Bool :=
  match g.op with | .not => true | _ => false

private def advance (s : List Bool × ℕ) (g : Gate) : List Bool × ℕ :=
  (s.1 ++ [outputBit g s.1], if inverting g then 2 * s.2 + (firstBit g s.1).toNat else s.2)

private def consistent (s t : List Bool × ℕ) : Prop :=
  s.2 ≤ t.2 ∧ (s.2 = t.2 → bitOrder s.1 t.1)

private theorem advance_consistent {s t : List Bool × ℕ} {g : Gate} (allowed : Allowed g)
    (before : consistent s t) : consistent (advance s g) (advance t g) := by
  by_cases strict : s.2 < t.2
  · have increase : (advance s g).2 < (advance t g).2 := by
      by_cases neg : inverting g = true
      · simp only [advance, neg, ite_true]
        have bit := bool_digit (firstBit g s.1)
        omega
      · simpa [advance, neg] using strict
    exact ⟨increase.le, fun eq => (increase.ne eq).elim⟩
  have eq : s.2 = t.2 := Nat.le_antisymm before.1 (Nat.le_of_not_gt strict)
  have ordered := before.2 eq
  rcases allowed with op | op | op
  · simp only [consistent, advance, inverting, op, Bool.false_eq_true, ite_false]
    exact ⟨before.1, fun _ => order_append ordered (and_order op ordered)⟩
  · simp only [consistent, advance, inverting, op, Bool.false_eq_true, ite_false]
    exact ⟨before.1, fun _ => order_append ordered (or_order op ordered)⟩
  · simp only [consistent, advance, inverting, op, ite_true]
    have order := digit_order (first_order g ordered)
    refine ⟨by omega, ?_⟩
    intro next
    have sameDigit : (firstBit g s.1).toNat = (firstBit g t.1).toNat := by omega
    have sameBit := digit_inj sameDigit
    apply order_append ordered
    simp only [outputBit, op, GateOp.eval]
    change (!firstBit g s.1) ≤ (!firstBit g t.1)
    rw [sameBit]

private def negCount (gs : List Gate) : ℕ := (gs.filter inverting).length

private theorem negCount_spec (C : Circuit) : negCount C.gates = notCount C := by
  classical
  unfold negCount notCount
  congr 2
  funext g
  cases h : g.op <;> simp [inverting, h]

private theorem run_consistent (gs : List Gate) (allowed : ∀ g ∈ gs, Allowed g)
    {s t : List Bool × ℕ} (before : consistent s t) :
    consistent (gs.foldl advance s) (gs.foldl advance t) := by
  induction gs generalizing s t with
  | nil => exact before
  | cons g rest ih =>
    exact ih (fun k hm => allowed k (List.mem_cons_of_mem _ hm))
      (advance_consistent (allowed g (List.mem_cons_self ..)) before)

private theorem run_bounded (gs : List Gate) (s : List Bool × ℕ) (d : ℕ) (bound : s.2 < 2 ^ d) :
    (gs.foldl advance s).2 < 2 ^ (d + negCount gs) := by
  induction gs generalizing s d with
  | nil => simpa [negCount] using bound
  | cons g rest ih =>
    by_cases neg : inverting g = true
    · have raises : (advance s g).2 < 2 ^ (d + 1) := by
        simp only [advance, neg, ite_true, Nat.pow_succ]
        have digit := bool_digit (firstBit g s.1)
        omega
      have next := ih (advance s g) (d + 1) raises
      simpa [negCount, neg, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next
    · have same : (advance s g).2 < 2 ^ d := by simpa [advance, neg] using bound
      simpa [negCount, neg] using ih (advance s g) d same

private theorem run_wires (gs : List Gate) (s : List Bool × ℕ) :
    (gs.foldl advance s).1 = gs.foldl gateStep s.1 := by
  induction gs generalizing s with
  | nil => rfl
  | cons g rest ih => exact ih (advance s g)

private def grade (C : Circuit) (x : List Bool) : ℕ := (C.gates.foldl advance (x, 0)).2

private theorem grade_bound (C : Circuit) (x : List Bool) : grade C x < 2 ^ (notCount C) := by
  simpa [grade, negCount_spec] using run_bounded C.gates (x, 0) 0 (by change 0 < (1 : ℕ); decide)

private theorem grade_order {C : Circuit} (basis : FanInTwo C) {x y : List Bool} (xy : bitOrder x y) :
    grade C x ≤ grade C y ∧ (grade C x = grade C y → C.eval x ≤ C.eval y) := by
  have allowed (g) (mem : g ∈ C.gates) : Allowed g := by
    simpa [Allowed] using (basis g mem).1
  have initial : consistent (x, 0) (y, 0) := ⟨le_rfl, fun _ => xy⟩
  have result := run_consistent C.gates allowed initial
  refine ⟨result.1, ?_⟩
  intro eq
  have order := (result.2 eq).2
  rw [run_wires, run_wires] at order
  exact order C.output

private theorem grade_fall {C : Circuit} (basis : FanInTwo C) {x y : List Bool} (xy : bitOrder x y)
    (up : C.eval x = true) (down : C.eval y = false) : grade C x < grade C y := by
  obtain ⟨le, eq⟩ := grade_order basis xy
  refine lt_of_le_of_ne le (fun h => ?_)
  have bad := eq h
  rw [up, down] at bad
  exact (by decide : ¬(true ≤ false)) bad

/-! ### Section 3: Cone expansion and s + 1 raw-leaf bound -/

private def coneFrom (N : ℕ) (C : Circuit) : ℕ → Finset ℕ → Finset ℕ
  | 0, F => F
  | k + 1, F =>
    if N + k ∈ F then
      coneFrom N C k ((F.erase (N + k)) ∪ (gateAt C k).inputs.toFinset)
    else
      coneFrom N C k F

private theorem coneFrom_lt {N : ℕ} {C : Circuit} (hRB : ReadsBack N C) :
    ∀ k ≤ C.size, ∀ F : Finset ℕ, (∀ w ∈ F, w < N + k) → ∀ w ∈ coneFrom N C k F, w < N := by
  intro k
  induction k with
  | zero =>
    intro _ F hF w hw
    simpa using hF w hw
  | succ k ih =>
    intro hk F hF w hw
    dsimp only [coneFrom] at hw
    split_ifs at hw with hmem
    · apply ih (by omega) _ _ w hw
      intro u hu
      rcases Finset.mem_union.mp hu with h1 | h2
      · have hne : u ≠ N + k := (Finset.mem_erase.mp h1).1
        have hlt : u < N + (k + 1) := hF u (Finset.mem_erase.mp h1).2
        omega
      · exact hRB k (by unfold Circuit.size at hk; omega) u (List.mem_toFinset.mp h2)
    · apply ih (by omega) F _ w hw
      intro u hu
      have hlt : u < N + (k + 1) := hF u hu
      have hne : u ≠ N + k := fun heq => hmem (heq ▸ hu)
      omega

private theorem coneFrom_card {N : ℕ} {C : Circuit} (hF2 : FanInTwo C) :
    ∀ k ≤ C.size, ∀ F : Finset ℕ, (coneFrom N C k F).card ≤ F.card + k := by
  intro k
  induction k with
  | zero => intro _ F; simp [coneFrom]
  | succ k ih =>
    intro hk F
    dsimp only [coneFrom]
    split_ifs with hmem
    · have h1 := ih (by omega) ((F.erase (N + k)) ∪ (gateAt C k).inputs.toFinset)
      have h2 : ((F.erase (N + k)) ∪ (gateAt C k).inputs.toFinset).card ≤
          (F.erase (N + k)).card + (gateAt C k).inputs.toFinset.card :=
        Finset.card_union_le _ _
      have h3 : (F.erase (N + k)).card = F.card - 1 := Finset.card_erase_of_mem hmem
      have hpos : 1 ≤ F.card := Finset.one_le_card.mpr ⟨N + k, hmem⟩
      have hk' : k < C.gates.length := by unfold Circuit.size at hk; omega
      have hgk : gateAt C k = C.gates[k]'hk' := by
        rw [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']; rfl
      have hlen : (gateAt C k).inputs.length ≤ 2 := by
        rw [hgk]; exact (hF2 _ (List.getElem_mem _)).2
      have h4 : (gateAt C k).inputs.toFinset.card ≤ 2 :=
        (List.toFinset_card_le _).trans hlen
      omega
    · have h1 := ih (by omega) F
      omega

private theorem coneFrom_agree {N : ℕ} {C : Circuit} (hRB : ReadsBack N C)
    {x y : List Bool} (hx : x.length = N) (hy : y.length = N) :
    ∀ k ≤ C.size, ∀ F : Finset ℕ, (∀ w ∈ F, w < N + k) →
      (∀ w ∈ coneFrom N C k F, (C.wires x).getD w false = (C.wires y).getD w false) →
      ∀ w ∈ F, (C.wires x).getD w false = (C.wires y).getD w false := by
  intro k
  induction k with
  | zero =>
    intro _ F _ hagree w hw
    exact hagree w hw
  | succ k ih =>
    intro hk F hF hagree w hw
    dsimp only [coneFrom] at hagree
    split_ifs at hagree with hmem
    · let F' := (F.erase (N + k)) ∪ (gateAt C k).inputs.toFinset
      have hF' : ∀ u ∈ F', u < N + k := by
        intro u hu
        rcases Finset.mem_union.mp hu with h1 | h2
        · have hne : u ≠ N + k := (Finset.mem_erase.mp h1).1
          have hlt : u < N + (k + 1) := hF u (Finset.mem_erase.mp h1).2
          omega
        · exact hRB k (by unfold Circuit.size at hk; omega) u (List.mem_toFinset.mp h2)
      have ih_res := ih (by omega) F' hF' hagree
      by_cases hwk : w = N + k
      · subst hwk
        have hgx := wires_gate C x (hx.symm ▸ hRB) (by omega : k < C.size)
        have hgy := wires_gate C y (hy.symm ▸ hRB) (by omega : k < C.size)
        rw [hx] at hgx
        rw [hy] at hgy
        rw [hgx, hgy]
        apply congrArg (gateAt C k).op.eval
        apply List.map_congr_left
        intro i hi
        exact ih_res i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
      · exact ih_res w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwk, hw⟩))
    · apply ih (by omega) F _ hagree w hw
      intro u hu
      have hlt : u < N + (k + 1) := hF u hu
      have hne : u ≠ N + k := fun heq => hmem (heq ▸ hu)
      omega

private def cone (N : ℕ) (C : Circuit) : Finset ℕ :=
  coneFrom N C C.size {C.output}

private theorem cone_lt {N : ℕ} {C : Circuit} (hRB : ReadsBack N C) (hout : C.output < N + C.size) :
    ∀ w ∈ cone N C, w < N :=
  coneFrom_lt hRB C.size le_rfl {C.output} (fun w hw => by rw [Finset.mem_singleton.mp hw]; exact hout)

private theorem cone_card {N : ℕ} {C : Circuit} (hF2 : FanInTwo C) :
    (cone N C).card ≤ C.size + 1 := by
  have h := coneFrom_card (N := N) hF2 C.size le_rfl {C.output}
  simpa [cone, Nat.add_comm] using h

private theorem cone_eval_eq {N : ℕ} {C : Circuit} (hRB : ReadsBack N C)
    (hout : C.output < N + C.size) {x y : List Bool} (hx : x.length = N) (hy : y.length = N)
    (hagree : ∀ w ∈ cone N C, x.getD w false = y.getD w false) :
    C.eval x = C.eval y := by
  apply coneFrom_agree hRB hx hy C.size le_rfl {C.output}
    (fun w hw => by rw [Finset.mem_singleton.mp hw]; exact hout) _ C.output (Finset.mem_singleton_self _)
  intro w hw
  have hwlt : w < N := cone_lt hRB hout w hw
  rw [show (C.wires x).getD w false = x.getD w false from wires_input C x (hx.symm ▸ hwlt),
      show (C.wires y).getD w false = y.getD w false from wires_input C y (hy.symm ▸ hwlt)]
  exact hagree w hw

/-! ### Section 4: Prefix-run alternating circuit builder (≤ min(b, a) NOTs, ≤ 6a pos gates) -/

private def notBudget : ℕ → ℕ
  | 0 => 0
  | n + 1 => 1 + notBudget ((n + 1) / 2)
termination_by n => n

private theorem notBudget_zero : notBudget 0 = 0 := by simp [notBudget]

private theorem notBudget_succ (n : ℕ) : notBudget (n + 1) = 1 + notBudget ((n + 1) / 2) := by
  rw [notBudget]

private theorem notBudget_le_self (a : ℕ) : notBudget a ≤ a := by
  induction a using Nat.strong_induction_on with
  | ind a ih =>
    cases a with
    | zero => simp [notBudget_zero]
    | succ n =>
      rw [notBudget_succ]
      have hdiv : (n + 1) / 2 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by decide)
      have := ih ((n + 1) / 2) hdiv
      omega

private theorem notBudget_le_of_lt_pow : ∀ b a : ℕ, a < 2 ^ b → notBudget a ≤ b := by
  intro b
  induction b with
  | zero =>
    intro a ha
    have : a = 0 := by omega
    subst this; simp [notBudget_zero]
  | succ b ih =>
    intro a ha
    cases a with
    | zero => simp [notBudget_zero]
    | succ n =>
      rw [notBudget_succ]
      have hdiv : (n + 1) / 2 < 2 ^ b := by
        rw [Nat.pow_succ] at ha; omega
      have := ih ((n + 1) / 2) hdiv
      omega

private def MonoChain {X : Type*} (input : X → List Bool) (C : Circuit)
    {a : ℕ} (u v : Fin a → ℕ) : Prop :=
  (∀ x i, value C (input x) (v i) ≤ value C (input x) (u i)) ∧
  (∀ x (i j : Fin a), i < j → value C (input x) (u j) ≤ value C (input x) (v i))

private theorem buildAlt {X : Type*} {N : ℕ}
    (input : X → List Bool) (hlen : ∀ x, (input x).length = N) :
    ∀ (a : ℕ) {C : Circuit} {cFalse : ℕ},
      Good N C → cFalse < nextWire N C → (∀ x, value C (input x) cFalse = false) →
      ∀ (u v : Fin a → ℕ),
        (∀ i, u i < nextWire N C) → (∀ i, v i < nextWire N C) →
        MonoChain input C u v →
        ∃ D out p, Good N D ∧ C.gates <+: D.gates ∧ out < nextWire N D ∧
          D.size = C.size + p + notBudget a ∧
          notCount D = notCount C + notBudget a ∧
          p ≤ 6 * a ∧
          ∀ x, value D (input x) out =
            decide (∃ i : Fin a, value C (input x) (u i) = true ∧ value C (input x) (v i) = false) := by
  intro a
  induction a using Nat.strong_induction_on with
  | ind a ih =>
    intro C cFalse hC hcF hFalseVal u v hu hv hmono
    cases a with
    | zero =>
      refine ⟨C, cFalse, 0, hC, List.prefix_refl _, hcF, by simp [notBudget_zero],
        by simp [notBudget_zero], by omega, ?_⟩
      intro x
      simp [hFalseVal x]
    | succ a' =>
      let a := a' + 1
      let pIdx : ℕ := a / 2
      have hp_lt : pIdx < a := Nat.div_lt_self (Nat.succ_pos a') (by decide)
      let pf : Fin a := ⟨pIdx, hp_lt⟩
      let L : ℕ := pIdx
      let R : ℕ := a - 1 - pIdx
      have hRL : R ≤ L := by dsimp only [R, L, pIdx, a]; omega
      -- Step 1: nw = !v[pf]
      obtain ⟨C1, nw, hC1, e1, hnw, s1, n1, v1⟩ := emit_not input hlen hC (hv pf)
      -- Step 2: mid = u[pf] && nw
      have hup1 : u pf < nextWire N C1 := (hu pf).trans_le (nextWire_le_of_prefix e1)
      obtain ⟨C2, mid, hC2, e2, hmid, s2, n2, v2⟩ := emit_binary input hlen hC1 true hup1 hnw
      have e12 := e1.trans e2
      -- Step 3: lu[i] = u[i] && nw (for i : Fin L)
      let uLeft : Fin L → ℕ := fun i => u ⟨i.val, by have := i.isLt; omega⟩
      let vLeft : Fin L → ℕ := fun i => v ⟨i.val, by have := i.isLt; omega⟩
      obtain ⟨C3, lu, hC3, e3, hlu, s3, n3, v3⟩ := emit_family input hlen hC2 true uLeft (fun _ => nw)
        (fun i => (hu _).trans_le (nextWire_le_of_prefix e12))
        (fun _ => hnw.trans_le (nextWire_le_of_prefix e2))
      have e13 := e12.trans e3
      -- Step 4: lv[i] = v[i] && nw (for i : Fin L)
      obtain ⟨C4, lv, hC4, e4, hlv, s4, n4, v4⟩ := emit_family input hlen hC3 true vLeft (fun _ => nw)
        (fun i => (hv _).trans_le (nextWire_le_of_prefix e13))
        (fun _ => hnw.trans_le (nextWire_le_of_prefix (e2.trans e3)))
      have e14 := e13.trans e4
      -- Step 5: u'[i] = lu[i] || uRight[i]
      let uRight : Fin L → ℕ := fun i =>
        if h : i.val < R then u ⟨pIdx + 1 + i.val, by dsimp only [R] at h; omega⟩ else cFalse
      let vRight : Fin L → ℕ := fun i =>
        if h : i.val < R then v ⟨pIdx + 1 + i.val, by dsimp only [R] at h; omega⟩ else cFalse
      have huRight : ∀ i, uRight i < nextWire N C4 := by
        intro i; dsimp only [uRight]; split_ifs with h
        · exact (hu _).trans_le (nextWire_le_of_prefix e14)
        · exact hcF.trans_le (nextWire_le_of_prefix e14)
      obtain ⟨C5, u', hC5, e5, hu', s5, n5, v5⟩ := emit_family input hlen hC4 false lu uRight
        (fun i => (hlu i).trans_le (nextWire_le_of_prefix e4)) huRight
      have e15 := e14.trans e5
      -- Step 6: v'[i] = lv[i] || vRight[i]
      have hvRight : ∀ i, vRight i < nextWire N C5 := by
        intro i; dsimp only [vRight]; split_ifs with h
        · exact (hv _).trans_le (nextWire_le_of_prefix e15)
        · exact hcF.trans_le (nextWire_le_of_prefix e15)
      obtain ⟨C6, v', hC6, e6, hv', s6, n6, v6⟩ := emit_family input hlen hC5 false lv vRight
        (fun i => (hlv i).trans_le (nextWire_le_of_prefix e5)) hvRight
      have e16 := e15.trans e6
      -- Helper evaluations of u', v', mid in C6
      have hOld (x : X) {D : Circuit} (ext : C.gates <+: D.gates) {w : ℕ} (hw : w < nextWire N C) :
          value D (input x) w = value C (input x) w :=
        wires_prefix ext (input x) (by rw [hlen x]; exact hw)
      have hu'Eval : ∀ x (i : Fin L), value C6 (input x) (u' i) =
          ((value C (input x) (u ⟨i.val, by have := i.isLt; omega⟩) && !value C (input x) (v pf)) ||
           if h : i.val < R then value C (input x) (u ⟨pIdx + 1 + i.val, by dsimp only [R] at h; omega⟩)
           else false) := by
        intro x i
        rw [wires_prefix e6 (input x) (by rw [hlen x]; exact hu' i), v5,
            wires_prefix e4 (input x) (by rw [hlen x]; exact hlu i), v3,
            hOld x e12 (hu _),
            wires_prefix e2 (input x) (by rw [hlen x]; exact hnw), v1]
        simp only [binVal, ite_true, ite_false, Bool.false_eq_true, uRight]
        split_ifs with h
        · rw [hOld x e14 (hu _)]
        · rw [hOld x e14 hcF, hFalseVal x]
      have hv'Eval : ∀ x (i : Fin L), value C6 (input x) (v' i) =
          ((value C (input x) (v ⟨i.val, by have := i.isLt; omega⟩) && !value C (input x) (v pf)) ||
           if h : i.val < R then value C (input x) (v ⟨pIdx + 1 + i.val, by dsimp only [R] at h; omega⟩)
           else false) := by
        intro x i
        rw [v6, wires_prefix e5 (input x) (by rw [hlen x]; exact hlv i), v4, hOld x e13 (hv _),
            wires_prefix (e2.trans e3) (input x) (by rw [hlen x]; exact hnw), v1]
        simp only [binVal, ite_true, ite_false, Bool.false_eq_true, vRight]
        split_ifs with h
        · rw [hOld x e15 (hv _)]
        · rw [hOld x e15 hcF, hFalseVal x]
      -- Simplified forms of u' and v' depending on v[pf]
      have hu'False : ∀ x, value C (input x) (v pf) = false → ∀ i : Fin L,
          value C6 (input x) (u' i) = value C (input x) (u ⟨i.val, by have := i.isLt; omega⟩) := by
        intro x hvp i
        rw [hu'Eval, hvp]
        split_ifs with h
        · have hle : value C (input x) (u ⟨pIdx + 1 + i.val, by dsimp only [R] at h; omega⟩) ≤
              value C (input x) (v pf) := hmono.2 x pf _ (Fin.lt_def.mpr (by dsimp only [pf]; omega))
          rw [hvp] at hle
          have hzero : value C (input x) (u ⟨pIdx + 1 + i.val, by dsimp only [R] at h; omega⟩) = false :=
            Bool.eq_false_of_le_false hle
          simp [hzero]
        · simp
      have hv'False : ∀ x, value C (input x) (v pf) = false → ∀ i : Fin L,
          value C6 (input x) (v' i) = value C (input x) (v ⟨i.val, by have := i.isLt; omega⟩) := by
        intro x hvp i
        rw [hv'Eval, hvp]
        split_ifs with h
        · have h1 := hmono.1 x ⟨pIdx + 1 + i.val, by dsimp only [R] at h; omega⟩
          have h2 := hmono.2 x pf ⟨pIdx + 1 + i.val, by dsimp only [R] at h; omega⟩ (Fin.lt_def.mpr (by dsimp only [pf]; omega))
          have hle := h1.trans h2
          rw [hvp] at hle
          have hzero : value C (input x) (v ⟨pIdx + 1 + i.val, by dsimp only [R] at h; omega⟩) = false :=
            Bool.eq_false_of_le_false hle
          simp [hzero]
        · simp
      have hu'True : ∀ x, value C (input x) (v pf) = true → ∀ i : Fin L,
          value C6 (input x) (u' i) =
            if h : i.val < R then value C (input x) (u ⟨pIdx + 1 + i.val, by dsimp only [R] at h; omega⟩)
            else false := by
        intro x hvp i
        rw [hu'Eval, hvp]; simp
      have hv'True : ∀ x, value C (input x) (v pf) = true → ∀ i : Fin L,
          value C6 (input x) (v' i) =
            if h : i.val < R then value C (input x) (v ⟨pIdx + 1 + i.val, by dsimp only [R] at h; omega⟩)
            else false := by
        intro x hvp i
        rw [hv'Eval, hvp]; simp
      -- Verify MonoChain for (u', v') in C6
      have hmono' : MonoChain input C6 u' v' := by
        constructor
        · intro x i
          cases hvp : value C (input x) (v pf)
          · rw [hu'False x hvp i, hv'False x hvp i]; exact hmono.1 x _
          · rw [hu'True x hvp i, hv'True x hvp i]
            split_ifs with h
            · exact hmono.1 x _
            · exact le_rfl
        · intro x i j hij
          cases hvp : value C (input x) (v pf)
          · rw [hu'False x hvp j, hv'False x hvp i]
            exact hmono.2 x _ _ (Fin.lt_def.mpr (Fin.lt_def.mp hij))
          · rw [hu'True x hvp j, hv'True x hvp i]
            split_ifs with hj hi
            · exact hmono.2 x _ _ (Fin.lt_def.mpr (by dsimp only; have := Fin.lt_def.mp hij; omega))
            · exfalso; exact hi ((Fin.lt_def.mp hij).trans hj)
            · exact Bool.false_le _
            · exact Bool.false_le _
      -- Step 7: Recursive call on L < a
      have hcF6 : cFalse < nextWire N C6 := hcF.trans_le (nextWire_le_of_prefix e16)
      have hFalse6 : ∀ x, value C6 (input x) cFalse = false :=
        fun x => (hOld x e16 hcF).trans (hFalseVal x)
      obtain ⟨C7, res, pRec, hC7, e7, hres, s7, n7, hpRec, v7⟩ :=
        ih L hp_lt hC6 hcF6 hFalse6 u' v'
          (fun i => (hu' i).trans_le (nextWire_le_of_prefix e6)) hv' hmono'
      -- Step 8: out = res || mid
      have e27 := (e3.trans (e4.trans (e5.trans (e6.trans e7))))
      have hmid7 : mid < nextWire N C7 := hmid.trans_le (nextWire_le_of_prefix e27)
      obtain ⟨D, out, hD, e8, hout, s8, n8, v8⟩ := emit_binary input hlen hC7 false hres hmid7
      refine ⟨D, out, pRec + 4 * L + 2, hD, (e16.trans e7).trans e8, hout, ?_, ?_, ?_, ?_⟩
      · have hnb : notBudget (a' + 1) = 1 + notBudget L := notBudget_succ a'
        omega
      · have hnb : notBudget (a' + 1) = 1 + notBudget L := notBudget_succ a'
        omega
      · cases a' with
        | zero =>
          have hL0 : L = 0 := by decide
          omega
        | succ a'' =>
          have h2L : 2 * L ≤ a := by dsimp only [L, pIdx, a]; omega
          omega
      · intro x
        rw [v8, v7, wires_prefix e27 (input x) (by rw [hlen x]; exact hmid), v2,
            hOld x e1 (hu pf), v1]
        simp only [binVal, ite_true, ite_false, Bool.false_eq_true]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
        cases hvp : value C (input x) (v pf)
        · constructor
          · rintro (⟨i, hi1, hi2⟩ | ⟨hup, _⟩)
            · rw [hu'False x hvp i] at hi1
              rw [hv'False x hvp i] at hi2
              exact ⟨⟨i.val, by have := i.isLt; omega⟩, hi1, hi2⟩
            · exact ⟨pf, hup, hvp⟩
          · rintro ⟨i, hi1, hi2⟩
            rcases lt_trichotomy i.val pIdx with hlt | heq | hgt
            · left
              refine ⟨⟨i.val, hlt⟩, ?_, ?_⟩
              · rw [hu'False x hvp]; exact hi1
              · rw [hv'False x hvp]; exact hi2
            · right
              have hpf : i = pf := Fin.ext heq
              subst hpf
              exact ⟨hi1, rfl⟩
            · exfalso
              have hle : value C (input x) (u i) ≤ value C (input x) (v pf) :=
                hmono.2 x pf i (Fin.lt_def.mpr (by dsimp only [pf]; exact hgt))
              rw [hi1, hvp] at hle
              exact (by decide : ¬(true ≤ false)) hle
        · simp only [Bool.true_eq_false, and_false, or_false]
          constructor
          · rintro ⟨i, hi1, hi2⟩
            rw [hu'True x hvp i] at hi1
            rw [hv'True x hvp i] at hi2
            split_ifs at hi1 hi2 with h
            exact ⟨⟨pIdx + 1 + i.val, by dsimp only [R] at h; omega⟩, hi1, hi2⟩
          · rintro ⟨i, hi1, hi2⟩
            by_cases hgt : pIdx < i.val
            · have hiR : i.val - (pIdx + 1) < R := by
                have := i.isLt; dsimp only [R]; omega
              have hiL : i.val - (pIdx + 1) < L := lt_of_lt_of_le hiR hRL
              refine ⟨⟨i.val - (pIdx + 1), hiL⟩, ?_, ?_⟩
              · rw [hu'True x hvp]; simp only [dite_eq_left hiR]
                have heq : (⟨pIdx + 1 + (i.val - (pIdx + 1)), by dsimp only [R] at hiR; omega⟩ : Fin a) = i :=
                  Fin.ext (by dsimp only; omega)
                rwa [heq]
              · rw [hv'True x hvp]; simp only [dite_eq_left hiR]
                have heq : (⟨pIdx + 1 + (i.val - (pIdx + 1)), by dsimp only [R] at hiR; omega⟩ : Fin a) = i :=
                  Fin.ext (by dsimp only; omega)
                rwa [heq]
            · exfalso
              have hle_vi : value C (input x) (v pf) ≤ value C (input x) (v i) := by
                by_cases heq : i.val = pIdx
                · have hpf : i = pf := Fin.ext heq; subst hpf; exact le_rfl
                · exact (hmono.1 x pf).trans (hmono.2 x i pf (Fin.lt_def.mpr (by dsimp only [pf]; omega)))
              rw [hvp, hi2] at hle_vi
              exact (by decide : ¬(true ≤ false)) hle_vi

/-! ### Section 5: Bank layout, raw encoding, and cardinality formula -/

private theorem flatten_getD_block (ls : List (List Bool)) :
    ∀ (a : ℕ) (ha : a < ls.length) (k : ℕ) (hk : k < ls[a].length),
      ls.flatten.getD (((ls.take a).map List.length).sum + k) false = ls[a][k] := by
  induction ls with
  | nil => intro a ha; cases ha
  | cons b bs ih =>
    intro a ha k hk
    cases a with
    | zero =>
      simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatten_cons]
      have hk' : k < b.length := hk
      rw [List.getD_append _ _ _ _ hk']
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
    | succ a =>
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons, Nat.add_assoc]
      rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _)]
      rw [Nat.add_sub_cancel_left]
      exact ih a (by simpa using ha) k (by simpa using hk)

private theorem flatten_decomp (ls : List (List Bool)) :
    ∀ i < ls.flatten.length,
      ∃ (a : ℕ) (ha : a < ls.length) (k : ℕ) (_ : k < ls[a].length),
        i = ((ls.take a).map List.length).sum + k := by
  induction ls with
  | nil => intro i hi; simp at hi
  | cons b bs ih =>
    intro i hi
    simp only [List.flatten_cons, List.length_append] at hi
    by_cases hlt : i < b.length
    · exact ⟨0, by simp, i, by simpa using hlt, by simp⟩
    · obtain ⟨a, ha, k, hk, heq⟩ := ih (i - b.length) (by omega)
      refine ⟨a + 1, by simpa using ha, k, by simpa using hk, ?_⟩
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      omega

private def width (d : ℕ) (w : Fin n → ℕ) (a : Fin n) : ℕ := d * w a

private def totalW (n d : ℕ) (w : Fin n → ℕ) : ℕ := Finset.univ.sum (width d w)

private def totalN (n m d : ℕ) (w : Fin n → ℕ) : ℕ := totalW n d w + 2 * m + 2

private def offset (n d : ℕ) (w : Fin n → ℕ) (a : Fin n) : ℕ :=
  ((List.ofFn (width d w)).take a.val).sum

private def pos (n d : ℕ) (w : Fin n → ℕ) (a : Fin n) (k : Fin (width d w a)) : ℕ :=
  offset n d w a + k.val

private def bankBlock (n d : ℕ) (w : Fin n → ℕ)
    (x : (a : Fin n) → Fin (width d w a) → Bool) : List Bool :=
  (List.ofFn (fun a : Fin n => List.ofFn (x a))).flatten

private def rawVec (n m d : ℕ) (w : Fin n → ℕ)
    (x : (a : Fin n) → Fin (width d w a) → Bool) (level : ℕ) : List Bool :=
  bankBlock n d w x ++ List.ofFn (fun g : Fin (2 * m) => decide (g.val < level)) ++ [false, true]

private theorem map_length_bankList (n d : ℕ) (w : Fin n → ℕ)
    (x : (a : Fin n) → Fin (width d w a) → Bool) :
    (List.ofFn (fun a : Fin n => List.ofFn (x a))).map List.length = List.ofFn (width d w) := by
  rw [List.map_ofFn]
  congr 1; funext a; exact List.length_ofFn

private theorem bankBlock_length (n d : ℕ) (w : Fin n → ℕ)
    (x : (a : Fin n) → Fin (width d w a) → Bool) :
    (bankBlock n d w x).length = totalW n d w := by
  unfold bankBlock totalW
  rw [List.length_flatten, map_length_bankList, List.sum_ofFn]

private theorem rawVec_length (n m d : ℕ) (w : Fin n → ℕ)
    (x : (a : Fin n) → Fin (width d w a) → Bool) (level : ℕ) :
    (rawVec n m d w x level).length = totalN n m d w := by
  simp [rawVec, totalN, bankBlock_length]; omega

private theorem offset_add_width_le (n d : ℕ) (w : Fin n → ℕ) {a b : Fin n} (hab : a < b) :
    offset n d w a + width d w a ≤ offset n d w b := by
  unfold offset
  let l := List.ofFn (width d w)
  have ha : a.val < l.length := by simp [l]
  have h1 : (l.take (a.val + 1)).sum = (l.take a.val).sum + l[a.val] := by
    rw [List.take_succ_eq_append_getElem ha, List.sum_append, List.sum_singleton]
  have hget : l[a.val] = width d w a := by simp [l]
  have hle : a.val + 1 ≤ b.val := Fin.lt_def.mp hab
  have h2 : (l.take (a.val + 1)).sum ≤ (l.take b.val).sum := by
    have hsplit : l.take b.val = l.take (a.val + 1) ++ (l.take b.val).drop (a.val + 1) :=
      (List.take_append_drop (a.val + 1) (l.take b.val)).symm.trans (by
        rw [List.take_take, Nat.min_eq_left hle])
    rw [hsplit, List.sum_append]
    exact Nat.le_add_right _ _
  change (l.take a.val).sum + width d w a ≤ (l.take b.val).sum
  omega

private theorem pos_lt_totalW {n d : ℕ} {w : Fin n → ℕ} (a : Fin n) (k : Fin (width d w a)) :
    pos n d w a k < totalW n d w := by
  unfold pos offset totalW
  let l := List.ofFn (width d w)
  have ha : a.val < l.length := by simp [l]
  have h1 : (l.take (a.val + 1)).sum = (l.take a.val).sum + width d w a := by
    rw [List.take_succ_eq_append_getElem ha, List.sum_append, List.sum_singleton]; simp [l]
  have h2 : (l.take (a.val + 1)).sum ≤ l.sum := by
    have hsplit := (List.take_append_drop (a.val + 1) l).symm
    conv_rhs => rw [hsplit]
    rw [List.sum_append]
    exact Nat.le_add_right _ _
  have h3 : l.sum = Finset.univ.sum (width d w) := List.sum_ofFn
  have hk := k.isLt
  change (l.take a.val).sum + k.val < Finset.univ.sum (width d w)
  omega

private theorem pos_inj {n d : ℕ} {w : Fin n → ℕ} {a1 a2 : Fin n}
    {k1 : Fin (width d w a1)} {k2 : Fin (width d w a2)}
    (heq : pos n d w a1 k1 = pos n d w a2 k2) : a1 = a2 ∧ k1.val = k2.val := by
  rcases lt_trichotomy a1 a2 with hlt | rfl | hgt
  · have h := offset_add_width_le n d w hlt
    have hk := k1.isLt
    unfold pos at heq; omega
  · unfold pos at heq; exact ⟨rfl, by omega⟩
  · have h := offset_add_width_le n d w hgt
    have hk := k2.isLt
    unfold pos at heq; omega

private theorem bankBlock_getD (n d : ℕ) (w : Fin n → ℕ)
    (x : (a : Fin n) → Fin (width d w a) → Bool) (a : Fin n) (k : Fin (width d w a)) :
    (bankBlock n d w x).getD (pos n d w a k) false = x a k := by
  let ls := List.ofFn (fun a : Fin n => List.ofFn (x a))
  have ha : a.val < ls.length := by simp [ls]
  have hls_a : ls[a.val] = List.ofFn (x a) := by simp [ls]
  have hk : k.val < ls[a.val].length := by rw [hls_a, List.length_ofFn]; exact k.isLt
  have hmap : (ls.take a.val).map List.length = (List.ofFn (width d w)).take a.val := by
    rw [List.map_take, map_length_bankList]
  have h := flatten_getD_block ls a.val ha k.val hk
  rw [hmap] at h
  change ls.flatten.getD (offset n d w a + k.val) false = x a k
  unfold offset
  rw [h]
  simp [ls]

private theorem bankBlock_decomp (n d : ℕ) (w : Fin n → ℕ) {i : ℕ} (hi : i < totalW n d w) :
    ∃ (a : Fin n) (k : Fin (width d w a)), i = pos n d w a k := by
  let x0 : (a : Fin n) → Fin (width d w a) → Bool := fun _ _ => false
  let ls := List.ofFn (fun a : Fin n => List.ofFn (x0 a))
  have hlen : ls.flatten.length = totalW n d w := bankBlock_length n d w x0
  obtain ⟨a, ha, k, hk, heq⟩ := flatten_decomp ls i (hlen.symm ▸ hi)
  have ha' : a < n := by simpa [ls] using ha
  let af : Fin n := ⟨a, ha'⟩
  have hls_a : ls[a] = List.ofFn (x0 af) := by simp [ls, af]
  have hk' : k < width d w af := by rw [hls_a, List.length_ofFn] at hk; exact hk
  have hmap : (ls.take a).map List.length = (List.ofFn (width d w)).take a := by
    rw [List.map_take, map_length_bankList]
  rw [hmap] at heq
  exact ⟨af, ⟨k, hk'⟩, heq⟩

private theorem rawVec_getD_bank (n m d : ℕ) (w : Fin n → ℕ)
    (x : (a : Fin n) → Fin (width d w a) → Bool) (level : ℕ) (a : Fin n) (k : Fin (width d w a)) :
    (rawVec n m d w x level).getD (pos n d w a k) false = x a k := by
  unfold rawVec
  rw [List.append_assoc, List.getD_append _ _ _ _ (by rw [bankBlock_length]; exact pos_lt_totalW a k)]
  exact bankBlock_getD n d w x a k

private theorem rawVec_getD_level (n m d : ℕ) (w : Fin n → ℕ)
    (x : (a : Fin n) → Fin (width d w a) → Bool) (level : ℕ) (g : Fin (2 * m)) :
    (rawVec n m d w x level).getD (totalW n d w + g.val) false = decide (g.val < level) := by
  unfold rawVec
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by rw [bankBlock_length]; omega)]
  rw [bankBlock_length, Nat.add_sub_cancel_left]
  rw [List.getD_append _ _ _ _ (by rw [List.length_ofFn]; exact g.isLt)]
  exact getD_ofFn_lt (fun g : Fin (2 * m) => decide (g.val < level)) false g.isLt

private theorem rawVec_getD_false (n m d : ℕ) (w : Fin n → ℕ)
    (x : (a : Fin n) → Fin (width d w a) → Bool) (level : ℕ) :
    (rawVec n m d w x level).getD (totalW n d w + 2 * m) false = false := by
  unfold rawVec
  have hlen : (bankBlock n d w x ++ List.ofFn (fun g : Fin (2 * m) => decide (g.val < level))).length =
      totalW n d w + 2 * m := by simp [bankBlock_length]
  rw [List.getD_append_right _ _ _ _ (by omega : _ ≤ totalW n d w + 2 * m)]
  rw [hlen, Nat.sub_self]
  rfl

private theorem rawVec_getD_true (n m d : ℕ) (w : Fin n → ℕ)
    (x : (a : Fin n) → Fin (width d w a) → Bool) (level : ℕ) :
    (rawVec n m d w x level).getD (totalW n d w + 2 * m + 1) false = true := by
  unfold rawVec
  have hlen : (bankBlock n d w x ++ List.ofFn (fun g : Fin (2 * m) => decide (g.val < level))).length =
      totalW n d w + 2 * m := by simp [bankBlock_length]
  rw [List.getD_append_right _ _ _ _ (by omega : _ ≤ totalW n d w + 2 * m + 1)]
  rw [hlen]
  have hsub : totalW n d w + 2 * m + 1 - (totalW n d w + 2 * m) = 1 := by omega
  rw [hsub]
  rfl

private theorem rawVec_inj {n m d : ℕ} {w : Fin n → ℕ}
    {x1 x2 : (a : Fin n) → Fin (width d w a) → Bool} {l1 l2 : ℕ}
    (hl1 : l1 ≤ 2 * m) (hl2 : l2 ≤ 2 * m)
    (heq : rawVec n m d w x1 l1 = rawVec n m d w x2 l2) : x1 = x2 ∧ l1 = l2 := by
  constructor
  · funext a k
    have h := congrArg (fun v => v.getD (pos n d w a k) false) heq
    rw [rawVec_getD_bank, rawVec_getD_bank] at h; exact h
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h := congrArg (fun v => v.getD (totalW n d w + l1) false) heq
      have h1 := rawVec_getD_level n m d w x1 l1 ⟨l1, by omega⟩
      have h2 := rawVec_getD_level n m d w x2 l2 ⟨l1, by omega⟩
      dsimp only at h1 h2
      rw [h1, h2] at h
      simp [hlt] at h
    · have h := congrArg (fun v => v.getD (totalW n d w + l2) false) heq
      have h1 := rawVec_getD_level n m d w x1 l1 ⟨l2, by omega⟩
      have h2 := rawVec_getD_level n m d w x2 l2 ⟨l2, by omega⟩
      dsimp only at h1 h2
      rw [h1, h2] at h
      simp [hgt] at h

private theorem rawVec_empty_order (n m d : ℕ) (w : Fin n → ℕ) {l1 l2 : ℕ} (hl : l1 ≤ l2) :
    bitOrder (rawVec n m d w (fun _ _ => false) l1) (rawVec n m d w (fun _ _ => false) l2) := by
  refine ⟨by simp [rawVec_length], ?_⟩
  intro i
  by_cases h1 : i < totalW n d w
  · obtain ⟨a, k, rfl⟩ := bankBlock_decomp n d w h1
    rw [rawVec_getD_bank, rawVec_getD_bank]
  · by_cases h2 : i < totalW n d w + 2 * m
    · let g : Fin (2 * m) := ⟨i - totalW n d w, by omega⟩
      have hi : i = totalW n d w + g.val := by dsimp only [g]; omega
      rw [hi, rawVec_getD_level, rawVec_getD_level]
      apply (bool_order _ _).mpr
      simp only [decide_eq_true_eq]
      omega
    · by_cases h3 : i = totalW n d w + 2 * m
      · subst h3; rw [rawVec_getD_false, rawVec_getD_false]
      · by_cases h4 : i = totalW n d w + 2 * m + 1
        · subst h4; rw [rawVec_getD_true, rawVec_getD_true]
        · have hge : totalN n m d w ≤ i := by unfold totalN; omega
          rw [List.getD_eq_default _ _ (by rw [rawVec_length]; exact hge),
              List.getD_eq_default _ _ (by rw [rawVec_length]; exact hge)]

private def zerosSet (n m d : ℕ) (w : Fin n → ℕ) : Finset (List Bool × Bool) :=
  (Finset.univ : Finset (Fin m)).image (fun j => (rawVec n m d w (fun _ _ => false) (2 * j.val + 1), false))

private def copyVec (n m d : ℕ) (w : Fin n → ℕ) (j : Fin m) (M : Finset (Fin n))
    (f : (a : {a : Fin n // a ∈ M}) → Fin (width d w a.val)) : List Bool :=
  rawVec n m d w (fun a k => if h : a ∈ M then decide (f ⟨a, h⟩ = k) else false) (2 * j.val)

private def copiesSet (n m d : ℕ) (w : Fin n → ℕ) (j : Fin m) (M : Finset (Fin n)) :
    Finset (List Bool × Bool) :=
  Finset.univ.image (fun f : (a : {a : Fin n // a ∈ M}) → Fin (width d w a.val) =>
    (copyVec n m d w j M f, true))

private def posRows (n m d : ℕ) (w : Fin n → ℕ) (E : Fin m → Finset (Finset (Fin n))) :
    Finset (List Bool × Bool) :=
  Finset.univ.biUnion (fun j => (E j).biUnion (copiesSet n m d w j))

private def rowsSet (n m d : ℕ) (w : Fin n → ℕ) (E : Fin m → Finset (Finset (Fin n))) :
    Finset (List Bool × Bool) :=
  zerosSet n m d w ∪ posRows n m d w E

private theorem card_zerosSet (n m d : ℕ) (w : Fin n → ℕ) :
    (zerosSet n m d w).card = m := by
  unfold zerosSet
  rw [Finset.card_image_of_injective]
  · simp
  · intro j1 j2 heq
    have h1 := congrArg Prod.fst heq
    dsimp only at h1
    have h := (rawVec_inj (by have := j1.isLt; omega) (by have := j2.isLt; omega) h1).2
    exact Fin.ext (by omega)

private theorem card_copiesSet (n m d : ℕ) (w : Fin n → ℕ) (j : Fin m) (M : Finset (Fin n)) :
    (copiesSet n m d w j M).card = M.prod (width d w) := by
  unfold copiesSet
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin]
    exact Finset.prod_coe_sort M (width d w)
  · intro f1 f2 heq
    have h1 := congrArg Prod.fst heq
    dsimp only [copyVec] at h1
    have hx := (rawVec_inj (by have := j.isLt; omega) (by have := j.isLt; omega) h1).1
    funext ⟨a, ha⟩
    have hbit := congrFun (congrFun hx a) (f1 ⟨a, ha⟩)
    simp [ha] at hbit
    exact hbit.symm

private theorem card_rowsSet (n m d : ℕ) (w : Fin n → ℕ) (E : Fin m → Finset (Finset (Fin n))) :
    (rowsSet n m d w E).card = m + ∑ j, (E j).sum (fun M => M.prod (width d w)) := by
  unfold rowsSet
  have hdisj0 : Disjoint (zerosSet n m d w) (posRows n m d w E) := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [zerosSet, Finset.mem_image, Finset.mem_univ, true_and] at hz1
    simp only [posRows, copiesSet, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image] at hz2
    obtain ⟨_, rfl⟩ := hz1
    obtain ⟨_, _, _, _, heq⟩ := hz2
    have := congrArg Prod.snd heq
    cases this
  rw [Finset.card_union_of_disjoint hdisj0, card_zerosSet]
  congr 1
  unfold posRows
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro j _
    rw [Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro M _
      exact card_copiesSet n m d w j M
    · intro M1 _ M2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      simp only [copiesSet, Finset.mem_image, Finset.mem_univ, true_and] at hz1 hz2
      obtain ⟨f1, rfl⟩ := hz1
      obtain ⟨f2, heq⟩ := hz2
      have h1 := congrArg Prod.fst heq
      dsimp only [copyVec] at h1
      have hx := (rawVec_inj (by have := j.isLt; omega) (by have := j.isLt; omega) h1).1
      apply hne
      ext a
      constructor
      · intro ha1
        have hbit := congrFun (congrFun hx a) (f1 ⟨a, ha1⟩)
        simp only [dite_eq_left ha1, decide_true] at hbit
        by_contra ha2
        simp [ha2] at hbit
      · intro ha2
        have hbit := congrFun (congrFun hx a) (f2 ⟨a, ha2⟩)
        simp only [dite_eq_left ha2, decide_true] at hbit
        by_contra ha1
        simp [ha1] at hbit
  · intro j1 _ j2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    simp only [Finset.mem_biUnion, copiesSet, Finset.mem_image, Finset.mem_univ, true_and] at hz1 hz2
    obtain ⟨M1, _, f1, rfl⟩ := hz1
    obtain ⟨M2, _, f2, heq⟩ := hz2
    have h1 := congrArg Prod.fst heq
    dsimp only [copyVec] at h1
    have hl := (rawVec_inj (by have := j1.isLt; omega) (by have := j2.isLt; omega) h1).2
    exact hne (Fin.ext (by omega))

/-! ### Section 6: Necessity and sufficiency -/

private noncomputable def missedSet (n m : ℕ) (E : Fin m → Finset (Finset (Fin n)))
    (S : Finset (Fin n)) : Finset (Fin m) :=
  letI := Classical.propDecidable
  (Finset.univ : Finset (Fin m)).filter (fun j => ∃ M ∈ E j, Disjoint M S)

private theorem necessity {n m d b k : ℕ} {w : Fin n → ℕ}
    {E : Fin m → Finset (Finset (Fin n))} (hd : 7 * m + 2 ≤ d)
    (C : Circuit) (hF2 : FanInTwo C) (hRB : ReadsBack (totalN n m d w) C)
    (hout : C.output < totalN n m d w + C.size) (hnot : notCount C ≤ b)
    (hsize : C.size ≤ d * k + 7 * m)
    (hfit : ∀ z ∈ rowsSet n m d w E, C.eval z.1 = z.2) :
    ∃ S : Finset (Fin n), S.sum w ≤ k ∧ (missedSet n m E S).card < 2 ^ b := by
  classical
  let N := totalN n m d w
  let I := cone N C
  let S : Finset (Fin n) := Finset.univ.filter (fun a => ∀ t : Fin (width d w a), pos n d w a t ∈ I)
  refine ⟨S, ?_, ?_⟩
  · -- Weight bound: d * S.sum w ≤ I.card ≤ C.size + 1 ≤ d * k + 7 * m + 1 < d * (k + 1)
    let bankWires (a : Fin n) : Finset ℕ := Finset.univ.image (pos n d w a)
    have hsub : S.biUnion bankWires ⊆ I := by
      intro u hu
      simp only [Finset.mem_biUnion, bankWires, Finset.mem_image, Finset.mem_univ, true_and] at hu
      obtain ⟨a, haS, t, rfl⟩ := hu
      exact (Finset.mem_filter.mp haS).2 t
    have hdisj : Set.PairwiseDisjoint (S : Set (Fin n)) bankWires := by
      intro a1 _ a2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      simp only [bankWires, Finset.mem_image, Finset.mem_univ, true_and] at hu1 hu2
      obtain ⟨t1, rfl⟩ := hu1
      obtain ⟨t2, heq⟩ := hu2
      exact hne (pos_inj heq.symm).1
    have hcard_bw : ∀ a : Fin n, (bankWires a).card = width d w a := by
      intro a
      unfold bankWires
      rw [Finset.card_image_of_injective]
      · simp
      · intro t1 t2 heq
        exact Fin.ext (pos_inj heq).2
    have hsum_le : S.sum (width d w) ≤ I.card := by
      calc S.sum (width d w)
          = S.sum (fun a => (bankWires a).card) := Finset.sum_congr rfl (fun a _ => (hcard_bw a).symm)
        _ = (S.biUnion bankWires).card := (Finset.card_biUnion hdisj).symm
        _ ≤ I.card := Finset.card_le_card hsub
    have hmul : S.sum (width d w) = d * S.sum w := by
      unfold width; rw [← Finset.mul_sum]
    have hI : I.card ≤ C.size + 1 := cone_card hF2
    have hlt : d * S.sum w < d * (k + 1) := by
      have : d * S.sum w ≤ d * k + 7 * m + 1 := by omega
      have : d * (k + 1) = d * k + d := by rw [Nat.mul_add, Nat.mul_one]
      omega
    have hlt' : S.sum w < k + 1 := Nat.lt_of_mul_lt_mul_left hlt
    omega
  · -- Missed-family bound via Markov grade on the monotone empty-bank chain
    let A := missedSet n m E S
    let e (l : ℕ) : List Bool := rawVec n m d w (fun _ _ => false) l
    have hfall : ∀ j ∈ A, grade C (e (2 * j.val)) < grade C (e (2 * j.val + 1)) := by
      intro j hj
      have hj' : ∃ M ∈ E j, Disjoint M S := by
        simpa [A, missedSet] using hj
      obtain ⟨M, hME, hdisj⟩ := hj'
      have hunseen : ∀ a : {a : Fin n // a ∈ M}, ∃ t : Fin (width d w a.val), pos n d w a.val t ∉ I := by
        intro ⟨a, haM⟩
        have haS : a ∉ S := Finset.disjoint_left.mp hdisj haM
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at haS
        exact haS
      let f : (a : {a : Fin n // a ∈ M}) → Fin (width d w a.val) := fun a => Classical.choose (hunseen a)
      have hf_spec : ∀ a : {a : Fin n // a ∈ M}, pos n d w a.val (f a) ∉ I :=
        fun a => Classical.choose_spec (hunseen a)
      have hmem_row : (copyVec n m d w j M f, true) ∈ rowsSet n m d w E := by
        apply Finset.mem_union_right
        unfold posRows
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
          Finset.mem_biUnion.mpr ⟨M, hME,
            Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩⟩⟩
      have hpos : C.eval (copyVec n m d w j M f) = true := hfit _ hmem_row
      have hagree : C.eval (e (2 * j.val)) = C.eval (copyVec n m d w j M f) := by
        apply cone_eval_eq hRB hout (rawVec_length ..) (rawVec_length ..)
        intro u hu
        by_cases hltW : u < totalW n d w
        · obtain ⟨a, t, rfl⟩ := bankBlock_decomp n d w hltW
          dsimp only [e, copyVec]
          rw [rawVec_getD_bank, rawVec_getD_bank]
          split_ifs with haM
          · have hne : f ⟨a, haM⟩ ≠ t := fun heq => hf_spec ⟨a, haM⟩ (heq ▸ hu)
            simp [hne]
          · rfl
        · by_cases hltL : u < totalW n d w + 2 * m
          · let g : Fin (2 * m) := ⟨u - totalW n d w, by omega⟩
            have hu_eq : u = totalW n d w + g.val := by dsimp only [g]; omega
            rw [hu_eq]
            dsimp only [e, copyVec]
            rw [rawVec_getD_level, rawVec_getD_level]
          · by_cases hF : u = totalW n d w + 2 * m
            · subst hF; dsimp only [e, copyVec]; rw [rawVec_getD_false, rawVec_getD_false]
            · by_cases hT : u = totalW n d w + 2 * m + 1
              · subst hT; dsimp only [e, copyVec]; rw [rawVec_getD_true, rawVec_getD_true]
              · have huN : u < N := cone_lt hRB hout u hu
                exfalso; unfold N totalN at huN; omega
      have heven : C.eval (e (2 * j.val)) = true := hagree.trans hpos
      have hmem_zero : (e (2 * j.val + 1), false) ∈ rowsSet n m d w E := by
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      have hodd : C.eval (e (2 * j.val + 1)) = false := hfit _ hmem_zero
      exact grade_fall hF2 (rawVec_empty_order n m d w (by omega)) heven hodd
    let gFn : Fin m → ℕ := fun j => grade C (e (2 * j.val))
    have hinj : Set.InjOn gFn (A : Set (Fin m)) := by
      intro j1 hj1 j2 hj2 heq
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
      · have h1 := hfall j1 hj1
        have h2 : grade C (e (2 * j1.val + 1)) ≤ grade C (e (2 * j2.val)) :=
          (grade_order hF2 (rawVec_empty_order n m d w (by omega : 2 * j1.val + 1 ≤ 2 * j2.val))).1
        dsimp only [gFn] at heq
        omega
      · have h1 := hfall j2 hj2
        have h2 : grade C (e (2 * j2.val + 1)) ≤ grade C (e (2 * j1.val)) :=
          (grade_order hF2 (rawVec_empty_order n m d w (by omega : 2 * j2.val + 1 ≤ 2 * j1.val))).1
        dsimp only [gFn] at heq
        omega
    have hmaps : ∀ j ∈ A, gFn j ∈ Finset.range (2 ^ b - 1) := by
      intro j hj
      rw [Finset.mem_range]
      have h1 := hfall j hj
      have h2 := (grade_bound C (e (2 * j.val + 1))).trans_le
        (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hnot)
      dsimp only [gFn]
      omega
    have hcard : A.card ≤ (Finset.range (2 ^ b - 1)).card :=
      Finset.card_le_card_of_injOn gFn hmaps hinj
    rw [Finset.card_range] at hcard
    have hpow : 0 < 2 ^ b := Nat.two_pow_pos b
    change A.card < 2 ^ b
    omega

private theorem sufficiency {n m d b k : ℕ} {w : Fin n → ℕ}
    {E : Fin m → Finset (Finset (Fin n))}
    (S : Finset (Fin n)) (hSw : S.sum w ≤ k) (hA : (missedSet n m E S).card < 2 ^ b) :
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack (totalN n m d w) C ∧
      C.output < totalN n m d w + C.size ∧ notCount C ≤ b ∧ C.size ≤ d * k + 7 * m ∧
      ∀ z ∈ rowsSet n m d w E, C.eval z.1 = z.2 := by
  classical
  let N := totalN n m d w
  let W := totalW n d w
  let A := missedSet n m E S
  let jsList : List (Fin m) := (List.finRange m).filter (fun j => decide (j ∈ A))
  have hjs_pair : jsList.Pairwise (· < ·) :=
    (List.pairwise_lt_finRange m).filter _
  have hjs_nodup : jsList.Nodup := hjs_pair.imp (fun h => ne_of_lt h)
  have hjs_mem : ∀ j : Fin m, j ∈ jsList ↔ j ∈ A := by
    intro j; simp [jsList]
  have hjs_len : jsList.length = A.card := by
    have htf : jsList.toFinset = A := by
      ext j; simp [hjs_mem]
    rw [← htf, List.toFinset_card_of_nodup hjs_nodup]
  let a := jsList.length
  have ha_le_m : a ≤ m := by
    change jsList.length ≤ m
    rw [hjs_len]
    calc A.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = m := by simp
  have ha_lt_pow : a < 2 ^ b := by
    change jsList.length < 2 ^ b
    rw [hjs_len]
    exact hA
  let js : Fin a → Fin m := fun i => jsList[i.val]'i.isLt
  have hjs_lt : ∀ i1 i2 : Fin a, i1 < i2 → js i1 < js i2 := by
    intro i1 i2 hlt
    exact (List.pairwise_iff_getElem.mp hjs_pair) i1.val i2.val i1.isLt i2.isLt hlt
  -- Build input wires u, v on emptyCircuit over type X = ((a : Fin n) → Fin (width d w a) → Bool) × Nat
  let X := ((x : Fin n) → Fin (width d w x) → Bool) × ℕ
  let inp : X → List Bool := fun p => rawVec n m d w p.1 p.2
  have hlen : ∀ p : X, (inp p).length = N := fun p => rawVec_length n m d w p.1 p.2
  let cFalse : ℕ := W + 2 * m
  let cTrue : ℕ := W + 2 * m + 1
  have hcF_lt : cFalse < nextWire N emptyCircuit := by
    simp [cFalse, nextWire, emptyCircuit, Circuit.size, N, totalN, W]
  have hcT_lt : cTrue < nextWire N emptyCircuit := by
    simp [cTrue, nextWire, emptyCircuit, Circuit.size, N, totalN, W]
  have hcF_val : ∀ p : X, value emptyCircuit (inp p) cFalse = false := by
    intro p
    rw [wires_input emptyCircuit (inp p) (by rw [hlen p]; simpa [nextWire, emptyCircuit, Circuit.size] using hcF_lt)]
    exact rawVec_getD_false n m d w p.1 p.2
  have hcT_val : ∀ p : X, value emptyCircuit (inp p) cTrue = true := by
    intro p
    rw [wires_input emptyCircuit (inp p) (by rw [hlen p]; simpa [nextWire, emptyCircuit, Circuit.size] using hcT_lt)]
    exact rawVec_getD_true n m d w p.1 p.2
  let u : Fin a → ℕ := fun i => if (js i).val = 0 then cTrue else W + (2 * (js i).val - 1)
  let v : Fin a → ℕ := fun i => W + 2 * (js i).val
  have hu_lt : ∀ i, u i < nextWire N emptyCircuit := by
    intro i; dsimp only [u]; split_ifs with h
    · exact hcT_lt
    · have := (js i).isLt
      simp only [nextWire, emptyCircuit, Circuit.size, N, totalN, W]; omega
  have hv_lt : ∀ i, v i < nextWire N emptyCircuit := by
    intro i
    have := (js i).isLt
    simp only [v, nextWire, emptyCircuit, Circuit.size, N, totalN, W]; omega
  have hu_val : ∀ p : X, ∀ i : Fin a, value emptyCircuit (inp p) (u i) = decide (2 * (js i).val ≤ p.2) := by
    intro p i
    dsimp only [u]
    split_ifs with h0
    · rw [hcT_val p, h0]; simp
    · have hlt : 2 * (js i).val - 1 < 2 * m := by have := (js i).isLt; omega
      rw [wires_input emptyCircuit (inp p) (by rw [hlen p]; unfold N totalN W; omega)]
      have h := rawVec_getD_level n m d w p.1 p.2 ⟨2 * (js i).val - 1, hlt⟩
      dsimp only at h
      change (rawVec n m d w p.1 p.2).getD (totalW n d w + (2 * (js i).val - 1)) false = _
      rw [h]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      omega
  have hv_val : ∀ p : X, ∀ i : Fin a, value emptyCircuit (inp p) (v i) = decide (2 * (js i).val < p.2) := by
    intro p i
    have hlt : 2 * (js i).val < 2 * m := by have := (js i).isLt; omega
    rw [wires_input emptyCircuit (inp p) (by rw [hlen p]; unfold v N totalN W; omega)]
    exact rawVec_getD_level n m d w p.1 p.2 ⟨2 * (js i).val, hlt⟩
  have hmono : MonoChain inp emptyCircuit u v := by
    constructor
    · intro p i
      rw [hu_val, hv_val]
      apply (bool_order _ _).mpr
      simp only [decide_eq_true_eq]; omega
    · intro p i1 i2 hlt
      rw [hu_val, hv_val]
      have hjl : (js i1).val < (js i2).val := hjs_lt i1 i2 hlt
      apply (bool_order _ _).mpr
      simp only [decide_eq_true_eq]; omega
  -- Build level-marking circuit C1
  obtain ⟨C1, w1, p1, hC1, e1, hw1, s1, n1, hp1, v1⟩ :=
    buildAlt inp hlen a (emptyCircuit_good N) hcF_lt hcF_val u v hu_lt hv_lt hmono
  -- Build list of all wires in banks a ∈ S
  let sList : List (Fin n) := (List.finRange n).filter (fun x => decide (x ∈ S))
  have hs_nodup : sList.Nodup := (List.nodup_finRange n).filter _
  have hs_mem : ∀ x : Fin n, x ∈ sList ↔ x ∈ S := by intro x; simp [sList]
  let wsS : List ℕ := sList.flatMap (fun x => (List.finRange (width d w x)).map (pos n d w x))
  have hwsS_lt : ∀ u ∈ wsS, u < nextWire N C1 := by
    intro u hu
    simp only [wsS, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hu
    obtain ⟨x, _, t, rfl⟩ := hu
    have hlt : pos n d w x t < N := (pos_lt_totalW x t).trans (by unfold N totalN; omega)
    unfold nextWire; omega
  have hwsS_len : wsS.length = d * S.sum w := by
    have h1 : wsS.length = (sList.map (width d w)).sum := by
      simp [wsS, List.length_flatMap]
    have h2 : (sList.map (width d w)).sum = S.sum (width d w) := by
      have htf : sList.toFinset = S := by ext x; simp [hs_mem]
      rw [← htf, List.sum_toFinset _ hs_nodup]
    rw [h1, h2]
    unfold width; rw [← Finset.mul_sum]
  -- Append OR gates for all wires in wsS
  obtain ⟨C2, w2, hC2, e2, hw2, s2, n2, v2⟩ := emit_any inp hlen wsS hC1 hw1 hwsS_lt
  let C : Circuit := ⟨C2.gates, w2⟩
  refine ⟨C, hC2.1, hC2.2, hw2, ?_, ?_, ?_⟩
  · -- notCount C ≤ b
    have hn0 : notCount emptyCircuit = 0 := rfl
    have hnb : notBudget a ≤ b := notBudget_le_of_lt_pow b a ha_lt_pow
    change notCount C2 ≤ b
    omega
  · -- C.size ≤ d * k + 7 * m
    have hs0 : emptyCircuit.size = 0 := rfl
    have hnb_a : notBudget a ≤ a := notBudget_le_self a
    have hdk : d * S.sum w ≤ d * k := Nat.mul_le_mul_left d hSw
    change C2.size ≤ d * k + 7 * m
    omega
  · -- Correctness on all z ∈ rowsSet
    intro z hz
    have heval : ∀ p : X, C.eval (inp p) =
        (decide (∃ i : Fin a, 2 * (js i).val = p.2) ||
         wsS.any (fun u => (inp p).getD u false)) := by
      intro p
      change value C2 (inp p) w2 = _
      rw [v2, v1]
      have hleft : decide (∃ i : Fin a, value emptyCircuit (inp p) (u i) = true ∧
          value emptyCircuit (inp p) (v i) = false) =
          decide (∃ i : Fin a, 2 * (js i).val = p.2) := by
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, hu_val, hv_val, decide_eq_false_iff_not]
        constructor <;> rintro ⟨i, hi⟩ <;> exact ⟨i, by omega⟩
      have hright : wsS.any (value C1 (inp p)) = wsS.any (fun u => (inp p).getD u false) := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true]
        constructor <;> rintro ⟨u, hu, hval⟩
        · simp only [wsS, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hu
          obtain ⟨x, hxS, t, rfl⟩ := hu
          have hlt : pos n d w x t < (inp p).length := by
            rw [hlen p]; exact (pos_lt_totalW x t).trans (by unfold N totalN; omega)
          exact ⟨pos n d w x t, by
            simp only [wsS, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
            exact ⟨x, hxS, t, rfl⟩, (wires_input C1 (inp p) hlt).symm.trans hval⟩
        · simp only [wsS, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hu
          obtain ⟨x, hxS, t, rfl⟩ := hu
          have hlt : pos n d w x t < (inp p).length := by
            rw [hlen p]; exact (pos_lt_totalW x t).trans (by unfold N totalN; omega)
          exact ⟨pos n d w x t, by
            simp only [wsS, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
            exact ⟨x, hxS, t, rfl⟩, (wires_input C1 (inp p) hlt).trans hval⟩
      rw [hleft, hright]
    rcases Finset.mem_union.mp hz with hz0 | hz1
    · -- z ∈ zerosSet
      simp only [zerosSet, Finset.mem_image, Finset.mem_univ, true_and] at hz0
      obtain ⟨j, rfl⟩ := hz0
      change C.eval (inp (fun _ _ => false, 2 * j.val + 1)) = false
      rw [heval]
      have h1 : decide (∃ i : Fin a, 2 * (js i).val = 2 * j.val + 1) = false := by
        simp only [decide_eq_false_iff_not, not_exists]; intro i; omega
      have h2 : wsS.any (fun u => (inp (fun _ _ => false, 2 * j.val + 1)).getD u false) = false := by
        rw [List.any_eq_false]
        intro u hu
        simp only [wsS, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hu
        obtain ⟨x, _, t, rfl⟩ := hu
        dsimp only [inp]; rw [rawVec_getD_bank]; decide
      rw [h1, h2]; rfl
    · -- z ∈ posRows
      simp only [posRows, copiesSet, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image] at hz1
      obtain ⟨j, M, hME, f, rfl⟩ := hz1
      let xf : (x : Fin n) → Fin (width d w x) → Bool :=
        fun x t => if h : x ∈ M then decide (f ⟨x, h⟩ = t) else false
      change C.eval (inp (xf, 2 * j.val)) = true
      rw [heval]
      by_cases hjA : j ∈ A
      · have hjmem : j ∈ jsList := (hjs_mem j).mpr hjA
        obtain ⟨idx, hidx, hget⟩ := List.getElem_of_mem hjmem
        have h1 : decide (∃ i : Fin a, 2 * (js i).val = 2 * j.val) = true := by
          rw [decide_eq_true_eq]
          exact ⟨⟨idx, hidx⟩, by simp [js, hget]⟩
        rw [h1]; rfl
      · have hnotdisj : ¬ Disjoint M S := by
          intro hdisj
          apply hjA
          simp only [A, missedSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨M, hME, hdisj⟩
        obtain ⟨x, hxM, hxS⟩ := Finset.not_disjoint_iff.mp hnotdisj
        let t := f ⟨x, hxM⟩
        have htmem : pos n d w x t ∈ wsS := by
          simp only [wsS, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
          exact ⟨x, (hs_mem x).mpr hxS, t, rfl⟩
        have h2 : wsS.any (fun u => (inp (xf, 2 * j.val)).getD u false) = true := by
          rw [List.any_eq_true]
          refine ⟨pos n d w x t, htmem, ?_⟩
          dsimp only [inp]; rw [rawVec_getD_bank]
          simp [xf, hxM, t]
        rw [h2]; simp

/-! ### Section 7: Bridge to Classical.propDecidable -/

private theorem solve (n m d : ℕ) (w : Fin n → ℕ) (E : Fin m → Finset (Finset (Fin n)))
    (hd : 7 * m + 2 ≤ d) :
    (rowsSet n m d w E).card = m + ∑ j, (E j).sum (fun M => M.prod (width d w)) ∧
      ∀ b k : ℕ,
        (∃ C : Circuit, FanInTwo C ∧ ReadsBack (totalN n m d w) C ∧
          C.output < totalN n m d w + C.size ∧ notCount C ≤ b ∧ C.size ≤ d * k + 7 * m ∧
          ∀ z ∈ rowsSet n m d w E, C.eval z.1 = z.2) ↔
        ∃ S : Finset (Fin n), S.sum w ≤ k ∧ (missedSet n m E S).card < 2 ^ b := by
  refine ⟨card_rowsSet n m d w E, fun b k => ⟨?_, ?_⟩⟩
  · rintro ⟨C, hF2, hRB, hout, hnot, hsize, hfit⟩
    exact necessity hd C hF2 hRB hout hnot hsize hfit
  · rintro ⟨S, hSw, hA⟩
    exact sufficiency S hSw hA

end PEqualNP.Outside.L_lib_1356_aux

open PEqualNP.Outside.L_lib_1356_aux in
theorem PEqualNP.Outside.L_lib_1356 :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n m d : Nat) (w : Fin n → Nat) (E : Fin m → Finset (Finset (Fin n))),
  7*m+2 ≤ d →
  let width := fun a : Fin n => d*w a
  let N := Finset.univ.sum width + 2*m + 2
  let raw := fun (x : (a : Fin n) → Fin (width a) → Bool) (level : Nat) =>
    (List.ofFn (fun a : Fin n => List.ofFn (x a))).flatten ++
    List.ofFn (fun g : Fin (2*m) => decide (g.val < level)) ++ [false,true]
  let zeros := (Finset.univ : Finset (Fin m)).image
    (fun j => (raw (fun _ _ => false) (2*j.val+1), false))
  let copies := fun (j : Fin m) (M : Finset (Fin n)) =>
    Finset.univ.image (fun f : (a : {a : Fin n // a ∈ M}) → Fin (width a.val) =>
      (raw (fun a k => if h : a ∈ M then decide (f ⟨a,h⟩ = k) else false) (2*j.val), true))
  let rows := zeros ∪ Finset.univ.biUnion (fun j => (E j).biUnion (copies j))
  rows.card = m + ∑ j, (E j).sum (fun M => M.prod width) ∧
    ∀ b k : Nat,
      (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack N C ∧ C.output < N+C.size ∧
        PEqualNP.NotBracket.notCount C ≤ b ∧ C.size ≤ d*k+7*m ∧
        ∀ z ∈ rows, C.eval z.1 = z.2) ↔
      ∃ S : Finset (Fin n), S.sum w ≤ k ∧
        ((Finset.univ : Finset (Fin m)).filter (fun j => ∃ M ∈ E j, Disjoint M S)).card < 2^b := by
  let _ : ∀ P : Prop, Decidable P := Classical.propDecidable
  intro n m d w E hd
  have hdec : ∀ (P : Prop) (d1 d2 : Decidable P), @decide P d1 = @decide P d2 :=
    fun _ _ _ => congrArg (@decide _) (Subsingleton.elim _ _)
  have hraw : ∀ (x : (a : Fin n) → Fin (d * w a) → Bool) (level : ℕ),
      (List.ofFn (fun a : Fin n => List.ofFn (x a))).flatten ++
        List.ofFn (fun g : Fin (2 * m) => @decide (g.val < level) (Classical.propDecidable _)) ++
        [false, true] =
      rawVec n m d w x level := by
    intro x level
    dsimp only [rawVec, bankBlock, width]
    congr 2
    apply congrArg List.ofFn
    funext g
    exact hdec _ _ _
  have hrows :
      ((Finset.univ : Finset (Fin m)).image
          (fun j => ((List.ofFn (fun a : Fin n => List.ofFn (fun _ : Fin (d * w a) => false))).flatten ++
            List.ofFn (fun g : Fin (2 * m) => @decide (g.val < 2 * j.val + 1) (Classical.propDecidable _)) ++
            [false, true], false)) ∪
        Finset.univ.biUnion (fun j => (E j).biUnion (fun M =>
          Finset.univ.image (fun f : (a : {a : Fin n // a ∈ M}) → Fin (d * w a.val) =>
            ((List.ofFn (fun a : Fin n => List.ofFn (fun k : Fin (d * w a) =>
              if h : a ∈ M then @decide (f ⟨a, h⟩ = k) (Classical.propDecidable _) else false))).flatten ++
              List.ofFn (fun g : Fin (2 * m) => @decide (g.val < 2 * j.val) (Classical.propDecidable _)) ++
              [false, true], true))))) =
      rowsSet n m d w E := by
    ext z
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and,
      rowsSet, zerosSet, posRows, copiesSet, copyVec]
    constructor
    · rintro (⟨j, rfl⟩ | ⟨j, M, hME, f, rfl⟩)
      · left; exact ⟨j, by rw [hraw]; rfl⟩
      · right
        refine ⟨j, M, hME, f, ?_⟩
        rw [hraw]
        congr 2
        funext a k
        by_cases ha : a ∈ M
        · simp only [dite_eq_left ha]; exact hdec _ _ _
        · simp [ha]
    · rintro (⟨j, rfl⟩ | ⟨j, M, hME, f, rfl⟩)
      · left; exact ⟨j, by rw [hraw]; rfl⟩
      · right
        refine ⟨j, M, hME, f, ?_⟩
        rw [hraw]
        congr 2
        funext a k
        by_cases ha : a ∈ M
        · simp only [dite_eq_left ha]; exact hdec _ _ _
        · simp [ha]
  have hmissed : ∀ S : Finset (Fin n),
      (Finset.univ : Finset (Fin m)).filter (fun j => ∃ M ∈ E j, Disjoint M S) =
      missedSet n m E S := by
    intro S
    ext j
    simp [missedSet]
  dsimp only
  rw [hrows]
  have hmain := solve n m d w E hd
  refine ⟨hmain.1, fun b k => ?_⟩
  simp_rw [hmissed]
  exact hmain.2 b k
