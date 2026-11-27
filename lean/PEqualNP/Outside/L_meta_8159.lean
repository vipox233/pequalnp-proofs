import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

namespace PEqualNP.Outside.L_meta_8159

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

lemma run_nil (x : List Bool) : run [] x = x := rfl

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (step x g) := rfl

lemma run_append (l1 l2 : List Gate) (x : List Bool) :
    run (l1 ++ l2) x = run l2 (run l1 x) := by
  simp [run, List.foldl_append]

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih, step_length]; simp; omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp only [step]
  exact List.getD_append _ _ _ _ hi

lemma step_getD_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [step]
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma run_getD (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => rw [run_cons, ih _ (by rw [step_length]; omega), step_getD _ _ _ hi]

lemma run_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run (gs.take j) x).getD i false) := by
  have hsplit : run gs x = run (gs.drop (j + 1)) (step (run (gs.take j) x) gs[j]) := by
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj]
    rw [run_append, run_cons]
  have hl : (run (gs.take j) x).length = x.length + j := by
    rw [run_length, List.length_take]; omega
  rw [hsplit, run_getD _ _ _ (by rw [step_length]; omega), ← hl, step_getD_last]

lemma run_prefix_getD (gs : List Gate) (x : List Bool) (j i : ℕ) (hj : j ≤ gs.length)
    (hi : i < x.length + j) :
    (run (gs.take j) x).getD i false = (run gs x).getD i false := by
  conv_rhs => rw [← List.take_append_drop j gs, run_append]
  exact (run_getD _ _ _ (by rw [run_length, List.length_take]; omega)).symm

lemma gate_val (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length)
    (hr : ∀ i ∈ gs[j].inputs, i < x.length + j) :
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run gs x).getD i false) := by
  rw [run_gate gs x j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact run_prefix_getD gs x j i hj.le (hr i hi)

lemma gateAt_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  unfold gateAt
  exact List.getD_eq_getElem _ _ hj

lemma gateAt_out (C : Circuit) (j : ℕ) (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  unfold gateAt
  exact List.getD_eq_default _ _ hj

lemma cval_gate (n : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) (hRB : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) :
    (run C.gates x).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (run C.gates x).getD i false) := by
  rw [gateAt_eq C j hj]
  have := gate_val C.gates x j hj (by
    intro i hi
    have := hRB j hj i (by rw [gateAt_eq C j hj]; exact hi)
    omega)
  rw [hx] at this
  exact this

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩


lemma gv (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    gateVal n C j x =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires (List.ofFn x)).getD i false) :=
  cval_gate n C (List.ofFn x) (by simp) hRB j hj

lemma wires_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  have h := run_getD C.gates (List.ofFn x) i (by simp; exact hi)
  show (run C.gates (List.ofFn x)).getD i false = _
  rw [h]
  simp [List.getD_eq_getElem?_getD, hi]

lemma or_true (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (x : Fin n → Bool) (w : ℕ) (hw : w ∈ (gateAt C k).inputs)
    (hv : (C.wires (List.ofFn x)).getD w false = true) : gateVal n C k x = true := by
  rw [gv n C hRB k hk x, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
  exact ⟨w, hw, hv⟩

lemma inCone_trans (n : ℕ) (C : Circuit) (m k : ℕ) (hmk : InCone n C m k) :
    ∀ g, InCone n C k g → InCone n C m g := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
    intro h
    obtain ⟨hg, k2, hk2, hin, hor⟩ := (inCone_iff n C k g).mp h
    rcases hor with e | hc
    · subst e
      exact (inCone_iff n C m g).mpr ⟨hg, k, hk2, hin, Or.inr hmk⟩
    · exact (inCone_iff n C m g).mpr ⟨hg, k2, hk2, hin, Or.inr (ih k2 hk2 hc)⟩

lemma op_cases (C : Circuit) (hA : AndOrOnly C) (k : ℕ) (hk : k < C.gates.length) :
    (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  apply hA
  rw [gateAt_eq C k hk]
  exact List.getElem_mem hk

open PEqualNP.ReadTwo

def IsAndWire (n : ℕ) (C : Circuit) (a : ℕ) : Prop :=
  ∃ i < C.size, a = n+i ∧ (gateAt C i).op = GateOp.and

def AncestorWire (n : ℕ) (C : Circuit) (a w : ℕ) : Prop :=
  a < n ∨ ∃ i < C.size, a = n+i ∧ (gateAt C i).op = GateOp.and ∧
    (w = n+i ∨ ∃ j, w = n+j ∧ InCone n C i j)

lemma frontier {n : ℕ} {C : Circuit} (hao : IsAO2 n C) (w : ℕ) (hw : w < n+C.size) :
    ∃ S : Finset ℕ, (∀ a ∈ S, AncestorWire n C a w) ∧
      ∀ x : Fin n → Bool, wval C x w = true ↔ ∃ a ∈ S, wval C x a = true := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases base : w < n
    · exact ⟨{w}, by intro a ha; rw [Finset.mem_singleton.mp ha]; exact Or.inl base, by simp⟩
    obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n, by omega⟩
    have hj : j < C.gates.length := by change n+j < n+C.gates.length at hw; omega
    rcases op_cases C hao.1 j hj with isAnd | isOr
    · refine ⟨{n+j}, ?_, by simp⟩
      intro a ha
      obtain rfl := Finset.mem_singleton.mp ha
      exact Or.inr ⟨j,hj,rfl,isAnd,Or.inl rfl⟩
    let inp := (gateAt C j).inputs.toFinset
    have smaller (b) (hb : b ∈ inp) : b < n+j :=
      hao.2.1 j hj b (List.mem_toFinset.mp hb)
    have sub (b) (hb : b ∈ inp) := ih b (smaller b hb) (by have := smaller b hb; omega)
    let ss (b : ℕ) : Finset ℕ := if h : b ∈ inp then (sub b h).choose else ∅
    have hs (b) (hb : b ∈ inp) :
        (∀ a ∈ ss b, AncestorWire n C a b) ∧
        ∀ x : Fin n → Bool, wval C x b = true ↔ ∃ a ∈ ss b, wval C x a = true := by
      simpa [ss,hb] using (sub b hb).choose_spec
    refine ⟨inp.biUnion ss, ?_, ?_⟩
    · intro a ha
      obtain ⟨b,hb,hab⟩ := Finset.mem_biUnion.mp ha
      rcases (hs b hb).1 a hab with raw | ⟨i,hi,ha,hop,rfl | ⟨k,rfl,hik⟩⟩
      · exact Or.inl raw
      · exact Or.inr ⟨i,hi,ha,hop,Or.inr ⟨j,rfl,(inCone_iff n C i j).2
          ⟨hj,i,by have := smaller _ hb; omega,List.mem_toFinset.mp hb,Or.inl rfl⟩⟩⟩
      · exact Or.inr ⟨i,hi,ha,hop,Or.inr ⟨j,rfl,(inCone_iff n C i j).2
          ⟨hj,k,by have := smaller _ hb; omega,List.mem_toFinset.mp hb,Or.inr hik⟩⟩⟩
    · intro x
      change gateVal n C j x = true ↔ _
      rw [gv n C hao.2.1 j hj x, isOr]
      simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq,
        Finset.mem_biUnion]
      constructor
      · rintro ⟨b,hb,v⟩
        have hbi : b ∈ inp := List.mem_toFinset.mpr hb
        obtain ⟨a,ha,hv⟩ := ((hs b hbi).2 x).mp v
        exact ⟨a,⟨b,hbi,ha⟩,hv⟩
      · rintro ⟨a,⟨b,hb,ha⟩,hv⟩
        exact ⟨b,List.mem_toFinset.mp hb,((hs b hb).2 x).mpr ⟨a,ha,hv⟩⟩

lemma operandFrontier {n : ℕ} {C : Circuit} (hao : IsAO2 n C)
    {j w : ℕ} (hj : j < C.size) (hw : w ∈ (gateAt C j).inputs) :
    ∃ S : Finset ℕ, (∀ a ∈ S, a < n ∨ ∃ k < C.size,
      a = n+k ∧ (gateAt C k).op = GateOp.and ∧ InCone n C k j) ∧
      ∀ x : Fin n → Bool, wval C x w = true ↔ ∃ a ∈ S, wval C x a = true := by
  have lt := hao.2.1 j hj w hw
  obtain ⟨S,valid,spec⟩ := frontier hao w (by omega)
  refine ⟨S,?_,spec⟩
  intro a ha
  rcases valid a ha with raw | ⟨k,hk,eq,op,rfl | ⟨i,rfl,hki⟩⟩
  · exact Or.inl raw
  · exact Or.inr ⟨k,hk,eq,op,(inCone_iff n C k j).2 ⟨hj,k,by omega,hw,Or.inl rfl⟩⟩
  · exact Or.inr ⟨k,hk,eq,op,(inCone_iff n C k j).2 ⟨hj,i,by omega,hw,Or.inr hki⟩⟩

open PEqualNP.MetaComplexity

def negRows : List ℕ := [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]
def posRows : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768]
def row (r : ℕ) : Fin 11 → Bool := fun i => r.testBit i.val
def Clean (C : Circuit) (j : ℕ) := ∀ r ∈ negRows, gateVal 11 C j (row r) = false

lemma hitRaw : ∀ v : Fin 11, ∃ r ∈ negRows, row r v = true := by decide +kernel

lemma outputCover {C : Circuit} (hao : IsAO2 11 C)
    (hp : ∀ r ∈ posRows, circuitFun 11 C (row r) = true)
    (hn : ∀ r ∈ negRows, circuitFun 11 C (row r) = false) :
    ∀ r ∈ posRows, ∃ j < C.size, (gateAt C j).op = GateOp.and ∧ Clean C j ∧
      gateVal 11 C j (row r) = true := by
  have hout : C.output < 11+C.size := by
    by_contra! h
    have hbad := hp 513 (by decide)
    change (run C.gates (List.ofFn (row 513))).getD C.output false = true at hbad
    rw [List.getD_eq_default _ _ (by rw [run_length]; simpa [Circuit.size] using h)] at hbad
    contradiction
  obtain ⟨S,valid,spec⟩ := frontier hao C.output hout
  have inactive (a) (ha : a ∈ S) (r) (hr : r ∈ negRows) : wval C (row r) a = false := by
    cases h : wval C (row r) a with
    | false => rfl
    | true =>
      have yes := (spec (row r)).2 ⟨a,ha,h⟩
      change circuitFun 11 C (row r) = true at yes
      rw [hn r hr] at yes
      contradiction
  intro r hr
  obtain ⟨a,ha,on⟩ := (spec (row r)).1 (hp r hr)
  rcases valid a ha with raw | ⟨j,hj,rfl,hand,_⟩
  · obtain ⟨q,hq,hv⟩ := hitRaw ⟨a,raw⟩
    have off := inactive a ha q hq
    change (C.wires (List.ofFn (row q))).getD a false = false at off
    rw [wires_input 11 C _ a raw, hv] at off
    contradiction
  · exact ⟨j,hj,hand,fun q hq => inactive _ ha q hq,on⟩

lemma binaryInputs {C : Circuit} {n j : ℕ} (hao : IsAO2 n C) (hj : j < C.size) :
    ∃ u v, (gateAt C j).inputs = [u,v] := by
  have len := hao.2.2 (gateAt C j) (by rw [gateAt_eq C j hj]; exact List.getElem_mem hj)
  cases h : (gateAt C j).inputs with
  | nil => simp [h] at len
  | cons u l =>
    cases l with
    | nil => simp [h] at len
    | cons v t =>
      have ht : t = [] := by simpa [h] using len
      exact ⟨u,v,by rw [ht]⟩

lemma factored {C : Circuit} {j : ℕ} (hao : IsAO2 11 C) (hj : j < C.size)
    (op : (gateAt C j).op = GateOp.and) :
    ∃ S T : Finset ℕ,
      (∀ a ∈ S ∪ T, a < 11 ∨ ∃ k < C.size, a = 11+k ∧
        (gateAt C k).op = GateOp.and ∧ InCone 11 C k j) ∧
      ∀ x : Fin 11 → Bool, gateVal 11 C j x = true ↔
        (∃ a ∈ S, wval C x a = true) ∧ (∃ a ∈ T, wval C x a = true) := by
  obtain ⟨u,v,eq⟩ := binaryInputs hao hj
  obtain ⟨S,hS,vS⟩ := operandFrontier hao hj (show u ∈ _ by rw [eq]; simp)
  obtain ⟨T,hT,vT⟩ := operandFrontier hao hj (show v ∈ _ by rw [eq]; simp)
  refine ⟨S,T,fun a ha => (Finset.mem_union.mp ha).elim (hS a) (hT a),?_⟩
  intro x
  rw [← vS, ← vT, gv 11 C hao.2.1 j hj x, op, eq]
  simp [GateOp.eval,wval]

lemma dirtyFactors {C : Circuit} {p q j : ℕ} (hao : IsAO2 11 C) (hj : j < C.size)
    (op : (gateAt C j).op = GateOp.and)
    (hjunk : ∀ k < C.size, (gateAt C k).op = GateOp.and →
      (Clean C k ↔ k ≠ p ∧ k ≠ q))
    (htop : ∀ k < C.size, (gateAt C k).op = GateOp.and → Clean C k →
      ∀ i < C.size, (gateAt C i).op = GateOp.and → ¬InCone 11 C k i) :
    ∃ S T : Finset ℕ,
      (∀ a ∈ S ∪ T, a < 11 ∨ (a = 11+p ∧ InCone 11 C p j) ∨
        (a = 11+q ∧ InCone 11 C q j)) ∧
      ∀ x : Fin 11 → Bool, gateVal 11 C j x = true ↔
        (∃ a ∈ S, wval C x a = true) ∧ (∃ a ∈ T, wval C x a = true) := by
  obtain ⟨S,T,valid,spec⟩ := factored hao hj op
  refine ⟨S,T,?_,spec⟩
  intro a ha
  rcases valid a ha with raw | ⟨k,hk,rfl,hand,path⟩
  · exact Or.inl raw
  by_cases h : k = p
  · exact Or.inr (Or.inl (h ▸ ⟨rfl,path⟩))
  by_cases h' : k = q
  · exact Or.inr (Or.inr (h' ▸ ⟨rfl,path⟩))
  exact (htop k hk hand ((hjunk k hk hand).2 ⟨h,h'⟩) j hj op path).elim

def hit {k : ℕ} (S : Finset (Fin k)) (v : Fin k → Prop) : Prop := ∃ i ∈ S, v i
abbrev Arms (k : ℕ) := Finset (Fin k) × Finset (Fin k)
def fires {k : ℕ} (s : Arms k) (v : Fin k → Prop) : Prop := hit s.1 v ∧ hit s.2 v
def pull {k : ℕ} (src : Fin k → ℕ) (S : Finset ℕ) : Finset (Fin k) :=
  Finset.univ.filter fun i => src i ∈ S

lemma pullHit {k : ℕ} (src : Fin k → ℕ) (S : Finset ℕ) (x : Fin 11 → Bool) (C : Circuit)
    (onto : ∀ a ∈ S, ∃ i, src i = a) :
    hit (pull src S) (fun i => wval C x (src i) = true) ↔ ∃ a ∈ S, wval C x a = true := by
  simp only [hit,pull,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi,hv⟩
    exact ⟨src i,hi,hv⟩
  · rintro ⟨a,ha,hv⟩
    obtain ⟨i,rfl⟩ := onto a ha
    exact ⟨i,ha,hv⟩

def source (p q : ℕ) (i : Fin 13) : ℕ :=
  if i.val < 11 then i.val else if i.val = 11 then 11+p else 11+q

def feature (d0 d1 : Arms 11) (x : Fin 11 → Bool) (i : Fin 13) : Prop :=
  if h : i.val < 11 then x ⟨i.val,h⟩ = true
  else if i.val = 11 then fires d0 (fun v => x v = true) else fires d1 (fun v => x v = true)

def TablesImpossible : Prop :=
  ∀ d0 d1 : Arms 11, ∀ tops : Finset (Arms 13), tops.card ≤ 4 →
    (∃ r ∈ negRows, fires d0 (fun i => row r i = true)) →
    (∃ r ∈ negRows, fires d1 (fun i => row r i = true)) →
    (∀ s ∈ tops, ∀ r ∈ negRows, ¬ fires s (feature d0 d1 (row r))) →
    (∀ r ∈ posRows, ∃ s ∈ tops, fires s (feature d0 d1 (row r))) → False

lemma rawPair {C : Circuit} {p q j : ℕ} (hao : IsAO2 11 C)
    (hj : j < C.size) (hand : (gateAt C j).op = GateOp.and)
    (hjunk : ∀ k < C.size, (gateAt C k).op = GateOp.and → (Clean C k ↔ k ≠ p ∧ k ≠ q))
    (htop : ∀ k < C.size, (gateAt C k).op = GateOp.and → Clean C k →
      ∀ i < C.size, (gateAt C i).op = GateOp.and → ¬InCone 11 C k i)
    (hnp : ¬InCone 11 C p j) (hnq : ¬InCone 11 C q j) :
    ∃ d : Arms 11, ∀ x : Fin 11 → Bool, gateVal 11 C j x = true ↔ fires d (fun i => x i = true) := by
  obtain ⟨S,T,valid,spec⟩ := dirtyFactors hao hj hand hjunk htop
  have allRaw (a) (ha : a ∈ S ∪ T) : ∃ i : Fin 11, i.val = a := by
    rcases valid a ha with h | ⟨_,h⟩ | ⟨_,h⟩
    · exact ⟨⟨a,h⟩,rfl⟩
    · exact (hnp h).elim
    · exact (hnq h).elim
  refine ⟨(pull Fin.val S,pull Fin.val T),?_⟩
  intro x
  have hraw (i : Fin 11) : wval C x i.val = x i := wires_input 11 C x i.val i.isLt
  simp only [fires]
  rw [spec]
  simpa only [hraw] using (and_congr
    (pullHit Fin.val S x C (fun a ha => allRaw a (Finset.mem_union_left _ ha)))
    (pullHit Fin.val T x C (fun a ha => allRaw a (Finset.mem_union_right _ ha)))).symm

lemma normalizedFactors {C : Circuit} {p q : ℕ} (hao : IsAO2 11 C)
    (hp : p < C.size) (hq : q < C.size)
    (op : (gateAt C p).op = GateOp.and) (oq : (gateAt C q).op = GateOp.and)
    (hqp : ¬InCone 11 C q p) (hpq : ¬InCone 11 C p q)
    (hjunk : ∀ k < C.size, (gateAt C k).op = GateOp.and → (Clean C k ↔ k ≠ p ∧ k ≠ q))
    (htop : ∀ k < C.size, (gateAt C k).op = GateOp.and → Clean C k →
      ∀ i < C.size, (gateAt C i).op = GateOp.and → ¬InCone 11 C k i) :
    ∃ d0 d1 : Arms 11, (∃ r ∈ negRows, fires d0 (fun i => row r i = true)) ∧
      (∃ r ∈ negRows, fires d1 (fun i => row r i = true)) ∧
      ∀ j < C.size, (gateAt C j).op = GateOp.and →
      ∃ s : Arms 13, ∀ x : Fin 11 → Bool, gateVal 11 C j x = true ↔ fires s (feature d0 d1 x) := by
  obtain ⟨d0,hd0⟩ := rawPair hao hp op hjunk htop (fun h => Nat.lt_irrefl _ (inCone_lt 11 C p p h).1) hqp
  obtain ⟨d1,hd1⟩ := rawPair hao hq oq hjunk htop hpq (fun h => Nat.lt_irrefl _ (inCone_lt 11 C q q h).1)
  have witness (j : ℕ) (h : ¬Clean C j) : ∃ r ∈ negRows, gateVal 11 C j (row r) = true := by
    unfold Clean at h
    push Not at h
    simpa using h
  obtain ⟨r,hr,vr⟩ := witness p (fun h => ((hjunk p hp op).1 h).1 rfl)
  obtain ⟨t,ht,vt⟩ := witness q (fun h => ((hjunk q hq oq).1 h).2 rfl)
  refine ⟨d0,d1,⟨r,hr,(hd0 _).1 vr⟩,⟨t,ht,(hd1 _).1 vt⟩,?_⟩
  intro j hj hand
  obtain ⟨S,T,valid,spec⟩ := dirtyFactors hao hj hand hjunk htop
  have allSrc (a) (ha : a ∈ S ∪ T) : ∃ i : Fin 13, source p q i = a := by
    rcases valid a ha with h | ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact ⟨⟨a,by omega⟩,by simp [source,h]⟩
    · exact ⟨11,rfl⟩
    · exact ⟨12,rfl⟩
  refine ⟨(pull (source p q) S,pull (source p q) T),?_⟩
  intro x
  have equiv (i : Fin 13) : (wval C x (source p q i) = true) = feature d0 d1 x i := by
    by_cases h : i.val < 11
    · simp only [source,feature,ite_eq_left h,dite_eq_left h,wval,wires_input 11 C x i.val h]
    · by_cases h' : i.val = 11
      · simp only [source,feature,ite_eq_right h,dite_eq_right h,ite_eq_left h']; exact propext (hd0 x)
      · simp only [source,feature,ite_eq_right h,dite_eq_right h,ite_eq_right h']; exact propext (hd1 x)
  simp only [fires]
  rw [spec]
  simpa only [equiv] using (and_congr
    (pullHit (source p q) S x C (fun a ha => allSrc a (Finset.mem_union_left _ ha)))
    (pullHit (source p q) T x C (fun a ha => allSrc a (Finset.mem_union_right _ ha)))).symm

lemma list_filter_length_eq_card_range (l : List Gate) (p : Gate → Bool) (d : Gate) :
    (l.filter p).length = ((Finset.range l.length).filter (fun j => p (l.getD j d) = true)).card := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l g ih =>
    rw [List.filter_append, List.length_append, List.length_append, List.length_singleton,
      Finset.range_add_one, Finset.filter_insert]
    have hlast : (l ++ [g]).getD l.length d = g := by
      have hlt : l.length < (l ++ [g]).length := by simp
      rw [List.getD_eq_getElem _ _ hlt, List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_cons_zero]
    have hfilt_eq : (Finset.range l.length).filter (fun j => p ((l ++ [g]).getD j d) = true) =
        (Finset.range l.length).filter (fun j => p (l.getD j d) = true) := by
      apply Finset.filter_congr
      intro j hj
      have hjlt : j < l.length := Finset.mem_range.mp hj
      have hjlt2 : j < (l ++ [g]).length := by simp; omega
      rw [List.getD_eq_getElem _ _ hjlt2, List.getD_eq_getElem _ _ hjlt, List.getElem_append_left hjlt]
    rw [hlast, hfilt_eq]
    cases hpg : p g with
    | false =>
      simp [List.filter, hpg, ih]
    | true =>
      simp [List.filter, hpg, ih]

lemma nAnd_eq_card (C : Circuit) [DecidablePred (fun j => (gateAt C j).op = GateOp.and)] :
    nAnd C = ((Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.and)).card := by
  unfold nAnd
  rw [list_filter_length_eq_card_range C.gates _ ⟨GateOp.or, []⟩]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_iff]
  rfl

lemma reduction (noModel : ∀ d0 d1 : Arms 11, ∀ tops : Finset (Arms 13), tops.card ≤ 4 →
      (∃ r ∈ negRows, fires d0 (fun i => row r i = true)) →
      (∃ r ∈ negRows, fires d1 (fun i => row r i = true)) →
      (∀ s ∈ tops, ∀ r ∈ negRows, ¬fires s (feature d0 d1 (row r))) →
      (∀ r ∈ posRows, ∃ s ∈ tops, fires s (feature d0 d1 (row r))) → False)
    {C : Circuit} {p q : ℕ} (hao : IsAO2 11 C) (count : nAnd C ≤ 6)
    (horder : p < q) (hq : q < C.size)
    (op : (gateAt C p).op = GateOp.and) (oq : (gateAt C q).op = GateOp.and)
    (hjunk : ∀ k < C.size, (gateAt C k).op = GateOp.and → (Clean C k ↔ k ≠ p ∧ k ≠ q))
    (htop : ∀ k < C.size, (gateAt C k).op = GateOp.and → Clean C k →
      ∀ i < C.size, (gateAt C i).op = GateOp.and → ¬InCone 11 C k i)
    (hpq : ¬InCone 11 C p q) (hqp : ¬InCone 11 C q p)
    (hpos : ∀ r ∈ posRows, circuitFun 11 C (row r) = true)
    (hneg : ∀ r ∈ negRows, circuitFun 11 C (row r) = false) : False := by
  classical
  obtain ⟨d0,d1,bad0,bad1,fac⟩ := normalizedFactors hao (by omega) hq op oq hqp hpq hjunk htop
  let A := (Finset.range C.size).filter fun j => (gateAt C j).op = GateOp.and
  let J := A \ {p,q}
  have hA : A.card = nAnd C := (nAnd_eq_card C).symm
  have sub : {p,q} ⊆ A := by
    intro j h
    rcases Finset.mem_insert.mp h with rfl | h
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),op⟩
    · obtain rfl := Finset.mem_singleton.mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hq,oq⟩
  have cap : J.card ≤ 4 := by
    have h := Finset.card_sdiff_of_subset sub
    rw [Finset.card_pair horder.ne,hA] at h
    change (A \ {p,q}).card ≤ 4
    omega
  have desc (j) (hj : j ∈ J) : j < C.size ∧ (gateAt C j).op = GateOp.and ∧ Clean C j := by
    obtain ⟨ha,notPair⟩ := Finset.mem_sdiff.mp hj
    obtain ⟨hr,hand⟩ := Finset.mem_filter.mp ha
    have lt := Finset.mem_range.mp hr
    exact ⟨lt,hand,(hjunk j lt hand).2 (by simpa using notPair)⟩
  let s (j : ℕ) : Arms 13 := if h : j ∈ J then (fac j (desc j h).1 (desc j h).2.1).choose else (∅,∅)
  have hs (j) (hj : j ∈ J) (x) : gateVal 11 C j x = true ↔ fires (s j) (feature d0 d1 x) := by
    simpa only [s,dite_eq_left hj] using (fac j (desc j hj).1 (desc j hj).2.1).choose_spec x
  apply noModel d0 d1 (J.image s) ((Finset.card_image_le).trans cap) bad0 bad1
  · intro k hk r hr on
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    have yes := (hs j hj _).2 on
    exact Bool.false_ne_true (((desc j hj).2.2 r hr).symm.trans yes)
  · intro r hr
    obtain ⟨j,lt,hand,clean,on⟩ := outputCover hao hpos hneg r hr
    have hj : j ∈ J := Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr lt,hand⟩,
      by simpa using (hjunk j lt hand).1 clean⟩
    exact ⟨s j,Finset.mem_image.mpr ⟨j,hj,rfl⟩,(hs j hj _).1 on⟩

theorem fromTables (noModel : TablesImpossible) : (have x1 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)]; have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)]; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) => ∀ x6 ∈ x1, (PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x4 x5 fun (x8 : Fin (11 : ℕ)) => x6.testBit ↑x8) = Bool.false; have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ); ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 : ℕ), PEqualNP.TopForm.IsAO2 (11 : ℕ) x6 → (5 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x6 → PEqualNP.ReadTwo.nAnd x6 ≤ (6 : ℕ) → x7 < x8 → x8 < x6.size → x3 x6 x7 → x3 x6 x8 → (∀ x16 < x6.size, x3 x6 x16 → (x4 x6 x16 ↔ x16 ≠ x7 ∧ x16 ≠ x8)) → (∀ x17 < x6.size, x3 x6 x17 → x4 x6 x17 → ∀ x21 < x6.size, x3 x6 x21 → ¬x5 x6 x17 x21) → ¬x5 x6 x7 x8 → ¬x5 x6 x8 x7 → (∃ x20 < x6.size, x3 x6 x20 ∧ x4 x6 x20 ∧ x5 x6 x7 x20 ∧ x5 x6 x8 x20) → (∀ x21 ∈ x2, (PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x6 fun (x23 : Fin (11 : ℕ)) => x21.testBit ↑x23) = Bool.true) → (∀ x22 ∈ x1, (PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x6 fun (x24 : Fin (11 : ℕ)) => x22.testBit ↑x24) = Bool.false) → False) := by
  intro neg pos isAnd clean cone C p q hao _lo hi hpq hq op oq hj ht path rev _common positives negatives
  exact reduction noModel hao hi hpq hq op oq hj ht path rev positives negatives

def overlap (d : Arms 11) := d.1 ∩ d.2
def separate (d : Arms 11) : Arms 11 := (d.1 \ d.2,d.2 \ d.1)
def emb (i : Fin 11) : Fin 13 := ⟨i.val,by omega⟩

lemma splitFires (d : Arms 11) (x : Fin 11 → Prop) :
    fires d x ↔ hit (overlap d) x ∨ fires (separate d) x := by
  classical
  constructor
  · rintro ⟨⟨u,hu,v⟩,⟨w,hw,t⟩⟩
    by_cases h : hit (overlap d) x
    · exact Or.inl h
    · refine Or.inr ⟨⟨u,Finset.mem_sdiff.mpr ⟨hu,?_⟩,v⟩,⟨w,Finset.mem_sdiff.mpr ⟨hw,?_⟩,t⟩⟩
      · exact fun hz => h ⟨u,Finset.mem_inter.mpr ⟨hu,hz⟩,v⟩
      · exact fun hz => h ⟨w,Finset.mem_inter.mpr ⟨hz,hw⟩,t⟩
  · rintro (⟨u,hu,v⟩ | ⟨⟨u,hu,v⟩,⟨w,hw,t⟩⟩)
    · exact ⟨⟨u,(Finset.mem_inter.mp hu).1,v⟩,⟨u,(Finset.mem_inter.mp hu).2,v⟩⟩
    · exact ⟨⟨u,(Finset.mem_sdiff.mp hu).1,v⟩,⟨w,(Finset.mem_sdiff.mp hw).1,t⟩⟩

def atoms (p q : Arms 11) (i : Fin 13) : Finset (Fin 13) :=
  if i = 11 then insert 11 ((overlap p).image emb)
  else if i = 12 then insert 12 ((overlap q).image emb) else {i}

lemma rawFeature (p q : Arms 11) (x : Fin 11 → Bool) (i : Fin 11) :
    feature p q x (emb i) ↔ x i = true := by simp [feature,emb,i.isLt]
lemma firstFeature (p q : Arms 11) (x : Fin 11 → Bool) :
    feature p q x 11 ↔ fires p (fun i => x i = true) := by rfl
lemma lastFeature (p q : Arms 11) (x : Fin 11 → Bool) :
    feature p q x 12 ↔ fires q (fun i => x i = true) := by rfl

lemma expandAtom (p q : Arms 11) (x : Fin 11 → Bool) (i : Fin 13) :
    feature p q x i ↔ hit (atoms p q i) (feature (separate p) (separate q) x) := by
  by_cases h : i = 11
  · subst i
    rw [firstFeature,splitFires]
    simp [atoms,hit,firstFeature,rawFeature,or_comm]
  by_cases k : i = 12
  · subst i
    rw [lastFeature,splitFires]
    simp [atoms,hit,lastFeature,rawFeature,or_comm]
  have small : i.val < 11 := by
    have n : i.val ≠ 11 := fun e => h (Fin.ext e)
    have m : i.val ≠ 12 := fun e => k (Fin.ext e)
    omega
  simp [atoms,h,k,hit,feature,small]

def expand (p q : Arms 11) (s : Arms 13) : Arms 13 :=
  (s.1.biUnion (atoms p q), s.2.biUnion (atoms p q))

lemma expandHit (p q : Arms 11) (x : Fin 11 → Bool) (s : Finset (Fin 13)) :
    hit s (feature p q x) ↔ hit (s.biUnion (atoms p q)) (feature (separate p) (separate q) x) := by
  constructor
  · rintro ⟨a,ha,h⟩
    obtain ⟨i,hi,v⟩ := (expandAtom p q x a).1 h
    exact ⟨i,Finset.mem_biUnion.mpr ⟨a,ha,hi⟩,v⟩
  · rintro ⟨i,hi,v⟩
    obtain ⟨a,ha,hai⟩ := Finset.mem_biUnion.mp hi
    exact ⟨a,ha,(expandAtom p q x a).2 ⟨i,hai,v⟩⟩

lemma expandFires (p q : Arms 11) (x : Fin 11 → Bool) (s : Arms 13) :
    fires s (feature p q x) ↔ fires (expand p q s) (feature (separate p) (separate q) x) :=
  and_congr (expandHit p q x s.1) (expandHit p q x s.2)

def productive (d : Arms 11) : Finset (Fin 11) :=
  Finset.univ.filter fun v => ∃ r ∈ posRows, row r v = true ∧
    (∃ a ∈ d.1, row r a = true) ∧ ∃ b ∈ d.2, row r b = true

def trim (d : Arms 11) : Arms 11 := (d.1 ∩ productive d,d.2 ∩ productive d)

lemma trimLe (d : Arms 11) (v : Fin 11 → Prop) : fires (trim d) v → fires d v := by
  rintro ⟨⟨a,ha,va⟩,⟨b,hb,vb⟩⟩
  exact ⟨⟨a,(Finset.mem_inter.mp ha).1,va⟩,⟨b,(Finset.mem_inter.mp hb).1,vb⟩⟩

lemma trimPos {d : Arms 11} {r : ℕ} (hr : r ∈ posRows) :
    fires d (fun i => row r i = true) ↔ fires (trim d) (fun i => row r i = true) := by
  refine ⟨?_,trimLe _ _⟩
  intro hd
  have active (i) (hi : row r i = true) : i ∈ productive d :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,r,hr,hi,hd⟩
  obtain ⟨⟨a,ha,va⟩,⟨b,hb,vb⟩⟩ := hd
  exact ⟨⟨a,Finset.mem_inter.mpr ⟨ha,active a va⟩,va⟩,⟨b,Finset.mem_inter.mpr ⟨hb,active b vb⟩,vb⟩⟩

lemma featureMono {x : Fin 11 → Bool} {a b c d : Arms 11}
    (h : fires a (fun i => x i = true) → fires c (fun i => x i = true))
    (k : fires b (fun i => x i = true) → fires d (fun i => x i = true)) (i : Fin 13) :
    feature a b x i → feature c d x i := by
  unfold feature
  split <;> first | exact id | split <;> assumption

lemma firesMono {k : ℕ} {f g : Fin k → Prop} (s : Arms k) (h : ∀ i, f i → g i) :
    fires s f → fires s g := by
  rintro ⟨⟨u,hu,vu⟩,⟨v,hv,vv⟩⟩
  exact ⟨⟨u,hu,h _ vu⟩,⟨v,hv,h _ vv⟩⟩

def Canonical (s : Arms 11) := Disjoint s.1 s.2 ∧
  ∀ i ∈ s.1 ∪ s.2, ∃ r ∈ posRows, row r i = true ∧ fires s (fun v => row r v = true)

lemma canonical (s : Arms 11) : Canonical (trim (separate s)) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hi).1).2 (Finset.mem_sdiff.mp (Finset.mem_inter.mp hj).1).1
  · intro i hi
    have h : i ∈ productive (separate s) := (Finset.mem_union.mp hi).elim
      (fun h => (Finset.mem_inter.mp h).2) (fun h => (Finset.mem_inter.mp h).2)
    obtain ⟨_,r,hr,vi,ev⟩ := Finset.mem_filter.mp h
    exact ⟨r,hr,vi,(trimPos hr).1 ev⟩

def splitTags (s : Arms 13) := ∀ i : Fin 13, 11 ≤ i.val → i ∈ s.1 → i ∉ s.2

lemma highAtoms (p q : Arms 11) {i j : Fin 13} (h : 11 ≤ i.val) : i ∈ atoms p q j ↔ i = j := by
  have no (d : Arms 11) : i ∉ (overlap d).image emb := by
    rintro hi
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hi
    change 11 ≤ t.val at h
    omega
  by_cases a : j = 11
  · subst j; simp [atoms,no]
  by_cases b : j = 12
  · subst j; simp [atoms,no]
  simp [atoms,a,b]

lemma highExpanded (p q : Arms 11) {i : Fin 13} (h : 11 ≤ i.val) (s : Finset (Fin 13)) :
    i ∈ s.biUnion (atoms p q) ↔ i ∈ s := by simp [highAtoms p q h]

lemma coreReduction
    (hard : ∀ p q : Arms 11, Canonical p → Canonical q → ∀ tops : Finset (Arms 13), tops.card ≤ 4 →
      (∀ s ∈ tops, splitTags s) →
      (∀ s ∈ tops, ∀ r ∈ negRows, ¬ fires s (feature p q (row r))) →
      (∀ r ∈ posRows, ∃ s ∈ tops, fires s (feature p q (row r))) → False) : TablesImpossible := by
  intro p q tops cnt dp dq hn hp
  let a := separate p
  let b := separate q
  have notRepeated (s : Arms 13) (hs : s ∈ tops) : splitTags s := by
    intro i hi hL hR
    have existsRow : ∃ r ∈ negRows, feature p q (row r) i := by
      have idx : i = 11 ∨ i = 12 := by
        by_cases h : i.val = 11
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext (by change i.val = 12; omega))
      rcases idx with rfl|rfl
      · exact dp
      · exact dq
    obtain ⟨r,hr,yes⟩ := existsRow
    exact hn s hs r hr ⟨⟨i,hL,yes⟩,⟨i,hR,yes⟩⟩
  refine hard (trim a) (trim b) (canonical p) (canonical q)
    (tops.image (expand p q)) (Finset.card_image_le.trans cnt) ?_ ?_ ?_
  · intro s hs
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
    intro i hi hL hR
    exact notRepeated t ht i hi ((highExpanded p q hi _).1 hL) ((highExpanded p q hi _).1 hR)
  · intro s hs r hr fire
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
    apply hn t ht r hr
    apply (expandFires p q (row r) t).2
    apply firesMono _ (featureMono (trimLe a _) (trimLe b _)) fire
  · intro r hr
    obtain ⟨s,hs,on⟩ := hp r hr
    refine ⟨_,Finset.mem_image.mpr ⟨s,hs,rfl⟩,?_⟩
    exact firesMono _ (featureMono (trimPos hr).1 (trimPos hr).1) ((expandFires p q (row r) s).1 on)

def exclude (n m : ℕ) := n ^^^ (n &&& m)

lemma bitExclude {n m i : ℕ} (h : (exclude n m).testBit i = true) :
    n.testBit i = true ∧ m.testBit i = false := by
  simp only [exclude,Nat.testBit_xor,Nat.testBit_and] at h
  cases hi : n.testBit i <;> cases hj : m.testBit i <;> simp_all

def rejects (order env : List ℕ) : ℕ → ℕ → Bool
  | 0, need => order.any (need.testBit ·)
  | k+1, need => match order.find? (need.testBit ·) with
    | none => false
    | some i => env.all fun m => !m.testBit i || rejects order env k (exclude need m)

lemma rejectsSound (order env : List ℕ) (k need : ℕ) (pass : rejects order env k need = true)
    (used : Finset ℕ) (sub : ∀ m ∈ used, m ∈ env) (cnt : used.card ≤ k)
    (cov : ∀ i, need.testBit i = true → ∃ m ∈ used, m.testBit i = true) : False := by
  induction k generalizing need used with
  | zero =>
    obtain ⟨i,_,hi⟩ := List.any_eq_true.mp pass
    obtain ⟨m,hm,_⟩ := cov i hi
    have := Finset.card_pos.mpr (show used.Nonempty from ⟨m,hm⟩)
    omega
  | succ k ih =>
    unfold rejects at pass
    cases h : order.find? (need.testBit ·) with
    | none => simp [h] at pass
    | some i =>
      simp only [h] at pass
      have hi := List.find?_some h
      obtain ⟨m,hm,bit⟩ := cov i hi
      have smaller := List.all_eq_true.mp pass m (sub m hm)
      simp only [bit,Bool.not_true,Bool.false_or] at smaller
      apply ih _ smaller (used.erase m) (fun a ha => sub a (Finset.mem_erase.mp ha).2)
        (by rw [Finset.card_erase_of_mem hm]; have := Finset.card_pos.mpr (show used.Nonempty from ⟨m,hm⟩); omega)
      intro j hj
      obtain ⟨needed,off⟩ := bitExclude hj
      obtain ⟨v,hv,on⟩ := cov j needed
      refine ⟨v,Finset.mem_erase.mpr ⟨?_,hv⟩,on⟩
      rintro rfl
      simp [off] at on

def within (p q : Arms 11) (s : Arms 13) (m : ℕ) :=
  ∀ i : Fin 16, fires s (feature p q (row (posRows.getD i.val 0))) → m.testBit i.val = true

lemma coverageFails {env order : List ℕ} (checked : rejects order env 4 65535 = true)
    {p q : Arms 11} {tops : Finset (Arms 13)} (cnt : tops.card ≤ 4)
    (hpos : ∀ r ∈ posRows, ∃ s ∈ tops, fires s (feature p q (row r)))
    (caps : ∀ s ∈ tops, ∃ m ∈ env, within p q s m) : False := by
  classical
  let choice (s : Arms 13) := if hs : s ∈ tops then (caps s hs).choose else 0
  have hc (s : Arms 13) (hs : s ∈ tops) : choice s ∈ env ∧ within p q s (choice s) := by
    simpa only [choice,dite_eq_left hs] using (caps s hs).choose_spec
  apply rejectsSound order env 4 65535 checked (tops.image choice) _ (Finset.card_image_le.trans cnt)
  · intro i hi
    have bound : i < 16 := by
      by_contra! big
      have off := Nat.testBit_lt_two_pow (x:=65535) (i:=i) (Nat.lt_of_lt_of_le (by decide : 65535 < 2^16) (Nat.pow_le_pow_right (by decide) big))
      simp [off] at hi
    let j : Fin 16 := ⟨i,bound⟩
    have mem : posRows.getD j.val 0 ∈ posRows := by
      rw [List.getD_eq_getElem _ _ (show j.val < posRows.length from j.isLt)]
      exact List.getElem_mem _
    obtain ⟨s,hs,fire⟩ := hpos _ mem
    exact ⟨choice s,Finset.mem_image.mpr ⟨s,hs,rfl⟩,(hc s hs).2 j fire⟩
  · intro m hm
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hm
    exact (hc s hs).1

def rawSet (s : Finset (Fin 13)) : Finset (Fin 11) := Finset.univ.filter fun v => emb v ∈ s

lemma memRaw {s : Finset (Fin 13)} {v : Fin 11} : v ∈ rawSet s ↔ emb v ∈ s := by simp [rawSet]

def compatibleV (u v : Fin 11) := ∀ r ∈ negRows, ¬(row r u = true ∧ row r v = true)

lemma squareFree : ∀ a b c d : Fin 11, a ≠ b → c ≠ d → compatibleV a c →
    compatibleV b c → compatibleV a d → ¬compatibleV b d := by
  unfold compatibleV
  decide +kernel

def CleanPair (p q : Arms 11) (s : Arms 13) := ∀ r ∈ negRows, ¬fires s (feature p q (row r))

lemma compatibleCross {p q : Arms 11} {s : Arms 13} (clean : CleanPair p q s)
    {u v : Fin 11} (hu : u ∈ rawSet s.1) (hv : v ∈ rawSet s.2) : compatibleV u v := by
  rintro r hr ⟨a,b⟩
  exact clean r hr ⟨⟨_,memRaw.mp hu,(rawFeature p q _ _).2 a⟩,
    ⟨_,memRaw.mp hv,(rawFeature p q _ _).2 b⟩⟩

def atMostOne (S : Finset (Fin 11)) := ∀ a ∈ S, ∀ b ∈ S, a = b

lemma oriented {p q : Arms 11} {s : Arms 13} (clean : CleanPair p q s) :
    atMostOne (rawSet s.1) ∨ atMostOne (rawSet s.2) := by
  classical
  unfold atMostOne
  by_contra! h
  obtain ⟨a,ha,b,hb,diff⟩ := h.1
  obtain ⟨c,hc,d,hd,dist⟩ := h.2
  exact squareFree a b c d diff dist (compatibleCross clean ha hc) (compatibleCross clean hb hc)
    (compatibleCross clean ha hd) (compatibleCross clean hb hd)

def exchange {k : ℕ} (s : Arms k) : Arms k := (s.2,s.1)

lemma exchangeFires {k : ℕ} (s : Arms k) (x : Fin k → Prop) : fires (exchange s) x ↔ fires s x := and_comm

lemma exchangeClean {p q : Arms 11} {s : Arms 13} (h : CleanPair p q s) : CleanPair p q (exchange s) :=
  fun r hr fire => h r hr ((exchangeFires _ _).1 fire)

lemma exchangeSplit {s : Arms 13} (h : splitTags s) : splitTags (exchange s) :=
  fun i hi hR hL => h i hi hL hR

lemma centerExists {S : Finset (Fin 11)} (h : atMostOne S) :
    ∃ c : Fin 12, (c.val = 11 ∨ ∃ v ∈ S, v.val = c.val) ∧ ∀ i ∈ S, i.val = c.val := by
  classical
  by_cases emp : S.Nonempty
  · obtain ⟨a,ha⟩ := emp
    exact ⟨⟨a.val,by omega⟩,Or.inr ⟨a,ha,rfl⟩,fun i hi => congrArg Fin.val (h i hi a ha)⟩
  · exact ⟨11,Or.inl rfl,fun i hi => (emp ⟨i,hi⟩).elim⟩

def active (p : Arms 11) (r : ℕ) := fires p (fun i => row r i = true)
def safeV (p : Arms 11) (u : Fin 11) := ∀ r ∈ negRows, ¬(active p r ∧ row r u = true)
def safeJoint (p q : Arms 11) := ∀ r ∈ negRows, ¬(active p r ∧ active q r)

lemma guardCross {p q : Arms 11} {s : Arms 13} (clean : CleanPair p q s) {v : Fin 11} :
    (11 ∈ s.1 → v ∈ rawSet s.2 → safeV p v) ∧
    (12 ∈ s.1 → v ∈ rawSet s.2 → safeV q v) ∧
    (11 ∈ s.1 → 12 ∈ s.2 → safeJoint p q) ∧
    (12 ∈ s.1 → 11 ∈ s.2 → safeJoint p q) := by
  refine ⟨?_,?_,?_,?_⟩
  · rintro h k r hr ⟨a,b⟩
    exact clean r hr ⟨⟨11,h,a⟩,⟨_,memRaw.mp k,(rawFeature _ _ _ _).2 b⟩⟩
  · rintro h k r hr ⟨a,b⟩
    exact clean r hr ⟨⟨12,h,a⟩,⟨_,memRaw.mp k,(rawFeature _ _ _ _).2 b⟩⟩
  · rintro h k r hr ⟨a,b⟩
    exact clean r hr ⟨⟨11,h,a⟩,⟨12,k,b⟩⟩
  · rintro h k r hr ⟨a,b⟩
    exact clean r hr ⟨⟨12,h,b⟩,⟨11,k,a⟩⟩

lemma featureWitness {p q : Arms 11} {r : ℕ} {S : Finset (Fin 13)} (h : hit S (feature p q (row r))) :
    (∃ v ∈ rawSet S, row r v = true) ∨ (11 ∈ S ∧ active p r) ∨ (12 ∈ S ∧ active q r) := by
  obtain ⟨i,hi,v⟩ := h
  by_cases small : i.val < 11
  · let j : Fin 11 := ⟨i.val,small⟩
    have e : emb j = i := Fin.ext rfl
    exact Or.inl ⟨j,memRaw.mpr (e ▸ hi),(rawFeature _ _ _ _).1 (e ▸ v)⟩
  · have e : i = 11 ∨ i = 12 := by
      by_cases h : i.val = 11
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext (by change i.val = 12; omega))
    rcases e with rfl | rfl
    · exact Or.inr (Or.inl ⟨hi,v⟩)
    · exact Or.inr (Or.inr ⟨hi,v⟩)

def posAt (i : Fin 16) := posRows.getD i.val 0

abbrev Profile := ℕ × ℕ

def BoundsSingle (d : Arms 11) (p : Profile) : Prop :=
  (∀ v : Fin 11, safeV d v → p.1.testBit v.val = true) ∧
  ∀ (v : Fin 11) (i : Fin 16), safeV d v → row (posAt i) v = true → active d (posAt i) →
    p.2.testBit i.val = true

def BoundsJoint (p q : Arms 11) (j : ℕ) : Prop :=
  ∀ i : Fin 16, safeJoint p q → active p (posAt i) → active q (posAt i) → j.testBit i.val = true

def vertexRows : List ℕ := [3,12,48,192,772,3088,12352,20608,34056,51201,8738]

lemma vertexRowsOn : ∀ (v : Fin 11) (i : Fin 16), row (posAt i) v = true →
    (vertexRows.getD v.val 0).testBit i.val = true := by decide +kernel

def touchAux (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => (if b.testBit k then vertexRows.getD k 0 else 0) ||| touchAux b k

lemma touchAuxOn {b k v i : ℕ} (hv : v < k) (bv : b.testBit v = true)
    (vr : (vertexRows.getD v 0).testBit i = true) : (touchAux b k).testBit i = true := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [touchAux,Nat.testBit_or,Bool.or_eq_true]
    by_cases eq : v = k
    · subst v; exact Or.inl (by simpa [bv] using vr)
    · exact Or.inr (ih (by omega))

def nearRows : List ℕ := [1536,272,1056,192,1282,772,1160,584,562,417,85,2047]

lemma nearRowsOn : ∀ u v : Fin 11, compatibleV u v →
    (nearRows.getD u.val 0).testBit v.val = true := by unfold compatibleV; decide +kernel

lemma allVertices : ∀ i : Fin 11, Nat.testBit 2047 i.val = true := by decide

def rawCenter (c : Fin 12) := if c.val < 11 then 2^c.val else 0

lemma rawCenterOn {v : Fin 11} {c : Fin 12} (h : v.val = c.val) : (rawCenter c).testBit v.val = true := by
  have lt : c.val < 11 := h ▸ v.isLt
  simp [rawCenter,lt,h]

def sideMask (g h : ℕ) (c : Fin 12) (a b : Bool) :=
  nearRows.getD c.val 0 &&& (if a then g else 2047) &&& (if b then h else 2047)

def allow (c : Fin 12) (a : Bool) (g : ℕ) := !a && (decide (c.val = 11) || g.testBit c.val)

def tagged (b : Bool) (x : ℕ) := if b then x else 0

def limitMask (p q : Profile) (j : ℕ) (c : Fin 12) (a b : Bool) :=
  let t := touchAux (sideMask p.1 q.1 c a b) 11
  let raw := touchAux (rawCenter c) 11
  let x := allow c a p.1
  let y := allow c b q.1
  (raw &&& t) ||| tagged a (p.2 &&& t) ||| tagged b (q.2 &&& t) |||
    tagged x (p.2 &&& raw) ||| tagged y (q.2 &&& raw) ||| tagged ((x && b) || (y && a)) j

lemma limitBits {p q : Profile} {j : ℕ} {c : Fin 12} {a b : Bool} {i : ℕ} :
    (limitMask p q j c a b).testBit i = true ↔
      (((touchAux (rawCenter c) 11).testBit i = true ∧ (touchAux (sideMask p.1 q.1 c a b) 11).testBit i = true) ∨
      (a = true ∧ p.2.testBit i = true ∧ (touchAux (sideMask p.1 q.1 c a b) 11).testBit i = true) ∨
      (b = true ∧ q.2.testBit i = true ∧ (touchAux (sideMask p.1 q.1 c a b) 11).testBit i = true) ∨
      (allow c a p.1 = true ∧ p.2.testBit i = true ∧ (touchAux (rawCenter c) 11).testBit i = true) ∨
      (allow c b q.1 = true ∧ q.2.testBit i = true ∧ (touchAux (rawCenter c) 11).testBit i = true) ∨
      (((allow c a p.1 = true ∧ b = true) ∨ (allow c b q.1 = true ∧ a = true)) ∧ j.testBit i = true)) := by
  have tag (t : Bool) (m : ℕ) : (tagged t m).testBit i = true ↔ t = true ∧ m.testBit i = true := by
    cases t <;> simp [tagged]
  simp only [limitMask,Nat.testBit_or,Nat.testBit_and,Bool.or_eq_true,Bool.and_eq_true,tag,or_assoc,and_assoc]

lemma directedLimit {d e : Arms 11} {s : Arms 13} {p q : Profile} {j : ℕ}
    (hp : BoundsSingle d p) (hq : BoundsSingle e q) (joint : BoundsJoint d e j)
    (split : splitTags s) (clean : CleanPair d e s) (one : atMostOne (rawSet s.1)) :
    ∃ c a b, within d e s (limitMask p q j c a b) := by
  classical
  obtain ⟨c,hc,center⟩ := centerExists one
  let a := decide ((11 : Fin 13) ∈ s.1)
  let b := decide ((12 : Fin 13) ∈ s.1)
  have hA : a = true ↔ (11 : Fin 13) ∈ s.1 := decide_eq_true_iff
  have hB : b = true ↔ (12 : Fin 13) ∈ s.1 := decide_eq_true_iff
  have cross (v : Fin 11) := guardCross (v:=v) clean
  have rev (v : Fin 11) := guardCross (v:=v) (exchangeClean clean)
  have guardP {v : Fin 11} (ht : (11 : Fin 13) ∈ s.2) (hv : v ∈ rawSet s.1) := (rev v).1 ht hv
  have guardQ {v : Fin 11} (ht : (12 : Fin 13) ∈ s.2) (hv : v ∈ rawSet s.1) := (rev v).2.1 ht hv
  have allowedP (ht : (11 : Fin 13) ∈ s.2) : allow c a p.1 = true := by
    have off : (11 : Fin 13) ∉ s.1 := fun h => split 11 (by decide) h ht
    simp only [allow,a,decide_eq_false off,Bool.not_false,Bool.true_and,Bool.or_eq_true,decide_eq_true_eq]
    rcases hc with h | ⟨v,hv,eq⟩
    · exact Or.inl h
    · exact Or.inr (eq ▸ hp.1 v (guardP ht hv))
  have allowedQ (ht : (12 : Fin 13) ∈ s.2) : allow c b q.1 = true := by
    have off : (12 : Fin 13) ∉ s.1 := fun h => split 12 (by decide) h ht
    simp only [allow,b,decide_eq_false off,Bool.not_false,Bool.true_and,Bool.or_eq_true,decide_eq_true_eq]
    rcases hc with h | ⟨v,hv,eq⟩
    · exact Or.inl h
    · exact Or.inr (eq ▸ hq.1 v (guardQ ht hv))
  have onB {v : Fin 11} (hv : v ∈ rawSet s.2) : (sideMask p.1 q.1 c a b).testBit v.val = true := by
    simp only [sideMask,Nat.testBit_and,Bool.and_eq_true]
    refine ⟨⟨?_,?_⟩,?_⟩
    · rcases hc with h | ⟨u,hu,eq⟩
      · rw [h]; exact allVertices v
      · rw [← eq]; exact nearRowsOn u v (compatibleCross clean hu hv)
    · by_cases h : a = true
      · simp [h,hp.1 v ((cross v).1 (hA.1 h) hv)]
      · simp [h,allVertices]
    · by_cases h : b = true
      · simp [h,hq.1 v ((cross v).2.1 (hB.1 h) hv)]
      · simp [h,allVertices]
  refine ⟨c,a,b,?_⟩
  intro i fire
  have rawOn {v : Fin 11} (hv : v ∈ rawSet s.1) (h : row (posAt i) v = true) :=
    touchAuxOn v.isLt (rawCenterOn (center v hv)) (vertexRowsOn v i h)
  have otherOn {v : Fin 11} (hv : v ∈ rawSet s.2) (h : row (posAt i) v = true) :=
    touchAuxOn v.isLt (onB hv) (vertexRowsOn v i h)
  apply limitBits.2
  rcases featureWitness fire.1 with ⟨u,hu,vu⟩ | ⟨L,pv⟩ | ⟨L,qv⟩
  · rcases featureWitness fire.2 with ⟨v,hv,vv⟩ | ⟨R,pv⟩ | ⟨R,qv⟩
    · exact Or.inl ⟨rawOn hu vu,otherOn hv vv⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨allowedP R,hp.2 u i (guardP R hu) vu pv,rawOn hu vu⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨allowedQ R,hq.2 u i (guardQ R hu) vu qv,rawOn hu vu⟩))))
  · rcases featureWitness fire.2 with ⟨v,hv,vv⟩ | ⟨R,_⟩ | ⟨R,qv⟩
    · exact Or.inr (Or.inl ⟨hA.2 L,hp.2 v i ((cross v).1 L hv) vv pv,otherOn hv vv⟩)
    · exact (split 11 (by decide) L R).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨Or.inr ⟨allowedQ R,hA.2 L⟩,joint i ((cross 0).2.2.1 L R) pv qv⟩))))
  · rcases featureWitness fire.2 with ⟨v,hv,vv⟩ | ⟨R,pv⟩ | ⟨R,_⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hB.2 L,hq.2 v i ((cross v).2.1 L hv) vv qv,otherOn hv vv⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨Or.inl ⟨allowedP R,hB.2 L⟩,joint i ((cross 0).2.2.2 L R) pv qv⟩))))
    · exact (split 12 (by decide) L R).elim

lemma boundedLimit {d e : Arms 11} {s : Arms 13} {p q : Profile} {j : ℕ}
    (hp : BoundsSingle d p) (hq : BoundsSingle e q) (joint : BoundsJoint d e j)
    (split : splitTags s) (clean : CleanPair d e s) :
    ∃ c a b, within d e s (limitMask p q j c a b) := by
  rcases oriented clean with h | h
  · exact directedLimit hp hq joint split clean h
  · obtain ⟨c,a,b,lim⟩ := directedLimit hp hq joint (exchangeSplit split) (exchangeClean clean) h
    exact ⟨c,a,b,fun i h => lim i ((exchangeFires _ _).2 h)⟩

def envelope0 : List ℕ × List ℕ := ([7, 2, 5, 11, 1, 0, 4, 6, 3, 12, 10, 8, 14, 13, 9, 15], [46954, 64841, 46411, 46456, 46924, 48472, 62920, 30498, 53001, 36632, 42761, 44568, 52504, 55048, 56065, 57954, 58180, 59144, 59913, 60496, 62088, 13059, 18188, 21260, 21440, 21763, 21772, 21808, 22276, 23824, 29444, 29504, 34315, 34360, 41483, 41528, 41672, 50444, 53507, 57411, 57420, 57456, 57859, 61506, 62016, 62208, 9008, 9776, 10000, 12992, 7680])

lemma checked0 : rejects envelope0.1 envelope0.2 4 65535 = true := by decide +kernel

def envelope1 : List ℕ × List ℕ := ([12, 5, 11, 0, 2, 4, 1, 10, 3, 8, 9, 15, 13, 6, 7, 14], [42986, 52681, 30152, 34251, 34296, 34764, 36312, 46536, 54728, 59272, 28304, 52504, 60033, 9156, 17292, 25186, 25219, 25228, 25250, 25264, 25476, 29376, 52304, 24769, 24770, 49924, 61504, 16451, 16496, 17216, 49155, 49164])

lemma checked1 : rejects envelope1.1 envelope1.2 4 65535 = true := by decide +kernel

def envelope2 : List ℕ × List ℕ := ([0, 7, 5, 3, 8, 2, 6, 1, 9, 12, 15, 13, 4, 10, 11, 14], [15986, 16212, 44826, 48472, 60947, 64593, 15443, 15452, 30258, 31952, 32386, 60744, 11790, 11970, 12038, 22292, 27234, 27460, 52504, 53000, 54552, 55363, 56464, 1814, 21523, 21532, 21650, 22547, 23600, 26691, 26700, 26736, 27696, 28784, 30768, 30786, 30816, 35590, 41522, 49926, 51972, 52272, 61632, 1054, 1234, 1564, 12803, 20674, 29248, 33294, 33556, 33842, 34564, 35376, 41732, 51392, 32796, 33804, 34828, 42016, 49164, 57376])

lemma checked2 : rejects envelope2.1 envelope2.2 4 65535 = true := by decide +kernel

def envelope3 : List ℕ × List ℕ := ([3, 6, 11, 5, 4, 1, 7, 0, 10, 12, 13, 2, 8, 15, 14, 9], [24468, 29606, 55180, 56197, 21383, 21428, 29636, 46348, 52741, 52756, 57894, 62020, 29313, 40080, 41762, 42760, 49671, 49716, 49860, 52481, 52496, 63489, 1588, 1828, 8963, 9008, 12803, 24707, 24752, 25091, 33542, 34561, 34576, 49411, 53251, 8716, 1088])

lemma checked3 : rejects envelope3.1 envelope3.2 4 65535 = true := by decide +kernel

def envelope4 : List ℕ × List ℕ := ([2, 0, 4, 6, 7, 12, 1, 8, 14, 3, 13, 10, 15, 11, 5, 9], [42795, 42798, 42810, 44841, 44842, 60195, 60459, 60707, 60963, 61224, 62634, 12067, 12082, 42218, 43826, 44090, 44338, 44594, 46186, 52491, 52747, 53001, 53004, 56712, 59948, 60128, 60196, 60976, 64096, 64160, 13642, 13898, 21898, 22154, 27186, 29282, 29346, 31266, 31552, 36152, 36408, 36632, 45416, 45672, 51497, 51753, 52504, 53672, 53928, 61986, 1482, 1738, 3354, 3610, 3846, 3876, 8930, 19248, 19392, 20240, 23424, 33256, 33512, 31744])

lemma checked4 : rejects envelope4.1 envelope4.2 4 65535 = true := by decide +kernel

def envelope5 : List ℕ × List ℕ := ([13, 12, 1, 14, 8, 0, 3, 2, 6, 9, 7, 15, 11, 10, 5, 4], [12018, 4052, 34296, 36312, 51441, 52433, 1012, 3283, 3292, 3892, 15568, 23760, 36152, 52273, 243, 252, 12528, 15456, 20720, 22704, 33588, 34353, 34584, 34600, 35363, 51729, 563, 3107, 32819, 33827, 34564, 34835, 35588, 540, 556, 1068, 1548, 2092, 21536, 53376, 32780])

lemma checked5 : rejects envelope5.1 envelope5.2 4 65535 = true := by decide +kernel

def envelope6 : List ℕ × List ℕ := ([6, 9, 8, 1, 4, 15, 0, 2, 3, 10, 13, 11, 5, 7, 12, 14], [29358, 23708, 54668, 55437, 56457, 58792, 20623, 20668, 21388, 25508, 27824, 28876, 40328, 59553, 1836, 3132, 9766, 22704, 24739, 26659, 28833, 28848, 28896, 30768, 52229, 52488, 55329, 63489, 7216, 12323, 22531, 30784, 1031, 3264, 13328, 18624, 37920, 46080])

lemma checked6 : rejects envelope6.1 envelope6.2 4 65535 = true := by decide +kernel

def envelope7 : List ℕ × List ℕ := ([3, 4, 12, 13, 14, 0, 1, 6, 5, 7, 15, 8, 10, 11, 9, 2], [52165, 4052, 9190, 34764, 967, 1012, 11814, 13252, 15940, 21444, 24196, 36620, 43558, 47684, 52609, 52741, 55940, 3380, 3591, 3636, 34092, 35335, 35380, 36372, 1828, 547, 556])

lemma checked7 : rejects envelope7.1 envelope7.2 4 65535 = true := by decide +kernel

def envelope8 : List ℕ × List ℕ := ([6, 11, 3, 2, 1, 8, 9, 10, 7, 0, 15, 12, 13, 14, 4, 5], [54712, 14002, 21428, 29362, 55473, 56465, 6036, 12963, 20659, 20668, 23728, 28912, 29904, 49957, 49972, 50473, 52273, 57891, 57906, 61537, 61552, 63505, 5267, 5276, 8755, 9763, 12339, 31760, 34584, 42033, 42264, 42784, 49197, 49203, 49212, 49377, 49392, 8996, 9008, 11312, 12481, 12896, 28801, 30848, 34561, 33795, 524])

lemma checked8 : rejects envelope8.1 envelope8.2 4 65535 = true := by decide +kernel

def envelope9 : List ℕ × List ℕ := ([7, 11, 4, 5, 10, 0, 8, 14, 1, 6, 9, 12, 13, 3, 15, 2], [63565, 12910, 15452, 38732, 46412, 12367, 12412, 13132, 28876, 41510, 50444, 33546, 35860, 41736, 53380, 519, 774, 8707, 32775, 32820, 49155, 20992, 49664])

lemma checked9 : rejects envelope9.1 envelope9.2 4 65535 = true := by decide +kernel

def envelope10 : List ℕ × List ℕ := ([5, 0, 1, 4, 11, 6, 2, 13, 9, 14, 15, 10, 3, 7, 8, 12], [14250, 56713, 5515, 5560, 6028, 7576, 13768, 37772, 52504, 34572, 38664, 53388, 28864, 29056, 17156, 45120, 49155, 49344])

lemma checked10 : rejects envelope10.1 envelope10.2 4 65535 = true := by decide +kernel

def envelope11 : List ℕ × List ℕ := ([0, 6, 3, 2, 4, 8, 5, 10, 15, 9, 13, 1, 11, 7, 12, 14], [51114, 64035, 20146, 29347, 29410, 51875, 17070, 17318, 38282, 55427, 59523, 4998, 7314, 8998, 25138, 25378, 30768, 42760, 52488, 54536, 4238, 4274, 11312, 13060, 15376, 19648, 22672, 22720, 23568, 30784, 30848, 52225, 52240, 53440, 61504, 1796, 8716, 33540, 46080])

lemma checked11 : rejects envelope11.1 envelope11.2 4 65535 = true := by decide +kernel

def envelope12 : List ℕ × List ℕ := ([7, 8, 1, 4, 12, 6, 3, 10, 5, 2, 13, 15, 14, 9, 0, 11], [53005, 10799, 27175, 31301, 44593, 59939, 14413, 18997, 19141, 19989, 22669, 23173, 41511, 51719, 51761, 52249, 52273, 59441, 60161, 63521, 63553, 63617, 64001, 1596, 1836, 2109, 2253, 3101, 9763, 33295, 51393, 2852, 3128, 14432, 25348, 26720, 28768, 33572, 33803, 35364, 41732, 41760, 45632, 57860, 57920, 3075, 3586, 24768])

lemma checked12 : rejects envelope12.1 envelope12.2 4 65535 = true := by decide +kernel

def envelope13 : List ℕ × List ℕ := ([7, 1, 3, 2, 4, 5, 9, 14, 12, 10, 8, 6, 13, 11, 15, 0], [64035, 43619, 43845, 44361, 63555, 63681, 12899, 25187, 38217, 43085, 43121, 44113, 52489, 56577, 4933, 7249, 52241, 59649, 3844, 4173, 4209, 9988, 11312, 12400, 15616, 34051, 49924, 8992, 18480, 34560, 49164])

lemma checked13 : rejects envelope13.1 envelope13.2 4 65535 = true := by decide +kernel

def envelope14 : List ℕ × List ℕ := ([4, 6, 7, 12, 8, 3, 5, 10, 11, 2, 14, 9, 13, 15, 0, 1], [59955, 60195, 11827, 42547, 42793, 51975, 52491, 53001, 8999, 29282, 29345, 41766, 42786, 52243, 52273, 63554, 63617, 1799, 12835, 34570, 55299, 12355, 20611, 28737, 28802, 34564, 15, 195, 525, 526, 2062, 8385, 8386, 16577, 16578, 24768, 32781, 32782, 33292, 1036])

lemma checked14 : rejects envelope14.1 envelope14.2 4 65535 = true := by decide +kernel

def envelope15 : List ℕ × List ℕ := ([5, 12, 4, 10, 9, 8, 0, 11, 14, 15, 13, 3, 6, 7, 1, 2], [8942, 51405, 3292, 34252, 51215, 51395, 207, 252, 972, 12492, 20684, 24771, 28866, 33550, 34062, 59395, 519, 3078, 8242, 8962, 10256, 41216])

lemma checked15 : rejects envelope15.1 envelope15.2 4 65535 = true := by decide +kernel

def envelope16 : List ℕ × List ℕ := ([2, 3, 9, 12, 13, 8, 5, 10, 11, 14, 4, 15, 6, 7, 1, 0], [34251, 967, 3283, 8931, 51395, 207, 243, 8755, 12483, 20675, 33843, 34073, 34865, 35857, 18449, 49409, 53249])

lemma checked16 : rejects envelope16.1 envelope16.2 4 65535 = true := by decide +kernel

def envelope17 : List ℕ × List ℕ := ([9, 15, 7, 6, 10, 12, 14, 13, 11, 3, 1, 5, 8, 0, 2, 4], [51261, 3103, 8751, 8766, 8999, 9014, 12367, 12412, 20623, 20668, 34063, 34108, 51215, 51477, 51505, 63, 207, 252, 783, 819, 828, 3123, 3132, 3347, 3349, 8755, 12613, 12628, 20869, 20884, 34073, 51219, 51459, 279, 309, 453, 468, 3352, 3376, 12386, 19473, 28832, 14352, 28736, 8384])

lemma checked17 : rejects envelope17.1 envelope17.2 4 65535 = true := by decide +kernel

def envelope18 : List ℕ × List ℕ := ([7, 6, 10, 9, 12, 13, 0, 2, 1, 8, 14, 15, 3, 5, 11, 4], [10814, 11058, 14428, 22684, 33596, 36124, 41530, 41778, 45176, 51229, 51257, 52504, 53432, 2079, 2268, 2844, 26659, 32827, 33016, 34104, 35091, 35896, 51473, 18451, 19504, 22576, 28768, 49187, 49440])

lemma checked18 : rejects envelope18.1 envelope18.2 4 65535 = true := by decide +kernel

def envelope19 : List ℕ × List ℕ := ([3, 7, 11, 14, 0, 1, 4, 5, 10, 15, 13, 9, 6, 12, 2, 8], [13158, 55621, 7508, 29124, 38220, 4423, 4468, 9156, 34572, 37636, 8707, 8752])

lemma checked19 : rejects envelope19.1 envelope19.2 4 65535 = true := by decide +kernel

def envelope20 : List ℕ × List ℕ := ([3, 6, 7, 1, 2, 12, 4, 13, 5, 8, 14, 0, 10, 11, 15, 9], [53005, 27427, 51975, 8999, 10019, 43555, 52497, 3377, 3843, 41762, 51729, 55425, 55809, 1828, 3348, 3601, 3632, 29248, 34051, 34576, 61504, 20612, 28800, 33840, 34864, 52, 12292, 13312, 16576, 21504, 32960])

lemma checked20 : rejects envelope20.1 envelope20.2 4 65535 = true := by decide +kernel

def envelope21 : List ℕ × List ℕ := ([6, 2, 7, 12, 15, 14, 5, 13, 8, 3, 9, 0, 4, 11, 1, 10], [42778, 52505, 59923, 1807, 9771, 11058, 11826, 13387, 21643, 52235, 52243, 1083, 1227, 3099, 3860, 8755, 8762, 8995, 10018, 10787, 34059, 796, 1840, 2099, 2332, 3346, 3376, 22657, 23680, 1052, 3084, 14400, 15360, 28800, 33537, 35584, 16576])

lemma checked21 : rejects envelope21.1 envelope21.2 4 65535 = true := by decide +kernel

def envelope22 : List ℕ × List ℕ := ([6, 7, 12, 13, 3, 10, 1, 5, 14, 0, 8, 15, 2, 4, 9, 11], [36636, 3892, 9014, 10806, 14932, 23188, 51733, 52497, 1596, 2583, 2772, 35632, 51213, 51461, 51465, 33542, 34096, 35331, 51203])

lemma checked22 : rejects envelope22.1 envelope22.2 4 65535 = true := by decide +kernel

def envelope23 : List ℕ × List ℕ := ([6, 7, 1, 3, 2, 12, 13, 0, 9, 14, 8, 4, 10, 15, 5, 11], [52505, 43555, 51251, 52273, 3123, 8755, 10802, 15408, 34089, 34600, 35859, 51489, 55329, 55425, 1828, 3376, 3844, 9008, 10016, 12400, 22672, 28768, 30784, 30848, 33572, 34564, 35588, 3084, 18624, 33804, 34828, 208])

lemma checked23 : rejects envelope23.1 envelope23.2 4 65535 = true := by decide +kernel

def envelope24 : List ℕ × List ℕ := ([6, 2, 7, 4, 12, 3, 13, 5, 11, 14, 1, 9, 8, 0, 10, 15], [52505, 34571, 36107, 42786, 8995, 33295, 34572, 41507, 51459, 55425, 33541, 54400, 61504, 3120, 33840, 34864, 46080, 49344])

lemma checked24 : rejects envelope24.1 envelope24.2 4 65535 = true := by decide +kernel

def envelope25 : List ℕ × List ℕ := ([6, 7, 0, 2, 12, 3, 14, 4, 8, 1, 15, 10, 11, 13, 9, 5], [11827, 12082, 10022, 36632, 52243, 12898, 14882, 34104, 34600, 51235, 51249, 28832, 30848, 556, 1548, 8416, 33540])

lemma checked25 : rejects envelope25.1 envelope25.2 4 65535 = true := by decide +kernel

def envelope26 : List ℕ × List ℕ := ([6, 2, 7, 14, 0, 12, 13, 3, 1, 8, 9, 11, 4, 5, 15, 10], [52505, 34604, 34616, 36152, 1596, 1844, 9010, 9778, 10018, 35868, 23680, 54400, 55424, 3075, 12384, 13376, 32803, 33795, 34819, 1216])

lemma checked26 : rejects envelope26.1 envelope26.2 4 65535 = true := by decide +kernel

def envelope27 : List ℕ × List ℕ := ([6, 4, 7, 11, 13, 2, 5, 14, 3, 8, 10, 12, 9, 15, 0, 1], [52491, 34571, 34574, 36121, 8995, 12835, 33295, 33543, 55299, 1039, 4291, 12355, 20611, 53377, 562, 1074])

lemma checked27 : rejects envelope27.1 envelope27.2 4 65535 = true := by decide +kernel

def envelope28 : List ℕ × List ℕ := ([0, 1, 3, 6, 2, 8, 9, 13, 5, 15, 7, 10, 11, 12, 4, 14], [56465, 52504, 12850, 19664, 22704, 28848, 7216, 28864, 51203, 1796, 33540, 1036])

lemma checked28 : rejects envelope28.1 envelope28.2 4 65535 = true := by decide +kernel

def envelope29 : List ℕ × List ℕ := ([6, 5, 7, 12, 13, 14, 15, 11, 4, 10, 0, 2, 3, 8, 1, 9], [8766, 8999, 9782, 34573, 1820, 34076, 51211, 51459, 51715, 527, 782, 3345, 3856, 12866, 3096, 20609, 21120, 192])

lemma checked29 : rejects envelope29.1 envelope29.2 4 65535 = true := by decide +kernel

def envelope30 : List ℕ × List ℕ := ([2, 15, 3, 6, 1, 4, 5, 7, 8, 9, 0, 11, 12, 10, 13, 14], [56705, 24771, 25123, 12834, 28737, 28802, 28864, 50440, 1796, 3120, 18449, 19472, 3080, 16432, 17152, 12])

lemma checked30 : rejects envelope30.1 envelope30.2 4 65535 = true := by decide +kernel

def envelope31 : List ℕ × List ℕ := ([6, 7, 12, 0, 1, 13, 14, 2, 8, 10, 11, 15, 3, 9, 4, 5], [9014, 34588, 8750, 51473, 572, 3376, 12896, 35864, 51209, 547, 1080, 20608, 192])

lemma checked31 : rejects envelope31.1 envelope31.2 4 65535 = true := by decide +kernel

def envelope32 : List ℕ × List ℕ := ([0, 1, 5, 6, 7, 8, 9, 12, 13, 14, 15, 2, 3, 4, 10, 11], [36124, 52249, 8758, 1804, 3120, 22656, 2051, 12352, 192])

lemma checked32 : rejects envelope32.1 envelope32.2 4 65535 = true := by decide +kernel

def envelope33 : List ℕ × List ℕ := ([2, 3, 4, 8, 10, 11, 15, 5, 9, 6, 7, 12, 14, 0, 1, 13], [8931, 12899, 55427, 24771, 28739, 28803, 28865, 28866, 50441, 8966, 19473, 8242, 12])

lemma checked33 : rejects envelope33.1 envelope33.2 4 65535 = true := by decide +kernel

def envelope34 : List ℕ × List ℕ := ([0, 1, 2, 3, 7, 9, 10, 11, 8, 6, 12, 14, 15, 5, 4, 13], [12914, 55313, 8432, 8996, 28752, 28864, 34072, 3120, 8227, 41216, 57344, 12])

lemma checked34 : rejects envelope34.1 envelope34.2 4 65535 = true := by decide +kernel

def envelope35 : List ℕ × List ℕ := ([2, 3, 12, 0, 1, 8, 9, 10, 15, 4, 6, 7, 13, 14, 5, 11], [8432, 8802, 12512, 18640, 22720, 51329, 52240, 3120, 8227, 8992, 18435, 34056, 772, 12])

lemma checked35 : rejects envelope35.1 envelope35.2 4 65535 = true := by decide +kernel

def catalogue : List (List ℕ × List ℕ) := [envelope0, envelope1, envelope2, envelope3, envelope4, envelope5, envelope6, envelope7, envelope8, envelope9, envelope10, envelope11, envelope12, envelope13, envelope14, envelope15, envelope16, envelope17, envelope18, envelope19, envelope20, envelope21, envelope22, envelope23, envelope24, envelope25, envelope26, envelope27, envelope28, envelope29, envelope30, envelope31, envelope32, envelope33, envelope34, envelope35]

lemma catalogueChecked {c : List ℕ × List ℕ} (h : c ∈ catalogue) : rejects c.1 c.2 4 65535 = true := by
  simp only [catalogue,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checked0
  · exact checked1
  · exact checked2
  · exact checked3
  · exact checked4
  · exact checked5
  · exact checked6
  · exact checked7
  · exact checked8
  · exact checked9
  · exact checked10
  · exact checked11
  · exact checked12
  · exact checked13
  · exact checked14
  · exact checked15
  · exact checked16
  · exact checked17
  · exact checked18
  · exact checked19
  · exact checked20
  · exact checked21
  · exact checked22
  · exact checked23
  · exact checked24
  · exact checked25
  · exact checked26
  · exact checked27
  · exact checked28
  · exact checked29
  · exact checked30
  · exact checked31
  · exact checked32
  · exact checked33
  · exact checked34
  · exact checked35

abbrev Box := Profile × Profile × ℕ

def boxAccept (env : List ℕ) (t : Box) := (List.finRange 12).all fun c =>
  [false,true].all fun a => [false,true].all fun b =>
    let m := limitMask t.1 t.2.1 t.2.2 c a b
    env.any fun n => (m &&& n) == m

lemma boxCaps {env : List ℕ} {t : Box} (h : boxAccept env t = true) (c : Fin 12) (a b : Bool) :
    ∃ n ∈ env, ∀ i, (limitMask t.1 t.2.1 t.2.2 c a b).testBit i = true → n.testBit i = true := by
  have hc := List.all_eq_true.mp h c (List.mem_finRange c)
  have al (x : Bool) : x ∈ [false,true] := by cases x <;> simp
  have hc' := List.all_eq_true.mp (List.all_eq_true.mp hc a (al a)) b (al b)
  obtain ⟨n,hn,eq⟩ := List.any_eq_true.mp hc'
  refine ⟨n,hn,?_⟩
  have key := beq_iff_eq.mp eq
  intro i hi
  have bits := congrArg (fun m : ℕ => m.testBit i) key
  simp only [Nat.testBit_and,hi,Bool.true_and] at bits
  exact bits

def Mirrors (d e : Arms 11) (t : Box) := BoundsSingle d t.1 ∧ BoundsSingle e t.2.1 ∧ BoundsJoint d e t.2.2

def CoversProfiles (boxes : List Box) := ∀ d e : Arms 11, Canonical d → Canonical e →
  ∃ t ∈ boxes, Mirrors d e t ∨ Mirrors e d t

lemma swapLimit (p q : Profile) (j) (c : Fin 12) (a b : Bool) :
    limitMask p q j c a b = limitMask q p j c b a := by
  have side : sideMask p.1 q.1 c a b = sideMask q.1 p.1 c b a := by
    simp only [sideMask,Nat.and_left_comm,Nat.and_comm]
  rw [limitMask,limitMask,side]
  simp only [Bool.or_comm (x := allow c a p.1 && b) (y := allow c b q.1 && a)]
  ac_rfl

lemma certCloses {boxes : List Box} (hboxes : CoversProfiles boxes)
    (valid : ∀ t ∈ boxes, ∃ group ∈ catalogue, boxAccept group.2 t = true) : TablesImpossible := by
  apply coreReduction
  intro d e hd he tops cap separate clean pos
  obtain ⟨t,ht,hde⟩ := hboxes d e hd he
  obtain ⟨group,inCat,accepted⟩ := valid t ht
  apply coverageFails (catalogueChecked inCat) cap pos
  intro s hs
  have use {p q : Profile} {j : ℕ} (hp : BoundsSingle d p) (hq : BoundsSingle e q)
      (joint : BoundsJoint d e j) := boundedLimit (s:=s) hp hq joint (separate s hs) (clean s hs)
  rcases hde with v | v
  · obtain ⟨c,a,b,m⟩ := use v.1 v.2.1 v.2.2
    obtain ⟨n,hn,bits⟩ := boxCaps accepted c a b
    exact ⟨n,hn,fun i f => bits i.val (m i f)⟩
  · have joint : BoundsJoint d e t.2.2 := fun i sj h1 h2 =>
      v.2.2 i (fun r hr h => sj r hr h.symm) h2 h1
    obtain ⟨c,a,b,m⟩ := use v.2.1 v.1 joint
    obtain ⟨n,hn,bits⟩ := boxCaps accepted c b a
    rw [swapLimit] at m
    exact ⟨n,hn,fun i f => bits i.val (m i f)⟩

def box0_0 : List Box := [((2047,46408),(2047,46408),46408),((929,52489),(2047,34056),34056),((1392,46456),(2047,46408),46408),((2042,13124),(2047,46920),8448),((2047,0),(2047,0),21760),((2042,54536),(2047,46408),37120),((2047,0),(2047,0),41480),((2047,0),(2047,0),57408),((2047,61760),(2047,54536),0),((853,34568),(2047,0),34312),((1013,34568),(2047,12352),41216),((605,8384),(2047,50440),0)]

lemma box0_0ok : box0_0.all (boxAccept envelope0.2) = true := by decide +kernel

def box0_12 : List Box := [((1959,33804),(2047,12864),0),((1216,12898),(2047,42760),8704),((947,52489),(2047,61504),0),((2000,46411),(2047,46408),0),((1248,12384),(2047,34568),0),((1866,49408),(2047,29184),16640),((853,34568),(2042,13124),768),((820,36120),(2047,45888),256),((844,50176),(2047,0),17408),((1001,62792),(2042,53504),53248),((1013,34568),(2046,54536),33024),((2047,61440),(2047,41728),8192)]

lemma box0_12ok : box0_12.all (boxAccept envelope0.2) = true := by decide +kernel

def box0_24 : List Box := [((2047,61504),(1994,12864),12544),((501,28736),(861,50952),16384),((1870,50440),(1722,8960),256),((1546,8704),(2047,0),4864),((1546,49152),(2047,0),20736),((520,49152),(2047,0),54536),((1001,62792),(2047,45888),8192),((947,52489),(1722,8960),256),((1434,8964),(2047,28672),12608),((1026,8704),(2047,0),4928),((1016,53256),(2047,12800),45128),((176,768),(2047,0),41472)]

lemma box0_24ok : box0_24.all (boxAccept envelope0.2) = true := by decide +kernel

def box0_36 : List Box := [((690,23553),(2047,28736),57408),((2047,46920),(1808,34057),33032),((1722,53248),(1216,8802),0),((2027,62792),(1176,8964),8448),((2027,29248),(784,52489),16384),((2047,42760),(1728,12354),8192),((1498,13124),(1918,50456),0),((1870,46604),(1005,62528),0),((1392,46456),(2027,62792),0),((1914,50456),(1216,12898),0),((993,64841),(2000,46411),0),((1914,50456),(1248,12384),0)]

lemma box0_36ok : box0_36.all (boxAccept envelope0.2) = true := by decide +kernel

def box0_48 : List Box := [((2031,50444),(1728,12354),0),((820,36120),(481,28736),0),((1808,50441),(1216,12898),0),((768,51465),(1216,12898),0),((949,36104),(1216,12898),0),((1328,34072),(1728,12354),0),((288,3352),(1216,12898),0),((1808,50441),(1728,12354),0),((1728,12354),(949,36104),0),((304,3352),(1728,12354),0)]

lemma box0_48ok : box0_48.all (boxAccept envelope0.2) = true := by decide +kernel

def box1_0 : List Box := [((1023,51080),(2047,34056),34056),((2047,192),(2047,34248),34248),((1808,34057),(2047,50632),34056),((2047,0),(2047,0),25216),((1959,33804),(2047,34248),33800),((1449,16576),(2047,34248),192),((840,50440),(2047,16576),17800),((2047,8384),(1013,34568),0),((2047,8896),(1791,9152),8832),((754,49280),(2047,192),34248),((1886,50440),(2047,192),0),((1474,12864),(2047,16576),64)]

lemma box1_0ok : box1_0.all (boxAccept envelope1.2) = true := by decide +kernel

def box1_12 : List Box := [((1449,16576),(2047,0),16448),((2047,8384),(818,52489),0),((2047,24768),(949,36104),0),((1722,8960),(1866,12864),8704),((304,3352),(2047,24768),0),((2047,16576),(1328,34072),0),((754,49280),(1900,50456),49152),((754,49280),(1866,49408),49152),((1722,8960),(754,49280),0),((605,8384),(754,49280),128),((578,49152),(2047,0),16768),((1449,16576),(1870,50432),16384)]

lemma box1_12ok : box1_12.all (boxAccept envelope1.2) = true := by decide +kernel

def box1_24 : List Box := [((1432,8708),(1994,12864),8704),((501,33536),(1474,12864),512),((754,49280),(1443,32780),32768),((1866,12800),(754,49280),0),((818,52489),(1449,16576),16384),((160,16512),(2047,0),49216),((605,8384),(1432,8964),8192),((856,49160),(1449,16576),16384),((1866,12800),(1328,34072),0),((1994,12864),(433,3336),0),((1328,34072),(605,8384),0),((1808,34057),(605,8384),0)]

lemma box1_24ok : box1_24.all (boxAccept envelope1.2) = true := by decide +kernel

def box1_36 : List Box := [((1298,34572),(2043,49352),32776),((1432,8964),(433,3336),0)]

lemma box1_36ok : box1_36.all (boxAccept envelope1.2) = true := by decide +kernel

def box2_0 : List Box := [((2047,3088),(2047,15440),15440),((2047,0),(2047,0),11778),((1023,19504),(2047,23568),3088),((2047,0),(2047,0),21520),((2047,0),(2047,0),26688),((2047,0),(2047,0),1042),((1994,12864),(2047,15440),12288),((1015,3120),(2047,12864),0),((2047,30800),(2047,23568),2064),((754,53376),(2047,12352),4096),((1996,22656),(2047,15440),6160),((1449,8195),(2047,12352),8192)]

lemma box2_0ok : box2_0.all (boxAccept envelope2.2) = true := by decide +kernel

def box2_12 : List Box := [((2047,19472),(605,8384),0),((481,28736),(2047,0),26688),((1586,34832),(2047,61504),0),((1953,52241),(2047,61504),0),((1314,3344),(2047,29248),0),((1798,35072),(2047,30784),0),((1786,56464),(2047,19472),17424),((1828,52241),(2047,29248),0),((1248,12384),(2047,3088),8272),((1808,518),(2047,15440),0),((1728,12354),(2047,19472),0),((1552,774),(2047,15440),0)]

lemma box2_12ok : box2_12.all (boxAccept envelope2.2) = true := by decide +kernel

def box2_24 : List Box := [((1120,12384),(2047,0),12400),((1600,12354),(2047,0),4162),((2047,61440),(1932,22528),20480),((501,2096),(501,28672),0),((772,48),(2047,0),11794),((634,19472),(2045,30784),18432),((481,28736),(754,53376),20480),((2025,30800),(2028,22672),22528),((1023,52272),(2017,64593),1040),((1015,3120),(605,8384),0),((1141,15986),(2045,62480),1024),((518,48),(2047,0),1552)]

lemma box2_24ok : box2_24.all (boxAccept envelope2.2) = true := by decide +kernel

def box2_36 : List Box := [((904,22528),(2047,0),15440),((388,20528),(2047,0),14352),((1640,18448),(2047,28672),20496),((932,56337),(2047,30784),26624),((35,3),(2047,0),33282),((772,50177),(2047,33808),33794),((1474,12864),(2028,22544),4096),((2017,28738),(1568,52241),16384),((384,16512),(2047,20480),18496),((1986,12866),(1023,19504),0),((1898,16208),(1714,55440),2048),((1866,12800),(1640,19472),0)]

lemma box2_36ok : box2_36.all (boxAccept envelope2.2) = true := by decide +kernel

def box2_48 : List Box := [((1994,12864),(1798,35072),0),((1918,52240),(1248,12898),0),((1971,35856),(605,8384),0),((1830,36112),(605,8384),0),((481,28736),(1808,8710),8192),((304,3096),(1248,12898),0),((1586,34832),(1808,518),0),((1586,34832),(1728,12354),0),((1971,35856),(1552,774),0),((1441,33808),(1728,12354),0),((1830,36112),(1728,12354),0)]

lemma box2_48ok : box2_48.all (boxAccept envelope2.2) = true := by decide +kernel

def box3_0 : List Box := [((2047,21380),(2047,21380),21380),((2042,13124),(2047,21380),768),((631,524),(2047,21380),516),((1786,53376),(2047,21380),20480),((2047,0),(2047,0),49668),((853,1792),(2047,772),768),((2047,20608),(2047,49924),16384),((501,28800),(2047,772),20992),((1866,12864),(2047,20608),4608),((2047,53376),(853,34564),0),((2047,8964),(1449,16576),0),((433,33540),(2047,53376),33284)]

lemma box3_0ok : box3_0.all (boxAccept envelope3.2) = true := by decide +kernel

def box3_12 : List Box := [((501,33536),(2047,0),33280),((690,53376),(2047,0),36992),((2047,20608),(1296,8998),0),((964,22656),(2047,54148),20608),((501,33540),(1978,8964),768),((1533,29572),(1786,53376),20480),((2047,21380),(2000,21383),0),((1722,53248),(1870,50432),49152),((501,33540),(1866,12800),512),((631,524),(1866,12800),512),((1015,54144),(759,53900),32768),((1245,29572),(2010,13124),12800)]

lemma box3_12ok : box3_12.all (boxAccept envelope3.2) = true := by decide +kernel

def box3_24 : List Box := [((947,54148),(2047,29568),0),((1525,29348),(1791,53900),0),((213,28800),(2047,49920),16384),((1449,16576),(631,524),0),((1288,8704),(2047,0),4868),((690,53376),(2047,12800),20864),((501,28800),(1296,8998),8192),((433,33540),(1449,16576),0),((1296,8998),(1786,53376),0),((320,33024),(2047,0),17152),((754,53376),(1474,12864),4096),((320,33024),(2047,0),49664)]

lemma box3_24ok : box3_24.all (boxAccept envelope3.2) = true := by decide +kernel

def box3_36 : List Box := [((433,34564),(704,51329),32768),((1072,804),(2042,53632),256),((1269,29604),(860,50948),0),((1296,8998),(1449,16576),0),((1728,20609),(1978,8964),0),((2000,21383),(759,53900),0),((1808,518),(1722,53376),0),((1449,16576),(788,34564),0),((1328,804),(1866,12800),512),((704,55425),(1296,8998),0),((949,34564),(1728,20609),0),((213,28800),(1808,774),0)]

lemma box3_36ok : box3_36.all (boxAccept envelope3.2) = true := by decide +kernel

def box3_48 : List Box := [((1296,8998),(964,22656),0),((964,18560),(788,34564),0),((1474,12864),(1728,20609),0),((704,55425),(1808,774),0),((1296,8998),(1728,20609),0),((964,22656),(1808,774),0),((1728,20609),(1808,774),0)]

lemma box3_48ok : box3_48.all (boxAccept envelope3.2) = true := by decide +kernel

def box4_0 : List Box := [((2047,8998),(2047,8998),8738),((2047,8994),(2047,34572),512),((2047,53004),(2047,53004),256),((2047,3340),(2047,34060),1288),((1451,8739),(2047,10018),8738),((1934,8754),(2047,8994),8738),((2047,0),(2047,0),42026),((2047,0),(2047,0),59936),((2047,0),(2047,0),1290),((1898,12832),(2047,8738),25120),((2047,0),(2047,524),1546),((501,34572),(2047,1804),768)]

lemma box4_0ok : box4_0.all (boxAccept envelope4.2) = true := by decide +kernel

def box4_12 : List Box := [((1846,10022),(2047,42764),1792),((2047,0),(2047,0),33064),((2047,0),(2047,524),33320),((1015,36620),(2047,36108),33032),((2047,0),(2047,0),19200),((1449,8739),(2047,42764),512),((1846,9010),(2047,3328),42274),((1846,36120),(2047,52488),35072),((890,52488),(2047,8994),0),((950,55424),(2047,8738),0),((1932,8754),(2047,42764),512),((1608,12834),(2047,50956),512)]

lemma box4_12ok : box4_12.all (boxAccept envelope4.2) = true := by decide +kernel

def box4_24 : List Box := [((1971,34571),(2047,42794),0),((1932,22528),(2047,34060),0),((2047,12066),(1971,12067),0),((2047,8738),(1014,51328),0),((1846,34616),(2047,42794),34056),((1846,43826),(2047,43810),33024),((1640,12320),(2047,50444),0),((876,52240),(2047,8742),0),((1932,22528),(2047,8964),0),((2047,8994),(949,36104),0),((1760,8802),(2047,780),512),((1792,50441),(2047,34568),34059)]

lemma box4_24ok : box4_24.all (boxAccept envelope4.2) = true := by decide +kernel

def box4_36 : List Box := [((1298,42798),(2047,42766),42798),((1312,36120),(2047,35080),34104),((1640,12834),(2047,8998),8704),((1955,52489),(2047,3848),2816),((1896,52504),(2047,33804),33800),((1879,34572),(639,19980),1544),((861,50956),(1975,3340),1288),((566,816),(2047,0),42530),((257,3),(2047,33024),43553),((260,48),(2047,1280),11810),((289,3),(2047,0),43554),((433,34564),(1886,50440),33024)]

lemma box4_36ok : box4_36.all (boxAccept envelope4.2) = true := by decide +kernel

def box4_48 : List Box := [((1955,52481),(1722,8994),258),((1013,36620),(1451,8739),512),((1932,22528),(1021,53000),18432),((1015,34572),(1896,52504),1288),((2028,10288),(2047,52224),59424),((341,34568),(1846,35376),34304),((1527,36616),(1934,8754),512),((1953,42795),(1971,34571),257),((1449,8739),(1459,3876),0),((1916,50456),(1451,8739),0),((1451,12067),(1950,43780),256),((949,34564),(1932,22528),0)]

lemma box4_48ok : box4_48.all (boxAccept envelope4.2) = true := by decide +kernel

def box4_60 : List Box := [((1015,34572),(1640,12320),0),((1014,51328),(2047,52488),51200),((528,2049),(2047,0),3074),((1842,36120),(1932,8754),272),((1980,10288),(2047,35072),34848),((1976,42790),(1934,8754),544),((1019,19720),(1640,12834),0),((1846,36120),(1640,12834),0),((1934,8754),(1808,34057),0),((1798,560),(1443,33804),0),((1328,804),(2027,52492),260),((1944,8966),(1798,1036),4)]

lemma box4_60ok : box4_60.all (boxAccept envelope4.2) = true := by decide +kernel

def box4_72 : List Box := [((1443,515),(1525,34604),41506),((1449,8195),(1808,32777),1),((1918,52504),(1432,8998),0),((1932,8754),(788,36104),3600),((1464,8998),(1810,52489),33034),((1980,10022),(2018,8802),8704),((1586,19457),(1328,804),0)]

lemma box4_72ok : box4_72.all (boxAccept envelope4.2) = true := by decide +kernel

def box5_0 : List Box := [((2047,1264),(2047,3280),16),((2047,0),(2047,0),3280),((2047,0),(2047,0),240),((1314,3344),(2047,3312),3088),((501,2096),(2047,1264),48),((1441,33808),(2047,3280),1040),((1586,34832),(2047,3312),2064),((1312,36120),(2047,3312),1040),((631,1072),(2047,3120),1056),((117,3120),(2047,0),3104),((1798,560),(2047,3088),16),((501,2096),(2047,3120),2080)]

lemma box5_0ok : box5_0.all (boxAccept envelope5.2) = true := by decide +kernel

def box5_12 : List Box := [((117,3120),(2047,192),0),((964,22656),(2047,192),128),((2047,2288),(1798,35072),2048),((1328,548),(2047,3312),32),((1072,804),(2047,3312),1568),((2047,192),(1004,19600),3280),((1798,560),(2047,0),528),((1248,12384),(2047,192),64),((1248,8288),(2047,0),112),((631,1072),(844,50176),1024),((501,2096),(964,18560),2048),((1798,35072),(631,3120),2048)]

lemma box5_12ok : box5_12.all (boxAccept envelope5.2) = true := by decide +kernel

def box5_24 : List Box := [((964,22656),(631,1072),0),((48,2064),(2047,0),32816),((1441,33808),(1586,34832),32784),((33,1040),(2047,0),33824),((501,3120),(1328,3096),1040),((501,3120),(1248,12384),32),((631,3120),(805,50193),33840),((1015,3120),(1796,33793),1024),((1314,3344),(1328,1048),1044),((1312,36120),(1798,560),272),((544,19473),(844,50176),17408),((964,18560),(1586,34832),2048)]

lemma box5_24ok : box5_24.all (boxAccept envelope5.2) = true := by decide +kernel

def box5_36 : List Box := [((1314,3344),(1798,560),304),((616,19472),(1798,560),16),((1586,34832),(1798,560),16),((804,52241),(1824,35857),1041),((1568,3089),(1796,33793),1041),((1328,1048),(1798,560),16),((1328,548),(1586,34832),0),((1328,548),(1314,3344),0),((1328,548),(900,22656),0),((1328,548),(964,18560),0),((1586,34832),(1072,804),0),((1072,804),(964,18560),0)]

lemma box5_36ok : box5_36.all (boxAccept envelope5.2) = true := by decide +kernel

def box5_48 : List Box := [((1796,33793),(1798,560),0),((788,34824),(1798,560),0),((772,35080),(1798,560),0),((804,36120),(1248,8288),0)]

lemma box5_48ok : box5_48.all (boxAccept envelope5.2) = true := by decide +kernel

def box6_0 : List Box := [((2047,12),(2047,20620),20620),((501,28800),(2047,20620),20608),((2047,0),(2047,0),24736),((964,22656),(2047,20620),20608),((1932,22528),(2047,20608),20480),((1728,20609),(2047,21644),20608),((1019,52232),(2047,20608),16392),((840,50440),(2047,20620),16392),((1640,12384),(2047,20620),4096),((501,28672),(2047,0),24576),((213,28800),(2047,0),24704),((2047,12),(1018,53384),20616)]

lemma box6_0ok : box6_0.all (boxAccept envelope6.2) = true := by decide +kernel

def box6_12 : List Box := [((2047,22656),(1798,1036),0),((900,22656),(2047,0),6272),((2047,1036),(704,55425),0),((1798,1036),(2047,0),1028),((501,28672),(1932,8240),8192),((501,28800),(1996,22656),20480),((690,53376),(1932,22528),20480),((501,28672),(1640,12384),12288),((949,23688),(634,19456),19456),((964,22656),(1449,16576),16512),((964,18560),(1932,22528),18432),((213,28800),(1932,8240),8192)]

lemma box6_12ok : box6_12.all (boxAccept envelope6.2) = true := by decide +kernel

def box6_24 : List Box := [((213,28800),(1768,12384),12288),((1932,8240),(1932,22528),0),((48,516),(2047,0),44),((1640,12320),(1932,22656),4096),((213,28800),(1017,52232),16384),((754,53376),(1798,1036),0),((1932,8240),(964,22656),0),((1798,1036),(1449,16576),0),((433,3080),(704,55425),2048),((1019,19464),(1728,20609),16384),((1248,12384),(1998,23692),4096),((1248,12384),(433,3080),0)]

lemma box6_24ok : box6_24.all (boxAccept envelope6.2) = true := by decide +kernel

def box7_0 : List Box := [((2047,192),(2047,772),964),((2047,0),(2047,0),3588),((2047,0),(2047,0),35332),((433,33540),(2047,1988),772),((788,1796),(2047,964),772),((1498,9028),(2047,964),836),((1328,804),(2047,1796),772),((1808,774),(2047,964),772),((2047,192),(631,524),0),((1798,560),(2047,772),512),((2047,192),(1443,3328),0),((788,1796),(2047,0),1540)]

lemma box7_0ok : box7_0.all (boxAccept envelope7.2) = true := by decide +kernel

def box7_12 : List Box := [((2047,192),(1040,8998),0),((1072,804),(2047,0),292),((433,33540),(631,524),33284),((272,34564),(2047,192),0),((1328,548),(2047,0),36),((631,524),(788,1796),1540),((631,524),(1432,8964),516),((518,12),(2047,0),1540),((631,524),(1808,774),516),((35,12),(2047,0),33284),((631,524),(1328,548),516),((433,33540),(1808,518),516)]

lemma box7_12ok : box7_12.all (boxAccept envelope7.2) = true := by decide +kernel

def box7_24 : List Box := [((433,33540),(1798,560),512),((788,1796),(1474,12864),512)]

lemma box7_24ok : box7_24.all (boxAccept envelope7.2) = true := by decide +kernel

def box8_0 : List Box := [((2047,48),(2047,20656),20656),((2047,0),(2047,0),5264),((754,53376),(2047,20656),20608),((2047,0),(2047,0),49185),((2047,0),(2047,0),49200),((631,1072),(2047,53424),48),((605,16387),(2047,20608),16384),((2028,12400),(2047,28848),48),((2047,560),(501,28800),0),((2047,8240),(1449,16576),0),((2029,50192),(2047,20656),16),((1932,8240),(2047,0),8208)]

lemma box8_0ok : box8_0.all (boxAccept envelope8.2) = true := by decide +kernel

def box8_12 : List Box := [((2047,48),(996,55441),16432),((1328,548),(2047,28801),0),((1072,804),(2047,28801),0),((1640,12320),(2047,0),4144),((1664,20609),(2047,0),4225),((1957,50193),(2047,48),32784),((2047,48),(1728,20609),0),((501,28800),(631,1072),0),((631,1072),(1441,33808),1040),((213,28800),(1722,8960),8192),((840,52224),(2047,49152),21648),((1768,12384),(1722,53248),4096)]

lemma box8_12ok : box8_12.all (boxAccept envelope8.2) = true := by decide +kernel

def box8_24 : List Box := [((605,16387),(754,53376),16384),((1957,33809),(1722,53377),32768),((1544,8224),(2047,0),12304),((631,1072),(1768,12384),32),((996,56465),(1722,8960),0),((1474,12864),(1932,8240),8192),((96,12288),(2047,0),20512),((964,55425),(1898,12832),4096),((754,49280),(1957,33809),32768),((1441,33808),(1934,8752),16),((1866,12864),(1441,33808),0),((1957,33809),(213,28800),0)]

lemma box8_24ok : box8_24.all (boxAccept envelope8.2) = true := by decide +kernel

def box8_36 : List Box := [((1957,50193),(1449,16576),16384),((1749,28801),(876,52241),16384),((964,55425),(1441,33808),32768),((1640,12384),(1798,560),32),((1474,8768),(1441,33808),0),((1328,548),(1449,16576),0),((964,55425),(1432,8708),0),((1072,804),(1449,16576),0),((1640,12320),(616,19472),0),((1328,548),(704,55425),0),((704,55425),(1072,804),0)]

lemma box8_36ok : box8_36.all (boxAccept envelope8.2) = true := by decide +kernel

def box9_0 : List Box := [((2047,12),(2047,12352),12364),((501,28736),(2047,12364),12352),((1498,12868),(2047,12364),12356),((631,524),(2047,12364),12),((1728,12354),(2047,12364),12352),((2047,12),(1722,53248),0),((1248,8288),(2047,12352),8256),((1798,1036),(2047,12),12),((2047,12),(1866,12800),0),((1346,12864),(2047,0),4676),((1432,8964),(2047,12),4),((1443,32780),(2047,0),32772)]

lemma box9_0ok : box9_0.all (boxAccept envelope9.2) = true := by decide +kernel

def box9_12 : List Box := [((2047,12),(1088,12898),0),((631,524),(1798,1036),12),((1443,32780),(1722,53248),32768),((501,28736),(1443,32780),0),((631,524),(1474,8768),512),((605,8384),(1474,12864),8256),((631,524),(1346,12864),512),((1798,1036),(1722,53248),0),((1432,8964),(1443,32780),4),((605,8384),(1248,12384),8256),((481,28736),(1432,8708),8192),((1282,33804),(1722,53248),32768)]

lemma box9_12ok : box9_12.all (boxAccept envelope9.2) = true := by decide +kernel

def box9_24 : List Box := [((501,28672),(1808,518),0),((1798,1036),(605,8384),0),((1443,32780),(1216,12898),0),((1552,774),(1866,12864),512),((1176,8964),(1798,1036),4),((1798,1036),(1216,12898),0),((1120,12384),(1432,8708),8192),((1432,8708),(1600,12354),8192),((1808,518),(1088,12898),0),((1120,12384),(1808,518),0)]

lemma box9_24ok : box9_24.all (boxAccept envelope9.2) = true := by decide +kernel

def box10_0 : List Box := [((2047,20608),(2047,34056),0),((2047,0),(2047,0),5512),((634,19457),(2047,34056),1024),((272,34564),(2047,34056),34560),((690,55425),(2047,34056),32768),((2047,20608),(341,34568),0),((213,28800),(2047,34056),0),((704,51329),(2047,34056),32768),((2047,20608),(1443,32780),0),((1013,56712),(2047,54664),0),((929,52489),(2047,53376),49152),((562,19457),(2047,20608),16384)]

lemma box10_0ok : box10_0.all (boxAccept envelope10.2) = true := by decide +kernel

def box10_12 : List Box := [((784,51209),(2047,20608),16384),((1328,34072),(2047,53376),0),((2047,54664),(2000,54665),0),((2047,20608),(1282,33804),0),((512,49152),(2047,0),54664),((341,34568),(754,56449),33792),((213,28800),(853,34568),0),((1013,34568),(1449,16576),0),((929,56713),(1018,56713),19457),((213,28800),(634,19457),16384),((501,28672),(562,19457),16384),((501,28800),(784,52489),16384)]

lemma box10_12ok : box10_12.all (boxAccept envelope10.2) = true := by decide +kernel

def box10_24 : List Box := [((530,49152),(2047,0),37256),((501,33536),(704,51329),32768),((1328,34072),(501,28800),0),((501,28800),(1959,33804),0),((1808,34057),(501,28800),0),((704,55425),(1443,33804),32768),((690,53376),(1312,34072),32768),((634,19456),(1792,34057),1024),((288,3352),(501,28672),0),((501,28800),(949,36104),0),((853,1792),(964,18560),0),((1728,20609),(1013,34568),0)]

lemma box10_24ok : box10_24.all (boxAccept envelope10.2) = true := by decide +kernel

def box10_36 : List Box := [((964,22656),(1443,33804),0),((433,3336),(900,22656),2048),((1728,20609),(1866,50441),16384),((1728,20609),(1443,33804),0),((704,51328),(1312,34072),32768),((1728,20609),(768,51465),0),((1808,32777),(1728,20609),0),((1728,20609),(788,35080),0)]

lemma box10_36ok : box10_36.all (boxAccept envelope10.2) = true := by decide +kernel

def box11_0 : List Box := [((2047,8930),(2047,12898),8192),((2047,28896),(2047,29410),0),((2047,12352),(2047,20608),4096),((2047,16576),(2047,20608),16512),((1736,12898),(2047,29282),12834),((2047,0),(2047,0),17058),((501,28736),(2047,8930),8192),((2047,8738),(1722,53248),0),((2047,0),(2047,0),4226),((1586,8994),(2047,12354),8192),((481,28736),(2047,20608),20480),((213,28800),(2047,12352),12288)]

lemma box11_0ok : box11_0.all (boxAccept envelope11.2) = true := by decide +kernel

def box11_12 : List Box := [((213,28800),(2047,8738),8192),((1443,8739),(2047,13024),8192),((1474,12864),(2047,12834),8704),((1451,8739),(2047,29312),512),((2047,20672),(1586,8994),0),((1672,55297),(2047,12834),4098),((1932,22528),(2047,8738),0),((1021,28864),(2047,20672),16512),((1248,12384),(2047,12834),8224),((1640,12320),(2047,12352),12288),((1798,8754),(2047,12898),8192),((1608,12898),(2047,20608),4096)]

lemma box11_12ok : box11_12.all (boxAccept envelope11.2) = true := by decide +kernel

def box11_24 : List Box := [((1798,8754),(2047,28864),0),((754,53376),(2047,16576),16512),((1216,12898),(2047,24768),29410),((1640,18448),(2047,20608),16384),((1296,8742),(2047,13026),8704),((1451,8739),(1736,12898),25122),((634,19456),(2047,16576),16384),((1728,20609),(2047,29346),20610),((1449,8739),(1932,8240),8224),((1527,29408),(1451,8739),8192),((501,28736),(1586,8994),8192),((1451,8739),(1786,53376),0)]

lemma box11_24ok : box11_24.all (boxAccept envelope11.2) = true := by decide +kernel

def box11_36 : List Box := [((733,28864),(1586,8994),8192),((1443,8739),(1736,55425),4097),((501,28736),(1932,8754),8192),((840,50440),(1586,8994),256),((1505,28768),(1449,16576),16448),((1451,8739),(1798,8754),546),((1506,12898),(1722,8994),8704),((1449,8739),(840,50440),0),((1443,8739),(1449,16576),0),((1934,8754),(1722,53248),0),((1661,12512),(754,53376),128),((213,28800),(1796,8754),8192)]

lemma box11_36ok : box11_36.all (boxAccept envelope11.2) = true := by decide +kernel

def box11_48 : List Box := [((605,8384),(1796,8754),8192),((481,28736),(1640,12320),12288),((1451,8739),(964,22656),0),((754,53376),(1934,8754),0),((1934,8754),(1672,55297),0),((1722,8994),(876,52240),0),((605,8384),(964,22656),128),((576,8256),(2047,0),8322),((1248,8288),(1934,8754),8224),((704,55425),(1934,8754),0),((1798,8754),(964,22656),0),((1934,8754),(1728,20609),0)]

lemma box11_48ok : box11_48.all (boxAccept envelope11.2) = true := by decide +kernel

def box11_60 : List Box := [((1640,18448),(1640,12320),0),((1728,20609),(1248,12898),0)]

lemma box11_60ok : box11_60.all (boxAccept envelope11.2) = true := by decide +kernel

def box12_0 : List Box := [((2047,52233),(2047,52233),51201),((895,51203),(2047,51201),51201),((2047,1548),(2047,52225),0),((2027,52493),(2047,52233),51201),((2047,0),(2047,0),18949),((1982,55296),(2047,51201),51200),((2047,0),(2047,0),2061),((964,18560),(2047,51201),18432),((2025,52241),(2047,52237),18432),((1866,12800),(2047,51201),0),((2047,36364),(605,51203),32768),((2047,33292),(631,32771),32768)]

lemma box12_0ok : box12_0.all (boxAccept envelope12.2) = true := by decide +kernel

def box12_12 : List Box := [((1474,8768),(2047,51201),0),((2047,52233),(1176,8964),0),((2047,51209),(1640,12320),0),((2047,51201),(1432,8708),0),((2047,51201),(1346,12864),0),((2047,51201),(1798,560),0),((895,51203),(1914,52493),51201),((895,51203),(1982,55297),51201),((2047,34316),(1866,51457),32768),((2047,19981),(1672,55297),18432),((2047,524),(853,2051),0),((1120,12384),(2047,51213),0)]

lemma box12_12ok : box12_12.all (boxAccept envelope12.2) = true := by decide +kernel

def box12_24 : List Box := [((1328,548),(2047,51201),0),((2047,51201),(1072,804),0),((2047,51213),(1248,8288),0),((818,52489),(2047,52749),52233),((1955,34061),(2047,1548),12),((949,35848),(2047,0),2056),((1328,804),(2047,1036),4),((1808,32777),(2047,3596),13),((887,1548),(856,50440),2060),((33,3),(2047,0),41505),((1672,55297),(1978,8964),0),((35,3),(2047,0),33281)]

lemma box12_24ok : box12_24.all (boxAccept envelope12.2) = true := by decide +kernel

def box12_36 : List Box := [((895,51203),(1988,51329),16385),((1884,52233),(1722,55297),49152),((895,51203),(1924,55425),16385),((1911,1548),(1798,560),512),((1866,12800),(1658,19457),0),((1866,12800),(1794,51457),0),((895,51203),(1640,12320),0),((1280,33032),(2047,32776),32773),((1868,50177),(1568,51217),49169),((1474,8768),(1794,51457),0),((1474,8768),(1672,55297),0),((895,51203),(1248,8288),0)]

lemma box12_36ok : box12_36.all (boxAccept envelope12.2) = true := by decide +kernel

def box12_48 : List Box := [((1794,51457),(1640,12320),0),((1794,51457),(1346,12864),0),((1586,3073),(1798,1596),1024),((1640,52241),(1798,1596),1040),((1586,19457),(1474,8768),0),((1846,35841),(1640,12320),0),((1568,51217),(1640,12320),0),((1248,8288),(1955,36109),0),((1842,52489),(1248,8288),0)]

lemma box12_48ok : box12_48.all (boxAccept envelope12.2) = true := by decide +kernel

def box13_0 : List Box := [((2047,55425),(2047,51393),16384),((2047,55425),(2047,30912),0),((1736,55425),(2047,63617),55297),((2047,8384),(2047,12352),8256),((2047,0),(2047,0),43073),((754,53376),(2047,55297),49152),((501,28800),(2047,51201),16384),((2047,0),(2047,0),4161),((481,28736),(2047,51201),16384),((887,51203),(2047,55489),16384),((895,51203),(2047,28736),0),((2047,55297),(1608,12834),4096)]

lemma box13_0ok : box13_0.all (boxAccept envelope13.2) = true := by decide +kernel

def box13_12 : List Box := [((1932,8240),(2047,12352),8192),((1513,28864),(2047,12480),8256),((1672,55425),(2047,12352),4096),((1794,51457),(2047,63617),49152),((2047,51201),(1216,8802),0),((2047,55297),(1088,12898),4163),((1794,51457),(2047,12480),0),((2047,12352),(1443,3328),0),((704,55425),(2047,24768),63681),((1568,51217),(2047,55425),18432),((1586,19457),(2047,55489),0),((1586,3073),(2047,12480),0)]

lemma box13_12ok : box13_12.all (boxAccept envelope13.2) = true := by decide +kernel

def box13_24 : List Box := [((2047,63553),(1728,12354),12353),((1828,52241),(2047,55489),0),((1023,63555),(895,51203),16384),((1,3),(2047,28672),59939),((895,51203),(1608,12898),4099),((856,51209),(1786,53377),49152),((861,51203),(1640,18448),18432),((1994,12864),(895,51203),0),((887,51203),(733,28864),0),((1443,3328),(1722,53248),0),((1443,3328),(1932,55297),2048),((1866,12800),(1932,22528),4096)]

lemma box13_24ok : box13_24.all (boxAccept envelope13.2) = true := by decide +kernel

def box13_36 : List Box := [((1513,28864),(1794,51457),16384),((501,28800),(1568,51217),16384),((887,51203),(1728,8802),2),((1586,3073),(501,28864),0),((1866,12864),(1443,3328),0),((1658,19457),(1608,12834),0),((481,28736),(1443,3328),0),((1794,51457),(1736,12898),0),((1736,12898),(1443,3328),0),((1736,12898),(1014,55425),4096),((1443,3328),(1757,59585),2048),((1749,63617),(1640,18448),18432)]

lemma box13_36ok : box13_36.all (boxAccept envelope13.2) = true := by decide +kernel

def box13_48 : List Box := [((1152,16512),(2047,0),16449),((1474,8768),(1443,3328),0),((1640,52241),(1608,12834),0),((1828,52241),(733,28864),0),((1736,12898),(856,51209),0),((1932,56321),(1728,12898),0),((1586,19457),(1728,12898),0),((1930,55553),(1248,8288),0),((1608,12834),(1796,33793),0),((64,12352),(605,51203),20482)]

lemma box13_48ok : box13_48.all (boxAccept envelope13.2) = true := by decide +kernel

def box14_0 : List Box := [((2047,51715),(2047,8739),0),((2047,16387),(2047,8738),2),((2047,8195),(2047,51201),1),((1957,52241),(2047,51203),51201),((1443,8739),(2047,51201),1),((887,51203),(2047,8738),2),((2047,51203),(1722,8994),0),((1441,8739),(2047,0),8737),((597,51203),(2047,0),51202),((1655,52227),(2047,2051),3),((1443,8739),(2047,16387),3),((1866,51457),(2047,8739),0)]

lemma box14_0ok : box14_0.all (boxAccept envelope14.2) = true := by decide +kernel

def box14_12 : List Box := [((2029,59955),(2047,59939),0),((1586,8994),(2047,51203),32770),((853,2051),(2047,8195),3),((704,51329),(2047,8738),0),((1957,33809),(2047,8739),1),((562,19457),(2047,8739),1),((2047,59395),(1296,8742),2),((640,55425),(2047,25123),59393),((784,51209),(2047,8739),1),((929,52489),(2047,59939),2049),((1449,8739),(1796,8754),10786),((631,32771),(2047,0),32770)]

lemma box14_12ok : box14_12.all (boxAccept envelope14.2) = true := by decide +kernel

def box14_24 : List Box := [((1569,52241),(2047,3),51249),((804,52241),(2047,8739),33),((2047,16387),(1443,3328),0),((1443,515),(2047,0),513),((853,2099),(2047,51203),2050),((1449,8195),(2047,0),8193),((887,51203),(1957,8755),3),((605,16387),(2047,0),16386),((876,52240),(2047,35331),0),((1965,8755),(1898,12834),8736),((1586,8994),(1866,12800),8704),((631,51203),(1443,515),3)]

lemma box14_24ok : box14_24.all (boxAccept envelope14.2) = true := by decide +kernel

def box14_36 : List Box := [((1655,52227),(1449,8195),3),((1586,8994),(1982,55297),0),((1586,8994),(1866,51457),257),((853,2051),(1443,515),3),((1451,8739),(1794,51457),259),((1858,12866),(1722,8994),8704),((1658,19457),(1443,8739),1),((1451,8739),(1932,22528),0),((1974,55425),(1586,8994),0),((1586,8994),(2038,51329),0),((1451,8739),(1808,8742),514),((1451,8739),(1552,8998),514)]

lemma box14_36ok : box14_36.all (boxAccept envelope14.2) = true := by decide +kernel

def box14_48 : List Box := [((929,52489),(1586,8994),769),((1586,8994),(1792,34057),256),((1866,51457),(1934,8754),0),((840,52489),(1934,8754),0),((1798,8754),(1932,22528),0),((562,19457),(1586,8994),0),((1640,51217),(1722,8994),0),((1586,8994),(784,51209),0),((532,34817),(2047,2049),1027),((1965,42033),(1796,42547),16),((2028,59441),(1828,59955),17),((1934,8754),(856,51209),0)]

lemma box14_48ok : box14_48.all (boxAccept envelope14.2) = true := by decide +kernel

def box14_60 : List Box := [((1934,8754),(844,50177),0),((1640,12834),(1792,52489),0),((1722,8994),(1796,33793),0),((256,34056),(1443,8739),51713),((1957,33809),(1976,8742),0),((1608,12834),(1808,32777),0)]

lemma box14_60ok : box14_60.all (boxAccept envelope14.2) = true := by decide +kernel

def box15_0 : List Box := [((2047,12),(2047,192),204),((1757,8386),(2047,204),192),((1449,8195),(2047,192),0),((2047,12),(1449,16576),0),((1728,12354),(2047,192),194),((1552,774),(2047,12),4),((1808,518),(2047,12),6),((605,8384),(1449,16576),192),((605,8384),(1449,8195),8192),((1443,32780),(1449,16576),0),((1443,32780),(605,8384),0),((528,516),(2047,0),14)]

lemma box15_0ok : box15_0.all (boxAccept envelope15.2) = true := by decide +kernel

def box15_12 : List Box := [((1449,16576),(1728,12354),64),((1451,49356),(1552,774),4),((1451,49356),(1808,518),4),((1808,518),(605,8384),0),((1552,774),(605,8384),0)]

lemma box15_12ok : box15_12.all (boxAccept envelope15.2) = true := by decide +kernel

def box16_0 : List Box := [((2047,3),(2047,195),195),((2047,3),(631,1072),0),((2047,192),(605,16387),0),((631,32771),(631,1072),0),((1152,8194),(2047,0),67),((576,16385),(2047,0),131)]

lemma box16_0ok : box16_0.all (boxAccept envelope16.2) = true := by decide +kernel

def box17_0 : List Box := [((2047,12),(2047,48),60),((2047,12),(2047,3),15),((2047,48),(2047,3),0),((2047,0),(2047,0),276),((2047,0),(2047,0),261),((605,16387),(2047,3),3),((1449,8195),(2047,3),3),((1798,8754),(2047,8240),48),((117,3120),(2047,48),48),((1798,8754),(2047,3),2),((2047,12),(117,3120),0),((117,3120),(2047,3),0)]

lemma box17_0ok : box17_0.all (boxAccept envelope17.2) = true := by decide +kernel

def box17_12 : List Box := [((2047,12),(1798,560),0),((501,2096),(1932,8240),48),((501,2096),(1798,8754),48),((631,1072),(1798,8754),48),((631,1072),(1932,8240),48),((117,3120),(1932,8240),48),((117,3120),(1798,8754),48),((605,16387),(1449,8195),3),((1538,544),(2047,0),304),((1058,514),(2047,0),259),((501,2096),(1640,12320),32),((631,1072),(1296,8998),288)]

lemma box17_12ok : box17_12.all (boxAccept envelope17.2) = true := by decide +kernel

def box17_24 : List Box := [((605,16387),(1798,8754),2),((1280,544),(2047,0),308),((514,32769),(2047,0),259),((528,32769),(2047,0),11),((34,1040),(2047,0),304),((1280,514),(2047,0),7),((117,3120),(1296,8998),288),((512,51201),(1796,8754),19),((34,3088),(1536,8738),304),((32,3088),(1280,8738),49),((516,48),(528,2049),3090)]

lemma box17_24ok : box17_24.all (boxAccept envelope17.2) = true := by decide +kernel

def box18_0 : List Box := [((2047,0),(2047,0),2076),((2047,0),(2047,0),32824),((1443,32780),(2047,12),12),((2047,12),(501,2096),0),((2047,48),(1722,53248),0),((2047,48),(1658,19472),16),((2047,48),(1866,49408),0),((2047,48),(856,50440),0),((2047,48),(1932,22528),0),((2047,48),(1443,32780),0),((1296,8742),(2047,48),32),((2047,12),(1586,34832),0)]

lemma box18_0ok : box18_0.all (boxAccept envelope18.2) = true := by decide +kernel

def box18_12 : List Box := [((1586,34832),(2047,0),32784),((816,35864),(2047,0),2076),((2047,48),(788,34824),32792),((1882,49416),(501,2096),0),((501,2096),(1443,32780),0),((1538,34816),(2047,0),2320),((856,49160),(1443,32780),32776),((1538,34816),(2047,0),33040),((690,53376),(1443,32780),32768),((501,2096),(900,22656),2048),((501,2096),(844,50176),0),((1296,8742),(1722,53248),0)]

lemma box18_12ok : box18_12.all (boxAccept envelope18.2) = true := by decide +kernel

def box18_24 : List Box := [((1640,19472),(1932,8240),16),((304,3352),(634,19472),3072),((48,1040),(2047,0),56),((860,50440),(900,22656),16384),((1658,19472),(1296,8742),0),((1866,49408),(1296,8742),0),((900,22656),(1443,32780),0),((304,3352),(1586,34832),2328),((304,3096),(1932,22528),2048),((690,53376),(304,3352),0),((1296,8742),(900,22656),0)]

lemma box18_24ok : box18_24.all (boxAccept envelope18.2) = true := by decide +kernel

def box19_0 : List Box := [((2047,772),(2047,12352),0),((2047,0),(2047,0),4420),((433,33540),(2047,12352),0),((481,28736),(2047,772),0),((2047,772),(605,8384),0),((1104,13158),(2047,13124),13124),((2047,12352),(788,1796),0),((1176,8964),(2047,0),12612),((272,34564),(2047,12864),512),((1328,804),(2047,12352),0),((2047,772),(1600,12354),0),((501,28736),(631,524),0)]

lemma box19_0ok : box19_0.all (boxAccept envelope19.2) = true := by decide +kernel

def box19_12 : List Box := [((605,8384),(631,524),0),((631,524),(1088,12898),512),((501,28736),(1040,8998),8192),((433,33540),(481,28736),0),((433,33540),(605,8384),0),((501,28736),(788,1796),0),((433,33540),(1474,12898),512),((788,1796),(1866,12866),512),((1216,8802),(1432,8998),8704),((605,8384),(1040,8998),8192),((272,34564),(501,28736),0),((481,28736),(1296,8742),0)]

lemma box19_12ok : box19_12.all (boxAccept envelope19.2) = true := by decide +kernel

def box19_24 : List Box := [((501,28736),(1552,774),0),((1600,12354),(631,524),0),((605,8384),(788,1796),0),((1808,774),(1866,12866),512),((1298,34572),(605,8384),0),((1328,804),(481,28736),0),((1328,804),(605,8384),0),((433,33540),(1248,8288),0),((433,33540),(1728,12354),0),((1040,8998),(1088,12898),0),((1216,12898),(788,1796),0),((1298,34572),(1216,12898),0)]

lemma box19_24ok : box19_24.all (boxAccept envelope19.2) = true := by decide +kernel

def box19_36 : List Box := [((1392,13156),(1104,13158),0),((1104,13158),(1616,13126),0),((272,34564),(1248,8288),0),((272,34564),(1728,12354),0),((1392,13156),(1616,13126),0)]

lemma box19_36ok : box19_36.all (boxAccept envelope19.2) = true := by decide +kernel

def box20_0 : List Box := [((2047,52225),(2047,36612),0),((690,53376),(2047,51201),49152),((501,33536),(2047,51201),32768),((433,34564),(2047,52225),32768),((1798,35072),(2047,51201),34816),((895,51203),(2047,35588),0),((1443,32780),(2047,1796),4),((1810,53005),(2047,34564),772),((1810,51975),(2047,51457),18689),((2047,52481),(1040,8998),256),((1672,55297),(2047,1796),0),((784,53005),(2047,52481),53005)]

lemma box20_0ok : box20_0.all (boxAccept envelope20.2) = true := by decide +kernel

def box20_12 : List Box := [((704,51329),(2047,1796),0),((1640,51217),(2047,772),0),((640,55425),(2047,52996),51200),((804,52241),(2047,52997),3072),((2047,772),(1568,3089),0),((1552,774),(2047,33540),775),((1586,3073),(2047,50945),1281),((1982,55296),(631,524),0),((1796,33793),(2047,19712),1025),((631,51203),(1879,36612),34816),((690,55425),(1882,53005),49152),((497,33540),(631,51203),49664)]

lemma box20_12ok : box20_12.all (boxAccept envelope20.2) = true := by decide +kernel

def box20_24 : List Box := [((818,53005),(1982,55297),51200),((1586,3073),(2047,51457),2305),((895,51203),(1552,8998),258),((1459,36620),(1672,55297),34816),((639,49155),(861,50948),32768),((964,51329),(631,19981),18432),((895,51203),(1432,8964),0),((900,55425),(631,19981),18432),((853,1792),(853,2051),0),((257,1280),(2047,0),3584),((562,19457),(2047,52997),19713),((861,51203),(1808,774),32770)]

lemma box20_24ok : box20_24.all (boxAccept envelope20.2) = true := by decide +kernel

def box20_36 : List Box := [((853,1796),(1798,560),512),((1658,19457),(1432,8708),0),((1328,804),(895,51203),0),((1019,52489),(1808,8998),773),((1794,51457),(1296,8742),0),((1794,51457),(1432,8708),0),((1296,8998),(1932,55297),0),((1808,8998),(1443,3328),256),((1808,774),(1982,55297),0),((1877,2823),(860,50949),0),((788,1796),(1586,3073),1024),((1586,3073),(1296,8742),0)]

lemma box20_36ok : box20_36.all (boxAccept envelope20.2) = true := by decide +kernel

def box20_48 : List Box := [((1586,19457),(1346,12864),0),((1019,52232),(1328,804),0),((1328,804),(1932,55297),0),((518,48),(853,34564),3584),((1586,3073),(1808,774),0),((1640,52241),(1808,774),0)]

lemma box20_48ok : box20_48.all (boxAccept envelope20.2) = true := by decide +kernel

def box21_0 : List Box := [((2047,3),(2047,3088),0),((2047,0),(2047,0),1035),((1443,3344),(2047,3096),3072),((853,1792),(2047,3088),1024),((929,52489),(2047,3344),3072),((433,3080),(2047,3088),3072),((1586,19457),(2047,3088),3072),((1796,8754),(2047,0),8722),((501,2096),(2047,3),0),((1328,1048),(2047,3088),1040),((890,19736),(2047,3),0),((1314,3344),(2047,0),2320)]

lemma box21_0ok : box21_0.all (boxAccept envelope21.2) = true := by decide +kernel

def box21_12 : List Box := [((1312,34072),(2047,3),0),((1586,34832),(2047,3075),0),((1314,3344),(2047,3),0),((2047,3075),(1328,1048),1024),((1015,3120),(1443,3328),3072),((631,3120),(853,1792),1024),((1658,19472),(1443,3344),3072),((1328,1048),(2047,0),24),((501,3120),(853,2051),2048),((853,2051),(631,1072),0),((853,2051),(1443,3344),2048),((1586,52241),(1443,3344),3088)]

lemma box21_12ok : box21_12.all (boxAccept envelope21.2) = true := by decide +kernel

def box21_24 : List Box := [((1015,3120),(1586,19457),3072),((1449,8195),(634,19472),0),((634,19473),(1796,8754),16),((433,3336),(616,19472),3072),((616,19472),(853,2051),2048),((1441,34072),(1586,52241),33808),((433,3096),(1586,52241),3072),((1449,8195),(1792,34057),1),((1586,3073),(1796,8754),0),((933,36120),(1586,52241),3072),((772,35080),(605,16387),0),((1328,1048),(1586,51217),24)]

lemma box21_24ok : box21_24.all (boxAccept envelope21.2) = true := by decide +kernel

def box21_36 : List Box := [((1314,3344),(1538,34816),2320),((616,19473),(1796,33793),1025),((1441,36120),(1728,16513),0),((1441,36120),(1664,20609),0),((1330,3352),(1664,20609),0),((1328,3096),(1728,16513),0)]

lemma box21_36ok : box21_36.all (boxAccept envelope21.2) = true := by decide +kernel

def box22_0 : List Box := [((2047,772),(2047,3088),0),((2047,12),(2047,772),4),((2047,0),(2047,0),2580),((1015,3120),(2047,1796),0),((2047,3088),(631,524),0),((2047,3088),(501,33540),0),((820,36636),(2047,3860),3344),((2047,524),(631,1072),0),((1798,1036),(2047,772),4),((1330,36120),(2047,780),256),((433,33540),(2047,12),4),((1971,36112),(2047,3860),0)]

lemma box22_0ok : box22_0.all (boxAccept envelope22.2) = true := by decide +kernel

def box22_12 : List Box := [((1176,8964),(2047,3088),0),((2047,772),(616,19472),0),((1040,8998),(2047,3344),256),((788,1796),(2047,12),4),((1072,804),(2047,524),516),((501,3120),(631,524),0),((501,2096),(501,33536),0),((1015,3120),(1457,34580),16),((1141,3892),(1527,33548),4),((1794,51457),(631,3120),2048),((260,34056),(2047,1280),3860),((1586,34832),(1798,52481),34816)]

lemma box22_12ok : box22_12.all (boxAccept envelope22.2) = true := by decide +kernel

def box22_24 : List Box := [((501,2096),(1798,1036),0),((1971,35856),(631,524),0),((1568,52241),(631,524),0),((1176,8964),(631,3120),0),((433,34564),(1568,52241),32768),((304,3096),(631,524),8),((433,33540),(1798,1036),4),((1459,33548),(1846,36120),32768),((260,33024),(2047,0),35328),((1176,8964),(1798,51457),256),((1457,34580),(1443,36112),256),((1808,774),(631,3120),0)]

lemma box22_24ok : box22_24.all (boxAccept envelope22.2) = true := by decide +kernel

def box22_36 : List Box := [((35,3),(501,33536),33280),((1176,8964),(1314,3344),256),((1328,804),(1798,51457),256),((1441,33808),(1176,8964),0),((1441,33808),(1040,8998),0),((1568,51217),(1328,8998),0),((1568,52241),(1432,8964),0),((1568,52241),(788,1796),1024),((1330,36120),(1552,774),256),((804,52241),(1328,8998),0),((772,50177),(1432,8708),0),((1328,804),(1640,19472),0)]

lemma box22_36ok : box22_36.all (boxAccept envelope22.2) = true := by decide +kernel

def box22_48 : List Box := [((1296,8998),(1568,3089),0),((304,3352),(1328,804),788),((1328,804),(1568,3089),0),((788,35080),(1808,774),0)]

lemma box22_48ok : box22_48.all (boxAccept envelope22.2) = true := by decide +kernel

def box23_0 : List Box := [((2047,3088),(2047,51201),2048),((2047,34864),(2047,51217),0),((1015,3120),(2047,51201),2048),((605,51203),(2047,19472),2048),((872,52505),(2047,52241),18432),((900,22656),(2047,51201),18432),((1586,34832),(2047,51201),34816),((887,34819),(2047,3088),2048),((1932,8240),(2047,3088),16),((1870,51457),(2047,19472),2048),((1672,55297),(2047,3120),2048),((1314,3344),(2047,51201),2048)]

lemma box23_0ok : box23_0.all (boxAccept envelope23.2) = true := by decide +kernel

def box23_12 : List Box := [((2047,34864),(895,51203),0),((1728,51329),(2047,35856),2048),((784,51209),(2047,3088),2048),((304,3096),(2047,51217),2048),((2047,2096),(1794,51457),2048),((1640,12320),(2047,3088),0),((1568,52241),(2047,3120),2064),((2047,34864),(1586,19457),0),((2047,48),(1792,34057),0),((1015,3120),(605,51203),2048),((2047,48),(1808,32777),0),((639,51203),(1443,3344),2048)]

lemma box23_12ok : box23_12.all (boxAccept envelope23.2) = true := by decide +kernel

def box23_24 : List Box := [((887,51203),(1586,34832),34816),((631,32771),(117,3120),32800),((1898,52497),(1932,55297),18432),((887,51203),(1798,560),0),((853,2051),(1798,35072),2048),((1586,35857),(1932,55297),2048),((117,3120),(1640,12320),32),((788,51209),(1586,51217),34816),((1441,36120),(1672,55297),34816),((772,52489),(1653,51219),51201),((1586,3073),(1932,8240),0),((634,19457),(1798,560),0)]

lemma box23_24ok : box23_24.all (boxAccept envelope23.2) = true := by decide +kernel

def box23_36 : List Box := [((1120,12384),(895,51203),0),((562,19473),(1932,8240),16),((1640,12320),(1443,3328),0),((1988,51329),(1830,36112),2048),((1957,36121),(1640,19472),2064),((784,51209),(1314,3344),2048),((964,18560),(1586,3089),2048),((1840,3097),(1798,51457),2048),((1120,12384),(1959,52497),0),((562,19473),(1640,12320),0),((304,3096),(1672,55296),2048),((1586,19457),(1120,12384),0)]

lemma box23_36ok : box23_36.all (boxAccept envelope23.2) = true := by decide +kernel

def box23_48 : List Box := [((1798,35072),(1664,20609),0),((257,3),(388,20480),10240),((1,3),(112,2064),51232)]

lemma box23_48ok : box23_48.all (boxAccept envelope23.2) = true := by decide +kernel

def box24_0 : List Box := [((2047,34056),(2047,51201),32768),((1810,52489),(2047,52488),33024),((605,51203),(2047,50440),32768),((887,34819),(2047,34056),32768),((341,34568),(2047,51201),32768),((1441,33808),(2047,34056),33792),((1672,55297),(2047,36104),32768),((804,52241),(2047,50440),33792),((1796,33793),(2047,34056),33792),((1640,51217),(2047,50440),32768),((772,35080),(2047,51201),34816),((1328,34072),(2047,51201),32768)]

lemma box24_0ok : box24_0.all (boxAccept envelope24.2) = true := by decide +kernel

def box24_12 : List Box := [((1013,34568),(631,32771),32768),((501,34568),(1814,52489),33024),((501,34568),(861,51203),32768),((1866,50441),(1672,55297),49152),((341,34568),(1014,51328),32768),((1013,34568),(1441,33808),33792),((501,34568),(1672,55297),32768),((341,34568),(1932,22528),0),((1013,34568),(1568,51217),32768),((1722,53248),(1830,36121),32768),((856,50440),(1971,36121),33792),((1971,52505),(1824,36121),34057)]

lemma box24_12ok : box24_12.all (boxAccept envelope24.2) = true := by decide +kernel

def box24_24 : List Box := [((704,51329),(1886,52489),49152),((433,3352),(861,51203),2048),((895,51203),(1328,34072),32768),((853,34568),(1796,33793),33794),((929,52505),(1586,35857),35840),((1568,51217),(1798,51457),34816),((1971,36121),(1914,52505),32768),((844,50176),(1441,34072),33792),((1443,33804),(1568,51217),32768),((1840,36121),(1982,55297),0),((1441,33808),(1932,22528),0),((1842,52505),(1014,51329),0)]

lemma box24_24ok : box24_24.all (boxAccept envelope24.2) = true := by decide +kernel

def box24_36 : List Box := [((690,55425),(788,35080),32768),((640,55425),(1971,36120),34816),((900,22656),(1842,52505),2048),((1298,34572),(1842,52505),33800),((704,51329),(1808,518),0),((1314,3352),(1808,518),0),((900,22656),(1808,518),0),((33,3),(176,20480),40960),((160,16512),(160,20480),49216)]

lemma box24_36ok : box24_36.all (boxAccept envelope24.2) = true := by decide +kernel

def box25_0 : List Box := [((2047,8754),(2047,3632),0),((2047,48),(2047,8738),32),((501,2096),(2047,8738),32),((631,1072),(2047,8738),32),((117,3120),(2047,11826),32),((1451,8739),(2047,3120),0),((1722,8994),(2047,3120),0),((1828,11827),(2047,11826),3088),((1828,52241),(2047,3088),3088),((1441,8739),(2047,1072),32),((1586,8994),(2047,2096),32),((1314,3344),(2047,8738),0)]

lemma box25_0ok : box25_0.all (boxAccept envelope25.2) = true := by decide +kernel

def box25_12 : List Box := [((1608,12834),(2047,3088),0),((1866,12834),(2047,48),32),((304,3096),(2047,8738),0),((288,36120),(2047,8754),1808),((1432,8742),(2047,11312),0),((2047,3088),(1216,8802),0),((2047,11312),(1088,12898),8224),((1474,8802),(2047,48),32),((1572,35857),(2047,0),1043),((501,3120),(1441,8739),10272),((631,3120),(1586,8994),9762),((501,2096),(1608,12834),32)]

lemma box25_12ok : box25_12.all (boxAccept envelope25.2) = true := by decide +kernel

def box25_24 : List Box := [((631,3120),(1608,12834),32),((1216,8802),(2047,9264),8224),((1314,3344),(1722,8994),256),((1455,8755),(1568,52241),2067),((501,3120),(1216,8802),32),((1451,8739),(1586,34832),0),((1451,8739),(1314,3344),0),((1441,8739),(616,19472),0),((1441,33808),(1722,8994),0),((1072,804),(1830,12082),1824),((1120,12384),(1932,8754),8224),((804,36120),(1586,8994),256)]

lemma box25_24ok : box25_24.all (boxAccept envelope25.2) = true := by decide +kernel

def box25_36 : List Box := [((1296,8742),(1798,560),544),((804,52241),(1586,8994),0),((1312,34072),(1640,12834),0),((1451,8739),(304,3096),0),((1451,8739),(288,3352),0),((304,3096),(1586,8994),0),((1441,33808),(1640,12834),0),((1722,8994),(1568,3089),0),((772,50177),(1640,12834),0),((1474,8802),(1586,34832),0),((1441,33808),(1248,8802),0),((1314,3344),(1248,8802),0)]

lemma box25_36ok : box25_36.all (boxAccept envelope25.2) = true := by decide +kernel

def box25_48 : List Box := [((1314,3344),(1088,12898),0),((1828,52241),(1248,8802),0),((1568,52241),(1088,12898),0),((1798,35072),(1248,8802),0),((1798,35072),(1088,12898),0),((34,3088),(1586,8994),1312),((1640,12320),(1568,3089),0)]

lemma box25_48ok : box25_48.all (boxAccept envelope25.2) = true := by decide +kernel

def box26_0 : List Box := [((2047,3088),(2047,34056),1024),((2047,48),(2047,34056),0),((1015,3120),(2047,34056),1024),((1314,3344),(2047,34056),1280),((341,34568),(2047,3096),1024),((1586,3089),(2047,34056),1024),((634,19472),(2047,34072),1024),((860,50440),(2047,3352),1024),((2047,1072),(1013,34568),0),((2047,3088),(1959,33804),1024),((1812,34057),(2047,3096),1024),((2047,33840),(1459,3352),0)]

lemma box26_0ok : box26_0.all (boxAccept envelope26.2) = true := by decide +kernel

def box26_12 : List Box := [((2047,1072),(1798,1036),1024),((2047,33848),(818,52489),33792),((2047,1072),(788,1796),1024),((1328,3096),(2047,1072),1040),((341,34568),(1015,3120),1024),((2047,1072),(1298,34572),1024),((2047,1080),(788,35080),8),((1013,34568),(1314,3344),1280),((1443,33804),(1015,3120),1024),((433,3336),(1015,3120),1024),((341,34568),(1586,3089),1024),((1015,3120),(1808,34057),1024)]

lemma box26_12ok : box26_12.all (boxAccept envelope26.2) = true := by decide +kernel

def box26_24 : List Box := [((501,3384),(788,52489),3336),((856,49160),(631,3120),0),((853,34568),(900,22656),0),((48,1808),(2047,1040),33832),((788,1796),(1798,1036),1028),((117,3120),(788,1796),1024),((1525,35888),(1798,1036),1024),((35,12),(501,34568),33288),((853,34568),(544,19473),1024),((1568,3089),(1013,34560),1024),((900,22656),(1846,36120),2048),((788,1796),(1457,33816),1024)]

lemma box26_24ok : box26_24.all (boxAccept envelope26.2) = true := by decide +kernel

def box26_36 : List Box := [((1441,33808),(1814,35081),32768),((772,50177),(1846,36120),33792),((1443,36120),(1796,33793),33792),((1842,35864),(1798,33804),33800),((900,22656),(788,34564),0),((1441,34072),(1328,804),0),((1120,12384),(1792,34057),0),((1120,12384),(772,52489),0),((1120,12384),(417,3352),0),((1072,804),(900,22656),0),((1812,36105),(1328,804),256),((1328,548),(1328,1048),0)]

lemma box26_36ok : box26_36.all (boxAccept envelope26.2) = true := by decide +kernel

def box26_48 : List Box := [((1072,804),(1328,1048),34088)]

lemma box26_48ok : box26_48.all (boxAccept envelope26.2) = true := by decide +kernel

def box27_0 : List Box := [((2047,3),(2047,34056),0),((304,3352),(2047,34059),1288),((784,51209),(2047,34056),32778),((1013,34568),(2047,3),0),((768,52489),(2047,0),16649),((1794,51457),(2047,3),1),((1864,50441),(2047,3),1),((433,33540),(2047,3),0),((2047,3),(1443,32780),0),((1814,35080),(2047,33795),0),((1880,49161),(2047,3),1),((1798,1036),(2047,3),0)]

lemma box27_0ok : box27_0.all (boxAccept envelope27.2) = true := by decide +kernel

def box27_12 : List Box := [((2047,32771),(433,3336),0),((1808,774),(2047,32771),2),((1282,33804),(2047,3),0),((433,33540),(1443,32780),32772),((1459,33548),(1810,52489),33032),((417,3336),(1808,52489),3336),((562,19457),(840,50440),17672),((631,32771),(1798,1036),0),((1443,515),(1443,32780),0),((1959,33804),(853,2051),0),((520,16385),(2047,0),4099),((1032,8194),(2047,0),4099)]

lemma box27_12ok : box27_12.all (boxAccept envelope27.2) = true := by decide +kernel

def box27_24 : List Box := [((887,34819),(788,35080),32768),((1798,33804),(1443,515),0),((304,3096),(1443,33804),1032),((1443,515),(1808,32777),1),((16,772),(631,32771),32770),((1828,34073),(1808,774),0),((1808,32777),(1808,518),0),((1808,32777),(1552,774),0),((1808,518),(1328,1048),0)]

lemma box27_24ok : box27_24.all (boxAccept envelope27.2) = true := by decide +kernel

def box28_0 : List Box := [((2047,20608),(2047,3088),0),((501,2096),(2047,20608),0),((2047,23696),(1786,55440),0),((117,3120),(2047,20608),0),((213,28800),(2047,3088),0),((2047,3088),(1449,16576),0),((900,55425),(2047,3088),2048),((876,52241),(2047,20608),16384),((1314,3344),(2047,20608),0),((2047,20608),(1798,35072),0),((304,3096),(2047,20608),0),((288,36120),(2047,22672),51216)]

lemma box28_0ok : box28_0.all (boxAccept envelope28.2) = true := by decide +kernel

def box28_12 : List Box := [((1664,20609),(2047,3088),0),((501,3120),(1786,53376),0),((690,53376),(844,52488),49152),((634,19472),(844,50440),17424),((1015,3120),(840,50440),1024),((1866,49408),(631,3120),0),((501,3120),(213,28800),0),((1015,3120),(1449,16576),0),((544,19473),(2047,22656),23696),((1015,3120),(704,55425),2048),((634,19472),(964,52353),19456),((213,28800),(876,52504),16384)]

lemma box28_12ok : box28_12.all (boxAccept envelope28.2) = true := by decide +kernel

def box28_24 : List Box := [((117,3120),(964,22656),2048),((690,53376),(1798,35072),32768),((1640,52241),(1449,16576),16384),((762,56464),(900,56449),51200),((754,53376),(1586,34832),0),((304,3096),(501,28800),0),((1015,3120),(1728,20609),0),((1586,34832),(213,28800),0),((1586,34832),(1449,16576),0),((1314,3344),(213,28800),0),((1314,3344),(1449,16576),0),((1798,35072),(213,28800),0)]

lemma box28_24ok : box28_24.all (boxAccept envelope28.2) = true := by decide +kernel

def box28_36 : List Box := [((1798,35072),(1449,16576),0),((304,3096),(964,51328),2048),((1586,34832),(1664,20609),0),((288,3352),(704,51328),2048)]

lemma box28_36ok : box28_36.all (boxAccept envelope28.2) = true := by decide +kernel

def box29_0 : List Box := [((2047,772),(2047,3),0),((1040,8998),(2047,775),8998),((1443,515),(2047,772),512),((2047,3),(631,524),0),((2047,12),(1443,515),0),((1432,8964),(2047,3),0),((2047,3),(788,1796),0),((272,34564),(2047,3),0),((1328,804),(2047,3),0),((631,524),(1443,515),512),((1280,1032),(2047,0),1044),((1280,1032),(2047,0),28)]

lemma box29_0ok : box29_0.all (boxAccept envelope29.2) = true := by decide +kernel

def box29_12 : List Box := [((1280,514),(2047,0),517),((1432,8964),(1443,515),512)]

lemma box29_12ok : box29_12.all (boxAccept envelope29.2) = true := by decide +kernel

def box30_0 : List Box := [((640,55425),(2047,20608),55425),((704,51329),(2047,20608),16512),((2047,20608),(1443,3328),0),((501,28800),(1443,3328),0),((605,16387),(1449,16576),16384),((754,53376),(1443,3328),0),((1443,3328),(1449,16576),0),((900,22656),(1443,3328),2048),((9,195),(2047,0),24771),((1449,16576),(1728,20609),16512),((1664,20609),(1443,3328),0),((9,3),(501,28672),24576)]

lemma box30_0ok : box30_0.all (boxAccept envelope30.2) = true := by decide +kernel

def box31_0 : List Box := [((2047,48),(2047,772),0),((1296,8742),(2047,772),532),((2047,48),(631,524),0),((2047,48),(433,33540),0),((1040,8998),(2047,560),544),((1120,12384),(2047,804),0),((1328,1048),(2047,12),8),((304,3096),(2047,48),16),((2047,48),(272,34564),0),((2047,48),(1808,774),0),((501,2096),(1296,8998),32),((501,2096),(1176,8964),0)]

lemma box31_0ok : box31_0.all (boxAccept envelope31.2) = true := by decide +kernel

def box31_12 : List Box := [((631,524),(1328,1048),8),((1120,12384),(631,524),0),((501,2096),(1808,774),0),((1328,1048),(1443,32780),8),((1328,1048),(1798,1036),1032),((1120,12384),(433,33540),0),((1328,804),(1346,12864),512),((788,1796),(1088,12896),512),((304,3096),(1814,822),16),((1120,12384),(788,1796),0),((1298,34572),(1120,12384),0)]

lemma box31_12ok : box31_12.all (boxAccept envelope31.2) = true := by decide +kernel

def box32_0 : List Box := [((2047,12),(2047,3088),0),((288,3352),(2047,3088),3088),((304,3096),(2047,1036),1032),((544,19473),(772,50177),17425),((1314,3344),(1798,1036),1024)]

lemma box32_0ok : box32_0.all (boxAccept envelope32.2) = true := by decide +kernel

def box33_0 : List Box := [((2047,28800),(2047,3),0),((2047,3),(2047,28736),0),((1216,8802),(2047,12352),8256),((2047,3),(1786,53376),0),((1736,12898),(2047,3),2),((1736,55425),(2047,3),1),((1994,12864),(2047,3),0),((1996,22656),(2047,3),0),((2047,24643),(2045,24769),0),((1768,12384),(2047,3),0),((1728,20609),(2047,8384),129),((733,28864),(1736,12898),12353)]

lemma box33_0ok : box33_0.all (boxAccept envelope33.2) = true := by decide +kernel

def box33_12 : List Box := [((213,28800),(605,24771),24704),((1513,28739),(1736,55425),20481),((690,53376),(1608,12834),4096),((1152,16512),(2047,0),193),((640,55425),(1866,12800),4096),((512,16385),(2047,0),4227),((1346,12864),(1672,55297),4096),((690,53376),(1768,12384),4096),((605,16387),(1728,8802),2),((1120,12384),(1736,55425),4096),((1474,12864),(704,55425),0),((1474,12864),(964,22656),0)]

lemma box33_12ok : box33_12.all (boxAccept envelope33.2) = true := by decide +kernel

def box33_24 : List Box := [((704,55425),(1176,8964),0),((1248,8288),(754,49280),0),((964,22656),(1176,8964),0),((1176,8964),(1600,12354),8192),((704,55425),(1248,8288),0),((9,3),(481,28736),24576),((1728,20609),(1600,12354),0),((1664,20609),(1728,8258),0)]

lemma box33_24ok : box33_24.all (boxAccept envelope33.2) = true := by decide +kernel

def box34_0 : List Box := [((2047,48),(2047,12352),0),((1088,12898),(2047,12352),12898),((2047,48),(481,28736),0),((2047,48),(605,8384),0),((2047,48),(1176,8964),0),((2047,48),(1346,12864),0),((2047,48),(1728,12354),0),((605,8384),(1932,8240),8192),((1728,12354),(1932,8240),8192),((1120,12384),(1176,8964),8192),((9,192),(501,28736),24640)]

lemma box34_0ok : box34_0.all (boxAccept envelope34.2) = true := by decide +kernel

def box35_0 : List Box := [((1932,8240),(2047,192),0),((1640,18448),(2047,192),0)]

lemma box35_0ok : box35_0.all (boxAccept envelope35.2) = true := by decide +kernel

def boxes : List Box := (((((((box0_0 ++ box0_12) ++ (box0_24 ++ box0_36)) ++ ((box0_48 ++ box1_0) ++ (box1_12 ++ box1_24))) ++ (((box1_36 ++ box2_0) ++ (box2_12 ++ box2_24)) ++ ((box2_36 ++ box2_48) ++ (box3_0 ++ box3_12)))) ++ ((((box3_24 ++ box3_36) ++ (box3_48 ++ box4_0)) ++ ((box4_12 ++ box4_24) ++ (box4_36 ++ box4_48))) ++ (((box4_60 ++ box4_72) ++ (box5_0 ++ box5_12)) ++ ((box5_24 ++ box5_36) ++ (box5_48 ++ (box6_0 ++ box6_12)))))) ++ (((((box6_24 ++ box7_0) ++ (box7_12 ++ box7_24)) ++ ((box8_0 ++ box8_12) ++ (box8_24 ++ box8_36))) ++ (((box9_0 ++ box9_12) ++ (box9_24 ++ box10_0)) ++ ((box10_12 ++ box10_24) ++ (box10_36 ++ (box11_0 ++ box11_12))))) ++ ((((box11_24 ++ box11_36) ++ (box11_48 ++ box11_60)) ++ ((box12_0 ++ box12_12) ++ (box12_24 ++ box12_36))) ++ (((box12_48 ++ box13_0) ++ (box13_12 ++ box13_24)) ++ ((box13_36 ++ box13_48) ++ (box14_0 ++ (box14_12 ++ box14_24))))))) ++ ((((((box14_36 ++ box14_48) ++ (box14_60 ++ box15_0)) ++ ((box15_12 ++ box16_0) ++ (box17_0 ++ box17_12))) ++ (((box17_24 ++ box18_0) ++ (box18_12 ++ box18_24)) ++ ((box19_0 ++ box19_12) ++ (box19_24 ++ box19_36)))) ++ ((((box20_0 ++ box20_12) ++ (box20_24 ++ box20_36)) ++ ((box20_48 ++ box21_0) ++ (box21_12 ++ box21_24))) ++ (((box21_36 ++ box22_0) ++ (box22_12 ++ box22_24)) ++ ((box22_36 ++ box22_48) ++ (box23_0 ++ (box23_12 ++ box23_24)))))) ++ (((((box23_36 ++ box23_48) ++ (box24_0 ++ box24_12)) ++ ((box24_24 ++ box24_36) ++ (box25_0 ++ box25_12))) ++ (((box25_24 ++ box25_36) ++ (box25_48 ++ box26_0)) ++ ((box26_12 ++ box26_24) ++ (box26_36 ++ (box26_48 ++ box27_0))))) ++ ((((box27_12 ++ box27_24) ++ (box28_0 ++ box28_12)) ++ ((box28_24 ++ box28_36) ++ (box29_0 ++ box29_12))) ++ (((box30_0 ++ box31_0) ++ (box31_12 ++ box32_0)) ++ ((box33_0 ++ box33_12) ++ (box33_24 ++ (box34_0 ++ box35_0))))))))

lemma boxesAccepted {t : Box} (h : t ∈ boxes) : ∃ group ∈ catalogue, boxAccept group.2 t = true := by
  unfold boxes at h
  rcases List.mem_append.mp h with h | h
  ·
    rcases List.mem_append.mp h with h | h
    ·
      rcases List.mem_append.mp h with h | h
      ·
        rcases List.mem_append.mp h with h | h
        ·
          rcases List.mem_append.mp h with h | h
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope0,(List.getElem_mem (show 0 < catalogue.length by decide)),List.all_eq_true.mp box0_0ok t h⟩
              ·
                exact ⟨envelope0,(List.getElem_mem (show 0 < catalogue.length by decide)),List.all_eq_true.mp box0_12ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope0,(List.getElem_mem (show 0 < catalogue.length by decide)),List.all_eq_true.mp box0_24ok t h⟩
              ·
                exact ⟨envelope0,(List.getElem_mem (show 0 < catalogue.length by decide)),List.all_eq_true.mp box0_36ok t h⟩
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope0,(List.getElem_mem (show 0 < catalogue.length by decide)),List.all_eq_true.mp box0_48ok t h⟩
              ·
                exact ⟨envelope1,(List.getElem_mem (show 1 < catalogue.length by decide)),List.all_eq_true.mp box1_0ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope1,(List.getElem_mem (show 1 < catalogue.length by decide)),List.all_eq_true.mp box1_12ok t h⟩
              ·
                exact ⟨envelope1,(List.getElem_mem (show 1 < catalogue.length by decide)),List.all_eq_true.mp box1_24ok t h⟩
        ·
          rcases List.mem_append.mp h with h | h
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope1,(List.getElem_mem (show 1 < catalogue.length by decide)),List.all_eq_true.mp box1_36ok t h⟩
              ·
                exact ⟨envelope2,(List.getElem_mem (show 2 < catalogue.length by decide)),List.all_eq_true.mp box2_0ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope2,(List.getElem_mem (show 2 < catalogue.length by decide)),List.all_eq_true.mp box2_12ok t h⟩
              ·
                exact ⟨envelope2,(List.getElem_mem (show 2 < catalogue.length by decide)),List.all_eq_true.mp box2_24ok t h⟩
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope2,(List.getElem_mem (show 2 < catalogue.length by decide)),List.all_eq_true.mp box2_36ok t h⟩
              ·
                exact ⟨envelope2,(List.getElem_mem (show 2 < catalogue.length by decide)),List.all_eq_true.mp box2_48ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope3,(List.getElem_mem (show 3 < catalogue.length by decide)),List.all_eq_true.mp box3_0ok t h⟩
              ·
                exact ⟨envelope3,(List.getElem_mem (show 3 < catalogue.length by decide)),List.all_eq_true.mp box3_12ok t h⟩
      ·
        rcases List.mem_append.mp h with h | h
        ·
          rcases List.mem_append.mp h with h | h
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope3,(List.getElem_mem (show 3 < catalogue.length by decide)),List.all_eq_true.mp box3_24ok t h⟩
              ·
                exact ⟨envelope3,(List.getElem_mem (show 3 < catalogue.length by decide)),List.all_eq_true.mp box3_36ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope3,(List.getElem_mem (show 3 < catalogue.length by decide)),List.all_eq_true.mp box3_48ok t h⟩
              ·
                exact ⟨envelope4,(List.getElem_mem (show 4 < catalogue.length by decide)),List.all_eq_true.mp box4_0ok t h⟩
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope4,(List.getElem_mem (show 4 < catalogue.length by decide)),List.all_eq_true.mp box4_12ok t h⟩
              ·
                exact ⟨envelope4,(List.getElem_mem (show 4 < catalogue.length by decide)),List.all_eq_true.mp box4_24ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope4,(List.getElem_mem (show 4 < catalogue.length by decide)),List.all_eq_true.mp box4_36ok t h⟩
              ·
                exact ⟨envelope4,(List.getElem_mem (show 4 < catalogue.length by decide)),List.all_eq_true.mp box4_48ok t h⟩
        ·
          rcases List.mem_append.mp h with h | h
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope4,(List.getElem_mem (show 4 < catalogue.length by decide)),List.all_eq_true.mp box4_60ok t h⟩
              ·
                exact ⟨envelope4,(List.getElem_mem (show 4 < catalogue.length by decide)),List.all_eq_true.mp box4_72ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope5,(List.getElem_mem (show 5 < catalogue.length by decide)),List.all_eq_true.mp box5_0ok t h⟩
              ·
                exact ⟨envelope5,(List.getElem_mem (show 5 < catalogue.length by decide)),List.all_eq_true.mp box5_12ok t h⟩
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope5,(List.getElem_mem (show 5 < catalogue.length by decide)),List.all_eq_true.mp box5_24ok t h⟩
              ·
                exact ⟨envelope5,(List.getElem_mem (show 5 < catalogue.length by decide)),List.all_eq_true.mp box5_36ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope5,(List.getElem_mem (show 5 < catalogue.length by decide)),List.all_eq_true.mp box5_48ok t h⟩
              ·
                rcases List.mem_append.mp h with h | h
                ·
                  exact ⟨envelope6,(List.getElem_mem (show 6 < catalogue.length by decide)),List.all_eq_true.mp box6_0ok t h⟩
                ·
                  exact ⟨envelope6,(List.getElem_mem (show 6 < catalogue.length by decide)),List.all_eq_true.mp box6_12ok t h⟩
    ·
      rcases List.mem_append.mp h with h | h
      ·
        rcases List.mem_append.mp h with h | h
        ·
          rcases List.mem_append.mp h with h | h
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope6,(List.getElem_mem (show 6 < catalogue.length by decide)),List.all_eq_true.mp box6_24ok t h⟩
              ·
                exact ⟨envelope7,(List.getElem_mem (show 7 < catalogue.length by decide)),List.all_eq_true.mp box7_0ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope7,(List.getElem_mem (show 7 < catalogue.length by decide)),List.all_eq_true.mp box7_12ok t h⟩
              ·
                exact ⟨envelope7,(List.getElem_mem (show 7 < catalogue.length by decide)),List.all_eq_true.mp box7_24ok t h⟩
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope8,(List.getElem_mem (show 8 < catalogue.length by decide)),List.all_eq_true.mp box8_0ok t h⟩
              ·
                exact ⟨envelope8,(List.getElem_mem (show 8 < catalogue.length by decide)),List.all_eq_true.mp box8_12ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope8,(List.getElem_mem (show 8 < catalogue.length by decide)),List.all_eq_true.mp box8_24ok t h⟩
              ·
                exact ⟨envelope8,(List.getElem_mem (show 8 < catalogue.length by decide)),List.all_eq_true.mp box8_36ok t h⟩
        ·
          rcases List.mem_append.mp h with h | h
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope9,(List.getElem_mem (show 9 < catalogue.length by decide)),List.all_eq_true.mp box9_0ok t h⟩
              ·
                exact ⟨envelope9,(List.getElem_mem (show 9 < catalogue.length by decide)),List.all_eq_true.mp box9_12ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope9,(List.getElem_mem (show 9 < catalogue.length by decide)),List.all_eq_true.mp box9_24ok t h⟩
              ·
                exact ⟨envelope10,(List.getElem_mem (show 10 < catalogue.length by decide)),List.all_eq_true.mp box10_0ok t h⟩
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope10,(List.getElem_mem (show 10 < catalogue.length by decide)),List.all_eq_true.mp box10_12ok t h⟩
              ·
                exact ⟨envelope10,(List.getElem_mem (show 10 < catalogue.length by decide)),List.all_eq_true.mp box10_24ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope10,(List.getElem_mem (show 10 < catalogue.length by decide)),List.all_eq_true.mp box10_36ok t h⟩
              ·
                rcases List.mem_append.mp h with h | h
                ·
                  exact ⟨envelope11,(List.getElem_mem (show 11 < catalogue.length by decide)),List.all_eq_true.mp box11_0ok t h⟩
                ·
                  exact ⟨envelope11,(List.getElem_mem (show 11 < catalogue.length by decide)),List.all_eq_true.mp box11_12ok t h⟩
      ·
        rcases List.mem_append.mp h with h | h
        ·
          rcases List.mem_append.mp h with h | h
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope11,(List.getElem_mem (show 11 < catalogue.length by decide)),List.all_eq_true.mp box11_24ok t h⟩
              ·
                exact ⟨envelope11,(List.getElem_mem (show 11 < catalogue.length by decide)),List.all_eq_true.mp box11_36ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope11,(List.getElem_mem (show 11 < catalogue.length by decide)),List.all_eq_true.mp box11_48ok t h⟩
              ·
                exact ⟨envelope11,(List.getElem_mem (show 11 < catalogue.length by decide)),List.all_eq_true.mp box11_60ok t h⟩
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope12,(List.getElem_mem (show 12 < catalogue.length by decide)),List.all_eq_true.mp box12_0ok t h⟩
              ·
                exact ⟨envelope12,(List.getElem_mem (show 12 < catalogue.length by decide)),List.all_eq_true.mp box12_12ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope12,(List.getElem_mem (show 12 < catalogue.length by decide)),List.all_eq_true.mp box12_24ok t h⟩
              ·
                exact ⟨envelope12,(List.getElem_mem (show 12 < catalogue.length by decide)),List.all_eq_true.mp box12_36ok t h⟩
        ·
          rcases List.mem_append.mp h with h | h
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope12,(List.getElem_mem (show 12 < catalogue.length by decide)),List.all_eq_true.mp box12_48ok t h⟩
              ·
                exact ⟨envelope13,(List.getElem_mem (show 13 < catalogue.length by decide)),List.all_eq_true.mp box13_0ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope13,(List.getElem_mem (show 13 < catalogue.length by decide)),List.all_eq_true.mp box13_12ok t h⟩
              ·
                exact ⟨envelope13,(List.getElem_mem (show 13 < catalogue.length by decide)),List.all_eq_true.mp box13_24ok t h⟩
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope13,(List.getElem_mem (show 13 < catalogue.length by decide)),List.all_eq_true.mp box13_36ok t h⟩
              ·
                exact ⟨envelope13,(List.getElem_mem (show 13 < catalogue.length by decide)),List.all_eq_true.mp box13_48ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope14,(List.getElem_mem (show 14 < catalogue.length by decide)),List.all_eq_true.mp box14_0ok t h⟩
              ·
                rcases List.mem_append.mp h with h | h
                ·
                  exact ⟨envelope14,(List.getElem_mem (show 14 < catalogue.length by decide)),List.all_eq_true.mp box14_12ok t h⟩
                ·
                  exact ⟨envelope14,(List.getElem_mem (show 14 < catalogue.length by decide)),List.all_eq_true.mp box14_24ok t h⟩
  ·
    rcases List.mem_append.mp h with h | h
    ·
      rcases List.mem_append.mp h with h | h
      ·
        rcases List.mem_append.mp h with h | h
        ·
          rcases List.mem_append.mp h with h | h
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope14,(List.getElem_mem (show 14 < catalogue.length by decide)),List.all_eq_true.mp box14_36ok t h⟩
              ·
                exact ⟨envelope14,(List.getElem_mem (show 14 < catalogue.length by decide)),List.all_eq_true.mp box14_48ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope14,(List.getElem_mem (show 14 < catalogue.length by decide)),List.all_eq_true.mp box14_60ok t h⟩
              ·
                exact ⟨envelope15,(List.getElem_mem (show 15 < catalogue.length by decide)),List.all_eq_true.mp box15_0ok t h⟩
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope15,(List.getElem_mem (show 15 < catalogue.length by decide)),List.all_eq_true.mp box15_12ok t h⟩
              ·
                exact ⟨envelope16,(List.getElem_mem (show 16 < catalogue.length by decide)),List.all_eq_true.mp box16_0ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope17,(List.getElem_mem (show 17 < catalogue.length by decide)),List.all_eq_true.mp box17_0ok t h⟩
              ·
                exact ⟨envelope17,(List.getElem_mem (show 17 < catalogue.length by decide)),List.all_eq_true.mp box17_12ok t h⟩
        ·
          rcases List.mem_append.mp h with h | h
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope17,(List.getElem_mem (show 17 < catalogue.length by decide)),List.all_eq_true.mp box17_24ok t h⟩
              ·
                exact ⟨envelope18,(List.getElem_mem (show 18 < catalogue.length by decide)),List.all_eq_true.mp box18_0ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope18,(List.getElem_mem (show 18 < catalogue.length by decide)),List.all_eq_true.mp box18_12ok t h⟩
              ·
                exact ⟨envelope18,(List.getElem_mem (show 18 < catalogue.length by decide)),List.all_eq_true.mp box18_24ok t h⟩
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope19,(List.getElem_mem (show 19 < catalogue.length by decide)),List.all_eq_true.mp box19_0ok t h⟩
              ·
                exact ⟨envelope19,(List.getElem_mem (show 19 < catalogue.length by decide)),List.all_eq_true.mp box19_12ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope19,(List.getElem_mem (show 19 < catalogue.length by decide)),List.all_eq_true.mp box19_24ok t h⟩
              ·
                exact ⟨envelope19,(List.getElem_mem (show 19 < catalogue.length by decide)),List.all_eq_true.mp box19_36ok t h⟩
      ·
        rcases List.mem_append.mp h with h | h
        ·
          rcases List.mem_append.mp h with h | h
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope20,(List.getElem_mem (show 20 < catalogue.length by decide)),List.all_eq_true.mp box20_0ok t h⟩
              ·
                exact ⟨envelope20,(List.getElem_mem (show 20 < catalogue.length by decide)),List.all_eq_true.mp box20_12ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope20,(List.getElem_mem (show 20 < catalogue.length by decide)),List.all_eq_true.mp box20_24ok t h⟩
              ·
                exact ⟨envelope20,(List.getElem_mem (show 20 < catalogue.length by decide)),List.all_eq_true.mp box20_36ok t h⟩
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope20,(List.getElem_mem (show 20 < catalogue.length by decide)),List.all_eq_true.mp box20_48ok t h⟩
              ·
                exact ⟨envelope21,(List.getElem_mem (show 21 < catalogue.length by decide)),List.all_eq_true.mp box21_0ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope21,(List.getElem_mem (show 21 < catalogue.length by decide)),List.all_eq_true.mp box21_12ok t h⟩
              ·
                exact ⟨envelope21,(List.getElem_mem (show 21 < catalogue.length by decide)),List.all_eq_true.mp box21_24ok t h⟩
        ·
          rcases List.mem_append.mp h with h | h
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope21,(List.getElem_mem (show 21 < catalogue.length by decide)),List.all_eq_true.mp box21_36ok t h⟩
              ·
                exact ⟨envelope22,(List.getElem_mem (show 22 < catalogue.length by decide)),List.all_eq_true.mp box22_0ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope22,(List.getElem_mem (show 22 < catalogue.length by decide)),List.all_eq_true.mp box22_12ok t h⟩
              ·
                exact ⟨envelope22,(List.getElem_mem (show 22 < catalogue.length by decide)),List.all_eq_true.mp box22_24ok t h⟩
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope22,(List.getElem_mem (show 22 < catalogue.length by decide)),List.all_eq_true.mp box22_36ok t h⟩
              ·
                exact ⟨envelope22,(List.getElem_mem (show 22 < catalogue.length by decide)),List.all_eq_true.mp box22_48ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope23,(List.getElem_mem (show 23 < catalogue.length by decide)),List.all_eq_true.mp box23_0ok t h⟩
              ·
                rcases List.mem_append.mp h with h | h
                ·
                  exact ⟨envelope23,(List.getElem_mem (show 23 < catalogue.length by decide)),List.all_eq_true.mp box23_12ok t h⟩
                ·
                  exact ⟨envelope23,(List.getElem_mem (show 23 < catalogue.length by decide)),List.all_eq_true.mp box23_24ok t h⟩
    ·
      rcases List.mem_append.mp h with h | h
      ·
        rcases List.mem_append.mp h with h | h
        ·
          rcases List.mem_append.mp h with h | h
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope23,(List.getElem_mem (show 23 < catalogue.length by decide)),List.all_eq_true.mp box23_36ok t h⟩
              ·
                exact ⟨envelope23,(List.getElem_mem (show 23 < catalogue.length by decide)),List.all_eq_true.mp box23_48ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope24,(List.getElem_mem (show 24 < catalogue.length by decide)),List.all_eq_true.mp box24_0ok t h⟩
              ·
                exact ⟨envelope24,(List.getElem_mem (show 24 < catalogue.length by decide)),List.all_eq_true.mp box24_12ok t h⟩
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope24,(List.getElem_mem (show 24 < catalogue.length by decide)),List.all_eq_true.mp box24_24ok t h⟩
              ·
                exact ⟨envelope24,(List.getElem_mem (show 24 < catalogue.length by decide)),List.all_eq_true.mp box24_36ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope25,(List.getElem_mem (show 25 < catalogue.length by decide)),List.all_eq_true.mp box25_0ok t h⟩
              ·
                exact ⟨envelope25,(List.getElem_mem (show 25 < catalogue.length by decide)),List.all_eq_true.mp box25_12ok t h⟩
        ·
          rcases List.mem_append.mp h with h | h
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope25,(List.getElem_mem (show 25 < catalogue.length by decide)),List.all_eq_true.mp box25_24ok t h⟩
              ·
                exact ⟨envelope25,(List.getElem_mem (show 25 < catalogue.length by decide)),List.all_eq_true.mp box25_36ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope25,(List.getElem_mem (show 25 < catalogue.length by decide)),List.all_eq_true.mp box25_48ok t h⟩
              ·
                exact ⟨envelope26,(List.getElem_mem (show 26 < catalogue.length by decide)),List.all_eq_true.mp box26_0ok t h⟩
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope26,(List.getElem_mem (show 26 < catalogue.length by decide)),List.all_eq_true.mp box26_12ok t h⟩
              ·
                exact ⟨envelope26,(List.getElem_mem (show 26 < catalogue.length by decide)),List.all_eq_true.mp box26_24ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope26,(List.getElem_mem (show 26 < catalogue.length by decide)),List.all_eq_true.mp box26_36ok t h⟩
              ·
                rcases List.mem_append.mp h with h | h
                ·
                  exact ⟨envelope26,(List.getElem_mem (show 26 < catalogue.length by decide)),List.all_eq_true.mp box26_48ok t h⟩
                ·
                  exact ⟨envelope27,(List.getElem_mem (show 27 < catalogue.length by decide)),List.all_eq_true.mp box27_0ok t h⟩
      ·
        rcases List.mem_append.mp h with h | h
        ·
          rcases List.mem_append.mp h with h | h
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope27,(List.getElem_mem (show 27 < catalogue.length by decide)),List.all_eq_true.mp box27_12ok t h⟩
              ·
                exact ⟨envelope27,(List.getElem_mem (show 27 < catalogue.length by decide)),List.all_eq_true.mp box27_24ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope28,(List.getElem_mem (show 28 < catalogue.length by decide)),List.all_eq_true.mp box28_0ok t h⟩
              ·
                exact ⟨envelope28,(List.getElem_mem (show 28 < catalogue.length by decide)),List.all_eq_true.mp box28_12ok t h⟩
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope28,(List.getElem_mem (show 28 < catalogue.length by decide)),List.all_eq_true.mp box28_24ok t h⟩
              ·
                exact ⟨envelope28,(List.getElem_mem (show 28 < catalogue.length by decide)),List.all_eq_true.mp box28_36ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope29,(List.getElem_mem (show 29 < catalogue.length by decide)),List.all_eq_true.mp box29_0ok t h⟩
              ·
                exact ⟨envelope29,(List.getElem_mem (show 29 < catalogue.length by decide)),List.all_eq_true.mp box29_12ok t h⟩
        ·
          rcases List.mem_append.mp h with h | h
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope30,(List.getElem_mem (show 30 < catalogue.length by decide)),List.all_eq_true.mp box30_0ok t h⟩
              ·
                exact ⟨envelope31,(List.getElem_mem (show 31 < catalogue.length by decide)),List.all_eq_true.mp box31_0ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope31,(List.getElem_mem (show 31 < catalogue.length by decide)),List.all_eq_true.mp box31_12ok t h⟩
              ·
                exact ⟨envelope32,(List.getElem_mem (show 32 < catalogue.length by decide)),List.all_eq_true.mp box32_0ok t h⟩
          ·
            rcases List.mem_append.mp h with h | h
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope33,(List.getElem_mem (show 33 < catalogue.length by decide)),List.all_eq_true.mp box33_0ok t h⟩
              ·
                exact ⟨envelope33,(List.getElem_mem (show 33 < catalogue.length by decide)),List.all_eq_true.mp box33_12ok t h⟩
            ·
              rcases List.mem_append.mp h with h | h
              ·
                exact ⟨envelope33,(List.getElem_mem (show 33 < catalogue.length by decide)),List.all_eq_true.mp box33_24ok t h⟩
              ·
                rcases List.mem_append.mp h with h | h
                ·
                  exact ⟨envelope34,(List.getElem_mem (show 34 < catalogue.length by decide)),List.all_eq_true.mp box34_0ok t h⟩
                ·
                  exact ⟨envelope35,(List.getElem_mem (show 35 < catalogue.length by decide)),List.all_eq_true.mp box35_0ok t h⟩

def codeMask : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | k+1, f => Nat.bit (f 0) (codeMask k (fun i => f (i+1)))

lemma codeBit (k : ℕ) (f : ℕ → Bool) (i : ℕ) (h : i < k) : (codeMask k f).testBit i = f i := by
  induction k generalizing i f with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero => exact Nat.testBit_bit_zero _ _
    | succ i => exact (Nat.testBit_bit_succ _ _ _).trans (ih _ i (by omega))

lemma codeBound (k : ℕ) (f : ℕ → Bool) : codeMask k f < 2^k := by
  induction k generalizing f with
  | zero => simp [codeMask]
  | succ k ih =>
    have h := ih (fun i => f (i+1))
    rw [codeMask,pow_succ]
    cases f 0 <;> simp only [Nat.bit_false,Nat.bit_true] <;> omega

def armMask (S : Finset (Fin 11)) := codeMask 11 (fun i => if h : i < 11 then decide (⟨i,h⟩ ∈ S) else false)

lemma armMem (S : Finset (Fin 11)) (v : Fin 11) : (armMask S).testBit v.val = true ↔ v ∈ S := by
  simp [armMask,codeBit _ _ _ v.isLt,v.isLt]

def meets (a b : ℕ) := (a &&& b) != 0

lemma meetsIff (a b : ℕ) : meets a b = true ↔ ∃ i, a.testBit i = true ∧ b.testBit i = true := by
  simp only [meets,bne_iff_ne]
  constructor
  · contrapose!
    intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and,Nat.zero_testBit,Bool.and_eq_false_imp]
    simpa using h i
  · rintro ⟨i,hi,hj⟩ hz
    have bits := congrArg (fun m : ℕ => m.testBit i) hz
    simpa [Nat.testBit_and,hi,hj] using bits

lemma hitsMask (S : Finset (Fin 11)) (r : ℕ) :
    hit S (fun i => row r i = true) ↔ meets (armMask S) r = true := by
  rw [meetsIff]
  constructor
  · rintro ⟨v,hv,vr⟩
    exact ⟨v.val,(armMem S v).2 hv,vr⟩
  · rintro ⟨i,hi,on⟩
    have small : i < 11 := by
      by_contra! big
      have off := Nat.testBit_lt_two_pow (x:=armMask S) (i:=i)
        ((codeBound 11 _).trans_le (Nat.pow_le_pow_right (by decide) big))
      simp [off] at hi
    exact ⟨⟨i,small⟩,(armMem S ⟨i,small⟩).1 hi,on⟩

def signature (rows : List ℕ) (a b : ℕ) := codeMask rows.length fun i =>
  meets a (rows.getD i 0) && meets b (rows.getD i 0)

def Encode (s : Arms 11) (a b : ℕ) :=
  (a = armMask s.1 ∧ b = armMask s.2) ∨ (b = armMask s.1 ∧ a = armMask s.2)

lemma signatureSpec {a b : ℕ} {s : Arms 11} (en : Encode s a b) (rs : List ℕ)
    (i : ℕ) (hi : i < rs.length) :
    (signature rs a b).testBit i = true ↔ active s (rs.getD i 0) := by
  simp only [signature,codeBit _ _ _ hi,active,fires,hitsMask,Bool.and_eq_true]
  rcases en with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · exact and_comm

def negVertex : List ℕ := [32767,10126677,521011,11112463,330410,1576140,401648,5263104,6320128,8880128,16252928]
lemma negVertexEq : ∀ v : Fin 11, ∀ i : Fin 24,
    (negVertex.getD v.val 0).testBit i.val = row (negRows.getD i.val 0) v := by decide +kernel

lemma posVertexEq : ∀ v : Fin 11, ∀ i : Fin 16,
    (vertexRows.getD v.val 0).testBit i.val = row (posRows.getD i.val 0) v := by decide +kernel

def guarded (n : ℕ) := codeMask 11 fun v => !(meets n (negVertex.getD v 0))
def coversVertex (e : ℕ) := codeMask 11 fun v => meets e (vertexRows.getD v 0)
def below (n m : ℕ) := (n &&& m) == n

lemma belowBit {n m : ℕ} (h : below n m = true) {i : ℕ} (hi : n.testBit i = true) : m.testBit i = true := by
  have b := congrArg (fun a : ℕ => a.testBit i) (beq_iff_eq.mp h)
  simpa only [Nat.testBit_and,hi,Bool.true_and] using b

lemma belowIff {n m : ℕ} : below n m = true ↔ ∀ i, n.testBit i = true → m.testBit i = true := by
  refine ⟨fun h _ hi => belowBit h hi,?_⟩
  intro h
  apply beq_iff_eq.mpr
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  cases val : n.testBit i
  · rfl
  · simp [h i val]

lemma guardOn {d : Arms 11} {a b : ℕ} (enc : Encode d a b) {v : Fin 11} (safe : safeV d v) :
    (guarded (signature negRows a b)).testBit v.val = true := by
  simp only [guarded,codeBit _ _ _ v.isLt,Bool.not_eq_true']
  by_contra! h
  obtain ⟨i,on,raw⟩ := (meetsIff _ _).mp (Bool.eq_true_of_not_eq_false h)
  have bound : i < negRows.length := by
    by_contra! big
    have off := Nat.testBit_lt_two_pow (x:=signature negRows a b) (i:=i)
      ((codeBound negRows.length _).trans_le (Nat.pow_le_pow_right (by decide) big))
    simp [off] at on
  let k : Fin 24 := ⟨i,bound⟩
  have mem : negRows.getD i 0 ∈ negRows := by rw [List.getD_eq_getElem _ _ bound]; exact List.getElem_mem _
  exact safe _ mem ⟨(signatureSpec enc _ i bound).1 on, (negVertexEq v k) ▸ raw⟩

def rawProfile (n e : ℕ) : Profile := (guarded n,e &&& touchAux (guarded n) 11)
def rawJoint (n e m f : ℕ) := if meets n m then 0 else e &&& f
def ProfileBelow (s t : Profile) := below s.1 t.1 && below s.2 t.2
def containsBox (n e m f : ℕ) (t : Box) := ProfileBelow (rawProfile n e) t.1 &&
  ProfileBelow (rawProfile m f) t.2.1 && below (rawJoint n e m f) t.2.2

lemma rawSingle {d : Arms 11} {a b : ℕ} (enc : Encode d a b) :
    BoundsSingle d (rawProfile (signature negRows a b) (signature posRows a b)) := by
  refine ⟨fun _ h => guardOn enc h,?_⟩
  intro v i safe on yes
  rw [rawProfile,Nat.testBit_and,Bool.and_eq_true]
  exact ⟨(signatureSpec enc posRows i.val i.isLt).2 yes,
    touchAuxOn v.isLt (guardOn enc safe) (vertexRowsOn v i on)⟩

lemma rawBoth {d e : Arms 11} {a b c f : ℕ} (first : Encode d a b) (second : Encode e c f) :
    BoundsJoint d e (rawJoint (signature negRows a b) (signature posRows a b)
      (signature negRows c f) (signature posRows c f)) := by
  intro i safe da ea
  have no : meets (signature negRows a b) (signature negRows c f) = false := by
    by_contra! h
    obtain ⟨k,on,yes⟩ := (meetsIff _ _).mp (Bool.eq_true_of_not_eq_false h)
    have bound : k < negRows.length := by
      by_contra! big
      have off := Nat.testBit_lt_two_pow (x:=signature negRows a b) (i:=k)
        ((codeBound negRows.length _).trans_le (Nat.pow_le_pow_right (by decide) big))
      simp [off] at on
    have mem : negRows.getD k 0 ∈ negRows := by rw [List.getD_eq_getElem _ _ bound]; exact List.getElem_mem _
    exact safe _ mem ⟨(signatureSpec first _ k bound).1 on,(signatureSpec second _ k bound).1 yes⟩
  simp only [rawJoint,no,Bool.false_eq_true,↓reduceIte,Nat.testBit_and,Bool.and_eq_true]
  exact ⟨(signatureSpec first _ _ i.isLt).2 da,(signatureSpec second _ _ i.isLt).2 ea⟩

lemma boundsEnlarge {d : Arms 11} {p q : Profile} (h : BoundsSingle d p) (le : ProfileBelow p q = true) :
    BoundsSingle d q := by
  obtain ⟨L,R⟩ := (Bool.and_eq_true_iff).1 le
  exact ⟨fun v hv => belowBit L (h.1 v hv),fun v i s on a => belowBit R (h.2 v i s on a)⟩

lemma containsSound {d e : Arms 11} {a b c f : ℕ} (first : Encode d a b) (second : Encode e c f)
    (t : Box) (h : containsBox (signature negRows a b) (signature posRows a b)
       (signature negRows c f) (signature posRows c f) t = true) : Mirrors d e t := by
  obtain ⟨lr,J⟩ := (Bool.and_eq_true_iff).1 h
  obtain ⟨L,R⟩ := (Bool.and_eq_true_iff).1 lr
  exact ⟨boundsEnlarge (rawSingle first) L,boundsEnlarge (rawSingle second) R,
    fun i sj f1 f2 => belowBit J (rawBoth first second i sj f1 f2)⟩

def trimmedShape (a b : ℕ) := below (a ||| b) (coversVertex (signature posRows a b))
def shapeOK (a b : ℕ) := a ≤ b ∧ b < 2048 ∧ (a &&& b) = 0 ∧ trimmedShape a b = true

lemma armSmall (S : Finset (Fin 11)) : armMask S < 2048 := codeBound 11 _

lemma admitShape {d : Arms 11} (can : Canonical d) : ∃ a b, Encode d a b ∧ shapeOK a b := by
  let a := armMask d.1
  let b := armMask d.2
  have enc : Encode d a b := Or.inl ⟨rfl,rfl⟩
  have order {x i : ℕ} (hx : x < 2048) (on : x.testBit i = true) : i < 11 := by
    by_contra! hi
    have b := Nat.testBit_lt_two_pow (x:=x) (i:=i) (hx.trans_le (Nat.pow_le_pow_right (n:=2) (by decide) hi))
    simp [b] at on
  have no : a &&& b = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and,Nat.zero_testBit]
    cases h : a.testBit i
    · rfl
    · have small := order (armSmall d.1) h
      have no := Finset.disjoint_left.mp can.1 ((armMem d.1 ⟨i,small⟩).1 h)
      have off : b.testBit i = false := by
        cases v : b.testBit i <;> simp_all [show ¬b.testBit i = true from fun t => no ((armMem d.2 ⟨i,small⟩).1 t)]
      simp [off]
  have cap (x y : ℕ) (en : Encode d x y) : trimmedShape x y = true := by
    apply belowIff.mpr
    intro i hi
    have hmem : a.testBit i = true ∨ b.testBit i = true := by
      rcases en with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · simpa [a,b,Nat.testBit_or] using hi
      · simpa [a,b,Nat.testBit_or,or_comm] using hi
    have bound : i < 11 := hmem.elim (order (armSmall _)) (order (armSmall _))
    let u : Fin 11 := ⟨i,bound⟩
    have mem : u ∈ d.1 ∪ d.2 := Finset.mem_union.mpr (hmem.imp ((armMem _ u).1) ((armMem _ u).1))
    obtain ⟨r,hr,vu,on⟩ := can.2 u mem
    obtain ⟨k,hk,eq⟩ := List.mem_iff_getElem.mp hr
    have eq' : posRows.getD k 0 = r := by rw [List.getD_eq_getElem _ _ hk]; exact eq
    simp only [coversVertex,codeBit _ _ _ bound]
    apply (meetsIff _ _).2
    exact ⟨k,(signatureSpec en _ _ hk).2 (eq' ▸ on),(posVertexEq u ⟨k,hk⟩) ▸ (eq' ▸ vu)⟩
  by_cases le : a ≤ b
  · exact ⟨a,b,enc,le,armSmall _,no,cap _ _ enc⟩
  · have en : Encode d b a := Or.inr ⟨rfl,rfl⟩
    exact ⟨b,a,en,by omega,armSmall _,by rw [Nat.and_comm,no],cap _ _ en⟩

def finiteCertificate (B : List Box) := ∀ a b c f : ℕ, shapeOK a b → shapeOK c f →
    ∃ t ∈ B,
      containsBox (signature negRows a b) (signature posRows a b) (signature negRows c f) (signature posRows c f) t = true ∨
      containsBox (signature negRows c f) (signature posRows c f) (signature negRows a b) (signature posRows a b) t = true

lemma coversViaFinite {B : List Box} (finite : finiteCertificate B) :
    ∀ d e : Arms 11, Canonical d → Canonical e → ∃ t ∈ B, Mirrors d e t ∨ Mirrors e d t := by
  intro d e left right
  obtain ⟨a,b,de,ds⟩ := admitShape left
  obtain ⟨c,f,ee,es⟩ := admitShape right
  obtain ⟨t,ht,spec⟩ := finite _ _ _ _ ds es
  exact ⟨t,ht,spec.imp (containsSound de ee t) (containsSound ee de t)⟩

theorem unit8159Reduced (checked : finiteCertificate boxes) : TablesImpossible :=
  certCloses (coversViaFinite checked) (fun _ => boxesAccepted)

abbrev Hull := Profile × ℕ × ℕ

def decodeHull (w : ℕ) : Hull :=
  ((w % 2048,(w >>> 11) % 65536),(w >>> 27) % 16777216,(w >>> 51) % 65536)

def shapeHull (n e : ℕ) : Hull := (rawProfile n e,n,e)
def underHull (a b : Hull) := ProfileBelow a.1 b.1 && below b.2.1 a.2.1 && below a.2.2 b.2.2

def holdsBox (a b : Hull) (t : Box) := ProfileBelow a.1 t.1 && ProfileBelow b.1 t.2.1 &&
  below (rawJoint a.2.1 a.2.2 b.2.1 b.2.2) t.2.2

lemma leMaskTrans {x y z : ℕ} (h : below x y = true) (k : below y z = true) : below x z = true :=
  belowIff.2 (fun _ hx => belowBit k (belowBit h hx))

lemma profileTrans {x y z : Profile} (h : ProfileBelow x y = true) (k : ProfileBelow y z = true) :
    ProfileBelow x z = true := by
  obtain ⟨h1,h2⟩ := (Bool.and_eq_true_iff).1 h
  obtain ⟨k1,k2⟩ := (Bool.and_eq_true_iff).1 k
  exact (Bool.and_eq_true_iff).2 ⟨leMaskTrans h1 k1,leMaskTrans h2 k2⟩

lemma meetsUp {x y u v : ℕ} (xu : below x u = true) (yv : below y v = true) (on : meets x y = true) :
    meets u v = true := by
  obtain ⟨i,h,k⟩ := (meetsIff _ _).1 on
  exact (meetsIff _ _).2 ⟨i,belowBit xu h,belowBit yv k⟩

lemma jointUp {a b A B : Hull} (ha : underHull a A = true) (hb : underHull b B = true) :
    below (rawJoint a.2.1 a.2.2 b.2.1 b.2.2) (rawJoint A.2.1 A.2.2 B.2.1 B.2.2) = true := by
  obtain ⟨ha,ap⟩ := (Bool.and_eq_true_iff).1 ha
  obtain ⟨_,an⟩ := (Bool.and_eq_true_iff).1 ha
  obtain ⟨hb,bp⟩ := (Bool.and_eq_true_iff).1 hb
  obtain ⟨_,bn⟩ := (Bool.and_eq_true_iff).1 hb
  apply belowIff.2
  intro i h
  by_cases collision : meets a.2.1 b.2.1 = true
  · simp [rawJoint,collision] at h
  have wide : ¬meets A.2.1 B.2.1 = true := fun t => collision (meetsUp an bn t)
  simp only [rawJoint,ite_eq_right collision,Nat.testBit_and,Bool.and_eq_true] at h
  simp only [rawJoint,ite_eq_right wide,Nat.testBit_and,Bool.and_eq_true]
  exact ⟨belowBit ap h.1,belowBit bp h.2⟩

lemma holdsUnder {a b A B : Hull} {t : Box} (ha : underHull a A = true) (hb : underHull b B = true)
    (ok : holdsBox A B t = true) : holdsBox a b t = true := by
  have ap := (Bool.and_eq_true_iff).1 ((Bool.and_eq_true_iff).1 ha).1
  have bp := (Bool.and_eq_true_iff).1 ((Bool.and_eq_true_iff).1 hb).1
  obtain ⟨lr,jo⟩ := (Bool.and_eq_true_iff).1 ok
  obtain ⟨l,r⟩ := (Bool.and_eq_true_iff).1 lr
  exact (Bool.and_eq_true_iff).2 ⟨(Bool.and_eq_true_iff).2 ⟨profileTrans ap.1 l,profileTrans bp.1 r⟩,
    leMaskTrans (jointUp ha hb) jo⟩

def flipBox (t : Box) : Box := (t.2.1,t.1,t.2.2)

lemma flipped {a b : Hull} {t : Box} (h : holdsBox a b (flipBox t) = true) : holdsBox b a t = true := by
  have swap : rawJoint b.2.1 b.2.2 a.2.1 a.2.2 = rawJoint a.2.1 a.2.2 b.2.1 b.2.2 := by
    unfold rawJoint meets
    rw [Nat.and_comm b.2.1 a.2.1,Nat.and_comm b.2.2 a.2.2]
  obtain ⟨lr,j⟩ := (Bool.and_eq_true_iff).1 h
  obtain ⟨l,r⟩ := (Bool.and_eq_true_iff).1 lr
  exact (Bool.and_eq_true_iff).2 ⟨(Bool.and_eq_true_iff).2 ⟨r,l⟩,swap ▸ j⟩


def blockBits : ℕ → ℕ → (ℕ → Bool) → ℕ
  | 0, s, f => if f s then 1 else 0
  | k+1, s, f =>
    blockBits k s f ||| (blockBits k (s+2^k) f <<< (2^k))

lemma blockBitsAt (k s : ℕ) (f : ℕ → Bool) (i : ℕ) :
    (blockBits k s f).testBit i = (decide (i < 2^k) && f (s+i)) := by
  induction k generalizing s i with
  | zero =>
    cases i with
    | zero => cases h : f s <;> simp [blockBits,h]
    | succ i =>
      have off : Nat.testBit 1 (i+1) = false := by
        exact Nat.testBit_lt_two_pow ((by decide : 1 < 2^1).trans_le (Nat.pow_le_pow_right (by decide) (show 1 ≤ i+1 by omega)))
      cases h : f s <;> simp [blockBits,h,off]
  | succ k ih =>
    rw [blockBits,Nat.testBit_or,Nat.testBit_shiftLeft,ih,ih,pow_succ]
    by_cases lo : i < 2^k
    · have hi : i < 2^k*2 := by omega
      simp [lo,hi,Nat.not_le.mpr lo]
    · have le : 2^k ≤ i := by omega
      have eq : s+2^k+(i-2^k) = s+i := by omega
      have lt : i-2^k < 2^k ↔ i < 2^k*2 := by omega
      simp [lo,le,eq,lt]

def bigOnes (n : ℕ) := (1 <<< n)-1
lemma onesOn {b w : ℕ} (h : b < w) : (bigOnes w).testBit b = true := by
  simp [bigOnes,Nat.shiftLeft_eq,Nat.testBit_two_pow_sub_one,h]

def everyMask (full : ℕ) (xs : List ℕ) := xs.foldr (· &&& ·) full

lemma everyMaskOn {xs : List ℕ} {i full : ℕ} (hf : full.testBit i = true)
    (h : ∀ n ∈ xs, n.testBit i = true) : (everyMask full xs).testBit i = true := by
  induction xs with
  | nil => exact hf
  | cons a xs ih =>
    rw [everyMask,List.foldr_cons,Nat.testBit_and,Bool.and_eq_true]
    exact ⟨h a (by simp),ih (fun n hn => h n (by simp [hn]))⟩

def neighbor (v : ℕ) := nearRows.getD v 0
lemma oppositeEndpoint : ∀ (j : Fin 16) (u v : Fin 11), u ≠ v → row (posAt j) u = true →
    row (posAt j) v = true → (neighbor u.val).testBit v.val = true := by decide +kernel

lemma outsideBits {a i k : ℕ} (small : a < 2^k) (on : a.testBit i = true) : i < k := by
  by_contra! h
  have off := Nat.testBit_lt_two_pow (x:=a) (i:=i) (small.trans_le (Nat.pow_le_pow_right (by decide) h))
  simp [off] at on

lemma hasPartner {a b v : ℕ} (hv : v < 11) (ha : a < 2048) (bit : a.testBit v = false)
    (need : (coversVertex (signature posRows a b)).testBit v = true) : meets a (neighbor v) = true := by
  simp only [coversVertex,codeBit _ _ _ hv] at need
  obtain ⟨j,hj,vu⟩ := (meetsIff _ _).1 need
  have small : j < posRows.length := outsideBits (codeBound _ _) hj
  have active : meets a (posRows.getD j 0) = true ∧ meets b (posRows.getD j 0) = true := by
    simpa only [signature,codeBit _ _ _ small,Bool.and_eq_true] using hj
  obtain ⟨w,aw,rw⟩ := (meetsIff _ _).1 active.1
  have wlow : w < 11 := outsideBits (k:=11) ha aw
  let x : Fin 11 := ⟨v,hv⟩
  let y : Fin 11 := ⟨w,wlow⟩
  have ne : x ≠ y := by
    intro h
    have he : v = w := congrArg Fin.val h
    simp [← he,bit] at aw
  have uon : row (posAt ⟨j,small⟩) x = true := (posVertexEq x ⟨j,small⟩).symm.trans vu
  exact (meetsIff _ _).2 ⟨w,aw,oppositeEndpoint ⟨j,small⟩ x y ne uon rw⟩

lemma sigSwap (ls : List ℕ) (a b : ℕ) : signature ls a b = signature ls b a := by
  unfold signature
  congr 1
  funext i
  exact Bool.and_comm _ _

def domainFor (absent partners : List ℕ) (a : ℕ) :=
  everyMask (bigOnes 2048) ((List.range 11).map fun v =>
    if a.testBit v then absent.getD v 0 &&& partners.getD v 0
    else if meets a (neighbor v) then bigOnes 2048 else absent.getD v 0)

lemma domainForSound {absent partners : List ℕ}
    (ac : ∀ v : Fin 11, blockBits 11 0 (fun b => !(b.testBit v.val)) = absent.getD v.val 0)
    (pc : ∀ v : Fin 11, blockBits 11 0 (fun b => meets b (neighbor v.val)) = partners.getD v.val 0)
    {a b : ℕ} (ok : shapeOK a b) : (domainFor absent partners a).testBit b = true := by
  have small := ok.2.1
  apply everyMaskOn (onesOn small)
  intro n hn
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hn
  let x : Fin 11 := ⟨v,List.mem_range.mp hv⟩
  have abs : (absent.getD v 0).testBit b = !(b.testBit v) := by
    rw [← ac x,blockBitsAt]; simp [small,x]
  have part : (partners.getD v 0).testBit b = meets b (neighbor v) := by
    rw [← pc x,blockBitsAt]; simp [small,x]
  have covered (on : (a ||| b).testBit v = true) := belowBit ok.2.2.2 on
  cases ha : a.testBit v
  · simp only [Bool.false_eq_true,↓reduceIte]
    by_cases near : meets a (neighbor v) = true
    · simp only [near,↓reduceIte]; exact onesOn small
    · simp only [ite_eq_right near,abs,Bool.not_eq_true']
      by_contra! h
      have vb : b.testBit v = true := Bool.eq_true_of_not_eq_false h
      exact near (hasPartner x.isLt (ok.1.trans_lt small) ha (covered (by simp [Nat.testBit_or,vb])))
  · have dis := congrArg (fun m : ℕ => m.testBit v) ok.2.2.1
    have off : b.testBit v = false := by simpa [Nat.testBit_and,ha] using dis
    simp only [↓reduceIte,Nat.testBit_and,abs,off,Bool.not_false,Bool.true_and,part]
    have need := covered (by simp [Nat.testBit_or,ha])
    rw [sigSwap posRows a b] at need
    exact hasPartner x.isLt small off need


def unarySignature (rs : List ℕ) (a : ℕ) := codeMask rs.length fun i => meets a (rs.getD i 0)

lemma offCode {n i : ℕ} (f : ℕ → Bool) (off : n ≤ i) : (codeMask n f).testBit i = false :=
  Nat.testBit_lt_two_pow ((codeBound n f).trans_le (Nat.pow_le_pow_right (by decide) off))

lemma joinedSignature (rs : List ℕ) (a b : ℕ) :
    signature rs a b = unarySignature rs a &&& unarySignature rs b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < rs.length
  · simp only [signature,unarySignature,Nat.testBit_and,codeBit _ _ _ hi]
  · simp only [signature,unarySignature,Nat.testBit_and,offCode _ (Nat.le_of_not_gt hi),Bool.and_self]

lemma meetsUnion (x y r : ℕ) : meets (x ||| y) r = (meets x r || meets y r) := by
  apply Bool.eq_iff_iff.mpr
  simp only [meetsIff,Bool.or_eq_true,Nat.testBit_or]
  constructor
  · rintro ⟨i,h,hi⟩
    exact h.elim (fun h => Or.inl ⟨i,h,hi⟩) (fun h => Or.inr ⟨i,h,hi⟩)
  · rintro (⟨i,h,hi⟩ | ⟨i,h,hi⟩)
    · exact ⟨i,Or.inl h,hi⟩
    · exact ⟨i,Or.inr h,hi⟩

lemma unaryUnion (rs : List ℕ) (x y : ℕ) :
    unarySignature rs (x ||| y) = unarySignature rs x ||| unarySignature rs y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < rs.length
  · simp only [unarySignature,Nat.testBit_or,codeBit _ _ _ hi,meetsUnion]
  · simp only [unarySignature,Nat.testBit_or,offCode _ (Nat.le_of_not_gt hi),Bool.or_self]

lemma splitSix (a : ℕ) : (a%64) ||| ((a/64) <<< 6) = a := by
  rw [show a/64 = a >>> 6 by rw [Nat.shiftRight_eq_div_pow]]
  change (a%2^6) ||| ((a >>> 6) <<< 6) = a
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or,Nat.testBit_mod_two_pow,Nat.testBit_shiftLeft,Nat.testBit_shiftRight]
  by_cases lt : i < 6
  · simp [lt,Nat.not_le.mpr lt]
  · have ge : 6 ≤ i := by omega
    simp [lt,ge,show 6+(i-6)=i by omega]

def fromParts (l r : List ℕ) (a : ℕ) := l.getD (a%64) 0 ||| r.getD (a/64) 0

lemma partsCorrect (rs l r : List ℕ)
    (lo : ∀ i : Fin 64, unarySignature rs i.val = l.getD i.val 0)
    (hi : ∀ i : Fin 32, unarySignature rs (i.val <<< 6) = r.getD i.val 0)
    (a : ℕ) (small : a < 2048) : unarySignature rs a = fromParts l r a := by
  conv_lhs => rw [← splitSix a]
  rw [unaryUnion,lo ⟨a%64,by omega⟩,hi ⟨a/64,by omega⟩]
  rfl

def groupedAt {α : Type} (rows : List (List α)) (i : ℕ) (fallback : α) :=
  (rows.getD (i/32) []).getD (i%32) fallback

def listedCode (row : List ℕ) := row.foldr (fun w acc => (1 <<< (w%2048)) ||| acc) 0

lemma listedBit {row : List ℕ} {b : ℕ} (hi : (listedCode row).testBit b = true) :
    ∃ w ∈ row, w%2048 = b := by
  induction row with
  | nil => simp [listedCode] at hi
  | cons a row ih =>
    rw [listedCode,List.foldr_cons,Nat.testBit_or,Bool.or_eq_true] at hi
    rcases hi with h | h
    · refine ⟨a,by simp,?_⟩
      simpa [Nat.shiftLeft_eq,Nat.testBit_two_pow,eq_comm] using h
    · obtain ⟨w,hm,eq⟩ := ih h
      exact ⟨w,by simp [hm],eq⟩


def window (s : ℕ) (n : ℕ) (test : ℕ → Bool) : Bool :=
  match n with
  | 0 => true
  | k+1 => window s k test && test (s+k)

lemma windowIff (s n : ℕ) (test : ℕ → Bool) : window s n test = true ↔ ∀ i < n, test (s+i) = true := by
  induction n with
  | zero => simp [window]
  | succ n ih =>
    rw [window,Bool.and_eq_true,ih]
    constructor
    · rintro ⟨earlier,last⟩ i hi
      by_cases eq : i = n
      · exact eq ▸ last
      · exact earlier _ (by omega)
    · intro h
      exact ⟨fun _ hi => h _ (by omega),h n (by omega)⟩

lemma joinWindow {test : ℕ → Bool} {s n m : ℕ} (left : window s n test = true)
    (right : window (s+n) m test = true) : window s (n+m) test = true := by
  apply (windowIff _ _ _).2
  intro i hi
  by_cases before : i < n
  · exact (windowIff _ _ _).1 left i before
  · have on := (windowIff _ _ _).1 right (i-n) (by omega)
    rwa [show s+n+(i-n) = s+i by omega] at on

lemma windowIndex {n i : ℕ} {test : ℕ → Bool} (checked : window 0 n test = true) (hi : i < n) : test i = true :=
  Nat.zero_add i ▸ (windowIff _ _ _).1 checked i hi


def hc0 : List (ℕ) := [0x18000000001fff,0x600000000067ff,0x1800000000187ff,0x6000000000607ff,0x61d4c00000000c0,0x6601802d0000180,0x1018280000101da3,0x1030002aa8103710,0x1038282aa8101500,0x1063000000106277,0x1073002aa8102210,0x1120140888112530,0x1163140888102030,0x1180004440118706,0x11a0144cc8110500,0x18182b8000101422,0x18200000001827ff,0x183003aaa8183610,0x18382baaa8101400,0x1920178888192430,0x198003c440110602,0x19a017ccc8110400,0x2060004440206706,0x20c014088820c530,0x20e0144cc8204500,0x2183000000218277,0x21c3140888208030,0x246188ec50000000,0x2983281110208022,0x2e41008000000212,0x3063004440006206,0x3073006ee8000200]

def hc1 : List (ℕ) := [0x3183004440018206,0x31e3144cc8000000,0x358388e010000040,0x3800c00000380355,0x3820c02220382314,0x3830c3aaa8182210,0x4018c00000401b55,0x41840000004181f5,0x5018e80000001901,0x5038e82aa8000100,0x5184004440018104,0x6008038000600e32,0x6018c38000400a10,0x60441400006041b1,0x605cd78000000010,0x60800000006087ff,0x6088039998608e20,0x60c414088860c130,0x60d8c39998400a00,0x60e4144cc8204100,0x6187000000618075,0x61c7140888608030,0x626c054540000000,0x63857101e0000080,0x66808ce000000040,0x68002800006805a3,0x68082b8000600422,0x68443c00006841a1,0x6880281110688522,0x68882b9998608420,0x68c43c199868c120,0x6987281110608020]

def hc2 : List (ℕ) := [0x6a451c8680000080,0x6ae91c8690000000,0x7064144440204100,0x7187004440018004,0x73f4704560000000,0x7800e80000280101,0x7818eb8000000000,0x7844fc0000284101,0x7880e81110280100,0x78a0e83330280100,0x78c4fc1998284100,0x7c24ac7000000100,0x7edd8e7800000040,0x8062125280000008,0x8182b16180000008,0x9112a00100000008,0x9257410780000000,0x980222050000000a,0x9820a02d00000108,0xa183b16180000000,0xa654c10780000000,0xb063a12d00000000,0xb822e20700000000,0xbbf2a12580000000,0xe080b16180000008,0xe420b06000000108,0xe888b17000000000,0xf20b204540000000,0x10018300001001da9,0x1018000060101878c,0x102100080790216c0,0x10218308079001480]

def hc3 : List (ℕ) := [0x103000c80190304e0,0x103800c8619010480,0x1060280000106025d,0x10612808079020240,0x107028c8019020040,0x11018380001101da1,0x11020100281102598,0x11070102aa9103510,0x111100000011117ff,0x111183c0001111da1,0x11138382aa9111500,0x11170140a89113510,0x11190004641119704,0x111b0144ec9111500,0x111b83c6661111500,0x112000800511205c2,0x112201802d1100580,0x112631882d0000000,0x113000c80591304c0,0x113100880791314c0,0x11318388079111480,0x113631c8ad8000000,0x11602880051020040,0x11622982ad0000000,0x1166390aa80000010,0x11712888059020040,0x117928ce618000000,0x118000100011806ba,0x11820110281182498,0x11910038001191632,0x119183b8001111420,0x11930138a89193410]

def hc4 : List (ℕ) := [0x119383baaa9111400,0x1199003c641111600,0x119b017cec9111400,0x11a00090051100482,0x11a201902d1100480,0x11b183b8079111400,0x11ba01c8ad9110400,0x11bf818a279111400,0x11e028b0050000000,0x11e229b2ad0000000,0x12183000600018204,0x123830c8618000000,0x1264390ee80000000,0x1278380e600000200,0x12e01a0d500000000,0x12f74c05110000100,0x13063100280102010,0x13193004640018204,0x133e31c8e98000000,0x1360388e650000000,0x13800c10000180210,0x13910c38000180210,0x13e22ca0070000040,0x14018f00000001901,0x14184000600018184,0x141b4e83330000100,0x143840c8618000080,0x15118f80000001901,0x15138f82aa8000100,0x15194004640018104,0x15220f822f0000100,0x153b4144cc8000100]

def hc5 : List (ℕ) := [0x16047140680000000,0x160c0f10000000000,0x16187000600018004,0x161c7140e88000000,0x16244450068000080,0x162810c8600000080,0x16280700060000180,0x163870c8618000000,0x168473c0780000000,0x169b7283330000000,0x16b85280700000080,0x170671446c0000000,0x17197004640018004,0x17898f90000000000,0x178a0f922a0000000,0x17a20c90070000000,0x17b78f08078000000,0x17b940cc650000000,0x17be71c8680000000,0x17ff48ca600000000,0x18018327801001408,0x18100021801810668,0x18180021e01010608,0x182000000018207ff,0x1821002f879821640,0x1821832f879001400,0x183000e9819830460,0x183800e9e19010400,0x18903281510000002,0x1900000500190074a,0x19020105281100508,0x19063125280000000]

def hc6 : List (ℕ) := [0x19110025801911648,0x191183a7801111400,0x19190025e41111600,0x191b83a7a21111400,0x19200085051920542,0x192201852d1100500,0x192631ad2d0000000,0x193000ed859930440,0x193100af879931440,0x19373121a88000000,0x193900cc659111400,0x1980001500110060a,0x19820115281100408,0x1991003d801111600,0x1999003de41111600,0x199b0125a89111400,0x19a00095051100402,0x19a201952d1100400,0x19b100b8059111400,0x19b183af801111400,0x19b900fc659111400,0x19ba01edad9110400,0x19bb81ae221111400,0x1a0e0a16d40000000,0x1a183021e00000200,0x1a3830e9e18000000,0x1a670c38050000200,0x1a9b3205550000002,0x1aa41008400000282,0x1af93209518000000,0x1b193025640000200,0x1b1f2121e88000000]

def hc7 : List (ℕ) := [0x1b20308c650000000,0x1b79300c458000200,0x1b910c17000000200,0x1b930d172a0000000,0x1bb10c97070000000,0x1be75427a20000000,0x1c018f27800000000,0x1c238e2f878000000,0x1d224b06540000100,0x1d538ea7800000000,0x1d620f87000000100,0x1e080f16180000000,0x1e200c06000000300,0x1e2c0f10060000000,0x1e7fc945550000100,0x1faf8f10070000000,0x1fea0d97000000000,0x1fef8f3f800000000,0x1ff38daf800000000,0x1ff5cb5e800000000,0x2001a800002001a5d,0x201a2bc4000000000,0x2040800807a040ec0,0x2041a80807a000a40,0x206003000020605a9,0x2060830807a040480,0x20620b82ad0000100,0x20c022a0050000002,0x20e023b0050000000,0x2101aa80000001801,0x21122bc2888000000,0x21424445028000140]

def hc8 : List (ℕ) := [0x2162c640528000180,0x21715400100000080,0x21d828ce018000040,0x23f75616780000000,0x2401ac00002401a55,0x24080021802408668,0x24184021800408060,0x244004000624403c4,0x2440840807a440ac0,0x24600700062040180,0x2460870807a040080,0x2501ae80000001801,0x2600202000260027a,0x2600a038002600a32,0x2601ac38002400a10,0x2605ed78000000010,0x26082021802608268,0x2608a03999a608a20,0x26187021800608060,0x26402420062400240,0x26446560028000010,0x26480421862400240,0x265cd421820000040,0x26680730060000000,0x268022a0000600022,0x2680a2b8000600022,0x26846160000600030,0x2684c178000600030,0x2688a2a1910608020,0x268cc179998608020,0x269872a1910608020,0x269c6141888608020]

def hc9 : List (ℕ) := [0x269cf039998608020,0x26ec8238018000000,0x27795605560000000,0x27802aa0000000000,0x2781aeb8000000000,0x27c1aab8078000000,0x2801a810782000a08,0x284000000028407ff,0x284080187fa840e80,0x2841a8187fa000a00,0x28c022a0500000002,0x28c882987f8000000,0x29420a80000000100,0x29822aa0500000000,0x29c028a0050000040,0x29c20882850000140,0x29da2bd6000000000,0x29dbaa907e0000000,0x2ae80ace018000000,0x2bfe09ca8c8000000,0x2c000000602c0078c,0x2c080021e02400608,0x2c400400662c40384,0x2c4084187fac40a80,0x2c41ac187fa400a00,0x2c66c544028000100,0x2c6ac665820000000,0x2d402e80700000000,0x2e002020602400208,0x2e07ed78500000000,0x2e082021e02400208,0x2e08a038782400a00]

def hc10 : List (ℕ) := [0x2e25dcd0780000000,0x2e402420662400200,0x2e480421e62400200,0x2e49a43801a400a00,0x2e88a2a0700000000,0x2efc65408e8000000,0x2fa46fe0780000000,0x2fa9aea0700000000,0x2fea0e82f20000100,0x2feaa6a0070000000,0x2fef8ca1f18000000,0x3001ab00000001809,0x30602b00000060009,0x3111ab80000001801,0x311babc6400000000,0x31622b82ad0000000,0x31702b80010000000,0x317a2bce618000000,0x3191aab0000000000,0x31d3aabaa88000000,0x31fb28fe640000000,0x33ffa1ce660000000,0x3401af00000001801,0x34602f00060000000,0x3511af80000001801,0x35122b82a80000000,0x3513aa82aa8000000,0x35600e80070000100,0x356a0e82a70000100,0x36098f30000000000,0x36602c30060000200,0x37766645528000000]

def hc11 : List (ℕ) := [0x37898eb1990000000,0x378dcf60000000000,0x37918fb0000000000,0x37938ffaaa8000000,0x3797cf50000000000,0x37cb8ebaaa8000000,0x37ef8e319e0000000,0x37f7abb0050000000,0x380040000038001f5,0x38104021801800060,0x382040c00038201e1,0x382471e8280000000,0x383040e9819820060,0x384054000038400d5,0x38446160280000010,0x38505421801800040,0x39004005001800140,0x39024145280000100,0x39114025801800040,0x392040c5051820140,0x39266165280000000,0x393140ed859820040,0x39405405001800040,0x394255452a8000000,0x39515425801800040,0x39774161888000000,0x39e276a0500000000,0x39ffcffe220000000,0x3b476465028000040,0x3c004000602800184,0x3c174e02900000100,0x3c184021e00000000]

def hc12 : List (ℕ) := [0x3c2040c0602800180,0x3c264640528000180,0x3c405400662840084,0x3d004005640000100,0x3d224044240000100,0x3d405405460000000,0x3d7b4145448000000,0x3e007020600000000,0x3e187021e00000000,0x3e2070e8600000000,0x3e38d0e9e18000000,0x3e3c6161e88000000,0x3e407420660000000,0x3e446160680000000,0x3e5c5421e60000000,0x3e746770028000000,0x3ea4f2a0500000000,0x3eace1e0680000000,0x3ee4c038780000000,0x3eefe578018000000,0x3efaf6a0720000000,0x3efb4ea3b30000000,0x3efd7281f10000000,0x3effcd05310000000,0x3f594025440000000,0x3f7ee165440000000,0x3f7f7144cc8000000,0x3fec67e0078000000,0x3ffce039790000000,0x4001b000004001a77,0x40048002aac004f10,0x4005b002aac000a10]

def hc13 : List (ℕ) := [0x400602800040065a3,0x40068282aac004500,0x402613882d0000080,0x4026c4d0528000080,0x4081b005554000a02,0x4101b280000001823,0x41063280000006023,0x4107b282aa8000000,0x411633c0888000020,0x418040000041801f5,0x418241400041821b1,0x41924178888182030,0x42008006664200f04,0x4201b006664000a04,0x42060284444206502,0x420803c00042085a1,0x420883c6664200500,0x420c03c088c20c520,0x420e8284ccc204500,0x421833c0000208021,0x421c33c0888208020,0x42642420020000250,0x42808007774280f00,0x4281b007774000a00,0x428400000042847ff,0x42848006eec284f00,0x4285b006eec000a00,0x428803c1114288520,0x428c03c199c28c520,0x428c83c7774284500,0x429c33c1998208020,0x42d832c1110208020]

def hc14 : List (ℕ) := [0x42e420a0050000042,0x43063284440006002,0x431833c4440000000,0x4361f4d0500000000,0x43824d42224382110,0x43844c00004384155,0x44040c02224404314,0x44060e82224004100,0x44080038004408632,0x440e0ebb330000000,0x44184038000408030,0x441c4c3a220000010,0x44800004444480706,0x44840c06664484304,0x4488003c444400602,0x448c0c3a224400210,0x450e3ebb330000000,0x45804004444080104,0x45824144444080100,0x45844c06664084104,0x4598403c440000000,0x45b857381e0000000,0x46a6c4d0060000080,0x46a80790060000080,0x47860e82220280100,0x47c1e4e5000000040,0x47de49ce800000000,0x47ffe4e7a80000000,0x47ffd6901e0000000,0x47ffd650780000080,0x48002320000000028,0x4806a325280000000]

def hc15 : List (ℕ) := [0x49b74310180000000,0x4a002320600000008,0x4a0e21256c0000000,0x4a802220500000008,0x4a842120280000018,0x4bb50238580000000,0x4c008326000000008,0x4c60c0c6000000140,0x4de2a027d50000000,0x4e8c8b26100000000,0x4f846b20500000000,0x4fbd6b16180000000,0x4fbfd650528000000,0x4fcea321e00000000,0x4fdc68ce010000040,0x4fe2eb42d00000000,0x4fe65608500000080,0x4ffcc817190000000,0x4fffeb505c8000000,0x5001b300000001821,0x5021b308078000000,0x50753108898000000,0x5081b305550000000,0x5111b380000001821,0x51263388050000000,0x5131b388058000000,0x513633c8ad8000000,0x518040100001800b0,0x51824150280182090,0x51914038000180030,0x51a241d02d0000080,0x51b140d0050000080]

def hc16 : List (ℕ) := [0x521833c0600000000,0x522c4fd0180000000,0x52754850008000010,0x52803200500000002,0x52a41100200000090,0x5307b380280000000,0x531833c4640000000,0x531f3100e88000000,0x533e13c8618000080,0x533fb18a278000000,0x53820d122a0182010,0x53844c10000180010,0x53930138a88182010,0x53954c38000180010,0x53a04cd0070000000,0x53a44cd0078000000,0x53b341d02d0000000,0x53bc12c8618000000,0x53e46ce0060000040,0x53ee66e1020000000,0x53f708b8058000000,0x53ff280aad8000000,0x54044c12620000000,0x55060f822a0000100,0x559d4038600000000,0x55a64014640000000,0x55ae1f0a2e0000000,0x56964e00100000100,0x57fec8f7d00000000,0x58203300000000020,0x586060e0000000060,0x58b431e1800000020]

def hc17 : List (ℕ) := [0x58c063e0550000000,0x592633a5280000000,0x5976e7e1800000000,0x5991b227800000000,0x59b1b30d058000000,0x5a003020600000200,0x5a243120280000010,0x5a25910aaf8000000,0x5a843220500000002,0x5a983281600000000,0x5a9c3141e88000000,0x5aa41308400000080,0x5aa40410020000290,0x5abf930c658000000,0x5b0631256c0000000,0x5b2e118c650000000,0x5b5e33e5440000000,0x5b7fb3a5288000000,0x5b9fb227a20000000,0x5ba26e22d00000000,0x5bbfb1a1e08000000,0x5bdfd6e5a20000000,0x5c042f262a0000000,0x5c1f4ebb330000000,0x5c405fc6000000000,0x5cac1738180000000,0x5cacab3c1c0000000,0x5d01bf27800000000,0x5d4fae27220000000,0x5d6248c6400000100,0x5d6833a5000000000,0x5d77bfa7aa8000000]

def hc18 : List (ℕ) := [0x5dae3f26040000000,0x5dd196e7000000000,0x5dedbf27810000000,0x5df7b667850000000,0x5ede67e0220000000,0x5f103324000000000,0x5fafbf29170000000,0x5fce4b56000000000,0x5fe2e8e0050000040,0x5fe66c20220000000,0x6001b800006001a55,0x60040802806004358,0x604010080060402f2,0x6040900807e040ac0,0x6041b80807e000a40,0x6044180a806000250,0x6046188a850000040,0x606013080020400a0,0x6060930807a040080,0x60641b0aa80000000,0x60649b0aaf8000000,0x60661b8aad0000000,0x6080000500608074a,0x60c0100d006000242,0x60e0130d500000000,0x6101ba80000001801,0x61804005004080140,0x61c2540d000000040,0x6200080600620034c,0x62008806666200b04,0x6201b806666000a04,0x62040806806204348]

def hc19 : List (ℕ) := [0x62048806eee204b00,0x62060a82804204100,0x62080bc6004200100,0x62088bc6664200100,0x62183bc6000000000,0x621c3bc6888000000,0x6240180e006000240,0x6241980e67e000a00,0x6244180e806000240,0x62800807006280348,0x62808807776280b00,0x62840807806284348,0x62848807ffe284b00,0x62880bc7114280100,0x628e8a8688c284100,0x62c0180f006000240,0x62c4180f806000240,0x6356388a850000040,0x63804c07004280140,0x63844c07804284140,0x63864145004280100,0x638e4fc1114284100,0x638e8947334284100,0x63c45c0f000000040,0x63ee8b0e678000000,0x63f7570d500000000,0x64008000006400fff,0x6401bc00006401a55,0x64048802a26404b10,0x6405b802aae400a10,0x64068a82a24004100,0x64088039806408e20]

def hc20 : List (ℕ) := [0x6418c039800408020,0x644014080664402c0,0x6440940807e440ac0,0x6441ac0807e400a40,0x64441c0aa66400200,0x64609708062040080,0x64808005446480f02,0x6481b805556400a00,0x64848c07e66484b00,0x64c0900d466400a00,0x64c41c0fe66400200,0x64c81439866400200,0x64e897399e0000000,0x6501be80000001801,0x6582c145444080100,0x667cd7319e0000000,0x66fcf6a1860000000,0x6784c005444284100,0x67862a82800000000,0x678e8ea1910000000,0x67c2d00d440000000,0x67fed735560000000,0x680000100068006ba,0x68040812806000218,0x68060a12d00000008,0x684010180068402b2,0x684090187fe840a80,0x6844181a806000210,0x6844980aafe000a00,0x6845b8082fe000a00,0x68461a9ad50000000,0x68543bca898000000]

def hc21 : List (ℕ) := [0x6880001500600060a,0x68c0101d006000202,0x69102a90100000000,0x69162b52988000000,0x69403a98550000000,0x69d229d8088000000,0x6a000816006000208,0x6a0088167e6000a00,0x6a01b810786000a00,0x6a040816806000208,0x6a048816fee000a00,0x6a05b802eae000a00,0x6a060a96d40000000,0x6a080bd6180000000,0x6a088bd67e0000000,0x6a0e0b56988000000,0x6a40181e006000200,0x6a44181e806000200,0x6a800817006000208,0x6a81b807776000a00,0x6a840817806000208,0x6a8488177f6000a00,0x6a9c8b85110000000,0x6ac0181f006000200,0x6ac0900c77e000a00,0x6ac4181f806000200,0x6ac5980eefe000a00,0x6ae7f4147c0000000,0x6b563a92d00000000,0x6b61ba86440000000,0x6bbe3b56180000000,0x6bdc19ce018000000]

def hc22 : List (ℕ) := [0x6bfe9a8e810000000,0x6bff9a907e0000000,0x6c000010606c00688,0x6c008010786c00e88,0x6c040c12e26400200,0x6c401418666c40280,0x6c4094187fec40a80,0x6c459c082fe400a00,0x6c6e828aa70000000,0x6c808015646400e00,0x6c81b8157d6400a00,0x6c840c17e66400200,0x6c848812fae400a00,0x6c888039c06400e00,0x6cb7b8557d0000000,0x6cc0141d666400200,0x6cc41c1ae66400200,0x6ccc0439a26400200,0x6ccc84191be400a00,0x6ccd9c0919e400a00,0x6cf8d039800000000,0x6d463e9af70000000,0x6d49aa98770000000,0x6d625e00500000000,0x6db1a890700000000,0x6defbcb9b10000000,0x6dff433a1c0000000,0x6e05ac10786400a00,0x6ec5b80456e400a00,0x6effddb13d0000000,0x6f2e8292f20000000,0x6f35edd0180000000]

def hc23 : List (ℕ) := [0x6f7ff4d2528000000,0x6f97aa92fa8000000,0x6fd7ae987f8000000,0x6ff7aa78580000000,0x6ffe4a4f008000000,0x7001bb00000001801,0x7005b302a80000000,0x70643b08000000000,0x707033c8018000020,0x70f1b2c1110000000,0x7111bb80000001801,0x7117b3c0888000000,0x71763b82a80000000,0x72843b04400000000,0x729fb303710000000,0x72ba7fc3330000000,0x72e41b0c400000000,0x72ff99c6618000000,0x7301b204600000000,0x7319b3c6400000000,0x731e3384c80000000,0x737fb206ee8000000,0x737f998e450000000,0x7401bf00000001801,0x7405bb022a0000000,0x74843f04540000000,0x75063f82aa0000000,0x7511bf80000001801,0x7517ba82aa8000000,0x754dbe39100000000,0x75669e0aa60000000,0x75703a08040000000]

def hc24 : List (ℕ) := [0x7577aa8aad8000000,0x75e2930c560000000,0x7693ad05500000000,0x76e27e40500000000,0x76f5ba05550000000,0x7775aa08078000000,0x778fabb2280000000,0x77ef9b099c0000000,0x780040100028000b0,0x78104039800000020,0x782040d00028000a0,0x78244c12800000010,0x783040f8018000020,0x78344c3b800000000,0x78405418002840090,0x78f35081110000000,0x79804015000000000,0x79824155280000000,0x79a040d5050000000,0x7a004c16000000000,0x7a044c16800000000,0x7a064e92d00000000,0x7a244cd6060000000,0x7a2c4fd6180000000,0x7a445c1a000000010,0x7a4edfde198000000,0x7a774e89110000000,0x7aa8c4167e0000000,0x7b804c17000000000,0x7b82cc172a0000000,0x7b954c17800000000,0x7bb54cd7070000000]

def hc25 : List (ℕ) := [0x7bd55419000000000,0x7bf3403d800000000,0x7c004010602800080,0x7c00c010782800080,0x7c044c12e20000000,0x7c20c0d0602800080,0x7c24cc12628000000,0x7c3840e8618000000,0x7c405418662840080,0x7c40d4187fa840080,0x7c445c1ae60000000,0x7c78c039e00000000,0x7c7f4c3ba00000000,0x7d804015640000000,0x7d82c0156c0000000,0x7d98403dc40000000,0x7da44c17e60000000,0x7dbac07c648000000,0x7dc2541d220000000,0x7ddb417ccc8000000,0x7ddd4039c20000000,0x7dff40fa618000000,0x7e26ce10520000000,0x7e44dc1a7f8000000,0x7e56de82d50000000,0x7efbed4d558000000,0x7efecc2bb30000000,0x7effdd66540000000,0x7faecfd1190000000,0x7faec350940000000,0x7fb2c054250000000,0x7fb940ed650000000]

def hc26 : List (ℕ) := [0x7fbccc16fe8000000,0x7fc6dc0f220000000,0x7fdec01d4c8000000,0x7fef4ec9118000000]

def hc : List (List (ℕ)) := [hc0,hc1,hc2,hc3,hc4,hc5,hc6,hc7,hc8,hc9,hc10,hc11,hc12,hc13,hc14,hc15,hc16,hc17,hc18,hc19,hc20,hc21,hc22,hc23,hc24,hc25,hc26]

def hCount : ℕ := 836

def hullAt (i : ℕ) := decodeHull (groupedAt hc i 0)


def absTable : List ℕ := [0x55555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555,0x33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff]

def meetTable : List ℕ := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ffffffffffffffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffccccffffffffffffcccc,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaaffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa,0xfffffffffffffffffffffafafffffafafffffffffffffffffffffafafffffafafffffffffffffffffffffafafffffafafffffffffffffffffffffafafffffafafffffffffffffffffffffafafffffafafffffffffffffffffffffafafffffafafffffffffffffffffffffafafffffafafffffffffffffffffffffafafffffafafffffffffffffffffffffafafffffafafffffffffffffffffffffafafffffafafffffffffffffffffffffafafffffafafffffffffffffffffffffafafffffafafffffffffffffffffffffafafffffafafffffffffffffffffffffafafffffafafffffffffffffffffffffafafffffafafffffffffffffffffffffafafffffafa]

lemma absVerified : ∀ v : Fin 11, blockBits 11 0 (fun b => !(b.testBit v.val)) = absTable.getD v.val 0 := by decide +kernel

lemma meetVerified : ∀ v : Fin 11, blockBits 11 0 (fun b => meets b (neighbor v.val)) = meetTable.getD v.val 0 := by decide +kernel

def pSmall : List ℕ := [0,3,12,15,48,51,60,63,192,195,204,207,240,243,252,255,772,775,780,783,820,823,828,831,964,967,972,975,1012,1015,1020,1023,3088,3091,3100,3103,3120,3123,3132,3135,3280,3283,3292,3295,3312,3315,3324,3327,3860,3863,3868,3871,3892,3895,3900,3903,4052,4055,4060,4063,4084,4087,4092,4095]

def pLarge : List ℕ := [0,12352,20608,28864,34056,46408,54664,62920,51201,63553,55425,63681,52489,64841,56713,64969,8738,12898,29346,29410,42794,46954,63402,63466,59939,64099,64163,64227,61227,65387,65451,65515]

lemma pParts {a : ℕ} (h : a < 2048) : unarySignature posRows a = fromParts pSmall pLarge a :=

  partsCorrect _ _ _ (by decide +kernel) (by decide +kernel) a h

def nSmall : List ℕ := [0,32767,10126677,10158079,521011,524287,10483575,10485759,11112463,11141119,12293471,12320767,11531071,11534335,12580735,12582911,330410,360447,10457087,10485759,523195,524287,10485759,10485759,11377327,11403263,12558335,12582911,11533247,11534335,12582911,12582911,1576140,1605631,10128861,10158079,2097151,2097151,10485759,10485759,12164303,12189695,12295647,12320767,12582911,12582911,12582911,12582911,1904366,1933311,10457087,10485759,2097151,2097151,10485759,10485759,12426991,12451839,12558335,12582911,12582911,12582911,12582911,12582911]

def nLarge : List ℕ := [0,401648,5263104,5664752,6320128,6713584,7372544,7766000,8880128,8888560,14143232,14151664,15200256,15200496,16252672,16252912,16252928,16654576,16273152,16674800,16281600,16675056,16285440,16678896,16744448,16752880,16764672,16773104,16773120,16773360,16776960,16777200]

lemma nParts {a : ℕ} (h : a < 2048) : unarySignature negRows a = fromParts nSmall nLarge a :=

  partsCorrect _ _ _ (by decide +kernel) (by decide +kernel) a h


def rc0 : List (List ℕ) := [[0],[512,1024,1536],[2064,2304,2320],[1339920,580352,111376,293904,1076480,294160,488976,96000,489232],[4128,5120,5152],[225824,214016,222240,216576,226848],[149552,948512,936240,1104912,314416,1076480,1105168,941344,1162544],[225840,723744,488240,293904,314416,1076480,294160,1099040,1162544,488976,226864,730880,489232,778016,489264],[6208,6272,6336],[1649216,998016,998080,527424,771200,527552,9792,9856,9920],[229456,620688,10448,1057088,10576,1210752,1212816,59840,10704],[111184,488080,488144,824128,111440,156544,488336,156608,488400,293968,294032,294096,173376,294224,1639808,294288,173504,294352,489040,489104,489168,657216,489296,157568,489360,157632,489424],[340064,567456,571616,527424,113760,752768,570528,527552,1342688],[1628768,643744,643808,527424,140384,771200,836768,527552,595168,978496,976480,1183360,1158816,978624,976608],[489584,712880,712944,485728,489840,1477024,1458608,733664,733680,984144,975984,1604752,830640,1502416,830704,984384,984400,1496416,976240,1639808,1627536,570784,1664432,1664448,1496528,1342944,976368],[488048,488112,488176,777056,134000,156576,488368,156640,488432,293968,140400,294032,830640,294096,830704,984384,294224,140640,140656,1639808,294288,1664416,1664432,531904,294352,1496544,835056,489040,489072,478864,489136,489168,489200,978752,489296,778080,489328,499584,489360,778144,489392,499648,489424,778208,489456],[33024,33026,33792,33794,34048,34050],[16898,31488,37634,214016,15362,257280,36098,13824,17922,32512,38658],[901376,929024],[580352,1076480,724736],[28706,41248,43298,214016,23554,27680,29730,257280,40194,42272,44322],[225826,439072,439074,214016,220162,222240,224290,257280,261378,265504,267554,216576,218626,226848,226850,259840,263938,440096,440098],[948512,1076480,1099040],[723744,1076480,1099040,730880,778016],[524354,522370,524482,450880,1016130,1227136,1235330,59840,1016258,527424,525378,767104,523394,527552,525506,1017152,1017154,1236352,1236354,1017280,1017282],[524866,643714,524994,824128,977730,1483648,1158018,824256,977858,527424,977986,771200,470146,527552,470210,994624,978242,1639808,470402,531904,470466,978496,978498,1183360,1158786,978624,978626,978752,978754,1183616,1159042,978880,978882],[450880,1278336,59840,1017152,1293696,1017280],[824128,156544,156608,984384,1639808,495040,978752,157568,157632],[139362,798882,643298,1165664,1007970,1333664,1677730,1335776,1354210,527424,984130,140384,140386,771200,773250,836768,799906,527552,773314,595168,799970,984384,984386,961888,1008994,1639808,1641858,1680800,1678754,1297856,1297858,1355232,1355234],[1503842,643746,643810,439136,439138,1158048,1158050,975840,975842,527424,977986,140384,140386,771200,773250,836768,799906,527552,531650,595168,799970,984384,978242,1496416,978274,1639808,1641858,1680800,1678754,531904,531906,1496544,978402,978496,978498,976480,976482,1183360,1158786,1158816,1158818,978624,978626,976608,976610,978752,978754,440160,440162,1183616,1159042,1159072,1159074,978880,978882,976864,976866],[1102176,1477024,494048,984384,1496416,1639808,1680800,531904,1355232],[777056,156576,156640,984384,1496416,1639808,1680800,531904,1496544,978752,778080,499584,778144,499648,778208]]

def rc1 : List (List ℕ) := [[96512,96516,96768,96772,97024,97028],[1298944,98820,88832,99076,103428,91392,103684,79360,103940,91904,104196],[901376,47364,45328,49428,135696,104980,92928,101124,135952,105236],[1339920,1708564,580352,584452,111376,1708820,326676,1076480,103684,294160,488724,488976,488980,96000,104196,489232,489236],[306432,318976,726784],[306432,318976,726784],[1076480,294160,488976,730880,489232],[1076480,294160,488976,730880,489232],[198724,114820,114884,450880,338244,1257856,115076,59840,115140,787008,315972,998016,115332,998080,115396,338752,338756,115584,115588,115648,115652],[1649216,1661508,998016,1018500,998080,1018564,824128,807748,156544,156548,156608,156612,676932,156804,156868,173376,677188,1639808,157060,173504,157124,656960,677444,157312,157316,157376,157380,657216,677700,157568,157572,157632,157636],[274516,628884,628948,450880,133444,1145168,133460,1261952,1440132,55696,629140,59840,1542596,1552848,629204,795216,326228,1174160,971412,1174224,367316,131904,133956,133968,133972,971648,971652,971664,971668,367552,367556,367568,367572],[111184,1673812,488080,488084,488144,488148,824128,133956,111440,133972,156544,156548,488336,488340,156608,156612,488400,488404,326740,488596,367828,173376,677188,294224,488788,1639808,157060,294288,488852,173504,157124,294352,368084,489040,489044,489104,489108,489168,489172,657216,677700,489296,489300,157568,157572,489360,489364,157632,157636,489424,489428],[994624,1639808,531904,349760,478848,978624,350016,497536,368576],[994624,1639808,531904,978496,478848,978624,978752,497536,497600],[994624,294224,1639808,294288,531904,294352,489040,478864,489168,978752,489296,499584,489360,368576,368592],[994624,294224,1639808,294288,531904,294352,489040,478864,489168,978752,489296,499584,489360,499648,489424],[901376,73986,123140,149766,932354,150022,117504,967426,123652,150278,148484,150534,72960,75010,148740,150790,83456,968194,148996,151046,143104,968450,149252,151302],[84482,731654,119552,731906,125700,731910,721924,732166,306432,77058,722180,732422,83456,85506,722436,732678,145152,732930,722692,732934],[901376,909572,121600,127748,929024,152836,147200,153348],[580352,584452,1076480,724228,724736,724740],[306432,1074434,318976,321026,726784,728834],[306432,1074434,318976,321026,726784,728834],[1076480,730880],[1076480,730880],[366662,1515654,366790,450880,1016130,1083716,366918,1276288,1706370,627076,1515910,59840,1016258,627140,367046,789058,367174,154242,1516166,1174210,367302,348992,367426,348996,367430,154496,154498,1516420,1516422,367552,367554,367556,367558,1084484,367686,1516676,1516678,367812,367814,1017152,1017154,1084740,367942,1293696,1707394,1516932,1516934,1017280,1017282,368068,368070,1490496,1490498,1711684,368198,155264,155266,1517188,1517190,1175232,1175234,368324,368326,1017664,368450,1711940,368454,155520,155522,1517444,1517446,368576,368578,368580,368582],[1503810,676422,477826,643718,643778,643782,824128,977730,592708,676678,156544,732034,156548,732038,156608,977858,156612,676806,676932,367686,156804,732294,156868,367814,994624,978242,677188,367942,1639808,470402,157060,732550,531904,470466,157124,368070,978496,978498,677444,677446,157312,478850,157316,732806,157376,978626,157380,677574,978752,978754,677700,677702,157568,733058,157572,733062,157632,978882,157636,677830],[450880,133444,1278336,1440132,59840,1442244,131904,133956,971648,971652,367552,367556,1017152,1084740,1293696,972164,1017280,368068,1017664,1711940,972672,972676,368576,368580],[824128,133956,156544,156548,156608,156612,994624,677188,1639808,157060,495040,157124,978752,677700,157568,157572,157632,157636],[994624,978242,1639808,1641858,531904,531906,978496,978498,478848,478850,978624,978626,978752,368450,497536,497538,368576,368578],[994624,978242,1639808,1641858,531904,531906,978496,978498,478848,478850,978624,978626,978752,978754,497536,497538,497600,497602],[994624,1639808,531904,978752,499584,368576],[994624,1639808,531904,978752,499584,499648]]

def rc2 : List (List ℕ) := [[374912,374920,214016,375816,375936,375944],[195080,369280,379528,214016,193544,394368,377992,189952,196104,370304,380552],[168080,788632,1138952,788760,1358208,1139080,1360272,788888,1104912,789528,783504,789656,1072384,1053960,1105168,789784,1596800,1140104,783760,789912],[524824,488080,473752,592648,111384,498560,490376,488336,488344,293904,293912,783504,474264,1076480,447752,294160,294168,1635712,447880,447888,447896,488976,362008,489104,474776,724736,362248,489232,362264,495488,491400,489360,489368],[372896,383144,214016,197640,191520,199720,371840,382088,373920,384168],[277032,400032,438952,214016,236552,222240,414760,394368,410760,398496,414888,216576,239112,226848,278056,396928,433800,401056,439976],[671920,671928,366888,366904,1477024,1663400,1503664,676280,1104912,1627160,314416,367672,783504,1627288,830640,830648,1076480,1053960,1105168,1627416,1099040,367912,1162544,367928,1600896,1600904,783760,1627544,1664416,1664424,1162672,1664440],[277048,400048,438968,277288,277304,494496,490408,488368,488376,293904,293912,314416,367672,478352,1627288,830640,830648,1076480,1053960,294160,294168,1099040,367912,1162544,367928,1635712,1637768,783760,1627544,1664416,1664424,1162672,1664440,488976,362008,226864,278072,478864,489112,401072,439992,730880,362248,489232,362264,778016,278312,489264,278328,499584,499592,489360,489368,778144,778152,489392,489400],[604288,748672],[998016,771200,1183360],[614544,1366400,1372560,1688720,1623424,1688976],[488080,498560,488336,478352,1639808,447888,478864,495488,489360],[659616,752768,816288],[643744,771200,836768,1183360,1158816],[671920,1477024,1458608,1604752,830640,1639808,1627536,816544,1664432],[488112,494496,488368,478352,830640,1639808,1627536,1664416,1664432,478864,489136,499584,489360,778144,489392],[389250,403594,268552,270602,416128,418178,426376,428426,214016,209922,228360,230410,388224,390274,402568,404618,253184,255234,269576,271626,417152,419202,427400,429450],[277002,400002,438922,273160,277258,433024,439170,433032,439178,214016,211970,236552,277514,394368,425090,410760,439434,257280,261378,431368,277770,421248,425346,431496,439690,208384,218626,239112,278026,396928,401026,433800,439946,259840,263938,274184,278282,434048,440194,434056,440202],[962824,1417600,1139080,1072384,1080584,1635712,1637768],[592648,498560,490376,1076480,1090824,1635712,1637768,724736,362248,495488,491400],[424098,436394,434472,274730,422304,424354,434600,436650,214016,220162,234504,275466,222240,224290,414760,275498,394368,425090,408712,437386,398496,425122,414888,437418,257280,261378,431368,275722,265504,267554,435496,275754,421248,425346,431496,437642,423328,425378,435624,437674],[277034,400034,438954,277288,277290,439200,439202,439208,439210,214016,220162,236552,277514,222240,224290,414760,277546,394368,425090,410760,439434,398496,425122,414888,439466,257280,261378,431368,277770,265504,267554,435496,277802,421248,425346,431496,439690,423328,425378,435624,439722,216576,218626,239112,278026,226848,226850,278056,278058,396928,401026,433800,439946,401056,401058,439976,439978,259840,263938,274184,278282,440096,440098,278312,278314,434048,440194,434056,440202,440224,440226,440232,440234],[366888,1477024,1681832,1076480,1090824,1099040,367912,1635712,1637768,1680800,1682856],[277288,494496,490408,1076480,1090824,1099040,367912,1635712,1637768,1680800,1682856,730880,362248,778016,278312,499584,499592,778144,778152],[641154,1378688,1675650,767104,769154,1639808,1676674],[641666,1483648,1158018,771200,470146,1639808,470402,1183360,1158786,1183616,1159042],[1427840,1639808],[498560,1639808,495488],[798882,1477024,1677730,771200,773250,836768,799906,1639808,1641858,1680800,1678754],[643746,1158048,1158050,771200,773250,836768,799906,1639808,1641858,1680800,1678754,1183360,1158786,1158816,1158818,1183616,1159042,1159072,1159074],[1477024,1639808,1680800],[494496,1639808,1680800,499584,778144]]

def rc3 : List (List ℕ) := [[180356,485516,1138952,340236,1388928,180612,483720,485772,340488,340492,182912,180868,483976,486028,340744,340748,183168,181124,484232,486284,330756,341004,482436,486540,304384,331012,1139976,341260,484736,482692,484744,486796,310784,331268,341512,341516,484992,482948,485000,487052,331520,331524,341768,341772,485248,483204,485256,487308],[545288,592396,995968,184964,473736,490124,592648,592652,185216,185220,490376,490380,715780,490508,494724,490636,306432,716036,447752,490764,464256,494980,447880,490892,310784,716292,361992,491020,472704,495236,474760,491148,716544,716548,362248,491276,495488,495492,491400,491404],[440468,1697948,336136,1698060,110872,139548,1395072,1407364,1139080,485772,440720,440724,1683864,1698204,641560,139804,182928,1194644,475800,1698460,336648,1698572,111384,140060,1194880,1194884,486280,486284,1194896,1194900,1684376,1698716,326676,326684,441492,1698972,1072384,331012,337160,486668,1105168,1699092,1684760,1699100,1615232,1195396,1140104,486796,441744,441748,1684888,1699228,1105424,327188,790040,327196,476816,1195668,476824,1699484,331520,331524,337672,487180,730896,1699604,1685272,1699612,1195904,1195908,487304,487308,1195920,1195924,1685400,1699740],[641560,643612,488080,488084,473752,488092,592648,592652,111384,1698588,498560,1002372,490376,490380,488336,488340,488344,488348,326676,326684,488596,488604,1076480,724228,447752,490764,294160,488724,294168,488732,1635712,494980,447880,490892,447888,488852,447896,488860,488976,488980,362008,488988,489104,489108,474776,489116,724736,724740,362248,491276,489232,489236,362264,489244,495488,495492,491400,491404,489360,489364,489368,489372],[306432,1090824,464256,468360,318976,361992,478848,497288,726784,362248,497536,497544],[306432,1090824,464256,468360,318976,361992,478848,497288,726784,362248,497536,497544],[1076480,1053960,294160,294168,1635712,1637768,1627536,1627544,488976,362008,478864,489112,730880,362248,489232,362264,499584,499592,489360,489368],[1076480,1053960,294160,294168,1635712,1637768,1627536,1627544,488976,362008,478864,489112,730880,362248,489232,362264,499584,499592,489360,489368],[626820,1409408,627076,182912,1194628,183168,1194884,1195140,1623424,1195396,1164928,1195652,1195904,1195908],[998016,1018500,498560,1018756,494724,1639808,494980,478848,495236,495488,495492],[628884,1411456,1440132,1442192,629140,182928,1194644,498560,1194884,1194896,1194900,1195156,1623424,1195396,1688976,1195412,1175184,1195668,499584,1195908,1195920,1195924],[488080,488084,498560,1018756,488336,488340,488596,1639808,494980,447888,488852,478864,489108,495488,495492,489360,489364],[1639808,478848,497536],[1639808,478848,497536],[1639808,1627536,478864,499584,489360],[1639808,1627536,478864,499584,489360],[491654,489614,1138952,358666,964876,489742,1413504,465282,184708,491910,467336,491914,489868,489870,324106,489998,182914,492166,479882,490126,965384,359178,965388,490254,185216,492418,185220,492422,490376,490378,490380,490382,355332,357382,490508,490510,492676,492678,490636,490638,304384,1070338,355588,357638,359688,359690,490764,490766,464256,466306,492932,492934,468360,492938,490892,490894,318976,1097218,355844,357894,712200,325130,491020,491022,480896,480898,493188,493190,480904,480906,491148,491150,356096,358146,356100,358150,360200,360202,491276,491278,493440,493442,493444,493446,491400,491402,491404,491406],[360970,489998,477826,494214,473738,490126,592648,361226,592652,490254,185216,494466,185220,494470,490376,490378,490380,490382,355332,732166,490508,277518,494724,400518,490636,439438,306432,1074434,355588,732422,1090824,1090826,490764,490766,464256,466306,494980,494982,468360,497034,490892,490894,318976,321026,355844,732678,361992,361994,491020,491022,478848,478850,495236,495238,497288,497290,491148,491150,356096,732930,356100,732934,362248,362250,491276,491278,495488,495490,495492,495494,491400,491402,491404,491406],[962824,1698060,1417600,1421700,1139080,489868,963336,1698572,1194880,1018756,490376,490380,1072384,1697028,1080584,490764,1635712,1195396,1637768,490892,730880,1697540,491272,491276,1195904,1195908,491400,491404],[592648,592652,498560,1002372,490376,490380,1076480,724228,1090824,490764,1635712,494980,1637768,490892,724736,724740,362248,491276,495488,495492,491400,491404],[306432,1074434,1090824,1090826,464256,466306,468360,497034,318976,321026,361992,361994,478848,478850,497288,497290,726784,728834,362248,362250,497536,497538,497544,497546],[306432,1074434,1090824,1090826,464256,466306,468360,497034,318976,321026,361992,361994,478848,478850,497288,497290,726784,728834,362248,362250,497536,497538,497544,497546],[1076480,1090824,1635712,1637768,730880,362248,499584,499592],[1076480,1090824,1635712,1637768,730880,362248,499584,499592],[491654,1423744,1706370,627076,491910,182914,492166,1194880,492418,1018756,492422,492676,492678,1639808,1707394,492932,492934,480896,480898,493188,493190,493440,493442,493444,493446],[477826,494214,498560,494466,1018756,494470,494724,494726,1639808,470402,494980,494982,478848,478850,495236,495238,495488,495490,495492,495494],[1427840,1440132,498560,1018756,1639808,1195396,499584,1195908],[498560,1018756,1639808,494980,495488,495492],[1639808,1641858,478848,478850,497536,497538],[1639808,1641858,478848,478850,497536,497538],[1639808,499584],[1639808,499584]]

def rc4 : List (List ℕ) := [[604672,604680,604736,604744],[1298944,504328,1448512,606792,203784,603200,609352,501248,507400,603712,609864],[895240,778520,991552,749896,158032,641368,1286672,522776,756304,641624,578304,566024,1286928,641816,750400,750408,762704,641880],[1339920,641560,1667664,641624,580352,826120,838416,641816,824128,824136,838480,641880,293912,834640,488536,447752,294168,173376,173384,447824,447832,1578512,1691160,835152,835160,556800,827144,651024,827160,651072,827208,651088,827224],[1249824,627240,1403488,627304,205832,529448,162880,1387592,160864,623720,683520,689672,503328,529960,1381952,1388104,624224,624232],[1251872,1294888,1405536,612968,248840,250920,162880,625736,179296,625768,683520,1584648,685600,699944,1492544,626248,626272,626280],[1012008,1087800,1001824,776552,1171824,776568,1288752,834104,834160,834168,723744,592680,777008,777016,777056,777064,777072,777080,293912,1516600,834640,834648,834672,623736,1053960,294168,1013032,1516856,984384,818504,834896,834904,1006944,777576,834928,777592,503312,1627672,503344,835128,835152,835160,624240,624248,730880,818952,730896,1627928,778016,778024,778032,778040,1507136,819016,835408,835416,778080,778088,778096,778104],[1290800,834104,834160,834168,699168,592680,699184,699192,777056,777064,777072,777080,293912,367672,834640,488536,179312,488568,1053960,294168,367912,367928,984384,1021256,834896,488792,179552,777576,179568,488824,1578512,1691160,685616,699960,835152,626264,626288,626296,730880,737032,730896,737048,700192,700200,700208,700216,1507136,1513288,835408,835416,778080,778088,778096,778104],[741952],[1649216,164928,656960],[1126720,405840,795216,744256,762704],[1700432,822080,838480,834640,165184,447824,835152,657216,835408],[1620576,984128,1006688,1506880,1439328],[1628768,984128,179296,1492544,1445472],[485728,489840,834160,777056,777072,834640,834672,984384,834896,1006944,834928,835152,835184,1507136,835408,778080,778096],[834160,777056,777072,834640,179312,984384,834896,179552,179568,835152,835184,1507136,835408,778080,778096],[917768,620810,166208,168258,610632,620874,614914,614922,614978,614986,574208,1348354,514824,621322,611136,617282,611144,621386,242696,621578,162880,169026,615496,615498,619784,621834,167232,169282,619848,621898,519680,615938,615944,615946,616000,616002,616008,616010,597760,1349378,620296,622346,618304,618306,620360,622410],[1307138,1458698,1503810,1458762,576256,695042,592648,695050,664384,1510210,613192,625482,248840,1092618,162880,179266,625736,625738,1090824,1090826,994624,179522,625992,625994,519680,710146,1584648,1574410,1492544,1510978,626248,626250,694016,696066,601864,696074,1492800,1511234,626504,626506],[917768,991552,842056,578304,842504,822080,842568,1086728,1004864,843080,724736,843528,669504,843592],[580352,592648,822080,824136,1090824,984384,1021256,724736,737032,1515328,1513288],[528680,629034,178528,178530,622952,622954,1274402,629290,1407586,629354,623392,623394,529192,623402,623456,623458,623464,623466,248840,629770,529448,629802,162880,179266,1387592,629834,179296,179298,623720,623722,1090824,630026,529704,630058,994624,179522,1387848,630090,179552,179554,623976,623978,683520,521730,689672,630282,685600,685602,529960,630314,1381952,1384002,1388104,630346,624224,624226,624232,624234,694016,1388290,737032,630538,624416,624418,530216,624426,1515328,1388354,1388360,630602,624480,624482,624488,624490],[1274402,1294890,1503842,1458794,699168,699170,592680,699178,625504,625506,613224,625514,248840,1092618,250920,699434,162880,179266,625736,625738,179296,179298,625768,625770,1090824,1090826,697640,697642,994624,179522,625992,625994,179552,179554,626024,626026,683520,710146,1584648,1574410,685600,685602,699944,699946,1492544,1510978,626248,626250,626272,626274,626280,626282,694016,696066,737032,696074,700192,700194,700200,700202,1492800,1511234,626504,626506,626528,626530,626536,626538],[366888,178528,776552,699168,592680,777056,777064,1090824,367912,984384,1021256,179552,777576,730880,737032,700192,700200,1515328,1513288,778080,778088],[699168,592680,777056,777064,1090824,367912,984384,1021256,179552,777576,730880,737032,700192,700200,1515328,1513288,778080,778088],[450880,1016130,789058,820032,774978,1489984,1489986,1017152,1017154,1490496,1490498,776000,776002],[1503810,820032,828226,164928,179266,994624,179522,1492544,1508930,671552,1515330],[450880,820032,1017152,669504],[820032,984384,1515328],[178528,178530,1698402,1438560,629602,984128,179266,179296,179298,984384,179522,179552,179554,1506880,1508930,1439328,841314,1515328,1515330,1439584,630626],[1503842,670560,777058,984128,179266,179296,179298,984384,179522,179552,179554,1492544,1508930,1445472,1445474,1492800,1515330,778080,778082],[178528,777056,984384,179552,1515328,778080],[777056,984384,179552,1515328,778080]]

def rc5 : List (List ℕ) := [[563464,567564,647488,651588,657736,659788,1298944,535044,539144,567820,631360,633412,635464,660044,549632,557828,563976,568076,648000,652100,658248,660300],[1298944,1309188,541192,1479180,1448512,1468996,637512,1479244,551680,559876,662280,662284,654144,654148,662344,662348,662540,662596,662604,447752,662796,1498432,662852,447816,662860,534016,663044,1318408,663052,1498688,663108,640584,663116,554752,663300,663304,663308,1498944,663364,663368,663372],[895240,665868,778520,837916,991552,457028,813384,665932,987472,457044,778584,837980,1339920,799252,641560,799260,795216,799316,641624,799324,578304,588548,566024,666380,838416,838420,838424,838428,813888,809796,813896,666444,838480,838484,838488,838492],[1339920,1708564,641560,1708572,1667664,1673812,641624,1708636,580352,584452,826120,826124,838416,838420,826136,826140,824128,844612,824136,826188,838480,838484,826200,826204,488476,425044,488540,447752,826636,294168,488732,173376,458052,173384,826700,447824,458068,447832,488796,1578512,826900,1691160,826908,835152,826964,835160,826972,556800,827140,827144,827148,651024,827156,827160,827164,651072,827204,827208,827212,651088,827220,827224,827228],[1090824,994624,1512776,706048,1584648,1492544,1513032,726784,737032,1515328,1513288],[1090824,994624,1512776,706048,1584648,1492544,1513032,726784,737032,1515328,1513288],[1053960,294168,994624,818504,834896,488792,1578512,720408,835152,800344,730880,737032,730896,720664,1507136,819016,835408,835416],[1053960,294168,994624,1021256,834896,488792,1578512,1691160,835152,835160,730880,737032,730896,737048,1507136,1513288,835408,835416],[450880,444740,787008,1653316,805696,807748],[1649216,1661508,824128,807748,676932,173376,677188,656960,677444,657216,677700],[450880,1155396,1145168,1145172,795216,799316,822080,809796,838480,838484],[1700432,1673812,822080,822084,838480,838484,488532,173376,677188,447824,488788,835152,677460,657216,677700,835408,677716],[994624,1492544,1507136],[994624,1492544,1507136],[994624,834896,835152,1507136,835408],[994624,834896,835152,1507136,835408],[917768,307466,674060,674062,989504,176450,663876,672070,674120,672074,674124,672078,1307138,1350150,713226,713230,672322,672326,672330,672334,574208,1348354,582404,1350406,674568,674570,674572,674574,664384,672578,664388,672582,674632,672586,674636,672590,674828,674830,670788,672838,674892,672846,308488,308490,675084,675086,177472,177474,671044,673094,675144,673098,675148,673102,548352,1349122,1351172,1351174,712200,714250,675340,675342,646720,673346,671300,673350,646728,673354,675404,673358,597760,1349378,1351428,1351430,675592,675594,675596,675598,671552,673602,671556,673606,675656,673610,675660,673614],[1307138,731654,1458698,731662,1503810,676422,1458762,676430,576256,731906,582404,731910,592648,674570,592652,674574,664384,1510210,664388,676678,674632,674634,674636,674638,734220,732174,670788,179270,625740,625742,1090824,1090826,734476,732430,994624,179522,671044,179526,1512776,1512778,677196,677198,548352,710146,722436,732678,1584648,1574410,734732,732686,1492544,1510978,671300,677446,1488456,1513034,677452,677454,599808,732930,722692,732934,601864,732938,734988,732942,671552,1511234,671556,677702,1513288,1513290,677708,677710],[917768,665868,991552,1009988,842056,665932,578304,588548,842504,666380,822080,822084,842568,666444,1086728,843020,1004864,677188,843080,677196,724736,724740,843528,843532,669504,677700,843592,677708],[580352,584452,592648,592652,822080,822084,824136,826188,1090824,734476,994624,677188,1021256,677196,724736,724740,737032,734988,1515328,677700,1513288,677708],[1090824,630026,994624,179522,1512776,630090,706048,708098,1584648,1574410,1492544,1510978,1513032,1513034,726784,728834,737032,737034,1515328,1511234,1513288,1513290],[1090824,1090826,994624,179522,1512776,1512778,706048,710146,1584648,1574410,1492544,1510978,1513032,1513034,726784,728834,737032,737034,1515328,1511234,1513288,1513290],[1090824,994624,1021256,730880,737032,1515328,1513288],[1090824,994624,1021256,730880,737032,1515328,1513288],[450880,1016130,452932,672070,672322,672326,820032,672578,832324,672582,670788,672838,1017152,1017154,671044,673094,1490496,673346,671300,673350,671552,673602,671556,673606],[1503810,676422,820032,828226,844612,676678,670788,179270,994624,179522,671044,179526,1492544,1508930,671300,677446,671552,1515330,671556,677702],[450880,1155396,820032,822084,1017152,677188,669504,677700],[820032,822084,994624,677188,1515328,677700],[994624,179522,1492544,1508930,1515328,1515330],[994624,179522,1492544,1508930,1515328,1515330],[994624,1515328],[994624,1515328]]

def rc6 : List (List ℕ) := [[508424,201736,679424,681480],[510472,203784,679424,1584648],[895240,719128,524824,817928,641816,719896,1053960,720152,1578512,720408,724736,818952,730896,720664],[524824,592648,641816,293912,447752,294168,1578512,1691160,724736,827144,730896,827160],[627240,205832,250920,683520,689672,685600,691752],[1294888,248840,250920,683520,1584648,685600,699944],[366888,366904,834104,592680,777016,293912,367672,1053960,294168,367912,367928,1578512,720408,685616,691768,730880,818952,730896,720664,778016,778024,778032,778040],[834104,592680,699192,293912,367672,1053960,294168,367912,367928,1578512,1691160,685616,699960,730880,737032,730896,737048,700192,700200,700208,700216],[],[],[],[],[],[],[],[],[917768,280842,512522,516872,736010,242696,244746,279816,281866,683520,708098,689672,687626,694016,1586946,737032,737034],[1458698,592648,736010,248840,1092618,1090824,1090826,683520,710146,1584648,1574410,694016,696066,737032,737034],[917768,842504,1086728,724736,737032],[592648,1090824,724736,737032],[696616,629034,629290,592680,629546,248840,1092618,250920,1092650,1090824,1090826,697640,697642,683520,708098,689672,1574410,685600,685602,691752,691754,694016,696066,737032,737034,698144,698146,698152,698154],[1294890,592680,699178,248840,1092618,250920,699434,1090824,1090826,697640,697642,683520,710146,1584648,1574410,685600,685602,699944,699946,694016,696066,737032,737034,700192,700194,700200,700202],[366888,592680,1090824,367912,730880,737032,700192,700200],[592680,1090824,367912,730880,737032,700192,700200],[],[],[],[],[],[],[],[]]

def rc7 : List (List ℕ) := [[895240,571660,543240,571916,572168,572172,734220,718088,734476,701952,716292,704008,734732,716544,716548,718600,734988],[545288,592396,592648,592652,734220,447752,734476,701952,716292,1584648,734732,716544,716548,1584904,734988],[895240,665868,719128,837916,641560,643612,817928,666380,719640,838428,734236,1053960,734476,720152,734492,1578512,800276,720408,734748,724736,724740,818952,734988,730896,839444,720664,735004],[641560,643612,592648,592652,826136,826140,488476,447752,734476,294168,488732,1578512,826900,1691160,734748,724736,724740,827144,734988,730896,827156,827160,735004],[1090824,706048,1584648,726784,737032],[1090824,706048,1584648,726784,737032],[1053960,294168,1578512,720408,730880,737032,730896,720664],[1053960,294168,1578512,1691160,730880,737032,730896,737048],[],[],[],[],[],[],[],[],[917768,307466,674060,674062,713226,713230,674568,674570,674572,674574,734220,713742,308488,308490,734476,734478,706048,708098,722436,1586694,712200,714250,734732,714254,726784,1586946,722692,1586950,737032,737034,734988,734990],[1458698,733710,592648,674570,592652,674574,734220,734222,1090824,1090826,734476,734478,706048,710146,722436,732678,1584648,1574410,734732,734734,726784,732930,722692,732934,737032,737034,734988,734990],[917768,665868,842504,666380,1086728,734476,724736,724740,737032,734988],[592648,592652,1090824,734476,724736,724740,737032,734988],[1090824,1090826,706048,708098,1584648,1574410,726784,728834,737032,737034],[1090824,1090826,706048,710146,1584648,1574410,726784,728834,737032,737034],[1090824,730880,737032],[1090824,730880,737032],[],[],[],[],[],[],[],[]]

def rc8 : List (List ℕ) := [[901632,901634,901648,901650,901664,901666,901680,901682],[1298944,848386,1323536,903698,877088,903714,897584,903730,21506,861200,906258,298016,64546,900144,906290,847360,851458,861712,906770,880160,906786,900656,906802],[872976,926256],[1339920,1290800,293904,293936,1578512,1578544],[883232,887330,907824,909874,25602,58384,914450,52256,54306,58416,914482,892416,869890,917008,914962,892448,894498,917040,914994],[885280,889378,911920,911922,220162,449552,1537042,298016,1063970,449584,1537074,1031680,1531394,1527312,1537554,1547808,1551906,1537584,1537586],[1288752,1104912,347184,1105424,1539632],[1290800,293904,347184,1578512,1537584],[1593920,1139266,1047120,963154,963168,963170,963184,963186,1110656,895618,918160,918162,895648,895650,918192,918194,1110720,895682,918224,918226,895712,895714,918256,918258],[1649216,858690,1700432,963154,963168,963170,963184,963186,998016,973442,1000080,973458,969376,973474,969392,973490,998080,973506,1000144,973522,973536,973538,973552,973554,164930,1432656,1432658,1432672,1432674,1432688,1432690,470146,1604752,470162,470176,470178,470192,470194,470210,1432784,470226,470240,470242,470256,470258,925248,1508930,1433168,1433170,925280,1433186,1433200,1433202,970368,974466,970384,974482,970400,974498,970416,974514,925376,974530,974544,974546,925408,974562,974576,974578],[1045072,963184,1196688,1196720,1196752,1196784],[1700432,963184,1000080,1196720,1000144,973552,293968,294000,294032,294064,294096,294128,1433168,1433200,1695376,1695408,974544,974576],[965216,1698402,965232,1698418,1088160,1088162,1088176,1088178,1088224,1088226,1088240,1088242,984130,984144,666706,113760,666722,975984,666738,570498,1604752,666770,570528,570530,1344688,666802,773314,1604816,666834,1342688,666850,976112,666866,984640,984642,984656,976466,976480,976482,976496,976498,1119872,1119874,917136,1345170,1345184,1345186,917168,1345202,1119936,1119938,1527504,976594,976608,976610,976624,976626],[1628768,1503842,1628784,1698418,1010336,973474,1010352,973490,973536,973538,973552,973554,977986,984144,531538,140384,140386,975984,832626,773250,1604752,832658,836768,840866,832688,832690,531650,531664,531666,595168,840930,832752,832754,978496,978498,978512,976466,976480,976482,976496,976498,1183360,974466,1183376,974482,1158816,974498,1158832,974514,974528,974530,974544,974546,974560,974562,974576,974578],[1696368,1088176,1088240,984144,975984,1604752,830640,736464,830704,984656,976496,1605264,1189552,1502928,976624],[1696368,1010352,973552,293968,179312,294032,830640,294096,830704,978512,976496,1187472,1158832,974544,974576],[852482,881186,19458,62496,62498,863744,865794,921120,921122],[854530,889378,21506,298016,64546,863744,867842,1545760,1551906],[],[],[889378,25602,66592,68642,1031680,869890,923168,1549858],[889378,220162,298016,1063970,1031680,1531394,1547808,1551906],[],[],[858690,963170,1088130,1088162,1088194,1088226,1008706,187488,1008738,779394,836768,779426,720066,595168,720098,925248,1009218,925280,1009250,970368,1089154,970400,1089186,925376,1089218,925408,1089250],[858690,963170,973442,973474,973506,973538,977986,531552,531554,470146,470176,470178,470210,470240,470242,925248,978498,925280,976482,970368,974466,970400,974498,925376,974530,925408,974562],[],[],[1698402,1088162,1088226,984130,140384,140386,773250,836768,838818,720066,595168,838882,984640,984642,976480,976482,1119872,1119874,1148576,1148578,1119936,1119938,976608,976610],[1503842,973474,973538,977986,140384,140386,773250,836768,840866,531650,595168,840930,978496,978498,976480,976482,1183360,974466,1158816,974498,974528,974530,974560,974562],[],[]]

def rc9 : List (List ℕ) := [[1298944,930306,934404,948742,942608,944658,946708,948758],[1298944,1303042,1309188,1479174,1323536,1327634,1468948,1479190,103430,1481748,1481750,1302016,1306114,1482244,1482246,1326608,1500690,1482260,1482262],[954896,1677844],[1339920,1708564,826388,1578512,1691156],[1564160,1566210,1578512,1582610],[1564160,1566210,1578512,1582610],[1105424],[1578512],[1649216,1651266,1653316,1681990,1100368,963154,1673812,1682006,998016,1198722,1012356,1012358,1196688,1198738,1012372,1012374,998080,1198786,1682116,1682118,1196752,1198802,1682132,1682134],[1649216,1651266,1661508,1692230,1700432,963154,1673812,1018454,998016,973442,1018500,973446,1000080,973458,1018516,973462,998080,973506,1018564,973510,1000144,973522,1018580,973526,367686,363604,156758,156806,156820,156822,156870,156884,156886,1492544,1508930,1494596,1494598,1472080,1472082,1494612,974422,970368,974466,1482372,974470,970384,974482,1482388,974486,974528,974530,974532,974534,974544,974546,974548,974550],[1100368,1673812,1196688,971412,1196752,1682132],[1700432,1673812,1000080,1106580,1000144,1106644,676948,826516,367828,1472080,1494612,1695376,1691284,974544,974548],[978496,978498,978512,976466,1183360,974466,1183376,974482,974528,974530,974544,974546],[978496,978498,978512,976466,1183360,974466,1183376,974482,974528,974530,974544,974546],[978512,1187472,974544],[978512,1187472,974544],[932354,936454,951302,1338880,968194,1568260,951814],[1307138,1350150,1494022,1338880,1566210,1568260,1494534],[],[],[1564160,1566210],[1564160,1566210],[],[],[1684034,1681990,1172098,1172102,1198786,1516230,367686,1088646,367814,1490496,1009218,1711684,1009222,970368,1173122,1013380,1173126,1175232,1199810,1517252,1509062],[1503810,1503814,973442,973446,973506,973510,179270,973958,367814,978496,978498,978500,978502,970368,974466,1568388,974470,974528,974530,974532,974534],[],[],[978496,978498,1183360,974466,974528,974530],[978496,978498,1183360,974466,974528,974530],[],[]]

def rc10 : List (List ℕ) := [[1214984,1057290,1137176,1057306,1057320,1057322,1057336,1057338,979584,991874,1108616,1127050,989840,991890,1137304,1137306,985760,991906,1137320,1127082,989872,991922,1137336,1137338,295938,1057802,1055760,1057810,451608,451610,283680,295970,451624,451626,1055792,1057842,451640,451642,1127554,1127562,1131664,1131666,451736,451738,1125536,1127586,451752,451754,1131696,1131698,451768,451770,1023488,1058306,1109512,1058314,1056272,1058322,1138200,1058330,1058336,1058338,1058344,1058346,1056304,1058354,1058360,1058362,1109632,1128066,1109640,1128074,1132176,1132178,1138328,1138330,1126048,1128098,1138344,1128106,1132208,1132210,1138360,1138362],[1217032,1128970,1575448,1141274,1141288,1129002,1141304,1141306,995968,981634,1122952,1129098,1000080,1010322,1000088,1141402,1010336,1010338,1141416,1129130,1010352,1010354,1141432,1141434,211970,1027082,449552,1537042,453656,1141786,298016,1063970,461864,1129514,449584,1537074,453688,1141818,412802,412810,449680,1152146,453784,1141914,455840,457890,461992,1129642,449712,1152178,453816,1141946,1023488,1521154,1025544,1129994,1029648,1537554,1123864,1142298,1545760,1551906,1142312,1130026,1537584,1537586,1142328,1142330,1121920,1152642,1123976,1130122,1121936,1152658,1123992,1142426,1152672,1152674,1142440,1130154,1152688,1152690,1142456,1142458],[1016344,1016376,1014416,1014424,1014448,1014456,1104912,1580056,1104944,1580088,1154192,1154200,1154224,1154232,1105424,1580568,1105456,1580600,1154704,1154712,1154736,1154744],[1575448,1141304,1000080,1000088,1010352,1014456,293904,293912,293936,293944,449680,1186968,449712,470200,1578512,1691160,1537584,1142328,1187472,1187480,1152688,1142456],[1065512,1065514,1083960,1083962,1010336,1010338,1155752,1155754,1010352,1010354,1155768,1155770,220162,1027082,386064,1135634,453656,1084442,283680,1063970,285736,300074,1133616,1135666,453688,1084474,412802,412810,386192,1113234,453784,1113242,443552,457890,445608,1156266,1133744,1135794,453816,1156282,1031680,1531394,1525256,1027594,1527312,1136146,1527320,1084954,1050144,1064482,1066536,1066538,1134128,1136178,1084984,1084986,1113728,1113730,1113736,1113738,1113744,1113746,1113752,1113754,1134240,1136290,1156776,1156778,1134256,1136306,1156792,1156794],[1141288,1141290,1141304,1141306,1010336,1010338,1141416,1141418,1010352,1010354,1141432,1141434,220162,277514,449552,1537042,453656,277530,298016,1063970,461864,699434,449584,1537074,453688,699450,412802,412810,449680,1152146,453784,1141914,455840,457890,461992,1156266,449712,1152178,453816,1141946,1031680,1531394,1035784,1068554,1527312,1537554,1123864,1142298,1547808,1551906,1068584,1068586,1537584,1537586,1142328,1142330,1121920,1150594,1123976,1150602,1121936,1152658,1123992,1142426,1152672,1150626,1142440,1142442,1152688,1152690,1142456,1142458],[1710648,1010352,1155768,1104912,1604632,347184,367672,1604752,1604760,828592,828600,1105424,1605144,1537584,1539640,1605264,1605272,1189552,1156792],[1141304,1010352,1141432,293904,293912,347184,367672,449680,1186968,449712,830648,1578512,1691160,1537584,1142328,1187472,1187480,1152688,1142456],[1110656,1188482,1114768,1188498,1188512,1188514,1188528,1188530,750722,775312,842898,812192,814242,828592,842930,1111680,1189506,1115792,1189522,1189536,1189538,1189552,1189554],[998016,1118850,1000080,1010322,1010336,1010338,1010352,1010354,470146,1604752,470162,470176,470178,470192,470194,1183360,1150594,1183376,1158802,1158816,1150626,1158832,1158834],[1014416,1014448,775312,828592,1197712,1189552],[1000080,1010352,1604752,470192,1187472,1158832],[1010336,1010338,1010352,1010354,773250,1604752,832658,816288,816290,828592,832690,1119872,1119874,1605264,1189522,1189536,1189538,1189552,1189554],[1010336,1010338,1010352,1010354,773250,1604752,832658,836768,840866,832688,832690,1183360,1150594,1183376,1158802,1158816,1150626,1158832,1158834],[1010352,1604752,828592,1605264,1189552],[1010352,1604752,830640,1187472,1158832],[856586,1145386,981634,1116810,987810,1145514,295938,232458,298016,295970,459816,1145898,392322,406666,455840,1143970,459944,1146026,1031680,1060354,1033736,1033738,1545760,1060386,1146408,1146410,1177216,1117826,1177224,1117834,1191584,1144482,1146536,1146538],[1458698,1141290,981634,1149578,1010338,1141418,211970,277514,298016,1063970,461864,1068074,412802,412810,455840,457890,461992,1156266,1031680,1060354,1035784,1068554,1545760,1060386,1068584,1068586,1121920,1150594,1123976,1150602,1152672,1150626,1156776,1150634],[],[],[1065514,987810,1141418,220162,240650,298016,1063970,461864,300074,412802,412810,455840,457890,461992,1156266,1031680,1531394,1035784,1037834,1062432,1064482,1066536,1066538,1191552,1150594,1123976,1150602,1148576,1148578,1156776,1150634],[1141290,1010338,1141418,220162,277514,298016,1063970,461864,699434,412802,412810,455840,457890,461992,1156266,1031680,1531394,1035784,1068554,1547808,1551906,1068584,1068586,1121920,1150594,1123976,1150602,1152672,1150626,1156776,1150634],[],[],[1188482,1188514,779394,836768,779426,1177216,1150594,1148576,1148578],[1118850,1010338,470146,470176,470178,1183360,1150594,1158816,1150626],[],[],[1010338,773250,836768,838818,1119872,1119874,1148576,1148578],[1010338,773250,836768,840866,1183360,1150594,1158816,1150626],[],[]]

def rc11 : List (List ℕ) := [[1321480,1102346,1165836,1102350,1575448,1102362,1165852,1102366,995968,1159810,1002116,1002118,1180296,1180298,1165964,1165966,1002128,1002130,1002132,1002134,1180312,1180314,1165980,1165982,330758,486414,1166356,1102870,1166364,1102878,1166470,486542,1166484,1166486,1166492,1166494,1555968,1558018,1166852,1166854,1572360,1103370,1166860,1103374,1560080,1560082,1166868,1103382,1576472,1103386,1166876,1103390,1191552,1160834,1166980,1166982,1181320,1181322,1166988,1166990,1181328,1181330,1166996,1166998,1181336,1181338,1167004,1167006],[1321480,1569290,1335820,1587726,1575448,1587738,1335836,1587742,995968,1172098,1002116,1002118,1184392,1184394,1168012,1168014,1000080,1002130,1002132,1002134,1000088,1184410,1168028,1168030,1567750,490510,449556,490518,453660,490526,494726,490638,449684,490646,453788,490654,1555968,1558018,1568260,1568262,1584648,1584650,1193484,1193486,1578512,1582610,1588756,1185302,1582616,1582618,1193500,1185310,1171072,1173122,1185412,1173126,1185416,1185418,1185420,1185422,1185424,1185426,1185428,1185430,1185432,1185434,1185436,1185438],[1016344,1008156,1014416,1020564,1014424,1008284,1678356,1698844,1180820,1180828,1105424,1678868,1576472,1699356,1181328,1181332,1181336,1181340],[1575448,1008156,1000080,1020564,1000088,1008284,449556,490524,449684,490652,1578512,1588756,1691160,1193500,1187472,1691284,1187480,1193628],[1564160,1566210,1572360,1574410,1578512,1582610,1582616,1582618,1183360,1179266,1187464,1179274,1183376,1187474,1187480,1187482],[1564160,1566210,1584648,1574410,1578512,1582610,1582616,1582618,1183360,1179266,1187464,1179274,1183376,1187474,1187480,1187482],[1105424,1691160,1187472,1187480],[1578512,1691160,1187472,1187480],[998016,1188482,1012356,1012358,1196688,1188498,1012372,1012374,777350,826516,777366,1164928,1189506,1195652,1189510,1197712,1189522,1195668,1189526],[998016,1172098,1018500,1018502,1000080,1010322,1018516,1010326,494726,453780,494742,1183360,1173122,1185412,1173126,1183376,1185426,1185428,1185430],[1014416,1020564,826516,1197712,1195668],[1000080,1020564,494740,1187472,1691284],[1183360,1179266,1183376,1187474],[1183360,1179266,1183376,1187474],[1187472],[1187472],[1102346,1102350,1172098,1172102,1180298,1180302,1586182,490510,1172614,490638,1564160,1097218,1568260,1586694,1572360,1103370,1193484,1103374,1177216,1173122,1177220,1173126,1177224,1181322,1177228,1181326],[1458698,1458702,1172098,1172102,1178250,1192590,1586182,277518,494726,490638,1564160,1566210,1568260,1586694,1584648,1574410,1193484,1193486,1171072,1173122,1185412,1173126,1185416,1179274,1185420,1193614],[],[],[1564160,1566210,1572360,1574410,1183360,1179266,1187464,1179274],[1564160,1566210,1584648,1574410,1183360,1179266,1187464,1179274],[],[],[1172098,1172102,777350,1177216,1173122,1177220,1173126],[1172098,1172102,494726,1183360,1173122,1185412,1173126],[],[],[1183360,1179266],[1183360,1179266],[],[]]

def rc12 : List (List ℕ) := [[1298944,1202690,1204744,1210890,1225232,1268242,1227288,1278490,1237536,1243682,1258024,1262122,1264176,1268274,1276472,1278522,1356352,1358402,1362504,1366602,1376848,1417810,1378904,1428058,1389152,1395298,1409640,1411690,1413744,1417842,1423992,1428090],[1298944,1303042,1206792,1368586,1323536,1270290,1329688,1430042,1239584,1245730,1260072,1430058,1266224,1270322,1425976,1430074,1448512,1466946,1364552,1368650,1460816,1419858,1426008,1430106,1391200,1397346,1426024,1430122,1419888,1419890,1426040,1430138,1371146,1500184,1430554,461864,1430570,1500216,1430586,1399874,1371210,1463376,1500242,1500248,1430618,1393760,1399906,461928,1430634,1416304,1500274,1500280,1430650,1201664,1306114,1209864,1371658,1326608,1500690,1500696,1431066,1242656,1400354,1261096,1431082,1416752,1500722,1500728,1431098,1394240,1400386,1371720,1371722,1463888,1500754,1500760,1431130,1394272,1400418,1500776,1431146,1416816,1500786,1500792,1431162],[1286672,1235480,1286704,1706552,1608272,1675864,1632880,1706616],[1339920,1352216,1290800,1352248,1667664,1708632,1632880,1706616,293912,293944,834640,834648,466032,834680,1578512,1691160,1578544,1691192,1433168,1433176,1433200,1433208],[1249824,1274402,1440296,1440298,1272368,1274418,1440312,1440314,1403488,1407586,1440360,1440362,1421936,1421938,1440376,1440378,1027082,916504,1440794,70696,1440810,916536,1440826,1383490,1375306,1422416,1422418,1387608,1440858,171104,1438818,1440872,1440874,1422448,1422450,1440888,1440890,1529344,1531394,1525256,1375754,1422864,1422866,1527320,1441306,1254944,1256994,1441320,1441322,1422896,1422898,1441336,1441338,1381952,1384002,1388104,1375818,1422928,1422930,1388120,1441370,1439328,1439330,1441384,1441386,1422960,1422962,1441400,1441402],[1251872,1274402,1294888,1294890,1290800,1274418,1294904,1294906,1405536,1503842,1444456,1442410,1421936,1421938,1444472,1442426,1027082,453656,699418,461864,699434,453688,699450,179266,1444938,449616,179282,453720,1444954,179296,179298,461928,1444970,179312,179314,453752,1444986,1529344,1531394,1584648,1574410,1527312,1537554,1527320,1543706,1547808,1551906,1543720,1543722,1537584,1537586,1543736,1543738,1492544,1510978,1445448,1445450,1472080,1445458,1445464,1445466,1445472,1445474,1445480,1445482,1445488,1445490,1445496,1445498],[1288752,1516088,1696368,1516152,293912,1516600,834640,834648,834672,834680,1605136,1605144,1539632,1517112,1605200,1388120,1439344,1517176],[1290800,1294904,1696368,1444472,293912,367672,449616,625752,179312,834680,1578512,1691160,1537584,1543736,1472080,1445464,1445488,1445496],[1593920,1595970,1610320,1636946,1618528,1618530,1636976,1636978],[1649216,1651266,1700432,1704530,1628768,1704546,1628784,1704562,164930,1432656,1432658,173152,173154,468080,1432690,1492544,1508930,1433168,1433170,1433184,1433186,1433200,1433202],[1700432,1700464],[1700432,1700464,834640,834672,1433168,1433200],[1620576,1620578,1696368,1696370,984130,984144,666706,1006688,666722,1006704,666738,1506880,1506882,1605200,1439314,1439328,1439330,1439344,1439346],[1628768,1503842,1628784,1696370,179266,834640,179282,179296,179298,179312,179314,1492544,1506882,1472080,1445458,1445472,1445474,1445488,1445490],[1696368,834640,834672,1605200,1439344],[1696368,834640,179312,1472080,1445488],[1247746,1212938,1247778,1442346,1360450,1372746,1401442,1442410,1281034,70696,1281066,175170,1434698,187488,175202,1436776,1434730,1232384,1349122,1572360,1281546,1437216,1349154,1437224,1281578,1381952,1435202,1386056,1435210,1437280,1435234,1437288,1435242],[1307138,1458698,1274402,1442346,1503810,1444426,1503842,1442410,1092618,461864,1092650,179266,1444938,179296,179298,461928,1444970,1232384,1566210,1584648,1574410,1437216,1551906,1437224,1551914,1492544,1510978,1445448,1445450,1437280,1445474,1437288,1445482],[],[],[1274402,1442346,1407586,1442410,629770,70696,629802,179266,629834,179296,179298,461928,629866,1529344,1531394,1572360,1281546,1547808,1549858,1441320,1443370,1381952,1384002,1388104,1435210,1439328,1439330,1441384,1443434],[1274402,1294890,1503842,1442410,1092618,461864,699434,179266,1444938,179296,179298,461928,1444970,1529344,1531394,1584648,1574410,1547808,1551906,1553960,1551914,1492544,1510978,1445448,1445450,1445472,1445474,1445480,1445482],[],[],[1684034,1684066,1008706,187488,1008738,1490496,1508930,1437280,1508962],[1503810,1503842,179266,179296,179298,1492544,1508930,1437280,1445474],[],[],[1698402,179266,179296,179298,1506880,1508930,1439328,1439330],[1503842,179266,179296,179298,1492544,1508930,1445472,1445474],[],[]]

def rc13 : List (List ℕ) := [[1298944,1303042,1309188,1477126,1313288,1319434,1333772,1477134,1323536,1327634,1468948,1477142,1329688,1331738,1333788,1477150,1446464,1450562,1468996,1477190,1452616,1475146,1477196,1477198,1460816,1464914,1469012,1477206,1473112,1475162,1477212,1477214],[1298944,1303042,1309188,1479174,1315336,1456650,1479180,1479182,1323536,1327634,1468948,1479190,1329688,1481242,1479196,1479198,1448512,1466946,1468996,1479238,1454664,1456714,1479244,1479246,1460816,1466962,1469012,1479254,1479256,1479258,1479260,1479262,1481742,1481756,1481758,1481798,1481806,422996,1481814,1481820,1481822,1302016,1306114,1482244,1482246,1318408,1457674,1482252,1482254,1326608,1500690,1482260,1482262,1500696,1482266,1482268,1482270,1498688,1498690,1482308,1482310,1457736,1457738,1482316,1482318,1463888,1500754,1482324,1482326,1482328,1482330,1482332,1482334],[1339920,1677844,1352216,1677852,1667664,1673812,1675864,1677916],[1339920,1708564,1352216,1708572,1667664,1673812,1708632,1708636,826396,425044,826460,1578512,1691156,1691160,1691164,1472080,1691220,1691224,1691228],[1564160,1566210,1572360,1574410,1578512,1582610,1582616,1582618,1492544,1510978,1513032,1513034,1472080,1472082,1513048,1513050],[1564160,1566210,1584648,1574410,1578512,1582610,1582616,1582618,1492544,1510978,1513032,1513034,1472080,1472082,1513048,1513050],[1578512,1691160,1472080,1513048],[1578512,1691160,1472080,1513048],[1649216,1651266,1653316,1663558,1700432,1671762,1673812,1682006],[1649216,1651266,1661508,1692230,1700432,1704530,1673812,1692246,676934,435284,676950,1492544,1508930,1494596,1494598,1472080,1472082,1494612,1494614],[1700432,1673812],[1700432,1673812,676948,1472080,1494612],[1492544,1506882,1472080,1472082],[1492544,1506882,1472080,1472082],[1472080],[1472080],[1307138,1350150,1458698,1458702,1503810,1503814,1458762,1458766,1494030,1494086,1494094,1338880,1349122,1351172,1351174,1572360,1570314,1568268,1494542,1492544,1504834,1494596,1494598,1488456,1486410,1488460,1494606],[1307138,1350150,1458698,1458702,1503810,1503814,1458762,1458766,734222,179270,676942,1338880,1566210,1568260,1494534,1584648,1574410,1568268,1494542,1492544,1510978,1494596,1494598,1488456,1513034,1488460,1494606],[],[],[1564160,1566210,1572360,1574410,1492544,1510978,1513032,1513034],[1564160,1566210,1584648,1574410,1492544,1510978,1513032,1513034],[],[],[1503810,1503814,676934,1490496,1504834,1494596,1494598],[1503810,1503814,179270,1492544,1508930,1494596,1494598],[],[],[1492544,1508930],[1492544,1508930],[],[]]

def rc14 : List (List ℕ) := [[1214984,1219082,1229336,1540634,1540648,1540650,1540664,1540666,246794,291864,1541146,289832,287786,291896,1541178,1519104,1521154,1523208,1523210,1535504,1535506,1541656,1541658,1535520,1535522,1541672,1541674,1535536,1535538,1541688,1541690],[1217032,1221130,1575448,1294874,1294888,1294890,1294904,1294906,1027082,453656,1092634,461864,1092650,453688,1092666,1519104,1521154,1584648,1584650,1582608,1537554,1582616,1582618,1545760,1551906,1584680,1551914,1537584,1537586,1582648,1582650],[1296920,1296952,1580056,1580088,1578512,1580568,1578544,1580600],[1575448,1294904,293912,293944,1578512,1691160,1537584,1691192],[1542696,1442346,1542712,1442362,1027082,453656,1543194,289832,1543210,453688,1543226,1529344,1531394,1525256,1533450,1527312,1537554,1527320,1543706,1547808,1549858,1543720,1543722,1537584,1537586,1543736,1543738],[1294888,1294890,1294904,1294906,1027082,453656,699418,461864,699434,453688,699450,1529344,1531394,1584648,1574410,1527312,1537554,1527320,1543706,1547808,1551906,1543720,1543722,1537584,1537586,1543736,1543738],[1516088,293912,367672,1578512,1605144,1537584,1543736],[1294904,293912,367672,1578512,1691160,1537584,1543736],[],[],[],[],[],[],[],[],[1223178,1442346,246794,302120,1553450,1529344,1533442,1572360,1533450,1545760,1549858,1553960,1553962],[1458698,1294890,1092618,461864,1092650,1529344,1566210,1584648,1574410,1545760,1551906,1553960,1551914],[],[],[1442346,1092618,461864,1092650,1529344,1531394,1572360,1533450,1547808,1549858,1553960,1553962],[1294890,1092618,461864,699434,1529344,1531394,1584648,1574410,1547808,1551906,1553960,1551914],[],[],[],[],[],[],[],[],[],[]]

def rc15 : List (List ℕ) := [[1321480,1569290,1335820,1587726,1575448,1587738,1335836,1587742,734222,734236,494622,1555968,1558018,1568260,1568262,1572360,1570314,1588748,1588750,1560080,1560082,1588756,1588758,1576472,1588762,1588764,1588766],[1321480,1569290,1335820,1587726,1575448,1587738,1335836,1587742,734222,453660,494622,1555968,1558018,1568260,1568262,1584648,1584650,1588748,1588750,1578512,1582610,1588756,1588758,1582616,1582618,1588764,1588766],[1575448,1354268,734236,1578512,1588756,1576472,1588764],[1575448,1354268,734236,1578512,1588756,1691160,1588764],[1564160,1566210,1572360,1574410,1578512,1582610,1582616,1582618],[1564160,1566210,1584648,1574410,1578512,1582610,1582616,1582618],[1578512,1691160],[1578512,1691160],[],[],[],[],[],[],[],[],[1458698,1458702,734222,1564160,1562114,1568260,1586694,1572360,1570314,1588748,1588750],[1458698,1458702,734222,1564160,1566210,1568260,1586694,1584648,1574410,1588748,1588750],[],[],[1564160,1566210,1572360,1574410],[1564160,1566210,1584648,1574410],[],[],[],[],[],[],[],[],[],[]]

def rc16 : List (List ℕ) := [[],[322592,758912,836768,1043712,1099040,1641856,1680800],[],[314416,783504,783536,1076480,1627408,1099040,1162544,1635712,1627536,1664416,1664432],[1311745,80928,1311777,537728,1311873,537760,1311905,939264,1312001,939296,1312033,1312128,1312129,1312160,1312161],[322592,758912,836768,1043712,1099040,1641856,1680800],[1692689,314416,1692721,783504,1692817,830640,1692849,1076480,1692929,1105168,1692945,941344,1692961,1162544,1692977,1600896,1693057,1627536,1693073,1664416,1693089,1664432,1693105],[314416,783504,830640,1076480,1627408,1099040,1162544,1635712,1627536,1664416,1664432],[],[140384,771200,836768,527552,595168,984384,1496416,1639808,1680800,1297856,1496544],[],[140400,1604752,830640,531664,734448,984384,984400,1496416,976240,1639808,1627536,1664416,1664432,1297856,1297872,1496544,1496560],[1342529,113760,1342561,752768,570497,570528,570529,527552,1342657,1342688,1342689,984384,1342785,961888,1342817,1484160,1484161,1484192,1484193,1484224,1342913,1342944,1342945],[140384,771200,836768,527552,595168,984384,1496416,1639808,1680800,1297856,1496544],[277585,975984,975985,1604752,1692817,830640,1692849,1502416,1502417,830704,1502449,984384,1342785,984400,976209,1496416,1342817,976240,976241,1639808,1693057,1627536,1693073,1664416,1693089,1664432,1693105,1664448,1342913,1496528,1502673,1342944,1342945,1496560,1502705],[140400,1604752,830640,531664,830704,984384,984400,1496416,976240,1639808,1627536,1664416,1664432,1297856,1297872,1496544,1496560],[1346561,1340419,87072,1346593,136226,1340451,754816,1346689,1287298,1340547,1346720,1346721,1340578,1340579,871680,1346817,873730,1340675,953632,1346849,955682,1340707,1234304,1346945,1287554,1340803,1346976,1346977,1340834,1340835],[322592,326690,758912,773250,836768,799906,1043712,1074434,1099040,1678626,1641856,1641858,1680800,1678754],[929024,1346817,957728,1346849,1285504,1346945,1346976,1346977],[1076480,1099040,1635712,1680800],[1709057,1709059,87072,1709089,326690,1709091,758912,1709185,773250,1709187,836768,1709217,799906,1709219,1043712,1709313,875778,1709315,959776,1709345,1678626,1709347,1641856,1709441,1641858,1709443,1670560,1709473,1678754,1709475],[322592,326690,758912,773250,836768,799906,1043712,1074434,1099040,1678626,1641856,1641858,1680800,1678754],[1076480,1019137,1099040,1019169,1635712,1705345,1680800,1705377],[1076480,1099040,1635712,1680800],[1576001,525379,140384,1576033,140386,1576035,767104,1352833,523394,1352835,797856,1352865,799906,1352867,527552,1576129,525506,525507,595168,1576161,799970,1576163,1017152,1576257,1017154,1576259,1017184,1576289,1017186,1576291,1236352,1353089,1236354,1353091,1353120,1353121,1353122,1353123,1297856,1576385,1297858,1576387,1576416,1576417,1576418,1576419],[140384,140386,771200,773250,836768,799906,527552,531650,595168,799970,984384,978242,1496416,978274,1639808,1641858,1680800,1678754,1297856,1297858,1496544,1496546],[1017152,1295681,1017184,1588577,1293696,1707393,1707424,1707425,1297856,1295809,1588704,1588705],[984384,1496416,1639808,1680800,1297856,1496544],[1354817,1008707,140384,1354849,140386,1008739,771200,1709185,773250,1709187,836768,1709217,799906,1709219,527552,1354945,773314,1354947,595168,1354977,799970,1354979,984384,1355073,984386,1008963,961888,1355105,1008994,1008995,1639808,1709441,1641858,1709443,1680800,1709473,1678754,1709475,1297856,1355201,1297858,1355203,1355232,1355233,1355234,1355235],[140384,140386,771200,773250,836768,799906,527552,531650,595168,799970,984384,978242,1496416,978274,1639808,1641858,1680800,1678754,1297856,1297858,1496544,1496546],[984384,1019201,1496416,1019233,1639808,1709441,1680800,1709473,1297856,1355201,1355232,1355233],[984384,1496416,1639808,1680800,1297856,1496544]]

def rc17 : List (List ℕ) := [[],[715908,1076480,1711364,1635712,1711492],[],[799892,1076480,1711364,1627408,1711380,1635712,1711492,1627536,1711508],[1076480,1019137,1635712,1693057],[1076480,1635712],[1076480,1019137,1105168,1692945,1635712,1693057,1627536,1693073],[1076480,1627408,1635712,1627536],[],[1481860,677060,994624,978244,1639808,1711492,1297856,1543620],[],[799892,677076,994624,978244,1297744,978260,1639808,1711492,1627536,1553812,1297856,1543620,1297872,1502676],[994624,1019201,1639808,1693057,1297856,1342913],[994624,1639808,1297856],[994624,1019201,1297744,976209,1639808,1693057,1443216,1443217,1297856,1342913,1297872,1355217],[994624,1297744,1639808,1627536,1297856,1297872],[226309,226311,1289348,1291397,1289350,1291399,929024,1346817,926978,1291523,1289476,1291525,1289478,1291527,1283456,1346945,1287554,1291651,1289604,1291653,1289606,1291655],[722052,732294,1076480,1074434,1711364,1711366,1635712,1641858,1711492,1711494],[929024,1346817,1289476,1291525,1285504,1346945,1289604,1291653],[1076480,1711364,1635712,1711492],[1076480,1019137,1074434,1701123,1635712,1705345,1641858,1701251],[1076480,1074434,1635712,1641858],[1076480,1019137,1635712,1705345],[1076480,1635712],[277573,277575,1440900,1295493,1516678,1295495,1516740,1295557,1516742,1295559,1017152,1295681,1017154,1295683,1084740,1295685,1711430,1295687,1293696,1353089,1707394,1353091,1441156,1295749,1516934,1295751,1297856,1295809,1297858,1295811,1516996,1295813,1516998,1295815],[1711236,732294,677060,677062,994624,978242,978244,978246,1639808,1641858,1711492,1711494,1297856,1297858,1711556,1711558],[1017152,1295681,1084740,1295685,1293696,1707393,1441156,1295749,1297856,1295809,1443268,1295813],[994624,978244,1639808,1711492,1297856,1711556],[994624,1019201,978242,978243,1639808,1709441,1641858,1709443,1297856,1355201,1297858,1355203],[994624,978242,1639808,1641858,1297856,1297858],[994624,1019201,1639808,1709441,1297856,1355201],[994624,1639808,1297856]]

def rc18 : List (List ℕ) := [[1645569,1649673,312352,1645601,787496,1649705,738432,1645697,742536,1649801,781472,1645729,787624,1649833,1039616,1645825,1594632,1649929,1643808,1645857,1649960,1649961,1590656,1645953,1594760,1650057,1643936,1645985,1650088,1650089],[322592,363560,758912,765064,836768,1703080,1043712,1047816,1099040,1682728,1641856,1641864,1680800,1682856],[1684497,1684505,1104944,1684529,789560,1684537,783504,1684625,789656,1684633,783536,1684657,789688,1684665,1072384,1651969,1053960,1651977,1105168,1684753,1684760,1684761,1094944,1652001,1652008,1652009,1105200,1684785,1684792,1684793,1596800,1652097,1596808,1652105,1617296,1684881,1684888,1684889,1648032,1652129,1652136,1652137,1684912,1684913,1684920,1684921],[314416,367672,783504,1627288,783536,830648,1076480,1053960,1627408,1090840,1099040,1682728,1162544,1682744,1635712,1637768,1627536,1627544,1664416,1664424,1664432,1664440],[1661953,1661961,312352,1661985,316456,1661993,740480,1662081,746632,1662089,785568,1662113,1653928,1662121,1043712,1662209,1598728,1662217,1099040,1662241,1654056,1662249,1592704,1662337,1598856,1662345,1662368,1662369,1654184,1662377],[322592,363560,758912,765064,836768,1703080,1043712,1047816,1099040,1682728,1641856,1641864,1680800,1682856],[1692689,1692697,314416,1692721,367672,1692729,783504,1692817,1627288,1692825,830640,1692849,830648,1692857,1076480,1692929,1053960,1692937,1105168,1692945,1627416,1692953,1099040,1692961,1682728,1692969,1162544,1692977,1682744,1692985,1600896,1693057,1600904,1693065,1627536,1693073,1627544,1693081,1664416,1693089,1664424,1693097,1664432,1693105,1664440,1693113],[314416,367672,783504,1627288,830640,830648,1076480,1053960,1627408,1090840,1099040,1682728,1162544,1682744,1635712,1637768,1627536,1627544,1664416,1664424,1664432,1664440],[748672,1657985,791712,1658017,1602944,1658241,1656224,1658273],[771200,836768,1639808,1680800],[1688720,1688721,1688752,1688753,1623424,1686913,1688976,1688977,1660320,1686945,1689008,1689009],[1604752,830640,1639808,1627536,1664416,1664432],[752768,1662081,816288,1662113,1639808,1662337,1662368,1662369],[771200,836768,1639808,1680800],[1604752,1688721,830640,1692849,1639808,1693057,1627536,1688977,1664416,1693089,1664432,1693105],[1604752,830640,1639808,1627536,1664416,1664432],[1668097,1668099,1700873,1700875,322592,1668129,795682,1668131,795688,1700905,795690,1700907,754816,1668225,756866,1668227,760968,1701001,795786,1701003,793760,1668257,795810,1668259,795816,1701033,795818,1701035,1039616,1668353,1041666,1668355,1047816,1701129,1045770,1701131,1101088,1668385,1101090,1668387,1101096,1701161,1101098,1701163,1607040,1668481,1609090,1668483,1611144,1701257,1701258,1701259,1666464,1668513,1668514,1668515,1701288,1701289,1701290,1701291],[322592,326690,363560,326698,758912,773250,765064,773258,836768,799906,1703080,799914,1043712,1074434,1047816,1082634,1099040,1678626,1682728,1682730,1641856,1641858,1641864,1641866,1680800,1678754,1682856,1682858],[1072384,1705217,1080584,1705225,1101088,1705249,1101096,1705257,1635712,1705345,1637768,1705353,1672608,1705377,1672616,1705385],[1076480,1090824,1099040,1682728,1635712,1637768,1680800,1682856],[1709057,1674243,1674249,1674251,322592,1709089,326690,1674275,363560,1674281,326698,1674283,758912,1709185,773250,1674371,765064,1674377,773258,1674379,836768,1709217,799906,1674403,1703080,1674409,799914,1674411,1043712,1709313,1074434,1674499,1047816,1674505,1082634,1674507,1099040,1709345,1674530,1674531,1674536,1674537,1674538,1674539,1641856,1709441,1641858,1674627,1641864,1674633,1641866,1674635,1670560,1709473,1674658,1674659,1674664,1674665,1674666,1674667],[322592,326690,363560,326698,758912,773250,765064,773258,836768,799906,1703080,799914,1043712,1074434,1047816,1082634,1099040,1678626,1682728,1682730,1641856,1641858,1641864,1641866,1680800,1678754,1682856,1682858],[1076480,1705217,1090824,1107209,1099040,1705249,1682728,1107241,1635712,1705345,1637768,1705353,1680800,1705377,1682856,1705385],[1076480,1090824,1099040,1682728,1635712,1637768,1680800,1682856],[767104,1709185,769154,1709187,797856,1709217,799906,1709219,1639808,1709441,1676674,1709443,1676704,1709473,1676706,1709475],[771200,773250,836768,799906,1639808,1641858,1680800,1678754],[1639808,1707393,1707424,1707425],[1639808,1680800],[771200,1709185,773250,1709187,836768,1709217,799906,1709219,1639808,1709441,1641858,1709443,1680800,1709473,1678754,1709475],[771200,773250,836768,799906,1639808,1641858,1680800,1678754],[1639808,1709441,1680800,1709473],[1639808,1680800]]

def rc19 : List (List ℕ) := [[226309,1629197,1621124,1629317,1621132,1629325,1072384,1629441,1051908,1629445,1139976,1629449,1051916,1629453,1613184,1629569,1621380,1629573,1619336,1629577,1621388,1629581],[1711236,1711244,1076480,1711364,1053960,1711372,1635712,1711492,1637768,1711500],[226325,1698845,1698964,1698965,1698972,1698973,1072384,1705217,1051908,1699077,1053960,1705225,1051916,1699085,1105168,1684753,1699092,1699093,1684760,1684761,1699100,1699101,1615232,1705345,1621380,1699205,1619336,1705353,1621388,1699213,1617296,1684881,1699220,1699221,1684888,1684889,1699228,1699229],[799892,799900,1076480,1711364,1053960,1711372,1627408,1711380,1090840,1711388,1635712,1711492,1637768,1711500,1627536,1711508,1627544,1711516],[1076480,1692929,1053960,1107209,1635712,1693057,1637768,1693065],[1076480,1053960,1635712,1637768],[1076480,1692929,1053960,1107209,1105168,1692945,1090840,1107225,1635712,1693057,1637768,1693065,1627536,1693073,1627544,1693081],[1076480,1053960,1627408,1090840,1635712,1637768,1627536,1627544],[1625220,1625221,1623424,1686913,1625476,1625477],[1711236,1639808,1711492],[1625236,1625237,1623424,1686913,1625476,1625477,1688976,1688977,1625492,1625493],[799892,1639808,1711492,1627536,1695124],[1639808,1693057],[1639808],[1639808,1693057,1627536,1688977],[1639808,1627536],[226309,226311,490509,490511,1696900,1696901,1696902,1696903,1696908,1696909,1696910,1696911,1072384,1633537,1070338,1633539,1697028,1697029,1697030,1697031,1078536,1701129,1082634,1701131,1697036,1697037,1697038,1697039,1631616,1633665,1633666,1633667,1697156,1697157,1697158,1697159,1637768,1701257,1701258,1701259,1697164,1697165,1697166,1697167],[1711236,777350,1711244,777358,1076480,1074434,1711364,1711366,1090824,1082634,1711372,1711374,1635712,1641858,1711492,1711494,1637768,1641866,1711500,1711502],[1072384,1705217,1697028,1697029,1080584,1705225,1697036,1697037,1635712,1705345,1697156,1697157,1637768,1705353,1697164,1697165],[1076480,1711364,1090824,1711372,1635712,1711492,1637768,1711500],[1076480,1705217,1074434,1701123,1090824,1107209,1082634,1107211,1635712,1705345,1641858,1701251,1637768,1701257,1641866,1701259],[1076480,1074434,1090824,1082634,1635712,1641858,1637768,1641866],[1076480,1705217,1090824,1107209,1635712,1705345,1637768,1705353],[1076480,1090824,1635712,1637768],[1711236,1709189,1711238,1709191,1639808,1707393,1707394,1707395,1711492,1709445,1711494,1709447],[1711236,777350,1639808,1641858,1711492,1711494],[1639808,1707393,1711492,1709445],[1639808,1711492],[1639808,1709441,1641858,1709443],[1639808,1641858],[1639808,1709441],[1639808]]

def rc20 : List (List ℕ) := [[],[367656,1006688,1021032,1053960,1682728,984384,1021256,1006944,1021288],[],[367672,490608,488568,1053960,1090840,1682728,1172792,984384,1021256,984400,1021272,1006944,1021288,1162608,1021304],[1018889,1012776,1018921,1018945,498761,1006688,1018977,1012840,1018985,1053960,1019145,1013032,1019177,984384,1019201,1387848,1019209,1006944,1019233,1013096,1019241],[367656,1006688,1021032,1053960,1682728,984384,1021256,1006944,1021288],[478233,1516600,973881,400465,478297,834672,834673,834680,834681,1053960,974089,1627416,974105,1013032,974121,1516856,974137,984384,1019201,1189192,1019209,984400,1693009,1189208,1119577,1006944,1019233,1013096,1019241,1162608,1693041,1189240,1693049],[367672,834672,488568,1053960,1090840,1682728,1682744,984384,1021256,984400,1021272,1006944,1021288,1162608,1021304],[],[1006688,984384,1006944],[],[490608,984384,984400,1006944,1193328],[1018945,1006688,1018977,984384,1019201,1006944,1019233],[1006688,984384,1006944],[439377,834672,834673,984384,1019201,984400,1150289,1006944,1019233,1496432,1502577],[834672,984384,984400,1006944,1496432],[1000457,838667,1174568,1000489,1174570,838699,1000513,838723,838729,838731,476256,1000545,476258,838755,1174632,838761,1014890,838763,1197320,1000713,1197322,1000715,1197352,1000745,1197354,1000747,1004864,1000769,1015106,1000771,1197384,1000777,1015114,1000779,1004896,1000801,1015138,1000803,1197416,1000809,1015146,1000811],[367656,367658,1006688,1021026,1021032,1021034,1090824,1090826,1682728,1678634,984384,984386,1021256,1021258,1006944,1021282,1021288,1021290],[1086728,974089,1199400,974121,1004864,1011009,1199432,1011017,1004896,1011041,1199464,1011049],[1090824,1682728,984384,1021256,1006944,1021288],[1018889,838667,1012776,1018921,971818,838699,1018945,838723,498761,838731,1006688,1018977,1021026,838755,1012840,838761,1021034,838763,1090824,1019145,1090826,1107211,1013032,1019177,972074,1107243,984384,1019201,984386,1021251,1021256,1019209,1021258,1021259,1006944,1019233,1021282,1021283,1013096,1019241,1021290,1021291],[367656,367658,1006688,1021026,1021032,1021034,1090824,1090826,1682728,1678634,984384,984386,1021256,1021258,1006944,1021282,1021288,1021290],[1090824,974089,1013032,974121,984384,1019201,1021256,1019209,1006944,1019233,1013096,1019241],[1090824,1682728,984384,1021256,1006944,1021288],[187457,838723,187488,187489,476258,838755,1017152,1000769,1015106,1000771,1017184,1000801,1015138,1000803],[1006688,840802,984384,984386,1006944,1008994],[1017152,1185089,1017184,1185121],[984384,1006944],[1018945,838723,1006688,1018977,840802,838755,984384,1019201,984386,1008963,1006944,1019233,1008994,1008995],[1006688,840802,984384,984386,1006944,1008994],[984384,1019201,1006944,1019233],[984384,1006944]]

def rc21 : List (List ℕ) := [[],[1053960,1711372,994624,1711428,1021256,1021260],[],[1053960,1711372,1090840,1021212,994624,1711428,1021256,1021260,1627472,1021268,1021272,1021276],[1053960,974089,994624,1019201,1021256,1019209],[1053960,994624,1021256],[1053960,974089,1090840,974105,994624,1019201,1021256,1019209,1627472,1510737,1021272,1021273],[1053960,1090840,994624,1021256,1627472,1021272],[],[994624,1156420],[],[994624,1156420,1432912,1021268],[994624,1019201],[994624],[994624,1019201,1502544,1142097],[994624,1502544],[674829,674831,400453,400455,674893,674895,1086728,969993,1197322,1197323,1088780,1010957,1088782,1010959,1004864,1011009,1015106,1011011,1011012,1011013,1011014,1011015,1197384,1011017,1015114,1011019,1011020,1011021,1011022,1011023],[1090824,1090826,1711372,1092878,994624,1514818,1711428,1711430,1021256,1021258,1021260,1021262],[1086728,974089,1088780,974093,1004864,1011009,1011012,1011013,1199432,1011017,1011020,1011021],[1090824,1711372,994624,1711428,1021256,1021260],[1090824,974089,1090826,974091,994624,1019201,1514818,1021251,1021256,1019209,1021258,1021259],[1090824,1090826,994624,1514818,1021256,1021258],[1090824,974089,994624,1019201,1021256,1019209],[1090824,994624,1021256],[439365,439367,1017152,1193281,1015106,1015107,1156420,1156421,1156422,1156423],[994624,1008962,1156420,1008966],[1017152,1193281,1156420,1156421],[994624,1156420],[994624,1019201,1008962,1008963],[994624,1008962],[994624,1019201],[994624]]

def rc22 : List (List ℕ) := [[1106953,1174568,1106985,1111304,1107209,1174824,1107241],[367656,1053960,1682728],[1106969,719928,1107001,1053960,1107209,1088792,1107225,1199400,1107241,1199416,1107257],[367672,1053960,1090840,1682728,1682744],[844809,367656,844841,1053960,1107209,1682728,1107241],[367656,1053960,1682728],[1106969,367672,1107001,1053960,1107209,1627416,1107225,1682728,1107241,1682744,1107257],[367672,1053960,1090840,1682728,1682744],[],[],[],[],[],[],[],[],[1106953,838667,1174568,1106985,1174570,838699,1197320,1107209,1197322,1107211,1197352,1107241,1197354,1107243],[367656,367658,1090824,1090826,1682728,1682730],[1086728,1107209,1199400,1107241],[1090824,1682728],[844809,838667,367656,844841,367658,838699,1090824,1107209,1090826,1107211,1682728,1107241,1682730,1107243],[367656,367658,1090824,1090826,1682728,1682730],[1090824,1107209,1682728,1107241],[1090824,1682728],[],[],[],[],[],[],[],[]]

def rc23 : List (List ℕ) := [[734221,1086728,1107209,1088780,1107213],[1053960,1711372],[734237,1053960,1107209,1088780,1107213,1088792,1107225,1088796,1107229],[1053960,1711372,1090840,1711388],[1053960,1107209],[1053960],[1053960,1107209,1090840,1107225],[1053960,1090840],[],[],[],[],[],[],[],[],[734221,734223,1086728,1107209,1197322,1107211,1088780,1107213,1088782,1107215],[1090824,1090826,1711372,1092878],[1086728,1107209,1088780,1107213],[1090824,1711372],[1090824,1107209,1090826,1107211],[1090824,1090826],[1090824,1107209],[1090824],[],[],[],[],[],[],[],[]]

def rc24 : List (List ℕ) := [[],[353312,840738,347184,832562,773250,1604752,832658,836768,840866,832688,832690],[],[347184,1604752,830640],[590851,590865,590867,107552,590881,109602,590883,130096,590897,588850,590899,588930,590979,586896,590993,588946,590995,562336,591009,588962,591011,586928,591025,588978,591027],[353312,840738,347184,832562,773250,1604752,832658,836768,840866,832688,832690],[695313,347184,1692721,1604752,695441,830640,1692849],[347184,1604752,830640],[],[140384,140386,975984,832626,773250,1604752,832658,836768,840866,832688,832690,531650,531664,531666,595168,840930,832752,832754],[],[490608,1604752,830640,531664,734448],[1342531,273489,975955,113760,1342561,666722,1342563,975984,975985,666738,975987,570498,570499,1604752,1344657,666770,1344659,570528,570529,570530,570531,1344688,1344689,666802,1344691,773314,1342659,1604816,1344721,666834,1344723,1342688,1342689,666850,1342691,1344752,1344753,666866,1344755],[140384,140386,975984,832626,773250,1604752,832658,836768,840866,832688,832690,531650,531664,531666,595168,840930,832752,832754],[277585,975984,975985,1604752,695441,830640,1692849,736464,736465,830704,1502449],[834672,1604752,830640,531664,830704],[838659,138272,1346593,136226,838691,1287298,838787,836768,1346721,838818,838819],[353312,840738,773250,836768,840866],[],[],[838659,138272,1709089,840738,838691,773250,838787,836768,1709217,838818,838819],[353312,840738,773250,836768,840866],[],[],[838723,140384,187489,140386,838755,779394,838787,836768,1352865,838818,838819,720066,838851,595168,1354977,720098,838883],[140384,140386,773250,836768,840866,531650,595168,840930],[],[],[838723,140384,1354849,140386,838755,773250,838787,836768,1709217,838818,838819,720066,838851,595168,1354977,838882,838883],[140384,140386,773250,836768,840866,531650,595168,840930],[],[]]

def rc25 : List (List ℕ) := [[],[724102,722068,677014],[],[826516],[],[],[],[],[],[777350,826516,677014,677062,677076,677078],[],[826516,677076],[],[],[],[],[490503,777350,699527],[777350],[],[],[],[],[],[],[277575,777350,699527,777414,699591],[777350,677062],[],[],[],[],[],[]]

def rc26 : List (List ℕ) := [[824323,822283,820241,820243,820249,820251,332832,824353,328738,824355,338984,824361,365610,822315,349232,820273,345138,820275,349240,820281,365626,820283,750722,824451,744586,822411,820368,820369,820370,820371,820376,820377,820378,820379,801952,824481,814242,824483,806056,824489,822442,822443,820400,820401,820402,820403,820408,820409,820410,820411],[353312,840738,363560,840746,347184,832562,363576,832570,773250,773258,1604752,832658,1604760,832666,836768,840866,1703080,840874,832688,832690,832696,832698],[695313,828441,1104944,732209,367672,828473,775312,828561,775320,828569,828592,828593,828600,828601],[347184,367672,1604752,1604760,830640,830648],[844803,844811,844817,844819,844825,844827,332832,844833,334882,844835,343080,807977,365610,844843,349232,844849,832562,844851,349240,844857,365626,844859,773250,844931,773258,844939,1604752,844945,832658,844947,1604760,844953,832666,844955,804000,844961,810146,844963,808104,808105,810154,844971,832688,844977,832690,844979,832696,844985,832698,844987],[353312,840738,363560,840746,347184,832562,363576,832570,773250,773258,1604752,832658,1604760,832666,836768,840866,1703080,840874,832688,832690,832696,832698],[695313,828441,347184,828465,367672,828473,1604752,828561,1604760,828569,828592,828593,828600,828601],[347184,367672,1604752,1604760,830640,830648],[750722,824451,775312,824465,842898,824467,812192,824481,814242,824483,828592,824497,842930,824499],[773250,1604752,832658,836768,840866,832688,832690],[775312,828561,828592,828593],[1604752,830640],[773250,844931,1604752,828561,832658,844947,816288,844961,816290,844963,828592,828593,832690,844979],[773250,1604752,832658,836768,840866,832688,832690],[1604752,828561,828592,828593],[1604752,830640],[838659,838667,353312,844833,351266,838691,363560,844841,365610,838699,763010,838787,763018,838795,836768,844961,838818,838819,1703080,844969,838826,838827],[353312,840738,363560,840746,773250,773258,836768,840866,1703080,840874],[],[],[838659,838667,353312,844833,840738,838691,363560,844841,365610,838699,773250,838787,773258,838795,836768,844961,838818,838819,1703080,844969,838826,838827],[353312,840738,363560,840746,773250,773258,836768,840866,1703080,840874],[],[],[779394,838787,836768,844961,838818,838819],[773250,836768,840866],[],[],[773250,838787,836768,844961,838818,838819],[773250,836768,840866],[],[]]

def rc27 : List (List ℕ) := [[699399,699407,355349,699415,439325,699423,777350,777351,777358,777359,1694868,777365,777366,777367,1694876,777373,777374,777375],[777350,777358,826516,777366,826524,777374],[439317,439325,1678484,777365,1694876,777373],[826516,826524],[],[],[],[],[777350,777351,826516,777365,777366,777367],[777350,826516,777366],[826516,777365],[826516],[],[],[],[],[490503,490511,777350,777351,777358,777359],[777350,777358],[],[],[],[],[],[],[777350,777351],[777350],[],[],[],[],[],[]]

def rc28 : List (List ℕ) := [[],[367656,367658,367672,367674,1006688,840802,1021032,498794,1006704,832626,1021048,498810],[],[367672,490608,834680],[1018891,1018905,498715,1012776,1018921,971818,1018923,1012792,1018937,971834,1018939,498755,498763,433233,498771,498777,498779,1006688,1018977,1006690,1018979,1012840,1018985,1012842,1018987,1006704,1018993,1006706,1018995,1012856,1019001,1012858,1019003],[367656,367658,367672,367674,1006688,840802,1021032,840810,1006704,832626,1021048,832634],[695321,1516600,973881,439377,496729,834672,834673,834680,834681],[367672,834672,834680],[],[1006688,840802,490608,490610],[],[490608],[498755,433233,498771,1006688,1018977,666722,1018979,1006704,1018993,666738,1018995],[1006688,840802,834672,832626],[439377,834672,834673],[834672],[838667,1012776,156713,971818,838699,838723,838731,187488,187489,1195106,838755,1012840,498793,1195114,838763],[367656,367658,1006688,840802,1021032,840810],[],[],[838667,1012776,1018921,840746,838699,838723,838731,1006688,1018977,840802,838755,1012840,838761,840810,838763],[367656,367658,1006688,840802,1021032,840810],[],[],[490563,187488,187489,1008738,490595],[1006688,840802],[],[],[838723,1006688,1018977,840802,838755],[1006688,840802],[],[]]

def rc29 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[494607,490567,494671],[],[],[],[],[],[],[],[490567],[],[],[],[],[],[],[]]

def rc30 : List (List ℕ) := [[824331,824345,498715,367656,824361,367658,824363,367672,824377,367674,498747],[367656,367658,367672,367674],[828441,367672,828473],[367672],[844811,844825,498715,367656,844841,367658,844843,367672,844857,367674,844859],[367656,367658,367672,367674],[828441,367672,828473],[367672],[],[],[],[],[],[],[],[],[838667,367656,844841,367658,838699],[367656,367658],[],[],[838667,367656,844841,367658,838699],[367656,367658],[],[],[],[],[],[],[],[],[],[]]

def rc31 : List (List ℕ) := [[494607,494621,494623],[],[494621],[],[],[],[],[],[],[],[],[],[],[],[],[],[494607],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc32 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc33 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc34 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc35 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc36 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc37 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc38 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc39 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc40 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc41 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc42 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc43 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc44 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc45 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc46 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc47 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc48 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc49 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc50 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc51 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc52 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc53 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc54 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc55 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc56 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc57 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc58 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc59 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc60 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc61 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc62 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc63 : List (List ℕ) := [[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]

def rc : List (List (List ℕ)) := [rc0,rc1,rc2,rc3,rc4,rc5,rc6,rc7,rc8,rc9,rc10,rc11,rc12,rc13,rc14,rc15,rc16,rc17,rc18,rc19,rc20,rc21,rc22,rc23,rc24,rc25,rc26,rc27,rc28,rc29,rc30,rc31,rc32,rc33,rc34,rc35,rc36,rc37,rc38,rc39,rc40,rc41,rc42,rc43,rc44,rc45,rc46,rc47,rc48,rc49,rc50,rc51,rc52,rc53,rc54,rc55,rc56,rc57,rc58,rc59,rc60,rc61,rc62,rc63]

def rawWitness (a : ℕ) := groupedAt rc a []


def fastHull (a b : ℕ) :=
  shapeHull (fromParts nSmall nLarge a &&& fromParts nSmall nLarge b)
    (fromParts pSmall pLarge a &&& fromParts pSmall pLarge b)

lemma fastHullEq {a b : ℕ} (ha : a < 2048) (hb : b < 2048) : fastHull a b =
    shapeHull (signature negRows a b) (signature posRows a b) := by
  rw [joinedSignature negRows,joinedSignature posRows,nParts ha,nParts hb,pParts ha,pParts hb,fastHull]

def checkRaw (a : ℕ) :=
  let rcodes := rawWitness a
  below (domainFor absTable meetTable a &&& (bigOnes 2048 <<< a)) (listedCode rcodes) &&
  rcodes.all fun w => decide (w/2048 < hCount) && underHull (fastHull a (w%2048)) (hullAt (w/2048))

lemma rawInHull (checked : window 0 2048 checkRaw = true) {a b : ℕ} (ok : shapeOK a b) :
    ∃ i < hCount, underHull (shapeHull (signature negRows a b) (signature posRows a b)) (hullAt i) = true := by
  have aSmall := ok.1.trans_lt ok.2.1
  have check := windowIndex checked aSmall
  obtain ⟨dc,rows⟩ := (Bool.and_eq_true_iff).1 check
  have permitted := domainForSound absVerified meetVerified ok
  have afterBit : ((bigOnes 2048) <<< a).testBit b = true := by
    rw [Nat.testBit_shiftLeft]
    simp [ok.1,onesOn (show b-a < 2048 from (Nat.sub_le _ _).trans_lt ok.2.1)]
  have available := belowBit dc (show (domainFor absTable meetTable a &&& (bigOnes 2048 <<< a)).testBit b = true by
    simp [Nat.testBit_and,permitted,afterBit])
  obtain ⟨w,hw,eq⟩ := listedBit available
  have cw := (Bool.and_eq_true_iff).1 (List.all_eq_true.mp rows w hw)
  refine ⟨w/2048,of_decide_eq_true cw.1,?_⟩
  simpa only [eq,fastHullEq aSmall ok.2.1] using cw.2


lemma rawWin0 : window 0 32 checkRaw = true := by decide +kernel

lemma rawWin1 : window 32 32 checkRaw = true := by decide +kernel

lemma rawWin2 : window 64 32 checkRaw = true := by decide +kernel

lemma rawWin3 : window 96 32 checkRaw = true := by decide +kernel

lemma rawWin4 : window 128 32 checkRaw = true := by decide +kernel

lemma rawWin5 : window 160 32 checkRaw = true := by decide +kernel

lemma rawWin6 : window 192 32 checkRaw = true := by decide +kernel

lemma rawWin7 : window 224 32 checkRaw = true := by decide +kernel

lemma rawWin8 : window 256 32 checkRaw = true := by decide +kernel

lemma rawWin9 : window 288 32 checkRaw = true := by decide +kernel

lemma rawWin10 : window 320 32 checkRaw = true := by decide +kernel

lemma rawWin11 : window 352 32 checkRaw = true := by decide +kernel

lemma rawWin12 : window 384 32 checkRaw = true := by decide +kernel

lemma rawWin13 : window 416 32 checkRaw = true := by decide +kernel

lemma rawWin14 : window 448 32 checkRaw = true := by decide +kernel

lemma rawWin15 : window 480 32 checkRaw = true := by decide +kernel

lemma rawWin16 : window 512 32 checkRaw = true := by decide +kernel

lemma rawWin17 : window 544 32 checkRaw = true := by decide +kernel

lemma rawWin18 : window 576 32 checkRaw = true := by decide +kernel

lemma rawWin19 : window 608 32 checkRaw = true := by decide +kernel

lemma rawWin20 : window 640 32 checkRaw = true := by decide +kernel

lemma rawWin21 : window 672 32 checkRaw = true := by decide +kernel

lemma rawWin22 : window 704 32 checkRaw = true := by decide +kernel

lemma rawWin23 : window 736 32 checkRaw = true := by decide +kernel

lemma rawWin24 : window 768 32 checkRaw = true := by decide +kernel

lemma rawWin25 : window 800 32 checkRaw = true := by decide +kernel

lemma rawWin26 : window 832 32 checkRaw = true := by decide +kernel

lemma rawWin27 : window 864 32 checkRaw = true := by decide +kernel

lemma rawWin28 : window 896 32 checkRaw = true := by decide +kernel

lemma rawWin29 : window 928 32 checkRaw = true := by decide +kernel

lemma rawWin30 : window 960 32 checkRaw = true := by decide +kernel

lemma rawWin31 : window 992 32 checkRaw = true := by decide +kernel

lemma rawWin32 : window 1024 32 checkRaw = true := by decide +kernel

lemma rawWin33 : window 1056 32 checkRaw = true := by decide +kernel

lemma rawWin34 : window 1088 32 checkRaw = true := by decide +kernel

lemma rawWin35 : window 1120 32 checkRaw = true := by decide +kernel

lemma rawWin36 : window 1152 32 checkRaw = true := by decide +kernel

lemma rawWin37 : window 1184 32 checkRaw = true := by decide +kernel

lemma rawWin38 : window 1216 32 checkRaw = true := by decide +kernel

lemma rawWin39 : window 1248 32 checkRaw = true := by decide +kernel

lemma rawWin40 : window 1280 32 checkRaw = true := by decide +kernel

lemma rawWin41 : window 1312 32 checkRaw = true := by decide +kernel

lemma rawWin42 : window 1344 32 checkRaw = true := by decide +kernel

lemma rawWin43 : window 1376 32 checkRaw = true := by decide +kernel

lemma rawWin44 : window 1408 32 checkRaw = true := by decide +kernel

lemma rawWin45 : window 1440 32 checkRaw = true := by decide +kernel

lemma rawWin46 : window 1472 32 checkRaw = true := by decide +kernel

lemma rawWin47 : window 1504 32 checkRaw = true := by decide +kernel

lemma rawWin48 : window 1536 32 checkRaw = true := by decide +kernel

lemma rawWin49 : window 1568 32 checkRaw = true := by decide +kernel

lemma rawWin50 : window 1600 32 checkRaw = true := by decide +kernel

lemma rawWin51 : window 1632 32 checkRaw = true := by decide +kernel

lemma rawWin52 : window 1664 32 checkRaw = true := by decide +kernel

lemma rawWin53 : window 1696 32 checkRaw = true := by decide +kernel

lemma rawWin54 : window 1728 32 checkRaw = true := by decide +kernel

lemma rawWin55 : window 1760 32 checkRaw = true := by decide +kernel

lemma rawWin56 : window 1792 32 checkRaw = true := by decide +kernel

lemma rawWin57 : window 1824 32 checkRaw = true := by decide +kernel

lemma rawWin58 : window 1856 32 checkRaw = true := by decide +kernel

lemma rawWin59 : window 1888 32 checkRaw = true := by decide +kernel

lemma rawWin60 : window 1920 32 checkRaw = true := by decide +kernel

lemma rawWin61 : window 1952 32 checkRaw = true := by decide +kernel

lemma rawWin62 : window 1984 32 checkRaw = true := by decide +kernel

lemma rawWin63 : window 2016 32 checkRaw = true := by decide +kernel

lemma rawWinAll : window 0 2048 checkRaw = true := (joinWindow (s:=0) (n:=1024) (m:=1024) (joinWindow (s:=0) (n:=512) (m:=512) (joinWindow (s:=0) (n:=256) (m:=256) (joinWindow (s:=0) (n:=128) (m:=128) (joinWindow (s:=0) (n:=64) (m:=64) (joinWindow (s:=0) (n:=32) (m:=32) rawWin0 rawWin1) (joinWindow (s:=64) (n:=32) (m:=32) rawWin2 rawWin3)) (joinWindow (s:=128) (n:=64) (m:=64) (joinWindow (s:=128) (n:=32) (m:=32) rawWin4 rawWin5) (joinWindow (s:=192) (n:=32) (m:=32) rawWin6 rawWin7))) (joinWindow (s:=256) (n:=128) (m:=128) (joinWindow (s:=256) (n:=64) (m:=64) (joinWindow (s:=256) (n:=32) (m:=32) rawWin8 rawWin9) (joinWindow (s:=320) (n:=32) (m:=32) rawWin10 rawWin11)) (joinWindow (s:=384) (n:=64) (m:=64) (joinWindow (s:=384) (n:=32) (m:=32) rawWin12 rawWin13) (joinWindow (s:=448) (n:=32) (m:=32) rawWin14 rawWin15)))) (joinWindow (s:=512) (n:=256) (m:=256) (joinWindow (s:=512) (n:=128) (m:=128) (joinWindow (s:=512) (n:=64) (m:=64) (joinWindow (s:=512) (n:=32) (m:=32) rawWin16 rawWin17) (joinWindow (s:=576) (n:=32) (m:=32) rawWin18 rawWin19)) (joinWindow (s:=640) (n:=64) (m:=64) (joinWindow (s:=640) (n:=32) (m:=32) rawWin20 rawWin21) (joinWindow (s:=704) (n:=32) (m:=32) rawWin22 rawWin23))) (joinWindow (s:=768) (n:=128) (m:=128) (joinWindow (s:=768) (n:=64) (m:=64) (joinWindow (s:=768) (n:=32) (m:=32) rawWin24 rawWin25) (joinWindow (s:=832) (n:=32) (m:=32) rawWin26 rawWin27)) (joinWindow (s:=896) (n:=64) (m:=64) (joinWindow (s:=896) (n:=32) (m:=32) rawWin28 rawWin29) (joinWindow (s:=960) (n:=32) (m:=32) rawWin30 rawWin31))))) (joinWindow (s:=1024) (n:=512) (m:=512) (joinWindow (s:=1024) (n:=256) (m:=256) (joinWindow (s:=1024) (n:=128) (m:=128) (joinWindow (s:=1024) (n:=64) (m:=64) (joinWindow (s:=1024) (n:=32) (m:=32) rawWin32 rawWin33) (joinWindow (s:=1088) (n:=32) (m:=32) rawWin34 rawWin35)) (joinWindow (s:=1152) (n:=64) (m:=64) (joinWindow (s:=1152) (n:=32) (m:=32) rawWin36 rawWin37) (joinWindow (s:=1216) (n:=32) (m:=32) rawWin38 rawWin39))) (joinWindow (s:=1280) (n:=128) (m:=128) (joinWindow (s:=1280) (n:=64) (m:=64) (joinWindow (s:=1280) (n:=32) (m:=32) rawWin40 rawWin41) (joinWindow (s:=1344) (n:=32) (m:=32) rawWin42 rawWin43)) (joinWindow (s:=1408) (n:=64) (m:=64) (joinWindow (s:=1408) (n:=32) (m:=32) rawWin44 rawWin45) (joinWindow (s:=1472) (n:=32) (m:=32) rawWin46 rawWin47)))) (joinWindow (s:=1536) (n:=256) (m:=256) (joinWindow (s:=1536) (n:=128) (m:=128) (joinWindow (s:=1536) (n:=64) (m:=64) (joinWindow (s:=1536) (n:=32) (m:=32) rawWin48 rawWin49) (joinWindow (s:=1600) (n:=32) (m:=32) rawWin50 rawWin51)) (joinWindow (s:=1664) (n:=64) (m:=64) (joinWindow (s:=1664) (n:=32) (m:=32) rawWin52 rawWin53) (joinWindow (s:=1728) (n:=32) (m:=32) rawWin54 rawWin55))) (joinWindow (s:=1792) (n:=128) (m:=128) (joinWindow (s:=1792) (n:=64) (m:=64) (joinWindow (s:=1792) (n:=32) (m:=32) rawWin56 rawWin57) (joinWindow (s:=1856) (n:=32) (m:=32) rawWin58 rawWin59)) (joinWindow (s:=1920) (n:=64) (m:=64) (joinWindow (s:=1920) (n:=32) (m:=32) rawWin60 rawWin61) (joinWindow (s:=1984) (n:=32) (m:=32) rawWin62 rawWin63))))))


def guardCols : List ℕ := [0x88004200000000000000000000020000c00000002000400000000000000000000880000000000200108866120000000000025000140380000000080000008102110000000000000008000000880000000000324100000a00a10a1c80201024f,0x3024000400400000000c0100000000100000000080000000000005103010040712000000000000000000000000000048003003000080000001801081030800000000000082800810000020000160088017251a24f,0xc00000070000400000000000000000000000000000a3060010032002000000420002100000000000050008000000090001000000000000000801004210204000000110420000008001084d94241220f,0xc0014024101c0000004000a009040080000000000000000000000005a4000000001000000000000000000000000001800503000c000011020011000000000180160f0000000000000180001443306e000000080000001000f,0x10049000000000000000000000000000ac000003c00000000009c000000104000003c143800001000008d7001200e00e00000000000610000000000000000800c10f01000100000000000000080000000310000b90009c4000000000032f8f8268b1e8f,0x170000000100000000000000000002400001840000000002100000000000e00000002888000040000500d91a8f6120000000000017000000000000000081ff073060010000000000000004a00000000000006800032110000000fe33a88016899a4f,0xe0c8f8b409cc1fd00000000004004000000004080020000210120020020000000116db700000000000000c080006d11f480d000000000019125a0000000400000024c811d40001000011080cc0201021f,0x32c00004500000000000000006c000000000640002604000000000630000000180000000110d801000020c000000100860d00000007200025000000000000d001800000078303400000100000000080047005000018181d8363f00000010a80a0800001007f,0x24140547c7e0fb4400800200000000880000000000080010e30f03b47d6034000001b600b0500180001000250908000000281850055000000003060800040fb8080000001ffe032040fa45a0aa7d801c169ef,0x180fbefc07bf0fc33ec00fdebc019fc1f0c0fc000000102000000000000000000000f14007e03010e0000000000000004000000ed1f003c0002b71b000d010065500680521e00000003224022800110c6000000000059879e253268f,0x220c00000001004000408400000000400000000000000000000000000000000051003b47d003400000000000000000000000003001800000002003400000007ffdbf6ff00000000000fff81dffe3f00000003601880001ffe9cf]

def edgeCols : List ℕ := [0x8800420180c36c805280d80340023ccbc001481620064000000000000000000008800000000000006c03030e00000000000000001402808818003400002691020d0000000000000000000000880000000000220100000000005194000000041,0x880042000000000000000000000200008000000020004000000000000000000008800000000000000000020200000000000000001402800000000000000081020100000005ce50f03100000088000a7e0187fa0d000000000000140000681c1,0x1400100000000000001200004c41000000000000000000000000000000000000000000000000000000000000000000010000900008c00000000000000030404b1e82,0x201005068580380000800000000000000000000000000000820e2330640434000000000000000000000000000000000000000000000000000000000000000000000000000000000000484480a200041c00202,0x1800000000000000000000000000000000000000000000500d81a800000000000000000000000000000000001f0070060000000000000000000001004210204000000100020000008f033848116802004,0x7ce58f0c601004210204e7e01c7f03200000080010048102386804,0x28140000001000000000000000000001000000000001900580000000000000024c801d400000000000000000000008,0x30000004000000000000000006000000000060000260000000000063000000000000000000000000000000000000000000000000004000020000000100000c00180000007800340000000000000000000000000000000000004000000000000000000000008,0x24140007c7e00044000000000000000003c0038000000010e30303b400e00000000000000000000000000000000000000000000000000000000000000000000300000b8000000000007a05a000038000b0000,0x3c00380000000000003000000e00000000000000000000000000000000000000000000000000007ffdbf60000000003100fff81dffe00000000000000038003fffc0,0x20000007c7e0fb000000000000000000000000000000001000030fb5fd00000000000000000000000000000000001ff0730000000000000000000000000000000000000000000000007a4fe3ba81817c00000,0x180fbefc0000000000000fdfbc000000000000000000000000000000000000000000f5400000000000000000000000000000000ed1f00001ff2f71f0000000000000000000000000000000000000000000000000fe37b8c000000000,0x32c00004500000000000000006c00000000064000000000000000000000000000000000000000000000000000000000000000000005216db7000000000000d0018000000000000000000000019125a000000000000000000000000000000000000000000000,0x16db70000000000000000000000000000000000007ffdbf6ff00000000000fffa5dfffff00000000000000000000000,0x32c0000450000000000180fbefc07bf0fc33ec00ffebc019fc1f0c6fc00000000000000000000000000000000000000000000000005200025000000000ed1f003c0002b77b003d0000000000000000000000000000000000000000000000000000000000000,0x180fbefc07bf0fc33ec24fdefc7dffcff4c0fc00000000000000000000000000000ef1f03fc7f613e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]

def negativeCols : List ℕ := [0xd02aa02c00200102110220917100c10c085008c28b400000c210050a100146000801224900032938406341000000000005616098acc088c4212a01028840a0428038c0b23a0120505c2c00082a23487800f010098940408e5863c2c9bc0000400602f022285ae5d80,0x8d7a00280860490310042c304226c45c185680010f408008c016234800035614c0080a0910033c300c772410000010201f8c0001418e8040000281081180386080184cb23700205041ec0c0932e3705f01f038280464c8bf806ff801bc0000702f005000418000020,0x304d50750a840002255208007506799f205284c8034219f3e714014896014625090e4108004ccc6000010100011e9aad026e1308ac830d02618800068dca0032607c20b2400f8078182c0a0b8004001080301c250524000a100184488c00002100080023080060580,0x5eb8be700884400b3c26000043461cfe22d2854907433dffe01021489603561490401e0910635c240c754010410fe700726c570140f00507c002800c058b0822601cacb2400a807801ec0e1934cb745f403039850e04a03fe02fff008c800001c00c80403c9706020,0x5108842082a8200c11530184eac0c54ca4c20eda8b40090002000502100380000864244c204a114a254260835b820000056160986d40628000292486906088061818a0b41a00200084400080880229260c0044909d005125591a32cc00199640360af022285ae5da0,0x93fc002080ea0809e2200c20fffec544a5968f59c452890800260340001000040068801011800000a00479f2930210208f8c0001810f5000244000041800005d1a9822f457002000b0000490028800000100007000200c0000000000009ffc710f0c5000010000000,0x3c4a77ffc280200415526d0466b63dffe0d284d8034000510714014896038021090f6e6e207e317f154002016a909aad026c13086d0f67f9da8924828163a85d7d9f20b400000000804000029c372d66cc84e5fad770f3ed795a37cc22051220300000230800605a0,0x58bfbeffc0820001e027f600f59e1fe7e3d285d90453247c003001489610000002019ef21134201c90045b52e201e700e26c5701817577fefa4000000803245d7f9f22f440000000900004103fb904404184e1dada50e7c060400700228f7001f00480403c9706000,0x125199c1240302a81543018424233391116129e08d98d9d11f00b59238039880c883c048c902010800420a1000c00000056160982c4604d00c32492691608852444288001f0670060440e02e083a8e38f0f7000089004124581a02c8000241400602f02228dae5d80,0xe9615f803f407a2942000c210221eee0002fc0003003bdfc182fdbe000dc0004ed8b7461e90080000004221048a010200f8c0001013e04d6893ff92418000040444200005f0670060800746fceb2bfbffff7002000200c0000000000004003f00f005000010000000,0x30da11450fbf82841556ad05344211911f6bffec8d984051071cffffff039888fb9cc008814e006000002cbc00d09aad026c13082c020000048000028163ac100000d80000000000c440f1ffc00c8010a03184200520832810580448007ac5a000100023488060580,0x7ca0fe002fadf0016027f20101000ce01effff6c3003247c003ddfffdfdc000affd67e01a1200004000424bc48e1e700626c570100780007819ff000080324000060500040000000c802f5fff48fbfdffe3121800a00af006040070000f08781c01480407c9706000,0xe86be9f83070072a3e041019c067fa1e187830032fe101e3f838381c009bff0400680a89005323300273140200431cf0000000804100c060008201828003a0008a18c0b332a02e50402ce0083367c65c00f0f00a0042c78e7e73e001bc000004325055824283e8000,0x570ffff7ffbff7f402000000fef77fe7e5ab7f7ff4fe098018000000000000080068010001351fc06f806182130f1cf0800000808100c8000080000fd601c0009a1830b732a82e008100ba81c049778000000e0120030033ff800000005b9404024c55820003e8000,0x8c3a98820000324020000008261220000000000000299801800000000000037fdeff416fd11c30002000277eca31cf01002008001b3fff809f34daef601c06def420643b7ffff060180602e0c77ce3cf8f70000000600327e00000000042304024055820003e8000,0x8fa2a00a082c61408000a8b1980004000c000e028800040000070203c0000019a21210405d00fc147d404d0802e44001cf81b8d080e0aae531aba5c1a80324061260d0000ac108005c0284000023004800c0e09b98404084404246a1300001c87496a600205a85810,0x8912000a086e494411c5a9f07e3600103b0407034c00d20004022603e02210112e1b38207d09fc363c78040801fc1028ff81fc1ef087306010c281cad1f3fe7d1080ffc38530008047c250611027f05fa1c0ee7a05e4c0bf946ffc63300001fe3ff00030418048170,0x3a080000028200c60fdbfde0a4000000c040e0288020d0200370203c013e00f5cf53ecd7a48117f357fcae57c4a40014781b8d040e8aa8400a92489e23e3f86022090000ac908600572fed48806a926ac215694bd88512f5d1b36ee09708649748aa600205a85820,0x83140000006a000fbffbdfffe44e001037040f01cc12db0204320603e033e00ffdfef2b1f2c8a016b07ddbe6bf1a10286f81fc1e7087180024c0000ffbfcffbd00c073c3e53800e097f2aafc02888000a121167425a804021401046209feecff0fe80030010048140,0xb1fc51751fff8680c6e808005aaaf88f0080000000029bd3e0aac00000800025f9be810040cccec02000110003be9aaf80020000808b8d0265dc0a07ff9c007ef2fc0001400f8cf9b8007befc040000000001e0525af0800000000000005107f00084537800000010,0xb1fc11450f7f828fdffc3b4bebbe95c93f6fffffcf98c259879effffff239cfc5bdc800001cf4ec060006ce000509aaf00000000000a00000480000ff7fdffdc1290ff2780000c81464bfffdc048000000009e0025af8f30007c0001c07fcdfe00104537c08000000,0x2098407010300c09affffffe132b9c4e3ff8b0912fe31beb62a8381f04bbff46fcb37effaa40203f907f910003021000ec49821f4a45157a405c0a80000000001000000054044000a000000237b00024090041fad000f7c00012200000829100b80b00007fe001610,0x20000000000007dbfbcffef9b6044007808093ca0052088280200304200477ddc5f477fe02c02e907fced1eca01000fc4b821f0be5bbb8014104880c7fffafaf9036679d71ff81478b00003eb00024090041b8d004f3f0007e2001c08ebe00880300007d6001600,0xfffffffffffffff0800008011a4900000080000000033c00102bc00000c00039021a800055b4de806f807dc813e7e0c3800000e081fffffffffffff128000006126000005ec54804b8008412000000000000e1f9da70080000000000000111c9dc8fa648000000010]

def positiveCols : List ℕ := [0x77fc24a682a0000f779ee4e6ffb5c77cb2d684d80343bf3edfd4054896214654e9c36209c1000022002deb3c0ba40000826c530baf29f0400080000ff256c6e99a7820b733a42ed1122dec2c00048000a02112000188000a1401046209c00104224455b4000048151,0x88a381003c40080f539ee4e6fbf4844822c080900200020882a0000804200444e98b62098013132a4a2fc18213a000008048020b0a5e800405b2400ff257c6c89210202740000c81a209ec2feec5ce70f031b3200baa280a7e6187fa8d091905000045360800685d1,0xe7f6e5002262280cf5472d81f66a0410358009028413c400043724002082103d9b0bfe0061eb917a05505b105bd45029200044dcf06b800525e9200f8963ac700260bb00000000009c427c7a88ce29268c00dca00d24582d591a36cc002e42a1600480232c96f5fa2,0xf3df11451c7f028f1777378dffe2f5993de729e08f9af851073fb592380398add96f7fdc69ffeabb605277e35bd49aae3773641cfdecfe8025a1048d28020046122080003ac508008000ae02094800240800d091b000590800122088000b13497486e6002edc01622,0xdbe3a98800a8000c0207ac011665e2103c040e000002998018160603c000000d556b7a600152a03c300067a043cb1cf04f81f80001ffa4d4088000063303247bcc42f0807f0e700640023e802ebf0c40c084e76eea7062cc6040070022588571af1bf848717b06004,0x5cf3a9883c400b235987adf1fa5104003d040002c80218001020200300000003a80b7261c993333c5a6a658213c300c04c018090017f0cd40cb24929c873f6020000b0005c044004e402c421eeb7ce78f1c6f168cbf26ace7e63c7f132088c01880b0048716387804,0x9fe6318e28cc4bcbbc0639399e7904103680000000021902003000000013e034de61ab8d6f63fc316c73799a138e000090020000c1eff8e530e381cc0d8b397e1060c00060080060b170ff5b3367f07f00f8f84f0c44cfbf807ff801fc891101301c0000020000038,0xe0fbc1f030700c0bbe063139d36ff81e3bf830032fe319e3e038381c009bff39ef1230005503c00040027e1803e000009802000001ffcf0641fc0e0e0d8bb972e0fcfdfa600f8078f9fcf462224000000000800000048f30007c0001c021018000100000428000038,0xffe3fe003f80780de0203e21e371ffe03cffc0023003f5fc003fdfe000dc003df063c3f199f3ffc18f847ff393ffef031ffc00e1018ff00000c0000ff003c07f0000fec3bff00000c180f803c387ff800100fe7000070c3fff800000004c61fe3fe000038303f8000,0xff03fe003f00700e3fc7c1c1fc7e00003f000003c003e600003fe00000e0003eff83fc01e17bfffe0ff87fd213f3f003e00000fe01f0000781fff00ff9f3fe7c0080bf03c0000080fe00f873fc07fffffe00ff800f87f03ffffffffe008e79ffc0000073fc03fffc0,0xfffc00003fff800fc007fe01ff8000003ffffffc0003f800003fffffff00003f0003fffe0183fffff0007fe3e3fc0003ffffff0001fffff80100000ffe02007fff00c003ffffff008000ff83fff800000000fffff007ffc00000000000ff81ffffffff83fffc00000,0xffffffffc000000ffff80001ffffffffc00000000003ffffffc000000000003ffffc000001fc000000007ffc03fffffc0000000001fffffffe00000ffffc007fffff0003ffffffff0000fffc000000000000fffffff800000000000000f001fffffffffc000000000,0xfffffffffffffff000000001fffffffffffffffffffc0000000000000000003ffffffffffe00000000007ffffc0000000000000001fffffffffffff00000007ffffffffc000000000000ffffffffffffffff0000000000000000000000fffe0000000000000000000,0xfffffffffffffffffffffffe000000000000000000000000000000000000003fffffffffffffffffffff8000000000000000000001ffffffffffffffffffff8000000000000000000000ffffffffffffffffffffffffffffffffffffff00000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000001ffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]


def unionCols : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, x => if x = 0 then 0 else (if x.testBit 0 then c else 0) ||| unionCols cs (x >>> 1)

lemma unionAt (cs : List ℕ) (x i : ℕ) : (unionCols cs x).testBit i = true ↔
    ∃ k < cs.length, x.testBit k = true ∧ (cs.getD k 0).testBit i = true := by
  induction cs generalizing x with
  | nil => simp [unionCols]
  | cons c cs ih =>
    by_cases zero : x = 0
    · simp [unionCols,zero]
    simp only [unionCols,ite_eq_right zero,Nat.testBit_or,Bool.or_eq_true,ih]
    constructor
    · rintro (h | ⟨k,hk,bit,on⟩)
      · cases hh : x.testBit 0 with
        | false => simp [hh] at h
        | true => exact ⟨0,by simp,hh,by simpa [hh] using h⟩
      · exact ⟨k+1,by simp [hk],by simpa [Nat.testBit_shiftRight,Nat.add_comm] using bit,
          by simpa using on⟩
    · rintro ⟨k,hk,bit,on⟩
      cases k with
      | zero => exact Or.inl (by simpa [bit] using on)
      | succ k => exact Or.inr ⟨k,by simpa using hk,by simpa [Nat.testBit_shiftRight,Nat.add_comm] using bit,
          by simpa using on⟩

def checkedPlane (cs : List ℕ) (v i : ℕ) :=
  window 0 cs.length fun k => (cs.getD k 0).testBit i == v.testBit k

def isPlane (cs : List ℕ) (v i : ℕ) := ∀ k < cs.length, (cs.getD k 0).testBit i = v.testBit k

lemma planeSound {cs : List ℕ} {v i : ℕ} (h : checkedPlane cs v i = true) : isPlane cs v i :=
  fun _ hk => beq_iff_eq.mp (windowIndex h hk)

def invertIn (width x : ℕ) := bigOnes width ^^^ x

lemma invertAt {width x i : ℕ} (hi : i < width) : (invertIn width x).testBit i = !(x.testBit i) := by
  simp only [invertIn,Nat.testBit_xor,onesOn hi]
  cases x.testBit i <;> rfl

def missingBits (x y : ℕ) := x ^^^ (x &&& y)

lemma missingAt {x y i : ℕ} : (missingBits x y).testBit i = true ↔ x.testBit i = true ∧ y.testBit i = false := by
  simp only [missingBits,Nat.testBit_xor,Nat.testBit_and]
  cases x.testBit i <;> cases y.testBit i <;> decide

lemma sideAllowed {cs : List ℕ} {x i y : ℕ} (small : x < 2^cs.length) (plane : isPlane cs x i)
    (off : (unionCols cs (invertIn cs.length y)).testBit i = false) : below x y = true := by
  apply belowIff.2
  intro k on
  have hk := outsideBits small on
  cases hy : y.testBit k with
  | true => rfl
  | false =>
    have bad := (unionAt cs (invertIn cs.length y) i).2
      ⟨k,hk,by simp [invertAt hk,hy],(plane k hk).trans on⟩
    simp [off] at bad

lemma collisionFound {cs : List ℕ} {mask x i : ℕ} (plane : isPlane cs x i)
    (on : (unionCols cs mask).testBit i = true) : meets mask x = true := by
  obtain ⟨k,hk,bit,out⟩ := (unionAt cs mask i).1 on
  exact (meetsIff _ _).2 ⟨k,bit,(plane k hk).symm.trans out⟩

lemma missingOff {cs : List ℕ} {a b j i : ℕ} (bSmall : b < 2^cs.length) (plane : isPlane cs b i)
    (off : (unionCols cs (missingBits a j)).testBit i = false) : below (a &&& b) j = true := by
  apply belowIff.2
  intro k bit
  rw [Nat.testBit_and,Bool.and_eq_true] at bit
  have hk := outsideBits bSmall bit.2
  cases hj : j.testBit k with
  | true => rfl
  | false =>
    have bad := (unionAt _ _ _).2 ⟨k,hk,missingAt.2 ⟨bit.1,hj⟩,(plane k hk).trans bit.2⟩
    simp [off] at bad


def bcs0 : List (List Box) := [box0_0,box0_12,box0_24,box0_36,box0_48,box1_0,box1_12,box1_24,box1_36,box2_0,box2_12,box2_24,box2_36,box2_48,box3_0,box3_12]

def bcs1 : List (List Box) := [box3_24,box3_36,box3_48,box4_0,box4_12,box4_24,box4_36,box4_48,box4_60,box4_72,box5_0,box5_12,box5_24,box5_36,box5_48,box6_0]

def bcs2 : List (List Box) := [box6_12,box6_24,box7_0,box7_12,box7_24,box8_0,box8_12,box8_24,box8_36,box9_0,box9_12,box9_24,box10_0,box10_12,box10_24,box10_36]

def bcs3 : List (List Box) := [box11_0,box11_12,box11_24,box11_36,box11_48,box11_60,box12_0,box12_12,box12_24,box12_36,box12_48,box13_0,box13_12,box13_24,box13_36,box13_48]

def bcs4 : List (List Box) := [box14_0,box14_12,box14_24,box14_36,box14_48,box14_60,box15_0,box15_12,box16_0,box17_0,box17_12,box17_24,box18_0,box18_12,box18_24,box19_0]

def bcs5 : List (List Box) := [box19_12,box19_24,box19_36,box20_0,box20_12,box20_24,box20_36,box20_48,box21_0,box21_12,box21_24,box21_36,box22_0,box22_12,box22_24,box22_36]

def bcs6 : List (List Box) := [box22_48,box23_0,box23_12,box23_24,box23_36,box23_48,box24_0,box24_12,box24_24,box24_36,box25_0,box25_12,box25_24,box25_36,box25_48,box26_0]

def bcs7 : List (List Box) := [box26_12,box26_24,box26_36,box26_48,box27_0,box27_12,box27_24,box28_0,box28_12,box28_24,box28_36,box29_0,box29_12,box30_0,box31_0,box31_12]

def bcs8 : List (List Box) := [box32_0,box33_0,box33_12,box33_24,box34_0,box35_0]

def bcs : List (List (List Box)) := [bcs0,bcs1,bcs2,bcs3,bcs4,bcs5,bcs6,bcs7,bcs8]

def tile (code : ℕ) := ((bcs.getD ((code % 4096)/256) []).getD ((code/16)%16) []).getD (code % 16) ((2047,46408),(2047,46408),46408)

def orientedTile (code : ℕ) := if code < 4096 then tile code else flipBox (tile code)


def wr0 : List (List ℕ) := [[5129,5130,5958,6165,6164,1408,6160,5123,5273,5969,5955,6166,1152,1971,2067,5514,6169,5136,5520,5959,5961,6167,1046,1872,2065,2072,5137,5269,5270,5962,6069,6072,1025,1026,1030,1058,1153,1427,1856,1864,1974,5131,5138,5144,5145,5160,5265,5266,5275,5512,5521,5522,5957,5963,5970,6064,6065,6071],[496,4995,4448,4452,4421,866,4754,4401,4419,1168,514,507,4442,4968,874,1473,4600,6146,306,4755,4996,672,875,889,1120,1479,4426,4593,4595,4597,4998,307,656,661,664,888,890,1123,1169,1178,1184,1219,1227,1972,2048,4427,4433,4753,4756,4759,4762,4999,5217,5221,5222,5577,5578,5587,6118],[608,1568,5271,4519,4695,5272,1697,1784,1221,4532,5801,1793,592,2018,5670,1223,416,1787,2016,4518,4709,5815,600,614,1220,1576,1718,1797,1798,2025,2118,4690,4693,5322,5658,5797,5802,5809,5891,434,601,1170,1222,1224,1225,1553,1572,1575,1578,1777,1792,1794,2019,2112,2114,2115,2116,2117,4515,4516,4531,4698,5264,5798,5812,6116],[81,5064,4898,5049,769,416,5040,544,4512,4187,4897,97,4180,4186,437,5073,98,101,5057,87,4178,4881,5217,771,1154,4181,4196,4535,4645,4647,4896,4900,6170,88,434,552,554,560,788,947,4515,4516,4517,4518,4528,4529,4531,4532,4643,4644,4659,4887,4902,5062,5066,5216,5218,5220,5248,6224,6225],[1040,306,946,1696,772,1152,304,5771,864,4963,5123,802,146,4405,5220,5252,5253,5269,5270,6170,0,224,968],[1040,1670,5216,769,306,507,1696,5040,304,4176,4593,4709,0,224,374,81,900,5217],[308,5163,400,4905,1701,817,5203,4473,805,5136,821,1731,785,4465,811,1034,1082,5145,5174,6073,787,1083,378,834,4471,5140,5985,6081,336,824,1024,1028,1076,1079,1733,1734,1747,1748,1880,1891,1970,4434,5131,5144,5153,5160,5171,6068],[5475,304,169,5178,1384,4448,4387,389,5467,320,1299,4342,5989,405,5493,1336,551,1873,4664,277,696,1126,1385,1515,4389,4390,4450,5234,5635,5781,395,1139,1383,1896,4308,4310,4379,4667,4784,4793,5204,5492,5990,6121,6130,6136],[1040,352,4498,4865,1703,5475,804,817,5158,304,389,264,375,1205,1731,288,1034,1336,5140,326,1079,1104,5174],[4448,866,226,371,4421,659,4426,4995,4453,323,4401,5601,566,678,5461,5463,874,4442,4996,5447,5602,306,568,875,904,915,1281,4346,4353,4355,4373,5589,249,384,565,570,673,676,888,889,890,1479,1977,2032,4411,4427,4648,4658,4999,5371,5376,5393,5572,5577,5588,5605,6067,6114,6129],[1339,304,371,256,5458,5571,4448,4321,306,4387,5178,5431,389,405,1335,1360,323,5493,5577,169,234,246,277,696,4312,4339,4450,4453,548,659,673,1131,1139,1274,1873,4308,4793,4996,5890],[304,1378,394,5633,609,435,320,404,389,405,564,649,4496,4666,2038,5925,257,550,1394,4472,5489,5930,902,1273,1312,1531,4450,4502,5625,280,470,471,472,473,645,896,1301,1302,1316,1522,1538,1835,1976,4439,5621,6117],[866,4448,304,436,609,1378,306,1286,404,649,1511,4453,659,369,1360,323,389,1508,235,371,405,547,4339,4450,234,248,320,673,1268,1274,1283,1514,1863,4996,6117],[309,5187,5286,800,4917,4485,4981,5811,4470,5027,794,1175,4937,4739,5011,5683,392,4553,393,836,842,843,1099,1104,4560,4562,4931,5186,5472,5691,5792,340,341,426,553,825,1092,1177,4565,4576,4577,4578,4672,4729,4936,5026,5280,5282,5283,5296,6136],[1040,352,4865,4498,5161,817,768,404,304,1201,1703,5633,257,1731,4470,4483,5286,288,4404,4502,5140,5283,1079,1104,1175,5282],[5136,320,4865,5818,5163,304,1076,817,768,4473,5184,1696,811,821,338,787,5835,345,834,1034,1731,4437,4471,4915,5140,5174,837,1028,1073,1074,1734,1747,1891,5144,5153,5171],[224,5431,306,5365,4421,5577,4321,4426,5429,4411,4448,4416,4645,5571,5424,4442,5440,5442,4322,4323,234,246,4327,4339,4450,4646,4647,4649,5434,5441,5579,6066,304,1264,1268,1274,1348,1472,1489,1968,4325,4440,4640,4643,4644,5363,5430,5443,5569,5576,6112,6117],[5475,304,5624,5179,1384,171,4387,389,1349,5458,1299,320,4342,405,5493,1336,4664,5233,5989,277,1385,1515,4312,4389,4390,4450,5392,5409,5635,395,551,1125,1140,1383,1873,4379,4448,5412,5492,5991,6121,6130],[1040,352,4498,4865,1703,772,817,5475,5433,5076,304,389,1001,1076,1731,5061,375,1349,186,1034],[304,1378,394,436,610,404,320,561,405,4746,1492,4496,1737,2038,550,5925,273,1394,4472,5489,5930,1273,1312,1531,4450,4502,5625,5633,274,280,389,475,647,902,1301,1302,1316,1522,1538,1833,1840,1976,4570,4993,5621,6117],[5136,320,4865,4404,1041,4560,304,768,4727,5286,5187,5811,1073,4437,345,392,4553,5027,843,1074,1099,1104,4931,5691,326,338,426,1106,1175,4565,4729,5184,5282,5283,6136],[1040,352,4865,4498,5161,817,772,404,304,5433,1001,1703,1731,4560,345,1073,1201,1969,5633,186,1175,5282,5283,5286],[4448,866,4421,4452,4835,4995,4426,16,4454,306,514,5923,84,4401,4491,4608,4769,693,874,5888,4403,4996,4998,5027,5910,64,889,1867,4597,4629,4634,5908,55,357,535,663,679,689,888,915,1480,1881,1889,4419,4427,4438,4999,5026,5606,5881,5975,6148],[340,1670,1795,5523,738,4150,1451,1793,1675,5879,1481,5762,57,377,721,1827,4552,5777,2,327,387,402,1673,4197,5878,5882,59,69,391,469,1798,2022,4548,5921,56,122,1417,1460,1461,1528,1643,2035,4216,5506,5607,5766,5778,5779,5915,5931,5936,5992,6128],[1670,352,377,738,423,16,4416,514,4982,5755,353,4818,4552,57,374,864,1673,1979,53,59,391,722,4608,55,82,122,336,357,1424,1445],[184,597,454,5797,1187,1793,4519,146,1924,4532,1929,627,5575,151,1577,1778,1722,4516,1188,1195,1475,1803,4518,5801,185,424,1718,1794,1797,1798,1942,4297,4544,4711,5611,5658,5825,5891,5897,416,441,455,1428,1429,1440,1495,1554,1699,1728,1784,1792,1927,4515,4531,4539,5249,5251,5529,5593,5603,5798,5812,5892,5896,5905,6021],[1670,340,597,5762,4150,1478,209,1929,100,186,1722,1808,2050,377,1187,1250,327,402,1255,1589,1700,1811,1857,23,69,391,1495,1537,1890,1936,1942,2040,4516,56,454,738,1188,1440,1476,1552,1923,5907],[1040,1670,769,352,946,1703,899,86,304,306,184,224],[1670,340,597,5675,164,5574,464,1929,1481,5797,209,419,5833,1923,327,1195,1586,1785,5531,218,391,456,1187,1208,1765,1930,1942,4516,5610,160,402,455,1188,1410,1418,1456,1528,1552,1659,1685,1699,1793,1909,1939,1945,4531,5529,5617],[81,5136,1370,769,371,899,953,424,4645,5120,4416,48,437,4097,340,184,4436,4448,5217,5953,224,323,1227,1659,4181,4187,4339,5875],[866,4448,4353,371,4421,4426,16,4453,4995,514,5923,4401,306,84,226,507,693,874,5888,4403,4608,4996,5027,5910,64,565,566,568,875,889,4373,4600,55,323,496,535,570,661,689,888,890,898,915,1169,1977,4411,4427,4658,4999,5026,5588,5881,6148],[1040,1670,769,320,1703,946,4448,304,5755,4404,1664,1033,1335,4105,0,496,1096,1722,4996]]

def wr1 : List (List ℕ) := [[1553,4485,184,597,4917,5811,146,794,608,1395,1722,5187,392,800,1568,4695,5011,454,1440,1696,1798,4519,309,393,614,836,1099,4469,4516,4518,5186,5891,5897,326,340,341,441,455,553,1170,1187,4470,4515,4532,4672,5264],[1040,352,769,1670,946,1703,899,304,1168,306,369,1255,1435,1498,4516,184],[1040,306,769,5771,304,946,4242,599,437,802,146,1556,305,374,452,4516,0,224,358,838,4276],[4416,5424,371,22,369,4329,306,358,5431,5525,4426,357,4443,4113,4411,4448,5440,5442,5449,5491,80,4183,5443,53,1799,4116,4129,4843,5434,9,10,229,384,727,746,1368,1376,1411,1653,1656,1667,1810,1859,4401,4427,4436,4466,4822,5446,5460,5466,5571,5574,5579,5880,5913],[306,4448,5449,1478,4329,4426,320,1287,5431,369,4416,371,548,405,5381,5424,5440,5442,4661,5623,282,358,1819,4646,5434,5491,5890,357,379,384,1376,1386,1491,1812,2039,4370,4375,4385,4401,4427,4643,5366,5394,5402,5430,5460,5466,5481,5571,5574,5579,5909,5924,6070,6137],[1339,304,371,256,5458,3,389,1478,4387,4448,5179,5431,405,1287,1360,306,548,4661,5493,246,277,320,358,1819,4339,4450,5233,5365,5491,5890,1125,1140,1335,1812,1873,4312,5363,5412,5571,5574,5909],[886,1062,953,1060,5123,5079,1333,5528,887,980,5129,5761,954,912,1362,1666,4986,994,1385,1433,1888,5137,914,984,1042,1046,1075,1366,1434,1588,5156,5474,5977,865,918,923,982,1029,1030,1371,1559,1584,1587,1635,5136,5464,5540,5664,5696,5746],[146,1186,1577,1721,4519,151,420,1475,1808,1929,5670,1921,1924,5797,453,1493,2026,1185,1241,1495,1803,4515,4518,5897,427,452,1428,1440,1554,1718,1732,1942,2034,4297,4531,5331,5658,5802,5896,179,184,185,434,442,455,1194,1242,1416,1432,1494,1504,1568,1572,1698,1723,1778,1905,1926,1927,2027,4532,5315,5798,5812,5892],[1040,325,1050,886,4905,5123,953,5203,5528,805,5129,887,4473,308,817,1082,5761,400,785,1434,787,821,1083,1701,1888,360,808,865,982,1034,1559,1584,1588,5540],[1049,1670,769,352,953,1339,1703,304,327,1050,22,373,1556,5129,5435,1034],[1040,330,5146,599,146,403,794,608,4485,420,1808,1731,4483,1060,1223,1703,309,392,453,800,1921,614,836,1440,1787,4698,4917,5186,341,361,455,1428,4515,4518],[864,5435,4434,5536,970,4982,971,1350,1659,5545,1014,1078,1328,1670,5778,930,995,4962,5754,406,1361,1387,1396,1414,1435,5542,881,932,933,936,997,1033,1072,1337,1377,1392,1427,1448,1589,1594,1611,1781,4963,5012,5482,5541,5671,5702,5779,5898],[1370,1062,945,1670,5904,953,899,4434,5192,1060,5889,4500,5097,5306,1659,887,1042,1371,4148,706,5129,5195,386,882,898,1029,1067,1414,1435,1611,1633,4821,4824,5156],[4995,4441,4454,1670,18,1665,1801,307,536,1446,306,713,369,520,1379,1808,68,4194,374,889,4217,5506,390,537,1393,1659,4168,4225,4635,4968,5968,753,864,1413,1443,4419,4423,4451,4466,4481,4628,4999,5882,5883],[1370,769,1670,5136,352,953,424,4443,304,5129,98,4422,146,978,1067,184,899,1033,1430,5192,5299],[4242,5800,5574,5797,4248,4262,5799,5651,6006,5879,1785,5508,4519,5655,5510,5665,1477,4246,4264,4512,5657,5812,5882,1717,1718,4266,4518,4522,5656,5658,5798,144,160,1476,1552,1776,1909,4250,4265,4267,4515,4517,4531,4532,5504,5506,5507,5509,5513,5568,5584,5586,5666,5669,5792,5808,5876,6000,6004,6016,6144],[1670,1703,977,1027,167,5444,5545,468,5778,5827,872,931,1761,5632,1011,1397,1526,1762,1817,4295,4563,5634,5779,5847,1010,1435,1506,1527,1586,1607,1781,4280,5541,5542,5604,5702,5704,5862,5898],[1670,1478,5843,1941,1808,23,387,1857,1665,1255,213,5879,100,402,1795,2050,1675,2040,5777,327,1249,1446,73,391,1537,1673,1890,1953,4548,65,1256,1460,1461,1509,1571,1607,1610,1714,1749,1914,5353,5607,5766,5778,5779,5876],[1049,1670,946,1370,1703,945,899,5827,999,4500,1,167,291,368,789,1720,5306,467,898,1033,1207,1611,1633,4821,5129,5192,5541,5904],[1049,352,728,423,4104,5755,1339,1915,213,4416,16,374,1233,1478,53,100,390,537,889,1255,1808,371,738,904,1498],[146,1577,1190,1808,151,1496,1921,4519,1721,425,1924,1929,1700,5670,1813,1936,1189,1206,1803,4515,4518,5681,5897,184,185,186,452,453,454,1428,1440,1493,1718,1722,1732,1942,4297,4532,5611,5658,5797,5799,432,455,1176,1179,1429,1432,1475,1495,1554,1590,1728,1778,1814,1907,1926,1927,4531,4539,5274,5593,5603,5798,5812,5892,5896,5905,6021],[1670,1700,1857,1478,1941,23,1808,1929,209,1665,4262,402,2050,100,1190,1255,1589,1722,5797,327,1495,73,391,1537,1890,1923,1936,1942,2040,65,1176,1189,1440,1476,1552,1607,1907,5876],[1049,1670,769,352,1339,946,1703,81,304,899,656,802,5700,146,1379,5435,4999],[1049,306,769,1670,946,4242,304,4536,599,4176,144,4709,81,146,374,772,802,4272],[1040,306,144,946,5771,437,769,4242,304,81,599,807,1556,146,374,4609,314,802],[5435,4434,5524,306,5675,4454,6099,1002,4423,368,307,5096,5442,5526,338,5574,5479,5531,986,4451,374,1410,5063,5443,378,867,1659,4481,4490,5092,5883,6103,985,1826,2006,4472,4650,5031,5094,5105,5154,5530,5698,5704,6098,6101,6106],[970,338,5574,164,1350,1670,419,5435,306,5096,4982,307,402,4250,5792,1361,4454,209,406,1396,1410,160,368,391,864,995,1033,1072,1659,4517],[728,1049,1877,306,1801,4454,18,4423,1379,307,1808,4194,68,1449,374,4217,39,58,390,713,1088,1363,4225,4451,4490,5883,753,1412,1443,1458,1459,1604,1826,4419,4466,4481,4841,5031,5928],[1670,5830,5574,164,419,202,387,5531,1779,1481,5699,5879,5675,327,1586,402,1755,5526,5777,5895,5921,218,391,456,464,1659,1730,1760,2052,5610,5778,211,1410,1426,1456,1460,1528,1563,1675,1685,1707,1826,1912,1945,1946,4567,5508,5530,5586,5607,5617,5701,5704,5753,5779,5833],[1670,1703,977,4467,1027,164,327,209,402,4250,356,5797,4563,186,218,391,1011,1397,1410,1730,5627,468,1481,1779],[1670,1715,4467,1857,1915,23,1808,423,402,1665,70,327,356,1675,5777,5844,1249,1255,5879,73,100,391,1449,1478,1537,1556,1592,65,483,744,1458,1459,1528,1673,1685,1739,1955,5353,5928,6027],[1347,1700,1857,977,164,1670,4467,209,872,1027,464,1057,327,343,1255,1915,73,391,452,1011,1190,1206,1208,1478,1765,5755,5833,23,356,1176,1189,1528,1586,1639,4531,5617]]

def wr2 : List (List ℕ) := [[1049,1670,769,306,946,4242,4176,304,0,5792,144,4709,3,802,146,307],[1049,5755,769,352,1703,946,1339,304,0,437,82,72,802,146],[1339,352,1049,423,728,18,5755,1107,1915,213,1446,4416,1715,16,899,53,100,390,537,889,904,1412,306,738,1249],[1040,330,1703,800,403,4485,608,794,1808,1395,5146,146,597,1223,1731,1787,309,392,627,4519,361,614,836,1060,1440,5186,5799,184,186,340,341,452,455,1428,1722,4515,4518,4532,4917],[1049,306,769,5755,946,1703,304,899,352,1041,802,0,146,599,5531,4272,4536,4550],[728,4416,1049,5435,4423,22,306,5524,0,5096,5574,1877,4194,986,1449,4457,18,373,1410,4411,4809,282,315,374,1649,1667,4116,5526,5883,307,357,384,713,4401,4427,4451,4806,5594],[1049,352,769,1670,946,1339,1703,304,4276,5574,5755,22,373,4443,5076,5435,821,899,1033,1076,5192],[1049,306,728,1796,22,4416,4423,1877,18,307,4194,68,357,1449,373,4451,4809,53,374,722,1363,1667,4116,5883,315,384,713,867,1412,1443,1604,4401,4427,4466,4806],[1049,352,728,419,164,1339,1715,5755,1915,5594,5096,4416,4499,1360,5574,59,100,282,456,1255,371,384,738,899],[1049,352,1670,164,728,419,1339,5096,5594,1715,1915,1537,306,1360,4416,59,100,282,456,1255,4499,384,738,899,1514,5574],[1049,1670,352,728,18,1715,327,423,1915,4416,57,899,22,53,59,100,390,722,1255,1360,738,1478,1556],[1049,1670,769,352,1703,899,5064,243,304,306,81,437,887,1556,2009,1088,1379,4609,6024],[1040,306,769,5771,1700,946,304,968,1556,1269,0,144,496,599,1042,5064,6170,437,4609,5220,5252],[1040,306,496,4282,946,769,1658,304,1696,886,1556,507,0,389,4105,4996,224,772],[1040,306,946,1658,772,592,304,886,1556,769,4290,1696,599,4516,4707,144,389],[772,886,946,325,1040,4498,4405,304,1556,5824,769,306,592,1152,4516],[1040,1670,946,352,1700,772,4898,306,304,802,899,4404,1269,82,184,681,1033,4098,4273,5220],[5136,224,5766,4128,306,5040,769,304,5120,1696,4411,886,4328,4321,4131,4263,4416,805,4727,146,507,4118,4327],[1040,306,224,1696,769,5040,1658,304,886,1556,4128,4645,4328,4356,389,405,4131,4340,245,496,2081,4321,4322,4327,4416,4448,4643,5365],[1040,306,946,1670,772,420,304,1703,4707,1556,1928,82,599,4516,88,146],[1040,1670,243,0,1703,352,946,4898,802,4404,304,306,772,1339,81,1041,1269,146,184,681,2009,4098,4273,5064,5220],[1040,1670,352,946,772,1703,306,304,100,1269,899,184,496],[1040,1670,352,946,772,1703,306,100,304,1269,1658,864,4101,570],[1040,1670,352,946,772,1703,306,304,802,1269,4898,899,0,146,4272,4516,184,353,420,656,1033,4536,4753,5220],[1040,306,144,946,4242,769,1658,304,886,1556,4288,599,772,389,4707,0,146,4250],[1040,306,144,5064,769,4242,304,1658,6024,224,404,1556,81,183,437,4600,5792,4128,5042,507,4288,4593,4597,4609,5510,496,545,955,4322,5799],[1049,1670,946,352,769,1703,1928,306,304,899,0,184,772],[1049,352,946,1670,1703,769,899,144,304,306,1556,802,1410,1593,4753,519,681,4098],[308,5168,325,4905,5143,1701,1040,805,4473,2081,1050,5145,1731,1082,376,811,1083,1174,4465,808,834,1065,1122,1441,1447,5140,5287,155,378,401,787,821,1026,1061,1076,1079,1733,1734,1747,1748,2072,5131,5136,5138,5144,5153,5224],[309,1040,599,330,603,4483,4904,5285,5834,4485,4937,1098,5187,4914,392,1065,4470,5344,6215,372,403,534,836,843,1099,1718,4619,4725,4931,5186,5284,5697,5825,6216,388,529,601,825,960,1097,1104,1560,1696,2128,4729,4936,5281,5690,5799],[5072,772,4149,201,4901,1001,4501,1124,4160,5090,4167,4314,72,2120,199,346,4165,6171,170,1012,2072,4169,4890,5109,5110,6184,1000,2068,4154,4311,4313,4865,4873,5095,5232,5400,5411,6199,6214],[1040,4498,772,325,1001,5072,1696,304,1156,404,5168,802,4405,5857,1034,4470,817,787,4313,4880,5138]]

def wr3 : List (List ℕ) := [[792,5032,168,5019,769,4501,4155,840,440,809,20,4994,6196,4305,4870,5857,538,4549,935,346,820,822,4579,4624,4777,4945,5111,439,539,599,619,662,2073,2097,4309,4723,5399,5410,5850,5851,5859,6183],[1040,4498,772,325,599,168,304,817,5032,802,809,5857,1001,440,4470,5285,5344,389,257,529,662,4619,4729,5281,5284],[5064,11,2075,4281,4881,5041,947,1121,5364,97,677,768,4256,6176,5080,5107,88,98,118,826,1127,4218,87,2119,4219,4870,5057,6168,681,838,4196,4306,4307,4900,5396,5398,6170,791,816,832,1128,1280,1289,1298,4785,4896,5062,5067,5098,5226,5235,5236,5380,6211],[5072,4501,3,4280,4901,5041,4898,4160,772,4114,978,4263,1121,4098,4119,49,152,346,2119,4306,4307,4890,8,88,599,791,816,967,1127,2068,5062,5067,5362,5368,6176],[5072,4501,54,5814,809,802,772,5041,1608,891,4114,978,3,838,4305,4119,4898,346,840,935,6176,538,791,810,2037,2068,5028,5368],[308,5158,325,4905,1701,817,1031,4473,805,1050,1040,785,1731,5145,1082,375,376,811,1034,1083,4465,5174,808,821,834,1065,5140,5143,378,787,824,1028,1076,1079,1733,1734,1735,1747,1748,5131,5136,5144,5153,5203],[304,4498,5462,5365,4742,658,1716,404,549,4118,4421,112,245,389,4448,405,40,4662,5622,129,1985,4340,4347,4372,4450,5002,5204,5473,3,225,234,395,680,695,1973,4214,4416,4440,4474,4778,4790,4979,5626],[352,5142,804,4498,4358,1716,404,5178,4377,304,389,264,1382,5475,288,292,5204,5625,275,1383,1536,4308,4338,5483,5621],[304,5125,305,4404,5796,4868,4424,4405,5143,5131,4865,4870,5145,4409,4436,5139,338,345,4432,4880,4882,4885,4888,339,1696,4425,4437,4439,4864,4903,5121,5136,5140,5153,5795,768,775,4886,5120,5141,5144,5793,5794,5799,5803,5810,5811],[308,5158,325,4905,817,5817,1031,805,4473,1040,1050,376,5145,785,1065,1082,1731,375,811,1034,1083,1705,4465,5153,5174,821,834,5140,5143,378,787,808,824,1028,1076,1079,1701,1733,1734,1735,1747,1748,5131,5136,5144,5203],[1040,352,4498,4905,804,389,817,5475,5158,304,5817,264,375,1731,288,800,1034,1705,5140,326,1028,1076,1079,1104,1696,5174],[352,5142,804,4498,4358,389,404,5178,4377,304,264,5302,1382,5475,288,292,5204,5291,5625,275,1226,1383,1536,1716,4338,5387,5483,5621,6122],[1040,5146,330,800,5286,1415,1703,309,794,4485,4483,4937,5158,5187,403,5834,4914,5303,5538,392,4470,836,842,843,1099,1104,4917,4923,4928,4931,5186,5193,5194,5283,341,825,1065,1092,1175,1177,4936,5282,5296,5544,5799],[1040,352,4905,4498,1703,804,817,404,4404,5142,304,264,1731,4470,5286,288,800,4483,5140,5174,5283,403,1079,1104,1175,1415,5282],[1040,352,4905,4498,1703,817,804,404,5158,304,1731,5286,264,1065,4470,5305,288,800,1034,5140,5174,1028,1079,1104,1175,4483,5194,5282,5283,5538],[786,983,5365,54,201,658,4501,4865,809,2090,4118,4263,549,768,4128,52,629,4119,49,198,4112,5028,91,121,208,290,822,922,2091,4347,4362,4773,4890,3,150,644,880,921,1009,1719,1753,2070,4209,4260,4772,5368,5382],[1040,4498,304,4905,658,1696,305,549,817,404,805,4263,5365,245,786,4470,389,834,4865,5028,198,644,4662,4773],[1040,352,1670,769,946,1700,899,656,772,304,306,549,82,184],[772,1001,4153,802,4305,4501,809,1729,17,5109,346,4162,5090,4164,5828,5857,4890,4945,5110,5403,822,1000,1012,2066,2068,4146,4163,4166,4309,4786,4789,4865,5060,5095,5382,5813,5850,5851,5859,6171,6184],[772,1001,4153,802,4305,4501,4901,17,1729,5090,5109,346,4162,4164,5828,5857,4890,4945,5110,5403,6184,822,1000,1012,2066,2068,4146,4163,4166,4309,4786,4789,4865,5060,5095,5382,5813,5850,5851,5859,6171],[1040,4498,772,325,1001,1729,304,802,404,5158,5857,817,5817,1034,4470,389,5110,6171,775,787,1028,1079,1696,2066,5140],[1040,1670,352,769,946,1700,306,304,48,1556,99,656,81],[5072,4501,54,802,5814,809,772,5041,1608,17,891,978,4114,826,4305,4119,4898,346,840,935,6176,538,791,822,2068,5028,5064,5368,5382],[1040,1670,352,769,1700,946,4640,306,304,1269,243,1556,40,4602,4898],[1670,769,352,5136,953,1269,436,1041,306,304,656,48,4640,4709,83,224,369,373,437],[5041,772,17,5814,978,4501,802,1608,4160,5032,54,72,4305,4901,346,4898,840,4119,0,791,810,2068,5368,5382,6176],[1040,1670,769,352,946,1703,306,304,802,418,772,1556,1928,144,4516,146,420,1033,4404,4602,4898],[4448,5126,304,225,4135,4404,4918,4724,4119,4405,4118,3,1702,4130,305,4436,4123,49,4184,5365,53,4340,4372,4424,4437,4450,4464,4713,5002,5190,99,104,234,338,837,1106,1751,4134,4352,4416,4440,5826,5832],[4977,4448,304,225,4498,4421,5365,389,4147,404,549,6192,1521,4118,5462,251,405,245,1507,4662,5622,3,1985,4340,4372,4450,5002,6194,40,129,234,395,666,680,1271,1488,1513,1973,2099,4214,4347,4416,4440,4474,5619,6123,6212,6217],[304,1041,320,326,4404,5176,4918,5818,4464,1081,4405,4912,5861,1073,4436,4906,5184,777,4424,4884,345,837,1702,1706,4437,4450,4915,5190,5835,5841,338,1066,1074,1089,1095,1106,1751,4432,5189,5826,5832,5845],[1040,320,4905,5818,304,817,4487,5158,768,1076,4405,5184,4305,4865,375,811,1065,1731,4915,326,834,1034,1706,5140,5174,341,345,785,1028,1073,1074,1696,4424,5144,5153,5835],[5475,304,4498,1969,4358,352,1269,5433,389,4377,5458,264,405,5291,1382,5179,275,288,292,404,1305,1490,4450,5302,1313,1536,2020,4338,4656,5378,5385,5408,5620,5621,5625,6122]]

def wr4 : List (List ℕ) := [[1040,352,4498,772,1001,5814,5433,5475,5076,304,389,800,5061,1076,1731,292,375,4912,186,1034],[1040,320,772,1703,4404,1001,5475,304,4483,1041,5304,5106,5109,326,800,5286,375,4487,4912,5811,331,843,338,775,1074,1175,5193,5282,5283],[1040,352,4498,4865,1703,772,817,404,1969,1041,304,5433,1001,1731,345,1073,4912,5304,186,1175,4483,5282,5283,5286,5811],[5136,3,5365,4724,304,5120,1696,40,4135,305,4130,549,768,809,4118,54,811,4119,629,817,49,786,91,201,338,4263,4340,4437,4773,4865,198,644,658,921,1734,4347,4416,4448],[1040,4498,772,549,1001,1696,325,404,1271,304,4130,817,4118,4263,5365,4135,338,389,658,802,3,198,225,245,644,4340,4347,4662],[1040,352,4498,772,1001,5814,5433,802,5475,5076,304,5061,1731,292,375,389,186,787,1034,1269,4358],[1040,352,4498,772,1001,1703,5433,802,404,304,817,1269,1731,345,1073,186,787,1175,4358,5282,5283,5286],[1040,352,4498,772,1001,1703,5433,404,802,5076,304,5061,1269,1731,5286,292,345,186,787,1034,1175,4358,5194,5282,5283,5538],[1040,1670,352,769,946,1700,4640,306,1269,304,802,1556,5161,40,243,4185,4602,4898],[1040,1670,769,352,1700,946,306,4640,304,1269,1556,243,40,4185,4602,4898],[1040,326,4519,599,330,180,309,184,608,1924,146,794,4485,1793,454,4904,5834,340,800,1703,1722,4914,392,597,403,614,836,1065,1718,4516,5186,5825,5891,5897,341,441,455,1099,1440,4483,4515,4936],[1040,352,4262,772,5755,946,1703,144,82,304,802,1649,809,4516,420],[1040,1670,769,352,1703,946,48,304,306,0,1339,677,1658,1928,81],[1040,306,769,5755,946,1703,304,144,437,48,4449,4404,4898,81,592,677,772,864,4516,5891,146,184,968,1435],[1040,1670,769,352,1703,946,0,1339,81,304,1658,48,1269,1928,72,802],[1040,352,769,5755,953,4280,4498,0,4404,4422,4448,243,81,864,1060,4181,4520,5907,144,304,404,420,808,4657,4660],[352,1339,804,436,5142,4742,1683,235,304,306,369,371,4358,389,1360,128,246,1514,4147],[1040,330,1703,800,1722,608,794,180,4485,1793,5146,403,5027,597,1223,4519,4914,309,392,4469,5834,146,326,614,836,1060,1104,1210,4516,5186,5891,5897,184,340,341,455,1065,1395,1440,4483,4515,4917,4936],[1040,1670,352,769,946,1703,1339,304,72,772,0,81,184,420,4516],[1040,1670,769,352,946,1703,304,306,48,802,1658,864,0,224,519,809],[1339,4448,304,4724,1041,4918,371,5818,320,4329,4404,326,4405,5431,777,4906,306,1073,1478,4183,246,358,1702,1819,4450,5493,99,234,256,359,4312,4443,5574],[1339,4448,304,4724,1041,4918,320,5818,371,4329,4404,4405,4443,5861,777,4906,306,1073,4183,5431,246,326,358,1478,1706,1819,4450,5493,99,234,256,1667,4312,4464,5574],[1040,306,769,5771,1700,946,1269,304,4185,772,1556,0,1780,5161,243,802,4411,4448,496,570,4643],[1040,886,1050,4905,325,5817,953,5143,805,5123,308,5129,4473,785,1082,1701,4465,376,817,887,1083,1588,1617,5514,808,821,865,982,1034,1434,1559,1584,5540],[1040,1721,330,599,146,193,309,1929,1808,4483,420,1731,4485,960,1223,1718,392,1065,1696,1921,184,442,614,836,1097,1428,1440,1577,1787,4515,4725,4904,5186,5825,6215,6216,372,388,534,601,1432,1554,4518,4936,5834],[1049,1670,769,352,953,1703,327,1556,304,420,5297,456,464,1060,1255,0,4657,4660],[1049,306,144,946,1670,772,4242,304,1047,968,420,374,4709,146,311],[1040,886,4905,325,1050,5817,953,360,308,805,5123,5129,4473,817,1065,1082,4465,376,887,1705,785,821,1083,1617,5152,5514,808,865,982,1034,1434,1559,1584,1588,5143,5203,5540],[1049,1670,769,352,953,427,1339,304,1050,98,195,389,112,1556,5129,1034,5203],[1040,330,5146,599,146,794,608,1060,420,1808,4485,180,1731,309,4483,1223,1703,392,1921,184,614,836,1440,1787,4917,4928,4936,5186,341,361,372,403,455,601,1065,1428,4515,4518,5834],[1049,306,769,1682,1703,304,953,786,1556,352,40,144,81,5365],[1049,352,769,1670,1703,953,1339,1060,4458,304,961,5594,327,420,1255,4404,180,184,1478]]

def wr5 : List (List ℕ) := [[1049,352,144,946,1339,804,5755,1700,304,82,1556,72,18,1412],[1049,5755,352,946,144,804,1339,1703,304,306,4276,146,195,4699,5511,82,1808,4289],[1040,330,1703,800,5146,180,1808,794,1929,361,1924,4485,4519,146,309,597,392,1731,1787,1936,340,454,614,836,1060,1065,1440,1718,1722,4515,5186,5799,5825,184,186,341,452,455,1099,1428,4518,4936,5834],[1049,1670,769,352,1703,946,1339,304,3,72,144,1435,184,420,1255],[1049,0,728,1483,772,1670,4242,306,946,304,1047,4176,968,1808,307,840,1412,632,4276,146,314,420,2075,4448],[1049,144,306,728,772,1670,599,304,946,968,4242,1047,4422,4176,4709,0,146],[1049,144,306,728,304,769,1670,4242,5531,195,5040,4257,4264,768,4709,81,146,374,889,4276,4699,420,961,4120,4289],[1049,1670,769,352,1703,946,144,899,304,306,772,968,82,146,1047,184,420],[1049,352,769,5755,1703,946,1339,768,304,1556,82,72,4422,144],[1049,1670,769,352,946,1703,327,304,899,456,464,1060,1255,5297,0,184,420,1210,4422,4657,4660],[1049,306,946,1670,772,4242,4176,304,144,4422,5531,802,4709,0,3,599,976,146,452,4657],[1049,1670,769,352,1703,946,1339,304,72,1556,768,1107,82,1412],[1040,330,1703,800,794,608,1808,180,4485,5146,146,309,597,1223,1787,392,1060,1731,4519,361,614,836,1210,1440,1722,5186,184,186,340,341,403,452,455,1065,1395,1428,4515,4518,4917,4936,5799,5834],[1049,5755,352,769,946,4276,1339,772,146,304,306,419,1715,4289,4443,4699,5076,5511,1033,1076,5192,5435],[1049,5755,769,352,946,1703,1339,772,304,306,4276,146,1715,5435],[1049,352,144,728,772,5755,946,1703,1339,5365,802,0,5574,4276,5161,146,304,4289,570,899,4448],[1049,5755,352,769,946,306,772,4242,304,4257,4457,427,840,1556,144,968,979,4521,5818,1033,4468,5064,5076],[1049,1670,769,352,946,1703,306,1060,5146,304,802,0,146,1556,180,420,772,4550],[1049,1670,769,352,946,1703,1339,304,72,82,772,0,146,81,144,184,420],[1049,306,769,1670,946,1703,304,352,437,0,772,899,81,592,1041,4404,144,146,184,361,802,4550],[1040,4498,772,325,5076,2081,1696,304,404,6171,1001,4405,1731,4470,1174,4865,5051,5093,5140,795,1026,1104],[4868,4978,4487,354,5161,4727,342,4615,769,4480,5014,1105,793,4624,4885,5686,4486,4864,313,599,4903,5029,5705,504,531,619,643,648,826,1573,1602,1766,2073,4723,4881,4888,4929,4944,5024,5030,5290,5846,5848,6183],[1040,772,331,1696,1001,611,5161,304,4487,626,1105,5051,5106,6171,769,4470,5093,843,1097,4978,5284,504,599,1104,1560,4464,4729,5281,5285],[0,5058,4881,152,5041,5365,4099,4890,4101,4753,4754,4114,5057,4112,4868,5050,4098,4263,4875,6162,4119,49,4106,4247,32,976,4250,4251,4900,5043,5056,5369,8,770,967,1270,4249,4258,4259,4260,4261,4265,4267,4752,4755,4758,4864,4873,4889,5062,5067,5360,5362,5368,6161,6208],[5072,772,4149,201,4901,1001,4160,177,5076,5370,4167,4314,72,2120,199,4165,4900,6171,6198,170,1012,4169,4890,5109,5110,5395,5412,6195,660,795,1000,1077,1124,1297,2068,4154,4311,4313,4791,5095,5232,5383,5400,5409,5411,6214],[1040,4498,352,772,1001,5814,5061,404,5072,5076,304,802,5433,199,72,292,389,186,795,1034,6171],[891,769,2,1608,809,2089,2021,4305,176,1738,4155,1600,822,4615,538,1831,20,2121,599,820,826,1832,4549,4624,4777,4900,5707,6138,168,439,504,539,619,643,694,697,792,1312,1316,1830,2033,2037,2041,2073,4309,4723],[1040,4498,769,352,176,5161,817,1608,5032,304,802,1001,1703,345,772,5051,2,504,599,4624,5281,5283,5285],[1670,769,352,5136,953,4128,306,5120,424,304,4709,4422,224,4448,4657],[4868,873,150,5161,3,4727,4347,4128,232,983,4195,4345,52,4118,4263,4864,120,4119,4247,4885,49,225,916,4112,4134,4865,4883,121,203,4344,4376,4900,4903,5395,55,115,202,208,313,634,917,987,996,1713,2070,4117,4138,4208,4260,4357,4760,4882,4890,5162,5365,5368,5383],[1040,4498,5365,304,4128,4727,1696,305,260,404,768,1985,658,4263,4865,405,4470,245,389,836,843,916,4347,4662,88,232,549,634,680,987,4448],[1040,352,1670,769,946,1700,772,306,656,304,224,899,369,184,507]]

def wr6 : List (List ℕ) := [[772,331,5076,4487,4901,354,1001,5106,5161,6171,1105,5051,5824,4486,4865,4903,5093,795,1000,1012,1016,1109,1712,1713,2068,4890,5095,5819,5846,5848],[1040,4498,772,352,817,5076,5814,404,6171,1001,304,5433,1731,5061,345,389,800,186,795,1034],[1040,331,772,1703,4404,1001,304,4487,5475,1041,5106,5109,6171,375,800,1415,338,843,5283,795,1074,1175,5051,5193,5282,5286],[1040,4498,352,772,1001,1703,404,5076,304,802,5061,5433,1731,292,345,6171,186,795,1034,1175,5282,5283,5286],[786,983,658,54,201,4347,665,2086,809,4128,2090,225,822,4263,4868,3,52,629,4119,5365,49,91,4112,5488,121,198,202,290,2091,4118,4362,4773,4865,4890,4900,5395,6134,150,208,232,634,996,2070,4208,4209,4260,4673,4774,4980,5025,5368,5382,6213],[1040,4498,352,4865,1703,658,817,804,404,665,245,304,4263,4470,40,288,916,4347,91,198,232,634,4773,5365],[1040,1670,769,352,946,1700,656,306,304,899,40,549,184,224,507],[772,5076,17,5814,1001,1269,809,4153,5061,802,4162,4305,4164,4768,5858,4890,4900,4945,5109,5110,5403,5408,186,795,822,1000,1012,1312,1313,2068,4163,4166,4309,4786,4789,4792,5095,5377,5382,5856,5860,6135,6171],[772,5076,17,5814,1001,1269,5061,4901,802,4153,4162,4305,4164,4768,5858,4890,4900,4945,5109,5110,5403,5408,186,795,822,1000,1012,1306,1313,2068,4163,4166,4309,4786,4789,4792,5095,5377,5382,5401,5856,5860,6171],[1040,1670,769,352,946,1700,1269,306,304,656,4753,1556,1969,389,802,1033],[1040,352,772,4498,1001,1703,802,404,1041,4404,304,5051,5433,5286,1731,292,345,1415,186,795,1175,1269,5194,5282,5283,5538,6171],[304,4128,4724,4436,5365,5161,5120,1696,305,4135,768,4885,35,4118,4130,202,4119,4184,49,4263,203,843,916,4113,4340,4347,4404,4464,3,104,208,225,232,234,634,987,1099,4260,4416,4448,4727],[1040,4498,772,225,1696,5365,1001,325,404,260,304,1985,1271,4263,4135,5051,549,4118,389,843,4662,6171,3,232,234,338,634,658,680,4340,4448,4464],[1040,320,772,1703,4404,1001,5475,4487,304,326,1041,5106,5818,5051,6171,375,800,331,843,1706,4405,5109,338,795,1074,5140],[1040,320,772,1703,4404,1001,5475,4487,304,1041,5106,5109,375,800,6171,326,331,843,5283,338,775,795,1074,1175,5193,5282,5286],[1040,352,4498,772,1001,1703,404,1969,1041,1269,304,802,5109,1731,5433,292,345,6171,186,795,1175,5051,5282,5283,5286],[5136,352,150,5176,40,54,768,5161,41,5120,817,4135,201,304,4119,4263,49,91,4437,5365,338,339,4128,4773,198,232,634,658,917,1175,1734,4347],[1040,4498,1269,1001,352,1703,772,404,304,802,4263,817,4135,338,1073,186,232,4347],[1040,352,772,4498,1001,5814,5433,802,1041,4404,5475,304,1269,817,1731,375,389,5051,186,795,6171],[1040,4498,352,772,1001,5814,802,404,5076,304,5061,5433,1731,6171,292,345,389,1269,186,795,1034],[1040,4498,352,772,1001,1703,404,802,1041,4404,304,5109,1731,4470,292,5093,186,264,795,1175,1269,5282,5283,5286,6171],[1040,4498,352,772,1001,1703,404,802,304,5109,1269,1731,4470,292,5093,186,795,1175,5051,5282,5283,5286,6171],[1040,4498,352,772,1001,1703,404,802,5076,304,5061,5433,1269,1731,292,345,186,795,1034,1175,5282,5283,5286,6171],[1040,1670,769,352,946,1703,899,0,304,306,772,184,4347],[1040,1670,772,320,946,144,4422,304,5161,899,422,184,306,358,769,592,618,4516],[1040,1670,769,352,946,1703,144,304,306,802,899,40,809,184,420,618,4516],[1040,5755,769,306,4448,946,1703,0,4404,304,900,1556,4753,968,4754,224,1041,2119,4276,32,570,1335,4996,5222,5227,5299],[1670,769,352,5136,953,1041,4128,1370,419,5574,592,4403,4422,4448,4516,0,184,304,338,456,4262,4482,4657,4660],[0,5136,4262,306,5040,4404,1670,4136,768,371,1696,4416,5120,4403,4448,4128,4133,4176,4868,5043,3,32,323,864,4138,4181,4754,49,144,184,224,256,4098,4422,4753,4889,4995,5365,5875,5953],[1040,1670,769,352,946,1703,0,304,899,306,4753,592,618,802,1033,184,437,4516],[1040,1670,769,320,946,1703,304,772,4404,1664,1722,144,358,1033,5541,5891,180,310,592,4516],[1040,1670,352,769,946,1703,772,899,0,304,306,1969,618,1658,4347,224,420,1033,4516]]

def wr7 : List (List ℕ) := [[1040,1670,352,769,946,1703,0,304,306,802,1658,772,809,864],[1040,1670,769,320,946,1703,304,4404,1664,5072,180,4448,358,772,144,224,968,1033,4516,146,184,592,1722,4898],[1040,0,5818,946,306,5755,772,304,4404,4405,320,146,769,4448,424,864,1041,35,326,359,1928],[1040,1670,769,352,946,424,772,1339,0,304,72,374,1969,35,184,1041],[1040,1670,769,352,946,0,424,1339,304,1658,840,91,40,72,1041,4404,4422,35,1928],[1040,1670,946,352,772,1703,802,4404,306,304,224,1269,1339,1034,184,681,4898],[1049,1670,352,769,946,1703,772,4289,306,304,1556,516,5064,1033,5076],[1049,1670,352,769,946,1703,327,304,5072,4289,1556,516,1152,5064,4288,5076],[1049,306,769,1682,1703,953,304,1556,658,243,352,5042,81,519,4098,4264],[1049,1670,769,352,427,946,327,304,772,4468,243,5064,1556,374,1152,4289,4708,5076,6170],[1049,1670,769,352,1703,5064,327,304,1556,183,243,4468,40,81,4597,5042,0,145,976,4289],[1049,306,144,946,5755,772,419,304,146,1928,4289,82,374,864,4276,4699,4722,88],[144,1049,306,728,304,1703,4898,5755,769,5042,4288,5161,1449,183,4181,4753,5904,243,1339,4754,81,4276,4289,4448,4889,146,976,1412,4098,4264,6024],[1049,306,144,946,5755,772,1703,304,899,81,1928,100,146,4264,4272,4276,4289,0,4288,4699,4722,4753],[1049,1670,769,352,1703,953,899,304,243,81,306,1075,0,1169,5301,184,420,1255,1339,4550,4999,5129,5299],[1049,306,144,946,5755,772,352,1703,304,968,146,1928,0,864,4276,4289,1033,4288,4699,4722,4753,5076],[1049,1670,769,352,946,1703,306,304,0,899,81,224,4276,4288,4289,40,105,184,976,2009,4699,5064],[1049,1670,769,352,946,1703,306,304,1556,5072,1152,4276,4289,224,1269,4288,4699,5076],[1049,1670,769,352,946,1700,306,304,1556,5072,1152,4289,4468,5818,144,224,427,4457,4521,5064,5076],[1049,1670,769,352,946,1700,306,304,1928,81,144,899,5818,184,808,1033,1269,5076],[886,5130,5074,5673,914,1333,5113,980,5123,4970,912,1364,5079,624,887,1200,1666,5761,1362,2088,982,1046,1173,1366,1555,1579,1634,2004,5137,5474,5664,598,865,918,923,954,1025,1030,1063,1191,1371,2072,5136,5250,5546,5696,5746,6176],[1040,306,946,1670,769,592,304,5152,1703,352,4262,599,1556,979,4516,608],[946,807,5554,6177,4378,6038,2074,754,5008,641,849,501,747,4633,4913,276,1569,4388,4939,5073,294,755,759,1603,4386,5066,5077,5557,6105,277,757,945,1003,2069,2102,4342,4705,4706,4710,4818,4854,5059,5098,5177,6168],[1040,5771,946,1328,4280,807,872,849,1664,968,1379,1062,1556,58,276,1157,706,841,1072,4386,5474,277,747,945,1030,1033,1067,4704,4824,5048],[5064,769,85,5049,6023,5040,4330,4898,4916,6034,4182,4897,4212,98,101,259,4187,4178,4371,4617,4736,4823,4920,6168,107,279,1136,2009,4196,4697,4887,4896,5066,5223,96,771,788,961,992,1137,1138,4215,4224,4359,4631,4741,4743,4902,5219,5225,6005,6040,6042,6048,6100,6102],[946,769,5554,5008,230,6023,2083,754,166,501,5073,98,807,809,5064,233,242,276,4212,4916,4939,5556,85,246,755,96,107,257,709,722,788,961,992,1569,1603,2002,2069,4215,4353,4369,4688,5066,5223],[1040,1670,243,769,352,963,1703,385,81,304,1556,224,4593,0,4898],[1370,769,1670,5074,352,4182,953,1696,507,304,1024,98,81,374,4202,4593,52,184,224],[1040,5755,769,352,946,1700,4182,1664,304,81,146,243,807,0,802,1336,4202],[1040,886,979,325,1701,953,805,2081,785,5123,821,4473,400,4465,1082,5203,5514,308,982,1083,1434,378,787,808,865,954,1033,1584,5451,6176],[1040,1670,946,352,769,436,1339,304,979,72,389,22,184,5203],[1040,224,5771,306,769,953,1696,304,1556,1355,507,4645,86,5161,88,978,4322,369,496,4763,5435]]

def wr8 : List (List ℕ) := [[1049,306,4262,769,1670,4645,243,1696,304,5040,544,864,224,33,374,658,786,1027,5123,81,562,4761,4898,5217],[728,4898,306,427,4901,304,946,1670,802,772,978,1664,4645,4968,4405,4903,5220,0,224,1034,4272,4536,4761,5159],[1040,306,4262,769,592,5771,946,304,1700,1269,599,802,1556,4339,4714,144,608,807,4409,4411,4448,4516,4898],[1040,1670,946,352,1700,769,306,304,802,166,1556,224,1269,4898,4903,81,599,1017,1033,4272,4536,5220],[886,1062,953,5673,5074,1333,1032,5123,887,1029,4970,1353,980,5761,912,1666,994,1362,1634,5079,914,982,984,1046,1067,1366,1555,1579,5113,5137,5474,865,918,923,954,1030,1033,1072,1371,1584,1587,5136,5156,5664,5689,5696,5746],[872,5700,1040,4262,4467,5099,5078,4242,209,183,5652,402,1098,4248,6011,5657,5766,1094,1248,1397,1586,1938,4266,4294,5627,152,160,194,803,848,931,1010,1345,1430,1641,2129,4279,4299,5317],[1556,1186,5700,4704,4467,5099,1040,4248,5714,872,5078,183,343,1732,5652,4297,209,420,1700,1721,4262,5657,5766,6011,402,1094,1185,1586,1938,144,151,160,453,803,848,1010,1345,1397,1428,1641,4532],[385,243,5008,4435,6024,4279,5771,5042,4938,4533,5097,154,1365,4930,945,4384,4538,289,293,521,522,631,752,1606,4634,4934,5073,6026,6187,448,459,499,512,628,642,646,871,1603,2071,2098,4569,4571,4613,4630,4704,4842,5065,5177,5748,6011,6032,6049],[946,5771,841,968,5008,1664,1344,5097,1365,4913,6025,6177,6026,281,291,631,711,741,1569,4368,4610,6186,628,646,650,945,1003,1043,2001,2069,2096,2100,4632,4704,4745,4821,4824,4833,5098,5177,6185],[728,769,243,1682,5008,5064,385,4916,4696,4533,739,5042,6026,809,4736,233,242,4321,4538,200,246,517,5223,154,250,448,497,522,709,788,871,961,2064,4279,4369,4568,4593,4630,4896,5065,6024,6032],[728,769,1682,1346,5008,946,6025,968,385,501,1047,242,276,835,4736,6026,200,246,739,154,250,594,650,709,788,961,1003,4353,4916,5064],[1040,886,979,325,953,5673,805,785,5123,308,4473,5203,2081,5761,400,887,1050,1082,787,982,1083,1434,1555,1888,360,808,821,865,954,1033,1353,1584,1701,5451],[4824,4262,328,4982,4453,181,4242,306,864,1923,209,1782,1930,402,4297,4423,184,806,1078,4616,390,537,743,889,1379,1393,1430,4963,5345,146,160,502,1418,1442,1595,4248,4468,4825,5012,5317,5448,5537],[1370,1045,4824,5536,48,899,970,4982,1659,1014,1379,4968,5463,5545,5889,406,1878,39,116,706,715,881,932,936,997,1093,1360,1377,1392,1414,1435,1442,1595,1601,1609,1611,4193,4821,4825,5012,5461,5542,5671],[1370,5136,953,5771,5074,899,5904,4500,1030,5097,1062,5889,1633,1659,887,945,1032,4148,1371,706,882,885,898,1029,1033,1067,1072,1414,1435,1555,1611,4821,4824,5156],[1370,769,1670,5136,352,953,978,1696,304,899,98,1062,1478,181,184,1033,1067,1659],[1556,4242,343,1923,181,4467,1064,1930,5700,1939,872,4262,209,5539,1442,1444,4297,5651,4737,5652,5657,5766,160,184,356,402,1248,1586,4933,5831,146,465,1010,1397,1430,1457,1782,1911,1938,4248,4299,4533,4744,5317,5537,5585,5627],[1347,1057,5766,977,195,1574,872,1027,1928,5652,1529,5545,167,1761,2051,931,1397,1526,1556,1762,4295,458,467,628,1010,1011,1442,1457,1506,1601,1609,1639,1704,1745,1938,4737,5541,5542,5704,5779,5827,5912],[1556,1700,4467,144,4262,1064,5766,1808,1939,1923,1930,343,1190,1721,356,1577,4297,181,209,4737,5657,160,184,402,1189,1428,1586,1732,4933,151,425,432,453,455,872,1010,1176,1397,1432,1475,1590,1776,1911,1938,4532,5537],[1040,306,4262,946,618,4242,886,4533,5097,1923,184,343,1782,243,841,5079,209,328,402,864,945,1430,5345,5539,146,181,291,390,521,650,4704,6024],[1370,769,1670,5136,4182,352,953,5120,507,1696,304,98,887,81,1478,184,224],[1040,306,4262,946,4242,5771,618,5074,968,5097,343,4533,243,5079,209,328,402,841,864,1248,1923,4824,146,154,184,291,390,650,706,1430,4453,4616,4704],[1040,306,946,5771,592,772,304,4242,802,307,1923,1186,1556,4961,417,599,1042,1078,5075,81,144,184,385,618,1428,4449,5127,5152],[1040,1670,946,352,769,1703,4533,385,618,304,899,802,48,243,728,978,4264,184,200],[1370,1045,1670,181,419,899,4824,5096,4982,1379,1930,4262,151,368,5435,374,5574,209,378,406,537,889,1782,1878,1939,116,160,307,390,502,1659,4454,4825],[1370,1045,4262,899,181,419,5766,970,5096,4982,402,151,5435,374,5574,184,209,328,406,1379,1878,1939,160,307,390,456,502,1659,1930,4454,4825],[1370,1700,899,1857,995,5435,1670,23,209,1665,100,402,1930,1939,338,1360,1878,73,306,390,406,537,1379,1478,4262,184,369,502,1808],[1370,1700,970,899,4982,23,1670,5435,209,1045,402,5889,306,181,1478,73,390,406,1379,100,307,328,502,995,1659,1808,1878,1930,1939],[1670,1057,4467,1928,23,1703,977,327,1027,209,4262,343,356,4295,391,1410,1529,100,181,184,216,458,468,1478,1586,1722,1779,1930,1939,2051,4737,5617],[1670,1703,977,1027,4467,164,209,343,2051,356,1057,1808,1915,327,1478,73,391,402,1011,1730,184,216,458,468,1529,1857],[1670,1057,977,4467,164,419,1027,209,327,343,356,1915,73,391,458,1011,1190,1529,1730,1857,184,216,1176,1189,1478,1586,1930,4262,5617],[1670,1057,977,4467,23,419,1027,1808,209,4262,343,356,1478,1915,327,1255,1765,4295,186,391,402,464,1011,1347,1930,216,458,1176,1189,1190,1208,1529,1586,1857,1939]]

def wr9 : List (List ℕ) := [[1670,1057,977,4467,144,419,1027,209,164,343,1915,356,1808,327,1478,2051,73,391,402,468,1011,1190,1730,184,216,458,1056,1176,1189,1209,1529,1857,1938],[1049,5755,769,1370,946,1703,352,899,968,304,1027,1928,1878,0,146,807,1808,4257,5435,144],[1040,306,769,1670,946,1703,304,899,802,0,592,184,352,452,1017,1033,1255,4536],[1339,769,352,1670,946,1040,1703,304,403,5755,1050,4409,1410,373,5435],[1040,5755,769,352,946,1339,1703,304,4498,1050,1410,979,5435,22,373,1033],[1040,1670,769,352,946,1703,1339,304,72,791,4409,4898,184,807,899,1033],[1040,5766,946,1328,886,1562,980,872,1379,1556,5130,789,906,944,1090,1638,2088,5113,6177,1173,5474,898,945,962,1030,1191,4962,4976,5732,6182,6185],[224,6096,4883,6011,5049,4891,6097,5042,4896,704,1904,4593,4598,769,4328,4690,4887,6007,4599,4810,4322,4817,4874,230,233,242,722,4321,4323,246,944,4339,4597,4600,4688,4694,4809,4867,5073,512,709,712,723,788,1906,1913,2002,2064,4592,4596,4693,4695,4698,4705,4706,4811,4816,4866,4899,5059,5065,5066,6001,6003,6008,6010,6024],[946,807,5555,6177,4378,6038,754,612,5010,641,849,501,747,4633,4913,5556,276,2074,4388,4939,5073,294,755,759,4386,5066,5077,6105,277,757,962,1003,1080,1920,2010,2069,2102,2103,4342,4705,4706,4710,4818,4854,5059,5712,6050],[1040,5771,946,1370,1562,899,849,807,1633,4500,968,1556,5172,58,841,167,291,368,980,2085,347,962,1033,6177],[1370,769,1670,261,5136,352,5064,507,5120,1696,304,385,953,4182,4132,4357,4593,0,52,81,184,224,4202,4323,4339,4597],[1049,5755,946,352,772,1703,1339,304,807,166,370,802,1027,1878],[1040,224,5755,352,804,5064,1556,1715,385,2081,243,1379,4868,1339,4327,201,4898,86,1537,4128,4328,4339,4356,4597,178,304,519,4593,5203,5365],[1040,1670,224,769,352,946,1700,1339,1269,72,304,4132,4327,184,570,1379],[1040,306,224,5771,772,1700,946,304,1556,802,1269,243,4411,807,4117,4132,4202,4327,4357,4361,4898,5435],[1040,224,5771,306,769,1696,2081,304,1556,183,243,86,374,658,4327,4356,4645,5466,22,4117,4131,4132,4202,4322,4328,4357,4361,4411,4416,4593,4643,4898,5435],[1040,1670,769,352,592,946,306,304,1703,1928,5064,1556,0,81,4707,4898,166,243,599,608,807,2009,4516,4726],[1040,1670,352,769,946,1703,1339,304,72,772,4898,224,1152,166,184,243,420,608,807,4202,4327,4516,4726],[1040,306,769,5755,1928,946,1703,304,0,166,320,807,81,864,802,4707],[1040,1670,352,769,946,1703,1339,304,0,72,4550,224,599,81,1269,1928,4898,184,807,4132,4327,4516],[5042,370,790,4279,4983,5682,4242,5456,337,4274,955,344,944,5769,945,5175,1013,4294,5478,154,500,965,4475,4618,4634,5073,5083,5188,5480,5490,5685,869,976,1351,2071,4261,4277,4613,4614,4625,4627,5082,5169,5320,5352,5770,6011],[946,306,5136,154,4961,5766,194,789,4963,209,864,402,4242,944,976,1024,1030,1397,4294,4490,160,885,4279,4291,5317,5700,6011],[243,1682,4930,4279,5041,5097,6024,5347,5010,4938,1367,513,4849,154,631,1818,4384,6035,293,521,752,1828,4613,4630,4634,4934,5073,5906,6187,329,433,448,499,512,628,642,646,713,1080,1557,2007,2071,2098,4568,4704,5065,5337,5929,6032],[728,1047,1681,946,1346,968,841,5097,1354,5010,5073,4610,6177,281,1680,6025,6035,291,631,6186,628,646,650,708,741,962,1003,1080,1367,1910,2000,2096,2100,4704,4745,4821,4913,5066,6185],[1040,5771,946,1370,1562,899,980,4500,1633,968,167,1556,5172,789,841,994,291,368,355,898,962,1033,1611,1928,4821,5113,6177],[1049,306,769,1703,5042,496,1682,304,1339,507,81,183,656,1027,352,5123,519,4187,5064,5217,25,1556,5435],[1049,1670,769,352,946,1703,968,306,1269,304,243,1556,1027,544],[1040,306,769,1682,946,1703,304,1556,243,772,802,305,1339,4327,5064,327,2009],[946,5136,306,6024,4824,618,154,1040,886,5108,1782,1923,4242,343,789,1444,1556,4453,192,806,209,328,402,1430,4279,4294,5345,146,160,465,897,1362,1562,4616],[1040,1670,769,352,946,1703,385,304,772,899,184,1033,1067,1339,4999,5301],[1040,306,946,4242,5766,6024,5108,886,343,618,945,1444,1556,4453,5539,192,1090,5079,209,328,402,1923,146,154,184,390,706,806,897,1362,1430,4279,5317],[1049,728,5771,1370,946,1574,999,899,4500,945,5545,841,1928,291,368,631,1555,6177,1,116,167,898,962,1611,1704,2051,4821,5541,6182]]

def wr10 : List (List ℕ) := [[1040,306,946,1670,772,1703,304,968,899,0,1042,1556,25,965,980,4273,5220,5252,6026],[1040,306,946,1562,618,728,1928,999,1556,4500,1782,886,167,968,5904,631,841,1412,209,243,291,328,154,458,4279],[1040,306,1928,1682,946,4242,5074,999,4500,968,899,167,618,841,146,209,243,291,328,1,154,184,390,1339,1574,1923,4279,4824],[1040,728,5766,1370,946,1574,999,899,968,4500,5827,167,789,1556,1928,5545,291,368,2051,1,467,898,931,962,1033,1207,1601,1611,1704,4821,5541,6177],[1049,5755,946,1370,769,1703,352,4133,304,899,1269,4498,4,1878,4132,144,452,5574],[1040,1670,769,352,946,1700,1339,72,243,304,81,618,1269,599,1478,0,184,1255,1765,4132,4133,4182,4202,4357,4820],[1040,1670,769,352,946,1703,306,304,1339,1269,81,4132,184,976],[1040,1670,769,352,946,1703,1339,304,72,1269,81,4132,184,224,452,899,1033,4327,5220,5574],[1040,1670,769,352,1703,953,1339,243,304,98,81,4327,0,184,224,899,1088,1255,4131,4132,4202,4328,4357],[1049,1670,769,352,946,1703,1339,618,1269,81,224,304,370,4182,243,4133,4820,0,184,452,570,899,1379,4132,4202,4327,4357,5574],[1040,1670,769,352,946,1703,304,306,802,243,899,1042,0,81,184,5076],[1040,886,805,325,1701,5143,2011,308,2081,5123,4905,4473,1152,4465,376,1082,2101,5514,6176,624,808,887,982,1050,1065,1083,2072,155,378,598,821,865,912,914,1579,1733],[5040,4898,4519,4881,5064,4281,4330,2122,768,11,1121,4212,6034,5049,88,98,677,4897,6168,87,791,947,2119,4178,4180,4256,4371,4736,6176,107,279,681,2009,2075,4307,4617,4647,5398,101,259,554,816,832,992,4196,4306,4359,4512,4896,5066],[1040,886,979,325,1701,953,805,2081,785,308,5123,4473,4465,6176,376,1050,1082,5514,5817,1065,1083,378,808,821,865,954,982,1033,1434,1584,1618,1705,5143,5152,5203,5451],[1040,306,769,5755,946,1703,304,979,5152,4262,352,772,864,4516,4602,420,608,1033,1056],[1040,1670,769,352,946,1700,385,802,304,243,48,1339,224,4409,4602,184,4898],[1040,306,802,1670,772,946,5814,304,5064,243,979,1339,4405,1556,4602,4898,608,1928,0,17,5203],[1040,1670,769,352,946,1703,306,304,48,592,1556,802,1928,4409,166,608,4516,4602,4898],[1040,306,769,5755,946,304,1339,5814,979,352,4405,772,146,4602,1033,5435],[1040,1670,769,352,946,1700,1339,304,72,802,48,389,1928,4409,184,1033,4602,4898,5435],[1040,1670,769,352,946,1703,306,304,802,1556,48,592,1033,4404,4516,4602],[1040,1670,769,352,946,1703,306,304,48,1556,592,802,1033,4409,166,608,4516,4602,4898],[1040,886,979,325,953,5673,805,785,5123,308,4473,2081,4465,376,887,1082,2101,5514,982,1050,1083,1353,787,808,821,865,1033,1434,1555,1584,1701,5817],[1040,306,1682,946,968,304,1703,768,4257,1556,243,681,48,4468,195],[1040,886,979,325,953,1701,805,785,308,5123,4473,2081,4465,376,887,1050,1082,5514,5817,1065,1083,4905,360,808,821,865,982,1033,1353,1434,1555,1584,1618,1705,5152,5203,5451],[1049,1670,946,352,772,427,1339,979,304,72,100,389,1556,4602,1050,5203],[1049,1670,769,352,946,1339,427,979,304,327,389,772,1556,4602,5435,1033,1050],[1040,352,1556,769,5064,1670,4405,4409,243,304,327,0,195,419,953,4898,81,887,1050,1339,83,786,1410,4289],[1040,1670,769,352,1703,953,1339,304,243,327,4409,0,81,195,184,1255],[1049,1670,352,946,772,1339,419,4276,195,304,5755,5192,802,72,144,4699,5076,5511,457,728,1033,4289],[1040,306,144,946,5755,768,1703,304,968,1339,5161,5904,48,243,81,146,681,195,1412,4257,4289],[1040,1670,769,352,946,1700,899,304,1269,306,507,81,224,1556,0,144,496,1120]]

def wr11 : List (List ℕ) := [[1040,1670,769,352,946,1339,4276,304,419,72,195,1715,184,311,403,899,1033,4289,4699,5076,5192,5511],[1040,352,1670,769,946,1339,419,772,304,5755,4276,72,1715,4443,1033,1076,4699,5076,5192,5299,5511],[1040,1670,769,352,946,1339,304,5755,979,4457,5818,772,4405,72,427,4443,5076,144,1033,1076,4468,4521,5192,5435],[1040,1670,769,352,946,436,1339,304,72,389,48,4409,4457,144,184,427,1033,1076,4521,5076,5435],[1040,352,946,5755,772,436,1339,304,306,4405,100,4443,4455,144,183,1033,1076,5076,5192,5299,6026],[1040,1670,769,352,946,1703,1339,304,72,48,791,1715,4276,4409,5435,184,899,1033,1076,5076],[1040,1670,769,352,946,1703,304,306,144,899,0,48,81,243,4264,4276,184,195,968,1033,4257,4289,4699,5076],[1040,1670,769,352,946,1700,306,304,1339,224,979,0,81,4468,4898,5755,99,144,243,427,1033,4202,4602],[657,5042,4291,4868,33,978,809,152,231,818,245,4834,4136,6107,769,731,27,32,517,745,4277,262,739,774,4696,4836,519,950,4259,8,257,497,615,688,730,791,810,993,1285,1296,2003,2064,4117,4258,4260,4261,4263,4275,4282,4290,4352,4705,4706,4840,5059,5091,5386,6037,6218],[313,2081,4487,4099,342,4868,978,599,630,5161,354,1608,183,4114,4480,5075,4240,4280,33,245,769,49,4723,0,497,643,774,791,809,950,2064,4291,4888,5029,6107,6218],[657,2081,769,4161,4144,978,33,4280,4152,4868,1267,820,25,809,52,38,51,183,199,818,976,6197,32,58,152,182,212,952,961,4114,4151,4277,5397,8,675,682,774,778,810,833,992,998,1275,1282,1285,1291,1296,4258,4259,4260,4261,4263,4291,4896,5091,5379,5386,6161,6210,6218],[1040,1670,946,352,772,1700,385,304,507,802,0,899,184,886,1878],[5041,769,0,4280,978,4099,1608,891,6197,2081,4155,809,4114,176,183,1738,3,2021,4119,212,599,820,961,4112,6218,25,33,49,152,202,643,778,792,810,952,1270,1275,1282,1291,1296,2037,2073,4291,4723,5067,5368],[5041,497,2075,1931,2080,251,809,5042,6022,4834,769,231,615,731,745,5080,729,245,262,528,739,1908,4836,4903,258,274,283,641,726,791,4696,4731,257,517,523,532,617,710,779,784,816,827,950,993,1003,2003,2064,4352,4705,4706,5059,5091,5107,6037,6039,6041,6043],[1370,769,1670,507,5136,352,5064,5120,1696,42,304,953,98,405,1878,245,1269,81,83,184,224,4339,4597],[5041,772,331,5814,802,978,1608,354,4487,4114,4901,641,2081,4903,49,152,25,178,497,599,643,916,950,1738,2064],[313,2081,0,231,4280,769,978,5075,5161,54,5365,52,183,4263,245,739,745,822,4118,49,730,774,150,202,497,4119,4344,4345,4376,4696,4868,4883,4900,5395,33,208,634,791,916,917,950,967,2064,4208,4260,4277,4347,4673,4882,5368,6107,6218],[728,1703,352,5074,224,1670,804,953,1107,306,83,304,656,243,1556,1024,256,2081,4868,5435],[772,331,1608,4901,1017,5814,802,2081,354,4487,4114,183,245,49,152,4890,5076,497,599,916,950,2068],[5041,769,0,4280,978,5365,2081,54,225,6197,809,4112,4114,4263,822,4119,25,49,152,232,818,820,3,182,961,4144,4900,5369,5395,33,52,183,202,208,599,634,657,778,786,952,967,992,2070,4118,4208,4260,4277,4347,4673,4774,4890,5067,5362,5368,6218],[1040,1670,769,352,946,1700,306,304,1269,507,0,496,1556,224,369,802,976,4898,5435],[5041,772,54,5814,4901,1269,1608,891,1017,4114,802,17,4305,4119,212,2021,2081,4112,4890,5076,25,49,183,599,778,810,952,1282,1291,1296,2037,2068,4673,4774,5067,5368],[5041,772,331,802,5814,4901,1608,354,1017,4487,52,729,4903,49,72,152,978,2081,4890,25,33,178,497,599,916,950,2064],[1040,1670,224,772,352,946,1700,385,802,304,1556,1107,978,5435],[5041,772,331,5814,4901,802,1608,354,4487,4114,978,4903,152,49,1017,2081,4890,25,178,497,599,916,950,2068],[1040,1670,769,352,802,946,5814,4901,304,323,1017,243,1269,1556,4405,1041,0,1928,5064,81,224],[1040,1670,769,352,946,1700,385,1269,304,1339,4132,52,81,184,224,570,976,1878,2009,4448],[1040,1670,769,352,946,1703,306,304,1556,420,1152,0,224,5076],[1040,306,769,5771,1700,946,304,496,1269,507,1556,0,86,4404,224,1783,516,1033,4996,5435],[243,1682,195,774,193,5042,370,4242,4983,4868,337,5075,5682,809,32,27,242,233,246,344,519,818,945,1367,4263,4618,4696,5490,5713,152,520,521,642,657,810,869,1818,2007,2064,6107,6218],[728,5136,352,144,769,5755,1339,4868,656,1060,304,4754,4405,5042,243,427,4809,32,1556,183,338,4888],[728,772,306,1670,592,1047,946,304,144,5075,802,1027,1339,1700,1721,420,184,1923]]

def wr12 : List (List ℕ) := [[728,769,1682,192,243,4983,4242,161,337,5042,370,809,976,183,820,27,242,4296,4868,5075,5682,32,233,246,344,818,961,4263,4696,5397,152,250,519,642,657,774,810,869,998,1818,2064,5713,6107,6218],[1040,306,769,1670,507,427,656,5040,4754,304,864,496,5682,374,25,32,81,978,4182,4868,184,224,459,519,900,961,4448,5367],[5041,769,1682,243,5010,1931,4696,1367,2080,154,745,809,2075,251,233,242,528,739,6024,246,513,791,4731,6022,6035,448,497,523,532,617,641,704,709,779,784,816,827,1003,1557,1818,2007,2064,4353,4706,5065],[728,1703,352,769,5075,1670,953,5146,224,1027,327,304,144,1556,243,369,774,6104,7,355,5042],[728,1703,352,769,1339,5075,144,224,1658,5146,5042,1027,1556,304,243,4809,4898,369,820,961,6104,146,148,519,665,1412,5435],[1040,306,946,1670,772,1703,304,802,1339,4901,33,311,1556,1928,978],[1040,1670,769,352,946,1703,1339,802,304,5075,243,370,5128,5435,1060,420,1255,1969,0,184,224,1017,4458],[1049,5755,946,352,144,772,1700,1339,618,1047,304,728,802,4498,1412],[1049,1670,946,352,772,1703,144,1339,304,968,5146,72,4714,184,361,420],[1049,1670,769,352,946,1703,144,385,304,618,899,968,32,728,1047,184],[1049,1670,769,352,946,1703,144,304,306,968,1047,592,899,184,618,1027],[1049,1670,769,352,946,1703,1339,304,72,0,144,618,677,968,184,420],[1040,306,769,5755,946,1703,304,1928,728,1339,618,772,809,81,146,86,1412],[1049,1670,243,772,352,1703,946,4182,1339,304,968,4820,72,144,507,4133,5064,0,81,184,1412,1928,2009],[1040,1670,769,352,592,946,1703,304,802,4901,306,1928,1339,772,4714,184,978],[1040,1670,769,352,946,1700,4182,385,304,507,1269,1339,81,840,0,144,184,224],[1049,5755,769,352,946,1703,899,304,1269,4133,4498,0,1339,81,144,507,976,1878,4132,4448],[1049,1670,769,352,946,1703,1339,4133,304,0,72,507,32,1878,4132,81,144,184,976],[1370,769,1670,1047,352,1703,946,968,304,899,1027,1269,1928,72,144,184,224,1339,1878],[1040,1670,769,352,946,1703,899,304,1339,224,5700,1152,1269,5435,1067,1878,4699,5511],[1049,1670,769,352,946,1703,385,304,1339,4133,1269,592,1878,81,184,452,4132,4660],[1040,1670,769,352,946,1703,327,304,243,1556,0,81,1041,4550,420,464],[1040,1670,769,352,946,1703,306,304,899,0,592,1060,81,144,184,618,1210,1255,1928,4422],[1040,1670,769,352,946,1703,1339,304,72,243,1152,0,5172,81,184,420,1255,4422,4550,5076],[728,772,352,1670,802,5075,1703,946,5146,1339,243,304,5128,327,4550,180,1060,4901,5541,0,81,420,452,1017],[1049,1670,769,352,946,1703,899,304,507,1339,5435,5700,0,81,224,1107,420,1379,4999],[1040,1670,769,352,946,1703,1339,304,72,5329,0,224,1060,1498,81,145,184,420,899,1210,1255,1435,1969,4458],[1040,1670,769,352,946,1703,899,304,4182,507,306,4133,4820,1269,81,0,184,224,1336,4132,4202,4357,4699],[1049,1670,769,352,946,1703,899,304,144,306,802,1928,4456,1339,5127,184,420,968,1047,1107,1923],[886,1062,953,5137,5123,5074,887,980,1353,1559,4971,5079,1033,5744,912,1666,994,1362,5451,5664,914,984,1046,1067,1366,1579,1584,1872,1888,5136,5474,5953,865,918,923,954,1029,1030,1051,1072,1155,1333,1364,1585,1587,1635,1879,5160,5696,5969,5988],[864,4145,4488,1670,4982,903,5450,4500,82,740,1659,1675,66,1335,5972,913,1633,4471,5899,71,336,758,5766,5987,123,882,898,1673,1786,1866,1894,1895,4154,4497,4818,4963,4987,5205,5674,5778,5779,5973],[899,1062,1670,945,4145,4500,953,5097,978,1203,1328,5650,887,1033,1339,1371,4488,1067,5889,882,898,1029,1072,1555,1633,1659,4987,5137,5427,5904]]

def wr13 : List (List ℕ) := [[4448,867,4452,1876,4421,4419,16,4837,4426,900,4808,1800,4401,84,690,874,1511,4776,1334,4968,5334,5336,5971,5986,64,306,875,1363,4490,4771,4848,4851,667,674,888,898,1129,1130,1137,1138,1672,1881,4210,4427,4433,4438,4489,4835,4987,5321,5881,5960,5976,6131],[1670,340,352,4982,738,423,5755,16,4837,864,57,377,903,913,4416,82,374,4809,5015,53,59,391,722,4804,55,122,327,721,1673,1862],[1040,1670,769,4419,946,1696,304,4138,323,496,864,961,374,4176,184,224],[1049,1670,769,306,946,1696,81,304,4176,900,1027,968,4709,374,656,4645,5435,224],[1670,5172,963,899,1090,4500,945,1633,999,978,368,1033,5650,1335,5079,1362,5446,5745,5889,882,898,1029,1559,4987,5435,5969,5972],[886,308,5074,400,1701,953,5203,785,5123,887,1033,805,4971,5136,817,821,1666,787,1082,1083,4465,5514,1579,1584,1888,6081,865,1024,1353,1364,1635,1879,1970],[867,4448,4421,4452,226,659,1876,4426,323,4837,1815,1800,4401,566,690,874,249,1511,4346,4658,4968,5217,16,568,875,900,1363,4353,4373,4595,4600,5334,64,84,565,570,674,888,890,898,915,1123,1168,1169,1672,1972,2032,2048,4427,4433,4453,4753,5588,5605],[1040,1670,352,769,946,1700,1339,304,323,1033,22,373,1169,184,5435],[1040,1670,769,304,323,953,436,400,4448,899,887,389,547,900,99,1815,184,1585],[4448,26,1649,315,374,4496,371,10,306,4416,250,1650,4436,244,4113,727,737,5442,369,4119,53,113,323,1653,1654,4116,4183,4339,4843,5424,5880,240,248,384,1330,1648,1656,1799,1859,4123,4134,4326,4354,4401,4427,4437,4466,5443,5573,5590,5592,5911,5913],[4448,1331,1876,256,547,5591,369,323,363,1286,4416,371,1355,235,244,272,4426,5442,306,562,1266,1508,1511,1514,282,576,1304,1363,4339,5429,248,263,379,384,571,1283,1284,1303,1482,1510,1863,1875,4401,4427,5445,5573,6115,6133],[306,1737,1355,256,304,404,436,1286,4448,369,1511,4746,1331,547,1360,3,323,562,1508,235,246,363,371,405,902,1378,4339,4450,234,248,389,1268,1274,1283,1514,1863,1875,6117],[1027,5435,1044,977,5922,167,4551,4963,625,864,1013,1108,1328,4564,1352,1786,4962,5427,5763,920,1011,5202,5553,5595,480,613,881,933,1097,1337,1604,1640,1761,1834,1893,4728,4995,5112,5193,5446,5704,5745,5961],[1040,1825,945,1347,1062,953,886,1096,5763,4551,5097,4970,1108,167,467,625,4968,4995,5427,920,1033,1067,1362,1786,5137,5200,5446,5922,613,628,631,864,881,897,898,1029,1072,1639,4987,5426],[352,1683,4421,55,4837,1800,306,4982,128,4401,16,1307,867,4835,5450,64,1363,4426,4448,4452,4490,4848,4851,84,357,683,1300,1874,1889,2042,4403,4419,4427,4433,4438,4489,4819,4968,5031,5881,5893],[1637,1445,1044,4738,4280,1670,163,5754,1483,5749,625,1027,872,1108,633,1097,421,1754,1793,1824,4282,4293,5610,217,602,1592,1604,1659,1736,1750,1814,4730,5915,210,216,635,640,1458,1505,1523,1524,1674,1787,1826,1829,4728,4740,5767],[1670,1044,352,977,167,4280,5755,1027,209,4416,4563,625,920,306,374,53,391,423,450,1011,82,864,1604,4564],[340,1670,5762,423,738,4467,5755,4150,353,5777,5754,57,356,377,1675,2,387,402,4838,5878,5921,59,69,391,457,721,1445,1592,1829,1893,56,122,1424,1458,1459,1481,1643,1673,1826,4197,4198,4216,4852,5753,5767,5778],[1670,340,352,4982,738,423,5755,16,4837,353,57,82,377,913,4416,374,864,53,59,391,722,1445,4804,4809,55,122,357,721,1673,1862],[1670,1044,4550,4738,184,5749,1445,597,1496,1027,1187,5754,1108,627,4248,872,4297,421,625,1793,1824,5574,454,1188,1483,1592,1659,1717,1718,1722,5907,151,160,216,635,640,1195,1458,1476,1523,1637,1699,1728,1736,1785,1787,1826,1829,4516,5767],[1670,1057,977,2,1347,4550,353,356,1027,209,1187,164,340,343,5755,1639,625,5936,69,391,402,597,1011,1722,144,216,450,454,1188,1476,1592,1826,4516],[81,5136,5771,769,4419,5042,4185,4452,304,677,5120,424,4138,864,4403,2075,945,26,323,1658,4436,4448,0,224,681,886,1127,4176,4257,4337,5953],[1670,4488,5755,4982,4145,5450,4500,82,347,900,740,1675,66,867,1335,1586,4471,5899,5972,71,375,1633,1893,4850,5201,123,336,368,936,1786,1862,4154,4818,4839,5543,5672,5704,5753,5778,5779],[1040,5755,946,347,899,1562,945,4500,5172,999,1346,4145,841,1670,291,789,1033,368,898,1096,1335,1412,1633,4987,5972],[4176,4097,4416,4098,5730,5874,4099,4804,5953,4419,4421,4448,4403,4802,4104,4423,5731,4113,4178,4807,5729,5735,722,4101,4426,4809,5734,5875,53,4107,5733,5737,5877,5954,0,306,1632,4116,4177,4180,4181,4401,4427,4432,4433,4436,4438,4800,4806,5736,5872,5873,5878,5952],[1670,4488,5755,4982,4145,5450,4500,82,347,900,740,1675,66,867,1335,1673,4471,5899,5972,71,375,1633,1893,4850,5201,123,336,936,1786,1862,4154,4818,4839,5185,5543,5672,5753,5778,5779,5926],[1040,5755,946,347,899,1562,945,4500,5172,999,1346,4145,841,1670,291,789,1033,368,898,1096,1335,1412,1633,4987,5972],[1670,340,5762,738,423,5755,4467,4150,353,5699,5777,5754,57,356,377,2,387,402,4838,5878,5921,59,69,391,457,1445,1586,1829,56,122,721,1424,1459,1481,1528,1592,1643,1826,1893,4197,4198,4216,4852,5753,5767,5778],[1670,340,5762,738,423,4467,5755,4150,353,5777,57,356,377,1675,2,387,402,4838,5767,5878,5921,59,69,391,457,721,1445,1592,1829,1893,56,122,1424,1458,1459,1481,1643,1673,1826,4197,4198,4216,4852,5753,5778],[1670,340,4099,4982,4809,423,352,4804,5755,57,82,377,4416,374,722,867,1673,4104,53,59,391,1445,1675,122,306,357,721,738,1862,4101],[1670,1057,977,2,4467,419,353,1027,209,5755,164,340,343,356,464,625,5936,69,391,402,597,1011,1639,1765,216,450,454,1187,1188,1208,1478,1592,1826,4516,4550],[1670,1057,977,2,4467,4550,5755,353,1027,209,5936,164,343,340,356,464,1639,625,1928,69,391,597,1011,1478,1765,450,454,1187,1188,1195,1208,1528,1592,1826,4516,4533,5617]]

def wr14 : List (List ℕ) := [[5136,81,769,5771,306,4176,4185,5042,5120,424,304,5435,949,4099,4419,4709,6002,496,4101,4337,4436,4448,4593,0,49,4181,4403,4416,5953],[867,352,4421,1683,4353,1800,4442,514,16,306,4982,128,1360,4401,4608,4968,672,4373,4426,4448,4600,55,64,84,323,507,570,689,915,1168,1169,1889,4403,4427,5588,5881],[1040,1670,769,352,946,1703,1445,327,304,4550,599,1556,146,4516],[1040,1670,769,352,946,1703,899,304,306,968,1042,82,772,1928,5220,5252,0,184,6170],[1339,352,369,1683,1290,389,5450,371,4416,128,1272,272,306,1307,1360,1478,5449,282,1315,4329,5591,5893,384,563,1300,1314,1514,1975,2042,4370,4385,4401,4427,4496,5460,5481,5491,5924],[306,4448,725,22,369,1796,80,1649,4416,4436,357,26,1650,1799,4443,373,727,4113,371,374,4496,9,49,53,323,358,1653,1654,1667,1780,1802,1810,4116,4129,4183,4843,10,315,384,1636,1648,1652,1655,1656,1816,1859,4401,4427,4805,4822,5880,5911],[864,369,4419,5904,4841,23,4423,4963,4499,5776,323,402,4194,5984,68,874,4449,4968,5760,5894,913,4441,4995,391,1478,1539,1834,4168,4481,4855,5920,65,481,713,898,1591,1865,4466,4987,5914],[1049,352,1339,728,5904,16,1915,5755,423,5108,981,1379,1556,374,4423,18,59,913,4194,4490,5000,328,384,738,875,1591,4995],[1558,422,341,5541,327,162,5680,1670,1483,5778,209,1675,5351,387,402,5829,1827,5777,1499,1589,5607,6002,215,391,4298,210,214,216,466,474,1425,1435,1505,1568,1943,1944,1954,4469,4555,4566,5323,5547,5665,5687,5764,5779,5849,6036],[1040,1670,769,352,946,1703,5329,327,304,899,1537,184,875,1339,5527,6075],[1670,1700,4248,454,5680,1478,327,1906,5541,420,5714,209,1929,23,1186,402,1721,1827,1936,5607,5797,73,100,391,1481,1499,1942,2034,4531,341,452,474,1179,1185,1206,1495,1558,1568,1589,1905,1926,4469,5681,5687,5689],[1370,769,1670,5136,352,953,4449,1041,304,327,420,422,1186,1339,4404,454,1435,4458,4546,5346,5527],[327,341,5449,4423,165,4419,4530,5699,5729,6033,4474,306,1561,5442,5684,402,1763,4304,5424,5435,218,391,443,1764,1947,4437,5432,5618,5734,5920,211,1332,1337,1616,1865,1952,4481,4484,5429,5443,5457,5466,5607,5609,5703,5704,5753,5765,5914,6009],[306,1593,4499,23,5904,5776,4419,4423,5729,369,713,402,68,323,1449,1739,4194,4449,5760,5894,5734,5984,327,391,1539,1604,1834,1865,4168,4481,4841,4855,5920,65,482,483,1450,1478,1642,4441,4466,5753,5914,5921,5927],[963,341,1670,4961,306,422,327,999,4449,5351,4500,945,1024,864,4419,1090,4304,209,4546,5432,5552,391,4963,5547],[1339,5136,945,4419,1670,953,5351,4449,4961,328,422,4500,5097,323,1478,23,209,466,1024,1371,4546,5904,391,5435,5547],[1040,1670,769,352,946,1703,1339,304,72,1537,5329,184,899,1474,1715,4276,5435,5527,6075],[327,5435,374,725,22,4423,4456,4416,1593,306,722,165,369,68,1449,1561,1649,4194,315,1654,1796,4339,4496,53,391,1653,4116,5460,26,323,713,1332,1498,1859,1947,4401,4530,5684,5911],[1339,352,1049,963,423,5755,999,1107,23,4423,1556,4416,82,1715,1593,5435,59,18,122,384,1355],[306,725,369,4098,1796,1649,4416,4423,22,713,1650,323,68,374,1449,4194,4104,4496,5911,53,327,357,391,722,1604,1653,1654,4809,26,315,483,1478,1593,1642,1648,1655,1859,4401,4806,5873,5904],[946,352,1703,769,1670,4458,327,1027,304,4449,1339,4404,420,1498,452,454,864,1107,1478,4546,4560],[1040,1670,769,352,946,1703,327,304,961,1556,599,22],[1049,1670,769,306,4185,946,4242,5435,304,4176,1120,1027,5792,4645,4709,0,146,802,900,26,224,545,1379],[1040,1670,769,306,4242,946,4176,304,0,146,599,4709,374,802,1027,26,144],[1049,352,1339,728,419,164,5755,1915,1715,5096,5904,1379,22,714,4423,5435,59,100,282,986,1449,1537,4457,384,738,1088,1249,1593,1648,4427],[1040,306,769,5771,1700,946,304,4185,864,968,1269,146,1042,5064,6170,0,184,224,772,4337,4443,5435],[1040,1670,769,352,946,1703,306,304,1928,899,81,599,4550,184,875],[1040,1670,769,352,1703,946,306,304,968,4185,1556,592,1042,0,4337,5064,5220,5252,6170],[1040,5755,769,352,946,4242,82,304,1649,599,146,374,772,802,1034,0,224],[1040,1670,946,306,4695,304,802,4242,772,4176,224,4709,0,146,374,1034,4898,5220,26,81,420,496,4645,4761,5253,6170],[1040,4101,5766,5042,325,769,1696,864,304,0,183,4176,32,404,1556,389,1657,4327,4337,224,955,4121],[1049,1670,352,946,769,1700,1339,4138,304,72,656,184,772]]

def wr15 : List (List ℕ) := [[1040,5755,946,352,802,436,1041,1339,772,4898,1269,304,0,4405,82,146,323,4272,4273,4536,5220],[1040,0,946,1658,306,772,1696,4176,304,886,4133,1556,769,389,144],[1040,1670,946,352,769,1703,899,304,0,306,496,1658,4138,772],[1040,0,946,1658,306,772,1696,4176,4416,4133,886,4136,1556,769,4101,4419,389,4448,3,32,144],[0,5136,1658,769,306,4176,5040,304,5120,4133,404,1696,4101,32,864,4180,4807,146,496,4138,4327,4337,3,184,358,4121,4423,5875],[1040,5755,352,946,772,436,82,1041,1269,304,1556,0,323,374,802,4753],[946,338,4498,769,325,1562,886,304,4961,1556,4419,389,0,5122,772],[1040,306,5064,144,769,5771,4961,1696,304,0,5042,864,81,5123,437,5217,183,374,519,1042,4185,25,224,976,1371,1584,4181,4337,4609,4708,6170,6179],[1049,1670,769,352,946,1703,1339,304,968,1107,327,0,224,4185,4337,197,355,807,4138,4753],[1049,1670,946,352,769,1703,306,304,0,1339,184,772,1027],[1040,1670,769,352,946,1703,327,772,304,899,1269,4101,0,184],[1040,1670,946,352,769,1703,306,304,0,1556,1928,599,1152,4272,4536,4707,4898,144,146,1269,5220],[1040,5755,946,352,772,1703,1269,82,304,1649,146,0,656,802,1034,420],[1049,1670,352,769,1703,946,1339,304,724,772,5064,72,1928,802,2000,4185,184,807,4133,4337,4820,6170],[1040,306,769,5771,946,1700,304,437,0,1269,1556,86,146,496,599,4707,4250,4609,6024],[1049,1670,769,352,1703,946,327,1269,304,5064,899,4185,1681,1928,0,81,976,1088,4101,4337,4832,4898,5365,6170],[1040,306,946,1670,772,1696,4645,802,4176,146,224,304,4133,0,544,4709,374,496,4101,4356,4448,4761,5365,49,81,244,571,1120,4098,4131,4137,4138,4646,4995],[1049,1670,769,352,946,1703,0,1339,304,1928,968,72,1107,4550,4185,144,599,1027,5001,5064,5127,5541],[1040,1670,769,352,946,1703,327,304,772,1556,4185,592,1152,0,146],[1040,400,886,4905,1701,5143,308,953,325,805,5123,1033,785,1666,817,887,1082,1083,5514,808,1050,1579,1584,1687,1872,1888,362,821,865,1353,1364,1635,5136],[1040,1670,352,769,946,5814,48,327,304,772,968,1556,374,1033,5064,177],[1040,1670,352,769,946,5814,4138,304,323,48,968,864,1033,1928,4405,3,184,802,1067],[1040,1670,769,352,946,1700,327,48,304,864,1033,184,4422],[1040,400,886,4905,1701,308,953,905,325,805,5123,817,1033,1065,1666,887,1050,1082,1083,5514,5817,785,1579,1687,1872,1888,808,821,865,1353,1364,1584,1585,1635,1705,5136,5143,5152,5203],[1040,352,1670,769,946,5814,899,772,4138,304,306,374,961,82,184],[1040,1670,352,769,946,5814,772,327,48,304,864,1152,374,979,184,1033],[1040,1670,352,769,946,1700,327,304,48,1556,99,0,81],[4448,1331,304,4724,1649,10,4496,1702,315,26,4918,235,4436,306,4405,1650,371,4404,272,4184,53,246,256,323,1363,1508,1511,1653,4450,99,234,379,562,1283,1355,1514,1859,5365],[306,304,1355,224,5571,4448,404,251,363,4498,369,1331,235,6192,3,389,405,547,1514,272,562,1508,5365,246,256,323,1363,4339,4450,5429,234,379,395,666,1283,1472,1863,1875,2099,4214,6112,6117],[304,404,4448,4724,306,4496,4918,436,1041,26,315,610,1511,4405,323,777,1331,4404,1073,1840,235,371,1508,1737,4184,4436,4450,10,99,234,562,1283,1653,1811],[1040,1670,769,306,946,1696,304,0,26,547,772,1027,4709,374,802,496,562,4448],[1670,772,306,946,4496,0,427,304,26,315,802,5128,4448,840,4404,864,1034,184,968,5090,5147]]

def wr16 : List (List ℕ) := [[1040,352,1670,769,946,1703,772,899,304,1445,306,4550,82,146,48,184,420,4516],[1040,1670,769,352,946,4280,304,323,144,768,899,0,146,976,1703,4276,4699,5511,81,184,875],[1670,352,769,1041,424,4185,953,0,304,437,1339,1269,98,4404,4422,5064,81,1658,1667,4458,4898,224,838,1127,4405,4409,4868],[352,5136,1670,963,768,899,4422,5120,327,419,48,4176,304,769,1410,184,326,4369,4448],[0,5136,1670,5040,306,4176,304,4242,5120,4422,1446,2075,1649,1799,48,3,26,769,4180,4097,4136,4264,4403,4448,4754,5043,5883,144,519,864,4106,5365],[1040,352,5755,769,946,1703,1339,772,304,4452,72,373,1033,4138,1096,5435],[1040,1670,769,352,946,1703,306,1445,304,772,1556,4550,48,146,420,4516],[1040,352,1670,769,946,1703,772,1339,304,72,1969,48,184,403,420,450,1033,1096,1435,4516,4545],[1040,1670,769,306,946,4242,304,4176,0,772,4105,4448,374,4709,146,400,549,4455,4516,48,420,496,802],[1040,1670,352,769,946,1703,772,306,304,1556,48,1033,4516,81,146,420],[1339,352,1737,610,369,1683,1269,436,4377,304,306,1355,405,1360,128,288,371,1378,4450,5365,5378,235,389,1140,1274,1514,1840,1863,6217],[352,1339,4918,4724,1041,436,1683,304,235,306,4448,4436,610,777,4404,371,1073,4405,4496,1653,4450,5818,99,128,272,1140,1283,1478,4443],[1339,352,1737,610,5179,1683,1269,436,4377,304,306,5467,405,1360,4496,128,288,371,404,1286,4358,4450,235,389,1274,1514,1840,1873,1892,2042,4147,4214],[352,1041,1737,610,1683,4918,4724,306,304,436,1339,777,1073,1840,4404,4443,4496,128,371,404,4405,4436,4450,5818,99,235,1140,1283,1653,1667,1811,4448],[1040,352,1670,769,946,4280,0,327,304,1703,772,802,1556,1047,516,875,968,4276,4448],[1040,352,1670,769,946,4280,0,327,304,1703,772,968,1556,1047,516,875,4276],[1040,352,1670,769,946,1700,1339,1041,0,304,72,772,82,146,802,184,424],[1040,352,5755,769,946,1703,1339,772,0,304,82,146,72,802,4516,48,420],[1040,306,769,5771,1700,946,304,1269,4185,1556,0,26,496,802,5161,144,4337],[1040,1670,769,352,946,419,899,4185,304,323,0,81,184,224,1715,4337,4699,5511],[1040,1670,352,769,946,424,327,304,48,840,802,899,99,1041,4422,0,184,224,4404,4458,4602,4898],[1040,1670,352,769,946,1703,1339,304,48,802,4404,72,99,358,592,0,1033,4516,4602,4898,5541],[1040,352,946,5755,804,1703,327,1047,304,1556,769,875,1412],[1040,352,1670,769,963,1339,1703,804,304,4423,1050,1556,98,373,40,311,875,1591,4138,5435],[728,772,352,1670,4458,599,1339,4449,953,304,1703,4404,72,1041,82,968,1060,4550,144,183,1478,1498,4292,4546,4560,5128,5346,5527],[728,769,352,5755,1339,1703,4458,0,946,1027,304,802,4404,4423,146,681,82,519,570,968,1107],[1040,1670,352,769,946,1703,327,772,48,304,1556,146,81],[728,352,5161,5755,945,1339,4448,4422,1027,805,963,146,3,427,4423,4888,144,304,338,887,1065,1591,4520,4657,4660,5907],[1049,1670,769,352,1703,946,968,306,304,5064,1556,0,592,976,1047,4185,144,437,1027,4550,6170],[1670,0,1040,5042,304,306,419,4898,945,4138,400,840,864,4868,42,1928,4753,25,182,323,976,4754,81,184,519,4098,4264],[1040,0,5064,1696,306,769,886,304,4423,25,1556,4185,32,864,5161,4181,4337,5042,224,976,4339,4597,81,178,4448],[1040,1670,769,4419,1700,5042,0,304,899,840,1928,4138,3,182,306,4448,4615,25,81,184,323,976,4106]]

def wr17 : List (List ℕ) := [[1040,1670,769,352,946,1700,327,4185,304,4832,1269,1556,4101,0,81,224,4337],[1040,1670,769,352,946,1700,306,4138,304,1556,5072,81,976],[1049,1670,769,352,5814,946,327,304,5064,5123,0,81,4405,224,976,4185,4337,4708,6170],[1040,352,1670,946,772,435,306,304,840,1339,4138,100,1033,5064,0,184],[1040,1670,352,769,946,1700,327,304,4138,5072,864,802,808,1033,5064,0,184],[1040,0,5755,946,304,1703,772,899,82,1047,1346,4133,146,340,4138,4422,72,88,4106],[1670,769,0,352,5136,953,1041,424,899,304,1269,1658,4133,2075,4138,82,323,4101,4753,81,224,338,373,681],[1040,1670,946,352,772,1703,306,968,5076,304,1339,0,4138,184,347,979,1033,1067,4753],[1670,769,352,5136,0,963,32,899,5120,419,304,327,768,4133,4138,4448,1683,4101,4128,4176,184,224,374],[1040,1670,769,352,946,1703,899,0,304,306,452,772,4133,5755,420,450,4138,4422,4516,4545,4657],[1040,1670,769,352,946,1703,1339,0,304,72,772,184,420,450,4133,4138,4422,4516,4545],[1040,0,4262,306,946,1670,1696,772,304,4176,802,4133,4138,4709,323,374,404,4101,4136,4754,3,32,144,4106,4416,4422,4448,4753],[0,5040,304,1670,4961,4176,2075,4436,4403,4419,371,4404,4422,4754,4242,4448,4458,4753,5365,864,5043,5729,178,224,323,1653,4288,4405,5953,26,32,144,256,592,1024,1799,4098,4181,4185,4264,4889],[1040,1670,769,352,946,1703,306,304,4138,0,146,772,1556,5076,802,4516,420,1033,4753],[1040,1670,769,352,946,1703,304,306,4138,772,1339,369,0,184,224,656],[1040,1670,769,352,946,1703,306,0,304,899,772,146,802,4138,184,656],[1040,1670,769,352,946,1703,899,304,306,0,592,4138,40,81,184,4516],[1040,1670,769,352,946,1703,306,304,4138,1556,0,592,1033,40,81,437,4516],[1040,1670,352,769,946,1703,772,306,304,899,1033,4138,184,420,4516],[1040,1670,946,352,1269,1703,769,327,304,1556,0,4101,4898,81,681,976],[1040,1670,769,352,946,1703,304,306,0,899,1033,40,81,184,420,4133,4138,4516],[1040,1670,769,352,946,1703,306,304,1556,592,802,1034,0],[1040,1670,352,769,946,1703,306,772,304,1556,4138,0],[1040,1670,769,352,946,1703,327,304,420,1556,1041,0,464,1168,4660,5297,5346,5527,6075],[1040,306,769,1682,946,1703,304,1556,772,81,1591,4597,224,516],[1040,1670,946,352,772,419,327,968,304,899,1269,4289,82,184,457,1339,4288,4699,4753,5435,5511],[1049,1670,769,352,946,1703,306,304,5072,1556,4289,81,4288,4347,4699],[1040,1670,352,946,772,419,306,304,4289,840,1556,5064,100,4138,1033],[1040,1670,352,769,1703,946,772,306,304,899,81,4138,0,184,224,570,1033,4185,4337,5329,5527],[1040,306,769,1682,5064,1703,352,0,1556,304,953,4185,437,976,1027,1591,4181,5365,25,81,144,224,519,809,2009,4337,4458],[1049,1670,769,352,5064,1703,946,327,304,968,864,1928,4289,4597,5072,184,976,4138,4699],[1040,1670,769,352,946,1700,306,304,1556,1152,5072,224,427,4138]]

def wr18 : List (List ℕ) := [[1040,1670,352,769,946,1703,306,304,1556,5064,5072,4138,4264,4288,4289,81,4699],[1040,1670,769,352,946,427,306,304,772,802,840,1556,1034,5064,224,4138,4289,4468,4708,5061,5253,6170,6181],[1040,1670,352,769,946,1703,306,304,1556,5064,5072,1152,4138,4289,224,4288,4699],[1040,1670,769,352,946,427,306,304,840,1556,1152,5064,5072,224,4138,4289,4468],[1040,1670,769,352,946,1703,1339,4185,304,72,4133,4820,82,1269,592,4832,0,81,184,464,4101,4138,4337],[1049,1670,352,946,772,419,327,968,304,361,899,840,5064,0,427,4138,4289,184,4468],[1040,1670,769,352,946,1703,306,304,1556,5072,968,4138,4289,5064,1033,4288,4699],[1040,1670,769,352,1703,946,1928,306,304,772,81,5064,146,1556,0,144,875,2009,4185,4276,4699,4722],[1040,306,769,5771,1700,946,1269,304,0,1556,4185,496,802,4101,144,516,568,864,1033,4337,4448,4832,5157],[1040,1670,352,769,946,1703,327,1269,304,4185,5755,1339,4404,0,570,802,224,373,681,1478,4101,4337,4832,4898],[886,1062,953,5123,5074,1032,1353,4970,887,1029,5673,980,5746,912,1666,994,1371,5079,5451,5761,914,982,984,1046,1067,1366,1555,1579,1584,1634,5113,5137,5474,865,918,923,954,1030,1033,1072,1333,1362,1587,5136,5664,5689,5696],[864,4995,377,1658,42,306,981,5195,4129,4982,5108,4968,402,502,358,4122,328,1238,4963,5450,5760,59,90,913,1379,1393,1809,4150,4224,4459,5,80,119,882,1235,1251,1783,1866,4107,4423,4466,4481,4603,4628,5000,5319],[949,594,4907,385,89,5771,5097,4341,5040,5049,166,233,4339,835,4224,4922,4810,102,250,4178,4331,4360,266,632,801,4278,4373,4720,6017,114,153,227,533,1939,4200,4211,4346,4353,4369,4435,4603,4693,4821,5059,5077,5177,6163,6193],[946,5771,841,968,5008,1664,1344,5097,1365,4913,4368,6025,6177,281,6026,291,631,711,741,4610,6186,628,642,646,650,945,1003,1043,1569,2001,2069,2096,2100,4632,4704,4745,4821,4824,4833,5098,5177,6185],[1040,5771,946,1328,4280,1664,980,4970,945,1379,5746,841,968,994,1556,5079,1030,1062,1366,4368,5474,5766,631,711,898,1029,1032,1033,1067,1072,2001,4704,4987,5048,5113],[864,5136,1658,4603,4341,4121,89,953,306,1024,4995,5097,978,1379,4339,5650,887,32,358,385,4331,4922,166,328,594,1393,5,59,80,184,801,835,886,1238,4122,4224],[1040,306,946,5771,769,1700,496,304,1556,81,1269,5435,4331,25,4419,86,4598],[1354,769,5064,5771,5049,594,385,89,4341,166,949,250,809,246,4187,4916,242,835,6023,230,233,632,739,4339,4346,5223,117,256,497,788,961,1688,1939,2064,4353,4369,4694,4821],[946,1047,1682,1346,769,6023,968,385,501,5008,166,242,276,835,4736,246,739,4916,250,594,650,788,961,1688,4353,4821,5064],[1040,1670,946,352,769,1700,81,385,48,304,1928,677,1339,86,184,4995],[1049,1670,946,352,769,1700,385,304,48,968,1556,224],[1040,1670,769,352,946,1700,385,304,81,496,1556,0],[5435,867,5,1090,5766,4982,306,5450,21,5170,1035,1561,4459,57,4203,5466,5760,402,4339,5432,59,64,1651,1925,4122,4150,4490,4850,4984,34,51,90,1235,1337,1586,4107,4121,4199,4326,4343,4354,4427,4438,5318,5443,5737],[864,5136,5,106,5771,306,953,5074,89,5435,887,32,5097,5650,1024,1379,4339,4922,4122,166,594,801,1393,4341,4459,5466,5766,34,51,59,114,328,835],[1040,1670,946,352,769,1700,81,385,304,48,224,802,864,978,1269,1928,184],[1040,886,979,325,1701,953,805,400,785,5123,821,4473,2081,4465,887,1082,5203,5514,308,787,982,1083,1434,1584,808,865,954,1033,1353,1634,5451],[5435,1556,374,323,22,1355,4416,5450,1658,86,306,369,4104,4982,315,4113,5760,1796,4339,53,59,265,867,1651,4850,5466,9,25,384,503,1035,1586,1649,4107,4198,4354,4401,4427,5318,5911],[1040,306,946,1700,224,772,5771,5435,1379,1269,4901,81,864,802,4452,304,4763,228,496,570,632,978,5466],[4995,306,377,80,4129,6019,5200,864,6018,1783,1671,209,343,5460,4459,4737,4963,4481,5442,64,913,4150,4537,5760,90,920,1064,4423,4933,5435,5730,184,402,602,1251,1911,4104,4107,4122,4151,4203,4282,4370,4427,4438,4466,4554,4968,5338,5446,5481],[1027,5200,1825,977,1347,195,4995,4963,1057,6035,1013,6147,1529,4962,5427,5904,167,6026,197,467,864,920,1752,5446,5481,5745,613,628,640,881,913,1011,1530,1639,1704,1745,1761,1911,4550,4737,4968,5704],[1040,1825,953,1347,195,886,5650,5097,4970,1529,1062,4968,5745,167,887,1371,467,920,945,1067,1366,4995,5137,5200,5427,5446,5904,197,613,628,631,864,898,1029,1032,1033,1072,1639,1704,4987,6147],[4963,4995,377,1658,306,356,38,5450,1091,4982,1556,502,402,6020,57,4459,5760,86,913,6019,59,64,328,358,1379,1393,4129,4467,4481,4850,80,864,1251,1783,1862,4107,4122,4427,4438,4466,4628,5319]]

def wr19 : List (List ℕ) := [[1049,728,899,5904,4148,4500,714,5889,347,5766,66,1335,1339,1556,4982,1091,1360,4193,58,1379,1412,4827,4850,5201,18,39,116,936,1088,1633,1659,1675,5778,5927,5972],[1339,1049,352,1670,714,423,4148,4416,57,5450,5760,306,374,1360,53,59,391,1915,4194,4827,4850,5755,0,1648,4995],[1049,306,5755,1915,4145,6019,423,4416,209,899,920,5450,195,1715,5760,352,913,4737,6147,53,391,1445,4194,714,1027],[1049,306,977,5755,4145,423,714,4416,209,899,195,352,374,920,1915,6147,53,391,6019,122,450,467,1027,4628],[1040,306,769,5755,946,1700,304,5152,166,599,352,5800,450,608,979,4516,4545],[1040,1670,769,352,946,1700,306,304,599,899,144,184,353,450,4516,4545],[1040,1658,946,306,86,4280,38,89,166,5771,5097,343,4714,835,4331,4922,402,594,864,4339,59,80,114,291,328,650,4121,4122,4995],[1040,5771,946,1346,899,1562,999,4500,167,968,347,5172,841,291,368,789,982,1412,1633,195,197,898,1033,2000,4824,4987,6026],[1040,306,946,5771,86,4280,89,38,5097,166,343,1658,835,4331,4922,356,358,402,594,864,4339,4714,59,80,291,328,650,4121,4122,4995],[867,5435,377,1658,80,38,5450,306,1091,4982,1379,86,6020,4459,5466,57,503,1556,5760,34,358,819,6019,59,64,356,1651,4129,4481,4490,4850,25,51,328,402,1251,1586,1783,1862,4107,4122,4427,4438,5319,5729,6027],[1049,728,5766,899,4148,5889,4500,714,1339,347,5904,66,1335,1556,4982,1088,1091,1360,4193,58,1379,4827,4850,5201,18,39,116,936,1412,1633,1675,5704,5778,5972],[867,80,377,5974,1658,306,38,5450,1091,4982,503,1379,6020,57,358,1556,4459,5729,5760,34,86,819,6019,59,64,356,1651,4129,4467,4481,4490,4850,25,51,328,402,1251,1783,1862,4107,4122,4427,4438,4466,5319,6027],[1049,5766,728,899,4148,4500,5889,714,1339,347,1556,66,1335,4982,1088,1091,1360,4193,5904,58,1379,4827,4850,5201,18,39,116,936,1412,1633,1675,5778,5927,5972],[1049,306,5755,1915,4145,423,728,4416,57,352,714,867,1715,53,59,282,391,1360,4129,4194,353,371,1445,1648,4481,4827,5442],[1049,352,1670,728,23,423,1915,1339,4416,57,306,714,1715,53,59,391,722,1360,4129,4194,5755,353,1445,4481,4827,4982,5450],[1040,306,946,5771,86,4280,89,5097,32,343,1658,166,4922,835,4459,358,594,864,1362,4339,4714,5466,5,34,51,59,80,114,328,650,4121,4122,5435],[1040,306,946,5771,86,89,4280,5097,32,343,166,4922,358,835,4459,356,594,864,1362,4339,4714,5974,5,34,51,59,80,328,650,1658,4121,4122],[1040,306,946,5771,772,1700,304,224,1556,81,566,496,4331,5435,802,25,144,358,4327,4336,4363,4448],[867,4448,22,1658,4809,369,374,4176,86,4416,4982,306,1556,4824,1796,4113,5450,4104,4496,5466,5760,53,59,315,358,1651,4850,6019,0,9,25,323,384,503,1586,1649,1780,1859,4107,4198,4370,4401,4427,5319,5435,5911],[1556,4448,0,306,369,374,4809,1658,86,22,4982,4416,4824,1796,4113,5450,4403,5760,5974,53,59,867,1651,4104,4496,4850,6019,9,25,315,323,357,384,503,1649,1780,1859,4107,4198,4401,4427,4466,4806,5319,5911],[1339,352,1049,1670,738,423,1272,1107,4416,714,899,4982,1715,4113,5442,5760,1360,53,59,306,391,1915,4194,4850,5435,18,1514],[1049,5755,352,728,4104,423,1715,1915,899,4416,57,22,353,714,53,59,391,722,1360,4194,371,738,1445,1648],[1049,1670,352,728,23,423,1339,1915,4416,57,306,1715,714,53,59,391,722,1107,1360,4129,4194,1088,1445,1556,4827,4982],[1040,306,769,5771,946,1700,304,81,1269,86,166,369,323,864,4098,224,358,1653,4448,5466],[1049,1670,769,352,946,1703,306,304,166,48,807,968,1556,802,1027],[1040,1670,769,352,946,1700,899,304,306,224,802,1269,81,144,184,544,1017,1033],[864,5124,4963,4961,5042,5123,5650,5048,1030,5427,4965,1328,945,4962,4968,5045,5739,5122,5136,5653,5738,944,964,965,976,1046,5046,5432,5654,881,882,883,884,885,897,898,955,1024,1337,4967,4969,4976,4987,4992,5040,5426,5428,5648,5649,5652,5659,5667,5728,5732],[886,1062,953,5074,5123,1032,1353,887,5673,1029,4970,980,5746,1666,5761,994,1371,5079,5451,912,982,984,1046,1067,1366,1555,1579,1584,1634,5113,5137,5474,865,914,918,923,954,1030,1033,1072,1333,1362,1587,5136,5156,5664,5689,5696],[899,1048,5766,4148,981,4500,4963,5904,4982,1335,5108,5195,1675,1360,4968,1339,4193,4824,4827,5745,1379,1591,5889,18,39,116,720,882,898,1570,1605,1633,1858,4987,4995,5191,5778,5972],[899,5136,953,5766,5074,1354,4500,1339,5097,4148,5650,887,945,1062,1328,5745,885,1067,1371,1555,1584,39,882,898,1029,1032,1033,1072,1435,1633,1858,4968,4987,4995,5137,5427,5649,5904],[1049,1670,352,1339,1915,4148,423,725,5108,5904,981,4416,374,4423,59,913,1556,4194,4827,0,384,4982,4995,5000],[1027,5766,5827,969,167,1345,5652,5016,872,1094,1574,5689,1525,5768,1761,4295,5194,5545,5752,1397,1526,1641,1669,1762,1938,5089,5541,5604,931,934,977,1010,1011,1040,1098,1435,1506,1527,5687,5704]]

def wr20 : List (List ℕ) := [[1670,1703,1056,969,23,4467,327,1027,209,356,420,5016,343,1057,4295,391,402,1011,1186,1938,162,216,341,454,474,1185,1209,1345,4546],[946,841,5771,385,968,5008,1344,5097,6025,4610,4913,4368,6026,6177,281,756,291,631,741,1664,6186,628,642,646,650,945,1003,1043,1365,1569,1603,2001,2069,2096,2100,4704,4745,4821,4833,5177,6049,6051,6185],[946,5771,4913,968,841,1664,1344,5008,5097,1365,6025,6177,4368,281,6026,291,631,711,741,4610,6186,628,642,646,650,945,1003,1043,1569,2001,2069,2096,2100,4632,4704,4745,4821,4824,4833,5098,5177,6185],[1040,5771,946,1328,4280,4963,980,872,945,1379,5746,841,968,994,1556,5079,1030,1062,1366,4368,5474,5650,631,642,711,898,1029,1032,1033,1067,1072,1365,1664,2001,4704,4987,5048,5113],[1040,306,946,5771,1562,999,1339,4500,167,968,841,899,1681,166,209,291,328,1346,1,195,631,2000,5904],[946,1047,1682,1346,769,6025,385,968,501,5008,242,276,835,4736,246,739,1003,154,200,250,594,650,709,788,961,1688,4353,4916,5064,6026],[867,1090,5435,963,5766,4982,1633,999,4500,5172,4984,1561,355,966,5466,5088,5432,368,1335,1497,5595,5668,5745,928,929,936,1035,1861,5013,5017,5443,5457,5703,5704,5765,5972],[1040,728,1681,945,1347,1562,899,4500,5172,946,999,1556,1339,4148,841,1633,368,789,5745,58,116,355,898,1033,1335,1362,1371,4987,5972],[1049,5766,728,899,4148,4500,1091,1339,714,1335,1556,67,4982,1088,1360,4193,5745,5904,58,1379,1668,4827,4853,5201,5889,1,18,39,116,936,1633,1675,5778,5927,5972],[1049,5771,946,1339,1562,4500,899,968,999,1027,1335,167,1633,841,1681,291,355,368,1555,5745,195,631,898,2000,4987,5972],[1040,306,946,5771,1562,999,4500,167,899,968,841,1339,166,209,291,368,1,195,631,642,2000,5745,5904,5972],[1040,306,946,5771,1574,968,209,4500,5016,5074,167,355,999,166,291,328,841,5972,1,631,2000,5194,5541,5745],[1049,1670,769,352,946,1703,385,304,968,1556,48,200,224,1027],[1040,886,979,325,953,1701,805,400,785,5123,4473,5203,308,887,5761,1050,1082,787,982,1083,1434,1555,1584,1888,2081,5528,360,808,821,865,954,1033,1353,1634,5451],[1339,340,963,1670,352,1107,423,999,4982,23,867,4416,1715,5435,59,306,1049,1379,1556,4194,18,384,919,1088,1668],[1049,1670,769,352,946,1700,306,304,592,802,899,144,4536,184,417,418,599,1027],[1049,1670,769,352,946,1700,306,304,899,144,592,81,184,599],[1339,352,1107,5755,18,1715,728,1915,4982,899,423,1088,57,22,714,4416,53,59,86,391,722,1049,1360,4423,122,371,738,1412,4448],[1339,769,352,1670,946,1040,1703,4416,1681,1050,4409,72,1715,5435,899],[1049,1670,769,352,946,1339,1703,304,4499,72,1715,184,899,1027,5435],[1049,1670,769,352,1339,946,1703,1107,5755,802,304,5435,385,1027,1379,224,81,570,919],[1049,1670,769,352,946,1703,306,304,802,899,592,0,184,1027,4536],[4121,4983,4921,5042,1657,227,166,955,5456,5,4341,4907,944,5009,32,4122,4360,4715,5045,50,965,976,1351,4114,4259,4721,4770,5480,5769,6017,8,27,178,233,247,869,945,4258,4331,4339,4353,4369,4693,4757,4775,4779,4871,5059,5066,5081,5169,5316,6163],[864,42,5136,4121,1658,227,5042,4603,4961,5435,5108,306,328,402,5650,944,981,358,1238,4715,5,32,166,886,1024,1371,1393,4341,80,178,184,885,945,955,1657,4122,4224,4331,4339,4995,5000,5316],[1040,306,946,1696,769,496,886,304,1658,0,1556,4754,389,4121,4419,4755,32,224,228,875,4331,4598,5435],[1354,594,4907,241,166,5097,5042,4341,5049,4339,250,708,835,2087,742,801,4360,5073,233,266,949,1257,1680,4278,4373,4720,4721,4809,4922,5066,6017,153,227,256,261,329,518,533,1080,1240,1922,1937,1939,1940,2005,4298,4331,4346,4353,4369,4603,4693,4817,4821,6163],[946,1047,1681,1346,968,1354,6025,5097,5010,5073,1367,6177,281,841,1680,291,631,1003,4610,6186,628,646,650,708,741,962,1080,1910,2000,2096,2100,4704,4745,4821,4913,5066,6035,6185],[899,5136,4121,1658,953,4603,306,736,1024,4341,5097,978,1339,1379,4339,5650,5652,32,2087,178,328,594,801,1393,5,80,166,358,835,945,4122,4331,4995],[1049,5771,946,1346,1562,899,999,968,4500,347,167,631,841,291,368,1555,1633,197,898,962,1339,2000,4987,5904,6177],[1040,5771,946,1346,1562,899,980,4500,347,968,167,789,5172,841,994,1556,291,368,1633,197,898,962,1033,1339,2000,4987,5113,5904,6177],[1040,1670,769,352,946,1700,1339,496,304,323,1269,81,0,184],[1040,1670,946,352,772,1700,385,304,802,1339,1928,0,184,4995]]

def wr21 : List (List ℕ) := [[864,5,5136,227,5766,5042,4961,36,306,1024,209,4963,402,5650,944,32,5045,5170,5435,64,166,4122,4341,4490,5432,5466,8,27,178,882,885,945,955,4121,4259,4339,4459,5316],[899,5136,261,5771,963,306,5074,736,999,4339,4500,5650,328,4922,5,801,5889,32,166,178,1024,1379,4122,4459,5466,59,594,835,4121,4341,5435],[1040,1670,946,352,772,436,802,1339,304,72,4898,389,1556,608,4327,4726,5203],[1040,1670,946,352,772,436,1339,304,802,72,389,4327,0,184,5435],[1040,1670,769,352,946,1700,385,772,224,304,1556,1339,4327,81],[1040,1670,352,769,946,436,4898,1339,772,1928,304,72,389,224,1556,81,608,807,4327,4726,5435],[946,1658,1040,37,306,166,5108,6020,886,38,343,4715,1556,4714,4961,86,1090,5459,402,4121,5,80,328,602,897,945,1362,4122,4467],[1049,5771,946,1347,899,5889,999,4500,347,167,968,1027,841,5904,6026,291,368,1633,6177,631,898,962,982,1346,1412,6185],[1040,5771,946,1346,899,1562,980,4500,5172,347,968,789,841,994,1556,6177,291,368,1339,1633,5113,167,197,898,962,1033,1412,4824,6182,6185],[1040,1658,946,37,306,4282,1090,4995,38,1556,343,5108,4961,86,166,356,6020,358,402,4467,4714,4715,5432,5,80,328,602,897,945,4121,4122,4331],[1049,5771,946,1347,899,4280,999,4500,347,167,968,1027,841,5889,291,368,1633,631,898,962,982,1346,1412,4987,5904,6177],[1040,5771,946,1346,899,1562,999,4500,1825,5172,789,347,945,841,291,368,1339,1555,6177,116,167,197,728,898,962,1033,1412,4987,5904,6182],[1040,1670,769,352,946,1703,899,304,306,0,37,184,875],[1040,306,946,5755,769,1703,1928,304,166,0,864,4707,340,875],[1049,306,769,5755,946,1703,304,166,0,864,340,519,1027],[1040,1670,769,352,946,1703,306,304,1928,0,899,184,875],[1040,306,946,1658,724,1562,5097,166,5771,4500,38,4714,968,835,899,2087,291,347,4339,5,328,594,1346,4121],[1040,306,946,5771,724,1562,999,899,4500,38,968,1658,166,835,2087,4714,291,347,4339,5,328,358,594,1346,4121],[1040,1658,946,37,306,4282,1090,886,38,1379,1556,5108,4961,86,166,6020,343,356,358,4714,4715,5466,5,51,80,328,602,897,945,4121,4122,4459,4467],[1040,728,1825,945,1347,1562,899,4500,946,999,5172,1556,347,167,841,1339,291,368,789,58,116,197,898,962,1033,1335,1412,4987,5904,5972,6177],[1040,1658,37,946,306,4282,1090,886,38,1556,343,5108,4961,86,166,356,358,6020,402,4467,4714,4715,5974,5,80,328,602,897,945,1362,4121,4122,4459],[1049,5771,946,1347,4280,899,999,347,4500,167,968,1027,841,1339,5889,291,368,1633,631,898,962,982,1335,1412,4987,5904,5972,6177],[1049,1670,946,352,769,899,1700,37,4550,304,306,599,144,1928,184,353,450,1027,1765,4516],[1040,306,946,5771,724,1562,999,4500,38,1339,968,1658,166,835,2087,4714,291,347,4339,5972,5,328,358,594,4121],[1049,5771,946,1339,899,1562,4500,6177,347,968,999,1335,167,841,291,368,982,1027,1633,197,631,898,962,1412,2000,4987,5904,5972,6026],[1040,306,946,5771,724,1562,999,4500,38,899,968,166,835,1339,2087,4714,291,347,4339,5,197,328,358,594,4121,4459],[1040,5771,946,1347,1562,899,999,4500,347,167,968,5172,841,1339,291,368,789,1555,1633,197,898,962,1033,1335,1412,2000,4987,5904,5972,6177],[1040,1670,769,352,946,1703,304,306,5172,899,224,802,5755,0,166,519,681,1033,4098,5435],[1040,1670,769,352,946,1700,1339,304,224,72,1269,5755,81,144,496,1928,2009,4327,5064],[1040,1670,769,352,946,1703,5755,304,1664,1593,0,802,807,5064,166,728,1033,6147],[1040,1670,946,352,769,1703,306,304,592,1556,1928,1269,4707,81,166,599,608,976,4516,4726,4898],[1040,1670,769,352,946,1703,1928,306,304,0,166,592,1556,81,4707,35,599,608,4516,4726]]

def wr22 : List (List ℕ) := [[1049,1670,769,352,946,1703,1339,304,1928,0,72,599,724,81,5755,4516],[1040,1670,769,352,946,1703,1339,304,72,772,166,592,1152,5755,0,608,4327,4516,4726,4898],[946,4932,5456,4983,5688,5682,789,1562,5459,5747,6177,1638,4985,5009,1013,906,944,1338,4913,5478,965,5480,5490,5750,945,962,976,1015,2069,5018,5169,5685,5706,5769,6182,6185],[946,4932,5769,5456,4983,5459,6177,5682,4913,5747,1638,4985,1562,789,1013,5009,906,944,1338,5478,965,5480,5490,5688,5750,945,962,976,1015,2069,5018,5169,5685,6182,6185],[1040,306,946,5771,1562,899,999,4500,1681,945,1027,1346,841,166,209,291,328,631,6177,1,116,167,962,1339,5904,6182],[946,1047,1354,1681,1346,968,6025,5097,5010,5073,1367,6035,281,841,962,1680,291,631,4610,6186,628,646,650,708,741,1003,1080,1910,2000,2096,2100,4704,4745,4821,5066,6177,6185],[946,1047,1681,1346,1354,968,6025,5097,5010,5073,1367,6177,281,841,1680,291,631,1003,4610,6186,628,646,650,708,741,962,1080,1910,2000,2096,2100,4704,4745,4821,4913,5066,6035,6185],[1040,5771,946,1346,1562,899,968,980,4500,1633,167,789,5172,841,994,1556,291,368,1,642,898,962,1033,1339,2000,4821,4987,5113,5904,6177],[1049,1670,946,352,769,1703,1339,304,807,1027,72,802,0,81,184,899],[946,1090,5766,1027,1335,872,999,4963,1562,4500,167,5172,355,1633,4968,5432,944,368,789,5435,5466,5745,864,898,945,962,1506,4987,5542,5972,6177],[1040,5771,946,1347,1562,899,999,4500,1633,167,968,5172,841,291,355,368,789,1555,5745,642,898,962,1033,1335,4987,5972,6177],[1040,306,946,5771,1562,999,899,4500,167,968,1027,1339,841,166,209,291,328,642,1,631,962,5745,5904,5972,6177],[1049,5771,946,1347,1562,899,999,1339,4500,1633,945,1027,841,291,368,631,642,1555,5745,6177,1,116,167,898,962,1335,4987,5904,5972,6182],[946,1090,5766,1027,1335,4963,999,872,4500,1574,167,5172,355,1633,4968,5016,944,5435,368,789,1397,5541,5745,864,898,945,962,1506,4987,5972,6177],[1040,1670,769,352,946,1700,327,304,1556,5172,802,0,427,1033],[1040,306,946,5771,1562,999,1339,968,4500,5074,899,167,841,1681,166,209,291,328,1,355,631,962,2000,5745,5972,6177],[1040,306,946,5771,1562,999,1339,4500,968,167,841,899,166,209,291,328,631,4423,1,642,962,2000,5745,5904,5972,6177],[1040,5771,946,306,1574,968,1056,899,209,4500,1339,167,999,1027,5136,291,328,5541,1,166,631,931,962,2000,5016,5745,5904,5972,6177],[1049,5771,946,1346,899,1056,1574,968,1339,999,4500,167,1633,1027,291,368,1555,5541,5745,1,631,898,931,962,1098,1335,2000,4987,5016,5194,5904,5972,6177],[1040,5771,946,1346,1574,899,999,4500,1339,968,5827,167,1633,291,368,789,1555,5745,1,898,931,962,1033,1207,1335,2000,4987,5016,5194,5541,5904,5972,6177],[1049,1670,769,352,946,419,968,327,1056,304,5016,592,1269,1027,1186,1928,144,599,802,1057,1209,4546],[1040,1670,769,352,946,1703,1339,304,72,772,81,184,224,899,4327],[1040,1670,352,769,946,1703,385,304,4898,772,1339,807,1152,1915,184,452,4327,5329],[1040,306,946,1670,1269,1703,5365,1556,352,772,968,976,1537,4898,25,224,304,544,681,1379,1584,1593,2009,4098],[1040,1670,352,946,772,1700,968,1339,304,4898,327,1556,0,1042,427,965,979,980,1410,1618,4273,4327,4726,5220,5252],[1040,1670,769,352,946,1703,1339,304,72,802,1042,0,184,224,899,1715,4276,5435],[1040,1670,769,352,946,1703,306,304,420,1339,5128,802,1041,1269,184,224,599,1017,1060],[1040,5771,946,1346,899,1562,980,4500,5172,1633,968,789,841,994,1556,6177,291,368,1339,5113,1,167,898,962,1033,1412,4821,5541,5904,6182,6185],[1040,5771,946,1347,1562,899,999,4500,5172,167,1633,968,1593,841,1339,291,368,789,1556,5745,1,898,962,1033,1335,1412,1584,2000,4987,5541,5904,5972,6177],[1040,1670,769,352,946,1703,306,304,1556,592,1152,0],[1049,1670,946,352,769,1703,1339,304,1027,72,0,802,4327,184,251,899],[1040,1670,946,352,772,419,385,304,0,802,1339,4405,1556,420,1033,4273,5220]]

def wr23 : List (List ℕ) := [[1040,1670,769,352,946,1703,385,304,772,1556,592,802,1042,1269,1915],[1040,1670,769,352,946,1700,1339,304,72,144,4327,184,251,427,899,1033],[1040,1670,769,352,946,1700,1339,304,772,72,1152,1556,144,224,427,899,1618,4327,4726,4898],[1040,1670,769,352,946,1700,306,304,1269,1339,81,807,144,184,427,1033,1928,4327,4898],[1040,1670,769,352,946,1703,306,0,304,1928,1269,81,899,599,4550,184,875,1120],[1040,886,979,325,1701,953,805,785,5123,400,4473,2081,4465,308,887,1082,2101,5514,808,982,1050,1083,1434,1584,787,821,865,1033,1353,1634],[1040,352,1670,946,772,1700,1339,48,304,802,72,1033,184,4995],[1040,1670,352,946,48,5814,804,385,42,1928,304,968,1556,49,677,840,1339,4995],[1040,5755,769,1354,5064,304,1700,899,48,4419,4468,953,4409,887,1928,81,166,400,323,498,792,840],[1040,5755,352,769,946,5814,48,864,4422,327,304,1033,1928,0,146,968,1585,4448],[1040,886,979,325,953,1701,805,785,400,5123,308,4473,2081,4465,887,1050,1082,5514,808,1065,1083,1434,1618,4905,821,865,982,1033,1353,1584,1634,1705,5152,5203,5451,5817],[1040,352,1670,769,946,1339,4405,979,304,424,323,1033,772,184,1585,5435],[1040,1670,769,352,946,1700,385,304,979,1339,0,224,389,802,99,184,656,976,1585,1928,2009,5064,5435],[1040,306,946,5755,804,1703,352,48,1339,304,166,920,4422,82],[1040,1670,769,352,946,1703,306,48,304,1339,1033,184,420,450,1096,4422,4516,4545],[1040,1670,769,352,946,1703,327,304,899,464,961,184,353,420,450,4422],[1040,306,769,5755,946,1703,304,0,48,166,352,1928,81,864,1269,519,968],[1040,306,769,5755,946,1703,352,304,899,979,1928,0,81,166,5152,420,450,608,772,1033,4422,4516,4545],[1040,352,5755,946,772,1703,1339,48,82,304,166,385,1096,802,920,1033,6147],[1040,1670,769,352,946,1703,306,304,979,5152,772,899,166,1033,5816,184,420,450,608,1096,4516,4545],[1040,1670,769,352,946,1703,899,304,306,48,353,53,184,420,450,4516,4545],[1040,1670,769,352,946,1703,899,304,48,306,592,1033,81,184,347,450,1096,4516,4545],[1040,1670,769,352,946,1703,306,304,48,166,1556,81,592,4409,0,608,1033,4516],[1040,886,979,325,953,1701,805,785,5123,400,4473,887,4465,308,1050,1082,2101,5514,982,1083,1353,1434,1584,2081,5817,787,808,821,865,1033,1555,1634],[1040,306,946,1670,772,1703,979,352,1339,304,100,1593,48,1556,805,1033,1584,4995],[1040,306,769,5755,946,1703,352,48,1556,304,528,1593,1584,4422],[1040,1670,769,352,946,1703,1339,304,979,1681,72,772,373,1050,5435],[1040,325,979,1701,953,886,805,785,5123,308,400,4473,887,4465,1050,1082,5514,1065,1083,1434,1618,2081,4905,5817,360,808,821,865,982,1033,1353,1555,1584,1634,1705,5152,5203,5451],[1040,1670,769,352,946,1339,427,304,979,72,389,772,1681,5435,899,1033,1050,1618],[1040,1670,769,352,946,419,1339,195,304,5755,4276,5511,72,81,2000,5329,5527,112,311,899,1033,1715,4289,4448,4699,5435],[1049,1670,769,352,946,1703,1339,304,48,72,968,979,99,184,224,899],[1040,1670,352,946,772,427,979,385,968,304,1339,48,840,224,1556,4468,802,1410,4257,5064]]

def wr24 : List (List ℕ) := [[1040,1670,769,352,946,1700,1339,304,979,72,0,427,802,99,184,224,899,1033,4602,4898],[1049,1670,769,352,946,1703,385,48,304,1556,968,1027,224,519],[1040,1670,352,946,772,1700,1339,48,72,100,304,1681,4422,5172,144,311,427,864,919,1033,1618,5301,5445],[1040,306,946,1670,1269,1703,804,352,5365,1339,304,2075,184,791,1120,4422,183,1584,1593,2009],[1040,1670,769,352,946,1700,899,48,306,304,1152,1681,4448,0,144,224,427,1339,1618,1683,4422,4657,5904],[1040,1670,352,946,772,1700,979,1339,304,802,48,72,4468,4898,1152,1556,0,144,224,427,899,968,4257,4602,5064],[1040,1670,769,352,946,1703,1339,304,979,72,772,184,1033,1715,4276,4602,5435],[1040,1670,769,352,946,1703,306,304,48,899,968,979,0,81,184,224,1033,4257,4289,4699,5064],[42,1354,48,5042,4868,1657,4242,224,809,4983,5075,166,774,4114,250,262,818,517,4122,5009,246,256,519,657,949,4136,4259,4696,4721,5045,5769,5783,5,32,230,233,512,788,791,1240,1906,2002,2064,4353,4369,5066,6107,6218],[1670,769,304,4468,323,953,1027,0,305,1700,5075,4404,864,1928,774,4458,5042,6104,176,454,632,840],[1354,42,769,4242,5042,48,4983,1657,230,257,809,4114,4868,166,262,818,820,976,183,4259,5009,5075,5784,33,246,497,739,961,4136,4696,5397,5769,5,27,233,519,657,774,788,869,998,1906,2064,5045,5066,5783,6107,6218],[1670,769,0,352,4961,953,1696,385,5064,2075,304,1269,809,818,1339,178,224,632,1152,4192,4458,7,681,981,4213],[1040,1670,769,306,953,4468,304,0,864,1700,385,1027,6104,1928,5161,32,820,886,961,5075,176,184,4458],[1040,1670,769,352,946,5814,327,304,0,1047,4709,677,802,840,454,875,1721,4458],[5041,1354,769,166,594,809,2080,241,230,251,745,2075,5049,517,250,262,742,5073,233,246,791,1257,4721,5066,6017,256,497,512,523,528,615,708,709,779,784,788,827,835,949,1240,1906,1922,1937,1939,2002,2064,4298,4353,4369,4817,5042],[1040,1670,946,352,772,1700,968,864,323,4448,1928,4901,1017,4422,0,1033,5755,224,808,4657,4660],[946,352,1700,1670,5075,772,224,385,4901,0,1027,1339,304,968,4496,197,516,4448,864],[1040,1670,946,352,772,1700,1339,1355,224,304,385,802,0,311,369,184,978,5435],[1040,1670,946,352,772,1700,968,385,0,1047,304,1027,1269,864,516,184],[1040,352,946,5755,772,0,419,1664,1047,166,304,840,1928,802,875,4276],[1040,352,946,1670,772,419,0,1047,1658,899,304,840,306,802,1928,875,4276],[1040,1670,769,352,946,1703,385,304,0,899,656,772,184,875,1269],[1040,1670,946,352,0,772,1703,306,304,968,1556,166,1047,1928,516,875,4276],[1040,1670,769,352,946,1703,306,304,0,166,1556,1928,81,144,519,875,976,4276,4699,4722],[1370,769,1683,5120,352,424,953,0,385,304,32,496,2075,166,809,4405,4714,81,178,1339,519,791,1653,4448,4820],[1049,1670,769,352,946,1703,306,304,1928,166,1556,772,81,4699,4722],[1040,1670,769,352,946,424,327,0,4422,899,4448,5755,304,1041,1928,81,404,808,1667,1811,4443,4660],[1049,1670,946,352,772,1703,1047,968,1339,304,72,0,166,1027,5541,681,4098],[1040,352,946,1670,804,1703,0,1339,1658,304,4404,4496,4,48,72,35,86,311,516,875,1928,4276,4448],[1049,1670,946,352,804,1703,1339,0,304,72,1047,197,224,1107,5001,5088,5127,1027],[1040,352,1670,946,772,436,0,1339,304,72,4404,840,4496,4,802,1041,35,197,311,454,1928,4422],[1040,1670,769,352,946,424,0,306,304,840,899,968,1041,35,184,1928,4404,4422,4458]]

def wr25 : List (List ℕ) := [[1040,5755,946,352,772,424,802,899,724,4901,224,1339,304,4498,4405,1017,1033,1928,4448,5435],[1670,769,352,946,424,4901,802,5075,304,327,0,840,1041,1269,1339,1928,4496,5128,197,224,454,544,1017,4422],[946,1047,1682,1346,968,1562,2075,1681,1354,251,4983,337,528,242,370,835,5682,246,250,4263,5397,5,27,48,657,741,788],[946,1047,1682,1346,968,1562,2075,337,251,5009,4983,370,528,242,835,246,250,642,4121,5397,5682,5,27,657,741,788],[1040,1670,946,352,772,1703,385,968,1047,304,4709,875,1412],[946,1047,1682,968,1346,1562,769,337,2075,370,4983,5009,242,251,835,246,5397,5682,5,27,250,519,642,657,788,1354],[1049,1670,946,352,772,1703,385,968,1047,0,304,5123,5682,1269,1027],[1049,1670,946,352,772,1703,385,968,1047,144,304,1027,592,1556,420],[946,1047,1682,1346,769,6025,1354,968,1681,501,5010,242,251,745,835,2075,246,5073,6035,154,250,256,528,594,650,708,709,741,779,788,1003,4353],[728,769,1682,1346,1047,6025,946,501,745,968,1354,5010,242,251,835,2075,246,4721,154,250,256,528,594,641,650,708,709,741,779,788,1003,4353,6035],[1040,1670,769,352,946,1703,385,304,809,4709,86,772,224,1412],[728,1703,306,769,1670,1047,304,968,946,899,1027,592,5075,327,144,4550,596,677,802,1928,4456,4546,5001,5016,5127],[1040,1670,769,352,946,1703,327,304,968,4404,4550,1041,4709,592,1269,4458,464],[728,1703,352,946,772,5755,5075,1339,1027,968,5146,304,385,4496,146,224,1047],[1370,769,1670,946,352,1703,5075,1027,304,968,385,1047,772,1107,1339,197,5127,224,4456,5001,5435],[728,769,1670,352,1703,5075,946,327,1027,304,4458,802,4901,1339,0,420,454,1107,4546],[1040,1670,769,352,946,1703,327,304,968,1339,4404,4496,0,197,681,875],[728,1703,352,769,1670,946,5075,327,1027,304,802,1047,1339,1107,0,420,184,224,385,1478,1498,4456,4560,5001,5127,5435],[1040,1670,946,352,772,1703,224,1339,4901,802,385,304,724,197,570,978,5435],[1040,1670,769,352,946,1703,327,304,1339,5075,802,5128,224,420,1041,1498,4496,0,184,1017,1060,1478,4458,4560,5435],[728,1703,352,772,1670,946,5075,802,327,5146,304,1339,4496,592,968,5128,1041,4550,81,596,1017,1060,4546,4901,5016],[1040,1670,769,352,946,1703,306,968,304,1339,5075,5128,144,420,772,1041,1928,4458,4901,184,1017,1060],[1049,1670,946,352,1703,772,0,385,656,1269,5365,802,1556,4098,304,6026,570,681,1027,2075,4448],[1049,1670,769,352,946,1703,1339,304,72,772,1047,86,183,197,224,6026],[1049,306,769,1670,946,1700,304,1269,1339,496,0,1681,81,144],[1040,1670,769,352,946,1703,304,306,1339,592,1152,0,184,1067],[1049,1670,769,352,946,1703,304,327,1047,4550,968,1339,592,0,464,1027,5001,5127,5541],[1040,1670,769,352,946,1703,304,306,1339,592,1152,0,184,1067],[1049,1670,769,352,946,419,327,304,0,899,1715,4276,81,184,1027,1928,4699,5511],[1049,1670,769,352,946,1703,1339,304,0,1027,72,144,802,180,184,251,899,1928,4276,4699],[728,1700,352,769,1339,5755,946,5075,0,1027,304,968,224,1047,385,1107,772,144,183,424,4456,5001,5127,5435,6026],[1040,1670,769,352,946,1703,385,304,802,0,1556,5075,5128,1041,4458,4901,144,420,1017,1060,4550]]

def wr26 : List (List ℕ) := [[1049,1670,769,352,946,1703,1339,304,72,968,0,1047,1107,4550,5127,420,1027,5001,5541],[1049,1670,769,352,946,1703,1339,224,304,5755,0,72,81,5127,86,112,570,1047,1107],[728,1703,352,769,1670,1339,5075,946,1027,304,802,899,1047,1107,5435,0,72,224,4550,5127,81,420,4456,5001,5541],[1040,1670,769,352,946,419,327,304,0,899,1041,1715,1928,4276,81,184,1667,4699,5511]]

def wr : List (List (List ℕ)) := [wr0,wr1,wr2,wr3,wr4,wr5,wr6,wr7,wr8,wr9,wr10,wr11,wr12,wr13,wr14,wr15,wr16,wr17,wr18,wr19,wr20,wr21,wr22,wr23,wr24,wr25,wr26]

def pairWitness (i : ℕ) := groupedAt wr i []


def checkPlanes (i : ℕ) :=
  let h := hullAt i
  checkedPlane guardCols h.1.1 i && checkedPlane edgeCols h.1.2 i &&
    checkedPlane negativeCols h.2.1 i && checkedPlane positiveCols h.2.2 i

def sideCover (r : Profile) := invertIn hCount
  (unionCols guardCols (invertIn 11 r.1) ||| unionCols edgeCols (invertIn 16 r.2))

def tileMask (first : Hull) (shared : ℕ) (t : Box) :=
  if ProfileBelow first.1 t.1 then sideCover t.2.1 &&&
    (shared ||| invertIn hCount (unionCols positiveCols (missingBits first.2.2 t.2.2))) else 0

def witnessUnion (cells : List ℕ) (f : ℕ → ℕ) := cells.foldr (fun c acc => f c ||| acc) 0

def checkTiles (i : ℕ) :=
  let h := hullAt i
  let shared := unionCols negativeCols h.2.1
  below (bigOnes hCount) (witnessUnion (pairWitness i) (fun z => tileMask h shared (orientedTile z)))

lemma witnessAt {cells : List ℕ} {f : ℕ → ℕ} {i : ℕ} (h : (witnessUnion cells f).testBit i = true) :
    ∃ z ∈ cells, (f z).testBit i = true := by
  induction cells with
  | nil => simp [witnessUnion] at h
  | cons z zs ih =>
    rw [witnessUnion,List.foldr_cons,Nat.testBit_or,Bool.or_eq_true] at h
    rcases h with yes | more
    · exact ⟨z,by simp,yes⟩
    · obtain ⟨v,hv,vv⟩ := ih more
      exact ⟨v,by simp [hv],vv⟩

lemma tileSound {first : Hull} {i : ℕ} {t : Box} (hi : i < hCount) (checks : checkPlanes i = true)
    (bit : (tileMask first (unionCols negativeCols first.2.1) t).testBit i = true) :
    holdsBox first (hullAt i) t = true := by
  obtain ⟨ck,cp⟩ := (Bool.and_eq_true_iff).1 checks
  obtain ⟨ck,cn⟩ := (Bool.and_eq_true_iff).1 ck
  obtain ⟨cg,ce⟩ := (Bool.and_eq_true_iff).1 ck
  have left : ProfileBelow first.1 t.1 = true := by
    by_contra! bad
    simp [tileMask,bad] at bit
  simp only [tileMask,left,↓reduceIte,Nat.testBit_and,Nat.testBit_or,Bool.and_eq_true,Bool.or_eq_true] at bit
  obtain ⟨right,common⟩ := bit
  rw [sideCover,invertAt hi,Nat.testBit_or,Bool.not_eq_true',Bool.or_eq_false_iff] at right
  have gSmall : (hullAt i).1.1 < 2^guardCols.length := Nat.mod_lt _ (by decide)
  have eSmall : (hullAt i).1.2 < 2^edgeCols.length := Nat.mod_lt _ (by decide)
  have rightFit : ProfileBelow (hullAt i).1 t.2.1 = true :=
    (Bool.and_eq_true_iff).2 ⟨sideAllowed gSmall (planeSound cg) right.1,
      sideAllowed eSmall (planeSound ce) right.2⟩
  apply (Bool.and_eq_true_iff).2
  refine ⟨(Bool.and_eq_true_iff).2 ⟨left,rightFit⟩,?_⟩
  rcases common with on | off
  · have equal := collisionFound (planeSound cn) on
    simp [rawJoint,equal,below]
  · rw [invertAt hi,Bool.not_eq_true'] at off
    have lastSmall : (hullAt i).2.2 < 2^positiveCols.length := Nat.mod_lt _ (by decide)
    have both := missingOff lastSmall (planeSound cp) off
    unfold rawJoint
    split
    · simp [below]
    · exact both

lemma lookupInvariant {α : Type} {P : α → Prop} (xs : List α) (i : ℕ) (d : α)
    (fallback : P d) (all : ∀ x ∈ xs, P x) : P (xs.getD i d) := by
  by_cases inside : i < xs.length
  · rw [List.getD_eq_getElem _ _ inside]
    exact all _ (List.getElem_mem _)
  · simpa only [List.getD_eq_default _ _ (Nat.le_of_not_gt inside)] using fallback

set_option maxRecDepth 4096 in
lemma boxTableEq : bcs.flatten.flatten = boxes := by decide +kernel

set_option maxRecDepth 4096 in
lemma tileIn (code : ℕ) : tile code ∈ boxes := by
  have base : ((2047,46408),(2047,46408),46408) ∈ boxes :=
    List.getElem_mem (show 0 < boxes.length by decide +kernel)
  have every : ∀ batch ∈ bcs, ∀ chunk ∈ batch, ∀ t ∈ chunk, t ∈ boxes := by
    intro batch hb chunk hc t ht
    rw [← boxTableEq]
    exact List.mem_flatten.mpr ⟨chunk,List.mem_flatten.mpr ⟨batch,hb,hc⟩,ht⟩
  let batches := bcs.getD ((code % 4096)/256) []
  have hb : ∀ chunk ∈ batches, ∀ x ∈ chunk, x ∈ boxes :=
    lookupInvariant (P:=fun cuts => ∀ chunk ∈ cuts, ∀ x ∈ chunk, x ∈ boxes) bcs _ [] (by simp) every
  have hc : ∀ x ∈ batches.getD ((code/16)%16) [], x ∈ boxes :=
    lookupInvariant (P:=fun chunk => ∀ x ∈ chunk, x ∈ boxes) batches _ [] (by simp) hb
  exact lookupInvariant (P:=fun x => x ∈ boxes) _ _ _ base hc

set_option maxRecDepth 4096 in
lemma hullsCovered (planesOK : window 0 hCount checkPlanes = true) (tilesOK : window 0 hCount checkTiles = true)
    {i j : ℕ} (hi : i < hCount) (hj : j < hCount) :
    ∃ t ∈ boxes, holdsBox (hullAt i) (hullAt j) t = true ∨ holdsBox (hullAt j) (hullAt i) t = true := by
  let h := hullAt i
  let cell (z : ℕ) := tileMask h (unionCols negativeCols h.2.1) (orientedTile z)
  have rowOk : below (bigOnes hCount) (witnessUnion (pairWitness i) cell) = true := windowIndex (test:=checkTiles) tilesOK hi
  have yes := belowBit rowOk (onesOn hj)
  obtain ⟨z,_,on⟩ := witnessAt (cells:=pairWitness i) (f:=cell) yes
  have checked := tileSound hj (windowIndex planesOK hj) on
  refine ⟨tile z,tileIn _,?_⟩
  by_cases forward : z < 4096
  · exact Or.inl (by simpa only [orientedTile,ite_eq_left forward] using checked)
  · exact Or.inr (flipped (by simpa only [orientedTile,ite_eq_right forward] using checked))


lemma planeWin0 : window 0 32 checkPlanes = true := by decide +kernel

lemma planeWin1 : window 32 32 checkPlanes = true := by decide +kernel

lemma planeWin2 : window 64 32 checkPlanes = true := by decide +kernel

lemma planeWin3 : window 96 32 checkPlanes = true := by decide +kernel

lemma planeWin4 : window 128 32 checkPlanes = true := by decide +kernel

lemma planeWin5 : window 160 32 checkPlanes = true := by decide +kernel

lemma planeWin6 : window 192 32 checkPlanes = true := by decide +kernel

lemma planeWin7 : window 224 32 checkPlanes = true := by decide +kernel

lemma planeWin8 : window 256 32 checkPlanes = true := by decide +kernel

lemma planeWin9 : window 288 32 checkPlanes = true := by decide +kernel

lemma planeWin10 : window 320 32 checkPlanes = true := by decide +kernel

lemma planeWin11 : window 352 32 checkPlanes = true := by decide +kernel

lemma planeWin12 : window 384 32 checkPlanes = true := by decide +kernel

lemma planeWin13 : window 416 32 checkPlanes = true := by decide +kernel

lemma planeWin14 : window 448 32 checkPlanes = true := by decide +kernel

lemma planeWin15 : window 480 32 checkPlanes = true := by decide +kernel

lemma planeWin16 : window 512 32 checkPlanes = true := by decide +kernel

lemma planeWin17 : window 544 32 checkPlanes = true := by decide +kernel

lemma planeWin18 : window 576 32 checkPlanes = true := by decide +kernel

lemma planeWin19 : window 608 32 checkPlanes = true := by decide +kernel

lemma planeWin20 : window 640 32 checkPlanes = true := by decide +kernel

lemma planeWin21 : window 672 32 checkPlanes = true := by decide +kernel

lemma planeWin22 : window 704 32 checkPlanes = true := by decide +kernel

lemma planeWin23 : window 736 32 checkPlanes = true := by decide +kernel

lemma planeWin24 : window 768 32 checkPlanes = true := by decide +kernel

lemma planeWin25 : window 800 32 checkPlanes = true := by decide +kernel

lemma planeWin26 : window 832 4 checkPlanes = true := by decide +kernel

lemma planeWinAll : window 0 836 checkPlanes = true := (joinWindow (s:=0) (n:=416) (m:=420) (joinWindow (s:=0) (n:=192) (m:=224) (joinWindow (s:=0) (n:=96) (m:=96) (joinWindow (s:=0) (n:=32) (m:=64) planeWin0 (joinWindow (s:=32) (n:=32) (m:=32) planeWin1 planeWin2)) (joinWindow (s:=96) (n:=32) (m:=64) planeWin3 (joinWindow (s:=128) (n:=32) (m:=32) planeWin4 planeWin5))) (joinWindow (s:=192) (n:=96) (m:=128) (joinWindow (s:=192) (n:=32) (m:=64) planeWin6 (joinWindow (s:=224) (n:=32) (m:=32) planeWin7 planeWin8)) (joinWindow (s:=288) (n:=64) (m:=64) (joinWindow (s:=288) (n:=32) (m:=32) planeWin9 planeWin10) (joinWindow (s:=352) (n:=32) (m:=32) planeWin11 planeWin12)))) (joinWindow (s:=416) (n:=224) (m:=196) (joinWindow (s:=416) (n:=96) (m:=128) (joinWindow (s:=416) (n:=32) (m:=64) planeWin13 (joinWindow (s:=448) (n:=32) (m:=32) planeWin14 planeWin15)) (joinWindow (s:=512) (n:=64) (m:=64) (joinWindow (s:=512) (n:=32) (m:=32) planeWin16 planeWin17) (joinWindow (s:=576) (n:=32) (m:=32) planeWin18 planeWin19))) (joinWindow (s:=640) (n:=96) (m:=100) (joinWindow (s:=640) (n:=32) (m:=64) planeWin20 (joinWindow (s:=672) (n:=32) (m:=32) planeWin21 planeWin22)) (joinWindow (s:=736) (n:=64) (m:=36) (joinWindow (s:=736) (n:=32) (m:=32) planeWin23 planeWin24) (joinWindow (s:=800) (n:=32) (m:=4) planeWin25 planeWin26)))))


lemma tileWin0 : window 0 8 checkTiles = true := by decide +kernel

lemma tileWin1 : window 8 8 checkTiles = true := by decide +kernel

lemma tileWin2 : window 16 8 checkTiles = true := by decide +kernel

lemma tileWin3 : window 24 8 checkTiles = true := by decide +kernel

lemma tileWin4 : window 32 8 checkTiles = true := by decide +kernel

lemma tileWin5 : window 40 8 checkTiles = true := by decide +kernel

lemma tileWin6 : window 48 8 checkTiles = true := by decide +kernel

lemma tileWin7 : window 56 8 checkTiles = true := by decide +kernel

lemma tileWin8 : window 64 8 checkTiles = true := by decide +kernel

lemma tileWin9 : window 72 8 checkTiles = true := by decide +kernel

lemma tileWin10 : window 80 8 checkTiles = true := by decide +kernel

lemma tileWin11 : window 88 8 checkTiles = true := by decide +kernel

lemma tileWin12 : window 96 8 checkTiles = true := by decide +kernel

lemma tileWin13 : window 104 8 checkTiles = true := by decide +kernel

lemma tileWin14 : window 112 8 checkTiles = true := by decide +kernel

lemma tileWin15 : window 120 8 checkTiles = true := by decide +kernel

lemma tileWin16 : window 128 8 checkTiles = true := by decide +kernel

lemma tileWin17 : window 136 8 checkTiles = true := by decide +kernel

lemma tileWin18 : window 144 8 checkTiles = true := by decide +kernel

lemma tileWin19 : window 152 8 checkTiles = true := by decide +kernel

lemma tileWin20 : window 160 8 checkTiles = true := by decide +kernel

lemma tileWin21 : window 168 8 checkTiles = true := by decide +kernel

lemma tileWin22 : window 176 8 checkTiles = true := by decide +kernel

lemma tileWin23 : window 184 8 checkTiles = true := by decide +kernel

lemma tileWin24 : window 192 8 checkTiles = true := by decide +kernel

lemma tileWin25 : window 200 8 checkTiles = true := by decide +kernel

lemma tileWin26 : window 208 8 checkTiles = true := by decide +kernel

lemma tileWin27 : window 216 8 checkTiles = true := by decide +kernel

lemma tileWin28 : window 224 8 checkTiles = true := by decide +kernel

lemma tileWin29 : window 232 8 checkTiles = true := by decide +kernel

lemma tileWin30 : window 240 8 checkTiles = true := by decide +kernel

lemma tileWin31 : window 248 8 checkTiles = true := by decide +kernel

lemma tileWin32 : window 256 8 checkTiles = true := by decide +kernel

lemma tileWin33 : window 264 8 checkTiles = true := by decide +kernel

lemma tileWin34 : window 272 8 checkTiles = true := by decide +kernel

lemma tileWin35 : window 280 8 checkTiles = true := by decide +kernel

lemma tileWin36 : window 288 8 checkTiles = true := by decide +kernel

lemma tileWin37 : window 296 8 checkTiles = true := by decide +kernel

lemma tileWin38 : window 304 8 checkTiles = true := by decide +kernel

lemma tileWin39 : window 312 8 checkTiles = true := by decide +kernel

lemma tileWin40 : window 320 8 checkTiles = true := by decide +kernel

lemma tileWin41 : window 328 8 checkTiles = true := by decide +kernel

lemma tileWin42 : window 336 8 checkTiles = true := by decide +kernel

lemma tileWin43 : window 344 8 checkTiles = true := by decide +kernel

lemma tileWin44 : window 352 8 checkTiles = true := by decide +kernel

lemma tileWin45 : window 360 8 checkTiles = true := by decide +kernel

lemma tileWin46 : window 368 8 checkTiles = true := by decide +kernel

lemma tileWin47 : window 376 8 checkTiles = true := by decide +kernel

lemma tileWin48 : window 384 8 checkTiles = true := by decide +kernel

lemma tileWin49 : window 392 8 checkTiles = true := by decide +kernel

lemma tileWin50 : window 400 8 checkTiles = true := by decide +kernel

lemma tileWin51 : window 408 8 checkTiles = true := by decide +kernel

lemma tileWin52 : window 416 8 checkTiles = true := by decide +kernel

lemma tileWin53 : window 424 8 checkTiles = true := by decide +kernel

lemma tileWin54 : window 432 8 checkTiles = true := by decide +kernel

lemma tileWin55 : window 440 8 checkTiles = true := by decide +kernel

lemma tileWin56 : window 448 8 checkTiles = true := by decide +kernel

lemma tileWin57 : window 456 8 checkTiles = true := by decide +kernel

lemma tileWin58 : window 464 8 checkTiles = true := by decide +kernel

lemma tileWin59 : window 472 8 checkTiles = true := by decide +kernel

lemma tileWin60 : window 480 8 checkTiles = true := by decide +kernel

lemma tileWin61 : window 488 8 checkTiles = true := by decide +kernel

lemma tileWin62 : window 496 8 checkTiles = true := by decide +kernel

lemma tileWin63 : window 504 8 checkTiles = true := by decide +kernel

lemma tileWin64 : window 512 8 checkTiles = true := by decide +kernel

lemma tileWin65 : window 520 8 checkTiles = true := by decide +kernel

lemma tileWin66 : window 528 8 checkTiles = true := by decide +kernel

lemma tileWin67 : window 536 8 checkTiles = true := by decide +kernel

lemma tileWin68 : window 544 8 checkTiles = true := by decide +kernel

lemma tileWin69 : window 552 8 checkTiles = true := by decide +kernel

lemma tileWin70 : window 560 8 checkTiles = true := by decide +kernel

lemma tileWin71 : window 568 8 checkTiles = true := by decide +kernel

lemma tileWin72 : window 576 8 checkTiles = true := by decide +kernel

lemma tileWin73 : window 584 8 checkTiles = true := by decide +kernel

lemma tileWin74 : window 592 8 checkTiles = true := by decide +kernel

lemma tileWin75 : window 600 8 checkTiles = true := by decide +kernel

lemma tileWin76 : window 608 8 checkTiles = true := by decide +kernel

lemma tileWin77 : window 616 8 checkTiles = true := by decide +kernel

lemma tileWin78 : window 624 8 checkTiles = true := by decide +kernel

lemma tileWin79 : window 632 8 checkTiles = true := by decide +kernel

lemma tileWin80 : window 640 8 checkTiles = true := by decide +kernel

lemma tileWin81 : window 648 8 checkTiles = true := by decide +kernel

lemma tileWin82 : window 656 8 checkTiles = true := by decide +kernel

lemma tileWin83 : window 664 8 checkTiles = true := by decide +kernel

lemma tileWin84 : window 672 8 checkTiles = true := by decide +kernel

lemma tileWin85 : window 680 8 checkTiles = true := by decide +kernel

lemma tileWin86 : window 688 8 checkTiles = true := by decide +kernel

lemma tileWin87 : window 696 8 checkTiles = true := by decide +kernel

lemma tileWin88 : window 704 8 checkTiles = true := by decide +kernel

lemma tileWin89 : window 712 8 checkTiles = true := by decide +kernel

lemma tileWin90 : window 720 8 checkTiles = true := by decide +kernel

lemma tileWin91 : window 728 8 checkTiles = true := by decide +kernel

lemma tileWin92 : window 736 8 checkTiles = true := by decide +kernel

lemma tileWin93 : window 744 8 checkTiles = true := by decide +kernel

lemma tileWin94 : window 752 8 checkTiles = true := by decide +kernel

lemma tileWin95 : window 760 8 checkTiles = true := by decide +kernel

lemma tileWin96 : window 768 8 checkTiles = true := by decide +kernel

lemma tileWin97 : window 776 8 checkTiles = true := by decide +kernel

lemma tileWin98 : window 784 8 checkTiles = true := by decide +kernel

lemma tileWin99 : window 792 8 checkTiles = true := by decide +kernel

lemma tileWin100 : window 800 8 checkTiles = true := by decide +kernel

lemma tileWin101 : window 808 8 checkTiles = true := by decide +kernel

lemma tileWin102 : window 816 8 checkTiles = true := by decide +kernel

lemma tileWin103 : window 824 8 checkTiles = true := by decide +kernel

lemma tileWin104 : window 832 4 checkTiles = true := by decide +kernel

lemma tileWinAll : window 0 836 checkTiles = true := (joinWindow (s:=0) (n:=416) (m:=420) (joinWindow (s:=0) (n:=208) (m:=208) (joinWindow (s:=0) (n:=104) (m:=104) (joinWindow (s:=0) (n:=48) (m:=56) (joinWindow (s:=0) (n:=24) (m:=24) (joinWindow (s:=0) (n:=8) (m:=16) tileWin0 (joinWindow (s:=8) (n:=8) (m:=8) tileWin1 tileWin2)) (joinWindow (s:=24) (n:=8) (m:=16) tileWin3 (joinWindow (s:=32) (n:=8) (m:=8) tileWin4 tileWin5))) (joinWindow (s:=48) (n:=24) (m:=32) (joinWindow (s:=48) (n:=8) (m:=16) tileWin6 (joinWindow (s:=56) (n:=8) (m:=8) tileWin7 tileWin8)) (joinWindow (s:=72) (n:=16) (m:=16) (joinWindow (s:=72) (n:=8) (m:=8) tileWin9 tileWin10) (joinWindow (s:=88) (n:=8) (m:=8) tileWin11 tileWin12)))) (joinWindow (s:=104) (n:=48) (m:=56) (joinWindow (s:=104) (n:=24) (m:=24) (joinWindow (s:=104) (n:=8) (m:=16) tileWin13 (joinWindow (s:=112) (n:=8) (m:=8) tileWin14 tileWin15)) (joinWindow (s:=128) (n:=8) (m:=16) tileWin16 (joinWindow (s:=136) (n:=8) (m:=8) tileWin17 tileWin18))) (joinWindow (s:=152) (n:=24) (m:=32) (joinWindow (s:=152) (n:=8) (m:=16) tileWin19 (joinWindow (s:=160) (n:=8) (m:=8) tileWin20 tileWin21)) (joinWindow (s:=176) (n:=16) (m:=16) (joinWindow (s:=176) (n:=8) (m:=8) tileWin22 tileWin23) (joinWindow (s:=192) (n:=8) (m:=8) tileWin24 tileWin25))))) (joinWindow (s:=208) (n:=104) (m:=104) (joinWindow (s:=208) (n:=48) (m:=56) (joinWindow (s:=208) (n:=24) (m:=24) (joinWindow (s:=208) (n:=8) (m:=16) tileWin26 (joinWindow (s:=216) (n:=8) (m:=8) tileWin27 tileWin28)) (joinWindow (s:=232) (n:=8) (m:=16) tileWin29 (joinWindow (s:=240) (n:=8) (m:=8) tileWin30 tileWin31))) (joinWindow (s:=256) (n:=24) (m:=32) (joinWindow (s:=256) (n:=8) (m:=16) tileWin32 (joinWindow (s:=264) (n:=8) (m:=8) tileWin33 tileWin34)) (joinWindow (s:=280) (n:=16) (m:=16) (joinWindow (s:=280) (n:=8) (m:=8) tileWin35 tileWin36) (joinWindow (s:=296) (n:=8) (m:=8) tileWin37 tileWin38)))) (joinWindow (s:=312) (n:=48) (m:=56) (joinWindow (s:=312) (n:=24) (m:=24) (joinWindow (s:=312) (n:=8) (m:=16) tileWin39 (joinWindow (s:=320) (n:=8) (m:=8) tileWin40 tileWin41)) (joinWindow (s:=336) (n:=8) (m:=16) tileWin42 (joinWindow (s:=344) (n:=8) (m:=8) tileWin43 tileWin44))) (joinWindow (s:=360) (n:=24) (m:=32) (joinWindow (s:=360) (n:=8) (m:=16) tileWin45 (joinWindow (s:=368) (n:=8) (m:=8) tileWin46 tileWin47)) (joinWindow (s:=384) (n:=16) (m:=16) (joinWindow (s:=384) (n:=8) (m:=8) tileWin48 tileWin49) (joinWindow (s:=400) (n:=8) (m:=8) tileWin50 tileWin51)))))) (joinWindow (s:=416) (n:=208) (m:=212) (joinWindow (s:=416) (n:=104) (m:=104) (joinWindow (s:=416) (n:=48) (m:=56) (joinWindow (s:=416) (n:=24) (m:=24) (joinWindow (s:=416) (n:=8) (m:=16) tileWin52 (joinWindow (s:=424) (n:=8) (m:=8) tileWin53 tileWin54)) (joinWindow (s:=440) (n:=8) (m:=16) tileWin55 (joinWindow (s:=448) (n:=8) (m:=8) tileWin56 tileWin57))) (joinWindow (s:=464) (n:=24) (m:=32) (joinWindow (s:=464) (n:=8) (m:=16) tileWin58 (joinWindow (s:=472) (n:=8) (m:=8) tileWin59 tileWin60)) (joinWindow (s:=488) (n:=16) (m:=16) (joinWindow (s:=488) (n:=8) (m:=8) tileWin61 tileWin62) (joinWindow (s:=504) (n:=8) (m:=8) tileWin63 tileWin64)))) (joinWindow (s:=520) (n:=48) (m:=56) (joinWindow (s:=520) (n:=24) (m:=24) (joinWindow (s:=520) (n:=8) (m:=16) tileWin65 (joinWindow (s:=528) (n:=8) (m:=8) tileWin66 tileWin67)) (joinWindow (s:=544) (n:=8) (m:=16) tileWin68 (joinWindow (s:=552) (n:=8) (m:=8) tileWin69 tileWin70))) (joinWindow (s:=568) (n:=24) (m:=32) (joinWindow (s:=568) (n:=8) (m:=16) tileWin71 (joinWindow (s:=576) (n:=8) (m:=8) tileWin72 tileWin73)) (joinWindow (s:=592) (n:=16) (m:=16) (joinWindow (s:=592) (n:=8) (m:=8) tileWin74 tileWin75) (joinWindow (s:=608) (n:=8) (m:=8) tileWin76 tileWin77))))) (joinWindow (s:=624) (n:=104) (m:=108) (joinWindow (s:=624) (n:=48) (m:=56) (joinWindow (s:=624) (n:=24) (m:=24) (joinWindow (s:=624) (n:=8) (m:=16) tileWin78 (joinWindow (s:=632) (n:=8) (m:=8) tileWin79 tileWin80)) (joinWindow (s:=648) (n:=8) (m:=16) tileWin81 (joinWindow (s:=656) (n:=8) (m:=8) tileWin82 tileWin83))) (joinWindow (s:=672) (n:=24) (m:=32) (joinWindow (s:=672) (n:=8) (m:=16) tileWin84 (joinWindow (s:=680) (n:=8) (m:=8) tileWin85 tileWin86)) (joinWindow (s:=696) (n:=16) (m:=16) (joinWindow (s:=696) (n:=8) (m:=8) tileWin87 tileWin88) (joinWindow (s:=712) (n:=8) (m:=8) tileWin89 tileWin90)))) (joinWindow (s:=728) (n:=56) (m:=52) (joinWindow (s:=728) (n:=24) (m:=32) (joinWindow (s:=728) (n:=8) (m:=16) tileWin91 (joinWindow (s:=736) (n:=8) (m:=8) tileWin92 tileWin93)) (joinWindow (s:=752) (n:=16) (m:=16) (joinWindow (s:=752) (n:=8) (m:=8) tileWin94 tileWin95) (joinWindow (s:=768) (n:=8) (m:=8) tileWin96 tileWin97))) (joinWindow (s:=784) (n:=24) (m:=28) (joinWindow (s:=784) (n:=8) (m:=16) tileWin98 (joinWindow (s:=792) (n:=8) (m:=8) tileWin99 tileWin100)) (joinWindow (s:=808) (n:=16) (m:=12) (joinWindow (s:=808) (n:=8) (m:=8) tileWin101 tileWin102) (joinWindow (s:=824) (n:=8) (m:=4) tileWin103 tileWin104)))))))


lemma finiteDone : finiteCertificate boxes := by
  intro a b c f first second
  obtain ⟨i,hi,ui⟩ := rawInHull rawWinAll first
  obtain ⟨j,hj,uj⟩ := rawInHull rawWinAll second
  obtain ⟨t,ht,case1 | case2⟩ := hullsCovered planeWinAll tileWinAll hi hj
  · exact ⟨t,ht,Or.inl (holdsUnder ui uj case1)⟩
  · exact ⟨t,ht,Or.inr (holdsUnder uj ui case2)⟩

end PEqualNP.Outside.L_meta_8159

theorem PEqualNP.Outside.L_meta_8159 : (have x1 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)]; have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)]; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) => ∀ x6 ∈ x1, (PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x4 x5 fun (x8 : Fin (11 : ℕ)) => x6.testBit ↑x8) = Bool.false; have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ); ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 : ℕ), PEqualNP.TopForm.IsAO2 (11 : ℕ) x6 → (5 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x6 → PEqualNP.ReadTwo.nAnd x6 ≤ (6 : ℕ) → x7 < x8 → x8 < x6.size → x3 x6 x7 → x3 x6 x8 → (∀ x16 < x6.size, x3 x6 x16 → (x4 x6 x16 ↔ x16 ≠ x7 ∧ x16 ≠ x8)) → (∀ x17 < x6.size, x3 x6 x17 → x4 x6 x17 → ∀ x21 < x6.size, x3 x6 x21 → ¬x5 x6 x17 x21) → ¬x5 x6 x7 x8 → ¬x5 x6 x8 x7 → (∃ x20 < x6.size, x3 x6 x20 ∧ x4 x6 x20 ∧ x5 x6 x7 x20 ∧ x5 x6 x8 x20) → (∀ x21 ∈ x2, (PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x6 fun (x23 : Fin (11 : ℕ)) => x21.testBit ↑x23) = Bool.true) → (∀ x22 ∈ x1, (PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x6 fun (x24 : Fin (11 : ℕ)) => x22.testBit ↑x24) = Bool.false) → False) := by
  exact PEqualNP.Outside.L_meta_8159.fromTables (PEqualNP.Outside.L_meta_8159.unit8159Reduced PEqualNP.Outside.L_meta_8159.finiteDone)
