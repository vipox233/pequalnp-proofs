import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1402

open PEqualNP.CircuitLowerBounds

private def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

private lemma decide_eq_not (op : GateOp) (inst : Decidable (op = GateOp.not)) :
    @decide (op = GateOp.not) inst = isNotOp op := by
  cases inst with
  | isTrue h => subst h; rfl
  | isFalse h =>
    cases op with
    | not => exact False.elim (h rfl)
    | and => rfl
    | or => rfl
    | mod _ => rfl
    | maj => rfl

private lemma decide_irrel (P : Prop) (d1 d2 : Decidable P) :
    @decide P d1 = @decide P d2 := by
  by_cases hp : P <;> simp [hp]

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private noncomputable def inp (n : Nat) (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun j : Fin n => @decide (j ∈ x) (Classical.propDecidable _)) ++ [false, true]

private noncomputable def wireVal (n : Nat) (C : Circuit) (x : Finset (Fin n)) (w : Nat) : Bool :=
  (C.wires (inp n x)).getD w false

private lemma wireVal_eq_foldl (n : Nat) (C : Circuit) (x : Finset (Fin n)) (w : Nat) :
    wireVal n C x w = (C.gates.foldl stepWire (inp n x)).getD w false := rfl

private lemma cdecide_true {P : Prop} (h : P) : @decide P (Classical.propDecidable P) = true :=
  @decide_eq_true P (Classical.propDecidable P) h

private lemma cdecide_false {P : Prop} (h : ¬P) : @decide P (Classical.propDecidable P) = false :=
  @decide_eq_false P (Classical.propDecidable P) h

private lemma of_cdecide_true {P : Prop} (h : @decide P (Classical.propDecidable P) = true) : P :=
  @of_decide_eq_true P (Classical.propDecidable P) h

private lemma getD_append_left {α : Type _} (l₁ l₂ : List α) (i : Nat) (d : α)
    (hi : i < l₁.length) : (l₁ ++ l₂).getD i d = l₁.getD i d := by
  induction l₁ generalizing i with
  | nil => cases hi
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i =>
      exact ih i (Nat.lt_of_succ_lt_succ hi)

private lemma getD_append_right_eq {α : Type _} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  induction l with
  | nil => rfl
  | cons x xs ih => exact ih

private lemma getD_eq_getElem {α : Type _} (l : List α) (k : Nat) (d : α) (hk : k < l.length) :
    l.getD k d = l[k] := by
  induction l generalizing k with
  | nil => cases hk
  | cons a l ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k (Nat.lt_of_succ_lt_succ hk)

private lemma length_inp (n : Nat) (x : Finset (Fin n)) : (inp n x).length = n + 2 := by
  simp [inp]

private lemma getD_inp_lt (n : Nat) (x : Finset (Fin n)) (w : Nat) (hw : w < n) :
    (inp n x).getD w false = @decide (⟨w, hw⟩ ∈ x) (Classical.propDecidable _) := by
  unfold inp
  have hlen : w < (List.ofFn (fun j : Fin n => @decide (j ∈ x) (Classical.propDecidable _))).length := by
    simp [hw]
  rw [getD_append_left _ _ _ _ hlen, getD_eq_getElem _ _ _ hlen]
  simp

private lemma getD_inp_n (n : Nat) (x : Finset (Fin n)) : (inp n x).getD n false = false := by
  let xs := List.ofFn (fun j : Fin n => @decide (j ∈ x) (Classical.propDecidable _))
  have h : inp n x = (xs ++ [false]) ++ [true] := by simp [inp, xs]
  have hlen : n < (xs ++ [false]).length := by simp [xs]
  have hlen2 : xs.length = n := by simp [xs]
  rw [h, getD_append_left _ _ _ _ hlen]
  have h1 := getD_append_right_eq xs false false
  rw [hlen2] at h1
  exact h1

private lemma getD_inp_n1 (n : Nat) (x : Finset (Fin n)) : (inp n x).getD (n + 1) false = true := by
  let xs := List.ofFn (fun j : Fin n => @decide (j ∈ x) (Classical.propDecidable _))
  have h : inp n x = (xs ++ [false]) ++ [true] := by simp [inp, xs]
  have hlen : (xs ++ [false]).length = n + 1 := by simp [xs]
  rw [h]
  have h1 := getD_append_right_eq (xs ++ [false]) true false
  rw [hlen] at h1
  exact h1

private lemma length_foldl_stepWire (gs : List Gate) (v : List Bool) :
    (gs.foldl stepWire v).length = v.length + gs.length := by
  induction gs generalizing v with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

private lemma getD_foldl_stepWire_of_lt (gs : List Gate) (v : List Bool) (i : Nat)
    (hi : i < v.length) : (gs.foldl stepWire v).getD i false = v.getD i false := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (stepWire v g).length := by
      simp only [stepWire, List.length_append, List.length_singleton]
      omega
    rw [ih (stepWire v g) hi']
    exact getD_append_left v _ i false hi

private lemma map_eq_of_forall {α β : Type _} (l : List α) (f g : α → β)
    (h : ∀ a ∈ l, f a = g a) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons]
    rw [h a (List.mem_cons_self), ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

private lemma getD_foldl_at (gs : List Gate) (v : List Bool) (k : Nat) (hk : k < gs.length)
    (hRB : ∀ i ∈ gs[k].inputs, i < v.length + k) :
    (gs.foldl stepWire v).getD (v.length + k) false =
      gs[k].op.eval (gs[k].inputs.map fun i => (gs.foldl stepWire v).getD i false) := by
  induction gs generalizing v k with
  | nil => cases hk
  | cons g gs ih =>
    cases k with
    | zero =>
      simp only [List.foldl_cons, Nat.add_zero, List.getElem_cons_zero]
      have hlen : v.length < (stepWire v g).length := by
        simp [stepWire]
      rw [getD_foldl_stepWire_of_lt gs (stepWire v g) v.length hlen]
      simp only [stepWire, getD_append_right_eq]
      congr 1
      apply map_eq_of_forall
      intro i hi
      have hiv : i < v.length := by
        have := hRB i hi
        omega
      have hiv' : i < (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]).length := by
        simp; omega
      rw [getD_foldl_stepWire_of_lt gs _ i hiv', getD_append_left v _ i false hiv]
    | succ k =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      have hlen : (stepWire v g).length = v.length + 1 := by
        simp [stepWire]
      have heq : v.length + (k + 1) = (stepWire v g).length + k := by omega
      rw [heq]
      apply ih (stepWire v g) k (Nat.lt_of_succ_lt_succ hk)
      intro i hi
      have := hRB i hi
      omega

private lemma wireVal_eval_at_gate (n : Nat) (C : Circuit)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    (x : Finset (Fin n)) (k : Nat) (hk : k < C.gates.length) :
    wireVal n C x (n + 2 + k) =
      C.gates[k].op.eval (C.gates[k].inputs.map fun i => wireVal n C x i) := by
  unfold wireVal Circuit.wires
  have hv : (inp n x).length = n + 2 := length_inp n x
  conv_lhs => rw [← hv]
  apply getD_foldl_at C.gates (inp n x) k hk
  intro i hi
  rw [hv]
  have h1 := hRB k hk i
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt at h1
  rw [getD_eq_getElem C.gates k _ hk] at h1
  exact h1 hi

private def isNotGateList (gs : List Gate) (k : Nat) : Bool :=
  if hk : k < gs.length then isNotOp gs[k].op else false

private def B_cntList (gs : List Gate) : Nat → Nat
  | 0 => 0
  | k + 1 => B_cntList gs k + if isNotGateList gs k then 1 else 0

private lemma B_cntList_cons (g : Gate) (gs : List Gate) (k : Nat) :
    B_cntList (g :: gs) (k + 1) = (if isNotOp g.op then 1 else 0) + B_cntList gs k := by
  induction k with
  | zero =>
    simp [B_cntList, isNotGateList]
  | succ k ih =>
    change B_cntList (g :: gs) (k + 1) + (if isNotGateList (g :: gs) (k + 1) then 1 else 0) =
      (if isNotOp g.op then 1 else 0) + (B_cntList gs k + if isNotGateList gs k then 1 else 0)
    rw [ih]
    have hnot : isNotGateList (g :: gs) (k + 1) = isNotGateList gs k := by
      unfold isNotGateList
      by_cases hk : k < gs.length
      · have hk' : k + 1 < (g :: gs).length := by simp [hk]
        simp [hk, hk']
      · have hk' : ¬(k + 1 < (g :: gs).length) := by simp [hk]
        simp [hk, hk']
    rw [hnot]
    omega

private lemma B_cntList_length (gs : List Gate) :
    B_cntList gs gs.length = (gs.filter fun g => isNotOp g.op).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.length_cons, B_cntList_cons, List.filter_cons]
    cases h : isNotOp g.op <;> simp [ih] <;> omega

private lemma notCount_eq_filter_isNotOp (C : Circuit) :
    PEqualNP.NotBracket.notCount C = (C.gates.filter fun g => isNotOp g.op).length := by
  unfold PEqualNP.NotBracket.notCount
  congr 1
  apply congrArg (fun f => C.gates.filter f)
  funext g
  exact decide_eq_not g.op _

private noncomputable def V (n : Nat) (C : Circuit) (x : Finset (Fin n)) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    if isNotGateList C.gates k then
      2 * V n C x k + if wireVal n C x (n + 2 + k) then 1 else 0
    else
      V n C x k

private lemma V_lt_pow (n : Nat) (C : Circuit) (x : Finset (Fin n)) (k : Nat) :
    V n C x k < 2 ^ B_cntList C.gates k := by
  induction k with
  | zero =>
    simp [V, B_cntList]
  | succ k ih =>
    simp only [V, B_cntList]
    cases h : isNotGateList C.gates k
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact ih
    · simp only [↓reduceIte]
      rw [Nat.pow_succ]
      cases wireVal n C x (n + 2 + k) <;> simp <;> omega

private lemma all_id_mono {α : Type _} (l : List α) (f g : α → Bool)
    (h : ∀ a ∈ l, f a = true → g a = true) :
    (l.map f).all id = true → (l.map g).all id = true := by
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons, id_eq, Bool.and_eq_true]
    intro ⟨ha, hl⟩
    exact ⟨h a (List.mem_cons_self) ha, ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) hl⟩

private lemma any_id_mono {α : Type _} (l : List α) (f g : α → Bool)
    (h : ∀ a ∈ l, f a = true → g a = true) :
    (l.map f).any id = true → (l.map g).any id = true := by
  induction l with
  | nil => intro h0; cases h0
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, id_eq, Bool.or_eq_true]
    intro h0
    rcases h0 with ha | hl
    · exact Or.inl (h a (List.mem_cons_self) ha)
    · exact Or.inr (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) hl)

private lemma V_anti_and_mono_wires (n : Nat) (C : Circuit)
    (hFan : PEqualNP.MetaComplexity.FanInTwo C)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    {u v : Finset (Fin n)} (huv : u ⊆ v) :
    ∀ k ≤ C.gates.length,
      V n C v k ≤ V n C u k ∧
      (V n C v k = V n C u k → ∀ w < n + 2 + k, wireVal n C u w = true → wireVal n C v w = true) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨Nat.le_refl _, ?_⟩
    intro _ w hw huw
    rw [wireVal_eq_foldl] at huw ⊢
    have hlen_u : w < (inp n u).length := by rw [length_inp]; exact hw
    have hlen_v : w < (inp n v).length := by rw [length_inp]; exact hw
    rw [getD_foldl_stepWire_of_lt C.gates (inp n u) w hlen_u] at huw
    rw [getD_foldl_stepWire_of_lt C.gates (inp n v) w hlen_v]
    by_cases hwn : w < n
    · rw [getD_inp_lt n u w hwn] at huw
      rw [getD_inp_lt n v w hwn]
      have hmem_u : (⟨w, hwn⟩ : Fin n) ∈ u := of_cdecide_true huw
      exact cdecide_true (huv hmem_u)
    · by_cases hweq : w = n
      · subst hweq
        rw [getD_inp_n] at huw
        cases huw
      · have hweq1 : w = n + 1 := by omega
        subst hweq1
        exact getD_inp_n1 n v
  | succ k ih =>
    intro hk1
    have hk : k < C.gates.length := Nat.lt_of_succ_le hk1
    obtain ⟨ihLe, ihMono⟩ := ih (Nat.le_of_lt hk)
    have hgate_mem : C.gates[k] ∈ C.gates := List.getElem_mem hk
    have hgate_op := (hFan C.gates[k] hgate_mem).1
    have hrb_k : ∀ i ∈ C.gates[k].inputs, i < n + 2 + k := by
      intro i hi
      have h1 := hRB k hk i
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt at h1
      rw [getD_eq_getElem C.gates k _ hk] at h1
      exact h1 hi
    have heval_u := wireVal_eval_at_gate n C hRB u k hk
    have heval_v := wireVal_eval_at_gate n C hRB v k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate_op
    rcases hgate_op with hop | hop | hop
    · have hnot : isNotGateList C.gates k = false := by
        simp [isNotGateList, hk, hop, isNotOp]
      simp only [V, hnot, Bool.false_eq_true, ↓reduceIte]
      refine ⟨ihLe, ?_⟩
      intro hveq w hw huw
      by_cases hwk : w < n + 2 + k
      · exact ihMono hveq w hwk huw
      · have hweq : w = n + 2 + k := by omega
        subst hweq
        rw [heval_u, hop, GateOp.eval] at huw
        rw [heval_v, hop, GateOp.eval]
        exact all_id_mono C.gates[k].inputs (wireVal n C u) (wireVal n C v)
          (fun i hi => ihMono hveq i (hrb_k i hi)) huw
    · have hnot : isNotGateList C.gates k = false := by
        simp [isNotGateList, hk, hop, isNotOp]
      simp only [V, hnot, Bool.false_eq_true, ↓reduceIte]
      refine ⟨ihLe, ?_⟩
      intro hveq w hw huw
      by_cases hwk : w < n + 2 + k
      · exact ihMono hveq w hwk huw
      · have hweq : w = n + 2 + k := by omega
        subst hweq
        rw [heval_u, hop, GateOp.eval] at huw
        rw [heval_v, hop, GateOp.eval]
        exact any_id_mono C.gates[k].inputs (wireVal n C u) (wireVal n C v)
          (fun i hi => ihMono hveq i (hrb_k i hi)) huw
    · have hnot : isNotGateList C.gates k = true := by
        simp [isNotGateList, hk, hop, isNotOp]
      simp only [V, hnot, ↓reduceIte]
      by_cases hlt : V n C v k < V n C u k
      · constructor
        · cases wireVal n C v (n + 2 + k) <;> cases wireVal n C u (n + 2 + k) <;>
            simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
        · intro heq
          exfalso
          cases hv : wireVal n C v (n + 2 + k) <;> cases hu : wireVal n C u (n + 2 + k) <;>
            simp only [hv, hu, Bool.false_eq_true, ↓reduceIte] at heq <;> omega
      · have hveq : V n C v k = V n C u k := by omega
        have hbit : wireVal n C v (n + 2 + k) = true → wireVal n C u (n + 2 + k) = true := by
          intro hvtrue
          rw [heval_v, hop, GateOp.eval] at hvtrue
          rw [heval_u, hop, GateOp.eval]
          cases hins : C.gates[k].inputs with
          | nil =>
            simp
          | cons i0 rest =>
            simp only [hins, List.map_cons, List.headD_cons] at hvtrue ⊢
            cases hvi0 : wireVal n C v i0
            · cases hui0 : wireVal n C u i0
              · rfl
              · have hi0 : i0 < n + 2 + k := hrb_k i0 (by simp [hins])
                have hcontr := ihMono hveq i0 hi0 hui0
                rw [hvi0] at hcontr
                cases hcontr
            · rw [hvi0] at hvtrue
              cases hvtrue
        constructor
        · cases hv1 : wireVal n C v (n + 2 + k)
          · cases hu1 : wireVal n C u (n + 2 + k) <;> simp <;> omega
          · have hu1 := hbit hv1
            rw [hu1]
            simp [hveq]
        · intro hveq1 w hw huw
          by_cases hwk : w < n + 2 + k
          · exact ihMono hveq w hwk huw
          · have hweq : w = n + 2 + k := by omega
            subst hweq
            rw [huw] at hveq1
            cases hv1 : wireVal n C v (n + 2 + k)
            · rw [hv1] at hveq1
              simp at hveq1
              omega
            · rfl

def Fit (h r b c z : Nat)
    (ok : Fin (h+1) → Finset (Fin r) → Prop) : Prop :=
  ∃ (C D : PEqualNP.CircuitLowerBounds.Circuit) (wire : Fin r → Nat) (out : Fin (h+1) → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (h+2) C ∧
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r+2) D ∧
    C.output < h+2+C.size ∧ D.output < r+2+D.size ∧
    (∀ j, wire j < h+2+C.size) ∧ (∀ j, out j < r+2+D.size) ∧
    PEqualNP.NotBracket.notCount C ≤ b ∧ PEqualNP.NotBracket.notCount D ≤ c ∧
    (C.size - PEqualNP.NotBracket.notCount C) + (D.size - PEqualNP.NotBracket.notCount D) ≤ z ∧
    ∀ (A : Finset (Fin h)) (i : Fin (h+1)), A.sup (fun j => j.val+1) = i.val →
      let v := C.wires (List.ofFn (fun j : Fin h => decide (j ∈ A)) ++ [false,true])
      let msg := Finset.univ.filter (fun j : Fin r => v.getD (wire j) false = true)
      let w := D.wires (List.ofFn (fun j : Fin r => decide (j ∈ msg)) ++ [false,true])
      ok i msg ∧ ∀ j, w.getD (out j) false = decide (i = j)

def initialSegment {h : Nat} (i : Fin (h+1)) : Finset (Fin h) :=
  Finset.univ.filter (fun j => j.val < i.val)

lemma initialSegmentRank {h : Nat} (i : Fin (h+1)) :
    (initialSegment i).sup (fun j => j.val+1) = i.val := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    omega
  · cases hi : i.val with
    | zero => exact Nat.zero_le _
    | succ k =>
      let j : Fin h := ⟨k, by have := i.isLt; omega⟩
      have hmem : j ∈ initialSegment i := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [j, hi]⟩
      exact Finset.le_sup (f := fun j : Fin h => j.val+1) hmem

private lemma inpOrdinary (n : Nat) (x : Finset (Fin n)) :
    inp n x = List.ofFn (fun j : Fin n => decide (j ∈ x)) ++ [false,true] := by
  unfold inp
  congr 1
  apply congrArg List.ofFn
  funext j
  exact decide_irrel _ _ _

private noncomputable def phase (n : Nat) (C : Circuit) (b : Nat)
    (bound : PEqualNP.NotBracket.notCount C ≤ b) (A : Finset (Fin n)) : Fin (2^b) :=
  ⟨V n C A C.gates.length, by
    apply lt_of_lt_of_le (V_lt_pow n C A C.gates.length)
    apply Nat.pow_le_pow_right (by decide)
    rwa [B_cntList_length, ← notCount_eq_filter_isNotOp]⟩

lemma sampleColors {h r b c z : Nat} (allowed : Finset (Finset (Fin r)))
    (physical : Fit h r b c z (fun _ w => w ∈ allowed)) :
    ∃ (W : Fin (h+1) → Finset (Fin r))
      (e : Fin (h+1) → Fin (2^b)) (d : Fin (h+1) → Fin (2^c)),
      (∀ i, W i ∈ allowed) ∧ Function.Injective W ∧
      (∀ i j, i ≤ j → e i = e j → W i ⊆ W j) ∧
      (∀ i j, W i ⊆ W j → d i = d j → i = j) := by
  rcases physical with ⟨C,D,wire,out,hc,hcr,hd,hdr,_,_,hwire,hout,hb,hc',_,eval⟩
  let W : Fin (h+1) → Finset (Fin r) := fun i =>
    Finset.univ.filter (fun j => wireVal h C (initialSegment i) (wire j) = true)
  let e := fun i => phase h C b hb (initialSegment i)
  let d := fun i => phase r D c hc' (W i)
  have wf (i : Fin (h+1)) :
      W i ∈ allowed ∧ (∀ j, wireVal r D (W i) (out j) = decide (i=j)) := by
    have H := eval (initialSegment i) i (initialSegmentRank i)
    simpa only [W, wireVal, inpOrdinary] using H
  have monoD (i j : Fin (h+1)) (sub : W i ⊆ W j) (eq : d i = d j) : i = j := by
    have phaseEq : V r D (W j) D.gates.length = V r D (W i) D.gates.length :=
      congrArg Fin.val eq.symm
    have hh := (V_anti_and_mono_wires r D hd hdr sub D.gates.length (le_refl _)).2
      phaseEq (out i) (hout i)
    have hi : wireVal r D (W i) (out i) = true := by simp [(wf i).2]
    have hj := hh hi
    rw [(wf j).2] at hj
    exact (of_decide_eq_true hj).symm
  refine ⟨W,e,d,fun i => (wf i).1,?_,?_,monoD⟩
  · intro i j eq
    exact monoD _ _ eq.subset (congrArg (phase r D c hc') eq)
  · intro i j hij eq k hk
    have sub : initialSegment i ⊆ initialSegment j := by
      intro t ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le (Finset.mem_filter.mp ht).2 hij⟩
    have phaseEq : V h C (initialSegment j) C.gates.length = V h C (initialSegment i) C.gates.length :=
      congrArg Fin.val eq.symm
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (V_anti_and_mono_wires h C hc hcr sub C.gates.length (le_refl _)).2
      phaseEq (wire k) (hwire k) (Finset.mem_filter.mp hk).2⟩

end PEqualNP.Outside.L_lib_1402

namespace PEqualNP.Outside.L_lib_1402
namespace StageNet
section WireFacts
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
variable {n m : ℕ}
abbrev Col (m : ℕ) := Fin m → Bool
noncomputable def raw (x : Fin m → Finset (Fin n)) (i : Fin m) :=
  List.ofFn (fun a : Fin n => decide (a ∈ x i)) ++ [false,true]
noncomputable def val (x : Fin m → Finset (Fin n)) (gs : List Gate) (p : ℕ) : Col m :=
  fun i => ((Circuit.mk gs 0).wires (raw x i)).getD p false
noncomputable def ix (gs : List Gate) := (List.range gs.length).filter fun j =>
  decide ((gs.getD j ⟨.or,[]⟩).op = GateOp.not)
noncomputable def trace (x : Fin m → Finset (Fin n)) (gs : List Gate) :=
  (ix gs).map fun j => val x gs (n+2+j)
noncomputable def sing (x : Fin m → Finset (Fin n)) (a : Fin n) : Col m := fun i => decide (a∈x i)
noncomputable def base (x : Fin m → Finset (Fin n)) : Set (Col m) :=
  {f | f=(fun _ => false) ∨ f=(fun _ => true) ∨ ∃ a, f=sing x a}
noncomputable def inv (f : Col m) : Col m := fun i => !(f i)
noncomputable def conj (f g : Col m) : Col m := fun i => f i && g i
noncomputable def disj (f g : Col m) : Col m := fun i => f i || g i

theorem wirelen (gs : List Gate) (u : List Bool) : ((Circuit.mk gs 0).wires u).length=u.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih => simpa [Circuit.wires,List.foldl_append,Nat.add_assoc] using congrArg Nat.succ ih

theorem old (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) {p} (hp : p<n+2+gs.length) :
    val x (gs++[g]) p=val x gs p := by
  funext i
  have len := wirelen gs (raw x i)
  rw [show (raw x i).length=n+2 by simp [raw]] at len
  simp only [val,Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil]
  change (((Circuit.mk gs 0).wires (raw x i)) ++ [_]).getD p false = _
  exact List.getD_append _ _ _ _ (by omega)

theorem fresh (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) (i : Fin m) :
    val x (gs++[g]) (n+2+gs.length) i=g.op.eval (g.inputs.map fun p => val x gs p i) := by
  have len := wirelen gs (raw x i)
  rw [show (raw x i).length=n+2 by simp [raw]] at len
  simp only [val,Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil]
  change ( ((Circuit.mk gs 0).wires (raw x i)) ++ [_]).getD _ false = _
  rw [←len,List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem ixAdd (gs : List Gate) (g : Gate) :
    ix (gs++[g])=ix gs ++ (if g.op=.not then [gs.length] else []) := by
  unfold ix
  simp only [List.length_append,List.length_singleton,List.range_succ,List.filter_append]
  congr 1
  · apply List.filter_congr
    intro i hi
    rw [List.getD_append _ _ _ _ (List.mem_range.mp hi)]
  · by_cases h : g.op=.not <;> simp [h]

theorem ixRange {gs : List Gate} {j} (h : j∈ix gs) : j<gs.length :=
  List.mem_range.mp (List.mem_filter.mp h).1

theorem traceAdd (x : Fin m → Finset (Fin n)) (gs : List Gate) (g : Gate) :
    trace x (gs++[g])=trace x gs ++ (if g.op=.not then [val x (gs++[g]) (n+2+gs.length)] else []) := by
  unfold trace
  rw [ixAdd,List.map_append]
  congr 1
  · apply List.map_congr_left
    intro j hj
    exact old _ _ _ (by have := ixRange hj; omega)
  · split <;> rfl

theorem countIx (gs : List Gate) : PEqualNP.NotBracket.notCount ⟨gs,0⟩=(ix gs).length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [ixAdd]
    unfold PEqualNP.NotBracket.notCount at *
    by_cases h : g.op=.not <;> simp [List.filter_append,h,ih]

theorem extendBack (gs : List Gate) (g : Gate) (h : ReadsBack (n+2) ⟨gs,0⟩)
    (ok : ∀ p∈g.inputs,p<n+2+gs.length) : ReadsBack (n+2) ⟨gs++[g],0⟩ := by
  intro j hj p hp
  simp only [List.length_append,List.length_singleton] at hj
  by_cases hj' : j<gs.length
  · apply h j hj' p
    simpa only [gateAt,List.getD_append _ _ _ _ hj'] using hp
  · obtain rfl : j=gs.length := by omega
    apply ok
    simpa [gateAt,List.getD_append_right _ _ _ _ (le_refl _)] using hp

noncomputable def Built (x : Fin m → Finset (Fin n)) (tr : List (Col m)) (k : ℕ) (S : Set (Col m)) :=
  ∃ gs : List Gate, FanInTwo ⟨gs,0⟩ ∧ ReadsBack (n+2) ⟨gs,0⟩ ∧ gs.length≤k ∧ trace x gs=tr ∧
    ∀ f∈S, ∃ p<n+2+gs.length, val x gs p=f
end WireFacts

section Compiler
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
variable {n m : ℕ} {x : Fin m → Finset (Fin n)} {tr : List (Col m)} {k : ℕ} {S : Set (Col m)}

theorem Built.start : Built x [] 0 (base x) := by
  refine ⟨[],by simp [FanInTwo],by simp [ReadsBack],by simp,rfl,?_⟩
  intro f hf
  rcases hf with rfl|rfl|⟨a,rfl⟩
  · refine ⟨n,by simp,?_⟩
    funext i
    simp [val,Circuit.wires,raw]
  · refine ⟨n+1,by simp,?_⟩
    funext i
    simp [val,Circuit.wires,raw]
  · refine ⟨a.val,by have := a.isLt; simp; omega,?_⟩
    funext i
    change ((List.ofFn fun u : Fin n => decide (u∈x i)) ++ _).getD a.val false=_
    rw [List.getD_append _ _ _ _ (by simp)]
    simp [sing]

theorem Built.relax {K : ℕ} {T : Set (Col m)} (ih : Built x tr k S) (sz : k≤K) (sub : T⊆S) : Built x tr K T := by
  obtain ⟨gs,fan,back,le,trace,signal⟩ := ih
  exact ⟨gs,fan,back,le.trans sz,trace,fun f hf => signal f (sub hf)⟩

theorem Built.andGate {f z : Col m} (ih : Built x tr k S) (hf : f∈S) (hg : z∈S) : Built x tr (k+1) (insert (conj f z) S) := by
  obtain ⟨gs,fan,back,sz,ht,sig⟩ := ih
  obtain ⟨a,ha,ea⟩ := sig _ hf
  obtain ⟨b,hb,eb⟩ := sig _ hg
  let g : Gate := ⟨.and,[a,b]⟩
  refine ⟨gs++[g],?_,?_,by simpa using sz,?_,?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with oj|nj
    · exact fan j oj
    · obtain rfl : j=g := List.mem_singleton.mp nj
      simp [g]
  · apply extendBack _ _ back
    simp_all [g]
  · rw [traceAdd]; simpa [g] using ht
  · intro f mem
    rcases mem with rfl|mem
    · refine ⟨n+2+gs.length,by simp,?_⟩
      funext i; rw [fresh]; simp [g,GateOp.eval,ea,eb,conj]
    · obtain ⟨p,hp,eq⟩ := sig _ mem
      exact ⟨p,by simp; omega,(old _ _ _ hp).trans eq⟩

theorem Built.orGate {f z : Col m} (ih : Built x tr k S) (hf : f∈S) (hg : z∈S) : Built x tr (k+1) (insert (disj f z) S) := by
  obtain ⟨gs,fan,back,sz,ht,sig⟩ := ih
  obtain ⟨a,ha,ea⟩ := sig _ hf
  obtain ⟨b,hb,eb⟩ := sig _ hg
  let g : Gate := ⟨.or,[a,b]⟩
  refine ⟨gs++[g],?_,?_,by simpa using sz,?_,?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with oj|nj
    · exact fan j oj
    · obtain rfl : j=g := List.mem_singleton.mp nj
      simp [g]
  · apply extendBack _ _ back
    simp_all [g]
  · rw [traceAdd]; simpa [g] using ht
  · intro f mem
    rcases mem with rfl|mem
    · refine ⟨n+2+gs.length,by simp,?_⟩
      funext i; rw [fresh]; simp [g,GateOp.eval,ea,eb,disj]
    · obtain ⟨p,hp,eq⟩ := sig _ mem
      exact ⟨p,by simp; omega,(old _ _ _ hp).trans eq⟩

theorem Built.notGate {f : Col m} (ih : Built x tr k S) (hf : f∈S) : Built x (tr++[inv f]) (k+1) (insert (inv f) S) := by
  obtain ⟨gs,fan,back,sz,ht,sig⟩ := ih
  obtain ⟨a,ha,ea⟩ := sig _ hf
  let g : Gate := ⟨.not,[a]⟩
  have ev : val x (gs++[g]) (n+2+gs.length)=inv f := by
    funext i; rw [fresh]; simp [g,GateOp.eval,ea,inv]
  refine ⟨gs++[g],?_,?_,by simpa using sz,by simp [traceAdd,g,ht,ev],?_⟩
  · intro j hj
    rcases List.mem_append.mp hj with old|new
    · exact fan j old
    · obtain rfl : j=g := List.mem_singleton.mp new
      simp [g]
  · apply extendBack _ _ back; simpa [g] using ha
  · intro f mem
    rcases mem with rfl|mem
    · exact ⟨_,by simp,ev⟩
    · obtain ⟨p,hp,eq⟩ := sig _ mem
      exact ⟨p,by simp; omega,(old _ _ _ hp).trans eq⟩

end Compiler

section Construction
open scoped Classical
variable {n m : ℕ} {x : Fin m → Finset (Fin n)} {tr : List (Col m)} {k : ℕ} {S : Set (Col m)}

noncomputable def Grow (x : Fin m → Finset (Fin n)) (tr : List (Col m)) (k : ℕ) (S : Set (Col m))
    (b : ℕ) (f : Col m) := ∃ T, Built x tr (k+b) T ∧ S⊆T ∧ f∈T

theorem batch {ι : Type} (s : Finset ι) (F : ι → Col m) (b : ℕ) (H : Built x tr k S)
    (make : ∀ {K T}, Built x tr K T → S⊆T → ∀ a∈s, Grow x tr K T b (F a)) :
    ∃ T, Built x tr (k+s.card*b) T ∧ S⊆T ∧ ∀ a∈s, F a∈T := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simp⟩
  | @insert a s fresh ih =>
    obtain ⟨U,hU,sub,allU⟩ := ih (fun h st i hi => make h st i (Finset.mem_insert_of_mem hi))
    obtain ⟨T,hT,ut,hit⟩ := make hU sub a (Finset.mem_insert_self _ _)
    refine ⟨T,by simpa [Finset.card_insert_of_notMem fresh,Nat.add_mul,Nat.add_assoc] using hT,sub.trans ut,?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hh
    · exact hit
    · exact ut (allU _ hh)

theorem allFold {ι : Type} (s : Finset ι) (F : ι → Col m) (H : Built x tr k S)
    (unit : (fun _ => true)∈S) (get : ∀ a∈s, F a∈S) :
    Grow x tr k S s.card (fun j => decide (∀ a∈s, F a j=true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simpa using unit⟩
  | @insert a s fr ih =>
    obtain ⟨T,h,st,ft⟩ := ih (fun a ha => get a (Finset.mem_insert_of_mem ha))
    have g := Built.andGate h (st (get a (Finset.mem_insert_self _ _))) ft
    refine ⟨_,by simpa [Finset.card_insert_of_notMem fr,Nat.add_assoc] using g,st.trans (Set.subset_insert _ _),?_⟩
    apply Set.mem_insert_iff.mpr; left
    funext j
    simp [conj, Bool.decide_and]

theorem anyFold {ι : Type} (s : Finset ι) (F : ι → Col m) (H : Built x tr k S)
    (unit : (fun _ => false)∈S) (get : ∀ a∈s, F a∈S) :
    Grow x tr k S s.card (fun j => decide (∃ a∈s, F a j=true)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨S,by simpa using H,Set.Subset.rfl,by simpa using unit⟩
  | @insert a s fr ih =>
    obtain ⟨T,h,st,ft⟩ := ih (fun a ha => get a (Finset.mem_insert_of_mem ha))
    have g := Built.orGate h (st (get a (Finset.mem_insert_self _ _))) ft
    refine ⟨_,by simpa [Finset.card_insert_of_notMem fr,Nat.add_assoc] using g,st.trans (Set.subset_insert _ _),?_⟩
    apply Set.mem_insert_iff.mpr; left
    funext j
    simp [disj, Bool.decide_or]

noncomputable def indicator (x : Fin m → Finset (Fin n)) (v : Fin m → ℕ) (i : Fin m) : Col m :=
  fun j => decide (x i⊆x j ∧ v i=v j)
noncomputable def hist (r : ℕ) (v : Fin m → ℕ) : List (Col m) :=
  List.ofFn fun b : Fin r => fun i => !(v i).testBit (r-1-b.val)

theorem hist_succ (r : ℕ) (v : Fin m → ℕ) :
    hist (r+1) v=hist r (fun i => v i/2) ++ [fun i => !(v i).testBit 0] := by
  rw [hist,List.ofFn_succ',List.concat_eq_append]
  congr 1
  · unfold hist
    congr 1
    funext b i
    simp [Nat.testBit_div_two,show r-1-(b:ℕ)+1 = r+1-1-b by have := b.isLt; omega]
  · simp

theorem stages (x : Fin m → Finset (Fin n)) (r : ℕ) (v : Fin m → ℕ)
    (cap : ∀ i, v i<2^r) (mono : ∀ i j, x i⊆x j → v i≤v j) :
    ∃ S, Built x (hist r v) (m*(n+2*r)+r) S ∧ base x ⊆ S ∧ ∀ i, indicator x v i∈S := by
  induction r generalizing v with
  | zero =>
    have z : ∀ i,v i=0 := fun i => by have := cap i; simp at this; omega
    obtain ⟨T,bt,st,allT⟩ := batch (Finset.univ : Finset (Fin m)) (indicator x v) n (Built.start (x:=x)) (by
      intro K U h bu i _
      obtain ⟨V,hh,sub,fi⟩ := allFold (x i) (sing x) h (bu (Or.inr (Or.inl rfl)))
        (fun a _ => bu (Or.inr (Or.inr ⟨a,rfl⟩)))
      have lim := Finset.card_le_univ (x i)
      refine ⟨V,hh.relax (by simpa using Nat.add_le_add_left lim K) Set.Subset.rfl,sub,?_⟩
      have eq : indicator x v i = (fun j => decide (∀ a ∈ x i,sing x a j=true)) := by
        funext j; simp [indicator,sing,z,Finset.subset_iff]
      rw [eq]; convert fi using 1; funext j; apply Bool.eq_iff_iff.mpr; simp)
    exact ⟨T,by simpa [hist] using bt,st,fun i => allT i (Finset.mem_univ _)⟩
  | succ r ih =>
    let u := fun i => v i/2
    have ucap : ∀ i,u i<2^r := fun i => by have := cap i; simp [pow_succ] at this; dsimp [u]; omega
    obtain ⟨S,h,bs,hInd⟩ := ih u ucap (fun i j h => Nat.div_le_div_right (mono i j h))
    let bit : Col m := fun i => (v i).testBit 0
    let sel := Finset.univ.filter fun i => bit i=true
    obtain ⟨T,hT,st,hit⟩ := anyFold sel (indicator x u) h (bs (Or.inl rfl)) (fun i _ => hInd i)
    have eqn : (fun j => decide (∃ a∈sel, indicator x u a j=true))=bit := by
      funext j
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,indicator,sel,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨a,ba,sub,eq⟩
        have ord := mono a j sub
        simp [u] at eq
        simp [bit] at ba ⊢
        omega
      · intro b; exact ⟨j,b,Finset.Subset.rfl,rfl⟩
    have hit2 : bit ∈ T := by
      rw [←eqn]; convert hit using 1; funext j; apply Bool.eq_iff_iff.mpr; simp
    have hn := Built.notGate hT hit2
    let U := insert (inv bit) T
    have su : S⊆U := st.trans (Set.subset_insert _ _)
    obtain ⟨V,hV,uv,allV⟩ := batch (Finset.univ : Finset (Fin m)) (indicator x v) 1 hn (by
      intro K W hw uw i _
      have iw := uw (su (hInd i))
      by_cases bi : bit i=true
      · have same : indicator x v i=indicator x u i := by
          funext j; simp only [indicator,decide_eq_decide]
          constructor
          · rintro ⟨a,b⟩; exact ⟨a,congrArg (·/2) b⟩
          · rintro ⟨a,b⟩; have ord := mono i j a
            simp [bit] at bi; dsimp [u] at b; exact ⟨a,by omega⟩
        exact ⟨W,hw.relax (by omega) Set.Subset.rfl,Set.Subset.rfl,same ▸ iw⟩
      · have bw : inv bit ∈ W := uw (Set.mem_insert _ _)
        have made := Built.andGate hw iw bw
        refine ⟨_,made,Set.subset_insert _ _,Set.mem_insert_iff.mpr (Or.inl ?_)⟩
        funext j
        apply Bool.eq_iff_iff.mpr
        simp only [indicator,conj,inv,decide_eq_true_eq,Bool.and_eq_true,Bool.not_eq_true']
        simp [bit] at bi
        simp [bit,u]
        grind)
    have lim : sel.card≤ m := by simpa using Finset.card_le_univ sel
    rw [hist_succ]
    refine ⟨V,hV.relax ?_ Set.Subset.rfl,(bs.trans su).trans uv,fun i => allV i (Finset.mem_univ _)⟩
    simp only [Finset.card_univ,Fintype.card_fin,mul_one]
    simp only [Nat.mul_add,Nat.mul_succ] at *
    omega
end Construction

end StageNet
end PEqualNP.Outside.L_lib_1402

namespace PEqualNP.Outside.L_lib_1402
namespace Encoder

theorem runCode {h r b : Nat} (W : Fin (h+1) → Finset (Fin r)) (inj : Function.Injective W)
    (falls : (Finset.univ.filter (fun i : Fin h => ¬ W i.castSucc ⊆ W i.succ)).card < 2^b) :
    ∃ v : Fin (h+1) → Nat, Monotone v ∧ (∀ i, v i < 2^(min b r)) ∧
      ∀ i j, i ≤ j → v i = v j → W i ⊆ W j := by
  classical
  let bad := Finset.univ.filter (fun i : Fin h => ¬ W i.castSucc ⊆ W i.succ)
  let before := fun i : Fin (h+1) => bad.filter (fun j => j.val < i.val)
  let v := fun i => (before i).card
  have sub {i j : Fin (h+1)} (le : i ≤ j) : before i ⊆ before j := by
    intro k mk
    obtain ⟨mb,lt⟩ := Finset.mem_filter.mp mk
    exact Finset.mem_filter.mpr ⟨mb,lt_of_lt_of_le lt le⟩
  have mono : Monotone v := fun _ _ le => Finset.card_le_card (sub le)
  have across (k : Fin h) (no : ¬ W k.castSucc ⊆ W k.succ) : v k.castSucc < v k.succ := by
    apply Finset.card_lt_card
    apply lt_of_le_of_ne (sub (Fin.castSucc_le_succ k))
    intro eq
    have mem : k ∈ before k.succ :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,no⟩,Nat.lt_succ_self _⟩
    obtain ⟨_,lt⟩ := Finset.mem_filter.mp (eq ▸ mem : k ∈ before k.castSucc)
    exact (Nat.lt_irrefl k.val) lt
  refine ⟨v,mono,?_,?_⟩
  · intro i
    have bound : v i ≤ bad.card := Finset.card_le_card (Finset.filter_subset _ _)
    by_cases br : b ≤ r
    · rw [Nat.min_eq_left br]
      exact lt_of_le_of_lt bound falls
    · rw [Nat.min_eq_right (by omega)]
      have bc : bad.card ≤ h := by simpa using Finset.card_le_univ bad
      have hcap : h+1 ≤ 2^r := by simpa using Fintype.card_le_of_injective W inj
      omega
  · intro i j
    induction j using Fin.induction with
    | zero =>
      intro le _
      have eq : i = 0 := le_antisymm le (Fin.zero_le i)
      subst i
      exact Finset.Subset.refl _
    | succ j ih =>
      intro le eq
      by_cases same : i = j.succ
      · subst i
        exact Finset.Subset.refl _
      have small : i ≤ j.castSucc := by
        have lt : i < j.succ := lt_of_le_of_ne le same
        exact Nat.le_of_lt_succ lt
      have less := mono small
      have next := mono (Fin.castSucc_le_succ j)
      have last : W j.castSucc ⊆ W j.succ := by
        by_contra no
        have := across j no
        omega
      exact (ih small (by omega)).trans last

end Encoder
end PEqualNP.Outside.L_lib_1402

namespace PEqualNP.Outside.L_lib_1402
namespace Encoder
open StageNet
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
variable {h m : Nat}

noncomputable def level (A : Finset (Fin h)) : Fin (h+1) :=
  ⟨A.sup (fun j => j.val+1), by
    apply Nat.lt_succ_of_le
    apply Finset.sup_le
    intro j _
    have := j.isLt
    omega⟩

noncomputable def suffix (x : Fin m → Finset (Fin h)) (k : Nat) : Col m :=
  fun j => decide (∃ a ∈ x j, k ≤ a.val)

lemma suffixBase (x : Fin m → Finset (Fin h)) : suffix x h = fun _ => false := by
  funext j
  unfold suffix
  apply decide_eq_false
  rintro ⟨a,_,ha⟩
  exact (Nat.not_le_of_lt a.isLt) ha

lemma suffixStep (x : Fin m → Finset (Fin h)) (k : Nat) (hk : k<h) :
    suffix x k = disj (sing x ⟨k,hk⟩) (suffix x (k+1)) := by
  funext j
  apply Bool.eq_iff_iff.mpr
  simp only [suffix, disj, sing, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨a,ha,hg⟩
    by_cases hh : a.val=k
    · left
      have eq : a = ⟨k,hk⟩ := Fin.ext hh
      simpa [eq] using ha
    · right
      exact ⟨a,ha,by omega⟩
  · rintro (ha|⟨a,ha,hh⟩)
    · exact ⟨⟨k,hk⟩,ha,le_refl _⟩
    · exact ⟨a,ha,by omega⟩

lemma suffixBuild (x : Fin m → Finset (Fin h)) (t : Nat) (ht : t ≤ h) :
    ∃ S, Built x [] t S ∧ base x ⊆ S ∧ ∀ k, h-t ≤ k → k≤h → suffix x k ∈ S := by
  induction t with
  | zero =>
    refine ⟨base x, Built.start, Set.Subset.rfl, ?_⟩
    intro k hk hf
    have eq : k=h := by omega
    rw [eq,suffixBase]
    exact Or.inl rfl
  | succ t ih =>
    obtain ⟨S,B,sub,hs⟩ := ih (by omega)
    let j := h-(t+1)
    have hj : j<h := by dsimp [j];omega
    have prev := hs (j+1) (by dsimp [j];omega) (by dsimp [j];omega)
    have add := Built.orGate B (sub (Or.inr (Or.inr ⟨⟨j,hj⟩,rfl⟩))) prev
    refine ⟨_,add,sub.trans (Set.subset_insert _ _),?_⟩
    intro k hk he
    by_cases eq : k=j
    · rw [eq,suffixStep x j hj]
      exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (hs k (by dsimp [j] at eq;omega) he)

noncomputable def mark (rank : Fin m → Fin (h+1)) (v : Fin (h+1) → Nat)
    (i : Fin (h+1)) : Col m := fun j => decide (i≤rank j ∧ v i=v (rank j))

lemma thresholdBuild (x : Fin m → Finset (Fin h)) :
    ∃ S, Built x [] h S ∧ base x ⊆ S ∧
      ∀ i : Fin (h+1), (fun j => decide (i≤level (x j))) ∈ S := by
  obtain ⟨S,B,sub,allS⟩ := suffixBuild x h (le_refl _)
  refine ⟨S,B,sub,?_⟩
  intro i
  cases hi : i.val with
  | zero =>
    have eq : (fun j => decide (i≤level (x j))) = fun _ => true := by
      funext j; apply decide_eq_true; change i.val ≤ _;omega
    rw [eq];exact sub (Or.inr (Or.inl rfl))
  | succ k =>
    have eq : (fun j => decide (i≤level (x j))) = suffix x k := by
      funext j
      simp only [suffix, decide_eq_decide]
      change i.val ≤ (x j).sup (fun a => a.val+1) ↔ _
      rw [hi]
      constructor
      · intro hh
        by_contra! no
        have lim : (x j).sup (fun a => a.val+1) ≤ k := Finset.sup_le (fun a ha => by have := no a ha;omega)
        omega
      · rintro ⟨a,ha,hh⟩
        exact le_trans (by omega : k+1 ≤ a.val+1) (Finset.le_sup (f := fun a : Fin h => a.val+1) ha)
    rw [eq]
    exact allS k (by omega) (by have := i.isLt;omega)

lemma runStages (x : Fin m → Finset (Fin h)) (k : Nat) (v : Fin (h+1) → Nat)
    (cap : ∀ i, v i<2^k) (mono : Monotone v) :
    ∃ S, Built x (hist k (fun j => v (level (x j)))) (h+(h+1)*(2*k)+k) S ∧
      base x ⊆ S ∧ ∀ i, mark (fun j => level (x j)) v i ∈ S := by
  induction k generalizing v with
  | zero =>
    obtain ⟨S,B,sub,ts⟩ := thresholdBuild x
    have z : ∀ i,v i=0 := fun i => by have := cap i;simp at this;omega
    refine ⟨S,by simpa [hist] using B,sub,?_⟩
    intro i
    have hh : mark (fun j => level (x j)) v i = fun j => decide (i ≤ level (x j)) := by
      funext j
      simp [mark,z]
    rw [hh]
    exact ts i
  | succ k ih =>
    let u := fun i => v i/2
    have uc : ∀ i,u i<2^k := fun i => by have := cap i;simp [pow_succ] at this;dsimp [u];omega
    obtain ⟨S,B,sub,old⟩ := ih u uc (fun _ _ le => Nat.div_le_div_right (mono le))
    let rank := fun j => level (x j)
    let bit := fun i => (v i).testBit 0
    let sel := Finset.univ.filter (fun i => bit i = true)
    obtain ⟨T,BT,st,hit⟩ := anyFold sel (mark rank u) B (sub (Or.inl rfl))
      (fun i _ => old i)
    have eqn : (fun j => decide (∃ a∈sel, mark rank u a j=true)) = fun j => bit (rank j) := by
      funext j
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,mark,sel,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨a,ba,le,eq⟩
        have ord := mono le
        simp [u] at eq
        simp [bit] at ba ⊢
        omega
      · intro bb
        exact ⟨rank j,bb,le_rfl,rfl⟩
    have hit' : (fun j => bit (rank j)) ∈ T := by
      rw [←eqn];convert hit using 1;funext j;apply Bool.eq_iff_iff.mpr;simp
    have BN := Built.notGate BT hit'
    have st' : S ⊆ insert (inv (fun j => bit (rank j))) T := st.trans (Set.subset_insert _ _)
    obtain ⟨U,BU,su,allU⟩ := batch (Finset.univ : Finset (Fin (h+1))) (mark rank v) 1 BN (by
      intro K R br sr i _
      have iw := sr (st' (old i))
      by_cases bi : bit i=true
      · have same : mark rank v i=mark rank u i := by
          funext j;simp only [mark,decide_eq_decide]
          constructor
          · rintro ⟨a,b⟩;exact ⟨a,congrArg (·/2) b⟩
          · rintro ⟨a,b⟩
            have ord := mono a
            simp [bit] at bi;dsimp [u] at b
            exact ⟨a,by omega⟩
        exact ⟨R,br.relax (by omega) Set.Subset.rfl,Set.Subset.rfl,same ▸ iw⟩
      · have bw : inv (fun j => bit (rank j)) ∈ R := sr (Set.mem_insert _ _)
        have made := Built.andGate br iw bw
        refine ⟨_,made,Set.subset_insert _ _,Set.mem_insert_iff.mpr (Or.inl ?_)⟩
        funext j
        apply Bool.eq_iff_iff.mpr
        simp only [mark,conj,inv,decide_eq_true_eq,Bool.and_eq_true,Bool.not_eq_true']
        simp [bit] at bi
        simp [bit,u]
        grind)
    have lim : sel.card≤h+1 := by simpa using Finset.card_le_univ sel
    rw [hist_succ]
    refine ⟨U,BU.relax ?_ Set.Subset.rfl,(sub.trans st').trans su,fun i => allU i (Finset.mem_univ _)⟩
    simp only [Finset.card_univ,Fintype.card_fin,mul_one]
    ring_nf at *
    omega

lemma encodeWithRuns {r b : Nat} (W : Fin (h+1) → Finset (Fin r)) (v : Fin (h+1) → Nat)
    (mono : Monotone v) (cap : ∀ i, v i < 2^(min b r))
    (grow : ∀ i j, i ≤ j → v i = v j → W i ⊆ W j) :
    ∃ (C : Circuit) (wire : Fin r → Nat),
      FanInTwo C ∧ ReadsBack (h+2) C ∧ C.output < h+2+C.size ∧
      (∀ j, wire j < h+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
      C.size - PEqualNP.NotBracket.notCount C ≤ 10*(r+1)*(h+1) ∧
      ∀ (A : Finset (Fin h)) (i : Fin (h+1)), A.sup (fun j => j.val+1)=i.val →
        (Finset.univ.filter (fun j : Fin r => (C.wires (List.ofFn (fun j : Fin h => decide (j∈A)) ++ [false,true])).getD (wire j) false=true))=W i := by
  classical
  let n := Fintype.card (Finset (Fin h))
  let ixA : Finset (Fin h) ≃ Fin n := Fintype.equivFin _
  let x : Fin n → Finset (Fin h) := ixA.symm
  let rank := fun j => level (x j)
  let k := min b r
  obtain ⟨S,bs,baseS,marks⟩ := runStages x k v cap mono
  let col : Fin r → Col n := fun t j => decide (t∈W (rank j))
  obtain ⟨T,bt,_,hits⟩ := batch (Finset.univ : Finset (Fin r)) col (h+1) bs (by
    intro K U bu su t _
    let sel := Finset.univ.filter (fun a => t∈W a)
    obtain ⟨V,bv,uv,hv⟩ := anyFold sel (mark rank v) bu (su (baseS (Or.inl rfl))) (fun i _ => su (marks i))
    have same : col t = (fun j => decide (∃ a∈sel, mark rank v a j=true)) := by
      funext j
      simp only [col,mark,decide_eq_decide,decide_eq_true_eq,sel,Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · intro ht
        exact ⟨rank j,ht,le_rfl,rfl⟩
      · rintro ⟨a,hm,le,eq⟩
        exact grow a (rank j) le eq hm
    have lim : sel.card ≤ h+1 := by simpa using Finset.card_le_univ sel
    refine ⟨V,bv.relax (by omega) Set.Subset.rfl,uv,?_⟩
    rw [same]
    convert hv using 1
    funext j
    apply Bool.eq_iff_iff.mpr
    simp)
  obtain ⟨gs,fan,back,sz,ht,wire⟩ := bt
  choose tap valid data using fun a => wire _ (hits a (Finset.mem_univ _))
  have hlen := congrArg List.length ht
  simp [trace,hist] at hlen
  have nots := (countIx gs).trans hlen
  refine ⟨⟨gs,0⟩,tap,fan,back,by simp [Circuit.size],valid,nots.le.trans (Nat.min_le_left ..),?_,?_⟩
  · change gs.length - _ ≤ _
    simp only [Finset.card_univ,Fintype.card_fin] at sz
    have kr : k ≤ r := Nat.min_le_right ..
    have times := Nat.mul_le_mul_left (h+1) kr
    have nle := Nat.sub_le gs.length (PEqualNP.NotBracket.notCount ⟨gs,0⟩)
    nlinarith
  · intro A i hl
    have hA : x (ixA A)=A := ixA.symm_apply_apply A
    have hi : rank (ixA A)=i := Fin.ext (by simpa [rank,level,hA] using hl)
    ext t
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    have ev := congrFun (data t) (ixA A)
    simp only [val,raw,col,hi,hA] at ev
    rw [ev]
    simp

lemma encoder {r b : Nat} (W : Fin (h+1) → Finset (Fin r)) (inj : Function.Injective W)
    (falls : (Finset.univ.filter (fun i : Fin h => ¬ W i.castSucc ⊆ W i.succ)).card < 2^b) :
    ∃ (C : Circuit) (wire : Fin r → Nat),
      FanInTwo C ∧ ReadsBack (h+2) C ∧ C.output < h+2+C.size ∧
      (∀ j, wire j < h+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
      C.size - PEqualNP.NotBracket.notCount C ≤ 10*(r+1)*(h+1) ∧
      ∀ (A : Finset (Fin h)) (i : Fin (h+1)), A.sup (fun j => j.val+1)=i.val →
        (Finset.univ.filter (fun j : Fin r => (C.wires (List.ofFn (fun j : Fin h => decide (j∈A)) ++ [false,true])).getD (wire j) false=true))=W i := by
  obtain ⟨v,mono,cap,grow⟩ := runCode W inj falls
  exact encodeWithRuns W v mono cap grow

end Encoder
end PEqualNP.Outside.L_lib_1402

namespace PEqualNP.Outside.L_lib_1402
namespace StageNet

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def Chain {r : Nat} (U : Finset (Finset (Fin r))) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, x ⊆ y ∨ y ⊆ x

noncomputable def belowChoices {r : Nat} (S : Finset (Finset (Fin r))) (x : Finset (Fin r)) := by
  classical
  exact S.powerset.filter (fun U => Chain U ∧ ∀ y ∈ U, y ⊂ x)

noncomputable def rankBelow {r : Nat} (S : Finset (Finset (Fin r))) (x : Finset (Fin r)) : Nat :=
  (belowChoices S x).sup Finset.card

theorem below_iff {r : Nat} {S : Finset (Finset (Fin r))} {x : Finset (Fin r)}
    {U : Finset (Finset (Fin r))} :
    U ∈ belowChoices S x ↔ U ⊆ S ∧ Chain U ∧ ∀ y ∈ U, y ⊂ x := by
  classical
  simp [belowChoices,Finset.mem_powerset]

theorem best_below {r : Nat} (S : Finset (Finset (Fin r))) (x : Finset (Fin r)) :
    ∃ U ∈ belowChoices S x, rankBelow S x = U.card := by
  classical
  apply Finset.exists_mem_eq_sup
  exact ⟨∅,below_iff.mpr ⟨Finset.empty_subset _,by simp [Chain],by simp⟩⟩

theorem chain_insert_top {r : Nat} {U : Finset (Finset (Fin r))} {x : Finset (Fin r)}
    (chain : Chain U) (lt : ∀ y ∈ U, y ⊂ x) : Chain (insert x U) := by
  classical
  intro a ma b mb
  rcases Finset.mem_insert.mp ma with rfl | ha <;> rcases Finset.mem_insert.mp mb with rfl | hb
  · exact Or.inl (Finset.Subset.refl _)
  · exact Or.inr (le_of_lt (lt _ hb))
  · exact Or.inl (le_of_lt (lt _ ha))
  · exact chain _ ha _ hb

theorem rank_strict {r : Nat} (S : Finset (Finset (Fin r))) {x y : Finset (Fin r)}
    (hx : x ∈ S) (xy : x ⊂ y) : rankBelow S x < rankBelow S y := by
  classical
  obtain ⟨U,mem,best⟩ := best_below S x
  obtain ⟨sub,ch,lt⟩ := below_iff.mp mem
  have fresh : x ∉ U := fun h => (lt_irrefl x) (lt x h)
  have bigger : insert x U ∈ belowChoices S y := by
    refine below_iff.mpr ⟨Finset.insert_subset hx sub,chain_insert_top ch lt,?_⟩
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact xy
    · exact lt_trans (lt a ha) xy
  have count : (insert x U).card ≤ rankBelow S y :=
    Finset.le_sup (f := Finset.card) bigger
  rw [Finset.card_insert_of_notMem fresh] at count
  omega

theorem rank_lt_height {r t : Nat} (S : Finset (Finset (Fin r)))
    (height : ∀ U ⊆ S, Chain U → U.card ≤ t) {x : Finset (Fin r)} (hx : x ∈ S) :
    rankBelow S x < t := by
  classical
  obtain ⟨U,mem,best⟩ := best_below S x
  obtain ⟨sub,ch,lt⟩ := below_iff.mp mem
  have fresh : x ∉ U := fun h => (lt_irrefl x) (lt x h)
  have card := height (insert x U) (Finset.insert_subset hx sub) (chain_insert_top ch lt)
  rw [Finset.card_insert_of_notMem fresh] at card
  omega

theorem decoder {h r c : Nat} (W : Fin (h+1) → Finset (Fin r)) (inj : Function.Injective W)
    (height : ∀ U ⊆ Finset.univ.image W, (∀ x ∈ U, ∀ y ∈ U, x ⊆ y ∨ y ⊆ x) → U.card ≤ 2^c) :
    ∃ (D : Circuit) (out : Fin (h+1) → Nat),
      FanInTwo D ∧ ReadsBack (r+2) D ∧ D.output < r+2+D.size ∧
      (∀ j, out j < r+2+D.size) ∧ PEqualNP.NotBracket.notCount D ≤ c ∧
      D.size - PEqualNP.NotBracket.notCount D ≤ 3*r*(h+1) ∧
      ∀ i j, (D.wires (List.ofFn (fun a : Fin r => decide (a ∈ W i)) ++ [false,true])).getD
        (out j) false = decide (i=j) := by
  classical
  let S := Finset.univ.image W
  have mem (i : Fin (h+1)) : W i ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  let k := min c r
  obtain ⟨v,cap,strict⟩ : ∃ v : Fin (h+1) → Nat, (∀ i, v i < 2^k) ∧
      ∀ i j, W i ⊂ W j → v i < v j := by
    by_cases cr : c ≤ r
    · refine ⟨fun i => rankBelow S (W i),?_,fun i j h => rank_strict S (mem i) h⟩
      intro i
      simpa [k, Nat.min_eq_left cr] using rank_lt_height S height (mem i)
    · refine ⟨fun i => (W i).card,?_,fun i j h => Finset.card_lt_card h⟩
      intro i
      have hi : (W i).card ≤ r := by simpa using Finset.card_le_univ (W i)
      have rk : k = r := Nat.min_eq_right (by omega)
      rw [rk]
      exact lt_of_le_of_lt hi (Nat.lt_two_pow_self)
  have mono : ∀ i j, W i ⊆ W j → v i ≤ v j := by
    intro i j h
    by_cases e : W i = W j
    · rw [inj e]
    · exact le_of_lt (strict i j (lt_of_le_of_ne h e))
  obtain ⟨T,built,_,ind⟩ := stages W k v cap mono
  obtain ⟨gs,fan,back,size,histEq,wire⟩ := built
  choose out valid data using fun i => wire _ (ind i)
  have traceSize := congrArg List.length histEq
  simp [trace,hist] at traceSize
  let D : Circuit := ⟨gs,0⟩
  have nCount : PEqualNP.NotBracket.notCount D = k := (countIx gs).trans traceSize
  have kc : k ≤ c := Nat.min_le_left _ _
  have kr : k ≤ r := Nat.min_le_right _ _
  refine ⟨D,out,fan,back,by simp [D,Circuit.size],valid,nCount ▸ kc,?_,?_⟩
  · rw [nCount]
    change gs.length-k ≤ _
    have h1 : (h+1)*(r+2*k) ≤ (h+1)*(3*r) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_comm (h+1) (3*r)] at h1
    omega
  · intro i j
    have d := congrFun (data j) i
    change val W gs (out j) i = _
    rw [d]
    change decide (W j ⊆ W i ∧ v j = v i) = decide (i=j)
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨sub,eq⟩
      by_contra ne
      have noeq : W j ≠ W i := fun e => ne (inj e).symm
      exact (ne_of_lt (strict j i (lt_of_le_of_ne sub noeq))) eq
    · rintro rfl
      exact ⟨Finset.Subset.refl _,rfl⟩

end StageNet
end PEqualNP.Outside.L_lib_1402

namespace PEqualNP.Outside.L_lib_1402
namespace Poset

theorem matchUp {r q : Nat} (S : Finset (Finset (Fin r)))
    (width : ∀ U ⊆ S, (∀ x ∈ U, ∀ y ∈ U, x ⊆ y → x = y) → U.card ≤ q) :
    ∃ f : ↥S → (↥S ⊕ Fin q), Function.Injective f ∧
      ∀ x y : ↥S, f x = Sum.inl y → x.val ⊂ y.val := by
  classical
  let higher := fun x : ↥S => Finset.univ.filter (fun y : ↥S => x.val ⊂ y.val)
  let choices := fun x : ↥S => (higher x).disjSum (Finset.univ : Finset (Fin q))
  obtain ⟨f, inj, good⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective choices).mp (by
    intro u
    rcases u.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
    · simp
    let above := u.biUnion higher
    let mins := u \ above
    let actual := mins.image Subtype.val
    have inS : actual ⊆ S := by
      intro x hx
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
      exact a.property
    have anti : ∀ x ∈ actual, ∀ y ∈ actual, x ⊆ y → x = y := by
      intro x hx y hy le
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
      by_contra hne
      have lt : a.val ⊂ b.val := lt_of_le_of_ne le hne
      have hab : b ∈ above := Finset.mem_biUnion.mpr
        ⟨a,(Finset.mem_sdiff.mp ha).1,Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt⟩⟩
      exact (Finset.mem_sdiff.mp hb).2 hab
    have cm : mins.card ≤ q := by
      simpa [actual, Finset.card_image_of_injective _ Subtype.val_injective] using width actual inS anti
    have cu : u ⊆ mins ∪ above := by
      intro x mem
      by_cases h : x ∈ above
      · exact Finset.mem_union_right _ h
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨mem,h⟩)
    have right : above.disjSum (Finset.univ : Finset (Fin q)) ⊆ u.biUnion choices := by
      intro z hz
      cases z with
      | inl y =>
        have hy : y ∈ above := by simpa using hz
        obtain ⟨x,hx,hm⟩ := Finset.mem_biUnion.mp hy
        exact Finset.mem_biUnion.mpr ⟨x,hx,by simpa [choices] using hm⟩
      | inr j => exact Finset.mem_biUnion.mpr ⟨w,hw,by simp [choices]⟩
    have h1 := Finset.card_le_card cu
    have h2 := Finset.card_union_le mins above
    have h3 := Finset.card_le_card right
    rw [Finset.card_disjSum,Finset.card_univ,Fintype.card_fin] at h3
    omega)
  refine ⟨f,inj,?_⟩
  intro x y eq
  have mem := good x
  rw [eq] at mem
  have higher_mem : y ∈ higher x := by simpa [choices] using mem
  exact (Finset.mem_filter.mp higher_mem).2

noncomputable def prev {X Y : Type} (f : X → X ⊕ Y) (z : X ⊕ Y) : Option X := by
  classical
  exact if h : ∃ x, f x = z then some h.choose else none

theorem prev_eq_some {X Y : Type} {f : X → X ⊕ Y} (inj : Function.Injective f)
    (z : X ⊕ Y) (x : X) : prev f z = some x ↔ f x = z := by
  classical
  unfold prev
  split <;> rename_i h
  · constructor
    · intro eq
      rw [← Option.some.inj eq]
      exact h.choose_spec
    · intro eq
      exact congrArg some (inj (h.choose_spec.trans eq.symm))
  · simp only [reduceCtorEq, false_iff]
    exact fun eq => h ⟨x,eq⟩

noncomputable def predAt {X Y : Type} (f : X → X ⊕ Y) (j : Y) : Nat → Option X
  | 0 => prev f (.inr j)
  | n + 1 => (predAt f j n).bind (fun x => prev f (.inl x))

theorem all_on_path {r q : Nat} {S : Finset (Finset (Fin r))}
    (f : ↥S → (↥S ⊕ Fin q)) (inj : Function.Injective f)
    (greater : ∀ x y : ↥S, f x = .inl y → x.val ⊂ y.val) (x : ↥S) :
    ∃ (j : Fin q) (n : Nat), predAt f j n = some x := by
  classical
  suffices ∀ k (x : ↥S), r - x.val.card = k → ∃ j n, predAt f j n = some x by exact this _ x rfl
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro x hx
    cases eq : f x with
    | inr j => exact ⟨j,0,(prev_eq_some inj _ _).mpr eq⟩
    | inl y =>
      have hxy := Finset.card_lt_card (greater x y eq)
      have hy : y.val.card ≤ r := by simpa using Finset.card_le_univ y.val
      obtain ⟨j,n,at_y⟩ := ih (r-y.val.card) (by omega) y rfl
      refine ⟨j,n+1,?_⟩
      rw [predAt,at_y]
      exact (prev_eq_some inj _ _).mpr eq

theorem same_path_subset {r q : Nat} {S : Finset (Finset (Fin r))}
    (f : ↥S → (↥S ⊕ Fin q)) (inj : Function.Injective f)
    (greater : ∀ x y : ↥S, f x = .inl y → x.val ⊂ y.val) (j : Fin q)
    {i k : Nat} (le : i ≤ k) {x y : ↥S}
    (hx : predAt f j i = some x) (hy : predAt f j k = some y) : y.val ⊆ x.val := by
  induction le generalizing y with
  | refl =>
    have eq : x = y := Option.some.inj (hx.symm.trans hy)
    exact eq ▸ Finset.Subset.refl _
  | @step k _ ih =>
    obtain ⟨z,hz,hm⟩ := Option.bind_eq_some_iff.mp hy
    have fy : f y = .inl z := (prev_eq_some inj _ _).mp hm
    exact le_trans (le_of_lt (greater y z fy)) (ih hz)

theorem width_colors {r q : Nat} (S : Finset (Finset (Fin r)))
    (width : ∀ U ⊆ S, (∀ x ∈ U, ∀ y ∈ U, x ⊆ y → x = y) → U.card ≤ q) :
    ∃ color : ↥S → Fin q, ∀ x y : ↥S, color x = color y → x.val ⊆ y.val ∨ y.val ⊆ x.val := by
  classical
  obtain ⟨f,inj,greater⟩ := matchUp S width
  choose color depth found using all_on_path f inj greater
  refine ⟨color,?_⟩
  intro x y eq
  have hx := found x
  have hy := found y
  rw [← eq] at hy
  rcases le_total (depth x) (depth y) with le | ge
  · exact Or.inr (same_path_subset f inj greater _ le hx hy)
  · exact Or.inl (same_path_subset f inj greater _ ge hy hx)

end Poset
end PEqualNP.Outside.L_lib_1402

namespace PEqualNP.Outside.L_lib_1402

theorem orderedEnumerationOfChainColors {h r q : Nat} (S : Finset (Finset (Fin r)))
    (hS : S.card = h+1) (color : ↥S → Fin q)
    (hc : ∀ x y : ↥S, color x = color y → x.val ⊆ y.val ∨ y.val ⊆ x.val) :
    ∃ W : Fin (h+1) → Finset (Fin r), Function.Injective W ∧ Finset.univ.image W = S ∧
      (Finset.univ.filter (fun i : Fin h => ¬ W i.castSucc ⊆ W i.succ)).card < q := by
  classical
  let key : ↥S → Nat := fun x => (color x).val * (r+1) + x.val.card
  have cardLt (x : ↥S) : x.val.card < r+1 := by
    have hh := Finset.card_le_univ x.val
    simpa using Nat.lt_succ_of_le hh
  have keyLt {x y : ↥S} (xy : color x < color y) : key x < key y := by
    have hs : (color x).val + 1 ≤ (color y).val := xy
    calc
      key x < (color x).val * (r+1) + (r+1) := Nat.add_lt_add_left (cardLt x) _
      _ = ((color x).val+1)*(r+1) := (Nat.succ_mul _ _).symm
      _ ≤ (color y).val*(r+1) := Nat.mul_le_mul_right _ hs
      _ ≤ key y := Nat.le_add_right _ _
  have keyInj : Function.Injective key := by
    intro x y he
    have eqc : color x = color y := by
      rcases lt_trichotomy (color x) (color y) with hxy | heq | hyx
      · exact False.elim ((keyLt hxy).ne he)
      · exact heq
      · exact False.elim ((keyLt hyx).ne he.symm)
    have ecard : x.val.card = y.val.card := by
      dsimp [key] at he
      rw [eqc] at he
      omega
    apply Subtype.ext
    rcases hc x y eqc with hxy | hyx
    · exact Finset.eq_of_subset_of_card_le hxy ecard.ge
    · exact (Finset.eq_of_subset_of_card_le hyx ecard.le).symm
  let emb : ↥S ↪ Nat := ⟨key, keyInj⟩
  let codes := Finset.univ.map emb
  let ranks : Fin (h+1) ≃o ↥codes := codes.orderIsoOfFin (by simpa [codes] using hS)
  have ex (i : Fin (h+1)) : ∃ x : ↥S, key x = (ranks i).val := by
    obtain ⟨x, _, hx⟩ := Finset.mem_map.mp (ranks i).property
    exact ⟨x,hx⟩
  let e (i : Fin (h+1)) : ↥S := Classical.choose (ex i)
  have ek (i : Fin (h+1)) : key (e i) = (ranks i).val := Classical.choose_spec (ex i)
  have ei : Function.Injective e := by
    intro i j hh
    apply ranks.injective
    apply Subtype.ext
    rw [← ek i, ← ek j, hh]
  have es : Function.Surjective e := by
    intro x
    have hm : key x ∈ codes := Finset.mem_map.mpr ⟨x, Finset.mem_univ _, rfl⟩
    obtain ⟨i, hi⟩ := ranks.surjective ⟨key x,hm⟩
    exact ⟨i,keyInj ((ek i).trans (congrArg Subtype.val hi))⟩
  let W : Fin (h+1) → Finset (Fin r) := fun i => (e i).val
  have sorted {i j : Fin (h+1)} (hij : i ≤ j) : key (e i) ≤ key (e j) := by
    rw [ek, ek]
    exact ranks.monotone hij
  have colors {i j : Fin (h+1)} (hij : i ≤ j) : color (e i) ≤ color (e j) := by
    by_contra! hh
    exact (not_lt_of_ge (sorted hij)) (keyLt hh)
  have ascending {i j : Fin (h+1)} (hij : i ≤ j) (he : color (e i) = color (e j)) :
      W i ⊆ W j := by
    rcases hc (e i) (e j) he with hxy | hyx
    · exact hxy
    · have hl := sorted hij
      dsimp [key] at hl
      rw [he] at hl
      have eq : (e j).val = (e i).val := Finset.eq_of_subset_of_card_le hyx (by omega)
      exact eq.ge
  let falls := Finset.univ.filter (fun i : Fin h => ¬ W i.castSucc ⊆ W i.succ)
  have strict {i : Fin h} (hi : i ∈ falls) : color (e i.castSucc) < color (e i.succ) := by
    have ord : i.castSucc ≤ i.succ := by apply Fin.le_iff_val_le_val.mpr; simp
    apply lt_of_le_of_ne (colors ord)
    exact fun he => (Finset.mem_filter.mp hi).2 (ascending ord he)
  refine ⟨W, fun _ _ he => ei (Subtype.ext he), ?_, ?_⟩
  · ext x
    constructor
    · rintro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact (e i).property
    · intro hx
      obtain ⟨i, hi⟩ := es ⟨x,hx⟩
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, congrArg Subtype.val hi⟩
  · let charge : Fin h → Nat := fun i => (color (e i.castSucc)).val
    have hlt {i j : Fin h} (hi : i ∈ falls) (hij : i < j) : charge i < charge j := by
      have hn : i.succ ≤ j.castSucc := by
        change i.val + 1 ≤ j.val
        exact hij
      exact lt_of_lt_of_le (strict hi) (colors hn)
    have bound : falls.card ≤ (Finset.range (color (e (Fin.last h))).val).card := by
      apply Finset.card_le_card_of_injOn charge
      · intro i hi
        apply Finset.mem_range.mpr
        exact lt_of_lt_of_le (strict hi) (colors (Fin.le_last _))
      · intro i hi j hj he
        rcases lt_trichotomy i j with h | h | h
        · exact False.elim ((hlt hi h).ne he)
        · exact h
        · exact False.elim ((hlt hj h).ne he.symm)
    exact lt_of_le_of_lt (by simpa using bound) (color (e (Fin.last h))).isLt

end PEqualNP.Outside.L_lib_1402

namespace PEqualNP.Outside.L_lib_1402

theorem widthOfOrderedColors {h r q : Nat} (W : Fin (h+1) → Finset (Fin r))
    (hW : Function.Injective W) (color : Fin (h+1) → Fin q)
    (hc : ∀ i j, i ≤ j → color i = color j → W i ⊆ W j) :
    ∀ U ⊆ Finset.univ.image W, (∀ x ∈ U, ∀ y ∈ U, x ⊆ y → x = y) → U.card ≤ q := by
  classical
  intro U hU hanti
  let f : Finset (Fin r) → Fin q := fun x => color (Function.invFun W x)
  have bound : U.card ≤ (Finset.univ : Finset (Fin q)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro x hx
      exact Finset.mem_univ _
    · intro x hx y hy he
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hU hx)
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (hU hy)
      have eq : color i = color j := by
        simpa [f, Function.leftInverse_invFun hW i, Function.leftInverse_invFun hW j] using he
      rcases le_total i j with hij | hji
      · exact hanti _ hx _ hy (hc i j hij eq)
      · exact (hanti _ hy _ hx (hc j i hji eq.symm)).symm
  simpa using bound

theorem heightOfComparableColors {h r q : Nat} (W : Fin (h+1) → Finset (Fin r))
    (hW : Function.Injective W) (color : Fin (h+1) → Fin q)
    (hc : ∀ i j, W i ⊆ W j → color i = color j → i = j) :
    ∀ U ⊆ Finset.univ.image W, (∀ x ∈ U, ∀ y ∈ U, x ⊆ y ∨ y ⊆ x) → U.card ≤ q := by
  classical
  intro U hU hchain
  let f : Finset (Fin r) → Fin q := fun x => color (Function.invFun W x)
  have bound : U.card ≤ (Finset.univ : Finset (Fin q)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro x hx
      exact Finset.mem_univ _
    · intro x hx y hy he
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hU hx)
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (hU hy)
      have eq : color i = color j := by
        simpa [f, Function.leftInverse_invFun hW i, Function.leftInverse_invFun hW j] using he
      rcases hchain _ hx _ hy with hij | hji
      · exact congrArg W (hc i j hij eq)
      · exact congrArg W (hc j i hji eq.symm).symm
  simpa using bound

end PEqualNP.Outside.L_lib_1402

open PEqualNP.Outside.L_lib_1402 in
theorem PEqualNP.Outside.L_lib_1402 :
  let fit := fun (h r b c z : Nat)
      (ok : Fin (h+1) → Finset (Fin r) → Prop) =>
    ∃ (C D : PEqualNP.CircuitLowerBounds.Circuit) (wire : Fin r → Nat) (out : Fin (h+1) → Nat),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (h+2) C ∧
      PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (r+2) D ∧
      C.output < h+2+C.size ∧ D.output < r+2+D.size ∧
      (∀ j, wire j < h+2+C.size) ∧ (∀ j, out j < r+2+D.size) ∧
      PEqualNP.NotBracket.notCount C ≤ b ∧ PEqualNP.NotBracket.notCount D ≤ c ∧
      (C.size - PEqualNP.NotBracket.notCount C) + (D.size - PEqualNP.NotBracket.notCount D) ≤ z ∧
      ∀ (A : Finset (Fin h)) (i : Fin (h+1)), A.sup (fun j => j.val+1) = i.val →
        let v := C.wires (List.ofFn (fun j : Fin h => decide (j ∈ A)) ++ [false,true])
        let msg := Finset.univ.filter (fun j : Fin r => v.getD (wire j) false = true)
        let w := D.wires (List.ofFn (fun j : Fin r => decide (j ∈ msg)) ++ [false,true])
        ok i msg ∧ ∀ j, w.getD (out j) false = decide (i = j)
  let heightAtMost := fun {r : Nat} (S : Finset (Finset (Fin r))) (p : Nat) =>
    ∀ U ⊆ S, (∀ x ∈ U, ∀ y ∈ U, x ⊆ y ∨ y ⊆ x) → U.card ≤ p
  let widthAtMost := fun {r : Nat} (S : Finset (Finset (Fin r))) (q : Nat) =>
    ∀ U ⊆ S, (∀ x ∈ U, ∀ y ∈ U, x ⊆ y → x = y) → U.card ≤ q
  ∀ (h r b c : Nat) (allowed : Finset (Finset (Fin r))),
    let ok := fun (_ : Fin (h+1)) (w : Finset (Fin r)) => w ∈ allowed
    let test := ∃ S ⊆ allowed, S.card = h+1 ∧ widthAtMost S (2^b) ∧ heightAtMost S (2^c)
    ((∃ z, fit h r b c z ok) ↔ test) ∧ (test → fit h r b c (64*(r+1)*(h+1)) ok) := by
  classical
  dsimp only
  intro h r b c allowed
  let ok := fun (_ : Fin (h+1)) (w : Finset (Fin r)) => w ∈ allowed
  let test := ∃ S ⊆ allowed, S.card = h+1 ∧
    (∀ U ⊆ S, (∀ x ∈ U, ∀ y ∈ U, x ⊆ y → x = y) → U.card ≤ 2^b) ∧
    (∀ U ⊆ S, (∀ x ∈ U, ∀ y ∈ U, x ⊆ y ∨ y ⊆ x) → U.card ≤ 2^c)
  change ((∃ z, Fit h r b c z ok) ↔ test) ∧ (test → Fit h r b c (64*(r+1)*(h+1)) ok)
  have sound : ∀ z, Fit h r b c z ok → test := by
    intro z physical
    obtain ⟨W,e,d,admissible,winj,encOrder,decOrder⟩ := sampleColors allowed physical
    refine ⟨Finset.univ.image W,?_,?_,widthOfOrderedColors W winj e encOrder,
      heightOfComparableColors W winj d decOrder⟩
    · intro u hu
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
      exact admissible i
    · simp [Finset.card_image_of_injective _ winj]
  have complete : test → Fit h r b c (64*(r+1)*(h+1)) ok := by
    rintro ⟨S,allowedS,cardS,width,height⟩
    obtain ⟨color,comp⟩ := PEqualNP.Outside.L_lib_1402.Poset.width_colors S width
    obtain ⟨W,inj,imageEq,falls⟩ := orderedEnumerationOfChainColors S cardS color comp
    obtain ⟨C,wire,fanC,backC,outputC,validC,invC,sizeC,encode⟩ := Encoder.encoder W inj falls
    obtain ⟨D,out,fanD,backD,outputD,validD,invD,sizeD,decode⟩ :=
      StageNet.decoder W inj (imageEq.symm ▸ height)
    refine ⟨C,D,wire,out,fanC,backC,fanD,backD,outputC,outputD,validC,validD,invC,invD,?_,?_⟩
    · nlinarith [Nat.zero_le r,Nat.zero_le h]
    · intro A i rankA
      dsimp only
      rw [encode A i rankA]
      refine ⟨allowedS ?_,decode i⟩
      rw [← imageEq]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  exact ⟨⟨fun ⟨z,p⟩ => sound z p, fun t => ⟨_,complete t⟩⟩,complete⟩

