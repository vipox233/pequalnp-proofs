import PEqualNP.Defs
import Mathlib.Data.Finset.Max

namespace PEqualNP.Outside.L_lib_1329

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

private lemma decide_eq_cdecide {P : Prop} (inst : Decidable P) :
    @decide P inst = @decide P (Classical.propDecidable P) := by
  by_cases h : P
  · rw [@decide_eq_true P inst h, @decide_eq_true P (Classical.propDecidable P) h]
  · rw [@decide_eq_false P inst h, @decide_eq_false P (Classical.propDecidable P) h]

private lemma cdecide_true {P : Prop} (h : P) :
    @decide P (Classical.propDecidable P) = true :=
  @decide_eq_true P (Classical.propDecidable P) h

private lemma cdecide_false {P : Prop} (h : ¬P) :
    @decide P (Classical.propDecidable P) = false :=
  @decide_eq_false P (Classical.propDecidable P) h

private lemma of_cdecide_true {P : Prop}
    (h : @decide P (Classical.propDecidable P) = true) : P :=
  @of_decide_eq_true P (Classical.propDecidable P) h

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private noncomputable def inp (n : Nat) (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun j : Fin n => @decide (j ∈ x) (Classical.propDecidable _)) ++ [false, true]

private lemma inp_eq_ofFn {n : Nat} (x : Finset (Fin n))
    (inst : ∀ a : Fin n, Decidable (a ∈ x)) :
    List.ofFn (fun a : Fin n => @decide (a ∈ x) (inst a)) ++ [false, true] = inp n x := by
  unfold inp
  congr 1
  apply congrArg List.ofFn
  funext a
  exact decide_eq_cdecide (inst a)

private noncomputable def wireVal (n : Nat) (C : Circuit) (x : Finset (Fin n)) (w : Nat) : Bool :=
  (C.wires (inp n x)).getD w false

private lemma wireVal_eq_foldl (n : Nat) (C : Circuit) (x : Finset (Fin n)) (w : Nat) :
    wireVal n C x w = (C.gates.foldl stepWire (inp n x)).getD w false := rfl

private lemma getD_append_left {α : Type _} (l₁ l₂ : List α) (i : Nat) (d : α)
    (hi : i < l₁.length) : (l₁ ++ l₂).getD i d = l₁.getD i d := by
  induction l₁ generalizing i with
  | nil => cases hi
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (Nat.lt_of_succ_lt_succ hi)

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

private lemma wireVal_inp_mono (n : Nat) (C : Circuit) {u v : Finset (Fin n)} (huv : u ⊆ v)
    (w : Nat) (hw : w < n + 2) (huw : wireVal n C u w = true) :
    wireVal n C v w = true := by
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

private noncomputable def rankAt (n : Nat) (C : Circuit) (x : Finset (Fin n)) : Nat → Nat
  | 0 => 0
  | m + 1 =>
    if isNotGateList C.gates m then
      2 * rankAt n C x m + if wireVal n C x (n + 2 + m) then 0 else 1
    else
      rankAt n C x m

private lemma ite_bool_eq_of_eq {b₁ b₂ : Bool} (hb : b₁ = b₂)
    (inst : Decidable (b₁ = true)) (x y : Nat) :
    @ite Nat (b₁ = true) inst x y = if b₂ then x else y := by
  subst hb
  cases b₁ <;> simp

private lemma filter_congr_dec {α : Type _} (s : Finset α) (p : α → Prop)
    (d₁ d₂ : DecidablePred p) :
    @Finset.filter α p d₁ s = @Finset.filter α p d₂ s := by
  ext a
  simp

private lemma rankAt_eq_foldl_range (n : Nat) (C : Circuit) (x : Finset (Fin n))
    (inst : ∀ z, Decidable ((C.gates.getD z ⟨GateOp.or, []⟩).op = GateOp.not)) :
    ∀ m ≤ C.gates.length,
      rankAt n C x m =
        ((List.range m).filter (fun z =>
          @decide ((C.gates.getD z ⟨GateOp.or, []⟩).op = GateOp.not) (inst z))).foldl
          (fun v z => 2 * v + (if wireVal n C x (n + 2 + z) then 0 else 1)) 0 := by
  intro m
  induction m with
  | zero =>
    intro _
    simp [rankAt]
  | succ m ih =>
    intro hm1
    have hm : m < C.gates.length := Nat.lt_of_succ_le hm1
    rw [List.range_succ, List.filter_append]
    have hdec : @decide ((C.gates.getD m ⟨GateOp.or, []⟩).op = GateOp.not) (inst m) =
        isNotGateList C.gates m := by
      rw [decide_eq_not]
      rw [getD_eq_getElem C.gates m _ hm]
      simp [isNotGateList, hm]
    have hih := ih (Nat.le_of_lt hm)
    simp only [rankAt]
    cases hnot : isNotGateList C.gates m
    · have hf : [m].filter (fun z =>
          @decide ((C.gates.getD z ⟨GateOp.or, []⟩).op = GateOp.not) (inst z)) = [] := by
        simp [hdec, hnot]
      rw [hf, List.append_nil]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact hih
    · have hf : [m].filter (fun z =>
          @decide ((C.gates.getD z ⟨GateOp.or, []⟩).op = GateOp.not) (inst z)) = [m] := by
        simp [hdec, hnot]
      rw [hf, List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only [↓reduceIte]
      rw [hih]

private lemma rankAt_lt_pow (n : Nat) (C : Circuit) (x : Finset (Fin n)) (m : Nat) :
    rankAt n C x m < 2 ^ B_cntList C.gates m := by
  induction m with
  | zero =>
    simp [rankAt, B_cntList]
  | succ m ih =>
    simp only [rankAt, B_cntList]
    cases h : isNotGateList C.gates m
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact ih
    · simp only [↓reduceIte]
      rw [Nat.pow_succ]
      cases wireVal n C x (n + 2 + m) <;> simp <;> omega

private lemma rankAt_eq_imp_not_eq (n : Nat) (C : Circuit) (x y : Finset (Fin n)) :
    ∀ m, rankAt n C x m = rankAt n C y m →
      ∀ z < m, isNotGateList C.gates z = true →
        wireVal n C x (n + 2 + z) = wireVal n C y (n + 2 + z) := by
  intro m
  induction m with
  | zero =>
    intro _ z hz
    omega
  | succ m ih =>
    intro heq z hz hnotz
    simp only [rankAt] at heq
    cases hnotm : isNotGateList C.gates m
    · simp only [hnotm, Bool.false_eq_true, ↓reduceIte] at heq
      have hzm : z < m := by
        by_cases hzm' : z = m
        · subst hzm'; rw [hnotm] at hnotz; cases hnotz
        · omega
      exact ih heq z hzm hnotz
    · simp only [hnotm, ↓reduceIte] at heq
      have hpair : rankAt n C x m = rankAt n C y m ∧
          wireVal n C x (n + 2 + m) = wireVal n C y (n + 2 + m) := by
        cases hx : wireVal n C x (n + 2 + m) <;> cases hy : wireVal n C y (n + 2 + m) <;>
          simp only [hx, hy, Bool.false_eq_true, ↓reduceIte] at heq
        · exact ⟨by omega, rfl⟩
        · omega
        · omega
        · exact ⟨by omega, rfl⟩
      by_cases hzm : z = m
      · subst hzm; exact hpair.2
      · exact ih hpair.1 z (by omega) hnotz

private lemma rankAt_mono_and_wires (n : Nat) (C : Circuit)
    (hFan : PEqualNP.MetaComplexity.FanInTwo C)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    {u v : Finset (Fin n)} (huv : u ⊆ v) :
    ∀ m ≤ C.gates.length,
      rankAt n C u m ≤ rankAt n C v m ∧
      (rankAt n C u m = rankAt n C v m →
        ∀ w < n + 2 + m, wireVal n C u w = true → wireVal n C v w = true) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨Nat.le_refl _, ?_⟩
    intro _ w hw huw
    exact wireVal_inp_mono n C huv w hw huw
  | succ m ih =>
    intro hm1
    have hm : m < C.gates.length := Nat.lt_of_succ_le hm1
    obtain ⟨ihLe, ihMono⟩ := ih (Nat.le_of_lt hm)
    have hgate_mem : C.gates[m] ∈ C.gates := List.getElem_mem hm
    have hgate_op := (hFan C.gates[m] hgate_mem).1
    have hrb_m : ∀ i ∈ C.gates[m].inputs, i < n + 2 + m := by
      intro i hi
      have h1 := hRB m hm i
      unfold PEqualNP.MetaComplexity.NestedCover.gateAt at h1
      rw [getD_eq_getElem C.gates m _ hm] at h1
      exact h1 hi
    have heval_u := wireVal_eval_at_gate n C hRB u m hm
    have heval_v := wireVal_eval_at_gate n C hRB v m hm
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate_op
    rcases hgate_op with hop | hop | hop
    · have hnot : isNotGateList C.gates m = false := by
        simp [isNotGateList, hm, hop, isNotOp]
      simp only [rankAt, hnot, Bool.false_eq_true, ↓reduceIte]
      refine ⟨ihLe, ?_⟩
      intro hreq w hw huw
      by_cases hwm : w < n + 2 + m
      · exact ihMono hreq w hwm huw
      · have hweq : w = n + 2 + m := by omega
        subst hweq
        rw [heval_u, hop, GateOp.eval] at huw
        rw [heval_v, hop, GateOp.eval]
        exact all_id_mono C.gates[m].inputs (wireVal n C u) (wireVal n C v)
          (fun i hi => ihMono hreq i (hrb_m i hi)) huw
    · have hnot : isNotGateList C.gates m = false := by
        simp [isNotGateList, hm, hop, isNotOp]
      simp only [rankAt, hnot, Bool.false_eq_true, ↓reduceIte]
      refine ⟨ihLe, ?_⟩
      intro hreq w hw huw
      by_cases hwm : w < n + 2 + m
      · exact ihMono hreq w hwm huw
      · have hweq : w = n + 2 + m := by omega
        subst hweq
        rw [heval_u, hop, GateOp.eval] at huw
        rw [heval_v, hop, GateOp.eval]
        exact any_id_mono C.gates[m].inputs (wireVal n C u) (wireVal n C v)
          (fun i hi => ihMono hreq i (hrb_m i hi)) huw
    · have hnot : isNotGateList C.gates m = true := by
        simp [isNotGateList, hm, hop, isNotOp]
      simp only [rankAt, hnot, ↓reduceIte]
      by_cases hlt : rankAt n C u m < rankAt n C v m
      · constructor
        · cases wireVal n C u (n + 2 + m) <;> cases wireVal n C v (n + 2 + m) <;>
            simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
        · intro heq
          exfalso
          cases hu : wireVal n C u (n + 2 + m) <;> cases hv : wireVal n C v (n + 2 + m) <;>
            simp only [hu, hv, Bool.false_eq_true, ↓reduceIte] at heq <;> omega
      · have hreq : rankAt n C u m = rankAt n C v m := by omega
        have hbit : wireVal n C v (n + 2 + m) = true → wireVal n C u (n + 2 + m) = true := by
          intro hvtrue
          rw [heval_v, hop, GateOp.eval] at hvtrue
          rw [heval_u, hop, GateOp.eval]
          cases hins : C.gates[m].inputs with
          | nil => simp
          | cons i0 rest =>
            simp only [hins, List.map_cons, List.headD_cons] at hvtrue ⊢
            cases hvi0 : wireVal n C v i0
            · cases hui0 : wireVal n C u i0
              · rfl
              · have hi0 : i0 < n + 2 + m := hrb_m i0 (by simp [hins])
                have hcontr := ihMono hreq i0 hi0 hui0
                rw [hvi0] at hcontr
                cases hcontr
            · rw [hvi0] at hvtrue
              cases hvtrue
        constructor
        · cases hv1 : wireVal n C v (n + 2 + m)
          · cases hu1 : wireVal n C u (n + 2 + m) <;> simp <;> omega
          · have hu1 := hbit hv1
            rw [hu1]
            simp [hreq]
        · intro hreq1 w hw huw
          by_cases hwm : w < n + 2 + m
          · exact ihMono hreq w hwm huw
          · have hweq : w = n + 2 + m := by omega
            subst hweq
            rw [huw] at hreq1
            cases hv1 : wireVal n C v (n + 2 + m)
            · rw [hv1] at hreq1
              simp at hreq1
              omega
            · rfl

private lemma strict_interval_card_add_lo_le_hi {k : Nat} (lo hi : Fin k → Nat)
    (horder : ∀ i j : Fin k, i < j → hi i ≤ lo j)
    (hle : ∀ i : Fin k, lo i ≤ hi i) :
    ∀ c : Nat, ∀ T : Finset (Fin k), T.card = c →
      (hT : T.Nonempty) → (∀ i ∈ T, lo i < hi i) →
      T.card + lo (T.min' hT) ≤ hi (T.max' hT) := by
  have hlo_mono : ∀ i j : Fin k, i ≤ j → lo i ≤ lo j := by
    intro i j hij
    rcases lt_or_eq_of_le hij with h | rfl
    · exact Nat.le_trans (hle i) (horder i j h)
    · exact Nat.le_refl _
  intro c
  induction c with
  | zero =>
    intro T hcard hT _
    have hpos := Finset.Nonempty.card_pos hT
    omega
  | succ c ih =>
    intro T hcard hT hstrict
    set imax := T.max' hT
    have himax_mem : imax ∈ T := Finset.max'_mem T hT
    have himax_strict : lo imax < hi imax := hstrict imax himax_mem
    by_cases hc0 : c = 0
    · have hmin_le : T.min' hT ≤ imax := Finset.min'_le_max' T hT
      have hlo_le : lo (T.min' hT) ≤ lo imax := hlo_mono _ _ hmin_le
      omega
    · set T' := T.erase imax
      have hT'_card : T'.card = c := by
        have h1 : T'.card = T.card - 1 := Finset.card_erase_of_mem himax_mem
        omega
      have hT' : T'.Nonempty := Finset.card_pos.mp (by omega)
      have hT'_strict : ∀ i ∈ T', lo i < hi i := fun i hi' =>
        hstrict i (Finset.mem_of_mem_erase hi')
      have hih := ih T' hT'_card hT' hT'_strict
      set jmax := T'.max' hT'
      have hjmax_mem' : jmax ∈ T' := Finset.max'_mem T' hT'
      have hjmax_ne : jmax ≠ imax := (Finset.mem_erase.mp hjmax_mem').1
      have hjmax_mem : jmax ∈ T := (Finset.mem_erase.mp hjmax_mem').2
      have hjmax_lt : jmax < imax := lt_of_le_of_ne (Finset.le_max' T jmax hjmax_mem) hjmax_ne
      have hhi_le : hi jmax ≤ lo imax := horder jmax imax hjmax_lt
      have hmin'_mem : T'.min' hT' ∈ T := Finset.mem_of_mem_erase (Finset.min'_mem T' hT')
      have hmin_le : T.min' hT ≤ T'.min' hT' := Finset.min'_le T _ hmin'_mem
      have hlo_le : lo (T.min' hT) ≤ lo (T'.min' hT') := hlo_mono _ _ hmin_le
      omega

private lemma strict_interval_card_le {k B : Nat} (lo hi : Fin k → Nat)
    (d : DecidablePred (fun i : Fin k => lo i < hi i))
    (horder : ∀ i j : Fin k, i < j → hi i ≤ lo j)
    (hle : ∀ i : Fin k, lo i ≤ hi i)
    (hlt : ∀ i : Fin k, hi i < B) :
    (@Finset.filter (Fin k) (fun i : Fin k => lo i < hi i) d Finset.univ).card ≤ B - 1 := by
  set T := @Finset.filter (Fin k) (fun i : Fin k => lo i < hi i) d Finset.univ
  by_cases hT : T.Nonempty
  · have hstrict : ∀ i ∈ T, lo i < hi i := fun i hi => (Finset.mem_filter.mp hi).2
    have hbound := strict_interval_card_add_lo_le_hi lo hi horder hle T.card T rfl hT hstrict
    have hlt_max := hlt (T.max' hT)
    omega
  · have hemp : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    rw [hemp, Finset.card_empty]
    exact Nat.zero_le _

private lemma monotone2_imp_fanInTwo {C : Circuit}
    (hM : PEqualNP.MetaComplexity.Monotone2 C) : PEqualNP.MetaComplexity.FanInTwo C := by
  intro g hg
  obtain ⟨hop, hlen⟩ := hM g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
  refine ⟨?_, hlen⟩
  rcases hop with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

private lemma mono_circuit_wires (n : Nat) (M : Circuit)
    (hMono : PEqualNP.MetaComplexity.Monotone2 M)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) M)
    {u v : Finset (Fin n)} (huv : u ⊆ v) :
    ∀ m ≤ M.gates.length, ∀ w < n + 2 + m,
      wireVal n M u w = true → wireVal n M v w = true := by
  intro m
  induction m with
  | zero =>
    intro _ w hw huw
    exact wireVal_inp_mono n M huv w hw huw
  | succ m ih =>
    intro hm1 w hw huw
    have hm : m < M.gates.length := Nat.lt_of_succ_le hm1
    by_cases hwm : w < n + 2 + m
    · exact ih (Nat.le_of_lt hm) w hwm huw
    · have hweq : w = n + 2 + m := by omega
      subst hweq
      have hrb_m : ∀ i ∈ M.gates[m].inputs, i < n + 2 + m := by
        intro i hi
        have h1 := hRB m hm i
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt at h1
        rw [getD_eq_getElem M.gates m _ hm] at h1
        exact h1 hi
      have hgate_op := (hMono M.gates[m] (List.getElem_mem hm)).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate_op
      rw [wireVal_eval_at_gate n M hRB u m hm] at huw
      rw [wireVal_eval_at_gate n M hRB v m hm]
      rcases hgate_op with hop | hop
      · rw [hop, GateOp.eval] at huw ⊢
        exact all_id_mono M.gates[m].inputs (wireVal n M u) (wireVal n M v)
          (fun i hi => ih (Nat.le_of_lt hm) i (hrb_m i hi)) huw
      · rw [hop, GateOp.eval] at huw ⊢
        exact any_id_mono M.gates[m].inputs (wireVal n M u) (wireVal n M v)
          (fun i hi => ih (Nat.le_of_lt hm) i (hrb_m i hi)) huw

private noncomputable def freezeStep (n : Nat) (C : Circuit) (x0 : Finset (Fin n)) :
    Nat → List Gate × (Nat → Nat)
  | 0 => ([], id)
  | m + 1 =>
    let prev := freezeStep n C x0 m
    let mg := prev.1
    let mp := prev.2
    if hm : m < C.gates.length then
      if isNotGateList C.gates m then
        (mg, fun w => if w = n + 2 + m then
          (if wireVal n C x0 (n + 2 + m) then n + 1 else n) else mp w)
      else
        (mg ++ [⟨C.gates[m].op, C.gates[m].inputs.map mp⟩],
          fun w => if w = n + 2 + m then n + 2 + mg.length else mp w)
    else prev

private lemma freezeStep_spec (n : Nat) (C : Circuit) (x0 : Finset (Fin n))
    (hFan : PEqualNP.MetaComplexity.FanInTwo C)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C) :
    ∀ m ≤ C.gates.length,
      let mg := (freezeStep n C x0 m).1
      let mp := (freezeStep n C x0 m).2
      PEqualNP.MetaComplexity.Monotone2 ⟨mg, 0⟩ ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨mg, 0⟩ ∧
      (∀ w < n + 2 + m, mp w < n + 2 + mg.length) ∧
      mg.length + B_cntList C.gates m = m ∧
      (∀ x : Finset (Fin n),
        (∀ z < m, isNotGateList C.gates z = true →
          wireVal n C x (n + 2 + z) = wireVal n C x0 (n + 2 + z)) →
        ∀ w < n + 2 + m,
          (mg.foldl stepWire (inp n x)).getD (mp w) false = wireVal n C x w) := by
  intro m
  induction m with
  | zero =>
    intro _
    simp only [freezeStep, B_cntList, List.length_nil, Nat.add_zero, List.foldl_nil, id_eq]
    refine ⟨?_, ?_, ?_, trivial, ?_⟩
    · intro g hg; cases hg
    · intro j hj; cases hj
    · intro w hw; exact hw
    · intro x _ w hw
      rw [wireVal_eq_foldl]
      have hlen : w < (inp n x).length := by rw [length_inp]; exact hw
      rw [getD_foldl_stepWire_of_lt C.gates (inp n x) w hlen]
  | succ m ih =>
    intro hm1
    have hm : m < C.gates.length := Nat.lt_of_succ_le hm1
    obtain ⟨ihMono, ihRB, ihLt, ihLen, ihWire⟩ := ih (Nat.le_of_lt hm)
    set mg := (freezeStep n C x0 m).1 with hmg_def
    set mp := (freezeStep n C x0 m).2 with hmp_def
    have hstep : freezeStep n C x0 (m + 1) =
        if isNotGateList C.gates m then
          (mg, fun w => if w = n + 2 + m then
            (if wireVal n C x0 (n + 2 + m) then n + 1 else n) else mp w)
        else
          (mg ++ [⟨C.gates[m].op, C.gates[m].inputs.map mp⟩],
            fun w => if w = n + 2 + m then n + 2 + mg.length else mp w) := by
      simp only [freezeStep, hm, ↓reduceDIte, hmg_def, hmp_def]
    cases hnot : isNotGateList C.gates m
    · rw [hstep, if_neg (by rw [hnot]; exact Bool.false_ne_true)]
      dsimp only
      set g' : Gate := ⟨C.gates[m].op, C.gates[m].inputs.map mp⟩
      have hrb_m : ∀ i ∈ C.gates[m].inputs, i < n + 2 + m := by
        intro i hi
        have h1 := hRB m hm i
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt at h1
        rw [getD_eq_getElem C.gates m _ hm] at h1
        exact h1 hi
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | hg
        · exact ihMono g hg
        · subst hg
          have hgm := hFan C.gates[m] (List.getElem_mem hm)
          refine ⟨?_, by simp [g', hgm.2]⟩
          have hop := hgm.1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
          rcases hop with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso
            have hcontr : isNotGateList C.gates m = true := by
              simp [isNotGateList, hm, h, isNotOp]
            rw [hnot] at hcontr
            cases hcontr
      · intro j hj i hi
        simp only [List.length_append, List.length_singleton] at hj
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
        by_cases hjd : j < mg.length
        · rw [getD_append_left mg [g'] j _ hjd] at hi
          exact ihRB j hjd i hi
        · have hjeq : j = mg.length := by omega
          subst hjeq
          rw [getD_append_right_eq mg g'] at hi
          simp only [g', List.mem_map] at hi
          obtain ⟨i0, hi0, rfl⟩ := hi
          exact ihLt i0 (hrb_m i0 hi0)
      · intro w hw
        simp only [List.length_append, List.length_singleton]
        by_cases hweq : w = n + 2 + m
        · rw [if_pos hweq]; omega
        · rw [if_neg hweq]
          have := ihLt w (by omega)
          omega
      · simp only [List.length_append, List.length_singleton, B_cntList, hnot,
          Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        omega
      · intro x hagree w hw
        have hagree' : ∀ z < m, isNotGateList C.gates z = true →
            wireVal n C x (n + 2 + z) = wireVal n C x0 (n + 2 + z) :=
          fun z hz hnz => hagree z (Nat.lt_succ_of_lt hz) hnz
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        set W := mg.foldl stepWire (inp n x)
        have hWlen : W.length = n + 2 + mg.length := by
          rw [length_foldl_stepWire, length_inp]
        by_cases hweq : w = n + 2 + m
        · subst hweq
          rw [if_pos rfl]
          unfold stepWire
          rw [← hWlen, getD_append_right_eq]
          rw [wireVal_eval_at_gate n C hRB x m hm]
          congr 1
          simp only [g', List.map_map]
          apply map_eq_of_forall
          intro i hi
          exact ihWire x hagree' i (hrb_m i hi)
        · rw [if_neg hweq]
          unfold stepWire
          have hlt : mp w < W.length := by
            rw [hWlen]
            exact ihLt w (by omega)
          rw [getD_append_left W _ (mp w) false hlt]
          exact ihWire x hagree' w (by omega)
    · rw [hstep, if_pos hnot]
      dsimp only
      refine ⟨ihMono, ihRB, ?_, ?_, ?_⟩
      · intro w hw
        by_cases hweq : w = n + 2 + m
        · rw [if_pos hweq]
          cases wireVal n C x0 (n + 2 + m) <;> simp <;> omega
        · rw [if_neg hweq]
          exact ihLt w (by omega)
      · simp only [B_cntList, hnot, ↓reduceIte]
        omega
      · intro x hagree w hw
        by_cases hweq : w = n + 2 + m
        · subst hweq
          rw [if_pos rfl]
          rw [hagree m (Nat.lt_succ_self m) hnot]
          cases hval : wireVal n C x0 (n + 2 + m)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            have hlen : n < (inp n x).length := by rw [length_inp]; omega
            rw [getD_foldl_stepWire_of_lt mg (inp n x) n hlen, getD_inp_n]
          · simp only [↓reduceIte]
            have hlen : n + 1 < (inp n x).length := by rw [length_inp]; omega
            rw [getD_foldl_stepWire_of_lt mg (inp n x) (n + 1) hlen, getD_inp_n1]
        · rw [if_neg hweq]
          exact ihWire x (fun z hz hnz => hagree z (Nat.lt_succ_of_lt hz) hnz) w (by omega)

private noncomputable def freezeNots (n : Nat) (C : Circuit) (x0 : Finset (Fin n)) : Circuit :=
  ⟨(freezeStep n C x0 C.gates.length).1, 0⟩

private noncomputable def freezeMap (n : Nat) (C : Circuit) (x0 : Finset (Fin n)) : Nat → Nat :=
  (freezeStep n C x0 C.gates.length).2

private def variesOn (n : Nat) (M : Circuit) (S : Finset (Finset (Fin n))) (q : Nat) : Prop :=
  ∃ x ∈ S, ∃ y ∈ S, wireVal n M x (n + 2 + q) = false ∧ wireVal n M y (n + 2 + q) = true

private lemma const_of_not_variesOn (n : Nat) (M : Circuit) (S : Finset (Finset (Fin n)))
    (q : Nat) (hnv : ¬ variesOn n M S q) {x0 x : Finset (Fin n)} (hx0 : x0 ∈ S) (hx : x ∈ S) :
    wireVal n M x (n + 2 + q) = wireVal n M x0 (n + 2 + q) := by
  cases hvx : wireVal n M x (n + 2 + q) <;> cases hvx0 : wireVal n M x0 (n + 2 + q)
  · rfl
  · exact False.elim (hnv ⟨x, hx, x0, hx0, hvx, hvx0⟩)
  · exact False.elim (hnv ⟨x0, hx0, x, hx, hvx0, hvx⟩)
  · rfl

private noncomputable def pruneStep (n : Nat) (M : Circuit) (S : Finset (Finset (Fin n)))
    (x0 : Finset (Fin n)) : Nat → List Gate × (Nat → Nat)
  | 0 => ([], id)
  | q + 1 =>
    let prev := pruneStep n M S x0 q
    let dg := prev.1
    let dmp := prev.2
    if hq : q < M.gates.length then
      if @decide (variesOn n M S q) (Classical.propDecidable _) then
        (dg ++ [⟨M.gates[q].op, M.gates[q].inputs.map dmp⟩],
          fun w => if w = n + 2 + q then n + 2 + dg.length else dmp w)
      else
        (dg, fun w => if w = n + 2 + q then
          (if wireVal n M x0 (n + 2 + q) then n + 1 else n) else dmp w)
    else prev

private lemma card_filter_range_succ (q : Nat) (f : Nat → Bool) :
    ((Finset.range (q + 1)).filter (fun r => f r = true)).card =
      ((Finset.range q).filter (fun r => f r = true)).card + if f q = true then 1 else 0 := by
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases hfq : f q = true
  · rw [if_pos hfq, if_pos hfq]
    have hnotmem : q ∉ (Finset.range q).filter (fun r => f r = true) := by
      simp [Finset.mem_filter, Finset.mem_range]
    rw [Finset.card_insert_of_notMem hnotmem]
  · rw [if_neg hfq, if_neg hfq, Nat.add_zero]

private lemma pruneStep_spec (n : Nat) (M : Circuit) (S : Finset (Finset (Fin n)))
    (x0 : Finset (Fin n)) (hx0 : x0 ∈ S)
    (hMono : PEqualNP.MetaComplexity.Monotone2 M)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) M) :
    ∀ q ≤ M.gates.length,
      let dg := (pruneStep n M S x0 q).1
      let dmp := (pruneStep n M S x0 q).2
      PEqualNP.MetaComplexity.Monotone2 ⟨dg, 0⟩ ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨dg, 0⟩ ∧
      (∀ w < n + 2 + q, dmp w < n + 2 + dg.length) ∧
      dg.length = ((Finset.range q).filter (fun r =>
        @decide (variesOn n M S r) (Classical.propDecidable _) = true)).card ∧
      (∀ x ∈ S, ∀ w < n + 2 + q,
        (dg.foldl stepWire (inp n x)).getD (dmp w) false = wireVal n M x w) := by
  intro q
  induction q with
  | zero =>
    intro _
    simp only [pruneStep, List.length_nil, Finset.range_zero, Finset.filter_empty,
      Finset.card_empty, List.foldl_nil, id_eq]
    refine ⟨?_, ?_, ?_, trivial, ?_⟩
    · intro g hg; cases hg
    · intro j hj; cases hj
    · intro w hw; exact hw
    · intro x _ w hw
      rw [wireVal_eq_foldl]
      have hlen : w < (inp n x).length := by rw [length_inp]; exact hw
      rw [getD_foldl_stepWire_of_lt M.gates (inp n x) w hlen]
  | succ q ih =>
    intro hq1
    have hq : q < M.gates.length := Nat.lt_of_succ_le hq1
    obtain ⟨ihMono, ihRB, ihLt, ihLen, ihWire⟩ := ih (Nat.le_of_lt hq)
    set dg := (pruneStep n M S x0 q).1 with hdg_def
    set dmp := (pruneStep n M S x0 q).2 with hdmp_def
    have hstep : pruneStep n M S x0 (q + 1) =
        if @decide (variesOn n M S q) (Classical.propDecidable _) then
          (dg ++ [⟨M.gates[q].op, M.gates[q].inputs.map dmp⟩],
            fun w => if w = n + 2 + q then n + 2 + dg.length else dmp w)
        else
          (dg, fun w => if w = n + 2 + q then
            (if wireVal n M x0 (n + 2 + q) then n + 1 else n) else dmp w) := by
      simp only [pruneStep, hq, ↓reduceDIte, hdg_def, hdmp_def]
    by_cases hvar : variesOn n M S q
    · have hdec : @decide (variesOn n M S q) (Classical.propDecidable _) = true :=
        cdecide_true hvar
      rw [hstep, if_pos hdec]
      dsimp only
      set g' : Gate := ⟨M.gates[q].op, M.gates[q].inputs.map dmp⟩
      have hrb_q : ∀ i ∈ M.gates[q].inputs, i < n + 2 + q := by
        intro i hi
        have h1 := hRB q hq i
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt at h1
        rw [getD_eq_getElem M.gates q _ hq] at h1
        exact h1 hi
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | hg
        · exact ihMono g hg
        · subst hg
          have hgq := hMono M.gates[q] (List.getElem_mem hq)
          exact ⟨hgq.1, by simp [g', hgq.2]⟩
      · intro j hj i hi
        simp only [List.length_append, List.length_singleton] at hj
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hi
        by_cases hjd : j < dg.length
        · rw [getD_append_left dg [g'] j _ hjd] at hi
          exact ihRB j hjd i hi
        · have hjeq : j = dg.length := by omega
          subst hjeq
          rw [getD_append_right_eq dg g'] at hi
          simp only [g', List.mem_map] at hi
          obtain ⟨i0, hi0, rfl⟩ := hi
          exact ihLt i0 (hrb_q i0 hi0)
      · intro w hw
        simp only [List.length_append, List.length_singleton]
        by_cases hweq : w = n + 2 + q
        · rw [if_pos hweq]; omega
        · rw [if_neg hweq]
          have := ihLt w (by omega)
          omega
      · rw [List.length_append, List.length_singleton, ihLen]
        rw [card_filter_range_succ q (fun r => @decide (variesOn n M S r) (Classical.propDecidable _))]
        rw [if_pos hdec]
      · intro x hxS w hw
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        set W := dg.foldl stepWire (inp n x)
        have hWlen : W.length = n + 2 + dg.length := by
          rw [length_foldl_stepWire, length_inp]
        by_cases hweq : w = n + 2 + q
        · subst hweq
          rw [if_pos rfl]
          unfold stepWire
          rw [← hWlen, getD_append_right_eq]
          rw [wireVal_eval_at_gate n M hRB x q hq]
          congr 1
          simp only [g', List.map_map]
          apply map_eq_of_forall
          intro i hi
          exact ihWire x hxS i (hrb_q i hi)
        · rw [if_neg hweq]
          unfold stepWire
          have hlt : dmp w < W.length := by
            rw [hWlen]
            exact ihLt w (by omega)
          rw [getD_append_left W _ (dmp w) false hlt]
          exact ihWire x hxS w (by omega)
    · have hdec : @decide (variesOn n M S q) (Classical.propDecidable _) = false :=
        cdecide_false hvar
      rw [hstep, if_neg (by rw [hdec]; exact Bool.false_ne_true)]
      dsimp only
      refine ⟨ihMono, ihRB, ?_, ?_, ?_⟩
      · intro w hw
        by_cases hweq : w = n + 2 + q
        · rw [if_pos hweq]
          cases wireVal n M x0 (n + 2 + q) <;> simp <;> omega
        · rw [if_neg hweq]
          exact ihLt w (by omega)
      · rw [ihLen]
        rw [card_filter_range_succ q (fun r => @decide (variesOn n M S r) (Classical.propDecidable _))]
        rw [if_neg (by rw [hdec]; exact Bool.false_ne_true), Nat.add_zero]
      · intro x hxS w hw
        by_cases hweq : w = n + 2 + q
        · subst hweq
          rw [if_pos rfl]
          rw [const_of_not_variesOn n M S q hvar hx0 hxS]
          cases hval : wireVal n M x0 (n + 2 + q)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            have hlen : n < (inp n x).length := by rw [length_inp]; omega
            rw [getD_foldl_stepWire_of_lt dg (inp n x) n hlen, getD_inp_n]
          · simp only [↓reduceIte]
            have hlen : n + 1 < (inp n x).length := by rw [length_inp]; omega
            rw [getD_foldl_stepWire_of_lt dg (inp n x) (n + 1) hlen, getD_inp_n1]
        · rw [if_neg hweq]
          exact ihWire x hxS w (by omega)

private lemma not_both_variesOn {n k : Nat} {G : Fin k → Finset (Finset (Fin n))}
    (hord : ∀ i j, i < j → ∀ x ∈ G i, ∀ y ∈ G j, x ⊆ y)
    (M : Circuit) (hMono : PEqualNP.MetaComplexity.Monotone2 M)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) M)
    {i j : Fin k} (hij : i < j) {q : Nat} (hq : q < M.gates.length)
    (hi : variesOn n M (G i) q) (hj : variesOn n M (G j) q) : False := by
  obtain ⟨_, _, y, hyG, _, hyval⟩ := hi
  obtain ⟨x, hxG, _, _, hxval, _⟩ := hj
  have hyx : y ⊆ x := hord i j hij y hyG x hxG
  have hxtrue : wireVal n M x (n + 2 + q) = true :=
    mono_circuit_wires n M hMono hRB hyx M.gates.length (Nat.le_refl _) (n + 2 + q) (by omega) hyval
  rw [hxval] at hxtrue
  cases hxtrue

private lemma sum_card_filter_range_le {k : Nat} (I : Finset (Fin k)) (f : Fin k → Nat → Bool) :
    ∀ p : Nat, (∀ q < p, (I.filter (fun i => f i q = true)).card ≤ 1) →
      I.sum (fun i => ((Finset.range p).filter (fun q => f i q = true)).card) ≤ p := by
  intro p
  induction p with
  | zero =>
    intro _
    simp
  | succ p ih =>
    intro hle
    have hsplit : ∀ i ∈ I,
        ((Finset.range (p + 1)).filter (fun q => f i q = true)).card =
          ((Finset.range p).filter (fun q => f i q = true)).card +
            if f i p = true then 1 else 0 :=
      fun i _ => card_filter_range_succ p (f i)
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    have hih := ih (fun q hq => hle q (Nat.lt_succ_of_lt hq))
    have hlast : I.sum (fun i => if f i p = true then 1 else 0) =
        (I.filter (fun i => f i p = true)).card := by
      rw [Finset.card_filter]
    rw [hlast]
    have hp := hle p (Nat.lt_succ_self p)
    omega

end PEqualNP.Outside.L_lib_1329

theorem PEqualNP.Outside.L_lib_1329 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n k t : Nat) (G : Fin k → Finset (Finset (Fin n)))
  (ok : Fin k → Finset (Fin n) → (Fin t → Bool) → Prop),
  (∀ i j, i < j → ∀ x ∈ G i, ∀ y ∈ G j, x ⊆ y) →
  let valid := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size
  let fits := fun (i : Fin k) (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat) =>
    valid C ∧ (∀ a, tap a < n+2+C.size) ∧ ∀ x ∈ G i,
      let w := C.wires (List.ofFn (fun a : Fin n => decide (a ∈ x)) ++ [false,true])
      ok i x (fun a => w.getD (tap a) false)
  let localFit := fun (i : Fin k) (s : Nat) =>
    ∃ C tap, fits i C tap ∧ PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s
  (∀ i, (G i).Nonempty) →
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin k → Fin t → Nat),
    valid C → (∀ i, fits i C (tap i)) →
    let b := PEqualNP.NotBracket.notCount C
    let p := C.size - b
    let gates := (List.range C.size).filter (fun z => decide
      ((C.gates.getD z ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).op = .not))
    let rank := fun (x : Finset (Fin n)) =>
      let w := C.wires (List.ofFn (fun a : Fin n => decide (a ∈ x)) ++ [false,true])
      gates.foldl (fun v z => 2*v+(if w.getD (n+2+z) false then 0 else 1)) 0
    ∃ lo hi s : Fin k → Nat,
      (∀ i, (∃ x ∈ G i, rank x = lo i) ∧ (∃ y ∈ G i, rank y = hi i) ∧
        ∀ x ∈ G i, lo i ≤ rank x ∧ rank x ≤ hi i) ∧
      (∀ i, lo i ≤ hi i ∧ hi i < 2^b) ∧ (∀ i j, i < j → hi i ≤ lo j) ∧
      (Finset.univ.filter (fun i => lo i < hi i)).card ≤ 2^b - 1 ∧
      (∀ i, lo i = hi i → localFit i (s i)) ∧
      ∀ l : Fin (2^b), ((Finset.univ.filter (fun i => lo i = l.val ∧ hi i = l.val)).sum s) ≤ p) := by
  intro n k t G ok hord valid fits localFit hG C tap hvalid hfits b p gates rank
  obtain ⟨hFan, hRB, _⟩ := hvalid
  have hrank_eq : ∀ x : Finset (Fin n),
      rank x = PEqualNP.Outside.L_lib_1329.rankAt n C x C.gates.length := by
    intro x
    have hfold : rank x = gates.foldl (fun v z =>
        2 * v + (if PEqualNP.Outside.L_lib_1329.wireVal n C x (n + 2 + z) then 0 else 1)) 0 := by
      dsimp only [rank]
      congr 1
      funext v z
      congr 1
      apply PEqualNP.Outside.L_lib_1329.ite_bool_eq_of_eq
      unfold PEqualNP.Outside.L_lib_1329.wireVal
      congr 2
    rw [hfold]
    exact (PEqualNP.Outside.L_lib_1329.rankAt_eq_foldl_range n C x _ C.gates.length (Nat.le_refl _)).symm
  have hb_eq : PEqualNP.Outside.L_lib_1329.B_cntList C.gates C.gates.length = b := by
    rw [PEqualNP.Outside.L_lib_1329.B_cntList_length,
      ← PEqualNP.Outside.L_lib_1329.notCount_eq_filter_isNotOp]
  let R : Fin k → Finset Nat := fun i => (G i).image rank
  have hRne : ∀ i : Fin k, (R i).Nonempty := fun i => (hG i).image rank
  let lo : Fin k → Nat := fun i => (R i).min' (hRne i)
  let hi : Fin k → Nat := fun i => (R i).max' (hRne i)
  have hlo_mem : ∀ i : Fin k, ∃ x ∈ G i, rank x = lo i := by
    intro i
    have hm : lo i ∈ R i := Finset.min'_mem (R i) (hRne i)
    exact Finset.mem_image.mp hm
  have hhi_mem : ∀ i : Fin k, ∃ y ∈ G i, rank y = hi i := by
    intro i
    have hm : hi i ∈ R i := Finset.max'_mem (R i) (hRne i)
    exact Finset.mem_image.mp hm
  have hbounds : ∀ i : Fin k, ∀ x ∈ G i, lo i ≤ rank x ∧ rank x ≤ hi i := by
    intro i x hx
    have hmem : rank x ∈ R i := Finset.mem_image_of_mem rank hx
    exact ⟨Finset.min'_le (R i) (rank x) hmem, Finset.le_max' (R i) (rank x) hmem⟩
  have hle : ∀ i : Fin k, lo i ≤ hi i := fun i => Finset.min'_le_max' (R i) (hRne i)
  have hhi_lt : ∀ i : Fin k, hi i < 2 ^ b := by
    intro i
    obtain ⟨y, _, hy⟩ := hhi_mem i
    rw [← hy, hrank_eq y, ← hb_eq]
    exact PEqualNP.Outside.L_lib_1329.rankAt_lt_pow n C y C.gates.length
  have horder : ∀ i j : Fin k, i < j → hi i ≤ lo j := by
    intro i j hij
    obtain ⟨y, hyG, hy⟩ := hhi_mem i
    obtain ⟨x, hxG, hx⟩ := hlo_mem j
    rw [← hy, ← hx, hrank_eq y, hrank_eq x]
    have hyx : y ⊆ x := hord i j hij y hyG x hxG
    exact (PEqualNP.Outside.L_lib_1329.rankAt_mono_and_wires n C hFan hRB hyx
      C.gates.length (Nat.le_refl _)).1
  have hstrict_card : ∀ d : DecidablePred (fun i : Fin k => lo i < hi i),
      (@Finset.filter (Fin k) (fun i : Fin k => lo i < hi i) d Finset.univ).card ≤ 2 ^ b - 1 :=
    fun d => PEqualNP.Outside.L_lib_1329.strict_interval_card_le lo hi d horder hle hhi_lt
  let ISet : Nat → Finset (Fin k) := fun l => Finset.univ.filter (fun i => lo i = l ∧ hi i = l)
  let xOf : Nat → Finset (Fin n) := fun l =>
    if hl : (ISet l).Nonempty then
      Classical.choose (hG (Classical.choose hl))
    else
      ∅
  let MOf : Nat → PEqualNP.CircuitLowerBounds.Circuit := fun l =>
    PEqualNP.Outside.L_lib_1329.freezeNots n C (xOf l)
  have hMOf_spec : ∀ l : Nat,
      PEqualNP.MetaComplexity.Monotone2 (MOf l) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) (MOf l) ∧
      (MOf l).gates.length = p := by
    intro l
    obtain ⟨hMono, hRBM, _, hLen, _⟩ :=
      PEqualNP.Outside.L_lib_1329.freezeStep_spec n C (xOf l) hFan hRB C.gates.length (Nat.le_refl _)
    refine ⟨hMono, hRBM, ?_⟩
    change (PEqualNP.Outside.L_lib_1329.freezeStep n C (xOf l) C.gates.length).1.length =
      C.gates.length - b
    rw [hb_eq] at hLen
    omega
  let s : Fin k → Nat := fun i =>
    ((Finset.range p).filter (fun q =>
      @decide (PEqualNP.Outside.L_lib_1329.variesOn n (MOf (lo i)) (G i) q)
        (Classical.propDecidable _) = true)).card
  refine ⟨lo, hi, s, ?_, ?_, horder, hstrict_card _, ?_, ?_⟩
  · intro i
    exact ⟨hlo_mem i, hhi_mem i, hbounds i⟩
  · intro i
    exact ⟨hle i, hhi_lt i⟩
  · intro i heq
    set l := lo i
    have hi_mem_I : i ∈ ISet l := by
      simp [ISet, l, heq]
    have hIne : (ISet l).Nonempty := ⟨i, hi_mem_I⟩
    have hxOf_rank : PEqualNP.Outside.L_lib_1329.rankAt n C (xOf l) C.gates.length = l := by
      have hxl : xOf l = Classical.choose (hG (Classical.choose hIne)) := by
        simp [xOf, hIne]
      have h_il : Classical.choose hIne ∈ ISet l := Classical.choose_spec hIne
      have h_il_eq : lo (Classical.choose hIne) = l ∧ hi (Classical.choose hIne) = l :=
        (Finset.mem_filter.mp h_il).2
      have h_x_mem : xOf l ∈ G (Classical.choose hIne) := by
        rw [hxl]
        exact Classical.choose_spec (hG (Classical.choose hIne))
      have hbnd := hbounds (Classical.choose hIne) (xOf l) h_x_mem
      rw [h_il_eq.1, h_il_eq.2, hrank_eq (xOf l)] at hbnd
      omega
    obtain ⟨hMonoM, hRBM, hLtM, hLenM, hWireM⟩ :=
      PEqualNP.Outside.L_lib_1329.freezeStep_spec n C (xOf l) hFan hRB C.gates.length (Nat.le_refl _)
    have hMsize : (MOf l).gates.length = p := (hMOf_spec l).2.2
    set xBase := Classical.choose (hG i)
    have hxBase : xBase ∈ G i := Classical.choose_spec (hG i)
    obtain ⟨hMonoD, hRBD, hLtD, hLenD, hWireD⟩ :=
      PEqualNP.Outside.L_lib_1329.pruneStep_spec n (MOf l) (G i) xBase hxBase hMonoM hRBM
        (MOf l).gates.length (Nat.le_refl _)
    set D : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨(PEqualNP.Outside.L_lib_1329.pruneStep n (MOf l) (G i) xBase (MOf l).gates.length).1, 0⟩
    set dmp := (PEqualNP.Outside.L_lib_1329.pruneStep n (MOf l) (G i) xBase (MOf l).gates.length).2
    set mp := PEqualNP.Outside.L_lib_1329.freezeMap n C (xOf l)
    set tapD : Fin t → Nat := fun a => dmp (mp (tap i a))
    have hfit_i := hfits i
    obtain ⟨_, htap_lt, hok_i⟩ := hfit_i
    refine ⟨D, tapD, ⟨⟨PEqualNP.Outside.L_lib_1329.monotone2_imp_fanInTwo hMonoD, hRBD, ?_⟩, ?_, ?_⟩,
      hMonoD, ?_⟩
    · show (0 : Nat) < n + 2 + D.gates.length
      omega
    · intro a
      have ha1 : tap i a < n + 2 + C.gates.length := htap_lt a
      have ha2 : mp (tap i a) < n + 2 + (MOf l).gates.length := hLtM (tap i a) ha1
      exact hLtD (mp (tap i a)) ha2
    · intro x hxG
      have hokx := hok_i x hxG
      have hrank_x : PEqualNP.Outside.L_lib_1329.rankAt n C x C.gates.length =
          PEqualNP.Outside.L_lib_1329.rankAt n C (xOf l) C.gates.length := by
        have hbnd := hbounds i x hxG
        rw [← heq] at hbnd
        rw [← hrank_eq x, hxOf_rank]
        omega
      have hagree : ∀ z < C.gates.length,
          PEqualNP.Outside.L_lib_1329.isNotGateList C.gates z = true →
          PEqualNP.Outside.L_lib_1329.wireVal n C x (n + 2 + z) =
            PEqualNP.Outside.L_lib_1329.wireVal n C (xOf l) (n + 2 + z) :=
        PEqualNP.Outside.L_lib_1329.rankAt_eq_imp_not_eq n C x (xOf l) C.gates.length hrank_x
      dsimp only at hokx ⊢
      refine Eq.mp (congrArg (ok i x) ?_) hokx
      funext a
      have ha1 : tap i a < n + 2 + C.gates.length := htap_lt a
      have ha2 : mp (tap i a) < n + 2 + (MOf l).gates.length := hLtM (tap i a) ha1
      have h1 : (D.wires (PEqualNP.Outside.L_lib_1329.inp n x)).getD (tapD a) false =
          PEqualNP.Outside.L_lib_1329.wireVal n (MOf l) x (mp (tap i a)) :=
        hWireD x hxG (mp (tap i a)) ha2
      have h2 : PEqualNP.Outside.L_lib_1329.wireVal n (MOf l) x (mp (tap i a)) =
          PEqualNP.Outside.L_lib_1329.wireVal n C x (tap i a) :=
        hWireM x hagree (tap i a) ha1
      have h3 : (C.wires (PEqualNP.Outside.L_lib_1329.inp n x)).getD (tap i a) false =
          (D.wires (PEqualNP.Outside.L_lib_1329.inp n x)).getD (tapD a) false := by
        rw [h1, h2]
        rfl
      refine Eq.trans ?_ (Eq.trans h3 ?_)
      · apply congrArg (fun l => (C.wires l).getD (tap i a) false)
        apply PEqualNP.Outside.L_lib_1329.inp_eq_ofFn
      · apply Eq.symm
        apply congrArg (fun l => (D.wires l).getD (tapD a) false)
        apply PEqualNP.Outside.L_lib_1329.inp_eq_ofFn
    · show D.gates.length ≤ s i
      rw [hLenD, hMsize]
  · intro l
    rw [PEqualNP.Outside.L_lib_1329.filter_congr_dec Finset.univ
      (fun i : Fin k => lo i = l.val ∧ hi i = l.val) _ (fun i => inferInstance)]
    set I := Finset.univ.filter (fun i : Fin k => lo i = l.val ∧ hi i = l.val)
    obtain ⟨hMonoM, hRBM, hMsize⟩ := hMOf_spec l.val
    have hsum_eq : I.sum s = I.sum (fun i =>
        ((Finset.range p).filter (fun q =>
          @decide (PEqualNP.Outside.L_lib_1329.variesOn n (MOf l.val) (G i) q)
            (Classical.propDecidable _) = true)).card) := by
      apply Finset.sum_congr rfl
      intro i hiI
      have hloi : lo i = l.val := (Finset.mem_filter.mp hiI).2.1
      dsimp only [s]
      rw [hloi]
    rw [hsum_eq]
    apply PEqualNP.Outside.L_lib_1329.sum_card_filter_range_le I
      (fun i q => @decide (PEqualNP.Outside.L_lib_1329.variesOn n (MOf l.val) (G i) q)
        (Classical.propDecidable _)) p
    intro q hq
    rw [Finset.card_le_one]
    intro i hiI j hjI
    by_contra hij
    have hiV : PEqualNP.Outside.L_lib_1329.variesOn n (MOf l.val) (G i) q :=
      PEqualNP.Outside.L_lib_1329.of_cdecide_true (Finset.mem_filter.mp hiI).2
    have hjV : PEqualNP.Outside.L_lib_1329.variesOn n (MOf l.val) (G j) q :=
      PEqualNP.Outside.L_lib_1329.of_cdecide_true (Finset.mem_filter.mp hjI).2
    have hqM : q < (MOf l.val).gates.length := by omega
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact PEqualNP.Outside.L_lib_1329.not_both_variesOn hord (MOf l.val) hMonoM hRBM hlt hqM hiV hjV
    · exact PEqualNP.Outside.L_lib_1329.not_both_variesOn hord (MOf l.val) hMonoM hRBM hgt hqM hjV hiV
