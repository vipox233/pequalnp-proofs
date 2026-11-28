import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1283

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

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private noncomputable def inp (n : Nat) (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun j : Fin n => @decide (j ∈ x) (Classical.propDecidable _)) ++ [false, true]

private noncomputable def wireVal (n : Nat) (C : Circuit) (x : Finset (Fin n)) (w : Nat) : Bool :=
  (C.wires (inp n x)).getD w false

private lemma wireVal_eq_foldl (n : Nat) (C : Circuit) (x : Finset (Fin n)) (w : Nat) :
    wireVal n C x w = (C.gates.foldl stepWire (inp n x)).getD w false := rfl

private lemma wireVal_congr_set {n : Nat} {C : Circuit} {y z : Finset (Fin n)} {w : Nat}
    (h : ∀ j : Fin n, j ∈ y ↔ j ∈ z) : wireVal n C y w = wireVal n C z w := by
  have hyz : y = z := Finset.ext h
  rw [hyz]

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

private lemma B_cntList_mono (gs : List Gate) {k m : Nat} (hkm : k ≤ m) :
    B_cntList gs k ≤ B_cntList gs m := by
  induction hkm with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    simp only [B_cntList]
    omega

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

private lemma V_div_pow_aux (n : Nat) (C : Circuit) (x : Finset (Fin n)) (k m : Nat) (hkm : k ≤ m) :
    V n C x m / 2 ^ (B_cntList C.gates m - B_cntList C.gates k) = V n C x k := by
  induction hkm with
  | refl =>
    simp
  | @step m hkm ih =>
    simp only [V, B_cntList]
    cases hnot : isNotGateList C.gates m
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact ih
    · simp only [↓reduceIte]
      have hbm : B_cntList C.gates k ≤ B_cntList C.gates m := B_cntList_mono C.gates hkm
      have hsub : B_cntList C.gates m + 1 - B_cntList C.gates k =
          (B_cntList C.gates m - B_cntList C.gates k) + 1 := by omega
      rw [hsub, Nat.pow_succ, Nat.mul_comm (2 ^ (B_cntList C.gates m - B_cntList C.gates k)) 2,
        ← Nat.div_div_eq_div_mul]
      have hdiv2 : (2 * V n C x m + if wireVal n C x (n + 2 + m) then 1 else 0) / 2 = V n C x m := by
        cases wireVal n C x (n + 2 + m) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
      rw [hdiv2]
      exact ih

private lemma div_eq_of_bounds {v q P : Nat} (hP : 0 < P) (h1 : q * P ≤ v) (h2 : v < (q + 1) * P) :
    v / P = q := by
  have hge : q ≤ v / P := (Nat.le_div_iff_mul_le hP).mpr h1
  have hlt : v / P < q + 1 := (Nat.div_lt_iff_lt_mul hP).mpr h2
  omega

private lemma V_eq_of_div_eq (n : Nat) (C : Circuit) (y l : Finset (Fin n)) (s m : Nat)
    (hm : m ≤ C.gates.length)
    (hs : s ≤ B_cntList C.gates C.gates.length - B_cntList C.gates m)
    (hdiv : V n C y C.gates.length / 2 ^ s = V n C l C.gates.length / 2 ^ s) :
    V n C y m = V n C l m := by
  rw [← V_div_pow_aux n C y m C.gates.length hm, ← V_div_pow_aux n C l m C.gates.length hm]
  have hsplit : B_cntList C.gates C.gates.length - B_cntList C.gates m =
      s + (B_cntList C.gates C.gates.length - B_cntList C.gates m - s) := by omega
  rw [hsplit, Nat.pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hdiv]

private lemma wireVal_const_of_div_eq (n : Nat) (C : Circuit) (y l : Finset (Fin n)) (s k : Nat)
    (hk : k < C.gates.length)
    (hnot : isNotGateList C.gates k = true)
    (hbk : B_cntList C.gates k < B_cntList C.gates C.gates.length - s)
    (hdiv : V n C y C.gates.length / 2 ^ s = V n C l C.gates.length / 2 ^ s) :
    wireVal n C y (n + 2 + k) = wireVal n C l (n + 2 + k) := by
  have hsk1 : s ≤ B_cntList C.gates C.gates.length - B_cntList C.gates (k + 1) := by
    simp only [B_cntList, hnot, ↓reduceIte]
    omega
  have hsk : s ≤ B_cntList C.gates C.gates.length - B_cntList C.gates k := by omega
  have hvk := V_eq_of_div_eq n C y l s k (Nat.le_of_lt hk) hsk hdiv
  have hvk1 := V_eq_of_div_eq n C y l s (k + 1) hk hsk1 hdiv
  simp only [V, hnot, ↓reduceIte] at hvk1
  rw [hvk] at hvk1
  cases hy : wireVal n C y (n + 2 + k) <;> cases hl : wireVal n C l (n + 2 + k) <;>
    simp [hy, hl] at hvk1 ⊢

private noncomputable def tBase (n : Nat) (l u : Finset (Fin n)) (w : Nat) : Nat :=
  if hw : w < n then
    if @decide (⟨w, hw⟩ ∈ l) (Classical.propDecidable _) then n + 1
    else if @decide (⟨w, hw⟩ ∈ u) (Classical.propDecidable _) then w
    else n
  else w

private noncomputable def buildStep (n : Nat) (C : Circuit) (l u : Finset (Fin n)) (cut : Nat) :
    Nat → List Gate × (Nat → Nat)
  | 0 => ([], tBase n l u)
  | k + 1 =>
    let res := buildStep n C l u cut k
    let dg := res.1
    let tm := res.2
    if hk : k < C.gates.length then
      if isNotGateList C.gates k && decide (B_cntList C.gates k < cut) then
        let cWire := if wireVal n C l (n + 2 + k) then n + 1 else n
        (dg, fun w => if w = n + 2 + k then cWire else tm w)
      else
        let g' : Gate := ⟨C.gates[k].op, C.gates[k].inputs.map tm⟩
        (dg ++ [g'], fun w => if w = n + 2 + k then n + 2 + dg.length else tm w)
    else
      (dg, tm)

private lemma filter_append_singleton {α : Type _} (l : List α) (a : α) (p : α → Bool) :
    ((l ++ [a]).filter p).length = (l.filter p).length + if p a then 1 else 0 := by
  induction l with
  | nil =>
    cases h : p a <;> simp [h]
  | cons x xs ih =>
    simp only [List.cons_append, List.filter_cons]
    cases p x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih
    · simp only [↓reduceIte, List.length_cons, ih]
      omega

private lemma buildStep_invariants (n : Nat) (C : Circuit)
    (hFan : PEqualNP.MetaComplexity.FanInTwo C)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    (l u : Finset (Fin n)) (cut : Nat)
    (hconst : ∀ x : Finset (Fin n), ∀ k < C.gates.length,
      isNotGateList C.gates k = true → B_cntList C.gates k < cut →
      wireVal n C (l ∪ (x ∩ u)) (n + 2 + k) = wireVal n C l (n + 2 + k)) :
    ∀ k ≤ C.gates.length,
      let dg := (buildStep n C l u cut k).1
      let tm := (buildStep n C l u cut k).2
      PEqualNP.MetaComplexity.FanInTwo ⟨dg, 0⟩ ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) ⟨dg, 0⟩ ∧
      (∀ w < n + 2 + k, tm w < n + 2 + dg.length) ∧
      dg.length + min (B_cntList C.gates k) cut = k ∧
      (dg.filter fun g => isNotOp g.op).length =
        B_cntList C.gates k - min (B_cntList C.gates k) cut ∧
      (∀ (x : Finset (Fin n)), ∀ w < n + 2 + k,
        (dg.foldl stepWire (inp n x)).getD (tm w) false = wireVal n C (l ∪ (x ∩ u)) w) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [buildStep, B_cntList, List.length_nil, Nat.zero_min, Nat.add_zero, Nat.sub_zero,
      List.filter_nil, List.foldl_nil]
    refine ⟨?_, ?_, ?_, trivial, trivial, ?_⟩
    · intro g hg
      cases hg
    · intro j hj
      cases hj
    · intro w hw
      unfold tBase
      split_ifs <;> omega
    · intro x w hw
      rw [wireVal_eq_foldl]
      have hlen_f : w < (inp n (l ∪ (x ∩ u))).length := by rw [length_inp]; exact hw
      rw [getD_foldl_stepWire_of_lt C.gates (inp n (l ∪ (x ∩ u))) w hlen_f]
      unfold tBase
      by_cases hwn : w < n
      · rw [dif_pos hwn, getD_inp_lt n (l ∪ (x ∩ u)) w hwn]
        by_cases hml : (⟨w, hwn⟩ : Fin n) ∈ l
        · have hd1 : @decide ((⟨w, hwn⟩ : Fin n) ∈ l) (Classical.propDecidable _) = true :=
            cdecide_true hml
          rw [hd1, if_pos rfl, getD_inp_n1]
          symm
          exact cdecide_true (Finset.mem_union_left _ hml)
        · have hd1 : @decide ((⟨w, hwn⟩ : Fin n) ∈ l) (Classical.propDecidable _) = false :=
            cdecide_false hml
          rw [hd1, if_neg Bool.false_ne_true]
          by_cases hmu : (⟨w, hwn⟩ : Fin n) ∈ u
          · have hd2 : @decide ((⟨w, hwn⟩ : Fin n) ∈ u) (Classical.propDecidable _) = true :=
              cdecide_true hmu
            rw [hd2, if_pos rfl, getD_inp_lt n x w hwn]
            by_cases hmx : (⟨w, hwn⟩ : Fin n) ∈ x
            · rw [cdecide_true hmx, cdecide_true (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hmx, hmu⟩))]
            · rw [cdecide_false hmx]
              symm
              apply cdecide_false
              intro hmem
              rcases Finset.mem_union.mp hmem with h1 | h2
              · exact hml h1
              · exact hmx (Finset.mem_inter.mp h2).1
          · have hd2 : @decide ((⟨w, hwn⟩ : Fin n) ∈ u) (Classical.propDecidable _) = false :=
              cdecide_false hmu
            rw [hd2, if_neg Bool.false_ne_true, getD_inp_n]
            symm
            apply cdecide_false
            intro hmem
            rcases Finset.mem_union.mp hmem with h1 | h2
            · exact hml h1
            · exact hmu (Finset.mem_inter.mp h2).2
      · rw [dif_neg hwn]
        by_cases hweq : w = n
        · subst hweq
          rw [getD_inp_n, getD_inp_n]
        · have hweq1 : w = n + 1 := by omega
          subst hweq1
          rw [getD_inp_n1, getD_inp_n1]
  | succ k ih =>
    intro hk1
    have hk : k < C.gates.length := Nat.lt_of_succ_le hk1
    obtain ⟨ihFan, ihRB, ihLt, ihLen, ihNot, ihWire⟩ := ih (Nat.le_of_lt hk)
    set dg := (buildStep n C l u cut k).1 with hdg_def
    set tm := (buildStep n C l u cut k).2 with htm_def
    have hstep : buildStep n C l u cut (k + 1) =
        if isNotGateList C.gates k && decide (B_cntList C.gates k < cut) then
          (dg, fun w => if w = n + 2 + k then (if wireVal n C l (n + 2 + k) then n + 1 else n) else tm w)
        else
          (dg ++ [⟨C.gates[k].op, C.gates[k].inputs.map tm⟩],
            fun w => if w = n + 2 + k then n + 2 + dg.length else tm w) := by
      simp only [buildStep, hk, ↓reduceDIte, hdg_def, htm_def]
    by_cases hcond : isNotGateList C.gates k = true ∧ B_cntList C.gates k < cut
    · obtain ⟨hnot, hlt⟩ := hcond
      have hbool : (isNotGateList C.gates k && decide (B_cntList C.gates k < cut)) = true := by
        simp [hnot, hlt]
      rw [hstep, if_pos hbool]
      dsimp only
      refine ⟨ihFan, ihRB, ?_, ?_, ?_, ?_⟩
      · intro w hw
        by_cases hweq : w = n + 2 + k
        · rw [if_pos hweq]
          cases wireVal n C l (n + 2 + k) <;> simp <;> omega
        · rw [if_neg hweq]
          exact ihLt w (by omega)
      · simp only [B_cntList, hnot, ↓reduceIte]
        omega
      · simp only [B_cntList, hnot, ↓reduceIte]
        omega
      · intro x w hw
        by_cases hweq : w = n + 2 + k
        · subst hweq
          rw [if_pos rfl]
          rw [hconst x k hk hnot hlt]
          cases hval : wireVal n C l (n + 2 + k)
          · simp only [Bool.false_eq_true, ↓reduceIte]
            have hlen : n < (inp n x).length := by rw [length_inp]; omega
            rw [getD_foldl_stepWire_of_lt dg (inp n x) n hlen, getD_inp_n]
          · simp only [↓reduceIte]
            have hlen : n + 1 < (inp n x).length := by rw [length_inp]; omega
            rw [getD_foldl_stepWire_of_lt dg (inp n x) (n + 1) hlen, getD_inp_n1]
        · rw [if_neg hweq]
          exact ihWire x w (by omega)
    · have hbool : (isNotGateList C.gates k && decide (B_cntList C.gates k < cut)) = false := by
        cases h1 : isNotGateList C.gates k
        · rfl
        · simp only [Bool.true_and, decide_eq_false_iff_not]
          intro h2
          exact hcond ⟨h1, h2⟩
      rw [hstep, if_neg (by rw [hbool]; exact Bool.false_ne_true)]
      dsimp only
      set g' : Gate := ⟨C.gates[k].op, C.gates[k].inputs.map tm⟩
      have hrb_k : ∀ i ∈ C.gates[k].inputs, i < n + 2 + k := by
        intro i hi
        have h1 := hRB k hk i
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt at h1
        rw [getD_eq_getElem C.gates k _ hk] at h1
        exact h1 hi
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | hg
        · exact ihFan g hg
        · subst hg
          have hgk := hFan C.gates[k] (List.getElem_mem hk)
          exact ⟨hgk.1, by simp [g', hgk.2]⟩
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
          exact ihLt i0 (hrb_k i0 hi0)
      · intro w hw
        simp only [List.length_append, List.length_singleton]
        by_cases hweq : w = n + 2 + k
        · rw [if_pos hweq]
          omega
        · rw [if_neg hweq]
          have := ihLt w (by omega)
          omega
      · simp only [List.length_append, List.length_singleton, B_cntList]
        cases hnot : isNotGateList C.gates k
        · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
          omega
        · simp only [↓reduceIte]
          have hge : ¬(B_cntList C.gates k < cut) := fun hlt => hcond ⟨hnot, hlt⟩
          omega
      · rw [filter_append_singleton]
        have hg_not : isNotOp g'.op = isNotGateList C.gates k := by
          simp [g', isNotGateList, hk]
        rw [hg_not]
        simp only [B_cntList]
        cases hnot : isNotGateList C.gates k
        · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
          exact ihNot
        · simp only [↓reduceIte]
          have hge : ¬(B_cntList C.gates k < cut) := fun hlt => hcond ⟨hnot, hlt⟩
          omega
      · intro x w hw
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        set W := dg.foldl stepWire (inp n x)
        have hWlen : W.length = n + 2 + dg.length := by
          rw [length_foldl_stepWire, length_inp]
        by_cases hweq : w = n + 2 + k
        · subst hweq
          rw [if_pos rfl]
          unfold stepWire
          rw [← hWlen, getD_append_right_eq]
          rw [wireVal_eval_at_gate n C hRB (l ∪ (x ∩ u)) k hk]
          congr 1
          simp only [g', List.map_map]
          apply map_eq_of_forall
          intro i hi
          exact ihWire x i (hrb_k i hi)
        · rw [if_neg hweq]
          unfold stepWire
          have hlt : tm w < W.length := by
            rw [hWlen]
            exact ihLt w (by omega)
          rw [getD_append_left W _ (tm w) false hlt]
          exact ihWire x w (by omega)

end PEqualNP.Outside.L_lib_1283

theorem PEqualNP.Outside.L_lib_1283 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit),
  let valid := fun (D : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) D ∧
      D.output < n+2+D.size
  let wire := fun (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Finset (Fin n)) (i : Nat) =>
    (D.wires (List.ofFn (fun j : Fin n => decide (j ∈ x)) ++ [false,true])).getD i false
  let drop := fun x y => ∃ i, i < n+2+C.size ∧ wire C x i = true ∧ wire C y i = false
  let before := Nat.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
    (fun _ prev x => ∃ u v, prev u ∧ u ⊆ v ∧ v ⊆ x ∧ drop u v)
  let after := Nat.rec (motive := fun _ => Finset (Fin n) → Prop) (fun _ => True)
    (fun _ prev x => ∃ u v, x ⊆ u ∧ u ⊆ v ∧ drop u v ∧ prev v)
  let b := PEqualNP.NotBracket.notCount C
  valid C → ∀ (l u : Finset (Fin n)) (i j s q : Nat), l ⊆ u →
    before i l → after j u → q*2^s ≤ j → 2^b ≤ (q+1)*2^s+i →
    ∃ D, valid D ∧ D.size + (b-s) ≤ C.size ∧ PEqualNP.NotBracket.notCount D ≤ s ∧
      ∃ t : Fin (n+2+C.size) → Fin (n+2+D.size),
        (∀ x k, wire D x (t k).val = wire C (l ∪ (x ∩ u)) k.val) ∧
        ∀ x, wire D x D.output = wire C (l ∪ (x ∩ u)) C.output) := by
  intro n C valid wire drop before after b hvalid l u i j s q hlu hbef haft hq1 hq2
  obtain ⟨hFan, hRB, hOut⟩ := hvalid
  have hwire_eq : ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (x : Finset (Fin n)) (w : Nat),
      wire D x w = PEqualNP.Outside.L_lib_1283.wireVal n D x w := by
    intro D x w
    rfl
  have hb_eq : b = PEqualNP.Outside.L_lib_1283.B_cntList C.gates C.gates.length := by
    change PEqualNP.NotBracket.notCount C = PEqualNP.Outside.L_lib_1283.B_cntList C.gates C.gates.length
    rw [PEqualNP.Outside.L_lib_1283.notCount_eq_filter_isNotOp, PEqualNP.Outside.L_lib_1283.B_cntList_length]
  have hdrop_lt : ∀ {a c : Finset (Fin n)}, a ⊆ c → drop a c →
      PEqualNP.Outside.L_lib_1283.V n C c C.gates.length < PEqualNP.Outside.L_lib_1283.V n C a C.gates.length := by
    intro a c hac ⟨w, hw, hwa, hwc⟩
    obtain ⟨hle, hmono⟩ := PEqualNP.Outside.L_lib_1283.V_anti_and_mono_wires n C hFan hRB hac C.gates.length (Nat.le_refl _)
    by_cases heq : PEqualNP.Outside.L_lib_1283.V n C c C.gates.length = PEqualNP.Outside.L_lib_1283.V n C a C.gates.length
    · exfalso
      rw [hwire_eq] at hwa hwc
      have hvtrue := hmono heq w hw hwa
      rw [hwc] at hvtrue
      cases hvtrue
    · omega
  have hbefore_bound : ∀ (m : Nat) (x : Finset (Fin n)), before m x →
      PEqualNP.Outside.L_lib_1283.V n C x C.gates.length + m < 2 ^ b := by
    intro m
    induction m with
    | zero =>
      intro x _
      rw [hb_eq, Nat.add_zero]
      exact PEqualNP.Outside.L_lib_1283.V_lt_pow n C x C.gates.length
    | succ m ih =>
      intro x ⟨a, c, ha, hac, hcx, hdrop⟩
      have h1 := ih a ha
      have h2 := hdrop_lt hac hdrop
      have h3 := (PEqualNP.Outside.L_lib_1283.V_anti_and_mono_wires n C hFan hRB hcx C.gates.length (Nat.le_refl _)).1
      omega
  have hafter_bound : ∀ (m : Nat) (x : Finset (Fin n)), after m x →
      m ≤ PEqualNP.Outside.L_lib_1283.V n C x C.gates.length := by
    intro m
    induction m with
    | zero =>
      intro x _
      exact Nat.zero_le _
    | succ m ih =>
      intro x ⟨a, c, hxa, hac, hdrop, hc⟩
      have h1 := ih c hc
      have h2 := hdrop_lt hac hdrop
      have h3 := (PEqualNP.Outside.L_lib_1283.V_anti_and_mono_wires n C hFan hRB hxa C.gates.length (Nat.le_refl _)).1
      omega
  have hVl : PEqualNP.Outside.L_lib_1283.V n C l C.gates.length + i < 2 ^ b := hbefore_bound i l hbef
  have hVu : j ≤ PEqualNP.Outside.L_lib_1283.V n C u C.gates.length := hafter_bound j u haft
  have hdiv_face : ∀ y : Finset (Fin n), l ⊆ y → y ⊆ u →
      PEqualNP.Outside.L_lib_1283.V n C y C.gates.length / 2 ^ s = q := by
    intro y hly hyu
    have h1 := (PEqualNP.Outside.L_lib_1283.V_anti_and_mono_wires n C hFan hRB hly C.gates.length (Nat.le_refl _)).1
    have h2 := (PEqualNP.Outside.L_lib_1283.V_anti_and_mono_wires n C hFan hRB hyu C.gates.length (Nat.le_refl _)).1
    have hpos : 0 < 2 ^ s := Nat.pow_pos (by omega)
    exact PEqualNP.Outside.L_lib_1283.div_eq_of_bounds hpos (by omega) (by omega)
  have hdiv_l : PEqualNP.Outside.L_lib_1283.V n C l C.gates.length / 2 ^ s = q :=
    hdiv_face l (Finset.Subset.refl l) hlu
  have hconst : ∀ x : Finset (Fin n), ∀ k < C.gates.length,
      PEqualNP.Outside.L_lib_1283.isNotGateList C.gates k = true → PEqualNP.Outside.L_lib_1283.B_cntList C.gates k < b - s →
      PEqualNP.Outside.L_lib_1283.wireVal n C (l ∪ (x ∩ u)) (n + 2 + k) = PEqualNP.Outside.L_lib_1283.wireVal n C l (n + 2 + k) := by
    intro x k hk hnot hbk
    have hly : l ⊆ l ∪ (x ∩ u) := Finset.subset_union_left
    have hyu : l ∪ (x ∩ u) ⊆ u := Finset.union_subset hlu Finset.inter_subset_right
    have hdiv_eq : PEqualNP.Outside.L_lib_1283.V n C (l ∪ (x ∩ u)) C.gates.length / 2 ^ s =
        PEqualNP.Outside.L_lib_1283.V n C l C.gates.length / 2 ^ s := by
      rw [hdiv_face (l ∪ (x ∩ u)) hly hyu, hdiv_l]
    rw [hb_eq] at hbk
    exact PEqualNP.Outside.L_lib_1283.wireVal_const_of_div_eq n C (l ∪ (x ∩ u)) l s k hk hnot hbk hdiv_eq
  obtain ⟨hDFan, hDRB, hDLt, hDLen, hDNot, hDWire⟩ :=
    PEqualNP.Outside.L_lib_1283.buildStep_invariants n C hFan hRB l u (b - s) hconst C.gates.length (Nat.le_refl _)
  set dg := (PEqualNP.Outside.L_lib_1283.buildStep n C l u (b - s) C.gates.length).1
  set tm := (PEqualNP.Outside.L_lib_1283.buildStep n C l u (b - s) C.gates.length).2
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨dg, tm C.output⟩
  have hDout : D.output < n + 2 + D.size := hDLt C.output hOut
  have hmin : min (PEqualNP.Outside.L_lib_1283.B_cntList C.gates C.gates.length) (b - s) = b - s := by
    rw [← hb_eq]
    omega
  refine ⟨D, ⟨hDFan, hDRB, hDout⟩, ?_, ?_, ?_⟩
  · change dg.length + (b - s) ≤ C.gates.length
    rw [← hmin]
    omega
  · rw [PEqualNP.Outside.L_lib_1283.notCount_eq_filter_isNotOp]
    change (dg.filter fun g => PEqualNP.Outside.L_lib_1283.isNotOp g.op).length ≤ s
    rw [hDNot, hmin, ← hb_eq]
    omega
  · refine ⟨fun k => ⟨tm k.val, hDLt k.val k.isLt⟩, ?_, ?_⟩
    · intro x k
      rw [hwire_eq, hwire_eq]
      refine (hDWire x k.val k.isLt).trans ?_
      apply PEqualNP.Outside.L_lib_1283.wireVal_congr_set
      intro j
      simp [Finset.mem_union, Finset.mem_inter]
    · intro x
      rw [hwire_eq, hwire_eq]
      refine (hDWire x C.output hOut).trans ?_
      apply PEqualNP.Outside.L_lib_1283.wireVal_congr_set
      intro j
      simp [Finset.mem_union, Finset.mem_inter]
