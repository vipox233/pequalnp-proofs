import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1301

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

private def interAll {t : Nat} (S : Finset (Finset (Fin t))) : Finset (Fin t) :=
  Finset.univ.filter (fun a => ∀ s ∈ S, a ∈ s)

private lemma mem_interAll {t : Nat} {S : Finset (Finset (Fin t))} {a : Fin t} :
    a ∈ interAll S ↔ ∀ s ∈ S, a ∈ s := by
  unfold interAll
  simp

private lemma interAll_subset {t : Nat} {S : Finset (Finset (Fin t))} {s : Finset (Fin t)}
    (hs : s ∈ S) : interAll S ⊆ s := by
  intro a ha
  exact (mem_interAll.mp ha) s hs

private lemma interAll_mem {t : Nat} {S : Finset (Finset (Fin t))}
    (hS : S.Nonempty) (hCl : ∀ a ∈ S, ∀ b ∈ S, ∃ c ∈ S, ∀ u, u ∈ c ↔ u ∈ a ∧ u ∈ b) :
    interAll S ∈ S := by
  have haux : ∀ k, ∀ a ∈ S, a.card = k → interAll S ∈ S := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro a ha hcard
      by_cases hsub : a ⊆ interAll S
      · have heq : interAll S = a := Finset.Subset.antisymm (interAll_subset ha) hsub
        rw [heq]
        exact ha
      · have hex : ∃ u ∈ a, u ∉ interAll S := by
          apply Classical.byContradiction
          intro hno
          apply hsub
          intro u hu
          apply Classical.byContradiction
          intro hnot
          exact hno ⟨u, hu, hnot⟩
        obtain ⟨u, hua, hu_not⟩ := hex
        have hex2 : ∃ b ∈ S, u ∉ b := by
          apply Classical.byContradiction
          intro hno
          apply hu_not
          exact mem_interAll.mpr (fun b hb => Classical.byContradiction (fun hnb => hno ⟨b, hb, hnb⟩))
        obtain ⟨b, hb, hub⟩ := hex2
        obtain ⟨c, hc_mem, hc_iff⟩ := hCl a ha b hb
        have hc_ssub : c ⊂ a := by
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨fun v hv => ((hc_iff v).mp hv).1, ?_⟩
          intro heq
          have : u ∈ c := heq.symm ▸ hua
          exact hub ((hc_iff u).mp this).2
        have hc_lt : c.card < k := by
          rw [← hcard]
          exact Finset.card_lt_card hc_ssub
        exact ih c.card hc_lt c hc_mem rfl
  obtain ⟨a, ha⟩ := hS
  exact haux a.card a ha rfl

private def beforeSt {t : Nat} (a b : Nat × Finset (Fin t)) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ⊆ b.2)

private lemma beforeSt_refl {t : Nat} (a : Nat × Finset (Fin t)) : beforeSt a a :=
  Or.inr ⟨rfl, Finset.Subset.refl _⟩

private lemma beforeSt_antisymm {t : Nat} {a b : Nat × Finset (Fin t)}
    (h1 : beforeSt a b) (h2 : beforeSt b a) : a = b := by
  rcases h1 with h1 | ⟨h1a, h1b⟩ <;> rcases h2 with h2 | ⟨h2a, h2b⟩
  · omega
  · omega
  · omega
  · exact Prod.ext h1a (Finset.Subset.antisymm h1b h2b)

private lemma beforeSt_trans {t : Nat} {a b c : Nat × Finset (Fin t)}
    (h1 : beforeSt a b) (h2 : beforeSt b c) : beforeSt a c := by
  rcases h1 with h1 | ⟨h1a, h1b⟩ <;> rcases h2 with h2 | ⟨h2a, h2b⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, Finset.Subset.trans h1b h2b⟩

private def candSt {n m t : Nat} (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin t)))
    (g : Fin m → Nat × Finset (Fin t)) (i : Fin m) (b : Nat × Finset (Fin t)) : Prop :=
  b.2 ∈ A i ∧ ∀ j, j ≠ i → x j ⊆ x i → beforeSt (g j) b

private def greedySt {n m t : Nat} (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin t)))
    (g : Fin m → Nat × Finset (Fin t)) : Prop :=
  ∀ i, candSt x A g i (g i) ∧ ∀ b, candSt x A g i b → beforeSt (g i) b

private lemma card_lt_of_ne_subset {n m : Nat} {x : Fin m → Finset (Fin n)}
    (hx : Function.Injective x) {i j : Fin m} (hji : j ≠ i) (hsub : x j ⊆ x i) :
    (x j).card < (x i).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  exact ⟨hsub, fun heq => hji (hx heq)⟩

private lemma greedySt_least {n m t : Nat} {x : Fin m → Finset (Fin n)}
    {A : Fin m → Finset (Finset (Fin t))} (hx : Function.Injective x)
    {g h : Fin m → Nat × Finset (Fin t)}
    (hg : greedySt x A g) (hh : ∀ i, candSt x A h i (h i)) :
    ∀ i, beforeSt (g i) (h i) := by
  have haux : ∀ k, ∀ i : Fin m, (x i).card = k → beforeSt (g i) (h i) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro i hi
      apply (hg i).2 (h i)
      refine ⟨(hh i).1, ?_⟩
      intro j hji hsub
      have hlt : (x j).card < k := by
        rw [← hi]
        exact card_lt_of_ne_subset hx hji hsub
      exact beforeSt_trans (ih (x j).card hlt j rfl) ((hh i).2 j hji hsub)
  intro i
  exact haux (x i).card i rfl

private lemma greedySt_unique {n m t : Nat} {x : Fin m → Finset (Fin n)}
    {A : Fin m → Finset (Finset (Fin t))} (hx : Function.Injective x)
    {g1 g2 : Fin m → Nat × Finset (Fin t)}
    (h1 : greedySt x A g1) (h2 : greedySt x A g2) : g1 = g2 := by
  funext i
  exact beforeSt_antisymm
    (greedySt_least hx h1 (fun j => (h2 j).1) i)
    (greedySt_least hx h2 (fun j => (h1 j).1) i)

private def listMax : List Nat → Nat
  | [] => 0
  | a :: l => max a (listMax l)

private lemma le_listMax {l : List Nat} {a : Nat} (ha : a ∈ l) : a ≤ listMax l := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    simp only [listMax]
    rcases List.mem_cons.mp ha with rfl | hmem
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hmem) (Nat.le_max_right _ _)

private lemma exists_mem_listMax {l : List Nat} (hl : l ≠ []) : ∃ a ∈ l, a = listMax l := by
  induction l with
  | nil => exact False.elim (hl rfl)
  | cons x xs ih =>
    cases xs with
    | nil =>
      refine ⟨x, List.mem_cons_self, ?_⟩
      simp [listMax]
    | cons y ys =>
      obtain ⟨a, ha, heq⟩ := ih (List.cons_ne_nil y ys)
      by_cases hxy : x ≤ listMax (y :: ys)
      · refine ⟨a, List.mem_cons_of_mem _ ha, ?_⟩
        change a = max x (listMax (y :: ys))
        rw [Nat.max_eq_right hxy]
        exact heq
      · refine ⟨x, List.mem_cons_self, ?_⟩
        change x = max x (listMax (y :: ys))
        rw [Nat.max_eq_left (by omega)]

private def predList {n m : Nat} (x : Fin m → Finset (Fin n)) (i : Fin m) :
    List (Fin m) :=
  (List.finRange m).filter (fun j => decide (j ≠ i ∧ x j ⊆ x i))

private lemma mem_predList {n m : Nat} (x : Fin m → Finset (Fin n)) (i j : Fin m) :
    j ∈ predList x i ↔ j ≠ i ∧ x j ⊆ x i := by
  unfold predList
  simp

private def stepGreedyAux {t : Nat} (Ai : Finset (Finset (Fin t)))
    (L : Nat) (W : Finset (Fin t)) : Nat × Finset (Fin t) :=
  let SupA := Ai.filter (fun s => W ⊆ s)
  if SupA.Nonempty then (L, interAll SupA) else (L + 1, interAll Ai)

private def stepGreedy {n m t : Nat} (x : Fin m → Finset (Fin n))
    (A : Fin m → Finset (Finset (Fin t))) (prev : Fin m → Nat × Finset (Fin t)) (i : Fin m) :
    Nat × Finset (Fin t) :=
  let P := predList x i
  if P = [] then
    (0, interAll (A i))
  else
    let L := listMax (P.map (fun j => (prev j).1))
    let W := Finset.univ.filter (fun a : Fin t => ∃ j ∈ P, (prev j).1 = L ∧ a ∈ (prev j).2)
    stepGreedyAux (A i) L W

private lemma stepGreedy_congr {n m t : Nat} (x : Fin m → Finset (Fin n))
    (A : Fin m → Finset (Finset (Fin t))) (p1 p2 : Fin m → Nat × Finset (Fin t)) (i : Fin m)
    (h : ∀ j, j ≠ i → x j ⊆ x i → p1 j = p2 j) :
    stepGreedy x A p1 i = stepGreedy x A p2 i := by
  unfold stepGreedy
  dsimp only
  by_cases hP : predList x i = []
  · simp [hP]
  · simp only [hP, ↓reduceIte]
    have hmap : (predList x i).map (fun j => (p1 j).1) = (predList x i).map (fun j => (p2 j).1) := by
      apply map_eq_of_forall
      intro j hj
      obtain ⟨hji, hsub⟩ := (mem_predList x i j).mp hj
      rw [h j hji hsub]
    have hL : listMax ((predList x i).map (fun j => (p1 j).1)) =
        listMax ((predList x i).map (fun j => (p2 j).1)) := by
      rw [hmap]
    have hW : Finset.univ.filter (fun a : Fin t => ∃ j ∈ predList x i,
          (p1 j).1 = listMax ((predList x i).map (fun j => (p1 j).1)) ∧ a ∈ (p1 j).2) =
        Finset.univ.filter (fun a : Fin t => ∃ j ∈ predList x i,
          (p2 j).1 = listMax ((predList x i).map (fun j => (p2 j).1)) ∧ a ∈ (p2 j).2) := by
      apply Finset.ext
      intro a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, hj, h1, h2⟩
        obtain ⟨hji, hsub⟩ := (mem_predList x i j).mp hj
        refine ⟨j, hj, ?_, ?_⟩
        · rw [← h j hji hsub, ← hL]; exact h1
        · rw [← h j hji hsub]; exact h2
      · rintro ⟨j, hj, h1, h2⟩
        obtain ⟨hji, hsub⟩ := (mem_predList x i j).mp hj
        refine ⟨j, hj, ?_, ?_⟩
        · rw [h j hji hsub, hL]; exact h1
        · rw [h j hji hsub]; exact h2
    exact congrArg₂ (stepGreedyAux (A i)) hL hW

private def gIter {n m t : Nat} (x : Fin m → Finset (Fin n))
    (A : Fin m → Finset (Finset (Fin t))) : Nat → Fin m → Nat × Finset (Fin t)
  | 0 => stepGreedy x A (fun _ => (0, ∅))
  | k + 1 => stepGreedy x A (gIter x A k)

private lemma gIter_stable {n m t : Nat} {x : Fin m → Finset (Fin n)}
    {A : Fin m → Finset (Finset (Fin t))} (hx : Function.Injective x) :
    ∀ k k', k ≤ k' → ∀ i : Fin m, (x i).card ≤ k → gIter x A k' i = gIter x A k i := by
  intro k
  induction k with
  | zero =>
    intro k' _ i hi
    cases k' with
    | zero => rfl
    | succ d =>
      simp only [gIter]
      apply stepGreedy_congr
      intro j hji hsub
      have hlt := card_lt_of_ne_subset hx hji hsub
      omega
  | succ k ih =>
    intro k' hkk' i hi
    cases k' with
    | zero => omega
    | succ d =>
      simp only [gIter]
      apply stepGreedy_congr
      intro j hji hsub
      have hlt := card_lt_of_ne_subset hx hji hsub
      exact ih d (by omega) j (by omega)

private def gStar {n m t : Nat} (x : Fin m → Finset (Fin n))
    (A : Fin m → Finset (Finset (Fin t))) : Fin m → Nat × Finset (Fin t) :=
  gIter x A n

private lemma gStar_eq_step {n m t : Nat} {x : Fin m → Finset (Fin n)}
    {A : Fin m → Finset (Finset (Fin t))} (hx : Function.Injective x) (i : Fin m) :
    gStar x A i = stepGreedy x A (gStar x A) i := by
  have hcard : (x i).card ≤ n := by
    have h1 := Finset.card_le_univ (x i)
    simpa using h1
  have hst := gIter_stable (A := A) hx n (n + 1) (Nat.le_succ n) i hcard
  exact hst.symm

private lemma gStar_greedy {n m t : Nat} {x : Fin m → Finset (Fin n)}
    {A : Fin m → Finset (Finset (Fin t))} (hx : Function.Injective x)
    (hAne : ∀ i, (A i).Nonempty)
    (hAcl : ∀ i a b, a ∈ A i → b ∈ A i → ∃ c ∈ A i, ∀ u, u ∈ c ↔ u ∈ a ∧ u ∈ b) :
    greedySt x A (gStar x A) := by
  intro i
  have hfix := gStar_eq_step (A := A) hx i
  unfold stepGreedy stepGreedyAux at hfix
  dsimp only at hfix
  have hAcl_i : ∀ a ∈ A i, ∀ b ∈ A i, ∃ c ∈ A i, ∀ u, u ∈ c ↔ u ∈ a ∧ u ∈ b :=
    fun a ha b hb => hAcl i a b ha hb
  by_cases hP : predList x i = []
  · simp only [hP, ↓reduceIte] at hfix
    constructor
    · refine ⟨?_, ?_⟩
      · rw [hfix]
        exact interAll_mem (hAne i) hAcl_i
      · intro j hji hsub
        have hmem : j ∈ predList x i := (mem_predList x i j).mpr ⟨hji, hsub⟩
        rw [hP] at hmem
        cases hmem
    · intro b hb
      rw [hfix]
      by_cases hb0 : 0 < b.1
      · exact Or.inl hb0
      · exact Or.inr ⟨by omega, interAll_subset hb.1⟩
  · simp only [hP, ↓reduceIte] at hfix
    set P := predList x i
    set L := listMax (P.map (fun j => (gStar x A j).1))
    set W : Finset (Fin t) := Finset.univ.filter (fun a : Fin t => ∃ j ∈ P, (gStar x A j).1 = L ∧ a ∈ (gStar x A j).2)
    set SupA : Finset (Finset (Fin t)) := (A i).filter (fun s => W ⊆ s)
    have hPne : P.map (fun j => (gStar x A j).1) ≠ [] := by
      intro hnil
      exact hP (List.map_eq_nil_iff.mp hnil)
    obtain ⟨v0, hv0_mem, hv0_eq⟩ := exists_mem_listMax hPne
    obtain ⟨j0, hj0P, hj0_eq⟩ := List.mem_map.mp hv0_mem
    have hj0L : (gStar x A j0).1 = L := hj0_eq.trans hv0_eq
    have hj0_prop := (mem_predList x i j0).mp hj0P
    have hleL : ∀ j ∈ P, (gStar x A j).1 ≤ L := by
      intro j hj
      exact le_listMax (List.mem_map.mpr ⟨j, hj, rfl⟩)
    have hSupCl : ∀ a ∈ SupA, ∀ b ∈ SupA, ∃ c ∈ SupA, ∀ u, u ∈ c ↔ u ∈ a ∧ u ∈ b := by
      intro a ha b hb
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      obtain ⟨c, hc_mem, hc_iff⟩ := hAcl i a b ha'.1 hb'.1
      refine ⟨c, Finset.mem_filter.mpr ⟨hc_mem, fun u hu => (hc_iff u).mpr ⟨ha'.2 hu, hb'.2 hu⟩⟩, hc_iff⟩
    have hW_sub_of_eq : ∀ b : Nat × Finset (Fin t), candSt x A (gStar x A) i b → b.1 = L → W ⊆ b.2 := by
      intro b hb hbL a ha
      have ha' := (Finset.mem_filter.mp ha).2
      obtain ⟨j, hjP, hjL, haj⟩ := ha'
      obtain ⟨hji, hsub⟩ := (mem_predList x i j).mp hjP
      have hbef := hb.2 j hji hsub
      rcases hbef with hlt | ⟨_, hsub2⟩
      · omega
      · exact hsub2 haj
    have hL_le : ∀ b : Nat × Finset (Fin t), candSt x A (gStar x A) i b → L ≤ b.1 := by
      intro b hb
      have hbef := hb.2 j0 hj0_prop.1 hj0_prop.2
      rcases hbef with hlt | ⟨heq, _⟩ <;> omega
    by_cases hSup : SupA.Nonempty
    · simp only [hSup, ↓reduceIte] at hfix
      have hmin_mem : interAll SupA ∈ SupA := interAll_mem hSup hSupCl
      have hmin_mem' := Finset.mem_filter.mp hmin_mem
      constructor
      · refine ⟨?_, ?_⟩
        · rw [hfix]; exact hmin_mem'.1
        · intro j hji hsub
          rw [hfix]
          have hjP : j ∈ P := (mem_predList x i j).mpr ⟨hji, hsub⟩
          have hjle := hleL j hjP
          by_cases hjlt : (gStar x A j).1 < L
          · exact Or.inl hjlt
          · have hjeq : (gStar x A j).1 = L := by omega
            refine Or.inr ⟨hjeq, ?_⟩
            intro a ha
            apply hmin_mem'.2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, ⟨j, hjP, hjeq, ha⟩⟩
      · intro b hb
        rw [hfix]
        have hLb := hL_le b hb
        by_cases hlt : L < b.1
        · exact Or.inl hlt
        · have heq : L = b.1 := by omega
          have hbSup : b.2 ∈ SupA := Finset.mem_filter.mpr ⟨hb.1, hW_sub_of_eq b hb heq.symm⟩
          exact Or.inr ⟨heq, interAll_subset hbSup⟩
    · simp only [hSup, ↓reduceIte] at hfix
      constructor
      · refine ⟨?_, ?_⟩
        · rw [hfix]
          exact interAll_mem (hAne i) hAcl_i
        · intro j hji hsub
          rw [hfix]
          have hjP : j ∈ P := (mem_predList x i j).mpr ⟨hji, hsub⟩
          have hjle := hleL j hjP
          exact Or.inl (by omega)
      · intro b hb
        rw [hfix]
        have hLb := hL_le b hb
        have hne : b.1 ≠ L := by
          intro heq
          apply hSup
          exact ⟨b.2, Finset.mem_filter.mpr ⟨hb.1, hW_sub_of_eq b hb heq⟩⟩
        by_cases hlt : L + 1 < b.1
        · exact Or.inl hlt
        · exact Or.inr ⟨by omega, interAll_subset hb.1⟩

private lemma gStar_level_le_card {n m t : Nat} {x : Fin m → Finset (Fin n)}
    {A : Fin m → Finset (Finset (Fin t))} (hx : Function.Injective x) :
    ∀ i : Fin m, (gStar x A i).1 ≤ (x i).card := by
  have haux : ∀ k, ∀ i : Fin m, (x i).card = k → (gStar x A i).1 ≤ (x i).card := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro i hi
      have hfix := gStar_eq_step (A := A) hx i
      unfold stepGreedy stepGreedyAux at hfix
      dsimp only at hfix
      by_cases hP : predList x i = []
      · simp only [hP, ↓reduceIte] at hfix
        rw [hfix]
        exact Nat.zero_le _
      · simp only [hP, ↓reduceIte] at hfix
        set P := predList x i
        set L := listMax (P.map (fun j => (gStar x A j).1))
        have hPne : P.map (fun j => (gStar x A j).1) ≠ [] := by
          intro hnil
          exact hP (List.map_eq_nil_iff.mp hnil)
        obtain ⟨v0, hv0_mem, hv0_eq⟩ := exists_mem_listMax hPne
        obtain ⟨j0, hj0P, hj0_eq⟩ := List.mem_map.mp hv0_mem
        have hj0L : (gStar x A j0).1 = L := hj0_eq.trans hv0_eq
        obtain ⟨hj0ne, hj0sub⟩ := (mem_predList x i j0).mp hj0P
        have hlt : (x j0).card < k := by
          rw [← hi]
          exact card_lt_of_ne_subset hx hj0ne hj0sub
        have hj0le : L ≤ (x j0).card := by
          rw [← hj0L]
          exact ih (x j0).card hlt j0 rfl
        rw [hfix]
        split_ifs <;> omega
  intro i
  exact haux (x i).card i rfl

private def GoodGates (N : Nat) (gs : List Gate) : Prop :=
  PEqualNP.MetaComplexity.FanInTwo ⟨gs, 0⟩ ∧
  PEqualNP.MetaComplexity.NestedCover.ReadsBack N ⟨gs, 0⟩

private def notCnt (gs : List Gate) : Nat :=
  (gs.filter fun g => isNotOp g.op).length

private def evalW (gs : List Gate) (v : List Bool) (w : Nat) : Bool :=
  (gs.foldl stepWire v).getD w false

private def IsExt (gs1 gs2 : List Gate) : Prop :=
  ∃ extra, gs2 = gs1 ++ extra

private lemma IsExt_refl (gs : List Gate) : IsExt gs gs :=
  ⟨[], by simp⟩

private lemma IsExt_trans {a b c : List Gate} (h1 : IsExt a b) (h2 : IsExt b c) : IsExt a c := by
  obtain ⟨e1, rfl⟩ := h1
  obtain ⟨e2, rfl⟩ := h2
  exact ⟨e1 ++ e2, by simp⟩

private lemma IsExt_length_le {a b : List Gate} (h : IsExt a b) : a.length ≤ b.length := by
  obtain ⟨e, rfl⟩ := h
  simp

private lemma evalW_of_IsExt {N : Nat} {gs1 gs2 : List Gate} (hext : IsExt gs1 gs2)
    {v : List Bool} (hv : v.length = N) {w : Nat} (hw : w < N + gs1.length) :
    evalW gs2 v w = evalW gs1 v w := by
  obtain ⟨extra, rfl⟩ := hext
  unfold evalW
  rw [List.foldl_append]
  have hlen : w < (gs1.foldl stepWire v).length := by
    rw [length_foldl_stepWire, hv]
    exact hw
  exact getD_foldl_stepWire_of_lt extra (gs1.foldl stepWire v) w hlen

private lemma evalW_input {N : Nat} (gs : List Gate) {v : List Bool} (hv : v.length = N)
    {w : Nat} (hw : w < N) : evalW gs v w = v.getD w false := by
  unfold evalW
  apply getD_foldl_stepWire_of_lt gs v w
  rw [hv]
  exact hw

private def emitGate (N : Nat) (gs : List Gate) (g : Gate) : List Gate × Nat :=
  (gs ++ [g], N + gs.length)

private def emitNot (N : Nat) (gs : List Gate) (a : Nat) : List Gate × Nat :=
  emitGate N gs ⟨GateOp.not, [a]⟩

private def emitAnd (N : Nat) (gs : List Gate) (a b : Nat) : List Gate × Nat :=
  emitGate N gs ⟨GateOp.and, [a, b]⟩

private def emitOr (N : Nat) (gs : List Gate) (a b : Nat) : List Gate × Nat :=
  emitGate N gs ⟨GateOp.or, [a, b]⟩

private lemma emitGate_spec (N : Nat) (gs : List Gate) (g : Gate)
    (hG : GoodGates N gs)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2)
    (hinp : ∀ u ∈ g.inputs, u < N + gs.length) :
    let res := emitGate N gs g
    IsExt gs res.1 ∧ GoodGates N res.1 ∧ res.1.length = gs.length + 1 ∧
    notCnt res.1 = notCnt gs + (if isNotOp g.op then 1 else 0) ∧
    res.2 < N + res.1.length ∧
    ∀ v : List Bool, v.length = N →
      evalW res.1 v res.2 = g.op.eval (g.inputs.map (evalW gs v)) := by
  dsimp only [emitGate]
  refine ⟨⟨[g], rfl⟩, ⟨?_, ?_⟩, by simp, filter_append_singleton gs g (fun x => isNotOp x.op), by simp, ?_⟩
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hG.1 x hx
    · exact ⟨hop, hlen⟩
  · intro j hj u hu
    simp only [List.length_append, List.length_singleton] at hj
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt at hu
    by_cases hjd : j < gs.length
    · rw [getD_append_left gs [g] j _ hjd] at hu
      exact hG.2 j hjd u hu
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [getD_append_right_eq gs g] at hu
      exact hinp u hu
  · intro v hv
    unfold evalW
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set W := gs.foldl stepWire v
    have hvlen : W.length = N + gs.length := by
      rw [length_foldl_stepWire, hv]
    unfold stepWire
    rw [← hvlen, getD_append_right_eq]

private lemma emitNot_spec (N : Nat) (gs : List Gate) (a : Nat)
    (hG : GoodGates N gs) (ha : a < N + gs.length) :
    let res := emitNot N gs a
    IsExt gs res.1 ∧ GoodGates N res.1 ∧ res.1.length = gs.length + 1 ∧
    notCnt res.1 = notCnt gs + 1 ∧ res.2 < N + res.1.length ∧
    ∀ v : List Bool, v.length = N → evalW res.1 v res.2 = !(evalW gs v a) := by
  have h := emitGate_spec N gs ⟨GateOp.not, [a]⟩ hG (by simp) (by simp) (by intro u hu; simp at hu; omega)
  dsimp only [emitNot]
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, h.2.2.2.2.1, ?_⟩
  · simpa [isNotOp] using h.2.2.2.1
  · intro v hv
    have hev := h.2.2.2.2.2 v hv
    simpa [GateOp.eval] using hev

private lemma emitAnd_spec (N : Nat) (gs : List Gate) (a b : Nat)
    (hG : GoodGates N gs) (ha : a < N + gs.length) (hb : b < N + gs.length) :
    let res := emitAnd N gs a b
    IsExt gs res.1 ∧ GoodGates N res.1 ∧ res.1.length = gs.length + 1 ∧
    notCnt res.1 = notCnt gs ∧ res.2 < N + res.1.length ∧
    ∀ v : List Bool, v.length = N → evalW res.1 v res.2 = (evalW gs v a && evalW gs v b) := by
  have h := emitGate_spec N gs ⟨GateOp.and, [a, b]⟩ hG (by simp) (by simp) (by
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> assumption)
  dsimp only [emitAnd]
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, h.2.2.2.2.1, ?_⟩
  · simpa [isNotOp] using h.2.2.2.1
  · intro v hv
    have hev := h.2.2.2.2.2 v hv
    simpa [GateOp.eval] using hev

private lemma emitOr_spec (N : Nat) (gs : List Gate) (a b : Nat)
    (hG : GoodGates N gs) (ha : a < N + gs.length) (hb : b < N + gs.length) :
    let res := emitOr N gs a b
    IsExt gs res.1 ∧ GoodGates N res.1 ∧ res.1.length = gs.length + 1 ∧
    notCnt res.1 = notCnt gs ∧ res.2 < N + res.1.length ∧
    ∀ v : List Bool, v.length = N → evalW res.1 v res.2 = (evalW gs v a || evalW gs v b) := by
  have h := emitGate_spec N gs ⟨GateOp.or, [a, b]⟩ hG (by simp) (by simp) (by
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;> assumption)
  dsimp only [emitOr]
  refine ⟨h.1, h.2.1, h.2.2.1, ?_, h.2.2.2.2.1, ?_⟩
  · simpa [isNotOp] using h.2.2.2.1
  · intro v hv
    have hev := h.2.2.2.2.2 v hv
    simpa [GateOp.eval] using hev

private def emitAndFold (N : Nat) (gs : List Gate) (acc : Nat) : List Nat → List Gate × Nat
  | [] => (gs, acc)
  | w :: ws =>
    let res := emitAnd N gs acc w
    emitAndFold N res.1 res.2 ws

private lemma emitAndFold_spec (N : Nat) (ws : List Nat) :
    ∀ (gs : List Gate) (acc : Nat),
      GoodGates N gs → acc < N + gs.length → (∀ u ∈ ws, u < N + gs.length) →
      let res := emitAndFold N gs acc ws
      IsExt gs res.1 ∧ GoodGates N res.1 ∧ res.1.length = gs.length + ws.length ∧
      notCnt res.1 = notCnt gs ∧ res.2 < N + res.1.length ∧
      ∀ v : List Bool, v.length = N →
        (evalW res.1 v res.2 = true ↔ evalW gs v acc = true ∧ ∀ u ∈ ws, evalW gs v u = true) := by
  induction ws with
  | nil =>
    intro gs acc hG hacc _
    dsimp only [emitAndFold]
    refine ⟨IsExt_refl gs, hG, by simp, rfl, hacc, ?_⟩
    intro v _
    simp
  | cons w ws ih =>
    intro gs acc hG hacc hws
    dsimp only [emitAndFold]
    have hw : w < N + gs.length := hws w List.mem_cons_self
    obtain ⟨hext1, hG1, hlen1, hnot1, hacc1, heval1⟩ := emitAnd_spec N gs acc w hG hacc hw
    set res1 := emitAnd N gs acc w
    have hws1 : ∀ u ∈ ws, u < N + res1.1.length := by
      intro u hu
      have := hws u (List.mem_cons_of_mem _ hu)
      omega
    obtain ⟨hext2, hG2, hlen2, hnot2, hout2, heval2⟩ := ih res1.1 res1.2 hG1 hacc1 hws1
    refine ⟨IsExt_trans hext1 hext2, hG2, by simp only [List.length_cons]; omega, hnot2.trans hnot1, hout2, ?_⟩
    intro v hv
    rw [heval2 v hv, heval1 v hv, Bool.and_eq_true]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, ?_⟩
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hmem
      · exact h2
      · have hlt := hws u (List.mem_cons_of_mem _ hmem)
        rw [← evalW_of_IsExt hext1 hv hlt]
        exact h3 u hmem
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, h2 w List.mem_cons_self⟩, ?_⟩
      intro u hu
      have hlt := hws u (List.mem_cons_of_mem _ hu)
      rw [evalW_of_IsExt hext1 hv hlt]
      exact h2 u (List.mem_cons_of_mem _ hu)

private def emitAndList (N : Nat) (gs : List Gate) (trueW : Nat) : List Nat → List Gate × Nat
  | [] => (gs, trueW)
  | w :: ws => emitAndFold N gs w ws

private lemma emitAndList_spec (N : Nat) (gs : List Gate) (trueW : Nat) (ws : List Nat)
    (hG : GoodGates N gs) (htrue : trueW < N + gs.length) (hws : ∀ u ∈ ws, u < N + gs.length) :
    let res := emitAndList N gs trueW ws
    IsExt gs res.1 ∧ GoodGates N res.1 ∧ res.1.length ≤ gs.length + ws.length ∧
    notCnt res.1 = notCnt gs ∧ res.2 < N + res.1.length ∧
    ∀ v : List Bool, v.length = N → evalW gs v trueW = true →
      (evalW res.1 v res.2 = true ↔ ∀ u ∈ ws, evalW gs v u = true) := by
  cases ws with
  | nil =>
    dsimp only [emitAndList]
    refine ⟨IsExt_refl gs, hG, by simp, rfl, htrue, ?_⟩
    intro v _ htv
    simp [htv]
  | cons w ws =>
    dsimp only [emitAndList]
    obtain ⟨hext, hG1, hlen, hnot, hout, heval⟩ :=
      emitAndFold_spec N ws gs w hG (hws w List.mem_cons_self) (fun u hu => hws u (List.mem_cons_of_mem _ hu))
    refine ⟨hext, hG1, by simp only [List.length_cons]; omega, hnot, hout, ?_⟩
    intro v hv _
    rw [heval v hv]
    constructor
    · rintro ⟨hw, hrest⟩ u hu
      rcases List.mem_cons.mp hu with rfl | hmem
      · exact hw
      · exact hrest u hmem
    · intro hall
      exact ⟨hall w List.mem_cons_self, fun u hu => hall u (List.mem_cons_of_mem _ hu)⟩

private def emitOrFold (N : Nat) (gs : List Gate) (acc : Nat) : List Nat → List Gate × Nat
  | [] => (gs, acc)
  | w :: ws =>
    let res := emitOr N gs acc w
    emitOrFold N res.1 res.2 ws

private lemma emitOrFold_spec (N : Nat) (ws : List Nat) :
    ∀ (gs : List Gate) (acc : Nat),
      GoodGates N gs → acc < N + gs.length → (∀ u ∈ ws, u < N + gs.length) →
      let res := emitOrFold N gs acc ws
      IsExt gs res.1 ∧ GoodGates N res.1 ∧ res.1.length = gs.length + ws.length ∧
      notCnt res.1 = notCnt gs ∧ res.2 < N + res.1.length ∧
      ∀ v : List Bool, v.length = N →
        (evalW res.1 v res.2 = true ↔ evalW gs v acc = true ∨ ∃ u ∈ ws, evalW gs v u = true) := by
  induction ws with
  | nil =>
    intro gs acc hG hacc _
    dsimp only [emitOrFold]
    refine ⟨IsExt_refl gs, hG, by simp, rfl, hacc, ?_⟩
    intro v _
    simp
  | cons w ws ih =>
    intro gs acc hG hacc hws
    dsimp only [emitOrFold]
    have hw : w < N + gs.length := hws w List.mem_cons_self
    obtain ⟨hext1, hG1, hlen1, hnot1, hacc1, heval1⟩ := emitOr_spec N gs acc w hG hacc hw
    set res1 := emitOr N gs acc w
    have hws1 : ∀ u ∈ ws, u < N + res1.1.length := by
      intro u hu
      have := hws u (List.mem_cons_of_mem _ hu)
      omega
    obtain ⟨hext2, hG2, hlen2, hnot2, hout2, heval2⟩ := ih res1.1 res1.2 hG1 hacc1 hws1
    refine ⟨IsExt_trans hext1 hext2, hG2, by simp only [List.length_cons]; omega, hnot2.trans hnot1, hout2, ?_⟩
    intro v hv
    rw [heval2 v hv, heval1 v hv, Bool.or_eq_true]
    constructor
    · rintro ((h1 | h2) | ⟨u, hu, h3⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, List.mem_cons_self, h2⟩
      · have hlt := hws u (List.mem_cons_of_mem _ hu)
        rw [evalW_of_IsExt hext1 hv hlt] at h3
        exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, h3⟩
    · rintro (h1 | ⟨u, hu, h2⟩)
      · exact Or.inl (Or.inl h1)
      · rcases List.mem_cons.mp hu with rfl | hmem
        · exact Or.inl (Or.inr h2)
        · have hlt := hws u (List.mem_cons_of_mem _ hmem)
          refine Or.inr ⟨u, hmem, ?_⟩
          rw [evalW_of_IsExt hext1 hv hlt]
          exact h2

private def emitOrList (N : Nat) (gs : List Gate) (falseW : Nat) : List Nat → List Gate × Nat
  | [] => (gs, falseW)
  | w :: ws => emitOrFold N gs w ws

private lemma emitOrList_spec (N : Nat) (gs : List Gate) (falseW : Nat) (ws : List Nat)
    (hG : GoodGates N gs) (hfalse : falseW < N + gs.length) (hws : ∀ u ∈ ws, u < N + gs.length) :
    let res := emitOrList N gs falseW ws
    IsExt gs res.1 ∧ GoodGates N res.1 ∧ res.1.length ≤ gs.length + ws.length ∧
    notCnt res.1 = notCnt gs ∧ res.2 < N + res.1.length ∧
    ∀ v : List Bool, v.length = N → evalW gs v falseW = false →
      (evalW res.1 v res.2 = true ↔ ∃ u ∈ ws, evalW gs v u = true) := by
  cases ws with
  | nil =>
    dsimp only [emitOrList]
    refine ⟨IsExt_refl gs, hG, by simp, rfl, hfalse, ?_⟩
    intro v _ hfv
    simp [hfv]
  | cons w ws =>
    dsimp only [emitOrList]
    obtain ⟨hext, hG1, hlen, hnot, hout, heval⟩ :=
      emitOrFold_spec N ws gs w hG (hws w List.mem_cons_self) (fun u hu => hws u (List.mem_cons_of_mem _ hu))
    refine ⟨hext, hG1, by simp only [List.length_cons]; omega, hnot, hout, ?_⟩
    intro v hv _
    rw [heval v hv]
    constructor
    · rintro (hw | ⟨u, hu, h2⟩)
      · exact ⟨w, List.mem_cons_self, hw⟩
      · exact ⟨u, List.mem_cons_of_mem _ hu, h2⟩
    · rintro ⟨u, hu, h2⟩
      rcases List.mem_cons.mp hu with rfl | hmem
      · exact Or.inl h2
      · exact Or.inr ⟨u, hmem, h2⟩

private noncomputable def buildInd0 {n m : Nat} (x : Fin m → Finset (Fin n)) :
    (k : Nat) → k ≤ m → List Gate × (Fin m → Nat)
  | 0, _ => ([], fun _ => n + 1)
  | k + 1, hk =>
    let prev := buildInd0 x k (Nat.le_of_lt hk)
    let ik : Fin m := ⟨k, hk⟩
    let ws := ((List.finRange n).filter (fun v => @decide (v ∈ x ik) (Classical.propDecidable _))).map Fin.val
    let res := emitAndList (n + 2) prev.1 (n + 1) ws
    (res.1, fun i => if i.val = k then res.2 else prev.2 i)

private lemma buildInd0_spec {n m : Nat} (x : Fin m → Finset (Fin n)) :
    ∀ (k : Nat) (hk : k ≤ m),
      let res := buildInd0 x k hk
      GoodGates (n + 2) res.1 ∧
      res.1.length ≤ k * n ∧
      notCnt res.1 = 0 ∧
      (∀ i : Fin m, i.val < k → res.2 i < n + 2 + res.1.length) ∧
      (∀ i : Fin m, i.val < k → ∀ iStar : Fin m,
        evalW res.1 (inp n (x iStar)) (res.2 i) = true ↔ x i ⊆ x iStar) := by
  intro k
  induction k with
  | zero =>
    intro _
    dsimp only [buildInd0]
    refine ⟨⟨?_, ?_⟩, by simp, by simp [notCnt], ?_, ?_⟩
    · intro g hg; cases hg
    · intro j hj; cases hj
    · intro i hi; omega
    · intro i hi; omega
  | succ k ih =>
    intro hk
    dsimp only [buildInd0]
    obtain ⟨hG, hlen, hnot, hlt, heval⟩ := ih (Nat.le_of_lt hk)
    set prev := buildInd0 x k (Nat.le_of_lt hk)
    set ik : Fin m := ⟨k, hk⟩
    set ws := ((List.finRange n).filter (fun v => @decide (v ∈ x ik) (Classical.propDecidable _))).map Fin.val
    have hws_lt : ∀ u ∈ ws, u < n + 2 + prev.1.length := by
      intro u hu
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hu
      have := v.isLt
      omega
    have hws_len : ws.length ≤ n := by
      simp only [ws, List.length_map]
      exact (List.length_filter_le _ _).trans (by simp)
    obtain ⟨hext, hG1, hlen1, hnot1, hout1, heval1⟩ :=
      emitAndList_spec (n + 2) prev.1 (n + 1) ws hG (by omega) hws_lt
    set res := emitAndList (n + 2) prev.1 (n + 1) ws
    refine ⟨hG1, ?_, hnot1.trans hnot, ?_, ?_⟩
    · calc res.1.length ≤ prev.1.length + ws.length := hlen1
        _ ≤ k * n + n := Nat.add_le_add hlen hws_len
        _ = (k + 1) * n := by rw [Nat.succ_mul]
    · intro i hi
      by_cases hik : i.val = k
      · simp only [hik, ↓reduceIte]
        exact hout1
      · simp only [hik, ↓reduceIte]
        have := hlt i (by omega)
        have := IsExt_length_le hext
        omega
    · intro i hi iStar
      by_cases hik : i.val = k
      · simp only [hik, ↓reduceIte]
        have hieq : i = ik := Fin.ext hik
        rw [hieq]
        have htrue : evalW prev.1 (inp n (x iStar)) (n + 1) = true := by
          rw [evalW_input prev.1 (length_inp n (x iStar)) (by omega), getD_inp_n1]
        rw [heval1 (inp n (x iStar)) (length_inp n (x iStar)) htrue]
        constructor
        · intro hall v hv
          have hvws : v.val ∈ ws := by
            simp only [ws, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
            exact ⟨v, cdecide_true hv, rfl⟩
          have hevv := hall v.val hvws
          rw [evalW_input prev.1 (length_inp n (x iStar)) (by have := v.isLt; omega),
            getD_inp_lt n (x iStar) v.val v.isLt] at hevv
          exact of_cdecide_true hevv
        · intro hsub u hu
          simp only [ws, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hu
          obtain ⟨v, hv, rfl⟩ := hu
          have hvik : v ∈ x ik := of_cdecide_true hv
          rw [evalW_input prev.1 (length_inp n (x iStar)) (by have := v.isLt; omega),
            getD_inp_lt n (x iStar) v.val v.isLt]
          exact cdecide_true (hsub hvik)
      · simp only [hik, ↓reduceIte]
        have hil : i.val < k := by omega
        rw [evalW_of_IsExt hext (length_inp n (x iStar)) (hlt i hil)]
        exact heval i hil iStar

private def updateInd {m t : Nat} (g : Fin m → Nat × Finset (Fin t)) (n k : Nat)
    (gsInit : List Gate) (indOld : Fin m → Nat) (notW : Nat) :
    (j : Nat) → j ≤ m → List Gate × (Fin m → Nat)
  | 0, _ => (gsInit, indOld)
  | j + 1, hj =>
    let prev := updateInd g n k gsInit indOld notW j (Nat.le_of_lt hj)
    let ij : Fin m := ⟨j, hj⟩
    if ((g ij).1 / 2 ^ k) % 2 = 1 then
      (prev.1, prev.2)
    else
      let res := emitAnd (n + 2) prev.1 (indOld ij) notW
      (res.1, fun i => if i.val = j then res.2 else prev.2 i)

private lemma updateInd_spec {m t : Nat} (g : Fin m → Nat × Finset (Fin t)) (n k : Nat)
    (gsInit : List Gate) (indOld : Fin m → Nat) (notW : Nat)
    (hG0 : GoodGates (n + 2) gsInit)
    (hind0 : ∀ i : Fin m, indOld i < n + 2 + gsInit.length)
    (hnot0 : notW < n + 2 + gsInit.length) :
    ∀ (j : Nat) (hj : j ≤ m),
      let res := updateInd g n k gsInit indOld notW j hj
      IsExt gsInit res.1 ∧
      GoodGates (n + 2) res.1 ∧
      res.1.length ≤ gsInit.length + j ∧
      notCnt res.1 = notCnt gsInit ∧
      (∀ i : Fin m, res.2 i < n + 2 + res.1.length) ∧
      (∀ i : Fin m, j ≤ i.val → res.2 i = indOld i) ∧
      (∀ i : Fin m, i.val < j → ∀ v : List Bool, v.length = n + 2 →
        evalW res.1 v (res.2 i) =
          if ((g i).1 / 2 ^ k) % 2 = 1 then evalW gsInit v (indOld i)
          else (evalW gsInit v (indOld i) && evalW gsInit v notW)) := by
  intro j
  induction j with
  | zero =>
    intro _
    dsimp only [updateInd]
    refine ⟨IsExt_refl gsInit, hG0, by simp, rfl, hind0, ?_, ?_⟩
    · intro i _; rfl
    · intro i hi; omega
  | succ j ih =>
    intro hj
    obtain ⟨hext, hG, hlen, hnot, hind, hge, hlt⟩ := ih (Nat.le_of_lt hj)
    set prev := updateInd g n k gsInit indOld notW j (Nat.le_of_lt hj)
    dsimp only [updateInd]
    by_cases hbit : ((g ⟨j, hj⟩).1 / 2 ^ k) % 2 = 1
    · simp only [hbit, ↓reduceIte]
      refine ⟨hext, hG, Nat.le_trans hlen (Nat.le_succ _), hnot, hind, ?_, ?_⟩
      · intro i hi
        exact hge i (by omega)
      · intro i hi v hv
        by_cases hij : i.val = j
        · have hieq : i = ⟨j, hj⟩ := Fin.ext hij
          rw [hieq]
          simp only [hbit, ↓reduceIte]
          rw [hge ⟨j, hj⟩ (Nat.le_refl j)]
          exact evalW_of_IsExt hext hv (hind0 ⟨j, hj⟩)
        · exact hlt i (by omega) v hv
    · simp only [hbit, ↓reduceIte]
      have hlen_ext : gsInit.length ≤ prev.1.length := IsExt_length_le hext
      have ha : indOld ⟨j, hj⟩ < n + 2 + prev.1.length := by have := hind0 ⟨j, hj⟩; omega
      have hb : notW < n + 2 + prev.1.length := by omega
      obtain ⟨hext1, hG1, hlen1, hnot1, hout1, heval1⟩ := emitAnd_spec (n + 2) prev.1 (indOld ⟨j, hj⟩) notW hG ha hb
      set res := emitAnd (n + 2) prev.1 (indOld ⟨j, hj⟩) notW
      have hlen_prev : prev.1.length ≤ gsInit.length + j := hlen
      refine ⟨IsExt_trans hext hext1, hG1, by omega, hnot1.trans hnot, ?_, ?_, ?_⟩
      · intro i
        by_cases hij : i.val = j
        · simp only [hij, ↓reduceIte]; exact hout1
        · simp only [hij, ↓reduceIte]
          have h2 : res.1.length = prev.1.length + 1 := hlen1
          exact Nat.lt_of_lt_of_le (hind i) (by change n + 2 + prev.1.length ≤ n + 2 + res.1.length; omega)
      · intro i hi
        have hne : i.val ≠ j := by omega
        simp only [hne, ↓reduceIte]
        exact hge i (by omega)
      · intro i hi v hv
        by_cases hij : i.val = j
        · simp only [hij, ↓reduceIte]
          have hieq : i = ⟨j, hj⟩ := Fin.ext hij
          rw [hieq]
          simp only [hbit, ↓reduceIte]
          rw [heval1 v hv, evalW_of_IsExt hext hv (hind0 ⟨j, hj⟩), evalW_of_IsExt hext hv hnot0]
        · simp only [hij, ↓reduceIte]
          rw [evalW_of_IsExt hext1 hv (hind i)]
          exact hlt i (by omega) v hv

private def stageStep {m t : Nat} (g : Fin m → Nat × Finset (Fin t)) (n k : Nat)
    (gs0 : List Gate) (ind0 : Fin m → Nat) : List Gate × (Fin m → Nat) :=
  let ones := ((List.finRange m).filter (fun i => decide (((g i).1 / 2 ^ k) % 2 = 1))).map ind0
  let resOr := emitOrList (n + 2) gs0 n ones
  let resNot := emitNot (n + 2) resOr.1 resOr.2
  updateInd g n k resNot.1 ind0 resNot.2 m (Nat.le_refl m)

private lemma stageStep_spec {n m t : Nat} {x : Fin m → Finset (Fin n)}
    {A : Fin m → Finset (Finset (Fin t))} {g : Fin m → Nat × Finset (Fin t)}
    (hg : greedySt x A g) (k : Nat) (gs0 : List Gate) (ind0 : Fin m → Nat)
    (hG0 : GoodGates (n + 2) gs0)
    (hind0 : ∀ i : Fin m, ind0 i < n + 2 + gs0.length)
    (hinv : ∀ i iStar : Fin m,
      evalW gs0 (inp n (x iStar)) (ind0 i) = true ↔
        x i ⊆ x iStar ∧ (g i).1 / 2 ^ (k + 1) = (g iStar).1 / 2 ^ (k + 1)) :
    let res := stageStep g n k gs0 ind0
    GoodGates (n + 2) res.1 ∧
    res.1.length ≤ gs0.length + (2 * m + 1) ∧
    notCnt res.1 = notCnt gs0 + 1 ∧
    (∀ i : Fin m, res.2 i < n + 2 + res.1.length) ∧
    (∀ i iStar : Fin m,
      evalW res.1 (inp n (x iStar)) (res.2 i) = true ↔
        x i ⊆ x iStar ∧ (g i).1 / 2 ^ k = (g iStar).1 / 2 ^ k) := by
  dsimp only [stageStep]
  set ones := ((List.finRange m).filter (fun i => decide (((g i).1 / 2 ^ k) % 2 = 1))).map ind0
  have hones_lt : ∀ u ∈ ones, u < n + 2 + gs0.length := by
    intro u hu
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hu
    exact hind0 i
  have hones_len : ones.length ≤ m := by
    simp only [ones, List.length_map]
    exact (List.length_filter_le _ _).trans (by simp)
  obtain ⟨hextOr, hGOr, hlenOr, hnotOr, houtOr, hevalOr⟩ :=
    emitOrList_spec (n + 2) gs0 n ones hG0 (by omega) hones_lt
  set resOr := emitOrList (n + 2) gs0 n ones
  obtain ⟨hextNot, hGNot, hlenNot, hnotNot, houtNot, hevalNot⟩ :=
    emitNot_spec (n + 2) resOr.1 resOr.2 hGOr houtOr
  set resNot := emitNot (n + 2) resOr.1 resOr.2
  have hext0Not : IsExt gs0 resNot.1 := IsExt_trans hextOr hextNot
  have hindNot : ∀ i : Fin m, ind0 i < n + 2 + resNot.1.length := by
    intro i
    have := hind0 i
    have := IsExt_length_le hext0Not
    omega
  obtain ⟨hextU, hGU, hlenU, hnotU, hindU, _, hevalU⟩ :=
    updateInd_spec g n k resNot.1 ind0 resNot.2 hGNot hindNot houtNot m (Nat.le_refl m)
  have hle_of_sub : ∀ i iStar : Fin m, x i ⊆ x iStar → (g i).1 ≤ (g iStar).1 := by
    intro i iStar hsub
    by_cases heq : i = iStar
    · subst heq; exact Nat.le_refl _
    · rcases (hg iStar).1.2 i heq hsub with hlt | ⟨heq1, _⟩ <;> omega
  have hdiv_step : ∀ a : Nat, a / 2 ^ (k + 1) = (a / 2 ^ k) / 2 := by
    intro a
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  have hor_sem : ∀ iStar : Fin m,
      evalW resOr.1 (inp n (x iStar)) resOr.2 = true ↔ ((g iStar).1 / 2 ^ k) % 2 = 1 := by
    intro iStar
    have hfalse : evalW gs0 (inp n (x iStar)) n = false := by
      rw [evalW_input gs0 (length_inp n (x iStar)) (by omega), getD_inp_n]
    rw [hevalOr (inp n (x iStar)) (length_inp n (x iStar)) hfalse]
    constructor
    · rintro ⟨u, hu, hevu⟩
      simp only [ones, List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hu
      obtain ⟨i, hibit, rfl⟩ := hu
      obtain ⟨hsub, hdiv⟩ := (hinv i iStar).mp hevu
      have hgle := hle_of_sub i iStar hsub
      have hqle : (g i).1 / 2 ^ k ≤ (g iStar).1 / 2 ^ k := Nat.div_le_div_right hgle
      rw [hdiv_step, hdiv_step] at hdiv
      omega
    · intro hbit
      refine ⟨ind0 iStar, ?_, ?_⟩
      · simp only [ones, List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
        exact ⟨iStar, hbit, rfl⟩
      · exact (hinv iStar iStar).mpr ⟨Finset.Subset.refl _, rfl⟩
  have hnot_sem : ∀ iStar : Fin m,
      evalW resNot.1 (inp n (x iStar)) resNot.2 = true ↔ ((g iStar).1 / 2 ^ k) % 2 = 0 := by
    intro iStar
    rw [hevalNot (inp n (x iStar)) (length_inp n (x iStar))]
    have hor := hor_sem iStar
    cases hval : evalW resOr.1 (inp n (x iStar)) resOr.2
    · simp only [Bool.not_false, true_iff]
      have hne : ((g iStar).1 / 2 ^ k) % 2 ≠ 1 := by
        intro h1
        have := hor.mpr h1
        rw [hval] at this
        cases this
      omega
    · simp only [Bool.not_true, Bool.false_eq_true, false_iff]
      have h1 := hor.mp hval
      omega
  refine ⟨hGU, by omega, by rw [hnotU, hnotNot, hnotOr], hindU, ?_⟩
  intro i iStar
  rw [hevalU i i.isLt (inp n (x iStar)) (length_inp n (x iStar))]
  by_cases hbit : ((g i).1 / 2 ^ k) % 2 = 1
  · simp only [hbit, ↓reduceIte]
    rw [evalW_of_IsExt hext0Not (length_inp n (x iStar)) (hind0 i), hinv i iStar]
    constructor
    · rintro ⟨hsub, hdiv⟩
      refine ⟨hsub, ?_⟩
      have hqle : (g i).1 / 2 ^ k ≤ (g iStar).1 / 2 ^ k := Nat.div_le_div_right (hle_of_sub i iStar hsub)
      rw [hdiv_step, hdiv_step] at hdiv
      omega
    · rintro ⟨hsub, hqeq⟩
      refine ⟨hsub, ?_⟩
      rw [hdiv_step, hdiv_step, hqeq]
  · simp only [hbit, ↓reduceIte]
    rw [Bool.and_eq_true,
      evalW_of_IsExt hext0Not (length_inp n (x iStar)) (hind0 i), hinv i iStar, hnot_sem iStar]
    constructor
    · rintro ⟨⟨hsub, hdiv⟩, hb0⟩
      refine ⟨hsub, ?_⟩
      rw [hdiv_step, hdiv_step] at hdiv
      omega
    · rintro ⟨hsub, hqeq⟩
      refine ⟨⟨hsub, ?_⟩, ?_⟩
      · rw [hdiv_step, hdiv_step, hqeq]
      · rw [← hqeq]
        omega

private def buildStages {m t : Nat} (g : Fin m → Nat × Finset (Fin t)) (n r : Nat)
    (gs0 : List Gate) (ind0 : Fin m → Nat) : Nat → List Gate × (Fin m → Nat)
  | 0 => (gs0, ind0)
  | s + 1 =>
    let prev := buildStages g n r gs0 ind0 s
    stageStep g n (r - 1 - s) prev.1 prev.2

private lemma buildStages_spec {n m t : Nat} {x : Fin m → Finset (Fin n)}
    {A : Fin m → Finset (Finset (Fin t))} {g : Fin m → Nat × Finset (Fin t)}
    (hg : greedySt x A g) (r : Nat) (hbound : ∀ i : Fin m, (g i).1 < 2 ^ r)
    (gs0 : List Gate) (ind0 : Fin m → Nat)
    (hG0 : GoodGates (n + 2) gs0) (hnot0 : notCnt gs0 = 0)
    (hind0 : ∀ i : Fin m, ind0 i < n + 2 + gs0.length)
    (hinv0 : ∀ i iStar : Fin m, evalW gs0 (inp n (x iStar)) (ind0 i) = true ↔ x i ⊆ x iStar) :
    ∀ s ≤ r,
      let res := buildStages g n r gs0 ind0 s
      GoodGates (n + 2) res.1 ∧
      res.1.length ≤ gs0.length + s * (2 * m + 1) ∧
      notCnt res.1 = s ∧
      (∀ i : Fin m, res.2 i < n + 2 + res.1.length) ∧
      (∀ i iStar : Fin m,
        evalW res.1 (inp n (x iStar)) (res.2 i) = true ↔
          x i ⊆ x iStar ∧ (g i).1 / 2 ^ (r - s) = (g iStar).1 / 2 ^ (r - s)) := by
  intro s
  induction s with
  | zero =>
    intro _
    dsimp only [buildStages]
    refine ⟨hG0, by simp, hnot0, hind0, ?_⟩
    intro i iStar
    simp only [Nat.sub_zero]
    rw [hinv0 i iStar, Nat.div_eq_of_lt (hbound i), Nat.div_eq_of_lt (hbound iStar)]
    simp
  | succ s ih =>
    intro hs
    dsimp only [buildStages]
    obtain ⟨hG, hlen, hnot, hind, hinv⟩ := ih (Nat.le_of_lt hs)
    set prev := buildStages g n r gs0 ind0 s
    have hsub1 : r - s = (r - 1 - s) + 1 := by omega
    have hinv' : ∀ i iStar : Fin m,
        evalW prev.1 (inp n (x iStar)) (prev.2 i) = true ↔
          x i ⊆ x iStar ∧ (g i).1 / 2 ^ ((r - 1 - s) + 1) = (g iStar).1 / 2 ^ ((r - 1 - s) + 1) := by
      intro i iStar
      rw [← hsub1]
      exact hinv i iStar
    obtain ⟨hG1, hlen1, hnot1, hind1, hinv1⟩ :=
      stageStep_spec hg (r - 1 - s) prev.1 prev.2 hG hind hinv'
    have hsub2 : r - (s + 1) = r - 1 - s := by omega
    refine ⟨hG1, ?_, by omega, hind1, ?_⟩
    · calc (stageStep g n (r - 1 - s) prev.1 prev.2).1.length
          ≤ prev.1.length + (2 * m + 1) := hlen1
        _ ≤ gs0.length + s * (2 * m + 1) + (2 * m + 1) := Nat.add_le_add_right hlen _
        _ = gs0.length + (s + 1) * (2 * m + 1) := by rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
    · intro i iStar
      rw [hsub2]
      exact hinv1 i iStar

private noncomputable def buildTaps {m t : Nat} (g : Fin m → Nat × Finset (Fin t)) (n : Nat)
    (gsInit : List Gate) (indR : Fin m → Nat) :
    (k : Nat) → k ≤ t → List Gate × (Fin t → Nat)
  | 0, _ => (gsInit, fun _ => n)
  | k + 1, hk =>
    let prev := buildTaps g n gsInit indR k (Nat.le_of_lt hk)
    let ak : Fin t := ⟨k, hk⟩
    let src := ((List.finRange m).filter (fun i => @decide (ak ∈ (g i).2) (Classical.propDecidable _))).map indR
    let res := emitOrList (n + 2) prev.1 n src
    (res.1, fun a => if a.val = k then res.2 else prev.2 a)

private lemma buildTaps_spec {n m t : Nat} {x : Fin m → Finset (Fin n)}
    {A : Fin m → Finset (Finset (Fin t))} {g : Fin m → Nat × Finset (Fin t)}
    (hg : greedySt x A g) (gsInit : List Gate) (indR : Fin m → Nat)
    (hG0 : GoodGates (n + 2) gsInit)
    (hind0 : ∀ i : Fin m, indR i < n + 2 + gsInit.length)
    (hinv0 : ∀ i iStar : Fin m,
      evalW gsInit (inp n (x iStar)) (indR i) = true ↔ x i ⊆ x iStar ∧ (g i).1 = (g iStar).1) :
    ∀ (k : Nat) (hk : k ≤ t),
      let res := buildTaps g n gsInit indR k hk
      IsExt gsInit res.1 ∧
      GoodGates (n + 2) res.1 ∧
      res.1.length ≤ gsInit.length + k * m ∧
      notCnt res.1 = notCnt gsInit ∧
      (∀ a : Fin t, a.val < k → res.2 a < n + 2 + res.1.length) ∧
      (∀ a : Fin t, a.val < k → ∀ iStar : Fin m,
        evalW res.1 (inp n (x iStar)) (res.2 a) = true ↔ a ∈ (g iStar).2) := by
  intro k
  induction k with
  | zero =>
    intro _
    dsimp only [buildTaps]
    refine ⟨IsExt_refl gsInit, hG0, by simp, rfl, ?_, ?_⟩
    · intro a ha; omega
    · intro a ha; omega
  | succ k ih =>
    intro hk
    dsimp only [buildTaps]
    obtain ⟨hext, hG, hlen, hnot, hlt, heval⟩ := ih (Nat.le_of_lt hk)
    set prev := buildTaps g n gsInit indR k (Nat.le_of_lt hk)
    set ak : Fin t := ⟨k, hk⟩
    set src := ((List.finRange m).filter (fun i => @decide (ak ∈ (g i).2) (Classical.propDecidable _))).map indR
    have hsrc_lt : ∀ u ∈ src, u < n + 2 + prev.1.length := by
      intro u hu
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hu
      have := hind0 i
      have := IsExt_length_le hext
      omega
    have hsrc_len : src.length ≤ m := by
      simp only [src, List.length_map]
      exact (List.length_filter_le _ _).trans (by simp)
    obtain ⟨hext1, hG1, hlen1, hnot1, hout1, heval1⟩ :=
      emitOrList_spec (n + 2) prev.1 n src hG (by omega) hsrc_lt
    set res := emitOrList (n + 2) prev.1 n src
    refine ⟨IsExt_trans hext hext1, hG1, ?_, hnot1.trans hnot, ?_, ?_⟩
    · calc res.1.length ≤ prev.1.length + src.length := hlen1
        _ ≤ gsInit.length + k * m + m := Nat.add_le_add hlen hsrc_len
        _ = gsInit.length + (k + 1) * m := by rw [Nat.succ_mul, Nat.add_assoc]
    · intro a ha
      by_cases hak : a.val = k
      · simp only [hak, ↓reduceIte]; exact hout1
      · simp only [hak, ↓reduceIte]
        have := hlt a (by omega)
        have := IsExt_length_le hext1
        omega
    · intro a ha iStar
      by_cases hak : a.val = k
      · simp only [hak, ↓reduceIte]
        have haeq : a = ak := Fin.ext hak
        rw [haeq]
        have hfalse : evalW prev.1 (inp n (x iStar)) n = false := by
          rw [evalW_input prev.1 (length_inp n (x iStar)) (by omega), getD_inp_n]
        rw [heval1 (inp n (x iStar)) (length_inp n (x iStar)) hfalse]
        constructor
        · rintro ⟨u, hu, hevu⟩
          simp only [src, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hu
          obtain ⟨i, hai, rfl⟩ := hu
          have hmemi : ak ∈ (g i).2 := of_cdecide_true hai
          rw [evalW_of_IsExt hext (length_inp n (x iStar)) (hind0 i)] at hevu
          obtain ⟨hsub, hgeq⟩ := (hinv0 i iStar).mp hevu
          by_cases hieq : i = iStar
          · subst hieq; exact hmemi
          · rcases (hg iStar).1.2 i hieq hsub with hlt1 | ⟨_, hsub2⟩
            · omega
            · exact hsub2 hmemi
        · intro hmem
          refine ⟨indR iStar, ?_, ?_⟩
          · simp only [src, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
            exact ⟨iStar, cdecide_true hmem, rfl⟩
          · rw [evalW_of_IsExt hext (length_inp n (x iStar)) (hind0 iStar)]
            exact (hinv0 iStar iStar).mpr ⟨Finset.Subset.refl _, rfl⟩
      · simp only [hak, ↓reduceIte]
        have hal : a.val < k := by omega
        rw [evalW_of_IsExt hext1 (length_inp n (x iStar)) (hlt a hal)]
        exact heval a hal iStar

private lemma size_arith (m n r t : Nat) :
    m * n + r * (2 * m + 1) + t * m = m * (n + 2 * r + t) + r := by
  have h1 : r * (2 * m + 1) = r * (2 * m) + r := by rw [Nat.mul_add, Nat.mul_one]
  have h2 : r * (2 * m) = m * (2 * r) := by
    calc r * (2 * m) = 2 * m * r := Nat.mul_comm _ _
      _ = m * 2 * r := by rw [Nat.mul_comm 2 m]
      _ = m * (2 * r) := Nat.mul_assoc _ _ _
  have h3 : t * m = m * t := Nat.mul_comm t m
  have h4 : m * (n + 2 * r + t) = m * n + m * (2 * r) + m * t := by
    rw [Nat.mul_add, Nat.mul_add]
  omega

private lemma realize_greedy {n m t : Nat} {x : Fin m → Finset (Fin n)}
    {A : Fin m → Finset (Finset (Fin t))} {g : Fin m → Nat × Finset (Fin t)}
    (hg : greedySt x A g) (r : Nat) (hbound : ∀ i : Fin m, (g i).1 < 2 ^ r) :
    ∃ (C : Circuit) (tap : Fin t → Nat),
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C ∧
      C.output < n + 2 + C.size ∧
      (∀ a, tap a < n + 2 + C.size) ∧
      PEqualNP.NotBracket.notCount C ≤ r ∧
      C.size ≤ m * (n + 2 * r + t) + r ∧
      ∀ i a, (C.wires (inp n (x i))).getD (tap a) false =
        @decide (a ∈ (g i).2) (Classical.propDecidable _) := by
  obtain ⟨hG0, hlen0, hnot0, hind0, heval0⟩ := buildInd0_spec x m (Nat.le_refl m)
  set res0 := buildInd0 x m (Nat.le_refl m)
  have hind0' : ∀ i : Fin m, res0.2 i < n + 2 + res0.1.length := fun i => hind0 i i.isLt
  have heval0' : ∀ i iStar : Fin m, evalW res0.1 (inp n (x iStar)) (res0.2 i) = true ↔ x i ⊆ x iStar :=
    fun i iStar => heval0 i i.isLt iStar
  obtain ⟨hGr, hlenr, hnotr, hindr, hevalr⟩ :=
    buildStages_spec hg r hbound res0.1 res0.2 hG0 hnot0 hind0' heval0' r (Nat.le_refl r)
  set resr := buildStages g n r res0.1 res0.2 r
  have hevalr' : ∀ i iStar : Fin m,
      evalW resr.1 (inp n (x iStar)) (resr.2 i) = true ↔ x i ⊆ x iStar ∧ (g i).1 = (g iStar).1 := by
    intro i iStar
    simpa using hevalr i iStar
  obtain ⟨_, hGf, hlenf, hnotf, htapf, hevalf⟩ :=
    buildTaps_spec hg resr.1 resr.2 hGr hindr hevalr' t (Nat.le_refl t)
  set resf := buildTaps g n resr.1 resr.2 t (Nat.le_refl t)
  refine ⟨⟨resf.1, 0⟩, resf.2, hGf.1, hGf.2, by dsimp only [Circuit.size]; omega, ?_, ?_, ?_, ?_⟩
  · intro a
    exact htapf a a.isLt
  · rw [notCount_eq_filter_isNotOp]
    change notCnt resf.1 ≤ r
    rw [hnotf, hnotr]
  · change resf.1.length ≤ m * (n + 2 * r + t) + r
    have hsum := size_arith m n r t
    omega
  · intro i a
    have hiff := hevalf a a.isLt i
    change evalW resf.1 (inp n (x i)) (resf.2 a) = @decide (a ∈ (g i).2) (Classical.propDecidable _)
    by_cases ha : a ∈ (g i).2
    · rw [cdecide_true ha]
      exact hiff.mpr ha
    · rw [cdecide_false ha]
      cases hval : evalW resf.1 (inp n (x i)) (resf.2 a)
      · rfl
      · exact False.elim (ha (hiff.mp hval))

private lemma necessity_greedy {n m t : Nat} {x : Fin m → Finset (Fin n)}
    {A : Fin m → Finset (Finset (Fin t))} (hx : Function.Injective x)
    {g : Fin m → Nat × Finset (Fin t)} (hg : greedySt x A g)
    {r : Nat} {C : Circuit} {tap : Fin t → Nat}
    (hFan : PEqualNP.MetaComplexity.FanInTwo C)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    (hTap : ∀ a, tap a < n + 2 + C.size)
    (hNot : PEqualNP.NotBracket.notCount C ≤ r)
    (hMem : ∀ i, ∃ s ∈ A i, ∀ a : Fin t, a ∈ s ↔ wireVal n C (x i) (tap a) = true) :
    ∀ i : Fin m, (g i).1 < 2 ^ r := by
  have hb_le : B_cntList C.gates C.gates.length ≤ r := by
    rw [B_cntList_length, ← notCount_eq_filter_isNotOp]
    exact hNot
  have hV_lt : ∀ i : Fin m, V n C (x i) C.gates.length < 2 ^ r := by
    intro i
    have h1 := V_lt_pow n C (x i) C.gates.length
    have h2 : 2 ^ B_cntList C.gates C.gates.length ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hb_le
    omega
  let h : Fin m → Nat × Finset (Fin t) := fun i =>
    (2 ^ r - 1 - V n C (x i) C.gates.length,
      Finset.univ.filter (fun a => wireVal n C (x i) (tap a) = true))
  have hcand : ∀ i : Fin m, candSt x A h i (h i) := by
    intro i
    refine ⟨?_, ?_⟩
    · obtain ⟨s, hsA, hs_iff⟩ := hMem i
      have heq : (h i).2 = s := by
        apply Finset.ext
        intro a
        simp only [h, Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hs_iff a).symm
      rw [heq]
      exact hsA
    · intro j hji hsub
      obtain ⟨hle, hmono⟩ := V_anti_and_mono_wires n C hFan hRB hsub C.gates.length (Nat.le_refl _)
      have hVi := hV_lt i
      have hVj := hV_lt j
      by_cases hlt : V n C (x i) C.gates.length < V n C (x j) C.gates.length
      · exact Or.inl (by dsimp only [h]; omega)
      · have hveq : V n C (x i) C.gates.length = V n C (x j) C.gates.length := by omega
        refine Or.inr ⟨by dsimp only [h]; rw [hveq], ?_⟩
        intro a ha
        simp only [h, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        exact hmono hveq (tap a) (hTap a) ha
  intro i
  have hbef := greedySt_least hx hg hcand i
  have hpow : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  rcases hbef with hlt | ⟨heq, _⟩
  · dsimp only [h] at hlt
    omega
  · dsimp only [h] at heq
    omega

end PEqualNP.Outside.L_lib_1301

theorem PEqualNP.Outside.L_lib_1301 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n m t : Nat) (x : Fin m → Finset (Fin n)) (A : Fin m → Finset (Finset (Fin t))),
  Function.Injective x → (∀ i, (A i).Nonempty) →
  (∀ i a b, a ∈ A i → b ∈ A i → a ∩ b ∈ A i) →
  let st := Nat × Finset (Fin t)
  let before := fun (a b : st) => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ⊆ b.2)
  let candidate := fun (g : Fin m → st) (i : Fin m) (b : st) =>
    b.2 ∈ A i ∧ ∀ j, j ≠ i → x j ⊆ x i → before (g j) b
  let greedy := fun (g : Fin m → st) => ∀ i,
    candidate g i (g i) ∧ ∀ b, candidate g i b → before (g i) b
  let fit := fun (r : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ (∀ a, tap a < n+2+C.size) ∧ PEqualNP.NotBracket.notCount C ≤ r ∧
    ∀ i, (Finset.univ.filter (fun a =>
      (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false,true])).getD (tap a) false = true)) ∈ A i
  (∃! g, greedy g) ∧ ∀ g, greedy g →
    (∀ i, (g i).1 ≤ (x i).card) ∧
    (∀ h, (∀ i, candidate h i (h i)) → ∀ i, before (g i) (h i)) ∧
    ∀ r, ((∃ C tap, fit r C tap) ↔ ∀ i, (g i).1 < 2^r) ∧
      ((∀ i, (g i).1 < 2^r) → ∃ C tap, fit r C tap ∧ C.size ≤ m*(n+2*r+t)+r ∧
        ∀ i a, (C.wires (List.ofFn (fun j : Fin n => decide (j ∈ x i)) ++ [false,true])).getD (tap a) false =
          decide (a ∈ (g i).2))) := by
  intro n m t x A hx hAne hAcl st before candidate greedy fit
  have hAcl' : ∀ i a b, a ∈ A i → b ∈ A i → ∃ c ∈ A i, ∀ u, u ∈ c ↔ u ∈ a ∧ u ∈ b :=
    fun i a b ha hb => ⟨_, hAcl i a b ha hb, fun _ =>
      @Finset.mem_inter (Fin t) (fun u v => Classical.propDecidable (u = v)) _ _ _⟩
  have hgs : PEqualNP.Outside.L_lib_1301.greedySt x A (PEqualNP.Outside.L_lib_1301.gStar x A) :=
    PEqualNP.Outside.L_lib_1301.gStar_greedy hx hAne hAcl'
  refine ⟨⟨PEqualNP.Outside.L_lib_1301.gStar x A, hgs, fun g hg =>
    PEqualNP.Outside.L_lib_1301.greedySt_unique hx hg hgs⟩, ?_⟩
  intro g hg
  have hgeq : g = PEqualNP.Outside.L_lib_1301.gStar x A :=
    PEqualNP.Outside.L_lib_1301.greedySt_unique hx hg hgs
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [hgeq]
    exact PEqualNP.Outside.L_lib_1301.gStar_level_le_card hx i
  · intro h hh i
    exact PEqualNP.Outside.L_lib_1301.greedySt_least hx hg hh i
  · intro r
    have hreal : (∀ i, (g i).1 < 2 ^ r) →
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin t → Nat),
          fit r C tap ∧ C.size ≤ m * (n + 2 * r + t) + r ∧
          ∀ i a, (C.wires (PEqualNP.Outside.L_lib_1301.inp n (x i))).getD (tap a) false =
            @decide (a ∈ (g i).2) (Classical.propDecidable _) := by
      intro hbound
      obtain ⟨C, tap, hFan, hRB, hOut, hTap, hNot, hSize, hEval⟩ :=
        PEqualNP.Outside.L_lib_1301.realize_greedy hg r hbound
      refine ⟨C, tap, ⟨hFan, hRB, hOut, hTap, hNot, ?_⟩, hSize, hEval⟩
      intro i
      have hfilt : (@Finset.filter (Fin t) (fun a =>
          (C.wires (PEqualNP.Outside.L_lib_1301.inp n (x i))).getD (tap a) false = true)
          (fun _ => Classical.propDecidable _) Finset.univ) = (g i).2 := by
        apply Finset.ext
        intro a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hEval i a]
        exact @decide_eq_true_iff (a ∈ (g i).2) (Classical.propDecidable _)
      change (@Finset.filter (Fin t) (fun a =>
          (C.wires (PEqualNP.Outside.L_lib_1301.inp n (x i))).getD (tap a) false = true)
          (fun _ => Classical.propDecidable _) Finset.univ) ∈ A i
      rw [hfilt]
      exact (hg i).1.1
    refine ⟨⟨?_, ?_⟩, hreal⟩
    · rintro ⟨C, tap, hFan, hRB, _, hTap, hNot, hMem⟩
      have hMem' : ∀ i, ∃ s ∈ A i, ∀ a : Fin t, a ∈ s ↔
          PEqualNP.Outside.L_lib_1301.wireVal n C (x i) (tap a) = true := by
        intro i
        refine ⟨_, hMem i, ?_⟩
        intro a
        simp [PEqualNP.Outside.L_lib_1301.wireVal, PEqualNP.Outside.L_lib_1301.inp]
      exact PEqualNP.Outside.L_lib_1301.necessity_greedy hx hg hFan hRB hTap hNot hMem'
    · intro hbound
      obtain ⟨C, tap, hfit, _, _⟩ := hreal hbound
      exact ⟨C, tap, hfit⟩
