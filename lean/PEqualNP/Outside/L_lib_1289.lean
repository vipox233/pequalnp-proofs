import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1289

open PEqualNP.CircuitLowerBounds

private abbrev PairT := {p : Fin 3 × Fin 3 // p.1 ≠ p.2}

private abbrev IxT (n : Nat) := Fin n × Option PairT

private lemma decide_irrel (P : Prop) (d1 d2 : Decidable P) : @decide P d1 = @decide P d2 := by
  by_cases hp : P <;> simp [hp]

private lemma cdecide_true {P : Prop} (h : P) :
    @decide P (Classical.propDecidable P) = true :=
  @decide_eq_true P (Classical.propDecidable P) h

private lemma cdecide_false {P : Prop} (h : ¬P) :
    @decide P (Classical.propDecidable P) = false :=
  @decide_eq_false P (Classical.propDecidable P) h

private lemma of_cdecide_true {P : Prop} (h : @decide P (Classical.propDecidable P) = true) : P :=
  @of_decide_eq_true P (Classical.propDecidable P) h

private lemma of_cdecide_false {P : Prop} (h : @decide P (Classical.propDecidable P) = false) : ¬P :=
  @of_decide_eq_false P (Classical.propDecidable P) h

private def pairOfFin6 : Fin 6 → PairT
  | ⟨0, _⟩ => ⟨(0, 1), by decide⟩
  | ⟨1, _⟩ => ⟨(0, 2), by decide⟩
  | ⟨2, _⟩ => ⟨(1, 0), by decide⟩
  | ⟨3, _⟩ => ⟨(1, 2), by decide⟩
  | ⟨4, _⟩ => ⟨(2, 0), by decide⟩
  | ⟨5, _⟩ => ⟨(2, 1), by decide⟩

private def fin6OfPair (x : PairT) : Fin 6 :=
  match x.1.1.val, x.1.2.val with
  | 0, 1 => ⟨0, by decide⟩
  | 0, 2 => ⟨1, by decide⟩
  | 1, 0 => ⟨2, by decide⟩
  | 1, 2 => ⟨3, by decide⟩
  | 2, 0 => ⟨4, by decide⟩
  | _, _ => ⟨5, by decide⟩

private lemma pairOfFin6_fin6OfPair (x : PairT) : pairOfFin6 (fin6OfPair x) = x := by
  rcases x with ⟨⟨a, b⟩, hab⟩
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | rfl

private lemma fin6OfPair_pairOfFin6 (k : Fin 6) : fin6OfPair (pairOfFin6 k) = k := by
  fin_cases k <;> rfl

private def optPairToFin7 : Option PairT → Fin 7
  | none => ⟨0, by decide⟩
  | some p => ⟨(fin6OfPair p).val + 1, by have := (fin6OfPair p).isLt; omega⟩

private def fin7ToOptPair : Fin 7 → Option PairT
  | ⟨0, _⟩ => none
  | ⟨k + 1, hk⟩ => some (pairOfFin6 ⟨k, by omega⟩)

private lemma optPair_left_inv (o : Option PairT) : fin7ToOptPair (optPairToFin7 o) = o := by
  cases o with
  | none => rfl
  | some p =>
    simp only [optPairToFin7, fin7ToOptPair]
    exact congrArg some (pairOfFin6_fin6OfPair p)

private lemma optPair_right_inv (k : Fin 7) : optPairToFin7 (fin7ToOptPair k) = k := by
  rcases k with ⟨v, hv⟩
  cases v with
  | zero => rfl
  | succ k =>
    simp only [fin7ToOptPair, optPairToFin7]
    apply Fin.ext
    have h := congrArg Fin.val (fin6OfPair_pairOfFin6 ⟨k, by omega⟩)
    simpa using h

private def ixEquivFin7n (n : Nat) : IxT n ≃ Fin (7 * n) where
  toFun x := ⟨7 * x.1.val + (optPairToFin7 x.2).val, by
    have h1 := x.1.isLt
    have h2 := (optPairToFin7 x.2).isLt
    omega⟩
  invFun k := (⟨k.val / 7, by have := k.isLt; omega⟩, fin7ToOptPair ⟨k.val % 7, by omega⟩)
  left_inv x := by
    rcases x with ⟨u, o⟩
    have h2 := (optPairToFin7 o).isLt
    have hdiv : (7 * u.val + (optPairToFin7 o).val) / 7 = u.val := by omega
    have hmod : (7 * u.val + (optPairToFin7 o).val) % 7 = (optPairToFin7 o).val := by omega
    apply Prod.ext
    · exact Fin.ext hdiv
    · dsimp only
      have hfin : (⟨(7 * u.val + (optPairToFin7 o).val) % 7, by omega⟩ : Fin 7) = optPairToFin7 o :=
        Fin.ext hmod
      rw [hfin]
      exact optPair_left_inv o
  right_inv k := by
    apply Fin.ext
    dsimp only
    have h := congrArg Fin.val (optPair_right_inv ⟨k.val % 7, by omega⟩)
    dsimp only at h
    rw [h]
    omega

private lemma card_ix_eq (n : Nat) (inst : Fintype (IxT n)) : @Fintype.card (IxT n) inst = 7 * n := by
  have h1 := @Fintype.card_congr (IxT n) (Fin (7 * n)) inst _ (ixEquivFin7n n)
  rw [h1, Fintype.card_fin]

private lemma getD_append_left {α : Type _} (l1 l2 : List α) (i : Nat) (d : α)
    (hi : i < l1.length) : (l1 ++ l2).getD i d = l1.getD i d := by
  induction l1 generalizing i with
  | nil => cases hi
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (Nat.lt_of_succ_lt_succ hi)

private lemma getD_append_right {α : Type _} (l1 l2 : List α) (i : Nat) (d : α)
    (hi : l1.length ≤ i) : (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  induction l1 generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simp at hi
    | succ i =>
      simp only [List.cons_append, List.getD_cons_succ, List.length_cons, Nat.succ_sub_succ_eq_sub]
      exact ih i (Nat.le_of_succ_le_succ hi)

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

private lemma getD_replicate_lt {α : Type _} (k : Nat) (a d : α) (i : Nat) (hi : i < k) :
    (List.replicate k a).getD i d = a := by
  have hlen : i < (List.replicate k a).length := by simp [hi]
  rw [getD_eq_getElem _ _ _ hlen]
  simp

private lemma getD_ofFn_lt {α : Type _} {k : Nat} (f : Fin k → α) (d : α) (i : Nat) (hi : i < k) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  have hlen : i < (List.ofFn f).length := by simp [hi]
  rw [getD_eq_getElem _ _ _ hlen]
  simp

private lemma length_filterMap_le {α β : Type _} (f : α → Option β) (l : List α) :
    (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filterMap_cons, List.length_cons]
    cases f a <;> simp <;> omega

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

private def wireEval (C : Circuit) (y : List Bool) (u : Nat) : Bool :=
  (C.wires y).getD u false

private lemma wireEval_eq_foldl (C : Circuit) (y : List Bool) (u : Nat) :
    wireEval C y u = (C.gates.foldl stepWire y).getD u false := rfl

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
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

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
      have hlen : v.length < (stepWire v g).length := by simp [stepWire]
      rw [getD_foldl_stepWire_of_lt gs (stepWire v g) v.length hlen]
      simp only [stepWire, getD_append_right_eq]
      congr 1
      apply map_eq_of_forall
      intro i hi
      have hiv : i < v.length := by have := hRB i hi; omega
      have hiv' : i < (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]).length := by
        simp; omega
      rw [getD_foldl_stepWire_of_lt gs _ i hiv', getD_append_left v _ i false hiv]
    | succ k =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      have hlen : (stepWire v g).length = v.length + 1 := by simp [stepWire]
      have heq : v.length + (k + 1) = (stepWire v g).length + k := by omega
      rw [heq]
      apply ih (stepWire v g) k (Nat.lt_of_succ_lt_succ hk)
      intro i hi
      have := hRB i hi
      omega

private lemma wireEval_eval_at_gate (N : Nat) (C : Circuit)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack N C)
    (y : List Bool) (hy : y.length = N) (k : Nat) (hk : k < C.gates.length) :
    wireEval C y (N + k) =
      C.gates[k].op.eval (C.gates[k].inputs.map fun i => wireEval C y i) := by
  rw [wireEval_eq_foldl]
  conv_lhs => rw [← hy]
  apply getD_foldl_at C.gates y k hk
  intro i hi
  rw [hy]
  have h1 := hRB k hk i
  dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at h1
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
  | zero => simp [B_cntList, isNotGateList]
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

private def notCountList (gs : List Gate) : Nat :=
  (gs.filter fun g => isNotOp g.op).length

private lemma notCount_eq_notCountList (C : Circuit) :
    PEqualNP.NotBracket.notCount C = notCountList C.gates := by
  dsimp only [PEqualNP.NotBracket.notCount, notCountList]
  congr 1
  apply congrArg (fun fn => C.gates.filter fn)
  funext g
  exact decide_eq_not g.op _

private lemma B_cntList_eq_notCount (C : Circuit) :
    B_cntList C.gates C.gates.length = PEqualNP.NotBracket.notCount C := by
  rw [B_cntList_length]
  exact (notCount_eq_notCountList C).symm

private def V (N : Nat) (C : Circuit) (y : List Bool) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    if isNotGateList C.gates k then
      2 * V N C y k + if wireEval C y (N + k) then 1 else 0
    else
      V N C y k

private lemma V_lt_pow (N : Nat) (C : Circuit) (y : List Bool) (k : Nat) :
    V N C y k < 2 ^ B_cntList C.gates k := by
  induction k with
  | zero => simp [V, B_cntList]
  | succ k ih =>
    simp only [V, B_cntList]
    cases h : isNotGateList C.gates k
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact ih
    · simp only [↓reduceIte]
      rw [Nat.pow_succ]
      cases wireEval C y (N + k) <;> simp <;> omega

private lemma all_id_mono {α : Type _} (l : List α) (f g : α → Bool)
    (h : ∀ a ∈ l, f a = true → g a = true) :
    (l.map f).all id = true → (l.map g).all id = true := by
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons, id_eq, Bool.and_eq_true]
    intro ⟨ha, hl⟩
    exact ⟨h a List.mem_cons_self ha, ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) hl⟩

private lemma any_id_mono {α : Type _} (l : List α) (f g : α → Bool)
    (h : ∀ a ∈ l, f a = true → g a = true) :
    (l.map f).any id = true → (l.map g).any id = true := by
  induction l with
  | nil => intro h0; cases h0
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, id_eq, Bool.or_eq_true]
    intro h0
    rcases h0 with ha | hl
    · exact Or.inl (h a List.mem_cons_self ha)
    · exact Or.inr (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) hl)

private def ListLe (y z : List Bool) : Prop :=
  y.length = z.length ∧ ∀ q < y.length, y.getD q false = true → z.getD q false = true

private lemma V_anti_and_mono_wires (N : Nat) (C : Circuit)
    (hFan : PEqualNP.MetaComplexity.FanInTwo C)
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack N C)
    {y z : List Bool} (hy : y.length = N) (hz : z.length = N) (hyz : ListLe y z) :
    ∀ k ≤ C.gates.length,
      V N C z k ≤ V N C y k ∧
      (V N C z k = V N C y k → ∀ u < N + k, wireEval C y u = true → wireEval C z u = true) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨Nat.le_refl _, ?_⟩
    intro _ u hu hyu
    rw [wireEval_eq_foldl] at hyu ⊢
    have hlu : u < y.length := by omega
    have hlv : u < z.length := by omega
    rw [getD_foldl_stepWire_of_lt C.gates y u hlu] at hyu
    rw [getD_foldl_stepWire_of_lt C.gates z u hlv]
    exact hyz.2 u hlu hyu
  | succ k ih =>
    intro hk1
    have hk : k < C.gates.length := Nat.lt_of_succ_le hk1
    obtain ⟨ihLe, ihMono⟩ := ih (Nat.le_of_lt hk)
    have hgate_mem : C.gates[k] ∈ C.gates := List.getElem_mem hk
    have hgate_op := (hFan C.gates[k] hgate_mem).1
    have hrb_k : ∀ i ∈ C.gates[k].inputs, i < N + k := by
      intro i hi
      have h1 := hRB k hk i
      dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at h1
      rw [getD_eq_getElem C.gates k _ hk] at h1
      exact h1 hi
    have heval_y := wireEval_eval_at_gate N C hRB y hy k hk
    have heval_z := wireEval_eval_at_gate N C hRB z hz k hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate_op
    rcases hgate_op with hop | hop | hop
    · have hnot : isNotGateList C.gates k = false := by
        simp [isNotGateList, hk, hop, isNotOp]
      simp only [V, hnot, Bool.false_eq_true, ↓reduceIte]
      refine ⟨ihLe, ?_⟩
      intro hveq u hu hyu
      by_cases huk : u < N + k
      · exact ihMono hveq u huk hyu
      · have hueq : u = N + k := by omega
        subst hueq
        rw [heval_y, hop, GateOp.eval] at hyu
        rw [heval_z, hop, GateOp.eval]
        exact all_id_mono C.gates[k].inputs (wireEval C y) (wireEval C z)
          (fun i hi => ihMono hveq i (hrb_k i hi)) hyu
    · have hnot : isNotGateList C.gates k = false := by
        simp [isNotGateList, hk, hop, isNotOp]
      simp only [V, hnot, Bool.false_eq_true, ↓reduceIte]
      refine ⟨ihLe, ?_⟩
      intro hveq u hu hyu
      by_cases huk : u < N + k
      · exact ihMono hveq u huk hyu
      · have hueq : u = N + k := by omega
        subst hueq
        rw [heval_y, hop, GateOp.eval] at hyu
        rw [heval_z, hop, GateOp.eval]
        exact any_id_mono C.gates[k].inputs (wireEval C y) (wireEval C z)
          (fun i hi => ihMono hveq i (hrb_k i hi)) hyu
    · have hnot : isNotGateList C.gates k = true := by
        simp [isNotGateList, hk, hop, isNotOp]
      simp only [V, hnot, ↓reduceIte]
      by_cases hlt : V N C z k < V N C y k
      · constructor
        · cases wireEval C z (N + k) <;> cases wireEval C y (N + k) <;>
            simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
        · intro heq
          exfalso
          cases hz1 : wireEval C z (N + k) <;> cases hy1 : wireEval C y (N + k) <;>
            simp only [hz1, hy1, Bool.false_eq_true, ↓reduceIte] at heq <;> omega
      · have hveq : V N C z k = V N C y k := by omega
        have hbit : wireEval C z (N + k) = true → wireEval C y (N + k) = true := by
          intro hztrue
          rw [heval_z, hop, GateOp.eval] at hztrue
          rw [heval_y, hop, GateOp.eval]
          cases hins : C.gates[k].inputs with
          | nil => simp
          | cons i0 rest =>
            simp only [hins, List.map_cons, List.headD_cons] at hztrue ⊢
            cases hzi0 : wireEval C z i0
            · cases hyi0 : wireEval C y i0
              · rfl
              · have hi0 : i0 < N + k := hrb_k i0 (by simp [hins])
                have hcontr := ihMono hveq i0 hi0 hyi0
                rw [hzi0] at hcontr
                cases hcontr
            · rw [hzi0] at hztrue
              cases hztrue
        constructor
        · cases hz1 : wireEval C z (N + k)
          · cases hy1 : wireEval C y (N + k) <;> simp <;> omega
          · have hy1 := hbit hz1
            rw [hy1]
            simp [hveq]
        · intro hveq1 u hu hyu
          by_cases huk : u < N + k
          · exact ihMono hveq u huk hyu
          · have hueq : u = N + k := by omega
            subst hueq
            rw [hyu] at hveq1
            cases hz1 : wireEval C z (N + k)
            · rw [hz1] at hveq1
              simp at hveq1
              omega
            · rfl

private noncomputable def edgeRel {n : Nat} (E : Fin n → Fin n → Prop) (i j : IxT n) : Prop :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  if i.2 = none ∧ j.2 = none then E i.1 j.1
  else i.1 = j.1 ∧ (i.2 = none ∨ j.2 = none ∨ i.2 = j.2)

private noncomputable def leftVec {n h : Nat} (key : Fin h ≃ IxT n) (i : IxT n) : List Bool :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  List.ofFn (fun k : Fin h => decide (key k = i)) ++ List.replicate h false

private noncomputable def rightVec {n h : Nat} (E : Fin n → Fin n → Prop) (key : Fin h ≃ IxT n)
    (j : IxT n) : List Bool :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  List.ofFn (fun k : Fin h => decide (edgeRel E (key k) j)) ++
    List.ofFn (fun k : Fin h => decide (key k = j))

private def clockFull (h m r : Nat) : List Bool :=
  List.replicate (2 * h) false ++ List.ofFn (fun i : Fin m => decide (i.val < r)) ++ [false, true]

private lemma length_leftVec {n h : Nat} (key : Fin h ≃ IxT n) (i : IxT n) :
    (leftVec key i).length = 2 * h := by
  simp [leftVec]
  omega

private lemma length_rightVec {n h : Nat} (E : Fin n → Fin n → Prop) (key : Fin h ≃ IxT n)
    (j : IxT n) : (rightVec E key j).length = 2 * h := by
  simp [rightVec]
  omega

private lemma length_clockFull (h m r : Nat) : (clockFull h m r).length = 2 * h + m + 2 := by
  simp [clockFull]
  omega

private lemma length_leftFull {n h : Nat} (key : Fin h ≃ IxT n) (m : Nat) (i : IxT n) :
    (leftVec key i ++ List.replicate m true ++ [false, true]).length = 2 * h + m + 2 := by
  simp [length_leftVec]
  omega

private lemma length_rightFull {n h : Nat} (E : Fin n → Fin n → Prop) (key : Fin h ≃ IxT n)
    (m : Nat) (j : IxT n) :
    (rightVec E key j ++ List.replicate m true ++ [false, true]).length = 2 * h + m + 2 := by
  simp [length_rightVec]
  omega

private lemma clockFull_eq_fin (h m : Nat) (j : Fin m) :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    List.replicate (2 * h) false ++ List.ofFn (fun i : Fin m => decide (i < j)) ++ [false, true] =
      clockFull h m j.val := by
  dsimp only [clockFull]
  congr 2
  apply congrArg List.ofFn
  funext i
  exact decide_irrel (i.val < j.val) _ _

private lemma clockFull_m_eq (h m : Nat) :
    clockFull h m m = List.replicate (2 * h) false ++ List.replicate m true ++ [false, true] := by
  dsimp only [clockFull]
  congr 2
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn, List.getElem_replicate]
    simp at h1
    simp [h1]

private lemma listLe_clockFull (h m r1 r2 : Nat) (hr : r1 ≤ r2) :
    ListLe (clockFull h m r1) (clockFull h m r2) := by
  refine ⟨by simp [length_clockFull], ?_⟩
  intro q hq htrue
  rw [length_clockFull] at hq
  dsimp only [clockFull] at htrue ⊢
  by_cases h1 : q < 2 * h + m
  · have hlen1 : q < (List.replicate (2 * h) false ++ List.ofFn (fun i : Fin m => decide (i.val < r1))).length := by
      simp [h1]
    have hlen2 : q < (List.replicate (2 * h) false ++ List.ofFn (fun i : Fin m => decide (i.val < r2))).length := by
      simp [h1]
    rw [getD_append_left _ _ _ _ hlen1] at htrue
    rw [getD_append_left _ _ _ _ hlen2]
    by_cases h2 : q < 2 * h
    · have hl : q < (List.replicate (2 * h) false).length := by simp [h2]
      rw [getD_append_left _ _ _ _ hl, getD_replicate_lt _ _ _ _ h2] at htrue
      cases htrue
    · have hl : (List.replicate (2 * h) false).length ≤ q := by simp; omega
      rw [getD_append_right _ _ _ _ hl] at htrue ⊢
      have hqm : q - (List.replicate (2 * h) false).length < m := by simp; omega
      rw [getD_ofFn_lt _ _ _ hqm] at htrue ⊢
      simp at htrue ⊢
      omega
  · have hlen1 : (List.replicate (2 * h) false ++ List.ofFn (fun i : Fin m => decide (i.val < r1))).length ≤ q := by
      simp; omega
    have hlen2 : (List.replicate (2 * h) false ++ List.ofFn (fun i : Fin m => decide (i.val < r2))).length ≤ q := by
      simp; omega
    rw [getD_append_right _ _ _ _ hlen1] at htrue
    rw [getD_append_right _ _ _ _ hlen2]
    have hlenEq :
        (List.replicate (2 * h) false ++ List.ofFn (fun i : Fin m => decide (i.val < r1))).length =
        (List.replicate (2 * h) false ++ List.ofFn (fun i : Fin m => decide (i.val < r2))).length := by
      simp
    rw [← hlenEq]
    exact htrue

private lemma listLe_clockFull_shore (h m : Nat) (s : List Bool) (hs : s.length = 2 * h) :
    ListLe (clockFull h m m) (s ++ List.replicate m true ++ [false, true]) := by
  rw [clockFull_m_eq]
  refine ⟨by simp [hs], ?_⟩
  intro q hq htrue
  by_cases h1 : q < 2 * h
  · have hl1 : q < (List.replicate (2 * h) false ++ List.replicate m true).length := by simp; omega
    rw [getD_append_left _ _ _ _ hl1] at htrue
    have hl2 : q < (List.replicate (2 * h) false).length := by simp [h1]
    rw [getD_append_left _ _ _ _ hl2, getD_replicate_lt _ _ _ _ h1] at htrue
    cases htrue
  · rw [List.append_assoc] at htrue ⊢
    have hl1 : (List.replicate (2 * h) false).length ≤ q := by simp; omega
    have hl2 : s.length ≤ q := by omega
    rw [getD_append_right _ _ _ _ hl1] at htrue
    rw [getD_append_right _ _ _ _ hl2]
    have heq : s.length = (List.replicate (2 * h) false).length := by simp [hs]
    rw [heq]
    exact htrue

private lemma listLe_left_right {n h m : Nat} (E : Fin n → Fin n → Prop) (key : Fin h ≃ IxT n)
    (i j : IxT n) (hed : edgeRel E i j) :
    ListLe (leftVec key i ++ List.replicate m true ++ [false, true])
      (rightVec E key j ++ List.replicate m true ++ [false, true]) := by
  refine ⟨by simp [length_leftVec, length_rightVec], ?_⟩
  intro q hq htrue
  rw [List.append_assoc] at htrue ⊢
  by_cases h1 : q < 2 * h
  · have hl1 : q < (leftVec key i).length := by rw [length_leftVec]; exact h1
    have hl2 : q < (rightVec E key j).length := by rw [length_rightVec]; exact h1
    rw [getD_append_left _ _ _ _ hl1] at htrue
    rw [getD_append_left _ _ _ _ hl2]
    dsimp only [leftVec] at htrue
    dsimp only [rightVec]
    by_cases h2 : q < h
    · have ha1 : q < (List.ofFn (fun k : Fin h => @decide (key k = i) (Classical.propDecidable _))).length := by
        simp [h2]
      have ha2 : q < (List.ofFn (fun k : Fin h => @decide (edgeRel E (key k) j) (Classical.propDecidable _))).length := by
        simp [h2]
      rw [getD_append_left _ _ _ _ ha1, getD_ofFn_lt _ _ _ h2] at htrue
      rw [getD_append_left _ _ _ _ ha2, getD_ofFn_lt _ _ _ h2]
      have hki : key ⟨q, h2⟩ = i := of_cdecide_true htrue
      rw [hki]
      exact cdecide_true hed
    · have ha1 : (List.ofFn (fun k : Fin h => @decide (key k = i) (Classical.propDecidable _))).length ≤ q := by
        simp; omega
      rw [getD_append_right _ _ _ _ ha1] at htrue
      have hqh : q - (List.ofFn (fun k : Fin h => @decide (key k = i) (Classical.propDecidable _))).length < h := by
        simp; omega
      rw [getD_replicate_lt _ _ _ _ hqh] at htrue
      cases htrue
  · have hl1 : (leftVec key i).length ≤ q := by rw [length_leftVec]; omega
    have hl2 : (rightVec E key j).length ≤ q := by rw [length_rightVec]; omega
    rw [getD_append_right _ _ _ _ hl1] at htrue
    rw [getD_append_right _ _ _ _ hl2]
    rw [length_leftVec] at htrue
    rw [length_rightVec]
    exact htrue

private lemma le_of_pow2_le {a b : Nat} (h : 2 ^ a ≤ 2 ^ b) : a ≤ b := by
  by_contra hlt
  have hba : b < a := by omega
  have hpow : 2 ^ b < 2 ^ a := Nat.pow_lt_pow_right (by omega : 1 < 2) hba
  omega

private lemma partA_lower_bound {n b h : Nat} (E : Fin n → Fin n → Prop) (f : Fin n → Fin 3)
    (key : Fin h ≃ IxT n) (C : Circuit) (p : Fin 3 → Nat) :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    let m := 2 * (2 ^ b - 1)
    let w := 2 * h + m
    let v := fun (z : List Bool) (k : Fin 3) => (C.wires (z ++ [false, true])).getD (p k) false
    PEqualNP.MetaComplexity.FanInTwo C →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (w + 2) C →
    (∀ k, p k < w + 2 + C.size) →
    (∀ i : IxT n, ∃ a : Fin 3, (∀ d : PairT, i.2 = some d → a ≠ d.val.1) ∧
      ∀ k, v (leftVec key i ++ List.replicate m true) k = decide (k = a)) →
    (∀ j : IxT n, ∃ a : Fin 3, (∀ d : PairT, j.2 = some d → a ≠ d.val.2) ∧
      ∀ k, v (rightVec E key j ++ List.replicate m true) k = decide (k ≠ a)) →
    (∀ (j : Fin m) (k : Fin 3),
      v (List.replicate (2 * h) false ++ List.ofFn (fun i : Fin m => decide (i < j))) k =
        decide (k = 0 ∧ j.val % 2 = 0)) →
    b ≤ PEqualNP.NotBracket.notCount C ∧
      (PEqualNP.NotBracket.notCount C = b →
        (∃ g : Fin n → Fin 3, ∀ u v, E u v → g u ≠ g v) ∧
        ((∀ (i : Fin n) (k : Fin 3),
            (C.wires (leftVec key (i, none) ++ List.replicate m true ++ [false, true])).getD (p k) false =
              decide (k = f i)) →
          ∀ u v, E u v → f u ≠ f v)) := by
  dsimp only
  intro hFan hRB hpLt hLeft hRight hClk
  let m := 2 * (2 ^ b - 1)
  let N := 2 * h + m + 2
  let M := C.gates.length
  have hClkFull : ∀ (j : Fin m) (k : Fin 3),
      wireEval C (clockFull h m j.val) (p k) = @decide (k = 0 ∧ j.val % 2 = 0) (Classical.propDecidable _) := by
    intro j k
    have h1 := hClk j k
    dsimp only [wireEval]
    rw [← clockFull_eq_fin h m j]
    exact h1
  have hStep : ∀ t, t < 2 ^ b - 1 →
      V N C (clockFull h m (2 * (t + 1))) M + 1 ≤ V N C (clockFull h m (2 * t)) M := by
    intro t ht
    have h2t : 2 * t < m := by omega
    have h2t1 : 2 * t + 1 < m := by omega
    have hle1 : ListLe (clockFull h m (2 * t)) (clockFull h m (2 * t + 1)) :=
      listLe_clockFull h m (2 * t) (2 * t + 1) (by omega)
    have hle2 : ListLe (clockFull h m (2 * t + 1)) (clockFull h m (2 * (t + 1))) :=
      listLe_clockFull h m (2 * t + 1) (2 * (t + 1)) (by omega)
    have hvm1 := V_anti_and_mono_wires N C hFan hRB (length_clockFull h m (2 * t))
      (length_clockFull h m (2 * t + 1)) hle1 M (Nat.le_refl _)
    have hvm2 := V_anti_and_mono_wires N C hFan hRB (length_clockFull h m (2 * t + 1))
      (length_clockFull h m (2 * (t + 1))) hle2 M (Nat.le_refl _)
    have hneq : V N C (clockFull h m (2 * t + 1)) M ≠ V N C (clockFull h m (2 * t)) M := by
      intro heq
      have h0true : wireEval C (clockFull h m (2 * t)) (p 0) = true := by
        rw [hClkFull ⟨2 * t, h2t⟩ 0]
        exact cdecide_true ⟨rfl, by dsimp only; omega⟩
      have h1false : wireEval C (clockFull h m (2 * t + 1)) (p 0) = false := by
        rw [hClkFull ⟨2 * t + 1, h2t1⟩ 0]
        exact cdecide_false (by intro ⟨_, hmod⟩; dsimp only at hmod; omega)
      have h1true := hvm1.2 heq (p 0) (hpLt 0) h0true
      rw [h1false] at h1true
      cases h1true
    omega
  have hChain : ∀ t, t ≤ 2 ^ b - 1 →
      V N C (clockFull h m (2 * t)) M + t ≤ V N C (clockFull h m 0) M := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht1
      have ht : t < 2 ^ b - 1 := by omega
      have h1 := hStep t ht
      have h2 := ih (Nat.le_of_lt ht)
      omega
  have hV0lt : V N C (clockFull h m 0) M < 2 ^ PEqualNP.NotBracket.notCount C := by
    rw [← B_cntList_eq_notCount C]
    exact V_lt_pow N C (clockFull h m 0) M
  have hPowPos : 1 ≤ 2 ^ b := Nat.one_le_pow b 2 (by omega)
  have hEnd : V N C (clockFull h m m) M + 2 ^ b ≤ 2 ^ PEqualNP.NotBracket.notCount C := by
    have h1 := hChain (2 ^ b - 1) (Nat.le_refl _)
    have hmEq : 2 * (2 ^ b - 1) = m := rfl
    rw [hmEq] at h1
    omega
  have hbLe : b ≤ PEqualNP.NotBracket.notCount C := le_of_pow2_le (by omega)
  refine ⟨hbLe, ?_⟩
  intro hNotEq
  have hVmZero : V N C (clockFull h m m) M = 0 := by
    rw [hNotEq] at hEnd
    omega
  have hVLeftZero : ∀ i : IxT n,
      V N C (leftVec key i ++ List.replicate m true ++ [false, true]) M = 0 := by
    intro i
    have hle := listLe_clockFull_shore h m (leftVec key i) (length_leftVec key i)
    have hvm := V_anti_and_mono_wires N C hFan hRB (length_clockFull h m m)
      (length_leftFull key m i) hle M (Nat.le_refl _)
    omega
  have hVRightZero : ∀ j : IxT n,
      V N C (rightVec E key j ++ List.replicate m true ++ [false, true]) M = 0 := by
    intro j
    have hle := listLe_clockFull_shore h m (rightVec E key j) (length_rightVec E key j)
    have hvm := V_anti_and_mono_wires N C hFan hRB (length_clockFull h m m)
      (length_rightFull E key m j) hle M (Nat.le_refl _)
    omega
  let aL : IxT n → Fin 3 := fun i => Classical.choose (hLeft i)
  have haL : ∀ i : IxT n, (∀ d : PairT, i.2 = some d → aL i ≠ d.val.1) ∧
      ∀ k, wireEval C (leftVec key i ++ List.replicate m true ++ [false, true]) (p k) =
        @decide (k = aL i) (Classical.propDecidable _) :=
    fun i => Classical.choose_spec (hLeft i)
  let aR : IxT n → Fin 3 := fun j => Classical.choose (hRight j)
  have haR : ∀ j : IxT n, (∀ d : PairT, j.2 = some d → aR j ≠ d.val.2) ∧
      ∀ k, wireEval C (rightVec E key j ++ List.replicate m true ++ [false, true]) (p k) =
        @decide (k ≠ aR j) (Classical.propDecidable _) :=
    fun j => Classical.choose_spec (hRight j)
  have hEdgeNe : ∀ i j : IxT n, edgeRel E i j → aL i ≠ aR j := by
    intro i j hed
    have hle := listLe_left_right E key i j hed (m := m)
    have hvm := V_anti_and_mono_wires N C hFan hRB (length_leftFull key m i)
      (length_rightFull E key m j) hle M (Nat.le_refl _)
    have hveq : V N C (rightVec E key j ++ List.replicate m true ++ [false, true]) M =
        V N C (leftVec key i ++ List.replicate m true ++ [false, true]) M := by
      rw [hVRightZero j, hVLeftZero i]
    have hltrue : wireEval C (leftVec key i ++ List.replicate m true ++ [false, true]) (p (aL i)) = true := by
      rw [(haL i).2 (aL i)]
      exact cdecide_true rfl
    have hrtrue := hvm.2 hveq (p (aL i)) (hpLt (aL i)) hltrue
    rw [(haR j).2 (aL i)] at hrtrue
    exact of_cdecide_true hrtrue
  have hAgree : ∀ u : Fin n, aL (u, none) = aR (u, none) := by
    intro u
    by_contra hne
    let d : PairT := ⟨(aL (u, none), aR (u, none)), hne⟩
    have h1 : aL (u, some d) ≠ aL (u, none) := (haL (u, some d)).1 d rfl
    have h2 : aL (u, some d) ≠ aR (u, none) := hEdgeNe (u, some d) (u, none) (by
      simp [edgeRel])
    have h3 : aR (u, some d) ≠ aR (u, none) := (haR (u, some d)).1 d rfl
    have h4 : aL (u, none) ≠ aR (u, some d) := hEdgeNe (u, none) (u, some d) (by
      simp [edgeRel])
    have h5 : aL (u, some d) ≠ aR (u, some d) := hEdgeNe (u, some d) (u, some d) (by
      simp [edgeRel])
    have hv1 : (aL (u, none)).val ≠ (aR (u, none)).val := fun h => hne (Fin.ext h)
    have hv2 : (aL (u, some d)).val ≠ (aL (u, none)).val := fun h => h1 (Fin.ext h)
    have hv3 : (aL (u, some d)).val ≠ (aR (u, none)).val := fun h => h2 (Fin.ext h)
    have hv4 : (aR (u, some d)).val ≠ (aR (u, none)).val := fun h => h3 (Fin.ext h)
    have hv5 : (aL (u, none)).val ≠ (aR (u, some d)).val := fun h => h4 (Fin.ext h)
    have hv6 : (aL (u, some d)).val ≠ (aR (u, some d)).val := fun h => h5 (Fin.ext h)
    have hb1 := (aL (u, none)).isLt
    have hb2 := (aR (u, none)).isLt
    have hb3 := (aL (u, some d)).isLt
    have hb4 := (aR (u, some d)).isLt
    omega
  have hProperAL : ∀ u v : Fin n, E u v → aL (u, none) ≠ aL (v, none) := by
    intro u v huv
    rw [hAgree v]
    exact hEdgeNe (u, none) (v, none) (by simp [edgeRel, huv])
  refine ⟨⟨fun u => aL (u, none), hProperAL⟩, ?_⟩
  intro hTrace u v huv
  have hfu : ∀ x : Fin n, f x = aL (x, none) := by
    intro x
    have h1 := hTrace x (f x)
    have h2 := (haL (x, none)).2 (f x)
    dsimp only [wireEval] at h2
    rw [h1] at h2
    have htrue : @decide (f x = aL (x, none)) (Classical.propDecidable _) = true := by
      rw [← h2]
      exact cdecide_true rfl
    exact of_cdecide_true htrue
  rw [hfu u, hfu v]
  exact hProperAL u v huv

private def FanInTwoList (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def ReadsBackList (N : Nat) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < N + j

private def WF (N : Nat) (gs : List Gate) : Prop :=
  FanInTwoList gs ∧ ReadsBackList N gs

private def Extends (gs1 gs2 : List Gate) : Prop :=
  ∃ ext : List Gate, gs2 = gs1 ++ ext

private lemma extends_refl (gs : List Gate) : Extends gs gs :=
  ⟨[], by simp⟩

private lemma extends_trans {gs1 gs2 gs3 : List Gate}
    (h12 : Extends gs1 gs2) (h23 : Extends gs2 gs3) : Extends gs1 gs3 := by
  rcases h12 with ⟨e1, rfl⟩
  rcases h23 with ⟨e2, rfl⟩
  exact ⟨e1 ++ e2, by simp [List.append_assoc]⟩

private lemma extends_length_le {gs1 gs2 : List Gate} (h : Extends gs1 gs2) :
    gs1.length ≤ gs2.length := by
  rcases h with ⟨e, rfl⟩
  simp

private lemma getD_foldl_extends {gs1 gs2 : List Gate} (h : Extends gs1 gs2)
    (v : List Bool) (u : Nat) (hu : u < v.length + gs1.length) :
    (gs2.foldl stepWire v).getD u false = (gs1.foldl stepWire v).getD u false := by
  rcases h with ⟨e, rfl⟩
  rw [List.foldl_append]
  apply getD_foldl_stepWire_of_lt
  rw [length_foldl_stepWire]
  exact hu

private lemma getD_foldl_snoc_new (gs : List Gate) (g : Gate) (v : List Bool) :
    ((gs ++ [g]).foldl stepWire v).getD (v.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (gs.foldl stepWire v).getD i false) := by
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl stepWire v).length = v.length + gs.length := length_foldl_stepWire gs v
  rw [← hlen]
  exact getD_append_right_eq (gs.foldl stepWire v) _ false

private lemma wf_nil (N : Nat) : WF N [] :=
  ⟨(fun _ hg => nomatch hg), (fun _ hj => nomatch hj)⟩

private lemma wf_snoc {N : Nat} {gs : List Gate} {g : Gate} (hwf : WF N gs)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2)
    (hins : ∀ i ∈ g.inputs, i < N + gs.length) : WF N (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hwf.1 x hx
    · exact ⟨hop, hlen⟩
  · intro j hj i hi
    by_cases hlt : j < gs.length
    · rw [List.getElem_append_left hlt] at hi
      exact hwf.2 j hlt i hi
    · have hjeq : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst hjeq
      have hge : (gs ++ [g])[gs.length] = g := by simp
      rw [hge] at hi
      exact hins i hi

private lemma notCountList_snoc (gs : List Gate) (g : Gate) :
    notCountList (gs ++ [g]) = notCountList gs + if isNotOp g.op then 1 else 0 := by
  dsimp only [notCountList]
  rw [List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
  cases isNotOp g.op <;> simp

private lemma readsBack_of_wf {N : Nat} {gs : List Gate} (hwf : WF N gs) (o : Nat) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N { gates := gs, output := o } := by
  intro j hj i hi
  dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at hi
  rw [getD_eq_getElem gs j _ hj] at hi
  exact hwf.2 j hj i hi

private def emitGate (N : Nat) (gs : List Gate) (g : Gate) : List Gate × Nat :=
  (gs ++ [g], N + gs.length)

private def emitNot (N : Nat) (gs : List Gate) (a : Nat) : List Gate × Nat :=
  emitGate N gs ⟨GateOp.not, [a]⟩

private def emitAnd (N : Nat) (gs : List Gate) (a b : Nat) : List Gate × Nat :=
  emitGate N gs ⟨GateOp.and, [a, b]⟩

private def emitOr (N : Nat) (gs : List Gate) (a b : Nat) : List Gate × Nat :=
  emitGate N gs ⟨GateOp.or, [a, b]⟩

private lemma emitNot_spec (N : Nat) (gs : List Gate) (a : Nat)
    (hwf : WF N gs) (ha : a < N + gs.length) :
    let r := emitNot N gs a
    Extends gs r.1 ∧ WF N r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < N + r.1.length ∧
      notCountList r.1 = notCountList gs + 1 ∧
      ∀ v : List Bool, v.length = N →
        (r.1.foldl stepWire v).getD r.2 false = !((gs.foldl stepWire v).getD a false) := by
  dsimp only [emitNot, emitGate]
  refine ⟨⟨[_], rfl⟩, ?_, by simp, by simp, ?_, ?_⟩
  · apply wf_snoc hwf (by simp) (by simp)
    intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    exact ha
  · rw [notCountList_snoc]
    simp [isNotOp]
  · intro v hv
    rw [← hv, getD_foldl_snoc_new]
    rfl

private lemma emitAnd_spec (N : Nat) (gs : List Gate) (a b : Nat)
    (hwf : WF N gs) (ha : a < N + gs.length) (hb : b < N + gs.length) :
    let r := emitAnd N gs a b
    Extends gs r.1 ∧ WF N r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < N + r.1.length ∧
      notCountList r.1 = notCountList gs ∧
      ∀ v : List Bool, v.length = N →
        (r.1.foldl stepWire v).getD r.2 false =
          (((gs.foldl stepWire v).getD a false) && ((gs.foldl stepWire v).getD b false)) := by
  dsimp only [emitAnd, emitGate]
  refine ⟨⟨[_], rfl⟩, ?_, by simp, by simp, ?_, ?_⟩
  · apply wf_snoc hwf (by simp) (by simp)
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · rw [notCountList_snoc]
    simp [isNotOp]
  · intro v hv
    rw [← hv, getD_foldl_snoc_new]
    simp [GateOp.eval]

private lemma emitOr_spec (N : Nat) (gs : List Gate) (a b : Nat)
    (hwf : WF N gs) (ha : a < N + gs.length) (hb : b < N + gs.length) :
    let r := emitOr N gs a b
    Extends gs r.1 ∧ WF N r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < N + r.1.length ∧
      notCountList r.1 = notCountList gs ∧
      ∀ v : List Bool, v.length = N →
        (r.1.foldl stepWire v).getD r.2 false =
          (((gs.foldl stepWire v).getD a false) || ((gs.foldl stepWire v).getD b false)) := by
  dsimp only [emitOr, emitGate]
  refine ⟨⟨[_], rfl⟩, ?_, by simp, by simp, ?_, ?_⟩
  · apply wf_snoc hwf (by simp) (by simp)
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · rw [notCountList_snoc]
    simp [isNotOp]
  · intro v hv
    rw [← hv, getD_foldl_snoc_new]
    simp [GateOp.eval]

private def emitOrListAux (N : Nat) (gs : List Gate) (acc : Nat) : List Nat → List Gate × Nat
  | [] => (gs, acc)
  | a :: rest =>
    let r := emitOr N gs acc a
    emitOrListAux N r.1 r.2 rest

private def emitOrList (N : Nat) (gs : List Gate) (falseW : Nat) : List Nat → List Gate × Nat
  | [] => (gs, falseW)
  | a :: rest => emitOrListAux N gs a rest

private lemma emitOrListAux_spec (N : Nat) (l : List Nat) :
    ∀ (gs : List Gate) (acc : Nat),
      WF N gs → acc < N + gs.length → (∀ u ∈ l, u < N + gs.length) →
      let r := emitOrListAux N gs acc l
      Extends gs r.1 ∧ WF N r.1 ∧ r.1.length = gs.length + l.length ∧ r.2 < N + r.1.length ∧
        notCountList r.1 = notCountList gs ∧
        ∀ v : List Bool, v.length = N →
          (r.1.foldl stepWire v).getD r.2 false =
            (((gs.foldl stepWire v).getD acc false) ||
              l.any (fun u => (gs.foldl stepWire v).getD u false)) := by
  induction l with
  | nil =>
    intro gs acc hwf hacc _
    refine ⟨extends_refl gs, hwf, by simp [emitOrListAux], hacc, rfl, ?_⟩
    intro v _
    simp [emitOrListAux]
  | cons a rest ih =>
    intro gs acc hwf hacc hl
    have ha : a < N + gs.length := hl a List.mem_cons_self
    have h1 := emitOr_spec N gs acc a hwf hacc ha
    set r1 := emitOr N gs acc a
    have hrest : ∀ u ∈ rest, u < N + r1.1.length := by
      intro u hu
      have hlt := hl u (List.mem_cons_of_mem _ hu)
      have hl1 := h1.2.2.1
      omega
    have h2 := ih r1.1 r1.2 h1.2.1 h1.2.2.2.1 hrest
    refine ⟨extends_trans h1.1 h2.1, h2.2.1, ?_, h2.2.2.2.1,
      by dsimp only [emitOrListAux]; rw [h2.2.2.2.2.1, h1.2.2.2.2.1], ?_⟩
    · change (emitOrListAux N r1.1 r1.2 rest).1.length = gs.length + (a :: rest).length
      rw [h2.2.2.1, h1.2.2.1]
      simp only [List.length_cons]
      omega
    · intro v hv
      dsimp only [emitOrListAux]
      rw [h2.2.2.2.2.2 v hv, h1.2.2.2.2.2 v hv]
      have hany : rest.any (fun u => (r1.1.foldl stepWire v).getD u false) =
          rest.any (fun u => (gs.foldl stepWire v).getD u false) := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true]
        constructor
        · rintro ⟨u, hu, hget⟩
          rw [getD_foldl_extends h1.1 v u (by rw [hv]; exact hl u (List.mem_cons_of_mem _ hu))] at hget
          exact ⟨u, hu, hget⟩
        · rintro ⟨u, hu, hget⟩
          refine ⟨u, hu, ?_⟩
          rw [getD_foldl_extends h1.1 v u (by rw [hv]; exact hl u (List.mem_cons_of_mem _ hu))]
          exact hget
      rw [hany]
      simp [List.any_cons, Bool.or_assoc]

private lemma emitOrList_spec (N : Nat) (gs : List Gate) (falseW : Nat) (l : List Nat)
    (hwf : WF N gs) (hf : falseW < N + gs.length) (hl : ∀ u ∈ l, u < N + gs.length) :
    let r := emitOrList N gs falseW l
    Extends gs r.1 ∧ WF N r.1 ∧ r.1.length ≤ gs.length + l.length ∧ r.2 < N + r.1.length ∧
      notCountList r.1 = notCountList gs ∧
      ∀ v : List Bool, v.length = N → (gs.foldl stepWire v).getD falseW false = false →
        (r.1.foldl stepWire v).getD r.2 false =
          l.any (fun u => (gs.foldl stepWire v).getD u false) := by
  cases l with
  | nil =>
    refine ⟨extends_refl gs, hwf, by simp [emitOrList], hf, rfl, ?_⟩
    intro v _ hfv
    simpa [emitOrList] using hfv
  | cons a rest =>
    have ha : a < N + gs.length := hl a List.mem_cons_self
    have hrest : ∀ u ∈ rest, u < N + gs.length := fun u hu => hl u (List.mem_cons_of_mem _ hu)
    have h := emitOrListAux_spec N rest gs a hwf ha hrest
    refine ⟨h.1, h.2.1, ?_, h.2.2.2.1, h.2.2.2.2.1, ?_⟩
    · dsimp only [emitOrList]
      have hl := h.2.2.1
      simp only [List.length_cons]
      omega
    intro v hv _
    simpa [emitOrList, List.any_cons] using h.2.2.2.2.2 v hv

private def clockLen (b : Nat) : Nat := 2 * (2 ^ b - 1)

private def buildClockSub (N : Nat) (gs : List Gate) (falseW notMid : Nat)
    (uWires : List Nat) (m' : Nat) : Nat → List Gate × List Nat
  | 0 => (gs, [])
  | k + 1 =>
    let r0 := buildClockSub N gs falseW notMid uWires m' k
    let r1 := emitAnd N r0.1 notMid (uWires.getD k falseW)
    let r2 := emitOr N r1.1 (uWires.getD (m' + 2 + k) falseW) r1.2
    (r2.1, r0.2 ++ [r2.2])

private lemma buildClockSub_spec (N : Nat) (gs : List Gate) (falseW notMid : Nat)
    (uWires : List Nat) (m' : Nat)
    (hwf : WF N gs) (hf : falseW < N + gs.length) (hnm : notMid < N + gs.length)
    (hu : ∀ r < 2 * m' + 2, uWires.getD r falseW < N + gs.length) :
    ∀ k ≤ m',
      let r := buildClockSub N gs falseW notMid uWires m' k
      Extends gs r.1 ∧ WF N r.1 ∧ r.1.length = gs.length + 2 * k ∧
        notCountList r.1 = notCountList gs ∧ r.2.length = k ∧
        (∀ i < k, r.2.getD i falseW < N + r.1.length) ∧
        ∀ v : List Bool, v.length = N → ∀ i < k,
          (r.1.foldl stepWire v).getD (r.2.getD i falseW) false =
            (((gs.foldl stepWire v).getD (uWires.getD (m' + 2 + i) falseW) false) ||
              (((gs.foldl stepWire v).getD notMid false) &&
                ((gs.foldl stepWire v).getD (uWires.getD i falseW) false))) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨extends_refl gs, hwf, by simp [buildClockSub], rfl, rfl, (fun _ hi => nomatch hi), ?_⟩
    intro _ _ i hi
    cases hi
  | succ k ih =>
    intro hk1
    have hkm : k ≤ m' := by omega
    obtain ⟨hExt0, hWf0, hLen0, hNot0, hRLen0, hLt0, hEval0⟩ := ih hkm
    set r0 := buildClockSub N gs falseW notMid uWires m' k
    have hnm0 : notMid < N + r0.1.length := by omega
    have huk0 : uWires.getD k falseW < N + r0.1.length := by
      have := hu k (by omega); omega
    have h1 := emitAnd_spec N r0.1 notMid (uWires.getD k falseW) hWf0 hnm0 huk0
    set r1 := emitAnd N r0.1 notMid (uWires.getD k falseW)
    have huhi1 : uWires.getD (m' + 2 + k) falseW < N + r1.1.length := by
      have := hu (m' + 2 + k) (by omega); have := h1.2.2.1; omega
    have h2 := emitOr_spec N r1.1 (uWires.getD (m' + 2 + k) falseW) r1.2 h1.2.1 huhi1 h1.2.2.2.1
    set r2 := emitOr N r1.1 (uWires.getD (m' + 2 + k) falseW) r1.2
    have hExt02 : Extends r0.1 r2.1 := extends_trans h1.1 h2.1
    have hExtG1 : Extends gs r1.1 := extends_trans hExt0 h1.1
    have hExtG2 : Extends gs r2.1 := extends_trans hExtG1 h2.1
    refine ⟨hExtG2, h2.2.1, ?_,
      by change notCountList r2.1 = notCountList gs; rw [h2.2.2.2.2.1, h1.2.2.2.2.1, hNot0],
      by change (r0.2 ++ [r2.2]).length = k + 1; simp [hRLen0], ?_, ?_⟩
    · change r2.1.length = gs.length + 2 * (k + 1)
      rw [h2.2.2.1, h1.2.2.1, hLen0]
      omega
    · intro i hi
      change (r0.2 ++ [r2.2]).getD i falseW < N + r2.1.length
      by_cases hik : i < k
      · have hil : i < r0.2.length := by omega
        rw [getD_append_left _ _ _ _ hil]
        have := hLt0 i hik
        have := h1.2.2.1
        have := h2.2.2.1
        omega
      · have hieq : i = k := by omega
        rw [hieq]
        have hget : (r0.2 ++ [r2.2]).getD k falseW = r2.2 := by
          simpa [hRLen0] using getD_append_right_eq r0.2 r2.2 falseW
        rw [hget]
        exact h2.2.2.2.1
    · intro v hv i hi
      change (r2.1.foldl stepWire v).getD ((r0.2 ++ [r2.2]).getD i falseW) false = _
      by_cases hik : i < k
      · have hil : i < r0.2.length := by omega
        rw [getD_append_left _ _ _ _ hil]
        have hiu : r0.2.getD i falseW < v.length + r0.1.length := by
          rw [hv]; exact hLt0 i hik
        rw [getD_foldl_extends hExt02 v _ hiu]
        exact hEval0 v hv i hik
      · have hieq : i = k := by omega
        rw [hieq]
        have hget : (r0.2 ++ [r2.2]).getD k falseW = r2.2 := by
          simpa [hRLen0] using getD_append_right_eq r0.2 r2.2 falseW
        rw [hget]
        rw [h2.2.2.2.2.2 v hv, h1.2.2.2.2.2 v hv]
        have huhiG : uWires.getD (m' + 2 + k) falseW < v.length + gs.length := by
          rw [hv]; exact hu (m' + 2 + k) (by omega)
        have hnmG : notMid < v.length + gs.length := by rw [hv]; exact hnm
        have huiG : uWires.getD k falseW < v.length + gs.length := by
          rw [hv]; exact hu k (by omega)
        rw [getD_foldl_extends hExtG1 v _ huhiG,
            getD_foldl_extends hExt0 v _ hnmG,
            getD_foldl_extends hExt0 v _ huiG]

private def buildClock : Nat → Nat → List Gate → Nat → List Nat → List Gate × Nat
  | 0, _, gs, falseW, _ => (gs, falseW)
  | 1, N, gs, falseW, uWires => emitNot N gs (uWires.getD 0 falseW)
  | b' + 2, N, gs, falseW, uWires =>
    let b1 := b' + 1
    let m' := clockLen b1
    let mid := uWires.getD m' falseW
    let hi := uWires.getD (m' + 1) falseW
    let prev := uWires.getD (m' - 1) falseW
    let r1 := emitNot N gs mid
    let r2 := buildClockSub N r1.1 falseW r1.2 uWires m' m'
    let r3 := buildClock b1 N r2.1 falseW r2.2
    let r4 := emitOr N r3.1 r1.2 hi
    let r5 := emitAnd N r4.1 r4.2 r3.2
    let r6 := emitAnd N r5.1 r1.2 prev
    emitOr N r6.1 r5.2 r6.2

private lemma clockLen_succ (b1 : Nat) : clockLen (b1 + 1) = 2 * clockLen b1 + 2 := by
  dsimp only [clockLen]
  have hpos : 1 ≤ 2 ^ b1 := Nat.one_le_pow b1 2 (by omega)
  rw [Nat.pow_succ]
  omega

private lemma clockLen_ge_two (b' : Nat) : 2 ≤ clockLen (b' + 1) := by
  dsimp only [clockLen]
  have h1 : 1 ≤ 2 ^ b' := Nat.one_le_pow b' 2 (by omega)
  rw [Nat.pow_succ]
  omega

private lemma buildClock_spec : ∀ (b N : Nat) (gs : List Gate) (falseW : Nat) (uWires : List Nat),
    WF N gs → falseW < N + gs.length →
    (∀ r < clockLen b, uWires.getD r falseW < N + gs.length) →
    let res := buildClock b N gs falseW uWires
    Extends gs res.1 ∧ WF N res.1 ∧ res.2 < N + res.1.length ∧
      res.1.length ≤ gs.length + 3 * clockLen b ∧
      notCountList res.1 = notCountList gs + b ∧
      ∀ (v : List Bool) (L : Nat), v.length = N →
        (gs.foldl stepWire v).getD falseW false = false →
        L ≤ clockLen b →
        (∀ r < clockLen b, (gs.foldl stepWire v).getD (uWires.getD r falseW) false = decide (r < L)) →
        (res.1.foldl stepWire v).getD res.2 false = decide (L < clockLen b ∧ L % 2 = 0)
  | 0, N, gs, falseW, uWires, hwf, hf, _ => by
    refine ⟨extends_refl gs, hwf, hf, by simp [buildClock, clockLen], by simp [buildClock], ?_⟩
    intro v L _ hfv hL _
    have hL0 : L = 0 := by simp [clockLen] at hL; omega
    subst hL0
    simpa [buildClock, clockLen] using hfv
  | 1, N, gs, falseW, uWires, hwf, _, hu => by
    have hu0 : uWires.getD 0 falseW < N + gs.length := hu 0 (by decide)
    have h1 := emitNot_spec N gs (uWires.getD 0 falseW) hwf hu0
    refine ⟨h1.1, h1.2.1, h1.2.2.2.1, by dsimp only [buildClock, clockLen]; have := h1.2.2.1; omega,
      h1.2.2.2.2.1, ?_⟩
    intro v L hv _ hL huEval
    dsimp only [buildClock]
    rw [h1.2.2.2.2.2 v hv, huEval 0 (by decide)]
    have hL2 : L ≤ 2 := by simpa [clockLen] using hL
    have : L = 0 ∨ L = 1 ∨ L = 2 := by omega
    rcases this with rfl | rfl | rfl <;> decide
  | b' + 2, N, gs, falseW, uWires, hwf, hf, hu => by
    set b1 := b' + 1
    set m' := clockLen b1
    have hm'2 : 2 ≤ m' := clockLen_ge_two b'
    have hcl : clockLen (b' + 2) = 2 * m' + 2 := clockLen_succ b1
    have hm'even : m' % 2 = 0 := by dsimp only [m', clockLen]; omega
    have hu' : ∀ r < 2 * m' + 2, uWires.getD r falseW < N + gs.length := by
      intro r hr; exact hu r (by omega)
    set mid := uWires.getD m' falseW
    set hi := uWires.getD (m' + 1) falseW
    set prev := uWires.getD (m' - 1) falseW
    have hmid : mid < N + gs.length := hu' m' (by omega)
    have hhi : hi < N + gs.length := hu' (m' + 1) (by omega)
    have hprev : prev < N + gs.length := hu' (m' - 1) (by omega)
    have hr1 := emitNot_spec N gs mid hwf hmid
    set r1 := emitNot N gs mid
    have hf1 : falseW < N + r1.1.length := by have := hr1.2.2.1; omega
    have hu1 : ∀ r < 2 * m' + 2, uWires.getD r falseW < N + r1.1.length := by
      intro r hr; have := hu' r hr; have := hr1.2.2.1; omega
    obtain ⟨hExt2, hWf2, hLen2, hNot2, _, hLt2, hEval2⟩ :=
      buildClockSub_spec N r1.1 falseW r1.2 uWires m' hr1.2.1 hf1 hr1.2.2.2.1 hu1 m' (Nat.le_refl _)
    set r2 := buildClockSub N r1.1 falseW r1.2 uWires m' m'
    have hf2 : falseW < N + r2.1.length := by omega
    obtain ⟨hExt3, hWf3, hOut3, hLen3, hNot3, hEval3⟩ :=
      buildClock_spec b1 N r2.1 falseW r2.2 hWf2 hf2 hLt2
    set r3 := buildClock b1 N r2.1 falseW r2.2
    have hExt12 : Extends r1.1 r2.1 := hExt2
    have hExt13 : Extends r1.1 r3.1 := extends_trans hExt12 hExt3
    have hExtG2 : Extends gs r2.1 := extends_trans hr1.1 hExt12
    have hExtG3 : Extends gs r3.1 := extends_trans hr1.1 hExt13
    have hnm3 : r1.2 < N + r3.1.length := by
      have := extends_length_le hExt13; have := hr1.2.2.2.1; omega
    have hhi3 : hi < N + r3.1.length := by
      have := extends_length_le hExtG3; omega
    have hr4 := emitOr_spec N r3.1 r1.2 hi hWf3 hnm3 hhi3
    set r4 := emitOr N r3.1 r1.2 hi
    have hsub4 : r3.2 < N + r4.1.length := by have := hr4.2.2.1; omega
    have hr5 := emitAnd_spec N r4.1 r4.2 r3.2 hr4.2.1 hr4.2.2.2.1 hsub4
    set r5 := emitAnd N r4.1 r4.2 r3.2
    have hExt15 : Extends r1.1 r5.1 := extends_trans hExt13 (extends_trans hr4.1 hr5.1)
    have hExtG5 : Extends gs r5.1 := extends_trans hr1.1 hExt15
    have hnm5 : r1.2 < N + r5.1.length := by
      have := extends_length_le hExt15; have := hr1.2.2.2.1; omega
    have hprev5 : prev < N + r5.1.length := by
      have := extends_length_le hExtG5; omega
    have hr6 := emitAnd_spec N r5.1 r1.2 prev hr5.2.1 hnm5 hprev5
    set r6 := emitAnd N r5.1 r1.2 prev
    have hr5lt6 : r5.2 < N + r6.1.length := by have := hr6.2.2.1; have := hr5.2.2.2.1; omega
    have hr7 := emitOr_spec N r6.1 r5.2 r6.2 hr6.2.1 hr5lt6 hr6.2.2.2.1
    have hExtAll : Extends gs (emitOr N r6.1 r5.2 r6.2).1 :=
      extends_trans hExtG5 (extends_trans hr6.1 hr7.1)
    refine ⟨hExtAll, hr7.2.1, hr7.2.2.2.1, ?_, ?_, ?_⟩
    · change (emitOr N r6.1 r5.2 r6.2).1.length ≤ gs.length + 3 * clockLen (b' + 2)
      have h7len := hr7.2.2.1
      have h6len := hr6.2.2.1
      have h5len := hr5.2.2.1
      have h4len := hr4.2.2.1
      have h1len := hr1.2.2.1
      omega
    · change notCountList (emitOr N r6.1 r5.2 r6.2).1 = notCountList gs + (b' + 2)
      rw [hr7.2.2.2.2.1, hr6.2.2.2.2.1, hr5.2.2.2.2.1, hr4.2.2.2.2.1, hNot3, hNot2, hr1.2.2.2.2.1]
      omega
    · intro v L hv hfv hL huEval
      dsimp only [buildClock]
      have huEval' : ∀ r < 2 * m' + 2,
          (gs.foldl stepWire v).getD (uWires.getD r falseW) false = decide (r < L) := by
        intro r hr; exact huEval r (by omega)
      have hNotMidVal : (r1.1.foldl stepWire v).getD r1.2 false = decide (L ≤ m') := by
        rw [hr1.2.2.2.2.2 v hv, huEval' m' (by omega)]
        by_cases hLm : m' < L
        · have hnot : ¬(L ≤ m') := by omega
          simp [hLm, hnot]
        · have hle : L ≤ m' := by omega
          simp [hLm, hle]
      have hHiVal : (gs.foldl stepWire v).getD hi false = decide (m' + 1 < L) :=
        huEval' (m' + 1) (by omega)
      have hPrevVal : (gs.foldl stepWire v).getD prev false = decide (m' - 1 < L) :=
        huEval' (m' - 1) (by omega)
      have hSubVal : ∀ i < m',
          (r2.1.foldl stepWire v).getD (r2.2.getD i falseW) false =
            ((decide (m' + 2 + i < L)) || (decide (L ≤ m') && decide (i < L))) := by
        intro i hi
        rw [hEval2 v hv i hi]
        have huhiG : uWires.getD (m' + 2 + i) falseW < v.length + gs.length := by
          rw [hv]; exact hu' (m' + 2 + i) (by omega)
        have huiG : uWires.getD i falseW < v.length + gs.length := by
          rw [hv]; exact hu' i (by omega)
        rw [getD_foldl_extends hr1.1 v _ huhiG, getD_foldl_extends hr1.1 v _ huiG,
            huEval' (m' + 2 + i) (by omega), huEval' i (by omega), hNotMidVal]
      have hfv2 : (r2.1.foldl stepWire v).getD falseW false = false := by
        have hfg : falseW < v.length + gs.length := by rw [hv]; exact hf
        rw [getD_foldl_extends hExtG2 v _ hfg]
        exact hfv
      rw [hr7.2.2.2.2.2 v hv,
          getD_foldl_extends hr6.1 v _ (by rw [hv]; exact hr5.2.2.2.1),
          hr5.2.2.2.2.2 v hv,
          hr4.2.2.2.2.2 v hv,
          getD_foldl_extends hExt13 v _ (by rw [hv]; exact hr1.2.2.2.1),
          getD_foldl_extends hExtG3 v _ (by rw [hv]; exact hhi),
          getD_foldl_extends hr4.1 v _ (by rw [hv]; exact hOut3),
          hr6.2.2.2.2.2 v hv,
          getD_foldl_extends hExt15 v _ (by rw [hv]; exact hr1.2.2.2.1),
          getD_foldl_extends hExtG5 v _ (by rw [hv]; exact hprev),
          hNotMidVal, hHiVal, hPrevVal]
      by_cases hCase1 : L ≤ m'
      · have hSubL : ∀ i < m', (r2.1.foldl stepWire v).getD (r2.2.getD i falseW) false = decide (i < L) := by
          intro i hi
          rw [hSubVal i hi]
          have hno : ¬(m' + 2 + i < L) := by omega
          simp [hno, hCase1]
        have h3val : (r3.1.foldl stepWire v).getD r3.2 false = decide (L < m' ∧ L % 2 = 0) :=
          hEval3 v L hv hfv2 hCase1 hSubL
        rw [h3val]
        by_cases hLt : L < m'
        · have h1 : ¬(m' + 1 < L) := by omega
          have h2 : ¬(m' - 1 < L) := by omega
          have h3 : L < clockLen (b' + 2) := by omega
          simp [hCase1, h1, h2, hLt, h3]
        · have hEq : L = m' := by omega
          subst hEq
          have h1 : ¬(m' + 1 < m') := by omega
          have h2 : m' - 1 < m' := by omega
          have h3 : m' < clockLen (b' + 2) := by omega
          simp [h1, h2, h3, hm'even]
      · by_cases hCase2 : L = m' + 1
        · subst hCase2
          have h1 : ¬(m' + 1 ≤ m') := by omega
          have h2 : ¬(m' + 1 < m' + 1) := by omega
          have h3 : ¬((m' + 1) % 2 = 0) := by omega
          simp [h1, h2, h3]
        · have hGe : m' + 2 ≤ L := by omega
          let L' := L - (m' + 2)
          have hL'le : L' ≤ m' := by omega
          have hSubL' : ∀ i < m',
              (r2.1.foldl stepWire v).getD (r2.2.getD i falseW) false = decide (i < L') := by
            intro i hi
            rw [hSubVal i hi]
            have h1 : ¬(L ≤ m') := hCase1
            have hiff : m' + 2 + i < L ↔ i < L' := by omega
            simp [h1, hiff]
          have h3val : (r3.1.foldl stepWire v).getD r3.2 false = decide (L' < m' ∧ L' % 2 = 0) :=
            hEval3 v L' hv hfv2 hL'le hSubL'
          rw [h3val]
          have hhiT : m' + 1 < L := by omega
          have hltIff : L' < m' ↔ L < clockLen (b' + 2) := by omega
          have hmodIff : L' % 2 = 0 ↔ L % 2 = 0 := by omega
          simp [hCase1, hhiT, hltIff, hmodIff]

private def thirdColor (c1 c2 : Fin 3) : Fin 3 :=
  if c1 ≠ (0 : Fin 3) ∧ c2 ≠ (0 : Fin 3) then 0
  else if c1 ≠ (1 : Fin 3) ∧ c2 ≠ (1 : Fin 3) then 1
  else 2

private def colL {n : Nat} (f : Fin n → Fin 3) : IxT n → Fin 3
  | (u, none) => f u
  | (u, some d) => if f u = d.1.2 then thirdColor d.1.1 d.1.2 else d.1.2

private def colR {n : Nat} (f : Fin n → Fin 3) : IxT n → Fin 3
  | (u, none) => f u
  | (u, some d) => if f u = d.1.1 then thirdColor d.1.1 d.1.2 else d.1.1

private lemma thirdColor_ne (c1 c2 : Fin 3) : thirdColor c1 c2 ≠ c1 ∧ thirdColor c1 c2 ≠ c2 := by
  fin_cases c1 <;> fin_cases c2 <;> decide

private lemma colL_some_props {n : Nat} (f : Fin n → Fin 3) (u : Fin n) (d : PairT) :
    colL f (u, some d) ≠ d.1.1 ∧ colL f (u, some d) ≠ f u := by
  dsimp only [colL]
  split_ifs with h
  · have ht := thirdColor_ne d.1.1 d.1.2
    exact ⟨ht.1, by rw [h]; exact ht.2⟩
  · exact ⟨Ne.symm d.2, Ne.symm h⟩

private lemma colR_some_props {n : Nat} (f : Fin n → Fin 3) (u : Fin n) (d : PairT) :
    colR f (u, some d) ≠ d.1.2 ∧ colR f (u, some d) ≠ f u := by
  dsimp only [colR]
  split_ifs with h
  · have ht := thirdColor_ne d.1.1 d.1.2
    exact ⟨ht.2, by rw [h]; exact ht.1⟩
  · exact ⟨d.2, Ne.symm h⟩

private lemma colL_some_ne_colR_some {n : Nat} (f : Fin n → Fin 3) (u : Fin n) (d : PairT) :
    colL f (u, some d) ≠ colR f (u, some d) := by
  dsimp only [colL, colR]
  have ht := thirdColor_ne d.1.1 d.1.2
  split_ifs with h1 h2 h2
  · exact absurd (h1.symm.trans h2) (Ne.symm d.2)
  · exact ht.1
  · exact Ne.symm ht.2
  · exact Ne.symm d.2

private lemma colL_ne_colR_of_edge {n : Nat} (E : Fin n → Fin n → Prop) (f : Fin n → Fin 3)
    (hprop : ∀ u v, E u v → f u ≠ f v) (i j : IxT n) (hed : edgeRel E i j) :
    colL f i ≠ colR f j := by
  rcases i with ⟨u, oi⟩
  rcases j with ⟨v, oj⟩
  cases oi with
  | none =>
    cases oj with
    | none =>
      simp only [edgeRel, and_self, ↓reduceIte] at hed
      exact hprop u v hed
    | some d =>
      simp only [edgeRel, reduceCtorEq, and_false, ↓reduceIte, true_or, and_true] at hed
      subst hed
      exact Ne.symm (colR_some_props f u d).2
  | some d =>
    cases oj with
    | none =>
      simp only [edgeRel, reduceCtorEq, false_and, ↓reduceIte, or_true, true_or, and_true] at hed
      subst hed
      exact (colL_some_props f u d).2
    | some d2 =>
      simp [edgeRel] at hed
      rcases hed with ⟨rfl, rfl⟩
      exact colL_some_ne_colR_some f u d

private def leftIdx {n h : Nat} (key : Fin h ≃ IxT n) (f : Fin n → Fin 3) (k : Fin 3) : List Nat :=
  (List.finRange h).filterMap (fun q => if colL f (key q) = k then some q.val else none)

private def rightIdx {n h : Nat} (key : Fin h ≃ IxT n) (f : Fin n → Fin 3) (k : Fin 3) : List Nat :=
  (List.finRange h).filterMap (fun q => if colR f (key q) ≠ k then some (h + q.val) else none)

private def allRightIdx (h : Nat) : List Nat :=
  (List.finRange h).map (fun q => h + q.val)

private lemma length_leftIdx_le {n h : Nat} (key : Fin h ≃ IxT n) (f : Fin n → Fin 3) (k : Fin 3) :
    (leftIdx key f k).length ≤ h := by
  dsimp only [leftIdx]
  calc (List.filterMap _ (List.finRange h)).length
      ≤ (List.finRange h).length := length_filterMap_le _ _
    _ = h := List.length_finRange

private lemma length_rightIdx_le {n h : Nat} (key : Fin h ≃ IxT n) (f : Fin n → Fin 3) (k : Fin 3) :
    (rightIdx key f k).length ≤ h := by
  dsimp only [rightIdx]
  calc (List.filterMap _ (List.finRange h)).length
      ≤ (List.finRange h).length := length_filterMap_le _ _
    _ = h := List.length_finRange

private lemma length_allRightIdx (h : Nat) : (allRightIdx h).length = h := by
  simp [allRightIdx]

private lemma mem_leftIdx {n h : Nat} (key : Fin h ≃ IxT n) (f : Fin n → Fin 3) (k : Fin 3)
    (u : Nat) : u ∈ leftIdx key f k ↔ ∃ q : Fin h, colL f (key q) = k ∧ q.val = u := by
  dsimp only [leftIdx]
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨q, _, hq⟩
    by_cases hc : colL f (key q) = k
    · simp only [hc, ↓reduceIte, Option.some.injEq] at hq
      exact ⟨q, hc, hq⟩
    · simp [hc] at hq
  · rintro ⟨q, hc, rfl⟩
    exact ⟨q, List.mem_finRange q, by simp [hc]⟩

private lemma mem_rightIdx {n h : Nat} (key : Fin h ≃ IxT n) (f : Fin n → Fin 3) (k : Fin 3)
    (u : Nat) : u ∈ rightIdx key f k ↔ ∃ q : Fin h, colR f (key q) ≠ k ∧ h + q.val = u := by
  dsimp only [rightIdx]
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨q, _, hq⟩
    by_cases hc : colR f (key q) ≠ k
    · simp [hc] at hq
      exact ⟨q, hc, hq⟩
    · simp [hc] at hq
  · rintro ⟨q, hc, rfl⟩
    exact ⟨q, List.mem_finRange q, by simp [hc]⟩

private lemma mem_allRightIdx (h u : Nat) :
    u ∈ allRightIdx h ↔ ∃ q : Fin h, h + q.val = u := by
  dsimp only [allRightIdx]
  rw [List.mem_map]
  constructor
  · rintro ⟨q, _, rfl⟩; exact ⟨q, rfl⟩
  · rintro ⟨q, rfl⟩; exact ⟨q, List.mem_finRange q, rfl⟩

private lemma leftIdx_lt {n h : Nat} (key : Fin h ≃ IxT n) (f : Fin n → Fin 3) (k : Fin 3)
    (u : Nat) (hu : u ∈ leftIdx key f k) : u < 2 * h := by
  rw [mem_leftIdx] at hu
  rcases hu with ⟨q, _, rfl⟩
  have := q.isLt
  omega

private lemma rightIdx_lt {n h : Nat} (key : Fin h ≃ IxT n) (f : Fin n → Fin 3) (k : Fin 3)
    (u : Nat) (hu : u ∈ rightIdx key f k) : u < 2 * h := by
  rw [mem_rightIdx] at hu
  rcases hu with ⟨q, _, rfl⟩
  have := q.isLt
  omega

private lemma allRightIdx_lt (h u : Nat) (hu : u ∈ allRightIdx h) : u < 2 * h := by
  rw [mem_allRightIdx] at hu
  rcases hu with ⟨q, rfl⟩
  have := q.isLt
  omega

private lemma getD_leftFull_lt_h {n h m : Nat} (key : Fin h ≃ IxT n) (i : IxT n) (q : Fin h) :
    (leftVec key i ++ List.replicate m true ++ [false, true]).getD q.val false =
      @decide (key q = i) (Classical.propDecidable _) := by
  have h1 : q.val < (leftVec key i ++ List.replicate m true).length := by
    simp [length_leftVec]; have := q.isLt; omega
  have h2 : q.val < (leftVec key i).length := by
    rw [length_leftVec]; have := q.isLt; omega
  rw [getD_append_left _ _ _ _ h1, getD_append_left _ _ _ _ h2]
  dsimp only [leftVec]
  have h3 : q.val < (List.ofFn (fun k : Fin h => @decide (key k = i) (Classical.propDecidable _))).length := by
    simp [q.isLt]
  rw [getD_append_left _ _ _ _ h3, getD_ofFn_lt _ _ _ q.isLt]

private lemma getD_leftFull_hi_h {n h m : Nat} (key : Fin h ≃ IxT n) (i : IxT n) (q : Fin h) :
    (leftVec key i ++ List.replicate m true ++ [false, true]).getD (h + q.val) false = false := by
  have h1 : h + q.val < (leftVec key i ++ List.replicate m true).length := by
    simp [length_leftVec]; have := q.isLt; omega
  have h2 : h + q.val < (leftVec key i).length := by
    rw [length_leftVec]; have := q.isLt; omega
  rw [getD_append_left _ _ _ _ h1, getD_append_left _ _ _ _ h2]
  dsimp only [leftVec]
  have h3 : (List.ofFn (fun k : Fin h => @decide (key k = i) (Classical.propDecidable _))).length ≤ h + q.val := by
    simp
  rw [getD_append_right _ _ _ _ h3]
  have h4 : h + q.val - (List.ofFn (fun k : Fin h => @decide (key k = i) (Classical.propDecidable _))).length < h := by
    simp [q.isLt]
  exact getD_replicate_lt _ _ _ _ h4

private lemma getD_rightFull_lt_h {n h m : Nat} (E : Fin n → Fin n → Prop) (key : Fin h ≃ IxT n)
    (j : IxT n) (q : Fin h) :
    (rightVec E key j ++ List.replicate m true ++ [false, true]).getD q.val false =
      @decide (edgeRel E (key q) j) (Classical.propDecidable _) := by
  have h1 : q.val < (rightVec E key j ++ List.replicate m true).length := by
    simp [length_rightVec]; have := q.isLt; omega
  have h2 : q.val < (rightVec E key j).length := by
    rw [length_rightVec]; have := q.isLt; omega
  rw [getD_append_left _ _ _ _ h1, getD_append_left _ _ _ _ h2]
  dsimp only [rightVec]
  have h3 : q.val < (List.ofFn (fun k : Fin h => @decide (edgeRel E (key k) j) (Classical.propDecidable _))).length := by
    simp [q.isLt]
  rw [getD_append_left _ _ _ _ h3, getD_ofFn_lt _ _ _ q.isLt]

private lemma getD_rightFull_hi_h {n h m : Nat} (E : Fin n → Fin n → Prop) (key : Fin h ≃ IxT n)
    (j : IxT n) (q : Fin h) :
    (rightVec E key j ++ List.replicate m true ++ [false, true]).getD (h + q.val) false =
      @decide (key q = j) (Classical.propDecidable _) := by
  have h1 : h + q.val < (rightVec E key j ++ List.replicate m true).length := by
    simp [length_rightVec]; have := q.isLt; omega
  have h2 : h + q.val < (rightVec E key j).length := by
    rw [length_rightVec]; have := q.isLt; omega
  rw [getD_append_left _ _ _ _ h1, getD_append_left _ _ _ _ h2]
  dsimp only [rightVec]
  have h3 : (List.ofFn (fun k : Fin h => @decide (edgeRel E (key k) j) (Classical.propDecidable _))).length ≤ h + q.val := by
    simp
  rw [getD_append_right _ _ _ _ h3]
  have hlen : (List.ofFn (fun k : Fin h => @decide (edgeRel E (key k) j) (Classical.propDecidable _))).length = h := by
    simp
  rw [hlen, Nat.add_sub_cancel_left]
  exact getD_ofFn_lt _ _ _ q.isLt

private lemma any_leftIdx_on_left {n h m : Nat} (key : Fin h ≃ IxT n) (f : Fin n → Fin 3)
    (i : IxT n) (k : Fin 3) :
    (leftIdx key f k).any (fun u => (leftVec key i ++ List.replicate m true ++ [false, true]).getD u false) =
      decide (k = colL f i) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨u, hu, hget⟩
    rw [mem_leftIdx] at hu
    rcases hu with ⟨q, hcol, rfl⟩
    rw [getD_leftFull_lt_h] at hget
    have hki : key q = i := of_cdecide_true hget
    rw [← hki, hcol]
  · intro hk
    refine ⟨(key.symm i).val, ?_, ?_⟩
    · rw [mem_leftIdx]
      exact ⟨key.symm i, by simp [hk], rfl⟩
    · rw [getD_leftFull_lt_h]
      exact cdecide_true (key.apply_symm_apply i)

private lemma any_rightIdx_on_left {n h m : Nat} (key : Fin h ≃ IxT n) (f : Fin n → Fin 3)
    (i : IxT n) (k : Fin 3) :
    (rightIdx key f k).any (fun u => (leftVec key i ++ List.replicate m true ++ [false, true]).getD u false) =
      false := by
  cases h : (rightIdx key f k).any (fun u => (leftVec key i ++ List.replicate m true ++ [false, true]).getD u false)
  · rfl
  · rw [List.any_eq_true] at h
    rcases h with ⟨u, hu, hget⟩
    rw [mem_rightIdx] at hu
    rcases hu with ⟨q, _, rfl⟩
    rw [getD_leftFull_hi_h] at hget
    cases hget

private lemma any_allRightIdx_on_left {n h m : Nat} (key : Fin h ≃ IxT n) (i : IxT n) :
    (allRightIdx h).any (fun u => (leftVec key i ++ List.replicate m true ++ [false, true]).getD u false) =
      false := by
  cases h : (allRightIdx h).any (fun u => (leftVec key i ++ List.replicate m true ++ [false, true]).getD u false)
  · rfl
  · rw [List.any_eq_true] at h
    rcases h with ⟨u, hu, hget⟩
    rw [mem_allRightIdx] at hu
    rcases hu with ⟨q, rfl⟩
    rw [getD_leftFull_hi_h] at hget
    cases hget

private lemma any_rightIdx_on_right {n h m : Nat} (E : Fin n → Fin n → Prop) (key : Fin h ≃ IxT n)
    (f : Fin n → Fin 3) (j : IxT n) (k : Fin 3) :
    (rightIdx key f k).any (fun u => (rightVec E key j ++ List.replicate m true ++ [false, true]).getD u false) =
      decide (k ≠ colR f j) := by
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨u, hu, hget⟩
    rw [mem_rightIdx] at hu
    rcases hu with ⟨q, hcol, rfl⟩
    rw [getD_rightFull_hi_h] at hget
    have hkj : key q = j := of_cdecide_true hget
    rw [← hkj]
    exact Ne.symm hcol
  · intro hk
    refine ⟨h + (key.symm j).val, ?_, ?_⟩
    · rw [mem_rightIdx]
      exact ⟨key.symm j, by simp [Ne.symm hk], rfl⟩
    · rw [getD_rightFull_hi_h]
      exact cdecide_true (key.apply_symm_apply j)

private lemma any_allRightIdx_on_right {n h m : Nat} (E : Fin n → Fin n → Prop)
    (key : Fin h ≃ IxT n) (j : IxT n) :
    (allRightIdx h).any (fun u => (rightVec E key j ++ List.replicate m true ++ [false, true]).getD u false) =
      true := by
  rw [List.any_eq_true]
  refine ⟨h + (key.symm j).val, ?_, ?_⟩
  · rw [mem_allRightIdx]
    exact ⟨key.symm j, rfl⟩
  · rw [getD_rightFull_hi_h]
    exact cdecide_true (key.apply_symm_apply j)

private lemma any_both_on_right_proper {n h m : Nat} (E : Fin n → Fin n → Prop)
    (key : Fin h ≃ IxT n) (f : Fin n → Fin 3) (hprop : ∀ u v, E u v → f u ≠ f v)
    (j : IxT n) (k : Fin 3) :
    (leftIdx key f k ++ rightIdx key f k).any
      (fun u => (rightVec E key j ++ List.replicate m true ++ [false, true]).getD u false) =
      decide (k ≠ colR f j) := by
  rw [List.any_append, any_rightIdx_on_right]
  by_cases hk : k ≠ colR f j
  · simp [hk]
  · have hkeq : k = colR f j := by
      by_contra hne; exact hk hne
    have hleftF : (leftIdx key f k).any
        (fun u => (rightVec E key j ++ List.replicate m true ++ [false, true]).getD u false) = false := by
      cases h : (leftIdx key f k).any
          (fun u => (rightVec E key j ++ List.replicate m true ++ [false, true]).getD u false)
      · rfl
      · rw [List.any_eq_true] at h
        rcases h with ⟨u, hu, hget⟩
        rw [mem_leftIdx] at hu
        rcases hu with ⟨q, hcol, rfl⟩
        rw [getD_rightFull_lt_h] at hget
        have hed : edgeRel E (key q) j := of_cdecide_true hget
        have hne := colL_ne_colR_of_edge E f hprop (key q) j hed
        rw [hcol, hkeq] at hne
        exact False.elim (hne rfl)
    rw [hleftF, Bool.false_or]

private lemma getD_input_pad_shore (h m : Nat) (s : List Bool) (hs : s.length = 2 * h) :
    (∀ r < m, (s ++ List.replicate m true ++ [false, true]).getD (2 * h + r) false = true) ∧
      (s ++ List.replicate m true ++ [false, true]).getD (2 * h + m) false = false ∧
      (s ++ List.replicate m true ++ [false, true]).getD (2 * h + m + 1) false = true := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    have h1 : 2 * h + r < (s ++ List.replicate m true).length := by simp [hs]; omega
    rw [getD_append_left _ _ _ _ h1]
    have h2 : s.length ≤ 2 * h + r := by omega
    rw [getD_append_right _ _ _ _ h2, hs, Nat.add_sub_cancel_left]
    exact getD_replicate_lt _ _ _ _ hr
  · have hlen : (s ++ List.replicate m true).length = 2 * h + m := by simp [hs]
    have h1 : (s ++ List.replicate m true).length ≤ 2 * h + m := by omega
    rw [getD_append_right _ _ _ _ h1, hlen, Nat.sub_self]
    rfl
  · have hlen : (s ++ List.replicate m true).length = 2 * h + m := by simp [hs]
    have h1 : (s ++ List.replicate m true).length ≤ 2 * h + m + 1 := by omega
    rw [getD_append_right _ _ _ _ h1, hlen]
    have hsub : 2 * h + m + 1 - (2 * h + m) = 1 := by omega
    rw [hsub]
    rfl

private lemma getD_input_pad_clock (h m r : Nat) :
    (∀ i < m, (clockFull h m r).getD (2 * h + i) false = decide (i < r)) ∧
      (clockFull h m r).getD (2 * h + m) false = false ∧
      (clockFull h m r).getD (2 * h + m + 1) false = true := by
  dsimp only [clockFull]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have h1 : 2 * h + i < (List.replicate (2 * h) false ++ List.ofFn (fun x : Fin m => decide (x.val < r))).length := by
      simp; omega
    rw [getD_append_left _ _ _ _ h1]
    have h2 : (List.replicate (2 * h) false).length ≤ 2 * h + i := by simp
    rw [getD_append_right _ _ _ _ h2]
    have hlen : (List.replicate (2 * h) false).length = 2 * h := by simp
    rw [hlen, Nat.add_sub_cancel_left]
    exact getD_ofFn_lt _ _ _ hi
  · have hlen : (List.replicate (2 * h) false ++ List.ofFn (fun x : Fin m => decide (x.val < r))).length = 2 * h + m := by
      simp
    have h1 : (List.replicate (2 * h) false ++ List.ofFn (fun x : Fin m => decide (x.val < r))).length ≤ 2 * h + m := by
      omega
    rw [getD_append_right _ _ _ _ h1, hlen, Nat.sub_self]
    rfl
  · have hlen : (List.replicate (2 * h) false ++ List.ofFn (fun x : Fin m => decide (x.val < r))).length = 2 * h + m := by
      simp
    have h1 : (List.replicate (2 * h) false ++ List.ofFn (fun x : Fin m => decide (x.val < r))).length ≤ 2 * h + m + 1 := by
      omega
    rw [getD_append_right _ _ _ _ h1, hlen]
    have hsub : 2 * h + m + 1 - (2 * h + m) = 1 := by omega
    rw [hsub]
    rfl

private def clkInputWires (h m : Nat) : List Nat :=
  (List.finRange m).map (fun r => 2 * h + r.val)

private lemma getD_clkInputWires (h m falseW r : Nat) (hr : r < m) :
    (clkInputWires h m).getD r falseW = 2 * h + r := by
  dsimp only [clkInputWires]
  have hlen : r < ((List.finRange m).map (fun x => 2 * h + x.val)).length := by simp [hr]
  rw [getD_eq_getElem _ _ _ hlen]
  simp

private def finalizeTaps (N : Nat) (gs : List Gate) (fullPad clkOut s0 s1 s2 : Nat) :
    Circuit × (Fin 3 → Nat) :=
  let r1 := emitAnd N gs fullPad s0
  let r2 := emitOr N r1.1 clkOut r1.2
  let r3 := emitAnd N r2.1 fullPad s1
  let r4 := emitAnd N r3.1 fullPad s2
  let C : Circuit := { gates := r4.1, output := r2.2 }
  let p : Fin 3 → Nat := fun k =>
    match k.val with
    | 0 => r2.2
    | 1 => r3.2
    | _ => r4.2
  (C, p)

private lemma finalizeTaps_spec (N : Nat) (gs : List Gate) (fullPad clkOut s0 s1 s2 : Nat)
    (hwf : WF N gs) (hpad : fullPad < N + gs.length) (hclk : clkOut < N + gs.length)
    (hs0 : s0 < N + gs.length) (hs1 : s1 < N + gs.length) (hs2 : s2 < N + gs.length) :
    let res := finalizeTaps N gs fullPad clkOut s0 s1 s2
    PEqualNP.MetaComplexity.FanInTwo res.1 ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack N res.1 ∧
      res.1.output < N + res.1.size ∧ (∀ k, res.2 k < N + res.1.size) ∧ res.2 0 = res.1.output ∧
      res.1.size = gs.length + 4 ∧
      PEqualNP.NotBracket.notCount res.1 = notCountList gs ∧
      ∀ v : List Bool, v.length = N →
        (wireEval res.1 v (res.2 0) =
          (((gs.foldl stepWire v).getD clkOut false) ||
            (((gs.foldl stepWire v).getD fullPad false) && ((gs.foldl stepWire v).getD s0 false)))) ∧
        (wireEval res.1 v (res.2 1) =
          (((gs.foldl stepWire v).getD fullPad false) && ((gs.foldl stepWire v).getD s1 false))) ∧
        (wireEval res.1 v (res.2 2) =
          (((gs.foldl stepWire v).getD fullPad false) && ((gs.foldl stepWire v).getD s2 false))) := by
  have h1 := emitAnd_spec N gs fullPad s0 hwf hpad hs0
  set r1 := emitAnd N gs fullPad s0
  have hclk1 : clkOut < N + r1.1.length := by have := h1.2.2.1; omega
  have h2 := emitOr_spec N r1.1 clkOut r1.2 h1.2.1 hclk1 h1.2.2.2.1
  set r2 := emitOr N r1.1 clkOut r1.2
  have hpad2 : fullPad < N + r2.1.length := by have := h2.2.2.1; have := h1.2.2.1; omega
  have hs1_2 : s1 < N + r2.1.length := by have := h2.2.2.1; have := h1.2.2.1; omega
  have h3 := emitAnd_spec N r2.1 fullPad s1 h2.2.1 hpad2 hs1_2
  set r3 := emitAnd N r2.1 fullPad s1
  have hpad3 : fullPad < N + r3.1.length := by have := h3.2.2.1; omega
  have hs2_3 : s2 < N + r3.1.length := by have := h3.2.2.1; omega
  have h4 := emitAnd_spec N r3.1 fullPad s2 h3.2.1 hpad3 hs2_3
  set r4 := emitAnd N r3.1 fullPad s2
  have hExt24 : Extends r2.1 r4.1 := extends_trans h3.1 h4.1
  have hExtG2 : Extends gs r2.1 := extends_trans h1.1 h2.1
  have hExtG3 : Extends gs r3.1 := extends_trans hExtG2 h3.1
  refine ⟨h4.2.1.1, readsBack_of_wf h4.2.1 _, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · change r2.2 < N + r4.1.length
    have := h2.2.2.2.1; have := h3.2.2.1; have := h4.2.2.1; omega
  · intro k
    fin_cases k
    · change r2.2 < N + r4.1.length; have := h2.2.2.2.1; have := h3.2.2.1; have := h4.2.2.1; omega
    · change r3.2 < N + r4.1.length; have := h3.2.2.2.1; have := h4.2.2.1; omega
    · change r4.2 < N + r4.1.length; exact h4.2.2.2.1
  · change r4.1.length = gs.length + 4
    rw [h4.2.2.1, h3.2.2.1, h2.2.2.1, h1.2.2.1]
  · dsimp only [finalizeTaps]
    rw [notCount_eq_notCountList, h4.2.2.2.2.1, h3.2.2.2.2.1, h2.2.2.2.2.1, h1.2.2.2.2.1]
  · intro v hv
    refine ⟨?_, ?_, ?_⟩
    · change (r4.1.foldl stepWire v).getD r2.2 false = _
      rw [getD_foldl_extends hExt24 v _ (by rw [hv]; exact h2.2.2.2.1),
          h2.2.2.2.2.2 v hv,
          getD_foldl_extends h1.1 v _ (by rw [hv]; exact hclk),
          h1.2.2.2.2.2 v hv]
    · change (r4.1.foldl stepWire v).getD r3.2 false = _
      rw [getD_foldl_extends h4.1 v _ (by rw [hv]; exact h3.2.2.2.1),
          h3.2.2.2.2.2 v hv,
          getD_foldl_extends hExtG2 v _ (by rw [hv]; exact hpad),
          getD_foldl_extends hExtG2 v _ (by rw [hv]; exact hs1)]
    · change (r4.1.foldl stepWire v).getD r4.2 false = _
      rw [h4.2.2.2.2.2 v hv,
          getD_foldl_extends hExtG3 v _ (by rw [hv]; exact hpad),
          getD_foldl_extends hExtG3 v _ (by rw [hv]; exact hs2)]

private lemma fullPad_eval (h b : Nat) (s : List Bool) (hs : s.length = 2 * h) :
    let m := clockLen b
    let fullPad := if b = 0 then 2 * h + m + 1 else 2 * h + (m - 1)
    fullPad < 2 * h + m + 2 ∧
      (s ++ List.replicate m true ++ [false, true]).getD fullPad false = true ∧
      ∀ j : Fin m, (clockFull h m j.val).getD fullPad false = false := by
  dsimp only
  set m := clockLen b
  by_cases hb : b = 0
  · subst hb
    have hm0 : m = 0 := rfl
    simp only [↓reduceIte, hm0]
    refine ⟨by omega, (getD_input_pad_shore h 0 s hs).2.2, ?_⟩
    intro j
    exact Fin.elim0 j
  · have hb1 : ∃ b', b = b' + 1 := Nat.exists_eq_succ_of_ne_zero hb
    rcases hb1 with ⟨b', rfl⟩
    have hm2 : 2 ≤ m := clockLen_ge_two b'
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    refine ⟨by omega, (getD_input_pad_shore h m s hs).1 (m - 1) (by omega), ?_⟩
    intro j
    rw [(getD_input_pad_clock h m j.val).1 (m - 1) (by omega)]
    have hnot : ¬(m - 1 < j.val) := by have := j.isLt; omega
    simp [hnot]

private lemma partB_proper {n b h : Nat} (E : Fin n → Fin n → Prop) (f : Fin n → Fin 3)
    (key : Fin h ≃ IxT n) (hh : h = 7 * n) (hprop : ∀ u v, E u v → f u ≠ f v) :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    let m := 2 * (2 ^ b - 1)
    let w := 2 * h + m
    ∃ C : Circuit, ∃ p : Fin 3 → Nat,
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (w + 2) C ∧
      C.output < w + 2 + C.size ∧ (∀ k, p k < w + 2 + C.size) ∧ p 0 = C.output ∧
      (∀ i : IxT n, ∃ a : Fin 3, (∀ d : PairT, i.2 = some d → a ≠ d.val.1) ∧
        ∀ k, (C.wires (leftVec key i ++ List.replicate m true ++ [false, true])).getD (p k) false =
          decide (k = a)) ∧
      (∀ j : IxT n, ∃ a : Fin 3, (∀ d : PairT, j.2 = some d → a ≠ d.val.2) ∧
        ∀ k, (C.wires (rightVec E key j ++ List.replicate m true ++ [false, true])).getD (p k) false =
          decide (k ≠ a)) ∧
      (∀ (j : Fin m) (k : Fin 3),
        (C.wires (List.replicate (2 * h) false ++ List.ofFn (fun i : Fin m => decide (i < j)) ++
          [false, true])).getD (p k) false = decide (k = 0 ∧ j.val % 2 = 0)) ∧
      (∀ (i : Fin n) (k : Fin 3),
        (C.wires (leftVec key (i, none) ++ List.replicate m true ++ [false, true])).getD (p k) false =
          decide (k = f i)) ∧
      PEqualNP.NotBracket.notCount C = b ∧ C.size ≤ 100 * (n + m + 1) := by
  dsimp only
  let m := clockLen b
  let w := 2 * h + m
  let N := w + 2
  let falseW := w
  let fullPad := if b = 0 then w + 1 else 2 * h + (m - 1)
  have huClk : ∀ r < m, (clkInputWires h m).getD r falseW < N + ([] : List Gate).length := by
    intro r hr
    rw [getD_clkInputWires h m falseW r hr]
    omega
  obtain ⟨hExtC, hWfC, hOutC, hLenC, hNotC, hEvalC⟩ :=
    buildClock_spec b N [] falseW (clkInputWires h m) (wf_nil N) (by omega) huClk
  set rC := buildClock b N [] falseW (clkInputWires h m)
  have hIdxLt : ∀ (k : Fin 3) (gs : List Gate), ∀ u ∈ leftIdx key f k ++ rightIdx key f k, u < N + gs.length := by
    intro k gs u hu
    rw [List.mem_append] at hu
    rcases hu with hu | hu
    · have := leftIdx_lt key f k u hu; omega
    · have := rightIdx_lt key f k u hu; omega
  have hS0 := emitOrList_spec N rC.1 falseW (leftIdx key f 0 ++ rightIdx key f 0)
    hWfC (by omega) (hIdxLt 0 rC.1)
  set rS0 := emitOrList N rC.1 falseW (leftIdx key f 0 ++ rightIdx key f 0)
  have hS1 := emitOrList_spec N rS0.1 falseW (leftIdx key f 1 ++ rightIdx key f 1)
    hS0.2.1 (by omega) (hIdxLt 1 rS0.1)
  set rS1 := emitOrList N rS0.1 falseW (leftIdx key f 1 ++ rightIdx key f 1)
  have hS2 := emitOrList_spec N rS1.1 falseW (leftIdx key f 2 ++ rightIdx key f 2)
    hS1.2.1 (by omega) (hIdxLt 2 rS1.1)
  set rS2 := emitOrList N rS1.1 falseW (leftIdx key f 2 ++ rightIdx key f 2)
  have hExtC2 : Extends rC.1 rS2.1 := extends_trans hS0.1 (extends_trans hS1.1 hS2.1)
  have hExt02 : Extends rS0.1 rS2.1 := extends_trans hS1.1 hS2.1
  have hpadLt : fullPad < N + rS2.1.length := by
    have hpf : fullPad < N := (fullPad_eval h b (List.replicate (2 * h) false) (by simp)).1
    omega
  have hclkLt : rC.2 < N + rS2.1.length := by
    have := extends_length_le hExtC2; omega
  have hs0Lt : rS0.2 < N + rS2.1.length := by
    have := extends_length_le hExt02; have := hS0.2.2.2.1; omega
  have hs1Lt : rS1.2 < N + rS2.1.length := by
    have := extends_length_le hS2.1; have := hS1.2.2.2.1; omega
  have hFin := finalizeTaps_spec N rS2.1 fullPad rC.2 rS0.2 rS1.2 rS2.2
    hS2.2.1 hpadLt hclkLt hs0Lt hs1Lt hS2.2.2.2.1
  set res := finalizeTaps N rS2.1 fullPad rC.2 rS0.2 rS1.2 rS2.2
  have hclkShore : ∀ s : List Bool, s.length = 2 * h →
      (rC.1.foldl stepWire (s ++ List.replicate m true ++ [false, true])).getD rC.2 false = false := by
    intro s hs
    have hpad := getD_input_pad_shore h m s hs
    have h1 := hEvalC (s ++ List.replicate m true ++ [false, true]) m
      (by simp [hs]; omega) hpad.2.1 (Nat.le_refl _) (by
        intro r hr
        have hr' : r < m := hr
        rw [List.foldl_nil, getD_clkInputWires h m falseW r hr', hpad.1 r hr']
        simp [hr'])
    have hnot : ¬(m < clockLen b) := by dsimp only [m]; omega
    simpa [hnot] using h1
  refine ⟨res.1, res.2, hFin.1, hFin.2.1, hFin.2.2.1, hFin.2.2.2.1, hFin.2.2.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨colL f i, ?_, ?_⟩
    · intro d hid
      rcases i with ⟨u, oi⟩
      dsimp only at hid
      subst hid
      exact (colL_some_props f u d).1
    · intro k
      set v := leftVec key i ++ List.replicate m true ++ [false, true]
      have hv : v.length = N := length_leftFull key m i
      have hpad := getD_input_pad_shore h m (leftVec key i) (length_leftVec key i)
      have hclkVal : (rC.1.foldl stepWire v).getD rC.2 false = false :=
        hclkShore (leftVec key i) (length_leftVec key i)
      have hfullVal : (rS2.1.foldl stepWire v).getD fullPad false = true := by
        have hlt : fullPad < v.length := by
          rw [hv]; exact (fullPad_eval h b (leftVec key i) (length_leftVec key i)).1
        rw [getD_foldl_stepWire_of_lt _ _ _ hlt]
        exact (fullPad_eval h b (leftVec key i) (length_leftVec key i)).2.1
      have hclk2 : (rS2.1.foldl stepWire v).getD rC.2 false = false := by
        rw [getD_foldl_extends hExtC2 v _ (by rw [hv]; exact hOutC)]
        exact hclkVal
      have hShoreVal : ∀ (q : Fin 3) (gs : List Gate),
          (leftIdx key f q ++ rightIdx key f q).any (fun u => (gs.foldl stepWire v).getD u false) =
            decide (q = colL f i) := by
        intro q gs
        have hcongr : (leftIdx key f q ++ rightIdx key f q).any (fun u => (gs.foldl stepWire v).getD u false) =
            (leftIdx key f q ++ rightIdx key f q).any (fun u => v.getD u false) := by
          apply Bool.eq_iff_iff.mpr
          simp only [List.any_eq_true]
          constructor
          · rintro ⟨u, hu, hget⟩
            have hlt : u < v.length := by
              rw [hv]; have := hIdxLt q [] u hu; simp at this; omega
            rw [getD_foldl_stepWire_of_lt _ _ _ hlt] at hget
            exact ⟨u, hu, hget⟩
          · rintro ⟨u, hu, hget⟩
            have hlt : u < v.length := by
              rw [hv]; have := hIdxLt q [] u hu; simp at this; omega
            refine ⟨u, hu, ?_⟩
            rw [getD_foldl_stepWire_of_lt _ _ _ hlt]
            exact hget
        rw [hcongr, List.any_append, any_leftIdx_on_left, any_rightIdx_on_left, Bool.or_false]
      have hTaps := hFin.2.2.2.2.2.2.2 v hv
      have hfvC : (rC.1.foldl stepWire v).getD falseW false = false := by
        rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
      have hfv0 : (rS0.1.foldl stepWire v).getD falseW false = false := by
        rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
      have hfv1 : (rS1.1.foldl stepWire v).getD falseW false = false := by
        rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
      have hs0v : (rS2.1.foldl stepWire v).getD rS0.2 false = decide ((0 : Fin 3) = colL f i) := by
        rw [getD_foldl_extends hExt02 v _ (by rw [hv]; exact hS0.2.2.2.1),
            hS0.2.2.2.2.2 v hv hfvC, hShoreVal 0 rC.1]
      have hs1v : (rS2.1.foldl stepWire v).getD rS1.2 false = decide ((1 : Fin 3) = colL f i) := by
        rw [getD_foldl_extends hS2.1 v _ (by rw [hv]; exact hS1.2.2.2.1),
            hS1.2.2.2.2.2 v hv hfv0, hShoreVal 1 rS0.1]
      have hs2v : (rS2.1.foldl stepWire v).getD rS2.2 false = decide ((2 : Fin 3) = colL f i) := by
        rw [hS2.2.2.2.2.2 v hv hfv1, hShoreVal 2 rS1.1]
      fin_cases k
      · change wireEval res.1 v (res.2 0) = _
        rw [hTaps.1, hclk2, hfullVal, hs0v]
        simpa using decide_irrel ((0 : Fin 3) = colL f i) _ _
      · change wireEval res.1 v (res.2 1) = _
        rw [hTaps.2.1, hfullVal, hs1v]
        simpa using decide_irrel ((1 : Fin 3) = colL f i) _ _
      · change wireEval res.1 v (res.2 2) = _
        rw [hTaps.2.2, hfullVal, hs2v]
        simpa using decide_irrel ((2 : Fin 3) = colL f i) _ _
  · intro j
    refine ⟨colR f j, ?_, ?_⟩
    · intro d hjd
      rcases j with ⟨u, oj⟩
      dsimp only at hjd
      subst hjd
      exact (colR_some_props f u d).1
    · intro k
      set v := rightVec E key j ++ List.replicate m true ++ [false, true]
      have hv : v.length = N := length_rightFull E key m j
      have hpad := getD_input_pad_shore h m (rightVec E key j) (length_rightVec E key j)
      have hclkVal : (rC.1.foldl stepWire v).getD rC.2 false = false :=
        hclkShore (rightVec E key j) (length_rightVec E key j)
      have hfullVal : (rS2.1.foldl stepWire v).getD fullPad false = true := by
        have hlt : fullPad < v.length := by
          rw [hv]; exact (fullPad_eval h b (rightVec E key j) (length_rightVec E key j)).1
        rw [getD_foldl_stepWire_of_lt _ _ _ hlt]
        exact (fullPad_eval h b (rightVec E key j) (length_rightVec E key j)).2.1
      have hclk2 : (rS2.1.foldl stepWire v).getD rC.2 false = false := by
        rw [getD_foldl_extends hExtC2 v _ (by rw [hv]; exact hOutC)]
        exact hclkVal
      have hShoreVal : ∀ (q : Fin 3) (gs : List Gate),
          (leftIdx key f q ++ rightIdx key f q).any (fun u => (gs.foldl stepWire v).getD u false) =
            decide (q ≠ colR f j) := by
        intro q gs
        have hcongr : (leftIdx key f q ++ rightIdx key f q).any (fun u => (gs.foldl stepWire v).getD u false) =
            (leftIdx key f q ++ rightIdx key f q).any (fun u => v.getD u false) := by
          apply Bool.eq_iff_iff.mpr
          simp only [List.any_eq_true]
          constructor
          · rintro ⟨u, hu, hget⟩
            have hlt : u < v.length := by
              rw [hv]; have := hIdxLt q [] u hu; simp at this; omega
            rw [getD_foldl_stepWire_of_lt _ _ _ hlt] at hget
            exact ⟨u, hu, hget⟩
          · rintro ⟨u, hu, hget⟩
            have hlt : u < v.length := by
              rw [hv]; have := hIdxLt q [] u hu; simp at this; omega
            refine ⟨u, hu, ?_⟩
            rw [getD_foldl_stepWire_of_lt _ _ _ hlt]
            exact hget
        rw [hcongr]
        exact any_both_on_right_proper E key f hprop j q
      have hTaps := hFin.2.2.2.2.2.2.2 v hv
      have hfvC : (rC.1.foldl stepWire v).getD falseW false = false := by
        rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
      have hfv0 : (rS0.1.foldl stepWire v).getD falseW false = false := by
        rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
      have hfv1 : (rS1.1.foldl stepWire v).getD falseW false = false := by
        rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
      have hs0v : (rS2.1.foldl stepWire v).getD rS0.2 false = decide ((0 : Fin 3) ≠ colR f j) := by
        rw [getD_foldl_extends hExt02 v _ (by rw [hv]; exact hS0.2.2.2.1),
            hS0.2.2.2.2.2 v hv hfvC, hShoreVal 0 rC.1]
      have hs1v : (rS2.1.foldl stepWire v).getD rS1.2 false = decide ((1 : Fin 3) ≠ colR f j) := by
        rw [getD_foldl_extends hS2.1 v _ (by rw [hv]; exact hS1.2.2.2.1),
            hS1.2.2.2.2.2 v hv hfv0, hShoreVal 1 rS0.1]
      have hs2v : (rS2.1.foldl stepWire v).getD rS2.2 false = decide ((2 : Fin 3) ≠ colR f j) := by
        rw [hS2.2.2.2.2.2 v hv hfv1, hShoreVal 2 rS1.1]
      fin_cases k
      · change wireEval res.1 v (res.2 0) = _
        rw [hTaps.1, hclk2, hfullVal, hs0v]
        simpa using decide_irrel ((0 : Fin 3) ≠ colR f j) _ _
      · change wireEval res.1 v (res.2 1) = _
        rw [hTaps.2.1, hfullVal, hs1v]
        simpa using decide_irrel ((1 : Fin 3) ≠ colR f j) _ _
      · change wireEval res.1 v (res.2 2) = _
        rw [hTaps.2.2, hfullVal, hs2v]
        simpa using decide_irrel ((2 : Fin 3) ≠ colR f j) _ _
  · intro j k
    have hcf : List.replicate (2 * h) false ++
        List.ofFn (fun i : Fin (2 * (2 ^ b - 1)) => @decide (i < j) (Classical.propDecidable _)) ++
        [false, true] = clockFull h m j.val := clockFull_eq_fin h m j
    rw [hcf]
    set v := clockFull h m j.val
    have hv : v.length = N := length_clockFull h m j.val
    have hpad := getD_input_pad_clock h m j.val
    have hclkVal : (rC.1.foldl stepWire v).getD rC.2 false = decide (j.val % 2 = 0) := by
      have h1 := hEvalC v j.val hv hpad.2.1 (Nat.le_of_lt j.isLt) (by
        intro r hr
        have hr' : r < m := hr
        rw [List.foldl_nil, getD_clkInputWires h m falseW r hr', hpad.1 r hr'])
      have hjlt : j.val < clockLen b := j.isLt
      simpa [hjlt] using h1
    have hfullVal : (rS2.1.foldl stepWire v).getD fullPad false = false := by
      have hlt : fullPad < v.length := by
        rw [hv]; exact (fullPad_eval h b (List.replicate (2 * h) false) (by simp)).1
      rw [getD_foldl_stepWire_of_lt _ _ _ hlt]
      exact (fullPad_eval h b (List.replicate (2 * h) false) (by simp)).2.2 j
    have hclk2 : (rS2.1.foldl stepWire v).getD rC.2 false = decide (j.val % 2 = 0) := by
      rw [getD_foldl_extends hExtC2 v _ (by rw [hv]; exact hOutC)]
      exact hclkVal
    have hTaps := hFin.2.2.2.2.2.2.2 v hv
    fin_cases k
    · change wireEval res.1 v (res.2 0) = _
      rw [hTaps.1, hclk2, hfullVal]
      simp only [Bool.false_and, Bool.or_false]
      have hiff : ((0 : Fin 3) = 0 ∧ j.val % 2 = 0) ↔ j.val % 2 = 0 := by simp
      by_cases hmod : j.val % 2 = 0
      · simp [hmod]
      · simp [hmod]
    · change wireEval res.1 v (res.2 1) = _
      rw [hTaps.2.1, hfullVal]
      simp
    · change wireEval res.1 v (res.2 2) = _
      rw [hTaps.2.2, hfullVal]
      simp
  · intro u k
    set i : IxT n := (u, none)
    set v := leftVec key i ++ List.replicate m true ++ [false, true]
    have hv : v.length = N := length_leftFull key m i
    have hpad := getD_input_pad_shore h m (leftVec key i) (length_leftVec key i)
    have hclkVal : (rC.1.foldl stepWire v).getD rC.2 false = false :=
      hclkShore (leftVec key i) (length_leftVec key i)
    have hfullVal : (rS2.1.foldl stepWire v).getD fullPad false = true := by
      have hlt : fullPad < v.length := by
        rw [hv]; exact (fullPad_eval h b (leftVec key i) (length_leftVec key i)).1
      rw [getD_foldl_stepWire_of_lt _ _ _ hlt]
      exact (fullPad_eval h b (leftVec key i) (length_leftVec key i)).2.1
    have hclk2 : (rS2.1.foldl stepWire v).getD rC.2 false = false := by
      rw [getD_foldl_extends hExtC2 v _ (by rw [hv]; exact hOutC)]
      exact hclkVal
    have hShoreVal : ∀ (q : Fin 3) (gs : List Gate),
        (leftIdx key f q ++ rightIdx key f q).any (fun x => (gs.foldl stepWire v).getD x false) =
          decide (q = f u) := by
      intro q gs
      have hcongr : (leftIdx key f q ++ rightIdx key f q).any (fun x => (gs.foldl stepWire v).getD x false) =
          (leftIdx key f q ++ rightIdx key f q).any (fun x => v.getD x false) := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true]
        constructor
        · rintro ⟨x, hx, hget⟩
          have hlt : x < v.length := by
            rw [hv]; have := hIdxLt q [] x hx; simp at this; omega
          rw [getD_foldl_stepWire_of_lt _ _ _ hlt] at hget
          exact ⟨x, hx, hget⟩
        · rintro ⟨x, hx, hget⟩
          have hlt : x < v.length := by
            rw [hv]; have := hIdxLt q [] x hx; simp at this; omega
          refine ⟨x, hx, ?_⟩
          rw [getD_foldl_stepWire_of_lt _ _ _ hlt]
          exact hget
      rw [hcongr, List.any_append, any_leftIdx_on_left, any_rightIdx_on_left, Bool.or_false]
      rfl
    have hTaps := hFin.2.2.2.2.2.2.2 v hv
    have hfvC : (rC.1.foldl stepWire v).getD falseW false = false := by
      rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
    have hfv0 : (rS0.1.foldl stepWire v).getD falseW false = false := by
      rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
    have hfv1 : (rS1.1.foldl stepWire v).getD falseW false = false := by
      rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
    have hs0v : (rS2.1.foldl stepWire v).getD rS0.2 false = decide ((0 : Fin 3) = f u) := by
      rw [getD_foldl_extends hExt02 v _ (by rw [hv]; exact hS0.2.2.2.1),
          hS0.2.2.2.2.2 v hv hfvC, hShoreVal 0 rC.1]
    have hs1v : (rS2.1.foldl stepWire v).getD rS1.2 false = decide ((1 : Fin 3) = f u) := by
      rw [getD_foldl_extends hS2.1 v _ (by rw [hv]; exact hS1.2.2.2.1),
          hS1.2.2.2.2.2 v hv hfv0, hShoreVal 1 rS0.1]
    have hs2v : (rS2.1.foldl stepWire v).getD rS2.2 false = decide ((2 : Fin 3) = f u) := by
      rw [hS2.2.2.2.2.2 v hv hfv1, hShoreVal 2 rS1.1]
    fin_cases k
    · change wireEval res.1 v (res.2 0) = _
      rw [hTaps.1, hclk2, hfullVal, hs0v]
      simpa using decide_irrel ((0 : Fin 3) = f u) _ _
    · change wireEval res.1 v (res.2 1) = _
      rw [hTaps.2.1, hfullVal, hs1v]
      simpa using decide_irrel ((1 : Fin 3) = f u) _ _
    · change wireEval res.1 v (res.2 2) = _
      rw [hTaps.2.2, hfullVal, hs2v]
      simpa using decide_irrel ((2 : Fin 3) = f u) _ _
  · rw [hFin.2.2.2.2.2.2.1, hS2.2.2.2.2.1, hS1.2.2.2.2.1, hS0.2.2.2.2.1, hNotC]
    simp [notCountList]
  · have hsz := hFin.2.2.2.2.2.1
    have hl0 := hS0.2.2.1
    have hl1 := hS1.2.2.1
    have hl2 := hS2.2.2.1
    have ha0 : (leftIdx key f 0 ++ rightIdx key f 0).length ≤ 2 * h := by
      rw [List.length_append]
      have := length_leftIdx_le key f 0; have := length_rightIdx_le key f 0; omega
    have ha1 : (leftIdx key f 1 ++ rightIdx key f 1).length ≤ 2 * h := by
      rw [List.length_append]
      have := length_leftIdx_le key f 1; have := length_rightIdx_le key f 1; omega
    have ha2 : (leftIdx key f 2 ++ rightIdx key f 2).length ≤ 2 * h := by
      rw [List.length_append]
      have := length_leftIdx_le key f 2; have := length_rightIdx_le key f 2; omega
    simp only [List.length_nil, Nat.zero_add] at hLenC
    dsimp only [clockLen] at hLenC
    omega

private def emitShore1Not (N : Nat) (gs : List Gate) (falseW isLeft : Nat)
    (lIdx rIdx : List Nat) : List Gate × Nat :=
  let rL := emitOrList N gs falseW lIdx
  let rR := emitOrList N rL.1 falseW rIdx
  let rA := emitAnd N rR.1 isLeft rL.2
  emitOr N rA.1 rA.2 rR.2

private lemma emitShore1Not_spec (N : Nat) (gs : List Gate) (falseW isLeft : Nat)
    (lIdx rIdx : List Nat) (hwf : WF N gs) (hf : falseW < N + gs.length)
    (his : isLeft < N + gs.length) (hl : ∀ u ∈ lIdx, u < N + gs.length)
    (hr : ∀ u ∈ rIdx, u < N + gs.length) :
    let res := emitShore1Not N gs falseW isLeft lIdx rIdx
    Extends gs res.1 ∧ WF N res.1 ∧ res.1.length ≤ gs.length + lIdx.length + rIdx.length + 2 ∧
      res.2 < N + res.1.length ∧ notCountList res.1 = notCountList gs ∧
      ∀ v : List Bool, v.length = N → (gs.foldl stepWire v).getD falseW false = false →
        (res.1.foldl stepWire v).getD res.2 false =
          ((((gs.foldl stepWire v).getD isLeft false) &&
            lIdx.any (fun u => (gs.foldl stepWire v).getD u false)) ||
            rIdx.any (fun u => (gs.foldl stepWire v).getD u false)) := by
  have hL := emitOrList_spec N gs falseW lIdx hwf hf hl
  set rL := emitOrList N gs falseW lIdx
  have hfL : falseW < N + rL.1.length := by have := extends_length_le hL.1; omega
  have hrL : ∀ u ∈ rIdx, u < N + rL.1.length := by
    intro u hu; have := hr u hu; have := extends_length_le hL.1; omega
  have hR := emitOrList_spec N rL.1 falseW rIdx hL.2.1 hfL hrL
  set rR := emitOrList N rL.1 falseW rIdx
  have hExtGR : Extends gs rR.1 := extends_trans hL.1 hR.1
  have hisR : isLeft < N + rR.1.length := by have := extends_length_le hExtGR; omega
  have hlR : rL.2 < N + rR.1.length := by have := extends_length_le hR.1; have := hL.2.2.2.1; omega
  have hA := emitAnd_spec N rR.1 isLeft rL.2 hR.2.1 hisR hlR
  set rA := emitAnd N rR.1 isLeft rL.2
  have hrA : rR.2 < N + rA.1.length := by have := hR.2.2.2.1; omega
  have hO := emitOr_spec N rA.1 rA.2 rR.2 hA.2.1 hA.2.2.2.1 hrA
  refine ⟨extends_trans hExtGR (extends_trans hA.1 hO.1), hO.2.1, ?_, hO.2.2.2.1, ?_, ?_⟩
  · change (emitOr N rA.1 rA.2 rR.2).1.length ≤ gs.length + lIdx.length + rIdx.length + 2
    have := hO.2.2.1; have := hA.2.2.1; have := hR.2.2.1; have := hL.2.2.1; omega
  · change notCountList (emitOr N rA.1 rA.2 rR.2).1 = notCountList gs
    rw [hO.2.2.2.2.1, hA.2.2.2.2.1, hR.2.2.2.2.1, hL.2.2.2.2.1]
  · intro v hv hfv
    dsimp only [emitShore1Not]
    have hfvL : (rL.1.foldl stepWire v).getD falseW false = false := by
      rw [getD_foldl_extends hL.1 v _ (by rw [hv]; exact hf)]; exact hfv
    have hrCongr : rIdx.any (fun u => (rL.1.foldl stepWire v).getD u false) =
        rIdx.any (fun u => (gs.foldl stepWire v).getD u false) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨u, hu, hget⟩
        rw [getD_foldl_extends hL.1 v _ (by rw [hv]; exact hr u hu)] at hget
        exact ⟨u, hu, hget⟩
      · rintro ⟨u, hu, hget⟩
        refine ⟨u, hu, ?_⟩
        rw [getD_foldl_extends hL.1 v _ (by rw [hv]; exact hr u hu)]
        exact hget
    rw [hO.2.2.2.2.2 v hv,
        hA.2.2.2.2.2 v hv,
        getD_foldl_extends hA.1 v _ (by rw [hv]; exact hR.2.2.2.1),
        getD_foldl_extends hExtGR v _ (by rw [hv]; exact his),
        getD_foldl_extends hR.1 v _ (by rw [hv]; exact hL.2.2.2.1),
        hL.2.2.2.2.2 v hv hfv,
        hR.2.2.2.2.2 v hv hfvL,
        hrCongr]

private lemma partB_any {n b h : Nat} (E : Fin n → Fin n → Prop) (f : Fin n → Fin 3)
    (key : Fin h ≃ IxT n) (hh : h = 7 * n) :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    let m := 2 * (2 ^ b - 1)
    let w := 2 * h + m
    ∃ C : Circuit, ∃ p : Fin 3 → Nat,
      PEqualNP.MetaComplexity.FanInTwo C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (w + 2) C ∧
      C.output < w + 2 + C.size ∧ (∀ k, p k < w + 2 + C.size) ∧ p 0 = C.output ∧
      (∀ i : IxT n, ∃ a : Fin 3, (∀ d : PairT, i.2 = some d → a ≠ d.val.1) ∧
        ∀ k, (C.wires (leftVec key i ++ List.replicate m true ++ [false, true])).getD (p k) false =
          decide (k = a)) ∧
      (∀ j : IxT n, ∃ a : Fin 3, (∀ d : PairT, j.2 = some d → a ≠ d.val.2) ∧
        ∀ k, (C.wires (rightVec E key j ++ List.replicate m true ++ [false, true])).getD (p k) false =
          decide (k ≠ a)) ∧
      (∀ (j : Fin m) (k : Fin 3),
        (C.wires (List.replicate (2 * h) false ++ List.ofFn (fun i : Fin m => decide (i < j)) ++
          [false, true])).getD (p k) false = decide (k = 0 ∧ j.val % 2 = 0)) ∧
      (∀ (i : Fin n) (k : Fin 3),
        (C.wires (leftVec key (i, none) ++ List.replicate m true ++ [false, true])).getD (p k) false =
          decide (k = f i)) ∧
      PEqualNP.NotBracket.notCount C = b + 1 ∧ C.size ≤ 100 * (n + m + 1) := by
  dsimp only
  let m := clockLen b
  let w := 2 * h + m
  let N := w + 2
  let falseW := w
  let fullPad := if b = 0 then w + 1 else 2 * h + (m - 1)
  have huClk : ∀ r < m, (clkInputWires h m).getD r falseW < N + ([] : List Gate).length := by
    intro r hr
    rw [getD_clkInputWires h m falseW r hr]
    omega
  obtain ⟨hExtC, hWfC, hOutC, hLenC, hNotC, hEvalC⟩ :=
    buildClock_spec b N [] falseW (clkInputWires h m) (wf_nil N) (by omega) huClk
  set rC := buildClock b N [] falseW (clkInputWires h m)
  have hAR := emitOrList_spec N rC.1 falseW (allRightIdx h) hWfC (by omega) (by
    intro u hu; have := allRightIdx_lt h u hu; omega)
  set rAR := emitOrList N rC.1 falseW (allRightIdx h)
  have hIL := emitNot_spec N rAR.1 rAR.2 hAR.2.1 hAR.2.2.2.1
  set rIL := emitNot N rAR.1 rAR.2
  have hLLt : ∀ (k : Fin 3) (gs : List Gate), ∀ u ∈ leftIdx key f k, u < N + gs.length := by
    intro k gs u hu; have := leftIdx_lt key f k u hu; omega
  have hRLt : ∀ (k : Fin 3) (gs : List Gate), ∀ u ∈ rightIdx key f k, u < N + gs.length := by
    intro k gs u hu; have := rightIdx_lt key f k u hu; omega
  have hS0 := emitShore1Not_spec N rIL.1 falseW rIL.2 (leftIdx key f 0) (rightIdx key f 0)
    hIL.2.1 (by omega) hIL.2.2.2.1 (hLLt 0 rIL.1) (hRLt 0 rIL.1)
  set rS0 := emitShore1Not N rIL.1 falseW rIL.2 (leftIdx key f 0) (rightIdx key f 0)
  have his0 : rIL.2 < N + rS0.1.length := by
    have := extends_length_le hS0.1; have := hIL.2.2.2.1; omega
  have hS1 := emitShore1Not_spec N rS0.1 falseW rIL.2 (leftIdx key f 1) (rightIdx key f 1)
    hS0.2.1 (by omega) his0 (hLLt 1 rS0.1) (hRLt 1 rS0.1)
  set rS1 := emitShore1Not N rS0.1 falseW rIL.2 (leftIdx key f 1) (rightIdx key f 1)
  have his1 : rIL.2 < N + rS1.1.length := by
    have := extends_length_le hS1.1; omega
  have hS2 := emitShore1Not_spec N rS1.1 falseW rIL.2 (leftIdx key f 2) (rightIdx key f 2)
    hS1.2.1 (by omega) his1 (hLLt 2 rS1.1) (hRLt 2 rS1.1)
  set rS2 := emitShore1Not N rS1.1 falseW rIL.2 (leftIdx key f 2) (rightIdx key f 2)
  have hExtCIL : Extends rC.1 rIL.1 := extends_trans hAR.1 hIL.1
  have hExtIL1 : Extends rIL.1 rS1.1 := extends_trans hS0.1 hS1.1
  have hExtIL2 : Extends rIL.1 rS2.1 := extends_trans hExtIL1 hS2.1
  have hExtC2 : Extends rC.1 rS2.1 := extends_trans hExtCIL hExtIL2
  have hExt02 : Extends rS0.1 rS2.1 := extends_trans hS1.1 hS2.1
  have hpadLt : fullPad < N + rS2.1.length := by
    have hpf : fullPad < N := (fullPad_eval h b (List.replicate (2 * h) false) (by simp)).1
    omega
  have hclkLt : rC.2 < N + rS2.1.length := by
    have := extends_length_le hExtC2; omega
  have hs0Lt : rS0.2 < N + rS2.1.length := by
    have := extends_length_le hExt02; have := hS0.2.2.2.1; omega
  have hs1Lt : rS1.2 < N + rS2.1.length := by
    have := extends_length_le hS2.1; have := hS1.2.2.2.1; omega
  have hFin := finalizeTaps_spec N rS2.1 fullPad rC.2 rS0.2 rS1.2 rS2.2
    hS2.2.1 hpadLt hclkLt hs0Lt hs1Lt hS2.2.2.2.1
  set res := finalizeTaps N rS2.1 fullPad rC.2 rS0.2 rS1.2 rS2.2
  have hclkShore : ∀ s : List Bool, s.length = 2 * h →
      (rC.1.foldl stepWire (s ++ List.replicate m true ++ [false, true])).getD rC.2 false = false := by
    intro s hs
    have hpad := getD_input_pad_shore h m s hs
    have h1 := hEvalC (s ++ List.replicate m true ++ [false, true]) m
      (by simp [hs]; omega) hpad.2.1 (Nat.le_refl _) (by
        intro r hr
        have hr' : r < m := hr
        rw [List.foldl_nil, getD_clkInputWires h m falseW r hr', hpad.1 r hr']
        simp [hr'])
    have hnot : ¬(m < clockLen b) := by dsimp only [m]; omega
    simpa [hnot] using h1
  have hAnyCongr : ∀ (l : List Nat) (gs : List Gate) (v : List Bool),
      v.length = N → (∀ u ∈ l, u < 2 * h) →
      l.any (fun u => (gs.foldl stepWire v).getD u false) = l.any (fun u => v.getD u false) := by
    intro l gs v hv hl
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨u, hu, hget⟩
      have hlt : u < v.length := by rw [hv]; have := hl u hu; omega
      rw [getD_foldl_stepWire_of_lt _ _ _ hlt] at hget
      exact ⟨u, hu, hget⟩
    · rintro ⟨u, hu, hget⟩
      have hlt : u < v.length := by rw [hv]; have := hl u hu; omega
      refine ⟨u, hu, ?_⟩
      rw [getD_foldl_stepWire_of_lt _ _ _ hlt]
      exact hget
  refine ⟨res.1, res.2, hFin.1, hFin.2.1, hFin.2.2.1, hFin.2.2.2.1, hFin.2.2.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨colL f i, ?_, ?_⟩
    · intro d hid
      rcases i with ⟨u, oi⟩
      dsimp only at hid
      subst hid
      exact (colL_some_props f u d).1
    · intro k
      set v := leftVec key i ++ List.replicate m true ++ [false, true]
      have hv : v.length = N := length_leftFull key m i
      have hpad := getD_input_pad_shore h m (leftVec key i) (length_leftVec key i)
      have hclkVal : (rC.1.foldl stepWire v).getD rC.2 false = false :=
        hclkShore (leftVec key i) (length_leftVec key i)
      have hfullVal : (rS2.1.foldl stepWire v).getD fullPad false = true := by
        have hlt : fullPad < v.length := by
          rw [hv]; exact (fullPad_eval h b (leftVec key i) (length_leftVec key i)).1
        rw [getD_foldl_stepWire_of_lt _ _ _ hlt]
        exact (fullPad_eval h b (leftVec key i) (length_leftVec key i)).2.1
      have hclk2 : (rS2.1.foldl stepWire v).getD rC.2 false = false := by
        rw [getD_foldl_extends hExtC2 v _ (by rw [hv]; exact hOutC)]
        exact hclkVal
      have hfvC : (rC.1.foldl stepWire v).getD falseW false = false := by
        rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
      have hfvIL : (rIL.1.foldl stepWire v).getD falseW false = false := by
        rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
      have hfv0 : (rS0.1.foldl stepWire v).getD falseW false = false := by
        rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
      have hfv1 : (rS1.1.foldl stepWire v).getD falseW false = false := by
        rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
      have hisL : (rIL.1.foldl stepWire v).getD rIL.2 false = true := by
        rw [hIL.2.2.2.2.2 v hv, hAR.2.2.2.2.2 v hv hfvC,
            hAnyCongr (allRightIdx h) rC.1 v hv (allRightIdx_lt h),
            any_allRightIdx_on_left]
        rfl
      have hs0v : (rS2.1.foldl stepWire v).getD rS0.2 false = decide ((0 : Fin 3) = colL f i) := by
        rw [getD_foldl_extends hExt02 v _ (by rw [hv]; exact hS0.2.2.2.1),
            hS0.2.2.2.2.2 v hv hfvIL, hisL,
            hAnyCongr (leftIdx key f 0) rIL.1 v hv (leftIdx_lt key f 0),
            hAnyCongr (rightIdx key f 0) rIL.1 v hv (rightIdx_lt key f 0),
            any_leftIdx_on_left, any_rightIdx_on_left]
        simp
      have hs1v : (rS2.1.foldl stepWire v).getD rS1.2 false = decide ((1 : Fin 3) = colL f i) := by
        rw [getD_foldl_extends hS2.1 v _ (by rw [hv]; exact hS1.2.2.2.1),
            hS1.2.2.2.2.2 v hv hfv0,
            getD_foldl_extends hS0.1 v _ (by rw [hv]; exact hIL.2.2.2.1), hisL,
            hAnyCongr (leftIdx key f 1) rS0.1 v hv (leftIdx_lt key f 1),
            hAnyCongr (rightIdx key f 1) rS0.1 v hv (rightIdx_lt key f 1),
            any_leftIdx_on_left, any_rightIdx_on_left]
        simp
      have hs2v : (rS2.1.foldl stepWire v).getD rS2.2 false = decide ((2 : Fin 3) = colL f i) := by
        rw [hS2.2.2.2.2.2 v hv hfv1,
            getD_foldl_extends hExtIL1 v _ (by rw [hv]; exact hIL.2.2.2.1), hisL,
            hAnyCongr (leftIdx key f 2) rS1.1 v hv (leftIdx_lt key f 2),
            hAnyCongr (rightIdx key f 2) rS1.1 v hv (rightIdx_lt key f 2),
            any_leftIdx_on_left, any_rightIdx_on_left]
        simp
      have hTaps := hFin.2.2.2.2.2.2.2 v hv
      fin_cases k
      · change wireEval res.1 v (res.2 0) = _
        rw [hTaps.1, hclk2, hfullVal, hs0v]
        simpa using decide_irrel ((0 : Fin 3) = colL f i) _ _
      · change wireEval res.1 v (res.2 1) = _
        rw [hTaps.2.1, hfullVal, hs1v]
        simpa using decide_irrel ((1 : Fin 3) = colL f i) _ _
      · change wireEval res.1 v (res.2 2) = _
        rw [hTaps.2.2, hfullVal, hs2v]
        simpa using decide_irrel ((2 : Fin 3) = colL f i) _ _
  · intro j
    refine ⟨colR f j, ?_, ?_⟩
    · intro d hjd
      rcases j with ⟨u, oj⟩
      dsimp only at hjd
      subst hjd
      exact (colR_some_props f u d).1
    · intro k
      set v := rightVec E key j ++ List.replicate m true ++ [false, true]
      have hv : v.length = N := length_rightFull E key m j
      have hpad := getD_input_pad_shore h m (rightVec E key j) (length_rightVec E key j)
      have hclkVal : (rC.1.foldl stepWire v).getD rC.2 false = false :=
        hclkShore (rightVec E key j) (length_rightVec E key j)
      have hfullVal : (rS2.1.foldl stepWire v).getD fullPad false = true := by
        have hlt : fullPad < v.length := by
          rw [hv]; exact (fullPad_eval h b (rightVec E key j) (length_rightVec E key j)).1
        rw [getD_foldl_stepWire_of_lt _ _ _ hlt]
        exact (fullPad_eval h b (rightVec E key j) (length_rightVec E key j)).2.1
      have hclk2 : (rS2.1.foldl stepWire v).getD rC.2 false = false := by
        rw [getD_foldl_extends hExtC2 v _ (by rw [hv]; exact hOutC)]
        exact hclkVal
      have hfvC : (rC.1.foldl stepWire v).getD falseW false = false := by
        rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
      have hfvIL : (rIL.1.foldl stepWire v).getD falseW false = false := by
        rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
      have hfv0 : (rS0.1.foldl stepWire v).getD falseW false = false := by
        rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
      have hfv1 : (rS1.1.foldl stepWire v).getD falseW false = false := by
        rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
      have hisL : (rIL.1.foldl stepWire v).getD rIL.2 false = false := by
        rw [hIL.2.2.2.2.2 v hv, hAR.2.2.2.2.2 v hv hfvC,
            hAnyCongr (allRightIdx h) rC.1 v hv (allRightIdx_lt h),
            any_allRightIdx_on_right]
        rfl
      have hs0v : (rS2.1.foldl stepWire v).getD rS0.2 false = decide ((0 : Fin 3) ≠ colR f j) := by
        rw [getD_foldl_extends hExt02 v _ (by rw [hv]; exact hS0.2.2.2.1),
            hS0.2.2.2.2.2 v hv hfvIL, hisL,
            hAnyCongr (rightIdx key f 0) rIL.1 v hv (rightIdx_lt key f 0),
            any_rightIdx_on_right]
        simp
      have hs1v : (rS2.1.foldl stepWire v).getD rS1.2 false = decide ((1 : Fin 3) ≠ colR f j) := by
        rw [getD_foldl_extends hS2.1 v _ (by rw [hv]; exact hS1.2.2.2.1),
            hS1.2.2.2.2.2 v hv hfv0,
            getD_foldl_extends hS0.1 v _ (by rw [hv]; exact hIL.2.2.2.1), hisL,
            hAnyCongr (rightIdx key f 1) rS0.1 v hv (rightIdx_lt key f 1),
            any_rightIdx_on_right]
        simp
      have hs2v : (rS2.1.foldl stepWire v).getD rS2.2 false = decide ((2 : Fin 3) ≠ colR f j) := by
        rw [hS2.2.2.2.2.2 v hv hfv1,
            getD_foldl_extends hExtIL1 v _ (by rw [hv]; exact hIL.2.2.2.1), hisL,
            hAnyCongr (rightIdx key f 2) rS1.1 v hv (rightIdx_lt key f 2),
            any_rightIdx_on_right]
        simp
      have hTaps := hFin.2.2.2.2.2.2.2 v hv
      fin_cases k
      · change wireEval res.1 v (res.2 0) = _
        rw [hTaps.1, hclk2, hfullVal, hs0v]
        simpa using decide_irrel ((0 : Fin 3) ≠ colR f j) _ _
      · change wireEval res.1 v (res.2 1) = _
        rw [hTaps.2.1, hfullVal, hs1v]
        simpa using decide_irrel ((1 : Fin 3) ≠ colR f j) _ _
      · change wireEval res.1 v (res.2 2) = _
        rw [hTaps.2.2, hfullVal, hs2v]
        simpa using decide_irrel ((2 : Fin 3) ≠ colR f j) _ _
  · intro j k
    have hcf : List.replicate (2 * h) false ++
        List.ofFn (fun i : Fin (2 * (2 ^ b - 1)) => @decide (i < j) (Classical.propDecidable _)) ++
        [false, true] = clockFull h m j.val := clockFull_eq_fin h m j
    rw [hcf]
    set v := clockFull h m j.val
    have hv : v.length = N := length_clockFull h m j.val
    have hpad := getD_input_pad_clock h m j.val
    have hclkVal : (rC.1.foldl stepWire v).getD rC.2 false = decide (j.val % 2 = 0) := by
      have h1 := hEvalC v j.val hv hpad.2.1 (Nat.le_of_lt j.isLt) (by
        intro r hr
        have hr' : r < m := hr
        rw [List.foldl_nil, getD_clkInputWires h m falseW r hr', hpad.1 r hr'])
      have hjlt : j.val < clockLen b := j.isLt
      simpa [hjlt] using h1
    have hfullVal : (rS2.1.foldl stepWire v).getD fullPad false = false := by
      have hlt : fullPad < v.length := by
        rw [hv]; exact (fullPad_eval h b (List.replicate (2 * h) false) (by simp)).1
      rw [getD_foldl_stepWire_of_lt _ _ _ hlt]
      exact (fullPad_eval h b (List.replicate (2 * h) false) (by simp)).2.2 j
    have hclk2 : (rS2.1.foldl stepWire v).getD rC.2 false = decide (j.val % 2 = 0) := by
      rw [getD_foldl_extends hExtC2 v _ (by rw [hv]; exact hOutC)]
      exact hclkVal
    have hTaps := hFin.2.2.2.2.2.2.2 v hv
    fin_cases k
    · change wireEval res.1 v (res.2 0) = _
      rw [hTaps.1, hclk2, hfullVal]
      simp only [Bool.false_and, Bool.or_false]
      by_cases hmod : j.val % 2 = 0
      · simp [hmod]
      · simp [hmod]
    · change wireEval res.1 v (res.2 1) = _
      rw [hTaps.2.1, hfullVal]
      simp
    · change wireEval res.1 v (res.2 2) = _
      rw [hTaps.2.2, hfullVal]
      simp
  · intro u k
    set i : IxT n := (u, none)
    set v := leftVec key i ++ List.replicate m true ++ [false, true]
    have hv : v.length = N := length_leftFull key m i
    have hpad := getD_input_pad_shore h m (leftVec key i) (length_leftVec key i)
    have hclkVal : (rC.1.foldl stepWire v).getD rC.2 false = false :=
      hclkShore (leftVec key i) (length_leftVec key i)
    have hfullVal : (rS2.1.foldl stepWire v).getD fullPad false = true := by
      have hlt : fullPad < v.length := by
        rw [hv]; exact (fullPad_eval h b (leftVec key i) (length_leftVec key i)).1
      rw [getD_foldl_stepWire_of_lt _ _ _ hlt]
      exact (fullPad_eval h b (leftVec key i) (length_leftVec key i)).2.1
    have hclk2 : (rS2.1.foldl stepWire v).getD rC.2 false = false := by
      rw [getD_foldl_extends hExtC2 v _ (by rw [hv]; exact hOutC)]
      exact hclkVal
    have hfvC : (rC.1.foldl stepWire v).getD falseW false = false := by
      rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
    have hfvIL : (rIL.1.foldl stepWire v).getD falseW false = false := by
      rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
    have hfv0 : (rS0.1.foldl stepWire v).getD falseW false = false := by
      rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
    have hfv1 : (rS1.1.foldl stepWire v).getD falseW false = false := by
      rw [getD_foldl_stepWire_of_lt _ _ _ (by rw [hv]; omega)]; exact hpad.2.1
    have hisL : (rIL.1.foldl stepWire v).getD rIL.2 false = true := by
      rw [hIL.2.2.2.2.2 v hv, hAR.2.2.2.2.2 v hv hfvC,
          hAnyCongr (allRightIdx h) rC.1 v hv (allRightIdx_lt h),
          any_allRightIdx_on_left]
      rfl
    have hs0v : (rS2.1.foldl stepWire v).getD rS0.2 false = decide ((0 : Fin 3) = f u) := by
      rw [getD_foldl_extends hExt02 v _ (by rw [hv]; exact hS0.2.2.2.1),
          hS0.2.2.2.2.2 v hv hfvIL, hisL,
          hAnyCongr (leftIdx key f 0) rIL.1 v hv (leftIdx_lt key f 0),
          hAnyCongr (rightIdx key f 0) rIL.1 v hv (rightIdx_lt key f 0),
          any_leftIdx_on_left, any_rightIdx_on_left]
      rw [Bool.true_and, Bool.or_false]
      exact decide_irrel ((0 : Fin 3) = f u) _ _
    have hs1v : (rS2.1.foldl stepWire v).getD rS1.2 false = decide ((1 : Fin 3) = f u) := by
      rw [getD_foldl_extends hS2.1 v _ (by rw [hv]; exact hS1.2.2.2.1),
          hS1.2.2.2.2.2 v hv hfv0,
          getD_foldl_extends hS0.1 v _ (by rw [hv]; exact hIL.2.2.2.1), hisL,
          hAnyCongr (leftIdx key f 1) rS0.1 v hv (leftIdx_lt key f 1),
          hAnyCongr (rightIdx key f 1) rS0.1 v hv (rightIdx_lt key f 1),
          any_leftIdx_on_left, any_rightIdx_on_left]
      rw [Bool.true_and, Bool.or_false]
      exact decide_irrel ((1 : Fin 3) = f u) _ _
    have hs2v : (rS2.1.foldl stepWire v).getD rS2.2 false = decide ((2 : Fin 3) = f u) := by
      rw [hS2.2.2.2.2.2 v hv hfv1,
          getD_foldl_extends hExtIL1 v _ (by rw [hv]; exact hIL.2.2.2.1), hisL,
          hAnyCongr (leftIdx key f 2) rS1.1 v hv (leftIdx_lt key f 2),
          hAnyCongr (rightIdx key f 2) rS1.1 v hv (rightIdx_lt key f 2),
          any_leftIdx_on_left, any_rightIdx_on_left]
      rw [Bool.true_and, Bool.or_false]
      exact decide_irrel ((2 : Fin 3) = f u) _ _
    have hTaps := hFin.2.2.2.2.2.2.2 v hv
    fin_cases k
    · change wireEval res.1 v (res.2 0) = _
      rw [hTaps.1, hclk2, hfullVal, hs0v]
      simpa using decide_irrel ((0 : Fin 3) = f u) _ _
    · change wireEval res.1 v (res.2 1) = _
      rw [hTaps.2.1, hfullVal, hs1v]
      simpa using decide_irrel ((1 : Fin 3) = f u) _ _
    · change wireEval res.1 v (res.2 2) = _
      rw [hTaps.2.2, hfullVal, hs2v]
      simpa using decide_irrel ((2 : Fin 3) = f u) _ _
  · rw [hFin.2.2.2.2.2.2.1, hS2.2.2.2.2.1, hS1.2.2.2.2.1, hS0.2.2.2.2.1,
        hIL.2.2.2.2.1, hAR.2.2.2.2.1, hNotC]
    simp [notCountList]
  · have hsz := hFin.2.2.2.2.2.1
    have hlAR := hAR.2.2.1
    have hlIL := hIL.2.2.1
    have hl0 := hS0.2.2.1
    have hl1 := hS1.2.2.1
    have hl2 := hS2.2.2.1
    have hARlen := length_allRightIdx h
    have hlL0 := length_leftIdx_le key f 0
    have hlR0 := length_rightIdx_le key f 0
    have hlL1 := length_leftIdx_le key f 1
    have hlR1 := length_rightIdx_le key f 1
    have hlL2 := length_leftIdx_le key f 2
    have hlR2 := length_rightIdx_le key f 2
    simp only [List.length_nil, Nat.zero_add] at hLenC
    dsimp only [clockLen] at hLenC
    omega

end PEqualNP.Outside.L_lib_1289

theorem PEqualNP.Outside.L_lib_1289 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n b : Nat) (E : Fin n → Fin n → Prop) (f : Fin n → Fin 3),
  let Pair := {p : Fin 3 × Fin 3 // p.1 ≠ p.2}
  let Ix := Fin n × Option Pair
  let h := Fintype.card Ix
  let key := (Fintype.equivFin Ix).symm
  let m := 2*(2^b-1)
  let w := 2*h+m
  let edge := fun (i j : Ix) => if i.2=none ∧ j.2=none then E i.1 j.1
    else i.1=j.1 ∧ (i.2=none ∨ j.2=none ∨ i.2=j.2)
  let left := fun (i : Ix) => List.ofFn (fun k : Fin h => decide (key k=i)) ++ List.replicate h false
  let right := fun (j : Ix) => List.ofFn (fun k : Fin h => decide (edge (key k) j)) ++
    List.ofFn (fun k : Fin h => decide (key k=j))
  let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin 3 → Nat) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (w+2) C ∧
    C.output < w+2+C.size ∧ (∀ k, p k < w+2+C.size) ∧ p 0 = C.output ∧
      let v := fun (z : List Bool) (k : Fin 3) => (C.wires (z ++ [false,true])).getD (p k) false
      (∀ i : Ix, ∃ a : Fin 3, (∀ d : Pair, i.2=some d → a≠d.val.1) ∧
        ∀ k, v (left i ++ List.replicate m true) k = decide (k=a)) ∧
      (∀ j : Ix, ∃ a : Fin 3, (∀ d : Pair, j.2=some d → a≠d.val.2) ∧
        ∀ k, v (right j ++ List.replicate m true) k = decide (k≠a)) ∧
      ∀ (j : Fin m) (k : Fin 3), v (List.replicate (2*h) false ++
        List.ofFn (fun i : Fin m => decide (i<j))) k = decide (k=0 ∧ j.val % 2=0)
  let trace := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Fin 3 → Nat) =>
    ∀ (i : Fin n) (k : Fin 3), (C.wires (left (i,none) ++ List.replicate m true ++
      [false,true])).getD (p k) false = decide (k=f i)
  let proper := fun (g : Fin n → Fin 3) => ∀ i j, E i j → g i ≠ g j
  ((∃ g, proper g) ↔ ∃ C p, fits C p ∧ PEqualNP.NotBracket.notCount C=b) ∧
  (∀ C p, fits C p → b ≤ PEqualNP.NotBracket.notCount C ∧
    (PEqualNP.NotBracket.notCount C=b → trace C p → proper f)) ∧
  (proper f → ∃ C p, fits C p ∧ trace C p ∧ PEqualNP.NotBracket.notCount C=b ∧ C.size ≤ 100*(n+m+1)) ∧
  ∃ C p, fits C p ∧ trace C p ∧ PEqualNP.NotBracket.notCount C=b+1 ∧ C.size ≤ 100*(n+m+1)) := by
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  intro n b E f
  dsimp only
  set Pair := {p : Fin 3 × Fin 3 // p.1 ≠ p.2}
  set Ix := Fin n × Option Pair
  set h := Fintype.card Ix
  set key := (Fintype.equivFin Ix).symm
  have hh : h = 7 * n := PEqualNP.Outside.L_lib_1289.card_ix_eq n _
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · rintro ⟨g, hg⟩
      obtain ⟨C, p, h1, h2, h3, h4, h5, h6, h7, h8, _, h10, _⟩ :=
        PEqualNP.Outside.L_lib_1289.partB_proper E g key hh hg
      exact ⟨C, p, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, h10⟩
    · rintro ⟨C, p, ⟨h1, h2, _, h4, _, h6, h7, h8⟩, hnot⟩
      have hA := PEqualNP.Outside.L_lib_1289.partA_lower_bound E f key C p h1 h2 h4 h6 h7 h8
      exact (hA.2 hnot).1
  · intro C p ⟨h1, h2, _, h4, _, h6, h7, h8⟩
    have hA := PEqualNP.Outside.L_lib_1289.partA_lower_bound E f key C p h1 h2 h4 h6 h7 h8
    exact ⟨hA.1, fun hnot htr => (hA.2 hnot).2 htr⟩
  · intro hprop
    obtain ⟨C, p, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
      PEqualNP.Outside.L_lib_1289.partB_proper E f key hh hprop
    exact ⟨C, p, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, h9, h10, h11⟩
  · obtain ⟨C, p, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
      PEqualNP.Outside.L_lib_1289.partB_any E f key hh
    exact ⟨C, p, ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, h9, h10, h11⟩
